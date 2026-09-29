-- Prove2me | solution 1 for ModularCurve.exists_ne_zero_mul_eq_isIntegral_of_mem_closure_of_mem_valuationSubring
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/e96dd05b-9a1f-5037-91fa-4e09feee253e

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_ne_zero_mul_eq_isIntegral_of_mem_closure_of_mem_valuationSubring
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

section FracWHelpers

open Polynomial IntermediateField

private theorem fracW_isIntegral_tail {A L : Type*} [CommRing A] [Field L] [Algebra A L]
    (c : ℕ → L) (hc : ∀ i, c i ∈ Set.range (algebraMap A L)) (d : ℕ) (f : L)
    (hrel : ∑ i ∈ Finset.range (d + 1), c i * f ^ i = 0) (r : ℕ) :
    IsIntegral A (∑ i ∈ Finset.Ico r (d + 1), c i * f ^ (i - r)) := by
  classical
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp only [Nat.sub_zero]
    rw [← Finset.range_eq_Ico, hrel]
    exact isIntegral_zero
  by_cases hrd : d < r
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    exact isIntegral_zero
  push Not at hrd
  obtain ⟨t, ht⟩ : ∃ t, t = ∑ i ∈ Finset.Ico r (d + 1), c i * f ^ (i - r) := ⟨_, rfl⟩
  rw [← ht]
  have hsmul : ∀ (i : ℕ) (x : L) (N : Submodule A L), x ∈ N → c i * x ∈ N := by
    intro i x N hx
    obtain ⟨b, hb⟩ := hc i
    rw [← hb, ← Algebra.smul_def]
    exact N.smul_mem b hx
  let N : Submodule A L := Submodule.span A ((fun k => f ^ k) '' (Finset.range d : Set ℕ))
  have hpow : ∀ k < d, f ^ k ∈ N := fun k hk =>
    Submodule.subset_span ⟨k, by simpa using hk, rfl⟩
  have hN1 : (1 : L) ∈ N := by simpa using hpow 0 (by omega)
  have hNbot : N ≠ ⊥ := fun h => one_ne_zero ((Submodule.eq_bot_iff _).mp h 1 hN1)
  have hNfg : N.FG := Submodule.fg_span ((Finset.range d).finite_toSet.image _)

  have hkey : f ^ r * t = -∑ i ∈ Finset.range r, c i * f ^ i := by
    rw [eq_neg_iff_add_eq_zero, ← hrel, ht, Finset.mul_sum]
    have : ∑ i ∈ Finset.Ico r (d + 1), f ^ r * (c i * f ^ (i - r))
        = ∑ i ∈ Finset.Ico r (d + 1), c i * f ^ i := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : r ≤ i := (Finset.mem_Ico.mp hi).1
      rw [mul_left_comm, ← _root_.pow_add, Nat.add_sub_cancel' hi']
    rw [this, Finset.range_eq_Ico, Finset.range_eq_Ico, add_comm,
      Finset.sum_Ico_consecutive _ (Nat.zero_le r) (by omega)]
  refine isIntegral_of_smul_mem_submodule N hNbot hNfg t ?_
  suffices h : ∀ k < d, t * f ^ k ∈ N by
    have hle : N ≤ N.comap (LinearMap.mulLeft A t) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨k, hk, rfl⟩
      simpa using h k (by simpa using hk)
    intro n hn
    simpa using hle hn
  intro k hk
  by_cases hkr : k < r
  · rw [ht, Finset.sum_mul]
    refine Submodule.sum_mem _ fun i hi => ?_
    have hi' := Finset.mem_Ico.mp hi
    rw [mul_assoc, ← _root_.pow_add]
    exact hsmul _ _ _ (hpow _ (by omega))
  · push Not at hkr
    have : t * f ^ k = f ^ (k - r) * (f ^ r * t) := by
      rw [← mul_assoc, ← _root_.pow_add, Nat.sub_add_cancel hkr, mul_comm]
    rw [this, hkey, mul_neg, Finset.mul_sum]
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun i hi => ?_)
    have hi' := Finset.mem_range.mp hi
    rw [mul_left_comm, ← _root_.pow_add]
    exact hsmul _ _ _ (hpow _ (by omega))

private theorem fracW_eval₂_mem {K₀ L : Type*} [Field K₀] [Field L] {S : Type*} [SetLike S L] [SubringClass S L]
    (σ : K₀ →+* L) {j : L} (s : S) (hσ : ∀ c, σ c ∈ s) (hj : j ∈ s) (p : K₀[X]) :
    p.eval₂ σ j ∈ s := by
  rw [Polynomial.eval₂_eq_sum_range]
  exact sum_mem fun i _ => mul_mem (hσ _) (pow_mem hj _)

private theorem fracW_core {K₀ L : Type*} [Field K₀] [Field L]
    (σ : K₀ →+* L) (O : ValuationSubring L) (hσO : ∀ c, σ c ∈ O)
    {j f : L} (hjO : j ∈ O) (hfO : f ∈ O)
    (hinj : ∀ p : K₀[X], p.eval₂ σ j = 0 → p = 0)
    {A : Type*} [CommRing A] [Algebra A L]
    (hA : ∀ p : K₀[X], p.eval₂ σ j ∈ Set.range (algebraMap A L))
    (E : Subfield L) (hσE : ∀ c, σ c ∈ E) (hjE : j ∈ E) (hfE : f ∈ E)
    {d : ℕ} (G : ℕ → K₀[X]) (hG : ∃ i ∈ Finset.range (d + 1), G i ≠ 0)
    (hrel : ∑ i ∈ Finset.range (d + 1), (G i).eval₂ σ j * f ^ i = 0) :
    ∃ a s : L, IsIntegral A a ∧ IsIntegral A s ∧ a ∈ E ∧ s ∈ E ∧
      s ≠ 0 ∧ s ∈ O ∧ s⁻¹ ∈ O ∧ f * s = a := by
  classical

  obtain ⟨G', hGG', hgcd⟩ := Finset.extract_gcd G (⟨0, Finset.mem_range.mpr (Nat.succ_pos d)⟩ : (Finset.range (d + 1)).Nonempty)
  have hg₀ne : (Finset.range (d + 1)).gcd G ≠ 0 := by
    intro h
    rw [Finset.gcd_eq_zero_iff] at h
    obtain ⟨i, hi, hne⟩ := hG
    exact hne (h i hi)
  obtain ⟨c, hc⟩ : ∃ c : ℕ → L, ∀ i, c i = (G' i).eval₂ σ j := ⟨_, fun _ => rfl⟩
  have hcA : ∀ i, c i ∈ Set.range (algebraMap A L) := fun i => hc i ▸ hA (G' i)
  have hrel' : ∑ i ∈ Finset.range (d + 1), c i * f ^ i = 0 := by
    have h1 : ∑ i ∈ Finset.range (d + 1), (G i).eval₂ σ j * f ^ i
        = ((Finset.range (d + 1)).gcd G).eval₂ σ j * ∑ i ∈ Finset.range (d + 1), c i * f ^ i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hGG' i hi, Polynomial.eval₂_mul, mul_assoc, hc]
    rw [h1] at hrel
    exact (mul_eq_zero.mp hrel).resolve_left (fun h => hg₀ne (hinj _ h))

  let w := O.valuation
  have hwf : w f ≤ 1 := (O.valuation_le_one_iff _).mpr hfO
  have hwc : ∀ i, w (c i) ≤ 1 := fun i =>
    (O.valuation_le_one_iff _).mpr (hc i ▸ fracW_eval₂_mem σ O hσO hjO _)
  have hprod : ∀ i n, w (c i) < 1 → w (c i * f ^ n) < 1 := fun i n hi => by
    rw [Valuation.map_mul, Valuation.map_pow]
    calc w (c i) * w f ^ n ≤ w (c i) * 1 := mul_le_mul_right (pow_le_one' hwf n) _
      _ < 1 := by rwa [mul_one]

  let ψ : K₀[X] →+* O :=
    (Polynomial.eval₂RingHom σ j).codRestrict O (fun p => fracW_eval₂_mem σ O hσO hjO p)
  let 𝔭 : Ideal K₀[X] := (IsLocalRing.maximalIdeal O).comap ψ
  have h𝔭 : ∀ p : K₀[X], p ∈ 𝔭 ↔ w (p.eval₂ σ j) < 1 := fun p => by
    rw [Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
    rfl
  haveI h𝔭prime : 𝔭.IsPrime := Ideal.IsPrime.comap ψ
  haveI h𝔭princ : Submodule.IsPrincipal 𝔭 := IsPrincipalIdealRing.principal 𝔭
  have hex : ∃ m ∈ Finset.range (d + 1), G' m ∉ 𝔭 := by
    by_contra h
    push Not at h
    have hdvd : Submodule.IsPrincipal.generator 𝔭 ∣ (Finset.range (d + 1)).gcd G' :=
      Finset.dvd_gcd_iff.mpr fun i hi =>
        (Submodule.IsPrincipal.mem_iff_generator_dvd 𝔭).mp (h i hi)
    rw [hgcd] at hdvd
    exact h𝔭prime.ne_top
      (Ideal.eq_top_of_isUnit_mem 𝔭 (Submodule.IsPrincipal.generator_mem 𝔭) (isUnit_of_dvd_one hdvd))

  let T := (Finset.range (d + 1)).filter fun i => G' i ∉ 𝔭
  have hT : T.Nonempty := by
    obtain ⟨m, hm, hm'⟩ := hex
    exact ⟨m, Finset.mem_filter.mpr ⟨hm, hm'⟩⟩
  obtain ⟨m, hmT, hmax⟩ : ∃ m ∈ T, ∀ i ∈ T, i ≤ m :=
    ⟨T.max' hT, Finset.max'_mem _ _, fun i hi => Finset.le_max' _ _ hi⟩
  have hmd : m < d + 1 := Finset.mem_range.mp (Finset.mem_filter.mp hmT).1
  have hm𝔭 : G' m ∉ 𝔭 := (Finset.mem_filter.mp hmT).2
  have hwm : w (c m) = 1 := by
    refine le_antisymm (hwc m) (not_lt.mp fun hlt => hm𝔭 ?_)
    rw [h𝔭, ← hc]
    exact hlt
  have hwi : ∀ i ∈ Finset.range (d + 1), m < i → w (c i) < 1 := fun i hi hmi => by
    rw [hc, ← h𝔭]
    by_contra h
    exact absurd (hmax i (Finset.mem_filter.mpr ⟨hi, h⟩)) (not_le.mpr hmi)

  have hm0 : m ≠ 0 := by
    intro hm0
    subst hm0
    have h1 : c 0 * f ^ 0 + ∑ i ∈ Finset.Ico 1 (d + 1), c i * f ^ i = 0 := by
      rwa [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos d)] at hrel'
    rw [pow_zero, mul_one, add_eq_zero_iff_eq_neg] at h1
    have h2 : w (c 0) < 1 := by
      rw [h1, Valuation.map_neg]
      refine Valuation.map_sum_lt _ one_ne_zero fun i hi => ?_
      have hi' := Finset.mem_Ico.mp hi
      exact hprod i i (hwi i (Finset.mem_range.mpr hi'.2) hi'.1)
    exact absurd hwm (ne_of_lt h2)
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0

  obtain ⟨s, hs⟩ : ∃ s : L, s = ∑ i ∈ Finset.Ico m (d + 1), c i * f ^ (i - m) := ⟨_, rfl⟩
  have hws : w s = 1 := by
    have hrest : w (∑ i ∈ Finset.Ico (m + 1) (d + 1), c i * f ^ (i - m)) < w (c m) := by
      rw [hwm]
      refine Valuation.map_sum_lt _ one_ne_zero fun i hi => ?_
      have hi' := Finset.mem_Ico.mp hi
      exact hprod i (i - m) (hwi i (Finset.mem_range.mpr hi'.2) (by omega))
    rw [hs, Finset.sum_eq_sum_Ico_succ_bot hmd, Nat.sub_self, pow_zero, mul_one,
      Valuation.map_add_eq_of_lt_left _ hrest, hwm]
  have hsE : s ∈ E := by
    rw [hs]
    exact sum_mem fun i _ => mul_mem (hc i ▸ fracW_eval₂_mem σ E hσE hjE _) (pow_mem hfE _)
  have hsO : s ∈ O := (O.valuation_le_one_iff s).mp hws.le
  have hsO' : s⁻¹ ∈ O := (O.valuation_le_one_iff _).mp (by rw [map_inv₀]; exact le_of_eq (by rw [hws, inv_one]))
  have hfs : f * s = (∑ i ∈ Finset.Ico (m - 1) (d + 1), c i * f ^ (i - (m - 1))) - c (m - 1) := by
    rw [Finset.sum_eq_sum_Ico_succ_bot (show m - 1 < d + 1 by omega), Nat.sub_self, pow_zero,
      mul_one, Nat.sub_add_cancel hm1, add_sub_cancel_left, hs, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := (Finset.mem_Ico.mp hi).1
    rw [mul_left_comm, ← pow_succ', show i - m + 1 = i - (m - 1) by omega]
  have hs0 : s ≠ 0 := (Valuation.ne_zero_iff w).mp (by rw [hws]; exact one_ne_zero)
  refine ⟨f * s, s, ?_, ?_, mul_mem hfE hsE, hsE, hs0, hsO, hsO', rfl⟩
  · rw [hfs]
    refine (fracW_isIntegral_tail c hcA d f hrel' (m - 1)).sub ?_
    obtain ⟨b, hb⟩ := hcA (m - 1)
    rw [← hb]
    exact isIntegral_algebraMap
  · rw [hs]
    exact fracW_isIntegral_tail c hcA d f hrel' m

private theorem fracW_exists_relation {K₀ L : Type*} [Field K₀] [Field L] (σ : K₀ →+* L) {j y f : L}
    (hy : ∃ P : Polynomial (Polynomial ℤ), P.Monic ∧
      P.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom L) j) y = 0)
    (hf : f ∈ Subfield.closure (Set.range σ ∪ {j, y})) :
    ∃ (d : ℕ) (G : ℕ → K₀[X]), (∃ i ∈ Finset.range (d + 1), G i ≠ 0) ∧
      ∑ i ∈ Finset.range (d + 1), (G i).eval₂ σ j * f ^ i = 0 := by
  classical
  letI : Algebra K₀ L := σ.toAlgebra
  have hσ : algebraMap K₀ L = σ := rfl
  have haeval : ∀ p : K₀[X], aeval j p = p.eval₂ σ j := fun p => rfl
  have hjM : j ∈ K₀⟮j⟯ := IntermediateField.mem_adjoin_simple_self K₀ j

  have hyM : IsIntegral K₀⟮j⟯ y := by
    obtain ⟨P, hPm, hPy⟩ := hy
    let θ : Polynomial ℤ →+* K₀⟮j⟯ := Polynomial.eval₂RingHom (Int.castRingHom K₀⟮j⟯) ⟨j, hjM⟩
    refine ⟨P.map θ, hPm.map θ, ?_⟩
    have hθ : (algebraMap K₀⟮j⟯ L).comp θ = Polynomial.eval₂RingHom (Int.castRingHom L) j := by
      refine Polynomial.ringHom_ext (fun a => ?_) ?_
      · simp [θ]
      · simp [θ]
    rw [Polynomial.eval₂_map, hθ]
    exact hPy
  haveI : FiniteDimensional K₀⟮j⟯ K₀⟮j⟯⟮y⟯ := IntermediateField.adjoin.finiteDimensional hyM

  have hfK : f ∈ K₀⟮j, y⟯ := by
    rw [← IntermediateField.mem_toSubfield, IntermediateField.adjoin_toSubfield, hσ]
    exact hf
  have hfM : f ∈ K₀⟮j⟯⟮y⟯ := by
    have : f ∈ IntermediateField.restrictScalars K₀ K₀⟮j⟯⟮y⟯ := by
      rw [IntermediateField.adjoin_simple_adjoin_simple]
      exact hfK
    exact this
  have hfint : IsIntegral K₀⟮j⟯ f := by
    have h := (IsIntegral.of_finite K₀⟮j⟯ (⟨f, hfM⟩ : K₀⟮j⟯⟮y⟯)).algebraMap (B := L)
    exact h
  obtain ⟨P₁, hP₁m, hP₁f⟩ := hfint

  have hcoef : ∀ i, ∃ r s : K₀[X], aeval j s ≠ 0 ∧
      ((P₁.coeff i : K₀⟮j⟯) : L) = aeval j r / aeval j s := by
    intro i
    obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff K₀ _).mp (P₁.coeff i).2
    by_cases hs : aeval j s = 0
    · refine ⟨0, 1, by simp, ?_⟩
      rw [hrs, hs, div_zero]
      simp
    · exact ⟨r, s, hs, hrs⟩
  choose r s hs hrs using hcoef
  have hD : ∏ l ∈ Finset.range (P₁.natDegree + 1), aeval j (s l) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun l _ => hs l
  refine ⟨P₁.natDegree, fun i => r i * ∏ l ∈ (Finset.range (P₁.natDegree + 1)).erase i, s l,
    ⟨P₁.natDegree, Finset.self_mem_range_succ _, ?_⟩, ?_⟩
  ·
    intro h
    have hn1 : ((P₁.coeff P₁.natDegree : K₀⟮j⟯) : L) = 1 := by
      rw [Polynomial.Monic.coeff_natDegree hP₁m]
      rfl
    have hrn : aeval j (r P₁.natDegree) = aeval j (s P₁.natDegree) := by
      have := hrs P₁.natDegree
      rw [hn1, eq_div_iff (hs _), one_mul] at this
      exact this.symm
    have h' := congrArg (aeval j) h
    rw [map_zero, map_mul, map_prod, hrn] at h'
    rw [← Finset.mul_prod_erase _ (fun l => aeval j (s l))
      (Finset.self_mem_range_succ P₁.natDegree)] at hD
    exact hD h'
  ·
    have hev : ∑ i ∈ Finset.range (P₁.natDegree + 1),
        ((P₁.coeff i : K₀⟮j⟯) : L) * f ^ i = 0 := by
      rw [Polynomial.eval₂_eq_sum_range] at hP₁f
      exact hP₁f
    have key : ∀ i ∈ Finset.range (P₁.natDegree + 1),
        (r i * ∏ l ∈ (Finset.range (P₁.natDegree + 1)).erase i, s l).eval₂ σ j * f ^ i
          = (∏ l ∈ Finset.range (P₁.natDegree + 1), aeval j (s l)) *
              (((P₁.coeff i : K₀⟮j⟯) : L) * f ^ i) := by
      intro i hi
      rw [← haeval, map_mul, map_prod, hrs i,
        ← Finset.mul_prod_erase _ (fun l => aeval j (s l)) hi]
      field_simp
      rw [mul_div_assoc, div_self (hs i), mul_one]
    rw [Finset.sum_congr rfl key, ← Finset.mul_sum, hev, mul_zero]

private theorem fracW_coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (N : ℕ)
    [NeZero N] (x : LaurentSeries R) :
    coeffMap φ (qExpand R N x) = qExpand S N (coeffMap φ x) := by
  ext m
  by_cases h : (N : ℤ) ∣ m
  · obtain ⟨m, rfl⟩ := h
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd N _ h, qExpand_coeff_of_not_dvd N _ h, map_zero]

end FracWHelpers

theorem solution
    {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] (hqN : ¬ q ∣ N)
    (k₀ : Subfield k) (v : Place k (modularFunctionFieldC k N))
    (hv : (jGeomGen k N : ↥(modularFunctionFieldC k N)) ∈ v.toValuationSubring)
    (f : ↥(modularFunctionFieldC k N))
    (hf₀ : f ∈ Subfield.closure (Set.range (fun c : ↥k₀ => algebraMap k ↥(modularFunctionFieldC k N) (c : k)) ∪
          {(jGeomGen k N : ↥(modularFunctionFieldC k N)), (jNGeomGen k N : ↥(modularFunctionFieldC k N))}))
    (hf : f ∈ v.toValuationSubring) :
    ∃ a s : ↥(modularFunctionFieldC k N),
      IsIntegral ↥(Algebra.adjoin k ({jGeomGen k N, jNGeomGen k N} : Set ↥(modularFunctionFieldC k N))) a ∧
      IsIntegral ↥(Algebra.adjoin k ({jGeomGen k N, jNGeomGen k N} : Set ↥(modularFunctionFieldC k N))) s ∧
      a ∈ Subfield.closure (Set.range (fun c : ↥k₀ => algebraMap k ↥(modularFunctionFieldC k N) (c : k)) ∪
          {(jGeomGen k N : ↥(modularFunctionFieldC k N)), (jNGeomGen k N : ↥(modularFunctionFieldC k N))}) ∧
      s ∈ Subfield.closure (Set.range (fun c : ↥k₀ => algebraMap k ↥(modularFunctionFieldC k N) (c : k)) ∪
          {(jGeomGen k N : ↥(modularFunctionFieldC k N)), (jNGeomGen k N : ↥(modularFunctionFieldC k N))}) ∧
      (∀ n : ℤ, ((a : ↥(modularFunctionFieldC k N)) : LaurentSeries k).coeff n ∈ k₀) ∧
      (∀ n : ℤ, ((s : ↥(modularFunctionFieldC k N)) : LaurentSeries k).coeff n ∈ k₀) ∧
      s ≠ 0 ∧ s ∈ v.toValuationSubring ∧ s⁻¹ ∈ v.toValuationSubring ∧
      f * s = a := by
  classical
  obtain ⟨data⟩ := nonempty_modularPolynomialData N

  let σ : ↥k₀ →+* ↥(modularFunctionFieldC k N) :=
    (algebraMap k ↥(modularFunctionFieldC k N)).comp k₀.subtype
  have hσ : ∀ c : ↥k₀, σ c = algebraMap k ↥(modularFunctionFieldC k N) (c : k) := fun _ => rfl
  have hσr : Set.range (fun c : ↥k₀ => algebraMap k ↥(modularFunctionFieldC k N) (c : k)) = Set.range σ :=
    rfl
  rw [hσr] at hf₀ ⊢
  have hFL : ∀ x : ↥(modularFunctionFieldC k N),
      algebraMap ↥(modularFunctionFieldC k N) (LaurentSeries k) x = (x : LaurentSeries k) := fun _ => rfl
  have hcomp : (algebraMap ↥(modularFunctionFieldC k N) (LaurentSeries k)).comp σ
      = (algebraMap k (LaurentSeries k)).comp k₀.subtype :=
    RingHom.ext fun c => (IsScalarTower.algebraMap_apply k ↥(modularFunctionFieldC k N)
      (LaurentSeries k) (c : k)).symm

  have hinj : ∀ p : Polynomial ↥k₀, p.eval₂ σ (jGeomGen k N) = 0 → p = 0 := by
    intro p hp
    have h1 := congrArg (algebraMap ↥(modularFunctionFieldC k N) (LaurentSeries k)) hp
    rw [map_zero, Polynomial.hom_eval₂, hcomp, hFL, coe_jGeomGen, ← Polynomial.eval₂_map,
      ← Polynomial.aeval_def] at h1
    have h2 := (transcendental_iff.mp (transcendental_jqModC k)) _ h1
    exact (Polynomial.map_eq_zero_iff k₀.subtype.injective).mp h2

  have hy : ∃ P : Polynomial (Polynomial ℤ), P.Monic ∧
      P.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ↥(modularFunctionFieldC k N)) (jGeomGen k N))
        (jNGeomGen k N) = 0 := by
    refine ⟨data.Φ, data.monic, ?_⟩
    apply (algebraMap ↥(modularFunctionFieldC k N) (LaurentSeries k)).injective
    have hθ : (algebraMap ↥(modularFunctionFieldC k N) (LaurentSeries k)).comp
        (Polynomial.eval₂RingHom (Int.castRingHom ↥(modularFunctionFieldC k N)) (jGeomGen k N))
        = evalAtJGeom k := by
      refine Polynomial.ringHom_ext (fun a => ?_) ?_
      · simp [evalAtJGeom]
      · rw [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, evalAtJGeom_X, hFL,
          coe_jGeomGen]
    rw [map_zero, Polynomial.hom_eval₂, hθ, hFL, coe_jNGeomGen]
    exact eval_int_eq_zero_geom k data

  obtain ⟨d, G, hG, hrel⟩ := fracW_exists_relation σ hy hf₀

  have hA : ∀ p : Polynomial ↥k₀, p.eval₂ σ (jGeomGen k N) ∈ Set.range (algebraMap
      ↥(Algebra.adjoin k ({jGeomGen k N, jNGeomGen k N} : Set ↥(modularFunctionFieldC k N)))
      ↥(modularFunctionFieldC k N)) := by
    intro p
    refine ⟨⟨p.eval₂ σ (jGeomGen k N), ?_⟩, rfl⟩
    exact fracW_eval₂_mem σ (Algebra.adjoin k ({jGeomGen k N, jNGeomGen k N} : Set ↥(modularFunctionFieldC k N)))
      (fun c => Subalgebra.algebraMap_mem _ (c : k)) (Algebra.subset_adjoin (Set.mem_insert _ _)) p

  obtain ⟨a, s, ha, hs, haE, hsE, hs0, hsO, hsO', hfs⟩ := fracW_core σ v.toValuationSubring
    (fun c => v.algebraMap_mem' (c : k)) hv hf hinj hA
    (Subfield.closure (Set.range σ ∪ {jGeomGen k N, jNGeomGen k N}))
    (fun c => Subfield.subset_closure (Or.inl ⟨c, rfl⟩))
    (Subfield.subset_closure (Or.inr (Set.mem_insert _ _))) hf₀ G hG hrel

  have hcoeff : ∀ x ∈ Subfield.closure (Set.range σ ∪ {jGeomGen k N, jNGeomGen k N}),
      ∀ n : ℤ, ((x : ↥(modularFunctionFieldC k N)) : LaurentSeries k).coeff n ∈ k₀ := by
    intro x hx n
    let T : Subfield ↥(modularFunctionFieldC k N) :=
      ((coeffMap k₀.subtype).fieldRange).comap (algebraMap ↥(modularFunctionFieldC k N) (LaurentSeries k))
    have hmemT : ∀ z : ↥(modularFunctionFieldC k N),
        (∃ y, coeffMap k₀.subtype y = (z : LaurentSeries k)) → z ∈ (T : Set ↥(modularFunctionFieldC k N)) := by
      intro z h
      show z ∈ T
      rw [Subfield.mem_comap, RingHom.mem_fieldRange]
      exact h
    have hjq : coeffMap k₀.subtype (jqModC ↥k₀) = jqModC k := map_jqModC k₀.subtype
    have hT : Subfield.closure (Set.range σ ∪ {jGeomGen k N, jNGeomGen k N}) ≤ T := by
      refine Subfield.closure_le.mpr ?_
      rintro z (⟨c, rfl⟩ | rfl | rfl)
      · refine hmemT _ ⟨HahnSeries.single 0 c, ?_⟩
        rw [coeffMap_single, ← hFL, hσ, ← IsScalarTower.algebraMap_apply,
          algebraMap_laurentSeries_eq_single]
        rfl
      · exact hmemT _ ⟨jqModC ↥k₀, by rw [hjq, coe_jGeomGen]⟩
      · refine hmemT _ ⟨jqNModC ↥k₀ N, ?_⟩
        rw [coe_jNGeomGen]
        simp only [jqNModC]
        rw [fracW_coeffMap_qExpand, hjq]
    have hx' : x ∈ T := hT hx
    rw [Subfield.mem_comap, RingHom.mem_fieldRange] at hx'
    obtain ⟨y, hy⟩ := hx'
    rw [hFL] at hy
    rw [← hy, coeffMap_coeff]
    exact (y.coeff n).2
  exact ⟨a, s, ha, hs, haE, hsE, hcoeff a haE, hcoeff s hsE, hs0, hsO, hsO', hfs⟩

end S_ModularCurve_exists_ne_zero_mul_eq_isIntegral_of_mem_closure_of_mem_valuationSubring
end P2MW
export P2MW.S_ModularCurve_exists_ne_zero_mul_eq_isIntegral_of_mem_closure_of_mem_valuationSubring (solution)
