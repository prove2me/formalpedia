-- Prove2me | solution 1 for ModularCurve.slot_restrictAlong_heckeBetaBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/6e794d45-5279-53e1-bbec-f0a4f564c304

import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_QAdicPlace
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Theorems.Thm_ModularCurve_slot_ord_of_algHom_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_Place_one_le_ramificationIndexAlong
import Theorems.Thm_ModularCurve_minpoly_jqN_map_eq_prod_slots
import Theorems.Thm_ModularCurve_finrank_adjoin_jqN_eq_dedekindPsi
import Theorems.Thm_ModularCurve_functionFieldGeneration
import Theorems.Thm_ModularCurve_laurentBaseChange_adjoin_pair
import Theorems.Thm_ModularCurve_exists_phiIrreducible_of_finrank_eq
import Theorems.Thm_ModularCurve_PhiGen_splits_prime_at_slot_of_isPrimitiveRoot
import Theorems.Thm_ModularCurve_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_coeffEmb_jq
import Theorems.Thm_ModularCurve_coeffEmb_jqN
import Theorems.Thm_ModularCurve_order_qExpand
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_slot_restrictAlong_heckeBetaBar
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

open ModularCurve AlgebraicCurve

namespace SlotRestrictBeta

variable {K : Type*} [Field K]

private theorem order_eq_of_coeff {x : LaurentSeries K} {m : ℤ} (h1 : x.coeff m ≠ 0)
    (h2 : ∀ i < m, x.coeff i = 0) : x.order = m := by
  have hx : x ≠ 0 := fun h => h1 (by rw [h, HahnSeries.coeff_zero])
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero h1) ?_
  by_contra! h
  exact hx (HahnSeries.coeff_order_eq_zero.mp (h2 _ h))

private theorem order_qTwist (v : Kˣ) (f : LaurentSeries K) : (qTwist v f).order = f.order := by
  rcases eq_or_ne f 0 with rfl | hf
  · rw [map_zero]
  have h1 : ∀ (u : Kˣ) (g : LaurentSeries K), g ≠ 0 → (qTwist u g).order ≤ g.order :=
    fun u g hg => HahnSeries.order_le_of_coeff_ne_zero (by
      rw [qTwist_coeff]
      exact mul_ne_zero (Units.ne_zero _) (mt HahnSeries.coeff_order_eq_zero.mp hg))
  refine le_antisymm (h1 v f hf) ?_
  have h2 := h1 v⁻¹ (qTwist v f) ((map_ne_zero_iff _ (qTwist_injective v)).mpr hf)
  rwa [qTwist_qTwist, inv_mul_cancel, qTwist_one_apply] at h2

private noncomputable def qExpandAlgK (M : ℕ) [NeZero M] :
    LaurentSeries K →ₐ[K] LaurentSeries K where
  __ := qExpand K M
  commutes' r := by
    show qExpand K M (algebraMap K (LaurentSeries K) r) = algebraMap K (LaurentSeries K) r
    rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero]

private theorem qExpandAlgK_apply (M : ℕ) [NeZero M] (f : LaurentSeries K) :
    qExpandAlgK M f = qExpand K M f := rfl

private noncomputable def qTwistAlgK (v : Kˣ) : LaurentSeries K →ₐ[K] LaurentSeries K where
  __ := qTwist v
  commutes' r := by
    show qTwist v (algebraMap K (LaurentSeries K) r) = algebraMap K (LaurentSeries K) r
    rw [algebraMap_laurentSeries_eq_single, qTwist_single, zpow_zero, Units.val_one, one_mul]

private theorem qTwistAlgK_apply (v : Kˣ) (f : LaurentSeries K) :
    qTwistAlgK v f = qTwist v f := rfl

private theorem descend {F : Type*} [Field F] [Algebra K F]
    (Φ : F →ₐ[K] LaurentSeries K) (E : LaurentSeries K →ₐ[K] LaurentSeries K)
    (hE : Function.Injective E) (hΦ : ∀ x, Φ x ∈ E.range) :
    ∃ Φ₀ : F →ₐ[K] LaurentSeries K, ∀ x, E (Φ₀ x) = Φ x := by
  have hΦ' : ∀ x, ∃ y, E y = Φ x := fun x => (AlgHom.mem_range E).mp (hΦ x)
  choose g hg using hΦ'
  refine ⟨{ toFun := g, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_,
            commutes' := ?_ }, fun x => hg x⟩
  · exact hE (by rw [hg, map_one, map_one])
  · intro x y
    exact hE (by rw [hg, map_mul, map_mul, hg, hg])
  · exact hE (by rw [hg, map_zero, map_zero])
  · intro x y
    exact hE (by rw [hg, map_add, map_add, hg, hg])
  · intro r
    exact hE (by rw [hg, AlgHom.commutes, AlgHom.commutes])

private theorem gcd_level_eq {N ℓ a a₀ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hN : N ≠ 0)
    (ha₀ : a₀ ∣ N) (haa : a₀ * Nat.gcd a ℓ = a) :
    Nat.gcd a (N * ℓ / a) = Nat.gcd a₀ (N / a₀) := by
  obtain ⟨c, hc⟩ := ha₀
  have ha₀0 : a₀ ≠ 0 := fun h => hN (by rw [hc, h, zero_mul])
  have hℓa₀ : Nat.Coprime ℓ a₀ :=
    (Nat.Prime.coprime_iff_not_dvd hℓ).mpr fun h => hℓN (hc ▸ h.mul_right c)
  have hℓc : Nat.Coprime ℓ c :=
    (Nat.Prime.coprime_iff_not_dvd hℓ).mpr fun h => hℓN (hc ▸ h.mul_left a₀)
  have hNa₀ : N / a₀ = c := by rw [hc, Nat.mul_div_cancel_left c (Nat.pos_of_ne_zero ha₀0)]
  rw [hNa₀]

  rcases (Nat.dvd_prime hℓ).mp (Nat.gcd_dvd_right a ℓ) with h1 | hℓ'
  ·
    rw [h1, mul_one] at haa
    subst haa
    have : N * ℓ / a₀ = c * ℓ := by
      rw [hc, mul_assoc, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero ha₀0)]
    rw [this]
    exact Nat.Coprime.gcd_mul_right_cancel_right c hℓa₀
  ·
    rw [hℓ'] at haa
    subst haa
    have : N * ℓ / (a₀ * ℓ) = c := by
      rw [hc, show a₀ * c * ℓ = a₀ * ℓ * c by ring,
        Nat.mul_div_cancel_left c (Nat.pos_of_ne_zero (mul_ne_zero ha₀0 hℓ.ne_zero))]
    rw [this]
    exact Nat.Coprime.gcd_mul_right_cancel a₀ hℓc

variable [Algebra ℚ K]

private theorem coeff_slot_pow (v : Kˣ) (A : ℕ) [NeZero A] (n : ℕ) :
    ((qExpand K A (qTwist v (coeffEmb K jq))) ^ n).coeff (-((A * n : ℕ) : ℤ)) =
        ((v ^ (-(n : ℤ)) : Kˣ) : K) ∧
      ∀ i < -((A * n : ℕ) : ℤ), ((qExpand K A (qTwist v (coeffEmb K jq))) ^ n).coeff i = 0 := by
  have _ := ‹Algebra ℚ K›
  rw [← map_pow, ← map_pow, ← map_pow]
  constructor
  · rw [show -((A * n : ℕ) : ℤ) = (A : ℤ) * (-(n : ℤ)) by push_cast; ring, qExpand_coeff_mul,
      qTwist_coeff, coeffEmb_coeff, coeff_jq_pow_self, map_one, mul_one]
  · intro i hi
    by_cases hdvd : (A : ℤ) ∣ i
    · obtain ⟨m, rfl⟩ := hdvd
      have hA : (0 : ℤ) < A := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne A)
      have hm : m < -(n : ℤ) := by
        refine lt_of_mul_lt_mul_left ?_ hA.le
        rw [mul_neg]
        exact_mod_cast hi
      rw [qExpand_coeff_mul, qTwist_coeff, coeffEmb_coeff, coeff_jq_pow_of_lt hm, map_zero,
        mul_zero]
    · exact qExpand_coeff_of_not_dvd A _ hdvd

private theorem order_slot (v : Kˣ) (A : ℕ) [NeZero A] :
    (qExpand K A (qTwist v (coeffEmb K jq))).order = -(A : ℤ) := by
  obtain ⟨h1, h2⟩ := coeff_slot_pow (K := K) v A 1
  rw [pow_one, mul_one] at h1 h2
  exact order_eq_of_coeff (by rw [h1]; exact Units.ne_zero _) h2

private theorem level_eq_of_slot_eq {A A' : ℕ} [NeZero A] [NeZero A'] {u u' : Kˣ}
    (h : qExpand K A (qTwist u (coeffEmb K jq)) = qExpand K A' (qTwist u' (coeffEmb K jq))) :
    A = A' := by
  have ho := congrArg HahnSeries.order h
  rw [order_slot, order_slot, neg_inj] at ho
  exact_mod_cast ho

private theorem twist_eq_of_slot_eq {A : ℕ} [NeZero A] {u u' : Kˣ}
    (h : qExpand K A (qTwist u (coeffEmb K jq)) = qExpand K A (qTwist u' (coeffEmb K jq))) :
    u = u' := by
  obtain ⟨h1, -⟩ := coeff_slot_pow (K := K) u A 1
  obtain ⟨h1', -⟩ := coeff_slot_pow (K := K) u' A 1
  rw [pow_one] at h1 h1'
  rw [h, h1'] at h1
  have hu : u' ^ (-(1 : ℤ)) = u ^ (-(1 : ℤ)) := Units.ext h1
  rw [zpow_neg, zpow_one, zpow_neg, zpow_one, inv_inj] at hu
  exact hu.symm

private theorem comp_eval₂RingHom_int {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (x : A) :
    φ.comp (Polynomial.eval₂RingHom (Int.castRingHom A) x) =
      Polynomial.eval₂RingHom (Int.castRingHom B) (φ x) :=
  Polynomial.ringHom_ext' (RingHom.ext_int _ _) (by simp)

private theorem map_eval₂_eval₂ {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (Φ : Polynomial (Polynomial ℤ)) (x y : A) :
    φ (Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom A) x) y) =
      Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom B) (φ x)) (φ y) := by
  rw [Polynomial.hom_eval₂, comp_eval₂RingHom_int]

private theorem evalAtJ_eq :
    evalAtJ = Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℚ)) jq :=
  Polynomial.ringHom_ext' (RingHom.ext_int _ _) (by simp)

private theorem exists_of_eval_map_prod_prod_eq_zero {R S : Type*} [CommRing R] [CommRing S]
    [IsDomain S] (φ : R →+* S) {α γ : Type*} (s : Finset α) (t : α → Finset γ) (c : α → γ → R)
    (z : S) (h : ((∏ a ∈ s, ∏ b ∈ t a, (Polynomial.X - Polynomial.C (c a b))).map φ).eval z = 0) :
    ∃ a ∈ s, ∃ b ∈ t a, z = φ (c a b) := by
  rw [Polynomial.map_prod, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at h
  obtain ⟨a, ha, h⟩ := h
  rw [Polynomial.map_prod, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at h
  obtain ⟨b, hb, h⟩ := h
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, sub_eq_zero] at h
  exact ⟨a, ha, b, hb, h⟩

section Relations

variable (K)

private theorem rel_map (M d : ℕ) [NeZero M] [NeZero d] (hd : d ∣ M) (data : ModularPolynomialData d)
    {S : Type*} [CommRing S] (φ : laurentBaseChange K (modularFunctionFieldFull M) →+* S) :
    data.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom S)
        (φ ⟨coeffEmb K jq, coeffEmb_mem_laurentBaseChange K (jq_mem_full M)⟩))
      (φ ⟨coeffEmb K (jqN d), coeffEmb_mem_laurentBaseChange K (jqd_mem_full M hd)⟩) = 0 := by
  set jb : laurentBaseChange K (modularFunctionFieldFull M) :=
    ⟨coeffEmb K jq, coeffEmb_mem_laurentBaseChange K (jq_mem_full M)⟩
  set jd : laurentBaseChange K (modularFunctionFieldFull M) :=
    ⟨coeffEmb K (jqN d), coeffEmb_mem_laurentBaseChange K (jqd_mem_full M hd)⟩

  have hK : data.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) (coeffEmb K jq))
      (coeffEmb K (jqN d)) = 0 := by
    have h := congrArg (coeffEmb K) data.eval_eq_zero
    rwa [map_zero, evalAtJ_eq, map_eval₂_eval₂] at h
  have hF : data.Φ.eval₂ (Polynomial.eval₂RingHom
      (Int.castRingHom (laurentBaseChange K (modularFunctionFieldFull M))) jb) jd = 0 := by
    apply (algebraMap (laurentBaseChange K (modularFunctionFieldFull M)) (LaurentSeries K)).injective
    rw [map_zero, map_eval₂_eval₂]
    exact hK
  have h := congrArg φ hF
  rwa [map_zero, map_eval₂_eval₂] at h

private theorem iota_jl_cases (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) (N * ℓ))
    (ι : laurentBaseChange K (modularFunctionFieldFull (N * ℓ)) →ₐ[K] LaurentSeries K)
    (hι₁ : ι ⟨coeffEmb K jq, coeffEmb_mem_laurentBaseChange K (jq_mem_full (N * ℓ))⟩ =
        qExpand K (N * ℓ) (coeffEmb K jq)) :
    ι ⟨coeffEmb K (jqN ℓ), coeffEmb_mem_laurentBaseChange K (jqd_mem_full (N * ℓ) (dvd_mul_left ℓ N))⟩ =
        qExpand K (ℓ * (ℓ * N)) (jqModC K) ∨
      ∃ B, B < ℓ ∧
        ι ⟨coeffEmb K (jqN ℓ), coeffEmb_mem_laurentBaseChange K (jqd_mem_full (N * ℓ) (dvd_mul_left ℓ N))⟩ =
          qExpand K N (qTwist ((ζ ^ N) ^ B) (jqModC K)) := by
  have hℓ : ℓ.Prime := Fact.out
  obtain ⟨data, -⟩ := exists_phiIrreducible_of_finrank_eq ℓ (finrank_adjoin_jqN_eq_dedekindPsi ℓ)
  have hζu : IsPrimitiveRoot ζ (N * ℓ) := IsPrimitiveRoot.coe_units_iff.mp hζ
  have hζℓ : IsPrimitiveRoot ((ζ ^ N : Kˣ) : K) ℓ :=
    IsPrimitiveRoot.coe_units_iff.mpr (hζu.pow (Nat.pos_of_ne_zero (NeZero.ne _)) rfl)
  have hsplit := PhiGen.splits_prime_at_slot_of_isPrimitiveRoot ℓ (ζ ^ N) hζℓ data N 1
  have hrel : data.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
      (ι ⟨coeffEmb K jq, coeffEmb_mem_laurentBaseChange K (jq_mem_full (N * ℓ))⟩))
      (ι ⟨coeffEmb K (jqN ℓ),
        coeffEmb_mem_laurentBaseChange K (jqd_mem_full (N * ℓ) (dvd_mul_left ℓ N))⟩) = 0 :=
    rel_map K (N * ℓ) ℓ (dvd_mul_left ℓ N) data ι.toRingHom
  rw [hι₁] at hrel
  have hinner : qExpand K (N * ℓ) (coeffEmb K jq) = qExpand K (ℓ * N) (qTwist ((1 : Kˣ) ^ ℓ) (jqModC K)) := by
    rw [one_pow, qTwist_one_apply, coeffEmb_jq, qExpand_congr (mul_comm N ℓ)]
  rw [hinner, ← Polynomial.eval_map, hsplit, Polynomial.eval_mul, mul_eq_zero, Polynomial.eval_prod,
    Finset.prod_eq_zero_iff] at hrel
  rcases hrel with h | ⟨B, hB, h⟩
  · left
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero, one_pow,
      qTwist_one_apply] at h
    exact h
  · right
    refine ⟨B, Finset.mem_range.mp hB, ?_⟩
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero, one_mul] at h
    exact h

private theorem full_eq_of_generation (d : ℕ) [NeZero d] :
    modularFunctionField d = modularFunctionFieldFull d := by
  refine le_antisymm (modularFunctionField_le_full d) ?_
  rw [modularFunctionFieldFull, IntermediateField.adjoin_le_iff]
  rintro x ⟨d', hd', hdvd, rfl⟩
  exact functionFieldGeneration d d' hdvd hd'

private theorem minpoly_eq_toAdjoin {N : ℕ} [NeZero N] (data : ModularPolynomialData N)
    (hirr : PhiIrreducible data) :
    minpoly (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (jqN N) = data.toAdjoin := by
  have haeval : Polynomial.aeval (jqN N) data.toAdjoin = 0 := by
    rw [Polynomial.aeval_def, ModularPolynomialData.toAdjoin, Polynomial.eval₂_map,
      algebraMap_comp_evalAtJGen]
    exact data.eval_eq_zero
  exact (minpoly.eq_of_irreducible_of_monic hirr haeval data.toAdjoin_monic).symm

private theorem prod_slots (N : ℕ) [NeZero N] (ζ₀ : Kˣ) (hζ₀ : IsPrimitiveRoot (ζ₀ : K) N) :
    ∃ data : ModularPolynomialData N,
      data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
          (qExpand K N (coeffEmb K jq))) =
        ∏ a ∈ N.divisors, ∏ b ∈ (Finset.range (N / a)).filter
            (fun b => Nat.gcd (Nat.gcd a b) (N / a) = 1),
          (Polynomial.X - Polynomial.C (if h : a = 0 then 0 else
            letI : NeZero a := ⟨h⟩; qExpand K (a * a) (qTwist (ζ₀ ^ (b * a)) (coeffEmb K jq)))) := by
  obtain ⟨data, hirr⟩ :=
    exists_phiIrreducible_of_finrank_eq N (finrank_adjoin_jqN_eq_dedekindPsi N)
  refine ⟨data, ?_⟩
  have hall : ∀ d : ℕ, d ∣ N → ∀ [NeZero d],
      Module.finrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
          (IntermediateField.adjoin (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
            ({jqN d} : Set (LaurentSeries ℚ))) = dedekindPsi d ∧
        modularFunctionField d = modularFunctionFieldFull d :=
    fun d _ => ⟨finrank_adjoin_jqN_eq_dedekindPsi d, full_eq_of_generation d⟩
  have hprod := minpoly_jqN_map_eq_prod_slots (K := K) N ζ₀ hζ₀ hall
  rw [minpoly_eq_toAdjoin data hirr, ModularPolynomialData.toAdjoin, Polynomial.map_map] at hprod
  have hF : (((coeffEmb K).comp (qExpand ℚ N)).comp
        (algebraMap (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
          (LaurentSeries ℚ))).comp evalAtJGen =
      Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) (qExpand K N (coeffEmb K jq)) := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp only [RingHom.coe_comp, Function.comp_apply, evalAtJGen, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_X]
    exact coeffEmb_qExpand K N jq
  rw [hF] at hprod
  exact hprod

private theorem forall_mem_range (N : ℕ) [NeZero N]
    (Φ : laurentBaseChange K (modularFunctionFieldFull N) →ₐ[K] LaurentSeries K)
    (E : LaurentSeries K →ₐ[K] LaurentSeries K)
    (h1 : Φ ⟨coeffEmb K jq, coeffEmb_mem_laurentBaseChange K (jq_mem_full N)⟩ ∈ E.range)
    (h2 : Φ ⟨coeffEmb K (jqN N), coeffEmb_mem_laurentBaseChange K (jqd_mem_full N (dvd_refl N))⟩ ∈
      E.range) :
    ∀ x, Φ x ∈ E.range := by
  intro x
  set T : IntermediateField K (laurentBaseChange K (modularFunctionFieldFull N)) :=
    E.fieldRange.comap Φ with hT
  have hmem : ∀ y, y ∈ T ↔ Φ y ∈ E.range := fun y =>
    (AlgHom.mem_fieldRange (f := E) (y := Φ y)).trans (AlgHom.mem_range E).symm
  have hgen := laurentBaseChange_adjoin_pair K N (functionFieldGeneration N)
  have hsub : ({jqModC K, jqNModC K N} : Set (LaurentSeries K)) ⊆ (IntermediateField.lift T) := by
    rintro _ (rfl | rfl)
    · have h : coeffEmb K jq ∈ IntermediateField.lift T :=
        (IntermediateField.mem_lift
          (⟨coeffEmb K jq, coeffEmb_mem_laurentBaseChange K (jq_mem_full N)⟩ :
            laurentBaseChange K (modularFunctionFieldFull N))).mpr ((hmem _).mpr h1)
      rwa [coeffEmb_jq] at h
    · have h : coeffEmb K (jqN N) ∈ IntermediateField.lift T :=
        (IntermediateField.mem_lift
          (⟨coeffEmb K (jqN N), coeffEmb_mem_laurentBaseChange K (jqd_mem_full N (dvd_refl N))⟩ :
            laurentBaseChange K (modularFunctionFieldFull N))).mpr ((hmem _).mpr h2)
      rwa [coeffEmb_jqN] at h
  have hx : (x : LaurentSeries K) ∈ IntermediateField.lift T := by
    have hx' : (x : LaurentSeries K) ∈ IntermediateField.adjoin K ({jqModC K, jqNModC K N} :
        Set (LaurentSeries K)) := by
      rw [← hgen]
      exact x.2
    exact IntermediateField.adjoin_le_iff.mpr hsub hx'
  exact (hmem x).mp ((IntermediateField.mem_lift x).mp hx)

end Relations

section Core

variable (K)

private theorem beta_core (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) (N * ℓ)) (a b : ℕ) [NeZero a]
    (ι : laurentBaseChange K (modularFunctionFieldFull (N * ℓ)) →ₐ[K] LaurentSeries K)
    (hι₁ : ι ⟨coeffEmb K jq, coeffEmb_mem_laurentBaseChange K (jq_mem_full (N * ℓ))⟩ =
        qExpand K (N * ℓ) (coeffEmb K jq))
    (hι₂ : ι ⟨coeffEmb K (jqN (N * ℓ)),
        coeffEmb_mem_laurentBaseChange K (jqd_mem_full (N * ℓ) (dvd_refl (N * ℓ)))⟩ =
        qExpand K (a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq))) :
    ∃ (a₀ b₀ k : ℕ) (_ : NeZero a₀) (E : LaurentSeries K →ₐ[K] LaurentSeries K),
      a₀ ∣ N ∧ a₀ * Nat.gcd a ℓ = a ∧ k = Nat.gcd a ℓ ^ 2 ∧
      Function.Injective E ∧ (∀ f, (E f).order = (k : ℤ) * f.order) ∧
      (∀ x, ι (heckeBetaBar K N ℓ x) ∈ E.range) ∧
      E (qExpand K N (coeffEmb K jq)) =
        ι (heckeBetaBar K N ℓ ⟨coeffEmb K jq, coeffEmb_mem_laurentBaseChange K (jq_mem_full N)⟩) ∧
      E (qExpand K (a₀ * a₀) (qTwist ((ζ ^ ℓ) ^ (b₀ * a₀)) (coeffEmb K jq))) =
        ι (heckeBetaBar K N ℓ ⟨coeffEmb K (jqN N),
          coeffEmb_mem_laurentBaseChange K (jqd_mem_full N (dvd_refl N))⟩) ∧
      ℓ / Nat.gcd a ℓ * b₀ ≡ b [MOD Nat.gcd a₀ (N / a₀)] := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have hN0 : N ≠ 0 := NeZero.ne N
  have ha0 : a ≠ 0 := NeZero.ne a
  have hζu : IsPrimitiveRoot ζ (N * ℓ) := IsPrimitiveRoot.coe_units_iff.mp hζ
  have hζN : IsPrimitiveRoot ((ζ ^ ℓ : Kˣ) : K) N :=
    IsPrimitiveRoot.coe_units_iff.mpr (hζu.pow (Nat.pos_of_ne_zero (NeZero.ne _)) (mul_comm N ℓ))
  set F := laurentBaseChange K (modularFunctionFieldFull N) with hF
  set β := heckeBetaBar K N ℓ with hβdef
  set jb : F := ⟨coeffEmb K jq, coeffEmb_mem_laurentBaseChange K (jq_mem_full N)⟩ with hjb
  set jbN : F := ⟨coeffEmb K (jqN N), coeffEmb_mem_laurentBaseChange K (jqd_mem_full N (dvd_refl N))⟩
    with hjbN

  have hβ1 : β jb = ⟨coeffEmb K (jqN ℓ),
      coeffEmb_mem_laurentBaseChange K (jqd_mem_full (N * ℓ) (dvd_mul_left ℓ N))⟩ := by
    refine Subtype.ext ?_
    show qExpand K ℓ (coeffEmb K jq) = coeffEmb K (qExpand ℚ ℓ jq)
    rw [coeffEmb_qExpand]
  have hβ2 : β jbN = ⟨coeffEmb K (jqN (N * ℓ)),
      coeffEmb_mem_laurentBaseChange K (jqd_mem_full (N * ℓ) (dvd_refl (N * ℓ)))⟩ := by
    refine Subtype.ext ?_
    show qExpand K ℓ (coeffEmb K (qExpand ℚ N jq)) = coeffEmb K (qExpand ℚ (N * ℓ) jq)
    rw [coeffEmb_qExpand, coeffEmb_qExpand, qExpand_qExpand, qExpand_congr (mul_comm ℓ N)]
  have hz : ι (β jbN) = qExpand K (a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq)) := by
    rw [hβ2]; exact hι₂

  obtain ⟨dataN, hprod⟩ := prod_slots K N (ζ ^ ℓ) hζN
  have hrelN : dataN.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
      (ι (β jb))) (ι (β jbN)) = 0 :=
    rel_map K N N (dvd_refl N) dataN (ι.comp β).toRingHom
  rw [hz] at hrelN

  rcases iota_jl_cases K N ℓ ζ hζ ι hι₁ with hy | ⟨B, -, hy⟩
  ·
    rw [hβ1, hy] at hrelN
    have hmap : (dataN.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
        (qExpand K N (coeffEmb K jq)))).map (qExpand K (ℓ * ℓ)) =
        dataN.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
          (qExpand K (ℓ * (ℓ * N)) (jqModC K))) := by
      rw [Polynomial.map_map, comp_eval₂RingHom_int, qExpand_qExpand, coeffEmb_jq,
        qExpand_congr (mul_assoc ℓ ℓ N)]
    have hroot : ((∏ a' ∈ N.divisors, ∏ b' ∈ (Finset.range (N / a')).filter
        (fun b' => Nat.gcd (Nat.gcd a' b') (N / a') = 1),
          (Polynomial.X - Polynomial.C (if h : a' = 0 then 0 else
            letI : NeZero a' := ⟨h⟩;
            qExpand K (a' * a') (qTwist ((ζ ^ ℓ) ^ (b' * a')) (coeffEmb K jq))))).map
          (qExpand K (ℓ * ℓ))).eval (qExpand K (a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq))) = 0 := by
      rw [← hprod, hmap, Polynomial.eval_map]
      exact hrelN
    obtain ⟨a₀, ha₀, b₀, -, hzE⟩ := exists_of_eval_map_prod_prod_eq_zero _ _ _ _ _ hroot
    obtain ⟨ha₀N, -⟩ := Nat.mem_divisors.mp ha₀
    have ha₀ne : a₀ ≠ 0 := fun h => hN0 (Nat.eq_zero_of_zero_dvd (h ▸ ha₀N))
    haveI : NeZero a₀ := ⟨ha₀ne⟩
    rw [dif_neg ha₀ne, qExpand_qExpand] at hzE

    have haℓ : a = ℓ * a₀ := by
      have h := level_eq_of_slot_eq hzE
      exact Nat.mul_self_inj.mp (by rw [h]; ring)
    have hgcd : Nat.gcd a ℓ = ℓ :=
      Nat.dvd_antisymm (Nat.gcd_dvd_right _ _) (Nat.dvd_gcd ⟨a₀, haℓ⟩ dvd_rfl)

    rw [qExpand_congr (show ℓ * ℓ * (a₀ * a₀) = a * a by rw [haℓ]; ring)] at hzE
    have hu := twist_eq_of_slot_eq hzE
    rw [← pow_mul, pow_eq_pow_iff_modEq, ← hζu.eq_orderOf] at hu

    have hmod : b₀ ≡ b [MOD Nat.gcd a₀ (N / a₀)] := by
      have h1 : (ℓ * a₀) * b ≡ (ℓ * a₀) * b₀ [MOD (ℓ * a₀) * (N / a₀)] := by
        have hNℓ : (ℓ * a₀) * (N / a₀) = N * ℓ := by
          rw [mul_assoc, Nat.mul_div_cancel' ha₀N, mul_comm]
        rw [hNℓ]
        have e1 : ℓ * a₀ * b = b * a := by rw [haℓ]; ring
        have e2 : ℓ * a₀ * b₀ = ℓ * (b₀ * a₀) := by ring
        rw [e1, e2]
        exact hu
      have h2 := Nat.ModEq.mul_left_cancel' (mul_ne_zero hℓ.ne_zero ha₀ne) h1
      exact (Nat.ModEq.of_dvd (Nat.gcd_dvd_right a₀ (N / a₀)) h2).symm
    refine ⟨a₀, b₀, ℓ * ℓ, inferInstance, qExpandAlgK (ℓ * ℓ), ha₀N, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hgcd, haℓ, mul_comm]
    · rw [hgcd, sq]
    · exact fun x y h => (qExpand K (ℓ * ℓ)).injective h
    · intro f
      exact order_qExpand (ℓ * ℓ) f
    · refine forall_mem_range K N (ι.comp β) (qExpandAlgK (ℓ * ℓ)) ?_ ?_
      · refine (AlgHom.mem_range _).mpr ⟨qExpand K N (coeffEmb K jq), ?_⟩
        show qExpand K (ℓ * ℓ) (qExpand K N (coeffEmb K jq)) = ι (β jb)
        rw [hβ1, hy, qExpand_qExpand, coeffEmb_jq, qExpand_congr (mul_assoc ℓ ℓ N)]
      · refine (AlgHom.mem_range _).mpr
          ⟨qExpand K (a₀ * a₀) (qTwist ((ζ ^ ℓ) ^ (b₀ * a₀)) (coeffEmb K jq)), ?_⟩
        show qExpand K (ℓ * ℓ) _ = ι (β jbN)
        rw [hz, qExpand_qExpand, qExpand_congr (show ℓ * ℓ * (a₀ * a₀) = a * a by rw [haℓ]; ring)]
        exact hzE.symm
    · show qExpand K (ℓ * ℓ) (qExpand K N (coeffEmb K jq)) = ι (β jb)
      rw [hβ1, hy, qExpand_qExpand, coeffEmb_jq, qExpand_congr (mul_assoc ℓ ℓ N)]
    · show qExpand K (ℓ * ℓ) _ = ι (β jbN)
      rw [hz, qExpand_qExpand, qExpand_congr (show ℓ * ℓ * (a₀ * a₀) = a * a by rw [haℓ]; ring)]
      exact hzE.symm
    · rwa [hgcd, Nat.div_self hℓ.pos, one_mul]
  ·
    rw [hβ1, hy] at hrelN
    have hBN : (ζ ^ B) ^ (N : ℤ) = (ζ ^ N) ^ B := by
      rw [zpow_natCast, ← pow_mul, ← pow_mul, mul_comm]
    have hmap : (dataN.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
        (qExpand K N (coeffEmb K jq)))).map (qTwist (ζ ^ B)) =
        dataN.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
          (qExpand K N (qTwist ((ζ ^ N) ^ B) (jqModC K)))) := by
      rw [Polynomial.map_map, comp_eval₂RingHom_int, qTwist_qExpand, hBN, coeffEmb_jq]
    have hroot : ((∏ a' ∈ N.divisors, ∏ b' ∈ (Finset.range (N / a')).filter
        (fun b' => Nat.gcd (Nat.gcd a' b') (N / a') = 1),
          (Polynomial.X - Polynomial.C (if h : a' = 0 then 0 else
            letI : NeZero a' := ⟨h⟩;
            qExpand K (a' * a') (qTwist ((ζ ^ ℓ) ^ (b' * a')) (coeffEmb K jq))))).map
          (qTwist (ζ ^ B))).eval (qExpand K (a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq))) = 0 := by
      rw [← hprod, hmap, Polynomial.eval_map]
      exact hrelN
    obtain ⟨a₀, ha₀, b₀, -, hzE⟩ := exists_of_eval_map_prod_prod_eq_zero _ _ _ _ _ hroot
    obtain ⟨ha₀N, -⟩ := Nat.mem_divisors.mp ha₀
    have ha₀ne : a₀ ≠ 0 := fun h => hN0 (Nat.eq_zero_of_zero_dvd (h ▸ ha₀N))
    haveI : NeZero a₀ := ⟨ha₀ne⟩
    rw [dif_neg ha₀ne, qTwist_qExpand, qTwist_qTwist] at hzE

    have haa : a = a₀ := Nat.mul_self_inj.mp (level_eq_of_slot_eq hzE)
    subst haa

    have hgcd : Nat.gcd a ℓ = 1 :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr fun h => hℓN (h.trans ha₀N))

    have hu := twist_eq_of_slot_eq hzE
    rw [zpow_natCast, ← pow_mul, ← pow_mul, ← pow_add, pow_eq_pow_iff_modEq, ← hζu.eq_orderOf] at hu

    have hmod : ℓ * b₀ ≡ b [MOD Nat.gcd a (N / a)] := by
      have h1 : a * b ≡ a * (B * a + ℓ * b₀) [MOD a * (ℓ * (N / a))] := by
        have hNℓ : a * (ℓ * (N / a)) = N * ℓ := by
          rw [mul_left_comm, Nat.mul_div_cancel' ha₀N, mul_comm]
        rw [hNℓ]
        have e1 : a * b = b * a := mul_comm a b
        have e2 : a * (B * a + ℓ * b₀) = B * (a * a) + ℓ * (b₀ * a) := by ring
        rw [e1, e2]
        exact hu
      have h2 := Nat.ModEq.mul_left_cancel' ha0 h1
      have h3 : b ≡ B * a + ℓ * b₀ [MOD Nat.gcd a (N / a)] :=
        Nat.ModEq.of_dvd ((Nat.gcd_dvd_right a (N / a)).trans (dvd_mul_left (N / a) ℓ)) h2
      have h4 : B * a + ℓ * b₀ ≡ 0 + ℓ * b₀ [MOD Nat.gcd a (N / a)] :=
        Nat.ModEq.add_right _ (Nat.modEq_zero_iff_dvd.mpr ((Nat.gcd_dvd_left a (N / a)).mul_left B))
      rw [zero_add] at h4
      exact (h3.trans h4).symm
    refine ⟨a, b₀, 1, inferInstance, qTwistAlgK (ζ ^ B), ha₀N, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hgcd, mul_one]
    · rw [hgcd, one_pow]
    · exact fun x y h => qTwist_injective (ζ ^ B) h
    · intro f
      rw [Nat.cast_one, one_mul]
      exact order_qTwist (ζ ^ B) f
    · intro x
      exact (AlgHom.mem_range _).mpr ⟨qTwist (ζ ^ B)⁻¹ (ι (β x)), by
        show qTwist (ζ ^ B) (qTwist (ζ ^ B)⁻¹ (ι (β x))) = ι (β x)
        rw [qTwist_qTwist, mul_inv_cancel, qTwist_one_apply]⟩
    · show qTwist (ζ ^ B) (qExpand K N (coeffEmb K jq)) = ι (β jb)
      rw [hβ1, hy, qTwist_qExpand, hBN, coeffEmb_jq]
    · show qTwist (ζ ^ B) _ = ι (β jbN)
      rw [hz, qTwist_qExpand, qTwist_qTwist]
      exact hzE.symm
    · rwa [hgcd, Nat.div_one]

end Core

section Main

variable (K)

private theorem res_main (K : Type*) [Field K] [Algebra ℚ K] (N ℓ : ℕ)
    [NeZero N] [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (hβ : HeckeBetaBarIntegral K N ℓ)
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) (N * ℓ)) (a b : ℕ) (ha : a ∣ N * ℓ) [NeZero a]
    (ι : laurentBaseChange K (modularFunctionFieldFull (N * ℓ)) →ₐ[K] LaurentSeries K)
    (hι₁ : ι ⟨coeffEmb K jq, coeffEmb_mem_laurentBaseChange K (jq_mem_full (N * ℓ))⟩ =
        qExpand K (N * ℓ) (coeffEmb K jq))
    (hι₂ : ι ⟨coeffEmb K (jqN (N * ℓ)), coeffEmb_mem_laurentBaseChange K (jqd_mem_full (N * ℓ) (dvd_refl (N * ℓ)))⟩ =
        qExpand K (a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq)))
    (W : Place K (laurentBaseChange K (modularFunctionFieldFull (N * ℓ)))) (γ : ℤ) (hγ : 0 < γ)
    (hW : ∀ x, W.ord x * γ = (ι x).order) :
    W.ramificationIndexAlong (heckeBetaBar K N ℓ) = Nat.gcd a ℓ ∧
    ∃ (a₀ b₀ : ℕ) (_ : NeZero a₀)
      (ι₀ : laurentBaseChange K (modularFunctionFieldFull N) →ₐ[K] LaurentSeries K),
      a₀ * Nat.gcd a ℓ = a ∧
      ι₀ ⟨coeffEmb K jq, coeffEmb_mem_laurentBaseChange K (jq_mem_full N)⟩ =
          qExpand K N (coeffEmb K jq) ∧
      ι₀ ⟨coeffEmb K (jqN N), coeffEmb_mem_laurentBaseChange K (jqd_mem_full N (dvd_refl N))⟩ =
          qExpand K (a₀ * a₀) (qTwist ((ζ ^ ℓ) ^ (b₀ * a₀)) (coeffEmb K jq)) ∧
      (∀ x, (W.restrictAlong (heckeBetaBar K N ℓ) hβ).ord x * ((a₀ * Nat.gcd a₀ (N / a₀) : ℕ) : ℤ)
          = (ι₀ x).order) ∧
      ℓ / Nat.gcd a ℓ * b₀ ≡ b [MOD Nat.gcd a₀ (N / a₀)] := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have hN0 : N ≠ 0 := NeZero.ne N
  set β := heckeBetaBar K N ℓ with hβdef
  obtain ⟨a₀, b₀, k, ha₀0, E, ha₀N, haa, hk, hEinj, hEord, hErange, hE₁, hE₂, hmod⟩ :=
    beta_core K N ℓ hℓN ζ hζ a b ι hι₁ hι₂
  obtain ⟨ι₀, hι₀⟩ := descend (ι.comp β) E hEinj (fun x => hErange x)
  have hι₀' : ∀ x, E (ι₀ x) = ι (β x) := fun x => hι₀ x

  have h₁ : ι₀ ⟨coeffEmb K jq, coeffEmb_mem_laurentBaseChange K (jq_mem_full N)⟩ =
      qExpand K N (coeffEmb K jq) := hEinj (by rw [hι₀', hE₁])
  have h₂ : ι₀ ⟨coeffEmb K (jqN N),
        coeffEmb_mem_laurentBaseChange K (jqd_mem_full N (dvd_refl N))⟩ =
      qExpand K (a₀ * a₀) (qTwist ((ζ ^ ℓ) ^ (b₀ * a₀)) (coeffEmb K jq)) :=
    hEinj (by rw [hι₀', hE₂])

  set W₀ := W.restrictAlong β hβ with hW₀def
  set e := W.ramificationIndexAlong β with hedef
  have hkpos : 0 < k := by
    rw [hk]
    exact pow_pos (Nat.gcd_pos_of_pos_right a hℓ.pos) 2
  have he1 : 1 ≤ e := Place.one_le_ramificationIndexAlong β hβ W
  have hrel : ∀ x, (k : ℤ) * (ι₀ x).order = (e : ℤ) * γ * W₀.ord x := fun x => by
    have h1 := hEord (ι₀ x)
    rw [hι₀'] at h1
    have h2 := hW (β x)
    rw [Place.ord_restrictAlong β hβ W x, ← hedef, ← hW₀def] at h2
    rw [← h1, ← h2]
    ring

  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W₀.toValuationSubring
  have hπ1 : W₀.ord (π : laurentBaseChange K (modularFunctionFieldFull N)) = 1 :=
    W₀.ord_coe_irreducible hπ
  set γ₀ : ℤ := (ι₀ (π : laurentBaseChange K (modularFunctionFieldFull N))).order with hγ₀def
  have hkγ₀ : (k : ℤ) * γ₀ = (e : ℤ) * γ := by
    have := hrel (π : laurentBaseChange K (modularFunctionFieldFull N))
    rw [hπ1, mul_one] at this
    exact this
  have hγ₀ : 0 < γ₀ := by
    have h : 0 < (k : ℤ) * γ₀ := by
      rw [hkγ₀]
      exact mul_pos (by exact_mod_cast he1) hγ
    exact pos_of_mul_pos_right h (by exact_mod_cast hkpos.le)
  have hW₀ : ∀ x, W₀.ord x * γ₀ = (ι₀ x).order := fun x => by
    have h := hrel x
    rw [← hkγ₀] at h
    have hk0 : (k : ℤ) ≠ 0 := by exact_mod_cast hkpos.ne'
    have : (k : ℤ) * (ι₀ x).order = (k : ℤ) * (W₀.ord x * γ₀) := by rw [h]; ring
    exact (mul_left_cancel₀ hk0 this).symm

  obtain ⟨hγ₀eq, -, -⟩ := slot_ord_of_algHom_laurentBaseChange K N (ζ ^ ℓ) a₀ b₀ ha₀N ι₀ h₁ h₂
    W₀ γ₀ hγ₀ hW₀
  obtain ⟨hγeq, -, -⟩ :=
    slot_ord_of_algHom_laurentBaseChange K (N * ℓ) ζ a b ha ι hι₁ hι₂ W γ hγ hW

  have hg := gcd_level_eq hℓ hℓN hN0 ha₀N haa
  have he : e = Nat.gcd a ℓ := by
    have hpos : (0 : ℤ) < (a₀ : ℤ) * (Nat.gcd a₀ (N / a₀) : ℕ) * (Nat.gcd a ℓ : ℕ) := by
      have h1 : 0 < a₀ := Nat.pos_of_ne_zero (NeZero.ne a₀)
      have h2 : 0 < Nat.gcd a₀ (N / a₀) := Nat.gcd_pos_of_pos_left _ h1
      have h3 : 0 < Nat.gcd a ℓ := Nat.gcd_pos_of_pos_right a hℓ.pos
      exact_mod_cast Nat.mul_pos (Nat.mul_pos h1 h2) h3
    have haZ : (a : ℤ) = (a₀ : ℤ) * (Nat.gcd a ℓ : ℕ) := by exact_mod_cast haa.symm
    have h := hkγ₀
    rw [hγ₀eq, hγeq, hg, hk, haZ] at h
    push_cast at h
    have key : ((Nat.gcd a ℓ : ℕ) : ℤ) * ((a₀ : ℤ) * (Nat.gcd a₀ (N / a₀) : ℕ) * (Nat.gcd a ℓ : ℕ)) =
        (e : ℤ) * ((a₀ : ℤ) * (Nat.gcd a₀ (N / a₀) : ℕ) * (Nat.gcd a ℓ : ℕ)) := by
      linear_combination h
    exact_mod_cast (mul_right_cancel₀ hpos.ne' key).symm
  refine ⟨he, a₀, b₀, ha₀0, ι₀, haa, h₁, h₂, fun x => ?_, hmod⟩
  rw [← hW₀ x, hγ₀eq]
  push_cast
  ring

end Main

end SlotRestrictBeta

theorem solution (K : Type*) [Field K] [Algebra ℚ K] (N ℓ : ℕ)
    [NeZero N] [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (hβ : HeckeBetaBarIntegral K N ℓ)
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) (N * ℓ)) (a b : ℕ) (ha : a ∣ N * ℓ) [NeZero a]
    (ι : laurentBaseChange K (modularFunctionFieldFull (N * ℓ)) →ₐ[K] LaurentSeries K)
    (hι₁ : ι ⟨coeffEmb K jq, coeffEmb_mem_laurentBaseChange K (jq_mem_full (N * ℓ))⟩ =
        qExpand K (N * ℓ) (coeffEmb K jq))
    (hι₂ : ι ⟨coeffEmb K (jqN (N * ℓ)), coeffEmb_mem_laurentBaseChange K (jqd_mem_full (N * ℓ) (dvd_refl (N * ℓ)))⟩ =
        qExpand K (a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq)))
    (W : Place K (laurentBaseChange K (modularFunctionFieldFull (N * ℓ)))) (γ : ℤ) (hγ : 0 < γ)
    (hW : ∀ x, W.ord x * γ = (ι x).order) :
    W.ramificationIndexAlong (heckeBetaBar K N ℓ) = Nat.gcd a ℓ ∧
    ∃ (a₀ b₀ : ℕ) (_ : NeZero a₀)
      (ι₀ : laurentBaseChange K (modularFunctionFieldFull N) →ₐ[K] LaurentSeries K),
      a₀ * Nat.gcd a ℓ = a ∧
      ι₀ ⟨coeffEmb K jq, coeffEmb_mem_laurentBaseChange K (jq_mem_full N)⟩ =
          qExpand K N (coeffEmb K jq) ∧
      ι₀ ⟨coeffEmb K (jqN N), coeffEmb_mem_laurentBaseChange K (jqd_mem_full N (dvd_refl N))⟩ =
          qExpand K (a₀ * a₀) (qTwist ((ζ ^ ℓ) ^ (b₀ * a₀)) (coeffEmb K jq)) ∧
      (∀ x, (W.restrictAlong (heckeBetaBar K N ℓ) hβ).ord x * ((a₀ * Nat.gcd a₀ (N / a₀) : ℕ) : ℤ)
          = (ι₀ x).order) ∧
      ℓ / Nat.gcd a ℓ * b₀ ≡ b [MOD Nat.gcd a₀ (N / a₀)] :=
  SlotRestrictBeta.res_main K N ℓ hℓN hβ ζ hζ a b ha ι hι₁ hι₂ W γ hγ hW

end S_ModularCurve_slot_restrictAlong_heckeBetaBar
end P2MW
export P2MW.S_ModularCurve_slot_restrictAlong_heckeBetaBar (solution)
