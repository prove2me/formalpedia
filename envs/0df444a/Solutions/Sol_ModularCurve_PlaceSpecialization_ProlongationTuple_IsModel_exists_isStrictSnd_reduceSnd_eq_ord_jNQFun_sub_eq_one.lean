-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_isStrictSnd_reduceSnd_eq_ord_jNQFun_sub_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/d07789a4-9952-5b25-b790-65403bbb10c2

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_residue_jNFun_sub_jNQFun_sub
import Theorems.Thm_AlgebraicCurve_Place_one_le_ramificationIndexAlong
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_coeff_jqModC_pow_self
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_isStrictSnd_reduceSnd_eq_ord_jNQFun_sub_eq_one
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_isStrictSnd_reduceSnd_eq_ord_jNQFun_sub_eq_one.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_single qExpand_injective qExpand_congr qExpand_qExpand jq ModularPolynomialData jqd_mem_full algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC modularFunctionFieldC PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobOnPlacesGeomLevel KroneckerCongruence jNGeomGen jNGeomGen_sub_algebraMap_ne_zero IsAffineGeomPlace coeffMap_qExpand coeff_jqModC_pow_self hasPrincipalDivisors_modularFunctionFieldBar_unconditional"
namespace DiscCoordCore
p2m_open "ModularCurve"

open Classical in

theorem existsUnique_of_mapDomain_filter_eq_one {α β : Type*} (D : α →₀ ℤ) (S : α → Prop)
    (r : α → β) (v : β)
    (hlaw : Finsupp.mapDomain r (D.filter S) v = 1)
    (hnn : ∀ W, S W → r W = v → 0 ≤ D W) :
    ∃ Q, (S Q ∧ r Q = v ∧ D Q = 1) ∧ ∀ Q', S Q' → r Q' = v → Q' ≠ Q → D Q' = 0 := by
  classical
  set x : α →₀ ℤ := D.filter S with hx
  have hxapp : ∀ W, x W = if S W then D W else 0 := fun W => by
    rw [hx, Finsupp.filter_apply]
  let g : α → ℤ := fun W => if r W = v then x W else 0
  have hxnn : ∀ W, r W = v → 0 ≤ x W := fun W hW => by
    rw [hxapp]
    split_ifs with h
    · exact hnn W h hW
    · exact le_refl _
  have hgnn : ∀ W, 0 ≤ g W := fun W => by
    show 0 ≤ (if r W = v then x W else 0)
    split_ifs with h
    · exact hxnn W h
    · exact le_refl _
  have hsum : ∑ W ∈ x.support, g W = 1 := by
    rw [← hlaw]
    unfold Finsupp.mapDomain
    rw [Finsupp.sum_apply, Finsupp.sum]
    apply Finset.sum_congr rfl
    intro W _
    simp only [g, Finsupp.single_apply]
  obtain ⟨Q, hQmem, hgQ0⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (s := x.support) (f := g) (by rw [hsum]; exact one_ne_zero)
  have hrQ : r Q = v := by
    by_contra h
    exact hgQ0 (if_neg h)
  have hgQx : g Q = x Q := if_pos hrQ
  have hSQ : S Q := by
    by_contra h
    apply hgQ0
    rw [hgQx, hxapp, if_neg h]
  have hxQ : x Q = D Q := by rw [hxapp, if_pos hSQ]
  have hle : g Q ≤ 1 := by
    have h := Finset.single_le_sum (f := g) (s := x.support) (fun W _ => hgnn W) hQmem
    rwa [hsum] at h
  have h0le : 0 ≤ D Q := hnn Q hSQ hrQ
  have hDQ1 : D Q = 1 := by
    rw [hgQx, hxQ] at hgQ0 hle
    omega
  refine ⟨Q, ⟨hSQ, hrQ, hDQ1⟩, fun Q' hS' hr' hne => ?_⟩
  by_contra h0
  have hxQ' : x Q' = D Q' := by rw [hxapp, if_pos hS']
  have hQ'mem : Q' ∈ x.support := by rw [Finsupp.mem_support_iff, hxQ']; exact h0
  have hgQ' : g Q' = D Q' := by
    show (if r Q' = v then x Q' else 0) = D Q'
    rw [if_pos hr', hxQ']
  have hpair : g Q + g Q' ≤ ∑ W ∈ x.support, g W := by
    rw [← Finset.sum_pair (Ne.symm hne)]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact hQmem
      · exact hQ'mem
    · intro y _ _
      exact hgnn y
  rw [hsum, hgQx, hxQ, hgQ', hDQ1] at hpair
  have := hnn Q' hS' hr'
  omega

theorem jqModC_pow_sub_algebraMap_ne_zero (K : Type*) [Field K] {n : ℕ} (hn : 0 < n) (c : K) :
    jqModC K ^ n - algebraMap K (LaurentSeries K) c ≠ 0 := by
  intro h
  have h1 := congrArg (fun f : LaurentSeries K => f.coeff (-(n : ℤ))) h
  rw [HahnSeries.coeff_sub, coeff_jqModC_pow_self, algebraMap_laurentSeries_eq_single,
    HahnSeries.coeff_single_of_ne (by omega), sub_zero, HahnSeries.coeff_zero] at h1
  exact one_ne_zero h1

end ModularCurve.DiscCoordCore

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_single qExpand_injective qExpand_congr qExpand_qExpand jq ModularPolynomialData jqd_mem_full algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC modularFunctionFieldC PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobOnPlacesGeomLevel KroneckerCongruence jNGeomGen jNGeomGen_sub_algebraMap_ne_zero IsAffineGeomPlace coeffMap_qExpand coeff_jqModC_pow_self hasPrincipalDivisors_modularFunctionFieldBar_unconditional"
namespace DiscCoordJN
p2m_open "ModularCurve"

local notation "𝕂" => AlgebraicClosure ℚ

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_isStrictSnd_reduceSnd_eq_ord_jNQFun_sub_eq_one.ModularCurve ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring 𝕂}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral 𝕂 N q}
  {hβ : HeckeBetaBarIntegral 𝕂 N q}

noncomputable def jNBarN (N : ℕ) [NeZero N] : modularFunctionFieldBar N :=
  ⟨coeffEmb 𝕂 (qExpand ℚ N jq), coeffEmb_mem_laurentBaseChange 𝕂 (jqd_mem_full N (dvd_refl N))⟩

noncomputable def jNFun (N q : ℕ) [NeZero N] [NeZero q] : modularFunctionFieldBar (N * q) :=
  ⟨coeffEmb 𝕂 (qExpand ℚ N jq), coeffEmb_mem_laurentBaseChange 𝕂 (jqd_mem_full (N * q) (dvd_mul_right N q))⟩

noncomputable def jNQFun (N q : ℕ) [NeZero N] [NeZero q] : modularFunctionFieldBar (N * q) :=
  ⟨coeffEmb 𝕂 (qExpand ℚ (N * q) jq), coeffEmb_mem_laurentBaseChange 𝕂 (jqd_mem_full (N * q) (dvd_refl (N * q)))⟩

theorem heckeAlphaBar_jNBarN : heckeAlphaBar 𝕂 N q (jNBarN N) = jNFun N q :=
  Subtype.ext (coe_heckeAlphaBar N q _)

theorem heckeBetaBar_jNBarN : heckeBetaBar 𝕂 N q (jNBarN N) = jNQFun N q := by
  apply Subtype.ext
  rw [coe_heckeBetaBar]
  show qExpand 𝕂 q (coeffEmb 𝕂 (qExpand ℚ N jq)) = coeffEmb 𝕂 (qExpand ℚ (N * q) jq)
  rw [coeffEmb, ModularCurve.coeffMap_qExpand, ModularCurve.coeffMap_qExpand, qExpand_qExpand,
    qExpand_congr (mul_comm q N)]

theorem exists_ord_jNBarN_sub_pos_of_jNGeomGen_mem (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (w : Place 𝕂 (modularFunctionFieldBar N))
    (hj : jNGeomGen k N ∈ (P.sp w).toValuationSubring) :
    ∃ a : A, 0 < w.ord (jNBarN N - algebraMap 𝕂 (modularFunctionFieldBar N) (a : 𝕂)) ∧
      0 < (P.sp w).ord (jNGeomGen k N - algebraMap k (modularFunctionFieldC k N) (red a)) := by
  by_cases h : ∃ a : A, 0 < w.ord (jNBarN N - algebraMap 𝕂 (modularFunctionFieldBar N) (a : 𝕂))
  · obtain ⟨a, ha⟩ := h
    exact ⟨a, ha, P.d0_jN w a ha⟩
  · exfalso
    push Not at h
    have hpole : (P.sp w).ord (jNGeomGen k N) < 0 := P.d0_jN_pole w h
    have hnn : 0 ≤ (P.sp w).ord (jNGeomGen k N) := (P.sp w).ord_nonneg_of_mem hj
    omega

theorem ord_pos_along {F F' : Type*} [Field F] [Field F'] [Algebra 𝕂 F] [Algebra 𝕂 F']
    (φ : F →ₐ[𝕂] F') (hφ : φ.toRingHom.IsIntegral) (Q : Place 𝕂 F') (f : F)
    (h : 0 < (Q.restrictAlong φ hφ).ord f) : 0 < Q.ord (φ f) := by
  rw [Place.ord_restrictAlong φ hφ]
  have he : (0 : ℤ) < (Place.ramificationIndexAlong φ Q : ℤ) := by
    exact_mod_cast Place.one_le_ramificationIndexAlong φ hφ Q
  exact mul_pos he h

theorem jNFun_mem_of_isAffineGeomPlace_reduceFst (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Place 𝕂 (modularFunctionFieldBar (N * q))) (haff : IsAffineGeomPlace k N (P.reduceFst W)) :
    jNFun N q ∈ W.toValuationSubring := by
  obtain ⟨a, ha, -⟩ := exists_ord_jNBarN_sub_pos_of_jNGeomGen_mem P
    (W.restrictAlong (heckeAlphaBar 𝕂 N q) hα) haff.2
  have hup : 0 < W.ord (jNFun N q - algebraMap 𝕂 (modularFunctionFieldBar (N * q)) (a : 𝕂)) := by
    have e : jNFun N q - algebraMap 𝕂 (modularFunctionFieldBar (N * q)) (a : 𝕂)
        = heckeAlphaBar 𝕂 N q (jNBarN N - algebraMap 𝕂 (modularFunctionFieldBar N) (a : 𝕂)) := by
      rw [map_sub, heckeAlphaBar_jNBarN, AlgHom.commutes]
    rw [e]; exact ord_pos_along _ hα W _ ha
  have hne : jNFun N q - algebraMap 𝕂 (modularFunctionFieldBar (N * q)) (a : 𝕂) ≠ 0 := by
    intro h0; rw [h0] at hup; simp at hup
  have hmem := W.mem_of_ord_nonneg hne hup.le
  have := add_mem hmem (W.algebraMap_mem' (a : 𝕂))
  simpa using this

theorem jNQFun_mem_of_isAffineGeomPlace_reduceSnd (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Place 𝕂 (modularFunctionFieldBar (N * q))) (haff : IsAffineGeomPlace k N (P.reduceSnd W)) :
    jNQFun N q ∈ W.toValuationSubring := by
  obtain ⟨a, ha, -⟩ := exists_ord_jNBarN_sub_pos_of_jNGeomGen_mem P
    (W.restrictAlong (heckeBetaBar 𝕂 N q) hβ) haff.2
  have hup : 0 < W.ord (jNQFun N q - algebraMap 𝕂 (modularFunctionFieldBar (N * q)) (a : 𝕂)) := by
    have e : jNQFun N q - algebraMap 𝕂 (modularFunctionFieldBar (N * q)) (a : 𝕂)
        = heckeBetaBar 𝕂 N q (jNBarN N - algebraMap 𝕂 (modularFunctionFieldBar N) (a : 𝕂)) := by
      rw [map_sub, heckeBetaBar_jNBarN, AlgHom.commutes]
    rw [e]; exact ord_pos_along _ hβ W _ ha
  have hne : jNQFun N q - algebraMap 𝕂 (modularFunctionFieldBar (N * q)) (a : 𝕂) ≠ 0 := by
    intro h0; rw [h0] at hup; simp at hup
  have hmem := W.mem_of_ord_nonneg hne hup.le
  have := add_mem hmem (W.algebraMap_mem' (a : 𝕂))
  simpa using this

theorem jqNModC_pow_sub_algebraMap_ne_zero (K : Type*) [Field K] (N : ℕ) [NeZero N] {n : ℕ} (hn : 0 < n) (c : K) :
    jqNModC K N ^ n - algebraMap K (LaurentSeries K) c ≠ 0 := by
  intro h
  have e : jqNModC K N ^ n - algebraMap K (LaurentSeries K) c
      = qExpand K N (jqModC K ^ n - algebraMap K (LaurentSeries K) c) := by
    rw [map_sub, map_pow, jqNModC, algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero]
  rw [e, map_eq_zero_iff _ (qExpand_injective N)] at h
  have h1 := congrArg (fun f : LaurentSeries K => f.coeff (-(n : ℤ))) h
  rw [HahnSeries.coeff_sub, coeff_jqModC_pow_self, algebraMap_laurentSeries_eq_single,
    HahnSeries.coeff_single_of_ne (by omega), sub_zero, HahnSeries.coeff_zero] at h1
  exact one_ne_zero h1

end ModularCurve.DiscCoordJN

open ModularCurve.DiscCoordCore ModularCurve.DiscCoordJN ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
    (R : ProlongationTuple P) (hR : R.IsModel)
    (v : Place k ↥(modularFunctionFieldC k N)) (hv : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) ≠ v) (haff : IsAffineGeomPlace k N v)
    (c₂ : k) (hc : v.ord (jNGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c₂) = 1) (a : A) (ha : red a = c₂) :
    ∃ Q : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      (P.IsStrictSnd Q ∧ P.reduceSnd Q = v ∧
        Q.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (N * q) jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (N * q) (dvd_refl (N * q)))⟩ : ↥(modularFunctionFieldBar (N * q))) - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)) = 1) ∧
      ∀ Q' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.IsStrictSnd Q' → P.reduceSnd Q' = v → Q' ≠ Q →
        Q'.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (N * q) jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (N * q) (dvd_refl (N * q)))⟩ : ↥(modularFunctionFieldBar (N * q))) - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)) = 0 := by
  classical
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  obtain ⟨-, -, h₁, h₂, -, -, E₁, E₂⟩ := R.residue_jNFun_sub_jNQFun_sub hqN a
  set t := (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (N * q) jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (N * q) (dvd_refl (N * q)))⟩ : ↥(modularFunctionFieldBar (N * q)))
    - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) with ht_def
  have hres2 : R.R₂.residue ⟨t, h₂⟩ ≠ 0 := by
    intro h0
    have h' : R.residue₂ ⟨t, h₂⟩ = 0 := by rw [residue₂_apply, h0, map_zero]
    rw [E₂, ha] at h'
    exact jNGeomGen_sub_algebraMap_ne_zero k N c₂ h'
  have hres1 : R.R₁.residue ⟨t, h₁⟩ ≠ 0 := by
    intro h0
    have h' : R.residue₁ ⟨t, h₁⟩ = 0 := by rw [residue₁_apply, h0, map_zero]
    rw [E₁] at h'
    have h'' : jqNModC k N ^ q - algebraMap k (LaurentSeries k) (red a) = 0 :=
      congrArg Subtype.val h'
    exact jqNModC_pow_sub_algebraMap_ne_zero k N (Fact.out : q.Prime).pos (red a) h''
  have ht0 : t ≠ 0 := by
    intro h0
    apply hres2
    have : (⟨t, h₂⟩ : R.R₂.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hord2 : v.ord (R.residue₂ ⟨t, h₂⟩) = 1 := by rw [E₂, ha]; exact hc
  have hnn : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      P.IsStrictSnd W → P.reduceSnd W = v → 0 ≤ W.ord t := by
    intro W _ hW
    have haffW : IsAffineGeomPlace k N (P.reduceSnd W) := by rw [hW]; exact haff
    have hj : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (N * q) jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (N * q) (dvd_refl (N * q)))⟩ : ↥(modularFunctionFieldBar (N * q))) ∈ W.toValuationSubring :=
      jNQFun_mem_of_isAffineGeomPlace_reduceSnd P W haffW
    exact W.ord_nonneg_of_mem (sub_mem hj (W.algebraMap_mem' _))
  obtain ⟨D, hD, -⟩ :=
    (hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)).exists_divisor t ht0
  have hlaw : Finsupp.mapDomain P.reduceSnd (D.filter P.IsStrictSnd) v = v.ord (R.residue₂ ⟨t, h₂⟩) :=
    hR.2.1 t h₁ h₂ hres1 hres2 D hD v hv
  rw [hord2] at hlaw
  obtain ⟨Q, ⟨hS, hr, hD1⟩, huniq⟩ := existsUnique_of_mapDomain_filter_eq_one D P.IsStrictSnd P.reduceSnd v hlaw
    (fun W hSW hW => by rw [hD]; exact hnn W hSW hW)
  refine ⟨Q, ⟨hS, hr, by rw [← hD]; exact hD1⟩, fun Q' hS' hr' hne => ?_⟩
  rw [← hD]
  exact huniq Q' hS' hr' hne

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_isStrictSnd_reduceSnd_eq_ord_jNQFun_sub_eq_one
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_isStrictSnd_reduceSnd_eq_ord_jNQFun_sub_eq_one (solution)
