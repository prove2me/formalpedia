-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_isStrictFst_reduceFst_eq_ord_jFun_sub_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/714ae597-3b21-5231-b9f3-5c69012c94a9

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_residue_jFun_sub_jQFun_sub
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_ord_jFun_sub_pos_of_isAffineGeomPlace_reduceFst
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_coeff_jqModC_pow_self
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_isStrictFst_reduceFst_eq_ord_jFun_sub_eq_one
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_isStrictFst_reduceFst_eq_ord_jFun_sub_eq_one.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar ModularPolynomialData algebraMap_laurentSeries_eq_single jqModC modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral frobOnPlacesGeomLevel KroneckerCongruence jGeomGen jGeomGen_sub_algebraMap_ne_zero IsAffineGeomPlace coeff_jqModC_pow_self hasPrincipalDivisors_modularFunctionFieldBar_unconditional"
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
  beta_reduce at h1
  rw [HahnSeries.coeff_sub, coeff_jqModC_pow_self, algebraMap_laurentSeries_eq_single,
    HahnSeries.coeff_single_of_ne (by omega), sub_zero, HahnSeries.coeff_zero] at h1
  exact one_ne_zero h1

end ModularCurve.DiscCoordCore

open ModularCurve.DiscCoordCore ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
    (R : ProlongationTuple P) (hR : R.IsModel)
    (v : Place k ↥(modularFunctionFieldC k N)) (hv : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) ≠ v) (haff : IsAffineGeomPlace k N v)
    (c₁ : k) (hc : v.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c₁) = 1) (a : A) (ha : red a = c₁) :
    ∃ Q : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      (P.IsStrictFst Q ∧ P.reduceFst Q = v ∧ Q.ord (ProlongationTuple.jFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)) = 1) ∧
      ∀ Q' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.IsStrictFst Q' → P.reduceFst Q' = v → Q' ≠ Q →
        Q'.ord (ProlongationTuple.jFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)) = 0 := by
  classical
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  obtain ⟨h₁, h₂, -, -, E₁, E₂, -, -⟩ := R.residue_jFun_sub_jQFun_sub hqN a
  set t := ProlongationTuple.jFun N q
    - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) with ht_def

  have hres1 : R.R₁.residue ⟨t, h₁⟩ ≠ 0 := by
    intro h0
    have h' : R.residue₁ ⟨t, h₁⟩ = 0 := by rw [residue₁_apply, h0, map_zero]
    rw [E₁, ha] at h'
    exact jGeomGen_sub_algebraMap_ne_zero k N c₁ h'
  have hres2 : R.R₂.residue ⟨t, h₂⟩ ≠ 0 := by
    intro h0
    have h' : R.residue₂ ⟨t, h₂⟩ = 0 := by rw [residue₂_apply, h0, map_zero]
    rw [E₂] at h'
    have h'' : jqModC k ^ q - algebraMap k (LaurentSeries k) (red a) = 0 :=
      congrArg Subtype.val h'
    exact jqModC_pow_sub_algebraMap_ne_zero k (Fact.out : q.Prime).pos (red a) h''
  have ht0 : t ≠ 0 := by
    intro h0
    apply hres1
    have : (⟨t, h₁⟩ : R.R₁.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]

  have hord1 : v.ord (R.residue₁ ⟨t, h₁⟩) = 1 := by rw [E₁, ha]; exact hc

  have hnn : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      P.IsStrictFst W → P.reduceFst W = v → 0 ≤ W.ord t := by
    intro W _ hW
    have haffW : IsAffineGeomPlace k N (P.reduceFst W) := by rw [hW]; exact haff
    obtain ⟨a', ha', -⟩ := P.exists_ord_jFun_sub_pos_of_isAffineGeomPlace_reduceFst W haffW
    have hne : ProlongationTuple.jFun N q - algebraMap (AlgebraicClosure ℚ)
        ↥(modularFunctionFieldBar (N * q)) (a' : AlgebraicClosure ℚ) ≠ 0 := by
      intro h0; rw [h0] at ha'; simp at ha'
    have hja : ProlongationTuple.jFun N q - algebraMap (AlgebraicClosure ℚ)
        ↥(modularFunctionFieldBar (N * q)) (a' : AlgebraicClosure ℚ) ∈ W.toValuationSubring :=
      W.mem_of_ord_nonneg hne ha'.le
    have hj : ProlongationTuple.jFun N q ∈ W.toValuationSubring := by
      have := add_mem hja (W.algebraMap_mem' (a' : AlgebraicClosure ℚ))
      simpa using this
    exact W.ord_nonneg_of_mem (sub_mem hj (W.algebraMap_mem' _))

  obtain ⟨D, hD, -⟩ :=
    (hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)).exists_divisor t ht0
  have hlaw : Finsupp.mapDomain P.reduceFst (D.filter P.IsStrictFst) v = v.ord (R.residue₁ ⟨t, h₁⟩) :=
    hR.1 t h₁ h₂ hres1 hres2 D hD v hv
  rw [hord1] at hlaw
  obtain ⟨Q, ⟨hS, hr, hD1⟩, huniq⟩ := existsUnique_of_mapDomain_filter_eq_one D P.IsStrictFst P.reduceFst v hlaw
    (fun W hSW hW => by rw [hD]; exact hnn W hSW hW)
  refine ⟨Q, ⟨hS, hr, by rw [← hD]; exact hD1⟩, fun Q' hS' hr' hne => ?_⟩
  rw [← hD]
  exact huniq Q' hS' hr' hne

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_isStrictFst_reduceFst_eq_ord_jFun_sub_eq_one
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_isStrictFst_reduceFst_eq_ord_jFun_sub_eq_one (solution)
