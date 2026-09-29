-- Prove2me | solution 1 for ModularCurve.LevelN.exists_algHom_laurentBaseChange_apply_eq_qExpand
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/462e8492-1441-55ad-8813-de7d0ffe5c16

import Mathlib
import Definitions.Def_ModularCurve_LevelNFunctionField
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN_qExpansion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelN_exists_algHom_laurentBaseChange_apply_eq_qExpand

set_option autoImplicit false

open scoped MatrixGroups IntermediateField
open Polynomial

noncomputable def N3Prep.qExpandAlgHom (L : Type*) [Field L] (N : ℕ) [NeZero N] :
    LaurentSeries L →ₐ[L] LaurentSeries L :=
  AlgHom.mk' (ModularCurve.qExpand L N) (fun c x => by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, LaurentSeries.algebraMap_apply,
      ModularCurve.qExpand_C])

theorem N3Prep.qExpandAlgHom_apply (L : Type*) [Field L] (N : ℕ) [NeZero N] (x : LaurentSeries L) :
    N3Prep.qExpandAlgHom L N x = ModularCurve.qExpand L N x := rfl

theorem N3Prep.exists_apply_eq_apply_smul
    {F K L : Type*} [Field F] [Field K] [Algebra F K] [Field L] [Algebra F L]
    (H : Subgroup (K ≃ₐ[F] K)) [Finite H] (E E' : K →ₐ[F] L)
    (hagree : ∀ c ∈ IntermediateField.fixedField H, E c = E' c) (x : K) :
    ∃ h : H, E' x = E ((h : K ≃ₐ[F] K) x) := by
  classical
  haveI : Fintype H := Fintype.ofFinite H
  set Q : K[X] := ∏ h : H, (X - C ((h : K ≃ₐ[F] K) x)) with hQ

  have hfix : ∀ i, Q.coeff i ∈ IntermediateField.fixedField H := by
    intro i
    rw [IntermediateField.mem_fixedField_iff]
    intro g hg
    have hmap : Q.map (g : K →+* K) = Q := by
      rw [hQ, Polynomial.map_prod]
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, RingHom.coe_coe]
      exact Fintype.prod_bijective (fun h : H => (⟨g, hg⟩ : H) * h) (Group.mulLeft_bijective _)
        _ _ fun h => rfl
    have := congrArg (fun P : K[X] => P.coeff i) hmap
    simpa only [Polynomial.coeff_map, RingHom.coe_coe] using this

  have hmapEE' : Q.map (E : K →+* L) = Q.map (E' : K →+* L) := by
    ext i
    rw [Polynomial.coeff_map, Polynomial.coeff_map, RingHom.coe_coe, RingHom.coe_coe]
    exact hagree _ (hfix i)

  have hQx : Q.eval x = 0 := by
    rw [hQ, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ (1 : H)) (by simp)
  have hroot : (Q.map (E : K →+* L)).eval (E' x) = 0 := by
    have h0 : Polynomial.eval₂ (E' : K →+* L) ((E' : K →+* L) x) Q = 0 := by
      rw [Polynomial.eval₂_hom, hQx, map_zero]
    rw [hmapEE', Polynomial.eval_map]
    simpa only [RingHom.coe_coe] using h0

  have hfac : Q.map (E : K →+* L) = ∏ h : H, (X - C (E ((h : K ≃ₐ[F] K) x))) := by
    rw [hQ, Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, RingHom.coe_coe]
  rw [hfac, eval_prod, Finset.prod_eq_zero_iff] at hroot
  obtain ⟨h, -, hh⟩ := hroot
  refine ⟨h, ?_⟩
  simpa [sub_eq_zero] using hh

theorem N3Prep.exists_algHom_comp_eq
    {F K L : Type*} [Field F] [Field K] [Algebra F K] [Field L] [Algebra F L]
    (H : Subgroup (K ≃ₐ[F] K)) [Finite H] (E E' : K →ₐ[F] L)
    (hagree : ∀ c ∈ IntermediateField.fixedField H, E c = E' c) :
    ∃ g : K →ₐ[F] K, ∀ x, E (g x) = E' x := by
  have hmem : ∀ x, E' x ∈ E.range := by
    intro x
    obtain ⟨h, hh⟩ := N3Prep.exists_apply_eq_apply_smul H E E' hagree x
    exact ⟨_, hh.symm⟩
  refine ⟨(AlgEquiv.ofInjectiveField E).symm.toAlgHom.comp (E'.codRestrict E.range hmem), fun x => ?_⟩
  have h1 := AlgEquiv.ofInjective_apply E (RingHom.injective (E : K →+* L))
    ((AlgEquiv.ofInjectiveField E).symm (E'.codRestrict E.range hmem x))
  show E ((AlgEquiv.ofInjectiveField E).symm (E'.codRestrict E.range hmem x)) = E' x
  rw [← h1]
  show (((AlgEquiv.ofInjectiveField E) ((AlgEquiv.ofInjectiveField E).symm
    (E'.codRestrict E.range hmem x))) : L) = E' x
  rw [AlgEquiv.apply_symm_apply]
  rfl

theorem solution
    (M : ℕ) [NeZero M]
    (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ModularCurve.LevelN.ring M) K]
    [IsScalarTower ℂ (ModularCurve.LevelN.ring M) K]
    [IsFractionRing (ModularCurve.LevelN.ring M) K]
    (σ : SL(2, ℤ) →* (K ≃ₐ[ℂ] K))
    (hker : σ.ker = CongruenceSubgroup.Gamma M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)))
    (hfixed : IntermediateField.fixedField σ.range =
      IntermediateField.adjoin ℂ
        ({algebraMap (ModularCurve.LevelN.ring M) K (ModularCurve.LevelN.jGen M)} : Set K))
    (E : K →ₐ[ℂ] LaurentSeries ℂ)
    (hEj : E (algebraMap (ModularCurve.LevelN.ring M) K (ModularCurve.LevelN.jGen M)) =
      ModularCurve.qExpand ℂ M (ModularCurve.jqModC ℂ))
    (Γ : Subgroup SL(2, ℤ)) (hΓ : CongruenceSubgroup.Gamma M ≤ Γ) (hT : ModularGroup.T ∈ Γ) :
    ∃ Ψ : ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ) →ₐ[ℂ] K,
      ∀ u : ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ),
        E (Ψ u) = ModularCurve.qExpand ℂ M (u : LaurentSeries ℂ) := by
  classical
  set jK := algebraMap (ModularCurve.LevelN.ring M) K (ModularCurve.LevelN.jGen M) with hjK

  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  let ι : AlgebraicClosure ℚ →+* ℂ :=
    (IsAlgClosed.lift (R := ℚ) (S := AlgebraicClosure ℚ) (M := ℂ)).toRingHom
  have h9 := ModularCurve.exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN_qExpansion
    M Γ hΓ hT ι K
  obtain ⟨Φ, E₉, hE₉j, hE₉Φ, -, -, -⟩ := h9
  have hcoeff : ∀ x : LaurentSeries ℚ,
      ModularCurve.coeffMap ι (ModularCurve.coeffEmb (AlgebraicClosure ℚ) x) =
        ModularCurve.coeffEmb ℂ x := by
    intro x
    rw [ModularCurve.coeffEmb, ModularCurve.coeffEmb, ModularCurve.coeffMap_coeffMap]
    exact ModularCurve.coeffMap_congr (RingHom.ext_rat _ _) x
  have hrange : ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ) ≤
      E₉.fieldRange.comap (N3Prep.qExpandAlgHom ℂ M) := by
    rw [ModularCurve.laurentBaseChange, IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, hx, rfl⟩
    show N3Prep.qExpandAlgHom ℂ M (ModularCurve.coeffEmb ℂ x) ∈ E₉.fieldRange
    rw [AlgHom.mem_fieldRange]
    refine ⟨Φ ⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) x,
      ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hx⟩, ?_⟩
    rw [hE₉Φ, N3Prep.qExpandAlgHom_apply, hcoeff]
  have hmem : ∀ u : ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ),
      (N3Prep.qExpandAlgHom ℂ M).comp
          (ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ)).val u ∈
        E₉.range := by
    intro u
    obtain ⟨y, hy⟩ := AlgHom.mem_fieldRange.mp (hrange u.2)
    exact ⟨y, hy⟩
  let Ψ₉ : ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ) →ₐ[ℂ] K :=
    (AlgEquiv.ofInjectiveField E₉).symm.toAlgHom.comp
      (((N3Prep.qExpandAlgHom ℂ M).comp
        (ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ)).val).codRestrict
          E₉.range hmem)
  have hΨ₉ : ∀ u, E₉ (Ψ₉ u) = ModularCurve.qExpand ℂ M (u : LaurentSeries ℂ) := by
    intro u
    set w : E₉.range := ((N3Prep.qExpandAlgHom ℂ M).comp
      (ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ)).val).codRestrict
        E₉.range hmem u with hw
    have h1 := AlgEquiv.ofInjective_apply E₉ (RingHom.injective (E₉ : K →+* LaurentSeries ℂ))
      ((AlgEquiv.ofInjectiveField E₉).symm w)
    show E₉ ((AlgEquiv.ofInjectiveField E₉).symm w) = _
    rw [← h1]
    show (((AlgEquiv.ofInjectiveField E₉) ((AlgEquiv.ofInjectiveField E₉).symm w)) : LaurentSeries ℂ) = _
    rw [AlgEquiv.apply_symm_apply]
    rfl

  haveI : σ.ker.FiniteIndex := by
    rw [hker]; exact Subgroup.finiteIndex_of_le le_sup_left
  haveI : Finite σ.range :=
    Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange σ).toEquiv

  have hagree : ∀ c ∈ IntermediateField.fixedField σ.range, E c = E₉ c := by
    intro c hc
    rw [hfixed] at hc
    obtain ⟨p, q, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff ℂ c).mp hc
    have key : ∀ (φ : K →ₐ[ℂ] LaurentSeries ℂ) (r : ℂ[X]), φ (aeval jK r) = aeval (φ jK) r :=
      fun φ r => (Polynomial.aeval_algHom_apply φ jK r).symm
    rw [map_div₀, map_div₀, key E, key E, key E₉, key E₉, hEj, hE₉j]

  obtain ⟨g, hg⟩ := N3Prep.exists_algHom_comp_eq σ.range E E₉ hagree
  exact ⟨g.comp Ψ₉, fun u => by rw [AlgHom.comp_apply, hg, hΨ₉]⟩

end S_ModularCurve_LevelN_exists_algHom_laurentBaseChange_apply_eq_qExpand
end P2MW
export P2MW.S_ModularCurve_LevelN_exists_algHom_laurentBaseChange_apply_eq_qExpand (solution)
