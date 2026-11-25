-- Prove2me | solution 1 for GlobalTheory.UnramOrder.card_coker_eq_pow_addVal_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:23:26.434986+00:00
-- url     : https://prove2.me/submissions/461b1efd-c00a-4be1-99da-830e7ce11a41

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableSpanSpanOfDetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardCokernelUnramifiedOrderMatrixOfDetBase
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.UnramOrder
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
open Ideal in
private lemma card_quotient_span_eq_card_residueField_pow_addVal {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {a : R} (ha : a ≠ 0) :
    Nat.card (R ⧸ Ideal.span {a}) = Nat.card (IsLocalRing.ResidueField R) ^
      (IsDiscreteValuationRing.addVal R a).toNat := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  have hm : IsLocalRing.maximalIdeal R = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hspan : Ideal.span {(u : R) * ϖ ^ n} = IsLocalRing.maximalIdeal R ^ n := by
    rw [Ideal.span_singleton_mul_left_unit u.isUnit, hm, Ideal.span_singleton_pow]
  have hv : IsDiscreteValuationRing.addVal R ((u : R) * ϖ ^ n) = n := by
    rw [IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_uniformizer hϖ, IsDiscreteValuationRing.addVal_eq_zero_of_unit u]
    simp
  have hne : IsLocalRing.maximalIdeal R ≠ ⊥ := by
    rw [hm, Ne, Ideal.span_singleton_eq_bot]
    exact hϖ.ne_zero
  rw [hv, hspan, ← Submodule.cardQuot_apply, cardQuot_pow_of_prime hne, Submodule.cardQuot_apply]
  simp
  rfl
end GlobalTheory.UnramOrder
end

set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.UnramOrder
open ValuativeRel MeasureTheory
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.UnramOrder
namespace _root_.GlobalTheory.UnramOrder
theorem _root_.solution {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Free R M]
    [Module.Finite R M] (f : M →ₗ[R] M) (hf : LinearMap.det f ≠ 0) :
    Nat.card (M ⧸ LinearMap.range f) = Nat.card (IsLocalRing.ResidueField R) ^
      (IsDiscreteValuationRing.addVal R (LinearMap.det f)).toNat := by
  classical
  let b := Module.Free.chooseBasis R M
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hx0
    apply hf
    rw [← LinearMap.det_toMatrix b]
    refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨b.repr x, fun h => hx0 ?_, ?_⟩
    · have h' : b.repr x = 0 := by
        ext i
        exact congrFun h i
      simpa using h'
    · rw [LinearMap.toMatrix_mulVec_repr, hx, map_zero]
      rfl
  have hrank : Module.finrank R (LinearMap.range f) = Module.finrank R M :=
    LinearMap.finrank_range_of_inj hinj
  let T := Submodule.smithNormalFormTopBasis b hrank
  let B := Submodule.smithNormalFormBotBasis b hrank
  let a := Submodule.smithNormalFormCoeffs b hrank
  let e : M ≃ₗ[R] LinearMap.range f := T.equiv B (Equiv.refl _)
  let g : M →ₗ[R] M := (LinearMap.range f).subtype ∘ₗ e.toLinearMap
  have hgT : ∀ i, g (T i) = a i • T i := by
    intro i
    simp [g, e, Module.Basis.equiv_apply, B, T, a, Submodule.smithNormalFormBotBasis_def]
  have hdetg : LinearMap.det g = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix T]
    have hmat : LinearMap.toMatrix T T g = Matrix.diagonal a := by
      ext i j
      rw [LinearMap.toMatrix_apply, hgT, map_smul, T.repr_self, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij, Finsupp.single_apply, Ne.symm hij]
    rw [hmat, Matrix.det_diagonal]
  let h : M →ₗ[R] M := e.symm.toLinearMap ∘ₗ f.rangeRestrict
  have hfgh : f = g ∘ₗ h := by
    ext x
    simp [g, h]
  have hsurj : Function.Surjective h := e.symm.surjective.comp f.surjective_rangeRestrict
  have hbij : Function.Bijective h :=
    ⟨OrzechProperty.injective_of_surjective_endomorphism h hsurj, hsurj⟩
  have hdeth : IsUnit (LinearMap.det h) := by
    have h1 := LinearEquiv.isUnit_det' (LinearEquiv.ofBijective h hbij)
    have h2 : ((LinearEquiv.ofBijective h hbij : M ≃ₗ[R] M) : M →ₗ[R] M) = h :=
      LinearMap.ext fun _ => rfl
    rwa [h2] at h1
  have hdet : LinearMap.det f = (∏ i, a i) * LinearMap.det h := by
    rw [hfgh, LinearMap.det_comp, hdetg]
  have ha : ∀ i, a i ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero b hrank
  have key : ∀ s : Finset (Module.Free.ChooseBasisIndex R M),
      (IsDiscreteValuationRing.addVal R (∏ i ∈ s, a i)).toNat =
        ∑ i ∈ s, (IsDiscreteValuationRing.addVal R (a i)).toNat := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, IsDiscreteValuationRing.addVal_mul,
        ENat.toNat_add, ih]
      · exact IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr (ha i)
      · exact IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr
          (Finset.prod_ne_zero_iff.mpr fun j _ => ha j)
  rw [Nat.card_congr (Submodule.quotientEquivPiSpan (LinearMap.range f) b hrank).toEquiv,
    Nat.card_pi]
  rw [Finset.prod_congr rfl fun i _ =>
    card_quotient_span_eq_card_residueField_pow_addVal (Submodule.smithNormalFormCoeffs_ne_zero b hrank i)]
  have hu : IsDiscreteValuationRing.addVal R (LinearMap.det h) = 0 := by
    have h3 := IsDiscreteValuationRing.addVal_eq_zero_of_unit hdeth.unit
    rwa [IsUnit.unit_spec] at h3
  rw [Finset.prod_pow_eq_pow_sum, hdet, IsDiscreteValuationRing.addVal_mul, hu, add_zero]
  exact congrArg _ (key Finset.univ).symm
end _root_.GlobalTheory.UnramOrder
end GlobalTheory.UnramOrder
