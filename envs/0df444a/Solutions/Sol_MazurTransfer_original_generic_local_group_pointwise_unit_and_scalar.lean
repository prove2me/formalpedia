-- Prove2me | solution 1 for MazurTransfer.original_generic_local_group_pointwise_unit_and_scalar
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-21T02:26:37.652594+00:00
-- url     : https://prove2.me/submissions/03b23518-658a-466e-adae-d8460c1a7efb

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the same selected local Picard generic group law and represented Picard law have the same identity and every natural scalar action on every original rational test scheme.
Named downstream consumer: the actual local generic point comparison and selected integral nineteen norm-kernel arithmetic labels.
-/
import Definitions.Def_MazurTransfer_OriginalPicardComparisonGroupProvidersData20261020
import Definitions.Def_MazurTransfer_Order13GoodPrimeLocalGenericGroupConstructorData
import Theorems.Thm_MazurTransfer_Order13GoodPrimeLocalGenericGroupIdentity_generic_group_law_units_equal
import Theorems.Thm_MazurTransfer_Order13GoodPrimeGenericNormGroupLaws_generic_group_law_multiplications_equal
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open MazurTransfer.Order13GoodPrimeLocalGenericGroupIdentity MazurTransfer.Order13GoodPrimeLocalGenericPicardComparison
open MazurTransfer.Order13GoodPrimeGenericNormGroupLaws
namespace MazurTransfer.OriginalGenericLocalGroupPointwiseUnitAndScalarProof20261020Boundary
end MazurTransfer.OriginalGenericLocalGroupPointwiseUnitAndScalarProof20261020Boundary
namespace MazurTransfer.OriginalGenericLocalGroupPointwiseUnitAndScalarProof20261020
variable (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104)
theorem generic_group_law_units_equal_all {T : Scheme}
    (t : T ⟶ Spec (CommRingCat.of ℚ)) :
    (genericLocalLaw q hq).one t = (genericRepresentedLaw q hq).one t := by
  have h := congrArg (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t))
    (generic_group_law_units_equal q hq)
  erw [RelativeGroupLaw.one_natural, RelativeGroupLaw.one_natural] at h
  exact h
theorem generic_group_law_nsmul_equal {T : Scheme}
    (t : T ⟶ Spec (CommRingCat.of ℚ)) (n : ℕ)
    (x : SchemeHomOver t (localGenericPicard q hq).toBase) :
    (genericLocalLaw q hq).nsmul t n x = (genericRepresentedLaw q hq).nsmul t n x := by
  induction n with
  | zero =>
    erw [RelativeGroupLaw.nsmul_zero, RelativeGroupLaw.nsmul_zero]
    exact generic_group_law_units_equal_all q hq t
  | succ n ih =>
    erw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ,
      generic_group_law_multiplications_equal, ih]
end MazurTransfer.OriginalGenericLocalGroupPointwiseUnitAndScalarProof20261020
theorem solution : (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104), ∀ {T : Scheme}
    (t : T ⟶ Spec (CommRingCat.of ℚ)),
(genericLocalLaw q hq).one t = (genericRepresentedLaw q hq).one t) ∧ (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104), ∀ {T : Scheme}
    (t : T ⟶ Spec (CommRingCat.of ℚ)) (n : ℕ)
    (x : SchemeHomOver t (localGenericPicard q hq).toBase),
(genericLocalLaw q hq).nsmul t n x = (genericRepresentedLaw q hq).nsmul t n x) := by
  exact ⟨MazurTransfer.OriginalGenericLocalGroupPointwiseUnitAndScalarProof20261020.generic_group_law_units_equal_all, MazurTransfer.OriginalGenericLocalGroupPointwiseUnitAndScalarProof20261020.generic_group_law_nsmul_equal⟩
#print axioms solution
