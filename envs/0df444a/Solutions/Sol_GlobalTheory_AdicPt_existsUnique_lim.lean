-- Prove2me | solution 1 for GlobalTheory.AdicPt.existsUnique_lim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:36:24.762639+00:00
-- url     : https://prove2.me/submissions/92bf893e-4c2e-4669-89e4-cdd7bb5b7cfd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ChartPointCongruence_EqOfMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueLim
import Theorems.Thm_GlobalTheory_AdicPt_scheme_ext
import Theorems.Thm_GlobalTheory_AdicPt_scheme_lim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AdicPt
open IsLocalRing
variable {R : Type} [CommRing R] [IsLocalRing R] {a : R}
namespace GlobalTheory.AdicPt
theorem _root_.solution : ∀ (O R : Type) [CommRing O] [CommRing R] [Algebra O R] [IsLocalRing R] (a : R), ¬ IsUnit a → IsAdicComplete (Ideal.span {a}) R → ∀ (X : Over (Spec (CommRingCat.of O))) (x : ∀ m : ℕ, specO O (R ⧸ Ideal.span {a ^ m}) ⟶ X), (∀ m : ℕ, ptMap (Ideal.Quotient.factorₐ O (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow a (Nat.le_succ m)))) ≫ x (m + 1) = x m) → ∃! Q : specO O R ⟶ X, ∀ m : ℕ, ptMap (Ideal.Quotient.mkₐ O (Ideal.span {a ^ m})) ≫ Q = x m := by
  intro O R _ _ _ _ a ha hc X x hx
  obtain ⟨Q, hQ⟩ := scheme_lim ha hc (Y := X.left) (fun m => (x m).left)
    (fun m => congrArg CommaMorphism.left (hx m))
  have hw : Q ≫ X.hom = (specO O R).hom := by
    refine scheme_ext ha hc _ _ fun m => ?_
    rw [← Category.assoc, hQ]
    exact (Over.w (x m)).trans (Over.w (ptMap (Ideal.Quotient.mkₐ O (Ideal.span {a ^ m})))).symm
  refine ⟨Over.homMk Q hw, fun m => Over.OverMorphism.ext (hQ m), fun Q' hQ' => Over.OverMorphism.ext ?_⟩
  refine scheme_ext ha hc _ _ fun m => ?_
  exact (congrArg CommaMorphism.left (hQ' m)).trans (hQ m).symm
end GlobalTheory.AdicPt
