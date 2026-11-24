-- Prove2me | solution 1 for GlobalTheory.ExtendLineBundle.exists_pow_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:49:30.284148+00:00
-- url     : https://prove2.me/submissions/4dbebe10-bebf-49a8-a9fc-959e5784c4cd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLineBundleExtension
import Theorems.Thm_GlobalTheory_ExtendLineBundle_germ_mem
import Theorems.Thm_GlobalTheory_ExtendLineBundle_exists_section

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
noncomputable section
open GlobalTheory GlobalTheory.ExtendLineBundle
variable {X Y : Scheme.{0}} [IsIntegral X]
namespace GlobalTheory.ExtendLineBundle
theorem _root_.solution {U : X.Opens} (hU : IsAffineOpen U) (a : Γ(X, U))
    (h : genericPoint X ∈ U) (ha : genericPoint X ∈ X.basicOpen a) {t : X.functionField}
    (ht : ∀ y ∈ X.basicOpen a, t ∈ localSubring y) :
    ∃ n : ℕ, ∀ x ∈ U, X.presheaf.germ U _ h a ^ n * t ∈ localSubring x := by
  obtain ⟨s, rfl⟩ := exists_section ha ht
  obtain ⟨n, b, e⟩ := exists_eq_pow_mul_of_isAffineOpen X U hU a s
  refine ⟨n, fun x hx => ?_⟩
  have e' := congrArg (X.presheaf.germ _ _ ha) e
  rw [map_mul, map_pow] at e'
  have r : ∀ c : Γ(X, U), X.presheaf.germ _ _ ha (c |_ X.basicOpen a) =
      X.presheaf.germ U _ h c := fun c => X.presheaf.germ_res_apply _ _ _ _
  rw [r, r] at e'
  rw [← e']
  exact germ_mem hx h b
end GlobalTheory.ExtendLineBundle
