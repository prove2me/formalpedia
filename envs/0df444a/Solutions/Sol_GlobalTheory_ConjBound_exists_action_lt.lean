-- Prove2me | solution 1 for GlobalTheory.ConjBound.exists_action_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:40:32.145781+00:00
-- url     : https://prove2.me/submissions/a382e101-2ae9-40a2-aabb-7ee733c8b3dd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_EqZeroOfSumEmbeddingMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ImAdjointOfSpan
import Theorems.Thm_GlobalTheory_ConjBound_im_adjoint_of_span
import Theorems.Thm_GlobalTheory_ConjBound_entry_comm
import Theorems.Thm_GlobalTheory_ConjBound_re_lt_of_comm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.ConjBound
open GlobalTheory.EigenNorm
variable {g : ℕ}
namespace GlobalTheory.ConjBound
theorem _root_.solution :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Q : D.La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (a : 𝓞 E) (κ : ℕ), (∀ (c : 𝓞 E) x i, Q (c • x) i = ty i (c : E) * Q x i) → (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = D.EF x y) → (∀ τ : E →+* ℂ, ‖τ (a : E)‖ ^ 2 < κ) → ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q (a • x)) ∧ ∀ y, y ≠ 0 → (hermForm Hm (F y) (F y)).re < κ * (hermForm Hm y y).re := by
  intro E _ _ _ H D g ty Q Hm a κ hlin ⟨_, _, hspan, _, hpos, him⟩ hκ
  let t : Fin g → ℂ := fun i => ty i (a : E)
  have h1 : ∀ x, t * Q x = Q (a • x) := fun x => funext fun i => (hlin a x i).symm
  have h2 : ∀ x, star t * Q x = Q (H.bar a • x) := fun x => funext fun i => by
    rw [hlin, H.bar_eq, IsCMField.complexEmbedding_complexConj]; rfl
  refine ⟨LinearMap.mulLeft ℂ t, h1, fun y hy => ?_⟩
  refine re_lt_of_comm Hm t κ hpos (entry_comm Hm t (im_adjoint_of_span Hm t (star t) _ hspan ?_))
    (fun i => hκ (ty i)) y hy
  rintro _ ⟨x, rfl⟩ _ ⟨x', rfl⟩
  rw [h1, h2, him, him, D.adj]
end GlobalTheory.ConjBound
