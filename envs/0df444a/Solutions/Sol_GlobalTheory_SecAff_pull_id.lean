-- Prove2me | solution 1 for GlobalTheory.SecAff.pull_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:35:53.523611+00:00
-- url     : https://prove2.me/submissions/4270bd60-6576-43c9-90ea-58d1571c9040

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSectionsSpanAffine
import Theorems.Thm_GlobalTheory_SecAff_rs_self
import Theorems.Thm_GlobalTheory_SecAff_pa_id

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SecAff
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (a : ℤ) {T T' T'' : Over S}
namespace GlobalTheory.SecAff
theorem _root_.solution (s : SecM A L a T) : pull A L a (𝟙 T) s = s := by
  ext j
  have : ∀ (φ : (T ⊗ A).left ⟶ (T ⊗ A).left) (_ : φ = 𝟙 _) (W : (T ⊗ A).left.Opens)
      (e : W ≤ φ ⁻¹ᵁ W) (x : Γ((T ⊗ A).left, W)), pa φ e x = x := by
    rintro _ rfl W e x
    rw [pa_id]
    exact rs_self _ _
  exact this _ (by rw [id_whiskerRight]; rfl) _ _ _
end GlobalTheory.SecAff
