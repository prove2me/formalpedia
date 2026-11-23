-- Prove2me | solution 1 for GlobalTheory.SecAff.fun_kill
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:50:14.847053+00:00
-- url     : https://prove2.me/submissions/720b4895-96d3-465c-b9aa-428a2bc7350b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSectionsSpanAffine
import Theorems.Thm_GlobalTheory_SecAff_pa_bijective

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
variable {X X' X'' : Scheme.{0}}
namespace GlobalTheory.SecAff
theorem _root_.solution (φ : X' ⟶ X) [IsOpenImmersion φ] (f : Γ(X, ⊤))
    (hφ : φ.opensRange = X.basicOpen f) {W : X.Opens} (hW : IsCompact (W : Set X)) {W' : X'.Opens}
    (h : W' ≤ φ ⁻¹ᵁ W) (h' : φ ⁻¹ᵁ W ≤ W') (x : Γ(X, W)) (hx : pa φ h x = 0) :
    ∃ N : ℕ, rs (le_top : W ≤ ⊤) f ^ N * x = 0 := by
  have hb : X.basicOpen (rs (le_top : W ≤ ⊤) f) = W ⊓ X.basicOpen f := X.basicOpen_res f _
  have hle : W' ≤ φ ⁻¹ᵁ X.basicOpen (rs (le_top : W ≤ ⊤) f) := by
    rw [hb, ← hφ]
    exact fun y hy => ⟨h hy, ⟨y, rfl⟩⟩
  refine exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact X hW x _ ?_
  change rs (X.basicOpen_le _) x = 0
  apply (pa_bijective φ hle ((φ.preimage_mono (X.basicOpen_le _)).trans h')
    (by rw [hb, hφ]; exact inf_le_right)).1
  rw [pa_rs, map_zero]
  exact hx
end GlobalTheory.SecAff
