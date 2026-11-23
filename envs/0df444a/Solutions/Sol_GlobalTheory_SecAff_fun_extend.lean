-- Prove2me | solution 1 for GlobalTheory.SecAff.fun_extend
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:50:14.734793+00:00
-- url     : https://prove2.me/submissions/5405bfa1-f81e-4eda-b2e7-e4bfad4d676d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSectionsSpanAffine
import Theorems.Thm_GlobalTheory_SecAff_rs_rs
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
    (hφ : φ.opensRange = X.basicOpen f) {W : X.Opens} (hW : IsAffineOpen W) {W' : X'.Opens}
    (h : W' ≤ φ ⁻¹ᵁ W) (h' : φ ⁻¹ᵁ W ≤ W') (t : Γ(X', W')) :
    ∃ (N : ℕ) (x : Γ(X, W)), pa φ h x = pa φ (le_pre_top φ) f ^ N * t := by
  have hb : X.basicOpen (rs (le_top : W ≤ ⊤) f) = W ⊓ X.basicOpen f := X.basicOpen_res f _
  have hle : W' ≤ φ ⁻¹ᵁ X.basicOpen (rs (le_top : W ≤ ⊤) f) := by
    rw [hb, ← hφ]
    exact fun y hy => ⟨h hy, ⟨y, rfl⟩⟩
  obtain ⟨z, rfl⟩ := (pa_bijective φ hle ((φ.preimage_mono (X.basicOpen_le _)).trans h')
    (by rw [hb, hφ]; exact inf_le_right)).2 t
  obtain ⟨N, x, e⟩ := exists_eq_pow_mul_of_isAffineOpen X W hW _ z
  replace e : rs (X.basicOpen_le _) x =
    rs (X.basicOpen_le _) (rs (le_top : W ≤ ⊤) f) ^ N * z := e
  refine ⟨N, x, ?_⟩
  have := congrArg (pa φ hle) e
  rw [map_mul, map_pow, rs_rs, pa_rs, pa_rs] at this
  exact this
end GlobalTheory.SecAff
