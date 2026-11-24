-- Prove2me | solution 1 for GlobalTheory.GenTorsor.unit_glue_opens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:18:12.70735+00:00
-- url     : https://prove2.me/submissions/7d7b8e02-916e-448a-b4a3-17742b77a795

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsRepresentableOfCover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.GenTorsor
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.GenTorsor
theorem _root_.solution {J : Type*} (V : X.Opens) (W : J → X.Opens) (hW : ∀ i, W i ≤ V)
    (hc : V ≤ iSup W) (u : ∀ i, Γ(X, W i)ˣ)
    (hh : ∀ i j, res (inf_le_left : W i ⊓ W j ≤ W i) (u i) = res inf_le_right (u j)) :
    ∃ s : Γ(X, V)ˣ, ∀ i, res (hW i) s = u i := by
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' W V (fun i => homOfLE (hW i)) hc
    (fun i => (u i).val) (fun i j => congrArg Units.val (hh i j))
  obtain ⟨s', hs', -⟩ := X.sheaf.existsUnique_gluing' W V (fun i => homOfLE (hW i)) hc
    (fun i => ((u i)⁻¹).val)
    (fun i j => congrArg Units.val
      (show res (inf_le_left : W i ⊓ W j ≤ W i) (u i)⁻¹ = res inf_le_right (u j)⁻¹ by
        rw [map_inv, map_inv, hh]))
  have e : (show Γ(X, V) from s) * (show Γ(X, V) from s') = 1 := by
    apply X.sheaf.eq_of_locally_eq' W V (fun i => homOfLE (hW i)) hc
    intro i
    show (X.presheaf.map (homOfLE (hW i)).op).hom _ = (X.presheaf.map (homOfLE (hW i)).op).hom _
    rw [map_mul, map_one]
    exact (congrArg₂ (· * ·) (hs i) (hs' i)).trans (u i).mul_inv
  exact ⟨⟨s, s', e, (mul_comm _ _).trans e⟩, fun i => Units.ext (hs i)⟩
end GlobalTheory.GenTorsor
