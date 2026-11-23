-- Prove2me | solution 1 for GlobalTheory.KuennethOne.glue
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:42:46.206973+00:00
-- url     : https://prove2.me/submissions/9cb943f3-804b-4d25-adf0-e886f6dace06

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitsOfIsAffineOpen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.KuennethOne
variable {Z : Scheme.{0}}
namespace GlobalTheory.KuennethOne
theorem _root_.solution {J : Type} (O : Z.Opens) (W : J → Z.Opens) (hW : ∀ j, W j ≤ O) (hc : O ≤ iSup W)
    (sf : ∀ j, Γ(Z, W j))
    (h : ∀ j k, rs (inf_le_left : W j ⊓ W k ≤ W j) (sf j) = rs inf_le_right (sf k)) :
    ∃ s : Γ(Z, O), ∀ j, rs (hW j) s = sf j := by
  obtain ⟨s, hs, -⟩ := Z.sheaf.existsUnique_gluing' W O (fun j => homOfLE (hW j)) hc sf h
  exact ⟨s, hs⟩
end GlobalTheory.KuennethOne
