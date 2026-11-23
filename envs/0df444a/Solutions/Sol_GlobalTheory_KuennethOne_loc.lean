-- Prove2me | solution 1 for GlobalTheory.KuennethOne.loc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:42:46.397649+00:00
-- url     : https://prove2.me/submissions/b81b602d-1259-4337-808e-dfff99aaf197

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
theorem _root_.solution {J : Type} {N : Z.Opens} (W : J → Z.Opens) (hc : N ≤ iSup W) (x y : Γ(Z, N))
    (h : ∀ j, rs (inf_le_left : N ⊓ W j ≤ N) x = rs inf_le_left y) : x = y := by
  refine Z.sheaf.eq_of_locally_eq' (fun j => N ⊓ W j) N (fun j => homOfLE inf_le_left) ?_ x y h
  rw [← inf_iSup_eq]
  exact le_inf le_rfl hc
end GlobalTheory.KuennethOne
