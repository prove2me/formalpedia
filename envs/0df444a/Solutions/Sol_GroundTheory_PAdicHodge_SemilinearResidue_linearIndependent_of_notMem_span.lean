-- Prove2me | solution 1 for GroundTheory.PAdicHodge.SemilinearResidue.linearIndependent_of_notMem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:17:27.583862+00:00
-- url     : https://prove2.me/submissions/807416dc-8fdb-4db0-b66e-f968afd1de62

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_SemilinearResidue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Polynomial Module Finset
open GroundTheory.PAdicHodge.SemilinearResidue
variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
namespace GroundTheory.PAdicHodge.SemilinearResidue
theorem _root_.solution (v : ℕ → V) : ∀ m : ℕ,
    (∀ j < m, v j ∉ Submodule.span k (Set.range (fun i : Fin j => v i))) →
      LinearIndependent k (fun i : Fin m => v i)
  | 0, _ => linearIndependent_empty_type
  | m + 1, h => by
    have ih := solution v m (fun j hj => h j (by omega))
    have : (fun i : Fin (m + 1) => v i) = Fin.snoc (fun i : Fin m => v i) (v m) := by
      funext i
      refine Fin.lastCases ?_ (fun i => ?_) i <;> simp
    rw [this]
    exact linearIndependent_finSnoc.mpr ⟨ih, h m (by omega)⟩
end GroundTheory.PAdicHodge.SemilinearResidue
