-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.cliqueMinorFree_iff_not_isMinor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:24:32.417809+00:00
-- url     : https://prove2.me/submissions/16b206d2-dd90-42cc-9002-822e2efbf1a1

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Reach
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_MinorModel

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
variable {V W : Type*}
variable {G : SimpleGraph V} {k : ℕ}
namespace LeanPool.K5MinorFreeChoosability
theorem _root_.solution :
    CliqueMinorFree G k ↔ ¬ IsMinor (⊤ : SimpleGraph (Fin k)) G :=
  ⟨fun h ⟨M⟩ => h ⟨M.toCliqueMinorModel⟩, fun h ⟨M⟩ => h ⟨M.toMinorModel⟩⟩
end LeanPool.K5MinorFreeChoosability
