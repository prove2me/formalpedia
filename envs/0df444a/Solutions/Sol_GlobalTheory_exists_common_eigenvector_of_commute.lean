-- Prove2me | solution 1 for GlobalTheory.exists_common_eigenvector_of_commute
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:26.470609+00:00
-- url     : https://prove2.me/submissions/3e8da580-3c40-4a51-bfcd-445c587be888

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsCharacterEigenvectorOfCommutingRepresentat
import Theorems.Thm_GlobalTheory_UnimodularLatticeLemma_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {L : Type} [Field L] [IsAlgClosed L] {ι : Type}
    {V : Type} [AddCommGroup V] [Module L V] [FiniteDimensional L V] [Nontrivial V]
    (f : ι → Module.End L V) (hf : ∀ a b, f a * f b = f b * f a) :
    ∃ v : V, v ≠ 0 ∧ ∀ b, ∃ μ : L, f b v = μ • v := by
  first
  | exact @_root_.GlobalTheory.UnimodularLatticeLemma.main
  | exact _root_.GlobalTheory.UnimodularLatticeLemma.main
  | (apply _root_.GlobalTheory.UnimodularLatticeLemma.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnimodularLatticeLemma.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnimodularLatticeLemma.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnimodularLatticeLemma.main ..)
end GlobalTheory
