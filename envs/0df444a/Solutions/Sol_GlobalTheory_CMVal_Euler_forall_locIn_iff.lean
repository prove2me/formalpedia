-- Prove2me | solution 1 for GlobalTheory.CMVal.Euler.forall_locIn_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:24:13.938785+00:00
-- url     : https://prove2.me/submissions/98b87b3d-7399-44c1-b1a9-1a543ca90c51

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ForallLocInShift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal Filter Topology
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Euler
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.Euler
theorem _root_.solution (m : HeightOneSpectrum (OF E) → ℕ) (v : HeightOneSpectrum (OF E)) (y : Af E) :
    (∀ v', LocIn (m v') v' y) ↔ LocIn (m v) v y ∧ ∀ v' ≠ v, LocIn (m v') v' y := by
  refine ⟨fun h => ⟨h v, fun v' _ => h v'⟩, fun h v' => ?_⟩
  by_cases hv' : v' = v
  · rw [hv']; exact h.1
  · exact h.2 v' hv'
end GlobalTheory.CMVal.Euler
