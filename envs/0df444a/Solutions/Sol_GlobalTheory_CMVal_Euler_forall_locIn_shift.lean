-- Prove2me | solution 1 for GlobalTheory.CMVal.Euler.forall_locIn_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:40:15.50486+00:00
-- url     : https://prove2.me/submissions/44e1eed5-b212-4016-9412-415ed74d7157

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ForallLocInShift
import Theorems.Thm_GlobalTheory_CMVal_Euler_shift_coord
import Theorems.Thm_GlobalTheory_CMVal_Euler_not_over
import Theorems.Thm_GlobalTheory_CMVal_Euler_locIn_congr


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
theorem _root_.solution {m m' : HeightOneSpectrum (OF E) → ℕ} {v : HeightOneSpectrum (OF E)} (hm : ∀ v' ≠ v, m' v' = m v')
    {π : (Af E)ˣ} (hπ : ∀ w, ¬ Over w v → (π : Af E) w = 1) (y : (Af E)ˣ) :
    (∀ v', LocIn (m' v') v' ((π⁻¹ * y : (Af E)ˣ) : Af E)) ↔
      LocIn (m' v) v ((π⁻¹ * y : (Af E)ˣ) : Af E) ∧ ∀ v' ≠ v, LocIn (m v') v' (y : Af E) := by
  have key : ∀ v' ≠ v, LocIn (m' v') v' ((π⁻¹ * y : (Af E)ˣ) : Af E) ↔ LocIn (m v') v' (y : Af E) := fun v' hv' => by
    rw [hm v' hv']
    exact locIn_congr fun P hP => shift_coord y (hπ P (not_over hP hv'))
  refine ⟨fun h => ⟨h v, fun v' hv' => (key v' hv').1 (h v')⟩, fun h v' => ?_⟩
  by_cases hv' : v' = v
  · rw [hv']; exact h.1
  · exact (key v' hv').2 (h.2 v' hv')
end GlobalTheory.CMVal.Euler
