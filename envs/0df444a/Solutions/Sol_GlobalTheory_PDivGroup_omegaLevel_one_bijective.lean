-- Prove2me | solution 1 for GlobalTheory.PDivGroup.omegaLevel_one_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:41:30.600624+00:00
-- url     : https://prove2.me/submissions/d075664d-4cb8-45f6-a809-d2b49eab0243

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToBaseChangePtsBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DUnitMemRangeOfMemKerIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PadicActionConstInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra CategoryTheory
open GlobalTheory
open GlobalTheory.PDivGroup
open PDiv
variable {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)
namespace GlobalTheory.PDivGroup
theorem _root_.solution (hp : (p : R) = 0) : Function.Bijective (G.omegaLevel 1) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun w hw => ?_, G.omegaLevel_surjective 1⟩
  obtain ⟨v, rfl⟩ := (G.omega_val_eq_zero_iff 1 w).1 hw
  rw [pow_one, hp, zero_smul]
end GlobalTheory.PDivGroup
