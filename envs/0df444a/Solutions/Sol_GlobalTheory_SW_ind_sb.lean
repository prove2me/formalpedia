-- Prove2me | solution 1 for GlobalTheory.SW.ind_sb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:31:17.693092+00:00
-- url     : https://prove2.me/submissions/72d94953-2eb9-42d2-bba4-eef645cd55f9

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_PeriodLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TestFunctionWitness
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Complex
namespace GlobalTheory.SW
private theorem intM_add_iff_of_intM_right {K : Type} [Field K] {κ ι : Type} {x y : Matrix κ ι K} (hy : IntM y) :
    IntM (x + y) ↔ IntM x :=
  ⟨fun h k i => by simpa using (h k i).sub (hy k i), fun h k i => (h k i).add (hy k i)⟩
end GlobalTheory.SW
end

set_option autoImplicit false
open Matrix Complex
open GlobalTheory GlobalTheory.SW
open Classical
namespace GlobalTheory.SW
theorem _root_.solution {K : Type} [Field K] [NumberField K] {κ ι : Type} [Fintype κ] [Fintype ι] :
    HasLevel 1 (fun x : Matrix κ ι K => if IntM x then (1:ℂ) else 0) := by
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · rw [Nat.cast_one, one_smul]
    by_contra h
    exact hx (if_neg h)
  · rw [Nat.cast_one, one_smul]
    exact if_congr (intM_add_iff_of_intM_right hy) rfl rfl
end GlobalTheory.SW
