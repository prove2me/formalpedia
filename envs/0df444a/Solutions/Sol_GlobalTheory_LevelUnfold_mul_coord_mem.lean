-- Prove2me | solution 1 for GlobalTheory.LevelUnfold.mul_coord_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:00:38.855123+00:00
-- url     : https://prove2.me/submissions/90f1d150-578d-437e-9cca-46bdede25171

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FlagVolumeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemSmulOfMemFlagSubOne
import Theorems.Thm_GlobalTheory_LevelUnfold_mul_inv_q
import Theorems.Thm_GlobalTheory_LevelUnfold_mem_gluedS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix IsLocalRing
open scoped Pointwise ENNReal
noncomputable section
open GlobalTheory GlobalTheory.LevelUnfold
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LatPair GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} {c : ℕ} {q : Unif k}
namespace GlobalTheory.LevelUnfold
theorem _root_.solution {L : Submodule 𝒪[k] (n → k)} {f : n → k} {y : n ⊕ Fin c → k} (hy : y ∈ gluedS q c L f)
    (i : Fin c) : (q.1 : k) * y (Sum.inr i) ∈ 𝒪[k] := by
  obtain ⟨s, -, h⟩ := mem_gluedS.1 hy
  rcases Nat.eq_zero_or_pos i.val with hi | hi
  · rw [(h i).1 hi, ← mul_assoc, mul_inv_q, one_mul]
    exact s.2
  · exact (h i).2 hi
end GlobalTheory.LevelUnfold
