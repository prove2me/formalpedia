-- Prove2me | solution 1 for GlobalTheory.RootEx.LatOpen.isCompact_stdLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:41:03.224009+00:00
-- url     : https://prove2.me/submissions/3f230f44-996f-4106-8574-c0f2ebdfee83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ScaledBasisMemChainLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsOpenAndRelIndexNeZero
import Theorems.Thm_GlobalTheory_RootEx_UnfoldShape_mem_stdLat
import Theorems.Thm_GlobalTheory_SplitWeil_isCompact_int


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.LatOpen
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι : Type}
namespace GlobalTheory.RootEx.LatOpen
theorem _root_.solution : IsCompact (stdLat k ι : Set (ι → k)) := by
  have e : (stdLat k ι : Set (ι → k)) = Set.pi Set.univ fun _ => (𝒪[k] : Set k) := by
    ext v
    simp only [SetLike.mem_coe, mem_stdLat, Set.mem_pi, Set.mem_univ, true_imp_iff]
  rw [e]
  exact isCompact_univ_pi fun _ => isCompact_int k
end GlobalTheory.RootEx.LatOpen
