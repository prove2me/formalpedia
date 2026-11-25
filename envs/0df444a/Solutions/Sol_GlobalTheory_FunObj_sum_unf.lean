-- Prove2me | solution 1 for GlobalTheory.FunObj.sum_unf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:52:23.854839+00:00
-- url     : https://prove2.me/submissions/7d93923f-2995-4f51-8dd1-605157d8b0dd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
variable {k : Type*} [Field k] (G : Grid k)
variable {G}
variable (hs : 1 ≤ G.s)
variable {hs}
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k)
variable {J : G.Level} (keep : Bool) (ρ : Reps hs J) (T : G.Args → ℂ)
namespace GlobalTheory.FunObj
theorem _root_.solution (hfin : (unfSupport ψ ν keep ρ T).Finite) (f : UnfTerm G → ℂ) :
    ((unf ψ ν keep ρ T hfin).map f).sum = ∑ᶠ β ∈ unfSupport ψ ν keep ρ T, f (unfTerm ψ ν keep ρ T β) := by
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, unf, Multiset.map_map]; rfl
end GlobalTheory.FunObj
