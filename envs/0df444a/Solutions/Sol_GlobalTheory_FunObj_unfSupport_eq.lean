-- Prove2me | solution 1 for GlobalTheory.FunObj.unfSupport_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:44:45.855496+00:00
-- url     : https://prove2.me/submissions/17d4ac76-b42a-4419-802d-eb2d2d307281

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
theorem _root_.solution : unfSupport ψ ν keep ρ T = unfSupport ψ ν true ρ T := by
  cases keep
  · ext β
    have h : (unfTerm ψ ν false ρ T β).datum = (((charFactor G (ρ.elt β))⁻¹ : ℂˣ) : ℂ) • (unfTerm ψ ν true ρ T β).datum := by
      funext x y
      simp [unfTerm, flatTensor, flatIntegrand, moved, mul_assoc, integral_const_mul]
    simp only [unfSupport, Set.mem_setOf_eq, h, ne_eq, smul_eq_zero, Units.ne_zero, false_or]
  · rfl
end GlobalTheory.FunObj
