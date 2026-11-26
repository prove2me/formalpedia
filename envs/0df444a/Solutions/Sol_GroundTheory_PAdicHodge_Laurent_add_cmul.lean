-- Prove2me | solution 1 for GroundTheory.PAdicHodge.Laurent.add_cmul
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T14:30:53.91789+00:00
-- url     : https://prove2.me/submissions/c431110e-0e66-4e06-8a5e-1ec63a110a31

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open Filter Topology
open GroundTheory.PAdicHodge.Laurent
set_option linter.unusedSectionVars false
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {a b c : ℤ → K} {ρ : ℝ}
variable [CompleteSpace K]

theorem solution (hρ : 0 < ρ) (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ)
    (hc : ConvergesAt c ρ) : cmul (a + b) c = cmul a c + cmul b c := by
  have hsum (a c : ℤ → K) (ha : ConvergesAt a ρ) (hc : ConvergesAt c ρ) (n : ℤ) :
      Summable fun i : ℤ => a i * c (n - i) := by
    refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hw := (tendsto_weight_prod ha hc).comp
      (Function.Injective.tendsto_cofinite (f := fun i : ℤ => (i, n - i)) ?_)
    · simp_rw [norm_mul_term hρ.ne' n]
      convert hw.div_const (ρ ^ n)
      · rfl
      · rw [zero_div]
    · intro i j h
      simpa using congrArg Prod.fst h
  ext n
  simp only [cmul, Pi.add_apply, add_mul]
  rw [Summable.tsum_add (hsum a c ha hc n) (hsum b c hb hc n)]
