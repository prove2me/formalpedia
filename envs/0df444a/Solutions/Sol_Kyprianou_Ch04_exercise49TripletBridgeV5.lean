-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49TripletBridgeV5
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:10:44.134646+00:00
-- url     : https://prove2.me/submissions/e965be6f-6ec3-4dc6-8c18-5447389b491d

import Mathlib
import Theorems.Thm_levy_foundations_compoundPoissonTripleExponentIdentity
import Definitions.Def_Kyprianou_Ch04_Exercise4_9Certification
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_levy_foundations_compoundPoissonTripleGivenLevyMeasure
import Definitions.Def_levy_foundations_exponent
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    (b : ℝ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ProbabilityTheory.IsLevyMeasure ν)
    (hL : LevyFoundations.isLevyMeasure ((1 : ENNReal) • ν)) :
    let T : ProbabilityTheory.LevyKhintchineTriple :=
      ⟨b + ∫ y in Ioo (-1 : ℝ) 1, y ∂ν,0,ν,hν⟩
    ∀ ξ : ℝ, Kyprianou.Ch01.levyTripleExponent T ξ =
      Complex.I * b * ξ + (charFun ν ξ - 1) := by
  dsimp only
  intro ξ
  have h := levy_foundations_compoundPoissonTripleExponentIdentity b (1 : NNReal) ν
    (by simpa using hL) ξ
  unfold LevyFoundations.exponent LevyFoundations.compoundPoissonTripleGivenLevyMeasure at h
  unfold Kyprianou.Ch01.levyTripleExponent
  have hs : {x : ℝ | |x| < 1} = Ioo (-1 : ℝ) 1 := by
    ext x
    change |x| < (1 : ℝ) ↔ -1 < x ∧ x < 1
    exact abs_lt
  simp only [NNReal.coe_one,ENNReal.coe_one,one_smul,hs,NNReal.coe_zero,
    Complex.ofReal_zero,zero_mul,zero_div,sub_zero,one_mul] at h ⊢
  have hi : (fun x => LevyFoundations.compensatedIntegrand ξ x) =
      ProbabilityTheory.levyCompensatedIntegrand ξ := rfl
  rw [hi] at h
  norm_num at h ⊢
  push_cast at h ⊢
  linear_combination h
