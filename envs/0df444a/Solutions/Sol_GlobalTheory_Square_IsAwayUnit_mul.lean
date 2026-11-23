-- Prove2me | solution 1 for GlobalTheory.Square.IsAwayUnit.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:21:14.841804+00:00
-- url     : https://prove2.me/submissions/0b12cf51-211d-440f-ade6-6449ab260b6c

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementH
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TupleConstantsNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw conjPl)
open Formalism.PairingDivisionLocalBalance (Pl wt)
noncomputable section
open GlobalTheory GlobalTheory.Square
variable {K : Type} [Field K] [NumberField K] [StarRing K]
attribute [instance] Co.finX
attribute [instance] Sq.finκ
omit [NumberField K] [StarRing K]
namespace GlobalTheory.Square
namespace IsAwayUnit
theorem _root_.solution {m : ℕ} {x x' : K} (h : IsAwayUnit m x) (h' : IsAwayUnit m x') : IsAwayUnit m (x * x') := by
  obtain ⟨a, k, j, ha, hx⟩ := h
  obtain ⟨a', k', j', ha', hx'⟩ := h'
  refine ⟨a * a', k + k', j + j', by rw [pow_add]; exact mul_dvd_mul ha ha', ?_⟩
  have : ((a * a' : 𝓞 K) : K) = (a : K) * (a' : K) := by simp
  rw [this, ← hx, ← hx']
  ring
end IsAwayUnit
end GlobalTheory.Square
