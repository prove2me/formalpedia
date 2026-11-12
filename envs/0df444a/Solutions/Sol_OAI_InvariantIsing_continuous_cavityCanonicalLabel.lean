-- Prove2me | solution 1 for OAI.InvariantIsing.continuous_cavityCanonicalLabel
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:14:57.132462+00:00
-- url     : https://prove2.me/submissions/66b5ce41-63c0-44d6-8751-e06b8fa12813

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258001

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCanonicalLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Canonical spectral labels as continuous monotone functions of the
total overlap, with the diagonal bound built into their range. -/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma continuous_cavityCanonicalCoordinate {m : ℕ} (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : Fin m) :
    Continuous (cavityCanonicalCoordinate ρ eig hρ hρsum p a) := by
  have hi := spectralPathDensity_intervalIntegrable ρ eig hρ hρsum p a ⟨zero_le_one, le_rfl⟩
  have hp := intervalIntegral.continuousOn_primitive_interval' hi (a := 0) left_mem_uIcc
  have hp' : ContinuousOn (fun z => ∫ r in 0..z, spectralPathDensity ρ eig hρ hρsum p a r)
      (Icc 0 1) := by simpa only [uIcc_of_le zero_le_one] using hp
  exact hp'.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
    (fun t => (Set.projIcc 0 1 zero_le_one t).property)

lemma continuous_cavityCanonicalLabel_oai {m : ℕ} (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : Fin m) :
    Continuous (cavityCanonicalLabel ρ eig hρ hρsum p a) :=
  (continuous_cavityCanonicalCoordinate ρ eig hρ hρsum p a).subtype_mk _

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.continuous_cavityCanonicalLabel_oai := @OAI.InvariantIsing.continuous_cavityCanonicalLabel_oai
