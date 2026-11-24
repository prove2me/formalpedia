-- Prove2me | solution 1 for GlobalTheory.SW.Dict.map_ofQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:27:12.830752+00:00
-- url     : https://prove2.me/submissions/12b8e3a9-8f38-4c35-8219-abf4dfe167cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Dict
noncomputable section
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}
variable (Ψ : Finset (E →+* ℂ))
open Matrix Complex NumberField Filter Topology
open scoped ComplexConjugate ComplexOrder Real
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}
variable (Ψ : Finset (E →+* ℂ))
namespace GlobalTheory.SW.Dict
namespace _root_.GlobalTheory.SW.Dict
theorem _root_.solution (σ : E →+* ℂ)
    (m : Matrix (Fin n) (_root_.GlobalTheory.SW.QI E N) ℚ) (k : Fin n) (a : Fin N) :
    σ (_root_.GlobalTheory.SW.ofQ m k a) =
      _root_.GlobalTheory.SW.Dict.vec σ (_root_.GlobalTheory.SW.qv (m k)) a := by
  simp only [_root_.GlobalTheory.SW.ofQ, Matrix.of_apply, map_sum,
    _root_.GlobalTheory.SW.Dict.vec, _root_.GlobalTheory.SW.qv]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Rat.smul_def, map_mul, map_ratCast, mul_comm]
end _root_.GlobalTheory.SW.Dict
end GlobalTheory.SW.Dict
