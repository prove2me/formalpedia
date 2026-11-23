-- Prove2me | solution 1 for GlobalTheory.SW.Dict.quad_tauOf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:37:13.171099+00:00
-- url     : https://prove2.me/submissions/5f4ee36a-ac34-475e-ae63-0efb100060bb

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
theorem _root_.solution (Z : _root_.GlobalTheory.SW.CM Ψ N N)
    (m : _root_.GlobalTheory.SW.QI E N → ℂ) (hm : ∀ p, conj (m p) = m p) :
    m ⬝ᵥ _root_.GlobalTheory.SW.tauOf Ψ Z *ᵥ m =
      2 * ∑ τ : Ψ, _root_.GlobalTheory.SW.Dict.vec τ.1 m ⬝ᵥ Z τ *ᵥ
        fun a => conj (_root_.GlobalTheory.SW.Dict.vec τ.1 m a) := by
  rw [two_mul]
  simp only [dotProduct, mulVec, _root_.GlobalTheory.SW.tauOf, _root_.GlobalTheory.SW.Dict.vec, Matrix.of_apply, map_sum, map_mul, hm, Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul, mul_add, add_mul, Finset.sum_add_distrib]
  congr 1
  ·
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    conv_lhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  · refine (Finset.sum_congr rfl fun a _ => Finset.sum_comm).trans ?_
    conv_lhs => rw [Finset.sum_comm]
    refine (Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm).trans ?_
    refine (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    conv_lhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
end _root_.GlobalTheory.SW.Dict
end GlobalTheory.SW.Dict
