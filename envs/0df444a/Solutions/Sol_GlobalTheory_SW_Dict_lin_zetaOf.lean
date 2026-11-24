-- Prove2me | solution 1 for GlobalTheory.SW.Dict.lin_zetaOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:24:43.055411+00:00
-- url     : https://prove2.me/submissions/29055946-a821-4755-845d-fd6b7d13c8f2

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
theorem _root_.solution (z z' : _root_.GlobalTheory.SW.CM Ψ n N)
    (k : Fin n) (m : _root_.GlobalTheory.SW.QI E N → ℂ) (hm : ∀ p, conj (m p) = m p) :
    m ⬝ᵥ _root_.GlobalTheory.SW.zetaOf Ψ z z' k =
      ∑ τ : Ψ, (_root_.GlobalTheory.SW.Dict.vec τ.1 m ⬝ᵥ z τ k +
        z' τ k ⬝ᵥ fun a => conj (_root_.GlobalTheory.SW.Dict.vec τ.1 m a)) := by
  simp only [dotProduct, _root_.GlobalTheory.SW.zetaOf, _root_.GlobalTheory.SW.Dict.vec, map_sum, map_mul, hm, Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul, mul_add, Finset.sum_add_distrib]
  rw [Finset.sum_comm (s := (Finset.univ : Finset Ψ))]
  simp only [Finset.sum_comm (s := (Finset.univ : Finset Ψ))]
  congr 1 <;> exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring
end _root_.GlobalTheory.SW.Dict
end GlobalTheory.SW.Dict
