-- Prove2me | solution 1 for GlobalTheory.SW.Dict.thH_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:42:48.297822+00:00
-- url     : https://prove2.me/submissions/716126dc-1e2c-4152-96bf-6c2129e496c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Theorems.Thm_GlobalTheory_SW_Dict_quad_tauOf
import Theorems.Thm_GlobalTheory_SW_Dict_lin_zetaOf
import Theorems.Thm_GlobalTheory_SW_Dict_map_ofQ

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
theorem _root_.solution (φ : Matrix (Fin n) (Fin N) E → ℂ)
    (Z : _root_.GlobalTheory.SW.CM Ψ N N) (z z' : _root_.GlobalTheory.SW.CM Ψ n N) :
    _root_.GlobalTheory.SW.thH Ψ φ Z z z' =
      _root_.GlobalTheory.SW.thS (fun m => φ (_root_.GlobalTheory.SW.ofQ m))
        (_root_.GlobalTheory.SW.tauOf Ψ Z) (_root_.GlobalTheory.SW.zetaOf Ψ z z') := by
  have hreal : ∀ (m : Matrix (Fin n) (_root_.GlobalTheory.SW.QI E N) ℚ) k p,
      conj (_root_.GlobalTheory.SW.qv (m k) p) = _root_.GlobalTheory.SW.qv (m k) p := by
    intro m k p
    simp [_root_.GlobalTheory.SW.qv]
  unfold _root_.GlobalTheory.SW.thH _root_.GlobalTheory.SW.thS
  rw [← (_root_.GlobalTheory.SW.Dict.ofQEquiv E n N).toEquiv.tsum_eq]
  refine tsum_congr fun m => ?_
  change φ (_root_.GlobalTheory.SW.ofQ m) * _ = _
  congr 2
  rw [Finset.sum_congr rfl fun k _ => by
    rw [_root_.GlobalTheory.SW.Dict.quad_tauOf Ψ Z _ (hreal m k),
      _root_.GlobalTheory.SW.Dict.lin_zetaOf Ψ z z' k _ (hreal m k)]]
  unfold _root_.GlobalTheory.SW.expo
  change 2 * (π : ℂ) * I * ∑ τ : Ψ, ∑ k, (((fun a => (τ : E →+* ℂ) (_root_.GlobalTheory.SW.ofQ m k a)) ⬝ᵥ
    Z τ *ᵥ fun a => conj ((τ : E →+* ℂ) (_root_.GlobalTheory.SW.ofQ m k a))) +
    (fun a => (τ : E →+* ℂ) (_root_.GlobalTheory.SW.ofQ m k a)) ⬝ᵥ z τ k +
    z' τ k ⬝ᵥ fun a => conj ((τ : E →+* ℂ) (_root_.GlobalTheory.SW.ofQ m k a))) = _
  simp only [_root_.GlobalTheory.SW.Dict.map_ofQ]
  rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Finset.sum_add_distrib]
  ring
end _root_.GlobalTheory.SW.Dict
end GlobalTheory.SW.Dict
