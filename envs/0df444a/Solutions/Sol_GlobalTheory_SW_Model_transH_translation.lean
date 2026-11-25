-- Prove2me | solution 1 for GlobalTheory.SW.Model.transH_translation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:10:30.183131+00:00
-- url     : https://prove2.me/submissions/b008b17e-eeb0-4e12-8e9a-820d9dbb45f4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_FirstCoordinateAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_NotAdmissibleHalfLatticeFamily

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField
open scoped ComplexConjugate ComplexOrder
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Model
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.SW.Model
theorem _root_.solution (Ψ : Finset (E →+* ℂ)) {n N : ℕ} (β : Matrix (Fin N) (Fin N) E)
    (ψ : Matrix (Fin n) (Fin N) E → ℂ) :
    TransH Ψ (Matrix.fromBlocks 1 β 0 1) (fun x => ψ x * chiH Ψ β x) ψ := by
  intro Z _ z z'
  have d1 : ∀ τ, hDen Ψ (Matrix.fromBlocks 1 β 0 1) Z τ = 1 := fun τ => by simp [hDen]
  have d2 : ∀ τ, hDen' Ψ (Matrix.fromBlocks 1 β 0 1) Z τ = 1 := fun τ => by simp [hDen']
  have a : hAct Ψ (Matrix.fromBlocks 1 β 0 1) Z = fun τ => Z τ + β.map τ.1 := by
    funext τ; simp [hAct, d1]
  have f : hFac Ψ (Matrix.fromBlocks 1 β 0 1) Z z z' = 1 := by simp [hFac, d1]
  have e1 : (fun τ => Matrix.of fun k => (hDen' Ψ (Matrix.fromBlocks 1 β 0 1) Z τ)⁻¹ *ᵥ z τ k) = z := by
    funext τ; ext k i; simp [d2]
  have e2 : (fun τ => Matrix.of fun k => z' τ k ᵥ* (hDen Ψ (Matrix.fromBlocks 1 β 0 1) Z τ)⁻¹) = z' := by
    funext τ; ext k i; simp [d1]
  rw [a, f, one_mul, e1, e2]
  unfold thH
  congr 1
  funext x
  rw [mul_assoc (ψ x), chiH, ← Complex.exp_add, ← mul_add]
  congr 3
  unfold expo
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hc : ∀ t : E, τ.1 (cc t) = conj (τ.1 t) := fun t => by
    simp [cc, IsCMField.complexEmbedding_complexConj]
  rw [Matrix.trace, map_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : τ.1 ((x * β * ccT x).diag k) =
      (fun a => τ.1 (x k a)) ⬝ᵥ β.map τ.1 *ᵥ (fun a => conj (τ.1 (x k a))) := by
    simp only [Matrix.diag, Matrix.mul_apply, ccT, Matrix.transpose_apply, Matrix.map_apply,
      map_sum, map_mul, hc, dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mul_assoc]
  rw [this, Matrix.add_mulVec, dotProduct_add]
  ring
end GlobalTheory.SW.Model
