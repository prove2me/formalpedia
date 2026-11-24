-- Prove2me | solution 1 for GlobalTheory.PeriodOnto.hermC_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:22:56.876532+00:00
-- url     : https://prove2.me/submissions/aae4eb98-b65e-4b11-a81d-7cb17036e199

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqIffConjNe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsFrameOfIsPeriod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexOrder ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.PeriodOnto
variable {E : Type} [Field E] [NumberField E]
variable [IsCMField E]
namespace GlobalTheory.PeriodOnto
theorem _root_.solution {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (hG : ∀ a b, FD.cc (G a b) = G b a) (x : Matrix (Fin r) (Fin r) ℂ) (v : Fin r → ℂ) (a : Fin r) :
    conj ((v ᵥ* (G.map τ * x.map conj)) a) = FD.hermC τ G (FD.col x a) v := by
  have hcc : ∀ a b, conj (τ (G a b)) = τ (G b a) := fun a b => by
    rw [← hG a b]
    exact (IsCMField.complexEmbedding_complexConj E τ _).symm
  simp only [FD.hermC, FD.col, vecMul, dotProduct, Matrix.mul_apply, map_apply,
    map_sum, map_mul, Complex.conj_conj, Finset.mul_sum, hcc]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
end GlobalTheory.PeriodOnto
