-- Prove2me | solution 1 for GlobalTheory.exists_finset_types_of_bounded_bases
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:38:02.943962+00:00
-- url     : https://prove2.me/submissions/cdb95108-d3f3-43ff-aebd-6b9c53a5cff2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegerApproximationCountHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsFinsetTypesOfBoundedBases
import Theorems.Thm_GlobalTheory_exists_finset_boundedBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory
open BoundedBasis
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory
theorem _root_.solution (X : DataX E r) {B : ℝ} (hB : 1 ≤ B) :
    ∃ V : Finset (Fin r → Fin r → E),
      (∀ v ∈ V, (∀ i, v i ∈ X.L') ∧ LinearIndependent E v ∧
        ∀ (τ : E →+* ℂ) (i k : Fin r), ‖τ (herm X.Gm (v i) (v k))‖ ≤ B) ∧
      (∀ v : Fin r → Fin r → E, (∀ i, v i ∈ X.L') → LinearIndependent E v →
        (∀ (τ : E →+* ℂ) (i k : Fin r), ‖τ (herm X.Gm (v i) (v k))‖ ≤ B) →
        ∃ γ ∈ X.Γ, ∃ w ∈ V, ∀ i, v i = Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) (w i)) ∧
      (V.card : ℝ) ≤ (1 + 2 * B) ^ (2 * fdeg E * r ^ 2) *
        ((X.NA : ℝ) * X.NC * r * B) ^ (2 * fdeg E * r ^ 2) * (X.g : ℝ) ^ (2 * fdeg E * r ^ 2) ∧
      (V.card : ℝ) ≤ (3 * (X.NA : ℝ) * X.NC * X.g * r * B ^ 2) ^ (2 * fdeg E * r ^ 2) := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  obtain ⟨V, h₁, h₂, h₃⟩ := exists_finset_boundedBasis X hB0
  refine ⟨V, h₁, fun v a b c => h₂ v ⟨a, b, c⟩, h₃, h₃.trans ?_⟩
  rw [← mul_pow, ← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ _
  calc (1 + 2 * B) * ((X.NA : ℝ) * X.NC * r * B) * X.g
      ≤ (3 * B) * ((X.NA : ℝ) * X.NC * r * B) * X.g := by gcongr; linarith
    _ = _ := by ring
end GlobalTheory
