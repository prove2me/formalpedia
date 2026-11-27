-- Prove2me | solution 2 for GlobalTheory.exists_valuation_eval_eq_gaussVal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:38:33.266838+00:00
-- url     : https://prove2.me/submissions/34f776e2-0f8b-4584-a146-5d4a7742155f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
import Theorems.Thm_GlobalTheory_valuation_eval_le_gaussVal
import Theorems.Thm_GlobalTheory_exists_eq_C_mul_gaussVal_eq_one
import Theorems.Thm_GlobalTheory_gaussVal_le_one_iff
import Theorems.Thm_GlobalTheory_gaussVal_lt_one_iff_map_residue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
noncomputable section
open scoped NNReal TensorProduct
open MvPolynomial
variable {K Γ₀ σ τ : Type*} [Field K]
variable [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
namespace GlobalTheory
theorem _root_.solution {O : Type*} [CommRing O] [IsLocalRing O] [Algebra O K]
    (hO : v.Integers O) [Infinite (IsLocalRing.ResidueField O)] (f d : MvPolynomial σ K)
    (hd : gaussVal v d = 1) :
    ∃ x : σ → K, (∀ i, v (x i) ≤ 1) ∧ v (eval x d) = 1 ∧ v (eval x f) = gaussVal v f := by
  have key : ∀ g : MvPolynomial σ K, gaussVal v g = 1 →
      ∃ x : σ → K, (∀ i, v (x i) ≤ 1) ∧ v (eval x g) = 1 := by
    intro g hg
    obtain ⟨g, rfl⟩ := (gaussVal_le_one_iff v hO).mp hg.le
    have h₁ : map (IsLocalRing.residue O) g ≠ 0 := fun h =>
      ((gaussVal_lt_one_iff_map_residue v hO g).mpr h).ne hg
    obtain ⟨y, hy⟩ : ∃ y, eval y (map (IsLocalRing.residue O) g) ≠ 0 := by
      by_contra! h
      exact h₁ (MvPolynomial.funext fun y => by simpa using h y)
    choose z hz using fun i => IsLocalRing.residue_surjective (y i)
    refine ⟨fun i => algebraMap O K (z i), fun i => hO.map_le_one _, ?_⟩
    have e₁ : eval (fun i => algebraMap O K (z i)) (map (algebraMap O K) g) =
        algebraMap O K (eval z g) := by
      rw [eval_map, ← coe_eval₂Hom, ← MvPolynomial.eval₂_id, ← coe_eval₂Hom, map_eval₂Hom]
      simp
    have e₂ : eval y (map (IsLocalRing.residue O) g) = IsLocalRing.residue O (eval z g) := by
      rw [eval_map, ← coe_eval₂Hom, ← MvPolynomial.eval₂_id, ← coe_eval₂Hom, map_eval₂Hom]
      simp [hz]
    rw [e₂, IsLocalRing.residue_ne_zero_iff_isUnit] at hy
    rw [e₁]
    exact hO.isUnit_iff_valuation_eq_one.mp hy
  by_cases hf : f = 0
  · obtain ⟨x, hx, hx'⟩ := key d hd
    exact ⟨x, hx, hx', by simp [hf]⟩
  obtain ⟨c, g, -, hc, hg, rfl⟩ := exists_eq_C_mul_gaussVal_eq_one v hf
  obtain ⟨x, hx, hx'⟩ := key (g * d) (by rw [map_mul, hg, hd, mul_one])
  rw [map_mul, map_mul] at hx'
  have h₁ : v (eval x g) ≤ 1 := hg ▸ valuation_eval_le_gaussVal v x hx g
  have h₂ : v (eval x d) ≤ 1 := hd ▸ valuation_eval_le_gaussVal v x hx d
  have h₃ : v (eval x g) = 1 :=
    le_antisymm h₁ (hx' ▸ (mul_le_mul_right h₂ _).trans_eq (mul_one _))
  refine ⟨x, hx, by simpa [h₃] using hx', ?_⟩
  rw [← hc]
  simp [h₃]
end GlobalTheory
