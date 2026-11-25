-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg.exists_clear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:34:14.764684+00:00
-- url     : https://prove2.me/submissions/7c04605a-127f-40ca-b92e-c7c6aea43b2e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterPCProof
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionRegularLocalRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg
theorem _root_.solution {σ Ω C : Type} [Field Ω] [CharZero Ω] [CommRing C] [Algebra ℚ C] (u : σ → Ω) (t : σ → C)
    (F : MvPolynomial σ ℚ) (a : Ω) (b : C) (ha : a * aeval u F = 1) (hb : b * aeval t F = 1)
    (h : MvPolynomial (Option σ) ℚ) :
    ∃ (n : ℕ) (g : MvPolynomial σ ℚ),
      aeval u F ^ n * aeval (fun o : Option σ => o.elim a u) h = aeval u g ∧
      aeval t F ^ n * aeval (fun o : Option σ => o.elim b t) h = aeval t g := by
  induction h using MvPolynomial.induction_on with
  | C r => exact ⟨0, MvPolynomial.C r, by simp, by simp⟩
  | add p q hp hq =>
    obtain ⟨n₁, g₁, h₁, h₁'⟩ := hp
    obtain ⟨n₂, g₂, h₂, h₂'⟩ := hq
    refine ⟨n₁ + n₂, F ^ n₂ * g₁ + F ^ n₁ * g₂, ?_, ?_⟩
    · simp only [map_add, map_mul, map_pow, ← h₁, ← h₂]; ring
    · simp only [map_add, map_mul, map_pow, ← h₁', ← h₂']; ring
  | mul_X p o hp =>
    obtain ⟨n, g, h₁, h₁'⟩ := hp
    cases o with
    | none =>
      refine ⟨n + 1, g, ?_, ?_⟩
      · rw [← h₁, map_mul, aeval_X, Option.elim_none]
        calc _ = aeval u F ^ n * aeval (fun o : Option σ => o.elim a u) p * (a * aeval u F) := by ring
          _ = _ := by rw [ha, mul_one]
      · rw [← h₁', map_mul, aeval_X, Option.elim_none]
        calc _ = aeval t F ^ n * aeval (fun o : Option σ => o.elim b t) p * (b * aeval t F) := by ring
          _ = _ := by rw [hb, mul_one]
    | some q =>
      refine ⟨n, g * X q, ?_, ?_⟩
      · rw [map_mul, map_mul, aeval_X, aeval_X, Option.elim_some, ← h₁]; ring
      · rw [map_mul, map_mul, aeval_X, aeval_X, Option.elim_some, ← h₁']; ring
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg
