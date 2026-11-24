-- Prove2me | solution 1 for GlobalTheory.QuadraticZeta.exists_periodPair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:01:30.508861+00:00
-- url     : https://prove2.me/submissions/a180d3a3-b8a0-4b09-a9c1-6a6a77583498

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIsKroneckerCharOfDiscr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsBasisEmbedding
import Theorems.Thm_GlobalTheory_QuadraticZeta_discr_pos
import Theorems.Thm_GlobalTheory_QuadraticZeta_absNorm_mul_sqrt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module FractionalIdeal
open scoped nonZeroDivisors UpperHalfPlane ComplexConjugate
open GlobalTheory GlobalTheory.QuadraticZeta
variable {K : Type*} [Field K] [NumberField K] {d : ℕ}
variable (h2 : finrank ℚ K = 2) (hD : discr K = -d) (σ : K →+* ℂ)
include h2 hD
namespace GlobalTheory.QuadraticZeta
theorem _root_.solution (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ L : PeriodPair, (L.lattice : Set ℂ) = σ '' 𝔞.1 := by
  let b : Basis (Fin 2) ℤ (𝔞.1 : Submodule (𝓞 K) K) := finBasisOfFinrankEq ℤ _
    ((fractionalIdeal_rank K 𝔞).trans ((RingOfIntegers.rank K).trans h2))
  have hd0 := discr_pos h2 hD
  have h0 : (σ (b 1) * conj (σ (b 0))).im ≠ 0 := by
    rw [← abs_ne_zero, ← absNorm_mul_sqrt h2 hD σ]
    have : (absNorm 𝔞.1 : ℝ) ≠ 0 := by simp [absNorm_eq_zero_iff]
    positivity
  refine ⟨⟨σ (b 0), σ (b 1), ?_⟩, ?_⟩
  · rw [LinearIndependent.pair_iff]
    intro x y e
    have e1 := congrArg Complex.re e
    have e2 := congrArg Complex.im e
    simp at e1 e2 h0
    constructor
    · refine mul_right_cancel₀ h0 ?_
      linear_combination (σ (b 1)).im * e1 - (σ (b 1)).re * e2
    · refine mul_right_cancel₀ h0 ?_
      linear_combination (σ (b 0)).re * e2 - (σ (b 0)).im * e1
  · ext z
    rw [SetLike.mem_coe, PeriodPair.mem_lattice]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨_, (m • b 0 + n • b 1).2, by simp⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨b.repr ⟨x, hx⟩ 0, b.repr ⟨x, hx⟩ 1, ?_⟩
      have := congrArg (fun x : (𝔞.1 : Submodule (𝓞 K) K) => σ x) (b.sum_repr ⟨x, hx⟩)
      rw [Fin.sum_univ_two] at this
      simpa using this
end GlobalTheory.QuadraticZeta
