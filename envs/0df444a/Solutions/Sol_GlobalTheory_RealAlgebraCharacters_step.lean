-- Prove2me | solution 1 for GlobalTheory.RealAlgebraCharacters.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:28:29.188561+00:00
-- url     : https://prove2.me/submissions/8d38a01e-adc6-40a7-8b7a-9c7814eff754

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RealAlgSep
import Theorems.Thm_GlobalTheory_RealAlgebraCharacters_span_bdd
import Theorems.Thm_GlobalTheory_RealAlgebraCharacters_realAlg_sep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.RealAlgebraCharacters
open Filter Topology
variable {X : Type} {B : Type} [AddCommGroup B] (χ : B → X → ℂ)
namespace GlobalTheory.RealAlgebraCharacters
theorem _root_.solution [TopologicalSpace X] (hc : ∀ b, Continuous (χ b))
    (hadd : ∀ (a b : B) (x : X), χ (a + b) x = χ a x * χ b x)
    (h0 : ∀ x, χ 0 x = 1) (hn : ∀ (a : B) (x : X), ‖χ a x‖ = 1)
    (hs : ∀ x y : X, x ≠ y → ∃ b, χ b x ≠ χ b y) (β : X → ℝ) (hβ : Continuous β)
    (hβ1 : ∀ u, 0 ≤ β u ∧ β u ≤ 1) {K : Set X} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) :
    ∃ (s : Finset B) (c : B → ℂ), (∀ x, ‖∑ b ∈ s, c b * χ b x‖ ≤ 2) ∧
      ∀ x ∈ K, ‖∑ b ∈ s, c b * χ b x - (β x : ℂ)‖ ≤ 2 * ε := by
  obtain ⟨g, hgA, hg⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
      (realAlg_sep χ hc hadd h0 hn hs) ⟨β, hβ⟩ hK hε
  obtain ⟨M, hM⟩ := span_bdd χ hn hgA
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn (-M) M (fun t => max 0 (min t 1))
    (by fun_prop) ε hε
  have hmem : Polynomial.aeval g p ∈ realAlg χ hadd h0 := by
    have : Algebra.adjoin ℝ {g} ≤ realAlg χ hadd h0 :=
      Algebra.adjoin_le (Set.singleton_subset_iff.2 hgA)
    exact this (Polynomial.aeval_mem_adjoin_singleton ℝ g)
  have hmem' : (fun x => (((Polynomial.aeval g p) x : ℝ) : ℂ)) ∈
      Submodule.span ℂ (Set.range χ) := hmem
  obtain ⟨c, hcf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hmem'
  have hval : ∀ x, ∑ b ∈ c.support, c b * χ b x = ((p.eval (g x) : ℝ) : ℂ) := by
    intro x
    have := congrFun hcf x
    rw [Polynomial.aeval_continuousMap_apply] at this
    rw [← this, Finsupp.sum, Finset.sum_apply]
    simp
  have hnear : ∀ x, |p.eval (g x) - max 0 (min (g x) 1)| < ε := by
    intro x
    have := hM x
    rw [Complex.norm_real, Real.norm_eq_abs] at this
    exact hp _ (abs_le.1 this)
  refine ⟨c.support, c, fun x => ?_, fun x hx => ?_⟩
  · rw [hval, Complex.norm_real, Real.norm_eq_abs]
    have h1 := abs_lt.1 (hnear x)
    have h2 : 0 ≤ max 0 (min (g x) 1) := le_max_left _ _
    have h3 : max 0 (min (g x) 1) ≤ 1 := max_le zero_le_one (min_le_right _ _)
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2]
  · rw [hval, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have h1 := abs_lt.1 (hnear x)
    have h2 : |g x - β x| < ε := hg x hx
    have h3 := abs_lt.1 h2
    have h4 := hβ1 x
    have h5 : max 0 (min (g x) 1) ≤ β x + ε :=
      max_le (by linarith [h4.1]) ((min_le_left _ _).trans (by linarith [h3.2]))
    have h6 : β x - ε ≤ max 0 (min (g x) 1) :=
      le_max_of_le_right (le_min (by linarith [h3.1]) (by linarith [h4.2]))
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2]
end GlobalTheory.RealAlgebraCharacters
