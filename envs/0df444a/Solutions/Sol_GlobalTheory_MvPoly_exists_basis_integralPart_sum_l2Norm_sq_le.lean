-- Prove2me | solution 1 for GlobalTheory.MvPoly.exists_basis_integralPart_sum_l2Norm_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:40:29.423368+00:00
-- url     : https://prove2.me/submissions/07608411-070b-4ca8-9f2c-2e9c589a310a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsShortBasisAdaptedOfSubsetSpan
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SumFinsuppAntidiagProdPowDivMultiFactorial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsReducedBasisIntegralPartOfLinearIndependen
import Theorems.Thm_GlobalTheory_exists_short_basis_of_ratSpan
import Theorems.Thm_GlobalTheory_MvPoly_smul_mem_integralPart
import Theorems.Thm_GlobalTheory_MvPoly_norm_conjCoeffs_sq
import Theorems.Thm_GlobalTheory_MvPoly_l2Norm_nonneg
import Theorems.Thm_GlobalTheory_MvPoly_support_subset_monomialsLE
import Theorems.Thm_GlobalTheory_MvPoly_vectorL2Norm_const_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule MvPolynomial NumberField
open GlobalTheory
open GlobalTheory.MvPoly
variable {K σ : Type*} [Field K]
variable [NumberField K] [Fintype σ]
namespace GlobalTheory.MvPoly
theorem _root_.solution {κ : Type*}
    (W : Submodule K (MvPolynomial σ K)) {D : ℕ} (hD : ∀ P ∈ W, P.totalDegree ≤ D)
    (S : Set (MvPolynomial σ K)) (hSH : S ⊆ integralPart W) (hSW : span K S = W) {B : ℝ}
    (hB : ∀ P ∈ S, ∀ s : K →+* ℂ, l2Norm (map s P) ≤ B)
    (ω : κ → 𝓞 K) (hω : span ℚ (Set.range fun k => (ω k : K)) = ⊤) {A : ℝ}
    (hA : ∀ (s : K →+* ℂ) k, ‖s (ω k)‖ ≤ A) {R : ℕ} (hR : R = finrank ℚ K * finrank K W) :
    ∃ b : Basis (Fin R) ℤ (integralPart W), ∀ i,
      √(∑ s : K →+* ℂ, l2Norm (map s (b i : MvPolynomial σ K)) ^ 2) ≤
        √((R + 3) / 4) * √(finrank ℚ K) * A * B := by
  classical
  let v : κ × S → MvPolynomial σ K := fun p => ω p.1 • (p.2 : MvPolynomial σ K)
  have hvH : ∀ p, v p ∈ integralPart W := fun p => smul_mem_integralPart _ (hSH p.2.2)
  have hsp : span ℚ (Set.range v) = W.restrictScalars ℚ := by
    refine le_antisymm (span_le.2 ?_) fun P hP => ?_
    · rintro _ ⟨p, rfl⟩; exact (hvH p).1
    · have hP' : P ∈ span K S := hSW ▸ hP
      have key : ∀ c : K, c • P ∈ span ℚ (Set.range v) := by
        clear hP
        induction hP' using span_induction with
        | mem y hy =>
          intro c
          have hc : c ∈ span ℚ (Set.range fun k => (ω k : K)) := hω ▸ mem_top
          induction hc using span_induction with
          | mem c hc => obtain ⟨k, rfl⟩ := hc; exact subset_span ⟨(k, ⟨y, hy⟩), rfl⟩
          | zero => simp
          | add c c' _ _ h h' => rw [add_smul]; exact add_mem h h'
          | smul q c _ h => rw [smul_assoc]; exact smul_mem _ _ h
        | zero => simp
        | add y z _ _ hy hz => intro c; rw [smul_add]; exact add_mem (hy c) (hz c)
        | smul c' y _ hy => intro c; rw [smul_smul]; exact hy _
      simpa using key 1
  have hφ : ∀ P ∈ integralPart W, P ≠ 0 → 1 ≤ ‖conjCoeffs K σ D P‖ := by
    intro P hP h0
    obtain ⟨α, hα⟩ := support_nonempty.2 h0
    obtain ⟨s, hs⟩ := exists_conjugate_one_le_norm (K := K) (α := ⟨P.coeff α, hP.2 α⟩)
      (fun h => mem_support_iff.1 hα (congrArg Subtype.val h))
    exact hs.trans (PiLp.norm_apply_le (conjCoeffs K σ D P)
      (s, ⟨α, support_subset_monomialsLE.2 (hD P hP.1) hα⟩))
  have hr : ∀ p, ‖conjCoeffs K σ D (v p)‖ ≤ √(finrank ℚ K) * A * B := by
    intro p
    have h1 : ∀ s : K →+* ℂ, l2Norm (map s (v p)) ≤ A * B := fun s => by
      have : map s (v p) = s (ω p.1) • map s (p.2 : MvPolynomial σ K) := by
        ext α
        rw [coeff_smul, coeff_map, coeff_map, smul_eq_mul, ← map_mul]
        rfl
      rw [this, vectorL2Norm_const_mul]
      exact mul_le_mul (hA s _) (hB _ p.2.2 s) (l2Norm_nonneg _) ((norm_nonneg _).trans (hA s p.1))
    have h0 : 0 ≤ A * B := (l2Norm_nonneg _).trans (h1 (Classical.arbitrary _))
    rw [mul_assoc]
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    rw [norm_conjCoeffs_sq (hD _ (hvH p).1), mul_pow, Real.sq_sqrt (Nat.cast_nonneg _),
      ← Embeddings.card K ℂ, ← nsmul_eq_mul, ← Finset.card_univ]
    exact Finset.sum_le_card_nsmul _ _ _ fun s _ => pow_le_pow_left₀ (l2Norm_nonneg _) (h1 s) 2
  obtain ⟨b, hb⟩ := exists_short_basis_of_ratSpan (integralPart W) (conjCoeffs K σ D) one_pos hφ v
    hvH (by rw [hsp]; exact fun P hP => hP.1) hr (R := R)
    (by rw [hsp, hR]; exact Module.finrank_mul_finrank ℚ K W)
  refine ⟨b, fun i => ?_⟩
  have hne : Nonempty (κ × S) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have h2 : (b i : MvPolynomial σ K) ∈ span ℚ (Set.range v) := hsp ▸ (b i).2.1
    rw [Set.range_eq_empty, span_empty, mem_bot] at h2
    exact b.ne_zero i (Subtype.ext h2)
  have h0 : 0 ≤ √(finrank ℚ K) * A * B := (norm_nonneg _).trans (hr hne.some)
  rw [← norm_conjCoeffs_sq (hD _ (b i).2.1), mul_assoc, mul_assoc, ← mul_assoc (√(finrank ℚ K)),
    ← Real.sqrt_sq h0, ← Real.sqrt_mul (by positivity)]
  exact Real.sqrt_le_sqrt (hb i)
end GlobalTheory.MvPoly
