-- Prove2me | solution 1 for GlobalTheory.idealCharacterL_continuation_ne_zero_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:12:42.340303+00:00
-- url     : https://prove2.me/submissions/115f9d11-1ce5-4a9b-854f-72b5630029fc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CountableIdealSummableAbsNormRpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_EulerProductNeZeroOneOfEntire
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_OneSubRePosOfNormLeHalf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_DedekindZetaEulerProductMulSubOneEntire
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdealCharacterLContinuationNeZeroOne
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_GlobalTheory_countable_ideal_and_summable_absNorm_rpow
import Theorems.Thm_GlobalTheory_dedekindZeta_eulerProduct_mul_sub_one_entire
import Theorems.Thm_GlobalTheory_eulerProduct_eq_exp_and_pos
import Theorems.Thm_GlobalTheory_eulerProduct_ne_zero_one_of_entire
import Theorems.Thm_GlobalTheory_idealCharacter_LSeries_continuation
import Theorems.Thm_GlobalTheory_tsum_ideal_mul_absNorm_cpow_eq_exp_tsum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply


section
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
namespace GlobalTheory
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
private theorem two_le_absNorm_heightOneSpectrum {K : Type} [Field K] [NumberField K]
    (P : HeightOneSpectrum (𝓞 K)) : 2 ≤ Ideal.absNorm P.asIdeal := by
  have h0 : Ideal.absNorm P.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr P.ne_bot
  have h1 : Ideal.absNorm P.asIdeal ≠ 1 := Ideal.absNorm_eq_one_iff.not.mpr P.isPrime.ne_top
  omega
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
private theorem one_sub_mul_natCast_cpow_neg_ne_zero {c : ℂ} (hc : ‖c‖ ≤ 1) {n : ℕ} (hn : 2 ≤ n)
    {s : ℂ} (hs : 0 < s.re) : 1 - c * (n : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h1 : c * (n : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
  have h2 : ‖(n : ℂ) ^ (-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (by omega : 1 < n)) (by linarith)
  have h3 := congrArg norm h1
  rw [norm_mul, norm_one] at h3
  nlinarith [norm_nonneg c, norm_nonneg ((n : ℂ) ^ (-s))]
end GlobalTheory
end

set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open GlobalTheory
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (K : Type) [Field K] [NumberField K] (m : Ideal (𝓞 K)) (X : Ideal (𝓞 K) → ℂ)
    (φ : mixedSpace K → ℂ), m ≠ ⊥ → X ⊥ = 0 → (∀ I J, X (I * J) = X I * X J) →
    (∀ I, I ≠ ⊥ → I ⊔ m = ⊤ → ‖X I‖ = 1) → (∀ I, I ⊔ m ≠ ⊤ → X I = 0) →
    (∀ x y, φ (x * y) = φ x * φ y) → (∀ (t : ℝ) x, 0 < t → φ (t • x) = φ x) →
    ContDiffOn ℝ ∞ φ {x | mixedEmbedding.norm x ≠ 0} →
    (∀ x, mixedEmbedding.norm x ≠ 0 → ‖φ x‖ = 1) →
    (∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = φ (mixedEmbedding K β)) →
    (∃ J, J ≠ ⊥ ∧ J ⊔ m = ⊤ ∧ X J ≠ 1) → ∀ c : HeightOneSpectrum (𝓞 K) → ℂ,
    (∀ P, ‖c P‖ ≤ 1) → (∀ P, ¬ m ≤ P.asIdeal → c P = X P.asIdeal) →
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L {s | 0 < s.re} ∧ (∀ s : ℂ, 1 < s.re →
      L s = Complex.exp (∑' P : HeightOneSpectrum (𝓞 K),
        -Complex.log (1 - c P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s)))) ∧ L 1 ≠ 0 := by
  intro K _ _ m X φ hm hXbot hXmul hXnorm hXzero hφmul hφsmul hφsmooth hφnorm hXφ hJ c hc hcX
  have hXtop : X ⊤ = 1 := by
    have h1 := hXnorm ⊤ top_ne_bot (top_sup_eq m)
    have h2 : X ⊤ = X ⊤ * X ⊤ := by rw [← hXmul, Ideal.top_mul]
    have h3 : X ⊤ ≠ 0 := fun h => by rw [h, norm_zero] at h1; exact zero_ne_one h1
    exact mul_left_cancel₀ h3 (by rw [mul_one]; exact h2.symm)
  have hXle : ∀ I, ‖X I‖ ≤ 1 := by
    intro I
    by_cases hI : I = ⊥
    · rw [hI, hXbot, norm_zero]
      exact zero_le_one
    by_cases hIm : I ⊔ m = ⊤
    · rw [hXnorm I hI hIm]
    · rw [hXzero I hIm, norm_zero]
      exact zero_le_one
  obtain ⟨Z, hZd, hZ, hZ1⟩ := _root_.GlobalTheory.idealCharacter_LSeries_continuation K m X φ hm hXbot hXmul hXnorm
    hXzero hφmul hφsmul hφsmooth hφnorm hXφ
  have hZ0 := hZ1 hJ
  let LX : ℂ → ℂ := dslope Z 1
  have hLXd : Differentiable ℂ LX := by
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope Filter.univ_mem).mpr hZd.differentiableOn
  have hLX : ∀ s : ℂ, 1 < s.re → LX s = Complex.exp (∑' P : HeightOneSpectrum (𝓞 K),
      -Complex.log (1 - X P.asIdeal * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))) := by
    intro s hs
    have hs1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at hs; exact lt_irrefl _ hs
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    rw [← _root_.GlobalTheory.tsum_ideal_mul_absNorm_cpow_eq_exp_tsum K X hXbot hXtop hXmul hXle s hs]
    simp only [LX, dslope_of_ne _ hs1, slope_def_field, hZ s hs, hZ0, sub_zero]
    field_simp
  obtain ⟨Zζ, hZζd, hZζ⟩ := _root_.GlobalTheory.dedekindZeta_eulerProduct_mul_sub_one_entire K
  have hsum : ∀ σ : ℝ, 1 < σ → Summable fun P : HeightOneSpectrum (𝓞 K) =>
      ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-σ) :=
    fun σ hσ => ((_root_.GlobalTheory.countable_ideal_and_summable_absNorm_rpow K).2 σ hσ).2
  have hne : Nonempty (HeightOneSpectrum (𝓞 K)) := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 K)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField K)⟩⟩
  have hLX1 : LX 1 ≠ 0 := _root_.GlobalTheory.eulerProduct_ne_zero_one_of_entire (HeightOneSpectrum (𝓞 K))
    (fun P => Ideal.absNorm P.asIdeal) (fun P => X P.asIdeal) two_le_absNorm_heightOneSpectrum
    (fun P => hXle _) hsum hne Zζ LX hZζd hLXd hZζ hLX
  have hfin : {P : HeightOneSpectrum (𝓞 K) | P.asIdeal ∣ m}.Finite := Ideal.finite_factors hm
  let S := hfin.toFinset
  have hmemS : ∀ P, P ∈ S ↔ m ≤ P.asIdeal := fun P => by simp [S, Ideal.dvd_iff_le]
  have hfac : ∀ (P : HeightOneSpectrum (𝓞 K)) (s : ℂ), 0 < s.re →
      1 - c P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s) ≠ 0 :=
    fun P s hs => one_sub_mul_natCast_cpow_neg_ne_zero (hc P) (two_le_absNorm_heightOneSpectrum P) hs
  let F : ℂ → ℂ := ∏ P ∈ S, fun s => (1 - c P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹
  have hF : ∀ s, F s = ∏ P ∈ S, (1 - c P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ :=
    fun s => by simp [F, Finset.prod_apply]
  refine ⟨fun s => LX s * F s, ?_, ?_, ?_⟩
  · apply hLXd.differentiableOn.mul
    apply DifferentiableOn.finset_prod
    intro P _
    refine DifferentiableOn.inv ?_ (fun s hs => hfac P s hs)
    refine DifferentiableOn.const_sub ?_ _
    refine DifferentiableOn.const_mul ?_ _
    intro s _
    refine DifferentiableAt.differentiableWithinAt ?_
    exact differentiableAt_id.neg.const_cpow
      (Or.inl (Nat.cast_ne_zero.mpr (by have := two_le_absNorm_heightOneSpectrum P; omega)))
  · intro s hs
    have hs0 : 0 < s.re := by linarith
    obtain ⟨hsa, -⟩ := (_root_.GlobalTheory.eulerProduct_eq_exp_and_pos (HeightOneSpectrum (𝓞 K))
      (fun P => Ideal.absNorm P.asIdeal) (fun P => X P.asIdeal) two_le_absNorm_heightOneSpectrum
      (fun P => hXle _) hsum).1 s hs
    have hsplit : ∀ P : HeightOneSpectrum (𝓞 K),
        -Complex.log (1 - c P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s)) =
        -Complex.log (1 - X P.asIdeal * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s)) +
        (if P ∈ S then -Complex.log (1 - c P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))
          else 0) := by
      intro P
      by_cases hP : P ∈ S
      · rw [if_pos hP]
        have hXP : X P.asIdeal = 0 := hXzero _ (by
          rw [sup_eq_left.mpr ((hmemS P).mp hP)]
          exact P.isPrime.ne_top)
        rw [hXP, zero_mul, sub_zero, Complex.log_one, neg_zero, zero_add]
      · rw [if_neg hP, add_zero, hcX P (fun h => hP ((hmemS P).mpr h))]
    show LX s * F s = _
    rw [tsum_congr hsplit, hsa.tsum_add (summable_of_ne_finset_zero (s := S) fun P hP => if_neg hP),
      tsum_eq_sum (s := S) (fun P hP => if_neg hP), Complex.exp_add, ← hLX s hs, hF,
      Complex.exp_sum]
    congr 1
    refine Finset.prod_congr rfl fun P hP => ?_
    rw [if_pos hP, Complex.exp_neg, Complex.exp_log (hfac P s hs0)]
  · show LX 1 * F 1 ≠ 0
    rw [hF]
    exact mul_ne_zero hLX1 (Finset.prod_ne_zero_iff.mpr fun P _ => inv_ne_zero (hfac P 1 (by simp)))
end _root_.GlobalTheory
end GlobalTheory
