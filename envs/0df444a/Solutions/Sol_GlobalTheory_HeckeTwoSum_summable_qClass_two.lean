-- Prove2me | solution 1 for GlobalTheory.HeckeTwoSum.summable_qClass_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:54:46.601797+00:00
-- url     : https://prove2.me/submissions/d0182cf9-0486-482a-b2f7-3546b76d04f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AbsNormEqProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeEisensteinConstantTermPartDifferentiableOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DiscreteTopologyFractionalIdealRealLatticeImage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableHilbertEisensteinWeightTwoQSeries
import Theorems.Thm_GlobalTheory_HeckeTwoSum_pow_mul_exp_neg_le
import Theorems.Thm_GlobalTheory_HeckeTwoSum_exists_norm_lower
import Theorems.Thm_GlobalTheory_HeckeTwoSum_norm_qPow
import Theorems.Thm_GlobalTheory_HeckeTwoExp_abs_norm_eq_prod
import Theorems.Thm_GlobalTheory_HeckeTwoExp_emb_nonempty
import Theorems.Thm_GlobalTheory_HeckeTwoExp_nrm_ne_zero
import Theorems.Thm_GlobalTheory_HeckeTwoExp_toQ_injective
import Theorems.Thm_GlobalTheory_HeckeTwoExp_toQ_surjective
import Theorems.Thm_GlobalTheory_HeckeTwo_APart_summable_norm_rpow
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OmegaFactorization_qClass_mk
import Theorems.Thm_GlobalTheory_LipschitzTR_discrete_latOf
import Theorems.Thm_GlobalTheory_LipschitzTR_mem_latOf
import Theorems.Thm_GlobalTheory_LipschitzTR_remb_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LipschitzTR.remb_apply



set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwoSum
open GlobalTheory.LipschitzTR
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.HeckeTwoSum
theorem _root_.solution [IsTotallyReal F] (𝔞 𝔟 : Frac F) (z : Emb F → ℂ) (hz : z ∈ upperHalf F) :
    Summable (qClass 𝔞 𝔟 2 z) := by
  classical
  obtain ⟨τ₀⟩ := GlobalTheory.HeckeTwoExp.emb_nonempty (F := F)
  obtain ⟨m, hm, hmy⟩ : ∃ m : ℝ, 0 < m ∧ ∀ τ, m ≤ (z τ).im := by
    obtain ⟨τ₁, -, hτ₁⟩ := Finset.exists_min_image Finset.univ (fun τ => (z τ).im) ⟨τ₀, Finset.mem_univ _⟩
    exact ⟨_, hz τ₁, fun τ => hτ₁ τ (Finset.mem_univ _)⟩
  obtain ⟨κ, hκ, hκν⟩ := exists_norm_lower (𝔞 : FractionalIdeal (𝓞 F)⁰ F)
  have hnrm : 0 < nrm 𝔞 := lt_of_le_of_ne (by unfold nrm; exact_mod_cast FractionalIdeal.absNorm_nonneg _)
    (GlobalTheory.HeckeTwoExp.nrm_ne_zero 𝔞).symm
  set N : FractionalIdeal (𝓞 F)⁰ F := (𝔞 : FractionalIdeal (𝓞 F)⁰ F) * (𝔟 : FractionalIdeal (𝓞 F)⁰ F) with hN
  haveI : DiscreteTopology (latOf N) := discrete_latOf F N
  set n : ℕ := Module.finrank ℤ (latOf N) + 1 with hn
  have hL : Summable fun v : latOf N => ‖v‖⁻¹ ^ n := ZLattice.summable_norm_pow_inv (latOf N) n (Nat.lt_succ_self _)
  set f : ℕ := Fintype.card (Emb F) with hf
  set K : ℝ := ((2 * f + n).factorial : ℝ) / (2 * Real.pi * m) ^ (2 * f + n) with hK
  set C : ℝ := K / (nrm 𝔞 * κ) with hC
  have hK0 : 0 < K := by positivity
  have hC0 : 0 < C := by positivity
  have key : ∀ ν b : F, ν ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) → ν ≠ 0 → b ≠ 0 → (∀ τ : Emb F, 0 < τ (ν * b)) →
      ‖qTerm 𝔞 2 z (ν, b)‖ ≤
        C * ((|((Algebra.norm ℚ b : ℚ) : ℝ)| ^ 2)⁻¹ * ‖remb F (ν * b)‖⁻¹ ^ n) := by
    intro ν b hν hν0 hb0 hpos
    set ξ := ν * b with hξ
    set s := ∑ τ : Emb F, τ ξ with hs_def
    set A := |((Algebra.norm ℚ ν : ℚ) : ℝ)| with hA_def
    set B := |((Algebra.norm ℚ b : ℚ) : ℝ)| with hB_def
    set w := ‖remb F ξ‖ with hw_def
    have hs : 0 < s := Finset.sum_pos (fun τ _ => hpos τ) ⟨τ₀, Finset.mem_univ _⟩
    have hA : κ ≤ A := hκν ν hν hν0
    have hA0 : 0 < A := hκ.trans_le hA
    have hB0 : 0 < B := by
      rw [hB_def, abs_pos, Rat.cast_ne_zero]; exact (Algebra.norm_ne_zero_iff).2 hb0
    have hw0 : 0 < w := by
      rw [hw_def, norm_pos_iff]
      intro h
      have := congrArg (fun v : RSp F => v τ₀) h
      have h3 : τ₀ ξ = 0 := by simpa using this
      have h2 := hpos τ₀
      linarith
    have hws : w ≤ s := by
      rw [hw_def, EuclideanSpace.norm_eq]
      refine Real.sqrt_le_iff.2 ⟨hs.le, ?_⟩
      calc ∑ τ, ‖(remb F ξ) τ‖ ^ 2 = ∑ τ : Emb F, (τ ξ) ^ 2 := by
            refine Finset.sum_congr rfl fun τ _ => ?_
            rw [remb_apply, Real.norm_eq_abs, sq_abs]
        _ ≤ (∑ τ : Emb F, τ ξ) ^ 2 := Finset.sum_sq_le_sq_sum_of_nonneg fun τ _ => (hpos τ).le
    have hAB : A * B ≤ s ^ f := by
      have h2 := GlobalTheory.HeckeTwoExp.abs_norm_eq_prod ξ
      rw [← Complex.ofReal_prod] at h2
      have h3 := Complex.ofReal_injective h2
      have h1 : A * B = ∏ τ : Emb F, τ ξ := by
        rw [hA_def, hB_def, ← abs_mul, ← Rat.cast_mul, ← map_mul, ← hξ, h3]
        exact Finset.prod_congr rfl fun τ _ => abs_of_pos (hpos τ)
      rw [h1, hf, ← Finset.card_univ, ← Finset.prod_const]
      exact Finset.prod_le_prod (fun τ _ => (hpos τ).le)
        (fun τ _ => Finset.single_le_sum (fun τ _ => (hpos τ).le) (Finset.mem_univ τ))
    set E := Real.exp (-(2 * Real.pi * ∑ τ, τ ξ * (z τ).im)) with hE
    set E' := Real.exp (-((2 * Real.pi * m) * s)) with hE'
    have hEE : E ≤ E' := by
      apply Real.exp_le_exp.2
      have : m * s ≤ ∑ τ, τ ξ * (z τ).im := by
        rw [hs_def, Finset.mul_sum]
        exact Finset.sum_le_sum fun τ _ => by nlinarith [hpos τ, hmy τ]
      nlinarith [Real.pi_pos]
    have hKs := pow_mul_exp_neg_le (c := 2 * Real.pi * m) (t := s) (by positivity) hs.le (2 * f + n)
    have hP : (A * B) ^ 2 * w ^ n ≤ s ^ (2 * f + n) := by
      rw [show s ^ (2 * f + n) = (s ^ f) ^ 2 * s ^ n by ring]
      gcongr
    have hE'K : E' * ((A * B) ^ 2 * w ^ n) ≤ K := by
      have hE'0 : 0 ≤ E' := (Real.exp_pos _).le
      calc E' * ((A * B) ^ 2 * w ^ n) ≤ E' * s ^ (2 * f + n) := mul_le_mul_of_nonneg_left hP hE'0
        _ = s ^ (2 * f + n) * E' := mul_comm _ _
        _ ≤ K := hKs
    have hnorm : ‖qTerm 𝔞 2 z (ν, b)‖ = A / nrm 𝔞 * E := by
      rw [qTerm, norm_mul, norm_qPow, Complex.norm_real, Real.norm_eq_abs, show (2 : ℕ) - 1 = 1 from rfl, pow_one,
        abs_of_nonneg (div_nonneg (abs_nonneg _) hnrm.le)]
    have hR : C * ((B ^ 2)⁻¹ * w⁻¹ ^ n) = K / (nrm 𝔞 * κ * B ^ 2 * w ^ n) := by
      rw [hC, inv_pow]
      field_simp
    rw [hnorm, hR, le_div_iff₀ (by positivity)]
    calc A / nrm 𝔞 * E * (nrm 𝔞 * κ * B ^ 2 * w ^ n) = E * (A * κ * B ^ 2 * w ^ n) := by
          field_simp
      _ ≤ E' * (A * A * B ^ 2 * w ^ n) := by
          gcongr
      _ = E' * ((A * B) ^ 2 * w ^ n) := by ring
      _ ≤ K := hE'K
  set e := Equiv.ofBijective (GlobalTheory.HeckeTwoExp.toQ 𝔞 𝔟)
    ⟨GlobalTheory.HeckeTwoExp.toQ_injective 𝔞 𝔟, GlobalTheory.HeckeTwoExp.toQ_surjective 𝔞 𝔟⟩ with he
  let ι : ∀ c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)),
      {ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) // ∀ τ : Emb F, 0 < τ (ν.1 * c.out.1)} → latOf N :=
    fun c ν => ⟨remb F (ν.1.1 * c.out.1),
      (mem_latOf N _).2 ⟨_, FractionalIdeal.mul_mem_mul ν.1.2.1 c.out.2.1, rfl⟩⟩
  have hι : ∀ c, Function.Injective (ι c) := by
    intro c ν ν' h
    have h1 := congrArg (fun v : latOf N => (v : RSp F) τ₀) h
    simp only [ι, remb_apply] at h1
    have h2 : ν.1.1 * c.out.1 = ν'.1.1 * c.out.1 := τ₀.injective h1
    exact Subtype.ext (Subtype.ext (mul_right_cancel₀ c.out.2.2 h2))
  set Bf : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) → ℝ :=
    fun c => |((Algebra.norm ℚ c.out.1 : ℚ) : ℝ)| with hBf
  set G : (Σ c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)),
      {ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) // ∀ τ : Emb F, 0 < τ (ν.1 * c.out.1)}) → ℝ :=
    fun p => C * ((Bf p.1 ^ 2)⁻¹ * ‖ι p.1 p.2‖⁻¹ ^ n) with hG
  have hG0 : ∀ p, 0 ≤ G p := fun p => by
    simp only [hG]; positivity
  have hbound : ∀ p, ‖qClass 𝔞 𝔟 2 z (e p)‖ ≤ G p := by
    rintro ⟨c, ν⟩
    calc ‖qClass 𝔞 𝔟 2 z (e ⟨c, ν⟩)‖ = ‖qTerm 𝔞 2 z (ν.1.1, c.out.1)‖ :=
          congrArg norm (qClass_mk 𝔞 𝔟 2 z ⟨(ν.1.1, c.out.1), ν.1.2.1, c.out.2.1, ν.2⟩)
      _ ≤ G ⟨c, ν⟩ := key ν.1.1 c.out.1 ν.1.2.1 ν.1.2.2 c.out.2.2 ν.2
  have hGs : Summable G := by
    refine (summable_sigma_of_nonneg hG0).2 ⟨fun c => ?_, ?_⟩
    · exact ((hL.comp_injective (hι c)).mul_left ((Bf c ^ 2)⁻¹)).mul_left C
    · have hZ := GlobalTheory.HeckeTwo.APart.summable_norm_rpow (𝔟 : FractionalIdeal (𝓞 F)⁰ F) (s := 2) one_lt_two
      refine Summable.of_nonneg_of_le (fun c => tsum_nonneg fun ν => hG0 ⟨c, ν⟩) (fun c => ?_)
        (hZ.mul_left (C * ∑' v : latOf N, ‖v‖⁻¹ ^ n))
      show ∑' ν, C * ((Bf c ^ 2)⁻¹ * ‖ι c ν‖⁻¹ ^ n) ≤ _
      rw [tsum_mul_left, tsum_mul_left, Real.rpow_neg (abs_nonneg _), Real.rpow_two]
      have hH : ∑' ν, ‖ι c ν‖⁻¹ ^ n ≤ ∑' v : latOf N, ‖v‖⁻¹ ^ n :=
        tsum_comp_le_tsum_of_inj hL (fun _ => by positivity) (hι c)
      have hB : 0 ≤ (Bf c ^ 2)⁻¹ := by positivity
      calc C * ((Bf c ^ 2)⁻¹ * ∑' ν, ‖ι c ν‖⁻¹ ^ n) ≤ C * ((Bf c ^ 2)⁻¹ * ∑' v : latOf N, ‖v‖⁻¹ ^ n) := by
            gcongr
        _ = _ := by simp only [hBf]; ring
  refine Summable.of_norm ?_
  rw [← e.summable_iff]
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound hGs
end GlobalTheory.HeckeTwoSum
