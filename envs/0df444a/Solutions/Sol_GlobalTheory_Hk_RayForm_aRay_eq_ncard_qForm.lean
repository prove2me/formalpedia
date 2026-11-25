-- Prove2me | solution 1 for GlobalTheory.Hk.RayForm.aRay_eq_ncard_qForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:49:47.136243+00:00
-- url     : https://prove2.me/submissions/3cbffa0f-30cb-43a0-a9bd-290bd6657d6d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_PlaneLatticeShortBasisOfBoundPowTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayClassPartialZetaContinuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_RingOfIntegersSqrtNegThreeModFour
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassIdealCountEqNcardShiftedBinaryForm
import Theorems.Thm_GlobalTheory_Hk_RayForm_exists_qForm
import Theorems.Thm_GlobalTheory_Hk_RayForm_exists_equiv
import Theorems.Thm_GlobalTheory_Hk_RayForm_unit_eq_one
import Theorems.Thm_GlobalTheory_Hk_RayForm_exists_basis_im
import Theorems.Thm_GlobalTheory_Mem_PartialZeta_abs_im_eq
import Theorems.Thm_GlobalTheory_Mem_PartialZeta_gen_bij
import Theorems.Thm_GlobalTheory_Mem_PartialZeta_lattice_bij
import Theorems.Thm_GlobalTheory_Mem_PartialZeta_ne_bot_of_coprime
import Theorems.Thm_GlobalTheory_Mem_PartialZeta_normSq_eq
import Theorems.Thm_GlobalTheory_plane_lattice_short_basis
import Theorems.Thm_GlobalTheory_ringOfIntegers_sqrt_neg_three_mod_four


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RayForm
open GlobalTheory.Mem.PartialZeta
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.Hk.RayForm
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] (d M : ℕ) (x : K), d.Prime → d % 4 = 3 → 100 ≤ d → x ^ 2 = -(d : K) → Module.finrank ℚ K = 2 → 3 ≤ M → ∀ D : RayData K M, ∀ g : D.G, ∃ α γ l θ₁ θ₂ : ℝ, 1 ≤ α ∧ 1 ≤ γ ∧ α * γ = d * (M : ℝ) ^ 4 / 4 ∧ (∀ v : ℤ × ℤ, ∃ n : ℕ, 1 ≤ n ∧ qForm α γ l θ₁ θ₂ v = n) ∧ ∀ n : ℕ, aRay D g n = (({v : ℤ × ℤ | qForm α γ l θ₁ θ₂ v = n}.ncard : ℕ) : ℝ) := by
  intro K _ _ d M x hp hd hd100 hx h2 hM D g
  obtain ⟨w, bar, hw, hwb, hall, hemb, φ, hφ⟩ :=
    GlobalTheory.ringOfIntegers_sqrt_neg_three_mod_four d (Irreducible.squarefree hp) hd K h2 x hx
  have : IsTotallyComplex K :=
    ⟨fun v => InfinitePlace.isComplex_iff.mpr (hemb v.embedding).1⟩
  obtain ⟨b, hb⟩ := exists_basis_im hp hd hx h2 φ
  have hNnorm : Ideal.absNorm (Ideal.span {(M : 𝓞 K)}) = M ^ 2 := by
    have := normSq_eq h2 φ (M : 𝓞 K)
    simp only [map_natCast, Complex.norm_natCast] at this
    exact_mod_cast this.symm
  have hM9 : 9 ≤ M ^ 2 := by nlinarith
  have hNtop : Ideal.span {(M : 𝓞 K)} ≠ ⊤ := by
    intro h
    rw [h, Ideal.absNorm_top] at hNnorm
    omega
  have hN0 : Ideal.span {(M : 𝓞 K)} ≠ ⊥ := by
    intro h
    rw [h, Ideal.absNorm_bot] at hNnorm
    omega
  obtain ⟨B, hBc, hB0, hBg⟩ := D.cls_surj g⁻¹
  obtain ⟨E0', hE0'⟩ := gen_bij hNtop D g B hBc hB0 hBg
  haveI hU : Unique {u : (𝓞 K)ˣ // (u : 𝓞 K) - 1 ∈ Ideal.span {(M : 𝓞 K)}} :=
    { default := ⟨1, by simp⟩
      uniq := fun u => Subtype.ext (unit_eq_one h2 hM u.1 u.2) }
  obtain ⟨x₀, hx₀B, hx₀N⟩ : ∃ x₀ ∈ B, x₀ - 1 ∈ Ideal.span {(M : 𝓞 K)} := by
    obtain ⟨i, hi, j, hj, hij⟩ := Ideal.isCoprime_iff_exists.mp hBc
    refine ⟨i, hi, ?_⟩
    rw [show i - 1 = -j by linear_combination hij]
    exact Submodule.neg_mem _ hj
  have hNB0 : Ideal.span {(M : 𝓞 K)} * B ≠ ⊥ := by
    rw [Ne, Ideal.mul_eq_bot, not_or]
    exact ⟨hN0, hB0⟩
  obtain ⟨E1, hE1⟩ := lattice_bij (Ideal.span {(M : 𝓞 K)}) B hBc
    (Ideal.selfBasis b _ hNB0) x₀ hx₀B hx₀N
  have hIm := abs_im_eq φ b _ (Ideal.selfBasis b _ hNB0)
  set e := Ideal.selfBasis b _ hNB0 with he_def
  set e₁ : ℂ := φ (((e 0 : 𝓞 K)) : K) with he₁
  set e₂ : ℂ := φ (((e 1 : 𝓞 K)) : K) with he₂
  have hBn0 : Ideal.absNorm B ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact hB0
  set Nr : ℝ := (Ideal.absNorm B : ℝ) with hNr
  have hNrpos : 0 < Nr := by
    rw [hNr]
    exact_mod_cast Nat.pos_of_ne_zero hBn0
  have hsd10 : (10 : ℝ) ≤ √(d : ℝ) := by
    rw [show (10 : ℝ) = √(100 : ℝ) by
      rw [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hd100)
  have hsq : (√(d : ℝ)) ^ 2 = d := Real.sq_sqrt (Nat.cast_nonneg _)
  have hImb : |((starRingEnd ℂ) (φ ((b 0 : 𝓞 K) : K)) * φ ((b 1 : 𝓞 K) : K)).im| = √(d : ℝ) / 2 := by
    rw [← Real.sqrt_sq_eq_abs, hb, Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hMr : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hIme : |((starRingEnd ℂ) e₁ * e₂).im| = (M : ℝ) ^ 2 * Nr * (√(d : ℝ) / 2) := by
    rw [hIm, map_mul, hNnorm, hImb, hNr]
    push_cast
    ring
  have hA : ((starRingEnd ℂ) e₁ * e₂).im ≠ 0 := by
    intro h
    rw [h, abs_zero] at hIme
    have : 0 < (M : ℝ) ^ 2 * Nr * (√(d : ℝ) / 2) := by positivity
    linarith
  obtain ⟨f₁, f₂, hspan, hImf, hshort⟩ := GlobalTheory.plane_lattice_short_basis e₁ e₂ hA
  have hAf : ((starRingEnd ℂ) f₁ * f₂).im ≠ 0 := by
    intro h
    rw [h, abs_zero] at hImf
    exact hA (abs_eq_zero.mp hImf.symm)
  obtain ⟨σ, hσ⟩ := exists_equiv f₁ f₂ e₁ e₂ hAf hA hspan
  obtain ⟨l, θ₁, θ₂, hq⟩ := exists_qForm f₁ f₂ (φ (x₀ : K)) Nr hNrpos.ne' hAf
  set Iv : ℝ := |((starRingEnd ℂ) f₁ * f₂).im| with hIv
  have hIv' : Iv = (M : ℝ) ^ 2 * Nr * (√(d : ℝ) / 2) := by rw [hImf, hIme]
  have hIsq : ((starRingEnd ℂ) f₁ * f₂).im ^ 2 = Iv ^ 2 := (sq_abs _).symm
  have hf₁ : f₁ ≠ 0 := by
    rintro rfl
    simp at hAf
  have hlow : (M : ℝ) ^ 2 * Nr ≤ ‖f₁‖ ^ 2 := by
    have hmem : f₁ ∈ Submodule.span ℤ {e₁, e₂} := hspan ▸ Submodule.subset_span (by simp)
    obtain ⟨r, s, hrs⟩ := Submodule.mem_span_pair.mp hmem
    set y : 𝓞 K := r * (e 0 : 𝓞 K) + s * (e 1 : 𝓞 K) with hy
    have hyf : φ (y : K) = f₁ := by
      rw [← hrs, hy, he₁, he₂]
      simp [zsmul_eq_mul]
    have hyB : y ∈ Ideal.span {(M : 𝓞 K)} * B := by
      rw [hy]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (e 0).2) (Ideal.mul_mem_left _ _ (e 1).2)
    have hy0 : y ≠ 0 := by
      rintro h0
      rw [h0] at hyf
      simp at hyf
      exact hf₁ hyf.symm
    have hdvd := Ideal.absNorm_dvd_absNorm_of_le
      ((Ideal.span_singleton_le_iff_mem _).mpr hyB)
    have hne : Ideal.absNorm (Ideal.span {y}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact hy0
    have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd
    rw [map_mul, hNnorm] at hle
    rw [← hyf, normSq_eq h2 φ y, hNr]
    exact_mod_cast hle
  let E0 := (Equiv.prodUnique _ {u : (𝓞 K)ˣ // (u : 𝓞 K) - 1 ∈ Ideal.span {(M : 𝓞 K)}}).symm.trans E0'
  let Φ := σ.trans (E1.trans E0.symm)
  have key : ∀ v, qForm (‖f₁‖ ^ 2 / Nr) (((starRingEnd ℂ) f₁ * f₂).im ^ 2 / (‖f₁‖ ^ 2 * Nr)) l θ₁ θ₂ v =
      (Ideal.absNorm (Φ v).1 : ℝ) := by
    intro v
    rw [hq v, hσ v]
    have hE : (E0 (Φ v) : 𝓞 K) = E1 (σ v) := by
      simp only [Φ, Equiv.trans_apply, Equiv.apply_symm_apply]
    have hspanv : Ideal.span {((E1 (σ v)) : 𝓞 K)} = (Φ v).1 * B := by
      rw [← hE]
      exact hE0' _
    have hval : φ (x₀ : K) + (((σ v).1 : ℂ) * e₁ + ((σ v).2 : ℂ) * e₂) =
        φ (((E1 (σ v) : 𝓞 K)) : K) := by
      rw [hE1, he₁, he₂]
      simp
      ring
    rw [hval, normSq_eq h2 φ, hspanv, map_mul, hNr]
    push_cast
    field_simp
  refine ⟨‖f₁‖ ^ 2 / Nr, ((starRingEnd ℂ) f₁ * f₂).im ^ 2 / (‖f₁‖ ^ 2 * Nr), l, θ₁, θ₂,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hNrpos, one_mul]
    have hM2 : (1 : ℝ) ≤ (M : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hM2 hNrpos.le]
  · have hf2 : 0 < ‖f₁‖ ^ 2 := by positivity
    rw [le_div_iff₀ (by positivity), hIsq, one_mul]
    have h1 : ‖f₁‖ ^ 2 ≤ 2 * Iv := by rw [hImf]; exact hshort
    have h2' : 2 * Nr ≤ Iv := by
      have hM2 : (9 : ℝ) ≤ (M : ℝ) ^ 2 := by nlinarith
      have hk : (2 : ℝ) ≤ (M : ℝ) ^ 2 * (√(d : ℝ) / 2) := by nlinarith
      rw [hIv']
      calc 2 * Nr ≤ (M : ℝ) ^ 2 * (√(d : ℝ) / 2) * Nr := mul_le_mul_of_nonneg_right hk hNrpos.le
        _ = (M : ℝ) ^ 2 * Nr * (√(d : ℝ) / 2) := by ring
    have hIv0 : 0 ≤ Iv := abs_nonneg _
    nlinarith
  · have hf2 : ‖f₁‖ ^ 2 ≠ 0 := by positivity
    rw [hIsq, hIv']
    field_simp
    rw [hsq]
    ring
  · intro v
    refine ⟨Ideal.absNorm (Φ v).1, ?_, key v⟩
    apply Nat.one_le_iff_ne_zero.mpr
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact ne_bot_of_coprime hNtop (Φ v).2.1
  · intro n
    have hset : idealsIn D g n = (Subtype.val ∘ Φ) ''
        {v : ℤ × ℤ | qForm (‖f₁‖ ^ 2 / Nr) (((starRingEnd ℂ) f₁ * f₂).im ^ 2 / (‖f₁‖ ^ 2 * Nr))
          l θ₁ θ₂ v = n} := by
      ext I
      simp only [idealsIn, Set.mem_setOf_eq, Set.mem_image, Function.comp_apply]
      constructor
      · rintro ⟨_, hIc, hIn, hIg⟩
        refine ⟨Φ.symm ⟨I, hIc, hIg⟩, ?_, by simp⟩
        rw [key, Equiv.apply_symm_apply]
        exact_mod_cast hIn
      · rintro ⟨v, hv, rfl⟩
        rw [key] at hv
        exact ⟨ne_bot_of_coprime hNtop (Φ v).2.1, (Φ v).2.1, by exact_mod_cast hv, (Φ v).2.2⟩
    rw [aRay, hset, Set.ncard_image_of_injective _ (Subtype.val_injective.comp Φ.injective)]
end GlobalTheory.Hk.RayForm
