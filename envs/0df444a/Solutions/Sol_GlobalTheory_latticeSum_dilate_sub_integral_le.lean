-- Prove2me | solution 1 for GlobalTheory.latticeSum_dilate_sub_integral_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:14:42.667363+00:00
-- url     : https://prove2.me/submissions/0cfcf9c5-dd97-4785-b1ab-c449253efcbf

import Mathlib
import Definitions.Def_Formalism_LatticeTheta_ThetaShiftInversion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ZlatticeTsumDilateSubIntegralLeRapid
import Theorems.Thm_GlobalTheory_fourier_comp_smul_of_pos
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_H_dualIsLattice
import Theorems.Thm_Formalism_H_poissonSchwartz
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open scoped FourierTransform RealInnerProductSpace SchwartzMap
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (V : Type) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] (f : V → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (A : ℕ) :
    ∃ C : ℝ, ∀ (x₀ : V) (t : ℝ), 0 < t → t ≤ 1 →
      ‖∑' l : L, f (t • ((l : V) + x₀)) - (∫ x, f x) /
        ((ZLattice.covolume L * t ^ Module.finrank ℝ V : ℝ) : ℂ)‖ ≤ C * t ^ A := by
  obtain ⟨hD, -⟩ := Formalism.H.dualIsLattice V L
  set d := Module.finrank ℝ V with hd
  set k := A + d + Module.finrank ℤ (Formalism.H.dual L) + 1 with hk
  set F : 𝓢(V, ℂ) := hc.toSchwartzMap hf with hF
  have hFf : (F : V → ℂ) = f := rfl
  obtain ⟨C, hC0, hC⟩ := (𝓕 F : 𝓢(V, ℂ)).decay k 0
  have hs := ZLattice.summable_norm_pow_inv (Formalism.H.dual L) k (by omega)
  have hcov : 0 < ZLattice.covolume L := ZLattice.covolume_pos L volume
  refine ⟨(ZLattice.covolume L)⁻¹ * (C * ∑' y : Formalism.H.dual L, ‖y‖⁻¹ ^ k), ?_⟩
  intro x₀ t ht ht1
  have hft : ContDiff ℝ ∞ (fun x : V => f (t • x)) := hf.comp (contDiff_const_smul t)
  have hct : HasCompactSupport (fun x : V => f (t • x)) :=
    hc.comp_homeomorph (Homeomorph.smulOfNeZero t ht.ne')
  obtain ⟨G, hG⟩ : ∃ G : 𝓢(V, ℂ), (G : V → ℂ) = fun x : V => f (t • x) :=
    ⟨hct.toSchwartzMap hft, rfl⟩
  obtain ⟨h1, h2⟩ := Formalism.H.poissonSchwartz V L G x₀
  rw [hG] at h1 h2
  rw [h2.tsum_eq, h1.tsum_eq_add_tsum_ite 0]
  have h0 : (𝓕 (fun x : V => f (t • x)) : V → ℂ) ((0 : Formalism.H.dual L) : V) *
      Complex.exp (2 * Real.pi * Complex.I * (⟪((0 : Formalism.H.dual L) : V), x₀⟫ : ℝ))
      = (((t ^ d)⁻¹ : ℝ) : ℂ) * ∫ x, f x := by
    rw [fourier_comp_smul_of_pos f ht, Real.fourier_eq']
    simp [hd]
  rw [h0, mul_add]
  have h3 : ∀ S : ℂ, (ZLattice.covolume L : ℂ)⁻¹ * ((((t ^ d)⁻¹ : ℝ) : ℂ) * ∫ x, f x) + S -
      (∫ x, f x) / ((ZLattice.covolume L * t ^ d : ℝ) : ℂ) = S := by
    intro S
    push_cast
    rw [div_eq_mul_inv, mul_inv]
    ring
  rw [h3, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hcov.le,
    mul_assoc (ZLattice.covolume L volume)⁻¹]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hcov.le)
  rw [← tsum_mul_left, ← tsum_mul_right]
  refine tsum_of_norm_bounded (((hs.mul_left C).mul_right (t ^ A)).hasSum) ?_
  intro y
  split_ifs with hy
  · rw [norm_zero]; positivity
  have hn : 0 < ‖(y : V)‖ := norm_pos_iff.2 (fun h => hy (Subtype.ext h))
  have he : ‖Complex.exp (2 * Real.pi * Complex.I * (⟪(y : V), x₀⟫ : ℝ))‖ = 1 := by
    rw [Complex.norm_exp]; simp
  rw [norm_mul, he, mul_one, fourier_comp_smul_of_pos f ht, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  have h4 := hC (t⁻¹ • (y : V))
  rw [norm_iteratedFDeriv_zero, _root_.norm_smul, Real.norm_of_nonneg (by positivity),
    SchwartzMap.fourier_coe, hFf] at h4
  change _ ≤ C * ‖(y : V)‖⁻¹ ^ k * t ^ A
  have h5 : ‖(𝓕 f : V → ℂ) (t⁻¹ • (y : V))‖ ≤ C * ‖(y : V)‖⁻¹ ^ k * t ^ k := by
    rw [mul_comm, ← le_div_iff₀ (by positivity)] at h4
    refine h4.trans_eq ?_
    rw [mul_pow, inv_pow, inv_pow]
    field_simp
  have h6 : t ^ k ≤ t ^ (A + d) := pow_le_pow_of_le_one ht.le ht1 (by omega)
  calc (t ^ d)⁻¹ * ‖(𝓕 f : V → ℂ) (t⁻¹ • (y : V))‖
      ≤ (t ^ d)⁻¹ * (C * ‖(y : V)‖⁻¹ ^ k * t ^ (A + d)) := by
        refine mul_le_mul_of_nonneg_left (h5.trans ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left h6 (by positivity)
    _ = _ := by rw [pow_add t A d]; field_simp
end GlobalTheory
