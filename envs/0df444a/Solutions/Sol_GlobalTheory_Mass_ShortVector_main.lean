-- Prove2me | solution 1 for GlobalTheory.Mass.ShortVector.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:45:48.338783+00:00
-- url     : https://prove2.me/submissions/060ead2f-505d-4c3d-acbd-1d7a626fbb0d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RegulatorLeSumSmallIdealsInClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsShortVectorIntegralHermitianLatticeRankOne
import Theorems.Thm_GlobalTheory_Mass_ShortVector_nondeg
import Theorems.Thm_GlobalTheory_Mass_ShortVector_exists_gen
import Theorems.Thm_GlobalTheory_RegulatorClassBound_exists_mem_box
import Theorems.Thm_GlobalTheory_RegulatorClassBound_sum_mult_log


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.ShortVector
open GlobalTheory.Mass.DiscOrder
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.Mass.ShortVector
theorem _root_.solution : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → Module.finrank K V = 1 → ∀ M : Submodule (𝓞 K) V, IsIntLat h M → ∃ x ∈ M, x ≠ 0 ∧ ∀ τ : K →+* ℂ, (τ (h x x)).re ≤ (2 * vInv K) * (discN h M : ℝ) ^ ((1 : ℝ) / (2 * fDeg K)) := by
  intro K V _ _ _ _ _ _ _ _ h hK hs hp h1 M hM
  have hn := nondeg h hp
  obtain ⟨x₀, b, I, hx0, hb, hI, hIM, hnorm⟩ := exists_gen h hs hn h1 M hM
  have hTC : IsTotallyComplex K := hK.1
  have hstar := hK.2.1
  have hbK0 : (b : K) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hb
    exact zero_ne_one hb
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hbK0
  have hNI : (0 : ℝ) < Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hNb : (0 : ℝ) < Ideal.absNorm (Ideal.span {b}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hb0))
  have hnormR : ((Ideal.absNorm I : ℕ) : ℝ) ^ 2 =
      (Ideal.absNorm (Ideal.span {b}) : ℝ) * (discN h M : ℝ) := by
    exact_mod_cast hnorm
  have hD : (0 : ℝ) < discN h M := by
    by_contra hD
    have h0 : (discN h M : ℝ) = 0 := le_antisymm (not_lt.mp hD) (Nat.cast_nonneg _)
    rw [h0, mul_zero] at hnormR
    exact (pow_pos hNI 2).ne' hnormR
  have hf : (0 : ℝ) < fDeg K := by
    unfold fDeg
    exact_mod_cast Fintype.card_pos
  have hf0 := hf.ne'
  have hdK : (0 : ℝ) < |(discr K : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero K)
  have hv : 2 * vInv K = |(discr K : ℝ)| ^ ((1 : ℝ) / (2 * (fDeg K : ℝ))) := by
    rw [vInv]
    ring
  have hT : 0 < 2 * vInv K * (discN h M : ℝ) ^ ((1 : ℝ) / (2 * fDeg K)) := by
    rw [hv]
    exact mul_pos (Real.rpow_pos_of_pos hdK _) (Real.rpow_pos_of_pos hD _)
  have hlogT : (fDeg K : ℝ) * Real.log (2 * vInv K * (discN h M : ℝ) ^ ((1 : ℝ) / (2 * fDeg K))) =
      (Real.log |(discr K : ℝ)| + Real.log (discN h M : ℝ)) / 2 := by
    rw [hv, Real.log_mul (Real.rpow_pos_of_pos hdK _).ne' (Real.rpow_pos_of_pos hD _).ne',
      Real.log_rpow hdK, Real.log_rpow hD]
    field_simp
  have hI2 : 2 * Real.log (Ideal.absNorm I : ℝ) =
      Real.log (Ideal.absNorm (Ideal.span {b}) : ℝ) + Real.log (discN h M : ℝ) := by
    rw [← Real.log_mul hNb.ne' hD.ne', ← hnormR, Real.log_pow]
    norm_num
  set T : ℝ := 2 * vInv K * (discN h M : ℝ) ^ ((1 : ℝ) / (2 * fDeg K)) with hTdef
  have hmult : ∀ w : InfinitePlace K, (w.mult : ℝ) = 2 := by
    intro w
    simp [InfinitePlace.mult, InfinitePlace.not_isReal_iff_isComplex.mpr (hTC.isComplex w)]
  have hsum := GlobalTheory.RegulatorClassBound.sum_mult_log K b hb0
  have hc : ∑ w : InfinitePlace K, (w.mult : ℝ) * ((Real.log T + Real.log (w (b : K))) / 2) =
      Real.log ((Ideal.absNorm I : ℝ) * Real.sqrt |(discr K : ℝ)|) := by
    have e : ∀ w : InfinitePlace K, (w.mult : ℝ) * ((Real.log T + Real.log (w (b : K))) / 2) =
        Real.log T + (w.mult : ℝ) * Real.log (w (b : K)) / 2 := by
      intro w
      rw [hmult w]
      ring
    rw [Finset.sum_congr rfl fun w _ => e w, Finset.sum_add_distrib, ← Finset.sum_div, hsum,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Real.log_mul hNI.ne' (Real.sqrt_pos.mpr hdK).ne', Real.log_sqrt hdK.le]
    have hfc : ((Fintype.card (InfinitePlace K) : ℕ) : ℝ) = (fDeg K : ℝ) := rfl
    rw [hfc]
    linarith [hlogT, hI2]
  obtain ⟨a, haI, ha0, hab⟩ := GlobalTheory.RegulatorClassBound.exists_mem_box K I hI
    (fun w => (Real.log T + Real.log (w (b : K))) / 2) hc
  have haK : algebraMap (𝓞 K) K a ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).mpr ha0
  refine ⟨a • x₀, hIM a haI, ?_, fun τ => ?_⟩
  · rw [← algebraMap_smul K a x₀]
    exact smul_ne_zero haK hx0
  · have hh0 : starRingEnd K (h x₀ x₀) = h x₀ x₀ := hs.eq x₀ x₀
    have hreal : (((τ (h x₀ x₀)).re : ℝ) : ℂ) = τ (h x₀ x₀) := by
      apply Complex.conj_eq_iff_re.mp
      rw [← hstar, ← starRingEnd_apply, hh0]
    obtain ⟨r, hrc⟩ : ∃ r : ℝ, (r : ℂ) = τ (h x₀ x₀) := ⟨_, hreal⟩
    have hr : 0 < r := by
      have hpos := hp τ x₀ hx0
      rwa [← hrc, Complex.ofReal_re] at hpos
    have hbr : ‖τ (b : K)‖ * r = 1 := by
      have e := congrArg (fun z => ‖τ z‖) hb
      simp only [map_mul, map_one, norm_mul, norm_one] at e
      rw [← hrc, Complex.norm_real, Real.norm_of_nonneg hr.le] at e
      exact e
    have hw : ∀ z : K, (InfinitePlace.mk τ) z = ‖τ z‖ := fun z => InfinitePlace.apply τ z
    have hbpos : 0 < ‖τ (b : K)‖ := norm_pos_iff.mpr ((map_ne_zero τ).mpr hbK0)
    have ha' := hab (InfinitePlace.mk τ)
    rw [hw, hw] at ha'
    have hsq : ‖τ (a : K)‖ * ‖τ (a : K)‖ < T * ‖τ (b : K)‖ := by
      have hmm := mul_self_lt_mul_self (norm_nonneg _) ha'
      rwa [← Real.exp_add, add_halves, Real.exp_add, Real.exp_log hT, Real.exp_log hbpos] at hmm
    have hvx : (τ (h (a • x₀) (a • x₀))).re = ‖τ (a : K)‖ * ‖τ (a : K)‖ * r := by
      rw [← algebraMap_smul K a x₀, LinearMap.map_smulₛₗ₂, LinearMap.map_smul, smul_eq_mul,
        smul_eq_mul, map_mul, map_mul, starRingEnd_apply, hstar, ← hrc, ← mul_assoc,
        ← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_mul, Complex.ofReal_re,
        Complex.normSq_eq_norm_sq, sq]
    rw [hvx]
    calc ‖τ (a : K)‖ * ‖τ (a : K)‖ * r ≤ T * ‖τ (b : K)‖ * r :=
          mul_le_mul_of_nonneg_right hsq.le hr.le
      _ = T := by rw [mul_assoc, hbr, mul_one]
end GlobalTheory.Mass.ShortVector
