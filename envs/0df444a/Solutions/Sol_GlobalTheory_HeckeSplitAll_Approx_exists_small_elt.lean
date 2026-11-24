-- Prove2me | solution 1 for GlobalTheory.HeckeSplitAll.Approx.exists_small_elt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:32:26.306345+00:00
-- url     : https://prove2.me/submissions/63bb18f5-e0b4-4e21-8943-adef91e00d4a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentApproximation_AddDense
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsFinsetNormOne
import Theorems.Thm_GlobalTheory_HeckeSplitAll_Approx_norm_int_le_one
import Theorems.Thm_GlobalTheory_HeckeSplitAll_Approx_norm_int_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Topology Filter
open GlobalTheory GlobalTheory.HeckeSplitAll GlobalTheory.HeckeSplitAll.Approx
variable {F : Type} [Field F] [NumberField F]
open NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory ENNReal Module
open scoped nonZeroDivisors
namespace GlobalTheory.HeckeSplitAll.Approx
theorem _root_.solution (v₀ : HeightOneSpectrum (𝓞 F)) (η : ℝ) (hη : 0 < η) :
    ∃ x : F, x ≠ 0 ∧ (∀ w : InfinitePlace F, w x < η) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), v ≠ v₀ → ‖algebraMap F (v.adicCompletion F) x‖ ≤ 1 := by
  classical
  let f : InfinitePlace F → NNReal := fun _ => ⟨η, hη.le⟩
  have hV : volume (convexBodyLT F f) ≠ ⊤ := by
    rw [convexBodyLT_volume]; exact mul_ne_top coe_ne_top coe_ne_top
  have hV0 : 0 < (volume (convexBodyLT F f)).toReal := by
    rw [convexBodyLT_volume, toReal_mul, coe_toReal, coe_toReal]
    have h1 : (1 : ℝ) ≤ convexBodyLTFactor F := by exact_mod_cast one_le_convexBodyLTFactor F
    refine mul_pos (by linarith) ?_
    rw [NNReal.coe_prod]
    exact Finset.prod_pos fun w _ => by rw [NNReal.coe_pow]; exact pow_pos hη _
  set B : ℝ := (volume (ZSpan.fundamentalDomain (latticeBasis F))).toReal * 2 ^ finrank ℝ (mixedSpace F) with hB
  have hq : (1 : ℝ) < Ideal.absNorm v₀.asIdeal := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v₀
  have ht : Tendsto (fun k : ℕ => ((Ideal.absNorm v₀.asIdeal : ℝ)⁻¹) ^ k * B) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (Ideal.absNorm v₀.asIdeal : ℝ)⁻¹) (by positivity)
      (inv_lt_one_of_one_lt₀ hq)).mul_const B
    rwa [zero_mul] at this
  obtain ⟨k, hk⟩ := (ht.eventually (Iio_mem_nhds hV0)).exists
  have hI : ((v₀.asIdeal ^ k : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (pow_ne_zero k v₀.ne_bot)
  let J : (FractionalIdeal (𝓞 F)⁰ F)ˣ := Units.mk0 _ (inv_ne_zero hI)
  have h : minkowskiBound F J < volume (convexBodyLT F f) := by
    rw [← ENNReal.toReal_lt_toReal (minkowskiBound_lt_top F J).ne hV]
    refine lt_of_eq_of_lt ?_ hk
    rw [minkowskiBound, volume_fundamentalDomain_fractionalIdealLatticeBasis, toReal_mul, toReal_mul, toReal_pow,
      ENNReal.toReal_ofReal (Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg _)), hB]
    simp only [J, Units.val_mk0, map_inv₀, FractionalIdeal.coeIdeal_absNorm, map_pow, toReal_ofNat]
    push_cast
    rw [inv_pow]
    ring
  obtain ⟨a, ha, hne, hlt⟩ := exists_ne_zero_mem_ideal_lt F J h
  refine ⟨a, hne, fun w => hlt w, fun v hv => ?_⟩
  obtain ⟨p, hp0, hpv⟩ : ∃ p ∈ v₀.asIdeal, p ∉ v.asIdeal := by
    by_contra hc
    push Not at hc
    exact hv (HeightOneSpectrum.ext (v₀.isMaximal.eq_of_le v.isPrime.ne_top hc).symm)
  have hm : a * algebraMap (𝓞 F) F (p ^ k) ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [← inv_mul_cancel₀ hI]
    exact FractionalIdeal.mul_mem_mul ha (FractionalIdeal.mem_coeIdeal_of_mem _ (Ideal.pow_mem_pow hp0 k))
  obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 hm
  have h1 := norm_int_le_one v o
  rw [show (o : F) = algebraMap (𝓞 F) F o from rfl, ho, map_mul, norm_mul, map_pow, map_pow, norm_pow] at h1
  have h2 := norm_int_eq_one v p hpv
  rw [show (p : F) = algebraMap (𝓞 F) F p from rfl] at h2
  rwa [h2, one_pow, mul_one] at h1
end GlobalTheory.HeckeSplitAll.Approx
