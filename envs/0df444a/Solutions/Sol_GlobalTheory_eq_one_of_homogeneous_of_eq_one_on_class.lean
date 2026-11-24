-- Prove2me | solution 1 for GlobalTheory.eq_one_of_homogeneous_of_eq_one_on_class
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:55:06.970573+00:00
-- url     : https://prove2.me/submissions/802cb509-353e-4671-9e62-67e8753d8636

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_RayInvariantContinuousEqOne
import Theorems.Thm_GlobalTheory_exists_near_one_mod_ideal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (K : Type) [Field K] [NumberField K] (m : Ideal (𝓞 K)) (φ : mixedSpace K → ℂ), m ≠ ⊥ → ContinuousOn φ {x | mixedEmbedding.norm x ≠ 0} → (∀ (t : ℝ) x, 0 < t → φ (t • x) = φ x) → (∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → φ (mixedEmbedding K β) = 1) → ∀ x, mixedEmbedding.norm x ≠ 0 → φ x = 1 := by
  intro K _ _ m φ hm hc hh h1 x hx
  obtain ⟨C, hC⟩ := exists_near_one_mod_ideal K m hm
  choose β hβm hβ using hC
  set y : ℕ → mixedSpace K := fun n =>
    ((n : ℝ) + 1)⁻¹ • mixedEmbedding K (β (((n : ℝ) + 1) • x)) with hy
  have hpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hlim : Filter.Tendsto y Filter.atTop (nhds x) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h0 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1) * C) Filter.atTop (nhds 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const C
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) h0
    have : x - y n = ((n : ℝ) + 1)⁻¹ •
        (((n : ℝ) + 1) • x - mixedEmbedding K (β (((n : ℝ) + 1) • x))) := by
      rw [smul_sub, inv_smul_smul₀ (hpos n).ne']
    rw [norm_sub_rev, this, _root_.norm_smul, Real.norm_of_nonneg (inv_pos.mpr (hpos n)).le, one_div]
    exact mul_le_mul_of_nonneg_left (hβ _) (inv_pos.mpr (hpos n)).le
  have hopen : IsOpen {x : mixedSpace K | mixedEmbedding.norm x ≠ 0} :=
    isOpen_ne_fun (mixedEmbedding.continuous_norm K) continuous_const
  have hca : ContinuousAt φ x := hc.continuousAt (hopen.mem_nhds hx)
  have hev : ∀ᶠ n in Filter.atTop, φ (y n) = 1 := by
    filter_upwards [hlim.eventually (hopen.mem_nhds hx)] with n hn
    have hne : β (((n : ℝ) + 1) • x) ≠ 0 := by
      intro h0
      apply hn
      simp [hy, h0]
    simp only [hy]
    rw [hh _ _ (inv_pos.mpr (hpos n))]
    exact h1 _ hne (hβm _)
  have h2 : Filter.Tendsto (fun n => φ (y n)) Filter.atTop (nhds (φ x)) := hca.tendsto.comp hlim
  have h3 : Filter.Tendsto (fun n => φ (y n)) Filter.atTop (nhds 1) :=
    tendsto_const_nhds.congr' (hev.mono fun n hn => hn.symm)
  exact tendsto_nhds_unique h2 h3
end GlobalTheory
