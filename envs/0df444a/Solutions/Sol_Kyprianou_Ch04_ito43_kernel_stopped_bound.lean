-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_kernel_stopped_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:42:37.392639+00:00
-- url     : https://prove2.me/submissions/6ddfe33f-ab63-4473-b665-f7b0bcf69d88

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch04_ito43_stopped_grid_error
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Apply the deterministic stopped grid bound to the measurable path. -/
theorem solution {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ)
    (hX : Measurable (fun z : NNReal × Omega => X z.1 z.2))
    (hCad : ∀ w, IsCadlag (fun t => X t w))
    (g : ℝ × ℝ → ℝ)
    (hg : ContinuousOn g (Ici (0 : ℝ) ×ˢ (univ : Set ℝ))) (T : NNReal) (M : Omega → ℝ)
    (hM : ∀ w, 0 ≤ M w)
    (hb : ∀ w s, s ∈ Icc (0 : ℝ) (T : ℝ) → ∀ r : NNReal, r ≤ T → |g (s,X r w)| ≤ M w) :
    ∀ n : ℕ, 0 < n → ∀ t : NNReal, t ≤ T → ∀ w,
      let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
      let v : ℕ → NNReal := fun k => min t (u k)
      |(∫ s in Icc (0 : ℝ) (t : ℝ), g (s,X (Real.toNNReal s) w)) -
        ∑ k ∈ Finset.range n,
          (∫ s in Icc (v k : ℝ) (v (k+1) : ℝ), g (s,X (v (k+1)) w))| ≤ (∑ k ∈ Finset.range n,
      (∫ s in Icc ((u k : NNReal) : ℝ) ((u (k+1) : NNReal) : ℝ),
        |g (s,X (Real.toNNReal s) w) - g (s,X (u (k+1)) w)|)) + 2 * M w * (T : ℝ) / (n : ℝ) := by
  intro n hn t ht w u v
  let H : ℝ → ℝ := fun s => g (s,X (Real.toNNReal s) w)
  let G : ℝ → ℝ → ℝ := fun s r => g (s,X (Real.toNNReal r) w)
  let a : ℕ → ℝ := fun k => (u k : ℝ)
  have hn0 : (n : NNReal) ≠ 0 := by exact_mod_cast hn.ne'
  have ha0 : a 0 = 0 := by simp [a,u]
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have han : a n = (T : ℝ) := by simp [a,u,mul_div_cancel_right₀ _ hnr]
  have ha (k : ℕ) : a k = (T : ℝ) * (k : ℝ) / (n : ℝ) := by simp [a,u]
  have hmono : Monotone a := by
    intro i j hij
    rw [ha,ha]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by exact_mod_cast hij)
      T.coe_nonneg) (by positivity)
  have hmesh (k : ℕ) (_ : k < n) : a (k+1)-a k ≤ (T : ℝ)/(n : ℝ) := by
    rw [ha,ha,Nat.cast_add,Nat.cast_one, mul_add, add_div]
    simp only [mul_one]
    linarith
  have hG (s : ℝ) (hs : s ∈ Icc 0 (T : ℝ)) (r : ℝ) (hr : r ∈ Icc 0 (T : ℝ)) :
      |G s r| ≤ M w := by
    apply hb w s hs
    exact (Real.toNNReal_le_iff_le_coe).mpr hr.2
  have hH (s : ℝ) (hs : s ∈ Icc 0 (T : ℝ)) : |H s| ≤ M w := hG s hs s hs
  have hg0 : Continuous (fun z : ℝ × ℝ => g (max 0 z.1,z.2)) :=
    hg.comp_continuous ((continuous_const.max continuous_fst).prodMk continuous_snd)
      (fun z => ⟨show 0 ≤ max 0 z.1 from le_max_left _ _,mem_univ _⟩)
  have hXm : Measurable (fun s : ℝ => X (Real.toNNReal s) w) :=
    hX.comp (measurable_real_toNNReal.prodMk measurable_const)
  have hHm : Measurable (fun s : ℝ => g (max 0 s,X (Real.toNNReal s) w)) :=
    hg0.measurable.comp (measurable_id.prodMk hXm)
  have hHi : IntegrableOn H (Icc 0 (T : ℝ)) := by
    let μ := volume.restrict (Icc 0 (T : ℝ))
    have hEq : (fun s : ℝ => g (max 0 s,X (Real.toNNReal s) w)) =ᵐ[μ] H := by
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with s hs
      simp [H,max_eq_right hs.1]
    apply (integrable_const (M w)).mono (hHm.aestronglyMeasurable.congr hEq)
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with s hs
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hM w)] using hH s hs
  have hGi (r : ℝ) (_ : r ∈ Icc 0 (T : ℝ)) : IntegrableOn (fun s => G s r) (Icc 0 (T : ℝ)) :=
    ContinuousOn.integrableOn_compact isCompact_Icc
      (hg.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun s hs => ⟨hs.1,mem_univ _⟩))
  have K := Kyprianou.Ch04.ito43_stopped_grid_error H G a hmono n (T : ℝ) (t : ℝ)
    (M w) ((T : ℝ)/(n : ℝ)) ha0 han ⟨by positivity,by exact_mod_cast ht⟩
    (hM w) (by positivity) hmesh hHi hGi hH hG
  dsimp [H,G,a] at K
  simpa only [← NNReal.coe_min,Real.toNNReal_coe, mul_div_assoc] using K
