-- Prove2me | solution 1 for ModernOnlineLearning.SaddlePoint.theorem_7_47_linear
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-20T17:40:47.579339+00:00
-- url     : https://prove2.me/submissions/4de5af33-34b2-4efb-abce-758036d44065

import Definitions.Def_ModernOnlineLearning_SaddlePoint_Setting

set_option autoImplicit false
open Filter Topology
open ModernOnlineLearning.SaddlePoint

private lemma growth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Set E) (ψ : E → ℝ) (lam : ℝ) (hstrong : StrongConvexOn V lam ψ)
    (θ : E →L[ℝ] ℝ) (x y : E)
    (hx : ModernOnlineLearning.SaddlePoint.IsMinOn V (fun z => ψ z + θ z) x) (hy : y ∈ V) :
    lam / 2 * ‖x - y‖ ^ 2 ≤ ψ y + θ y - (ψ x + θ x) := by
  have hsegment : ∀ t : ℝ, 0 < t → t < 1 →
      (1 - t) * (lam / 2 * ‖x - y‖ ^ 2) ≤ ψ y + θ y - (ψ x + θ x) := by
    intro t ht ht1
    have ha : 0 ≤ 1 - t := by linarith
    have hab : 1 - t + t = 1 := by ring
    have hv : (1 - t) • x + t • y ∈ V := hstrong.1 hx.1 hy ha ht.le hab
    have hm := hx.2 _ hv
    have hs := hstrong.2 hx.1 hy ha ht.le hab
    simp only [map_add, map_smul, smul_eq_mul] at hm hs
    nlinarith
  have hl : Tendsto (fun t : ℝ => (1 - t) * (lam / 2 * ‖x - y‖ ^ 2))
      (𝓝[>] 0) (𝓝 (lam / 2 * ‖x - y‖ ^ 2)) := by
    have hcont : ContinuousAt (fun t : ℝ => (1 - t) * (lam / 2 * ‖x - y‖ ^ 2)) 0 := by
      fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto hl
  filter_upwards [self_mem_nhdsWithin, (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with t ht ht1
  exact hsegment t ht ht1

private lemma young_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E →L[ℝ] ℝ) (z : E) (lam : ℝ) (hlam : 0 < lam) :
    g z - lam / 2 * ‖z‖ ^ 2 ≤ ‖g‖ ^ 2 / (2 * lam) := by
  have ho : g z ≤ ‖g‖ * ‖z‖ := by
    have h := g.le_opNorm z
    rw [Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  apply (le_div_iff₀ (show 0 < 2 * lam by positivity)).mpr
  nlinarith [sq_nonneg (‖g‖ - lam * ‖z‖)]

private lemma telescope (f : ℕ → ℝ) (n : ℕ) :
    (∑ t ∈ Finset.Icc 1 n, (f t - f (t + 1))) = f 1 - f (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    ring

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (V : Set E) (ψ : E → ℝ) (g : ℕ → E →L[ℝ] ℝ) (z : ℕ → E)
    (lam : ℝ) (T : ℕ) (u : E) (hT : 1 ≤ T)
    (hVne : V.Nonempty) (hVclosed : IsClosed V) (hu : u ∈ V) (hlam : 0 < lam) (hstrong : StrongConvexOn V lam ψ)
    (hrun : IsOptFTRLRun V ψ g z T) (w : E)
    (hw : ModernOnlineLearning.SaddlePoint.IsMinOn V (fun v => ψ v + ∑ i ∈ Finset.Icc 1 T, g i v) w) :
    (∑ t ∈ Finset.Icc 1 T, g t (z t - u) ≤
      ψ u - ψ (z 1) +
      ∑ t ∈ Finset.Icc 1 T,
        ((g t - g (t - 1)) (z t - (if t < T then z (t + 1) else w)) -
          lam / 2 * ‖z t - (if t < T then z (t + 1) else w)‖ ^ 2)) ∧
    (∑ t ∈ Finset.Icc 1 T, g t (z t - u) ≤
      ψ u - ψ (z 1) +
      ∑ t ∈ Finset.Icc 1 T, ‖g t - g (t - 1)‖ ^ 2 / (2 * lam))  := by
  let F : ℕ → E → ℝ := fun t v => ψ v + ∑ i ∈ Finset.Ico 1 t, g i v
  let Z : ℕ → E := fun t => if t ≤ T then z t else w
  have hZ (t : ℕ) (ht : t ∈ Finset.Icc 1 T) : Z t = z t :=
    if_pos (Finset.mem_Icc.mp ht).2
  have hZn (t : ℕ) : Z (t+1) = if t < T then z (t+1) else w := by
    dsimp only [Z]
    congr 1
  have hZmem (t : ℕ) (ht : 1 ≤ t) : Z t ∈ V := by
    by_cases h : t ≤ T
    · simpa only [Z, if_pos h] using (hrun.2 t (Finset.mem_Icc.mpr ⟨ht,h⟩)).1
    · simpa only [Z, if_neg h] using hw.1
  have hFsucc (t : ℕ) (ht : 1 ≤ t) (v : E) : F (t+1) v = F t v + g t v := by
    dsimp only [F]
    rw [Finset.sum_Ico_succ_top ht]
    ring
  have hstep (t : ℕ) (ht : t ∈ Finset.Icc 1 T) :
      F t (Z t) - F (t+1) (Z (t+1)) + g t (z t) ≤
      (g t - g (t-1)) (z t - Z (t+1)) - lam/2 * ‖z t-Z (t+1)‖^2 := by
    let θ : E →L[ℝ] ℝ := g (t-1) + ∑ i ∈ Finset.Ico 1 t, g i
    have hθ (v : E) : θ v = g (t-1) v + ∑ i ∈ Finset.Ico 1 t, g i v := by simp [θ]
    have hm : ModernOnlineLearning.SaddlePoint.IsMinOn V (fun v => ψ v + θ v) (z t) := by
      refine ⟨(hrun.2 t ht).1, ?_⟩
      intro v hv
      have h := (hrun.2 t ht).2 v hv
      simp only [hθ]
      linarith
    have hg := growth V ψ lam hstrong θ (z t) (Z (t+1)) hm (hZmem _ (by omega))
    rw [hθ, hθ] at hg
    have hg' : lam/2 * ‖z t-Z (t+1)‖^2 ≤
        F t (Z (t+1)) + g (t-1) (Z (t+1)) - (F t (z t)+g (t-1) (z t)) := by
      dsimp only [F]
      linarith
    rw [hZ t ht, hFsucc t (Finset.mem_Icc.mp ht).1]
    simp only [ContinuousLinearMap.sub_apply, map_sub]
    linarith
  have hs := Finset.sum_le_sum hstep
  have htel : (∑ t ∈ Finset.Icc 1 T,
      (F t (Z t)-F (t+1) (Z (t+1))+g t (z t))) =
      ψ (z 1)-F (T+1) w + ∑ t ∈ Finset.Icc 1 T, g t (z t) := by
    rw [Finset.sum_add_distrib, telescope (fun t => F t (Z t))]
    simp only [Z, if_pos hT, Nat.not_succ_le_self, if_false]
    simp only [F, Finset.Ico_self, Finset.sum_empty, add_zero]
  rw [htel] at hs
  have hmin : F (T+1) w ≤ F (T+1) u := by
    simpa only [F, Finset.Ico_add_one_right_eq_Icc] using hw.2 u hu
  have hFu : F (T+1) u = ψ u + ∑ t ∈ Finset.Icc 1 T, g t u := by
    simp only [F, Finset.Ico_add_one_right_eq_Icc]
  have hfirst : (∑ t ∈ Finset.Icc 1 T, g t (z t-u)) ≤
      ψ u-ψ (z 1)+(∑ t ∈ Finset.Icc 1 T,
      ((g t-g (t-1)) (z t-Z (t+1))-lam/2*‖z t-Z (t+1)‖^2)) := by
    simp only [map_sub, Finset.sum_sub_distrib] at hs ⊢
    rw [hFu] at hmin
    linarith
  constructor
  · simpa only [hZn] using hfirst
  · apply hfirst.trans
    apply add_le_add le_rfl
    apply Finset.sum_le_sum
    intro t ht
    exact young_bound (g t-g (t-1)) (z t-Z (t+1)) lam hlam

