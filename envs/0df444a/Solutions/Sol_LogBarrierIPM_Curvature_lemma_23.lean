-- Prove2me | solution 1 for LogBarrierIPM.Curvature.lemma_23
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T02:11:40.462978+00:00
-- url     : https://prove2.me/submissions/b51b426c-7641-4bc5-84b6-9a2c32a1af09

import Mathlib
import Definitions.Def_LogBarrierIPM_Curvature_TotalCurvature
import Definitions.Def_LogBarrierIPM_Curvature_Puiseux
import Definitions.Def_LogBarrierIPM_Curvature_TropicalAngle

set_option autoImplicit false

open Filter Topology

namespace LogBarrierIPM.Curvature.L23

open LogBarrierIPM.Curvature

lemma exists_greatest (f : Puiseux) (hne : (Function.support f.coeff).Nonempty) :
    IsGreatest (Function.support f.coeff) (sSup (Function.support f.coeff)) := by
  obtain ⟨s0, hs0⟩ := hne
  set T : Set ℝ := {β | s0 ≤ β ∧ f.coeff β ≠ 0} with hT
  have hTf : T.Finite := f.support_finite_above s0
  have hTne : T.Nonempty := ⟨s0, le_refl _, hs0⟩
  have hm : sSup T ∈ T := hTne.csSup_mem hTf
  have hG : IsGreatest (Function.support f.coeff) (sSup T) := by
    refine ⟨hm.2, ?_⟩
    intro β hβ
    by_cases h : s0 ≤ β
    · exact le_csSup hTf.bddAbove ⟨h, hβ⟩
    · exact (lt_of_not_ge h).le.trans hm.1
  rw [hG.csSup_eq]
  exact hG

lemma coeff_le_val (f : Puiseux) {α : ℝ} (h : f.coeff α ≠ 0) : (α : WithBot ℝ) ≤ f.val := by
  have hne : (Function.support f.coeff).Nonempty := ⟨α, h⟩
  rw [Puiseux.val, if_pos hne]
  exact WithBot.coe_le_coe.mpr ((exists_greatest f hne).2 h)

lemma coeff_val_ne (f : Puiseux) {v : ℝ} (h : f.val = (v : WithBot ℝ)) : f.coeff v ≠ 0 := by
  by_cases hne : (Function.support f.coeff).Nonempty
  · rw [Puiseux.val, if_pos hne] at h
    have hv : sSup (Function.support f.coeff) = v := WithBot.coe_injective h
    have := (exists_greatest f hne).1
    rw [hv] at this
    exact this
  · rw [Puiseux.val, if_neg hne] at h
    exact absurd h.symm (WithBot.coe_ne_bot)

lemma tendsto_eval_div (f : Puiseux) {v : ℝ} (hv : f.val ≤ (v : WithBot ℝ)) :
    Tendsto (fun t : ℝ => f.eval t / t ^ v) atTop (𝓝 (f.coeff v)) := by
  obtain ⟨ρ, hρ, hs⟩ := f.abs_summable
  set t0 := ρ + 1 with ht0
  have ht0pos : 0 < t0 := by linarith
  have hsum := hs t0 (by linarith)
  have hle : ∀ α, f.coeff α ≠ 0 → α ≤ v := fun α h =>
    WithBot.coe_le_coe.mp ((coeff_le_val f h).trans hv)
  have key : Tendsto (fun t : ℝ => ∑' α : ℝ, f.coeff α * t ^ (α - v)) atTop
      (𝓝 (∑' α : ℝ, if α = v then f.coeff v else 0)) := by
    apply tendsto_tsum_of_dominated_convergence
      (bound := fun α => |f.coeff α| * t0 ^ α * t0 ^ (-v))
    · exact hsum.mul_right _
    · intro α
      by_cases hα : f.coeff α = 0
      · split_ifs with h
        · subst h; simp [hα]
        · simp [hα]
      · rcases (hle α hα).lt_or_eq with hlt | heq
        · rw [if_neg hlt.ne]
          have h1 : Tendsto (fun t : ℝ => t ^ (α - v)) atTop (𝓝 0) := by
            have := tendsto_rpow_neg_atTop (y := v - α) (by linarith)
            simpa [neg_sub] using this
          simpa using h1.const_mul (f.coeff α)
        · subst heq
          simp
    · filter_upwards [eventually_ge_atTop t0] with t ht α
      have htpos : 0 < t := lt_of_lt_of_le ht0pos ht
      by_cases hα : f.coeff α = 0
      · simp only [hα, zero_mul, norm_zero]
        positivity
      · have hα' := hle α hα
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos htpos _), mul_assoc,
          ← Real.rpow_add ht0pos]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        rw [← sub_eq_add_neg]
        exact Real.rpow_le_rpow_of_nonpos ht0pos ht (by linarith)
  rw [tsum_ite_eq] at key
  refine key.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [Puiseux.eval, ← tsum_div_const]
  congr 1
  ext α
  rw [Real.rpow_sub ht, mul_div_assoc]

end LogBarrierIPM.Curvature.L23

open Filter Topology LogBarrierIPM.Curvature in
theorem solution {d : ℕ} (U V W : Fin d → Puiseux)
    (hUV : tmax (valVec U) < tmax (valVec V)) (hVW : tmax (valVec V) < tmax (valVec W))
    (hdisj : Disjoint (targmax (valVec V)) (targmax (valVec W))) :
    Tendsto (fun t : ℝ => turningAngle (evalVec U t) (evalVec V t) (evalVec W t))
      atTop (𝓝 (Real.pi / 2)) := by
  classical
  obtain ⟨b, hb⟩ := WithBot.ne_bot_iff_exists.mp (ne_bot_of_gt hUV)
  obtain ⟨c, hc⟩ := WithBot.ne_bot_iff_exists.mp (ne_bot_of_gt hVW)
  have hle : ∀ (X : Fin d → Puiseux) i, (X i).val ≤ tmax (valVec X) := fun X i =>
    Finset.le_sup (f := valVec X) (Finset.mem_univ i)
  have hbc : b < c := by
    have := hVW; rw [← hb, ← hc] at this; exact WithBot.coe_lt_coe.mp this
  have hUb : ∀ i, (U i).val ≤ (b : WithBot ℝ) := fun i => (hle U i).trans (hb ▸ hUV.le)
  have hVb : ∀ i, (V i).val ≤ (b : WithBot ℝ) := fun i => (hle V i).trans hb.symm.le
  have hUc : ∀ i, (U i).val ≤ (c : WithBot ℝ) := fun i =>
    (hUb i).trans (WithBot.coe_le_coe.mpr hbc.le)
  have hVc : ∀ i, (V i).val ≤ (c : WithBot ℝ) := fun i =>
    (hVb i).trans (WithBot.coe_le_coe.mpr hbc.le)
  have hWc : ∀ i, (W i).val ≤ (c : WithBot ℝ) := fun i => (hle W i).trans hc.symm.le
  have hU0 : ∀ i, (U i).coeff b = 0 := by
    intro i; by_contra h
    have h1 := (L23.coeff_le_val (U i) h).trans (hle U i)
    rw [← hb] at hUV
    exact absurd (lt_of_le_of_lt h1 hUV) (lt_irrefl _)
  have hV0 : ∀ i, (V i).coeff c = 0 := by
    intro i; by_contra h
    have h1 := (L23.coeff_le_val (V i) h).trans (hle V i)
    rw [← hc] at hVW
    exact absurd (lt_of_le_of_lt h1 hVW) (lt_irrefl _)
  set p : Fin d → ℝ := fun i => (V i).coeff b with hp
  set q : Fin d → ℝ := fun i => (W i).coeff c with hq
  -- nonemptiness of the index set
  have huniv : (Finset.univ : Finset (Fin d)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have : tmax (valVec V) = ⊥ := by simp [tmax, h]
    rw [this] at hUV
    exact absurd hUV not_lt_bot
  have hP : (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin d)) ≠ 0 := by
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup _ huniv (valVec V)
    have hvi : (V i).val = (b : WithBot ℝ) := by
      rw [hb]; exact hi.symm
    intro h0
    have := congrArg (fun x : EuclideanSpace ℝ (Fin d) => x i) h0
    simp only at this
    exact L23.coeff_val_ne (V i) hvi (by simpa [p] using this)
  have hQ : (WithLp.toLp 2 q : EuclideanSpace ℝ (Fin d)) ≠ 0 := by
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup _ huniv (valVec W)
    have hvi : (W i).val = (c : WithBot ℝ) := by
      rw [hc]; exact hi.symm
    intro h0
    have := congrArg (fun x : EuclideanSpace ℝ (Fin d) => x i) h0
    simp only at this
    exact L23.coeff_val_ne (W i) hvi (by simpa [q] using this)
  have hPQ : inner ℝ (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin d)) (WithLp.toLp 2 q) = 0 := by
    rw [PiLp.inner_apply]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hpi : p i = 0
    · simp [hpi]
    by_cases hqi : q i = 0
    · simp [hqi]
    exfalso
    have hiV : i ∈ targmax (valVec V) := by
      show valVec V i = tmax (valVec V)
      rw [← hb]
      exact le_antisymm (by rw [hb]; exact hle V i) (L23.coeff_le_val (V i) hpi)
    have hiW : i ∈ targmax (valVec W) := by
      show valVec W i = tmax (valVec W)
      rw [← hc]
      exact le_antisymm (by rw [hc]; exact hle W i) (L23.coeff_le_val (W i) hqi)
    exact Set.disjoint_left.mp hdisj hiV hiW
  have hX : Tendsto (fun t : ℝ => (t ^ b)⁻¹ • (evalVec V t - evalVec U t)) atTop
      (𝓝 (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin d))) := by
    have hF : Tendsto (fun t : ℝ => (WithLp.toLp 2
        (fun i => (V i).eval t / t ^ b - (U i).eval t / t ^ b) : EuclideanSpace ℝ (Fin d)))
        atTop (𝓝 (WithLp.toLp 2 p)) := by
      refine ((PiLp.continuous_toLp 2 _).tendsto _).comp ?_
      refine tendsto_pi_nhds.mpr fun i => ?_
      have := (L23.tendsto_eval_div (V i) (hVb i)).sub (L23.tendsto_eval_div (U i) (hUb i))
      simpa [hU0 i, p] using this
    refine hF.congr' (Eventually.of_forall fun t => ?_)
    ext i
    simp [evalVec, div_eq_inv_mul, mul_sub]
  have hY : Tendsto (fun t : ℝ => (t ^ c)⁻¹ • (evalVec W t - evalVec V t)) atTop
      (𝓝 (WithLp.toLp 2 q : EuclideanSpace ℝ (Fin d))) := by
    have hF : Tendsto (fun t : ℝ => (WithLp.toLp 2
        (fun i => (W i).eval t / t ^ c - (V i).eval t / t ^ c) : EuclideanSpace ℝ (Fin d)))
        atTop (𝓝 (WithLp.toLp 2 q)) := by
      refine ((PiLp.continuous_toLp 2 _).tendsto _).comp ?_
      refine tendsto_pi_nhds.mpr fun i => ?_
      have := (L23.tendsto_eval_div (W i) (hWc i)).sub (L23.tendsto_eval_div (V i) (hVc i))
      simpa [hV0 i, q] using this
    refine hF.congr' (Eventually.of_forall fun t => ?_)
    ext i
    simp [evalVec, div_eq_inv_mul, mul_sub]
  have hA := ((InnerProductGeometry.continuousAt_angle
    (x := ((WithLp.toLp 2 p : EuclideanSpace ℝ (Fin d)), (WithLp.toLp 2 q : EuclideanSpace ℝ (Fin d))))
    hP hQ).tendsto).comp (hX.prodMk_nhds hY)
  rw [show InnerProductGeometry.angle (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin d))
      (WithLp.toLp 2 q) = Real.pi / 2 from
    (InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two _ _).mp hPQ] at hA
  refine hA.congr' ?_
  filter_upwards [eventually_gt_atTop 0, hX.eventually_ne hP, hY.eventually_ne hQ]
    with t ht hXt hYt
  have hb0 : 0 < (t ^ b)⁻¹ := inv_pos.mpr (Real.rpow_pos_of_pos ht _)
  have hc0 : 0 < (t ^ c)⁻¹ := inv_pos.mpr (Real.rpow_pos_of_pos ht _)
  have h1 : evalVec U t ≠ evalVec V t := by
    intro h; apply hXt; rw [h, sub_self, smul_zero]
  have h2 : evalVec V t ≠ evalVec W t := by
    intro h; apply hYt; rw [h, sub_self, smul_zero]
  simp only [Function.comp_apply, turningAngle, h1, h2, or_self, if_false]
  rw [InnerProductGeometry.angle_smul_left_of_pos _ _ hb0,
    InnerProductGeometry.angle_smul_right_of_pos _ _ hc0]
