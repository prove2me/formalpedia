-- Prove2me | solution 1 for LostSalesOldNew.StateReduction.claim_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:10:09.971871+00:00
-- url     : https://prove2.me/submissions/40974d7e-4016-41d1-bcdc-5217230ac4dd

import Mathlib
import Definitions.Def_LostSalesOldNew_StateReduction_Model

set_option autoImplicit false
open LostSalesOldNew.StateReduction MeasureTheory ProbabilityTheory Filter

lemma LSS_snoc_tail {L : ℕ} (x : Fin L → ℝ) (z : ℝ) (l : Fin L) :
    ∑ m : Fin L, (if (l : ℕ) ≤ (m : ℕ) then (Fin.snoc (α := fun _ => ℝ) x z) m.succ else 0)
      = v x ((l : ℕ) + 1) + z := by
  have h1 : ∑ m' : Fin (L + 1), (if (l : ℕ) + 1 ≤ (m' : ℕ) then (Fin.snoc (α := fun _ => ℝ) x z) m' else 0)
      = v x ((l : ℕ) + 1) + z := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.snoc_castSucc, Fin.snoc_last, Fin.val_last, v]
    have : (l : ℕ) + 1 ≤ L := l.isLt
    simp [this]
  rw [← h1, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ]
  simp

lemma LSS_next_apply {L : ℕ} (hL : 0 < L) (x : Fin L → ℝ) (z d : ℝ) (i : Fin L) :
    next x z d i = (if (i : ℕ) = 0 then max (x ⟨0, hL⟩ - d) 0 else 0) +
      (Fin.snoc (α := fun _ => ℝ) x z) i.succ := by
  unfold next shift
  by_cases h : (i : ℕ) = 0
  · have h0 : (Fin.snoc (α := fun _ => ℝ) x z) (0 : Fin (L + 1)) = x ⟨0, hL⟩ := by
      have : (0 : Fin (L + 1)) = Fin.castSucc ⟨0, hL⟩ := Fin.ext rfl
      rw [this, Fin.snoc_castSucc]
    simp [h, h0]
  · simp [h]


theorem LSS_inv {L : ℕ} (hL : 0 < L)
    (s : Fin (L + 1) → ℝ) (hs : IsLevelVector s)
    (z : (Fin L → ℝ) → ℝ) (hz : z ∈ Zs s) (x : Fin L → ℝ) (hx : x ∈ Xs s)
    (d : ℝ) (hd : 0 ≤ d) :
    next x (z x) d ∈ Xs s := by
  obtain ⟨hz0, hz1, hz2⟩ := hz
  obtain ⟨hx0, hx1⟩ := hx
  have hzx : 0 ≤ z x := hz0 x hx0
  have hy : ∀ i : Fin (L + 1), 0 ≤ (Fin.snoc (α := fun _ => ℝ) x (z x)) i := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hzx
    · simpa using hx0 j
  have hxs : x ∈ Xs s := ⟨hx0, hx1⟩
  have hM : 0 ≤ max (x ⟨0, hL⟩ - d) 0 := le_max_right _ _
  refine ⟨?_, ?_⟩
  · intro i
    rw [LSS_next_apply hL]
    have := hy i.succ
    split_ifs <;> linarith
  · intro l
    have key : v (next x (z x) d) (l : ℕ) =
        (if (l : ℕ) = 0 then max (x ⟨0, hL⟩ - d) 0 else 0) + (v x ((l : ℕ) + 1) + z x) := by
      rw [← LSS_snoc_tail x (z x) l]
      unfold v
      have e : ∀ m : Fin L, (if (l : ℕ) ≤ (m : ℕ) then next x (z x) d m else 0) =
          (if m = ⟨0, hL⟩ then (if (l : ℕ) = 0 then max (x ⟨0, hL⟩ - d) 0 else 0) else 0) +
          (if (l : ℕ) ≤ (m : ℕ) then (Fin.snoc (α := fun _ => ℝ) x (z x)) m.succ else 0) := by
        intro m
        rw [LSS_next_apply hL]
        by_cases hm : m = ⟨0, hL⟩
        · have hm' : (m : ℕ) = 0 := by rw [hm]
          by_cases hl : (l : ℕ) = 0
          · simp [hm, hl]
          · simp [hm, hl]
        · have hm' : (m : ℕ) ≠ 0 := fun h => hm (Fin.ext h)
          simp [hm, hm']
      simp only [e, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [key]
    have hl1 : (l : ℕ) + 1 < L + 1 + 1 := by omega
    by_cases hl : (l : ℕ) = 0
    · rw [if_pos hl]
      have h0 := hz2 x hxs ⟨0, by omega⟩
      have hv0 : v x 0 = v x 1 + x ⟨0, hL⟩ := by
        unfold v
        have e : ∀ m : Fin L, (if 0 ≤ (m : ℕ) then x m else 0) =
            (if 1 ≤ (m : ℕ) then x m else 0) + (if m = ⟨0, hL⟩ then x m else 0) := by
          intro m
          by_cases hm : m = ⟨0, hL⟩
          · have hm' : (m : ℕ) = 0 := by rw [hm]
            simp [hm, hm']
          · have hm' : (m : ℕ) ≠ 0 := fun h => hm (Fin.ext h)
            have : 1 ≤ (m : ℕ) := by omega
            simp [hm, this]
        simp only [e, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      have hv1 : (l : ℕ) + 1 = 1 := by omega
      have hlc : l.castSucc = (⟨0, by omega⟩ : Fin (L + 1)) := Fin.ext hl
      rw [hv1, hlc]
      have hxx : max (x ⟨0, hL⟩ - d) 0 ≤ x ⟨0, hL⟩ := max_le (by linarith) (hx0 _)
      linarith
    · rw [if_neg hl]
      have := hz2 x hxs ⟨(l : ℕ) + 1, by omega⟩
      have hanti := hs.1 (show l.castSucc ≤ (⟨(l : ℕ) + 1, by omega⟩ : Fin (L + 1)) from by
        simp [Fin.le_def])
      simp only at this
      linarith

lemma LSS_snoc_succ {L : ℕ} (x : Fin L → ℝ) (z : ℝ) (m : Fin L) :
    (Fin.snoc (α := fun _ => ℝ) x z) m.succ =
      if h : (m : ℕ) + 1 < L then x ⟨(m : ℕ) + 1, h⟩ else z := by
  by_cases h : (m : ℕ) + 1 < L
  · have : m.succ = Fin.castSucc (⟨(m : ℕ) + 1, h⟩ : Fin L) := Fin.ext rfl
    rw [this, Fin.snoc_castSucc]
    simp [h]
  · have : m.succ = Fin.last L := Fin.ext (by simp; omega)
    rw [this, Fin.snoc_last]
    simp [h]


theorem LSS_reach {L : ℕ} (hL : 0 < L)
    (s : Fin (L + 1) → ℝ) (hs : IsLevelVector s)
    (z : (Fin L → ℝ) → ℝ) (hz : z ∈ Zs s) (x : Fin L → ℝ) (hx : ∀ i, 0 ≤ x i)
    (ds : ℕ → ℝ) (hds : ∀ t, 0 ≤ ds t)
    (hdiv : Filter.Tendsto (fun n => ∑ t ∈ Finset.range n, ds t) Filter.atTop Filter.atTop) :
    ∃ t, traj z x ds t ∈ Xs s := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hz0, hz1, hz2⟩ := hz
  have hnn : ∀ t i, 0 ≤ traj z x ds t i := by
    intro t
    induction t with
    | zero => exact hx
    | succ t ih =>
      intro i
      show 0 ≤ next (traj z x ds t) (z (traj z x ds t)) (ds t) i
      rw [LSS_next_apply hL, LSS_snoc_succ]
      have h1 : 0 ≤ max (traj z x ds t ⟨0, hL⟩ - ds t) 0 := le_max_right _ _
      have h2 := hz0 _ ih
      split_ifs <;> first | linarith | exact add_nonneg (by linarith) (ih _)
  have hzero : ∀ t, z (traj z x ds t) = 0 := fun t => hz1 _ (hnn t) (hcon t)
  have hstep : ∀ t, traj z x ds (t + 1) = next (traj z x ds t) 0 (ds t) := by
    intro t
    show next (traj z x ds t) (z (traj z x ds t)) (ds t) = _
    rw [hzero t]
  have htail : ∀ t (m : Fin L), 1 ≤ (m : ℕ) → L ≤ (m : ℕ) + t → traj z x ds t m = 0 := by
    intro t
    induction t with
    | zero => intro m _ h; have := m.isLt; omega
    | succ t ih =>
      intro m hm h
      rw [hstep, LSS_next_apply hL, LSS_snoc_succ, if_neg (by omega), zero_add]
      by_cases h' : (m : ℕ) + 1 < L
      · rw [dif_pos h']
        exact ih _ (by simp) (by simp; omega)
      · rw [dif_neg h']
  have hy : ∀ t, L ≤ t → traj z x ds (t + 1) ⟨0, hL⟩ = max (traj z x ds t ⟨0, hL⟩ - ds t) 0 := by
    intro t ht
    rw [hstep, LSS_next_apply hL, LSS_snoc_succ]
    simp only [if_true]
    by_cases h' : 1 < L
    · rw [dif_pos (by simpa using h')]
      have := htail t ⟨1, h'⟩ (by simp) (by simp; omega)
      simp [this]
    · rw [dif_neg (by simpa using h')]
      simp
  have hyn : ∀ n, traj z x ds (L + n) ⟨0, hL⟩ =
      max (traj z x ds L ⟨0, hL⟩ - ∑ u ∈ Finset.range n, ds (L + u)) 0 := by
    intro n
    induction n with
    | zero => simp [le_of_lt, max_eq_left (hnn L _)]
    | succ n ih =>
      rw [← add_assoc, hy (L + n) (by omega), ih, Finset.sum_range_succ]
      have := hds (L + n)
      rcases le_total (traj z x ds L ⟨0, hL⟩ - ∑ u ∈ Finset.range n, ds (L + u)) 0 with h | h
      · rw [max_eq_right h, max_eq_right (by linarith), max_eq_right (by linarith)]
      · rw [max_eq_left h]
        rcases le_total (traj z x ds L ⟨0, hL⟩ - ∑ u ∈ Finset.range n, ds (L + u) - ds (L + n)) 0 with h2 | h2
        · rw [max_eq_right h2, max_eq_right (by linarith)]
        · rw [max_eq_left h2, max_eq_left (by linarith)]
          ring_nf
  set C : ℝ := traj z x ds L ⟨0, hL⟩ + ∑ t ∈ Finset.range L, ds t with hC
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 (Filter.tendsto_atTop.1 hdiv C)
  have hsum := hM (L + M) (by omega)
  rw [Finset.sum_range_add] at hsum
  have hy0 : traj z x ds (L + M) ⟨0, hL⟩ = 0 := by
    rw [hyn]
    apply max_eq_right
    linarith
  apply hcon (L + M)
  have hall : ∀ m : Fin L, traj z x ds (L + M) m = 0 := by
    intro m
    by_cases hm : (m : ℕ) = 0
    · have : m = ⟨0, hL⟩ := Fin.ext hm
      rw [this]; exact hy0
    · exact htail _ m (by omega) (by omega)
  refine ⟨hnn _, ?_⟩
  intro l
  have hv : v (traj z x ds (L + M)) l = 0 := by
    unfold v
    apply Finset.sum_eq_zero
    intro m _
    rw [hall m]
    simp
  rw [hv]
  have := hs.1 (Fin.le_last l.castSucc)
  linarith [hs.2]


theorem solution {L : ℕ} (hL : 0 < L) (s : Fin (L + 1) → ℝ) (hs : IsLevelVector s)
    (z : (Fin L → ℝ) → ℝ) (hz : z ∈ Zs s)
    (D : Measure ℝ) (hD : IsDemand D) (hDpos : 0 < D (Set.Ioi 0))
    (x : Fin L → ℝ) (hx : ∀ i, 0 ≤ x i) :
    haveI := hD.isProb
    ∀ᵐ ds ∂(Measure.infinitePi (fun _ : ℕ => D)),
      ∃ T : ℕ, ∀ t, T ≤ t → traj z x ds t ∈ Xs s := by
  haveI := hD.isProb
  set μ : Measure (ℕ → ℝ) := Measure.infinitePi (fun _ : ℕ => D) with hμ
  -- nonnegativity of the demands
  have hnn : ∀ᵐ ds ∂μ, ∀ t, 0 ≤ ds t := by
    rw [ae_all_iff]
    intro t
    rw [ae_iff]
    have h1 : {ds : ℕ → ℝ | ¬ 0 ≤ ds t} = (fun ds : ℕ → ℝ => ds t) ⁻¹' (Set.Iio 0) := by
      ext ds; simp
    rw [h1]
    have := (measurePreserving_eval_infinitePi (fun _ : ℕ => D) t).measure_preimage
      (measurableSet_Iio (a := (0 : ℝ))).nullMeasurableSet
    rw [show (Set.Iio (0:ℝ)) = Set.Iio 0 from rfl] at this
    simpa [hμ, hD.nonneg] using this
  -- divergence of the cumulative demand
  have hdiv : ∀ᵐ ds ∂μ, Tendsto (fun n => ∑ t ∈ Finset.range n, ds t) atTop atTop := by
    set g : ℝ → ℝ := fun y => min (max y 0) 1 with hg
    have hgm : Measurable g := (measurable_id.max measurable_const).min measurable_const
    have hg0 : ∀ y, 0 ≤ g y := fun y => le_min (le_max_right _ _) zero_le_one
    have hg1 : ∀ y, g y ≤ 1 := fun y => min_le_right _ _
    have hgle : ∀ y, 0 ≤ y → g y ≤ y := by
      intro y hy
      simp only [hg, max_eq_left hy]
      exact min_le_left _ _
    have hind : iIndepFun (fun (i : ℕ) (ω : ℕ → ℝ) => g (ω i)) μ :=
      iIndepFun_infinitePi (P := fun _ : ℕ => D) (X := fun _ => g) (fun _ => hgm)
    have hmeas : ∀ i : ℕ, Measurable (fun ω : ℕ → ℝ => g (ω i)) :=
      fun i => hgm.comp (measurable_pi_apply i)
    have hint : Integrable (fun ω : ℕ → ℝ => g (ω 0)) μ := by
      refine Integrable.of_bound (hmeas 0).aestronglyMeasurable 1 ?_
      refine Filter.Eventually.of_forall (fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hg0 _)]
      exact hg1 _
    have hindep : Pairwise (Function.onFun (fun f h => f ⟂ᵢ[μ] h) (fun (n : ℕ) (ω : ℕ → ℝ) => g (ω n))) :=
      fun i j hij => hind.indepFun hij
    have hmap : ∀ i : ℕ, μ.map (fun ω : ℕ → ℝ => g (ω i)) = D.map g := by
      intro i
      have : (fun ω : ℕ → ℝ => g (ω i)) = g ∘ (fun ω : ℕ → ℝ => ω i) := rfl
      rw [this, ← Measure.map_map hgm (measurable_pi_apply i), hμ, Measure.infinitePi_map_eval]
    have hident : ∀ i, IdentDistrib (fun ω : ℕ → ℝ => g (ω i)) (fun ω : ℕ → ℝ => g (ω 0)) μ μ :=
      fun i => ⟨(hmeas i).aemeasurable, (hmeas 0).aemeasurable, by rw [hmap i, hmap 0]⟩
    have hlaw := strong_law_ae (μ := μ) (fun (n : ℕ) (ω : ℕ → ℝ) => g (ω n)) hint hindep hident
    have hE : 0 < ∫ ω, g (ω 0) ∂μ := by
      have h1 : ∫ ω, g (ω 0) ∂μ = ∫ y, g y ∂D := by
        rw [← integral_map (φ := fun ω : ℕ → ℝ => ω 0) (measurable_pi_apply 0).aemeasurable
          hgm.aestronglyMeasurable, hμ, Measure.infinitePi_map_eval]
      rw [h1]
      have hgi : Integrable g D :=
        Integrable.of_bound hgm.aestronglyMeasurable 1
          (Filter.Eventually.of_forall (fun y => by
            rw [Real.norm_eq_abs, abs_of_nonneg (hg0 _)]; exact hg1 _))
      rw [integral_pos_iff_support_of_nonneg hg0 hgi]
      have hsupp : Function.support g = Set.Ioi 0 := by
        ext y
        simp only [Function.mem_support, Set.mem_Ioi]
        by_cases hy : 0 < y
        · have : 0 < g y := lt_min (lt_of_lt_of_le hy (le_max_left _ _)) one_pos
          simp [this.ne', hy]
        · have : g y = 0 := by
            simp only [hg, max_eq_right (not_lt.1 hy)]
            simp
          simp [this, hy]
      rw [hsupp]
      exact hDpos
    set m := ∫ ω, g (ω 0) ∂μ with hm
    filter_upwards [hlaw, hnn] with ds hds' hds0
    have hev := (tendsto_order.1 hds').1 (m / 2) (by linarith)
    have hlin : Tendsto (fun n : ℕ => (n : ℝ) * (m / 2)) atTop atTop :=
      Tendsto.atTop_mul_const (by positivity) tendsto_natCast_atTop_atTop
    refine tendsto_atTop_mono' atTop ?_ hlin
    filter_upwards [hev, eventually_gt_atTop 0] with n hn hn0
    have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
    have h1 : m / 2 < (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, g (ds i) := by
      simpa [smul_eq_mul] using hn
    have h2 : (n : ℝ) * (m / 2) ≤ ∑ i ∈ Finset.range n, g (ds i) := by
      have := mul_lt_mul_of_pos_left h1 hn0'
      rw [← mul_assoc, mul_inv_cancel₀ hn0'.ne', one_mul] at this
      exact this.le
    refine h2.trans ?_
    exact Finset.sum_le_sum (fun i _ => hgle _ (hds0 i))
  filter_upwards [hnn, hdiv] with ds hds hdv
  obtain ⟨t0, ht0⟩ := LSS_reach hL s hs z hz x hx ds hds hdv
  refine ⟨t0, ?_⟩
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact ht0
  | succ t _ ih =>
    exact LSS_inv hL s hs z hz _ ih (ds t) (hds t)
