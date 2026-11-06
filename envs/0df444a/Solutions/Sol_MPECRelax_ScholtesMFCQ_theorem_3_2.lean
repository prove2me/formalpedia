-- Prove2me | solution 1 for MPECRelax.ScholtesMFCQ.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T19:28:16.843224+00:00
-- url     : https://prove2.me/submissions/c17cc6d5-851c-41ab-97f4-b3873a2e37dd

import Mathlib
import Definitions.Def_MPECRelax_ScholtesMFCQ_Basic
import Theorems.Thm_MPECRelax_ScholtesMFCQ_eq_6

open Filter Topology
open scoped RealInnerProductSpace

namespace ScholtesMFCQAux

abbrev E (n : ℕ) := MPECRelax.ScholtesConv.E n

lemma key {n : ℕ} {K : Type} [Fintype K] [DecidableEq K] (u : K → E n → E n) (xs : E n)
    (hu : ∀ k, ContinuousAt (u k) xs) (hli : LinearIndependent ℝ (fun k => u k xs)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x in 𝓝 xs, ∀ s : K → ℝ, ∃ w : E n,
      (∀ k, ⟪u k x, w⟫ = s k) ∧ ‖w‖ ≤ C * ‖s‖ := by
  let L : E n → (E n →L[ℝ] (K → ℝ)) := fun x =>
    ContinuousLinearMap.pi (fun k => innerSL ℝ (u k x))
  have hL : ∀ x w, L x w = fun k => ⟪u k x, w⟫ := fun x w => rfl
  -- surjectivity at xs
  have hsurj : (L xs).range = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    apply hf0
    have hc : ∑ k, f (Pi.single k 1) • u k xs = 0 := by
      have : ∀ w : E n, ⟪∑ k, f (Pi.single k 1) • u k xs, w⟫ = 0 := by
        intro w
        have h1 : f (L xs w) = 0 := hf ⟨w, rfl⟩
        have h2 : L xs w = ∑ k, (⟪u k xs, w⟫) • (Pi.single k (1:ℝ) : K → ℝ) := by
          ext j; simp [hL, Finset.sum_apply, Pi.single_apply]
        rw [h2, map_sum] at h1
        simp only [map_smul, smul_eq_mul] at h1
        rw [sum_inner]
        simp only [real_inner_smul_left]
        rw [← h1]; apply Finset.sum_congr rfl; intro k _; ring
      exact inner_self_eq_zero.1 (this _)
    have hz := Fintype.linearIndependent_iff.1 hli _ hc
    apply LinearMap.ext; intro y
    have : y = ∑ k, y k • (Pi.single k (1:ℝ) : K → ℝ) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    rw [this, map_sum]; simp [hz]
  obtain ⟨R0, hR0⟩ := (L xs).exists_rightInverse_of_surjective hsurj
  let M : E n → ((K → ℝ) →L[ℝ] (K → ℝ)) := fun x => (L x).comp R0
  have hMxs : M xs = 1 := hR0
  -- continuity of M at xs
  have hMc : ContinuousAt M xs := by
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    have hb : ∀ x, ‖M x - M xs‖ ≤ (∑ k, ‖u k x - u k xs‖) * ‖R0‖ := by
      intro x
      have : M x - M xs = (L x - L xs).comp R0 := by
        simp [M, ContinuousLinearMap.sub_comp]
      rw [this]
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      gcongr
      refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg (fun k _ => norm_nonneg _)) ?_
      intro w
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 ?_
      intro k
      have e1 : (L x - L xs) w k = ⟪u k x - u k xs, w⟫ := by
        simp [hL, inner_sub_left]
      rw [e1, Real.norm_eq_abs]
      refine (abs_real_inner_le_norm _ _).trans ?_
      gcongr
      exact Finset.single_le_sum (f := fun k => ‖u k x - u k xs‖) (fun k _ => norm_nonneg _)
        (Finset.mem_univ k)
    have ht : Tendsto (fun x => (∑ k, ‖u k x - u k xs‖) * ‖R0‖) (𝓝 xs) (𝓝 0) := by
      have : Tendsto (fun x => (∑ k, ‖u k x - u k xs‖)) (𝓝 xs) (𝓝 (∑ k : K, (0:ℝ))) := by
        apply tendsto_finsetSum
        intro k _
        exact tendsto_iff_norm_sub_tendsto_zero.1 (hu k)
      simpa using this.mul_const ‖R0‖
    exact squeeze_zero (fun _ => norm_nonneg _) hb ht
  -- inverse
  have hinvc : ContinuousAt (fun x => Ring.inverse (M x)) xs := by
    have h1 := NormedRing.inverse_continuousAt (1 : ((K → ℝ) →L[ℝ] (K → ℝ))ˣ)
    rw [Units.val_one, ← hMxs] at h1
    exact h1.comp hMc
  have hev1 : ∀ᶠ x in 𝓝 xs, IsUnit (M x) := by
    have : {y : (K → ℝ) →L[ℝ] (K → ℝ) | IsUnit y} ∈ 𝓝 (M xs) := by
      rw [hMxs]; exact Units.isOpen.mem_nhds isUnit_one
    exact hMc this
  have hev2 : ∀ᶠ x in 𝓝 xs, ‖Ring.inverse (M x)‖ < 2 := by
    have := hinvc (Metric.ball_mem_nhds _ one_pos)
    filter_upwards [this] with x hx
    rw [Set.mem_preimage, Metric.mem_ball, dist_eq_norm, hMxs, Ring.inverse_one] at hx
    have h1 : ‖(1 : (K → ℝ) →L[ℝ] (K → ℝ))‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    calc ‖Ring.inverse (M x)‖ = ‖(Ring.inverse (M x) - 1) + 1‖ := by simp
      _ ≤ ‖Ring.inverse (M x) - 1‖ + ‖(1 : (K → ℝ) →L[ℝ] (K → ℝ))‖ := norm_add_le _ _
      _ < 2 := by linarith
  refine ⟨2 * ‖R0‖, by positivity, ?_⟩
  filter_upwards [hev1, hev2] with x hx1 hx2 s
  refine ⟨R0 (Ring.inverse (M x) s), ?_, ?_⟩
  · intro k
    have : M x * Ring.inverse (M x) = 1 := Ring.mul_inverse_cancel _ hx1
    have h2 : L x (R0 (Ring.inverse (M x) s)) = s := by
      have := congrArg (fun T => T s) this
      simpa [M] using this
    have h3 := congrFun h2 k
    rw [hL] at h3
    exact h3
  · calc ‖R0 (Ring.inverse (M x) s)‖ ≤ ‖R0‖ * ‖Ring.inverse (M x) s‖ := R0.le_opNorm _
      _ ≤ ‖R0‖ * (‖Ring.inverse (M x)‖ * ‖s‖) := by gcongr; exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖R0‖ * (2 * ‖s‖) := by gcongr
      _ = 2 * ‖R0‖ * ‖s‖ := by ring


lemma grad_cont {n : ℕ} {f : E n → ℝ} (hf : ContDiff ℝ 1 f) : Continuous (gradient f) :=
  (InnerProductSpace.toDual ℝ (E n)).symm.continuous.comp (hf.continuous_fderiv one_ne_zero)

lemma ig {n : ℕ} (f : E n → ℝ) (x d : E n) : ⟪gradient f x, d⟫ = fderiv ℝ f x d :=
  InnerProductSpace.toDual_symm_apply

lemma ev_abs_lt {n : ℕ} {f : E n → ℝ} {xs : E n} (hf : ContinuousAt f xs) (h0 : f xs = 0)
    {δ : ℝ} (hδ : 0 < δ) : ∀ᶠ x in 𝓝 xs, |f x| < δ := by
  have := hf (Metric.ball_mem_nhds (f xs) hδ)
  filter_upwards [this] with x hx
  simpa [Metric.mem_ball, Real.dist_eq, h0] using hx

end ScholtesMFCQAux

open MPECRelax.ScholtesMFCQ MPECRelax.ScholtesMFCQ.MPEC ScholtesMFCQAux

theorem solution {n m p l : ℕ} (P : MPEC n m p l) (hP : P.IsC1)
    (xs : MPECRelax.ScholtesConv.E n) (hfeas : P.Feasible xs) (hCQ : P.MPEC_MFCQ xs) :
    ∃ N ∈ 𝓝 xs, ∃ tbar : ℝ, 0 < tbar ∧
      ∀ t : ℝ, 0 < t → ∀ x ∈ N, (P.RS t).Feasible x → (P.RS t).IsMFCQ x := by
  classical
  obtain ⟨hf1, hg1, hh1, hG1, hH1⟩ := hP
  obtain ⟨hli, d0, hd0g, hd0h⟩ := hCQ
  set T := P.TNLP xs with hT
  let u : _ → E n → E n := fun k x => gradient (T.h k) x
  have hTc : ∀ k, ContDiff ℝ 1 (T.h k) := by
    intro k
    rcases k with j | i | i
    · exact hh1 j
    · exact hG1 i
    · exact hH1 i
  have huc : ∀ k, Continuous (u k) := fun k => grad_cont (hTc k)
  -- Step 1: the strict inequalities for the active `g_i` survive small perturbations
  have hstep1 : ∀ᶠ z in 𝓝 (xs, (0 : E n)), ∀ i, P.g i xs = 0 →
      ⟪gradient (P.g i) z.1, d0 + z.2⟫ < 0 := by
    refine Filter.eventually_all.2 (fun i => ?_)
    by_cases hi : P.g i xs = 0
    · have hcont : Continuous (fun z : E n × E n => ⟪gradient (P.g i) z.1, d0 + z.2⟫) :=
        ((grad_cont (hg1 i)).comp continuous_fst).inner (continuous_const.add continuous_snd)
      have h0 : ⟪gradient (P.g i) xs, d0 + 0⟫ < 0 := by
        rw [add_zero]
        exact hd0g (Sum.inl i) hi
      filter_upwards [hcont.continuousAt.eventually_lt continuousAt_const h0] with z hz _
      exact hz
    · exact Filter.Eventually.of_forall (fun z h => absurd h hi)
  rw [nhds_prod_eq] at hstep1
  obtain ⟨pa, hpa, pb, hpb, hall⟩ := Filter.eventually_prod_iff.1 hstep1
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1 hpb
  -- Step 2: uniform solvability of the linear equations
  obtain ⟨C, hC0, hC⟩ := key u xs (fun k => (huc k).continuousAt) hli
  set δ : ℝ := ρ / (2 * C + 2) with hδdef
  have hδ : 0 < δ := by positivity
  have h2Cδ : 2 * C * δ < ρ := by
    rw [hδdef, ← mul_div_assoc, div_lt_iff₀ (by positivity)]
    nlinarith
  set D : ℝ := ‖d0‖ + ρ with hD
  -- Step 3: further eventual conditions
  obtain ⟨N6, hN6, h6⟩ := eq_6 P ⟨hf1, hg1, hh1, hG1, hH1⟩ xs hfeas
  have hev_b : ∀ᶠ x in 𝓝 xs, ∀ k, |⟪u k x, d0⟫| < δ := by
    refine Filter.eventually_all.2 (fun k => ?_)
    exact ev_abs_lt (((huc k).inner continuous_const).continuousAt) (hd0h k) hδ
  have hev_c : ∀ᶠ x in 𝓝 xs, ∀ i, P.G i xs = 0 → 0 < P.H i xs →
      P.G i x * (‖gradient (P.H i) x‖ * D) < P.H i x * δ := by
    refine Filter.eventually_all.2 (fun i => ?_)
    by_cases hi : P.G i xs = 0 ∧ 0 < P.H i xs
    · have hc1 : Continuous (fun x => P.G i x * (‖gradient (P.H i) x‖ * D)) :=
        (hG1 i).continuous.mul (((grad_cont (hH1 i)).norm).mul continuous_const)
      have hc2 : Continuous (fun x => P.H i x * δ) := (hH1 i).continuous.mul continuous_const
      have h0 : P.G i xs * (‖gradient (P.H i) xs‖ * D) < P.H i xs * δ := by
        rw [hi.1, zero_mul]; exact mul_pos hi.2 hδ
      filter_upwards [hc1.continuousAt.eventually_lt hc2.continuousAt h0] with x hx _ _
      exact hx
    · exact Filter.Eventually.of_forall (fun x h1 h2 => absurd ⟨h1, h2⟩ hi)
  have hev_d : ∀ᶠ x in 𝓝 xs, ∀ i, 0 < P.G i xs → P.H i xs = 0 →
      P.H i x * (‖gradient (P.G i) x‖ * D) < P.G i x * δ := by
    refine Filter.eventually_all.2 (fun i => ?_)
    by_cases hi : 0 < P.G i xs ∧ P.H i xs = 0
    · have hc1 : Continuous (fun x => P.H i x * (‖gradient (P.G i) x‖ * D)) :=
        (hH1 i).continuous.mul (((grad_cont (hG1 i)).norm).mul continuous_const)
      have hc2 : Continuous (fun x => P.G i x * δ) := (hG1 i).continuous.mul continuous_const
      have h0 : P.H i xs * (‖gradient (P.G i) xs‖ * D) < P.G i xs * δ := by
        rw [hi.2, zero_mul]; exact mul_pos hi.1 hδ
      filter_upwards [hc1.continuousAt.eventually_lt hc2.continuousAt h0] with x hx _ _
      exact hx
    · exact Filter.Eventually.of_forall (fun x h1 h2 => absurd ⟨h1, h2⟩ hi)
  have hNmem : {x | pa x ∧ (∀ s : _ → ℝ, ∃ w : E n, (∀ k, ⟪u k x, w⟫ = s k) ∧ ‖w‖ ≤ C * ‖s‖) ∧
      (∀ k, |⟪u k x, d0⟫| < δ) ∧
      (∀ i, P.G i xs = 0 → 0 < P.H i xs → P.G i x * (‖gradient (P.H i) x‖ * D) < P.H i x * δ) ∧
      (∀ i, 0 < P.G i xs → P.H i xs = 0 → P.H i x * (‖gradient (P.G i) x‖ * D) < P.G i x * δ)}
        ∩ N6 ∈ 𝓝 xs := by
    refine Filter.inter_mem ?_ hN6
    filter_upwards [hpa, hC, hev_b, hev_c, hev_d] with x h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  refine ⟨_, hNmem, 1, one_pos, ?_⟩
  rintro t ht x ⟨⟨hxa, hxC, hxb, hxc, hxd⟩, hxN6⟩ hxfeas
  obtain ⟨h6g, h6G, h6H, -, -⟩ := h6 t ht x hxN6 hxfeas
  constructor
  · -- linear independence of the equality gradients
    refine Fintype.linearIndependent_iff.2 (fun β hβ => ?_)
    obtain ⟨w, hw, -⟩ := hxC (Sum.elim β (fun _ => 0))
    have hsum : ∑ j, β j * β j = 0 := by
      have h0 : ⟪∑ j, β j • gradient (P.h j) x, w⟫ = 0 := by
        have : (∑ j, β j • gradient ((P.RS t).h j) x) = ∑ j, β j • gradient (P.h j) x := rfl
        rw [← this, hβ, inner_zero_left]
      rw [sum_inner] at h0
      rw [← h0]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [real_inner_smul_left]
      have := hw (Sum.inl j)
      simp only [Sum.elim_inl] at this
      rw [show gradient (P.h j) x = u (Sum.inl j) x from rfl, this]
    intro j
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (β j))).1 hsum j
      (Finset.mem_univ j)
    exact mul_self_eq_zero.1 this
  · -- the MFCQ direction
    let r : (Fin p ⊕ ↥(P.I0p xs ∪ P.I00 xs) ⊕ ↥(P.Ip0 xs ∪ P.I00 xs)) → ℝ :=
      Sum.elim (fun _ => 0)
      (Sum.elim (fun i => if P.H i.1 x * P.G i.1 x = t then -δ else δ)
        (fun i => if P.H i.1 x * P.G i.1 x = t then -δ else δ))
    have hr : ∀ k, |r k| ≤ δ := by
      intro k
      rcases k with j | i | i
      · simp [r, hδ.le]
      · simp only [r, Sum.elim_inr, Sum.elim_inl]; split_ifs <;> simp [abs_of_pos hδ]
      · simp only [r, Sum.elim_inr]; split_ifs <;> simp [abs_of_pos hδ]
    obtain ⟨w, hw, hwn⟩ := hxC (fun k => r k - ⟪u k x, d0⟫)
    have hsn : ‖(fun k => r k - ⟪u k x, d0⟫)‖ ≤ 2 * δ := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 (fun k => ?_)
      rw [Real.norm_eq_abs]
      have := hr k; have := hxb k
      calc |r k - ⟪u k x, d0⟫| ≤ |r k| + |⟪u k x, d0⟫| := abs_sub _ _
        _ ≤ 2 * δ := by linarith
    have hwρ : ‖w‖ < ρ := by
      calc ‖w‖ ≤ C * (2 * δ) := hwn.trans (by gcongr)
        _ < ρ := by linarith
    have hdn : ‖d0 + w‖ ≤ D := by
      calc ‖d0 + w‖ ≤ ‖d0‖ + ‖w‖ := norm_add_le _ _
        _ ≤ D := by rw [hD]; linarith
    have hud : ∀ k, ⟪u k x, d0 + w⟫ = r k := by
      intro k; rw [inner_add_right, hw k]; ring
    have hdG : ∀ i (hi : i ∈ P.I0p xs ∪ P.I00 xs), ⟪gradient (P.G i) x, d0 + w⟫ =
        if P.H i x * P.G i x = t then -δ else δ := fun i hi => hud (Sum.inr (Sum.inl ⟨i, hi⟩))
    have hdH : ∀ i (hi : i ∈ P.Ip0 xs ∪ P.I00 xs), ⟪gradient (P.H i) x, d0 + w⟫ =
        if P.H i x * P.G i x = t then -δ else δ := fun i hi => hud (Sum.inr (Sum.inr ⟨i, hi⟩))
    have hdh : ∀ j, ⟪gradient (P.h j) x, d0 + w⟫ = 0 := fun j => hud (Sum.inl j)
    obtain ⟨hfg, -⟩ := hxfeas
    have hGnn : ∀ i, 0 ≤ P.G i x := fun i => by
      have := hfg (Sum.inr (Sum.inl i)); simp [MPEC.RS] at this; exact this
    have hHnn : ∀ i, 0 ≤ P.H i x := fun i => by
      have := hfg (Sum.inr (Sum.inr (Sum.inl i))); simp [MPEC.RS] at this; exact this
    refine ⟨d0 + w, ?_, fun j => hdh j⟩
    intro k hk
    simp only [MPECRelax.ScholtesConv.NLP.activeSet, Set.mem_ofPred_eq] at hk
    rcases k with i | i | i | i
    · -- g_i
      have hk' : P.g i x = 0 := hk
      have hixs : P.g i xs = 0 := h6g hk'
      have := @hall x hxa w (hball (by simpa [dist_eq_norm] using hwρ)) i hixs
      exact this
    · -- -G_i
      have hk' : P.G i x = 0 := by
        have : -P.G i x = 0 := hk
        linarith
      have hmem : i ∈ P.I0p xs ∪ P.I00 xs := by
        rcases h6G hk' with h | h
        · exact Or.inr h
        · exact Or.inl h
      have hne : ¬ (P.H i x * P.G i x = t) := by rw [hk', mul_zero]; exact ht.ne
      have e1 := hdG i hmem
      rw [if_neg hne] at e1
      show ⟪gradient (fun y => -P.G i y) x, d0 + w⟫ < 0
      rw [ig, fderiv_fun_neg, neg_apply, ← ig, e1]
      linarith
    · -- -H_i
      have hk' : P.H i x = 0 := by
        have : -P.H i x = 0 := hk
        linarith
      have hmem : i ∈ P.Ip0 xs ∪ P.I00 xs := by
        rcases h6H hk' with h | h
        · exact Or.inr h
        · exact Or.inl h
      have hne : ¬ (P.H i x * P.G i x = t) := by rw [hk', zero_mul]; exact ht.ne
      have e1 := hdH i hmem
      rw [if_neg hne] at e1
      show ⟪gradient (fun y => -P.H i y) x, d0 + w⟫ < 0
      rw [ig, fderiv_fun_neg, neg_apply, ← ig, e1]
      linarith
    · -- product constraint
      have hk' : P.G i x * P.H i x = t := by
        have : P.G i x * P.H i x - t = 0 := hk
        linarith
      have hHG : P.H i x * P.G i x = t := by rw [mul_comm]; exact hk'
      have hGp : 0 < P.G i x := by
        rcases (hGnn i).lt_or_eq with h | h
        · exact h
        · rw [← h, zero_mul] at hk'; exact absurd hk' ht.ne
      have hHp : 0 < P.H i x := by
        rcases (hHnn i).lt_or_eq with h | h
        · exact h
        · rw [← h, mul_zero] at hk'; exact absurd hk' ht.ne
      show ⟪gradient (fun y => P.G i y * P.H i y - t) x, d0 + w⟫ < 0
      have hdiffG : DifferentiableAt ℝ (P.G i) x := (hG1 i).differentiable one_ne_zero x
      have hdiffH : DifferentiableAt ℝ (P.H i) x := (hH1 i).differentiable one_ne_zero x
      rw [ig, fderiv_sub_const, fderiv_fun_mul hdiffG hdiffH]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [← ig, ← ig]
      obtain ⟨hxsG, hxsH, hxs0⟩ := hfeas.2.2 i
      rcases hxsG.lt_or_eq with hGs | hGs
      · -- G_i(xs) > 0, so H_i(xs) = 0
        have hHs : P.H i xs = 0 := by
          rcases mul_eq_zero.1 hxs0 with h | h
          · exact absurd h hGs.ne'
          · exact h
        have hmem : i ∈ P.Ip0 xs ∪ P.I00 xs := Or.inl ⟨hGs, hHs⟩
        rw [hdH i hmem, if_pos hHG]
        have hb := hxd i hGs hHs
        have hcs : ⟪gradient (P.G i) x, d0 + w⟫ ≤ ‖gradient (P.G i) x‖ * D :=
          (real_inner_le_norm _ _).trans (by gcongr)
        have : P.H i x * ⟪gradient (P.G i) x, d0 + w⟫ ≤ P.H i x * (‖gradient (P.G i) x‖ * D) :=
          mul_le_mul_of_nonneg_left hcs hHp.le
        nlinarith
      · have hGs' : P.G i xs = 0 := hGs.symm
        rcases hxsH.lt_or_eq with hHs | hHs
        · have hmem : i ∈ P.I0p xs ∪ P.I00 xs := Or.inl ⟨hGs', hHs⟩
          rw [hdG i hmem, if_pos hHG]
          have hb := hxc i hGs' hHs
          have hcs : ⟪gradient (P.H i) x, d0 + w⟫ ≤ ‖gradient (P.H i) x‖ * D :=
            (real_inner_le_norm _ _).trans (by gcongr)
          have : P.G i x * ⟪gradient (P.H i) x, d0 + w⟫ ≤
              P.G i x * (‖gradient (P.H i) x‖ * D) :=
            mul_le_mul_of_nonneg_left hcs hGp.le
          nlinarith
        · have hHs' : P.H i xs = 0 := hHs.symm
          rw [hdG i (Or.inr ⟨hGs', hHs'⟩), hdH i (Or.inr ⟨hGs', hHs'⟩), if_pos hHG]
          nlinarith
