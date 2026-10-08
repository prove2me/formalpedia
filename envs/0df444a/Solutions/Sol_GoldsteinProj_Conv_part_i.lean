-- Prove2me | solution 1 for GoldsteinProj.Conv.part_i
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T01:50:08.158143+00:00
-- url     : https://prove2.me/submissions/66ab9bdf-c8f1-4d5f-8065-50308faa3610

import Mathlib
import Definitions.Def_GoldsteinProj_Conv_Setting

set_option autoImplicit false

open Filter Topology RealInnerProductSpace

namespace GP592

open GoldsteinProj.Conv

/-- Variational inequality of the metric projection onto a convex set. -/
lemma proj_inner_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {C : Set H} (hCv : Convex ℝ C) {P : H → H} (hP : IsProjection C P)
    (z c : H) (hc : c ∈ C) : ⟪z - P z, c - P z⟫ ≤ 0 := by
  have hPz := (hP z).1
  refine (norm_eq_iInf_iff_real_inner_le_zero hCv hPz).1 ?_ c hc
  have : Nonempty C := ⟨⟨P z, hPz⟩⟩
  apply le_antisymm
  · apply le_ciInf
    rintro ⟨w, hw⟩
    exact (hP z).2 w hw
  · have hb : BddBelow (Set.range fun w : C => ‖z - (w : H)‖) :=
      ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
    exact ciInf_le hb ⟨P z, hPz⟩

lemma hasDerivAt_phi {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → ℝ) (x d : H) (t : ℝ) (hf : DifferentiableAt ℝ f (x + t • d)) :
    HasDerivAt (fun s : ℝ => f (x + s • d)) (fderiv ℝ f (x + t • d) d) t := by
  have h1 : HasDerivAt (fun s : ℝ => x + s • d) d t := by
    simpa using ((hasDerivAt_id t).smul_const d).const_add x
  exact hf.hasFDerivAt.comp_hasDerivAt t h1

lemma hasDerivAt_phi' {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → ℝ) (x d : H) (t : ℝ)
    (hf : DifferentiableAt ℝ (fun s : ℝ => fderiv ℝ f ((x + t • d) + s • d) d) 0) :
    HasDerivAt (fun s : ℝ => fderiv ℝ f (x + s • d) d) (d2 f (x + t • d) d) t := by
  have h0 : HasDerivAt (fun s : ℝ => fderiv ℝ f ((x + t • d) + s • d) d)
      (d2 f (x + t • d) d) (t - t) := by
    rw [sub_self]; exact hf.hasDerivAt
  have h2 := h0.comp_sub_const t t
  have e : (fun r : ℝ => fderiv ℝ f ((x + t • d) + (r - t) • d) d)
      = fun s : ℝ => fderiv ℝ f (x + s • d) d := by
    funext r
    rw [sub_smul]; congr 2; abel
  rw [e] at h2
  exact h2

/-- Second-order Taylor upper bound along a segment lying in `Shat`. -/
lemma taylor_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → ℝ) (Shat : Set H) (ρ0 : ℝ) (hD : SecondDerivBound f Shat ρ0)
    (x d : H) (u : ℝ) (hu : 0 ≤ u)
    (hseg : ∀ t ∈ Set.Icc (0:ℝ) u, x + t • d ∈ Shat) :
    ∀ t ∈ Set.Icc (0:ℝ) u, f (x + t • d) ≤ f x + t * fderiv ℝ f x d
        + ‖d‖ ^ 2 / ρ0 * t ^ 2 / 2 := by
  set M := ‖d‖ ^ 2 / ρ0
  set φ : ℝ → ℝ := fun s => f (x + s • d)
  set φ' : ℝ → ℝ := fun s => fderiv ℝ f (x + s • d) d
  have hφ : ∀ t ∈ Set.Icc (0:ℝ) u, HasDerivAt φ (φ' t) t := fun t ht =>
    hasDerivAt_phi f x d t (hD _ (hseg t ht)).1
  have hφ' : ∀ t ∈ Set.Icc (0:ℝ) u, HasDerivAt φ' (d2 f (x + t • d) d) t := fun t ht =>
    hasDerivAt_phi' f x d t ((hD _ (hseg t ht)).2 d).1
  have hbd : ∀ t ∈ Set.Icc (0:ℝ) u, d2 f (x + t • d) d ≤ M := fun t ht =>
    (le_abs_self _).trans ((hD _ (hseg t ht)).2 d).2
  have hint : interior (Set.Icc (0:ℝ) u) ⊆ Set.Icc 0 u := interior_subset
  -- step 1: φ' t ≤ φ' 0 + M t
  have hA : AntitoneOn (fun s => φ' s - M * s) (Set.Icc 0 u) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 u)
      (f' := fun s => d2 f (x + s • d) d - M)
    · intro s hs
      exact ((hφ' s hs).continuousAt.sub (continuousAt_const.mul continuousAt_id))
        |>.continuousWithinAt
    · intro s hs
      exact (((hφ' s (hint hs)).sub ((hasDerivAt_id s).const_mul M)).congr_deriv
        (by simp)).hasDerivWithinAt
    · intro s hs
      have := hbd s (hint hs); linarith
  have h0mem : (0:ℝ) ∈ Set.Icc 0 u := ⟨le_rfl, hu⟩
  have hB : ∀ t ∈ Set.Icc (0:ℝ) u, φ' t ≤ φ' 0 + M * t := by
    intro t ht
    have := hA h0mem ht ht.1
    simp only [mul_zero, sub_zero] at this
    linarith
  -- step 2
  have hC : AntitoneOn (fun s => φ s - φ 0 - s * φ' 0 - M * s ^ 2 / 2) (Set.Icc 0 u) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 u)
      (f' := fun s => φ' s - φ' 0 - M * s)
    · intro s hs
      exact (((hφ s hs).continuousAt.sub continuousAt_const).sub
        (continuousAt_id.mul continuousAt_const)).sub
        ((continuousAt_const.mul (continuousAt_id.pow 2)).div_const 2)
        |>.continuousWithinAt
    · intro s hs
      have h1 := (((hφ s (hint hs)).sub_const (φ 0)).sub
        ((hasDerivAt_id s).mul_const (φ' 0))).sub
        (((hasDerivAt_id s).pow 2).const_mul M |>.div_const 2)
      refine (h1.congr_deriv ?_).hasDerivWithinAt
      simp; ring
    · intro s hs
      have := hB s (hint hs); linarith
  intro t ht
  have := hC h0mem ht ht.1
  simp only [φ, φ', zero_smul, add_zero, zero_mul, sub_self] at this
  have e : (0:ℝ) ^ 2 = 0 := by norm_num
  rw [e, mul_zero, zero_div] at this
  linarith

/-- One step of the method decreases `f`. -/
lemma step_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (hCv : Convex ℝ C) (f : H → ℝ) (hfC : ContinuousOn f C)
    (Shat : Set H) (hShat_open : IsOpen Shat) (ρ0 : ℝ) (hρ0 : 0 < ρ0)
    (hD : SecondDerivBound f Shat ρ0)
    (x y : H) (hx : x ∈ C) (hy : y ∈ C) (hsub : ∀ z ∈ C, f z ≤ f x → z ∈ Shat)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ2 : ρ ≤ 2 * ρ0)
    (hvi : ρ * ⟪gradient f x, y - x⟫ ≤ -‖y - x‖ ^ 2) :
    f y ≤ f x + ⟪gradient f x, y - x⟫ + ‖y - x‖ ^ 2 / ρ0 / 2 := by
  set d := y - x with hd
  set a := ⟪gradient f x, d⟫
  set N := ‖d‖ ^ 2
  have hN : 0 ≤ N := by positivity
  have hfa : fderiv ℝ f x d = a := by
    simp [a]
  -- a ≤ -N/ρ ≤ -N/(2ρ0)
  have ha : a ≤ -(N / (2 * ρ0)) := by
    have h1 : a ≤ -N / ρ := by rw [le_div_iff₀ hρ]; linarith
    have h2 : N / (2 * ρ0) ≤ N / ρ := div_le_div_of_nonneg_left hN hρ hρ2
    rw [neg_div] at h1; linarith
  have key : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → (∀ t ∈ Set.Icc (0:ℝ) u, x + t • d ∈ Shat) →
      ∀ t ∈ Set.Icc (0:ℝ) u, f (x + t • d) ≤ f x + t * a + N / ρ0 * t ^ 2 / 2 := by
    intro u hu _ hseg t ht
    have := taylor_le f Shat ρ0 hD x d u hu hseg t ht
    rw [hfa] at this; exact this
  have key2 : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → f x + t * a + N / ρ0 * t ^ 2 / 2 ≤ f x := by
    intro t ht0 ht1
    have e : N / ρ0 * t ^ 2 / 2 = t * (t * (N / (2 * ρ0))) := by field_simp
    rw [e]
    have hq : 0 ≤ N / (2 * ρ0) := by positivity
    have : t * (N / (2 * ρ0)) ≤ N / (2 * ρ0) := by nlinarith
    nlinarith
  have hcont : ContinuousOn (fun t : ℝ => f (x + t • d)) (Set.Icc 0 1) := by
    refine hfC.comp (by fun_prop) ?_
    intro t ht
    exact hCv.add_smul_sub_mem hx hy ht
  set U : Set ℝ := {t | x + t • d ∈ Shat}
  have hUo : IsOpen U := hShat_open.preimage (by fun_prop)
  have hall : Set.Icc (0:ℝ) 1 ⊆ U := by
    by_contra hne
    rw [Set.not_subset] at hne
    set B := Set.Icc (0:ℝ) 1 ∩ Uᶜ
    have hBne : B.Nonempty := by
      obtain ⟨t, ht, htU⟩ := hne; exact ⟨t, ht, htU⟩
    have hBc : IsClosed B := isClosed_Icc.inter hUo.isClosed_compl
    have hBb : BddBelow B := ⟨0, fun t ht => ht.1.1⟩
    set u0 := sInf B
    have hu0 : u0 ∈ B := hBc.csInf_mem hBne hBb
    have hbelow : ∀ t ∈ Set.Ico (0:ℝ) u0, t ∈ U := by
      intro t ht
      by_contra htU
      have : u0 ≤ t := csInf_le hBb ⟨⟨ht.1, ht.2.le.trans hu0.1.2⟩, htU⟩
      exact absurd ht.2 (not_lt.2 this)
    have hle : ∀ t ∈ Set.Ico (0:ℝ) u0, f (x + t • d) ≤ f x := by
      intro t ht
      have h1 := key t ht.1 (ht.2.le.trans hu0.1.2)
        (fun s hs => hbelow s ⟨hs.1, hs.2.trans_lt ht.2⟩) t ⟨ht.1, le_rfl⟩
      exact h1.trans (key2 t ht.1 (ht.2.le.trans hu0.1.2))
    have hfu0 : f (x + u0 • d) ≤ f x := by
      rcases eq_or_lt_of_le hu0.1.1 with h | h
      · rw [← h]; simp
      · have hcl : u0 ∈ closure (Set.Ico (0:ℝ) u0) := by
          rw [closure_Ico h.ne]; exact ⟨h.le, le_rfl⟩
        have hcw : ContinuousWithinAt (fun t : ℝ => f (x + t • d)) (Set.Ico 0 u0) u0 :=
          (hcont u0 hu0.1).mono (fun s hs => ⟨hs.1, hs.2.le.trans hu0.1.2⟩)
        exact ContinuousWithinAt.closure_le hcl hcw continuousWithinAt_const hle
    have hmemC : x + u0 • d ∈ C := hCv.add_smul_sub_mem hx hy hu0.1
    exact hu0.2 (hsub _ hmemC hfu0)
  have h1 := key 1 zero_le_one le_rfl (fun t ht => hall ht) 1 ⟨zero_le_one, le_rfl⟩
  have e1 : x + (1:ℝ) • d = y := by simp [d]
  rw [e1] at h1
  have : f x + 1 * a + N / ρ0 * 1 ^ 2 / 2 = f x + a + N / ρ0 / 2 := by ring
  linarith

end GP592

open Filter Topology RealInnerProductSpace GoldsteinProj.Conv in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (hCc : IsClosed C) (hCv : Convex ℝ C) (P : H → H) (hP : IsProjection C P)
    (f : H → ℝ) (hbdd : BddBelow (Set.range f)) (hfC : ContinuousOn f C)
    (x0 : H) (hx0 : x0 ∈ C)
    (Shat : Set H) (hShat_open : IsOpen Shat) (hShat : convexHull ℝ (levelSet f C x0) ⊆ Shat)
    (ρ0 : ℝ) (hρ0 : 0 < ρ0) (hD : SecondDerivBound f Shat ρ0)
    (σ : ℝ) (hσ : 0 < σ) (hσρ0 : σ ≤ ρ0) (ρ : ℕ → ℝ) (x : ℕ → H)
    (hrun : IsGoldsteinRun f P x0 σ ρ0 ρ x) :
    (∀ k, x k ∈ levelSet f C x0) ∧ Tendsto (fun k => x (k + 1) - x k) atTop (𝓝 0) ∧
      ∃ L : ℝ, Antitone (fun k => f (x k)) ∧ Tendsto (fun k => f (x k)) atTop (𝓝 L) := by
  obtain ⟨h0, hρ, hstep⟩ := hrun
  have hS : levelSet f C x0 ⊆ Shat := (subset_convexHull ℝ _).trans hShat
  set c : ℝ := 1 / (2 * ρ0 - σ) - 1 / (2 * ρ0) with hc_def
  have hpos : 0 < 2 * ρ0 - σ := by linarith
  have hc : 0 < c := by
    have : 1 / (2 * ρ0) < 1 / (2 * ρ0 - σ) := one_div_lt_one_div_of_lt hpos (by linarith)
    linarith
  have step : ∀ k, x k ∈ levelSet f C x0 →
      x (k + 1) ∈ C ∧ f (x (k + 1)) ≤ f (x k) - c * ‖x (k + 1) - x k‖ ^ 2 := by
    intro k hk
    have hρk : 0 < ρ k := lt_of_lt_of_le hσ (hρ k).1
    set g := gradient f (x k)
    set y := x (k + 1) with hy_def
    have hyP : y = P (x k - ρ k • g) := hstep k
    have hyC : y ∈ C := by rw [hyP]; exact (hP _).1
    have hvi0 := GP592.proj_inner_le hCv hP (x k - ρ k • g) (x k) hk.1
    rw [← hyP] at hvi0
    have e1 : x k - ρ k • g - y = -((y - x k) + ρ k • g) := by abel
    have e2 : x k - y = -(y - x k) := by abel
    rw [e1, e2, inner_neg_neg, inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq] at hvi0
    have hcomm : ⟪y - x k, g⟫ = ⟪g, y - x k⟫ := real_inner_comm _ _
    simp only [RCLike.conj_to_real] at hvi0
    have hvi : ρ k * ⟪g, y - x k⟫ ≤ -‖y - x k‖ ^ 2 := by linarith
    have hsub : ∀ z ∈ C, f z ≤ f (x k) → z ∈ Shat := fun z hz hfz =>
      hS ⟨hz, hfz.trans hk.2⟩
    have hmain := GP592.step_le C hCv f hfC Shat hShat_open ρ0 hρ0 hD (x k) y hk.1 hyC hsub
      (ρ k) hρk (by linarith [(hρ k).2]) hvi
    refine ⟨hyC, ?_⟩
    set a := ⟪g, y - x k⟫
    set N := ‖y - x k‖ ^ 2
    have hN : 0 ≤ N := by positivity
    have h1 : a ≤ -N / ρ k := by rw [le_div_iff₀ hρk]; linarith
    have h2 : N / (2 * ρ0 - σ) ≤ N / ρ k := div_le_div_of_nonneg_left hN hρk (hρ k).2
    have h3 : c * N = N / (2 * ρ0 - σ) - N / ρ0 / 2 := by
      rw [hc_def]; field_simp
    rw [neg_div] at h1
    linarith
  have hmem : ∀ k, x k ∈ levelSet f C x0 := by
    intro k
    induction k with
    | zero => rw [h0]; exact ⟨hx0, le_rfl⟩
    | succ k ih =>
      obtain ⟨h1, h2⟩ := step k ih
      have : 0 ≤ c * ‖x (k + 1) - x k‖ ^ 2 := by positivity
      exact ⟨h1, by linarith [ih.2]⟩
  have hdec : ∀ k, f (x (k + 1)) ≤ f (x k) - c * ‖x (k + 1) - x k‖ ^ 2 :=
    fun k => (step k (hmem k)).2
  have hanti : Antitone (fun k => f (x k)) := by
    apply antitone_nat_of_succ_le
    intro k
    have : 0 ≤ c * ‖x (k + 1) - x k‖ ^ 2 := by positivity
    linarith [hdec k]
  have hbb : BddBelow (Set.range (fun k => f (x k))) := by
    obtain ⟨m, hm⟩ := hbdd
    exact ⟨m, by rintro _ ⟨k, rfl⟩; exact hm ⟨x k, rfl⟩⟩
  have hL := tendsto_atTop_ciInf hanti hbb
  refine ⟨hmem, ?_, _, hanti, hL⟩
  have hdiff : Tendsto (fun k => (f (x k) - f (x (k + 1))) / c) atTop (𝓝 0) := by
    have := (hL.sub (hL.comp (tendsto_add_atTop_nat 1))).div_const c
    simpa using this
  have hsq : Tendsto (fun k => ‖x (k + 1) - x k‖ ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero (fun k => by positivity) (fun k => ?_) hdiff
    rw [le_div_iff₀ hc]
    linarith [hdec k]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have := hsq.sqrt
  simpa [Real.sqrt_sq (norm_nonneg _)] using this
