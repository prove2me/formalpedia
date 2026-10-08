-- Prove2me | solution 1 for GoldsteinProj.Conv.goldstein_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T00:22:48.985692+00:00
-- url     : https://prove2.me/submissions/fb455fbf-ffd8-4475-93f2-e0cbdb5316d0

import Mathlib
import Definitions.Def_GoldsteinProj_Conv_Setting

set_option autoImplicit false

open Filter Topology RealInnerProductSpace

namespace GPf272

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

theorem part_i' {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
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
    have hvi0 := proj_inner_le hCv hP (x k - ρ k • g) (x k) hk.1
    rw [← hyP] at hvi0
    have e1 : x k - ρ k • g - y = -((y - x k) + ρ k • g) := by abel
    have e2 : x k - y = -(y - x k) := by abel
    rw [e1, e2, inner_neg_neg, inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq] at hvi0
    have hcomm : ⟪y - x k, g⟫ = ⟪g, y - x k⟫ := real_inner_comm _ _
    simp only [RCLike.conj_to_real] at hvi0
    have hvi : ρ k * ⟪g, y - x k⟫ ≤ -‖y - x k‖ ^ 2 := by linarith
    have hsub : ∀ z ∈ C, f z ≤ f (x k) → z ∈ Shat := fun z hz hfz =>
      hS ⟨hz, hfz.trans hk.2⟩
    have hmain := step_le C hCv f hfC Shat hShat_open ρ0 hρ0 hD (x k) y hk.1 hyC hsub
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


/-- A cluster point of a sequence that eventually lies in a closed set lies in that set. -/
lemma cluster_mem {X : Type*} [TopologicalSpace X] {a : X} {u : ℕ → X}
    (h : MapClusterPt a atTop u) {Q : Set X} (hQ : IsClosed Q)
    (hev : ∀ᶠ k in atTop, u k ∈ Q) : a ∈ Q := by
  by_contra ha
  obtain ⟨k, hk1, hk2⟩ := ((h.frequently (hQ.isOpen_compl.mem_nhds ha)).and_eventually hev).exists
  exact hk1 hk2

/-- The projection step as a variational inequality. -/
lemma vi_step {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {C : Set H} (hCv : Convex ℝ C) {P : H → H} (hP : IsProjection C P) (f : H → ℝ)
    (x : ℕ → H) (ρ : ℕ → ℝ) (hstep : ∀ k, x (k + 1) = P (x k - ρ k • gradient f (x k)))
    (k : ℕ) (y : H) (hy : y ∈ C) :
    ⟪x k - x (k + 1), y - x (k + 1)⟫ ≤ ρ k * ⟪gradient f (x k), y - x (k + 1)⟫ := by
  have h := proj_inner_le hCv hP (x k - ρ k • gradient f (x k)) y hy
  rw [← hstep k] at h
  have e : x k - ρ k • gradient f (x k) - x (k + 1)
      = (x k - x (k + 1)) - ρ k • gradient f (x k) := by abel
  rw [e, inner_sub_left, real_inner_smul_left] at h
  linarith

/-- `⟪∇f(x_k), x_{k+1} - x_k⟫ → 0`. -/
lemma gd_tendsto {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (hCv : Convex ℝ C) (P : H → H) (hP : IsProjection C P)
    (f : H → ℝ) (hfC : ContinuousOn f C) (Shat : Set H) (hShat_open : IsOpen Shat)
    (ρ0 : ℝ) (hρ0 : 0 < ρ0) (hD : SecondDerivBound f Shat ρ0) (σ : ℝ) (hσ : 0 < σ)
    (ρ : ℕ → ℝ) (x : ℕ → H) (hρ : ∀ k, σ ≤ ρ k ∧ ρ k ≤ 2 * ρ0 - σ)
    (hstep : ∀ k, x (k + 1) = P (x k - ρ k • gradient f (x k)))
    (hmemC : ∀ k, x k ∈ C) (hsub : ∀ k, ∀ z ∈ C, f z ≤ f (x k) → z ∈ Shat)
    (L : ℝ) (hlim : Tendsto (fun k => f (x k)) atTop (𝓝 L))
    (hdiff : Tendsto (fun k => x (k + 1) - x k) atTop (𝓝 0)) :
    Tendsto (fun k => ⟪gradient f (x k), x (k + 1) - x k⟫) atTop (𝓝 0) := by
  have hvi : ∀ k, ρ k * ⟪gradient f (x k), x (k + 1) - x k⟫ ≤ -‖x (k + 1) - x k‖ ^ 2 := by
    intro k
    have h := vi_step hCv hP f x ρ hstep k (x k) (hmemC k)
    have e1 : x k - x (k + 1) = -(x (k + 1) - x k) := (neg_sub _ _).symm
    rw [e1] at h
    simp only [inner_neg_left, inner_neg_right, neg_neg, real_inner_self_eq_norm_sq] at h
    linarith
  have hup : ∀ k, ⟪gradient f (x k), x (k + 1) - x k⟫ ≤ 0 := by
    intro k
    have h1 := hvi k
    have hρk : 0 < ρ k := lt_of_lt_of_le hσ (hρ k).1
    by_contra hc
    push_neg at hc
    have := mul_pos hρk hc
    nlinarith [sq_nonneg ‖x (k + 1) - x k‖]
  have hlow : ∀ k, f (x (k + 1)) - f (x k) - ‖x (k + 1) - x k‖ ^ 2 / ρ0 / 2
      ≤ ⟪gradient f (x k), x (k + 1) - x k⟫ := by
    intro k
    have hρk : 0 < ρ k := lt_of_lt_of_le hσ (hρ k).1
    have := step_le C hCv f hfC Shat hShat_open ρ0 hρ0 hD (x k) (x (k + 1)) (hmemC k)
      (hmemC (k + 1)) (hsub k) (ρ k) hρk (by linarith [(hρ k).2]) (hvi k)
    linarith
  have hT : Tendsto (fun k => f (x (k + 1)) - f (x k) - ‖x (k + 1) - x k‖ ^ 2 / ρ0 / 2)
      atTop (𝓝 0) := by
    have h1 := (hlim.comp (tendsto_add_atTop_nat 1)).sub hlim
    have h2 := ((hdiff.norm.pow 2).div_const ρ0).div_const 2
    have := h1.sub h2
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hT tendsto_const_nhds hlow hup

/-- Second-order Taylor lower bound along a segment. -/
lemma taylor_ge {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → ℝ) (Shat : Set H) (ρ0 : ℝ) (hD : SecondDerivBound f Shat ρ0)
    (x d : H) (u : ℝ) (hu : 0 ≤ u)
    (hseg : ∀ t ∈ Set.Icc (0:ℝ) u, x + t • d ∈ Shat) (m : ℝ)
    (hm : ∀ t ∈ Set.Icc (0:ℝ) u, m ≤ d2 f (x + t • d) d) :
    ∀ t ∈ Set.Icc (0:ℝ) u, f x + t * fderiv ℝ f x d + m * t ^ 2 / 2 ≤ f (x + t • d) := by
  set φ : ℝ → ℝ := fun s => f (x + s • d)
  set φ' : ℝ → ℝ := fun s => fderiv ℝ f (x + s • d) d
  have hφ : ∀ t ∈ Set.Icc (0:ℝ) u, HasDerivAt φ (φ' t) t := fun t ht =>
    hasDerivAt_phi f x d t (hD _ (hseg t ht)).1
  have hφ' : ∀ t ∈ Set.Icc (0:ℝ) u, HasDerivAt φ' (d2 f (x + t • d) d) t := fun t ht =>
    hasDerivAt_phi' f x d t ((hD _ (hseg t ht)).2 d).1
  have hint : interior (Set.Icc (0:ℝ) u) ⊆ Set.Icc 0 u := interior_subset
  have hA : MonotoneOn (fun s => φ' s - m * s) (Set.Icc 0 u) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 u)
      (f' := fun s => d2 f (x + s • d) d - m)
    · intro s hs
      exact ((hφ' s hs).continuousAt.sub (continuousAt_const.mul continuousAt_id))
        |>.continuousWithinAt
    · intro s hs
      exact (((hφ' s (hint hs)).sub ((hasDerivAt_id s).const_mul m)).congr_deriv
        (by simp)).hasDerivWithinAt
    · intro s hs
      have := hm s (hint hs); linarith
  have h0mem : (0:ℝ) ∈ Set.Icc 0 u := ⟨le_rfl, hu⟩
  have hB : ∀ t ∈ Set.Icc (0:ℝ) u, φ' 0 + m * t ≤ φ' t := by
    intro t ht
    have := hA h0mem ht ht.1
    simp only [mul_zero, sub_zero] at this
    linarith
  have hC : MonotoneOn (fun s => φ s - φ 0 - s * φ' 0 - m * s ^ 2 / 2) (Set.Icc 0 u) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 u)
      (f' := fun s => φ' s - φ' 0 - m * s)
    · intro s hs
      exact (((hφ s hs).continuousAt.sub continuousAt_const).sub
        (continuousAt_id.mul continuousAt_const)).sub
        ((continuousAt_const.mul (continuousAt_id.pow 2)).div_const 2)
        |>.continuousWithinAt
    · intro s hs
      have h1 := (((hφ s (hint hs)).sub_const (φ 0)).sub
        ((hasDerivAt_id s).mul_const (φ' 0))).sub
        (((hasDerivAt_id s).pow 2).const_mul m |>.div_const 2)
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

lemma fderiv_eq_inner {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) (z v : H) : fderiv ℝ f z v = ⟪gradient f z, v⟫ := by
  simp only [gradient]; exact InnerProductSpace.toDual_symm_apply.symm

/-- First-order (strong) convexity inequality on `S`. -/
lemma convex_ineq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (f : H → ℝ) (x0 : H) (Shat : Set H) (ρ0 : ℝ) (hD : SecondDerivBound f Shat ρ0)
    (hSS : levelSet f C x0 ⊆ Shat) (μ : ℝ) (hconv : ConvexityHyp f C x0 μ)
    (a b : H) (ha : a ∈ levelSet f C x0) (hb : b ∈ levelSet f C x0) :
    f a + ⟪gradient f a, b - a⟫ + μ * ‖b - a‖ ^ 2 / 2 ≤ f b := by
  have seg : ∀ t ∈ Set.Icc (0:ℝ) 1, a + t • (b - a) ∈ levelSet f C x0 := fun t ht =>
    hconv.1.add_smul_sub_mem ha hb ht
  have h := taylor_ge f Shat ρ0 hD a (b - a) 1 zero_le_one (fun t ht => hSS (seg t ht))
    (μ * ‖b - a‖ ^ 2) (fun t ht => hconv.2.2 _ (seg t ht) _) 1 ⟨zero_le_one, le_rfl⟩
  have e1 : a + (1:ℝ) • (b - a) = b := by simp
  rw [e1, fderiv_eq_inner] at h
  have : f a + 1 * ⟪gradient f a, b - a⟫ + μ * ‖b - a‖ ^ 2 * 1 ^ 2 / 2
      = f a + ⟪gradient f a, b - a⟫ + μ * ‖b - a‖ ^ 2 / 2 := by ring
  linarith

/-- Midpoint form of strong convexity. -/
lemma mid_ineq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (f : H → ℝ) (x0 : H) (Shat : Set H) (ρ0 : ℝ) (hD : SecondDerivBound f Shat ρ0)
    (hSS : levelSet f C x0 ⊆ Shat) (μ : ℝ) (hconv : ConvexityHyp f C x0 μ)
    (a b : H) (ha : a ∈ levelSet f C x0) (hb : b ∈ levelSet f C x0) :
    a + (1/2:ℝ) • (b - a) ∈ levelSet f C x0 ∧
      2 * f (a + (1/2:ℝ) • (b - a)) + μ * ‖b - a‖ ^ 2 / 4 ≤ f a + f b := by
  set m := a + (1/2:ℝ) • (b - a) with hm_def
  have hm : m ∈ levelSet f C x0 :=
    hconv.1.add_smul_sub_mem ha hb ⟨by norm_num, by norm_num⟩
  have h1 := convex_ineq C f x0 Shat ρ0 hD hSS μ hconv m a hm ha
  have h2 := convex_ineq C f x0 Shat ρ0 hD hSS μ hconv m b hm hb
  have e1 : a - m = -((1/2:ℝ) • (b - a)) := by rw [hm_def]; abel
  have e2 : b - m = (1/2:ℝ) • (b - a) := by rw [hm_def]; module
  rw [e1, inner_neg_right, norm_neg] at h1
  rw [e2] at h2
  have hn : ‖(1/2:ℝ) • (b - a)‖ ^ 2 = ‖b - a‖ ^ 2 / 4 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]; ring
  rw [hn] at h1 h2
  exact ⟨hm, by linarith⟩

/-- (iii), lower-bound half: `L ≤ f y` on `C`. -/
lemma L_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (hCv : Convex ℝ C) (P : H → H) (hP : IsProjection C P)
    (f : H → ℝ) (x0 : H) (Shat : Set H) (ρ0 : ℝ) (hD : SecondDerivBound f Shat ρ0)
    (hSS : levelSet f C x0 ⊆ Shat) (μ : ℝ) (hconv : ConvexityHyp f C x0 μ)
    (σ : ℝ) (hσ : 0 < σ) (ρ : ℕ → ℝ) (x : ℕ → H) (hρ : ∀ k, σ ≤ ρ k)
    (hstep : ∀ k, x (k + 1) = P (x k - ρ k • gradient f (x k)))
    (hmem : ∀ k, x k ∈ levelSet f C x0) (hx00 : x 0 = x0)
    (L : ℝ) (hanti : Antitone (fun k => f (x k))) (hlim : Tendsto (fun k => f (x k)) atTop (𝓝 L))
    (hgd : Tendsto (fun k => ⟪gradient f (x k), x (k + 1) - x k⟫) atTop (𝓝 0)) :
    ∀ y ∈ C, L ≤ f y := by
  intro y hy
  by_contra hlt
  push_neg at hlt
  have hLk : ∀ k, L ≤ f (x k) := hanti.le_of_tendsto hlim
  have hyS : y ∈ levelSet f C x0 := ⟨hy, by have := hLk 0; rw [hx00] at this; linarith⟩
  set ε := L - f y with hε
  have hεpos : 0 < ε := by linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (hgd.eventually (Ioi_mem_nhds (show -(ε / 2) < (0:ℝ) by linarith)))
  set a : ℕ → ℝ := fun k => ‖y - x k‖ ^ 2 with ha_def
  have hdec : ∀ k, N ≤ k → a (k + 1) ≤ a k - σ * ε := by
    intro k hk
    have h1 := convex_ineq C f x0 Shat ρ0 hD hSS μ hconv (x k) y (hmem k) hyS
    have hμn : 0 ≤ μ * ‖y - x k‖ ^ 2 / 2 := by have := hconv.2.1; positivity
    have h2 : -(ε / 2) < ⟪gradient f (x k), x (k + 1) - x k⟫ := hN k hk
    have e1 : ⟪gradient f (x k), y - x (k + 1)⟫
        = ⟪gradient f (x k), y - x k⟫ - ⟪gradient f (x k), x (k + 1) - x k⟫ := by
      rw [← inner_sub_right]; congr 1; abel
    have h3 : ⟪gradient f (x k), y - x (k + 1)⟫ ≤ -(ε / 2) := by
      rw [e1]; linarith [hLk k]
    have h4 := vi_step hCv hP f x ρ hstep k y hy
    have hρk := hρ k
    have h45 : ρ k * ⟪gradient f (x k), y - x (k + 1)⟫ ≤ σ * ⟪gradient f (x k), y - x (k + 1)⟫ :=
      by nlinarith
    have h5 : ⟪x k - x (k + 1), y - x (k + 1)⟫ ≤ -(σ * ε / 2) := by nlinarith
    have e2 : y - x k = (y - x (k + 1)) + (x (k + 1) - x k) := by abel
    have e3 : ⟪x k - x (k + 1), y - x (k + 1)⟫ = -⟪y - x (k + 1), x (k + 1) - x k⟫ := by
      rw [real_inner_comm, ← inner_neg_right, neg_sub]
    have h6 : a k = ‖y - x (k + 1)‖ ^ 2 + 2 * ⟪y - x (k + 1), x (k + 1) - x k⟫
        + ‖x (k + 1) - x k‖ ^ 2 := by
      simp only [ha_def]; rw [e2, norm_add_sq_real]
    show ‖y - x (k + 1)‖ ^ 2 ≤ a k - σ * ε
    have := sq_nonneg ‖x (k + 1) - x k‖
    linarith
  have hiter : ∀ n : ℕ, a (N + n) ≤ a N - n * (σ * ε) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := hdec (N + n) (by omega)
      rw [← add_assoc]
      push_cast
      linarith
  have hσε : 0 < σ * ε := mul_pos hσ hεpos
  obtain ⟨n, hn⟩ := exists_nat_gt (a N / (σ * ε))
  have h1 := hiter n
  have h2 : 0 ≤ a (N + n) := by simp only [ha_def]; positivity
  rw [div_lt_iff₀ hσε] at hn
  linarith

/-- From the variational inequality to stationarity. -/
lemma stat_of_vi {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (P : H → H) (hP : IsProjection C P) (f : H → ℝ) (z : H) (hz : z ∈ C)
    (hvi : ∀ y ∈ C, 0 ≤ ⟪gradient f z, y - z⟫) : IsStationary f C P z := by
  refine ⟨hz, fun ρ hρ => ?_⟩
  obtain ⟨hPx, hcl⟩ := hP (z - ρ • gradient f z)
  have hle := hcl z hz
  have hinner : 0 ≤ ⟪gradient f z, P (z - ρ • gradient f z) - z⟫ := hvi _ hPx
  have e1 : z - ρ • gradient f z - P (z - ρ • gradient f z)
      = -(ρ • gradient f z + (P (z - ρ • gradient f z) - z)) := by abel
  have e2 : z - ρ • gradient f z - z = -(ρ • gradient f z) := by abel
  rw [e1, e2, norm_neg, norm_neg] at hle
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hle 2
  rw [norm_add_sq_real, real_inner_smul_left] at hsq
  have hm := mul_nonneg hρ.le hinner
  have h4 : ‖P (z - ρ • gradient f z) - z‖ ^ 2 ≤ 0 := by linarith
  have h5 : ‖P (z - ρ • gradient f z) - z‖ = 0 := by
    nlinarith [norm_nonneg (P (z - ρ • gradient f z) - z)]
  exact sub_eq_zero.1 (norm_eq_zero.1 h5)

/-- Part (ii). -/
lemma part_ii' {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (hCc : IsClosed C) (hCv : Convex ℝ C) (P : H → H) (hP : IsProjection C P)
    (f : H → ℝ) (x0 : H) (σ : ℝ) (hσ : 0 < σ) (ρ : ℕ → ℝ) (x : ℕ → H) (hρ : ∀ k, σ ≤ ρ k)
    (hstep : ∀ k, x (k + 1) = P (x k - ρ k • gradient f (x k)))
    (hmem : ∀ k, x k ∈ levelSet f C x0)
    (hdiff : Tendsto (fun k => x (k + 1) - x k) atTop (𝓝 0))
    (hgd : Tendsto (fun k => ⟪gradient f (x k), x (k + 1) - x k⟫) atTop (𝓝 0))
    (hS : IsCompact (levelSet f C x0)) :
    (∀ z, MapClusterPt z atTop x → (∃ U ∈ 𝓝 z, ContinuousOn (gradient f) U) →
        IsStationary f C P z) ∧
      (∀ z, MapClusterPt z atTop x → (∀ z', MapClusterPt z' atTop x → z' = z) →
        Tendsto x atTop (𝓝 z)) := by
  refine ⟨fun z hz ⟨U, hU, hcont⟩ => ?_, fun z _ huniq =>
    hS.tendsto_nhds_of_unique_mapClusterPt (Eventually.of_forall hmem)
      (fun a _ ha => huniq a ha)⟩
  have hzC : z ∈ C := cluster_mem hz hCc (Eventually.of_forall fun k => (hmem k).1)
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hS.isBounded
  apply stat_of_vi C P hP f z hzC
  intro y hy
  set q : H → ℝ := fun w => ⟪gradient f w, y - w⟫ with hq_def
  have hq : ContinuousAt q z :=
    (hcont.continuousAt hU).inner (continuousAt_const.sub continuousAt_id)
  have hcl := hz.continuousAt_comp hq
  set T : ℕ → ℝ := fun k => ‖x (k + 1) - x k‖ * (‖y‖ + R) / σ with hT_def
  have hT : Tendsto T atTop (𝓝 0) := by
    have := (hdiff.norm.mul_const (‖y‖ + R)).div_const σ
    simpa using this
  have hbound : ∀ k, ⟪gradient f (x k), x (k + 1) - x k⟫ - T k ≤ q (x k) := by
    intro k
    have h4 := vi_step hCv hP f x ρ hstep k y hy
    have hn1 : ‖x k - x (k + 1)‖ = ‖x (k + 1) - x k‖ := norm_sub_rev _ _
    have hn2 : ‖y - x (k + 1)‖ ≤ ‖y‖ + R :=
      (norm_sub_le _ _).trans (by linarith [hR _ (hmem (k + 1))])
    have h5 : -(‖x (k + 1) - x k‖ * (‖y‖ + R)) ≤ ⟪x k - x (k + 1), y - x (k + 1)⟫ := by
      have ha := abs_real_inner_le_norm (x k - x (k + 1)) (y - x (k + 1))
      have hb := neg_abs_le ⟪x k - x (k + 1), y - x (k + 1)⟫
      rw [hn1] at ha
      nlinarith [norm_nonneg (x (k + 1) - x k),
        mul_le_mul_of_nonneg_left hn2 (norm_nonneg (x (k + 1) - x k))]
    set X := ⟪gradient f (x k), y - x (k + 1)⟫ with hX
    set A := ‖x (k + 1) - x k‖ * (‖y‖ + R) with hA
    have hρk := hρ k
    have hσX : -A ≤ σ * X := by
      by_cases hX0 : 0 ≤ X
      · have : 0 ≤ A := by
          have : 0 ≤ ‖y‖ + R := le_trans (norm_nonneg _) hn2
          positivity
        nlinarith
      · push_neg at hX0
        nlinarith
    have hXT : -T k ≤ X := by
      have h1 : -X ≤ A / σ := by rw [le_div_iff₀ hσ]; linarith
      have h2 : T k = A / σ := rfl
      rw [h2]; linarith
    have e : q (x k) = X + ⟪gradient f (x k), x (k + 1) - x k⟫ := by
      simp only [hq_def, hX]
      rw [← inner_add_right]; congr 1; abel
    rw [e]; linarith
  by_contra hneg
  push_neg at hneg
  have hqz : q z < 0 := hneg
  set ε := -q z / 2 with hε
  have hεpos : 0 < ε := by linarith
  have hev : ∀ᶠ k in atTop, (q ∘ x) k ∈ Set.Ici (-ε) := by
    have := (hgd.sub hT).eventually (Ioi_mem_nhds (show -ε < (0:ℝ) - 0 by linarith))
    filter_upwards [this] with k hk
    simp only [Function.comp, Set.mem_Ici]
    have := hbound k
    have hk' : -ε < ⟪gradient f (x k), x (k + 1) - x k⟫ - T k := hk
    linarith
  have := cluster_mem hcl isClosed_Ici hev
  simp only [Set.mem_Ici] at this
  linarith

/-- Part (iv). -/
lemma part_iv' {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (hCc : IsClosed C) (f : H → ℝ) (hfC : ContinuousOn f C) (x0 : H)
    (Shat : Set H) (ρ0 : ℝ) (hD : SecondDerivBound f Shat ρ0)
    (hSS : levelSet f C x0 ⊆ Shat) (μ : ℝ) (hconv : ConvexityHyp f C x0 μ)
    (x : ℕ → H) (hmem : ∀ k, x k ∈ levelSet f C x0)
    (L : ℝ) (hlim : Tendsto (fun k => f (x k)) atTop (𝓝 L)) (hLle : ∀ y ∈ C, L ≤ f y)
    (z : H) (hz : IsWeakClusterPt x z) : z ∈ C ∧ ∀ y ∈ C, f z ≤ f y := by
  have hSc : IsClosed (levelSet f C x0) := by
    have : levelSet f C x0 = C ∩ f ⁻¹' Set.Iic (f x0) := by ext; simp [levelSet]
    rw [this]; exact hfC.preimage_isClosed_of_isClosed hCc isClosed_Iic
  set W := toWeakSpace ℝ H with hW
  have hWc : IsClosed (W '' levelSet f C x0) := by
    have h := hconv.1.toWeakSpace_closure ℝ
    rw [hSc.closure_eq] at h
    rw [h]; exact isClosed_closure
  have hz' : MapClusterPt (W z) atTop (fun k => W (x k)) := hz
  have hzS : z ∈ levelSet f C x0 := by
    have hin : W z ∈ W '' levelSet f C x0 :=
      cluster_mem hz' hWc (Eventually.of_forall fun k => ⟨x k, hmem k, rfl⟩)
    obtain ⟨z', hz'', e⟩ := hin
    rwa [W.injective e] at hz''
  refine ⟨hzS.1, fun y hy => ?_⟩
  suffices h : f z ≤ L by linarith [hLle y hy]
  by_contra hlt
  push_neg at hlt
  set g := gradient f z with hg
  set ε := f z - L with hε
  have hεpos : 0 < ε := by linarith
  let ψ : WeakSpace ℝ H → ℝ := fun w => (topDualPairing ℝ H).flip w (innerSL ℝ g)
  have hψc : Continuous ψ := WeakBilin.eval_continuous _ _
  have hψ : ∀ v, ψ (W v) = ⟪g, v⟫ := fun v => rfl
  have hcl := hz'.continuousAt_comp hψc.continuousAt
  have hev : ∀ᶠ k in atTop, (ψ ∘ fun k => W (x k)) k ∈ Set.Iic (⟪g, z⟫ - ε / 2) := by
    have := hlim.eventually (Iio_mem_nhds (show L < L + ε / 2 by linarith))
    filter_upwards [this] with k hk
    simp only [Function.comp, hψ, Set.mem_Iic]
    have h1 := convex_ineq C f x0 Shat ρ0 hD hSS μ hconv z (x k) hzS (hmem k)
    have hμn : 0 ≤ μ * ‖x k - z‖ ^ 2 / 2 := by have := hconv.2.1; positivity
    rw [inner_sub_right] at h1
    have hk' : f (x k) < L + ε / 2 := hk
    linarith
  have := cluster_mem hcl isClosed_Iic hev
  rw [hψ] at this
  simp only [Set.mem_Iic] at this
  linarith

/-- Part (v). -/
lemma part_v' {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (hCc : IsClosed C) (f : H → ℝ) (hfC : ContinuousOn f C) (x0 : H)
    (Shat : Set H) (ρ0 : ℝ) (hD : SecondDerivBound f Shat ρ0)
    (hSS : levelSet f C x0 ⊆ Shat) (μ : ℝ) (hμ : 0 < μ) (hconv : ConvexityHyp f C x0 μ)
    (x : ℕ → H) (hmem : ∀ k, x k ∈ levelSet f C x0)
    (L : ℝ) (hanti : Antitone (fun k => f (x k))) (hlim : Tendsto (fun k => f (x k)) atTop (𝓝 L))
    (hLle : ∀ y ∈ C, L ≤ f y) :
    ∃ z ∈ levelSet f C x0, f z = L ∧ Tendsto x atTop (𝓝 z) ∧
      (∀ y ∈ C, f z ≤ f y) ∧
      ∀ y ∈ C, (∀ w ∈ C, f y ≤ f w) → y = z := by
  have hLk : ∀ k, L ≤ f (x k) := hanti.le_of_tendsto hlim
  have hmid : ∀ a b, a ∈ levelSet f C x0 → b ∈ levelSet f C x0 →
      μ * ‖b - a‖ ^ 2 / 4 ≤ f a + f b - 2 * L := by
    intro a b ha hb
    obtain ⟨hm, h⟩ := mid_ineq C f x0 Shat ρ0 hD hSS μ hconv a b ha hb
    have := hLle _ hm.1
    linarith
  have hcs : CauchySeq x := by
    refine cauchySeq_of_le_tendsto_0 (fun N => Real.sqrt (8 / μ * (f (x N) - L))) ?_ ?_
    · intro n m N hn hm
      rw [dist_eq_norm]
      have h1 := hmid (x m) (x n) (hmem m) (hmem n)
      have h2 := hanti hn
      have h3 := hanti hm
      have h4 : ‖x n - x m‖ ^ 2 ≤ 8 / μ * (f (x N) - L) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hμ]
        simp only at h2 h3
        nlinarith
      exact (le_abs_self _).trans (Real.abs_le_sqrt h4)
    · have h0 := ((hlim.sub_const L).const_mul (8 / μ)).sqrt
      simpa using h0
  obtain ⟨z, hxz⟩ := cauchySeq_tendsto_of_complete hcs
  have hzC : z ∈ C := hCc.mem_of_tendsto hxz (Eventually.of_forall fun k => (hmem k).1)
  have hfz : Tendsto (fun k => f (x k)) atTop (𝓝 (f z)) :=
    (hfC z hzC).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hxz, Eventually.of_forall fun k => (hmem k).1⟩)
  have hzL : f z = L := tendsto_nhds_unique hfz hlim
  have hzS : z ∈ levelSet f C x0 := ⟨hzC, by linarith [hLk 0, (hmem 0).2]⟩
  refine ⟨z, hzS, hzL, hxz, fun y hy => hzL ▸ hLle y hy, fun y hy hymin => ?_⟩
  have hfy : f y = L := le_antisymm (hzL ▸ hymin z hzC) (hLle y hy)
  have hyS : y ∈ levelSet f C x0 := ⟨hy, by linarith [hzS.2]⟩
  have h := hmid z y hzS hyS
  have hq : ‖y - z‖ ^ 2 ≤ 0 := by
    have : μ * ‖y - z‖ ^ 2 ≤ 0 := by linarith
    nlinarith [sq_nonneg ‖y - z‖]
  have h0 : ‖y - z‖ ^ 2 = 0 := le_antisymm hq (sq_nonneg _)
  exact sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h0))

end GPf272

open Filter Topology RealInnerProductSpace GoldsteinProj.Conv in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (hCc : IsClosed C) (hCv : Convex ℝ C) (P : H → H) (hP : IsProjection C P)
    (f : H → ℝ) (hbdd : BddBelow (Set.range f)) (hfC : ContinuousOn f C)
    (x0 : H) (hx0 : x0 ∈ C)
    (Shat : Set H) (hShat_open : IsOpen Shat) (hShat : convexHull ℝ (levelSet f C x0) ⊆ Shat)
    (ρ0 : ℝ) (hρ0 : 0 < ρ0) (hD : SecondDerivBound f Shat ρ0)
    (σ : ℝ) (hσ : 0 < σ) (hσρ0 : σ ≤ ρ0) (ρ : ℕ → ℝ) (x : ℕ → H)
    (hrun : IsGoldsteinRun f P x0 σ ρ0 ρ x) :
    ∃ L : ℝ,
      -- (i)
      ((∀ k, x k ∈ levelSet f C x0) ∧ Tendsto (fun k => x (k + 1) - x k) atTop (𝓝 0) ∧
        Antitone (fun k => f (x k)) ∧ Tendsto (fun k => f (x k)) atTop (𝓝 L)) ∧
      -- (ii), without its last clause
      (IsCompact (levelSet f C x0) →
        (∀ z, MapClusterPt z atTop x → (∃ U ∈ 𝓝 z, ContinuousOn (gradient f) U) →
            IsStationary f C P z) ∧
        (∀ z, MapClusterPt z atTop x → (∀ z', MapClusterPt z' atTop x → z' = z) →
            Tendsto x atTop (𝓝 z))) ∧
      -- (iii)
      (∀ μ : ℝ, ConvexityHyp f C x0 μ → IsGLB (f '' C) L) ∧
      -- (iv)
      (∀ μ : ℝ, ConvexityHyp f C x0 μ → Bornology.IsBounded (levelSet f C x0) →
        ∀ z, IsWeakClusterPt x z → z ∈ C ∧ ∀ y ∈ C, f z ≤ f y) ∧
      -- (v)
      (∀ μ : ℝ, 0 < μ → ConvexityHyp f C x0 μ →
        (∃ M : ℝ, ∀ y ∈ levelSet f C x0, ‖gradient f y‖ ≤ M) →
        ∃ z ∈ levelSet f C x0, f z = L ∧ Tendsto x atTop (𝓝 z) ∧
          (∀ y ∈ C, f z ≤ f y) ∧
          ∀ y ∈ C, (∀ w ∈ C, f y ≤ f w) → y = z) := by
  obtain ⟨hmem, hdiff, L, hanti, hlim⟩ := GPf272.part_i' C hCc hCv P hP f hbdd hfC x0 hx0 Shat
    hShat_open hShat ρ0 hρ0 hD σ hσ hσρ0 ρ x hrun
  obtain ⟨h0, hρ, hstep⟩ := hrun
  have hSS : levelSet f C x0 ⊆ Shat := (subset_convexHull ℝ _).trans hShat
  have hsub : ∀ k, ∀ z ∈ C, f z ≤ f (x k) → z ∈ Shat := fun k z hz hfz =>
    hSS ⟨hz, hfz.trans (hmem k).2⟩
  have hgd := GPf272.gd_tendsto C hCv P hP f hfC Shat hShat_open ρ0 hρ0 hD σ hσ ρ x hρ hstep
    (fun k => (hmem k).1) hsub L hlim hdiff
  have hLle : ∀ μ, ConvexityHyp f C x0 μ → ∀ y ∈ C, L ≤ f y := fun μ hμ =>
    GPf272.L_le C hCv P hP f x0 Shat ρ0 hD hSS μ hμ σ hσ ρ x (fun k => (hρ k).1) hstep hmem h0
      L hanti hlim hgd
  refine ⟨L, ⟨hmem, hdiff, hanti, hlim⟩, fun hS => GPf272.part_ii' C hCc hCv P hP f x0 σ hσ ρ x
    (fun k => (hρ k).1) hstep hmem hdiff hgd hS, fun μ hμ => ⟨?_, ?_⟩,
    fun μ hμ _ z hz => GPf272.part_iv' C hCc f hfC x0 Shat ρ0 hD hSS μ hμ x hmem L hlim
      (hLle μ hμ) z hz,
    fun μ hμ0 hμ _ => GPf272.part_v' C hCc f hfC x0 Shat ρ0 hD hSS μ hμ0 hμ x hmem L hanti hlim
      (hLle μ hμ)⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact hLle μ hμ y hy
  · intro b hb
    exact ge_of_tendsto' hlim (fun k => hb ⟨x k, (hmem k).1, rfl⟩)
