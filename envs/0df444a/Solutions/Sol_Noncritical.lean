-- Prove2me | solution 1 for Noncritical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:31:28.035132+00:00
-- url     : https://prove2.me/submissions/8d3757e3-c812-4616-9849-002d90d99bc4

import Definitions.Def_PHigherOrder_BootstrapRound
import Definitions.Def_PHigherOrder_CoeffFieldFromScalarBounds
import Definitions.Def_PHigherOrder_DifferentiatedEqn
import Definitions.Def_PHigherOrder_DivFormSchauderInput
import Definitions.Def_PHigherOrder_FluxFieldBootstrapRound
import Definitions.Def_PHigherOrder_GradientFieldOrderShift
import Definitions.Def_PHigherOrder_GradientAnnulus
import Definitions.Def_PHigherOrder_PHarmRestrict
import Definitions.Def_PHigherOrder_PHarmWeakGradClassical
import Definitions.Def_PHigherOrder_SmoothAwayFromCriticalInput
import Definitions.Def_PHigherOrder_Noncritical
import Theorems.Thm_BootstrapRound
import Theorems.Thm_CoeffFieldFromScalarBounds
import Theorems.Thm_DifferentiatedEqn
import Theorems.Thm_FluxFieldBootstrapRound
import Theorems.Thm_GradientAnnulus
import Theorems.Thm_GradientFieldOrderShift
import Theorems.Thm_PHarmRestrict
import Theorems.Thm_PHarmWeakGradClassical


set_option autoImplicit false

theorem _root_.solution (p : ℝ) (hp : 1 < p) (hp2 : p < 2) (k : ℕ)
    (F : FirstOrderEstimateInput p) (hsm : SmoothAwayFromCriticalInput p)
    (hS : DivFormSchauderInput) (δ : ℝ) (hδ : 0 < δ) :
    ∃ τ : ℝ, 0 < τ ∧ τ < 1 / 4 ∧ ∃ Cδ : ℝ, 0 < Cδ ∧
      ∀ (v : Plane → ℝ) (g : Plane → Plane), IsPHarm p (Metric.ball 0 1) v g →
        (∀ x ∈ Metric.ball (0 : Plane) 1, |v x| ≤ 1) → δ < ‖gradient v 0‖ →
        ContDiffOn ℝ ((k + 1 : ℕ) : ℕ∞) v (Metric.ball 0 τ) ∧
          ∀ i ≤ k + 1, ∀ x ∈ Metric.ball (0 : Plane) τ,
            ‖iteratedFDeriv ℝ i v x‖ ≤ Cδ := by
  -- STEP 0:  all constants, fixed before any `v`.
  obtain ⟨κ, hκdef⟩ : ∃ t : ℝ, t = F.kappa := ⟨_, rfl⟩
  have hC0 : 0 < F.C₀ := F.C₀_pos
  -- (0a) the radius `τ`
  obtain ⟨τ, hτ0, hτ4, hGA⟩ := GradientAnnulus p F δ hδ
  refine ⟨τ, hτ0, hτ4, ?_⟩
  -- (0b) the annulus trapping `Dv` away from the origin
  obtain ⟨a, hadef⟩ : ∃ t : ℝ, t = δ / 4 := ⟨_, rfl⟩
  obtain ⟨b, hbdef⟩ : ∃ t : ℝ, t = F.C₀ + 3 * δ / 4 := ⟨_, rfl⟩
  have ha : 0 < a := by rw [hadef]; linarith
  have hab : a ≤ b := by rw [hadef, hbdef]; linarith
  -- (0c) the nested radii
  obtain ⟨rr, hrrdef⟩ : ∃ t : ℕ → ℝ, t = fun i : ℕ => 2 * τ - (i : ℝ) * τ / ((k : ℝ) + 2) :=
    ⟨_, rfl⟩
  have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hrrub : ∀ i : ℕ, rr i ≤ 2 * τ := by
    intro i
    rw [hrrdef]
    have : 0 ≤ (i : ℝ) * τ / ((k : ℝ) + 2) := by positivity
    simp only
    linarith
  have hrrlb : ∀ i ≤ k + 1, τ < rr i := by
    intro i hi
    rw [hrrdef]
    have h1 : (i : ℝ) < (k : ℝ) + 2 := by
      have : (i : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast hi
      linarith
    have h2 : (i : ℝ) * τ / ((k : ℝ) + 2) < τ := by
      rw [div_lt_iff₀ hk2]
      nlinarith
    simp only
    linarith
  have hkne : ((k : ℝ) + 2) ≠ 0 := ne_of_gt hk2
  have hrrdec : ∀ i : ℕ, rr (i + 1) < rr i := by
    intro i
    rw [hrrdef]
    simp only
    push_cast
    have h : (0 : ℝ) < τ / ((k : ℝ) + 2) := by positivity
    have hid : ((i : ℝ) + 1) * τ / ((k : ℝ) + 2)
        = (i : ℝ) * τ / ((k : ℝ) + 2) + τ / ((k : ℝ) + 2) := by
      field_simp
    rw [hid]
    linarith
  have hrr0 : rr 0 = 2 * τ := by rw [hrrdef]; simp
  -- (0d) the constants of the bootstrap.  The recursion is TOTAL on `ℕ`; the content is
  -- claimed only for `i ≤ k`, which is all the induction uses.
  have hstep : ∀ (i : ℕ) (D : ℝ), 0 < D → ∃ D' : ℝ, 0 < D' ∧ 1 ≤ D' ∧
      (i ≤ k → ∀ (v : Plane → ℝ) (V : Set Plane),
        IsOpen V → Convex ℝ V → (∀ ζ ∈ V, a ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ b) →
        (∀ x ∈ Metric.ball (0 : Plane) (rr i), gradient v x ∈ V) →
        ContDiffOn ℝ (⊤ : ℕ∞) v (Metric.ball 0 (rr i)) →
        (∀ x ∈ Metric.ball (0 : Plane) (rr i), |v x| ≤ 1) →
        (∀ x ∈ Metric.ball (0 : Plane) (rr i), ‖gradient v x‖ ≤ F.C₀) →
        (∀ m ≤ i + 1, ∀ x ∈ Metric.ball (0 : Plane) (rr i),
            ‖iteratedFDeriv ℝ m v x‖ ≤ D) →
        (∀ x ∈ Metric.ball (0 : Plane) (rr i), ∀ y ∈ Metric.ball (0 : Plane) (rr i),
            ‖iteratedFDeriv ℝ (i + 1) v x - iteratedFDeriv ℝ (i + 1) v y‖
              ≤ D * ‖x - y‖ ^ κ) →
        (∀ e : Plane, IsLinearDivSol (Metric.ball 0 (rr i))
            (fun x => FluxJacobian p (gradient v x))
            (fun x => inner ℝ (gradient v x) e)
            (fun x => gradient (fun y => inner ℝ (gradient v y) e) x)) →
        (∀ m ≤ i + 2, ∀ x ∈ Metric.ball (0 : Plane) (rr (i + 1)),
            ‖iteratedFDeriv ℝ m v x‖ ≤ D')
          ∧ (∀ x ∈ Metric.ball (0 : Plane) (rr (i + 1)),
              ∀ y ∈ Metric.ball (0 : Plane) (rr (i + 1)),
              ‖iteratedFDeriv ℝ (i + 2) v x - iteratedFDeriv ℝ (i + 2) v y‖
                ≤ D' * ‖x - y‖ ^ κ)) := by
    intro i D hD
    by_cases hik : i ≤ k
    · -- one round on the consecutive radii `rr i` and `rr (i + 1)`
      have hrp : 0 < rr (i + 1) := lt_trans hτ0 (hrrlb (i + 1) (by omega))
      obtain ⟨D', hD'0, hD'1, hbody⟩ :=
        FluxFieldBootstrapRound p hp hp2 F hS κ hκdef i a b ha hab (rr i) (rr (i + 1)) hrp
          (hrrdec i) D hD
      exact ⟨D', hD'0, hD'1, fun _ => hbody⟩
    · exact ⟨1, one_pos, le_refl 1, fun h => absurd h hik⟩
  choose! Nf hNf0 hNf1 hNfP using hstep
  obtain ⟨N, hNdef⟩ : ∃ t : ℕ → ℝ,
      t = fun i : ℕ => Nat.rec (1 + max 1 F.C₀) (fun n acc => Nf n acc) i := ⟨_, rfl⟩
  have hN0 : N 0 = 1 + max 1 F.C₀ := by rw [hNdef]; rfl
  have hNsucc : ∀ i : ℕ, N (i + 1) = Nf i (N i) := by intro i; rw [hNdef]
  have hNpos : ∀ i : ℕ, 0 < N i := by
    intro i
    induction i with
    | zero =>
      rw [hN0]
      have := le_max_left 1 F.C₀
      linarith
    | succ n ih => rw [hNsucc]; exact hNf0 n _ ih
  refine ⟨N k, hNpos k, ?_⟩
  -- STEP 1:  fix `v` and record its structural properties.
  intro v g hph hbd hgrad
  obtain ⟨hvC1, hann⟩ := hGA v g hph hbd hgrad
  have h2τ : (0 : ℝ) < 2 * τ := by linarith
  have hsub1 : Metric.ball (0 : Plane) (2 * τ) ⊆ Metric.ball (0 : Plane) 1 :=
    Metric.ball_subset_ball (by linarith)
  have hsub34 : Metric.ball (0 : Plane) (2 * τ) ⊆ Metric.ball (0 : Plane) (3 / 4) :=
    Metric.ball_subset_ball (by linarith)
  have hzero : (0 : Plane) ∈ Metric.ball (0 : Plane) (2 * τ) := Metric.mem_ball_self h2τ
  -- (1b) smoothness
  have hne : ∀ x ∈ Metric.ball (0 : Plane) (2 * τ), gradient v x ≠ 0 := by
    intro x hx hc
    have := (hann x hx).1
    rw [hc, norm_zero] at this
    linarith
  have hvsm : ContDiffOn ℝ (⊤ : ℕ∞) v (Metric.ball 0 (2 * τ)) :=
    hsm.smooth (Metric.ball 0 1) v g hph (Metric.ball 0 (2 * τ)) Metric.isOpen_ball hsub1
      hvC1 hne
  -- (1c) the convex trap for `Dv`
  obtain ⟨V, hVdef⟩ : ∃ t : Set Plane, t = Metric.ball (gradient v 0) (3 * δ / 4) := ⟨_, rfl⟩
  have hVo : IsOpen V := by rw [hVdef]; exact Metric.isOpen_ball
  have hVc : Convex ℝ V := by rw [hVdef]; exact convex_ball _ _
  have hξ0b : ‖gradient v 0‖ ≤ F.C₀ := (hann 0 hzero).2.1
  have hVann : ∀ ζ ∈ V, a ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ b := by
    intro ζ hζ
    rw [hVdef, Metric.mem_ball, dist_eq_norm] at hζ
    have h1 : ‖gradient v 0‖ - ‖ζ - gradient v 0‖ ≤ ‖ζ‖ := by
      have := norm_sub_norm_le (gradient v 0) (gradient v 0 - ζ)
      have h2 : ‖gradient v 0 - (gradient v 0 - ζ)‖ = ‖ζ‖ := by simp
      have h3 : ‖gradient v 0 - ζ‖ = ‖ζ - gradient v 0‖ := norm_sub_rev _ _
      rw [h2, h3] at this
      linarith
    have h4 : ‖ζ‖ ≤ ‖gradient v 0‖ + ‖ζ - gradient v 0‖ := by
      have := norm_add_le (gradient v 0) (ζ - gradient v 0)
      simpa using this
    rw [hadef, hbdef]
    exact ⟨by linarith, by linarith⟩
  have hgV2 : ∀ x ∈ Metric.ball (0 : Plane) (2 * τ), gradient v x ∈ V := by
    intro x hx
    rw [hVdef, Metric.mem_ball, dist_eq_norm]
    have := (hann x hx).2.2
    linarith
  -- (1a) + (1e):  the differentiated equation on every ball `B_r`, `0 < r ≤ 2 τ`
  have hdivsol : ∀ r : ℝ, 0 < r → r ≤ 2 * τ → ∀ e : Plane,
      IsLinearDivSol (Metric.ball 0 r) (fun x => FluxJacobian p (gradient v x))
        (fun x => inner ℝ (gradient v x) e)
        (fun x => gradient (fun y => inner ℝ (gradient v y) e) x) := by
    intro r hr hr2 e
    have hsubr : Metric.ball (0 : Plane) r ⊆ Metric.ball (0 : Plane) (2 * τ) :=
      Metric.ball_subset_ball hr2
    have hphr : IsPHarm p (Metric.ball 0 r) v g :=
      (PHarmRestrict p hp hp2 (Metric.ball 0 1) v g hph).1 (Metric.ball 0 r)
        Metric.isOpen_ball (hsubr.trans hsub1)
    have hphr' : IsPHarm p (Metric.ball 0 r) v (gradient v) :=
      (PHarmWeakGradClassical p hp (Metric.ball 0 r) v g hphr
        (hvC1.mono hsubr)).1
    exact DifferentiatedEqn p hp hp2 (Metric.ball 0 r) v hphr' (hvsm.mono hsubr)
      (fun x hx => hne x (hsubr hx)) e
  -- the two sharp bridges between `v` and its gradient field, at a point and at a pair
  obtain ⟨-, -, hbrSup, hbrHol⟩ :=
    GradientFieldOrderShift (Metric.ball 0 (2 * τ)) v Metric.isOpen_ball hvsm
  have hbr1 : ∀ x : Plane, ‖iteratedFDeriv ℝ 1 v x‖ = ‖gradient v x‖ := by
    intro x
    rw [← hbrSup 0 x, norm_iteratedFDeriv_zero]
  have hz0 : ∀ (f : Plane → Plane) (x y : Plane),
      ‖iteratedFDeriv ℝ 0 f x - iteratedFDeriv ℝ 0 f y‖ = ‖f x - f y‖ := by
    intro f x y
    rw [iteratedFDeriv_zero_eq_comp]
    show ‖(continuousMultilinearCurryFin0 ℝ Plane Plane).symm (f x)
        - (continuousMultilinearCurryFin0 ℝ Plane Plane).symm (f y)‖ = _
    rw [← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map]
  -- STEP 2:  the inductive claim.
  have hind : ∀ i : ℕ, i ≤ k →
      (∀ m ≤ i + 1, ∀ x ∈ Metric.ball (0 : Plane) (rr i), ‖iteratedFDeriv ℝ m v x‖ ≤ N i)
        ∧ (∀ x ∈ Metric.ball (0 : Plane) (rr i), ∀ y ∈ Metric.ball (0 : Plane) (rr i),
            ‖iteratedFDeriv ℝ (i + 1) v x - iteratedFDeriv ℝ (i + 1) v y‖
              ≤ N i * ‖x - y‖ ^ κ) := by
    intro i
    induction i with
    | zero =>
      -- base case:  `r_0 = 2 τ`, and both halves come from the first-order estimate
      intro _
      obtain ⟨-, -, hest3⟩ := F.est v g hph hbd
      have hr0 : Metric.ball (0 : Plane) (rr 0) = Metric.ball (0 : Plane) (2 * τ) := by
        rw [hrr0]
      have h1 : (1 : ℝ) ≤ N 0 := by
        rw [hN0]; have := le_max_left 1 F.C₀; linarith
      have hC : F.C₀ ≤ N 0 := by
        rw [hN0]; have := le_max_right 1 F.C₀; linarith
      refine ⟨?_, ?_⟩
      · intro m hm x hx
        rw [hr0] at hx
        interval_cases m
        · rw [norm_iteratedFDeriv_zero]
          calc ‖v x‖ = |v x| := Real.norm_eq_abs _
            _ ≤ 1 := hbd x (hsub1 hx)
            _ ≤ N 0 := h1
        · rw [hbr1 x]
          exact le_trans (hann x hx).2.1 hC
      · intro x hx y hy
        rw [hr0] at hx hy
        rw [← hbrHol 0 x hx y hy, hz0]
        have hE := hest3 x (hsub34 hx) y (hsub34 hy)
        rw [← hκdef] at hE
        refine le_trans hE ?_
        have hpow : (0 : ℝ) ≤ ‖x - y‖ ^ κ := Real.rpow_nonneg (norm_nonneg _) κ
        exact mul_le_mul_of_nonneg_right hC hpow
    | succ n ih =>
      -- inductive step:  one bootstrap round, via (0d)
      intro hi
      have hn : n ≤ k := by omega
      obtain ⟨s1, s2⟩ := ih hn
      have hrn : 0 < rr n := lt_trans hτ0 (hrrlb n (by omega))
      have hrn2 : rr n ≤ 2 * τ := hrrub n
      have hsubn : Metric.ball (0 : Plane) (rr n) ⊆ Metric.ball (0 : Plane) (2 * τ) :=
        Metric.ball_subset_ball hrn2
      have hres := hNfP n (N n) (hNpos n) hn v V hVo hVc hVann
        (fun x hx => hgV2 x (hsubn hx))
        (hvsm.mono hsubn)
        (fun x hx => hbd x (hsub1 (hsubn hx)))
        (fun x hx => (hann x (hsubn hx)).2.1)
        s1 s2 (hdivsol (rr n) hrn hrn2)
      rw [← hNsucc n] at hres
      exact hres
  -- STEP 3:  conclusion.
  obtain ⟨hck, -⟩ := hind k (le_refl k)
  have hsubτ : Metric.ball (0 : Plane) τ ⊆ Metric.ball (0 : Plane) (rr k) :=
    Metric.ball_subset_ball (le_of_lt (hrrlb k (by omega)))
  refine ⟨?_, ?_⟩
  · exact (hvsm.mono (Metric.ball_subset_ball (by linarith))).of_le (by exact_mod_cast le_top)
  · intro i hi x hx
    exact hck i hi x (hsubτ hx)
