-- Prove2me | solution 1 for GlobalInexactNewton.TrustRegion.theorem_4_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T07:19:26.6841+00:00
-- url     : https://prove2.me/submissions/25160db7-dd1c-4bf3-b749-05d1701784d6

import Mathlib
import Definitions.Def_GlobalInexactNewton_TrustRegion_Method

set_option autoImplicit false

namespace TRProofC7710

open Filter Topology GlobalInexactNewton.TrustRegion GlobalInexactNewton.Backtracking

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma pred_eq (F : E → E) (x s : E) : pred F x s = ‖F x‖ - ‖F x + fderiv ℝ F x s‖ := rfl

lemma ared_eq (F : E → E) (x s : E) : ared F x s = ‖F x‖ - ‖F (x + s)‖ := rfl

lemma min_self {F : E → E} {x : E} {ρ : ℝ} {s : E} (hs : IsLinModelMin F x ρ s) :
    IsLinModelMin F x ‖s‖ s :=
  ⟨le_rfl, fun s' hs' => hs.2 s' (hs'.trans hs.1)⟩

lemma pred_nonneg {F : E → E} {x : E} {ρ : ℝ} {s : E} (hs : IsLinModelMin F x ρ s) :
    0 ≤ pred F x s := by
  have h := hs.2 0 (by rw [norm_zero]; exact (norm_nonneg s).trans hs.1)
  rw [map_zero, add_zero] at h
  rw [pred_eq]; linarith

lemma pred_ge {F : E → E} {x : E} {ρ : ℝ} {s : E} (hs : IsLinModelMin F x ρ s) (v : E) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hcv : c * ‖v‖ ≤ ρ) :
    c * (‖F x‖ - ‖F x + fderiv ℝ F x v‖) ≤ pred F x s := by
  have h1 := hs.2 (c • v) (by rw [norm_smul, Real.norm_of_nonneg hc0]; exact hcv)
  have h2 : F x + fderiv ℝ F x (c • v) = (1 - c) • F x + c • (F x + fderiv ℝ F x v) := by
    rw [map_smul, smul_add, sub_smul, one_smul]; abel
  have h3 : ‖F x + fderiv ℝ F x (c • v)‖ ≤ (1 - c) * ‖F x‖ + c * ‖F x + fderiv ℝ F x v‖ := by
    rw [h2]
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [norm_smul, norm_smul, Real.norm_of_nonneg hc0, Real.norm_of_nonneg (by linarith)]
  rw [pred_eq]; linarith

lemma ratio_good {F : E → E} {x s : E} {η M u : ℝ}
    (hT : ‖F (x + s) - F x - fderiv ℝ F x s‖ ≤ η * ‖s‖) (hM : ‖s‖ ≤ M * pred F x s)
    (hηM : η * M ≤ 1 - u) (hη : 0 ≤ η) (hp : 0 ≤ pred F x s) :
    u * pred F x s ≤ ared F x s := by
  have e : (F x + fderiv ℝ F x s) + (F (x + s) - F x - fderiv ℝ F x s) = F (x + s) := by abel
  have h1 := norm_add_le (F x + fderiv ℝ F x s) (F (x + s) - F x - fderiv ℝ F x s)
  rw [e] at h1
  have h2 : η * ‖s‖ ≤ η * (M * pred F x s) := mul_le_mul_of_nonneg_left hM hη
  have h3 : η * M * pred F x s ≤ (1 - u) * pred F x s := mul_le_mul_of_nonneg_right hηM hp
  have hP := pred_eq F x s
  rw [ared_eq]
  nlinarith

lemma taylor_unif {F : E → E} (hF : ContDiff ℝ 1 F) (y : E) {η : ℝ} (hη : 0 < η) :
    ∃ r > 0, ∀ x, dist x y < r → ∀ s : E, ‖s‖ < r →
      ‖F (x + s) - F x - fderiv ℝ F x s‖ ≤ η * ‖s‖ := by
  have hs : HasStrictFDerivAt F (fderiv ℝ F y) y :=
    hF.contDiffAt.hasStrictFDerivAt (by norm_num)
  have ho := hasStrictFDerivAt_iff_isLittleO.mp hs
  have h1 := ho.def (half_pos hη)
  obtain ⟨ε, hε, hε'⟩ := Metric.eventually_nhds_iff.mp h1
  have hc : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by norm_num)
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuous_iff.mp hc y (η / 2) (half_pos hη)
  refine ⟨min (ε / 2) δ, lt_min (half_pos hε) hδ, fun x hx s hs' => ?_⟩
  have hxe : dist x y < ε / 2 := lt_of_lt_of_le hx (min_le_left _ _)
  have hse : ‖s‖ < ε / 2 := lt_of_lt_of_le hs' (min_le_left _ _)
  have hp : dist (x + s, x) (y, y) < ε := by
    rw [Prod.dist_eq]
    refine max_lt ?_ (by linarith)
    calc dist (x + s) y ≤ dist (x + s) x + dist x y := dist_triangle _ _ _
      _ = ‖s‖ + dist x y := by rw [dist_eq_norm, add_sub_cancel_left]
      _ < ε := by linarith
  have h2 := hε' hp
  simp only [add_sub_cancel_left] at h2
  have h3 : ‖fderiv ℝ F x - fderiv ℝ F y‖ < η / 2 := by
    have := hδ' x (lt_of_lt_of_le hx (min_le_right _ _)); rwa [dist_eq_norm] at this
  have e : F (x + s) - F x - fderiv ℝ F x s =
      (F (x + s) - F x - fderiv ℝ F y s) - (fderiv ℝ F x - fderiv ℝ F y) s := by
    rw [ContinuousLinearMap.sub_apply]; abel
  rw [e]
  calc _ ≤ ‖F (x + s) - F x - fderiv ℝ F y s‖ + ‖(fderiv ℝ F x - fderiv ℝ F y) s‖ :=
        norm_sub_le _ _
    _ ≤ η / 2 * ‖s‖ + η / 2 * ‖s‖ :=
        add_le_add h2 ((ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right h3.le (norm_nonneg _)))
    _ = η * ‖s‖ := by ring

lemma trialRadius_pos {δ θmin : ℝ} {θ : ℕ → ℝ} (hθmin : 0 < θmin) (hδ : 0 < δ) :
    ∀ n : ℕ, (∀ j < n, θmin ≤ θ j) → 0 < trialRadius δ θ n
  | 0, _ => by simp only [trialRadius]; exact hδ
  | n + 1, h => by
      simp only [trialRadius]
      exact mul_pos (lt_of_lt_of_le hθmin (h n (Nat.lt_succ_self n)))
        (trialRadius_pos hθmin hδ n fun j hj => h j (Nat.lt_succ_of_lt hj))

/-- Every model minimizer at radius at most `r` from `x` passes the `u`-test. -/
def Good (F : E → E) (u : ℝ) (x : E) (r : ℝ) : Prop :=
  ∀ ρ ≤ r, ∀ s : E, IsLinModelMin F x ρ s → u * pred F x s ≤ ared F x s

section run

variable {F : E → E} {t u θmin θmax : ℝ} {x : ℕ → E} {δbar : ℕ → ℝ}
    {θ : ℕ → ℕ → ℝ} {m : ℕ → ℕ} {s : ℕ → ℕ → E}

lemma δbar_pos (hrun : IsTRRun F t u θmin θmax x δbar θ m s) : ∀ k, 0 < δbar k
  | 0 => hrun.δbar_zero_pos
  | k + 1 => by
    have hθ0 := hrun.θ_bounds.1
    have hk := trialRadius_pos hθ0 (δbar_pos hrun k) (m k) fun j hj => (hrun.θ_mem k j hj).1
    by_cases h : u * pred F (x k) (s k (m k)) ≤ ared F (x k) (s k (m k))
    · exact lt_of_lt_of_le hk (hrun.radius_up k h)
    · exact lt_of_lt_of_le (mul_pos hθ0 hk) (hrun.radius_down k (not_le.mp h))

lemma step_radius (hrun : IsTRRun F t u θmin θmax x δbar θ m s) (k : ℕ) {r : ℝ} (hr : 0 < r)
    (hG : Good F u (x k) r) :
    min (δbar k) (θmin * r) ≤ trialRadius (δbar k) (θ k) (m k) ∧
      min (δbar k) (θmin * r) ≤ δbar (k + 1) := by
  obtain ⟨ht0, htu, -⟩ := hrun.tu
  obtain ⟨hθ0, hθlt, hθ1⟩ := hrun.θ_bounds
  have hpos := trialRadius_pos hθ0 (δbar_pos hrun k) (m k) fun j hj => (hrun.θ_mem k j hj).1
  have h1 : min (δbar k) (θmin * r) ≤ trialRadius (δbar k) (θ k) (m k) := by
    rcases hmk : m k with _ | j
    · simp only [trialRadius]; exact min_le_left _ _
    · have hrej := hrun.rejected k j (by omega)
      have hρ : r < trialRadius (δbar k) (θ k) j := by
        by_contra hle
        push_neg at hle
        have := hG _ hle _ (hrun.argmin k j (by omega))
        have hp := pred_nonneg (hrun.argmin k j (by omega))
        nlinarith
      have hθj := hrun.θ_mem k j (by omega)
      simp only [trialRadius]
      calc min (δbar k) (θmin * r) ≤ θmin * r := min_le_right _ _
        _ ≤ θ k j * trialRadius (δbar k) (θ k) j :=
          mul_le_mul hθj.1 hρ.le hr.le (hθ0.le.trans hθj.1)
  refine ⟨h1, ?_⟩
  by_cases hδ : trialRadius (δbar k) (θ k) (m k) ≤ r
  · have hu := hG _ hδ _ (hrun.argmin k (m k) le_rfl)
    exact h1.trans (hrun.radius_up k hu)
  · push_neg at hδ
    have hlow : θmin * trialRadius (δbar k) (θ k) (m k) ≤ δbar (k + 1) := by
      by_cases h : u * pred F (x k) (s k (m k)) ≤ ared F (x k) (s k (m k))
      · have := hrun.radius_up k h
        nlinarith
      · exact hrun.radius_down k (not_le.mp h)
    calc min (δbar k) (θmin * r) ≤ θmin * r := min_le_right _ _
      _ ≤ θmin * trialRadius (δbar k) (θ k) (m k) := mul_le_mul_of_nonneg_left hδ.le hθ0.le
      _ ≤ δbar (k + 1) := hlow

lemma radius_stays (hrun : IsTRRun F t u θmin θmax x δbar θ m s) {r : ℝ} (hr : 0 < r) (k0 : ℕ)
    (hG : ∀ k ≥ k0, Good F u (x k) r) :
    ∀ k ≥ k0, min (δbar k0) (θmin * r) ≤ δbar k ∧
      min (δbar k0) (θmin * r) ≤ trialRadius (δbar k) (θ k) (m k) := by
  have hb : ∀ k ≥ k0, min (δbar k0) (θmin * r) ≤ δbar k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact min_le_left _ _
    | succ k hk ih =>
      exact le_trans (le_min ih (min_le_right _ _)) (step_radius hrun k hr (hG k hk)).2
  intro k hk
  exact ⟨hb k hk, le_trans (le_min (hb k hk) (min_le_right _ _)) (step_radius hrun k hr (hG k hk)).1⟩

lemma norm_step (hrun : IsTRRun F t u θmin θmax x δbar θ m s) (k : ℕ) :
    t * pred F (x k) (s k (m k)) ≤ ‖F (x k)‖ - ‖F (x (k + 1))‖ := by
  have := hrun.accepted k
  rw [ared_eq, ← hrun.step k] at this
  exact this

lemma norm_anti (hrun : IsTRRun F t u θmin θmax x δbar θ m s) :
    Antitone (fun k => ‖F (x k)‖) := by
  refine antitone_nat_of_succ_le fun k => ?_
  have h1 := norm_step hrun k
  have hp := pred_nonneg (hrun.argmin k (m k) le_rfl)
  have ht := hrun.tu.1
  nlinarith

end run

section part1

variable {F : E → E} {t u θmin θmax : ℝ} {x : ℕ → E} {δbar : ℕ → ℝ}
    {θ : ℕ → ℕ → ℝ} {m : ℕ → ℕ} {s : ℕ → ℕ → E}

lemma part1 (hF : ContDiff ℝ 1 F) (hrun : IsTRRun F t u θmin θmax x δbar θ m s) (y : E)
    (hy : MapClusterPt y atTop x) : IsStationaryPtNorm F y := by
  intro sbar
  by_contra hcon
  push_neg at hcon
  obtain ⟨ht0, htu, hu1⟩ := hrun.tu
  obtain ⟨hθ0, hθlt, hθ1⟩ := hrun.θ_bounds
  have hFc : Continuous F := hF.continuous
  have hdc : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by norm_num)
  let g : E → ℝ := fun z => ‖F z‖ - ‖F z + fderiv ℝ F z sbar‖
  have hgc : Continuous g :=
    hFc.norm.sub ((hFc.add (hdc.clm_apply continuous_const)).norm)
  obtain ⟨ε, hε0, hεg⟩ : ∃ ε : ℝ, 0 < ε ∧ ε = g y / 2 := ⟨g y / 2, by simp only [g]; linarith, rfl⟩
  obtain ⟨N, hN, hNdef⟩ : ∃ N : ℝ, 0 < N ∧ N = ‖sbar‖ := by
    refine ⟨‖sbar‖, ?_, rfl⟩
    rw [norm_pos_iff]; rintro rfl; simp at hcon
  obtain ⟨r1, hr1, hr1'⟩ : ∃ r1 > 0, ∀ z, dist z y < r1 → ε < g z := by
    obtain ⟨δ, hδ, h⟩ := Metric.continuous_iff.mp hgc y ε hε0
    refine ⟨δ, hδ, fun z hz => ?_⟩
    have h2 := h z hz; rw [Real.dist_eq] at h2
    have := (abs_lt.mp h2).1; linarith
  -- lower bound on pred from the descent direction sbar
  have hbase : ∀ z, dist z y < r1 → ∀ ρ s', IsLinModelMin F z ρ s' → ∀ c : ℝ, 0 ≤ c → c ≤ 1 →
      c * N ≤ ρ → ε * c ≤ pred F z s' := by
    intro z hz ρ s' hs' c hc0 hc1 hcN
    have h := pred_ge hs' sbar hc0 hc1 (by rw [← hNdef]; exact hcN)
    have hgz := hr1' z hz
    have : ε * c ≤ c * g z := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left hgz.le hc0
    exact this.trans h
  have hA : ∀ z, dist z y < r1 → ∀ ρ s', IsLinModelMin F z ρ s' →
      ε * min 1 (‖s'‖ / N) ≤ pred F z s' := by
    intro z hz ρ s' hs'
    refine hbase z hz _ s' (min_self hs') _ (le_min zero_le_one (div_nonneg (norm_nonneg _) hN.le))
      (min_le_left _ _) ?_
    calc min 1 (‖s'‖ / N) * N ≤ (‖s'‖ / N) * N := mul_le_mul_of_nonneg_right (min_le_right _ _) hN.le
      _ = ‖s'‖ := div_mul_cancel₀ _ hN.ne'
  have hη0 : 0 < (1 - u) * ε / N := div_pos (mul_pos (by linarith) hε0) hN
  obtain ⟨rT, hrT, hT⟩ := taylor_unif hF y hη0
  obtain ⟨R, hR, hRr1, hRrT⟩ : ∃ R : ℝ, 0 < R ∧ R ≤ r1 ∧ R ≤ rT :=
    ⟨min r1 rT, lt_min hr1 hrT, min_le_left _ _, min_le_right _ _⟩
  obtain ⟨r, hr, hrT2, hrN⟩ : ∃ r : ℝ, 0 < r ∧ r < rT ∧ r ≤ N :=
    ⟨min (rT / 2) N, lt_min (half_pos hrT) hN,
      lt_of_le_of_lt (min_le_left _ _) (half_lt_self hrT), min_le_right _ _⟩
  have hGood : ∀ z, dist z y < R → Good F u z r := by
    intro z hz ρ hρ s' hs'
    have hzr1 : dist z y < r1 := lt_of_lt_of_le hz hRr1
    have hzrT : dist z y < rT := lt_of_lt_of_le hz hRrT
    have hsρ : ‖s'‖ ≤ r := hs'.1.trans hρ
    have hsN : ‖s'‖ / N ≤ 1 := (div_le_one hN).mpr (hsρ.trans hrN)
    have hA' := hA z hzr1 ρ s' hs'
    rw [min_eq_right hsN] at hA'
    have hM : ‖s'‖ ≤ (N / ε) * pred F z s' := by
      have e1 : ‖s'‖ = (N / ε) * (ε * (‖s'‖ / N)) := by field_simp
      rw [e1]
      exact mul_le_mul_of_nonneg_left hA' (div_nonneg hN.le hε0.le)
    refine ratio_good (hT z hzrT s' (lt_of_le_of_lt hsρ hrT2)) hM (le_of_eq ?_) hη0.le
      (pred_nonneg hs')
    field_simp
  -- the norms ‖F (x k)‖ decrease to a limit L
  have hanti := norm_anti hrun
  have hbdd : BddBelow (Set.range fun k => ‖F (x k)‖) :=
    ⟨0, by rintro _ ⟨k, rfl⟩; exact norm_nonneg _⟩
  obtain ⟨L, hlim⟩ : ∃ L, Tendsto (fun k => ‖F (x k)‖) atTop (𝓝 L) :=
    ⟨_, tendsto_atTop_ciInf hanti hbdd⟩
  have haL : ∀ k, L ≤ ‖F (x k)‖ := fun k => hanti.le_of_tendsto hlim k
  have hmono : ∀ k k', k ≤ k' → ‖F (x k')‖ ≤ ‖F (x k)‖ := fun k k' h => hanti h
  set C : ℝ := N / (ε * t) with hC
  have hC0 : 0 < C := div_pos hN (mul_pos hε0 ht0)
  have hτ : 0 < min (t * ε) (R / (2 * C)) := lt_min (mul_pos ht0 hε0) (by positivity)
  obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.mp hlim) _ hτ
  obtain ⟨k0, hk0K, hk0⟩ := Filter.frequently_atTop.mp
    (hy.frequently (p := fun z => z ∈ Metric.ball y (R / 2)) (Metric.ball_mem_nhds y (half_pos hR))) K
  have hk0' : dist (x k0) y < R / 2 := hk0
  have hgap : ‖F (x k0)‖ - L < min (t * ε) (R / (2 * C)) := by
    have := hK k0 hk0K; rw [Real.dist_eq] at this; exact lt_of_le_of_lt (le_abs_self _) this
  have hgap1 := lt_of_lt_of_le hgap (min_le_left _ _)
  have hgap2 := lt_of_lt_of_le hgap (min_le_right _ _)
  -- staying close: a bound on the distance travelled implies being in the good ball
  have hclose : ∀ k, dist (x k) (x k0) ≤ C * (‖F (x k0)‖ - ‖F (x k)‖) → dist (x k) y < R := by
    intro k hk
    have h1 : C * (‖F (x k0)‖ - ‖F (x k)‖) ≤ C * (‖F (x k0)‖ - L) :=
      mul_le_mul_of_nonneg_left (by linarith [haL k]) hC0.le
    have h2 : C * (‖F (x k0)‖ - L) < R / 2 := by
      have := mul_lt_mul_of_pos_left hgap2 hC0
      rwa [mul_div_assoc', mul_comm C R, mul_div_mul_right _ _ hC0.ne'] at this
    calc dist (x k) y ≤ dist (x k) (x k0) + dist (x k0) y := dist_triangle _ _ _
      _ < R := by linarith
  have hpath : ∀ k ≥ k0, dist (x k) (x k0) ≤ C * (‖F (x k0)‖ - ‖F (x k)‖) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
      have hxk := hclose k ih
      have hsk := hrun.argmin k (m k) le_rfl
      have hA' := hA (x k) (lt_of_lt_of_le hxk hRr1) _ _ hsk
      have hstep := norm_step hrun k
      have hpk : pred F (x k) (s k (m k)) < ε := by
        have h1 : ‖F (x k)‖ - ‖F (x (k + 1))‖ ≤ ‖F (x k0)‖ - L := by
          linarith [hmono k0 k hk, haL (k + 1)]
        nlinarith
      have hmin : min 1 (‖s k (m k)‖ / N) = ‖s k (m k)‖ / N := by
        rcases min_cases 1 (‖s k (m k)‖ / N) with ⟨h, -⟩ | ⟨h, -⟩
        · rw [h] at hA'; linarith
        · exact h
      rw [hmin] at hA'
      have hsk' : ‖s k (m k)‖ ≤ C * (‖F (x k)‖ - ‖F (x (k + 1))‖) := by
        have e1 : ‖s k (m k)‖ = C * (t * (ε * (‖s k (m k)‖ / N))) := by
          rw [hC]; field_simp
        rw [e1]
        refine mul_le_mul_of_nonneg_left ?_ hC0.le
        exact (mul_le_mul_of_nonneg_left hA' ht0.le).trans hstep
      calc dist (x (k + 1)) (x k0) ≤ dist (x (k + 1)) (x k) + dist (x k) (x k0) :=
            dist_triangle _ _ _
        _ = ‖s k (m k)‖ + dist (x k) (x k0) := by
            rw [hrun.step k, dist_eq_norm, add_sub_cancel_left]
        _ ≤ C * (‖F (x k)‖ - ‖F (x (k + 1))‖) + C * (‖F (x k0)‖ - ‖F (x k)‖) :=
            add_le_add hsk' ih
        _ = C * (‖F (x k0)‖ - ‖F (x (k + 1))‖) := by ring
  have hin : ∀ k ≥ k0, dist (x k) y < R := fun k hk => hclose k (hpath k hk)
  have hstay := radius_stays hrun hr k0 (fun k hk => hGood (x k) (hin k hk))
  obtain ⟨c, hc, hcdef⟩ : ∃ c : ℝ, 0 < c ∧ c = min (δbar k0) (θmin * r) :=
    ⟨_, lt_min (δbar_pos hrun k0) (mul_pos hθ0 hr), rfl⟩
  have hc1 : 0 ≤ min 1 (c / N) := le_min zero_le_one (div_nonneg hc.le hN.le)
  have hp0 : ∀ k ≥ k0, ε * min 1 (c / N) ≤ pred F (x k) (s k (m k)) := by
    intro k hk
    refine hbase (x k) (lt_of_lt_of_le (hin k hk) hRr1) _ _ (hrun.argmin k (m k) le_rfl) _ hc1
      (min_le_left _ _) ?_
    calc min 1 (c / N) * N ≤ (c / N) * N := mul_le_mul_of_nonneg_right (min_le_right _ _) hN.le
      _ = c := div_mul_cancel₀ _ hN.ne'
      _ ≤ _ := by rw [hcdef]; exact (hstay k hk).2
  have hdiff : Tendsto (fun k => ‖F (x k)‖ - ‖F (x (k + 1))‖) atTop (𝓝 0) := by
    have := hlim.sub (hlim.comp (tendsto_add_atTop_nat 1))
    simpa using this
  have hq : 0 < t * (ε * min 1 (c / N)) :=
    mul_pos ht0 (mul_pos hε0 (lt_min zero_lt_one (div_pos hc hN)))
  obtain ⟨K2, hK2⟩ := (Metric.tendsto_atTop.mp hdiff) _ hq
  have h1 := hK2 (max K2 k0) (le_max_left _ _)
  have h2 := hp0 (max K2 k0) (le_max_right _ _)
  have h3 := norm_step hrun (max K2 k0)
  rw [Real.dist_eq, sub_zero] at h1
  have h4 := (abs_lt.mp h1).2
  have h5 := mul_le_mul_of_nonneg_left h2 ht0.le
  linarith

end part1

section part23

variable [FiniteDimensional ℝ E] {F : E → E} {t u θmin θmax : ℝ} {x : ℕ → E} {δbar : ℕ → ℝ}
    {θ : ℕ → ℕ → ℝ} {m : ℕ → ℕ} {s : ℕ → ℕ → E}

lemma part23 (hF : ContDiff ℝ 1 F) (hrun : IsTRRun F t u θmin θmax x δbar θ m s) (xstar : E)
    (hcl : MapClusterPt xstar atTop x) (hinv : (fderiv ℝ F xstar).IsInvertible)
    (hst : IsStationaryPtNorm F xstar) :
    F xstar = 0 ∧ Tendsto x atTop (𝓝 xstar) ∧
      ∀ᶠ k in atTop, s k (m k) = -((fderiv ℝ F (x k)).inverse (F (x k))) := by
  obtain ⟨ht0, htu, hu1⟩ := hrun.tu
  obtain ⟨hθ0, hθlt, hθ1⟩ := hrun.θ_bounds
  have hFc : Continuous F := hF.continuous
  have hdc : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by norm_num)
  have hF0 : F xstar = 0 := by
    have h := hst (-((fderiv ℝ F xstar).inverse (F xstar)))
    rw [map_neg, hinv.self_apply_inverse, add_neg_cancel, norm_zero] at h
    exact norm_le_zero_iff.mp h
  refine ⟨hF0, ?_⟩
  obtain ⟨e, he⟩ := hinv
  obtain ⟨K, hK0, hKv⟩ : ∃ K : ℝ, 0 < K ∧ ∀ v, ‖v‖ ≤ K * ‖fderiv ℝ F xstar v‖ := by
    refine ⟨‖(e.symm : E →L[ℝ] E)‖ + 1, by positivity, fun v => ?_⟩
    have h1 : (e.symm : E →L[ℝ] E) (fderiv ℝ F xstar v) = v := by rw [← he]; simp
    calc ‖v‖ = ‖(e.symm : E →L[ℝ] E) (fderiv ℝ F xstar v)‖ := by rw [h1]
      _ ≤ ‖(e.symm : E →L[ℝ] E)‖ * ‖fderiv ℝ F xstar v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖(e.symm : E →L[ℝ] E)‖ + 1) * ‖fderiv ℝ F xstar v‖ := by
          nlinarith [norm_nonneg (fderiv ℝ F xstar v)]
  obtain ⟨M, hM0, hMdef⟩ : ∃ M : ℝ, 0 < M ∧ M = 2 * K := ⟨2 * K, by positivity, rfl⟩
  have hU1 : {z | (fderiv ℝ F z).IsInvertible} ∈ 𝓝 xstar := by
    have : Set.range ((↑) : (E ≃L[ℝ] E) → E →L[ℝ] E) ∈ 𝓝 (fderiv ℝ F xstar) :=
      ContinuousLinearEquiv.isOpen.mem_nhds ⟨e, he⟩
    exact hdc.continuousAt.preimage_mem_nhds this
  obtain ⟨ρ1, hρ1, hρ1'⟩ := Metric.mem_nhds_iff.mp hU1
  obtain ⟨ρ2, hρ2, hρ2'⟩ := Metric.continuous_iff.mp hdc xstar (1 / (2 * K)) (by positivity)
  have hη0 : 0 < (1 - u) / (2 * M) := div_pos (by linarith) (by positivity)
  obtain ⟨rT, hrT, hT⟩ := taylor_unif hF xstar hη0
  obtain ⟨R, hR, hR1, hR2, hR3⟩ : ∃ R : ℝ, 0 < R ∧ R ≤ ρ1 ∧ R ≤ ρ2 ∧ R ≤ rT :=
    ⟨min ρ1 (min ρ2 rT), lt_min hρ1 (lt_min hρ2 hrT), min_le_left _ _,
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  have hinvz : ∀ z, dist z xstar < R → (fderiv ℝ F z).IsInvertible := fun z hz =>
    hρ1' (Metric.mem_ball.mpr (lt_of_lt_of_le hz hR1))
  have hMv : ∀ z, dist z xstar < R → ∀ v, ‖v‖ ≤ M * ‖fderiv ℝ F z v‖ := by
    intro z hz v
    have hd : ‖fderiv ℝ F z - fderiv ℝ F xstar‖ < 1 / (2 * K) := by
      have := hρ2' z (lt_of_lt_of_le hz hR2); rwa [dist_eq_norm] at this
    have h1 : ‖fderiv ℝ F xstar v‖ ≤
        ‖fderiv ℝ F z v‖ + ‖(fderiv ℝ F z - fderiv ℝ F xstar) v‖ := by
      have e1 : fderiv ℝ F xstar v = fderiv ℝ F z v - (fderiv ℝ F z - fderiv ℝ F xstar) v := by
        rw [ContinuousLinearMap.sub_apply]; abel
      rw [e1]; exact norm_sub_le _ _
    have h2 : ‖(fderiv ℝ F z - fderiv ℝ F xstar) v‖ ≤ 1 / (2 * K) * ‖v‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hd.le (norm_nonneg _))
    have h3 := hKv v
    have h4 : K * (1 / (2 * K) * ‖v‖) = ‖v‖ / 2 := by field_simp <;> ring
    have h5 : K * ‖fderiv ℝ F xstar v‖ ≤ K * (‖fderiv ℝ F z v‖ + 1 / (2 * K) * ‖v‖) :=
      mul_le_mul_of_nonneg_left (by linarith) hK0.le
    rw [mul_add, h4] at h5
    rw [hMdef]; linarith
  have hdist : ∀ z, dist z xstar < R → ‖z - xstar‖ ≤ 2 * M * ‖F z‖ := by
    intro z hz
    have hzs : ‖z - xstar‖ < rT := by rw [← dist_eq_norm]; exact lt_of_lt_of_le hz hR3
    have hT' := hT xstar (by rw [dist_self]; exact hrT) (z - xstar) hzs
    have e0 : xstar + (z - xstar) = z := by abel
    rw [e0, hF0, sub_zero] at hT'
    have h1 := hMv xstar (by rw [dist_self]; exact hR) (z - xstar)
    have h2 : ‖fderiv ℝ F xstar (z - xstar)‖ ≤ ‖F z‖ + (1 - u) / (2 * M) * ‖z - xstar‖ := by
      have e1 : fderiv ℝ F xstar (z - xstar) = F z - (F z - fderiv ℝ F xstar (z - xstar)) := by
        abel
      rw [e1]; linarith [norm_sub_le (F z) (F z - fderiv ℝ F xstar (z - xstar))]
    have h3 : M * ((1 - u) / (2 * M) * ‖z - xstar‖) = (1 - u) / 2 * ‖z - xstar‖ := by
      field_simp <;> ring
    have h4 := mul_le_mul_of_nonneg_left h2 hM0.le
    rw [mul_add, h3] at h4
    nlinarith [norm_nonneg (z - xstar), norm_nonneg (F z)]
  have hsmall : ∀ z, dist z xstar < R → ∀ ρ s', IsLinModelMin F z ρ s' →
      ‖s'‖ ≤ 2 * M * ‖F z‖ := by
    intro z hz ρ s' hs'
    have hp := pred_nonneg hs'
    rw [pred_eq] at hp
    have h1 : ‖fderiv ℝ F z s'‖ ≤ 2 * ‖F z‖ := by
      have e1 : fderiv ℝ F z s' = (F z + fderiv ℝ F z s') - F z := by abel
      rw [e1]; linarith [norm_sub_le (F z + fderiv ℝ F z s') (F z)]
    have h2 := hMv z hz s'
    nlinarith [mul_le_mul_of_nonneg_left h1 hM0.le]
  have hnewt : ∀ z, dist z xstar < R →
      F z + fderiv ℝ F z (-((fderiv ℝ F z).inverse (F z))) = 0 ∧
      ‖-((fderiv ℝ F z).inverse (F z))‖ ≤ M * ‖F z‖ := by
    intro z hz
    have hi := hinvz z hz
    have e1 : fderiv ℝ F z (-((fderiv ℝ F z).inverse (F z))) = - F z := by
      rw [map_neg, hi.self_apply_inverse]
    refine ⟨by rw [e1, add_neg_cancel], ?_⟩
    have := hMv z hz (-((fderiv ℝ F z).inverse (F z)))
    simpa only [e1, norm_neg] using this
  have hGoodz : ∀ z, dist z xstar < R → ‖F z‖ < rT / (2 * M) → Good F u z 1 := by
    intro z hz hFz ρ _ s' hs'
    have hs1 := hsmall z hz ρ s' hs'
    have hsT : ‖s'‖ < rT := by
      calc ‖s'‖ ≤ 2 * M * ‖F z‖ := hs1
        _ < 2 * M * (rT / (2 * M)) := mul_lt_mul_of_pos_left hFz (by positivity)
        _ = rT := by field_simp
    obtain ⟨hN0, hNb⟩ := hnewt z hz
    have hgN : ‖F z‖ - ‖F z + fderiv ℝ F z (-((fderiv ℝ F z).inverse (F z)))‖ = ‖F z‖ := by
      rw [hN0, norm_zero, sub_zero]
    have hpp := pred_nonneg hs'
    have hpred : ‖s'‖ ≤ 2 * M * pred F z s' := by
      rcases le_or_gt ‖-((fderiv ℝ F z).inverse (F z))‖ ‖s'‖ with h | h
      · have := pred_ge (min_self hs') (-((fderiv ℝ F z).inverse (F z))) zero_le_one le_rfl
          (by rw [one_mul]; exact h)
        rw [hgN, one_mul] at this
        have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 2 * M)
        linarith
      · have hsN0 : 0 < ‖-((fderiv ℝ F z).inverse (F z))‖ := lt_of_le_of_lt (norm_nonneg _) h
        obtain ⟨q, hq⟩ : ∃ q : ℝ, q = ‖s'‖ / ‖-((fderiv ℝ F z).inverse (F z))‖ := ⟨_, rfl⟩
        have hq0 : 0 ≤ q := by rw [hq]; exact div_nonneg (norm_nonneg _) hsN0.le
        have hq1 : q ≤ 1 := by rw [hq]; exact (div_le_one hsN0).mpr h.le
        have hqN : q * ‖-((fderiv ℝ F z).inverse (F z))‖ = ‖s'‖ := by
          rw [hq]; exact div_mul_cancel₀ _ hsN0.ne'
        have h3 := pred_ge (min_self hs') (-((fderiv ℝ F z).inverse (F z))) hq0 hq1 hqN.le
        rw [hgN] at h3
        have h1 := mul_le_mul_of_nonneg_left hNb hq0
        have h2 := mul_le_mul_of_nonneg_left h3 hM0.le
        nlinarith [norm_nonneg (F z), mul_nonneg hq0 (norm_nonneg (F z)), mul_nonneg hM0.le hpp]
    refine ratio_good (hT z (lt_of_lt_of_le hz hR3) s' hsT) hpred (le_of_eq ?_) hη0.le hpp
    field_simp
  have hFsmall : ∀ τ > 0, ∃ K', ∀ k ≥ K', ‖F (x k)‖ < τ := by
    intro τ hτ
    have hev : ∀ᶠ z in 𝓝 xstar, ‖F z‖ < τ := by
      have h2 : Tendsto (fun z => ‖F z‖) (𝓝 xstar) (𝓝 0) := by
        have := hFc.norm.tendsto xstar; rwa [hF0, norm_zero] at this
      exact h2.eventually (gt_mem_nhds hτ)
    obtain ⟨K', -, hK'⟩ := Filter.frequently_atTop.mp (hcl.frequently hev) 0
    exact ⟨K', fun k hk => lt_of_le_of_lt (norm_anti hrun hk) hK'⟩
  obtain ⟨K1, hK1⟩ := hFsmall (R / (8 * M)) (by positivity)
  obtain ⟨k0, hk0K, hk0⟩ := Filter.frequently_atTop.mp
    (hcl.frequently (p := fun z => z ∈ Metric.ball xstar (R / 2))
      (Metric.ball_mem_nhds xstar (half_pos hR))) K1
  have hin : ∀ k ≥ k0, dist (x k) xstar < R / 2 := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact hk0
    | succ k hk ih =>
      have hzR : dist (x k) xstar < R := by linarith
      have hs1 := hsmall (x k) hzR _ _ (hrun.argmin k (m k) le_rfl)
      have hFk := hK1 k (le_trans hk0K hk)
      have e8 : 2 * M * (R / (8 * M)) = R / 4 := by field_simp <;> ring
      have hs2 : ‖s k (m k)‖ < R / 4 := by
        have := mul_lt_mul_of_pos_left hFk (by positivity : (0 : ℝ) < 2 * M)
        linarith
      have hd1 : dist (x (k + 1)) xstar < R := by
        calc dist (x (k + 1)) xstar ≤ dist (x (k + 1)) (x k) + dist (x k) xstar :=
              dist_triangle _ _ _
          _ = ‖s k (m k)‖ + dist (x k) xstar := by
              rw [hrun.step k, dist_eq_norm, add_sub_cancel_left]
          _ < R := by linarith
      have hd2 := hdist (x (k + 1)) hd1
      have hFk1 := hK1 (k + 1) (by omega)
      have := mul_lt_mul_of_pos_left hFk1 (by positivity : (0 : ℝ) < 2 * M)
      rw [dist_eq_norm]; linarith
  have hconv : Tendsto x atTop (𝓝 xstar) := by
    rw [Metric.tendsto_atTop]
    intro τ hτ
    obtain ⟨K2, hK2⟩ := hFsmall (τ / (2 * M)) (by positivity)
    refine ⟨max k0 K2, fun k hk => ?_⟩
    have hz : dist (x k) xstar < R := by linarith [hin k (le_trans (le_max_left _ _) hk)]
    have h1 := hdist (x k) hz
    have h2 := hK2 k (le_trans (le_max_right _ _) hk)
    have h3 := mul_lt_mul_of_pos_left h2 (by positivity : (0 : ℝ) < 2 * M)
    have e : 2 * M * (τ / (2 * M)) = τ := by field_simp
    rw [dist_eq_norm]; linarith
  refine ⟨hconv, ?_⟩
  obtain ⟨K3, hK3⟩ := hFsmall (rT / (2 * M)) (by positivity)
  have hG : ∀ k ≥ max k0 K3, Good F u (x k) 1 := fun k hk =>
    hGoodz (x k) (by linarith [hin k (le_trans (le_max_left _ _) hk)])
      (hK3 k (le_trans (le_max_right _ _) hk))
  have hstay := radius_stays hrun one_pos (max k0 K3) hG
  obtain ⟨c, hc, hcdef⟩ : ∃ c : ℝ, 0 < c ∧ c = min (δbar (max k0 K3)) (θmin * 1) :=
    ⟨_, lt_min (δbar_pos hrun _) (by linarith), rfl⟩
  obtain ⟨K4, hK4⟩ := hFsmall (c / M) (by positivity)
  refine Filter.eventually_atTop.mpr ⟨max (max k0 K3) K4, fun k hk => ?_⟩
  have hkk1 : max k0 K3 ≤ k := le_trans (le_max_left _ _) hk
  have hz : dist (x k) xstar < R := by
    linarith [hin k (le_trans (le_max_left _ _) hkk1)]
  obtain ⟨hN0, hNb⟩ := hnewt (x k) hz
  have hδ : c ≤ trialRadius (δbar k) (θ k) (m k) := by rw [hcdef]; exact (hstay k hkk1).2
  have hFk := hK4 k (le_trans (le_max_right _ _) hk)
  have hNle : ‖-((fderiv ℝ F (x k)).inverse (F (x k)))‖ ≤ trialRadius (δbar k) (θ k) (m k) := by
    have := mul_lt_mul_of_pos_left hFk hM0
    have e : M * (c / M) = c := by field_simp
    linarith
  have hmin := hrun.argmin k (m k) le_rfl
  have h1 := hmin.2 _ hNle
  rw [hN0, norm_zero] at h1
  have h2 : F (x k) + fderiv ℝ F (x k) (s k (m k)) = 0 := norm_le_zero_iff.mp h1
  have h3 : fderiv ℝ F (x k) (s k (m k)) =
      fderiv ℝ F (x k) (-((fderiv ℝ F (x k)).inverse (F (x k)))) :=
    (add_right_inj (F (x k))).mp (h2.trans hN0.symm)
  have h5 := hMv (x k) hz (s k (m k) - -((fderiv ℝ F (x k)).inverse (F (x k))))
  rw [map_sub, h3, sub_self, norm_zero, mul_zero] at h5
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h5)

end part23

end TRProofC7710

open GlobalInexactNewton.TrustRegion Filter Topology in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : E → E) (hF : ContDiff ℝ 1 F) (t u θmin θmax : ℝ) (x : ℕ → E) (δbar : ℕ → ℝ)
    (θ : ℕ → ℕ → ℝ) (m : ℕ → ℕ) (s : ℕ → ℕ → E)
    (hrun : IsTRRun F t u θmin θmax x δbar θ m s) :
    (∀ y : E, MapClusterPt y atTop x → IsStationaryPtNorm F y) ∧
      ∀ xstar : E, MapClusterPt xstar atTop x → (fderiv ℝ F xstar).IsInvertible →
        F xstar = 0 ∧ Tendsto x atTop (𝓝 xstar) ∧
          ∀ᶠ k in atTop, s k (m k) = -((fderiv ℝ F (x k)).inverse (F (x k))) := by
  exact ⟨fun y hy => TRProofC7710.part1 hF hrun y hy, fun xstar hcl hinv =>
    TRProofC7710.part23 hF hrun xstar hcl hinv (TRProofC7710.part1 hF hrun xstar hcl)⟩
