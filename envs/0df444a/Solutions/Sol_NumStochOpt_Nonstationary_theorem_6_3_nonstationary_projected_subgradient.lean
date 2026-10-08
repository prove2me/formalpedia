-- Prove2me | solution 1 for NumStochOpt.Nonstationary.theorem_6_3_nonstationary_projected_subgradient
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T07:06:15.890126+00:00
-- url     : https://prove2.me/submissions/75952ca8-61cc-4125-927a-b2c8fa006a93

import Mathlib
import Definitions.Def_NumStochOpt_QuasiFejer_ProjectionMethod

open scoped RealInnerProductSpace
open Filter Topology

set_option autoImplicit false

namespace T2d58517dAux

open NumStochOpt.QuasiFejer

theorem projX_spec {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hXclosed : IsClosed X)
    (hXconv : Convex ℝ X) (hne : X.Nonempty) (y : EuclideanSpace ℝ (Fin n)) :
    projX X y ∈ X ∧ ∀ z ∈ X, ‖y - projX X y‖ ^ 2 ≤ ‖y - z‖ ^ 2 := by
  obtain ⟨v, hv, hveq⟩ :=
    exists_norm_eq_iInf_of_complete_convex hne hXclosed.isComplete hXconv y
  have hex : ∃ x ∈ X, ∀ z ∈ X, ‖y - x‖ ^ 2 ≤ ‖y - z‖ ^ 2 := by
    refine ⟨v, hv, fun z hz => ?_⟩
    have : ‖y - v‖ ≤ ‖y - z‖ := by
      rw [hveq]
      exact ciInf_le ⟨0, Set.forall_mem_range.2 fun _ => norm_nonneg _⟩ (⟨z, hz⟩ : X)
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  unfold projX
  rw [dif_pos hex]
  exact hex.choose_spec

theorem projX_nonexp {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hXclosed : IsClosed X)
    (hXconv : Convex ℝ X) (y z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ X) :
    ‖projX X y - z‖ ≤ ‖y - z‖ := by
  obtain ⟨hp, hmin⟩ := projX_spec X hXclosed hXconv ⟨z, hz⟩ y
  set p := projX X y
  have hinf : ‖y - p‖ = ⨅ w : X, ‖y - w‖ := by
    haveI : Nonempty X := ⟨⟨z, hz⟩⟩
    apply le_antisymm
    · apply le_ciInf
      intro w
      have h := hmin w w.2
      nlinarith [norm_nonneg (y - p), norm_nonneg (y - (w : EuclideanSpace ℝ (Fin n)))]
    · exact ciInf_le ⟨0, Set.forall_mem_range.2 fun _ => norm_nonneg _⟩ (⟨p, hp⟩ : X)
  have hvi := (norm_eq_iInf_iff_real_inner_le_zero hXconv hp).1 hinf z hz
  have h1 : y - z = (y - p) + (p - z) := by abel
  have h2 : ‖y - z‖ ^ 2 = ‖y - p‖ ^ 2 + 2 * ⟪y - p, p - z⟫ + ‖p - z‖ ^ 2 := by
    rw [h1]; exact norm_add_sq_real _ _
  have h3 : ⟪y - p, p - z⟫ = -⟪y - p, z - p⟫ := by
    rw [← inner_neg_right, neg_sub]
  have h4 : ‖p - z‖ ^ 2 ≤ ‖y - z‖ ^ 2 := by nlinarith [sq_nonneg ‖y - p‖]
  nlinarith [norm_nonneg (p - z), norm_nonneg (y - z)]

/-- Abstract descent lemma for a nonnegative real sequence. -/
theorem seq_lemma (a ρ : ℕ → ℝ) (ε ε' δ : ℝ) (N : ℕ) (hδ : 0 < δ)
    (ha0 : ∀ s, 0 ≤ a s) (hρnn : ∀ s, 0 ≤ ρ s)
    (hρsum : Tendsto (fun N => ∑ s ∈ Finset.range N, ρ s) atTop atTop)
    (hdec : ∀ s, N ≤ s → ε ≤ a s → a (s + 1) ≤ a s - ρ s * δ)
    (hsmall : ∀ s, N ≤ s → a s < ε → a (s + 1) ≤ ε') :
    ∀ᶠ s in atTop, a s ≤ max ε ε' := by
  have hfirst : ∃ M, N ≤ M ∧ a M < ε := by
    by_contra hcon
    push_neg at hcon
    have hind : ∀ k, a (N + k) + δ * ∑ s ∈ Finset.range (N + k), ρ s ≤
        a N + δ * ∑ s ∈ Finset.range N, ρ s := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have h1 := hdec (N + k) (by omega) (hcon (N + k) (by omega))
        rw [← add_assoc, Finset.sum_range_succ]
        nlinarith
    have hev := (tendsto_atTop.1 hρsum) ((a N + δ * ∑ s ∈ Finset.range N, ρ s) / δ + 1)
    obtain ⟨K, hK⟩ := eventually_atTop.1 hev
    have h1 := hind K
    have h2 := hK (N + K) (by omega)
    have h3 := ha0 (N + K)
    have h4 : δ * ((a N + δ * ∑ s ∈ Finset.range N, ρ s) / δ + 1) ≤
        δ * ∑ s ∈ Finset.range (N + K), ρ s := mul_le_mul_of_nonneg_left h2 hδ.le
    rw [mul_add, mul_div_cancel₀ _ hδ.ne'] at h4
    linarith
  obtain ⟨M, hNM, hM⟩ := hfirst
  have hall : ∀ k, a (M + k) ≤ max ε ε' := by
    intro k
    induction k with
    | zero => simp only [Nat.add_zero]; exact le_max_of_le_left hM.le
    | succ k ih =>
      rw [← add_assoc]
      by_cases hk : a (M + k) < ε
      · exact le_max_of_le_right (hsmall (M + k) (by omega) hk)
      · push_neg at hk
        have h1 := hdec (M + k) (by omega) hk
        have h2 : 0 ≤ ρ (M + k) * δ := mul_nonneg (hρnn _) hδ.le
        linarith
  refine eventually_atTop.2 ⟨M, fun s hs => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hs
  exact hall k

/-- A positive gap of `f` away from its sublevel set on a compact set. -/
theorem gap_lemma {n : ℕ} (X S : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hX : IsCompact X) (hf : Continuous f) (m : ℝ)
    (hS : ∀ y ∈ X, f y ≤ m → y ∈ S) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ y ∈ X, ε ≤ Metric.infDist y S ^ 2 → m + δ ≤ f y := by
  set K := X ∩ {y | ε ≤ Metric.infDist y S ^ 2} with hKdef
  have hK : IsCompact K :=
    hX.inter_right (isClosed_le continuous_const ((Metric.continuous_infDist_pt S).pow 2))
  by_cases hKne : K.Nonempty
  · obtain ⟨q, hqK, hqmin⟩ := hK.exists_isMinOn hKne hf.continuousOn
    refine ⟨f q - m, ?_, fun y hy hyε => ?_⟩
    · by_contra hneg
      push_neg at hneg
      have hqS : q ∈ S := hS q hqK.1 (by linarith)
      have h0 : Metric.infDist q S = 0 := Metric.infDist_zero_of_mem hqS
      have := hqK.2
      simp only [Set.mem_setOf_eq, h0] at this
      norm_num at this
      linarith
    · have := hqmin (show y ∈ K from ⟨hy, hyε⟩)
      simp only [Set.mem_setOf_eq] at this
      linarith
  · refine ⟨1, one_pos, fun y hy hyε => ?_⟩
    exact absurd ⟨y, hy, hyε⟩ hKne

end T2d58517dAux

open NumStochOpt.QuasiFejer RealInnerProductSpace Filter Topology in
theorem solution {n : ℕ}
    (F : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (X : Set (EuclideanSpace ℝ (Fin n)))
    (x g : ℕ → EuclideanSpace ℝ (Fin n)) (ρ : ℕ → ℝ) (C : ℝ)
    (hFconv : ∀ s, ConvexOn ℝ Set.univ (F s)) (hFcont : ∀ s, Continuous (F s))
    (hfconv : ConvexOn ℝ Set.univ f) (hfcont : Continuous f)
    (hXconv : Convex ℝ X) (hXcpt : IsCompact X) (hXne : X.Nonempty)
    (hunif : TendstoUniformlyOn F f atTop X)
    (hsub : ∀ s y, F s (x s) + ⟪g s, y - x s⟫ ≤ F s y)
    (hbound : ∀ s, ‖g s‖ ≤ C)
    (hrec : ∀ s, x (s + 1) = NumStochOpt.QuasiFejer.projX X (x s - ρ s • g s))
    (hρnn : ∀ s, 0 ≤ ρ s) (hρ0 : Tendsto ρ atTop (𝓝 0))
    (hρsum : Tendsto (fun N => ∑ s ∈ Finset.range N, ρ s) atTop atTop) :
    Tendsto (fun s => F s (x s)) atTop (𝓝 (sInf (f '' X))) := by
  have hXcl : IsClosed X := hXcpt.isClosed
  obtain ⟨x0, hx0X, hx0min⟩ := hXcpt.exists_isMinOn hXne hfcont.continuousOn
  have hx0 : ∀ y ∈ X, f x0 ≤ f y := fun y hy => hx0min hy
  have hInf : sInf (f '' X) = f x0 := by
    apply IsLeast.csInf_eq
    refine ⟨Set.mem_image_of_mem f hx0X, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hx0 y hy
  rw [hInf]
  obtain ⟨S, hSdef⟩ : ∃ S : Set (EuclideanSpace ℝ (Fin n)), S = X ∩ {y | f y ≤ f x0} :=
    ⟨_, rfl⟩
  have hScpt : IsCompact S := by
    rw [hSdef]; exact hXcpt.inter_right (isClosed_le hfcont continuous_const)
  have hSne : S.Nonempty := ⟨x0, by rw [hSdef]; exact ⟨hx0X, show f x0 ≤ f x0 from le_refl _⟩⟩
  have hSmem : ∀ y ∈ X, f y ≤ f x0 → y ∈ S := fun y hy hle => by rw [hSdef]; exact ⟨hy, hle⟩
  have hSX : ∀ p ∈ S, p ∈ X ∧ f p ≤ f x0 := fun p hp => by rw [hSdef] at hp; exact hp
  have hxX : ∀ s, 1 ≤ s → x s ∈ X := by
    intro s hs
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hs
    rw [add_comm, hrec k]
    exact (T2d58517dAux.projX_spec X hXcl hXconv hXne _).1
  have hC : 0 ≤ C := (norm_nonneg _).trans (hbound 0)
  -- one-step recursion
  have hstep : ∀ s, ∀ p ∈ S, Metric.infDist (x s) S = dist (x s) p →
      Metric.infDist (x (s + 1)) S ^ 2 ≤
        Metric.infDist (x s) S ^ 2 + 2 * ρ s * (F s p - F s (x s)) + ρ s ^ 2 * C ^ 2 := by
    intro s p hp hdp
    have hpX := (hSX p hp).1
    have hy := T2d58517dAux.projX_nonexp X hXcl hXconv (x s - ρ s • g s) p hpX
    rw [← hrec] at hy
    have hd : Metric.infDist (x (s + 1)) S ≤ ‖x (s + 1) - p‖ := by
      rw [← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem hp
    have hsq : Metric.infDist (x (s + 1)) S ^ 2 ≤ ‖x s - ρ s • g s - p‖ ^ 2 :=
      pow_le_pow_left₀ Metric.infDist_nonneg (hd.trans hy) 2
    have hexp : ‖x s - ρ s • g s - p‖ ^ 2
        = ‖p - x s‖ ^ 2 + 2 * ρ s * ⟪g s, p - x s⟫ + ρ s ^ 2 * ‖g s‖ ^ 2 := by
      have e : x s - ρ s • g s - p = -(p - x s) - ρ s • g s := by abel
      rw [e, norm_sub_sq_real, norm_neg, inner_neg_left, real_inner_smul_right, norm_smul,
        mul_pow, Real.norm_eq_abs, sq_abs, real_inner_comm (g s) (p - x s)]
      ring
    have hpx : ‖p - x s‖ = Metric.infDist (x s) S := by
      rw [← dist_eq_norm, dist_comm, hdp]
    rw [hpx] at hexp
    have hsp := hsub s p
    have hg : ‖g s‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hbound s) 2
    have h1 : ρ s ^ 2 * ‖g s‖ ^ 2 ≤ ρ s ^ 2 * C ^ 2 :=
      mul_le_mul_of_nonneg_left hg (sq_nonneg _)
    have h2 : 2 * ρ s * ⟪g s, p - x s⟫ ≤ 2 * ρ s * (F s p - F s (x s)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith [hρnn s])
    linarith
  -- distance to S tends to zero
  have hdist : ∀ ε > 0, ∀ᶠ s in atTop, Metric.infDist (x s) S ^ 2 ≤ max ε (2 * ε) := by
    intro ε hε
    obtain ⟨δ, hδ, hgap⟩ := T2d58517dAux.gap_lemma X S f hXcpt hfcont (f x0) hSmem ε hε
    have hu := (Metric.tendstoUniformlyOn_iff.1 hunif) (δ / 4) (by linarith)
    have hr1 : ∀ᶠ s in atTop, ρ s * C ^ 2 < δ / 2 := by
      have := hρ0.mul_const (C ^ 2)
      rw [zero_mul] at this
      exact this.eventually (gt_mem_nhds (by linarith))
    have hr2 : ∀ᶠ s in atTop, ρ s * (2 * δ) < ε := by
      have := hρ0.mul_const (2 * δ)
      rw [zero_mul] at this
      exact this.eventually (gt_mem_nhds hε)
    obtain ⟨N1, hN1⟩ := eventually_atTop.1 (hu.and (hr1.and hr2))
    refine T2d58517dAux.seq_lemma (fun s => Metric.infDist (x s) S ^ 2) ρ ε (2 * ε) (δ / 2)
      (N1 + 1) (by linarith) (fun s => sq_nonneg _) hρnn hρsum ?_ ?_
    · intro s hs hεs
      obtain ⟨hU, hρC, _⟩ := hN1 s (by omega)
      obtain ⟨p, hp, hdp⟩ := hScpt.exists_infDist_eq_dist hSne (x s)
      have hxs := hxX s (by omega)
      obtain ⟨hpX, hfp⟩ := hSX p hp
      have hfx := hgap (x s) hxs hεs
      have e1 := hU p hpX
      have e2 := hU (x s) hxs
      rw [Real.dist_eq, abs_lt] at e1 e2
      have hFd : F s p - F s (x s) ≤ -(δ / 2) := by linarith
      have hrs := hstep s p hp hdp
      have h1 : 2 * ρ s * (F s p - F s (x s)) ≤ 2 * ρ s * (-(δ / 2)) :=
        mul_le_mul_of_nonneg_left hFd (by linarith [hρnn s])
      have h2 : ρ s * (ρ s * C ^ 2) ≤ ρ s * (δ / 2) :=
        mul_le_mul_of_nonneg_left hρC.le (hρnn s)
      have h3 : ρ s ^ 2 * C ^ 2 = ρ s * (ρ s * C ^ 2) := by ring
      show Metric.infDist (x (s + 1)) S ^ 2 ≤ Metric.infDist (x s) S ^ 2 - ρ s * (δ / 2)
      nlinarith
    · intro s hs hεs
      obtain ⟨hU, hρC, hρε⟩ := hN1 s (by omega)
      obtain ⟨p, hp, hdp⟩ := hScpt.exists_infDist_eq_dist hSne (x s)
      have hxs := hxX s (by omega)
      obtain ⟨hpX, hfp⟩ := hSX p hp
      have hfx := hx0 (x s) hxs
      have e1 := hU p hpX
      have e2 := hU (x s) hxs
      rw [Real.dist_eq, abs_lt] at e1 e2
      have hFd : F s p - F s (x s) ≤ δ / 2 := by linarith
      have hrs := hstep s p hp hdp
      have h1 : 2 * ρ s * (F s p - F s (x s)) ≤ 2 * ρ s * (δ / 2) :=
        mul_le_mul_of_nonneg_left hFd (by linarith [hρnn s])
      have h2 : ρ s * (ρ s * C ^ 2) ≤ ρ s * (δ / 2) :=
        mul_le_mul_of_nonneg_left hρC.le (hρnn s)
      have h3 : ρ s ^ 2 * C ^ 2 = ρ s * (ρ s * C ^ 2) := by ring
      show Metric.infDist (x (s + 1)) S ^ 2 ≤ 2 * ε
      nlinarith
  -- conclude
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ1, hδ1, hUC⟩ := Metric.uniformContinuousOn_iff.1
    (hXcpt.uniformContinuousOn_of_continuous hfcont.continuousOn) (ε / 2) (by linarith)
  have hu := (Metric.tendstoUniformlyOn_iff.1 hunif) (ε / 2) (by linarith)
  have hd := hdist (δ1 ^ 2 / 4) (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hu.and hd)
  refine ⟨N + 1, fun s hs => ?_⟩
  obtain ⟨hU, hD⟩ := hN s (by omega)
  have hxs := hxX s (by omega)
  obtain ⟨p, hp, hdp⟩ := hScpt.exists_infDist_eq_dist hSne (x s)
  obtain ⟨hpX, hfp⟩ := hSX p hp
  have hmax : max (δ1 ^ 2 / 4) (2 * (δ1 ^ 2 / 4)) = 2 * (δ1 ^ 2 / 4) :=
    max_eq_right (by nlinarith [sq_nonneg δ1])
  rw [hmax] at hD
  have hlt : dist (x s) p < δ1 := by
    rw [← hdp]
    by_contra hcon
    push_neg at hcon
    nlinarith [Metric.infDist_nonneg (x := x s) (s := S)]
  have h1 := hUC (x s) hxs p hpX hlt
  have h2 := hU (x s) hxs
  have h3 := hx0 p hpX
  have h4 := hx0 (x s) hxs
  rw [Real.dist_eq, abs_lt] at h1 h2
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith
