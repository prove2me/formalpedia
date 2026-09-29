-- Prove2me | solution 1 for NonsmoothNewton.Global.newton_global_convergence
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:03:09.359556+00:00
-- url     : https://prove2.me/submissions/57a37083-c248-46db-ba79-e18e70eab204

import Mathlib
import Definitions.Def_NonsmoothNewton_Global_dirDeriv
import Definitions.Def_NonsmoothNewton_Global_clarkeJac
import Definitions.Def_NonsmoothNewton_Global_SemismoothAt
import Definitions.Def_NonsmoothNewton_Global_IsNewtonRun



namespace NonsmoothNewton.Global

open Filter Topology

theorem ngc_core {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (x0 : EuclideanSpace ℝ (Fin n)) (r β γ δ : ℝ)
    (hF : LocallyLipschitz F)
    (hinv : ∀ x ∈ Metric.closedBall x0 r, ∀ V ∈ clarkeJac F x,
      ∃ W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n), V.comp W = 1 ∧ W.comp V = 1 ∧ ‖W‖ ≤ β)
    (hγ : ∀ x ∈ Metric.closedBall x0 r, ∀ y ∈ Metric.closedBall x0 r, ∀ V ∈ clarkeJac F x,
      ‖V (y - x) - dirDeriv F x (y - x)‖ ≤ γ * ‖y - x‖)
    (hδ : ∀ x ∈ Metric.closedBall x0 r, ∀ y ∈ Metric.closedBall x0 r,
      ‖F y - F x - dirDeriv F x (y - x)‖ ≤ δ * ‖y - x‖)
    (hα : β * (γ + δ) < 1)
    (hr0 : 0 ≤ r) (hr : β * ‖F x0‖ ≤ r * (1 - β * (γ + δ)))
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (V : ℕ → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hx0 : x 0 = x0) (hrun : IsNewtonRun F x V) :
    (∀ k, x k ∈ Metric.closedBall x0 r) ∧ (∀ k, IsUnit (V k)) ∧
      ∃ xstar ∈ Metric.closedBall x0 r, F xstar = 0 ∧
        (∀ y ∈ Metric.closedBall x0 r, F y = 0 → y = xstar) ∧
        Tendsto x atTop (𝓝 xstar) ∧
        ∀ k, ‖x (k + 1) - xstar‖ ≤
          (β * (γ + δ)) / (1 - β * (γ + δ)) * ‖x (k + 1) - x k‖ := by
  set B := Metric.closedBall x0 r with hB
  set α := β * (γ + δ) with hαdef
  have hx0mem : x0 ∈ B := Metric.mem_closedBall_self hr0
  have hV0 : V 0 ∈ clarkeJac F x0 := hx0 ▸ (hrun 0).1
  have hβ : 0 ≤ β := by
    obtain ⟨W, -, -, hW⟩ := hinv x0 hx0mem (V 0) hV0
    exact (norm_nonneg _).trans hW
  have hinvb : ∀ z ∈ B, ∀ U ∈ clarkeJac F z, ∀ u, ‖u‖ ≤ β * ‖U u‖ := by
    intro z hz U hU u
    obtain ⟨W, -, h2, hW⟩ := hinv z hz U hU
    have : u = W (U u) := by
      have := congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) => L u) h2
      simpa using this.symm
    calc ‖u‖ = ‖W (U u)‖ := congrArg _ this
      _ ≤ ‖W‖ * ‖U u‖ := W.le_opNorm _
      _ ≤ β * ‖U u‖ := mul_le_mul_of_nonneg_right hW (norm_nonneg _)
  have hFb : ∀ a ∈ B, ∀ b ∈ B, ∀ U ∈ clarkeJac F a, U (b - a) = -F a →
      ‖F b‖ ≤ (γ + δ) * ‖b - a‖ := by
    intro a ha b hb U hU hN
    have e : F b = (F b - F a - dirDeriv F a (b - a)) - (U (b - a) - dirDeriv F a (b - a)) := by
      rw [hN]; abel
    rw [e]
    calc _ ≤ ‖F b - F a - dirDeriv F a (b - a)‖ + ‖U (b - a) - dirDeriv F a (b - a)‖ := norm_sub_le _ _
      _ ≤ δ * ‖b - a‖ + γ * ‖b - a‖ := add_le_add (hδ a ha b hb) (hγ a ha b hb U hU)
      _ = _ := by ring
  have hcon : ∀ a ∈ B, ∀ b, ∀ y ∈ B, F y = 0 → ∀ U ∈ clarkeJac F a, U (b - a) = -F a →
      ‖b - y‖ ≤ α * ‖a - y‖ := by
    intro a ha b y hy hFy U hU hN
    have e : U (b - y) = (F y - F a - dirDeriv F a (y - a)) - (U (y - a) - dirDeriv F a (y - a)) := by
      have : b - y = (b - a) - (y - a) := by abel
      rw [this, map_sub, hN, hFy]; abel
    have h1 : ‖U (b - y)‖ ≤ (γ + δ) * ‖a - y‖ := by
      rw [e, norm_sub_rev a y]
      calc _ ≤ ‖F y - F a - dirDeriv F a (y - a)‖ + ‖U (y - a) - dirDeriv F a (y - a)‖ := norm_sub_le _ _
        _ ≤ δ * ‖y - a‖ + γ * ‖y - a‖ := add_le_add (hδ a ha y hy) (hγ a ha y hy U hU)
        _ = _ := by ring
    calc ‖b - y‖ ≤ β * ‖U (b - y)‖ := hinvb a ha U hU _
      _ ≤ β * ((γ + δ) * ‖a - y‖) := mul_le_mul_of_nonneg_left h1 hβ
      _ = _ := by ring
  -- one step
  have hstep : ∀ k, x k ∈ B → x (k + 1) ∈ B →
      ‖x (k + 2) - x (k + 1)‖ ≤ α * ‖x (k + 1) - x k‖ := by
    intro k hk hk1
    have h1 := hinvb _ hk1 _ (hrun (k + 1)).1 (x (k + 2) - x (k + 1))
    rw [(hrun (k + 1)).2, norm_neg] at h1
    have h2 := hFb _ hk _ hk1 _ (hrun k).1 (hrun k).2
    calc _ ≤ β * ‖F (x (k + 1))‖ := h1
      _ ≤ β * ((γ + δ) * ‖x (k + 1) - x k‖) := mul_le_mul_of_nonneg_left h2 hβ
      _ = _ := by ring
  -- key facts
  obtain ⟨hball, a, C, ha1, hgeo, hpow⟩ : (∀ k, x k ∈ B) ∧ ∃ a C : ℝ, a < 1 ∧
      (∀ k, ‖x (k + 1) - x k‖ ≤ C * a ^ k) ∧
      (∀ k m, ‖x (k + m + 1) - x (k + m)‖ ≤ α ^ m * ‖x (k + 1) - x k‖) := by
    rcases le_or_gt 0 α with hα0 | hα0
    · have Q : ∀ k, x k ∈ B ∧ x (k + 1) ∈ B ∧ ‖x (k + 1) - x0‖ ≤ r * (1 - α ^ (k + 1)) ∧
          ‖x (k + 1) - x k‖ ≤ r * (1 - α) * α ^ k := by
        intro k
        induction k with
        | zero =>
          have h1 := hinvb _ hx0mem _ hV0 (x 1 - x 0)
          rw [(hrun 0).2, norm_neg] at h1
          have hd : ‖x 1 - x 0‖ ≤ r * (1 - α) := h1.trans (by rw [hx0]; exact hr)
          refine ⟨hx0 ▸ hx0mem, ?_, ?_, ?_⟩
          · rw [hB, Metric.mem_closedBall, dist_eq_norm, ← hx0]
            nlinarith
          · rw [← hx0]; simpa using hd
          · simpa using hd
        | succ k ih =>
          obtain ⟨hk, hk1, hdist, hd⟩ := ih
          have hs := hstep k hk hk1
          have hd' : ‖x (k + 2) - x (k + 1)‖ ≤ r * (1 - α) * α ^ (k + 1) := by
            calc _ ≤ α * ‖x (k + 1) - x k‖ := hs
              _ ≤ α * (r * (1 - α) * α ^ k) := mul_le_mul_of_nonneg_left hd hα0
              _ = _ := by ring
          have hdist' : ‖x (k + 2) - x0‖ ≤ r * (1 - α ^ (k + 2)) := by
            calc ‖x (k + 2) - x0‖ = ‖(x (k + 2) - x (k + 1)) + (x (k + 1) - x0)‖ := by
                  congr 1; abel
              _ ≤ ‖x (k + 2) - x (k + 1)‖ + ‖x (k + 1) - x0‖ := norm_add_le _ _
              _ ≤ r * (1 - α) * α ^ (k + 1) + r * (1 - α ^ (k + 1)) := add_le_add hd' hdist
              _ = _ := by ring
          refine ⟨hk1, ?_, hdist', hd'⟩
          rw [hB, Metric.mem_closedBall, dist_eq_norm]
          have : 0 ≤ α ^ (k + 2) := pow_nonneg hα0 _
          nlinarith
      refine ⟨fun k => (Q k).1, α, r * (1 - α), hα, fun k => (Q k).2.2.2, ?_⟩
      intro k m
      induction m with
      | zero => simp
      | succ m ih =>
        have hs := hstep (k + m) (Q _).1 (Q _).2.1
        calc ‖x (k + (m + 1) + 1) - x (k + (m + 1))‖ = ‖x (k + m + 2) - x (k + m + 1)‖ := by
              ring_nf
          _ ≤ α * ‖x (k + m + 1) - x (k + m)‖ := hs
          _ ≤ α * (α ^ m * ‖x (k + 1) - x k‖) := mul_le_mul_of_nonneg_left ih hα0
          _ = _ := by ring
    · -- degenerate case: F x0 = 0 and the run is constant
      have hF0 : F x0 = 0 := by
        by_contra hne
        have hpos : 0 < ‖F x0‖ := norm_pos_iff.mpr hne
        have hrpos : 0 < r := by
          rcases lt_or_eq_of_le hr0 with h | h
          · exact h
          · exfalso
            subst h
            have hβ0 : β = 0 := by
              have : β * ‖F x0‖ ≤ 0 := by simpa using hr
              nlinarith
            have := hinvb x0 hx0mem _ hV0 (F x0)
            rw [hβ0] at this
            linarith
        set y := x0 + (r / ‖F x0‖) • F x0 with hy
        have hyx : y - x0 = (r / ‖F x0‖) • F x0 := by rw [hy]; abel
        have hny : ‖y - x0‖ = r := by
          rw [hyx, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hrpos hpos)]
          field_simp
        have hyB : y ∈ B := by
          rw [hB, Metric.mem_closedBall, dist_eq_norm, hny]
        have h1 := hδ x0 hx0mem y hyB
        have h2 := hγ x0 hx0mem y hyB _ hV0
        rw [hny] at h1 h2
        have hδ0 : 0 ≤ δ := by
          by_contra h; push Not at h
          have := norm_nonneg (F y - F x0 - dirDeriv F x0 (y - x0))
          nlinarith
        have hγ0 : 0 ≤ γ := by
          by_contra h; push Not at h
          have := norm_nonneg ((V 0) (y - x0) - dirDeriv F x0 (y - x0))
          nlinarith
        have : 0 ≤ α := mul_nonneg hβ (add_nonneg hγ0 hδ0)
        linarith
      have hconst : ∀ k, x k = x0 := by
        intro k
        induction k with
        | zero => exact hx0
        | succ k ih =>
          have h1 := hinvb _ hx0mem _ (ih ▸ (hrun k).1) (x (k + 1) - x k)
          rw [(hrun k).2, norm_neg, ih, hF0, norm_zero, mul_zero] at h1
          have := norm_le_zero_iff.mp h1
          rw [sub_eq_zero] at this
          rw [this]
      refine ⟨fun k => (hconst k).symm ▸ hx0mem, 0, 0, by norm_num, ?_, ?_⟩
      · intro k; simp [hconst]
      · intro k m; simp [hconst]
  have hcauchy : CauchySeq x := by
    refine cauchySeq_of_le_geometric a C ha1 (fun k => ?_)
    rw [dist_comm, dist_eq_norm]; exact hgeo k
  obtain ⟨xstar, hlim⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hxsB : xstar ∈ B := Metric.isClosed_closedBall.mem_of_tendsto hlim (Eventually.of_forall hball)
  have hlim1 : Tendsto (fun k => x (k + 1)) atTop (𝓝 xstar) := hlim.comp (tendsto_add_atTop_nat 1)
  have hd0 : Tendsto (fun k => x (k + 1) - x k) atTop (𝓝 0) := by
    have := hlim1.sub hlim
    simpa using this
  have hFxs : F xstar = 0 := by
    have h1 : Tendsto (fun k => F (x (k + 1))) atTop (𝓝 (F xstar)) :=
      (hF.continuous.tendsto xstar).comp hlim1
    have h2 : Tendsto (fun k => F (x (k + 1))) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun k => hFb _ (hball k) _ (hball (k + 1)) _ (hrun k).1 (hrun k).2) ?_
      have := (hd0.norm).const_mul (γ + δ)
      simpa using this
    exact tendsto_nhds_unique h1 h2
  refine ⟨hball, ?_, xstar, hxsB, hFxs, ?_, hlim, ?_⟩
  · intro k
    obtain ⟨W, h1, h2, -⟩ := hinv _ (hball k) _ (hrun k).1
    exact ⟨⟨V k, W, h1, h2⟩, rfl⟩
  · intro y hy hFy
    set a' := max α 0
    have hc : ∀ k, ‖x (k + 1) - y‖ ≤ a' * ‖x k - y‖ := fun k =>
      (hcon _ (hball k) _ y hy hFy _ (hrun k).1 (hrun k).2).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    have hk : ∀ k, ‖x k - y‖ ≤ a' ^ k * ‖x 0 - y‖ := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        calc _ ≤ a' * ‖x k - y‖ := hc k
          _ ≤ a' * (a' ^ k * ‖x 0 - y‖) := mul_le_mul_of_nonneg_left ih (le_max_right _ _)
          _ = _ := by ring
    have hty : Tendsto x atTop (𝓝 y) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun k => norm_nonneg _) hk ?_
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (le_max_right α 0)
        (max_lt hα one_pos)).mul_const ‖x 0 - y‖
      simpa using this
    exact tendsto_nhds_unique hty hlim
  · intro k
    have hu : ∀ m, dist (x (m + (k + 1))) (x (m + 1 + (k + 1))) ≤ (α * ‖x (k + 1) - x k‖) * α ^ m := by
      intro m
      rw [dist_comm, dist_eq_norm]
      have := hpow k (m + 1)
      calc ‖x (m + 1 + (k + 1)) - x (m + (k + 1))‖ = ‖x (k + (m + 1) + 1) - x (k + (m + 1))‖ := by
            ring_nf
        _ ≤ _ := this
        _ = _ := by ring
    have hl : Tendsto (fun m => x (m + (k + 1))) atTop (𝓝 xstar) :=
      (tendsto_add_atTop_iff_nat (k + 1)).mpr hlim
    have := dist_le_of_le_geometric_of_tendsto α _ hα hu hl 0
    simp only [zero_add, pow_zero, mul_one, dist_eq_norm] at this
    calc _ ≤ _ := this
      _ = _ := by ring

end NonsmoothNewton.Global

open NonsmoothNewton.Global
open NonsmoothNewton.Global Filter Topology

theorem solution {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (x0 : EuclideanSpace ℝ (Fin n)) (r β γ δ : ℝ)
    (hF : LocallyLipschitz F)
    (hsemi : ∀ x ∈ Metric.closedBall x0 r, SemismoothAt F x)
    (hinv : ∀ x ∈ Metric.closedBall x0 r, ∀ V ∈ clarkeJac F x,
      ∃ W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n), V.comp W = 1 ∧ W.comp V = 1 ∧ ‖W‖ ≤ β)
    (hγ : ∀ x ∈ Metric.closedBall x0 r, ∀ y ∈ Metric.closedBall x0 r, ∀ V ∈ clarkeJac F x,
      ‖V (y - x) - dirDeriv F x (y - x)‖ ≤ γ * ‖y - x‖)
    (hδ : ∀ x ∈ Metric.closedBall x0 r, ∀ y ∈ Metric.closedBall x0 r,
      ‖F y - F x - dirDeriv F x (y - x)‖ ≤ δ * ‖y - x‖)
    (hα : β * (γ + δ) < 1)
    (hr0 : 0 ≤ r) (hr : β * ‖F x0‖ ≤ r * (1 - β * (γ + δ)))
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (V : ℕ → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hx0 : x 0 = x0) (hrun : IsNewtonRun F x V) :
    (∀ k, x k ∈ Metric.closedBall x0 r) ∧ (∀ k, IsUnit (V k)) ∧
      ∃ xstar ∈ Metric.closedBall x0 r, F xstar = 0 ∧
        (∀ y ∈ Metric.closedBall x0 r, F y = 0 → y = xstar) ∧
        Tendsto x atTop (𝓝 xstar) ∧
        ∀ k, ‖x (k + 1) - xstar‖ ≤
          (β * (γ + δ)) / (1 - β * (γ + δ)) * ‖x (k + 1) - x k‖ := by
  exact ngc_core F x0 r β γ δ hF hinv hγ hδ hα hr0 hr x V hx0 hrun
