-- Prove2me | solution 1 for GoldenRatioVI.Explicit.energy_inequality
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:21:59.407968+00:00
-- url     : https://prove2.me/submissions/8aa89450-d165-4762-b5bb-557a8a04d0ce

import Definitions.Def_GoldenRatioVI_Explicit_viProblem
import Definitions.Def_GoldenRatioVI_Explicit_egraalRun

open scoped RealInnerProductSpace
namespace GoldenRatioVI.Explicit

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem run_pos (g : E → EReal) (F : E → E) (ϕ lamBar : ℝ)
    (z zbar : ℕ → E) (lam theta : ℕ → ℝ)
    (h : IsEGRAALRun g F ϕ lamBar z zbar lam theta) :
    ∀ k, 0 < lam k ∧ 0 < theta k := by
  have hp : 0 < ϕ := by linarith [h.one_lt_phi]
  have hr : 0 < rho ϕ := by dsimp [rho]; positivity
  intro k
  induction k with
  | zero => exact ⟨h.lam_zero_pos, by rw [h.theta_zero]; norm_num⟩
  | succ k ih =>
    have hlk : 0 < lam k := ih.1
    have htk : 0 < theta k := ih.2
    have hl : 0 < lam (k+1) := by
      by_cases hf : F (z (k+1)) = F (z k)
      · rw [h.step_of_eq k hf]; exact lt_min (mul_pos hr ih.1) h.lamBar_pos
      · have hz : z (k+1)-z k ≠ 0 := by intro he; exact hf (congrArg F (sub_eq_zero.mp he))
        have hFn : F (z (k+1))-F (z k) ≠ 0 := sub_ne_zero.mpr hf
        rw [h.step_of_ne k hf]
        exact lt_min (lt_min (mul_pos hr ih.1)
          (mul_pos (div_pos (mul_pos hp ih.2) (by positivity))
            (div_pos (sq_pos_of_pos (norm_pos_iff.mpr hz))
              (sq_pos_of_pos (norm_pos_iff.mpr hFn))))) h.lamBar_pos
    exact ⟨hl, by rw [h.theta_succ]; exact mul_pos (div_pos hl ih.1) hp⟩

private theorem run_estimates (g : E → EReal) (F : E → E) (ϕ lamBar : ℝ)
    (z zbar : ℕ → E) (lam theta : ℕ → ℝ)
    (h : IsEGRAALRun g F ϕ lamBar z zbar lam theta) (k : ℕ) :
    theta (k+1) ≤ 1+1/ϕ ∧
      4*(lam (k+1))^2*‖F (z (k+1))-F (z k)‖^2 ≤
        theta (k+1)*theta k*‖z (k+1)-z k‖^2 := by
  have hp : 0 < ϕ := by linarith [h.one_lt_phi]
  have hpos := run_pos g F ϕ lamBar z zbar lam theta h
  have hlk : 0 < lam k := (hpos k).1
  have hln : 0 < lam (k+1) := (hpos (k+1)).1
  have htk : 0 < theta k := (hpos k).2
  have htn : 0 < theta (k+1) := (hpos (k+1)).2
  have hl : lam (k+1) ≤ rho ϕ*lam k := by
    by_cases hf : F (z (k+1)) = F (z k)
    · rw [h.step_of_eq k hf]; exact min_le_left _ _
    · rw [h.step_of_ne k hf]; exact (min_le_left _ _).trans (min_le_left _ _)
  constructor
  · rw [h.theta_succ]
    have hh := mul_le_mul_of_nonneg_right ((div_le_iff₀ (hpos k).1).mpr hl) hp.le
    convert! hh using 1 <;> try dsimp [rho]
    all_goals try field_simp
    all_goals first | rfl | ring
  · by_cases hf : F (z (k+1)) = F (z k)
    · simp only [hf, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, mul_zero]
      positivity
    · have hFn : 0 < ‖F (z (k+1))-F (z k)‖^2 :=
        sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hf))
      have hmid : lam (k+1) ≤ ϕ*theta k/(4*lam k) *
          (‖z (k+1)-z k‖^2/‖F (z (k+1))-F (z k)‖^2) := by
        rw [h.step_of_ne k hf]; exact (min_le_left _ _).trans (min_le_right _ _)
      have hh := mul_le_mul_of_nonneg_right hmid (show 0 ≤ 4*lam (k+1)*‖F (z (k+1))-F (z k)‖^2 by positivity)
      rw [h.theta_succ]
      convert! hh using 1 <;>
        try field_simp [hlk.ne', norm_ne_zero_iff.mpr (sub_ne_zero.mpr hf)]
      all_goals first | rfl | ring

private theorem norm_segment {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b w : E) (t : ℝ) :
    ‖(1-t) • a + t • b - w‖^2 = ‖a-w‖^2 +
      2*t*⟪a-w,b-a⟫ + t^2*‖b-a‖^2 := by
  have he : (1-t) • a+t • b-w = (a-w)+t • (b-a) := by module
  rw [he, norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]
  ring

private theorem scaled_prox {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : E → EReal) (hg : IsProperConvexLSC g) (a : ℝ) (ha : 0 < a) (w b : E)
    (hprox : GoldenRatioVI.Shared.IsProxPoint (fun x => (a:EReal)*g x) w b) :
    g b ≠ ⊤ ∧ ∀ x, g x ≠ ⊤ →
      a*((g b).toReal-(g x).toReal) ≤ ⟪b-w,x-b⟫ := by
  obtain ⟨y, hy⟩ := hg.exists_ne_top
  have gy : ((g y).toReal : EReal) = g y := EReal.coe_toReal hy (hg.ne_bot y)
  have hb : g b ≠ ⊤ := by
    intro ht
    have hh := hprox y
    dsimp only at hh
    rw [ht, ← gy] at hh
    simpa [EReal.coe_mul_top_of_pos ha, ← EReal.coe_mul, ← EReal.coe_add] using hh
  refine ⟨hb, ?_⟩
  have gb : ((g b).toReal : EReal) = g b := EReal.coe_toReal hb (hg.ne_bot b)
  intro x hx
  have gx : ((g x).toReal : EReal) = g x := EReal.coe_toReal hx (hg.ne_bot x)
  by_contra hn
  let D : ℝ := a*((g b).toReal-(g x).toReal)-⟪b-w,x-b⟫
  have hD : 0 < D := by dsimp [D]; linarith
  let S : ℝ := ‖x-b‖^2
  have hS : 0 ≤ S := sq_nonneg _
  let t : ℝ := min 1 (D/(S+1))
  have ht : 0 < t := lt_min zero_lt_one (div_pos hD (by positivity))
  have ht1 : t ≤ 1 := min_le_left _ _
  have htd : t*(S+1) ≤ D := (le_div_iff₀ (by positivity : 0 < S+1)).mp (min_le_right _ _)
  have hc := hg.convex_epigraph
    (show (b,(g b).toReal) ∈ {p:E×ℝ | g p.1 ≤ (p.2:EReal)} by change g b ≤ _; rw [gb])
    (show (x,(g x).toReal) ∈ {p:E×ℝ | g p.1 ≤ (p.2:EReal)} by change g x ≤ _; rw [gx])
    (show 0 ≤ 1-t by linarith) ht.le (by ring : 1-t+t=1)
  change g ((1-t) • b+t • x) ≤ ↑((1-t)*(g b).toReal+t*(g x).toReal) at hc
  have hc' := mul_le_mul_of_nonneg_left hc (EReal.coe_nonneg.mpr ha.le)
  have hadd : (a:EReal)*g ((1-t) • b+t • x) + ((‖(1-t) • b+t • x-w‖^2/2:ℝ):EReal) ≤
      (a:EReal)*↑((1-t)*(g b).toReal+t*(g x).toReal) + ((‖(1-t) • b+t • x-w‖^2/2:ℝ):EReal) := by
    gcongr
  have hm := (hprox ((1-t) • b+t • x)).trans hadd
  dsimp only at hm
  rw [← gb, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_add,
    EReal.coe_le_coe_iff] at hm
  rw [norm_segment] at hm
  simp only [EReal.toReal_coe] at hm
  have hineq : t*D ≤ t^2*S/2 := by dsimp [D,S]; nlinarith [hm]
  have hdle : D ≤ t*S/2 := by nlinarith
  nlinarith


private theorem zbar_identity_local {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (g : E → EReal) (F : E → E) (ϕ lamBar : ℝ)
    (z zbar : ℕ → E) (lam theta : ℕ → ℝ)
    (hrun : IsEGRAALRun g F ϕ lamBar z zbar lam theta) (u : E) (k : ℕ) :
    ‖z (k + 1) - u‖ ^ 2 =
      ϕ / (ϕ - 1) * ‖zbar (k + 1) - u‖ ^ 2 - 1 / (ϕ - 1) * ‖zbar k - u‖ ^ 2
        + 1 / ϕ * ‖z (k + 1) - zbar k‖ ^ 2 := by
  have hp : ϕ ≠ 0 := by linarith [hrun.one_lt_phi]
  have hp1 : ϕ-1 ≠ 0 := by linarith [hrun.one_lt_phi]
  rw [hrun.zbar_succ]
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  simp only [real_inner_comm (zbar k) (z (k+1)), real_inner_comm u (z (k+1)),
    real_inner_comm u (zbar k)]
  field_simp
  <;> ring

end GoldenRatioVI.Explicit
open GoldenRatioVI.Explicit

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (g : E → EReal) (F : E → E) (ϕ lamBar : ℝ)
    (z zbar : ℕ → E) (lam theta : ℕ → ℝ)
    (hg : IsProperConvexLSC g) (hF : IsMonotoneOnDom g F)
    (h : IsEGRAALRun g F ϕ lamBar z zbar lam theta)
    (u : E) (hu : u ∈ dom g) (k : ℕ) (hk : 2 ≤ k) :
    ϕ / (ϕ - 1) * ‖zbar (k + 1) - u‖ ^ 2 + theta k / 2 * ‖z (k + 1) - z k‖ ^ 2
        + 2 * lam k * psi g F u (z k) ≤
      ϕ / (ϕ - 1) * ‖zbar k - u‖ ^ 2 + theta (k - 1) / 2 * ‖z k - z (k - 1)‖ ^ 2
        - theta k * ‖z k - zbar k‖ ^ 2 := by
  have hp : 0 < ϕ := by linarith [h.one_lt_phi]
  have hp1 : ϕ-1 ≠ 0 := by linarith [h.one_lt_phi]
  have hpos := run_pos g F ϕ lamBar z zbar lam theta h
  have hlk : 0 < lam k := (hpos k).1
  have hlp : 0 < lam (k-1) := (hpos (k-1)).1
  have htk : 0 < theta k := (hpos k).2
  have htp : 0 < theta (k-1) := (hpos (k-1)).2
  have hkm : k-1+1=k := by omega
  have hkmm : k-2+1=k-1 := by omega
  have hkm2 : k-2+2=k := by omega
  have hkn : k-1+2=k+1 := by omega
  have proxnow := scaled_prox g hg (lam k) hlk (zbar k-lam k • F (z k)) (z (k+1))
    (by simpa only [hkm,hkn] using h.prox_step (k-1))
  have proxprev := scaled_prox g hg (lam (k-1)) hlp
    (zbar (k-1)-lam (k-1) • F (z (k-1))) (z k)
    (by simpa only [hkmm,hkm2] using h.prox_step (k-2))
  have hprox1 := proxnow.2 u hu
  have hprox2 := mul_le_mul_of_nonneg_left (proxprev.2 (z (k+1)) proxnow.1)
    (div_nonneg hlk.le hlp.le)
  have htdef : theta k = lam k/lam (k-1)*ϕ := by simpa only [hkm] using h.theta_succ (k-1)
  have hbdef : zbar k = (1/ϕ) • ((ϕ-1) • z k+zbar (k-1)) := by
    simpa only [hkm] using h.zbar_succ (k-1)
  have hscale : (lam k/lam (k-1)) • (z k-zbar (k-1)) = theta k • (z k-zbar k) := by
    have hv : ϕ • (z k-zbar k) = z k-zbar (k-1) := by
      rw [smul_sub, hbdef, smul_smul]
      simp only [one_div, mul_inv_cancel₀ hp.ne', one_smul]
      module
    rw [htdef, mul_smul, hv]
  have hprox2' : lam k*((g (z k)).toReal-(g (z (k+1))).toReal) ≤
      theta k*⟪z k-zbar k,z (k+1)-z k⟫ + lam k*⟪F (z (k-1)),z (k+1)-z k⟫ := by
    have hv : (lam k/lam (k-1)) • (z k-(zbar (k-1)-lam (k-1) • F (z (k-1)))) =
        theta k • (z k-zbar k)+lam k • F (z (k-1)) := by
      rw [show z k-(zbar (k-1)-lam (k-1) • F (z (k-1))) =
        (z k-zbar (k-1))+lam (k-1) • F (z (k-1)) by abel,
        smul_add, smul_smul, div_mul_cancel₀ _ hlp.ne', hscale]
    rw [← real_inner_smul_left, hv, inner_add_left, real_inner_smul_left,
      real_inner_smul_left, ← mul_assoc, div_mul_cancel₀ _ hlp.ne'] at hprox2
    exact hprox2
  have hmon := hF (z k) proxprev.1 u hu
  have hsum : lam k*psi g F u (z k) ≤
      ⟪z (k+1)-zbar k,u-z (k+1)⟫ + theta k*⟪z k-zbar k,z (k+1)-z k⟫ +
        lam k*⟪F (z k)-F (z (k-1)),z k-z (k+1)⟫ := by
    have hm := mul_nonneg hlk.le hmon
    simp only [sub_sub, inner_add_left, inner_sub_left, inner_sub_right, real_inner_smul_left, psi]
      at hprox1 hprox2' hm ⊢
    nlinarith
  have hest := run_estimates g F ϕ lamBar z zbar lam theta h (k-1)
  simp only [hkm] at hest
  have hyoung : 2*lam k*⟪F (z k)-F (z (k-1)),z k-z (k+1)⟫ ≤
      theta k/2*‖z (k+1)-z k‖^2 + theta (k-1)/2*‖z k-z (k-1)‖^2 := by
    have hs := sq_nonneg ‖(2*lam k) • (F (z k)-F (z (k-1))) + theta k • (z (k+1)-z k)‖
    rw [norm_add_sq_real, real_inner_smul_left, real_inner_smul_right,
      norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow,
      sq_abs, sq_abs] at hs
    have hsgn : ⟪F (z k)-F (z (k-1)),z k-z (k+1)⟫ =
        -⟪F (z k)-F (z (k-1)),z (k+1)-z k⟫ := by
      rw [← neg_sub (z (k+1)), inner_neg_right]
    rw [hsgn]
    nlinarith [hest.2]
  have hc1 : 2*⟪z (k+1)-zbar k,u-z (k+1)⟫ =
      ‖zbar k-u‖^2-‖z (k+1)-u‖^2-‖z (k+1)-zbar k‖^2 := by
    simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right]
    simp only [real_inner_comm u (z (k+1)), real_inner_comm u (zbar k),
      real_inner_comm (zbar k) (z (k+1))]
    ring
  have hc2 : 2*⟪z k-zbar k,z (k+1)-z k⟫ =
      ‖z (k+1)-zbar k‖^2-‖z (k+1)-z k‖^2-‖z k-zbar k‖^2 := by
    simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right]
    simp only [real_inner_comm (zbar k) (z (k+1)), real_inner_comm (z k) (z (k+1)),
      real_inner_comm (zbar k) (z k)]
    ring
  have hz := zbar_identity_local g F ϕ lamBar z zbar lam theta h u k
  have hcoeff : ϕ/(ϕ-1) = 1+1/(ϕ-1) := by field_simp; ring
  have hneg := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hest.1) (sq_nonneg ‖z (k+1)-zbar k‖)
  nlinarith

