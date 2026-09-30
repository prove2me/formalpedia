-- Prove2me | solution 1 for GoldenRatioVI.Explicit.egraal_converges
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:44:14.789987+00:00
-- url     : https://prove2.me/submissions/a4f88f17-7c54-43e6-9722-3fdab021cbf9

import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Tactic
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Sequences
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

private theorem energy_local {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
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


private theorem steps_local {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (g : E → EReal) (F : E → E) (ϕ lamBar : ℝ)
    (z zbar : ℕ → E) (lam theta : ℕ → ℝ)
    (hg : IsProperConvexLSC g) (hL : IsLipschitzOnBoundedDom g F)
    (h : IsEGRAALRun g F ϕ lamBar z zbar lam theta)
    (hz : Bornology.IsBounded (Set.range z)) :
    (∃ C : ℝ, ∀ k, lam k ≤ C) ∧ (∃ c : ℝ, 0 < c ∧ ∀ k, c ≤ lam k) ∧
    (∃ C : ℝ, ∀ k, theta k ≤ C) ∧ (∃ c : ℝ, 0 < c ∧ ∀ k, c ≤ theta k) := by
  have hp : 0 < ϕ := by linarith [h.one_lt_phi]
  have hp2 : 0 < ϕ^2 := sq_pos_of_pos hp
  have hpos := run_pos g F ϕ lamBar z zbar lam theta h
  have hr : 1 ≤ rho ϕ := by
    have hquad : ϕ^2 ≤ ϕ+1 := by
      have hm := mul_nonneg (sub_nonneg.mpr h.phi_le_goldenRatio)
        (show 0 ≤ Real.goldenRatio+ϕ-1 by linarith [Real.one_lt_goldenRatio])
      nlinarith [Real.goldenRatio_sq]
    have hid : rho ϕ = (ϕ+1)/ϕ^2 := by dsimp [rho]; field_simp <;> ring
    rw [hid]
    exact (le_div_iff₀ hp2).mpr (by simpa using hquad)
  let C : ℝ := max (lam 0) lamBar
  have hC : 0 < C := lt_of_lt_of_le h.lam_zero_pos (le_max_left _ _)
  have hupper : ∀ k, lam k ≤ C := by
    intro k
    cases k with
    | zero => exact le_max_left _ _
    | succ k =>
      have hh : lam (k+1) ≤ lamBar := by
        by_cases hf : F (z (k+1)) = F (z k)
        · rw [h.step_of_eq k hf]; exact min_le_right _ _
        · rw [h.step_of_ne k hf]; exact min_le_right _ _
      exact hh.trans (le_max_right _ _)
  have hdom : ∀ k, 2 ≤ k → z k ∈ dom g := by
    intro k hk
    have hk1 : k-2+1=k-1 := by omega
    have hk2 : k-2+2=k := by omega
    have hl := (hpos (k-1)).1
    exact (scaled_prox g hg (lam (k-1)) hl (zbar (k-1)-lam (k-1) • F (z (k-1)))
      (z k) (by simpa only [hk1,hk2] using h.prox_step (k-2))).1
  let B : Set E := {x | ∃ k, 2 ≤ k ∧ z k=x}
  have hBdom : B ⊆ dom g := by rintro x ⟨k,hk,rfl⟩; exact hdom k hk
  have hBbounded : Bornology.IsBounded B := hz.subset (by rintro x ⟨k,_,rfl⟩; exact ⟨k,rfl⟩)
  obtain ⟨L,hLip⟩ := hL B hBdom hBbounded
  let M : ℝ := L+1
  have hM : 0 < M := by dsimp [M]; positivity
  have hLip' : ∀ j k, 2 ≤ j → 2 ≤ k → ‖F (z j)-F (z k)‖ ≤ M*‖z j-z k‖ := by
    intro j k hj hk
    have hh := hLip.dist_le_mul (z j) (show z j ∈ B from ⟨j,hj,rfl⟩)
      (z k) (show z k ∈ B from ⟨k,hk,rfl⟩)
    rw [dist_eq_norm,dist_eq_norm] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (by dsimp [M]; linarith) (norm_nonneg _))
  let R : ℝ := ϕ^2/(4*C*M^2)
  have hR : 0 < R := by dsimp [R]; positivity
  let c : ℝ := min (lam 0) (min (lam 1) (min (lam 2) (min lamBar R)))
  have hc : 0 < c := by dsimp [c]; exact lt_min (hpos 0).1 (lt_min (hpos 1).1
    (lt_min (hpos 2).1 (lt_min h.lamBar_pos hR)))
  have hc0 : c ≤ lam 0 := min_le_left _ _
  have hc1 : c ≤ lam 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hc2 : c ≤ lam 2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hcb : c ≤ lamBar := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hcR : c ≤ R := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have hlower : ∀ k, c ≤ lam k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      by_cases hk : k ≤ 2
      · interval_cases k <;> assumption
      have hk3 : 3 ≤ k := by omega
      have hk1 : k-1+1=k := by omega
      have hk2 : k-2+1=k-1 := by omega
      have hlp := (hpos (k-1)).1
      have hlpp := (hpos (k-2)).1
      have hrl : c ≤ rho ϕ*lam (k-1) :=
        (ih (k-1) (by omega)).trans (by nlinarith [mul_nonneg (sub_nonneg.mpr hr) hlp.le])
      by_cases hf : F (z k) = F (z (k-1))
      · have he := h.step_of_eq (k-1) (by simpa only [hk1] using hf)
        simp only [hk1] at he
        rw [he]; exact le_min hrl hcb
      · have hFn : 0 < ‖F (z k)-F (z (k-1))‖^2 :=
          sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hf))
        have hsq : ‖F (z k)-F (z (k-1))‖^2 ≤ M^2*‖z k-z (k-1)‖^2 := by
          nlinarith [hLip' k (k-1) (by omega) (by omega),
            norm_nonneg (F (z k)-F (z (k-1))), norm_nonneg (z k-z (k-1))]
        have hden : lam (k-2)*‖F (z k)-F (z (k-1))‖^2 ≤ C*M^2*‖z k-z (k-1)‖^2 := by
          have ha := mul_le_mul_of_nonneg_right (hupper (k-2)) hFn.le
          have hb := mul_le_mul_of_nonneg_left hsq hC.le
          nlinarith
        have hRle : R ≤ ϕ^2*‖z k-z (k-1)‖^2/(4*lam (k-2)*‖F (z k)-F (z (k-1))‖^2) := by
          apply (div_le_div_iff₀ (by positivity : 0 < 4*C*M^2) (by positivity)).mpr
          nlinarith [mul_le_mul_of_nonneg_left hden hp2.le]
        have hmid : R ≤ ϕ*theta (k-1)/(4*lam (k-1)) *
            (‖z k-z (k-1)‖^2/‖F (z k)-F (z (k-1))‖^2) := by
          have ht := h.theta_succ (k-2)
          simp only [hk2] at ht
          rw [ht]
          convert hRle using 1 <;>
            field_simp [hlp.ne',hlpp.ne',norm_ne_zero_iff.mpr (sub_ne_zero.mpr hf)] <;> ring
        have he := h.step_of_ne (k-1) (by simpa only [hk1] using hf)
        simp only [hk1] at he
        rw [he]; exact le_min (le_min hrl (hcR.trans hmid)) hcb
  refine ⟨⟨C,hupper⟩,⟨c,hc,hlower⟩,?_,?_⟩
  · refine ⟨max 1 (1+1/ϕ),fun k => ?_⟩
    cases k with
    | zero => rw [h.theta_zero]; exact le_max_left _ _
    | succ k => exact (run_estimates g F ϕ lamBar z zbar lam theta h k).1.trans (le_max_right _ _)
  · refine ⟨min 1 (c/C*ϕ),lt_min zero_lt_one (mul_pos (div_pos hc hC) hp),fun k => ?_⟩
    cases k with
    | zero => rw [h.theta_zero]; exact min_le_left _ _
    | succ k =>
      have hd : c/C ≤ lam (k+1)/lam k := by
        apply (div_le_div_iff₀ hC (hpos k).1).mpr
        have ha := mul_le_mul_of_nonneg_left (hupper k) hc.le
        have hb := mul_le_mul_of_nonneg_right (hlower (k+1)) hC.le
        nlinarith
      rw [h.theta_succ]
      exact (min_le_right _ _).trans (mul_le_mul_of_nonneg_right hd hp.le)


open Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem tail_dom (g : E → EReal) (F : E → E) (ϕ lamBar : ℝ)
    (z zbar : ℕ → E) (lam theta : ℕ → ℝ) (hg : IsProperConvexLSC g)
    (h : IsEGRAALRun g F ϕ lamBar z zbar lam theta) (k : ℕ) (hk : 2 ≤ k) : z k ∈ dom g := by
  have hp := run_pos g F ϕ lamBar z zbar lam theta h
  change g (z k) ≠ ⊤
  simpa only [show k-2+1=k-1 by omega,show k-2+2=k by omega] using
    (scaled_prox g hg (lam (k-2+1)) (hp (k-2+1)).1
      (zbar (k-2+1)-lam (k-2+1) • F (z (k-2+1))) (z (k-2+2)) (h.prox_step (k-2))).1

private theorem psi_nonneg (g : E → EReal) (F : E → E) (hg : IsProperConvexLSC g)
    {u v : E} (hu : u ∈ solutionSet g F) (hv : v ∈ dom g) : 0 ≤ psi g F u v := by
  have hh := hu.2 v
  rw [← EReal.coe_toReal hu.1 (hg.ne_bot u),← EReal.coe_toReal hv (hg.ne_bot v),
    ← EReal.coe_add,EReal.coe_le_coe_iff] at hh
  dsimp [psi]; linarith

private noncomputable def energy (ϕ : ℝ) (z zbar : ℕ → E) (theta : ℕ → ℝ) (u : E) (n : ℕ) : ℝ :=
  ϕ/(ϕ-1)*‖zbar (n+2)-u‖^2+theta (n+1)/2*‖z (n+2)-z (n+1)‖^2

private theorem energy_facts (g : E → EReal) (F : E → E) (ϕ lamBar : ℝ)
    (z zbar : ℕ → E) (lam theta : ℕ → ℝ) (hg : IsProperConvexLSC g)
    (hF : IsMonotoneOnDom g F) (h : IsEGRAALRun g F ϕ lamBar z zbar lam theta)
    (u : E) (hu : u ∈ solutionSet g F) :
    (∀ n,0 ≤ energy ϕ z zbar theta u n) ∧
    (∀ n,energy ϕ z zbar theta u (n+1)+theta (n+2)*‖z (n+2)-zbar (n+2)‖^2 ≤
      energy ϕ z zbar theta u n) := by
  have hp : 0 < ϕ := by linarith [h.one_lt_phi]
  have hp1 : 0 < ϕ-1 := by linarith [h.one_lt_phi]
  have hpos := run_pos g F ϕ lamBar z zbar lam theta h
  constructor
  · intro n; dsimp [energy]
    exact add_nonneg (mul_nonneg (div_nonneg hp.le hp1.le) (sq_nonneg _))
      (mul_nonneg (div_nonneg (hpos (n+1)).2.le (by norm_num)) (sq_nonneg _))
  · intro n
    have hh := energy_local g F ϕ lamBar z zbar lam theta hg hF h u hu.1 (n+2) (by omega)
    have hn := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (hpos (n+2)).1.le)
      (psi_nonneg g F hg hu (tail_dom g F ϕ lamBar z zbar lam theta hg h (n+2) (by omega)))
    simp only [show n+2-1=n+1 by omega] at hh
    dsimp [energy]
    convert (show ϕ/(ϕ-1)*‖zbar (n+2+1)-u‖^2+theta (n+2)/2*‖z (n+2+1)-z (n+2)‖^2 +
      theta (n+2)*‖z (n+2)-zbar (n+2)‖^2 ≤
      ϕ/(ϕ-1)*‖zbar (n+2)-u‖^2+theta (n+1)/2*‖z (n+2)-z (n+1)‖^2 by linarith) using 1 <;> congr 1 <;> omega

private theorem run_bounded (g : E → EReal) (F : E → E) (ϕ lamBar : ℝ)
    (z zbar : ℕ → E) (lam theta : ℕ → ℝ) (hg : IsProperConvexLSC g)
    (hF : IsMonotoneOnDom g F) (h : IsEGRAALRun g F ϕ lamBar z zbar lam theta)
    (u : E) (hu : u ∈ solutionSet g F) : Bornology.IsBounded (Set.range z) := by
  have hp : 0 < ϕ := by linarith [h.one_lt_phi]
  have hp1 : 0 < ϕ-1 := by linarith [h.one_lt_phi]
  have hA : 0 < ϕ/(ϕ-1) := div_pos hp hp1
  obtain ⟨he0,he⟩ := energy_facts g F ϕ lamBar z zbar lam theta hg hF h u hu
  have ht := fun k => (run_pos g F ϕ lamBar z zbar lam theta h k).2
  have hanti : Antitone (energy ϕ z zbar theta u) := antitone_nat_of_succ_le (fun n => by
    have hh := he n; have hh' := mul_nonneg (ht (n+2)).le (sq_nonneg ‖z (n+2)-zbar (n+2)‖); linarith)
  let R := Real.sqrt (energy ϕ z zbar theta u 0 / (ϕ/(ϕ-1)))
  have hR : ∀ n,‖zbar (n+2)-u‖ ≤ R := by
    intro n
    apply (Real.le_sqrt (norm_nonneg _) (div_nonneg (he0 0) hA.le)).mpr
    apply (le_div_iff₀ hA).mpr
    have hh := hanti (show 0 ≤ n by omega)
    have hn := mul_nonneg (div_nonneg (ht (n+1)).le (by norm_num : (0:ℝ) ≤ 2))
      (sq_nonneg ‖z (n+2)-z (n+1)‖)
    dsimp [energy] at hh ⊢
    nlinarith
  let B := max (max ‖zbar 0‖ ‖zbar 1‖) (R+‖u‖)
  have hb : ∀ n,‖zbar n‖ ≤ B := by
    intro n
    by_cases hn : n < 2
    · interval_cases n
      · exact (le_max_left _ _).trans (le_max_left _ _)
      · exact (le_max_right _ _).trans (le_max_left _ _)
    · have hh := hR (n-2)
      rw [show n-2+2=n by omega] at hh
      calc ‖zbar n‖ ≤ ‖zbar n-u‖+‖u‖ := by simpa using norm_add_le (zbar n-u) u
           _ ≤ R+‖u‖ := by linarith
           _ ≤ B := le_max_right _ _
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨max ‖z 0‖ ((ϕ*B+B)/(ϕ-1)),?_⟩
  rintro _ ⟨k,rfl⟩
  cases k with
  | zero => exact le_max_left _ _
  | succ k =>
    have hv : (ϕ-1) • z (k+1) = ϕ • zbar (k+1)-zbar k := by
      rw [h.zbar_succ,smul_smul]
      simp only [one_div,mul_inv_cancel₀ hp.ne',one_smul]; abel
    have hh := norm_sub_le (ϕ • zbar (k+1)) (zbar k)
    rw [← hv,norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_pos hp,abs_of_pos hp1] at hh
    apply le_trans _ (le_max_right _ _)
    apply (le_div_iff₀ hp1).mpr
    nlinarith [hb (k+1),hb k]


private theorem residual_limit (g : E → EReal) (F : E → E) (ϕ lamBar : ℝ)
    (z zbar : ℕ → E) (lam theta : ℕ → ℝ) (hg : IsProperConvexLSC g)
    (hF : IsMonotoneOnDom g F) (hL : IsLipschitzOnBoundedDom g F)
    (h : IsEGRAALRun g F ϕ lamBar z zbar lam theta)
    (u : E) (hu : u ∈ solutionSet g F) :
    Tendsto (fun k => z k-zbar k) atTop (𝓝 0) ∧
    Tendsto (fun k => z (k+1)-z k) atTop (𝓝 0) := by
  have hb := run_bounded g F ϕ lamBar z zbar lam theta hg hF h u hu
  obtain ⟨_,_,_,c,hc,hct⟩ := steps_local g F ϕ lamBar z zbar lam theta hg hL h hb
  obtain ⟨he0,he⟩ := energy_facts g F ϕ lamBar z zbar lam theta hg hF h u hu
  let V := energy ϕ z zbar theta u
  have hanti : Antitone V := antitone_nat_of_succ_le (fun n => by
    have hh := he n; have hh' := mul_nonneg (le_trans hc.le (hct (n+2))) (sq_nonneg ‖z (n+2)-zbar (n+2)‖); linarith)
  have hlim := tendsto_atTop_ciInf hanti (show BddBelow (Set.range V) from ⟨0,by rintro _ ⟨n,rfl⟩; exact he0 n⟩)
  have hd : Tendsto (fun n => (V n-V (n+1))/c) atTop (𝓝 0) := by
    simpa using (hlim.sub (hlim.comp (tendsto_add_atTop_nat 1))).div_const c
  have hs : Tendsto (fun n => ‖z (n+2)-zbar (n+2)‖^2) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => sq_nonneg _) (fun n => ?_) hd
    apply (le_div_iff₀ hc).mpr
    have hh := he n
    have hh' := mul_le_mul_of_nonneg_right (hct (n+2)) (sq_nonneg ‖z (n+2)-zbar (n+2)‖)
    change c*‖z (n+2)-zbar (n+2)‖^2 ≤ _ at hh'
    dsimp [V]; nlinarith
  have hn : Tendsto (fun n => ‖z (n+2)-zbar (n+2)‖) atTop (𝓝 0) := by
    simpa only [Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hs.sqrt
  have hr : Tendsto (fun k => z k-zbar k) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr ((tendsto_add_atTop_iff_nat 2).mp hn)
  refine ⟨hr,?_⟩
  have ht : Tendsto (fun k => ϕ • (z (k+1)-zbar (k+1))-(z k-zbar k)) atTop (𝓝 0) := by
    simpa using ((hr.comp (tendsto_add_atTop_nat 1)).const_smul ϕ).sub hr
  convert ht using 1
  funext k
  rw [smul_sub,h.zbar_succ,smul_smul]
  have hp : ϕ ≠ 0 := by linarith [h.one_lt_phi]
  simp only [one_div,mul_inv_cancel₀ hp,one_smul]
  module


private theorem cluster_solution (g : E → EReal) (F : E → E) (ϕ lamBar : ℝ)
    (z zbar : ℕ → E) (lam theta : ℕ → ℝ) (hg : IsProperConvexLSC g)
    (hF : IsMonotoneOnDom g F) (hL : IsLipschitzOnBoundedDom g F)
    (h : IsEGRAALRun g F ϕ lamBar z zbar lam theta)
    (u : E) (hu : u ∈ solutionSet g F) (κ : ℕ → ℕ) (hκ : Tendsto κ atTop atTop)
    (hk : ∀ i,2 ≤ κ i) (xs : E) (hz : Tendsto (z ∘ κ) atTop (𝓝 xs)) :
    xs ∈ solutionSet g F := by
  have hbounded := run_bounded g F ϕ lamBar z zbar lam theta hg hF h u hu
  obtain ⟨_,⟨c,hc,hcl⟩,_,_⟩ := steps_local g F ϕ lamBar z zbar lam theta hg hL h hbounded
  have hpos := run_pos g F ϕ lamBar z zbar lam theta h
  obtain ⟨hr,hd⟩ := residual_limit g F ϕ lamBar z zbar lam theta hg hF hL h u hu
  obtain ⟨he0,he⟩ := energy_facts g F ϕ lamBar z zbar lam theta hg hF h u hu
  have hanti : Antitone (energy ϕ z zbar theta u) := antitone_nat_of_succ_le (fun n => by
    have hh := he n; have hh' := mul_nonneg (hpos (n+2)).2.le (sq_nonneg ‖z (n+2)-zbar (n+2)‖); linarith)
  have hpsi (k : ℕ) (hk : 2 ≤ k) : 2*c*psi g F u (z k) ≤ energy ϕ z zbar theta u 0 := by
    have hp := psi_nonneg g F hg hu (tail_dom g F ϕ lamBar z zbar lam theta hg h k hk)
    have hh := energy_local g F ϕ lamBar z zbar lam theta hg hF h u hu.1 k hk
    have hh0 := he0 (k-1)
    have hm := hanti (show 0 ≤ k-2 by omega)
    have hn := mul_nonneg (hpos k).2.le (sq_nonneg ‖z k-zbar k‖)
    have hl := mul_le_mul_of_nonneg_right (hcl k) hp
    dsimp [energy] at hh0 hm ⊢
    rw [show k-1+2=k+1 by omega,show k-1+1=k by omega] at hh0
    rw [show k-2+2=k by omega,show k-2+1=k-1 by omega] at hm
    linarith
  let C := energy ϕ z zbar theta u 0/(2*c)
  have hbound (i : ℕ) : g (z (κ i)) ≤
      (((g u).toReal+C-⟪F u,z (κ i)-u⟫ : ℝ):EReal) := by
    rw [← EReal.coe_toReal (tail_dom g F ϕ lamBar z zbar lam theta hg h (κ i) (hk i)) (hg.ne_bot _),
      EReal.coe_le_coe_iff]
    have hh : psi g F u (z (κ i)) ≤ C := (le_div_iff₀ (show 0 < 2*c by positivity)).mpr (by
      simpa only [mul_assoc,mul_comm,mul_left_comm] using hpsi (κ i) (hk i))
    change psi g F u (z (κ i)) ≤ C at hh
    dsimp [psi] at hh
    linarith
  have hrlim : Tendsto (fun i => (g u).toReal+C-⟪F u,z (κ i)-u⟫) atTop
      (𝓝 ((g u).toReal+C-⟪F u,xs-u⟫)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.inner (hz.sub_const u))
  have hfin : g xs ≠ ⊤ := by
    have hh : g xs ≤ (((g u).toReal+C-⟪F u,xs-u⟫ : ℝ):EReal) :=
      hg.lsc.isClosed_epigraph.mem_of_tendsto
        (hz.prodMk_nhds (EReal.tendsto_coe.mpr hrlim)) (Eventually.of_forall hbound)
    intro ht; simp only [ht,top_le_iff,EReal.coe_ne_top] at hh
  let B : Set E := insert xs {x | ∃ k,2 ≤ k ∧ z k=x}
  have hB : B ⊆ dom g := by
    rintro x (rfl | ⟨k,hk,rfl⟩)
    · exact hfin
    · exact tail_dom g F ϕ lamBar z zbar lam theta hg h k hk
  have hBb : Bornology.IsBounded B := (hbounded.subset (by
    rintro x ⟨k,_,rfl⟩; exact ⟨k,rfl⟩)).insert xs
  obtain ⟨L,hLip⟩ := hL B hB hBb
  have hFlim : Tendsto (fun i => F (z (κ i))) atTop (𝓝 (F xs)) := by
    apply (hLip.continuousOn xs (Set.mem_insert _ _)).tendsto.comp
    exact tendsto_nhdsWithin_iff.mpr ⟨hz,Eventually.of_forall (fun i =>
      Set.mem_insert_of_mem _ ⟨κ i,hk i,rfl⟩)⟩
  have hnext : Tendsto (fun i => z (κ i+1)) atTop (𝓝 xs) := by
    convert (hd.comp hκ).add hz using 1 <;> simp
  have hw : Tendsto (fun i => z (κ i+1)-zbar (κ i)) atTop (𝓝 0) := by
    convert (hd.comp hκ).add (hr.comp hκ) using 1 <;> simp
  have hscaled : Tendsto (fun i => (1/lam (κ i)) • (z (κ i+1)-zbar (κ i))) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (fun i => ?_)
      (show Tendsto (fun i => ‖z (κ i+1)-zbar (κ i)‖/c) atTop (𝓝 0) by simpa using hw.norm.div_const c)
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos zero_lt_one (hpos (κ i)).1),one_div]
    rw [inv_mul_eq_div]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hc (hcl (κ i))
  refine ⟨hfin,fun x => ?_⟩
  by_cases hx : g x=⊤
  · simp [hx]
  have hupper (i : ℕ) : g (z (κ i+1)) ≤
      (((g x).toReal+⟪(1/lam (κ i)) • (z (κ i+1)-zbar (κ i))+F (z (κ i)),x-z (κ i+1)⟫ : ℝ):EReal) := by
    have hki := hk i
    have hprox := scaled_prox g hg (lam (κ i)) (hpos (κ i)).1
      (zbar (κ i)-lam (κ i) • F (z (κ i))) (z (κ i+1))
      (by simpa only [show κ i-1+1=κ i by omega,show κ i-1+2=κ i+1 by omega] using h.prox_step (κ i-1))
    rw [← EReal.coe_toReal hprox.1 (hg.ne_bot _),EReal.coe_le_coe_iff]
    have hh := hprox.2 x hx
    have hl : 0 < lam (κ i) := (hpos (κ i)).1
    apply (mul_le_mul_iff_right₀ hl).mp
    simp only [inner_add_left,inner_sub_left,real_inner_smul_left] at hh ⊢
    field_simp [hl.ne']
    nlinarith
  have hulim : Tendsto (fun i => (g x).toReal+
      ⟪(1/lam (κ i)) • (z (κ i+1)-zbar (κ i))+F (z (κ i)),x-z (κ i+1)⟫) atTop
      (𝓝 ((g x).toReal+⟪F xs,x-xs⟫)) := by
    simpa using tendsto_const_nhds.add ((hscaled.add hFlim).inner (tendsto_const_nhds.sub hnext))
  have hh : g xs ≤ (((g x).toReal+⟪F xs,x-xs⟫ : ℝ):EReal) :=
    hg.lsc.isClosed_epigraph.mem_of_tendsto
      (hnext.prodMk_nhds (EReal.tendsto_coe.mpr hulim)) (Eventually.of_forall hupper)
  simpa only [EReal.coe_add,EReal.coe_toReal hx (hg.ne_bot x),add_comm] using hh


theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (g : E → EReal) (F : E → E) (ϕ lamBar : ℝ)
    (z zbar : ℕ → E) (lam theta : ℕ → ℝ)
    (hS : (solutionSet g F).Nonempty) (hg : IsProperConvexLSC g) (hF : IsMonotoneOnDom g F)
    (hL : IsLipschitzOnBoundedDom g F)
    (h : IsEGRAALRun g F ϕ lamBar z zbar lam theta) :
    ∃ zs ∈ solutionSet g F,Tendsto z atTop (𝓝 zs) ∧ Tendsto zbar atTop (𝓝 zs) := by
  obtain ⟨u,hu⟩ := hS
  have hb := run_bounded g F ϕ lamBar z zbar lam theta hg hF h u hu
  obtain ⟨xs,_,κ,hκ,hz⟩ := hb.isCompact_closure.tendsto_subseq (fun n =>
    subset_closure (show z (n+2) ∈ Set.range z from ⟨n+2,rfl⟩))
  have hκ2 : Tendsto (fun i => κ i+2) atTop atTop := (tendsto_add_atTop_nat 2).comp hκ.tendsto_atTop
  have hx := cluster_solution g F ϕ lamBar z zbar lam theta hg hF hL h u hu
    (fun i => κ i+2) hκ2 (fun _ => by omega) xs hz
  obtain ⟨hr,hd⟩ := residual_limit g F ϕ lamBar z zbar lam theta hg hF hL h u hu
  obtain ⟨_,_,⟨U,hU⟩,_⟩ := steps_local g F ϕ lamBar z zbar lam theta hg hL h hb
  have hpos := run_pos g F ϕ lamBar z zbar lam theta h
  have hUp : 0 < U := (hpos 0).2.trans_le (hU 0)
  have hweighted : Tendsto (fun n => theta (n+1)/2*‖z (n+2)-z (n+1)‖^2) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => mul_nonneg (div_nonneg (hpos (n+1)).2.le (by norm_num)) (sq_nonneg _))
      (fun n => mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hU (n+1)) (by norm_num)) (sq_nonneg _))
    convert (((hd.comp (tendsto_add_atTop_nat 1)).norm.pow 2).const_mul (U/2)) using 1 <;> simp [Nat.add_assoc]
  have hbsub : Tendsto (fun i => zbar (κ i+2)) atTop (𝓝 xs) := by
    convert hz.sub (hr.comp hκ2) using 1 <;> simp
  have hEsub : Tendsto (fun i => energy ϕ z zbar theta xs (κ i)) atTop (𝓝 0) := by
    have hh := (((hbsub.sub_const xs).norm.pow 2).const_mul (ϕ/(ϕ-1))).add
      (hweighted.comp hκ.tendsto_atTop)
    simpa only [sub_self,norm_zero,zero_pow (by norm_num : 2 ≠ 0),mul_zero,zero_add,energy,Function.comp_def] using hh
  obtain ⟨he0,he⟩ := energy_facts g F ϕ lamBar z zbar lam theta hg hF h xs hx
  have hanti : Antitone (energy ϕ z zbar theta xs) := antitone_nat_of_succ_le (fun n => by
    have hh := he n; have hh' := mul_nonneg (hpos (n+2)).2.le (sq_nonneg ‖z (n+2)-zbar (n+2)‖); linarith)
  have hElim := tendsto_atTop_ciInf hanti (show BddBelow (Set.range (energy ϕ z zbar theta xs)) from
    ⟨0,by rintro _ ⟨n,rfl⟩; exact he0 n⟩)
  have hE0 : Tendsto (energy ϕ z zbar theta xs) atTop (𝓝 0) := by
    have hh := tendsto_nhds_unique (hElim.comp hκ.tendsto_atTop) hEsub
    rwa [hh] at hElim
  have hA : 0 < ϕ/(ϕ-1) := div_pos (by linarith [h.one_lt_phi]) (by linarith [h.one_lt_phi])
  have hsq : Tendsto (fun n => ‖zbar (n+2)-xs‖^2) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => sq_nonneg _) (fun n => ?_)
      (show Tendsto (fun n => energy ϕ z zbar theta xs n/(ϕ/(ϕ-1))) atTop (𝓝 0) by simpa using hE0.div_const (ϕ/(ϕ-1)))
    apply (le_div_iff₀ hA).mpr
    have hh := mul_nonneg (div_nonneg (hpos (n+1)).2.le (by norm_num : (0:ℝ)≤2))
      (sq_nonneg ‖z (n+2)-z (n+1)‖)
    dsimp [energy]; nlinarith
  have hn : Tendsto (fun n => ‖zbar (n+2)-xs‖) atTop (𝓝 0) := by
    simpa only [Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hsq.sqrt
  have hbar : Tendsto zbar atTop (𝓝 xs) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr ((tendsto_add_atTop_iff_nat 2).mp hn)
  refine ⟨xs,hx,?_,hbar⟩
  simpa using hr.add hbar
