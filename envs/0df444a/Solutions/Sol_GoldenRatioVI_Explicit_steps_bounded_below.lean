-- Prove2me | solution 1 for GoldenRatioVI.Explicit.steps_bounded_below
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:26:03.781977+00:00
-- url     : https://prove2.me/submissions/11cbab58-3df8-49ee-8937-fadd7d7fd513

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



end GoldenRatioVI.Explicit
open GoldenRatioVI.Explicit

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
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
