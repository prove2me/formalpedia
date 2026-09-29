-- Prove2me | solution 1 for Mandelbrot.mandelbrot_lemniscate_isPreconnected
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T10:55:20.084027+00:00
-- url     : https://prove2.me/submissions/790ed55d-8e81-45cf-bb47-e96f2e1d05bc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_mandelbrot_sets
import Theorems.Thm_Mandelbrot_mandelbrot_iterate_critical_values_le_two

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Topology Set Polynomial unitInterval

namespace AgentI

/-- Filled polynomial lemniscate at a level `r` strictly above all critical values is
preconnected: retract `ℂ` onto it by lifting radial paths through the covering `p`. -/
theorem lemn_gt (p : ℂ[X]) (R r : ℝ) (hR : 0 ≤ R) (hRr : R < r)
    (hcrit : ∀ z, p.derivative.eval z = 0 → ‖p.eval z‖ ≤ R) :
    IsPreconnected {z : ℂ | ‖p.eval z‖ ≤ r} := by
  set T : Set ℂ := {w | R < ‖w‖} with hTdef
  have hT : T ⊆ (p.eval '' {k | p.derivative.eval k = 0})ᶜ := by
    rintro w hw ⟨k, hk, rfl⟩
    exact absurd (hcrit k hk) (not_le.2 hw)
  have cov : IsCoveringMap (T.restrictPreimage p.eval) :=
    ((p.isCoveringMapOn_eval).mono hT).isCoveringMap_restrictPreimage
  set S : Set ℂ := {z | r ≤ ‖p.eval z‖} with hSdef
  have hr0 : 0 < r := lt_of_le_of_lt hR hRr
  have hposS : ∀ a : S, 0 < ‖p.eval a.1‖ := fun a => lt_of_lt_of_le hr0 a.2
  -- the scalar
  let sc : I × S → ℝ := fun ta => (1 - (ta.1 : ℝ)) + (ta.1 : ℝ) * r / ‖p.eval ta.2.1‖
  have sc_cont : Continuous sc := by
    have h1 : Continuous fun ta : I × S => ‖p.eval ta.2.1‖ :=
      (p.continuous.comp (continuous_subtype_val.comp continuous_snd)).norm
    refine (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).add ?_
    refine Continuous.div ((continuous_subtype_val.comp continuous_fst).mul continuous_const) h1 ?_
    intro ta; exact (hposS ta.2).ne'
  have norm_H : ∀ ta : I × S, ‖((sc ta : ℝ) : ℂ) * p.eval ta.2.1‖
      = (1 - (ta.1 : ℝ)) * ‖p.eval ta.2.1‖ + (ta.1 : ℝ) * r := by
    intro ta
    have hp := hposS ta.2
    have ht0 : 0 ≤ (ta.1 : ℝ) := ta.1.2.1
    have ht1 : (ta.1 : ℝ) ≤ 1 := ta.1.2.2
    have hsc : 0 ≤ sc ta := by
      simp only [sc]; have := div_nonneg (mul_nonneg ht0 hr0.le) hp.le; linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsc]
    simp only [sc]; field_simp
  have H_mem : ∀ ta : I × S, ((sc ta : ℝ) : ℂ) * p.eval ta.2.1 ∈ T := by
    intro ta
    show R < ‖((sc ta : ℝ) : ℂ) * p.eval ta.2.1‖
    rw [norm_H]
    have h2 : r ≤ ‖p.eval ta.2.1‖ := ta.2.2
    have ht0 : 0 ≤ (ta.1 : ℝ) := ta.1.2.1
    have ht1 : (ta.1 : ℝ) ≤ 1 := ta.1.2.2
    have := mul_le_mul_of_nonneg_left h2 (sub_nonneg.2 ht1)
    nlinarith
  let H : C(I × S, T) :=
    ⟨fun ta => ⟨((sc ta : ℝ) : ℂ) * p.eval ta.2.1, H_mem ta⟩, by
      refine Continuous.subtype_mk ?_ _
      exact (Complex.continuous_ofReal.comp sc_cont).mul
        (p.continuous.comp (continuous_subtype_val.comp continuous_snd))⟩
  let f : C(S, p.eval ⁻¹' T) :=
    ⟨fun a => ⟨a.1, show R < ‖p.eval a.1‖ from lt_of_lt_of_le hRr a.2⟩,
      Continuous.subtype_mk continuous_subtype_val _⟩
  have H_0 : ∀ a, H (0, a) = T.restrictPreimage p.eval (f a) := by
    intro a
    apply Subtype.ext
    simp [H, f, sc, Set.restrictPreimage]
  let L := cov.liftHomotopy H f H_0
  have L_lifts : ∀ ta, T.restrictPreimage p.eval (L ta) = H ta := fun ta =>
    congr_fun (cov.liftHomotopy_lifts H f H_0) ta
  -- on the boundary the homotopy is constant, so the lift is constant
  have L_bdry : ∀ a : S, ‖p.eval a.1‖ = r → ∀ t, L (t, a) = f a := by
    intro a ha t
    have hconst : ∀ t : I, H (t, a) = H (0, a) := by
      intro t
      apply Subtype.ext
      simp only [H, sc, ContinuousMap.coe_mk, ha]
      have : r ≠ 0 := hr0.ne'
      congr 2
      field_simp
      push_cast; ring
    have key := cov.eq_of_comp_eq (A := I) (g₁ := fun t => L (t, a)) (g₂ := fun _ => f a)
      (L.continuous.comp (Continuous.prodMk_left a)) continuous_const
      (by funext t; simp only [Function.comp_apply]; rw [L_lifts, hconst t, H_0]) 0
      (cov.liftHomotopy_zero H f H_0 a)
    exact congr_fun key t
  classical
  let ρ : ℂ → ℂ := fun z => if h : r ≤ ‖p.eval z‖ then (L (1, ⟨z, h⟩)).1 else z
  have ρ_fix : ∀ z, ‖p.eval z‖ ≤ r → ρ z = z := by
    intro z hz
    by_cases h : r ≤ ‖p.eval z‖
    · have he : ‖p.eval z‖ = r := le_antisymm hz h
      simp only [ρ, dif_pos h]
      rw [L_bdry ⟨z, h⟩ he 1]
      rfl
    · simp only [ρ, dif_neg h]
  have ρ_mem : ∀ z, ‖p.eval (ρ z)‖ ≤ r := by
    intro z
    by_cases h : r ≤ ‖p.eval z‖
    · simp only [ρ, dif_pos h]
      have e1 := congrArg Subtype.val (L_lifts (1, ⟨z, h⟩))
      have e2 : p.eval (L (1, ⟨z, h⟩)).1 = ((sc (1, ⟨z, h⟩) : ℝ) : ℂ) * p.eval z := e1
      rw [e2, norm_H]
      simp
    · simp only [ρ, dif_neg h]; exact (not_le.1 h).le
  have ρ_cont : Continuous ρ := by
    have hS : IsClosed S := isClosed_le continuous_const (p.continuous.norm)
    have hK : IsClosed {z : ℂ | ‖p.eval z‖ ≤ r} := isClosed_le (p.continuous.norm) continuous_const
    have c1 : ContinuousOn ρ S := by
      rw [continuousOn_iff_continuous_domRestrict]
      have : S.domRestrict ρ = fun a : S => (L (1, a)).1 := by
        funext a
        simp only [Set.domRestrict_apply, ρ]
        rw [dif_pos (show r ≤ ‖p.eval a.1‖ from a.2)]
      rw [this]
      exact continuous_subtype_val.comp (L.continuous.comp (Continuous.prodMk_right 1))
    have c2 : ContinuousOn ρ {z : ℂ | ‖p.eval z‖ ≤ r} :=
      continuousOn_id.congr fun z hz => ρ_fix z hz
    have := c1.union_of_isClosed c2 hS hK
    have hu : S ∪ {z : ℂ | ‖p.eval z‖ ≤ r} = univ := by
      ext z; simp only [mem_union, mem_setOf_eq, S, mem_univ, iff_true]; exact le_total _ _
    rw [hu] at this
    exact continuousOn_univ.1 this
  have hrange : range ρ = {z : ℂ | ‖p.eval z‖ ≤ r} := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩; exact ρ_mem y
    · intro hz; exact ⟨z, ρ_fix z hz⟩
  rw [← hrange]
  exact isPreconnected_range ρ_cont

theorem nested_preconnected
    {α : Type*} [TopologicalSpace α] [T2Space α] {s : ℕ → Set α}
    (hanti : Antitone s) (hcomp : ∀ n, IsCompact (s n))
    (hconn : ∀ n, IsPreconnected (s n)) :
    IsPreconnected (⋂ n, s n) := by
  have hKcl : IsClosed (⋂ n, s n) := isClosed_iInter fun n => (hcomp n).isClosed
  have hKcomp : IsCompact (⋂ n, s n) :=
    (hcomp 0).of_isClosed_subset hKcl (iInter_subset s 0)
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed hKcl]
  intro u v hu hv hsub hdisj
  by_contra hcon
  push Not at hcon
  obtain ⟨hnu, hnv⟩ := hcon
  have hAne : ((⋂ n, s n) ∩ u).Nonempty := by
    obtain ⟨x, hxK, hxv⟩ := not_subset.mp hnv
    rcases hsub hxK with h | h
    · exact ⟨x, hxK, h⟩
    · exact absurd h hxv
  have hBne : ((⋂ n, s n) ∩ v).Nonempty := by
    obtain ⟨x, hxK, hxu⟩ := not_subset.mp hnu
    rcases hsub hxK with h | h
    · exact absurd h hxu
    · exact ⟨x, hxK, h⟩
  have hABd : Disjoint ((⋂ n, s n) ∩ u) ((⋂ n, s n) ∩ v) :=
    hdisj.mono inter_subset_right inter_subset_right
  obtain ⟨U, V, hUo, hVo, hAU, hBV, hUV⟩ :=
    SeparatedNhds.of_isCompact_isCompact (hKcomp.inter_right hu) (hKcomp.inter_right hv) hABd
  have hKUV : (⋂ n, s n) ⊆ U ∪ V := by
    intro x hx
    rcases hsub hx with h | h
    · exact Or.inl (hAU ⟨hx, h⟩)
    · exact Or.inr (hBV ⟨hx, h⟩)
  have hex : ∃ n, s n ⊆ U ∪ V := by
    by_contra hno
    push Not at hno
    have hne : ∀ n, (s n \ (U ∪ V)).Nonempty := by
      intro n
      obtain ⟨x, hx1, hx2⟩ := not_subset.mp (hno n)
      exact ⟨x, hx1, hx2⟩
    have htc : ∀ n, IsCompact (s n \ (U ∪ V)) := fun n => (hcomp n).diff (hUo.union hVo)
    have hanti' : Antitone (fun n => s n \ (U ∪ V)) := fun a b hab =>
      Set.sdiff_subset_sdiff_left (hanti hab)
    have hdir : Directed (· ⊇ ·) (fun n => s n \ (U ∪ V)) := hanti'.directed_ge
    obtain ⟨x, hx⟩ :=
      IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
        (fun n => s n \ (U ∪ V)) hdir hne htc (fun n => (htc n).isClosed)
    simp only [mem_iInter, Set.mem_sdiff] at hx
    exact (hx 0).2 (hKUV (mem_iInter.2 fun n => (hx n).1))
  obtain ⟨n, hn⟩ := hex
  have hKsn : (⋂ m, s m) ⊆ s n := iInter_subset s n
  obtain ⟨y, -, hyU, hyV⟩ :=
    hconn n U V hUo hVo hn
      (hAne.mono (fun x hx => ⟨hKsn hx.1, hAU hx⟩))
      (hBne.mono (fun x hx => ⟨hKsn hx.1, hBV hx⟩))
  exact (hUV.le_bot ⟨hyU, hyV⟩ : y ∈ (⊥ : Set α))

/-- Level `R` itself, given compactness of the slightly larger sublevel sets. -/
theorem lemn_ge (p : ℂ[X]) (R : ℝ) (hR : 0 ≤ R)
    (hcrit : ∀ z, p.derivative.eval z = 0 → ‖p.eval z‖ ≤ R)
    (hcpt : ∀ r, R < r → IsCompact {z : ℂ | ‖p.eval z‖ ≤ r}) :
    IsPreconnected {z : ℂ | ‖p.eval z‖ ≤ R} := by
  let s : ℕ → Set ℂ := fun n => {z : ℂ | ‖p.eval z‖ ≤ R + 1 / ((n : ℝ) + 1)}
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have heq : {z : ℂ | ‖p.eval z‖ ≤ R} = ⋂ n, s n := by
    ext z
    simp only [mem_iInter, s, mem_setOf_eq]
    constructor
    · intro h n; linarith [hpos n]
    · intro h
      by_contra hc
      push Not at hc
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hc)
      have := h n
      linarith
  rw [heq]
  refine nested_preconnected ?_ (fun n => hcpt _ (by linarith [hpos n]))
    (fun n => lemn_gt p R _ hR (by linarith [hpos n]) hcrit)
  intro a b hab z hz
  simp only [s, mem_setOf_eq] at hz ⊢
  have : 1 / ((b : ℝ) + 1) ≤ 1 / ((a : ℝ) + 1) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hab 1
  linarith

/-- The Mandelbrot polynomials `P_k`. -/
noncomputable def mpoly : ℕ → ℂ[X]
  | 0 => 0
  | k + 1 => mpoly k ^ 2 + X

theorem mpoly_eval (k : ℕ) (c : ℂ) : (mpoly k).eval c = (fun z ↦ z ^ 2 + c)^[k] 0 := by
  induction k with
  | zero => simp [mpoly]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ← ih]
    simp [mpoly]

/-- Escape bound: for `|c| > 2` and `k ≥ 1`, `|P_k(c)| ≥ |c|`. -/
theorem mpoly_escape (c : ℂ) (hc : 2 < ‖c‖) : ∀ k, 1 ≤ k → ‖c‖ ≤ ‖(mpoly k).eval c‖ := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp [mpoly]
    · have h := ih hk0
      have e : (mpoly (k + 1)).eval c = (mpoly k).eval c ^ 2 + c := by simp [mpoly]
      rw [e]
      have h1 : ‖(mpoly k).eval c ^ 2‖ - ‖c‖ ≤ ‖(mpoly k).eval c ^ 2 + c‖ := by
        have h2 := norm_add_le ((mpoly k).eval c ^ 2 + c) (-c)
        simp only [add_neg_cancel_right, norm_neg] at h2
        linarith
      rw [norm_pow] at h1
      nlinarith

theorem mpoly_sub_closedBall (k : ℕ) (hk : 1 ≤ k) (r : ℝ) (hr : 2 ≤ r) :
    {z : ℂ | ‖(mpoly k).eval z‖ ≤ r} ⊆ Metric.closedBall 0 r := by
  intro z hz
  simp only [mem_setOf_eq] at hz
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra h
  push Not at h
  have := mpoly_escape z (by linarith) k hk
  linarith

theorem reduction
    (hstar : ∀ (k : ℕ) (c : ℂ), deriv (fun c : ℂ ↦ (fun z ↦ z ^ 2 + c)^[k] 0) c = 0 →
      ‖(fun z ↦ z ^ 2 + c)^[k] 0‖ ≤ 2)
    (k : ℕ) : IsPreconnected {c : ℂ | ‖(fun z ↦ z ^ 2 + c)^[k] 0‖ ≤ 2} := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [Function.iterate_zero, id, norm_zero]
    have : {c : ℂ | (0 : ℝ) ≤ 2} = univ := by ext; simp
    rw [this]; exact isPreconnected_univ
  have hfun : (fun c : ℂ ↦ (fun z ↦ z ^ 2 + c)^[k] 0) = fun c => (mpoly k).eval c :=
    funext fun c => (mpoly_eval k c).symm
  have hset : {c : ℂ | ‖(fun z ↦ z ^ 2 + c)^[k] 0‖ ≤ 2} = {c : ℂ | ‖(mpoly k).eval c‖ ≤ 2} := by
    ext c; simp [mpoly_eval]
  rw [hset]
  refine lemn_ge (mpoly k) 2 (by norm_num) ?_ ?_
  · intro z hz
    have := hstar k z (by rw [hfun, Polynomial.deriv]; exact hz)
    rwa [← mpoly_eval] at this
  · intro r hr
    exact (isCompact_closedBall 0 r).of_isClosed_subset
      (isClosed_le (mpoly k).continuous.norm continuous_const)
      (mpoly_sub_closedBall k hk r hr.le)

end AgentI


namespace Mandelbrot

theorem _root_.solution (k : ℕ) :
    IsPreconnected {c : ℂ | ‖(fun z ↦ z ^ 2 + c)^[k] 0‖ ≤ 2} :=
  AgentI.reduction (fun k c h => mandelbrot_iterate_critical_values_le_two k c h) k

end Mandelbrot
