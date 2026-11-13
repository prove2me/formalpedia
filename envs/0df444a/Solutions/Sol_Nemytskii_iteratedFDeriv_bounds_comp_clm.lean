-- Prove2me | solution 1 for Nemytskii.iteratedFDeriv_bounds_comp_clm
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-12T22:46:53.923487+00:00
-- url     : https://prove2.me/submissions/b3754354-31a5-4d07-affe-842fb4b75402

import Mathlib
import Definitions.Def_FiniteEnergyPlane_TubeFamily

open Metric Set Filter Topology BoundedContinuousFunction
open scoped ContDiff
open Metric Set Filter Topology



/-!
# Nemytskii operators on bounded continuous functions: base layer (spike (e))

`nem Φ u = (x ↦ Φ x (u x))` on `X →ᵇ E`, its continuity, and the pointwise-application
operator `pmul : (X →ᵇ (E →L F)) →L (X →ᵇ E) →L (X →ᵇ F)`.
-/


noncomputable section

namespace NEM

universe u v

variable {X : Type u} [TopologicalSpace X]
  {E F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Base hypotheses on `Φ : X → E → F`: joint continuity, boundedness on `X × closedBall 0 R`,
and uniform equicontinuity of `Φ x` on `closedBall 0 R`, uniformly in `x`. -/
structure IsBaseNem (Φ : X → E → F) : Prop where
  cont : Continuous (fun p : X × E => Φ p.1 p.2)
  bdd : ∀ R : ℝ, ∃ C : ℝ, ∀ x, ∀ a ∈ closedBall (0 : E) R, ‖Φ x a‖ ≤ C
  ueq : ∀ R : ℝ, ∀ ε > 0, ∃ δ > 0, ∀ x, ∀ a ∈ closedBall (0 : E) R,
    ∀ b ∈ closedBall (0 : E) R, ‖a - b‖ < δ → ‖Φ x a - Φ x b‖ < ε

lemma mem_closedBall_norm (u : X →ᵇ E) (x : X) : u x ∈ closedBall (0 : E) ‖u‖ :=
  mem_closedBall_zero_iff.2 (u.norm_coe_le_norm x)

/-- The Nemytskii (superposition) operator. -/
def nem (Φ : X → E → F) (hΦ : IsBaseNem Φ) (u : X →ᵇ E) : X →ᵇ F :=
  ofNormedAddCommGroup (fun x => Φ x (u x))
    (hΦ.cont.comp (continuous_id.prodMk u.continuous)) (hΦ.bdd ‖u‖).choose
    (fun x => (hΦ.bdd ‖u‖).choose_spec x (u x) (mem_closedBall_norm u x))

@[simp] lemma nem_apply (Φ : X → E → F) (hΦ : IsBaseNem Φ) (u : X →ᵇ E) (x : X) :
    nem Φ hΦ u x = Φ x (u x) := rfl

lemma closedBall_succ {u v : X →ᵇ E} (h : dist v u < 1) (x : X) :
    v x ∈ closedBall (0 : E) (‖u‖ + 1) := by
  rw [mem_closedBall_zero_iff]
  have h1 : ‖v x - u x‖ ≤ ‖v - u‖ := by
    simpa using (v - u).norm_coe_le_norm x
  have h2 : ‖v x‖ ≤ ‖u x‖ + ‖v x - u x‖ := by
    simpa using norm_le_insert' (v x) (u x)
  have h3 := u.norm_coe_le_norm x
  rw [dist_eq_norm] at h
  linarith

lemma closedBall_le_succ (u : X →ᵇ E) (x : X) : u x ∈ closedBall (0 : E) (‖u‖ + 1) :=
  closedBall_subset_closedBall (by linarith) (mem_closedBall_norm u x)

/-- Milestone 0: the Nemytskii operator is continuous. -/
theorem continuous_nem (Φ : X → E → F) (hΦ : IsBaseNem Φ) : Continuous (nem Φ hΦ) := by
  refine continuous_iff_continuousAt.2 fun u => Metric.continuousAt_iff.2 fun ε hε => ?_
  obtain ⟨δ, hδ, hδ'⟩ := hΦ.ueq (‖u‖ + 1) (ε / 2) (half_pos hε)
  refine ⟨min δ 1, lt_min hδ one_pos, fun v hv => ?_⟩
  have hv1 : dist v u < 1 := lt_of_lt_of_le hv (min_le_right _ _)
  have hvδ : dist v u < δ := lt_of_lt_of_le hv (min_le_left _ _)
  refine lt_of_le_of_lt ((BoundedContinuousFunction.dist_le (half_pos hε).le).2 fun x => ?_)
    (half_lt_self hε)
  rw [nem_apply, nem_apply, dist_eq_norm]
  refine (hδ' x _ (closedBall_succ hv1 x) _ (closedBall_le_succ u x) ?_).le
  exact lt_of_le_of_lt (by simpa [dist_eq_norm] using dist_coe_le_dist (f := v) (g := u) x) hvδ

variable {G : Type v} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Pointwise application `(f, g) ↦ (x ↦ B (f x) (g x))` of a continuous bilinear `B`.
(Generic in `G`: elaborating `X →ᵇ (E →L F)` directly picks a non-matching `AddCommMonoid`.) -/
def pmulAux (B : G →L[ℝ] E →L[ℝ] F) (f : X →ᵇ G) (g : X →ᵇ E) : X →ᵇ F :=
  ofNormedAddCommGroup (fun x => B (f x) (g x))
    ((B.continuous.comp f.continuous).clm_apply g.continuous) (‖B‖ * ‖f‖ * ‖g‖)
    (fun x => (B.le_opNorm₂ (f x) (g x)).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left (f.norm_coe_le_norm x) (norm_nonneg B))
        (g.norm_coe_le_norm x) (norm_nonneg (g x)) (by positivity)))

@[simp] lemma pmulAux_apply (B : G →L[ℝ] E →L[ℝ] F) (f : X →ᵇ G) (g : X →ᵇ E) (x : X) :
    pmulAux B f g x = B (f x) (g x) := rfl

def pmulL (B : G →L[ℝ] E →L[ℝ] F) : (X →ᵇ G) →ₗ[ℝ] (X →ᵇ E) →ₗ[ℝ] (X →ᵇ F) :=
  LinearMap.mk₂ ℝ (pmulAux B)
    (fun f₁ f₂ g => BoundedContinuousFunction.ext fun x => by simp)
    (fun c f g => BoundedContinuousFunction.ext fun x => by simp)
    (fun f g₁ g₂ => BoundedContinuousFunction.ext fun x => by simp)
    (fun c f g => BoundedContinuousFunction.ext fun x => by simp)

/-- The pointwise-application operator, a continuous bilinear map of norm `≤ ‖B‖`. -/
def pmul (B : G →L[ℝ] E →L[ℝ] F) : (X →ᵇ G) →L[ℝ] (X →ᵇ E) →L[ℝ] (X →ᵇ F) :=
  (pmulL B).mkContinuous₂ ‖B‖ (fun f g => by
      show ‖pmulAux B f g‖ ≤ _
      exact norm_ofNormedAddCommGroup_le _ (by positivity) _)

@[simp] lemma pmul_apply (B : G →L[ℝ] E →L[ℝ] F) (f : X →ᵇ G) (g : X →ᵇ E) (x : X) :
    pmul B f g x = B (f x) (g x) := rfl

end NEM

/-!
# Nemytskii operators on bounded continuous functions: C¹ and C^∞ (spike (e))

* M1 `hasFDerivAt_nem`: `N'(u) h = (x ↦ D₂Φ(x, u x) (h x))`.
* M2 `contDiff_nem` / `contDiff_infty_nem`: induction over the class `UC n`, which is closed
  under `Φ ↦ D₂Φ` by definition.
-/


noncomputable section

namespace NEM

universe u v

variable {X : Type u} [TopologicalSpace X]
  {E F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Milestone 1: the Nemytskii operator is Fréchet differentiable, with derivative
`h ↦ (x ↦ D₂Φ(x, u x) (h x))`. -/
theorem hasFDerivAt_nem (Φ : X → E → F) (hb : IsBaseNem Φ) (hd : ∀ x, Differentiable ℝ (Φ x))
    (hb' : IsBaseNem (fun x => fderiv ℝ (Φ x))) (u : X →ᵇ E) :
    HasFDerivAt (nem Φ hb)
      (pmul (ContinuousLinearMap.id ℝ (E →L[ℝ] F)) (nem (fun x => fderiv ℝ (Φ x)) hb' u)) u := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  refine Asymptotics.IsLittleO.of_bound fun c hc => ?_
  obtain ⟨δ, hδ, hδ'⟩ := hb'.ueq (‖u‖ + 1) c hc
  filter_upwards [Metric.ball_mem_nhds (0 : X →ᵇ E) (lt_min hδ one_pos)] with h hh
  rw [mem_ball_zero_iff] at hh
  have hh1 : ‖h‖ < 1 := lt_of_lt_of_le hh (min_le_right _ _)
  have hhδ : ‖h‖ < δ := lt_of_lt_of_le hh (min_le_left _ _)
  refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun x => ?_
  simp only [coe_sub, Pi.sub_apply, nem_apply, coe_add, Pi.add_apply, pmul_apply,
    ContinuousLinearMap.id_apply]
  have hhx : ‖h x‖ ≤ ‖h‖ := h.norm_coe_le_norm x
  have hux := closedBall_le_succ u x
  have key := Convex.norm_image_sub_le_of_norm_fderiv_le' (𝕜 := ℝ) (f := Φ x)
    (s := closedBall (u x) ‖h x‖) (φ := fderiv ℝ (Φ x) (u x)) (C := c)
    (fun y _ => (hd x).differentiableAt) ?_ (convex_closedBall _ _)
    (mem_closedBall_self (norm_nonneg _)) (y := u x + h x) (by simp [mem_closedBall, dist_eq_norm])
  · simp only [add_sub_cancel_left] at key
    exact key.trans (mul_le_mul_of_nonneg_left hhx hc.le)
  · intro y hy
    rw [mem_closedBall, dist_eq_norm] at hy
    have hy0 : y ∈ closedBall (0 : E) (‖u‖ + 1) := by
      rw [mem_closedBall_zero_iff]
      have h2 : ‖y‖ ≤ ‖u x‖ + ‖y - u x‖ := by simpa using norm_le_insert' y (u x)
      have h3 := u.norm_coe_le_norm x
      linarith
    exact (hδ' x y hy0 (u x) hux (by linarith)).le

/-- The expected derivative formula. -/
theorem fderiv_nem_apply (Φ : X → E → F) (hb : IsBaseNem Φ) (hd : ∀ x, Differentiable ℝ (Φ x))
    (hb' : IsBaseNem (fun x => fderiv ℝ (Φ x))) (u h : X →ᵇ E) (x : X) :
    fderiv ℝ (nem Φ hb) u h x = fderiv ℝ (Φ x) (u x) (h x) := by
  rw [(hasFDerivAt_nem Φ hb hd hb' u).fderiv]
  rfl

/-- The smoothness class: `UC n F Φ` says `Φ, D₂Φ, …, D₂ⁿΦ` all satisfy the base hypotheses
(and the first `n` are differentiable in the second variable). Closed under `D₂` by definition. -/
def UC : ℕ → ∀ (F : Type v) [NormedAddCommGroup F] [NormedSpace ℝ F], (X → E → F) → Prop
  | 0, _, _, _, Φ => IsBaseNem Φ
  | n + 1, F, _, _, Φ => IsBaseNem Φ ∧ (∀ x, Differentiable ℝ (Φ x)) ∧
      UC n (E →L[ℝ] F) (fun x => fderiv ℝ (Φ x))

theorem UC.base {n : ℕ} {Φ : X → E → F} (h : UC n F Φ) : IsBaseNem Φ := by
  cases n with
  | zero => exact h
  | succ n => exact h.1

/-- Milestone 2: `UC n` gives `C^n`. -/
theorem contDiff_nem : ∀ (n : ℕ) (F : Type v) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Φ : X → E → F), UC n F Φ → ∀ hb : IsBaseNem Φ, ContDiff ℝ n (nem Φ hb)
  | 0, F, _, _, Φ, _, hb => contDiff_zero.2 (continuous_nem Φ hb)
  | n + 1, F, _, _, Φ, h, hb => by
      obtain ⟨-, hd, h'⟩ := h
      have IH := contDiff_nem n (E →L[ℝ] F) (fun x => fderiv ℝ (Φ x)) h' h'.base
      rw [Nat.cast_succ]
      exact contDiff_succ_iff_hasFDerivAt.2
        ⟨fun u => pmul (ContinuousLinearMap.id ℝ (E →L[ℝ] F))
            (nem (fun x => fderiv ℝ (Φ x)) h'.base u),
          (pmul (X := X) (ContinuousLinearMap.id ℝ (E →L[ℝ] F))).contDiff.comp IH,
          fun u => hasFDerivAt_nem Φ hb hd h'.base u⟩

/-- Milestone 2 (∞): if every `UC n` holds, the Nemytskii operator is `C^∞`. -/
theorem contDiff_infty_nem (Φ : X → E → F) (h : ∀ n, UC n F Φ) (hb : IsBaseNem Φ) :
    ContDiff ℝ ∞ (nem Φ hb) :=
  contDiff_infty.2 fun n => contDiff_nem n F Φ (h n) hb

end NEM

/-!
# Q-N, layer 0: generic tools (local, NOT published)

* `NEM.uc_of_iteratedFDeriv`: a Nemytskii integrand whose value-derivatives of every order are
  jointly continuous and bounded on `X × closedBall 0 R` lies in every class `UC n`.
-/


noncomputable section

namespace NEM

universe u v

variable {X : Type u} [TopologicalSpace X]
  {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Base hypotheses from bounds on the value and the first value-derivative. -/
theorem isBaseNem_of_bounds {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Φ : X → E → F) (hd : ∀ x, Differentiable ℝ (Φ x))
    (hc : Continuous (fun p : X × E => Φ p.1 p.2))
    (h0 : ∀ R : ℝ, ∃ C : ℝ, ∀ x, ∀ a ∈ closedBall (0 : E) R, ‖Φ x a‖ ≤ C)
    (h1 : ∀ R : ℝ, ∃ C : ℝ, ∀ x, ∀ a ∈ closedBall (0 : E) R, ‖fderiv ℝ (Φ x) a‖ ≤ C) :
    IsBaseNem Φ := by
  refine ⟨hc, h0, fun R ε hε => ?_⟩
  obtain ⟨C, hC⟩ := h1 R
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  refine ⟨ε / (max C 0 + 1), by positivity, fun x a ha b hb hab => ?_⟩
  have key := (convex_closedBall (0 : E) R).norm_image_sub_le_of_norm_fderiv_le
    (f := Φ x) (fun y _ => (hd x).differentiableAt)
    (fun y hy => (hC x y hy).trans (le_max_left C 0)) hb ha
  calc ‖Φ x a - Φ x b‖ ≤ max C 0 * ‖a - b‖ := key
    _ ≤ (max C 0 + 1) * ‖a - b‖ := by nlinarith [norm_nonneg (a - b)]
    _ < (max C 0 + 1) * (ε / (max C 0 + 1)) := by
        exact mul_lt_mul_of_pos_left hab (by positivity)
    _ = ε := by field_simp

/-- **UC criterion.** If every value-derivative `(x, a) ↦ D₂ᵏΦ(x, a)` is jointly continuous and
bounded on `X × closedBall 0 R` (for every `R`), then `Φ` lies in every class `UC n`. -/
theorem uc_of_iteratedFDeriv : ∀ (n : ℕ) (F : Type v) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Φ : X → E → F), (∀ x, ContDiff ℝ ∞ (Φ x)) →
    (∀ k : ℕ, Continuous (fun p : X × E => iteratedFDeriv ℝ k (Φ p.1) p.2)) →
    (∀ (k : ℕ) (R : ℝ), ∃ C : ℝ, ∀ x, ∀ a ∈ closedBall (0 : E) R,
      ‖iteratedFDeriv ℝ k (Φ x) a‖ ≤ C) →
    UC n F Φ := by
  intro n
  induction n with
  | zero =>
    intro F _ _ Φ hs hc hb
    show IsBaseNem Φ
    refine isBaseNem_of_bounds Φ (fun x => (hs x).differentiable (by simp)) ?_ ?_ ?_
    · have := (continuousMultilinearCurryFin0 ℝ E F).continuous.comp (hc 0)
      refine this.congr fun p => ?_
      simp [Function.comp]
    · intro R
      obtain ⟨C, hC⟩ := hb 0 R
      exact ⟨C, fun x a ha => by simpa [norm_iteratedFDeriv_zero] using hC x a ha⟩
    · intro R
      obtain ⟨C, hC⟩ := hb 1 R
      refine ⟨C, fun x a ha => ?_⟩
      have h := hC x a ha
      rw [← norm_iteratedFDeriv_fderiv (n := 0), norm_iteratedFDeriv_zero] at h
      exact h
  | succ n ih =>
    intro F _ _ Φ hs hc hb
    have hd : ∀ x, Differentiable ℝ (Φ x) := fun x => (hs x).differentiable (by simp)
    have hbase : IsBaseNem Φ := by
      have := ih F Φ hs hc hb
      exact this.base
    refine ⟨hbase, hd, ih (E →L[ℝ] F) (fun x => fderiv ℝ (Φ x)) ?_ ?_ ?_⟩
    · exact fun x => (hs x).fderiv_right (m := ∞) le_rfl
    · intro k
      have := (continuousMultilinearCurryRightEquiv' ℝ k E F).continuous.comp (hc (k + 1))
      refine this.congr fun p => ?_
      simp only [Function.comp, iteratedFDeriv_succ_eq_comp_right]
      simp
    · intro k R
      obtain ⟨C, hC⟩ := hb (k + 1) R
      exact ⟨C, fun x a ha => by rw [norm_iteratedFDeriv_fderiv]; exact hC x a ha⟩

/-- Value-derivatives of a partial map `a ↦ Ψ (q, a)`. -/
lemma iteratedFDeriv_partial {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Ψ : P × E → F) (hΨ : ContDiff ℝ ∞ Ψ) (k : ℕ) (q : P) (a : E) :
    iteratedFDeriv ℝ k (fun a => Ψ (q, a)) a =
      (iteratedFDeriv ℝ k Ψ (q, a)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ P E) := by
  have hfun : (fun a => Ψ (q, a)) =
      (fun y => Ψ ((q, 0) + y)) ∘ (ContinuousLinearMap.inr ℝ P E) := by
    funext a; simp
  have hf : ContDiff ℝ ∞ (fun y : P × E => Ψ ((q, 0) + y)) :=
    hΨ.comp (contDiff_const.add contDiff_id)
  rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_right _ hf a (by exact_mod_cast le_top),
    iteratedFDeriv_comp_add_left]
  simp

/-- **UC through a compact parameter.** If `Φ x a = Ψ (p x, a)` with `Ψ` jointly `C^∞` on a
finite-dimensional product and `p` continuous with values in a compact set, then `Φ` lies in
every class `UC n`. -/
theorem uc_of_comp {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P]
    [ProperSpace E] (F : Type v) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Ψ : P × E → F) (hΨ : ContDiff ℝ ∞ Ψ) (p : X → P) (hp : Continuous p) (K : Set P)
    (hK : IsCompact K) (hpK : ∀ x, p x ∈ K) (n : ℕ) :
    UC n F (fun x a => Ψ (p x, a)) := by
  refine uc_of_iteratedFDeriv n F _ (fun x => hΨ.comp (contDiff_const.prodMk contDiff_id))
    (fun k => ?_) (fun k R => ?_)
  · have hc : Continuous (fun y : P × E => iteratedFDeriv ℝ k Ψ y) :=
      hΨ.continuous_iteratedFDeriv (by exact_mod_cast le_top)
    refine ((ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin k => ContinuousLinearMap.inr ℝ P E)).continuous.comp
        (hc.comp ((hp.comp continuous_fst).prodMk continuous_snd))).congr fun y => ?_
    simp [Function.comp, iteratedFDeriv_partial Ψ hΨ]
  · have hc : Continuous (fun y : P × E => iteratedFDeriv ℝ k Ψ y) :=
      hΨ.continuous_iteratedFDeriv (by exact_mod_cast le_top)
    obtain ⟨C, hC⟩ := (hK.prod (isCompact_closedBall (0 : E) R)).exists_bound_of_continuousOn
      hc.continuousOn
    refine ⟨C, fun x a ha => ?_⟩
    rw [iteratedFDeriv_partial Ψ hΨ]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have h1 : ∏ _i : Fin k, ‖ContinuousLinearMap.inr ℝ P E‖ ≤ 1 :=
      Finset.prod_le_one (fun _ _ => norm_nonneg _)
        (fun _ _ => ContinuousLinearMap.norm_inr_le_one ℝ P E)
    have h2 := hC (p x, a) ⟨hpK x, ha⟩
    calc _ ≤ ‖iteratedFDeriv ℝ k Ψ (p x, a)‖ * 1 :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ ≤ C := by simpa using h2

end NEM

/-!
# Q-N, layer 4 (local, NOT published): UC through a bounded linear rescaling of the value

`NEM.uc_of_comp_clm`: if `Ψ x` has value-derivatives of every order that are jointly continuous
and bounded on `X × closedBall 0 R` (every `R`), and `L : X → E →L[ℝ] E'` is continuous and
bounded, then `Φ x a = Ψ x (L x a)` lies in every class `UC n`. The `k`-th value-derivative of
`Φ` costs `‖L x‖ ^ k`; this is the `+∞` mechanism where each `ζT`-derivative costs `e^{δT s}`.
-/


noncomputable section

namespace NEM

universe u v w

variable {X : Type u} [TopologicalSpace X]
  {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {E' : Type w} [NormedAddCommGroup E'] [NormedSpace ℝ E']

/-- Joint continuity of `(f, g) ↦ f ∘ (g, …, g)`. -/
lemma continuous_compCLM_diag {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (k : ℕ) :
    Continuous (fun y : ContinuousMultilinearMap ℝ (fun _ : Fin k => E') G × (E →L[ℝ] E') =>
      y.1.compContinuousLinearMap (fun _ => y.2)) := by
  have h := (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
    (fun _ : Fin k => E) (fun _ : Fin k => E') G).cont
  have h2 : Continuous (fun y : ContinuousMultilinearMap ℝ (fun _ : Fin k => E') G ×
      (E →L[ℝ] E') =>
      (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
        (fun _ : Fin k => E) (fun _ : Fin k => E') G (fun _ => y.2)) y.1) :=
    (h.comp (continuous_pi fun _ => continuous_snd)).clm_apply continuous_fst
  exact h2

/-- **UC through a bounded rescaling.** -/
theorem uc_of_comp_clm (n : ℕ) (F : Type v) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Ψ : X → E' → F) (hs : ∀ x, ContDiff ℝ ∞ (Ψ x))
    (hc : ∀ k : ℕ, Continuous (fun p : X × E' => iteratedFDeriv ℝ k (Ψ p.1) p.2))
    (hb : ∀ (k : ℕ) (R : ℝ), ∃ C : ℝ, ∀ x, ∀ a ∈ closedBall (0 : E') R,
      ‖iteratedFDeriv ℝ k (Ψ x) a‖ ≤ C)
    (L : X → E →L[ℝ] E') (hL : Continuous L) (Λ : ℝ) (hΛ : ∀ x, ‖L x‖ ≤ Λ) :
    UC n F (fun x a => Ψ x (L x a)) := by
  have hit : ∀ (k : ℕ) (x : X) (a : E), iteratedFDeriv ℝ k (fun a => Ψ x (L x a)) a =
      (iteratedFDeriv ℝ k (Ψ x) (L x a)).compContinuousLinearMap (fun _ => L x) := fun k x a =>
    (L x).iteratedFDeriv_comp_right (hs x) a (by exact_mod_cast le_top)
  refine uc_of_iteratedFDeriv n F _ (fun x => (hs x).comp (L x).contDiff) (fun k => ?_)
    (fun k R => ?_)
  · have h1 : Continuous (fun p : X × E => (iteratedFDeriv ℝ k (Ψ p.1) (L p.1 p.2), L p.1)) :=
      ((hc k).comp (continuous_fst.prodMk ((hL.comp continuous_fst).clm_apply continuous_snd))).prodMk
        (hL.comp continuous_fst)
    refine ((continuous_compCLM_diag (E := E) k).comp h1).congr fun p => ?_
    simp only [Function.comp, hit]
  · obtain ⟨C, hC⟩ := hb k (max Λ 0 * R)
    refine ⟨max C 0 * max Λ 0 ^ k, fun x a ha => ?_⟩
    have hLa : L x a ∈ closedBall (0 : E') (max Λ 0 * R) := by
      rw [mem_closedBall_zero_iff] at ha ⊢
      calc ‖L x a‖ ≤ ‖L x‖ * ‖a‖ := (L x).le_opNorm a
        _ ≤ max Λ 0 * R := mul_le_mul ((hΛ x).trans (le_max_left _ _)) ha (norm_nonneg _)
            (le_max_right _ _)
    rw [hit]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact mul_le_mul ((hC x _ hLa).trans (le_max_left _ _))
      (pow_le_pow_left₀ (norm_nonneg _) ((hΛ x).trans (le_max_left _ _)) k)
      (pow_nonneg (norm_nonneg _) _) (le_max_right _ _)

end NEM

/-!
# Q-N, layer 9 (local, NOT published): Nemytskii integrands from derivative bounds

* `NEM.partial_of_bdd`: for `Ψ` jointly `C^∞` on `P × E` with derivative bounds on
  `range p × closedBall 0 R`, the partial maps `a ↦ Ψ (p x, a)` satisfy the hypotheses of
  `uc_of_iteratedFDeriv` / `uc_of_comp_clm` (no compactness).
* `BddDerivOn`, `BddDeriv1On`: smooth maps with bounded derivatives (of order `≥ 1`) on a set;
  closed under bilinear products, composition, sums; CLMs and constants.
-/


noncomputable section

namespace NEM

universe u v

variable {X : Type u} [TopologicalSpace X] {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Partial maps of a jointly smooth `Ψ` with bounds along `p`. -/
theorem partial_of_bdd {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Ψ : P × E → F) (hΨ : ContDiff ℝ ∞ Ψ) (p : X → P) (hp : Continuous p)
    (hbd : ∀ (k : ℕ) (R : ℝ), ∃ C : ℝ, ∀ x, ∀ a ∈ closedBall (0 : E) R,
      ‖iteratedFDeriv ℝ k Ψ (p x, a)‖ ≤ C) :
    (∀ x, ContDiff ℝ ∞ (fun a => Ψ (p x, a))) ∧
      (∀ k : ℕ, Continuous (fun y : X × E => iteratedFDeriv ℝ k (fun a => Ψ (p y.1, a)) y.2)) ∧
      ∀ (k : ℕ) (R : ℝ), ∃ C : ℝ, ∀ x, ∀ a ∈ closedBall (0 : E) R,
        ‖iteratedFDeriv ℝ k (fun a => Ψ (p x, a)) a‖ ≤ C := by
  refine ⟨fun x => hΨ.comp (contDiff_const.prodMk contDiff_id), fun k => ?_, fun k R => ?_⟩
  · have hc : Continuous (fun y : P × E => iteratedFDeriv ℝ k Ψ y) :=
      hΨ.continuous_iteratedFDeriv (by exact_mod_cast le_top)
    refine ((ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin k => ContinuousLinearMap.inr ℝ P E)).continuous.comp
        (hc.comp ((hp.comp continuous_fst).prodMk continuous_snd))).congr fun y => ?_
    simp [Function.comp, iteratedFDeriv_partial Ψ hΨ]
  · obtain ⟨C, hC⟩ := hbd k R
    refine ⟨C, fun x a ha => ?_⟩
    rw [iteratedFDeriv_partial Ψ hΨ]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have h1 : ∏ _i : Fin k, ‖ContinuousLinearMap.inr ℝ P E‖ ≤ 1 :=
      Finset.prod_le_one (fun _ _ => norm_nonneg _)
        (fun _ _ => ContinuousLinearMap.norm_inr_le_one ℝ P E)
    calc _ ≤ ‖iteratedFDeriv ℝ k Ψ (p x, a)‖ * 1 :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ ≤ C := by simpa using hC x a ha

/-- **UC from bounds along a continuous parameter.** -/
theorem uc_of_comp_bdd {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (F : Type v) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Ψ : P × E → F) (hΨ : ContDiff ℝ ∞ Ψ) (p : X → P) (hp : Continuous p)
    (hbd : ∀ (k : ℕ) (R : ℝ), ∃ C : ℝ, ∀ x, ∀ a ∈ closedBall (0 : E) R,
      ‖iteratedFDeriv ℝ k Ψ (p x, a)‖ ≤ C) (n : ℕ) :
    UC n F (fun x a => Ψ (p x, a)) := by
  obtain ⟨h1, h2, h3⟩ := partial_of_bdd Ψ hΨ p hp hbd
  exact uc_of_iteratedFDeriv n F _ h1 h2 h3

/-- **UC from bounds, through a bounded rescaling of the value.** -/
theorem uc_of_comp_bdd_clm {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {E' : Type v} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (F : Type v) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Ψ : P × E' → F) (hΨ : ContDiff ℝ ∞ Ψ) (p : X → P) (hp : Continuous p)
    (hbd : ∀ (k : ℕ) (R : ℝ), ∃ C : ℝ, ∀ x, ∀ a ∈ closedBall (0 : E') R,
      ‖iteratedFDeriv ℝ k Ψ (p x, a)‖ ≤ C)
    (L : X → E →L[ℝ] E') (hL : Continuous L) (Λ : ℝ) (hΛ : ∀ x, ‖L x‖ ≤ Λ) (n : ℕ) :
    UC n F (fun x a => Ψ (p x, L x a)) := by
  obtain ⟨h1, h2, h3⟩ := partial_of_bdd Ψ hΨ p hp hbd
  exact uc_of_comp_clm n F (fun x b => Ψ (p x, b)) h1 h2 h3 L hL Λ hΛ

end NEM

namespace QN9

variable {Y Z W : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Smooth with every derivative bounded on `U`. -/
def BddDerivOn (f : Y → Z) (U : Set Y) : Prop :=
  ContDiff ℝ ∞ f ∧ ∀ k : ℕ, ∃ C : ℝ, ∀ y ∈ U, ‖iteratedFDeriv ℝ k f y‖ ≤ C

/-- Smooth with every derivative of order `≥ 1` bounded on `U`. -/
def BddDeriv1On (f : Y → Z) (U : Set Y) : Prop :=
  ContDiff ℝ ∞ f ∧ ∀ k : ℕ, 1 ≤ k → ∃ C : ℝ, ∀ y ∈ U, ‖iteratedFDeriv ℝ k f y‖ ≤ C

lemma BddDerivOn.one {f : Y → Z} {U : Set Y} (h : BddDerivOn f U) : BddDeriv1On f U :=
  ⟨h.1, fun k _ => h.2 k⟩

lemma BddDerivOn.mono {f : Y → Z} {U V : Set Y} (h : BddDerivOn f V) (hUV : U ⊆ V) :
    BddDerivOn f U := ⟨h.1, fun k => (h.2 k).imp fun C hC y hy => hC y (hUV hy)⟩

lemma BddDeriv1On.mono {f : Y → Z} {U V : Set Y} (h : BddDeriv1On f V) (hUV : U ⊆ V) :
    BddDeriv1On f U := ⟨h.1, fun k hk => (h.2 k hk).imp fun C hC y hy => hC y (hUV hy)⟩

/-- A family of bounds, nonnegative. -/
lemma choose_bounds {f : Y → Z} {U : Set Y} (h : ∀ k : ℕ, ∃ C : ℝ, ∀ y ∈ U, ‖iteratedFDeriv ℝ k f y‖ ≤ C) :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧ ∀ k, ∀ y ∈ U, ‖iteratedFDeriv ℝ k f y‖ ≤ C k := by
  choose C hC using h
  exact ⟨fun k => max (C k) 0, fun k => le_max_right _ _,
    fun k y hy => (hC k y hy).trans (le_max_left _ _)⟩

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma BddDerivOn.bilin (B : Z →L[ℝ] W →L[ℝ] V) {f : Y → Z} {g : Y → W} {U : Set Y}
    (hf : BddDerivOn f U) (hg : BddDerivOn g U) :
    BddDerivOn (fun y => B (f y) (g y)) U := by
  refine ⟨B.isBoundedBilinearMap.contDiff.comp (hf.1.prodMk hg.1), fun n => ?_⟩
  obtain ⟨Cf, hCf0, hCf⟩ := choose_bounds hf.2
  obtain ⟨Cg, hCg0, hCg⟩ := choose_bounds hg.2
  refine ⟨‖B‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * Cf i * Cg (n - i), fun y hy => ?_⟩
  refine (B.norm_iteratedFDeriv_le_of_bilinear hf.1 hg.1 y (by exact_mod_cast le_top)).trans ?_
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (norm_nonneg B)
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hCf i y hy) (Nat.cast_nonneg _)) (hCg (n - i) y hy)
    (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hCf0 i))

lemma BddDerivOn.add {f g : Y → Z} {U : Set Y} (hf : BddDerivOn f U) (hg : BddDerivOn g U) :
    BddDerivOn (fun y => f y + g y) U := by
  refine ⟨hf.1.add hg.1, fun n => ?_⟩
  obtain ⟨C1, hC1⟩ := hf.2 n
  obtain ⟨C2, hC2⟩ := hg.2 n
  refine ⟨C1 + C2, fun y hy => ?_⟩
  rw [iteratedFDeriv_add_apply' (hf.1.contDiffAt.of_le (by exact_mod_cast le_top))
    (hg.1.contDiffAt.of_le (by exact_mod_cast le_top))]
  exact (norm_add_le _ _).trans (add_le_add (hC1 y hy) (hC2 y hy))

lemma BddDeriv1On.add {f g : Y → Z} {U : Set Y} (hf : BddDeriv1On f U) (hg : BddDeriv1On g U) :
    BddDeriv1On (fun y => f y + g y) U := by
  refine ⟨hf.1.add hg.1, fun n hn => ?_⟩
  obtain ⟨C1, hC1⟩ := hf.2 n hn
  obtain ⟨C2, hC2⟩ := hg.2 n hn
  refine ⟨C1 + C2, fun y hy => ?_⟩
  rw [iteratedFDeriv_add_apply' (hf.1.contDiffAt.of_le (by exact_mod_cast le_top))
    (hg.1.contDiffAt.of_le (by exact_mod_cast le_top))]
  exact (norm_add_le _ _).trans (add_le_add (hC1 y hy) (hC2 y hy))

lemma bddDerivOn_const (c : Z) (U : Set Y) : BddDerivOn (fun _ : Y => c) U := by
  refine ⟨contDiff_const, fun k => ⟨‖c‖, fun y _ => ?_⟩⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [norm_iteratedFDeriv_zero]
  · rw [iteratedFDeriv_const_of_ne hk.ne' c]; simp

lemma bddDeriv1On_clm (L : Y →L[ℝ] Z) (U : Set Y) : BddDeriv1On L U := by
  refine ⟨L.contDiff, fun k hk => ⟨‖L‖, fun y _ => ?_⟩⟩
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hL : fderiv ℝ (⇑L) = fun _ => L := funext fun _ => L.fderiv
  rw [← norm_iteratedFDeriv_fderiv, hL]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [norm_iteratedFDeriv_zero]
  · rw [iteratedFDeriv_const_of_ne hm.ne' L]; simp

/-- **Composition** (Faà di Bruno). -/
lemma BddDerivOn.comp {g : Z → W} {f : Y → Z} {U : Set Y} {V : Set Z} (hg : BddDerivOn g V)
    (hf : BddDeriv1On f U) (hfUV : MapsTo f U V) : BddDerivOn (g ∘ f) U := by
  refine ⟨hg.1.comp hf.1, fun n => ?_⟩
  obtain ⟨Cg, hCg0, hCg⟩ := choose_bounds hg.2
  choose Cf hCf using hf.2
  set C := ∑ i ∈ Finset.range (n + 1), Cg i
  set D := 1 + ∑ i ∈ Finset.range (n + 1), if h : 1 ≤ i then max (Cf i h) 0 else 0
  have hD1 : 1 ≤ D := by
    have : 0 ≤ ∑ i ∈ Finset.range (n + 1), if h : 1 ≤ i then max (Cf i h) 0 else 0 :=
      Finset.sum_nonneg fun i _ => by split_ifs <;> simp
    linarith
  refine ⟨n.factorial * C * D ^ n, fun y hy => ?_⟩
  refine norm_iteratedFDeriv_comp_le hg.1 hf.1 (by exact_mod_cast le_top) y (fun i hi => ?_)
    (fun i hi1 hin => ?_)
  · exact (hCg i (f y) (hfUV hy)).trans (Finset.single_le_sum (fun j _ => hCg0 j)
      (Finset.mem_range.2 (by omega)))
  · have h1 : ‖iteratedFDeriv ℝ i f y‖ ≤ max (Cf i hi1) 0 := (hCf i hi1 y hy).trans (le_max_left _ _)
    have h2 : max (Cf i hi1) 0 ≤ D := by
      have := Finset.single_le_sum (f := fun i => if h : 1 ≤ i then max (Cf i h) 0 else 0)
        (fun j _ => by split_ifs <;> simp) (Finset.mem_range.2 (show i < n + 1 by omega))
      simp only [dif_pos hi1] at this
      linarith
    calc ‖iteratedFDeriv ℝ i f y‖ ≤ D := h1.trans h2
      _ = D ^ 1 := (pow_one D).symm
      _ ≤ D ^ i := pow_le_pow_right₀ hD1 hi1

end QN9

/-!
# Proofs of the published Nemytskii children (local)

`exists_contDiff_superposition`, `iteratedFDeriv_bounds_of_comp_compact`,
`iteratedFDeriv_bounds_comp_clm`, `iteratedFDeriv_bounds_of_partial`, from `NEM_*`, `JWQ_N0`,
`JWQ_N4`, `JWQ_N9`.
-/


noncomputable section

namespace NEM

universe u v

theorem exists_contDiff_superposition_proof {X : Type u} [TopologicalSpace X]
    {E F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (Φ : X → E → F)
    (hs : ∀ x, ContDiff ℝ ∞ (Φ x))
    (hc : ∀ k : ℕ, Continuous (fun p : X × E => iteratedFDeriv ℝ k (Φ p.1) p.2))
    (hb : ∀ (k : ℕ) (R : ℝ), ∃ C : ℝ, ∀ x, ∀ a ∈ closedBall (0 : E) R,
      ‖iteratedFDeriv ℝ k (Φ x) a‖ ≤ C) :
    ∃ N : (X →ᵇ E) → (X →ᵇ F), ContDiff ℝ ∞ N ∧ ∀ u x, N u x = Φ x (u x) := by
  have h : ∀ n, UC n F Φ := fun n => uc_of_iteratedFDeriv n F Φ hs hc hb
  exact ⟨nem Φ (h 0).base, contDiff_infty_nem Φ h (h 0).base, fun u x => rfl⟩

theorem iteratedFDeriv_bounds_of_comp_compact_proof {X : Type*} [TopologicalSpace X]
    {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Ψ : P × E → F) (hΨ : ContDiff ℝ ∞ Ψ) (p : X → P) (hp : Continuous p) (K : Set P)
    (hK : IsCompact K) (hpK : ∀ x, p x ∈ K) :
    (∀ x, ContDiff ℝ ∞ ((fun x a => Ψ (p x, a)) x)) ∧
      (∀ k : ℕ, Continuous (fun y : X × E => iteratedFDeriv ℝ k ((fun x a => Ψ (p x, a)) y.1) y.2)) ∧
      ∀ (k : ℕ) (R : ℝ), ∃ C : ℝ, ∀ x, ∀ a ∈ closedBall (0 : E) R,
        ‖iteratedFDeriv ℝ k ((fun x a => Ψ (p x, a)) x) a‖ ≤ C := by
  refine ⟨fun x => hΨ.comp (contDiff_const.prodMk contDiff_id), fun k => ?_, fun k R => ?_⟩
  · have hc : Continuous (fun y : P × E => iteratedFDeriv ℝ k Ψ y) :=
      hΨ.continuous_iteratedFDeriv (by exact_mod_cast le_top)
    refine ((ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin k => ContinuousLinearMap.inr ℝ P E)).continuous.comp
        (hc.comp ((hp.comp continuous_fst).prodMk continuous_snd))).congr fun y => ?_
    simp [Function.comp, iteratedFDeriv_partial Ψ hΨ]
  · have hc : Continuous (fun y : P × E => iteratedFDeriv ℝ k Ψ y) :=
      hΨ.continuous_iteratedFDeriv (by exact_mod_cast le_top)
    obtain ⟨C, hC⟩ := (hK.prod (isCompact_closedBall (0 : E) R)).exists_bound_of_continuousOn
      hc.continuousOn
    refine ⟨C, fun x a ha => ?_⟩
    rw [iteratedFDeriv_partial Ψ hΨ]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have h1 : ∏ _i : Fin k, ‖ContinuousLinearMap.inr ℝ P E‖ ≤ 1 :=
      Finset.prod_le_one (fun _ _ => norm_nonneg _)
        (fun _ _ => ContinuousLinearMap.norm_inr_le_one ℝ P E)
    have h2 := hC (p x, a) ⟨hpK x, ha⟩
    calc _ ≤ ‖iteratedFDeriv ℝ k Ψ (p x, a)‖ * 1 :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ ≤ C := by simpa using h2


theorem iteratedFDeriv_bounds_comp_clm_proof {X : Type*} [TopologicalSpace X]
    {E E' F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Ψ : X → E' → F) (hs : ∀ x, ContDiff ℝ ∞ (Ψ x))
    (hc : ∀ k : ℕ, Continuous (fun p : X × E' => iteratedFDeriv ℝ k (Ψ p.1) p.2))
    (hb : ∀ (k : ℕ) (R : ℝ), ∃ C : ℝ, ∀ x, ∀ a ∈ closedBall (0 : E') R,
      ‖iteratedFDeriv ℝ k (Ψ x) a‖ ≤ C)
    (L : X → E →L[ℝ] E') (hL : Continuous L) (Λ : ℝ) (hΛ : ∀ x, ‖L x‖ ≤ Λ) :
    (∀ x, ContDiff ℝ ∞ ((fun x a => Ψ x (L x a)) x)) ∧
      (∀ k : ℕ, Continuous (fun y : X × E => iteratedFDeriv ℝ k ((fun x a => Ψ x (L x a)) y.1) y.2)) ∧
      ∀ (k : ℕ) (R : ℝ), ∃ C : ℝ, ∀ x, ∀ a ∈ closedBall (0 : E) R,
        ‖iteratedFDeriv ℝ k ((fun x a => Ψ x (L x a)) x) a‖ ≤ C := by
  have hit : ∀ (k : ℕ) (x : X) (a : E), iteratedFDeriv ℝ k (fun a => Ψ x (L x a)) a =
      (iteratedFDeriv ℝ k (Ψ x) (L x a)).compContinuousLinearMap (fun _ => L x) := fun k x a =>
    (L x).iteratedFDeriv_comp_right (hs x) a (by exact_mod_cast le_top)
  refine ⟨fun x => (hs x).comp (L x).contDiff, fun k => ?_, fun k R => ?_⟩
  · have h1 : Continuous (fun p : X × E => (iteratedFDeriv ℝ k (Ψ p.1) (L p.1 p.2), L p.1)) :=
      ((hc k).comp (continuous_fst.prodMk ((hL.comp continuous_fst).clm_apply continuous_snd))).prodMk
        (hL.comp continuous_fst)
    refine ((continuous_compCLM_diag (E := E) k).comp h1).congr fun p => ?_
    simp only [Function.comp, hit]
  · obtain ⟨C, hC⟩ := hb k (max Λ 0 * R)
    refine ⟨max C 0 * max Λ 0 ^ k, fun x a ha => ?_⟩
    have hLa : L x a ∈ closedBall (0 : E') (max Λ 0 * R) := by
      rw [mem_closedBall_zero_iff] at ha ⊢
      calc ‖L x a‖ ≤ ‖L x‖ * ‖a‖ := (L x).le_opNorm a
        _ ≤ max Λ 0 * R := mul_le_mul ((hΛ x).trans (le_max_left _ _)) ha (norm_nonneg _)
            (le_max_right _ _)
    rw [hit]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact mul_le_mul ((hC x _ hLa).trans (le_max_left _ _))
      (pow_le_pow_left₀ (norm_nonneg _) ((hΛ x).trans (le_max_left _ _)) k)
      (pow_nonneg (norm_nonneg _) _) (le_max_right _ _)


theorem iteratedFDeriv_bounds_of_partial_proof {X : Type*} [TopologicalSpace X]
    {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Ψ : P × E → F) (hΨ : ContDiff ℝ ∞ Ψ) (p : X → P) (hp : Continuous p)
    (hbd : ∀ (k : ℕ) (R : ℝ), ∃ C : ℝ, ∀ x, ∀ a ∈ closedBall (0 : E) R,
      ‖iteratedFDeriv ℝ k Ψ (p x, a)‖ ≤ C) :
    (∀ x, ContDiff ℝ ∞ ((fun x a => Ψ (p x, a)) x)) ∧
      (∀ k : ℕ, Continuous (fun y : X × E => iteratedFDeriv ℝ k ((fun x a => Ψ (p x, a)) y.1) y.2)) ∧
      ∀ (k : ℕ) (R : ℝ), ∃ C : ℝ, ∀ x, ∀ a ∈ closedBall (0 : E) R,
        ‖iteratedFDeriv ℝ k ((fun x a => Ψ (p x, a)) x) a‖ ≤ C := by
  refine ⟨fun x => hΨ.comp (contDiff_const.prodMk contDiff_id), fun k => ?_, fun k R => ?_⟩
  · have hc : Continuous (fun y : P × E => iteratedFDeriv ℝ k Ψ y) :=
      hΨ.continuous_iteratedFDeriv (by exact_mod_cast le_top)
    refine ((ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin k => ContinuousLinearMap.inr ℝ P E)).continuous.comp
        (hc.comp ((hp.comp continuous_fst).prodMk continuous_snd))).congr fun y => ?_
    simp [Function.comp, iteratedFDeriv_partial Ψ hΨ]
  · obtain ⟨C, hC⟩ := hbd k R
    refine ⟨C, fun x a ha => ?_⟩
    rw [iteratedFDeriv_partial Ψ hΨ]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have h1 : ∏ _i : Fin k, ‖ContinuousLinearMap.inr ℝ P E‖ ≤ 1 :=
      Finset.prod_le_one (fun _ _ => norm_nonneg _)
        (fun _ _ => ContinuousLinearMap.norm_inr_le_one ℝ P E)
    calc _ ≤ ‖iteratedFDeriv ℝ k Ψ (p x, a)‖ * 1 :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ ≤ C := by simpa using hC x a ha

end NEM

-- Namespace of the published Nemytskii statements.
namespace Nemytskii
theorem namespace_marker : True := trivial
end Nemytskii

open Nemytskii

theorem solution {X : Type*} [TopologicalSpace X]
    {E E' F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Ψ : X → E' → F) (hs : ∀ x, ContDiff ℝ ∞ (Ψ x))
    (hc : ∀ k : ℕ, Continuous (fun p : X × E' => iteratedFDeriv ℝ k (Ψ p.1) p.2))
    (hb : ∀ (k : ℕ) (R : ℝ), ∃ C : ℝ, ∀ x, ∀ a ∈ closedBall (0 : E') R,
      ‖iteratedFDeriv ℝ k (Ψ x) a‖ ≤ C)
    (L : X → E →L[ℝ] E') (hL : Continuous L) (Λ : ℝ) (hΛ : ∀ x, ‖L x‖ ≤ Λ) :
    (∀ x, ContDiff ℝ ∞ ((fun x a => Ψ x (L x a)) x)) ∧
      (∀ k : ℕ, Continuous (fun y : X × E => iteratedFDeriv ℝ k ((fun x a => Ψ x (L x a)) y.1) y.2)) ∧
      ∀ (k : ℕ) (R : ℝ), ∃ C : ℝ, ∀ x, ∀ a ∈ closedBall (0 : E) R,
        ‖iteratedFDeriv ℝ k ((fun x a => Ψ x (L x a)) x) a‖ ≤ C :=
  NEM.iteratedFDeriv_bounds_comp_clm_proof Ψ hs hc hb L hL Λ hΛ
