-- Prove2me | solution 1 for OAI.SharpTerminalLeave.prefix_present_edge_closure
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T07:00:21.439298+00:00
-- url     : https://prove2.me/submissions/205e8827-863d-4276-80d7-770b5b736c95

import Mathlib
import Definitions.Def_TriangleRemoval
import Definitions.Def_OAIQ4Tr000
import Theorems.Thm_OAI_SharpTerminalLeave_prefix_edge_residual_bounds

section
-- module Solutions.OAIQ4_Tr.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_MovingStarDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators

namespace SharpTerminalLeave

open Classical

private lemma moving_abs_sub_bound (x y : ℝ) : |x-y| ≤ |x|+|y| := by
  simpa using (abs_sub_le x 0 y)

lemma movingStarDegree_nonneg {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (active : Finset E) (u : V) :
    0 ≤ movingStarDegree ends active u := Nat.cast_nonneg _

lemma movingStarMean_congr {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (active : Finset E) {x y : E → ℝ}
    (h : ∀ e ∈ active, x e = y e) : movingStarMean ends active x = movingStarMean ends active y := by
  classical
  funext u
  unfold movingStarMean
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  exact h e (Finset.mem_filter.mp he).1

lemma movingStarMean_sub {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (active : Finset E) (x y : E → ℝ) (u : V) :
    movingStarMean ends active (fun e => x e-y e) u =
      movingStarMean ends active x u-movingStarMean ends active y u := by
  classical
  simp only [movingStarMean,Finset.sum_sub_distrib,sub_div]

lemma movingStarMean_zero_degree {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (active : Finset E) (x : E → ℝ) (u : V)
    (hd : movingStarDegree ends active u = 0) : movingStarMean ends active x u = 0 := by
  simp [movingStarMean,hd]

lemma movingStarMean_bound {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (active : Finset E) (x : E → ℝ) (u : V)
    {M : ℝ} (hM : 0 ≤ M) (hx : ∀ e ∈ active, |x e| ≤ M) :
    |movingStarMean ends active x u| ≤ M := by
  classical
  by_cases hd : movingStarDegree ends active u = 0
  · simpa [movingStarMean_zero_degree ends active x u hd] using hM
  · have hp : 0 < movingStarDegree ends active u :=
      lt_of_le_of_ne (movingStarDegree_nonneg ends active u) (Ne.symm hd)
    unfold movingStarMean
    rw [abs_div,abs_of_pos hp]
    apply (div_le_iff₀ hp).mpr
    calc
      _ ≤ ∑ e ∈ active.filter (fun e => u ∈ ends e), |x e| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _e ∈ active.filter (fun e => u ∈ ends e), M := by
        apply Finset.sum_le_sum
        intro e he
        exact hx e (Finset.mem_filter.mp he).1
      _ = _ := by simp [movingStarDegree,mul_comm]

lemma movingStarLift_bound {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (hends : ∀ e, (ends e).card = 2) (b : V → ℝ)
    {B : ℝ} (hb : ∀ v, |b v| ≤ B) (e : E) : |movingStarLift ends b e| ≤ 2*B := by
  classical
  unfold movingStarLift
  calc
    _ ≤ ∑ v ∈ ends e, |b v| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _v ∈ ends e, B := Finset.sum_le_sum (fun v _ => hb v)
    _ = _ := by simp [hends]

lemma movingStarOtherMean_bound {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (hends : ∀ e, (ends e).card = 2) (active : Finset E)
    (b : V → ℝ) (u : V) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ v, |b v| ≤ B) :
    |movingStarOtherMean ends active b u| ≤ B := by
  classical
  by_cases hd : movingStarDegree ends active u = 0
  · simpa [movingStarOtherMean,hd] using hB
  · have hp : 0 < movingStarDegree ends active u :=
      lt_of_le_of_ne (movingStarDegree_nonneg ends active u) (Ne.symm hd)
    unfold movingStarOtherMean
    rw [abs_div,abs_of_pos hp]
    apply (div_le_iff₀ hp).mpr
    calc
      _ ≤ ∑ e ∈ active.filter (fun e => u ∈ ends e), |∑ v ∈ (ends e).erase u, b v| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _e ∈ active.filter (fun e => u ∈ ends e), B := by
        apply Finset.sum_le_sum
        intro e he
        have hu := (Finset.mem_filter.mp he).2
        have hc : ((ends e).erase u).card = 1 := by
          rw [Finset.card_erase_of_mem hu,hends]
        calc
          _ ≤ ∑ v ∈ (ends e).erase u, |b v| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _v ∈ (ends e).erase u, B := Finset.sum_le_sum (fun v _ => hb v)
          _ = B := by simp [hc]
      _ = _ := by simp [movingStarDegree,mul_comm]

lemma movingStarMean_lift {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (active : Finset E) (b : V → ℝ) (u : V)
    (hd : movingStarDegree ends active u ≠ 0) :
    movingStarMean ends active (movingStarLift ends b) u =
      b u + movingStarOtherMean ends active b u := by
  classical
  have he : (∑ e ∈ active.filter (fun e => u ∈ ends e), movingStarLift ends b e) =
      movingStarDegree ends active u*b u +
      ∑ e ∈ active.filter (fun e => u ∈ ends e), ∑ v ∈ (ends e).erase u, b v := by
    calc
      _ = ∑ e ∈ active.filter (fun e => u ∈ ends e), (b u+∑ v ∈ (ends e).erase u, b v) := by
        apply Finset.sum_congr rfl
        intro e he
        exact (Finset.add_sum_erase _ b (Finset.mem_filter.mp he).2).symm
      _ = _ := by simp [Finset.sum_add_distrib,movingStarDegree]
  unfold movingStarMean movingStarOtherMean
  rw [he,add_div,mul_div_cancel_left₀ _ hd]

theorem movingStar_vertex_step_bound {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (hends : ∀ e, (ends e).card = 2) (active : Finset E)
    (b : V → ℝ) (M : E → ℝ) {B R a : ℝ} (hB : 0 ≤ B) (hR : 0 ≤ R)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : ∀ u, |b u| ≤ B)
    (hM : ∀ e ∈ active, |M e| ≤ R) (u : V) :
    |b u + a*movingStarMean ends active (fun e => M e-movingStarLift ends b e) u| ≤ B+a*R := by
  classical
  rw [movingStarMean_sub]
  by_cases hd : movingStarDegree ends active u = 0
  · rw [movingStarMean_zero_degree ends active M u hd,
      movingStarMean_zero_degree ends active (movingStarLift ends b) u hd]
    simp only [sub_self,mul_zero,add_zero]
    exact (hb u).trans (le_add_of_nonneg_right (mul_nonneg ha hR))
  · rw [movingStarMean_lift ends active b u hd]
    have hid : b u+a*(movingStarMean ends active M u-(b u+movingStarOtherMean ends active b u)) =
        (1-a)*b u-a*movingStarOtherMean ends active b u+a*movingStarMean ends active M u := by ring
    rw [hid]
    calc
      _ ≤ |(1-a)*b u-a*movingStarOtherMean ends active b u|+
          |a*movingStarMean ends active M u| := abs_add_le _ _
      _ ≤ (|(1-a)*b u|+|a*movingStarOtherMean ends active b u|)+
          |a*movingStarMean ends active M u| := by
        exact add_le_add (moving_abs_sub_bound _ _) le_rfl
      _ = ((1-a)*|b u|+a*|movingStarOtherMean ends active b u|)+
          a*|movingStarMean ends active M u| := by
        rw [abs_mul,abs_mul,abs_mul,abs_of_nonneg (sub_nonneg.mpr ha1),abs_of_nonneg ha]
      _ ≤ ((1-a)*B+a*B)+a*R := by
        gcongr
        · exact hb u
        · exact movingStarOtherMean_bound ends hends active b u hB hb
        · exact movingStarMean_bound ends active M u hR hM
      _ = _ := by ring

theorem movingStarVertices_bound {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (hends : ∀ e, (ends e).card = 2)
    (active : ℕ → Finset E) (a : ℕ → ℝ) (M : ℕ → E → ℝ) (T : ℕ)
    {R : ℝ} (hR : 0 ≤ R) (ha : ∀ k < T, 0 ≤ a k ∧ a k ≤ 1)
    (hM : ∀ k < T, ∀ e ∈ active k, |M k e| ≤ R) :
    ∀ u, |movingStarVertices ends active a M T u| ≤ R*∑ k ∈ Finset.range T, a k := by
  induction T with
  | zero => intro u; simp [movingStarVertices]
  | succ T ih =>
    have haT := ha T (by omega)
    have hb := ih (fun k hk => ha k (by omega)) (fun k hk => hM k (by omega))
    have hB : 0 ≤ R*∑ k ∈ Finset.range T, a k := by
      exact mul_nonneg hR (Finset.sum_nonneg (fun k hk => (ha k (by have := Finset.mem_range.mp hk; omega)).1))
    intro u
    have hh := movingStar_vertex_step_bound ends hends (active T)
      (movingStarVertices ends active a M T) (M T) hB hR haT.1 haT.2 hb (hM T (by omega)) u
    simpa only [movingStarVertices,Finset.sum_range_succ,mul_add,mul_comm] using hh

theorem movingStar_trajectory_representation {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (active : ℕ → Finset E) (a : ℕ → ℝ)
    (M x : ℕ → E → ℝ) (T : ℕ)
    (hnest : ∀ k < T, active (k+1) ⊆ active k)
    (hinit : ∀ e ∈ active 0, x 0 e = M 0 e)
    (hstep : ∀ k < T, ∀ e ∈ active (k+1), x (k+1) e = x k e -
      a k*movingStarLift ends (movingStarMean ends (active k) (x k)) e + (M (k+1) e-M k e)) :
    ∀ e ∈ active T, x T e = M T e-movingStarLift ends (movingStarVertices ends active a M T) e := by
  induction T with
  | zero => intro e he; simpa [movingStarVertices,movingStarLift] using hinit e he
  | succ T ih =>
    have hx := ih (fun k hk => hnest k (by omega)) (fun k hk => hstep k (by omega))
    have hm := movingStarMean_congr ends (active T) hx
    intro e he
    rw [hstep T (by omega) e he,hx e (hnest T (by omega) he),hm]
    simp only [movingStarVertices,movingStarLift,Finset.sum_add_distrib,Finset.mul_sum]
    ring

theorem movingStar_trajectory_bound {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (hends : ∀ e, (ends e).card = 2)
    (active : ℕ → Finset E) (a : ℕ → ℝ) (M x : ℕ → E → ℝ) (T : ℕ)
    (hnest : ∀ k < T, active (k+1) ⊆ active k)
    (hinit : ∀ e ∈ active 0, x 0 e = M 0 e)
    (hstep : ∀ k < T, ∀ e ∈ active (k+1), x (k+1) e = x k e -
      a k*movingStarLift ends (movingStarMean ends (active k) (x k)) e + (M (k+1) e-M k e))
    {R : ℝ} (hR : 0 ≤ R) (ha : ∀ k < T, 0 ≤ a k ∧ a k ≤ 1)
    (hM : ∀ k ≤ T, ∀ e ∈ active k, |M k e| ≤ R) :
    ∀ e ∈ active T, |x T e| ≤ R*(1+2*∑ k ∈ Finset.range T, a k) := by
  have hb := movingStarVertices_bound ends hends active a M T hR ha (fun k hk => hM k (by omega))
  intro e he
  rw [movingStar_trajectory_representation ends active a M x T hnest hinit hstep e he]
  calc
    _ ≤ |M T e|+|movingStarLift ends (movingStarVertices ends active a M T) e| := moving_abs_sub_bound _ _
    _ ≤ R+2*(R*∑ k ∈ Finset.range T, a k) := add_le_add (hM T le_rfl e he)
      (movingStarLift_bound ends hends _ hb e)
    _ = _ := by ring

lemma movingStar_incidence_swap {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (active : Finset E) (f : E → V → ℝ) :
    (∑ e ∈ active, ∑ u ∈ ends e, f e u) =
      ∑ u, ∑ e ∈ active.filter (fun e => u ∈ ends e), f e u := by
  classical
  have he (e : E) : (∑ u ∈ ends e, f e u) = ∑ u, if u ∈ ends e then f e u else 0 := by simp
  simp_rw [he]
  rw [Finset.sum_comm]
  simp only [Finset.sum_filter]

lemma movingStarMean_mass {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (active : Finset E) (x : E → ℝ) (u : V) :
    movingStarDegree ends active u*movingStarMean ends active x u =
      ∑ e ∈ active.filter (fun e => u ∈ ends e), x e := by
  classical
  by_cases hd : movingStarDegree ends active u = 0
  · have hc : (active.filter (fun e => u ∈ ends e)).card = 0 := by
      exact_mod_cast (show ((active.filter (fun e => u ∈ ends e)).card : ℝ) = 0 from hd)
    have he := Finset.card_eq_zero.mp hc
    simp [movingStarMean,hd,he]
  · unfold movingStarMean
    exact mul_div_cancel₀ _ hd

theorem movingStar_energy_identity {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (active : Finset E) (x : E → ℝ) :
    (∑ e ∈ active, x e*movingStarLift ends (movingStarMean ends active x) e) =
      ∑ u, movingStarDegree ends active u*(movingStarMean ends active x u)^2 := by
  classical
  simp only [movingStarLift,Finset.mul_sum]
  rw [movingStar_incidence_swap]
  apply Finset.sum_congr rfl
  intro u _
  rw [← Finset.sum_mul,← movingStarMean_mass ends active x u]
  ring

lemma movingStar_lift_sq_bound {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (hends : ∀ e, (ends e).card = 2)
    (active : Finset E) (b : V → ℝ) :
    (∑ e ∈ active, (movingStarLift ends b e)^2) ≤
      2*∑ u, movingStarDegree ends active u*(b u)^2 := by
  classical
  calc
    _ ≤ ∑ e ∈ active, 2*∑ u ∈ ends e, (b u)^2 := by
      apply Finset.sum_le_sum
      intro e _
      simpa only [movingStarLift,hends,Nat.cast_ofNat] using
        (sq_sum_le_card_mul_sum_sq (s := ends e) (f := b))
    _ = _ := by
      rw [← Finset.mul_sum,movingStar_incidence_swap]
      congr 1
      apply Finset.sum_congr rfl
      intro u _
      simp [movingStarDegree]

theorem movingStar_euler_energy_le {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (hends : ∀ e, (ends e).card = 2)
    (active : Finset E) (x : E → ℝ) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (∑ e ∈ active, (x e-a*movingStarLift ends (movingStarMean ends active x) e)^2) ≤
      ∑ e ∈ active, (x e)^2 := by
  classical
  let P := movingStarLift ends (movingStarMean ends active x)
  let V := ∑ u, movingStarDegree ends active u*(movingStarMean ends active x u)^2
  have hV : 0 ≤ V := Finset.sum_nonneg (fun u _ =>
    mul_nonneg (movingStarDegree_nonneg ends active u) (sq_nonneg _))
  have hlin : (∑ e ∈ active, x e*P e) = V := movingStar_energy_identity ends active x
  have hsq : (∑ e ∈ active, (P e)^2) ≤ 2*V :=
    movingStar_lift_sq_bound ends hends active (movingStarMean ends active x)
  have hexpand : (∑ e ∈ active, (x e-a*P e)^2) =
      (∑ e ∈ active, (x e)^2)-2*a*(∑ e ∈ active, x e*P e)+
      a^2*(∑ e ∈ active, (P e)^2) := by
    calc
      _ = ∑ e ∈ active, ((x e)^2-2*a*(x e*P e)+a^2*(P e)^2) := by
        apply Finset.sum_congr rfl
        intro e _
        ring
      _ = _ := by simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.mul_sum]
  change (∑ e ∈ active, (x e-a*P e)^2) ≤ _
  rw [hexpand,hlin]
  have hsq' := mul_le_mul_of_nonneg_left hsq (sq_nonneg a)
  have hab : a^2 ≤ a := by nlinarith
  have hb := mul_le_mul_of_nonneg_right hab hV
  nlinarith only [hsq',hb]

end SharpTerminalLeave
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Asymptotics_ActiveL2Map
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators

namespace SharpTerminalLeave
open Classical

lemma activeL2_sq {E : Type*} [Fintype E] (s : Finset E) (x : E → ℝ) :
    (activeL2 s x)^2 = ∑ e ∈ s, (x e)^2 := by
  change ‖activeL2Map s x‖^2 = _
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [activeL2Map]

lemma activeL2_congr {E : Type*} [Fintype E] (s : Finset E) {x y : E → ℝ}
    (h : ∀ e ∈ s, x e = y e) : activeL2 s x = activeL2 s y := by
  have hm : activeL2Map s x = activeL2Map s y := by
    ext e
    by_cases he : e ∈ s
    · simp [activeL2Map,he,h e he]
    · simp [activeL2Map,he]
  change ‖activeL2Map s x‖ = ‖activeL2Map s y‖
  rw [hm]

lemma activeL2_mono {E : Type*} [Fintype E] {s t : Finset E} (h : s ⊆ t) (x : E → ℝ) :
    activeL2 s x ≤ activeL2 t x := by
  have hs : (activeL2 s x)^2 ≤ (activeL2 t x)^2 := by
    rw [activeL2_sq,activeL2_sq]
    exact Finset.sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => sq_nonneg _)
  nlinarith [apply_nonneg (activeL2 s) x,apply_nonneg (activeL2 t) x]

lemma activeL2_coordinate {E : Type*} [Fintype E] (s : Finset E) (x : E → ℝ)
    {e : E} (he : e ∈ s) : |x e| ≤ activeL2 s x := by
  have hs : (x e)^2 ≤ (activeL2 s x)^2 := by
    rw [activeL2_sq]
    exact Finset.single_le_sum (fun _ _ => sq_nonneg _) he
  nlinarith [sq_abs (x e), abs_nonneg (x e),apply_nonneg (activeL2 s) x]

lemma activeL2_of_bound {E : Type*} [Fintype E] (s : Finset E) (x : E → ℝ)
    {R : ℝ} (hR : 0 ≤ R) (hx : ∀ e ∈ s, |x e| ≤ R) :
    activeL2 s x ≤ (Fintype.card E : ℝ)*R := by
  have hs : (activeL2 s x)^2 ≤ (s.card : ℝ)*R^2 := by
    rw [activeL2_sq]
    calc
      _ ≤ ∑ _e ∈ s, R^2 := Finset.sum_le_sum (fun e he => by
        have := hx e he
        nlinarith [sq_abs (x e),abs_nonneg (x e)])
      _ = _ := by simp
  have hn : (s.card : ℝ) ≤ Fintype.card E := by exact_mod_cast Finset.card_le_univ s
  have hn2 : (Fintype.card E : ℝ) ≤ (Fintype.card E : ℝ)^2 := by
    have := Nat.le_mul_self (Fintype.card E)
    exact_mod_cast (by simpa only [pow_two] using this)
  have hp := mul_le_mul_of_nonneg_right (hn.trans hn2) (sq_nonneg R)
  have h0 : 0 ≤ (Fintype.card E : ℝ)*R := mul_nonneg (Nat.cast_nonneg _) hR
  nlinarith [apply_nonneg (activeL2 s) x]

lemma movingStar_euler_activeL2 {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (hends : ∀ e, (ends e).card = 2)
    (s : Finset E) (x : E → ℝ) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    activeL2 s (fun e => x e-a*movingStarLift ends (movingStarMean ends s x) e) ≤ activeL2 s x := by
  have hs := movingStar_euler_energy_le ends hends s x ha ha1
  rw [← activeL2_sq,← activeL2_sq] at hs
  nlinarith [apply_nonneg (activeL2 s) x,
    apply_nonneg (activeL2 s) (fun e => x e-a*movingStarLift ends (movingStarMean ends s x) e)]

lemma movingStar_activeL2_bound {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (hends : ∀ e, (ends e).card = 2)
    (s : Finset E) (x : E → ℝ) :
    activeL2 s (movingStarLift ends (movingStarMean ends s x)) ≤ 2*activeL2 s x := by
  let P := movingStarLift ends (movingStarMean ends s x)
  have hi : P = x-(x-P) := by funext e; simp
  have he := movingStar_euler_activeL2 ends hends s x (a := 1) (by norm_num) le_rfl
  simp only [one_mul] at he
  calc
    activeL2 s P = activeL2 s (x-(x-P)) := congrArg _ hi
    _ ≤ activeL2 s x+activeL2 s (x-P) := map_sub_le_add _ _ _
    _ ≤ activeL2 s x+activeL2 s x := add_le_add le_rfl he
    _ = _ := by ring

theorem movingStar_trajectory_l2_bound {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (hends : ∀ e, (ends e).card = 2)
    (active : ℕ → Finset E) (a : ℕ → ℝ) (M x : ℕ → E → ℝ) (T : ℕ)
    (hnest : ∀ k < T, active (k+1) ⊆ active k)
    (hinit : ∀ e ∈ active 0, x 0 e = M 0 e)
    (hstep : ∀ k < T, ∀ e ∈ active (k+1), x (k+1) e = x k e -
      a k*movingStarLift ends (movingStarMean ends (active k) (x k)) e + (M (k+1) e-M k e))
    {R : ℝ} (_hR : 0 ≤ R) (ha : ∀ k < T, 0 ≤ a k ∧ a k ≤ 1)
    (hM : ∀ k ≤ T, activeL2 (active k) (M k) ≤ R) :
    activeL2 (active T) (x T) ≤ R*(1+2*∑ k ∈ Finset.range T, a k) := by
  let z : ℕ → E → ℝ := fun k => x k-M k
  have hz : ∀ t ≤ T, activeL2 (active t) (z t) ≤ 2*R*∑ k ∈ Finset.range t, a k := by
    intro t ht
    induction t with
    | zero =>
      have he : activeL2 (active 0) (z 0) = 0 := by
        trans activeL2 (active 0) 0
        · apply activeL2_congr
          intro e he
          simp [z,hinit e he]
        · exact map_zero _
      simpa only [he, Finset.range_zero, Finset.sum_empty, mul_zero] using (le_refl (0 : ℝ))
    | succ t ih =>
      have htT : t < T := by omega
      have hi := ih (by omega)
      have hzstep : ∀ e ∈ active (t+1), z (t+1) e =
          (z t e-a t*movingStarLift ends (movingStarMean ends (active t) (z t)) e)-
            a t*movingStarLift ends (movingStarMean ends (active t) (M t)) e := by
        intro e he
        have hx : x t = z t+M t := by funext e; simp [z]
        have hp := hstep t htT e he
        rw [hx] at hp
        have hm : movingStarMean ends (active t) (z t+M t) =
            movingStarMean ends (active t) (z t)+movingStarMean ends (active t) (M t) := by
          funext u
          exact movingStarMean_add ends (active t) (z t) (M t) u
        rw [hm,movingStarLift_add] at hp
        change x (t+1) e-M (t+1) e = _
        simp only [Pi.add_apply] at hp
        linarith only [hp]
      calc
        activeL2 (active (t+1)) (z (t+1)) = activeL2 (active (t+1))
          ((fun e => z t e-a t*movingStarLift ends (movingStarMean ends (active t) (z t)) e)-
            a t • movingStarLift ends (movingStarMean ends (active t) (M t))) :=
              activeL2_congr _ hzstep
        _ ≤ activeL2 (active t)
          ((fun e => z t e-a t*movingStarLift ends (movingStarMean ends (active t) (z t)) e)-
            a t • movingStarLift ends (movingStarMean ends (active t) (M t))) :=
              activeL2_mono (hnest t htT) _
        _ ≤ activeL2 (active t)
          (fun e => z t e-a t*movingStarLift ends (movingStarMean ends (active t) (z t)) e)+
            activeL2 (active t) (a t • movingStarLift ends (movingStarMean ends (active t) (M t))) :=
              map_sub_le_add _ _ _
        _ ≤ activeL2 (active t) (z t)+a t*(2*activeL2 (active t) (M t)) := by
          rw [map_smul_eq_mul,Real.norm_eq_abs,abs_of_nonneg (ha t htT).1]
          exact add_le_add (movingStar_euler_activeL2 ends hends _ _ (ha t htT).1 (ha t htT).2)
            (mul_le_mul_of_nonneg_left (movingStar_activeL2_bound ends hends _ _) (ha t htT).1)
        _ ≤ 2*R*∑ k ∈ Finset.range t, a k+a t*(2*R) := by
          exact add_le_add hi (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hM t (by omega)) (by norm_num)) (ha t htT).1)
        _ = _ := by rw [Finset.sum_range_succ]; ring
  have hx : x T = M T+z T := by funext e; simp [z]
  calc
    activeL2 (active T) (x T) = activeL2 (active T) (M T+z T) := congrArg _ hx
    _ ≤ activeL2 (active T) (M T)+activeL2 (active T) (z T) := map_add_le_add _ _ _
    _ ≤ R+2*R*∑ k ∈ Finset.range T, a k := add_le_add (hM T le_rfl) (hz T le_rfl)
    _ = _ := by ring

lemma activeLinf_coordinate {E : Type*} [Fintype E] (s : Finset E) (x : E → ℝ)
    {e : E} (he : e ∈ s) : |x e| ≤ activeLinf s x := by
  exact Seminorm.le_finset_sup_apply (p := fun e =>
    (normSeminorm ℝ ℝ).comp (LinearMap.proj e)) (x := x) he

lemma activeLinf_bound {E : Type*} [Fintype E] (s : Finset E) (x : E → ℝ)
    {R : ℝ} (hR : 0 ≤ R) (hx : ∀ e ∈ s, |x e| ≤ R) : activeLinf s x ≤ R := by
  exact Seminorm.finset_sup_apply_le hR hx

lemma activeLinf_le_l2 {E : Type*} [Fintype E] (s : Finset E) (x : E → ℝ) :
    activeLinf s x ≤ activeL2 s x :=
  activeLinf_bound s x (apply_nonneg _ _) (fun _ he => activeL2_coordinate s x he)

lemma activeL2_le_card_linf {E : Type*} [Fintype E] (s : Finset E) (x : E → ℝ) :
    activeL2 s x ≤ (Fintype.card E : ℝ)*activeLinf s x :=
  activeL2_of_bound s x (apply_nonneg _ _) (fun _ he => activeLinf_coordinate s x he)

lemma trajectorySeminorm_at {E : Type*} [Fintype E]
    (P : ℕ → Seminorm ℝ (E → ℝ)) (T : ℕ) (x : ℕ → E → ℝ) {t : ℕ} (ht : t ≤ T) :
    P t (x t) ≤ trajectorySeminorm P T x :=
  Seminorm.le_finset_sup_apply (p := fun t => (P t).comp (LinearMap.proj t))
    (x := x) (Finset.mem_range.mpr (by omega))

lemma trajectorySeminorm_bound {E : Type*} [Fintype E]
    (P : ℕ → Seminorm ℝ (E → ℝ)) (T : ℕ) (x : ℕ → E → ℝ) {R : ℝ}
    (hR : 0 ≤ R) (hx : ∀ t ≤ T, P t (x t) ≤ R) : trajectorySeminorm P T x ≤ R := by
  apply Seminorm.finset_sup_apply_le hR
  intro t ht
  exact hx t (by have := Finset.mem_range.mp ht; omega)

lemma trajectory_mixed_seminorms {E : Type*} [Fintype E]
    (active : ℕ → Finset E) (T : ℕ) (x : ℕ → E → ℝ) :
    trajectorySeminorm (fun t => activeLinf (active t)) T x ≤
      trajectorySeminorm (fun t => activeL2 (active t)) T x ∧
    trajectorySeminorm (fun t => activeL2 (active t)) T x ≤
      (Fintype.card E : ℝ)*trajectorySeminorm (fun t => activeLinf (active t)) T x := by
  constructor
  · apply trajectorySeminorm_bound _ _ _ (apply_nonneg _ _)
    intro t ht
    exact (activeLinf_le_l2 _ _).trans (trajectorySeminorm_at (fun t => activeL2 (active t)) T x ht)
  · apply trajectorySeminorm_bound _ _ _ (by positivity)
    intro t ht
    exact (activeL2_le_card_linf _ _).trans
      (mul_le_mul_of_nonneg_left (trajectorySeminorm_at (fun t => activeLinf (active t)) T x ht) (Nat.cast_nonneg _))

lemma movingStarResponse_linf {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (hends : ∀ e, (ends e).card = 2)
    (active : ℕ → Finset E) (a : ℕ → ℝ) (T : ℕ)
    (hnest : ∀ k < T, active (k+1) ⊆ active k)
    (ha : ∀ k < T, 0 ≤ a k ∧ a k ≤ 1) (M : ℕ → E → ℝ) :
    trajectorySeminorm (fun t => activeLinf (active t)) T (movingStarResponse ends active a M) ≤
      (1+2*∑ k ∈ Finset.range T, a k)*trajectorySeminorm (fun t => activeLinf (active t)) T M := by
  let R := trajectorySeminorm (fun t => activeLinf (active t)) T M
  have hR : 0 ≤ R := apply_nonneg _ _
  have hsum : ∀ t ≤ T, (∑ k ∈ Finset.range t, a k) ≤ ∑ k ∈ Finset.range T, a k := by
    intro t ht
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono ht)
      (fun k hk _ => (ha k (Finset.mem_range.mp hk)).1)
  have hS : 0 ≤ ∑ k ∈ Finset.range T, a k :=
    Finset.sum_nonneg (fun k hk => (ha k (Finset.mem_range.mp hk)).1)
  apply trajectorySeminorm_bound _ _ _ (by positivity)
  intro t ht
  apply activeLinf_bound _ _ (by positivity)
  intro e he
  have hb := movingStar_trajectory_bound ends hends active a M
    (movingStarSolve ends active a M) t (fun k hk => hnest k (by omega))
    (fun _ _ => rfl) (fun _ _ _ _ => rfl) hR (fun k hk => ha k (by omega))
    (fun k hk f hf => (activeLinf_coordinate _ _ hf).trans (trajectorySeminorm_at (fun t => activeLinf (active t)) T M (by omega))) e he
  exact hb.trans (by nlinarith [mul_le_mul_of_nonneg_left (hsum t ht) hR])

lemma movingStarResponse_l2 {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (hends : ∀ e, (ends e).card = 2)
    (active : ℕ → Finset E) (a : ℕ → ℝ) (T : ℕ)
    (hnest : ∀ k < T, active (k+1) ⊆ active k)
    (ha : ∀ k < T, 0 ≤ a k ∧ a k ≤ 1) (M : ℕ → E → ℝ) :
    trajectorySeminorm (fun t => activeL2 (active t)) T (movingStarResponse ends active a M) ≤
      (1+2*∑ k ∈ Finset.range T, a k)*trajectorySeminorm (fun t => activeL2 (active t)) T M := by
  let R := trajectorySeminorm (fun t => activeL2 (active t)) T M
  have hR : 0 ≤ R := apply_nonneg _ _
  have hsum : ∀ t ≤ T, (∑ k ∈ Finset.range t, a k) ≤ ∑ k ∈ Finset.range T, a k := by
    intro t ht
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono ht)
      (fun k hk _ => (ha k (Finset.mem_range.mp hk)).1)
  have hS : 0 ≤ ∑ k ∈ Finset.range T, a k :=
    Finset.sum_nonneg (fun k hk => (ha k (Finset.mem_range.mp hk)).1)
  apply trajectorySeminorm_bound _ _ _ (by positivity)
  intro t ht
  have hb := movingStar_trajectory_l2_bound ends hends active a M
    (movingStarSolve ends active a M) t (fun k hk => hnest k (by omega))
    (fun _ _ => rfl) (fun _ _ _ _ => rfl) hR (fun k hk => ha k (by omega))
    (fun k hk => trajectorySeminorm_at (fun t => activeL2 (active t)) T M (by omega))
  exact hb.trans (by nlinarith [mul_le_mul_of_nonneg_left (hsum t ht) hR])

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Asymptotics_LogStepSandwich
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators

namespace SharpTerminalLeave

lemma log_step_sandwich {p q h : ℝ} (hp : 0 < p) (hq : 0 < q) (hs : p = q+h) :
    h/p ≤ Real.log p-Real.log q ∧ Real.log p-Real.log q ≤ h/q := by
  have hl := Real.log_le_sub_one_of_pos (div_pos hq hp)
  have hu := Real.log_le_sub_one_of_pos (div_pos hp hq)
  rw [Real.log_div (ne_of_gt hq) (ne_of_gt hp)] at hl
  rw [Real.log_div (ne_of_gt hp) (ne_of_gt hq)] at hu
  have he₁ : q/p-1 = -(h/p) := by field_simp; linarith only [hs]
  have he₂ : p/q-1 = h/q := by field_simp; linarith only [hs]
  rw [he₁] at hl
  rw [he₂] at hu
  exact ⟨by linarith only [hl],hu⟩

theorem density_log_sum_bounds (p : ℕ → ℝ) (h : ℝ) (T : ℕ)
    (hp : ∀ i ≤ T, 0 < p i) (hs : ∀ i < T, p i = p (i+1)+h) :
    (∑ i ∈ Finset.range T, h/p i) ≤ Real.log (p 0)-Real.log (p T) ∧
    Real.log (p 0)-Real.log (p T) ≤
      (∑ i ∈ Finset.range T, h/p i)+(h/p T-h/p 0) := by
  induction T with
  | zero => simp
  | succ T ih =>
    obtain ⟨hl,hu⟩ := ih (fun i hi => hp i (by omega)) (fun i hi => hs i (by omega))
    obtain ⟨sl,su⟩ := log_step_sandwich (hp T (by omega)) (hp (T+1) le_rfl) (hs T (by omega))
    rw [Finset.sum_range_succ]
    constructor <;> linarith only [hl,hu,sl,su]

lemma inverse_square_grid_step {a p q h : ℝ} (ha : 0 < a) (hp : 0 < p) (hq : 0 < q)
    (hh : 0 ≤ h) (hs : p = q+h) :
    2*h/(a*p^3) ≤ 1/(a*q^2)-1/(a*p^2) := by
  have hpq : q ≤ p := by linarith only [hs,hh]
  have hc : 2*q^2 ≤ p*(p+q) := by nlinarith [mul_nonneg (sub_nonneg.mpr hpq) (by linarith : 0 ≤ p+2*q)]
  have hm := mul_le_mul_of_nonneg_left hc hh
  have he : p^2-q^2 = h*(p+q) := by rw [hs]; ring
  apply (div_le_iff₀ (mul_pos ha (pow_pos hp 3))).mpr
  have hd : (1/(a*q^2)-1/(a*p^2))*(a*p^3) = (p^2-q^2)*p/q^2 := by
    field_simp
  rw [hd,he]
  apply (le_div_iff₀ (pow_pos hq 2)).mpr
  nlinarith only [hm]

theorem inverse_square_grid_sum (p : ℕ → ℝ) (a h : ℝ) (T : ℕ)
    (ha : 0 < a) (hh : 0 ≤ h) (hp : ∀ i ≤ T, 0 < p i)
    (hs : ∀ i < T, p i = p (i+1)+h) :
    (∑ i ∈ Finset.range T, 2*h/(a*p i^3)) ≤ 1/(a*p T^2)-1/(a*p 0^2) := by
  induction T with
  | zero => simp
  | succ T ih =>
    have hi := ih (fun i hi => hp i (by omega)) (fun i hi => hs i (by omega))
    have hstep := inverse_square_grid_step ha (hp T (by omega)) (hp (T+1) le_rfl) hh (hs T (by omega))
    rw [Finset.sum_range_succ]
    linarith only [hi,hstep]

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Probability_FiniteMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem pmf_weight_sum {α : Type*} [Fintype α] (p : PMF α) :
    ∑ a, (p a).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun a _ => p.apply_ne_top a)]
  have h : ∑ a, p a = 1 := by simpa only [tsum_fintype] using p.tsum_coe
  rw [h, ENNReal.toReal_one]

@[simp] theorem pmfMean_const {α : Type*} [Fintype α] (p : PMF α) (c : ℝ) :
    pmfMean p (fun _ => c) = c := by
  simp only [pmfMean, ← Finset.sum_mul, pmf_weight_sum, one_mul]

theorem pmfMean_congr {α : Type*} [Fintype α] (p : PMF α) {f g : α → ℝ}
    (h : ∀ a ∈ p.support, f a = g a) : pmfMean p f = pmfMean p g := by
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · have hz : p a = 0 := by simpa only [PMF.mem_support_iff, not_not] using ha
    simp [hz]

theorem pmfMean_mul_const {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ) (c : ℝ) :
    pmfMean p (fun a => f a * c) = pmfMean p f * c := by
  simp only [pmfMean, ← mul_assoc, ← Finset.sum_mul]

theorem pmfMean_bind {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (q : α → PMF β) (f : β → ℝ) :
    pmfMean (p.bind q) f = pmfMean p (fun a => pmfMean (q a) f) := by
  classical
  simp only [pmfMean, PMF.bind_apply, tsum_fintype]
  have hfin (b : β) (a : α) : p a * q a b ≠ ⊤ :=
    ENNReal.mul_ne_top (p.apply_ne_top a) ((q a).apply_ne_top b)
  simp_rw [ENNReal.toReal_sum (fun a _ => hfin _ a), Finset.sum_mul,
    ENNReal.toReal_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

@[simp] theorem pmfMean_map {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (g : α → β) (f : β → ℝ) :
    pmfMean (p.map g) f = pmfMean p (fun a => f (g a)) := by
  rw [← PMF.bind_pure_comp, pmfMean_bind]
  simp

theorem pmfMean_uniformOfFinset {α : Type*} [Fintype α]
    (s : Finset α) (hs : s.Nonempty) (f : α → ℝ) :
    pmfMean (PMF.uniformOfFinset s hs) f = (∑ a ∈ s, f a) / (s.card : ℝ) := by
  classical
  simp only [pmfMean, PMF.uniformOfFinset_apply]
  simp_rw [apply_ite ENNReal.toReal, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_zero, ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_univ_mem]
  simp only [div_eq_mul_inv, mul_comm, Finset.sum_mul]

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_TerminalLaw
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem triangle_edge_card {n : ℕ} {G : Graph n} {t : Finset (Fin n)}
    (ht : t ∈ triangles G) : (t.powersetCard 2).card = 3 := by
  rw [Finset.card_powersetCard, (mem_triangles.mp ht).1]
  decide

theorem step_card_of_active {n : ℕ} {G H : Graph n}
    (hG : (triangles G).Nonempty) (h : H ∈ (step G).support) :
    H.card + 3 = G.card := by
  obtain ⟨t, ht, rfl⟩ := (step_support_active hG).mp h
  have hc := Finset.card_sdiff_add_card_eq_card (mem_triangles.mp ht).2
  rwa [triangle_edge_card ht] at hc

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_TriangleDrift
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem pmfMean_sum {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (f : β → α → ℝ) :
    pmfMean p (fun a => ∑ b, f b a) = ∑ b, pmfMean p (f b) := by
  simp only [pmfMean, Finset.mul_sum]
  exact Finset.sum_comm

theorem step_mean {n : ℕ} (G : Graph n) (f : Graph n → ℝ)
    (hG : (triangles G).Nonempty) :
    pmfMean (step G) f =
      (∑ t ∈ triangles G, f (G \ t.powersetCard 2)) / ((triangles G).card : ℝ) := by
  rw [step, dite_eq_left hG, pmfMean_map, pmfMean_uniformOfFinset]

theorem intact_delete {n : ℕ} {G F : Graph n} (hF : F ⊆ G)
    (t : Finset (Fin n)) :
    intact F (G \ t.powersetCard 2) =
      1 - if ¬ Disjoint F (t.powersetCard 2) then 1 else 0 := by
  classical
  simp only [intact, Finset.subset_sdiff, hF, true_and]
  split_ifs <;> simp_all

theorem step_mean_intact {n : ℕ} {G F : Graph n} (hF : F ⊆ G)
    (hG : (triangles G).Nonempty) :
    pmfMean (step G) (intact F) =
      1 - ((hittingTriangles G F).card : ℝ) / ((triangles G).card : ℝ) := by
  classical
  rw [step_mean G (intact F) hG]
  simp_rw [intact_delete hF]
  rw [Finset.sum_sub_distrib]
  have hb : (∑ t ∈ triangles G, if ¬ Disjoint F (t.powersetCard 2) then (1 : ℝ) else 0) =
      ((hittingTriangles G F).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp [hittingTriangles]
  rw [hb]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [sub_div, div_self (by exact_mod_cast hG.card_pos.ne')]

theorem step_mean_intact_of_not_subset {n : ℕ} {G F : Graph n}
    (hF : ¬ F ⊆ G) : pmfMean (step G) (intact F) = 0 := by
  rw [← pmfMean_const (step G) 0]
  apply pmfMean_congr
  intro H hH
  have hFH : ¬ F ⊆ H := fun h => hF (h.trans (step_support_subset hH))
  simp [intact, hFH]

theorem step_mean_copyCount {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (G : Graph n) (hG : (triangles G).Nonempty) :
    pmfMean (step G) (copyCount required) = copyCount required G -
      (∑ a, if required a ⊆ G then ((hittingTriangles G (required a)).card : ℝ) else 0) /
        ((triangles G).card : ℝ) := by
  classical
  unfold copyCount
  rw [pmfMean_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : required a ⊆ G
  · rw [step_mean_intact ha hG, ite_eq_left ha, intact, ite_eq_left ha]
  · rw [step_mean_intact_of_not_subset ha, ite_eq_right ha, intact, ite_eq_right ha]
    simp

theorem three_le_card_union {α : Type*} [DecidableEq α]
    {e f : Finset α} (he : e.card = 2) (hf : f.card = 2) (hef : e ≠ f) :
    3 ≤ (e ∪ f).card := by
  have hi : (e ∩ f).card < 2 := by
    by_contra h
    have hge : 2 ≤ (e ∩ f).card := by omega
    have heq : e ∩ f = e := Finset.eq_of_subset_of_card_le
      Finset.inter_subset_left (by omega)
    have hfq : e ∩ f = f := Finset.eq_of_subset_of_card_le
      Finset.inter_subset_right (by omega)
    exact hef (heq.symm.trans hfq)
  have h := Finset.card_union_add_card_inter e f
  omega

theorem triangle_eq_of_two_edges {α : Type*} [DecidableEq α]
    {t u e f : Finset α} (ht : t.card = 3) (hu : u.card = 3)
    (he : e.card = 2) (hf : f.card = 2) (hef : e ≠ f)
    (het : e ⊆ t) (hft : f ⊆ t) (heu : e ⊆ u) (hfu : f ⊆ u) : t = u := by
  have hm := three_le_card_union he hf hef
  have ht' : e ∪ f = t := Finset.eq_of_subset_of_card_le
    (Finset.union_subset het hft) (by omega)
  have hu' : e ∪ f = u := Finset.eq_of_subset_of_card_le
    (Finset.union_subset heu hfu) (by omega)
  exact ht'.symm.trans hu'

theorem hittingTriangles_eq_biUnion {n : ℕ} (G F : Graph n) :
    hittingTriangles G F = F.biUnion (incidentTriangles G) := by
  classical
  ext t
  simp only [hittingTriangles, Finset.mem_filter, Finset.mem_biUnion,
    incidentTriangles, Finset.not_disjoint_iff]
  constructor
  · rintro ⟨ht, e, heF, het⟩
    exact ⟨e, heF, ht, het⟩
  · rintro ⟨e, heF, ht, het⟩
    exact ⟨ht, e, heF, het⟩

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_TriangleDegreeMean
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma triangles_delete_eq_sdiff_hitting {n : ℕ} (G : Graph n) (t : Finset (Fin n)) :
    triangles (G \ t.powersetCard 2) = triangles G \ hittingTriangles G (t.powersetCard 2) := by
  ext u
  simp only [mem_triangles, hittingTriangles, Finset.mem_sdiff, Finset.mem_filter]
  constructor
  · rintro ⟨hu,hs⟩
    refine ⟨⟨hu, fun e he => (Finset.mem_sdiff.mp (hs he)).1⟩, ?_⟩
    rintro ⟨_,hd⟩
    apply hd
    apply Finset.disjoint_left.mpr
    intro e het heu
    exact (Finset.mem_sdiff.mp (hs heu)).2 het
  · rintro ⟨⟨hu,hs⟩,hn⟩
    refine ⟨hu, ?_⟩
    intro e he
    refine Finset.mem_sdiff.mpr ⟨hs he, ?_⟩
    intro het
    apply hn
    refine ⟨⟨hu,hs⟩, ?_⟩
    exact fun hd => Finset.disjoint_left.mp hd het he

lemma triangle_edge_inter_card_le_one {n : ℕ} {G : Graph n}
    {t u : Finset (Fin n)} (ht : t ∈ triangles G) (hu : u ∈ triangles G)
    (hne : t ≠ u) : (t.powersetCard 2 ∩ u.powersetCard 2).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro e he f hf
  by_contra hef
  apply hne
  have he' := Finset.mem_inter.mp he
  have hf' := Finset.mem_inter.mp hf
  exact triangle_eq_of_two_edges (mem_triangles.mp ht).1 (mem_triangles.mp hu).1
    (Finset.mem_powersetCard.mp he'.1).2 (Finset.mem_powersetCard.mp hf'.1).2 hef
    (Finset.mem_powersetCard.mp he'.1).1 (Finset.mem_powersetCard.mp hf'.1).1
    (Finset.mem_powersetCard.mp he'.2).1 (Finset.mem_powersetCard.mp hf'.2).1

lemma triangle_incidence_swap {n : ℕ} (G : Graph n) (f : Finset (Fin n) → ℝ) :
    (∑ t ∈ triangles G, ∑ e ∈ t.powersetCard 2, f e) =
      ∑ e ∈ G, (triangleDegree G e : ℝ) * f e := by
  classical
  calc
    _ = ∑ t ∈ triangles G, ∑ e ∈ G, if e ∈ t.powersetCard 2 then f e else 0 := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [← Finset.sum_filter]
      congr 1
      ext e
      simp only [Finset.mem_filter]
      exact ⟨fun he => ⟨(mem_triangles.mp ht).2 he,he⟩, fun he => he.2⟩
    _ = ∑ e ∈ G, ∑ t ∈ triangles G, if e ∈ t.powersetCard 2 then f e else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e he
      rw [← Finset.sum_filter]
      simp [triangleDegree, incidentTriangles, mul_comm]

lemma triangle_degree_sum {n : ℕ} (G : Graph n) :
    (∑ e ∈ G, (triangleDegree G e : ℝ)) = 3 * (triangles G).card := by
  have h := triangle_incidence_swap G (fun _ => (1 : ℝ))
  simp only [mul_one, Finset.sum_const, nsmul_eq_mul] at h
  calc
    _ = ∑ t ∈ triangles G, ((t.powersetCard 2).card : ℝ) := h.symm
    _ = ∑ _t ∈ triangles G, (3 : ℝ) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [triangle_edge_card ht]
      norm_num
    _ = _ := by simp; ring

lemma triangle_incidence_sum_on {n : ℕ} (G F : Graph n) :
    (∑ e ∈ F, (triangleDegree G e : ℝ)) =
      ∑ t ∈ triangles G, ((F ∩ t.powersetCard 2).card : ℝ) := by
  classical
  have he (e : Finset (Fin n)) : (triangleDegree G e : ℝ) =
      ∑ t ∈ triangles G, if e ∈ t.powersetCard 2 then (1 : ℝ) else 0 := by
    simp [triangleDegree, incidentTriangles, Finset.sum_boole]
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  simp only [Finset.sum_boole]
  congr 1

lemma triangle_hit_multiplicity {n : ℕ} {G : Graph n} {t u : Finset (Fin n)}
    (ht : t ∈ triangles G) (hu : u ∈ triangles G) :
    ((t.powersetCard 2 ∩ u.powersetCard 2).card : ℝ) =
      (if u ∈ hittingTriangles G (t.powersetCard 2) then 1 else 0) +
      (if u = t then 2 else 0) := by
  classical
  by_cases hut : u = t
  · subst u
    have hhit : t ∈ hittingTriangles G (t.powersetCard 2) := by
      apply Finset.mem_filter.mpr
      refine ⟨ht, ?_⟩
      intro hd
      have hzero : t.powersetCard 2 = ∅ := disjoint_self.mp hd
      have hc := triangle_edge_card ht
      rw [hzero,Finset.card_empty] at hc
      omega
    norm_num [hhit, triangle_edge_card ht]
  · by_cases hhit : u ∈ hittingTriangles G (t.powersetCard 2)
    · have hnon : (t.powersetCard 2 ∩ u.powersetCard 2).Nonempty := by
        exact Finset.not_disjoint_iff_nonempty_inter.mp (Finset.mem_filter.mp hhit).2
      have hcard : (t.powersetCard 2 ∩ u.powersetCard 2).card = 1 := by
        exact Nat.le_antisymm (triangle_edge_inter_card_le_one ht hu (Ne.symm hut))
          (Finset.one_le_card.mpr hnon)
      simp [hhit,hut,hcard]
    · have hd : Disjoint (t.powersetCard 2) (u.powersetCard 2) := by
        by_contra hn
        exact hhit (Finset.mem_filter.mpr ⟨hu,hn⟩)
      simp [hhit,hut,Finset.disjoint_iff_inter_eq_empty.mp hd]

theorem triangle_hitting_card_exact {n : ℕ} {G : Graph n} {t : Finset (Fin n)}
    (ht : t ∈ triangles G) :
    ((hittingTriangles G (t.powersetCard 2)).card : ℝ) =
      (∑ e ∈ t.powersetCard 2, (triangleDegree G e : ℝ)) - 2 := by
  classical
  rw [triangle_incidence_sum_on]
  have hm : (∑ u ∈ triangles G, ((t.powersetCard 2 ∩ u.powersetCard 2).card : ℝ)) =
      ((hittingTriangles G (t.powersetCard 2)).card : ℝ) + 2 := by
    calc
      _ = ∑ u ∈ triangles G,
          ((if u ∈ hittingTriangles G (t.powersetCard 2) then (1 : ℝ) else 0) +
          (if u = t then 2 else 0)) := by
        apply Finset.sum_congr rfl
        exact fun u hu => triangle_hit_multiplicity ht hu
      _ = _ := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_boole,Finset.sum_ite_eq',ht,ite_true]
        have hf : (triangles G).filter (fun u => u ∈ hittingTriangles G (t.powersetCard 2)) =
            hittingTriangles G (t.powersetCard 2) := by
          ext u
          simp only [hittingTriangles,Finset.mem_filter]
          tauto
        rw [hf]
  linarith

theorem triangle_count_delete {n : ℕ} {G : Graph n} {t : Finset (Fin n)}
    (ht : t ∈ triangles G) :
    ((triangles (G \ t.powersetCard 2)).card : ℝ) =
      (triangles G).card - (∑ e ∈ t.powersetCard 2, (triangleDegree G e : ℝ)) + 2 := by
  have hsub : hittingTriangles G (t.powersetCard 2) ⊆ triangles G := Finset.filter_subset _ _
  rw [triangles_delete_eq_sdiff_hitting,Finset.card_sdiff_of_subset hsub,
    Nat.cast_sub (Finset.card_le_card hsub), triangle_hitting_card_exact ht]
  ring

theorem step_mean_triangle_count {n : ℕ} {G : Graph n}
    (hQ : (triangles G).Nonempty) :
    pmfMean (step G) (fun H => ((triangles H).card : ℝ)) =
      (triangles G).card - (∑ e ∈ G, (triangleDegree G e : ℝ)^2) /
        (triangles G).card + 2 := by
  classical
  rw [step_mean G _ hQ]
  have he : (∑ t ∈ triangles G, ((triangles (G \ t.powersetCard 2)).card : ℝ)) =
      (triangles G).card * ((triangles G).card + 2 : ℝ) -
      ∑ e ∈ G, (triangleDegree G e : ℝ)^2 := by
    calc
      _ = ∑ t ∈ triangles G, (((triangles G).card : ℝ) + 2 -
          ∑ e ∈ t.powersetCard 2, (triangleDegree G e : ℝ)) := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [triangle_count_delete ht]
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib,triangle_incidence_swap]
        simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, pow_two]
        ring
  rw [he]
  have hq : ((triangles G).card : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hQ.card_pos
  field_simp
  ring

lemma triangleDegreeVariance_nonneg {n : ℕ} (G : Graph n) :
    0 ≤ triangleDegreeVariance G := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma triangleDegreeMean_mass {n : ℕ} {G : Graph n} (hG : G.Nonempty) :
    (G.card : ℝ) * triangleDegreeMean G = 3 * (triangles G).card := by
  have hm : (G.card : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hG.card_pos
  unfold triangleDegreeMean
  field_simp

theorem triangle_degree_second_moment {n : ℕ} {G : Graph n} (hG : G.Nonempty) :
    (∑ e ∈ G, (triangleDegree G e : ℝ)^2) =
      triangleDegreeVariance G + (G.card : ℝ)*(triangleDegreeMean G)^2 := by
  have hlin := triangle_degree_sum G
  have hm := triangleDegreeMean_mass hG
  have hv : triangleDegreeVariance G =
      (∑ e ∈ G, (triangleDegree G e : ℝ)^2) -
      2*triangleDegreeMean G*(∑ e ∈ G, (triangleDegree G e : ℝ)) +
      (G.card : ℝ)*(triangleDegreeMean G)^2 := by
    unfold triangleDegreeVariance
    calc
      _ = ∑ e ∈ G, ((triangleDegree G e : ℝ)^2 -
          2*triangleDegreeMean G*(triangleDegree G e : ℝ) + (triangleDegreeMean G)^2) := by
        apply Finset.sum_congr rfl
        intro e _
        ring
      _ = _ := by simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,
        Finset.mul_sum,Finset.sum_const,nsmul_eq_mul]
  rw [hlin, ← hm] at hv
  nlinarith only [hv]

lemma graph_nonempty_of_triangles {n : ℕ} {G : Graph n} (hQ : (triangles G).Nonempty) :
    G.Nonempty := by
  obtain ⟨t,ht⟩ := hQ
  have hc := triangle_edge_card ht
  have he : (t.powersetCard 2).Nonempty := Finset.card_pos.mp (by omega)
  exact he.mono (mem_triangles.mp ht).2

theorem step_mean_triangle_count_centered {n : ℕ} {G : Graph n}
    (hQ : (triangles G).Nonempty) :
    pmfMean (step G) (fun H => ((triangles H).card : ℝ)) =
      (triangles G).card - 9*(triangles G).card / G.card -
      triangleDegreeVariance G / (triangles G).card + 2 := by
  rw [step_mean_triangle_count hQ, triangle_degree_second_moment (graph_nonempty_of_triangles hQ)]
  have hq : ((triangles G).card : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hQ.card_pos
  have hm : (G.card : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (graph_nonempty_of_triangles hQ).card_pos
  unfold triangleDegreeMean
  field_simp
  ring

lemma triangle_degree_variance_shift {n : ℕ} {G : Graph n} (hG : G.Nonempty) (d : ℝ) :
    (∑ e ∈ G, ((triangleDegree G e : ℝ)-d)^2) =
      triangleDegreeVariance G + (G.card : ℝ)*(triangleDegreeMean G-d)^2 := by
  have hlin := triangle_degree_sum G
  have hm := triangleDegreeMean_mass hG
  have hsec := triangle_degree_second_moment hG
  calc
    _ = (∑ e ∈ G, (triangleDegree G e : ℝ)^2) -
        2*d*(∑ e ∈ G, (triangleDegree G e : ℝ))+(G.card : ℝ)*d^2 := by
      calc
        _ = ∑ e ∈ G, ((triangleDegree G e : ℝ)^2 - 2*d*(triangleDegree G e : ℝ) + d^2) := by
          apply Finset.sum_congr rfl
          intro e _
          ring
        _ = _ := by simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,
          Finset.mul_sum,Finset.sum_const,nsmul_eq_mul]
    _ = _ := by rw [hsec,hlin,← hm]; ring

lemma triangle_degree_variance_le {n : ℕ} {G : Graph n} (hG : G.Nonempty)
    (d δ : ℝ) (hδ : 0 ≤ δ) (h : ∀ e ∈ G, |(triangleDegree G e : ℝ)-d| ≤ δ) :
    triangleDegreeVariance G ≤ (G.card : ℝ)*δ^2 := by
  have hv : triangleDegreeVariance G ≤ ∑ e ∈ G, ((triangleDegree G e : ℝ)-d)^2 := by
    rw [triangle_degree_variance_shift hG d]
    exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  apply hv.trans
  calc
    _ ≤ ∑ _e ∈ G, δ^2 := by
      apply Finset.sum_le_sum
      intro e he
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hδ).mpr (h e he)
    _ = _ := by simp

end SharpTerminalLeave
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Asymptotics_DensityEdgeSafe
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators

namespace SharpTerminalLeave
open Classical

lemma triangle_count_from_edge_degrees {n : ℕ} (G : Graph n) (D δ : ℝ)
    (hd : ∀ e ∈ G, |(triangleDegree G e : ℝ)-D| ≤ δ) :
    |3*(triangles G).card-(G.card : ℝ)*D| ≤ (G.card : ℝ)*δ := by
  have he : 3*(triangles G).card-(G.card : ℝ)*D =
      ∑ e ∈ G, ((triangleDegree G e : ℝ)-D) := by
    rw [Finset.sum_sub_distrib,triangle_degree_sum]
    simp
  rw [he]
  calc
    _ ≤ ∑ e ∈ G, |(triangleDegree G e : ℝ)-D| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ G, δ := Finset.sum_le_sum (fun e he => hd e he)
    _ = _ := by simp

lemma densityEdgeSafe_triangle_bounds {n : ℕ} {p η : ℝ} {G : Graph n}
    (h : densityEdgeSafe n p η G) :
    (n : ℝ)^3*p^3/6*(1-η) ≤ (triangles G).card ∧
      (triangles G).card ≤ (n : ℝ)^3*p^3/6*(1+η) := by
  have hc := triangle_count_from_edge_degrees G (n*p^2) (η*(n*p^2)) h.2.2
  rw [h.2.1] at hc
  obtain ⟨hl,hu⟩ := abs_le.mp hc
  constructor <;> nlinarith only [hl,hu]

lemma densityEdgeSafe_triangle_positive {n : ℕ} {p η : ℝ} {G : Graph n}
    (hn : 0 < n) (hp : 0 < p) (hη : η ≤ 1/2) (h : densityEdgeSafe n p η G) :
    (triangles G).Nonempty := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hq := (densityEdgeSafe_triangle_bounds h).1
  have hfac : 0 < 1-η := by linarith
  have hpos : (0 : ℝ) < (triangles G).card :=
    lt_of_lt_of_le (by positivity) hq
  exact Finset.card_pos.mp (by exact_mod_cast hpos)

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_CommonNeighbors
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem commonNeighbors_ne {n : ℕ} {G : Graph n} (hG : G ⊆ completeGraph n)
    {u v w : Fin n} (hw : w ∈ commonNeighbors G u v) : u ≠ w ∧ v ≠ w := by
  obtain ⟨hu,hv⟩ := (mem_commonNeighbors G u v w).mp hw
  constructor
  · intro h
    have hc := mem_completeGraph.mp (hG hu)
    simp [h] at hc
  · intro h
    have hc := mem_completeGraph.mp (hG hv)
    simp [h] at hc

theorem currentCodegree_copyCount {n : ℕ} (G : Graph n) (u v : Fin n) :
    (currentCodegree G u v : ℝ) = copyCount (wedgeEdges u v) G := by
  simp only [copyCount, intact, wedgeEdges_subset]
  rw [← Finset.sum_filter]
  simp [currentCodegree, commonNeighbors]

theorem step_mean_codegree_hazard {n : ℕ} (G : Graph n) (u v : Fin n)
    (hG : (triangles G).Nonempty) :
    pmfMean (step G) (fun H => (currentCodegree H u v : ℝ)) =
      (currentCodegree G u v : ℝ) -
      (∑ w ∈ commonNeighbors G u v,
        ((hittingTriangles G (wedgeEdges u v w)).card : ℝ)) / (triangles G).card := by
  simp_rw [currentCodegree_copyCount]
  rw [step_mean_copyCount _ G hG]
  congr 2
  simp only [wedgeEdges_subset]
  rw [← Finset.sum_filter]
  simp [commonNeighbors]

theorem hittingTriangles_wedge {n : ℕ} (G : Graph n) (u v w : Fin n) :
    hittingTriangles G (wedgeEdges u v w) =
      incidentTriangles G {u,w} ∪ incidentTriangles G {v,w} := by
  rw [hittingTriangles_eq_biUnion]
  simp [wedgeEdges]

theorem wedge_incident_inter {n : ℕ} (G : Graph n) {u v w : Fin n}
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    incidentTriangles G {u,w} ∩ incidentTriangles G {v,w} =
      if {u,v,w} ∈ triangles G then {{u,v,w}} else ∅ := by
  ext t
  simp only [Finset.mem_inter, incidentTriangles, Finset.mem_filter]
  have hpairu : ({u,w} : Finset (Fin n)).card = 2 := Finset.card_pair huw
  have hpairv : ({v,w} : Finset (Fin n)).card = 2 := Finset.card_pair hvw
  have htriple : ({u,v,w} : Finset (Fin n)).card = 3 := by simp [huv,huw,hvw]
  have hpt : ({u,w} : Finset (Fin n)) ⊆ {u,v,w} := by
    simp [Finset.insert_subset_iff, Finset.singleton_subset_iff]
  have hqt : ({v,w} : Finset (Fin n)) ⊆ {u,v,w} := by
    simp
  have hpq : ({u,w} : Finset (Fin n)) ≠ {v,w} := by
    intro he
    have hh : u ∈ ({v,w} : Finset (Fin n)) := he ▸ (by simp)
    simp [huv,huw] at hh
  constructor
  · rintro ⟨⟨ht,he⟩,_,hf⟩
    have heq := triangle_eq_of_two_edges (mem_triangles.mp ht).1 htriple
      hpairu hpairv hpq (Finset.mem_powersetCard.mp he).1
      (Finset.mem_powersetCard.mp hf).1 hpt hqt
    subst t
    simp [ht]
  · intro hh
    split_ifs at hh with ht
    · have heq : t = {u,v,w} := Finset.mem_singleton.mp hh
      subst t
      exact ⟨⟨ht,Finset.mem_powersetCard.mpr ⟨hpt,hpairu⟩⟩,
        ht,Finset.mem_powersetCard.mpr ⟨hqt,hpairv⟩⟩
    · exact False.elim (Finset.notMem_empty t hh)

theorem wedge_hazard_exact {n : ℕ} {G : Graph n} (hG : G ⊆ completeGraph n)
    {u v w : Fin n} (huv : u ≠ v) (hw : w ∈ commonNeighbors G u v) :
    ((hittingTriangles G (wedgeEdges u v w)).card : ℝ) =
      (triangleDegree G {u,w} : ℝ) + (triangleDegree G {v,w} : ℝ) -
        if {u,v,w} ∈ triangles G then 1 else 0 := by
  obtain ⟨huw,hvw⟩ := commonNeighbors_ne hG hw
  have hh := Finset.card_union_add_card_inter
    (incidentTriangles G {u,w}) (incidentTriangles G {v,w})
  rw [wedge_incident_inter G huv huw hvw] at hh
  rw [hittingTriangles_wedge]
  unfold triangleDegree
  split_ifs at hh ⊢ with ht <;> simp only [Finset.card_singleton, Finset.card_empty] at hh
  all_goals
    have hh' : ((incidentTriangles G {u,w} ∪ incidentTriangles G {v,w}).card : ℝ) +
        (if {u,v,w} ∈ triangles G then 1 else 0) =
        (incidentTriangles G {u,w}).card + (incidentTriangles G {v,w}).card := by
      simp only [ht, ↓reduceIte]
      exact_mod_cast hh
    simp only [ht, ↓reduceIte] at hh'
    linarith

end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_PrefixEpsilon
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem prefixDensity_bounds (n : ℕ) (hn : 0 < n)
    (ht : 0 ≤ prefixTargetTime n) :
    prefixTargetDensity n ≤ prefixDensity n ∧
      prefixDensity n < prefixTargetDensity n + 6 / (n : ℝ)^2 := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn2 : 0 < (n : ℝ)^2 := sq_pos_of_pos hnR
  have hf : (prefixTime n : ℝ) ≤ prefixTargetTime n := Nat.floor_le ht
  have hg : prefixTargetTime n < (prefixTime n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hx : prefixTargetTime n * 6 =
      (n : ℝ)^2 * (1 - 1 / (n : ℝ) - prefixTargetDensity n) := by
    unfold prefixTargetTime
    ring
  have hp : prefixDensity n * (n : ℝ)^2 =
      (1 - 1 / (n : ℝ)) * (n : ℝ)^2 - 6 * prefixTime n := by
    unfold prefixDensity
    field_simp
  constructor
  · apply (le_of_mul_le_mul_right (a := (n : ℝ)^2) _ hn2)
    nlinarith
  · apply (lt_of_mul_lt_mul_right (a := (n : ℝ)^2) _ (le_of_lt hn2))
    have he : (6 / (n : ℝ)^2) * (n : ℝ)^2 = 6 := div_mul_cancel₀ _ (ne_of_gt hn2)
    nlinarith

end SharpTerminalLeave

open InnerProductSpace
open scoped InnerProductSpace

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Asymptotics_OneAddLogRpow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

open Asymptotics

lemma one_add_log_rpow_isLittleO (C : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    (fun x : ℝ => (1 + Real.log x) ^ C) =o[atTop] fun x => x ^ δ := by
  let C' := max C 1
  have hC' : 0 < C' := lt_max_iff.mpr (Or.inr zero_lt_one)
  have hq : 0 < δ / C' := div_pos hδ hC'
  have hc : (fun _ : ℝ => (1 : ℝ)) =o[atTop] fun x => x ^ (δ / C') := by
    apply (isLittleO_const_left_of_ne one_ne_zero).mpr
    apply (tendsto_rpow_atTop hq).congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact (Real.norm_of_nonneg (Real.rpow_nonneg hx _)).symm
  have hs := hc.add (isLittleO_log_rpow_atTop hq)
  calc
    (fun x : ℝ => (1 + Real.log x) ^ C) =O[atTop]
        fun x => (1 + Real.log x) ^ C' := by
      apply IsBigO.of_norm_eventuallyLE
      filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 0] with x hx
      simp only [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ 1 + Real.log x) C)]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left _ _)
    _ =o[atTop] fun x => (x ^ (δ / C')) ^ C' :=
      hs.rpow hC' ((eventually_ge_atTop (0 : ℝ)).mono fun x hx => Real.rpow_nonneg hx _)
    _ =ᶠ[atTop] fun x => x ^ δ := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      rw [← Real.rpow_mul hx,div_mul_cancel₀ _ hC'.ne']

 theorem prefixTemplateFactor_subpower (C : ℝ) {δ b : ℝ} (hδ : 0 < δ) (hb : 0 < b) :
    ∀ᶠ n : ℕ in atTop, prefixTemplateFactor n C ≤ b * (n : ℝ) ^ δ := by
  have h := ((one_add_log_rpow_isLittleO C hδ).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).bound hb
  filter_upwards [h,eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hl : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
  have hb0 : 0 ≤ 1 + Real.log (n : ℝ) := by linarith
  simpa only [Function.comp_apply,Real.norm_of_nonneg (Real.rpow_nonneg hb0 C),
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) δ),prefixTemplateFactor] using hn

lemma prefixTargetDensity_eq (n : ℕ) :
    prefixTargetDensity n = (n : ℝ) ^ (-(999 / 2000 : ℝ)) := by
  unfold prefixTargetDensity prefixEpsilon
  congr 1
  norm_num

lemma prefixTargetDensity_tendsto : Tendsto prefixTargetDensity atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => prefixTargetDensity n) atTop (𝓝 0)
  simp_rw [prefixTargetDensity_eq]
  exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 999 / 2000)).comp
    tendsto_natCast_atTop_atTop

lemma prefixTargetTime_eventually_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ prefixTargetTime n := by
  have hi : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div,Function.comp_def] using (tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ)))
  filter_upwards [prefixTargetDensity_tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1/2),
    hi.eventually_le_const (by norm_num : (0 : ℝ) < 1/2)] with n hp hi
  unfold prefixTargetTime
  exact mul_nonneg (by positivity) (by linarith)

theorem prefixDensity_eventual_envelope : ∀ᶠ n : ℕ in atTop,
    (n : ℝ) ^ (-(999 / 2000 : ℝ)) ≤ prefixDensity n ∧
      prefixDensity n ≤ 2 * (n : ℝ) ^ (-(999 / 2000 : ℝ)) := by
  filter_upwards [prefixTargetTime_eventually_nonneg,eventually_ge_atTop (6 : ℕ)] with n ht hn
  have hnR : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨hl,hu⟩ := prefixDensity_bounds n (by omega) ht
  rw [prefixTargetDensity_eq] at hl hu
  refine ⟨hl,?_⟩
  have h1 : 6 / (n : ℝ)^2 ≤ 1 / (n : ℝ) := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ)^2) hn0).mpr
    nlinarith
  have h2 : 1 / (n : ℝ) ≤ (n : ℝ) ^ (-(999 / 2000 : ℝ)) := by
    rw [one_div,← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  linarith

lemma prefix_target_D_identity (n : ℕ) (hn : 0 < n) :
    (n : ℝ) * ((n : ℝ) ^ (-(999 / 2000 : ℝ))) ^ 2 =
      (n : ℝ) ^ (1 / 1000 : ℝ) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [← Real.rpow_natCast,← Real.rpow_mul hnR.le]
  conv_lhs => lhs; rw [← Real.rpow_one (n : ℝ)]
  rw [← Real.rpow_add hnR]
  congr 1
  norm_num

theorem prefixD_eventual_envelope : ∀ᶠ n : ℕ in atTop,
    (n : ℝ) ^ (1 / 1000 : ℝ) ≤ prefixD n ∧
      prefixD n ≤ 4 * (n : ℝ) ^ (1 / 1000 : ℝ) := by
  filter_upwards [prefixDensity_eventual_envelope,eventually_ge_atTop (1 : ℕ)] with n hp hn
  have hn0 : 0 < n := by omega
  have hq : 0 ≤ (n : ℝ) ^ (-(999 / 2000 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hpl : 0 ≤ prefixDensity n := hq.trans hp.1
  rw [← prefix_target_D_identity n hn0]
  unfold prefixD
  constructor
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq hp.1 2) (Nat.cast_nonneg n)
  · have hsq := pow_le_pow_left₀ hpl hp.2 2
    nlinarith [mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hsq)]

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Probability_HistoryLawPathSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem historyNoise_succ_same {α : Type*} [Fintype α]
    (K : ℕ → α → PMF α) (f : ℕ → α → ℝ)
    (T j : ℕ) (hj : j < T) (ω : History α T) :
    historyNoise K f T (j+1) ω =
      historyNoise K f T j ω + historyIncrement K f T j ω := by
  simp only [historyNoise,Nat.min_eq_left (by omega : j+1 ≤ T),
    Nat.min_eq_left hj.le,Finset.sum_range_succ]

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_PowersetCardTriple
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma powersetCard_triple {α : Type*} [DecidableEq α] {u v w : α}
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    ({u,v,w} : Finset α).powersetCard 2 = {{u,v},{u,w},{v,w}} := by
  have h2 : ({v,w}:Finset α).powersetCard 2 = {{v,w}} := by
    rw [← Finset.card_pair hvw]
    exact Finset.powersetCard_self _
  rw [Finset.powersetCard_succ_insert (by simp [huv,huw]) 1, h2]
  simp only [Finset.powersetCard_one, Finset.map_insert, Finset.map_singleton, Finset.image_insert,
    Finset.image_singleton, Function.Embedding.coeFn_mk]
  ext s
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

lemma triangle_closure_iff {n : ℕ} {G : Graph n} (hG : G ⊆ completeGraph n)
    {u v w : Fin n} (huv : u ≠ v) (hw : w ∈ commonNeighbors G u v) :
    {u,v,w} ∈ triangles G ↔ {u,v} ∈ G := by
  obtain ⟨huw,hvw⟩ := commonNeighbors_ne hG hw
  obtain ⟨huwG,hvwG⟩ := (mem_commonNeighbors G u v w).mp hw
  rw [mem_triangles, powersetCard_triple huv huw hvw]
  simp [huv,huw,hvw,Finset.insert_subset_iff,Finset.singleton_subset_iff,huwG,hvwG]

end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Asymptotics_RelativeScaleBudgetLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem relativeScaleBudget_le_log (s : ℕ → ℝ) (T : ℕ)
    (hs : ∀ k ≤ T, 0 < s k)
    (hdec : ∀ k < T, s (k+1) ≤ s k)
    (hratio : ∀ k < T, s k ≤ 2*s (k+1)) :
    relativeScaleBudget s T ≤ 2*Real.log (s 0/s T) := by
  have hsingle {r : ℝ} (h1 : 1 ≤ r) (h2 : r ≤ 2) : r-1 ≤ 2*Real.log r := by
    have hr : 0 < r := lt_of_lt_of_le zero_lt_one h1
    have hi : 0 ≤ 1-r⁻¹ := sub_nonneg.mpr ((inv_le_one₀ hr).mpr h1)
    calc
      r-1 = r*(1-r⁻¹) := by field_simp
      _ ≤ 2*(1-r⁻¹) := mul_le_mul_of_nonneg_right h2 hi
      _ ≤ 2*Real.log r := mul_le_mul_of_nonneg_left
        (Real.one_sub_inv_le_log_of_pos hr) (by norm_num)
  have htel : (∑ k ∈ Finset.range T, Real.log (s k/s (k+1))) =
      Real.log (s 0/s T) := by
    calc
      _ = ∑ k ∈ Finset.range T, (Real.log (s k)-Real.log (s (k+1))) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkT := Finset.mem_range.mp hk
        exact Real.log_div (ne_of_gt (hs k (by omega)))
          (ne_of_gt (hs (k+1) (by omega)))
      _ = Real.log (s 0)-Real.log (s T) := by rw [Finset.sum_range_sub']
      _ = Real.log (s 0/s T) := (Real.log_div
        (ne_of_gt (hs 0 (Nat.zero_le T))) (ne_of_gt (hs T le_rfl))).symm
  rw [← htel,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  have hkT := Finset.mem_range.mp hk
  exact hsingle ((one_le_div (hs (k+1) (by omega))).mpr (hdec k hkT))
    ((div_le_iff₀ (hs (k+1) (by omega))).mpr (hratio k hkT))

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Asymptotics_EarlyDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma earlyDensity_antitone (n : ℕ) : Antitone (earlyDensity n) := by
  intro i j hij
  unfold earlyDensity
  have hh : (i : ℝ) ≤ j := by exact_mod_cast hij
  exact sub_le_sub_left (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hh (by norm_num)) (sq_nonneg (n : ℝ))) _

lemma earlyDensity_succ (n i : ℕ) :
    earlyDensity n i = earlyDensity n (i+1)+6/(n : ℝ)^2 := by
  unfold earlyDensity
  push_cast
  ring

lemma prefixDensity_eventually_inverse_lower : ∀ᶠ n : ℕ in atTop,
    1/(n : ℝ) ≤ prefixDensity n := by
  filter_upwards [prefixDensity_eventual_envelope,eventually_ge_atTop (1 : ℕ)] with n hn hn1
  apply le_trans _ hn.1
  rw [one_div,← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) (by norm_num)

theorem earlyTemplateScale_regular (a b : ℕ) : ∀ᶠ n : ℕ in atTop,
    (∀ i ≤ prefixTime n, 0 < earlyTemplateScale a b n i) ∧
    (∀ i < prefixTime n, earlyTemplateScale a b n (i+1) ≤ earlyTemplateScale a b n i) ∧
    (∀ i < prefixTime n, earlyTemplateScale a b n i ≤ 2*earlyTemplateScale a b n (i+1)) := by
  have hi : Tendsto (fun n : ℕ => 6/(n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ => (1+6/(n : ℝ))^b) atTop (𝓝 1) := by
    simpa only [add_zero,one_pow] using ((tendsto_const_nhds (x := (1 : ℝ))).add hi).pow b
  filter_upwards [prefixDensity_eventually_inverse_lower,
    hlim.eventually_le_const (by norm_num : (1 : ℝ) < 2),
    eventually_ge_atTop (1 : ℕ)] with n hp hratio hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlow : ∀ i ≤ prefixTime n, 1/(n : ℝ) ≤ earlyDensity n i := by
    intro i hi
    exact hp.trans (earlyDensity_antitone n hi)
  have hpos : ∀ i ≤ prefixTime n, 0 < earlyDensity n i := by
    intro i hi
    exact lt_of_lt_of_le (by positivity) (hlow i hi)
  refine ⟨?_,?_,?_⟩
  · intro i hi
    exact mul_pos (pow_pos hn0 _) (pow_pos (hpos i hi) _)
  · intro i hi
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hpos (i+1) (by omega)).le
      (earlyDensity_antitone n (Nat.le_succ i)) b) (by positivity)
  · intro i hi
    have hp1 : 0 < earlyDensity n (i+1) := hpos (i+1) (by omega)
    have hstep : earlyDensity n i ≤ earlyDensity n (i+1)*(1+6/(n : ℝ)) := by
      rw [earlyDensity_succ n i]
      have hh := hlow (i+1) (by omega)
      have hhmul := mul_le_mul_of_nonneg_left hh (show 0 ≤ 6/(n : ℝ) by positivity)
      have he : (6/(n : ℝ))*(1/(n : ℝ)) = 6/(n : ℝ)^2 := by ring
      rw [he] at hhmul
      nlinarith only [hhmul]
    have hpw := pow_le_pow_left₀ (hpos i (by omega)).le hstep b
    rw [mul_pow] at hpw
    unfold earlyTemplateScale
    calc
      _ ≤ (n : ℝ)^a * (earlyDensity n (i+1)^b*(1+6/(n : ℝ))^b) :=
        mul_le_mul_of_nonneg_left hpw (by positivity)
      _ ≤ (n : ℝ)^a * (earlyDensity n (i+1)^b*2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hratio (by positivity))
          (by positivity)
      _ = _ := by ring

theorem earlyTemplateScale_log_budget (a b : ℕ) : ∀ᶠ n : ℕ in atTop,
    relativeScaleBudget (earlyTemplateScale a b n) (prefixTime n) ≤
      2*(b : ℝ)*Real.log n := by
  filter_upwards [earlyTemplateScale_regular a b,prefixDensity_eventually_inverse_lower,
    eventually_ge_atTop (1 : ℕ)] with n hreg hlow hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hp : 0 < prefixDensity n := lt_of_lt_of_le (by positivity) hlow
  have hscale : earlyTemplateScale a b n 0/earlyTemplateScale a b n (prefixTime n) ≤
      (n : ℝ)^b := by
    unfold earlyTemplateScale
    rw [earlyDensity_prefix,mul_div_mul_left _ _ (ne_of_gt (pow_pos hn0 a)),← div_pow]
    apply pow_le_pow_left₀ (div_nonneg (by
      have hh := (earlyDensity_antitone n (Nat.zero_le (prefixTime n)))
      change prefixDensity n ≤ earlyDensity n 0 at hh
      linarith) hp.le)
    apply (div_le_iff₀ hp).mpr
    have hp' := (div_le_iff₀ hn0).mp hlow
    have hzero : earlyDensity n 0 ≤ 1 := by unfold earlyDensity; simp
    nlinarith only [hp',hzero]
  have hlog := Real.log_le_log
    (div_pos (hreg.1 0 (Nat.zero_le _)) (hreg.1 (prefixTime n) le_rfl)) hscale
  rw [Real.log_pow] at hlog
  exact (relativeScaleBudget_le_log (earlyTemplateScale a b n) (prefixTime n)
    hreg.1 hreg.2.1 hreg.2.2).trans (by nlinarith only [hlog])

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_CodegreeVertexCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma earlyCodegreeScale_ge_prefixD (n i : ℕ) (hi : i ≤ prefixTime n)
    (hp : 0 ≤ prefixDensity n) : prefixD n ≤ earlyTemplateScale 1 2 n i := by
  unfold earlyTemplateScale prefixD
  rw [pow_one]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hp (earlyDensity_antitone n hi) 2) (Nat.cast_nonneg n)

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Asymptotics_EarlyDensityOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma earlyDensity_le_one (n i : ℕ) : earlyDensity n i ≤ 1 := by
  unfold earlyDensity
  have h₁ : 0 ≤ 1/(n : ℝ) := by positivity
  have h₂ : 0 ≤ 6*(i : ℝ)/(n : ℝ)^2 := by positivity
  linarith

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_PrefixEdgeRadius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter
open Classical

namespace SharpTerminalLeave

lemma early_density_positive {n : ℕ} (hn : 0 < n)
    (hp : 1/(n : ℝ) ≤ prefixDensity n) {i : ℕ} (hi : i ≤ prefixTime n) :
    0 < earlyDensity n i := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  exact lt_of_lt_of_le (by positivity) (hp.trans (earlyDensity_antitone n hi))

lemma early_density_log_bound {n i : ℕ} (hn : 0 < n)
    (hp : 1/(n : ℝ) ≤ prefixDensity n) (hi : i ≤ prefixTime n) :
    -Real.log (earlyDensity n i) ≤ Real.log n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hh : Real.log (1/(n : ℝ)) ≤ Real.log (earlyDensity n i) :=
    Real.log_le_log (by positivity) (hp.trans (earlyDensity_antitone n hi))
  rw [one_div,Real.log_inv] at hh
  linarith

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_PowerEulerError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

lemma power_euler_error (b : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    |(1-r)^b-1+(b : ℝ)*r| ≤ (b : ℝ)^2*r^2 := by
  have hber : ∀ b : ℕ, 0 ≤ (1-r)^b-1+(b : ℝ)*r := by
    intro b
    have hh := one_add_mul_le_pow (show -2 ≤ -r by linarith) b
    simp only [← sub_eq_add_neg,mul_neg] at hh
    linarith only [hh]
  have hupper : ∀ b : ℕ, (1-r)^b-1+(b : ℝ)*r ≤ (b : ℝ)^2*r^2 := by
    intro b
    induction b with
    | zero => simp
    | succ b ih =>
      have hm := mul_le_mul_of_nonneg_left ih (show 0 ≤ 1-r by linarith)
      have hn : 0 ≤ (b : ℝ) := Nat.cast_nonneg _
      have hcube : 0 ≤ (b : ℝ)^2*r^3 := by positivity
      rw [pow_succ,Nat.cast_add,Nat.cast_one]
      nlinarith only [hm,hcube,mul_nonneg hn (sq_nonneg r),sq_nonneg r]
  rw [abs_of_nonneg (hber b)]
  exact hupper b

lemma history_relative_drift_sum {α : Type*} [Fintype α]
    (K : ℕ → α → PMF α) (f : α → ℝ) (s : ℕ → ℝ)
    (T j : ℕ) (hj : j ≤ T) (ω : History α T) :
    f (ω (historyIndex T j))/s j-f (ω (historyIndex T 0))/s 0-
      historyNoise K (fun k a => f a/s k) T j ω =
    ∑ k ∈ Finset.range j,
      (pmfMean (K k (ω (historyIndex T k))) f/s (k+1)-f (ω (historyIndex T k))/s k) := by
  unfold historyNoise historyIncrement
  simp only [Nat.min_eq_left hj,div_eq_mul_inv,pmfMean_mul_const]
  have he := Finset.sum_range_sub' (fun k => f (ω (historyIndex T k))*(s k)⁻¹) j
  have hh : (∑ k ∈ Finset.range j,
      (f (ω (historyIndex T k))*(s k)⁻¹-f (ω (historyIndex T (k+1)))*(s (k+1))⁻¹))+
      (∑ k ∈ Finset.range j,
        (f (ω (historyIndex T (k+1)))*(s (k+1))⁻¹-
          pmfMean (K k (ω (historyIndex T k))) f*(s (k+1))⁻¹)) =
      -(∑ k ∈ Finset.range j,
        (pmfMean (K k (ω (historyIndex T k))) f*(s (k+1))⁻¹-
          f (ω (historyIndex T k))*(s k)⁻¹)) := by
    rw [← Finset.sum_add_distrib,← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he] at hh
  linarith only [hh]

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_CommonNeighborsComplete
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma commonNeighbors_complete {n : ℕ} (u v : Fin n) :
    commonNeighbors (completeGraph n) u v = Finset.univ \ {u,v} := by
  ext w
  simp only [mem_commonNeighbors,mem_completeGraph,Finset.mem_sdiff,
    Finset.mem_univ,Finset.mem_insert,Finset.mem_singleton,true_and]
  by_cases hu : u = w <;> by_cases hv : v = w <;>
    simp [hu,hv,eq_comm]

lemma currentCodegree_complete {n : ℕ} (u v : Fin n) (huv : u ≠ v) :
    currentCodegree (completeGraph n) u v = n-2 := by
  rw [currentCodegree,commonNeighbors_complete]
  rw [Finset.card_sdiff]
  simp only [Finset.inter_univ]
  simp only [Finset.card_univ,Fintype.card_fin,Finset.card_pair huv]

theorem initial_normalized_codegree_error {n : ℕ} (hn : 2 ≤ n)
    (u v : Fin n) (huv : u ≠ v) :
    (currentCodegree (completeGraph n) u v : ℝ)/earlyTemplateScale 1 2 n 0-1 =
      -1/((n : ℝ)-1)^2 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn1 : (n : ℝ)-1 ≠ 0 := by linarith
  rw [currentCodegree_complete u v huv,Nat.cast_sub hn,Nat.cast_ofNat]
  unfold earlyTemplateScale earlyDensity
  simp only [Nat.cast_zero,mul_zero,zero_div,sub_zero,pow_one]
  field_simp
  ring

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_StarInclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix InnerProductSpace
open scoped BigOperators
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

namespace SharpTerminalLeave

variable {E U : Type*} [Fintype E] [DecidableEq E] [Fintype U]

theorem starInclusion_mulVec (S : Finset E) (x : E → ℝ) :
    (starInclusion S)ᴴ *ᵥ x = fun e : S => x e.val := by
  ext e
  simp [starInclusion,Matrix.mulVec,dotProduct]

end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_EdgePairNe
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma edge_pair_ne {n : ℕ} {G : Graph n} (hG : G ⊆ completeGraph n)
    {u v : Fin n} (h : {u,v} ∈ G) : u ≠ v := by
  intro he
  have hh := mem_completeGraph.mp (hG h)
  simp [he] at hh

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_PrefixSpectralErrorPower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave
open Filter

theorem prefixSpectralError_power_decay {c : ℝ} (hc : 0 < c) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n : ℕ in atTop,
      2 * prefixSpectralError n c ≤ (n : ℝ)^(-γ) := by
  let a : ℝ := min c (1/1000)
  let B : ℝ := (8000 : ℝ)^8001 * 2^8000
  let L : ℝ := 4 * (8001 + 2*B) ^ (1/(8000 : ℝ)) + 7
  have ha : 0 < a := lt_min hc (by norm_num)
  have hac : a ≤ c := min_le_left _ _
  have ha1 : a ≤ 1/1000 := min_le_right _ _
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨a/16000,by positivity,?_⟩
  have ht : Tendsto (fun n : ℕ => (n : ℝ)^(a/16000)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < a/16000)).comp tendsto_natCast_atTop_atTop
  filter_upwards [prefixD_eventual_envelope, eventually_ge_atTop (1 : ℕ),
    ht.eventually_ge_atTop (2*L)] with n hD hn hLr
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hDr : 0 < (n : ℝ)^(1/1000 : ℝ) := Real.rpow_pos_of_pos hn0 _
  have hD0 : 0 < prefixD n := hDr.trans_le hD.1
  have hδ : (n : ℝ)^(-c) ≤ (n : ℝ)^(-a) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have h4000 : ((n : ℝ)^(1/1000 : ℝ))^4000 = (n : ℝ)^(4 : ℝ) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hn0.le]
    norm_num
  have hq : (n : ℝ)/prefixD n^4000 ≤ (n : ℝ)^(-a) := by
    calc
      _ ≤ (n : ℝ) / ((n : ℝ)^(1/1000 : ℝ))^4000 :=
        div_le_div_of_nonneg_left hn0.le (pow_pos hDr _)
          (pow_le_pow_left₀ hDr.le hD.1 _)
      _ = (n : ℝ)^(-(3 : ℝ)) := by
        rw [h4000]
        conv_lhs => lhs; rw [← Real.rpow_one (n : ℝ)]
        rw [← Real.rpow_sub hn0]
        norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hi : 1/prefixD n ≤ (n : ℝ)^(-a) := by
    calc
      _ ≤ 1/(n : ℝ)^(1/1000 : ℝ) :=
        div_le_div_of_nonneg_left zero_le_one hDr hD.1
      _ = (n : ℝ)^(-(1/1000 : ℝ)) := by rw [Real.rpow_neg hn0.le,one_div]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hsum : 8001*(n : ℝ)^(-c) + B*((n : ℝ)/prefixD n^4000 + 1/prefixD n) ≤
      (8001+2*B) * (n : ℝ)^(-a) := by
    have hh := mul_le_mul_of_nonneg_left (add_le_add hq hi) hB
    calc
      _ ≤ 8001*(n : ℝ)^(-a)+B*((n : ℝ)^(-a)+(n : ℝ)^(-a)) :=
        add_le_add (mul_le_mul_of_nonneg_left hδ (by norm_num)) hh
      _ = _ := (show ∀ x y : ℝ, 8001*x+y*(x+x)=(8001+2*y)*x by
        intro x y; ring) _ _
  have hrt : (8001*(n : ℝ)^(-c) + B*((n : ℝ)/prefixD n^4000 + 1/prefixD n)) ^
      (1/(8000 : ℝ)) ≤ (8001+2*B)^(1/(8000 : ℝ)) * (n : ℝ)^(-a/8000) := by
    calc
      _ ≤ ((8001+2*B) * (n : ℝ)^(-a))^(1/(8000 : ℝ)) :=
        Real.rpow_le_rpow (add_nonneg
          (mul_nonneg (by norm_num) (Real.rpow_nonneg hn0.le _))
          (mul_nonneg hB (add_nonneg (div_nonneg hn0.le (pow_nonneg hD0.le _))
            (div_nonneg zero_le_one hD0.le)))) hsum (by norm_num)
      _ = _ := by
        rw [Real.mul_rpow (by positivity) (by positivity),← Real.rpow_mul hn0.le]
        congr 2
        ring
  have hδ' : (n : ℝ)^(-c) ≤ (n : ℝ)^(-a/8000) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have herr : prefixSpectralError n c ≤ L * (n : ℝ)^(-a/8000) := by
    unfold prefixSpectralError
    change 4*(8001*(n : ℝ)^(-c)+B*((n : ℝ)/prefixD n^4000+1/prefixD n))^
      (1/(8000 : ℝ))+7*(n : ℝ)^(-c) ≤ _
    dsimp [L]
    nlinarith
  calc
    _ ≤ (2*L)*(n : ℝ)^(-a/8000) := by linarith
    _ ≤ (n : ℝ)^(a/16000)*(n : ℝ)^(-a/8000) :=
      mul_le_mul_of_nonneg_right hLr (by positivity)
    _ = (n : ℝ)^(-(a/16000)) := by
      rw [← Real.rpow_add hn0]
      congr 1
      ring

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_IncidentTriangleThird
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma incidentTriangle_third {n : ℕ} {G : Graph n} {u v : Fin n}
    (huv : u ≠ v) {t : Finset (Fin n)} (ht : t ∈ incidentTriangles G {u,v}) :
    ∃ w ∈ commonNeighbors G u v, t = {u,v,w} ∧ u ≠ w ∧ v ≠ w := by
  obtain ⟨ht,hpair⟩ := Finset.mem_filter.mp ht
  obtain ⟨htcard,htG⟩ := mem_triangles.mp ht
  have hsub : ({u,v} : Finset (Fin n)) ⊆ t := (Finset.mem_powersetCard.mp hpair).1
  have hc : (t \ {u,v}).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, htcard, Finset.card_pair huv]
  obtain ⟨w,heq⟩ := Finset.card_eq_one.mp hc
  have hw : w ∈ t \ {u,v} := by rw [heq]; simp
  obtain ⟨hwt,hwuv⟩ := Finset.mem_sdiff.mp hw
  have huw : u ≠ w := by intro h; apply hwuv; simp [h]
  have hvw : v ≠ w := by intro h; apply hwuv; simp [h]
  have htriple : t = {u,v,w} := by
    have hu := Finset.sdiff_union_of_subset hsub
    rw [heq] at hu
    rw [← hu]
    ext x
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    tauto
  have hcw : w ∈ commonNeighbors G u v := by
    apply (mem_commonNeighbors G u v w).mpr
    constructor
    · apply htG
      apply Finset.mem_powersetCard.mpr
      exact ⟨by rw [htriple]; simp, Finset.card_pair huw⟩
    · apply htG
      apply Finset.mem_powersetCard.mpr
      exact ⟨by rw [htriple]; simp, Finset.card_pair hvw⟩
  exact ⟨w,hcw,htriple,huw,hvw⟩

lemma incidentTriangles_eq_image {n : ℕ} {G : Graph n}
    (hG : G ⊆ completeGraph n) {u v : Fin n} (he : {u,v} ∈ G) :
    incidentTriangles G {u,v} = (commonNeighbors G u v).image (fun w => {u,v,w}) := by
  have huv : u ≠ v := by
    intro h
    have hh := mem_completeGraph.mp (hG he)
    simp [h] at hh
  ext t
  constructor
  · intro ht
    obtain ⟨w,hw,rfl,_,_⟩ := incidentTriangle_third huv ht
    exact Finset.mem_image.mpr ⟨w,hw,rfl⟩
  · intro ht
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp ht
    apply Finset.mem_filter.mpr
    refine ⟨(triangle_closure_iff hG huv hw).mpr he,?_⟩
    exact Finset.mem_powersetCard.mpr ⟨by simp,Finset.card_pair huv⟩

theorem triangleDegree_eq_codegree {n : ℕ} {G : Graph n}
    (hG : G ⊆ completeGraph n) {u v : Fin n} (he : {u,v} ∈ G) :
    triangleDegree G {u,v} = currentCodegree G u v := by
  unfold triangleDegree currentCodegree
  rw [incidentTriangles_eq_image hG he]
  apply Finset.card_image_of_injOn
  intro a ha b _ hab
  change ({u,v,a} : Finset (Fin n)) = {u,v,b} at hab
  have ha' : a ∈ ({u,v,b} : Finset (Fin n)) := by rw [← hab]; simp
  have hnea := commonNeighbors_ne hG ha
  simpa [hnea.1.symm,hnea.2.symm] using ha'

theorem step_mean_codegree {n : ℕ} {G : Graph n}
    (hG : G ⊆ completeGraph n) (hQ : (triangles G).Nonempty)
    (u v : Fin n) (huv : u ≠ v) :
    pmfMean (step G) (fun H => (currentCodegree H u v : ℝ)) =
      (currentCodegree G u v : ℝ) -
      (∑ w ∈ commonNeighbors G u v,
        ((currentCodegree G u w : ℝ) + currentCodegree G v w -
          if {u,v} ∈ G then 1 else 0)) / (triangles G).card := by
  rw [step_mean_codegree_hazard G u v hQ]
  congr 2
  apply Finset.sum_congr rfl
  intro w hw
  rw [wedge_hazard_exact hG huv hw]
  have hw' := (mem_commonNeighbors G u v w).mp hw
  rw [triangleDegree_eq_codegree hG hw'.1, triangleDegree_eq_codegree hG hw'.2]
  simp only [triangle_closure_iff hG huv hw]

end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_ProspectiveFailure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

@[simp] theorem markedGood_bind {α : Type*} [Fintype α] (π : PMF α)
    (p : α → PMF (Bool × Bool)) :
    markedGood (π.bind p) = pmfMean π (fun a => markedGood (p a)) :=
  pmfMean_bind π p _

@[simp] theorem markedGood_no_marks (p : PMF Bool) :
    markedGood (p.map (fun b => (b,true))) = 1 := by
  rw [markedGood,pmfMean_map]
  simp only [↓reduceIte,pmfMean_const]

@[simp] theorem markedSuccess_no_marks (p : PMF Bool) :
    markedSuccess (p.map (fun b => (b,true))) = (p true).toReal := by
  rw [markedSuccess,pmfMean_map]
  simp [pmfMean]

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_TriangleIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

lemma earlyTriangleScale_regular : ∀ᶠ n : ℕ in atTop,
    (∀ i ≤ prefixTime n, 0 < earlyTriangleScale n i) ∧
    (∀ i < prefixTime n, earlyTriangleScale n (i+1) ≤ earlyTriangleScale n i) ∧
    (∀ i < prefixTime n, earlyTriangleScale n i ≤ 2*earlyTriangleScale n (i+1)) ∧
    relativeScaleBudget (earlyTriangleScale n) (prefixTime n) ≤ 6*Real.log n := by
  filter_upwards [earlyTemplateScale_regular 3 3,earlyTemplateScale_log_budget 3 3] with n hr hb
  refine ⟨fun i hi => div_pos (hr.1 i hi) (by norm_num),?_,?_,?_⟩
  · intro i hi
    exact div_le_div_of_nonneg_right (hr.2.1 i hi) (by norm_num)
  · intro i hi
    have hh := div_le_div_of_nonneg_right (hr.2.2 i hi) (by norm_num : (0 : ℝ) ≤ 6)
    simpa only [earlyTriangleScale,mul_div_assoc] using hh
  · convert hb using 1
    · unfold relativeScaleBudget earlyTriangleScale
      congr 1
      ext i
      ring
    · norm_num

lemma completeGraph_early_mass {n : ℕ} (hn : 0 < n) :
    ((completeGraph n).card : ℝ) = (n : ℝ)^2*earlyDensity n 0/2 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [card_completeGraph,Nat.cast_choose_two]
  simp only [earlyDensity,Nat.cast_zero,mul_zero,zero_div,sub_zero]
  field_simp

lemma triangleDegree_complete {n : ℕ} (e : Finset (Fin n)) (he : e ∈ completeGraph n) :
    triangleDegree (completeGraph n) e = n-2 := by
  obtain ⟨u,v,huv,rfl⟩ := Finset.card_eq_two.mp (mem_completeGraph.mp he)
  rw [triangleDegree_eq_codegree (Finset.Subset.refl _) he,currentCodegree_complete u v huv]

lemma triangleCount_complete_formula {n : ℕ} (hn : 2 ≤ n) :
    ((triangles (completeGraph n)).card : ℝ) = (n : ℝ)*(n-1)*(n-2)/6 := by
  have hh := triangle_degree_sum (completeGraph n)
  have he : (∑ e ∈ completeGraph n, (triangleDegree (completeGraph n) e : ℝ)) =
      ((completeGraph n).card : ℝ)*(n-2) := by
    calc
      _ = ∑ _e ∈ completeGraph n, ((n-2 : ℕ) : ℝ) := Finset.sum_congr rfl (fun e he => by rw [triangleDegree_complete e he])
      _ = _ := by simp [Nat.cast_sub hn]; ring
  rw [he,card_completeGraph,Nat.cast_choose_two] at hh
  nlinarith only [hh]

lemma initial_triangle_relative_error {n : ℕ} (hn : 2 ≤ n) :
    ((triangles (completeGraph n)).card : ℝ)/earlyTriangleScale n 0-1 = -1/((n : ℝ)-1)^2 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn1 : (n : ℝ)-1 ≠ 0 := by linarith
  have hs : earlyTriangleScale n 0 = ((n : ℝ)-1)^3/6 := by
    unfold earlyTriangleScale earlyTemplateScale earlyDensity
    simp only [Nat.cast_zero,mul_zero,zero_div,sub_zero]
    field_simp
  rw [triangleCount_complete_formula hn,hs]
  field_simp
  ring

lemma densityEdgeSafe_triangle_load {n : ℕ} {p η : ℝ} {G : Graph n}
    (hp : 0 ≤ p) (hη : η ≤ 1) (h : densityEdgeSafe n p η G) :
    copyLoadSafe (triangleRequired (n := n)) (2*((n : ℝ)*p^2)) G := by
  intro e he
  rw [triangle_copyEdgeLoad]
  have hb := (abs_le.mp (h.2.2 e he)).2
  have hd : 0 ≤ (n : ℝ)*p^2 := mul_nonneg (Nat.cast_nonneg n) (pow_nonneg hp 2)
  have hh := mul_le_mul_of_nonneg_right hη hd
  linarith

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Asymptotics_DensityEdgeSafeTriangle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

theorem densityEdgeSafe_triangle_euler_error {n : ℕ} {p η : ℝ} {G : Graph n}
    (hn : 0 < n) (hp : 0 < p) (hη : 0 ≤ η) (hη1 : η ≤ 1/2)
    (h : densityEdgeSafe n p η G) :
    |pmfMean (step G) (fun H => ((triangles H).card : ℝ))-(triangles G).card+
      3*(6/(n : ℝ)^2/p)*(triangles G).card| ≤ 6*η^2*((n : ℝ)*p^2)+2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have ht := densityEdgeSafe_triangle_positive hn hp hη1 h
  have hq : (0 : ℝ) < (triangles G).card := by exact_mod_cast ht.card_pos
  have hm : (0 : ℝ) < G.card := by exact_mod_cast (graph_nonempty_of_triangles ht).card_pos
  have he : 9/(G.card : ℝ) = 3*(6/(n : ℝ)^2/p) := by
    rw [h.2.1]
    field_simp
    ring
  have hv := triangle_degree_variance_le (graph_nonempty_of_triangles ht) ((n : ℝ)*p^2)
    (η*((n : ℝ)*p^2)) (by positivity) h.2.2
  have hlo := (densityEdgeSafe_triangle_bounds h).1
  have hhalf : (n : ℝ)^3*p^3/12 ≤ (triangles G).card := by
    have hh := mul_le_mul_of_nonneg_left hη1 (show 0 ≤ (n : ℝ)^3*p^3/6 by positivity)
    nlinarith only [hlo,hh]
  have hVbound : triangleDegreeVariance G/(triangles G).card ≤ 6*η^2*((n : ℝ)*p^2) := by
    apply (div_le_iff₀ hq).mpr
    have hh := mul_le_mul_of_nonneg_left hhalf (show 0 ≤ 6*η^2*((n : ℝ)*p^2) by positivity)
    rw [h.2.1] at hv
    nlinarith only [hv,hh]
  have hVnonneg : 0 ≤ triangleDegreeVariance G/(triangles G).card :=
    div_nonneg (triangleDegreeVariance_nonneg G) hq.le
  rw [step_mean_triangle_count_centered ht]
  have he' : 9*(triangles G).card/(G.card : ℝ) = 3*(6/(n : ℝ)^2/p)*(triangles G).card := by
    rw [mul_div_right_comm,he]
  rw [he']
  apply abs_le.mpr
  constructor <;> linarith only [hVbound,hVnonneg]

lemma relative_power_absolute_drift_bound {X Y s t r a B : ℝ} {b : ℕ}
    (hX : 0 ≤ X) (hs : 0 < s) (ht : 0 < t) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hscale : t = s*(1-r)^b) (hratio : s ≤ 2*t) (hcap : X ≤ B*s)
    (ha : 0 ≤ a) (h : |Y-X+(b : ℝ)*r*X| ≤ a*s) :
    |Y/t-X/s| ≤ 2*(a+B*(b : ℝ)^2*r^2) := by
  have hpow := power_euler_error b hr hr1
  have he : Y/t-X/s = ((Y-X+(b : ℝ)*r*X)-X*((1-r)^b-1+(b : ℝ)*r))/t := by
    apply (eq_div_iff ht.ne').mpr
    field_simp [hs.ne']
    rw [hscale]
    ring
  have hB : 0 ≤ B := (mul_nonneg_iff_of_pos_right hs).mp (hX.trans hcap)
  have hnum : |(Y-X+(b : ℝ)*r*X)-X*((1-r)^b-1+(b : ℝ)*r)| ≤
      (a+B*(b : ℝ)^2*r^2)*s := by
    calc
      _ ≤ |Y-X+(b : ℝ)*r*X|+|X*((1-r)^b-1+(b : ℝ)*r)| := abs_sub _ _
      _ ≤ a*s+X*((b : ℝ)^2*r^2) := by
        apply add_le_add h
        rw [abs_mul,abs_of_nonneg hX]
        exact mul_le_mul_of_nonneg_left hpow hX
      _ ≤ a*s+(B*s)*((b : ℝ)^2*r^2) := add_le_add le_rfl
        (mul_le_mul_of_nonneg_right hcap (by positivity))
      _ = _ := by ring
  rw [he,abs_div,abs_of_pos ht]
  apply (div_le_iff₀ ht).mpr
  have hm := mul_le_mul_of_nonneg_left hratio (show 0 ≤ a+B*(b : ℝ)^2*r^2 by positivity)
  exact hnum.trans (by nlinarith only [hm])

lemma early_triangle_drift_single {n : ℕ} {i : ℕ} {G : Graph n} {η : ℝ}
    (hn : 0 < n) (hp : 1/(n : ℝ) ≤ prefixDensity n) (hi : i < prefixTime n)
    (hη : 0 ≤ η) (hη1 : η ≤ 1/2)
    (hreg : earlyTriangleScale n i ≤ 2*earlyTriangleScale n (i+1))
    (h : densityEdgeSafe n (earlyDensity n i) η G) :
    |pmfMean (step G) (fun H => ((triangles H).card : ℝ))/earlyTriangleScale n (i+1)-
      (triangles G).card/earlyTriangleScale n i| ≤
      12*η^2*(6/(n : ℝ)^2/earlyDensity n i)+
        4*(6/(n : ℝ)^2/earlyDensity n i)/((n : ℝ)*earlyDensity n i^2)+
        36*(6/(n : ℝ)^2/earlyDensity n i)^2 := by
  let p := earlyDensity n i
  let lam := 6/(n : ℝ)^2/p
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hp0 : 0 < p := early_density_positive hn hp hi.le
  have hp1 := early_density_positive hn hp (show i+1 ≤ prefixTime n by omega)
  have hstep := earlyDensity_succ n i
  have hl : 0 ≤ lam := by dsimp [lam]; positivity
  have hl1 : lam ≤ 1 := by
    apply (div_le_iff₀ hp0).mpr
    dsimp only [p] at hp0 ⊢
    linarith only [hstep,hp1]
  have hs : 0 < earlyTriangleScale n i := by unfold earlyTriangleScale earlyTemplateScale; change 0 < (n : ℝ)^3*p^3/6; positivity
  have ht : 0 < earlyTriangleScale n (i+1) := by unfold earlyTriangleScale earlyTemplateScale; positivity
  have hscale : earlyTriangleScale n (i+1) = earlyTriangleScale n i*(1-lam)^3 := by
    have he : earlyDensity n (i+1) = p*(1-lam) := by
      have he : earlyDensity n (i+1) = p-6/(n : ℝ)^2 := by dsimp [p]; linarith only [hstep]
      rw [he]
      dsimp [lam]
      field_simp
    unfold earlyTriangleScale earlyTemplateScale
    rw [he,mul_pow]
    dsimp [p]
    ring
  have hcap : ((triangles G).card : ℝ) ≤ 2*earlyTriangleScale n i := by
    have hu := (densityEdgeSafe_triangle_bounds h).2
    have hh := mul_le_mul_of_nonneg_left (show 1+η ≤ 2 by linarith) hs.le
    exact hu.trans (by dsimp only [earlyTriangleScale,earlyTemplateScale] at hh ⊢; nlinarith only [hh])
  have hd := densityEdgeSafe_triangle_euler_error hn hp0 hη hη1 h
  have he : (6*η^2*lam+2*lam/((n : ℝ)*p^2))*earlyTriangleScale n i = 6*η^2*((n : ℝ)*p^2)+2 := by
    dsimp [lam,earlyTriangleScale,earlyTemplateScale]
    change (6*η^2*(6/(n : ℝ)^2/p)+2*(6/(n : ℝ)^2/p)/((n : ℝ)*p^2))*((n : ℝ)^3*p^3/6) = _
    field_simp
  rw [← he] at hd
  have hh := relative_power_absolute_drift_bound (Nat.cast_nonneg (triangles G).card) hs ht hl hl1
    hscale hreg hcap (by positivity : 0 ≤ 6*η^2*lam+2*lam/((n : ℝ)*p^2)) hd
  norm_num only [Nat.cast_ofNat] at hh
  dsimp only [lam,p] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

lemma early_grid_sum_bounds {n : ℕ} (hn : 0 < n)
    (hp : 1/(n : ℝ) ≤ prefixDensity n) (j : ℕ) (hj : j ≤ prefixTime n) :
    (∑ i ∈ Finset.range j, 6/(n : ℝ)^2/earlyDensity n i) ≤ Real.log n ∧
    (∑ i ∈ Finset.range j, (6/(n : ℝ)^2/earlyDensity n i)/((n : ℝ)*earlyDensity n i^2)) ≤ 1/(2*prefixD n) ∧
    (∑ i ∈ Finset.range j, (6/(n : ℝ)^2/earlyDensity n i)^2) ≤ 6/(n : ℝ)*Real.log n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let p := earlyDensity n
  let h : ℝ := 6/(n : ℝ)^2
  let lam : ℕ → ℝ := fun i => h/p i
  have hpos : ∀ i ≤ prefixTime n, 0 < p i := fun i hi => early_density_positive hn hp hi
  have hstep : ∀ i, p i = p (i+1)+h := fun i => earlyDensity_succ n i
  have hlog : (∑ i ∈ Finset.range j, lam i) ≤ Real.log n := by
    have hh := (density_log_sum_bounds p h j (fun i hi => hpos i (hi.trans hj))
      (fun i _ => hstep i)).1
    have hp0 := Real.log_nonpos (hpos 0 (Nat.zero_le _)).le (earlyDensity_le_one n 0)
    have hln := early_density_log_bound hn hp hj
    dsimp only [lam] at hh ⊢
    linarith only [hh,hp0,hln]
  have hlD : (∑ i ∈ Finset.range j, lam i/((n : ℝ)*p i^2)) ≤ 1/(2*prefixD n) := by
    have hh := inverse_square_grid_sum p (n : ℝ) h j hnR (by dsimp [h]; positivity)
      (fun i hi => hpos i (hi.trans hj)) (fun i _ => hstep i)
    have he : (∑ i ∈ Finset.range j, 2*h/((n : ℝ)*p i^3)) =
        2*(∑ i ∈ Finset.range j, lam i/((n : ℝ)*p i^2)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have := hpos i ((Finset.mem_range.mp hi).le.trans hj)
      dsimp only [lam]
      field_simp
    rw [he] at hh
    have hDj := earlyCodegreeScale_ge_prefixD n j hj (le_trans (by positivity) hp)
    have hD : 0 < prefixD n := by unfold prefixD; have := early_density_positive hn hp (show prefixTime n ≤ prefixTime n by rfl); rw [earlyDensity_prefix] at this; positivity
    have hDj' : prefixD n ≤ (n : ℝ)*p j^2 := by simpa only [earlyTemplateScale,pow_one] using hDj
    have hr := one_div_le_one_div_of_le hD hDj'
    have ht : 0 ≤ 1/((n : ℝ)*p 0^2) := by positivity
    have he' : 1/prefixD n = 2*(1/(2*prefixD n)) := by ring
    rw [he'] at hr
    linarith only [hh,hr,ht]
  have hsq : (∑ i ∈ Finset.range j, (lam i)^2) ≤ 6/(n : ℝ)*Real.log n := by
    have hlmax (i : ℕ) (hi : i < j) : lam i ≤ 6/(n : ℝ) := by
      have hp' := hp.trans (earlyDensity_antitone n (hi.le.trans hj))
      change 1/(n : ℝ) ≤ p i at hp'
      apply (div_le_iff₀ (hpos i (hi.le.trans hj))).mpr
      dsimp only [h]
      have hm := mul_le_mul_of_nonneg_left hp' (show 0 ≤ 6/(n : ℝ) by positivity)
      convert hm using 1
      all_goals try with_reducible_and_instances rfl
      field_simp
    calc
      _ ≤ ∑ i ∈ Finset.range j, (6/(n : ℝ))*lam i := by
        apply Finset.sum_le_sum
        intro i hi
        have hli : 0 ≤ lam i := by dsimp [lam,h]; exact div_nonneg (by positivity) (hpos i ((Finset.mem_range.mp hi).le.trans hj)).le
        nlinarith only [mul_le_mul_of_nonneg_right (hlmax i (Finset.mem_range.mp hi)) hli]
      _ = 6/(n : ℝ)*(∑ i ∈ Finset.range j, lam i) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hlog (by positivity)
  exact ⟨hlog,hlD,hsq⟩

theorem early_triangle_drift_bound {n : ℕ} (η : ℝ) (hn : 0 < n)
    (hp : 1/(n : ℝ) ≤ prefixDensity n) (hη : 0 ≤ η) (hη1 : η ≤ 1/2)
    (hreg : ∀ i < prefixTime n, earlyTriangleScale n i ≤ 2*earlyTriangleScale n (i+1))
    (j : ℕ) (hj : j ≤ prefixTime n) (ω : History (Graph n) (prefixTime n))
    (hsafe : ∀ i < j, densityEdgeSafe n (earlyDensity n i) η (ω (historyIndex (prefixTime n) i))) :
    |(triangles (ω (historyIndex (prefixTime n) j))).card/earlyTriangleScale n j-
      (triangles (ω (historyIndex (prefixTime n) 0))).card/earlyTriangleScale n 0-
      historyNoise (fun _ => step) (fun i G => (triangles G).card/earlyTriangleScale n i)
        (prefixTime n) j ω| ≤ 12*η^2*Real.log n+2/prefixD n+216*Real.log n/(n : ℝ) := by
  have hb := early_grid_sum_bounds hn hp j hj
  rw [history_relative_drift_sum (fun _ => step) (fun G : Graph n => ((triangles G).card : ℝ))
    (earlyTriangleScale n) (prefixTime n) j hj ω]
  calc
    _ ≤ ∑ i ∈ Finset.range j,
        |pmfMean (step (ω (historyIndex (prefixTime n) i))) (fun G => ((triangles G).card : ℝ))/earlyTriangleScale n (i+1)-
          (triangles (ω (historyIndex (prefixTime n) i))).card/earlyTriangleScale n i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range j,
        (12*η^2*(6/(n : ℝ)^2/earlyDensity n i)+
        4*(6/(n : ℝ)^2/earlyDensity n i)/((n : ℝ)*earlyDensity n i^2)+
        36*(6/(n : ℝ)^2/earlyDensity n i)^2) := by
      apply Finset.sum_le_sum
      intro i hi
      have hij := Finset.mem_range.mp hi
      exact early_triangle_drift_single hn hp (by omega) hη hη1 (hreg i (by omega)) (hsafe i hij)
    _ = 12*η^2*(∑ i ∈ Finset.range j, 6/(n : ℝ)^2/earlyDensity n i)+
        4*(∑ i ∈ Finset.range j, (6/(n : ℝ)^2/earlyDensity n i)/((n : ℝ)*earlyDensity n i^2))+
        36*(∑ i ∈ Finset.range j, (6/(n : ℝ)^2/earlyDensity n i)^2) := by
      simp only [Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ _ := by
      have h₁ := mul_le_mul_of_nonneg_left hb.1 (show 0 ≤ 12*η^2 by positivity)
      have h₂ := mul_le_mul_of_nonneg_left hb.2.1 (by norm_num : (0 : ℝ) ≤ 4)
      have h₃ := mul_le_mul_of_nonneg_left hb.2.2 (by norm_num : (0 : ℝ) ≤ 36)
      simp only [div_eq_mul_inv,mul_inv_rev] at h₁ h₂ h₃ ⊢
      norm_num only [invOf_eq_inv,inv_div,inv_one] at h₂
      nlinarith only [h₁,h₂,h₃]

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Stability_MovingPerturbationFiniteExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators

namespace SharpTerminalLeave

theorem moving_perturbation_finite_expansion {X : Type*} [AddCommGroup X] [Module ℝ X]
    (V : Module.End ℝ X) (x y : X) (h : x = y + V x) (K : ℕ) :
    x = (∑ j ∈ Finset.range K, (V^j) y) + (V^K) x := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, pow_succ]
    calc
      x = (∑ j ∈ Finset.range K, (V^j) y) + (V^K) x := ih
      _ = (∑ j ∈ Finset.range K, (V^j) y) + (V^K) (y + V x) := by rw [← h]
      _ = _ := by simp [Module.End.mul_apply, add_assoc]

lemma seminorm_end_pow_le {X : Type*} [AddCommGroup X] [Module ℝ X]
    (p : Seminorm ℝ X) (V : Module.End ℝ X) {A : ℝ} (hA : 0 ≤ A)
    (hV : ∀ x, p (V x) ≤ A * p x) (K : ℕ) (x : X) :
    p ((V^K) x) ≤ A^K * p x := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [pow_succ',Module.End.mul_apply,pow_succ']
    exact (hV _).trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left ih hA)

lemma seminorm_finset_sum_le {X I : Type*} [AddCommGroup X] [Module ℝ X]
    (p : Seminorm ℝ X) (s : Finset I) (f : I → X) :
    p (∑ i ∈ s, f i) ≤ ∑ i ∈ s, p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (map_add_le_add p _ _).trans (add_le_add le_rfl ih)

theorem moving_perturbation_mixed_norm_bound {X : Type*} [AddCommGroup X] [Module ℝ X]
    (p q : Seminorm ℝ X) (V : Module.End ℝ X) (x y : X)
    {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hVp : ∀ z, p (V z) ≤ A * p z) (hVq : ∀ z, q (V z) ≤ B * q z)
    (hpq : ∀ z, p z ≤ q z) (hqp : ∀ z, q z ≤ C * p z)
    (h : x = y + V x) (K : ℕ) :
    p x ≤ (∑ j ∈ Finset.range K, A^j) * p y + B^K * C * p x := by
  have he := moving_perturbation_finite_expansion V x y h K
  calc
    p x = p ((∑ j ∈ Finset.range K, (V^j) y) + (V^K) x) := congrArg p he
    _ ≤ p (∑ j ∈ Finset.range K, (V^j) y) + p ((V^K) x) := map_add_le_add p _ _
    _ ≤ (∑ j ∈ Finset.range K, p ((V^j) y)) + q ((V^K) x) :=
      add_le_add (seminorm_finset_sum_le p _ _) (hpq _)
    _ ≤ (∑ j ∈ Finset.range K, A^j * p y) + B^K * q x :=
      add_le_add (Finset.sum_le_sum (fun j _ => seminorm_end_pow_le p V hA hVp j y))
        (seminorm_end_pow_le q V hB hVq K x)
    _ ≤ (∑ j ∈ Finset.range K, A^j * p y) + B^K * (C * p x) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (hqp x) (pow_nonneg hB K))
    _ = _ := by rw [Finset.sum_mul]; ring

theorem moving_perturbation_mixed_norm_absorb {X : Type*} [AddCommGroup X] [Module ℝ X]
    (p q : Seminorm ℝ X) (V : Module.End ℝ X) (x y : X)
    {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hVp : ∀ z, p (V z) ≤ A * p z) (hVq : ∀ z, q (V z) ≤ B * q z)
    (hpq : ∀ z, p z ≤ q z) (hqp : ∀ z, q z ≤ C * p z)
    (h : x = y + V x) (K : ℕ) (hK : B^K*C ≤ 1/2) :
    p x ≤ 2*(∑ j ∈ Finset.range K, A^j)*p y := by
  have hb := moving_perturbation_mixed_norm_bound p q V x y hA hB hVp hVq hpq hqp h K
  have hp : 0 ≤ p x := apply_nonneg p x
  have ht := mul_le_mul_of_nonneg_right hK hp
  nlinarith only [hb,ht]

theorem moving_perturbation_mixed_norm_absorb_modulo {X : Type*} [AddCommGroup X] [Module ℝ X]
    (p q : Seminorm ℝ X) (V : Module.End ℝ X) (x y : X)
    {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hVp : ∀ z, p (V z) ≤ A * p z) (hVq : ∀ z, q (V z) ≤ B * q z)
    (hpq : ∀ z, p z ≤ q z) (hqp : ∀ z, q z ≤ C * p z)
    (h : p (x-y-V x) = 0) (K : ℕ) (hK : B^K*C ≤ 1/2) :
    p x ≤ 2*(∑ j ∈ Finset.range K, A^j)*p y := by
  let z := x-y-V x
  have he : x = (y+z)+V x := by dsimp only [z]; abel
  have hb := moving_perturbation_mixed_norm_absorb p q V x (y+z) hA hB hVp hVq hpq hqp he K hK
  have hy : p (y+z) ≤ p y := by
    have hh := map_add_le_add p y z
    change p z = 0 at h
    linarith only [hh,h]
  apply hb.trans
  exact mul_le_mul_of_nonneg_left hy (by positivity)

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Stability_MovingResidualForcing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators

namespace SharpTerminalLeave
open Classical

lemma moving_active_subset {E : Type*} (active : ℕ → Finset E) (T : ℕ)
    (hnest : ∀ k < T, active (k+1) ⊆ active k) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ T) :
    active j ⊆ active i := by
  induction j, hij using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ k hik ih => exact (hnest k (by omega)).trans (ih (by omega))

lemma activeLinf_mono {E : Type*} [Fintype E] {s t : Finset E} (h : s ⊆ t) (x : E → ℝ) :
    activeLinf s x ≤ activeLinf t x :=
  activeLinf_bound s x (apply_nonneg _ _) (fun _ he => activeLinf_coordinate t x (h he))

lemma movingResidualForcing_zero {E : Type*} [Fintype E]
    (a : ℕ → ℝ) (R : ℕ → Module.End ℝ (E → ℝ)) (x : ℕ → E → ℝ) :
    movingResidualForcing a R x 0 = 0 := by simp [movingResidualForcing]

lemma movingResidualForcing_succ {E : Type*} [Fintype E]
    (a : ℕ → ℝ) (R : ℕ → Module.End ℝ (E → ℝ)) (x : ℕ → E → ℝ) (t : ℕ) :
    movingResidualForcing a R x (t+1) = movingResidualForcing a R x t-a t • R t (x t) := by
  simp [movingResidualForcing,Finset.sum_range_succ,sub_eq_add_neg,add_comm]

lemma movingResidualForcing_bound {E : Type*} [Fintype E]
    (P : ℕ → Seminorm ℝ (E → ℝ)) (a : ℕ → ℝ) (R : ℕ → Module.End ℝ (E → ℝ))
    (T : ℕ) (ha : ∀ i < T, 0 ≤ a i)
    (hmono : ∀ i j, i ≤ j → j ≤ T → ∀ x, P j x ≤ P i x)
    {B : ℝ} (hB : 0 ≤ B) (hR : ∀ i < T, ∀ x, P i (R i x) ≤ B*P i x)
    (x : ℕ → E → ℝ) :
    trajectorySeminorm P T (movingResidualForcing a R x) ≤
      (∑ i ∈ Finset.range T, a i)*B*trajectorySeminorm P T x := by
  have hS : 0 ≤ ∑ i ∈ Finset.range T, a i :=
    Finset.sum_nonneg (fun i hi => ha i (Finset.mem_range.mp hi))
  have hx0 := apply_nonneg (trajectorySeminorm P T) x
  apply trajectorySeminorm_bound _ _ _ (by positivity)
  intro t ht
  change P t (∑ i ∈ Finset.range t, (-a i) • R i (x i)) ≤ _
  calc
    _ ≤ ∑ i ∈ Finset.range t, P t ((-a i) • R i (x i)) := seminorm_finset_sum_le _ _ _
    _ ≤ ∑ i ∈ Finset.range t, a i*(B*trajectorySeminorm P T x) := by
      apply Finset.sum_le_sum
      intro i hi
      have hit : i < t := Finset.mem_range.mp hi
      have hiT : i < T := by omega
      rw [map_smul_eq_mul,Real.norm_eq_abs,abs_neg,abs_of_nonneg (ha i hiT)]
      apply mul_le_mul_of_nonneg_left _ (ha i hiT)
      exact (hmono i t hit.le ht _).trans ((hR i hiT _).trans
        (mul_le_mul_of_nonneg_left (trajectorySeminorm_at P T x (by omega)) hB))
    _ ≤ ∑ i ∈ Finset.range T, a i*(B*trajectorySeminorm P T x) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono ht)
        (fun i hi _ => mul_nonneg (ha i (Finset.mem_range.mp hi)) (mul_nonneg hB hx0))
    _ = _ := by rw [← Finset.sum_mul]; ring

lemma movingStar_actual_response {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (active : ℕ → Finset E) (a : ℕ → ℝ)
    (R : ℕ → Module.End ℝ (E → ℝ)) (M x : ℕ → E → ℝ) (T : ℕ)
    (hnest : ∀ k < T, active (k+1) ⊆ active k)
    (hinit : ∀ e ∈ active 0, x 0 e = M 0 e)
    (hstep : ∀ k < T, ∀ e ∈ active (k+1), x (k+1) e = x k e -
      a k*(movingStarLift ends (movingStarMean ends (active k) (x k)) e+R k (x k) e) +
        (M (k+1) e-M k e)) :
    trajectorySeminorm (fun t => activeLinf (active t)) T
      (x-movingStarResponse ends active a M-
        movingStarResponse ends active a (movingResidualForcing a R x)) = 0 := by
  let F := M+movingResidualForcing a R x
  have hi : ∀ e ∈ active 0, x 0 e = F 0 e := by
    intro e he
    simp only [F,Pi.add_apply,movingResidualForcing_zero,Pi.zero_apply,add_zero]
    exact hinit e he
  have hs : ∀ k < T, ∀ e ∈ active (k+1), x (k+1) e = x k e -
      a k*movingStarLift ends (movingStarMean ends (active k) (x k)) e + (F (k+1) e-F k e) := by
    intro k hk e he
    rw [hstep k hk e he]
    simp only [F,Pi.add_apply,movingResidualForcing_succ,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    ring
  apply le_antisymm _ (apply_nonneg _ _)
  apply trajectorySeminorm_bound _ _ _ le_rfl
  intro t ht
  apply activeLinf_bound _ _ le_rfl
  intro e he
  have h₁ := movingStar_trajectory_representation ends active a F x t
    (fun k hk => hnest k (by omega)) hi (fun k hk => hs k (by omega)) e he
  have h₂ := movingStar_trajectory_representation ends active a F
    (movingStarSolve ends active a F) t (fun k hk => hnest k (by omega))
    (fun _ _ => rfl) (fun _ _ _ _ => rfl) e he
  have h_eq : x t e = movingStarResponse ends active a F t e := h₁.trans h₂.symm
  change |x t e-movingStarResponse ends active a M t e-
    movingStarResponse ends active a (movingResidualForcing a R x) t e| ≤ 0
  have hadd := congrFun (congrFun (map_add (movingStarResponse ends active a)
    M (movingResidualForcing a R x)) t) e
  change movingStarResponse ends active a F t e = _ at hadd
  rw [h_eq,hadd]
  simp

theorem movingStar_mixed_stability {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (hends : ∀ e, (ends e).card = 2)
    (active : ℕ → Finset E) (a : ℕ → ℝ) (R : ℕ → Module.End ℝ (E → ℝ))
    (M x : ℕ → E → ℝ) (T K : ℕ)
    (hnest : ∀ k < T, active (k+1) ⊆ active k)
    (ha : ∀ k < T, 0 ≤ a k ∧ a k ≤ 1)
    (hinit : ∀ e ∈ active 0, x 0 e = M 0 e)
    (hstep : ∀ k < T, ∀ e ∈ active (k+1), x (k+1) e = x k e -
      a k*(movingStarLift ends (movingStarMean ends (active k) (x k)) e+R k (x k) e) +
        (M (k+1) e-M k e))
    {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hRinf : ∀ k < T, ∀ z, activeLinf (active k) (R k z) ≤ B*activeLinf (active k) z)
    (hR₂ : ∀ k < T, ∀ z, activeL2 (active k) (R k z) ≤ δ*activeL2 (active k) z)
    (hK : ((1+2*∑ k ∈ Finset.range T, a k)*(∑ k ∈ Finset.range T, a k)*δ)^K*
      (Fintype.card E : ℝ) ≤ 1/2) :
    trajectorySeminorm (fun t => activeLinf (active t)) T x ≤
      2*(∑ j ∈ Finset.range K,
        ((1+2*∑ k ∈ Finset.range T, a k)*(∑ k ∈ Finset.range T, a k)*B)^j)*
        (1+2*∑ k ∈ Finset.range T, a k)*trajectorySeminorm (fun t => activeLinf (active t)) T M := by
  let p := trajectorySeminorm (fun t => activeLinf (active t)) T
  let q := trajectorySeminorm (fun t => activeL2 (active t)) T
  let V₁ := (movingStarResponse ends active a).comp (movingResidualForcing a R)
  let S := ∑ k ∈ Finset.range T, a k
  let L := 1+2*S
  have hS : 0 ≤ S := Finset.sum_nonneg (fun k hk => (ha k (Finset.mem_range.mp hk)).1)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hVp : ∀ z, p (V₁ z) ≤ L*S*B*p z := by
    intro z
    have hb := movingStarResponse_linf ends hends active a T hnest ha (movingResidualForcing a R z)
    have hf := movingResidualForcing_bound (fun t => activeLinf (active t)) a R T
      (fun k hk => (ha k hk).1)
      (fun i j hij hj z => activeLinf_mono (moving_active_subset active T hnest hij hj) z) hB hRinf z
    exact hb.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hf hL)
  have hVq : ∀ z, q (V₁ z) ≤ L*S*δ*q z := by
    intro z
    have hb := movingStarResponse_l2 ends hends active a T hnest ha (movingResidualForcing a R z)
    have hf := movingResidualForcing_bound (fun t => activeL2 (active t)) a R T
      (fun k hk => (ha k hk).1)
      (fun i j hij hj z => activeL2_mono (moving_active_subset active T hnest hij hj) z) hδ hR₂ z
    exact hb.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hf hL)
  have hb := moving_perturbation_mixed_norm_absorb_modulo p q V₁ x
    (movingStarResponse ends active a M) (by positivity : 0 ≤ L*S*B) (by positivity : 0 ≤ L*S*δ)
    hVp hVq (fun z => (trajectory_mixed_seminorms active T z).1)
    (fun z => (trajectory_mixed_seminorms active T z).2)
    (movingStar_actual_response ends active a R M x T hnest hinit hstep) K hK
  have hy := movingStarResponse_linf ends hends active a T hnest ha M
  apply hb.trans
  calc
    _ ≤ 2*(∑ j ∈ Finset.range K, (L*S*B)^j)*(L*p M) :=
      mul_le_mul_of_nonneg_left hy (by positivity)
    _ = _ := by dsimp only [p,L,S]; ring

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_CompleteEdge
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Classical Matrix

namespace SharpTerminalLeave

lemma graphActive_sum {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n) (f : CompleteEdge n → ℝ) :
    (∑ e ∈ graphActive G, f e) = ∑ e : G, f (graphEdgeEmbed G hG e) := by
  apply Finset.sum_bij (fun e he => (⟨e.val,(mem_graphActive G e).mp he⟩ : G))
  · intro _ _; exact Finset.mem_univ _
  · intro a ha b hb he
    exact Subtype.ext (congrArg (fun e : G => e.val) he)
  · intro e _
    exact ⟨graphEdgeEmbed G hG e,by exact (mem_graphActive G _).mpr e.property,rfl⟩
  · intro _ _; rfl

lemma graphActive_card_le {n : ℕ} : Fintype.card (CompleteEdge n) ≤ n^2 := by
  rw [Fintype.card_coe,card_completeGraph]
  exact (Nat.choose_le_pow n 2)

lemma graphActive_nested {n : ℕ} {G H : Graph n} (h : H ⊆ G) : graphActive H ⊆ graphActive G := by
  intro e he
  exact (mem_graphActive G e).mpr (h ((mem_graphActive H e).mp he))

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_ExtendStarMulVec
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Classical Matrix

namespace SharpTerminalLeave

lemma extendStar_mulVec_apply {E : Type*} [Fintype E] [DecidableEq E]
    (S : Finset E) (M : Matrix S S ℝ) (z : E → ℝ) (e : E) :
    (extendStar S M *ᵥ z) e = if he : e ∈ S then
      (M *ᵥ fun f : S => z f.val) ⟨e,he⟩ else 0 := by
  rw [extendStar,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,starInclusion_mulVec]
  simp only [Matrix.mulVec,dotProduct,starInclusion]
  by_cases he : e ∈ S
  · have hh : ∀ f : S, e = f.val ↔ f = ⟨e,he⟩ := fun f => by rw [Subtype.ext_iff]; exact eq_comm
    simp [he,hh]
  · have hh : ∀ f : S, e ≠ f.val := fun f hf => he (hf.symm ▸ f.property)
    simp [he,hh]

lemma extendStar_average_apply {E : Type*} [Fintype E] [DecidableEq E]
    (S : Finset E) (z : E → ℝ) (e : E) :
    (extendStar S averagingProjector *ᵥ z) e =
      if e ∈ S then (∑ f ∈ S, z f)/(S.card : ℝ) else 0 := by
  rw [extendStar_mulVec_apply]
  split_ifs with he
  · simp only [Matrix.mulVec,dotProduct,averagingProjector,Fintype.card_coe]
    rw [← Finset.mul_sum,Finset.sum_coe_sort]
    ring
  · rfl

lemma graphActive_star_sum {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (x : CompleteEdge n → ℝ) (u : Fin n) :
    (∑ e ∈ (graphActive G).filter (fun e => u ∈ e.val), x e) =
      ∑ e ∈ edgeStar G u, graphRestrict G hG x e := by
  rw [Finset.sum_filter]
  rw [graphActive_sum G hG]
  simp only [edgeStar,Finset.sum_filter]
  rfl

lemma graphActive_star_card {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n) (u : Fin n) :
    ((graphActive G).filter (fun e => u ∈ e.val)).card = (edgeStar G u).card := by
  have hh := graphActive_star_sum G hG (fun _ => 1) u
  simpa only [graphRestrict,LinearMap.coe_mk,AddHom.coe_mk,Finset.sum_const,nsmul_eq_mul,mul_one,
    Nat.cast_inj] using hh

lemma graph_movingStarMean {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (x : CompleteEdge n → ℝ) (u : Fin n) :
    movingStarMean (fun e : CompleteEdge n => e.val) (graphActive G) x u =
      (∑ e ∈ edgeStar G u, graphRestrict G hG x e)/(edgeStar G u).card := by
  unfold movingStarMean movingStarDegree
  congr 1
  · convert graphActive_star_sum G hG x u using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext e
    simp
  · convert congrArg (Nat.cast : ℕ → ℝ) (graphActive_star_card G hG u) using 1
    all_goals try with_reducible_and_instances rfl
    congr 2
    ext e
    simp

lemma graph_movingStarLift {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (x : CompleteEdge n → ℝ) (e : CompleteEdge n) (he : e ∈ graphActive G) :
    movingStarLift (fun e : CompleteEdge n => e.val)
      (movingStarMean (fun e : CompleteEdge n => e.val) (graphActive G) x) e =
      graphMatrixLift G hG (globalStarAverage G) x e := by
  have heG : e.val ∈ G := (mem_graphActive G e).mp he
  change (∑ u ∈ e.val, _) = (graphExtend G (globalStarAverage G *ᵥ graphRestrict G hG x)) e
  simp only [graphExtend,LinearMap.coe_mk,AddHom.coe_mk,dite_eq_left heG]
  rw [globalStarAverage,Matrix.sum_mulVec]
  simp only [Finset.sum_apply,extendStar_average_apply,mem_edgeStar]
  rw [← Finset.sum_filter]
  have heq : Finset.univ.filter (fun u => u ∈ e.val) = e.val := by ext; simp
  rw [heq]
  exact Finset.sum_congr rfl (fun u _ => graph_movingStarMean G hG x u)

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_CenteredCodegreeNeighborSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma codegree_hazard_centering {n : ℕ} (G : Graph n) (u v : Fin n) (s : ℝ) :
    (∑ w ∈ commonNeighbors G u v,
      ((currentCodegree G u w : ℝ)+currentCodegree G v w-if {u,v} ∈ G then 1 else 0)) =
    (2*s-if {u,v} ∈ G then 1 else 0)*(currentCodegree G u v : ℝ)+
      centeredCodegreeNeighborSum G u v s := by
  classical
  have he : (∑ w ∈ commonNeighbors G u v,
      ((currentCodegree G u w : ℝ)+currentCodegree G v w-if {u,v} ∈ G then 1 else 0)) =
      (∑ _w ∈ commonNeighbors G u v, (2*s-if {u,v} ∈ G then 1 else 0))+
        centeredCodegreeNeighborSum G u v s := by
    rw [centeredCodegreeNeighborSum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w _
    ring
  rw [he]
  simp only [Finset.sum_const,nsmul_eq_mul,currentCodegree]
  ring

theorem normalized_codegree_centered_drift {n : ℕ} {G : Graph n}
    (hG : G ⊆ completeGraph n) (u v : Fin n) (huv : u ≠ v) (s t : ℝ) :
    pmfMean (step G) (fun H => (currentCodegree H u v : ℝ)/t)-
      (currentCodegree G u v : ℝ)/s =
    (currentCodegree G u v : ℝ)*(1/t-1/s)-
      ((2*s-if {u,v} ∈ G then 1 else 0)*(currentCodegree G u v : ℝ)+
        centeredCodegreeNeighborSum G u v s)/((triangles G).card*t) := by
  by_cases hQ : (triangles G).Nonempty
  · have hd := step_mean_codegree hG hQ u v huv
    rw [codegree_hazard_centering G u v s] at hd
    simp only [div_eq_mul_inv,pmfMean_mul_const] at hd ⊢
    rw [hd,mul_inv_rev]
    ring
  · have hzero : triangles G = ∅ := Finset.not_nonempty_iff_eq_empty.mp hQ
    rw [step,dite_eq_right hQ,pmfMean_pure,hzero,Finset.card_empty,Nat.cast_zero,zero_mul,div_zero]
    ring

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_ExtendedLinkMulVec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Classical Matrix

namespace SharpTerminalLeave

lemma extended_link_mulVec_neighbor {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (u : Fin n) (v : neighbors G u) (z : G → ℝ) :
    (extendStar (edgeStar G u) (linkStarMatrix G hG u) *ᵥ z) (neighborEdge G u v).val =
      ∑ w : neighbors G u, if {v.val,w.val} ∈ G then z (neighborEdge G u w).val else 0 := by
  rw [extendStar_mulVec_apply,dite_eq_left (neighborEdge G u v).property]
  simp only [Matrix.mulVec,dotProduct,linkStarMatrix,Matrix.reindex_apply,Matrix.submatrix_apply]
  rw [← Equiv.sum_comp (neighborEdgeEquiv G hG u)]
  have hev : (⟨(neighborEdge G u v).val,(neighborEdge G u v).property⟩ : edgeStar G u) =
      neighborEdgeEquiv G hG u v := rfl
  rw [hev]
  simp only [Equiv.symm_apply_apply,SimpleGraph.adjMatrix_apply,linkSimpleGraph_adj]
  apply Finset.sum_congr rfl
  intro w _
  split_ifs <;> simp only [one_mul,zero_mul]
  rfl

lemma neighbor_filtered_sum {n : ℕ} (G : Graph n) (u v : Fin n) (f : Fin n → ℝ) :
    (∑ w : neighbors G u, if {v,w.val} ∈ G then f w.val else 0) =
      ∑ w ∈ commonNeighbors G u v, f w := by
  trans ∑ w ∈ neighbors G u, if {v,w} ∈ G then f w else 0
  · exact Finset.sum_coe_sort (neighbors G u) (fun w : Fin n => if {v,w} ∈ G then f w else 0)
  rw [← Finset.sum_filter]
  congr 1
  ext w
  simp [neighbors,mem_commonNeighbors]

lemma extended_link_codegree_action {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (u : Fin n) (v : neighbors G u) (s : ℝ) :
    (extendStar (edgeStar G u) (linkStarMatrix G hG u) *ᵥ
      (fun e : G => (triangleDegree G e.val : ℝ)/s-1)) (neighborEdge G u v).val =
      ∑ w ∈ commonNeighbors G u v.val, ((currentCodegree G u w : ℝ)/s-1) := by
  rw [extended_link_mulVec_neighbor]
  have he : (fun w : neighbors G u =>
      if {v.val,w.val} ∈ G then (triangleDegree G (neighborEdge G u w).val.val : ℝ)/s-1 else 0) =
      (fun w : neighbors G u => if {v.val,w.val} ∈ G then (currentCodegree G u w.val : ℝ)/s-1 else 0) := by
    funext w
    simp only [neighborEdge,triangleDegree_eq_codegree hG (Finset.mem_filter.mp w.property).2]
  rw [he]
  exact neighbor_filtered_sum G u v.val (fun w => (currentCodegree G u w : ℝ)/s-1)

lemma global_link_codegree_action {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (u v : Fin n) (he : {u,v} ∈ G) (s : ℝ) (hs : s ≠ 0) :
    (globalLinkAdjacency G hG *ᵥ (fun e : G => (triangleDegree G e.val : ℝ)/s-1)) ⟨{u,v},he⟩ =
      centeredCodegreeNeighborSum G u v s/s := by
  have huv := edge_pair_ne hG he
  let z : G → ℝ := fun e => (triangleDegree G e.val : ℝ)/s-1
  have hz : ∀ a : Fin n, a ∉ ({u,v} : Finset (Fin n)) →
      (extendStar (edgeStar G a) (linkStarMatrix G hG a) *ᵥ z) ⟨{u,v},he⟩ = 0 := by
    intro a ha
    rw [extendStar_mulVec_apply,dite_eq_right]
    simpa only [mem_edgeStar] using ha
  have heq : (globalLinkAdjacency G hG *ᵥ z) ⟨{u,v},he⟩ =
      ∑ a ∈ ({u,v} : Finset (Fin n)),
        (extendStar (edgeStar G a) (linkStarMatrix G hG a) *ᵥ z) ⟨{u,v},he⟩ := by
    rw [globalLinkAdjacency,Matrix.sum_mulVec,Finset.sum_apply]
    exact (Finset.sum_subset (Finset.subset_univ _) (fun a _ ha => hz a ha)).symm
  change (globalLinkAdjacency G hG *ᵥ z) _ = _
  rw [heq,Finset.sum_pair huv]
  have hvG : ({v,u} : Finset (Fin n)) ∈ G := by simpa only [Finset.pair_comm] using he
  have huact := extended_link_codegree_action G hG u
    (⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩⟩ : neighbors G u) s
  have hvact := extended_link_codegree_action G hG v
    (⟨u,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hvG⟩⟩ : neighbors G v) s
  change (extendStar (edgeStar G u) (linkStarMatrix G hG u) *ᵥ z) ⟨{u,v},he⟩ = _ at huact
  have hev : (⟨{v,u},hvG⟩ : G) = ⟨{u,v},he⟩ := Subtype.ext (Finset.pair_comm _ _)
  change (extendStar (edgeStar G v) (linkStarMatrix G hG v) *ᵥ z) ⟨{v,u},hvG⟩ = _ at hvact
  rw [hev] at hvact
  rw [huact,hvact]
  have hcn : commonNeighbors G v u = commonNeighbors G u v := by
    ext w; simp [mem_commonNeighbors,and_comm]
  rw [hcn,← Finset.sum_add_distrib,centeredCodegreeNeighborSum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro w _
  field_simp
  ring

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Stability_EdgeStabilityRate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

lemma triangle_relative_inverse_bound {Q S r : ℝ} (hS : 0 < S) (hr : r ≤ 1/2)
    (h : |Q/S-1| ≤ r) : 0 < Q ∧ |1-S/Q| ≤ 2*r ∧ S/Q ≤ 2 := by
  obtain ⟨hl,hu⟩ := abs_le.mp h
  have hlow : S/2 ≤ Q := by
    have hh : 1/2 ≤ Q/S := by linarith
    have hh' := (le_div_iff₀ hS).mp hh
    linarith only [hh']
  have hQ : 0 < Q := lt_of_lt_of_le (by positivity) hlow
  have hab : |Q-S| ≤ r*S := by
    have he : Q/S-1 = (Q-S)/S := by field_simp
    rw [he,abs_div,abs_of_pos hS] at h
    exact (div_le_iff₀ hS).mp h
  have hratio : S/Q ≤ 2 := (div_le_iff₀ hQ).mpr (by linarith)
  have hr0 : 0 ≤ r := (abs_nonneg _).trans h
  refine ⟨hQ,?_,hratio⟩
  have he : 1-S/Q = (Q-S)/Q := by field_simp
  rw [he,abs_div,abs_of_pos hQ]
  calc
    _ ≤ r*S/Q := div_le_div_of_nonneg_right hab hQ.le
    _ = r*(S/Q) := by ring
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hratio hr0]

lemma edge_stability_coefficients {s t Q S lam r κ : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hS : 0 < S) (hl : 0 ≤ lam)
    (hscale : t = s*(1-lam)^2) (hratio : s ≤ 2*t)
    (hident : s = lam*S) (hr : r ≤ 1/2) (hQerr : |Q/S-1| ≤ r)
    (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1) :
    (0 ≤ edgeStabilityRate s t Q ∧ edgeStabilityRate s t Q ≤ 4*lam) ∧
      |edgeStabilityScalar s t Q κ| ≤ 8*r*lam+2*lam^2+4*lam/s := by
  obtain ⟨hQ,habs,hSQ⟩ := triangle_relative_inverse_bound hS hr hQerr
  have hr0 : 0 ≤ r := (abs_nonneg _).trans hQerr
  have hsQ : s/Q ≤ 2*lam := by
    rw [hident,mul_div_assoc]
    simpa only [mul_comm lam 2] using mul_le_mul_of_nonneg_left hSQ hl
  have hsQdiff : |lam-s/Q| ≤ 2*r*lam := by
    have he : lam-s/Q = lam*(1-S/Q) := by rw [hident]; ring
    rw [he,abs_mul,abs_of_nonneg hl]
    nlinarith only [mul_le_mul_of_nonneg_left habs hl]
  have hsT : s/t ≤ 2 := (div_le_iff₀ ht).mpr hratio
  have haeq : edgeStabilityRate s t Q = (s/t)*(s/Q) := by unfold edgeStabilityRate; ring
  have hbeq : edgeStabilityScalar s t Q κ =
      (s/t)*(2*(lam-s/Q)-lam^2+κ/Q) := by
    unfold edgeStabilityScalar edgeStabilityRate
    apply (mul_right_cancel₀ ht.ne')
    field_simp [hs.ne',ht.ne',hQ.ne']
    rw [hscale]
    ring
  constructor
  · rw [haeq]
    exact ⟨by positivity,(mul_le_mul hsT hsQ (by positivity) (by norm_num)).trans_eq (by ring)⟩
  · have hκQ : |κ/Q| ≤ 2*lam/s := by
      rw [abs_of_nonneg (div_nonneg hκ hQ.le)]
      apply (le_div_iff₀ hs).mpr
      have hh := div_le_div_of_nonneg_right hκ1 hQ.le
      have hm := mul_le_mul_of_nonneg_right hh hs.le
      calc
        _ ≤ (1/Q)*s := hm
        _ = s/Q := by ring
        _ ≤ _ := hsQ
    have hb : |2*(lam-s/Q)-lam^2+κ/Q| ≤ 4*r*lam+lam^2+2*lam/s := by
      calc
        _ ≤ |2*(lam-s/Q)-lam^2|+|κ/Q| := abs_add_le _ _
        _ ≤ |2*(lam-s/Q)|+|lam^2|+|κ/Q| := by linarith only [abs_sub (2*(lam-s/Q)) (lam^2)]
        _ ≤ 4*r*lam+lam^2+2*lam/s := by
          rw [abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),abs_of_nonneg (sq_nonneg lam)]
          linarith only [hsQdiff,hκQ]
    rw [hbeq,abs_mul,abs_of_pos (div_pos hs ht)]
    calc
      _ ≤ 2*(4*r*lam+lam^2+2*lam/s) := mul_le_mul hsT hb (abs_nonneg _) (by norm_num)
      _ = _ := by ring

lemma early_codegree_grid {n i : ℕ} (hn : 0 < n)
    (hp : 1/(n : ℝ) ≤ prefixDensity n) (hi : i < prefixTime n) :
    earlyTemplateScale 1 2 n (i+1) = earlyTemplateScale 1 2 n i*
      (1-6/(n : ℝ)^2/earlyDensity n i)^2 ∧
    earlyTemplateScale 1 2 n i = (6/(n : ℝ)^2/earlyDensity n i)*earlyTriangleScale n i ∧
    0 ≤ 6/(n : ℝ)^2/earlyDensity n i ∧
    6/(n : ℝ)^2/earlyDensity n i ≤ 6/(n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpi := early_density_positive hn hp hi.le
  have hs := earlyDensity_succ n i
  have he : earlyDensity n (i+1) = earlyDensity n i*(1-6/(n : ℝ)^2/earlyDensity n i) := by
    have he : earlyDensity n (i+1) = earlyDensity n i-6/(n : ℝ)^2 := by linarith only [hs]
    rw [he]
    field_simp
  refine ⟨?_,?_,by positivity,?_⟩
  · simp only [earlyTemplateScale,pow_one,he,mul_pow]; ring
  · unfold earlyTriangleScale
    simp only [earlyTemplateScale,pow_one]
    field_simp
  · have hp' := hp.trans (earlyDensity_antitone n hi.le)
    apply (div_le_iff₀ hpi).mpr
    have hm := mul_le_mul_of_nonneg_left hp' (show 0 ≤ 6/(n : ℝ) by positivity)
    convert hm using 1
    all_goals try with_reducible_and_instances rfl
    field_simp

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_CompleteEdgePair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical Matrix

namespace SharpTerminalLeave

lemma centeredEdgeVector_restrict {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n) (s : ℝ) :
    graphRestrict G hG (centeredEdgeVector G s) = fun e : G => (triangleDegree G e.val : ℝ)/s-1 := by
  funext e
  let uv := completeEdgePair (graphEdgeEmbed G hG e)
  have he : e.val = {uv.val.1,uv.val.2} := uv.property.2
  change (currentCodegree G uv.val.1 uv.val.2 : ℝ)/s-1 = _
  rw [he,triangleDegree_eq_codegree hG (he ▸ e.property)]

lemma graphMatrixLift_apply {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (M : Matrix G G ℝ) (z : CompleteEdge n → ℝ) (e : CompleteEdge n) (he : e.val ∈ G) :
    graphMatrixLift G hG M z e = (M *ᵥ graphRestrict G hG z) ⟨e.val,he⟩ := by
  change (if he : e.val ∈ G then _ else 0) = _
  rw [dite_eq_left he]
  rfl

lemma graph_centered_normalized_operator {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (s : ℝ) (e : CompleteEdge n) (he : e.val ∈ G) :
    graphMatrixLift G hG (s⁻¹ • globalLinkAdjacency G hG) (centeredEdgeVector G s) e =
      centeredCodegreeNeighborSum G (completeEdgePair e).val.1 (completeEdgePair e).val.2 s/s^2 := by
  by_cases hs : s = 0
  · subst s; simp [graphMatrixLift]
  let uv := completeEdgePair e
  have heq : e.val = {uv.val.1,uv.val.2} := uv.property.2
  rw [graphMatrixLift_apply _ _ _ _ _ he,centeredEdgeVector_restrict,Matrix.smul_mulVec]
  simp only [Pi.smul_apply,smul_eq_mul]
  have hp : {uv.val.1,uv.val.2} ∈ G := heq ▸ he
  have hei : (⟨e.val,he⟩ : G) = ⟨{uv.val.1,uv.val.2},hp⟩ := Subtype.ext heq
  rw [hei,global_link_codegree_action G hG _ _ hp s hs]
  dsimp only [uv]
  ring

lemma graph_star_residual_sum {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (s : ℝ) (z : CompleteEdge n → ℝ) (e : CompleteEdge n) (he : e.val ∈ G) :
    movingStarLift (fun e : CompleteEdge n => e.val)
      (movingStarMean (fun e : CompleteEdge n => e.val) (graphActive G) z) e+
      graphMatrixLift G hG (s⁻¹ • globalLinkAdjacency G hG-globalStarAverage G) z e =
      graphMatrixLift G hG (s⁻¹ • globalLinkAdjacency G hG) z e := by
  rw [graph_movingStarLift G hG z e ((mem_graphActive _ _).mpr he)]
  simp only [graphMatrixLift_apply G hG _ _ _ he,Matrix.sub_mulVec,Pi.sub_apply]
  ring

lemma centered_edge_operator_drift {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (s t : ℝ) (hs : s ≠ 0) (e : CompleteEdge n) (he : e.val ∈ G) :
    pmfMean (step G) (fun H => (currentCodegree H (completeEdgePair e).val.1 (completeEdgePair e).val.2 : ℝ)/t)-
      (centeredEdgeVector G s e+1) =
      -edgeStabilityRate s t (triangles G).card*
        (movingStarLift (fun e : CompleteEdge n => e.val)
          (movingStarMean (fun e : CompleteEdge n => e.val) (graphActive G) (centeredEdgeVector G s)) e+
          graphMatrixLift G hG (s⁻¹ • globalLinkAdjacency G hG-globalStarAverage G) (centeredEdgeVector G s) e)+
      edgeStabilityScalar s t (triangles G).card 1*(centeredEdgeVector G s e+1) := by
  rw [graph_star_residual_sum G hG s _ e he,graph_centered_normalized_operator G hG s e he]
  let uv := completeEdgePair e
  have huv := uv.property.1
  have hep : {uv.val.1,uv.val.2} ∈ G := uv.property.2 ▸ he
  dsimp only [centeredEdgeVector]
  simp only [sub_add_cancel]
  rw [normalized_codegree_centered_drift hG _ _ huv s t,ite_eq_left hep]
  unfold edgeStabilityScalar edgeStabilityRate
  field_simp [hs]
  ring

lemma prefixEdgeForcing_zero {n : ℕ} (ω : History (Graph n) (prefixTime n)) :
    prefixEdgeForcing ω 0 = prefixCenteredEdge ω 0 := by
  funext e
  simp [prefixEdgeForcing]

lemma prefix_centered_edge_recurrence {n i : ℕ} (ω : History (Graph n) (prefixTime n))
    (hω : ω ∈ (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n)).support)
    (hi : i < prefixTime n) (hs : earlyTemplateScale 1 2 n i ≠ 0)
    (e : CompleteEdge n) (he : e ∈ graphActive (ω (historyIndex (prefixTime n) (i+1)))) :
    prefixCenteredEdge ω (i+1) e = prefixCenteredEdge ω i e-
      prefixEdgeRate ω i*(movingStarLift (fun e : CompleteEdge n => e.val)
        (movingStarMean (fun e : CompleteEdge n => e.val)
          (graphActive (ω (historyIndex (prefixTime n) i))) (prefixCenteredEdge ω i)) e+
        prefixEdgeResidual ω hω i (prefixCenteredEdge ω i) e)+
      (prefixEdgeForcing ω (i+1) e-prefixEdgeForcing ω i e) := by
  have hpath := (historyLaw_path_support (PMF.pure (completeGraph n)) (fun _ => step)
    (prefixTime n) (prefixTime n) le_rfl ω hω).2 i hi
  have he0 : e.val ∈ ω (historyIndex (prefixTime n) i) := step_support_subset hpath ((mem_graphActive _ _).mp he)
  have hd := centered_edge_operator_drift _ (history_valid_all ω hω i)
    (earlyTemplateScale 1 2 n i) (earlyTemplateScale 1 2 n (i+1)) hs e he0
  unfold prefixEdgeForcing
  rw [historyNoise_succ_same _ _ _ _ hi,Finset.sum_range_succ]
  simp only [historyIncrement] at *
  change _ = _ at hd
  dsimp only [prefixCenteredEdge,prefixEdgeRate,prefixEdgeScalar,prefixEdgeResidual] at *
  dsimp only [centeredEdgeVector] at *
  linarith only [hd]

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_PrefixTriangleRadius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

lemma triangle_closure_budget : ∀ᶠ n : ℕ in atTop,
    0 ≤ prefixEdgeRadius n ∧ prefixEdgeRadius n ≤ 1/2 ∧
    4/(n : ℝ)+codegreeNoiseRadius n+12*(prefixEdgeRadius n)^2*Real.log n+
      2/prefixD n+216*Real.log n/(n : ℝ) ≤ prefixTriangleRadius n := by
  have hrad : Tendsto prefixEdgeRadius atTop (nhds 0) := by
    change Tendsto (fun n : ℕ => (n : ℝ)^(-1/40000 : ℝ)) atTop (nhds 0)
    simpa only [Function.comp_def,neg_div] using (tendsto_rpow_neg_atTop
      (by norm_num : (0 : ℝ) < 1/40000)).comp tendsto_natCast_atTop_atTop
  filter_upwards [prefixTemplateFactor_subpower 1 (by norm_num : (0 : ℝ) < 1/80000)
      (by norm_num : (0 : ℝ) < 1/235),prefixD_eventual_envelope,
    hrad.eventually_le_const (by norm_num : (0 : ℝ) < 1/2),
    eventually_ge_atTop (1 : ℕ)] with n hlog hD hrad hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have he : (prefixEdgeRadius n)^2 = (n : ℝ)^(-1/20000 : ℝ) := by
    unfold prefixEdgeRadius
    rw [← Real.rpow_natCast,← Real.rpow_mul hn0.le]
    norm_num
  have hinv : 1/(n : ℝ) ≤ (prefixEdgeRadius n)^2 := by
    rw [he]
    simpa only [Real.rpow_neg_one,one_div] using
      (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (-1 : ℝ) ≤ -1/20000))
  have hnoise : codegreeNoiseRadius n ≤ (prefixEdgeRadius n)^2 := by
    rw [he]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have hdisc : 1/prefixD n ≤ (prefixEdgeRadius n)^2 := by
    rw [he]
    apply (div_le_div_of_nonneg_left zero_le_one (Real.rpow_pos_of_pos hn0 _) hD.1).trans
    rw [one_div,← Real.rpow_neg hn0.le]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have hl : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hs := mul_le_mul_of_nonneg_right (show 1+Real.log (n : ℝ) ≤
      1/235*(n : ℝ)^(1/80000 : ℝ) by
        simpa only [prefixTemplateFactor,Real.rpow_one] using hlog)
      (show 0 ≤ 235*(prefixEdgeRadius n)^2 by positivity)
  have hprod : (n : ℝ)^(1/80000 : ℝ)*(prefixEdgeRadius n)^2 = prefixTriangleRadius n := by
    rw [he,← Real.rpow_add hn0]
    norm_num [prefixTriangleRadius]
  have hscaled : 235*(1+Real.log (n : ℝ))*(prefixEdgeRadius n)^2 ≤ prefixTriangleRadius n := by
    nlinarith only [hs,hprod]
  refine ⟨Real.rpow_nonneg hn0.le _,hrad,?_⟩
  have hgrid := mul_le_mul_of_nonneg_left hinv (show 0 ≤ 216*Real.log (n : ℝ) by positivity)
  simp only [div_eq_mul_inv,one_mul] at hinv hdisc hgrid ⊢
  nlinarith only [hinv,hnoise,hdisc,hgrid,hscaled,sq_nonneg (prefixEdgeRadius n),
    mul_nonneg (sq_nonneg (prefixEdgeRadius n)) hl]

theorem prefix_triangle_tracking : ∀ᶠ n : ℕ in atTop,
    ∀ ω : History (Graph n) (prefixTime n),
    ω ∈ (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n)).support →
    PrefixTriangleNoise n ω → ∀ j ≤ prefixTime n,
    historyAlive (fun i => densityEdgeSafe n (earlyDensity n i) (prefixEdgeRadius n)) (prefixTime n) j ω →
    |(triangles (ω (historyIndex (prefixTime n) j))).card/earlyTriangleScale n j-1| ≤
      prefixTriangleRadius n := by
  filter_upwards [triangle_closure_budget,earlyTriangleScale_regular,
    prefixDensity_eventually_inverse_lower,eventually_ge_atTop (2 : ℕ)] with n hb hr hp hn
  intro ω hω hnse j hj hsafe
  have hn0 : 0 < n := by omega
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hi := (historyLaw_path_support (PMF.pure (completeGraph n)) (fun _ => step)
    (prefixTime n) (prefixTime n) le_rfl ω hω).1
  have hi' : ω (historyIndex (prefixTime n) 0) = completeGraph n := by
    simpa only [PMF.mem_support_pure_iff] using hi
  have hloads : pastRelativeCopyLoadsSafe (triangleRequired (n := n)) (triangleNoiseLoad n)
      (prefixTime n) j ω := by
    intro i hit
    have hij : i < j := lt_of_lt_of_le hit (Nat.min_le_left _ _)
    have hh := densityEdgeSafe_triangle_load (early_density_positive hn0 hp (by omega)).le
      (show prefixEdgeRadius n ≤ 1 by linarith only [hb.2.1]) (hsafe i hij)
    simpa only [triangleNoiseLoad,earlyTemplateScale,pow_one] using hh
  have hcap : ∀ i < j, copyCount (triangleRequired (n := n)) (ω (historyIndex (prefixTime n) i)) ≤
      2*earlyTriangleScale n i := by
    intro i hij
    rw [triangle_copyCount]
    have hh := (densityEdgeSafe_triangle_bounds (hsafe i hij)).2
    have hS : 0 ≤ earlyTriangleScale n i := (hr.1 i (by omega)).le
    change _ ≤ earlyTriangleScale n i*(1+prefixEdgeRadius n) at hh
    have ht := mul_le_mul_of_nonneg_right hb.2.1 hS
    linarith only [hh,ht,hS]
  have hnoise : |historyNoise (fun _ => step)
      (fun i G => ((triangles G).card : ℝ)/earlyTriangleScale n i) (prefixTime n) j ω| < codegreeNoiseRadius n := by
    apply lt_of_not_ge
    intro hcross
    apply hnse
    refine ⟨j,hj,hloads,hcap,?_⟩
    simpa only [triangle_copyCount] using hcross
  have hd := early_triangle_drift_bound (prefixEdgeRadius n) hn0 hp hb.1 hb.2.1
    hr.2.2.1 j hj ω hsafe
  have hinit : |(triangles (ω (historyIndex (prefixTime n) 0))).card/earlyTriangleScale n 0-1| ≤ 4/(n : ℝ) := by
    rw [hi',initial_triangle_relative_error hn,neg_div,abs_neg,abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1/((n : ℝ)-1)^2)]
    apply (div_le_div_iff₀ (sq_pos_of_ne_zero (by linarith)) (by linarith : (0 : ℝ) < n)).mpr
    nlinarith
  have ht := (abs_add_le
    (((triangles (ω (historyIndex (prefixTime n) j))).card : ℝ)/earlyTriangleScale n j-
      (triangles (ω (historyIndex (prefixTime n) 0))).card/earlyTriangleScale n 0-
      historyNoise (fun _ => step) (fun i G => ((triangles G).card : ℝ)/earlyTriangleScale n i) (prefixTime n) j ω)
    (historyNoise (fun _ => step) (fun i G => ((triangles G).card : ℝ)/earlyTriangleScale n i) (prefixTime n) j ω))
  have ht' := abs_add_le
    (((triangles (ω (historyIndex (prefixTime n) j))).card : ℝ)/earlyTriangleScale n j-
      (triangles (ω (historyIndex (prefixTime n) 0))).card/earlyTriangleScale n 0)
    (((triangles (ω (historyIndex (prefixTime n) 0))).card : ℝ)/earlyTriangleScale n 0-1)
  simp only [sub_add_cancel] at ht
  simp only [sub_add_sub_cancel] at ht'
  linarith only [ht,ht',hd,hnoise,hinit,hb.2.2]

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_PrefixEdgeForcingBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

lemma prefix_edge_forcing_power : ∀ᶠ n : ℕ in atTop,
    0 ≤ prefixEdgeForcingBound n ∧
    prefixEdgeForcingBound n ≤ 49*(1+Real.log (n : ℝ))*prefixTriangleRadius n := by
  filter_upwards [prefixD_eventual_envelope,eventually_ge_atTop (1 : ℕ)] with n hD hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have ht : 0 ≤ prefixTriangleRadius n := Real.rpow_nonneg hn0.le _
  have hl := Real.log_nonneg hn1
  have hD0 := lt_of_lt_of_le (Real.rpow_pos_of_pos hn0 _) hD.1
  have hi : 1/(n : ℝ) ≤ prefixTriangleRadius n := by
    simpa only [Real.rpow_neg_one,one_div,prefixTriangleRadius] using
      (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (-1 : ℝ) ≤ -3/80000))
  have hno0 : 0 ≤ codegreeNoiseRadius n := Real.rpow_nonneg hn0.le _
  have hno : codegreeNoiseRadius n ≤ prefixTriangleRadius n :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have hdi : 1/prefixD n ≤ prefixTriangleRadius n := by
    apply (div_le_div_of_nonneg_left zero_le_one (Real.rpow_pos_of_pos hn0 _) hD.1).trans
    rw [one_div,← Real.rpow_neg hn0.le]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have hg := mul_le_mul_of_nonneg_left hi (show 0 ≤ 24*Real.log (n : ℝ) by positivity)
  constructor
  · unfold prefixEdgeForcingBound
    positivity
  · unfold prefixEdgeForcingBound
    simp only [div_eq_mul_inv,one_mul] at hi hdi hg ⊢
    nlinarith only [hi,hno,hdi,hg,ht,mul_nonneg ht hl]

lemma edge_stability_log_bounds {L S : ℝ} (hL : 0 ≤ L) (hS : 0 ≤ S) (hS' : S ≤ 4*L) :
    0 ≤ 1+2*S ∧ 1+2*S ≤ 8*(1+L) ∧
    (1+2*S)*S ≤ 32*(1+L)^2 ∧
    (1+2*S)*S*6 ≤ 192*(1+L)^2 := by
  have hp := mul_le_mul (show 1+2*S ≤ 8*(1+L) by linarith) hS'
    hS (show 0 ≤ 8*(1+L) by positivity)
  have hpoly : 8*(1+L)*(4*L) ≤ 32*(1+L)^2 := by nlinarith only [hL]
  refine ⟨by positivity,by linarith,hp.trans hpoly,?_⟩
  nlinarith only [hp,hpoly]

lemma edge_stability_gain_bound {K : ℕ} {L S F r : ℝ}
    (hL : 0 ≤ L) (hS : 0 ≤ S) (hS' : S ≤ 4*L) (hF : 0 ≤ F)
    (hr : 0 ≤ r) (hF' : F ≤ 49*(1+L)*r) :
    2*(∑ j ∈ Finset.range K, ((1+2*S)*S*6)^j)*(1+2*S)*F ≤
      (784*(K : ℝ)*192^K)*(1+L)^(2*K+2)*r := by
  obtain ⟨hB,hB',_,hA⟩ := edge_stability_log_bounds hL hS hS'
  have hbase : 1 ≤ 192*(1+L)^2 := by nlinarith only [hL,sq_nonneg L]
  have hsum : (∑ j ∈ Finset.range K, ((1+2*S)*S*6)^j) ≤
      (K : ℝ)*(192*(1+L)^2)^K := by
    calc
      _ ≤ ∑ _j ∈ Finset.range K, (192*(1+L)^2)^K := by
        apply Finset.sum_le_sum
        intro j hj
        exact (pow_le_pow_left₀ (by positivity) hA j).trans
          (pow_le_pow_right₀ hbase (Finset.mem_range.mp hj).le)
      _ = _ := by simp
  have hs0 : 0 ≤ ∑ j ∈ Finset.range K, ((1+2*S)*S*6)^j := by positivity
  calc
    _ ≤ 2*(∑ j ∈ Finset.range K, ((1+2*S)*S*6)^j)*(1+2*S)*(49*(1+L)*r) :=
      mul_le_mul le_rfl hF' hF (mul_nonneg (mul_nonneg (by norm_num) hs0) hB)
    _ ≤ 2*((K : ℝ)*(192*(1+L)^2)^K)*(8*(1+L))*(49*(1+L)*r) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg (by positivity) hr)
      gcongr
    _ = _ := by rw [mul_pow,← pow_mul,pow_add,pow_succ, pow_succ]; ring

theorem prefix_edge_stability_budget {γ : ℝ} (hγ : 0 < γ) :
    ∃ K : ℕ, 0 < K ∧ ∀ᶠ n : ℕ in atTop, ∀ S : ℝ,
      0 ≤ S → S ≤ 4*Real.log n →
      ((1+2*S)*S*(n : ℝ)^(-γ))^K*(n : ℝ)^2 ≤ 1/2 ∧
      2*(∑ j ∈ Finset.range K, ((1+2*S)*S*6)^j)*(1+2*S)*prefixEdgeForcingBound n ≤
        prefixEdgeRadius n/2 := by
  obtain ⟨K,hK⟩ := exists_nat_gt (3/γ)
  have hKγ : 3 < γ*(K : ℝ) := by
    have hh := (div_lt_iff₀ hγ).mp hK
    nlinarith only [hh]
  have hK0 : 0 < K := by
    have hkR : (0 : ℝ) < K := lt_trans (by positivity) hK
    exact_mod_cast hkR
  let C : ℝ := 784*(K : ℝ)*192^K
  have hC : 0 < C := by dsimp [C]; positivity
  have hremexp : 0 < γ*(K : ℝ)-2 := by linarith
  refine ⟨K,hK0,?_⟩
  filter_upwards [prefix_edge_forcing_power,
    prefixTemplateFactor_subpower (2*K : ℝ) hremexp
      (by positivity : (0 : ℝ) < 1/(2*32^K)),
    prefixTemplateFactor_subpower (2*K+2 : ℝ)
      (by norm_num : (0 : ℝ) < 1/80000) (by positivity : (0 : ℝ) < 1/(2*C)),
    eventually_ge_atTop (1 : ℕ)] with n hF hrem hgain hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hl := Real.log_nonneg hn1
  have htr0 : 0 ≤ prefixTriangleRadius n := Real.rpow_nonneg hn0.le _
  have hrem' : (1+Real.log (n : ℝ))^(2*K) ≤
      1/(2*32^K)*(n : ℝ)^(γ*(K : ℝ)-2) := by
    convert hrem using 1
    all_goals try with_reducible_and_instances rfl
    simp only [prefixTemplateFactor]
    rw [← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  have hgain' : (1+Real.log (n : ℝ))^(2*K+2) ≤
      1/(2*C)*(n : ℝ)^(1/80000 : ℝ) := by
    convert hgain using 1
    all_goals try with_reducible_and_instances rfl
    simp only [prefixTemplateFactor]
    rw [← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  intro S hS hS'
  obtain ⟨hB,hB',hA,_⟩ := edge_stability_log_bounds hl hS hS'
  constructor
  · calc
      _ ≤ (32*(1+Real.log (n : ℝ))^2*(n : ℝ)^(-γ))^K*(n : ℝ)^2 := by gcongr
      _ = 32^K*(1+Real.log (n : ℝ))^(2*K)*(n : ℝ)^(-γ*(K : ℝ)+2) := by
        rw [mul_pow,mul_pow,← pow_mul]
        have he : ((n : ℝ)^(-γ))^K*(n : ℝ)^2 = (n : ℝ)^(-γ*(K : ℝ)+2) := by
          rw [← Real.rpow_natCast ((n : ℝ)^(-γ)) K,← Real.rpow_mul hn0.le,
            ← Real.rpow_natCast (n : ℝ) 2,← Real.rpow_add hn0]
          norm_num
        rw [mul_assoc (32^K*(1+Real.log (n : ℝ))^(2*K)),he]
      _ ≤ 32^K*(1/(2*32^K)*(n : ℝ)^(γ*(K : ℝ)-2))*(n : ℝ)^(-γ*(K : ℝ)+2) := by gcongr
      _ = 1/2 := by
        rw [mul_assoc, mul_assoc,← Real.rpow_add hn0]
        simp only [show γ*(K : ℝ)-2+(-γ*(K : ℝ)+2) = 0 by ring,Real.rpow_zero,mul_one]
        field_simp
  · have hb := edge_stability_gain_bound hl hS hS' hF.1
      htr0 hF.2 (K := K)
    apply hb.trans
    change C*(1+Real.log (n : ℝ))^(2*K+2)*prefixTriangleRadius n ≤ _
    calc
      _ ≤ C*(1/(2*C)*(n : ℝ)^(1/80000 : ℝ))*prefixTriangleRadius n := by gcongr
      _ = prefixEdgeRadius n/2 := by
        have he : (n : ℝ)^(1/80000 : ℝ)*prefixTriangleRadius n = prefixEdgeRadius n := by
          unfold prefixTriangleRadius prefixEdgeRadius
          rw [← Real.rpow_add hn0]
          norm_num
        calc
          _ = (C*(1/(2*C)))*((n : ℝ)^(1/80000 : ℝ)*prefixTriangleRadius n) := by ring
          _ = prefixEdgeRadius n/2 := by rw [he]; field_simp

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_HistoryGraphNested
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

lemma history_graph_nested {n T : ℕ} (ω : History (Graph n) T)
    (hω : ω ∈ (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) T T).support)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ T) :
    ω (historyIndex T j) ⊆ ω (historyIndex T i) := by
  have hp := (historyLaw_path_support (PMF.pure (completeGraph n)) (fun _ => step)
    T T le_rfl ω hω).2
  induction j, hij using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ k hik ih => exact (step_support_subset (hp k (by omega))).trans (ih (by omega))

lemma densityEdgeSafe_pair_upper {n : ℕ} {p η : ℝ} {G : Graph n}
    (hp : 0 ≤ (n : ℝ)*p^2) (hη : η ≤ 1) (h : densityEdgeSafe n p η G)
    (u v : Fin n) (he : {u,v} ∈ G) :
    (currentCodegree G u v : ℝ) ≤ 2*((n : ℝ)*p^2) := by
  have hh := (abs_le.mp (h.2.2 {u,v} he)).2
  rw [triangleDegree_eq_codegree h.1 he] at hh
  nlinarith only [hh,mul_le_mul_of_nonneg_right hη hp]

lemma initial_centered_edge_bound {n : ℕ} (hn : 2 ≤ n)
    (ω : History (Graph n) (prefixTime n))
    (hω : ω ∈ (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n)).support)
    (e : CompleteEdge n) : |prefixCenteredEdge ω 0 e| ≤ 4/(n : ℝ) := by
  have hi := (historyLaw_path_support (PMF.pure (completeGraph n)) (fun _ => step)
    (prefixTime n) (prefixTime n) le_rfl ω hω).1
  have hi' : ω (historyIndex (prefixTime n) 0) = completeGraph n := by simpa using hi
  unfold prefixCenteredEdge centeredEdgeVector
  rw [hi',initial_normalized_codegree_error hn _ _ (completeEdgePair e).property.1,
    neg_div,abs_neg,abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1/((n : ℝ)-1)^2)]
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  apply (div_le_div_iff₀ (sq_pos_of_ne_zero (by linarith)) (by linarith : (0 : ℝ) < n)).mpr
  nlinarith

lemma prefix_triangle_radius_small : ∀ᶠ n : ℕ in atTop,
    0 ≤ prefixTriangleRadius n ∧ prefixTriangleRadius n ≤ 1/2 := by
  have hl : Tendsto prefixTriangleRadius atTop (nhds 0) := by
    change Tendsto (fun n : ℕ => (n : ℝ)^(-3/80000 : ℝ)) atTop (nhds 0)
    simpa only [Function.comp_def,neg_div] using (tendsto_rpow_neg_atTop
      (by norm_num : (0 : ℝ) < 3/80000)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hl.eventually_le_const (by norm_num : (0 : ℝ) < 1/2)] with n hn
  exact ⟨Real.rpow_nonneg (Nat.cast_nonneg _) _,hn⟩

theorem prefix_edge_coefficient_bounds : ∀ᶠ n : ℕ in atTop,
    ∀ ω : History (Graph n) (prefixTime n),
    ω ∈ (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n)).support →
    PrefixTriangleNoise n ω → ∀ j ≤ prefixTime n,
    historyAlive (fun i => densityEdgeSafe n (earlyDensity n i) (prefixEdgeRadius n)) (prefixTime n) j ω →
    (∀ i < j, 0 ≤ prefixEdgeRate ω i ∧ prefixEdgeRate ω i ≤ 1 ∧
      prefixEdgeRate ω i ≤ 4*(6/(n : ℝ)^2/earlyDensity n i) ∧
      |prefixEdgeScalar ω i| ≤ 8*prefixTriangleRadius n*(6/(n : ℝ)^2/earlyDensity n i)+
        2*(6/(n : ℝ)^2/earlyDensity n i)^2+
        4*(6/(n : ℝ)^2/earlyDensity n i)/earlyTemplateScale 1 2 n i) ∧
    (∑ i ∈ Finset.range j, prefixEdgeRate ω i) ≤ 4*Real.log n := by
  filter_upwards [prefix_triangle_tracking,earlyTemplateScale_regular 1 2,
    earlyTriangleScale_regular,prefix_triangle_radius_small,prefixDensity_eventually_inverse_lower,
    eventually_ge_atTop (24 : ℕ)] with n htrack hreg htri hr hp hn
  intro ω hω hnoise j hj hsafe
  have hni : 0 < n := by omega
  have hnR : (24 : ℝ) ≤ n := by exact_mod_cast hn
  have hcoeff : ∀ i < j, 0 ≤ prefixEdgeRate ω i ∧ prefixEdgeRate ω i ≤ 1 ∧
      prefixEdgeRate ω i ≤ 4*(6/(n : ℝ)^2/earlyDensity n i) ∧
      |prefixEdgeScalar ω i| ≤ 8*prefixTriangleRadius n*(6/(n : ℝ)^2/earlyDensity n i)+
        2*(6/(n : ℝ)^2/earlyDensity n i)^2+
        4*(6/(n : ℝ)^2/earlyDensity n i)/earlyTemplateScale 1 2 n i := by
    intro i hi
    have hiT : i < prefixTime n := by omega
    have hs := early_codegree_grid hni hp hiT
    have hc := htrack ω hω hnoise i (by omega) (fun k hk => hsafe k (by omega))
    have hb := edge_stability_coefficients (hreg.1 i (by omega)) (hreg.1 (i+1) (by omega))
      (htri.1 i (by omega)) hs.2.2.1 hs.1 (hreg.2.2 i hiT) hs.2.1 hr.2 hc
      (by norm_num : (0 : ℝ) ≤ 1) le_rfl
    have hsmall : 4*(6/(n : ℝ)^2/earlyDensity n i) ≤ 1 := by
      have hh := mul_le_mul_of_nonneg_left hs.2.2.2 (by norm_num : (0 : ℝ) ≤ 4)
      have hi : 4*(6/(n : ℝ)) ≤ 1 := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (by linarith : (0 : ℝ) < n)).mpr
        linarith only [hnR]
      exact hh.trans hi
    exact ⟨hb.1.1,hb.1.2.trans hsmall,hb.1.2,hb.2⟩
  refine ⟨hcoeff,?_⟩
  calc
    _ ≤ ∑ i ∈ Finset.range j, 4*(6/(n : ℝ)^2/earlyDensity n i) :=
      Finset.sum_le_sum (fun i hi => (hcoeff i (Finset.mem_range.mp hi)).2.2.1)
    _ = 4*(∑ i ∈ Finset.range j, 6/(n : ℝ)^2/earlyDensity n i) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (early_grid_sum_bounds hni hp j hj).1 (by norm_num)

theorem prefix_edge_forcing_bound : ∀ᶠ n : ℕ in atTop,
    ∀ ω : History (Graph n) (prefixTime n),
    ω ∈ (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n)).support →
    PrefixTriangleNoise n ω → PrefixCodegreeNoiseGood n ω → ∀ j ≤ prefixTime n,
    historyAlive (fun i => densityEdgeSafe n (earlyDensity n i) (prefixEdgeRadius n)) (prefixTime n) j ω →
    trajectorySeminorm (fun t => activeLinf (graphActive (ω (historyIndex (prefixTime n) t)))) j
      (prefixEdgeForcing ω) ≤ prefixEdgeForcingBound n := by
  filter_upwards [prefix_edge_coefficient_bounds,prefix_edge_forcing_power,triangle_closure_budget,
    prefix_triangle_radius_small,prefixDensity_eventually_inverse_lower,
    eventually_ge_atTop (2 : ℕ)] with n hcoeff hF hbud hr hp hn
  intro ω hω htri hnoise j hj hsafe
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  apply trajectorySeminorm_bound _ _ _ hF.1
  intro t ht
  apply activeLinf_bound _ _ hF.1
  intro e he
  have het : e.val ∈ ω (historyIndex (prefixTime n) t) := (mem_graphActive _ _).mp he
  have hep (i : ℕ) (hi : i < t) : e.val ∈ ω (historyIndex (prefixTime n) i) :=
    history_graph_nested ω hω hi.le (ht.trans hj) het
  have hc (i : ℕ) (hi : i < t) :
      0 ≤ prefixCenteredEdge ω i e+1 ∧ prefixCenteredEdge ω i e+1 ≤ 2 := by
    have hpos : 0 < (n : ℝ)*earlyDensity n i^2 := mul_pos hnR (sq_pos_of_pos (early_density_positive hn0 hp (by omega)))
    have hh := densityEdgeSafe_pair_upper hpos.le (show prefixEdgeRadius n ≤ 1 by linarith only [hbud.2.1])
      (hsafe i (by omega)) (completeEdgePair e).val.1 (completeEdgePair e).val.2
      ((completeEdgePair e).property.2 ▸ hep i hi)
    change 0 ≤ (currentCodegree _ _ _ : ℝ)/earlyTemplateScale 1 2 n i-1+1 ∧
      (currentCodegree _ _ _ : ℝ)/earlyTemplateScale 1 2 n i-1+1 ≤ 2
    simp only [sub_add_cancel,earlyTemplateScale,pow_one]
    exact ⟨by positivity,(div_le_iff₀ hpos).mpr hh⟩
  have hnse : |historyNoise (fun _ => step)
      (fun k H => (currentCodegree H (completeEdgePair e).val.1 (completeEdgePair e).val.2 : ℝ)/earlyTemplateScale 1 2 n k)
      (prefixTime n) t ω| < codegreeNoiseRadius n := by
    apply lt_of_not_ge
    intro hx
    apply hnoise (completeEdgePair e).val.1 (completeEdgePair e).val.2
    refine ⟨t,by omega,?_,hx⟩
    intro i hi
    have hpos := mul_pos hnR (sq_pos_of_pos (early_density_positive hn0 hp (by omega : i ≤ prefixTime n)))
    have hh := (hc i hi).2
    change (currentCodegree _ _ _ : ℝ)/earlyTemplateScale 1 2 n i-1+1 ≤ 2 at hh
    simp only [sub_add_cancel,earlyTemplateScale,pow_one] at hh
    simpa only [earlyTemplateScale,pow_one] using (div_le_iff₀ hpos).mp hh
  have hcb := (hcoeff ω hω htri j hj hsafe).1
  have hsumb : |∑ i ∈ Finset.range t, prefixEdgeScalar ω i*(prefixCenteredEdge ω i e+1)| ≤
      16*prefixTriangleRadius n*Real.log n+4/prefixD n+24*Real.log n/(n : ℝ) := by
    have hgrid := early_grid_sum_bounds hn0 hp t (by omega)
    calc
      _ ≤ ∑ i ∈ Finset.range t, |prefixEdgeScalar ω i*(prefixCenteredEdge ω i e+1)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range t,
          (16*prefixTriangleRadius n*(6/(n : ℝ)^2/earlyDensity n i)+
            4*(6/(n : ℝ)^2/earlyDensity n i)^2+
            8*(6/(n : ℝ)^2/earlyDensity n i)/((n : ℝ)*earlyDensity n i^2)) := by
        apply Finset.sum_le_sum
        intro i hi
        have hit := Finset.mem_range.mp hi
        rw [abs_mul,abs_of_nonneg (hc i hit).1]
        have hh := (mul_le_mul_of_nonneg_left (hc i hit).2 (abs_nonneg (prefixEdgeScalar ω i))).trans
          (mul_le_mul_of_nonneg_right (hcb i (by omega)).2.2.2 (by norm_num : (0 : ℝ) ≤ 2))
        exact hh.trans_eq (by simp only [earlyTemplateScale,pow_one]; ring)
      _ = 16*prefixTriangleRadius n*(∑ i ∈ Finset.range t, 6/(n : ℝ)^2/earlyDensity n i)+
          4*(∑ i ∈ Finset.range t, (6/(n : ℝ)^2/earlyDensity n i)^2)+
          8*(∑ i ∈ Finset.range t, (6/(n : ℝ)^2/earlyDensity n i)/((n : ℝ)*earlyDensity n i^2)) := by
        simp only [Finset.mul_sum,← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ _ := by
        have h₁ := mul_le_mul_of_nonneg_left hgrid.1 (show 0 ≤ 16*prefixTriangleRadius n by exact mul_nonneg (by norm_num) hr.1)
        have h₂ := mul_le_mul_of_nonneg_left hgrid.2.2 (by norm_num : (0 : ℝ) ≤ 4)
        have h₃ := mul_le_mul_of_nonneg_left hgrid.2.1 (by norm_num : (0 : ℝ) ≤ 8)
        simp only [div_eq_mul_inv,mul_inv_rev] at h₁ h₂ h₃ ⊢
        norm_num at h₃
        nlinarith only [h₁,h₂,h₃]
  have hi := initial_centered_edge_bound hn ω hω e
  unfold prefixEdgeForcing prefixEdgeForcingBound
  calc
    _ ≤ |prefixCenteredEdge ω 0 e|+
        |historyNoise (fun _ => step) (fun k H => (currentCodegree H (completeEdgePair e).val.1 (completeEdgePair e).val.2 : ℝ)/earlyTemplateScale 1 2 n k) (prefixTime n) t ω|+
        |∑ k ∈ Finset.range t, prefixEdgeScalar ω k*(prefixCenteredEdge ω k e+1)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by linarith only [hi,hnse,hsumb]

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_CenteredEdgeVectorTriangle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

lemma centeredEdgeVector_eq_triangle {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (s : ℝ) (e : CompleteEdge n) (he : e.val ∈ G) :
    centeredEdgeVector G s e = (triangleDegree G e.val : ℝ)/s-1 := by
  exact congrFun (centeredEdgeVector_restrict G hG s) (⟨e.val,he⟩ : G)

theorem prefix_edge_barrier_improvement : ∀ᶠ n : ℕ in atTop,
    ∀ ω : History (Graph n) (prefixTime n),
    ω ∈ (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n)).support →
    PrefixRootedUpper 8001 n ω → PrefixBalancedNoise 8001 n ω →
    PrefixTriangleNoise n ω → PrefixCodegreeNoiseGood n ω →
    ∀ j ≤ prefixTime n,
    historyAlive (fun i => densityEdgeSafe n (earlyDensity n i) (prefixEdgeRadius n)) (prefixTime n) j ω →
    trajectorySeminorm (fun t => activeLinf (graphActive (ω (historyIndex (prefixTime n) t)))) j
      (prefixCenteredEdge ω) ≤ prefixEdgeRadius n/2 := by
  obtain ⟨γ,hγ,hdec⟩ := prefixSpectralError_power_decay (by norm_num : (0 : ℝ) < 1/80000)
  obtain ⟨K,hK0,hbudget⟩ := prefix_edge_stability_budget hγ
  filter_upwards [hdec,hbudget,prefix_edge_residual_bounds,prefix_edge_forcing_bound,
    prefix_edge_coefficient_bounds,earlyTemplateScale_regular 1 2] with n hdec hbudget hR hM ha hreg
  intro ω hω hroot hbalanced htri hnoise j hj hsafe
  let active (i : ℕ) := graphActive (ω (historyIndex (prefixTime n) i))
  let a := prefixEdgeRate ω
  let R := prefixEdgeResidual ω hω
  let M := prefixEdgeForcing ω
  let x := prefixCenteredEdge ω
  let S := ∑ i ∈ Finset.range j, a i
  have hcb := ha ω hω htri j hj hsafe
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun i hi => (hcb.1 i (Finset.mem_range.mp hi)).1)
  have hS1 : S ≤ 4*Real.log n := hcb.2
  have hnest : ∀ i < j, active (i+1) ⊆ active i := by
    intro i hi
    apply graphActive_nested
    exact history_graph_nested ω hω (Nat.le_succ i) (by omega)
  have hinit : ∀ e ∈ active 0, x 0 e = M 0 e := by
    intro e _
    rw [show M 0 = x 0 from prefixEdgeForcing_zero ω]
  have hstep : ∀ i < j, ∀ e ∈ active (i+1), x (i+1) e = x i e-
      a i*(movingStarLift (fun e : CompleteEdge n => e.val)
        (movingStarMean (fun e : CompleteEdge n => e.val) (active i) (x i)) e+R i (x i) e)+
      (M (i+1) e-M i e) := by
    intro i hi e he
    exact prefix_centered_edge_recurrence ω hω (by omega) (hreg.1 i (by omega)).ne' e he
  have hRinf : ∀ i < j, ∀ z, activeLinf (active i) (R i z) ≤ 6*activeLinf (active i) z := by
    intro i hi z
    exact (hR ω hω hroot hbalanced j hj hsafe i hi z).1
  have hR2 : ∀ i < j, ∀ z, activeL2 (active i) (R i z) ≤ (n : ℝ)^(-γ)*activeL2 (active i) z := by
    intro i hi z
    exact (hR ω hω hroot hbalanced j hj hsafe i hi z).2.trans
      (mul_le_mul_of_nonneg_right hdec (apply_nonneg _ _))
  have hk : ((1+2*S)*S*(n : ℝ)^(-γ))^K*(Fintype.card (CompleteEdge n) : ℝ) ≤ 1/2 := by
    have hc : (Fintype.card (CompleteEdge n) : ℝ) ≤ (n : ℝ)^2 := by exact_mod_cast graphActive_card_le (n := n)
    exact (mul_le_mul_of_nonneg_left hc (by positivity)).trans (hbudget S hS0 hS1).1
  have hm := movingStar_mixed_stability (fun e : CompleteEdge n => e.val)
    (fun e => mem_completeGraph.mp e.property) active a R M x j K hnest
    (fun i hi => ⟨(hcb.1 i hi).1,(hcb.1 i hi).2.1⟩) hinit hstep
    (by norm_num : (0 : ℝ) ≤ 6) (Real.rpow_nonneg (Nat.cast_nonneg n) (-γ)) hRinf hR2 hk
  apply hm.trans
  apply le_trans _ (hbudget S hS0 hS1).2
  apply mul_le_mul_of_nonneg_left (hM ω hω htri hnoise j hj hsafe)
  have ha0 : ∀ i ∈ Finset.range j, 0 ≤ a i := fun i hi => (hcb.1 i (Finset.mem_range.mp hi)).1
  positivity

lemma history_mass_of_alive {n : ℕ} (hn : 0 < n)
    (hp : 1/(n : ℝ) ≤ prefixDensity n) (hη : prefixEdgeRadius n ≤ 1/2)
    (ω : History (Graph n) (prefixTime n))
    (hω : ω ∈ (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n)).support)
    (j : ℕ) (hj : j ≤ prefixTime n)
    (hsafe : historyAlive (fun i => densityEdgeSafe n (earlyDensity n i) (prefixEdgeRadius n)) (prefixTime n) j ω) :
    ((ω (historyIndex (prefixTime n) j)).card : ℝ) = (n : ℝ)^2*earlyDensity n j/2 := by
  obtain ⟨hinit,hpath⟩ := historyLaw_path_support (PMF.pure (completeGraph n)) (fun _ => step)
    (prefixTime n) (prefixTime n) le_rfl ω hω
  cases j with
  | zero =>
    have hi : ω (historyIndex (prefixTime n) 0) = completeGraph n := by simpa using hinit
    rw [hi]
    exact completeGraph_early_mass hn
  | succ i =>
    have hs := hsafe i (Nat.lt_succ_self i)
    have hactive := densityEdgeSafe_triangle_positive hn (early_density_positive hn hp (by omega)) hη hs
    have hc := step_card_of_active hactive (hpath i (by omega))
    have hcR : ((ω (historyIndex (prefixTime n) (i+1))).card : ℝ)+3 = (n : ℝ)^2*earlyDensity n i/2 := by
      rw [← hs.2.1]
      exact_mod_cast hc
    rw [earlyDensity_succ n i] at hcR
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have he : (n : ℝ)^2*(earlyDensity n (i+1)+6/(n : ℝ)^2)/2 =
        (n : ℝ)^2*earlyDensity n (i+1)/2+3 := by field_simp; ring
    rw [he] at hcR
    linarith only [hcR]

theorem prefix_present_edge_closure_oai : ∀ᶠ n : ℕ in atTop,
    ∀ ω : History (Graph n) (prefixTime n),
    ω ∈ (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n)).support →
    PrefixRootedUpper 8001 n ω → PrefixBalancedNoise 8001 n ω →
    PrefixTriangleNoise n ω → PrefixCodegreeNoiseGood n ω →
    ∀ j ≤ prefixTime n, densityEdgeSafe n (earlyDensity n j) (prefixEdgeRadius n)
      (ω (historyIndex (prefixTime n) j)) := by
  filter_upwards [prefix_edge_barrier_improvement,triangle_closure_budget,
    prefixDensity_eventually_inverse_lower,earlyTemplateScale_regular 1 2,
    eventually_ge_atTop (1 : ℕ)] with n hb hη hp hreg hn
  intro ω hω hroot hbalanced htri hnoise j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj
    have hs : historyAlive (fun i => densityEdgeSafe n (earlyDensity n i) (prefixEdgeRadius n)) (prefixTime n) j ω := by
      intro i hi
      exact ih i hi (by omega)
    have hbound := hb ω hω hroot hbalanced htri hnoise j hj hs
    have hG := complete_history_valid ω hω j hj
    refine ⟨hG,history_mass_of_alive (by omega) hp hη.2.1 ω hω j hj hs,?_⟩
    intro e he
    let E : CompleteEdge n := ⟨e,hG he⟩
    have hEa : E ∈ graphActive (ω (historyIndex (prefixTime n) j)) := (mem_graphActive _ _).mpr he
    have hx := (activeLinf_coordinate (graphActive (ω (historyIndex (prefixTime n) j)))
      (prefixCenteredEdge ω j) hEa).trans ((trajectorySeminorm_at
        (fun t => activeLinf (graphActive (ω (historyIndex (prefixTime n) t)))) j
        (prefixCenteredEdge ω) le_rfl).trans hbound)
    change |centeredEdgeVector _ _ E| ≤ _ at hx
    rw [centeredEdgeVector_eq_triangle _ hG _ E he] at hx
    have hpos := hreg.1 j hj
    have heq : (triangleDegree (ω (historyIndex (prefixTime n) j)) e : ℝ)/earlyTemplateScale 1 2 n j-1 =
        ((triangleDegree (ω (historyIndex (prefixTime n) j)) e : ℝ)-earlyTemplateScale 1 2 n j)/earlyTemplateScale 1 2 n j := by field_simp
    change |(triangleDegree (ω (historyIndex (prefixTime n) j)) e : ℝ)/earlyTemplateScale 1 2 n j-1| ≤ _ at hx
    rw [heq,abs_div,abs_of_pos hpos] at hx
    have hh := (div_le_iff₀ hpos).mp hx
    simpa only [earlyTemplateScale,pow_one] using hh.trans (mul_le_mul_of_nonneg_right (by linarith only [hη.1]) hpos.le)

end SharpTerminalLeave
end
end

end OAI
end

theorem solution : type_of% @OAI.SharpTerminalLeave.prefix_present_edge_closure_oai := @OAI.SharpTerminalLeave.prefix_present_edge_closure_oai
