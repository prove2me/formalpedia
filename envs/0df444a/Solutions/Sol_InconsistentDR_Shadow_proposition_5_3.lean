-- Prove2me | solution 1 for InconsistentDR.Shadow.proposition_5_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T23:53:27.914489+00:00
-- url     : https://prove2.me/submissions/35716302-2730-4b94-a424-203de056f5c6

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_InconsistentDR_Shadow_Operators
import Theorems.Thm_InconsistentDR_Shadow_lemma_4_1

open scoped InnerProductSpace Topology Pointwise
open Filter ThreeOpSplitting.Convergence

namespace DR53Aux

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

lemma res_mem (A : X → Set X) (J : X → X) (hJ : IsResolvent 1 A J) (x : X) :
    x - J x ∈ A (J x) := by
  have := hJ x; rwa [inv_one, one_smul] at this

/-- `⟪J x - J y, J_{A⁻¹} x - J_{A⁻¹} y⟫ ≥ 0`. -/
lemma res_inner_nonneg (A : X → Set X) (hA : IsMonotoneOp A) (J : X → X)
    (hJ : IsResolvent 1 A J) (x y : X) :
    0 ≤ ⟪J x - J y, (x - J x) - (y - J y)⟫_ℝ :=
  hA _ _ _ _ (res_mem A J hJ x) (res_mem A J hJ y)

lemma res_unique (A : X → Set X) (hA : IsMonotoneOp A) (J : X → X) (hJ : IsResolvent 1 A J)
    {x y : X} (hy : x - y ∈ A y) : J x = y := by
  have := hA _ _ _ _ (res_mem A J hJ x) hy
  have e : (x - J x) - (x - y) = -(J x - y) := by abel
  rw [e, inner_neg_right, real_inner_self_eq_norm_sq] at this
  have h0 : ‖J x - y‖ = 0 := by nlinarith [norm_nonneg (J x - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp h0)

/-- The reflected resolvent is nonexpansive. -/
lemma refl_nonexp (A : X → Set X) (hA : IsMonotoneOp A) (J : X → X) (hJ : IsResolvent 1 A J)
    (x y : X) : ‖InconsistentDR.Shadow.refl J x - InconsistentDR.Shadow.refl J y‖ ≤ ‖x - y‖ := by
  have h := res_inner_nonneg A hA J hJ x y
  have e : InconsistentDR.Shadow.refl J x - InconsistentDR.Shadow.refl J y =
      (J x - J y) - ((x - J x) - (y - J y)) := by
    simp only [InconsistentDR.Shadow.refl]; module
  have e2 : x - y = (J x - J y) + ((x - J x) - (y - J y)) := by abel
  have h2 : ‖InconsistentDR.Shadow.refl J x - InconsistentDR.Shadow.refl J y‖ ^ 2 ≤
      ‖x - y‖ ^ 2 := by
    rw [e, e2, norm_sub_sq_real, norm_add_sq_real]
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

/-- The Douglas–Rachford operator is firmly nonexpansive. -/
lemma drT_fne (A B : X → Set X) (hA : IsMonotoneOp A) (hB : IsMonotoneOp B) (JA JB : X → X)
    (hJA : IsResolvent 1 A JA) (hJB : IsResolvent 1 B JB) (x y : X) :
    ‖InconsistentDR.Shadow.drT JA JB x - InconsistentDR.Shadow.drT JA JB y‖ ^ 2 +
      ‖(x - InconsistentDR.Shadow.drT JA JB x) - (y - InconsistentDR.Shadow.drT JA JB y)‖ ^ 2
      ≤ ‖x - y‖ ^ 2 := by
  open InconsistentDR.Shadow in
  have hN : ‖refl JB (refl JA x) - refl JB (refl JA y)‖ ≤ ‖x - y‖ :=
    (refl_nonexp B hB JB hJB _ _).trans (refl_nonexp A hA JA hJA x y)
  open InconsistentDR.Shadow in
  have e1 : drT JA JB x - drT JA JB y =
      (1 / 2 : ℝ) • ((x - y) + (refl JB (refl JA x) - refl JB (refl JA y))) := by
    simp only [InconsistentDR.Shadow.drT, InconsistentDR.Shadow.refl]; module
  open InconsistentDR.Shadow in
  have e2 : (x - drT JA JB x) - (y - drT JA JB y) =
      (1 / 2 : ℝ) • ((x - y) - (refl JB (refl JA x) - refl JB (refl JA y))) := by
    simp only [InconsistentDR.Shadow.drT, InconsistentDR.Shadow.refl]; module
  rw [e1, e2]
  have h2 := pow_le_pow_left₀ (norm_nonneg _) hN 2
  generalize x - y = a at h2 ⊢
  generalize InconsistentDR.Shadow.refl JB (InconsistentDR.Shadow.refl JA x) -
    InconsistentDR.Shadow.refl JB (InconsistentDR.Shadow.refl JA y) = b at h2 ⊢
  rw [norm_smul, norm_smul, mul_pow, mul_pow, norm_add_sq_real, norm_sub_sq_real]
  have : ‖(1 / 2 : ℝ)‖ ^ 2 = 1 / 4 := by norm_num
  rw [this]
  nlinarith

/-- `Fix(v + T)` is invariant under `T` ([13, Proposition 2.5]). -/
lemma fix_step (T : X → X)
    (hfne : ∀ x y, ‖T x - T y‖ ^ 2 + ‖(x - T x) - (y - T y)‖ ^ 2 ≤ ‖x - y‖ ^ 2)
    (v : X) (hv : ∀ w, ‖v‖ ≤ ‖w - T w‖) (q : X) (hq : v + T q = q) :
    v + T (q - v) = q - v := by
  have hTq : T q = q - v := eq_sub_of_add_eq' hq
  have h := hfne q (q - v)
  rw [hTq, sub_sub_cancel] at h
  set w := q - v - T (q - v) with hw
  have hvw := hv (q - v)
  rw [← hw] at hvw
  have h2 : ‖v‖ ^ 2 ≤ ‖w‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hvw 2
  have h3 : ‖v - w‖ = 0 := by nlinarith [norm_nonneg (v - w)]
  have h5 : q - v - T (q - v) = v := (sub_eq_zero.mp (norm_eq_zero.mp h3)).symm
  calc v + T (q - v) = v + (q - v - (q - v - T (q - v))) := by abel
    _ = q - v := by rw [h5]; abel


end DR53Aux

open InconsistentDR.Shadow in
theorem solution {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (A B : X → Set X) (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (JA JB : X → X) (hJA : IsResolvent 1 A JA) (hJB : IsResolvent 1 B JB)
    (v vD vR : X)
    (hv : IsMinNormPt (closure (Set.range fun x => x - drT JA JB x)) v)
    (hvD : IsMinNormPt (closure (setD A B)) vD) (hvR : IsMinNormPt (closure (setR A B)) vR)
    (h12 : Standing12 A B JA JB)
    (p : X) (hp : p ∈ FixSet (fun y => v + drT JA JB y)) (n : ℕ) :
    (drT JA JB)^[n] p = p - (n : ℝ) • v ∧
    JA ((drT JA JB)^[n] p) = JA p - (n : ℝ) • vR ∧
    resInv JA ((drT JA JB)^[n] p) = resInv JA p - (n : ℝ) • vD ∧
    JB (refl JA ((drT JA JB)^[n] p)) = JB (refl JA p) - (n : ℝ) • vR ∧
    resInv JB (refl JA ((drT JA JB)^[n] p)) = resInv JB (refl JA p) + (n : ℝ) • vD := by
  have h41 := (lemma_4_1 A B hA hB JA JB hJA hJB v vD vR hv hvD hvR h12).1
  set T := drT JA JB with hT
  have hfne := DR53Aux.drT_fne A B hA.1 hB.1 JA JB hJA hJB
  have hvmin : ∀ w, ‖v‖ ≤ ‖w - T w‖ := fun w => hv.2 _ (subset_closure ⟨w, rfl⟩)
  have hp' : v + T p = p := hp
  -- the orbit stays in `Fix(v + T)` and moves by `-v`
  have horb : ∀ k : ℕ, v + T (T^[k] p) = T^[k] p ∧ T^[k] p = p - (k : ℝ) • v := by
    intro k
    induction k with
    | zero => exact ⟨by simpa using hp', by simp⟩
    | succ k ih =>
      obtain ⟨h1, h2⟩ := ih
      have hTk : T (T^[k] p) = T^[k] p - v := eq_sub_of_add_eq' h1
      rw [Function.iterate_succ_apply', hTk]
      refine ⟨DR53Aux.fix_step T hfne v hvmin _ h1, ?_⟩
      rw [h2]; push_cast; module
  have hstep : ∀ k : ℕ, JA (T^[k + 1] p) = JA (T^[k] p) - vR ∧
      resInv JA (T^[k + 1] p) = resInv JA (T^[k] p) - vD := by
    intro k
    obtain ⟨-, h2, h3, -⟩ := h41 (T^[k] p) (horb k).1
    rw [Function.iterate_succ_apply']
    exact ⟨h2, h3⟩
  have hJ : ∀ k : ℕ, JA (T^[k] p) = JA p - (k : ℝ) • vR ∧
      resInv JA (T^[k] p) = resInv JA p - (k : ℝ) • vD := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      obtain ⟨s1, s2⟩ := hstep k
      rw [s1, s2, ih.1, ih.2]
      push_cast
      constructor <;> module
  -- on `Fix(v + T)`: `J_B R_A q = J_A q - v` and `J_{B⁻¹} R_A q = v - J_{A⁻¹} q`
  have hB1 : ∀ q, v + T q = q → JB (refl JA q) = JA q - v := by
    intro q hq
    have : q - T q = v := sub_eq_of_eq_add hq.symm
    simp only [hT, drT] at this
    rw [← this]; abel
  have hB2 : ∀ q, v + T q = q → resInv JB (refl JA q) = v - resInv JA q := by
    intro q hq
    simp only [resInv]
    rw [hB1 q hq]
    simp only [InconsistentDR.Shadow.refl]
    module
  obtain ⟨hfixn, hTn⟩ := horb n
  obtain ⟨hJn1, hJn2⟩ := hJ n
  refine ⟨hTn, hJn1, hJn2, ?_, ?_⟩
  · rw [hB1 _ hfixn, hB1 _ hp', hJn1]; abel
  · rw [hB2 _ hfixn, hB2 _ hp', hJn2]; abel
