-- Prove2me | solution 1 for NumStochOpt.Stepsize.thm2_step1_stepsizes_not_summable
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:15:16.51161+00:00
-- url     : https://prove2.me/submissions/938d99ca-833b-4bc1-9995-568148aeb825

import Mathlib
import Definitions.Def_NumStochOpt_Stepsize_SQGBasics

set_option autoImplicit false
open Filter Topology
open scoped InnerProductSpace

section ProjLib
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma inner_le_of_min {S : Set E} (hcv : Convex ℝ S) {z p : E} (hp : p ∈ S)
    (hmin : ∀ w ∈ S, ‖z - p‖ ≤ ‖z - w‖) : ∀ w ∈ S, inner ℝ (z - p) (w - p) ≤ 0 := by
  have hb : BddBelow (Set.range fun w : S => ‖z - (w : E)‖) :=
    ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
  have : ‖z - p‖ = ⨅ w : S, ‖z - (w : E)‖ := by
    have : Nonempty S := ⟨⟨p, hp⟩⟩
    apply le_antisymm
    · exact le_ciInf (fun w => hmin w w.2)
    · exact ciInf_le hb ⟨p, hp⟩
  exact (norm_eq_iInf_iff_real_inner_le_zero hcv hp).1 this

lemma min_of_inner_le {S : Set E} (hcv : Convex ℝ S) {z p : E} (hp : p ∈ S)
    (h : ∀ w ∈ S, inner ℝ (z - p) (w - p) ≤ 0) : ∀ w ∈ S, ‖z - p‖ ≤ ‖z - w‖ := by
  have hb : BddBelow (Set.range fun w : S => ‖z - (w : E)‖) :=
    ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
  have := (norm_eq_iInf_iff_real_inner_le_zero hcv hp).2 h
  intro w hw
  rw [this]
  exact ciInf_le hb ⟨w, hw⟩

lemma proj_nonexp {S : Set E} (hcv : Convex ℝ S) {z z' y y' : E} (hy : y ∈ S) (hy' : y' ∈ S)
    (h1 : ∀ w ∈ S, ‖z - y‖ ≤ ‖z - w‖) (h2 : ∀ w ∈ S, ‖z' - y'‖ ≤ ‖z' - w‖) :
    ‖y - y'‖ ≤ ‖z - z'‖ := by
  have a1 := inner_le_of_min hcv hy h1 y' hy'
  have a2 := inner_le_of_min hcv hy' h2 y hy
  have key : ‖y - y'‖ ^ 2 ≤ inner ℝ (z - z') (y - y') := by
    have e1 : inner ℝ (z - y) (y' - y) = - inner ℝ (z - y) (y - y') := by
      rw [← inner_neg_right]; congr 1; abel
    have e2 : inner ℝ (z' - y') (y - y') = inner ℝ (z' - y') (y - y') := rfl
    have e3 : inner ℝ (z - z') (y - y') = inner ℝ (z - y) (y - y') - inner ℝ (z' - y') (y - y')
        + inner ℝ (y - y') (y - y') := by
      rw [← inner_sub_left, ← inner_add_left]; congr 1; abel
    rw [e3, real_inner_self_eq_norm_sq]
    linarith
  have key2 : inner ℝ (z - z') (y - y') ≤ ‖z - z'‖ * ‖y - y'‖ := real_inner_le_norm _ _
  by_cases h0 : ‖y - y'‖ = 0
  · rw [h0]; exact norm_nonneg _
  · have hpos : 0 < ‖y - y'‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith
end ProjLib

lemma step_bound {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (x ξ : ℕ → EuclideanSpace ℝ (Fin n)) (ρ : ℕ → ℝ) (C₂ : ℝ)
    (hX_ne : X.Nonempty) (hX_closed : IsClosed X) (hX_conv : Convex ℝ X)
    (hx0 : x 0 ∈ X)
    (hrec : ∀ s, x (s + 1) = NumStochOpt.QuasiFejer.projX X (x s - ρ s • ξ s))
    (hρ : ∀ s, 0 ≤ ρ s) (hξ : ∀ s, ‖ξ s‖ ≤ C₂) :
    ∀ s, ‖x (s + 1) - x s‖ ≤ ‖ρ s • ξ s‖ ∧ ‖ρ s • ξ s‖ ≤ ρ s * C₂ := by
  have hproj : ∀ y, NumStochOpt.QuasiFejer.projX X y ∈ X ∧
      ∀ z ∈ X, ‖y - NumStochOpt.QuasiFejer.projX X y‖ ≤ ‖y - z‖ := by
    intro y
    obtain ⟨v, hv, hvmin⟩ :=
      exists_norm_eq_iInf_of_complete_convex hX_ne hX_closed.isComplete hX_conv y
    have hb : BddBelow (Set.range fun w : X => ‖y - (w : EuclideanSpace ℝ (Fin n))‖) :=
      ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
    have hex : ∃ x ∈ X, ∀ z ∈ X, ‖y - x‖ ^ 2 ≤ ‖y - z‖ ^ 2 := by
      refine ⟨v, hv, fun z hz => ?_⟩
      have : ‖y - v‖ ≤ ‖y - z‖ := by rw [hvmin]; exact ciInf_le hb ⟨z, hz⟩
      exact pow_le_pow_left₀ (norm_nonneg _) this 2
    unfold NumStochOpt.QuasiFejer.projX
    rw [dif_pos hex]
    obtain ⟨h1, h2⟩ := hex.choose_spec
    refine ⟨h1, fun z hz => ?_⟩
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (h2 z hz)
  intro s
  have hxs : ∀ s, x s ∈ X := by
    intro s
    induction s with
    | zero => exact hx0
    | succ k _ => rw [hrec k]; exact (hproj _).1
  have h1 : ‖x (s + 1) - x s‖ ≤ ‖(x s - ρ s • ξ s) - x s‖ := by
    rw [hrec s]
    apply proj_nonexp hX_conv (hproj _).1 (hxs s) (hproj _).2
    intro w _
    simp
  have h2 : ‖(x s - ρ s • ξ s) - x s‖ = ‖ρ s • ξ s‖ := by
    rw [sub_sub_cancel_left, norm_neg]
  refine ⟨h2 ▸ h1, ?_⟩
  rw [norm_smul, Real.norm_of_nonneg (hρ s)]
  exact mul_le_mul_of_nonneg_left (hξ s) (hρ s)


lemma rho_pos {n : ℕ} (x ξ : ℕ → EuclideanSpace ℝ (Fin n)) (ρ : ℕ → ℝ) (a δ : ℝ)
    (ha : 1 < a) (hρ0 : 0 < ρ 0)
    (hrule : ∀ s, ρ (s + 1) = ρ s * a ^ (inner ℝ (ξ (s + 1)) (x s - x (s + 1)) - δ * ρ s)) :
    ∀ s, 0 < ρ s := by
  intro s
  induction s with
  | zero => exact hρ0
  | succ k ih =>
    rw [hrule k]
    exact mul_pos ih (Real.rpow_pos_of_pos (by linarith) _)

lemma exponent_bound {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (x ξ : ℕ → EuclideanSpace ℝ (Fin n)) (ρ : ℕ → ℝ) (δ C₂ : ℝ)
    (hX_ne : X.Nonempty) (hX_closed : IsClosed X) (hX_conv : Convex ℝ X)
    (hx0 : x 0 ∈ X)
    (hrec : ∀ s, x (s + 1) = NumStochOpt.QuasiFejer.projX X (x s - ρ s • ξ s))
    (hρ : ∀ s, 0 ≤ ρ s) (hξ : ∀ s, ‖ξ s‖ ≤ C₂) (hδ : 0 < δ) :
    ∀ s, |inner ℝ (ξ (s + 1)) (x s - x (s + 1)) - δ * ρ s| ≤ (C₂ ^ 2 + δ) * ρ s := by
  intro s
  have h1 := (step_bound X x ξ ρ C₂ hX_ne hX_closed hX_conv hx0 hrec hρ hξ s)
  have hC : 0 ≤ C₂ := le_trans (norm_nonneg _) (hξ 0)
  have h2 : |inner ℝ (ξ (s + 1)) (x s - x (s + 1))| ≤ C₂ * (ρ s * C₂) := by
    calc |inner ℝ (ξ (s + 1)) (x s - x (s + 1))| ≤ ‖ξ (s + 1)‖ * ‖x s - x (s + 1)‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ C₂ * (ρ s * C₂) := by
          rw [norm_sub_rev]
          exact mul_le_mul (hξ _) (h1.1.trans h1.2) (norm_nonneg _) hC
  have h3 : |δ * ρ s| = δ * ρ s := abs_of_nonneg (mul_nonneg hδ.le (hρ s))
  calc |inner ℝ (ξ (s + 1)) (x s - x (s + 1)) - δ * ρ s|
      ≤ |inner ℝ (ξ (s + 1)) (x s - x (s + 1))| + |δ * ρ s| := abs_sub _ _
    _ ≤ C₂ * (ρ s * C₂) + δ * ρ s := by rw [h3]; linarith
    _ = (C₂ ^ 2 + δ) * ρ s := by ring


theorem solution {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (x ξ : ℕ → EuclideanSpace ℝ (Fin n)) (ρ : ℕ → ℝ) (a δ C₂ : ℝ)
    (hX_ne : X.Nonempty) (hX_closed : IsClosed X) (hX_conv : Convex ℝ X)
    (ha : 1 < a) (hδ : 0 < δ) (hρ0 : 0 < ρ 0)
    (hx0 : x 0 ∈ X)
    (hrec : ∀ s, x (s + 1) = NumStochOpt.QuasiFejer.projX X (x s - ρ s • ξ s))
    (hrule : ∀ s, ρ (s + 1) = ρ s * a ^ (⟪ξ (s + 1), x s - x (s + 1)⟫_ℝ - δ * ρ s))
    (hξ : ∀ s, ‖ξ s‖ ≤ C₂) :
    Tendsto (fun N => ∑ s ∈ Finset.range N, ρ s) atTop atTop := by
  have hpos := rho_pos x ξ ρ a δ ha hρ0 hrule
  have hbd := exponent_bound X x ξ ρ δ C₂ hX_ne hX_closed hX_conv hx0 hrec (fun s => (hpos s).le) hξ hδ
  rw [← not_summable_iff_tendsto_nat_atTop_of_nonneg (fun s => (hpos s).le)]
  intro hsum
  have hl : 0 < Real.log a := Real.log_pos ha
  set K := (C₂ ^ 2 + δ) * Real.log a with hKdef
  have hK : 0 ≤ K := by positivity
  set S := ∑' s, ρ s with hSdef
  have hstep : ∀ s, ρ s * Real.exp (-(K * ρ s)) ≤ ρ (s + 1) := by
    intro s
    rw [hrule s]
    apply mul_le_mul_of_nonneg_left _ (hpos s).le
    rw [Real.rpow_def_of_pos (by linarith)]
    apply Real.exp_le_exp.2
    have h1 := (abs_le.1 (hbd s)).1
    rw [hKdef]
    nlinarith
  have hind : ∀ N, ρ 0 * Real.exp (-(K * ∑ s ∈ Finset.range N, ρ s)) ≤ ρ N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      calc ρ 0 * Real.exp (-(K * ∑ s ∈ Finset.range (N + 1), ρ s))
          = (ρ 0 * Real.exp (-(K * ∑ s ∈ Finset.range N, ρ s))) * Real.exp (-(K * ρ N)) := by
            rw [Finset.sum_range_succ, mul_add, neg_add, Real.exp_add]; ring
        _ ≤ ρ N * Real.exp (-(K * ρ N)) :=
            mul_le_mul_of_nonneg_right ih (Real.exp_pos _).le
        _ ≤ ρ (N + 1) := hstep N
  have hS : ∀ N, ∑ s ∈ Finset.range N, ρ s ≤ S := fun N =>
    hsum.sum_le_tsum (Finset.range N) (fun s _ => (hpos s).le)
  have hlb : ∀ N, ρ 0 * Real.exp (-(K * S)) ≤ ρ N := by
    intro N
    refine le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (hpos 0).le) (hind N)
    have := mul_le_mul_of_nonneg_left (hS N) hK
    linarith
  have hc : 0 < ρ 0 * Real.exp (-(K * S)) := mul_pos (hpos 0) (Real.exp_pos _)
  obtain ⟨N, hN⟩ := (hsum.tendsto_atTop_zero.eventually (gt_mem_nhds hc)).exists
  linarith [hlb N]
