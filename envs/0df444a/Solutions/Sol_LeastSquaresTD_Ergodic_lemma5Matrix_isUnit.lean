-- Prove2me | solution 1 for LeastSquaresTD.Ergodic.lemma5Matrix_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T10:51:05.197352+00:00
-- url     : https://prove2.me/submissions/0f63b6ce-5faa-4aba-9da6-ec6eb7ded1b9

import Mathlib
import Definitions.Def_LeastSquaresTD_Ergodic_Chain
import Definitions.Def_LeastSquaresTD_Ergodic_LSTD

set_option autoImplicit false

open MeasureTheory Matrix Filter Topology

namespace P2M_2771d2c7

open LeastSquaresTD.Ergodic

theorem pow_nonneg' {X : Type*} [Fintype X] [DecidableEq X] (C : Chain X) :
    ∀ n : ℕ, ∀ x y, 0 ≤ (C.P ^ n) x y := by
  intro n
  induction n with
  | zero =>
    intro x y
    rw [pow_zero, Matrix.one_apply]
    split_ifs <;> norm_num
  | succ n ih =>
    intro x y
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun z _ => mul_nonneg (ih x z) (C.nonneg z y)

theorem vecMul_pow {X : Type*} [Fintype X] [DecidableEq X] (C : Chain X) (π : X → ℝ)
    (h : Matrix.vecMul π C.P = π) : ∀ n : ℕ, Matrix.vecMul π (C.P ^ n) = π := by
  intro n
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, h]

theorem pi_pos {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (C : Chain X) (hC : C.IsErgodic) (π : X → ℝ) (hπ : C.IsStationary π) :
    ∀ x, 0 < π x := by
  obtain ⟨h0, h1, h2⟩ := hπ
  obtain ⟨x0, hx0⟩ : ∃ x0, 0 < π x0 := by
    by_contra hne
    push Not at hne
    have : ∑ x, π x ≤ 0 := Finset.sum_nonpos fun x _ => hne x
    linarith
  intro y
  obtain ⟨n, hn⟩ := hC x0 y
  have key := congrFun (vecMul_pow C π h2 n) y
  rw [Matrix.vecMul, dotProduct] at key
  have hge : π x0 * (C.P ^ n) x0 y ≤ ∑ x, π x * (C.P ^ n) x y :=
    Finset.single_le_sum (f := fun x => π x * (C.P ^ n) x y)
      (fun x _ => mul_nonneg (h0 x) (pow_nonneg' C n x y)) (Finset.mem_univ x0)
  have : 0 < π x0 * (C.P ^ n) x0 y := mul_pos hx0 hn
  linarith [key]

theorem IgP_ker {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (C : Chain X) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (z : X → ℝ)
    (hz : (1 - γ • C.P) *ᵥ z = 0) : z = 0 := by
  have hz' : ∀ x, z x = γ * ∑ y, C.P x y * z y := by
    intro x
    have := congrFun hz x
    simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Pi.zero_apply, sub_mul, Finset.sum_sub_distrib, Matrix.one_apply, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_assoc, ← Finset.mul_sum] at this
    linarith
  obtain ⟨x0, hx0⟩ := Finite.exists_max (fun x => |z x|)
  have hb : |∑ y, C.P x0 y * z y| ≤ |z x0| := by
    calc |∑ y, C.P x0 y * z y| ≤ ∑ y, |C.P x0 y * z y| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ y, C.P x0 y * |z y| := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [abs_mul, abs_of_nonneg (C.nonneg x0 y)]
      _ ≤ ∑ y, C.P x0 y * |z x0| :=
          Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hx0 y) (C.nonneg x0 y)
      _ = |z x0| := by rw [← Finset.sum_mul, C.row_sum x0, one_mul]
  have e : |z x0| = γ * |∑ y, C.P x0 y * z y| := by
    conv_lhs => rw [hz' x0]
    rw [abs_mul, abs_of_pos hγ0]
  have hle : |z x0| ≤ γ * |z x0| := by
    exact e.trans_le (mul_le_mul_of_nonneg_left hb hγ0.le)
  have h0 : |z x0| = 0 := by
    have := abs_nonneg (z x0)
    nlinarith
  funext y
  have := hx0 y
  have := abs_nonneg (z y)
  have : |z y| = 0 := by linarith
  simpa using this

end P2M_2771d2c7

open LeastSquaresTD.Ergodic in
theorem solution {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (C : Chain X) (hC : C.IsErgodic) (π : X → ℝ) (hπ : C.IsStationary π)
    {m : ℕ} (φ : X → Fin m → ℝ) (hφ : LinearIndependent ℝ φ) (hm : m = Fintype.card X)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    (∀ x, 0 < π x) ∧ IsUnit (lemma5Matrix C φ π γ) := by
  have hpos := P2M_2771d2c7.pi_pos C hC π hπ
  refine ⟨hpos, ?_⟩
  set Φ := featureMatrix φ with hΦdef
  -- Φᵀ has trivial kernel
  have hΦT : ∀ w : X → ℝ, Φᵀ *ᵥ w = 0 → w = 0 := by
    intro w hw
    have hsum : ∑ x, w x • φ x = 0 := by
      funext i
      have := congrFun hw i
      simpa [Φ, featureMatrix, Matrix.mulVec, dotProduct, mul_comm] using this
    funext x
    exact (Fintype.linearIndependent_iff.mp hφ) w hsum x
  -- Φ has trivial kernel
  have hspan : Submodule.span ℝ (Set.range φ) = ⊤ :=
    hφ.span_eq_top_of_card_eq_finrank (by simp [hm])
  have hΦ : ∀ v : Fin m → ℝ, Φ *ᵥ v = 0 → v = 0 := by
    intro v hv
    let f : (Fin m → ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun w => ∑ i, v i * w i
        map_add' := by intro a b; simp [mul_add, Finset.sum_add_distrib]
        map_smul' := by
          intro c a
          simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring }
    have hf : ∀ w ∈ Submodule.span ℝ (Set.range φ), f w = 0 := by
      intro w hw
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
      · rintro _ ⟨x, rfl⟩
        have := congrFun hv x
        simp only [f, LinearMap.coe_mk, AddHom.coe_mk]
        simpa [Φ, featureMatrix, Matrix.mulVec, dotProduct, mul_comm] using this
      · simp
      · intro a b _ _ ha hb; rw [map_add, ha, hb, add_zero]
      · intro c a _ ha; rw [map_smul, ha, smul_zero]
    funext j
    have := hf (Pi.single j 1) (by rw [hspan]; trivial)
    simpa [f, Pi.single_apply] using this
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro a b hab
  have hker : ∀ v, lemma5Matrix C φ π γ *ᵥ v = 0 → v = 0 := by
    intro v hv
    simp only [lemma5Matrix, ← Matrix.mulVec_mulVec] at hv
    have h1 := hΦT _ hv
    have h2 : (1 - γ • C.P) *ᵥ (Φ *ᵥ v) = 0 := by
      funext x
      have := congrFun h1 x
      rw [Matrix.mulVec_diagonal] at this
      exact (mul_eq_zero.mp this).resolve_left (hpos x).ne'
    exact hΦ v (P2M_2771d2c7.IgP_ker C γ hγ0 hγ1 _ h2)
  have := hker (a - b) (by rw [Matrix.mulVec_sub, hab, sub_self])
  exact sub_eq_zero.mp this
