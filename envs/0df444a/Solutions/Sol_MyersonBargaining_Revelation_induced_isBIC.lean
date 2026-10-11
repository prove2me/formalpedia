-- Prove2me | solution 1 for MyersonBargaining.Revelation.induced_isBIC
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-11T04:06:53.5456+00:00
-- url     : https://prove2.me/submissions/39269e6a-6b82-4e07-89a2-dd8e24192ad1

import Mathlib
import Definitions.Def_MyersonBargaining_NashSolution_Model
import Definitions.Def_MyersonBargaining_Revelation_Equilibrium
open MyersonBargaining.NashSolution MyersonBargaining.Revelation
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  {A : ι → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
  [∀ i, Nonempty (A i)] {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]

private theorem induced_choice {S : ι → Type} [∀ i, Fintype (S i)]
    (π : C → (∀ i, S i) → ℝ) (σ : ∀ i, S i → A i → ℝ)
    (hπ : IsChoiceMechanism π) (hσ : ∀ i, IsResponsePlan (σ i)) :
    IsChoiceMechanism (induced π σ) := by
  classical
  constructor
  · intro c α
    exact Finset.sum_nonneg (fun s _ => mul_nonneg (hπ.1 c s)
      (Finset.prod_nonneg (fun i _ => (hσ i).1 (s i) (α i))))
  · intro α
    unfold induced
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hπ.2, one_mul]
    rw [← Fintype.prod_sum (fun i s => σ i s (α i))]
    simp only [show ∀ i, ∑ s, σ i s (α i) = 1 from fun i => (hσ i).2 (α i), Finset.prod_const_one]

private theorem induced_payoff (G : Problem ι A C) {S : ι → Type} [∀ i, Fintype (S i)]
    (π : C → (∀ i, S i) → ℝ) (σ : ∀ i, S i → A i → ℝ) :
    V G (induced π σ) = W G π σ := by
  classical
  funext ⟨i,a⟩
  simp only [V, Z, W, induced]
  apply Finset.sum_congr rfl
  intro α _
  by_cases h : α i = a
  · have hu : Function.update α i a = α := by rw [← h, Function.update_eq_self]
    rw [hu]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro c _
    ring
  · simp [MyersonBargaining.NashSolution.cond, h]

private theorem induced_report (G : Problem ι A C) {S : ι → Type} [∀ i, Fintype (S i)]
    (π : C → (∀ i, S i) → ℝ) (σ : ∀ i, S i → A i → ℝ) (i : ι) (a b : A i) :
    Z G i (induced π σ) b a =
      W G π (Function.update σ i (fun s _ => σ i s b)) ⟨i,a⟩ := by
  classical
  simp only [Z, W, induced]
  apply Finset.sum_congr rfl
  intro α _
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  have hp : (∏ j, σ j (s j) (Function.update α i b j)) =
      ∏ j, Function.update σ i (fun s _ => σ i s b) j (s j) (α j) := by
    apply Finset.prod_congr rfl
    intro j _
    by_cases hj : j = i
    · subst j; simp
    · simp [hj]
  rw [hp]
  apply Finset.sum_congr rfl
  intro c _
  ring

private theorem induced_bic (G : Problem ι A C) {S : ι → Type} [∀ i, Fintype (S i)]
    (π : C → (∀ i, S i) → ℝ) (σ : ∀ i, S i → A i → ℝ)
    (hσ : ∀ i, IsResponsePlan (σ i)) (heq : IsResponsePlanEq G π σ) :
    IsBIC G (induced π σ) := by
  intro i a b
  have ht : IsResponsePlan (fun s (_ : A i) => σ i s b) :=
    ⟨fun s _ => (hσ i).1 s b, fun _ => (hσ i).2 b⟩
  have h := heq i a (fun s _ => σ i s b) ht
  rw [← induced_report] at h
  have hv := congrFun (induced_payoff G π σ) ⟨i,a⟩
  exact h.trans_eq hv.symm

private theorem honest_product (s α : ∀ i, A i) :
    (∏ i, honest i (s i) (α i)) = if s = α then (1 : ℝ) else 0 := by
  classical
  simp only [honest, Fintype.prod_boole, funext_iff]

private theorem honest_induced (π : C → (∀ i, A i) → ℝ) :
    induced π (honest (A := A)) = π := by
  classical
  funext c α
  simp [induced, honest_product]

private theorem mix_product (i : ι) (τ : A i → A i → ℝ) (s α : ∀ i, A i) :
    (∏ j, Function.update (honest (A := A)) i τ j (s j) (α j)) =
      ∑ b, τ b (α i) * ∏ j, honest j (s j) (Function.update α i b j) := by
  classical
  let p : ℝ := ∏ j ∈ Finset.univ.erase i, honest j (s j) (α j)
  have hl : (∏ j, Function.update (honest (A := A)) i τ j (s j) (α j)) =
      τ (s i) (α i) * p := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    simp only [Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    simp [(Finset.mem_erase.mp hj).1]
  have hr (b : A i) : (∏ j, honest j (s j) (Function.update α i b j)) =
      (if s i = b then (1 : ℝ) else 0) * p := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    simp only [Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    simp [(Finset.mem_erase.mp hj).1]
  rw [hl]
  simp_rw [hr]
  simp [mul_assoc, ← Finset.sum_mul, eq_comm]

private theorem mix_induced (π : C → (∀ i, A i) → ℝ)
    (i : ι) (τ : A i → A i → ℝ) (c : C) (α : ∀ i, A i) :
    induced π (Function.update (honest (A := A)) i τ) c α =
      ∑ b, τ b (α i) * π c (Function.update α i b) := by
  classical
  unfold induced
  simp_rw [mix_product, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  simp_rw [honest_product]
  simp [mul_assoc, mul_left_comm, mul_comm]


private theorem mix_payoff (G : Problem ι A C) (π : C → (∀ i, A i) → ℝ)
    (i : ι) (a : A i) (τ : A i → A i → ℝ) :
    W G π (Function.update (honest (A := A)) i τ) ⟨i,a⟩ =
      ∑ b, τ b a * Z G i π b a := by
  classical
  rw [← induced_payoff]
  simp only [V, Z]
  simp_rw [mix_induced, Function.update_self, Function.update_idem,
    Finset.mul_sum, Finset.sum_mul]
  conv_lhs =>
    arg 2
    ext α
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro c _
  ring

private theorem honest_eq (G : Problem ι A C) (π : C → (∀ i, A i) → ℝ)
    (hbic : IsBIC G π) :
    (∀ i, IsResponsePlan (honest (A := A) i)) ∧
      IsResponsePlanEq G π (honest (A := A)) ∧ W G π (honest (A := A)) = V G π := by
  classical
  have hw : W G π (honest (A := A)) = V G π := by
    rw [← induced_payoff, honest_induced]
  refine ⟨?_, ?_, hw⟩
  · intro i
    constructor
    · intro b a; dsimp [honest]; split_ifs <;> norm_num
    · intro a; simp [honest]
  · intro i a τ hτ
    rw [mix_payoff, hw]
    calc
      (∑ b, τ b a * Z G i π b a) ≤ ∑ b, τ b a * Z G i π a a := by
        exact Finset.sum_le_sum (fun b _ => mul_le_mul_of_nonneg_left (hbic i a b) (hτ.1 b a))
      _ = V G π ⟨i,a⟩ := by rw [← Finset.sum_mul, hτ.2, one_mul]; rfl

private theorem feasible_eq (G : Problem ι A C) : FStarStar G = FStar G := by
  classical
  ext x
  constructor
  · rintro ⟨S, hS, hnS, π, σ, hπ, hσ, heq, rfl⟩
    exact ⟨induced π σ, induced_choice π σ hπ hσ, induced_bic G π σ hσ heq,
      induced_payoff G π σ⟩
  · rintro ⟨π, hπ, hbic, rfl⟩
    obtain ⟨hh, he, hw⟩ := honest_eq G π hbic
    exact ⟨A, inferInstance, inferInstance, π, honest, hπ, hh, he, hw⟩


theorem solution (G : MyersonBargaining.NashSolution.Problem ι A C) {S : ι → Type} [∀ i, Fintype (S i)]
    [∀ i, Nonempty (S i)] (π : C → (∀ i, S i) → ℝ) (σ : ∀ i, S i → A i → ℝ)
    (hπ : MyersonBargaining.NashSolution.IsChoiceMechanism π) (hσ : ∀ i, IsResponsePlan (σ i))
    (heq : IsResponsePlanEq G π σ) :
    MyersonBargaining.NashSolution.IsBIC G (induced π σ) := by exact induced_bic G π σ hσ heq

