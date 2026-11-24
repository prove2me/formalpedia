-- Prove2me | solution 1 for GlobalTheory.theta_term_smul_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:36:57.224019+00:00
-- url     : https://prove2.me/submissions/4823f164-426c-4446-a0f3-f4d784e84091

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ThetaSeriesTermSmulAddDecomposition
import Theorems.Thm_GlobalTheory_Ex_NumD_Gt_pow_s
import Theorems.Thm_P2M_GlobalTheory_Ex_NumD___add_84e84f39bbbc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (O : Type) [CommRing O] (N : GlobalTheory.Ex.NumD O) (S : Subring O) (m : ℕ) (h : N.Gt)
    (y : N.X) (hy : h ^ m = N.io y)
    (hθ : ∀ x ∈ Subgroup.closure (Set.range N.c ∪ {h.b}), ∀ x' ∈ Subgroup.closure (Set.range N.c ∪ {h.b}),
      ∀ x'' ∈ Subgroup.closure (Set.range N.c ∪ {h.b}),
        (N.θ x x' x'' : O) ∈ S ∧ (((N.θ x x' x'')⁻¹ : Oˣ) : O) ∈ S)
    (hσ : ∀ x ∈ Subgroup.closure (Set.range N.c ∪ {h.b}), (N.σ x : O) ∈ S ∧ (((N.σ x)⁻¹ : Oˣ) : O) ∈ S)
    (a b : N.X) : ∃ w : Oˣ, (w : O) ∈ S ∧
      N.ψ (m • a + b) * h.s (m • a + b) = w * N.ψ a ^ (m ^ 2) * N.τ a (m • b + y) * (N.ψ b * h.s b) := by
  set H := Subgroup.closure (Set.range N.c ∪ {h.b}) with hH
  set T := S.toSubmonoid.units with hT
  set π : Oˣ →* Oˣ ⧸ T := QuotientGroup.mk' T with hπ
  have Hc : ∀ a, N.c a ∈ H := fun a => Subgroup.subset_closure (Or.inl ⟨a, rfl⟩)
  have Hb : h.b ∈ H := Subgroup.subset_closure (Or.inr rfl)
  have θ1 : ∀ x ∈ H, ∀ x' ∈ H, ∀ x'' ∈ H, π (N.θ x x' x'') = 1 := fun x hx x' hx' x'' hx'' =>
    (QuotientGroup.eq_one_iff _).2 ((Submonoid.mem_units_iff _ _).2 (hθ x hx x' hx' x'' hx''))
  have σ1 : ∀ a, π (N.σ (N.c a)) = 1 := fun a =>
    (QuotientGroup.eq_one_iff _).2 ((Submonoid.mem_units_iff _ _).2 (hσ _ (Hc a)))
  have Bl : ∀ a a' b, π (N.τ (a + a') b) = π (N.τ a b) * π (N.τ a' b) := by
    intro a a' b
    have := congrArg π (N.τ_add_left a a' b)
    rwa [map_mul, map_mul, θ1 _ (Hc a) _ (Hc a') _ (Hc b), mul_one] at this
  have Br : ∀ a b b', π (N.τ a (b + b')) = π (N.τ a b) * π (N.τ a b') := by
    intro a b b'
    have := congrArg π (N.τ_add_right a b b')
    rwa [map_mul, map_mul, θ1 _ (Hc b) _ (Hc b') _ (Hc a), mul_one] at this
  have fadd : ∀ a b, π (N.ψ (a + b)) = π (N.τ a b) * π (N.ψ a) * π (N.ψ b) := by
    intro a b
    rw [N.ψ_add, map_mul, map_mul]
  have fneg : ∀ a, π (N.ψ (-a)) = π (N.ψ a) := by
    intro a
    have := congrArg π (N.even a)
    rwa [map_mul, σ1, mul_one] at this
  have Bnegr : ∀ a b, π (N.τ a (-b)) = (π (N.τ a b))⁻¹ := by
    intro a b
    have := Br a b (-b)
    rw [add_neg_cancel, N.τ_zero_right, map_one] at this
    exact eq_inv_of_mul_eq_one_right this.symm
  have Bself : ∀ a, π (N.τ a a) = π (N.ψ a) ^ 2 := by
    intro a
    have := fadd a (-a)
    rw [add_neg_cancel, N.ψ_zero, map_one, fneg, Bnegr, mul_assoc, eq_comm, inv_mul_eq_one] at this
    rw [sq]
    exact this
  have Bsmul : ∀ (k : ℕ) a b, π (N.τ (k • a) b) = π (N.τ a b) ^ k := by
    intro k a b
    induction k with
    | zero => simp
    | succ k ih => rw [succ_nsmul, Bl, ih, pow_succ]
  have Bsmulr : ∀ (k : ℕ) a b, π (N.τ a (k • b)) = π (N.τ a b) ^ k := by
    intro k a b
    rw [N.τ_symm, Bsmul, N.τ_symm]
  have fsmul : ∀ (k : ℕ) a, π (N.ψ (k • a)) = π (N.ψ a) ^ (k ^ 2) := by
    intro k a
    induction k with
    | zero => simp
    | succ k ih =>
      rw [succ_nsmul, fadd, ih, Bsmul, Bself, ← pow_mul, ← pow_add, ← pow_succ]
      congr 1
      ring
  have Sadd : ∀ χ χ', π (h.s (χ + χ')) = π (h.s χ) * π (h.s χ') := by
    intro χ χ'
    have := congrArg π (h.mult χ χ')
    rwa [map_mul, map_mul, θ1 _ (Hc χ) _ (Hc χ') _ Hb, mul_one] at this
  have Ssmul : ∀ (k : ℕ) a, π (h.s (k • a)) = π (h.s a) ^ k := by
    intro k a
    induction k with
    | zero => simp
    | succ k ih => rw [succ_nsmul, Sadd, ih, pow_succ]
  have Spow : π (h.s a) ^ m = π (N.τ a y) := by
    have := congrArg π (h.pow_s m a)
    rw [map_mul, map_pow, hy, GlobalTheory.Ex.NumD.io_s, N.τ_symm] at this
    have hc : π (cubN N.θ m 1 h.b (N.c a)) = 1 := by
      unfold cubN
      rw [map_prod]
      exact Finset.prod_eq_one fun i _ => θ1 _ (by rw [one_mul]; exact pow_mem Hb i) _ Hb _ (Hc a)
    rw [hc, mul_one] at this
    exact this.symm
  refine ⟨N.ψ (m • a + b) * h.s (m • a + b) / (N.ψ a ^ (m ^ 2) * N.τ a (m • b + y) * (N.ψ b * h.s b)), ?_, ?_⟩
  · have e : π (N.ψ (m • a + b) * h.s (m • a + b) / (N.ψ a ^ (m ^ 2) * N.τ a (m • b + y) * (N.ψ b * h.s b))) = 1 := by
      rw [map_div, div_eq_one, map_mul, map_mul, map_mul, map_mul, map_pow, fadd, Sadd, fsmul, Bsmul, Br, Bsmulr,
        Ssmul, Spow]
      ac_rfl
    exact ((Submonoid.mem_units_iff _ _).1 ((QuotientGroup.eq_one_iff _).1 e)).1
  · exact (fun (L X Y Z : Oˣ) => show L = L / (X * Y * Z) * X * Y * Z by
      rw [mul_assoc (L / (X * Y * Z)) X Y, mul_assoc (L / (X * Y * Z)) (X * Y) Z, div_mul_cancel]) _ _ _ _
end GlobalTheory
