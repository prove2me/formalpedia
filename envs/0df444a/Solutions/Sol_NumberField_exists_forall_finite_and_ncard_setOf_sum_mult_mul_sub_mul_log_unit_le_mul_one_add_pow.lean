-- Prove2me | solution 1 for NumberField.exists_forall_finite_and_ncard_setOf_sum_mult_mul_sub_mul_log_unit_le_mul_one_add_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/e5133c99-55bf-5007-a207-170aeec8c31d

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Theorems.Thm_ZLattice_exists_forall_ncard_add_mem_closedBall_le
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_exists_forall_finite_and_ncard_setOf_sum_mult_mul_sub_mul_log_unit_le_mul_one_add_pow

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm

noncomputable section

namespace DualLat

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem NumberField.InfinitePlace Module
open scoped Classical

variable (K : Type) [Field K] [NumberField K]

def pair (y ℓ : logSpace K) : ℝ := ∑ w, y w * ℓ w

theorem pair_add_left (y y' ℓ : logSpace K) : pair K (y + y') ℓ = pair K y ℓ + pair K y' ℓ := by
  simp only [pair, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem pair_neg_left (y ℓ : logSpace K) : pair K (-y) ℓ = -pair K y ℓ := by
  simp only [pair, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

theorem pair_sub_left (y y' ℓ : logSpace K) : pair K (y - y') ℓ = pair K y ℓ - pair K y' ℓ := by
  simp only [pair, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem pair_add_right (y ℓ ℓ' : logSpace K) : pair K y (ℓ + ℓ') = pair K y ℓ + pair K y ℓ' := by
  simp only [pair, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem pair_smul_right (y ℓ : logSpace K) (c : ℝ) : pair K y (c • ℓ) = c * pair K y ℓ := by
  simp only [pair, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun w _ => by ring

theorem abs_pair_le (y ℓ : logSpace K) : |pair K y ℓ| ≤ ‖y‖ * ∑ w, |ℓ w| := by
  unfold pair
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun w _ => ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (by simpa using norm_le_pi_norm y w) (abs_nonneg _)

theorem eq_zero_of_pair_self (y : logSpace K) (h : pair K y y = 0) : y = 0 := by
  unfold pair at h
  have h' : ∀ w ∈ (Finset.univ : Finset {w : InfinitePlace K // w ≠ w₀}), y w * y w = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun w _ => mul_self_nonneg (y w)).1 h
  funext w
  exact mul_self_eq_zero.1 (h' w (Finset.mem_univ w))

def B : Basis (Fin (rank K)) ℝ (logSpace K) := (basisUnitLattice K).ofZLatticeBasis ℝ (unitLattice K)

theorem B_eq (i : Fin (rank K)) : (B K i : logSpace K) = logEmbedding K (Additive.ofMul (fundSystem K i)) := by
  rw [B, Basis.ofZLatticeBasis_apply, ← logEmbedding_fundSystem]

theorem eq_zero_of_pair_B (y : logSpace K) (h : ∀ i, pair K y (B K i) = 0) : y = 0 := by
  apply eq_zero_of_pair_self
  have hrep := (B K).sum_repr y
  conv_lhs => arg 3; rw [← hrep]
  have : ∀ s : Finset (Fin (rank K)), pair K y (∑ i ∈ s, (B K).repr y i • B K i) = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [pair]
    | insert a s ha ih => rw [Finset.sum_insert ha, pair_add_right, pair_smul_right, h a, ih]; ring
  exact this _

def M : AddSubgroup (logSpace K) where
  carrier := {y | ∀ i : Fin (rank K), ∃ n : ℤ, pair K y (B K i) = 2 * Real.pi * n}
  add_mem' := by
    intro y y' hy hy' i
    obtain ⟨n, hn⟩ := hy i
    obtain ⟨n', hn'⟩ := hy' i
    exact ⟨n + n', by rw [pair_add_left, hn, hn']; push_cast; ring⟩
  zero_mem' := fun i => ⟨0, by simp [pair]⟩
  neg_mem' := by
    intro y hy i
    obtain ⟨n, hn⟩ := hy i
    exact ⟨-n, by rw [pair_neg_left, hn]; push_cast; ring⟩

theorem mem_M {y : logSpace K} : y ∈ M K ↔ ∀ i : Fin (rank K), ∃ n : ℤ, pair K y (B K i) = 2 * Real.pi * n := Iff.rfl

theorem discrete_M : DiscreteTopology (M K) := by
  set S : ℝ := 1 + ∑ i : Fin (rank K), ∑ w, |(B K i : logSpace K) w| with hS
  have hS1 : 1 ≤ S := by
    have : 0 ≤ ∑ i : Fin (rank K), ∑ w, |(B K i : logSpace K) w| :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  have hε : 0 < 2 * Real.pi / S := by positivity
  refine DiscreteTopology.of_forall_le_dist (α := ↥(M K)) hε ?_
  intro x y hxy
  by_contra hlt
  push Not at hlt
  apply hxy
  have hd : (x : logSpace K) - y ∈ M K := (M K).sub_mem x.2 y.2
  have hnorm : ‖(x : logSpace K) - y‖ < 2 * Real.pi / S := by rwa [← dist_eq_norm]
  have hzero : ∀ i, pair K ((x : logSpace K) - y) (B K i) = 0 := by
    intro i
    obtain ⟨n, hn⟩ := hd i
    have h1 : |pair K ((x : logSpace K) - y) (B K i)| ≤ ‖(x : logSpace K) - y‖ * ∑ w, |(B K i : logSpace K) w| :=
      abs_pair_le K _ _
    have h2 : ∑ w, |(B K i : logSpace K) w| ≤ S := by
      rw [hS]
      have := Finset.single_le_sum (f := fun i => ∑ w, |(B K i : logSpace K) w|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
      linarith
    have h3 : |(2 * Real.pi * n : ℝ)| < 2 * Real.pi := by
      rw [← hn]
      calc |pair K ((x : logSpace K) - y) (B K i)| ≤ ‖(x : logSpace K) - y‖ * ∑ w, |(B K i : logSpace K) w| := h1
        _ ≤ ‖(x : logSpace K) - y‖ * S := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
        _ < 2 * Real.pi / S * S := mul_lt_mul_of_pos_right hnorm (by linarith)
        _ = 2 * Real.pi := div_mul_cancel₀ _ (by linarith)
    have h4 : |(n : ℝ)| < 1 := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at h3
      nlinarith [Real.pi_pos, abs_nonneg (n : ℝ)]
    have h5 : n = 0 := by
      have : |n| < 1 := by exact_mod_cast h4
      exact Int.abs_lt_one_iff.mp this
    rw [hn, h5]; simp
  have := eq_zero_of_pair_B K _ hzero
  exact Subtype.ext (sub_eq_zero.1 this)

theorem pair_logEmbedding (y : logSpace K) (ε : (𝓞 K)ˣ) :
    pair K y (logEmbedding K (Additive.ofMul ε)) =
      ∑ w : {w : InfinitePlace K // w ≠ w₀}, y w * ((w.1.mult : ℝ) * Real.log (w.1 ((algebraMap (𝓞 K) K) ε))) := by
  unfold pair
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [logEmbedding_component]

end DualLat

open DualLat NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem NumberField.InfinitePlace Module in
theorem solution
    (K : Type) [Field K] [NumberField K] (w₀ : InfinitePlace K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : InfinitePlace K → ℝ) (R : ℝ), 0 ≤ R →
      {σ : InfinitePlace K → ℝ | σ w₀ = 0 ∧
        (∀ ε : (𝓞 K)ˣ, ∃ n : ℤ,
          ∑ v : InfinitePlace K, (v.mult : ℝ) * (σ v - a v) * Real.log (v (((ε : 𝓞 K)) : K)) = 2 * Real.pi * n) ∧
        ∑ v : InfinitePlace K, ∑ v' : InfinitePlace K, |σ v - σ v'| ≤ R}.Finite ∧
      (({σ : InfinitePlace K → ℝ | σ w₀ = 0 ∧
        (∀ ε : (𝓞 K)ˣ, ∃ n : ℤ,
          ∑ v : InfinitePlace K, (v.mult : ℝ) * (σ v - a v) * Real.log (v (((ε : 𝓞 K)) : K)) = 2 * Real.pi * n) ∧
        ∑ v : InfinitePlace K, ∑ v' : InfinitePlace K, |σ v - σ v'| ≤ R}.ncard : ℕ) : ℝ) ≤
        C * (1 + R) ^ (Fintype.card (InfinitePlace K) - 1) := by
  classical
  obtain ⟨C, hC0, hC⟩ := ZLattice.exists_forall_ncard_add_mem_closedBall_le (M K) (discrete_M K)
  have hrank : Module.finrank ℝ (logSpace K) = Fintype.card (InfinitePlace K) - 1 :=
    NumberField.Units.finrank_eq_rank K
  refine ⟨C, hC0, fun a R hR => ?_⟩
  set α : logSpace K := fun w => a w.1 - a dirichletUnitTheorem.w₀ with hα
  obtain ⟨hfin, hcount⟩ := hC α R hR

  set f : (InfinitePlace K → ℝ) → logSpace K := fun σ => (fun w => σ w.1 - σ dirichletUnitTheorem.w₀) - α with hf
  set S : Set (InfinitePlace K → ℝ) := {σ : InfinitePlace K → ℝ | σ w₀ = 0 ∧
        (∀ ε : (𝓞 K)ˣ, ∃ n : ℤ,
          ∑ v : InfinitePlace K, (v.mult : ℝ) * (σ v - a v) * Real.log (v (((ε : 𝓞 K)) : K)) = 2 * Real.pi * n) ∧
        ∑ v : InfinitePlace K, ∑ v' : InfinitePlace K, |σ v - σ v'| ≤ R} with hSdef
  have hmaps : Set.MapsTo f S {x : logSpace K | x ∈ M K ∧ ‖α + x‖ ≤ R} := by
    intro σ hσ
    obtain ⟨hσ0, hσP, hσR⟩ := hσ
    refine ⟨?_, ?_⟩
    · rw [mem_M]
      intro i
      obtain ⟨n, hn⟩ := hσP (fundSystem K i)
      refine ⟨n, ?_⟩
      rw [B_eq, pair_logEmbedding]

      set g : InfinitePlace K → ℝ := fun v => (σ v - σ dirichletUnitTheorem.w₀ - (a v - a dirichletUnitTheorem.w₀)) *
            ((v.mult : ℝ) * Real.log (v ((algebraMap (𝓞 K) K) (fundSystem K i)))) with hg
      have hsum : ∑ w : {w : InfinitePlace K // w ≠ dirichletUnitTheorem.w₀},
          f σ w * ((w.1.mult : ℝ) * Real.log (w.1 ((algebraMap (𝓞 K) K) (fundSystem K i)))) =
          ∑ v : InfinitePlace K, g v := by
        have e0 : g dirichletUnitTheorem.w₀ = 0 := by simp [hg]
        symm
        rw [← Finset.add_sum_erase Finset.univ g (Finset.mem_univ _), e0, zero_add,
          Finset.sum_subtype (p := fun w => w ≠ dirichletUnitTheorem.w₀) (Finset.univ.erase dirichletUnitTheorem.w₀)
            (fun w => by simp) g]
        refine Finset.sum_congr rfl fun w _ => ?_
        simp [hg, hf, hα]
      rw [hsum]
      have h0 := NumberField.Units.sum_mult_mul_log (fundSystem K i)
      have e1 : ∀ v : InfinitePlace K, g v =
          (v.mult : ℝ) * (σ v - a v) * Real.log (v (((fundSystem K i : (𝓞 K)ˣ) : 𝓞 K) : K)) -
            (σ dirichletUnitTheorem.w₀ - a dirichletUnitTheorem.w₀) *
              ((v.mult : ℝ) * Real.log (v ((algebraMap (𝓞 K) K) (fundSystem K i)))) := by
        intro v
        have : (((fundSystem K i : (𝓞 K)ˣ) : 𝓞 K) : K) = (algebraMap (𝓞 K) K) (fundSystem K i) := rfl
        rw [hg, this]; ring
      rw [Finset.sum_congr rfl fun v _ => e1 v, Finset.sum_sub_distrib, hn, ← Finset.mul_sum, h0, mul_zero, sub_zero]
    · show ‖α + f σ‖ ≤ R
      have : α + f σ = fun w => σ w.1 - σ dirichletUnitTheorem.w₀ := by
        simp only [hf]; abel
      rw [this, pi_norm_le_iff_of_nonneg hR]
      intro w
      rw [Real.norm_eq_abs]
      calc |σ w.1 - σ dirichletUnitTheorem.w₀|
          ≤ ∑ v' : InfinitePlace K, |σ w.1 - σ v'| :=
            Finset.single_le_sum (f := fun v' => |σ w.1 - σ v'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ _)
        _ ≤ ∑ v : InfinitePlace K, ∑ v' : InfinitePlace K, |σ v - σ v'| :=
            Finset.single_le_sum (f := fun v => ∑ v' : InfinitePlace K, |σ v - σ v'|)
              (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ _)
        _ ≤ R := hσR
  have hinj : Set.InjOn f S := by
    intro σ hσ σ' hσ' hf'
    have hc : ∀ w : {w : InfinitePlace K // w ≠ dirichletUnitTheorem.w₀},
        σ w.1 - σ dirichletUnitTheorem.w₀ = σ' w.1 - σ' dirichletUnitTheorem.w₀ := by
      intro w
      have := congrFun hf' w
      simp only [hf, Pi.sub_apply] at this
      linarith
    have hall : ∀ v : InfinitePlace K, σ v - σ' v = σ dirichletUnitTheorem.w₀ - σ' dirichletUnitTheorem.w₀ := by
      intro v
      by_cases hv : v = dirichletUnitTheorem.w₀
      · rw [hv]
      · have := hc ⟨v, hv⟩; simp only at this; linarith
    have hconst : σ dirichletUnitTheorem.w₀ - σ' dirichletUnitTheorem.w₀ = 0 := by
      have := hall w₀; rw [hσ.1, hσ'.1] at this; linarith
    funext v
    have := hall v; rw [hconst] at this; linarith
  refine ⟨Set.Finite.of_injOn hmaps hinj hfin, ?_⟩
  rw [← hrank]
  refine le_trans ?_ hcount
  exact_mod_cast Set.ncard_le_ncard_of_injOn f hmaps hinj hfin

end

end S_NumberField_exists_forall_finite_and_ncard_setOf_sum_mult_mul_sub_mul_log_unit_le_mul_one_add_pow
end P2MW
export P2MW.S_NumberField_exists_forall_finite_and_ncard_setOf_sum_mult_mul_sub_mul_log_unit_le_mul_one_add_pow (solution)
