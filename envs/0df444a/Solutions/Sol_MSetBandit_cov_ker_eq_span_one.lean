-- Prove2me | solution 1 for MSetBandit.cov_ker_eq_span_one
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:11:00.973803+00:00
-- url     : https://prove2.me/submissions/ee37faf4-7d6c-46fa-bcd2-5dc9343858d7

import Mathlib
import Definitions.Def_MSetBandit_cov
import Definitions.Def_MSetBandit_wdist
open Matrix

namespace Aux_MSet_cov
open MSetBandit Matrix

def sc {d m : ℕ} (z : Fin d → ℝ) (x : Action d m) : ℝ := ∑ j, ind x j * z j

theorem ind_sum {d m : ℕ} (x : Action d m) : ∑ i, ind x i = m := by
  unfold ind
  rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter, x.2]

theorem covz {d m : ℕ} (p : Action d m → ℝ) (z : Fin d → ℝ) (i : Fin d) :
    (cov p *ᵥ z) i = ∑ x, p x * ind x i * (sc z x - ∑ y, p y * sc z y) := by
  have h1 : (secondMoment p *ᵥ z) i = ∑ x, p x * ind x i * sc z x := by
    simp only [Matrix.mulVec, dotProduct, secondMoment, Matrix.of_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [sc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h2 : marg p ⬝ᵥ z = ∑ y, p y * sc z y := by
    simp only [dotProduct, marg, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [sc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  unfold cov
  rw [Matrix.sub_mulVec, Pi.sub_apply, h1, vecMulVec_mulVec, Pi.smul_apply, h2]
  simp only [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, marg, Finset.sum_mul,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

end Aux_MSet_cov

open MSetBandit Matrix Aux_MSet_cov in
theorem solution {d m : ℕ} (hm : 1 ≤ m) (hmd : m + 1 ≤ d) (θ : Fin d → ℝ) :
    (∀ z : Fin d → ℝ, cov (wdist (m := m) θ) *ᵥ z = 0 ↔ ∃ a : ℝ, z = fun _ => a) ∧
    (∀ y : Fin d → ℝ, (∃ z, cov (wdist (m := m) θ) *ᵥ z = y) ↔ ∑ i, y i = 0) := by
  classical
  set p := wdist (m := m) θ with hpdef
  have hZpos : 0 < ∑ y : Action d m, Real.exp (θ ⬝ᵥ ind y) := by
    obtain ⟨t, _, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin d)))
      (n := m) (by rw [Finset.card_univ, Fintype.card_fin]; omega)
    exact Finset.sum_pos (fun y _ => Real.exp_pos _) ⟨⟨t, ht⟩, Finset.mem_univ _⟩
  have hp_pos : ∀ x, 0 < p x := fun x => div_pos (Real.exp_pos _) hZpos
  have hp1 : ∑ x, p x = 1 := by
    rw [hpdef]; unfold wdist; rw [← Finset.sum_div, div_self hZpos.ne']
  -- the variance identity
  have hquad : ∀ z : Fin d → ℝ, ∑ i, z i * (cov p *ᵥ z) i =
      ∑ x, p x * (sc z x - ∑ y, p y * sc z y) ^ 2 := by
    intro z
    simp only [covz, Finset.mul_sum]
    rw [Finset.sum_comm]
    set S := ∑ y, p y * sc z y with hS
    have h0 : ∑ x, p x * (sc z x - S) = 0 := by
      rw [Finset.sum_congr rfl (fun x _ => mul_sub (p x) (sc z x) S), Finset.sum_sub_distrib,
        ← Finset.sum_mul, hp1, one_mul, hS, sub_self]
    have : ∀ x, ∑ i, z i * (p x * ind x i * (sc z x - S)) = p x * (sc z x - S) ^ 2 + S * (p x * (sc z x - S)) := by
      intro x
      have e : ∑ i, z i * (p x * ind x i * (sc z x - S)) =
          (∑ i, ind x i * z i) * (p x * (sc z x - S)) := by
        rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; ring
      rw [e]
      have e2 : (∑ i, ind x i * z i) = sc z x := rfl
      rw [e2]; ring
    rw [Finset.sum_congr rfl (fun x _ => this x), Finset.sum_add_distrib, ← Finset.mul_sum, h0,
      mul_zero, add_zero]
  have hsumcov : ∀ z : Fin d → ℝ, ∑ i, (cov p *ᵥ z) i = 0 := by
    intro z
    simp only [covz]
    rw [Finset.sum_comm]
    set S := ∑ y, p y * sc z y with hS
    have : ∀ x, ∑ i, p x * ind x i * (sc z x - S) = (m : ℝ) * (p x * (sc z x - S)) := by
      intro x
      rw [← Finset.sum_mul, ← Finset.mul_sum, ind_sum]; ring
    rw [Finset.sum_congr rfl (fun x _ => this x), ← Finset.mul_sum,
      Finset.sum_congr rfl (fun x _ => mul_sub (p x) (sc z x) S), Finset.sum_sub_distrib,
      ← Finset.sum_mul, hp1, one_mul, hS, sub_self, mul_zero]
  have part1 : ∀ z : Fin d → ℝ, cov p *ᵥ z = 0 ↔ ∃ a : ℝ, z = fun _ => a := by
    intro z
    constructor
    · intro hz
      have hq := hquad z
      rw [hz] at hq
      simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at hq
      set S := ∑ y, p y * sc z y
      have hconst : ∀ x : Action d m, sc z x = S := by
        intro x
        have hnn : ∀ x ∈ Finset.univ, 0 ≤ p x * (sc z x - S) ^ 2 :=
          fun x _ => mul_nonneg (hp_pos x).le (sq_nonneg _)
        have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hq.symm x (Finset.mem_univ _)
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h (hp_pos x).ne'
        · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h; linarith
      have hij : ∀ i j : Fin d, i ≠ j → z i = z j := by
        intro i j hij
        obtain ⟨t, ht, htc⟩ := Finset.exists_subset_card_eq
          (s := (Finset.univ.erase i).erase j) (n := m - 1) (by
            rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ _⟩),
              Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
            omega)
        have hit : i ∉ t := fun h => by have := ht h; simp at this
        have hjt : j ∉ t := fun h => by have := ht h; simp at this
        have hc1 : (insert i t).card = m := by rw [Finset.card_insert_of_notMem hit, htc]; omega
        have hc2 : (insert j t).card = m := by rw [Finset.card_insert_of_notMem hjt, htc]; omega
        have e1 := hconst ⟨insert i t, hc1⟩
        have e2 := hconst ⟨insert j t, hc2⟩
        have hs : ∀ (k : Fin d) (hk : k ∉ t) (hc : (insert k t).card = m),
            sc z ⟨insert k t, hc⟩ = z k + ∑ l ∈ t, z l := by
          intro k hk hc
          unfold sc ind
          simp only [ite_mul, one_mul, zero_mul]
          rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_insert hk]
        rw [hs i hit hc1] at e1
        rw [hs j hjt hc2] at e2
        linarith
      have hd : 0 < d := by omega
      refine ⟨z ⟨0, hd⟩, funext fun i => ?_⟩
      by_cases h : i = ⟨0, hd⟩
      · rw [h]
      · exact hij i ⟨0, hd⟩ h
    · rintro ⟨a, rfl⟩
      funext i
      rw [covz]
      have hsc : ∀ x : Action d m, sc (fun _ => a) x = a * m := by
        intro x; unfold sc; rw [← Finset.sum_mul, ind_sum]; ring
      simp only [hsc, ← Finset.sum_mul, hp1, one_mul, sub_self, mul_zero, Finset.sum_const_zero,
        Pi.zero_apply]
  refine ⟨part1, fun y => ⟨?_, ?_⟩⟩
  · rintro ⟨z, rfl⟩; exact hsumcov z
  · intro hy
    -- dimension argument
    set L := Matrix.mulVecLin (cov p) with hL
    let Sm : (Fin d → ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun v => ∑ i, v i
        map_add' := fun u v => by simp [Finset.sum_add_distrib]
        map_smul' := fun c v => by simp [Finset.mul_sum] }
    have hle : LinearMap.range L ≤ LinearMap.ker Sm := by
      rintro _ ⟨z, rfl⟩
      exact hsumcov z
    have hd : 0 < d := by omega
    have hker : LinearMap.ker L = ℝ ∙ (fun _ : Fin d => (1 : ℝ)) := by
      ext z
      rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
      show cov p *ᵥ z = 0 ↔ _
      rw [part1]
      constructor
      · rintro ⟨a, rfl⟩; exact ⟨a, by funext; simp⟩
      · rintro ⟨a, rfl⟩; exact ⟨a, by funext; simp⟩
    have hone : (fun _ : Fin d => (1 : ℝ)) ≠ 0 := by
      intro h; have := congrFun h ⟨0, hd⟩; simp at this
    have hrL := LinearMap.finrank_range_add_finrank_ker L
    rw [hker, finrank_span_singleton hone, Module.finrank_fin_fun] at hrL
    have hSm_surj : LinearMap.range Sm = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro r
      refine ⟨fun i => if i = ⟨0, hd⟩ then r else 0, ?_⟩
      show ∑ i, (if i = (⟨0, hd⟩ : Fin d) then r else 0) = r
      simp
    have hrS := LinearMap.finrank_range_add_finrank_ker Sm
    rw [hSm_surj, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at hrS
    have heq : LinearMap.range L = LinearMap.ker Sm :=
      Submodule.eq_of_le_of_finrank_eq hle (by omega)
    have hyk : y ∈ LinearMap.ker Sm := hy
    rw [← heq] at hyk
    obtain ⟨z, hz⟩ := hyk
    exact ⟨z, hz⟩
