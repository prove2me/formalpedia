-- Prove2me | solution 1 for LinMaxLoad.theorem_17
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:49:41.018896+00:00
-- url     : https://prove2.me/submissions/21797d52-3862-4e11-b710-75a79cad93de
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LinMaxLoad_linMaxLoad
import Definitions.Def_LinMaxLoad_cosetSum
import Theorems.Thm_LinMaxLoad_theorem_17_per_piece
import Theorems.Thm_LinMaxLoad_section_2_1_max_load_facts

section
set_option autoImplicit false
namespace LinMaxLoad.Dev.Thm17

theorem avgLin_mono {K E : Type*} [Field K] [Fintype K] [AddCommGroup E] [Module K E] [Finite E]
    (r : ℕ) (X Y : (E →ₗ[K] (Fin r → K)) → ℝ) (hXY : ∀ h, X h ≤ Y h) :
    LinMaxLoad.avgLin K E r X ≤ LinMaxLoad.avgLin K E r Y := by
  unfold LinMaxLoad.avgLin
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun h _ => hXY h)
    (Nat.cast_pos.mpr (@Fintype.card_pos _ (Fintype.ofFinite _) _)).le

theorem avgLin_sum {K E : Type*} [Field K] [Fintype K] [AddCommGroup E] [Module K E] [Finite E]
    (r : ℕ) {ι : Type*} (s : Finset ι) (X : ι → (E →ₗ[K] (Fin r → K)) → ℝ) :
    LinMaxLoad.avgLin K E r (fun h => ∑ i ∈ s, X i h) = ∑ i ∈ s, LinMaxLoad.avgLin K E r (X i) := by
  unfold LinMaxLoad.avgLin
  rw [Finset.sum_comm, Finset.sum_div]


theorem maxLoad_biUnion {A B : Type*} [DecidableEq A] [DecidableEq B] {ι : Type*}
    (h : A → B) (s : Finset ι) (F : ι → Finset A) :
    LinMaxLoad.maxLoad h (s.biUnion F) ≤ ∑ i ∈ s, LinMaxLoad.maxLoad h (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [LinMaxLoad.maxLoad]
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    exact ((LinMaxLoad.section_2_1_max_load_facts h _ _).1).trans (Nat.add_le_add_left ih _)

end LinMaxLoad.Dev.Thm17
namespace LinMaxLoad
open LinMaxLoad.Dev.Thm17 in
open Pointwise in
theorem chk_theorem_17 :
    ∃ c : ℝ, ∀ (p : ℕ) [Fact p.Prime] (u C : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 →
      ∀ (S : Finset (Fin u → ZMod p)) (V : Fin C → Submodule (ZMod p) (Fin u → ZMod p))
        (T : Fin C → Finset (Fin u → ZMod p)),
        (∀ i, Nat.card (V i) ≤ S.card) →
        (∀ i, ((T i).card : ℝ) ≤ ((S.card : ℝ) / Nat.card (V i)) ^ (1 - ε)) →
        ((S : Set (Fin u → ZMod p)) ⊆ ⋃ i, ((V i : Set (Fin u → ZMod p)) + ((T i : Finset _) : Set (Fin u → ZMod p)))) →
        linMaxLoad p u S ≤ c * p * C / ε := by
  obtain ⟨c₁, hc₁⟩ := theorem_17_per_piece
  refine ⟨max c₁ 0, ?_⟩
  intro p _ u C ε hε hε1 S V T hV hT hcov
  have hsub : S ⊆ (Finset.univ : Finset (Fin C)).biUnion (fun i => cosetSum (V i) (T i)) := by
    intro y hy
    have := hcov hy
    simp only [Set.mem_iUnion] at this
    obtain ⟨i, hi⟩ := this
    rw [Finset.mem_biUnion]
    refine ⟨i, Finset.mem_univ _, ?_⟩
    unfold cosetSum
    rw [Set.Finite.mem_toFinset]
    exact hi
  have hpt : ∀ h : (Fin u → ZMod p) →ₗ[ZMod p] (Fin (Nat.clog p S.card) → ZMod p),
      (maxLoad (h : (Fin u → ZMod p) → Fin (Nat.clog p S.card) → ZMod p) S : ℝ) ≤
        ∑ i : Fin C, (maxLoad (h : (Fin u → ZMod p) → Fin (Nat.clog p S.card) → ZMod p)
          (cosetSum (V i) (T i)) : ℝ) := by
    intro h
    rw [← Nat.cast_sum]
    exact Nat.cast_le.mpr (((section_2_1_max_load_facts _ _ _).2 hsub).trans (maxLoad_biUnion _ _ _))
  have h1 : linMaxLoad p u S ≤ ∑ i : Fin C, expLoad (ZMod p) (Fin u → ZMod p) (Nat.clog p S.card)
        (cosetSum (V i) (T i)) := by
    have k1 := avgLin_mono (K := ZMod p) (E := Fin u → ZMod p) (Nat.clog p S.card)
      (fun h => (maxLoad (h : (Fin u → ZMod p) → Fin (Nat.clog p S.card) → ZMod p) S : ℝ))
      (fun h => ∑ i : Fin C, (maxLoad (h : (Fin u → ZMod p) → Fin (Nat.clog p S.card) → ZMod p)
          (cosetSum (V i) (T i)) : ℝ)) hpt
    rw [avgLin_sum] at k1
    unfold linMaxLoad expLoad
    convert k1
  have hp : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg _
  have h2 : ∀ i : Fin C, expLoad (ZMod p) (Fin u → ZMod p) (Nat.clog p S.card)
      (cosetSum (V i) (T i)) ≤ max c₁ 0 * p / ε := fun i =>
    (hc₁ p u ε hε hε1 S (V i) (T i) (hV i) (hT i)).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hp) hε.le)
  calc linMaxLoad p u S ≤ ∑ i : Fin C, expLoad (ZMod p) (Fin u → ZMod p) (Nat.clog p S.card)
        (cosetSum (V i) (T i)) := h1
    _ ≤ ∑ _i : Fin C, max c₁ 0 * p / ε := Finset.sum_le_sum fun i _ => h2 i
    _ = max c₁ 0 * p * C / ε := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
end LinMaxLoad
end

theorem solution : type_of% @LinMaxLoad.chk_theorem_17 := @LinMaxLoad.chk_theorem_17
