-- Prove2me | solution 1 for MinimaxSLP.ObjExtremal.zero_weight_reduction
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T22:44:22.017123+00:00
-- url     : https://prove2.me/submissions/f525ff02-6dd5-4979-bbbb-985a946409bb

import Mathlib
import Definitions.Def_MinimaxSLP_ObjExtremal_Model
import Theorems.Thm_MinimaxSLP_ObjExtremal_Qval_homogeneous_superadditive
import Theorems.Thm_MinimaxSLP_ObjExtremal_scaled_weak_duality

open MeasureTheory Matrix

namespace MSLP2ZW
open MinimaxSLP.ObjSDP MinimaxSLP.ObjExtremal

lemma bordered_quad {d : ℕ} (V : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) (v0 : ℝ)
    (z : Fin d → ℝ) (c : ℝ) :
    star (Sum.elim z (fun _ : Fin 1 => c)) ⬝ᵥ (bordered V v v0 *ᵥ Sum.elim z (fun _ => c)) =
      z ⬝ᵥ (V *ᵥ z) + 2 * c * (z ⬝ᵥ v) + c ^ 2 * v0 := by
  simp only [star_trivial, bordered, dotProduct, mulVec, Fintype.sum_sum_type, fromBlocks_apply₁₁,
    fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Sum.elim_inl, Sum.elim_inr, of_apply,
    Fin.sum_univ_one]
  simp only [mul_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
  have : ∀ i, ∑ j, z i * (V i j * z j) = ∑ j, z i * V i j * z j := fun i =>
    Finset.sum_congr rfl fun j _ => by ring
  rw [Finset.sum_congr rfl fun i _ => this i]
  have e1 : ∑ i, z i * (v i * c) = ∑ i, c * (z i * v i) := Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, c * (v i * z i) = ∑ i, c * (z i * v i) := Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2]
  simp only [← Finset.mul_sum]
  ring

lemma bordered_psd_iff {d : ℕ} (V : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) (v0 : ℝ) :
    (bordered V v v0).PosSemidef ↔
      V.IsSymm ∧ ∀ z c, 0 ≤ z ⬝ᵥ (V *ᵥ z) + 2 * c * (z ⬝ᵥ v) + c ^ 2 * v0 := by
  constructor
  · intro hP
    refine ⟨?_, fun z c => ?_⟩
    · ext a b
      have := congrFun (congrFun hP.1 (Sum.inl a)) (Sum.inl b)
      simpa [bordered, conjTranspose_apply, transpose_apply] using this
    · rw [← bordered_quad]; exact hP.dotProduct_mulVec_nonneg _
  · rintro ⟨hS, hq⟩
    refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · ext a b
      rcases a with a | a <;> rcases b with b | b
      · simpa [bordered, conjTranspose_apply] using congrFun (congrFun hS a) b
      · simp [bordered, conjTranspose_apply]
      · simp [bordered, conjTranspose_apply]
      · simp [bordered, conjTranspose_apply]
    · intro y
      have hy : y = Sum.elim (fun a => y (Sum.inl a)) (fun _ : Fin 1 => y (Sum.inr 0)) := by
        funext a; rcases a with a | a
        · rfl
        · simp [Fin.fin_one_eq_zero a]
      rw [hy, bordered_quad]
      exact hq _ _

theorem zw_main {m₁ n r d K : ℕ} [NeZero K]
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (α β : Fin K → ℝ) (hα : ∀ k, 0 ≤ α k)
    (μ : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (hrec : (MinimaxSLP.ObjSDP.recourseSet W T h x).Nonempty)
    (s : (Fin K → Matrix (Fin d) (Fin d) ℝ) × (Fin K → Fin d → ℝ) × (Fin K → ℝ) ×
      (Fin K → Fin r → ℝ))
    (hs : s ∈ feasible9 W α μ Q)
    (hopt : ∀ s' ∈ feasible9 W α μ Q, obj9 T h β x s' ≤ obj9 T h β x s) :
    ∃ s' ∈ feasible9 W α μ Q, obj9 T h β x s' = obj9 T h β x s ∧
      (∀ k, s'.2.2.1 k = s.2.2.1 k) ∧
      ∀ k, 0 < s'.2.2.1 k ∨
        (s'.1 k = 0 ∧ s'.2.1 k = 0 ∧ s'.2.2.1 k = 0 ∧ s'.2.2.2 k = 0) := by
  obtain ⟨V, v, v0, p⟩ := s
  obtain ⟨hsumB, hpsd, hdual⟩ := hs
  simp only at hsumB hpsd hdual hopt ⊢
  obtain ⟨hhom, -⟩ := Qval_homogeneous_superadditive W T h hA3 x hrec
  have hQv0 : Qval W T h 0 x = 0 := by
    have := hhom 2 (by norm_num) 0
    simp only [smul_zero] at this
    linarith
  have F1 : ∀ k z c, 0 ≤ z ⬝ᵥ (V k *ᵥ z) + 2 * c * (z ⬝ᵥ v k) + c ^ 2 * v0 k :=
    fun k => ((bordered_psd_iff _ _ _).mp (hpsd k)).2
  have hsym : ∀ k, (V k).IsSymm := fun k => ((bordered_psd_iff _ _ _).mp (hpsd k)).1
  have F2 : ∀ k, 0 ≤ v0 k := by
    intro k; have := F1 k 0 1; simpa using this
  have F3'' : ∑ k, v0 k = 1 := by
    have := congrFun (congrFun hsumB (Sum.inr 0)) (Sum.inr 0)
    simpa [Matrix.sum_apply, bordered] using this
  have F4 : ∀ k, v0 k = 0 → v k = 0 := by
    intro k hk
    have hB : 0 ≤ v k ⬝ᵥ v k := by
      simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    rcases hB.lt_or_eq with hB | hB
    · exfalso
      set A := v k ⬝ᵥ (V k *ᵥ v k)
      have := F1 k (v k) (-(|A| + 1) / (2 * (v k ⬝ᵥ v k)))
      rw [hk] at this
      have e : 2 * (-(|A| + 1) / (2 * (v k ⬝ᵥ v k))) * (v k ⬝ᵥ v k) = -(|A| + 1) := by
        field_simp
      rw [e] at this
      have := le_abs_self A
      nlinarith
    · exact dotProduct_self_eq_zero.mp hB.symm
  have hVpsd : ∀ k z, 0 ≤ z ⬝ᵥ (V k *ᵥ z) := fun k z => by simpa using F1 k z 0
  -- a block with positive weight
  obtain ⟨j, hj⟩ : ∃ j, 0 < v0 j := by
    by_contra hne
    push_neg at hne
    have : ∑ k, v0 k ≤ 0 := Finset.sum_nonpos fun k _ => hne k
    linarith
  classical
  set ext : Matrix (Fin d) (Fin d) ℝ := ∑ k, if 0 < v0 k then 0 else V k with hext
  set V' : Fin K → Matrix (Fin d) (Fin d) ℝ :=
    fun k => if k = j then V k + ext else if 0 < v0 k then V k else 0 with hV'
  set p' : Fin K → Fin r → ℝ := fun k => if 0 < v0 k then p k else 0 with hp'
  have hnp : ∀ k, ¬ 0 < v0 k → v0 k = 0 := fun k hk => le_antisymm (not_lt.mp hk) (F2 k)
  have hextq : ∀ z, 0 ≤ z ⬝ᵥ (ext *ᵥ z) := by
    intro z
    rw [hext, sum_mulVec, dotProduct_sum]
    refine Finset.sum_nonneg fun k _ => ?_
    split_ifs
    · simp
    · exact hVpsd k z
  have hextS : ext.IsSymm := by
    rw [hext, IsSymm, transpose_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs
    · simp
    · exact hsym k
  have hfeas : (V', v, v0, p') ∈ feasible9 W α μ Q := by
    refine ⟨?_, ?_, ?_⟩
    · rw [← hsumB]
      simp only
      ext a b
      rcases a with a | a <;> rcases b with b | b <;>
        simp only [Matrix.sum_apply, bordered, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
          fromBlocks_apply₂₁, fromBlocks_apply₂₂]
      have e : ∀ k, V' k a b = (if 0 < v0 k then V k a b else 0) + (if k = j then ext a b else 0) := by
        intro k
        simp only [hV']
        by_cases hk : k = j
        · subst hk; simp [hj]
        · simp only [hk, if_false, add_zero]; split_ifs <;> rfl
      rw [Finset.sum_congr rfl fun k _ => e k, Finset.sum_add_distrib, Finset.sum_ite_eq']
      simp only [Finset.mem_univ, if_true, hext, Matrix.sum_apply]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      split_ifs <;> simp
    · intro k
      rw [bordered_psd_iff]
      simp only [hV']
      by_cases hk : k = j
      · subst hk
        simp only [if_true]
        refine ⟨(hsym k).add hextS, fun z c => ?_⟩
        rw [add_mulVec, dotProduct_add]
        have := F1 k z c
        have := hextq z
        linarith
      · simp only [hk, if_false]
        by_cases hpk : 0 < v0 k
        · simp only [hpk, if_true]; exact ⟨hsym k, F1 k⟩
        · simp only [hpk, if_false]
          refine ⟨by simp [IsSymm], fun z c => ?_⟩
          rw [F4 k (hnp k hpk), hnp k hpk]
          simp
    · intro k
      simp only [hp']
      by_cases hpk : 0 < v0 k
      · simp only [hpk, if_true]; exact hdual k
      · simp only [hpk, if_false, mulVec_zero]
        rw [F4 k (hnp k hpk), smul_zero]
  refine ⟨(V', v, v0, p'), hfeas, ?_, fun k => rfl, ?_⟩
  · refine le_antisymm (hopt _ hfeas) ?_
    unfold obj9
    simp only
    refine Finset.sum_le_sum fun k _ => ?_
    simp only [hp']
    by_cases hpk : 0 < v0 k
    · simp [hpk]
    · simp only [hpk, if_false, dotProduct_zero, zero_add]
      have := scaled_weak_duality W T h hA3 x hrec (α k) (hα k) (v k) (p k) (hdual k)
      rw [F4 k (hnp k hpk), hQv0, mul_zero] at this
      linarith
  · intro k
    by_cases hpk : 0 < v0 k
    · exact Or.inl hpk
    · right
      have hkj : k ≠ j := fun e => hpk (e ▸ hj)
      refine ⟨?_, F4 k (hnp k hpk), hnp k hpk, ?_⟩
      · simp [hV', hkj, hpk]
      · simp [hp', hpk]

end MSLP2ZW

open MinimaxSLP.ObjExtremal in
theorem solution {m₁ n r d K : ℕ} [NeZero K]
    (A : Matrix (Fin m₁) (Fin n) ℝ) (b : Fin m₁ → ℝ)
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (α β : Fin K → ℝ) (hα : ∀ k, 0 ≤ α k)
    (μ : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.IsSymm) (hA4 : (Q - Matrix.vecMulVec μ μ).PosDef)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (hx : x ∈ MinimaxSLP.ObjSDP.X A b) (hrec : (MinimaxSLP.ObjSDP.recourseSet W T h x).Nonempty)
    (s : (Fin K → Matrix (Fin d) (Fin d) ℝ) × (Fin K → Fin d → ℝ) × (Fin K → ℝ) ×
      (Fin K → Fin r → ℝ))
    (hs : s ∈ feasible9 W α μ Q)
    (hopt : ∀ s' ∈ feasible9 W α μ Q, obj9 T h β x s' ≤ obj9 T h β x s) :
    ∃ s' ∈ feasible9 W α μ Q, obj9 T h β x s' = obj9 T h β x s ∧
      (∀ k, s'.2.2.1 k = s.2.2.1 k) ∧
      ∀ k, 0 < s'.2.2.1 k ∨
        (s'.1 k = 0 ∧ s'.2.1 k = 0 ∧ s'.2.2.1 k = 0 ∧ s'.2.2.2 k = 0) :=
  MSLP2ZW.zw_main (m₁ := m₁) W T h α β hα μ Q hA3 x hrec s hs hopt
