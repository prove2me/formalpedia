-- Prove2me | solution 1 for LovaszSchrijver.OddHole.mem_NG_iff_matrix_system
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T18:18:14.294782+00:00
-- url     : https://prove2.me/submissions/a29e1b85-4848-444a-abb7-c9b1a6c8dc63

import Mathlib
import Definitions.Def_LovaszSchrijver_OddHole_MatrixCone
import Definitions.Def_LovaszSchrijver_OddHole_StableSetCones

set_option autoImplicit false

namespace LSHelp69127d82
open LovaszSchrijver.OddHole Matrix

lemma dualQ_of {ι : Type} [Fintype ι] (v : Option ι → ℝ)
    (h : ∀ x : Option ι → ℝ, x none = 1 → (∀ i : ι, x (some i) = 0 ∨ x (some i) = 1) →
      0 ≤ v ⬝ᵥ x) :
    v ∈ dualCone (Q ι) := by
  intro x hx
  unfold Q at hx
  rw [SetLike.mem_coe] at hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact h y hy.1 hy.2
  | zero => simp
  | add a b _ _ ha hb => rw [dotProduct_add]; exact add_nonneg ha hb
  | smul c a _ ha =>
    rw [← Nonneg.coe_smul, dotProduct_smul, smul_eq_mul]; exact mul_nonneg c.2 ha

lemma mem_Q_of {ι : Type} (x : Option ι → ℝ) (h0 : x none = 1)
    (h : ∀ i : ι, x (some i) = 0 ∨ x (some i) = 1) : x ∈ Q ι := by
  unfold Q
  exact PointedCone.subset_hull ⟨h0, h⟩

lemma single_mem_dualQ {ι : Type} [Fintype ι] [DecidableEq ι] (q : Option ι) :
    (Pi.single q 1 : Option ι → ℝ) ∈ dualCone (Q ι) := by
  apply dualQ_of
  intro x h0 h
  rw [single_dotProduct, one_mul]
  cases q with
  | none => rw [h0]; norm_num
  | some k => rcases h k with hk | hk <;> rw [hk] <;> norm_num

lemma diff_mem_dualQ {ι : Type} [Fintype ι] [DecidableEq ι] (k : ι) :
    (Pi.single none 1 - Pi.single (some k) 1 : Option ι → ℝ) ∈ dualCone (Q ι) := by
  apply dualQ_of
  intro x h0 h
  rw [sub_dotProduct, single_dotProduct, single_dotProduct, one_mul, one_mul, h0]
  rcases h k with hk | hk <;> rw [hk] <;> norm_num

lemma single_some_mem_dualFR {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (i : V) : (Pi.single (some i) 1 : Option V → ℝ) ∈ dualCone (FR G) := by
  intro w hw
  rw [single_dotProduct, one_mul]
  exact hw.1 i

lemma edge_mem_dualFR {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (i j : V) (h : G.Adj i j) :
    (Pi.single none 1 - Pi.single (some i) 1 - Pi.single (some j) 1 : Option V → ℝ) ∈
      dualCone (FR G) := by
  intro w hw
  simp only [sub_dotProduct, single_dotProduct, one_mul]
  linarith [hw.2 i j h]

lemma mulVec_single_apply {ι : Type} [Fintype ι] [DecidableEq ι]
    (Y : Matrix (Option ι) (Option ι) ℝ) (q p : Option ι) :
    (Y *ᵥ (Pi.single q 1 : Option ι → ℝ)) p = Y p q := by
  simp [Matrix.mulVec_single_one, Matrix.col]

lemma vecMul_apply_eq {ι : Type} [Fintype ι] [DecidableEq ι]
    (Y : Matrix (Option ι) (Option ι) ℝ) (u : Option ι → ℝ) (o : Option ι) :
    (u ᵥ* Y) o = u ⬝ᵥ (Y *ᵥ (Pi.single o 1 : Option ι → ℝ)) := by
  simp [Matrix.mulVec_single_one, Matrix.vecMul, dotProduct]

end LSHelp69127d82

open LSHelp69127d82 in
open Matrix in
open LovaszSchrijver.OddHole in
theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : ∀ v, ∃ w, G.Adj v w) (x : V → ℝ) :
    x ∈ NG G ↔ ∃ Y : Matrix (Option V) (Option V) ℝ,
      (∀ p q, 0 ≤ Y p q) ∧ Y.IsSymm ∧ Y none none = 1 ∧
      (∀ i, Y (some i) none = x i ∧ Y (some i) (some i) = x i) ∧
      ∀ i j k, G.Adj i j →
        x i + x j + x k - 1 ≤ Y (some i) (some k) + Y (some j) (some k) ∧
        Y (some i) (some k) + Y (some j) (some k) ≤ x k := by
  constructor
  · rintro ⟨Y, ⟨hsymm, hdiag, hdual⟩, hcol⟩
    have hS : ∀ p q, Y p q = Y q p := fun p q => by
      have := congrFun (congrFun hsymm q) p
      simpa [Matrix.transpose_apply] using this
    have hY0 : ∀ p, Y p none = hom x p := fun p => by
      rw [← hcol, mulVec_single_apply]
    have h00 : Y none none = 1 := by rw [hY0]; rfl
    have hi0 : ∀ i, Y (some i) none = x i := fun i => by rw [hY0]; rfl
    have hpos : ∀ i q, 0 ≤ Y (some i) q := fun i q => by
      have := hdual _ (single_some_mem_dualFR G i) _ (single_mem_dualQ q)
      rwa [single_dotProduct, one_mul, mulVec_single_apply] at this
    refine ⟨Y, ?_, hsymm, h00, fun i => ⟨hi0 i, ?_⟩, ?_⟩
    · intro p q
      cases p with
      | some i => exact hpos i q
      | none =>
        cases q with
        | none => rw [h00]; norm_num
        | some k => rw [hS]; exact hpos k none
    · rw [hdiag, hS, hi0]
    · intro i j k hij
      have hlo := hdual _ (edge_mem_dualFR G i j hij) _ (diff_mem_dualQ k)
      have hup := hdual _ (edge_mem_dualFR G i j hij) _ (single_mem_dualQ (some k))
      simp only [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, single_dotProduct, one_mul,
        Pi.sub_apply, mulVec_single_apply] at hlo hup
      have hk0 : Y none (some k) = x k := by rw [hS, hi0]
      rw [h00, hk0, hi0, hi0] at hlo
      rw [hk0] at hup
      constructor <;> linarith
  · rintro ⟨Y, hnn, hsymm, h00, hx, hE⟩
    have hS : ∀ p q, Y p q = Y q p := fun p q => by
      have := congrFun (congrFun hsymm q) p
      simpa [Matrix.transpose_apply] using this
    refine ⟨Y, ⟨hsymm, ?_, ?_⟩, ?_⟩
    · intro i; rw [(hx i).2, hS, (hx i).1]
    · intro u hu v hv
      have hc0 : Y *ᵥ (Pi.single none 1 : Option V → ℝ) ∈ FR G := by
        refine ⟨fun i => ?_, fun i j hij => ?_⟩
        · rw [mulVec_single_apply]; exact hnn _ _
        · rw [mulVec_single_apply, mulVec_single_apply, mulVec_single_apply, (hx i).1,
            (hx j).1, h00]
          have := hE i j i hij
          rw [(hx i).2] at this
          linarith [this.1, this.2]
      have hck : ∀ k, Y *ᵥ (Pi.single (some k) 1 : Option V → ℝ) ∈ FR G := by
        intro k
        refine ⟨fun i => ?_, fun i j hij => ?_⟩
        · rw [mulVec_single_apply]; exact hnn _ _
        · rw [mulVec_single_apply, mulVec_single_apply, mulVec_single_apply, hS none,
            (hx k).1]
          exact (hE i j k hij).2
      have hcd : ∀ k, Y *ᵥ (Pi.single none 1 - Pi.single (some k) 1 : Option V → ℝ) ∈ FR G := by
        intro k
        refine ⟨fun i => ?_, fun i j hij => ?_⟩
        · rw [Matrix.mulVec_sub, Pi.sub_apply, mulVec_single_apply, mulVec_single_apply,
            (hx i).1, hS (some i) (some k)]
          obtain ⟨w, hw⟩ := hG k
          have := (hE k w i hw).2
          linarith [hnn (some w) (some i)]
        · simp only [Matrix.mulVec_sub, Pi.sub_apply, mulVec_single_apply]
          rw [(hx i).1, (hx j).1, h00, hS none (some k), (hx k).1]
          linarith [(hE i j k hij).1]
      set c := u ⬝ᵥ (Y *ᵥ (Pi.single none 1 : Option V → ℝ)) with hc
      set a : V → ℝ := fun k => u ⬝ᵥ (Y *ᵥ (Pi.single (some k) 1 : Option V → ℝ)) with ha
      have hc_nn : 0 ≤ c := hu _ hc0
      have ha_nn : ∀ k, 0 ≤ a k := fun k => hu _ (hck k)
      have ha_le : ∀ k, a k ≤ c := fun k => by
        have := hu _ (hcd k)
        rw [Matrix.mulVec_sub, dotProduct_sub] at this
        simp only [ha, hc]
        linarith
      have hexp : u ⬝ᵥ (Y *ᵥ v) = v none * c + ∑ k, v (some k) * a k := by
        rw [Matrix.dotProduct_mulVec, dotProduct, Fintype.sum_option, vecMul_apply_eq]
        congr 1
        · ring
        · refine Finset.sum_congr rfl fun k _ => ?_
          rw [vecMul_apply_eq]; ring
      let w : Option V → ℝ := fun o => o.elim 1 (fun k => if v (some k) < 0 then 1 else 0)
      have hwQ : w ∈ Q V := by
        apply mem_Q_of
        · rfl
        · intro i
          show (if v (some i) < 0 then (1:ℝ) else 0) = 0 ∨ (if v (some i) < 0 then (1:ℝ) else 0) = 1
          split_ifs <;> simp
      have hvw := hv w hwQ
      have hvw' : v ⬝ᵥ w = v none + ∑ k, (if v (some k) < 0 then v (some k) else 0) := by
        rw [dotProduct, Fintype.sum_option]
        congr 1
        · show v none * 1 = v none; ring
        · refine Finset.sum_congr rfl fun k _ => ?_
          show v (some k) * (if v (some k) < 0 then (1:ℝ) else 0) = _
          split_ifs <;> ring
      have hterm : ∀ k, (if v (some k) < 0 then v (some k) else 0) * c ≤ v (some k) * a k := by
        intro k
        split_ifs with hneg
        · nlinarith [ha_le k]
        · push_neg at hneg; rw [zero_mul]; exact mul_nonneg hneg (ha_nn k)
      have hsum : (∑ k, (if v (some k) < 0 then v (some k) else 0)) * c ≤
          ∑ k, v (some k) * a k := by
        rw [Finset.sum_mul]; exact Finset.sum_le_sum fun k _ => hterm k
      rw [hexp]
      rw [hvw'] at hvw
      nlinarith [mul_nonneg hvw hc_nn]
    · funext p
      rw [mulVec_single_apply]
      cases p with
      | none => exact h00
      | some i => exact (hx i).1
