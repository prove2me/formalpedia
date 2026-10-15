-- Prove2me | solution 1 for OAI.QAC.toffoli_reflection
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:28:43.844087+00:00
-- url     : https://prove2.me/submissions/45c54287-b55d-4e76-b9c7-00cc988e4d34

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Toffoli.lean:L92-L128
-- (upload_full_project.md Phase 4): solution for node OAI.QAC.toffoli_reflection. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_QACParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Basic
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ProductProjection
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Circuit
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Count
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Spectral
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Transition
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Reflection
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Polynomial
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_DepthZero
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Localization
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Toffoli

-- ---- from OAI.InformationTheory.QuantumCircuit.Toffoli ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Matrix Polynomial Filter Asymptotics

namespace QAC

lemma rankOne_basis (b : Bit) (x y : Bit) :
    rankOne (basisVector b) x y = if x=b ∧ y=b then 1 else 0 := by
  classical
  simp only [rankOne,basisVector]
  split_ifs <;> simp_all

lemma rankOne_minus (x y : Bit) :
    rankOne minusVector x y = if x=y then (1/2:ℂ) else -(1/2:ℂ) := by
  have hh : (halfScale:ℂ)^2 = 1/2 := by rw [← Complex.ofReal_pow,halfScale_sq]; norm_num
  fin_cases x <;> fin_cases y <;> simp [rankOne,minusVector,← pow_two,hh]

lemma toffoliCount_entry {N : ℕ} (c : Finset (Fin N)) (t : Fin N) (ht : t ∉ c)
    (x y : Word N) :
    (toffoliCount c t).zero x y =
      if (∀ i, i ≠ t → x i=y i) ∧ (∀ i ∈ c, y i=1) then
        rankOne minusVector (x t) (y t) else 0 := by
  classical
  let a : Fin N → QubitOperator := fun i =>
    if i ∈ insert t c then rankOne (if i=t then minusVector else basisVector 1) else 1
  change (∏ i, a i (x i) (y i)) = _
  have hat : a t (x t) (y t) = rankOne minusVector (x t) (y t) := by simp [a]
  have hf : ∀ i, i ≠ t → a i (x i) (y i) =
      if x i=y i ∧ (i ∈ c → y i=1) then 1 else 0 := by
    intro i hi
    by_cases hic : i ∈ c
    · simp only [a,Finset.mem_insert,hic,or_true,ite_true,ite_eq_right hi,rankOne_basis,true_implies]
      congr 1
      apply propext
      constructor
      · rintro ⟨hx,hy⟩; exact ⟨hx.trans hy.symm,hy⟩
      · rintro ⟨hxy,hy⟩; exact ⟨hxy.trans hy,hy⟩
    · simp [a,hi,hic,Matrix.one_apply]
  split_ifs with h
  · rw [Finset.prod_eq_single t]
    · exact hat
    · intro i _ hit
      rw [hf i hit,ite_eq_left ⟨h.1 i hit,h.2 i⟩]
    · simp
  · obtain h | h := not_and_or.mp h
    · push Not at h
      obtain ⟨i,hit,hxy⟩ := h
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hf i hit]; simp [hxy])
    · push Not at h
      obtain ⟨i,hic,hy⟩ := h
      have hit : i ≠ t := fun h => ht (h ▸ hic)
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hf i hit]; simp [hic,hy])

lemma toffoli_reflection {N : ℕ} (c : Finset (Fin N)) (t : Fin N) (ht : t ∉ c) :
    Gate.matrix (.toffoli c t ht) = reflect (toffoliCount c t) := by
  classical
  ext x y
  change (if x=Gate.toffoliWord c t y then (1:ℂ) else 0) =
    (if x=y then 1 else 0) - 2*(toffoliCount c t).zero x y
  rw [toffoliCount_entry c t ht]
  by_cases hctrl : ∀ i ∈ c, y i=1
  · have hw : Gate.toffoliWord c t y = Function.update y t (1-y t) := by
      exact ite_eq_left hctrl
    rw [hw]
    by_cases hrest : ∀ i, i ≠ t → x i=y i
    · have hxy : x=y ↔ x t=y t := by
        constructor
        · intro h; exact congrFun h t
        · intro h; funext i; by_cases hi : i=t
          · simpa [hi] using h
          · exact hrest i hi
      have hxu : x=Function.update y t (1-y t) ↔ x t=1-y t := by
        constructor
        · intro h; simpa using congrFun h t
        · intro h; funext i; by_cases hi : i=t
          · simpa [hi] using h
          · simpa [Function.update_of_ne hi] using hrest i hi
      have hboth : (∀ i, i ≠ t → x i=y i) ∧ (∀ i ∈ c, y i=1) := ⟨hrest,hctrl⟩
      rw [ite_eq_left hboth,rankOne_minus]
      simp only [hxy,hxu]
      generalize x t = a, y t = b
      fin_cases a <;> fin_cases b <;> norm_num
    · have hxy : x ≠ y := by intro h; apply hrest; intro i _; exact congrFun h i
      have hxu : x ≠ Function.update y t (1-y t) := by
        intro h; apply hrest; intro i hi
        simpa [Function.update_of_ne hi] using congrFun h i
      simp [hrest,hxy,hxu]
  · have hw : Gate.toffoliWord c t y = y := by exact ite_eq_right hctrl
    rw [hw]
    simp [hctrl]

end QAC

end

end OAI

-- ---- platform node ----
open OAI OAI.QAC
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Matrix Polynomial Filter Asymptotics

theorem solution {N : ℕ} (c : Finset (Fin N)) (t : Fin N) (ht : t ∉ c) :
    Gate.matrix (.toffoli c t ht) = reflect (toffoliCount c t) := by
  first
    | exact OAI.QAC.toffoli_reflection c t ht
    | exact OAI.QAC.toffoli_reflection
    | (apply OAI.QAC.toffoli_reflection <;> assumption)
    | (intros; apply OAI.QAC.toffoli_reflection <;> assumption)
