-- Prove2me | solution 1 for OAI.QAC.finite_scale_induction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:26:11.956866+00:00
-- url     : https://prove2.me/submissions/6c3c4c63-0055-4d8f-9599-1062e60d7637

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/ScaleInduction.lean:L11-L113
-- (upload_full_project.md Phase 4): solution for node OAI.QAC.finite_scale_induction. The node keeps its source
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

-- ---- from OAI.InformationTheory.QuantumCircuit.ScaleInduction ----
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Polynomial Filter Asymptotics

namespace QAC

/-- Finite scale bootstrap, stated for the uniform bound relation.  This is a
pure real-arithmetic induction and contains no operator-theoretic assumption. -/
theorem finite_scale_induction (B : ℝ → ℝ → Prop)
    (large : ∀ s t, 0 ≤ s → s < t → 1 < t → B s t)
    (backstep : ∀ s t a b u w, 0 ≤ s → s < a → a < u → u < w → w < t → t < b →
      (a + b) / 2 < u → B t b → B s t) :
    ∀ s t, 0 ≤ s → s < t → B s t := by
  intro s t hs hst
  by_cases ht : 1 < t
  · exact large s t hs hst ht
  have ht1 : t ≤ 1 := le_of_not_gt ht
  let g := t - s
  have hg : 0 < g := sub_pos.2 hst
  have hg1 : g ≤ 1 := by dsimp [g]; linarith
  let K := ⌈2 / g⌉₊
  let η := g ^ 2 / 100
  have hη : 0 < η := by dsimp [η]; positivity
  have hKlow : 2 / g ≤ (K : ℝ) := Nat.le_ceil _
  have hKhigh : (K : ℝ) < 2 / g + 1 := Nat.ceil_lt_add_one (by positivity)
  have hKg : (K : ℝ) * g ≥ 2 := (div_le_iff₀ hg).1 hKlow
  have hKg' : (K : ℝ) * g < 2 + g := by
    have := (lt_div_iff₀ hg).1 (show (K : ℝ) < (2 + g) / g by
      convert hKhigh using 1
      field_simp)
    exact this
  have hKη : 3 * (K : ℝ) * η < g / 2 := by
    dsimp [η]
    nlinarith only [hg, hg1, hKg', mul_lt_mul_of_pos_right hKg' hg]
  let T : ℕ → ℝ := fun i => t + (i : ℝ) * g - 3 * η * i * (i + 1) / 2
  let S : ℕ → ℝ := fun i => T i - (g - 3 * i * η)
  have hT0 : T 0 = t := by simp [T]
  have hS0 : S 0 = s := by simp [S, T, g]
  have hTS : ∀ i, S (i + 1) = T i := by
    intro i
    dsimp [S, T]
    push_cast
    ring
  have hgap : ∀ i ≤ K, g / 2 < T i - S i := by
    intro i hi
    have hi' : (i : ℝ) ≤ K := by exact_mod_cast hi
    dsimp [S]
    nlinarith only [hKη, mul_le_mul_of_nonneg_right hi' hη.le]
  have hTstep : ∀ i, T (i + 1) = 2 * T i - S i - 3 * η := by
    intro i
    dsimp [S, T]
    push_cast
    ring
  have hSnonneg : ∀ i ≤ K, 0 ≤ S i := by
    intro i
    induction i with
    | zero => intro _; simpa only [hS0] using hs
    | succ i ih =>
      intro hi
      have hiK : i ≤ K := by omega
      rw [hTS]
      have := hgap i hiK
      have := ih hiK
      linarith
  have hstep : ∀ i < K, T i + g / 2 < T (i + 1) := by
    intro i hi
    have h := hgap (i + 1) (by omega)
    rw [hTS] at h
    linarith
  have hTbound : ∀ i ≤ K, t + i * (g / 2) ≤ T i := by
    intro i
    induction i with
    | zero => intro _; simp [hT0]
    | succ i ih =>
      intro hi
      have h := hstep i (by omega)
      have h' := ih (by omega)
      push_cast
      linarith
  have hTK : 1 < T K := by
    have h := hTbound K le_rfl
    have ht0 : 0 < t := lt_of_le_of_lt hs hst
    nlinarith only [h, hKg, ht0]
  have hηgap : ∀ i ≤ K, 3 * η < T i - S i := by
    intro i hi
    have h := hgap i hi
    dsimp [η]
    nlinarith only [h, hg, hg1, mul_le_mul_of_nonneg_left hg1 hg.le]
  have hB : ∀ i ≤ K, B (S i) (T i) := by
    intro i hi
    induction hi using Nat.decreasingInduction with
    | self =>
      exact large (S K) (T K) (hSnonneg K le_rfl)
        (by have := hgap K le_rfl; linarith) hTK
    | of_succ i hi ih =>
      have hiK : i ≤ K := by omega
      have h := hηgap i hiK
      have htstep := hTstep i
      have hnext : B (T i) (T (i + 1)) := by simpa only [hTS] using ih
      apply backstep (S i) (T i) (S i + η / 2) (T (i + 1))
        (T i - η) (T i - η / 2) (hSnonneg i hiK)
      · linarith
      · linarith
      · linarith
      · linarith
      · linarith
      · linarith
      · exact hnext
  simpa only [hS0, hT0] using hB 0 (Nat.zero_le K)

end QAC

end

end OAI

-- ---- platform node ----
open OAI OAI.QAC
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Polynomial Filter Asymptotics

theorem solution (B : ℝ → ℝ → Prop)
    (large : ∀ s t, 0 ≤ s → s < t → 1 < t → B s t)
    (backstep : ∀ s t a b u w, 0 ≤ s → s < a → a < u → u < w → w < t → t < b →
      (a + b) / 2 < u → B t b → B s t) :
    ∀ s t, 0 ≤ s → s < t → B s t := by
  first
    | exact OAI.QAC.finite_scale_induction B large backstep
    | exact OAI.QAC.finite_scale_induction
    | (apply OAI.QAC.finite_scale_induction <;> assumption)
    | (intros; apply OAI.QAC.finite_scale_induction <;> assumption)
