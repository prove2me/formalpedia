-- Prove2me | solution 1 for InventoryAnomaly.EW.lemma_14
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-10-28T06:53:52.708138+00:00
-- url     : https://prove2.me/submissions/b2cb4345-a094-4f93-af20-637e9dfe9a96

import Mathlib

namespace Prove2SwarmSubmission

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-!
# `InventoryAnomaly.EW.lemma_14`: independence, MGF and expectation bridge (source-scout)

This file holds helpers only; it does not prove the target. They cover the piece root assigned to this
seat at 06:04Z, with interface `inventory-lemma14-bridge-interface-source-scout.md`:
* (I)  `indepFun_prod_sum`: `O a * T a` is independent of `∑ ij ∈ A, O ij * T ij` whenever `a ∉ A`,
  obtained from the frozen joint independence over `(Fin n × Fin m) ⊕ (Fin n × Fin m)`;
* (II) `mgf_sum_prod`: the MGF of the product sum factorises over any finite index set;
* (III) `integral_O`, `integral_O_mul_T`, `p_nonneg`, `p_le_one`: the expectation bridge;
* (IV) `mgf_prod_le`: `mgf (O ij * T ij) s ≤ exp (pO * p ij * (exp s - 1))` for every real `s`;
* (V)  `mgf_sum_le` and `mgf_centered_le`: the total bounds, with `S = ∑ ij, pO * p ij`.
Every hypothesis is copied from the frozen binders of the target. The file starts with the frozen
preamble, byte for byte. Its two internal helpers (`integrable_of_abs_le` and `exp_mul_le_of_mem_Icc`)
are prefixed by this piece's own namespace.
-/

namespace InventoryAnomaly.EW.ScoutBridge

/-- A bounded measurable real function on a finite measure space is integrable. -/
theorem integrable_of_abs_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {f : Ω → ℝ} (hf : Measurable f) (C : ℝ) (hC : ∀ ω, |f ω| ≤ C) : Integrable f P :=
  Integrable.mono' (integrable_const C) hf.aestronglyMeasurable
    (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]
      exact hC ω)

/-- Convexity of `exp`: on `[0, 1]`, `exp (s * x)` lies below the chord. -/
theorem exp_mul_le_of_mem_Icc (s x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp (s * x) ≤ 1 + x * (Real.exp s - 1) := by
  have h := convexOn_exp.2 (Set.mem_univ s) (Set.mem_univ 0) hx0 (sub_nonneg.mpr hx1)
    (by ring : x + (1 - x) = 1)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at h
  calc Real.exp (s * x) = Real.exp (x * s) := congrArg Real.exp (mul_comm s x)
    _ ≤ x * Real.exp s + (1 - x) := h
    _ = 1 + x * (Real.exp s - 1) := by ring

/-- (I) Block independence. -/
theorem indepFun_prod_sum {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n m : ℕ}
    (O T : Fin n × Fin m → Ω → ℝ)
    (hOm : ∀ ij, Measurable (O ij)) (hTm : ∀ ij, Measurable (T ij))
    (hind : iIndepFun (fun k : (Fin n × Fin m) ⊕ (Fin n × Fin m) => Sum.elim O T k) P)
    (a : Fin n × Fin m) (A : Finset (Fin n × Fin m)) (ha : a ∉ A) :
    IndepFun (fun ω => O a ω * T a ω) (fun ω => ∑ ij ∈ A, O ij ω * T ij ω) P := by
  classical
  have hZ : ∀ k : (Fin n × Fin m) ⊕ (Fin n × Fin m), Measurable (Sum.elim O T k) := by
    intro k
    cases k with
    | inl ij => exact hOm ij
    | inr ij => exact hTm ij
  let S : Finset ((Fin n × Fin m) ⊕ (Fin n × Fin m)) := {Sum.inl a, Sum.inr a}
  let B : Finset ((Fin n × Fin m) ⊕ (Fin n × Fin m)) := A.disjSum A
  have hdisj : Disjoint S B := by
    rw [Finset.disjoint_left]
    intro k hkS hkB
    have hk : k = Sum.inl a ∨ k = Sum.inr a := by simpa [S] using hkS
    rcases hk with rfl | rfl
    · exact ha (by simpa [B] using hkB)
    · exact ha (by simpa [B] using hkB)
  have h := hind.indepFun_finset S B hdisj hZ
  have hS1 : (Sum.inl a : (Fin n × Fin m) ⊕ (Fin n × Fin m)) ∈ S := by simp [S]
  have hS2 : (Sum.inr a : (Fin n × Fin m) ⊕ (Fin n × Fin m)) ∈ S := by simp [S]
  have hB1 : ∀ ij ∈ A, (Sum.inl ij : (Fin n × Fin m) ⊕ (Fin n × Fin m)) ∈ B := by
    intro ij hij
    simp [B, hij]
  have hB2 : ∀ ij ∈ A, (Sum.inr ij : (Fin n × Fin m) ⊕ (Fin n × Fin m)) ∈ B := by
    intro ij hij
    simp [B, hij]
  have hφ : Measurable (fun z : S → ℝ => z ⟨Sum.inl a, hS1⟩ * z ⟨Sum.inr a, hS2⟩) :=
    (measurable_pi_apply _).mul (measurable_pi_apply _)
  have hψ : Measurable (fun z : B → ℝ =>
      ∑ ij ∈ A.attach, z ⟨Sum.inl ij.1, hB1 ij.1 ij.2⟩ * z ⟨Sum.inr ij.1, hB2 ij.1 ij.2⟩) :=
    Finset.measurable_sum _ fun ij _ => (measurable_pi_apply _).mul (measurable_pi_apply _)
  have h3 : IndepFun
      ((fun z : S → ℝ => z ⟨Sum.inl a, hS1⟩ * z ⟨Sum.inr a, hS2⟩) ∘
        (fun ω (i : S) => Sum.elim O T i ω))
      ((fun z : B → ℝ =>
          ∑ ij ∈ A.attach, z ⟨Sum.inl ij.1, hB1 ij.1 ij.2⟩ * z ⟨Sum.inr ij.1, hB2 ij.1 ij.2⟩) ∘
        (fun ω (i : B) => Sum.elim O T i ω)) P :=
    h.comp hφ hψ
  have e1 : (fun ω => O a ω * T a ω)
      = (fun z : S → ℝ => z ⟨Sum.inl a, hS1⟩ * z ⟨Sum.inr a, hS2⟩) ∘
          (fun ω (i : S) => Sum.elim O T i ω) := by
    funext ω
    rfl
  have e2 : (fun ω => ∑ ij ∈ A, O ij ω * T ij ω)
      = (fun z : B → ℝ =>
          ∑ ij ∈ A.attach, z ⟨Sum.inl ij.1, hB1 ij.1 ij.2⟩ * z ⟨Sum.inr ij.1, hB2 ij.1 ij.2⟩) ∘
          (fun ω (i : B) => Sum.elim O T i ω) := by
    funext ω
    exact (Finset.sum_attach A (fun ij => O ij ω * T ij ω)).symm
  rw [e1, e2]
  exact h3

/-- (II) The MGF of the product sum factorises over every finite index set. -/
theorem mgf_sum_prod {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n m : ℕ} (O T : Fin n × Fin m → Ω → ℝ)
    (hOm : ∀ ij, Measurable (O ij)) (hTm : ∀ ij, Measurable (T ij))
    (hind : iIndepFun (fun k : (Fin n × Fin m) ⊕ (Fin n × Fin m) => Sum.elim O T k) P)
    (A : Finset (Fin n × Fin m)) (s : ℝ) :
    mgf (fun ω => ∑ ij ∈ A, O ij ω * T ij ω) P s
      = ∏ ij ∈ A, mgf (fun ω => O ij ω * T ij ω) P s := by
  classical
  induction A using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Finset.prod_empty, mgf_const, mul_zero, Real.exp_zero]
  | insert a A ha ih =>
    have hsplit : (fun ω => ∑ ij ∈ insert a A, O ij ω * T ij ω)
        = (fun ω => O a ω * T a ω) + (fun ω => ∑ ij ∈ A, O ij ω * T ij ω) := by
      funext ω
      simp only [Pi.add_apply, Finset.sum_insert ha]
    have hXa : Measurable (fun ω => O a ω * T a ω) := (hOm a).mul (hTm a)
    have hXA : Measurable (fun ω => ∑ ij ∈ A, O ij ω * T ij ω) :=
      Finset.measurable_sum A fun ij _ => (hOm ij).mul (hTm ij)
    rw [hsplit, Finset.prod_insert ha, ← ih,
      (indepFun_prod_sum P O T hOm hTm hind a A ha).mgf_add
        (hXa.const_mul s).exp.aestronglyMeasurable
        (hXA.const_mul s).exp.aestronglyMeasurable]

/-- (III) The mean of a `{0,1}`-valued `O ij` is `pO`. -/
theorem integral_O {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n m : ℕ} (pO : ℝ)
    (O : Fin n × Fin m → Ω → ℝ) (hOm : ∀ ij, Measurable (O ij))
    (hO01 : ∀ ij ω, O ij ω = 0 ∨ O ij ω = 1) (hOp : ∀ ij, P.real {ω | O ij ω = 1} = pO)
    (ij : Fin n × Fin m) : ∫ ω, O ij ω ∂P = pO := by
  have hmeas : MeasurableSet {ω | O ij ω = 1} := hOm ij (measurableSet_singleton 1)
  calc ∫ ω, O ij ω ∂P = ∫ ω, {ω | O ij ω = 1}.indicator 1 ω ∂P := by
        congr 1
        funext ω
        rcases hO01 ij ω with h | h
        · simp [h]
        · simp [h]
    _ = P.real {ω | O ij ω = 1} := integral_indicator_one hmeas
    _ = pO := hOp ij

/-- (III) The expectation bridge: `E[O ij * T ij] = pO * p ij`. -/
theorem integral_O_mul_T {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n m : ℕ}
    (pO : ℝ) (O T : Fin n × Fin m → Ω → ℝ) (p : Fin n × Fin m → ℝ)
    (hOm : ∀ ij, Measurable (O ij)) (hTm : ∀ ij, Measurable (T ij))
    (hind : iIndepFun (fun k : (Fin n × Fin m) ⊕ (Fin n × Fin m) => Sum.elim O T k) P)
    (hO01 : ∀ ij ω, O ij ω = 0 ∨ O ij ω = 1) (hOp : ∀ ij, P.real {ω | O ij ω = 1} = pO)
    (hTp : ∀ ij, ∫ ω, T ij ω ∂P = p ij) (ij : Fin n × Fin m) :
    ∫ ω, O ij ω * T ij ω ∂P = pO * p ij := by
  have hOT : IndepFun (O ij) (T ij) P :=
    hind.indepFun (i := Sum.inl ij) (j := Sum.inr ij) Sum.inl_ne_inr
  calc ∫ ω, O ij ω * T ij ω ∂P = (∫ ω, O ij ω ∂P) * (∫ ω, T ij ω ∂P) :=
        hOT.integral_fun_mul_eq_mul_integral (hOm ij).aestronglyMeasurable
          (hTm ij).aestronglyMeasurable
    _ = pO * p ij := by rw [integral_O P pO O hOm hO01 hOp ij, hTp ij]

/-- (III) The means `p ij` are nonnegative; this is derived, not assumed. -/
theorem p_nonneg {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n m : ℕ}
    (T : Fin n × Fin m → Ω → ℝ) (p : Fin n × Fin m → ℝ)
    (hT01 : ∀ ij ω, 0 ≤ T ij ω ∧ T ij ω ≤ 1) (hTp : ∀ ij, ∫ ω, T ij ω ∂P = p ij)
    (ij : Fin n × Fin m) : 0 ≤ p ij := by
  rw [← hTp ij]
  exact integral_nonneg fun ω => (hT01 ij ω).1

/-- (III) The means `p ij` are at most `1`. -/
theorem p_le_one {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n m : ℕ} (T : Fin n × Fin m → Ω → ℝ) (p : Fin n × Fin m → ℝ)
    (hTm : ∀ ij, Measurable (T ij))
    (hT01 : ∀ ij ω, 0 ≤ T ij ω ∧ T ij ω ≤ 1) (hTp : ∀ ij, ∫ ω, T ij ω ∂P = p ij)
    (ij : Fin n × Fin m) : p ij ≤ 1 := by
  have hint : Integrable (T ij) P := integrable_of_abs_le P (hTm ij) 1 fun ω => by
    rw [abs_of_nonneg (hT01 ij ω).1]
    exact (hT01 ij ω).2
  rw [← hTp ij]
  calc ∫ ω, T ij ω ∂P ≤ ∫ _, (1 : ℝ) ∂P :=
        integral_mono hint (integrable_const 1) fun ω => (hT01 ij ω).2
    _ = 1 := by simp

/-- (IV) Per-cell MGF bound, valid for every real `s`. -/
theorem mgf_prod_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n m : ℕ} (pO : ℝ) (O T : Fin n × Fin m → Ω → ℝ) (p : Fin n × Fin m → ℝ)
    (hOm : ∀ ij, Measurable (O ij)) (hTm : ∀ ij, Measurable (T ij))
    (hind : iIndepFun (fun k : (Fin n × Fin m) ⊕ (Fin n × Fin m) => Sum.elim O T k) P)
    (hO01 : ∀ ij ω, O ij ω = 0 ∨ O ij ω = 1) (hOp : ∀ ij, P.real {ω | O ij ω = 1} = pO)
    (hT01 : ∀ ij ω, 0 ≤ T ij ω ∧ T ij ω ≤ 1) (hTp : ∀ ij, ∫ ω, T ij ω ∂P = p ij)
    (ij : Fin n × Fin m) (s : ℝ) :
    mgf (fun ω => O ij ω * T ij ω) P s ≤ Real.exp (pO * p ij * (Real.exp s - 1)) := by
  have hX : Measurable (fun ω => O ij ω * T ij ω) := (hOm ij).mul (hTm ij)
  have hX01 : ∀ ω, 0 ≤ O ij ω * T ij ω ∧ O ij ω * T ij ω ≤ 1 := by
    intro ω
    obtain ⟨hT0, hT1⟩ := hT01 ij ω
    rcases hO01 ij ω with h | h
    · rw [h, zero_mul]
      exact ⟨le_refl 0, zero_le_one⟩
    · rw [h, one_mul]
      exact ⟨hT0, hT1⟩
  have hXint : Integrable (fun ω => O ij ω * T ij ω) P :=
    integrable_of_abs_le P hX 1 fun ω => by
      show |O ij ω * T ij ω| ≤ 1
      rw [abs_of_nonneg (hX01 ω).1]
      exact (hX01 ω).2
  have hgint : Integrable (fun ω => 1 + O ij ω * T ij ω * (Real.exp s - 1)) P :=
    (integrable_const 1).add (hXint.mul_const (Real.exp s - 1))
  have hmean : ∫ ω, O ij ω * T ij ω ∂P = pO * p ij :=
    integral_O_mul_T P pO O T p hOm hTm hind hO01 hOp hTp ij
  calc mgf (fun ω => O ij ω * T ij ω) P s
      = ∫ ω, Real.exp (s * (O ij ω * T ij ω)) ∂P := rfl
    _ ≤ ∫ ω, (1 + O ij ω * T ij ω * (Real.exp s - 1)) ∂P := by
        refine integral_mono_of_nonneg (ae_of_all _ fun ω => (Real.exp_pos _).le) hgint
          (ae_of_all _ fun ω => ?_)
        exact exp_mul_le_of_mem_Icc s _ (hX01 ω).1 (hX01 ω).2
    _ = 1 + pO * p ij * (Real.exp s - 1) := by
        rw [integral_add (integrable_const 1) (hXint.mul_const (Real.exp s - 1)), integral_const,
          integral_mul_const, hmean]
        simp
    _ ≤ Real.exp (pO * p ij * (Real.exp s - 1)) := by
        linarith [Real.add_one_le_exp (pO * p ij * (Real.exp s - 1))]

/-- (V) Total MGF bound for the frozen sum, valid for every real `s`. -/
theorem mgf_sum_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n m : ℕ} (pO : ℝ) (O T : Fin n × Fin m → Ω → ℝ) (p : Fin n × Fin m → ℝ)
    (hOm : ∀ ij, Measurable (O ij)) (hTm : ∀ ij, Measurable (T ij))
    (hind : iIndepFun (fun k : (Fin n × Fin m) ⊕ (Fin n × Fin m) => Sum.elim O T k) P)
    (hO01 : ∀ ij ω, O ij ω = 0 ∨ O ij ω = 1) (hOp : ∀ ij, P.real {ω | O ij ω = 1} = pO)
    (hT01 : ∀ ij ω, 0 ≤ T ij ω ∧ T ij ω ≤ 1) (hTp : ∀ ij, ∫ ω, T ij ω ∂P = p ij) (s : ℝ) :
    mgf (fun ω => ∑ ij, O ij ω * T ij ω) P s
      ≤ Real.exp ((∑ ij, pO * p ij) * (Real.exp s - 1)) := by
  rw [mgf_sum_prod P O T hOm hTm hind Finset.univ s]
  calc ∏ ij, mgf (fun ω => O ij ω * T ij ω) P s
      ≤ ∏ ij, Real.exp (pO * p ij * (Real.exp s - 1)) :=
        Finset.prod_le_prod (fun _ _ => mgf_nonneg)
          (fun ij _ => mgf_prod_le P pO O T p hOm hTm hind hO01 hOp hT01 hTp ij s)
    _ = Real.exp ((∑ ij, pO * p ij) * (Real.exp s - 1)) := by
        rw [← Real.exp_sum, Finset.sum_mul]

/-- (V') Centred total MGF bound, for Chernoff bounds in both directions. -/
theorem mgf_centered_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n m : ℕ} (pO : ℝ) (O T : Fin n × Fin m → Ω → ℝ) (p : Fin n × Fin m → ℝ)
    (hOm : ∀ ij, Measurable (O ij)) (hTm : ∀ ij, Measurable (T ij))
    (hind : iIndepFun (fun k : (Fin n × Fin m) ⊕ (Fin n × Fin m) => Sum.elim O T k) P)
    (hO01 : ∀ ij ω, O ij ω = 0 ∨ O ij ω = 1) (hOp : ∀ ij, P.real {ω | O ij ω = 1} = pO)
    (hT01 : ∀ ij ω, 0 ≤ T ij ω ∧ T ij ω ≤ 1) (hTp : ∀ ij, ∫ ω, T ij ω ∂P = p ij) (s : ℝ) :
    mgf (fun ω => ∑ ij, O ij ω * T ij ω - ∑ ij, pO * p ij) P s
      ≤ Real.exp ((∑ ij, pO * p ij) * (Real.exp s - 1 - s)) := by
  have h1 : mgf (fun ω => ∑ ij, O ij ω * T ij ω - ∑ ij, pO * p ij) P s
      = mgf (fun ω => ∑ ij, O ij ω * T ij ω) P s * Real.exp (s * -(∑ ij, pO * p ij)) := by
    have h := mgf_add_const (μ := P) (t := s) (X := fun ω => ∑ ij, O ij ω * T ij ω)
      (-(∑ ij, pO * p ij))
    simpa only [sub_eq_add_neg] using h
  rw [h1]
  calc mgf (fun ω => ∑ ij, O ij ω * T ij ω) P s * Real.exp (s * -(∑ ij, pO * p ij))
      ≤ Real.exp ((∑ ij, pO * p ij) * (Real.exp s - 1)) * Real.exp (s * -(∑ ij, pO * p ij)) :=
        mul_le_mul_of_nonneg_right
          (mgf_sum_le P pO O T p hOm hTm hind hO01 hOp hT01 hTp s) (Real.exp_pos _).le
    _ = Real.exp ((∑ ij, pO * p ij) * (Real.exp s - 1 - s)) := by
        rw [← Real.exp_add]
        congr 1
        ring

end InventoryAnomaly.EW.ScoutBridge

namespace InventoryAnomaly.EW.Glue

theorem centered_measurable {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ} (pO : ℝ)
    (O T : Fin n × Fin m → Ω → ℝ) (p : Fin n × Fin m → ℝ)
    (hOm : ∀ ij, Measurable (O ij)) (hTm : ∀ ij, Measurable (T ij)) :
    Measurable (fun ω => ∑ ij, O ij ω * T ij ω - ∑ ij, pO * p ij) := by
  exact (Finset.measurable_sum Finset.univ (fun ij _ => (hOm ij).mul (hTm ij))).sub
    measurable_const

theorem centered_abs_le {Ω : Type*} {n m : ℕ} (pO : ℝ)
    (O T : Fin n × Fin m → Ω → ℝ) (p : Fin n × Fin m → ℝ)
    (hO01 : ∀ ij ω, O ij ω = 0 ∨ O ij ω = 1)
    (hT01 : ∀ ij ω, 0 ≤ T ij ω ∧ T ij ω ≤ 1) (ω : Ω) :
    |∑ ij, O ij ω * T ij ω - ∑ ij, pO * p ij|
      ≤ (∑ _ij : Fin n × Fin m, (1 : ℝ)) + |∑ ij, pO * p ij| := by
  have hprod : ∀ ij : Fin n × Fin m,
      0 ≤ O ij ω * T ij ω ∧ O ij ω * T ij ω ≤ 1 := by
    intro ij
    rcases hO01 ij ω with hO | hO
    · simp [hO]
    · simpa only [hO, one_mul] using hT01 ij ω
  have hsum_nonneg : (0 : ℝ) ≤ ∑ ij, O ij ω * T ij ω := by
    exact Finset.sum_nonneg (fun ij _ => (hprod ij).1)
  have hsum_le : (∑ ij, O ij ω * T ij ω) ≤
      ∑ _ij : Fin n × Fin m, (1 : ℝ) := by
    exact Finset.sum_le_sum (fun ij _ => (hprod ij).2)
  calc
    |∑ ij, O ij ω * T ij ω - ∑ ij, pO * p ij|
        ≤ |∑ ij, O ij ω * T ij ω| + |∑ ij, pO * p ij| := abs_sub _ _
    _ = (∑ ij, O ij ω * T ij ω) + |∑ ij, pO * p ij| := by
      rw [abs_of_nonneg hsum_nonneg]
    _ ≤ (∑ _ij : Fin n × Fin m, (1 : ℝ)) + |∑ ij, pO * p ij| :=
      add_le_add hsum_le le_rfl

theorem S_nonneg {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n m : ℕ} (pO : ℝ)
    (T : Fin n × Fin m → Ω → ℝ) (p : Fin n × Fin m → ℝ) (hpO : 0 ≤ pO)
    (hT01 : ∀ ij ω, 0 ≤ T ij ω ∧ T ij ω ≤ 1) (hTp : ∀ ij, ∫ ω, T ij ω ∂P = p ij) :
    0 ≤ ∑ ij, pO * p ij := by
  classical
  apply Finset.sum_nonneg
  intro ij _
  apply mul_nonneg hpO
  rw [← hTp ij]
  exact integral_nonneg fun ω => (hT01 ij ω).1

theorem nm_eq_one_or_two_le {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    (n : ℝ) * m = 1 ∨ 2 ≤ (n : ℝ) * m := by
  have hnm : 0 < n * m := Nat.mul_pos hn hm
  have hcases : n * m = 1 ∨ 2 ≤ n * m := by omega
  rcases hcases with h | h
  · left
    exact_mod_cast h
  · right
    exact_mod_cast h

end InventoryAnomaly.EW.Glue

namespace InventoryAnomaly.EW.ConcAP

/-- `exp (s * Y)` is integrable when `Y` is measurable and bounded. -/
theorem integrable_exp_mul_of_abs_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] (Y : Ω → ℝ) (hY : Measurable Y) (B : ℝ) (hB : ∀ ω, |Y ω| ≤ B) (s : ℝ) :
    Integrable (fun ω => Real.exp (s * Y ω)) P := by
  refine (integrable_const (Real.exp (|s| * B))).mono'
    (hY.const_mul s).exp.aestronglyMeasurable (ae_of_all P (fun ω => ?_))
  have hsY : s * Y ω ≤ |s| * B :=
    calc
      s * Y ω ≤ |s * Y ω| := le_abs_self _
      _ = |s| * |Y ω| := abs_mul s (Y ω)
      _ ≤ |s| * B := mul_le_mul_of_nonneg_left (hB ω) (abs_nonneg s)
  exact (Real.norm_of_nonneg (Real.exp_pos (s * Y ω)).le).trans_le (Real.exp_le_exp.mpr hsY)

/-- `exp t - 1 - t ≤ t ^ 2` for `|t| ≤ 1`. -/
private lemma concAP_exp_sub_one_sub_le {t : ℝ} (ht : |t| ≤ 1) :
    Real.exp t - 1 - t ≤ t ^ 2 :=
  (le_abs_self _).trans (Real.abs_exp_sub_one_sub_id_le ht)

/-- The centred moment generating function bound, specialised to `|t| ≤ 1`. -/
private lemma concAP_mgf_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y : Ω → ℝ)
    (S : ℝ) (hS : 0 ≤ S) (hmgf : ∀ s : ℝ, mgf Y P s ≤ Real.exp (S * (Real.exp s - 1 - s)))
    {t : ℝ} (ht : |t| ≤ 1) : mgf Y P t ≤ Real.exp (S * t ^ 2) :=
  (hmgf t).trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (concAP_exp_sub_one_sub_le ht) hS))

/-- Upper Chernoff tail for `s ∈ [0, 1]`. -/
private lemma concAP_upper {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (S : ℝ) (hS : 0 ≤ S)
    (hint : ∀ s : ℝ, Integrable (fun ω => Real.exp (s * Y ω)) P)
    (hmgf : ∀ s : ℝ, mgf Y P s ≤ Real.exp (S * (Real.exp s - 1 - s)))
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (a : ℝ) :
    P.real {ω | a ≤ Y ω} ≤ Real.exp (-s * a + S * s ^ 2) :=
  calc
    P.real {ω | a ≤ Y ω} ≤ Real.exp (-s * a) * mgf Y P s :=
      measure_ge_le_exp_mul_mgf a hs0 (hint s)
    _ ≤ Real.exp (-s * a) * Real.exp (S * s ^ 2) :=
      mul_le_mul_of_nonneg_left
        (concAP_mgf_le P Y S hS hmgf (abs_le.mpr ⟨by linarith, hs1⟩)) (Real.exp_pos _).le
    _ = Real.exp (-s * a + S * s ^ 2) := (Real.exp_add _ _).symm

/-- Lower Chernoff tail for `s ∈ [0, 1]`, through the moment generating function at `-s`. -/
private lemma concAP_lower {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (S : ℝ) (hS : 0 ≤ S)
    (hint : ∀ s : ℝ, Integrable (fun ω => Real.exp (s * Y ω)) P)
    (hmgf : ∀ s : ℝ, mgf Y P s ≤ Real.exp (S * (Real.exp s - 1 - s)))
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (a : ℝ) :
    P.real {ω | Y ω ≤ -a} ≤ Real.exp (-s * a + S * s ^ 2) :=
  calc
    P.real {ω | Y ω ≤ -a} ≤ Real.exp (-(-s) * (-a)) * mgf Y P (-s) :=
      measure_le_le_exp_mul_mgf (-a) (by linarith) (hint (-s))
    _ ≤ Real.exp (-(-s) * (-a)) * Real.exp (S * (-s) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (concAP_mgf_le P Y S hS hmgf (abs_le.mpr ⟨by linarith, by linarith⟩))
        (Real.exp_pos _).le
    _ = Real.exp (-s * a + S * s ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Core estimate with `L ≥ log 2` in place of `log N`: the failure probability is at most
`2 exp (-5 L) ≤ exp (-L)`. The exponent `s` is `√(L / S)` when `L ≤ S` and `1` otherwise. -/
private lemma concAP_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (S L : ℝ) (hS : 0 ≤ S) (hL : Real.log 2 ≤ L)
    (hint : ∀ s : ℝ, Integrable (fun ω => Real.exp (s * Y ω)) P)
    (hmgf : ∀ s : ℝ, mgf Y P s ≤ Real.exp (S * (Real.exp s - 1 - s))) :
    1 - Real.exp (-L) ≤ P.real {ω | |Y ω| ≤ 6 * (Real.sqrt (S * L) + L)} := by
  have hL0 : 0 < L := lt_of_lt_of_le (Real.log_pos (by norm_num)) hL
  obtain ⟨s, hs0, hs1, hquad, hkey⟩ : ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ S * s ^ 2 ≤ L ∧
      L ≤ s * Real.sqrt (S * L) + s * L := by
    rcases le_or_gt L S with hLS | hSL
    · have hSpos : 0 < S := lt_of_lt_of_le hL0 hLS
      refine ⟨Real.sqrt (L / S), Real.sqrt_nonneg _, ?_, ?_, ?_⟩
      · exact Real.sqrt_le_one.mpr ((div_le_one hSpos).mpr hLS)
      · have h : S * Real.sqrt (L / S) ^ 2 = L := by
          rw [Real.sq_sqrt (div_nonneg hL0.le hS), mul_comm, div_mul_cancel₀ L hSpos.ne']
        exact h.le
      · have h1 : Real.sqrt (L / S) * Real.sqrt (S * L) = L := by
          rw [← Real.sqrt_mul (div_nonneg hL0.le hS),
            show L / S * (S * L) = L * L by rw [← mul_assoc, div_mul_cancel₀ L hSpos.ne'],
            Real.sqrt_mul_self hL0.le]
        have h2 : 0 ≤ Real.sqrt (L / S) * L := mul_nonneg (Real.sqrt_nonneg _) hL0.le
        linarith
    · refine ⟨1, zero_le_one, le_refl 1, by linarith, ?_⟩
      have h := Real.sqrt_nonneg (S * L)
      linarith
  have hexp : -s * (6 * (Real.sqrt (S * L) + L)) + S * s ^ 2 ≤ -5 * L := by
    linarith
  have hup := concAP_upper P Y S hS hint hmgf hs0 hs1 (6 * (Real.sqrt (S * L) + L))
  have hlo := concAP_lower P Y S hS hint hmgf hs0 hs1 (6 * (Real.sqrt (S * L) + L))
  have hexp5 : Real.exp (-s * (6 * (Real.sqrt (S * L) + L)) + S * s ^ 2) ≤ Real.exp (-5 * L) :=
    Real.exp_le_exp.mpr hexp
  have h4L : 2 ≤ Real.exp (4 * L) := by
    have h1 := Real.add_one_le_exp (4 * L)
    have h2 := Real.log_two_gt_d9
    linarith
  have htot : 2 * Real.exp (-5 * L) ≤ Real.exp (-L) :=
    calc
      2 * Real.exp (-5 * L) ≤ Real.exp (4 * L) * Real.exp (-5 * L) :=
        mul_le_mul_of_nonneg_right h4L (Real.exp_pos _).le
      _ = Real.exp (-L) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hsub : {ω | |Y ω| ≤ 6 * (Real.sqrt (S * L) + L)}ᶜ ⊆
      {ω | 6 * (Real.sqrt (S * L) + L) ≤ Y ω} ∪ {ω | Y ω ≤ -(6 * (Real.sqrt (S * L) + L))} := by
    intro ω hω
    have hω' : ¬ (|Y ω| ≤ 6 * (Real.sqrt (S * L) + L)) := hω
    rcases lt_abs.mp (not_le.mp hω') with h | h
    · exact Or.inl h.le
    · exact Or.inr (show Y ω ≤ -(6 * (Real.sqrt (S * L) + L)) by linarith)
  have hcompl : P.real {ω | |Y ω| ≤ 6 * (Real.sqrt (S * L) + L)}ᶜ ≤
      P.real {ω | 6 * (Real.sqrt (S * L) + L) ≤ Y ω} +
        P.real {ω | Y ω ≤ -(6 * (Real.sqrt (S * L) + L))} :=
    (measureReal_mono (μ := P) hsub).trans (measureReal_union_le _ _)
  have huniv : (1 : ℝ) ≤ P.real {ω | |Y ω| ≤ 6 * (Real.sqrt (S * L) + L)} +
      P.real {ω | |Y ω| ≤ 6 * (Real.sqrt (S * L) + L)}ᶜ :=
    calc
      (1 : ℝ) = P.real Set.univ := probReal_univ.symm
      _ = P.real ({ω | |Y ω| ≤ 6 * (Real.sqrt (S * L) + L)} ∪
          {ω | |Y ω| ≤ 6 * (Real.sqrt (S * L) + L)}ᶜ) := by rw [Set.union_compl_self]
      _ ≤ P.real {ω | |Y ω| ≤ 6 * (Real.sqrt (S * L) + L)} +
          P.real {ω | |Y ω| ≤ 6 * (Real.sqrt (S * L) + L)}ᶜ := measureReal_union_le _ _
  linarith

/-- Two-sided concentration with the constant `6`, from a Poisson-type centred moment generating
function bound. `N = 1` is trivial; for `N ≥ 2` the failure probability is at most
`2 N⁻⁵ ≤ N⁻¹`. -/
theorem prob_abs_le_of_mgf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (S N : ℝ) (hS : 0 ≤ S) (hN : N = 1 ∨ 2 ≤ N)
    (hint : ∀ s : ℝ, Integrable (fun ω => Real.exp (s * Y ω)) P)
    (hmgf : ∀ s : ℝ, mgf Y P s ≤ Real.exp (S * (Real.exp s - 1 - s))) :
    1 - 1 / N ≤ P.real {ω | |Y ω| ≤ 6 * (Real.sqrt (S * Real.log N) + Real.log N)} := by
  rcases hN with rfl | hN2
  · rw [div_one, sub_self]
    exact measureReal_nonneg
  · have hNpos : 0 < N := by linarith
    have hL : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN2
    have hcore := concAP_core P Y S (Real.log N) hS hL hint hmgf
    have hEL : Real.exp (-Real.log N) = 1 / N := by
      rw [Real.exp_neg, Real.exp_log hNpos, one_div]
    rw [hEL] at hcore
    exact hcore

end InventoryAnomaly.EW.ConcAP

namespace InventoryAnomaly.EW

theorem lemma_14 : ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {n m : ℕ}
      (pO : ℝ) (O T : Fin n × Fin m → Ω → ℝ) (p : Fin n × Fin m → ℝ),
      0 < n → 0 < m → 0 ≤ pO → pO ≤ 1 →
      (∀ ij, Measurable (O ij)) → (∀ ij, Measurable (T ij)) →
      iIndepFun (fun k : (Fin n × Fin m) ⊕ (Fin n × Fin m) => Sum.elim O T k) P →
      (∀ ij ω, O ij ω = 0 ∨ O ij ω = 1) → (∀ ij, P.real {ω | O ij ω = 1} = pO) →
      (∀ ij ω, 0 ≤ T ij ω ∧ T ij ω ≤ 1) → (∀ ij, ∫ ω, T ij ω ∂P = p ij) →
      1 - 1 / ((n : ℝ) * m) ≤ P.real {ω | |∑ ij, O ij ω * T ij ω - ∑ ij, pO * p ij| ≤
        C * (Real.sqrt ((∑ ij, pO * p ij) * Real.log (m * n)) + Real.log (m * n))} := by
  refine ⟨6, by norm_num, ?_⟩
  intro Ω _ P _ n m pO O T p hn hm hpO0 hpO1 hOm hTm hind hO01 hOp hT01 hTp
  have hY := Glue.centered_measurable pO O T p hOm hTm
  have key := ConcAP.prob_abs_le_of_mgf P (fun ω => ∑ ij, O ij ω * T ij ω - ∑ ij, pO * p ij)
    (∑ ij, pO * p ij) ((n : ℝ) * m) (Glue.S_nonneg P pO T p hpO0 hT01 hTp)
    (Glue.nm_eq_one_or_two_le hn hm)
    (fun s => ConcAP.integrable_exp_mul_of_abs_le P _ hY _ (Glue.centered_abs_le pO O T p hO01 hT01) s)
    (fun s => ScoutBridge.mgf_centered_le P pO O T p hOm hTm hind hO01 hOp hT01 hTp s)
  have hlog : Real.log ((n : ℝ) * m) = Real.log ((m : ℝ) * n) := by rw [mul_comm]
  rw [hlog] at key
  exact key

end InventoryAnomaly.EW

end Prove2SwarmSubmission

open MeasureTheory ProbabilityTheory
open scoped NNReal
theorem solution : ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {n m : ℕ}
      (pO : ℝ) (O T : Fin n × Fin m → Ω → ℝ) (p : Fin n × Fin m → ℝ),
      0 < n → 0 < m → 0 ≤ pO → pO ≤ 1 →
      (∀ ij, Measurable (O ij)) → (∀ ij, Measurable (T ij)) →
      iIndepFun (fun k : (Fin n × Fin m) ⊕ (Fin n × Fin m) => Sum.elim O T k) P →
      (∀ ij ω, O ij ω = 0 ∨ O ij ω = 1) → (∀ ij, P.real {ω | O ij ω = 1} = pO) →
      (∀ ij ω, 0 ≤ T ij ω ∧ T ij ω ≤ 1) → (∀ ij, ∫ ω, T ij ω ∂P = p ij) →
      1 - 1 / ((n : ℝ) * m) ≤ P.real {ω | |∑ ij, O ij ω * T ij ω - ∑ ij, pO * p ij| ≤
        C * (Real.sqrt ((∑ ij, pO * p ij) * Real.log (m * n)) + Real.log (m * n))} := by
  exact Prove2SwarmSubmission.InventoryAnomaly.EW.lemma_14 
