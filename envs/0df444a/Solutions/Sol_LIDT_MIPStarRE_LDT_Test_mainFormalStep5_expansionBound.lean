-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Test.mainFormalStep5_expansionBound
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:52:16.153274+00:00
-- url     : https://prove2.me/submissions/c9424587-bff0-41d7-aa38-ab4e0f198b67

-- Generated proof for MIPStarRE.LDT.Test.mainFormalStep5_expansionBound.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFUniformAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_PolynomialAgreement
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_SchwartzZippelStep
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.RingTheory.MvPolynomial.Basic

namespace LIDT

/- Source helpers from MIPStarRE/LDT/Test/SchwartzZippelStep.lean. -/
/-!
# `mainFormal` Step 5 — Schwartz--Zippel self-consistency handoff

This file isolates the paper's Step 5 bridge in
`references/ldt-paper/inductive_step.tex`, lines 119--133.  The algebraic
expansion/reindexing from evaluated consistency to the full-polynomial
consistency defect is proved here, and the genuinely Schwartz--Zippel part is
provided by the shared tensor bound
`Preliminaries.polynomialCollisionMass_le_mdq`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace Test

open Classical in
private lemma qBipartiteMatchMass_postprocess_eq_pair_sum
    {α β ιA ιB : Type*} [Fintype α] [Fintype β]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) (A : SubMeas α ιA) (B : SubMeas α ιB)
    (f : α → β) :
    qBipartiteMatchMass ψ (postprocess A f) (postprocess B f) =
      ∑ aa : α × α,
        if f aa.1 = f aa.2 then
          ev ψ (opTensor (A.outcome aa.1) (B.outcome aa.2))
        else 0 := by
  classical
  unfold qBipartiteMatchMass
  calc
    ∑ b : β, ev ψ (opTensor ((postprocess A f).outcome b) ((postprocess B f).outcome b))
      = ∑ b : β, ∑ aa : α × α,
          if f aa.1 = b ∧ f aa.2 = b then
            ev ψ (opTensor (A.outcome aa.1) (B.outcome aa.2))
          else 0 := by
            refine Finset.sum_congr rfl ?_
            intro b _
            simp only [postprocess, Finset.sum_filter, opTensor_sum_left_univ,
              opTensor_sum_right_univ, ev_sum]
            rw [Fintype.sum_prod_type]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro a _
            refine Finset.sum_congr rfl ?_
            intro x _
            by_cases ha : f a = b <;> by_cases hx : f x = b <;>
              simp [ha, hx, opTensor, ev_zero]
    _ = ∑ aa : α × α, ∑ b : β,
          if f aa.1 = b ∧ f aa.2 = b then
            ev ψ (opTensor (A.outcome aa.1) (B.outcome aa.2))
          else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ aa : α × α,
        if f aa.1 = f aa.2 then
          ev ψ (opTensor (A.outcome aa.1) (B.outcome aa.2))
        else 0 := by
            refine Finset.sum_congr rfl ?_
            intro aa _
            by_cases h : f aa.1 = f aa.2
            · rw [Finset.sum_eq_single (f aa.1)]
              · simp [h]
              · intro b _ hb
                have hb1 : f aa.1 ≠ b := by
                  intro hEq
                  exact hb hEq.symm
                by_cases h1 : f aa.1 = b
                · exact (hb1 h1).elim
                · simp [h1]
              · simp
            · have hzero : (∑ b : β,
                  if f aa.1 = b ∧ f aa.2 = b then
                    ev ψ (opTensor (A.outcome aa.1) (B.outcome aa.2)) else 0) = 0 := by
                refine Finset.sum_eq_zero ?_
                intro b _
                by_cases h1 : f aa.1 = b
                · have h2 : f aa.2 ≠ b := by
                    intro h2
                    exact h (h1.trans h2.symm)
                  simp [h1, h2]
                · simp [h1]
              simp [h, hzero]



private lemma qBipartiteMatchMass_postprocess_eq_add_localCollision
    {α β ιA ιB : Type*} [Fintype α] [Fintype β]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) (A : SubMeas α ιA) (B : SubMeas α ιB)
    (f : α → β) :
    qBipartiteMatchMass ψ (postprocess A f) (postprocess B f) =
      qBipartiteMatchMass ψ A B + localCollisionMass ψ A B f := by
  classical
  have hdiag :
      qBipartiteMatchMass ψ A B =
        ∑ aa : α × α,
          if aa.1 = aa.2 then
            ev ψ (opTensor (A.outcome aa.1) (B.outcome aa.2))
          else 0 := by
    unfold qBipartiteMatchMass
    symm
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl ?_
    intro a _
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      have hb' : ¬ a = b := by
        intro hEq
        exact hb hEq.symm
      simp [hb']
    · simp
  rw [qBipartiteMatchMass_postprocess_eq_pair_sum]
  rw [hdiag]
  unfold localCollisionMass
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro aa _
  by_cases hEq : aa.1 = aa.2
  · simp [hEq]
  · by_cases hf : f aa.1 = f aa.2 <;> simp [hEq, hf]

private lemma qBipartiteConsDefect_le_postprocess_add_localCollision
    {α β ιA ιB : Type*} [Fintype α] [Fintype β]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) (A : SubMeas α ιA) (B : SubMeas α ιB)
    (f : α → β) :
    qBipartiteConsDefect ψ A B ≤
      qBipartiteConsDefect ψ (postprocess A f) (postprocess B f) +
        localCollisionMass ψ A B f := by
  classical
  let c := localCollisionMass ψ A B f
  have hc : 0 ≤ c := by
    dsimp [c, localCollisionMass]
    refine Finset.sum_nonneg ?_
    intro aa _
    apply mul_nonneg
    · by_cases hEq : aa.1 = aa.2
      · simp [hEq]
      · by_cases hf : f aa.1 = f aa.2
        · simp [hEq, hf]
        · simp [hEq, hf]
    · exact ev_nonneg_of_psd ψ _
        (opTensor_nonneg (A.outcome_pos aa.1) (B.outcome_pos aa.2))
  have hmatch := qBipartiteMatchMass_postprocess_eq_add_localCollision ψ A B f
  unfold qBipartiteConsDefect
  simp only [postprocess_total]
  rw [hmatch]
  change max 0 (ev ψ (opTensor A.total B.total) - qBipartiteMatchMass ψ A B) ≤
    max 0 (ev ψ (opTensor A.total B.total) -
      (qBipartiteMatchMass ψ A B + c)) + c
  apply max_le
  · exact add_nonneg (le_max_left 0 _) hc
  · have hle :
        ev ψ (opTensor A.total B.total) - qBipartiteMatchMass ψ A B - c ≤
          max 0 (ev ψ (opTensor A.total B.total) -
            (qBipartiteMatchMass ψ A B + c)) := by
      have hrewrite :
          ev ψ (opTensor A.total B.total) - qBipartiteMatchMass ψ A B - c =
            ev ψ (opTensor A.total B.total) - (qBipartiteMatchMass ψ A B + c) := by
        rw [sub_add_eq_sub_sub]
      rw [hrewrite]
      exact le_max_right 0 _
    linarith

private lemma avg_localCollisionMass_eval_eq_polynomialCollisionMass
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (params : Parameters) [FieldModel params.q]
    (ψ : QuantumState (ιA × ιB))
    (Left : SubMeas (Polynomial params) ιA) (Right : SubMeas (Polynomial params) ιB) :
    avgOver (uniformDistribution (Point params))
      (fun u => localCollisionMass ψ Left Right (fun g : Polynomial params => g u)) =
      Preliminaries.polynomialCollisionMass params ψ Left Right := by
  classical
  unfold localCollisionMass Preliminaries.polynomialCollisionMass
  rw [avgOver_sum]
  refine Finset.sum_congr rfl ?_
  intro gg _
  by_cases hEq : gg.1 = gg.2
  · simp [hEq, avgOver_zero]
  · simp only [hEq, ite_false]
    rw [avgOver_mul_const]
    congr 1
    apply avgOver_congr
    intro u
    by_cases h : gg.1 u = gg.2 u <;> simp [h]









end Test

end MIPStarRE.LDT

end

end LIDT

open LIDT
/-!
# `mainFormal` Step 5 — Schwartz--Zippel self-consistency handoff

This file isolates the paper's Step 5 bridge in
`references/ldt-paper/inductive_step.tex`, lines 119--133.  The algebraic
expansion/reindexing from evaluated consistency to the full-polynomial
consistency defect is proved here, and the genuinely Schwartz--Zippel part is
provided by the shared tensor bound
`Preliminaries.polynomialCollisionMass_le_mdq`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT

open LIDT.MIPStarRE.LDT.Test

theorem solution
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ιA × ιB))
    (Left : _root_.LIDT.MIPStarRE.LDT.SubMeas (_root_.LIDT.MIPStarRE.LDT.Polynomial params) ιA) (Right : _root_.LIDT.MIPStarRE.LDT.SubMeas (_root_.LIDT.MIPStarRE.LDT.Polynomial params) ιB) :
    _root_.LIDT.MIPStarRE.LDT.Test.MainFormalStep5ExpansionBound params ψ Left Right := by
  classical
  unfold _root_.LIDT.MIPStarRE.LDT.Test.MainFormalStep5ExpansionBound
  calc
    _root_.LIDT.MIPStarRE.LDT.bipartiteConsError ψ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
        (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily Left) (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily Right)
      = _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect ψ Left Right := by
          simp [_root_.LIDT.MIPStarRE.LDT.bipartiteConsError, _root_.LIDT.MIPStarRE.LDT.avgOver, _root_.LIDT.MIPStarRE.LDT.uniformDistribution, _root_.LIDT.MIPStarRE.LDT.constSubMeasFamily]
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params))
          (fun _ : _root_.LIDT.MIPStarRE.LDT.Point params => _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect ψ Left Right) := by
          exact (_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_const (α := _root_.LIDT.MIPStarRE.LDT.Point params)
            (c := _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect ψ Left Right)).symm
    _ ≤ _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params))
          (fun u =>
            _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect ψ (_root_.LIDT.MIPStarRE.LDT.evaluateAt params u Left) (_root_.LIDT.MIPStarRE.LDT.evaluateAt params u Right) +
              localCollisionMass ψ Left Right (fun g : _root_.LIDT.MIPStarRE.LDT.Polynomial params => g u)) := by
          apply _root_.LIDT.MIPStarRE.LDT.avgOver_mono
          intro u
          exact qBipartiteConsDefect_le_postprocess_add_localCollision ψ Left Right
            (fun g : _root_.LIDT.MIPStarRE.LDT.Polynomial params => g u)
    _ = _root_.LIDT.MIPStarRE.LDT.bipartiteConsError ψ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params))
          (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params Left)
          (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params Right) +
        _root_.LIDT.MIPStarRE.LDT.Preliminaries.polynomialCollisionMass params ψ Left Right := by
          rw [_root_.LIDT.MIPStarRE.LDT.avgOver_add]
          change _root_.LIDT.MIPStarRE.LDT.bipartiteConsError ψ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params))
              (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params Left)
              (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params Right) +
            _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params))
              (fun u => localCollisionMass ψ Left Right (fun g : _root_.LIDT.MIPStarRE.LDT.Polynomial params => g u)) =
            _root_.LIDT.MIPStarRE.LDT.bipartiteConsError ψ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params))
              (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params Left)
              (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params Right) +
            _root_.LIDT.MIPStarRE.LDT.Preliminaries.polynomialCollisionMass params ψ Left Right
          rw [avg_localCollisionMass_eval_eq_polynomialCollisionMass]
