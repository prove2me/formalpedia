-- Prove2me | solution 1 for OAI.GAD.entropy_qubit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:33:30.599978+00:00
-- url     : https://prove2.me/submissions/d0127049-bbf0-4993-ad93-23121406bc82

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/PhaseStates.lean:L12-L38
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.entropy_qubit. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Pinching
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_GramMatrices
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ScalarDeficit
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ThermalEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_OutputConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_TensorEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PureRecursion
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_StateEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_EntropyContinuity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_BlockFactors
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Naimark
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_HolevoInformation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_OutputEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_EnsembleBounds
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PhaseStates

-- ---- from OAI.InformationTheory.AmplitudeDamping.SpectralEntropy ----
namespace OAI

universe u_1

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

variable {ι : Type u_1} [Fintype ι] [DecidableEq ι]

/-- Trace invariance under a unitary change of basis. -/
theorem trace_unitary_conj (U : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) :
    (Unitary.conjStarAlgAut ℂ _ U A).trace = A.trace := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle]
  simp

/-- Spectral trace for any function on the finite real spectrum. -/
theorem trace_cfc_eq {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, (f (hA.eigenvalues i) : ℂ) := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, trace_unitary_conj]
  simp [Matrix.trace_diagonal, Function.comp_def]

theorem entropy_eq_sum {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    entropy A = ∑ i, Real.negMulLog (hA.eigenvalues i) := by
  simp [entropy, trace_cfc_eq hA]

end GAD

end

end OAI

-- ---- from OAI.InformationTheory.AmplitudeDamping.PhaseStates ----
namespace OAI

noncomputable section

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

/-- Entropy of any Hermitian trace-one two-level matrix, expressed through its determinant. -/
theorem entropy_qubit {P : Matrix (Fin 2) (Fin 2) ℂ} (hP : P.IsHermitian)
    (htr : P.trace=1) : entropy P = g P.det.re := by
  let a := hP.eigenvalues 0
  let b := hP.eigenvalues 1
  have hab : a+b=1 := by
    have h := congrArg Complex.re (hP.trace_eq_sum_eigenvalues.symm.trans htr)
    simpa [Fin.sum_univ_two,a,b] using h
  have hd : P.det.re=a*b := by
    rw [hP.det_eq_prod_eigenvalues,Fin.prod_univ_two]
    simp [a,b]
  have he : entropy P=Real.negMulLog a+Real.negMulLog b := by
    rw [entropy_eq_sum hP,Fin.sum_univ_two]
  have hdisc : 1-4*P.det.re=(a-b)^2 := by rw [hd]; nlinarith only [hab]
  rw [he,g,hdisc,Real.sqrt_sq_eq_abs]
  by_cases h : b ≤ a
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    have ht : (1+(a-b))/2=a := by linarith
    rw [ht,Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    congr 1
    congr 1
    linarith
  · rw [abs_of_neg (sub_neg.mpr (lt_of_not_ge h))]
    have ht : (1+ -(a-b))/2=b := by linarith
    rw [ht,Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    have ht' : 1-b=a := by linarith
    rw [ht']; ring

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

end GAD

end

end OAI

-- ---- platform node ----
open OAI OAI.GAD
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix


theorem solution : type_of% @_root_.OAI.GAD.entropy_qubit := @_root_.OAI.GAD.entropy_qubit
