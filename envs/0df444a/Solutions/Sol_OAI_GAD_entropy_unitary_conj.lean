-- Prove2me | solution 1 for OAI.GAD.entropy_unitary_conj
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:32:55.262685+00:00
-- url     : https://prove2.me/submissions/a4192c79-6de3-4985-8e95-2c24e4cab88f

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/SpectralEntropy.lean:L94-L110
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.entropy_unitary_conj. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity

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

/-- Entropy is invariant under every unitary basis change. -/
theorem entropy_unitary_conj (U : Matrix.unitaryGroup ι ℂ)
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    entropy (Unitary.conjStarAlgAut ℂ _ U A) = entropy A := by
  have hφA : (Unitary.conjStarAlgAut ℂ _ U A).IsHermitian := by
    simpa only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using
      Matrix.isHermitian_mul_mul_conjTranspose (U : Matrix ι ι ℂ) hA
  have hm := StarAlgHomClass.map_cfc (S := ℂ)
    (Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U) Real.negMulLog A
    Real.continuous_negMulLog.continuousOn
    (show Continuous (fun P : Matrix ι ι ℂ ↦ (U : Matrix ι ι ℂ) * P * star U) by fun_prop)
    hA hφA
  unfold entropy
  calc
    _ = (Matrix.trace (Unitary.conjStarAlgAut ℂ _ U (cfc Real.negMulLog A))).re :=
      congrArg (fun P : Matrix ι ι ℂ ↦ P.trace.re) hm.symm
    _ = _ := congrArg Complex.re (trace_unitary_conj U _)

end GAD

end

end OAI

-- ---- platform node ----
open OAI OAI.GAD
open scoped BigOperators
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix


theorem solution : type_of% @_root_.OAI.GAD.entropy_unitary_conj := @_root_.OAI.GAD.entropy_unitary_conj
