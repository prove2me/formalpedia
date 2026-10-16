-- Prove2me | solution 1 for OAI.GAD.scalarDeficit_weighted_le_of_log_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:47:44.997684+00:00
-- url     : https://prove2.me/submissions/820e2ce4-1fe9-423e-a9ad-5bee22a0c820

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/ScalarDeficit.lean:L91-L106
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.scalarDeficit_weighted_le_of_log_le. The node keeps its source
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
import Theorems.Thm_OAI_GAD_deficitSpectrum_log
import Theorems.Thm_OAI_GAD_entropy_sum_le_of_log_sum_le

-- ---- from OAI.InformationTheory.AmplitudeDamping.ScalarDeficit ----
namespace OAI

universe u_1 u_2

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder
open scoped BigOperators Topology
open Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Topology

open scoped BigOperators ComplexOrder
open Matrix Set
namespace GAD

theorem blockLambda_properties {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ blockLambdaPlus x y z ∧ 0 ≤ blockLambdaMinus x y z ∧
    blockLambdaPlus x y z + blockLambdaMinus x y z = x + y + z ∧
    blockLambdaPlus x y z * blockLambdaMinus x y z = y*z := by
  have hd : 0 ≤ (x+y+z)^2 - 4*y*z := by
    nlinarith [sq_nonneg (y-z), mul_nonneg hx (by linarith : 0 ≤ y+z)]
  have hs := Real.sq_sqrt hd
  have hsr := Real.sqrt_nonneg ((x+y+z)^2-4*y*z)
  have hle : Real.sqrt ((x+y+z)^2-4*y*z) ≤ x+y+z := by
    nlinarith [mul_nonneg hy hz]
  dsimp [blockLambdaPlus, blockLambdaMinus]
  refine ⟨by positivity, by linarith, by ring, ?_⟩
  nlinarith

theorem deficitSpectrum_nonneg {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (i : Fin 5) : 0 ≤ deficitSpectrum x y z i := by
  have h := blockLambda_properties hx hy hz
  fin_cases i <;> simp [deficitSpectrum] <;> tauto

theorem deficitSpectrum_trace {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    ∑ i, deficitSigns i * deficitSpectrum x y z i = 0 := by
  have h := (blockLambda_properties hx hy hz).2.2.1
  simp [deficitSpectrum, deficitSigns, Fin.sum_univ_succ]
  linarith

theorem deficitSpectrum_entropy (x y z : ℝ) :
    ∑ i, deficitSigns i * Real.negMulLog (deficitSpectrum x y z i) = scalarDeficit x y z := by
  simp [deficitSpectrum, deficitSigns, scalarDeficit, Fin.sum_univ_succ]
  ring

/-- Finite weighted scalar deficits inherit every pointwise logarithmic comparison. -/
theorem scalarDeficit_weighted_le_of_log_le {α : Type u_1} [Fintype α]
    (c x y z : α → ℝ) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) (hz : ∀ i, 0 ≤ z i)
    (hlog : ∀ t : ℝ, 0 < t → ∑ i, c i * deficitLog (x i) (y i) (z i) t ≤ 0) :
    ∑ i, c i * scalarDeficit (x i) (y i) (z i) ≤ 0 := by
  have h := entropy_sum_le_of_log_sum_le
    (fun i : α × Fin 5 ↦ c i.1 * deficitSigns i.2)
    (fun i ↦ deficitSpectrum (x i.1) (y i.1) (z i.1) i.2)
    (fun i ↦ deficitSpectrum_nonneg (hx i.1) (hy i.1) (hz i.1) i.2) ?_ ?_
  · simpa only [Fintype.sum_prod_type, mul_assoc, ← Finset.mul_sum,
      deficitSpectrum_entropy] using h
  · simp only [Fintype.sum_prod_type, mul_assoc, ← Finset.mul_sum,
      deficitSpectrum_trace (hx _) (hy _) (hz _), mul_zero, Finset.sum_const_zero]
  · intro t ht
    simpa only [Fintype.sum_prod_type, mul_assoc, ← Finset.mul_sum,
      deficitSpectrum_log (hx _) (hy _) (hz _) ht] using hlog t ht

end GAD
open scoped BigOperators ComplexOrder
open Matrix Set
namespace GAD

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
open scoped BigOperators Topology
open Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Topology
open scoped BigOperators ComplexOrder
open Matrix Set


theorem solution : type_of% @_root_.OAI.GAD.scalarDeficit_weighted_le_of_log_le := @_root_.OAI.GAD.scalarDeficit_weighted_le_of_log_le
