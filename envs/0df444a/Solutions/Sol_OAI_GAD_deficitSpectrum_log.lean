-- Prove2me | solution 1 for OAI.GAD.deficitSpectrum_log
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:46:15.232353+00:00
-- url     : https://prove2.me/submissions/161ea8a9-d68b-4292-b242-d89e824a2233

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/ScalarDeficit.lean:L70-L89
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.deficitSpectrum_log. The node keeps its source
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

theorem deficitSpectrum_log {x y z t : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (ht : 0 < t) :
    ∑ i, deficitSigns i * Real.log (1 + deficitSpectrum x y z i / t) = deficitLog x y z t := by
  obtain ⟨hlp, hlm, hsum, hprod⟩ := blockLambda_properties hx hy hz
  have hn (a : ℝ) (ha : 0 ≤ a) : 1 + a/t ≠ 0 := ne_of_gt (by positivity)
  have hty : t+y ≠ 0 := by linarith
  have htz : t+z ≠ 0 := by linarith
  have hid : (1 + blockLambdaPlus x y z/t) * (1 + blockLambdaMinus x y z/t) =
      (1+y/t)*(1+z/t)*(1+t*x/((t+y)*(t+z))) := by
    field_simp
    nlinarith [hsum, hprod]
  have hlast : 1+t*x/((t+y)*(t+z)) ≠ 0 := ne_of_gt (by positivity)
  simp only [deficitSigns, deficitSpectrum, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.cons_val_fin_one, one_mul, neg_one_mul]
  have hh := congrArg Real.log hid
  rw [Real.log_mul (hn _ hlp) (hn _ hlm),
    Real.log_mul (mul_ne_zero (hn _ hy) (hn _ hz)) hlast,
    Real.log_mul (hn _ hy) (hn _ hz)] at hh
  dsimp [deficitLog]
  linarith

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


theorem solution : type_of% @_root_.OAI.GAD.deficitSpectrum_log := @_root_.OAI.GAD.deficitSpectrum_log
