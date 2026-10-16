-- Prove2me | solution 1 for OAI.EntropyPhotonNumber.logarithmicMean_exp_pair
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:28:50.539245+00:00
-- url     : https://prove2.me/submissions/4479e100-42b8-4b3c-801c-d5038879d460

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Interpolation.lean:L353-L372
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyPhotonNumber.logarithmicMean_exp_pair. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs
import Definitions.Def_OAI_Analysis_TensorLp
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamTrace
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Functions
import Definitions.Def_OAI_Analysis_DiagonalForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_ThermalMetric
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Generator
import Definitions.Def_OAI_InformationTheory_PhotonNumber_SpectralLog
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Continuity
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Entropy
import Definitions.Def_OAI_InformationTheory_PhotonNumber_GibbsVariational
import Definitions.Def_OAI_Analysis_Herglotz
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Interpolation

-- ---- from OAI.InformationTheory.PhotonNumber.Functions ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate

namespace EntropyPhotonNumber

open Set Filter Topology

theorem f_mul_sinh (x : ℝ) : f x * Real.sinh x = x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [f_of_ne_zero hx, div_mul_cancel₀ _ (Real.sinh_ne_zero.mpr hx)]

theorem f_mul_exp (x : ℝ) : f x * Real.exp x = b x + x := by
  have h : Real.exp x = Real.cosh x + Real.sinh x := by
    rw [Real.cosh_eq, Real.sinh_eq]
    ring
  rw [h, mul_add, f_mul_sinh]
  rfl

theorem f_mul_exp_neg (x : ℝ) : f x * Real.exp (-x) = b x - x := by
  simpa [sub_eq_add_neg] using f_mul_exp (-x)

end EntropyPhotonNumber

end

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric

namespace EntropyPhotonNumber

open Set Filter Topology
end EntropyPhotonNumber

end

end OAI

-- ---- from OAI.InformationTheory.PhotonNumber.Interpolation ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal

namespace EntropyPhotonNumber
open Herglotz MeasureTheory

end EntropyPhotonNumber

namespace EntropyPhotonNumber.Herglotz

end EntropyPhotonNumber.Herglotz

namespace EntropyPhotonNumber
open MeasureTheory Herglotz

end EntropyPhotonNumber

end

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology

namespace EntropyPhotonNumber

section
open DiagonalForms.System MeasureTheory Set Filter Topology

theorem logarithmicMean_exp_pair {m : ℝ} (hm : 0 < m) (x : ℝ) :
    logMean (m*f x*Real.exp x) (m*f x*Real.exp (-x)) = m := by
  by_cases hx : x = 0
  · simp [hx, logMean]
  have hx2 : 2*x ≠ 0 := mul_ne_zero (by norm_num) hx
  have hmf : 0 < m*f x := mul_pos hm (f_pos x)
  have he : m*f x*Real.exp x ≠ m*f x*Real.exp (-x) := by
    intro h
    have ht := mul_left_cancel₀ hmf.ne' h
    have ht' := Real.exp_injective ht
    exact hx (by linarith)
  rw [logMean, ite_eq_right he, Real.log_mul hmf.ne' (Real.exp_ne_zero _),
    Real.log_mul hmf.ne' (Real.exp_ne_zero _), Real.log_exp, Real.log_exp]
  have hn : m*f x*Real.exp (-x) - m*f x*Real.exp x = -2*m*x := by
    rw [mul_assoc, mul_assoc, f_mul_exp_neg, f_mul_exp]
    ring
  rw [hn]
  have hd : Real.log (m*f x) + -x - (Real.log (m*f x) + x) = -2*x := by ring
  rw [hd]
  field_simp

end

open DiagonalForms.System MeasureTheory Set Filter Topology Herglotz

end EntropyPhotonNumber

end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyPhotonNumber
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology
open DiagonalForms.System MeasureTheory Set Filter Topology


theorem solution : type_of% @_root_.OAI.EntropyPhotonNumber.logarithmicMean_exp_pair := @_root_.OAI.EntropyPhotonNumber.logarithmicMean_exp_pair
