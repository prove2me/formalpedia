-- Prove2me | solution 1 for OAI.EntropyPhotonNumber.inv_sqrt_mem_sineQuadrant
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:59:42.457832+00:00
-- url     : https://prove2.me/submissions/6bb275c7-0c70-4238-81ee-4dc9ec7dc5bc

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Functions.lean:L877-L895
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyPhotonNumber.inv_sqrt_mem_sineQuadrant. The node keeps its source
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
theorem inv_sqrt_mem_sineQuadrant {s : ℂ} (hs : 0 < s.im) :
    (Complex.sqrt s)⁻¹ ∈ sineQuadrant := by
  have hn : |s.re| < ‖s‖ := Complex.abs_re_lt_norm.mpr hs.ne'
  have hr : 0 < (Complex.sqrt s).re := by
    change 0 < (s ^ (2⁻¹ : ℂ)).re
    rw [Complex.cpow_inv_two_re]
    apply Real.sqrt_pos.mpr
    have := (abs_lt.mp hn).1
    linarith
  have hi : 0 < (Complex.sqrt s).im := by
    change 0 < (s ^ (2⁻¹ : ℂ)).im
    rw [Complex.cpow_inv_two_im_eq_sqrt hs.le]
    exact Real.sqrt_pos.mpr (by linarith [(abs_lt.mp hn).2])
  have hz : Complex.sqrt s ≠ 0 := by intro he; simp [he] at hr
  constructor
  · rw [Complex.inv_re]
    exact div_pos hr (Complex.normSq_pos.mpr hz)
  · rw [Complex.inv_im]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos hi) (Complex.normSq_pos.mpr hz)

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
open Set Filter Topology


theorem solution : type_of% @_root_.OAI.EntropyPhotonNumber.inv_sqrt_mem_sineQuadrant := @_root_.OAI.EntropyPhotonNumber.inv_sqrt_mem_sineQuadrant
