-- Prove2me | solution 1 for OAI.EntropyPhotonNumber.inv_sqrt_mem_closedSineQuadrant
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T04:02:03.985+00:00
-- url     : https://prove2.me/submissions/5dfd9ab4-b972-4921-86fe-d0e1deff9bc5

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Functions.lean:L1211-L1224
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyPhotonNumber.inv_sqrt_mem_closedSineQuadrant. The node keeps its source
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
import Theorems.Thm_OAI_EntropyPhotonNumber_inv_sqrt_mem_sineQuadrant

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
theorem inv_sqrt_mem_closedSineQuadrant {s : ℂ} (hr : 0 < s.re) (hi : 0 ≤ s.im) :
    (Complex.sqrt s)⁻¹ ∈ closedSineQuadrant := by
  rcases eq_or_lt_of_le hi with he | hpos
  · have hs : s = (s.re : ℂ) := eq_of_im_zero he.symm
    have hsq : Complex.sqrt s = (Real.sqrt s.re : ℂ) := by
      rw [hs]
      change (s.re : ℂ) ^ (2⁻¹ : ℂ) = (Real.sqrt s.re : ℂ)
      rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hr.le]
      congr 1
      norm_num
    rw [hsq, ← Complex.ofReal_inv]
    exact ⟨inv_pos.mpr (Real.sqrt_pos.mpr hr), by simp⟩
  · have hm := inv_sqrt_mem_sineQuadrant hpos
    exact ⟨hm.1, hm.2.le⟩

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


theorem solution : type_of% @_root_.OAI.EntropyPhotonNumber.inv_sqrt_mem_closedSineQuadrant := @_root_.OAI.EntropyPhotonNumber.inv_sqrt_mem_closedSineQuadrant
