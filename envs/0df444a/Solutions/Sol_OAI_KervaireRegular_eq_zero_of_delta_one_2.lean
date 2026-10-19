-- Prove2me | solution 2 for OAI.KervaireRegular.eq_zero_of_delta_one
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:17:42.617975+00:00
-- url     : https://prove2.me/submissions/18ae2ce6-fb9f-49b3-9d4c-43a28feb82ac

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/RegularOperators.lean:L185-L199
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireRegular.eq_zero_of_delta_one. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralMeasures
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralLogarithm
import Definitions.Def_OAI_GroupTheory_Kervaire_ScalarPhase
import Definitions.Def_OAI_GroupTheory_Kervaire_TraceCalculus
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralApproximation
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseSubadditivity
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseNaturality
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseGrids
import Definitions.Def_OAI_GroupTheory_Kervaire_RegularOperators

-- ---- from OAI.GroupTheory.Kervaire.RegularOperators ----
namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate

namespace KervaireRegular

variable {α β γ : Type*}

variable {A : Type*} [Group A]

/-- Translation equivariance determines every matrix coefficient from one column. -/
theorem apply_delta_eq_right {T : Operator A} (hT : InCommutant T) (y : A) :
    T (delta y) = right y⁻¹ (T (delta 1)) := by
  have h := DFunLike.congr_fun (hT y⁻¹).eq (delta 1)
  simpa using h

/-- The vector at the identity is separating for the right regular commutant. -/
theorem eq_zero_of_delta_one {T : Operator A} (hT : InCommutant T)
    (h : T (delta 1) = 0) : T = 0 := by
  classical
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ENNReal) ≠ ⊤)
  intro i
  apply ContinuousLinearMap.ext
  intro c
  simp only [ContinuousLinearMap.comp_apply, lp.singleContinuousLinearMap_apply,
    zero_apply]
  have hi : T (delta i) = 0 := by
    rw [apply_delta_eq_right hT, h, map_zero]
  have hc : lp.single 2 i c = c • delta i := by
    simp [delta, ← lp.single_smul]
  rw [hc, map_smul, hi, smul_zero]

attribute [local instance] OAI.KervaireRegular.instContinuousFunctionalCalculusRealOperatorIsSelfAdjoint
end KervaireRegular

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireRegular
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate


theorem solution : type_of% @_root_.OAI.KervaireRegular.eq_zero_of_delta_one := @_root_.OAI.KervaireRegular.eq_zero_of_delta_one
