-- Prove2me | solution 1 for GlobalTheory.ThetaLiftGL.compactOpen_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:46:27.982409+00:00
-- url     : https://prove2.me/submissions/785bb42a-5f29-4716-b4df-96d64d8d733b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_IsParahoricVec
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisGeometry__HoweDualityGL_c4f3064dc8a43034
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsOpenNormalisedSubgroupSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_SmoothContragredientIrreducibleAndReflexiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaPairContragredientQuotientStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaPairDetTwistStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaCorrespondenceLargeRank
import Theorems.Thm_GlobalTheory_SmGL_exists_open_normalised_subgroup_subset


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.Published
open scoped TensorProduct
open GlobalTheory GlobalTheory.ThetaLiftGL
namespace GlobalTheory.ThetaLiftGL
theorem _root_.solution (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) :
    ∀ U ∈ nhds (1 : GL (Fin n) k), ∃ K : Subgroup (GL (Fin n) k),
      IsOpen (K : Set (GL (Fin n) k)) ∧ IsCompact (K : Set (GL (Fin n) k)) ∧ (K : Set (GL (Fin n) k)) ⊆ U := by
  intro U hU
  obtain ⟨J, h1, h2, h3, -⟩ := exists_open_normalised_subgroup_subset k (Fin n) U hU
  exact ⟨J, h1, SplitFlip.isCompact_KO.of_isClosed_subset (J.isClosed_of_isOpen h1) h3, h2⟩
end GlobalTheory.ThetaLiftGL
