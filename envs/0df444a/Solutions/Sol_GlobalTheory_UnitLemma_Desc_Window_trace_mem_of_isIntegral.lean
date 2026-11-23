-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.Window.trace_mem_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:10:39.422661+00:00
-- url     : https://prove2.me/submissions/e4d7f113-5b0c-40f8-b70b-2114bb38647f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiscrMulMemOfIsIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlternatingDifferenceTermWindow
import Theorems.Thm_GlobalTheory_DiscConductor_isIntegral_trace_of_isIntegral


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology Classical
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc GlobalTheory.UnitLemma.Desc.Window
variable {K : UQ} (B : InvAlg K) {ι : Type}
namespace GlobalTheory.UnitLemma.Desc.Window
theorem _root_.solution {y : B.A} (hy : IsIntegral K.O y) :
    Algebra.trace K.E B.A y ∈ (algebraMap K.O K.E).range := by
  have h := GlobalTheory.DiscConductor.isIntegral_trace_of_isIntegral K.O K.E B.A y hy
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  exact ⟨z, hz⟩
end GlobalTheory.UnitLemma.Desc.Window
