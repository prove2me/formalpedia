-- Prove2me | solution 1 for GlobalTheory.JR.WeilEtProof.weilAt_of_isField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:35:51.945441+00:00
-- url     : https://prove2.me/submissions/964ea12e-6372-4ee2-9efa-5f27ea5dd90c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSplitting
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsWeilRepresentationHyperbolicSplitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilRepresentationExistsEtaleOfSubsingletonStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaKEqNegOneOfNotNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsEtaleInvolutiveAlgebraSplittingSmallerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilConditionProductSplittingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilRepresentationEtaleOfQuadraticField
import Theorems.Thm_GlobalTheory_T_etaK_eq_neg_one_of_not_norm
import Theorems.Thm_GlobalTheory_T_etaleHermitianPair_structure_facts


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilEtProof
namespace GlobalTheory.JR.WeilEtProof
theorem _root_.solution : WeilField → ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), IsField A.K → IsField A.L → WeilAt A := by
  intro hF F E _ _ _ _ _ A hK hL ψ hψ x μ hμ
  have hfacts := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  refine hF F E A hK hL ψ hψ x μ hμ A.etaK (fun s => ⟨?_, fun h => GlobalTheory.T.etaK_eq_neg_one_of_not_norm F E A hK hL s h⟩)
  rintro ⟨y, hy⟩
  have hy0 : y ≠ 0 := by
    rintro rfl
    have h1 := hfacts.1 0
    rw [hy, zero_mul] at h1
    have hu : IsUnit (algebraMap A.K A.L s) := s.isUnit.map _
    rw [h1, isUnit_zero_iff] at hu
    obtain ⟨a, b, hab⟩ := hL.exists_pair_ne
    exact hab (by rw [← one_mul a, ← one_mul b, ← hu, zero_mul, zero_mul])
  obtain ⟨b, hb⟩ := hL.mul_inv_cancel hy0
  have := hfacts.2.2.2.1 y (IsUnit.of_mul_eq_one _ hb)
  rwa [hy] at this
end GlobalTheory.JR.WeilEtProof
