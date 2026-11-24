-- Prove2me | solution 1 for GlobalTheory.LocalQuad.finite_setOf_valued_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:49:08.5598+00:00
-- url     : https://prove2.me/submissions/f15cb2f9-a54b-49dc-8153-0860afed115e

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsQuaternaryOfCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfValuedSubOneLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitValuedTernaryLtOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsZeroFiveOfValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsForallAbvSubLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRingHomAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsZeroCoordNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsCongrIffTraceFormsIsometric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsCongrIffTraceFormsIsometricCm
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_Inertia_negIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_symm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk
attribute [local simp] GlobalTheory.Inertia.negIndex_neg
attribute [local simp] GlobalTheory.Inertia.posIndex_neg



set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero
open GlobalTheory GlobalTheory.LocalQuad
namespace GlobalTheory.LocalQuad
theorem _root_.solution (F : Type) [Field F] [NumberField F] {c : F} (hc : c ≠ 0) :
    {v : HeightOneSpectrum (𝓞 F) |
      Valued.v (algebraMap F (v.adicCompletion F) c) ≠ 1}.Finite := by
  have h := (FinitePlace.hasFiniteMulSupport hc).preimage
    (f := FinitePlace.equivHeightOneSpectrum.symm)
    (FinitePlace.equivHeightOneSpectrum (K := F)).symm.injective.injOn
  refine h.subset fun v hv => ?_
  simp only [Set.mem_preimage, Function.mem_mulSupport,
    FinitePlace.equivHeightOneSpectrum_symm_apply]
  intro h1
  exact hv (le_antisymm (Valued.toNormedField.norm_le_one_iff.1 h1.le)
    (Valued.toNormedField.one_le_norm_iff.1 h1.ge))
end GlobalTheory.LocalQuad
