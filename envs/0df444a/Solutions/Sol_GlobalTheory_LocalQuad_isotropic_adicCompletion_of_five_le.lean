-- Prove2me | solution 1 for GlobalTheory.LocalQuad.isotropic_adicCompletion_of_five_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:24:42.08707+00:00
-- url     : https://prove2.me/submissions/59bbb555-848f-40b1-91d0-c16bd920ac52

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
import Theorems.Thm_GlobalTheory_LocalQuad_exists_unit_valued_ternary_lt_one
import Theorems.Thm_GlobalTheory_LocalQuad_exists_zero_five_of_valuation
import Theorems.Thm_GlobalTheory_LocalQuad_isSquare_of_valued_sub_one_lt
import Theorems.Thm_GlobalTheory_LocalQuad_isotropic_of_injective
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
theorem _root_.solution (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) {ι : Type*} [Fintype ι] (hι : 5 ≤ Fintype.card ι)
    (a : ι → v.adicCompletion F) :
    ∃ x : ι → v.adicCompletion F, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by
  haveI : CharZero (v.adicCompletion F) :=
    charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
  obtain ⟨e⟩ : Nonempty (Fin 5 ↪ ι) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hι)
  exact isotropic_of_injective e e.injective
    (exists_zero_five_of_valuation two_ne_zero Valued.v (v.valuedAdicCompletion_surjective F)
      (isSquare_of_valued_sub_one_lt F v) (exists_unit_valued_ternary_lt_one F v) _)
end GlobalTheory.LocalQuad
