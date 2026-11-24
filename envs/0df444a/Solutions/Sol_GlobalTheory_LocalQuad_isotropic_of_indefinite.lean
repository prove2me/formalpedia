-- Prove2me | solution 1 for GlobalTheory.LocalQuad.isotropic_of_indefinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:10:44.622291+00:00
-- url     : https://prove2.me/submissions/8e3189d6-8d3c-453a-83bc-38451aba6f37

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
import Theorems.Thm_GlobalTheory_LocalQuad_isotropic_adicCompletion_of_five_le
import Theorems.Thm_GlobalTheory_LocalQuad_isotropic_of_locally_isotropic
import Theorems.Thm_GlobalTheory_LocalQuad_isotropic_real


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero
open GlobalTheory GlobalTheory.LocalQuad
namespace GlobalTheory.LocalQuad
theorem _root_.solution (H : GlobalTheory.Published.HasseNormSt) (F : Type) [Field F] [NumberField F]
    {ι : Type*} [Fintype ι] (a : ι → F) (hι : 5 ≤ Fintype.card ι) (ha : ∀ i, a i ≠ 0)
    (hr : ∀ σ : F →+* ℝ, ∃ i j, σ (a i) < 0 ∧ 0 < σ (a j)) :
    ∃ x : ι → F, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 :=
  isotropic_of_locally_isotropic H F (by omega) a ha
    (fun σ => by
      obtain ⟨i, j, hi, hj⟩ := hr σ
      exact isotropic_real (a := fun i => σ (a i)) hi hj)
    (fun v => isotropic_adicCompletion_of_five_le F v hι _)
end GlobalTheory.LocalQuad
