-- Prove2me | solution 1 for GlobalTheory.LocalQuad.isotropic_of_locally_isotropic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:56:07.557768+00:00
-- url     : https://prove2.me/submissions/237c2332-eec1-4a62-8cc3-4b7a8ac885a6

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
import Theorems.Thm_GlobalTheory_LocalQuad_isotropic_add_four
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_Inertia_negIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_symm
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
theorem _root_.solution (H : GlobalTheory.Published.HasseNormSt) (F : Type) [Field F]
    [NumberField F] {ι : Type*} [Fintype ι] (hι : 4 ≤ Fintype.card ι) (a : ι → F)
    (ha : ∀ i, a i ≠ 0)
    (hr : ∀ σ : F →+* ℝ, ∃ x : ι → ℝ, x ≠ 0 ∧ ∑ i, σ (a i) * x i ^ 2 = 0)
    (hf : ∀ v : HeightOneSpectrum (𝓞 F), ∃ x : ι → v.adicCompletion F, x ≠ 0 ∧
      ∑ i, algebraMap F (v.adicCompletion F) (a i) * x i ^ 2 = 0) :
    ∃ x : ι → F, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le' hι
  let e : ι ≃ Fin (n + 4) := Fintype.equivFinOfCardEq hn
  refine isotropic_of_injective e.symm e.symm.injective
    (isotropic_add_four H F n _ (fun i => ha _) (fun σ => ?_) (fun v => ?_))
  · exact isotropic_of_injective e e.injective (by simpa using hr σ)
  · exact isotropic_of_injective e e.injective (by simpa only [e.symm_apply_apply] using hf v)
end GlobalTheory.LocalQuad
