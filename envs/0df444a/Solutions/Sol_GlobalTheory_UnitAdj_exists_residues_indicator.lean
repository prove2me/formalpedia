-- Prove2me | solution 1 for GlobalTheory.UnitAdj.exists_residues_indicator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:13:26.850827+00:00
-- url     : https://prove2.me/submissions/fb97bcf7-de29-41de-80ee-87437c14c445

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqMulIntegralClosureOfSeparableInvolutionAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitaryMulIntegralOfNormMaximalOrderUnit
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_C
import Theorems.Thm_GlobalTheory_mvEvalAdic_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_coe
import Theorems.Thm_GlobalTheory_pderivEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.mvEvalAdic_C
attribute [local simp] GlobalTheory.mvEvalAdic_X
attribute [local simp] GlobalTheory.mvEvalAdic_coe
attribute [local simp] GlobalTheory.pderivEval_X



set_option autoImplicit false
noncomputable section
open Polynomial Matrix GlobalTheory.LatOrb
open GlobalTheory GlobalTheory.UnitAdj
variable {A : Type} [CommRing A] [IsArtinianRing A] [IsReduced A]
namespace GlobalTheory.UnitAdj
theorem _root_.solution (P : MaximalSpectrum A → Prop) :
    ∃ e : A, ∀ I : MaximalSpectrum A, (P I → e - 1 ∈ I.asIdeal) ∧ (¬ P I → e ∈ I.asIdeal) := by
  classical
  let v : ∀ I : MaximalSpectrum A, A ⧸ I.asIdeal := fun I => if P I then 1 else 0
  refine ⟨(IsArtinianRing.equivPi A).symm v, fun I => ⟨fun hP => ?_, fun hP => ?_⟩⟩
  · have h1 := congrFun ((IsArtinianRing.equivPi A).apply_symm_apply v) I
    rw [IsArtinianRing.equivPi_apply] at h1
    rw [← Ideal.Quotient.eq, h1, map_one]
    simp [v, hP]
  · have h1 := congrFun ((IsArtinianRing.equivPi A).apply_symm_apply v) I
    rw [IsArtinianRing.equivPi_apply] at h1
    rw [← Ideal.Quotient.eq_zero_iff_mem, h1]
    simp [v, hP]
end GlobalTheory.UnitAdj
