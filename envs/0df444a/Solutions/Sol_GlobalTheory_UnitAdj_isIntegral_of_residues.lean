-- Prove2me | solution 1 for GlobalTheory.UnitAdj.isIntegral_of_residues
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:14:19.971936+00:00
-- url     : https://prove2.me/submissions/65f5dcd6-ecc8-40d5-b50a-5a156bab143f

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqMulIntegralClosureOfSeparableInvolutionAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitaryMulIntegralOfNormMaximalOrderUnit
import Theorems.Thm_P2M_GlobalTheory_UnitLemma_PrincipalLat_isIntegral_pi__b1b6cca95627


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Matrix GlobalTheory.LatOrb
open GlobalTheory GlobalTheory.UnitAdj
variable {A : Type} [CommRing A] [IsArtinianRing A] [IsReduced A]
namespace GlobalTheory.UnitAdj
theorem _root_.solution {O : Type} [CommRing O] [Algebra O A] {y : A}
    (h : ∀ I : MaximalSpectrum A, IsIntegral O (Ideal.Quotient.mk I.asIdeal y)) :
    IsIntegral O y := by
  let ψ : A ≃ₐ[O] (∀ I : MaximalSpectrum A, A ⧸ I.asIdeal) :=
    (IsArtinianRing.equivPi A).restrictScalars O
  refine (isIntegral_algHom_iff ψ.toAlgHom ψ.injective).1 ?_
  refine GlobalTheory.UnitLemma.PrincipalLat.isIntegral_pi' _ fun I => ?_
  have : ψ.toAlgHom y I = Ideal.Quotient.mk I.asIdeal y := IsArtinianRing.equivPi_apply A y I
  rw [this]
  exact h I
end GlobalTheory.UnitAdj
