-- Prove2me | solution 1 for GlobalTheory.isDiscreteValuationRing_of_etale_of_isLocalHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:38:51.218964+00:00
-- url     : https://prove2.me/submissions/41560c6a-1906-4702-a58a-be705f6e022e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
import Theorems.Thm_GlobalTheory_exists_isDiscreteValuationRing_of_unramified
import Theorems.Thm_GlobalTheory_finite_and_isSeparable_fractionRing_of_unramified


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution (V V' : Type*) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [CommRing V'] [IsLocalRing V'] [Algebra V V']
    [IsLocalHom (algebraMap V V')] [Algebra.Etale V V'] :
    ∃ (_ : IsDomain V') (_ : IsDiscreteValuationRing V'),
      (maximalIdeal V).map (algebraMap V V') = maximalIdeal V' ∧
      Module.FaithfullyFlat V V' ∧
      Module.Finite (ResidueField V) (ResidueField V') ∧
      Algebra.IsSeparable (ResidueField V) (ResidueField V') ∧
      ∃ (_ : Algebra (FractionRing V) (FractionRing V'))
        (_ : IsScalarTower V (FractionRing V) (FractionRing V')),
        Module.Finite (FractionRing V) (FractionRing V') ∧
        Algebra.IsSeparable (FractionRing V) (FractionRing V') := by
  obtain ⟨hD, hR⟩ := _root_.GlobalTheory.exists_isDiscreteValuationRing_of_unramified V V'
  have hF : Module.FaithfullyFlat V V' := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hinj : Function.Injective (algebraMap V V') := FaithfulSMul.algebraMap_injective V V'
  haveI : FaithfulSMul V (FractionRing V') := by
    rw [faithfulSMul_iff_algebraMap_injective, IsScalarTower.algebraMap_eq V V' (FractionRing V')]
    exact (IsFractionRing.injective V' (FractionRing V')).comp hinj
  letI := FractionRing.liftAlgebra V (FractionRing V')
  haveI := FractionRing.isScalarTower_liftAlgebra V (FractionRing V')
  obtain ⟨hfin, hsep⟩ :=
    _root_.GlobalTheory.finite_and_isSeparable_fractionRing_of_unramified V V' (FractionRing V) (FractionRing V')
  exact ⟨hD, hR, Algebra.FormallyUnramified.map_maximalIdeal, hF, inferInstance, inferInstance,
    _, inferInstance, hfin, hsep⟩
end _root_.GlobalTheory
end GlobalTheory
