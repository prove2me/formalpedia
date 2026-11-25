-- Prove2me | solution 1 for GlobalTheory.AbCoh.Vanish.omega_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:11:21.723034+00:00
-- url     : https://prove2.me/submissions/a8facc47-e6a2-4f3b-82d9-312252435ec9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CommAlgFunctorCohomologyTwoEqZeroOfIsInitial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbCoh GlobalTheory.AbCoh.Vanish
namespace GlobalTheory.AbCoh.Vanish
theorem _root_.solution {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) [IsIso s] :
    Subsingleton Ω[Sec s ⊤⁄R] := by
  refine KaehlerDifferential.subsingleton_of_surjective R _ ?_
  have : IsIso (secMap s ⊤) := by
    unfold secMap
    haveI h1 : IsIso s.appTop := inferInstanceAs (IsIso (s.app ⊤))
    haveI h2 : IsIso (X.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op) := by
      rw [show (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 _ from rfl]
      infer_instance
    exact IsIso.comp_isIso' (f := (Scheme.ΓSpecIso (CommRingCat.of R)).inv) inferInstance
      (IsIso.comp_isIso' h1 h2)
  exact (ConcreteCategory.bijective_of_isIso (secMap s ⊤)).2
end GlobalTheory.AbCoh.Vanish
