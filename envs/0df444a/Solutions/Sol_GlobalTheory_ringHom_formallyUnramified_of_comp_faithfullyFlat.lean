-- Prove2me | solution 1 for GlobalTheory.ringHom_formallyUnramified_of_comp_faithfullyFlat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:32:32.902708+00:00
-- url     : https://prove2.me/submissions/64ab902b-4c6a-405f-89f5-78870db8b6e7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FormallyUnramifiedOfCompOfEtaleOfSurjective
import Theorems.Thm_GlobalTheory_IsAdicFamily_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
local notation "OO" p:max => (Valuation.valuationSubring (Valued.v : Valuation (PadicAlgCl p) NNReal))
local notation "cPt" p:max => (IsLocalRing.closedPoint (OO p) : Sp (OO p))
local notation "gPt" p:max => spMap (ValuationSubring.subtype (OO p))
open GlobalTheory
universe u
open TensorProduct
namespace GlobalTheory
theorem _root_.solution {A B C : Type*} [CommRing A]
    [CommRing B] [CommRing C] {φ : A →+* B} {β : B →+* C} (hβ : β.FaithfullyFlat)
    (hs : β.FormallySmooth) (hu : β.FormallyUnramified) (h : (β.comp φ).FormallyUnramified) :
    φ.FormallyUnramified := by
  algebraize [φ, β, β.comp φ]
  have : Algebra.FormallyEtale B C :=
    Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr ⟨hu, hs⟩
  have h1 : Subsingleton (C ⊗[B] Ω[B⁄A]) :=
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale A B C).subsingleton
  exact ⟨(Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right B C).mp h1⟩
end GlobalTheory
