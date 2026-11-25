-- Prove2me | solution 1 for GlobalTheory.ThetaLeast.exists_lift_integers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:51:26.118729+00:00
-- url     : https://prove2.me/submissions/5707d706-450e-45b7-9833-24ddb3e9199e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NabValNMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsIntegralCombinationOfMemHaO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_VVAlgebraMapNonnegDvr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsCombinationIntegers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField
open GlobalTheory GlobalTheory.ThetaLeast
namespace GlobalTheory.ThetaLeast
theorem _root_.solution (K : Type) [Field K] [NumberField K] (V L : Type) [CommRing V] [IsDomain V]
    [IsIntegrallyClosed V] [Field L] [Algebra V L] [IsFractionRing V L] (io : K →+* L) :
    ∃ φ : 𝓞 K →+* V, ∀ x : 𝓞 K, algebraMap V L (φ x) = io (x : K) := by
  have h : ∀ x : 𝓞 K, ∃ z : V, algebraMap V L z = io (x : K) := fun x =>
    IsIntegrallyClosed.algebraMap_eq_of_integral
      (IsIntegral.tower_top (R := ℤ) (map_isIntegral_int io x.isIntegral_coe))
  choose g hg using h
  have inj := IsFractionRing.injective V L
  refine ⟨⟨⟨⟨g, inj ?_⟩, fun x y => inj ?_⟩, inj ?_, fun x y => inj ?_⟩, hg⟩ <;> simp [hg]
end GlobalTheory.ThetaLeast
