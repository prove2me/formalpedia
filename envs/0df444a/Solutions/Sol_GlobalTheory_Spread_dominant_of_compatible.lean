-- Prove2me | solution 1 for GlobalTheory.Spread.dominant_of_compatible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:44:28.725828+00:00
-- url     : https://prove2.me/submissions/af592e07-a32e-4054-931c-1a276c060bf0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Theorems.Thm_GlobalTheory_Spread_eq_bcMap
import Theorems.Thm_GlobalTheory_Spread_isSchemeTheoreticallyDominant_bcMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Spread
variable {k A : Type} [Field k] [CommRing A] [Algebra k A] {B Z : Scheme.{0}} (pB : B ⟶ Sp k)
namespace GlobalTheory.Spread
theorem _root_.solution (R : Subalgebra k A)
    {j : pullback pB (spMap (algebraMap k A)) ⟶ pullback pB (spMap (algebraMap k R))}
    (h₁ : j ≫ pullback.fst _ _ = pullback.fst _ _)
    (h₂ : j ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap R.val.toRingHom) :
    QuasiCompact j ∧ IsSchemeTheoreticallyDominant j := by
  obtain rfl := eq_bcMap pB R.val h₁ h₂
  exact ⟨inferInstance, isSchemeTheoreticallyDominant_bcMap pB _ Subtype.val_injective⟩
end GlobalTheory.Spread
