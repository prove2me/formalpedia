-- Prove2me | solution 1 for GlobalTheory.SmoothDim.ringKrullDim_affineOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:01:40.912267+00:00
-- url     : https://prove2.me/submissions/9b6996df-784b-4b02-84fb-20aff5bcddd0

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimOfEtaleMvPolynomial
import Theorems.Thm_GlobalTheory_SmoothDim_ringKrullDim_of_isStandardSmooth
import Theorems.Thm_GlobalTheory_SmoothDim_ringKrullDim_eq_of_span_eq_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SmoothDim
namespace GlobalTheory.SmoothDim
theorem _root_.solution :
    ∀ (K : Type) [Field K] (X : Scheme.{0}) (p : X ⟶ Sp K) (g : ℕ),
      SmoothOfRelativeDimension g p → ∀ U : X.Opens, IsAffineOpen U → (U : Set X).Nonempty →
        ringKrullDim Γ(X, U) = g := by
  intro K _ X p g hp U hU hne
  haveI : Nonempty U := hne.to_subtype
  have hK : IsField Γ(Sp K, ⊤) :=
    MulEquiv.isField (Field.toIsField K) (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv
  obtain ⟨s, hs, h⟩ := HasRingHomProperty.appLE (@SmoothOfRelativeDimension g) p hp
    ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  exact ringKrullDim_eq_of_span_eq_top s hs _ fun t ht _ =>
    ringKrullDim_of_isStandardSmooth hK (h t ht)
end GlobalTheory.SmoothDim
