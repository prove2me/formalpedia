-- Prove2me | solution 1 for GlobalTheory.SmoothDim.ringKrullDim_of_isStandardSmooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:25:10.418847+00:00
-- url     : https://prove2.me/submissions/51a451c4-8fc5-4578-b6a1-6ccd4538c2cc

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimOfEtaleMvPolynomial
import Theorems.Thm_GlobalTheory_SmoothDim_ringKrullDim_of_etale_mvPolynomial

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
theorem _root_.solution {K B : Type*} [CommRing K] (hK : IsField K) [CommRing B]
    [Nontrivial B] {g : ℕ} {f : K →+* B} (hf : f.IsStandardSmoothOfRelativeDimension g) :
    ringKrullDim B = g := by
  letI := hK.toField
  obtain ⟨φ, -, hφ⟩ := hf.exists_etale_mvPolynomial
  algebraize [φ]
  exact ringKrullDim_of_etale_mvPolynomial K B g
end GlobalTheory.SmoothDim
