-- Prove2me | solution 1 for GlobalTheory.SquareDensity.dvd_aeval_sub_aeval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:57:17.872699+00:00
-- url     : https://prove2.me/submissions/361eacc5-8727-4a34-995e-1190de5d4831

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSqAddSubDvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory
open GlobalTheory.SquareDensity
namespace GlobalTheory.SquareDensity
theorem _root_.solution {K S σ : Type*} [CommRing K] [CommRing S] [Algebra K S]
    (Φ : MvPolynomial σ K) (s : S) (a b : σ → S) (h : ∀ i, s ∣ a i - b i) :
    s ∣ MvPolynomial.aeval a Φ - MvPolynomial.aeval b Φ := by
  induction Φ using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
    have := dvd_add hp hq
    simp only [map_add]
    convert this using 1
    ring
  | mul_X p i hp =>
    have := dvd_add (hp.mul_right (a i)) ((h i).mul_left (MvPolynomial.aeval b p))
    simp only [map_mul, MvPolynomial.aeval_X]
    convert this using 1
    ring
end GlobalTheory.SquareDensity
