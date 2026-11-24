-- Prove2me | solution 1 for GlobalTheory.NilRigidity.exists_preimage_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:20:46.803811+00:00
-- url     : https://prove2.me/submissions/955d2ecb-d324-4cd0-8225-6a1192fa5914

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_EqCompSectionOfSurjectiveAppTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SurjectiveAppOfIsAbelianScheme
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GlobalFnsHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqOfPullbackQuotientEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.NilRigidity
namespace GlobalTheory.NilRigidity
theorem _root_.solution {R : Type} [CommRing R] (I : Ideal R) (hI : I ≤ nilradical R) (t : Sp R) :
    ∃ t₀ : Sp (R ⧸ I), spMap (Ideal.Quotient.mk I) t₀ = t := by
  have hsurj : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
  have hmem : t ∈ PrimeSpectrum.zeroLocus (RingHom.ker (Ideal.Quotient.mk I) : Set R) := by
    rw [Ideal.mk_ker]
    intro x hx
    exact (@nilradical_le_prime _ _ t.asIdeal t.isPrime) (hI hx)
  rw [← range_comap_of_surjective _ _ hsurj] at hmem
  obtain ⟨t₀, ht₀⟩ := hmem
  exact ⟨t₀, ht₀⟩
end GlobalTheory.NilRigidity
