-- Prove2me | solution 1 for GlobalTheory.SplitTorus.connectedSpace_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:56:06.125628+00:00
-- url     : https://prove2.me/submissions/d1beded8-0004-4cfa-9362-4bf89dc36dfa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_QSurjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
universe u
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
open AddMonoidAlgebra (single)
open GlobalTheory
open GlobalTheory.SplitTorus
namespace GlobalTheory.SplitTorus
theorem _root_.solution {R : Type*} [CommRing R] [ConnectedSpace (PrimeSpectrum R)]
    (I : Ideal R) (hI : I ≤ nilradical R) : ConnectedSpace (PrimeSpectrum (R ⧸ I)) := by
  have h := PrimeSpectrum.isHomeomorph_comap (Ideal.Quotient.mk I)
    (fun x => ⟨1, one_pos, by simpa using Ideal.Quotient.mk_surjective x⟩) (by simpa using hI)
  exact h.homeomorph.symm.surjective.connectedSpace h.homeomorph.symm.continuous
end GlobalTheory.SplitTorus
