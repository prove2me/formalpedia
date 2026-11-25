-- Prove2me | solution 1 for GlobalTheory.SS.Ord.nonempty_basicOpen_inter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:13:37.802802+00:00
-- url     : https://prove2.me/submissions/108493f0-4baf-42d7-a4f6-dc5319c2b6a0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelHasJacobianOrder
import Theorems.Thm_GlobalTheory_SS_Ord_mem_basicOpen_cst
import Theorems.Thm_GlobalTheory_SS_Ord_prime_cst

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
open GlobalTheory.SS
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Ord
variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type} [Field K] [Algebra R K]
  [IsFractionRing R K] {A : Over (Sp K)} {π : R}
omit [IsFractionRing R K]
namespace GlobalTheory.SS.Ord
theorem _root_.solution (hπ : Irreducible π) (M : Model R A) (hM : M.Irr) {U : M.Y.left.Opens}
    (hU : IsAffineOpen U) (h : ((U : Set M.Y.left) ∩ M.sp).Nonempty) {b : Γ(M.Y.left, U)}
    (hb : ¬ cst M U π ∣ b) : ((M.Y.left.basicOpen b : Set M.Y.left) ∩ M.sp).Nonempty := by
  have hp := prime_cst hπ M hM hU h
  let p : PrimeSpectrum Γ(M.Y.left, U) := ⟨Ideal.span {cst M U π}, (Ideal.span_singleton_prime hp.ne_zero).2 hp⟩
  refine ⟨hU.fromSpec p, (hU.fromSpec_preimage_basicOpen b).ge ?_, ?_⟩
  · exact fun h => hb (Ideal.mem_span_singleton.1 h)
  · by_contra hn
    have : hU.fromSpec p ∈ M.Y.left.basicOpen (cst M U π) :=
      (mem_basicOpen_cst hπ M U _).2 ⟨hU.range_fromSpec.le ⟨p, rfl⟩, hn⟩
    exact (hU.fromSpec_preimage_basicOpen _).le this (Ideal.mem_span_singleton_self _)
end GlobalTheory.SS.Ord
