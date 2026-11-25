-- Prove2me | solution 1 for GlobalTheory.SS.Ord.dvd_of_dvd_rs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:35:06.496814+00:00
-- url     : https://prove2.me/submissions/bf5d0f30-7b77-4476-ad19-3b9bb695f0b6

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
import Theorems.Thm_GlobalTheory_SS_Ord_nonempty_basicOpen_inter

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
theorem _root_.solution (hπ : Irreducible π) (M : Model R A) (hM : M.Irr) {U W : M.Y.left.Opens}
    (hU : IsAffineOpen U) (hW : W ≤ U) (h : ((W : Set M.Y.left) ∩ M.sp).Nonempty) {b : Γ(M.Y.left, U)}
    (hb : cst M W π ∣ rs _ hW b) : cst M U π ∣ b := by
  by_contra hn
  obtain ⟨x, hx, hx'⟩ := nonempty_basicOpen_inter hπ M hM hU (h.mono fun x hx => ⟨hW hx.1, hx.2⟩) hn
  obtain ⟨y, hy, hy'⟩ := h
  obtain ⟨z, hz, hz1, hz2⟩ := hM.2 _ _ (M.Y.left.basicOpen b).isOpen W.isOpen ⟨x, hx', hx⟩ ⟨y, hy', hy⟩
  have h1 : z ∈ M.Y.left.basicOpen (rs _ hW b) := (M.Y.left.basicOpen_res b (homOfLE hW).op).ge ⟨hz2, hz1⟩
  obtain ⟨c, hc⟩ := hb
  rw [hc, Scheme.basicOpen_mul] at h1
  exact ((mem_basicOpen_cst hπ M W z).1 h1.1).2 hz
end GlobalTheory.SS.Ord
