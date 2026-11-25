-- Prove2me | solution 1 for GlobalTheory.SS.Ord.exists_j_eq_of_rs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:43:39.200684+00:00
-- url     : https://prove2.me/submissions/f1eaa9b8-d3d1-4896-8f5c-3fd7f624d08b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelHasJacobianOrder
import Theorems.Thm_GlobalTheory_SS_Ord_j_app_injective
import Theorems.Thm_GlobalTheory_SS_Ord_rs_cst
import Theorems.Thm_GlobalTheory_SS_Ord_rs_j
import Theorems.Thm_GlobalTheory_SS_Ord_isUnit_j_cst
import Theorems.Thm_GlobalTheory_SS_Ord_exists_pow_mul_eq
import Theorems.Thm_GlobalTheory_SS_Ord_dvd_of_dvd_rs

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
namespace GlobalTheory.SS.Ord
theorem _root_.solution (hπ : Irreducible π) (M : Model R A) (hM : M.Irr) {U W : M.Y.left.Opens}
    (hU : IsAffineOpen U) (hW : W ≤ U) (h : ((W : Set M.Y.left) ∩ M.sp).Nonempty)
    (f : Γ(A.left, M.j ⁻¹ᵁ U)) (s : Γ(M.Y.left, W)) (hs : (M.j.app W).hom s = rs _ (M.j.preimage_mono hW) f) :
    ∃ b, (M.j.app U).hom b = f := by
  obtain ⟨k, b, hb⟩ := exists_pow_mul_eq hπ M hU f
  induction k generalizing b with
  | zero => exact ⟨b, by simpa using hb⟩
  | succ k ih =>
    have h1 : rs _ hW b = cst M W π ^ (k + 1) * s := j_app_injective M W (by
      rw [← rs_j M hW, hb, map_mul, map_pow, map_mul, map_pow, hs, rs_j M hW, rs_cst])
    obtain ⟨c, rfl⟩ := dvd_of_dvd_rs hπ M hM hU hW h (b := b) ⟨cst M W π ^ k * s, by rw [h1]; ring⟩
    refine ih c ((isUnit_j_cst hπ M U).mul_left_cancel ?_)
    rw [← map_mul, hb]; ring
end GlobalTheory.SS.Ord
