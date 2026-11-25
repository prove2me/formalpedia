-- Prove2me | solution 1 for GlobalTheory.SS.Ord.exists_hasOrd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:01:47.057907+00:00
-- url     : https://prove2.me/submissions/efb835f4-59b7-4fd5-8b43-820848a8d762

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelHasJacobianOrder
import Theorems.Thm_GlobalTheory_SS_Ord_j_cst
import Theorems.Thm_GlobalTheory_SS_Ord_rs_cstK
import Theorems.Thm_GlobalTheory_SS_Ord_rs_j
import Theorems.Thm_GlobalTheory_SS_Ord_rs_jac
import Theorems.Thm_GlobalTheory_SS_Ord_nonempty_basicOpen_inter
import Theorems.Thm_GlobalTheory_SS_Ord_exists_lower
import Theorems.Thm_GlobalTheory_SS_Ord_exists_upper
import Theorems.Thm_GlobalTheory_SS_Ord_forall_of_affine

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
  [IsFractionRing R K] {A : Over (Sp K)} {π : R} {I : Type} [Fintype I] [DecidableEq I]
namespace GlobalTheory.SS.Ord
theorem _root_.solution (hπ : Irreducible π) (M : Model R A) (hM : M.Irr) {D : I → VF A} (hD : IsFrame D) :
    ∃ n : ℤ, HasOrd M D π n := by
  have hp : algebraMap R K π ≠ 0 := by simpa using hπ.ne_zero
  obtain ⟨x, hx⟩ := hM.1
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := M.Y.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ x) isOpen_univ
  have h : ((U : Set M.Y.left) ∩ M.sp).Nonempty := ⟨x, hxU, hx⟩
  obtain ⟨m, hm⟩ := exists_upper hπ M hM hD hU h
  obtain ⟨n, hn, hmax⟩ := Int.exists_greatest_of_bdd (P := fun n : ℤ => ∀ t : I → Γ(M.Y.left, U),
    ∃ s : Γ(M.Y.left, U), jac D (M.j ⁻¹ᵁ U) (fun i => (M.j.app U).hom (t i)) =
        cstK A _ (algebraMap R K π ^ n) * (M.j.app U).hom s) ⟨m, fun n hn => by
      by_contra hlt
      obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = m + k := ⟨(n - m).toNat, by omega⟩
      refine hm fun t => ?_
      obtain ⟨s, hs⟩ := hn t
      exact ⟨cst M U π ^ k * s, by
        rw [hs, zpow_add₀ hp, map_mul, map_mul, map_pow, j_cst, zpow_natCast _ k, map_pow, _root_.mul_assoc]⟩⟩
    (exists_lower hπ M D hU)
  refine ⟨n, forall_of_affine hπ M hM D hU h hn, ?_⟩
  obtain ⟨t, ht⟩ := not_forall.1 (fun h => by have := hmax (n + 1) h; omega)
  obtain ⟨s, hs⟩ := hn t
  have hns : ¬ cst M U π ∣ s := by
    rintro ⟨c, rfl⟩
    exact ht ⟨c, by rw [hs, zpow_add_one₀ hp, map_mul, map_mul, j_cst, _root_.mul_assoc]⟩
  have hle := M.Y.left.basicOpen_le s
  refine ⟨M.Y.left.basicOpen s, fun i => rs _ hle (t i), rs _ hle s,
    nonempty_basicOpen_inter hπ M hM hU h hns, M.Y.left.toRingedSpace.isUnit_res_basicOpen s, ?_⟩
  have := congrArg (rs _ (M.j.preimage_mono hle)) hs
  rw [rs_jac, map_mul, rs_cstK, rs_j M hle] at this
  simpa only [rs_j M hle] using this
end GlobalTheory.SS.Ord
