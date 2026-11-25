-- Prove2me | solution 1 for GlobalTheory.SS.Ord.forall_of_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:52:50.957416+00:00
-- url     : https://prove2.me/submissions/58ba9a75-4a45-4a5d-a793-6b41c8721cf1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelHasJacobianOrder
import Theorems.Thm_GlobalTheory_SS_Ord_rs_rs
import Theorems.Thm_GlobalTheory_SS_Ord_rs_cstK
import Theorems.Thm_GlobalTheory_SS_Ord_rs_j
import Theorems.Thm_GlobalTheory_SS_Ord_rs_jac
import Theorems.Thm_GlobalTheory_SS_Ord_exists_j_eq_of_local
import Theorems.Thm_GlobalTheory_SS_Ord_j_app_surjective
import Theorems.Thm_GlobalTheory_SS_Ord_exists_j_eq_of_rs
import Theorems.Thm_GlobalTheory_SS_Ord_jac_mem_basicOpen

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
theorem _root_.solution (hπ : Irreducible π) (M : Model R A) (hM : M.Irr) (D : I → VF A)
    {U₀ : M.Y.left.Opens} (hU₀ : IsAffineOpen U₀) (h₀ : ((U₀ : Set M.Y.left) ∩ M.sp).Nonempty) {n : ℤ}
    (hn : ∀ t : I → Γ(M.Y.left, U₀), ∃ s : Γ(M.Y.left, U₀),
      jac D (M.j ⁻¹ᵁ U₀) (fun i => (M.j.app U₀).hom (t i)) =
        cstK A _ (algebraMap R K π ^ n) * (M.j.app U₀).hom s)
    (U : M.Y.left.Opens) (t : I → Γ(M.Y.left, U)) : ∃ s : Γ(M.Y.left, U),
      jac D (M.j ⁻¹ᵁ U) (fun i => (M.j.app U).hom (t i)) =
        cstK A _ (algebraMap R K π ^ n) * (M.j.app U).hom s := by
  have hp : algebraMap R K π ≠ 0 := by simpa using hπ.ne_zero
  have hinv : ∀ V : A.left.Opens, cstK A V (algebraMap R K π ^ n) * cstK A V (algebraMap R K π ^ n)⁻¹ = 1 :=
    fun V => by rw [← map_mul, mul_inv_cancel₀ (zpow_ne_zero n hp), map_one]
  suffices h : ∃ s, (M.j.app U).hom s = cstK A _ (algebraMap R K π ^ n)⁻¹ *
      jac D (M.j ⁻¹ᵁ U) (fun i => (M.j.app U).hom (t i)) by
    obtain ⟨s, hs⟩ := h
    exact ⟨s, by rw [hs, ← _root_.mul_assoc, hinv, _root_.one_mul]⟩
  refine exists_j_eq_of_local M U _ fun x hx => ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := M.Y.left.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
  have hVU' : V ≤ U := hVU
  refine ⟨V, hVU', hxV, ?_⟩
  by_cases hs : ((V : Set M.Y.left) ∩ M.sp).Nonempty
  swap
  · exact j_app_surjective M (fun z hz hz' => hs ⟨z, hz, hz'⟩) _
  obtain ⟨a, ha, ha'⟩ := hs
  obtain ⟨b, hb, hb'⟩ := h₀
  obtain ⟨z, hz, hz1, hz2⟩ := hM.2 _ _ V.isOpen U₀.isOpen ⟨a, ha', ha⟩ ⟨b, hb', hb⟩
  obtain ⟨g, hg, hzg⟩ := hU₀.exists_basicOpen_le (V := V) ⟨z, hz1⟩ hz2
  let N : AddSubgroup Γ(A.left, M.j ⁻¹ᵁ M.Y.left.basicOpen g) :=
    ((AddMonoidHom.mulLeft (cstK A _ (algebraMap R K π ^ n))).comp
      (M.j.app (M.Y.left.basicOpen g)).hom.toAddMonoidHom).range
  have hN : ∀ x, x ∈ N ↔ ∃ s, cstK A _ (algebraMap R K π ^ n) * (M.j.app (M.Y.left.basicOpen g)).hom s = x :=
    fun x => Iff.rfl
  have key := jac_mem_basicOpen M D hU₀ g N
    (fun s x hx => by
      obtain ⟨y, rfl⟩ := (hN x).1 hx
      exact (hN _).2 ⟨s * y, by rw [map_mul]; ring⟩)
    (fun t => by
      obtain ⟨s, hs⟩ := hn t
      exact (hN _).2 ⟨rs _ (M.Y.left.basicOpen_le g) s, by
        rw [hs, map_mul, rs_cstK, rs_j M (M.Y.left.basicOpen_le g)]⟩)
    (fun i => rs _ (hg.trans hVU') (t i))
  obtain ⟨s, hs⟩ := (hN _).1 key
  refine exists_j_eq_of_rs hπ M hM hV hg ⟨z, hzg, hz⟩ _ s ?_
  rw [rs_rs, map_mul, rs_cstK, rs_jac]
  simp only [rs_j M (hg.trans hVU')]
  rw [← hs, ← _root_.mul_assoc, _root_.mul_comm (cstK A _ _⁻¹), hinv, _root_.one_mul]
end GlobalTheory.SS.Ord
