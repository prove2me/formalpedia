-- Prove2me | solution 1 for GlobalTheory.SectionsDescent.exists_sum_sec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:40:14.576705+00:00
-- url     : https://prove2.me/submissions/145fbad6-06a8-4be0-9276-4c0ca1297420

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsExtensionAffine
import Theorems.Thm_GlobalTheory_SectionsDescent_rs_rs
import Theorems.Thm_GlobalTheory_SectionsDescent_rs_self
import Theorems.Thm_GlobalTheory_SectionsDescent_app_rs
import Theorems.Thm_GlobalTheory_SectionsDescent_rs_constHom
import Theorems.Thm_GlobalTheory_SectionsDescent_ext_cover
import Theorems.Thm_GlobalTheory_SectionsDescent_le_iSup_affine
import Theorems.Thm_GlobalTheory_SectionsDescent_isExtension_affine
import Theorems.Thm_GlobalTheory_SectionsDescent_sec_compat
import Theorems.Thm_GlobalTheory_SectionsDescent_exists_coord_sec
import Theorems.Thm_GlobalTheory_FieldBaseChange_exists_expansion


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
noncomputable section
open GlobalTheory GlobalTheory.SectionsDescent
open GlobalTheory.FieldBaseChange
variable {K F : Type} [Field K] [Field F] [Algebra K F] {Y Y' : Scheme.{0}}
  {π : Y ⟶ Spec (CommRingCat.of K)} {π' : Y' ⟶ Spec (CommRingCat.of F)} {p : Y' ⟶ Y}
  (H : IsPullback p π' π (Spec.map (CommRingCat.ofHom (algebraMap K F))))
include H
namespace GlobalTheory.SectionsDescent
theorem _root_.solution [CompactSpace Y] {M : LB Y} (hM : M.IsLB) (t : (M.pull p).Sec) :
    ∃ (J : Type) (S : Finset J) (c : J → F) (s : J → M.Sec), ∀ j : M.ι,
      loc t j = ∑ a ∈ S, constHom π' _ (c a) * (p.app _).hom ((s a).f j) := by
  classical
  let b := Module.Basis.ofVectorSpace K F
  choose Λ hΛ using fun a V (hV : IsAffineOpen V) => (isExtension_affine H hV).coord (b.coord a)
  choose s hs using fun a => exists_coord_sec H (Λ a) (hΛ a) t
  choose S hS hS' using fun j V (hV : IsAffineOpen V) (h : V ≤ M.U j) =>
    exists_expansion b (isExtension_affine H hV).span (fun a => hΛ a V hV) (rs (pre_mono p h) (loc t j))
  have hc : ∀ y : Y, ∃ (j : M.ι) (V : Y.Opens), IsAffineOpen V ∧ V ≤ M.U j ∧ y ∈ V := fun y => by
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (hM.cover.ge (Set.mem_univ y))
    obtain ⟨V, hV⟩ := TopologicalSpace.Opens.mem_iSup.1 (le_iSup_affine _ hj)
    exact ⟨j, V.1, V.2.1, V.2.2, hV⟩
  choose J V hV hVJ hy using hc
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun y : Y => (V y : Set Y)) (fun y => (V y).isOpen)
    (fun y _ => Set.mem_iUnion.2 ⟨y, hy y⟩)
  let S₀ := T.biUnion fun y => S (J y) (V y) (hV y) (hVJ y)
  have z : ∀ a ∉ S₀, ∀ j, (s a).f j = 0 := fun a ha j => by
    refine ext_cover (fun y : T => M.U j ⊓ V y) (fun _ => inf_le_left) (fun x hx => ?_) fun y => ?_
    · obtain ⟨y, hyT, hxy⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ x))
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, hyT⟩, hx, hxy⟩
    · have z₀ : rs (hVJ y) ((s a).f (J y)) = 0 := (hs a _ _ (hV y) (hVJ y)).trans
        (hS _ _ _ _ a fun h => ha (Finset.mem_biUnion.2 ⟨y, y.2, h⟩))
      rw [sec_compat (s a) j (J y) inf_le_left (inf_le_right.trans (hVJ y)),
        ← rs_rs (hVJ y) inf_le_right, z₀, map_zero, map_zero, mul_zero]
  refine ⟨_, S₀, b, s, fun j => ?_⟩
  refine ext_cover (fun W : {W : Y.Opens // IsAffineOpen W ∧ W ≤ M.U j} => p ⁻¹ᵁ W.1)
    (fun W => pre_mono p W.2.2) (fun x hx => ?_) fun W => ?_
  · obtain ⟨W, hW⟩ := TopologicalSpace.Opens.mem_iSup.1 (le_iSup_affine (M.U j) (show p x ∈ M.U j from hx))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨W, hW⟩
  · obtain ⟨W, hW, h⟩ := W
    have e : ∀ a, rs (pre_mono p h) (constHom π' _ (b a) * (p.app _).hom ((s a).f j)) =
        constHom π' (p ⁻¹ᵁ W) (b a) *
          rs le_rfl ((p.app W).hom (Λ a W hW (rs (pre_mono p h) (loc t j)))) := fun a => by
      rw [map_mul, rs_constHom, ← app_rs p h, hs a j W hW h, rs_self]
    have e' : rs (pre_mono p h) (loc t j) = ∑ a ∈ S j W hW h ∪ S₀, constHom π' (p ⁻¹ᵁ W) (b a) *
          rs le_rfl ((p.app W).hom (Λ a W hW (rs (pre_mono p h) (loc t j)))) :=
      hS' j W hW h (S j W hW h ∪ S₀) Finset.subset_union_left
    refine e'.trans ((Finset.sum_congr rfl fun a _ => (e a).symm).trans
      ((Finset.sum_subset Finset.subset_union_right fun a _ ha => ?_).symm.trans (map_sum _ _ _).symm))
    rw [z a ha, map_zero, mul_zero, map_zero]
end GlobalTheory.SectionsDescent
