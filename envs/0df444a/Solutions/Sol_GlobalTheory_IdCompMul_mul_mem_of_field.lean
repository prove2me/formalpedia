-- Prove2me | solution 1 for GlobalTheory.IdCompMul.mul_mem_of_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:28:45.907083+00:00
-- url     : https://prove2.me/submissions/74269c1e-d807-47a0-a7e7-a8ac363beb27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SectionComponentsPreimageOfIsPullbackStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MulMemIdentityComponentOfRationalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdentityComponentsSmoothGroupSchemeMulMem
import Theorems.Thm_GlobalTheory_T_preimage_section_connectedComponentIn_of_isPullback
import Theorems.Thm_P2M_GlobalTheory_T_mul_mem_identityComponent_of_rational__c555fc7d5940


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
noncomputable section
open GlobalTheory GlobalTheory.IdCompMul
namespace GlobalTheory.IdCompMul
theorem _root_.solution {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : Smooth G.hom) (k : Type) [Field k]
    (p : Spec (CommRingCat.of k) ⟶ S) (a b : Over.mk p ⟶ G)
    (ha : a.left (IsLocalRing.closedPoint k) ∈
      {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))})
    (hb : b.left (IsLocalRing.closedPoint k) ∈
      {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))}) :
    (a * b).left (IsLocalRing.closedPoint k) ∈
      {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} := by
  let F := Over.pullback p
  let G' : Over (Spec (CommRingCat.of k)) := F.obj G
  have hpt : ∀ z : (Spec (CommRingCat.of k) : Scheme), z = IsLocalRing.closedPoint k :=
    fun z => Subsingleton.elim _ _
  have hsec : η[G'].left ≫ pullback.fst G.hom p = p ≫ η[G].left := by
    have hc : pullback.fst (𝟙 S) p = pullback.snd (𝟙 S) p ≫ p := by
      simpa using pullback.condition (f := 𝟙 S) (g := p)
    simp [G', F, hc]
    exact pullback.lift_fst _ _ _
  have key := GlobalTheory.T.preimage_section_connectedComponentIn_of_isPullback G.left S G'.left (Spec (CommRingCat.of k)) G.hom G'.hom p
    (pullback.fst G.hom p) η[G].left η[G'].left hG (IsPullback.of_hasPullback G.hom p)
    (Over.w η[G]) (Over.w η[G']) hsec
  have huniv : ∀ t : (Spec (CommRingCat.of k) : Scheme), G'.hom ⁻¹' {t} = Set.univ :=
    fun t => Set.eq_univ_of_forall fun y => Set.mem_singleton_iff.mpr ((hpt _).trans (hpt t).symm)
  have hq : ∀ z : G'.left,
      pullback.fst G.hom p z ∈
        {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} ↔
      z ∈ connectedComponent ((η[G']).left (IsLocalRing.closedPoint k)) := by
    intro z
    rw [← Set.mem_preimage, key]
    show z ∈ connectedComponentIn (G'.hom ⁻¹' {G'.hom z}) ((η[G']).left (G'.hom z)) ↔ _
    rw [huniv, connectedComponentIn_univ, hpt (G'.hom z)]
  let u : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ F.obj (Over.mk p) :=
    Over.homMk (pullback.lift (𝟙 _) (𝟙 _) (by simp)) (by simp [F]; exact pullback.lift_snd _ _ _)
  have hgen : ∀ c : Over.mk p ⟶ G, (u ≫ F.map c).left ≫ pullback.fst G.hom p = c.left := by
    intro c
    simp [u, F]
    erw [pullback.lift_fst, ← Category.assoc, pullback.lift_fst, Category.id_comp]
  have hpoint : ∀ (c : Over.mk p ⟶ G) (t : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G'),
      t.left ≫ pullback.fst G.hom p = c.left →
        pullback.fst G.hom p (t.left (IsLocalRing.closedPoint k)) = c.left (IsLocalRing.closedPoint k) := by
    intro c t h
    rw [← h]
    rfl
  have ha' := (hq _).1 (by rw [hpoint a _ (hgen a)]; exact ha)
  have hb' := (hq _).1 (by rw [hpoint b _ (hgen b)]; exact hb)
  have hm := GlobalTheory.T.mul_mem_identityComponent_of_rational' k G' (u ≫ F.map a) (u ≫ F.map b) ha' hb'
  have e1 := hgen (a * b)
  rw [Functor.map_mul, MonObj.comp_mul] at e1
  rw [← hpoint (a * b) _ e1]
  exact (hq _).2 hm
end GlobalTheory.IdCompMul
