-- Prove2me | solution 1 for GlobalTheory.irreducibleSpace_of_smooth_of_geometricallyConnected_domain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:59:33.194798+00:00
-- url     : https://prove2.me/submissions/1fdcfc06-7577-4176-ae12-7e33983c6196

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleSpaceOfSmoothFieldOfConnectedSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleSpaceOfSmoothOfGeometricallyConnected
import Theorems.Thm_GlobalTheory_irreducibleSpace_of_smooth_field_of_connectedSpace


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (R : Type) [CommRing R] [IsDomain R] (G : Over (Spec (CommRingCat.of R))), Smooth G.hom →
      GeometricallyConnected G.hom → Nonempty G.left → IrreducibleSpace G.left := by
  intro R _ _ G hs hc _
  let K := FractionRing R
  let g : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R K))
  let F : Scheme := pullback G.hom g
  have hsnd : Smooth (pullback.snd G.hom g) :=
    MorphismProperty.of_isPullback (P := @Smooth) (IsPullback.of_hasPullback G.hom g) hs
  have hcon : ConnectedSpace F :=
    GeometricallyConnected.geometrically_connectedSpace (f := G.hom) g (pullback.fst _ _)
      (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
  have hirr : IrreducibleSpace F :=
    irreducibleSpace_of_smooth_field_of_connectedSpace K _ (pullback.snd G.hom g) hsnd hcon
  have hgf : Flat g := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors R))
  have hG : Flat G.hom := inferInstance

  have hη : genericPoint (Spec (CommRingCat.of R)) ∈ Set.range g :=
    (Flat.generalizingMap g).stableUnderGeneralization_range
      (genericPoint_specializes (g (closedPoint K))) ⟨closedPoint K, rfl⟩
  let ξ : G.left := pullback.fst G.hom g (genericPoint F)
  have hspec : ∀ z : G.left, ξ ⤳ z := by
    intro z
    obtain ⟨z', hz', e⟩ := Flat.generalizingMap G.hom (genericPoint_specializes (G.hom z))
    have hr : z' ∈ Set.range (pullback.fst G.hom g) := by
      rw [Scheme.Pullback.range_fst, Set.mem_preimage, e]; exact hη
    obtain ⟨w, rfl⟩ := hr
    exact ((genericPoint_specializes w).map (pullback.fst G.hom g).continuous).trans hz'
  have hcl : closure ({ξ} : Set G.left) = Set.univ :=
    Set.eq_univ_of_forall fun z => specializes_iff_mem_closure.mp (hspec z)
  rw [irreducibleSpace_def]
  have := (isIrreducible_singleton (x := ξ)).closure
  rw [hcl] at this
  exact this
end GlobalTheory
