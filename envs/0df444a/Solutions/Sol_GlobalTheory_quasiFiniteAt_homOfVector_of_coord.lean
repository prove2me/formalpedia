-- Prove2me | solution 1 for GlobalTheory.quasiFiniteAt_homOfVector_of_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:37:45.567627+00:00
-- url     : https://prove2.me/submissions/ef17556e-3eab-458b-a978-c2242f6ab739

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_QuasiFiniteAtAffineSpaceHomOfVectorOfCoord
import Theorems.Thm_GlobalTheory_quasiFiniteAt_of_isClosed_of_generization
import Theorems.Thm_GlobalTheory_eq_of_specializes_of_basicOpen

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
open GlobalTheory.ZJ
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (C : Core) (w : C.G.toScheme) (W : C.G.toScheme.Opens) (hw : w ∈ W) (u : Fin C.g → Γ(C.G.toScheme, W)), IsClosed ({w} : Set C.G.toScheme) → C.Coord w W hw u → (AffineSpace.homOfVector (W.ι ≫ C.GG.hom) (fun i => W.topIso.inv.hom (u i))).QuasiFiniteAt ⟨w, hw⟩ := by
  intro C w W hw u hcl hco
  have := C.proper
  have hlft : LocallyOfFiniteType C.GG.hom := inferInstanceAs (LocallyOfFiniteType (C.G.ι ≫ C.P.hom))
  unfold Core.Coord at hco
  change IsLocalRing.maximalIdeal (C.GG.left.presheaf.stalk w) = _ at hco
  set f := AffineSpace.homOfVector (W.ι ≫ C.GG.hom) (fun i => W.topIso.inv.hom (u i)) with hf
  have hover : f ≫ (𝔸(Fin C.g; C.Z) ↘ C.Z) = W.ι ≫ C.GG.hom := AffineSpace.homOfVector_over _ _
  have : LocallyOfFiniteType (f ≫ (𝔸(Fin C.g; C.Z) ↘ C.Z)) := by
    rw [hover]; infer_instance
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f (𝔸(Fin C.g; C.Z) ↘ C.Z)
  have hemb := W.ι.isOpenEmbedding
  apply quasiFiniteAt_of_isClosed_of_generization
  · have := hcl.preimage hemb.continuous
    convert this using 1
    ext z
    exact Subtype.ext_iff
  intro y hy hfy
  have hy' : y.1 ⤳ w := hy.map hemb.continuous
  have hg : C.GG.hom y.1 = C.GG.hom w := by
    have e : ∀ t : W.toScheme, C.GG.hom t.1 = (𝔸(Fin C.g; C.Z) ↘ C.Z) (f t) := by
      intro t
      rw [← Scheme.Hom.comp_apply, hover]; rfl
    rw [e y, hfy, ← e ⟨w, hw⟩]
  apply Subtype.ext
  let P : Ideal (C.G.toScheme.presheaf.stalk w) :=
    (IsLocalRing.maximalIdeal _).comap (C.G.toScheme.presheaf.stalkSpecializes hy').hom
  have hP : ∀ (U : C.G.toScheme.Opens) (hU : w ∈ U) (s : Γ(C.G.toScheme, U)),
      (C.G.toScheme.presheaf.germ U w hU).hom s ∈ P ↔ y.1 ∉ C.G.toScheme.basicOpen s := by
    intro U hU s
    rw [C.G.toScheme.mem_basicOpen s y.1 (hy'.mem_open U.2 hU), Ideal.mem_comap,
      IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← CommRingCat.comp_apply,
      TopCat.Presheaf.germ_stalkSpecializes]
  have hm : ∀ (U : C.G.toScheme.Opens) (hU : w ∈ U) (s : Γ(C.G.toScheme, U)),
      (C.G.toScheme.presheaf.germ U w hU).hom s ∈ IsLocalRing.maximalIdeal _ ↔
        w ∉ C.G.toScheme.basicOpen s := by
    intro U hU s
    rw [C.G.toScheme.mem_basicOpen s w hU, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hle : IsLocalRing.maximalIdeal (C.G.toScheme.presheaf.stalk w) ≤ P := by
    refine hco.le.trans (sup_le ?_ ?_)
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      have h1 : w ∉ C.G.toScheme.basicOpen (u i) := by
        rw [← hm W hw]
        exact hco.ge (Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩))
      have e : ∀ t : W.toScheme, t.1 ∈ C.G.toScheme.basicOpen (u i) ↔
          f t ∈ Scheme.basicOpen _ (AffineSpace.coord C.Z i) := by
        intro t
        have e1 : f ⁻¹ᵁ Scheme.basicOpen _ (AffineSpace.coord C.Z i) =
            W.toScheme.basicOpen (W.topIso.inv.hom (u i)) := by
          rw [Scheme.preimage_basicOpen_top, hf, AffineSpace.homOfVector_appTop_coord]
        have e2 := W.ι_image_basicOpen_topIso_inv (u i)
        rw [← e2, ← e1]
        exact Scheme.Hom.apply_mem_image_iff W.ι (x := t)
      refine (hP W hw (u i)).2 ?_
      rw [e y, hfy, ← e ⟨w, hw⟩]
      exact h1
    · refine (Ideal.IsPrime.radical_le_iff inferInstance).2 ?_
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      obtain ⟨V, hV, s, rfl⟩ := C.Z.presheaf.exists_germ_eq a
      rw [Ideal.mem_comap, Scheme.Hom.germ_stalkMap_apply]
      refine (hP _ _ _).2 ?_
      have h1 : C.GG.hom w ∉ C.Z.basicOpen s := by
        rw [C.Z.mem_basicOpen s _ hV]
        exact ha
      rw [← hg] at h1
      intro h2
      apply h1
      have e := Scheme.preimage_basicOpen C.GG.hom s
      exact e.ge h2
  apply eq_of_specializes_of_basicOpen hy'
  intro U hU s hs
  by_contra hn
  exact (hP U hU s).1 (hle ((hm U hU s).2 hn)) hs
end GlobalTheory
