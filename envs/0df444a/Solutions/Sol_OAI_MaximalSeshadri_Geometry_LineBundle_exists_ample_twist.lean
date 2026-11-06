-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.LineBundle.exists_ample_twist
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:47:45.074265+00:00
-- url     : https://prove2.me/submissions/bb371366-3cb7-48e6-8733-254b5d0071ad
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_LineBundle_ample_framed_cover
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_LineBundle_mixed_frame_extension
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_LineBundle_ample_of_affine_section_cover

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open OAI.MaximalSeshadri
open OAI.MaximalSeshadri.Geometry
open OAI.MaximalSeshadri.Frames OAI.MaximalSeshadri.Projective OAI.MaximalSeshadri.TensorPure

variable {X : Scheme.{0}}

private lemma sectionOpen_postcomp {M N P : X.Modules} (f : M ⟶ N) (e : N ≅ P) :
    SectionOpens.isoOpen (f ≫ e.hom) = SectionOpens.isoOpen f := by
  apply le_antisymm
  · intro x hx
    obtain ⟨U, hxU, hU⟩ := (SectionOpens.mem_isoOpen_iff (f ≫ e.hom) x).mp hx
    refine (SectionOpens.mem_isoOpen_iff f x).mpr ⟨U, hxU, ?_⟩
    rw [Functor.map_comp] at hU
    let := hU
    exact IsIso.of_isIso_comp_right
      ((Scheme.Modules.restrictFunctor U.ι).map f)
      ((Scheme.Modules.restrictFunctor U.ι).map e.hom)
  · intro x hx
    obtain ⟨U, hxU, hU⟩ := (SectionOpens.mem_isoOpen_iff f x).mp hx
    refine (SectionOpens.mem_isoOpen_iff (f ≫ e.hom) x).mpr ⟨U, hxU, ?_⟩
    rw [Functor.map_comp]
    let := hU
    infer_instance

theorem solution [IsIntegral X] [CompactSpace X]
    (L M : LineBundle X) (hL : L.IsAmple) :
    ∃ d : ℕ, 0 < d ∧ ((L.pow d).tensor M).IsAmple := by
  classical
  obtain ⟨a,ha,-,ι,hi,s,hs,hsa,hsn,he⟩ := L.ample_framed_cover M hL 1 (by decide)
  choose N hN using fun i => (L.pow a).mixed_frame_extension M (s i) (hsn i)
    (Classical.choice (he i))
  let n := Finset.univ.sup N
  choose t ht hval using fun i => hN i n (Finset.le_sup (Finset.mem_univ i))
  let e : (((L.pow a).pow (n+1)).tensor M).sheaf ≅ ((L.pow (a*(n+1))).tensor M).sheaf :=
    moduleTensorIso (linePowerMul L a (n+1)) (Iso.refl M.sheaf)
  let q (i : ι) : O X ⟶ ((L.pow (a*(n+1))).tensor M).sheaf := t i ≫ e.hom
  have hq (i : ι) : sectionOpen X (q i) = sectionOpen X (s i) := by
    exact (sectionOpen_postcomp (t i) e).trans (ht i)
  refine ⟨a*(n+1),Nat.mul_pos ha (by omega),
    ((L.pow (a*(n+1))).tensor M).ample_of_affine_section_cover q ?_ ?_⟩
  · simpa only [hq] using hs
  · intro i
    rw [hq]
    exact hsa i
