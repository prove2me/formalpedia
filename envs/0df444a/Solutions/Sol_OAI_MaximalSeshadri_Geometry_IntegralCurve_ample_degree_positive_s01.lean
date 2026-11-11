-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.IntegralCurve.ample_degree_positive_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:12:19.157627+00:00
-- url     : https://prove2.me/submissions/cd033841-bade-4c64-8380-eea9351841cb

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES009
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_IntegralCurve_exists_projective_sections_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_curveDegree_pow_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_projective_section_positive_degree_s01

section
-- module Solutions.Q223_SES.Seshadri_Intersection_AmpleCurveDegree
attribute [-instance] _root_.OAI.MaximalSeshadri.AffineBlowup.scheme_isReduced _root_.OAI.MaximalSeshadri.BlowupGluing.scheme_isReduced _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                          
section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open MaximalSeshadri.Projective MaximalSeshadri.Frames MaximalSeshadri.SectionOpens

variable {X : Scheme.{0}}

lemma section_ne_zero_of_mem_isoOpen (L : LineBundle X) (s : O X ⟶ L.sheaf)
    (x : X) (hx : x ∈ isoOpen s) : s ≠ 0 := by
  obtain ⟨U,hxU,⟨e⟩⟩ := L.locallyRankOne x
  have hm : (⟨x,hxU⟩ : U.toScheme) ∈ U.ι ⁻¹ᵁ isoOpen s := hx
  rw [preimage_isoOpen s U.ι e] at hm
  intro hz
  subst s
  rw [restrictSection_zero,coefficient_zero (X := U.toScheme) e,
    Scheme.basicOpen_zero] at hm
  exact hm

lemma exists_proper_nonempty_open [IsIntegral X] (hd : topologicalKrullDim X = 1) :
    ∃ (U : X.Opens) (x : X), x ∈ U ∧ U ≠ ⊤ := by
  have ht : Nontrivial X := by
    by_contra hn
    let : Subsingleton X := not_nontrivial_iff_subsingleton.mp hn
    have hh := topologicalKrullDim_zero_of_discreteTopology X
    rw [hd] at hh
    norm_num at hh
  let := ht
  obtain ⟨x,y,hxy⟩ := exists_pair_ne X
  obtain ⟨U,hU,hxyU⟩ := exists_isOpen_xor_mem hxy
  rcases hxyU with ⟨hx,hy⟩ | ⟨hx,hy⟩
  · refine ⟨⟨U,hU⟩,x,hx,?_⟩
    intro hh
    have : y ∈ (⟨U,hU⟩ : X.Opens) := by rw [hh]; trivial
    exact hy this
  · refine ⟨⟨U,hU⟩,y,hx,?_⟩
    intro hh
    have : x ∈ (⟨U,hU⟩ : X.Opens) := by rw [hh]; trivial
    exact hy this

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_PullbackSectionOpenExact
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                                  
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective MaximalSeshadri.SectionOpens

variable {X Y : Scheme.{0}}

theorem pullback_isoOpen_eq (L : LineBundle X) (s : O X ⟶ L.sheaf) (f : Y ⟶ X) :
    isoOpen (pullbackSection f s) = f ⁻¹ᵁ isoOpen s := by
  ext y
  obtain ⟨U,hy,⟨e⟩⟩ := L.locallyRankOne (f y)
  obtain ⟨eF,he⟩ := exists_restricted_pullback_frame_all f U e
  calc
    y ∈ isoOpen (pullbackSection f s) ↔
        (⟨y,hy⟩ : (f ⁻¹ᵁ U).toScheme) ∈ (f ⁻¹ᵁ U).toScheme.basicOpen
          (coefficient eF (restrictSection (f ⁻¹ᵁ U).ι (pullbackSection f s))) :=
      (congrArg (fun V => (⟨y,hy⟩ : (f ⁻¹ᵁ U).toScheme) ∈ V)
        (preimage_isoOpen (pullbackSection f s) (f ⁻¹ᵁ U).ι eF)).to_iff
    _ ↔ (⟨f y,hy⟩ : U.toScheme) ∈ U.toScheme.basicOpen
          (coefficient e (restrictSection U.ι s)) := by
      rw [he,← Scheme.preimage_basicOpen_top]
      change (f ∣_ U) ⟨y,hy⟩ ∈ U.toScheme.basicOpen
        (coefficient e (restrictSection U.ι s)) ↔ _
      rw [morphismRestrict_base]
      rfl
    _ ↔ f y ∈ isoOpen s :=
      (congrArg (fun V => (⟨f y,hy⟩ : U.toScheme) ∈ V)
        (preimage_isoOpen s U.ι e)).to_iff.symm

theorem IntegralCurve.exists_positive_ambient_power (S : Surface) (C : IntegralCurve S)
    (L : LineBundle S.scheme) (hL : L.IsAmple) :
    ∃ m : ℕ, 0 < m ∧ 0 < curveDegree S (L.pow m) C := by
  obtain ⟨U,x,hx,hU⟩ := exists_proper_nonempty_open C.dimension
  have hUC : IsOpen (U : Set C.scheme) := U.isOpen
  obtain ⟨V,hV,hVU⟩ := C.embedding.isClosedEmbedding.isInducing.isOpen_iff.mp hUC
  let W : S.scheme.Opens := ⟨V,hV⟩
  have hxW : C.embedding x ∈ W := by
    change x ∈ C.embedding ⁻¹' V
    rw [hVU]
    exact hx
  obtain ⟨m,hm,s,hxs,hsW,_⟩ := hL (C.embedding x) W hxW
  let t : O C.scheme ⟶ ((L.pow m).pullback C.embedding).sheaf :=
    pullbackSection C.embedding s
  have htopen : isoOpen t = C.embedding ⁻¹ᵁ isoOpen s :=
    pullback_isoOpen_eq (L.pow m) s C.embedding
  have hxt : x ∈ isoOpen t := by
    rw [htopen]
    exact hxs
  have ht : t ≠ 0 := section_ne_zero_of_mem_isoOpen
    ((L.pow m).pullback C.embedding) t x hxt
  have hproper : isoOpen t ≠ ⊤ := by
    intro he
    apply hU
    apply top_unique
    intro y _hy
    have hyt : y ∈ isoOpen t := by rw [he]; trivial
    rw [htopen] at hyt
    have hyW := hsW hyt
    change y ∈ (U : Set C.scheme)
    rw [← hVU]
    exact hyW
  obtain ⟨σ,hσ,B,a,ha,hc⟩ := C.exists_projective_sections_s01 S L hL
  let := hσ
  let := hc
  refine ⟨m,hm,?_⟩
  exact projective_section_positive_degree_s01 (C.embedding ≫ S.structureMap)
    C.dimension a ha ((L.pow m).pullback C.embedding) t ht hproper

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_SurfacePositiveSquare
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

theorem IntegralCurve.ample_degree_positive_s01_oai (S : Surface) (C : IntegralCurve S)
    (L : LineBundle S.scheme) (hL : L.IsAmple) : 0 < curveDegree S L C := by
  obtain ⟨m,hm,hp⟩ := C.exists_positive_ambient_power S L hL
  rw [curveDegree_pow_s01 S L hL] at hp
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  nlinarith

end
end MaximalSeshadri.Geometry

end

end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Geometry.IntegralCurve.ample_degree_positive_s01_oai := @OAI.MaximalSeshadri.Geometry.IntegralCurve.ample_degree_positive_s01_oai
