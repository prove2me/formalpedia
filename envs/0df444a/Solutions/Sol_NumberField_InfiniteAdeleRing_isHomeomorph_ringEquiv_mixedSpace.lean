-- Prove2me | solution 1 for NumberField.InfiniteAdeleRing.isHomeomorph_ringEquiv_mixedSpace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/bc54b63f-8785-5708-bb9d-8dda3ab4ad1a

import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_InfiniteAdeleRing_isHomeomorph_ringEquiv_mixedSpace

set_option autoImplicit false

p2m_open "NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion NumberField.InfiniteAdeleRing"

namespace P2mMixedHomeo

variable (K : Type) [Field K]

theorem continuous_ringEquiv_mixedSpace : Continuous (ringEquiv_mixedSpace K) := by
  refine continuous_prodMk.2 ⟨continuous_pi fun v => ?_, continuous_pi fun v => ?_⟩
  · exact (isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

theorem continuous_ringEquiv_mixedSpace_symm : Continuous (ringEquiv_mixedSpace K).symm := by
  apply continuous_pi
  intro v
  by_cases hv : IsReal v
  · have key : (fun y : mixedEmbedding.mixedSpace K => (ringEquiv_mixedSpace K).symm y v)
        = fun y => (isometryEquivRealOfIsReal hv).symm (y.1 ⟨v, hv⟩) := by
      funext y
      apply (isometryEquivRealOfIsReal hv).injective
      rw [IsometryEquiv.apply_symm_apply]
      exact congrArg (fun z : mixedEmbedding.mixedSpace K => z.1 ⟨v, hv⟩)
        ((ringEquiv_mixedSpace K).apply_symm_apply y)
    rw [key]
    exact (isometryEquivRealOfIsReal hv).symm.continuous.comp
      ((continuous_apply _).comp continuous_fst)
  · have hc : IsComplex v := not_isReal_iff_isComplex.1 hv
    have key : (fun y : mixedEmbedding.mixedSpace K => (ringEquiv_mixedSpace K).symm y v)
        = fun y => (isometryEquivComplexOfIsComplex hc).symm (y.2 ⟨v, hc⟩) := by
      funext y
      apply (isometryEquivComplexOfIsComplex hc).injective
      rw [IsometryEquiv.apply_symm_apply]
      exact congrArg (fun z : mixedEmbedding.mixedSpace K => z.2 ⟨v, hc⟩)
        ((ringEquiv_mixedSpace K).apply_symm_apply y)
    rw [key]
    exact (isometryEquivComplexOfIsComplex hc).symm.continuous.comp
      ((continuous_apply _).comp continuous_snd)

noncomputable def mixedHomeo : InfiniteAdeleRing K ≃ₜ mixedEmbedding.mixedSpace K where
  toEquiv := (ringEquiv_mixedSpace K).toEquiv
  continuous_toFun := continuous_ringEquiv_mixedSpace K
  continuous_invFun := continuous_ringEquiv_mixedSpace_symm K

theorem main : IsHomeomorph (ringEquiv_mixedSpace K) :=
  (mixedHomeo K).isHomeomorph

end P2mMixedHomeo

theorem solution (K : Type) [Field K] :
    IsHomeomorph (InfiniteAdeleRing.ringEquiv_mixedSpace K) :=
  P2mMixedHomeo.main K

end S_NumberField_InfiniteAdeleRing_isHomeomorph_ringEquiv_mixedSpace
end P2MW
export P2MW.S_NumberField_InfiniteAdeleRing_isHomeomorph_ringEquiv_mixedSpace (solution)
