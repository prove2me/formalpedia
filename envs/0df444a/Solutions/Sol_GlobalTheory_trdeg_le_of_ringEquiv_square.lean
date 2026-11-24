-- Prove2me | solution 1 for GlobalTheory.trdeg_le_of_ringEquiv_square
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:38:53.958194+00:00
-- url     : https://prove2.me/submissions/e13fb039-d436-4fa2-8f53-863586ae5a49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ResidueFieldIsoInvCompSpec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K L K' L' : Type} [Field K] [Field L] [Field K'] [Field L']
    (f : K →+* L) (f' : K' →+* L') (eK : K ≃+* K') (eL : L ≃+* L')
    (h : f'.comp (eK : K →+* K') = (eL : L →+* L').comp f) :
    @Algebra.trdeg K L _ _ f.toAlgebra ≤ @Algebra.trdeg K' L' _ _ f'.toAlgebra := by
  letI := f.toAlgebra
  letI := f'.toAlgebra
  haveI : FaithfulSMul K L := (faithfulSMul_iff_algebraMap_injective K L).mpr f.injective
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K L
  rw [← hs.cardinalMk_eq_trdeg]
  have hi : AlgebraicIndependent K' ((eL : L → L') ∘ ((↑) : s → L)) :=
    (algebraicIndependent_ringHom_iff_of_comp_eq eK (eL : L →+* L') eL.injective h).mpr hs.1
  simpa using hi.lift_cardinalMk_le_trdeg
end GlobalTheory
