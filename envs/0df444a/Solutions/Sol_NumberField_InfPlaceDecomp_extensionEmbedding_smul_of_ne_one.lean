-- Prove2me | solution 1 for NumberField.InfPlaceDecomp.extensionEmbedding_smul_of_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/b15491bc-502f-59fb-9e1e-e8e954a14509

import Mathlib
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_InfPlaceDecomp_extensionEmbedding_smul_of_ne_one

set_option autoImplicit false
open NumberField
open scoped NumberField.InfPlaceDecomp

namespace P2mS26A1
open NumberField.InfPlaceDecomp

theorem isConj_embedding_of_ne_one {E K : Type*} [Field E] [Field K] [Algebra E K] {w : InfinitePlace K}
    (σ : decomp E K w) (hσ : σ ≠ 1) : ComplexEmbedding.IsConj w.embedding (σ : K ≃ₐ[E] K) := by
  have h : (σ : K ≃ₐ[E] K) ∈ MulAction.stabilizer (K ≃ₐ[E] K) (InfinitePlace.mk w.embedding) := by
    rw [InfinitePlace.mk_embedding]; exact σ.2
  rcases (InfinitePlace.mem_stabilizer_mk_iff w.embedding (σ : K ≃ₐ[E] K)).1 h with h1 | h2
  · exact absurd (Subtype.ext h1) hσ
  · exact h2

theorem extensionEmbedding_smul_coe {E K : Type*} [Field E] [Field K] [Algebra E K] {w : InfinitePlace K}
    (σ : decomp E K w) (hσ : σ ≠ 1) (y : WithAbs w.1) :
    InfinitePlace.Completion.extensionEmbedding w (σ • (y : w.Completion)) =
      starRingEnd ℂ (InfinitePlace.Completion.extensionEmbedding w (y : w.Completion)) := by
  rw [smul_def, actRingEquiv_coe, InfinitePlace.Completion.extensionEmbedding_coe,
    InfinitePlace.Completion.extensionEmbedding_coe, WithAbs.congr_apply, WithAbs.equiv_apply, WithAbs.equiv_apply]
  change w.embedding ((σ : K ≃ₐ[E] K) y.ofAbs) = _
  exact (isConj_embedding_of_ne_one σ hσ).eq y.ofAbs

end P2mS26A1

open P2mS26A1 NumberField.InfPlaceDecomp in

theorem solution (E K : Type*) [Field E] [Field K] [Algebra E K]
    (w : InfinitePlace K) (σ : NumberField.InfPlaceDecomp.decomp E K w) (hσ : σ ≠ 1) (x : w.Completion) :
    InfinitePlace.Completion.extensionEmbedding w (σ • x) =
      starRingEnd ℂ (InfinitePlace.Completion.extensionEmbedding w x) := by
  refine InfinitePlace.Completion.induction_on _ x ?_ (fun y => extensionEmbedding_smul_coe σ hσ y)
  exact isClosed_eq ((InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (NumberField.InfPlaceDecomp.continuous_actRingEquiv σ))
    (Complex.continuous_conj.comp (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous)

end S_NumberField_InfPlaceDecomp_extensionEmbedding_smul_of_ne_one
end P2MW
export P2MW.S_NumberField_InfPlaceDecomp_extensionEmbedding_smul_of_ne_one (solution)
