-- Prove2me | solution 1 for GlobalTheory.QNorm.IsQuad.finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:48.625292+00:00
-- url     : https://prove2.me/submissions/346a7b8d-e0d3-4658-9833-a8f7cee12376

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsQuadraticSqrtExtensionBasicFacts
import Theorems.Thm_GlobalTheory_QNorm_IsQuad_coord_indep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
variable {F E : Type} [Field F] [Field E] [Algebra F E] {δ : F} {θ : E} {σ : E ≃ₐ[F] E}
namespace GlobalTheory.QNorm
namespace IsQuad
theorem _root_.solution (h : IsQuad δ θ σ) : Module.finrank F E = 2 := by
  have hli : LinearIndependent F ![(1 : E), θ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    apply h.coord_indep
    simpa [Algebra.smul_def] using hst
  have hsp : ⊤ ≤ Submodule.span F (Set.range ![(1 : E), θ]) := by
    intro x _
    obtain ⟨a, b, rfl⟩ := h.span x
    refine Submodule.add_mem _ ?_ ?_
    · rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
    · rw [← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)
  simpa using Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)
end IsQuad
end GlobalTheory.QNorm
