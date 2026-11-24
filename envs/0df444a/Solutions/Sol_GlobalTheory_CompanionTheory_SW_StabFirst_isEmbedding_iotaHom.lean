-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.StabFirst.isEmbedding_iotaHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:20:55.611202+00:00
-- url     : https://prove2.me/submissions/2c2685ea-cd3e-4782-8074-ea581b7fd677

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneRightInjective
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_StabFirst_isEmbedding_pairMap
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_StabFirst_continuous_iotaHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.StabFirst
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (s : E)
variable [TopologicalSpace R]
namespace GlobalTheory.CompanionTheory.SW.StabFirst
theorem _root_.solution : IsEmbedding (iotaHom R σ J s) := by
  have hp := (isEmbedding_pairMap R σ (blockOne s J)).continuous
  let P : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E) × (Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E))ᵐᵒᵖ →
      Matrix (Fin M) (Fin M) (R ⊗[F] E) × (Matrix (Fin M) (Fin M) (R ⊗[F] E))ᵐᵒᵖ :=
    fun p => (p.1.submatrix Fin.succ Fin.succ,
      MulOpposite.op ((MulOpposite.unop p.2).submatrix Fin.succ Fin.succ))
  have hP : Continuous P := by
    refine Continuous.prodMk ?_ ?_
    · exact continuous_fst.matrix_submatrix _ _
    · exact MulOpposite.continuous_op.comp
        ((MulOpposite.continuous_unop.comp continuous_snd).matrix_submatrix _ _)
  refine IsEmbedding.of_comp (continuous_iotaHom R σ J s) (hP.comp hp) ?_
  have : (P ∘ pairMap R σ (blockOne s J)) ∘ iotaHom R σ J s = pairMap R σ J := by
    funext u
    rfl
  rw [this]
  exact isEmbedding_pairMap R σ J
end GlobalTheory.CompanionTheory.SW.StabFirst
