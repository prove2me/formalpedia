-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.SizeScale.continuous_size
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:32:20.547295+00:00
-- url     : https://prove2.me/submissions/353baf5d-572e-4cb8-b917-ea967fb14632

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsSizeMulLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.SizeScale
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
namespace GlobalTheory.CompanionTheory.SW.SizeScale
theorem _root_.solution (b : Module.Basis (Fin d) F E) :
    Continuous (sizeInf b : Ainf F ⊗[F] E → ℝ) := by
  have : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩
  unfold sizeInf
  refine continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun v _ => ?_
  have hk : Continuous fun y : Ainf F ⊗[F] E =>
      (Algebra.TensorProduct.basis (Ainf F) b).coord k y :=
    IsModuleTopology.continuous_of_linearMap _
  simp only [← Module.Basis.coord_apply]
  exact continuous_norm.comp ((continuous_apply v).comp hk)
end GlobalTheory.CompanionTheory.SW.SizeScale
