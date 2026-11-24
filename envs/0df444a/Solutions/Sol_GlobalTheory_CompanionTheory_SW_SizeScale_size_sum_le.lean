-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.SizeScale.size_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:56:07.420415+00:00
-- url     : https://prove2.me/submissions/17495237-f393-465f-8036-2166cc08ae1d

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsSizeMulLe
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_SizeScale_size_add_le
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_SizeScale_size_zero

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
theorem _root_.solution {ι : Type} (b : Module.Basis (Fin d) F E) (s : Finset ι)
    (f : ι → Ainf F ⊗[F] E) : sizeInf b (∑ c ∈ s, f c) ≤ ∑ c ∈ s, sizeInf b (f c) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [size_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (size_add_le b _ _).trans (by gcongr)
end GlobalTheory.CompanionTheory.SW.SizeScale
