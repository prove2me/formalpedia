-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.PureH.prod_union_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:45.607607+00:00
-- url     : https://prove2.me/submissions/13a3519f-c5ee-4799-9a1c-bfd6f0c028dc

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneDetHermitianGram
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupProjections
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeStableAlmostEverywhere
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryFiniteSetDecomposition

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PureH
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  [DecidableEq (HeightOneSpectrum (𝓞 F))]
namespace GlobalTheory.CompanionTheory.SW.PureH
theorem _root_.solution {ι : Type} [DecidableEq ι] (S Sh : Finset ι) (A B : ι → ℝ≥0∞) (P : ι → Prop)
    [DecidablePred P] (hS : ∀ v, P v ↔ v ∈ S) :
    ∏ v ∈ S ∪ Sh, (if P v then A v else B v) = (∏ v ∈ S, A v) * ∏ v ∈ Sh \ S, B v := by
  rw [← Finset.union_sdiff_self_eq_union, Finset.prod_union Finset.disjoint_sdiff]
  congr 1
  · exact Finset.prod_congr rfl fun v hv => if_pos ((hS v).2 hv)
  · exact Finset.prod_congr rfl fun v hv => if_neg fun h => (Finset.mem_sdiff.1 hv).2 ((hS v).1 h)
end GlobalTheory.CompanionTheory.SW.PureH
