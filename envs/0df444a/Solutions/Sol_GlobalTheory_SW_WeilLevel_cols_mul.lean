-- Prove2me | solution 1 for GlobalTheory.SW.WeilLevel.cols_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:04.771822+00:00
-- url     : https://prove2.me/submissions/0a2e1673-acca-4db3-afbc-163276fc6658

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_NotAdmissibleHalfLatticeFamily
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianHeisenbergOperatorLaws
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.WeilLevel
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ} {Λ : Lt E n}
omit [IsCMField E]
namespace GlobalTheory.SW.WeilLevel
theorem _root_.solution {d b : Matrix (Fin n) (Fin N) E} (hd : ColsIn Λ d) (hb : ColsIn Λ b)
    {g : M2 E N} (hg : IntM g) (i : Fin N ⊕ Fin N) : (Matrix.fromCols d b * g)ᵀ i ∈ Λ := by
  have : (Matrix.fromCols d b * g)ᵀ i =
      ∑ j, (⟨g j i, hg j i⟩ : 𝓞 E) • (Matrix.fromCols d b)ᵀ j := by
    ext k
    rw [Finset.sum_apply, Matrix.transpose_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [this]
  refine Λ.sum_mem fun j _ => Λ.smul_mem _ ?_
  rcases j with j | j
  · exact hd j
  · exact hb j
end GlobalTheory.SW.WeilLevel
