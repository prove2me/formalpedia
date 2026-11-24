-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Red.balanced_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:30:50.713786+00:00
-- url     : https://prove2.me/submissions/3d5f906c-df6e-456f-9ec4-e29434161dc7

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsCuspReductionBoundStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MobiusActionUpperHalfPlaneStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CuspRepresentativesFiniteStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitBalancingImaginaryPartsStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ReductionToSiegelDomain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Red
namespace GlobalTheory.CompanionTheory.SW.Red
theorem _root_.solution {ι : Type} [Fintype ι] (z : ι → ℝ) (hz : ∀ i, 0 < z i) (κ P : ℝ)
    (hκ : 0 < κ) (hbal : ∀ v w, κ * z w ≤ z v) (hprod : P ≤ ∏ i, z i) (w : ι) :
    κ * min 1 P ≤ z w := by
  by_contra h
  push_neg at h
  set q := z w / κ with hq
  have hqpos : 0 < q := div_pos (hz w) hκ
  have hqlt : q < min 1 P := by
    rw [hq, div_lt_iff₀ hκ]; linarith
  have hq1 : q ≤ 1 := (hqlt.trans_le (min_le_left _ _)).le
  have hqP : q < P := hqlt.trans_le (min_le_right _ _)
  have hle : ∀ v, z v ≤ q := by
    intro v
    rw [hq, le_div_iff₀ hκ]
    have := hbal w v
    linarith
  haveI : Nonempty ι := ⟨w⟩
  have hcard : Fintype.card ι ≠ 0 := Fintype.card_ne_zero
  have hp : ∏ i, z i ≤ q ^ Fintype.card ι := by
    calc ∏ i, z i ≤ ∏ _i : ι, q :=
          Finset.prod_le_prod (fun i _ => (hz i).le) (fun i _ => hle i)
      _ = q ^ Fintype.card ι := by simp
  have := pow_le_of_le_one hqpos.le hq1 hcard
  linarith
end GlobalTheory.CompanionTheory.SW.Red
