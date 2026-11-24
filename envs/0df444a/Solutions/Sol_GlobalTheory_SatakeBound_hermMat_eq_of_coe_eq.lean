-- Prove2me | solution 1 for GlobalTheory.SatakeBound.hermMat_eq_of_coe_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:46:57.910531+00:00
-- url     : https://prove2.me/submissions/09f09b8b-9575-4fc2-8c56-06ae6775a221

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_SatakeTrivialRangeBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelativeLatticeVolumeOfDetValuation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsBorelSphRevInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HermiteReductionUnipotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Theorems.Thm_GlobalTheory_SatakeBound_mapMatrix_inj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel
open GlobalTheory GlobalTheory.SatakeBound
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {p : 𝒪[k]}
namespace GlobalTheory.SatakeBound
theorem _root_.solution (hp : Irreducible p) {a a' : Fin n → ℕ} {c : HermIdx p a} {c' : HermIdx p a'}
    (h : (hermGL hp a' c' : GL (Fin n) k ⧸ KO k (Fin n)) = hermGL hp a c) :
    ∃ W, hermMat p a c = hermMat p a' c' * W := by
  obtain ⟨W, hW⟩ := QuotientGroup.eq.1 h
  refine ⟨W, mapMatrix_inj ?_⟩
  rw [eq_inv_mul_iff_mul_eq] at hW
  rw [map_mul]
  exact (congrArg Units.val hW).symm
end GlobalTheory.SatakeBound
