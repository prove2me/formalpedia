-- Prove2me | solution 1 for GlobalTheory.LGrp.HasGJValue.unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:35:05.941399+00:00
-- url     : https://prove2.me/submissions/c2c74a58-4b32-4d9e-92fd-c30f385c4ef8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Theorems.Thm_GlobalTheory_LGrp_HasGJ_unique
import Theorems.Thm_GlobalTheory_SplitWeil_one_lt_resCard


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open GlobalTheory GlobalTheory.LGrp
open ValuativeRel GlobalTheory.SplitWeil
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]
variable [MeasurableSpace (GL n k)]
variable {μ : Measure (GL n k)} {Ξ : Matrix n n k → ℂ} {c : GL n k → ℂ}
namespace GlobalTheory.LGrp
namespace HasGJValue
theorem _root_.solution {z₀ w w' : ℂ} (h : HasGJValue μ Ξ c z₀ w) (h' : HasGJValue μ Ξ c z₀ w') : w = w' :=
  h.2.unique (one_lt_resCard k) h'.2
end HasGJValue
end GlobalTheory.LGrp
