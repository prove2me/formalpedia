-- Prove2me | solution 1 for GlobalTheory.KTypeSteps.kSpan_le_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:29:43.729949+00:00
-- url     : https://prove2.me/submissions/3c66ed34-2088-47f5-8457-a4e724753266

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_QuotientSettingHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_KtypesWithinSteps
import Theorems.Thm_Formalism_REAL_glRel_kRel
import Theorems.Thm_Formalism_REAL_isUnitary_kUnit
import Theorems.Thm_Formalism_REAL_kOrth
import Theorems.Thm_Formalism_REAL_mem_compact_span_self_general


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.KTypeSteps
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
namespace GlobalTheory.KTypeSteps
theorem _root_.solution {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V}
    (hg : GlRel E) (hu : IsUnitary ε E) {μ ν : Fin n → ℝ} {x y : V}
    (hx : KHighest ε E μ x) (hy : KHighest ε E ν y) (hne : μ ≠ ν) :
    kSpan ε E y ≤ LinearMap.ker (innerₛₗ ℂ x) := by
  intro z hz
  rw [LinearMap.mem_ker, innerₛₗ_apply_apply]
  exact kOrth V n ε E μ ν x y (glRel_kRel ε E hg) (isUnitary_kUnit ε E hu) hx hy hne x
    (mem_compact_span_self_general x) z hz
end GlobalTheory.KTypeSteps
