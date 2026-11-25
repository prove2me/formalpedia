-- Prove2me | solution 1 for GlobalTheory.ArchMetric.muMax_sq_eq_iSup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:29:22.846998+00:00
-- url     : https://prove2.me/submissions/1142dede-6250-4530-963b-037f7fd9f085

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsSmulMemOfMemSpanLattice
import Theorems.Thm_GlobalTheory_ArchMetric_muMax_sq_le_coe_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
open scoped ComplexOrder ComplexConjugate
open GlobalTheory
open GlobalTheory.ArchMetric
variable {K : Type*} [Field K] [NumberField K] {V V' : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h : ArchMetric K V)
variable {A B : Submodule (𝓞 K) V}
namespace GlobalTheory.ArchMetric
theorem _root_.solution (A : Submodule (𝓞 K) V) :
    h.muMax_sq A = ⨆ (B : Submodule (𝓞 K) V) (_ : B ≤ A) (_ : B ≠ ⊥), (h.slope_sq B : EReal) := by
  have key : ∀ c : ℝ, h.muMax_sq A ≤ c ↔
      (⨆ (B : Submodule (𝓞 K) V) (_ : B ≤ A) (_ : B ≠ ⊥), (h.slope_sq B : EReal)) ≤ c := fun c => by
    simp only [muMax_sq_le_coe_iff, iSup_le_iff, EReal.coe_le_coe_iff]
  exact le_antisymm (EReal.le_of_forall_lt_iff_le.1 fun z hz => (key z).2 hz.le)
    (EReal.le_of_forall_lt_iff_le.1 fun z hz => (key z).1 hz.le)
end GlobalTheory.ArchMetric
