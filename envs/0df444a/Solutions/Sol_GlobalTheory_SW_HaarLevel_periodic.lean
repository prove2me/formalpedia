-- Prove2me | solution 1 for GlobalTheory.SW.HaarLevel.periodic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:09:11.68612+00:00
-- url     : https://prove2.me/submissions/ab3930f4-e7ca-42a7-89cd-61be8f3854ba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
import Theorems.Thm_GlobalTheory_SW_HaarLevel_intM_iff
import Theorems.Thm_GlobalTheory_SW_HaarLevel_mem_perSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HaarLevel
noncomputable section
open NumberField
variable {K : Type} [Field K] [NumberField K] {κ ι : Type} [Fintype κ] [Fintype ι]
omit [NumberField K] [Fintype κ] [Fintype ι]
namespace GlobalTheory.SW.HaarLevel
theorem _root_.solution {R : ℕ} {φ : Matrix κ ι K → ℂ} (h : HasLevel R φ) (x : Matrix κ ι K) :
    ∀ y ∈ perSub K κ ι R, φ (x + y) = φ x := by
  intro y hy
  obtain ⟨z, rfl⟩ := (mem_perSub _ _).1 hy
  rw [← Nat.cast_smul_eq_nsmul K]
  exact h.2 x _ ((intM_iff _).2 ⟨z, rfl⟩)
end GlobalTheory.SW.HaarLevel
