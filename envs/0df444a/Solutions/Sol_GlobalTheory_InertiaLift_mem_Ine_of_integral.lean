-- Prove2me | solution 1 for GlobalTheory.InertiaLift.mem_Ine_of_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:47:54.577044+00:00
-- url     : https://prove2.me/submissions/aaf11f0c-0976-4cb9-a94f-7950d5925b5e

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteGaloisInertiaLiftsAbsoluteInertiaRat
import Theorems.Thm_ReciprocityTheory_Gal_exists_den


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField Pointwise
open GlobalTheory GlobalTheory.InertiaLift
variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
namespace GlobalTheory.InertiaLift
theorem _root_.solution {A : ValuationSubring Ω} {σ : G F Ω} (hσ : σ ∈ Dec (F := F) A)
    (h : ∀ b : Ω, IsIntegral ℤ b → A.valuation (σ b - b) < 1) : σ ∈ Ine (F := F) A := by
  refine ⟨hσ, fun x hx => ?_⟩
  obtain ⟨s, t, hs, ht, hs1, e⟩ := exists_den F A hx
  have hσs : A.valuation (σ s) = 1 := by
    refine le_antisymm ((A.valuation_le_one_iff _).mpr ((apply_mem_iff_of_mem_Dec hσ s).mpr
      (mem_of_isIntegral_int A hs))) ?_
    rw [← not_lt, valuation_apply_lt_one_iff hσ, hs1]
    exact lt_irrefl 1
  have he' : σ s * σ x = σ t := by rw [← map_mul, e]
  have key : σ s * (σ x - x) = (σ t - t) + x * (s - σ s) := by
    rw [← he', ← e]; ring
  have hv : A.valuation (σ s * (σ x - x)) < 1 := by
    rw [key]
    refine Valuation.map_add_lt _ (h t ht) ?_
    rw [Valuation.map_mul, Valuation.map_sub_swap]
    calc A.valuation x * A.valuation (σ s - s) ≤ 1 * A.valuation (σ s - s) :=
          mul_le_mul_left hx _
      _ < 1 := by rw [one_mul]; exact h s hs
  rwa [Valuation.map_mul, hσs, one_mul] at hv
end GlobalTheory.InertiaLift
