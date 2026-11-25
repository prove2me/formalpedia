-- Prove2me | solution 1 for GlobalTheory.IsogenySum.translate_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:16:25.719175+00:00
-- url     : https://prove2.me/submissions/a7d3d50b-48f8-4f69-b649-035c6fc96de7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FockTranslationLaws
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ContinuousThetaSectionPointwiseNormSq
import Theorems.Thm_GlobalTheory_fock_translation_laws


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Complex ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory
open GlobalTheory.IsogenySum
open FockTranslation
variable {ι : Type} [Fintype ι]
variable (U : ℕ → EuclideanSpace ℂ ι → (EuclideanSpace ℂ ι → ℂ) → EuclideanSpace ℂ ι → ℂ)
  (hU : ∀ (q : ℕ) a F v, U q a F v =
    cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * F (v - a))
include hU
namespace GlobalTheory.IsogenySum
theorem _root_.solution (Y : GT ι)
    (hY : ∀ x ∈ lat Y.b, ∀ y ∈ lat Y.b,
      Y.ka (x + y) = Y.ka x * Y.ka y * cexp (Real.pi * I * (Hf x y).im))
    {x y : EuclideanSpace ℂ ι} (hx : x ∈ lat Y.b) (hy : y ∈ lat Y.b)
    (F : EuclideanSpace ℂ ι → ℂ) :
    Y.ka x • U 1 x (Y.ka y • U 1 y F) = Y.ka (x + y) • U 1 (x + y) F := by
  have h1 := (fock_translation_laws U hU 1).1 x y F
  have e : U 1 x (Y.ka y • U 1 y F) = Y.ka y • U 1 x (U 1 y F) := by
    funext v
    simp only [Pi.smul_apply, smul_eq_mul, hU 1 x]
    ring
  rw [e, h1, hY x hx y hy, smul_smul, smul_smul]
  congr 2
  obtain ⟨k, hk⟩ := Y.integral x y hx hy
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-k, ?_⟩
  rw [hk]
  push_cast
  ring
end GlobalTheory.IsogenySum
