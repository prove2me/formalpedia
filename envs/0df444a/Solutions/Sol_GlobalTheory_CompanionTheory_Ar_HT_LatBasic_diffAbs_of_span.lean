-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.HT.LatBasic.diffAbs_of_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:32:11.817842+00:00
-- url     : https://prove2.me/submissions/4fa4a166-e29e-4a58-b4bd-a8eaca55b244

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LogAbsVpOfNormalised
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_IdemDen
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_CommutativeAlgebra_LatNormGrLatNeZeroOfSpan
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_HT_LatBasic_val_le_one
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_HT_LatBasic_le_diffAbs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT
open Module NumberField
open GlobalTheory.CompanionTheory.Ar.HT.LatBasic
open TensorProduct
variable {A : Type} [CommRing A] {K : Type} [Field K] [Algebra A K]
  {V : Type} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
  {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CompanionTheory.Ar.HT.LatBasic
theorem _root_.solution (v : Valuation K NNReal) (σ : E →+* K) {δ : 𝓞 E}
    (h : differentIdeal ℤ (𝓞 E) = Ideal.span {δ}) : diffAbs v σ = v (σ (δ : E)) := by
  refine le_antisymm (ciSup_le fun x => ?_)
    (le_diffAbs v σ (h ▸ Ideal.mem_span_singleton_self δ))
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (h.le x.2)
  rw [← hy, RingOfIntegers.coe_eq_algebraMap, map_mul, map_mul, map_mul]
  exact mul_le_of_le_one_left' (val_le_one v σ y)
end GlobalTheory.CompanionTheory.Ar.HT.LatBasic
