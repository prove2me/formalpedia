-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.HT.LatBasic.diffAbs_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:32:18.985922+00:00
-- url     : https://prove2.me/submissions/d4b17a2a-9882-45e2-8eb4-4ecc0bf11e0a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LogAbsVpOfNormalised
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_IdemDen
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_CommutativeAlgebra_LatNormGrLatNeZeroOfSpan
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
theorem _root_.solution (v : Valuation K NNReal) (σ : E →+* K) : 0 < diffAbs v σ := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 E))
  refine lt_of_lt_of_le ?_ (le_diffAbs v σ hx)
  rw [pos_iff_ne_zero, Valuation.ne_zero_iff, map_ne_zero]
  exact_mod_cast hx0
end GlobalTheory.CompanionTheory.Ar.HT.LatBasic
