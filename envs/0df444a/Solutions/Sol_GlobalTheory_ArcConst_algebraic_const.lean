-- Prove2me | solution 1 for GlobalTheory.ArcConst.algebraic_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:37:22.184985+00:00
-- url     : https://prove2.me/submissions/36b665a8-99ee-4611-8dcd-3a0247d5b467

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsIntegralElemOfIsAlgebraicInt
import Theorems.Thm_GlobalTheory_ArcConst_algZ_of
import Theorems.Thm_GlobalTheory_ArcConst_AlgZ_map
import Theorems.Thm_GlobalTheory_ArcConst_algebraMap_injective
import Theorems.Thm_GlobalTheory_ArcConst_isDomain
import Theorems.Thm_P2M_GlobalTheory_ArcConst_arc__C_injective_0a8b9ebdf4ed
import Theorems.Thm_GlobalTheory_ArcConst_exists_const

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
noncomputable section
open GlobalTheory GlobalTheory.ArcConst
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace GlobalTheory.ArcConst
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (K : Type) [Field K] [CharZero K], IsDomain (ArcS Dw K) ∧ Function.Injective (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K)) (ArcS Dw K)) ∧ (∀ s : ArcS Dw K, IsAlgebraic ℤ s → ∃ x : K, s = arcι Dw K (PowerSeries.C (R := K) x)) ∧ ∀ (F : Type) [Field F] [NumberField F] (f : F →+* ArcS Dw K), ∃ f₀ : F →+* K, f = ((arcι Dw K).comp (PowerSeries.C (R := K))).comp f₀ := by
  intro E _ _ _ H Dw K _ _
  refine ⟨isDomain Dw K, algebraMap_injective Dw K, fun s hs => exists_const Dw K s (algZ_of hs), fun F _ _ f => ?_⟩
  have hinj := arcι_C_injective Dw K
  have hex : ∀ a : F, ∃ x : K, ((arcι Dw K).comp (PowerSeries.C (R := K))) x = f a := fun a => by
    have ha : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic a)
    obtain ⟨x, hx⟩ := exists_const Dw K (f a) ((algZ_of ha).map f)
    exact ⟨x, hx.symm⟩
  choose g hg using hex
  refine ⟨{ toFun := g, map_one' := hinj ?_, map_mul' := fun a b => hinj ?_, map_zero' := hinj ?_,
            map_add' := fun a b => hinj ?_ }, RingHom.ext fun a => (hg a).symm⟩
  · rw [hg, map_one, map_one]
  · rw [hg, map_mul, map_mul, hg, hg]
  · rw [hg, map_zero, map_zero]
  · rw [hg, map_add, map_add, hg, hg]
end GlobalTheory.ArcConst
