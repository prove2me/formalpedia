-- Prove2me | solution 1 for GlobalTheory.KSp.Homog.measurable_absE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:51:55.376806+00:00
-- url     : https://prove2.me/submissions/b2fbcb48-56f6-4d1b-ad69-93955412ba38

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HomogeneousMeasureEqSmulAddHaarLocalField
import Theorems.Thm_GlobalTheory_KSp_Homog_absE_eq_of_val_eq
import Theorems.Thm_GlobalTheory_KSp_Homog_measurableSet_preimage_valuation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open ValuativeRel Topology
open scoped ENNReal NNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.KSp GlobalTheory.KSp.Homog
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [MeasurableSpace F] [BorelSpace F]
namespace GlobalTheory.KSp.Homog
theorem _root_.solution : Measurable (absE : F → ℝ≥0∞) := by
  intro T _
  have : absE ⁻¹' T = valuation F ⁻¹' (valuation F '' (absE ⁻¹' T)) := by
    ext x; constructor
    · intro hx; exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hxy⟩
      simp only [Set.mem_preimage] at hy ⊢
      rwa [← absE_eq_of_val_eq hxy]
  rw [this]; exact measurableSet_preimage_valuation _
end GlobalTheory.KSp.Homog
