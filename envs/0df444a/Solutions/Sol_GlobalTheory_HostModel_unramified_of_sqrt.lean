-- Prove2me | solution 1 for GlobalTheory.HostModel.unramified_of_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:52:49.63455+00:00
-- url     : https://prove2.me/submissions/d2ea07da-12d4-49d2-be17-8f58fb954f69

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_OneAddZeta21PowSevenAddPowFourteenEqZero
import Theorems.Thm_GlobalTheory_HostModel_unramified_of_isCoprime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HostModel
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.HostModel
theorem _root_.solution {x₁ x₂ w₁ w₂ : 𝓞 E} {m n : ℕ} (hmn : m.Coprime n) (h₁ : x₁ ^ 2 = -(m : 𝓞 E))
    (h₂ : x₂ ^ 2 = -(n : 𝓞 E)) (hw₁ : 2 * w₁ = 1 + x₁) (hw₂ : 2 * w₂ = 1 + x₂) :
    Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) := by
  apply unramified_of_isCoprime w₁ w₂
  rw [sub_complexConj_eq_of_two_mul h₁ hw₁, sub_complexConj_eq_of_two_mul h₂ hw₂,
    ← IsCoprime.pow_iff (m := 2) (n := 2) two_pos two_pos, h₁, h₂, IsCoprime.neg_neg_iff]
  exact hmn.cast
end GlobalTheory.HostModel
