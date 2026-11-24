-- Prove2me | solution 1 for GlobalTheory.PeriodCoord.riemann_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:38:48.889885+00:00
-- url     : https://prove2.me/submissions/78c17605-2fcb-4a83-8754-f42354c547ca

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableOnLeftInverse
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsPreconnectedBlockUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFinsetOfMemNhds
import Theorems.Thm_GlobalTheory_PeriodCoord_herm_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodCoord
noncomputable section
variable {g : ℕ}
namespace GlobalTheory.PeriodCoord
theorem _root_.solution {M M₀ C : Matrix (Fin g) (Fin g) ℂ} (hM : M.IsHermitian)
    (h : ∀ z w, (hermForm M (z + C *ᵥ star z) (w + C *ᵥ star w)).im = (hermForm M₀ z w).im) (i j : Fin g) :
    (Cᵀ * M₀) i j = (Cᵀ * M₀) j i := by
  set c : (Fin g → ℂ) → (Fin g → ℂ) := fun z => C *ᵥ star z with hc
  have hcI : ∀ z, c (Complex.I • z) = (-Complex.I) • c z := fun z => by
    simp [hc, mulVec_smul, mulVec_neg]
  have key : ∀ z w, hermForm M (c w) z = hermForm M (c z) w ∧
      hermForm M₀ z w = hermForm M z w - hermForm M (c w) (c z) := fun z w => by
    have h1 : (hermForm M (z + c z) (w + c w)).im = _ := h z w
    have h2 : (hermForm M (_ + c _) (_ + c _)).im = _ := h (Complex.I • z) (Complex.I • w)
    have h3 : (hermForm M (_ + c _) (_ + c _)).im = _ := h (Complex.I • z) w
    have h4 : (hermForm M (_ + c _) (_ + c _)).im = _ := h z (Complex.I • w)
    simp only [hcI, herm_add_left, herm_add_right, herm_smul_left, herm_smul_right] at h1 h2 h3 h4
    simp at h1 h2 h3 h4
    rw [herm_conj hM (c w) z, herm_conj hM (c w) (c z)]
    refine ⟨Complex.ext ?_ ?_, Complex.ext ?_ ?_⟩ <;> simp <;> linarith
  have key2 : ∀ z w, hermForm M₀ (c z) w = hermForm M₀ (c w) z := fun z w => by
    rw [(key _ _).2, (key _ _).2, (key z w).1, herm_conj hM (c w) (c (c z)), (key (c w) (c z)).1,
      ← herm_conj hM]
  have := key2 (Pi.single i 1) (Pi.single j 1)
  simpa [hc, hermForm, ← Pi.single_star, mul_apply, dotProduct] using this
end GlobalTheory.PeriodCoord
