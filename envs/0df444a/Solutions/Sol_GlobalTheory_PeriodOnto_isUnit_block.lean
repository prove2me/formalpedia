-- Prove2me | solution 1 for GlobalTheory.PeriodOnto.isUnit_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:57:44.210537+00:00
-- url     : https://prove2.me/submissions/025e3366-ac8d-4caa-99db-a330659add4f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqIffConjNe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsFrameOfIsPeriod
import Theorems.Thm_GlobalTheory_PeriodOnto_blockOf_ofBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexOrder ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.PeriodOnto
variable {ι : Type} [Fintype ι] {g r : ℕ} (idx : Fin g ≃ ι × Fin r) (q : ℕ)
variable {Λ : Type} (P : Λ → Fin g → ℂ) (hspan : Submodule.span ℝ (Set.range P) = ⊤)
  (e : ι → Λ → Fin r → ℂ) (M : ι → Matrix (Fin r) (Fin r) ℂ)
  (hM : ∀ v t, blockOf idx q t (P v) = M t *ᵥ e t v)
include hspan hM
namespace GlobalTheory.PeriodOnto
theorem _root_.solution (t : ι) : IsUnit (M t) := by
  classical
  rw [← vecMul_injective_iff_isUnit]
  have : ∀ w, w ᵥ* M t = 0 → w = 0 := by
    intro w hw
    have h1 : ∀ z ∈ Submodule.span ℝ (Set.range P), w ⬝ᵥ blockOf idx q t z = 0 := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨v, rfl⟩ := hz
        rw [hM, dotProduct_mulVec, hw, zero_dotProduct]
      | zero => simp
      | add _ _ _ _ h1 h2 => simp [h1, h2]
      | smul c _ _ h1 => simp [h1]
    ext a
    have := h1 (ofBlock idx q t (Pi.single a 1)) (by rw [hspan]; trivial)
    simpa [blockOf_ofBlock] using this
  intro u u' huu
  have := this (u - u') (by rw [sub_vecMul]; exact sub_eq_zero.mpr huu)
  exact sub_eq_zero.mp this
end GlobalTheory.PeriodOnto
