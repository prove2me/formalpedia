-- Prove2me | solution 1 for GlobalTheory.FramePeriod.eq_of_hermC_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:28:18.816421+00:00
-- url     : https://prove2.me/submissions/c4bf0708-35aa-4d77-8230-df1ea8a81d0b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermFormConjDiag
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FrameOfPeriodLinear
import Theorems.Thm_GlobalTheory_CMLattice_embAll_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMLattice.embAll_apply



set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.FramePeriod
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
omit [NumberField E] [IsCMField E]
namespace GlobalTheory.FramePeriod
theorem _root_.solution (τ : E →+* ℂ) (Gm : Matrix (Fin r) (Fin r) E) (hG : Gm.det ≠ 0)
    (v w : Fin r → ℂ) (h : ∀ u, FD.hermC τ Gm v u = FD.hermC τ Gm w u) : v = w := by
  classical
  have hd : (τ.mapMatrix Gm).det ≠ 0 := by
    rw [← RingHom.map_det]; exact (map_ne_zero τ).2 hG
  rw [← sub_eq_zero]
  apply Matrix.eq_zero_of_vecMul_eq_zero hd
  rw [sub_vecMul, sub_eq_zero]
  funext b
  have := h (Pi.single b 1)
  simpa [FD.hermC, Pi.single_apply, apply_ite, vecMul, dotProduct] using this
end GlobalTheory.FramePeriod
