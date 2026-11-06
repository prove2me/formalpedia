-- Prove2me | solution 1 for OAI.ShortDraftSextic.sextic_power_is_unit_mask
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:06:27.406077+00:00
-- url     : https://prove2.me/submissions/4de9fc19-ff4e-44ce-91e3-d187daa7c981

import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_MatrixPhases

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
noncomputable section
open OAI.ShortDraftSextic
open scoped Classical
variable {R : Type*} [CommRing R]
namespace OAI.ShortDraftSextic
theorem _root_.solution (χ : MulChar R ℂ)
    (hχ : χ ^ 6 = 1) (u : R) :
    χ (u ^ 6) = if IsUnit u then 1 else 0 := by
  classical
  rw [map_pow, ← MulChar.pow_apply' χ (by decide : 6 ≠ 0), hχ]
  by_cases hu : IsUnit u
  · simp [hu, MulChar.one_apply]
  · simp [hu]
end OAI.ShortDraftSextic
