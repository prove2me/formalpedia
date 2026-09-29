-- Prove2me | solution 1 for Hatcher.fundamentalGroup_map_eq_changeOfBasepoint_comp_of_homotopy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-14T12:44:42.601068+00:00
-- url     : https://prove2.me/submissions/f6e15d17-f72e-405c-ba0c-74b5b2418c6f

import Mathlib

open CategoryTheory ContinuousMap FundamentalGroup FundamentalGroupoidFunctor

theorem solution {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {φ₀ φ₁ : C(X, Y)} (H : ContinuousMap.Homotopy φ₀ φ₁) (x₀ : X) :
    FundamentalGroup.map φ₁ x₀
      = (fundamentalGroupMulEquivOfPath (H.evalAt x₀)).toMonoidHom.comp
          (FundamentalGroup.map φ₀ x₀) := by
  ext γ
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  simp only [fundamentalGroupMulEquivOfPath, Iso.conj_apply]
  refine (Iso.eq_inv_comp _).mpr ?_
  exact ((homotopicMapsNatIso H).naturality γ).symm
