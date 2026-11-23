-- Prove2me | solution 1 for GlobalTheory.latticeCurve_j
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:25:07.263389+00:00
-- url     : https://prove2.me/submissions/e9cfb124-7133-46b2-88f1-124be2b36795

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Theorems.Thm_P2M_GlobalTheory_latticeCurve_c__6ffa6b5cc0c0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperHalfPlane ModularForm MatrixGroups Filter EisensteinSeries
open scoped Real Topology
noncomputable section
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {L : PeriodPair} {a : ℂ} {τ : ℍ} (ha : a ≠ 0)
    (h : ∀ x, x ∈ L.lattice ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x) :
    (latticeCurve L).j = E₄ τ ^ 3 / discriminant τ := by
  rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ',
    latticeCurve_Δ_eq_discriminant ha h, latticeCurve_c₄, g₂_eq_E₄ ha h]
  have := discriminant_ne_zero τ
  have : (π : ℂ) ≠ 0 := by simpa using Real.pi_ne_zero
  field_simp
  ring
end GlobalTheory
