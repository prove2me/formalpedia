-- Prove2me | solution 1 for ModularCurve.realize_eq_div
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/0b66f1df-2a96-50f5-8bb1-29ccf354cb75

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionary
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_realize_eq_div

set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups Topology Manifold

open UpperHalfPlane in
theorem solution (N : ℕ) {k : ℤ}
    (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k) (x : LaurentSeries ℂ)
    (hx : x * ((qExpansion 1 (h : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
      ((qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ))
    (τ : ℍ) (hτ : (h : ℍ → ℂ) τ ≠ 0) :
    ModularCurve.realize N x τ = (g : ℍ → ℂ) τ / (h : ℍ → ℂ) τ := by
  classical

  have h1 : (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    simp
  have H : ∃ p : (k : ℤ) × (ModularForm (CongruenceSubgroup.Gamma0 N) k ×
        ModularForm (CongruenceSubgroup.Gamma0 N) k),
      (p.2.2 : ℍ → ℂ) τ ≠ 0 ∧
        x * ((qExpansion 1 (p.2.2 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
          ((qExpansion 1 (p.2.1 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) :=
    ⟨⟨k, g, h⟩, hτ, hx⟩
  have hval : ModularCurve.realize N x τ = (H.choose.2.1 : ℍ → ℂ) τ / (H.choose.2.2 : ℍ → ℂ) τ := by
    simp only [ModularCurve.realize, dif_pos H]
  rw [hval]
  obtain ⟨hτ', hx'⟩ := H.choose_spec
  set p := H.choose with hp

  obtain ⟨k', g', h'⟩ := p
  simp only at hτ' hx' ⊢

  have hq : qExpansion 1 ((g' : ℍ → ℂ) * (h : ℍ → ℂ)) = qExpansion 1 ((g : ℍ → ℂ) * (h' : ℍ → ℂ)) := by
    apply (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ))
    rw [ModularForm.qExpansion_mul_coe one_pos h1, ModularForm.qExpansion_mul_coe one_pos h1,
      PowerSeries.coe_mul, PowerSeries.coe_mul, ← hx, ← hx']
    ring

  have hAB : (g'.mul h : ModularForm (CongruenceSubgroup.Gamma0 N) (k' + k)) =
      ModularForm.mcast (add_comm k k') (g.mul h') := by
    rw [← sub_eq_zero, ← ModularForm.qExpansion_eq_zero_iff one_pos h1, ModularForm.coe_sub,
      ModularForm.qExpansion_sub one_pos h1, sub_eq_zero, ModularForm.coe_mcast,
      ModularForm.coe_mul, ModularForm.coe_mul, hq]
  have hτeq : (g' : ℍ → ℂ) τ * (h : ℍ → ℂ) τ = (g : ℍ → ℂ) τ * (h' : ℍ → ℂ) τ := by
    have := congrArg (fun f : ModularForm (CongruenceSubgroup.Gamma0 N) (k' + k) => (f : ℍ → ℂ) τ)
      hAB
    simpa [ModularForm.coe_mul, ModularForm.coe_mcast] using this
  rw [div_eq_div_iff hτ' hτ, hτeq]

end S_ModularCurve_realize_eq_div
end P2MW
export P2MW.S_ModularCurve_realize_eq_div (solution)
