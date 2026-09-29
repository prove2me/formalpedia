-- Prove2me | solution 1 for ModularCurve.kernelVariableChangeDeg_dvd_inLineMulPoly_variableChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/b9ad9898-0d21-5136-8f30-1f8327304d8f

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassH1Pow
import Theorems.Thm_WeierstrassCurve_eval_PsiSq_variableChange
import Theorems.Thm_WeierstrassCurve_eval_Phi_variableChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_kernelVariableChangeDeg_dvd_inLineMulPoly_variableChange

set_option autoImplicit false

universe u

open Polynomial

noncomputable section

namespace LinkVC

variable {T : Type u} [CommRing T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)

abbrev σ : T[X] := Polynomial.C ((C.u : Tˣ) : T) ^ 2 * X + Polynomial.C C.r

abbrev ui : T := ((C.u⁻¹ : Tˣ) : T)

theorem ui_mul_u : ui C * ((C.u : Tˣ) : T) = 1 := by
  simp [ui, Units.inv_mul]

theorem point_eq_X :
    ((((C.map (Polynomial.C : T →+* T[X])).u⁻¹ : T[X]ˣ) : T[X])) ^ 2 *
      (σ C - (C.map (Polynomial.C : T →+* T[X])).r) = X := by
  simp only [WeierstrassCurve.VariableChange.map_u, WeierstrassCurve.VariableChange.map_r, σ, add_sub_cancel_right,
    Units.coe_map_inv, MonoidHom.coe_coe]
  rw [← mul_assoc, ← mul_pow, ← Polynomial.C_mul, ui_mul_u, Polynomial.C_1, one_pow, one_mul]

theorem comp_eq (p : T[X]) : p.comp (σ C) = (p.map (Polynomial.C : T →+* T[X])).eval (σ C) := by
  rw [Polynomial.comp, Polynomial.eval_map]

theorem PsiSq_vc (n : ℤ) :
    (C • W).ΨSq n = Polynomial.C (ui C ^ (2 * (n.natAbs ^ 2 - 1))) * (W.ΨSq n).comp (σ C) := by
  have key := WeierstrassCurve.eval_PsiSq_variableChange (W.map (Polynomial.C : T →+* T[X]))
    (C.map (Polynomial.C : T →+* T[X])) n (σ C)
  rw [WeierstrassCurve.map_variableChange, WeierstrassCurve.map_ΨSq, point_eq_X, Polynomial.eval_map,
    Polynomial.eval₂_C_X] at key
  rw [key, comp_eq, WeierstrassCurve.map_ΨSq]
  simp only [WeierstrassCurve.VariableChange.map_u, Units.coe_map_inv, MonoidHom.coe_coe, ← Polynomial.C_pow]

theorem Phi_vc (n : ℤ) :
    (C • W).Φ n = Polynomial.C (ui C ^ (2 * n.natAbs ^ 2)) * ((W.Φ n).comp (σ C) - Polynomial.C C.r * (W.ΨSq n).comp (σ C)) := by
  have key := WeierstrassCurve.eval_Phi_variableChange (W.map (Polynomial.C : T →+* T[X]))
    (C.map (Polynomial.C : T →+* T[X])) n (σ C)
  rw [WeierstrassCurve.map_variableChange, WeierstrassCurve.map_Φ, point_eq_X, Polynomial.eval_map,
    Polynomial.eval₂_C_X] at key
  rw [key, comp_eq, comp_eq, WeierstrassCurve.map_ΨSq, WeierstrassCurve.map_Φ]
  simp only [WeierstrassCurve.VariableChange.map_u, WeierstrassCurve.VariableChange.map_r, Units.coe_map_inv,
    MonoidHom.coe_coe, ← Polynomial.C_pow]

abbrev F (V : WeierstrassCurve T) (n a : ℕ) (x₀ : T) : T[X] :=
  V.Φ n * Polynomial.C ((V.ΨSq a).eval x₀) - Polynomial.C ((V.Φ a).eval x₀) * V.ΨSq n

theorem inLineMulPoly_eq (V : WeierstrassCurve T) (ℓ n : ℕ) (x₀ : T) :
    ModularCurve.inLineMulPoly V ℓ n x₀ = ∏ a ∈ Finset.Icc 1 ((ℓ - 1) / 2), F V n a x₀ := rfl

theorem F_comp (V : WeierstrassCurve T) (n a : ℕ) (x₀ : T) (q : T[X]) :
    (F V n a x₀).comp q = (V.Φ n).comp q * Polynomial.C ((V.ΨSq a).eval x₀) - Polynomial.C ((V.Φ a).eval x₀) * (V.ΨSq n).comp q := by
  simp only [F, ← Polynomial.coe_compRingHom_apply, map_sub, map_mul]
  simp only [Polynomial.coe_compRingHom_apply, Polynomial.C_comp]

theorem F_vc (n a : ℕ) (ha : 1 ≤ a) (x₀ : T) :
    F (C • W) n a (ui C ^ 2 * (x₀ - C.r)) =
      Polynomial.C (ui C ^ (2 * n ^ 2 + 2 * (a ^ 2 - 1))) * (F W n a x₀).comp (σ C) := by
  have hΨa := WeierstrassCurve.eval_PsiSq_variableChange W C a x₀
  have hΦa := WeierstrassCurve.eval_Phi_variableChange W C a x₀
  have hΨn := PsiSq_vc W C n
  have hΦn := Phi_vc W C n
  simp only [Int.natAbs_natCast] at hΨa hΦa hΨn hΦn
  obtain ⟨A', hA'⟩ : ∃ A' : ℕ, a ^ 2 = A' + 1 := ⟨a ^ 2 - 1, (Nat.sub_add_cancel (Nat.one_le_pow _ _ ha)).symm⟩
  rw [F_comp]
  show (C • W).Φ ↑n * Polynomial.C (((C • W).ΨSq ↑a).eval (ui C ^ 2 * (x₀ - C.r))) -
      Polynomial.C (((C • W).Φ ↑a).eval (ui C ^ 2 * (x₀ - C.r))) * (C • W).ΨSq ↑n = _
  rw [hΨa, hΦa, hΨn, hΦn, hA', Nat.add_sub_cancel]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [Nat.cast_zero, WeierstrassCurve.ΨSq_zero, WeierstrassCurve.Φ_zero, Polynomial.zero_comp, Polynomial.one_comp,
      mul_zero, sub_zero, mul_one, Polynomial.C_mul, Polynomial.C_pow]
    ring
  · obtain ⟨N', hN'⟩ : ∃ N' : ℕ, n ^ 2 = N' + 1 := ⟨n ^ 2 - 1, (Nat.sub_add_cancel (Nat.one_le_pow _ _ hn)).symm⟩
    rw [hN', Nat.add_sub_cancel]
    simp only [Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_sub]
    ring

end LinkVC

end

open LinkVC in
theorem solution
    (T : Type u) [CommRing T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
    (ℓ d n : ℕ) (h : Polynomial T) (x : T)
    (hx : h ∣ ModularCurve.inLineMulPoly W ℓ n x) :
    ModularCurve.kernelVariableChangeDeg C d h ∣
      ModularCurve.inLineMulPoly (C • W) ℓ n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)) := by
  classical
  set x' : T := ((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r) with hx'
  let c : ℕ → T := fun a => ui C ^ (2 * n ^ 2 + 2 * (a ^ 2 - 1))
  have hfac : ∀ a ∈ Finset.Icc 1 ((ℓ - 1) / 2),
      F (C • W) n a x' = Polynomial.C (c a) * (F W n a x).comp (σ C) := by
    intro a hamem
    exact F_vc W C n a (Finset.mem_Icc.mp hamem).1 x
  have hprod : ModularCurve.inLineMulPoly (C • W) ℓ n x' =
      Polynomial.C (∏ a ∈ Finset.Icc 1 ((ℓ - 1) / 2), c a) * (ModularCurve.inLineMulPoly W ℓ n x).comp (σ C) := by
    rw [inLineMulPoly_eq, inLineMulPoly_eq, Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, ← map_prod Polynomial.C]
    congr 1
    rw [← Polynomial.coe_compRingHom_apply, map_prod]
    simp only [Polynomial.coe_compRingHom_apply]
  obtain ⟨g, hg⟩ := hx
  have e : Polynomial.C (ui C ^ (2 * d)) * Polynomial.C (((C.u : Tˣ) : T) ^ (2 * d)) = (1 : T[X]) := by
    rw [← Polynomial.C_mul, ← mul_pow, ui_mul_u, one_pow, Polynomial.C_1]
  refine ⟨Polynomial.C ((((C.u : Tˣ) : T) ^ (2 * d)) * ∏ a ∈ Finset.Icc 1 ((ℓ - 1) / 2), c a) * g.comp (σ C), ?_⟩
  rw [hprod, hg, Polynomial.mul_comp]
  show _ = Polynomial.C (ui C ^ (2 * d)) * h.comp (σ C) * _
  rw [Polynomial.C_mul]
  linear_combination (-(Polynomial.C (∏ a ∈ Finset.Icc 1 ((ℓ - 1) / 2), c a) * h.comp (σ C) * g.comp (σ C))) * e

end S_ModularCurve_kernelVariableChangeDeg_dvd_inLineMulPoly_variableChange
end P2MW
export P2MW.S_ModularCurve_kernelVariableChangeDeg_dvd_inLineMulPoly_variableChange (solution)
