-- Prove2me | solution 1 for ModularCurve.periodMap_add
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/8c5cddb5-111c-5bb3-a94e-525370b51693

import Definitions.Def_ModularCurve_PeriodMapBundled
import Theorems.Thm_ModularCurve_Period_CuspForm_exists_equivariantPrimitive_gamma0
import Theorems.Thm_ModularCurve_periodMap_eq_periodHom
import Mathlib.Tactic.LinearCombination
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_periodMap_add

set_option autoImplicit false

namespace ModularCurve
p2m_export "ModularCurve" "HasEquivariantPrimitive periodMap periodMap_def Period.IsEquivariantPrimitive Period.IsEquivariantPrimitive.periodHom_apply Period.CuspForm.exists_equivariantPrimitive_gamma0 periodMap_eq_periodHom"
namespace SolLevelZero
p2m_open "ModularCurve"

open UpperHalfPlane Filter Topology CongruenceSubgroup

open scoped MatrixGroups

theorem period_eq_zero_of_apply_one_zero {Γ : Subgroup SL(2, ℤ)} {F : ℍ → ℂ}
    (hF : ModularCurve.Period.IsEquivariantPrimitive Γ F) (hlim : Tendsto F atImInfty (𝓝 0)) (γ : Γ)
    (hc : (γ : SL(2, ℤ)) 1 0 = 0) : hF.period γ = 0 := by
  set g : SL(2, ℤ) := (γ : SL(2, ℤ)) with hg
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have h := Matrix.det_fin_two (g : Matrix (Fin 2) (Fin 2) ℤ)
    rw [Matrix.SpecialLinearGroup.det_coe] at h
    exact h.symm
  have hdd : g 1 1 * g 1 1 = 1 := by
    rw [hc, mul_zero, sub_zero] at hdet
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨-, h1⟩ | ⟨-, h1⟩ <;> simp [h1]
  have him : ∀ z : ℍ, (g • z).im = z.im := by
    intro z
    rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply, hc]
    have hdd' : ((g 1 1 : ℤ) : ℝ) * ((g 1 1 : ℤ) : ℝ) = 1 := by exact_mod_cast hdd
    have hn : Complex.normSq (((0 : ℤ) : ℂ) * (z : ℂ) + ((g 1 1 : ℤ) : ℂ)) = 1 := by
      rw [Int.cast_zero, zero_mul, zero_add, Complex.normSq_intCast, hdd']
    rw [hn, div_one]
  have htend : Tendsto (fun z : ℍ => g • z) atImInfty atImInfty := by
    rw [atImInfty, Filter.tendsto_comap_iff]
    have hcomp : (UpperHalfPlane.im ∘ fun z : ℍ => g • z) = UpperHalfPlane.im := funext him
    rw [hcomp]
    exact Filter.tendsto_comap
  have h1 : Tendsto (fun z : ℍ => F (g • z) - F z) atImInfty (𝓝 (0 - 0)) := (hlim.comp htend).sub hlim
  have h2 : (fun z : ℍ => F (g • z) - F z) = fun _ => hF.period γ := funext (hF.sub_eq_period γ)
  rw [h2, sub_zero] at h1
  exact tendsto_nhds_unique tendsto_const_nhds h1

theorem periodMap_level_zero (f : CuspForm (Gamma0 0) 2) : ModularCurve.periodMap 0 f = 0 := by
  classical
  by_cases h : ∃ F : ℍ → ℂ, ModularCurve.HasEquivariantPrimitive 0 f F
  · obtain ⟨F, hF⟩ := h
    obtain ⟨F₀, h₀, hdef⟩ := ModularCurve.periodMap_def 0 f hF
    rw [hdef]
    refine AddMonoidHom.ext fun x => ?_
    obtain ⟨γ, rfl⟩ : ∃ γ : Gamma0 0, Additive.ofMul γ = x := ⟨Additive.toMul x, rfl⟩
    rw [ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply, AddMonoidHom.zero_apply]
    refine period_eq_zero_of_apply_one_zero h₀.2.2.1 h₀.2.1 γ ?_
    have hmem := Gamma0_mem.mp γ.2
    exact_mod_cast hmem
  · unfold ModularCurve.periodMap
    rw [dif_neg h]

end ModularCurve.SolLevelZero

open UpperHalfPlane

open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "HasEquivariantPrimitive periodMap periodMap_def Period.IsEquivariantPrimitive Period.IsEquivariantPrimitive.periodHom_apply Period.CuspForm.exists_equivariantPrimitive_gamma0 periodMap_eq_periodHom"
namespace Period
p2m_export "ModularCurve.Period" "IsEquivariantPrimitive IsEquivariantPrimitive.periodHom_apply CuspForm.exists_equivariantPrimitive_gamma0"
namespace IsEquivariantPrimitive
p2m_export "ModularCurve.Period.IsEquivariantPrimitive" "period sub_eq_period periodHom periodHom_apply"
p2m_open "ModularCurve.Period.IsEquivariantPrimitive ModularCurve.Period ModularCurve"

variable {Γ : Subgroup SL(2, ℤ)} {F F' : ℍ → ℂ}

private theorem _root_.ModularCurve.Period.IsEquivariantPrimitive.add' (hF : IsEquivariantPrimitive Γ F) (hF' : IsEquivariantPrimitive Γ F') :
    IsEquivariantPrimitive Γ (F + F') := by
  intro γ
  refine ⟨hF.period γ + hF'.period γ, fun z => ?_⟩
  have h1 := hF.sub_eq_period γ z
  have h2 := hF'.sub_eq_period γ z
  simp only [Pi.add_apply]
  linear_combination h1 + h2

p2m_export "ModularCurve.Period.IsEquivariantPrimitive" "add'"

private theorem _root_.ModularCurve.Period.IsEquivariantPrimitive.periodHom_add' (hF : IsEquivariantPrimitive Γ F) (hF' : IsEquivariantPrimitive Γ F') :
    (hF.add' hF').periodHom = hF.periodHom + hF'.periodHom := by
  refine AddMonoidHom.ext fun x => ?_
  show (hF.add' hF').period (Additive.toMul x) = hF.period (Additive.toMul x) + hF'.period (Additive.toMul x)
  rw [← (hF.add' hF').sub_eq_period _ UpperHalfPlane.I]
  have h1 := hF.sub_eq_period (Additive.toMul x) UpperHalfPlane.I
  have h2 := hF'.sub_eq_period (Additive.toMul x) UpperHalfPlane.I
  simp only [Pi.add_apply]
  linear_combination h1 + h2

p2m_export "ModularCurve.Period.IsEquivariantPrimitive" "periodHom_add'"
end ModularCurve.Period.IsEquivariantPrimitive

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_periodMap_add.ModularCurve _root_.ModularCurve.Period _root_.P2MW.S_ModularCurve_periodMap_add.ModularCurve.Period CongruenceSubgroup in

theorem solution {N : ℕ} (f g : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    ModularCurve.periodMap N (f + g) = ModularCurve.periodMap N f + ModularCurve.periodMap N g := by
  rcases Nat.eq_zero_or_pos N with rfl | hpos
  · rw [ModularCurve.SolLevelZero.periodMap_level_zero, ModularCurve.SolLevelZero.periodMap_level_zero,
      ModularCurve.SolLevelZero.periodMap_level_zero, add_zero]
  haveI : NeZero N := ⟨hpos.ne'⟩
  obtain ⟨F, hFf, -, hFe, -⟩ := Period.CuspForm.exists_equivariantPrimitive_gamma0 f
  obtain ⟨G, hGg, -, hGe, -⟩ := Period.CuspForm.exists_equivariantPrimitive_gamma0 g
  have hsum : ∀ τ : ℍ, HasDerivAt ((F + G) ∘ ofComplex) ((f + g) τ) ↑τ := by
    intro τ
    have h := (hFf τ).add (hGg τ)
    have hval : (f + g) τ = f τ + g τ := rfl
    rw [hval]
    exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => rfl)
  rw [periodMap_eq_periodHom (hFe.add' hGe) hsum, periodMap_eq_periodHom hFe hFf, periodMap_eq_periodHom hGe hGg]
  exact hFe.periodHom_add' hGe

#print axioms solution

end S_ModularCurve_periodMap_add
end P2MW
export P2MW.S_ModularCurve_periodMap_add (solution)
