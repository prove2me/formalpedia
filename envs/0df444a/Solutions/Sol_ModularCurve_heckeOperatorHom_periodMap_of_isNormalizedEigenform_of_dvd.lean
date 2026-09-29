-- Prove2me | solution 1 for ModularCurve.heckeOperatorHom_periodMap_of_isNormalizedEigenform_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/1b809ee4-ab07-5017-904f-e6bab57e66bc

import Definitions.Def_ModularCurve_PeriodMapBundled
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_ModularCurve_periodMap_heckeULin
import Theorems.Thm_ModularCurve_periodMap_smul
import Theorems.Thm_CuspForm_isNormalizedEigenform_iff_heckeTLin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_heckeOperatorHom_periodMap_of_isNormalizedEigenform_of_dvd

set_option Elab.async false
set_option autoImplicit false

namespace ModularCurve
p2m_export "ModularCurve" "HasEquivariantPrimitive periodMap periodMap_def Period.IsEquivariantPrimitive Period.IsEquivariantPrimitive.periodHom_apply periodMap_heckeULin periodMap_smul"
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

theorem solution {N : ℕ}
    {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f.IsNormalizedEigenform) {q : ℕ} (hq : q.Prime)
    (hqN : q ∣ N) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    HeckeEis.heckeOperatorHom N q ℂ (ModularCurve.periodMap N f)
      = (ModularFormClass.qCoeff f q) • ModularCurve.periodMap N f := by
  rcases Nat.eq_zero_or_pos N with rfl | hpos
  · rw [ModularCurve.SolLevelZero.periodMap_level_zero, map_zero, smul_zero]
  haveI : NeZero N := ⟨hpos.ne'⟩
  have heig : CuspForm.heckeULin 2 hqN f = ModularFormClass.qCoeff f q • f :=
    (((CuspForm.isNormalizedEigenform_iff_heckeTLin f).mp hf).2 q hq).2 hqN
  have h := ModularCurve.periodMap_heckeULin hq hqN f
  rw [heig, ModularCurve.periodMap_smul] at h
  exact h.symm

#print axioms solution

end S_ModularCurve_heckeOperatorHom_periodMap_of_isNormalizedEigenform_of_dvd
end P2MW
export P2MW.S_ModularCurve_heckeOperatorHom_periodMap_of_isNormalizedEigenform_of_dvd (solution)
