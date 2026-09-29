-- Prove2me | solution 1 for ModularCurve.realize_coeffEmb_jq_eventuallyEq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/353844fa-b9b6-596b-a168-d117a1c95be8

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionary
import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_ModularCurve_AtkinLehner
import Theorems.Thm_ModularCurve_exists_complexPlaceDictionary
import Theorems.Thm_ModularCurve_exists_modularForm_realize_eventuallyEq_div
import Theorems.Thm_ModularCurve_hasSum_jq_qParam
import Theorems.Thm_ModularCurve_hasSum_qParam_mul_laurent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_realize_coeffEmb_jq_eventuallyEq
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 8000000

open UpperHalfPlane Filter ModularCurve
open scoped Topology MatrixGroups Manifold

noncomputable section

namespace JREG

abbrev FC (N : ℕ) : Type := ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N))

def jC (N : ℕ) [NeZero N] : FC N :=
  ⟨ModularCurve.coeffEmb ℂ ModularCurve.jq, ModularCurve.coeffEmb_mem_laurentBaseChange ℂ (ModularCurve.jq_mem_full N)⟩

variable {N : ℕ} [NeZero N]

theorem jC_ne_zero : jC N ≠ 0 := by
  intro h0
  have h1 : ((jC N : FC N) : LaurentSeries ℂ) = 0 := by rw [h0]; rfl
  have h2 := ModularCurve.order_coeffEmb_jq ℂ
  change ((jC N : FC N) : LaurentSeries ℂ).order = -1 at h2
  rw [h1, HahnSeries.order_zero] at h2
  exact absurd h2 (by norm_num)

def Jfun : ℍ → ℂ := fun τ => ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ

omit [NeZero N] in
theorem analyticAt_modularForm_ofComplex {k : ℤ} {Γ : Subgroup (GL (Fin 2) ℝ)} (f : ModularForm Γ k) (τ : ℍ) :
    AnalyticAt ℂ (fun z : ℂ => (f : ℍ → ℂ) (ofComplex z)) (τ : ℂ) := by
  have hE : DifferentiableOn ℂ ((⇑f : ℍ → ℂ) ∘ ofComplex) {z | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp (ModularFormClass.holo f)
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  exact hE.analyticAt (hopen.mem_nhds τ.2)
omit [NeZero N] in
theorem analyticAt_cuspForm_ofComplex {k : ℤ} {Γ : Subgroup (GL (Fin 2) ℝ)} (f : CuspForm Γ k) (τ : ℍ) :
    AnalyticAt ℂ (fun z : ℂ => (f : ℍ → ℂ) (ofComplex z)) (τ : ℂ) := by
  have hE : DifferentiableOn ℂ ((⇑f : ℍ → ℂ) ∘ ofComplex) {z | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp (ModularFormClass.holo f)
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  exact hE.analyticAt (hopen.mem_nhds τ.2)

omit [NeZero N] in
theorem analyticAt_J_ofComplex (τ : ℍ) : AnalyticAt ℂ (fun z : ℂ => Jfun (ofComplex z)) (τ : ℂ) := by
  have hE := analyticAt_modularForm_ofComplex ModularForm.E₄ τ
  have hD := analyticAt_cuspForm_ofComplex CuspForm.discriminant τ
  have hD0 : (CuspForm.discriminant : ℍ → ℂ) (ofComplex (τ : ℂ)) ≠ 0 := by
    rw [ofComplex_apply]; exact ModularForm.discriminant_ne_zero τ
  exact (hE.pow 3).div hD hD0

omit [NeZero N] in
set_option maxHeartbeats 4000000 in

theorem hasSum_int_of_powerSeries {f : ℍ → ℂ} (P : PowerSeries ℂ) (τ : ℍ)
    (h : HasSum (fun m : ℕ => PowerSeries.coeff m P • Function.Periodic.qParam 1 (τ : ℂ) ^ m) (f τ)) :
    HasSum (fun m : ℤ => ((P : LaurentSeries ℂ)).coeff m * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (f τ) := by
  have hnat : HasSum (fun m : ℕ => ((P : LaurentSeries ℂ)).coeff (m : ℤ) *
      Function.Periodic.qParam 1 (τ : ℂ) ^ (m : ℤ)) (f τ) := by
    refine h.congr_fun fun m => ?_
    rw [PowerSeries.coeff_coe, zpow_natCast, smul_eq_mul, if_neg (by omega), Int.natAbs_natCast]
  have hneg : HasSum (fun m : ℕ => ((P : LaurentSeries ℂ)).coeff (-(m + 1 : ℤ)) *
      Function.Periodic.qParam 1 (τ : ℂ) ^ (-(m + 1 : ℤ))) 0 := by
    have hz : (fun m : ℕ => ((P : LaurentSeries ℂ)).coeff (-(m + 1 : ℤ)) *
        Function.Periodic.qParam 1 (τ : ℂ) ^ (-(m + 1 : ℤ))) = fun _ => 0 := by
      funext m
      rw [PowerSeries.coeff_coe, if_pos (by omega), zero_mul]
    rw [hz]; exact hasSum_zero
  have := HasSum.of_nat_of_neg_add_one
    (f := fun m : ℤ => ((P : LaurentSeries ℂ)).coeff m * Function.Periodic.qParam 1 (τ : ℂ) ^ m) hnat hneg
  rwa [add_zero] at this

omit [NeZero N] in

theorem hasSum_qExpansion_Gamma0 (N : ℕ) {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) (τ : ℍ) :
    HasSum (fun m : ℕ => PowerSeries.coeff m (qExpansion 1 (f : ℍ → ℂ)) •
      Function.Periodic.qParam 1 (τ : ℂ) ^ m) ((f : ℍ → ℂ) τ) := by
  have hΓ : (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma0 N).map
      (Matrix.SpecialLinearGroup.mapGL ℝ)).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma0]; exact AddSubgroup.mem_zmultiples _
  haveI : Fact (IsCusp OnePoint.infty ((CongruenceSubgroup.Gamma0 N).map
      (Matrix.SpecialLinearGroup.mapGL ℝ))) := ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  exact UpperHalfPlane.hasSum_qExpansion one_pos (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ)
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) τ

theorem main (N : ℕ) [NeZero N] (τ : ℍ) :
    (fun z : ℂ => ModularCurve.realize N (ModularCurve.coeffEmb ℂ ModularCurve.jq) (ofComplex z))
      =ᶠ[nhdsWithin (τ : ℂ) {(τ : ℂ)}ᶜ]
      fun z : ℂ => ModularForm.E₄ (ofComplex z) ^ 3 / ModularForm.discriminant (ofComplex z) := by
  obtain ⟨D⟩ := ModularCurve.exists_complexPlaceDictionary N
  obtain ⟨k, g, h, hh0, hx, hloc⟩ :=
    ModularCurve.exists_modularForm_realize_eventuallyEq_div N (jC N)
  have hgJ : ∀ t : ℍ, (g : ℍ → ℂ) t = Jfun t * (h : ℍ → ℂ) t := by
    intro t
    have hA : ∀ t : ℍ, HasSum (fun m : ℤ => ((jC N : FC N) : LaurentSeries ℂ).coeff m *
        Function.Periodic.qParam 1 (t : ℂ) ^ m) (Jfun t) := by
      intro t
      refine (ModularCurve.hasSum_jq_qParam t).congr_fun fun m => ?_
      show ((ModularCurve.jq.coeff m : ℚ) : ℂ) * _ = (ModularCurve.coeffEmb ℂ ModularCurve.jq).coeff m * _
      rw [ModularCurve.coeffEmb, ModularCurve.coeffMap_coeff, eq_ratCast]
    have hB : ∀ t : ℍ, HasSum (fun m : ℤ => (((qExpansion 1 (h : ℍ → ℂ)) : PowerSeries ℂ) : LaurentSeries ℂ).coeff m *
        Function.Periodic.qParam 1 (t : ℂ) ^ m) ((h : ℍ → ℂ) t) :=
      fun t => hasSum_int_of_powerSeries _ t (hasSum_qExpansion_Gamma0 N h t)
    have hAB := ModularCurve.hasSum_qParam_mul_laurent 1 one_pos _ _ _ _ hA hB t
    rw [hx] at hAB
    have hG := hasSum_int_of_powerSeries _ t (hasSum_qExpansion_Gamma0 N g t)
    exact hG.unique hAB
  have hmer := D.meromorphicOrderAt_realize τ (jC N) jC_ne_zero
  have hh_an := analyticAt_modularForm_ofComplex h τ
  change (fun z : ℂ => ModularCurve.realize N ((jC N : FC N) : LaurentSeries ℂ) (ofComplex z))
      =ᶠ[𝓝[≠] (τ : ℂ)] fun z => Jfun (ofComplex z)
  rcases hh_an.eventually_eq_zero_or_eventually_ne_zero with hz | hnz
  · exfalso
    have h0 : ∀ᶠ z in 𝓝[≠] (τ : ℂ), ModularCurve.realize N ((jC N : FC N) : LaurentSeries ℂ) (ofComplex z) = 0 := by
      filter_upwards [hloc τ, hz.filter_mono nhdsWithin_le_nhds] with z h1 h2
      rw [h1, h2, div_zero]
    have htop := meromorphicOrderAt_eq_top_iff.2 h0
    rw [htop] at hmer
    exact WithTop.top_ne_coe hmer
  · filter_upwards [hloc τ, hnz] with z h1 h2
    rw [h1]
    show (g : ℍ → ℂ) (ofComplex z) / (h : ℍ → ℂ) (ofComplex z) = Jfun (ofComplex z)
    rw [hgJ, mul_div_assoc, div_self h2, mul_one]

end JREG

theorem solution (N : ℕ) [NeZero N] (τ : ℍ) :
    (fun z : ℂ => ModularCurve.realize N (ModularCurve.coeffEmb ℂ ModularCurve.jq) (ofComplex z))
      =ᶠ[nhdsWithin (τ : ℂ) {(τ : ℂ)}ᶜ]
      fun z : ℂ => ModularForm.E₄ (ofComplex z) ^ 3 / ModularForm.discriminant (ofComplex z) :=
  JREG.main N τ

end

end S_ModularCurve_realize_coeffEmb_jq_eventuallyEq
end P2MW
export P2MW.S_ModularCurve_realize_coeffEmb_jq_eventuallyEq (solution)
