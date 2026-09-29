-- Prove2me | solution 1 for ModularCurve.exists_realizeOf_eventuallyEq_of_meromorphic_gammaH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/3277484e-b39e-543c-8d0c-c2ff82dec376

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_ModularCurve_XH
import Theorems.Thm_ModularCurve_exists_modularForm_eventuallyEq_div_of_meromorphic_of_finiteIndex
import Theorems.Thm_ModularCurve_qExpansion_div_mem_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_realizeOf_eq_div
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_realizeOf_eventuallyEq_of_meromorphic_gammaH

set_option autoImplicit false

open UpperHalfPlane Filter Topology
open scoped MatrixGroups Topology

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "realizeOf laurentBaseChange translation_mem_GammaH Gamma1_le_GammaH xHFunctionField exists_modularForm_eventuallyEq_div_of_meromorphic_of_finiteIndex qExpansion_div_mem_laurentBaseChange_xHFunctionField realizeOf_eq_div"
namespace GAGARealizeH
p2m_open "ModularCurve"

abbrev qL {Γ : Subgroup SL(2, ℤ)} {k : ℤ} (f : ModularForm Γ k) : LaurentSeries ℂ :=
  ((qExpansion 1 (f : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)

theorem one_mem_strictPeriods {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ) :
    (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
  exact AddSubgroup.mem_zmultiples _

theorem qL_ne_zero {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ) {k : ℤ} (f : ModularForm Γ k)
    (hf : f ≠ 0) : qL f ≠ 0 := by
  intro h
  apply hf
  rw [← ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods hT)]
  apply (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ))
  simpa [qL] using h

theorem map_coe_nhdsNE (τ : ℍ) :
    Filter.map ((↑) : ℍ → ℂ) (𝓝[≠] τ) = 𝓝[≠] (τ : ℂ) := by
  have h := isOpenEmbedding_coe.map_nhdsWithin_preimage_eq ({(τ : ℂ)}ᶜ) τ
  have hpre : ((↑) : ℍ → ℂ) ⁻¹' ({(τ : ℂ)}ᶜ : Set ℂ) = ({τ}ᶜ : Set ℍ) := by
    ext w
    simp
  rwa [hpre] at h

theorem eventually_nhdsNE_coe_iff {p : ℍ → Prop} {τ : ℍ} :
    (∀ᶠ z in 𝓝[≠] (τ : ℂ), p (ofComplex z)) ↔ ∀ᶠ w in 𝓝[≠] τ, p w := by
  rw [← map_coe_nhdsNE, Filter.eventually_map]
  simp only [ofComplex_apply]

theorem eventually_ne_zero {Γ : Subgroup SL(2, ℤ)} {k : ℤ} (f : ModularForm Γ k)
    (hf : f ≠ 0) (τ : ℍ) : ∀ᶠ w in 𝓝[≠] τ, (f : ℍ → ℂ) w ≠ 0 := by
  by_contra hcon
  have hfr : ∃ᶠ w in 𝓝[≠] τ, (f : ℍ → ℂ) w = 0 := by
    simpa [Filter.not_eventually] using hcon
  have h0 : (f : ℍ → ℂ) = 0 := eq_zero_of_frequently (ModularFormClass.holo f) hfr
  exact hf (DFunLike.coe_injective (by simpa using h0))

end ModularCurve.GAGARealizeH

end

open UpperHalfPlane ModularCurve.GAGARealizeH in
open scoped MatrixGroups Topology in
theorem solution (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) (F : UpperHalfPlane → ℂ)
    (hmer : ∀ τ : UpperHalfPlane, MeromorphicAt (fun z : ℂ => F (UpperHalfPlane.ofComplex z)) (τ : ℂ))
    (hinv : ∀ γ ∈ CohCarrier.GammaH M H, ∀ τ : UpperHalfPlane, F (γ • τ) = F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ C : ℝ,
      Asymptotics.IsBigO UpperHalfPlane.atImInfty (fun τ : UpperHalfPlane => F (σ • τ))
        fun τ : UpperHalfPlane => Real.exp (C * τ.im)) :
    ∃ x ∈ ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H),
      ∀ τ : UpperHalfPlane, (fun z : ℂ => F (UpperHalfPlane.ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
        fun z : ℂ => ModularCurve.realizeOf (CohCarrier.GammaH M H) x (UpperHalfPlane.ofComplex z) := by
  have hT : ModularGroup.T ∈ CohCarrier.GammaH M H := ModularCurve.translation_mem_GammaH M H
  haveI : (CohCarrier.GammaH M H).FiniteIndex :=
    Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH M H)
  obtain ⟨k, g, h, hh, hF⟩ :=
    ModularCurve.exists_modularForm_eventuallyEq_div_of_meromorphic_of_finiteIndex
      (CohCarrier.GammaH M H) F hmer hinv hcusp
  have hhL : qL h ≠ 0 := qL_ne_zero hT h hh
  have hx : qL g / qL h * qL h = qL g := div_mul_cancel₀ (qL g) hhL
  refine ⟨qL g / qL h, ModularCurve.qExpansion_div_mem_laurentBaseChange_xHFunctionField M H g h hh,
    fun τ => ?_⟩
  have hev : ∀ᶠ z in 𝓝[≠] (τ : ℂ), (h : ℍ → ℂ) (ofComplex z) ≠ 0 :=
    eventually_nhdsNE_coe_iff.mpr (eventually_ne_zero h hh τ)
  filter_upwards [hF τ, hev] with z hz1 hz2
  rw [hz1, ModularCurve.realizeOf_eq_div (CohCarrier.GammaH M H) hT g h (qL g / qL h) hx (ofComplex z) hz2]

end S_ModularCurve_exists_realizeOf_eventuallyEq_of_meromorphic_gammaH
end P2MW
export P2MW.S_ModularCurve_exists_realizeOf_eventuallyEq_of_meromorphic_gammaH (solution)
