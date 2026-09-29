-- Prove2me | solution 1 for NumberField.AdelicBox.algebraMap_mem_image_integralFiniteAdeles_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/2a9b9950-1efd-57e5-b52c-94e255de58ac

import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicBox_algebraMap_mem_image_integralFiniteAdeles_iff

set_option autoImplicit false

open NumberField NumberField.AdelicBox IsDedekindDomain
open scoped nonZeroDivisors

theorem solution
    (F : Type) [Field F] [NumberField F] (d : 𝓞 F) (hd : d ≠ 0) (k ξ : F) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ ∈
        (fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F
      ↔ ∃ a : 𝓞 F, ξ = k + (d : F) * (a : F) := by
  have hd' : (d : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hd
  constructor
  · rintro ⟨z, hz, h⟩
    set y : F := (d : F)⁻¹ * (ξ - k) with hy
    have hz' : z = algebraMap F (FiniteAdeleRing (𝓞 F) F) y := by
      have h1 : algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z
          = algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ - k) := by
        rw [map_sub, ← h]; ring
      calc z = algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F)⁻¹ * (d : F)) * z := by
              rw [inv_mul_cancel₀ hd', map_one, one_mul]
        _ = algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)⁻¹
              * (algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) := by rw [map_mul, mul_assoc]
        _ = algebraMap F (FiniteAdeleRing (𝓞 F) F) y := by rw [h1, ← map_mul]
    have hyint : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), v.valuation F y ≤ 1 := fun v => by
      have hv : (algebraMap F (FiniteAdeleRing (𝓞 F) F) y) v ∈ v.adicCompletionIntegers F := by
        rw [← hz']; exact hz v
      rwa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
        show (algebraMap F (FiniteAdeleRing (𝓞 F) F) y) v = (y : v.adicCompletion F) from rfl,
        IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hv
    obtain ⟨a, ha⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one F y hyint
    refine ⟨a, ?_⟩
    rw [RingOfIntegers.coe_eq_algebraMap a, ha, hy, mul_inv_cancel_left₀ hd', add_sub_cancel]
  · rintro ⟨a, rfl⟩
    refine ⟨algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F), fun v => ?_, by simp only [map_add, map_mul]⟩
    rw [RingOfIntegers.coe_eq_algebraMap]
    exact algebraMap_mem_adicCompletionIntegers (𝓞 F) F v a

end S_NumberField_AdelicBox_algebraMap_mem_image_integralFiniteAdeles_iff
end P2MW
export P2MW.S_NumberField_AdelicBox_algebraMap_mem_image_integralFiniteAdeles_iff (solution)
