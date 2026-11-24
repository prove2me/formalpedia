-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AdeleCharLocal.ker_mem_nhds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:23:28.567895+00:00
-- url     : https://prove2.me/submissions/41cdfb3d-4df8-44c8-ad4a-f1e39c51719c

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SiegelWeilUnitaryConvergent
import Definitions.Def_Formalism_UnipotentAdelicQuotients_StdAdditiveCharExists
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSet
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_HermitianCharacters_SelfDualLatticeFiltrationCharacter
import Theorems.Thm_GlobalTheory_AdLat_OpenLat_exists_nsmul_adele
import Theorems.Thm_GlobalTheory_AdLat_OpenLat_nsmul_integral_mem_nhds
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct RestrictedProduct nonZeroDivisors
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AdeleCharLocal
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.CompanionTheory.AdeleCharLocal
theorem _root_.solution {ψ : AddChar (AF F) ℂ} (hc : Continuous ψ)
    (hn : ∀ x, ‖ψ x‖ = 1) : {a : Af F | ψ (pairA F 0 a) = 1} ∈ 𝓝 (0 : Af F) := by
  let χ : Af F → Circle := fun a => ⟨ψ (pairA F 0 a), by simpa [Submonoid.unitSphere] using hn _⟩
  have hχ : Continuous χ := (hc.comp (continuous_const.prodMk continuous_id)).subtype_mk _
  have h0 : χ 0 = 1 := Subtype.ext ψ.map_zero_eq_one
  have hV : χ ⁻¹' Circle.centeredArc (Real.pi / 2) ∈ 𝓝 (0 : Af F) := by
    refine ((Circle.isOpen_centeredArc _).preimage hχ).mem_nhds ?_
    rw [Set.mem_preimage, h0, Circle.mem_centeredArc (by linarith [Real.pi_pos])]
    simp [Real.pi_pos]
  obtain ⟨N, hN, hNV⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ hV
  refine Filter.mem_of_superset (GlobalTheory.AdLat.OpenLat.nsmul_integral_mem_nhds F N hN) ?_
  rintro _ ⟨a, ha, rfl⟩
  have : χ (N • a) = 1 := by
    refine Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two fun n _ => ?_
    have h1 := hNV (n • a) fun v => nsmul_mem (ha v) n
    have h2 : χ (N • n • a) = χ (N • a) ^ n := by
      apply Subtype.ext
      show ψ (pairA F 0 (N • n • a)) = ((χ (N • a) ^ n : Circle) : ℂ)
      rw [Circle.coe_pow, smul_comm]
      show _ = ψ (pairA F 0 (N • a)) ^ n
      rw [← AddChar.map_nsmul_eq_pow]
      congr 1
      exact Prod.ext (smul_zero n).symm rfl
    rwa [Set.mem_preimage, h2] at h1
  exact congrArg Subtype.val this
end GlobalTheory.CompanionTheory.AdeleCharLocal
