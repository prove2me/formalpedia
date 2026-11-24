-- Prove2me | solution 1 for GlobalTheory.NormSquareRamified.exists_sq_sub_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:31:12.879421+00:00
-- url     : https://prove2.me/submissions/d4e250e0-4ba5-4413-b947-672691e7dce5

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsUnitNormOfIsCoprime
import Theorems.Thm_GlobalTheory_NormSquareRamified_dvd_of_mul_sq
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_Q3_CMRootsOfUnity_not_dvd_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.NormSquareRamified
namespace GlobalTheory.NormSquareRamified
theorem _root_.solution {F : Type*} [Field F] [NumberField F] {p : ℕ} (hp : p.Prime) {q : ℤ}
    (hq : ¬ (p : ℤ) ∣ q) (s : F) (hs : s * s = ((q * p : ℤ) : F)) (y : 𝓞 F) :
    ∃ A : ℤ, (p : ℤ) ∣ A ^ 2 - 4 * Algebra.norm ℤ y := by
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  set m : ℚ := ((q * p : ℤ) : ℚ) with hm
  have hm0 : m ≠ 0 := by
    rw [hm, Int.cast_ne_zero]
    exact mul_ne_zero (fun h => hq (h ▸ dvd_zero _)) hpp.ne_zero
  have : Fact (∀ r : ℚ, r ^ 2 ≠ m + 0 * r) := ⟨fun r hr => by
    rw [zero_mul, add_zero] at hr
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact hm0 (by rw [← hr]; simp)
    have : m * r⁻¹ ^ 2 = ((1 : ℤ) : ℚ) := by
      rw [← hr]; field_simp; simp
    exact hpp.not_dvd_one (dvd_of_mul_sq hp hq _ this)⟩
  let K := QuadraticAlgebra ℚ m 0
  let φ : K →ₐ[ℚ] F := QuadraticAlgebra.lift ⟨s, by
    rw [hs, zero_smul, add_zero, hm, Algebra.smul_def, mul_one, map_intCast]⟩
  let : Algebra K F := φ.toRingHom.toAlgebra
  have : IsScalarTower ℚ K F := IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  have : Module.Finite ℚ K := Module.Finite.of_basis (QuadraticAlgebra.basis m 0)
  set w : K := Algebra.norm K (y : F) with hw
  have hwi : IsIntegral ℤ w := Algebra.isIntegral_norm K y.isIntegral_coe
  have hn : ((Algebra.norm ℤ y : ℤ) : ℚ) = w.norm := by
    rw [Algebra.coe_norm_int, ← Algebra.norm_norm (S := K), ← hw,
      ← QuadraticAlgebra.det_toLinearMap_eq_norm, Algebra.norm_apply]
    rfl
  have hst : IsIntegral ℤ (star w) := hwi.map (starRingEnd K).toIntAlgHom
  have htr : IsIntegral ℤ (QuadraticAlgebra.trace w) := by
    have := hwi.add hst
    rw [← QuadraticAlgebra.algebraMap_trace_eq_add_star] at this
    exact (isIntegral_algebraMap_iff (algebraMap ℚ K).injective).mp this
  obtain ⟨A, hA⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp htr
  refine ⟨A, dvd_of_mul_sq hp hq (2 * w.im) ?_⟩
  rw [← hm]
  rw [eq_intCast] at hA
  push_cast
  rw [hA, hn, QuadraticAlgebra.trace_def, QuadraticAlgebra.norm_def]
  ring
end GlobalTheory.NormSquareRamified
