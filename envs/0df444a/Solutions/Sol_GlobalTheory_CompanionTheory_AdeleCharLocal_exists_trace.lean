-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AdeleCharLocal.exists_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:00:43.88203+00:00
-- url     : https://prove2.me/submissions/0de5857a-aea9-48a1-a379-8733c55396c6

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SiegelWeilUnitaryConvergent
import Definitions.Def_Formalism_UnipotentAdelicQuotients_StdAdditiveCharExists
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSet
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_HermitianCharacters_SelfDualLatticeFiltrationCharacter
import Theorems.Thm_GlobalTheory_CompanionTheory_AdeleCharLocal_exists_eq_exp
import Theorems.Thm_GlobalTheory_CompanionTheory_AdeleCharLocal_pairA_add
import Theorems.Thm_GlobalTheory_CompanionTheory_AdeleCharLocal_exists_nsmul_inf
import Theorems.Thm_GlobalTheory_CompanionTheory_AdeleCharLocal_exists_realHom
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
theorem _root_.solution {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) :
    ∃ a : F, ∀ x : F, ψ (pairA F (algebraMap F _ x) 0) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F (a * x) : ℚ) : ℂ)) := by
  classical
  obtain ⟨N, hN, hNr⟩ := exists_nsmul_inf hψ
  obtain ⟨ρ, hρ⟩ := exists_realHom (F := F)
  have hρq : ∀ q : ℚ, ρ (q : ℝ) = algebraMap F (Ainf F) (q : F) := fun q =>
    RingHom.congr_fun (RingHom.ext_rat (ρ.comp (Rat.castHom ℝ)) ((algebraMap F (Ainf F)).comp (Rat.castHom F))) q
  have hadd : ∀ x y : Ainf F, ψ (pairA F (x + y) 0) = ψ (pairA F x 0) * ψ (pairA F y 0) := fun x y => by
    rw [← AddChar.map_add_eq_mul, ← pairA_add, add_zero]
  have h0 : ψ (pairA F 0 0) = 1 := ψ.map_zero_eq_one
  have key : ∀ r : 𝓞 F, ∃ c : ℚ, ∀ q : ℚ, ψ (pairA F (algebraMap F _ (q • (r : F))) 0) =
      Complex.exp (2 * Real.pi * Complex.I * ((q * c : ℚ) : ℂ)) := fun r => by
    obtain ⟨c, hc⟩ := exists_eq_exp (fun t => ψ (pairA F (ρ t * algebraMap F _ (r : F)) 0))
      (hψ.1.comp ((hρ.mul continuous_const).prodMk continuous_const)) (fun t => hψ.2.1 _)
      (by simp only [map_zero, zero_mul, h0]) (fun s t => by simp only [map_add, add_mul, hadd])
    have hq : ∀ q : ℚ, ψ (pairA F (algebraMap F _ ((q : F) * (r : F))) 0) =
        Complex.exp (2 * Real.pi * Complex.I * ((c * q : ℝ) : ℂ)) := fun q => by
      rw [← hc, hρq, map_mul]
    have h1 := hq N
    rw [Rat.cast_natCast, hNr, eq_comm, Complex.exp_eq_one_iff] at h1
    obtain ⟨n, hn⟩ := h1
    rw [mul_comm (n : ℂ), mul_right_inj' Complex.two_pi_I_ne_zero] at hn
    have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    refine ⟨n / N, fun q => ?_⟩
    rw [Rat.smul_def, hq]
    congr 2
    push_cast at hn ⊢
    rw [← hn]
    field_simp
  choose c hc using key
  let b := integralBasis F
  let φ : F →ₗ[ℚ] ℚ := b.constr ℚ fun i => c (RingOfIntegers.basis F i)
  obtain ⟨a, ha⟩ := ((Algebra.traceForm ℚ F).toDual (traceForm_nondegenerate ℚ F)).surjective φ
  have ha' : ∀ x, Algebra.trace ℚ F (a * x) = φ x := fun x => by
    rw [← ha]; rfl
  refine ⟨a, fun x => ?_⟩
  rw [ha', ← b.sum_repr x]
  refine Finset.sum_induction _ (fun y : F => ψ (pairA F (algebraMap F _ y) 0) =
    Complex.exp (2 * Real.pi * Complex.I * ((φ y : ℚ) : ℂ))) (fun y z hy hz => ?_) ?_ fun i _ => ?_
  · rw [map_add, hadd, hy, hz, map_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  · simp only [map_zero, h0, Rat.cast_zero, mul_zero, Complex.exp_zero]
  · rw [map_smul φ, Module.Basis.constr_basis, smul_eq_mul, ← hc, integralBasis_apply]
end GlobalTheory.CompanionTheory.AdeleCharLocal
