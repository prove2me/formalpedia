-- Prove2me | solution 1 for GlobalTheory.ThetaDivisionPoints.exists_division_point_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:48:36.202915+00:00
-- url     : https://prove2.me/submissions/890ece8f-d2a8-4a6e-af28-4603c4b330d0

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FourierCoeffUnitCubeTranslateOfEntirePeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EntirePeriodicEqZeroOfFourierCoeffEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CardLePowOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ClassicalThetaLevelAndLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MemSpanThetaOfLevel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_RiemannThetaLevelOneNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsApplySubSmulNeZeroAndApplyAddNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsThetaDivisionPointNeZero
import Theorems.Thm_GlobalTheory_ThetaDivisionPoints_theta_add_int_div
import Theorems.Thm_GlobalTheory_ThetaDivisionPoints_theta_add_tau_div
import Theorems.Thm_GlobalTheory_ThetaDivisionPoints_intChar_injective
import Theorems.Thm_GlobalTheory_ThetaDivisionPoints_mem_span_of_laws
import Theorems.Thm_GlobalTheory_ThetaDivisionPoints_exists_theta_ne_zero
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply



set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix
open GlobalTheory GlobalTheory.ThetaDivisionPoints
namespace GlobalTheory.ThetaDivisionPoints
theorem _root_.solution :
    ∀ (g N : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (β : Fin g → ℂ) (f : (Fin g → ℂ) → ℂ), τ.IsSymm → (τ.map Complex.im).PosDef → 2 ≤ N → (∀ j, β j ≠ 0) → Differentiable ℂ f → f ≠ 0 → (∀ (i : Fin g) z, f (z + Pi.single i 1) = f z) → (∀ (j : Fin g) z, f (z + τ.mulVec (Pi.single j 1)) = β j * cexp (-(2 * Real.pi * I) * N * z j) * f z) → ∃ m n : Fin g → ℤ, f ((N : ℂ)⁻¹ • ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)))) ≠ 0 := by
  intro g N τ β f hs hp hN hβ hd hf0 hper hlaw
  have hτ : τ ∈ SiegelH (Fin g) := ⟨hs, hp⟩
  have hN0 : N ≠ 0 := by omega
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN0
  have hπ : (2 * Real.pi * I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  let w : Fin g → ℂ := fun j => Complex.log (β j) / (2 * Real.pi * I * N) + τ j j / 2
  have hw : ∀ j, β j * cexp (-(2 * Real.pi * I) * N * w j) = eC (-(τ j j) / 2) ^ N := by
    intro j
    rw [eC, ← Complex.exp_nat_mul]
    conv_lhs => rw [← Complex.exp_log (hβ j), ← Complex.exp_add]
    congr 1
    simp only [w]
    field_simp
    ring
  have hF := mem_span_of_laws (f := fun z => f (z + w)) hτ (by omega : 1 ≤ N)
    ⟨hd.comp (by fun_prop), fun i z => by
      rw [add_right_comm, hper], fun j z => by
      rw [add_right_comm, hlaw, ← hw j, Pi.add_apply, mul_add, Complex.exp_add]
      ring⟩
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hF
  obtain ⟨c₀, hc₀⟩ : ∃ c, a c ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hf0
    funext z
    have := congrFun ha (z - w)
    simpa [hcon] using this.symm
  by_contra hcon
  push Not at hcon
  have hvan : ∀ n : Fin g → ℤ, theta (fun i => ((c₀ i : ℕ) : ℝ) / N) 0
      ((N : ℂ) • (-w + (N : ℂ)⁻¹ • τ *ᵥ ofIntVec n)) ((N : ℂ) • τ) = 0 := by
    intro n
    have hli := (linearIndependent_monoidHom (Multiplicative (Fin g → ℤ)) ℂ).comp _
      (intChar_injective (g := g) hN0)
    have := Fintype.linearIndependent_iff.1 hli
      (fun c => a c * theta (fun i => ((c i : ℕ) : ℝ) / N) 0
        ((N : ℂ) • (-w + (N : ℂ)⁻¹ • τ *ᵥ ofIntVec n)) ((N : ℂ) • τ)) (by
        funext m
        have h1 := congrFun ha (-w + (N : ℂ)⁻¹ • τ *ᵥ ofIntVec n + (N : ℂ)⁻¹ • ofIntVec m.toAdd)
        have h2 := hcon m.toAdd n
        have e : -w + (N : ℂ)⁻¹ • τ *ᵥ ofIntVec n + (N : ℂ)⁻¹ • ofIntVec m.toAdd + w =
            (N : ℂ)⁻¹ • ((fun i => (m.toAdd i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) := by
          rw [smul_add]
          change _ = (N : ℂ)⁻¹ • ofIntVec m.toAdd + (N : ℂ)⁻¹ • τ *ᵥ ofIntVec n
          abel
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1 ⊢
        rw [e, h2] at h1
        rw [Pi.zero_apply, ← h1]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [theta_add_int_div hs hNC, mul_assoc, mul_comm (eC _)]
        rfl) c₀
    exact (mul_eq_zero.1 this).resolve_left hc₀
  obtain ⟨c, hc⟩ := exists_theta_ne_zero hτ hN (-w)
  obtain ⟨u, hu, h⟩ := theta_add_tau_div hs hNC (fun i => ((c₀ i : ℕ) : ℝ) / N) (-w)
    (fun i => ((c i : ℕ) : ℤ) - ((c₀ i : ℕ) : ℤ))
  rw [hvan] at h
  have e : ((fun i => ((c₀ i : ℕ) : ℝ) / N) +
      fun i => ((((c i : ℕ) : ℤ) - ((c₀ i : ℕ) : ℤ) : ℤ) : ℝ) / N) =
      fun i => ((c i : ℕ) : ℝ) / N := by
    funext i
    simp only [Pi.add_apply]
    push_cast
    ring
  rw [e] at h
  exact mul_ne_zero hu hc h.symm
end GlobalTheory.ThetaDivisionPoints
