-- Prove2me | solution 1 for ModularCurve.eisensteinNumerator_dvd_mul_of_witness
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/e13b8867-9c0e-5aea-bd0b-ff8abde234e8

import Definitions.Def_ModularCurve_EtaQuotient
import Definitions.Def_NumberTheory_DedekindSum
import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.NumberTheory.Modular
import Theorems.Thm_ModularForm_logEta_specialLinearGroup_smul
import Theorems.Thm_ModularForm_exp_logEta
import Theorems.Thm_ModularForm_continuous_logEta
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_eisensteinNumerator_dvd_mul_of_witness

set_option autoImplicit false

noncomputable section

open Complex ModularGroup

p2m_open "UpperHalfPlane~I"

open scoped ModularForm MatrixGroups Real Topology

namespace WNTW

def logEta (z : ℂ) : ℂ := π * I * z / 12 + ∑' n : ℕ, log (1 - ModularForm.eta_q n z)

private theorem _root_.WNTW.exp_logEta (z : ℍ) : exp (logEta z) = η (z : ℂ) := ModularForm.exp_logEta z

p2m_export "WNTW" "exp_logEta"
private theorem _root_.WNTW.continuous_logEta : Continuous fun τ : ℍ => logEta τ := ModularForm.continuous_logEta

p2m_export "WNTW" "continuous_logEta"
lemma neg_I_mul_re (ζ : ℂ) : (-I * ζ).re = ζ.im := by simp

def phi (γ : SL(2, ℤ)) : ℚ :=
  ((γ 0 0 + γ 1 1 : ℤ) : ℚ) / (((γ 1 0 : ℤ).toNat : ℕ) : ℚ) - 12 * dedekindSum (γ 1 1) (γ 1 0 : ℤ).toNat

def LogLaw (γ : SL(2, ℤ)) : Prop :=
  ∀ z : ℍ, logEta (((γ • z : ℍ) : ℂ)) =
    logEta z + log (-I * ((γ 1 0 : ℤ) * (z : ℂ) + (γ 1 1 : ℤ))) / 2 + π * I / 12 * (phi γ : ℂ)

lemma det_eq (γ : SL(2, ℤ)) : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have := γ.det_coe; rwa [Matrix.det_fin_two] at this

theorem logLaw (γ : SL(2, ℤ)) (hc : 0 < (γ 1 0 : ℤ)) : LogLaw γ := fun z =>
  ModularForm.logEta_specialLinearGroup_smul γ hc z

section N

open ModularCurve

variable (ℓ : ℕ) [NeZero ℓ]

lemma coe_D_smul (τ : ℍ) : ((ModularForm.heckeDiagMatrix ℓ • τ : ℍ) : ℂ) = (ℓ : ℂ) * τ :=
  ModularForm.coe_heckeDiagMatrix_smul (NeZero.ne ℓ) τ

def Lg (τ : ℍ) : ℂ := logEta τ - logEta ((ModularForm.heckeDiagMatrix ℓ • τ : ℍ) : ℂ)

omit [NeZero ℓ] in
lemma continuous_Lg : Continuous (Lg ℓ) :=
  continuous_logEta.sub (continuous_logEta.comp (continuous_const_smul _))

lemma exp_Lg (τ : ℍ) : exp (Lg ℓ τ) = η (τ : ℂ) / η ((ℓ : ℂ) * τ) := by
  rw [Lg, exp_sub, exp_logEta, exp_logEta, coe_D_smul]

lemma disc_div_disc (τ : ℍ) :
    ModularForm.discriminant τ / ModularForm.discriminant (ModularForm.heckeDiagMatrix ℓ • τ) =
      exp (24 * Lg ℓ τ) := by
  rw [show (24 : ℂ) * Lg ℓ τ = ((24 : ℕ) : ℂ) * Lg ℓ τ by push_cast; ring, Complex.exp_nat_mul, exp_Lg,
    div_pow, ModularForm.discriminant, ModularForm.discriminant, coe_D_smul]

lemma companion (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 ℓ) :
    ∃ γ' : SL(2, ℤ), (γ' 0 0 : ℤ) = γ 0 0 ∧ (γ' 1 1 : ℤ) = γ 1 1 ∧ (γ' 1 0 : ℤ) * ℓ = γ 1 0 ∧
      ∀ τ : ℍ, (ModularForm.heckeDiagMatrix ℓ • (γ • τ) : ℍ) = γ' • (ModularForm.heckeDiagMatrix ℓ • τ) := by
  have hdvd : (ℓ : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (CongruenceSubgroup.Gamma0_mem.1 hγ)
  obtain ⟨c', hc'⟩ := hdvd
  have hdet := det_eq γ
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne ℓ
  refine ⟨⟨!![γ 0 0, ℓ * γ 0 1; c', γ 1 1], ?_⟩, rfl, rfl, ?_, fun τ => ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet + (γ 0 1) * hc'
  · show c' * (ℓ : ℤ) = γ 1 0
    rw [hc']; ring
  · apply UpperHalfPlane.ext
    rw [coe_D_smul, coe_specialLinearGroup_apply, coe_specialLinearGroup_apply, coe_D_smul]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, eq_intCast]
    have hden : ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
      simpa [ModularGroup.denom_apply] using UpperHalfPlane.denom_ne_zero (γ : GL (Fin 2) ℝ) τ
    have hden' : ((c' : ℤ) : ℂ) * ((ℓ : ℂ) * (τ : ℂ)) + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
      rw [hc'] at hden; push_cast at hden; rw [← mul_assoc, mul_comm ((c' : ℤ) : ℂ)]; exact hden
    push_cast
    have hc'' : ((γ 1 0 : ℤ) : ℂ) = (ℓ : ℂ) * (c' : ℂ) := by rw [hc']; push_cast; ring
    rw [mul_div_assoc', div_eq_div_iff hden hden']
    linear_combination (-(ℓ : ℂ) * (((γ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 0 1 : ℤ) : ℂ)) * (τ : ℂ)) * hc''

theorem Lg_smul (γ γ' : SL(2, ℤ)) (hc : 0 < (γ 1 0 : ℤ)) (h11 : (γ' 1 1 : ℤ) = γ 1 1)
    (h10 : (γ' 1 0 : ℤ) * ℓ = γ 1 0)
    (hact : ∀ τ : ℍ, (ModularForm.heckeDiagMatrix ℓ • (γ • τ) : ℍ) = γ' • (ModularForm.heckeDiagMatrix ℓ • τ))
    (τ : ℍ) : Lg ℓ (γ • τ) = Lg ℓ τ + π * I / 12 * ((phi γ : ℂ) - (phi γ' : ℂ)) := by
  have hℓpos : (0 : ℤ) < ℓ := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne ℓ)
  have hc'pos : 0 < (γ' 1 0 : ℤ) := by
    by_contra h; push Not at h
    have : (γ' 1 0 : ℤ) * ℓ ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg h hℓpos.le
    linarith
  have L1 := logLaw γ hc τ
  have L2 := logLaw γ' hc'pos (ModularForm.heckeDiagMatrix ℓ • τ)
  rw [Lg, Lg, hact, L1, L2, coe_D_smul, h11]
  have hS : log (-I * (((γ' 1 0 : ℤ) : ℂ) * ((ℓ : ℂ) * (τ : ℂ)) + ((γ 1 1 : ℤ) : ℂ)))
      = log (-I * (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ))) := by
    rw [← h10]; push_cast; ring_nf
  rw [hS]
  ring

theorem eisensteinNumerator_dvd_mul_of_witness (hℓ : 2 ≤ ℓ) (a d : ℤ) (c' : ℕ) (hc' : 0 < c')
    (h1 : a * d ≡ 1 [ZMOD ((ℓ * c' : ℕ) : ℤ)]) (z₀ : ℤ)
    (hδ : 12 * (((a + d : ℤ) : ℚ) * (1 - (ℓ : ℚ)) / (12 * ((ℓ * c' : ℕ) : ℚ))
        + dedekindSum d c' - dedekindSum d (ℓ * c')) = ((Nat.gcd (ℓ - 1) 12 : ℕ) : ℚ) * z₀)
    (m : ℕ) (H : UpperHalfPlane → ℂ) (hH : Continuous H)
    (hpow : ∀ τ : UpperHalfPlane, H τ ^ (ℓ - 1)
      = (ModularForm.discriminant τ / ModularForm.discriminant (ModularForm.heckeDiagMatrix ℓ • τ)) ^ m)
    (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma0 ℓ, ∀ τ : UpperHalfPlane, H (γ • τ) = H τ) :
    (eisensteinNumerator ℓ : ℤ) ∣ (m : ℤ) * z₀ := by

  obtain ⟨b, hb⟩ : ((ℓ * c' : ℕ) : ℤ) ∣ a * d - 1 := (Int.ModEq.dvd h1.symm)
  let γ₀ : SL(2, ℤ) := ⟨!![a, b; (ℓ * c' : ℕ), d], by
    rw [Matrix.det_fin_two_of]; linear_combination hb⟩
  have hγ₀ : γ₀ ∈ CongruenceSubgroup.Gamma0 ℓ := by
    rw [CongruenceSubgroup.Gamma0_mem]
    show (((ℓ * c' : ℕ) : ℤ) : ZMod ℓ) = 0
    push_cast
    rw [ZMod.natCast_self, zero_mul]
  have hc0 : 0 < (γ₀ 1 0 : ℤ) := by
    show (0 : ℤ) < ((ℓ * c' : ℕ) : ℤ)
    have : 0 < ℓ * c' := Nat.mul_pos (by omega) hc'
    exact_mod_cast this
  obtain ⟨γ', h00, h11, h10, hact⟩ := companion ℓ γ₀ hγ₀
  have hc'eq : (γ' 1 0 : ℤ) = c' := by
    have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne ℓ
    have : (γ' 1 0 : ℤ) * ℓ = (c' : ℤ) * ℓ := by rw [h10]; show ((ℓ * c' : ℕ) : ℤ) = _; push_cast; ring
    exact mul_right_cancel₀ hℓ0 this

  have hphi : (phi γ₀ : ℂ) - (phi γ' : ℂ) = ((sharpIndex ℓ : ℕ) : ℂ) * (z₀ : ℂ) := by
    have e0 : phi γ₀ = ((a + d : ℤ) : ℚ) / ((ℓ * c' : ℕ) : ℚ) - 12 * dedekindSum d (ℓ * c') := by
      unfold phi
      show ((a + d : ℤ) : ℚ) / (((((ℓ * c' : ℕ) : ℤ)).toNat : ℕ) : ℚ) - 12 * dedekindSum d (((ℓ * c' : ℕ) : ℤ)).toNat = _
      rw [Int.toNat_natCast]
    have e1 : phi γ' = ((a + d : ℤ) : ℚ) / ((c' : ℕ) : ℚ) - 12 * dedekindSum d c' := by
      unfold phi; rw [h00, h11, hc'eq, Int.toNat_natCast]; rfl
    have hq : phi γ₀ - phi γ' = ((sharpIndex ℓ : ℕ) : ℚ) * z₀ := by
      rw [e0, e1, sharpIndex_def, ← hδ]
      have hC'q : ((c' : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hc'.ne'
      have hℓq : ((ℓ : ℕ) : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne ℓ
      push_cast
      field_simp
      ring
    have := congrArg (fun x : ℚ => (x : ℂ)) hq; push_cast at this; exact this

  have hL : ∀ τ : ℍ, Lg ℓ (γ₀ • τ) = Lg ℓ τ + π * I / 12 * (((sharpIndex ℓ : ℕ) : ℂ) * (z₀ : ℂ)) := by
    intro τ; rw [Lg_smul ℓ γ₀ γ' hc0 h11 h10 hact τ, hphi]

  set N : ℕ := ℓ - 1 with hN
  have hNpos : 0 < N := by omega
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hNpos.ne'
  set s : ℂ := (24 * m : ℂ) / N with hs
  have hsN : (N : ℂ) * s = 24 * m := by rw [hs]; field_simp
  let Q : ℍ → ℂ := fun τ => H τ * exp (-(s * Lg ℓ τ))
  have hQN : ∀ τ, Q τ ^ N = 1 := by
    intro τ
    have hu := hpow τ
    rw [disc_div_disc] at hu
    show (H τ * exp (-(s * Lg ℓ τ))) ^ N = 1
    rw [mul_pow, hu, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add,
      Complex.exp_eq_one_iff]
    exact ⟨0, by push_cast; linear_combination (-(Lg ℓ τ)) * hsN⟩
  have hQcont : Continuous Q := hH.mul (Complex.continuous_exp.comp ((continuous_Lg ℓ).const_smul s |>.neg |>.congr
    fun τ => by simp [smul_eq_mul]))
  have hfin : ({w : ℂ | w ^ N = 1} : Set ℂ).Finite := by
    refine Set.Finite.subset (Finset.finite_toSet ((Polynomial.nthRoots N (1 : ℂ)).toFinset)) ?_
    intro w hw
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    exact (Polynomial.mem_nthRoots hNpos).mpr hw
  have hQconst : ∀ τ τ', Q τ = Q τ' := fun τ τ' =>
    isPreconnected_univ.constant_of_mapsTo hfin.isDiscrete hQcont.continuousOn
      (fun τ _ => hQN τ) (Set.mem_univ τ) (Set.mem_univ τ')
  have hHQ : ∀ τ, H τ = Q τ * exp (s * Lg ℓ τ) := by
    intro τ; show H τ = H τ * exp (-(s * Lg ℓ τ)) * exp (s * Lg ℓ τ)
    rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
  have hQne : ∀ τ, Q τ ≠ 0 := by
    intro τ h0
    have := hQN τ; rw [h0, zero_pow hNpos.ne'] at this; exact zero_ne_one this

  have hE : exp (s * (π * I / 12 * (((sharpIndex ℓ : ℕ) : ℂ) * (z₀ : ℂ)))) = 1 := by
    have h := hinv γ₀ hγ₀ UpperHalfPlane.I
    rw [hHQ, hHQ, hQconst (γ₀ • UpperHalfPlane.I) UpperHalfPlane.I, hL, mul_add, Complex.exp_add,
      ← mul_assoc] at h
    have hne : Q UpperHalfPlane.I * exp (s * Lg ℓ UpperHalfPlane.I) ≠ 0 :=
      mul_ne_zero (hQne _) (Complex.exp_ne_zero _)
    exact (mul_eq_left₀ hne).1 h
  obtain ⟨M, hM⟩ := Complex.exp_eq_one_iff.1 hE

  have hkn : (sharpIndex ℓ : ℤ) * (eisensteinNumerator ℓ : ℤ) = N := by
    rw [hN]; exact_mod_cast sharpIndex_mul_eisensteinNumerator ℓ
  have hk0 : (sharpIndex ℓ : ℤ) ≠ 0 := by exact_mod_cast (sharpIndex_pos ℓ).ne'
  have hmain : (m : ℤ) * z₀ = M * (eisensteinNumerator ℓ : ℤ) := by
    have hπ : (π : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) I_ne_zero
    have h1 : s * (π * I / 12 * (((sharpIndex ℓ : ℕ) : ℂ) * (z₀ : ℂ))) * N
        = (2 * (m : ℂ) * ((sharpIndex ℓ : ℕ) : ℂ) * (z₀ : ℂ)) * (π * I) := by
      rw [show s * (π * I / 12 * (((sharpIndex ℓ : ℕ) : ℂ) * (z₀ : ℂ))) * N
          = (N * s) * (π * I / 12 * (((sharpIndex ℓ : ℕ) : ℂ) * (z₀ : ℂ))) by ring, hsN]
      ring
    rw [hM] at h1
    have h2πI : (2 * ((π : ℂ) * I)) ≠ 0 := mul_ne_zero two_ne_zero hπ
    have h1' : (M : ℂ) * N * (2 * (π * I)) = ((m : ℂ) * ((sharpIndex ℓ : ℕ) : ℂ) * (z₀ : ℂ)) * (2 * (π * I)) := by
      linear_combination h1
    have h2 : (M : ℂ) * N = (m : ℂ) * ((sharpIndex ℓ : ℕ) : ℂ) * (z₀ : ℂ) := mul_right_cancel₀ h2πI h1'
    have h3 : (M : ℤ) * (N : ℤ) = (m : ℤ) * (sharpIndex ℓ : ℤ) * z₀ := by exact_mod_cast h2
    rw [← hkn] at h3
    have : (sharpIndex ℓ : ℤ) * ((m : ℤ) * z₀) = (sharpIndex ℓ : ℤ) * (M * (eisensteinNumerator ℓ : ℤ)) := by
      linear_combination -h3
    exact mul_left_cancel₀ hk0 this
  have hdvd : (eisensteinNumerator ℓ : ℤ) ∣ (m : ℤ) * z₀ := ⟨M, by rw [hmain]; ring⟩
  exact hdvd

end N

end WNTW

end

theorem solution (ℓ : ℕ) [NeZero ℓ] (hℓ : 2 ≤ ℓ) (a d : ℤ) (c' : ℕ) (hc' : 0 < c') (h1 : Int.ModEq ((ℓ * c' : ℕ) : ℤ) (a * d) 1) (z₀ : ℤ) (hδ : 12 * (((a + d : ℤ) : ℚ) * (1 - (ℓ : ℚ)) / (12 * ((ℓ * c' : ℕ) : ℚ)) + dedekindSum d c' - dedekindSum d (ℓ * c')) = ((Nat.gcd (ℓ - 1) 12 : ℕ) : ℚ) * z₀) (m : ℕ) (H : UpperHalfPlane → ℂ) (hH : Continuous H) (hpow : ∀ τ : UpperHalfPlane, H τ ^ (ℓ - 1) = (ModularForm.discriminant τ / ModularForm.discriminant (ModularForm.heckeDiagMatrix ℓ • τ)) ^ m) (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma0 ℓ, ∀ τ : UpperHalfPlane, H (γ • τ) = H τ) : (ModularCurve.eisensteinNumerator ℓ : ℤ) ∣ (m : ℤ) * z₀ :=
  WNTW.eisensteinNumerator_dvd_mul_of_witness ℓ hℓ a d c' hc' h1 z₀ hδ m H hH hpow hinv

end S_ModularCurve_eisensteinNumerator_dvd_mul_of_witness
end P2MW
export P2MW.S_ModularCurve_eisensteinNumerator_dvd_mul_of_witness (solution)
