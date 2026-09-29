-- Prove2me | solution 1 for MTT.Cohomology.signed_evaluation
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-06T16:03:06.675689+00:00
-- url     : https://prove2.me/submissions/0ca7055f-7659-4f6e-a444-b1da7da69e66

import Definitions.Def_MTT_Cohomology
import Mathlib.RingTheory.Flat.Basic
import Theorems.Thm_MTT_Cohomology_reflection_class
import Theorems.Thm_MTT_Cohomology_integral_class_character_law
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open scoped BigOperators
open MTT.Cohomology

namespace P2MSE

open MvPolynomial

variable {R : Type*} [CommRing R]

/-! ### The coefficient action is a monoid homomorphism -/

theorem act_apply (A : Matrix (Fin 2) (Fin 2) ℤ) (P : Binary R) :
    act A P = MvPolynomial.bind₁ (fun i : Fin 2 =>
      ∑ a : Fin 2, (A a i : R) • MvPolynomial.X a) P := rfl

theorem act_one (P : Binary R) : act 1 P = P := by
  rw [act_apply]
  have h : (fun i : Fin 2 => ∑ a : Fin 2, ((1 : Matrix (Fin 2) (Fin 2) ℤ) a i : R) •
      MvPolynomial.X a) = fun i : Fin 2 => (MvPolynomial.X i : Binary R) := by
    funext i
    rw [Fin.sum_univ_two]
    fin_cases i <;> simp [Matrix.one_apply]
  rw [h, MvPolynomial.bind₁_X_left, AlgHom.id_apply]

theorem act_mul (A B : Matrix (Fin 2) (Fin 2) ℤ) (P : Binary R) :
    act (A * B) P = act A (act B P) := by
  simp only [act_apply]
  rw [MvPolynomial.bind₁_bind₁]
  have hfun : (fun i : Fin 2 => (MvPolynomial.bind₁
        (fun j : Fin 2 => (∑ a : Fin 2, (A a j : R) • MvPolynomial.X a : Binary R)))
        (∑ a : Fin 2, (B a i : R) • MvPolynomial.X a : Binary R))
      = fun i : Fin 2 => (∑ a : Fin 2, ((A * B) a i : R) • MvPolynomial.X a : Binary R) := by
    funext i
    rw [map_sum]
    simp only [map_smul, MvPolynomial.bind₁_X_right, Fin.sum_univ_two, Matrix.mul_apply]
    match_scalars <;> push_cast <;> ring
  rw [hfun]

end P2MSE

namespace P2MSE

open MvPolynomial

variable {R : Type*} [CommRing R]

/-- The reflection matrix `diag(-1, 1)`. -/
abbrev Jm : Matrix (Fin 2) (Fin 2) ℤ := !![-1, 0; 0, 1]

theorem Jm_mul_Jm : Jm * Jm = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

theorem act_Jm_X0 : act Jm (MvPolynomial.X 0 : Binary R) = -MvPolynomial.X 0 := by
  rw [act_apply]
  simp [Fin.sum_univ_two]

theorem act_Jm_X1 : act Jm (MvPolynomial.X 1 : Binary R) = MvPolynomial.X 1 := by
  rw [act_apply]
  simp [Fin.sum_univ_two]

theorem act_Jm_C (a : R) : act Jm (MvPolynomial.C a : Binary R) = MvPolynomial.C a := by
  rw [act_apply]; simp

theorem act_add (A : Matrix (Fin 2) (Fin 2) ℤ) (P Q : Binary R) :
    act A (P + Q) = act A P + act A Q := map_add _ _ _

theorem act_smul (A : Matrix (Fin 2) (Fin 2) ℤ) (c : R) (P : Binary R) :
    act A (c • P) = c • act A P := map_smul _ _ _

theorem act_mul' (A : Matrix (Fin 2) (Fin 2) ℤ) (P Q : Binary R) :
    act A (P * Q) = act A P * act A Q := by
  simp only [act_apply, map_mul]

/-- The reflection multiplies the `X^{d₀}Y^{d₁}` coefficient by `(-1)^{d₀}`. -/
theorem actJ_coeff (P : Binary R) (d : Fin 2 →₀ ℕ) :
    MvPolynomial.coeff d (act Jm P) = (-1 : R) ^ (d 0) * MvPolynomial.coeff d P := by
  induction P using MvPolynomial.induction_on generalizing d with
  | C a =>
      rw [act_Jm_C, MvPolynomial.coeff_C]
      split_ifs with h
      · rw [← h]; simp
      · rw [mul_zero]
  | add p q hp hq => rw [act_add, MvPolynomial.coeff_add, hp d, hq d,
      MvPolynomial.coeff_add, mul_add]
  | mul_X p i hp =>
      rw [act_mul']
      have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
      rcases hi with rfl | rfl
      · rw [act_Jm_X0, mul_neg, MvPolynomial.coeff_neg, MvPolynomial.coeff_mul_X',
          MvPolynomial.coeff_mul_X']
        by_cases h : (0 : Fin 2) ∈ d.support
        · rw [if_pos h, if_pos h, hp (d - Finsupp.single (0 : Fin 2) 1)]
          have hd0 : d 0 ≠ 0 := Finsupp.mem_support_iff.mp h
          have hsub : ((d - Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ)) 0 = d 0 - 1 := by
            simp [Finsupp.tsub_apply]
          rw [hsub]
          obtain ⟨m, hm⟩ : ∃ m, d 0 = m + 1 := ⟨d 0 - 1, by omega⟩
          rw [hm]
          simp only [Nat.add_sub_cancel, pow_succ]
          ring
        · rw [if_neg h, if_neg h]; simp
      · rw [act_Jm_X1, MvPolynomial.coeff_mul_X', MvPolynomial.coeff_mul_X']
        by_cases h : (1 : Fin 2) ∈ d.support
        · rw [if_pos h, if_pos h, hp (d - Finsupp.single (1 : Fin 2) 1)]
          have hsub : ((d - Finsupp.single (1 : Fin 2) 1 : Fin 2 →₀ ℕ)) 0 = d 0 := by
            simp [Finsupp.tsub_apply]
          rw [hsub]
        · rw [if_neg h, if_neg h]; simp

/-! ### The reflection on cusps -/

theorem fractional_Jm_infty : fractional Jm OnePoint.infty = OnePoint.infty := by
  simp [fractional]

theorem fractional_Jm_coe (r : ℚ) : fractional Jm ((r : ℚ) : Cusp) = ((-r : ℚ) : Cusp) := by
  norm_num [fractional]

theorem fractional_Jm_involutive (x : Cusp) : fractional Jm (fractional Jm x) = x := by
  induction x using OnePoint.rec with
  | infty => rw [fractional_Jm_infty, fractional_Jm_infty]
  | coe r => rw [fractional_Jm_coe, fractional_Jm_coe]; norm_num

end P2MSE

namespace P2MSE

open MvPolynomial

variable {R : Type*} [CommRing R]

/-! ### Linearity of the slash, Hecke and reflection operators -/

theorem slash_add (g : Matrix (Fin 2) (Fin 2) ℤ) (φ ψ : (Cusp × Cusp) → Binary R) :
    slash g (φ + ψ) = slash g φ + slash g ψ := by
  funext D; simp [slash, act_add]

theorem slash_smul (g : Matrix (Fin 2) (Fin 2) ℤ) (c : R) (φ : (Cusp × Cusp) → Binary R) :
    slash g (c • φ) = c • slash g φ := by
  funext D; simp [slash, act_smul]

theorem primeHecke_add (e : R) (l : ℕ) (φ ψ : (Cusp × Cusp) → Binary R) :
    primeHecke e l (φ + ψ) = primeHecke e l φ + primeHecke e l ψ := by
  simp only [primeHecke, slash_add, Finset.sum_add_distrib, smul_add]
  abel

theorem primeHecke_smul (e : R) (l : ℕ) (c : R) (φ : (Cusp × Cusp) → Binary R) :
    primeHecke e l (c • φ) = c • primeHecke e l φ := by
  simp only [primeHecke, slash_smul, smul_add, Finset.smul_sum]
  rw [smul_comm]

theorem reflection_add (φ ψ : (Cusp × Cusp) → Binary R) :
    reflection (φ + ψ) = reflection φ + reflection ψ := by
  funext D; simp [reflection, act_add]

theorem reflection_smul (c : R) (φ : (Cusp × Cusp) → Binary R) :
    reflection (c • φ) = c • reflection φ := by
  funext D; simp [reflection, act_smul]

theorem reflection_reflection (φ : (Cusp × Cusp) → Binary R) :
    reflection (reflection φ) = φ := by
  funext D
  show act Jm (act Jm (φ (fractional Jm (fractional Jm D.1),
      fractional Jm (fractional Jm D.2)))) = φ D
  rw [fractional_Jm_involutive, fractional_Jm_involutive, ← act_mul, Jm_mul_Jm, act_one]

/-! ### The reflection on coefficient functionals -/

theorem reflection_eval {N n : ℕ} (φ ψ : Hc N n R) (hψ : ψ.val = reflection φ.val)
    (j : ℕ) (r : ℚ) :
    evaluation j r ψ = (-1 : R) ^ j * evaluation j (-r) φ := by
  show MvPolynomial.coeff _ (ψ.val _) = _
  rw [hψ]
  show MvPolynomial.coeff _ (act Jm (φ.val (fractional Jm OnePoint.infty,
    fractional Jm ((r : ℚ) : Cusp)))) = _
  rw [fractional_Jm_infty, fractional_Jm_coe, actJ_coeff]
  rfl

end P2MSE


namespace P2MSE

theorem sign_sq (s : Bool) : ((MTT.sign s : ℤ) : ℂ) * ((MTT.sign s : ℤ) : ℂ) = 1 := by
  cases s <;> norm_num [MTT.sign]

/-- The signed projection is an eigenvector of the reflection. -/
theorem refl_clause {N n : ℕ} (Φ Ψ : Hc N n ℂ) (ss : ℂ) (hss : ss * ss = 1)
    (hΨ : Ψ.val = reflection Φ.val) :
    reflection (((2⁻¹ : ℂ) • (Φ + ss • Ψ)).val)
      = ss • (((2⁻¹ : ℂ) • (Φ + ss • Ψ)).val) := by
  have hval : ((2⁻¹ : ℂ) • (Φ + ss • Ψ)).val
      = (2⁻¹ : ℂ) • (Φ.val + ss • Ψ.val) := rfl
  rw [hval, reflection_smul, reflection_add, reflection_smul, hΨ,
    reflection_reflection, ← hΨ]
  match_scalars <;>
    first
      | linear_combination (2⁻¹ : ℂ) * hss
      | linear_combination (-2⁻¹ : ℂ) * hss
      | ring

end P2MSE

open P2MSE in
theorem solution {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k-2) ℂ)
    (hI : ∀ f, IntegralClass f (I f)) (hT : HeckeEquivariant I)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι) :
    ∃ φ : Bool → Hc N (k-2) ℂ, ∀ s,
      SignedClass f.form s (φ s) ∧
      Packet (fun d => ι (f.epsilon d)) (fun l => ι (f.coeff l)) s (φ s) := by
  classical
  set Φ : Hc N (k-2) ℂ := I f.form with hΦdef
  obtain ⟨⟨Ψ, hΨ⟩, hcomm, hchar⟩ := MTT.Cohomology.reflection_class Φ
  -- the two signed projections
  refine ⟨fun s => (2⁻¹ : ℂ) • (Φ + ((MTT.sign s : ℤ) : ℂ) • Ψ), fun s => ?_⟩
  set ss : ℂ := ((MTT.sign s : ℤ) : ℂ) with hssdef
  have hss : ss * ss = 1 := sign_sq s
  have hval : ((2⁻¹ : ℂ) • (Φ + ss • Ψ)).val
      = (2⁻¹ : ℂ) • (Φ.val + ss • Ψ.val) := rfl
  constructor
  · -- SignedClass
    intro j r hj
    have h1 : evaluation j r ((2⁻¹ : ℂ) • (Φ + ss • Ψ))
        = (2⁻¹ : ℂ) * (evaluation j r Φ + ss * evaluation j r Ψ) := by
      rw [map_smul, map_add, map_smul, smul_eq_mul, smul_eq_mul]
    rw [h1, reflection_eval Φ Ψ hΨ j r, hI f.form j r hj, hI f.form j (-r) hj]
    rw [MTT.signedIntegral]
    push_cast
    ring
  · refine ⟨?_, ?_, ?_⟩
    · -- prime Hecke eigenvalues
      intro l hl
      set E : ℂ := ι (f.epsilon (l : ZMod N)) with hEdef
      set c : ℂ := ι (f.coeff l) with hcdef
      have hΦH : primeHecke E l Φ.val = c • Φ.val := by
        set e : DirichletCharacter ℂ N := f.epsilon.ringHomComp ι with hedef
        have hel : e (l : ZMod N) = E := by rw [hedef, MulChar.ringHomComp_apply]
        have hg : ∀ z, (c • f.form) z = MTT.heckePrime k (e (l : ZMod N)) l f.form z := by
          intro z
          rw [hel, hEdef, f.eigen l hl z]
          rfl
        have hmain := hT e l hl f.form (c • f.form) hg
        rw [map_smul, hel] at hmain
        exact hmain.symm
      have hΨH : primeHecke E l Ψ.val = c • Ψ.val := by
        rw [hΨ, ← hcomm E l, hΦH, reflection_smul, ← hΨ]
      rw [hval, primeHecke_smul, primeHecke_add, primeHecke_smul, hΦH, hΨH]
      show (2⁻¹ : ℂ) • (c • Φ.val + ss • c • Ψ.val)
        = c • ((2⁻¹ : ℂ) • (Φ.val + ss • Ψ.val))
      match_scalars <;> ring
    · -- nebentype
      intro γ x y
      have hcharΦ : ∀ (γ : CongruenceSubgroup.Gamma0 N) (x y : Cusp),
          Φ.val (cuspAct γ.val x, cuspAct γ.val y)
            = ι (f.epsilon (γ.val 1 1 : ZMod N)) • act γ.val.val (Φ.val (x, y)) :=
        fun γ x y => MTT.Cohomology.integral_class_character_law hN hk ι f Φ (hI f.form) γ x y
      have hcharΨ := hchar (fun d => ι (f.epsilon d)) hcharΦ γ x y
      rw [← hΨ] at hcharΨ
      show ((2⁻¹ : ℂ) • (Φ.val + ss • Ψ.val)) _ = _
      show (2⁻¹ : ℂ) • (Φ.val (cuspAct γ.val x, cuspAct γ.val y)
        + ss • Ψ.val (cuspAct γ.val x, cuspAct γ.val y)) = _
      rw [hcharΦ γ x y, hcharΨ]
      show _ = ι (f.epsilon (γ.val 1 1 : ZMod N)) •
        act γ.val.val ((2⁻¹ : ℂ) • (Φ.val (x, y) + ss • Ψ.val (x, y)))
      rw [act_smul, act_add, act_smul]
      match_scalars <;> ring
    · -- reflection
      rw [← hssdef]
      exact refl_clause Φ Ψ ss hss hΨ
