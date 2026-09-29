-- Prove2me | solution 1 for MTT.Cohomology.integral_finite_generation
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-06T15:22:30.779327+00:00
-- url     : https://prove2.me/submissions/995ef47b-896f-4f6c-940b-fc6223e0eeb5

import Mathlib
import Definitions.Def_MTT_Cohomology
import Mathlib.RingTheory.Flat.Basic
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

namespace P2MFG

open MvPolynomial

abbrev SL2 := Matrix.SpecialLinearGroup (Fin 2) ℤ

/-! ### The action of `SL(2,ℤ)` on the cusps, in coordinates -/

theorem cuspAct_infty (g : SL2) :
    cuspAct g OnePoint.infty
      = if (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 then OnePoint.infty
        else ((((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℚ)
              / ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℚ)) : ℚ) := by
  rw [cuspAct, OnePoint.smul_infty_eq_ite]
  simp [Matrix.SpecialLinearGroup.mapGL]

theorem cuspAct_zero (g : SL2) :
    cuspAct g ((0 : ℚ) : Cusp)
      = if (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 0 then OnePoint.infty
        else ((((g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℚ)
              / ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℚ)) : ℚ) := by
  rw [cuspAct, OnePoint.smul_some_eq_ite]
  simp [Matrix.SpecialLinearGroup.mapGL]

theorem cuspAct_mul (g h : SL2) (x : Cusp) :
    cuspAct (g * h) x = cuspAct g (cuspAct h x) := by
  simp [cuspAct, map_mul, mul_smul]

/-! ### Elementary consequences of the cocycle relation -/

variable {N n : ℕ}

theorem hc_add (φ : Hc N n ℤ) (x y z : Cusp) :
    φ.val (x, y) + φ.val (y, z) = φ.val (x, z) := φ.2.2.1 x y z

theorem hc_hom (φ : Hc N n ℤ) (x y : Cusp) : φ.val (x, y) ∈ MTT.Cohomology.Sym ℤ n := φ.2.1 x y

theorem hc_equiv (φ : Hc N n ℤ) (γ : CongruenceSubgroup.Gamma1 N) (x y : Cusp) :
    φ.val (cuspAct γ.val x, cuspAct γ.val y) = act γ.val.val (φ.val (x, y)) :=
  φ.2.2.2 γ x y

theorem hc_self (φ : Hc N n ℤ) (x : Cusp) : φ.val (x, x) = 0 := by
  have h := hc_add φ x x x
  have h2 : φ.val (x, x) + φ.val (x, x) = 0 + φ.val (x, x) := by rw [zero_add]; exact h
  exact add_right_cancel h2

theorem hc_swap (φ : Hc N n ℤ) (x y : Cusp) : φ.val (y, x) = -φ.val (x, y) := by
  have h : φ.val (x, y) + φ.val (y, x) = 0 := by rw [hc_add φ x y x, hc_self]
  have h2 : φ.val (x, y) + φ.val (y, x) - φ.val (x, y) = 0 - φ.val (x, y) := by rw [h]
  simpa [add_sub_cancel_left] using h2

end P2MFG

namespace P2MFG

open MvPolynomial

variable {N n : ℕ}

/-- Manin's trick. If `φ` kills every unimodular path `(g·0, g·∞)`, it kills every
path `(∞, p/q)`; the induction is on the denominator. -/
theorem manin_aux (φ : Hc N n ℤ)
    (hU : ∀ g : SL2, φ.val (cuspAct g ((0 : ℚ) : Cusp), cuspAct g OnePoint.infty) = 0) :
    ∀ (m : ℕ) (p q : ℤ), 0 < q → q ≤ (m : ℤ) → IsCoprime p q →
      φ.val (OnePoint.infty, (((p : ℚ) / (q : ℚ)) : Cusp)) = 0 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro p q hq hqm hcop
    obtain ⟨u, v, huv⟩ := hcop
    set q' : ℤ := u % q with hq'def
    set p' : ℤ := -(v + p * (u / q)) with hp'def
    have hdet : p * q' - p' * q = 1 := by
      rw [hq'def, hp'def, Int.emod_def]
      linear_combination huv
    have hMdet : (!![p, p'; q, q'] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
      rw [Matrix.det_fin_two_of]; exact hdet
    set g : SL2 := ⟨!![p, p'; q, q'], hMdet⟩ with hgdef
    have hg00 : (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = p := by simp [hgdef]
    have hg01 : (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = p' := by simp [hgdef]
    have hg10 : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = q := by simp [hgdef]
    have hg11 : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = q' := by simp [hgdef]
    have hU' := hU g
    rw [cuspAct_infty, hg10, hg00, if_neg hq.ne', cuspAct_zero, hg11, hg01] at hU'
    by_cases hq'0 : q' = 0
    · rw [if_pos hq'0] at hU'
      exact hU'
    · rw [if_neg hq'0] at hU'
      have hq'pos : 0 < q' := lt_of_le_of_ne (Int.emod_nonneg u hq.ne') (Ne.symm hq'0)
      have hq'lt : q' < q := Int.emod_lt_of_pos u hq
      have hcop' : IsCoprime p' q' := ⟨-q, p, by linear_combination hdet⟩
      have hrec : φ.val (OnePoint.infty, (((p' : ℚ) / (q' : ℚ)) : Cusp)) = 0 := by
        refine ih q'.toNat (by omega) p' q' hq'pos ?_ hcop'
        omega
      have hsum := hc_add φ OnePoint.infty (((p' : ℚ) / (q' : ℚ)) : Cusp)
        (((p : ℚ) / (q : ℚ)) : Cusp)
      rw [hrec, hU', zero_add] at hsum
      exact hsum.symm

theorem manin (φ : Hc N n ℤ)
    (hU : ∀ g : SL2, φ.val (cuspAct g ((0 : ℚ) : Cusp), cuspAct g OnePoint.infty) = 0)
    (r : ℚ) : φ.val (OnePoint.infty, (r : Cusp)) = 0 := by
  have hcop : IsCoprime r.num (r.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd] using r.reduced
  have h := manin_aux φ hU r.den r.num (r.den : ℤ)
    (by exact_mod_cast r.pos) le_rfl hcop
  have hcast : (((r.den : ℤ) : ℚ)) = (r.den : ℚ) := by push_cast; ring
  rw [hcast, Rat.num_div_den] at h
  exact h

/-- A class killed on all unimodular paths is zero. -/
theorem hc_eq_zero_of_unimodular (φ : Hc N n ℤ)
    (hU : ∀ g : SL2, φ.val (cuspAct g ((0 : ℚ) : Cusp), cuspAct g OnePoint.infty) = 0) :
    φ = 0 := by
  have hinf : ∀ x : Cusp, φ.val (OnePoint.infty, x) = 0 := by
    intro x
    induction x using OnePoint.rec with
    | infty => exact hc_self φ _
    | coe r => exact manin φ hU r
  refine Subtype.ext (funext fun D => ?_)
  have hsum := hc_add φ D.1 OnePoint.infty D.2
  rw [hinf D.2, add_zero] at hsum
  have : φ.val (D.1, OnePoint.infty) = 0 := by
    rw [hc_swap φ OnePoint.infty D.1, hinf D.1, neg_zero]
  rw [this] at hsum
  simpa using hsum.symm

end P2MFG

open MTT.Cohomology

namespace P2MFG

open MvPolynomial

/-- The right-coset space of `Γ₁(N)` in `SL(2,ℤ)`. -/
abbrev Cos (N : ℕ) := Quotient (QuotientGroup.rightRel (CongruenceSubgroup.Gamma1 N))

variable {N n : ℕ}

theorem hc_eq_zero_of_reps (φ : Hc N n ℤ)
    (hR : ∀ q : Cos N,
      φ.val (cuspAct q.out ((0 : ℚ) : Cusp), cuspAct q.out OnePoint.infty) = 0) :
    φ = 0 := by
  refine hc_eq_zero_of_unimodular φ fun g => ?_
  set q : Cos N := Quotient.mk _ g with hqdef
  have hmk : (Quotient.mk (QuotientGroup.rightRel (CongruenceSubgroup.Gamma1 N)) q.out)
      = Quotient.mk _ g := by rw [Quotient.out_eq]
  have hrel : g * (Quotient.out q)⁻¹ ∈ CongruenceSubgroup.Gamma1 N :=
    QuotientGroup.rightRel_apply.mp (Quotient.exact hmk)
  obtain ⟨γ, hγ⟩ : ∃ γ : CongruenceSubgroup.Gamma1 N, g = γ.val * q.out :=
    ⟨⟨g * (q.out)⁻¹, hrel⟩, by simp⟩
  rw [hγ, cuspAct_mul, cuspAct_mul, hc_equiv φ γ, hR q, map_zero]

/-! ### Homogeneous binary forms are determined by their `X^j Y^{n-j}` coefficients -/

/-- The exponent vector of `X^j Y^{n-j}`. -/
def mono (n j : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i : Fin 2 => if i = 0 then j else n - j)

theorem mono_apply (n j : ℕ) (i : Fin 2) : mono n j i = if i = 0 then j else n - j := rfl

theorem hom_eq_zero (P : Binary ℤ) (hP : P ∈ MTT.Cohomology.Sym ℤ n)
    (h : ∀ j : Fin (n + 1), MvPolynomial.coeff (mono n j.val) P = 0) : P = 0 := by
  rw [MvPolynomial.mem_homogeneousSubmodule] at hP
  ext d
  rw [MvPolynomial.coeff_zero]
  by_cases hdeg : d.degree = n
  · have hsum : d 0 + d 1 = n := by
      have hds := Finsupp.degree_eq_sum d
      rw [Fin.sum_univ_two] at hds
      rw [hds] at hdeg
      exact hdeg
    have hd : d = mono n (d 0) := by
      refine Finsupp.ext fun i => ?_
      fin_cases i
      · simp [mono_apply]
      · simp only [mono_apply]
        norm_num
        omega
    have := h ⟨d 0, by omega⟩
    rwa [← hd] at this
  · exact hP.coeff_eq_zero hdeg

/-! ### The finite integral model -/

/-- Evaluation of a class on the unimodular paths attached to coset representatives. -/
def Theta (N n : ℕ) : Hc N n ℤ →ₗ[ℤ] ((Cos N × Fin (n + 1)) → ℤ) where
  toFun φ := fun z => MvPolynomial.coeff (mono n z.2.val)
    (φ.val (cuspAct z.1.out ((0 : ℚ) : Cusp), cuspAct z.1.out OnePoint.infty))
  map_add' φ ψ := by funext z; simp
  map_smul' c φ := by funext z; exact MvPolynomial.coeff_smul _ _ _

theorem Theta_injective : Function.Injective (Theta N n) := by
  rw [injective_iff_map_eq_zero]
  intro φ hφ
  refine hc_eq_zero_of_reps φ fun q => ?_
  refine hom_eq_zero _ (hc_hom φ _ _) fun j => ?_
  exact congrFun hφ (q, j)

end P2MFG


open P2MFG in
theorem solution {N n : ℕ} (hN : 0 < N) : Module.Finite ℤ (Hc N n ℤ) := by
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : Finite (Cos N) :=
    Finite.of_equiv _
      (QuotientGroup.quotientRightRelEquivQuotientLeftRel
        (CongruenceSubgroup.Gamma1 N)).symm
  haveI : Fintype (Cos N) := Fintype.ofFinite _
  exact Module.Finite.of_injective (Theta N n) Theta_injective
