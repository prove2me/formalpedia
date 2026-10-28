-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.fibreContact_divisor_vanishing_of_posWeights
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T09:00:25.736883+00:00
-- url     : https://prove2.me/submissions/d0cf4be5-88f1-43b1-89d9-188402e75849

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomialCurve_principal_divisor_balance
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomialCurve_weighted_polynomial_pole_le
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (E : Type) [Field E] [Algebra Complex E]
    [Algebra.EssFiniteType Complex E]
    (htrdeg : Algebra.trdeg Complex E = 1)
    (x : Fin (m + 1) → E)
    (hgen : IntermediateField.adjoin Complex (Set.range x) = ⊤)
    (w : Fin (m + 1) → Rat)
    (hw : ∀ i, 0 < (w i : Real))
    (R sigma : Rat)
    (hR : 0 < R) (hsigma : 0 < (sigma : Real))
    (N : Nat) (hN : 0 < N)
    (P : MvPolynomial (Fin m) Complex)
    (hP : fibreContactSupportBound (fun i => w i.succ) N P)
    (I : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (hexcess :
      (R : Real) / (1 + (sigma : Real)) *
        (∑ᶠ nu : PolynomialCurvePlace E, polynomialCurvePole nu x w) <
      (∑ᶠ nu : PolynomialCurvePlace E,
        (polynomialCurveIdealContact nu x I : Real)))
    (hlocal : MvPolynomial.aeval (fun i => x i.succ) P ≠ 0 →
      ∀ nu : PolynomialCurvePlace E,
        ((polynomialCurveIdealContact nu x I : Real) *
          ((1 + 2 * (sigma : Real)) * (N : Real))) ≤
          (R : Real) * max 0
            (polynomialCurveOrder nu
              (MvPolynomial.aeval (fun i => x i.succ) P) : Real)) :
    MvPolynomial.aeval (fun i => x i.succ) P = 0 := by
  classical
  by_contra hne
  let f : E := MvPolynomial.aeval (fun i => x i.succ) P
  let posOrd : PolynomialCurvePlace E → Real :=
    fun nu => max 0 (polynomialCurveOrder nu f : Real)
  let negOrd : PolynomialCurvePlace E → Real :=
    fun nu => max 0 (-(polynomialCurveOrder nu f : Real))
  let pole : PolynomialCurvePlace E → Real :=
    fun nu => polynomialCurvePole nu x w
  let contact : PolynomialCurvePlace E → Real :=
    fun nu => (polynomialCurveIdealContact nu x I : Real)
  -- A transcendental parameter is a transcendence basis in dimension one.
  -- Essential finite type then upgrades algebraicity to a finite extension.
  have hfinite : ∀ g : E, Transcendental Complex g →
      FiniteDimensional (IntermediateField.adjoin Complex {g}) E := by
    intro g hg
    have hind : AlgebraicIndependent Complex
        (fun z : ({g} : Set E) => (z : E)) := by
      rw [algebraicIndependent_singleton_iff ⟨g, rfl⟩]
      exact hg
    have hb := hind.isTranscendenceBasis_of_trdeg_le_of_finite
      (by simpa using htrdeg.le)
    have hrange : Set.range (fun z : ({g} : Set E) => (z : E)) = {g} :=
      Subtype.range_coe
    letI : Algebra.IsAlgebraic (IntermediateField.adjoin Complex {g}) E := by
      have ha := hb.isAlgebraic_field
      rw [hrange] at ha
      exact ha
    letI : Algebra.EssFiniteType (IntermediateField.adjoin Complex {g}) E :=
      Algebra.EssFiniteType.of_comp Complex (IntermediateField.adjoin Complex {g}) E
    exact Algebra.finite_of_essFiniteType_of_isAlgebraic
  obtain ⟨hord, hbalance⟩ :=
    polynomialCurve_principal_divisor_balance E hfinite f
  have hpos : posOrd.HasFiniteSupport :=
    hord.fun_comp (g := fun a : Real => max 0 a) (by simp)
  have hneg : negOrd.HasFiniteSupport :=
    hord.fun_comp (g := fun a : Real => max 0 (-a)) (by simp)
  have hbalance' : (∑ᶠ nu, posOrd nu) = (∑ᶠ nu, negOrd nu) :=
    hbalance

  -- Each coordinate has a finite divisor, so the finite maximum of
  -- coordinate pole contributions also has finite support.
  have hterm (i : Option (Fin (m + 1))) :
      (fun nu : PolynomialCurvePlace E =>
        i.elim (0 : Real) (fun j =>
          -(polynomialCurveOrder nu (x j) : Real) / (w j : Real))).HasFiniteSupport := by
    cases i with
    | none =>
        change (fun _ : PolynomialCurvePlace E => (0 : Real)).HasFiniteSupport
        exact Function.hasFiniteSupport_zero
    | some j =>
        exact (polynomialCurve_principal_divisor_balance E hfinite (x j)).1.fun_comp
          (g := fun a : Real => -a / (w j : Real)) (by simp)
  have hpole : pole.HasFiniteSupport := by
    dsimp only [pole, polynomialCurvePole]
    exact Function.HasFiniteSupport.sup' Finset.univ (fun i _ => hterm i) (by simp)
  have hpole0 (nu : PolynomialCurvePlace E) : 0 ≤ pole nu := by
    dsimp only [pole, polynomialCurvePole]
    exact Finset.le_sup'
      (fun i : Option (Fin (m + 1)) => i.elim (0 : Real) (fun j =>
        -(polynomialCurveOrder nu (x j) : Real) / (w j : Real)))
      (Finset.mem_univ (none : Option (Fin (m + 1))))

  -- Omitting the zeroth coordinate can only decrease the pole allowance.
  have hpole_succ (nu : PolynomialCurvePlace E) :
      polynomialCurvePole nu (fun i : Fin m => x i.succ)
        (fun i => w i.succ) ≤ pole nu := by
    dsimp only [pole, polynomialCurvePole]
    refine Finset.sup'_le _ _ ?_
    intro i hi
    cases i with
    | none =>
        exact Finset.le_sup'
          (fun i : Option (Fin (m + 1)) => i.elim (0 : Real) (fun j =>
            -(polynomialCurveOrder nu (x j) : Real) / (w j : Real)))
          (Finset.mem_univ (none : Option (Fin (m + 1))))
    | some j =>
        exact Finset.le_sup'
          (fun i : Option (Fin (m + 1)) => i.elim (0 : Real) (fun k =>
            -(polynomialCurveOrder nu (x k) : Real) / (w k : Real)))
          (Finset.mem_univ (some j.succ : Option (Fin (m + 1))))
  have hpoint (nu : PolynomialCurvePlace E) :
      negOrd nu ≤ (N : Real) * pole nu := by
    exact (polynomialCurve_weighted_polynomial_pole_le nu
      (fun i => x i.succ) (fun i => w i.succ)
      (fun i => hw i.succ) N P hP).trans
        (mul_le_mul_of_nonneg_left (hpole_succ nu) (Nat.cast_nonneg N))
  have hdivisor :
      (∑ᶠ nu, posOrd nu) ≤ (N : Real) * (∑ᶠ nu, pole nu) := by
    rw [hbalance']
    calc
      (∑ᶠ nu, negOrd nu) ≤ ∑ᶠ nu, (N : Real) * pole nu :=
        finsum_le_finsum' hneg
          (hpole.fun_comp (g := fun a : Real => (N : Real) * a) (by simp)) hpoint
      _ = (N : Real) * (∑ᶠ nu, pole nu) := (mul_finsum pole (N : Real)).symm

  let B : Real := ∑ᶠ nu, pole nu
  let T : Real := ∑ᶠ nu, contact nu
  have hRreal : 0 < (R : Real) := Rat.cast_pos.mpr hR
  have hNreal : 0 < (N : Real) := Nat.cast_pos.mpr hN
  have hden : 0 < 1 + (sigma : Real) := by linarith
  have hB : 0 ≤ B := finsum_nonneg hpole0
  have hex : (R : Real) / (1 + (sigma : Real)) * B < T := hexcess
  have hT : 0 < T :=
    lt_of_le_of_lt (mul_nonneg (div_nonneg hRreal.le hden.le) hB) hex
  -- A positive finsum cannot have infinite support under the finsum convention.
  have hcontact : contact.HasFiniteSupport :=
    hasFiniteSupport_of_finsum_ne_zero (show (∑ᶠ nu, contact nu) ≠ 0 from hT.ne')
  have hsum :
      T * ((1 + 2 * (sigma : Real)) * (N : Real)) ≤
        (R : Real) * (∑ᶠ nu, posOrd nu) := by
    change (∑ᶠ nu, contact nu) * ((1 + 2 * (sigma : Real)) * (N : Real)) ≤
      (R : Real) * (∑ᶠ nu, posOrd nu)
    rw [finsum_mul, mul_finsum]
    exact finsum_le_finsum'
      (hcontact.fun_comp
        (g := fun a : Real => a * ((1 + 2 * (sigma : Real)) * (N : Real))) (by simp))
      (hpos.fun_comp (g := fun a : Real => (R : Real) * a) (by simp))
      (hlocal hne)
  have hupper :
      T * ((1 + 2 * (sigma : Real)) * (N : Real)) ≤
        (R : Real) * ((N : Real) * B) :=
    hsum.trans (mul_le_mul_of_nonneg_left hdivisor hRreal.le)
  have hfirst : (R : Real) * B < T * (1 + (sigma : Real)) := by
    apply (div_lt_iff₀ hden).mp
    simpa only [div_mul_eq_mul_div] using hex
  have hgap : (R : Real) * B < T * (1 + 2 * (sigma : Real)) :=
    hfirst.trans_le
      (mul_le_mul_of_nonneg_left (by linarith : 1 + (sigma : Real) ≤
        1 + 2 * (sigma : Real)) hT.le)
  have hgapN := mul_lt_mul_of_pos_right hgap hNreal
  have hupper' :
      T * (1 + 2 * (sigma : Real)) * (N : Real) ≤
        (R : Real) * B * (N : Real) := by
    calc
      T * (1 + 2 * (sigma : Real)) * (N : Real) =
          T * ((1 + 2 * (sigma : Real)) * (N : Real)) := by ring
      _ ≤ (R : Real) * ((N : Real) * B) := hupper
      _ = (R : Real) * B * (N : Real) := by ring
  exact (not_lt_of_ge hupper') hgapN
