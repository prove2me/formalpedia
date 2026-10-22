-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.constant_fibre_contact_localization_matched_finsum
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T06:41:53.427836+00:00
-- url     : https://prove2.me/submissions/92e88f11-3779-4f2e-8417-9332444eb6fa

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomialCurveOrder_support_finite
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Tactic

open scoped BigOperators
open Function
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (T : Fin m → Nat) (e : Fin (m + 1) → Nat)
    (E : Type) [Field E] [Algebra Complex E] [Algebra.EssFiniteType Complex E]
    (htrdeg : Algebra.trdeg Complex E = 1) (x : Fin (m + 1) → E)
    (hgen : IntermediateField.adjoin Complex (Set.range x) = ⊤)
    (hfibre : x 0 = 1)
    (i0 : Fin m) (a : Complex) (ha : x i0.succ = algebraMap Complex E a)
    (k : Fin m) (hk : Transcendental Complex (x k.succ))
    (j : Fin K) (hj : c j i0 = a)
    (hlocal : ∀ nu : PolynomialCurvePlace E,
      (polynomialCurveIdealContact nu x (logarithmicCentersIdeal c T e) : Real) ≤
        (e k.succ : Real) *
          max (polynomialCurveOrder nu
            (x k.succ - algebraMap Complex E (c j k)) : Real) 0) :
    (∑ᶠ nu : PolynomialCurvePlace E,
      (polynomialCurveIdealContact nu x (logarithmicCentersIdeal c T e) : Real)) ≤
      (e k.succ : Real) *
        ∑ᶠ nu : PolynomialCurvePlace E,
          max (polynomialCurveOrder nu
            (x k.succ - algebraMap Complex E (c j k)) : Real) 0 := by
  classical
  set I := logarithmicCentersIdeal c T e
  set diff : E := x k.succ - algebraMap Complex E (c j k)
  set f : PolynomialCurvePlace E → ℝ :=
    fun nu => (polynomialCurveIdealContact nu x I : ℝ)
  set g : PolynomialCurvePlace E → ℝ :=
    fun nu => max (polynomialCurveOrder nu diff : ℝ) 0
  have hfg : ∀ nu, f nu ≤ (e k.succ : ℝ) * g nu := fun nu => by
    simpa [f, g, I, diff] using hlocal nu
  have hg : HasFiniteSupport g := by
    change (support g).Finite
    refine (polynomialCurveOrder_support_finite (E := E) htrdeg diff).subset ?_
    intro nu hnu
    simp only [mem_support, ne_eq, g, Set.mem_setOf_eq] at hnu ⊢
    intro hord0
    apply hnu
    have : (polynomialCurveOrder nu diff : ℝ) = 0 := by exact_mod_cast hord0
    simp [this]
  have heg : HasFiniteSupport (fun nu => (e k.succ : ℝ) * g nu) := by
    change (support fun nu => (e k.succ : ℝ) * g nu).Finite
    refine hg.subset ?_
    intro nu hnu
    simp only [mem_support, ne_eq] at hnu ⊢
    intro hg0
    simp [hg0] at hnu
  have hf : HasFiniteSupport f := by
    change (support f).Finite
    refine heg.subset ?_
    intro nu hnu
    simp only [mem_support, ne_eq] at hnu ⊢
    intro hz
    have hle0 : f nu ≤ 0 := by
      have := hfg nu
      simpa [hz] using this
    exact hnu (le_antisymm hle0 (Nat.cast_nonneg _))
  have hle : ∑ᶠ nu, f nu ≤ ∑ᶠ nu, (e k.succ : ℝ) * g nu :=
    finsum_le_finsum' hf heg fun nu => hfg nu
  calc
    ∑ᶠ nu, f nu ≤ ∑ᶠ nu, (e k.succ : ℝ) * g nu := hle
    _ = (e k.succ : ℝ) * ∑ᶠ nu, g nu := by
        simpa [smul_eq_mul] using (smul_finsum' (e k.succ : ℝ) hg).symm
