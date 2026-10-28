-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_logarithmic_component_normal_basis_factorial_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T20:50:07.192073+00:00
-- url     : https://prove2.me/submissions/6499b436-110f-4134-acfb-e633e801e073
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_coordinate_component_local_length_upper_from_multiplicity
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmic_transverse_simplex_card_le_component_local_length_from_multiplicity
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_strict_weighted_simplex_volume_lower_from_multiplicity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (w v : Fin (m + 1) → Rat) (sigma : Rat)
    (hsigma : 0 < (sigma : Real))
    (hw : ∀ i, 0 < (w i : Real)) (hv : ∀ i, 0 < (v i : Real))
    (N : Nat) (hN : 0 < N)
    (S : Finset (MvPolynomial (Fin (m + 1)) Complex))
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]
    (hP : P ≠ ⊥) (hY : MvPolynomial.X (0 : Fin (m + 1)) ∉ P)
    (hminimal :
      (Ideal.span (↑S : Set (MvPolynomial (Fin (m + 1)) Complex))).IsMinimalPrime P)
    (hdegree : ∀ f ∈ S, logarithmicDegreeBound w (N : Real) f)
    (hwords : ∀ f ∈ S, ∀ word : List (Fin (m + 1)),
      logarithmicFrameCost v word <
        ((sigma : Real) / ((m : Real) + 2)) * (N : Real) →
      logarithmicFrameWord word f ∈ P) :
    ∀ A B : Finset (Fin (m + 1)), A.card = B.card →
      coordinateNormalBasisAtPrime P A →
      logarithmicNormalBasisAtPrime P B →
      (∏ i ∈ A, (w i : Real)) ≤
        (2 * (A.card.factorial : Real) *
          (((m : Real) + 2) / (sigma : Real)) ^ A.card) *
          (∏ i ∈ B, (v i : Real)) := by
  classical
  intro A B hcard hA hB
  have hNR : 0 < (N : Real) := by exact_mod_cast hN
  have hm : 0 < (m : Real) + 2 := by positivity
  let T : Real := ((sigma : Real) / ((m : Real) + 2)) * (N : Real)
  let c : Real := ((m : Real) + 2) / (sigma : Real)
  let W : Real := ∏ i ∈ A, (w i : Real)
  let V : Real := ∏ i ∈ B, (v i : Real)
  let F : Real := (A.card.factorial : Real)
  have hT : 0 < T := mul_pos (div_pos hsigma hm) hNR
  have hc : 0 < c := div_pos hm hsigma
  have hW : 0 ≤ W := by
    dsimp [W]
    exact Finset.prod_nonneg (fun i _ => (hw i).le)
  have hV : 0 ≤ V := by
    dsimp [V]
    exact Finset.prod_nonneg (fun i _ => (hv i).le)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hFV : 0 ≤ F * V := mul_nonneg hF hV
  obtain ⟨L, hlength, hupper⟩ :=
    weighted_coordinate_component_local_length_upper_from_multiplicity
      w hw (N : Real) hNR S P hminimal hdegree A hA
  change (L : Real) * W ≤ 2 * (N : Real) ^ A.card at hupper
  have hcount :=
    logarithmic_transverse_simplex_card_le_component_local_length_from_multiplicity
      v hv T hT S P hY B hB.1 hwords
  rw [hlength] at hcount
  have hcountNat : strictWeightedSimplexCard (fun i : B => v i) T ≤ L :=
    ENat.natCast_le_natCast.mp hcount
  have hcountReal :
      (strictWeightedSimplexCard (fun i : B => v i) T : Real) ≤ (L : Real) := by
    exact_mod_cast hcountNat
  have hvolume :=
    (strict_weighted_simplex_volume_lower_from_multiplicity
      (fun i : B => v i) (fun i => hv i) T hT).2
  have hprod : (∏ i : B, (v i : Real)) = ∏ i ∈ B, (v i : Real) := by
    classical
    simpa using (Finset.prod_attach B (fun i : Fin (m + 1) => (v i : Real)))
  have hvolume' : T ^ A.card ≤
      (F * V) * (strictWeightedSimplexCard (fun i : B => v i) T : Real) := by
    have hvolume₁ := hvolume
    rw [Fintype.card_coe, ← hcard] at hvolume₁
    rw [hprod] at hvolume₁
    simpa only [F, V] using hvolume₁
  have hlower : T ^ A.card ≤ (F * V) * (L : Real) :=
    hvolume'.trans (mul_le_mul_of_nonneg_left hcountReal hFV)
  have hcombined : T ^ A.card * W ≤ (F * V) * (2 * (N : Real) ^ A.card) := by
    calc
      T ^ A.card * W ≤ ((F * V) * (L : Real)) * W :=
        mul_le_mul_of_nonneg_right hlower hW
      _ = (F * V) * ((L : Real) * W) := by ring
      _ ≤ (F * V) * (2 * (N : Real) ^ A.card) :=
        mul_le_mul_of_nonneg_left hupper hFV
  have hcT : c * T = (N : Real) := by
    dsimp [c, T]
    field_simp [hsigma.ne', hm.ne'] <;> ring
  have hpowers : c ^ A.card * T ^ A.card = (N : Real) ^ A.card := by
    rw [← mul_pow, hcT]
  have hscaled : (N : Real) ^ A.card * W ≤
      (N : Real) ^ A.card * ((2 * F * c ^ A.card) * V) := by
    calc
      (N : Real) ^ A.card * W = c ^ A.card * (T ^ A.card * W) := by
        rw [← hpowers]
        ring
      _ ≤ c ^ A.card * ((F * V) * (2 * (N : Real) ^ A.card)) :=
        mul_le_mul_of_nonneg_left hcombined (pow_nonneg hc.le _)
      _ = (N : Real) ^ A.card * ((2 * F * c ^ A.card) * V) := by ring
  have hresult : W ≤ (2 * F * c ^ A.card) * V :=
    (mul_le_mul_iff_right₀ (pow_pos hNR A.card)).mp hscaled
  exact hresult
