-- Prove2me | solution 1 for Kyprianou.Ch01.mckeanValueSmoothFit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:50:54.346556+00:00
-- url     : https://prove2.me/submissions/40bffbf9-53f6-4577-9ab8-a657d49c4395

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01 MeasureTheory ProbabilityTheory Set
set_option autoImplicit false

/-- The left and right derivatives of the McKean put value coincide at the optimal barrier. -/
private theorem mckeanSmoothFitAux
    (K phi : ℝ) (hK : 0 < K) (hphi : 0 < phi) :
    let b := Real.log (K * phi / (1 + phi))
    HasDerivAt (mckeanValue K b phi) (-Real.exp b) b := by
  dsimp
  let b : ℝ := Real.log (K * phi / (1 + phi))
  change HasDerivAt (mckeanValue K b phi) (-Real.exp b) b
  have hden : 0 < 1 + phi := by linarith
  have harg : 0 < K * phi / (1 + phi) :=
    div_pos (mul_pos hK hphi) hden
  have hexp : Real.exp b = K * phi / (1 + phi) :=
    Real.exp_log harg
  have hprod : (K - Real.exp b) * phi = Real.exp b := by
    rw [hexp]
    field_simp [ne_of_gt hden]
    ring
  have hfleft : HasDerivAt (fun x : ℝ => K - Real.exp x)
      (-Real.exp b) b := by
    simpa using (Real.hasDerivAt_exp b).const_sub K
  have hinner : HasDerivAt (fun x : ℝ => -phi * (x - b))
      (-phi) b := by
    have hh := ((hasDerivAt_id b).sub_const b).const_mul (-phi)
    simpa only [id_eq, mul_one] using hh
  have hright : HasDerivAt
      (fun x : ℝ => (K - Real.exp b) * Real.exp (-phi * (x - b)))
      (-Real.exp b) b := by
    have hh : HasDerivAt
        (fun x : ℝ => Real.exp (-phi * (x - b)))
        (Real.exp (-phi * (b - b)) * (-phi)) b := by
      simpa only [Function.comp_def] using
        (Real.hasDerivAt_exp (-phi * (b - b))).comp b hinner
    have hderiv : HasDerivAt
        (fun x : ℝ => Real.exp (-phi * (x - b))) (-phi) b := by
      simpa only [sub_self, mul_zero, neg_zero, Real.exp_zero, one_mul] using hh
    have hc := hderiv.const_mul (K - Real.exp b)
    have hco : (K - Real.exp b) * (-phi) = -Real.exp b := by
      nlinarith [hprod]
    simpa [hco] using hc
  have hleft_eq (x : ℝ) (hx : x ∈ Set.Iic b) :
      mckeanValue K b phi x = K - Real.exp x := by
    change x ≤ b at hx
    by_cases h : x < b
    · simp [mckeanValue, h]
    · have heq : x = b := le_antisymm hx (le_of_not_gt h)
      subst x
      simp [mckeanValue, Real.exp_zero]
  have hright_eq (x : ℝ) (hx : x ∈ Set.Ici b) :
      mckeanValue K b phi x =
        (K - Real.exp b) * Real.exp (-phi * (x - b)) := by
    change b ≤ x at hx
    simp [mckeanValue, not_lt.mpr hx]
  have hleft : HasDerivWithinAt (mckeanValue K b phi)
      (-Real.exp b) (Set.Iic b) b :=
    hfleft.hasDerivWithinAt.congr_of_mem hleft_eq (le_refl b)
  have hrightW : HasDerivWithinAt (mckeanValue K b phi)
      (-Real.exp b) (Set.Ici b) b :=
    hright.hasDerivWithinAt.congr_of_mem hright_eq (le_refl b)
  have hcover : Set.Iic b ∪ Set.Ici b = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici,
      Set.mem_univ, iff_true]
    exact le_total x b
  have h := hleft.union hrightW
  rw [hcover] at h
  exact hasDerivWithinAt_univ.mp h


theorem solution
    (K phi : ℝ) (hK : 0 < K) (hphi : 0 < phi) :
    let b := Real.log (K * phi / (1 + phi))
    HasDerivAt (mckeanValue K b phi) (-Real.exp b) b := by
  exact mckeanSmoothFitAux K phi hK hphi
