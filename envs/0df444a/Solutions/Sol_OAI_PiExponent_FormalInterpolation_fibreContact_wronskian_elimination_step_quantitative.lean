-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.fibreContact_wronskian_elimination_step_quantitative
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-22T23:25:30.358116+00:00
-- url     : https://prove2.me/submissions/8f9f81ed-f6d5-4dd8-9040-25172e71c86d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_prefix_derivative_detects_full_polynomial_at_transcendental_last_coordinate
import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData
import Mathlib.FieldTheory.IsAlgClosed.Basic

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {n : Nat} (W V : Fin (n + 1) -> Rat)
    (hW : forall i, 0 < (W i : Real)) (hV : forall i, 0 < (V i : Real))
    (E : Type) [Field E] [Algebra Complex E] (x : Fin (n + 1) -> E)
    (hlast : forall a : Complex, x (Fin.last n) ≠ algebraMap Complex E a)
    (B : Real)
    (hprefix : forall T : Nat, 0 < T ->
      forall U : MvPolynomial (Fin n) Complex, U ≠ 0 ->
        fibreContactSupportBound (fun i => W i.castSucc) T U ->
        exists word : List (Fin n),
          fibreContactWordCost (fun i => V i.castSucc) word <= B * (T : Real) /\
          MvPolynomial.aeval (fun i => x i.castSucc) (fibreContactWord word U) ≠ 0)
    (N : Nat) (hN : 0 < N)
    (F : MvPolynomial (Fin (n + 1)) Complex) (hF : F ≠ 0)
    (hbound : fibreContactSupportBound W N F) :
    exists word : List (Fin (n + 1)),
      fibreContactWordCost V word <=
        (B + (∑ i : Fin n, (V i.castSucc : Real)) /
          (W (Fin.last n) : Real)) * (N : Real) /\
      MvPolynomial.aeval x (fibreContactWord word F) ≠ 0 := by
  obtain ⟨word, _hword, hcost, hdetect⟩ :=
    OAI.PiExponent.FormalInterpolation.prefix_derivative_detects_full_polynomial_at_transcendental_last_coordinate
      W V hW hV E x hlast B hprefix N hN F hF hbound
  refine ⟨word, ?_, hdetect⟩
  have hsum : 0 <= ∑ i : Fin n, (V i.castSucc : Real) :=
    Finset.sum_nonneg fun i _ => le_of_lt (hV i.castSucc)
  have hlastW : 0 < (W (Fin.last n) : Real) := hW (Fin.last n)
  have hNR : 0 < (N : Real) := Nat.cast_pos.mpr hN
  have hterm : 0 <=
      ((∑ i : Fin n, (V i.castSucc : Real)) / (W (Fin.last n) : Real)) *
        (N : Real) :=
    mul_nonneg (div_nonneg hsum (le_of_lt hlastW)) (le_of_lt hNR)
  calc
    fibreContactWordCost V word <= B * (N : Real) := hcost
    _ <= (B + (∑ i : Fin n, (V i.castSucc : Real)) /
        (W (Fin.last n) : Real)) * (N : Real) := by nlinarith