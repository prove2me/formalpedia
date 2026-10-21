-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.finite_box_series_jet_interpolation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T05:35:05.223059+00:00
-- url     : https://prove2.me/submissions/771a31ed-f0c3-47d5-832c-2d843033b5b4

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Data.Finset.Lattice.Fold
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_single_center_series_jet_interpolation
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_finite_center_series_jet_patching

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {iota alpha : Type} [Fintype alpha] [DecidableEq alpha] {m : Nat}
    (center : iota -> Fin m -> Complex) (slot : alpha -> iota)
    (degree : alpha -> Fin (m + 1) -> Nat)
    (hcenters : (i j : iota) -> Not (i = j) -> Exists fun k => Not (center i k = center j k))
    (S : iota -> MvPowerSeries (Fin (m + 1)) Complex) :
    Exists fun P : MvPolynomial (Fin (m + 1)) Complex =>
      (b : alpha) -> (e : Fin (m + 1) -> Nat) ->
        ((k : Fin (m + 1)) -> LE.le (e k) (degree b k)) ->
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (formalJet (center (slot b)) P) =
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (S (slot b)) := by
  classical
  let D : (Fin (m + 1) -> Nat) := fun k => Finset.univ.sup (fun b : alpha => degree b k)
  have hD : forall (b : alpha) (k : Fin (m + 1)), degree b k <= D k := by
    intro b k
    exact Finset.le_sup (s := (Finset.univ : Finset alpha))
      (f := fun a : alpha => degree a k) (Finset.mem_univ b)
  let active : Finset iota := Finset.univ.image slot
  have hlocal : forall i, i ∈ active ->
      Exists fun q : MvPolynomial (Fin (m + 1)) Complex =>
        (e : Fin (m + 1) -> Nat) ->
          ((k : Fin (m + 1)) -> e k <= D k) ->
          MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
            (formalJet (center i) q) =
          MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) (S i) := by
    intro i hi
    exact OAI.PiExponent.LogarithmicJetIdeals.single_center_series_jet_interpolation
      (center i) D (S i)
  let Q : iota -> MvPolynomial (Fin (m + 1)) Complex := fun i =>
    if hi : i ∈ active then Classical.choose (hlocal i hi) else 0
  have hQ : forall i, i ∈ active ->
      (e : Fin (m + 1) -> Nat) ->
        ((k : Fin (m + 1)) -> e k <= D k) ->
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (formalJet (center i) (Q i)) =
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) (S i) := by
    intro i hi e he
    simpa [Q, hi] using (Classical.choose_spec (hlocal i hi) e he)
  obtain ⟨P, hP⟩ :=
    OAI.PiExponent.LogarithmicJetIdeals.finite_center_series_jet_patching
      active center D hcenters S Q hQ
  refine ⟨P, ?_⟩
  intro b e he
  have hslot : slot b ∈ active := by
    exact Finset.mem_image.mpr ⟨b, Finset.mem_univ b, rfl⟩
  apply hP (slot b) hslot e
  intro k
  exact le_trans (he k) (hD b k)