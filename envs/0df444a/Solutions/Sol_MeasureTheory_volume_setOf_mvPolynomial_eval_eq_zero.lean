-- Prove2me | solution 1 for MeasureTheory.volume_setOf_mvPolynomial_eval_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/e2d3d32f-db1f-5349-8690-33cf8dd267d8

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_volume_setOf_mvPolynomial_eval_eq_zero

set_option autoImplicit false

open MeasureTheory

namespace NullsetMvPolynomialSol

open MvPolynomial

theorem measurableSet_zeroSet {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    MeasurableSet {x : Fin n → ℝ | MvPolynomial.eval x p = 0} :=
  (isClosed_eq (MvPolynomial.continuous_eval p) continuous_const).measurableSet

theorem volume_setOf_polynomial_eval_eq_zero (P : Polynomial ℝ) (hP : P ≠ 0) :
    volume {a : ℝ | Polynomial.eval a P = 0} = 0 :=
  (Polynomial.finite_setOf_isRoot hP).measure_zero volume

theorem main : ∀ (n : ℕ) (p : MvPolynomial (Fin n) ℝ), p ≠ 0 →
    volume {x : Fin n → ℝ | MvPolynomial.eval x p = 0} = 0
  | 0, p, hp => by
    have hset : {x : Fin 0 → ℝ | MvPolynomial.eval x p = 0} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rw [p.eq_C_of_isEmpty] at hp ⊢
      simpa [C_ne_zero] using hp
    rw [hset, measure_empty]
  | n + 1, p, hp => by

    set P : Polynomial (MvPolynomial (Fin n) ℝ) := finSuccEquiv ℝ n p with hPdef
    have hP0 : P ≠ 0 := EmbeddingLike.map_ne_zero_iff.2 hp
    set q : MvPolynomial (Fin n) ℝ := P.leadingCoeff with hqdef
    have hq0 : q ≠ 0 := by simpa [q] using hP0

    have ih : volume {y : Fin n → ℝ | MvPolynomial.eval y q = 0} = 0 := main n q hq0

    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    have he : MeasurePreserving e volume volume :=
      volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    set S : Set (Fin (n + 1) → ℝ) := {x | MvPolynomial.eval x p = 0} with hSdef
    have hS : MeasurableSet S := measurableSet_zeroSet p
    set T : Set (ℝ × (Fin n → ℝ)) := e.symm ⁻¹' S with hTdef
    have hT : MeasurableSet T := hS.preimage e.symm.measurable
    have hST : S = e ⁻¹' T := by
      ext x
      simp [T, Set.mem_preimage, e.symm_apply_apply]
    have hsymm : ∀ (a : ℝ) (y : Fin n → ℝ), e.symm (a, y) = Fin.cons a y := by
      intro a y
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.insertNth_zero']
    rw [hST, he.measure_preimage hT.nullMeasurableSet, Measure.volume_eq_prod,
      Measure.prod_apply_symm hT]

    have hae : (fun y : Fin n → ℝ => volume ((fun a : ℝ => (a, y)) ⁻¹' T)) =ᵐ[volume]
        fun _ => 0 := by
      have hq_ae : ∀ᵐ y : Fin n → ℝ ∂volume, y ∉ {y : Fin n → ℝ | MvPolynomial.eval y q = 0} :=
        measure_eq_zero_iff_ae_notMem.1 ih
      filter_upwards [hq_ae] with y hy
      replace hy : ¬ MvPolynomial.eval y q = 0 := hy

      set Q : Polynomial ℝ := Polynomial.map (MvPolynomial.eval y) P with hQdef
      have hQ0 : Q ≠ 0 := by
        intro hQ
        apply hy
        have h1 : Q.coeff P.natDegree = MvPolynomial.eval y q := by
          rw [hQdef, Polynomial.coeff_map, Polynomial.coeff_natDegree]
        rw [← h1, hQ, Polynomial.coeff_zero]
      have hslice : (fun a : ℝ => (a, y)) ⁻¹' T = {a : ℝ | Polynomial.eval a Q = 0} := by
        ext a
        simp only [Set.mem_preimage, T, S, Set.mem_setOf_eq, hsymm a y]
        rw [MvPolynomial.eval_eq_eval_mv_eval']
      rw [hslice]
      exact volume_setOf_polynomial_eval_eq_zero Q hQ0
    rw [lintegral_congr_ae hae, lintegral_zero]

end NullsetMvPolynomialSol

theorem solution
    {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (hp : p ≠ 0) :
    volume {x : Fin n → ℝ | MvPolynomial.eval x p = 0} = 0 :=
  NullsetMvPolynomialSol.main n p hp

end S_MeasureTheory_volume_setOf_mvPolynomial_eval_eq_zero
end P2MW
export P2MW.S_MeasureTheory_volume_setOf_mvPolynomial_eval_eq_zero (solution)
