-- Prove2me | solution 1 for HermitekLEAN.hermiteCoeff_finiteHermiteSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:06:24.090677+00:00
-- url     : https://prove2.me/submissions/95b44a35-cc8d-4f48-a9af-7346b376b26d

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Theorems.Thm_HermitekLEAN_qkn_real
public import Theorems.Thm_HermitekLEAN_phi_orthonormal
public import Theorems.Thm_HermitekLEAN_integrable_weightedCross
attribute [local simp] HermitekLEAN.qkn_real
section
@[expose] public section
open Complex MeasureTheory Real Finset
open scoped BigOperators Topology
noncomputable section
namespace HermitekLEAN
private lemma weightedInner_finiteHermiteSum_basis
    (k : ℕ) {D : ℕ} (a : Fin D → ℂ) (n : ℕ) :
    weightedInner (finiteHermiteSum k a) (Phi k n) =
      ∑ m : Fin D, a m * weightedInner (Phi k m.1) (Phi k n) := by
  unfold weightedInner HermiteLEAN.weightedInner
  simp_rw [finiteHermiteSum, Finset.sum_mul, mul_assoc]
  rw [MeasureTheory.integral_finsetSum]
  · change
      (1 / Real.pi : ℂ) *
          ∑ m : Fin D,
            ∫ z : ℂ,
              a m *
                (Phi k m.1 z *
                  ((starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)))
        =
        ∑ m : Fin D,
          a m *
            ((1 / Real.pi : ℂ) *
              ∫ z : ℂ,
                Phi k m.1 z *
                  ((starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)))
    calc
        (1 / Real.pi : ℂ) *
            ∑ m : Fin D,
              ∫ z : ℂ,
                a m *
                  (Phi k m.1 z *
                    ((starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)))
          =
            ∑ m : Fin D,
              (1 / Real.pi : ℂ) *
                ∫ z : ℂ,
                  a m *
                    (Phi k m.1 z *
                      ((starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ))) := by
              simp [Finset.mul_sum]
        _ =
            ∑ m : Fin D,
              a m *
                ((1 / Real.pi : ℂ) *
                  ∫ z : ℂ,
                    Phi k m.1 z *
                      ((starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ))) := by
              refine Finset.sum_congr rfl ?_
              intro m hm
              have hconst :
                  (∫ z : ℂ,
                    a m *
                      (Phi k m.1 z *
                        ((starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)))
                    =
                      a m *
                        ∫ z : ℂ,
                          Phi k m.1 z *
                            ((starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ))) := by
                exact
                  MeasureTheory.integral_const_mul (a m)
                    (fun z : ℂ =>
                      Phi k m.1 z *
                        ((starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)))
              rw [hconst]
              ac_rfl
  · intro m hm
    simpa only [ofReal_exp, ofReal_neg, ofReal_pow, mul_assoc] using
      (integrable_weightedCross k m.1 n).const_mul (a m)
end HermitekLEAN
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators Topology
noncomputable section
open HermitekLEAN
namespace HermitekLEAN
theorem _root_.solution :
    ∀ {k D : ℕ} (a : Fin D → ℂ) (n : ℕ),
      hermiteCoeff k (finiteHermiteSum k a) n = if h : n < D then a ⟨n, h⟩ else 0 := by
  intro k D a n
  unfold hermiteCoeff
  rw [weightedInner_finiteHermiteSum_basis]
  by_cases h : n < D
  · let m : Fin D := ⟨n, h⟩
    have horth :
        ∀ x : Fin D, weightedInner (Phi k x.1) (Phi k n) = if x = m then 1 else 0 := by
      intro x
      rw [phi_orthonormal]
      by_cases hx : x = m
      · subst hx
        simp [m]
      · have hxval : x.1 ≠ n := by
          intro hEq
          exact hx (Fin.ext (by exact hEq))
        simp [hx, hxval, m]
    calc
      ∑ x : Fin D, a x * weightedInner (Phi k x.1) (Phi k n)
        = ∑ x : Fin D, a x * (if x = m then (1 : ℂ) else 0) := by
            simp_all only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ↓reduceIte]
      _ = a m := by simp
      _ = if h' : n < D then a ⟨n, h'⟩ else 0 := by simp [m, h]
  · have horth0 : ∀ x : Fin D, weightedInner (Phi k x.1) (Phi k n) = 0 := by
      intro x
      rw [phi_orthonormal]
      have hxne : x.1 ≠ n := by
        intro hEq
        exact h (hEq ▸ x.isLt)
      simp [hxne]
    simp_all only [not_lt, mul_zero, sum_const_zero, right_eq_dite_iff, isEmpty_Prop,
      IsEmpty.forall_iff]
end HermitekLEAN
