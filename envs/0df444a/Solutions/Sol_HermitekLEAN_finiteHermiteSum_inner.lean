-- Prove2me | solution 1 for HermitekLEAN.finiteHermiteSum_inner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:04:09.430874+00:00
-- url     : https://prove2.me/submissions/42f7ec32-dea9-4a4c-9400-f30bfb72bd6b

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
private lemma integrable_finiteHermiteSum_weightedCross
    (k : ℕ) {D n : ℕ} (a : Fin D → ℂ) :
    Integrable (fun z : ℂ =>
      finiteHermiteSum k a z * (starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
  unfold finiteHermiteSum
  have hEq :
      (fun z : ℂ =>
        (∑ m : Fin D, a m * Phi k m.1 z) * (starRingEnd ℂ) (Phi k n z) *
          (Real.exp (-‖z‖ ^ 2) : ℂ))
        =
      fun z : ℂ =>
        ∑ m : Fin D, a m * (Phi k m.1 z * (starRingEnd ℂ) (Phi k n z) *
          (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
    funext z
    calc
      (∑ m : Fin D, a m * Phi k m.1 z) * (starRingEnd ℂ) (Phi k n z) *
          (Real.exp (-‖z‖ ^ 2) : ℂ)
        = ∑ m : Fin D,
            (a m * Phi k m.1 z) *
              ((starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
              rw [mul_assoc, ← Finset.sum_mul]
      _ = ∑ m : Fin D,
          a m * (Phi k m.1 z * (starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
            refine Finset.sum_congr rfl ?_
            intro m hm
            ac_rfl
  rw [hEq]
  refine MeasureTheory.integrable_finsetSum (Finset.univ : Finset (Fin D)) ?_
  intro m hm
  exact
    (integrable_weightedCross k m.1 n).const_mul (a m)
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
private lemma weightedInner_finiteHermiteSum
    (k : ℕ) {D : ℕ} (a b : Fin D → ℂ) :
    weightedInner (finiteHermiteSum k a) (finiteHermiteSum k b) =
      ∑ m : Fin D, (starRingEnd ℂ) (b m) *
        weightedInner (finiteHermiteSum k a) (Phi k m.1) := by
  unfold weightedInner HermiteLEAN.weightedInner
  have hfun :
      (fun z : ℂ =>
        finiteHermiteSum k a z *
          (starRingEnd ℂ) (finiteHermiteSum k b z) *
            (Real.exp (-‖z‖ ^ 2) : ℂ))
        =
      fun z : ℂ =>
        ∑ m : Fin D,
          (starRingEnd ℂ) (b m) *
            (finiteHermiteSum k a z *
              ((starRingEnd ℂ) (Phi k m.1 z) * (Real.exp (-‖z‖ ^ 2) : ℂ))) := by
    funext z
    rw [finiteHermiteSum, finiteHermiteSum, map_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    simp [mul_assoc, mul_left_comm, mul_comm]
  rw [hfun, MeasureTheory.integral_finsetSum]
  · calc
      (1 / Real.pi : ℂ) *
          ∑ m : Fin D,
            ∫ z : ℂ,
              (starRingEnd ℂ) (b m) *
                (finiteHermiteSum k a z *
                  ((starRingEnd ℂ) (Phi k m.1 z) * (Real.exp (-‖z‖ ^ 2) : ℂ)))
        =
          (1 / Real.pi : ℂ) *
            ∑ m : Fin D,
              (starRingEnd ℂ) (b m) *
                ∫ z : ℂ,
                  finiteHermiteSum k a z *
                    ((starRingEnd ℂ) (Phi k m.1 z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
              congr 1
              refine Finset.sum_congr rfl (fun m _ => ?_)
              exact
                MeasureTheory.integral_const_mul ((starRingEnd ℂ) (b m))
                  (fun z : ℂ =>
                    finiteHermiteSum k a z *
                      ((starRingEnd ℂ) (Phi k m.1 z) * (Real.exp (-‖z‖ ^ 2) : ℂ)))
      _ =
          ∑ m : Fin D,
            (starRingEnd ℂ) (b m) *
              ((1 / Real.pi : ℂ) *
                ∫ z : ℂ,
                  (fun z => finiteHermiteSum k a z) z *
                    (starRingEnd ℂ) (Phi k m.1 z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl (fun m _ => ?_)
              have hintegral :
                  ∫ z : ℂ,
                    finiteHermiteSum k a z *
                      ((starRingEnd ℂ) (Phi k m.1 z) * (Real.exp (-‖z‖ ^ 2) : ℂ))
                    =
                      ∫ z : ℂ,
                        (fun z => finiteHermiteSum k a z) z *
                          (starRingEnd ℂ) (Phi k m.1 z) * (Real.exp (-‖z‖ ^ 2) : ℂ) := by
                apply integral_congr_ae
                filter_upwards with z
                ac_rfl
              exact
                calc
                  (1 / Real.pi : ℂ) *
                      ((starRingEnd ℂ) (b m) *
                        ∫ z : ℂ,
                          finiteHermiteSum k a z *
                            ((starRingEnd ℂ) (Phi k m.1 z) * (Real.exp (-‖z‖ ^ 2) : ℂ)))
                    =
                      (starRingEnd ℂ) (b m) *
                        ((1 / Real.pi : ℂ) *
                          ∫ z : ℂ,
                            finiteHermiteSum k a z *
                              ((starRingEnd ℂ) (Phi k m.1 z) * (Real.exp (-‖z‖ ^ 2) : ℂ))) := by
                        ac_rfl
                  _ =
                      (starRingEnd ℂ) (b m) *
                        ((1 / Real.pi : ℂ) *
                          ∫ z : ℂ,
                            (fun z => finiteHermiteSum k a z) z *
                              (starRingEnd ℂ) (Phi k m.1 z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
                        rw [hintegral]
      _ = ∑ m : Fin D, (starRingEnd ℂ) (b m) * weightedInner (finiteHermiteSum k a) (Phi k m.1) :=
          by
              refine Finset.sum_congr rfl ?_
              intro m hm
              rfl
  · intro m hm
    simpa only [ofReal_exp, ofReal_neg, ofReal_pow, mul_comm, mul_left_comm, mul_assoc] using
      (integrable_finiteHermiteSum_weightedCross (k := k) (a := a) (n := m.1)).const_mul
        ((starRingEnd ℂ) (b m))
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
    ∀ {k D : ℕ} (a b : Fin D → ℂ),
      weightedInner (finiteHermiteSum k a) (finiteHermiteSum k b) =
        ∑ n : Fin D, a n * star (b n) := by
  intro k D a b
  rw [weightedInner_finiteHermiteSum]
  calc
    ∑ m : Fin D, (starRingEnd ℂ) (b m) * weightedInner (finiteHermiteSum k a) (Phi k m.1)
      = ∑ m : Fin D, a m * star (b m) := by
          refine Finset.sum_congr rfl ?_
          intro m hm
          rw [weightedInner_finiteHermiteSum_basis]
          have horth :
              ∀ x : Fin D, weightedInner (Phi k x.1) (Phi k m.1) = if x = m then 1 else 0 := by
            intro x
            rw [phi_orthonormal]
            by_cases hxm : x = m
            · simp_all only [mem_univ, ↓reduceIte]
            · have hxval : x.1 ≠ m.1 := by
                intro hEq
                exact hxm (Fin.ext hEq)
              simp [hxm, hxval]
          calc
            star (b m) * ∑ x : Fin D, a x * weightedInner (Phi k x.1) (Phi k m.1)
              = star (b m) * ∑ x : Fin D, a x * (if x = m then (1 : ℂ) else 0) := by
                  simp_all only [mem_univ, RCLike.star_def, mul_ite, mul_one, mul_zero, sum_ite_eq',
                    ↓reduceIte]
            _ = star (b m) * a m := by simp
            _ = a m * star (b m) := by ring
    _ = ∑ n : Fin D, a n * star (b n) := by rfl
end HermitekLEAN
