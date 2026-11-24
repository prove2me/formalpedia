-- Prove2me | solution 1 for HermitekLEAN.finiteHermiteSum_mem_Hk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:06:57.364145+00:00
-- url     : https://prove2.me/submissions/f5798fa6-0bc8-4c31-94ee-92c3178ad170

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
public import Theorems.Thm_HermitekLEAN_finiteHermiteSum_normSq
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
private lemma weightedInner_finiteHermiteSum_coeff (k : ℕ) {D : ℕ} (a : Fin D → ℂ) (n : ℕ) :
    weightedInner (finiteHermiteSum k a) (Phi k n) =
      if h : n < D then a ⟨n, h⟩ else 0 := by
  rw [weightedInner_finiteHermiteSum_basis]
  by_cases h : n < D
  · let m : Fin D := ⟨n, h⟩
    calc ∑ x : Fin D, a x * weightedInner (Phi k x.1) (Phi k n)
        = ∑ x : Fin D, a x * (if x.1 = n then 1 else 0) := by
          refine Finset.sum_congr rfl ?_; intro x _; rw [phi_orthonormal]
      _ = ∑ x : Fin D, (if x = m then a m else 0) := by
          refine Finset.sum_congr rfl ?_; intro x _
          by_cases hx : x = m
          · subst hx; simp [m]
          · have : x.1 ≠ n := fun hEq => hx (Fin.ext (by exact hEq))
            simp [this, hx]
      _ = a m := by simp
    simp [m, h]
  · have : ∀ x : Fin D, a x * weightedInner (Phi k x.1) (Phi k n) = 0 := by
      intro x; rw [phi_orthonormal]
      simp [show x.1 ≠ n from fun hEq => h (hEq ▸ x.isLt)]
    simp [this, h]
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
    ∀ (k : ℕ) {D : ℕ} (a : Fin D → ℂ), finiteHermiteSum k a ∈ Hk k := by
  intro k D a
  refine ⟨?_, ?_⟩
  · change Integrable (fun z : ℂ => ‖finiteHermiteSum k a z‖ ^ 2 * rexp (-‖z‖ ^ 2))
    by_contra habs
    have hzero :
        (1 / Real.pi) * ∫ z : ℂ, ‖finiteHermiteSum k a z‖ ^ 2 * rexp (-‖z‖ ^ 2) = 0 := by
      rw [MeasureTheory.integral_undef habs]
      ring
    have hpos : (1 / Real.pi) * ∫ z : ℂ, ‖finiteHermiteSum k a z‖ ^ 2 * rexp (-‖z‖ ^ 2) =
        ∑ n : Fin D, ‖a n‖ ^ 2 := by
      change weightedNormSq (finiteHermiteSum k a) = _
      exact finiteHermiteSum_normSq (k := k) (a := a)
    rw [hpos] at hzero
    have hall_zero : ∀ n : Fin D, a n = 0 := by
      intro n
      have :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖a i‖)).mp hzero n
            (Finset.mem_univ n)
      exact norm_eq_zero.mp (by nlinarith only [this, sq_nonneg ‖a n‖])
    have hzero_fun : (fun z : ℂ => ‖finiteHermiteSum k a z‖ ^ 2 * rexp (-‖z‖ ^ 2)) = 0 := by
      ext z
      simp [finiteHermiteSum, hall_zero]
    simp_all
  · intro z
    simp_rw [weightedInner_finiteHermiteSum_coeff]
    let f : ℕ → ℂ := fun n => (if h : n < D then a ⟨n, h⟩ else 0) * Phi k n z
    change HasSum f (finiteHermiteSum k a z)
    have hfin : ∀ n, n ∉ Finset.range D → f n = 0 := by
      intro n hn
      simp only [f, Finset.mem_range, not_lt] at hn ⊢
      simp [show ¬(n < D) from not_lt.mpr hn]
    have hval : finiteHermiteSum k a z = ∑ n ∈ Finset.range D, f n := by
      simp only [finiteHermiteSum, f]
      rw [Finset.sum_range]
      simp_all
    rw [hval]
    exact hasSum_sum_of_ne_finset_zero hfin
end HermitekLEAN
