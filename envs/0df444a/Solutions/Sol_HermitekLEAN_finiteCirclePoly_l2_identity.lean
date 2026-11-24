-- Prove2me | solution 1 for HermitekLEAN.finiteCirclePoly_l2_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:06:35.208765+00:00
-- url     : https://prove2.me/submissions/a423d7e7-96df-409d-a301-f357f9881179

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Theorems.Thm_HermitekLEAN_qkn_real
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_PhaseRetrieval_integral_norm_sq_fourier_sum

attribute [local simp] HermitekLEAN.qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
section
@[expose] public section
open Complex MeasureTheory Real Finset
open scoped BigOperators Topology
noncomputable section
namespace HermitekLEAN
private theorem sum_Icc_eq_sum_Fin {α : Type*} [AddCommMonoid α]
    (N L : ℕ) (hL : 1 ≤ L) (f : ℕ → α) :
    ∑ n ∈ Finset.Icc N (N + L - 1), f n =
      ∑ m : Fin L, f (N + m.val) := by
  symm
  apply Finset.sum_nbij (fun (m : Fin L) => N + m.val)
  · intro m _
    exact Finset.mem_Icc.mpr ⟨Nat.le_add_right N m.val, by omega⟩
  · intro a _ b _ hab
    exact Fin.ext (Nat.add_left_cancel hab)
  · intro n hn
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hn
    refine ⟨⟨n - N, by omega⟩, Finset.mem_univ _, ?_⟩
    simp_all only [coe_Icc, Set.mem_Icc, and_self, add_tsub_cancel_of_le]
  · simp_all only [mem_univ, imp_self, implies_true]
private lemma circleL2Sq_finFourierPoly {D : ℕ} (c : Fin D → ℂ) :
    circleL2Sq (fun t : Circle => ∑ k : Fin D, c k * fourier (k.val : ℤ) t) =
      ∑ k : Fin D, ‖c k‖ ^ 2 := by
  let frequencies : Fin D ↪ ℤ :=
    ⟨fun i => (i.val : ℤ), fun i j h => Fin.ext (Nat.cast_injective h)⟩
  have hfrequencies (i : Fin D) : frequencies i = (i.val : ℤ) := rfl
  simpa only [circleL2Sq, HermiteLEAN.circleL2Sq, hfrequencies] using
    PhaseRetrieval.integral_norm_sq_fourier_sum (period := T) frequencies c
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
    ∀ {k D : ℕ} (r : ℝ) (a : Fin D → ℂ),
      circleL2Sq (finiteCirclePoly k r a) =
        ∑ n : Fin D, ‖a n‖ ^ 2 * |qkn k n.1 r| ^ 2 := by
  intro k D r a
  by_cases hD : D = 0
  · subst hD
    simp [finiteCirclePoly, HermiteLEAN.positiveTrigonometricPolynomial, HermiteLEAN.frequencyBand,
      HermiteLEAN.circleL2Sq, finiteCircleCoeff]
  · have hDpos : 1 ≤ D := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hD)
    have hpoly :
        finiteCirclePoly k r a =
          fun t : Circle => ∑ n : Fin D, a n * (qkn k n.1 r : ℂ) * fourier (n.1 : ℤ) t := by
      ext t
      change
        Finset.sum (Finset.Icc 0 (0 + D - 1))
            (fun n => (if h : n < D then a ⟨n, h⟩ * (qkn k n r : ℂ) else 0) * fourier (n : ℤ) t) =
          ∑ n : Fin D, a n * (qkn k n.1 r : ℂ) * fourier (n.1 : ℤ) t
      rw [sum_Icc_eq_sum_Fin 0 D hDpos]
      simp
    rw [hpoly, circleL2Sq_finFourierPoly]
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    ring
end HermitekLEAN
