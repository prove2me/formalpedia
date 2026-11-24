-- Prove2me | solution 1 for HermitekLEAN.finiteHermiteSum_circle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:01:54.296933+00:00
-- url     : https://prove2.me/submissions/0d32e6c8-875a-47db-b42c-7ac8e9f60c47

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Theorems.Thm_HermitekLEAN_phi_polar
public import Theorems.Thm_HermitekLEAN_qkn_real
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
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
    ∀ {k D : ℕ} (a : Fin D → ℂ) {r : ℝ},
      0 < r →
        ∀ t : Circle,
          finiteHermiteSum k a (circlePoint r t) =
            circleLeadingFactor k r *
              (fourier (-(k : ℤ)) t : ℂ) *
                finiteCirclePoly k r a t := by
  intro k D a r hr t
  have hpoly :
      ∑ n : Fin D, a n * ((qkn k n.1 r : ℂ) * fourier (n.1 : ℤ) t) = finiteCirclePoly k r a t := by
    by_cases hD : D = 0
    · subst hD
      have hband0 : frequencyBand 0 0 = Finset.range 1 := by simp [HermiteLEAN.frequencyBand]
      have hzero : finiteCirclePoly k r a t = 0 := by
        rw [finiteCirclePoly, positiveTrigonometricPolynomial, hband0]
        change Finset.sum (Finset.range 1) (fun n => finiteCircleCoeff k r a n * fourier (n : ℤ)
            t) = 0
        rw [Finset.sum_range_one]
        simp [finiteCircleCoeff]
      simp [hzero]
    · have hDpos : 1 ≤ D := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hD)
      have hsum :
          ∑ n ∈ frequencyBand 0 D,
              finiteCircleCoeff k r a n * fourier (n : ℤ) t =
            ∑ n : Fin D, a n * ((qkn k n.1 r : ℂ) * fourier (n.1 : ℤ) t) := by
        simpa only [HermiteLEAN.frequencyBand, zero_add, finiteCircleCoeff, mul_comm, fourier_apply,
          natCast_zsmul, mul_dite, mul_zero, Fin.is_lt, ↓reduceDIte, Fin.eta, mul_left_comm,
          mul_assoc]
            using
          (sum_Icc_eq_sum_Fin 0 D hDpos
            (fun n => finiteCircleCoeff k r a n * fourier (n : ℤ) t))
      simp only [finiteCirclePoly, positiveTrigonometricPolynomial]
      exact hsum.symm
  calc
    finiteHermiteSum k a (circlePoint r t)
        = ∑ n : Fin D, circleLeadingFactor k r *
            (fourier (-(k : ℤ)) t : ℂ) * (a n * ((qkn k n.1 r : ℂ) * fourier (n.1 : ℤ) t)) := by
            rw [finiteHermiteSum]
            refine Finset.sum_congr rfl ?_
            intro n hn
            rw [phi_polar (k := k) (n := n.1) (r := r) hr t]
            ac_rfl
    _ = circleLeadingFactor k r * (fourier (-(k : ℤ)) t : ℂ) *
        ∑ n : Fin D, a n * ((qkn k n.1 r : ℂ) * fourier (n.1 : ℤ) t) := by rw [← Finset.mul_sum]
    _ = circleLeadingFactor k r * (fourier (-(k : ℤ)) t : ℂ) * finiteCirclePoly k r a t := by
        rw [hpoly]
end HermitekLEAN
