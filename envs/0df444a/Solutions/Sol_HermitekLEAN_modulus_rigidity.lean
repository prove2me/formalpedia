-- Prove2me | solution 1 for HermitekLEAN.modulus_rigidity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:56:20.762354+00:00
-- url     : https://prove2.me/submissions/d26665ff-9d82-4d35-9374-4c65bc02af4e

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_ModulusRigidity
public import Theorems.Thm_HermitekLEAN_growth_forces_finite
public import Theorems.Thm_HermitekLEAN_finite_modulus_rigidity
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_expansion
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real


section
@[expose] public section
open Complex MeasureTheory Real Finset
open scoped Topology
noncomputable section
namespace HermitekLEAN
private theorem hermiteSeries_finiteCoeffSeq {k d : ℕ} (a : Fin (d + 1) → ℂ) :
    hermiteSeries k (finiteCoeffSeq a) = finiteHermiteSum k a := by
  funext z
  unfold hermiteSeries finiteHermiteSum finiteCoeffSeq
  rw [tsum_eq_sum (s := Finset.range (d + 1))]
  · have hleft :
        (∑ x : Fin (d + 1), if (x : ℕ) ≤ d then a x * Phi k x.1 z else 0) =
          ∑ n : Fin (d + 1), a n * Phi k n.1 z := by
        refine Finset.sum_congr rfl ?_
        intro n hn
        have hnle : (n : ℕ) ≤ d := Nat.le_of_lt_succ n.is_lt
        simp [hnle]
    have hsum :=
      Fin.sum_univ_eq_sum_range
        (fun x : ℕ => (if h : x < d + 1 then a ⟨x, h⟩ else 0) * Phi k x z) (d + 1)
    simp_all
  · simp_all
end HermitekLEAN
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped Topology
noncomputable section
open HermitekLEAN
namespace HermitekLEAN
theorem _root_.solution :
    ∀ {k d : ℕ}
      (a : Fin (d + 1) → ℂ)
      (_hTop : topCoeff a ≠ 0)
      {G : ℂ → ℂ},
        G ∈ Hk k →
          (∀ z : ℂ, ‖G z‖ = ‖finiteHermiteSum k a z‖) →
            ∃ w : ℂ, ‖w‖ = 1 ∧ G = w • finiteHermiteSum k a := by
  intro k d a hTop G hG hmod
  let b : Fin (d + 1) → ℂ := fun n => hermiteCoeff k G n.1
  have hvanish : ∀ n : ℕ, d < n → hermiteCoeff k G n = 0 :=
    growth_forces_finite (k := k) (d := d) (a := a) hTop hG hmod
  have hcoeffs : hermiteCoeff k G = finiteCoeffSeq b := by
    funext n
    unfold finiteCoeffSeq
    by_cases hn : n < d + 1
    · simp [hn, b]
    · simp_all
  have hG_eq : G = finiteHermiteSum k b := by
    calc
      G = hermiteSeries k (hermiteCoeff k G) := hermiteCoeff_expansion (k := k) (G := G) hG
      _ = hermiteSeries k (finiteCoeffSeq b) := by rw [hcoeffs]
      _ = finiteHermiteSum k b := hermiteSeries_finiteCoeffSeq (k := k) (d := d) b
  have hmod' : ∀ z : ℂ, ‖finiteHermiteSum k b z‖ = ‖finiteHermiteSum k a z‖ := by
    simp_all
  obtain ⟨w, hw, hwb⟩ := finite_modulus_rigidity (k := k) (d := d) (a := a) (b := b) hTop hmod'
  refine ⟨w, hw, ?_⟩
  simpa [hG_eq] using hwb
end HermitekLEAN
