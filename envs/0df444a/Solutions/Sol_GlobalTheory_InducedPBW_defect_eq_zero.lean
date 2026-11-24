-- Prove2me | solution 1 for GlobalTheory.InducedPBW.defect_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:50:17.625811+00:00
-- url     : https://prove2.me/submissions/711e0666-d91d-40a0-a793-0762cf6faa96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DegreeSingleAdd
import Theorems.Thm_GlobalTheory_InducedPBW_eq_on_degLt
import Theorems.Thm_GlobalTheory_InducedPBW_rho_apply
import Theorems.Thm_GlobalTheory_InducedPBW_c_strip
import Theorems.Thm_GlobalTheory_InducedPBW_rho_e_le
import Theorems.Thm_GlobalTheory_InducedPBW_le_support_add
import Theorems.Thm_GlobalTheory_InducedPBW_defect_apply
import Theorems.Thm_GlobalTheory_InducedPBW_defect_e
import Theorems.Thm_GlobalTheory_InducedPBW_defect_strip
import Theorems.Thm_GlobalTheory_InducedPBW_rho_zero_of_k

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.InducedPBW
variable {R : Type*} [CommRing R] {ι : Type*} {V : Type*} [AddCommGroup V] [Module R V]
variable {g : Type*} [LieRing g] [LieAlgebra R g]
variable [Fintype ι] [LinearOrder ι] (e : ι → g) (c : ι → g →ₗ[R] R) (act : g →ₗ[R] Module.End R V)
variable {e c act} {δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V)}
  (hce : ∀ i j, c i (e j) = if i = j then 1 else 0)
include hce
variable (hf : step e c act δ = δ)
include hf
namespace GlobalTheory.InducedPBW
theorem _root_.solution (hp : Pres δ)
    (hK : ∀ x y, (∀ j, c j x = 0) → (∀ j, c j y = 0) → ∀ j, c j ⁅x, y⁆ = 0)
    (hact : ∀ x y, (∀ j, c j x = 0) → (∀ j, c j y = 0) →
      act ⁅x, y⁆ = act x * act y - act y * act x) (n : ℕ) :
    ∀ x y, ∀ m ∈ degLt R ι V n, defect c δ m x y = 0 := by
  have lin : ∀ n x y, (∀ α v, α.degree < n → defect c δ (zv α v) x y = 0) →
      ∀ m ∈ degLt R ι V n, defect c δ m x y = 0 := by
    intro n x y h
    exact eq_on_degLt (rho c δ x * rho c δ y - rho c δ y * rho c δ x - rho c δ ⁅x, y⁆) 0 h
  induction n with
  | zero => exact fun x y => lin 0 x y fun α v h => absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    refine fun x y => lin _ x y fun α v hα => ?_
    rcases exponent_cases α with rfl | ⟨i, J, hJ, rfl⟩
    · rw [defect_strip (e := e) _ Finset.univ fun j _ x => defect_e hce hf j 0 (by simp) x v]
      have hx := fun j => c_strip hce (Finset.mem_univ j) x
      have hy := fun j => c_strip hce (Finset.mem_univ j) y
      rw [defect_apply, rho_zero_of_k hf _ hx, rho_zero_of_k hf _ hy,
        rho_zero_of_k hf _ hx, rho_zero_of_k hf _ hy,
        rho_zero_of_k hf _ (hK _ _ hx hy), hact _ _ hx hy]
      simp
    · rw [defect_strip (e := e) _ (Finset.univ.filter (· ≤ i)) fun j hj x =>
        defect_e hce hf j _ (fun k hk => (show j ≤ i by simpa using hj).trans
          (le_support_add hJ le_rfl k hk)) x v]
      have hx : ∀ j, j ≤ i → c j (strip e c (Finset.univ.filter (· ≤ i)) x) = 0 :=
        fun j hj => c_strip hce (by simpa using hj) x
      have hy : ∀ j, j ≤ i → c j (strip e c (Finset.univ.filter (· ≤ i)) y) = 0 :=
        fun j hj => c_strip hce (by simpa using hj) y
      generalize strip e c (Finset.univ.filter (· ≤ i)) x = x at hx
      generalize strip e c (Finset.univ.filter (· ≤ i)) y = y at hy
      rw [degree_single_add] at hα
      have hz : zv J v ∈ degLt R ι V n := zv_mem (by omega) v
      have key : ∀ a b : g, (∀ j, j ≤ i → c j b = 0) →
          defect c δ (rho c δ b (zv J v)) a (e i) = 0 := by
        intro a b hb
        have : defect c δ (rho c δ b (zv J v)) a (e i) =
            ∑ j, c j b • defect c δ (mulX j (zv J v)) a (e i) +
              defect c δ (δ b (zv J v)) a (e i) := by
          simp only [defect_apply, rho_apply c δ b, mulLin_apply c b, map_add, map_sum, map_smul,
            smul_sub, Finset.sum_sub_distrib]
          abel
        rw [this, ih _ _ _ (hp _ _ _ hz), add_zero]
        refine Finset.sum_eq_zero fun j _ => ?_
        by_cases hj : j ≤ i
        · simp [hb j hj]
        · rw [mulX_zv, defect_e hce hf i _ (le_support_add hJ (not_le.mp hj).le), smul_zero]
      have k1 := key x y hy
      have k2 := key y x hx
      have k3 := ih x y _ hz
      have k4 := ih ⁅x, e i⁆ y _ hz
      have k5 := ih x ⁅y, e i⁆ _ hz
      have k6 := ih ⁅x, y⁆ (e i) _ hz
      have k7 := congrArg (rho c δ x) (defect_e hce hf i J hJ y v)
      have k8 := congrArg (rho c δ y) (defect_e hce hf i J hJ x v)
      have k9 := congrArg (rho c δ (e i)) k3
      have jac : ⁅⁅x, y⁆, e i⁆ = ⁅⁅x, e i⁆, y⁆ + ⁅x, ⁅y, e i⁆⁆ := by
        rw [leibniz_lie x y (e i), ← lie_skew y ⁅x, e i⁆]; abel
      rw [← rho_e_le hce hf i J hJ]
      simp only [defect_apply, map_sub, map_zero, jac, map_add, LinearMap.add_apply] at *
      linear_combination (norm := abel1) k7 - k8 + k1 - k2 + k9 + k4 + k5 - k6
end GlobalTheory.InducedPBW
