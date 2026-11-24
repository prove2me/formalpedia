-- Prove2me | solution 1 for GlobalTheory.InducedPBW.exists_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:10:22.434224+00:00
-- url     : https://prove2.me/submissions/8cd9635f-2890-4749-8623-2d7205a28ca4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DegreeSingleAdd
import Theorems.Thm_GlobalTheory_InducedPBW_rho_apply
import Theorems.Thm_GlobalTheory_InducedPBW_exists_fixed
import Theorems.Thm_GlobalTheory_InducedPBW_defect_apply
import Theorems.Thm_GlobalTheory_InducedPBW_rho_zero_of_k
import Theorems.Thm_GlobalTheory_InducedPBW_defect_eq_zero

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
namespace GlobalTheory.InducedPBW
theorem _root_.solution (hce : ∀ i j, c i (e j) = if i = j then 1 else 0)
    (hK : ∀ x y, (∀ j, c j x = 0) → (∀ j, c j y = 0) → ∀ j, c j ⁅x, y⁆ = 0)
    (hact : ∀ x y, (∀ j, c j x = 0) → (∀ j, c j y = 0) →
      act ⁅x, y⁆ = act x * act y - act y * act x) :
    ∃ ρ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V),
      (∀ x y, ρ ⁅x, y⁆ = ρ x * ρ y - ρ y * ρ x) ∧
      (∀ x, (∀ j, c j x = 0) → ∀ v, ρ x (zv 0 v) = zv 0 (act x v)) ∧
      ∀ n x, ∀ m ∈ degLt R ι V n, ρ x m - mulLin c x m ∈ degLt R ι V n := by
  obtain ⟨δ, hp, hf⟩ := exists_fixed e c act
  refine ⟨rho c δ, fun x y => ext_zv fun α v => ?_, fun x hx v => rho_zero_of_k hf x hx v,
    fun n x m hm => by simpa [rho_apply] using hp n x m hm⟩
  have := defect_eq_zero hce hf hp hK hact _ x y _ (zv_mem (Nat.lt_succ_self α.degree) v)
  rw [defect_apply, sub_eq_zero] at this
  exact this.symm
end GlobalTheory.InducedPBW
