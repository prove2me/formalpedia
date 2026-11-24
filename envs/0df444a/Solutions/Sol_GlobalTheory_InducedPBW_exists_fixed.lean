-- Prove2me | solution 1 for GlobalTheory.InducedPBW.exists_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:58:42.011063+00:00
-- url     : https://prove2.me/submissions/fe4162b1-4904-48fe-aa3b-7c53c51947f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DegreeSingleAdd
import Theorems.Thm_GlobalTheory_InducedPBW_eq_on_degLt
import Theorems.Thm_GlobalTheory_InducedPBW_step_agree

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
theorem _root_.solution : ∃ δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V),
    Pres δ ∧ step e c act δ = δ := by
  let d : ℕ → g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V) := fun n => (step e c act)^[n] 0
  have hd : ∀ n, d (n + 1) = step e c act (d n) := fun n => Function.iterate_succ_apply' _ _ _
  have hp : ∀ n, Pres (d n) := by
    intro n
    induction n with
    | zero => intro n x m _; simp [d]
    | succ n ih => rw [hd]; exact ih.step e c act
  have hag : ∀ n k, ∀ x, ∀ m ∈ degLt R ι V n, d n x m = d (n + k) x m := by
    intro n
    induction n with
    | zero =>
      intro k x
      exact eq_on_degLt _ _ fun α v h => absurd h (Nat.not_lt_zero _)
    | succ n ih =>
      intro k
      rw [show n + 1 + k = (n + k) + 1 by omega, hd, hd]
      exact step_agree e c act (hp n) (ih k)
  let δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V) :=
    extend fun α => (d (α.degree + 1)).compl₂ (zv α)
  have hδ : ∀ x α v, δ x (zv α v) = d (α.degree + 1) x (zv α v) := by
    intro x α v
    simp [δ, extend_zv]
  have hδn : ∀ n x, ∀ m ∈ degLt R ι V n, d n x m = δ x m := by
    intro n x
    refine eq_on_degLt _ _ fun α v h => ?_
    obtain ⟨k, rfl⟩ : ∃ k, n = α.degree + 1 + k := ⟨n - (α.degree + 1), by omega⟩
    rw [hδ, ← hag _ k x _ (zv_mem (Nat.lt_succ_self _) v)]
  refine ⟨δ, fun n x m hm => ?_, ?_⟩
  · rw [← hδn n x m hm]; exact hp n n x m hm
  · ext1 x
    refine ext_zv fun α v => ?_
    rw [hδ, hd]
    exact (step_agree e c act (hp _) (hδn _) x _ (zv_mem (Nat.lt_succ_self _) v)).symm
end GlobalTheory.InducedPBW
