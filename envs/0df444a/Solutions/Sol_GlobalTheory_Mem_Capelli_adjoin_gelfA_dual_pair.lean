-- Prove2me | solution 1 for GlobalTheory.Mem.Capelli.adjoin_gelfA_dual_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:11:27.536266+00:00
-- url     : https://prove2.me/submissions/8975e2bf-f36f-430a-adbb-167f7d31768e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PolarConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommuteGelfandInvariantMatrixUnitsOfGlRel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AdjoinGelfandInvariantsDualPairEq
import Theorems.Thm_GlobalTheory_Mem_Capelli_trAlg_shift
import Theorems.Thm_GlobalTheory_Mem_Capelli_adjoin_gelfA
import Theorems.Thm_GlobalTheory_Mem_Capelli_trAlg_mul_comm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.Mem.Lift
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Capelli
variable {A : Type} [Ring A] [Algebra ℂ A] {n m : ℕ}
namespace GlobalTheory.Mem.Capelli
theorem _root_.solution : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n m : ℕ) (x d : Fin n × Fin m → A), IsCCR x d → ∀ c c' : ℂ, Algebra.adjoin ℂ (Set.range (GlobalTheory.SmoothForms.gelfA fun i j : Fin n => ∑ a, x (i, a) * d (j, a) + if i = j then algebraMap ℂ A c else 0)) = Algebra.adjoin ℂ (Set.range (GlobalTheory.SmoothForms.gelfA fun a b : Fin m => -∑ i, x (i, b) * d (i, a) + if a = b then algebraMap ℂ A c' else 0)) := by
  intro A _ _ n m x d h c c'
  obtain ⟨-, hdd, hdx⟩ := h
  let X : Matrix (Fin n) (Fin m) A := Matrix.of fun i a => x (i, a)
  let D : Matrix (Fin m) (Fin n) A := Matrix.of fun a i => d (i, a)
  have hdx' : ∀ a l i b, D a l * X i b = X i b * D a l + if i = l ∧ b = a then 1 else 0 := fun a l i b => by
    have := hdx (i, b) (l, a)
    rw [sub_eq_iff_eq_add'] at this
    simpa [X, D] using this
  have h1 : (Matrix.of fun i j : Fin n => ∑ a, x (i, a) * d (j, a) + if i = j then algebraMap ℂ A c else 0)
      = (1 : ℂ) • (X * D) + c • 1 := by
    ext i j
    by_cases hij : i = j <;> simp [X, D, Matrix.mul_apply, Matrix.one_apply, hij, Algebra.algebraMap_eq_smul_one]
  have h2 : (Matrix.of fun a b : Fin m => -∑ i, x (i, b) * d (i, a) + if a = b then algebraMap ℂ A c' else 0)
      = (-1 : ℂ) • (D * X) + (c' + n) • 1 := by
    ext a b
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, hdx', Finset.sum_add_distrib]
    by_cases hab : a = b
    · subst hab
      simp [X, D, Algebra.algebraMap_eq_smul_one, add_smul, Nat.cast_smul_eq_nsmul]
      abel
    · simp [X, D, hab, Ne.symm hab]
  rw [adjoin_gelfA, adjoin_gelfA, h1, h2, trAlg_shift _ one_ne_zero, trAlg_shift _ (by norm_num)]
  exact trAlg_mul_comm X D (fun a l b j => hdd _ _) hdx'
end GlobalTheory.Mem.Capelli
