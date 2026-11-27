-- Prove2me | solution 1 for GlobalTheory.exists_matrix_basis_ker_of_exact_at_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:38:13.653734+00:00
-- url     : https://prove2.me/submissions/ee3b0402-7f66-4992-93ee-0f9724f43ff0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsMulEqSmulOneOfMulVecInjective
import Theorems.Thm_GlobalTheory_exists_kernel_certificate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (R K : Type) [CommRing R] [Field K] (g₀ : R →+* K) (a b c : ℕ) (D₀ : Matrix (Fin b) (Fin a) R) (D₁ : Matrix (Fin c) (Fin b) R), D₁ * D₀ = 0 → (∀ w : Fin b → K, (D₁.map g₀).mulVec w = 0 → ∃ v, (D₀.map g₀).mulVec v = w) → ∃ (r : R) (n : ℕ) (B : Matrix (Fin a) (Fin n) R), g₀ r ≠ 0 ∧ D₀ * B = 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g r) → ∀ v : Fin a → R', (D₀.map g).mulVec v = 0 → ∃! z : Fin n → R', (B.map g).mulVec z = v := by
  intro R K _ _ g₀ a b c D₀ D₁ h0 hex
  obtain ⟨r, n, B, C, H, hr, hB, hCB, hBC⟩ := exists_kernel_certificate g₀ D₀ D₁ h0 hex
  refine ⟨r, n, B, hr, hB, ?_⟩
  intro R' _ g hu v hv
  obtain ⟨u, hu⟩ := hu
  have hone : ∀ (m : ℕ) (x : Fin m → R'),
      ((r • (1 : Matrix (Fin m) (Fin m) R)).map g).mulVec x = g r • x := by
    intro m x
    funext k
    simp [Matrix.mulVec, dotProduct, Matrix.one_apply, apply_ite g]
  have h1 : ∀ z : Fin n → R', (C.map g).mulVec ((B.map g).mulVec z) = (u : R') • z := by
    intro z
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hCB, hone, hu]
  have h2 : (B.map g).mulVec ((C.map g).mulVec v) = (u : R') • v := by
    rw [hu, ← hone, ← hBC, Matrix.map_add _ (map_add g), Matrix.add_mulVec, Matrix.map_mul,
      Matrix.map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero,
      add_zero]
  refine ⟨((u⁻¹ : R'ˣ) : R') • (C.map g).mulVec v, ?_, ?_⟩
  · show (B.map g).mulVec _ = v
    rw [Matrix.mulVec_smul, h2, smul_smul, Units.inv_mul, one_smul]
  · intro z hz
    rw [← hz, h1, smul_smul, Units.inv_mul, one_smul]
end GlobalTheory
