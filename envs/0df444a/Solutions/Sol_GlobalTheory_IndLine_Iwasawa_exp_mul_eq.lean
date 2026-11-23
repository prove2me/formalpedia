-- Prove2me | solution 1 for GlobalTheory.IndLine.Iwasawa.exp_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:35:54.578453+00:00
-- url     : https://prove2.me/submissions/aed3f83f-f363-4b5a-a4d9-ef75b05176d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapStarMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Matrix
open GlobalTheory GlobalTheory.IndLine GlobalTheory.IndLine.Iwasawa
variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
open scoped Matrix
variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
namespace GlobalTheory.IndLine.Iwasawa
namespace _root_.GlobalTheory.IndLine.Iwasawa
theorem _root_.solution {A : Matrix m m ℂ} {D : Matrix n n ℂ}
    {B : Matrix m n ℂ} (h : A * B = B * D) :
    NormedSpace.exp A * B = B * NormedSpace.exp D := by
  letI : NormedRing (Matrix m m ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix m m ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  have hk : ∀ k : ℕ, A ^ k * B = B * D ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, ← pow_succ]
  have hA := NormedSpace.expSeries_summable' (𝕂 := ℂ) A
  have hD := NormedSpace.expSeries_summable' (𝕂 := ℂ) D
  let L : Matrix m m ℂ →L[ℂ] Matrix m n ℂ := LinearMap.toContinuousLinearMap
    { toFun := fun X => X * B, map_add' := fun X Y => Matrix.add_mul X Y B,
      map_smul' := fun c X => Matrix.smul_mul c X B }
  let L' : Matrix n n ℂ →L[ℂ] Matrix m n ℂ := LinearMap.toContinuousLinearMap
    { toFun := fun X => B * X, map_add' := fun X Y => Matrix.mul_add B X Y,
      map_smul' := fun c X => Matrix.mul_smul B c X }
  have e1 := L.map_tsum hA
  have e2 := L'.map_tsum hD
  simp only [L, L', LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk] at e1 e2
  rw [NormedSpace.exp_eq_tsum ℂ, NormedSpace.exp_eq_tsum ℂ]
  show (∑' k : ℕ, ((k.factorial : ℂ)⁻¹ • A ^ k)) * B = B * ∑' k : ℕ, ((k.factorial : ℂ)⁻¹ • D ^ k)
  refine e1.trans (Eq.trans ?_ e2.symm)
  congr 1
  funext k
  rw [Matrix.smul_mul, Matrix.mul_smul, hk]
end _root_.GlobalTheory.IndLine.Iwasawa
end GlobalTheory.IndLine.Iwasawa
