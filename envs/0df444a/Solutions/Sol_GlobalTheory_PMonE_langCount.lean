-- Prove2me | solution 1 for GlobalTheory.PMonE.langCount
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:28:26.705474+00:00
-- url     : https://prove2.me/submissions/be015991-eb80-4673-8366-14f7854b2e97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LangXRoot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LangCountFrobeniusEqMulVecSolutions
import Theorems.Thm_GlobalTheory_PMonE_langCount_integral
import Theorems.Thm_GlobalTheory_PMonE_langCount_card_semilinear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE
open Polynomial
namespace GlobalTheory.PMonE
theorem _root_.solution : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [IsAlgClosed F] (p : ℕ)
    [Fact p.Prime] [CharP F p] (m : Type) [Fintype m] [DecidableEq m] (e : ℕ), 0 < e →
    ∀ A : Matrix m m F, (∀ i j, ‖A i j‖ ≤ 1) → A.det ≠ 0 →
    (∀ x : m → F, (∀ i, x i ^ p ^ e = A.mulVec x i) → Integral x) ∧
    Nat.card {x : m → F // ∀ i, x i ^ p ^ e = A.mulVec x i} = (p ^ e) ^ Fintype.card m := by
  intro F _ _ _ p _ _ m _ _ e he A hA hdet
  have hq : 1 < p ^ e := Nat.one_lt_pow he.ne' (Fact.out : p.Prime).one_lt
  refine ⟨fun x hx => langCount_integral (p ^ e) hq A hA x hx, ?_⟩
  have hu : IsUnit A.det := isUnit_iff_ne_zero.2 hdet
  let Φ : (m → F) →+ (m → F) := AddMonoidHom.mk' (fun x => A⁻¹.mulVec (fun i => x i ^ p ^ e)) (by
    intro a b
    rw [← Matrix.mulVec_add]
    congr 1
    funext i
    simp only [Pi.add_apply]
    rw [add_pow_char_pow])
  have hΦ : ∀ (c : F) (v : m → F), Φ (c • v) = c ^ p ^ e • Φ v := by
    intro c v
    show A⁻¹.mulVec (fun i => (c • v) i ^ p ^ e) = c ^ p ^ e • A⁻¹.mulVec (fun i => v i ^ p ^ e)
    rw [← Matrix.mulVec_smul]
    congr 1
    funext i
    simp [mul_pow]
  have hfix : ∀ x : m → F, Φ x = x ↔ ∀ i, x i ^ p ^ e = A.mulVec x i := by
    intro x
    change A⁻¹.mulVec (fun i => x i ^ p ^ e) = x ↔ _
    constructor
    · intro h i
      have h2 := congrArg A.mulVec h
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hu, Matrix.one_mulVec] at h2
      exact congrFun h2 i
    · intro h
      have h2 : (fun i => x i ^ p ^ e) = A.mulVec x := funext h
      rw [h2, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hu, Matrix.one_mulVec]
  have hinj : Function.Injective Φ := by
    intro x y hxy
    change A⁻¹.mulVec (fun i => x i ^ p ^ e) = A⁻¹.mulVec (fun i => y i ^ p ^ e) at hxy
    have h2 := congrArg A.mulVec hxy
    simp only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hu, Matrix.one_mulVec] at h2
    funext i
    have h3 := congrFun h2 i
    rw [← iterateFrobenius_def, ← iterateFrobenius_def] at h3
    exact (iterateFrobenius F p e).injective h3
  have hc := langCount_card_semilinear F p e he Φ hΦ hinj
  rw [Module.finrank_fintype_fun_eq_card] at hc
  rw [← hc]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => (hfix x).symm)
end GlobalTheory.PMonE
