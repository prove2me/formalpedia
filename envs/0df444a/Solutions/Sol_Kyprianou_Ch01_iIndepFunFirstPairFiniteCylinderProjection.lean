-- Prove2me | solution 1 for Kyprianou.Ch01.iIndepFunFirstPairFiniteCylinderProjection
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T19:16:20.159704+00:00
-- url     : https://prove2.me/submissions/276e2535-2c64-477c-80a9-3d489be6f4f5

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_iIndepFunFirstPairFiniteShiftedTailArrays
open MeasureTheory ProbabilityTheory Set
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω)
    (f : (ℕ ⊕ ℕ) → Ω → ℝ)
    (hIndep : iIndepFun f Q)
    (hMeas : ∀ i : ℕ ⊕ ℕ, Measurable (f i))
    (I : Finset (ℕ ⊕ ℕ)) :
    IndepFun
      (fun w => (f (Sum.inl 0) w, f (Sum.inr 0) w))
      (fun w (i : I) => f (Sum.map Nat.succ Nat.succ i.val) w) Q := by
  classical
  let S : Finset (ℕ ⊕ ℕ) := {Sum.inl 0, Sum.inr 0}
  let shift : (ℕ ⊕ ℕ) → (ℕ ⊕ ℕ) := Sum.map Nat.succ Nat.succ
  let T : Finset (ℕ ⊕ ℕ) := I.image shift
  have hST : IndepFun
      (fun w (i : S) => f i.val w)
      (fun w (i : T) => f i.val w) Q :=
    Kyprianou.Ch01.iIndepFunFirstPairFiniteShiftedTailArrays
      Q f hIndep hMeas I S T rfl rfl
  let p : S := ⟨Sum.inl 0, by simp [S]⟩
  let q : S := ⟨Sum.inr 0, by simp [S]⟩
  let emb (i : I) : T :=
    ⟨shift i.val, Finset.mem_image.mpr ⟨i.val, i.property, rfl⟩⟩
  let phi : (S → ℝ) → ℝ × ℝ := fun v => (v p, v q)
  let psi : (T → ℝ) → (I → ℝ) := fun v i => v (emb i)
  have hPsi : Measurable psi := by
    change Measurable (fun v : T → ℝ => fun i : I => v (emb i))
    exact measurable_pi_lambda
      (fun v : T → ℝ => fun i : I => v (emb i))
      (fun i => measurable_pi_apply (emb i))
  have hComp := ProbabilityTheory.IndepFun.comp hST
    ((measurable_pi_apply p).prodMk (measurable_pi_apply q)) hPsi
  convert hComp using 1
  · funext w
    rfl
  · funext w i
    simp [psi, emb, shift, Function.comp_apply]
