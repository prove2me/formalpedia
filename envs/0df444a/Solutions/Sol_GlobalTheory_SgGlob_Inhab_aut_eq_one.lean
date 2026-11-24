-- Prove2me | solution 1 for GlobalTheory.SgGlob.Inhab.aut_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:45:43.644158+00:00
-- url     : https://prove2.me/submissions/f69ac8cb-72e3-4887-8d3e-359792c7de70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.SgGlob GlobalTheory.SgGlob.Inhab
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.SgGlob.Inhab
theorem _root_.solution (σ : E →+* E) {g : ℕ} (hg : g ≠ 0) {x : Tri E 2 0}
    (hx : x ∈ GenConf σ !![1, 0; 0, -1] 1 (1 + 2 * g) g !![-1 - (g : E)])
    {γ : Matrix (Fin 2) (Fin 2) E} (hγ : IsoTri σ !![1, 0; 0, -1] γ x x) : γ = 1 := by
  obtain ⟨Λ, P, Q⟩ := x
  obtain ⟨-, ⟨⟨-, h1⟩, ⟨-, h2⟩, h3⟩, -⟩ := hx
  obtain ⟨-, -, hP, hQ⟩ := hγ
  dsimp only at h1 h2 h3 hP hQ
  have hg' : (g : E) ≠ 0 := Nat.cast_ne_zero.2 hg
  have e1 := congrFun (congrFun h1 0) 0
  have e2 := congrFun (congrFun h2 0) 0
  have e3 := congrFun (congrFun h3 0) 0
  simp [pairM, cT, TF, Matrix.mul_apply] at e1 e2 e3
  have hd : P 0 0 * Q 1 0 - P 1 0 * Q 0 0 ≠ 0 := by
    intro hd
    have q0 : Q 0 0 = (1 + g) * P 0 0 := by
      linear_combination Q 0 0 * e1 - P 0 0 * e3 - σ (P 1 0) * hd
    have q1 : Q 1 0 = (1 + g) * P 1 0 := by
      linear_combination Q 1 0 * e1 - P 1 0 * e3 - σ (P 0 0) * hd
    rw [q0, q1] at e2
    simp only [map_mul, map_add, map_one, map_natCast] at e2
    apply pow_ne_zero 2 hg'
    linear_combination (1 + g : E) ^ 2 * e1 - e2
  have p (i) := congrFun (congrFun hP i) 0
  have q (i) := congrFun (congrFun hQ i) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at p q
  ext i j
  apply mul_left_cancel₀ hd
  fin_cases i <;> fin_cases j <;> simp
  · linear_combination Q 1 0 * p 0 - P 1 0 * q 0
  · right
    apply mul_left_cancel₀ hd
    linear_combination P 0 0 * q 0 - Q 0 0 * p 0
  · right
    apply mul_left_cancel₀ hd
    linear_combination Q 1 0 * p 1 - P 1 0 * q 1
  · linear_combination P 0 0 * q 1 - Q 0 0 * p 1
end GlobalTheory.SgGlob.Inhab
