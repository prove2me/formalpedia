-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.colFourier22_colFourier22_comm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/c277577f-04e8-577c-815a-9f7cab563be3

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Theorems.Thm_LanglandsTunnell_CubicInduction_isSchwartzBruhat_colFourier23
import Theorems.Thm_LanglandsTunnell_CubicInduction_colFourier23_colFourier23_comm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_colFourier22_colFourier22_comm

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

namespace CS22

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (v.adicCompletion ℚ)
local notation "M22" => (Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
local notation "M23" => (Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ))

noncomputable def pad (X : M22) : M23 := Matrix.of fun i k => if h : (k : ℕ) < 2 then X i ⟨k, h⟩ else 0

noncomputable def cut (Y : M23) : M22 := Matrix.of fun i k => Y i (Fin.castSucc k)

theorem continuous_cut : Continuous (cut v) := by
  refine continuous_pi fun i => continuous_pi fun k => ?_
  simp only [cut, Matrix.of_apply]; fun_prop

theorem continuous_pad : Continuous (pad v) := by
  refine continuous_pi fun i => continuous_pi fun k => ?_
  simp only [pad, Matrix.of_apply]
  split_ifs <;> fun_prop

theorem pad_castSucc (X : M22) (i : Fin 2) (k : Fin 2) : pad v X i (Fin.castSucc k) = X i k := by
  have hk : ((Fin.castSucc k : Fin 3) : ℕ) < 2 := by simp [k.isLt]
  simp only [pad, Matrix.of_apply, dif_pos hk]
  congr 1

theorem pad_two (X : M22) (i : Fin 2) : pad v X i 2 = 0 := by
  simp [pad]

theorem cut_setCol23_pad (X : M22) (j : Fin 2) (u : F × F) :
    cut v (setCol23 v (pad v X) (Fin.castSucc j) u) = setCol22 v X j u := by
  ext i k
  simp only [cut, Matrix.of_apply, setCol23_apply, setCol22_apply]
  by_cases hk : k = j
  · subst hk; simp
  · have : (Fin.castSucc k : Fin 3) ≠ Fin.castSucc j := fun h => hk (Fin.castSucc_injective _ h)
    rw [if_neg this, if_neg hk, pad_castSucc]

noncomputable def lift (φ : M22 → ℂ) (Y : M23) : ℂ :=
  φ (cut v Y) * ((Metric.closedBall (0 : F) 1).indicator (fun _ => (1 : ℂ)) (Y 0 2) *
    (Metric.closedBall (0 : F) 1).indicator (fun _ => (1 : ℂ)) (Y 1 2))

theorem lift_setCol23_pad (φ : M22 → ℂ) (X : M22) (j : Fin 2) (u : F × F) :
    lift v φ (setCol23 v (pad v X) (Fin.castSucc j) u) = φ (setCol22 v X j u) := by
  rw [lift, cut_setCol23_pad]
  have h2 : ∀ i : Fin 2, setCol23 v (pad v X) (Fin.castSucc j) u i 2 = 0 := by
    intro i
    have : (2 : Fin 3) ≠ Fin.castSucc j := by
      intro h; have := congrArg Fin.val h; fin_cases j <;> simp at this
    rw [setCol23_apply, if_neg this, pad_two]
  rw [h2 0, h2 1, Set.indicator_of_mem (Metric.mem_closedBall_self zero_le_one), mul_one, mul_one]

theorem colFourier23_lift_pad (η : AddChar F ℂ) (φ : M22 → ℂ) (j : Fin 2) (X : M22) :
    colFourier23 v η (Fin.castSucc j) (lift v φ) (pad v X) = colFourier22 v η j φ X := by
  simp only [colFourier23_apply, colFourier22_apply, lift_setCol23_pad, pad_castSucc]

theorem isSchwartzBruhat_lift (φ : M22 → ℂ) (hφ : IsSchwartzBruhat φ) : IsSchwartzBruhat (lift v φ) := by
  have hS : IsCompact (Metric.closedBall (0 : F) 1) := isCompact_closedBall 0 1
  have hSo : IsClopen (Metric.closedBall (0 : F) 1) :=
    ⟨Metric.isClosed_closedBall, IsUltrametricDist.isOpen_closedBall 0 one_ne_zero⟩
  have hind : IsSchwartzBruhat ((Metric.closedBall (0 : F) 1).indicator fun _ : F => (1 : ℂ)) :=
    IsSchwartzBruhat.indicator_const hSo hS 1
  have hc02 : Continuous fun Y : M23 => Y 0 2 := (continuous_apply 2).comp (continuous_apply 0)
  have hc12 : Continuous fun Y : M23 => Y 1 2 := (continuous_apply 2).comp (continuous_apply 1)
  refine ⟨(hφ.1.comp_continuous (continuous_cut v)).mul ((hind.1.comp_continuous hc02).mul (hind.1.comp_continuous hc12)), ?_⟩

  let A : M22 × (F × F) → M23 := fun q =>
    Matrix.of fun i k => if h : (k : ℕ) < 2 then q.1 i ⟨k, h⟩ else (if i = 0 then q.2.1 else q.2.2)
  have hAc : Continuous A := by
    refine continuous_pi fun i => continuous_pi fun k => ?_
    simp only [A, Matrix.of_apply]
    split_ifs <;> fun_prop
  have hAR : ∀ Y : M23, A (cut v Y, (Y 0 2, Y 1 2)) = Y := by
    intro Y; ext i k
    simp only [A, cut, Matrix.of_apply]
    by_cases hk : (k : ℕ) < 2
    · rw [dif_pos hk]; congr 1
    · rw [dif_neg hk]
      have : k = 2 := by ext; simp; omega
      subst this
      fin_cases i <;> simp
  refine HasCompactSupport.intro ((hφ.2.prod (hS.prod hS)).image hAc) fun Y hY => ?_
  rw [lift]
  by_cases h1 : cut v Y ∈ tsupport φ
  · by_cases h2 : Y 0 2 ∈ Metric.closedBall (0 : F) 1
    · by_cases h3 : Y 1 2 ∈ Metric.closedBall (0 : F) 1
      · exact absurd ⟨(cut v Y, (Y 0 2, Y 1 2)), ⟨h1, h2, h3⟩, hAR Y⟩ hY
      · rw [Set.indicator_of_notMem h3, mul_zero, mul_zero]
    · rw [Set.indicator_of_notMem h2, zero_mul, mul_zero]
  · rw [image_eq_zero_of_notMem_tsupport h1, zero_mul]

theorem colFourier22_eq_comp_pad (η : AddChar F ℂ) (φ : M22 → ℂ) (j : Fin 2) :
    colFourier22 v η j φ = (colFourier23 v η (Fin.castSucc j) (lift v φ)) ∘ pad v := by
  funext X; exact (colFourier23_lift_pad v η φ j X).symm

theorem isSchwartzBruhat_comp_pad (G : M23 → ℂ) (hG : IsSchwartzBruhat G) : IsSchwartzBruhat (G ∘ pad v) := by
  refine ⟨hG.1.comp_continuous (continuous_pad v), ?_⟩
  refine HasCompactSupport.intro (hG.2.image (continuous_cut v)) fun X hX => ?_
  show G (pad v X) = 0
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  apply hX
  refine ⟨pad v X, hmem, ?_⟩
  ext i k; simp only [cut, Matrix.of_apply, pad_castSucc]

theorem isSchwartzBruhat_colFourier22 (η : AddChar F ℂ) (n : ℤ)
    (hηn : ∀ x : F, Valued.v x ≤ WithZero.exp n → η x = 1)
    (hηn' : ∃ x : F, Valued.v x ≤ WithZero.exp (n + 1) ∧ η x ≠ 1)
    (j : Fin 2) (φ : M22 → ℂ) (hφ : IsSchwartzBruhat φ) : IsSchwartzBruhat (colFourier22 v η j φ) := by
  rw [colFourier22_eq_comp_pad]
  exact isSchwartzBruhat_comp_pad v _
    (LanglandsTunnell.CubicInduction.isSchwartzBruhat_colFourier23 v η n hηn hηn' _ _ (isSchwartzBruhat_lift v φ hφ))

theorem cut_setCol23 (Y : M23) (j : Fin 2) (u : F × F) :
    cut v (setCol23 v Y (Fin.castSucc j) u) = setCol22 v (cut v Y) j u := by
  ext i k
  simp only [cut, Matrix.of_apply, setCol23_apply, setCol22_apply]
  by_cases hk : k = j
  · subst hk; simp
  · have : (Fin.castSucc k : Fin 3) ≠ Fin.castSucc j := fun h => hk (Fin.castSucc_injective _ h)
    rw [if_neg this, if_neg hk]

theorem setCol23_two (Y : M23) (j : Fin 2) (u : F × F) (i : Fin 2) :
    setCol23 v Y (Fin.castSucc j) u i 2 = Y i 2 := by
  have : (2 : Fin 3) ≠ Fin.castSucc j := by
    intro h; have := congrArg Fin.val h; fin_cases j <;> simp at this
  rw [setCol23_apply, if_neg this]

theorem colFourier23_lift (η : AddChar F ℂ) (φ : M22 → ℂ) (j : Fin 2) (Y : M23) :
    colFourier23 v η (Fin.castSucc j) (lift v φ) Y = lift v (colFourier22 v η j φ) Y := by
  rw [colFourier23_apply, lift, colFourier22_apply, ← integral_mul_const]
  congr 1; funext u
  rw [lift, cut_setCol23, setCol23_two, setCol23_two]
  simp only [cut, Matrix.of_apply, Fin.castSucc]
  ring_nf

end CS22

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (η : AddChar (v.adicCompletion ℚ) ℂ) (n : ℤ)
    (hηn : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp n → η x = 1)
    (hηn' : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (n + 1) ∧ η x ≠ 1)
    (ρ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) → ℂ) (hρ : IsSchwartzBruhat ρ) :
    colFourier22 v η 0 (colFourier22 v η 1 ρ) = colFourier22 v η 1 (colFourier22 v η 0 ρ) := by
  funext X

  have hρl := CS22.isSchwartzBruhat_lift v ρ hρ
  have e0 : ∀ (ψ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) → ℂ) (j : Fin 2),
      colFourier22 v η j ψ X = colFourier23 v η (Fin.castSucc j) (CS22.lift v ψ) (CS22.pad v X) :=
    fun ψ j => (CS22.colFourier23_lift_pad v η ψ j X).symm
  rw [e0 _ 0, e0 _ 1]
  have e1 : CS22.lift v (colFourier22 v η 1 ρ) = colFourier23 v η (Fin.castSucc 1) (CS22.lift v ρ) :=
    funext fun Y => (CS22.colFourier23_lift v η ρ 1 Y).symm
  have e2 : CS22.lift v (colFourier22 v η 0 ρ) = colFourier23 v η (Fin.castSucc 0) (CS22.lift v ρ) :=
    funext fun Y => (CS22.colFourier23_lift v η ρ 0 Y).symm
  rw [e1, e2]
  have h := LanglandsTunnell.CubicInduction.colFourier23_colFourier23_comm v η n hηn hηn'
    (Fin.castSucc (0 : Fin 2)) (Fin.castSucc (1 : Fin 2)) (by decide) _ hρl
  exact congrFun h _

end S_LanglandsTunnell_CubicInduction_colFourier22_colFourier22_comm
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_colFourier22_colFourier22_comm (solution)
