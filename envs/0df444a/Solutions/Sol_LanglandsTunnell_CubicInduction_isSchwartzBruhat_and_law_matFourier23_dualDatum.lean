-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.isSchwartzBruhat_and_law_matFourier23_dualDatum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/ae0c64b2-9324-5f21-a2f3-ed4830a4996f

import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Theorems.Thm_LanglandsTunnell_CubicInduction_isSchwartzBruhat_colFourier23
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_isSchwartzBruhat_and_law_matFourier23_dualDatum

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction NumberField.StandardAddChar

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Ws28DD

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ v)
local notation "G2" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
local notation "M23" => (Matrix (Fin 2) (Fin 3) (HeightOneSpectrum.adicCompletion ℚ v))

theorem sb_mul_const {f : M23 → ℂ} (hf : IsSchwartzBruhat f) (c : ℂ) :
    IsSchwartzBruhat (fun Y => f Y * c) :=
  ⟨hf.1.comp (· * c), hf.2.mul_right⟩

theorem sb_add {f g : M23 → ℂ} (hf : IsSchwartzBruhat f) (hg : IsSchwartzBruhat g) :
    IsSchwartzBruhat (fun Y => f Y + g Y) :=
  ⟨hf.1.comp₂ hg.1 (· + ·), hf.2.add hg.2⟩

theorem sb_zero : IsSchwartzBruhat (fun _ : M23 => (0 : ℂ)) := IsSchwartzBruhat.zero

theorem sb_sum {ι : Type*} (s : Finset ι) (g : ι → M23 → ℂ) (hg : ∀ i ∈ s, IsSchwartzBruhat (g i)) :
    IsSchwartzBruhat (fun Y => ∑ i ∈ s, g i Y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using sb_zero v
  | insert a s ha ih =>
    have h : (fun Y => ∑ i ∈ insert a s, g i Y) = fun Y => g a Y + ∑ i ∈ s, g i Y := by
      funext Y; rw [Finset.sum_insert ha]
    rw [h]
    exact sb_add v (hg a (Finset.mem_insert_self a s)) (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))

theorem colFourier23_const_mul (η : AddChar F ℂ) (j : Fin 3) (c : ℂ) (f : M23 → ℂ) :
    colFourier23 v η j (fun Y => c * f Y) = fun X => c * colFourier23 v η j f X := by
  funext X
  rw [colFourier23_apply, colFourier23_apply, ← integral_const_mul]
  congr 1
  funext u
  ring

theorem matFourier23_const_mul (η : AddChar F ℂ) (c : ℂ) (f : M23 → ℂ) :
    matFourier23 v η (fun Y => c * f Y) = fun X => c * matFourier23 v η f X := by
  funext X
  rw [matFourier23_eq, matFourier23_eq, colFourier23_const_mul, colFourier23_const_mul, colFourier23_const_mul]

theorem level_inv (η : AddChar F ℂ) (n : ℤ)
    (hηn : ∀ x : F, Valued.v x ≤ WithZero.exp n → η x = 1)
    (hηn' : ∃ x : F, Valued.v x ≤ WithZero.exp (n + 1) ∧ η x ≠ 1) :
    (∀ x : F, Valued.v x ≤ WithZero.exp n → η⁻¹ x = 1) ∧
      ∃ x : F, Valued.v x ≤ WithZero.exp (n + 1) ∧ η⁻¹ x ≠ 1 := by
  refine ⟨fun x hx => ?_, ?_⟩
  · rw [AddChar.inv_apply]; exact hηn (-x) (by rwa [Valuation.map_neg])
  · obtain ⟨x, hx, hne⟩ := hηn'
    refine ⟨-x, by rwa [Valuation.map_neg], ?_⟩
    rwa [AddChar.inv_apply, neg_neg]

theorem w2_mul_transposeInvN_unipotent (w₂ : G2) (hw₂ : ((w₂ : G2) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0])
    (a : F) : w₂ * transposeInvN (Fin 2) (unipotentGL2 a) = unipotentGL2 (-a) * w₂ := by
  have hinv : ((unipotentGL2 a : G2)⁻¹ : G2) = unipotentGL2 (-a) := by
    refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
    rw [Units.val_mul, unipotentGL2_coe, unipotentGL2_coe, Units.val_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_transposeInvN, hinv, hw₂, unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]

theorem main (η : AddChar F ℂ) (n : ℤ)
    (hηn : ∀ x : F, Valued.v x ≤ WithZero.exp n → η x = 1)
    (hηn' : ∃ x : F, Valued.v x ≤ WithZero.exp (n + 1) ∧ η x ≠ 1)
    (w₂ : G2) (hw₂ : ((w₂ : G2) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0])
    (Φ : M23 → G2 → ℂ)
    (hΦ : ∃ (m : ℕ) (φ : Fin m → M23 → ℂ) (K : Fin m → G2 → ℂ),
        (∀ i, IsLocallyConstant (φ i) ∧ HasCompactSupport (φ i)) ∧
        (∀ i, IsLocallyConstant (K i) ∧ ∀ (a : F) (k : G2), K i (unipotentGL2 a * k) = η a * K i k) ∧
        Φ = fun X k => ∑ i, φ i X * K i k) :
    (∀ k : G2, IsSchwartzBruhat (fun X : M23 => matFourier23 v η⁻¹ (fun Y => Φ Y (w₂ * transposeInvN (Fin 2) k)) X)) ∧
    ∀ (X : M23) (a : F) (k : G2),
      matFourier23 v η⁻¹ (fun Y => Φ Y (w₂ * transposeInvN (Fin 2) (unipotentGL2 a * k))) X =
        η⁻¹ a * matFourier23 v η⁻¹ (fun Y => Φ Y (w₂ * transposeInvN (Fin 2) k)) X := by
  obtain ⟨m, φ, K, hφ, hK, rfl⟩ := hΦ
  obtain ⟨hinv, hinv'⟩ := level_inv v η n hηn hηn'
  refine ⟨fun k => ?_, fun X a k => ?_⟩
  ·
    have hsb : IsSchwartzBruhat (fun Y : M23 => ∑ i, φ i Y * K i (w₂ * transposeInvN (Fin 2) k)) :=
      sb_sum v Finset.univ (fun i Y => φ i Y * K i (w₂ * transposeInvN (Fin 2) k)) fun i _ => sb_mul_const v (hφ i) _
    have h := LanglandsTunnell.CubicInduction.isSchwartzBruhat_colFourier23 v η⁻¹ n hinv hinv' 0 _
      (LanglandsTunnell.CubicInduction.isSchwartzBruhat_colFourier23 v η⁻¹ n hinv hinv' 1 _
        (LanglandsTunnell.CubicInduction.isSchwartzBruhat_colFourier23 v η⁻¹ n hinv hinv' 2 _ hsb))
    rw [← matFourier23_eq] at h
    exact h
  ·
    have hpt : (fun Y : M23 => ∑ i, φ i Y * K i (w₂ * transposeInvN (Fin 2) (unipotentGL2 a * k))) =
        fun Y => η⁻¹ a * ∑ i, φ i Y * K i (w₂ * transposeInvN (Fin 2) k) := by
      funext Y
      rw [transposeInvN_mul, ← mul_assoc, w2_mul_transposeInvN_unipotent v w₂ hw₂ a, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_assoc (unipotentGL2 (-a)), (hK i).2, AddChar.inv_apply]
      ring
    rw [hpt, matFourier23_const_mul]

end Ws28DD

end

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction NumberField.StandardAddChar in

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (η : AddChar (v.adicCompletion ℚ) ℂ) (n : ℤ)
    (hηn : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp n → η x = 1)
    (hηn' : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (n + 1) ∧ η x ≠ 1)
    (w₂ : GL (Fin 2) (v.adicCompletion ℚ))
    (hw₂ : ((w₂ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = !![0, 1; 1, 0])
    (Φ : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) → GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (hΦ : ∃ (m : ℕ) (φ : Fin m → Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) → ℂ)
        (K : Fin m → GL (Fin 2) (v.adicCompletion ℚ) → ℂ),
        (∀ i, IsLocallyConstant (φ i) ∧ HasCompactSupport (φ i)) ∧
        (∀ i, IsLocallyConstant (K i) ∧
          ∀ (a : v.adicCompletion ℚ) (k : GL (Fin 2) (v.adicCompletion ℚ)), K i (unipotentGL2 a * k) = η a * K i k) ∧
        Φ = fun X k => ∑ i, φ i X * K i k) :
    (∀ k : GL (Fin 2) (v.adicCompletion ℚ),
        IsSchwartzBruhat (fun X : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) =>
          matFourier23 v η⁻¹ (fun Y => Φ Y (w₂ * transposeInvN (Fin 2) k)) X)) ∧
    ∀ (X : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ)) (a : v.adicCompletion ℚ)
      (k : GL (Fin 2) (v.adicCompletion ℚ)),
      matFourier23 v η⁻¹ (fun Y => Φ Y (w₂ * transposeInvN (Fin 2) (unipotentGL2 a * k))) X =
        η⁻¹ a * matFourier23 v η⁻¹ (fun Y => Φ Y (w₂ * transposeInvN (Fin 2) k)) X :=
  Ws28DD.main v η n hηn hηn' w₂ hw₂ Φ hΦ

end S_LanglandsTunnell_CubicInduction_isSchwartzBruhat_and_law_matFourier23_dualDatum
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_isSchwartzBruhat_and_law_matFourier23_dualDatum (solution)
