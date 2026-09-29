-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.matFourier23_comp_mul_transvection_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/7b580d8c-5a52-5aad-960a-3f652a3c8e59

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Theorems.Thm_LanglandsTunnell_CubicInduction_isSchwartzBruhat_colFourier23
import Theorems.Thm_LanglandsTunnell_CubicInduction_colFourier23_colFourier23_comm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_matFourier23_comp_mul_transvection_eq

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

namespace TransvTwist

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (v.adicCompletion ℚ)
local notation "M23" => (Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel

theorem isAddHaarMeasure_selfDualHaarAt : (selfDualHaarAt ℚ v : Measure F).IsAddHaarMeasure := by
  have hq : (Ideal.absNorm v.asIdeal : NNReal) ≠ 0 := by
    have h : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
    exact_mod_cast (show Ideal.absNorm v.asIdeal ≠ 0 by omega)
  have hc : ((Ideal.absNorm v.asIdeal : NNReal) ^
      (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ v) : ℝ) / 2)) ≠ 0 :=
    (NNReal.rpow_pos (pos_iff_ne_zero.mpr hq)).ne'
  show ((((Ideal.absNorm v.asIdeal : NNReal) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ v) : ℝ) / 2))
      • Measure.addHaarMeasure (integersPositiveCompacts ℚ v) : Measure F)).IsAddHaarMeasure
  rw [ENNReal.smul_def]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc) ENNReal.coe_ne_top

theorem mul_transvection_apply (Y : M23) (i j : Fin 3) (c : F) (a : Fin 2) (b : Fin 3) :
    (Y * Matrix.transvection i j c) a b = Y a b + (if b = j then c * Y a i else 0) := by
  rw [Matrix.transvection, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
  congr 1
  simp only [Matrix.mul_apply, Matrix.single_apply]
  by_cases hb : b = j
  · subst hb
    rw [if_pos rfl, Finset.sum_eq_single i]
    · simp [mul_comm]
    · intro k _ hk; simp [Ne.symm hk]
    · simp
  · rw [if_neg hb]
    exact Finset.sum_eq_zero fun k _ => by simp [Ne.symm hb]

noncomputable def modl (η : AddChar F ℂ) (i j : Fin 3) (c : F) (X : M23) : ℂ := η (-(c * (X 0 i * X 0 j + X 1 i * X 1 j)))

theorem col_j_twist (η : AddChar F ℂ) {i j : Fin 3} (hij : i ≠ j) (c : F) (ρ : M23 → ℂ) (X : M23) :
    colFourier23 v η j (fun Y => ρ (Y * Matrix.transvection i j c)) X = modl v η i j c X * colFourier23 v η j ρ X := by
  haveI := isAddHaarMeasure_selfDualHaarAt v
  simp only [colFourier23_apply, modl]
  set t : F × F := (c * X 0 i, c * X 1 i) with ht
  have hsub : ∀ u : F × F, setCol23 v X j u * Matrix.transvection i j c = setCol23 v X j (u + t) := by
    intro u; ext a b
    simp only [mul_transvection_apply, setCol23_apply]
    by_cases hb : b = j
    · subst hb
      simp only [if_pos rfl, if_true, if_neg hij, ht, Prod.fst_add, Prod.snd_add]
      fin_cases a <;> simp
    · simp only [if_neg hb, add_zero]
  simp_rw [hsub]
  rw [← integral_const_mul,
    ← integral_add_right_eq_self (μ := (selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v))
      (fun w : F × F => (η (-(c * (X 0 i * X 0 j + X 1 i * X 1 j))) : ℂ) *
        (ρ (setCol23 v X j w) * (η (w.1 * X 0 j + w.2 * X 1 j) : ℂ))) t]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  have hη : (η (u.1 * X 0 j + u.2 * X 1 j) : ℂ) =
      η (-(c * (X 0 i * X 0 j + X 1 i * X 1 j))) * η ((u + t).1 * X 0 j + (u + t).2 * X 1 j) := by
    rw [← AddChar.map_add_eq_mul, ht, Prod.fst_add, Prod.snd_add]
    congr 1; ring
  beta_reduce
  rw [hη]; ring

theorem col_k_modl (η : AddChar F ℂ) {i j k : Fin 3} (hki : k ≠ i) (hkj : k ≠ j) (c : F) (G : M23 → ℂ) (X : M23) :
    colFourier23 v η k (fun Y => modl v η i j c Y * G Y) X = modl v η i j c X * colFourier23 v η k G X := by
  simp only [colFourier23_apply, modl]
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  simp only [setCol23_apply, if_neg (Ne.symm hki), if_neg (Ne.symm hkj)]
  ring

theorem col_i_modl (η : AddChar F ℂ) {i j : Fin 3} (hij : i ≠ j) (c : F) (G : M23 → ℂ) (X : M23) :
    colFourier23 v η i (fun Y => modl v η i j c Y * G Y) X =
      colFourier23 v η i G (X * Matrix.transvection j i (-c)) := by
  simp only [colFourier23_apply, modl]
  have hset : ∀ u : F × F, setCol23 v (X * Matrix.transvection j i (-c)) i u = setCol23 v X i u := by
    intro u; ext a b
    rw [setCol23_apply, setCol23_apply]
    by_cases hb : b = i
    · rw [if_pos hb, if_pos hb]
    · rw [if_neg hb, if_neg hb, mul_transvection_apply, if_neg hb, add_zero]
  simp_rw [hset]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  have e0i : setCol23 v X i u 0 i = u.1 := by simp [setCol23_apply]
  have e1i : setCol23 v X i u 1 i = u.2 := by simp [setCol23_apply]
  have e0j : setCol23 v X i u 0 j = X 0 j := by rw [setCol23_apply, if_neg (Ne.symm hij)]
  have e1j : setCol23 v X i u 1 j = X 1 j := by rw [setCol23_apply, if_neg (Ne.symm hij)]
  have f0 : (X * Matrix.transvection j i (-c)) 0 i = X 0 i + -c * X 0 j := by rw [mul_transvection_apply, if_pos rfl]
  have f1 : (X * Matrix.transvection j i (-c)) 1 i = X 1 i + -c * X 1 j := by rw [mul_transvection_apply, if_pos rfl]
  beta_reduce
  rw [e0i, e1i, e0j, e1j, f0, f1]
  rw [mul_comm ((η _ : ℂ)) (G _), mul_assoc, ← AddChar.map_add_eq_mul]
  congr 1; ring

theorem isSchwartzBruhat_twist {i j : Fin 3} (hij : i ≠ j) (c : F) (ρ : M23 → ℂ) (hρ : IsSchwartzBruhat ρ) :
    IsSchwartzBruhat (fun Y : M23 => ρ (Y * Matrix.transvection i j c)) := by
  refine ⟨hρ.1.comp_continuous (continuous_id.matrix_mul continuous_const), ?_⟩
  refine HasCompactSupport.intro
    ((hρ.2.image (continuous_id.matrix_mul (continuous_const (y := Matrix.transvection i j (-c))))) ) fun Y hY => ?_
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  apply hY
  refine ⟨Y * Matrix.transvection i j c, hmem, ?_⟩
  show Y * Matrix.transvection i j c * Matrix.transvection i j (-c) = Y
  rw [Matrix.mul_assoc, Matrix.transvection_mul_transvection_same _ _ hij, add_neg_cancel, Matrix.transvection_zero,
    Matrix.mul_one]

theorem perm3 (η : AddChar F ℂ) (n : ℤ)
    (hηn : ∀ x : F, Valued.v x ≤ WithZero.exp n → η x = 1)
    (hηn' : ∃ x : F, Valued.v x ≤ WithZero.exp (n + 1) ∧ η x ≠ 1)
    (f : M23 → ℂ) (hf : IsSchwartzBruhat f) (a b k : Fin 3) (hab : a ≠ b) (hbk : b ≠ k) (hak : a ≠ k) :
    colFourier23 v η a (colFourier23 v η b (colFourier23 v η k f)) = matFourier23 v η f := by
  have cs := fun (j : Fin 3) (g : M23 → ℂ) (hg : IsSchwartzBruhat g) =>
    LanglandsTunnell.CubicInduction.isSchwartzBruhat_colFourier23 v η n hηn hηn' j g hg
  have csw := fun (a b : Fin 3) (h : a ≠ b) (g : M23 → ℂ) (hg : IsSchwartzBruhat g) =>
    LanglandsTunnell.CubicInduction.colFourier23_colFourier23_comm v η n hηn hηn' a b h g hg
  rw [matFourier23_eq]
  fin_cases a <;> fin_cases b <;> fin_cases k <;>
    (first | exact absurd rfl hab | exact absurd rfl hbk | exact absurd rfl hak | skip) <;> dsimp only
  · rfl
  · exact congrArg (colFourier23 v η 0) (csw 2 1 (by decide) f hf)
  · exact csw 1 0 (by decide) _ (cs 2 f hf)
  · exact (congrArg (colFourier23 v η 1) (csw 2 0 (by decide) f hf)).trans (csw 1 0 (by decide) _ (cs 2 f hf))
  · exact (csw 2 0 (by decide) _ (cs 1 f hf)).trans (congrArg (colFourier23 v η 0) (csw 2 1 (by decide) f hf))
  · exact ((congrArg (colFourier23 v η 2) (csw 1 0 (by decide) f hf)).trans (csw 2 0 (by decide) _ (cs 1 f hf))).trans
      (congrArg (colFourier23 v η 0) (csw 2 1 (by decide) f hf))

end TransvTwist

open TransvTwist in
theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (η : AddChar (v.adicCompletion ℚ) ℂ) (n : ℤ)
    (hηn : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp n → η x = 1)
    (hηn' : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (n + 1) ∧ η x ≠ 1)
    (ρ : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) → ℂ) (hρ : IsSchwartzBruhat ρ)
    (i j : Fin 3) (hij : i ≠ j) (c : v.adicCompletion ℚ) (X : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ)) :
    matFourier23 v η (fun Y => ρ (Y * Matrix.transvection i j c)) X =
      matFourier23 v η ρ (X * Matrix.transvection j i (-c)) := by
  classical
  obtain ⟨k, hki, hkj⟩ : ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by
    revert hij; fin_cases i <;> fin_cases j <;> decide
  have hρT := TransvTwist.isSchwartzBruhat_twist v hij c ρ hρ

  rw [← TransvTwist.perm3 v η n hηn hηn' _ hρT i k j hki.symm hkj hij,
    ← TransvTwist.perm3 v η n hηn hηn' ρ hρ i k j hki.symm hkj hij]
  have h1 : colFourier23 v η j (fun Y => ρ (Y * Matrix.transvection i j c)) =
      fun X => TransvTwist.modl v η i j c X * colFourier23 v η j ρ X :=
    funext fun X => TransvTwist.col_j_twist v η hij c ρ X
  have h2 : colFourier23 v η k (fun X => TransvTwist.modl v η i j c X * colFourier23 v η j ρ X) =
      fun X => TransvTwist.modl v η i j c X * colFourier23 v η k (colFourier23 v η j ρ) X :=
    funext fun X => TransvTwist.col_k_modl v η hki hkj c _ X
  rw [h1, h2, TransvTwist.col_i_modl v η hij c]

end S_LanglandsTunnell_CubicInduction_matFourier23_comp_mul_transvection_eq
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_matFourier23_comp_mul_transvection_eq (solution)
