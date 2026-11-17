-- Prove2me | solution 1 for N25.diamondField_U25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:58:05.152206+00:00
-- url     : https://prove2.me/submissions/e00f402c-d6fa-47fa-8119-4c48e2b9851d

import Mathlib
import Theorems.Thm_N25_U25C_eq_mk
import Definitions.Def_N25_Units
import Theorems.Thm_N25_unitSeries25_mem
import Definitions.Def_N25_UnitAnalytic
import Definitions.Def_N25_Endgame
import Theorems.Thm_N25_unitAnalytic25_A13
import Theorems.Thm_N25_unitNumeratorForm25
import Theorems.Thm_N25_unitDenominatorForm25
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Theorems.Thm_N25_unitDenominatorSeries25_ne_zero
import Definitions.Def_N25_UnitSeries
import Theorems.Thm_N25_unitNumerator25_slash
import Theorems.Thm_N25_GammaH25GL_period_one
import Definitions.Def_N25
import Theorems.Thm_N25_exists_forget_algEquiv_action
import Theorems.Thm_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero
import Theorems.Thm_ModularCurve_diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

open ModularCurve CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace N25

private theorem integral_neg {k : ℤ} (F : ModularForm GammaH25GL k) (p : PowerSeries ℤ)
    (h : IsIntegralQExp F p) : IsIntegralQExp ((-F : ModularForm GammaH25GL k) : UpperHalfPlane → ℂ) (-p) := by
  have ha := ModularFormClass.analyticAt_cuspFunction_zero F one_pos GammaH25GL_period_one
  unfold IsIntegralQExp at h ⊢
  rw [map_neg, h]
  simpa only [FunLike.coe_neg] using (UpperHalfPlane.qExpansion_neg ha).symm

private theorem intSeries_neg (K : Type*) [Field K] (p : PowerSeries ℤ) :
    intSeriesC K (-p) = -intSeriesC K p := by
  simp [intSeriesC]

private theorem denominator_slash (G : ModularForm GammaH25GL 36)
    (hG : ∀ τ : UpperHalfPlane, G τ = ModularForm.discriminant τ ^ 3)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    ((G : UpperHalfPlane → ℂ) ∣[(36 : ℤ)] (A : GL (Fin 2) ℝ)) = G := by
  let D : ModularForm 𝒮ℒ 12 := CuspForm.toModularFormₗ CuspForm.discriminant
  let F : ModularForm 𝒮ℒ 36 := (D.mul D).mul D
  have hF (τ : UpperHalfPlane) : F τ = ModularForm.discriminant τ ^ 3 := by
    change (ModularForm.discriminant τ * ModularForm.discriminant τ) *
      ModularForm.discriminant τ = ModularForm.discriminant τ ^ 3
    ring
  have he : (G : UpperHalfPlane → ℂ) = (F : UpperHalfPlane → ℂ) :=
    funext fun τ => (hG τ).trans (hF τ).symm
  rw [he]
  exact F.slash_action_eq' (A : GL (Fin 2) ℝ) ⟨A, rfl⟩

private theorem chosen_normalizer_U25 (i : Fin 5) :
    let ρa := (exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero ℚ 25 N25.H25).choose
    let A : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
      ⟨!![13,1;25,2], by norm_num [Matrix.det_fin_two]⟩
    let T : Gamma0 25 := ⟨A, by
      apply Gamma0_mem.mpr
      change ((25 : ℤ) : ZMod 25) = 0
      decide⟩
    ρa T (U25 i) = if i=2 then U25 (i-1) else -U25 (i-1) := by
  classical
  let ρa := (exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero ℚ 25 N25.H25).choose
  let A : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
    ⟨!![13,1;25,2], by norm_num [Matrix.det_fin_two]⟩
  let T : Gamma0 25 := ⟨A, by
    apply Gamma0_mem.mpr
    change ((25 : ℤ) : ZMod 25) = 0
    decide⟩
  have hs := (exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero ℚ 25 N25.H25).choose_spec.2.2.2
  obtain ⟨F, hFval, hF⟩ := unitNumeratorForm25 i
  obtain ⟨Fp, hFpval, hFp⟩ := unitNumeratorForm25 (i-1)
  obtain ⟨G, hGval, hG⟩ := unitDenominatorForm25
  let F1 : ModularForm GammaH25GL 36 := if i=2 then Fp else -Fp
  let p1 : PowerSeries ℤ := if i=2 then unitNumeratorSeries25 (i-1) else -unitNumeratorSeries25 (i-1)
  have hF1 : IsIntegralQExp F1 p1 := by
    by_cases hi : i=2
    · simpa only [F1, p1, if_pos hi] using hFp
    · simpa only [F1, p1, if_neg hi] using integral_neg Fp (unitNumeratorSeries25 (i-1)) hFp
  have hcov (τ : UpperHalfPlane) : unitAnalytic25 i (A • τ) =
      if i=2 then unitAnalytic25 (i-1) τ else -unitAnalytic25 (i-1) τ := by
    have h := unitAnalytic25_A13 i τ
    have heps : (![-1,-1,1,-1,-1] : Fin 5 → ℂ) i = if i=2 then 1 else -1 := by
      fin_cases i <;> norm_num <;> decide
    change unitAnalytic25 i (A • τ) = (![-1,-1,1,-1,-1] : Fin 5 → ℂ) i * unitAnalytic25 (i-1) τ at h
    rw [heps] at h
    split_ifs at h ⊢ <;> simpa using h
  have hslash : ((F : UpperHalfPlane → ℂ) ∣[(36 : ℤ)] (A : GL (Fin 2) ℝ)) =
      (fun τ : UpperHalfPlane => ModularForm.discriminant τ ^ 3 * unitAnalytic25 i (A • τ)) := by
    rw [funext hFval]
    exact unitNumerator25_slash i A
  have hff : (F1 : UpperHalfPlane → ℂ) = (1 : ℂ) •
      ((F : UpperHalfPlane → ℂ) ∣[(36 : ℤ)] ((T : Matrix.SpecialLinearGroup (Fin 2) ℤ) : GL (Fin 2) ℝ)) := by
    rw [one_smul, hslash]
    funext τ
    rw [hcov τ]
    by_cases hi : i=2
    · simpa only [F1, if_pos hi] using hFpval τ
    · simp only [F1, if_neg hi]
      change -(Fp τ) = ModularForm.discriminant τ ^ 3 * (-unitAnalytic25 (i-1) τ)
      rw [hFpval τ]
      ring
  have hgg : (G : UpperHalfPlane → ℂ) = (1 : ℂ) •
      ((G : UpperHalfPlane → ℂ) ∣[(36 : ℤ)] ((T : Matrix.SpecialLinearGroup (Fin 2) ℤ) : GL (Fin 2) ℝ)) := by
    rw [one_smul, denominator_slash G hGval A]
  have hden := unitDenominatorSeries25_ne_zero ℚ
  have h := hs T F G F1 G 1 one_ne_zero hF hG hF1 hG hff hgg hden hden
  change ((ρa T (⟨unitSeries25 ℚ i, unitSeries25_mem ℚ i⟩ : N25.Endgame.FQ) : N25.Endgame.FQ) : LaurentSeries ℚ) =
    intSeriesC ℚ p1 / intSeriesC ℚ unitDenominatorSeries25 at h
  rw [← U25C_eq_mk] at h
  by_cases hi : i=2
  · simp only [if_pos hi]
    rw [show U25 (i-1) = ⟨unitSeries25 ℚ (i-1), unitSeries25_mem ℚ (i-1)⟩ from U25C_eq_mk ℚ (i-1)]
    apply Subtype.ext
    change ((ρa T (U25 i) : N25.Endgame.FQ) : LaurentSeries ℚ) = unitSeries25 ℚ (i-1)
    simpa only [p1, if_pos hi, unitSeries25] using h
  · simp only [if_neg hi]
    rw [show U25 (i-1) = ⟨unitSeries25 ℚ (i-1), unitSeries25_mem ℚ (i-1)⟩ from U25C_eq_mk ℚ (i-1)]
    apply Subtype.ext
    change ((ρa T (U25 i) : N25.Endgame.FQ) : LaurentSeries ℚ) = -unitSeries25 ℚ (i-1)
    simpa only [p1, if_neg hi, intSeries_neg, neg_div, unitSeries25] using h

/-- The literal geometric label-thirteen diamond acts on the coefficient-
embedded rational units by their exact signed cyclic predecessor. -/
theorem _root_.solution (i : Fin 5) :
    let ε : Fin 5 → N25.Endgame.FG := ![-1,-1,1,-1,-1]
    diamondAutHBar 25 N25.H25 (ZMod.unitOfCoprime 13 (by decide))
        (N25.Endgame.emb25 (U25 i)) =
      ε i * N25.Endgame.emb25 (U25 (i-1)) := by
  classical
  let ε : Fin 5 → N25.Endgame.FG := ![-1,-1,1,-1,-1]
  let ρa := (exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero ℚ 25 N25.H25).choose
  let A : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
    ⟨!![13,1;25,2], by norm_num [Matrix.det_fin_two]⟩
  let T : Gamma0 25 := ⟨A, by
    apply Gamma0_mem.mpr
    change ((25 : ℤ) : ZMod 25) = 0
    decide⟩
  have hp := (exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero ℚ 25 N25.H25).choose_spec
  obtain ⟨ρ, hρeval⟩ := N25.exists_forget_algEquiv_action
    (algebra := SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ (CohCarrier.GammaH 25 N25.H25))) ρa
  have hρH : ∀ C : Gamma0 25, (C : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ CohCarrier.GammaH 25 N25.H25 →
      ρ C = 1 := by
    intro C hC
    ext x
    rw [hρeval, hp.1 C hC]
    rfl
  have hcmp := diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply 25 N25.H25 ρ hρH (by
    intro C k f g f1 g1 pf pg pf1 pg1 c hc hf hg hf1 hg1 hff hgg hg0 hg10
    have he := congrArg (fun x : N25.Endgame.FQ => (x : LaurentSeries ℚ))
      (hρeval C ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩)
    exact he.trans (hp.2.2.2 C f g f1 g1 c hc hf hg hf1 hg1 hff hgg hg0 hg10))
    (ZMod.unitOfCoprime 13 (by decide)) T (by decide) (U25 i)
  have hrat : ρ T (U25 i) = if i=2 then U25 (i-1) else -U25 (i-1) :=
    (hρeval T (U25 i)).trans (chosen_normalizer_U25 i)
  have hemb : diamondAutHBar 25 N25.H25 (ZMod.unitOfCoprime 13 (by decide))
      (N25.Endgame.emb25 (U25 i)) =
      if i=2 then N25.Endgame.emb25 (U25 (i-1)) else -N25.Endgame.emb25 (U25 (i-1)) := by
    apply Subtype.ext
    by_cases hi : i=2
    · simp only [if_pos hi] at hrat ⊢
      exact hcmp.trans (congrArg (coeffEmb (AlgebraicClosure ℚ))
        (congrArg (fun x : N25.Endgame.FQ => (x : LaurentSeries ℚ)) hrat))
    · simp only [if_neg hi] at hrat ⊢
      have hc := hcmp.trans (congrArg (coeffEmb (AlgebraicClosure ℚ))
        (congrArg (fun x : N25.Endgame.FQ => (x : LaurentSeries ℚ)) hrat))
      change _ = coeffEmb (AlgebraicClosure ℚ) (-(U25 (i-1) : LaurentSeries ℚ)) at hc
      change _ = -(coeffEmb (AlgebraicClosure ℚ) (U25 (i-1) : LaurentSeries ℚ))
      exact hc.trans (map_neg _ _)
  have heps : ε i = if i=2 then 1 else -1 := by fin_cases i <;> norm_num [ε] <;> decide
  change diamondAutHBar 25 N25.H25 (ZMod.unitOfCoprime 13 (by decide))
    (N25.Endgame.emb25 (U25 i)) = ε i * N25.Endgame.emb25 (U25 (i-1))
  rw [hemb, heps]
  by_cases hi : i=2 <;> simp [hi]

end N25
