-- Prove2me | solution 1 for ModularCurve.exists_isBigO_slash_realizeOf_mul_deriv_realizeOf_of_forall_ordDifferential_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/b10ac99d-a70e-59f4-85fc-7985c665a293

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_ModularCurve_CanonicalDivisorUniformizer
import Theorems.Thm_ModularCurve_exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_realizeOf_eq_div
import Theorems.Thm_AlgebraicCurve_Place_exists_of_orderMap
import Theorems.Thm_ModularCurve_jqModC_eq_qExpansion_E4_cube_div_discriminant
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_isBigO_slash_realizeOf_mul_deriv_realizeOf_of_forall_ordDifferential_nonneg

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false

noncomputable section

open UpperHalfPlane Filter Function
open scoped MatrixGroups Topology Manifold ModularForm Pointwise

namespace ModularCurve
p2m_export "ModularCurve" "realizeOf laurentBaseChange realize constantCoeff_jNum qExpFunctionFieldC jqModC exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC realizeOf_eq_div jqModC_eq_qExpansion_E4_cube_div_discriminant"
namespace CuspDecayOfAux
p2m_open "ModularCurve"

def wd (Γ : Subgroup SL(2, ℤ)) : ℕ := Γ.normalCore.index

scoped instance wd_neZero (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] : NeZero (wd Γ) :=
  ⟨Subgroup.FiniteIndex.index_ne_zero⟩

theorem wd_pos (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] : (0 : ℝ) < wd Γ := by
  exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (wd Γ))

theorem conj_T_zpow_mem (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (σ : SL(2, ℤ)) :
    σ * ModularGroup.T ^ (wd Γ : ℤ) * σ⁻¹ ∈ Γ := by
  have h1 : ModularGroup.T ^ (wd Γ : ℤ) ∈ Γ.normalCore := by
    rw [zpow_natCast]
    exact Subgroup.pow_index_mem Γ.normalCore ModularGroup.T
  have h2 : σ * ModularGroup.T ^ (wd Γ : ℤ) * σ⁻¹ ∈ Γ.normalCore :=
    (Subgroup.normalCore_normal Γ).conj_mem _ h1 σ
  exact Subgroup.normalCore_le Γ h2

theorem coe_eq_mapGL (γ : SL(2, ℤ)) : (γ : GL (Fin 2) ℝ) = Matrix.SpecialLinearGroup.mapGL ℝ γ := rfl

theorem mapGL_T_zpow (N : ℕ) :
    Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ (N : ℤ)) =
      Matrix.GeneralLinearGroup.upperRightHom (N : ℝ) := by
  have hmat : ((ModularGroup.T ^ (N : ℤ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![1, (N : ℤ); 0, 1] := ModularGroup.coe_T_zpow (N : ℤ)
  rw [Units.ext_iff]
  have hval : (↑(Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ (N : ℤ))) : Matrix (Fin 2) (Fin 2) ℝ) =
      (!![1, (N : ℤ); 0, 1]).map (Int.cast : ℤ → ℝ) := by
    rw [← hmat]; rfl
  rw [hval]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.GeneralLinearGroup.upperRightHom]

theorem natCast_mem_strictPeriods_translate (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (σ : SL(2, ℤ)) :
    (wd Γ : ℝ) ∈ Subgroup.strictPeriods
      (ConjAct.toConjAct ((σ : GL (Fin 2) ℝ))⁻¹ • ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) := by
  rw [Subgroup.mem_strictPeriods_iff, map_inv, Subgroup.mem_inv_pointwise_smul_iff,
    ConjAct.toConjAct_smul, ← mapGL_T_zpow (wd Γ), coe_eq_mapGL, ← map_inv, ← map_mul, ← map_mul]
  exact Subgroup.mem_map_of_mem _ (conj_T_zpow_mem Γ σ)

section Presentations

variable {Γ : Subgroup SL(2, ℤ)} [hTΓ : Fact (ModularGroup.T ∈ Γ)]

abbrev qL {k : ℤ} (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) : LaurentSeries ℂ :=
  ((qExpansion 1 (f : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)

structure Pres (Γ : Subgroup SL(2, ℤ)) (x : LaurentSeries ℂ) where
  k : ℤ
  g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k
  h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k
  h_ne : h ≠ 0
  eq : x * qL h = qL g

theorem one_mem_strictPeriods (Γ : Subgroup SL(2, ℤ)) [hTΓ : Fact (ModularGroup.T ∈ Γ)] :
    (1 : ℝ) ∈ ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff]
  refine ⟨ModularGroup.T, hTΓ.out, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ModularGroup.T, Matrix.GeneralLinearGroup.upperRightHom_apply]

private theorem _root_.ModularCurve.CuspDecayOfAux.coe_eq_zero_iff {k : ℤ} (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) :
    (f : ℍ → ℂ) = 0 ↔ f = 0 := by
  constructor
  · intro h
    exact DFunLike.coe_injective (h.trans (ModularForm.coe_zero).symm)
  · rintro rfl; rfl

p2m_export "ModularCurve.CuspDecayOfAux" "coe_eq_zero_iff"

theorem qL_ne_zero {k : ℤ} (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hf : f ≠ 0) :
    qL f ≠ 0 := by
  intro h
  apply hf
  rw [← ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods Γ)]
  apply (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ))
  simpa [qL] using h

theorem qL_zero {k : ℤ} : qL (0 : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) = 0 := by
  simp [qL, UpperHalfPlane.qExpansion_zero]

theorem qL_mul {a b : ℤ} (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) a)
    (g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) b) : qL (f.mul g) = qL f * qL g := by
  simp only [qL, ModularForm.coe_mul,
    ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods Γ), PowerSeries.coe_mul]

theorem qL_add {a : ℤ} (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) a) :
    qL (f + g) = qL f + qL g := by
  simp only [qL, ModularForm.coe_add,
    ModularForm.qExpansion_add one_pos (one_mem_strictPeriods Γ), PowerSeries.coe_add]

theorem qL_one : qL (1 : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 0) = 1 := by
  simp only [qL, ModularForm.qExpansion_one, PowerSeries.coe_one]

theorem qL_const (c : ℂ) :
    qL (c • (1 : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 0)) = algebraMap ℂ (LaurentSeries ℂ) c := by
  rw [qL, ModularForm.IsGLPos.coe_smul,
    ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods Γ), ModularForm.qExpansion_one,
    Algebra.smul_def, mul_one, HahnSeries.algebraMap_apply']

theorem mul_ne_zero_of_ne_zero {a b : ℤ} (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) a)
    (g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) b) (hf : f ≠ 0) (hg : g ≠ 0) :
    f.mul g ≠ 0 := by
  intro hfg
  have h1 : qL (f.mul g) = 0 := by rw [hfg, qL_zero]
  rw [qL_mul] at h1
  exact (mul_ne_zero (qL_ne_zero f hf) (qL_ne_zero g hg)) h1

theorem one_ne_zero' : (1 : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 0) ≠ 0 := by
  intro h
  have h1 : qL (1 : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 0) = 0 := by rw [h, qL_zero]
  rw [qL_one] at h1
  exact one_ne_zero h1

abbrev Pres.mul {x y : LaurentSeries ℂ} (P : Pres Γ x) (Q : Pres Γ y) : Pres Γ (x * y) where
  k := P.k + Q.k
  g := P.g.mul Q.g
  h := P.h.mul Q.h
  h_ne := mul_ne_zero_of_ne_zero P.h Q.h P.h_ne Q.h_ne
  eq := by
    rw [qL_mul, qL_mul, ← P.eq, ← Q.eq]; ring

abbrev Pres.add {x y : LaurentSeries ℂ} (P : Pres Γ x) (Q : Pres Γ y) : Pres Γ (x + y) where
  k := P.k + Q.k
  g := P.g.mul Q.h + P.h.mul Q.g
  h := P.h.mul Q.h
  h_ne := mul_ne_zero_of_ne_zero P.h Q.h P.h_ne Q.h_ne
  eq := by
    rw [qL_add, qL_mul, qL_mul, qL_mul, ← P.eq, ← Q.eq]; ring

theorem algebraMap_laurentSeries_eq_C (c : ℂ) :
    algebraMap ℂ (LaurentSeries ℂ) c = HahnSeries.C c := by
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq, HahnSeries.ofPowerSeries_C]

abbrev Pres.const (Γ : Subgroup SL(2, ℤ)) [Fact (ModularGroup.T ∈ Γ)] (c : ℂ) : Pres Γ (algebraMap ℂ (LaurentSeries ℂ) c) where
  k := 0
  g := c • (1 : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 0)
  h := 1
  h_ne := one_ne_zero'
  eq := by
    rw [qL_one, mul_one, qL_const]

end Presentations

section Level

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] {k : ℤ}

def restrict {F : Type*} [FunLike F ℍ ℂ] {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℝ)} (hle : Γ₂ ≤ Γ₁)
    {k : ℤ} (f : F) [ModularFormClass F Γ₁ k] : ModularForm Γ₂ k where
  toFun := f
  slash_action_eq' γ hγ := SlashInvariantFormClass.slash_action_eq f γ (hle hγ)
  holo' := ModularFormClass.holo f
  bdd_at_cusps' hc := ModularFormClass.bdd_at_cusps f (hc.mono hle)

def translateSL (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (A : SL(2, ℤ)) :
    ModularForm (ConjAct.toConjAct ((A : GL (Fin 2) ℝ))⁻¹ •
      ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k :=
  ModularForm.translate f (A : GL (Fin 2) ℝ)

@[scoped simp] theorem coe_translateSL (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    (A : SL(2, ℤ)) : ⇑(translateSL Γ f A) = ⇑f ∣[k] A := by
  rw [translateSL, ModularForm.SL_slash]
  exact ModularForm.coe_translate f _

theorem translateSL_ne_zero (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hf : f ≠ 0)
    (A : SL(2, ℤ)) : translateSL Γ f A ≠ 0 := by
  intro h0
  apply hf
  have h1 : (⇑f ∣[k] A) = 0 := by
    rw [← coe_translateSL Γ f A, h0]; rfl
  rw [SlashAction.slash_eq_zero_iff] at h1
  exact (ModularForm.coe_eq_zero_iff f).mp h1

theorem div_slash_eq (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (σ : SL(2, ℤ)) (τ : ℍ) :
    (⇑g ∣[k] σ) τ / (⇑h ∣[k] σ) τ = g (σ • τ) / h (σ • τ) := by
  rw [ModularForm.SL_slash_apply, ModularForm.SL_slash_apply, mul_div_mul_right]
  exact zpow_ne_zero _ (denom_ne_zero _ _)

theorem apply_smul_ne_zero_of_slash_ne_zero (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    (σ : SL(2, ℤ)) {τ : ℍ} (hτ : (⇑f ∣[k] σ) τ ≠ 0) : f (σ • τ) ≠ 0 := by
  rw [ModularForm.SL_slash_apply] at hτ
  exact left_ne_zero_of_mul hτ

end Level

section CuspGeneral

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

theorem norm_qParam_lt_one' {h : ℝ} (hh : 0 < h) (τ : ℍ) : ‖Periodic.qParam h (τ : ℂ)‖ < 1 := by
  have := (Periodic.norm_qParam_lt_iff hh 0 (τ : ℂ)).mpr (by simpa using τ.im_pos)
  simpa using this

theorem eq_zero_of_cuspFunction_eventually_eq_zero {h : ℝ} (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (f : ModularForm Γ k) (hev : ∀ᶠ q in 𝓝 (0 : ℂ), cuspFunction h f q = 0) : f = 0 := by
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex f hΓ
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  have hball : AnalyticOnNhd ℂ (cuspFunction h f) (Metric.ball 0 1) :=
    (differentiableOn_cuspFunction_ball hh hper (ModularFormClass.holo f)
      (ModularFormClass.bdd_at_infty f)).analyticOnNhd Metric.isOpen_ball
  have hz := hball.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball (0 : ℂ) 1).isPreconnected (Metric.mem_ball_self one_pos) hev
  ext τ
  have hq : Periodic.qParam h (τ : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    simpa using norm_qParam_lt_one' hh τ
  have := hz hq
  rw [eq_cuspFunction τ hh.ne' hper] at this
  simpa using this

end CuspGeneral

section Cusp

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] [Fact (ModularGroup.T ∈ Γ)] {k : ℤ}

private def _root_.ModularCurve.CuspDecayOfAux.T (q : ℂ) : ℍ := ofComplex (Periodic.invQParam (wd Γ : ℝ) q)

p2m_export "ModularCurve.CuspDecayOfAux" "T"
theorem tendsto_T : Tendsto (T Γ) (𝓝[≠] 0) atImInfty :=
  tendsto_comap_im_ofComplex.comp (Periodic.invQParam_tendsto (wd_pos Γ))

theorem tendsto_qParam :
    Tendsto (fun τ : ℍ => Periodic.qParam (wd Γ : ℝ) (τ : ℂ)) atImInfty (𝓝[≠] 0) :=
  (Periodic.qParam_tendsto (wd_pos Γ)).comp tendsto_coe_atImInfty

theorem cuspFunction_eq_T (Fn : ℍ → ℂ) {q : ℂ} (hq : q ≠ 0) :
    cuspFunction (wd Γ : ℝ) Fn q = Fn (T Γ q) := by
  rw [cuspFunction, Periodic.cuspFunction_eq_of_nonzero _ _ hq]
  rfl

def Phi (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (σ : SL(2, ℤ)) : ℂ → ℂ :=
  cuspFunction (wd Γ : ℝ) (⇑f ∣[k] σ)

theorem analyticAt_Phi (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (σ : SL(2, ℤ)) :
    AnalyticAt ℂ (Phi Γ f σ) 0 :=
  ModularFormClass.analyticAt_cuspFunction_zero (translateSL Γ f σ) (wd_pos Γ)
    (natCast_mem_strictPeriods_translate Γ σ)

theorem periodic_slash (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (σ : SL(2, ℤ)) :
    Periodic ((⇑f ∣[k] σ) ∘ ofComplex) (wd Γ : ℝ) :=
  SlashInvariantFormClass.periodic_comp_ofComplex (translateSL Γ f σ)
    (natCast_mem_strictPeriods_translate Γ σ)

theorem Phi_qParam (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (σ : SL(2, ℤ)) (τ : ℍ) :
    Phi Γ f σ (Periodic.qParam (wd Γ : ℝ) (τ : ℂ)) = (⇑f ∣[k] σ) τ :=
  SlashInvariantFormClass.eq_cuspFunction (translateSL Γ f σ) τ
    (natCast_mem_strictPeriods_translate Γ σ) (wd_pos Γ).ne'

theorem Phi_eq_T (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (σ : SL(2, ℤ)) {q : ℂ}
    (hq : q ≠ 0) : Phi Γ f σ q = (⇑f ∣[k] σ) (T Γ q) :=
  cuspFunction_eq_T Γ _ hq

theorem Phi_zero (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (σ : SL(2, ℤ)) :
    Phi Γ f σ 0 = valueAtInfty (⇑f ∣[k] σ) :=
  cuspFunction_apply_zero (wd_pos Γ) (analyticAt_Phi Γ f σ) (periodic_slash Γ f σ)

theorem Phi_eventually_ne_zero (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hf : f ≠ 0)
    (σ : SL(2, ℤ)) : ∀ᶠ q in 𝓝[≠] (0 : ℂ), Phi Γ f σ q ≠ 0 := by
  rcases (analyticAt_Phi Γ f σ).eventually_eq_zero_or_eventually_ne_zero with hev | hev
  · exact absurd (eq_zero_of_cuspFunction_eventually_eq_zero (wd_pos Γ)
      (natCast_mem_strictPeriods_translate Γ σ) (translateSL Γ f σ) hev) (translateSL_ne_zero Γ f hf σ)
  · exact hev

theorem meromorphicOrderAt_Phi_ne_top (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : f ≠ 0) (σ : SL(2, ℤ)) : meromorphicOrderAt (Phi Γ f σ) 0 ≠ ⊤ :=
  (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
    (analyticAt_Phi Γ f σ).meromorphicAt).mpr (Phi_eventually_ne_zero Γ f hf σ)

theorem eventually_slash_ne_zero (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hf : f ≠ 0)
    (σ : SL(2, ℤ)) : ∀ᶠ τ in atImInfty, (⇑f ∣[k] σ) τ ≠ 0 := by
  filter_upwards [(tendsto_qParam Γ).eventually (Phi_eventually_ne_zero Γ f hf σ)] with τ hτ
  rwa [Phi_qParam] at hτ

theorem eventually_apply_smul_ne_zero (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : f ≠ 0) (σ : SL(2, ℤ)) : ∀ᶠ τ in atImInfty, f (σ • τ) ≠ 0 :=
  (eventually_slash_ne_zero Γ f hf σ).mono fun _ hτ => apply_smul_ne_zero_of_slash_ne_zero Γ f σ hτ

def F (x : LaurentSeries ℂ) (σ : SL(2, ℤ)) : ℂ → ℂ :=
  cuspFunction (wd Γ : ℝ) (fun τ : ℍ => realizeOf Γ x (σ • τ))

theorem F_eq_T (x : LaurentSeries ℂ) (σ : SL(2, ℤ)) {q : ℂ} (hq : q ≠ 0) :
    F Γ x σ q = realizeOf Γ x (σ • T Γ q) :=
  cuspFunction_eq_T Γ _ hq

theorem realize_smul_eventuallyEq {x : LaurentSeries ℂ} (P : Pres Γ x) (σ : SL(2, ℤ)) :
    ∀ᶠ τ in atImInfty, realizeOf Γ x (σ • τ) = P.g (σ • τ) / P.h (σ • τ) :=
  (eventually_apply_smul_ne_zero Γ P.h P.h_ne σ).mono fun τ hτ =>
    ModularCurve.realizeOf_eq_div Γ Fact.out P.g P.h x P.eq (σ • τ) hτ

theorem F_eventuallyEq {x : LaurentSeries ℂ} (P : Pres Γ x) (σ : SL(2, ℤ)) :
    F Γ x σ =ᶠ[𝓝[≠] 0] fun q => Phi Γ P.g σ q / Phi Γ P.h σ q := by
  filter_upwards [(tendsto_T Γ).eventually (realize_smul_eventuallyEq Γ P σ),
    self_mem_nhdsWithin] with q hq hq0
  have hq0' : q ≠ 0 := hq0
  rw [F_eq_T Γ _ _ hq0', hq, Phi_eq_T Γ _ _ hq0', Phi_eq_T Γ _ _ hq0', div_slash_eq]

theorem meromorphicAt_F {x : LaurentSeries ℂ} (P : Pres Γ x) (σ : SL(2, ℤ)) :
    MeromorphicAt (F Γ x σ) 0 :=
  ((analyticAt_Phi Γ P.g σ).meromorphicAt.div (analyticAt_Phi Γ P.h σ).meromorphicAt).congr
    (F_eventuallyEq Γ P σ).symm

theorem meromorphicOrderAt_F_eq {x : LaurentSeries ℂ} (P : Pres Γ x) (σ : SL(2, ℤ)) :
    ∃ m : ℤ, 0 ≤ m ∧ meromorphicOrderAt (Phi Γ P.h σ) 0 = m ∧
      meromorphicOrderAt (F Γ x σ) 0 =
        meromorphicOrderAt (Phi Γ P.g σ) 0 + ((-m : ℤ) : WithTop ℤ) := by
  have hh := meromorphicOrderAt_Phi_ne_top Γ P.h P.h_ne σ
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hh
  have hm0 : 0 ≤ m := by
    have := (analyticAt_Phi Γ P.h σ).meromorphicOrderAt_nonneg
    rw [← hm] at this
    exact_mod_cast this
  refine ⟨m, hm0, hm.symm, ?_⟩
  rw [meromorphicOrderAt_congr (F_eventuallyEq Γ P σ)]
  have hdiv : (fun q => Phi Γ P.g σ q / Phi Γ P.h σ q) = Phi Γ P.g σ * (Phi Γ P.h σ)⁻¹ := by
    ext q; simp [div_eq_mul_inv]
  rw [hdiv, meromorphicOrderAt_mul (analyticAt_Phi Γ P.g σ).meromorphicAt
    (analyticAt_Phi Γ P.h σ).meromorphicAt.inv, meromorphicOrderAt_inv, ← hm]
  rfl

theorem F_mul_eventuallyEq {x y : LaurentSeries ℂ} (P : Pres Γ x) (Q : Pres Γ y) (σ : SL(2, ℤ)) :
    F Γ (x * y) σ =ᶠ[𝓝[≠] 0] F Γ x σ * F Γ y σ := by
  filter_upwards [(tendsto_T Γ).eventually (realize_smul_eventuallyEq Γ (P.mul Q) σ),
    (tendsto_T Γ).eventually (realize_smul_eventuallyEq Γ P σ),
    (tendsto_T Γ).eventually (realize_smul_eventuallyEq Γ Q σ), self_mem_nhdsWithin]
    with q h1 h2 h3 hq0
  have hq : q ≠ 0 := hq0
  rw [Pi.mul_apply, F_eq_T Γ _ _ hq, F_eq_T Γ _ _ hq, F_eq_T Γ _ _ hq, h2, h3, h1]
  rw [ModularForm.coe_mul, ModularForm.coe_mul, Pi.mul_apply, Pi.mul_apply, mul_div_mul_comm]

theorem F_add_eventuallyEq {x y : LaurentSeries ℂ} (P : Pres Γ x) (Q : Pres Γ y) (σ : SL(2, ℤ)) :
    F Γ (x + y) σ =ᶠ[𝓝[≠] 0] F Γ x σ + F Γ y σ := by
  filter_upwards [(tendsto_T Γ).eventually (realize_smul_eventuallyEq Γ (P.add Q) σ),
    (tendsto_T Γ).eventually (realize_smul_eventuallyEq Γ P σ),
    (tendsto_T Γ).eventually (realize_smul_eventuallyEq Γ Q σ),
    (tendsto_T Γ).eventually (eventually_apply_smul_ne_zero Γ P.h P.h_ne σ),
    (tendsto_T Γ).eventually (eventually_apply_smul_ne_zero Γ Q.h Q.h_ne σ),
    self_mem_nhdsWithin] with q h1 h2 h3 hP hQ hq0
  have hq : q ≠ 0 := hq0
  rw [Pi.add_apply, F_eq_T Γ _ _ hq, F_eq_T Γ _ _ hq, F_eq_T Γ _ _ hq, h2, h3, h1]
  rw [ModularForm.coe_add, Pi.add_apply, ModularForm.coe_mul, ModularForm.coe_mul,
    ModularForm.coe_mul, Pi.mul_apply, Pi.mul_apply, Pi.mul_apply, div_add_div _ _ hP hQ,
    mul_comm ((P.h : ℍ → ℂ) (σ • T Γ q)) ((Q.g : ℍ → ℂ) (σ • T Γ q))]

theorem F_const_eventuallyEq (c : ℂ) (σ : SL(2, ℤ)) :
    F Γ (algebraMap ℂ (LaurentSeries ℂ) c) σ =ᶠ[𝓝[≠] 0] fun _ => c := by
  filter_upwards [(tendsto_T Γ).eventually (realize_smul_eventuallyEq Γ (Pres.const Γ c) σ),
    self_mem_nhdsWithin] with q h1 hq0
  have hq : q ≠ 0 := hq0
  rw [F_eq_T Γ _ _ hq, h1, ModularForm.IsGLPos.coe_smul, ModularForm.one_coe_eq_one]
  simp

abbrev CF (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) : Type :=
  ↥(laurentBaseChange ℂ F₀)

variable {F₀ : IntermediateField ℚ (LaurentSeries ℚ)} [hF₀ : Fact (F₀ = qExpFunctionFieldC ℚ Γ)]

def pres (x : CF F₀) : Pres Γ (x : LaurentSeries ℂ) :=
  let E := ModularCurve.exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC
    Γ Fact.out (x : LaurentSeries ℂ) (hF₀.out ▸ x.2)
  ⟨E.choose, E.choose_spec.choose, E.choose_spec.choose_spec.choose,
    E.choose_spec.choose_spec.choose_spec.1, E.choose_spec.choose_spec.choose_spec.2⟩

def nu (σ : SL(2, ℤ)) (x : CF F₀) : WithTop ℤ :=
  meromorphicOrderAt (F Γ (x : LaurentSeries ℂ) σ) 0

theorem meromorphicAt_F' (σ : SL(2, ℤ)) (x : CF F₀) :
    MeromorphicAt (F Γ (x : LaurentSeries ℂ) σ) 0 :=
  meromorphicAt_F Γ (pres Γ x) σ

theorem nu_mul (σ : SL(2, ℤ)) (x y : CF F₀) : nu Γ σ (x * y) = nu Γ σ x + nu Γ σ y := by
  show meromorphicOrderAt (F Γ ((x : LaurentSeries ℂ) * (y : LaurentSeries ℂ)) σ) 0 = _
  rw [meromorphicOrderAt_congr (F_mul_eventuallyEq Γ (pres Γ x) (pres Γ y) σ),
    meromorphicOrderAt_mul (meromorphicAt_F' Γ σ x) (meromorphicAt_F' Γ σ y)]
  rfl

theorem nu_add (σ : SL(2, ℤ)) (x y : CF F₀) : min (nu Γ σ x) (nu Γ σ y) ≤ nu Γ σ (x + y) := by
  show _ ≤ meromorphicOrderAt (F Γ ((x : LaurentSeries ℂ) + (y : LaurentSeries ℂ)) σ) 0
  rw [meromorphicOrderAt_congr (F_add_eventuallyEq Γ (pres Γ x) (pres Γ y) σ)]
  exact meromorphicOrderAt_add (meromorphicAt_F' Γ σ x) (meromorphicAt_F' Γ σ y)

theorem nu_algebraMap (σ : SL(2, ℤ)) (c : ℂ) (hc : c ≠ 0) : nu Γ σ (algebraMap ℂ (CF F₀) c) = 0 := by
  classical
  show meromorphicOrderAt (F Γ (algebraMap ℂ (LaurentSeries ℂ) c) σ) 0 = 0
  rw [meromorphicOrderAt_congr (F_const_eventuallyEq Γ c σ), meromorphicOrderAt_const, if_neg hc]

theorem nu_eq_top_iff (σ : SL(2, ℤ)) (x : CF F₀) : nu Γ σ x = ⊤ ↔ x = 0 := by
  obtain ⟨m, hm0, hmh, hnu⟩ := meromorphicOrderAt_F_eq Γ (pres Γ x) σ
  constructor
  · intro hx
    unfold nu at hx
    rw [hx] at hnu
    have hg : meromorphicOrderAt (Phi Γ (pres Γ x).g σ) 0 = ⊤ := by
      rcases WithTop.add_eq_top.mp hnu.symm with h | h
      · exact h
      · exact absurd h WithTop.coe_ne_top
    have hg0 : (pres Γ x).g = 0 := by
      by_contra hne
      exact meromorphicOrderAt_Phi_ne_top Γ _ hne σ hg
    have heq := (pres Γ x).eq
    rw [hg0, qL_zero] at heq
    have hx0 : (x : LaurentSeries ℂ) = 0 :=
      (mul_eq_zero.mp heq).resolve_right (qL_ne_zero _ (pres Γ x).h_ne)
    exact_mod_cast hx0
  · rintro rfl
    have heq : (0 : LaurentSeries ℂ) * qL (pres Γ (0 : CF F₀)).h = qL (pres Γ (0 : CF F₀)).g :=
      (pres Γ (0 : CF F₀)).eq
    rw [zero_mul] at heq
    have hg0 : (pres Γ (0 : CF F₀)).g = 0 := by
      by_contra hne
      exact qL_ne_zero _ hne heq.symm
    unfold nu
    rw [hnu, hg0]
    have h0 : meromorphicOrderAt
        (Phi Γ (0 : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (pres Γ (0 : CF F₀)).k) σ) 0 = ⊤ := by
      apply meromorphicOrderAt_eq_top_iff.mpr
      filter_upwards [self_mem_nhdsWithin] with q hq
      have hq' : q ≠ 0 := hq
      rw [Phi_eq_T Γ _ _ hq', ModularForm.coe_zero, SlashAction.zero_slash]
      rfl
    rw [h0, top_add]

theorem nu_ne_top (σ : SL(2, ℤ)) {x : CF F₀} (hx : x ≠ 0) : nu Γ σ x ≠ ⊤ :=
  fun h => hx ((nu_eq_top_iff Γ σ x).mp h)

theorem nu_one (σ : SL(2, ℤ)) : nu Γ σ (1 : CF F₀) = 0 := by
  rw [← map_one (algebraMap ℂ (CF F₀))]
  exact nu_algebraMap Γ σ 1 one_ne_zero

theorem y_ne_zero {y : CF F₀} (hy : (y : LaurentSeries ℂ) = jqModC ℂ) : y ≠ 0 := by
  intro h
  have h1 : ((y : CF F₀) : LaurentSeries ℂ) = 0 := by rw [h]; rfl
  have h3 := congrArg (fun z : LaurentSeries ℂ => z.coeff (-1)) (h1.symm.trans hy)
  simp only [HahnSeries.coeff_zero] at h3
  have h4 : (jqModC ℂ).coeff (-1) = 1 := by
    rw [show (jqModC ℂ).coeff (-1) = (jqModC ℂ).coeff (((0 : ℕ) : ℤ) + (-1)) by simp, jqModC,
      HahnSeries.coeff_single_mul_add, one_mul, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_jNum, map_one]
  rw [h4] at h3
  exact zero_ne_one h3

theorem le_SL :
    ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ :=
  Subgroup.map_le_range _ _

def G₁ : ModularForm 𝒮ℒ 12 := ModularForm.mcast (by decide) (ModularForm.E₄.pow 3)

def G : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 12 := restrict (le_SL Γ) G₁

def H : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 12 :=
  restrict (le_SL Γ) CuspForm.discriminant

theorem coe_G : ((G Γ : ModularForm _ 12) : ℍ → ℂ) = fun τ => ModularForm.E₄ τ ^ 3 := by
  show ((ModularForm.E₄.pow 3 : ModularForm 𝒮ℒ (3 * 4)) : ℍ → ℂ) = _
  rw [ModularForm.coe_pow]
  rfl

theorem coe_H : ((H Γ : ModularForm _ 12) : ℍ → ℂ) = ModularForm.discriminant := rfl

theorem H_ne_zero : H Γ ≠ 0 := by
  intro h
  have := congrArg (fun f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 12 => (f : ℍ → ℂ) I) h
  simp only [coe_H, ModularForm.coe_zero, Pi.zero_apply] at this
  exact ModularForm.discriminant_ne_zero I this

theorem qL_G : qL (G Γ) =
    ((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 := by
  have hc : ((G Γ : ModularForm _ 12) : ℍ → ℂ) =
      ((ModularForm.E₄.pow 3 : ModularForm 𝒮ℒ (3 * 4)) : ℍ → ℂ) := rfl
  have h : qExpansion 1 ((G Γ : ModularForm _ 12) : ℍ → ℂ) =
      (qExpansion 1 (ModularForm.E₄ : ℍ → ℂ)) ^ 3 := by
    rw [hc, ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  rw [qL, h, PowerSeries.coe_pow]

theorem qL_H : qL (H Γ) =
    ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) :=
  rfl

def PX {y : CF F₀} (hy : (y : LaurentSeries ℂ) = jqModC ℂ) : Pres Γ ((y : CF F₀) : LaurentSeries ℂ) where
  k := 12
  g := G Γ
  h := H Γ
  h_ne := H_ne_zero Γ
  eq := by
    rw [hy, jqModC_eq_qExpansion_E4_cube_div_discriminant, qL_G, ← qL_H Γ]
    exact div_mul_cancel₀ _ (qL_ne_zero (H Γ) (H_ne_zero Γ))

theorem slash_G (σ : SL(2, ℤ)) : ⇑(G Γ) ∣[(12 : ℤ)] σ = ⇑(G Γ) :=
  SlashInvariantFormClass.slash_action_eq (G₁ : ModularForm 𝒮ℒ 12)
    (Matrix.SpecialLinearGroup.mapGL ℝ σ) ⟨σ, rfl⟩

theorem slash_H (σ : SL(2, ℤ)) : ⇑(H Γ) ∣[(12 : ℤ)] σ = ⇑(H Γ) :=
  SlashInvariantFormClass.slash_action_eq CuspForm.discriminant
    (Matrix.SpecialLinearGroup.mapGL ℝ σ) ⟨σ, rfl⟩

theorem tendsto_E4_atImInfty : Tendsto (fun τ : ℍ => ModularForm.E₄ τ) atImInfty (𝓝 1) := by
  have hana := ModularFormClass.analyticAt_cuspFunction_zero ModularForm.E₄ one_pos
    one_mem_strictPeriods_SL
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄
    one_mem_strictPeriods_SL
  have h0 : cuspFunction 1 (⇑ModularForm.E₄) 0 = 1 := by
    rw [cuspFunction_apply_zero one_pos hana hper, ← qExpansion_coeff_zero one_pos hana hper]
    exact EisensteinSeries.E_qExpansion_coeff_zero (by norm_num) (by decide)
  have h1 := hana.continuousAt.tendsto.comp (qParam_tendsto_atImInfty one_pos)
  rw [h0] at h1
  refine h1.congr fun τ => ?_
  simp only [comp_apply]
  exact SlashInvariantFormClass.eq_cuspFunction ModularForm.E₄ τ one_mem_strictPeriods_SL
    one_ne_zero

theorem tendsto_G_atImInfty : Tendsto (⇑(G Γ)) atImInfty (𝓝 1) := by
  rw [coe_G]
  simpa using (tendsto_E4_atImInfty).pow 3

theorem tendsto_H_atImInfty : Tendsto (⇑(H Γ)) atImInfty (𝓝 0) :=
  ModularForm.discriminant_isZeroAtImInfty

theorem Phi_G_zero (σ : SL(2, ℤ)) : Phi Γ (G Γ) σ 0 = 1 := by
  rw [Phi_zero, slash_G]
  exact (tendsto_G_atImInfty Γ).limUnder_eq

theorem Phi_H_zero (σ : SL(2, ℤ)) : Phi Γ (H Γ) σ 0 = 0 := by
  rw [Phi_zero, slash_H]
  exact (tendsto_H_atImInfty Γ).limUnder_eq

theorem meromorphicOrderAt_Phi_G (σ : SL(2, ℤ)) : meromorphicOrderAt (Phi Γ (G Γ) σ) 0 = 0 := by
  apply (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero
    (analyticAt_Phi Γ (G Γ) σ).meromorphicAt).mp
  refine ⟨1, one_ne_zero, ?_⟩
  have h := ((analyticAt_Phi Γ (G Γ) σ).continuousAt.tendsto).mono_left
    (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℂ)))
  rwa [Phi_G_zero] at h

theorem meromorphicOrderAt_Phi_H_pos (σ : SL(2, ℤ)) :
    0 < meromorphicOrderAt (Phi Γ (H Γ) σ) 0 := by
  apply (tendsto_zero_iff_meromorphicOrderAt_pos (analyticAt_Phi Γ (H Γ) σ).meromorphicAt).mp
  have h := ((analyticAt_Phi Γ (H Γ) σ).continuousAt.tendsto).mono_left
    (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℂ)))
  rwa [Phi_H_zero] at h

theorem nu_X_neg (σ : SL(2, ℤ)) {y : CF F₀} (hy : (y : LaurentSeries ℂ) = jqModC ℂ) :
    nu Γ σ y < 0 := by
  obtain ⟨m, hm0, hmH, hF⟩ := meromorphicOrderAt_F_eq Γ (PX Γ hy) σ
  have hpos := meromorphicOrderAt_Phi_H_pos Γ σ
  have hmH' : meromorphicOrderAt (Phi Γ (H Γ) σ) 0 = m := hmH
  rw [hmH', ← WithTop.coe_zero, WithTop.coe_lt_coe] at hpos
  have hG : meromorphicOrderAt (Phi Γ (PX Γ hy).g σ) 0 = 0 := meromorphicOrderAt_Phi_G Γ σ
  show meromorphicOrderAt (F Γ ((y : CF F₀) : LaurentSeries ℂ) σ) 0 < 0
  rw [hF, hG, zero_add, ← WithTop.coe_zero, WithTop.coe_lt_coe]
  omega

theorem exists_nu_pos (σ : SL(2, ℤ)) {y : CF F₀} (hy : (y : LaurentSeries ℂ) = jqModC ℂ) :
    ∃ x : CF F₀, 0 < nu Γ σ x ∧ nu Γ σ x ≠ ⊤ := by
  have hy0 : y ≠ 0 := y_ne_zero hy
  have hXt := nu_ne_top Γ σ hy0
  have hneg := nu_X_neg Γ σ hy
  refine ⟨y⁻¹, ?_, nu_ne_top Γ σ (inv_ne_zero hy0)⟩
  have hsum : nu Γ σ y⁻¹ + nu Γ σ y = 0 := by
    rw [← nu_mul, inv_mul_cancel₀ hy0, nu_one]
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hXt
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (nu_ne_top Γ σ (inv_ne_zero hy0))
  rw [← hm, ← hn, ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_eq_coe] at hsum
  rw [← hm, ← WithTop.coe_zero, WithTop.coe_lt_coe] at hneg
  rw [← hn, ← WithTop.coe_zero, WithTop.coe_lt_coe]
  omega

theorem exists_place (σ : SL(2, ℤ)) {y : CF F₀} (hy : (y : LaurentSeries ℂ) = jqModC ℂ) :
    ∃ (P : AlgebraicCurve.Place ℂ (CF F₀)) (e : ℕ), 0 < e ∧
      (∀ x, x ∈ P.toValuationSubring ↔ 0 ≤ nu Γ σ x) ∧
      ∀ x, x ≠ 0 → nu Γ σ x = (((e : ℤ) * P.ord x : ℤ) : WithTop ℤ) :=
  AlgebraicCurve.Place.exists_of_orderMap (nu Γ σ) (nu_eq_top_iff Γ σ) (nu_mul Γ σ) (nu_add Γ σ)
    (fun c hc => nu_algebraMap Γ σ c hc) (exists_nu_pos Γ σ hy)

end Cusp

section Interior

variable (Γ : Subgroup SL(2, ℤ)) [Fact (ModularGroup.T ∈ Γ)]

theorem analyticAt_comp_ofComplex {k : ℤ} (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    (τ : ℍ) : AnalyticAt ℂ (fun z : ℂ => (f : ℍ → ℂ) (ofComplex z)) (τ : ℂ) := by
  have hf : DifferentiableOn ℂ ((f : ℍ → ℂ) ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp (ModularFormClass.holo f)
  exact hf.analyticAt (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)

abbrev rz (x : LaurentSeries ℂ) : ℂ → ℂ := fun w : ℂ => realizeOf Γ x (ofComplex w)

theorem differentiableAt_rz {x : LaurentSeries ℂ} (P : Pres Γ x) (w : ℍ) (hw : P.h w ≠ 0) :
    DifferentiableAt ℂ (rz Γ x) (w : ℂ) := by
  have hg := analyticAt_comp_ofComplex Γ P.g w
  have hh := analyticAt_comp_ofComplex Γ P.h w
  have hw' : (fun z : ℂ => (P.h : ℍ → ℂ) (ofComplex z)) (w : ℂ) ≠ 0 := by
    simpa only [ofComplex_apply] using hw
  refine (hg.div hh hw').differentiableAt.congr_of_eventuallyEq ?_
  filter_upwards [hh.continuousAt.eventually_ne hw'] with z hz
  exact ModularCurve.realizeOf_eq_div Γ Fact.out P.g P.h x P.eq (ofComplex z) hz

def moeb (g : SL(2, ℤ)) (z : ℂ) : ℂ := ((g • ofComplex z : ℍ) : ℂ)

theorem moeb_coe (g : SL(2, ℤ)) (τ : ℍ) : moeb g τ = ((g • τ : ℍ) : ℂ) := by
  simp [moeb, ofComplex_apply]

theorem hasDerivAt_moeb (γ : SL(2, ℤ)) (τ : ℍ) :
    HasDerivAt (moeb γ) (denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) ↑τ ^ (-2 : ℤ)) ↑τ := by
  set G : GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.mapGL ℝ γ with hG
  have hdet : (G : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hG, Matrix.SpecialLinearGroup.det_mapGL,
      Units.val_one]
  have hpos : (0:ℝ) < (G : Matrix (Fin 2) (Fin 2) ℝ).det := by rw [hdet]; norm_num
  have h1 := (UpperHalfPlane.hasStrictDerivAt_smul hpos τ).hasDerivAt
  have h2 : (fun z : ℂ => ((G • ofComplex z : ℍ) : ℂ)) = moeb γ := by
    funext z
    rw [moeb, MulAction.compHom_smul_def]
  rw [h2] at h1
  refine h1.congr_deriv ?_
  rw [hdet]
  push_cast
  rw [zpow_neg, one_div]
  norm_cast

theorem slash_two_apply (f : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    (f ∣[(2 : ℤ)] γ) τ =
      f (γ • τ) * denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) ↑τ ^ (-2 : ℤ) :=
  ModularForm.SL_slash_apply f γ τ

theorem hasDerivAt_qParam (h : ℝ) (z : ℂ) :
    HasDerivAt (Periodic.qParam h) (Periodic.qParam h z * (2 * ↑Real.pi * Complex.I / h)) z := by
  have qdiff : HasStrictDerivAt (Periodic.qParam h)
      (Periodic.qParam h z * (2 * ↑Real.pi * Complex.I / h)) z := by
    have := (((hasStrictDerivAt_id z).const_mul (2 * ↑Real.pi * Complex.I)).div_const (h : ℂ)).cexp
    simp only [id_eq, mul_one] at this
    exact this
  exact qdiff.hasDerivAt

end Interior

section CuspDeriv

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] [Fact (ModularGroup.T ∈ Γ)] {k : ℤ}

theorem differentiableAt_Phi (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (σ : SL(2, ℤ))
    {q : ℂ} (hq : ‖q‖ < 1) : DifferentiableAt ℂ (Phi Γ f σ) q :=
  ModularFormClass.differentiableAt_cuspFunction (translateSL Γ f σ) (wd_pos Γ)
    (natCast_mem_strictPeriods_translate Γ σ) hq

abbrev Psi {x : LaurentSeries ℂ} (P : Pres Γ x) (σ : SL(2, ℤ)) : ℂ → ℂ :=
  fun q => Phi Γ P.g σ q / Phi Γ P.h σ q

theorem differentiableAt_Psi {x : LaurentSeries ℂ} (P : Pres Γ x) (σ : SL(2, ℤ)) {q : ℂ}
    (hq : ‖q‖ < 1) (h0 : Phi Γ P.h σ q ≠ 0) : DifferentiableAt ℂ (Psi Γ P σ) q :=
  (differentiableAt_Phi Γ P.g σ hq).div (differentiableAt_Phi Γ P.h σ hq) h0

theorem slash_eventuallyEq {a x : LaurentSeries ℂ} (Pa : Pres Γ a) (Px : Pres Γ x)
    (σ : SL(2, ℤ)) :
    ∀ᶠ τ : ℍ in atImInfty,
      ((fun τ : ℍ => realizeOf Γ a τ * deriv (rz Γ x) τ) ∣[(2 : ℤ)] σ) τ =
        (2 * ↑Real.pi * Complex.I / (wd Γ : ℂ)) * Periodic.qParam (wd Γ : ℝ) (τ : ℂ) *
          (Psi Γ Pa σ (Periodic.qParam (wd Γ : ℝ) (τ : ℂ)) *
            deriv (Psi Γ Px σ) (Periodic.qParam (wd Γ : ℝ) (τ : ℂ))) := by
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp (eventually_apply_smul_ne_zero Γ Px.h Px.h_ne σ)
  have hevA : ∀ᶠ τ : ℍ in atImInfty, A < τ.im :=
    (atImInfty_mem _).mpr ⟨A + 1, fun z hz => lt_of_lt_of_le (lt_add_one A) hz⟩
  filter_upwards [hevA, realize_smul_eventuallyEq Γ Pa σ] with τ hτA hτa
  have hxτ : Px.h (σ • τ) ≠ 0 := hA τ hτA.le

  have hd : DifferentiableAt ℂ (rz Γ x) (moeb σ τ) := by
    rw [moeb_coe]; exact differentiableAt_rz Γ Px (σ • τ) hxτ
  have h1 : HasDerivAt (rz Γ x ∘ moeb σ)
      (deriv (rz Γ x) ((σ • τ : ℍ) : ℂ) *
        denom (Matrix.SpecialLinearGroup.mapGL ℝ σ) ↑τ ^ (-2 : ℤ)) τ := by
    have h := hd.hasDerivAt.comp (τ : ℂ) (hasDerivAt_moeb σ τ)
    rwa [moeb_coe] at h

  have hPhi : Phi Γ Px.h σ (Periodic.qParam (wd Γ : ℝ) (τ : ℂ)) ≠ 0 := by
    rw [Phi_qParam, ModularForm.SL_slash_apply]
    exact mul_ne_zero hxτ (zpow_ne_zero _ (denom_ne_zero _ _))
  have hPsi : DifferentiableAt ℂ (Psi Γ Px σ) (Periodic.qParam (wd Γ : ℝ) (τ : ℂ)) :=
    differentiableAt_Psi Γ Px σ (norm_qParam_lt_one' (wd_pos Γ) τ) hPhi
  have h2 : HasDerivAt (Psi Γ Px σ ∘ Periodic.qParam (wd Γ : ℝ))
      (deriv (Psi Γ Px σ) (Periodic.qParam (wd Γ : ℝ) (τ : ℂ)) *
        (Periodic.qParam (wd Γ : ℝ) (τ : ℂ) * (2 * ↑Real.pi * Complex.I / (wd Γ : ℝ)))) τ :=
    hPsi.hasDerivAt.comp (τ : ℂ) (hasDerivAt_qParam (wd Γ : ℝ) τ)

  have h12 : (rz Γ x ∘ moeb σ) =ᶠ[𝓝 (τ : ℂ)] (Psi Γ Px σ ∘ Periodic.qParam (wd Γ : ℝ)) := by
    have hopen : IsOpen {z : ℂ | max A 0 < z.im} :=
      isOpen_lt continuous_const Complex.continuous_im
    have hmem : (τ : ℂ) ∈ {z : ℂ | max A 0 < z.im} := by
      show max A 0 < (τ : ℂ).im
      rw [UpperHalfPlane.coe_im]
      exact max_lt hτA τ.im_pos
    filter_upwards [hopen.mem_nhds hmem] with z hz
    have hz0 : 0 < z.im := lt_of_le_of_lt (le_max_right A 0) hz
    have hzA : A < z.im := lt_of_le_of_lt (le_max_left A 0) hz
    have hoc : ofComplex z = ⟨z, hz0⟩ := ofComplex_apply_of_im_pos hz0
    have hz' : Px.h (σ • ofComplex z) ≠ 0 := hA (ofComplex z) (by rw [hoc]; exact hzA.le)
    have hcoe : ((ofComplex z : ℍ) : ℂ) = z := by rw [hoc]
    simp only [comp_apply, rz, moeb, ofComplex_apply, Psi]
    rw [ModularCurve.realizeOf_eq_div Γ Fact.out Px.g Px.h x Px.eq (σ • ofComplex z) hz',
      ← div_slash_eq Γ Px.g Px.h σ (ofComplex z), ← Phi_qParam Γ Px.g σ (ofComplex z),
      ← Phi_qParam Γ Px.h σ (ofComplex z), hcoe]

  have hderiv : deriv (rz Γ x) ((σ • τ : ℍ) : ℂ) *
      denom (Matrix.SpecialLinearGroup.mapGL ℝ σ) ↑τ ^ (-2 : ℤ) =
        deriv (Psi Γ Px σ) (Periodic.qParam (wd Γ : ℝ) (τ : ℂ)) *
          (Periodic.qParam (wd Γ : ℝ) (τ : ℂ) * (2 * ↑Real.pi * Complex.I / (wd Γ : ℝ))) :=
    (h1.congr_of_eventuallyEq h12.symm).unique h2

  rw [slash_two_apply, mul_assoc, hderiv, hτa, ← div_slash_eq Γ Pa.g Pa.h σ τ,
    ← Phi_qParam Γ Pa.g σ τ, ← Phi_qParam Γ Pa.h σ τ]
  push_cast
  ring

theorem isBigO_qParam :
    (fun τ : ℍ => (2 * ↑Real.pi * Complex.I / (wd Γ : ℂ)) * Periodic.qParam (wd Γ : ℝ) (τ : ℂ))
      =O[atImInfty] fun τ : ℍ => Real.exp (-(2 * Real.pi / (wd Γ : ℝ)) * τ.im) := by
  refine (Asymptotics.IsBigO.of_bound' ?_).const_mul_left _
  refine Filter.Eventually.of_forall fun τ => ?_
  rw [Periodic.norm_qParam, UpperHalfPlane.coe_im, Real.norm_eq_abs, Real.abs_exp]
  apply le_of_eq
  congr 1
  ring

end CuspDeriv

section Germs

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] [Fact (ModularGroup.T ∈ Γ)]
  {F₀ : IntermediateField ℚ (LaurentSeries ℚ)} [hF₀ : Fact (F₀ = qExpFunctionFieldC ℚ Γ)]

theorem eventually_eventuallyEq_nhds {f g : ℂ → ℂ} {τ : ℂ} (h : f =ᶠ[𝓝[≠] τ] g) :
    ∀ᶠ z in 𝓝[≠] τ, f =ᶠ[𝓝 z] g := by
  rw [Filter.EventuallyEq, eventually_nhdsWithin_iff] at h
  rw [eventually_nhdsWithin_iff]
  filter_upwards [h.eventually_nhds] with z hz hzτ
  filter_upwards [hz, eventually_ne_nhds (Set.mem_compl_singleton_iff.mp hzτ)] with w hw hwτ
  exact hw (Set.mem_compl_singleton_iff.mpr hwτ)

theorem deriv_eventuallyEq {f g : ℂ → ℂ} {τ : ℂ} (h : f =ᶠ[𝓝[≠] τ] g) :
    deriv f =ᶠ[𝓝[≠] τ] deriv g :=
  (eventually_eventuallyEq_nhds h).mono fun _ hz => hz.deriv_eq

theorem exists_analyticAt_eventuallyEq {f : ℂ → ℂ} (hf : MeromorphicAt f 0)
    (h : 0 ≤ meromorphicOrderAt f 0) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G 0 ∧ f =ᶠ[𝓝[≠] (0 : ℂ)] G := by
  by_cases htop : meromorphicOrderAt f 0 = ⊤
  · exact ⟨fun _ => 0, analyticAt_const, meromorphicOrderAt_eq_top_iff.mp htop⟩
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp htop
    have hn0 : (0 : ℤ) ≤ n := by
      rw [← hn] at h
      exact_mod_cast h
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn0
    obtain ⟨g, hg, -, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).mp hn.symm
    refine ⟨fun z => z ^ m * g z, (analyticAt_id.pow m).mul hg, ?_⟩
    filter_upwards [hfg] with z hz
    rw [hz, sub_zero, zpow_natCast, smul_eq_mul]

theorem eventually_differentiableAt_F (σ : SL(2, ℤ)) (y : CF F₀) :
    ∀ᶠ q in 𝓝[≠] (0 : ℂ), DifferentiableAt ℂ (F Γ (y : LaurentSeries ℂ) σ) q := by
  have hball : ∀ᶠ q in 𝓝[≠] (0 : ℂ), ‖q‖ < 1 := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0 : ℂ) one_pos)]
      with q hq
    rwa [mem_ball_zero_iff] at hq
  filter_upwards [eventually_eventuallyEq_nhds (F_eventuallyEq Γ (pres Γ y) σ),
    Phi_eventually_ne_zero Γ (pres Γ y).h (pres Γ y).h_ne σ, hball] with q hq hh hq1
  exact (differentiableAt_Psi Γ (pres Γ y) σ hq1 hh).congr_of_eventuallyEq hq

theorem F_coe_mul (σ : SL(2, ℤ)) (x y : CF F₀) :
    F Γ ((x * y : CF F₀) : LaurentSeries ℂ) σ =ᶠ[𝓝[≠] (0 : ℂ)]
      fun q => F Γ (x : LaurentSeries ℂ) σ q * F Γ (y : LaurentSeries ℂ) σ q := by
  show F Γ ((x : LaurentSeries ℂ) * (y : LaurentSeries ℂ)) σ =ᶠ[𝓝[≠] (0 : ℂ)]
    F Γ (x : LaurentSeries ℂ) σ * F Γ (y : LaurentSeries ℂ) σ
  exact F_mul_eventuallyEq Γ (pres Γ x) (pres Γ y) σ

theorem F_coe_add (σ : SL(2, ℤ)) (x y : CF F₀) :
    F Γ ((x + y : CF F₀) : LaurentSeries ℂ) σ =ᶠ[𝓝[≠] (0 : ℂ)]
      fun q => F Γ (x : LaurentSeries ℂ) σ q + F Γ (y : LaurentSeries ℂ) σ q := by
  show F Γ ((x : LaurentSeries ℂ) + (y : LaurentSeries ℂ)) σ =ᶠ[𝓝[≠] (0 : ℂ)]
    F Γ (x : LaurentSeries ℂ) σ + F Γ (y : LaurentSeries ℂ) σ
  exact F_add_eventuallyEq Γ (pres Γ x) (pres Γ y) σ

theorem F_coe_const (σ : SL(2, ℤ)) (c : ℂ) :
    F Γ ((algebraMap ℂ (CF F₀) c : CF F₀) : LaurentSeries ℂ) σ =ᶠ[𝓝[≠] (0 : ℂ)] fun _ => c :=
  F_const_eventuallyEq Γ c σ

theorem F_coe_smul (σ : SL(2, ℤ)) (c : ℂ) (y : CF F₀) :
    F Γ ((c • y : CF F₀) : LaurentSeries ℂ) σ =ᶠ[𝓝[≠] (0 : ℂ)]
      fun q => c * F Γ (y : LaurentSeries ℂ) σ q := by
  rw [Algebra.smul_def]
  filter_upwards [F_coe_mul Γ σ (algebraMap ℂ (CF F₀) c) y, F_coe_const (F₀ := F₀) Γ σ c]
    with q h1 h2
  rw [h1, h2]

@[nolint unusedArguments]
def Gm (_Γ : Subgroup SL(2, ℤ)) (_F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (_σ : SL(2, ℤ)) : Type :=
  Filter.Germ (𝓝[≠] (0 : ℂ)) ℂ

scoped instance instCommRingGm (σ : SL(2, ℤ)) : CommRing (Gm Γ F₀ σ) :=
  inferInstanceAs (CommRing (Filter.Germ (𝓝[≠] (0 : ℂ)) ℂ))

variable (F₀) in

def germ (σ : SL(2, ℤ)) (f : ℂ → ℂ) : Gm Γ F₀ σ := ((f : Filter.Germ (𝓝[≠] (0 : ℂ)) ℂ) : Gm Γ F₀ σ)

theorem germ_eq_iff {σ : SL(2, ℤ)} {f g : ℂ → ℂ} :
    germ Γ F₀ σ f = germ Γ F₀ σ g ↔ f =ᶠ[𝓝[≠] (0 : ℂ)] g := Filter.Germ.coe_eq

theorem germ_mul (σ : SL(2, ℤ)) (f g : ℂ → ℂ) :
    germ Γ F₀ σ (fun z => f z * g z) = germ Γ F₀ σ f * germ Γ F₀ σ g := rfl

theorem germ_add (σ : SL(2, ℤ)) (f g : ℂ → ℂ) :
    germ Γ F₀ σ (fun z => f z + g z) = germ Γ F₀ σ f + germ Γ F₀ σ g := rfl

theorem germ_zero (σ : SL(2, ℤ)) : germ Γ F₀ σ (fun _ => (0 : ℂ)) = 0 := rfl

theorem germ_one (σ : SL(2, ℤ)) : germ Γ F₀ σ (fun _ => (1 : ℂ)) = 1 := rfl

def φ (σ : SL(2, ℤ)) : CF F₀ →+* Gm Γ F₀ σ where
  toFun y := germ Γ F₀ σ (F Γ (y : LaurentSeries ℂ) σ)
  map_one' := by
    rw [← germ_one, germ_eq_iff]
    have h := F_coe_const (F₀ := F₀) Γ σ 1
    rwa [map_one] at h
  map_mul' x y := by
    rw [← germ_mul, germ_eq_iff]
    exact F_coe_mul Γ σ x y
  map_zero' := by
    rw [← germ_zero, germ_eq_iff]
    have h := F_coe_const (F₀ := F₀) Γ σ 0
    rwa [map_zero] at h
  map_add' x y := by
    rw [← germ_add, germ_eq_iff]
    exact F_coe_add Γ σ x y

scoped instance algebraCF (σ : SL(2, ℤ)) : Algebra (CF F₀) (Gm Γ F₀ σ) := (φ Γ σ).toAlgebra

scoped instance algebraC (σ : SL(2, ℤ)) : Algebra ℂ (Gm Γ F₀ σ) :=
  ((φ Γ σ).comp (algebraMap ℂ (CF F₀))).toAlgebra

scoped instance isScalarTower (σ : SL(2, ℤ)) : IsScalarTower ℂ (CF F₀) (Gm Γ F₀ σ) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

theorem smul_def_CF (σ : SL(2, ℤ)) (y : CF F₀) (m : Gm Γ F₀ σ) :
    y • m = germ Γ F₀ σ (F Γ (y : LaurentSeries ℂ) σ) * m := rfl

theorem smul_def_C (σ : SL(2, ℤ)) (c : ℂ) (m : Gm Γ F₀ σ) :
    c • m = germ Γ F₀ σ (F Γ ((algebraMap ℂ (CF F₀) c : CF F₀) : LaurentSeries ℂ) σ) * m := rfl

def δ (σ : SL(2, ℤ)) : Derivation ℂ (CF F₀) (Gm Γ F₀ σ) where
  toFun y := germ Γ F₀ σ (deriv (F Γ (y : LaurentSeries ℂ) σ))
  map_add' x y := by
    rw [← germ_add, germ_eq_iff]
    filter_upwards [deriv_eventuallyEq (F_coe_add Γ σ x y), eventually_differentiableAt_F Γ σ x,
      eventually_differentiableAt_F Γ σ y] with z hz hx hy
    rw [hz, deriv_fun_add hx hy]
  map_smul' c x := by
    simp only [RingHom.id_apply]
    rw [smul_def_C, ← germ_mul, germ_eq_iff]
    filter_upwards [deriv_eventuallyEq (F_coe_smul Γ σ c x), F_coe_const (F₀ := F₀) Γ σ c]
      with z h1 h2
    rw [h1, h2, deriv_const_mul_field]
  map_one_eq_zero' := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [← germ_zero, germ_eq_iff]
    have h1 := F_coe_const (F₀ := F₀) Γ σ 1
    rw [map_one] at h1
    filter_upwards [deriv_eventuallyEq h1] with z hz
    rw [hz, deriv_const]
  leibniz' x y := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [smul_def_CF, smul_def_CF, ← germ_mul, ← germ_mul, ← germ_add, germ_eq_iff]
    filter_upwards [deriv_eventuallyEq (F_coe_mul Γ σ x y), eventually_differentiableAt_F Γ σ x,
      eventually_differentiableAt_F Γ σ y] with z hz hx hy
    rw [hz, deriv_fun_mul hx hy]
    ring

theorem δ_apply (σ : SL(2, ℤ)) (y : CF F₀) :
    δ Γ σ y = germ Γ F₀ σ (deriv (F Γ (y : LaurentSeries ℂ) σ)) := rfl

theorem eventuallyEq_of_smul_D_eq_smul_D (σ : SL(2, ℤ)) {a x c π : CF F₀}
    (h : a • KaehlerDifferential.D ℂ (CF F₀) x = c • KaehlerDifferential.D ℂ (CF F₀) π) :
    (fun q => F Γ (a : LaurentSeries ℂ) σ q * deriv (F Γ (x : LaurentSeries ℂ) σ) q)
      =ᶠ[𝓝[≠] (0 : ℂ)]
      fun q => F Γ (c : LaurentSeries ℂ) σ q * deriv (F Γ (π : LaurentSeries ℂ) σ) q := by
  have h' := congrArg ((δ Γ σ).liftKaehlerDifferential) h
  rw [map_smul, map_smul, Derivation.liftKaehlerDifferential_comp_D,
    Derivation.liftKaehlerDifferential_comp_D, δ_apply, δ_apply, smul_def_CF, smul_def_CF,
    ← germ_mul, ← germ_mul, germ_eq_iff] at h'
  exact h'

end Germs

section Bounded

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] [Fact (ModularGroup.T ∈ Γ)]
  {F₀ : IntermediateField ℚ (LaurentSeries ℚ)} [hF₀ : Fact (F₀ = qExpFunctionFieldC ℚ Γ)]

set_option maxHeartbeats 16000000 in

theorem isBigO_cusp [∀ w : AlgebraicCurve.Place ℂ (CF F₀), w.DCoordGenerates]
    {y : CF F₀} (hy : (y : LaurentSeries ℂ) = jqModC ℂ) (a x : CF F₀)
    (hreg : ∀ v : AlgebraicCurve.Place ℂ (CF F₀), y ∉ v.toValuationSubring →
      0 ≤ v.ordDifferential (a • KaehlerDifferential.D ℂ (CF F₀) x))
    (σ : SL(2, ℤ)) :
    (fun q => Psi Γ (pres Γ a) σ q * deriv (Psi Γ (pres Γ x) σ) q) =O[𝓝[≠] (0 : ℂ)]
      fun _ => (1 : ℝ) := by
  obtain ⟨P, e, _he, hmem, hordP⟩ := exists_place Γ σ hy

  have hX : y ∉ P.toValuationSubring := by
    rw [hmem, not_le]
    exact nu_X_neg Γ σ hy

  obtain ⟨π, hπ0, hπ1, hdc⟩ : ∃ π : CF F₀, π ≠ 0 ∧ P.ord π = 1 ∧
      P.dCoord = KaehlerDifferential.D ℂ (CF F₀) π :=
    ⟨P.uniformizer, P.uniformizer_ne_zero, P.ord_uniformizer, P.dCoord_eq⟩

  obtain ⟨c, hac, hc⟩ : ∃ c : CF F₀,
      a • KaehlerDifferential.D ℂ (CF F₀) x = c • KaehlerDifferential.D ℂ (CF F₀) π ∧
        0 ≤ P.ord c := by
    refine ⟨P.differentialCoeff (a • KaehlerDifferential.D ℂ (CF F₀) x), ?_, ?_⟩
    · rw [← hdc]
      exact (P.differentialCoeff_smul_dCoord _).symm
    · have h := hreg P hX
      rwa [AlgebraicCurve.Place.ordDifferential] at h

  have hνc : 0 ≤ nu Γ σ c := by
    rcases eq_or_ne c 0 with h0 | h0
    · rw [(nu_eq_top_iff Γ σ _).mpr h0]
      exact le_top
    · rw [hordP _ h0, ← WithTop.coe_zero, WithTop.coe_le_coe]
      exact mul_nonneg (Int.natCast_nonneg e) hc
  have hνπ : 0 ≤ nu Γ σ π := by
    rw [hordP _ hπ0, hπ1, mul_one, ← WithTop.coe_zero, WithTop.coe_le_coe]
    exact Int.natCast_nonneg e

  obtain ⟨Gc, hGc, hFc⟩ := exists_analyticAt_eventuallyEq (meromorphicAt_F' Γ σ _) hνc
  obtain ⟨Gπ, hGπ, hFπ⟩ := exists_analyticAt_eventuallyEq (meromorphicAt_F' Γ σ _) hνπ

  have hbd : (fun q => Gc q * deriv Gπ q) =O[𝓝[≠] (0 : ℂ)] fun _ => (1 : ℝ) := by
    have hcont : ContinuousAt (fun q => Gc q * deriv Gπ q) 0 :=
      (hGc.mul hGπ.deriv).continuousAt
    exact (hcont.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one ℝ
  refine Filter.EventuallyEq.trans_isBigO ?_ hbd

  have h1 : (fun q => Psi Γ (pres Γ a) σ q * deriv (Psi Γ (pres Γ x) σ) q) =ᶠ[𝓝[≠] (0 : ℂ)]
      fun q => F Γ (a : LaurentSeries ℂ) σ q * deriv (F Γ (x : LaurentSeries ℂ) σ) q := by
    filter_upwards [F_eventuallyEq Γ (pres Γ a) σ,
      deriv_eventuallyEq (F_eventuallyEq Γ (pres Γ x) σ)] with q ha hx
    rw [ha, hx]
  have h2 := eventuallyEq_of_smul_D_eq_smul_D Γ σ hac
  have h3 : (fun q => F Γ (c : LaurentSeries ℂ) σ q * deriv (F Γ (π : LaurentSeries ℂ) σ) q)
      =ᶠ[𝓝[≠] (0 : ℂ)] fun q => Gc q * deriv Gπ q := by
    filter_upwards [hFc, deriv_eventuallyEq hFπ] with q h h'
    rw [h, h']
  exact (h1.trans h2).trans h3

set_option maxHeartbeats 16000000 in

theorem main [∀ w : AlgebraicCurve.Place ℂ (CF F₀), w.DCoordGenerates]
    {y : CF F₀} (hy : (y : LaurentSeries ℂ) = jqModC ℂ) (a x : CF F₀)
    (hreg : ∀ v : AlgebraicCurve.Place ℂ (CF F₀), y ∉ v.toValuationSubring →
      0 ≤ v.ordDifferential (a • KaehlerDifferential.D ℂ (CF F₀) x))
    (σ : SL(2, ℤ)) :
    ∃ δ : ℝ, 0 < δ ∧
      ((fun τ : ℍ => realizeOf Γ (a : LaurentSeries ℂ) τ *
          deriv (fun w : ℂ => realizeOf Γ (x : LaurentSeries ℂ) (ofComplex w)) τ)
        ∣[(2 : ℤ)] σ) =O[atImInfty] fun τ : ℍ => Real.exp (-δ * τ.im) := by
  refine ⟨2 * Real.pi / (wd Γ : ℝ), div_pos Real.two_pi_pos (wd_pos Γ), ?_⟩
  have hC := (isBigO_cusp Γ hy a x hreg σ).comp_tendsto (tendsto_qParam Γ)
  have hDC := ((isBigO_qParam Γ).mul hC).congr_right (fun _ => mul_one _)
  refine (Filter.EventuallyEq.trans_isBigO ?_ hDC)
  exact slash_eventuallyEq Γ (pres Γ a) (pres Γ x) σ

end Bounded

end ModularCurve.CuspDecayOfAux
p2m_reactivate "P2MW.S_ModularCurve_exists_isBigO_slash_realizeOf_mul_deriv_realizeOf_of_forall_ordDifferential_nonneg.ModularCurve P2MW.S_ModularCurve_exists_isBigO_slash_realizeOf_mul_deriv_realizeOf_of_forall_ordDifferential_nonneg.ModularCurve.CuspDecayOfAux"
p2m_reactivate "P2MW.S_ModularCurve_exists_isBigO_slash_realizeOf_mul_deriv_realizeOf_of_forall_ordDifferential_nonneg.ModularCurve"

set_option maxHeartbeats 16000000 in
open _root_.ModularCurve _root_.P2MW.S_ModularCurve_exists_isBigO_slash_realizeOf_mul_deriv_realizeOf_of_forall_ordDifferential_nonneg.ModularCurve ModularCurve.CuspDecayOfAux in
theorem solution
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (hF : F₀ = ModularCurve.qExpFunctionFieldC ℚ Γ)
    [∀ w : AlgebraicCurve.Place ℂ (ModularCurve.laurentBaseChange ℂ F₀), w.DCoordGenerates]
    (a x : ModularCurve.laurentBaseChange ℂ F₀)
    (y : ModularCurve.laurentBaseChange ℂ F₀) (hy : (y : LaurentSeries ℂ) = ModularCurve.jqModC ℂ)
    (hreg : ∀ v : AlgebraicCurve.Place ℂ (ModularCurve.laurentBaseChange ℂ F₀), y ∉ v.toValuationSubring →
      0 ≤ v.ordDifferential (a • KaehlerDifferential.D ℂ (ModularCurve.laurentBaseChange ℂ F₀) x))
    (σ : SL(2, ℤ)) :
    ∃ δ : ℝ, 0 < δ ∧
      ((fun τ : ℍ => ModularCurve.realizeOf Γ (a : LaurentSeries ℂ) τ *
          deriv (fun w : ℂ => ModularCurve.realizeOf Γ (x : LaurentSeries ℂ) (ofComplex w)) τ)
        ∣[(2 : ℤ)] σ) =O[atImInfty] fun τ : ℍ => Real.exp (-δ * τ.im) := by
  haveI : Fact (ModularGroup.T ∈ Γ) := ⟨hT⟩
  haveI : Fact (F₀ = ModularCurve.qExpFunctionFieldC ℚ Γ) := ⟨hF⟩
  exact main Γ hy a x hreg σ

end
p2m_reactivate "P2MW.S_ModularCurve_exists_isBigO_slash_realizeOf_mul_deriv_realizeOf_of_forall_ordDifferential_nonneg.ModularCurve P2MW.S_ModularCurve_exists_isBigO_slash_realizeOf_mul_deriv_realizeOf_of_forall_ordDifferential_nonneg.ModularCurve.CuspDecayOfAux"

end S_ModularCurve_exists_isBigO_slash_realizeOf_mul_deriv_realizeOf_of_forall_ordDifferential_nonneg
end P2MW
export P2MW.S_ModularCurve_exists_isBigO_slash_realizeOf_mul_deriv_realizeOf_of_forall_ordDifferential_nonneg (solution)
