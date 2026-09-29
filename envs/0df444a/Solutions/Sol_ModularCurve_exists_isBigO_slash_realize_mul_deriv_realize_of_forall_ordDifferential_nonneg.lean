-- Prove2me | solution 1 for ModularCurve.exists_isBigO_slash_realize_mul_deriv_realize_of_forall_ordDifferential_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/d886a5aa-8298-5308-baec-9b6f02739fc6

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionary
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_ModularCurve_CanonicalDivisorUniformizer
import Theorems.Thm_ModularCurve_exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange
import Theorems.Thm_ModularCurve_realize_eq_div
import Theorems.Thm_AlgebraicCurve_Place_exists_of_orderMap
import Theorems.Thm_ModularCurve_jqModC_eq_qExpansion_E4_cube_div_discriminant
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_isBigO_slash_realize_mul_deriv_realize_of_forall_ordDifferential_nonneg
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open UpperHalfPlane Filter Function
open scoped MatrixGroups Topology Manifold ModularForm Pointwise

namespace ModularCurve
p2m_export "ModularCurve" "realize jq coeff_jq_neg_one jq_mem modularFunctionFieldFull modularFunctionField_le_full coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange realize_eq_div jqModC_eq_qExpansion_E4_cube_div_discriminant jqModC jqModC_rat map_jqModC"
namespace CuspDecayAux
p2m_open "ModularCurve"

section Presentations

variable {N : ℕ}

abbrev qL {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) : LaurentSeries ℂ :=
  ((qExpansion 1 (f : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)

structure Pres (N : ℕ) (x : LaurentSeries ℂ) where
  k : ℤ
  g : ModularForm (CongruenceSubgroup.Gamma0 N) k
  h : ModularForm (CongruenceSubgroup.Gamma0 N) k
  h_ne : h ≠ 0
  eq : x * qL h = qL g

theorem one_mem_strictPeriods (N : ℕ) :
    (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

private theorem _root_.ModularCurve.CuspDecayAux.coe_eq_zero_iff {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) :
    (f : ℍ → ℂ) = 0 ↔ f = 0 := by
  constructor
  · intro h
    exact DFunLike.coe_injective (h.trans (ModularForm.coe_zero).symm)
  · rintro rfl; rfl

p2m_export "ModularCurve.CuspDecayAux" "coe_eq_zero_iff"

theorem qL_ne_zero {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) (hf : f ≠ 0) :
    qL f ≠ 0 := by
  intro h
  apply hf
  rw [← ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods N)]
  apply (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ))
  simpa [qL] using h

theorem qL_zero {k : ℤ} : qL (0 : ModularForm (CongruenceSubgroup.Gamma0 N) k) = 0 := by
  simp [qL, UpperHalfPlane.qExpansion_zero]

theorem qL_mul {a b : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) a)
    (g : ModularForm (CongruenceSubgroup.Gamma0 N) b) : qL (f.mul g) = qL f * qL g := by
  simp only [qL, ModularForm.coe_mul,
    ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods N), PowerSeries.coe_mul]

theorem qL_add {a : ℤ} (f g : ModularForm (CongruenceSubgroup.Gamma0 N) a) :
    qL (f + g) = qL f + qL g := by
  simp only [qL, ModularForm.coe_add,
    ModularForm.qExpansion_add one_pos (one_mem_strictPeriods N), PowerSeries.coe_add]

theorem qL_one : qL (1 : ModularForm (CongruenceSubgroup.Gamma0 N) 0) = 1 := by
  simp only [qL, ModularForm.qExpansion_one, PowerSeries.coe_one]

theorem qL_const (c : ℂ) :
    qL (c • (1 : ModularForm (CongruenceSubgroup.Gamma0 N) 0)) = algebraMap ℂ (LaurentSeries ℂ) c := by
  rw [qL, ModularForm.IsGLPos.coe_smul,
    ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods N), ModularForm.qExpansion_one,
    Algebra.smul_def, mul_one, HahnSeries.algebraMap_apply']

theorem mul_ne_zero_of_ne_zero {a b : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) a)
    (g : ModularForm (CongruenceSubgroup.Gamma0 N) b) (hf : f ≠ 0) (hg : g ≠ 0) :
    f.mul g ≠ 0 := by
  intro hfg
  have h1 : qL (f.mul g) = 0 := by rw [hfg, qL_zero]
  rw [qL_mul] at h1
  exact (mul_ne_zero (qL_ne_zero f hf) (qL_ne_zero g hg)) h1

theorem one_ne_zero' : (1 : ModularForm (CongruenceSubgroup.Gamma0 N) 0) ≠ 0 := by
  intro h
  have h1 : qL (1 : ModularForm (CongruenceSubgroup.Gamma0 N) 0) = 0 := by rw [h, qL_zero]
  rw [qL_one] at h1
  exact one_ne_zero h1

abbrev Pres.mul {x y : LaurentSeries ℂ} (P : Pres N x) (Q : Pres N y) : Pres N (x * y) where
  k := P.k + Q.k
  g := P.g.mul Q.g
  h := P.h.mul Q.h
  h_ne := mul_ne_zero_of_ne_zero P.h Q.h P.h_ne Q.h_ne
  eq := by
    rw [qL_mul, qL_mul, ← P.eq, ← Q.eq]; ring

abbrev Pres.add {x y : LaurentSeries ℂ} (P : Pres N x) (Q : Pres N y) : Pres N (x + y) where
  k := P.k + Q.k
  g := P.g.mul Q.h + P.h.mul Q.g
  h := P.h.mul Q.h
  h_ne := mul_ne_zero_of_ne_zero P.h Q.h P.h_ne Q.h_ne
  eq := by
    rw [qL_add, qL_mul, qL_mul, qL_mul, ← P.eq, ← Q.eq]; ring

theorem algebraMap_laurentSeries_eq_C (c : ℂ) :
    algebraMap ℂ (LaurentSeries ℂ) c = HahnSeries.C c := by
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq, HahnSeries.ofPowerSeries_C]

abbrev Pres.const (N : ℕ) (c : ℂ) : Pres N (algebraMap ℂ (LaurentSeries ℂ) c) where
  k := 0
  g := c • (1 : ModularForm (CongruenceSubgroup.Gamma0 N) 0)
  h := 1
  h_ne := one_ne_zero'
  eq := by
    rw [qL_one, mul_one, qL_const]

end Presentations

section Level

variable (N : ℕ) {k : ℤ}

theorem Gamma_le_Gamma0 : CongruenceSubgroup.Gamma N ≤ CongruenceSubgroup.Gamma0 N :=
  fun A hA => by
    rw [CongruenceSubgroup.Gamma0_mem]
    exact (CongruenceSubgroup.Gamma_mem.mp hA).2.2.1

def restrict {F : Type*} [FunLike F ℍ ℂ] {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (hle : Γ' ≤ Γ)
    {k : ℤ} (f : F) [ModularFormClass F Γ k] : ModularForm Γ' k where
  toFun := f
  slash_action_eq' γ hγ := SlashInvariantFormClass.slash_action_eq f γ (hle hγ)
  holo' := ModularFormClass.holo f
  bdd_at_cusps' hc := ModularFormClass.bdd_at_cusps f (hc.mono hle)

theorem Gamma_le_conj (A : SL(2, ℤ)) :
    ((CongruenceSubgroup.Gamma N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ A)⁻¹ •
        ((CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) := by
  rintro _ ⟨y, hy, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  refine ⟨A * y * A⁻¹,
    Gamma_le_Gamma0 N ((CongruenceSubgroup.Gamma_normal N).conj_mem y hy A), ?_⟩
  simp [map_mul, map_inv]

def translateSL (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) (A : SL(2, ℤ)) :
    ModularForm (CongruenceSubgroup.Gamma N) k :=
  restrict (Gamma_le_conj N A) (ModularForm.translate f (Matrix.SpecialLinearGroup.mapGL ℝ A))

@[scoped simp] theorem coe_translateSL (f : ModularForm (CongruenceSubgroup.Gamma0 N) k)
    (A : SL(2, ℤ)) : ⇑(translateSL N f A) = ⇑f ∣[k] A := rfl

theorem natCast_mem_strictPeriods_Gamma :
    (N : ℝ) ∈ (CongruenceSubgroup.Gamma N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

theorem natCast_pos [NeZero N] : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))

theorem translateSL_ne_zero (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) (hf : f ≠ 0)
    (A : SL(2, ℤ)) : translateSL N f A ≠ 0 := by
  intro h0
  apply hf
  have h1 : (⇑f ∣[k] A) = 0 := by
    rw [← coe_translateSL N f A, h0]; rfl
  rw [SlashAction.slash_eq_zero_iff] at h1
  exact (ModularForm.coe_eq_zero_iff f).mp h1

theorem div_slash_eq (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k) (σ : SL(2, ℤ)) (τ : ℍ) :
    (⇑g ∣[k] σ) τ / (⇑h ∣[k] σ) τ = g (σ • τ) / h (σ • τ) := by
  rw [ModularForm.SL_slash_apply, ModularForm.SL_slash_apply, mul_div_mul_right]
  exact zpow_ne_zero _ (denom_ne_zero _ _)

theorem apply_smul_ne_zero_of_slash_ne_zero (f : ModularForm (CongruenceSubgroup.Gamma0 N) k)
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

variable (N : ℕ) [NeZero N] {k : ℤ}

def T (q : ℂ) : ℍ := ofComplex (Periodic.invQParam (N : ℝ) q)

theorem tendsto_T : Tendsto (T N) (𝓝[≠] 0) atImInfty :=
  tendsto_comap_im_ofComplex.comp (Periodic.invQParam_tendsto (natCast_pos N))

theorem tendsto_qParam :
    Tendsto (fun τ : ℍ => Periodic.qParam (N : ℝ) (τ : ℂ)) atImInfty (𝓝[≠] 0) :=
  (Periodic.qParam_tendsto (natCast_pos N)).comp tendsto_coe_atImInfty

omit [NeZero N] in
theorem cuspFunction_eq_T (Fn : ℍ → ℂ) {q : ℂ} (hq : q ≠ 0) :
    cuspFunction (N : ℝ) Fn q = Fn (T N q) := by
  rw [cuspFunction, Periodic.cuspFunction_eq_of_nonzero _ _ hq]
  rfl

def Phi (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) (σ : SL(2, ℤ)) : ℂ → ℂ :=
  cuspFunction (N : ℝ) (⇑f ∣[k] σ)

theorem analyticAt_Phi (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) (σ : SL(2, ℤ)) :
    AnalyticAt ℂ (Phi N f σ) 0 :=
  ModularFormClass.analyticAt_cuspFunction_zero (translateSL N f σ) (natCast_pos N)
    (natCast_mem_strictPeriods_Gamma N)

omit [NeZero N] in
theorem periodic_slash (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) (σ : SL(2, ℤ)) :
    Periodic ((⇑f ∣[k] σ) ∘ ofComplex) (N : ℝ) :=
  SlashInvariantFormClass.periodic_comp_ofComplex (translateSL N f σ)
    (natCast_mem_strictPeriods_Gamma N)

theorem Phi_qParam (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) (σ : SL(2, ℤ)) (τ : ℍ) :
    Phi N f σ (Periodic.qParam (N : ℝ) (τ : ℂ)) = (⇑f ∣[k] σ) τ :=
  SlashInvariantFormClass.eq_cuspFunction (translateSL N f σ) τ
    (natCast_mem_strictPeriods_Gamma N) (natCast_pos N).ne'

omit [NeZero N] in
theorem Phi_eq_T (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) (σ : SL(2, ℤ)) {q : ℂ}
    (hq : q ≠ 0) : Phi N f σ q = (⇑f ∣[k] σ) (T N q) :=
  cuspFunction_eq_T N _ hq

theorem Phi_zero (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) (σ : SL(2, ℤ)) :
    Phi N f σ 0 = valueAtInfty (⇑f ∣[k] σ) :=
  cuspFunction_apply_zero (natCast_pos N) (analyticAt_Phi N f σ) (periodic_slash N f σ)

theorem Phi_eventually_ne_zero (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) (hf : f ≠ 0)
    (σ : SL(2, ℤ)) : ∀ᶠ q in 𝓝[≠] (0 : ℂ), Phi N f σ q ≠ 0 := by
  rcases (analyticAt_Phi N f σ).eventually_eq_zero_or_eventually_ne_zero with hev | hev
  · exact absurd (eq_zero_of_cuspFunction_eventually_eq_zero (natCast_pos N)
      (natCast_mem_strictPeriods_Gamma N) (translateSL N f σ) hev) (translateSL_ne_zero N f hf σ)
  · exact hev

theorem meromorphicOrderAt_Phi_ne_top (f : ModularForm (CongruenceSubgroup.Gamma0 N) k)
    (hf : f ≠ 0) (σ : SL(2, ℤ)) : meromorphicOrderAt (Phi N f σ) 0 ≠ ⊤ :=
  (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
    (analyticAt_Phi N f σ).meromorphicAt).mpr (Phi_eventually_ne_zero N f hf σ)

theorem eventually_slash_ne_zero (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) (hf : f ≠ 0)
    (σ : SL(2, ℤ)) : ∀ᶠ τ in atImInfty, (⇑f ∣[k] σ) τ ≠ 0 := by
  filter_upwards [(tendsto_qParam N).eventually (Phi_eventually_ne_zero N f hf σ)] with τ hτ
  rwa [Phi_qParam] at hτ

theorem eventually_apply_smul_ne_zero (f : ModularForm (CongruenceSubgroup.Gamma0 N) k)
    (hf : f ≠ 0) (σ : SL(2, ℤ)) : ∀ᶠ τ in atImInfty, f (σ • τ) ≠ 0 :=
  (eventually_slash_ne_zero N f hf σ).mono fun _ hτ => apply_smul_ne_zero_of_slash_ne_zero N f σ hτ

def F (x : LaurentSeries ℂ) (σ : SL(2, ℤ)) : ℂ → ℂ :=
  cuspFunction (N : ℝ) (fun τ : ℍ => realize N x (σ • τ))

omit [NeZero N] in
theorem F_eq_T (x : LaurentSeries ℂ) (σ : SL(2, ℤ)) {q : ℂ} (hq : q ≠ 0) :
    F N x σ q = realize N x (σ • T N q) :=
  cuspFunction_eq_T N _ hq

theorem realize_smul_eventuallyEq {x : LaurentSeries ℂ} (P : Pres N x) (σ : SL(2, ℤ)) :
    ∀ᶠ τ in atImInfty, realize N x (σ • τ) = P.g (σ • τ) / P.h (σ • τ) :=
  (eventually_apply_smul_ne_zero N P.h P.h_ne σ).mono fun τ hτ =>
    ModularCurve.realize_eq_div N P.g P.h x P.eq (σ • τ) hτ

theorem F_eventuallyEq {x : LaurentSeries ℂ} (P : Pres N x) (σ : SL(2, ℤ)) :
    F N x σ =ᶠ[𝓝[≠] 0] fun q => Phi N P.g σ q / Phi N P.h σ q := by
  filter_upwards [(tendsto_T N).eventually (realize_smul_eventuallyEq N P σ),
    self_mem_nhdsWithin] with q hq hq0
  have hq0' : q ≠ 0 := hq0
  rw [F_eq_T N _ _ hq0', hq, Phi_eq_T N _ _ hq0', Phi_eq_T N _ _ hq0', div_slash_eq]

theorem meromorphicAt_F {x : LaurentSeries ℂ} (P : Pres N x) (σ : SL(2, ℤ)) :
    MeromorphicAt (F N x σ) 0 :=
  ((analyticAt_Phi N P.g σ).meromorphicAt.div (analyticAt_Phi N P.h σ).meromorphicAt).congr
    (F_eventuallyEq N P σ).symm

theorem meromorphicOrderAt_F_eq {x : LaurentSeries ℂ} (P : Pres N x) (σ : SL(2, ℤ)) :
    ∃ m : ℤ, 0 ≤ m ∧ meromorphicOrderAt (Phi N P.h σ) 0 = m ∧
      meromorphicOrderAt (F N x σ) 0 =
        meromorphicOrderAt (Phi N P.g σ) 0 + ((-m : ℤ) : WithTop ℤ) := by
  have hh := meromorphicOrderAt_Phi_ne_top N P.h P.h_ne σ
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hh
  have hm0 : 0 ≤ m := by
    have := (analyticAt_Phi N P.h σ).meromorphicOrderAt_nonneg
    rw [← hm] at this
    exact_mod_cast this
  refine ⟨m, hm0, hm.symm, ?_⟩
  rw [meromorphicOrderAt_congr (F_eventuallyEq N P σ)]
  have hdiv : (fun q => Phi N P.g σ q / Phi N P.h σ q) = Phi N P.g σ * (Phi N P.h σ)⁻¹ := by
    ext q; simp [div_eq_mul_inv]
  rw [hdiv, meromorphicOrderAt_mul (analyticAt_Phi N P.g σ).meromorphicAt
    (analyticAt_Phi N P.h σ).meromorphicAt.inv, meromorphicOrderAt_inv, ← hm]
  rfl

theorem F_mul_eventuallyEq {x y : LaurentSeries ℂ} (P : Pres N x) (Q : Pres N y) (σ : SL(2, ℤ)) :
    F N (x * y) σ =ᶠ[𝓝[≠] 0] F N x σ * F N y σ := by
  filter_upwards [(tendsto_T N).eventually (realize_smul_eventuallyEq N (P.mul Q) σ),
    (tendsto_T N).eventually (realize_smul_eventuallyEq N P σ),
    (tendsto_T N).eventually (realize_smul_eventuallyEq N Q σ), self_mem_nhdsWithin]
    with q h1 h2 h3 hq0
  have hq : q ≠ 0 := hq0
  rw [Pi.mul_apply, F_eq_T N _ _ hq, F_eq_T N _ _ hq, F_eq_T N _ _ hq, h2, h3, h1]
  rw [ModularForm.coe_mul, ModularForm.coe_mul, Pi.mul_apply, Pi.mul_apply, mul_div_mul_comm]

theorem F_add_eventuallyEq {x y : LaurentSeries ℂ} (P : Pres N x) (Q : Pres N y) (σ : SL(2, ℤ)) :
    F N (x + y) σ =ᶠ[𝓝[≠] 0] F N x σ + F N y σ := by
  filter_upwards [(tendsto_T N).eventually (realize_smul_eventuallyEq N (P.add Q) σ),
    (tendsto_T N).eventually (realize_smul_eventuallyEq N P σ),
    (tendsto_T N).eventually (realize_smul_eventuallyEq N Q σ),
    (tendsto_T N).eventually (eventually_apply_smul_ne_zero N P.h P.h_ne σ),
    (tendsto_T N).eventually (eventually_apply_smul_ne_zero N Q.h Q.h_ne σ),
    self_mem_nhdsWithin] with q h1 h2 h3 hP hQ hq0
  have hq : q ≠ 0 := hq0
  rw [Pi.add_apply, F_eq_T N _ _ hq, F_eq_T N _ _ hq, F_eq_T N _ _ hq, h2, h3, h1]
  rw [ModularForm.coe_add, Pi.add_apply, ModularForm.coe_mul, ModularForm.coe_mul,
    ModularForm.coe_mul, Pi.mul_apply, Pi.mul_apply, Pi.mul_apply, div_add_div _ _ hP hQ,
    mul_comm ((P.h : ℍ → ℂ) (σ • T N q)) ((Q.g : ℍ → ℂ) (σ • T N q))]

theorem F_const_eventuallyEq (c : ℂ) (σ : SL(2, ℤ)) :
    F N (algebraMap ℂ (LaurentSeries ℂ) c) σ =ᶠ[𝓝[≠] 0] fun _ => c := by
  filter_upwards [(tendsto_T N).eventually (realize_smul_eventuallyEq N (Pres.const N c) σ),
    self_mem_nhdsWithin] with q h1 hq0
  have hq : q ≠ 0 := hq0
  rw [F_eq_T N _ _ hq, h1, ModularForm.IsGLPos.coe_smul, ModularForm.one_coe_eq_one]
  simp

abbrev CF (N : ℕ) [NeZero N] : Type :=
  ↥(laurentBaseChange ℂ (modularFunctionFieldFull N))

variable {N}

def pres (x : CF N) : Pres N (x : LaurentSeries ℂ) :=
  let E := ModularCurve.exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange N
    (x : LaurentSeries ℂ) x.2
  ⟨E.choose, E.choose_spec.choose, E.choose_spec.choose_spec.choose,
    E.choose_spec.choose_spec.choose_spec.1, E.choose_spec.choose_spec.choose_spec.2⟩

def nu (σ : SL(2, ℤ)) (x : CF N) : WithTop ℤ :=
  meromorphicOrderAt (F N (x : LaurentSeries ℂ) σ) 0

theorem meromorphicAt_F' (σ : SL(2, ℤ)) (x : CF N) :
    MeromorphicAt (F N (x : LaurentSeries ℂ) σ) 0 :=
  meromorphicAt_F N (pres x) σ

theorem nu_mul (σ : SL(2, ℤ)) (x y : CF N) : nu σ (x * y) = nu σ x + nu σ y := by
  show meromorphicOrderAt (F N ((x : LaurentSeries ℂ) * (y : LaurentSeries ℂ)) σ) 0 = _
  rw [meromorphicOrderAt_congr (F_mul_eventuallyEq N (pres x) (pres y) σ),
    meromorphicOrderAt_mul (meromorphicAt_F' σ x) (meromorphicAt_F' σ y)]
  rfl

theorem nu_add (σ : SL(2, ℤ)) (x y : CF N) : min (nu σ x) (nu σ y) ≤ nu σ (x + y) := by
  show _ ≤ meromorphicOrderAt (F N ((x : LaurentSeries ℂ) + (y : LaurentSeries ℂ)) σ) 0
  rw [meromorphicOrderAt_congr (F_add_eventuallyEq N (pres x) (pres y) σ)]
  exact meromorphicOrderAt_add (meromorphicAt_F' σ x) (meromorphicAt_F' σ y)

theorem nu_algebraMap (σ : SL(2, ℤ)) (c : ℂ) (hc : c ≠ 0) : nu σ (algebraMap ℂ (CF N) c) = 0 := by
  classical
  show meromorphicOrderAt (F N (algebraMap ℂ (LaurentSeries ℂ) c) σ) 0 = 0
  rw [meromorphicOrderAt_congr (F_const_eventuallyEq N c σ), meromorphicOrderAt_const, if_neg hc]

theorem nu_eq_top_iff (σ : SL(2, ℤ)) (x : CF N) : nu σ x = ⊤ ↔ x = 0 := by
  obtain ⟨m, hm0, hmh, hnu⟩ := meromorphicOrderAt_F_eq N (pres x) σ
  constructor
  · intro hx
    unfold nu at hx
    rw [hx] at hnu
    have hg : meromorphicOrderAt (Phi N (pres x).g σ) 0 = ⊤ := by
      rcases WithTop.add_eq_top.mp hnu.symm with h | h
      · exact h
      · exact absurd h WithTop.coe_ne_top
    have hg0 : (pres x).g = 0 := by
      by_contra hne
      exact meromorphicOrderAt_Phi_ne_top N _ hne σ hg
    have heq := (pres x).eq
    rw [hg0, qL_zero] at heq
    have hx0 : (x : LaurentSeries ℂ) = 0 :=
      (mul_eq_zero.mp heq).resolve_right (qL_ne_zero _ (pres x).h_ne)
    exact_mod_cast hx0
  · rintro rfl
    have heq : (0 : LaurentSeries ℂ) * qL (pres (0 : CF N)).h = qL (pres (0 : CF N)).g :=
      (pres (0 : CF N)).eq
    rw [zero_mul] at heq
    have hg0 : (pres (0 : CF N)).g = 0 := by
      by_contra hne
      exact qL_ne_zero _ hne heq.symm
    unfold nu
    rw [hnu, hg0]
    have h0 : meromorphicOrderAt
        (Phi N (0 : ModularForm (CongruenceSubgroup.Gamma0 N) (pres (0 : CF N)).k) σ) 0 = ⊤ := by
      apply meromorphicOrderAt_eq_top_iff.mpr
      filter_upwards [self_mem_nhdsWithin] with q hq
      have hq' : q ≠ 0 := hq
      rw [Phi_eq_T N _ _ hq', ModularForm.coe_zero, SlashAction.zero_slash]
      rfl
    rw [h0, top_add]

theorem nu_ne_top (σ : SL(2, ℤ)) {x : CF N} (hx : x ≠ 0) : nu σ x ≠ ⊤ :=
  fun h => hx ((nu_eq_top_iff σ x).mp h)

theorem nu_one (σ : SL(2, ℤ)) : nu σ (1 : CF N) = 0 := by
  rw [← map_one (algebraMap ℂ (CF N))]
  exact nu_algebraMap σ 1 one_ne_zero

def X (N : ℕ) [NeZero N] : CF N :=
  ⟨coeffEmb ℂ jq, coeffEmb_mem_laurentBaseChange ℂ (modularFunctionField_le_full N (jq_mem N))⟩

theorem X_ne_zero : X N ≠ 0 := by
  intro h
  have h1 := congrArg (fun y : CF N => (y : LaurentSeries ℂ).coeff (-1)) h
  simp only [X] at h1
  rw [coeffEmb_coeff, coeff_jq_neg_one, map_one] at h1
  have h2 : ((0 : CF N) : LaurentSeries ℂ).coeff (-1) = 0 := rfl
  exact one_ne_zero (h1.trans h2)

variable (N)

omit [NeZero N] in

theorem Gamma0_le_SL :
    ((CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ :=
  Subgroup.map_le_range _ _

def G₁ : ModularForm 𝒮ℒ 12 := ModularForm.mcast (by decide) (ModularForm.E₄.pow 3)

def G : ModularForm (CongruenceSubgroup.Gamma0 N) 12 := restrict (Gamma0_le_SL N) G₁

def H : ModularForm (CongruenceSubgroup.Gamma0 N) 12 :=
  restrict (Gamma0_le_SL N) CuspForm.discriminant

omit [NeZero N] in
theorem coe_G : ((G N : ModularForm _ 12) : ℍ → ℂ) = fun τ => ModularForm.E₄ τ ^ 3 := by
  show ((ModularForm.E₄.pow 3 : ModularForm 𝒮ℒ (3 * 4)) : ℍ → ℂ) = _
  rw [ModularForm.coe_pow]
  rfl

omit [NeZero N] in
theorem coe_H : ((H N : ModularForm _ 12) : ℍ → ℂ) = ModularForm.discriminant := rfl

omit [NeZero N] in
theorem H_ne_zero : H N ≠ 0 := by
  intro h
  have := congrArg (fun f : ModularForm (CongruenceSubgroup.Gamma0 N) 12 => (f : ℍ → ℂ) I) h
  simp only [coe_H, ModularForm.coe_zero, Pi.zero_apply] at this
  exact ModularForm.discriminant_ne_zero I this

omit [NeZero N] in
theorem qL_G : qL (G N) =
    ((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 := by
  have hc : ((G N : ModularForm _ 12) : ℍ → ℂ) =
      ((ModularForm.E₄.pow 3 : ModularForm 𝒮ℒ (3 * 4)) : ℍ → ℂ) := rfl
  have h : qExpansion 1 ((G N : ModularForm _ 12) : ℍ → ℂ) =
      (qExpansion 1 (ModularForm.E₄ : ℍ → ℂ)) ^ 3 := by
    rw [hc, ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  rw [qL, h, PowerSeries.coe_pow]

omit [NeZero N] in
theorem qL_H : qL (H N) =
    ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) :=
  rfl

theorem coeffEmb_jq_eq : coeffEmb ℂ jq = jqModC ℂ := by
  rw [← jqModC_rat]
  exact map_jqModC (algebraMap ℚ ℂ)

def PX : Pres N ((X N : CF N) : LaurentSeries ℂ) where
  k := 12
  g := G N
  h := H N
  h_ne := H_ne_zero N
  eq := by
    show coeffEmb ℂ jq * qL (H N) = qL (G N)
    rw [coeffEmb_jq_eq, jqModC_eq_qExpansion_E4_cube_div_discriminant, qL_G, ← qL_H N]
    exact div_mul_cancel₀ _ (qL_ne_zero (H N) (H_ne_zero N))

omit [NeZero N] in

theorem slash_G (σ : SL(2, ℤ)) : ⇑(G N) ∣[(12 : ℤ)] σ = ⇑(G N) :=
  SlashInvariantFormClass.slash_action_eq (G₁ : ModularForm 𝒮ℒ 12)
    (Matrix.SpecialLinearGroup.mapGL ℝ σ) ⟨σ, rfl⟩

omit [NeZero N] in

theorem slash_H (σ : SL(2, ℤ)) : ⇑(H N) ∣[(12 : ℤ)] σ = ⇑(H N) :=
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

omit [NeZero N] in
theorem tendsto_G_atImInfty : Tendsto (⇑(G N)) atImInfty (𝓝 1) := by
  rw [coe_G]
  simpa using (tendsto_E4_atImInfty).pow 3

omit [NeZero N] in
theorem tendsto_H_atImInfty : Tendsto (⇑(H N)) atImInfty (𝓝 0) :=
  ModularForm.discriminant_isZeroAtImInfty

theorem Phi_G_zero (σ : SL(2, ℤ)) : Phi N (G N) σ 0 = 1 := by
  rw [Phi_zero, slash_G]
  exact (tendsto_G_atImInfty N).limUnder_eq

theorem Phi_H_zero (σ : SL(2, ℤ)) : Phi N (H N) σ 0 = 0 := by
  rw [Phi_zero, slash_H]
  exact (tendsto_H_atImInfty N).limUnder_eq

theorem meromorphicOrderAt_Phi_G (σ : SL(2, ℤ)) : meromorphicOrderAt (Phi N (G N) σ) 0 = 0 := by
  apply (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero
    (analyticAt_Phi N (G N) σ).meromorphicAt).mp
  refine ⟨1, one_ne_zero, ?_⟩
  have h := ((analyticAt_Phi N (G N) σ).continuousAt.tendsto).mono_left
    (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℂ)))
  rwa [Phi_G_zero] at h

theorem meromorphicOrderAt_Phi_H_pos (σ : SL(2, ℤ)) :
    0 < meromorphicOrderAt (Phi N (H N) σ) 0 := by
  apply (tendsto_zero_iff_meromorphicOrderAt_pos (analyticAt_Phi N (H N) σ).meromorphicAt).mp
  have h := ((analyticAt_Phi N (H N) σ).continuousAt.tendsto).mono_left
    (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℂ)))
  rwa [Phi_H_zero] at h

theorem nu_X_neg (σ : SL(2, ℤ)) : nu σ (X N) < 0 := by
  obtain ⟨m, hm0, hmH, hF⟩ := meromorphicOrderAt_F_eq N (PX N) σ
  have hpos := meromorphicOrderAt_Phi_H_pos N σ
  have hmH' : meromorphicOrderAt (Phi N (H N) σ) 0 = m := hmH
  rw [hmH', ← WithTop.coe_zero, WithTop.coe_lt_coe] at hpos
  have hG : meromorphicOrderAt (Phi N (PX N).g σ) 0 = 0 := meromorphicOrderAt_Phi_G N σ
  show meromorphicOrderAt (F N ((X N : CF N) : LaurentSeries ℂ) σ) 0 < 0
  rw [hF, hG, zero_add, ← WithTop.coe_zero, WithTop.coe_lt_coe]
  omega

variable {N}

theorem exists_nu_pos (σ : SL(2, ℤ)) : ∃ x : CF N, 0 < nu σ x ∧ nu σ x ≠ ⊤ := by
  have hXt := nu_ne_top σ (X_ne_zero (N := N))
  have hneg := nu_X_neg N σ
  refine ⟨(X N)⁻¹, ?_, nu_ne_top σ (inv_ne_zero (X_ne_zero (N := N)))⟩
  have hsum : nu σ (X N)⁻¹ + nu σ (X N) = 0 := by
    rw [← nu_mul, inv_mul_cancel₀ (X_ne_zero (N := N)), nu_one]
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hXt
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (nu_ne_top σ (inv_ne_zero (X_ne_zero (N := N))))
  rw [← hm, ← hn, ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_eq_coe] at hsum
  rw [← hm, ← WithTop.coe_zero, WithTop.coe_lt_coe] at hneg
  rw [← hn, ← WithTop.coe_zero, WithTop.coe_lt_coe]
  omega

variable (N) in

theorem exists_place (σ : SL(2, ℤ)) :
    ∃ (P : AlgebraicCurve.Place ℂ (CF N)) (e : ℕ), 0 < e ∧
      (∀ x, x ∈ P.toValuationSubring ↔ 0 ≤ nu σ x) ∧
      ∀ x, x ≠ 0 → nu σ x = (((e : ℤ) * P.ord x : ℤ) : WithTop ℤ) :=
  AlgebraicCurve.Place.exists_of_orderMap (nu σ) (nu_eq_top_iff σ) (nu_mul σ) (nu_add σ)
    (fun c hc => nu_algebraMap σ c hc) (exists_nu_pos σ)

end Cusp

section Interior

variable (N : ℕ)

theorem analyticAt_comp_ofComplex {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k)
    (τ : ℍ) : AnalyticAt ℂ (fun z : ℂ => (f : ℍ → ℂ) (ofComplex z)) (τ : ℂ) := by
  have hf : DifferentiableOn ℂ ((f : ℍ → ℂ) ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp (ModularFormClass.holo f)
  exact hf.analyticAt (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)

abbrev rz (x : LaurentSeries ℂ) : ℂ → ℂ := fun w : ℂ => realize N x (ofComplex w)

theorem differentiableAt_rz {x : LaurentSeries ℂ} (P : Pres N x) (w : ℍ) (hw : P.h w ≠ 0) :
    DifferentiableAt ℂ (rz N x) (w : ℂ) := by
  have hg := analyticAt_comp_ofComplex N P.g w
  have hh := analyticAt_comp_ofComplex N P.h w
  have hw' : (fun z : ℂ => (P.h : ℍ → ℂ) (ofComplex z)) (w : ℂ) ≠ 0 := by
    simpa only [ofComplex_apply] using hw
  refine (hg.div hh hw').differentiableAt.congr_of_eventuallyEq ?_
  filter_upwards [hh.continuousAt.eventually_ne hw'] with z hz
  exact ModularCurve.realize_eq_div N P.g P.h x P.eq (ofComplex z) hz

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
  convert h1 using 1
  all_goals try rfl
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

variable (N : ℕ) [NeZero N] {k : ℤ}

theorem differentiableAt_Phi (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) (σ : SL(2, ℤ))
    {q : ℂ} (hq : ‖q‖ < 1) : DifferentiableAt ℂ (Phi N f σ) q :=
  ModularFormClass.differentiableAt_cuspFunction (translateSL N f σ) (natCast_pos N)
    (natCast_mem_strictPeriods_Gamma N) hq

abbrev Psi {x : LaurentSeries ℂ} (P : Pres N x) (σ : SL(2, ℤ)) : ℂ → ℂ :=
  fun q => Phi N P.g σ q / Phi N P.h σ q

theorem differentiableAt_Psi {x : LaurentSeries ℂ} (P : Pres N x) (σ : SL(2, ℤ)) {q : ℂ}
    (hq : ‖q‖ < 1) (h0 : Phi N P.h σ q ≠ 0) : DifferentiableAt ℂ (Psi N P σ) q :=
  (differentiableAt_Phi N P.g σ hq).div (differentiableAt_Phi N P.h σ hq) h0

theorem slash_eventuallyEq {a x : LaurentSeries ℂ} (Pa : Pres N a) (Px : Pres N x)
    (σ : SL(2, ℤ)) :
    ∀ᶠ τ : ℍ in atImInfty,
      ((fun τ : ℍ => realize N a τ * deriv (rz N x) τ) ∣[(2 : ℤ)] σ) τ =
        (2 * ↑Real.pi * Complex.I / (N : ℂ)) * Periodic.qParam (N : ℝ) (τ : ℂ) *
          (Psi N Pa σ (Periodic.qParam (N : ℝ) (τ : ℂ)) *
            deriv (Psi N Px σ) (Periodic.qParam (N : ℝ) (τ : ℂ))) := by
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp (eventually_apply_smul_ne_zero N Px.h Px.h_ne σ)
  have hevA : ∀ᶠ τ : ℍ in atImInfty, A < τ.im :=
    (atImInfty_mem _).mpr ⟨A + 1, fun z hz => lt_of_lt_of_le (lt_add_one A) hz⟩
  filter_upwards [hevA, realize_smul_eventuallyEq N Pa σ] with τ hτA hτa
  have hxτ : Px.h (σ • τ) ≠ 0 := hA τ hτA.le

  have hd : DifferentiableAt ℂ (rz N x) (moeb σ τ) := by
    rw [moeb_coe]; exact differentiableAt_rz N Px (σ • τ) hxτ
  have h1 : HasDerivAt (rz N x ∘ moeb σ)
      (deriv (rz N x) ((σ • τ : ℍ) : ℂ) *
        denom (Matrix.SpecialLinearGroup.mapGL ℝ σ) ↑τ ^ (-2 : ℤ)) τ := by
    have h := hd.hasDerivAt.comp (τ : ℂ) (hasDerivAt_moeb σ τ)
    rwa [moeb_coe] at h

  have hPhi : Phi N Px.h σ (Periodic.qParam (N : ℝ) (τ : ℂ)) ≠ 0 := by
    rw [Phi_qParam, ModularForm.SL_slash_apply]
    exact mul_ne_zero hxτ (zpow_ne_zero _ (denom_ne_zero _ _))
  have hPsi : DifferentiableAt ℂ (Psi N Px σ) (Periodic.qParam (N : ℝ) (τ : ℂ)) :=
    differentiableAt_Psi N Px σ (norm_qParam_lt_one' (natCast_pos N) τ) hPhi
  have h2 : HasDerivAt (Psi N Px σ ∘ Periodic.qParam (N : ℝ))
      (deriv (Psi N Px σ) (Periodic.qParam (N : ℝ) (τ : ℂ)) *
        (Periodic.qParam (N : ℝ) (τ : ℂ) * (2 * ↑Real.pi * Complex.I / (N : ℝ)))) τ :=
    hPsi.hasDerivAt.comp (τ : ℂ) (hasDerivAt_qParam (N : ℝ) τ)

  have h12 : (rz N x ∘ moeb σ) =ᶠ[𝓝 (τ : ℂ)] (Psi N Px σ ∘ Periodic.qParam (N : ℝ)) := by
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
    rw [ModularCurve.realize_eq_div N Px.g Px.h x Px.eq (σ • ofComplex z) hz',
      ← div_slash_eq N Px.g Px.h σ (ofComplex z), ← Phi_qParam N Px.g σ (ofComplex z),
      ← Phi_qParam N Px.h σ (ofComplex z), hcoe]

  have hderiv : deriv (rz N x) ((σ • τ : ℍ) : ℂ) *
      denom (Matrix.SpecialLinearGroup.mapGL ℝ σ) ↑τ ^ (-2 : ℤ) =
        deriv (Psi N Px σ) (Periodic.qParam (N : ℝ) (τ : ℂ)) *
          (Periodic.qParam (N : ℝ) (τ : ℂ) * (2 * ↑Real.pi * Complex.I / (N : ℝ))) :=
    (h1.congr_of_eventuallyEq h12.symm).unique h2

  rw [slash_two_apply, mul_assoc, hderiv, hτa, ← div_slash_eq N Pa.g Pa.h σ τ,
    ← Phi_qParam N Pa.g σ τ, ← Phi_qParam N Pa.h σ τ]
  push_cast
  ring

omit [NeZero N] in

theorem isBigO_qParam :
    (fun τ : ℍ => (2 * ↑Real.pi * Complex.I / (N : ℂ)) * Periodic.qParam (N : ℝ) (τ : ℂ))
      =O[atImInfty] fun τ : ℍ => Real.exp (-(2 * Real.pi / N) * τ.im) := by
  refine (Asymptotics.IsBigO.of_bound' ?_).const_mul_left _
  refine Filter.Eventually.of_forall fun τ => ?_
  rw [Periodic.norm_qParam, UpperHalfPlane.coe_im, Real.norm_eq_abs, Real.abs_exp]
  apply le_of_eq
  congr 1
  ring

end CuspDeriv

section Germs

variable (N : ℕ) [NeZero N]

omit [NeZero N] in

theorem eventually_eventuallyEq_nhds {f g : ℂ → ℂ} {τ : ℂ} (h : f =ᶠ[𝓝[≠] τ] g) :
    ∀ᶠ z in 𝓝[≠] τ, f =ᶠ[𝓝 z] g := by
  rw [Filter.EventuallyEq, eventually_nhdsWithin_iff] at h
  rw [eventually_nhdsWithin_iff]
  filter_upwards [h.eventually_nhds] with z hz hzτ
  filter_upwards [hz, eventually_ne_nhds (Set.mem_compl_singleton_iff.mp hzτ)] with w hw hwτ
  exact hw (Set.mem_compl_singleton_iff.mpr hwτ)

omit [NeZero N] in
theorem deriv_eventuallyEq {f g : ℂ → ℂ} {τ : ℂ} (h : f =ᶠ[𝓝[≠] τ] g) :
    deriv f =ᶠ[𝓝[≠] τ] deriv g :=
  (eventually_eventuallyEq_nhds h).mono fun _ hz => hz.deriv_eq

omit [NeZero N] in

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

variable {N}

theorem eventually_differentiableAt_F (σ : SL(2, ℤ)) (y : CF N) :
    ∀ᶠ q in 𝓝[≠] (0 : ℂ), DifferentiableAt ℂ (F N (y : LaurentSeries ℂ) σ) q := by
  have hball : ∀ᶠ q in 𝓝[≠] (0 : ℂ), ‖q‖ < 1 := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0 : ℂ) one_pos)]
      with q hq
    rwa [mem_ball_zero_iff] at hq
  filter_upwards [eventually_eventuallyEq_nhds (F_eventuallyEq N (pres y) σ),
    Phi_eventually_ne_zero N (pres y).h (pres y).h_ne σ, hball] with q hq hh hq1
  exact (differentiableAt_Psi N (pres y) σ hq1 hh).congr_of_eventuallyEq hq

theorem F_coe_mul (σ : SL(2, ℤ)) (x y : CF N) :
    F N ((x * y : CF N) : LaurentSeries ℂ) σ =ᶠ[𝓝[≠] (0 : ℂ)]
      fun q => F N (x : LaurentSeries ℂ) σ q * F N (y : LaurentSeries ℂ) σ q := by
  show F N ((x : LaurentSeries ℂ) * (y : LaurentSeries ℂ)) σ =ᶠ[𝓝[≠] (0 : ℂ)]
    F N (x : LaurentSeries ℂ) σ * F N (y : LaurentSeries ℂ) σ
  exact F_mul_eventuallyEq N (pres x) (pres y) σ

theorem F_coe_add (σ : SL(2, ℤ)) (x y : CF N) :
    F N ((x + y : CF N) : LaurentSeries ℂ) σ =ᶠ[𝓝[≠] (0 : ℂ)]
      fun q => F N (x : LaurentSeries ℂ) σ q + F N (y : LaurentSeries ℂ) σ q := by
  show F N ((x : LaurentSeries ℂ) + (y : LaurentSeries ℂ)) σ =ᶠ[𝓝[≠] (0 : ℂ)]
    F N (x : LaurentSeries ℂ) σ + F N (y : LaurentSeries ℂ) σ
  exact F_add_eventuallyEq N (pres x) (pres y) σ

theorem F_coe_const (σ : SL(2, ℤ)) (c : ℂ) :
    F N ((algebraMap ℂ (CF N) c : CF N) : LaurentSeries ℂ) σ =ᶠ[𝓝[≠] (0 : ℂ)] fun _ => c :=
  F_const_eventuallyEq N c σ

theorem F_coe_smul (σ : SL(2, ℤ)) (c : ℂ) (y : CF N) :
    F N ((c • y : CF N) : LaurentSeries ℂ) σ =ᶠ[𝓝[≠] (0 : ℂ)]
      fun q => c * F N (y : LaurentSeries ℂ) σ q := by
  rw [Algebra.smul_def]
  filter_upwards [F_coe_mul σ (algebraMap ℂ (CF N) c) y, F_coe_const (N := N) σ c]
    with q h1 h2
  rw [h1, h2]

@[nolint unusedArguments]
def Gm (_N : ℕ) (_σ : SL(2, ℤ)) : Type := Filter.Germ (𝓝[≠] (0 : ℂ)) ℂ

scoped instance instCommRingGm (σ : SL(2, ℤ)) : CommRing (Gm N σ) :=
  inferInstanceAs (CommRing (Filter.Germ (𝓝[≠] (0 : ℂ)) ℂ))

variable (N)

def germ (σ : SL(2, ℤ)) (f : ℂ → ℂ) : Gm N σ := ((f : Filter.Germ (𝓝[≠] (0 : ℂ)) ℂ) : Gm N σ)

omit [NeZero N] in
theorem germ_eq_iff {σ : SL(2, ℤ)} {f g : ℂ → ℂ} :
    germ N σ f = germ N σ g ↔ f =ᶠ[𝓝[≠] (0 : ℂ)] g := Filter.Germ.coe_eq

omit [NeZero N] in
theorem germ_mul (σ : SL(2, ℤ)) (f g : ℂ → ℂ) :
    germ N σ (fun z => f z * g z) = germ N σ f * germ N σ g := rfl

omit [NeZero N] in
theorem germ_add (σ : SL(2, ℤ)) (f g : ℂ → ℂ) :
    germ N σ (fun z => f z + g z) = germ N σ f + germ N σ g := rfl

omit [NeZero N] in
theorem germ_zero (σ : SL(2, ℤ)) : germ N σ (fun _ => (0 : ℂ)) = 0 := rfl

omit [NeZero N] in
theorem germ_one (σ : SL(2, ℤ)) : germ N σ (fun _ => (1 : ℂ)) = 1 := rfl

def φ (σ : SL(2, ℤ)) : CF N →+* Gm N σ where
  toFun y := germ N σ (F N (y : LaurentSeries ℂ) σ)
  map_one' := by
    rw [← germ_one, germ_eq_iff]
    have h := F_coe_const (N := N) σ 1
    rwa [map_one] at h
  map_mul' x y := by
    rw [← germ_mul, germ_eq_iff]
    exact F_coe_mul σ x y
  map_zero' := by
    rw [← germ_zero, germ_eq_iff]
    have h := F_coe_const (N := N) σ 0
    rwa [map_zero] at h
  map_add' x y := by
    rw [← germ_add, germ_eq_iff]
    exact F_coe_add σ x y

scoped instance algebraCF (σ : SL(2, ℤ)) : Algebra (CF N) (Gm N σ) := (φ N σ).toAlgebra

scoped instance algebraC (σ : SL(2, ℤ)) : Algebra ℂ (Gm N σ) :=
  ((φ N σ).comp (algebraMap ℂ (CF N))).toAlgebra

scoped instance isScalarTower (σ : SL(2, ℤ)) : IsScalarTower ℂ (CF N) (Gm N σ) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

theorem smul_def_CF (σ : SL(2, ℤ)) (y : CF N) (m : Gm N σ) :
    y • m = germ N σ (F N (y : LaurentSeries ℂ) σ) * m := rfl

theorem smul_def_C (σ : SL(2, ℤ)) (c : ℂ) (m : Gm N σ) :
    c • m = germ N σ (F N ((algebraMap ℂ (CF N) c : CF N) : LaurentSeries ℂ) σ) * m := rfl

def δ (σ : SL(2, ℤ)) : Derivation ℂ (CF N) (Gm N σ) where
  toFun y := germ N σ (deriv (F N (y : LaurentSeries ℂ) σ))
  map_add' x y := by
    rw [← germ_add, germ_eq_iff]
    filter_upwards [deriv_eventuallyEq (F_coe_add σ x y), eventually_differentiableAt_F σ x,
      eventually_differentiableAt_F σ y] with z hz hx hy
    rw [hz, deriv_fun_add hx hy]
  map_smul' c x := by
    simp only [RingHom.id_apply]
    rw [smul_def_C, ← germ_mul, germ_eq_iff]
    filter_upwards [deriv_eventuallyEq (F_coe_smul σ c x), F_coe_const (N := N) σ c]
      with z h1 h2
    rw [h1, h2, deriv_const_mul_field]
  map_one_eq_zero' := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [← germ_zero, germ_eq_iff]
    have h1 := F_coe_const (N := N) σ 1
    rw [map_one] at h1
    filter_upwards [deriv_eventuallyEq h1] with z hz
    rw [hz, deriv_const]
  leibniz' x y := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [smul_def_CF, smul_def_CF, ← germ_mul, ← germ_mul, ← germ_add, germ_eq_iff]
    filter_upwards [deriv_eventuallyEq (F_coe_mul σ x y), eventually_differentiableAt_F σ x,
      eventually_differentiableAt_F σ y] with z hz hx hy
    rw [hz, deriv_fun_mul hx hy]
    ring

theorem δ_apply (σ : SL(2, ℤ)) (y : CF N) :
    δ N σ y = germ N σ (deriv (F N (y : LaurentSeries ℂ) σ)) := rfl

variable {N}

theorem eventuallyEq_of_smul_D_eq_smul_D (σ : SL(2, ℤ)) {a x c π : CF N}
    (h : a • KaehlerDifferential.D ℂ (CF N) x = c • KaehlerDifferential.D ℂ (CF N) π) :
    (fun q => F N (a : LaurentSeries ℂ) σ q * deriv (F N (x : LaurentSeries ℂ) σ) q)
      =ᶠ[𝓝[≠] (0 : ℂ)]
      fun q => F N (c : LaurentSeries ℂ) σ q * deriv (F N (π : LaurentSeries ℂ) σ) q := by
  have h' := congrArg ((δ N σ).liftKaehlerDifferential) h
  rw [map_smul, map_smul, Derivation.liftKaehlerDifferential_comp_D,
    Derivation.liftKaehlerDifferential_comp_D, δ_apply, δ_apply, smul_def_CF, smul_def_CF,
    ← germ_mul, ← germ_mul, germ_eq_iff] at h'
  exact h'

end Germs

section Bounded

variable {N : ℕ} [NeZero N]

set_option maxHeartbeats 16000000 in

theorem isBigO_cusp [∀ w : AlgebraicCurve.Place ℂ (CF N), w.DCoordGenerates] (a x : CF N)
    (hreg : ∀ v : AlgebraicCurve.Place ℂ (CF N), X N ∉ v.toValuationSubring →
      0 ≤ v.ordDifferential (a • KaehlerDifferential.D ℂ (CF N) x))
    (σ : SL(2, ℤ)) :
    (fun q => Psi N (pres a) σ q * deriv (Psi N (pres x) σ) q) =O[𝓝[≠] (0 : ℂ)]
      fun _ => (1 : ℝ) := by
  obtain ⟨P, e, _he, hmem, hordP⟩ := exists_place N σ

  have hX : X N ∉ P.toValuationSubring := by
    rw [hmem, not_le]
    exact nu_X_neg N σ

  obtain ⟨π, hπ0, hπ1, hdc⟩ : ∃ π : CF N, π ≠ 0 ∧ P.ord π = 1 ∧
      P.dCoord = KaehlerDifferential.D ℂ (CF N) π :=
    ⟨P.uniformizer, P.uniformizer_ne_zero, P.ord_uniformizer, P.dCoord_eq⟩

  obtain ⟨c, hac, hc⟩ : ∃ c : CF N,
      a • KaehlerDifferential.D ℂ (CF N) x = c • KaehlerDifferential.D ℂ (CF N) π ∧
        0 ≤ P.ord c := by
    refine ⟨P.differentialCoeff (a • KaehlerDifferential.D ℂ (CF N) x), ?_, ?_⟩
    · rw [← hdc]
      exact (P.differentialCoeff_smul_dCoord _).symm
    · have h := hreg P hX
      rwa [AlgebraicCurve.Place.ordDifferential] at h

  have hνc : 0 ≤ nu σ c := by
    rcases eq_or_ne c 0 with h0 | h0
    · rw [(nu_eq_top_iff σ _).mpr h0]
      exact le_top
    · rw [hordP _ h0, ← WithTop.coe_zero, WithTop.coe_le_coe]
      exact mul_nonneg (Int.natCast_nonneg e) hc
  have hνπ : 0 ≤ nu σ π := by
    rw [hordP _ hπ0, hπ1, mul_one, ← WithTop.coe_zero, WithTop.coe_le_coe]
    exact Int.natCast_nonneg e

  obtain ⟨Gc, hGc, hFc⟩ := exists_analyticAt_eventuallyEq (meromorphicAt_F' σ _) hνc
  obtain ⟨Gπ, hGπ, hFπ⟩ := exists_analyticAt_eventuallyEq (meromorphicAt_F' σ _) hνπ

  have hbd : (fun q => Gc q * deriv Gπ q) =O[𝓝[≠] (0 : ℂ)] fun _ => (1 : ℝ) := by
    have hcont : ContinuousAt (fun q => Gc q * deriv Gπ q) 0 :=
      (hGc.mul hGπ.deriv).continuousAt
    exact (hcont.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one ℝ
  refine Filter.EventuallyEq.trans_isBigO ?_ hbd

  have h1 : (fun q => Psi N (pres a) σ q * deriv (Psi N (pres x) σ) q) =ᶠ[𝓝[≠] (0 : ℂ)]
      fun q => F N (a : LaurentSeries ℂ) σ q * deriv (F N (x : LaurentSeries ℂ) σ) q := by
    filter_upwards [F_eventuallyEq N (pres a) σ,
      deriv_eventuallyEq (F_eventuallyEq N (pres x) σ)] with q ha hx
    rw [ha, hx]
  have h2 := eventuallyEq_of_smul_D_eq_smul_D σ hac
  have h3 : (fun q => F N (c : LaurentSeries ℂ) σ q * deriv (F N (π : LaurentSeries ℂ) σ) q)
      =ᶠ[𝓝[≠] (0 : ℂ)] fun q => Gc q * deriv Gπ q := by
    filter_upwards [hFc, deriv_eventuallyEq hFπ] with q h h'
    rw [h, h']
  exact (h1.trans h2).trans h3

set_option maxHeartbeats 16000000 in

theorem main [∀ w : AlgebraicCurve.Place ℂ (CF N), w.DCoordGenerates] (a x : CF N)
    (hreg : ∀ v : AlgebraicCurve.Place ℂ (CF N), X N ∉ v.toValuationSubring →
      0 ≤ v.ordDifferential (a • KaehlerDifferential.D ℂ (CF N) x))
    (σ : SL(2, ℤ)) :
    ∃ δ : ℝ, 0 < δ ∧
      ((fun τ : ℍ => realize N (a : LaurentSeries ℂ) τ *
          deriv (fun w : ℂ => realize N (x : LaurentSeries ℂ) (ofComplex w)) τ)
        ∣[(2 : ℤ)] σ) =O[atImInfty] fun τ : ℍ => Real.exp (-δ * τ.im) := by
  refine ⟨2 * Real.pi / N, div_pos Real.two_pi_pos (natCast_pos N), ?_⟩
  have hC := (isBigO_cusp a x hreg σ).comp_tendsto (tendsto_qParam N)
  have hDC := ((isBigO_qParam N).mul hC).congr_right (fun _ => mul_one _)
  refine (Filter.EventuallyEq.trans_isBigO ?_ hDC)
  exact slash_eventuallyEq N (pres a) (pres x) σ

end Bounded

end ModularCurve.CuspDecayAux
p2m_reactivate "P2MW.S_ModularCurve_exists_isBigO_slash_realize_mul_deriv_realize_of_forall_ordDifferential_nonneg.ModularCurve P2MW.S_ModularCurve_exists_isBigO_slash_realize_mul_deriv_realize_of_forall_ordDifferential_nonneg.ModularCurve.CuspDecayAux"
p2m_reactivate "P2MW.S_ModularCurve_exists_isBigO_slash_realize_mul_deriv_realize_of_forall_ordDifferential_nonneg.ModularCurve"

set_option maxHeartbeats 16000000 in
open _root_.ModularCurve _root_.P2MW.S_ModularCurve_exists_isBigO_slash_realize_mul_deriv_realize_of_forall_ordDifferential_nonneg.ModularCurve ModularCurve.CuspDecayAux in
theorem solution
    (N : ℕ) [NeZero N]
    [∀ w : AlgebraicCurve.Place ℂ
      (ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)),
      w.DCoordGenerates]
    (a x : ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N))
    (hreg : ∀ v : AlgebraicCurve.Place ℂ
        (ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)),
      (⟨ModularCurve.coeffEmb ℂ ModularCurve.jq,
          ModularCurve.coeffEmb_mem_laurentBaseChange ℂ
            (ModularCurve.modularFunctionField_le_full N (ModularCurve.jq_mem N))⟩ :
          ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)) ∉
        v.toValuationSubring →
      0 ≤ v.ordDifferential (a • KaehlerDifferential.D ℂ
        (ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)) x))
    (σ : SL(2, ℤ)) :
    ∃ δ : ℝ, 0 < δ ∧
      ((fun τ : ℍ => ModularCurve.realize N (a : LaurentSeries ℂ) τ *
          deriv (fun w : ℂ => ModularCurve.realize N (x : LaurentSeries ℂ) (ofComplex w)) τ)
        ∣[(2 : ℤ)] σ) =O[atImInfty] fun τ : ℍ => Real.exp (-δ * τ.im) :=
  main a x hreg σ

end
p2m_reactivate "P2MW.S_ModularCurve_exists_isBigO_slash_realize_mul_deriv_realize_of_forall_ordDifferential_nonneg.ModularCurve P2MW.S_ModularCurve_exists_isBigO_slash_realize_mul_deriv_realize_of_forall_ordDifferential_nonneg.ModularCurve.CuspDecayAux"

end S_ModularCurve_exists_isBigO_slash_realize_mul_deriv_realize_of_forall_ordDifferential_nonneg
end P2MW
export P2MW.S_ModularCurve_exists_isBigO_slash_realize_mul_deriv_realize_of_forall_ordDifferential_nonneg (solution)
