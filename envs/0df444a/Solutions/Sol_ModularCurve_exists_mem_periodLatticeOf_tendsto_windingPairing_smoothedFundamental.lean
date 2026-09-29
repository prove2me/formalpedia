-- Prove2me | solution 1 for ModularCurve.exists_mem_periodLatticeOf_tendsto_windingPairing_smoothedFundamental
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/19c3767b-e680-5664-b76f-2f436e6d37cf

import Mathlib
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet
import Definitions.Def_ModularCurve_SmoothedFundamental
import Theorems.Thm_Complex_integral_logDeriv_wedge_add_finsum_eq_integral_dbarLogDeriv
import Theorems.Thm_ModularCurve_exists_exp_eq_of_invariant_ne_zero_isParabolicHom
import Theorems.Thm_ModularCurve_integral_dbar_mul_cuspForm_gammaFundamentalSet_eq_sidePairing
import Theorems.Thm_ModularCurve_exists_invariant_localModel_tendsto_integral_dbarLogDeriv_smoothedFundamental_periodAlongOf
import Theorems.Thm_FLT_Gamma0FundamentalSet_tendsto_integral_mul_smoothedFundamental
import Theorems.Thm_ModularCurve_contDiff_and_finsum_smoothedFundamental_eq_one
import Theorems.Thm_ModularCurve_exists_hasEquivariantPrimitiveOf
import Theorems.Thm_ModularCurve_periodAlongOf_apply_eq_sub_of_hasDerivAt
import Theorems.Thm_ModularCurve_exists_mem_periodLatticeOf_eq_sum_intCast_mul_edgeIntegral_of_isParabolicHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_mem_periodLatticeOf_tendsto_windingPairing_smoothedFundamental
p2m_attr_erase "instance" "FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2"
p2m_attr_erase "simp" "FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero"

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section

p2m_open "UpperHalfPlane~I"
open MeasureTheory Filter Complex Set
open scoped MatrixGroups Topology Real ComplexConjugate ModularForm

namespace ModularCurve
p2m_export "ModularCurve" "periodAlongOf periodLatticeOf clamp01_of_mem segmentPoint periodAlong period periodLattice smoothedFundamental exists_exp_eq_of_invariant_ne_zero_isParabolicHom integral_dbar_mul_cuspForm_gammaFundamentalSet_eq_sidePairing exists_invariant_localModel_tendsto_integral_dbarLogDeriv_smoothedFundamental_periodAlongOf contDiff_and_finsum_smoothedFundamental_eq_one exists_hasEquivariantPrimitiveOf periodAlongOf_apply_eq_sub_of_hasDerivAt exists_mem_periodLatticeOf_eq_sum_intCast_mul_edgeIntegral_of_isParabolicHom"
namespace WindingReciprocity
p2m_open "ModularCurve"

local notation "𝕌" => UpperHalfPlane.upperHalfPlaneSet

theorem coe_ofComplex {z : ℂ} (hz : 0 < z.im) : ((ofComplex z : ℍ) : ℂ) = z := by
  rw [ofComplex_apply_of_im_pos hz]

theorem ofComplex_coe (τ : ℍ) : ofComplex (τ : ℂ) = τ := ofComplex_apply τ

theorem mem_U (τ : ℍ) : (τ : ℂ) ∈ 𝕌 := τ.im_pos

section Smul

def sm (σ : SL(2, ℤ)) (z : ℂ) : ℂ := ((σ • ofComplex z : ℍ) : ℂ)

theorem sm_coe (σ : SL(2, ℤ)) (τ : ℍ) : sm σ τ = ((σ • τ : ℍ) : ℂ) := by
  simp [sm]

theorem im_sm_pos (σ : SL(2, ℤ)) (z : ℂ) : 0 < (sm σ z).im := (σ • ofComplex z).im_pos

theorem det_coe' (σ : SL(2, ℤ)) : ((σ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 :=
  (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) σ).det_coe

theorem det_pos (σ : SL(2, ℤ)) : 0 < ((σ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det := by
  rw [det_coe']; exact one_pos

theorem hasDerivAt_sm (σ : SL(2, ℤ)) (τ : ℍ) :
    HasDerivAt (sm σ) (1 / denom (σ : GL (Fin 2) ℝ) τ ^ 2) τ := by
  have h := (UpperHalfPlane.hasStrictDerivAt_smul (g := (σ : GL (Fin 2) ℝ)) (det_pos σ) τ).hasDerivAt
  rw [det_coe'] at h
  simp at h ⊢
  exact h

theorem deriv_sm_ne_zero (σ : SL(2, ℤ)) (τ : ℍ) : (1 / denom (σ : GL (Fin 2) ℝ) τ ^ 2 : ℂ) ≠ 0 :=
  div_ne_zero one_ne_zero (pow_ne_zero _ (denom_ne_zero _ _))

theorem differentiableAt_sm (σ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) : DifferentiableAt ℂ (sm σ) z :=
  (hasDerivAt_sm σ ⟨z, hz⟩).differentiableAt

theorem continuousAt_sm (σ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) : ContinuousAt (sm σ) z :=
  (differentiableAt_sm σ hz).continuousAt

theorem sm_mul (σ σ' : SL(2, ℤ)) (z : ℂ) : sm (σ * σ') z = sm σ (sm σ' z) := by
  simp only [sm]
  rw [ofComplex_coe, mul_smul]

theorem sm_one {z : ℂ} (hz : 0 < z.im) : sm 1 z = z := by
  simp [sm, coe_ofComplex hz]

theorem sm_inj (σ : SL(2, ℤ)) {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) (h : sm σ z = sm σ w) :
    z = w := by
  have : sm σ⁻¹ (sm σ z) = sm σ⁻¹ (sm σ w) := by rw [h]
  rwa [← sm_mul, ← sm_mul, inv_mul_cancel, sm_one hz, sm_one hw] at this

theorem im_smul_le_max (σ : SL(2, ℤ)) (τ : ℍ) : (σ • τ).im ≤ max τ.im τ.im⁻¹ := by
  rw [ModularGroup.im_smul_eq_div_normSq]
  have hy : 0 < τ.im := τ.im_pos
  by_cases hc : (σ 1 0 : ℤ) = 0
  ·
    have hd : (σ 1 1 : ℤ) ^ 2 = 1 := by
      have := σ.det_coe; rw [Matrix.det_fin_two] at this
      rw [hc] at this
      have h1 : (σ 0 0 : ℤ) * σ 1 1 = 1 := by linarith
      have := Int.eq_one_or_neg_one_of_mul_eq_one' h1
      rcases this with ⟨-, h⟩ | ⟨-, h⟩ <;> simp [h]
    have : Complex.normSq (denom (σ : GL (Fin 2) ℝ) τ) = 1 := by
      rw [ModularGroup.denom_apply, hc, Int.cast_zero, zero_mul, zero_add, Complex.normSq_intCast,
        ← sq]
      exact_mod_cast hd
    rw [this, div_one]; exact le_max_left _ _
  ·
    have hc2 : (1 : ℝ) ≤ ((σ 1 0 : ℤ) : ℝ) ^ 2 := by
      have : (1 : ℤ) ≤ (σ 1 0 : ℤ) ^ 2 := by
        have := Int.one_le_abs hc; nlinarith [sq_abs (σ 1 0 : ℤ)]
      exact_mod_cast this
    have hns : τ.im ^ 2 ≤ Complex.normSq (denom (σ : GL (Fin 2) ℝ) τ) := by
      rw [ModularGroup.denom_apply, Complex.normSq_apply]
      have him : (((σ 1 0 : ℤ) : ℂ) * τ + ((σ 1 1 : ℤ) : ℂ)).im = ((σ 1 0 : ℤ) : ℝ) * τ.im := by
        simp
      have hre := mul_self_nonneg ((((σ 1 0 : ℤ) : ℂ) * τ + ((σ 1 1 : ℤ) : ℂ)).re)
      rw [him]
      nlinarith [sq_nonneg τ.im, mul_nonneg (sub_nonneg.2 hc2) (sq_nonneg τ.im)]
    calc τ.im / Complex.normSq (denom (σ : GL (Fin 2) ℝ) τ) ≤ τ.im / τ.im ^ 2 :=
          div_le_div_of_nonneg_left hy.le (pow_pos hy 2) hns
      _ = τ.im⁻¹ := by field_simp
      _ ≤ max τ.im τ.im⁻¹ := le_max_right _ _

end Smul

section Primitives

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]

def Eg (g : CuspForm Γ 2) (z : ℂ) : ℂ :=
  ModularCurve.periodAlongOf Γ UpperHalfPlane.I (ofComplex z) g

def kC (g : CuspForm Γ 2) (z : ℂ) : ℂ := g (ofComplex z)

theorem hasDerivAt_affine (a b : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (1 - (s : ℂ)) * a + (s : ℂ) * b) (b - a) t := by
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
  have := ((h1.const_sub 1).mul_const a).add (h1.mul_const b)
  convert this using 1; rfl; rfl; ring

theorem segmentPoint_eq_of_mem {τ₀ τ₁ : ℍ} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ModularCurve.segmentPoint τ₀ τ₁ t = (1 - (t : ℂ)) * τ₀ + (t : ℂ) * τ₁ := by
  simp only [ModularCurve.segmentPoint, ModularCurve.clamp01_of_mem ht, Complex.real_smul,
    Complex.ofReal_sub, Complex.ofReal_one]

theorem hasDerivAt_Eg (g : CuspForm Γ 2) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (Eg Γ g) (kC Γ g z) z := by
  obtain ⟨P, hP⟩ := ModularCurve.exists_hasEquivariantPrimitiveOf Γ g
  have hfun : Eg Γ g = fun w => (P ∘ ofComplex) w - P UpperHalfPlane.I := by
    funext w
    simp only [Eg, ModularCurve.periodAlongOf_apply_eq_sub_of_hasDerivAt Γ g hP.1, Function.comp]
  rw [hfun]
  have h1 : HasDerivAt (P ∘ ofComplex) (g (ofComplex z)) z := by
    have := hP.1 (ofComplex z)
    rwa [coe_ofComplex hz] at this
  exact h1.sub_const _

theorem differentiableOn_Eg (g : CuspForm Γ 2) : DifferentiableOn ℂ (Eg Γ g) 𝕌 :=
  fun _ hz => (hasDerivAt_Eg Γ g hz).differentiableAt.differentiableWithinAt

theorem differentiableOn_kC (g : CuspForm Γ 2) : DifferentiableOn ℂ (kC Γ g) 𝕌 :=
  UpperHalfPlane.mdifferentiable_iff.mp (CuspFormClass.holo g)

theorem continuousOn_kC (g : CuspForm Γ 2) : ContinuousOn (kC Γ g) 𝕌 :=
  (differentiableOn_kC Γ g).continuousOn

def hT (T : ℝ) (z : ℂ) : ℂ := (ModularCurve.smoothedFundamental Γ T z : ℂ)

theorem hT_props (T : ℝ) :
    ContDiff ℝ 2 (hT Γ T) ∧ HasCompactSupport (hT Γ T) ∧ tsupport (hT Γ T) ⊆ 𝕌 := by
  obtain ⟨hcd, hcs, hts, -⟩ :=
    ModularCurve.contDiff_and_finsum_smoothedFundamental_eq_one Γ T
  have hsuppEq : Function.support (hT Γ T) =
      Function.support (ModularCurve.smoothedFundamental Γ T) := by
    ext z; simp [hT]
  refine ⟨?_, ?_, ?_⟩
  · have h1 : ContDiff ℝ 2 (ModularCurve.smoothedFundamental Γ T) := by
      exact_mod_cast hcd 2
    exact Complex.ofRealCLM.contDiff.comp h1
  · exact hcs.comp_left Complex.ofReal_zero
  · refine Subset.trans ?_ hts
    simp only [tsupport, hsuppEq]; exact Subset.rfl

theorem hT_eq_zero_of_notMem {T : ℝ} {z : ℂ} (hz : z ∉ 𝕌) : hT Γ T z = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hz ((hT_props Γ T).2.2 h)

theorem smoothedFundamental_eq_zero_of_notMem {T : ℝ} {z : ℂ} (hz : z ∉ 𝕌) :
    ModularCurve.smoothedFundamental Γ T z = 0 := by
  have := hT_eq_zero_of_notMem Γ (T := T) hz
  simpa [hT] using this

end Primitives

section Dbar

def dbar (f : ℂ → ℂ) (z : ℂ) : ℂ := (fderiv ℝ f z 1 + I * fderiv ℝ f z I) / 2

def dbarL (T : ℂ →L[ℝ] ℂ) : ℂ := (T 1 + I * T I) / 2

theorem dbar_eq_dbarL (f : ℂ → ℂ) (z : ℂ) : dbar f z = dbarL (fderiv ℝ f z) := rfl

theorem dbarL_comp_smul (T : ℂ →L[ℝ] ℂ) (d : ℂ) :
    dbarL (T.comp (d • (1 : ℂ →L[ℝ] ℂ))) = conj d * dbarL T := by
  have hlin : ∀ w : ℂ, T w = (w.re : ℂ) * T 1 + (w.im : ℂ) * T I := by
    intro w
    conv_lhs => rw [← Complex.re_add_im w]
    rw [map_add]
    have h1 : T (w.re : ℂ) = (w.re : ℂ) * T 1 := by
      rw [show ((w.re : ℂ)) = (w.re : ℝ) • (1 : ℂ) by simp, T.map_smul]; simp
    have h2 : T ((w.im : ℂ) * I) = (w.im : ℂ) * T I := by
      rw [show ((w.im : ℂ) * I) = (w.im : ℝ) • I by simp, T.map_smul]; simp
    rw [h1, h2]
  simp only [dbarL, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, smul_eq_mul, mul_one]
  rw [hlin d, hlin (d * I)]
  apply Complex.ext <;> simp <;> ring

variable {f : ℂ → ℂ}

theorem hasFDerivAt_sm (σ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    HasFDerivAt (sm σ) ((1 / denom (σ : GL (Fin 2) ℝ) (⟨z, hz⟩ : ℍ) ^ 2 : ℂ) • (1 : ℂ →L[ℝ] ℂ)) z :=
  (hasDerivAt_sm σ ⟨z, hz⟩).complexToReal_fderiv

theorem hasFDerivAt_comp_sm (σ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) {f' : ℂ →L[ℝ] ℂ}
    (hf : HasFDerivAt f f' (sm σ z)) :
    HasFDerivAt (fun u => f (sm σ u))
      (f'.comp ((1 / denom (σ : GL (Fin 2) ℝ) (⟨z, hz⟩ : ℍ) ^ 2 : ℂ) • (1 : ℂ →L[ℝ] ℂ))) z :=
  hf.comp z (hasFDerivAt_sm σ hz)

theorem fderiv_comp_sm (σ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im)
    (hf : DifferentiableAt ℝ f (sm σ z)) :
    fderiv ℝ (fun u => f (sm σ u)) z =
      (fderiv ℝ f (sm σ z)).comp ((1 / denom (σ : GL (Fin 2) ℝ) (⟨z, hz⟩ : ℍ) ^ 2 : ℂ) •
        (1 : ℂ →L[ℝ] ℂ)) :=
  (hasFDerivAt_comp_sm σ hz hf.hasFDerivAt).fderiv

theorem dbar_comp_sm (σ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im)
    (hf : DifferentiableAt ℝ f (sm σ z)) :
    dbar (fun u => f (sm σ u)) z =
      conj (1 / denom (σ : GL (Fin 2) ℝ) (⟨z, hz⟩ : ℍ) ^ 2 : ℂ) * dbar f (sm σ z) := by
  rw [dbar_eq_dbarL, fderiv_comp_sm σ hz hf, dbarL_comp_smul, dbar_eq_dbarL]

theorem norm_fderiv_comp_sm_smul (σ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) {c : ℂ}
    (hf : DifferentiableAt ℝ f (sm σ z)) {g : ℂ → ℂ}
    (hg : HasFDerivAt g (c • fderiv ℝ f (sm σ z)) (sm σ z)) :
    fderiv ℝ (fun u => g (sm σ u)) z = c • fderiv ℝ (fun u => f (sm σ u)) z := by
  rw [(hasFDerivAt_comp_sm σ hz hg).fderiv, fderiv_comp_sm σ hz hf, ContinuousLinearMap.smul_comp]

theorem dbar_smul_of_quasiperiodic {L : ℂ → ℂ} (hL : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℝ L z)
    (γ : SL(2, ℤ)) (c : ℂ) (hLc : ∀ z : ℂ, 0 < z.im → L (sm γ z) = L z + c) (τ : ℍ) :
    dbar L ((γ • τ : ℍ) : ℂ) = conj (denom (γ : GL (Fin 2) ℝ) τ) ^ 2 * dbar L τ := by
  have hτ : 0 < (τ : ℂ).im := τ.im_pos

  have hev : (fun u => L (sm γ u)) =ᶠ[𝓝 (τ : ℂ)] fun u => L u + c := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds (mem_U τ)] with u hu
    exact hLc u hu
  have h1 : dbar (fun u => L (sm γ u)) τ = dbar L τ := by
    simp only [dbar, hev.fderiv_eq]
    rw [show (fun u => L u + c) = fun u => L u + (fun _ => c) u from rfl, fderiv_add_const]
  have hsm : sm γ τ = ((γ • τ : ℍ) : ℂ) := sm_coe γ τ
  have hdiff : DifferentiableAt ℝ L (sm γ τ) := by rw [hsm]; exact hL _ (γ • τ).im_pos
  have h2 := dbar_comp_sm γ hτ hdiff
  rw [h1, hsm] at h2

  have hD : denom (γ : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ _
  have hmk : (⟨(τ : ℂ), hτ⟩ : ℍ) = τ := rfl
  rw [hmk] at h2
  rw [h2, map_div₀, map_one, map_pow]
  have hcD : conj (denom (γ : GL (Fin 2) ℝ) τ) ≠ 0 := (map_ne_zero _).2 hD
  field_simp

end Dbar

section LocalModels

def HasLocalModels (F : ℂ → ℂ) (n : ℍ → ℤ) : Prop :=
  ∀ τ : ℍ, ∃ Ψ : ℂ → ℂ, ContDiffAt ℝ 1 Ψ (τ : ℂ) ∧ Ψ τ ≠ 0 ∧
    F =ᶠ[𝓝 (τ : ℂ)] fun z => (z - τ) ^ (n τ) * Ψ z

def quot (Φ V : ℂ → ℂ) (z : ℂ) : ℂ := limUnder (𝓝[≠] z) fun w => Φ w / V w

variable {Φ V : ℂ → ℂ} {n : ℍ → ℤ}

theorem quot_local (hΦ : HasLocalModels Φ n) (hV : HasLocalModels V n) (τ : ℍ) :
    ∃ R : ℂ → ℂ, ContDiffAt ℝ 1 R (τ : ℂ) ∧ R τ ≠ 0 ∧ (quot Φ V =ᶠ[𝓝 (τ : ℂ)] R) ∧
      (∀ᶠ w in 𝓝[≠] (τ : ℂ), V w ≠ 0 ∧ Φ w = R w * V w) ∧
      (n τ = 0 → ∀ᶠ w in 𝓝 (τ : ℂ), V w ≠ 0 ∧ Φ w = quot Φ V w * V w) := by
  obtain ⟨Ψ, hΨ, hΨ0, hΦe⟩ := hΦ τ
  obtain ⟨Θ, hΘ, hΘ0, hVe⟩ := hV τ
  set R : ℂ → ℂ := fun w => Ψ w * (Θ w)⁻¹ with hR
  have hRcd : ContDiffAt ℝ 1 R τ := hΨ.mul (hΘ.inv hΘ0)
  have hRτ : R τ ≠ 0 := mul_ne_zero hΨ0 (inv_ne_zero hΘ0)

  have hΘne : ∀ᶠ w in 𝓝 (τ : ℂ), Θ w ≠ 0 := hΘ.continuousAt.eventually_ne hΘ0
  have hRc : ∀ᶠ w in 𝓝 (τ : ℂ), ContinuousAt R w :=
    (hRcd.eventually (by simp)).mono fun w hw => hw.continuousAt
  obtain ⟨O, hOmem, hOopen, hO⟩ : ∃ O : Set ℂ, (τ : ℂ) ∈ O ∧ IsOpen O ∧ ∀ w ∈ O,
      Φ w = (w - τ) ^ (n τ) * Ψ w ∧ V w = (w - τ) ^ (n τ) * Θ w ∧ Θ w ≠ 0 ∧ ContinuousAt R w := by
    have := ((hΦe.and hVe).and hΘne).and hRc
    obtain ⟨O, hO, hOo, hOm⟩ := eventually_nhds_iff.1 this
    exact ⟨O, hOm, hOo, fun w hw => ⟨(hO w hw).1.1.1, (hO w hw).1.1.2, (hO w hw).1.2, (hO w hw).2⟩⟩

  have hquotO : ∀ w ∈ O, w ≠ (τ : ℂ) → V w ≠ 0 ∧ Φ w = R w * V w := by
    intro w hw hne
    obtain ⟨h1, h2, h3, -⟩ := hO w hw
    have hz : (w - τ) ^ (n τ) ≠ 0 := zpow_ne_zero _ (sub_ne_zero.2 hne)
    refine ⟨by rw [h2]; exact mul_ne_zero hz h3, ?_⟩
    rw [h1, h2, hR]; field_simp

  have hqR : ∀ w ∈ O, quot Φ V w = R w := by
    intro w hw
    have hev : (fun u => Φ u / V u) =ᶠ[𝓝[≠] w] R := by
      have h1 : ∀ᶠ u in 𝓝[≠] w, u ∈ O := mem_nhdsWithin_of_mem_nhds (hOopen.mem_nhds hw)
      have h2 : ∀ᶠ u in 𝓝[≠] w, u ≠ (τ : ℂ) := by
        by_cases hwτ : w = τ
        · rw [hwτ]; exact self_mem_nhdsWithin
        · exact mem_nhdsWithin_of_mem_nhds (isOpen_ne.mem_nhds hwτ)
      filter_upwards [h1, h2] with u hu1 hu2
      obtain ⟨hVu, hΦu⟩ := hquotO u hu1 hu2
      rw [hΦu]; field_simp
    have hT : Tendsto (fun u => Φ u / V u) (𝓝[≠] w) (𝓝 (R w)) :=
      ((hO w hw).2.2.2.tendsto.mono_left nhdsWithin_le_nhds).congr' hev.symm
    exact hT.limUnder_eq
  refine ⟨R, hRcd, hRτ, ?_, ?_, ?_⟩
  · filter_upwards [hOopen.mem_nhds hOmem] with w hw using hqR w hw
  · have h1 : ∀ᶠ u in 𝓝[≠] (τ : ℂ), u ∈ O := mem_nhdsWithin_of_mem_nhds (hOopen.mem_nhds hOmem)
    filter_upwards [h1, self_mem_nhdsWithin] with u hu1 hu2 using hquotO u hu1 hu2
  · intro hn0
    filter_upwards [hOopen.mem_nhds hOmem] with w hw
    obtain ⟨h1, h2, h3, -⟩ := hO w hw
    rw [hn0, zpow_zero, one_mul] at h1 h2
    refine ⟨by rw [h2]; exact h3, ?_⟩
    rw [hqR w hw, h1, h2, hR]; field_simp

theorem contDiffAt_quot (hΦ : HasLocalModels Φ n) (hV : HasLocalModels V n) (τ : ℍ) :
    ContDiffAt ℝ 1 (quot Φ V) (τ : ℂ) := by
  obtain ⟨R, hR, -, hqR, -⟩ := quot_local hΦ hV τ
  exact hR.congr_of_eventuallyEq hqR

theorem quot_ne_zero (hΦ : HasLocalModels Φ n) (hV : HasLocalModels V n) (τ : ℍ) :
    quot Φ V τ ≠ 0 := by
  obtain ⟨R, -, hR0, hqR, -⟩ := quot_local hΦ hV τ
  rwa [hqR.self_of_nhds]

theorem tendsto_div_quot (hΦ : HasLocalModels Φ n) (hV : HasLocalModels V n) (τ : ℍ) :
    Tendsto (fun w => Φ w / V w) (𝓝[≠] (τ : ℂ)) (𝓝 (quot Φ V τ)) := by
  obtain ⟨R, hR, -, hqR, hev, -⟩ := quot_local hΦ hV τ
  have h1 : (fun w => Φ w / V w) =ᶠ[𝓝[≠] (τ : ℂ)] R := by
    filter_upwards [hev] with w hw
    rw [hw.2]; field_simp [hw.1]
  rw [hqR.self_of_nhds]
  exact ((hR.continuousAt.tendsto).mono_left nhdsWithin_le_nhds).congr' h1.symm

theorem eventually_eq_quot_mul (hΦ : HasLocalModels Φ n) (hV : HasLocalModels V n) (τ : ℍ)
    (hn : n τ = 0) : ∀ᶠ w in 𝓝 (τ : ℂ), V w ≠ 0 ∧ Φ w = quot Φ V w * V w := by
  obtain ⟨R, -, -, -, -, h⟩ := quot_local hΦ hV τ
  exact h hn

theorem quot_smul (hΦ : HasLocalModels Φ n) (hV : HasLocalModels V n) {Γ : Subgroup SL(2, ℤ)}
    (hinvΦ : ∀ γ ∈ Γ, ∀ τ : ℍ, Φ ((γ • τ : ℍ) : ℂ) = Φ τ)
    (hinvV : ∀ γ ∈ Γ, ∀ τ : ℍ, V ((γ • τ : ℍ) : ℂ) = V τ)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) (τ : ℍ) :
    quot Φ V ((γ • τ : ℍ) : ℂ) = quot Φ V τ := by
  have hτ : 0 < (τ : ℂ).im := τ.im_pos

  have hsm : Tendsto (sm γ) (𝓝[≠] (τ : ℂ)) (𝓝[≠] ((γ • τ : ℍ) : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · rw [← sm_coe]; exact (continuousAt_sm γ hτ).tendsto.mono_left nhdsWithin_le_nhds
    · have h1 : ∀ᶠ u in 𝓝[≠] (τ : ℂ), u ∈ 𝕌 :=
        mem_nhdsWithin_of_mem_nhds (isOpen_upperHalfPlaneSet.mem_nhds (mem_U τ))
      filter_upwards [h1, self_mem_nhdsWithin] with u hu hne
      intro heq
      rw [mem_singleton_iff, ← sm_coe] at heq
      exact hne (sm_inj γ hu hτ heq)
  have h1 := (tendsto_div_quot hΦ hV (γ • τ)).comp hsm
  have h2 : ((fun w => Φ w / V w) ∘ sm γ) =ᶠ[𝓝[≠] (τ : ℂ)] fun w => Φ w / V w := by
    have h1 : ∀ᶠ u in 𝓝[≠] (τ : ℂ), u ∈ 𝕌 :=
      mem_nhdsWithin_of_mem_nhds (isOpen_upperHalfPlaneSet.mem_nhds (mem_U τ))
    filter_upwards [h1] with u hu
    simp only [Function.comp, sm]
    rw [hinvΦ γ hγ, hinvV γ hγ, coe_ofComplex hu]
  exact tendsto_nhds_unique (h1.congr' h2) (tendsto_div_quot hΦ hV τ)

end LocalModels

section Divisor

variable {Γ : Subgroup SL(2, ℤ)} (S : Finset ℍ) (n : ℍ → ℤ)
  (hcov : ∀ τ : ℍ, n τ ≠ 0 → ∃ s ∈ S, ∃ γ : Γ, (γ : SL(2, ℤ)) • s = τ)
include hcov

theorem exists_height_n_eq_zero (σ : SL(2, ℤ)) :
    ∃ Y : ℝ, 0 < Y ∧ ∀ τ : ℍ, Y < τ.im → n (σ • τ) = 0 := by
  refine ⟨1 + ∑ s ∈ S, max s.im s.im⁻¹, by positivity, fun τ hτ => ?_⟩
  by_contra hne
  obtain ⟨s, hs, γ, hγ⟩ := hcov _ hne
  have hτeq : τ = (σ⁻¹ * (γ : SL(2, ℤ))) • s := by
    rw [mul_smul, hγ, inv_smul_smul]
  have h1 := im_smul_le_max (σ⁻¹ * (γ : SL(2, ℤ))) s
  rw [← hτeq] at h1
  have h2 : max s.im s.im⁻¹ ≤ ∑ t ∈ S, max t.im t.im⁻¹ :=
    Finset.single_le_sum (f := fun t : ℍ => max t.im t.im⁻¹) (fun t _ => by positivity) hs
  linarith

scoped instance countable_SL2Z : Countable SL(2, ℤ) := by
  have : Function.Injective (fun γ : SL(2, ℤ) => fun i j => (γ : Matrix (Fin 2) (Fin 2) ℤ) i j) := by
    intro a b h
    ext i j
    exact congrFun (congrFun h i) j
  exact this.countable

theorem countable_divisor : {z : ℂ | ∃ hz : 0 < z.im, n ⟨z, hz⟩ ≠ 0}.Countable := by
  have hsub : {z : ℂ | ∃ hz : 0 < z.im, n ⟨z, hz⟩ ≠ 0} ⊆
      ⋃ s ∈ S, Set.range fun γ : Γ => (((γ : SL(2, ℤ)) • s : ℍ) : ℂ) := by
    rintro z ⟨hz, hn⟩
    obtain ⟨s, hs, γ, hγ⟩ := hcov _ hn
    refine Set.mem_iUnion₂.2 ⟨s, hs, γ, ?_⟩
    show (((γ : SL(2, ℤ)) • s : ℍ) : ℂ) = z
    rw [hγ]
  refine Set.Countable.mono hsub ?_
  exact Set.Countable.biUnion S.countable_toSet fun s _ => Set.countable_range _

theorem volume_divisor : volume {z : ℂ | ∃ hz : 0 < z.im, n ⟨z, hz⟩ ≠ 0} = 0 :=
  (countable_divisor S n hcov).measure_zero volume

end Divisor

section CuspTransfer

variable {Φ V : ℂ → ℂ} {n : ℍ → ℤ}

theorem eventually_atImInfty {p : ℍ → Prop} {Y : ℝ} (h : ∀ τ : ℍ, Y < τ.im → p τ) :
    ∀ᶠ τ in atImInfty, p τ := by
  rw [Filter.Eventually, UpperHalfPlane.atImInfty_mem]
  exact ⟨Y + 1, fun τ hτ => h τ (by linarith)⟩

theorem quot_eq_of_high (hΦ : HasLocalModels Φ n) (hV : HasLocalModels V n) (σ : SL(2, ℤ))
    {Y : ℝ} (hY : ∀ τ : ℍ, Y < τ.im → n (σ • τ) = 0)
    (hV1 : ∀ z : ℂ, Y < z.im → V (sm σ z) = 1) {z : ℂ} (hz0 : 0 < z.im) (hz : Y < z.im) :
    quot Φ V (sm σ z) = Φ (sm σ z) := by
  have hn : n (σ • ofComplex z) = 0 := hY _ (by rwa [UpperHalfPlane.im, coe_ofComplex hz0])
  have := (eventually_eq_quot_mul hΦ hV (σ • ofComplex z) hn).self_of_nhds
  change V (sm σ z) ≠ 0 ∧ Φ (sm σ z) = quot Φ V (sm σ z) * V (sm σ z) at this
  rw [this.2, hV1 z hz, mul_one]

theorem tendsto_quot_smul (hΦ : HasLocalModels Φ n) (hV : HasLocalModels V n) (σ : SL(2, ℤ))
    {Y : ℝ} (hY0 : 0 < Y) (hY : ∀ τ : ℍ, Y < τ.im → n (σ • τ) = 0)
    (hV1 : ∀ z : ℂ, Y < z.im → V (sm σ z) = 1) {c : ℂ}
    (hc : Tendsto (fun τ : ℍ => Φ ((σ • τ : ℍ) : ℂ)) atImInfty (𝓝 c)) :
    Tendsto (fun τ : ℍ => quot Φ V ((σ • τ : ℍ) : ℂ)) atImInfty (𝓝 c) := by
  refine hc.congr' ?_
  refine eventually_atImInfty (Y := Y) fun τ hτ => ?_
  have := quot_eq_of_high hΦ hV σ hY hV1 τ.im_pos hτ
  rw [sm_coe] at this
  exact this.symm

theorem tendsto_fderiv_quot_smul (hΦ : HasLocalModels Φ n) (hV : HasLocalModels V n)
    (σ : SL(2, ℤ)) {Y : ℝ} (hY0 : 0 < Y) (hY : ∀ τ : ℍ, Y < τ.im → n (σ • τ) = 0)
    (hV1 : ∀ z : ℂ, Y < z.im → V (sm σ z) = 1)
    (hd : Tendsto (fun τ : ℍ => fderiv ℝ (fun u : ℂ => Φ (sm σ u)) (τ : ℂ)) atImInfty (𝓝 0)) :
    Tendsto (fun τ : ℍ => fderiv ℝ (fun u : ℂ => quot Φ V (sm σ u)) (τ : ℂ)) atImInfty (𝓝 0) := by
  refine hd.congr' ?_
  refine eventually_atImInfty (Y := Y) fun τ hτ => ?_
  have hopen : IsOpen {u : ℂ | Y < u.im} := isOpen_lt continuous_const Complex.continuous_im
  have hev : (fun u : ℂ => quot Φ V (sm σ u)) =ᶠ[𝓝 (τ : ℂ)] fun u => Φ (sm σ u) := by
    filter_upwards [hopen.mem_nhds (show (τ : ℂ) ∈ {u : ℂ | Y < u.im} from hτ)] with u hu
    exact quot_eq_of_high hΦ hV σ hY hV1 (lt_trans hY0 hu) hu
  exact (hev.fderiv_eq).symm

end CuspTransfer

section Density

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]

theorem g_smul (g : CuspForm Γ 2) {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) (τ : ℍ) :
    g (γ • τ) = denom (γ : GL (Fin 2) ℝ) τ ^ 2 * g τ := by
  have := SlashInvariantForm.slash_action_eqn_SL'' g hγ τ
  simpa using this

def Pd (L : ℂ → ℂ) (g : CuspForm Γ 2) (τ : ℍ) : ℂ :=
  dbar L τ * g τ * ((τ.im : ℂ) ^ 2)

theorem Pd_smul {L : ℂ → ℂ} (hL : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℝ L z)
    (c : SL(2, ℤ) → ℂ) (hLc : ∀ γ ∈ Γ, ∀ z : ℂ, 0 < z.im → L (sm γ z) = L z + c γ)
    (g : CuspForm Γ 2) (γ : SL(2, ℤ)) (hγ : γ ∈ Γ) (τ : ℍ) :
    Pd L g (γ • τ) = Pd L g τ := by
  simp only [Pd]
  rw [dbar_smul_of_quasiperiodic hL γ (c γ) (hLc γ hγ) τ, g_smul g hγ τ,
    ModularGroup.im_smul_eq_div_normSq]
  have hD : denom (γ : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ _
  have hns : (Complex.normSq (denom (γ : GL (Fin 2) ℝ) τ) : ℂ) =
      conj (denom (γ : GL (Fin 2) ℝ) τ) * denom (γ : GL (Fin 2) ℝ) τ := by
    rw [Complex.normSq_eq_conj_mul_self]
  have hns0 : (Complex.normSq (denom (γ : GL (Fin 2) ℝ) τ) : ℂ) ≠ 0 := by
    exact_mod_cast (Complex.normSq_pos.2 hD).ne'
  push_cast
  rw [hns] at hns0 ⊢
  field_simp

theorem measurable_dbar (L : ℂ → ℂ) : Measurable (dbar L) := by
  unfold dbar
  exact ((measurable_fderiv_apply_const ℝ L 1).add
    (measurable_const.mul (measurable_fderiv_apply_const ℝ L I))).div_const _

theorem aestronglyMeasurable_Pd (L : ℂ → ℂ) (g : CuspForm Γ 2) :
    AEStronglyMeasurable (Pd L g) volume := by
  refine Measurable.aestronglyMeasurable ?_
  unfold Pd
  refine ((measurable_dbar L).comp UpperHalfPlane.continuous_coe.measurable).mul
    (CuspFormClass.holo g).continuous.measurable |>.mul ?_
  exact (Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).measurable.pow_const _

theorem exists_height_of_eventually {p : ℂ → Prop} (h : ∀ᶠ τ : ℍ in atImInfty, p (τ : ℂ)) :
    ∃ Y : ℝ, 0 < Y ∧ ∀ z : ℂ, Y ≤ z.im → p z := by
  obtain ⟨A, hA⟩ := (UpperHalfPlane.atImInfty_mem _).1 h
  refine ⟨max A 1, by positivity, fun z hz => ?_⟩
  have hz0 : 0 < z.im := lt_of_lt_of_le (by positivity) hz
  exact hA ⟨z, hz0⟩ (le_trans (le_max_left _ _) hz)

theorem cusp_bound {L Φ₀ : ℂ → ℂ} (σ : SL(2, ℤ))
    (hΦ₀d : ∀ τ : ℍ, DifferentiableAt ℝ Φ₀ (τ : ℂ))
    (hLd : ∀ τ : ℍ, HasFDerivAt L ((Φ₀ τ)⁻¹ • fderiv ℝ Φ₀ τ) τ)
    {cL : ℂ} (hLlim : Tendsto (fun τ : ℍ => L ((σ • τ : ℍ) : ℂ)) atImInfty (𝓝 cL))
    {c : ℂ} (hc : c ≠ 0) (hΦlim : Tendsto (fun τ : ℍ => Φ₀ ((σ • τ : ℍ) : ℂ)) atImInfty (𝓝 c))
    (hdec : Tendsto (fun τ : ℍ => fderiv ℝ (fun u : ℂ => Φ₀ (sm σ u)) (τ : ℂ)) atImInfty (𝓝 0)) :
    ∃ C Y : ℝ, ∀ z : ℂ, Y ≤ z.im →
      ‖L ((σ • ofComplex z : ℍ) : ℂ)‖ ≤ C ∧
        ‖fderiv ℝ (fun u : ℂ => L ((σ • ofComplex u : ℍ) : ℂ)) z‖ ≤ C := by

  have h1 : ∀ᶠ τ : ℍ in atImInfty, ‖L ((σ • τ : ℍ) : ℂ)‖ ≤ ‖cL‖ + 1 := by
    have := hLlim.norm
    filter_upwards [this.eventually (Iic_mem_nhds (lt_add_one ‖cL‖))] with τ hτ using hτ
  have h2 : ∀ᶠ τ : ℍ in atImInfty, ‖c‖ / 2 ≤ ‖Φ₀ ((σ • τ : ℍ) : ℂ)‖ := by
    have := hΦlim.norm
    have hpos : ‖c‖ / 2 < ‖c‖ := by linarith [norm_pos_iff.2 hc]
    filter_upwards [this.eventually (Ici_mem_nhds hpos)] with τ hτ using hτ
  have h3 : ∀ᶠ τ : ℍ in atImInfty, ‖fderiv ℝ (fun u : ℂ => Φ₀ (sm σ u)) (τ : ℂ)‖ ≤ 1 := by
    have := hdec.norm
    rw [norm_zero] at this
    filter_upwards [this.eventually (Iic_mem_nhds one_pos)] with τ hτ using hτ
  have h123 : ∀ᶠ τ : ℍ in atImInfty,
      ‖L (sm σ (τ : ℂ))‖ ≤ ‖cL‖ + 1 ∧ ‖c‖ / 2 ≤ ‖Φ₀ (sm σ (τ : ℂ))‖ ∧
        ‖fderiv ℝ (fun u : ℂ => Φ₀ (sm σ u)) (τ : ℂ)‖ ≤ 1 := by
    filter_upwards [h1, h2, h3] with τ a b d
    rw [sm_coe]; exact ⟨a, b, d⟩
  obtain ⟨Y, hY0, hY⟩ := exists_height_of_eventually
    (p := fun z => ‖L (sm σ z)‖ ≤ ‖cL‖ + 1 ∧ ‖c‖ / 2 ≤ ‖Φ₀ (sm σ z)‖ ∧
        ‖fderiv ℝ (fun u : ℂ => Φ₀ (sm σ u)) z‖ ≤ 1) h123
  refine ⟨max (‖cL‖ + 1) (2 / ‖c‖), Y, fun z hz => ?_⟩
  obtain ⟨a, b, d⟩ := hY z hz
  have hz0 : 0 < z.im := lt_of_lt_of_le hY0 hz
  refine ⟨le_trans a (le_max_left _ _), ?_⟩

  have hw : sm σ z = ((σ • ofComplex z : ℍ) : ℂ) := rfl
  have hΦw : DifferentiableAt ℝ Φ₀ (sm σ z) := hΦ₀d _
  have hLw : HasFDerivAt L ((Φ₀ (sm σ z))⁻¹ • fderiv ℝ Φ₀ (sm σ z)) (sm σ z) := hLd _
  have key := norm_fderiv_comp_sm_smul σ hz0 hΦw hLw
  change fderiv ℝ (fun u => L (sm σ u)) z = _ at key
  show ‖fderiv ℝ (fun u => L (sm σ u)) z‖ ≤ _
  rw [key, norm_smul, norm_inv]
  have hcpos : 0 < ‖c‖ := norm_pos_iff.2 hc
  have hΦpos : 0 < ‖Φ₀ (sm σ z)‖ := lt_of_lt_of_le (by positivity) b
  calc ‖Φ₀ (sm σ z)‖⁻¹ * ‖fderiv ℝ (fun u => Φ₀ (sm σ u)) z‖ ≤ (‖c‖ / 2)⁻¹ * 1 := by
        gcongr
    _ = 2 / ‖c‖ := by field_simp
    _ ≤ _ := le_max_right _ _

end Density

section Main

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]

@[reducible] noncomputable def fintypeQ : Fintype (SL(2, ℤ) ⧸ Γ) :=
  Subgroup.fintypeQuotientOfFiniteIndex

attribute [local instance] fintypeQ

theorem pair_mem (a : SL(2, ℤ)) (q : SL(2, ℤ) ⧸ Γ) :
    (Quotient.out (a • q))⁻¹ * a * Quotient.out q ∈ Γ := by
  have h : (QuotientGroup.mk (Quotient.out (a • q)) : SL(2, ℤ) ⧸ Γ) =
      QuotientGroup.mk (a * Quotient.out q) := by
    rw [QuotientGroup.out_eq']
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  rw [mul_assoc]
  exact QuotientGroup.eq.mp h

noncomputable def gT (q : SL(2, ℤ) ⧸ Γ) : Γ :=
  ⟨(Quotient.out (ModularGroup.T • q))⁻¹ * ModularGroup.T * Quotient.out q, pair_mem _ q⟩

noncomputable def gS (q : SL(2, ℤ) ⧸ Γ) : Γ :=
  ⟨(Quotient.out (ModularGroup.S • q))⁻¹ * ModularGroup.S * Quotient.out q, pair_mem _ q⟩

theorem continuous_mul_of_tsupport_subset {f ψ : ℂ → ℂ}
    (hf : ContinuousOn f 𝕌) (hψ : Continuous ψ) (hψV : tsupport ψ ⊆ 𝕌) :
    Continuous fun z => f z * ψ z := by
  refine continuous_iff_continuousAt.2 fun z => ?_
  by_cases hz : z ∈ 𝕌
  · exact (hf.continuousAt (isOpen_upperHalfPlaneSet.mem_nhds hz)).mul hψ.continuousAt
  · have hz' : z ∉ tsupport ψ := fun h' => hz (hψV h')
    have h0 : ψ =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.1 hz'
    have : (fun w => f w * ψ w) =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [h0] with w hw
      simp [hw]
    exact (continuousAt_congr this).2 continuousAt_const

theorem integrable_mul_of_tsupport_subset {f ψ : ℂ → ℂ}
    (hf : ContinuousOn f 𝕌) (hψ : Continuous ψ) (hψs : HasCompactSupport ψ)
    (hψV : tsupport ψ ⊆ 𝕌) : Integrable fun z => f z * ψ z :=
  (continuous_mul_of_tsupport_subset hf hψ hψV).integrable_of_hasCompactSupport hψs.mul_left

theorem differentiableAt_of_localModel {V : ℂ → ℂ} {n : ℍ → ℤ} (hV : HasLocalModels V n) (τ : ℍ)
    (hn : n τ = 0) : DifferentiableAt ℝ V (τ : ℂ) := by
  obtain ⟨Θ, hΘ, -, hVe⟩ := hV τ
  rw [hn] at hVe
  have : V =ᶠ[𝓝 (τ : ℂ)] Θ := hVe.trans (Eventually.of_forall fun w => by simp)
  exact (hΘ.differentiableAt (by norm_num)).congr_of_eventuallyEq this

theorem scalar_identity (A B : ℂ) :
    2 / (π : ℂ) * (1 / 2 * (1 / (2 * I) * (I * (2 * π * I * A) + 1 / 2 * (2 * π * I * B)))) =
      I * A + 1 / 2 * B := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

theorem main (hneg : (-1 : SL(2, ℤ)) ∈ Γ) (Φ : ℂ → ℂ) (S : Finset ℍ) (n : ℍ → ℤ)
    (hloc : ∀ τ : ℍ, ∃ Ψ : ℂ → ℂ, ContDiffAt ℝ 1 Ψ (τ : ℂ) ∧ Ψ τ ≠ 0 ∧
      Φ =ᶠ[𝓝 (τ : ℂ)] fun z => (z - τ) ^ (n τ) * Ψ z)
    (hinv : ∀ (γ : Γ) (τ : ℍ), Φ (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) = Φ τ)
    (hcuspΦ : ∀ σ : SL(2, ℤ), ∃ c : ℂ, c ≠ 0 ∧
      Tendsto (fun τ : ℍ => Φ ((σ • τ : ℍ) : ℂ)) atImInfty (𝓝 c))
    (hdecay : ∀ σ : SL(2, ℤ), Tendsto (fun τ : ℍ =>
      fderiv ℝ (fun u : ℂ => Φ ((σ • ofComplex u : ℍ) : ℂ)) (τ : ℂ)) atImInfty (𝓝 0))
    (hn : ∀ (γ : Γ) (τ : ℍ), n ((γ : SL(2, ℤ)) • τ) = n τ)
    (hcov : ∀ τ : ℍ, n τ ≠ 0 → ∃ s ∈ S, ∃ γ : Γ, (γ : SL(2, ℤ)) • s = τ)
    (hinj : ∀ s ∈ S, ∀ t ∈ S, (∃ γ : Γ, (γ : SL(2, ℤ)) • s = t) → s = t)
    (hdvd : ∀ s ∈ S, (Nat.card (MulAction.stabilizer Γ s) : ℤ) ∣ 2 * n s)
    (hdeg : ∑ s ∈ S, (n s : ℂ) / (Nat.card (MulAction.stabilizer Γ s) : ℂ) = 0) :
    (∀ (T : ℝ) (g : CuspForm Γ 2),
      Integrable fun z : ℂ => Eg Γ g z / Φ z *
        (fderiv ℝ Φ z 1 * fderiv ℝ (hT Γ T) z I - fderiv ℝ Φ z I * fderiv ℝ (hT Γ T) z 1)) ∧
    ∃ Λ ∈ ModularCurve.periodLatticeOf Γ,
      ∀ g : CuspForm Γ 2,
        Tendsto (fun T : ℝ =>
          I / π * (∫ z : ℂ, Eg Γ g z / Φ z *
            (fderiv ℝ Φ z 1 * fderiv ℝ (hT Γ T) z I - fderiv ℝ Φ z I * fderiv ℝ (hT Γ T) z 1)) +
          2 * ∑ᶠ a : ℂ, ((n (ofComplex a) : ℤ) : ℂ) * Eg Γ g a * hT Γ T a) atTop
          (𝓝 (Λ g + ∑ s ∈ S, 2 * (n s : ℂ) / (Nat.card (MulAction.stabilizer Γ s) : ℂ) *
            ModularCurve.periodAlongOf Γ UpperHalfPlane.I s g)) := by
  classical

  obtain ⟨V, hVinv, hVloc, hVcusp, hVint, hVlim⟩ :=
    ModularCurve.exists_invariant_localModel_tendsto_integral_dbarLogDeriv_smoothedFundamental_periodAlongOf
      Γ hneg S n hn hcov hinj hdvd hdeg (hT Γ) (fun T z => rfl)
  have hΦL : HasLocalModels Φ n := hloc
  have hVL : HasLocalModels V n := hVloc
  have hinv' : ∀ γ ∈ Γ, ∀ τ : ℍ, Φ ((γ • τ : ℍ) : ℂ) = Φ τ := fun γ hγ τ => hinv ⟨γ, hγ⟩ τ
  have hVinv' : ∀ γ ∈ Γ, ∀ τ : ℍ, V ((γ • τ : ℍ) : ℂ) = V τ := fun γ hγ τ => hVinv ⟨γ, hγ⟩ τ

  set Φ₀ : ℂ → ℂ := quot Φ V with hΦ₀def
  have hΦ₀cd : ∀ τ : ℍ, ContDiffAt ℝ 1 Φ₀ τ := contDiffAt_quot hΦL hVL
  have hΦ₀d : ∀ τ : ℍ, DifferentiableAt ℝ Φ₀ (τ : ℂ) := fun τ =>
    (hΦ₀cd τ).differentiableAt (by norm_num)
  have hΦ₀ne : ∀ τ : ℍ, Φ₀ τ ≠ 0 := quot_ne_zero hΦL hVL
  have hΦ₀inv : ∀ γ ∈ Γ, ∀ τ : ℍ, Φ₀ ((γ • τ : ℍ) : ℂ) = Φ₀ τ := fun γ hγ τ =>
    quot_smul hΦL hVL hinv' hVinv' hγ τ

  have hY : ∀ σ : SL(2, ℤ), ∃ Y : ℝ, 0 < Y ∧ (∀ τ : ℍ, Y < τ.im → n (σ • τ) = 0) ∧
      ∀ z : ℂ, Y < z.im → V (sm σ z) = 1 := by
    intro σ
    obtain ⟨Y₁, hY₁, h1⟩ := exists_height_n_eq_zero S n hcov σ
    obtain ⟨Y₂, h2⟩ := hVcusp σ
    refine ⟨max Y₁ Y₂, lt_max_of_lt_left hY₁, fun τ hτ => h1 τ (lt_of_le_of_lt (le_max_left _ _) hτ),
      fun z hz => h2 z (lt_of_le_of_lt (le_max_right _ _) hz)⟩
  have hΦ₀cusp : ∀ σ : SL(2, ℤ), ∃ c : ℂ, c ≠ 0 ∧
      Tendsto (fun τ : ℍ => Φ₀ ((σ • τ : ℍ) : ℂ)) atImInfty (𝓝 c) := by
    intro σ
    obtain ⟨c, hc, hcT⟩ := hcuspΦ σ
    obtain ⟨Y, hY0, hYn, hYV⟩ := hY σ
    exact ⟨c, hc, tendsto_quot_smul hΦL hVL σ hY0 hYn hYV hcT⟩

  obtain ⟨L, m, hmpar, hLcd, hLd, hLexp, hLper, hLlim⟩ :=
    ModularCurve.exists_exp_eq_of_invariant_ne_zero_isParabolicHom Γ Φ₀ hΦ₀cd hΦ₀ne
      hΦ₀inv hΦ₀cusp
  have hLdiff : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℝ L z := fun z hz =>
    (hLd ⟨z, hz⟩).differentiableAt
  set c : SL(2, ℤ) → ℂ := fun γ =>
    if h : γ ∈ Γ then 2 * π * I * (m (Additive.ofMul (⟨γ, h⟩ : Γ)) : ℂ) else 0 with hcdef
  have hc_of_mem : ∀ (γ : SL(2, ℤ)) (hγ : γ ∈ Γ),
      c γ = 2 * π * I * (m (Additive.ofMul (⟨γ, hγ⟩ : Γ)) : ℂ) := fun γ hγ => dif_pos hγ
  have hLcH : ∀ γ ∈ Γ, ∀ τ : ℍ, L ((γ • τ : ℍ) : ℂ) = L τ + c γ := by
    intro γ hγ τ
    rw [hc_of_mem γ hγ]
    exact hLper ⟨γ, hγ⟩ τ
  have hLc' : ∀ γ ∈ Γ, ∀ z : ℂ, 0 < z.im → L (sm γ z) = L z + c γ := by
    intro γ hγ z hz
    have := hLcH γ hγ (ofComplex z)
    rwa [coe_ofComplex hz] at this
  have hLon : ContDiffOn ℝ 1 L 𝕌 := fun z hz => (hLcd ⟨z, hz⟩).contDiffWithinAt
  have hL'cont : ContinuousOn (fderiv ℝ L) 𝕌 :=
    hLon.continuousOn_fderiv_of_isOpen isOpen_upperHalfPlaneSet le_rfl
  have hbd : ∀ σ : SL(2, ℤ), ∃ C Y : ℝ, ∀ z : ℂ, Y ≤ z.im →
      ‖L ((σ • ofComplex z : ℍ) : ℂ)‖ ≤ C ∧
        ‖fderiv ℝ (fun u : ℂ => L ((σ • ofComplex u : ℍ) : ℂ)) z‖ ≤ C := by
    intro σ
    obtain ⟨cL, hcL⟩ := hLlim σ
    obtain ⟨c₀, hc₀, hΦlim⟩ := hΦ₀cusp σ
    obtain ⟨Y, hY0, hYn, hYV⟩ := hY σ
    exact cusp_bound σ hΦ₀d hLd hcL hc₀ hΦlim
      (tendsto_fderiv_quot_smul hΦL hVL σ hY0 hYn hYV (hdecay σ))

  obtain ⟨Λ, hΛmem, hΛeq⟩ :=
    ModularCurve.exists_mem_periodLatticeOf_eq_sum_intCast_mul_edgeIntegral_of_isParabolicHom
      Γ hneg gT gS (fun q => rfl) (fun q => rfl) m hmpar

  have hlocU : ∀ τ ∈ 𝕌, ∃ Ψ : ℂ → ℂ, ContDiffAt ℝ 1 Ψ τ ∧ Ψ τ ≠ 0 ∧
      Φ =ᶠ[𝓝 τ] fun z => (z - τ) ^ ((fun a : ℂ => n (ofComplex a)) τ) * Ψ z := by
    intro τ hτ
    obtain ⟨Ψ, h1, h2, h3⟩ := hloc ⟨τ, hτ⟩
    refine ⟨Ψ, h1, h2, ?_⟩
    simp only [ofComplex_apply_of_im_pos hτ]
    exact h3
  have hA : ∀ (T : ℝ) (g : CuspForm Γ 2), _ := fun T g =>
    Complex.integral_logDeriv_wedge_add_finsum_eq_integral_dbarLogDeriv 𝕌 isOpen_upperHalfPlaneSet
      Φ (fun a : ℂ => n (ofComplex a)) hlocU (Eg Γ g) (kC Γ g) (fun z hz => hasDerivAt_Eg Γ g hz)
      (hT Γ T) (hT_props Γ T).1 (hT_props Γ T).2.1 (hT_props Γ T).2.2
  refine ⟨fun T g => (hA T g).1, Λ, hΛmem, fun g => ?_⟩

  have hfun : (fun T : ℝ =>
      I / π * (∫ z : ℂ, Eg Γ g z / Φ z *
        (fderiv ℝ Φ z 1 * fderiv ℝ (hT Γ T) z I - fderiv ℝ Φ z I * fderiv ℝ (hT Γ T) z 1)) +
      2 * ∑ᶠ a : ℂ, ((n (ofComplex a) : ℤ) : ℂ) * Eg Γ g a * hT Γ T a) =
      fun T : ℝ => 2 / π * ∫ z : ℂ, kC Γ g z * hT Γ T z * (dbar Φ z / Φ z) :=
    funext fun T => (hA T g).2.2
  rw [hfun]

  have hae : ∀ T : ℝ, (fun z : ℂ => kC Γ g z * hT Γ T z * (dbar Φ z / Φ z)) =ᵐ[volume]
      fun z => kC Γ g z * dbar L z * hT Γ T z + kC Γ g z * hT Γ T z * (dbar V z / V z) := by
    intro T
    have h0 := volume_divisor S n hcov
    rw [measure_eq_zero_iff_ae_notMem] at h0
    filter_upwards [h0] with z hzD
    by_cases hz : 0 < z.im
    · have hn0 : n ⟨z, hz⟩ = 0 := by
        by_contra h; exact hzD ⟨hz, h⟩
      set τ : ℍ := ⟨z, hz⟩
      have hev := eventually_eq_quot_mul hΦL hVL τ hn0
      have hVz : V z ≠ 0 := (hev.self_of_nhds).1
      have hΦz : Φ z = Φ₀ z * V z := (hev.self_of_nhds).2
      have hΦeq : Φ =ᶠ[𝓝 z] fun w => Φ₀ w * V w := hev.mono fun w hw => hw.2
      have hVd : DifferentiableAt ℝ V z := differentiableAt_of_localModel hVL τ hn0
      have hΦ₀z : Φ₀ z ≠ 0 := hΦ₀ne τ
      have hfd : fderiv ℝ Φ z = Φ₀ z • fderiv ℝ V z + V z • fderiv ℝ Φ₀ z := by
        rw [hΦeq.fderiv_eq]; exact fderiv_mul (hΦ₀d τ) hVd
      have hfL : fderiv ℝ Φ₀ z = Φ₀ z • fderiv ℝ L z := by
        rw [(hLd τ).fderiv, smul_smul, mul_inv_cancel₀ hΦ₀z, one_smul]
      have hdb : dbar Φ z = Φ₀ z * dbar V z + V z * (Φ₀ z * dbar L z) := by
        simp only [dbar, hfd, hfL, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
          smul_eq_mul]
        ring
      rw [hdb, hΦz]
      field_simp
      ring
    · have : hT Γ T z = 0 := hT_eq_zero_of_notMem Γ hz
      simp [this]

  have hdbarL : ContinuousOn (dbar L) 𝕌 := by
    have h1 : ContinuousOn (fun z => fderiv ℝ L z 1) 𝕌 := hL'cont.clm_apply continuousOn_const
    have h2 : ContinuousOn (fun z => fderiv ℝ L z I) 𝕌 := hL'cont.clm_apply continuousOn_const
    exact (h1.add (continuousOn_const.mul h2)).div_const _
  have hint1 : ∀ T : ℝ, Integrable fun z => kC Γ g z * dbar L z * hT Γ T z := fun T =>
    integrable_mul_of_tsupport_subset ((continuousOn_kC Γ g).mul hdbarL)
      (hT_props Γ T).1.continuous (hT_props Γ T).2.1 (hT_props Γ T).2.2
  have hint2 : ∀ T : ℝ, Integrable fun z => kC Γ g z * hT Γ T z * (dbar V z / V z) := fun T =>
    hVint T g
  have hsplit : (fun T : ℝ => 2 / π * ∫ z : ℂ, kC Γ g z * hT Γ T z * (dbar Φ z / Φ z)) =
      fun T : ℝ => 2 / π * (∫ z : ℂ, kC Γ g z * dbar L z * hT Γ T z) +
        2 / π * ∫ z : ℂ, kC Γ g z * hT Γ T z * (dbar V z / V z) := by
    funext T
    rw [integral_congr_ae (hae T), integral_add (hint1 T) (hint2 T), mul_add]
  rw [hsplit]
  refine Tendsto.add ?_ (hVlim g)

  have hP := Pd_smul hLdiff c hLc' g
  obtain ⟨hPi, hCeq⟩ :=
    ModularCurve.integral_dbar_mul_cuspForm_gammaFundamentalSet_eq_sidePairing Γ
      hneg L (fderiv ℝ L) (fun z hz => (hLdiff z hz).hasFDerivAt) hL'cont c hLcH hbd
      g (fun q z => g ((Quotient.out q)⁻¹ • ofComplex z) /
        denom (((Quotient.out q)⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) (ofComplex z) ^ 2) (fun q z => rfl)
  have hX2 := FLT.Gamma0FundamentalSet.tendsto_integral_mul_smoothedFundamental (Γ := Γ)
    hneg (Pd L g) hP (aestronglyMeasurable_Pd L g) hPi

  have hpt : ∀ (T : ℝ) (z : ℂ), Pd L g (ofComplex z) *
      (((z.im ^ 2)⁻¹ * ModularCurve.smoothedFundamental Γ T z : ℝ) : ℂ) =
      kC Γ g z * dbar L z * hT Γ T z := by
    intro T z
    by_cases hz : 0 < z.im
    · have h1 : ((ofComplex z : ℍ) : ℂ) = z := coe_ofComplex hz
      have h2 : (ofComplex z).im = z.im := by
        rw [ofComplex_apply_of_im_pos hz]; rfl
      have hz0 : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hz.ne'
      simp only [Pd, kC, hT, h1, h2]
      push_cast
      field_simp
    · have hz' : z ∉ 𝕌 := hz
      rw [hT_eq_zero_of_notMem Γ hz', smoothedFundamental_eq_zero_of_notMem Γ hz']
      simp
  have hX2' : Tendsto (fun T : ℝ => ∫ z : ℂ, kC Γ g z * dbar L z * hT Γ T z) atTop
      (𝓝 ((1 / 2 : ℂ) * ∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ, Pd L g τ)) := by
    refine hX2.congr fun T => ?_
    exact integral_congr_ae (Eventually.of_forall (hpt T))
  have hval : 2 / (π : ℂ) * ((1 / 2 : ℂ) *
      ∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ, Pd L g τ) = Λ g := by
    have hCeq' : (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ, Pd L g τ) = _ := hCeq
    rw [hCeq']
    have hcT : ∀ q : SL(2, ℤ) ⧸ Γ,
        c ((Quotient.out (ModularGroup.T • q))⁻¹ * ModularGroup.T * Quotient.out q) =
          2 * π * I * (m (Additive.ofMul (gT q)) : ℂ) := fun q => hc_of_mem _ (pair_mem _ q)
    have hcS : ∀ q : SL(2, ℤ) ⧸ Γ,
        c ((Quotient.out (ModularGroup.S • q))⁻¹ * ModularGroup.S * Quotient.out q) =
          2 * π * I * (m (Additive.ofMul (gS q)) : ℂ) := fun q => hc_of_mem _ (pair_mem _ q)
    simp_rw [hcT, hcS, mul_assoc (2 * π * I), ← Finset.mul_sum]
    rw [← hΛeq g _ (fun q z => rfl), scalar_identity]
  rw [← hval]
  exact hX2'.const_mul _

end Main

end ModularCurve.WindingReciprocity
p2m_reactivate "P2MW.S_ModularCurve_exists_mem_periodLatticeOf_tendsto_windingPairing_smoothedFundamental.ModularCurve P2MW.S_ModularCurve_exists_mem_periodLatticeOf_tendsto_windingPairing_smoothedFundamental.ModularCurve.WindingReciprocity"
p2m_reactivate "P2MW.S_ModularCurve_exists_mem_periodLatticeOf_tendsto_windingPairing_smoothedFundamental.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_mem_periodLatticeOf_tendsto_windingPairing_smoothedFundamental.ModularCurve P2MW.S_ModularCurve_exists_mem_periodLatticeOf_tendsto_windingPairing_smoothedFundamental.ModularCurve.WindingReciprocity"

open UpperHalfPlane MeasureTheory Filter
open scoped MatrixGroups Topology

open ModularCurve.WindingReciprocity in
theorem solution
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hneg : (-1 : SL(2, ℤ)) ∈ Γ) (Φ : ℂ → ℂ) (S : Finset ℍ) (n : ℍ → ℤ)
    (hloc : ∀ τ : ℍ, ∃ Ψ : ℂ → ℂ, ContDiffAt ℝ 1 Ψ (τ : ℂ) ∧ Ψ τ ≠ 0 ∧
      Φ =ᶠ[𝓝 (τ : ℂ)] fun z => (z - τ) ^ (n τ) * Ψ z)
    (hinv : ∀ (γ : Γ) (τ : ℍ), Φ (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) = Φ τ)
    (hcuspΦ : ∀ σ : SL(2, ℤ), ∃ c : ℂ, c ≠ 0 ∧
      Tendsto (fun τ : ℍ => Φ ((σ • τ : ℍ) : ℂ)) atImInfty (𝓝 c))
    (hdecay : ∀ σ : SL(2, ℤ), Tendsto (fun τ : ℍ =>
      fderiv ℝ (fun u : ℂ => Φ ((σ • ofComplex u : ℍ) : ℂ)) (τ : ℂ)) atImInfty (𝓝 0))
    (hn : ∀ (γ : Γ) (τ : ℍ), n ((γ : SL(2, ℤ)) • τ) = n τ)
    (hcov : ∀ τ : ℍ, n τ ≠ 0 → ∃ s ∈ S, ∃ γ : Γ, (γ : SL(2, ℤ)) • s = τ)
    (hinj : ∀ s ∈ S, ∀ t ∈ S,
      (∃ γ : Γ, (γ : SL(2, ℤ)) • s = t) → s = t)
    (hdvd : ∀ s ∈ S, (Nat.card (MulAction.stabilizer (Γ) s) : ℤ) ∣ 2 * n s)
    (hdeg : ∑ s ∈ S, (n s : ℂ) /
      (Nat.card (MulAction.stabilizer (Γ) s) : ℂ) = 0)
    (h : ℝ → ℂ → ℂ)
    (hh : ∀ T z, h T z = (ModularCurve.smoothedFundamental (Γ) T z : ℂ))
    (E : CuspForm (Γ) 2 → ℂ → ℂ)
    (hE : ∀ g z, E g z = ModularCurve.periodAlongOf Γ UpperHalfPlane.I (ofComplex z) g) :
    (∀ (T : ℝ) (g : CuspForm (Γ) 2),
      Integrable fun z : ℂ => E g z / Φ z *
        (fderiv ℝ Φ z 1 * fderiv ℝ (h T) z Complex.I - fderiv ℝ Φ z Complex.I * fderiv ℝ (h T) z 1)) ∧
    ∃ Λ ∈ ModularCurve.periodLatticeOf Γ,
      ∀ g : CuspForm (Γ) 2,
        Tendsto (fun T : ℝ =>
          Complex.I / Real.pi * (∫ z : ℂ, E g z / Φ z *
            (fderiv ℝ Φ z 1 * fderiv ℝ (h T) z Complex.I -
              fderiv ℝ Φ z Complex.I * fderiv ℝ (h T) z 1)) +
          2 * ∑ᶠ a : ℂ, ((n (ofComplex a) : ℤ) : ℂ) * E g a * h T a) atTop
          (𝓝 (Λ g + ∑ s ∈ S, 2 * (n s : ℂ) /
            (Nat.card (MulAction.stabilizer (Γ) s) : ℂ) *
              ModularCurve.periodAlongOf Γ UpperHalfPlane.I s g)) := by
  have hE' : E = Eg Γ := by
    funext g z; exact hE g z
  have hh' : h = hT Γ := by
    funext T z; exact hh T z
  subst hE' hh'
  exact main hneg Φ S n hloc hinv hcuspΦ hdecay hn hcov hinj hdvd hdeg

end S_ModularCurve_exists_mem_periodLatticeOf_tendsto_windingPairing_smoothedFundamental
end P2MW
export P2MW.S_ModularCurve_exists_mem_periodLatticeOf_tendsto_windingPairing_smoothedFundamental (solution)
