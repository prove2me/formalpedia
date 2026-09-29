-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.rsGlobalIntegral_eq_rsGlobalIntegral_transposeInvN_dualForm_and_isFundamentalDomain_preimage
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/d6284d70-a806-59e3-b436-524f7247bd3c

import Definitions.Def_LanglandsTunnell_RSGlobalIntegral
import Definitions.Def_LanglandsTunnell_HonestLDatum
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_rsGlobalIntegral_eq_rsGlobalIntegral_transposeInvN_dualForm_and_isFundamentalDomain_preimage

set_option autoImplicit false

noncomputable section

p2m_open "MeasureTheory Measure MeasureTheory.Measure Matrix"

namespace LanglandsTunnell
namespace RankinSelberg
p2m_export "LanglandsTunnell.RankinSelberg" "iotaGL_transposeInvN rsGlobalIntegral rsGlobalIntegral_def"
namespace RSTranspose
p2m_open "LanglandsTunnell.RankinSelberg LanglandsTunnell"

section Haar

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [MeasurableSpace G] [BorelSpace G]

theorem map_eq_self_of_involutive (μ : Measure G) [IsHaarMeasure μ] [Regular μ] (θ : G ≃ₜ* G)
    (hθ : ∀ g, θ (θ g) = g) : Measure.map θ μ = μ := by
  haveI : (Measure.map θ μ).Regular := Regular.map θ.toHomeomorph
  let c : ENNReal := haarScalarFactor (Measure.map θ μ) μ
  have hc : Measure.map θ μ = c • μ := isMulLeftInvariant_eq_smul_of_regular (Measure.map θ μ) μ
  have hmeas : Measurable θ := θ.continuous.measurable
  have hcomp : (θ : G → G) ∘ (θ : G → G) = id := funext hθ
  have h2 : Measure.map θ (Measure.map θ μ) = c ^ 2 • μ := by
    rw [hc, Measure.map_smul, hc, smul_smul, pow_two]
  have μeq : μ = c ^ 2 • μ := by
    rw [Measure.map_map hmeas hmeas, hcomp, Measure.map_id] at h2
    exact h2
  have K : TopologicalSpace.PositiveCompacts G := Classical.arbitrary _
  have hK : c ^ 2 * μ K = 1 ^ 2 * μ K := by
    conv_rhs => rw [μeq]
    simp
  have hc2 : c ^ 2 = 1 ^ 2 :=
    (ENNReal.mul_left_inj (measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
      K.isCompact.measure_lt_top.ne).1 hK
  have hc1 : c = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective hc2
  rw [hc, hc1, one_smul]

end Haar

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.CubicInduction

section Theta

variable {R : Type*} [CommRing R] [TopologicalSpace R]

theorem continuous_transposeInvN : Continuous (transposeInvN (Fin 2) : GL (Fin 2) R → GL (Fin 2) R) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun g : GL (Fin 2) R =>
      ((transposeInvN (Fin 2) g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)
    have : (fun g : GL (Fin 2) R => ((transposeInvN (Fin 2) g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R))
        = fun g => (((g⁻¹ : GL (Fin 2) R)) : Matrix (Fin 2) (Fin 2) R)ᵀ := funext fun g => rfl
    rw [this]
    exact Units.continuous_coe_inv.matrix_transpose
  · show Continuous fun g : GL (Fin 2) R =>
      (((transposeInvN (Fin 2) g)⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)
    have : (fun g : GL (Fin 2) R => (((transposeInvN (Fin 2) g)⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R))
        = fun g => ((g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)ᵀ := funext fun g => rfl
    rw [this]
    exact Units.continuous_val.matrix_transpose

def thetaGL2 : GL (Fin 2) R ≃ₜ* GL (Fin 2) R where
  toFun := transposeInvN (Fin 2)
  invFun := transposeInvN (Fin 2)
  left_inv := transposeInvN_transposeInvN (Fin 2)
  right_inv := transposeInvN_transposeInvN (Fin 2)
  map_mul' := transposeInvN_mul (Fin 2)
  continuous_toFun := continuous_transposeInvN
  continuous_invFun := continuous_transposeInvN

@[scoped simp] theorem thetaGL2_apply (g : GL (Fin 2) R) : thetaGL2 g = transposeInvN (Fin 2) g := rfl

theorem thetaGL2_thetaGL2 (g : GL (Fin 2) R) : thetaGL2 (thetaGL2 g) = g :=
  transposeInvN_transposeInvN (Fin 2) g

omit [TopologicalSpace R] in

theorem det_transposeInvN (g : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.det (transposeInvN (Fin 2) g) = (Matrix.GeneralLinearGroup.det g)⁻¹ := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_transposeInvN, Matrix.det_transpose,
    ← Matrix.GeneralLinearGroup.val_det_apply, map_inv]

end Theta

attribute [local instance] NumberField.AdelicHaar.glBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

theorem map_thetaGL2_adelicGLHaar :
    Measure.map (thetaGL2 : AdelicGL2 (𝓞 ℚ) ℚ → AdelicGL2 (𝓞 ℚ) ℚ)
      (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) =
      NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ := by
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ
  haveI : (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).Regular := by
    unfold NumberField.AdelicHaar.adelicGLHaar
    exact regular_haarMeasure
  exact map_eq_self_of_involutive _ thetaGL2 thetaGL2_thetaGL2

theorem ideleNorm_inv (x : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    NumberField.TateGlobal.ideleNorm ℚ x⁻¹ = (NumberField.TateGlobal.ideleNorm ℚ x)⁻¹ := by
  have h := NumberField.TateGlobal.ideleNorm_mul (F := ℚ) x x⁻¹
  rw [mul_inv_cancel] at h
  have h1 : NumberField.TateGlobal.ideleNorm ℚ (1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ) = 1 := by
    have h' := NumberField.TateGlobal.ideleNorm_mul (F := ℚ) 1 1
    rw [mul_one] at h'
    have hp := NumberField.TateGlobal.ideleNorm_pos (F := ℚ) 1
    field_simp at h'
    nlinarith [h', hp]
  rw [h1] at h
  have hp := NumberField.TateGlobal.ideleNorm_pos (F := ℚ) x
  field_simp
  linarith [h]

theorem detNorm_thetaGL2 (g : AdelicGL2 (𝓞 ℚ) ℚ) : detNorm (thetaGL2 g) = (detNorm g)⁻¹ := by
  unfold detNorm
  rw [thetaGL2_apply, det_transposeInvN, ideleNorm_inv]

theorem iota_thetaGL2 (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    iota (𝓞 ℚ) ℚ (thetaGL2 g) = transposeInv3 (iota (𝓞 ℚ) ℚ g) :=
  iotaGL_transposeInvN g

theorem detNorm_thetaGL2_cpow (g : AdelicGL2 (𝓞 ℚ) ℚ) (s : ℂ) :
    ((detNorm (thetaGL2 g) : ℝ) : ℂ) ^ (s - 1 / 2) = ((detNorm g : ℝ) : ℂ) ^ ((1 - s) - 1 / 2) := by
  have hpos : 0 < detNorm g := NumberField.TateGlobal.ideleNorm_pos _
  rw [detNorm_thetaGL2, Complex.ofReal_inv]
  rw [Complex.inv_cpow _ _ (by
    rw [Complex.arg_ofReal_of_nonneg hpos.le]; exact Real.pi_pos.ne)]
  rw [← Complex.cpow_neg]
  congr 1
  ring

theorem rsGlobalIntegral_eq_rsGlobalIntegral_dual (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (s : ℂ)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (Θ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    rsGlobalIntegral D s φ Θ =
      rsGlobalIntegral ((thetaGL2 : AdelicGL2 (𝓞 ℚ) ℚ → AdelicGL2 (𝓞 ℚ) ℚ) ⁻¹' D) (1 - s)
        (fun g => φ (thetaGL2 g)) (dualForm Θ) := by
  have hθ : Measurable (thetaGL2 : AdelicGL2 (𝓞 ℚ) ℚ → AdelicGL2 (𝓞 ℚ) ℚ) :=
    (thetaGL2 : AdelicGL2 (𝓞 ℚ) ℚ ≃ₜ* AdelicGL2 (𝓞 ℚ) ℚ).continuous.measurable

  let e : AdelicGL2 (𝓞 ℚ) ℚ ≃ᵐ AdelicGL2 (𝓞 ℚ) ℚ :=
    (thetaGL2 : AdelicGL2 (𝓞 ℚ) ℚ ≃ₜ* AdelicGL2 (𝓞 ℚ) ℚ).toHomeomorph.toMeasurableEquiv
  have he : (e : AdelicGL2 (𝓞 ℚ) ℚ → AdelicGL2 (𝓞 ℚ) ℚ) = thetaGL2 := rfl
  rw [rsGlobalIntegral_def, rsGlobalIntegral_def]
  conv_lhs => rw [← map_thetaGL2_adelicGLHaar, ← he]
  rw [setIntegral_map_equiv]
  rw [he]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  show φ (thetaGL2 g) * Θ (iota (𝓞 ℚ) ℚ (thetaGL2 g)) * ((detNorm (thetaGL2 g) : ℝ) : ℂ) ^ (s - 1 / 2) =
    φ (thetaGL2 g) * dualForm Θ (iota (𝓞 ℚ) ℚ g) * ((detNorm g : ℝ) : ℂ) ^ ((1 - s) - 1 / 2)
  rw [iota_thetaGL2, detNorm_thetaGL2_cpow]
  rfl

theorem thetaGL2_globalPoints (γ : GL (Fin 2) ℚ) :
    thetaGL2 (globalPoints (𝓞 ℚ) ℚ γ) = globalPoints (𝓞 ℚ) ℚ (thetaGL2 γ) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  simp only [thetaGL2_apply]
  rw [globalPoints, Matrix.GeneralLinearGroup.map_apply, coe_transposeInvN, coe_transposeInvN,
    Matrix.transpose_apply, Matrix.transpose_apply, ← Matrix.GeneralLinearGroup.map_inv,
    Matrix.GeneralLinearGroup.map_apply]

theorem thetaGL2_mem_range {g : AdelicGL2 (𝓞 ℚ) ℚ} (hg : g ∈ (globalPoints (𝓞 ℚ) ℚ).range) :
    thetaGL2 g ∈ (globalPoints (𝓞 ℚ) ℚ).range := by
  obtain ⟨γ, rfl⟩ := hg
  exact ⟨thetaGL2 γ, (thetaGL2_globalPoints γ).symm⟩

def thetaRange : (globalPoints (𝓞 ℚ) ℚ).range → (globalPoints (𝓞 ℚ) ℚ).range :=
  fun γ => ⟨thetaGL2 (γ : AdelicGL2 (𝓞 ℚ) ℚ), thetaGL2_mem_range γ.2⟩

theorem thetaRange_thetaRange (γ : (globalPoints (𝓞 ℚ) ℚ).range) : thetaRange (thetaRange γ) = γ :=
  Subtype.ext (thetaGL2_thetaGL2 _)

theorem bijective_thetaRange : Function.Bijective thetaRange :=
  Function.Involutive.bijective thetaRange_thetaRange

theorem isFundamentalDomain_preimage_thetaGL2 {D : Set (AdelicGL2 (𝓞 ℚ) ℚ)}
    (hD : IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range D
      (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ)) :
    IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range
      ((thetaGL2 : AdelicGL2 (𝓞 ℚ) ℚ → AdelicGL2 (𝓞 ℚ) ℚ) ⁻¹' D)
      (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) := by
  have hθ : Measurable (thetaGL2 : AdelicGL2 (𝓞 ℚ) ℚ → AdelicGL2 (𝓞 ℚ) ℚ) :=
    (thetaGL2 : AdelicGL2 (𝓞 ℚ) ℚ ≃ₜ* AdelicGL2 (𝓞 ℚ) ℚ).continuous.measurable
  have hq : QuasiMeasurePreserving (thetaGL2 : AdelicGL2 (𝓞 ℚ) ℚ → AdelicGL2 (𝓞 ℚ) ℚ)
      (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ)
      (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) :=
    ⟨hθ, by rw [map_thetaGL2_adelicGLHaar]⟩
  refine hD.preimage_of_equiv hq bijective_thetaRange fun γ x => ?_
  show thetaGL2 ((thetaRange γ : AdelicGL2 (𝓞 ℚ) ℚ) * x) = (γ : AdelicGL2 (𝓞 ℚ) ℚ) * thetaGL2 x
  rw [map_mul]
  show thetaGL2 (thetaGL2 (γ : AdelicGL2 (𝓞 ℚ) ℚ)) * thetaGL2 x = _
  rw [thetaGL2_thetaGL2]
end LanglandsTunnell.RankinSelberg.RSTranspose
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_rsGlobalIntegral_eq_rsGlobalIntegral_transposeInvN_dualForm_and_isFundamentalDomain_preimage.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_rsGlobalIntegral_eq_rsGlobalIntegral_transposeInvN_dualForm_and_isFundamentalDomain_preimage.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_rsGlobalIntegral_eq_rsGlobalIntegral_transposeInvN_dualForm_and_isFundamentalDomain_preimage.LanglandsTunnell.RankinSelberg.RSTranspose"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_rsGlobalIntegral_eq_rsGlobalIntegral_transposeInvN_dualForm_and_isFundamentalDomain_preimage.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_rsGlobalIntegral_eq_rsGlobalIntegral_transposeInvN_dualForm_and_isFundamentalDomain_preimage.LanglandsTunnell.RankinSelberg"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_rsGlobalIntegral_eq_rsGlobalIntegral_transposeInvN_dualForm_and_isFundamentalDomain_preimage.LanglandsTunnell"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_rsGlobalIntegral_eq_rsGlobalIntegral_transposeInvN_dualForm_and_isFundamentalDomain_preimage.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_rsGlobalIntegral_eq_rsGlobalIntegral_transposeInvN_dualForm_and_isFundamentalDomain_preimage.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_rsGlobalIntegral_eq_rsGlobalIntegral_transposeInvN_dualForm_and_isFundamentalDomain_preimage.LanglandsTunnell.RankinSelberg.RSTranspose"

p2m_open "MeasureTheory IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_rsGlobalIntegral_eq_rsGlobalIntegral_transposeInvN_dualForm_and_isFundamentalDomain_preimage.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_rsGlobalIntegral_eq_rsGlobalIntegral_transposeInvN_dualForm_and_isFundamentalDomain_preimage.LanglandsTunnell.RankinSelberg.RSTranspose"

attribute [local instance] NumberField.AdelicHaar.glBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

theorem solution
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) :
    (∀ (s : ℂ) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (Θ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
      rsGlobalIntegral D s φ Θ =
        rsGlobalIntegral (transposeInvN (Fin 2) ⁻¹' D) (1 - s)
          (fun g => φ (transposeInvN (Fin 2) g)) (dualForm Θ)) ∧
    (IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range D
        (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) →
      IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range (transposeInvN (Fin 2) ⁻¹' D)
        (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ)) :=
  ⟨fun s φ Θ => rsGlobalIntegral_eq_rsGlobalIntegral_dual D s φ Θ,
    fun hD => isFundamentalDomain_preimage_thetaGL2 hD⟩

end S_LanglandsTunnell_RankinSelberg_rsGlobalIntegral_eq_rsGlobalIntegral_transposeInvN_dualForm_and_isFundamentalDomain_preimage
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_rsGlobalIntegral_eq_rsGlobalIntegral_transposeInvN_dualForm_and_isFundamentalDomain_preimage (solution)
