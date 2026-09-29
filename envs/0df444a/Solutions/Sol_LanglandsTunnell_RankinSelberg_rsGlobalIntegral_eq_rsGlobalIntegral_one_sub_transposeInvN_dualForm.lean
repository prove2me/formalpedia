-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.rsGlobalIntegral_eq_rsGlobalIntegral_one_sub_transposeInvN_dualForm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/05d4e8df-3273-5f4b-a87c-853bdb3e53e3

import Definitions.Def_LanglandsTunnell_RSGlobalIntegral
import Definitions.Def_LanglandsTunnell_HonestLDatum
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_rsGlobalIntegral_eq_rsGlobalIntegral_one_sub_transposeInvN_dualForm

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm
open LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg

namespace Ws23J2C

open LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg Matrix

abbrev G2 : Type := AdelicGL2 (𝓞 ℚ) ℚ

noncomputable def tauEquiv : G2 ≃* G2 where
  toFun := transposeInvN (Fin 2)
  invFun := transposeInvN (Fin 2)
  left_inv := transposeInvN_transposeInvN (Fin 2)
  right_inv := transposeInvN_transposeInvN (Fin 2)
  map_mul' := transposeInvN_mul (Fin 2)

theorem continuous_transposeInvN : Continuous (transposeInvN (Fin 2) : G2 → G2) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · have : (Units.val ∘ (transposeInvN (Fin 2) : G2 → G2)) =
        fun g => ((g⁻¹ : G2) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))ᵀ := funext (coe_transposeInvN (Fin 2))
    rw [this]
    exact (Units.continuous_val.comp continuous_inv).matrix_transpose
  · have : (fun g : G2 => (((transposeInvN (Fin 2) g)⁻¹ : G2) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))) =
        fun g => ((g : G2) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))ᵀ := funext (coe_inv_transposeInvN (Fin 2))
    rw [this]
    exact Units.continuous_val.matrix_transpose

noncomputable def tauCME : G2 ≃ₜ* G2 :=
  { tauEquiv with
    continuous_toFun := continuous_transposeInvN
    continuous_invFun := continuous_transposeInvN }

theorem coe_tauCME : ⇑tauCME = (transposeInvN (Fin 2) : G2 → G2) := rfl
theorem coe_tauCME_toHomeomorph : ⇑tauCME.toHomeomorph = (transposeInvN (Fin 2) : G2 → G2) := rfl

noncomputable def tauME : G2 ≃ᵐ G2 := tauCME.toHomeomorph.toMeasurableEquiv

theorem coe_tauME : ⇑tauME = (transposeInvN (Fin 2) : G2 → G2) := rfl
theorem coe_tauME_symm : ⇑tauME.symm = (transposeInvN (Fin 2) : G2 → G2) := rfl

scoped instance isHaarMeasure_adelicGLHaar' : (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).IsHaarMeasure :=
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ

theorem regular_adelicGLHaar : (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).Regular := by
  show (MeasureTheory.Measure.haar : Measure G2).Regular
  infer_instance

theorem map_transposeInvN_adelicGLHaar :
    Measure.map (transposeInvN (Fin 2) : G2 → G2) (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) =
      NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ := by
  set μ : Measure G2 := NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ with hμ
  haveI : μ.Regular := regular_adelicGLHaar
  have hmeas : Measurable (transposeInvN (Fin 2) : G2 → G2) := continuous_transposeInvN.measurable
  set ν : Measure G2 := Measure.map (transposeInvN (Fin 2) : G2 → G2) μ with hν
  haveI : ν.IsHaarMeasure := by rw [hν, ← coe_tauCME]; exact tauCME.isHaarMeasure_map μ
  haveI : ν.Regular := by
    rw [hν, ← coe_tauCME_toHomeomorph]; exact Measure.Regular.map tauCME.toHomeomorph
  have h1 : ν = ν.haarScalarFactor μ • μ := Measure.isMulLeftInvariant_eq_smul_of_regular ν μ
  set c := ν.haarScalarFactor μ with hc
  have h2 : Measure.map (transposeInvN (Fin 2) : G2 → G2) ν = μ := by
    rw [hν, Measure.map_map hmeas hmeas]
    have : (transposeInvN (Fin 2) : G2 → G2) ∘ (transposeInvN (Fin 2)) = id :=
      funext (transposeInvN_transposeInvN (Fin 2))
    rw [this, Measure.map_id]
  have h3 : μ = (c * c) • μ := by
    conv_lhs => rw [← h2, h1, Measure.map_smul, ← hν, h1, smul_smul]

  obtain ⟨K⟩ := (TopologicalSpace.PositiveCompacts.nonempty' : Nonempty (TopologicalSpace.PositiveCompacts G2))
  have hKpos : 0 < μ K := Measure.measure_pos_of_nonempty_interior μ K.interior_nonempty
  have hKtop : μ K < ⊤ := K.isCompact.measure_lt_top
  have h4 : 1 * μ K = ((c * c : NNReal) : ENNReal) * μ K := by
    rw [one_mul]
    conv_lhs => rw [h3]
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  have hcc : c * c = 1 := by
    have := (ENNReal.mul_left_inj hKpos.ne' hKtop.ne).mp h4
    exact_mod_cast this.symm
  have hc1 : c = 1 := by
    have h0 : (0 : ℝ) ≤ c := c.coe_nonneg
    have h' : (c : ℝ) * c = 1 := by exact_mod_cast hcc
    have : (c : ℝ) = 1 := by nlinarith
    exact_mod_cast this
  rw [h1, hc1, one_smul]

theorem measurePreserving_transposeInvN :
    MeasurePreserving (transposeInvN (Fin 2) : G2 → G2)
      (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) :=
  ⟨continuous_transposeInvN.measurable, map_transposeInvN_adelicGLHaar⟩

theorem transposeInvN_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (g : GL (Fin 2) A) :
    transposeInvN (Fin 2) (Matrix.GeneralLinearGroup.map f g) = Matrix.GeneralLinearGroup.map f (transposeInvN (Fin 2) g) := by
  refine Units.ext ?_
  rw [coe_transposeInvN, ← map_inv]
  change ((f.mapMatrix ((g⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)))ᵀ =
    f.mapMatrix ((transposeInvN (Fin 2) g : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)
  rw [coe_transposeInvN, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.transpose_map]

theorem transposeInvN_globalPoints (γ : GL (Fin 2) ℚ) :
    transposeInvN (Fin 2) (globalPoints (𝓞 ℚ) ℚ γ) = globalPoints (𝓞 ℚ) ℚ (transposeInvN (Fin 2) γ) :=
  transposeInvN_map _ γ

theorem iotaGL_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (g : GL (Fin 2) A) :
    iotaGL (Matrix.GeneralLinearGroup.map f g) = Matrix.GeneralLinearGroup.map f (iotaGL g) := by
  refine Units.ext ?_
  change embedMat2 (f.mapMatrix (g : Matrix (Fin 2) (Fin 2) A)) = f.mapMatrix (embedMat2 (g : Matrix (Fin 2) (Fin 2) A))
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, RingHom.mapMatrix_apply]

theorem iota_globalPoints (γ : GL (Fin 2) ℚ) :
    iota (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ) = globalPointsGL 3 (𝓞 ℚ) ℚ (iotaGL γ) :=
  iotaGL_map _ γ

theorem det_transposeInvN {A : Type*} [CommRing A] (g : GL (Fin 2) A) :
    Matrix.GeneralLinearGroup.det (transposeInvN (Fin 2) g) = (Matrix.GeneralLinearGroup.det g)⁻¹ := by
  rw [← map_inv]
  refine Units.ext ?_
  change Matrix.det ((transposeInvN (Fin 2) g : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) =
    Matrix.det ((g⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)
  rw [coe_transposeInvN, Matrix.det_transpose]

theorem detNorm_transposeInvN (g : G2) : detNorm (transposeInvN (Fin 2) g) = (detNorm g)⁻¹ := by
  unfold detNorm
  rw [det_transposeInvN]
  unfold NumberField.TateGlobal.ideleNorm
  rw [map_inv, NNReal.coe_inv]

theorem detNorm_globalPoints_mul (γ : GL (Fin 2) ℚ) (g : G2) :
    detNorm (globalPoints (𝓞 ℚ) ℚ γ * g) = detNorm g := by
  unfold detNorm
  rw [map_mul, NumberField.TateGlobal.ideleNorm_mul, AutomorphicForm.ideleNorm_det_globalPoints, one_mul]

theorem detNorm_pos (g : G2) : 0 < detNorm g := NumberField.TateGlobal.ideleNorm_pos _

theorem detNorm_transposeInvN_cpow (g : G2) (w : ℂ) :
    ((detNorm (transposeInvN (Fin 2) g) : ℝ) : ℂ) ^ w = ((detNorm g : ℝ) : ℂ) ^ (-w) := by
  rw [detNorm_transposeInvN, Complex.ofReal_inv, Complex.inv_cpow, Complex.cpow_neg]
  rw [Complex.arg_ofReal_of_nonneg (detNorm_pos g).le]
  exact Real.pi_pos.ne

scoped instance countable_range_globalPoints : Countable ((globalPoints (𝓞 ℚ) ℚ).range) :=
  (Set.countable_range (globalPoints (𝓞 ℚ) ℚ)).to_subtype

scoped instance smulInvariantMeasure_range_globalPoints :
    SMulInvariantMeasure ((globalPoints (𝓞 ℚ) ℚ).range) G2 (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) :=
  ⟨fun γ s _ => measure_preimage_mul _ (γ : G2) s⟩

noncomputable def tauRange : ((globalPoints (𝓞 ℚ) ℚ).range) ≃ ((globalPoints (𝓞 ℚ) ℚ).range) where
  toFun γ := ⟨transposeInvN (Fin 2) (γ : G2), by
    obtain ⟨γ₀, hγ₀⟩ := γ.2
    exact ⟨transposeInvN (Fin 2) γ₀, by rw [← hγ₀]; exact (transposeInvN_globalPoints γ₀).symm⟩⟩
  invFun γ := ⟨transposeInvN (Fin 2) (γ : G2), by
    obtain ⟨γ₀, hγ₀⟩ := γ.2
    exact ⟨transposeInvN (Fin 2) γ₀, by rw [← hγ₀]; exact (transposeInvN_globalPoints γ₀).symm⟩⟩
  left_inv γ := Subtype.ext (transposeInvN_transposeInvN (Fin 2) _)
  right_inv γ := Subtype.ext (transposeInvN_transposeInvN (Fin 2) _)

theorem isFundamentalDomain_image_transposeInvN {D : Set G2}
    (hD : IsFundamentalDomain ((globalPoints (𝓞 ℚ) ℚ).range) D (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ)) :
    IsFundamentalDomain ((globalPoints (𝓞 ℚ) ℚ).range) ((transposeInvN (Fin 2) : G2 → G2) '' D)
      (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) := by
  have h := hD.image_of_equiv (ν := NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) tauME.toEquiv
    (by rw [show ⇑tauME.toEquiv.symm = (transposeInvN (Fin 2) : G2 → G2) from rfl]
        exact measurePreserving_transposeInvN.quasiMeasurePreserving)
    tauRange
    (fun γ x => by
      show transposeInvN (Fin 2) ((transposeInvN (Fin 2) (γ : G2)) * x) = (γ : G2) * transposeInvN (Fin 2) x
      rw [transposeInvN_mul, transposeInvN_transposeInvN])
  exact h

end Ws23J2C
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_rsGlobalIntegral_eq_rsGlobalIntegral_one_sub_transposeInvN_dualForm.Ws23J2C"

open Ws23J2C LanglandsTunnell.CubicInduction in
theorem Ws23J2C.main
    (D D' : Set (AdelicGL2 (𝓞 ℚ) ℚ))
    (hD : IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range D
      (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ))
    (hD' : IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range D'
      (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ))
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hφ : ∀ (γ : GL (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ (globalPoints (𝓞 ℚ) ℚ γ * g) = φ g)
    (Θ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hΘ : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), Θ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = Θ g)
    (s : ℂ) :
    rsGlobalIntegral D s φ Θ =
      rsGlobalIntegral D' (1 - s) (fun g => φ (transposeInvN (Fin 2) g)) (dualForm Θ) := by

  set F : AdelicGL2 (𝓞 ℚ) ℚ → ℂ :=
    fun g => φ g * Θ (iota (𝓞 ℚ) ℚ g) * ((detNorm g : ℝ) : ℂ) ^ (s - 1 / 2) with hF
  have hFinv : ∀ (γ : (globalPoints (𝓞 ℚ) ℚ).range) (x : AdelicGL2 (𝓞 ℚ) ℚ), F (γ • x) = F x := by
    rintro ⟨_, γ₀, rfl⟩ x
    show F (globalPoints (𝓞 ℚ) ℚ γ₀ * x) = F x
    simp only [hF]
    rw [hφ, map_mul, iota_globalPoints, hΘ, detNorm_globalPoints_mul]

  have hpt : (fun g : AdelicGL2 (𝓞 ℚ) ℚ => (fun g => φ (transposeInvN (Fin 2) g)) g * dualForm Θ (iota (𝓞 ℚ) ℚ g) *
      ((detNorm g : ℝ) : ℂ) ^ (1 - s - 1 / 2)) = fun g => F (transposeInvN (Fin 2) g) := by
    funext g
    simp only [hF]
    have h1 : dualForm Θ (iota (𝓞 ℚ) ℚ g) = Θ (iota (𝓞 ℚ) ℚ (transposeInvN (Fin 2) g)) := by
      show Θ (transposeInv3 (iotaGL g)) = Θ (iotaGL (transposeInvN (Fin 2) g))
      rw [iotaGL_transposeInvN]
    rw [h1, detNorm_transposeInvN_cpow]
    congr 2
    ring
  rw [rsGlobalIntegral_def, rsGlobalIntegral_def, hpt,
    ← measurePreserving_transposeInvN.setIntegral_image_emb tauME.measurableEmbedding F D']
  exact IsFundamentalDomain.setIntegral_eq hD (isFundamentalDomain_image_transposeInvN hD') hFinv

theorem solution
    (D D' : Set (AdelicGL2 (𝓞 ℚ) ℚ))
    (hD : IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range D
      (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ))
    (hD' : IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range D'
      (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ))
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hφ : ∀ (γ : GL (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ (globalPoints (𝓞 ℚ) ℚ γ * g) = φ g)
    (Θ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hΘ : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), Θ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = Θ g)
    (s : ℂ) :
    rsGlobalIntegral D s φ Θ =
      rsGlobalIntegral D' (1 - s) (fun g => φ (transposeInvN (Fin 2) g)) (dualForm Θ) :=
  Ws23J2C.main D D' hD hD' φ hφ Θ hΘ s

end S_LanglandsTunnell_RankinSelberg_rsGlobalIntegral_eq_rsGlobalIntegral_one_sub_transposeInvN_dualForm
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_rsGlobalIntegral_eq_rsGlobalIntegral_one_sub_transposeInvN_dualForm (solution)
