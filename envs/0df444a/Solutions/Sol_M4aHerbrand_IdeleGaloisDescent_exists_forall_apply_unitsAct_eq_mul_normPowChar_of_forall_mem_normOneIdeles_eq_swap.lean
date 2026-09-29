-- Prove2me | solution 1 for M4aHerbrand.IdeleGaloisDescent.exists_forall_apply_unitsAct_eq_mul_normPowChar_of_forall_mem_normOneIdeles_eq_swap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/231a74a9-10ff-5c4f-aac4-95e9ca5a62c9

import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Theorems.Thm_NumberField_TateGlobal_exists_eq_normPowChar_of_forall_mem_normOneIdeles
import Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_apply_unitsAct_eq_of_forall_mem_normOneIdeles
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_IdeleGaloisDescent_exists_forall_apply_unitsAct_eq_mul_normPowChar_of_forall_mem_normOneIdeles_eq_swap
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

noncomputable section

namespace R4RevRigid

open NumberField MeasureTheory NumberField.TateGlobal
open scoped Pointwise ENNReal NNReal

section Modulus

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]

def actEquiv (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) :
    AdeleRing (𝓞 L) L ≃ₜ+ AdeleRing (𝓞 L) L :=
  { ((D.act σ : RingAut (AdeleRing (𝓞 L) L)) : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L).toAddEquiv with
    continuous_toFun := D.continuous_act σ
    continuous_invFun := by
      have h : Continuous (D.act σ⁻¹ : RingAut (AdeleRing (𝓞 L) L)) := D.continuous_act σ⁻¹
      have heq : (((D.act σ : RingAut (AdeleRing (𝓞 L) L)) : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L).toAddEquiv.symm :
          AdeleRing (𝓞 L) L → AdeleRing (𝓞 L) L) = (D.act σ⁻¹ : RingAut (AdeleRing (𝓞 L) L)) := by
        funext a
        rw [map_inv]
        rfl
      show Continuous ((((D.act σ : RingAut (AdeleRing (𝓞 L) L)) : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L).toAddEquiv.symm))
      rw [heq]; exact h }

theorem actEquiv_apply (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (a : AdeleRing (𝓞 L) L) :
    actEquiv K L D σ a = (D.act σ : RingAut (AdeleRing (𝓞 L) L)) a := rfl

theorem distribHaarChar_unitsMap_act (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (z : (AdeleRing (𝓞 L) L)ˣ) :
    distribHaarChar (AdeleRing (𝓞 L) L)
        (Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom : AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L) z) =
      distribHaarChar (AdeleRing (𝓞 L) L) z := by
  classical
  letI : MeasurableSpace (AdeleRing (𝓞 L) L) := borel _
  haveI : BorelSpace (AdeleRing (𝓞 L) L) := ⟨rfl⟩
  set θ := actEquiv K L D σ with hθ
  set μ : Measure (AdeleRing (𝓞 L) L) := Measure.addHaar with hμ
  haveI : μ.IsAddHaarMeasure := by rw [hμ]; infer_instance

  set ν : Measure (AdeleRing (𝓞 L) L) := Measure.map θ.symm μ with hν
  haveI hνH : ν.IsAddHaarMeasure := θ.symm.isAddHaarMeasure_map μ
  haveI : μ.Regular := by rw [hμ]; infer_instance
  haveI : ν.Regular := Measure.Regular.map θ.symm.toHomeomorph

  obtain ⟨s, hs_compact, hs_mem⟩ := exists_compact_mem_nhds (0 : AdeleRing (𝓞 L) L)
  have hs0 : μ s ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hs_mem).ne'
  have hstop : μ s ≠ ⊤ := hs_compact.measure_lt_top.ne

  set w : (AdeleRing (𝓞 L) L)ˣ := Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
    AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L) z with hw
  have hθsymm : ∀ b, (D.act σ : RingAut (AdeleRing (𝓞 L) L)) (θ.symm b) = b := fun b => θ.apply_symm_apply b

  have hset : (w • s : Set (AdeleRing (𝓞 L) L)) = θ '' (z • (θ.symm '' s)) := by
    ext a
    simp only [Set.mem_smul_set, Set.mem_image]
    constructor
    · rintro ⟨b, hb, rfl⟩
      refine ⟨(z : AdeleRing (𝓞 L) L) * θ.symm b, ⟨θ.symm b, ⟨b, hb, rfl⟩, rfl⟩, ?_⟩
      rw [actEquiv_apply, map_mul, hθsymm, Units.smul_def, smul_eq_mul]
      rfl
    · rintro ⟨_, ⟨_, ⟨b, hb, rfl⟩, rfl⟩, rfl⟩
      refine ⟨b, hb, ?_⟩
      rw [Units.smul_def, Units.smul_def, smul_eq_mul, smul_eq_mul, actEquiv_apply, map_mul, hθsymm]
      rfl

  have himg : ∀ B : Set (AdeleRing (𝓞 L) L), μ (θ '' B) = ν B := by
    intro B
    have hmap : ν B = μ (θ.symm ⁻¹' B) := (θ.symm.toHomeomorph.measurableEmbedding).map_apply μ B
    rw [hmap]
    congr 1
    ext a
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨b, hb, rfl⟩
      rwa [θ.symm_apply_apply]
    · intro ha
      exact ⟨θ.symm a, ha, θ.apply_symm_apply a⟩
  have himg' : θ '' (θ.symm '' s) = s := by
    rw [← Set.image_comp]
    rw [show (⇑θ ∘ ⇑θ.symm) = id from funext fun a => θ.apply_symm_apply a]
    exact Set.image_id s

  have h1 := distribHaarChar_mul μ w s
  have h2 := distribHaarChar_mul ν z (θ.symm '' s)
  rw [hset, himg, ← h2, ← himg, himg'] at h1

  have := congrArg (fun t => t / μ s) h1
  beta_reduce at this
  rwa [ENNReal.mul_div_cancel_right hs0 hstop, ENNReal.mul_div_cancel_right hs0 hstop, ENNReal.coe_inj] at this

theorem unitsAct_eq_unitsMap (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (z : (AdeleRing (𝓞 L) L)ˣ) :
    D.unitsAct σ z =
      Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom : AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L) z := by
  ext; rfl

theorem ideleNorm_unitsAct (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (z : (AdeleRing (𝓞 L) L)ˣ) :
    ideleNorm L (D.unitsAct σ z) = ideleNorm L z := by
  unfold NumberField.TateGlobal.ideleNorm
  rw [unitsAct_eq_unitsMap, distribHaarChar_unitsMap_act K L D σ z]

theorem unitsAct_mem_normOneIdeles (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    {z : (AdeleRing (𝓞 L) L)ˣ} (hz : z ∈ normOneIdeles L) : D.unitsAct σ z ∈ normOneIdeles L := by
  rw [mem_normOneIdeles_iff] at hz ⊢
  rw [ideleNorm_unitsAct, hz]

theorem normPowChar_unitsAct (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (t : ℝ)
    (z : (AdeleRing (𝓞 L) L)ˣ) : normPowChar L t (D.unitsAct σ z) = normPowChar L t z := by
  apply Units.ext
  rw [coe_normPowChar_apply, coe_normPowChar_apply, ideleNorm_unitsAct]

theorem continuous_unitsAct (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) :
    Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => D.unitsAct σ z := by
  have h : (fun z : (AdeleRing (𝓞 L) L)ˣ => D.unitsAct σ z) =
      Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom : AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L) :=
    funext fun z => unitsAct_eq_unitsMap K L D σ z
  rw [h]
  exact Continuous.units_map _ (D.continuous_act σ)

theorem unitsAct_mul_apply (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ τ : L ≃ₐ[K] L)
    (z : (AdeleRing (𝓞 L) L)ˣ) : D.unitsAct (σ * τ) z = D.unitsAct σ (D.unitsAct τ z) := by
  rw [map_mul, MulAut.mul_apply]

end Modulus

section NormPow

variable (L : Type) [Field L] [NumberField L]

theorem normPowChar_of_mem_normOneIdeles (t : ℝ) {z : (AdeleRing (𝓞 L) L)ˣ} (hz : z ∈ normOneIdeles L) :
    normPowChar L t z = 1 :=
  normPowChar_eq_one_of_ideleNorm_eq_one t ((mem_normOneIdeles_iff z).mp hz)

end NormPow

section Main

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]

def cob (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (μ ν : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ :=
  (μ.comp (D.unitsAct σ).toMonoidHom) / ν

theorem cob_apply (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (μ ν : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (z : (AdeleRing (𝓞 L) L)ˣ) :
    cob K L D σ μ ν z = μ (D.unitsAct σ z) / ν z := rfl

theorem continuous_cob (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (μ ν : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)
    (hμk : Continuous fun x : (AdeleRing (𝓞 L) L)ˣ => ((μ x : ℂˣ) : ℂ))
    (hνk : Continuous fun x : (AdeleRing (𝓞 L) L)ˣ => ((ν x : ℂˣ) : ℂ)) :
    Continuous (cob K L D σ μ ν) := by

  have hval : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((cob K L D σ μ ν z : ℂˣ) : ℂ) := by
    have h1 : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((μ (D.unitsAct σ z) : ℂˣ) : ℂ) :=
      hμk.comp (continuous_unitsAct K L D σ)
    have h2 : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => (((ν z)⁻¹ : ℂˣ) : ℂ) := by
      have : (fun z : (AdeleRing (𝓞 L) L)ˣ => (((ν z)⁻¹ : ℂˣ) : ℂ)) =
          fun z => (((ν z : ℂˣ) : ℂ))⁻¹ := funext fun z => Units.val_inv_eq_inv_val _
      rw [this]
      exact hνk.inv₀ fun z => (ν z).ne_zero
    have : (fun z : (AdeleRing (𝓞 L) L)ˣ => ((cob K L D σ μ ν z : ℂˣ) : ℂ)) =
        fun z => ((μ (D.unitsAct σ z) : ℂˣ) : ℂ) * (((ν z)⁻¹ : ℂˣ) : ℂ) := by
      funext z; rw [cob_apply, div_eq_mul_inv, Units.val_mul]
    rw [this]; exact h1.mul h2
  have hinv : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => (((cob K L D σ μ ν z)⁻¹ : ℂˣ) : ℂ) := by
    have : (fun z : (AdeleRing (𝓞 L) L)ˣ => (((cob K L D σ μ ν z)⁻¹ : ℂˣ) : ℂ)) =
        fun z => (((cob K L D σ μ ν z : ℂˣ) : ℂ))⁻¹ := funext fun z => Units.val_inv_eq_inv_val _
    rw [this]
    exact hval.inv₀ fun z => (cob K L D σ μ ν z).ne_zero
  exact Units.continuous_iff.mpr ⟨hval, hinv⟩

theorem isUnitaryChar_cob (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (μ ν : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)
    (hμ : AutomorphicForm.IsUnitaryChar (𝓞 L) L μ) (hν : AutomorphicForm.IsUnitaryChar (𝓞 L) L ν) :
    AutomorphicForm.IsUnitaryChar (𝓞 L) L (cob K L D σ μ ν) := by
  intro z
  rw [cob_apply, div_eq_mul_inv, Units.val_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv, hμ, hν,
    inv_one, mul_one]

theorem cob_eq_one_of_mem (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (μ ν : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)
    (h₁ : ∀ z ∈ normOneIdeles L, μ (D.unitsAct σ z) = ν z)
    (z : (AdeleRing (𝓞 L) L)ˣ) (hz : z ∈ normOneIdeles L) : cob K L D σ μ ν z = 1 := by
  rw [cob_apply, h₁ z hz, div_self']

theorem exists_forall_apply_unitsAct_eq_mul_normPowChar
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (μ ν : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)
    (hμ : AutomorphicForm.IsUnitaryChar (𝓞 L) L μ) (hν : AutomorphicForm.IsUnitaryChar (𝓞 L) L ν)
    (hμk : Continuous fun x : (AdeleRing (𝓞 L) L)ˣ => ((μ x : ℂˣ) : ℂ))
    (hνk : Continuous fun x : (AdeleRing (𝓞 L) L)ˣ => ((ν x : ℂˣ) : ℂ))
    (h₁ : ∀ z ∈ normOneIdeles L, μ (D.unitsAct σ z) = ν z) :
    ∃ τ : ℝ, ∀ z : (AdeleRing (𝓞 L) L)ˣ, μ (D.unitsAct σ z) = ν z * normPowChar L τ z := by
  obtain ⟨τ, hτ⟩ := NumberField.TateGlobal.exists_eq_normPowChar_of_forall_mem_normOneIdeles L
    (cob K L D σ μ ν) (continuous_cob K L D σ μ ν hμk hνk) (isUnitaryChar_cob K L D σ μ ν hμ hν)
    (cob_eq_one_of_mem K L D σ μ ν h₁)
  refine ⟨τ, fun z => ?_⟩
  have h := congrArg (fun f : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ => f z) hτ
  beta_reduce at h
  rw [cob_apply] at h
  rw [← h, mul_div_cancel]

theorem main [NumberField K] (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (μ ν : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)
    (hμ : AutomorphicForm.IsUnitaryChar (𝓞 L) L μ) (hν : AutomorphicForm.IsUnitaryChar (𝓞 L) L ν)
    (hμk : Continuous fun x : (AdeleRing (𝓞 L) L)ˣ => ((μ x : ℂˣ) : ℂ))
    (hνk : Continuous fun x : (AdeleRing (𝓞 L) L)ˣ => ((ν x : ℂˣ) : ℂ))
    (h₁ : ∀ z ∈ normOneIdeles L, μ (D.unitsAct σ z) = ν z)
    (h₂ : ∀ z ∈ normOneIdeles L, ν (D.unitsAct σ z) = μ z) :
    ∃ τ : ℝ, (∀ z : (AdeleRing (𝓞 L) L)ˣ, μ (D.unitsAct σ z) = ν z * normPowChar L τ z) ∧
      (∀ z : (AdeleRing (𝓞 L) L)ˣ, ν (D.unitsAct σ z) = μ z * (normPowChar L τ z)⁻¹) := by
  obtain ⟨τ₁, hτ₁⟩ := exists_forall_apply_unitsAct_eq_mul_normPowChar K L D σ μ ν hμ hν hμk hνk h₁
  obtain ⟨τ₂, hτ₂⟩ := exists_forall_apply_unitsAct_eq_mul_normPowChar K L D σ ν μ hν hμ hνk hμk h₂

  have hsq : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      μ (D.unitsAct (σ * σ) z) = μ z * (normPowChar L τ₂ z * normPowChar L τ₁ z) := by
    intro z
    rw [unitsAct_mul_apply K L D σ σ z, hτ₁, hτ₂, normPowChar_unitsAct K L D σ τ₁ z, mul_assoc]
  have hinv1 : ∀ z ∈ normOneIdeles L, μ (D.unitsAct (σ * σ) z) = μ z := by
    intro z hz
    rw [hsq z, normPowChar_of_mem_normOneIdeles L τ₁ hz, normPowChar_of_mem_normOneIdeles L τ₂ hz,
      mul_one, mul_one]
  have hinv : ∀ z : (AdeleRing (𝓞 L) L)ˣ, μ (D.unitsAct (σ * σ) z) = μ z :=
    M4aHerbrand.IdeleGaloisDescent.apply_unitsAct_eq_of_forall_mem_normOneIdeles K L D (σ * σ) μ hinv1

  have hprod : ∀ z : (AdeleRing (𝓞 L) L)ˣ, normPowChar L τ₂ z * normPowChar L τ₁ z = 1 := by
    intro z
    have h := hsq z
    rw [hinv z] at h
    exact (mul_eq_left.mp h.symm)
  refine ⟨τ₁, hτ₁, fun z => ?_⟩
  rw [hτ₂ z, eq_inv_of_mul_eq_one_left (hprod z)]

end Main

end R4RevRigid

end

open NumberField in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (μ ν : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)
    (hμ : AutomorphicForm.IsUnitaryChar (𝓞 L) L μ) (hν : AutomorphicForm.IsUnitaryChar (𝓞 L) L ν)
    (hμk : Continuous fun x : (AdeleRing (𝓞 L) L)ˣ => ((μ x : ℂˣ) : ℂ))
    (hνk : Continuous fun x : (AdeleRing (𝓞 L) L)ˣ => ((ν x : ℂˣ) : ℂ))
    (h₁ : ∀ z ∈ NumberField.TateGlobal.normOneIdeles L, μ (D.unitsAct σ z) = ν z)
    (h₂ : ∀ z ∈ NumberField.TateGlobal.normOneIdeles L, ν (D.unitsAct σ z) = μ z) :
    ∃ τ : ℝ, (∀ z : (AdeleRing (𝓞 L) L)ˣ, μ (D.unitsAct σ z) = ν z * NumberField.TateGlobal.normPowChar L τ z) ∧
      (∀ z : (AdeleRing (𝓞 L) L)ˣ, ν (D.unitsAct σ z) = μ z * (NumberField.TateGlobal.normPowChar L τ z)⁻¹) :=
  R4RevRigid.main K L D σ μ ν hμ hν hμk hνk h₁ h₂

end S_M4aHerbrand_IdeleGaloisDescent_exists_forall_apply_unitsAct_eq_mul_normPowChar_of_forall_mem_normOneIdeles_eq_swap
end P2MW
export P2MW.S_M4aHerbrand_IdeleGaloisDescent_exists_forall_apply_unitsAct_eq_mul_normPowChar_of_forall_mem_normOneIdeles_eq_swap (solution)
