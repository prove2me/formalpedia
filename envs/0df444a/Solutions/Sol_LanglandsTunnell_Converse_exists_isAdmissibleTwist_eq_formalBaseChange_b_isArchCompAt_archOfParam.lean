-- Prove2me | solution 1 for LanglandsTunnell.Converse.exists_isAdmissibleTwist_eq_formalBaseChange_b_isArchCompAt_archOfParam
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/141e6a74-edaf-5554-bbdd-09c866c885e5

import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_SiegelCovering
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_AdelicVolume
import Definitions.Def_NumberField_IdeleBox
import Definitions.Def_IsDedekindDomain_FiniteUnitIdeles
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_NumberField_InfiniteAdeleRing_BaseChangeData
import Definitions.Def_M4aHerbrand_ArchSemilocal
import Definitions.Def_M4aHerbrand_AdeleBaseChange
import Definitions.Def_M4aHerbrand_GenuineDescent
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Complex
import Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine
import Theorems.Thm_M4aHerbrand_GenuineDescent_adelicNorm_genuineBaseChange_algebraMap
import Theorems.Thm_M4aHerbrand_GenuineDescent_continuous_adelicNorm_genuineBaseChange
import Theorems.Thm_M4aHerbrand_exists_idelicNorm_uniformizerIdele_eq_pow_inertiaDeg_mul_localUnit
import Theorems.Thm_M4aHerbrand_genuineAdelicNorm_componentwise
import Theorems.Thm_M4aHerbrand_valuation_adelicNorm_eq_finprod_pow_inertiaDeg
import Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_norm_centralChar_eq_ideleNorm_of_forall_norm_b_eq_one
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_uniformizerIdele
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_LanglandsTunnell_Converse_exists_isAdmissibleTwist_eq_formalBaseChange_b_isArchCompAt_archOfParam
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

section

open IsDedekindDomain NumberField
open AutomorphicForm
open NumberField.TateGlobal
open LanglandsTunnell.Converse

section

variable {G : Type*} [Group G]

private noncomputable def circleNormalization (χ : G →* ℂˣ) : G →* ℂˣ where
  toFun g := Units.mk0 (((χ g : ℂˣ) : ℂ) / ‖((χ g : ℂˣ) : ℂ)‖)
    (div_ne_zero (χ g).ne_zero (by exact_mod_cast (norm_pos_iff.2 (χ g).ne_zero).ne'))
  map_one' := by
    ext
    simp
  map_mul' a b := by
    ext
    simp only [map_mul, Units.val_mul, Units.val_mk0, norm_mul, Complex.ofReal_mul]
    rw [div_mul_div_comm]

private theorem circleNormalization_apply (χ : G →* ℂˣ) (g : G) :
    ((circleNormalization χ g : ℂˣ) : ℂ) = ((χ g : ℂˣ) : ℂ) / ‖((χ g : ℂˣ) : ℂ)‖ :=
  rfl

private theorem norm_circleNormalization (χ : G →* ℂˣ) (g : G) :
    ‖((circleNormalization χ g : ℂˣ) : ℂ)‖ = 1 := by
  have hg : ((χ g : ℂˣ) : ℂ) ≠ 0 := (χ g).ne_zero
  rw [circleNormalization_apply, norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 hg)]

private theorem circleNormalization_eq_one (χ : G →* ℂˣ) {g : G} (hg : χ g = 1) :
    circleNormalization χ g = 1 := by
  ext
  rw [circleNormalization_apply, hg]
  simp

private theorem continuous_circleNormalization [TopologicalSpace G] (χ : G →* ℂˣ) (hχ : Continuous χ) :
    Continuous (circleNormalization χ) := by
  have hval : Continuous fun g : G => ((χ g : ℂˣ) : ℂ) := Units.continuous_val.comp hχ
  have hne : ∀ g : G, ((‖((χ g : ℂˣ) : ℂ)‖ : ℝ) : ℂ) ≠ 0 := fun g => by
    exact_mod_cast (norm_pos_iff.2 (χ g).ne_zero).ne'
  have hquot : Continuous fun g : G => ((χ g : ℂˣ) : ℂ) / ‖((χ g : ℂˣ) : ℂ)‖ :=
    hval.div (Complex.continuous_ofReal.comp hval.norm) hne
  refine Units.continuous_iff.2 ⟨hquot, ?_⟩
  have hne' : ∀ g : G, ((circleNormalization χ g : ℂˣ) : ℂ) ≠ 0 := fun g => (circleNormalization χ g).ne_zero
  simpa only [Units.val_inv_eq_inv_val, circleNormalization_apply] using hquot.fun_inv₀ hne'

end

section

variable (Φ : HeckeEigensystem ℚ ℂ) (R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ.toRawCentral)

private theorem centralChar_facts :
    IsIdeleClassChar (𝓞 ℚ) ℚ (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) ∧
      HeckeCharacter.AdmitsModulus ℚ (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) Φ.level ∧
      (Continuous R.toFun → Continuous (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom)) := by
  have h := AutomorphicForm.SmoothCuspRealizationAt.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine
    ℚ _ _ _ Φ.toRawCentral R
  exact ⟨h.1, h.2.1, fun hR => h.2.2 hR⟩

private theorem isIdeleClassChar_circleNormalization_centralChar :
    IsIdeleClassChar (𝓞 ℚ) ℚ (circleNormalization (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom)) :=
  fun u => circleNormalization_eq_one _ ((centralChar_facts Φ R).1 u)

private theorem continuous_circleNormalization_centralChar (hR : Continuous R.toFun) :
    Continuous (circleNormalization (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom)) :=
  continuous_circleNormalization _ ((centralChar_facts Φ R).2.2 hR)

end

section

variable (K : Type) [Field K] [NumberField K]

private theorem isAdmissibleTwist_comp_idelicNorm (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (h₁ : IsIdeleClassChar (𝓞 ℚ) ℚ η) (h₂ : Continuous η) (h₃ : ∀ x, ‖((η x : ℂˣ) : ℂ)‖ = 1) :
    IsAdmissibleTwist K (η.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u
    have hN : (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm
          (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) u) =
        Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) (Units.map (Algebra.norm ℚ) u) := by
      ext
      exact M4aHerbrand.GenuineDescent.adelicNorm_genuineBaseChange_algebraMap ℚ K (u : K)
    rw [MonoidHom.comp_apply, hN]
    exact h₁ _
  · have hN : Continuous (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm :=
      (M4aHerbrand.GenuineDescent.continuous_adelicNorm_genuineBaseChange ℚ K).units_map _
    exact h₂.comp hN
  · intro x
    exact h₃ _

end

end

section

open IsDedekindDomain NumberField
open NumberField.AdelicLevel
open AutomorphicForm
open NumberField.TateGlobal
open LanglandsTunnell.Converse

section

private theorem det_diagOne {A : Type*} [CommRing A] (a : Aˣ) :
    Matrix.GeneralLinearGroup.det (diagOne a) = a := by
  ext
  show Matrix.det (Matrix.diagonal ![(a : A), 1]) = (a : A)
  rw [Matrix.det_diagonal, Fin.prod_univ_two]
  simp

private theorem det_heckeGen (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v) = uniformizerIdele F v :=
  det_diagOne _

private theorem centralChar_comp_uniformizerIdele (Φ : HeckeEigensystem ℚ ℂ)
    (R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ.toRawCentral)
    {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∉ R.exceptionalSet) :
    (((R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) (uniformizerIdele ℚ v) : ℂˣ) : ℂ) =
      (HeckeEigensystem.cNorm v)⁻¹ * Φ.b v := by
  have h := R.centralChar_det_gen_eq_b hv (Subgroup.topEquiv.symm (uniformizerIdele ℚ v))
    (det_heckeGen ℚ v).symm
  exact h

private theorem cNorm_inv_mul_div_norm (v : HeightOneSpectrum (𝓞 ℚ)) {b : ℂ} (hb : ‖b‖ = 1) :
    ((HeckeEigensystem.cNorm v)⁻¹ * b) / ‖(HeckeEigensystem.cNorm v)⁻¹ * b‖ = b := by
  have hN : (HeckeEigensystem.cNorm v)⁻¹ ≠ 0 := inv_ne_zero (HeckeEigensystem.cNorm_ne_zero v)
  have hnorm : ((‖(HeckeEigensystem.cNorm v)⁻¹ * b‖ : ℝ) : ℂ) = (HeckeEigensystem.cNorm v)⁻¹ := by
    rw [norm_mul, hb, mul_one, norm_inv]
    simp [HeckeEigensystem.cNorm]
  rw [hnorm, mul_comm, mul_div_assoc, div_self hN, mul_one]

private theorem formalBaseChange_b_eq (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)]
    [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)] (Φ : HeckeEigensystem ℚ ℂ) (𝔓 : HeightOneSpectrum (𝓞 K)) :
    (formalBaseChange ℚ K Φ).b 𝔓 =
      Φ.b (𝔓.under (𝓞 ℚ)) ^ ((𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal) :=
  rfl

end

end

section

open IsDedekindDomain NumberField
open NumberField.AdelicLevel
open AutomorphicForm
open NumberField.TateGlobal
open LanglandsTunnell.Converse

section

private theorem idealMultiplicity_eq_zero_of_not_le (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) {𝔣 : Ideal (𝓞 F)} (h𝔣 : 𝔣 ≠ ⊥) (h : ¬ 𝔣 ≤ v.asIdeal) :
    HeckeCharacter.idealMultiplicity F v 𝔣 = 0 := by
  classical
  unfold HeckeCharacter.idealMultiplicity
  by_contra hne
  exact h (Ideal.dvd_iff_le.1 ((Associates.count_ne_zero_iff_dvd h𝔣 v.irreducible).1 hne))

private theorem valuation_eq_one_of_mem_of_inv_mem (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ)
    (ht : (t : v.adicCompletion F) ∈ v.adicCompletionIntegers F)
    (hti : ((t⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F) :
    Valued.v (t : v.adicCompletion F) = 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at ht hti
  rw [Units.val_inv_eq_inv_val, map_inv₀] at hti
  have hpos : 0 < Valued.v (t : v.adicCompletion F) := (Valuation.pos_iff _).2 t.ne_zero
  exact le_antisymm ht ((inv_le_one₀ hpos).1 hti)

private theorem apply_eq_one_of_admitsModulus (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) {𝔣 : Ideal (𝓞 ℚ)}
    (hη : HeckeCharacter.AdmitsModulus ℚ η 𝔣) (u : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (p : HeightOneSpectrum (𝓞 ℚ))
    (hp : HeckeCharacter.idealMultiplicity ℚ p 𝔣 = 0) (hinf : (u : AdeleRing (𝓞 ℚ) ℚ).1 = 1)
    (hp1 : Valued.v ((u : AdeleRing (𝓞 ℚ) ℚ).2 p) = 1)
    (hoff : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ≠ p → (u : AdeleRing (𝓞 ℚ) ℚ).2 v = 1) :
    η u = 1 := by
  refine hη u hinf fun v => ?_
  by_cases hv : v = p
  · subst hv
    refine ⟨hp1, ?_⟩
    have h := Valuation.map_sub Valued.v ((u : AdeleRing (𝓞 ℚ) ℚ).2 v) 1
    rw [hp1, Valuation.map_one, max_self] at h
    rw [hp]
    simpa using h
  · rw [hoff v hv]
    refine ⟨Valuation.map_one _, ?_⟩
    rw [sub_self, Valuation.map_zero]
    exact zero_le'

variable (K : Type) [Field K] [NumberField K]

private theorem comp_idelicNorm_isUnramifiedCharAt_and_apply_uniformizerIdele
    (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) {𝔣 : Ideal (𝓞 ℚ)} (hη : HeckeCharacter.AdmitsModulus ℚ η 𝔣)
    (𝔓 : HeightOneSpectrum (𝓞 K)) (hp : HeckeCharacter.idealMultiplicity ℚ (𝔓.under (𝓞 ℚ)) 𝔣 = 0) :
    IsUnramifiedCharAt (η.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓 ∧
      (((η.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
        ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
          ((𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal) := by
  have hunit : ∀ t : ((𝔓.under (𝓞 ℚ)).adicCompletion ℚ)ˣ,
      Valued.v (t : (𝔓.under (𝓞 ℚ)).adicCompletion ℚ) = 1 →
        η (Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ (𝔓.under (𝓞 ℚ)) t)) = 1 := by
    intro t ht
    refine apply_eq_one_of_admitsModulus η hη _ (𝔓.under (𝓞 ℚ)) hp rfl ?_ ?_
    · show Valued.v (((localUnit (𝓞 ℚ) ℚ (𝔓.under (𝓞 ℚ)) t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
        FiniteAdeleRing (𝓞 ℚ) ℚ) (𝔓.under (𝓞 ℚ))) = 1
      rw [localUnit_apply_self]
      exact ht
    · intro v hv
      show ((localUnit (𝓞 ℚ) ℚ (𝔓.under (𝓞 ℚ)) t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v = 1
      exact localUnit_apply_of_ne (𝓞 ℚ) ℚ (𝔓.under (𝓞 ℚ)) t hv
  refine ⟨?_, ?_⟩
  · intro t ht hti
    have hv1 : Valued.v (t : 𝔓.adicCompletion K) = 1 := valuation_eq_one_of_mem_of_inv_mem K 𝔓 t ht hti
    have hcomp := M4aHerbrand.genuineAdelicNorm_componentwise ℚ K (finIncl (𝓞 K) K (localUnit (𝓞 K) K 𝔓 t))
    have hval := M4aHerbrand.valuation_adelicNorm_eq_finprod_pow_inertiaDeg ℚ K
      (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K) (finIncl (𝓞 K) K (localUnit (𝓞 K) K 𝔓 t))
      (𝔓.under (𝓞 ℚ))
    show η ((M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm
      (Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K 𝔓 t))) = 1
    refine apply_eq_one_of_admitsModulus η hη _ (𝔓.under (𝓞 ℚ)) hp ?_ ?_ ?_
    · show ((M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).adelicNorm
        (finIncl (𝓞 K) K (localUnit (𝓞 K) K 𝔓 t))).1 = 1
      refine hcomp.1.trans ?_
      have h1 : (finIncl (𝓞 K) K (localUnit (𝓞 K) K 𝔓 t)).1 = 1 := rfl
      rw [h1]
      exact map_one _
    · show Valued.v ((((M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).adelicNorm
        (finIncl (𝓞 K) K (localUnit (𝓞 K) K 𝔓 t))).2 : FiniteAdeleRing (𝓞 ℚ) ℚ) (𝔓.under (𝓞 ℚ))) = 1
      rw [hval]
      refine finprod_eq_one_of_forall_eq_one fun w => ?_
      by_cases hw : 𝔓 = w
      · subst hw
        have h2 : ((finIncl (𝓞 K) K (localUnit (𝓞 K) K 𝔓 t)).2 : FiniteAdeleRing (𝓞 K) K) 𝔓 = t :=
          localUnit_apply_self (𝓞 K) K 𝔓 t
        rw [h2, hv1, one_pow]
      · have h2 : ((finIncl (𝓞 K) K (localUnit (𝓞 K) K 𝔓 t)).2 : FiniteAdeleRing (𝓞 K) K) w = 1 :=
          localUnit_apply_of_ne (𝓞 K) K 𝔓 t (Ne.symm hw)
        rw [h2, Valuation.map_one, one_pow]
    · intro v hv
      show (((M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).adelicNorm
        (finIncl (𝓞 K) K (localUnit (𝓞 K) K 𝔓 t))).2 : FiniteAdeleRing (𝓞 ℚ) ℚ) v = 1
      refine (hcomp.2 v).trans ?_
      refine Finset.prod_eq_one fun w _ => ?_
      have hw : w.1 ≠ 𝔓 := fun h =>
        hv (w.2.symm.trans (congrArg (fun q : HeightOneSpectrum (𝓞 K) => q.under (𝓞 ℚ)) h))
      have h2 : ((finIncl (𝓞 K) K (localUnit (𝓞 K) K 𝔓 t)).2 : FiniteAdeleRing (𝓞 K) K) w.1 = 1 :=
        localUnit_apply_of_ne (𝓞 K) K 𝔓 t hw
      rw [h2]
      exact map_one _
  · obtain ⟨t, ht, hN⟩ := M4aHerbrand.exists_idelicNorm_uniformizerIdele_eq_pow_inertiaDeg_mul_localUnit ℚ K 𝔓
    rw [MonoidHom.comp_apply, hN, map_mul, map_pow, hunit t ht, mul_one, Units.val_pow_eq_pow_val]

end

end

section

open IsDedekindDomain NumberField
open NumberField.AdelicLevel
open NumberField.AdeleRing
open AutomorphicForm
open NumberField.TateGlobal
open Rat.HeightOneSpectrum
open LanglandsTunnell.Converse

section

private noncomputable def principalIdele (q : ℚˣ) : (AdeleRing (𝓞 ℚ) ℚ)ˣ :=
  Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) : ℚ →* AdeleRing (𝓞 ℚ) ℚ) q

private noncomputable def archOf (q : ℚˣ) : (Rat.infinitePlace.Completion)ˣ :=
  Units.map (((Pi.evalRingHom (fun w : InfinitePlace ℚ => w.Completion) Rat.infinitePlace).comp
    ((RingHom.fst (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)).comp (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)))) :
      ℚ →* Rat.infinitePlace.Completion) q

private theorem norm_archOf (q : ℚˣ) : ‖(archOf q : Rat.infinitePlace.Completion)‖ = |((q : ℚ) : ℝ)| := by
  have h1 := AutomorphicForm.SiegelCovering.norm_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace
    (archOf q : Rat.infinitePlace.Completion)
  have h2 : InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace
      (archOf q : Rat.infinitePlace.Completion) =
        RatIdele.archCoord (Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) : ℚ →* AdeleRing (𝓞 ℚ) ℚ) q) := rfl
  rw [← h1, h2, RatIdele.archCoord_principal]
  exact Real.norm_eq_abs _

private noncomputable def ratPrimeUnit (v : HeightOneSpectrum (𝓞 ℚ)) : ℚˣ :=
  Units.mk0 ((natGenerator v : ℕ) : ℚ) (by exact_mod_cast (prime_natGenerator v).ne_zero)

private noncomputable def archIdele (v : HeightOneSpectrum (𝓞 ℚ)) : (AdeleRing (𝓞 ℚ) ℚ)ˣ :=
  archUnitHom Rat.infinitePlace (archOf (ratPrimeUnit v))

private noncomputable def unitRest (v : HeightOneSpectrum (𝓞 ℚ)) : (AdeleRing (𝓞 ℚ) ℚ)ˣ :=
  (uniformizerIdele ℚ v)⁻¹ * ((archIdele v)⁻¹ * principalIdele (ratPrimeUnit v))

private theorem absNorm_asIdeal (v : HeightOneSpectrum (𝓞 ℚ)) : Ideal.absNorm v.asIdeal = natGenerator v := by
  rw [RatIdele.asIdeal_eq_span_natGenerator, Ideal.absNorm_span_singleton,
    ← map_natCast (algebraMap ℤ (𝓞 ℚ)), Algebra.norm_algebraMap, RingOfIntegers.rank, Module.finrank_self, pow_one]
  simp

private theorem valued_principalIdele_snd (v w : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v ((principalIdele (ratPrimeUnit v) : AdeleRing (𝓞 ℚ) ℚ).2 w) =
      Valued.v ((uniformizerIdele ℚ v : AdeleRing (𝓞 ℚ) ℚ).2 w) := by

  have hl : (principalIdele (ratPrimeUnit v) : AdeleRing (𝓞 ℚ) ℚ).2 w = _ :=
    RatIdele.algebraMap_adeleRing_snd ((natGenerator v : ℕ) : ℚ) w
  have hr : (uniformizerIdele ℚ v : AdeleRing (𝓞 ℚ) ℚ).2 w =
      ((localUnit (𝓞 ℚ) ℚ v (uniformizerUnit ℚ v) : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) w := rfl
  rw [hl, hr, RatIdele.valued_algebraMap_rat]
  by_cases hw : v = w
  · subst hw
    rw [localUnit_apply_self, valued_uniformizerUnit, RatIdele.valuation_natGenerator]
  · rw [localUnit_apply_of_ne (𝓞 ℚ) ℚ v _ (Ne.symm hw), Valuation.map_one, RatIdele.valuation_natGenerator_of_ne hw]

private theorem adeleFst_mul (x y : AdeleRing (𝓞 ℚ) ℚ) : (x * y).1 = x.1 * y.1 := rfl

private theorem adeleFst_one : (1 : AdeleRing (𝓞 ℚ) ℚ).1 = 1 := rfl

private theorem principalIdele_fst (v : HeightOneSpectrum (𝓞 ℚ)) :
    (principalIdele (ratPrimeUnit v) : AdeleRing (𝓞 ℚ) ℚ).1 = (archIdele v : AdeleRing (𝓞 ℚ) ℚ).1 := by
  funext w
  obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
  show (principalIdele (ratPrimeUnit v) : AdeleRing (𝓞 ℚ) ℚ).1 Rat.infinitePlace =
    ((archUnitHom Rat.infinitePlace (archOf (ratPrimeUnit v)) : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).1
      Rat.infinitePlace
  rw [archUnitHom_apply, AdelicVolume.archCentralUnit_fst_self]
  rfl

private theorem unitRest_fst (v : HeightOneSpectrum (𝓞 ℚ)) : (unitRest v : AdeleRing (𝓞 ℚ) ℚ).1 = 1 := by
  have h1 : (((archIdele v)⁻¹ * principalIdele (ratPrimeUnit v) : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
      AdeleRing (𝓞 ℚ) ℚ).1 = 1 := by
    rw [Units.val_mul, adeleFst_mul, principalIdele_fst, ← adeleFst_mul, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, adeleFst_one]
  have h2 : (((uniformizerIdele ℚ v)⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).1 = 1 := by
    have h := congrArg Prod.fst (Units.inv_mul (uniformizerIdele ℚ v))
    rw [adeleFst_mul, adeleFst_one, show (uniformizerIdele ℚ v : AdeleRing (𝓞 ℚ) ℚ).1 = 1 from rfl, mul_one] at h
    exact h
  unfold unitRest
  rw [Units.val_mul, adeleFst_mul, h1, h2, mul_one]

private theorem valued_unitRest_snd (v w : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v ((unitRest v : AdeleRing (𝓞 ℚ) ℚ).2 w) = 1 := by
  have harch : Valued.v ((((archIdele v)⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 w) = 1 := by
    have h := RatIdele.valued_snd_inv_mul (archIdele v) w
    rw [show (archIdele v : AdeleRing (𝓞 ℚ) ℚ).2 w = 1 from rfl, Valuation.map_one, mul_one] at h
    exact h
  unfold unitRest
  rw [RatIdele.valued_snd_mul, RatIdele.valued_snd_mul, harch, one_mul, valued_principalIdele_snd,
    RatIdele.valued_snd_inv_mul]

private theorem ideleNorm_unitRest (v : HeightOneSpectrum (𝓞 ℚ)) : ideleNorm ℚ (unitRest v) = 1 := by
  refine ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles ℚ (unitRest v) (unitRest_fst v) ?_
  rw [FiniteAdeleRing.mem_unitIdeles_iff]
  refine ⟨fun w => ?_, fun w => ?_⟩
  · rw [val_finitePartUnits, HeightOneSpectrum.mem_adicCompletionIntegers]
    exact (valued_unitRest_snd v w).le
  · have h := RatIdele.valued_snd_inv_mul (unitRest v) w
    rw [valued_unitRest_snd, mul_one] at h
    rw [← map_inv, val_finitePartUnits, HeightOneSpectrum.mem_adicCompletionIntegers]
    exact h.le

private theorem ideleNorm_archIdele (v : HeightOneSpectrum (𝓞 ℚ))
    (h : ideleNorm ℚ (principalIdele (ratPrimeUnit v)) = 1) :
    ideleNorm ℚ (archIdele v) = ((natGenerator v : ℕ) : ℝ) := by
  have hdec : principalIdele (ratPrimeUnit v) = archIdele v * (uniformizerIdele ℚ v * unitRest v) := by
    unfold unitRest
    rw [mul_inv_cancel_left, mul_inv_cancel_left]
  have hp : ((natGenerator v : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (prime_natGenerator v).ne_zero
  rw [hdec, ideleNorm_mul, ideleNorm_mul, ideleNorm_uniformizerIdele, ideleNorm_unitRest, mul_one,
    absNorm_asIdeal] at h
  exact (mul_inv_eq_one₀ hp).1 h

private theorem re_eq_zero_of_isArchCompAt (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hnorm : ∀ x : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖((χ x : ℂˣ) : ℂ)‖ = ideleNorm ℚ x)
    (hclass : IsIdeleClassChar (𝓞 ℚ) ℚ χ) (e : ℂ) (a : ℤ)
    (hP : IsArchCompAt ℚ χ Rat.infinitePlace (e + 1) a) : e.re = 0 := by
  obtain ⟨v⟩ : Nonempty (HeightOneSpectrum (𝓞 ℚ)) := ⟨(primesEquiv (R := 𝓞 ℚ)).symm ⟨2, Nat.prime_two⟩⟩
  have hp1 : (1 : ℝ) < ((natGenerator v : ℕ) : ℝ) := by exact_mod_cast (prime_natGenerator v).one_lt
  have hp0 : (0 : ℝ) < ((natGenerator v : ℕ) : ℝ) := lt_trans zero_lt_one hp1
  have hc : χ (principalIdele (ratPrimeUnit v)) = 1 := hclass (ratPrimeUnit v)
  have hprinc : ideleNorm ℚ (principalIdele (ratPrimeUnit v)) = 1 := by
    rw [← hnorm, hc, Units.val_one, norm_one]
  have hy : ‖(archOf (ratPrimeUnit v) : Rat.infinitePlace.Completion)‖ = ((natGenerator v : ℕ) : ℝ) := by
    rw [norm_archOf]
    simp [ratPrimeUnit]
  have hleft : ‖((χ (archIdele v) : ℂˣ) : ℂ)‖ = ((natGenerator v : ℕ) : ℝ) := by
    rw [hnorm, ideleNorm_archIdele v hprinc]
  have hformula := hP (archOf (ratPrimeUnit v))
  have hmult : ((Rat.infinitePlace.mult : ℂ)) = 1 := by
    rw [InfinitePlace.mult, if_pos Rat.isReal_infinitePlace, Nat.cast_one]
  rw [hmult, one_mul] at hformula
  have hright : ‖((archLocalChar χ Rat.infinitePlace (archOf (ratPrimeUnit v)) : ℂˣ) : ℂ)‖ =
      ((natGenerator v : ℕ) : ℝ) ^ (e.re + 1) := by
    rw [hformula, norm_mul, norm_zpow, norm_div, AutomorphicForm.SiegelCoordinates.norm_extensionEmbedding,
      Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self (norm_ne_zero_iff.2 (archOf (ratPrimeUnit v)).ne_zero),
      one_zpow, mul_one, hy, Complex.norm_cpow_eq_rpow_re_of_pos hp0, Complex.add_re, Complex.one_re]
  have hkey : ((natGenerator v : ℕ) : ℝ) ^ (e.re + 1) = ((natGenerator v : ℕ) : ℝ) := by
    rw [← hright]
    exact hleft
  have hlog := congrArg Real.log hkey
  rw [Real.log_rpow hp0] at hlog
  have hlogne : Real.log ((natGenerator v : ℕ) : ℝ) ≠ 0 := (Real.log_pos hp1).ne'
  have h2 : (e.re + 1) * Real.log ((natGenerator v : ℕ) : ℝ) = 1 * Real.log ((natGenerator v : ℕ) : ℝ) := by
    rw [one_mul]
    exact hlog
  have h3 := mul_right_cancel₀ hlogne h2
  linarith

private theorem re_centralExponent_eq_zero
    (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ)
    (R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ.toRawCentral)
    (hR : Continuous R.toFun)
    (P : LanglandsTunnell.RealArchParam)
    (hP : ∀ (w : InfinitePlace ℚ) (_hw : w.IsReal),
        IsArchCompAt ℚ (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) w
          (P.centralExponent + 1) (P.centralSign.val : ℤ))
    (SQ₀ : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
    (hb : ∀ p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ), p ∉ SQ₀ → ‖Φ.b p‖ = 1) :
    P.centralExponent.re = 0 := by
  have hnorm0 := SmoothCuspRealizationAt.norm_centralChar_eq_ideleNorm_of_forall_norm_b_eq_one ℚ _ _ Φ R hR SQ₀ hb
  have hnorm : ∀ x : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
      ‖(((R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) x : ℂˣ) : ℂ)‖ = ideleNorm ℚ x := fun x =>
    hnorm0 (Subgroup.topEquiv.symm x)
  have hclass : IsIdeleClassChar (𝓞 ℚ) ℚ (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) :=
    (SmoothCuspRealizationAt.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine ℚ _ _ _ _ R).1
  exact re_eq_zero_of_isArchCompAt _ hnorm hclass _ _ (hP Rat.infinitePlace Rat.isReal_infinitePlace)

end

end

section

open NumberField
open NumberField.TateGlobal
open LanglandsTunnell.Converse

section

variable {F : Type} [Field F] [NumberField F]

private theorem isArchCompAt_circleNormalization (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (w : InfinitePlace F)
    {e : ℂ} {a : ℤ} (h : IsArchCompAt F χ w (e + 1) a) (hre : e.re = 0) :
    IsArchCompAt F (circleNormalization χ) w e a := by
  unfold IsArchCompAt at h ⊢
  intro x
  have hx := h x
  rw [archLocalChar_apply] at hx
  have hr : (0 : ℝ) < ‖(x : w.Completion)‖ := norm_pos_iff.2 x.ne_zero
  have hB : ((‖(x : w.Completion)‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hcirc : ‖InfinitePlace.Completion.extensionEmbedding w (x : w.Completion) / ((‖(x : w.Completion)‖ : ℝ) : ℂ)‖
      = 1 := by
    rw [norm_div, AutomorphicForm.SiegelCoordinates.norm_extensionEmbedding, Complex.norm_real, Real.norm_eq_abs,
      abs_norm, div_self hr.ne']
  have hden : ((‖((χ (AdelicVolume.archCentralUnit F w x) : ℂˣ) : ℂ)‖ : ℝ) : ℂ) =
      ((‖(x : w.Completion)‖ : ℝ) : ℂ) ^ ((w.mult : ℕ) : ℂ) := by
    rw [hx, norm_mul, norm_zpow, hcirc, one_zpow, mul_one, Complex.norm_cpow_eq_rpow_re_of_pos hr,
      show (((w.mult : ℕ) : ℂ) * (e + 1)).re = ((w.mult : ℕ) : ℝ) by simp [hre],
      Complex.ofReal_cpow hr.le, Complex.ofReal_natCast]
  have hsplit : ((‖(x : w.Completion)‖ : ℝ) : ℂ) ^ (((w.mult : ℕ) : ℂ) * (e + 1)) =
      ((‖(x : w.Completion)‖ : ℝ) : ℂ) ^ (((w.mult : ℕ) : ℂ) * e) *
        ((‖(x : w.Completion)‖ : ℝ) : ℂ) ^ ((w.mult : ℕ) : ℂ) := by
    rw [← Complex.cpow_add _ _ hB]
    congr 1
    ring
  have hBm : ((‖(x : w.Completion)‖ : ℝ) : ℂ) ^ ((w.mult : ℕ) : ℂ) ≠ 0 :=
    Complex.cpow_ne_zero_iff.2 (Or.inl hB)
  rw [archLocalChar_apply, circleNormalization_apply, hden, hx, hsplit, mul_right_comm, mul_div_assoc, div_self hBm,
    mul_one]

end

end

section

open NumberField IsDedekindDomain
open NumberField.TateGlobal NumberField.AdelicVolume
open M4aHerbrand.ArchSemilocal
open scoped NumberField.LiesOver
open LanglandsTunnell.Converse

private theorem algebraNorm_prod_fst_snd {R : Type*} [CommRing R] {A B : Type*} [Ring A] [Ring B] [Algebra R A]
    [Algebra R B] [Module.Free R A] [Module.Free R B] [Module.Finite R A] [Module.Finite R B] (x : A × B) :
    Algebra.norm R x = Algebra.norm R x.1 * Algebra.norm R x.2 := by
  have h : (Algebra.lmul R (A × B) x : (A × B) →ₗ[R] (A × B)) =
      LinearMap.prodMap (Algebra.lmul R A x.1) (Algebra.lmul R B x.2) :=
    LinearMap.ext fun _ => rfl
  rw [Algebra.norm_apply, Algebra.norm_apply, Algebra.norm_apply, h, LinearMap.det_prodMap]

private def piSplitAtAlgEquiv (R : Type*) [CommSemiring R] {ι : Type*} [DecidableEq ι] (i₀ : ι) (A : ι → Type*)
    [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)] : (∀ i, A i) ≃ₐ[R] A i₀ × ∀ i : {i // i ≠ i₀}, A i :=
  { Equiv.piSplitAt i₀ A with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl
    commutes' := fun _ => rfl }

private theorem algebraNorm_pi_mulSingle {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Ring (A i)] [∀ i, Algebra R (A i)] [∀ i, Module.Free R (A i)]
    [∀ i, Module.Finite R (A i)] (i₀ : ι) (a : A i₀) :
    Algebra.norm R (Pi.mulSingle i₀ a : ∀ i, A i) = Algebra.norm R a := by
  have h1 : (piSplitAtAlgEquiv R i₀ A (Pi.mulSingle i₀ a)).1 = a := Pi.mulSingle_eq_same i₀ a
  have h2 : (piSplitAtAlgEquiv R i₀ A (Pi.mulSingle i₀ a)).2 = 1 :=
    funext fun j => Pi.mulSingle_eq_of_ne j.2 a
  rw [← Algebra.norm_eq_of_algEquiv (piSplitAtAlgEquiv R i₀ A), algebraNorm_prod_fst_snd, h1, h2, map_one,
    mul_one]

section

variable (K : Type) [Field K] [NumberField K]

private theorem liesOver_default (w : InfinitePlace K) : w.1.LiesOver (default : InfinitePlace ℚ).1 :=
  liesOver_of_comap_eq (Subsingleton.elim _ _)

attribute [local instance] liesOver_default

attribute [local instance] extLiesOver

private theorem genuine_conorm_apply (x : InfiniteAdeleRing ℚ) (w : InfinitePlace K) :
    (genuineInfinitePlaceData (K := ℚ) (L := K)).conorm x w =
      algebraMap (default : InfinitePlace ℚ).Completion w.Completion (x default) := by
  have key : ∀ (v : InfinitePlace ℚ) [w.1.LiesOver v.1],
      algebraMap v.Completion w.Completion (x v) =
        algebraMap (default : InfinitePlace ℚ).Completion w.Completion (x default) := by
    intro v _
    obtain rfl : v = default := Subsingleton.elim _ _
    rfl
  haveI : w.1.LiesOver (w.comap (algebraMap ℚ K)).1 := liesOver_of_comap_eq rfl
  rw [← key (w.comap (algebraMap ℚ K))]
  exact congrFun ((placeEquivAlg (K := ℚ) (L := K) (w.comap (algebraMap ℚ K))).commutes
    (x (w.comap (algebraMap ℚ K)))) ⟨w, rfl⟩

private noncomputable abbrev piAlgebra :
    Algebra (default : InfinitePlace ℚ).Completion (InfiniteAdeleRing K) :=
  (Pi.algebra (InfinitePlace K) fun w : InfinitePlace K => w.Completion :
    Algebra (default : InfinitePlace ℚ).Completion ((w : InfinitePlace K) → w.Completion))

private noncomputable def evalDefault : InfiniteAdeleRing ℚ ≃+* (default : InfinitePlace ℚ).Completion :=
  (RingEquiv.piUnique fun v : InfinitePlace ℚ => v.Completion :
    ((v : InfinitePlace ℚ) → v.Completion) ≃+* (default : InfinitePlace ℚ).Completion)

private theorem norm_conorm_eq (y : InfiniteAdeleRing K) :
    (letI := (genuineInfinitePlaceData (K := ℚ) (L := K)).conorm.toAlgebra;
      Algebra.norm (InfiniteAdeleRing ℚ) y) default =
      (letI := piAlgebra K; Algebra.norm (default : InfinitePlace ℚ).Completion y) := by
  letI := (genuineInfinitePlaceData (K := ℚ) (L := K)).conorm.toAlgebra
  letI := piAlgebra K
  have he : (algebraMap (default : InfinitePlace ℚ).Completion (InfiniteAdeleRing K)).comp
      (evalDefault : InfiniteAdeleRing ℚ →+* (default : InfinitePlace ℚ).Completion) =
        algebraMap (InfiniteAdeleRing ℚ) (InfiniteAdeleRing K) := by
    ext x : 1
    funext w
    rw [RingHom.algebraMap_toAlgebra]
    exact (genuine_conorm_apply K x w).symm
  exact Algebra.norm_eq_of_ringEquiv evalDefault he y

private theorem norm_archCentralUnit_fst (w₀ : InfinitePlace K) (a : (w₀.Completion)ˣ) :
    (letI := piAlgebra K;
      Algebra.norm (default : InfinitePlace ℚ).Completion
        ((archCentralUnit K w₀ a : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1) =
      Algebra.norm (default : InfinitePlace ℚ).Completion (a : w₀.Completion) := by
  classical
  haveI hfin : ∀ w : InfinitePlace K, Module.Finite (default : InfinitePlace ℚ).Completion w.Completion :=
    fun w => finiteDimensional_completion default w
  haveI hfree : ∀ w : InfinitePlace K, Module.Free (default : InfinitePlace ℚ).Completion w.Completion :=
    fun w => Module.Free.of_divisionRing _ _
  have hy : ((archCentralUnit K w₀ a : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 =
      (Pi.mulSingle w₀ (a : w₀.Completion) : (w : InfinitePlace K) → w.Completion) := by
    funext w
    by_cases hw : w = w₀
    · subst hw
      rw [archCentralUnit_fst_self, Pi.mulSingle_eq_same]
    · rw [archCentralUnit_fst_of_ne w₀ a hw, Pi.mulSingle_eq_of_ne hw]
  rw [hy]
  exact algebraNorm_pi_mulSingle w₀ (a : w₀.Completion)

private noncomputable def localNormUnit (w₀ : InfinitePlace K) :
    (w₀.Completion)ˣ →* ((default : InfinitePlace ℚ).Completion)ˣ :=
  Units.map
    (Algebra.norm (default : InfinitePlace ℚ).Completion : w₀.Completion →* (default : InfinitePlace ℚ).Completion)

private theorem localNormUnit_apply (w₀ : InfinitePlace K) (a : (w₀.Completion)ˣ) :
    ((localNormUnit K w₀ a : ((default : InfinitePlace ℚ).Completion)ˣ) : (default : InfinitePlace ℚ).Completion) =
      Algebra.norm (default : InfinitePlace ℚ).Completion (a : w₀.Completion) :=
  rfl

private theorem idelicNorm_archUnitHom (w₀ : InfinitePlace K) (a : (w₀.Completion)ˣ) :
    (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm (archUnitHom w₀ a) =
      archUnitHom (default : InfinitePlace ℚ) (localNormUnit K w₀ a) := by
  have h := M4aHerbrand.genuineAdelicNorm_componentwise ℚ K
    ((archCentralUnit K w₀ a : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)
  ext : 1
  rw [archUnitHom_apply, archUnitHom_apply]
  show (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).adelicNorm
      ((archCentralUnit K w₀ a : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) = _
  refine Prod.ext ?_ ?_
  · funext v
    obtain rfl : v = default := Subsingleton.elim _ _
    rw [archCentralUnit_fst_self]
    refine Eq.trans ?_ (norm_archCentralUnit_fst K w₀ a)
    refine Eq.trans ?_ (norm_conorm_eq K _)
    exact congrFun h.1 default
  · rw [archCentralUnit_snd]
    ext v
    refine Eq.trans (h.2 v) ?_
    rw [archCentralUnit_snd]
    refine Finset.prod_eq_one fun w _ => ?_
    rw [show ((1 : FiniteAdeleRing (𝓞 K) K) : ∀ w : HeightOneSpectrum (𝓞 K), w.adicCompletion K) w.1 = 1 from rfl,
      map_one]

private theorem default_isReal : (default : InfinitePlace ℚ).IsReal := by
  rw [Subsingleton.elim (default : InfinitePlace ℚ) Rat.infinitePlace]
  exact Rat.isReal_infinitePlace

private theorem mult_default : (((default : InfinitePlace ℚ).mult : ℕ) : ℂ) = 1 := by
  rw [InfinitePlace.mult, if_pos default_isReal, Nat.cast_one]

private theorem exists_algebraMap_eq_of_isReal {w : InfinitePlace K} (hw : w.IsReal) (x : w.Completion) :
    ∃ r : (default : InfinitePlace ℚ).Completion,
      algebraMap (default : InfinitePlace ℚ).Completion w.Completion r = x := by
  have h1 : Module.finrank (default : InfinitePlace ℚ).Completion w.Completion = 1 :=
    InfinitePlace.Completion.finrank_eq_one_of_isUnramified default
      (InfinitePlace.IsReal.isUnramified ℚ hw)
  have hbot : (⊥ : Subalgebra (default : InfinitePlace ℚ).Completion w.Completion) = ⊤ :=
    Subalgebra.bot_eq_top_iff_finrank_eq_one.2 h1
  have hx : x ∈ (⊥ : Subalgebra (default : InfinitePlace ℚ).Completion w.Completion) := by
    rw [hbot]
    exact Algebra.mem_top
  exact Algebra.mem_bot.1 hx

private theorem norm_eq_of_isReal {w : InfinitePlace K} (hw : w.IsReal) (x : w.Completion) :
    ‖Algebra.norm (default : InfinitePlace ℚ).Completion x‖ = ‖x‖ ∧
      InfinitePlace.Completion.extensionEmbedding default (Algebra.norm (default : InfinitePlace ℚ).Completion x) =
        InfinitePlace.Completion.extensionEmbedding w x := by
  obtain ⟨r, rfl⟩ := exists_algebraMap_eq_of_isReal K hw x
  have h1 : Module.finrank (default : InfinitePlace ℚ).Completion w.Completion = 1 :=
    InfinitePlace.Completion.finrank_eq_one_of_isUnramified default
      (InfinitePlace.IsReal.isUnramified ℚ hw)
  rw [Algebra.norm_algebraMap, h1, pow_one]
  haveI : ComplexEmbedding.LiesOver (InfinitePlace.Completion.extensionEmbedding w)
      (InfinitePlace.Completion.extensionEmbedding (default : InfinitePlace ℚ)) :=
    InfinitePlace.LiesOver.extensionEmbedding_liesOver_of_isReal w default_isReal
  have hemb : InfinitePlace.Completion.extensionEmbedding w
      (algebraMap (default : InfinitePlace ℚ).Completion w.Completion r) =
        InfinitePlace.Completion.extensionEmbedding (default : InfinitePlace ℚ) r := by
    rw [InfinitePlace.Completion.liesOver_extensionEmbedding_apply]
  refine ⟨?_, hemb.symm⟩
  rw [← AutomorphicForm.SiegelCoordinates.norm_extensionEmbedding w, hemb,
    AutomorphicForm.SiegelCoordinates.norm_extensionEmbedding]

private theorem norm_eq_of_isComplex {w : InfinitePlace K} (hw : w.IsComplex) (x : w.Completion) :
    ‖Algebra.norm (default : InfinitePlace ℚ).Completion x‖ = ‖x‖ ^ 2 ∧
      InfinitePlace.Completion.extensionEmbedding default (Algebra.norm (default : InfinitePlace ℚ).Completion x) =
        ((‖x‖ ^ 2 : ℝ) : ℂ) := by
  haveI : ComplexEmbedding.LiesOver (InfinitePlace.Completion.extensionEmbedding w)
      (InfinitePlace.Completion.extensionEmbedding (default : InfinitePlace ℚ)) :=
    InfinitePlace.LiesOver.extensionEmbedding_liesOver_of_isReal w default_isReal
  have he : (algebraMap ℝ ℂ).comp
      (InfinitePlace.Completion.ringEquivRealOfIsReal default_isReal : (default : InfinitePlace ℚ).Completion →+* ℝ) =
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw : w.Completion →+* ℂ).comp
          (algebraMap (default : InfinitePlace ℚ).Completion w.Completion) := by
    ext c
    simp
  have hn : Algebra.norm (default : InfinitePlace ℚ).Completion x =
      (InfinitePlace.Completion.ringEquivRealOfIsReal default_isReal).symm
        (Complex.normSq (InfinitePlace.Completion.extensionEmbedding w x)) := by
    rw [Algebra.norm_eq_of_equiv_equiv (InfinitePlace.Completion.ringEquivRealOfIsReal default_isReal)
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw) he x, Algebra.norm_complex_apply,
      InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply]
  refine ⟨?_, ?_⟩
  · rw [hn, ← AutomorphicForm.norm_ringEquivRealOfIsReal default_isReal, RingEquiv.apply_symm_apply, Real.norm_eq_abs,
      abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq,
      AutomorphicForm.SiegelCoordinates.norm_extensionEmbedding]
  · rw [hn, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply default_isReal,
      ← InfinitePlace.Completion.ringEquivRealOfIsReal_apply default_isReal, RingEquiv.apply_symm_apply,
      Complex.normSq_eq_norm_sq, AutomorphicForm.SiegelCoordinates.norm_extensionEmbedding]

private theorem archLocalChar_comp_idelicNorm (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hN : ∀ (w₀ : InfinitePlace K) (a : (w₀.Completion)ˣ),
      (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm (archUnitHom w₀ a) =
        archUnitHom (default : InfinitePlace ℚ) (localNormUnit K w₀ a))
    (w : InfinitePlace K) (a : (w.Completion)ˣ) :
    archLocalChar (η.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) w a =
      archLocalChar η (default : InfinitePlace ℚ) (localNormUnit K w a) := by
  show η ((M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm (archUnitHom w a)) =
    η (archUnitHom (default : InfinitePlace ℚ) (localNormUnit K w a))
  rw [hN]

private theorem isArchCompAt_comp_idelicNorm_of_isReal (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hN : ∀ (w₀ : InfinitePlace K) (a : (w₀.Completion)ˣ),
      (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm (archUnitHom w₀ a) =
        archUnitHom (default : InfinitePlace ℚ) (localNormUnit K w₀ a))
    {e : ℂ} {a : ℤ} (hη : IsArchCompAt ℚ η (default : InfinitePlace ℚ) e a) {w : InfinitePlace K} (hw : w.IsReal) :
    IsArchCompAt K (η.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) w e a := by
  unfold IsArchCompAt at hη ⊢
  intro x
  rw [archLocalChar_comp_idelicNorm K η hN w x, hη (localNormUnit K w x), localNormUnit_apply]
  obtain ⟨h1, h2⟩ := norm_eq_of_isReal K hw (x : w.Completion)
  rw [h1, h2, mult_default, show ((w.mult : ℕ) : ℂ) = 1 by rw [InfinitePlace.mult, if_pos hw, Nat.cast_one]]

private theorem isArchCompAt_comp_idelicNorm_of_isComplex (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hN : ∀ (w₀ : InfinitePlace K) (a : (w₀.Completion)ˣ),
      (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm (archUnitHom w₀ a) =
        archUnitHom (default : InfinitePlace ℚ) (localNormUnit K w₀ a))
    {e : ℂ} {a : ℤ} (hη : IsArchCompAt ℚ η (default : InfinitePlace ℚ) e a) {w : InfinitePlace K}
    (hw : w.IsComplex) :
    IsArchCompAt K (η.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) w e 0 := by
  unfold IsArchCompAt at hη ⊢
  intro x
  rw [archLocalChar_comp_idelicNorm K η hN w x, hη (localNormUnit K w x), localNormUnit_apply]
  obtain ⟨h1, h2⟩ := norm_eq_of_isComplex K hw (x : w.Completion)
  have hx : (0 : ℝ) < ‖(x : w.Completion)‖ := norm_pos_iff.2 x.ne_zero
  have hx2 : (((‖(x : w.Completion)‖ ^ 2 : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos hx 2).ne'
  rw [h1, h2, mult_default, div_self hx2, one_zpow, zpow_zero,
    show ((w.mult : ℕ) : ℂ) = 2 by rw [InfinitePlace.mult, if_neg (InfinitePlace.not_isReal_iff_isComplex.2 hw)]; simp]
  simp only [mul_one, one_mul]
  rw [← Real.rpow_two, ← Complex.cpow_mul_ofReal_nonneg hx.le]
  norm_num

end

end

section

open NumberField

section Ambient

variable (K : Type) [Field K] [NumberField K]

private noncomputable abbrev ambientAlgebra : Algebra (𝓞 ℚ) (𝓞 K) := inferInstance

end Ambient

section

variable (K : Type) [Field K] [NumberField K] [instB : Algebra (𝓞 ℚ) (𝓞 K)]

private theorem algebra_eq_ambientAlgebra : instB = ambientAlgebra K := by
  apply Algebra.algebra_ext
  intro r
  show @algebraMap (𝓞 ℚ) (𝓞 K) _ _ instB r = @algebraMap (𝓞 ℚ) (𝓞 K) _ _ (ambientAlgebra K) r
  have h : (@algebraMap (𝓞 ℚ) (𝓞 K) _ _ instB).comp Rat.ringOfIntegersEquiv.symm.toRingHom =
      (@algebraMap (𝓞 ℚ) (𝓞 K) _ _ (ambientAlgebra K)).comp Rat.ringOfIntegersEquiv.symm.toRingHom :=
    Subsingleton.elim _ _
  have hr : r = Rat.ringOfIntegersEquiv.symm (Rat.ringOfIntegersEquiv r) :=
    (Rat.ringOfIntegersEquiv.symm_apply_apply r).symm
  rw [hr]
  exact congrArg (fun f : ℤ →+* 𝓞 K => f (Rat.ringOfIntegersEquiv r)) h

end

end

section

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume
open NumberField.TateGlobal
open LanglandsTunnell LanglandsTunnell.Converse

private theorem admitsModulus_circleNormalization (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) {𝔣 : Ideal (𝓞 ℚ)}
    (h : HeckeCharacter.AdmitsModulus ℚ χ 𝔣) : HeckeCharacter.AdmitsModulus ℚ (circleNormalization χ) 𝔣 :=
  fun u hu hv => circleNormalization_eq_one χ (h u hu hv)

theorem solution
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ)
    (R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ.toRawCentral)
    (hR : Continuous R.toFun)
    (P : RealArchParam)
    (hP : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
        IsArchCompAt ℚ (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) w
          (P.centralExponent + 1) (P.centralSign.val : ℤ))
    (SQ₀ : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
    (hb : ∀ p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ), p ∉ SQ₀ → ‖Φ.b p‖ = 1) :
    ∃ Tq : Finset (HeightOneSpectrum (𝓞 ℚ)), ∃ ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ,
      IsAdmissibleTwist K ω ∧
      (∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∉ Tq →
      IsUnramifiedCharAt ω 𝔓 ∧
        ((ω (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) = (formalBaseChange ℚ K Φ).b 𝔓) ∧
      (∀ (w : InfinitePlace K) (hw : w.IsReal),
      IsArchCompAt K ω w (archOfParamR K P w hw).centralExponent
        ((archOfParamR K P w hw).centralSign.val : ℤ)) ∧
      (∀ (w : InfinitePlace K) (hw : w.IsComplex),
      IsArchCompAt K ω w (archOfParamC K P w hw).centralExponent (archOfParamC K P w hw).centralTwist) := by
  classical
  obtain rfl : ‹Algebra (𝓞 ℚ) (𝓞 K)› = ambientAlgebra K := algebra_eq_ambientAlgebra K
  have hfacts := centralChar_facts Φ R
  have hre : P.centralExponent.re = 0 := re_centralExponent_eq_zero Φ R hR P hP SQ₀ hb
  have hη : IsArchCompAt ℚ (circleNormalization (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom))
      (default : InfinitePlace ℚ) P.centralExponent (P.centralSign.val : ℤ) :=
    isArchCompAt_circleNormalization _ default (hP default default_isReal) hre
  have hmod : HeckeCharacter.AdmitsModulus ℚ
      (circleNormalization (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom)) Φ.level :=
    admitsModulus_circleNormalization _ hfacts.2.1
  have hfin : {v : HeightOneSpectrum (𝓞 ℚ) | v.asIdeal ∣ Φ.level}.Finite :=
    Ideal.finite_factors (by simpa using Φ.level_ne_bot)
  refine ⟨hfin.toFinset ∪ R.exceptionalSet ∪ SQ₀,
    (circleNormalization (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom)).comp
      (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm, ?_, ?_, ?_, ?_⟩
  · exact isAdmissibleTwist_comp_idelicNorm K _ (isIdeleClassChar_circleNormalization_centralChar Φ R)
      (continuous_circleNormalization_centralChar Φ R hR) (norm_circleNormalization _)
  · intro 𝔓 h𝔓
    have hp1 : 𝔓.under (𝓞 ℚ) ∉ hfin.toFinset := fun h =>
      h𝔓 (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have hp2 : 𝔓.under (𝓞 ℚ) ∉ R.exceptionalSet := fun h => h𝔓 (Finset.mem_union_left _ (Finset.mem_union_right _ h))
    have hp3 : 𝔓.under (𝓞 ℚ) ∉ SQ₀ := fun h => h𝔓 (Finset.mem_union_right _ h)
    have hmult : HeckeCharacter.idealMultiplicity ℚ (𝔓.under (𝓞 ℚ)) Φ.level = 0 :=
      idealMultiplicity_eq_zero_of_not_le ℚ _ Φ.level_ne_bot fun hle =>
        hp1 (hfin.mem_toFinset.2 (Ideal.dvd_iff_le.2 hle))
    obtain ⟨hunr, hval⟩ := comp_idelicNorm_isUnramifiedCharAt_and_apply_uniformizerIdele K _ hmod 𝔓 hmult
    refine ⟨hunr, ?_⟩
    rw [hval, formalBaseChange_b_eq K Φ 𝔓]
    congr 1
    rw [circleNormalization_apply, centralChar_comp_uniformizerIdele Φ R hp2]
    exact cNorm_inv_mul_div_norm _ (hb _ hp3)
  · intro w hw
    rw [archOfParamR_apply]
    exact isArchCompAt_comp_idelicNorm_of_isReal K _ (idelicNorm_archUnitHom K) hη hw
  · intro w hw
    rw [archOfParamC_apply, RealArchParam.centralExponent_baseChange, RealArchParam.centralTwist_baseChange]
    exact isArchCompAt_comp_idelicNorm_of_isComplex K _ (idelicNorm_archUnitHom K) hη hw

end

end S_LanglandsTunnell_Converse_exists_isAdmissibleTwist_eq_formalBaseChange_b_isArchCompAt_archOfParam
end P2MW
export P2MW.S_LanglandsTunnell_Converse_exists_isAdmissibleTwist_eq_formalBaseChange_b_isArchCompAt_archOfParam (solution)
