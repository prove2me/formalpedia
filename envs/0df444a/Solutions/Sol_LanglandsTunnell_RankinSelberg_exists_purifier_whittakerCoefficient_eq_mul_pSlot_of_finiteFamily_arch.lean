-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/97f44f96-4f53-5358-8c3e-d8e0ff54365d

import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSGlobalIntegral
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_HonestLDatum
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_NumberField_IdeleBox
import Theorems.Thm_AutomorphicForm_exists_finWhittaker_eq_sum_prod_mul_of_isIsotypicCuspFormAt_placeEmbed_invariant_of_localSpaceAt
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_placeEmbed
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_one_ne_zero_of_isIsotypicCuspFormAt_of_ne_zero
import Definitions.Def_LanglandsTunnell_CubicInduction_FnTwist3
import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Theorems.Thm_RepresentationTheory_Admissible_exists_sum_translate_eq_of_linearIndependent
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply FLT.SmoothAdmissibleSchurCommutant.mem_repStabilizer FLT.SmoothAdmissibleSchurCommutant.mem_fixedVectors"

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField AutomorphicForm~whittakerCoefficient_unipotentGL2_mul LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell LanglandsTunnell.Converse"
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
p2m_open "LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction MeasureTheory"
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open IsDedekindDomain NumberField Matrix
open LanglandsTunnell.CubicInduction NumberField.AdelicLevel AdelicDock

noncomputable section

namespace Ws23PlaceEmbed3

section Generic

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

variable (v : HeightOneSpectrum R)

end Generic

section Family

variable (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))

variable (m : ↥SQ → ℕ)

variable {SQ m}

end Family

end Ws23PlaceEmbed3

end

namespace Ws23Fam5

section IotaComponents

open Matrix NumberField.AdelicLevel AdelicDock UnramifiedWhittaker

local notation "G2" => AdelicGL2 (𝓞 ℚ) ℚ

theorem coe_finFactor (g : G2) :
    (RSCarrier.finFactor g : G2) =
      (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (ratArchGL2 g))⁻¹ * g := rfl

theorem glFin_archRealGLAt (m : GL (Fin 2) ℝ) :
    glFin (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) m) = 1 :=
  glFin_adelicArchGLIncl ℚ _

theorem glFin_finFactor (g : G2) : glFin (𝓞 ℚ) ℚ (RSCarrier.finFactor g : G2) = glFin (𝓞 ℚ) ℚ g := by
  rw [coe_finFactor, map_mul, map_inv, glFin_archRealGLAt, inv_one, one_mul]

end IotaComponents

section WhittakerUnipotentLaw

open Matrix MeasureTheory
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

local notation "G2" => AdelicGL2 (𝓞 ℚ) ℚ
local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ
local notation "μA" => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ

scoped instance isAddHaarMeasure_adelicAddHaar_fam5 : (μA).IsAddHaarMeasure :=
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 ℚ) ℚ

scoped instance countable_principalSubgroup_fam5 : Countable (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) := by
  show Countable {x : 𝔸 // x ∈ Set.range (algebraMap ℚ 𝔸)}
  exact (Set.countable_range _).to_subtype

theorem globalPoints_unipotentGL2 (k : ℚ) :
    globalPoints (𝓞 ℚ) ℚ (unipotentGL2 k) = unipotentGL2 (algebraMap ℚ 𝔸 k) := by
  refine Units.ext ?_
  change (algebraMap ℚ 𝔸).mapMatrix ((unipotentGL2 k : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = _
  rw [unipotentGL2_coe, unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

scoped instance vaddInvariantMeasure_principalSubgroup_fam5 :
    VAddInvariantMeasure (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) 𝔸 μA :=
  ⟨fun k s _ => measure_preimage_add _ (k : 𝔸) s⟩

theorem integral_cond_adelicBox_comp_add_right (P : 𝔸 → ℂ)
    (hP : ∀ (k : AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) (x : 𝔸), P ((k : 𝔸) + x) = P x) (a : 𝔸) :
    ∫ x, P (x + a) ∂(ProbabilityTheory.cond μA (AdelicBox.adelicBox ℚ)) =
      ∫ x, P x ∂(ProbabilityTheory.cond μA (AdelicBox.adelicBox ℚ)) := by
  have hcond : ProbabilityTheory.cond μA (AdelicBox.adelicBox ℚ) =
      ((μA) (AdelicBox.adelicBox ℚ))⁻¹ • (μA).restrict (AdelicBox.adelicBox ℚ) := rfl
  rw [hcond, integral_smul_measure, integral_smul_measure]
  congr 1
  rw [← (measurePreserving_add_right (μA) a).setIntegral_image_emb (measurableEmbedding_addRight a) P
    (AdelicBox.adelicBox ℚ)]
  have hbox := AdelicBox.isAddFundamentalDomain_adelicBox ℚ (μA)
  have himg : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ)
      ((fun x : 𝔸 => x + a) '' AdelicBox.adelicBox ℚ) μA := by
    refine hbox.image_of_equiv (ν := μA) (Equiv.addRight a)
      (by simpa using (measurePreserving_add_right (μA) (-a)).quasiMeasurePreserving) (Equiv.refl _) ?_
    intro k x
    show (k : 𝔸) + x + a = (k : 𝔸) + (x + a)
    rw [add_assoc]
  exact MeasureTheory.IsAddFundamentalDomain.setIntegral_eq himg hbox (f := P) (fun k x => hP k x)

theorem whittakerCoefficient_unipotentGL2_mul (Dp : Set G2) (U : Ideal (𝓞 ℚ) → Subgroup G2)
    (gen : HeightOneSpectrum (𝓞 ℚ) → G2)
    (φ : G2 → ℂ) (hφ : ∀ (γ : GL (Fin 2) ℚ) (g : G2), φ (globalPoints (𝓞 ℚ) ℚ γ * g) = φ g)
    (χ : AddChar 𝔸 ℂ) (hχK : ∀ k : ℚ, χ (algebraMap ℚ 𝔸 k) = 1) (b : 𝔸) (g : G2) :
    whittakerCoefficient ℚ (productionPinsOf ℚ Dp U gen (AdelicBox.adelicBox ℚ)) χ φ 1 (unipotentGL2 b * g) =
      χ b * whittakerCoefficient ℚ (productionPinsOf ℚ Dp U gen (AdelicBox.adelicBox ℚ)) χ φ 1 g := by
  have e1 : ∀ g' : G2, whittakerCoefficient ℚ (productionPinsOf ℚ Dp U gen (AdelicBox.adelicBox ℚ)) χ φ 1 g' =
      ∫ t, φ (unipotentGL2 t * g') * χ (-t) ∂(ProbabilityTheory.cond μA (AdelicBox.adelicBox ℚ)) := by
    intro g'
    show (∫ x, φ (unipotentGL2 x * g') * χ (-(algebraMap ℚ 𝔸 1 * x))
      ∂(ProbabilityTheory.cond μA (AdelicBox.adelicBox ℚ))) = _
    congr 1
    funext x
    rw [map_one, one_mul]
  set P : 𝔸 → ℂ := fun t => φ (unipotentGL2 t * g) * χ (-t) with hP
  have hPer : ∀ (k : AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) (x : 𝔸), P ((k : 𝔸) + x) = P x := by
    rintro ⟨_, k, rfl⟩ x
    simp only [hP]
    rw [unipotentGL2_add, mul_assoc, ← globalPoints_unipotentGL2, hφ, neg_add, AddChar.map_add_eq_mul,
      ← map_neg, hχK, one_mul]
  have hshift : ∀ t : 𝔸, φ (unipotentGL2 t * (unipotentGL2 b * g)) * χ (-t) = χ b * P (t + b) := by
    intro t
    simp only [hP]
    rw [← mul_assoc, ← unipotentGL2_add, mul_left_comm, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  rw [e1, e1]
  simp_rw [hshift]
  rw [integral_const_mul, integral_cond_adelicBox_comp_add_right P hPer b]

noncomputable abbrev fstM (g : G2) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ) :=
  (RingHom.fst (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)).mapMatrix (g : Matrix (Fin 2) (Fin 2) 𝔸)
noncomputable abbrev sndM (g : G2) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  (RingHom.snd (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)).mapMatrix (g : Matrix (Fin 2) (Fin 2) 𝔸)

theorem fstM_mul (g h : G2) : fstM (g * h) = fstM g * fstM h := (RingHom.mapMatrix _).map_mul _ _
theorem sndM_mul (g h : G2) : sndM (g * h) = sndM g * sndM h := (RingHom.mapMatrix _).map_mul _ _

theorem eq_of_fstM_sndM {g h : G2} (h1 : fstM g = fstM h) (h2 : sndM g = sndM h) : g = h := by
  refine Units.ext (Matrix.ext fun i j => Prod.ext ?_ ?_)
  · exact congrFun (congrFun h1 i) j
  · exact congrFun (congrFun h2 i) j

theorem fstM_eq_one_of_mem {g : G2} (hg : g ∈ finiteAdelicGL2Subgroup ℚ) : fstM g = 1 := by
  rw [mem_finiteAdelicGL2Subgroup_iff] at hg
  exact congrArg (fun u : GL (Fin 2) (InfiniteAdeleRing ℚ) => (u : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ))) hg

theorem sndM_archRealGLAt (M : GL (Fin 2) ℝ) :
    sndM (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) M) = 1 :=
  Matrix.ext fun i j => rfl

theorem archRealGLAt_mul_comm {g : G2} (hg : g ∈ finiteAdelicGL2Subgroup ℚ) (M : GL (Fin 2) ℝ) :
    archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) M * g =
      g * archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) M := by
  refine eq_of_fstM_sndM ?_ ?_
  · rw [fstM_mul, fstM_mul, fstM_eq_one_of_mem hg, mul_one, one_mul]
  · rw [sndM_mul, sndM_mul, sndM_archRealGLAt, mul_one, one_mul]

end WhittakerUnipotentLaw

theorem finFactor_coe (g : finiteAdelicGL2Subgroup ℚ) : RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) = g := by
  apply Subtype.ext
  have h1 : ratArchGL2 (g : AdelicGL2 (𝓞 ℚ) ℚ) = 1 := by
    unfold LanglandsTunnell.ratArchGL2
    rw [(mem_finiteAdelicGL2Subgroup_iff ℚ _).1 g.2, map_one, map_one]
  simp only [RSCarrier.finFactor, h1, map_one, inv_one, one_mul]

theorem ratArchGL2_mul_coe (g : AdelicGL2 (𝓞 ℚ) ℚ) (k : finiteAdelicGL2Subgroup ℚ) :
    ratArchGL2 (g * (k : AdelicGL2 (𝓞 ℚ) ℚ)) = ratArchGL2 g := by
  unfold LanglandsTunnell.ratArchGL2
  rw [map_mul, (mem_finiteAdelicGL2Subgroup_iff ℚ _).1 k.2, mul_one]

theorem finFactor_mul_coe (g : AdelicGL2 (𝓞 ℚ) ℚ) (k : finiteAdelicGL2Subgroup ℚ) :
    RSCarrier.finFactor (g * (k : AdelicGL2 (𝓞 ℚ) ℚ)) = RSCarrier.finFactor g * k := by
  apply Subtype.ext
  show _ = ((RSCarrier.finFactor g : AdelicGL2 (𝓞 ℚ) ℚ)) * (k : AdelicGL2 (𝓞 ℚ) ℚ)
  simp only [RSCarrier.finFactor, ratArchGL2_mul_coe, mul_assoc]

theorem ratArchGL2_archRealGLAt (M : GL (Fin 2) ℝ) :
    ratArchGL2 (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) M) = M := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show ringEquivRealOfIsReal (IsTotallyReal.isReal (default : InfinitePlace ℚ))
      ((((archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) M : AdelicGL2 (𝓞 ℚ) ℚ) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).1 default) = _
  have h : ((((archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) M : AdelicGL2 (𝓞 ℚ) ℚ) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).1 default) =
      (ringEquivRealOfIsReal (IsTotallyReal.isReal (default : InfinitePlace ℚ))).symm ((M : Matrix (Fin 2) (Fin 2) ℝ) i j) := by
    show archMatrixUpdate ℚ default ((glEquivOfRingEquiv
      (ringEquivRealOfIsReal (IsTotallyReal.isReal (default : InfinitePlace ℚ))).symm M :
        GL (Fin 2) (default : InfinitePlace ℚ).Completion) : Matrix _ _ _) i j default = _
    rw [archMatrixUpdate_apply_self, glEquivOfRingEquiv_apply_entry]
  rw [h]
  exact (ringEquivRealOfIsReal _).apply_symm_apply _

theorem finFactor_archRealGLAt (M : GL (Fin 2) ℝ) :
    RSCarrier.finFactor (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) M) = 1 := by
  apply Subtype.ext
  show (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ))
      (ratArchGL2 (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) M)))⁻¹ *
        archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) M = 1
  rw [ratArchGL2_archRealGLAt, inv_mul_cancel]

end Ws23Fam5
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

noncomputable section

namespace Ws23Fam5Holes

section Local

variable (p : HeightOneSpectrum (𝓞 ℚ))

end Local
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

section Ugrp

variable (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))) (N : Ideal (𝓞 ℚ))

theorem localAt_apply (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ) (i j : Fin 2) :
    ((localAt ℚ p g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i j =
      (((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 p := by
  rw [show localAt ℚ p g = finComponent (𝓞 ℚ) ℚ p (glFin (𝓞 ℚ) ℚ g) from rfl, finComponent_apply, glFin_apply]

end Ugrp
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

end Ws23Fam5Holes
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

noncomputable section

namespace Ws23Fam5Holes

p2m_open "IsDedekindDomain NumberField AutomorphicForm~whittakerCoefficient_unipotentGL2_mul NumberField.AdelicLevel NumberField.TateGlobal"

section H45

variable (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))

theorem unipotentGL2_fin_mem (ξ : FiniteAdeleRing (𝓞 ℚ) ℚ) :
    (unipotentGL2 (((0 : InfiniteAdeleRing ℚ), ξ) : AdeleRing (𝓞 ℚ) ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) ∈
      finiteAdelicGL2Subgroup ℚ := by
  rw [mem_finiteAdelicGL2Subgroup_iff]
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [glArch_apply, unipotentGL2_coe, Units.val_one]
  fin_cases i <;> fin_cases j <;> rfl

end H45
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

end Ws23Fam5Holes
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

namespace Ws23Fam5Holes

end Ws23Fam5Holes
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

section PencBatch3
open scoped Matrix

namespace Ws23Fam5Holes

section GL3

variable {A : Type*} [CommRing A]

variable {R : Type*} [CommRing R]

end GL3
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

end Ws23Fam5Holes
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

end PencBatch3
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

namespace Ws23Fam5Holes

p2m_open "IsDedekindDomain NumberField AutomorphicForm~whittakerCoefficient_unipotentGL2_mul LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell LanglandsTunnell.CubicInduction NumberField.AdelicLevel"

theorem localAt_unipotentGL2 (b : AdeleRing (𝓞 ℚ) ℚ) (p : HeightOneSpectrum (𝓞 ℚ)) :
    localAt ℚ p (unipotentGL2 b : AdelicGL2 (𝓞 ℚ) ℚ) = unipotentGL2 (b.2 p) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [localAt_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> rfl

end Ws23Fam5Holes
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

section PencN12
open scoped Matrix

namespace Ws23Fam5Holes

p2m_open "IsDedekindDomain NumberField AutomorphicForm~whittakerCoefficient_unipotentGL2_mul NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell.CubicInduction UnramifiedWhittaker"

section OffPlace

variable (p : HeightOneSpectrum (𝓞 ℚ))

theorem localAt_placeEmbed (x : GL (Fin 2) (p.adicCompletion ℚ)) : localAt ℚ p (placeEmbed ℚ p x) = x := by
  change finComponent (𝓞 ℚ) ℚ p (glFin (𝓞 ℚ) ℚ (AdelicDock.finEmbed (𝓞 ℚ) ℚ (AdelicDock.localEmbed (𝓞 ℚ) ℚ p x))) = x
  rw [AdelicDock.glFin_finEmbed, AdelicDock.finComponent_localEmbed_self]

theorem localAt_placeEmbed_of_ne (x : GL (Fin 2) (p.adicCompletion ℚ)) {q : HeightOneSpectrum (𝓞 ℚ)} (hq : q ≠ p) :
    localAt ℚ q (placeEmbed ℚ p x) = 1 := by
  change finComponent (𝓞 ℚ) ℚ q (glFin (𝓞 ℚ) ℚ (AdelicDock.finEmbed (𝓞 ℚ) ℚ (AdelicDock.localEmbed (𝓞 ℚ) ℚ p x))) = 1
  rw [AdelicDock.glFin_finEmbed, AdelicDock.finComponent_localEmbed_of_ne (𝓞 ℚ) ℚ p x hq]

theorem glArch_placeEmbed (x : GL (Fin 2) (p.adicCompletion ℚ)) : glArch (𝓞 ℚ) ℚ (placeEmbed ℚ p x) = 1 :=
  AdelicDock.glArch_finEmbed (𝓞 ℚ) ℚ _

theorem ideleNorm_det_placeEmbed_mul (x : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    ideleNorm ℚ (Matrix.GeneralLinearGroup.det (placeEmbed ℚ p x * g)) =
      (LanglandsTunnell.TateLocal.modulus
          ((Matrix.GeneralLinearGroup.det x : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) *
        ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) := by
  rw [map_mul, ideleNorm_mul, NumberField.TateGlobal.ideleNorm_det_placeEmbed]

end OffPlace
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

section DualLaw

variable {A : Type*} [CommRing A] {R : Type*} [CommRing R]

end DualLaw
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

end Ws23Fam5Holes
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

end PencN12
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

section PencL13
open scoped Matrix Classical

namespace Ws23Fam5Holes

p2m_open "IsDedekindDomain NumberField AutomorphicForm~whittakerCoefficient_unipotentGL2_mul NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell.CubicInduction UnramifiedWhittaker"

section Ext2

theorem ext2 {x y : AdelicGL2 (𝓞 ℚ) ℚ} (harch : glArch (𝓞 ℚ) ℚ x = glArch (𝓞 ℚ) ℚ y)
    (hfin : ∀ q : HeightOneSpectrum (𝓞 ℚ), localAt ℚ q x = localAt ℚ q y) : x = y := by
  refine Matrix.GeneralLinearGroup.ext fun i j => Prod.ext ?_ ?_
  · rw [← glArch_apply, ← glArch_apply, harch]
  · refine RestrictedProduct.ext _ _ fun q => ?_
    have h := congrArg
      (fun u : GL (Fin 2) (q.adicCompletion ℚ) => (u : Matrix (Fin 2) (Fin 2) (q.adicCompletion ℚ)) i j) (hfin q)
    exact h

theorem placeEmbed_mul_comm_of_localAt_eq_one (p : HeightOneSpectrum (𝓞 ℚ)) (x : GL (Fin 2) (p.adicCompletion ℚ))
    {h : AdelicGL2 (𝓞 ℚ) ℚ} (hh : localAt ℚ p h = 1) : placeEmbed ℚ p x * h = h * placeEmbed ℚ p x := by
  refine ext2 ?_ fun q => ?_
  · rw [map_mul, map_mul, glArch_placeEmbed, one_mul, mul_one]
  · rw [map_mul, map_mul]
    by_cases hq : q = p
    · subst hq; rw [localAt_placeEmbed, hh, mul_one, one_mul]
    · rw [localAt_placeEmbed_of_ne p x hq, one_mul, mul_one]

theorem placeEmbed_commute {p q : HeightOneSpectrum (𝓞 ℚ)} (hpq : p ≠ q) (x : GL (Fin 2) (p.adicCompletion ℚ))
    (y : GL (Fin 2) (q.adicCompletion ℚ)) : Commute (placeEmbed ℚ p x) (placeEmbed ℚ q y) :=
  placeEmbed_mul_comm_of_localAt_eq_one p x (localAt_placeEmbed_of_ne q y hpq)

end Ext2
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

section L1

end L1
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

section L3

end L3
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

end Ws23Fam5Holes
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

end PencL13
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

section PencL2
open scoped Matrix Classical

namespace Ws23Fam5Holes

p2m_open "IsDedekindDomain NumberField AutomorphicForm~whittakerCoefficient_unipotentGL2_mul NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell.CubicInduction UnramifiedWhittaker"

section L2

variable (T : Finset (HeightOneSpectrum (𝓞 ℚ)))

theorem placesComm (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    ((T : Set (HeightOneSpectrum (𝓞 ℚ)))).Pairwise
      (Function.onFun Commute fun p : HeightOneSpectrum (𝓞 ℚ) => placeEmbed ℚ p (localAt ℚ p g)) :=
  fun _ _ _ _ hpq => placeEmbed_commute hpq _ _

noncomputable def placesProd (g : AdelicGL2 (𝓞 ℚ) ℚ) : AdelicGL2 (𝓞 ℚ) ℚ :=
  T.noncommProd (fun p : HeightOneSpectrum (𝓞 ℚ) => placeEmbed ℚ p (localAt ℚ p g)) (placesComm T g)

theorem localAt_placesProd_of_mem (g : AdelicGL2 (𝓞 ℚ) ℚ) {p : HeightOneSpectrum (𝓞 ℚ)} (hp : p ∈ T) :
    localAt ℚ p (placesProd T g) = localAt ℚ p g := by
  classical
  unfold placesProd
  rw [Finset.map_noncommProd, ← Finset.noncommProd_erase_mul _ hp,
    Finset.noncommProd_eq_pow_card _ _ _ 1 (fun q hq => localAt_placeEmbed_of_ne q _ (Finset.ne_of_mem_erase hq).symm),
    one_pow, one_mul, localAt_placeEmbed]

theorem localAt_placesProd_of_not_mem (g : AdelicGL2 (𝓞 ℚ) ℚ) {p : HeightOneSpectrum (𝓞 ℚ)} (hp : p ∉ T) :
    localAt ℚ p (placesProd T g) = 1 := by
  unfold placesProd
  rw [Finset.map_noncommProd,
    Finset.noncommProd_eq_pow_card _ _ _ 1 (fun q hq => localAt_placeEmbed_of_ne q _
      (fun h : p = q => hp (by rw [h]; exact hq))), one_pow]

theorem glArch_placesProd (g : AdelicGL2 (𝓞 ℚ) ℚ) : glArch (𝓞 ℚ) ℚ (placesProd T g) = 1 := by
  unfold placesProd
  rw [Finset.map_noncommProd, Finset.noncommProd_eq_pow_card _ _ _ 1 (fun q _ => glArch_placeEmbed q _), one_pow]

end L2
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

end Ws23Fam5Holes
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

end PencL2
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

section PencDE
open scoped Matrix Classical

namespace Ws23Fam5Holes

p2m_open "IsDedekindDomain NumberField AutomorphicForm~whittakerCoefficient_unipotentGL2_mul NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell LanglandsTunnell.CubicInduction UnramifiedWhittaker"

end Ws23Fam5Holes
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

end PencDE
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

section Ws23MiniPlaceKit

p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg"

noncomputable section

namespace Ws23HeckeLocalDualPort

open Matrix NumberField.AdelicVolume UnramifiedWhittaker

local notation "G2" => AdelicGL2 (𝓞 ℚ) ℚ
local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ

section Place

variable (p : HeightOneSpectrum (𝓞 ℚ))

abbrev Kp : Type := p.adicCompletion ℚ

private theorem _root_.Ws23HeckeLocalDualPort.localAt_placeEmbed (x : GL (Fin 2) (Kp p)) : localAt ℚ p (placeEmbed ℚ p x) = x := by
  show AdelicLevel.finComponent (𝓞 ℚ) ℚ p (AdelicLevel.glFin (𝓞 ℚ) ℚ
    (AdelicDock.finEmbed (𝓞 ℚ) ℚ (AdelicDock.localEmbed (𝓞 ℚ) ℚ p x))) = x
  rw [AdelicDock.glFin_finEmbed, AdelicDock.finComponent_localEmbed_self]

p2m_export "Ws23HeckeLocalDualPort" "localAt_placeEmbed"
end Place
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

end Ws23HeckeLocalDualPort
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

end Ws23MiniPlaceKit
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

section prover2_prefactor

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.TateGlobal
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction LanglandsTunnell.Converse"
p2m_open "UnramifiedWhittaker AutomorphicForm~whittakerCoefficient_unipotentGL2_mul"

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.IsAdmissibleTwist Converse.IsArchCompAt TateLocal.addCharLevel TateLocal.HasConductorExponentAt TateLocal.conductorExponentAt TateLocal.modulus TateLocal.modulus_pos TateLocal.modulus_mul RealArchParam signShift RealArchParam.discrete RealArchParam.principal CubicInduction.psiLoc ratArchGL2 TateLocal.modulus_adicCompletion_eq_nnnorm"
namespace RankinSelberg
p2m_export "LanglandsTunnell.RankinSelberg" "primeFibre"
namespace EntirePairAssembly
namespace Prefactor
p2m_open "LanglandsTunnell.RankinSelberg LanglandsTunnell"

section NormAlgebra
variable {G : Type*} [Group G] (ν : G → ℝ) (hmul : ∀ a b, ν (a * b) = ν a * ν b) (hone : ν 1 = 1) (hpos : ∀ a, 0 < ν a)
end NormAlgebra
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

variable (v : HeightOneSpectrum (𝓞 ℚ))

section Fibre
variable (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]

end Fibre
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

end LanglandsTunnell.RankinSelberg.EntirePairAssembly.Prefactor
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

end prover2_prefactor
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

section prover2_hlev

open IsDedekindDomain NumberField NumberField.StandardAddChar LanglandsTunnell.TateLocal

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.IsAdmissibleTwist Converse.IsArchCompAt TateLocal.addCharLevel TateLocal.HasConductorExponentAt TateLocal.conductorExponentAt TateLocal.modulus TateLocal.modulus_pos TateLocal.modulus_mul RealArchParam signShift RealArchParam.discrete RealArchParam.principal CubicInduction.psiLoc ratArchGL2 TateLocal.modulus_adicCompletion_eq_nnnorm"
namespace RankinSelberg
p2m_export "LanglandsTunnell.RankinSelberg" "primeFibre"
namespace EntirePairAssembly
namespace Prefactor
p2m_open "LanglandsTunnell.RankinSelberg LanglandsTunnell"

end LanglandsTunnell.RankinSelberg.EntirePairAssembly.Prefactor
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

end prover2_hlev
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

namespace Ws23Tw

open LanglandsTunnell.CubicInduction

structure TwCubic (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (S₀ : Finset (HeightOneSpectrum (𝓞 ℚ))) where

  whittakerLoc : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ

  cenLoc : (v : HeightOneSpectrum (𝓞 ℚ)) → (v.adicCompletion ℚ)ˣ →* ℂˣ
  whittakerLoc_law : ∀ v, IsGL3PsiWhittakerFn (psiLoc ψ v) (whittakerLoc v)
  spherical : ∀ v, ¬ IsBadPlace K μ v →
    IsInducedSphericalAt (inducedCoeff K μ) v (localMaximalCompact3 (𝓞 ℚ) ℚ v) (whittakerLoc v)
  levelInvariant : ∀ v, v ∉ S₀ →
    ∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ v (inducedLevelAt K μ v), ∀ g, whittakerLoc v (g * k) = whittakerLoc v g
  continuous : ∀ v, Continuous (whittakerLoc v)
  ne_zero : ∀ v, whittakerLoc v ≠ 0
  scalar : ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
    whittakerLoc v (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((cenLoc v t : ℂˣ) : ℂ) * whittakerLoc v h
  gauge : ∀ p : HeightOneSpectrum (𝓞 ℚ), ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 p,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → whittakerLoc p h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖whittakerLoc p h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t)

private noncomputable def _root_.Ws23Tw.twist (χA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 ℚ)) (W : LocalGL3 v → ℂ) : LocalGL3 v → ℂ :=
  fun x => ((NumberField.TateGlobal.localChar χA v (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W x

p2m_export "Ws23Tw" "twist"
end Ws23Tw
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

namespace Ws23Fam5

theorem finWhittaker_laws
    (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ) (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ.toRawCentral)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hiso : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) R.centralChar Φ.level S Φ φ) (hφne : φ ≠ 0)
    (WA : GL (Fin 2) ℝ → ℂ) (Wf : finiteAdelicGL2Subgroup ℚ → ℂ)
    (hWAf : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      whittakerCoefficient ℚ (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
        NumberField.StandardAddChar.psiQ φ 1 g = WA (ratArchGL2 g) * Wf (RSCarrier.finFactor g)) :
    (∃ M : GL (Fin 2) ℝ, WA M ≠ 0) ∧
    (∀ (b : FiniteAdeleRing (𝓞 ℚ) ℚ) (t : finiteAdelicGL2Subgroup ℚ),
      Wf (⟨unipotentGL2 (((0 : InfiniteAdeleRing ℚ), b) : AdeleRing (𝓞 ℚ) ℚ), Ws23Fam5Holes.unipotentGL2_fin_mem b⟩ * t) =
        NumberField.StandardAddChar.psiQ (((0 : InfiniteAdeleRing ℚ), b) : AdeleRing (𝓞 ℚ) ℚ) * Wf t) ∧
    (∀ u : finiteAdelicGL2Subgroup ℚ, (u : AdelicGL2 (𝓞 ℚ) ℚ) ∈ (productionPinsGeneral ℚ).U Φ.level →
      ∀ t : finiteAdelicGL2Subgroup ℚ, Wf (t * u) = Wf t) := by
  have hφinv : ∀ (γ : GL (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ (globalPoints (𝓞 ℚ) ℚ γ * g) = φ g :=
    fun γ g => (@AutomorphicForm.LsXiMember.toIsLsXiFunction _ _ _ _ _ _ _ _ _ (_) _ _
      hiso.smoothCusp.1.1).left_invariant γ g
  have hWAne : ∃ M : GL (Fin 2) ℝ, WA M ≠ 0 := by
    by_contra h
    push Not at h
    refine AutomorphicForm.whittakerCoefficient_one_ne_zero_of_isIsotypicCuspFormAt_of_ne_zero _ R.centralChar
      Φ.level S Φ φ hiso hφne (funext fun g => ?_)
    rw [hWAf, h, zero_mul, Pi.zero_apply]
  obtain ⟨M, hM⟩ := hWAne
  refine ⟨⟨M, hM⟩, fun b t => ?_, fun u hu t => ?_⟩
  · have key := whittakerCoefficient_unipotentGL2_mul (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2)
      (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) φ hφinv
      NumberField.StandardAddChar.psiQ NumberField.StandardAddChar.psiQ_algebraMap
      (((0 : InfiniteAdeleRing ℚ), b) : AdeleRing (𝓞 ℚ) ℚ)
      (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) M * (t : AdelicGL2 (𝓞 ℚ) ℚ))
    rw [← mul_assoc, ← archRealGLAt_mul_comm (Ws23Fam5Holes.unipotentGL2_fin_mem b) M, mul_assoc] at key
    have hcoe : (unipotentGL2 (((0 : InfiniteAdeleRing ℚ), b) : AdeleRing (𝓞 ℚ) ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) * (t : AdelicGL2 (𝓞 ℚ) ℚ) =
        ((⟨unipotentGL2 (((0 : InfiniteAdeleRing ℚ), b) : AdeleRing (𝓞 ℚ) ℚ), Ws23Fam5Holes.unipotentGL2_fin_mem b⟩ * t :
          finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) := rfl
    erw [hcoe, hWAf, hWAf] at key
    rw [ratArchGL2_mul_coe, finFactor_mul_coe, ratArchGL2_mul_coe, finFactor_mul_coe, ratArchGL2_archRealGLAt,
      finFactor_archRealGLAt, one_mul, one_mul, mul_left_comm] at key
    exact mul_left_cancel₀ hM key
  · have hlevφ : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ∀ k ∈ (productionPinsGeneral ℚ).U Φ.level, φ (g * k) = φ g :=
      hiso.level_invariant
    have hWφ : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
        whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ 1 (g * (u : AdelicGL2 (𝓞 ℚ) ℚ)) =
          whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ 1 g := by
      intro g
      simp only [whittakerCoefficient, ← mul_assoc, hlevφ _ _ hu]
    have key := hWφ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) M * (t : AdelicGL2 (𝓞 ℚ) ℚ))
    rw [mul_assoc, ← Subgroup.coe_mul] at key
    erw [hWAf, hWAf] at key
    rw [ratArchGL2_mul_coe, finFactor_mul_coe, ratArchGL2_mul_coe, finFactor_mul_coe, ratArchGL2_archRealGLAt,
      finFactor_archRealGLAt, one_mul, one_mul] at key
    exact mul_left_cancel₀ hM key

end Ws23Fam5
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

namespace Ws23Fam5Holes

p2m_open "IsDedekindDomain NumberField AutomorphicForm~whittakerCoefficient_unipotentGL2_mul NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell LanglandsTunnell.CubicInduction UnramifiedWhittaker"

end Ws23Fam5Holes
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

namespace Ws23Fam5Holes

p2m_open "IsDedekindDomain NumberField AutomorphicForm~whittakerCoefficient_unipotentGL2_mul NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell LanglandsTunnell.CubicInduction UnramifiedWhittaker"

section SupportedOn

variable (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))

def IsSupportedOn (h : AdelicGL2 (𝓞 ℚ) ℚ) : Prop :=
  glArch (𝓞 ℚ) ℚ h = 1 ∧ ∀ q : HeightOneSpectrum (𝓞 ℚ), q ∉ SQ → localAt ℚ q h = 1

theorem isSupportedOn_placeEmbed {p : HeightOneSpectrum (𝓞 ℚ)} (hp : p ∈ SQ) (x : GL (Fin 2) (p.adicCompletion ℚ)) :
    IsSupportedOn SQ (placeEmbed ℚ p x) :=
  ⟨glArch_placeEmbed p x, fun q hq => localAt_placeEmbed_of_ne p x (fun h => hq (h ▸ hp))⟩

theorem IsSupportedOn.mul {h h' : AdelicGL2 (𝓞 ℚ) ℚ} (hh : IsSupportedOn SQ h) (hh' : IsSupportedOn SQ h') :
    IsSupportedOn SQ (h * h') :=
  ⟨by rw [map_mul, hh.1, hh'.1, mul_one], fun q hq => by rw [map_mul, hh.2 q hq, hh'.2 q hq, mul_one]⟩

theorem IsSupportedOn.conj {h : AdelicGL2 (𝓞 ℚ) ℚ} (hh : IsSupportedOn SQ h) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    IsSupportedOn SQ (g⁻¹ * h * g) :=
  ⟨by rw [map_mul, map_mul, map_inv, hh.1, mul_one, inv_mul_cancel],
    fun q hq => by rw [map_mul, map_mul, map_inv, hh.2 q hq, mul_one, inv_mul_cancel]⟩

theorem IsSupportedOn.eq_placesProd {h : AdelicGL2 (𝓞 ℚ) ℚ} (hh : IsSupportedOn SQ h) : h = placesProd SQ h := by
  refine ext2 ?_ fun q => ?_
  · rw [hh.1, glArch_placesProd]
  · by_cases hq : q ∈ SQ
    · rw [localAt_placesProd_of_mem SQ h hq]
    · rw [hh.2 q hq, localAt_placesProd_of_not_mem SQ h hq]

variable {SQ}

theorem mul_eq_of_placeEmbed_invariant {X : Type*} (f : AdelicGL2 (𝓞 ℚ) ℚ → X)
    (hf : ∀ (p : ↥SQ) (x : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      f (g * placeEmbed ℚ (p : HeightOneSpectrum (𝓞 ℚ)) x) = f g)
    {h : AdelicGL2 (𝓞 ℚ) ℚ} (hh : IsSupportedOn SQ h) (g : AdelicGL2 (𝓞 ℚ) ℚ) : f (g * h) = f g := by
  rw [hh.eq_placesProd]
  unfold placesProd
  refine Finset.noncommProd_induction SQ _ (placesComm SQ h) (fun x => ∀ g, f (g * x) = f g) ?_ ?_ ?_ g
  · intro a b ha hb g
    rw [← mul_assoc, hb, ha]
  · intro g; rw [mul_one]
  · intro p hp g
    exact hf ⟨p, hp⟩ _ g

theorem mul_left_eq_of_placeEmbed_invariant {X : Type*} (f : AdelicGL2 (𝓞 ℚ) ℚ → X)
    (hf : ∀ (p : ↥SQ) (x : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      f (g * placeEmbed ℚ (p : HeightOneSpectrum (𝓞 ℚ)) x) = f g)
    {h : AdelicGL2 (𝓞 ℚ) ℚ} (hh : IsSupportedOn SQ h) (g : AdelicGL2 (𝓞 ℚ) ℚ) : f (h * g) = f g := by
  have h1 : h * g = g * (g⁻¹ * h * g) := by group
  rw [h1]
  exact mul_eq_of_placeEmbed_invariant f hf (hh.conj SQ g) g

variable (SQ)

end SupportedOn
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

section Weyl

theorem glArch_unipotentGL2_fin (b : FiniteAdeleRing (𝓞 ℚ) ℚ) :
    glArch (𝓞 ℚ) ℚ (unipotentGL2 (((0 : InfiniteAdeleRing ℚ), b) : AdeleRing (𝓞 ℚ) ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) = 1 :=
  (mem_finiteAdelicGL2Subgroup_iff ℚ _).1 (unipotentGL2_fin_mem b)

end Weyl
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

end Ws23Fam5Holes
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

namespace Ws23Fam5Holes

p2m_open "IsDedekindDomain NumberField AutomorphicForm~whittakerCoefficient_unipotentGL2_mul NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell LanglandsTunnell.CubicInduction UnramifiedWhittaker"

section Centrality

end Centrality
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

section FinFactor

theorem ratArchGL2_coe_mul (k : finiteAdelicGL2Subgroup ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    ratArchGL2 ((k : AdelicGL2 (𝓞 ℚ) ℚ) * g) = ratArchGL2 g := by
  unfold LanglandsTunnell.ratArchGL2
  rw [map_mul, (mem_finiteAdelicGL2Subgroup_iff ℚ _).1 k.2, one_mul]

theorem finFactor_coe_mul (k : finiteAdelicGL2Subgroup ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    RSCarrier.finFactor ((k : AdelicGL2 (𝓞 ℚ) ℚ) * g) = k * RSCarrier.finFactor g := by
  apply Subtype.ext
  show (archRealGLAt _ (ratArchGL2 ((k : AdelicGL2 (𝓞 ℚ) ℚ) * g)))⁻¹ * ((k : AdelicGL2 (𝓞 ℚ) ℚ) * g) =
    (k : AdelicGL2 (𝓞 ℚ) ℚ) * ((archRealGLAt _ (ratArchGL2 g))⁻¹ * g)
  rw [ratArchGL2_coe_mul]
  have hc := Ws23Fam5.archRealGLAt_mul_comm k.2 (ratArchGL2 g)
  have hci : (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (ratArchGL2 g))⁻¹ * (k : AdelicGL2 (𝓞 ℚ) ℚ) =
      (k : AdelicGL2 (𝓞 ℚ) ℚ) * (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (ratArchGL2 g))⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hc, mul_assoc, mul_inv_cancel, mul_one]
  rw [← mul_assoc, hci, mul_assoc]

end FinFactor
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

section UnitNorms

theorem det_unipotentGL2_val {A : Type*} [CommRing A] (x : A) :
    Matrix.det ((unipotentGL2 x : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = 1 := by
  rw [unipotentGL2_coe, Matrix.det_fin_two_of]; ring

end UnitNorms
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

section Levels

end Levels
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

end Ws23Fam5Holes
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

namespace Ws23Fam5Holes

p2m_open "IsDedekindDomain NumberField AutomorphicForm~whittakerCoefficient_unipotentGL2_mul NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell LanglandsTunnell.CubicInduction UnramifiedWhittaker"

section FlipOff

variable (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))

end FlipOff
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

section MixedGL2

variable (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))) (w₀ : GL (Fin 2) ℚ) (H : AdelicGL2 (𝓞 ℚ) ℚ)

variable {SQ w₀ H}

end MixedGL2
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

section CubicLaws

open scoped Classical

variable (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
  (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) {μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
  (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))) (F : Ws23Tw.TwCubic K ψ μ SQ)
  (W' : ∀ p : ↥SQ, LocalGL3 p.1 → ℂ)
  (BTv1 : ∀ v : HeightOneSpectrum (𝓞 ℚ), LocalGL3 v → ℂ)
  (hBTv1 : ∀ v y, BTv1 v y = if hv : v ∈ SQ then W' ⟨v, hv⟩ y else dualWhittakerFn3 (F.whittakerLoc v) y)

include hBTv1

end CubicLaws
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

end Ws23Fam5Holes
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

namespace Ws23W2

p2m_open "IsDedekindDomain NumberField AutomorphicForm~whittakerCoefficient_unipotentGL2_mul NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell LanglandsTunnell.CubicInduction UnramifiedWhittaker P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5Holes P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

theorem localAt_finFactor (r : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    localAt ℚ r (RSCarrier.finFactor g : AdelicGL2 (𝓞 ℚ) ℚ) = localAt ℚ r g := by
  show finComponent (𝓞 ℚ) ℚ r (glFin (𝓞 ℚ) ℚ _) = finComponent (𝓞 ℚ) ℚ r (glFin (𝓞 ℚ) ℚ g)
  rw [glFin_finFactor]

end Ws23W2
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

namespace Ws23W2

p2m_open "IsDedekindDomain NumberField AutomorphicForm~whittakerCoefficient_unipotentGL2_mul NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell LanglandsTunnell.CubicInduction UnramifiedWhittaker P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5Holes P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

end Ws23W2
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

namespace Ws23W2

p2m_open "IsDedekindDomain NumberField AutomorphicForm~whittakerCoefficient_unipotentGL2_mul NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell LanglandsTunnell.CubicInduction UnramifiedWhittaker P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5Holes P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

end Ws23W2
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

namespace Ws23Fam5Holes

p2m_open "IsDedekindDomain NumberField AutomorphicForm~whittakerCoefficient_unipotentGL2_mul NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell LanglandsTunnell.CubicInduction UnramifiedWhittaker MeasureTheory"

end Ws23Fam5Holes
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

section PenbSwapStep
open LanglandsTunnell.TateLocal UnramifiedWhittaker

noncomputable section

namespace Ws23SwapStep

open LanglandsTunnell.CubicInduction RSCarrier NumberField.AdelicLevel AdelicDock

private theorem _root_.Ws23SwapStep.localAt_placeEmbed_of_ne {p q : HeightOneSpectrum (𝓞 ℚ)} (hq : q ≠ p) (x : GL (Fin 2) (p.adicCompletion ℚ)) :
    localAt ℚ q (placeEmbed ℚ p x) = 1 := by
  show finComponent (𝓞 ℚ) ℚ q (glFin (𝓞 ℚ) ℚ (finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ p x))) = 1
  rw [glFin_finEmbed, finComponent_localEmbed_of_ne (𝓞 ℚ) ℚ p x hq]

p2m_export "Ws23SwapStep" "localAt_placeEmbed_of_ne"

theorem ratArchGL2_mul_placeEmbed (p : HeightOneSpectrum (𝓞 ℚ)) (G : AdelicGL2 (𝓞 ℚ) ℚ) (x : GL (Fin 2) (p.adicCompletion ℚ)) :
    LanglandsTunnell.ratArchGL2 (G * placeEmbed ℚ p x) = LanglandsTunnell.ratArchGL2 G := by
  unfold LanglandsTunnell.ratArchGL2
  rw [map_mul, show glArch (𝓞 ℚ) ℚ (placeEmbed ℚ p x) = 1 from glArch_finEmbed (𝓞 ℚ) ℚ _, mul_one]

theorem ratArchGL2_placeEmbed (p : HeightOneSpectrum (𝓞 ℚ)) (x : GL (Fin 2) (p.adicCompletion ℚ)) :
    LanglandsTunnell.ratArchGL2 (placeEmbed ℚ p x) = 1 := by
  have := ratArchGL2_mul_placeEmbed p 1 x
  rwa [one_mul, show LanglandsTunnell.ratArchGL2 (1 : AdelicGL2 (𝓞 ℚ) ℚ) = 1 from by
    unfold LanglandsTunnell.ratArchGL2; rw [map_one, map_one, map_one]] at this

theorem ratArchGL2_coe (g : finiteAdelicGL2Subgroup ℚ) : LanglandsTunnell.ratArchGL2 (g : AdelicGL2 (𝓞 ℚ) ℚ) = 1 := by
  unfold LanglandsTunnell.ratArchGL2
  rw [(mem_finiteAdelicGL2Subgroup_iff ℚ _).1 g.2, map_one, map_one]

private theorem _root_.Ws23SwapStep.coe_finFactor (G : AdelicGL2 (𝓞 ℚ) ℚ) : (finFactor G : AdelicGL2 (𝓞 ℚ) ℚ) =
    (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (LanglandsTunnell.ratArchGL2 G))⁻¹ * G := rfl

p2m_export "Ws23SwapStep" "coe_finFactor"
private theorem _root_.Ws23SwapStep.finFactor_coe (g : finiteAdelicGL2Subgroup ℚ) : finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) = g := by
  apply Subtype.ext
  rw [coe_finFactor, ratArchGL2_coe, map_one, inv_one, one_mul]

p2m_export "Ws23SwapStep" "finFactor_coe"
theorem coe_finFactor_placeEmbed (p : HeightOneSpectrum (𝓞 ℚ)) (x : GL (Fin 2) (p.adicCompletion ℚ)) :
    (finFactor (placeEmbed ℚ p x) : AdelicGL2 (𝓞 ℚ) ℚ) = placeEmbed ℚ p x := by
  rw [coe_finFactor, ratArchGL2_placeEmbed, map_one, inv_one, one_mul]

theorem finFactor_mul_placeEmbed (p : HeightOneSpectrum (𝓞 ℚ)) (G : AdelicGL2 (𝓞 ℚ) ℚ) (x : GL (Fin 2) (p.adicCompletion ℚ)) :
    finFactor (G * placeEmbed ℚ p x) = finFactor G * finFactor (placeEmbed ℚ p x) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, coe_finFactor, coe_finFactor, coe_finFactor_placeEmbed, ratArchGL2_mul_placeEmbed, mul_assoc]

end Ws23SwapStep
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

namespace Ws23SwapStep

open LanglandsTunnell.CubicInduction RSCarrier NumberField.AdelicLevel AdelicDock

end Ws23SwapStep
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

namespace Ws23SwapStep

end Ws23SwapStep
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

namespace Ws23SwapStep

end Ws23SwapStep
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

namespace Ws23SwapStep

end Ws23SwapStep
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

namespace Ws23SwapStep

end Ws23SwapStep
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

namespace Ws23SwapStep

end Ws23SwapStep
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

namespace Ws23SwapStep

p2m_open "AutomorphicForm~whittakerCoefficient_unipotentGL2_mul" in
theorem whittakerCoefficient_mul_right {F : Type} [Field F] [NumberField F] (pins : CarrierPins F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F) (X Y : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ φ α (X * Y) = whittakerCoefficient F pins ψ (fun x => φ (x * Y)) α X := by
  unfold whittakerCoefficient
  simp only [mul_assoc]

p2m_open "AutomorphicForm~whittakerCoefficient_unipotentGL2_mul" in open  AutomorphicForm.WhittakerModel in
theorem localFnAt_translate {F : Type} [Field F] [NumberField F] (pins : CarrierPins F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (h : GL (Fin 2) (v.adicCompletion F)) (g : GL (Fin 2) (v.adicCompletion F)) :
    localFnAt F pins ψ v φ (g * h) =
      localFnAt F pins ψ v (fun x => φ (x * AdelicDock.finEmbed (𝓞 F) F (AdelicDock.localEmbed (𝓞 F) F v h))) g := by
  unfold localFnAt
  rw [map_mul, map_mul, whittakerCoefficient_mul_right]

p2m_open "AutomorphicForm~whittakerCoefficient_unipotentGL2_mul" in open  AutomorphicForm.WhittakerModel in

theorem localSpaceAt_translate_mem {F : Type} [Field F] [NumberField F] (pins : CarrierPins F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    ∀ W ∈ localSpaceAt F pins ψ v φ, ∀ h : GL (Fin 2) (v.adicCompletion F),
      (fun g => W (g * h)) ∈ localSpaceAt F pins ψ v φ := by
  intro W hW h
  refine Submodule.span_induction (p := fun W _ => (fun g => W (g * h)) ∈ localSpaceAt F pins ψ v φ)
    ?_ ?_ ?_ ?_ hW
  · rintro _ ⟨h', rfl⟩
    refine Submodule.subset_span ⟨AdelicDock.finEmbed (𝓞 F) F (AdelicDock.localEmbed (𝓞 F) F v h) * h', ?_⟩
    funext g
    rw [localFnAt_translate]
    simp only [mul_assoc]
  · exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    exact Submodule.add_mem _ hx hy
  · intro a x _ hx
    exact Submodule.smul_mem _ a hx

end Ws23SwapStep
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

namespace Ws23SwapStep

section TranslateSpan
variable {G : Type*} [Group G]

end TranslateSpan
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

end Ws23SwapStep
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

end PenbSwapStep
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

namespace Ws23PencSwap

p2m_open "IsDedekindDomain NumberField AutomorphicForm~whittakerCoefficient_unipotentGL2_mul NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell LanglandsTunnell.CubicInduction UnramifiedWhittaker MeasureTheory"

open scoped Pointwise

section Stage

open scoped Classical

end Stage
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

end Ws23PencSwap
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

namespace Ws23Cubic

p2m_open "IsDedekindDomain NumberField AutomorphicForm~whittakerCoefficient_unipotentGL2_mul NumberField.AdelicLevel LanglandsTunnell.CubicInduction"

section Continuity3

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R)

end Continuity3
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

end Ws23Cubic
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

namespace Ws23Cubic

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

variable {v : HeightOneSpectrum (𝓞 ℚ)}

end Ws23Cubic
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

namespace Ws23Cubic

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

end Ws23Cubic
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

namespace Ws23Cubic

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

end Ws23Cubic
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

namespace Ws23Cubic

p2m_open "IsDedekindDomain NumberField AutomorphicForm~whittakerCoefficient_unipotentGL2_mul NumberField.AdelicLevel LanglandsTunnell.CubicInduction"

end Ws23Cubic
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

namespace Ws23Fam5Holes

p2m_open "IsDedekindDomain NumberField AutomorphicForm~whittakerCoefficient_unipotentGL2_mul NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell LanglandsTunnell.CubicInduction UnramifiedWhittaker MeasureTheory"

theorem continuous_modulus_det_real (p : HeightOneSpectrum (𝓞 ℚ)) :
    Continuous fun y : GL (Fin 2) (p.adicCompletion ℚ) =>
      ((LanglandsTunnell.TateLocal.modulus
        ((Matrix.GeneralLinearGroup.det y : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : NNReal) : ℝ) := by
  have h : (fun y : GL (Fin 2) (p.adicCompletion ℚ) =>
      ((LanglandsTunnell.TateLocal.modulus
        ((Matrix.GeneralLinearGroup.det y : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : NNReal) : ℝ)) =
      fun y : GL (Fin 2) (p.adicCompletion ℚ) => ‖Matrix.det (y : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))‖ := by
    funext y
    rw [Matrix.GeneralLinearGroup.val_det_apply, LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p, coe_nnnorm]
  rw [h]
  exact continuous_norm.comp (Units.continuous_val.matrix_det)

end Ws23Fam5Holes
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

section W2
open UnramifiedWhittaker LanglandsTunnell.TateLocal NumberField.AdelicLevel NumberField.TateGlobal AdelicDock

namespace Ws23W2

section Twist

variable {G : Type*} [Group G]

end Twist
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

variable (p : HeightOneSpectrum (𝓞 ℚ))

end Ws23W2
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

end W2
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

namespace Ws23Cubic

p2m_open "IsDedekindDomain NumberField AutomorphicForm~whittakerCoefficient_unipotentGL2_mul NumberField.AdelicLevel LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell LanglandsTunnell.CubicInduction UnramifiedWhittaker"

end Ws23Cubic
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

namespace Ws23Cubic

p2m_open "IsDedekindDomain NumberField AutomorphicForm~whittakerCoefficient_unipotentGL2_mul NumberField.AdelicLevel LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell LanglandsTunnell.CubicInduction UnramifiedWhittaker MeasureTheory"

end Ws23Cubic
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

namespace Ws23Nrest

p2m_open "IsDedekindDomain NumberField AutomorphicForm~whittakerCoefficient_unipotentGL2_mul NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg UnramifiedWhittaker P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5Holes"

section CutOff

variable (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))

end CutOff
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

end Ws23Nrest
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

section Eta0Off
open NumberField.AdelicLevel NumberField.TateGlobal AdelicDock Ws23Fam5Holes

end Eta0Off
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

namespace Ws23Tw

end Ws23Tw
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

namespace Ws23PencMatch

p2m_open "IsDedekindDomain NumberField LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg"

end Ws23PencMatch
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

namespace Ws23Fam5Holes

p2m_open "IsDedekindDomain NumberField AutomorphicForm~whittakerCoefficient_unipotentGL2_mul NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell LanglandsTunnell.CubicInduction UnramifiedWhittaker"

end Ws23Fam5Holes
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

namespace Ws23Regroup

theorem exists_linearIndepOn_finset_repr {K X ι : Type*} [Field K] [Fintype ι] (u : ι → X → K) :
    ∃ (s : Finset ι) (d : ι → ι → K), LinearIndepOn K u (s : Set ι) ∧ ∀ i x, u i x = ∑ j ∈ s, d i j * u j x := by
  classical
  obtain ⟨s, hind, hmax⟩ := exists_maximal_linearIndepOn K u
  have hmem : ∀ i, u i ∈ Submodule.span K (u '' s) := by
    intro i
    by_cases hi : i ∈ s
    · exact Submodule.subset_span ⟨i, hi, rfl⟩
    · obtain ⟨a, ha, h⟩ := hmax i hi
      have := Submodule.smul_mem _ a⁻¹ h
      rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at this
  have hrepr : ∀ i, ∃ d : ι →₀ K, (↑d.support ⊆ s) ∧ u i = d.sum fun j a => a • u j := by
    intro i
    obtain ⟨d, hds, hd⟩ := (Finsupp.mem_span_image_iff_linearCombination (R := K) (v := u)).1 (hmem i)
    exact ⟨d, (Finsupp.mem_supported K d).1 hds, by rw [← hd, Finsupp.linearCombination_apply]⟩
  choose d hds hd using hrepr
  refine ⟨s.toFinset, fun i j => d i j, by simpa using hind, fun i x => ?_⟩
  conv_lhs => rw [hd i]
  rw [Finsupp.sum, Finset.sum_apply]
  refine Finset.sum_subset (by simpa using hds i) fun j _ hj => ?_
  rw [Finsupp.notMem_support_iff.1 hj]; simp

end Ws23Regroup
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

namespace Ws23Away

p2m_open "IsDedekindDomain NumberField AutomorphicForm~whittakerCoefficient_unipotentGL2_mul NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell LanglandsTunnell.CubicInduction LanglandsTunnell.Converse LanglandsTunnell.TateLocal LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg UnramifiedWhittaker P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly.Prefactor"

end Ws23Away
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

namespace Ws23Cubic

p2m_open "IsDedekindDomain NumberField AutomorphicForm~whittakerCoefficient_unipotentGL2_mul LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction"

end Ws23Cubic
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

namespace Ws23Fam5

end Ws23Fam5
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

namespace Ws23Cubic

open IsDedekindDomain NumberField MeasureTheory

end Ws23Cubic
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

section W2EtaArch
open NumberField.AdelicVolume NumberField.InfinitePlace.Completion LanglandsTunnell.Converse

namespace Ws23W2

end Ws23W2
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

end W2EtaArch
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

namespace Ws23GaugeMem

open LanglandsTunnell.CubicInduction Matrix

variable {L : Type*} [NormedField L]

end Ws23GaugeMem
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

namespace Ws23Jpss

p2m_open "IsDedekindDomain NumberField AutomorphicForm~whittakerCoefficient_unipotentGL2_mul LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction"

open scoped nonZeroDivisors

end Ws23Jpss
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

namespace Ws23Jpss

p2m_open "IsDedekindDomain NumberField AutomorphicForm~whittakerCoefficient_unipotentGL2_mul LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction"

open scoped nonZeroDivisors

end Ws23Jpss
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

namespace Ws23Fam5

namespace Ws23J6e

p2m_open "IsDedekindDomain NumberField AutomorphicForm~whittakerCoefficient_unipotentGL2_mul NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell.Converse"

end Ws23J6e
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

end Ws23Fam5
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace Ws23Tw

open LanglandsTunnell.CubicInduction

variable {v : HeightOneSpectrum (𝓞 ℚ)}

end Ws23Tw
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

namespace Ws23Tw

end Ws23Tw
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

namespace Ws23Tw

end Ws23Tw
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField AutomorphicForm~whittakerCoefficient_unipotentGL2_mul LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell LanglandsTunnell.Converse"
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
p2m_open "LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction MeasureTheory"
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

section GamJPSec

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

noncomputable section

namespace GamJP

open UnramifiedWhittaker

local notation "G2" => AdelicGL2 (𝓞 ℚ) ℚ
local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ
local notation "μA" => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ

abbrev pinsQ (D : Set G2) : CarrierPins ℚ :=
  productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
    (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)

theorem W_apply (D : Set G2) (χ : AddChar 𝔸 ℂ) (f : G2 → ℂ) (g : G2) :
    whittakerCoefficient ℚ (pinsQ D) χ f 1 g = ∫ x, f (unipotentGL2 x * g) * χ (-x)
      ∂(ProbabilityTheory.cond μA (adelicBox ℚ)) := by
  show (∫ x, f (unipotentGL2 x * g) * χ (-(algebraMap ℚ 𝔸 1 * x)) ∂(ProbabilityTheory.cond μA (adelicBox ℚ))) = _
  congr 1; funext x; rw [map_one, one_mul]

theorem integrable_cond_adelicBox {f : 𝔸 → ℂ} (hf : Continuous f) :
    Integrable f (ProbabilityTheory.cond μA (adelicBox ℚ)) := by
  obtain ⟨C, hC, hsub⟩ := NumberField.AdelicBox.exists_isCompact_adelicBox_subset (K := ℚ)
  have h1 : IntegrableOn f (adelicBox ℚ) μA := (hf.continuousOn.integrableOn_compact hC).mono_set hsub
  have hcond : ProbabilityTheory.cond μA (adelicBox ℚ) = ((μA) (adelicBox ℚ))⁻¹ • (μA).restrict (adelicBox ℚ) := rfl
  rw [hcond]
  exact h1.integrable.smul_measure (ENNReal.inv_ne_top.2 (NumberField.AdelicBox.adelicAddHaar_adelicBox_pos (K := ℚ)).ne')

theorem W_finsum (D : Set G2) (χ : AddChar 𝔸 ℂ) (hχ : Continuous χ) {n : ℕ} (c : Fin n → ℂ) (f : Fin n → G2 → ℂ)
    (hf : ∀ i, Continuous (f i)) (g : G2) :
    whittakerCoefficient ℚ (pinsQ D) χ (fun z => ∑ i, c i * f i z) 1 g =
      ∑ i, c i * whittakerCoefficient ℚ (pinsQ D) χ (f i) 1 g := by
  rw [W_apply]
  simp_rw [W_apply, Finset.sum_mul]
  rw [integral_finset_sum _ (fun i _ => ?_)]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    ring
  · have hc : Continuous fun y : 𝔸 => c i * f i (unipotentGL2 y * g) * χ (-y) :=
      (continuous_const.mul ((hf i).comp ((AutomorphicForm.continuous_unipotentGL2 (R := 𝔸)).mul continuous_const))).mul
        (hχ.comp continuous_neg)
    exact integrable_cond_adelicBox hc

theorem det_unipotentGL2 (x : 𝔸) : Matrix.GeneralLinearGroup.det (unipotentGL2 x : G2) = 1 := by
  refine Units.ext ?_
  change Matrix.det ((unipotentGL2 x : G2) : Matrix (Fin 2) (Fin 2) 𝔸) = 1
  rw [unipotentGL2_coe, Matrix.det_fin_two_of]
  ring

theorem W_detNorm_translate (D : Set G2) (χ : AddChar 𝔸 ℂ) (f : G2 → ℂ) (k h g : G2) (e : ℂ) :
    whittakerCoefficient ℚ (pinsQ D) χ (fun z => (((detNorm (z * k)) : ℝ) : ℂ) ^ e * f (z * k * h)) 1 g =
      (((detNorm (g * k)) : ℝ) : ℂ) ^ e * whittakerCoefficient ℚ (pinsQ D) χ f 1 (g * k * h) := by
  rw [W_apply, W_apply, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have hd : detNorm (unipotentGL2 y * g * k) = detNorm (g * k) := by
    unfold detNorm; rw [mul_assoc, map_mul, det_unipotentGL2, one_mul]
  show (((detNorm (unipotentGL2 y * g * k)) : ℝ) : ℂ) ^ e * f (unipotentGL2 y * g * k * h) * χ (-y) =
    (((detNorm (g * k)) : ℝ) : ℂ) ^ e * (f (unipotentGL2 y * (g * k * h)) * χ (-y))
  rw [hd]
  simp only [mul_assoc]

end GamJP
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

end GamJPSec
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Fam5"

set_option maxHeartbeats 4000000 in
open MeasureTheory LanglandsTunnell.TateLocal UnramifiedWhittaker in
open scoped Classical in

theorem solution
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ)
    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hSQ : (∀ p : HeightOneSpectrum (𝓞 ℚ), Φ.level ≤ p.asIdeal → p ∈ SQ) ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∉ SQ →
        Ideal.ramificationIdx' (𝔓.under (𝓞 ℚ)).asIdeal 𝔓.asIdeal = 1)
    (hb : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → ‖Φ.b p‖ = 1)
    (ha : ∀ σ : ℝ, 1 < σ →
      Summable fun p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) =>
        ‖Φ.a p‖ * (Ideal.absNorm p.asIdeal : ℝ) ^ (-σ))
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (hSK : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓 ∈ SK ↔ 𝔓.under (𝓞 ℚ) ∈ SQ)
    (P : RealArchParam)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hS : S ⊆ SQ)
    (R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ.toRawCentral) (hRc : Continuous R.toFun)
    (Cfin : FiniteAdeleRing (𝓞 ℚ) ℚ → AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hRS : R.exceptionalSet ⊆ S)
    (hP1 : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1)
    (hP2 : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₂ →
          ∀ p : ℤ, p ≠ 0 → u₁ - u₂ = (p : ℂ) → a₁ - a₂ ≠ ((p + 1 : ℤ) : ZMod 2))
    (hRcen : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
        IsArchCompAt ℚ (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) w
          (P.centralExponent + 1) (P.centralSign.val : ℤ))
    (φv : (InfinitePlace ℚ → ZMod 2) → AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (Wr : (InfinitePlace ℚ → ZMod 2) → InfinitePlace ℚ → ℂ → ℂ)
    (kw : (InfinitePlace ℚ → ZMod 2) → InfinitePlace ℚ → ℤ)
    (hiso : ∀ par, IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) R.centralChar Φ.level S Φ (φv par))
    (hφne : ∀ par, φv par ≠ 0)
    (hφKf : ∀ par, ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ (φv par) α = φv par)
    (hφarch : ∀ par, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
        HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (kw par w)) (φv par))
    (hkw1 : ∀ par, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₂ →
          (kw par w : ℂ) = signShift (a₁ + par w) + signShift (a₂ + par w))
    (hkw2 : ∀ par, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
        P = RealArchParam.discrete u₀ n hn → kw par w = (n : ℤ) + 1)
    (hφW : ∀ par, ∀ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, g ∈ finiteAdelicGL2Subgroup ℚ →
        whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ (φv par) 1 (diagOne a * g)
          = (∏ w : InfinitePlace ℚ, Wr par w (extensionEmbedding w ((a : AdeleRing (𝓞 ℚ) ℚ).1 w)))
              * Cfin (a : AdeleRing (𝓞 ℚ) ℚ).2 g)
    (hWr1 : ∀ par, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₁ → par w = a₁ →
          ∀ t : ℝ, Wr par w (-t) = (-1 : ℂ) ^ a₁.val * Wr par w t)
    (hWr2 : ∀ par, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
        P = RealArchParam.discrete u₀ n hn → ∀ t : ℝ, t < 0 → Wr par w t = 0)
    (hWr3 : ∀ par, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₁ → par w = a₁ + 1 →
          ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
            MellinConvergent (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ a₁.val * Wr par w (-t)) / (t : ℂ)) s ∧
              mellin (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ a₁.val * Wr par w (-t)) / (t : ℂ)) s
                = (2 * s + u₁ + u₂ - 1) / (4 * (Real.pi : ℂ)) * (P.twist 0 a₁).archFactor s)
    (hWr4 : ∀ par, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (b : ZMod 2),
        (b = par w ∨ b = par w + P.centralSign) →
          ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
            MellinConvergent (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ b.val * Wr par w (-t)) / (t : ℂ)) s ∧
              mellin (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ b.val * Wr par w (-t)) / (t : ℂ)) s
                = (P.twist 0 b).archFactor s)
    (Tq : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hω : IsAdmissibleTwist K ω)
    (hωT : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∉ Tq →
      IsUnramifiedCharAt ω 𝔓 ∧
        ((ω (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) = (formalBaseChange ℚ K Φ).b 𝔓)
    (hE : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∈ Tq → 𝔓 ∈ SK)
    (hωR : ∀ (w : InfinitePlace K) (hw : w.IsReal),
      IsArchCompAt K ω w (archOfParamR K P w hw).centralExponent
        ((archOfParamR K P w hw).centralSign.val : ℤ))
    (hωC : ∀ (w : InfinitePlace K) (hw : w.IsComplex),
      IsArchCompAt K ω w (archOfParamC K P w hw).centralExponent (archOfParamC K P w hw).centralTwist)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (hoff : ¬ (∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal))
    (hdepth : ∀ w : ↥SK,
      4 * (FractionalIdeal.count K w.1
            ((Φ.level.map (algebraMap (𝓞 ℚ) (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) +
          LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K w.1) + 1) ≤
        LanglandsTunnell.TateLocal.conductorExponentAt K w.1 (localChar μ w.1))
    (χA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχA : LanglandsTunnell.Converse.IsAdmissibleTwist ℚ χA)
    (hχoff : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ → IsUnramifiedCharAt χA v)
    (kχ : HeightOneSpectrum (𝓞 ℚ) → ℕ)
    (hkχ : ∀ p ∈ SQ,
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p (NumberField.TateGlobal.localChar χA p) (kχ p))
    (hχinf : ∀ v : InfinitePlace ℚ, v.IsReal → LanglandsTunnell.Converse.IsArchCompAt ℚ χA v 0 0)
    (c₀ : HeightOneSpectrum (𝓞 ℚ) → ℕ)
    (hν : ∀ p ∈ SQ, ∀ w ∈ primeFibre ℚ K p, ∃ c : ℕ, c ≤ c₀ p ∧
      LanglandsTunnell.TateLocal.HasConductorExponentAt K w
        (NumberField.TateGlobal.localChar
          (μ * (χA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)⁻¹) w) c)
    (bQ : HeightOneSpectrum (𝓞 ℚ) → ℕ)
    (hbQ : ∀ p ∈ SQ, p.asIdeal ^ bQ p ∣ Φ.level ∧ ¬ p.asIdeal ^ (bQ p + 1) ∣ Φ.level)
    (hkfloor : ∀ p ∈ SQ,
      6 * ((bQ p : ℤ) + 3 * (2 * ((∑ᶠ w ∈ primeFibre ℚ K p,
              ((w.under (𝓞 ℚ)).asIdeal.inertiaDeg' w.asIdeal : ℤ) *
                ((Ideal.ramificationIdx' (w.under (𝓞 ℚ)).asIdeal w.asIdeal : ℤ) *
                    (2 * ((52 : ℤ) + 3 * (c₀ p : ℤ)) +
                      LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K w) + 2) +
                  (c₀ p : ℤ) + LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K w) + 1)) +
            ((52 : ℤ) + 3 * (c₀ p : ℤ)))) + 3) + 7 ≤ (kχ p : ℤ))
    (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hνadm : LanglandsTunnell.Converse.IsAdmissibleTwist K ν)
    (hμν : μ = ν * χA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ)
    (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ)
    (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (hcR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (hcC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw))
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ)
    (hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (hψQ : ψ⁻¹ = NumberField.StandardAddChar.psiQ)
    (F : CubicInductionForm K (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ψ ν)
    (hF0 : F.form ≠ 0 ∧ ∀ v, ¬ IsRamifiedIn K v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
        F.whittakerLoc v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K ν) v (F.whittakerLoc v))
    (hFc : Continuous F.form) (hFw : Continuous F.whittaker) (hFdw : Continuous F.dualWhittaker)
    (hFg : IsGaugeMajorised3 ℚ F.whittaker) (hFdg : IsGaugeMajorised3 ℚ F.dualWhittaker)
    (hBad :
        ∀ T : Finset (HeightOneSpectrum (𝓞 ℚ)),
          (∀ v ∈ T, IsBadPlace K ν v → ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
            ∀ k ∈ Uv, ∀ g : LocalGL3 v, F.whittakerLoc v (g * k) = F.whittakerLoc v g) ∧
          (∀ v ∈ T, IsBadPlace K ν v → ∀ W ∈ gl3CyclicSubspace (F.whittakerLoc v), W ≠ 0 →
            F.whittakerLoc v ∈ gl3CyclicSubspace W))
    (S' : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSS' : SQ ⊆ S')
    (hgood : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S' → ¬ IsBadPlace K μ p)
    (ϖ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p.adicCompletionIntegers ℚ)
    (hπ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
      algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p) ≠ 0)
    (hϖ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
      Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) = WithZero.exp (-1 : ℤ))
    (mP : ∀ p : ↥SQ, LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)) → ℂ)
    (hmPmem : ∀ p : ↥SQ, mP p ∈ gl3CyclicSubspace
      (fun g : LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)) => ((NumberField.TateGlobal.localChar χA (p : HeightOneSpectrum (𝓞 ℚ)) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ)) g))
    (hmP1 : ∀ p : ↥SQ, mP p 1 = 1)
    (hW₃admM : ∀ p : ↥SQ, ∀ Uv : Subgroup (LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ))), IsOpen (Uv : Set (LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)))) →
      ∃ B : Finset (LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)) → ℂ), ∀ W ∈ gl3CyclicSubspace (mP p),
        (∀ k ∈ Uv, ∀ g : LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)), W (g * k) = W g) → W ∈ Submodule.span ℂ (B : Set (LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)) → ℂ)))
    (hW₃irrM : ∀ p : ↥SQ, ∀ W ∈ gl3CyclicSubspace (mP p), W ≠ 0 → mP p ∈ gl3CyclicSubspace W)
    (hμf : finiteAdelicGL2Subgroup ℚ)
    (hhμf : (hμf : AdelicGL2 (𝓞 ℚ) ℚ) =
      ((S' \ SQ).toList.map (fun p => if hp : p ∉ SQ then
          UnramifiedWhittaker.placeEmbed ℚ p
            ((UnramifiedWhittaker.scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p))
              (hπ p hp)) ^ (-(inducedLevelAt K μ p : ℤ)))
        else 1)).prod)
    (WA : (InfinitePlace ℚ → ZMod 2) → GL (Fin 2) ℝ → ℂ)
    (Wf : (InfinitePlace ℚ → ZMod 2) → finiteAdelicGL2Subgroup ℚ → ℂ)
    (hWAf : ∀ par (g : AdelicGL2 (𝓞 ℚ) ℚ),
      whittakerCoefficient ℚ (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ (φv par) 1 g = WA par (ratArchGL2 g) * Wf par (RSCarrier.finFactor g))
    (hWfC : ∀ par (g : finiteAdelicGL2Subgroup ℚ), Wf par g = Cfin 1 (g : AdelicGL2 (𝓞 ℚ) ℚ))
    (hWf1 : ∀ par, Wf par 1 ≠ 0)
    (hV : ∀ par, ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ SQ →
      ((∀ W₀ ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
          W₀ ≠ 0 → ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
            W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => W₀ (g * h))) ∧
        (∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
          ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ), ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
            (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g) → W ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))) ∧
        (∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
          ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g)))
    (w₀ : GL (Fin 2) ℚ) (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) ℚ) = !![0, 1; 1, 0])
    (Wfd : (InfinitePlace ℚ → ZMod 2) → finiteAdelicGL2Subgroup ℚ → ℂ)
    (hWfd : ∀ par (gf : finiteAdelicGL2Subgroup ℚ), Wfd par gf =
      ((NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (gf : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) *
        Wf par (RSCarrier.finFactor (globalPoints (𝓞 ℚ) ℚ w₀ * transposeInvN (Fin 2) (gf : AdelicGL2 (𝓞 ℚ) ℚ))))
    (par : InfinitePlace ℚ → ZMod 2) (p : HeightOneSpectrum (𝓞 ℚ)) (hp : p ∈ SQ)
    (w₂b : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂b : w₂b ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par))
    (h₂ : AdelicGL2 (𝓞 ℚ) ℚ) (hh₂ : localAt ℚ p h₂ = 1) :
    ∃ (nP : ℕ) (cP : Fin nP → ℂ) (xP : Fin nP → GL (Fin 2) (p.adicCompletion ℚ))
      (wA : GL (Fin 2) ℝ → ℂ) (wf : finiteAdelicGL2Subgroup ℚ → ℂ) (wp : GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
      (∀ (x : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        wf (RSCarrier.finFactor (g * placeEmbed ℚ p x)) = wf (RSCarrier.finFactor g)) ∧
      Measurable wf ∧
      (∀ (t : AdeleRing (𝓞 ℚ) ℚ), t.1 = 0 →
        ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, wf (RSCarrier.finFactor (unipotentGL2 t * g)) =
          (ψ⁻¹ t * LanglandsTunnell.CubicInduction.psiLoc ψ p (t.2 p)) * wf (RSCarrier.finFactor g)) ∧
      (∀ (t : p.adicCompletion ℚ) (y : GL (Fin 2) (p.adicCompletion ℚ)),
        wp (unipotent t * y) = NumberField.StandardAddChar.psiLocal ℚ p t * wp y) ∧
      wp ≠ 0 ∧
      (∃ w₁ ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
        ∀ y : GL (Fin 2) (p.adicCompletion ℚ), wp y = ((modulus ((Matrix.GeneralLinearGroup.det y : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * w₁ y) ∧
      (∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
        whittakerCoefficient ℚ (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ψ⁻¹
            (fun g : AdelicGL2 (𝓞 ℚ) ℚ => ∑ j, cP j * (((detNorm (g * placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * φv par (g * placeEmbed ℚ p (xP j) * h₂))) 1 g =
          wp (localAt ℚ p g) * (wA (ratArchGL2 g) * wf (RSCarrier.finFactor g))) ∧

      (∃ g : AdelicGL2 (𝓞 ℚ) ℚ,
        whittakerCoefficient ℚ (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ψ⁻¹
            (fun g : AdelicGL2 (𝓞 ℚ) ℚ => ∑ j, cP j * (((detNorm (g * placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * φv par (g * placeEmbed ℚ p (xP j) * h₂))) 1 g ≠ 0) := by
  classical

  obtain ⟨m, w, W', hw0, hW1, hw2, hW3, hw4, hW5, hw6, hw7, hw8, hsplit⟩ :=
    AutomorphicForm.exists_finWhittaker_eq_sum_prod_mul_of_isIsotypicCuspFormAt_placeEmbed_invariant_of_localSpaceAt Φ S R
      φv hiso hφne WA Wf hWAf par ({p} : Finset (HeightOneSpectrum (𝓞 ℚ)))
      (fun q hq => by rw [Finset.mem_singleton] at hq; rw [hq]; exact hV par p hp)
  let P : ↥({p} : Finset (HeightOneSpectrum (𝓞 ℚ))) := ⟨p, Finset.mem_singleton_self p⟩
  haveI : Subsingleton ↥({p} : Finset (HeightOneSpectrum (𝓞 ℚ))) :=
    ⟨fun a b => Subtype.ext ((Finset.mem_singleton.1 a.2).trans (Finset.mem_singleton.1 b.2).symm)⟩
  have hprodT : ∀ (α : Fin m) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      (∏ q : ↥({p} : Finset (HeightOneSpectrum (𝓞 ℚ))), w q α (localAt ℚ (q : HeightOneSpectrum (𝓞 ℚ)) g)) =
        w P α (localAt ℚ p g) := fun α g => Fintype.prod_subsingleton _ P

  obtain ⟨s, d, hind, hrep⟩ := Ws23Regroup.exists_linearIndepOn_finset_repr (fun α : Fin m => w P α)
  obtain ⟨W'', hW''⟩ : ∃ W'' : Fin m → AdelicGL2 (𝓞 ℚ) ℚ → ℂ, ∀ β g, W'' β g = ∑ α, d α β * W' α g :=
    ⟨_, fun _ _ => rfl⟩
  have hsplit' : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      Wf par (RSCarrier.finFactor g) = ∑ β ∈ s, w P β (localAt ℚ p g) * W'' β g := by
    intro g
    rw [hsplit g]
    calc ∑ α : Fin m, (∏ q : ↥({p} : Finset (HeightOneSpectrum (𝓞 ℚ))), w q α (localAt ℚ (q : HeightOneSpectrum (𝓞 ℚ)) g)) * W' α g
        = ∑ α : Fin m, (∑ β ∈ s, d α β * w P β (localAt ℚ p g)) * W' α g :=
          Finset.sum_congr rfl fun α _ => by rw [hprodT, hrep α]
      _ = ∑ α : Fin m, ∑ β ∈ s, w P β (localAt ℚ p g) * (d α β * W' α g) :=
          Finset.sum_congr rfl fun α _ => by rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun β _ => by ring
      _ = ∑ β ∈ s, w P β (localAt ℚ p g) * W'' β g := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun β _ => ?_
          rw [hW'', Finset.mul_sum]

  have hsplitF : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      Wf par (RSCarrier.finFactor g) =
        ∑ β ∈ s, w P β (localAt ℚ p g) * W'' β ((RSCarrier.finFactor g : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) := by
    intro g
    have h := hsplit' ((RSCarrier.finFactor g : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)
    rw [Ws23Fam5.finFactor_coe, Ws23W2.localAt_finFactor] at h
    exact h

  have hW''1 : ∀ (β : Fin m) (x : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      W'' β (g * placeEmbed ℚ p x) = W'' β g := by
    intro β x g
    rw [hW'', hW'']
    exact Finset.sum_congr rfl fun α _ => by rw [hW1 α P x g]

  have hW''m : ∀ β : Fin m, Measurable fun g : finiteAdelicGL2Subgroup ℚ => W'' β (g : AdelicGL2 (𝓞 ℚ) ℚ) := by
    intro β
    have hfun : (fun g : finiteAdelicGL2Subgroup ℚ => W'' β (g : AdelicGL2 (𝓞 ℚ) ℚ)) =
        fun g : finiteAdelicGL2Subgroup ℚ => ∑ α, d α β * W' α (g : AdelicGL2 (𝓞 ℚ) ℚ) := funext fun g => hW'' β _
    rw [hfun]
    exact Finset.measurable_sum _ fun α _ => (hW5 α).const_mul _

  have hne : ∃ β ∈ s, ∃ g₁ : finiteAdelicGL2Subgroup ℚ, W'' β (g₁ : AdelicGL2 (𝓞 ℚ) ℚ) ≠ 0 := by
    by_contra hall
    push Not at hall
    refine AutomorphicForm.whittakerCoefficient_one_ne_zero_of_isIsotypicCuspFormAt_of_ne_zero _ R.centralChar
      Φ.level S Φ (φv par) (hiso par) (hφne par) (funext fun g => ?_)
    rw [hWAf par g, hsplitF g, Finset.sum_eq_zero (fun β hβ => ?_), mul_zero, Pi.zero_apply]
    rw [hall β hβ, mul_zero]
  obtain ⟨β₀, hβ₀, g₁, hg₁⟩ := hne
  obtain ⟨M₀, hM₀⟩ := (Ws23Fam5.finWhittaker_laws Φ S R (φv par) (hiso par) (hφne par) (WA par) (Wf par) (hWAf par)).1

  let V := AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par)
  let k : ℕ := s.card
  let ε : Fin k → Fin m := fun i => ((s.equivFin.symm i : ↥s) : Fin m)
  have hεmem : ∀ i, ε i ∈ s := fun i => (s.equivFin.symm i).2
  let i₀ : Fin k := s.equivFin ⟨β₀, hβ₀⟩
  have hεi₀ : ε i₀ = β₀ := by simp [ε, i₀]
  have hindk : LinearIndependent ℂ (fun i : Fin k => w P (ε i)) :=
    hind.comp (fun i : Fin k => s.equivFin.symm i) s.equivFin.symm.injective
  obtain ⟨nP, c, x, hcx⟩ :=
    RepresentationTheory.Admissible.exists_sum_translate_eq_of_linearIndependent
      (GL (Fin 2) (p.adicCompletion ℚ)) V
      (Ws23SwapStep.localSpaceAt_translate_mem (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par))
      (hV par p hp).1 (hV par p hp).2.1 (hV par p hp).2.2
      k (fun i => w P (ε i)) (fun i => hw0 P (ε i)) hindk
      (fun i => if i = i₀ then w P β₀ else 0)
      (fun i => by
        show (if i = i₀ then w P β₀ else (0 : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)) ∈ V
        split_ifs
        exacts [hw0 P β₀, Submodule.zero_mem _])

  have hpur : ∀ (β : Fin m), β ∈ s → ∀ y : GL (Fin 2) (p.adicCompletion ℚ),
      ∑ j, c j * w P β (y * x j) = if β = β₀ then w P β₀ y else 0 := by
    intro β hβ y
    have h := congrFun (hcx (s.equivFin ⟨β, hβ⟩)) y
    have hεβ : ε (s.equivFin ⟨β, hβ⟩) = β := by simp [ε]
    simp only [hεβ] at h
    rw [h]
    by_cases hb : β = β₀
    · subst hb
      simp [i₀]
    · have : s.equivFin ⟨β, hβ⟩ ≠ i₀ := fun h' => hb (by
        have := congrArg (fun i => ((s.equivFin.symm i : ↥s) : Fin m)) h'
        simpa [i₀] using this)
      simp [this, hb]

  have hRmul : ∀ a b : AdelicGL2 (𝓞 ℚ) ℚ, ratArchGL2 (a * b) = ratArchGL2 a * ratArchGL2 b := fun a b => by
    unfold LanglandsTunnell.ratArchGL2; rw [map_mul, map_mul, map_mul]
  have hfFarch : ∀ (M : GL (Fin 2) ℝ) (Z : AdelicGL2 (𝓞 ℚ) ℚ),
      RSCarrier.finFactor (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) M * Z) = RSCarrier.finFactor Z := by
    intro M Z
    apply Subtype.ext
    rw [Ws23Fam5.coe_finFactor, Ws23Fam5.coe_finFactor, hRmul, Ws23Fam5.ratArchGL2_archRealGLAt, map_mul, _root_.mul_inv_rev,
      mul_assoc, ← mul_assoc _ (archRealGLAt _ M) Z, inv_mul_cancel, one_mul]
  have hgsplit : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      g = archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (ratArchGL2 g) *
        ((RSCarrier.finFactor g : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) := fun g => by
    rw [Ws23Fam5.coe_finFactor, mul_inv_cancel_left]
  have hlocR : ∀ M : GL (Fin 2) ℝ, localAt ℚ p (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) M) = 1 := by
    intro M
    show finComponent (𝓞 ℚ) ℚ p (glFin (𝓞 ℚ) ℚ _) = 1
    rw [Ws23Fam5.glFin_archRealGLAt, map_one]
  have hdetn : ∀ t : p.adicCompletion ℚ, Matrix.GeneralLinearGroup.det (unipotent t : GL (Fin 2) (p.adicCompletion ℚ)) = 1 := by
    intro t
    rw [show (unipotent t : GL (Fin 2) (p.adicCompletion ℚ)) = unipotentGL2 t from Units.ext rfl]
    exact Units.ext (by rw [Matrix.GeneralLinearGroup.val_det_apply, Ws23Fam5Holes.det_unipotentGL2_val, Units.val_one])

  have hWfin' : ∀ (β : Fin m) (Z : AdelicGL2 (𝓞 ℚ) ℚ) (x : GL (Fin 2) (p.adicCompletion ℚ)),
      W'' β ((RSCarrier.finFactor (Z * placeEmbed ℚ p x * h₂) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) =
        W'' β ((RSCarrier.finFactor (Z * h₂) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) := by
    intro β Z x
    rw [mul_assoc, Ws23Fam5Holes.placeEmbed_mul_comm_of_localAt_eq_one p x hh₂, ← mul_assoc, Ws23SwapStep.finFactor_mul_placeEmbed,
      Subgroup.coe_mul, Ws23SwapStep.coe_finFactor_placeEmbed, hW''1]

  obtain ⟨y₀, hy₀⟩ : ∃ y, w P β₀ y ≠ 0 := Function.ne_iff.1 (hind.ne_zero hβ₀)

  have hmpos : ∀ y : GL (Fin 2) (p.adicCompletion ℚ), 0 < (LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det y : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) :=
    fun y => NNReal.coe_pos.2 (LanglandsTunnell.TateLocal.modulus_pos (Units.ne_zero _))
  have hNpos : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, 0 < ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) := fun g => ideleNorm_pos _
  have hNx : ∀ (g : AdelicGL2 (𝓞 ℚ) ℚ) (x : GL (Fin 2) (p.adicCompletion ℚ)),
      detNorm (g * placeEmbed ℚ p x) = ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) * (LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det x : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) := by
    intro g x
    unfold detNorm
    rw [map_mul, mul_comm, ← map_mul, Ws23Fam5Holes.ideleNorm_det_placeEmbed_mul, mul_comm]
  have hcpow0 : ∀ {r : ℝ}, 0 < r → ∀ e : ℂ, ((r : ℂ)) ^ e ≠ 0 := fun hr e =>
    fun h => by
      have := Complex.norm_cpow_eq_rpow_re_of_pos hr e
      rw [h, norm_zero] at this
      exact (Real.rpow_pos_of_pos hr _).ne' this.symm

  have hφc : Continuous (φv par) := (hiso par).continuous
  have hψc : Continuous (ψ⁻¹ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) := by
    have : ((ψ⁻¹ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) : AdeleRing (𝓞 ℚ) ℚ → ℂ) = fun a => ψ (-a) :=
      funext fun a => AddChar.inv_apply ψ a
    rw [this]; exact hψ.continuous.comp continuous_neg

  have hdn : Continuous (detNorm : AdelicGL2 (𝓞 ℚ) ℚ → ℝ) := continuous_ideleNorm_det ℚ
  have hfg : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, RSCarrier.finFactor (g * h₂) =
      RSCarrier.finFactor (((RSCarrier.finFactor g : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) * h₂) := by
    intro g
    have : g * h₂ = archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (ratArchGL2 g) * ((((RSCarrier.finFactor g : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)) * h₂) := by
      rw [← mul_assoc, ← hgsplit g]
    rw [this, hfFarch]
  have hfact : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      whittakerCoefficient ℚ (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ψ⁻¹ (fun g : AdelicGL2 (𝓞 ℚ) ℚ => ∑ j, c j * ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det (x j) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ ((1 / 2 : ℂ)) * (((detNorm (g * placeEmbed ℚ p (x j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * φv par (g * placeEmbed ℚ p (x j) * h₂))) 1 g =
        (fun y : GL (Fin 2) (p.adicCompletion ℚ) => ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det y : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * w P β₀ y) (localAt ℚ p g) * ((fun M : GL (Fin 2) ℝ => ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) M)) : ℂ)) ^ (-(1 / 2 : ℂ)) * WA par (M * ratArchGL2 h₂)) (ratArchGL2 g) * (fun gf : finiteAdelicGL2Subgroup ℚ => ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (gf : AdelicGL2 (𝓞 ℚ) ℚ)) / (LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det (localAt ℚ p (gf : AdelicGL2 (𝓞 ℚ) ℚ)) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * W'' β₀ ((RSCarrier.finFactor ((gf : AdelicGL2 (𝓞 ℚ) ℚ) * h₂) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)) (RSCarrier.finFactor g)) := by
    intro g
    have hlin : whittakerCoefficient ℚ (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ψ⁻¹ (fun g : AdelicGL2 (𝓞 ℚ) ℚ => ∑ j, c j * ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det (x j) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ ((1 / 2 : ℂ)) * (((detNorm (g * placeEmbed ℚ p (x j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * φv par (g * placeEmbed ℚ p (x j) * h₂))) 1 g =
        ∑ j, (c j * ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det (x j) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ ((1 / 2 : ℂ))) * whittakerCoefficient ℚ (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ψ⁻¹ (fun z : AdelicGL2 (𝓞 ℚ) ℚ => ((detNorm (z * placeEmbed ℚ p (x j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * φv par (z * placeEmbed ℚ p (x j) * h₂)) 1 g :=
      GamJP.W_finsum (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) ψ⁻¹ hψc
        (fun j => c j * ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det (x j) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ ((1 / 2 : ℂ)))
        (fun j => (fun z : AdelicGL2 (𝓞 ℚ) ℚ => ((detNorm (z * placeEmbed ℚ p (x j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * φv par (z * placeEmbed ℚ p (x j) * h₂)))
        (fun j => (Continuous.cpow (Complex.continuous_ofReal.comp (hdn.comp (continuous_mul_right _))) continuous_const
          (fun z => Complex.ofReal_mem_slitPlane.2 (ideleNorm_pos _))).mul (hφc.comp ((continuous_mul_right _).mul continuous_const))) g
    rw [hlin]
    have hterm : ∀ j, whittakerCoefficient ℚ (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ψ⁻¹ (fun z : AdelicGL2 (𝓞 ℚ) ℚ => ((detNorm (z * placeEmbed ℚ p (x j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * φv par (z * placeEmbed ℚ p (x j) * h₂)) 1 g =
        (((ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det (x j) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ))) *
          (WA par (ratArchGL2 g * ratArchGL2 h₂) *
            ∑ β ∈ s, w P β (localAt ℚ p g * x j) * W'' β ((RSCarrier.finFactor (g * h₂) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)) := by
      intro j
      rw [GamJP.W_detNorm_translate, hψQ, hWAf par, hsplitF, hNx, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (hNpos g).le (hmpos (x j)).le, hRmul, hRmul, Ws23SwapStep.ratArchGL2_placeEmbed, mul_one,
        map_mul (localAt ℚ p), map_mul (localAt ℚ p), Ws23Fam5Holes.localAt_placeEmbed, hh₂, mul_one]
      simp only [hWfin']
    rw [Finset.sum_congr rfl fun j _ => by rw [hterm j]]
    have hx0 : ∀ j, (((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det (x j) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ)) ≠ 0 := fun j => by exact_mod_cast (hmpos (x j)).ne'
    have hre : ∀ j, (c j * ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det (x j) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ ((1 / 2 : ℂ))) *
        ((((ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det (x j) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ))) *
          (WA par (ratArchGL2 g * ratArchGL2 h₂) *
            ∑ β ∈ s, w P β (localAt ℚ p g * x j) * W'' β ((RSCarrier.finFactor (g * h₂) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ))) =
        ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * WA par (ratArchGL2 g * ratArchGL2 h₂) *
          ∑ β ∈ s, (c j * w P β (localAt ℚ p g * x j)) * W'' β ((RSCarrier.finFactor (g * h₂) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) := by
      intro j
      have h1 : ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det (x j) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ ((1 / 2 : ℂ)) * ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det (x j) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) = 1 := by
        rw [← Complex.cpow_add _ _ (hx0 j), add_neg_cancel, Complex.cpow_zero]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun β _ => ?_
      linear_combination (((ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * WA par (ratArchGL2 g * ratArchGL2 h₂) *
        (c j * w P β (localAt ℚ p g * x j) * W'' β ((RSCarrier.finFactor (g * h₂) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ))) * h1
    rw [Finset.sum_congr rfl fun j _ => hre j, ← Finset.mul_sum, Finset.sum_comm]
    have hin : ∀ β ∈ s, ∑ j, (c j * w P β (localAt ℚ p g * x j)) * W'' β ((RSCarrier.finFactor (g * h₂) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) =
        if β = β₀ then w P β₀ (localAt ℚ p g) * W'' β₀ ((RSCarrier.finFactor (g * h₂) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) else 0 := by
      intro β hβ
      rw [← Finset.sum_mul, hpur β hβ]
      split_ifs with hb
      · subst hb; rfl
      · rw [zero_mul]
    rw [Finset.sum_congr rfl hin, Finset.sum_ite_eq' s β₀, if_pos hβ₀]

    have hsc : ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) =
        ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (ratArchGL2 g))) : ℂ)) ^ (-(1 / 2 : ℂ)) *
          (((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det (localAt ℚ p g) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) *
            ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (((RSCarrier.finFactor g : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ))) /
              (LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det (localAt ℚ p g) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ))) := by
      have hNg : ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) =
          ideleNorm ℚ (Matrix.GeneralLinearGroup.det (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (ratArchGL2 g))) *
            ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det (localAt ℚ p g) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) *
              (ideleNorm ℚ (Matrix.GeneralLinearGroup.det (((RSCarrier.finFactor g : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ))) /
                (LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det (localAt ℚ p g) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))) := by
        rw [← mul_div_assoc, mul_div_cancel_left₀ _ (hmpos _).ne']
        conv_lhs => rw [hgsplit g]
        rw [map_mul, ideleNorm_mul]
      rw [hNg, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (hNpos _).le (mul_nonneg (hmpos _).le (div_nonneg (hNpos _).le (hmpos _).le)),
        Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (hmpos _).le (div_nonneg (hNpos _).le (hmpos _).le)]
    beta_reduce
    rw [Ws23W2.localAt_finFactor, ← hfg g, hsc]
    ring

  refine ⟨nP, fun j => c j * ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det (x j) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ ((1 / 2 : ℂ)), x,
    fun M => ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) M)) : ℂ)) ^ (-(1 / 2 : ℂ)) *
      WA par (M * ratArchGL2 h₂),
    fun gf => ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (gf : AdelicGL2 (𝓞 ℚ) ℚ)) / (LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det (localAt ℚ p (gf : AdelicGL2 (𝓞 ℚ) ℚ)) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * W'' β₀ ((RSCarrier.finFactor ((gf : AdelicGL2 (𝓞 ℚ) ℚ) * h₂) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ),
    fun y => ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det y : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * w P β₀ y,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro x' g
    have h1 : ((RSCarrier.finFactor (g * placeEmbed ℚ p x') : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) =
        ((RSCarrier.finFactor g : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) * placeEmbed ℚ p x' := by
      rw [Ws23SwapStep.finFactor_mul_placeEmbed, Subgroup.coe_mul, Ws23SwapStep.coe_finFactor_placeEmbed]
    have hY : ∀ Y : AdelicGL2 (𝓞 ℚ) ℚ,
        ideleNorm ℚ (Matrix.GeneralLinearGroup.det (Y * placeEmbed ℚ p x')) / (LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det (localAt ℚ p (Y * placeEmbed ℚ p x')) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) =
          ideleNorm ℚ (Matrix.GeneralLinearGroup.det Y) / (LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det (localAt ℚ p Y) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) := by
      intro Y
      have hN : ideleNorm ℚ (Matrix.GeneralLinearGroup.det (Y * placeEmbed ℚ p x')) =
          ideleNorm ℚ (Matrix.GeneralLinearGroup.det Y) * (LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det x' : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) := by
        have := hNx Y x'; unfold detNorm at this; exact this
      rw [hN, map_mul (localAt ℚ p), Ws23Fam5Holes.localAt_placeEmbed, map_mul Matrix.GeneralLinearGroup.det, Units.val_mul,
        LanglandsTunnell.TateLocal.modulus_mul, NNReal.coe_mul, mul_div_mul_right _ _ (hmpos x').ne']
    simp only [h1]
    rw [hY, hWfin']
  ·
    refine Measurable.mul ?_ ?_
    · refine (Continuous.measurable ?_)
      refine Continuous.cpow ?_ continuous_const fun gf => Complex.ofReal_mem_slitPlane.2 (div_pos (hNpos _) (hmpos _))
      exact Complex.continuous_ofReal.comp
        (((continuous_ideleNorm_det ℚ).comp continuous_subtype_val).div
          ((Ws23Fam5Holes.continuous_modulus_det_real p).comp ((continuous_localAt ℚ p).comp continuous_subtype_val))
          fun gf => (hmpos _).ne')
    · have hfun : (fun gf : finiteAdelicGL2Subgroup ℚ =>
          W'' β₀ ((RSCarrier.finFactor ((gf : AdelicGL2 (𝓞 ℚ) ℚ) * h₂) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)) =
          (fun t : finiteAdelicGL2Subgroup ℚ => W'' β₀ (t : AdelicGL2 (𝓞 ℚ) ℚ)) ∘ fun gf => gf * RSCarrier.finFactor h₂ := by
        funext gf
        simp only [Function.comp_apply, Ws23Fam5Holes.finFactor_coe_mul]
      rw [hfun]
      exact (hW''m β₀).comp (continuous_mul_right _).measurable
  ·
    intro t ht g
    set sP : AdeleRing (𝓞 ℚ) ℚ := NumberField.StandardAddChar.adeleSingleAt ℚ p (t.2 p) with hsP
    have hsP1 : sP.1 = 0 := rfl
    have hsPp : sP.2 p = t.2 p := NumberField.StandardAddChar.finAdeleSingleAt_apply_self ℚ p _
    have hsPq : ∀ q : HeightOneSpectrum (𝓞 ℚ), q ≠ p → sP.2 q = 0 := fun q hq =>
      NumberField.StandardAddChar.finAdeleSingleAt_apply_of_ne ℚ p _ hq
    have ht' : (t - sP).1 = 0 := by change t.1 - sP.1 = 0; rw [ht, hsP1, sub_zero]
    have hu0 : ∀ {A : Type} [CommRing A], (unipotentGL2 (0 : A) : GL (Fin 2) A) = 1 := by
      intro A _
      exact Units.ext (by rw [unipotentGL2_coe, Units.val_one]; ext i j; fin_cases i <;> fin_cases j <;> rfl)
    have ht'p : localAt ℚ p (unipotentGL2 (t - sP)) = 1 := by
      rw [Ws23Fam5Holes.localAt_unipotentGL2]
      change unipotentGL2 (t.2 p - sP.2 p) = 1
      rw [hsPp, sub_self, hu0]
    have hnsP : (unipotentGL2 sP : AdelicGL2 (𝓞 ℚ) ℚ) = placeEmbed ℚ p (unipotent (t.2 p)) := by
      refine Ws23Fam5Holes.ext2 ?_ fun q => ?_
      · rw [Ws23Fam5Holes.glArch_placeEmbed, show sP = (((0 : InfiniteAdeleRing ℚ), sP.2) : AdeleRing (𝓞 ℚ) ℚ) from Prod.ext hsP1 rfl,
          Ws23Fam5Holes.glArch_unipotentGL2_fin]
      · rw [Ws23Fam5Holes.localAt_unipotentGL2]
        by_cases hq : q = p
        · subst hq
          rw [Ws23Fam5Holes.localAt_placeEmbed, hsPp]
          exact Units.ext rfl
        · rw [Ws23Fam5Holes.localAt_placeEmbed_of_ne p _ hq, hsPq q hq, hu0]
    have hmem : (unipotentGL2 t : AdelicGL2 (𝓞 ℚ) ℚ) ∈ finiteAdelicGL2Subgroup ℚ := by
      rw [show t = (((0 : InfiniteAdeleRing ℚ), t.2) : AdeleRing (𝓞 ℚ) ℚ) from Prod.ext ht rfl]
      exact Ws23Fam5Holes.unipotentGL2_fin_mem t.2
    have hfin : ∀ Y : AdelicGL2 (𝓞 ℚ) ℚ, ((RSCarrier.finFactor (unipotentGL2 t * Y) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) =
        unipotentGL2 t * ((RSCarrier.finFactor Y : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) := fun Y =>
      congrArg Subtype.val (Ws23Fam5Holes.finFactor_coe_mul ⟨unipotentGL2 t, hmem⟩ Y)
    have hS1 : ∀ Y : AdelicGL2 (𝓞 ℚ) ℚ, ideleNorm ℚ (Matrix.GeneralLinearGroup.det (unipotentGL2 t * Y)) =
        ideleNorm ℚ (Matrix.GeneralLinearGroup.det Y) := fun Y => by rw [map_mul, GamJP.det_unipotentGL2, one_mul]
    have hS2 : ∀ Y : AdelicGL2 (𝓞 ℚ) ℚ, (LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det (localAt ℚ p (unipotentGL2 t * Y)) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) = (LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det (localAt ℚ p Y) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) := by
      intro Y
      rw [map_mul, Ws23Fam5Holes.localAt_unipotentGL2, map_mul,
        show Matrix.GeneralLinearGroup.det (unipotentGL2 (t.2 p) : GL (Fin 2) (p.adicCompletion ℚ)) = 1 from
          Units.ext (by rw [Matrix.GeneralLinearGroup.val_det_apply, Ws23Fam5Holes.det_unipotentGL2_val, Units.val_one]), one_mul]

    have hW3' : ∀ (β : Fin m) (Z : AdelicGL2 (𝓞 ℚ) ℚ), W'' β (unipotentGL2 (t - sP) * Z) =
        NumberField.StandardAddChar.psiQ (t - sP) * W'' β Z := by
      intro β Z
      rw [hW'', hW'', Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [hW3 α (t - sP) ht' (fun q => by
        obtain ⟨q, hq⟩ := q
        have hq' : q = p := Finset.mem_singleton.1 hq
        subst hq'
        exact ht'p) Z]
      ring
    have hkey : ∀ Z : AdelicGL2 (𝓞 ℚ) ℚ, W'' β₀ (unipotentGL2 t * Z) =
        (ψ⁻¹ t * LanglandsTunnell.CubicInduction.psiLoc ψ p (t.2 p)) * W'' β₀ Z := by
      intro Z
      rw [show (unipotentGL2 t : AdelicGL2 (𝓞 ℚ) ℚ) = unipotentGL2 (t - sP) * unipotentGL2 sP from by
        rw [← unipotentGL2_add, sub_add_cancel], mul_assoc, hW3', hnsP,
        Ws23Fam5Holes.mul_left_eq_of_placeEmbed_invariant (SQ := ({p} : Finset (HeightOneSpectrum (𝓞 ℚ)))) (W'' β₀)
          (fun q x'' g'' => by
            obtain ⟨q, hq⟩ := q
            have hq' : q = p := Finset.mem_singleton.1 hq
            subst hq'
            exact hW''1 β₀ x'' g'')
          (Ws23Fam5Holes.isSupportedOn_placeEmbed (SQ := ({p} : Finset (HeightOneSpectrum (𝓞 ℚ)))) (Finset.mem_singleton_self p) _)]
      congr 1
      rw [← hψQ, AddChar.inv_apply, neg_sub, sub_eq_add_neg, AddChar.map_add_eq_mul, ← AddChar.inv_apply ψ t, mul_comm]
      rfl
    simp only [hfin, hS1, hS2]
    rw [mul_assoc (unipotentGL2 t : AdelicGL2 (𝓞 ℚ) ℚ), hfin, hkey]
    ring
  ·
    intro t y
    beta_reduce
    rw [map_mul Matrix.GeneralLinearGroup.det (unipotent t) y, hdetn, one_mul, hw2 P β₀ t y]
    ring
  ·
    intro h0
    have := congrFun h0 y₀
    simp only [Pi.zero_apply, mul_eq_zero] at this
    rcases this with h1 | h1
    · exact hcpow0 (hmpos y₀) _ h1
    · exact hy₀ h1
  ·
    exact ⟨w P β₀, hw0 P β₀, fun y => rfl⟩
  ·
    exact hfact
  ·
    set gf : finiteAdelicGL2Subgroup ℚ := g₁ * (RSCarrier.finFactor h₂)⁻¹ with hgf
    set z : GL (Fin 2) (p.adicCompletion ℚ) := (localAt ℚ p (gf : AdelicGL2 (𝓞 ℚ) ℚ))⁻¹ * y₀ with hz
    set M₁ : GL (Fin 2) ℝ := M₀ * (ratArchGL2 h₂)⁻¹ with hM₁
    refine ⟨archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) M₁ * (gf : AdelicGL2 (𝓞 ℚ) ℚ) * placeEmbed ℚ p z, ?_⟩
    beta_reduce
    rw [hfact]
    beta_reduce
    have hgp : localAt ℚ p (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) M₁ * (gf : AdelicGL2 (𝓞 ℚ) ℚ) * placeEmbed ℚ p z) = y₀ := by
      rw [map_mul, map_mul, hlocR, one_mul, Ws23Fam5Holes.localAt_placeEmbed, hz, mul_inv_cancel_left]
    have hga : ratArchGL2 (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) M₁ * (gf : AdelicGL2 (𝓞 ℚ) ℚ) * placeEmbed ℚ p z) = M₁ := by
      rw [hRmul, hRmul, Ws23Fam5.ratArchGL2_archRealGLAt, Ws23SwapStep.ratArchGL2_coe, Ws23SwapStep.ratArchGL2_placeEmbed,
        mul_one, mul_one]
    have hgfF : RSCarrier.finFactor (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) M₁ * (gf : AdelicGL2 (𝓞 ℚ) ℚ) * placeEmbed ℚ p z) =
        gf * RSCarrier.finFactor (placeEmbed ℚ p z) := by
      rw [mul_assoc, hfFarch, Ws23Fam5Holes.finFactor_coe_mul]
    have hW1 : W'' β₀ ((RSCarrier.finFactor (((gf * RSCarrier.finFactor (placeEmbed ℚ p z) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) * h₂) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) =
        W'' β₀ (g₁ : AdelicGL2 (𝓞 ℚ) ℚ) := by
      rw [Subgroup.coe_mul, Ws23SwapStep.coe_finFactor_placeEmbed, hWfin', Ws23Fam5Holes.finFactor_coe_mul, hgf,
        inv_mul_cancel_right]
    rw [hgp, hga, hgfF, hW1]
    beta_reduce
    refine mul_ne_zero (mul_ne_zero (hcpow0 (hmpos y₀) _) hy₀) (mul_ne_zero (mul_ne_zero (hcpow0 (hNpos _) _) ?_)
      (mul_ne_zero (hcpow0 (div_pos (hNpos _) (hmpos _)) _) hg₁))
    rw [hM₁, inv_mul_cancel_right]
    exact hM₀

end S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch (solution)
