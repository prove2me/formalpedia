-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/ed785b8b-9776-510d-9ad5-e49170c73ff0

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
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_placeEmbed
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_rsFinIntegral_eq_const_mul_rsLocalIntegral_of_factorsAt
import Definitions.Def_LanglandsTunnell_CubicInduction_FnTwist3
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_pos_forall_rsLocalIntegral_indicator_unipotent_mul_localLevelOne_eq
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_pos_integral_indicator_forall_localAt_unipotent_mul_localLevelOne_withDensity_eq
import Theorems.Thm_LanglandsTunnell_RankinSelberg_mul_eq_mul_one_and_ideleNorm_det_eq_finprod_of_mem_cut_of_blind
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_sFinite_forall_lintegral_withDensity_density_eq_lintegral_lintegral_mul_finFactor_placeEmbed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.LanglandsTunnell LanglandsTunnell.Converse"
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
p2m_open "LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction MeasureTheory"
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

scoped instance vaddInvariantMeasure_principalSubgroup_fam5 :
    VAddInvariantMeasure (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) 𝔸 μA :=
  ⟨fun k s _ => measure_preimage_add _ (k : 𝔸) s⟩

end WhittakerUnipotentLaw

private theorem _root_.Ws23Fam5.finFactor_coe (g : finiteAdelicGL2Subgroup ℚ) : RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) = g := by
  apply Subtype.ext
  have h1 : ratArchGL2 (g : AdelicGL2 (𝓞 ℚ) ℚ) = 1 := by
    unfold LanglandsTunnell.ratArchGL2
    rw [(mem_finiteAdelicGL2Subgroup_iff ℚ _).1 g.2, map_one, map_one]
  simp only [RSCarrier.finFactor, h1, map_one, inv_one, one_mul]

p2m_export "Ws23Fam5" "finFactor_coe"
end Ws23Fam5
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

noncomputable section

namespace Ws23Fam5Holes

section Local

variable (p : HeightOneSpectrum (𝓞 ℚ))

theorem isClosed_setOf_isLocalLevelOne (N : Ideal (𝓞 ℚ)) :
    IsClosed {m : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) | AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p N m} := by
  have h : {m : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) | AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p N m} =
      (⋂ i, ⋂ j, (fun m => m i j) ⁻¹' (p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ))) ∩
        ((fun m => m 1 0) ⁻¹' {y | Valued.v y ≤ idealBound (𝓞 ℚ) N p} ∩
          (fun m => m 1 1 - 1) ⁻¹' {y | Valued.v y ≤ idealBound (𝓞 ℚ) N p}) := by
    ext m
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    exact ⟨fun hm => ⟨hm.integral, hm.lowerLeft, hm.lowerRight⟩, fun hm => ⟨hm.1, hm.2.1, hm.2.2⟩⟩
  rw [h]
  exact (isClosed_iInter fun i => isClosed_iInter fun j =>
      (isClosed_adicCompletionIntegers p).preimage (continuous_id.matrix_elem i j)).inter
    (((isClosed_setOf_valued_le_idealBound p N).preimage (continuous_id.matrix_elem 1 0)).inter
      ((isClosed_setOf_valued_le_idealBound p N).preimage
        ((continuous_id.matrix_elem 1 1).sub continuous_const)))

theorem coe_localLevelOne_eq (N : Ideal (𝓞 ℚ)) :
    (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N : Set (GL (Fin 2) (p.adicCompletion ℚ))) =
      Units.val ⁻¹' {m | AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p N m} ∩
        (fun u : GL (Fin 2) (p.adicCompletion ℚ) => ((u⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix _ _ _)) ⁻¹'
          {m | AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p N m} := by
  ext k
  rw [SetLike.mem_coe, AdelicDock.mem_localLevelOne_iff]
  rfl

theorem isClosed_localLevelOne (N : Ideal (𝓞 ℚ)) :
    IsClosed (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N : Set (GL (Fin 2) (p.adicCompletion ℚ))) := by
  rw [coe_localLevelOne_eq]
  exact ((isClosed_setOf_isLocalLevelOne p N).preimage Units.continuous_val).inter
    ((isClosed_setOf_isLocalLevelOne p N).preimage Units.continuous_coe_inv)

theorem localLevelOne_subset_localIntegralSet (N : Ideal (𝓞 ℚ)) :
    (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N : Set (GL (Fin 2) (p.adicCompletion ℚ))) ⊆ localIntegralSet ℚ p := by
  intro k hk
  rw [SetLike.mem_coe, AdelicDock.mem_localLevelOne_iff] at hk
  exact ⟨hk.1.integral, hk.2.integral⟩

theorem isCompact_localLevelOne (N : Ideal (𝓞 ℚ)) :
    IsCompact (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N : Set (GL (Fin 2) (p.adicCompletion ℚ))) :=
  (isCompact_localIntegralSet ℚ p).of_isClosed_subset (isClosed_localLevelOne p N)
    (localLevelOne_subset_localIntegralSet p N)

end Local
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

section Ugrp

variable (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))) (N : Ideal (𝓞 ℚ))

theorem localAt_apply (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ) (i j : Fin 2) :
    ((localAt ℚ p g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i j =
      (((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 p := by
  rw [show localAt ℚ p g = finComponent (𝓞 ℚ) ℚ p (glFin (𝓞 ℚ) ℚ g) from rfl, finComponent_apply, glFin_apply]

theorem det_mem_of_forall_mem {p : HeightOneSpectrum (𝓞 ℚ)} (m : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))
    (h : ∀ i j, m i j ∈ p.adicCompletionIntegers ℚ) : m.det ∈ p.adicCompletionIntegers ℚ := by
  rw [Matrix.det_fin_two]
  exact sub_mem (mul_mem (h 0 0) (h 1 1)) (mul_mem (h 0 1) (h 1 0))

end Ugrp
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

end Ws23Fam5Holes
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

noncomputable section

namespace Ws23Fam5Holes

open IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel NumberField.TateGlobal

section H45

variable (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))

end H45
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

end Ws23Fam5Holes
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

namespace Ws23Fam5Holes

end Ws23Fam5Holes
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

section PencBatch3
open scoped Matrix

namespace Ws23Fam5Holes

section GL3

variable {A : Type*} [CommRing A]

variable {R : Type*} [CommRing R]

end GL3
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

end Ws23Fam5Holes
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

end PencBatch3
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

namespace Ws23Fam5Holes

p2m_open "IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.LanglandsTunnell LanglandsTunnell.CubicInduction NumberField.AdelicLevel"

def cellSet (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))) : Set (finiteAdelicGL2Subgroup ℚ) :=
  {g : finiteAdelicGL2Subgroup ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
    ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := p.adicCompletion ℚ)).range,
      ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
        localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}

theorem localAt_unipotentGL2 (b : AdeleRing (𝓞 ℚ) ℚ) (p : HeightOneSpectrum (𝓞 ℚ)) :
    localAt ℚ p (unipotentGL2 b : AdelicGL2 (𝓞 ℚ) ℚ) = unipotentGL2 (b.2 p) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [localAt_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> rfl

theorem unipotentGL2Hom_apply_zero_one (a : Multiplicative (AdeleRing (𝓞 ℚ) ℚ)) :
    ((unipotentGL2Hom a : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 0 1 = Multiplicative.toAdd a := by
  change ((unipotentGL2 (Multiplicative.toAdd a) : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 0 1 = _
  rw [unipotentGL2_coe]
  rfl

theorem exists_eq_unipotentGL2_of_mem_finUnipotent (n : RSCarrier.finUnipotent) :
    ∃ b : FiniteAdeleRing (𝓞 ℚ) ℚ,
      ((n : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) =
        unipotentGL2 (((0 : InfiniteAdeleRing ℚ), b) : AdeleRing (𝓞 ℚ) ℚ) := by
  obtain ⟨a, ha⟩ := Subgroup.mem_subgroupOf.1 n.2
  have harch : glArch (𝓞 ℚ) ℚ ((n : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) = 1 :=
    (mem_finiteAdelicGL2Subgroup_iff ℚ _).1 (n : finiteAdelicGL2Subgroup ℚ).2
  have h01 : (Multiplicative.toAdd a).1 = 0 := by
    have h := glArch_apply (𝓞 ℚ) ℚ ((n : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) 0 1
    rw [harch, Units.val_one, Matrix.one_apply_ne (by decide)] at h
    change (0 : InfiniteAdeleRing ℚ) =
      ((((n : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 0 1).1 at h
    rw [← ha, unipotentGL2Hom_apply_zero_one] at h
    exact h.symm
  refine ⟨(Multiplicative.toAdd a).2, ?_⟩
  rw [← ha]
  change (unipotentGL2 (Multiplicative.toAdd a) : AdelicGL2 (𝓞 ℚ) ℚ) = _
  congr 1
  exact Prod.ext h01 rfl

theorem localAt_coe_finUnipotent (n : RSCarrier.finUnipotent) (p : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ x : p.adicCompletion ℚ,
      localAt ℚ p ((n : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) = unipotentGL2 x := by
  obtain ⟨b, hb⟩ := exists_eq_unipotentGL2_of_mem_finUnipotent n
  refine ⟨b p, ?_⟩
  rw [hb]
  exact localAt_unipotentGL2 _ p

theorem unipotentGL2_mem_range (R : Type*) [CommRing R] (x : R) :
    (unipotentGL2 x : GL (Fin 2) R) ∈ (AutomorphicForm.unipotentGL2Hom (R := R)).range :=
  ⟨Multiplicative.ofAdd x, rfl⟩

theorem unipotent_mul_mem_cellSet_iff (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))) (n : RSCarrier.finUnipotent)
    (g : finiteAdelicGL2Subgroup ℚ) :
    (n : finiteAdelicGL2Subgroup ℚ) * g ∈ cellSet SQ ↔ g ∈ cellSet SQ := by
  constructor
  · intro h p hp
    obtain ⟨m, hm, k, hk, hmk⟩ := h p hp
    obtain ⟨x, hx⟩ := localAt_coe_finUnipotent n p
    rw [Subgroup.coe_mul, map_mul, hx] at hmk
    refine ⟨(unipotentGL2 x)⁻¹ * m, mul_mem (inv_mem (unipotentGL2_mem_range _ x)) hm, k, hk, ?_⟩
    rw [mul_assoc, ← hmk, inv_mul_cancel_left]
  · intro h p hp
    obtain ⟨m, hm, k, hk, hmk⟩ := h p hp
    obtain ⟨x, hx⟩ := localAt_coe_finUnipotent n p
    refine ⟨unipotentGL2 x * m, mul_mem (unipotentGL2_mem_range _ x) hm, k, hk, ?_⟩
    rw [Subgroup.coe_mul, map_mul, hx, hmk, mul_assoc]

end Ws23Fam5Holes
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

section PencN12
open scoped Matrix

namespace Ws23Fam5Holes

open IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell.CubicInduction UnramifiedWhittaker

section OffPlace

variable (p : HeightOneSpectrum (𝓞 ℚ))

private theorem _root_.Ws23Fam5Holes.localAt_placeEmbed_of_ne (x : GL (Fin 2) (p.adicCompletion ℚ)) {q : HeightOneSpectrum (𝓞 ℚ)} (hq : q ≠ p) :
    localAt ℚ q (placeEmbed ℚ p x) = 1 := by
  change finComponent (𝓞 ℚ) ℚ q (glFin (𝓞 ℚ) ℚ (AdelicDock.finEmbed (𝓞 ℚ) ℚ (AdelicDock.localEmbed (𝓞 ℚ) ℚ p x))) = 1
  rw [AdelicDock.glFin_finEmbed, AdelicDock.finComponent_localEmbed_of_ne (𝓞 ℚ) ℚ p x hq]

p2m_export "Ws23Fam5Holes" "localAt_placeEmbed_of_ne"

theorem ideleNorm_det_placeEmbed_mul (x : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    ideleNorm ℚ (Matrix.GeneralLinearGroup.det (placeEmbed ℚ p x * g)) =
      (LanglandsTunnell.TateLocal.modulus
          ((Matrix.GeneralLinearGroup.det x : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) *
        ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) := by
  rw [map_mul, ideleNorm_mul, NumberField.TateGlobal.ideleNorm_det_placeEmbed]

end OffPlace
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

section DualLaw

variable {A : Type*} [CommRing A] {R : Type*} [CommRing R]

end DualLaw
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

end Ws23Fam5Holes
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

end PencN12
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

section PencL13
open scoped Matrix Classical

namespace Ws23Fam5Holes

open IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell.CubicInduction UnramifiedWhittaker

section Ext2

end Ext2
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

section L1

end L1
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

section L3

end L3
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

end Ws23Fam5Holes
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

end PencL13
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

section PencL2
open scoped Matrix Classical

namespace Ws23Fam5Holes

open IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell.CubicInduction UnramifiedWhittaker

section L2

variable (T : Finset (HeightOneSpectrum (𝓞 ℚ)))

end L2
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

end Ws23Fam5Holes
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

end PencL2
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

section PencDE
open scoped Matrix Classical

namespace Ws23Fam5Holes

p2m_open "IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.LanglandsTunnell LanglandsTunnell.CubicInduction UnramifiedWhittaker"

end Ws23Fam5Holes
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

end PencDE
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

section Ws23MiniPlaceKit

p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.LanglandsTunnell.RankinSelberg"

noncomputable section

namespace Ws23HeckeLocalDualPort

open Matrix NumberField.AdelicVolume UnramifiedWhittaker

local notation "G2" => AdelicGL2 (𝓞 ℚ) ℚ
local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ

section Place

variable (p : HeightOneSpectrum (𝓞 ℚ))

end Place
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

end Ws23HeckeLocalDualPort
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

end Ws23MiniPlaceKit
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

section prover2_prefactor

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.TateGlobal
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction LanglandsTunnell.Converse"
open UnramifiedWhittaker AutomorphicForm

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.modulus ratArchGL2 TateLocal.modulus_adicCompletion_eq_nnnorm RankinSelberg.exists_forall_rsFinIntegral_eq_const_mul_rsLocalIntegral_of_factorsAt RankinSelberg.exists_pos_forall_rsLocalIntegral_indicator_unipotent_mul_localLevelOne_eq RankinSelberg.exists_pos_integral_indicator_forall_localAt_unipotent_mul_localLevelOne_withDensity_eq RankinSelberg.mul_eq_mul_one_and_ideleNorm_det_eq_finprod_of_mem_cut_of_blind RankinSelberg.exists_sFinite_forall_lintegral_withDensity_density_eq_lintegral_lintegral_mul_finFactor_placeEmbed"
namespace RankinSelberg
p2m_export "LanglandsTunnell.RankinSelberg" "exists_forall_rsFinIntegral_eq_const_mul_rsLocalIntegral_of_factorsAt exists_pos_forall_rsLocalIntegral_indicator_unipotent_mul_localLevelOne_eq exists_pos_integral_indicator_forall_localAt_unipotent_mul_localLevelOne_withDensity_eq mul_eq_mul_one_and_ideleNorm_det_eq_finprod_of_mem_cut_of_blind exists_sFinite_forall_lintegral_withDensity_density_eq_lintegral_lintegral_mul_finFactor_placeEmbed"
namespace EntirePairAssembly
namespace Prefactor
p2m_open "LanglandsTunnell.RankinSelberg LanglandsTunnell"

section NormAlgebra
variable {G : Type*} [Group G] (ν : G → ℝ) (hmul : ∀ a b, ν (a * b) = ν a * ν b) (hone : ν 1 = 1) (hpos : ∀ a, 0 < ν a)
end NormAlgebra
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

variable (v : HeightOneSpectrum (𝓞 ℚ))

section Fibre
variable (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]

end Fibre
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

end LanglandsTunnell.RankinSelberg.EntirePairAssembly.Prefactor
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

end prover2_prefactor
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

section prover2_hlev

open IsDedekindDomain NumberField NumberField.StandardAddChar LanglandsTunnell.TateLocal

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.modulus ratArchGL2 TateLocal.modulus_adicCompletion_eq_nnnorm RankinSelberg.exists_forall_rsFinIntegral_eq_const_mul_rsLocalIntegral_of_factorsAt RankinSelberg.exists_pos_forall_rsLocalIntegral_indicator_unipotent_mul_localLevelOne_eq RankinSelberg.exists_pos_integral_indicator_forall_localAt_unipotent_mul_localLevelOne_withDensity_eq RankinSelberg.mul_eq_mul_one_and_ideleNorm_det_eq_finprod_of_mem_cut_of_blind RankinSelberg.exists_sFinite_forall_lintegral_withDensity_density_eq_lintegral_lintegral_mul_finFactor_placeEmbed"
namespace RankinSelberg
p2m_export "LanglandsTunnell.RankinSelberg" "exists_forall_rsFinIntegral_eq_const_mul_rsLocalIntegral_of_factorsAt exists_pos_forall_rsLocalIntegral_indicator_unipotent_mul_localLevelOne_eq exists_pos_integral_indicator_forall_localAt_unipotent_mul_localLevelOne_withDensity_eq mul_eq_mul_one_and_ideleNorm_det_eq_finprod_of_mem_cut_of_blind exists_sFinite_forall_lintegral_withDensity_density_eq_lintegral_lintegral_mul_finFactor_placeEmbed"
namespace EntirePairAssembly
namespace Prefactor
p2m_open "LanglandsTunnell.RankinSelberg LanglandsTunnell"

end LanglandsTunnell.RankinSelberg.EntirePairAssembly.Prefactor
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

end prover2_hlev
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

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

end Ws23Tw
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

namespace Ws23Fam5

end Ws23Fam5
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

namespace Ws23Fam5Holes

p2m_open "IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.LanglandsTunnell LanglandsTunnell.CubicInduction UnramifiedWhittaker"

end Ws23Fam5Holes
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

namespace Ws23Fam5Holes

p2m_open "IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.LanglandsTunnell LanglandsTunnell.CubicInduction UnramifiedWhittaker"

section SupportedOn

variable (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))

def IsSupportedOn (h : AdelicGL2 (𝓞 ℚ) ℚ) : Prop :=
  glArch (𝓞 ℚ) ℚ h = 1 ∧ ∀ q : HeightOneSpectrum (𝓞 ℚ), q ∉ SQ → localAt ℚ q h = 1

theorem IsSupportedOn.mul {h h' : AdelicGL2 (𝓞 ℚ) ℚ} (hh : IsSupportedOn SQ h) (hh' : IsSupportedOn SQ h') :
    IsSupportedOn SQ (h * h') :=
  ⟨by rw [map_mul, hh.1, hh'.1, mul_one], fun q hq => by rw [map_mul, hh.2 q hq, hh'.2 q hq, mul_one]⟩

variable {SQ}

variable (SQ)

end SupportedOn
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

section Weyl

end Weyl
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

end Ws23Fam5Holes
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

namespace Ws23Fam5Holes

p2m_open "IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.LanglandsTunnell LanglandsTunnell.CubicInduction UnramifiedWhittaker"

section Centrality

end Centrality
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

section FinFactor

end FinFactor
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

section UnitNorms

theorem det_unipotentGL2_val {A : Type*} [CommRing A] (x : A) :
    Matrix.det ((unipotentGL2 x : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = 1 := by
  rw [unipotentGL2_coe, Matrix.det_fin_two_of]; ring

end UnitNorms
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

section Levels

end Levels
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

end Ws23Fam5Holes
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

namespace Ws23Fam5Holes

p2m_open "IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.LanglandsTunnell LanglandsTunnell.CubicInduction UnramifiedWhittaker"

section FlipOff

variable (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))

end FlipOff
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

section MixedGL2

variable (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))) (w₀ : GL (Fin 2) ℚ) (H : AdelicGL2 (𝓞 ℚ) ℚ)

variable {SQ w₀ H}

end MixedGL2
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

end Ws23Fam5Holes
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

namespace Ws23W2

p2m_open "IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.LanglandsTunnell LanglandsTunnell.CubicInduction UnramifiedWhittaker P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5Holes P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

end Ws23W2
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

namespace Ws23W2

p2m_open "IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.LanglandsTunnell LanglandsTunnell.CubicInduction UnramifiedWhittaker P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5Holes P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

end Ws23W2
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

namespace Ws23W2

p2m_open "IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.LanglandsTunnell LanglandsTunnell.CubicInduction UnramifiedWhittaker P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5Holes P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

end Ws23W2
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

namespace Ws23Fam5Holes

p2m_open "IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.LanglandsTunnell LanglandsTunnell.CubicInduction UnramifiedWhittaker MeasureTheory"

end Ws23Fam5Holes
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

section PenbSwapStep
open LanglandsTunnell.TateLocal UnramifiedWhittaker

noncomputable section

namespace Ws23SwapStep

open LanglandsTunnell.CubicInduction RSCarrier NumberField.AdelicLevel AdelicDock

theorem localAt_placeEmbed_self (p : HeightOneSpectrum (𝓞 ℚ)) (x : GL (Fin 2) (p.adicCompletion ℚ)) :
    localAt ℚ p (placeEmbed ℚ p x) = x := by
  show finComponent (𝓞 ℚ) ℚ p (glFin (𝓞 ℚ) ℚ (finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ p x))) = x
  rw [glFin_finEmbed, finComponent_localEmbed_self]

theorem localAt_placeEmbed_of_ne {p q : HeightOneSpectrum (𝓞 ℚ)} (hq : q ≠ p) (x : GL (Fin 2) (p.adicCompletion ℚ)) :
    localAt ℚ q (placeEmbed ℚ p x) = 1 := by
  show finComponent (𝓞 ℚ) ℚ q (glFin (𝓞 ℚ) ℚ (finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ p x))) = 1
  rw [glFin_finEmbed, finComponent_localEmbed_of_ne (𝓞 ℚ) ℚ p x hq]

theorem placeEmbed_mul_comm (p : HeightOneSpectrum (𝓞 ℚ)) {g : AdelicGL2 (𝓞 ℚ) ℚ} (hg : localAt ℚ p g = 1)
    (x : GL (Fin 2) (p.adicCompletion ℚ)) : placeEmbed ℚ p x * g = g * placeEmbed ℚ p x := by
  have hgp : (finAdeleEval (𝓞 ℚ) ℚ p).mapMatrix ((adeleFin (𝓞 ℚ) ℚ).mapMatrix
      (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))) = 1 := congrArg Units.val hg
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  show finMat (𝓞 ℚ) ℚ (localMat (𝓞 ℚ) ℚ p x) * _ = _ * finMat (𝓞 ℚ) ℚ (localMat (𝓞 ℚ) ℚ p x)
  refine matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 ℚ) ℚ ?_ ?_
  · rw [map_mul, map_mul, mapMatrix_arch_finMat, one_mul, mul_one]
  · rw [map_mul, map_mul, mapMatrix_fin_finMat]
    refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 ℚ) ℚ fun w => ?_
    rw [map_mul, map_mul]
    by_cases hw : w = p
    · subst hw
      rw [hgp, mul_one, one_mul]
    · rw [mapMatrix_localMat_of_ne (𝓞 ℚ) ℚ p _ hw, one_mul, mul_one]

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

theorem coe_finFactor (G : AdelicGL2 (𝓞 ℚ) ℚ) : (finFactor G : AdelicGL2 (𝓞 ℚ) ℚ) =
    (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (LanglandsTunnell.ratArchGL2 G))⁻¹ * G := rfl

theorem finFactor_coe (g : finiteAdelicGL2Subgroup ℚ) : finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) = g := by
  apply Subtype.ext
  rw [coe_finFactor, ratArchGL2_coe, map_one, inv_one, one_mul]

theorem coe_finFactor_placeEmbed (p : HeightOneSpectrum (𝓞 ℚ)) (x : GL (Fin 2) (p.adicCompletion ℚ)) :
    (finFactor (placeEmbed ℚ p x) : AdelicGL2 (𝓞 ℚ) ℚ) = placeEmbed ℚ p x := by
  rw [coe_finFactor, ratArchGL2_placeEmbed, map_one, inv_one, one_mul]

theorem finFactor_mul_placeEmbed (p : HeightOneSpectrum (𝓞 ℚ)) (G : AdelicGL2 (𝓞 ℚ) ℚ) (x : GL (Fin 2) (p.adicCompletion ℚ)) :
    finFactor (G * placeEmbed ℚ p x) = finFactor G * finFactor (placeEmbed ℚ p x) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, coe_finFactor, coe_finFactor, coe_finFactor_placeEmbed, ratArchGL2_mul_placeEmbed, mul_assoc]

theorem ind_mul {α M : Type*} [MulZeroClass M] (s : Set α) {f b : α → M} {a : M} {x : α} (h : f x = a * b x) :
    s.indicator f x = a * s.indicator b x := by
  classical
  by_cases hx : x ∈ s <;> simp [hx, h]

theorem ind_mul_ind {α M : Type*} [MulZeroClass M] (s : Set α) (f g : α → M) (x : α) :
    s.indicator f x * s.indicator g x = s.indicator f x * g x := by
  classical
  by_cases hx : x ∈ s <;> simp [hx]

end Ws23SwapStep
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

namespace Ws23SwapStep

open LanglandsTunnell.CubicInduction RSCarrier NumberField.AdelicLevel AdelicDock

theorem mem_range_unipotentGL2Hom_iff {R : Type*} [CommRing R] (g : GL (Fin 2) R) :
    g ∈ (unipotentGL2Hom (R := R)).range ↔
      (g : Matrix (Fin 2) (Fin 2) R) 0 0 = 1 ∧ (g : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 ∧
        (g : Matrix (Fin 2) (Fin 2) R) 1 1 = 1 := by
  constructor
  · rintro ⟨a, rfl⟩
    simp [unipotentGL2Hom]
  · rintro ⟨h00, h10, h11⟩
    refine ⟨Multiplicative.ofAdd ((g : Matrix (Fin 2) (Fin 2) R) 0 1), ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [unipotentGL2Hom, h00, h10, h11]

theorem isClosed_range_unipotentGL2Hom {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [T1Space R] : IsClosed (((unipotentGL2Hom (R := R)).range : Subgroup (GL (Fin 2) R)) : Set (GL (Fin 2) R)) := by
  have hc : ∀ i j : Fin 2, Continuous fun g : GL (Fin 2) R => (g : Matrix (Fin 2) (Fin 2) R) i j :=
    fun i j => Units.continuous_val.matrix_elem i j
  have : (((unipotentGL2Hom (R := R)).range : Subgroup (GL (Fin 2) R)) : Set (GL (Fin 2) R)) =
      ((fun g : GL (Fin 2) R => (g : Matrix (Fin 2) (Fin 2) R) 0 0) ⁻¹' {1} ∩
        (fun g : GL (Fin 2) R => (g : Matrix (Fin 2) (Fin 2) R) 1 0) ⁻¹' {0}) ∩
        (fun g : GL (Fin 2) R => (g : Matrix (Fin 2) (Fin 2) R) 1 1) ⁻¹' {1} := by
    ext g
    simp only [SetLike.mem_coe, mem_range_unipotentGL2Hom_iff, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff, and_assoc]
  rw [this]
  exact ((isClosed_singleton.preimage (hc 0 0)).inter (isClosed_singleton.preimage (hc 1 0))).inter
    (isClosed_singleton.preimage (hc 1 1))

end Ws23SwapStep
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

namespace Ws23SwapStep

end Ws23SwapStep
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

namespace Ws23SwapStep

end Ws23SwapStep
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

namespace Ws23SwapStep

end Ws23SwapStep
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

namespace Ws23SwapStep

end Ws23SwapStep
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

namespace Ws23SwapStep

end Ws23SwapStep
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

namespace Ws23SwapStep

end Ws23SwapStep
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

namespace Ws23SwapStep

section TranslateSpan
variable {G : Type*} [Group G]

end TranslateSpan
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

end Ws23SwapStep
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

end PenbSwapStep
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

namespace Ws23PencSwap

p2m_open "IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.LanglandsTunnell LanglandsTunnell.CubicInduction UnramifiedWhittaker MeasureTheory"

open scoped Pointwise

theorem modulus_det_eq_one_of_mem_localLevelOne (p : HeightOneSpectrum (𝓞 ℚ)) {N : Ideal (𝓞 ℚ)}
    {u : GL (Fin 2) (p.adicCompletion ℚ)} (hu : u ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N) :
    LanglandsTunnell.TateLocal.modulus
      ((Matrix.GeneralLinearGroup.det u : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) = 1 := by
  have hu' := (AdelicDock.mem_localLevelOne_iff (𝓞 ℚ) ℚ p u).1 hu
  have h1 := Ws23Fam5Holes.det_mem_of_forall_mem _ hu'.1.integral
  have h2 := Ws23Fam5Holes.det_mem_of_forall_mem _ hu'.2.integral
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h1 h2
  have hprod : Matrix.det (u : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
      Matrix.det ((u⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have hv : Valued.v (Matrix.det (u : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) = 1 := by
    refine le_antisymm h1 ?_
    have h := congrArg Valued.v hprod
    rw [map_mul, map_one] at h
    calc (1 : WithZero (Multiplicative ℤ)) = _ * _ := h.symm
      _ ≤ Valued.v (Matrix.det (u : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) * 1 := mul_le_mul_right h2 _
      _ = _ := mul_one _
  rw [Matrix.GeneralLinearGroup.val_det_apply, LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p,
    ← NNReal.coe_inj, coe_nnnorm, NNReal.coe_one, NumberField.FinitePlace.norm_def, hv, map_one, NNReal.coe_one]

theorem continuous_modulus_det (p : HeightOneSpectrum (𝓞 ℚ)) :
    Continuous fun y : GL (Fin 2) (p.adicCompletion ℚ) =>
      (((LanglandsTunnell.TateLocal.modulus
        ((Matrix.GeneralLinearGroup.det y : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : NNReal) : ℝ) : ℂ) := by
  have h : (fun y : GL (Fin 2) (p.adicCompletion ℚ) =>
      (((LanglandsTunnell.TateLocal.modulus
        ((Matrix.GeneralLinearGroup.det y : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : NNReal) : ℝ) : ℂ)) =
      fun y : GL (Fin 2) (p.adicCompletion ℚ) => ((‖Matrix.det (y : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))‖ : ℝ) : ℂ) := by
    funext y
    rw [Matrix.GeneralLinearGroup.val_det_apply, LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p, coe_nnnorm]
  rw [h]
  exact Complex.continuous_ofReal.comp (continuous_norm.comp (Units.continuous_val.matrix_det))

theorem isClosed_range_unipotentGL2Hom (p : HeightOneSpectrum (𝓞 ℚ)) :
    IsClosed (((unipotentGL2Hom (R := p.adicCompletion ℚ)).range : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) :
      Set (GL (Fin 2) (p.adicCompletion ℚ))) := by
  have hc : ∀ i j : Fin 2, Continuous fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
      (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i j :=
    fun i j => Units.continuous_val.matrix_elem i j
  have h : (((unipotentGL2Hom (R := p.adicCompletion ℚ)).range : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) :
      Set (GL (Fin 2) (p.adicCompletion ℚ))) =
      {g : GL (Fin 2) (p.adicCompletion ℚ) | (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 0 = 1 ∧
        (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 = 0 ∧
        (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1 = 1} := by
    ext g
    simp only [SetLike.mem_coe, MonoidHom.mem_range, Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, rfl⟩
      have h : ((unipotentGL2Hom x : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) =
          !![1, x.toAdd; 0, 1] := rfl
      simp [h]
    · rintro ⟨h00, h10, h11⟩
      refine ⟨Multiplicative.ofAdd ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1), Units.ext ?_⟩
      change ((unipotentGL2 ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1) : GL (Fin 2) (p.adicCompletion ℚ)) :
        Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = g
      rw [unipotentGL2_coe]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h00, h10, h11]
  rw [h]
  exact ((isClosed_singleton.preimage (hc 0 0)).inter
    ((isClosed_singleton.preimage (hc 1 0)).inter (isClosed_singleton.preimage (hc 1 1))))

theorem isClosed_bigCell (p : HeightOneSpectrum (𝓞 ℚ)) :
    IsClosed {y : GL (Fin 2) (p.adicCompletion ℚ) | ∃ n ∈ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range,
      ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, y = n * k} := by
  have h : {y : GL (Fin 2) (p.adicCompletion ℚ) | ∃ n ∈ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range,
      ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, y = n * k} =
      (((unipotentGL2Hom (R := p.adicCompletion ℚ)).range : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) :
          Set (GL (Fin 2) (p.adicCompletion ℚ))) *
        (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set (GL (Fin 2) (p.adicCompletion ℚ))) := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_mul, SetLike.mem_coe]
    exact ⟨fun ⟨n, hn, k, hk, h⟩ => ⟨n, hn, k, hk, h.symm⟩, fun ⟨n, hn, k, hk, h⟩ => ⟨n, hn, k, hk, h.symm⟩⟩
  rw [h]
  exact (isClosed_range_unipotentGL2Hom p).mul_right_of_isCompact (Ws23Fam5Holes.isCompact_localLevelOne p ⊤)

theorem isClosed_cellSet (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))) : IsClosed (Ws23Fam5Holes.cellSet SQ) := by
  have h : Ws23Fam5Holes.cellSet SQ = ⋂ (q : HeightOneSpectrum (𝓞 ℚ)) (_ : q ∉ SQ),
      (fun g : finiteAdelicGL2Subgroup ℚ => localAt ℚ q (g : AdelicGL2 (𝓞 ℚ) ℚ)) ⁻¹'
        {y : GL (Fin 2) (q.adicCompletion ℚ) | ∃ n ∈ (unipotentGL2Hom (R := q.adicCompletion ℚ)).range,
          ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ q ⊤, y = n * k} := by
    ext g
    simp only [Ws23Fam5Holes.cellSet, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  rw [h]
  exact isClosed_iInter fun q => isClosed_iInter fun _ =>
    (isClosed_bigCell q).preimage ((continuous_localAt ℚ q).comp continuous_subtype_val)

section Stage

open scoped Classical

end Stage
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

end Ws23PencSwap
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

namespace Ws23Cubic

open IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel LanglandsTunnell.CubicInduction

section Continuity3

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R)

end Continuity3
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

end Ws23Cubic
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

namespace Ws23Cubic

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

variable {v : HeightOneSpectrum (𝓞 ℚ)}

end Ws23Cubic
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

namespace Ws23Cubic

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

end Ws23Cubic
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

namespace Ws23Cubic

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

end Ws23Cubic
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

namespace Ws23Cubic

open IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel LanglandsTunnell.CubicInduction

end Ws23Cubic
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

namespace Ws23Fam5Holes

p2m_open "IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.LanglandsTunnell LanglandsTunnell.CubicInduction UnramifiedWhittaker MeasureTheory"

end Ws23Fam5Holes
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

section W2
open UnramifiedWhittaker LanglandsTunnell.TateLocal NumberField.AdelicLevel NumberField.TateGlobal AdelicDock

namespace Ws23W2

section Twist

variable {G : Type*} [Group G]

end Twist
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

variable (p : HeightOneSpectrum (𝓞 ℚ))

end Ws23W2
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

end W2
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

namespace Ws23Cubic

p2m_open "IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.LanglandsTunnell LanglandsTunnell.CubicInduction UnramifiedWhittaker"

end Ws23Cubic
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

namespace Ws23Cubic

p2m_open "IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.LanglandsTunnell LanglandsTunnell.CubicInduction UnramifiedWhittaker MeasureTheory"

end Ws23Cubic
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

namespace Ws23Nrest

p2m_open "IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.LanglandsTunnell LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.LanglandsTunnell.RankinSelberg UnramifiedWhittaker P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5Holes"

section CutOff

variable (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))

end CutOff
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

end Ws23Nrest
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

section Eta0Off
open NumberField.AdelicLevel NumberField.TateGlobal AdelicDock Ws23Fam5Holes

end Eta0Off
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

namespace Ws23Tw

end Ws23Tw
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

namespace Ws23PencMatch

p2m_open "IsDedekindDomain NumberField LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.LanglandsTunnell.RankinSelberg"

end Ws23PencMatch
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

namespace Ws23Fam5Holes

p2m_open "IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.LanglandsTunnell LanglandsTunnell.CubicInduction UnramifiedWhittaker"

end Ws23Fam5Holes
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

namespace Ws23Regroup

end Ws23Regroup
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

namespace Ws23Away

p2m_open "IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.LanglandsTunnell LanglandsTunnell.CubicInduction LanglandsTunnell.Converse LanglandsTunnell.TateLocal LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.LanglandsTunnell.RankinSelberg UnramifiedWhittaker P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.LanglandsTunnell.RankinSelberg.EntirePairAssembly.Prefactor"

end Ws23Away
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

namespace Ws23Cubic

p2m_open "IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction"

end Ws23Cubic
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

namespace Ws23Fam5

end Ws23Fam5
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

namespace Ws23Cubic

open IsDedekindDomain NumberField MeasureTheory

end Ws23Cubic
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

section W2EtaArch
open NumberField.AdelicVolume NumberField.InfinitePlace.Completion LanglandsTunnell.Converse

namespace Ws23W2

end Ws23W2
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

end W2EtaArch
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

namespace Ws23GaugeMem

open LanglandsTunnell.CubicInduction Matrix

variable {L : Type*} [NormedField L]

end Ws23GaugeMem
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

namespace Ws23Jpss

p2m_open "IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction"

open scoped nonZeroDivisors

end Ws23Jpss
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

namespace Ws23Jpss

p2m_open "IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction"

open scoped nonZeroDivisors

end Ws23Jpss
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

namespace Ws23Fam5

namespace Ws23J6e

open IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell.Converse

end Ws23J6e
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

end Ws23Fam5
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace Ws23Tw

open LanglandsTunnell.CubicInduction

variable {v : HeightOneSpectrum (𝓞 ℚ)}

end Ws23Tw
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

namespace Ws23Tw

end Ws23Tw
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

namespace Ws23Tw

end Ws23Tw
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.LanglandsTunnell LanglandsTunnell.Converse"
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
p2m_open "LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction MeasureTheory"
open scoped nonZeroDivisors ENNReal
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace Ws23FF

open RSCarrier UnramifiedWhittaker
open scoped Classical

def cellLoc (v : HeightOneSpectrum (𝓞 ℚ)) : Set (GL (Fin 2) (v.adicCompletion ℚ)) :=
  {x | ∃ n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range, ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, x = n * k}

noncomputable def refSlot (v : HeightOneSpectrum (𝓞 ℚ)) : GL (Fin 2) (v.adicCompletion ℚ) → ℂ :=
  (cellLoc v).indicator fun _ => (1 : ℂ)

def cellAll : Set (finiteAdelicGL2Subgroup ℚ) :=
  {g | ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
    ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}

noncomputable def tensor (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))) (a : ∀ v : HeightOneSpectrum (𝓞 ℚ), GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (W' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) : finiteAdelicGL2Subgroup ℚ → ℂ :=
  (Ws23Fam5Holes.cellSet SQ).indicator fun g : finiteAdelicGL2Subgroup ℚ => (∏ v ∈ SQ, a v (localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ))) * W' g

noncomputable def psiLoc (v : HeightOneSpectrum (𝓞 ℚ))
    (μv : @Measure (GL (Fin 2) (v.adicCompletion ℚ)) (localGLBorel ℚ v))
    (μNv : @Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range (@Subtype.instMeasurableSpace _ _ (localGLBorel ℚ v)))
    (s : ℂ) (a b : GL (Fin 2) (v.adicCompletion ℚ) → ℂ) : ℂ :=
  letI := localGLBorel ℚ v
  rsLocalIntegral μv (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μNv
    (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
      (LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
    s a b

end Ws23FF
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

namespace Ws23FF

open RSCarrier UnramifiedWhittaker
open scoped Classical

variable (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))

theorem unipotent_eq {v : HeightOneSpectrum (𝓞 ℚ)} (x : v.adicCompletion ℚ) :
    (UnramifiedWhittaker.unipotent x : GL (Fin 2) (v.adicCompletion ℚ)) = unipotentGL2 x := Units.ext rfl

theorem unipotentGL2_mul_mem_cellLoc_iff {v : HeightOneSpectrum (𝓞 ℚ)} (x : v.adicCompletion ℚ)
    (y : GL (Fin 2) (v.adicCompletion ℚ)) : unipotentGL2 x * y ∈ cellLoc v ↔ y ∈ cellLoc v := by
  constructor
  · rintro ⟨n, hn, k, hk, h⟩
    refine ⟨(unipotentGL2 x)⁻¹ * n, mul_mem (inv_mem (Ws23Fam5Holes.unipotentGL2_mem_range _ x)) hn, k, hk, ?_⟩
    rw [mul_assoc, ← h, inv_mul_cancel_left]
  · rintro ⟨n, hn, k, hk, h⟩
    refine ⟨unipotentGL2 x * n, mul_mem (Ws23Fam5Holes.unipotentGL2_mem_range _ x) hn, k, hk, ?_⟩
    rw [h, mul_assoc]

theorem refSlot_unipotent_mul {v : HeightOneSpectrum (𝓞 ℚ)} (x : v.adicCompletion ℚ) (y : GL (Fin 2) (v.adicCompletion ℚ)) :
    refSlot v (UnramifiedWhittaker.unipotent x * y) = refSlot v y := by
  unfold refSlot
  rw [unipotent_eq]
  by_cases hy : y ∈ cellLoc v
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem ((unipotentGL2_mul_mem_cellLoc_iff x y).2 hy)]
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (fun h => hy ((unipotentGL2_mul_mem_cellLoc_iff x y).1 h))]

theorem measurable_refSlot (v : HeightOneSpectrum (𝓞 ℚ)) :
    letI := localGLBorel ℚ v
    Measurable (refSlot v) := by
  letI := localGLBorel ℚ v
  haveI := borelSpace_localGLBorel ℚ v
  exact (measurable_const.indicator (Ws23PencSwap.isClosed_bigCell v).measurableSet)

theorem modulus_det_eq_one_of_mem_cellLoc {v : HeightOneSpectrum (𝓞 ℚ)} {y : GL (Fin 2) (v.adicCompletion ℚ)}
    (hy : y ∈ cellLoc v) :
    LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det y : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = 1 := by
  obtain ⟨n, hn, k, hk, rfl⟩ := hy
  obtain ⟨a, rfl⟩ := hn
  have hdet : Matrix.GeneralLinearGroup.det ((unipotentGL2Hom (R := v.adicCompletion ℚ)) a) = 1 := by
    refine Units.ext ?_
    change Matrix.det ((unipotentGL2 (Multiplicative.toAdd a) : GL (Fin 2) (v.adicCompletion ℚ)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = 1
    exact Ws23Fam5Holes.det_unipotentGL2_val _
  rw [map_mul, hdet, one_mul]
  exact Ws23PencSwap.modulus_det_eq_one_of_mem_localLevelOne _ hk

theorem measurableSet_cellSet : MeasurableSet (Ws23Fam5Holes.cellSet SQ) :=
  (Ws23PencSwap.isClosed_cellSet SQ).measurableSet

theorem measurable_localAt (v : HeightOneSpectrum (𝓞 ℚ)) :
    letI := localGLBorel ℚ v
    Measurable fun g : finiteAdelicGL2Subgroup ℚ => localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) := by
  letI := localGLBorel ℚ v
  haveI := borelSpace_localGLBorel ℚ v
  exact ((continuous_localAt ℚ v).comp continuous_subtype_val).measurable

theorem measurable_slot {v : HeightOneSpectrum (𝓞 ℚ)} {a : GL (Fin 2) (v.adicCompletion ℚ) → ℂ}
    (ha : letI := localGLBorel ℚ v; Measurable a) :
    Measurable fun g : finiteAdelicGL2Subgroup ℚ => a (localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ)) := by
  letI := localGLBorel ℚ v
  exact ha.comp (measurable_localAt v)

theorem measurable_normPow (s : ℂ) :
    Measurable fun g : finiteAdelicGL2Subgroup ℚ =>
      ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2) :=
  (Complex.continuous_ofReal.comp ((NumberField.TateGlobal.continuous_ideleNorm_det ℚ).comp
    continuous_subtype_val)).measurable.pow_const _

theorem ideleNorm_det_unipotent_mul (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ) :
    ideleNorm ℚ (Matrix.GeneralLinearGroup.det ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ)) =
      ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) := by
  obtain ⟨b, hb⟩ := Ws23Fam5Holes.exists_eq_unipotentGL2_of_mem_finUnipotent n
  have hdet : Matrix.GeneralLinearGroup.det ((n : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) = 1 := by
    rw [hb]
    exact Units.ext (Ws23Fam5Holes.det_unipotentGL2_val _)
  rw [Subgroup.coe_mul, map_mul, hdet, one_mul]

theorem tensor_eq_slot_mul {v₀ : HeightOneSpectrum (𝓞 ℚ)} (hv₀ : v₀ ∈ SQ)
    (a : ∀ v : HeightOneSpectrum (𝓞 ℚ), GL (Fin 2) (v.adicCompletion ℚ) → ℂ) (W' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (g : finiteAdelicGL2Subgroup ℚ) :
    tensor SQ a W' g = a v₀ (localAt ℚ v₀ (g : AdelicGL2 (𝓞 ℚ) ℚ)) *
      (Ws23Fam5Holes.cellSet SQ).indicator
        (fun g : finiteAdelicGL2Subgroup ℚ => (∏ v ∈ SQ.erase v₀, a v (localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ))) * W' g) g := by
  unfold tensor
  refine Ws23SwapStep.ind_mul _ ?_
  rw [← Finset.mul_prod_erase SQ _ hv₀, mul_assoc]

theorem tensor_update_eq_slot_mul {v₀ : HeightOneSpectrum (𝓞 ℚ)} (hv₀ : v₀ ∈ SQ)
    (a : ∀ v : HeightOneSpectrum (𝓞 ℚ), GL (Fin 2) (v.adicCompletion ℚ) → ℂ) (a₀ : GL (Fin 2) (v₀.adicCompletion ℚ) → ℂ)
    (W' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (g : finiteAdelicGL2Subgroup ℚ) :
    tensor SQ (Function.update a v₀ a₀) W' g = a₀ (localAt ℚ v₀ (g : AdelicGL2 (𝓞 ℚ) ℚ)) *
      (Ws23Fam5Holes.cellSet SQ).indicator
        (fun g : finiteAdelicGL2Subgroup ℚ => (∏ v ∈ SQ.erase v₀, a v (localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ))) * W' g) g := by
  rw [tensor_eq_slot_mul SQ hv₀, Function.update_self]
  congr 2
  funext g'
  congr 1
  refine Finset.prod_congr rfl fun v hv => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hv)]

end Ws23FF
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

namespace Ws23FF

open RSCarrier UnramifiedWhittaker
open scoped Classical

theorem one_place
    [SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ)]
    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))) {v₀ : HeightOneSpectrum (𝓞 ℚ)} (hv₀ : v₀ ∈ SQ)
    (μ : Measure (finiteAdelicGL2Subgroup ℚ)) [μ.IsHaarMeasure]
    (μN : Measure RSCarrier.finUnipotent) [μN.IsHaarMeasure]
    (a b : ∀ v : HeightOneSpectrum (𝓞 ℚ), GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (W' F' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hW' : ∀ (x : GL (Fin 2) (v₀.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ), W' (g * placeEmbed ℚ v₀ x) = W' g)
    (hF' : ∀ (x : GL (Fin 2) (v₀.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ), F' (g * placeEmbed ℚ v₀ x) = F' g)
    (hN : ∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
      W' ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) *
          F' ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) =
        W' (g : AdelicGL2 (𝓞 ℚ) ℚ) * F' (g : AdelicGL2 (𝓞 ℚ) ℚ))
    (hab : ∀ v ∈ SQ, ∀ (x : v.adicCompletion ℚ) (y : GL (Fin 2) (v.adicCompletion ℚ)),
      a v (UnramifiedWhittaker.unipotent x * y) * b v (UnramifiedWhittaker.unipotent x * y) = a v y * b v y)
    (hameas : ∀ v ∈ SQ, letI := localGLBorel ℚ v; Measurable (a v) ∧ Measurable (b v))
    (hmeas' : Measurable fun g : finiteAdelicGL2Subgroup ℚ => W' (g : AdelicGL2 (𝓞 ℚ) ℚ) * F' (g : AdelicGL2 (𝓞 ℚ) ℚ))
    (a₀ b₀ : GL (Fin 2) (v₀.adicCompletion ℚ) → ℂ)
    (hab₀ : ∀ (x : v₀.adicCompletion ℚ) (y : GL (Fin 2) (v₀.adicCompletion ℚ)),
      a₀ (UnramifiedWhittaker.unipotent x * y) * b₀ (UnramifiedWhittaker.unipotent x * y) = a₀ y * b₀ y)
    (hameas₀ : letI := localGLBorel ℚ v₀; Measurable a₀ ∧ Measurable b₀)
    (s : ℂ)
    (μ₂ : @Measure (GL (Fin 2) (v₀.adicCompletion ℚ)) (localGLBorel ℚ v₀))
    (μN₂ : @Measure ↥(unipotentGL2Hom (R := v₀.adicCompletion ℚ)).range (@Subtype.instMeasurableSpace _ _ (localGLBorel ℚ v₀)))
    (hμ₂ : letI := localGLBorel ℚ v₀
      haveI := borelSpace_localGLBorel ℚ v₀
      μ₂.IsHaarMeasure ∧ μN₂.IsHaarMeasure) :
    (∃ C : ℂ,
      rsFinIntegral μ μN s (tensor SQ a W') (tensor SQ b F') = C * psiLoc v₀ μ₂ μN₂ s (a v₀) (b v₀) ∧
      rsFinIntegral μ μN s (tensor SQ (Function.update a v₀ a₀) W') (tensor SQ (Function.update b v₀ b₀) F') =
        C * psiLoc v₀ μ₂ μN₂ s a₀ b₀) ∧
    (∃ J : ℝ≥0∞,
      (∫⁻ g, ‖(tensor SQ a W' g * tensor SQ b F' g) *
          ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2)‖ₑ
        ∂(μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN))) =
        (letI := localGLBorel ℚ v₀
         ∫⁻ x, ‖(a v₀ x * b v₀ x) *
            ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det x : (v₀.adicCompletion ℚ)ˣ) :
              v₀.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)‖ₑ
          ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v₀.adicCompletion ℚ)).range μN₂))) * J ∧
      (∫⁻ g, ‖(tensor SQ (Function.update a v₀ a₀) W' g * tensor SQ (Function.update b v₀ b₀) F' g) *
          ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2)‖ₑ
        ∂(μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN))) =
        (letI := localGLBorel ℚ v₀
         ∫⁻ x, ‖(a₀ x * b₀ x) *
            ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det x : (v₀.adicCompletion ℚ)ˣ) :
              v₀.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)‖ₑ
          ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v₀.adicCompletion ℚ)).range μN₂))) * J) := by
  letI : MeasurableSpace (GL (Fin 2) (v₀.adicCompletion ℚ)) := localGLBorel ℚ v₀
  haveI : BorelSpace (GL (Fin 2) (v₀.adicCompletion ℚ)) := borelSpace_localGLBorel ℚ v₀
  haveI := hμ₂.1
  haveI := hμ₂.2

  let restW : finiteAdelicGL2Subgroup ℚ → ℂ := fun g : finiteAdelicGL2Subgroup ℚ =>
    (∏ v ∈ SQ.erase v₀, a v (localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ))) * W' g
  let restF : finiteAdelicGL2Subgroup ℚ → ℂ := fun g : finiteAdelicGL2Subgroup ℚ =>
    (∏ v ∈ SQ.erase v₀, b v (localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ))) * F' g
  let WR : AdelicGL2 (𝓞 ℚ) ℚ → ℂ := fun G => (Ws23Fam5Holes.cellSet SQ).indicator restW (RSCarrier.finFactor G)
  let FR : AdelicGL2 (𝓞 ℚ) ℚ → ℂ := fun G => (Ws23Fam5Holes.cellSet SQ).indicator restF (RSCarrier.finFactor G)
  have hfe : ∀ x : GL (Fin 2) (v₀.adicCompletion ℚ),
      (RSCarrier.finFactor (placeEmbed ℚ v₀ x) : AdelicGL2 (𝓞 ℚ) ℚ) = placeEmbed ℚ v₀ x :=
    Ws23SwapStep.coe_finFactor_placeEmbed _

  have hCp : ∀ (g : finiteAdelicGL2Subgroup ℚ) (x : GL (Fin 2) (v₀.adicCompletion ℚ)),
      g * RSCarrier.finFactor (placeEmbed ℚ v₀ x) ∈ Ws23Fam5Holes.cellSet SQ ↔ g ∈ Ws23Fam5Holes.cellSet SQ := by
    intro g x
    have key : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
        localAt ℚ p ((g * RSCarrier.finFactor (placeEmbed ℚ v₀ x) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) =
          localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) := by
      intro p hp
      have hpv : p ≠ v₀ := fun h => by subst h; exact hp hv₀
      rw [Subgroup.coe_mul, hfe, map_mul, Ws23SwapStep.localAt_placeEmbed_of_ne hpv, mul_one]
    constructor
    · intro h p hp
      rw [← key p hp]
      exact h p hp
    · intro h p hp
      rw [key p hp]
      exact h p hp

  have hrestW_inv : ∀ (g : finiteAdelicGL2Subgroup ℚ) (x : GL (Fin 2) (v₀.adicCompletion ℚ)),
      restW (g * RSCarrier.finFactor (placeEmbed ℚ v₀ x)) = restW g := by
    intro g x
    show (∏ v ∈ SQ.erase v₀, a v (localAt ℚ v ((g * RSCarrier.finFactor (placeEmbed ℚ v₀ x) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ))) *
        W' ((g * RSCarrier.finFactor (placeEmbed ℚ v₀ x) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) = _
    rw [Subgroup.coe_mul, hfe, hW']
    congr 1
    refine Finset.prod_congr rfl fun v hv => ?_
    rw [map_mul, Ws23SwapStep.localAt_placeEmbed_of_ne (Finset.ne_of_mem_erase hv), mul_one]
  have hrestF_inv : ∀ (g : finiteAdelicGL2Subgroup ℚ) (x : GL (Fin 2) (v₀.adicCompletion ℚ)),
      restF (g * RSCarrier.finFactor (placeEmbed ℚ v₀ x)) = restF g := by
    intro g x
    show (∏ v ∈ SQ.erase v₀, b v (localAt ℚ v ((g * RSCarrier.finFactor (placeEmbed ℚ v₀ x) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ))) *
        F' ((g * RSCarrier.finFactor (placeEmbed ℚ v₀ x) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) = _
    rw [Subgroup.coe_mul, hfe, hF']
    congr 1
    refine Finset.prod_congr rfl fun v hv => ?_
    rw [map_mul, Ws23SwapStep.localAt_placeEmbed_of_ne (Finset.ne_of_mem_erase hv), mul_one]
  have hWR_inv : ∀ (x : GL (Fin 2) (v₀.adicCompletion ℚ)) (G : AdelicGL2 (𝓞 ℚ) ℚ), WR (G * placeEmbed ℚ v₀ x) = WR G := by
    intro x G
    show (Ws23Fam5Holes.cellSet SQ).indicator restW (RSCarrier.finFactor (G * placeEmbed ℚ v₀ x)) =
      (Ws23Fam5Holes.cellSet SQ).indicator restW (RSCarrier.finFactor G)
    rw [Ws23SwapStep.finFactor_mul_placeEmbed]
    by_cases hG : RSCarrier.finFactor G ∈ Ws23Fam5Holes.cellSet SQ
    · rw [Set.indicator_of_mem hG, Set.indicator_of_mem ((hCp _ x).2 hG), hrestW_inv]
    · rw [Set.indicator_of_notMem hG, Set.indicator_of_notMem (fun h => hG ((hCp _ x).1 h))]
  have hFR_inv : ∀ (x : GL (Fin 2) (v₀.adicCompletion ℚ)) (G : AdelicGL2 (𝓞 ℚ) ℚ), FR (G * placeEmbed ℚ v₀ x) = FR G := by
    intro x G
    show (Ws23Fam5Holes.cellSet SQ).indicator restF (RSCarrier.finFactor (G * placeEmbed ℚ v₀ x)) =
      (Ws23Fam5Holes.cellSet SQ).indicator restF (RSCarrier.finFactor G)
    rw [Ws23SwapStep.finFactor_mul_placeEmbed]
    by_cases hG : RSCarrier.finFactor G ∈ Ws23Fam5Holes.cellSet SQ
    · rw [Set.indicator_of_mem hG, Set.indicator_of_mem ((hCp _ x).2 hG), hrestF_inv]
    · rw [Set.indicator_of_notMem hG, Set.indicator_of_notMem (fun h => hG ((hCp _ x).1 h))]
  have hWR_coe : ∀ g : finiteAdelicGL2Subgroup ℚ, WR (g : AdelicGL2 (𝓞 ℚ) ℚ) = (Ws23Fam5Holes.cellSet SQ).indicator restW g :=
    fun g : finiteAdelicGL2Subgroup ℚ => by
      show (Ws23Fam5Holes.cellSet SQ).indicator restW (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ)) = _
      rw [Ws23SwapStep.finFactor_coe]
  have hFR_coe : ∀ g : finiteAdelicGL2Subgroup ℚ, FR (g : AdelicGL2 (𝓞 ℚ) ℚ) = (Ws23Fam5Holes.cellSet SQ).indicator restF g :=
    fun g : finiteAdelicGL2Subgroup ℚ => by
      show (Ws23Fam5Holes.cellSet SQ).indicator restF (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ)) = _
      rw [Ws23SwapStep.finFactor_coe]

  have hsplit : ∀ g : finiteAdelicGL2Subgroup ℚ, restW g * restF g =
      (∏ v ∈ SQ.erase v₀, a v (localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ)) * b v (localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ))) *
        (W' g * F' g) := by
    intro g
    show ((∏ v ∈ SQ.erase v₀, a v (localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ))) * W' g) *
        ((∏ v ∈ SQ.erase v₀, b v (localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ))) * F' g) = _
    rw [Finset.prod_mul_distrib]
    ring

  have hNrest : ∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
      restW ((n : finiteAdelicGL2Subgroup ℚ) * g) * restF ((n : finiteAdelicGL2Subgroup ℚ) * g) = restW g * restF g := by
    intro n g
    rw [hsplit, hsplit, hN n g]
    congr 1
    refine Finset.prod_congr rfl fun v hv => ?_
    obtain ⟨x, hx⟩ := Ws23Fam5Holes.localAt_coe_finUnipotent n v
    rw [Subgroup.coe_mul, map_mul, hx, ← unipotent_eq, hab v (Finset.mem_of_mem_erase hv)]
  have hN' : ∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
      WR ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) *
          FR ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) =
        WR (g : AdelicGL2 (𝓞 ℚ) ℚ) * FR (g : AdelicGL2 (𝓞 ℚ) ℚ) := by
    intro n g
    rw [hWR_coe, hFR_coe, hWR_coe, hFR_coe, Ws23SwapStep.ind_mul_ind, Ws23SwapStep.ind_mul_ind]
    by_cases hg : g ∈ Ws23Fam5Holes.cellSet SQ
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem ((Ws23Fam5Holes.unipotent_mul_mem_cellSet_iff SQ n g).2 hg),
        hNrest]
    · rw [Set.indicator_of_notMem hg,
        Set.indicator_of_notMem (fun h => hg ((Ws23Fam5Holes.unipotent_mul_mem_cellSet_iff SQ n g).1 h)),
        zero_mul, zero_mul]

  have hTa : ∀ g : finiteAdelicGL2Subgroup ℚ, tensor SQ a W' g = a v₀ (localAt ℚ v₀ (g : AdelicGL2 (𝓞 ℚ) ℚ)) * WR g :=
    fun g : finiteAdelicGL2Subgroup ℚ => by rw [hWR_coe]; exact tensor_eq_slot_mul SQ hv₀ a W' g
  have hTb : ∀ g : finiteAdelicGL2Subgroup ℚ, tensor SQ b F' g = b v₀ (localAt ℚ v₀ (g : AdelicGL2 (𝓞 ℚ) ℚ)) * FR g :=
    fun g : finiteAdelicGL2Subgroup ℚ => by rw [hFR_coe]; exact tensor_eq_slot_mul SQ hv₀ b F' g
  have hTa₀ : ∀ g : finiteAdelicGL2Subgroup ℚ,
      tensor SQ (Function.update a v₀ a₀) W' g = a₀ (localAt ℚ v₀ (g : AdelicGL2 (𝓞 ℚ) ℚ)) * WR g :=
    fun g : finiteAdelicGL2Subgroup ℚ => by rw [hWR_coe]; exact tensor_update_eq_slot_mul SQ hv₀ a a₀ W' g
  have hTb₀ : ∀ g : finiteAdelicGL2Subgroup ℚ,
      tensor SQ (Function.update b v₀ b₀) F' g = b₀ (localAt ℚ v₀ (g : AdelicGL2 (𝓞 ℚ) ℚ)) * FR g :=
    fun g : finiteAdelicGL2Subgroup ℚ => by rw [hFR_coe]; exact tensor_update_eq_slot_mul SQ hv₀ b b₀ F' g

  have hmeasRest : Measurable fun g : finiteAdelicGL2Subgroup ℚ =>
      (Ws23Fam5Holes.cellSet SQ).indicator restW g * (Ws23Fam5Holes.cellSet SQ).indicator restF g := by
    have h1 : (fun g : finiteAdelicGL2Subgroup ℚ =>
        (Ws23Fam5Holes.cellSet SQ).indicator restW g * (Ws23Fam5Holes.cellSet SQ).indicator restF g) =
        (Ws23Fam5Holes.cellSet SQ).indicator (fun g : finiteAdelicGL2Subgroup ℚ => restW g * restF g) := by
      funext g
      by_cases hg : g ∈ Ws23Fam5Holes.cellSet SQ
      · simp only [Set.indicator_of_mem hg]
      · simp only [Set.indicator_of_notMem hg, zero_mul]
    rw [h1]
    refine Measurable.indicator ?_ (measurableSet_cellSet SQ)
    rw [show (fun g : finiteAdelicGL2Subgroup ℚ => restW g * restF g) = fun g : finiteAdelicGL2Subgroup ℚ =>
        (∏ v ∈ SQ.erase v₀, a v (localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ)) * b v (localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ))) *
          (W' g * F' g) from funext hsplit]
    refine Measurable.mul (Finset.measurable_prod _ fun v hv => ?_) hmeas'
    exact (measurable_slot (hameas v (Finset.mem_of_mem_erase hv)).1).mul
      (measurable_slot (hameas v (Finset.mem_of_mem_erase hv)).2)
  have hmeas_pair : ∀ (p q : GL (Fin 2) (v₀.adicCompletion ℚ) → ℂ), Measurable p → Measurable q →
      Measurable (fun g : finiteAdelicGL2Subgroup ℚ =>
        (p (localAt ℚ v₀ (g : AdelicGL2 (𝓞 ℚ) ℚ)) * WR g) * (q (localAt ℚ v₀ (g : AdelicGL2 (𝓞 ℚ) ℚ)) * FR g)) := by
    intro p q hp hq
    have h1 : (fun g : finiteAdelicGL2Subgroup ℚ =>
        (p (localAt ℚ v₀ (g : AdelicGL2 (𝓞 ℚ) ℚ)) * WR g) * (q (localAt ℚ v₀ (g : AdelicGL2 (𝓞 ℚ) ℚ)) * FR g)) =
        fun g : finiteAdelicGL2Subgroup ℚ => (p (localAt ℚ v₀ (g : AdelicGL2 (𝓞 ℚ) ℚ)) * q (localAt ℚ v₀ (g : AdelicGL2 (𝓞 ℚ) ℚ))) *
          ((Ws23Fam5Holes.cellSet SQ).indicator restW g * (Ws23Fam5Holes.cellSet SQ).indicator restF g) := by
      funext g
      rw [hWR_coe, hFR_coe]
      ring
    rw [h1]
    exact ((measurable_slot hp).mul (measurable_slot hq)).mul hmeasRest

  obtain ⟨Cst, hCst⟩ :=
    LanglandsTunnell.RankinSelberg.exists_forall_rsFinIntegral_eq_const_mul_rsLocalIntegral_of_factorsAt v₀ μ μN
      WR FR hWR_inv hFR_inv hN' s μ₂ μN₂
  have hId : ∀ (p q : GL (Fin 2) (v₀.adicCompletion ℚ) → ℂ),
      (∀ (x : v₀.adicCompletion ℚ) (y : GL (Fin 2) (v₀.adicCompletion ℚ)),
        p (UnramifiedWhittaker.unipotent x * y) * q (UnramifiedWhittaker.unipotent x * y) = p y * q y) →
      Measurable p → Measurable q →
      rsFinIntegral μ μN s (fun g : finiteAdelicGL2Subgroup ℚ => p (localAt ℚ v₀ (g : AdelicGL2 (𝓞 ℚ) ℚ)) * WR g)
          (fun g : finiteAdelicGL2Subgroup ℚ => q (localAt ℚ v₀ (g : AdelicGL2 (𝓞 ℚ) ℚ)) * FR g) =
        Cst * psiLoc v₀ μ₂ μN₂ s p q :=
    fun p q hpq hp hq => hCst (fun G => p (localAt ℚ v₀ G) * WR G) (fun G => q (localAt ℚ v₀ G) * FR G) p q
      (fun _ => rfl) (fun _ => rfl) hpq (hmeas_pair p q hp hq)
  refine ⟨⟨Cst, ?_, ?_⟩, ?_⟩
  · rw [show tensor SQ a W' = fun g : finiteAdelicGL2Subgroup ℚ => a v₀ (localAt ℚ v₀ (g : AdelicGL2 (𝓞 ℚ) ℚ)) * WR g
        from funext hTa,
      show tensor SQ b F' = fun g : finiteAdelicGL2Subgroup ℚ => b v₀ (localAt ℚ v₀ (g : AdelicGL2 (𝓞 ℚ) ℚ)) * FR g
        from funext hTb]
    exact hId (a v₀) (b v₀) (hab v₀ hv₀) (hameas v₀ hv₀).1 (hameas v₀ hv₀).2
  · rw [show tensor SQ (Function.update a v₀ a₀) W' =
          fun g : finiteAdelicGL2Subgroup ℚ => a₀ (localAt ℚ v₀ (g : AdelicGL2 (𝓞 ℚ) ℚ)) * WR g from funext hTa₀,
      show tensor SQ (Function.update b v₀ b₀) F' =
          fun g : finiteAdelicGL2Subgroup ℚ => b₀ (localAt ℚ v₀ (g : AdelicGL2 (𝓞 ℚ) ℚ)) * FR g from funext hTb₀]
    exact hId a₀ b₀ hab₀ hameas₀.1 hameas₀.2

  obtain ⟨μ', _hsf, hae, hdis⟩ :=
    LanglandsTunnell.RankinSelberg.exists_sFinite_forall_lintegral_withDensity_density_eq_lintegral_lintegral_mul_finFactor_placeEmbed
      v₀ μ μN μ₂ μN₂

  let R : finiteAdelicGL2Subgroup ℚ → ℝ≥0∞ := fun g : finiteAdelicGL2Subgroup ℚ =>
    ‖((Ws23Fam5Holes.cellSet SQ).indicator restW g * (Ws23Fam5Holes.cellSet SQ).indicator restF g) *
      ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2)‖ₑ
  have hRmeas : Measurable R := (hmeasRest.mul (measurable_normPow s)).enorm

  have hL : ∀ (p q : GL (Fin 2) (v₀.adicCompletion ℚ) → ℂ),
      (∀ (x : v₀.adicCompletion ℚ) (y : GL (Fin 2) (v₀.adicCompletion ℚ)),
        p (UnramifiedWhittaker.unipotent x * y) * q (UnramifiedWhittaker.unipotent x * y) = p y * q y) →
      Measurable p → Measurable q →
      (∫⁻ g, ‖((p (localAt ℚ v₀ (g : AdelicGL2 (𝓞 ℚ) ℚ)) * WR g) * (q (localAt ℚ v₀ (g : AdelicGL2 (𝓞 ℚ) ℚ)) * FR g)) *
          ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2)‖ₑ
        ∂(μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN))) =
        (∫⁻ x, ‖(p x * q x) *
            ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det x : (v₀.adicCompletion ℚ)ˣ) :
              v₀.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)‖ₑ
          ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v₀.adicCompletion ℚ)).range μN₂))) *
          ∫⁻ g, R g ∂μ' := by
    intro p q hpq hp hq

    have hΦmeas : Measurable fun g : finiteAdelicGL2Subgroup ℚ =>
        ‖((p (localAt ℚ v₀ (g : AdelicGL2 (𝓞 ℚ) ℚ)) * WR g) * (q (localAt ℚ v₀ (g : AdelicGL2 (𝓞 ℚ) ℚ)) * FR g)) *
          ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2)‖ₑ :=
      ((hmeas_pair p q hp hq).mul (measurable_normPow s)).enorm
    have hΦinv : ∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
        ‖((p (localAt ℚ v₀ (((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)) *
              WR (((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)) *
            (q (localAt ℚ v₀ (((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)) *
              FR (((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ))) *
          ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det
              (((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2)‖ₑ =
        ‖((p (localAt ℚ v₀ (g : AdelicGL2 (𝓞 ℚ) ℚ)) * WR g) * (q (localAt ℚ v₀ (g : AdelicGL2 (𝓞 ℚ) ℚ)) * FR g)) *
          ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2)‖ₑ := by
      intro n g
      obtain ⟨x, hx⟩ := Ws23Fam5Holes.localAt_coe_finUnipotent n v₀
      rw [ideleNorm_det_unipotent_mul, mul_mul_mul_comm, hN' n g, Subgroup.coe_mul, map_mul, hx, ← unipotent_eq, hpq,
        ← mul_mul_mul_comm]
    rw [hdis _ hΦmeas hΦinv]

    have hinner : ∀ g' : finiteAdelicGL2Subgroup ℚ, localAt ℚ v₀ (g' : AdelicGL2 (𝓞 ℚ) ℚ) = 1 →
        (∫⁻ x, ‖((p (localAt ℚ v₀ ((g' * RSCarrier.finFactor (placeEmbed ℚ v₀ x) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)) *
                  WR ((g' * RSCarrier.finFactor (placeEmbed ℚ v₀ x) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)) *
                (q (localAt ℚ v₀ ((g' * RSCarrier.finFactor (placeEmbed ℚ v₀ x) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)) *
                  FR ((g' * RSCarrier.finFactor (placeEmbed ℚ v₀ x) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ))) *
              ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det
                  ((g' * RSCarrier.finFactor (placeEmbed ℚ v₀ x) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2)‖ₑ
            ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v₀.adicCompletion ℚ)).range μN₂))) =
          (∫⁻ x, ‖(p x * q x) *
              ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det x : (v₀.adicCompletion ℚ)ˣ) :
                v₀.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)‖ₑ
            ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v₀.adicCompletion ℚ)).range μN₂))) * R g' := by
      intro g' hg'
      have hcomm : ∀ x : GL (Fin 2) (v₀.adicCompletion ℚ),
          ((g' * RSCarrier.finFactor (placeEmbed ℚ v₀ x) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) =
            (g' : AdelicGL2 (𝓞 ℚ) ℚ) * placeEmbed ℚ v₀ x := fun x => by rw [Subgroup.coe_mul, hfe]
      have hpt : ∀ x : GL (Fin 2) (v₀.adicCompletion ℚ),
          ‖((p (localAt ℚ v₀ ((g' * RSCarrier.finFactor (placeEmbed ℚ v₀ x) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)) *
                  WR ((g' * RSCarrier.finFactor (placeEmbed ℚ v₀ x) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)) *
                (q (localAt ℚ v₀ ((g' * RSCarrier.finFactor (placeEmbed ℚ v₀ x) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)) *
                  FR ((g' * RSCarrier.finFactor (placeEmbed ℚ v₀ x) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ))) *
              ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det
                  ((g' * RSCarrier.finFactor (placeEmbed ℚ v₀ x) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2)‖ₑ =
          ‖(p x * q x) *
              ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det x : (v₀.adicCompletion ℚ)ˣ) :
                v₀.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)‖ₑ * R g' := by
        intro x
        have hloc : localAt ℚ v₀ ((g' : AdelicGL2 (𝓞 ℚ) ℚ) * placeEmbed ℚ v₀ x) = x := by
          rw [map_mul, hg', Ws23SwapStep.localAt_placeEmbed_self, one_mul]
        have hnorm : ideleNorm ℚ (Matrix.GeneralLinearGroup.det ((g' : AdelicGL2 (𝓞 ℚ) ℚ) * placeEmbed ℚ v₀ x)) =
            (LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det x : (v₀.adicCompletion ℚ)ˣ) : v₀.adicCompletion ℚ) : ℝ) *
              ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g' : AdelicGL2 (𝓞 ℚ) ℚ)) := by
          rw [← Ws23SwapStep.placeEmbed_mul_comm v₀ hg' x]
          exact Ws23Fam5Holes.ideleNorm_det_placeEmbed_mul v₀ x _
        rw [hcomm, hloc, hWR_inv, hFR_inv, hnorm]
        rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NumberField.TateGlobal.ideleNorm_pos _).le, hWR_coe, hFR_coe,
          ← enorm_mul]
        congr 1
        ring
      rw [lintegral_congr (fun x => hpt x)]
      exact lintegral_mul_const _ (((hp.mul hq).mul ((Ws23PencSwap.continuous_modulus_det v₀).measurable.pow_const _)).enorm)
    calc (∫⁻ g', ∫⁻ x, ‖((p (localAt ℚ v₀ ((g' * RSCarrier.finFactor (placeEmbed ℚ v₀ x) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)) *
                  WR ((g' * RSCarrier.finFactor (placeEmbed ℚ v₀ x) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)) *
                (q (localAt ℚ v₀ ((g' * RSCarrier.finFactor (placeEmbed ℚ v₀ x) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)) *
                  FR ((g' * RSCarrier.finFactor (placeEmbed ℚ v₀ x) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ))) *
              ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det
                  ((g' * RSCarrier.finFactor (placeEmbed ℚ v₀ x) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2)‖ₑ
            ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v₀.adicCompletion ℚ)).range μN₂)) ∂μ')
        = ∫⁻ g', (∫⁻ x, ‖(p x * q x) *
              ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det x : (v₀.adicCompletion ℚ)ˣ) :
                v₀.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)‖ₑ
            ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v₀.adicCompletion ℚ)).range μN₂))) * R g' ∂μ' := by
          refine lintegral_congr_ae ?_
          filter_upwards [hae] with g' hg'
          exact hinner g' hg'
      _ = (∫⁻ x, ‖(p x * q x) *
              ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det x : (v₀.adicCompletion ℚ)ˣ) :
                v₀.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)‖ₑ
            ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v₀.adicCompletion ℚ)).range μN₂))) * ∫⁻ g', R g' ∂μ' :=
          lintegral_const_mul _ hRmeas
  refine ⟨∫⁻ g', R g' ∂μ', ?_, ?_⟩
  · rw [show (fun g : finiteAdelicGL2Subgroup ℚ => ‖(tensor SQ a W' g * tensor SQ b F' g) *
          ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2)‖ₑ) =
        fun g : finiteAdelicGL2Subgroup ℚ => ‖((a v₀ (localAt ℚ v₀ (g : AdelicGL2 (𝓞 ℚ) ℚ)) * WR g) * (b v₀ (localAt ℚ v₀ (g : AdelicGL2 (𝓞 ℚ) ℚ)) * FR g)) *
          ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2)‖ₑ from
        funext fun g : finiteAdelicGL2Subgroup ℚ => by rw [hTa, hTb]]
    exact hL (a v₀) (b v₀) (hab v₀ hv₀) (hameas v₀ hv₀).1 (hameas v₀ hv₀).2
  · rw [show (fun g : finiteAdelicGL2Subgroup ℚ => ‖(tensor SQ (Function.update a v₀ a₀) W' g * tensor SQ (Function.update b v₀ b₀) F' g) *
          ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2)‖ₑ) =
        fun g : finiteAdelicGL2Subgroup ℚ => ‖((a₀ (localAt ℚ v₀ (g : AdelicGL2 (𝓞 ℚ) ℚ)) * WR g) * (b₀ (localAt ℚ v₀ (g : AdelicGL2 (𝓞 ℚ) ℚ)) * FR g)) *
          ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2)‖ₑ from
        funext fun g : finiteAdelicGL2Subgroup ℚ => by rw [hTa₀, hTb₀]]
    exact hL a₀ b₀ hab₀ hameas₀.1 hameas₀.2

theorem measurable_tensor_mul (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (a b : ∀ v : HeightOneSpectrum (𝓞 ℚ), GL (Fin 2) (v.adicCompletion ℚ) → ℂ) (W' F' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hameas : ∀ v ∈ SQ, letI := localGLBorel ℚ v; Measurable (a v) ∧ Measurable (b v))
    (hmeas' : Measurable fun g : finiteAdelicGL2Subgroup ℚ => W' (g : AdelicGL2 (𝓞 ℚ) ℚ) * F' (g : AdelicGL2 (𝓞 ℚ) ℚ)) :
    Measurable fun g : finiteAdelicGL2Subgroup ℚ => tensor SQ a W' g * tensor SQ b F' g := by
  have h1 : (fun g : finiteAdelicGL2Subgroup ℚ => tensor SQ a W' g * tensor SQ b F' g) =
      (Ws23Fam5Holes.cellSet SQ).indicator fun g : finiteAdelicGL2Subgroup ℚ =>
        (∏ v ∈ SQ, a v (localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ)) * b v (localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ))) *
          (W' g * F' g) := by
    funext g
    unfold tensor
    by_cases hg : g ∈ Ws23Fam5Holes.cellSet SQ
    · simp only [Set.indicator_of_mem hg]
      rw [Finset.prod_mul_distrib]
      ring
    · simp only [Set.indicator_of_notMem hg, zero_mul]
  rw [h1]
  refine Measurable.indicator ?_ (measurableSet_cellSet SQ)
  refine Measurable.mul (Finset.measurable_prod _ fun v hv => ?_) hmeas'
  exact (measurable_slot (hameas v hv).1).mul (measurable_slot (hameas v hv).2)

theorem terminal (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))) (W' F' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hblind : ∀ v ∈ SQ, ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      W' (g * placeEmbed ℚ v x) = W' g ∧ F' (g * placeEmbed ℚ v x) = F' g)
    (hN : ∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
      W' ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) *
          F' ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) =
        W' (g : AdelicGL2 (𝓞 ℚ) ℚ) * F' (g : AdelicGL2 (𝓞 ℚ) ℚ))
    (hK : ∀ k : finiteAdelicGL2Subgroup ℚ,
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ →
        localAt ℚ v (k : AdelicGL2 (𝓞 ℚ) ℚ) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤) →
      (∀ v ∈ SQ, localAt ℚ v (k : AdelicGL2 (𝓞 ℚ) ℚ) = 1) →
      ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
        W' (g * (k : AdelicGL2 (𝓞 ℚ) ℚ)) = W' g ∧ F' (g * (k : AdelicGL2 (𝓞 ℚ) ℚ)) = F' g)
    (s : ℂ) (g : finiteAdelicGL2Subgroup ℚ) :
    (tensor SQ (fun v => refSlot v) W' g * tensor SQ (fun v => refSlot v) F' g) *
        ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2) =
      (W' 1 * F' 1) * cellAll.indicator (fun _ => (1 : ℂ)) g := by
  classical
  by_cases hA : g ∈ cellAll
  · have hA' : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
        ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k := hA
    have hcut : g ∈ Ws23Fam5Holes.cellSet SQ := fun v _ => hA' v
    have hloc : ∀ v : HeightOneSpectrum (𝓞 ℚ), localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) ∈ cellLoc v := fun v => hA' v
    have hone : ∀ v ∈ SQ, refSlot v (localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ)) = 1 := fun v _ => by
      unfold refSlot
      rw [Set.indicator_of_mem (hloc v)]
    obtain ⟨hWF, hnorm⟩ :=
      LanglandsTunnell.RankinSelberg.mul_eq_mul_one_and_ideleNorm_det_eq_finprod_of_mem_cut_of_blind SQ W' F' hblind hN hK g hcut
    have hN1 : (ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) = 1 := by
      rw [hnorm]
      refine Finset.prod_eq_one fun v _ => ?_
      rw [modulus_det_eq_one_of_mem_cellLoc (hloc v)]
      rfl
    unfold tensor
    rw [Set.indicator_of_mem hcut, Set.indicator_of_mem hcut, Set.indicator_of_mem hA, Finset.prod_eq_one hone,
      one_mul, one_mul, hN1, Complex.ofReal_one, Complex.one_cpow, mul_one, mul_one, hWF]
  · rw [Set.indicator_of_notMem hA, mul_zero]
    have hA' : ¬ ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
        ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k := hA
    push Not at hA'
    obtain ⟨v, hv⟩ := hA'
    have hv' : localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) ∉ cellLoc v := fun ⟨n, hn, k, hk, h⟩ => hv n hn k hk h
    by_cases hvS : v ∈ SQ
    · have h0 : tensor SQ (fun v => refSlot v) W' g = 0 := by
        unfold tensor
        by_cases hg : g ∈ Ws23Fam5Holes.cellSet SQ
        · rw [Set.indicator_of_mem hg, Finset.prod_eq_zero hvS (Set.indicator_of_notMem hv' _), zero_mul]
        · rw [Set.indicator_of_notMem hg]
      rw [h0, zero_mul, zero_mul]
    · have hg : g ∉ Ws23Fam5Holes.cellSet SQ := fun h => by
        obtain ⟨n, hn, k, hk, h'⟩ := h v hvS
        exact hv n hn k hk h'
      unfold tensor
      rw [Set.indicator_of_notMem hg, zero_mul, zero_mul]

end Ws23FF
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable.Ws23Fam5"

open Ws23FF in
open scoped Classical in

theorem solution
    [SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ)]
    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (μ : Measure (finiteAdelicGL2Subgroup ℚ)) [μ.IsHaarMeasure]
    (μN : Measure RSCarrier.finUnipotent) [μN.IsHaarMeasure]

    (μv : ∀ v : HeightOneSpectrum (𝓞 ℚ), @Measure (GL (Fin 2) (v.adicCompletion ℚ)) (localGLBorel ℚ v))
    (μNv : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      @Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range (@Subtype.instMeasurableSpace _ _ (localGLBorel ℚ v)))
    (hμv : ∀ v ∈ SQ,
      letI := localGLBorel ℚ v
      haveI := borelSpace_localGLBorel ℚ v
      (μv v).IsHaarMeasure ∧ (μNv v).IsHaarMeasure) :
    ∃ c : ℂ, c ≠ 0 ∧
      ∀ (W F W' F' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
        (w f : ∀ v : HeightOneSpectrum (𝓞 ℚ), GL (Fin 2) (v.adicCompletion ℚ) → ℂ) (s : ℂ),

        (∀ g : AdelicGL2 (𝓞 ℚ) ℚ, W g = (∏ v ∈ SQ, w v (localAt ℚ v g)) * W' g) →
        (∀ g : AdelicGL2 (𝓞 ℚ) ℚ, F g = (∏ v ∈ SQ, f v (localAt ℚ v g)) * F' g) →
        (∀ v ∈ SQ, ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          W' (g * UnramifiedWhittaker.placeEmbed ℚ v x) = W' g ∧ F' (g * UnramifiedWhittaker.placeEmbed ℚ v x) = F' g) →

        (∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
          W' ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) *
              F' ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) =
            W' (g : AdelicGL2 (𝓞 ℚ) ℚ) * F' (g : AdelicGL2 (𝓞 ℚ) ℚ)) →
        (∀ k : finiteAdelicGL2Subgroup ℚ,
          (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ →
            localAt ℚ v (k : AdelicGL2 (𝓞 ℚ) ℚ) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤) →
          (∀ v ∈ SQ, localAt ℚ v (k : AdelicGL2 (𝓞 ℚ) ℚ) = 1) →
          ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
            W' (g * (k : AdelicGL2 (𝓞 ℚ) ℚ)) = W' g ∧ F' (g * (k : AdelicGL2 (𝓞 ℚ) ℚ)) = F' g) →

        (∀ v ∈ SQ, ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
          w v (UnramifiedWhittaker.unipotent x * g) * f v (UnramifiedWhittaker.unipotent x * g) = w v g * f v g) →
        Measurable (fun g : finiteAdelicGL2Subgroup ℚ => W g * F g) →

        (∀ v ∈ SQ,
          letI := localGLBorel ℚ v
          Measurable (w v) ∧ Measurable (f v)) →
        Measurable (fun g : finiteAdelicGL2Subgroup ℚ => W' (g : AdelicGL2 (𝓞 ℚ) ℚ) * F' (g : AdelicGL2 (𝓞 ℚ) ℚ)) →

        (∀ v ∈ SQ,
          letI := localGLBorel ℚ v
          haveI := borelSpace_localGLBorel ℚ v
          Integrable (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
            (f v g * w v g) *
              ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                  v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            ((μv v).withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range (μNv v)))) →
        Integrable (fun g : finiteAdelicGL2Subgroup ℚ =>
            (({g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
                  localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g : finiteAdelicGL2Subgroup ℚ => W (g : AdelicGL2 (𝓞 ℚ) ℚ))) g *
              ({g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
                  localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g : finiteAdelicGL2Subgroup ℚ => F (g : AdelicGL2 (𝓞 ℚ) ℚ))) g) *
              ((NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2))
          (μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN)) ∧
        RSCarrier.rsFinIntegral μ μN s
            ({g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
                  localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g : finiteAdelicGL2Subgroup ℚ => W (g : AdelicGL2 (𝓞 ℚ) ℚ)))
            ({g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
                  localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g : finiteAdelicGL2Subgroup ℚ => F (g : AdelicGL2 (𝓞 ℚ) ℚ))) =
          c * (W' 1 * F' 1) *
            ∏ v ∈ SQ,
              (letI := localGLBorel ℚ v
               RSCarrier.rsLocalIntegral (μv v) (unipotentGL2Hom (R := v.adicCompletion ℚ)).range (μNv v)
                (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
                  (LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                    v.adicCompletion ℚ) : ℝ))
                s (w v) (f v)) := by
  classical

  have hLCV : ∀ v ∈ SQ, ∃ m : ℝ, 0 < m ∧
      (∀ s : ℂ, letI := localGLBorel ℚ v
        Integrable (fun g : GL (Fin 2) (v.adicCompletion ℚ) => (refSlot v g * refSlot v g) *
          ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
          ((μv v).withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range (μNv v)))) ∧
      ∀ s : ℂ, Ws23FF.psiLoc v (μv v) (μNv v) s (refSlot v) (refSlot v) = m := by
    intro v hv
    letI := localGLBorel ℚ v
    haveI := borelSpace_localGLBorel ℚ v
    haveI := (hμv v hv).1
    haveI := (hμv v hv).2
    exact LanglandsTunnell.RankinSelberg.exists_pos_forall_rsLocalIntegral_indicator_unipotent_mul_localLevelOne_eq v (μv v) (μNv v)
  choose mref hmpos hmint hmval using hLCV
  obtain ⟨V, hVpos, hVint, hVval⟩ :=
    LanglandsTunnell.RankinSelberg.exists_pos_integral_indicator_forall_localAt_unipotent_mul_localLevelOne_withDensity_eq μ μN
  let mS : HeightOneSpectrum (𝓞 ℚ) → ℝ := fun v => if hv : v ∈ SQ then mref v hv else 1
  have hmSeq : ∀ v (hv : v ∈ SQ), mS v = mref v hv := fun v hv => by simp only [mS, dif_pos hv]
  have hmS0 : ∀ v ∈ SQ, ((mS v : ℝ) : ℂ) ≠ 0 := fun v hv => by
    rw [hmSeq v hv]; exact Complex.ofReal_ne_zero.2 (hmpos v hv).ne'
  refine ⟨(V : ℂ) * ∏ v ∈ SQ, ((mS v : ℝ) : ℂ)⁻¹, ?_, ?_⟩
  · exact mul_ne_zero (Complex.ofReal_ne_zero.2 hVpos.ne') (Finset.prod_ne_zero_iff.2 fun v hv => inv_ne_zero (hmS0 v hv))
  intro W F W' F' w f s hW hF hblind hN hK hloc hmeas hmeasv hmeas' hint

  obtain ⟨aT, haT⟩ : ∃ aT : Finset (HeightOneSpectrum (𝓞 ℚ)) → ∀ v : HeightOneSpectrum (𝓞 ℚ), GL (Fin 2) (v.adicCompletion ℚ) → ℂ,
      ∀ T v, aT T v = if v ∈ T then refSlot v else w v := ⟨_, fun _ _ => rfl⟩
  obtain ⟨bT, hbT⟩ : ∃ bT : Finset (HeightOneSpectrum (𝓞 ℚ)) → ∀ v : HeightOneSpectrum (𝓞 ℚ), GL (Fin 2) (v.adicCompletion ℚ) → ℂ,
      ∀ T v, bT T v = if v ∈ T then refSlot v else f v := ⟨_, fun _ _ => rfl⟩
  have haT0 : aT ∅ = w := funext fun v => by rw [haT, if_neg (Finset.notMem_empty v)]
  have hbT0 : bT ∅ = f := funext fun v => by rw [hbT, if_neg (Finset.notMem_empty v)]
  have haTins : ∀ (v₀ : HeightOneSpectrum (𝓞 ℚ)) (T : Finset (HeightOneSpectrum (𝓞 ℚ))),
      aT (insert v₀ T) = Function.update (aT T) v₀ (refSlot v₀) := by
    intro v₀ T
    funext v
    by_cases h : v = v₀
    · subst h
      rw [Function.update_self, haT, if_pos (Finset.mem_insert_self _ _)]
    · rw [Function.update_of_ne h, haT, haT]
      simp only [Finset.mem_insert, h, false_or]
  have hbTins : ∀ (v₀ : HeightOneSpectrum (𝓞 ℚ)) (T : Finset (HeightOneSpectrum (𝓞 ℚ))),
      bT (insert v₀ T) = Function.update (bT T) v₀ (refSlot v₀) := by
    intro v₀ T
    funext v
    by_cases h : v = v₀
    · subst h
      rw [Function.update_self, hbT, if_pos (Finset.mem_insert_self _ _)]
    · rw [Function.update_of_ne h, hbT, hbT]
      simp only [Finset.mem_insert, h, false_or]
  have habT : ∀ (T : Finset (HeightOneSpectrum (𝓞 ℚ))), ∀ v ∈ SQ, ∀ (x : v.adicCompletion ℚ) (y : GL (Fin 2) (v.adicCompletion ℚ)),
      aT T v (UnramifiedWhittaker.unipotent x * y) * bT T v (UnramifiedWhittaker.unipotent x * y) = aT T v y * bT T v y := by
    intro T v hv x y
    rw [haT, hbT]
    by_cases hT : v ∈ T
    · simp only [if_pos hT, refSlot_unipotent_mul]
    · simp only [if_neg hT]
      exact hloc v hv x y
  have hmeasT : ∀ (T : Finset (HeightOneSpectrum (𝓞 ℚ))), ∀ v ∈ SQ, letI := localGLBorel ℚ v
      Measurable (aT T v) ∧ Measurable (bT T v) := by
    intro T v hv
    rw [haT, hbT]
    by_cases hT : v ∈ T
    · simp only [if_pos hT]
      exact ⟨measurable_refSlot v, measurable_refSlot v⟩
    · simp only [if_neg hT]
      exact hmeasv v hv

  have key : ∀ T : Finset (HeightOneSpectrum (𝓞 ℚ)), T ⊆ SQ →
      RSCarrier.rsFinIntegral μ μN s (tensor SQ (aT ∅) W') (tensor SQ (bT ∅) F') =
        (∏ v ∈ T, Ws23FF.psiLoc v (μv v) (μNv v) s (w v) (f v) * ((mS v : ℝ) : ℂ)⁻¹) *
          RSCarrier.rsFinIntegral μ μN s (tensor SQ (aT T) W') (tensor SQ (bT T) F') ∧
      ((∫⁻ g, ‖(tensor SQ (aT T) W' g * tensor SQ (bT T) F' g) * ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2)‖ₑ ∂(μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN))) < ∞ →
        (∫⁻ g, ‖(tensor SQ (aT ∅) W' g * tensor SQ (bT ∅) F' g) * ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2)‖ₑ ∂(μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN))) < ∞) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨by rw [Finset.prod_empty, one_mul], id⟩
    | @insert v₀ T hv₀T ih =>
      intro hTS
      have hv₀ : v₀ ∈ SQ := hTS (Finset.mem_insert_self _ _)
      obtain ⟨ih1, ih2⟩ := ih (fun x hx => hTS (Finset.mem_insert_of_mem hx))
      have haTv : aT T v₀ = w v₀ := by rw [haT, if_neg hv₀T]
      have hbTv : bT T v₀ = f v₀ := by rw [hbT, if_neg hv₀T]
      obtain ⟨⟨C, hC1, hC2⟩, ⟨J, hJ1, hJ2⟩⟩ := one_place SQ hv₀ μ μN (aT T) (bT T) W' F'
        (fun x g => (hblind v₀ hv₀ x g).1) (fun x g => (hblind v₀ hv₀ x g).2) hN (habT T) (hmeasT T) hmeas'
        (refSlot v₀) (refSlot v₀) (fun x y => by rw [refSlot_unipotent_mul]) ⟨measurable_refSlot v₀, measurable_refSlot v₀⟩
        s (μv v₀) (μNv v₀) (hμv v₀ hv₀)
      rw [← haTins, ← hbTins] at hC2 hJ2
      rw [haTv, hbTv] at hC1 hJ1
      have hC2' : RSCarrier.rsFinIntegral μ μN s (tensor SQ (aT (insert v₀ T)) W') (tensor SQ (bT (insert v₀ T)) F') = C * ((mS v₀ : ℝ) : ℂ) := by
        rw [hC2, hmval v₀ hv₀ s, hmSeq v₀ hv₀]
      refine ⟨?_, ?_⟩
      · rw [ih1, Finset.prod_insert hv₀T, hC1,
          show C = RSCarrier.rsFinIntegral μ μN s (tensor SQ (aT (insert v₀ T)) W') (tensor SQ (bT (insert v₀ T)) F') * ((mS v₀ : ℝ) : ℂ)⁻¹ by
            rw [hC2', mul_assoc, mul_inv_cancel₀ (hmS0 v₀ hv₀), mul_one]]
        ring
      · intro hfin
        apply ih2
        rw [hJ1]
        rw [hJ2] at hfin

        letI := localGLBorel ℚ v₀
        haveI := borelSpace_localGLBorel ℚ v₀
        have hLref : (∫⁻ x, ‖(refSlot v₀ x * refSlot v₀ x) *
            ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det x : (v₀.adicCompletion ℚ)ˣ) :
              v₀.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)‖ₑ
          ∂((μv v₀).withDensity (HaarQuotient.density (unipotentGL2Hom (R := v₀.adicCompletion ℚ)).range (μNv v₀)))) ≠ 0 := by
          intro h0
          have hae := (lintegral_eq_zero_iff' (hmint v₀ hv₀ s).aestronglyMeasurable.aemeasurable.enorm).1 h0
          have hz : Ws23FF.psiLoc v₀ (μv v₀) (μNv v₀) s (refSlot v₀) (refSlot v₀) = 0 := by
            unfold Ws23FF.psiLoc RSCarrier.rsLocalIntegral
            refine integral_eq_zero_of_ae ?_
            filter_upwards [hae] with x hx
            simpa using hx
          rw [hmval v₀ hv₀ s] at hz
          exact (hmpos v₀ hv₀).ne' (by exact_mod_cast hz)
        have hJ : J < ∞ := ENNReal.lt_top_of_mul_ne_top_right hfin.ne hLref
        refine ENNReal.mul_lt_top ?_ hJ
        have hI := (hint v₀ hv₀).2
        rw [show (fun x : GL (Fin 2) (v₀.adicCompletion ℚ) => ‖(w v₀ x * f v₀ x) *
            ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det x : (v₀.adicCompletion ℚ)ˣ) :
              v₀.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)‖ₑ) =
            fun x => ‖(f v₀ x * w v₀ x) *
            ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det x : (v₀.adicCompletion ℚ)ˣ) :
              v₀.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)‖ₑ from funext fun x => by rw [mul_comm (w v₀ x)]]
        exact hI
  obtain ⟨kId, kFin⟩ := key SQ subset_rfl

  have haSQ : ∀ g : finiteAdelicGL2Subgroup ℚ, tensor SQ (aT SQ) W' g = tensor SQ (fun v => refSlot v) W' g := by
    intro g
    unfold tensor
    congr 1
    funext g'
    congr 1
    exact Finset.prod_congr rfl fun v hv => by rw [haT, if_pos hv]
  have hbSQ : ∀ g : finiteAdelicGL2Subgroup ℚ, tensor SQ (bT SQ) F' g = tensor SQ (fun v => refSlot v) F' g := by
    intro g
    unfold tensor
    congr 1
    funext g'
    congr 1
    exact Finset.prod_congr rfl fun v hv => by rw [hbT, if_pos hv]
  have hterm : ∀ g : finiteAdelicGL2Subgroup ℚ,
      (tensor SQ (aT SQ) W' g * tensor SQ (bT SQ) F' g) * ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2) = (W' 1 * F' 1) * cellAll.indicator (fun _ => (1 : ℂ)) g := by
    intro g
    rw [haSQ, hbSQ]
    exact terminal SQ W' F' hblind hN hK s g
  have hΨSQ : RSCarrier.rsFinIntegral μ μN s (tensor SQ (aT SQ) W') (tensor SQ (bT SQ) F') = (W' 1 * F' 1) * (V : ℂ) := by
    unfold RSCarrier.rsFinIntegral RSCarrier.rsLocalIntegral
    rw [show (fun g : finiteAdelicGL2Subgroup ℚ => (tensor SQ (aT SQ) W' g * tensor SQ (bT SQ) F' g) * ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2)) =
        fun g : finiteAdelicGL2Subgroup ℚ => (W' 1 * F' 1) * cellAll.indicator (fun _ => (1 : ℂ)) g from funext hterm, integral_const_mul]
    exact congrArg ((W' 1 * F' 1) * ·) hVval
  have hΛSQ : (∫⁻ g, ‖(tensor SQ (aT SQ) W' g * tensor SQ (bT SQ) F' g) * ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2)‖ₑ ∂(μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN))) < ∞ := by
    rw [show (fun g : finiteAdelicGL2Subgroup ℚ => ‖(tensor SQ (aT SQ) W' g * tensor SQ (bT SQ) F' g) * ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2)‖ₑ) =
        fun g : finiteAdelicGL2Subgroup ℚ => ‖W' 1 * F' 1‖ₑ * ‖cellAll.indicator (fun _ => (1 : ℂ)) g‖ₑ from funext fun g : finiteAdelicGL2Subgroup ℚ => by rw [hterm, enorm_mul],
      lintegral_const_mul' _ _ enorm_ne_top]
    exact ENNReal.mul_lt_top enorm_lt_top hVint.2

  have hWt : {g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ →
        ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
          ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
            localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g : finiteAdelicGL2Subgroup ℚ => W (g : AdelicGL2 (𝓞 ℚ) ℚ)) =
      tensor SQ (aT ∅) W' := by
    rw [haT0]
    unfold tensor
    congr 1
    funext g
    exact hW _
  have hFt : {g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ →
        ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
          ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
            localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g : finiteAdelicGL2Subgroup ℚ => F (g : AdelicGL2 (𝓞 ℚ) ℚ)) =
      tensor SQ (bT ∅) F' := by
    rw [hbT0]
    unfold tensor
    congr 1
    funext g
    exact hF _
  rw [hWt, hFt]
  refine ⟨?_, ?_⟩
  · refine ⟨((measurable_tensor_mul SQ (aT ∅) (bT ∅) W' F' (hmeasT ∅) hmeas').mul (measurable_normPow s)).aestronglyMeasurable, ?_⟩
    exact kFin hΛSQ
  · rw [kId, hΨSQ, Finset.prod_mul_distrib]
    unfold Ws23FF.psiLoc
    ring

end S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable (solution)
