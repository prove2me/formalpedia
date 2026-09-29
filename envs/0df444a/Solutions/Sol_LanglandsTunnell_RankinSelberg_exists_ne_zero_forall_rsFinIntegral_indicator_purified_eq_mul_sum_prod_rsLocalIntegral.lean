-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_ne_zero_forall_rsFinIntegral_indicator_purified_eq_mul_sum_prod_rsLocalIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/f4d10846-996a-5864-a182-551075d2f3de

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
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
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_DeltaLift

import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Theorems.Thm_LanglandsTunnell_CubicInduction_inducedLevelAt_twist_eq_of_isUnramifiedCharAt
import Theorems.Thm_NumberField_StandardAddChar_psiLocal_rat_eq_psiV
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat
import Theorems.Thm_LanglandsTunnell_CubicInduction_finite_setOf_isBadPlace_of_continuous
import Theorems.Thm_NumberField_TateGlobal_continuous_localChar
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_rsFinIntegral_indicator_purified_eq_mul_sum_prod_rsLocalIntegral
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.fnTwist3_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
p2m_open "LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction~det_upperUnipotent3 MeasureTheory"
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open UnramifiedWhittaker NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell.TateLocal

noncomputable section

namespace Ws23CutEval

open UnramifiedWhittaker NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell.TateLocal

abbrev G2 : Type := AdelicGL2 (𝓞 ℚ) ℚ
abbrev AA : Type := AdeleRing (𝓞 ℚ) ℚ

variable (v : HeightOneSpectrum (𝓞 ℚ))

theorem localAt_placeEmbed_self (x : GL (Fin 2) (v.adicCompletion ℚ)) :
    localAt ℚ v (placeEmbed ℚ v x) = x := by
  show AdelicLevel.finComponent (𝓞 ℚ) ℚ v (AdelicLevel.glFin (𝓞 ℚ) ℚ (AdelicDock.finEmbed (𝓞 ℚ) ℚ
    (AdelicDock.localEmbed (𝓞 ℚ) ℚ v x))) = x
  rw [AdelicDock.glFin_finEmbed, AdelicDock.finComponent_localEmbed_self]

theorem localAt_placeEmbed_of_ne (x : GL (Fin 2) (v.adicCompletion ℚ)) {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v) :
    localAt ℚ w (placeEmbed ℚ v x) = 1 := by
  show AdelicLevel.finComponent (𝓞 ℚ) ℚ w (AdelicLevel.glFin (𝓞 ℚ) ℚ (AdelicDock.finEmbed (𝓞 ℚ) ℚ
    (AdelicDock.localEmbed (𝓞 ℚ) ℚ v x))) = 1
  rw [AdelicDock.glFin_finEmbed, AdelicDock.finComponent_localEmbed_of_ne _ _ _ _ hw]

theorem placeEmbed_mem_fin (x : GL (Fin 2) (v.adicCompletion ℚ)) : placeEmbed ℚ v x ∈ finiteAdelicGL2Subgroup ℚ := by
  rw [mem_finiteAdelicGL2Subgroup_iff]
  exact AdelicDock.glArch_finEmbed _ _ _

theorem map_unipotentGL2 {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (a : A) :
    Matrix.GeneralLinearGroup.map f (unipotentGL2 a) = unipotentGL2 (f a) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show f ((unipotentGL2 a : Matrix (Fin 2) (Fin 2) A) i j) = (unipotentGL2 (f a) : Matrix (Fin 2) (Fin 2) B) i j
  fin_cases i <;> fin_cases j <;> simp [unipotentGL2_coe]

theorem det_unipotentGL2 {A : Type*} [CommRing A] (a : A) : Matrix.GeneralLinearGroup.det (unipotentGL2 a) = 1 :=
  Units.ext (by simp [Matrix.det_fin_two, unipotentGL2_coe])

noncomputable def uniAt (x : v.adicCompletion ℚ) : G2 :=
  unipotentGL2 (((0 : InfiniteAdeleRing ℚ), AdelicDock.splice (𝓞 ℚ) ℚ v 0 x) : AA)

theorem localAt_apply (w : HeightOneSpectrum (𝓞 ℚ)) (g : G2) (i j : Fin 2) :
    (localAt ℚ w g : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) i j = ((g : Matrix (Fin 2) (Fin 2) AA) i j).2 w := rfl

theorem localAt_eq_map (w : HeightOneSpectrum (𝓞 ℚ)) (g : G2) :
    localAt ℚ w g = Matrix.GeneralLinearGroup.map ((AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)) g := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rfl

theorem glArch_eq_map (g : G2) :
    AdelicLevel.glArch (𝓞 ℚ) ℚ g = Matrix.GeneralLinearGroup.map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ) g := rfl

theorem localAt_uniAt_self (x : v.adicCompletion ℚ) : localAt ℚ v (uniAt v x) = unipotentGL2 x := by
  rw [localAt_eq_map, uniAt, map_unipotentGL2]
  congr 1
  show (AdelicDock.splice (𝓞 ℚ) ℚ v 0 x) v = x
  exact AdelicDock.splice_apply_self _ _ _ _ _

theorem localAt_uniAt_of_ne (x : v.adicCompletion ℚ) {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v) :
    localAt ℚ w (uniAt v x) = 1 := by
  rw [localAt_eq_map, uniAt, map_unipotentGL2, ← unipotentGL2_zero]
  congr 1
  show (AdelicDock.splice (𝓞 ℚ) ℚ v 0 x) w = 0
  rw [AdelicDock.splice_apply_of_ne _ _ _ _ _ hw]
  rfl

theorem uniAt_mem_fin (x : v.adicCompletion ℚ) : uniAt v x ∈ finiteAdelicGL2Subgroup ℚ := by
  rw [mem_finiteAdelicGL2Subgroup_iff, glArch_eq_map, uniAt, map_unipotentGL2, ← unipotentGL2_zero]
  rfl

theorem uniAt_mem_unip (x : v.adicCompletion ℚ) : uniAt v x ∈ adelicUnipotent ℚ :=
  ⟨Multiplicative.ofAdd _, rfl⟩

theorem det_uniAt (x : v.adicCompletion ℚ) : Matrix.GeneralLinearGroup.det (uniAt v x) = 1 :=
  det_unipotentGL2 _

theorem eventually_mem_localLevelOne (g : G2) :
    ∀ᶠ w in Filter.cofinite, localAt ℚ w g ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ w ⊤ := by
  have h1 : ∀ i j : Fin 2, ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite,
      ((g : Matrix (Fin 2) (Fin 2) AA) i j).2 w ∈ w.adicCompletionIntegers ℚ :=
    fun i j => ((g : Matrix (Fin 2) (Fin 2) AA) i j).2.2
  have h2 : ∀ i j : Fin 2, ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite,
      (((g⁻¹ : G2) : Matrix (Fin 2) (Fin 2) AA) i j).2 w ∈ w.adicCompletionIntegers ℚ :=
    fun i j => (((g⁻¹ : G2) : Matrix (Fin 2) (Fin 2) AA) i j).2.2
  have hall := (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => h1 i j).and
    (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => h2 i j)
  refine hall.mono fun w hw => ?_
  have hint : ∀ {x : w.adicCompletion ℚ}, x ∈ w.adicCompletionIntegers ℚ → Valued.v x ≤ NumberField.AdelicLevel.idealBound (𝓞 ℚ) (⊤ : Ideal (𝓞 ℚ)) w :=
    fun hx => by rw [NumberField.AdelicLevel.idealBound_top]; exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hx
  rw [AdelicDock.mem_localLevelOne_iff, ← map_inv]
  exact ⟨⟨fun i j => hw.1 i j, hint (hw.1 1 0), hint (sub_mem (hw.1 1 1) (one_mem _))⟩,
    ⟨fun i j => hw.2 i j, hint (hw.2 1 0), hint (sub_mem (hw.2 1 1) (one_mem _))⟩⟩

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

theorem mul_comm_of_mem_range_unipotentGL2Hom {R : Type*} [CommRing R] {a b : GL (Fin 2) R}
    (ha : a ∈ (unipotentGL2Hom (R := R)).range) (hb : b ∈ (unipotentGL2Hom (R := R)).range) : a * b = b * a := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  rw [← map_mul, ← map_mul, mul_comm]

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

theorem localAt_mem_range_of_mem_adelicUnipotent (p : HeightOneSpectrum (𝓞 ℚ)) {g : AdelicGL2 (𝓞 ℚ) ℚ}
    (hg : g ∈ adelicUnipotent ℚ) :
    localAt ℚ p g ∈ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range := by
  rw [mem_range_unipotentGL2Hom_iff]
  rw [show adelicUnipotent ℚ = (unipotentGL2Hom (R := AdeleRing (𝓞 ℚ) ℚ)).range from rfl,
    mem_range_unipotentGL2Hom_iff] at hg
  have h : ∀ i j : Fin 2, (localAt ℚ p g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i j =
      (finAdeleEval (𝓞 ℚ) ℚ p) ((adeleFin (𝓞 ℚ) ℚ) ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j)) :=
    fun i j => rfl
  simp only [h, hg.1, hg.2.1, hg.2.2, map_one, map_zero, and_self]

theorem isLocalLevelOne_top_of_integral (v : HeightOneSpectrum (𝓞 ℚ)) (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hm : ∀ i j, m i j ∈ v.adicCompletionIntegers ℚ) : AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ v ⊤ m := by
  refine ⟨hm, ?_, ?_⟩
  · rw [NumberField.AdelicLevel.idealBound_top]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hm 1 0)
  · rw [NumberField.AdelicLevel.idealBound_top]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1
      ((v.adicCompletionIntegers ℚ).sub_mem (hm 1 1) (v.adicCompletionIntegers ℚ).one_mem)

theorem mem_levelOne_top_of_forall_localAt (g : G2)
    (h : ∀ w : HeightOneSpectrum (𝓞 ℚ), localAt ℚ w g ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ w ⊤) :
    g ∈ levelOne (𝓞 ℚ) ℚ ⊤ := by
  rw [NumberField.AdelicLevel.mem_levelOne_iff, NumberField.AdelicLevel.mem_finiteLevelOne_iff]
  have hint : ∀ i j, ((glFin (𝓞 ℚ) ℚ g : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ := fun i j w => by
    have := ((AdelicDock.mem_localLevelOne_iff (𝓞 ℚ) ℚ w _).1 (h w)).1.integral i j
    rw [localAt_apply] at this
    rw [glFin_apply]
    exact this
  have hint' : ∀ i j, (((glFin (𝓞 ℚ) ℚ g)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ := fun i j w => by
    have := ((AdelicDock.mem_localLevelOne_iff (𝓞 ℚ) ℚ w _).1 (h w)).2.integral i j
    rw [← map_inv, localAt_apply] at this
    rw [← map_inv, glFin_apply]
    exact this
  have key : ∀ m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ), (∀ i j, m i j ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ) →
      NumberField.AdelicLevel.IsLevelOneMatrix (𝓞 ℚ) ℚ ⊤ m := fun m hm =>
    { integral := hm
      lowerLeft := fun w => (NumberField.AdelicLevel.idealBound_top w).symm ▸
        NumberField.AdelicLevel.valued_apply_le_one (hm 1 0) w
      lowerRight := fun w => (NumberField.AdelicLevel.idealBound_top w).symm ▸
        NumberField.AdelicLevel.valued_apply_le_one
          (NumberField.AdelicLevel.sub_mem_integralFiniteAdeles (hm 1 1)
            NumberField.AdelicLevel.one_mem_integralFiniteAdeles) w }
  exact ⟨key _ hint, key _ hint'⟩

theorem localAt_mem_localLevelOne_of_mem_levelOne_top {g : G2} (hg : g ∈ levelOne (𝓞 ℚ) ℚ ⊤)
    (w : HeightOneSpectrum (𝓞 ℚ)) : localAt ℚ w g ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ w ⊤ := by
  rw [NumberField.AdelicLevel.mem_levelOne_iff, NumberField.AdelicLevel.mem_finiteLevelOne_iff] at hg
  rw [AdelicDock.mem_localLevelOne_iff, ← map_inv]
  refine ⟨isLocalLevelOne_top_of_integral w _ fun i j => ?_,
    isLocalLevelOne_top_of_integral w _ fun i j => ?_⟩
  · have := hg.1.integral i j w
    rw [glFin_apply] at this
    rw [localAt_apply]
    exact this
  · have := hg.2.integral i j w
    rw [← map_inv, glFin_apply] at this
    rw [localAt_apply]
    exact this

section TabFsec
open IsDedekindDomain NumberField Matrix AutomorphicForm
p2m_open "LanglandsTunnell LanglandsTunnell.CubicInduction~det_upperUnipotent3"
open NumberField.AdelicLevel AdelicDock UnramifiedWhittaker
namespace TabF

theorem glMap_apply {A B : Type*} [CommRing A] [CommRing B] {n : Type*} [Fintype n] [DecidableEq n]
    (φ : A →+* B) (g : GL n A) (i j : n) :
    ((Matrix.GeneralLinearGroup.map φ g : GL n B) : Matrix n n B) i j = φ ((g : Matrix n n A) i j) := rfl

theorem map_iotaGL {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (g : GL (Fin 2) A) :
    Matrix.GeneralLinearGroup.map φ (iotaGL g) = iotaGL (Matrix.GeneralLinearGroup.map φ g) := by
  ext i j
  rw [glMap_apply, coe_iotaGL, coe_iotaGL]
  fin_cases i <;> fin_cases j <;> simp [embedMat2]

abbrev G2 : Type := AdelicGL2 (𝓞 ℚ) ℚ

theorem componentAt3_iota (v : HeightOneSpectrum (𝓞 ℚ)) (g : G2) :
    componentAt3 (𝓞 ℚ) ℚ v (iota (𝓞 ℚ) ℚ g) = iotaGL (finComponent (𝓞 ℚ) ℚ v (glFin (𝓞 ℚ) ℚ g)) := by
  have h : finComponent (𝓞 ℚ) ℚ v (glFin (𝓞 ℚ) ℚ g) =
      Matrix.GeneralLinearGroup.map ((finAdeleEval (𝓞 ℚ) ℚ v).comp (adeleFin (𝓞 ℚ) ℚ)) g := by
    ext i j
    rfl
  rw [h]
  exact map_iotaGL _ g

theorem coe_finFactor (g : G2) :
    (RSCarrier.finFactor g : G2) =
      (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (ratArchGL2 g))⁻¹ * g := rfl

theorem glFin_archRealGLAt (m : GL (Fin 2) ℝ) :
    glFin (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) m) = 1 :=
  glFin_adelicArchGLIncl ℚ _

theorem glFin_finFactor (g : G2) : glFin (𝓞 ℚ) ℚ (RSCarrier.finFactor g : G2) = glFin (𝓞 ℚ) ℚ g := by
  rw [coe_finFactor, map_mul, map_inv, glFin_archRealGLAt, inv_one, one_mul]

theorem iotaGL_mem_localMaximalCompact3 (v : HeightOneSpectrum (𝓞 ℚ)) {x : GL (Fin 2) (v.adicCompletion ℚ)}
    (h1 : ∀ i j, Valued.v ((x : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1)
    (h2 : ∀ i j, Valued.v (((x⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1) :
    iotaGL x ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [coe_iotaGL]
    fin_cases i <;> fin_cases j <;> simp [embedMat2, h1]
  · have h2' : ∀ i j, Valued.v (((x : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))⁻¹ i j) ≤ 1 := fun i j => by
      rw [← Matrix.coe_units_inv]; exact h2 i j
    rw [← map_inv, coe_iotaGL]
    fin_cases i <;> fin_cases j <;> simp [embedMat2, h2']

theorem eventually_valued_le_one (a : FiniteAdeleRing (𝓞 ℚ) ℚ) :
    ∀ᶠ v in Filter.cofinite, Valued.v (a v) ≤ 1 := by
  have h := RestrictedProduct.eventually (fun v : HeightOneSpectrum (𝓞 ℚ) => v.adicCompletion ℚ)
    (fun v => (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))) a
  filter_upwards [h] with v hv
  exact hv

theorem eventually_componentAt3_iota_mem (g : G2) :
    ∀ᶠ v in Filter.cofinite, componentAt3 (𝓞 ℚ) ℚ v (iota (𝓞 ℚ) ℚ g) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  have hA : ∀ᶠ v in Filter.cofinite, ∀ i j : Fin 2,
      Valued.v ((((g : G2) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 v) ≤ 1 :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => eventually_valued_le_one _
  have hB : ∀ᶠ v in Filter.cofinite, ∀ i j : Fin 2,
      Valued.v ((((g⁻¹ : G2) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 v) ≤ 1 :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => eventually_valued_le_one _
  filter_upwards [hA, hB] with v hA hB
  rw [componentAt3_iota]
  refine iotaGL_mem_localMaximalCompact3 v (fun i j => hA i j) (fun i j => ?_)
  rw [← map_inv, ← map_inv]
  exact hB i j

end TabF
end TabFsec

section PsiSec
p2m_open "IsDedekindDomain NumberField LanglandsTunnell.CubicInduction~det_upperUnipotent3"

theorem psiLoc_psiQ_eq_psiV_tB (v : HeightOneSpectrum (𝓞 ℚ)) :
    LanglandsTunnell.CubicInduction.psiLoc NumberField.StandardAddChar.psiQ v = NumberField.StandardAddChar.psiV v := by
  classical
  refine DFunLike.ext _ _ fun x => ?_
  show NumberField.StandardAddChar.psiQ (NumberField.StandardAddChar.adeleSingleAt ℚ v x) = _
  rw [show NumberField.StandardAddChar.adeleSingleAt ℚ v x =
      ((0 : InfiniteAdeleRing ℚ), NumberField.StandardAddChar.finAdeleSingleAt ℚ v x) from rfl,
    NumberField.StandardAddChar.psiQ_apply]
  simp only
  rw [AddChar.map_zero_eq_one, one_mul, NumberField.StandardAddChar.psiFin_apply]
  rw [finprod_eq_single (fun w => NumberField.StandardAddChar.psiV w (NumberField.StandardAddChar.finAdeleSingleAt ℚ v x w)) v]
  · rw [NumberField.StandardAddChar.finAdeleSingleAt_apply_self]
  · intro w hw
    rw [NumberField.StandardAddChar.finAdeleSingleAt_apply_of_ne ℚ v x hw]
    exact AddChar.map_zero_eq_one _

theorem psiLoc_psiQ_eq_psiLocal_tB (v : HeightOneSpectrum (𝓞 ℚ)) :
    LanglandsTunnell.CubicInduction.psiLoc NumberField.StandardAddChar.psiQ v = NumberField.StandardAddChar.psiLocal ℚ v := by
  rw [psiLoc_psiQ_eq_psiV_tB, NumberField.StandardAddChar.psiLocal_rat_eq_psiV]

theorem supply_psi_tB (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (ϖ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p.adicCompletionIntegers ℚ)
    (hπ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
      algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p) ≠ 0)
    (hϖ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
      Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) = WithZero.exp (-1 : ℤ)) :
    (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → ∀ r : p.adicCompletionIntegers ℚ,
      LanglandsTunnell.CubicInduction.psiLoc NumberField.StandardAddChar.psiQ p
        (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) r) = 1) ∧
    (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → ∃ r : p.adicCompletionIntegers ℚ,
      LanglandsTunnell.CubicInduction.psiLoc NumberField.StandardAddChar.psiQ p
        (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) r /
          algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) ≠ 1) := by

  have key : ∀ p : HeightOneSpectrum (𝓞 ℚ),
      (∀ x : p.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (0 : ℤ) → NumberField.StandardAddChar.psiLocal ℚ p x = 1) ∧
      ∃ x : p.adicCompletion ℚ, Valued.v x ≤ WithZero.exp ((0 : ℤ) + 1) ∧
        NumberField.StandardAddChar.psiLocal ℚ p x ≠ 1 := by
    intro p
    have h := LanglandsTunnell.TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel ℚ p
      (NumberField.StandardAddChar.psiLocal ℚ p)
      ⟨0, fun x hx => by
        rw [NumberField.StandardAddChar.psiLocal_rat_eq_psiV]
        exact NumberField.StandardAddChar.psiV_eq_one_of_mem_integers p
          ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (by simpa using hx))⟩
      (LanglandsTunnell.TateLocal.psiLocal_ne_one ℚ p)
    rwa [LanglandsTunnell.TateLocal.addCharLevel_psiLocal_rat] at h
  refine ⟨fun p _ r => ?_, fun p hp => ?_⟩
  · rw [psiLoc_psiQ_eq_psiLocal_tB]
    refine (key p).1 _ ?_
    rw [WithZero.exp_zero]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 r.2
  · obtain ⟨x, hx, hne⟩ := (key p).2
    have hπ' := hπ p hp
    refine ⟨⟨x * algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p), ?_⟩, ?_⟩
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, hϖ p hp]
      calc Valued.v x * WithZero.exp (-1 : ℤ) ≤ WithZero.exp ((0 : ℤ) + 1) * WithZero.exp (-1 : ℤ) :=
            mul_le_mul_left hx _
        _ = 1 := by rw [← WithZero.exp_add]; norm_num
    · rw [psiLoc_psiQ_eq_psiLocal_tB]
      show NumberField.StandardAddChar.psiLocal ℚ p
        (x * algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p) /
          algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) ≠ 1
      rwa [mul_div_cancel_right₀ _ hπ']

theorem psiLoc_apply_of_inv_eq {ψ' φ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (h : ψ'⁻¹ = φ)
    (p : HeightOneSpectrum (𝓞 ℚ)) (y : p.adicCompletion ℚ) : psiLoc ψ' p y = psiLoc φ p (-y) := by
  have hψ : ψ' = φ⁻¹ := by rw [← h, inv_inv]
  rw [hψ]
  show φ⁻¹ (NumberField.StandardAddChar.adeleSingleAt ℚ p y) = φ (NumberField.StandardAddChar.adeleSingleAt ℚ p (-y))
  rw [AddChar.inv_apply, (NumberField.StandardAddChar.adeleSingleAt ℚ p).map_neg]

theorem exists_psiLoc_div_ne_one_of_inv_eq {ψ' φ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (h : ψ'⁻¹ = φ)
    (p : HeightOneSpectrum (𝓞 ℚ)) (ϖ' : p.adicCompletion ℚ)
    (hw : ∃ r : p.adicCompletionIntegers ℚ,
      psiLoc φ p (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) r / ϖ') ≠ 1) :
    ∃ r : p.adicCompletionIntegers ℚ,
      psiLoc ψ' p (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) r / ϖ') ≠ 1 := by
  obtain ⟨r, hr⟩ := hw
  refine ⟨-r, ?_⟩
  rwa [map_neg, neg_div, psiLoc_apply_of_inv_eq h, neg_neg]

end PsiSec

section AdelicGen

open IsDedekindDomain NumberField Matrix AutomorphicForm
p2m_open "LanglandsTunnell LanglandsTunnell.CubicInduction~det_upperUnipotent3 LanglandsTunnell.RankinSelberg"
open NumberField.AdelicLevel AdelicDock UnramifiedWhittaker
open Ws23CutEval.TabF

theorem iotaGL_mem_congruenceK1 (p : HeightOneSpectrum (𝓞 ℚ)) (c : ℕ) {x : GL (Fin 2) (p.adicCompletion ℚ)}
    (h1 : ∀ i j, Valued.v ((x : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i j) ≤ 1)
    (h2 : ∀ i j, Valued.v (((x⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) :
      Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i j) ≤ 1) :
    iotaGL x ∈ congruenceK1 (𝓞 ℚ) ℚ p c :=
  ⟨iotaGL_mem_localMaximalCompact3 p h1 h2, by simp [embedMat2], by simp [embedMat2], by simp [embedMat2]⟩

def finWgen (Wl : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ) (kf : AdelicGL 3 (𝓞 ℚ) ℚ) (g : G2) : ℂ :=
  ∏ᶠ v, Wl v (componentAt3 (𝓞 ℚ) ℚ v (iota (𝓞 ℚ) ℚ g) * componentAt3 (𝓞 ℚ) ℚ v kf)

theorem finWgen_eq_of_glFin_eq (Wl : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ) (kf : AdelicGL 3 (𝓞 ℚ) ℚ)
    {g g' : G2} (h : glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g') : finWgen Wl kf g = finWgen Wl kf g' := by
  unfold finWgen
  simp_rw [componentAt3_iota, h]

theorem finWgen_finFactor (Wl : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ) (kf : AdelicGL 3 (𝓞 ℚ) ℚ) (g : G2) :
    finWgen Wl kf (RSCarrier.finFactor g : G2) = finWgen Wl kf g :=
  finWgen_eq_of_glFin_eq Wl kf (glFin_finFactor g)

theorem finWgen_mul_placeEmbed_of_levelInvariant (Wl : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ)
    {kf : AdelicGL 3 (𝓞 ℚ) ℚ} {q : HeightOneSpectrum (𝓞 ℚ)} (c : ℕ)
    (hK1 : ∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ q c, ∀ y : LocalGL3 q, Wl q (y * k) = Wl q y)
    (hkq : componentAt3 (𝓞 ℚ) ℚ q kf = 1)
    (x : GL (Fin 2) (q.adicCompletion ℚ)) (hx : x ∈ localLevelOne (𝓞 ℚ) ℚ q ⊤) (g : G2) :
    finWgen Wl kf (g * placeEmbed ℚ q x) = finWgen Wl kf g := by
  have hx' := (mem_localLevelOne_iff (𝓞 ℚ) ℚ q x).1 hx
  have hfin : glFin (𝓞 ℚ) ℚ (placeEmbed ℚ q x) = localEmbed (𝓞 ℚ) ℚ q x := glFin_finEmbed ..
  unfold finWgen
  refine finprod_congr fun v => ?_
  simp only [map_mul]
  rw [componentAt3_iota v (placeEmbed ℚ q x), hfin]
  by_cases hv : v = q
  · subst hv
    rw [finComponent_localEmbed_self, hkq, mul_one, mul_one]
    exact hK1 _ (iotaGL_mem_congruenceK1 _ _ (fun i j => hx'.1.integral i j) (fun i j => hx'.2.integral i j)) _
  · rw [finComponent_localEmbed_of_ne (𝓞 ℚ) ℚ q x hv, map_one, mul_one]

theorem finWgen_mul_placeEmbed_of_localAt_eq_one (Wl : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ)
    {kf : AdelicGL 3 (𝓞 ℚ) ℚ} {q : HeightOneSpectrum (𝓞 ℚ)} (h1 : Wl q 1 = 1) (hkq : componentAt3 (𝓞 ℚ) ℚ q kf = 1)
    (hfin : ∀ g : G2,
      (Function.mulSupport fun v => Wl v (componentAt3 (𝓞 ℚ) ℚ v (iota (𝓞 ℚ) ℚ g) * componentAt3 (𝓞 ℚ) ℚ v kf)).Finite)
    (T : GL (Fin 2) (q.adicCompletion ℚ)) (g : G2) (hg : localAt ℚ q g = 1) :
    finWgen Wl kf (g * placeEmbed ℚ q T) = finWgen Wl kf g * Wl q (iotaGL T) := by
  classical
  have hfinE : glFin (𝓞 ℚ) ℚ (placeEmbed ℚ q T) = localEmbed (𝓞 ℚ) ℚ q T := glFin_finEmbed ..
  have hgq : finComponent (𝓞 ℚ) ℚ q (glFin (𝓞 ℚ) ℚ g) = 1 := hg
  have hA : componentAt3 (𝓞 ℚ) ℚ q (iota (𝓞 ℚ) ℚ g) * componentAt3 (𝓞 ℚ) ℚ q kf = 1 := by
    rw [componentAt3_iota, hgq, map_one, hkq, one_mul]
  have hB : componentAt3 (𝓞 ℚ) ℚ q (iota (𝓞 ℚ) ℚ (g * placeEmbed ℚ q T)) * componentAt3 (𝓞 ℚ) ℚ q kf = iotaGL T := by
    rw [map_mul, map_mul, componentAt3_iota q g, hgq, map_one, one_mul, componentAt3_iota, hfinE,
      finComponent_localEmbed_self, hkq, mul_one]
  have hpt : ∀ v, Wl v (componentAt3 (𝓞 ℚ) ℚ v (iota (𝓞 ℚ) ℚ (g * placeEmbed ℚ q T)) * componentAt3 (𝓞 ℚ) ℚ v kf) =
      Wl v (componentAt3 (𝓞 ℚ) ℚ v (iota (𝓞 ℚ) ℚ g) * componentAt3 (𝓞 ℚ) ℚ v kf) *
        (if v = q then Wl q (iotaGL T) else 1) := by
    intro v
    by_cases hv : v = q
    · subst hv
      rw [if_pos rfl, hA, hB, h1, one_mul]
    · rw [if_neg hv, mul_one]
      simp only [map_mul]
      rw [componentAt3_iota v (placeEmbed ℚ q T), hfinE, finComponent_localEmbed_of_ne (𝓞 ℚ) ℚ q T hv, map_one,
        mul_one]
  have hδ : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 ℚ) =>
      (if v = q then Wl q (iotaGL T) else (1 : ℂ))).Finite :=
    (Set.finite_singleton q).subset fun v hv => by
      by_contra h
      exact hv (if_neg h)
  unfold finWgen
  simp_rw [hpt]
  rw [finprod_mul_distrib (hfin g) hδ,
    finprod_eq_single (fun v : HeightOneSpectrum (𝓞 ℚ) => if v = q then Wl q (iotaGL T) else (1 : ℂ))
      q (fun v hv => if_neg hv), if_pos rfl]

theorem finite_mulSupport_finWgen (Wl : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ)
    {kf : AdelicGL 3 (𝓞 ℚ) ℚ} (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hkS : ∀ v, v ∉ S → componentAt3 (𝓞 ℚ) ℚ v kf = 1)
    (h1 : ∀ v, v ∉ S → ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v, Wl v k = 1) (g : G2) :
    (Function.mulSupport fun v => Wl v (componentAt3 (𝓞 ℚ) ℚ v (iota (𝓞 ℚ) ℚ g) * componentAt3 (𝓞 ℚ) ℚ v kf)).Finite := by
  classical
  have hfin := Filter.eventually_cofinite.1 (eventually_componentAt3_iota_mem g)
  refine (Finset.finite_toSet (S ∪ hfin.toFinset)).subset fun v hv => ?_
  by_contra hvT
  apply hv
  have hvS : v ∉ S := fun h => hvT (Finset.mem_union_left _ h)
  have hvK : componentAt3 (𝓞 ℚ) ℚ v (iota (𝓞 ℚ) ℚ g) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
    by_contra hk
    exact hvT (Finset.mem_union_right _ (hfin.mem_toFinset.2 hk))
  show Wl v (componentAt3 (𝓞 ℚ) ℚ v (iota (𝓞 ℚ) ℚ g) * componentAt3 (𝓞 ℚ) ℚ v kf) = 1
  rw [hkS v hvS, mul_one]
  exact h1 v hvS _ hvK

end AdelicGen

section LocalTwist

open IsDedekindDomain NumberField Matrix
p2m_open "LanglandsTunnell.CubicInduction~det_upperUnipotent3"

theorem det_upperUnipotent3 {A : Type*} [CommRing A] (x y z : A) :
    Matrix.GeneralLinearGroup.det (upperUnipotent3 x y z) = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, upperUnipotent3_coe, Units.val_one, Matrix.det_fin_three]
  simp

theorem isGL3PsiWhittakerFn_twist_det (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (χv : (v.adicCompletion ℚ)ˣ →* ℂˣ) (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψv W) :
    IsGL3PsiWhittakerFn ψv (fun y : LocalGL3 v => ((χv (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) * W y) := by
  intro x y z g
  show ((χv (Matrix.GeneralLinearGroup.det (upperUnipotent3 x y z * g)) : ℂˣ) : ℂ) * W (upperUnipotent3 x y z * g) =
    ψv (x + y) * (((χv (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * W g)
  rw [map_mul, det_upperUnipotent3, one_mul, hW]
  ring

theorem mem_congruenceK1_zero_of_mem (v : HeightOneSpectrum (𝓞 ℚ)) {k : LocalGL3 v}
    (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) : k ∈ congruenceK1 (𝓞 ℚ) ℚ v 0 := by
  refine ⟨hk, ?_, ?_, ?_⟩
  · simpa using hk.1 2 0
  · simpa using hk.1 2 1
  · have h1 : Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 - 1) ≤ 1 :=
      Valued.v.map_sub_le (hk.1 2 2) (by rw [Valuation.map_one])
    simpa using h1

end LocalTwist

section WtwSec
open IsDedekindDomain NumberField Matrix AutomorphicForm
p2m_open "LanglandsTunnell LanglandsTunnell.CubicInduction~det_upperUnipotent3 LanglandsTunnell.RankinSelberg"
open NumberField.AdelicLevel AdelicDock UnramifiedWhittaker Ws23CutEval.TabF
open scoped Classical in

def Wtw (p : HeightOneSpectrum (𝓞 ℚ)) (χA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (WF : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ) : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ :=
  fun v y => if v = p then (1 : ℂ) else
    ((NumberField.TateGlobal.localChar χA v (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) * WF v y

open scoped Classical in
theorem Wtw_of_ne {p q : HeightOneSpectrum (𝓞 ℚ)} (χA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (WF : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ) (h : q ≠ p) :
    Wtw p χA WF q = fun y : LocalGL3 q =>
      ((NumberField.TateGlobal.localChar χA q (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) * WF q y := by
  funext y
  simp [Wtw, h]

theorem localAt_finFactor' (p : HeightOneSpectrum (𝓞 ℚ)) (g : G2) :
    localAt ℚ p (RSCarrier.finFactor g : G2) = localAt ℚ p g := by
  show finComponent (𝓞 ℚ) ℚ p (glFin (𝓞 ℚ) ℚ (RSCarrier.finFactor g : G2)) = finComponent (𝓞 ℚ) ℚ p (glFin (𝓞 ℚ) ℚ g)
  rw [glFin_finFactor]

end WtwSec

section KitE

open IsDedekindDomain NumberField Matrix AutomorphicForm
p2m_open "LanglandsTunnell LanglandsTunnell.CubicInduction~det_upperUnipotent3 LanglandsTunnell.RankinSelberg"
open NumberField.AdelicLevel AdelicDock UnramifiedWhittaker

theorem ext_of_glArch_of_localAt {g h : G2} (ha : glArch (𝓞 ℚ) ℚ g = glArch (𝓞 ℚ) ℚ h)
    (hl : ∀ v : HeightOneSpectrum (𝓞 ℚ), localAt ℚ v g = localAt ℚ v h) : g = h := by
  apply Units.ext
  ext i j
  refine Prod.ext ?_ ?_
  · have := congrFun (congrFun (congrArg (fun M : GL (Fin 2) (InfiniteAdeleRing ℚ) =>
      (M : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ))) ha) i) j
    rw [glArch_apply, glArch_apply] at this
    exact this
  · refine RestrictedProduct.ext _ _ fun v => ?_
    have := congrFun (congrFun (congrArg (fun M : GL (Fin 2) (v.adicCompletion ℚ) =>
      (M : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) (hl v)) i) j
    rw [localAt_apply, localAt_apply] at this
    exact this

theorem glArch_placeEmbed (v : HeightOneSpectrum (𝓞 ℚ)) (x : GL (Fin 2) (v.adicCompletion ℚ)) :
    glArch (𝓞 ℚ) ℚ (placeEmbed ℚ v x) = 1 :=
  AdelicDock.glArch_finEmbed _ _ _

theorem inv_mul_placeEmbed_mul (v : HeightOneSpectrum (𝓞 ℚ)) (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : G2) :
    g⁻¹ * placeEmbed ℚ v x * g = placeEmbed ℚ v ((localAt ℚ v g)⁻¹ * x * localAt ℚ v g) := by
  refine ext_of_glArch_of_localAt ?_ fun u => ?_
  · rw [map_mul, map_mul, map_inv, glArch_placeEmbed, glArch_placeEmbed, mul_one, inv_mul_cancel]
  · by_cases hu : u = v
    · subst hu
      rw [map_mul, map_mul, map_inv, localAt_placeEmbed_self, localAt_placeEmbed_self]
    · rw [map_mul, map_mul, map_inv, localAt_placeEmbed_of_ne v _ hu, localAt_placeEmbed_of_ne v _ hu, mul_one,
        inv_mul_cancel]

theorem left_blind_of_right_blind {W : G2 → ℂ} {v : HeightOneSpectrum (𝓞 ℚ)}
    (h : ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : G2), W (g * placeEmbed ℚ v x) = W g)
    (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : G2) : W (placeEmbed ℚ v x * g) = W g := by
  have e : placeEmbed ℚ v x * g = g * (g⁻¹ * placeEmbed ℚ v x * g) := by group
  rw [e, inv_mul_placeEmbed_mul, h]

theorem apply_mul_eq_of_blind {W : G2 → ℂ} (T : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (h : ∀ v ∈ T, ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : G2), W (g * placeEmbed ℚ v x) = W g) :
    ∀ (e : G2), glArch (𝓞 ℚ) ℚ e = 1 → (∀ u, u ∉ T → localAt ℚ u e = 1) →
      ∀ g : G2, W (g * e) = W g ∧ W (e * g) = W g := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro e he hl g
    have : e = 1 := ext_of_glArch_of_localAt (by rw [he, map_one]) fun u => by
      rw [hl u (Finset.notMem_empty u), map_one]
    rw [this, mul_one, one_mul]
    exact ⟨rfl, rfl⟩
  | @insert v T hvT ih =>
    intro e he hl g

    set e' : G2 := e * placeEmbed ℚ v (localAt ℚ v e)⁻¹ with he'
    have he'a : glArch (𝓞 ℚ) ℚ e' = 1 := by rw [he', map_mul, he, glArch_placeEmbed, one_mul]
    have he'l : ∀ u, u ∉ T → localAt ℚ u e' = 1 := by
      intro u hu
      by_cases huv : u = v
      · subst huv; rw [he', map_mul, localAt_placeEmbed_self, mul_inv_cancel]
      · rw [he', map_mul, localAt_placeEmbed_of_ne v _ huv, mul_one]
        exact hl u (fun hh => (Finset.mem_insert.1 hh).elim huv hu)
    have hdec : e = e' * placeEmbed ℚ v (localAt ℚ v e) := by
      rw [he', mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
    have ih' := ih (fun u hu => h u (Finset.mem_insert_of_mem hu)) e' he'a he'l
    have hv := h v (Finset.mem_insert_self v T)
    refine ⟨?_, ?_⟩
    · rw [hdec, ← mul_assoc, hv, (ih' g).1]
    · rw [hdec, mul_assoc, (ih' _).2, left_blind_of_right_blind hv]

theorem unipotent_eq_unipotentGL2 {A : Type*} [Field A] (x : A) :
    UnramifiedWhittaker.unipotent x = unipotentGL2 x :=
  Units.ext rfl

theorem iotaGL_unipotentGL2 {A : Type*} [CommRing A] (x : A) :
    iotaGL (unipotentGL2 x) = upperUnipotent3 x 0 0 := by
  apply Units.ext
  ext i j
  rw [coe_iotaGL, unipotentGL2_coe, upperUnipotent3_coe]
  fin_cases i <;> fin_cases j <;> simp [embedMat2]

theorem localAt_unipotentGL2 (v : HeightOneSpectrum (𝓞 ℚ)) (t : AA) :
    localAt ℚ v (unipotentGL2 t) = unipotentGL2 (t.2 v) := by
  rw [localAt_eq_map, map_unipotentGL2]
  rfl

theorem glArch_unipotentGL2 (t : AA) : glArch (𝓞 ℚ) ℚ (unipotentGL2 t) = unipotentGL2 t.1 := by
  rw [glArch_eq_map, map_unipotentGL2]
  rfl

theorem fst_eq_zero_of_unipotentGL2_mem_fin {t : AA} (h : unipotentGL2 t ∈ finiteAdelicGL2Subgroup ℚ) : t.1 = 0 := by
  rw [mem_finiteAdelicGL2Subgroup_iff, glArch_unipotentGL2] at h
  have := congrFun (congrFun (congrArg (fun M : GL (Fin 2) (InfiniteAdeleRing ℚ) =>
    (M : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ))) h) 0) 1
  simpa [unipotentGL2_coe] using this

theorem psiLoc_eq_psiLocal_neg {ψ : AddChar AA ℂ} (hψQ : ψ⁻¹ = NumberField.StandardAddChar.psiQ)
    (u : HeightOneSpectrum (𝓞 ℚ)) (y : u.adicCompletion ℚ) :
    psiLoc ψ u y = NumberField.StandardAddChar.psiLocal ℚ u (-y) := by
  rw [psiLoc_apply_of_inv_eq hψQ, psiLoc_psiQ_eq_psiLocal_tB]

theorem psiLoc_eq_one_of_mem_integers {ψ : AddChar AA ℂ} (hψQ : ψ⁻¹ = NumberField.StandardAddChar.psiQ)
    (u : HeightOneSpectrum (𝓞 ℚ)) {y : u.adicCompletion ℚ} (hy : y ∈ u.adicCompletionIntegers ℚ) :
    psiLoc ψ u y = 1 := by
  rw [psiLoc_apply_of_inv_eq hψQ, psiLoc_psiQ_eq_psiV_tB]
  exact NumberField.StandardAddChar.psiV_eq_one_of_mem_integers u (neg_mem hy)

theorem apply_eq_finprod_psiLoc {ψ : AddChar AA ℂ} (hψQ : ψ⁻¹ = NumberField.StandardAddChar.psiQ)
    (t : AA) (ht : t.1 = 0) : ψ t = ∏ᶠ u : HeightOneSpectrum (𝓞 ℚ), psiLoc ψ u (t.2 u) := by
  have hψ : ψ = NumberField.StandardAddChar.psiQ⁻¹ := by rw [← hψQ, inv_inv]
  conv_lhs => rw [hψ, AddChar.inv_apply, NumberField.StandardAddChar.psiQ_apply]
  have h1 : (-t).1 = -t.1 := rfl
  have h2 : (-t).2 = -t.2 := rfl
  rw [h1, h2, ht, neg_zero, AddChar.map_zero_eq_one, one_mul, NumberField.StandardAddChar.psiFin_apply]
  refine finprod_congr fun u => ?_
  rw [psiLoc_apply_of_inv_eq hψQ, psiLoc_psiQ_eq_psiV_tB]
  rfl

theorem continuous_of_mul_invariant {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) (f : G → ℂ) (hf : ∀ k ∈ U, ∀ g, f (g * k) = f g) :
    Continuous f := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  have hev : f =ᶠ[nhds g] fun _ => f g := by
    have ho : IsOpen ((fun k => g * k) '' (U : Set G)) := (isOpenMap_mul_left g) _ hU
    have hg : g ∈ (fun k => g * k) '' (U : Set G) := ⟨1, U.one_mem, mul_one g⟩
    refine Filter.eventually_of_mem (ho.mem_nhds hg) ?_
    rintro _ ⟨k, hk, rfl⟩
    exact hf k hk g
  exact (continuousAt_const : ContinuousAt (fun _ : G => f g) g).congr hev.symm
end KitE

section SecB

open scoped Classical

open IsDedekindDomain NumberField Matrix AutomorphicForm
p2m_open "LanglandsTunnell LanglandsTunnell.CubicInduction~det_upperUnipotent3 LanglandsTunnell.RankinSelberg"
open NumberField.AdelicLevel AdelicDock UnramifiedWhittaker Ws23CutEval.TabF

theorem ratArchGL2_of_mem {g : G2} (hg : g ∈ finiteAdelicGL2Subgroup ℚ) : ratArchGL2 g = 1 := by
  unfold LanglandsTunnell.ratArchGL2
  rw [(mem_finiteAdelicGL2Subgroup_iff ℚ g).1 hg, map_one, map_one]

theorem finFactor_coe (gf : finiteAdelicGL2Subgroup ℚ) : RSCarrier.finFactor (gf : G2) = gf := by
  refine Subtype.ext ?_
  rw [coe_finFactor, ratArchGL2_of_mem gf.2, map_one, inv_one, one_mul]

theorem componentAt3_iota' (v : HeightOneSpectrum (𝓞 ℚ)) (g : G2) :
    componentAt3 (𝓞 ℚ) ℚ v (iota (𝓞 ℚ) ℚ g) = iotaGL (localAt ℚ v g) :=
  componentAt3_iota v g

theorem finprod_eq_prod_mul_finprod_ite {ι : Type*} [DecidableEq ι] (T : Finset ι) (f : ι → ℂ)
    (hf : (Function.mulSupport f).Finite) :
    ∏ᶠ i, f i = (∏ i ∈ T, f i) * ∏ᶠ i, (if i ∈ T then (1 : ℂ) else f i) := by
  classical
  have h1 : (Function.mulSupport fun i => if i ∈ T then f i else (1 : ℂ)).Finite :=
    (Finset.finite_toSet T).subset fun i hi => by
      by_contra h; exact hi (if_neg h)
  have h2 : (Function.mulSupport fun i => if i ∈ T then (1 : ℂ) else f i).Finite :=
    hf.subset fun i hi => by
      intro h; apply hi; simp [h]
  have hsplit : ∀ i, f i = (if i ∈ T then f i else 1) * (if i ∈ T then 1 else f i) := fun i => by
    by_cases h : i ∈ T <;> simp [h]
  conv_lhs => rw [finprod_congr hsplit]
  rw [finprod_mul_distrib h1 h2]
  congr 1
  rw [finprod_eq_prod_of_mulSupport_subset _ (show (Function.mulSupport fun i => if i ∈ T then f i else (1 : ℂ)) ⊆ T
    from fun i hi => by by_contra h; exact hi (if_neg h))]
  exact Finset.prod_congr rfl fun i hi => if_pos hi

variable (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))) (χA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
  (WF : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ)
  (p : HeightOneSpectrum (𝓞 ℚ)) (hp : p ∈ SQ)
  {m : ℕ} (w : ∀ v : ↥SQ, Fin m → GL (Fin 2) ((v : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) → ℂ)
  (W' : Fin m → G2 → ℂ)
  {nP : ℕ} (cP : Fin nP → ℂ) (xP : Fin nP → GL (Fin 2) (p.adicCompletion ℚ))
  (h₃f : AdelicGL 3 (𝓞 ℚ) ℚ) {m₃ : ℕ} (d : Fin m₃ → ℂ) (k : Fin m₃ → AdelicGL 3 (𝓞 ℚ) ℚ)

def uTil (β : Fin m) : GL (Fin 2) (p.adicCompletion ℚ) → ℂ :=
  fun y => ∑ j, (cP j * (((detNorm (UnramifiedWhittaker.placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)))) *
    w ⟨p, hp⟩ β (y * xP j)

open scoped Classical in

def wS (β : Fin m) : (v : HeightOneSpectrum (𝓞 ℚ)) → (GL (Fin 2) (v.adicCompletion ℚ) → ℂ) :=
  Function.update (fun v => if h : v ∈ SQ then w ⟨v, h⟩ β else fun _ => (1 : ℂ)) p (uTil SQ p hp w cP xP β)

open scoped Classical in

def fS : (v : HeightOneSpectrum (𝓞 ℚ)) → (GL (Fin 2) (v.adicCompletion ℚ) → ℂ) :=
  fun v y => if v = p then
      ∑ j, d j * (((NumberField.TateGlobal.localChar χA v (Matrix.GeneralLinearGroup.det
          (iotaGL y * componentAt3 (𝓞 ℚ) ℚ v (k j))) : ℂˣ) : ℂ) * WF v (iotaGL y * componentAt3 (𝓞 ℚ) ℚ v (k j)))
    else ((NumberField.TateGlobal.localChar χA v (Matrix.GeneralLinearGroup.det
          (iotaGL y * componentAt3 (𝓞 ℚ) ℚ v h₃f)) : ℂˣ) : ℂ) * WF v (iotaGL y * componentAt3 (𝓞 ℚ) ℚ v h₃f)

open scoped Classical in

def Fpr : G2 → ℂ :=
  fun g => ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), (if v ∈ SQ then (1 : ℂ) else
    ((NumberField.TateGlobal.localChar χA v (Matrix.GeneralLinearGroup.det (iotaGL (localAt ℚ v g))) : ℂˣ) : ℂ) *
      WF v (iotaGL (localAt ℚ v g)))

def Wten (β : Fin m) : G2 → ℂ := fun g => (∏ v ∈ SQ, wS SQ p hp w cP xP β v (localAt ℚ v g)) * W' β g

def Ften : G2 → ℂ := fun g => (∏ v ∈ SQ, fS χA WF p h₃f d k v (localAt ℚ v g)) * Fpr SQ χA WF g

theorem wS_self (β : Fin m) : wS SQ p hp w cP xP β p = uTil SQ p hp w cP xP β := by
  simp [wS]

theorem wS_of_ne (β : Fin m) {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∈ SQ) (hvp : v ≠ p) :
    wS SQ p hp w cP xP β v = w ⟨v, hv⟩ β := by
  simp [wS, Function.update_of_ne hvp, hv]

theorem fS_self : fS χA WF p h₃f d k p = fun y => ∑ j, d j *
    (((NumberField.TateGlobal.localChar χA p (Matrix.GeneralLinearGroup.det
        (iotaGL y * componentAt3 (𝓞 ℚ) ℚ p (k j))) : ℂˣ) : ℂ) * WF p (iotaGL y * componentAt3 (𝓞 ℚ) ℚ p (k j))) := by
  funext y; simp [fS]

theorem fS_of_ne {v : HeightOneSpectrum (𝓞 ℚ)} (hvp : v ≠ p) :
    fS χA WF p h₃f d k v = fun y => ((NumberField.TateGlobal.localChar χA v (Matrix.GeneralLinearGroup.det
      (iotaGL y * componentAt3 (𝓞 ℚ) ℚ v h₃f)) : ℂˣ) : ℂ) * WF v (iotaGL y * componentAt3 (𝓞 ℚ) ℚ v h₃f) := by
  funext y; simp [fS, hvp]

theorem purified_eq_sum (Wf0 : finiteAdelicGL2Subgroup ℚ → ℂ)
    (hblind : ∀ (α : Fin m) (v : ↥SQ) (x : GL (Fin 2) ((v : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) (g : G2),
      W' α (g * UnramifiedWhittaker.placeEmbed ℚ (v : HeightOneSpectrum (𝓞 ℚ)) x) = W' α g)
    (hsplitW : ∀ g : G2,
      Wf0 (RSCarrier.finFactor g) = ∑ α : Fin m, (∏ v : ↥SQ, w v α (localAt ℚ (v : HeightOneSpectrum (𝓞 ℚ)) g)) * W' α g)
    (g : finiteAdelicGL2Subgroup ℚ) :
    (∑ j, (cP j * (((detNorm (UnramifiedWhittaker.placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)))) *
        Wf0 (RSCarrier.finFactor (((RSCarrier.finFactor (g : G2) : finiteAdelicGL2Subgroup ℚ) : G2) *
          UnramifiedWhittaker.placeEmbed ℚ p (xP j)))) =
      ∑ β, Wten SQ p hp w W' cP xP β (g : G2) := by
  classical
  rw [finFactor_coe]
  have hterm : ∀ j, Wf0 (RSCarrier.finFactor ((g : G2) * placeEmbed ℚ p (xP j))) =
      ∑ β, (w ⟨p, hp⟩ β (localAt ℚ p (g : G2) * xP j) *
        ∏ u ∈ SQ.erase p, wS SQ p hp w cP xP β u (localAt ℚ u (g : G2))) * W' β (g : G2) := by
    intro j
    rw [hsplitW]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [hblind β ⟨p, hp⟩ (xP j) g]
    congr 1
    have hG : (∏ v : ↥SQ, w v β (localAt ℚ (v : HeightOneSpectrum (𝓞 ℚ)) ((g : G2) * placeEmbed ℚ p (xP j)))) =
        ∏ u ∈ SQ, (if h : u ∈ SQ then w ⟨u, h⟩ β (localAt ℚ u ((g : G2) * placeEmbed ℚ p (xP j))) else (1 : ℂ)) := by
      rw [← Finset.prod_coe_sort SQ (fun u : HeightOneSpectrum (𝓞 ℚ) => if h : u ∈ SQ then
          w ⟨u, h⟩ β (localAt ℚ u ((g : G2) * placeEmbed ℚ p (xP j))) else (1 : ℂ))]
      exact Finset.prod_congr rfl fun v _ => by rw [dif_pos v.2]
    rw [hG, ← Finset.mul_prod_erase SQ _ hp, dif_pos hp, map_mul, localAt_placeEmbed_self]
    congr 1
    refine Finset.prod_congr rfl fun u hu => ?_
    have hup : u ≠ p := Finset.ne_of_mem_erase hu
    have huS : u ∈ SQ := Finset.mem_of_mem_erase hu
    rw [dif_pos huS, wS_of_ne SQ p hp w cP xP β huS hup, map_mul, localAt_placeEmbed_of_ne p _ hup, mul_one]
  simp_rw [hterm, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun β _ => ?_
  unfold Wten
  rw [← Finset.mul_prod_erase SQ _ hp, wS_self]
  unfold uTil
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

def PhiF (v : HeightOneSpectrum (𝓞 ℚ)) (y : LocalGL3 v) : ℂ :=
  ((NumberField.TateGlobal.localChar χA v (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) * WF v y

theorem Fpr_def (g : G2) : Fpr SQ χA WF g =
    ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), (if v ∈ SQ then (1 : ℂ) else PhiF χA WF v (iotaGL (localAt ℚ v g))) := rfl

theorem Fpr_congr {g g' : G2} (h : ∀ u, u ∉ SQ → localAt ℚ u g = localAt ℚ u g') :
    Fpr SQ χA WF g = Fpr SQ χA WF g' := by
  unfold Fpr
  refine finprod_congr fun u => ?_
  by_cases hu : u ∈ SQ
  · rw [if_pos hu, if_pos hu]
  · rw [if_neg hu, if_neg hu, h u hu]

include hp in
theorem frozen_eq_Ften
    (hh₃f : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ → componentAt3 (𝓞 ℚ) ℚ v h₃f = 1)
    (hfin : ∀ g : G2, (Function.mulSupport fun v : HeightOneSpectrum (𝓞 ℚ) =>
      Wtw p χA WF v (componentAt3 (𝓞 ℚ) ℚ v (iota (𝓞 ℚ) ℚ g) * componentAt3 (𝓞 ℚ) ℚ v h₃f)).Finite)
    (g : finiteAdelicGL2Subgroup ℚ) :
    (fun g : finiteAdelicGL2Subgroup ℚ =>
            (fun y : LocalGL3 p => ∑ j : Fin m₃, d j * (((NumberField.TateGlobal.localChar χA p (Matrix.GeneralLinearGroup.det (y * componentAt3 (𝓞 ℚ) ℚ p (k j))) : ℂˣ) : ℂ) * WF p (y * componentAt3 (𝓞 ℚ) ℚ p (k j)))) (iotaGL (localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ))) *
            (∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
              (if v = p then (1 : ℂ) else
                ((NumberField.TateGlobal.localChar χA v (Matrix.GeneralLinearGroup.det
                    (componentAt3 (𝓞 ℚ) ℚ v (iota (𝓞 ℚ) ℚ (g : AdelicGL2 (𝓞 ℚ) ℚ)) * componentAt3 (𝓞 ℚ) ℚ v h₃f)) : ℂˣ) : ℂ) *
                  WF v (componentAt3 (𝓞 ℚ) ℚ v (iota (𝓞 ℚ) ℚ (g : AdelicGL2 (𝓞 ℚ) ℚ)) * componentAt3 (𝓞 ℚ) ℚ v h₃f))))
        (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ)) = Ften SQ χA WF p h₃f d k (g : G2) := by
  rw [finFactor_coe]
  show _ * finWgen (Wtw p χA WF) h₃f (g : G2) = _
  have hpne : ∀ u : HeightOneSpectrum (𝓞 ℚ), u ∉ SQ → u ≠ p := fun u hu h => hu (h ▸ hp)
  unfold finWgen Ften
  rw [finprod_eq_prod_mul_finprod_ite SQ _ (hfin g), ← Finset.mul_prod_erase SQ _ hp,
    ← Finset.mul_prod_erase SQ (fun v => fS χA WF p h₃f d k v (localAt ℚ v (g : G2))) hp]
  have h1 : Wtw p χA WF p (componentAt3 (𝓞 ℚ) ℚ p (iota (𝓞 ℚ) ℚ (g : G2)) * componentAt3 (𝓞 ℚ) ℚ p h₃f) = 1 := by
    simp [Wtw]
  have h2 : ∀ v ∈ SQ.erase p, Wtw p χA WF v (componentAt3 (𝓞 ℚ) ℚ v (iota (𝓞 ℚ) ℚ (g : G2)) * componentAt3 (𝓞 ℚ) ℚ v h₃f) =
      fS χA WF p h₃f d k v (localAt ℚ v (g : G2)) := by
    intro v hv
    rw [Wtw_of_ne χA WF (Finset.ne_of_mem_erase hv), fS_of_ne χA WF p h₃f d k (Finset.ne_of_mem_erase hv),
      componentAt3_iota']
  have h3 : (∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), (if v ∈ SQ then (1 : ℂ) else
      Wtw p χA WF v (componentAt3 (𝓞 ℚ) ℚ v (iota (𝓞 ℚ) ℚ (g : G2)) * componentAt3 (𝓞 ℚ) ℚ v h₃f))) =
      Fpr SQ χA WF (g : G2) := by
    unfold Fpr
    refine finprod_congr fun u => ?_
    by_cases hu : u ∈ SQ
    · rw [if_pos hu, if_pos hu]
    · rw [if_neg hu, if_neg hu, Wtw_of_ne χA WF (hpne u hu), hh₃f u hu, mul_one, componentAt3_iota']
  have h4 : fS χA WF p h₃f d k p (localAt ℚ p (g : G2)) = (fun y : LocalGL3 p => ∑ j : Fin m₃, d j *
      (((NumberField.TateGlobal.localChar χA p (Matrix.GeneralLinearGroup.det (y * componentAt3 (𝓞 ℚ) ℚ p (k j))) : ℂˣ) : ℂ) *
        WF p (y * componentAt3 (𝓞 ℚ) ℚ p (k j)))) (iotaGL (localAt ℚ p (g : G2))) := by
    rw [fS_self]
  rw [h1, one_mul, Finset.prod_congr rfl h2, h3, h4]
  ring

theorem Fpr_one (h1 : ∀ u, u ∉ SQ → WF u 1 = 1) : Fpr SQ χA WF 1 = 1 := by
  unfold Fpr
  refine finprod_eq_one_of_forall_eq_one fun u => ?_
  by_cases hu : u ∈ SQ
  · rw [if_pos hu]
  · rw [if_neg hu, map_one, map_one, map_one, map_one, Units.val_one, one_mul, h1 u hu]

theorem Fpr_mul_of_integral (c : HeightOneSpectrum (𝓞 ℚ) → ℕ)
    (hK : ∀ u, u ∉ SQ → ∀ kk ∈ congruenceK1 (𝓞 ℚ) ℚ u (c u), ∀ y : LocalGL3 u,
      PhiF χA WF u (y * kk) = PhiF χA WF u y)
    (g kf : G2) (hk : ∀ u, u ∉ SQ → localAt ℚ u kf ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ u ⊤) :
    Fpr SQ χA WF (g * kf) = Fpr SQ χA WF g := by
  rw [Fpr_def, Fpr_def]
  refine finprod_congr fun u => ?_
  by_cases hu : u ∈ SQ
  · rw [if_pos hu, if_pos hu]
  · rw [if_neg hu, if_neg hu, map_mul, map_mul]
    have hx' := (mem_localLevelOne_iff (𝓞 ℚ) ℚ u _).1 (hk u hu)
    exact hK u hu _ (iotaGL_mem_congruenceK1 _ _ (fun i j => hx'.1.integral i j) (fun i j => hx'.2.integral i j)) _

theorem PhiF_upperUnipotent_mul {ψ : AddChar AA ℂ} (hlaw : ∀ u, IsGL3PsiWhittakerFn (psiLoc ψ u) (WF u))
    (u : HeightOneSpectrum (𝓞 ℚ)) (x : u.adicCompletion ℚ) (y : LocalGL3 u) :
    PhiF χA WF u (upperUnipotent3 x 0 0 * y) = psiLoc ψ u x * PhiF χA WF u y := by
  unfold PhiF
  rw [map_mul, det_upperUnipotent3, one_mul, hlaw u x 0 0 y, add_zero]
  ring

theorem Fpr_unipotentGL2_mul {ψ : AddChar AA ℂ} (hψQ : ψ⁻¹ = NumberField.StandardAddChar.psiQ)
    (hlaw : ∀ u, IsGL3PsiWhittakerFn (psiLoc ψ u) (WF u))
    (hfin : ∀ g : G2, (Function.mulSupport fun v : HeightOneSpectrum (𝓞 ℚ) =>
      (if v ∈ SQ then (1 : ℂ) else PhiF χA WF v (iotaGL (localAt ℚ v g)))).Finite)
    (t : AA) (ht0 : t.1 = 0) (htS : ∀ u ∈ SQ, t.2 u = 0) (g : G2) :
    Fpr SQ χA WF (unipotentGL2 t * g) = ψ t * Fpr SQ χA WF g := by
  have hpt : ∀ u, (if u ∈ SQ then (1 : ℂ) else PhiF χA WF u (iotaGL (localAt ℚ u (unipotentGL2 t * g)))) =
      psiLoc ψ u (t.2 u) * (if u ∈ SQ then (1 : ℂ) else PhiF χA WF u (iotaGL (localAt ℚ u g))) := by
    intro u
    by_cases hu : u ∈ SQ
    · rw [if_pos hu, if_pos hu, htS u hu, AddChar.map_zero_eq_one, one_mul]
    · rw [if_neg hu, if_neg hu, map_mul, map_mul, localAt_unipotentGL2, iotaGL_unipotentGL2,
        PhiF_upperUnipotent_mul χA WF hlaw]
  have hψfin : (Function.mulSupport fun u : HeightOneSpectrum (𝓞 ℚ) => psiLoc ψ u (t.2 u)).Finite := by
    have hev : ∀ᶠ u : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, t.2 u ∈ u.adicCompletionIntegers ℚ := t.2.2
    refine (Filter.eventually_cofinite.1 hev).subset fun u hu => ?_
    by_contra hint
    exact hu (psiLoc_eq_one_of_mem_integers hψQ u (by simpa using hint))
  rw [Fpr_def, Fpr_def, finprod_congr hpt, finprod_mul_distrib hψfin (hfin g), apply_eq_finprod_psiLoc hψQ t ht0]

theorem continuous_iotaGL_local (v : HeightOneSpectrum (𝓞 ℚ)) :
    Continuous (iotaGL : GL (Fin 2) (v.adicCompletion ℚ) → LocalGL3 v) := by
  have hval : ∀ M : GL (Fin 2) (v.adicCompletion ℚ), Continuous fun _ : Unit => M := fun _ => continuous_const
  have hemb : Continuous fun M : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) => embedMat2 M := by
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      first
        | exact (continuous_apply_apply _ _)
        | exact continuous_const
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact hemb.comp Units.continuous_val
  · have : (fun g : GL (Fin 2) (v.adicCompletion ℚ) => ((iotaGL g)⁻¹ : LocalGL3 v).val) =
        fun g => embedMat2 ((g⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix _ _ _) := by
      funext g; rw [← map_inv, coe_iotaGL]
    rw [this]
    exact hemb.comp (Units.continuous_val.comp continuous_inv)

theorem continuous_det_units {n : ℕ} (v : HeightOneSpectrum (𝓞 ℚ)) :
    Continuous (Matrix.GeneralLinearGroup.det : GL (Fin n) (v.adicCompletion ℚ) → (v.adicCompletion ℚ)ˣ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (Units.continuous_val.matrix_det : Continuous fun g : GL (Fin n) (v.adicCompletion ℚ) =>
      (g : Matrix (Fin n) (Fin n) (v.adicCompletion ℚ)).det)
  · have : (fun g : GL (Fin n) (v.adicCompletion ℚ) => ((Matrix.GeneralLinearGroup.det g)⁻¹ : (v.adicCompletion ℚ)ˣ).val) =
        fun g => ((g⁻¹ : GL (Fin n) (v.adicCompletion ℚ)) : Matrix (Fin n) (Fin n) (v.adicCompletion ℚ)).det := by
      funext g; rw [← map_inv]; rfl
    rw [this]
    exact (Units.continuous_val.comp continuous_inv).matrix_det

theorem continuous_PhiF (hχ : Continuous χA) (v : HeightOneSpectrum (𝓞 ℚ)) (hW : Continuous (WF v)) :
    Continuous (PhiF χA WF v) := by
  unfold PhiF
  refine Continuous.mul ?_ hW
  exact Units.continuous_val.comp ((NumberField.TateGlobal.continuous_localChar χA hχ v).comp (continuous_det_units v))

include hp in
theorem continuous_fS (hχ : Continuous χA) (hW : ∀ v, Continuous (WF v)) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Continuous (fS χA WF p h₃f d k v) := by
  by_cases hv : v = p
  · subst hv
    rw [fS_self]
    refine continuous_finset_sum _ fun j _ => continuous_const.mul ?_
    exact (continuous_PhiF χA WF hχ v (hW v)).comp ((continuous_iotaGL_local v).mul continuous_const)
  · rw [fS_of_ne χA WF p h₃f d k hv]
    exact (continuous_PhiF χA WF hχ v (hW v)).comp ((continuous_iotaGL_local v).mul continuous_const)

theorem fS_unipotent_mul {ψ : AddChar AA ℂ} (hlaw : ∀ u, IsGL3PsiWhittakerFn (psiLoc ψ u) (WF u))
    (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ) (y : GL (Fin 2) (v.adicCompletion ℚ)) :
    fS χA WF p h₃f d k v (unipotentGL2 x * y) = psiLoc ψ v x * fS χA WF p h₃f d k v y := by
  by_cases hv : v = p
  · subst hv
    rw [fS_self, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    show d j * PhiF χA WF v (iotaGL (unipotentGL2 x * y) * componentAt3 (𝓞 ℚ) ℚ v (k j)) =
      psiLoc ψ v x * (d j * PhiF χA WF v (iotaGL y * componentAt3 (𝓞 ℚ) ℚ v (k j)))
    rw [map_mul, iotaGL_unipotentGL2, mul_assoc, PhiF_upperUnipotent_mul χA WF hlaw]
    ring
  · rw [fS_of_ne χA WF p h₃f d k hv]
    show PhiF χA WF v (iotaGL (unipotentGL2 x * y) * componentAt3 (𝓞 ℚ) ℚ v h₃f) =
      psiLoc ψ v x * PhiF χA WF v (iotaGL y * componentAt3 (𝓞 ℚ) ℚ v h₃f)
    rw [map_mul, iotaGL_unipotentGL2, mul_assoc, PhiF_upperUnipotent_mul χA WF hlaw]

theorem wS_unipotent_mul
    (hwlaw : ∀ (v : ↥SQ) (α : Fin m) (x : (v : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)
      (g : GL (Fin 2) ((v : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)),
      w v α (UnramifiedWhittaker.unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ (v : HeightOneSpectrum (𝓞 ℚ)) x * w v α g)
    (β : Fin m) {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∈ SQ) (x : v.adicCompletion ℚ) (y : GL (Fin 2) (v.adicCompletion ℚ)) :
    wS SQ p hp w cP xP β v (UnramifiedWhittaker.unipotent x * y) =
      NumberField.StandardAddChar.psiLocal ℚ v x * wS SQ p hp w cP xP β v y := by
  by_cases hvp : v = p
  · subst hvp
    rw [wS_self]
    unfold uTil
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc (UnramifiedWhittaker.unipotent x), hwlaw ⟨v, hv⟩ β x]
    ring
  · rw [wS_of_ne SQ p hp w cP xP β hv hvp]
    exact hwlaw ⟨v, hv⟩ β x y

theorem remainder_N_invariant {ψ : AddChar AA ℂ} (hψQ : ψ⁻¹ = NumberField.StandardAddChar.psiQ)
    (hlaw : ∀ u, IsGL3PsiWhittakerFn (psiLoc ψ u) (WF u))
    (hfin : ∀ g : G2, (Function.mulSupport fun v : HeightOneSpectrum (𝓞 ℚ) =>
      (if v ∈ SQ then (1 : ℂ) else PhiF χA WF v (iotaGL (localAt ℚ v g)))).Finite)
    (Wr : G2 → ℂ)
    (hblind : ∀ v ∈ SQ, ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : G2), Wr (g * placeEmbed ℚ v x) = Wr g)
    (hWlaw : ∀ t : AA, t.1 = 0 → (∀ v : ↥SQ, localAt ℚ (v : HeightOneSpectrum (𝓞 ℚ)) (unipotentGL2 t) = 1) →
      ∀ g : G2, Wr (unipotentGL2 t * g) = NumberField.StandardAddChar.psiQ t * Wr g)
    (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ) :
    Wr ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : G2) *
        Fpr SQ χA WF ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : G2) =
      Wr (g : G2) * Fpr SQ χA WF (g : G2) := by
  obtain ⟨a, ha⟩ := (Subgroup.mem_subgroupOf.1 n.2 : ((n : finiteAdelicGL2Subgroup ℚ) : G2) ∈ adelicUnipotent ℚ)
  have hn : (((n : finiteAdelicGL2Subgroup ℚ) : G2)) = unipotentGL2 (Multiplicative.toAdd a) := ha.symm
  set t : AA := Multiplicative.toAdd a with htdef
  have ht0 : t.1 = 0 := fst_eq_zero_of_unipotentGL2_mem_fin (hn ▸ (n : finiteAdelicGL2Subgroup ℚ).2)

  set tS : AA := ∑ v ∈ SQ, NumberField.StandardAddChar.adeleSingleAt ℚ v (t.2 v) with htS
  have htS1 : tS.1 = 0 := by
    change adeleArch (𝓞 ℚ) ℚ tS = 0
    rw [htS, map_sum]
    exact Finset.sum_eq_zero fun v _ => by rw [adeleArch_apply, NumberField.StandardAddChar.adeleSingleAt_apply]
  have htS2 : ∀ u, tS.2 u = if u ∈ SQ then t.2 u else 0 := by
    intro u
    change ((finAdeleEval (𝓞 ℚ) ℚ u).comp (adeleFin (𝓞 ℚ) ℚ)) tS = _
    rw [htS, map_sum]
    simp_rw [RingHom.comp_apply, adeleFin_apply, finAdeleEval_apply, NumberField.StandardAddChar.adeleSingleAt_apply]
    by_cases hu : u ∈ SQ
    · rw [if_pos hu, Finset.sum_eq_single_of_mem u hu fun v _ hvu =>
        NumberField.StandardAddChar.finAdeleSingleAt_apply_of_ne ℚ v _ (Ne.symm hvu)]
      exact NumberField.StandardAddChar.finAdeleSingleAt_apply_self ℚ u _
    · rw [if_neg hu]
      exact Finset.sum_eq_zero fun v hv =>
        NumberField.StandardAddChar.finAdeleSingleAt_apply_of_ne ℚ v _ (fun h => hu (h ▸ hv))
  set tO : AA := t - tS with htO
  have htO1 : tO.1 = 0 := by
    change adeleArch (𝓞 ℚ) ℚ (t - tS) = 0
    rw [map_sub, adeleArch_apply, adeleArch_apply, ht0, htS1, sub_zero]
  have htO2 : ∀ u, tO.2 u = if u ∈ SQ then 0 else t.2 u := by
    intro u
    change ((finAdeleEval (𝓞 ℚ) ℚ u).comp (adeleFin (𝓞 ℚ) ℚ)) (t - tS) = _
    rw [map_sub]
    simp only [RingHom.comp_apply, adeleFin_apply, finAdeleEval_apply]
    rw [htS2]
    by_cases hu : u ∈ SQ <;> simp [hu]
  have hdec : unipotentGL2 t = unipotentGL2 tO * unipotentGL2 tS := by
    rw [← unipotentGL2_add, htO, sub_add_cancel]
  have he1 : glArch (𝓞 ℚ) ℚ (unipotentGL2 tS) = 1 := by rw [glArch_unipotentGL2, htS1, unipotentGL2_zero]
  have he2 : ∀ u, u ∉ SQ → localAt ℚ u (unipotentGL2 tS) = 1 := fun u hu => by
    rw [localAt_unipotentGL2, htS2, if_neg hu, unipotentGL2_zero]
  have hWe := apply_mul_eq_of_blind SQ hblind (unipotentGL2 tS) he1 he2
  have hO : ∀ v : ↥SQ, localAt ℚ (v : HeightOneSpectrum (𝓞 ℚ)) (unipotentGL2 tO) = 1 := fun v => by
    rw [localAt_unipotentGL2, htO2, if_pos v.2, unipotentGL2_zero]
  have hcoe : ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : G2) =
      unipotentGL2 tO * (unipotentGL2 tS * (g : G2)) := by
    rw [Subgroup.coe_mul, hn, hdec, mul_assoc]
  rw [hcoe, hWlaw tO htO1 hO, (hWe _).2,
    Fpr_unipotentGL2_mul SQ χA WF hψQ hlaw hfin tO htO1 (fun u hu => by rw [htO2, if_pos hu]),
    Fpr_congr SQ χA WF (fun u hu => by rw [map_mul, he2 u hu, one_mul] :
      ∀ u, u ∉ SQ → localAt ℚ u (unipotentGL2 tS * (g : G2)) = localAt ℚ u (g : G2))]
  have hψ : NumberField.StandardAddChar.psiQ tO * ψ tO = 1 := by
    rw [← hψQ, AddChar.inv_apply, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  calc NumberField.StandardAddChar.psiQ tO * Wr (g : G2) * (ψ tO * Fpr SQ χA WF (g : G2))
      = (NumberField.StandardAddChar.psiQ tO * ψ tO) * (Wr (g : G2) * Fpr SQ χA WF (g : G2)) := by ring
    _ = _ := by rw [hψ, one_mul]

end SecB

section SecB4

open scoped Classical
open IsDedekindDomain NumberField Matrix AutomorphicForm
p2m_open "LanglandsTunnell LanglandsTunnell.CubicInduction~det_upperUnipotent3 LanglandsTunnell.RankinSelberg"
open NumberField.AdelicLevel AdelicDock UnramifiedWhittaker Ws23CutEval.TabF

theorem twist_facts
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hSQram : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∉ SQ →
      Ideal.ramificationIdx' (𝔓.under (𝓞 ℚ)).asIdeal 𝔓.asIdeal = 1)
    (χA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχA : LanglandsTunnell.Converse.IsAdmissibleTwist ℚ χA)
    (hχoff : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ → IsUnramifiedCharAt χA v)
    (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hνadm : LanglandsTunnell.Converse.IsAdmissibleTwist K ν)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    {pins : CarrierPins ℚ} (F : CubicInductionForm K pins ψ ν)
    (hF0 : ∀ v, ¬ IsRamifiedIn K v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
        F.whittakerLoc v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K ν) v (F.whittakerLoc v))
    (p : HeightOneSpectrum (𝓞 ℚ)) (hp : p ∈ SQ)
    (h₃f : AdelicGL 3 (𝓞 ℚ) ℚ) (hh₃f : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ → componentAt3 (𝓞 ℚ) ℚ v h₃f = 1) :
    (∀ u, u ∉ SQ → F.whittakerLoc u 1 = 1) ∧
    (∀ u, u ∉ SQ → ∀ kk ∈ congruenceK1 (𝓞 ℚ) ℚ u (inducedLevelAt K ν u), ∀ y : LocalGL3 u,
      PhiF χA F.whittakerLoc u (y * kk) = PhiF χA F.whittakerLoc u y) ∧
    (∀ g : G2, (Function.mulSupport fun v : HeightOneSpectrum (𝓞 ℚ) =>
      Wtw p χA F.whittakerLoc v (componentAt3 (𝓞 ℚ) ℚ v (iota (𝓞 ℚ) ℚ g) * componentAt3 (𝓞 ℚ) ℚ v h₃f)).Finite) ∧
    (∀ g : G2, (Function.mulSupport fun v : HeightOneSpectrum (𝓞 ℚ) =>
      (if v ∈ SQ then (1 : ℂ) else PhiF χA F.whittakerLoc v (iotaGL (localAt ℚ v g)))).Finite) := by
  have hpne : ∀ q : HeightOneSpectrum (𝓞 ℚ), q ∉ SQ → q ≠ p := fun q hq h => hq (h ▸ hp)
  have hunr : ∀ q : HeightOneSpectrum (𝓞 ℚ), q ∉ SQ → ¬ IsRamifiedIn K q := by
    intro q hq ⟨𝔓, h𝔓, hne⟩
    rw [mem_primeFibre] at h𝔓
    apply hne
    rw [← h𝔓]
    exact hSQram 𝔓 (h𝔓 ▸ hq)
  have hone : ∀ u, u ∉ SQ → F.whittakerLoc u 1 = 1 := fun u hu => (hF0 u (hunr u hu) (hlev u)).1
  have hPhiW : ∀ u, u ≠ p → PhiF χA F.whittakerLoc u = Wtw p χA F.whittakerLoc u := fun u hu => by
    rw [Wtw_of_ne χA F.whittakerLoc hu]; rfl
  have hK1 : ∀ u, u ∉ SQ → ∀ kk ∈ congruenceK1 (𝓞 ℚ) ℚ u (inducedLevelAt K ν u), ∀ y : LocalGL3 u,
      PhiF χA F.whittakerLoc u (y * kk) = PhiF χA F.whittakerLoc u y := by
    intro u hu kk hkk y
    exact (LanglandsTunnell.CubicInduction.inducedLevelAt_twist_eq_of_isUnramifiedCharAt K _hdeg ν hνadm χA hχA u
      (hχoff u hu)).2.2 _ (F.whittakerLoc u) (F.levelInvariant u (hunr u hu)) kk hkk y

  have hbadfin : {v : HeightOneSpectrum (𝓞 ℚ) | IsBadPlace K ν v}.Finite :=
    LanglandsTunnell.CubicInduction.finite_setOf_isBadPlace_of_continuous K ν hνadm.2.1
  have h1S : ∀ v, v ∉ SQ ∪ hbadfin.toFinset → ∀ kk ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v,
      Wtw p χA F.whittakerLoc v kk = 1 := by
    intro v hv kk hkk
    have hvSQ : v ∉ SQ := fun h => hv (Finset.mem_union_left _ h)
    have hgood : ¬ IsBadPlace K ν v := fun h => hv (Finset.mem_union_right _ (hbadfin.mem_toFinset.2 h))
    have hinv0 : ∀ k' ∈ congruenceK1 (𝓞 ℚ) ℚ v 0, ∀ g : LocalGL3 v, F.whittakerLoc v (g * k') = F.whittakerLoc v g :=
      fun k' hk' g => (F.spherical v hgood).1 g k' hk'.1
    have htw := (LanglandsTunnell.CubicInduction.inducedLevelAt_twist_eq_of_isUnramifiedCharAt K _hdeg ν hνadm χA hχA v
      (hχoff v hvSQ)).2.2 0 (F.whittakerLoc v) hinv0 kk (mem_congruenceK1_zero_of_mem v hkk) 1
    rw [one_mul] at htw
    rw [Wtw_of_ne χA F.whittakerLoc (hpne v hvSQ), htw]
    show PhiF χA F.whittakerLoc v 1 = 1
    unfold PhiF
    rw [map_one, map_one, Units.val_one, one_mul, hone v hvSQ]
  have hfinW : ∀ g : G2, (Function.mulSupport fun v : HeightOneSpectrum (𝓞 ℚ) =>
      Wtw p χA F.whittakerLoc v (componentAt3 (𝓞 ℚ) ℚ v (iota (𝓞 ℚ) ℚ g) * componentAt3 (𝓞 ℚ) ℚ v h₃f)).Finite :=
    finite_mulSupport_finWgen (Wtw p χA F.whittakerLoc) (SQ ∪ hbadfin.toFinset)
      (fun v hv => hh₃f v (fun h => hv (Finset.mem_union_left _ h))) h1S
  have hfin1 := finite_mulSupport_finWgen (Wtw p χA F.whittakerLoc) (kf := 1) (SQ ∪ hbadfin.toFinset)
      (fun v _ => map_one _) h1S
  refine ⟨hone, hK1, hfinW, fun g => (hfin1 g).subset fun v hv => ?_⟩
  rw [Function.mem_mulSupport] at hv ⊢
  by_cases hvS : v ∈ SQ
  · simp only [hvS, if_true] at hv
    exact absurd rfl hv
  · simp only [hvS, if_false] at hv
    rw [hPhiW v (hpne v hvS), ← componentAt3_iota'] at hv
    rwa [map_one, mul_one]

theorem continuous_Fpr_comp_val (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))) (χA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (WF : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ) (c : HeightOneSpectrum (𝓞 ℚ) → ℕ)
    (hK : ∀ u, u ∉ SQ → ∀ kk ∈ congruenceK1 (𝓞 ℚ) ℚ u (c u), ∀ y : LocalGL3 u, PhiF χA WF u (y * kk) = PhiF χA WF u y) :
    Continuous fun g : finiteAdelicGL2Subgroup ℚ => Fpr SQ χA WF (g : G2) := by
  let Kf : Subgroup (finiteAdelicGL2Subgroup ℚ) :=
    (levelOne (𝓞 ℚ) ℚ ⊤ ⊓ finiteAdelicGL2Subgroup ℚ).subgroupOf (finiteAdelicGL2Subgroup ℚ)
  have hKset' : (Kf : Set (finiteAdelicGL2Subgroup ℚ)) =
      Subtype.val ⁻¹' ((levelOne (𝓞 ℚ) ℚ ⊤ : Subgroup (AdelicGL2 (𝓞 ℚ) ℚ)) : Set (AdelicGL2 (𝓞 ℚ) ℚ)) := by
    ext g
    simp only [Kf, Subgroup.coe_subgroupOf, Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_inf, g.2, and_true,
      Subgroup.coe_subtype]
  have hKo : IsOpen (Kf : Set (finiteAdelicGL2Subgroup ℚ)) := by
    rw [hKset']
    exact (NumberField.AdelicLevel.isOpen_levelOne (𝓞 ℚ) ℚ top_ne_bot).preimage continuous_subtype_val
  refine continuous_of_mul_invariant Kf hKo _ fun kk hkk g => ?_
  have hk' : ((kk : finiteAdelicGL2Subgroup ℚ) : G2) ∈ levelOne (𝓞 ℚ) ℚ ⊤ :=
    (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hkk)).1
  show Fpr SQ χA WF ((g : G2) * (kk : G2)) = Fpr SQ χA WF (g : G2)
  exact Fpr_mul_of_integral SQ χA WF c hK _ _ fun u _ => localAt_mem_localLevelOne_of_mem_levelOne_top hk' u

end SecB4

section SecB5

open scoped Classical
open IsDedekindDomain NumberField Matrix AutomorphicForm
p2m_open "LanglandsTunnell LanglandsTunnell.CubicInduction~det_upperUnipotent3 LanglandsTunnell.RankinSelberg"
open NumberField.AdelicLevel AdelicDock UnramifiedWhittaker Ws23CutEval.TabF

variable (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))) (χA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
  (WF : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ)
  (p : HeightOneSpectrum (𝓞 ℚ)) (hp : p ∈ SQ)
  {m : ℕ} (w : ∀ v : ↥SQ, Fin m → GL (Fin 2) ((v : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) → ℂ)
  (W' : Fin m → G2 → ℂ)
  {nP : ℕ} (cP : Fin nP → ℂ) (xP : Fin nP → GL (Fin 2) (p.adicCompletion ℚ))
  (h₃f : AdelicGL 3 (𝓞 ℚ) ℚ) {m₃ : ℕ} (d : Fin m₃ → ℂ) (k : Fin m₃ → AdelicGL 3 (𝓞 ℚ) ℚ)

theorem blind_pair (β : Fin m)
    (hblind : ∀ (α : Fin m) (v : ↥SQ) (x : GL (Fin 2) ((v : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) (g : G2),
      W' α (g * UnramifiedWhittaker.placeEmbed ℚ (v : HeightOneSpectrum (𝓞 ℚ)) x) = W' α g) :
    ∀ v ∈ SQ, ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : G2),
      W' β (g * UnramifiedWhittaker.placeEmbed ℚ v x) = W' β g ∧
        Fpr SQ χA WF (g * UnramifiedWhittaker.placeEmbed ℚ v x) = Fpr SQ χA WF g := by
  intro v hv x g
  refine ⟨hblind β ⟨v, hv⟩ x g, Fpr_congr SQ χA WF fun u hu => ?_⟩
  have huv : u ≠ v := fun h => hu (h.symm ▸ hv)
  rw [map_mul, localAt_placeEmbed_of_ne v _ huv, mul_one]

theorem kinv_pair (β : Fin m) (c : HeightOneSpectrum (𝓞 ℚ) → ℕ)
    (hK : ∀ u, u ∉ SQ → ∀ kk ∈ congruenceK1 (𝓞 ℚ) ℚ u (c u), ∀ y : LocalGL3 u, PhiF χA WF u (y * kk) = PhiF χA WF u y)
    (hWK : ∀ (α : Fin m) (kk : finiteAdelicGL2Subgroup ℚ),
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ →
        localAt ℚ v (kk : AdelicGL2 (𝓞 ℚ) ℚ) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤) →
      (∀ v ∈ SQ, localAt ℚ v (kk : AdelicGL2 (𝓞 ℚ) ℚ) = 1) →
      ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, W' α (g * (kk : AdelicGL2 (𝓞 ℚ) ℚ)) = W' α g) :
    ∀ kk : finiteAdelicGL2Subgroup ℚ,
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ →
        localAt ℚ v (kk : AdelicGL2 (𝓞 ℚ) ℚ) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤) →
      (∀ v ∈ SQ, localAt ℚ v (kk : AdelicGL2 (𝓞 ℚ) ℚ) = 1) →
      ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
        W' β (g * (kk : AdelicGL2 (𝓞 ℚ) ℚ)) = W' β g ∧ Fpr SQ χA WF (g * (kk : AdelicGL2 (𝓞 ℚ) ℚ)) = Fpr SQ χA WF g :=
  fun kk h1 h2 g => ⟨hWK β kk h1 h2 g, Fpr_mul_of_integral SQ χA WF c hK g kk h1⟩

include hp in
theorem slots_unipotent (β : Fin m) {ψ : AddChar AA ℂ} (hψQ : ψ⁻¹ = NumberField.StandardAddChar.psiQ)
    (hlaw : ∀ u, IsGL3PsiWhittakerFn (psiLoc ψ u) (WF u))
    (hwlaw : ∀ (v : ↥SQ) (α : Fin m) (x : (v : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)
      (g : GL (Fin 2) ((v : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)),
      w v α (UnramifiedWhittaker.unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ (v : HeightOneSpectrum (𝓞 ℚ)) x * w v α g) :
    ∀ v ∈ SQ, ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
      wS SQ p hp w cP xP β v (UnramifiedWhittaker.unipotent x * g) * fS χA WF p h₃f d k v (UnramifiedWhittaker.unipotent x * g) =
        wS SQ p hp w cP xP β v g * fS χA WF p h₃f d k v g := by
  intro v hv x g
  rw [wS_unipotent_mul SQ p hp w cP xP hwlaw β hv x g, unipotent_eq_unipotentGL2, fS_unipotent_mul χA WF p h₃f d k hlaw,
    psiLoc_eq_psiLocal_neg hψQ]
  have h1 : NumberField.StandardAddChar.psiLocal ℚ v x * NumberField.StandardAddChar.psiLocal ℚ v (-x) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  calc NumberField.StandardAddChar.psiLocal ℚ v x * wS SQ p hp w cP xP β v g *
        (NumberField.StandardAddChar.psiLocal ℚ v (-x) * fS χA WF p h₃f d k v g)
      = (NumberField.StandardAddChar.psiLocal ℚ v x * NumberField.StandardAddChar.psiLocal ℚ v (-x)) *
          (wS SQ p hp w cP xP β v g * fS χA WF p h₃f d k v g) := by ring
    _ = _ := by rw [h1, one_mul]

include hp in
theorem measurable_slots (β : Fin m) (hχ : Continuous χA) (hW : ∀ v, Continuous (WF v))
    (hwmeas : ∀ (v : ↥SQ) (α : Fin m), letI := localGLBorel ℚ (v : HeightOneSpectrum (𝓞 ℚ)); Measurable (w v α)) :
    ∀ v ∈ SQ, letI := localGLBorel ℚ v
      Measurable (wS SQ p hp w cP xP β v) ∧ Measurable (fS χA WF p h₃f d k v) := by
  intro v hv
  letI := localGLBorel ℚ v
  haveI := borelSpace_localGLBorel ℚ v
  refine ⟨?_, (continuous_fS SQ χA WF p hp h₃f d k hχ hW v).measurable⟩
  by_cases hvp : v = p
  · subst hvp
    rw [wS_self]
    unfold uTil
    refine Finset.measurable_sum _ fun j _ => ?_
    exact ((hwmeas ⟨v, hv⟩ β).comp (continuous_mul_right (xP j)).measurable).const_mul _
  · rw [wS_of_ne SQ p hp w cP xP β hv hvp]
    exact hwmeas ⟨v, hv⟩ β

theorem measurable_remainders (β : Fin m) (c : HeightOneSpectrum (𝓞 ℚ) → ℕ)
    (hK : ∀ u, u ∉ SQ → ∀ kk ∈ congruenceK1 (𝓞 ℚ) ℚ u (c u), ∀ y : LocalGL3 u, PhiF χA WF u (y * kk) = PhiF χA WF u y)
    (hWmeas : ∀ α : Fin m, Measurable (fun g : finiteAdelicGL2Subgroup ℚ => W' α (g : AdelicGL2 (𝓞 ℚ) ℚ))) :
    Measurable (fun g : finiteAdelicGL2Subgroup ℚ => W' β (g : AdelicGL2 (𝓞 ℚ) ℚ) * Fpr SQ χA WF (g : AdelicGL2 (𝓞 ℚ) ℚ)) :=
  (hWmeas β).mul (continuous_Fpr_comp_val SQ χA WF c hK).measurable

include hp in
theorem measurable_tensors (β : Fin m) (hχ : Continuous χA) (hW : ∀ v, Continuous (WF v)) (c : HeightOneSpectrum (𝓞 ℚ) → ℕ)
    (hK : ∀ u, u ∉ SQ → ∀ kk ∈ congruenceK1 (𝓞 ℚ) ℚ u (c u), ∀ y : LocalGL3 u, PhiF χA WF u (y * kk) = PhiF χA WF u y)
    (hwmeas : ∀ (v : ↥SQ) (α : Fin m), letI := localGLBorel ℚ (v : HeightOneSpectrum (𝓞 ℚ)); Measurable (w v α))
    (hWmeas : ∀ α : Fin m, Measurable (fun g : finiteAdelicGL2Subgroup ℚ => W' α (g : AdelicGL2 (𝓞 ℚ) ℚ))) :
    Measurable (fun g : finiteAdelicGL2Subgroup ℚ =>
      Wten SQ p hp w W' cP xP β (g : G2) * Ften SQ χA WF p h₃f d k (g : G2)) := by
  have hw : ∀ v ∈ SQ, Measurable fun g : finiteAdelicGL2Subgroup ℚ => wS SQ p hp w cP xP β v (localAt ℚ v (g : G2)) := by
    intro v hv
    letI := localGLBorel ℚ v
    haveI := borelSpace_localGLBorel ℚ v
    exact (measurable_slots SQ χA WF p hp w cP xP h₃f d k β hχ hW hwmeas v hv).1.comp
      ((continuous_localAt ℚ v).comp continuous_subtype_val).measurable
  have hf : ∀ v ∈ SQ, Measurable fun g : finiteAdelicGL2Subgroup ℚ => fS χA WF p h₃f d k v (localAt ℚ v (g : G2)) := by
    intro v hv
    letI := localGLBorel ℚ v
    haveI := borelSpace_localGLBorel ℚ v
    exact (measurable_slots SQ χA WF p hp w cP xP h₃f d k β hχ hW hwmeas v hv).2.comp
      ((continuous_localAt ℚ v).comp continuous_subtype_val).measurable
  unfold Wten Ften
  exact ((Finset.measurable_prod SQ hw).mul (hWmeas β)).mul
    ((Finset.measurable_prod SQ hf).mul (continuous_Fpr_comp_val SQ χA WF c hK).measurable)

end SecB5

end Ws23CutEval

end

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
p2m_open "LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction~det_upperUnipotent3 MeasureTheory"
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace Ws23CutEval

theorem rsFinIntegral_finset_sum {ι : Type*} (T : Finset ι)
    (μ : Measure (finiteAdelicGL2Subgroup ℚ)) (μN : Measure RSCarrier.finUnipotent) (s : ℂ)
    (A : ι → finiteAdelicGL2Subgroup ℚ → ℂ) (B : finiteAdelicGL2Subgroup ℚ → ℂ)
    (hint : ∀ i ∈ T, Integrable (fun g : finiteAdelicGL2Subgroup ℚ => (A i g * B g) *
        ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2))
      (μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN))) :
    RSCarrier.rsFinIntegral μ μN s (∑ i ∈ T, A i) B = ∑ i ∈ T, RSCarrier.rsFinIntegral μ μN s (A i) B := by
  unfold RSCarrier.rsFinIntegral RSCarrier.rsLocalIntegral
  rw [← integral_finsetSum T hint]
  congr 1
  funext g
  rw [Finset.sum_apply, Finset.sum_mul, Finset.sum_mul]

end Ws23CutEval

open Ws23CutEval in
open scoped Classical in

theorem solution
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hSQram : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∉ SQ →
      Ideal.ramificationIdx' (𝔓.under (𝓞 ℚ)).asIdeal 𝔓.asIdeal = 1)
    (χA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχA : LanglandsTunnell.Converse.IsAdmissibleTwist ℚ χA)
    (hχoff : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ → IsUnramifiedCharAt χA v)
    (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hνadm : LanglandsTunnell.Converse.IsAdmissibleTwist K ν)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ) (hψQ : ψ⁻¹ = NumberField.StandardAddChar.psiQ)
    (hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (F : CubicInductionForm K (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2)
      (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ψ ν)
    (hF0 : F.form ≠ 0 ∧ ∀ v, ¬ IsRamifiedIn K v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
        F.whittakerLoc v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K ν) v (F.whittakerLoc v))
    (hFw : ∀ v, Continuous (F.whittakerLoc v))
    (p : HeightOneSpectrum (𝓞 ℚ)) (hp : p ∈ SQ)

    (Wf0 : finiteAdelicGL2Subgroup ℚ → ℂ)
    (m : ℕ) (w : ∀ v : ↥SQ, Fin m → GL (Fin 2) ((v : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) → ℂ)
    (W' : Fin m → AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hblind : ∀ (α : Fin m) (v : ↥SQ) (x : GL (Fin 2) ((v : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      W' α (g * UnramifiedWhittaker.placeEmbed ℚ (v : HeightOneSpectrum (𝓞 ℚ)) x) = W' α g)
    (hwlaw : ∀ (v : ↥SQ) (α : Fin m) (x : (v : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) (g : GL (Fin 2) ((v : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)),
      w v α (UnramifiedWhittaker.unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ (v : HeightOneSpectrum (𝓞 ℚ)) x * w v α g)
    (hWlaw : ∀ (α : Fin m) (t : AdeleRing (𝓞 ℚ) ℚ), t.1 = 0 → (∀ v : ↥SQ, localAt ℚ (v : HeightOneSpectrum (𝓞 ℚ)) (unipotentGL2 t) = 1) →
      ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, W' α (unipotentGL2 t * g) = NumberField.StandardAddChar.psiQ t * W' α g)
    (hwmeas : ∀ (v : ↥SQ) (α : Fin m), letI := localGLBorel ℚ (v : HeightOneSpectrum (𝓞 ℚ)); Measurable (w v α))
    (hWmeas : ∀ α : Fin m, Measurable (fun g : finiteAdelicGL2Subgroup ℚ => W' α (g : AdelicGL2 (𝓞 ℚ) ℚ)))
    (hwsm : ∀ (v : ↥SQ) (α : Fin m), ∃ U : Subgroup (GL (Fin 2) ((v : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)),
      IsOpen (U : Set (GL (Fin 2) ((v : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ))) ∧
        ∀ k ∈ U, ∀ g : GL (Fin 2) ((v : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ), w v α (g * k) = w v α g)
    (hWK : ∀ (α : Fin m) (k : finiteAdelicGL2Subgroup ℚ),
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ →
        localAt ℚ v (k : AdelicGL2 (𝓞 ℚ) ℚ) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤) →
      (∀ v ∈ SQ, localAt ℚ v (k : AdelicGL2 (𝓞 ℚ) ℚ) = 1) →
      ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, W' α (g * (k : AdelicGL2 (𝓞 ℚ) ℚ)) = W' α g)
    (hsplitW : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      Wf0 (RSCarrier.finFactor g) = ∑ α : Fin m, (∏ v : ↥SQ, w v α (localAt ℚ (v : HeightOneSpectrum (𝓞 ℚ)) g)) * W' α g)

    (nP : ℕ) (cP : Fin nP → ℂ) (xP : Fin nP → GL (Fin 2) (p.adicCompletion ℚ))

    [SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ)]
    (μfH : Measure (finiteAdelicGL2Subgroup ℚ)) [μfH.IsHaarMeasure]
    (μNF : Measure RSCarrier.finUnipotent) [μNF.IsHaarMeasure]

    (μv : ∀ v : HeightOneSpectrum (𝓞 ℚ), @Measure (GL (Fin 2) (v.adicCompletion ℚ)) (localGLBorel ℚ v))
    (μNv : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      @Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range (@Subtype.instMeasurableSpace _ _ (localGLBorel ℚ v)))
    (hμv : ∀ v ∈ SQ,
      letI := localGLBorel ℚ v
      haveI := borelSpace_localGLBorel ℚ v
      (μv v).IsHaarMeasure ∧ (μNv v).IsHaarMeasure) :
    ∃ c : ℂ, c ≠ 0 ∧

      ∀ (h₃f : AdelicGL 3 (𝓞 ℚ) ℚ),
        (archComponent3 (𝓞 ℚ) ℚ h₃f = 1 ∧ componentAt3 (𝓞 ℚ) ℚ p h₃f = 1 ∧
          ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ → componentAt3 (𝓞 ℚ) ℚ v h₃f = 1) →
      ∀ (m₃ : ℕ) (d : Fin m₃ → ℂ) (k : Fin m₃ → AdelicGL 3 (𝓞 ℚ) ℚ),
        (∀ j, archComponent3 (𝓞 ℚ) ℚ (k j) = 1 ∧
          ∀ v : HeightOneSpectrum (𝓞 ℚ), v ≠ p → componentAt3 (𝓞 ℚ) ℚ v (k j) = 1) →
      ∀ s : ℂ,

        (∀ β : Fin m, (letI := localGLBorel ℚ p
          haveI := borelSpace_localGLBorel ℚ p
          Integrable (fun g : GL (Fin 2) ((p).adicCompletion ℚ) =>
            ((fun y : GL (Fin 2) (p.adicCompletion ℚ) => (fun y : LocalGL3 p => ∑ j, d j * (((NumberField.TateGlobal.localChar χA p (Matrix.GeneralLinearGroup.det (y * componentAt3 (𝓞 ℚ) ℚ p (k j))) : ℂˣ) : ℂ) * F.whittakerLoc p (y * componentAt3 (𝓞 ℚ) ℚ p (k j)))) (iotaGL y)) g * (fun y : GL (Fin 2) (p.adicCompletion ℚ) => ∑ j, (cP j * (((detNorm (UnramifiedWhittaker.placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)))) * w ⟨p, hp⟩ β (y * xP j)) g) *
              ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : ((p).adicCompletion ℚ)ˣ) :
                  (p).adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            ((μv p).withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p).adicCompletion ℚ)).range (μNv p))))) →

        (∀ (β : Fin m) (v' : ↥SQ), (v' : HeightOneSpectrum (𝓞 ℚ)) ≠ p →
          (letI := localGLBorel ℚ (v' : HeightOneSpectrum (𝓞 ℚ))
          haveI := borelSpace_localGLBorel ℚ (v' : HeightOneSpectrum (𝓞 ℚ))
          Integrable (fun g : GL (Fin 2) (((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ) =>
            ((fun y : GL (Fin 2) (((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ) => ((NumberField.TateGlobal.localChar χA (v' : HeightOneSpectrum (𝓞 ℚ)) (Matrix.GeneralLinearGroup.det (iotaGL y * componentAt3 (𝓞 ℚ) ℚ (v' : HeightOneSpectrum (𝓞 ℚ)) h₃f)) : ℂˣ) : ℂ) * F.whittakerLoc (v' : HeightOneSpectrum (𝓞 ℚ)) (iotaGL y * componentAt3 (𝓞 ℚ) ℚ (v' : HeightOneSpectrum (𝓞 ℚ)) h₃f)) g * (w v' β) g) *
              ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ)ˣ) :
                  ((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            ((μv (v' : HeightOneSpectrum (𝓞 ℚ))).withDensity (HaarQuotient.density (unipotentGL2Hom (R := ((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ)).range (μNv (v' : HeightOneSpectrum (𝓞 ℚ))))))) →
        RSCarrier.rsFinIntegral μfH μNF s
            ({g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
                  localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g : finiteAdelicGL2Subgroup ℚ =>
                (fun gf : finiteAdelicGL2Subgroup ℚ => ∑ j, (cP j * (((detNorm (UnramifiedWhittaker.placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)))) *
        Wf0 (RSCarrier.finFactor ((gf : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p (xP j)))) (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ))))
            ({g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
                  localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g : finiteAdelicGL2Subgroup ℚ =>
                (fun g : finiteAdelicGL2Subgroup ℚ =>
            (fun y : LocalGL3 p => ∑ j : Fin m₃, d j * (((NumberField.TateGlobal.localChar χA p (Matrix.GeneralLinearGroup.det (y * componentAt3 (𝓞 ℚ) ℚ p (k j))) : ℂˣ) : ℂ) * F.whittakerLoc p (y * componentAt3 (𝓞 ℚ) ℚ p (k j)))) (iotaGL (localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ))) *
            (∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
              (if v = p then (1 : ℂ) else
                ((NumberField.TateGlobal.localChar χA v (Matrix.GeneralLinearGroup.det
                    (componentAt3 (𝓞 ℚ) ℚ v (iota (𝓞 ℚ) ℚ (g : AdelicGL2 (𝓞 ℚ) ℚ)) * componentAt3 (𝓞 ℚ) ℚ v h₃f)) : ℂˣ) : ℂ) *
                  F.whittakerLoc v (componentAt3 (𝓞 ℚ) ℚ v (iota (𝓞 ℚ) ℚ (g : AdelicGL2 (𝓞 ℚ) ℚ)) * componentAt3 (𝓞 ℚ) ℚ v h₃f)))) (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ)))) =
          c * ∑ β : Fin m, W' β 1 *
            ((letI := localGLBorel ℚ p; RSCarrier.rsLocalIntegral (μv p) (unipotentGL2Hom (R := (p).adicCompletion ℚ)).range (μNv p)
              (fun g : GL (Fin 2) ((p).adicCompletion ℚ) =>
                (LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : ((p).adicCompletion ℚ)ˣ) :
                  (p).adicCompletion ℚ) : ℝ))
              s (fun y : GL (Fin 2) (p.adicCompletion ℚ) => ∑ j, (cP j * (((detNorm (UnramifiedWhittaker.placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)))) * w ⟨p, hp⟩ β (y * xP j)) (fun y : GL (Fin 2) (p.adicCompletion ℚ) => (fun y : LocalGL3 p => ∑ j, d j * (((NumberField.TateGlobal.localChar χA p (Matrix.GeneralLinearGroup.det (y * componentAt3 (𝓞 ℚ) ℚ p (k j))) : ℂˣ) : ℂ) * F.whittakerLoc p (y * componentAt3 (𝓞 ℚ) ℚ p (k j)))) (iotaGL y))) *
              ∏ v' : ↥(SQ.erase p),
                (letI := localGLBorel ℚ (v' : HeightOneSpectrum (𝓞 ℚ)); RSCarrier.rsLocalIntegral (μv (v' : HeightOneSpectrum (𝓞 ℚ))) (unipotentGL2Hom (R := ((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ)).range (μNv (v' : HeightOneSpectrum (𝓞 ℚ)))
              (fun g : GL (Fin 2) (((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ) =>
                (LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ)ˣ) :
                  ((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ) : ℝ))
              s (w ⟨(v' : HeightOneSpectrum (𝓞 ℚ)), Finset.mem_of_mem_erase v'.2⟩ β) (fun y : GL (Fin 2) (((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ) => ((NumberField.TateGlobal.localChar χA (v' : HeightOneSpectrum (𝓞 ℚ)) (Matrix.GeneralLinearGroup.det (iotaGL y * componentAt3 (𝓞 ℚ) ℚ (v' : HeightOneSpectrum (𝓞 ℚ)) h₃f)) : ℂˣ) : ℂ) * F.whittakerLoc (v' : HeightOneSpectrum (𝓞 ℚ)) (iotaGL y * componentAt3 (𝓞 ℚ) ℚ (v' : HeightOneSpectrum (𝓞 ℚ)) h₃f)))) := by
  classical
  obtain ⟨c, hc0, HFF⟩ :=
    LanglandsTunnell.RankinSelberg.exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable
      SQ μfH μNF μv μNv hμv
  refine ⟨c, hc0, ?_⟩
  intro h₃f hh₃f m₃ d k hk s hIp hIv
  have hlaw : ∀ u : HeightOneSpectrum (𝓞 ℚ), IsGL3PsiWhittakerFn (psiLoc ψ u) (F.whittakerLoc u) := fun u => F.whittakerLoc_law u
  obtain ⟨hF1, hK1, hfinW, hfinF⟩ := twist_facts K _hdeg SQ hSQram χA hχA hχoff ν hνadm ψ hlev F hF0.2 p hp h₃f hh₃f.2.2

  have hβ : ∀ β : Fin m,
      Integrable (fun g : finiteAdelicGL2Subgroup ℚ =>
          (({g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ → ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range, ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g : finiteAdelicGL2Subgroup ℚ => Wten SQ p hp w W' cP xP β (g : AdelicGL2 (𝓞 ℚ) ℚ))) g *
            ({g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ → ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range, ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g : finiteAdelicGL2Subgroup ℚ => Ften SQ χA F.whittakerLoc p h₃f d k (g : AdelicGL2 (𝓞 ℚ) ℚ))) g) * ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2))
        (μfH.withDensity (HaarQuotient.density RSCarrier.finUnipotent μNF)) ∧
      RSCarrier.rsFinIntegral μfH μNF s
          ({g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ → ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range, ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g : finiteAdelicGL2Subgroup ℚ => Wten SQ p hp w W' cP xP β (g : AdelicGL2 (𝓞 ℚ) ℚ)))
          ({g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ → ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range, ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g : finiteAdelicGL2Subgroup ℚ => Ften SQ χA F.whittakerLoc p h₃f d k (g : AdelicGL2 (𝓞 ℚ) ℚ))) =
        c * (W' β 1 * Fpr SQ χA F.whittakerLoc 1) * ∏ v ∈ SQ, (letI := localGLBorel ℚ v; RSCarrier.rsLocalIntegral (μv v) (unipotentGL2Hom (R := v.adicCompletion ℚ)).range (μNv v)
              (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
                (LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                  v.adicCompletion ℚ) : ℝ))
              s (wS SQ p hp w cP xP β v) (fS χA F.whittakerLoc p h₃f d k v)) := by
    intro β
    exact HFF (Wten SQ p hp w W' cP xP β) (Ften SQ χA F.whittakerLoc p h₃f d k) (W' β) (Fpr SQ χA F.whittakerLoc) (wS SQ p hp w cP xP β) (fS χA F.whittakerLoc p h₃f d k) s (fun _ => rfl) (fun _ => rfl)
      (blind_pair (SQ := SQ) (χA := χA) (WF := F.whittakerLoc) (W' := W') (β := β) (hblind := hblind))
      (remainder_N_invariant SQ χA F.whittakerLoc hψQ hlaw hfinF (W' β) (fun v hv x g => hblind β ⟨v, hv⟩ x g) (hWlaw β))
      (kinv_pair (SQ := SQ) (χA := χA) (WF := F.whittakerLoc) (W' := W') (β := β) (c := fun u => inducedLevelAt K ν u)
        (hK := hK1) (hWK := hWK))
      (slots_unipotent (SQ := SQ) (χA := χA) (WF := F.whittakerLoc) (p := p) (hp := hp) (w := w) (cP := cP) (xP := xP)
        (h₃f := h₃f) (d := d) (k := k) (β := β) (hψQ := hψQ) (hlaw := hlaw) (hwlaw := hwlaw))
      (measurable_tensors (SQ := SQ) (χA := χA) (WF := F.whittakerLoc) (p := p) (hp := hp) (w := w) (W' := W') (cP := cP)
        (xP := xP) (h₃f := h₃f) (d := d) (k := k) (β := β) (hχ := hχA.2.1) (hW := hFw)
        (c := fun u => inducedLevelAt K ν u) (hK := hK1) (hwmeas := hwmeas) (hWmeas := hWmeas))
      (measurable_slots (SQ := SQ) (χA := χA) (WF := F.whittakerLoc) (p := p) (hp := hp) (w := w) (cP := cP) (xP := xP)
        (h₃f := h₃f) (d := d) (k := k) (β := β) (hχ := hχA.2.1) (hW := hFw) (hwmeas := hwmeas))
      (measurable_remainders (SQ := SQ) (χA := χA) (WF := F.whittakerLoc) (W' := W') (β := β)
        (c := fun u => inducedLevelAt K ν u) (hK := hK1) (hWmeas := hWmeas))
      (fun v hv => by
        by_cases hvp : v = p
        · subst hvp
          rw [wS_self, fS_self]
          exact hIp β
        · rw [wS_of_ne SQ p hp w cP xP β hv hvp, fS_of_ne χA F.whittakerLoc p h₃f d k hvp]
          exact hIv β ⟨v, hv⟩ hvp)

  have hWfun : ({g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ → ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range, ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator fun g : finiteAdelicGL2Subgroup ℚ =>
        (fun gf : finiteAdelicGL2Subgroup ℚ => ∑ j, (cP j * (((detNorm (UnramifiedWhittaker.placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)))) *
          Wf0 (RSCarrier.finFactor ((gf : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p (xP j)))) (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ))) =
      ∑ β : Fin m, {g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ → ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range, ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g : finiteAdelicGL2Subgroup ℚ => Wten SQ p hp w W' cP xP β (g : AdelicGL2 (𝓞 ℚ) ℚ)) := by
    rw [← Finset.indicator_sum]
    congr 1
    funext g
    rw [Finset.sum_apply]
    exact purified_eq_sum SQ p hp w W' cP xP Wf0 hblind hsplitW g
  have hFfun : ({g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ → ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range, ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator fun g : finiteAdelicGL2Subgroup ℚ =>
        (fun g : finiteAdelicGL2Subgroup ℚ =>
            (fun y : LocalGL3 p => ∑ j : Fin m₃, d j * (((NumberField.TateGlobal.localChar χA p (Matrix.GeneralLinearGroup.det (y * componentAt3 (𝓞 ℚ) ℚ p (k j))) : ℂˣ) : ℂ) * F.whittakerLoc p (y * componentAt3 (𝓞 ℚ) ℚ p (k j)))) (iotaGL (localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ))) *
            (∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
              (if v = p then (1 : ℂ) else
                ((NumberField.TateGlobal.localChar χA v (Matrix.GeneralLinearGroup.det
                    (componentAt3 (𝓞 ℚ) ℚ v (iota (𝓞 ℚ) ℚ (g : AdelicGL2 (𝓞 ℚ) ℚ)) * componentAt3 (𝓞 ℚ) ℚ v h₃f)) : ℂˣ) : ℂ) *
                  F.whittakerLoc v (componentAt3 (𝓞 ℚ) ℚ v (iota (𝓞 ℚ) ℚ (g : AdelicGL2 (𝓞 ℚ) ℚ)) * componentAt3 (𝓞 ℚ) ℚ v h₃f)))) (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ))) =
      {g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ → ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range, ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g : finiteAdelicGL2Subgroup ℚ => Ften SQ χA F.whittakerLoc p h₃f d k (g : AdelicGL2 (𝓞 ℚ) ℚ)) := by
    congr 1
    funext g
    exact frozen_eq_Ften SQ χA F.whittakerLoc p hp h₃f d k hh₃f.2.2 hfinW g
  rw [hWfun, hFfun, rsFinIntegral_finset_sum _ μfH μNF s _ _ (fun β _ => (hβ β).1), Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [(hβ β).2, Fpr_one SQ χA F.whittakerLoc hF1, mul_one, ← Finset.mul_prod_erase SQ _ hp, wS_self, fS_self,
    ← Finset.prod_coe_sort (SQ.erase p)]
  have hrest : ∀ v' : ↥(SQ.erase p),
      (letI := localGLBorel ℚ (v' : HeightOneSpectrum (𝓞 ℚ)); RSCarrier.rsLocalIntegral (μv (v' : HeightOneSpectrum (𝓞 ℚ))) (unipotentGL2Hom (R := (v' : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)).range (μNv (v' : HeightOneSpectrum (𝓞 ℚ)))
              (fun g : GL (Fin 2) ((v' : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) =>
                (LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : ((v' : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ) :
                  (v' : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) : ℝ))
              s (wS SQ p hp w cP xP β (v' : HeightOneSpectrum (𝓞 ℚ))) (fS χA F.whittakerLoc p h₃f d k (v' : HeightOneSpectrum (𝓞 ℚ)))) =
      (letI := localGLBorel ℚ (v' : HeightOneSpectrum (𝓞 ℚ)); RSCarrier.rsLocalIntegral (μv (v' : HeightOneSpectrum (𝓞 ℚ))) (unipotentGL2Hom (R := (v' : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)).range (μNv (v' : HeightOneSpectrum (𝓞 ℚ)))
              (fun g : GL (Fin 2) ((v' : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) =>
                (LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : ((v' : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ) :
                  (v' : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) : ℝ))
              s (w ⟨(v' : HeightOneSpectrum (𝓞 ℚ)), Finset.mem_of_mem_erase v'.2⟩ β) (fun y : GL (Fin 2) (((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ) => ((NumberField.TateGlobal.localChar χA (v' : HeightOneSpectrum (𝓞 ℚ)) (Matrix.GeneralLinearGroup.det (iotaGL y * componentAt3 (𝓞 ℚ) ℚ (v' : HeightOneSpectrum (𝓞 ℚ)) h₃f)) : ℂˣ) : ℂ) * F.whittakerLoc (v' : HeightOneSpectrum (𝓞 ℚ)) (iotaGL y * componentAt3 (𝓞 ℚ) ℚ (v' : HeightOneSpectrum (𝓞 ℚ)) h₃f))) := by
    intro v'
    rw [wS_of_ne SQ p hp w cP xP β (Finset.mem_of_mem_erase v'.2) (Finset.ne_of_mem_erase v'.2),
      fS_of_ne χA F.whittakerLoc p h₃f d k (Finset.ne_of_mem_erase v'.2)]
  rw [Fintype.prod_congr _ _ hrest]
  unfold uTil
  ring

end S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_rsFinIntegral_indicator_purified_eq_mul_sum_prod_rsLocalIntegral
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_rsFinIntegral_indicator_purified_eq_mul_sum_prod_rsLocalIntegral (solution)
