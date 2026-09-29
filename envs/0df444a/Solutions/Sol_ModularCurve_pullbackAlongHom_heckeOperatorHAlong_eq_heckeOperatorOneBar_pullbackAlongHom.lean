-- Prove2me | solution 1 for ModularCurve.pullbackAlongHom_heckeOperatorHAlong_eq_heckeOperatorOneBar_pullbackAlongHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/91e245d1-ceaf-5210-8dfb-d6297debe437

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_ModularCurve_XHHeckeOperator
import Definitions.Def_ModularCurve_ShimuraKernel
import Theorems.Thm_AlgebraicCurve_Divisor_pullbackAlong_pullbackAlong
import Theorems.Thm_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong
import Theorems.Thm_AlgebraicCurve_finrankAlong_comp
import Theorems.Thm_AlgebraicCurve_separableAlong_of_charZero
import Theorems.Thm_ModularCurve_finrankAlong_heckeAlphaOneBar
import Theorems.Thm_ModularCurve_finrankAlong_heckeAlphaHBar_of_dvd
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_ModularCurve_heckeInputsHAlong
import Theorems.Thm_ModularCurve_laurentBaseChange_x1FunctionField_sup_xHTopFunctionFieldC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_pullbackAlongHom_heckeOperatorHAlong_eq_heckeOperatorOneBar_pullbackAlongHom
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.qExpandAlgHomC_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ"
p2m_attr_erase "simp" "ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
p2m_open "ModularCurve AlgebraicCurve~finiteDimensional_adjoin_of_transcendental"
open scoped MatrixGroups

noncomputable section

namespace TransportU

p2m_open "ModularCurve AlgebraicCurve~finiteDimensional_adjoin_of_transcendental IntermediateField CongruenceSubgroup"
open scoped MatrixGroups

section Exchange

variable {K F A B E : Type*} [Field K] [Field F] [Field A] [Field B] [Field E]
  [Algebra K F] [Algebra K A] [Algebra K B] [Algebra K E]
  [HasPrincipalDivisors K A] [HasPrincipalDivisors K B] [HasPrincipalDivisors K E]

theorem pullbackAlong_congr {φ ψ : F →ₐ[K] E} (h : φ = ψ)
    (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral) (D : Divisor K F) :
    Divisor.pullbackAlong φ hφ D = Divisor.pullbackAlong ψ hψ D := by
  subst h; rfl

theorem pullbackAlong_correspondence
    (α β : F →ₐ[K] A) (hα : α.toRingHom.IsIntegral) (hβ : β.toRingHom.IsIntegral)
    (α' β' : B →ₐ[K] E) (hα' : α'.toRingHom.IsIntegral) (hβ' : β'.toRingHom.IsIntegral)
    (ι : F →ₐ[K] B) (hι : ι.toRingHom.IsIntegral) (j : A →ₐ[K] E) (hj : j.toRingHom.IsIntegral)
    (hsqβ : β'.comp ι = j.comp β)
    (hex : ∀ E₀ : Divisor K A, Divisor.pullbackAlong ι hι (Divisor.pushforwardAlong α hα E₀)
      = Divisor.pushforwardAlong α' hα' (Divisor.pullbackAlong j hj E₀))
    (D : Divisor K F) :
    Divisor.pullbackAlong ι hι (Divisor.correspondence β α hβ hα D)
      = Divisor.correspondence β' α' hβ' hα' (Divisor.pullbackAlong ι hι D) := by
  rw [Divisor.correspondence_apply, Divisor.correspondence_apply, hex,
    Divisor.pullbackAlong_pullbackAlong ι β' hι hβ' (RingHom.IsIntegral.trans _ _ hι hβ') D,
    pullbackAlong_congr hsqβ (RingHom.IsIntegral.trans _ _ hι hβ') (RingHom.IsIntegral.trans _ _ hβ hj) D,
    ← Divisor.pullbackAlong_pullbackAlong β j hβ hj (RingHom.IsIntegral.trans _ _ hβ hj) D]

theorem pullbackAlongHom_correspondence
    (α β : F →ₐ[K] A) (hα : α.toRingHom.IsIntegral) (hβ : β.toRingHom.IsIntegral)
    (hFIβ : FundamentalIdentityAlong K β hβ) (hfinα : FiniteAlong K α) (hNα : NormFormulaAlong K α hfinα)
    (α' β' : B →ₐ[K] E) (hα' : α'.toRingHom.IsIntegral) (hβ' : β'.toRingHom.IsIntegral)
    (hFIβ' : FundamentalIdentityAlong K β' hβ') (hfinα' : FiniteAlong K α')
    (hNα' : NormFormulaAlong K α' hfinα')
    (ι : F →ₐ[K] B) (hι : ι.toRingHom.IsIntegral) (hFIι : FundamentalIdentityAlong K ι hι)
    (j : A →ₐ[K] E) (hj : j.toRingHom.IsIntegral)
    (hsqβ : β'.comp ι = j.comp β)
    (hex : ∀ E₀ : Divisor K A, Divisor.pullbackAlong ι hι (Divisor.pushforwardAlong α hα E₀)
      = Divisor.pushforwardAlong α' hα' (Divisor.pullbackAlong j hj E₀))
    (x : Pic0 K F) :
    Pic0.pullbackAlongHom ι hι hFIι (Pic0.correspondence β α hβ hα hFIβ hfinα hNα x)
      = Pic0.correspondence β' α' hβ' hα' hFIβ' hfinα' hNα' (Pic0.pullbackAlongHom ι hι hFIι x) := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [Pic0.correspondence_mk, Pic0.pullbackAlongHom_mk, Pic0.pullbackAlongHom_mk, Pic0.correspondence_mk]
  refine congrArg Pic0.mk (Subtype.ext ?_)
  show Divisor.pullbackAlong ι hι (Divisor.correspondence β α hβ hα (D : Divisor K F))
    = Divisor.correspondence β' α' hβ' hα' (Divisor.pullbackAlong ι hι (D : Divisor K F))
  exact pullbackAlong_correspondence α β hα hβ α' β' hα' hβ' ι hι j hj hsqβ hex D

end Exchange

section GlueGeneric

variable {K L₀ : Type*} [Field K] [Field L₀] [Algebra K L₀]
variable {A B : Type*} [Field A] [Field B] [Algebra K A] [Algebra K B]

theorem adjoin_range_union_range_eq_top (E EA EB : IntermediateField K L₀)
    (u : A →ₐ[K] E) (v : B →ₐ[K] E) (hu : u.toRingHom.IsIntegral)
    (hA : EA ≤ IntermediateField.adjoin K (Set.range fun z : A => ((u z : E) : L₀)))
    (hB : EB ≤ IntermediateField.adjoin K (Set.range fun z : B => ((v z : E) : L₀)))
    (hGEN : E ≤ EA ⊔ EB) :
    Algebra.adjoin K (Set.range u ∪ Set.range v) = ⊤ := by
  set S : Subalgebra K E := Algebra.adjoin K (Set.range u ∪ Set.range v) with hSdef

  have hinv : ∀ x ∈ S, x⁻¹ ∈ S := by
    letI := AlgebraicCurve.algebraAlong u
    let S₁ : Subalgebra A E :=
      { S.toSubsemiring with
        algebraMap_mem' := fun k => Algebra.subset_adjoin (Or.inl (Set.mem_range_self k)) }
    intro x hx
    have hint : IsIntegral A x := hu x
    have halg : IsAlgebraic A x := hint.isAlgebraic
    exact Subalgebra.inv_mem_of_algebraic S₁ (x := ⟨x, hx⟩) halg
  let T : IntermediateField K E := S.toIntermediateField hinv
  have hle : E ≤ IntermediateField.lift T := by
    refine hGEN.trans (sup_le (hA.trans ?_) (hB.trans ?_))
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨z, rfl⟩
      exact (IntermediateField.mem_lift (u z)).mpr (Algebra.subset_adjoin (Or.inl (Set.mem_range_self z)))
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨z, rfl⟩
      exact (IntermediateField.mem_lift (v z)).mpr (Algebra.subset_adjoin (Or.inr (Set.mem_range_self z)))
  have hTtop : T = ⊤ := by
    apply IntermediateField.lift_injective E
    rw [IntermediateField.lift_top]
    exact le_antisymm (IntermediateField.lift_le T) hle
  have h := congrArg IntermediateField.toSubalgebra hTtop
  rwa [toSubalgebra_toIntermediateField, IntermediateField.top_toSubalgebra] at h

end GlueGeneric

namespace FiniteGeneric

open Cardinal

section Exchange

variable {L E : Type*} [Field L] [Field E] [Algebra L E]

open scoped IntermediateField.algebraAdjoinAdjoin in
theorem isAlgebraic_algebraAdjoin {x : E} [Algebra.IsAlgebraic L⟮x⟯ E] :
    Algebra.IsAlgebraic (Algebra.adjoin L ({x} : Set E)) E :=
  Algebra.IsAlgebraic.trans (Algebra.adjoin L ({x} : Set E)) L⟮x⟯ E

theorem isAlgebraic_adjoin_of_transcendental {x : E} (hx : Transcendental L x)
    [Algebra.IsAlgebraic L⟮x⟯ E] {y : E} (hy : Transcendental L y) :
    Algebra.IsAlgebraic L⟮y⟯ E := by
  have indx : AlgebraicIndependent L (fun _ : Unit => x) :=
    algebraicIndependent_unique_type_iff.mpr hx
  have indy : AlgebraicIndependent L (fun _ : Unit => y) :=
    algebraicIndependent_unique_type_iff.mpr hy
  have hrx : Set.range (fun _ : Unit => x) = {x} := Set.range_const
  have hry : Set.range (fun _ : Unit => y) = {y} := Set.range_const
  have algx : Algebra.IsAlgebraic (Algebra.adjoin L (Set.range fun _ : Unit => x)) E := by
    rw [hrx]
    exact isAlgebraic_algebraAdjoin
  have basx : IsTranscendenceBasis L (fun _ : Unit => x) :=
    indx.isTranscendenceBasis_iff_isAlgebraic.mpr algx
  have basy : IsTranscendenceBasis L (fun _ : Unit => y) :=
    indy.isTranscendenceBasis_of_lift_trdeg_le_of_finite (le_of_eq basx.lift_cardinalMk_eq_trdeg.symm)
  have h := basy.isAlgebraic_field
  rwa [hry] at h

theorem finiteDimensional_adjoin_of_transcendental {x : E} (hx : Transcendental L x)
    [FiniteDimensional L⟮x⟯ E] {y : E} (hy : Transcendental L y) :
    FiniteDimensional L⟮y⟯ E := by
  haveI : Algebra.IsAlgebraic L⟮y⟯ E := isAlgebraic_adjoin_of_transcendental hx hy
  obtain ⟨s, hs⟩ := Module.finite_def.mp (inferInstance : Module.Finite L⟮x⟯ E)
  set S : Set E := insert x (↑s : Set E) with hS
  haveI : Finite S := (s.finite_toSet.insert x).to_subtype
  set K' : IntermediateField L⟮y⟯ E := IntermediateField.adjoin L⟮y⟯ S with hK'def
  haveI hK'fin : FiniteDimensional L⟮y⟯ K' :=
    IntermediateField.finiteDimensional_adjoin fun z _ => (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
  have hxK' : x ∈ K' := IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
  have hLx_le : ∀ c : L⟮x⟯, (c : E) ∈ K' := by
    intro c
    have hle : L⟮x⟯ ≤ K'.restrictScalars L := IntermediateField.adjoin_simple_le_iff.mpr hxK'
    exact hle c.2
  have hK' : K' = ⊤ := by
    suffices h : ∀ e : E, e ∈ K' from eq_top_iff.mpr fun e _ => h e
    intro e
    have he : e ∈ Submodule.span L⟮x⟯ (↑s : Set E) := by rw [hs]; exact Submodule.mem_top
    induction he using Submodule.span_induction with
    | mem z hz => exact IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ hz)
    | zero => exact zero_mem _
    | add u v _ _ hu hv => exact add_mem hu hv
    | smul c z _ hz =>
        rw [IntermediateField.smul_def, smul_eq_mul] at *
        show (c : E) * z ∈ K'
        exact mul_mem (hLx_le c) hz
  have htop : FiniteDimensional L⟮y⟯ (⊤ : IntermediateField L⟮y⟯ E) := by
    rw [← hK']; exact hK'fin
  exact LinearEquiv.finiteDimensional
    (IntermediateField.topEquiv (F := L⟮y⟯) (E := E)).toLinearEquiv

end Exchange

section Along

variable {L F F' : Type*} [Field L] [Field F] [Field F'] [Algebra L F] [Algebra L F']

theorem finiteAlong_of_transcendental (φ : F →ₐ[L] F') {x₀ : F} (hx₀ : Transcendental L x₀)
    {x₁ : F'} (hx₁ : Transcendental L x₁) [FiniteDimensional L⟮x₁⟯ F'] :
    AlgebraicCurve.FiniteAlong L φ := by
  letI := AlgebraicCurve.algebraAlong φ
  haveI := AlgebraicCurve.isScalarTower_along φ

  have hy₀ : Transcendental L (φ x₀) := by
    have h := (transcendental_algebraMap_iff (R := L) (S := F) (A := F')
      (φ.toRingHom.injective)).mpr hx₀
    exact h
  haveI hfin : FiniteDimensional L⟮φ x₀⟯ F' := finiteDimensional_adjoin_of_transcendental hx₁ hy₀

  set E₀ : IntermediateField L F := L⟮x₀⟯ with hE₀
  have hmap : E₀.map φ = L⟮φ x₀⟯ := by
    rw [hE₀, IntermediateField.adjoin_map, Set.image_singleton]
  let e : E₀ ≃ₐ[L] L⟮φ x₀⟯ := (E₀.equivMap φ).trans (IntermediateField.equivOfEq hmap)
  have he : ∀ w : E₀, ((e w : L⟮φ x₀⟯) : F') = φ (w : F) := by
    intro w
    rfl
  letI : Algebra E₀ F' := ((algebraMap F F').comp (algebraMap E₀ F)).toAlgebra
  haveI : IsScalarTower E₀ F F' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite E₀ F' := by
    refine Module.Finite.of_equiv_equiv (A₁ := L⟮φ x₀⟯) (B₁ := F') (A₂ := E₀) (B₂ := F')
      e.symm.toRingEquiv (RingEquiv.refl F') ?_
    refine RingHom.ext fun z => ?_
    obtain ⟨w, rfl⟩ := e.surjective z
    simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, RingEquiv.refl_apply]
    rw [show e.symm.toRingEquiv (e w) = w from e.symm_apply_apply w]
    show φ (w : F) = ((e w : L⟮φ x₀⟯) : F')
    rw [he]
  show Module.Finite F F'
  exact Module.Finite.of_restrictScalars_finite E₀ F F'

theorem isIntegral_of_finiteAlong (φ : F →ₐ[L] F') (h : AlgebraicCurve.FiniteAlong L φ) :
    φ.toRingHom.IsIntegral := by
  letI := AlgebraicCurve.algebraAlong φ
  haveI : Module.Finite F F' := h
  haveI : Algebra.IsIntegral F F' := Algebra.IsIntegral.of_finite F F'
  exact fun x => Algebra.IsIntegral.isIntegral x

end Along

end FiniteGeneric

section Roofs

local notation "𝕂" => AlgebraicClosure ℚ

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (q : ℕ) [NeZero q]

abbrev RH : IntermediateField 𝕂 (LaurentSeries 𝕂) := laurentBaseChange 𝕂 (xHTopFunctionFieldC ℚ M H (M * q))
abbrev R1 : IntermediateField 𝕂 (LaurentSeries 𝕂) := laurentBaseChange 𝕂 (x1x0FunctionFieldC ℚ M (M * q))

theorem gamma1_le_gammaH : Gamma1 M ≤ CohCarrier.GammaH M H := by
  intro A hA
  rw [Gamma1_mem] at hA
  obtain ⟨-, h11, h10⟩ := hA
  have hA0 : A ∈ Gamma0 M := Gamma0_mem.mpr h10
  refine CohCarrier.mem_GammaH_iff.mpr ⟨hA0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨A, hA0⟩ = 1 := by
    apply Units.ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    exact h11
  rw [this]; exact one_mem _

theorem T_mem_Gamma1_inf_Gamma0 : ModularGroup.T ∈ Gamma1 M ⊓ Gamma0 (M * q) := by
  refine ⟨by simp [Gamma1_mem, ModularGroup.T], ?_⟩
  simp [Gamma0_mem, ModularGroup.T]

theorem T_mem_Gamma1 : ModularGroup.T ∈ Gamma1 M := by simp [Gamma1_mem, ModularGroup.T]

theorem T_mem_gammaH_inf_Gamma0 : ModularGroup.T ∈ CohCarrier.GammaH M H ⊓ Gamma0 (M * q) :=
  ⟨gamma1_le_gammaH M H (T_mem_Gamma1 M), (T_mem_Gamma1_inf_Gamma0 M q).2⟩

scoped instance finiteIndex_gammaH' : (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (gamma1_le_gammaH M H)

scoped instance finiteIndex_Gamma1_inf_Gamma0 : (Gamma1 M ⊓ Gamma0 (M * q)).FiniteIndex := by
  haveI : NeZero (M * q) := ⟨mul_ne_zero (NeZero.ne M) (NeZero.ne q)⟩
  infer_instance

scoped instance finiteIndex_gammaH_inf_Gamma0 : (CohCarrier.GammaH M H ⊓ Gamma0 (M * q)).FiniteIndex :=
  Subgroup.finiteIndex_of_le (show Gamma1 M ⊓ Gamma0 (M * q) ≤ CohCarrier.GammaH M H ⊓ Gamma0 (M * q) from
    inf_le_inf_right _ (gamma1_le_gammaH M H))

theorem laurentBaseChange_mono' (L : Type*) [Field L] [Algebra ℚ L] {F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)}
    (h : F₀ ≤ F₁) : laurentBaseChange L F₀ ≤ laurentBaseChange L F₁ := by
  rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
  rintro _ ⟨y, hy, rfl⟩
  exact coeffEmb_mem_laurentBaseChange L (h hy)

theorem rH_le_r1 : RH M H q ≤ R1 M q :=
  laurentBaseChange_mono' 𝕂 (qExpFunctionFieldC_mono ℚ (inf_le_inf_right _ (gamma1_le_gammaH M H)))

def roofJ : ↥(RH M H q) →ₐ[𝕂] ↥(R1 M q) := IntermediateField.inclusion (rH_le_r1 M H q)

@[scoped simp] theorem coe_roofJ (x : ↥(RH M H q)) : ((roofJ M H q x : ↥(R1 M q)) : LaurentSeries 𝕂) = (x : LaurentSeries 𝕂) :=
  IntermediateField.coe_inclusion _ x

theorem exists_tf_RH : ∃ x : ↥(RH M H q), Transcendental 𝕂 x ∧ FiniteDimensional 𝕂⟮x⟯ ↥(RH M H q) :=
  ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange 𝕂
    (CohCarrier.GammaH M H ⊓ Gamma0 (M * q)) (T_mem_gammaH_inf_Gamma0 M H q)

theorem exists_tf_R1 : ∃ x : ↥(R1 M q), Transcendental 𝕂 x ∧ FiniteDimensional 𝕂⟮x⟯ ↥(R1 M q) :=
  ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange 𝕂
    (Gamma1 M ⊓ Gamma0 (M * q)) (T_mem_Gamma1_inf_Gamma0 M q)

theorem exists_tf_FH : ∃ x : ↥(xHFunctionFieldBar M H), Transcendental 𝕂 x ∧ FiniteDimensional 𝕂⟮x⟯ ↥(xHFunctionFieldBar M H) :=
  ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange 𝕂
    (CohCarrier.GammaH M H) (gamma1_le_gammaH M H (T_mem_Gamma1 M))

theorem isIntegral_roofJ : (roofJ M H q).toRingHom.IsIntegral := by
  obtain ⟨x₀, hx₀, -⟩ := exists_tf_RH M H q
  obtain ⟨x₁, hx₁, hfin⟩ := exists_tf_R1 M q
  haveI := hfin
  exact FiniteGeneric.isIntegral_of_finiteAlong _ (FiniteGeneric.finiteAlong_of_transcendental _ hx₀ hx₁)

theorem charZero_K : CharZero 𝕂 := charZero_of_injective_algebraMap (algebraMap ℚ 𝕂).injective

scoped instance charZero_FH : CharZero ↥(xHFunctionFieldBar M H) := by
  haveI : CharZero 𝕂 := charZero_K
  exact charZero_of_injective_algebraMap (algebraMap 𝕂 _).injective

end Roofs

end TransportU
p2m_reactivate "P2MW.S_ModularCurve_pullbackAlongHom_heckeOperatorHAlong_eq_heckeOperatorOneBar_pullbackAlongHom.TransportU"

end
p2m_reactivate "P2MW.S_ModularCurve_pullbackAlongHom_heckeOperatorHAlong_eq_heckeOperatorOneBar_pullbackAlongHom.TransportU"

p2m_open "AlgebraicCurve~finiteDimensional_adjoin_of_transcendental" in open TransportU ModularCurve IntermediateField CongruenceSubgroup in

theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (hin : ModularCurve.HeckeDiamondInputsAll M)
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar M)]
    (ι : ↥(ModularCurve.xHFunctionFieldBar M H) →ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.x1FunctionFieldBar M))
    (hι : ∀ x : ↥(ModularCurve.xHFunctionFieldBar M H),
      ((ι x : ↥(ModularCurve.x1FunctionFieldBar M)) : LaurentSeries (AlgebraicClosure ℚ)) =
        (x : LaurentSeries (AlgebraicClosure ℚ)))
    (hint : ι.toRingHom.IsIntegral)
    (hFI : AlgebraicCurve.FundamentalIdentityAlong (AlgebraicClosure ℚ) ι hint)
    (q : ℕ) (hq : q.Prime) (hqM : q ∣ M)
    (x : AlgebraicCurve.Pic0 (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) :
    AlgebraicCurve.Pic0.pullbackAlongHom ι hint hFI
        (haveI : NeZero q := ⟨hq.ne_zero⟩; ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H q x) =
      ModularCurve.heckeOperatorOneBar M ⟨q, hq⟩ (AlgebraicCurve.Pic0.pullbackAlongHom ι hint hFI x) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩

  obtain ⟨hβd, hα1, hβ1, hP1, hfin1, hFI1, hN1⟩ := hin.1 ⟨q, hq⟩
  obtain ⟨h0, hαH, hβH, hPH, hfinH, hFIH, hNH⟩ := ModularCurve.heckeInputsHAlong (AlgebraicClosure ℚ) M H q
  haveI := hP1; haveI := hPH
  have e1 : ∀ y, heckeOperatorOneBar M ⟨q, hq⟩ y = heckePic0OneBar hα1 hβ1 hFI1 hfin1 hN1 y := fun y => by
    rw [heckeOperatorOneBar_apply]
    exact DFunLike.congr_fun (heckeOperatorOneAlong_eq hβd hα1 hβ1 hFI1 hfin1 hN1) y
  have eH : ∀ y, heckeOperatorHAlong (AlgebraicClosure ℚ) M H q y = heckePic0HBar hαH hβH hFIH hfinH hNH y := fun y =>
    DFunLike.congr_fun (heckeOperatorHAlong_eq h0 hαH hβH hFIH hfinH hNH) y

  set j := TransportU.roofJ M H q with hjdef
  have hj : j.toRingHom.IsIntegral := TransportU.isIntegral_roofJ M H q
  have hsqα : (heckeAlphaOneBar (AlgebraicClosure ℚ) M q).comp ι = j.comp (heckeAlphaHBar (AlgebraicClosure ℚ) M H q) := by
    apply AlgHom.ext; intro x; apply Subtype.ext
    rw [AlgHom.comp_apply, AlgHom.comp_apply, coe_heckeAlphaOneBar, hι, TransportU.coe_roofJ, coe_heckeAlphaHBar]
  have hsqβ : (heckeBetaOneBar (AlgebraicClosure ℚ) M q).comp ι = j.comp (heckeBetaHBar (AlgebraicClosure ℚ) M H q) := by
    apply AlgHom.ext; intro x; apply Subtype.ext
    rw [AlgHom.comp_apply, AlgHom.comp_apply, coe_heckeBetaOneBar M q hβd, hι, TransportU.coe_roofJ, coe_heckeBetaHBar M H q h0]

  have hex : ∀ E₀ : Divisor (AlgebraicClosure ℚ) ↥(TransportU.RH M H q),
      Divisor.pullbackAlong ι hint (Divisor.pushforwardAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H q) hαH E₀)
        = Divisor.pushforwardAlong (heckeAlphaOneBar (AlgebraicClosure ℚ) M q) hα1 (Divisor.pullbackAlong j hj E₀) := by
    intro E₀
    refine AlgebraicCurve.Divisor.pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong
      (heckeAlphaHBar (AlgebraicClosure ℚ) M H q) ι j (heckeAlphaOneBar (AlgebraicClosure ℚ) M q) hαH hint hj hα1 hsqα ?_ ?_ ?_ ?_ E₀
    ·
      obtain ⟨x₀, hx₀, -⟩ := TransportU.exists_tf_FH M H
      obtain ⟨x₁, hx₁, hfin⟩ := TransportU.exists_tf_R1 M q
      haveI := hfin
      exact FiniteGeneric.finiteAlong_of_transcendental _ hx₀ hx₁
    · exact AlgebraicCurve.separableAlong_of_charZero _ (RingHom.IsIntegral.trans _ _ hαH hj)
    · refine TransportU.adjoin_range_union_range_eq_top (TransportU.R1 M q) (TransportU.RH M H q)
        (laurentBaseChange (AlgebraicClosure ℚ) (x1FunctionField M)) j (heckeAlphaOneBar (AlgebraicClosure ℚ) M q) hj ?_ ?_ ?_
      · intro y hy
        exact IntermediateField.subset_adjoin _ _ ⟨⟨y, hy⟩, TransportU.coe_roofJ M H q _⟩
      · intro y hy
        exact IntermediateField.subset_adjoin _ _ ⟨⟨y, hy⟩, coe_heckeAlphaOneBar M q _⟩
      · rw [sup_comm]
        exact (ModularCurve.laurentBaseChange_x1FunctionField_sup_xHTopFunctionFieldC (AlgebraicClosure ℚ) M H q).ge
    · rw [← hsqα, AlgebraicCurve.finrankAlong_comp, ModularCurve.finrankAlong_heckeAlphaOneBar,
        ModularCurve.finrankAlong_heckeAlphaHBar_of_dvd (AlgebraicClosure ℚ) M H q hqM, if_pos hqM, mul_comm]

  show AlgebraicCurve.Pic0.pullbackAlongHom ι hint hFI (heckeOperatorHAlong (AlgebraicClosure ℚ) M H q x) = _
  rw [eH, e1]
  exact TransportU.pullbackAlongHom_correspondence (heckeAlphaHBar (AlgebraicClosure ℚ) M H q) (heckeBetaHBar (AlgebraicClosure ℚ) M H q)
    hαH hβH hFIH hfinH hNH (heckeAlphaOneBar (AlgebraicClosure ℚ) M q) (heckeBetaOneBar (AlgebraicClosure ℚ) M q)
    hα1 hβ1 hFI1 hfin1 hN1 ι hint hFI j hj hsqβ hex x

end S_ModularCurve_pullbackAlongHom_heckeOperatorHAlong_eq_heckeOperatorOneBar_pullbackAlongHom
end P2MW
export P2MW.S_ModularCurve_pullbackAlongHom_heckeOperatorHAlong_eq_heckeOperatorOneBar_pullbackAlongHom (solution)
