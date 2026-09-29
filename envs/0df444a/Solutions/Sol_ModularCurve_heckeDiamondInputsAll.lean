-- Prove2me | solution 1 for ModularCurve.heckeDiamondInputsAll
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/58a28fc8-6c82-5222-9ae1-5ad012a50a4e

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule
import Theorems.Thm_ModularCurve_qExpand_image_intFormRatiosC_subset
import Theorems.Thm_ModularCurve_exists_isDiamondAut
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_ModularCurve_exists_algEquiv_laurentBaseChange_cover
import Theorems.Thm_AlgebraicCurve_fundamentalIdentityAlong
import Theorems.Thm_AlgebraicCurve_normFormulaAlong
import Theorems.Thm_AlgebraicCurve_hasPrincipalDivisors_of_transcendental
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_heckeDiamondInputsAll
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one"

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups IntermediateField

namespace X1HDIGeneric

open Cardinal IntermediateField

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

theorem separableAlong_of_charZero [CharZero F] (φ : F →ₐ[L] F')
    (hφ : φ.toRingHom.IsIntegral) : AlgebraicCurve.SeparableAlong L φ := by
  letI := AlgebraicCurve.algebraAlong φ
  haveI : Algebra.IsIntegral F F' := ⟨fun x => hφ x⟩
  show Algebra.IsSeparable F F'
  infer_instance

end Along

end X1HDIGeneric

namespace X1HDIInputs

open ModularCurve AlgebraicCurve CongruenceSubgroup IntermediateField

section Groups

variable (M ℓ : ℕ)

theorem T_mem_Gamma1 : ModularGroup.T ∈ Gamma1 M := by
  simp [Gamma1_mem, ModularGroup.T]

theorem T_mem_Gamma1_inf_Gamma0 : ModularGroup.T ∈ Gamma1 M ⊓ Gamma0 (M * ℓ) := by
  refine ⟨T_mem_Gamma1 M, ?_⟩
  simp [Gamma0_mem, ModularGroup.T]

scoped instance finiteIndex_Gamma1_inf_Gamma0 [NeZero M] [NeZero ℓ] :
    (Gamma1 M ⊓ Gamma0 (M * ℓ)).FiniteIndex := by
  haveI : NeZero (M * ℓ) := ⟨mul_ne_zero (NeZero.ne M) (NeZero.ne ℓ)⟩
  infer_instance

theorem cocycle [NeZero ℓ] : ∀ γ ∈ Gamma1 M ⊓ Gamma0 (M * ℓ), ∃ γ₁ ∈ Gamma1 M,
    γ₁ 0 0 = γ 0 0 ∧ γ₁ 0 1 = (ℓ : ℤ) * γ 0 1 ∧ (ℓ : ℤ) * γ₁ 1 0 = γ 1 0 ∧ γ₁ 1 1 = γ 1 1 := by
  intro γ hγ
  obtain ⟨hγ1, hγ0⟩ := Subgroup.mem_inf.mp hγ
  have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe; rwa [Matrix.det_fin_two] at this
  have hMℓc : ((M * ℓ : ℕ) : ℤ) ∣ γ 1 0 := by
    have := Gamma0_mem.mp hγ0; rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  obtain ⟨c', hc'⟩ := hMℓc
  rw [Nat.cast_mul] at hc'
  have hdet' : Matrix.det !![(γ 0 0 : ℤ), (ℓ : ℤ) * γ 0 1; (M : ℤ) * c', γ 1 1] = 1 := by
    rw [Matrix.det_fin_two_of]; linear_combination hdet + (γ 0 1 : ℤ) * hc'
  refine ⟨⟨_, hdet'⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Gamma1_mem] at hγ1 ⊢
    obtain ⟨h00, h11, -⟩ := hγ1
    refine ⟨h00, h11, ?_⟩
    show (((M : ℤ) * c' : ℤ) : ZMod M) = 0
    push_cast; rw [ZMod.natCast_self, zero_mul]
  · rfl
  · rfl
  · show (ℓ : ℤ) * ((M : ℤ) * c') = γ 1 0
    linear_combination -hc'
  · rfl

end Groups

section Inputs

variable (L : Type*) [Field L] [Algebra ℚ L] (M ℓ : ℕ) [NeZero M] [NeZero ℓ]

theorem charZero_of_algebraRat : CharZero L :=
  charZero_of_injective_algebraMap (algebraMap ℚ L).injective

theorem heckeBetaOneDefined : HeckeBetaOneDefined M ℓ := by
  intro y hy
  have hsub := ModularCurve.qExpand_image_intFormRatiosC_subset ℚ (T_mem_Gamma1 M) ℓ (cocycle M ℓ)

  have hy' : y ∈ IntermediateField.adjoin ℚ (intFormRatiosC ℚ (Gamma1 M)) := hy
  have hmap : (IntermediateField.adjoin ℚ (intFormRatiosC ℚ (Gamma1 M))).map (qExpandₐ ℓ)
      ≤ IntermediateField.adjoin ℚ (intFormRatiosC ℚ (Gamma1 M ⊓ Gamma0 (M * ℓ))) := by
    rw [IntermediateField.adjoin_map]
    exact IntermediateField.adjoin.mono ℚ _ _ hsub
  exact hmap ⟨y, hy', rfl⟩

theorem exists_transcendental_bot :
    ∃ x₀ : laurentBaseChange L (x1FunctionField M), Transcendental L x₀ := by
  obtain ⟨x, hx, -⟩ :=
    ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange L (Gamma1 M)
      (T_mem_Gamma1 M)
  exact ⟨x, hx⟩

theorem exists_transcendental_finiteDimensional_top :
    ∃ x₁ : laurentBaseChange L (x1x0FunctionFieldC ℚ M (M * ℓ)), Transcendental L x₁ ∧
      FiniteDimensional L⟮x₁⟯ (laurentBaseChange L (x1x0FunctionFieldC ℚ M (M * ℓ))) :=
  ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange L
    (Gamma1 M ⊓ Gamma0 (M * ℓ)) (T_mem_Gamma1_inf_Gamma0 M ℓ)

theorem finiteAlong_alpha : FiniteAlong L (heckeAlphaOneBar L M ℓ) := by
  obtain ⟨x₀, hx₀⟩ := exists_transcendental_bot L M
  obtain ⟨x₁, hx₁, hfin⟩ := exists_transcendental_finiteDimensional_top L M ℓ
  haveI := hfin
  exact X1HDIGeneric.finiteAlong_of_transcendental _ hx₀ hx₁

theorem finiteAlong_beta : FiniteAlong L (heckeBetaOneBar L M ℓ) := by
  obtain ⟨x₀, hx₀⟩ := exists_transcendental_bot L M
  obtain ⟨x₁, hx₁, hfin⟩ := exists_transcendental_finiteDimensional_top L M ℓ
  haveI := hfin
  exact X1HDIGeneric.finiteAlong_of_transcendental _ hx₀ hx₁

theorem alphaIntegral : HeckeAlphaOneBarIntegral L M ℓ :=
  X1HDIGeneric.isIntegral_of_finiteAlong _ (finiteAlong_alpha L M ℓ)

theorem betaIntegral : HeckeBetaOneBarIntegral L M ℓ :=
  X1HDIGeneric.isIntegral_of_finiteAlong _ (finiteAlong_beta L M ℓ)

theorem hasPrincipalDivisors_top :
    HasPrincipalDivisors L (laurentBaseChange L (x1x0FunctionFieldC ℚ M (M * ℓ))) := by
  haveI : CharZero L := charZero_of_algebraRat L
  obtain ⟨x₁, hx₁, hfin⟩ := exists_transcendental_finiteDimensional_top L M ℓ
  haveI := hfin
  exact AlgebraicCurve.hasPrincipalDivisors_of_transcendental L x₁ hx₁

scoped instance charZero_bot : CharZero (laurentBaseChange L (x1FunctionField M)) := by
  haveI : CharZero L := charZero_of_algebraRat L
  exact charZero_of_injective_algebraMap (algebraMap L _).injective

theorem heckeInputsOneAlong : HeckeInputsOneAlong L M ℓ := by
  haveI := hasPrincipalDivisors_top L M ℓ
  have hα := alphaIntegral L M ℓ
  have hβ := betaIntegral L M ℓ
  have hfinα := finiteAlong_alpha L M ℓ
  have hfinβ := finiteAlong_beta L M ℓ
  refine heckeInputsOneAlong_intro (heckeBetaOneDefined M ℓ) hα hβ ?_ hfinα ?_
  · exact AlgebraicCurve.fundamentalIdentityAlong _ hβ hfinβ
      (X1HDIGeneric.separableAlong_of_charZero _ hβ)
  · exact AlgebraicCurve.normFormulaAlong _ hfinα
      (X1HDIGeneric.separableAlong_of_charZero _ hα)

end Inputs

section Diamond

variable (M : ℕ) [NeZero M]

theorem diamond_inputs (d : ℕ) (hd : Nat.Coprime d M) :
    (∃ σ : x1FunctionField M ≃ₐ[ℚ] x1FunctionField M, IsDiamondAut M d σ) ∧
      ∃ σ' : x1FunctionFieldBar M ≃ₐ[AlgebraicClosure ℚ] x1FunctionFieldBar M,
        IsBaseChangeAutOf (AlgebraicClosure ℚ) (diamondAut M d) σ' := by
  refine ⟨ModularCurve.exists_isDiamondAut M hd, ?_⟩
  obtain ⟨τ, hτ⟩ := ModularCurve.exists_algEquiv_laurentBaseChange_cover (AlgebraicClosure ℚ)
    (x1FunctionField M) (diamondAut M d).toRingEquiv
  exact ⟨τ, fun y => hτ y⟩

end Diamond

end X1HDIInputs
p2m_reactivate "P2MW.S_ModularCurve_heckeDiamondInputsAll.X1HDIInputs"

end
p2m_reactivate "P2MW.S_ModularCurve_heckeDiamondInputsAll.X1HDIInputs"

theorem solution (M : ℕ) [NeZero M] :
    ModularCurve.HeckeDiamondInputsAll M := by
  refine ⟨fun ℓ => ?_, fun d hd => X1HDIInputs.diamond_inputs M d hd⟩
  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  exact X1HDIInputs.heckeInputsOneAlong (AlgebraicClosure ℚ) M ℓ

end S_ModularCurve_heckeDiamondInputsAll
end P2MW
export P2MW.S_ModularCurve_heckeDiamondInputsAll (solution)
