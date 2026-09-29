-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.SlabL2.casimir_eq_smul_of_forall_isSmoothingKernel_casimir_smoothingOperator_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/dbf447b0-4528-57f8-ae8e-9acd00298d1d

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2KernelCasimir
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_casimir_archConvN_and_eq_of_forall_integral_kernelCasimir
import Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_casimir_apply_eq_kernelCasimir_archChart
import Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_smoothingOperator_eq_archConvN_and_exists_levelSet_subset
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_eq_smul_of_forall_isSmoothingKernel_casimir_smoothingOperator_eq_smul
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField AutomorphicForm Matrix MeasureTheory Topology Filter TopologicalSpace

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "SlabL2.kernelEnt SlabL2.kernelCasimir1 SlabL2.kernelCasimir2 SlabL2.kernelCasimir3 SlabL2.archChart SlabL2.archChart_apply SlabL2.archEntries SlabL2.IsSmoothArchFactor SlabL2.IsSmoothingKernel SlabL2.smoothingOperator AdelicGL localMaximalCompact3 componentAt3 WhittakerBlock.archDeriv WhittakerBlock.casimir1 WhittakerBlock.casimir2 WhittakerBlock.casimir3 finEmbedN SlabL2.casimir_archConvN_and_eq_of_forall_integral_kernelCasimir SlabL2.casimir_apply_eq_kernelCasimir_archChart SlabL2.smoothingOperator_eq_archConvN_and_exists_levelSet_subset"
namespace ArchConvCalculus
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

abbrev E33 : Type := Fin 3 → Fin 3 → ℝ

theorem realCoord_ofReal (r : ℝ) : StandardKernel.realCoord (StandardKernel.ofReal r) = r :=
  (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).apply_symm_apply r

def realEquiv : InfiniteAdeleRing ℚ ≃+* ℝ where
  toFun := StandardKernel.realCoord
  invFun := StandardKernel.ofReal
  left_inv := StandardKernel.ofReal_realCoord
  right_inv := realCoord_ofReal
  map_mul' := map_mul _
  map_add' := map_add _

theorem realEquiv_apply (x : InfiniteAdeleRing ℚ) : realEquiv x = StandardKernel.realCoord x := rfl

theorem realEquiv_symm_apply (r : ℝ) : realEquiv.symm r = StandardKernel.ofReal r := rfl

theorem continuous_realCoord : Continuous StandardKernel.realCoord :=
  (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).continuous.comp
    (continuous_apply Rat.infinitePlace)

def realHomeo : InfiniteAdeleRing ℚ ≃ₜ ℝ where
  toEquiv := realEquiv.toEquiv
  continuous_toFun := continuous_realCoord
  continuous_invFun := StandardKernel.continuous_ofReal

def ent (h : GL (Fin 3) (InfiniteAdeleRing ℚ)) : E33 :=
  fun a b => StandardKernel.realCoord ((h : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) a b)

theorem ent_apply (h : GL (Fin 3) (InfiniteAdeleRing ℚ)) (a b : Fin 3) :
    ent h a b = StandardKernel.realCoord ((h : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) a b) := rfl

theorem of_ent (h : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    Matrix.of (ent h) = ((StandardKernel.realGL h : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext a b; rfl

theorem of_ent_mul (h h' : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    Matrix.of (ent (h * h')) = Matrix.of (ent h) * Matrix.of (ent h') := by
  rw [of_ent, of_ent, of_ent, map_mul, Units.val_mul]

theorem of_ent_inv (h : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    Matrix.of (ent h⁻¹) = (Matrix.of (ent h))⁻¹ := by
  rw [of_ent, of_ent, map_inv, Matrix.coe_units_inv]

theorem det_of_ent_ne_zero (h : GL (Fin 3) (InfiniteAdeleRing ℚ)) : (Matrix.of (ent h)).det ≠ 0 := by
  rw [of_ent]
  exact Matrix.GeneralLinearGroup.det_ne_zero _

theorem continuous_ent : Continuous ent :=
  continuous_pi fun a => continuous_pi fun b =>
    continuous_realCoord.comp (Units.continuous_val.matrix_elem a b)

theorem archEntries_archInclN (h : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    SlabL2.archEntries (archInclN (Fin 3) ℚ h) = ent h := rfl

def toGinf : GL (Fin 3) ℝ →* GL (Fin 3) (InfiniteAdeleRing ℚ) :=
  Matrix.GeneralLinearGroup.map (realEquiv.symm : ℝ ≃+* InfiniteAdeleRing ℚ).toRingHom

def liftE (e : E33) (he : (Matrix.of e).det ≠ 0) : GL (Fin 3) (InfiniteAdeleRing ℚ) :=
  toGinf (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of e) he)

theorem coe_liftE (e : E33) (he : (Matrix.of e).det ≠ 0) (a b : Fin 3) :
    (liftE e he : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) a b = StandardKernel.ofReal (e a b) := rfl

theorem ent_liftE (e : E33) (he : (Matrix.of e).det ≠ 0) : ent (liftE e he) = e := by
  funext a b
  rw [ent_apply, coe_liftE, realCoord_ofReal]

theorem realGL_toGinf (u : GL (Fin 3) ℝ) : StandardKernel.realGL (toGinf u) = u := by
  ext a b
  exact realCoord_ofReal _

theorem toGinf_realGL (h : GL (Fin 3) (InfiniteAdeleRing ℚ)) : toGinf (StandardKernel.realGL h) = h := by
  ext a b
  exact StandardKernel.ofReal_realCoord _

theorem liftE_ent (h : GL (Fin 3) (InfiniteAdeleRing ℚ)) : liftE (ent h) (det_of_ent_ne_zero h) = h := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  rw [coe_liftE, ent_apply, StandardKernel.ofReal_realCoord]

theorem archRealLift3_eq (e : E33) (he : (Matrix.of e).det ≠ 0) :
    WhittakerBlock.archRealLift3 e = archInclN (Fin 3) ℚ (liftE e he) := by
  have hval : WhittakerBlock.archRealMat3 e =
      ((archInclN (Fin 3) ℚ (liftE e he) : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) := by
    rfl
  have hu : IsUnit (WhittakerBlock.archRealMat3 e) := ⟨archInclN (Fin 3) ℚ (liftE e he), hval.symm⟩
  unfold WhittakerBlock.archRealLift3
  rw [dif_pos hu]
  exact Units.ext (by rw [hu.unit_spec, hval])

theorem archInclN_eq_archRealLift3 (h : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    archInclN (Fin 3) ℚ h = WhittakerBlock.archRealLift3 (ent h) := by
  rw [archRealLift3_eq (ent h) (det_of_ent_ne_zero h), liftE_ent]

theorem continuous_archInclN : Continuous (archInclN (Fin 3) ℚ) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    show Continuous fun a : GL (Fin 3) (InfiniteAdeleRing ℚ) =>
      (((a : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i j,
        (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) : AdeleRing (𝓞 ℚ) ℚ)
    exact (Units.continuous_val.matrix_elem i j).prodMk continuous_const
  · refine continuous_matrix fun i j => ?_
    show Continuous fun a : GL (Fin 3) (InfiniteAdeleRing ℚ) =>
      ((((a⁻¹ : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i j,
        (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) : AdeleRing (𝓞 ℚ) ℚ)
    exact (Units.continuous_coe_inv.matrix_elem i j).prodMk continuous_const

theorem continuous_toGinf : Continuous toGinf :=
  Continuous.units_map _
    ((continuous_id.matrix_map StandardKernel.continuous_ofReal :
      Continuous fun m : Matrix (Fin 3) (Fin 3) ℝ => m.map StandardKernel.ofReal))

theorem continuous_liftE_subtype {T : Set E33} (hTloc : T ⊆ {m | (Matrix.of m).det ≠ 0}) :
    Continuous fun x : T => liftE x.1 (hTloc x.2) := by
  refine continuous_toGinf.comp ?_
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact continuous_subtype_val
  · have hfun : (fun x : T => (((Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of x.1) (hTloc x.2))⁻¹ :
        GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ)) = fun x : T => (Matrix.of x.1)⁻¹ :=
      funext fun x => Matrix.coe_units_inv _
    rw [hfun]
    refine continuous_iff_continuousAt.mpr fun x => ?_
    have hdet : IsUnit (Matrix.of x.1).det := isUnit_iff_ne_zero.mpr (hTloc x.2)
    have hc : ContinuousAt Ring.inverse (Matrix.of x.1).det := by
      simpa using NormedRing.inverse_continuousAt hdet.unit
    exact (continuousAt_matrix_inv (Matrix.of x.1) hc).comp (f := fun x : T => Matrix.of x.1)
      continuous_subtype_val.continuousAt

theorem isCompact_preimage_ent {T : Set E33} (hT : IsCompact T) (hTloc : T ⊆ {m | (Matrix.of m).det ≠ 0}) :
    IsCompact (ent ⁻¹' T) := by
  haveI : CompactSpace T := isCompact_iff_compactSpace.mp hT
  have hj := continuous_liftE_subtype hTloc
  have hsub : ent ⁻¹' T ⊆ Set.range fun x : T => liftE x.1 (hTloc x.2) := by
    intro a ha
    exact ⟨⟨ent a, ha⟩, liftE_ent a⟩
  exact (isCompact_range hj).of_isClosed_subset (hT.isClosed.preimage continuous_ent) hsub

theorem hasCompactSupport_comp_ent {β : E33 → ℂ} (hβ : SlabL2.IsSmoothArchFactor β) :
    HasCompactSupport fun h => β (ent h) :=
  (isCompact_preimage_ent hβ.2.1 hβ.2.2).of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal (fun _ ha => subset_closure ha) ((isClosed_tsupport β).preimage continuous_ent))

@[reducible] def ginfMeasurableSpace : MeasurableSpace (GL (Fin 3) (InfiniteAdeleRing ℚ)) :=
  AutomorphicForm.archGLBorelN (Fin 3) ℚ

attribute [local instance] ginfMeasurableSpace

theorem ginfBorelSpace : BorelSpace (GL (Fin 3) (InfiniteAdeleRing ℚ)) :=
  AutomorphicForm.borelSpace_archGLBorelN (Fin 3) ℚ

attribute [local instance] ginfBorelSpace

theorem locallyCompactSpace_ginf : LocallyCompactSpace (GL (Fin 3) (InfiniteAdeleRing ℚ)) :=
  AutomorphicForm.locallyCompactSpace_archGLN (Fin 3) ℚ

attribute [local instance] locallyCompactSpace_ginf

abbrev muInf : Measure (GL (Fin 3) (InfiniteAdeleRing ℚ)) := AutomorphicForm.archGLHaarN (Fin 3) ℚ

theorem isHaarMeasure_μ : muInf.IsHaarMeasure := AutomorphicForm.isHaarMeasure_archGLHaarN (Fin 3) ℚ

attribute [local instance] isHaarMeasure_μ

theorem archConvN_eq (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (α : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    archConvN (Fin 3) ℚ Φ α g = ∫ h, Φ (g * archInclN (Fin 3) ℚ h) * α h ∂muInf := rfl

theorem archConvN_mul_archInclN (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (α : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ)
    (y : AdelicGL 3 (𝓞 ℚ) ℚ) (l : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    archConvN (Fin 3) ℚ Φ α (y * archInclN (Fin 3) ℚ l) = archConvN (Fin 3) ℚ Φ (fun h => α (l⁻¹ * h)) y := by
  rw [archConvN_eq, archConvN_eq,
    ← integral_mul_left_eq_self (fun h => Φ (y * archInclN (Fin 3) ℚ h) * α (l⁻¹ * h)) l]
  simp only [map_mul, mul_assoc, inv_mul_cancel_left]

theorem integrable_mul_kernel (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hΦ : Continuous Φ) {β : E33 → ℂ}
    (hβ : SlabL2.IsSmoothArchFactor β) (y : AdelicGL 3 (𝓞 ℚ) ℚ) :
    Integrable (fun h => Φ (y * archInclN (Fin 3) ℚ h) * β (ent h)) muInf :=
  ((hΦ.comp (continuous_const.mul continuous_archInclN)).mul
    (hβ.1.continuous.comp continuous_ent)).integrable_of_hasCompactSupport (hasCompactSupport_comp_ent hβ).mul_left

theorem continuous_finEmbedN : Continuous (finEmbedN (Fin 3) (𝓞 ℚ) ℚ) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    show Continuous fun k : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ) =>
      (((1 : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i j,
        (k : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) : AdeleRing (𝓞 ℚ) ℚ)
    exact continuous_const.prodMk (Units.continuous_val.matrix_elem i j)
  · refine continuous_matrix fun i j => ?_
    show Continuous fun k : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ) =>
      (((1 : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i j,
        ((k⁻¹ : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) :
        AdeleRing (𝓞 ℚ) ℚ)
    exact continuous_const.prodMk (Units.continuous_coe_inv.matrix_elem i j)

theorem ent_eq_kernelEnt : ent = SlabL2.kernelEnt := rfl

theorem archDeriv_const_mul (a : ℂ) (G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (i j : Fin 3) :
    WhittakerBlock.archDeriv i j (fun y => a * G y) = fun y => a * WhittakerBlock.archDeriv i j G y := by
  funext y
  unfold WhittakerBlock.archDeriv
  exact deriv_const_mul_field a

theorem casimir1_const_mul (a : ℂ) (G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    WhittakerBlock.casimir1 (fun y => a * G y) = fun y => a * WhittakerBlock.casimir1 G y := by
  funext y
  show ∑ i : Fin 3, WhittakerBlock.archDeriv i i (fun y => a * G y) y = a * ∑ i : Fin 3, WhittakerBlock.archDeriv i i G y
  simp only [archDeriv_const_mul, Finset.mul_sum]

theorem casimir2_const_mul (a : ℂ) (G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    WhittakerBlock.casimir2 (fun y => a * G y) = fun y => a * WhittakerBlock.casimir2 G y := by
  funext y
  show ∑ i : Fin 3, ∑ j : Fin 3, WhittakerBlock.archDeriv i j (WhittakerBlock.archDeriv j i fun y => a * G y) y =
    a * ∑ i : Fin 3, ∑ j : Fin 3, WhittakerBlock.archDeriv i j (WhittakerBlock.archDeriv j i G) y
  simp only [archDeriv_const_mul, Finset.mul_sum]

theorem casimir3_const_mul (a : ℂ) (G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    WhittakerBlock.casimir3 (fun y => a * G y) = fun y => a * WhittakerBlock.casimir3 G y := by
  funext y
  show ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, WhittakerBlock.archDeriv i j
      (WhittakerBlock.archDeriv j k (WhittakerBlock.archDeriv k i fun y => a * G y)) y =
    a * ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      WhittakerBlock.archDeriv i j (WhittakerBlock.archDeriv j k (WhittakerBlock.archDeriv k i G)) y
  simp only [archDeriv_const_mul, Finset.mul_sum]

theorem isSmoothArchFactor_sub_const_mul {β γ : E33 → ℂ} (hβ : SlabL2.IsSmoothArchFactor β)
    (hγ : SlabL2.IsSmoothArchFactor γ) (c : ℂ) : SlabL2.IsSmoothArchFactor fun m => γ m - c * β m := by
  have hsupp : Function.support (fun m => γ m - c * β m) ⊆ tsupport γ ∪ tsupport β := by
    intro m hm
    by_contra h
    simp only [Set.mem_union, not_or] at h
    exact hm (show γ m - c * β m = 0 by
      rw [image_eq_zero_of_notMem_tsupport h.1, image_eq_zero_of_notMem_tsupport h.2, mul_zero, sub_zero])
  refine ⟨hγ.1.sub (contDiff_const.mul hβ.1), ?_, ?_⟩
  · exact HasCompactSupport.of_support_subset_isCompact (hγ.2.1.union hβ.2.1) hsupp
  · exact (closure_minimal hsupp ((isClosed_tsupport γ).union (isClosed_tsupport β))).trans
      (Set.union_subset hγ.2.2 hβ.2.2)

theorem weak_eq_of_forall_isSmoothingKernel
    (cas : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) (Ω : (E33 → ℂ) → (E33 → ℂ))
    (hcas_mul : ∀ (a : ℂ) (G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), cas (fun y => a * G y) = fun y => a * cas G y)
    (hcas_conv : ∀ (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), Continuous Φ → ∀ {β : E33 → ℂ}, SlabL2.IsSmoothArchFactor β →
      cas (archConvN (Fin 3) ℚ Φ fun h => β (ent h)) = archConvN (Fin 3) ℚ Φ fun h => Ω β (ent h))
    (hΩ : ∀ {β : E33 → ℂ}, SlabL2.IsSmoothArchFactor β → SlabL2.IsSmoothArchFactor (Ω β))
    (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hFc : Continuous F) (c : ℂ)
    (h : ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, SlabL2.IsSmoothingKernel φ →
      cas (SlabL2.smoothingOperator φ F) = c • SlabL2.smoothingOperator φ F)
    (x : AdelicGL 3 (𝓞 ℚ) ℚ) {β : E33 → ℂ} (hβ : SlabL2.IsSmoothArchFactor β) :
    ∫ h, F (x * archInclN (Fin 3) ℚ h) * Ω β (ent h) ∂muInf = c * ∫ h, F (x * archInclN (Fin 3) ℚ h) * β (ent h) ∂muInf := by
  have hC := SlabL2.smoothingOperator_eq_archConvN_and_exists_levelSet_subset

  set g : E33 → ℂ := fun m => Ω β m - c * β m with hg
  have hgs : SlabL2.IsSmoothArchFactor g := isSmoothArchFactor_sub_const_mul hβ (hΩ hβ) c

  suffices hzero : ∫ h, F (x * archInclN (Fin 3) ℚ h) * g (ent h) ∂muInf = 0 by
    have hI1 := integrable_mul_kernel F hFc (hΩ hβ) x
    have hI2 := integrable_mul_kernel F hFc hβ x
    have : ∫ h, F (x * archInclN (Fin 3) ℚ h) * g (ent h) ∂muInf =
        ∫ h, F (x * archInclN (Fin 3) ℚ h) * Ω β (ent h) ∂muInf -
          c * ∫ h, F (x * archInclN (Fin 3) ℚ h) * β (ent h) ∂muInf := by
      rw [← integral_const_mul, ← integral_sub hI1 (hI2.const_mul c)]
      congr 1; funext h; simp only [hg]; ring
    rw [this] at hzero
    exact sub_eq_zero.mp hzero

  have hlevel : ∀ (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ)))
      (Ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), Continuous Ψ →
      (∀ y, SlabL2.smoothingOperator (fun y => β (SlabL2.archEntries y) *
        Set.indicator {z : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p z ∈ K' p} (fun _ => (1 : ℂ)) y) F y =
          archConvN (Fin 3) ℚ Ψ (fun h => β (SlabL2.kernelEnt h)) y) →
      (∀ p, IsOpen (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ))) ∧ IsCompact (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ)))) →
      (∀ᶠ p in Filter.cofinite, K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p) →
      ∫ h, Ψ (x * archInclN (Fin 3) ℚ h) * g (ent h) ∂muInf = 0 := by
    intro K' Ψ hΨc hsm hK'1 hK'2
    set φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ := fun y => β (SlabL2.archEntries y) *
      Set.indicator {z : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p z ∈ K' p} (fun _ => (1 : ℂ)) y with hφdef
    have hφ : SlabL2.IsSmoothingKernel φ := ⟨β, K', hβ, hK'1, hK'2, fun _ => rfl⟩
    have hsm' : SlabL2.smoothingOperator φ F = archConvN (Fin 3) ℚ Ψ (fun h => β (ent h)) := funext hsm
    have heq := h φ hφ
    rw [hsm', hcas_conv Ψ hΨc hβ] at heq
    have hx := congrFun heq x
    simp only [Pi.smul_apply, smul_eq_mul] at hx
    rw [archConvN_eq, archConvN_eq] at hx
    have hI1 := integrable_mul_kernel Ψ hΨc (hΩ hβ) x
    have hI2 := integrable_mul_kernel Ψ hΨc hβ x
    have : ∫ h, Ψ (x * archInclN (Fin 3) ℚ h) * g (ent h) ∂muInf =
        ∫ h, Ψ (x * archInclN (Fin 3) ℚ h) * Ω β (ent h) ∂muInf -
          c * ∫ h, Ψ (x * archInclN (Fin 3) ℚ h) * β (ent h) ∂muInf := by
      rw [← integral_const_mul, ← integral_sub hI1 (hI2.const_mul c)]
      congr 1; funext h; simp only [hg]; ring
    rw [this, hx, sub_self]

  have hS : IsCompact (ent ⁻¹' tsupport g) := isCompact_preimage_ent hgs.2.1 hgs.2.2
  set C : Set (AdelicGL 3 (𝓞 ℚ) ℚ) := (fun h => x * archInclN (Fin 3) ℚ h) '' (ent ⁻¹' tsupport g) with hCdef
  have hCc : IsCompact C := hS.image (continuous_const.mul continuous_archInclN)
  have hbound : ∀ ε : ℝ, 0 < ε → ‖∫ h, F (x * archInclN (Fin 3) ℚ h) * g (ent h) ∂muInf‖ ≤
      ε * ∫ h, ‖g (ent h)‖ ∂muInf := by
    intro ε hε

    set D : AdelicGL 3 (𝓞 ℚ) ℚ × GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ) → ℂ :=
      fun q => F (q.1 * finEmbedN (Fin 3) (𝓞 ℚ) ℚ q.2) - F q.1 with hD
    have hDc : Continuous D := (hFc.comp (continuous_fst.mul (continuous_finEmbedN.comp continuous_snd))).sub
      (hFc.comp continuous_fst)
    have hO : IsOpen {q : AdelicGL 3 (𝓞 ℚ) ℚ × GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ) | ‖D q‖ < ε} :=
      isOpen_lt (continuous_norm.comp hDc) continuous_const
    have hsub : C ×ˢ ({1} : Set (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) ⊆
        {q : AdelicGL 3 (𝓞 ℚ) ℚ × GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ) | ‖D q‖ < ε} := by
      rintro ⟨y, k⟩ ⟨-, hk⟩
      rw [Set.mem_singleton_iff] at hk
      subst hk
      simp only [Set.mem_setOf_eq, hD, map_one, mul_one, sub_self, norm_zero]
      exact hε
    obtain ⟨U, V, hUo, hVo, hCU, h1V, hUV⟩ := generalized_tube_lemma hCc isCompact_singleton hO hsub
    have hV1 : V ∈ 𝓝 (1 : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := hVo.mem_nhds (h1V (Set.mem_singleton 1))
    obtain ⟨K', hK'1, hK'2, hK'V⟩ := hC.2 V hV1
    obtain ⟨Ψ, N, hΨc, hNpos, hsm, hclose⟩ := hC.1 β K' _ F hβ hK'1 hK'2 (fun _ => rfl) hFc
    have hclose' : ∀ y ∈ C, ‖F y - ((N : ℂ)⁻¹) * Ψ y‖ ≤ ε := by
      intro y hy
      have hest : ‖Ψ y - (N : ℂ) * F y‖ ≤ ε * N :=
        hclose y ε fun k hk => le_of_lt (hUV (Set.mk_mem_prod (hCU hy) (hK'V hk)) : ‖D (y, k)‖ < ε)
      have hscale : F y - ((N : ℂ)⁻¹) * Ψ y = -((N : ℂ)⁻¹) * (Ψ y - (N : ℂ) * F y) := by
        have hN0 : (N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hNpos.ne'
        field_simp
        ring
      rw [hscale, norm_mul, norm_neg, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hNpos]
      calc N⁻¹ * ‖Ψ y - (N : ℂ) * F y‖ ≤ N⁻¹ * (ε * N) := by gcongr
        _ = ε := by field_simp

    have hIF := integrable_mul_kernel F hFc hgs x
    have hIΨ := integrable_mul_kernel Ψ hΨc hgs x
    have hA : Integrable (fun h => (F (x * archInclN (Fin 3) ℚ h) - ((N : ℂ)⁻¹) * Ψ (x * archInclN (Fin 3) ℚ h)) *
        g (ent h)) muInf := by
      refine (hIF.sub (hIΨ.const_mul ((N : ℂ)⁻¹))).congr (Filter.Eventually.of_forall fun h => ?_)
      simp only [Pi.sub_apply]
      ring
    have hB : Integrable (fun h => ((N : ℂ)⁻¹) * (Ψ (x * archInclN (Fin 3) ℚ h) * g (ent h))) muInf :=
      hIΨ.const_mul _
    have hsplit : ∫ h, F (x * archInclN (Fin 3) ℚ h) * g (ent h) ∂muInf =
        ∫ h, (F (x * archInclN (Fin 3) ℚ h) - ((N : ℂ)⁻¹) * Ψ (x * archInclN (Fin 3) ℚ h)) * g (ent h) ∂muInf +
          ((N : ℂ)⁻¹) * ∫ h, Ψ (x * archInclN (Fin 3) ℚ h) * g (ent h) ∂muInf := by
      rw [← integral_const_mul, ← integral_add hA hB]
      congr 1; funext h; ring
    rw [hsplit, hlevel K' Ψ hΨc hsm hK'1 hK'2, mul_zero, add_zero]
    have hIg : Integrable (fun h => ‖g (ent h)‖) muInf :=
      ((hgs.1.continuous.comp continuous_ent).integrable_of_hasCompactSupport (hasCompactSupport_comp_ent hgs)).norm
    calc ‖∫ h, (F (x * archInclN (Fin 3) ℚ h) - ((N : ℂ)⁻¹) * Ψ (x * archInclN (Fin 3) ℚ h)) * g (ent h) ∂muInf‖
        ≤ ∫ h, ε * ‖g (ent h)‖ ∂muInf := by
          refine norm_integral_le_of_norm_le (hIg.const_mul ε) (Filter.Eventually.of_forall fun h => ?_)
          by_cases hh : h ∈ ent ⁻¹' tsupport g
          · rw [norm_mul]
            exact mul_le_mul_of_nonneg_right (hclose' _ ⟨h, hh, rfl⟩) (norm_nonneg _)
          · simp [image_eq_zero_of_notMem_tsupport hh]
      _ = ε * ∫ h, ‖g (ent h)‖ ∂muInf := integral_const_mul ε _

  have hM : 0 ≤ ∫ h, ‖g (ent h)‖ ∂muInf := integral_nonneg fun _ => norm_nonneg _
  refine norm_le_zero_iff.mp (le_of_forall_pos_le_add fun ε hε => ?_)
  rw [zero_add]
  have := hbound (ε / (∫ h, ‖g (ent h)‖ ∂muInf + 1)) (by positivity)
  refine this.trans ?_
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith

theorem archChart_kernelEnt (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (x : AdelicGL 3 (𝓞 ℚ) ℚ) (h : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    SlabL2.archChart F x (SlabL2.kernelEnt h) = F (x * archInclN (Fin 3) ℚ h) := by
  rw [SlabL2.archChart_apply, ← ent_eq_kernelEnt, ← archInclN_eq_archRealLift3]

theorem casimir_eq_smul_of_forall_isSmoothingKernel
    (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hFc : Continuous F) (hFs : WhittakerBlock.IsArchSmooth3 F) (c₁ c₂ c₃ : ℂ)
    (h : ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, SlabL2.IsSmoothingKernel φ →
      WhittakerBlock.casimir1 (SlabL2.smoothingOperator φ F) = c₁ • SlabL2.smoothingOperator φ F ∧
        WhittakerBlock.casimir2 (SlabL2.smoothingOperator φ F) = c₂ • SlabL2.smoothingOperator φ F ∧
          WhittakerBlock.casimir3 (SlabL2.smoothingOperator φ F) = c₃ • SlabL2.smoothingOperator φ F) :
    WhittakerBlock.casimir1 F = c₁ • F ∧ WhittakerBlock.casimir2 F = c₂ • F ∧ WhittakerBlock.casimir3 F = c₃ • F := by
  have hK := SlabL2.casimir_archConvN_and_eq_of_forall_integral_kernelCasimir

  have h1 : ∀ x : AdelicGL 3 (𝓞 ℚ) ℚ, ∀ β : E33 → ℂ, SlabL2.IsSmoothArchFactor β →
      ∫ h, SlabL2.archChart F x (SlabL2.kernelEnt h) * SlabL2.kernelCasimir1 β (SlabL2.kernelEnt h) ∂muInf =
        c₁ * ∫ h, SlabL2.archChart F x (SlabL2.kernelEnt h) * β (SlabL2.kernelEnt h) ∂muInf := by
    intro x β hβ
    simp only [archChart_kernelEnt]
    exact weak_eq_of_forall_isSmoothingKernel WhittakerBlock.casimir1 SlabL2.kernelCasimir1 casimir1_const_mul
      (fun Φ hΦ _ hβ => (hK.1 Φ hΦ _ hβ).2.1) (fun hβ => (hK.1 (fun _ => 0) continuous_const _ hβ).1.1) F hFc c₁
      (fun φ hφ => (h φ hφ).1) x hβ
  have h2 : ∀ x : AdelicGL 3 (𝓞 ℚ) ℚ, ∀ β : E33 → ℂ, SlabL2.IsSmoothArchFactor β →
      ∫ h, SlabL2.archChart F x (SlabL2.kernelEnt h) * SlabL2.kernelCasimir2 β (SlabL2.kernelEnt h) ∂muInf =
        c₂ * ∫ h, SlabL2.archChart F x (SlabL2.kernelEnt h) * β (SlabL2.kernelEnt h) ∂muInf := by
    intro x β hβ
    simp only [archChart_kernelEnt]
    exact weak_eq_of_forall_isSmoothingKernel WhittakerBlock.casimir2 SlabL2.kernelCasimir2 casimir2_const_mul
      (fun Φ hΦ _ hβ => (hK.1 Φ hΦ _ hβ).2.2.1) (fun hβ => (hK.1 (fun _ => 0) continuous_const _ hβ).1.2.1) F hFc c₂
      (fun φ hφ => (h φ hφ).2.1) x hβ
  have h3 : ∀ x : AdelicGL 3 (𝓞 ℚ) ℚ, ∀ β : E33 → ℂ, SlabL2.IsSmoothArchFactor β →
      ∫ h, SlabL2.archChart F x (SlabL2.kernelEnt h) * SlabL2.kernelCasimir3 β (SlabL2.kernelEnt h) ∂muInf =
        c₃ * ∫ h, SlabL2.archChart F x (SlabL2.kernelEnt h) * β (SlabL2.kernelEnt h) ∂muInf := by
    intro x β hβ
    simp only [archChart_kernelEnt]
    exact weak_eq_of_forall_isSmoothingKernel WhittakerBlock.casimir3 SlabL2.kernelCasimir3 casimir3_const_mul
      (fun Φ hΦ _ hβ => (hK.1 Φ hΦ _ hβ).2.2.2) (fun hβ => (hK.1 (fun _ => 0) continuous_const _ hβ).1.2.2) F hFc c₃
      (fun φ hφ => (h φ hφ).2.2) x hβ

  have hcs : ∀ x : AdelicGL 3 (𝓞 ℚ) ℚ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (SlabL2.archChart F x)
      {m : Fin 3 → Fin 3 → ℝ | (Matrix.of m).det ≠ 0} := fun x => hFs x
  have hidE : (Matrix.of (fun a b : Fin 3 => if a = b then (1 : ℝ) else 0)).det ≠ 0 := by
    have : Matrix.of (fun a b : Fin 3 => if a = b then (1 : ℝ) else 0) = 1 := by
      ext a b; rw [Matrix.of_apply, Matrix.one_apply]
    rw [this, Matrix.det_one]; exact one_ne_zero
  have key : ∀ x : AdelicGL 3 (𝓞 ℚ) ℚ, WhittakerBlock.casimir1 F x = c₁ * F x ∧ WhittakerBlock.casimir2 F x = c₂ * F x ∧
      WhittakerBlock.casimir3 F x = c₃ * F x := by
    intro x
    obtain ⟨h0, e1, e2, e3⟩ := SlabL2.casimir_apply_eq_kernelCasimir_archChart F hFs x
    refine ⟨?_, ?_, ?_⟩
    · rw [e1, (hK.2 (SlabL2.archChart F x) c₁).1 ((hcs x).of_le (WithTop.coe_le_coe.mpr le_top)) (h1 x) _ hidE, h0]
    · rw [e2, (hK.2 (SlabL2.archChart F x) c₂).2.1 ((hcs x).of_le (WithTop.coe_le_coe.mpr le_top)) (h2 x) _ hidE, h0]
    · rw [e3, (hK.2 (SlabL2.archChart F x) c₃).2.2 ((hcs x).of_le (WithTop.coe_le_coe.mpr le_top)) (h3 x) _ hidE, h0]
  refine ⟨funext fun x => ?_, funext fun x => ?_, funext fun x => ?_⟩
  · rw [Pi.smul_apply, smul_eq_mul]; exact (key x).1
  · rw [Pi.smul_apply, smul_eq_mul]; exact (key x).2.1
  · rw [Pi.smul_apply, smul_eq_mul]; exact (key x).2.2

end LanglandsTunnell.CubicInduction.ArchConvCalculus

p2m_open "IsDedekindDomain NumberField AutomorphicForm Matrix MeasureTheory LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_eq_smul_of_forall_isSmoothingKernel_casimir_smoothingOperator_eq_smul.LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2"

theorem solution
    (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hFc : Continuous F) (hFs : WhittakerBlock.IsArchSmooth3 F) (c₁ c₂ c₃ : ℂ)
    (h : ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ →
      WhittakerBlock.casimir1 (smoothingOperator φ F) = c₁ • smoothingOperator φ F ∧
        WhittakerBlock.casimir2 (smoothingOperator φ F) = c₂ • smoothingOperator φ F ∧
          WhittakerBlock.casimir3 (smoothingOperator φ F) = c₃ • smoothingOperator φ F) :
    WhittakerBlock.casimir1 F = c₁ • F ∧ WhittakerBlock.casimir2 F = c₂ • F ∧ WhittakerBlock.casimir3 F = c₃ • F :=
  LanglandsTunnell.CubicInduction.ArchConvCalculus.casimir_eq_smul_of_forall_isSmoothingKernel F hFc hFs c₁ c₂ c₃ h

end

end S_LanglandsTunnell_CubicInduction_SlabL2_casimir_eq_smul_of_forall_isSmoothingKernel_casimir_smoothingOperator_eq_smul
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_eq_smul_of_forall_isSmoothingKernel_casimir_smoothingOperator_eq_smul (solution)
