-- Prove2me | solution 1 for NumberField.AdelicFourier.continuous_integrable_comp_vecMul_mem_and_bottomRowVec_mem_schwartzBruhat_of_mem_schwartzBruhat2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/e078105a-84af-5477-b7d8-4c81c299c05e

import Definitions.Def_AutomorphicForm_GodementSection
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicFourier_continuous_integrable_comp_vecMul_mem_and_bottomRowVec_mem_schwartzBruhat_of_mem_schwartzBruhat2
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_AdelicFourier_continuous_integrable_comp_vecMul_mem_and_bottomRowVec_mem_schwartzBruhat_of_mem_schwartzBruhat2.NumberField NumberField.AdelicFourier P2MW.S_NumberField_AdelicFourier_continuous_integrable_comp_vecMul_mem_and_bottomRowVec_mem_schwartzBruhat_of_mem_schwartzBruhat2.NumberField.AdelicFourier IsDedekindDomain"
open scoped SchwartzMap

noncomputable section

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing InfinitePlace.IsReal InfinitePlace.IsComplex InfinitePlace.Completion InfinitePlace.Completion.isometryEquivComplexOfIsComplex InfinitePlace.not_isReal_iff_isComplex mixedEmbedding mixedEmbedding.mixedSpace InfiniteAdeleRing.ringEquiv_mixedSpace InfinitePlace.Completion.isometry_extensionEmbedding InfinitePlace InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal AdeleRing InfinitePlace.Completion.isometryEquivRealOfIsReal AdeleRing.secondCountableTopology"
namespace AdelicFourier
p2m_export "NumberField.AdelicFourier" "pureTensorSet2 schwartzBruhat2 pairHaar mem_schwartzBruhat2_of_mem_pureTensorSet2 zero_mem_schwartzBruhat2 schwartzBruhat2_induction pureTensorSet schwartzBruhat mem_schwartzBruhat_of_mem_pureTensorSet zero_mem_schwartzBruhat"
namespace SB2Reg
p2m_open "NumberField.AdelicFourier NumberField"

open scoped Classical

variable {F : Type} [Field F] [NumberField F]

variable (F) in

def archHom : AdeleRing (𝓞 F) F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp
    (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

variable (F) in

def finHom : AdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 F) F :=
  RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)

theorem archHom_apply (x : AdeleRing (𝓞 F) F) :
    archHom F x = InfiniteAdeleRing.ringEquiv_mixedSpace F x.1 := rfl

theorem finHom_apply (x : AdeleRing (𝓞 F) F) : finHom F x = x.2 := rfl

variable (F) in

def archProj (x : Fin 2 → AdeleRing (𝓞 F) F) : Fin 2 → mixedEmbedding.mixedSpace F :=
  fun i => archHom F (x i)

variable (F) in

def finProj (x : Fin 2 → AdeleRing (𝓞 F) F) : Fin 2 → FiniteAdeleRing (𝓞 F) F :=
  fun i => finHom F (x i)

theorem archProj_apply (x : Fin 2 → AdeleRing (𝓞 F) F) (i : Fin 2) :
    archProj F x i = InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 := rfl

theorem finProj_apply (x : Fin 2 → AdeleRing (𝓞 F) F) (i : Fin 2) :
    finProj F x i = (x i).2 := rfl

theorem archProj_add (x y : Fin 2 → AdeleRing (𝓞 F) F) :
    archProj F (x + y) = archProj F x + archProj F y := by
  funext i; simp [archProj]

theorem finProj_add (x y : Fin 2 → AdeleRing (𝓞 F) F) :
    finProj F (x + y) = finProj F x + finProj F y := by
  funext i; simp [finProj]

theorem continuous_fst_adele :
    Continuous (fun x : AdeleRing (𝓞 F) F => x.1) := continuous_fst

theorem continuous_snd_adele :
    Continuous (fun x : AdeleRing (𝓞 F) F => x.2) := continuous_snd

theorem continuous_ringEquiv_mixedSpace :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  refine continuous_prodMk.2 ⟨continuous_pi fun v => ?_, continuous_pi fun v => ?_⟩
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
      (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp
      (continuous_apply _)

theorem continuous_archHom : Continuous (archHom F) :=
  continuous_ringEquiv_mixedSpace.comp continuous_fst

theorem continuous_finHom : Continuous (finHom F) := continuous_snd

theorem continuous_archProj : Continuous (archProj F) :=
  continuous_pi fun i => continuous_archHom.comp (continuous_apply i)

theorem continuous_finProj : Continuous (finProj F) :=
  continuous_pi fun i => continuous_finHom.comp (continuous_apply i)

theorem continuous_ringEquiv_mixedSpace_symm :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  apply continuous_pi
  intro v
  by_cases hv : InfinitePlace.IsReal v
  · have key : (fun y : mixedEmbedding.mixedSpace F =>
          (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm y v)
        = fun y => (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm (y.1 ⟨v, hv⟩) := by
      funext y
      apply (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).injective
      rw [IsometryEquiv.apply_symm_apply]
      exact congrArg (fun z : mixedEmbedding.mixedSpace F => z.1 ⟨v, hv⟩)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)
    rw [key]
    exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.continuous.comp
      ((continuous_apply _).comp continuous_fst)
  · have hc : InfinitePlace.IsComplex v := InfinitePlace.not_isReal_iff_isComplex.1 hv
    have key : (fun y : mixedEmbedding.mixedSpace F =>
          (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm y v)
        = fun y => (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).symm
            (y.2 ⟨v, hc⟩) := by
      funext y
      apply (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).injective
      rw [IsometryEquiv.apply_symm_apply]
      exact congrArg (fun z : mixedEmbedding.mixedSpace F => z.2 ⟨v, hc⟩)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)
    rw [key]
    exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).symm.continuous.comp
      ((continuous_apply _).comp continuous_snd)

variable (F) in

def glue (p : (Fin 2 → mixedEmbedding.mixedSpace F) × (Fin 2 → FiniteAdeleRing (𝓞 F) F)) :
    Fin 2 → AdeleRing (𝓞 F) F :=
  fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i)

theorem continuous_glue : Continuous (glue F) := by
  refine continuous_pi fun i => ?_
  refine Continuous.prodMk ?_ ?_
  · exact continuous_ringEquiv_mixedSpace_symm.comp ((continuous_apply i).comp continuous_fst)
  · exact (continuous_apply i).comp continuous_snd

theorem glue_archProj_finProj (x : Fin 2 → AdeleRing (𝓞 F) F) :
    glue F (archProj F x, finProj F x) = x := by
  funext i
  refine Prod.ext ?_ rfl
  show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
      (InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) = (x i).1
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm_apply_apply _

theorem archProj_glue (p : (Fin 2 → mixedEmbedding.mixedSpace F) × (Fin 2 → FiniteAdeleRing (𝓞 F) F)) :
    archProj F (glue F p) = p.1 := by
  funext i
  show InfiniteAdeleRing.ringEquiv_mixedSpace F
      ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i)) = p.1 i
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _

theorem finProj_glue (p : (Fin 2 → mixedEmbedding.mixedSpace F) × (Fin 2 → FiniteAdeleRing (𝓞 F) F)) :
    finProj F (glue F p) = p.2 := rfl

theorem archProj_vecMul (x : Fin 2 → AdeleRing (𝓞 F) F)
    (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) :
    archProj F (Matrix.vecMul x g) = Matrix.vecMul (archProj F x) (g.map (archHom F)) := by
  funext i
  exact RingHom.map_vecMul (archHom F) g x i

theorem finProj_vecMul (x : Fin 2 → AdeleRing (𝓞 F) F)
    (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) :
    finProj F (Matrix.vecMul x g) = Matrix.vecMul (finProj F x) (g.map (finHom F)) := by
  funext i
  exact RingHom.map_vecMul (finHom F) g x i

def vecMulHomeomorph {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (M : GL (Fin 2) R) : (Fin 2 → R) ≃ₜ (Fin 2 → R) where
  toFun y := Matrix.vecMul y (M : Matrix (Fin 2) (Fin 2) R)
  invFun y := Matrix.vecMul y ((M⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)
  left_inv y := by
    show Matrix.vecMul (Matrix.vecMul y (M : Matrix (Fin 2) (Fin 2) R))
        ((M⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = y
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
  right_inv y := by
    show Matrix.vecMul (Matrix.vecMul y ((M⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R))
        (M : Matrix (Fin 2) (Fin 2) R) = y
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.vecMul_one]
  continuous_toFun := Continuous.matrix_vecMul continuous_id continuous_const
  continuous_invFun := Continuous.matrix_vecMul continuous_id continuous_const

def vecMulCLE (M : GL (Fin 2) (mixedEmbedding.mixedSpace F)) :
    (Fin 2 → mixedEmbedding.mixedSpace F) ≃L[ℝ] (Fin 2 → mixedEmbedding.mixedSpace F) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun y => Matrix.vecMul y (M : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F))
      map_add' := fun y z => Matrix.add_vecMul _ _ _
      map_smul' := fun c y => by
        show Matrix.vecMul (c • y) _ = c • Matrix.vecMul y _
        exact Matrix.smul_vecMul c y _
      invFun := fun y => Matrix.vecMul y
        ((M⁻¹ : GL (Fin 2) (mixedEmbedding.mixedSpace F)) :
          Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F))
      left_inv := (vecMulHomeomorph M).left_inv
      right_inv := (vecMulHomeomorph M).right_inv }

theorem vecMulCLE_apply (M : GL (Fin 2) (mixedEmbedding.mixedSpace F))
    (y : Fin 2 → mixedEmbedding.mixedSpace F) :
    vecMulCLE M y = Matrix.vecMul y (M : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F)) := rfl

theorem comp_vecMul_mem_pureTensorSet2 {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ}
    (hΦ : Φ ∈ pureTensorSet2 F) (g : AutomorphicForm.AdelicGL2 (𝓞 F) F) :
    (fun x => Φ (Matrix.vecMul x (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))))
      ∈ pureTensorSet2 F := by
  obtain ⟨G, H, hH1, hH2, rfl⟩ := hΦ
  let gA : GL (Fin 2) (mixedEmbedding.mixedSpace F) := Matrix.GeneralLinearGroup.map (archHom F) g
  let gF : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) := Matrix.GeneralLinearGroup.map (finHom F) g
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (vecMulCLE gA) G,
    fun z => H (Matrix.vecMul z (gF : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F))),
    hH1.comp_continuous (vecMulHomeomorph gF).continuous,
    hH2.comp_homeomorph (vecMulHomeomorph gF), ?_⟩
  funext x
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, vecMulCLE_apply]
  have h1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F
        ((Matrix.vecMul x (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))) i).1)
      = Matrix.vecMul (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)
          (gA : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F)) :=
    archProj_vecMul x g
  have h2 : (fun i => ((Matrix.vecMul x (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))) i).2)
      = Matrix.vecMul (fun i => (x i).2)
          (gF : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :=
    finProj_vecMul x g
  rw [h1, h2]

theorem comp_vecMul_mem_schwartzBruhat2 {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ}
    (hΦ : Φ ∈ schwartzBruhat2 F) (g : AutomorphicForm.AdelicGL2 (𝓞 F) F) :
    (fun x => Φ (Matrix.vecMul x (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))))
      ∈ schwartzBruhat2 F := by
  induction hΦ using schwartzBruhat2_induction with
  | tensor Φ hΦ => exact mem_schwartzBruhat2_of_mem_pureTensorSet2 (comp_vecMul_mem_pureTensorSet2 hΦ g)
  | zero => exact zero_mem_schwartzBruhat2
  | add Φ Ψ _ _ ihΦ ihΨ => exact Submodule.add_mem _ ihΦ ihΨ
  | smul c Φ _ ih => exact Submodule.smul_mem _ c ih

theorem vecMul_centralScalar (x : Fin 2 → AdeleRing (𝓞 F) F) (t : (AdeleRing (𝓞 F) F)ˣ) :
    Matrix.vecMul x ((AutomorphicForm.centralScalar (𝓞 F) F t :
        AutomorphicForm.AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = (t : AdeleRing (𝓞 F) F) • x := by
  have h : ((AutomorphicForm.centralScalar (𝓞 F) F t :
        AutomorphicForm.AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = Matrix.diagonal fun _ => (t : AdeleRing (𝓞 F) F) := by
    show ((Matrix.GeneralLinearGroup.scalar (Fin 2) t : GL (Fin 2) (AdeleRing (𝓞 F) F)) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) = _
    simp [Matrix.GeneralLinearGroup.scalar]
  rw [h]
  funext i
  rw [Matrix.vecMul_diagonal]
  simp [mul_comm]

theorem comp_smul_mem_schwartzBruhat2 {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ}
    (hΦ : Φ ∈ schwartzBruhat2 F) (t : (AdeleRing (𝓞 F) F)ˣ) :
    (fun x => Φ ((t : AdeleRing (𝓞 F) F) • x)) ∈ schwartzBruhat2 F := by
  have h := comp_vecMul_mem_schwartzBruhat2 hΦ (AutomorphicForm.centralScalar (𝓞 F) F t)
  simpa only [vecMul_centralScalar] using h

theorem comp_add_mem_pureTensorSet2 {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ}
    (hΦ : Φ ∈ pureTensorSet2 F) (a : Fin 2 → AdeleRing (𝓞 F) F) :
    (fun x => Φ (x + a)) ∈ pureTensorSet2 F := by
  obtain ⟨G, H, hH1, hH2, rfl⟩ := hΦ
  refine ⟨SchwartzMap.compSubConstCLM ℂ (-archProj F a) G, fun z => H (z + finProj F a),
    hH1.comp_continuous (continuous_id.add continuous_const),
    hH2.comp_homeomorph (Homeomorph.addRight (finProj F a)), ?_⟩
  funext x
  simp only [SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add]
  have h1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + a) i).1)
      = (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) + archProj F a :=
    archProj_add x a
  have h2 : (fun i => ((x + a) i).2) = (fun i => (x i).2) + finProj F a := finProj_add x a
  rw [h1, h2]

theorem comp_add_mem_schwartzBruhat2 {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ}
    (hΦ : Φ ∈ schwartzBruhat2 F) (a : Fin 2 → AdeleRing (𝓞 F) F) :
    (fun x => Φ (x + a)) ∈ schwartzBruhat2 F := by
  induction hΦ using schwartzBruhat2_induction with
  | tensor Φ hΦ => exact mem_schwartzBruhat2_of_mem_pureTensorSet2 (comp_add_mem_pureTensorSet2 hΦ a)
  | zero => exact zero_mem_schwartzBruhat2
  | add Φ Ψ _ _ ihΦ ihΨ => exact Submodule.add_mem _ ihΦ ihΨ
  | smul c Φ _ ih => exact Submodule.smul_mem _ c ih

theorem vecMul_single_one_eq_bottomRowVec (g : AutomorphicForm.AdelicGL2 (𝓞 F) F)
    (t : AdeleRing (𝓞 F) F) :
    Matrix.vecMul (Pi.single 1 t) (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = AutomorphicForm.bottomRowVec F g t := by
  rw [Matrix.single_vecMul]
  funext j
  simp [AutomorphicForm.bottomRowVec, Matrix.row_apply]

variable (F) in

def archSingle : mixedEmbedding.mixedSpace F →L[ℝ] (Fin 2 → mixedEmbedding.mixedSpace F) :=
  ContinuousLinearMap.single ℝ (fun _ : Fin 2 => mixedEmbedding.mixedSpace F) 1

theorem archSingle_apply (a : mixedEmbedding.mixedSpace F) : archSingle F a = Pi.single 1 a := rfl

theorem norm_le_norm_archSingle (a : mixedEmbedding.mixedSpace F) : ‖a‖ ≤ ‖archSingle F a‖ := by
  have h := norm_le_pi_norm (archSingle F a) 1
  rwa [archSingle_apply, Pi.single_eq_same] at h

theorem archProj_single (t : AdeleRing (𝓞 F) F) :
    archProj F (Pi.single 1 t) = Pi.single 1 (archHom F t) := by
  funext i
  by_cases hi : i = 1
  · subst hi; simp [archProj]
  · simp [archProj, Pi.single_eq_of_ne hi]

theorem finProj_single (t : AdeleRing (𝓞 F) F) :
    finProj F (Pi.single 1 t) = Pi.single 1 (finHom F t) := by
  funext i
  by_cases hi : i = 1
  · subst hi; simp [finProj]
  · simp [finProj, Pi.single_eq_of_ne hi]

theorem comp_single_mem_pureTensorSet {Ψ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ}
    (hΨ : Ψ ∈ pureTensorSet2 F) :
    (fun t : AdeleRing (𝓞 F) F => Ψ (Pi.single 1 t)) ∈ pureTensorSet F := by
  obtain ⟨G, H, hH1, hH2, rfl⟩ := hΨ
  have hup : ∃ (k : ℕ) (C : ℝ), ∀ a : mixedEmbedding.mixedSpace F,
      ‖a‖ ≤ C * (1 + ‖archSingle F a‖) ^ k := by
    refine ⟨1, 1, fun a => ?_⟩
    have h := norm_le_norm_archSingle a
    rw [one_mul, pow_one]
    linarith [norm_nonneg (archSingle F a)]
  have hc : Continuous fun z : FiniteAdeleRing (𝓞 F) F =>
      (Pi.single (1 : Fin 2) z : Fin 2 → FiniteAdeleRing (𝓞 F) F) :=
    continuous_single (A := fun _ : Fin 2 => FiniteAdeleRing (𝓞 F) F) 1
  refine ⟨SchwartzMap.compCLM ℂ (g := archSingle F) (archSingle F).hasTemperateGrowth hup G,
    fun z => H (Pi.single 1 z), hH1.comp_continuous hc, ?_, ?_⟩
  · refine HasCompactSupport.intro (hH2.image (continuous_apply 1)) fun z hz => ?_
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    exact hz ⟨Pi.single 1 z, hmem, by simp⟩
  · funext t
    simp only [SchwartzMap.compCLM_apply, Function.comp_apply, archSingle_apply]
    have h1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((Pi.single 1 t : Fin 2 → _) i).1)
        = Pi.single 1 (InfiniteAdeleRing.ringEquiv_mixedSpace F t.1) := archProj_single t
    have h2 : (fun i => ((Pi.single 1 t : Fin 2 → AdeleRing (𝓞 F) F) i).2) = Pi.single 1 t.2 :=
      finProj_single t
    rw [h1, h2]

theorem comp_single_mem_schwartzBruhat {Ψ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ}
    (hΨ : Ψ ∈ schwartzBruhat2 F) :
    (fun t : AdeleRing (𝓞 F) F => Ψ (Pi.single 1 t)) ∈ schwartzBruhat F := by
  induction hΨ using schwartzBruhat2_induction with
  | tensor Φ hΦ => exact mem_schwartzBruhat_of_mem_pureTensorSet (comp_single_mem_pureTensorSet hΦ)
  | zero => exact zero_mem_schwartzBruhat
  | add Φ Ψ _ _ ihΦ ihΨ => exact Submodule.add_mem _ ihΦ ihΨ
  | smul c Φ _ ih => exact Submodule.smul_mem _ c ih

theorem bottomRow_mem_schwartzBruhat {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ}
    (hΦ : Φ ∈ schwartzBruhat2 F) (g : AutomorphicForm.AdelicGL2 (𝓞 F) F) :
    (fun t : AdeleRing (𝓞 F) F => Φ (AutomorphicForm.bottomRowVec F g t)) ∈ schwartzBruhat F := by
  have h := comp_single_mem_schwartzBruhat (comp_vecMul_mem_schwartzBruhat2 hΦ g)
  simpa only [vecMul_single_one_eq_bottomRowVec] using h

theorem continuous_of_mem_pureTensorSet2 {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ}
    (hΦ : Φ ∈ pureTensorSet2 F) : Continuous Φ := by
  obtain ⟨G, H, hH1, hH2, rfl⟩ := hΦ
  exact (G.continuous.comp continuous_archProj).mul (hH1.continuous.comp continuous_finProj)

theorem continuous_of_mem_schwartzBruhat2 {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ}
    (hΦ : Φ ∈ schwartzBruhat2 F) : Continuous Φ := by
  induction hΦ using schwartzBruhat2_induction with
  | tensor Φ hΦ => exact continuous_of_mem_pureTensorSet2 hΦ
  | zero => exact continuous_const
  | add Φ Ψ _ _ ihΦ ihΨ => exact ihΦ.add ihΨ
  | smul c Φ _ ih => exact ih.const_smul c

def HasDecay (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) : Prop :=
  ∀ N : ℕ, ∃ (C : ℝ) (K : Set (Fin 2 → FiniteAdeleRing (𝓞 F) F)), 0 ≤ C ∧ IsCompact K ∧
    (∀ x, ‖Φ x‖ * (1 + ‖archProj F x‖) ^ N ≤ C) ∧
    (∀ x, finProj F x ∉ K → Φ x = 0)

theorem hasDecay_of_mem_pureTensorSet2 {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ}
    (hΦ : Φ ∈ pureTensorSet2 F) : HasDecay Φ := by
  obtain ⟨G, H, hH1, hH2, rfl⟩ := hΦ
  intro N
  obtain ⟨M, hM⟩ := hH2.exists_bound_of_continuous hH1.continuous
  set S : ℝ := 2 ^ N * (Finset.Iic (N, 0)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) G with hS
  have hS0 : 0 ≤ S := by positivity
  have hG : ∀ y, ‖G y‖ * (1 + ‖y‖) ^ N ≤ S := by
    intro y
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (N, 0)) (k := N) (n := 0)
      le_rfl le_rfl G y
    rw [norm_iteratedFDeriv_zero] at h
    rw [mul_comm]
    exact h
  refine ⟨S * max M 0, tsupport H, by positivity, hH2, fun x => ?_, fun x hx => ?_⟩
  · rw [norm_mul, mul_right_comm]
    refine mul_le_mul (hG _) ((hM _).trans (le_max_left _ _)) (norm_nonneg _) hS0
  · have h0 : H (finProj F x) = 0 := image_eq_zero_of_notMem_tsupport hx
    show G (archProj F x) * H (finProj F x) = 0
    rw [h0, mul_zero]

theorem hasDecay_zero : HasDecay (F := F) 0 := by
  intro N
  exact ⟨0, ∅, le_rfl, isCompact_empty, fun x => by simp, fun x _ => rfl⟩

theorem HasDecay.add {Φ Ψ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ} (hΦ : HasDecay Φ) (hΨ : HasDecay Ψ) :
    HasDecay (Φ + Ψ) := by
  intro N
  obtain ⟨C₁, K₁, hC₁, hK₁, hb₁, hv₁⟩ := hΦ N
  obtain ⟨C₂, K₂, hC₂, hK₂, hb₂, hv₂⟩ := hΨ N
  refine ⟨C₁ + C₂, K₁ ∪ K₂, by positivity, hK₁.union hK₂, fun x => ?_, fun x hx => ?_⟩
  · have hw : 0 ≤ (1 + ‖archProj F x‖) ^ N := by positivity
    calc ‖(Φ + Ψ) x‖ * (1 + ‖archProj F x‖) ^ N
        ≤ (‖Φ x‖ + ‖Ψ x‖) * (1 + ‖archProj F x‖) ^ N :=
          mul_le_mul_of_nonneg_right (norm_add_le _ _) hw
      _ = ‖Φ x‖ * (1 + ‖archProj F x‖) ^ N + ‖Ψ x‖ * (1 + ‖archProj F x‖) ^ N := by ring
      _ ≤ C₁ + C₂ := add_le_add (hb₁ x) (hb₂ x)
  · rw [Set.mem_union, not_or] at hx
    simp [hv₁ x hx.1, hv₂ x hx.2]

theorem HasDecay.smul {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ} (hΦ : HasDecay Φ) (c : ℂ) :
    HasDecay (c • Φ) := by
  intro N
  obtain ⟨C, K, hC, hK, hb, hv⟩ := hΦ N
  refine ⟨‖c‖ * C, K, by positivity, hK, fun x => ?_, fun x hx => ?_⟩
  · rw [Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hb x) (norm_nonneg c)
  · simp [hv x hx]

theorem hasDecay_of_mem_schwartzBruhat2 {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ}
    (hΦ : Φ ∈ schwartzBruhat2 F) : HasDecay Φ := by
  induction hΦ using schwartzBruhat2_induction with
  | tensor Φ hΦ => exact hasDecay_of_mem_pureTensorSet2 hΦ
  | zero => exact hasDecay_zero
  | add Φ Ψ _ _ ihΦ ihΨ => exact ihΦ.add ihΨ
  | smul c Φ _ ih => exact ih.smul c

section Integrable

variable [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]

theorem integrable_of_mem_pureTensorSet2 (μ : Measure (Fin 2 → AdeleRing (𝓞 F) F))
    [μ.IsAddHaarMeasure] {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ pureTensorSet2 F) :
    Integrable Φ μ := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F) :=
    NumberField.AdeleRing.secondCountableTopology F
  haveI : BorelSpace (Fin 2 → AdeleRing (𝓞 F) F) := Pi.borelSpace
  haveI hB0 : BorelSpace (Fin 2 → mixedEmbedding.mixedSpace F) := inferInstance
  obtain ⟨G, H, hH1, hH2, rfl⟩ := hΦ

  set S : Set (Fin 2 → AdeleRing (𝓞 F) F) := finProj F ⁻¹' tsupport H with hS
  have hSm : MeasurableSet S := ((isClosed_tsupport H).preimage continuous_finProj).measurableSet
  have hPm : Measurable (archProj F) := continuous_archProj.measurable

  set μ' : Measure (Fin 2 → mixedEmbedding.mixedSpace F) :=
    Measure.map (archProj F) (μ.restrict S) with hμ'

  have hfin : ∀ K : Set (Fin 2 → mixedEmbedding.mixedSpace F), IsCompact K → μ' K < ⊤ := by
    intro K hK
    rw [hμ', Measure.map_apply hPm hK.measurableSet, Measure.restrict_apply (hPm hK.measurableSet)]
    have hsub : archProj F ⁻¹' K ∩ S ⊆ glue F '' (K ×ˢ tsupport H) := by
      rintro x ⟨hxK, hxS⟩
      exact ⟨(archProj F x, finProj F x), ⟨hxK, hxS⟩, glue_archProj_finProj x⟩
    exact (measure_mono hsub).trans_lt ((hK.prod hH2).image continuous_glue).measure_lt_top
  haveI hμ'c : IsFiniteMeasureOnCompacts μ' := ⟨hfin⟩

  haveI hμ'i : μ'.IsAddLeftInvariant := by
    refine ⟨fun a => ?_⟩
    refine Measure.ext fun A hA => ?_
    have hA' : MeasurableSet ((fun y => a + y) ⁻¹' A) := measurable_const_add a hA
    set b : Fin 2 → AdeleRing (𝓞 F) F := glue F (a, 0) with hb
    have hPa : ∀ x, archProj F (b + x) = a + archProj F x := fun x => by
      rw [archProj_add, hb, archProj_glue]
    have hQa : ∀ x, finProj F (b + x) = finProj F x := fun x => by
      rw [finProj_add, hb, finProj_glue, zero_add]
    rw [Measure.map_apply (measurable_const_add a) hA, hμ', Measure.map_apply hPm hA',
      Measure.map_apply hPm hA, Measure.restrict_apply (hPm hA'), Measure.restrict_apply (hPm hA)]
    have hset : archProj F ⁻¹' ((fun y => a + y) ⁻¹' A) ∩ S
        = (fun x => b + x) ⁻¹' (archProj F ⁻¹' A ∩ S) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_inter_iff, hS, hPa, hQa]
    rw [hset, measure_preimage_add]

  set ν : Measure (Fin 2 → mixedEmbedding.mixedSpace F) :=
    μ' + (Module.finBasis ℝ (Fin 2 → mixedEmbedding.mixedSpace F)).addHaar with hν
  haveI : ν.IsAddLeftInvariant := by
    refine ⟨fun a => ?_⟩
    rw [hν, Measure.map_add _ _ (measurable_const_add a), map_add_left_eq_self, map_add_left_eq_self]
  have hK : IsCompact (Metric.closedBall (0 : Fin 2 → mixedEmbedding.mixedSpace F) 1) :=
    isCompact_closedBall 0 1
  have hKint : (interior (Metric.closedBall (0 : Fin 2 → mixedEmbedding.mixedSpace F) 1)).Nonempty := by
    rw [interior_closedBall 0 one_ne_zero]
    exact ⟨0, Metric.mem_ball_self one_pos⟩
  have hKpos : ν (Metric.closedBall 0 1) ≠ 0 := by
    rw [hν, Measure.add_apply]
    have h := (Metric.isOpen_ball.measure_pos
      ((Module.finBasis ℝ (Fin 2 → mixedEmbedding.mixedSpace F)).addHaar)
      ⟨(0 : Fin 2 → mixedEmbedding.mixedSpace F), Metric.mem_ball_self one_pos⟩).ne'
    have h' : (Module.finBasis ℝ (Fin 2 → mixedEmbedding.mixedSpace F)).addHaar
        (Metric.closedBall 0 1) ≠ 0 :=
      fun h0 => h (measure_mono_null Metric.ball_subset_closedBall h0)
    exact fun h0 => h' (add_eq_zero.mp h0).2
  have hKtop : ν (Metric.closedBall 0 1) ≠ ⊤ := by
    rw [hν, Measure.add_apply]
    exact ENNReal.add_ne_top.2 ⟨(hfin _ hK).ne, hK.measure_lt_top.ne⟩
  haveI hνH : ν.IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_of_isCompact_nonempty_interior ν _ hK hKint hKpos hKtop
  have hGν : Integrable G ν := G.integrable
  have hGμ' : Integrable G μ' := hGν.mono_measure (by rw [hν]; exact Measure.le_add_right le_rfl)

  have h1 : Integrable (fun x => G (archProj F x)) (μ.restrict S) :=
    (integrable_map_measure G.continuous.aestronglyMeasurable hPm.aemeasurable).mp hGμ'
  have h2 : Integrable (S.indicator fun x => G (archProj F x)) μ :=
    (integrable_indicator_iff hSm).mpr h1
  obtain ⟨M, hM⟩ := hH2.exists_bound_of_continuous hH1.continuous
  have h3 : Integrable (fun x => S.indicator (fun x => G (archProj F x)) x * H (finProj F x)) μ :=
    h2.mul_bdd ((hH1.continuous.comp continuous_finProj).aestronglyMeasurable)
      (ae_of_all _ fun x => hM _)
  have heq : (fun x : Fin 2 → AdeleRing (𝓞 F) F =>
        G (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) * H (fun i => (x i).2))
      = fun x => S.indicator (fun x => G (archProj F x)) x * H (finProj F x) := by
    funext x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]; rfl
    · have h0 : H (finProj F x) = 0 := image_eq_zero_of_notMem_tsupport hx
      rw [Set.indicator_of_notMem hx, zero_mul]
      show G (archProj F x) * H (finProj F x) = 0
      rw [h0, mul_zero]
  rw [heq]
  exact h3

theorem integrable_of_mem_schwartzBruhat2 (μ : Measure (Fin 2 → AdeleRing (𝓞 F) F))
    [μ.IsAddHaarMeasure] {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 F) :
    Integrable Φ μ := by
  induction hΦ using schwartzBruhat2_induction with
  | tensor Φ hΦ => exact integrable_of_mem_pureTensorSet2 μ hΦ
  | zero => exact integrable_zero _ _ μ
  | add Φ Ψ _ _ ihΦ ihΨ => exact ihΦ.add ihΨ
  | smul c Φ _ ih => exact ih.smul c

end Integrable

end NumberField.AdelicFourier.SB2Reg

open scoped Classical in
theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (hΦ : Φ ∈ schwartzBruhat2 F) :
    Continuous Φ ∧
    (∀ N : ℕ, ∃ (C : ℝ) (K : Set (Fin 2 → FiniteAdeleRing (𝓞 F) F)), 0 ≤ C ∧ IsCompact K ∧
      (∀ x : Fin 2 → AdeleRing (𝓞 F) F,
        ‖Φ x‖ * (1 + ‖fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1‖) ^ N ≤ C) ∧
      (∀ x : Fin 2 → AdeleRing (𝓞 F) F, (fun i => (x i).2) ∉ K → Φ x = 0)) ∧
    (∀ (μ : Measure (Fin 2 → AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure], Integrable Φ μ) ∧
    (∀ (μ₁ : Measure (AdeleRing (𝓞 F) F)) [μ₁.IsAddHaarMeasure], Integrable Φ (pairHaar μ₁)) ∧
    (∀ g : AutomorphicForm.AdelicGL2 (𝓞 F) F,
      (fun x => Φ (Matrix.vecMul x (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))))
        ∈ schwartzBruhat2 F) ∧
    (∀ t : (AdeleRing (𝓞 F) F)ˣ, (fun x => Φ ((t : AdeleRing (𝓞 F) F) • x)) ∈ schwartzBruhat2 F) ∧
    (∀ a : Fin 2 → AdeleRing (𝓞 F) F, (fun x => Φ (x + a)) ∈ schwartzBruhat2 F) ∧
    (∀ g : AutomorphicForm.AdelicGL2 (𝓞 F) F,
      (fun t : AdeleRing (𝓞 F) F => Φ (AutomorphicForm.bottomRowVec F g t)) ∈ schwartzBruhat F) := by
  refine ⟨SB2Reg.continuous_of_mem_schwartzBruhat2 hΦ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N
    obtain ⟨C, K, hC, hK, hb, hv⟩ := SB2Reg.hasDecay_of_mem_schwartzBruhat2 hΦ N
    exact ⟨C, K, hC, hK, hb, hv⟩
  · intro μ _
    exact SB2Reg.integrable_of_mem_schwartzBruhat2 μ hΦ
  · intro μ₁ _
    haveI : SecondCountableTopology (AdeleRing (𝓞 F) F) :=
      NumberField.AdeleRing.secondCountableTopology F
    haveI : (pairHaar μ₁).IsAddHaarMeasure := by
      unfold pairHaar
      infer_instance
    exact SB2Reg.integrable_of_mem_schwartzBruhat2 (pairHaar μ₁) hΦ
  · exact fun g => SB2Reg.comp_vecMul_mem_schwartzBruhat2 hΦ g
  · exact fun t => SB2Reg.comp_smul_mem_schwartzBruhat2 hΦ t
  · exact fun a => SB2Reg.comp_add_mem_schwartzBruhat2 hΦ a
  · exact fun g => SB2Reg.bottomRow_mem_schwartzBruhat hΦ g

end

end S_NumberField_AdelicFourier_continuous_integrable_comp_vecMul_mem_and_bottomRowVec_mem_schwartzBruhat_of_mem_schwartzBruhat2
end P2MW
export P2MW.S_NumberField_AdelicFourier_continuous_integrable_comp_vecMul_mem_and_bottomRowVec_mem_schwartzBruhat_of_mem_schwartzBruhat2 (solution)
