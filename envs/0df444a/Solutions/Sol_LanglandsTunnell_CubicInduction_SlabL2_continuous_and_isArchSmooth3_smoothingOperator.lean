-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.SlabL2.continuous_and_isArchSmooth3_smoothingOperator
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/2f5a29ce-3bdb-5c14-8e4b-8818654d2b3b

import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchSmooth3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchSmoothSpace3
import Theorems.Thm_LanglandsTunnell_CubicInduction_isOpen_and_isCompact_setOf_forall_componentAt3_finEmbedN_mem
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Group.Integral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_continuous_and_isArchSmooth3_smoothingOperator
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open NumberField MeasureTheory IsDedekindDomain AutomorphicForm

namespace SmoothingTranslation

open Matrix IsDedekindDomain NumberField AutomorphicForm

open LanglandsTunnell.CubicInduction

section ComponentDecomposition

open IsDedekindDomain NumberField

noncomputable section

namespace LanglandsTunnell
namespace CubicInduction

variable (p : HeightOneSpectrum (𝓞 ℚ))

private theorem fin_localToAdelic3 (x : LocalGL3 p) :
    (AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (localToAdelic3 p x : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      localMatN (Fin 3) (𝓞 ℚ) ℚ p (x : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) := by
  change (AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (finMatN (Fin 3) (𝓞 ℚ) ℚ
    (localMatN (Fin 3) (𝓞 ℚ) ℚ p (x : Matrix (Fin 3) (Fin 3) _))) = _
  rw [mapMatrix_fin_finMatN]

private theorem arch_localToAdelic3 (x : LocalGL3 p) :
    (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (localToAdelic3 p x : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      1 := by
  change (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (finMatN (Fin 3) (𝓞 ℚ) ℚ
    (localMatN (Fin 3) (𝓞 ℚ) ℚ p (x : Matrix (Fin 3) (Fin 3) _))) = _
  rw [mapMatrix_arch_finMatN]

private theorem componentAt3_coe {q : HeightOneSpectrum (𝓞 ℚ)} (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (componentAt3 (𝓞 ℚ) ℚ q g : Matrix (Fin 3) (Fin 3) (q.adicCompletion ℚ)) =
      (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ q).mapMatrix
        ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))) :=
  rfl

private theorem componentAt3_localToAdelic3_self (x : LocalGL3 p) :
    componentAt3 (𝓞 ℚ) ℚ p (localToAdelic3 p x) = x := by
  apply Units.ext
  rw [componentAt3_coe, fin_localToAdelic3, mapMatrix_localMatN_self]

private theorem componentAt3_localToAdelic3_of_ne {q : HeightOneSpectrum (𝓞 ℚ)} (hq : q ≠ p) (x : LocalGL3 p) :
    componentAt3 (𝓞 ℚ) ℚ q (localToAdelic3 p x) = 1 := by
  apply Units.ext
  rw [componentAt3_coe, fin_localToAdelic3, mapMatrix_localMatN_of_ne (Fin 3) (𝓞 ℚ) ℚ p _ hq, Units.val_one]

variable {p}

private theorem mul_localToAdelic3_comm_of_componentAt3_eq_one {g : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hg : componentAt3 (𝓞 ℚ) ℚ p g = 1) (x : LocalGL3 p) :
    g * localToAdelic3 p x = localToAdelic3 p x * g := by
  have hg' : (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ p).mapMatrix
      ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))) = 1 := by
    rw [← componentAt3_coe, hg, Units.val_one]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  refine matrixAdele_ext (Fin 3) (𝓞 ℚ) ℚ ?_ ?_
  · rw [map_mul, map_mul, arch_localToAdelic3, mul_one, one_mul]
  · rw [map_mul, map_mul, fin_localToAdelic3]
    refine matrixFin_ext (Fin 3) (𝓞 ℚ) ℚ fun w => ?_
    by_cases hw : w = p
    · subst hw
      rw [map_mul, map_mul, hg', mapMatrix_localMatN_self, one_mul, mul_one]
    · rw [map_mul, map_mul, mapMatrix_localMatN_of_ne (Fin 3) (𝓞 ℚ) ℚ p _ hw, one_mul, mul_one]

private theorem componentAt3_mul_inv_localToAdelic3 (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    componentAt3 (𝓞 ℚ) ℚ p (g * (localToAdelic3 p (componentAt3 (𝓞 ℚ) ℚ p g))⁻¹) = 1 := by
  rw [map_mul, map_inv, componentAt3_localToAdelic3_self, mul_inv_cancel]

private theorem mul_inv_localToAdelic3_mul_localToAdelic3 (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    g * (localToAdelic3 p (componentAt3 (𝓞 ℚ) ℚ p g))⁻¹ * localToAdelic3 p (componentAt3 (𝓞 ℚ) ℚ p g) = g :=
  inv_mul_cancel_right g _

end LanglandsTunnell.CubicInduction

end

end ComponentDecomposition

section ArchimedeanFinite

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory

noncomputable section

namespace LanglandsTunnell
namespace CubicInduction

section Components

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem coe_componentAt3 (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ((componentAt3 (𝓞 ℚ) ℚ v g : GL (Fin 3) (v.adicCompletion ℚ)) :
        Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      ((AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ v).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)).mapMatrix
        (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
  rfl

private theorem coe_archComponent3 (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ((archComponent3 (𝓞 ℚ) ℚ g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
        Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) =
      (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
  rfl

end Components

section ArchEmbedding

private def archMat3 (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ) :=
  Matrix.of fun i j =>
    ((g i j, (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) : AdeleRing (𝓞 ℚ) ℚ)

private theorem mapMatrix_arch_archMat3 (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :
    (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (archMat3 g) = g := by
  ext i j
  simp [archMat3, RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleArch_apply]

private theorem mapMatrix_fin_archMat3 (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :
    (AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (archMat3 g) = 1 := by
  ext i j
  simp [archMat3, RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleFin_apply]

private theorem archMat3_one : archMat3 1 = 1 :=
  matrixAdele_ext (Fin 3) (𝓞 ℚ) ℚ (by rw [mapMatrix_arch_archMat3, map_one])
    (by rw [mapMatrix_fin_archMat3, map_one])

private theorem archMat3_mul (g h : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :
    archMat3 (g * h) = archMat3 g * archMat3 h :=
  matrixAdele_ext (Fin 3) (𝓞 ℚ) ℚ
    (by rw [map_mul, mapMatrix_arch_archMat3, mapMatrix_arch_archMat3, mapMatrix_arch_archMat3])
    (by rw [map_mul, mapMatrix_fin_archMat3, mapMatrix_fin_archMat3, mapMatrix_fin_archMat3, mul_one])

private def archToAdelic3 : GL (Fin 3) (InfiniteAdeleRing ℚ) →* AdelicGL 3 (𝓞 ℚ) ℚ where
  toFun g :=
    { val := archMat3 g
      inv := archMat3 ((g⁻¹ : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ))
      val_inv := by rw [← archMat3_mul, Units.mul_inv, archMat3_one]
      inv_val := by rw [← archMat3_mul, Units.inv_mul, archMat3_one] }
  map_one' := Units.ext (by simp only [Units.val_one]; exact archMat3_one)
  map_mul' g h := Units.ext (by simp only [Units.val_mul]; exact archMat3_mul _ _)

private theorem coe_archToAdelic3 (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    ((archToAdelic3 g : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      archMat3 (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :=
  rfl

private theorem archComponent3_archToAdelic3 (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    archComponent3 (𝓞 ℚ) ℚ (archToAdelic3 g) = g := by
  apply Units.ext
  rw [coe_archComponent3, coe_archToAdelic3, mapMatrix_arch_archMat3]

private theorem componentAt3_archToAdelic3 (v : HeightOneSpectrum (𝓞 ℚ)) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    componentAt3 (𝓞 ℚ) ℚ v (archToAdelic3 g) = 1 := by
  apply Units.ext
  rw [coe_componentAt3, coe_archToAdelic3, ← RingHom.mapMatrix_comp, RingHom.comp_apply,
    mapMatrix_fin_archMat3, map_one, Units.val_one]

end ArchEmbedding

section ArchEntries

private def archEntries3 (a : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Fin 3 → Fin 3 → ℝ :=
  fun i j => SlabL2.realCoordinate ((a : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i j)

section RealCoordinate

p2m_open "LanglandsTunnell.CubicInduction.SlabL2"

private theorem isReal_of_rat (w : InfinitePlace ℚ) : w.IsReal := by
  rw [Subsingleton.elim w Rat.infinitePlace]
  exact Rat.isReal_infinitePlace

private theorem continuous_realCoordinate : Continuous realCoordinate :=
  (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).continuous.comp
    (continuous_apply Rat.infinitePlace)

private def ofRealAdele (r : ℝ) : InfiniteAdeleRing ℚ :=
  show (v : InfinitePlace ℚ) → v.Completion from
    fun v => (InfinitePlace.Completion.isometryEquivRealOfIsReal (isReal_of_rat v)).symm r

private theorem continuous_ofRealAdele : Continuous ofRealAdele :=
  continuous_pi fun v => (InfinitePlace.Completion.isometryEquivRealOfIsReal (isReal_of_rat v)).symm.continuous

private theorem realCoordinate_ofRealAdele (r : ℝ) : realCoordinate (ofRealAdele r) = r :=
  (InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).apply_symm_apply r

private theorem ofRealAdele_realCoordinate (x : InfiniteAdeleRing ℚ) : ofRealAdele (realCoordinate x) = x := by
  funext v
  obtain rfl : v = Rat.infinitePlace := Subsingleton.elim _ _
  exact (InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).symm_apply_apply
    (x Rat.infinitePlace)

private def realCoordinateRingEquiv : InfiniteAdeleRing ℚ ≃+* ℝ where
  toFun := realCoordinate
  invFun := ofRealAdele
  left_inv := ofRealAdele_realCoordinate
  right_inv := realCoordinate_ofRealAdele
  map_mul' := map_mul realCoordinate
  map_add' := map_add realCoordinate

private def realCoordinateHomeomorph : InfiniteAdeleRing ℚ ≃ₜ ℝ where
  toFun := realCoordinate
  invFun := ofRealAdele
  left_inv := ofRealAdele_realCoordinate
  right_inv := realCoordinate_ofRealAdele
  continuous_toFun := continuous_realCoordinate
  continuous_invFun := continuous_ofRealAdele

private theorem realCoordinateHomeomorph_apply (x : InfiniteAdeleRing ℚ) :
    realCoordinateHomeomorph x = realCoordinate x :=
  rfl

private theorem realCoordinateHomeomorph_symm_apply (r : ℝ) : realCoordinateHomeomorph.symm r = ofRealAdele r :=
  rfl

private theorem realCoordinateRingEquiv_symm_apply (r : ℝ) : realCoordinateRingEquiv.symm r = ofRealAdele r :=
  rfl

private theorem continuous_archEntries3 : Continuous archEntries3 :=
  continuous_pi fun i => continuous_pi fun j =>
    continuous_realCoordinate.comp (Units.continuous_val.matrix_elem i j)

private theorem isCompact_preimage_archEntries3 {T : Set (Fin 3 → Fin 3 → ℝ)} (hT : IsCompact T)
    (hTloc : T ⊆ {m | (Matrix.of m).det ≠ 0}) : IsCompact (archEntries3 ⁻¹' T) := by
  haveI : CompactSpace T := isCompact_iff_compactSpace.mp hT
  have hdet : ∀ x : T, IsUnit (Matrix.of x.1).det := fun x => isUnit_iff_ne_zero.mpr (hTloc x.2)
  let φ : ℝ →+* InfiniteAdeleRing ℚ := realCoordinateRingEquiv.symm
  let u : T → GL (Fin 3) ℝ := fun x =>
    ⟨Matrix.of x.1, (Matrix.of x.1)⁻¹, Matrix.mul_nonsing_inv _ (hdet x), Matrix.nonsing_inv_mul _ (hdet x)⟩
  let j : T → GL (Fin 3) (InfiniteAdeleRing ℚ) := fun x => Units.map (RingHom.mapMatrix φ).toMonoidHom (u x)
  have hof : Continuous fun x : T => Matrix.of x.1 := continuous_subtype_val
  have hinv : Continuous fun x : T => (Matrix.of x.1)⁻¹ := by
    refine continuous_iff_continuousAt.mpr fun x => ?_
    have hc : ContinuousAt Ring.inverse (Matrix.of x.1).det := by
      simpa using NormedRing.inverse_continuousAt (hdet x).unit
    exact (continuousAt_matrix_inv (Matrix.of x.1) hc).comp (f := fun x : T => Matrix.of x.1) hof.continuousAt
  have hj : Continuous j := by
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · refine continuous_matrix fun i k => ?_
      exact continuous_ofRealAdele.comp (hof.matrix_elem i k)
    · refine continuous_matrix fun i k => ?_
      exact continuous_ofRealAdele.comp (hinv.matrix_elem i k)
  have hsub : archEntries3 ⁻¹' T ⊆ Set.range j := by
    intro a ha
    refine ⟨⟨archEntries3 a, ha⟩, Units.ext (Matrix.ext fun i k => ?_)⟩
    show ofRealAdele (realCoordinate ((a : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i k)) = _
    exact ofRealAdele_realCoordinate _
  exact (isCompact_range hj).of_isClosed_subset (hT.isClosed.preimage continuous_archEntries3) hsub

end RealCoordinate

private theorem archEntries_archToAdelic3 (a : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    SlabL2.archEntries (archToAdelic3 a) = archEntries3 a := by
  funext i j
  rfl

end ArchEntries

private theorem continuous_archToAdelic3 : Continuous archToAdelic3 := by
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

private theorem continuous_finEmbedN3 : Continuous (finEmbedN (Fin 3) (𝓞 ℚ) ℚ) := by
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

private def finPart3 : AdelicGL 3 (𝓞 ℚ) ℚ →* GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  Matrix.GeneralLinearGroup.map (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)

private theorem coe_finPart3 (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ((finPart3 g : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) =
      (AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
  rfl

private theorem coe_finEmbedN_three (g : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    ((finEmbedN (Fin 3) (𝓞 ℚ) ℚ g : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      finMatN (Fin 3) (𝓞 ℚ) ℚ (g : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  rfl

private theorem archToAdelic3_archComponent3_mul_finEmbedN_finPart3 (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    archToAdelic3 (archComponent3 (𝓞 ℚ) ℚ g) * finEmbedN (Fin 3) (𝓞 ℚ) ℚ (finPart3 g) = g := by
  apply Units.ext
  rw [Units.val_mul, coe_archToAdelic3, coe_finEmbedN_three, coe_archComponent3, coe_finPart3]
  refine matrixAdele_ext (Fin 3) (𝓞 ℚ) ℚ ?_ ?_
  · rw [map_mul, mapMatrix_arch_archMat3, mapMatrix_arch_finMatN, mul_one]
  · rw [map_mul, mapMatrix_fin_archMat3, mapMatrix_fin_finMatN, one_mul]

private theorem continuous_finPart3 : Continuous finPart3 := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    show Continuous fun a : AdelicGL 3 (𝓞 ℚ) ℚ =>
      AdelicLevel.adeleFin (𝓞 ℚ) ℚ ((a : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j)
    exact (AdelicLevel.continuous_adeleFin (𝓞 ℚ) ℚ).comp (Units.continuous_val.matrix_elem i j)
  · refine continuous_matrix fun i j => ?_
    show Continuous fun a : AdelicGL 3 (𝓞 ℚ) ℚ =>
      AdelicLevel.adeleFin (𝓞 ℚ) ℚ (((a⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j)
    exact (AdelicLevel.continuous_adeleFin (𝓞 ℚ) ℚ).comp (Units.continuous_coe_inv.matrix_elem i j)

private theorem componentAt3_finEmbedN_finPart3 (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    componentAt3 (𝓞 ℚ) ℚ p (finEmbedN (Fin 3) (𝓞 ℚ) ℚ (finPart3 g)) = componentAt3 (𝓞 ℚ) ℚ p g := by
  conv_rhs => rw [← archToAdelic3_archComponent3_mul_finEmbedN_finPart3 g]
  rw [map_mul, componentAt3_archToAdelic3, one_mul]

private theorem archComponent3_finEmbedN_three (k : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    archComponent3 (𝓞 ℚ) ℚ (finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) = 1 := by
  apply Units.ext
  rw [coe_archComponent3, coe_finEmbedN_three, mapMatrix_arch_finMatN, Units.val_one]

private theorem archComponent3_mul_finEmbedN (y : AdelicGL 3 (𝓞 ℚ) ℚ) (k : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    archComponent3 (𝓞 ℚ) ℚ (y * finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) = archComponent3 (𝓞 ℚ) ℚ y := by
  rw [map_mul, archComponent3_finEmbedN_three, mul_one]

private theorem fst_coe_mul_finEmbedN (y : AdelicGL 3 (𝓞 ℚ) ℚ)
    (k : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) (i j : Fin 3) :
    (((y * finEmbedN (Fin 3) (𝓞 ℚ) ℚ k : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j).1 =
      ((y : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j).1 := by
  have h := congrArg
    (fun u : GL (Fin 3) (InfiniteAdeleRing ℚ) => (u : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i j)
    (archComponent3_mul_finEmbedN y k)
  simpa only [coe_archComponent3, RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleArch_apply] using h

end LanglandsTunnell.CubicInduction

end

end ArchimedeanFinite

section Integrability

open IsDedekindDomain NumberField MeasureTheory

noncomputable section

namespace LanglandsTunnell
namespace CubicInduction

attribute [local instance] NumberField.AdelicHaar.glBorel

private scoped instance : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ

private abbrev haarGL3 := NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ

private scoped instance : haarGL3.IsHaarMeasure := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ

private abbrev Gf := GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)

private abbrev finLevelSet (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (LocalGL3 p)) : Set Gf :=
  {k | ∀ p, componentAt3 (𝓞 ℚ) ℚ p (finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) ∈ K' p}

private abbrev adelicLevelSet (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (LocalGL3 p)) :
    Set (AdelicGL 3 (𝓞 ℚ) ℚ) :=
  {x | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p}

private theorem integrable_mul_of_support_subset {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} {C : Set (AdelicGL 3 (𝓞 ℚ) ℚ)}
    (hC : IsCompact C) (hsupp : Function.support φ ⊆ C) (hφm : AEStronglyMeasurable φ haarGL3)
    (hφb : ∃ M : ℝ, ∀ g, ‖φ g‖ ≤ M) {f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hf : Continuous f) (x : AdelicGL 3 (𝓞 ℚ) ℚ) :
    Integrable (fun g => φ g * f (x * g)) haarGL3 := by
  obtain ⟨M, hM⟩ := hφb
  have hxC : IsCompact ((fun g : AdelicGL 3 (𝓞 ℚ) ℚ => x * g) '' C) :=
    hC.image (continuous_const.mul continuous_id)
  obtain ⟨N, hN⟩ := hxC.exists_bound_of_continuousOn hf.continuousOn
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  refine Integrable.mono' (g := C.indicator fun _ => M * N) ?_ ?_ ?_
  · exact (integrableOn_const hC.measure_lt_top.ne).integrable_indicator hCm
  · exact hφm.mul (hf.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun g => ?_
    by_cases hg : g ∈ C
    · rw [Set.indicator_of_mem hg, norm_mul]
      exact mul_le_mul (hM g) (hN _ ⟨g, hg, rfl⟩) (norm_nonneg _) ((norm_nonneg _).trans (hM g))
    · have hφg : φ g = 0 := by
        by_contra h
        exact hg (hsupp (Function.mem_support.mpr h))
      simp [Set.indicator_of_notMem hg, hφg]

private theorem exists_forall_norm_le {α : (Fin 3 → Fin 3 → ℝ) → ℂ} (hα : SlabL2.IsSmoothArchFactor α)
    (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (LocalGL3 p)) {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hφ : ∀ g, φ g = α (SlabL2.archEntries g) * (adelicLevelSet K').indicator (fun _ => (1 : ℂ)) g) :
    ∃ M : ℝ, ∀ g, ‖φ g‖ ≤ M := by
  obtain ⟨M, hM⟩ := hα.1.continuous.bounded_above_of_compact_support hα.2.1
  refine ⟨M, fun g => ?_⟩
  rw [hφ g]
  by_cases hg : g ∈ adelicLevelSet K'
  · rw [Set.indicator_of_mem hg, mul_one]
    exact hM _
  · rw [Set.indicator_of_notMem hg, mul_zero, norm_zero]
    exact (norm_nonneg _).trans (hM 0)

section LevelSets

variable (e : GL (Fin 3) (InfiniteAdeleRing ℚ) →* AdelicGL 3 (𝓞 ℚ) ℚ) (fin : AdelicGL 3 (𝓞 ℚ) ℚ →* Gf)

private theorem adelicLevelSet_eq_preimage
    (hdec : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, e (archComponent3 (𝓞 ℚ) ℚ g) * finEmbedN (Fin 3) (𝓞 ℚ) ℚ (fin g) = g)
    (hcompe : ∀ (p : HeightOneSpectrum (𝓞 ℚ)) (a : GL (Fin 3) (InfiniteAdeleRing ℚ)),
      componentAt3 (𝓞 ℚ) ℚ p (e a) = 1)
    (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (LocalGL3 p)) :
    adelicLevelSet K' = fin ⁻¹' finLevelSet K' := by
  ext g
  have key : ∀ p, componentAt3 (𝓞 ℚ) ℚ p g = componentAt3 (𝓞 ℚ) ℚ p (finEmbedN (Fin 3) (𝓞 ℚ) ℚ (fin g)) := by
    intro p
    conv_lhs => rw [← hdec g]
    rw [map_mul, hcompe, one_mul]
  exact forall_congr' fun p => by rw [key p]

private theorem support_subset_image {α : (Fin 3 → Fin 3 → ℝ) → ℂ}
    (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (LocalGL3 p)) {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hφ : ∀ g, φ g = α (SlabL2.archEntries g) * (adelicLevelSet K').indicator (fun _ => (1 : ℂ)) g)
    (hdec : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, e (archComponent3 (𝓞 ℚ) ℚ g) * finEmbedN (Fin 3) (𝓞 ℚ) ℚ (fin g) = g)
    (hcompe : ∀ (p : HeightOneSpectrum (𝓞 ℚ)) (a : GL (Fin 3) (InfiniteAdeleRing ℚ)),
      componentAt3 (𝓞 ℚ) ℚ p (e a) = 1)
    (harch : ∀ (y : AdelicGL 3 (𝓞 ℚ) ℚ) (k : Gf),
      SlabL2.archEntries (y * finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) = SlabL2.archEntries y) :
    Function.support φ ⊆
      (fun q : GL (Fin 3) (InfiniteAdeleRing ℚ) × Gf => e q.1 * finEmbedN (Fin 3) (𝓞 ℚ) ℚ q.2) ''
        ({a | SlabL2.archEntries (e a) ∈ tsupport α} ×ˢ finLevelSet K') := by
  intro g hg
  rw [Function.mem_support, hφ g] at hg
  have h1 : α (SlabL2.archEntries g) ≠ 0 := left_ne_zero_of_mul hg
  have h2 : g ∈ adelicLevelSet K' := by
    by_contra hn
    exact right_ne_zero_of_mul hg (Set.indicator_of_notMem hn _)
  rw [adelicLevelSet_eq_preimage e fin hdec hcompe] at h2
  refine ⟨(archComponent3 (𝓞 ℚ) ℚ g, fin g), ⟨?_, h2⟩, hdec g⟩
  show SlabL2.archEntries (e (archComponent3 (𝓞 ℚ) ℚ g)) ∈ tsupport α
  have : SlabL2.archEntries (e (archComponent3 (𝓞 ℚ) ℚ g)) = SlabL2.archEntries g := by
    conv_rhs => rw [← hdec g]
    exact (harch _ _).symm
  rw [this]
  exact subset_tsupport α (Function.mem_support.mpr h1)

private theorem integrable_kernel_mul_of_continuous_of_decomposition
    {α : (Fin 3 → Fin 3 → ℝ) → ℂ} (hα : SlabL2.IsSmoothArchFactor α)
    (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (LocalGL3 p)) {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hφ : ∀ g, φ g = α (SlabL2.archEntries g) * (adelicLevelSet K').indicator (fun _ => (1 : ℂ)) g)
    (hdec : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, e (archComponent3 (𝓞 ℚ) ℚ g) * finEmbedN (Fin 3) (𝓞 ℚ) ℚ (fin g) = g)
    (hcompe : ∀ (p : HeightOneSpectrum (𝓞 ℚ)) (a : GL (Fin 3) (InfiniteAdeleRing ℚ)),
      componentAt3 (𝓞 ℚ) ℚ p (e a) = 1)
    (harch : ∀ (y : AdelicGL 3 (𝓞 ℚ) ℚ) (k : Gf),
      SlabL2.archEntries (y * finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) = SlabL2.archEntries y)
    (he : Continuous e) (hfin : Continuous fin) (hfinE : Continuous (finEmbedN (Fin 3) (𝓞 ℚ) ℚ))
    (harchc : Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ => α (SlabL2.archEntries g))
    (hT : IsCompact {a : GL (Fin 3) (InfiniteAdeleRing ℚ) | SlabL2.archEntries (e a) ∈ tsupport α})
    (hUo : IsOpen (finLevelSet K')) (hUc : IsCompact (finLevelSet K'))
    {f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hf : Continuous f) (x : AdelicGL 3 (𝓞 ℚ) ℚ) :
    Integrable (fun g => φ g * f (x * g)) haarGL3 := by
  refine integrable_mul_of_support_subset ((hT.prod hUc).image ?_)
    (support_subset_image e fin K' hφ hdec hcompe harch) ?_ (exists_forall_norm_le hα K' hφ) hf x
  · exact (he.comp continuous_fst).mul (hfinE.comp continuous_snd)
  · have hL : MeasurableSet (adelicLevelSet K') := by
      rw [adelicLevelSet_eq_preimage e fin hdec hcompe]
      exact (hUo.preimage hfin).measurableSet
    exact (harchc.aestronglyMeasurable.mul (aestronglyMeasurable_const.indicator hL)).congr
      (Filter.Eventually.of_forall fun g => (hφ g).symm)

end LevelSets

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_continuous_and_isArchSmooth3_smoothingOperator.SmoothingTranslation.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_continuous_and_isArchSmooth3_smoothingOperator.SmoothingTranslation.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_continuous_and_isArchSmooth3_smoothingOperator.SmoothingTranslation.LanglandsTunnell"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_continuous_and_isArchSmooth3_smoothingOperator.SmoothingTranslation.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_continuous_and_isArchSmooth3_smoothingOperator.SmoothingTranslation.LanglandsTunnell.CubicInduction"

end Integrability
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_continuous_and_isArchSmooth3_smoothingOperator.SmoothingTranslation.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_continuous_and_isArchSmooth3_smoothingOperator.SmoothingTranslation.LanglandsTunnell.CubicInduction"

section KernelIntegrability

open IsDedekindDomain NumberField MeasureTheory

noncomputable section

namespace LanglandsTunnell
namespace CubicInduction

attribute [local instance] NumberField.AdelicHaar.glBorel

private theorem archEntries_mul_finEmbedN (y : AdelicGL 3 (𝓞 ℚ) ℚ) (k : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    SlabL2.archEntries (y * finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) = SlabL2.archEntries y := by
  funext i j
  simp only [SlabL2.archEntries, fst_coe_mul_finEmbedN]

private theorem integrable_kernel_mul_of_continuous {α : (Fin 3 → Fin 3 → ℝ) → ℂ} (hα : SlabL2.IsSmoothArchFactor α)
    (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (LocalGL3 p)) {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hφ : ∀ g, φ g = α (SlabL2.archEntries g) *
      ({x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p}).indicator (fun _ => (1 : ℂ)) g)
    (harchc : Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ => α (SlabL2.archEntries g))
    (hT : IsCompact {a : GL (Fin 3) (InfiniteAdeleRing ℚ) | SlabL2.archEntries (archToAdelic3 a) ∈ tsupport α})
    (hUo : IsOpen {k : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ) |
      ∀ p, componentAt3 (𝓞 ℚ) ℚ p (finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) ∈ K' p})
    (hUc : IsCompact {k : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ) |
      ∀ p, componentAt3 (𝓞 ℚ) ℚ p (finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) ∈ K' p})
    {f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hf : Continuous f) (x : AdelicGL 3 (𝓞 ℚ) ℚ) :
    Integrable (fun g => φ g * f (x * g)) (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) :=
  integrable_kernel_mul_of_continuous_of_decomposition archToAdelic3 finPart3 hα K' hφ
    archToAdelic3_archComponent3_mul_finEmbedN_finPart3 componentAt3_archToAdelic3 archEntries_mul_finEmbedN
    continuous_archToAdelic3 continuous_finPart3 continuous_finEmbedN3 harchc hT hUo hUc hf x

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_continuous_and_isArchSmooth3_smoothingOperator.SmoothingTranslation.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_continuous_and_isArchSmooth3_smoothingOperator.SmoothingTranslation.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_continuous_and_isArchSmooth3_smoothingOperator.SmoothingTranslation.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_continuous_and_isArchSmooth3_smoothingOperator.SmoothingTranslation.LanglandsTunnell.CubicInduction"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_continuous_and_isArchSmooth3_smoothingOperator.SmoothingTranslation.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_continuous_and_isArchSmooth3_smoothingOperator.SmoothingTranslation.LanglandsTunnell.CubicInduction"

end KernelIntegrability
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_continuous_and_isArchSmooth3_smoothingOperator.SmoothingTranslation.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_continuous_and_isArchSmooth3_smoothingOperator.SmoothingTranslation.LanglandsTunnell.CubicInduction"

section KernelBounds

open IsDedekindDomain NumberField MeasureTheory

noncomputable section

namespace LanglandsTunnell
namespace CubicInduction

attribute [local instance] NumberField.AdelicHaar.glBorel

private theorem continuous_archEntries : Continuous SlabL2.archEntries := by
  have hreal : Continuous SlabL2.realCoordinate := by
    have : (SlabL2.realCoordinate : InfiniteAdeleRing ℚ → ℝ) = realCoordinateHomeomorph := by
      funext x
      exact (realCoordinateHomeomorph_apply x).symm
    rw [this]
    exact realCoordinateHomeomorph.continuous
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have hrow : Continuous fun a : AdelicGL 3 (𝓞 ℚ) ℚ => (a : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i :=
    Matrix.GeneralLinearGroup.continuous_apply (fun a => a) continuous_id i
  exact hreal.comp (continuous_fst.comp ((continuous_apply j).comp hrow))

private theorem isCompact_setOf_archEntries_archToAdelic3_mem_tsupport {α : (Fin 3 → Fin 3 → ℝ) → ℂ}
    (hα : SlabL2.IsSmoothArchFactor α) :
    IsCompact {a : GL (Fin 3) (InfiniteAdeleRing ℚ) | SlabL2.archEntries (archToAdelic3 a) ∈ tsupport α} := by
  have : {a : GL (Fin 3) (InfiniteAdeleRing ℚ) | SlabL2.archEntries (archToAdelic3 a) ∈ tsupport α} =
      archEntries3 ⁻¹' tsupport α := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_preimage, archEntries_archToAdelic3]
  rw [this]
  exact isCompact_preimage_archEntries3 hα.2.1 hα.2.2

private theorem integrable_mul_of_isSmoothingKernel {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hφ : SlabL2.IsSmoothingKernel φ)
    {f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hc : Continuous f) (x : AdelicGL 3 (𝓞 ℚ) ℚ) :
    Integrable (fun g => φ g * f (x * g)) (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := by
  obtain ⟨α, K', hα, hoc, hcof, hφeq⟩ := hφ
  have hU := isOpen_and_isCompact_setOf_forall_componentAt3_finEmbedN_mem K' (fun p => (hoc p).1)
    (fun p => (hoc p).2) hcof
  exact integrable_kernel_mul_of_continuous hα K' hφeq (hα.1.continuous.comp continuous_archEntries)
    (isCompact_setOf_archEntries_archToAdelic3_mem_tsupport hα) hU.1 hU.2 hc x

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_continuous_and_isArchSmooth3_smoothingOperator.SmoothingTranslation.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_continuous_and_isArchSmooth3_smoothingOperator.SmoothingTranslation.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_continuous_and_isArchSmooth3_smoothingOperator.SmoothingTranslation.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_continuous_and_isArchSmooth3_smoothingOperator.SmoothingTranslation.LanglandsTunnell.CubicInduction"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_continuous_and_isArchSmooth3_smoothingOperator.SmoothingTranslation.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_continuous_and_isArchSmooth3_smoothingOperator.SmoothingTranslation.LanglandsTunnell.CubicInduction"

end KernelBounds
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_continuous_and_isArchSmooth3_smoothingOperator.SmoothingTranslation.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_continuous_and_isArchSmooth3_smoothingOperator.SmoothingTranslation.LanglandsTunnell.CubicInduction"

end SmoothingTranslation
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_continuous_and_isArchSmooth3_smoothingOperator.SmoothingTranslation.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_continuous_and_isArchSmooth3_smoothingOperator.SmoothingTranslation.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_continuous_and_isArchSmooth3_smoothingOperator.SmoothingTranslation"

open LanglandsTunnell LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2
open SmoothingTranslation.LanglandsTunnell.CubicInduction

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

private scoped instance : SecondCountableTopology (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdeleRing.secondCountableTopology ℚ

private scoped instance : SecondCountableTopology (Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
  inferInstanceAs (SecondCountableTopology (Fin 3 → Fin 3 → AdeleRing (𝓞 ℚ) ℚ))

private scoped instance : SecondCountableTopology (Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

private scoped instance : SecondCountableTopology (AdelicGL 3 (𝓞 ℚ) ℚ) :=
  Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

private def SmoothingDeriv.realAdeleHom : ℝ →+* InfiniteAdeleRing ℚ :=
  RingHom.pi fun v => (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.toRingHom

private theorem SmoothingDeriv.archRealMat3_eq (e : Fin 3 → Fin 3 → ℝ) :
    WhittakerBlock.archRealMat3 e = archMatrixInclN (Fin 3) ℚ ((Matrix.of e).map SmoothingDeriv.realAdeleHom) :=
  rfl

private theorem SmoothingDeriv.isUnit_archRealMat3 {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    IsUnit (WhittakerBlock.archRealMat3 e) := by
  have hdet : IsUnit ((Matrix.of e).map SmoothingDeriv.realAdeleHom) := by
    rw [Matrix.isUnit_iff_isUnit_det, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (isUnit_iff_ne_zero.2 he).map SmoothingDeriv.realAdeleHom
  rw [SmoothingDeriv.archRealMat3_eq]
  exact hdet.map (archMatrixInclHomN (Fin 3) ℚ)

private theorem SmoothingDeriv.coe_archRealLift3 {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    (WhittakerBlock.archRealLift3 e : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) = WhittakerBlock.archRealMat3 e := by
  unfold WhittakerBlock.archRealLift3
  rw [dif_pos (SmoothingDeriv.isUnit_archRealMat3 he)]
  exact (SmoothingDeriv.isUnit_archRealMat3 he).unit_spec

private theorem SmoothingDeriv.realCoordinate_realAdeleHom (r : ℝ) :
    realCoordinate (SmoothingDeriv.realAdeleHom r) = r := by
  show InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal Rat.infinitePlace)
    ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal Rat.infinitePlace)).symm r) = r
  exact (InfinitePlace.Completion.ringEquivRealOfIsReal _).apply_symm_apply r

private theorem SmoothingDeriv.archEntries_mul (g h : AdelicGL 3 (𝓞 ℚ) ℚ) :
    archEntries (g * h) = fun a b => ∑ c, archEntries g a c * archEntries h c b := by
  funext a b
  show realCoordinate (AdelicLevel.adeleArch (𝓞 ℚ) ℚ
    (((g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) * (h : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))) a b)) = _
  rw [Matrix.mul_apply, map_sum, map_sum]
  simp only [map_mul, archEntries, AdelicLevel.adeleArch_apply]

private theorem SmoothingDeriv.archEntries_one :
    archEntries (1 : AdelicGL 3 (𝓞 ℚ) ℚ) = fun a b => if a = b then (1 : ℝ) else 0 := by
  funext a b
  show realCoordinate (AdelicLevel.adeleArch (𝓞 ℚ) ℚ
    (((1 : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) a b)) = _
  rw [Units.val_one, Matrix.one_apply]
  split_ifs <;> simp

private theorem SmoothingDeriv.archEntries_archRealLift3 (e : Fin 3 → Fin 3 → ℝ) (he : (Matrix.of e).det ≠ 0) :
    archEntries (WhittakerBlock.archRealLift3 e) = e := by
  funext a b
  show realCoordinate ((WhittakerBlock.archRealLift3 e : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) a b).1 = e a b
  rw [SmoothingDeriv.coe_archRealLift3 he, SmoothingDeriv.archRealMat3_eq]
  exact SmoothingDeriv.realCoordinate_realAdeleHom (e a b)

private theorem SmoothingDeriv.map_adeleFin_archRealMat3 (e : Fin 3 → Fin 3 → ℝ) :
    (WhittakerBlock.archRealMat3 e).map (AdelicLevel.adeleFin (𝓞 ℚ) ℚ) = 1 := by
  refine Matrix.ext fun a b => ?_
  rw [SmoothingDeriv.archRealMat3_eq]
  exact adeleFin_archMatrixInclN (Fin 3) ℚ ((Matrix.of e).map SmoothingDeriv.realAdeleHom) a b

private theorem SmoothingDeriv.componentAt3_archRealLift3 (p : HeightOneSpectrum (𝓞 ℚ)) (e : Fin 3 → Fin 3 → ℝ) :
    componentAt3 (𝓞 ℚ) ℚ p (WhittakerBlock.archRealLift3 e) = 1 := by
  unfold WhittakerBlock.archRealLift3
  split_ifs with h
  · apply Units.ext
    show (h.unit : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).map
      ((AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ p).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)) = 1
    rw [h.unit_spec, RingHom.coe_comp, ← Matrix.map_map, SmoothingDeriv.map_adeleFin_archRealMat3,
      Matrix.map_one _ (map_zero _) (map_one _)]
  · exact map_one _

private theorem SmoothingDeriv.norm_indicator_one_le (L : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (y : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ‖Set.indicator L (fun _ => (1 : ℂ)) y‖ ≤ 1 := by
  by_cases hy : y ∈ L
  · rw [Set.indicator_of_mem hy, norm_one]
  · rw [Set.indicator_of_notMem hy, norm_zero]
    exact zero_le_one

private theorem SmoothingDeriv.integrable_indicator_comp_mul {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hF : LocallyIntegrable F (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)) (x : AdelicGL 3 (𝓞 ℚ) ℚ)
    {C : Set (AdelicGL 3 (𝓞 ℚ) ℚ)} (hC : IsCompact C) :
    Integrable (Set.indicator C fun y => F (x * y)) (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := by
  haveI : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
  have hxC : IsCompact ((fun y : AdelicGL 3 (𝓞 ℚ) ℚ => x * y) '' C) := hC.image (continuous_const_mul x)
  have hme : MeasurableEmbedding fun y : AdelicGL 3 (𝓞 ℚ) ℚ => x * y :=
    (MeasurableEquiv.mulLeft x).measurableEmbedding
  have hIntC : IntegrableOn (fun y => F (x * y)) C (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := by
    have h := hF.integrableOn_isCompact hxC
    have hmp := (measurePreserving_mul_left (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)
      x).integrableOn_comp_preimage hme (f := F) (s := (fun y : AdelicGL 3 (𝓞 ℚ) ℚ => x * y) '' C)
    rw [Set.preimage_image_eq _ (mul_right_injective x)] at hmp
    exact hmp.mpr h
  exact hIntC.integrable_indicator hC.isClosed.measurableSet

private def KernelSmooth.mulArr (d m : Fin 3 → Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ := fun a b => ∑ c, d a c * m c b

private def KernelSmooth.invArr (e : Fin 3 → Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun a b => (Matrix.of e)⁻¹ a b

private def KernelSmooth.idArr : Fin 3 → Fin 3 → ℝ := fun a b => if a = b then (1 : ℝ) else 0

private theorem KernelSmooth.of_mulArr (d m : Fin 3 → Fin 3 → ℝ) :
    Matrix.of (KernelSmooth.mulArr d m) = Matrix.of d * Matrix.of m := by
  ext a b
  simp [KernelSmooth.mulArr, Matrix.mul_apply]

private theorem KernelSmooth.of_invArr (e : Fin 3 → Fin 3 → ℝ) :
    Matrix.of (KernelSmooth.invArr e) = (Matrix.of e)⁻¹ := by
  ext a b
  rfl

private theorem KernelSmooth.of_idArr : Matrix.of KernelSmooth.idArr = 1 := by
  ext a b
  simp [KernelSmooth.idArr, Matrix.one_apply]

private theorem KernelSmooth.of_injective {p q : Fin 3 → Fin 3 → ℝ} (h : Matrix.of p = Matrix.of q) : p = q := by
  funext a b
  exact congrFun (congrFun h a) b

private theorem KernelSmooth.mulArr_invArr_self {d : Fin 3 → Fin 3 → ℝ} (hd : (Matrix.of d).det ≠ 0) :
    KernelSmooth.mulArr (KernelSmooth.invArr d) d = KernelSmooth.idArr := by
  apply KernelSmooth.of_injective
  rw [KernelSmooth.of_mulArr, KernelSmooth.of_invArr, KernelSmooth.of_idArr,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hd)]

private theorem KernelSmooth.mulArr_invArr_mulArr {d : Fin 3 → Fin 3 → ℝ} (hd : (Matrix.of d).det ≠ 0)
    (m : Fin 3 → Fin 3 → ℝ) : KernelSmooth.mulArr d (KernelSmooth.mulArr (KernelSmooth.invArr d) m) = m := by
  apply KernelSmooth.of_injective
  rw [KernelSmooth.of_mulArr, KernelSmooth.of_mulArr, KernelSmooth.of_invArr,
    Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.2 hd)]

private theorem KernelSmooth.invArr_mulArr_mulArr {d : Fin 3 → Fin 3 → ℝ} (hd : (Matrix.of d).det ≠ 0)
    (m : Fin 3 → Fin 3 → ℝ) : KernelSmooth.mulArr (KernelSmooth.invArr d) (KernelSmooth.mulArr d m) = m := by
  apply KernelSmooth.of_injective
  rw [KernelSmooth.of_mulArr, KernelSmooth.of_mulArr, KernelSmooth.of_invArr,
    Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_iff_ne_zero.2 hd)]

private theorem KernelSmooth.mulArr_invArr_mulArr_mulArr {d : Fin 3 → Fin 3 → ℝ} (hd : (Matrix.of d).det ≠ 0)
    (h m : Fin 3 → Fin 3 → ℝ) :
    KernelSmooth.mulArr (KernelSmooth.mulArr h (KernelSmooth.invArr d)) (KernelSmooth.mulArr d m) =
      KernelSmooth.mulArr h m := by
  apply KernelSmooth.of_injective
  rw [KernelSmooth.of_mulArr, KernelSmooth.of_mulArr, KernelSmooth.of_mulArr, KernelSmooth.of_mulArr,
    KernelSmooth.of_invArr, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_right _ _ (isUnit_iff_ne_zero.2 hd)]

private theorem KernelSmooth.det_invArr_ne_zero {d : Fin 3 → Fin 3 → ℝ} (hd : (Matrix.of d).det ≠ 0) :
    (Matrix.of (KernelSmooth.invArr d)).det ≠ 0 := by
  rw [KernelSmooth.of_invArr, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  exact inv_ne_zero hd

private theorem KernelSmooth.det_mulArr_ne_zero {d m : Fin 3 → Fin 3 → ℝ} (hd : (Matrix.of d).det ≠ 0)
    (hm : (Matrix.of m).det ≠ 0) : (Matrix.of (KernelSmooth.mulArr d m)).det ≠ 0 := by
  rw [KernelSmooth.of_mulArr, Matrix.det_mul]
  exact mul_ne_zero hd hm

private theorem KernelSmooth.contDiff_det :
    ContDiff ℝ (⊤ : ℕ∞) fun e : Fin 3 → Fin 3 → ℝ => (Matrix.of e).det := by
  simp only [Matrix.det_fin_three, Matrix.of_apply]
  fun_prop

private theorem KernelSmooth.contDiff_adjugate (a b : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) fun e : Fin 3 → Fin 3 → ℝ => (Matrix.of e).adjugate a b := by
  fin_cases a <;> fin_cases b <;> simp [Matrix.adjugate_fin_three] <;> fun_prop

private theorem KernelSmooth.contDiffOn_invArr :
    ContDiffOn ℝ (⊤ : ℕ∞) KernelSmooth.invArr {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} := by
  refine contDiffOn_pi.2 fun a => contDiffOn_pi.2 fun b => ?_
  have h : ∀ e ∈ {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0},
      KernelSmooth.invArr e a b = ((Matrix.of e).det)⁻¹ * (Matrix.of e).adjugate a b := by
    intro e _
    show ((Matrix.of e)⁻¹) a b = _
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  refine ContDiffOn.congr ?_ h
  exact (KernelSmooth.contDiff_det.contDiffOn.inv fun e he => he).mul (KernelSmooth.contDiff_adjugate a b).contDiffOn

private theorem KernelSmooth.continuousOn_invArr :
    ContinuousOn KernelSmooth.invArr {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} :=
  KernelSmooth.contDiffOn_invArr.continuousOn

private theorem KernelSmooth.isOpen_det_ne_zero : IsOpen {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} :=
  isOpen_ne_fun KernelSmooth.contDiff_det.continuous continuous_const

private def KernelSmooth.mulRightL (m : Fin 3 → Fin 3 → ℝ) : (Fin 3 → Fin 3 → ℝ) →L[ℝ] (Fin 3 → Fin 3 → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun h => KernelSmooth.mulArr h m
      map_add' := fun h h' => by
        funext a b
        simp only [KernelSmooth.mulArr, Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun r h => by
        funext a b
        simp only [KernelSmooth.mulArr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc] }

private theorem KernelSmooth.mulRightL_apply (m h : Fin 3 → Fin 3 → ℝ) :
    KernelSmooth.mulRightL m h = KernelSmooth.mulArr h m :=
  rfl

private theorem KernelSmooth.continuous_mulArr_right (d : Fin 3 → Fin 3 → ℝ) :
    Continuous fun m : Fin 3 → Fin 3 → ℝ => KernelSmooth.mulArr d m := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [KernelSmooth.mulArr, Fin.sum_univ_three]
  fun_prop

private theorem KernelSmooth.continuous_mulArr :
    Continuous fun q : (Fin 3 → Fin 3 → ℝ) × (Fin 3 → Fin 3 → ℝ) => KernelSmooth.mulArr q.1 q.2 := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [KernelSmooth.mulArr, Fin.sum_univ_three]
  fun_prop

private theorem KernelSmooth.norm_mulArr_le (h m : Fin 3 → Fin 3 → ℝ) :
    ‖KernelSmooth.mulArr h m‖ ≤ 3 * ‖m‖ * ‖h‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun a => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun b => ?_
  show ‖∑ c, h a c * m c b‖ ≤ 3 * ‖m‖ * ‖h‖
  refine (norm_sum_le _ _).trans ?_
  calc ∑ c, ‖h a c * m c b‖ ≤ ∑ _c : Fin 3, ‖h‖ * ‖m‖ := by
        refine Finset.sum_le_sum fun c _ => ?_
        rw [norm_mul]
        exact mul_le_mul ((norm_le_pi_norm (h a) c).trans (norm_le_pi_norm h a))
          ((norm_le_pi_norm (m c) b).trans (norm_le_pi_norm m c)) (norm_nonneg _) (norm_nonneg _)
    _ = 3 * ‖m‖ * ‖h‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        simp only [nsmul_eq_mul, Nat.cast_ofNat]
        ring

private theorem KernelSmooth.norm_mulRightL_le (m : Fin 3 → Fin 3 → ℝ) : ‖KernelSmooth.mulRightL m‖ ≤ 3 * ‖m‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => KernelSmooth.norm_mulArr_le h m

private theorem KernelSmooth.archRealLift3_idArr : WhittakerBlock.archRealLift3 KernelSmooth.idArr = 1 := by
  have hdet : (Matrix.of KernelSmooth.idArr).det ≠ 0 := by
    rw [KernelSmooth.of_idArr, Matrix.det_one]
    exact one_ne_zero
  apply Units.ext
  rw [SmoothingDeriv.coe_archRealLift3 hdet, SmoothingDeriv.archRealMat3_eq, KernelSmooth.of_idArr,
    Matrix.map_one _ (map_zero _) (map_one _), AutomorphicForm.archMatrixInclN_one, Units.val_one]

private theorem KernelSmooth.archRealLift3_invArr_mul {d : Fin 3 → Fin 3 → ℝ} (hd : (Matrix.of d).det ≠ 0) :
    WhittakerBlock.archRealLift3 (KernelSmooth.invArr d) * WhittakerBlock.archRealLift3 d = 1 := by
  rw [WhittakerBlock.archRealLift3_mul (KernelSmooth.det_invArr_ne_zero hd) hd, ← KernelSmooth.archRealLift3_idArr]
  congr 1
  funext a b
  rw [KernelSmooth.of_invArr, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hd)]
  simp [Matrix.one_apply, KernelSmooth.idArr]

private theorem KernelSmooth.archEntries_lift_mul {d : Fin 3 → Fin 3 → ℝ} (hd : (Matrix.of d).det ≠ 0)
    (y : AdelicGL 3 (𝓞 ℚ) ℚ) :
    archEntries (WhittakerBlock.archRealLift3 d * y) = KernelSmooth.mulArr d (archEntries y) := by
  rw [SmoothingDeriv.archEntries_mul, SmoothingDeriv.archEntries_archRealLift3 d hd]
  rfl

private theorem KernelSmooth.componentAt3_lift_mul (d : Fin 3 → Fin 3 → ℝ) (y : AdelicGL 3 (𝓞 ℚ) ℚ)
    (p : HeightOneSpectrum (𝓞 ℚ)) :
    componentAt3 (𝓞 ℚ) ℚ p (WhittakerBlock.archRealLift3 d * y) = componentAt3 (𝓞 ℚ) ℚ p y := by
  rw [map_mul, SmoothingDeriv.componentAt3_archRealLift3, one_mul]

private theorem KernelSmooth.apply_lift_mul {α : (Fin 3 → Fin 3 → ℝ) → ℂ}
    {K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ))}
    {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hφ : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, φ g = α (archEntries g) *
      Set.indicator {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p} (fun _ => (1 : ℂ)) g)
    {d : Fin 3 → Fin 3 → ℝ} (hd : (Matrix.of d).det ≠ 0) (y : AdelicGL 3 (𝓞 ℚ) ℚ) :
    φ (WhittakerBlock.archRealLift3 d * y) = α (KernelSmooth.mulArr d (archEntries y)) *
      Set.indicator {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p} (fun _ => (1 : ℂ)) y := by
  rw [hφ, KernelSmooth.archEntries_lift_mul hd]
  congr 1
  have hmem : (WhittakerBlock.archRealLift3 d * y ∈
      {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p}) ↔
        y ∈ {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p} := by
    simp only [Set.mem_setOf_eq, KernelSmooth.componentAt3_lift_mul]
  by_cases hy : y ∈ {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p}
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (hmem.2 hy)]
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (mt hmem.1 hy)]

private theorem KernelSmooth.smoothingOperator_eq_integral_inv (φ F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (x : AdelicGL 3 (𝓞 ℚ) ℚ) :
    smoothingOperator φ F x =
      ∫ y, φ (x⁻¹ * y) * F y ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := by
  haveI : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
  rw [smoothingOperator_apply]
  have key : (fun y => φ y * F (x * y)) = fun y => (fun z => φ (x⁻¹ * z) * F z) (x * y) := by
    funext y
    simp only [inv_mul_cancel_left]
  rw [key]
  exact integral_mul_left_eq_self (fun z => φ (x⁻¹ * z) * F z) x

private theorem KernelSmooth.smoothingOperator_mul_lift (φ F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (g : AdelicGL 3 (𝓞 ℚ) ℚ)
    {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    smoothingOperator φ F (g * WhittakerBlock.archRealLift3 e) =
      ∫ y, φ (WhittakerBlock.archRealLift3 (KernelSmooth.invArr e) * y) * F (g * y)
        ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := by
  haveI : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
  rw [smoothingOperator_apply]
  have key : (fun y => φ y * F (g * WhittakerBlock.archRealLift3 e * y)) = fun y =>
      (fun z => φ (WhittakerBlock.archRealLift3 (KernelSmooth.invArr e) * z) * F (g * z))
        (WhittakerBlock.archRealLift3 e * y) := by
    funext y
    simp only [← mul_assoc, KernelSmooth.archRealLift3_invArr_mul he, one_mul]
  rw [key]
  exact integral_mul_left_eq_self
    (fun z => φ (WhittakerBlock.archRealLift3 (KernelSmooth.invArr e) * z) * F (g * z))
    (WhittakerBlock.archRealLift3 e)

private theorem KernelSmooth.box_clopen_and_carrier
    {K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ))}
    (hoc : ∀ p, IsOpen (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ))) ∧
      IsCompact (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ))))
    (hcof : ∀ᶠ p in Filter.cofinite, K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p) :
    IsOpen {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p} ∧
      IsClosed {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p} ∧
      ∀ T : Set (Fin 3 → Fin 3 → ℝ), IsCompact T → T ⊆ {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} →
        ∃ C : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact C ∧ ∀ y : AdelicGL 3 (𝓞 ℚ) ℚ,
          y ∈ {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p} → archEntries y ∈ T → y ∈ C := by
  have hU := isOpen_and_isCompact_setOf_forall_componentAt3_finEmbedN_mem K' (fun p => (hoc p).1)
    (fun p => (hoc p).2) hcof
  have hL : {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p} =
      finPart3 ⁻¹' {k : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ) |
        ∀ p, componentAt3 (𝓞 ℚ) ℚ p (finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) ∈ K' p} :=
    adelicLevelSet_eq_preimage archToAdelic3 finPart3 archToAdelic3_archComponent3_mul_finEmbedN_finPart3
      componentAt3_archToAdelic3 K'
  refine ⟨?_, ?_, fun T hT hTU => ?_⟩
  · rw [hL]
    exact hU.1.preimage continuous_finPart3
  · rw [hL]
    exact hU.2.isClosed.preimage continuous_finPart3
  have hA : IsCompact {a : GL (Fin 3) (InfiniteAdeleRing ℚ) | archEntries (archToAdelic3 a) ∈ T} := by
    have : {a : GL (Fin 3) (InfiniteAdeleRing ℚ) | archEntries (archToAdelic3 a) ∈ T} = archEntries3 ⁻¹' T := by
      ext a
      simp only [Set.mem_setOf_eq, Set.mem_preimage, archEntries_archToAdelic3]
    rw [this]
    exact isCompact_preimage_archEntries3 hT hTU
  refine ⟨(fun q : GL (Fin 3) (InfiniteAdeleRing ℚ) × GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ) =>
      archToAdelic3 q.1 * finEmbedN (Fin 3) (𝓞 ℚ) ℚ q.2) ''
    ({a : GL (Fin 3) (InfiniteAdeleRing ℚ) | archEntries (archToAdelic3 a) ∈ T} ×ˢ
      {k : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ) | ∀ p, componentAt3 (𝓞 ℚ) ℚ p (finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) ∈ K' p}),
    (hA.prod hU.2).image ((continuous_archToAdelic3.comp continuous_fst).mul
      (continuous_finEmbedN3.comp continuous_snd)), fun y hy hY => ?_⟩
  refine ⟨(archComponent3 (𝓞 ℚ) ℚ y, finPart3 y), ⟨?_, ?_⟩, archToAdelic3_archComponent3_mul_finEmbedN_finPart3 y⟩
  · show archEntries (archToAdelic3 (archComponent3 (𝓞 ℚ) ℚ y)) ∈ T
    have hsame : archEntries (archToAdelic3 (archComponent3 (𝓞 ℚ) ℚ y)) = archEntries y := by
      conv_rhs => rw [← archToAdelic3_archComponent3_mul_finEmbedN_finPart3 y]
      exact (archEntries_mul_finEmbedN _ _).symm
    rw [hsame]
    exact hY
  · show finPart3 y ∈ {k : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ) |
      ∀ p, componentAt3 (𝓞 ℚ) ℚ p (finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) ∈ K' p}
    rw [← Set.mem_preimage, ← hL]
    exact hy

private theorem KernelSmooth.stronglyMeasurable_kernel {α : (Fin 3 → Fin 3 → ℝ) → ℂ} (hα : IsSmoothArchFactor α)
    {L : Set (AdelicGL 3 (𝓞 ℚ) ℚ)} (hLm : MeasurableSet L) {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hφ : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, φ g = α (archEntries g) * Set.indicator L (fun _ => (1 : ℂ)) g) :
    StronglyMeasurable φ := by
  haveI : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  have h : φ = fun g => α (archEntries g) * Set.indicator L (fun _ => (1 : ℂ)) g := funext hφ
  rw [h]
  exact (hα.1.continuous.comp continuous_archEntries).stronglyMeasurable.mul (stronglyMeasurable_const.indicator hLm)

private theorem KernelSmooth.exists_norm_le {α : (Fin 3 → Fin 3 → ℝ) → ℂ} (hα : IsSmoothArchFactor α)
    (L : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hφ : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, φ g = α (archEntries g) * Set.indicator L (fun _ => (1 : ℂ)) g) :
    ∃ M : ℝ, ∀ g, ‖φ g‖ ≤ M := by
  obtain ⟨M, hM⟩ := hα.1.continuous.bounded_above_of_compact_support hα.2.1
  refine ⟨M, fun g => ?_⟩
  rw [hφ, norm_mul]
  refine (mul_le_mul (hM _) (SmoothingDeriv.norm_indicator_one_le L g) (norm_nonneg _)
    ((norm_nonneg _).trans (hM 0))).trans_eq (mul_one M)

private theorem KernelSmooth.continuous_smoothingOperator {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hφ : IsSmoothingKernel φ)
    {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hF : LocallyIntegrable F (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)) :
    Continuous (smoothingOperator φ F) := by
  haveI : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
  obtain ⟨α, K', hα, hoc, hcof, hφeq⟩ := hφ
  obtain ⟨hLo, hLc, hcar⟩ := KernelSmooth.box_clopen_and_carrier hoc hcof
  set Lb : Set (AdelicGL 3 (𝓞 ℚ) ℚ) := {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p} with hLb
  obtain ⟨Cφ, hCφ, hmemCφ⟩ := hcar (tsupport α) hα.2.1 hα.2.2
  obtain ⟨M, hM⟩ := KernelSmooth.exists_norm_le hα _ hφeq
  have hφsm := KernelSmooth.stronglyMeasurable_kernel hα hLc.measurableSet hφeq
  have heq : smoothingOperator φ F = fun x =>
      ∫ y, φ (x⁻¹ * y) * F y ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) :=
    funext (KernelSmooth.smoothingOperator_eq_integral_inv φ F)
  rw [heq]
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  obtain ⟨N, hN, hNx⟩ := exists_compact_mem_nhds x₀

  have hC : IsCompact ((fun q : AdelicGL 3 (𝓞 ℚ) ℚ × AdelicGL 3 (𝓞 ℚ) ℚ => q.1 * q.2) '' (N ×ˢ Cφ)) :=
    (hN.prod hCφ).image (continuous_fst.mul continuous_snd)
  have hmem : ∀ x ∈ N, ∀ y, φ (x⁻¹ * y) ≠ 0 →
      y ∈ (fun q : AdelicGL 3 (𝓞 ℚ) ℚ × AdelicGL 3 (𝓞 ℚ) ℚ => q.1 * q.2) '' (N ×ˢ Cφ) := by
    intro x hx y hy
    rw [hφeq] at hy
    have hyL : x⁻¹ * y ∈ Lb := by
      by_contra h
      exact right_ne_zero_of_mul hy (Set.indicator_of_notMem h _)
    exact ⟨(x, x⁻¹ * y), ⟨hx, hmemCφ _ hyL (subset_tsupport α (left_ne_zero_of_mul hy))⟩, mul_inv_cancel_left x y⟩
  refine continuousAt_of_dominated (bound := fun y => M * ‖Set.indicator
      ((fun q : AdelicGL 3 (𝓞 ℚ) ℚ × AdelicGL 3 (𝓞 ℚ) ℚ => q.1 * q.2) '' (N ×ˢ Cφ)) F y‖) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun x =>
      (hφsm.comp_measurable (measurable_const_mul x⁻¹)).aestronglyMeasurable.mul hF.aestronglyMeasurable
  · refine Filter.eventually_of_mem hNx fun x hx => Filter.Eventually.of_forall fun y => ?_
    show ‖φ (x⁻¹ * y) * F y‖ ≤ M * ‖Set.indicator
      ((fun q : AdelicGL 3 (𝓞 ℚ) ℚ × AdelicGL 3 (𝓞 ℚ) ℚ => q.1 * q.2) '' (N ×ˢ Cφ)) F y‖
    by_cases hz : φ (x⁻¹ * y) = 0
    · rw [hz, zero_mul, norm_zero]
      exact mul_nonneg ((norm_nonneg _).trans (hM 1)) (norm_nonneg _)
    · rw [norm_mul, Set.indicator_of_mem (hmem x hx y hz)]
      exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
  · exact ((hF.integrableOn_isCompact hC).integrable_indicator hC.isClosed.measurableSet).norm.const_mul M
  · refine Filter.Eventually.of_forall fun y => ?_
    have hm : Continuous fun x : AdelicGL 3 (𝓞 ℚ) ℚ => x⁻¹ * y := continuous_inv.mul continuous_const
    have h1 : Continuous fun x : AdelicGL 3 (𝓞 ℚ) ℚ => α (archEntries (x⁻¹ * y)) :=
      hα.1.continuous.comp (continuous_archEntries.comp hm)
    have h2 : ContinuousAt (fun x : AdelicGL 3 (𝓞 ℚ) ℚ => Set.indicator Lb (fun _ => (1 : ℂ)) (x⁻¹ * y)) x₀ := by
      by_cases hy : x₀⁻¹ * y ∈ Lb
      · have hev : ∀ᶠ x in nhds x₀, x⁻¹ * y ∈ Lb := hm.continuousAt.preimage_mem_nhds (hLo.mem_nhds hy)
        refine (continuousAt_const : ContinuousAt (fun _ : AdelicGL 3 (𝓞 ℚ) ℚ => (1 : ℂ)) x₀).congr ?_
        filter_upwards [hev] with x hx
        exact (Set.indicator_of_mem hx fun _ : AdelicGL 3 (𝓞 ℚ) ℚ => (1 : ℂ)).symm
      · have hev : ∀ᶠ x in nhds x₀, x⁻¹ * y ∈ Lbᶜ :=
          hm.continuousAt.preimage_mem_nhds (hLc.isOpen_compl.mem_nhds hy)
        refine (continuousAt_const : ContinuousAt (fun _ : AdelicGL 3 (𝓞 ℚ) ℚ => (0 : ℂ)) x₀).congr ?_
        filter_upwards [hev] with x hx
        exact (Set.indicator_of_notMem hx fun _ : AdelicGL 3 (𝓞 ℚ) ℚ => (1 : ℂ)).symm
    have h3 : ContinuousAt (fun x : AdelicGL 3 (𝓞 ℚ) ℚ => φ (x⁻¹ * y)) x₀ := by
      have : (fun x : AdelicGL 3 (𝓞 ℚ) ℚ => φ (x⁻¹ * y)) = fun x => α (archEntries (x⁻¹ * y)) *
          Set.indicator Lb (fun _ => (1 : ℂ)) (x⁻¹ * y) := funext fun x => hφeq _
      rw [this]
      exact h1.continuousAt.mul h2
    exact ContinuousAt.mul h3 (continuousAt_const : ContinuousAt (fun _ : AdelicGL 3 (𝓞 ℚ) ℚ => F y) x₀)

private def KernelSmooth.elemArr (a b : Fin 3) : Fin 3 → Fin 3 → ℝ := fun i k => if i = a ∧ k = b then (1 : ℝ) else 0

private theorem KernelSmooth.mulArr_elemArr_apply (a b : Fin 3) (m : Fin 3 → Fin 3 → ℝ) (i k : Fin 3) :
    KernelSmooth.mulArr (KernelSmooth.elemArr a b) m i k = if i = a then m b k else 0 := by
  simp only [KernelSmooth.mulArr, KernelSmooth.elemArr, ite_mul, one_mul, zero_mul]
  by_cases hi : i = a
  · rw [if_pos hi, Finset.sum_eq_single b (fun c _ hc => if_neg fun h => hc h.2)
      (fun h => absurd (Finset.mem_univ b) h), if_pos ⟨hi, rfl⟩]
  · rw [if_neg hi]
    exact Finset.sum_eq_zero fun c _ => if_neg fun h => hi h.1

private theorem KernelSmooth.mulArr_eq_sum (p m : Fin 3 → Fin 3 → ℝ) :
    KernelSmooth.mulArr p m = ∑ a, ∑ b, p a b • KernelSmooth.mulArr (KernelSmooth.elemArr a b) m := by
  funext i k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, KernelSmooth.mulArr_elemArr_apply, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rfl

private theorem KernelSmooth.contDiff_mulArr_right (d : Fin 3 → Fin 3 → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) fun m : Fin 3 → Fin 3 → ℝ => KernelSmooth.mulArr d m := by
  refine contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_
  simp only [KernelSmooth.mulArr, Fin.sum_univ_three]
  fun_prop

private def KernelSmooth.mulRightLin : (Fin 3 → Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → Fin 3 → ℝ) →L[ℝ] (Fin 3 → Fin 3 → ℝ) where
  toFun := KernelSmooth.mulRightL
  map_add' m m' := by
    ext h a b
    simp only [KernelSmooth.mulRightL_apply, ContinuousLinearMap.add_apply, Pi.add_apply, KernelSmooth.mulArr, mul_add,
      Finset.sum_add_distrib]
  map_smul' r m := by
    ext h a b
    simp only [KernelSmooth.mulRightL_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, KernelSmooth.mulArr, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring

private theorem KernelSmooth.continuous_mulRightL : Continuous KernelSmooth.mulRightL :=
  KernelSmooth.mulRightLin.continuous_of_finiteDimensional

private def KernelSmooth.dKer (β : (Fin 3 → Fin 3 → ℝ) → ℂ) (a b : Fin 3) (m : Fin 3 → Fin 3 → ℝ) : ℂ :=
  (fderiv ℝ β m) (KernelSmooth.mulArr (KernelSmooth.elemArr a b) m)

private theorem KernelSmooth.contDiff_dKer {β : (Fin 3 → Fin 3 → ℝ) → ℂ} (hβ : ContDiff ℝ (⊤ : ℕ∞) β) (a b : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (KernelSmooth.dKer β a b) :=
  (contDiff_infty_iff_fderiv.1 hβ).2.clm_apply (KernelSmooth.contDiff_mulArr_right _)

private theorem KernelSmooth.hasCompactSupport_dKer {β : (Fin 3 → Fin 3 → ℝ) → ℂ} (hβc : HasCompactSupport β)
    (a b : Fin 3) :
    HasCompactSupport (KernelSmooth.dKer β a b) := by
  refine (hβc.fderiv ℝ).mono fun m hm => ?_
  intro h
  exact hm (by simp only [KernelSmooth.dKer, h, ContinuousLinearMap.zero_apply])

private theorem KernelSmooth.tsupport_dKer_subset {β : (Fin 3 → Fin 3 → ℝ) → ℂ} (a b : Fin 3) :
    tsupport (KernelSmooth.dKer β a b) ⊆ tsupport β := by
  refine (closure_mono fun m hm => ?_).trans (tsupport_fderiv_subset ℝ)
  intro h
  exact hm (by simp only [KernelSmooth.dKer, h, ContinuousLinearMap.zero_apply])

private theorem KernelSmooth.fderiv_apply_mulArr (β : (Fin 3 → Fin 3 → ℝ) → ℂ) {d : Fin 3 → Fin 3 → ℝ}
    (hd : (Matrix.of d).det ≠ 0) (h m : Fin 3 → Fin 3 → ℝ) :
    (fderiv ℝ β (KernelSmooth.mulArr d m)) (KernelSmooth.mulArr h m) =
      ∑ a, ∑ b, ((KernelSmooth.mulArr h (KernelSmooth.invArr d) a b : ℝ) : ℂ) *
        KernelSmooth.dKer β a b (KernelSmooth.mulArr d m) := by
  rw [← KernelSmooth.mulArr_invArr_mulArr_mulArr hd h m,
    KernelSmooth.mulArr_eq_sum (KernelSmooth.mulArr h (KernelSmooth.invArr d)) (KernelSmooth.mulArr d m), map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [ContinuousLinearMap.map_smul, Complex.real_smul]
  rfl

private def KernelSmooth.Psi (β : (Fin 3 → Fin 3 → ℝ) → ℂ) (G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (d : Fin 3 → Fin 3 → ℝ) : ℂ :=
  ∫ y, G y * β (KernelSmooth.mulArr d (archEntries y)) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)

private theorem KernelSmooth.exists_ball_carrier {L : Set (AdelicGL 3 (𝓞 ℚ) ℚ)}
    (hcar : ∀ T : Set (Fin 3 → Fin 3 → ℝ), IsCompact T → T ⊆ {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} →
      ∃ C : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact C ∧ ∀ y : AdelicGL 3 (𝓞 ℚ) ℚ, y ∈ L → archEntries y ∈ T → y ∈ C)
    {G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hGL : ∀ y, y ∉ L → G y = 0)
    {T : Set (Fin 3 → Fin 3 → ℝ)} (hT : IsCompact T) (hTU : T ⊆ {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0})
    {d₀ : Fin 3 → Fin 3 → ℝ} (hd₀ : (Matrix.of d₀).det ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall d₀ r ⊆ {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} ∧
      ∃ C : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact C ∧ ∀ d ∈ Metric.closedBall d₀ r, ∀ y : AdelicGL 3 (𝓞 ℚ) ℚ,
        ∀ v : ℂ, G y * v ≠ 0 → (v ≠ 0 → KernelSmooth.mulArr d (archEntries y) ∈ T) → y ∈ C := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 KernelSmooth.isOpen_det_ne_zero d₀ hd₀
  have hB : Metric.closedBall d₀ (ε / 2) ⊆ {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hεU
  set T' : Set (Fin 3 → Fin 3 → ℝ) := (fun q : (Fin 3 → Fin 3 → ℝ) × (Fin 3 → Fin 3 → ℝ) =>
    KernelSmooth.mulArr (KernelSmooth.invArr q.1) q.2) '' (Metric.closedBall d₀ (ε / 2) ×ˢ T) with hT'
  have hT'c : IsCompact T' := by
    refine ((isCompact_closedBall d₀ (ε / 2)).prod hT).image_of_continuousOn ?_
    have hf : ContinuousOn (fun q : (Fin 3 → Fin 3 → ℝ) × (Fin 3 → Fin 3 → ℝ) => (KernelSmooth.invArr q.1, q.2))
        (Metric.closedBall d₀ (ε / 2) ×ˢ T) :=
      ((KernelSmooth.continuousOn_invArr.mono hB).comp continuousOn_fst fun q hq => hq.1).prodMk continuousOn_snd
    exact KernelSmooth.continuous_mulArr.comp_continuousOn hf
  have hT'U : T' ⊆ {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} := by
    rintro _ ⟨⟨d, m⟩, ⟨hd, hm⟩, rfl⟩
    exact KernelSmooth.det_mulArr_ne_zero (KernelSmooth.det_invArr_ne_zero (hB hd)) (hTU hm)
  obtain ⟨C, hC, hmemC⟩ := hcar T' hT'c hT'U
  refine ⟨ε / 2, half_pos hε, hB, C, hC, fun d hd y v hv hvT => ?_⟩
  have hy : y ∈ L := by
    by_contra h
    exact left_ne_zero_of_mul hv (hGL y h)
  refine hmemC y hy ⟨(d, KernelSmooth.mulArr d (archEntries y)), ⟨hd, hvT (right_ne_zero_of_mul hv)⟩, ?_⟩
  exact KernelSmooth.invArr_mulArr_mulArr (hB hd) _

private theorem KernelSmooth.integrable_mul_kernel {β : (Fin 3 → Fin 3 → ℝ) → ℂ} (hβ : Continuous β)
    (hβb : ∃ M : ℝ, ∀ m, ‖β m‖ ≤ M) {G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    {C : Set (AdelicGL 3 (𝓞 ℚ) ℚ)}
    (hGint : Integrable (C.indicator G) (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
    (d : Fin 3 → Fin 3 → ℝ)
    (hmem : ∀ y : AdelicGL 3 (𝓞 ℚ) ℚ, G y * β (KernelSmooth.mulArr d (archEntries y)) ≠ 0 → y ∈ C) :
    Integrable (fun y => G y * β (KernelSmooth.mulArr d (archEntries y)))
      (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := by
  haveI : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  obtain ⟨M, hM⟩ := hβb
  have hm : AEStronglyMeasurable (fun y : AdelicGL 3 (𝓞 ℚ) ℚ => β (KernelSmooth.mulArr d (archEntries y)))
      (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) :=
    (hβ.comp ((KernelSmooth.continuous_mulArr_right d).comp continuous_archEntries)).aestronglyMeasurable
  refine (hGint.bdd_mul hm (Filter.Eventually.of_forall fun y => hM _)).congr
    (Filter.Eventually.of_forall fun y => ?_)
  show β (KernelSmooth.mulArr d (archEntries y)) * C.indicator G y = G y * β (KernelSmooth.mulArr d (archEntries y))
  by_cases hy : y ∈ C
  · rw [Set.indicator_of_mem hy, mul_comm]
  · rw [Set.indicator_of_notMem hy, mul_zero]
    by_contra h
    exact hy (hmem y (Ne.symm h))

private theorem KernelSmooth.continuousOn_Psi {L : Set (AdelicGL 3 (𝓞 ℚ) ℚ)}
    (hcar : ∀ T : Set (Fin 3 → Fin 3 → ℝ), IsCompact T → T ⊆ {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} →
      ∃ C : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact C ∧ ∀ y : AdelicGL 3 (𝓞 ℚ) ℚ, y ∈ L → archEntries y ∈ T → y ∈ C)
    {G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hGm : AEStronglyMeasurable G (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
    (hGint : ∀ C : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact C →
      Integrable (C.indicator G) (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
    (hGL : ∀ y, y ∉ L → G y = 0) {β : (Fin 3 → Fin 3 → ℝ) → ℂ} (hβ : ContDiff ℝ (⊤ : ℕ∞) β)
    (hβc : HasCompactSupport β) (hβU : tsupport β ⊆ {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0}) :
    ContinuousOn (KernelSmooth.Psi β G) {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} := by
  haveI : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  intro d₀ hd₀
  apply ContinuousAt.continuousWithinAt
  obtain ⟨r, hr, hB, C, hC, hmemC⟩ := KernelSmooth.exists_ball_carrier hcar hGL hβc hβU hd₀
  obtain ⟨M, hM⟩ := hβ.continuous.bounded_above_of_compact_support hβc
  have hmem : ∀ d ∈ Metric.closedBall d₀ r, ∀ y : AdelicGL 3 (𝓞 ℚ) ℚ,
      G y * β (KernelSmooth.mulArr d (archEntries y)) ≠ 0 → y ∈ C :=
    fun d hd y hy => hmemC d hd y _ hy fun hv => subset_tsupport β hv
  unfold KernelSmooth.Psi
  refine continuousAt_of_dominated (bound := fun y => M * ‖C.indicator G y‖) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun d => hGm.mul
      (hβ.continuous.comp ((KernelSmooth.continuous_mulArr_right d).comp continuous_archEntries)).aestronglyMeasurable
  · refine Filter.eventually_of_mem (Metric.closedBall_mem_nhds d₀ hr) fun d hd =>
      Filter.Eventually.of_forall fun y => ?_
    show ‖G y * β (KernelSmooth.mulArr d (archEntries y))‖ ≤ M * ‖C.indicator G y‖
    by_cases hz : G y * β (KernelSmooth.mulArr d (archEntries y)) = 0
    · rw [hz, norm_zero]
      exact mul_nonneg ((norm_nonneg _).trans (hM 0)) (norm_nonneg _)
    · rw [norm_mul, Set.indicator_of_mem (hmem d hd y hz), mul_comm]
      exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
  · exact (hGint C hC).norm.const_mul M
  · refine Filter.Eventually.of_forall fun y => ?_
    exact continuousAt_const.mul
      ((hβ.continuous.comp (KernelSmooth.mulRightL (archEntries y)).continuous).continuousAt)

private def KernelSmooth.entryL (a c : Fin 3) : (Fin 3 → Fin 3 → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap { toFun := fun h => h a c, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

private theorem KernelSmooth.entryL_apply (a c : Fin 3) (h : Fin 3 → Fin 3 → ℝ) : KernelSmooth.entryL a c h = h a c :=
  rfl

private def KernelSmooth.dPsi (β : (Fin 3 → Fin 3 → ℝ) → ℂ) (G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (d : Fin 3 → Fin 3 → ℝ) :
    (Fin 3 → Fin 3 → ℝ) →L[ℝ] ℂ :=
  ∑ a, ∑ b, ∑ c, KernelSmooth.invArr d c b •
    (KernelSmooth.entryL a c).smulRight (KernelSmooth.Psi (KernelSmooth.dKer β a b) G d)

private theorem KernelSmooth.dPsi_apply (β : (Fin 3 → Fin 3 → ℝ) → ℂ) (G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (d h : Fin 3 → Fin 3 → ℝ) :
    KernelSmooth.dPsi β G d h =
      ∑ a, ∑ b, ((KernelSmooth.mulArr h (KernelSmooth.invArr d) a b : ℝ) : ℂ) *
        KernelSmooth.Psi (KernelSmooth.dKer β a b) G d := by
  simp only [KernelSmooth.dPsi, ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, ContinuousLinearMap.smulRight_apply, KernelSmooth.entryL_apply, Complex.real_smul]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  show ∑ c, ((KernelSmooth.invArr d c b : ℝ) : ℂ) *
      (((h a c : ℝ) : ℂ) * KernelSmooth.Psi (KernelSmooth.dKer β a b) G d) =
    ((∑ c, h a c * KernelSmooth.invArr d c b : ℝ) : ℂ) * KernelSmooth.Psi (KernelSmooth.dKer β a b) G d
  rw [Complex.ofReal_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Complex.ofReal_mul]
  ring

private theorem KernelSmooth.contDiffOn_dPsi {β : (Fin 3 → Fin 3 → ℝ) → ℂ} {G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} {n : ℕ}
    (h : ∀ a b, ContDiffOn ℝ n (KernelSmooth.Psi (KernelSmooth.dKer β a b) G)
      {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0}) :
    ContDiffOn ℝ n (KernelSmooth.dPsi β G) {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} := by
  have hfun : KernelSmooth.dPsi β G = fun d => ∑ a, ∑ b, ∑ c, KernelSmooth.invArr d c b •
      (KernelSmooth.entryL a c).smulRight (KernelSmooth.Psi (KernelSmooth.dKer β a b) G d) := rfl
  rw [hfun]
  refine ContDiffOn.sum fun a _ => ?_
  refine ContDiffOn.sum fun b _ => ?_
  refine ContDiffOn.sum fun c _ => ?_
  have hinv : ContDiffOn ℝ n (fun d => KernelSmooth.invArr d c b) {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} :=
    (contDiffOn_pi.1 (contDiffOn_pi.1 KernelSmooth.contDiffOn_invArr c) b).of_le (mod_cast le_top)
  exact hinv.smul (contDiffOn_const.smulRight (h a b))

private def KernelSmooth.dInt (β : (Fin 3 → Fin 3 → ℝ) → ℂ) (G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (x : Fin 3 → Fin 3 → ℝ)
    (y : AdelicGL 3 (𝓞 ℚ) ℚ) : (Fin 3 → Fin 3 → ℝ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.mul ℝ ℂ (G y)).comp
    ((fderiv ℝ β (KernelSmooth.mulArr x (archEntries y))).comp (KernelSmooth.mulRightL (archEntries y)))

private theorem KernelSmooth.dInt_apply (β : (Fin 3 → Fin 3 → ℝ) → ℂ) (G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (x : Fin 3 → Fin 3 → ℝ) (y : AdelicGL 3 (𝓞 ℚ) ℚ) (h : Fin 3 → Fin 3 → ℝ) :
    KernelSmooth.dInt β G x y h =
      G y * (fderiv ℝ β (KernelSmooth.mulArr x (archEntries y))) (KernelSmooth.mulArr h (archEntries y)) := by
  simp only [KernelSmooth.dInt, ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply',
    KernelSmooth.mulRightL_apply]

private theorem KernelSmooth.hasFDerivAt_integrand {β : (Fin 3 → Fin 3 → ℝ) → ℂ} (hβ : ContDiff ℝ (⊤ : ℕ∞) β)
    (G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (y : AdelicGL 3 (𝓞 ℚ) ℚ) (x : Fin 3 → Fin 3 → ℝ) :
    HasFDerivAt (fun x => G y * β (KernelSmooth.mulArr x (archEntries y))) (KernelSmooth.dInt β G x y) x := by
  have h1 : HasFDerivAt (fun x => β (KernelSmooth.mulArr x (archEntries y)))
      ((fderiv ℝ β (KernelSmooth.mulArr x (archEntries y))).comp (KernelSmooth.mulRightL (archEntries y))) x :=
    ((hβ.differentiable (by simp)) _).hasFDerivAt.comp x (KernelSmooth.mulRightL (archEntries y)).hasFDerivAt
  exact (ContinuousLinearMap.mul ℝ ℂ (G y)).hasFDerivAt.comp x h1

private theorem KernelSmooth.norm_dInt_le (β : (Fin 3 → Fin 3 → ℝ) → ℂ) (G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (x : Fin 3 → Fin 3 → ℝ) (y : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ‖KernelSmooth.dInt β G x y‖ ≤
      ‖G y‖ * (‖fderiv ℝ β (KernelSmooth.mulArr x (archEntries y))‖ * (3 * ‖archEntries y‖)) := by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  refine mul_le_mul (ContinuousLinearMap.opNorm_mul_apply_le ℝ ℂ (G y)) ?_ (norm_nonneg _) (norm_nonneg _)
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_left (KernelSmooth.norm_mulRightL_le _) (norm_nonneg _))

private theorem KernelSmooth.aestronglyMeasurable_dInt {β : (Fin 3 → Fin 3 → ℝ) → ℂ} (hβ : ContDiff ℝ (⊤ : ℕ∞) β)
    {G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hGm : AEStronglyMeasurable G (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
    (x : Fin 3 → Fin 3 → ℝ) :
    AEStronglyMeasurable (fun y => KernelSmooth.dInt β G x y)
      (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := by
  haveI : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  have hV : Continuous fun y : AdelicGL 3 (𝓞 ℚ) ℚ =>
      (fderiv ℝ β (KernelSmooth.mulArr x (archEntries y))).comp (KernelSmooth.mulRightL (archEntries y)) :=
    ((hβ.continuous_fderiv (by simp)).comp ((KernelSmooth.continuous_mulArr_right x).comp
      continuous_archEntries)).clm_comp (KernelSmooth.continuous_mulRightL.comp continuous_archEntries)
  have hP : AEStronglyMeasurable (fun y : AdelicGL 3 (𝓞 ℚ) ℚ => ContinuousLinearMap.mul ℝ ℂ (G y))
      (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) :=
    (ContinuousLinearMap.mul ℝ ℂ).continuous.comp_aestronglyMeasurable hGm
  have hc : Continuous fun p : (ℂ →L[ℝ] ℂ) × ((Fin 3 → Fin 3 → ℝ) →L[ℝ] ℂ) => p.1.comp p.2 :=
    isBoundedBilinearMap_comp.continuous
  exact hc.comp_aestronglyMeasurable (hP.prodMk hV.aestronglyMeasurable)

private theorem KernelSmooth.hasFDerivAt_Psi_integral {L : Set (AdelicGL 3 (𝓞 ℚ) ℚ)}
    (hcar : ∀ T : Set (Fin 3 → Fin 3 → ℝ), IsCompact T → T ⊆ {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} →
      ∃ C : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact C ∧ ∀ y : AdelicGL 3 (𝓞 ℚ) ℚ, y ∈ L → archEntries y ∈ T → y ∈ C)
    {G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hGm : AEStronglyMeasurable G (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
    (hGint : ∀ C : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact C →
      Integrable (C.indicator G) (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
    (hGL : ∀ y, y ∉ L → G y = 0) {β : (Fin 3 → Fin 3 → ℝ) → ℂ} (hβ : ContDiff ℝ (⊤ : ℕ∞) β)
    (hβc : HasCompactSupport β) (hβU : tsupport β ⊆ {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0})
    {d₀ : Fin 3 → Fin 3 → ℝ} (hd₀ : (Matrix.of d₀).det ≠ 0) :
    HasFDerivAt (KernelSmooth.Psi β G)
        (∫ y, KernelSmooth.dInt β G d₀ y ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)) d₀ ∧
      Integrable (fun y => KernelSmooth.dInt β G d₀ y) (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) ∧
      ∃ C : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact C ∧ ∀ y : AdelicGL 3 (𝓞 ℚ) ℚ, G y ≠ 0 →
        fderiv ℝ β (KernelSmooth.mulArr d₀ (archEntries y)) ≠ 0 → y ∈ C := by
  haveI : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  obtain ⟨r, hr, hB, C, hC, hmemC⟩ := KernelSmooth.exists_ball_carrier hcar hGL hβc hβU hd₀
  obtain ⟨M, hM⟩ := hβ.continuous.bounded_above_of_compact_support hβc
  obtain ⟨B, hBβ⟩ := (hβ.continuous_fderiv (by simp)).bounded_above_of_compact_support (hβc.fderiv ℝ)
  obtain ⟨R₀, hR₀⟩ := hC.exists_bound_of_continuousOn (f := fun y : AdelicGL 3 (𝓞 ℚ) ℚ => archEntries y)
    continuous_archEntries.continuousOn
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hBβ 0)
  have hmem : ∀ d ∈ Metric.closedBall d₀ r, ∀ y : AdelicGL 3 (𝓞 ℚ) ℚ,
      G y * β (KernelSmooth.mulArr d (archEntries y)) ≠ 0 → y ∈ C :=
    fun d hd y hy => hmemC d hd y _ hy fun hv => subset_tsupport β hv
  have hmem' : ∀ d ∈ Metric.closedBall d₀ r, ∀ y : AdelicGL 3 (𝓞 ℚ) ℚ, G y ≠ 0 →
      fderiv ℝ β (KernelSmooth.mulArr d (archEntries y)) ≠ 0 → y ∈ C := by
    intro d hd y hG hD
    refine hmemC d hd y (1 : ℂ) (by rwa [mul_one]) fun _ => ?_
    exact support_fderiv_subset ℝ (Function.mem_support.2 hD)
  have h_bound : ∀ᵐ y ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ), ∀ d ∈ Metric.closedBall d₀ r,
      ‖KernelSmooth.dInt β G d y‖ ≤ B * (3 * max R₀ 0) * ‖C.indicator G y‖ := by
    refine Filter.Eventually.of_forall fun y d hd => (KernelSmooth.norm_dInt_le β G d y).trans ?_
    by_cases hG : G y = 0
    · rw [hG, norm_zero, zero_mul]
      positivity
    by_cases hD : fderiv ℝ β (KernelSmooth.mulArr d (archEntries y)) = 0
    · rw [hD, norm_zero, zero_mul, mul_zero]
      positivity
    have hyC : y ∈ C := hmem' d hd y hG hD
    rw [Set.indicator_of_mem hyC, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    refine mul_le_mul (hBβ _) ?_ (by positivity) hB0
    exact mul_le_mul_of_nonneg_left ((hR₀ y hyC).trans (le_max_left _ _)) (by norm_num)
  have hmain := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun x y => G y * β (KernelSmooth.mulArr x (archEntries y))) (F' := KernelSmooth.dInt β G)
    (Metric.closedBall_mem_nhds d₀ hr)
    (Filter.Eventually.of_forall fun d => hGm.mul
      (hβ.continuous.comp ((KernelSmooth.continuous_mulArr_right d).comp continuous_archEntries)).aestronglyMeasurable)
    (KernelSmooth.integrable_mul_kernel hβ.continuous ⟨M, hM⟩ (hGint C hC) d₀
      (hmem d₀ (Metric.mem_closedBall_self hr.le)))
    (KernelSmooth.aestronglyMeasurable_dInt hβ hGm d₀) h_bound ((hGint C hC).norm.const_mul _)
    (Filter.Eventually.of_forall fun y d _ => KernelSmooth.hasFDerivAt_integrand hβ G y d)
  refine ⟨hmain, ?_, C, hC, fun y hG hD => hmem' d₀ (Metric.mem_closedBall_self hr.le) y hG hD⟩
  exact ((hGint C hC).norm.const_mul _).mono' (KernelSmooth.aestronglyMeasurable_dInt hβ hGm d₀)
    (h_bound.mono fun y hy => hy d₀ (Metric.mem_closedBall_self hr.le))

private theorem KernelSmooth.integrable_mul_dKer {β : (Fin 3 → Fin 3 → ℝ) → ℂ} (hβ : ContDiff ℝ (⊤ : ℕ∞) β)
    (hβc : HasCompactSupport β) {G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} {C : Set (AdelicGL 3 (𝓞 ℚ) ℚ)}
    (hGint : Integrable (C.indicator G) (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
    (d₀ : Fin 3 → Fin 3 → ℝ) (hmem' : ∀ y : AdelicGL 3 (𝓞 ℚ) ℚ, G y ≠ 0 →
      fderiv ℝ β (KernelSmooth.mulArr d₀ (archEntries y)) ≠ 0 → y ∈ C) (a b : Fin 3) :
    Integrable (fun y => G y * KernelSmooth.dKer β a b (KernelSmooth.mulArr d₀ (archEntries y)))
      (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := by
  refine KernelSmooth.integrable_mul_kernel (KernelSmooth.contDiff_dKer hβ a b).continuous
    ((KernelSmooth.contDiff_dKer hβ a b).continuous.bounded_above_of_compact_support
      (KernelSmooth.hasCompactSupport_dKer hβc a b)) hGint d₀ fun y hy => ?_
  refine hmem' y (left_ne_zero_of_mul hy) fun hD => ?_
  exact right_ne_zero_of_mul hy (by simp only [KernelSmooth.dKer, hD, ContinuousLinearMap.zero_apply])

private theorem KernelSmooth.hasFDerivAt_Psi {L : Set (AdelicGL 3 (𝓞 ℚ) ℚ)}
    (hcar : ∀ T : Set (Fin 3 → Fin 3 → ℝ), IsCompact T → T ⊆ {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} →
      ∃ C : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact C ∧ ∀ y : AdelicGL 3 (𝓞 ℚ) ℚ, y ∈ L → archEntries y ∈ T → y ∈ C)
    {G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hGm : AEStronglyMeasurable G (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
    (hGint : ∀ C : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact C →
      Integrable (C.indicator G) (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
    (hGL : ∀ y, y ∉ L → G y = 0) {β : (Fin 3 → Fin 3 → ℝ) → ℂ} (hβ : ContDiff ℝ (⊤ : ℕ∞) β)
    (hβc : HasCompactSupport β) (hβU : tsupport β ⊆ {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0})
    {d₀ : Fin 3 → Fin 3 → ℝ} (hd₀ : (Matrix.of d₀).det ≠ 0) :
    HasFDerivAt (KernelSmooth.Psi β G) (KernelSmooth.dPsi β G d₀) d₀ := by
  obtain ⟨hmain, hF'_int, C, hC, hmem'⟩ := KernelSmooth.hasFDerivAt_Psi_integral hcar hGm hGint hGL hβ hβc hβU hd₀
  have hker_int := KernelSmooth.integrable_mul_dKer hβ hβc (hGint C hC) d₀ hmem'
  refine hmain.congr_fderiv (ContinuousLinearMap.ext fun h => ?_)
  rw [ContinuousLinearMap.integral_apply hF'_int, KernelSmooth.dPsi_apply]
  simp only [KernelSmooth.dInt_apply, KernelSmooth.fderiv_apply_mulArr β hd₀, Finset.mul_sum]
  have hterm : ∀ a b, Integrable (fun y => G y * (((KernelSmooth.mulArr h (KernelSmooth.invArr d₀) a b : ℝ) : ℂ) *
      KernelSmooth.dKer β a b (KernelSmooth.mulArr d₀ (archEntries y))))
        (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := fun a b =>
    ((hker_int a b).const_mul (((KernelSmooth.mulArr h (KernelSmooth.invArr d₀) a b : ℝ) : ℂ))).congr
      (Filter.Eventually.of_forall fun y => mul_left_comm _ _ _)
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hterm a b]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ fun b _ => hterm a b]
  refine Finset.sum_congr rfl fun b _ => ?_
  unfold KernelSmooth.Psi
  rw [← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => mul_left_comm _ _ _)

private theorem KernelSmooth.contDiffOn_Psi_nat {L : Set (AdelicGL 3 (𝓞 ℚ) ℚ)}
    (hcar : ∀ T : Set (Fin 3 → Fin 3 → ℝ), IsCompact T → T ⊆ {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} →
      ∃ C : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact C ∧ ∀ y : AdelicGL 3 (𝓞 ℚ) ℚ, y ∈ L → archEntries y ∈ T → y ∈ C)
    {G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hGm : AEStronglyMeasurable G (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
    (hGint : ∀ C : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact C →
      Integrable (C.indicator G) (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
    (hGL : ∀ y, y ∉ L → G y = 0) (n : ℕ) :
    ∀ β : (Fin 3 → Fin 3 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) β → HasCompactSupport β →
      tsupport β ⊆ {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} →
        ContDiffOn ℝ n (KernelSmooth.Psi β G) {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} := by
  induction n with
  | zero =>
      intro β hβ hβc hβU
      rw [Nat.cast_zero, contDiffOn_zero]
      exact KernelSmooth.continuousOn_Psi hcar hGm hGint hGL hβ hβc hβU
  | succ n ih =>
      intro β hβ hβc hβU
      have hderiv : ∀ d ∈ {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0},
          HasFDerivAt (KernelSmooth.Psi β G) (KernelSmooth.dPsi β G d) d :=
        fun d hd => KernelSmooth.hasFDerivAt_Psi hcar hGm hGint hGL hβ hβc hβU hd
      rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen KernelSmooth.isOpen_det_ne_zero]
      refine ⟨fun d hd => (hderiv d hd).differentiableAt.differentiableWithinAt, fun h => absurd h (by simp), ?_⟩
      have hd' : ContDiffOn ℝ n (KernelSmooth.dPsi β G) {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} :=
        KernelSmooth.contDiffOn_dPsi fun a b => ih (KernelSmooth.dKer β a b) (KernelSmooth.contDiff_dKer hβ a b)
          (KernelSmooth.hasCompactSupport_dKer hβc a b) ((KernelSmooth.tsupport_dKer_subset a b).trans hβU)
      exact hd'.congr fun d hd => (hderiv d hd).fderiv

private theorem KernelSmooth.contDiffOn_Psi {L : Set (AdelicGL 3 (𝓞 ℚ) ℚ)}
    (hcar : ∀ T : Set (Fin 3 → Fin 3 → ℝ), IsCompact T → T ⊆ {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} →
      ∃ C : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact C ∧ ∀ y : AdelicGL 3 (𝓞 ℚ) ℚ, y ∈ L → archEntries y ∈ T → y ∈ C)
    {G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hGm : AEStronglyMeasurable G (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
    (hGint : ∀ C : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact C →
      Integrable (C.indicator G) (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
    (hGL : ∀ y, y ∉ L → G y = 0) {β : (Fin 3 → Fin 3 → ℝ) → ℂ} (hβ : ContDiff ℝ (⊤ : ℕ∞) β)
    (hβc : HasCompactSupport β) (hβU : tsupport β ⊆ {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0}) :
    ContDiffOn ℝ (⊤ : ℕ∞) (KernelSmooth.Psi β G) {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} :=
  contDiffOn_infty.2 fun n => KernelSmooth.contDiffOn_Psi_nat hcar hGm hGint hGL n β hβ hβc hβU

private theorem KernelSmooth.isArchSmooth3_smoothingOperator {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hφ : IsSmoothingKernel φ)
    {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hF : LocallyIntegrable F (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)) :
    WhittakerBlock.IsArchSmooth3 (smoothingOperator φ F) := by
  haveI : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
  obtain ⟨α, K', hα, hoc, hcof, hφeq⟩ := hφ
  obtain ⟨hLo, hLc, hcar⟩ := KernelSmooth.box_clopen_and_carrier hoc hcof
  intro g

  set G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ := fun y =>
    Set.indicator {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p} (fun _ => (1 : ℂ)) y * F (g * y)
    with hG
  have hFg : AEStronglyMeasurable (fun y => F (g * y)) (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) :=
    (measurePreserving_mul_left (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) g).aestronglyMeasurable_comp_iff
      (MeasurableEquiv.mulLeft g).measurableEmbedding |>.2 hF.aestronglyMeasurable
  have hGm : AEStronglyMeasurable G (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) :=
    (aestronglyMeasurable_const.indicator hLc.measurableSet).mul hFg
  have hGint : ∀ C : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact C →
      Integrable (C.indicator G) (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := by
    intro C hC
    have h1 := SmoothingDeriv.integrable_indicator_comp_mul hF g hC
    refine (h1.bdd_mul (c := 1) (aestronglyMeasurable_const.indicator hLc.measurableSet)
      (Filter.Eventually.of_forall fun y => SmoothingDeriv.norm_indicator_one_le _ y)).congr
      (Filter.Eventually.of_forall fun y => ?_)
    show Set.indicator {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p} (fun _ => (1 : ℂ)) y *
      C.indicator (fun y => F (g * y)) y = C.indicator G y
    by_cases hy : y ∈ C
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero]
  have hGL : ∀ y, y ∉ {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p} → G y = 0 := fun y hy => by
    simp only [hG, Set.indicator_of_notMem hy, zero_mul]
  have hPsi := KernelSmooth.contDiffOn_Psi hcar hGm hGint hGL hα.1 hα.2.1 hα.2.2

  have hcomp : ContDiffOn ℝ (⊤ : ℕ∞) (fun e => KernelSmooth.Psi α G (KernelSmooth.invArr e))
      {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} :=
    hPsi.comp KernelSmooth.contDiffOn_invArr fun e he => KernelSmooth.det_invArr_ne_zero he
  refine hcomp.congr fun e he => ?_
  rw [KernelSmooth.smoothingOperator_mul_lift φ F g he]
  unfold KernelSmooth.Psi
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show φ (WhittakerBlock.archRealLift3 (KernelSmooth.invArr e) * y) * F (g * y) =
    G y * α (KernelSmooth.mulArr (KernelSmooth.invArr e) (archEntries y))
  rw [KernelSmooth.apply_lift_mul hφeq (KernelSmooth.det_invArr_ne_zero he) y, hG]
  ring

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_continuous_and_isArchSmooth3_smoothingOperator.SmoothingTranslation.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_continuous_and_isArchSmooth3_smoothingOperator.SmoothingTranslation.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_continuous_and_isArchSmooth3_smoothingOperator.SmoothingTranslation"

open LanglandsTunnell LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2 in
attribute [local instance] NumberField.AdelicHaar.glBorel in

theorem solution
    (φ F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hφ : IsSmoothingKernel φ)
    (hF : LocallyIntegrable F (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)) :
    Continuous (smoothingOperator φ F) ∧ WhittakerBlock.IsArchSmooth3 (smoothingOperator φ F) := by
  exact ⟨KernelSmooth.continuous_smoothingOperator hφ hF, KernelSmooth.isArchSmooth3_smoothingOperator hφ hF⟩

end S_LanglandsTunnell_CubicInduction_SlabL2_continuous_and_isArchSmooth3_smoothingOperator
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_continuous_and_isArchSmooth3_smoothingOperator (solution)
