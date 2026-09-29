-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.SlabL2.casimir_smoothingOperator
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/8d66cbc6-adf5-584e-87c6-b01f51478a93

import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchSmoothSpace3
import Theorems.Thm_LanglandsTunnell_CubicInduction_isOpen_and_isCompact_setOf_forall_componentAt3_finEmbedN_mem
import Theorems.Thm_LanglandsTunnell_CubicInduction_WhittakerBlock_casimir_translateRight
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Group.Integral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_smoothingOperator

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm
open MeasureTheory

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
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_smoothingOperator.SmoothingTranslation.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_smoothingOperator.SmoothingTranslation.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_smoothingOperator.SmoothingTranslation.LanglandsTunnell"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_smoothingOperator.SmoothingTranslation.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_smoothingOperator.SmoothingTranslation.LanglandsTunnell.CubicInduction"

end Integrability
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_smoothingOperator.SmoothingTranslation.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_smoothingOperator.SmoothingTranslation.LanglandsTunnell.CubicInduction"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_smoothingOperator.SmoothingTranslation.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_smoothingOperator.SmoothingTranslation.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_smoothingOperator.SmoothingTranslation.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_smoothingOperator.SmoothingTranslation.LanglandsTunnell.CubicInduction"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_smoothingOperator.SmoothingTranslation.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_smoothingOperator.SmoothingTranslation.LanglandsTunnell.CubicInduction"

end KernelIntegrability
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_smoothingOperator.SmoothingTranslation.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_smoothingOperator.SmoothingTranslation.LanglandsTunnell.CubicInduction"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_smoothingOperator.SmoothingTranslation.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_smoothingOperator.SmoothingTranslation.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_smoothingOperator.SmoothingTranslation.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_smoothingOperator.SmoothingTranslation.LanglandsTunnell.CubicInduction"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_smoothingOperator.SmoothingTranslation.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_smoothingOperator.SmoothingTranslation.LanglandsTunnell.CubicInduction"

end KernelBounds
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_smoothingOperator.SmoothingTranslation.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_smoothingOperator.SmoothingTranslation.LanglandsTunnell.CubicInduction"

end SmoothingTranslation
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_smoothingOperator.SmoothingTranslation.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_smoothingOperator.SmoothingTranslation.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_smoothingOperator.SmoothingTranslation"

open LanglandsTunnell LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2
open SmoothingTranslation.LanglandsTunnell.CubicInduction

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

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

private def CentreConj.realMatrix (g : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of (archEntries g)

private theorem CentreConj.realMatrix_mul (g h : AdelicGL 3 (𝓞 ℚ) ℚ) :
    CentreConj.realMatrix (g * h) = CentreConj.realMatrix g * CentreConj.realMatrix h := by
  ext a b
  simp only [CentreConj.realMatrix, Matrix.of_apply, Matrix.mul_apply, SmoothingDeriv.archEntries_mul]

private theorem CentreConj.realMatrix_one : CentreConj.realMatrix 1 = 1 := by
  ext a b
  simp only [CentreConj.realMatrix, SmoothingDeriv.archEntries_one, Matrix.of_apply, Matrix.one_apply]

private theorem CentreConj.realMatrix_inv_mul (y : AdelicGL 3 (𝓞 ℚ) ℚ) :
    CentreConj.realMatrix y⁻¹ * CentreConj.realMatrix y = 1 := by
  rw [← CentreConj.realMatrix_mul, inv_mul_cancel, CentreConj.realMatrix_one]

private def CentreConj.conjMat (y : AdelicGL 3 (𝓞 ℚ) ℚ) (X : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  CentreConj.realMatrix y⁻¹ * X * CentreConj.realMatrix y

private theorem CentreConj.conjMat_one (y : AdelicGL 3 (𝓞 ℚ) ℚ) : CentreConj.conjMat y 1 = 1 := by
  rw [CentreConj.conjMat, mul_one, CentreConj.realMatrix_inv_mul]

private theorem CentreConj.conjMat_add_smul (y : AdelicGL 3 (𝓞 ℚ) ℚ) (X V : Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ) :
    CentreConj.conjMat y (X + s • V) = CentreConj.conjMat y X + s • CentreConj.conjMat y V := by
  simp only [CentreConj.conjMat, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]

private theorem CentreConj.det_conjMat (y : AdelicGL 3 (𝓞 ℚ) ℚ) (X : Matrix (Fin 3) (Fin 3) ℝ) :
    (CentreConj.conjMat y X).det = X.det := by
  rw [CentreConj.conjMat, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul,
    CentreConj.realMatrix_inv_mul, Matrix.det_one, one_mul]

private def CentreConj.conjEntries (y : AdelicGL 3 (𝓞 ℚ) ℚ) (e : Fin 3 → Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun a b => CentreConj.conjMat y (Matrix.of e) a b

private theorem CentreConj.of_conjEntries (y : AdelicGL 3 (𝓞 ℚ) ℚ) (e : Fin 3 → Fin 3 → ℝ) :
    Matrix.of (CentreConj.conjEntries y e) = CentreConj.conjMat y (Matrix.of e) :=
  rfl

private theorem CentreConj.det_of_conjEntries (y : AdelicGL 3 (𝓞 ℚ) ℚ) (e : Fin 3 → Fin 3 → ℝ) :
    (Matrix.of (CentreConj.conjEntries y e)).det = (Matrix.of e).det := by
  rw [CentreConj.of_conjEntries, CentreConj.det_conjMat]

private theorem CentreConj.conjEntries_add_smul (y : AdelicGL 3 (𝓞 ℚ) ℚ) (e v : Fin 3 → Fin 3 → ℝ) (s : ℝ) :
    CentreConj.conjEntries y (e + s • v) = CentreConj.conjEntries y e + s • CentreConj.conjEntries y v := by
  have h : CentreConj.conjMat y (Matrix.of (e + s • v)) =
      CentreConj.conjMat y (Matrix.of e) + s • CentreConj.conjMat y (Matrix.of v) :=
    CentreConj.conjMat_add_smul y (Matrix.of e) (Matrix.of v) s
  funext a b
  exact congrArg (fun X : Matrix (Fin 3) (Fin 3) ℝ => X a b) h

private def CentreConj.idArr : Fin 3 → Fin 3 → ℝ := fun a b => if a = b then (1 : ℝ) else 0

namespace CentreConj
private theorem _root_.CentreConj.of_idArr : Matrix.of CentreConj.idArr = 1 := by
  ext a b
  simp only [CentreConj.idArr, Matrix.of_apply, Matrix.one_apply]

end CentreConj
p2m_export "" "CentreConj.of_idArr"
private theorem CentreConj.det_of_idArr : (Matrix.of CentreConj.idArr).det ≠ 0 := by
  rw [CentreConj.of_idArr, Matrix.det_one]
  exact one_ne_zero

private theorem CentreConj.conjEntries_idArr (y : AdelicGL 3 (𝓞 ℚ) ℚ) :
    CentreConj.conjEntries y CentreConj.idArr = CentreConj.idArr := by
  funext a b
  show CentreConj.conjMat y (Matrix.of CentreConj.idArr) a b = CentreConj.idArr a b
  rw [CentreConj.of_idArr, CentreConj.conjMat_one]
  simp only [CentreConj.idArr, Matrix.one_apply]

private theorem CentreConj.matrix_ext_of_map {X Z : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)}
    (h₁ : X.map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ) = Z.map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ))
    (h₂ : X.map (AdelicLevel.adeleFin (𝓞 ℚ) ℚ) = Z.map (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)) : X = Z := by
  ext a b
  exact Prod.ext (congrArg (fun W : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ) => W a b) h₁)
    (congrArg (fun W : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ) => W a b) h₂)

private theorem CentreConj.realAdeleHom_realCoordinate (z : InfiniteAdeleRing ℚ) :
    SmoothingDeriv.realAdeleHom (realCoordinate z) = z :=
  StandardKernel.ofReal_realCoord z

private theorem CentreConj.map_adeleArch_coe (y : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (y : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ) =
      (CentreConj.realMatrix y).map SmoothingDeriv.realAdeleHom := by
  ext a b
  exact (CentreConj.realAdeleHom_realCoordinate _).symm

private theorem CentreConj.map_adeleArch_archRealMat3 (e : Fin 3 → Fin 3 → ℝ) :
    (WhittakerBlock.archRealMat3 e).map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ) =
      (Matrix.of e).map SmoothingDeriv.realAdeleHom := by
  ext a b
  exact adeleArch_archMatrixInclN (Fin 3) ℚ _ a b

private theorem CentreConj.conj_archRealLift3 (y : AdelicGL 3 (𝓞 ℚ) ℚ) {e : Fin 3 → Fin 3 → ℝ}
    (he : (Matrix.of e).det ≠ 0) :
    y⁻¹ * WhittakerBlock.archRealLift3 e * y = WhittakerBlock.archRealLift3 (CentreConj.conjEntries y e) := by
  have he' : (Matrix.of (CentreConj.conjEntries y e)).det ≠ 0 := by
    rw [CentreConj.det_of_conjEntries]
    exact he
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, SmoothingDeriv.coe_archRealLift3 he, SmoothingDeriv.coe_archRealLift3 he']
  refine CentreConj.matrix_ext_of_map ?_ ?_
  · simp only [Matrix.map_mul, CentreConj.map_adeleArch_archRealMat3, CentreConj.map_adeleArch_coe,
      CentreConj.of_conjEntries, CentreConj.conjMat]
  · simp only [Matrix.map_mul, SmoothingDeriv.map_adeleFin_archRealMat3, mul_one]
    rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

private theorem CentreConj.mul_archRealLift3_mul (x y : AdelicGL 3 (𝓞 ℚ) ℚ) {e : Fin 3 → Fin 3 → ℝ}
    (he : (Matrix.of e).det ≠ 0) :
    x * WhittakerBlock.archRealLift3 e * y = x * y * WhittakerBlock.archRealLift3 (CentreConj.conjEntries y e) := by
  rw [← CentreConj.conj_archRealLift3 y he]
  group

private noncomputable def SmoothingDeriv.eArr (i j : Fin 3) (s : ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0

private noncomputable def SmoothingDeriv.eLift (i j : Fin 3) (s : ℝ) : AdelicGL 3 (𝓞 ℚ) ℚ :=
  WhittakerBlock.archRealLift3 (SmoothingDeriv.eArr i j s)

private noncomputable def SmoothingDeriv.sigma (i j : Fin 3) (s : ℝ) : ℝ :=
  -s / (1 + if i = j then s else 0)

private noncomputable def SmoothingDeriv.sigma' (i j : Fin 3) (s : ℝ) : ℝ :=
  -1 / (1 + if i = j then s else 0) ^ 2

private theorem SmoothingDeriv.archDeriv_apply (i j : Fin 3) (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    WhittakerBlock.archDeriv i j f g = deriv (fun s => f (g * SmoothingDeriv.eLift i j s)) 0 :=
  rfl

private def CentreConj.elemArr (i j : Fin 3) : Fin 3 → Fin 3 → ℝ := fun a b => if i = a ∧ j = b then (1 : ℝ) else 0

private theorem CentreConj.of_elemArr (i j : Fin 3) : Matrix.of (CentreConj.elemArr i j) = Matrix.single i j (1 : ℝ) :=
  rfl

private theorem CentreConj.eArr_eq (i j : Fin 3) (s : ℝ) :
    SmoothingDeriv.eArr i j s = CentreConj.idArr + s • CentreConj.elemArr i j := by
  funext a b
  simp only [SmoothingDeriv.eArr, CentreConj.idArr, CentreConj.elemArr, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero, @eq_comm _ a i, @eq_comm _ b j]

private theorem CentreConj.eq_sum_smul_elemArr (v : Fin 3 → Fin 3 → ℝ) :
    v = ∑ a : Fin 3, ∑ b : Fin 3, v a b • CentreConj.elemArr a b := by
  funext c d
  simp [CentreConj.elemArr, Finset.sum_apply, ite_and]

private def CentreConj.invertibleArrays : Set (Fin 3 → Fin 3 → ℝ) := {e | (Matrix.of e).det ≠ 0}

private theorem CentreConj.isOpen_invertibleArrays : IsOpen CentreConj.invertibleArrays :=
  isOpen_ne.preimage (Continuous.matrix_det (continuous_matrix fun a b =>
    (continuous_apply b).comp (continuous_apply a)))

private theorem CentreConj.idArr_mem : CentreConj.idArr ∈ CentreConj.invertibleArrays := by
  show (Matrix.of CentreConj.idArr).det ≠ 0
  rw [CentreConj.of_idArr, Matrix.det_one]
  exact one_ne_zero

private theorem CentreConj.eventually_mem_invertibleArrays (v : Fin 3 → Fin 3 → ℝ) :
    ∀ᶠ s : ℝ in nhds 0, CentreConj.idArr + s • v ∈ CentreConj.invertibleArrays := by
  have hc : Continuous fun s : ℝ => CentreConj.idArr + s • v :=
    continuous_const.add (continuous_id.smul continuous_const)
  have h0 : CentreConj.idArr + (0 : ℝ) • v ∈ CentreConj.invertibleArrays := by
    rw [zero_smul, add_zero]
    exact CentreConj.idArr_mem
  exact hc.continuousAt.eventually_mem (CentreConj.isOpen_invertibleArrays.mem_nhds h0)

private theorem CentreConj.hasDerivAt_line {F : (Fin 3 → Fin 3 → ℝ) → ℂ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F CentreConj.invertibleArrays) (v : Fin 3 → Fin 3 → ℝ) :
    HasDerivAt (fun s : ℝ => F (CentreConj.idArr + s • v)) (fderiv ℝ F CentreConj.idArr v) 0 := by
  have hd : DifferentiableAt ℝ F CentreConj.idArr :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen CentreConj.isOpen_invertibleArrays).1 hF).1.differentiableAt
      (CentreConj.isOpen_invertibleArrays.mem_nhds CentreConj.idArr_mem)
  have hl : HasDerivAt (fun s : ℝ => CentreConj.idArr + s • v) ((1 : ℝ) • v) 0 :=
    ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add CentreConj.idArr
  rw [one_smul] at hl
  exact hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)

private theorem CentreConj.deriv_line {F : (Fin 3 → Fin 3 → ℝ) → ℂ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F CentreConj.invertibleArrays) (v : Fin 3 → Fin 3 → ℝ) :
    deriv (fun s : ℝ => F (CentreConj.idArr + s • v)) 0 = fderiv ℝ F CentreConj.idArr v :=
  (CentreConj.hasDerivAt_line hF v).deriv

private theorem CentreConj.clm_apply_eq_sum (L : (Fin 3 → Fin 3 → ℝ) →L[ℝ] ℂ) (v : Fin 3 → Fin 3 → ℝ) :
    L v = ∑ a : Fin 3, ∑ b : Fin 3, (v a b : ℂ) * L (CentreConj.elemArr a b) := by
  conv_lhs => rw [CentreConj.eq_sum_smul_elemArr v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  exact (L.map_smul (v a b) (CentreConj.elemArr a b)).trans Complex.real_smul

private noncomputable def CentreConj.chartDeriv (H : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (Fin 3 → Fin 3 → ℝ) →L[ℝ] ℂ :=
  fderiv ℝ (fun e => H (g * WhittakerBlock.archRealLift3 e)) CentreConj.idArr

private theorem CentreConj.archDeriv_eq_chartDeriv {H : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hH : WhittakerBlock.IsArchSmooth3 H)
    (i j : Fin 3) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    WhittakerBlock.archDeriv i j H g = CentreConj.chartDeriv H g (CentreConj.elemArr i j) := by
  rw [SmoothingDeriv.archDeriv_apply]
  simp only [SmoothingDeriv.eLift, CentreConj.eArr_eq]
  exact CentreConj.deriv_line (hH g) (CentreConj.elemArr i j)

private theorem CentreConj.chartDeriv_apply {H : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hH : WhittakerBlock.IsArchSmooth3 H)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (v : Fin 3 → Fin 3 → ℝ) :
    CentreConj.chartDeriv H g v = ∑ a : Fin 3, ∑ b : Fin 3, (v a b : ℂ) * WhittakerBlock.archDeriv a b H g := by
  rw [CentreConj.clm_apply_eq_sum]
  simp only [CentreConj.archDeriv_eq_chartDeriv hH]

private theorem CentreConj.archDeriv_translateRight_apply {H : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hH : WhittakerBlock.IsArchSmooth3 H) (y : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3) (x : AdelicGL 3 (𝓞 ℚ) ℚ) :
    WhittakerBlock.archDeriv i j (translateRight y H) x =
      CentreConj.chartDeriv H (x * y) (CentreConj.conjEntries y (CentreConj.elemArr i j)) := by
  rw [SmoothingDeriv.archDeriv_apply]
  have hev : (fun s : ℝ => translateRight y H (x * SmoothingDeriv.eLift i j s)) =ᶠ[nhds 0] fun s : ℝ =>
      H (x * y * WhittakerBlock.archRealLift3
        (CentreConj.idArr + s • CentreConj.conjEntries y (CentreConj.elemArr i j))) := by
    filter_upwards [CentreConj.eventually_mem_invertibleArrays (CentreConj.elemArr i j)] with s hs
    rw [translateRight_apply, SmoothingDeriv.eLift, CentreConj.eArr_eq,
      CentreConj.mul_archRealLift3_mul x y (e := CentreConj.idArr + s • CentreConj.elemArr i j) hs,
      CentreConj.conjEntries_add_smul, CentreConj.conjEntries_idArr]
  rw [hev.deriv_eq]
  exact CentreConj.deriv_line (hH (x * y)) _

private theorem CentreConj.archDeriv_translateRight {H : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hH : WhittakerBlock.IsArchSmooth3 H)
    (y : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3) :
    WhittakerBlock.archDeriv i j (translateRight y H) = translateRight y fun g =>
      ∑ a : Fin 3, ∑ b : Fin 3,
        (CentreConj.conjEntries y (CentreConj.elemArr i j) a b : ℂ) * WhittakerBlock.archDeriv a b H g := by
  funext x
  rw [CentreConj.archDeriv_translateRight_apply hH y i j x, translateRight_apply, CentreConj.chartDeriv_apply hH]

private noncomputable def CentreConj.comb (c : Fin 3 → Fin 3 → ℝ) (φ : WhittakerBlock.smoothFunctions3) :
    WhittakerBlock.smoothFunctions3 :=
  ∑ a : Fin 3, ∑ b : Fin 3, ((c a b : ℝ) : ℂ) • WhittakerBlock.archDerivₗ a b φ

private theorem CentreConj.coe_comb (c : Fin 3 → Fin 3 → ℝ) (φ : WhittakerBlock.smoothFunctions3) :
    ((CentreConj.comb c φ : WhittakerBlock.smoothFunctions3) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) =
      fun g => ∑ a : Fin 3, ∑ b : Fin 3,
        (c a b : ℂ) * WhittakerBlock.archDeriv a b (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) g := by
  funext g
  simp only [CentreConj.comb, Submodule.coe_sum, Submodule.coe_smul, WhittakerBlock.coe_archDerivₗ_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

private theorem CentreConj.archDeriv_translateRight_coe (φ : WhittakerBlock.smoothFunctions3) (y : AdelicGL 3 (𝓞 ℚ) ℚ)
    (i j : Fin 3) :
    WhittakerBlock.archDeriv i j (translateRight y (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) =
      translateRight y
        (CentreConj.comb (CentreConj.conjEntries y (CentreConj.elemArr i j)) φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) := by
  rw [CentreConj.archDeriv_translateRight φ.2 y i j, CentreConj.coe_comb]

private theorem CentreConj.conjEntries_elemArr_apply (y : AdelicGL 3 (𝓞 ℚ) ℚ) (i j c d : Fin 3) :
    CentreConj.conjEntries y (CentreConj.elemArr i j) c d =
      (CentreConj.realMatrix y⁻¹ * Matrix.single i j (1 : ℝ) * CentreConj.realMatrix y) c d :=
  rfl

private theorem SmoothingDeriv.det_eArr (i j : Fin 3) (s : ℝ) :
    (Matrix.of (SmoothingDeriv.eArr i j s)).det = 1 + if i = j then s else 0 := by
  fin_cases i <;> fin_cases j <;> simp [Matrix.det_fin_three, SmoothingDeriv.eArr]

private theorem SmoothingDeriv.det_eArr_ne_zero {i j : Fin 3} {s : ℝ} (hs : 1 + (if i = j then s else 0) ≠ 0) :
    (Matrix.of (SmoothingDeriv.eArr i j s)).det ≠ 0 := by
  rw [SmoothingDeriv.det_eArr]
  exact hs

private theorem SmoothingDeriv.sigma_zero (i j : Fin 3) : SmoothingDeriv.sigma i j 0 = 0 := by
  simp [SmoothingDeriv.sigma]

private theorem SmoothingDeriv.sigma'_zero (i j : Fin 3) : SmoothingDeriv.sigma' i j 0 = -1 := by
  simp [SmoothingDeriv.sigma']

private theorem SmoothingDeriv.one_add_sigma {i j : Fin 3} {s : ℝ} (hs : 1 + (if i = j then s else 0) ≠ 0) :
    (1 + if i = j then SmoothingDeriv.sigma i j s else 0) = 1 / (1 + if i = j then s else 0) := by
  unfold SmoothingDeriv.sigma
  by_cases hij : i = j
  · simp only [hij, if_true] at hs ⊢
    field_simp
    ring1
  · simp [hij]

private theorem SmoothingDeriv.det_eArr_sigma_ne_zero {i j : Fin 3} {s : ℝ} (hs : 1 + (if i = j then s else 0) ≠ 0) :
    (Matrix.of (SmoothingDeriv.eArr i j (SmoothingDeriv.sigma i j s))).det ≠ 0 := by
  rw [SmoothingDeriv.det_eArr, SmoothingDeriv.one_add_sigma hs]
  exact one_div_ne_zero hs

private theorem SmoothingDeriv.of_eArr_sigma_mul {i j : Fin 3} {s : ℝ} (hs : 1 + (if i = j then s else 0) ≠ 0) :
    Matrix.of (SmoothingDeriv.eArr i j (SmoothingDeriv.sigma i j s)) * Matrix.of (SmoothingDeriv.eArr i j s) = 1 := by
  unfold SmoothingDeriv.sigma
  fin_cases i <;> fin_cases j <;> simp only [if_true] at hs ⊢ <;>
    ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [SmoothingDeriv.eArr, Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp <;> ring1

private theorem SmoothingDeriv.hasDerivAt_sigma (i j : Fin 3) {s : ℝ} (hs : 1 + (if i = j then s else 0) ≠ 0) :
    HasDerivAt (SmoothingDeriv.sigma i j) (SmoothingDeriv.sigma' i j s) s := by
  unfold SmoothingDeriv.sigma SmoothingDeriv.sigma'
  by_cases hij : i = j
  · simp only [hij, if_true] at hs ⊢
    have h := ((hasDerivAt_id s).neg).div ((hasDerivAt_id s).const_add 1) hs
    convert h using 1 <;> try rfl
    try simp only [id, Pi.neg_apply]
    field_simp
    ring1
  · simp only [hij, if_false, add_zero, div_one, one_pow]
    exact (hasDerivAt_id s).neg

private theorem SmoothingDeriv.abs_sigma_le {i j : Fin 3} {s : ℝ} (hs : |s| ≤ 1 / 2) :
    |SmoothingDeriv.sigma i j s| ≤ 1 := by
  have h1 := (abs_le.1 hs).1
  have h2 := (abs_le.1 hs).2
  unfold SmoothingDeriv.sigma
  by_cases hij : i = j
  · have hpos : 0 < 1 + s := by linarith
    simp only [hij, if_true]
    rw [abs_div, abs_neg, abs_of_pos hpos, div_le_one hpos]
    linarith [le_abs_self s]
  · simp only [hij, if_false, add_zero, div_one, abs_neg]
    linarith

private theorem SmoothingDeriv.abs_sigma'_le {i j : Fin 3} {s : ℝ} (hs : |s| ≤ 1 / 2) :
    |SmoothingDeriv.sigma' i j s| ≤ 4 := by
  have h1 := (abs_le.1 hs).1
  unfold SmoothingDeriv.sigma'
  by_cases hij : i = j
  · have hpos : (0 : ℝ) < 1 + s := by linarith
    simp only [hij, if_true]
    rw [abs_div, abs_neg, abs_one, abs_of_pos (by positivity), div_le_iff₀ (by positivity)]
    nlinarith
  · simp only [hij, if_false, add_zero, one_pow, div_one, abs_neg, abs_one]
    norm_num

private def SmoothingDeriv.direction (i j : Fin 3) (m : Fin 3 → Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun a b => if a = i then m j b else 0

private theorem SmoothingDeriv.eArr_mul_eq (i j : Fin 3) (t : ℝ) (m : Fin 3 → Fin 3 → ℝ) :
    (fun a b => ∑ c, SmoothingDeriv.eArr i j t a c * m c b) = m + t • SmoothingDeriv.direction i j m := by
  funext a b
  fin_cases i <;> fin_cases j <;> fin_cases a <;>
    simp [SmoothingDeriv.eArr, SmoothingDeriv.direction, Fin.sum_univ_three] <;> ring1

private theorem SmoothingDeriv.contDiff_direction (i j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (SmoothingDeriv.direction i j) := by
  refine contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_
  by_cases h : a = i
  · simp only [SmoothingDeriv.direction, if_pos h]
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) b).contDiff.comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => Fin 3 → ℝ) j).contDiff
  · simp only [SmoothingDeriv.direction, if_neg h]
    exact contDiff_const

private noncomputable def SmoothingDeriv.derivedFactor (i j : Fin 3) (α : (Fin 3 → Fin 3 → ℝ) → ℂ) :
    (Fin 3 → Fin 3 → ℝ) → ℂ :=
  fun m => -(fderiv ℝ α m (SmoothingDeriv.direction i j m))

private theorem SmoothingDeriv.contDiff_derivedFactor (i j : Fin 3) {α : (Fin 3 → Fin 3 → ℝ) → ℂ}
    (hα : ContDiff ℝ (⊤ : ℕ∞) α) : ContDiff ℝ (⊤ : ℕ∞) (SmoothingDeriv.derivedFactor i j α) := by
  have hD : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ α) := (contDiff_infty_iff_fderiv.1 hα).2
  exact (hD.clm_apply (SmoothingDeriv.contDiff_direction i j)).neg

private theorem SmoothingDeriv.support_derivedFactor_subset (i j : Fin 3) (α : (Fin 3 → Fin 3 → ℝ) → ℂ) :
    Function.support (SmoothingDeriv.derivedFactor i j α) ⊆ tsupport α := by
  intro m hm
  apply support_fderiv_subset (𝕜 := ℝ)
  intro h0
  apply hm
  simp [SmoothingDeriv.derivedFactor, h0]

private theorem SmoothingDeriv.tsupport_derivedFactor_subset (i j : Fin 3) (α : (Fin 3 → Fin 3 → ℝ) → ℂ) :
    tsupport (SmoothingDeriv.derivedFactor i j α) ⊆ tsupport α :=
  closure_minimal (SmoothingDeriv.support_derivedFactor_subset i j α) (isClosed_tsupport α)

private theorem SmoothingDeriv.hasCompactSupport_derivedFactor (i j : Fin 3) {α : (Fin 3 → Fin 3 → ℝ) → ℂ}
    (hα : HasCompactSupport α) : HasCompactSupport (SmoothingDeriv.derivedFactor i j α) :=
  hα.mono' (SmoothingDeriv.support_derivedFactor_subset i j α)

private theorem SmoothingDeriv.one_add_sigma_ne_zero {i j : Fin 3} {s : ℝ} (hs : 1 + (if i = j then s else 0) ≠ 0) :
    1 + (if i = j then SmoothingDeriv.sigma i j s else 0) ≠ 0 := by
  rw [SmoothingDeriv.one_add_sigma hs]
  exact one_div_ne_zero hs

private theorem SmoothingDeriv.of_add_smul_direction (i j : Fin 3) (s : ℝ) (m : Fin 3 → Fin 3 → ℝ) :
    Matrix.of (m + s • SmoothingDeriv.direction i j m) = Matrix.of (SmoothingDeriv.eArr i j s) * Matrix.of m := by
  rw [← SmoothingDeriv.eArr_mul_eq]
  ext a b
  simp [Matrix.mul_apply]

private theorem SmoothingDeriv.of_eArr_mul_sigma {i j : Fin 3} {s : ℝ} (hs : 1 + (if i = j then s else 0) ≠ 0) :
    Matrix.of (SmoothingDeriv.eArr i j s) * Matrix.of (SmoothingDeriv.eArr i j (SmoothingDeriv.sigma i j s)) =
      1 := by
  unfold SmoothingDeriv.sigma
  fin_cases i <;> fin_cases j <;> simp only [if_true] at hs ⊢ <;>
    ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [SmoothingDeriv.eArr, Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp <;> ring1

private theorem SmoothingDeriv.flow_sigma_cancel (i j : Fin 3) {s : ℝ} (hs : 1 + (if i = j then s else 0) ≠ 0)
    (m : Fin 3 → Fin 3 → ℝ) :
    (m + SmoothingDeriv.sigma i j s • SmoothingDeriv.direction i j m) +
        s • SmoothingDeriv.direction i j (m + SmoothingDeriv.sigma i j s • SmoothingDeriv.direction i j m) = m := by
  apply Matrix.of.injective
  rw [SmoothingDeriv.of_add_smul_direction, SmoothingDeriv.of_add_smul_direction, ← mul_assoc,
    SmoothingDeriv.of_eArr_mul_sigma hs, one_mul]

private theorem SmoothingDeriv.det_flow (i j : Fin 3) (s : ℝ) (m : Fin 3 → Fin 3 → ℝ) :
    (Matrix.of (m + s • SmoothingDeriv.direction i j m)).det = (1 + if i = j then s else 0) * (Matrix.of m).det := by
  rw [SmoothingDeriv.of_add_smul_direction, Matrix.det_mul, SmoothingDeriv.det_eArr]

namespace SmoothingDeriv
private theorem _root_.SmoothingDeriv.of_idArr : Matrix.of (fun a b : Fin 3 => if a = b then (1 : ℝ) else 0) = 1 := by
  ext a b
  simp [Matrix.one_apply]

end SmoothingDeriv
p2m_export "" "SmoothingDeriv.of_idArr"

private theorem SmoothingDeriv.archRealLift3_idArr :
    WhittakerBlock.archRealLift3 (fun a b => if a = b then (1 : ℝ) else 0) = 1 := by
  have hdet : (Matrix.of fun a b : Fin 3 => if a = b then (1 : ℝ) else 0).det ≠ 0 := by
    rw [SmoothingDeriv.of_idArr, Matrix.det_one]
    exact one_ne_zero
  apply Units.ext
  rw [SmoothingDeriv.coe_archRealLift3 hdet, SmoothingDeriv.archRealMat3_eq, SmoothingDeriv.of_idArr,
    Matrix.map_one _ (map_zero _) (map_one _), AutomorphicForm.archMatrixInclN_one, Units.val_one]

private theorem SmoothingDeriv.eLift_sigma_mul (i j : Fin 3) {s : ℝ} (hs : 1 + (if i = j then s else 0) ≠ 0) :
    SmoothingDeriv.eLift i j (SmoothingDeriv.sigma i j s) * SmoothingDeriv.eLift i j s = 1 := by
  unfold SmoothingDeriv.eLift
  rw [WhittakerBlock.archRealLift3_mul (SmoothingDeriv.det_eArr_sigma_ne_zero hs) (SmoothingDeriv.det_eArr_ne_zero hs),
    ← SmoothingDeriv.archRealLift3_idArr]
  congr 1
  funext a b
  rw [SmoothingDeriv.of_eArr_sigma_mul hs, Matrix.one_apply]

private theorem SmoothingDeriv.isSmoothArchFactor_derivedFactor (i j : Fin 3) {α : (Fin 3 → Fin 3 → ℝ) → ℂ}
    (hα : IsSmoothArchFactor α) : IsSmoothArchFactor (SmoothingDeriv.derivedFactor i j α) :=
  ⟨SmoothingDeriv.contDiff_derivedFactor i j hα.1, SmoothingDeriv.hasCompactSupport_derivedFactor i j hα.2.1,
    (SmoothingDeriv.tsupport_derivedFactor_subset i j α).trans hα.2.2⟩

private theorem SmoothingDeriv.isSmoothingKernel_of_archFactor {α : (Fin 3 → Fin 3 → ℝ) → ℂ}
    {K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ))} (hα : IsSmoothArchFactor α)
    (hK : ∀ p, IsOpen (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ))) ∧
      IsCompact (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ))))
    (hcof : ∀ᶠ p in Filter.cofinite, K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p) :
    IsSmoothingKernel fun g => α (archEntries g) *
      Set.indicator {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p} (fun _ => (1 : ℂ)) g :=
  ⟨α, K', hα, hK, hcof, fun _ => rfl⟩

private noncomputable def KernelConj.conjCLM (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (Fin 3 → Fin 3 → ℝ) →L[ℝ] (Fin 3 → Fin 3 → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := CentreConj.conjEntries g
      map_add' := fun e v => by
        funext a b
        show CentreConj.conjMat g (Matrix.of e + Matrix.of v) a b =
          CentreConj.conjMat g (Matrix.of e) a b + CentreConj.conjMat g (Matrix.of v) a b
        simp only [CentreConj.conjMat, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
      map_smul' := fun s e => by
        funext a b
        show CentreConj.conjMat g (s • Matrix.of e) a b = s • CentreConj.conjMat g (Matrix.of e) a b
        simp only [CentreConj.conjMat, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply] }

private theorem KernelConj.coe_conjCLM (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ⇑(KernelConj.conjCLM g) = CentreConj.conjEntries g :=
  rfl

private theorem KernelConj.contDiff_conjEntries (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ContDiff ℝ (⊤ : ℕ∞) (CentreConj.conjEntries g) := by
  rw [← KernelConj.coe_conjCLM g]
  exact (KernelConj.conjCLM g).contDiff

private theorem KernelConj.continuous_conjEntries (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    Continuous (CentreConj.conjEntries g) :=
  (KernelConj.contDiff_conjEntries g).continuous

private theorem CentreConj.isArchSmooth3_translateRight {H : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hH : WhittakerBlock.IsArchSmooth3 H) (y : AdelicGL 3 (𝓞 ℚ) ℚ) :
    WhittakerBlock.IsArchSmooth3 (translateRight y H) := by
  intro g
  refine ContDiffOn.congr (s := CentreConj.invertibleArrays)
    (ContDiffOn.comp (t := CentreConj.invertibleArrays) (hH (g * y))
      (KernelConj.contDiff_conjEntries y).contDiffOn fun e he => ?_) fun e he => ?_
  · show (Matrix.of (CentreConj.conjEntries y e)).det ≠ 0
    rw [CentreConj.det_of_conjEntries]
    exact he
  · show translateRight y H (g * WhittakerBlock.archRealLift3 e) =
      H (g * y * WhittakerBlock.archRealLift3 (CentreConj.conjEntries y e))
    rw [translateRight_apply, CentreConj.mul_archRealLift3_mul g y he]

private noncomputable def CentreConj.combList :
    List (Fin 3 × Fin 3) → AdelicGL 3 (𝓞 ℚ) ℚ → WhittakerBlock.smoothFunctions3 → WhittakerBlock.smoothFunctions3
  | [], _, φ => φ
  | p :: m, y, φ =>
    CentreConj.comb (CentreConj.conjEntries y (CentreConj.elemArr p.1 p.2)) (CentreConj.combList m y φ)

private theorem CentreConj.transport_list (φ : WhittakerBlock.smoothFunctions3) (y : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ∀ m : List (Fin 3 × Fin 3),
    m.foldr (fun p G => WhittakerBlock.archDeriv p.1 p.2 G) (translateRight y (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) =
      translateRight y (CentreConj.combList m y φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
  | [] => rfl
  | p :: m => by
    rw [List.foldr_cons, CentreConj.transport_list φ y m, CentreConj.archDeriv_translateRight_coe]
    rfl

private noncomputable def CentreConj.derivList (n : List (Fin 3 × Fin 3)) :
    WhittakerBlock.smoothFunctions3 →ₗ[ℂ] WhittakerBlock.smoothFunctions3 :=
  n.foldr (fun p L => WhittakerBlock.archDerivₗ p.1 p.2 ∘ₗ L) LinearMap.id

private theorem CentreConj.coe_derivList (ψ : WhittakerBlock.smoothFunctions3) : ∀ n : List (Fin 3 × Fin 3),
    n.foldr (fun p G => WhittakerBlock.archDeriv p.1 p.2 G) (ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) =
      (CentreConj.derivList n ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
  | [] => rfl
  | p :: n => by
    rw [List.foldr_cons, CentreConj.coe_derivList ψ n, ← WhittakerBlock.coe_archDerivₗ_apply]
    rfl

private theorem CentreConj.foldr_archDeriv_coe_comb (n : List (Fin 3 × Fin 3)) (c : Fin 3 → Fin 3 → ℝ)
    (ψ : WhittakerBlock.smoothFunctions3) (w : AdelicGL 3 (𝓞 ℚ) ℚ) :
    n.foldr (fun p G => WhittakerBlock.archDeriv p.1 p.2 G) (CentreConj.comb c ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) w =
      ∑ a : Fin 3, ∑ b : Fin 3,
        (c a b : ℂ) *
          (n ++ [(a, b)]).foldr (fun p G => WhittakerBlock.archDeriv p.1 p.2 G) (ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) w := by
  rw [CentreConj.coe_derivList (CentreConj.comb c ψ) n]
  simp only [List.foldr_append, List.foldr_cons, List.foldr_nil, ← WhittakerBlock.coe_archDerivₗ_apply,
    CentreConj.coe_derivList, CentreConj.comb, map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

private theorem CentreConj.continuous_conjEntries_coeff (hc : Continuous archEntries) (e : Fin 3 → Fin 3 → ℝ)
    (a b : Fin 3) :
    Continuous fun y : AdelicGL 3 (𝓞 ℚ) ℚ => CentreConj.conjEntries y e a b := by
  simp only [CentreConj.conjEntries, CentreConj.conjMat, CentreConj.realMatrix, Matrix.mul_apply, Matrix.of_apply]
  refine continuous_finsetSum _ fun d _ => Continuous.mul (continuous_finsetSum _ fun c _ => Continuous.mul ?_
    continuous_const) ?_
  · exact (continuous_apply c).comp ((continuous_apply a).comp (hc.comp continuous_inv))
  · exact (continuous_apply b).comp ((continuous_apply d).comp hc)

private theorem SmoothingDeriv.of_eArr_mul_of_eArr (i j : Fin 3) (s t : ℝ) :
    Matrix.of (SmoothingDeriv.eArr i j s) * Matrix.of (SmoothingDeriv.eArr i j t) =
      Matrix.of (SmoothingDeriv.eArr i j (s + t + if i = j then s * t else 0)) := by
  fin_cases i <;> fin_cases j <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [SmoothingDeriv.eArr, Matrix.mul_apply, Fin.sum_univ_three] <;> ring1

private theorem SmoothingDeriv.step_add (i j : Fin 3) {s : ℝ} (hs : 1 + (if i = j then s else 0) ≠ 0) (h : ℝ) :
    (s + h / (1 + if i = j then s else 0) + if i = j then s * (h / (1 + if i = j then s else 0)) else 0) = s + h := by
  by_cases hij : i = j
  · simp only [hij, if_true] at hs ⊢
    field_simp
    ring1
  · simp [hij]

private theorem SmoothingDeriv.hasDerivAt_reparam {f : ℝ → ℂ} {d : ℂ} (hf : HasDerivAt f d 0) (c s : ℝ) :
    HasDerivAt (fun u : ℝ => f ((u - s) / c)) ((c⁻¹ : ℝ) • d) s := by
  have hlin : HasDerivAt (fun u : ℝ => (u - s) / c) (c⁻¹ : ℝ) s := by
    simpa using ((hasDerivAt_id s).sub_const s).div_const c
  have h0 : (s - s) / c = 0 := by
    simp
  have hf' : HasDerivAt f d ((s - s) / c) := by
    rw [h0]
    exact hf
  exact hf'.scomp s hlin

private theorem SmoothingDeriv.eLift_mul_eLift (i j : Fin 3) {s t : ℝ} (hs : 1 + (if i = j then s else 0) ≠ 0)
    (ht : 1 + (if i = j then t else 0) ≠ 0) :
    SmoothingDeriv.eLift i j s * SmoothingDeriv.eLift i j t =
      SmoothingDeriv.eLift i j (s + t + if i = j then s * t else 0) := by
  unfold SmoothingDeriv.eLift
  rw [WhittakerBlock.archRealLift3_mul (SmoothingDeriv.det_eArr_ne_zero hs) (SmoothingDeriv.det_eArr_ne_zero ht)]
  congr 1
  funext a b
  rw [SmoothingDeriv.of_eArr_mul_of_eArr]
  rfl

private theorem SmoothingDeriv.continuous_det_of : Continuous fun e : Fin 3 → Fin 3 → ℝ => (Matrix.of e).det := by
  simp only [Matrix.det_fin_three, Matrix.of_apply]
  fun_prop

private theorem SmoothingDeriv.contDiff_eArr (i j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (SmoothingDeriv.eArr i j) := by
  refine contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_
  simp only [SmoothingDeriv.eArr]
  by_cases h : a = i ∧ b = j
  · simp only [h, and_self, if_true]
    exact contDiff_const.add contDiff_id
  · simp only [h, if_false, add_zero]
    exact contDiff_const

private theorem SmoothingDeriv.setOf_det_mem_nhds (i j : Fin 3) {s : ℝ} (hs : 1 + (if i = j then s else 0) ≠ 0) :
    {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} ∈ nhds (SmoothingDeriv.eArr i j s) :=
  SmoothingDeriv.continuous_det_of.continuousAt.preimage_mem_nhds
    (isOpen_ne.mem_nhds (SmoothingDeriv.det_eArr_ne_zero hs))

private theorem SmoothingDeriv.hasDerivAt_curve {f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hf : WhittakerBlock.IsArchSmooth3 f)
    (i j : Fin 3) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    HasDerivAt (fun t => f (g * SmoothingDeriv.eLift i j t)) (WhittakerBlock.archDeriv i j f g) 0 := by
  have hmem := SmoothingDeriv.setOf_det_mem_nhds i j (s := 0) (by simp)
  have hchart : DifferentiableAt ℝ (fun e : Fin 3 → Fin 3 → ℝ => f (g * WhittakerBlock.archRealLift3 e))
      (SmoothingDeriv.eArr i j 0) :=
    ((hf g).contDiffAt hmem).differentiableAt (by simp)
  have hline : DifferentiableAt ℝ (SmoothingDeriv.eArr i j) 0 :=
    (SmoothingDeriv.contDiff_eArr i j).differentiable (by simp) 0
  have hcomp : DifferentiableAt ℝ (fun t => f (g * SmoothingDeriv.eLift i j t)) 0 := hchart.comp 0 hline
  rw [SmoothingDeriv.archDeriv_apply]
  exact hcomp.hasDerivAt

private theorem SmoothingDeriv.hasDerivAt_curve_at {f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hf : WhittakerBlock.IsArchSmooth3 f)
    (i j : Fin 3) (x : AdelicGL 3 (𝓞 ℚ) ℚ) {s : ℝ} (hs : 1 + (if i = j then s else 0) ≠ 0) :
    HasDerivAt (fun u => f (x * SmoothingDeriv.eLift i j u))
      (((1 + if i = j then s else 0)⁻¹ : ℝ) • WhittakerBlock.archDeriv i j f (x * SmoothingDeriv.eLift i j s)) s := by
  have hre := SmoothingDeriv.hasDerivAt_reparam
    (SmoothingDeriv.hasDerivAt_curve hf i j (x * SmoothingDeriv.eLift i j s)) (1 + if i = j then s else 0) s
  refine hre.congr_of_eventuallyEq ?_
  have hcont : Continuous fun u : ℝ => 1 + if i = j then (u - s) / (1 + if i = j then s else 0) else 0 := by
    split_ifs <;> fun_prop
  have hne : (fun u : ℝ => 1 + if i = j then (u - s) / (1 + if i = j then s else 0) else 0) s ≠ 0 := by
    simp
  filter_upwards [hcont.continuousAt.eventually_ne hne] with u hu
  rw [mul_assoc, SmoothingDeriv.eLift_mul_eLift i j hs hu, SmoothingDeriv.step_add i j hs (u - s), add_sub_cancel]

private theorem SmoothingDeriv.eLift_zero (i j : Fin 3) : SmoothingDeriv.eLift i j 0 = 1 := by
  unfold SmoothingDeriv.eLift
  have h : SmoothingDeriv.eArr i j 0 = fun a b => if a = b then (1 : ℝ) else 0 := by
    funext a b
    simp [SmoothingDeriv.eArr]
  rw [h]
  exact SmoothingDeriv.archRealLift3_idArr

private def SmoothingDeriv.clamp (s : ℝ) : ℝ := max (-(1 / 2 : ℝ)) (min (1 / 2 : ℝ) s)

private theorem SmoothingDeriv.continuous_clamp : Continuous SmoothingDeriv.clamp :=
  continuous_const.max (continuous_const.min continuous_id)

private theorem SmoothingDeriv.neg_half_le_clamp (s : ℝ) : -(1 / 2 : ℝ) ≤ SmoothingDeriv.clamp s :=
  le_max_left _ _

private theorem SmoothingDeriv.clamp_eq_self {s : ℝ} (hs : s ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) :
    SmoothingDeriv.clamp s = s := by
  unfold SmoothingDeriv.clamp
  rw [min_eq_right hs.2, max_eq_right hs.1]

private theorem SmoothingDeriv.one_add_clamp_ne_zero (i j : Fin 3) (s : ℝ) :
    1 + (if i = j then SmoothingDeriv.clamp s else 0) ≠ 0 := by
  have h := SmoothingDeriv.neg_half_le_clamp s
  split_ifs <;> intro h0 <;> linarith

private theorem SmoothingDeriv.continuous_eArr_entry (i j a b : Fin 3) :
    Continuous fun t : ℝ => SmoothingDeriv.eArr i j t a b := by
  simp only [SmoothingDeriv.eArr]
  split_ifs <;> fun_prop

private theorem SmoothingDeriv.continuous_sigma_clamp (i j : Fin 3) :
    Continuous fun s : ℝ => SmoothingDeriv.sigma i j (SmoothingDeriv.clamp s) := by
  unfold SmoothingDeriv.sigma
  split_ifs
  · refine (SmoothingDeriv.continuous_clamp.neg).div (continuous_const.add SmoothingDeriv.continuous_clamp) ?_
    intro s
    have h := SmoothingDeriv.neg_half_le_clamp s
    linarith
  · exact SmoothingDeriv.continuous_clamp.neg.div_const _

private theorem SmoothingDeriv.continuous_realAdeleHom : Continuous SmoothingDeriv.realAdeleHom := by
  have h : (SmoothingDeriv.realAdeleHom : ℝ → InfiniteAdeleRing ℚ) = realCoordinateHomeomorph.symm := by
    funext r
    apply realCoordinateHomeomorph.injective
    rw [Homeomorph.apply_symm_apply, realCoordinateHomeomorph_apply, SmoothingDeriv.realCoordinate_realAdeleHom]
  rw [h]
  exact realCoordinateHomeomorph.symm.continuous

private theorem SmoothingDeriv.continuous_archRealMat3_comp {e : ℝ → Fin 3 → Fin 3 → ℝ}
    (he : ∀ a b, Continuous fun t => e t a b) : Continuous fun t => WhittakerBlock.archRealMat3 (e t) := by
  refine continuous_matrix fun a b => ?_
  simp only [SmoothingDeriv.archRealMat3_eq]
  show Continuous fun t : ℝ => ((SmoothingDeriv.realAdeleHom (e t a b),
    (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) a b) : InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ)
  exact (SmoothingDeriv.continuous_realAdeleHom.comp (he a b)).prodMk continuous_const

private theorem SmoothingDeriv.eLift_inv (i j : Fin 3) {s : ℝ} (hs : 1 + (if i = j then s else 0) ≠ 0) :
    (SmoothingDeriv.eLift i j s)⁻¹ = SmoothingDeriv.eLift i j (SmoothingDeriv.sigma i j s) :=
  (eq_inv_of_mul_eq_one_left (SmoothingDeriv.eLift_sigma_mul i j hs)).symm

private theorem SmoothingDeriv.continuous_eLift_clamp (i j : Fin 3) :
    Continuous fun s : ℝ => SmoothingDeriv.eLift i j (SmoothingDeriv.clamp s) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · have h : (fun s : ℝ => ((SmoothingDeriv.eLift i j (SmoothingDeriv.clamp s) : AdelicGL 3 (𝓞 ℚ) ℚ) :
        Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))) =
        fun s => WhittakerBlock.archRealMat3 (SmoothingDeriv.eArr i j (SmoothingDeriv.clamp s)) := by
      funext s
      exact SmoothingDeriv.coe_archRealLift3
        (SmoothingDeriv.det_eArr_ne_zero (SmoothingDeriv.one_add_clamp_ne_zero i j s))
    show Continuous fun s : ℝ => ((SmoothingDeriv.eLift i j (SmoothingDeriv.clamp s) : AdelicGL 3 (𝓞 ℚ) ℚ) :
      Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))
    rw [h]
    exact SmoothingDeriv.continuous_archRealMat3_comp fun a b =>
      (SmoothingDeriv.continuous_eArr_entry i j a b).comp SmoothingDeriv.continuous_clamp
  · have h : (fun s : ℝ => (((SmoothingDeriv.eLift i j (SmoothingDeriv.clamp s))⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) :
        Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))) =
        fun s => WhittakerBlock.archRealMat3
          (SmoothingDeriv.eArr i j (SmoothingDeriv.sigma i j (SmoothingDeriv.clamp s))) := by
      funext s
      rw [SmoothingDeriv.eLift_inv i j (SmoothingDeriv.one_add_clamp_ne_zero i j s)]
      exact SmoothingDeriv.coe_archRealLift3
        (SmoothingDeriv.det_eArr_sigma_ne_zero (SmoothingDeriv.one_add_clamp_ne_zero i j s))
    show Continuous fun s : ℝ => (((SmoothingDeriv.eLift i j (SmoothingDeriv.clamp s))⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) :
      Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))
    rw [h]
    exact SmoothingDeriv.continuous_archRealMat3_comp fun a b =>
      (SmoothingDeriv.continuous_eArr_entry i j a b).comp (SmoothingDeriv.continuous_sigma_clamp i j)

private theorem SmoothingDeriv.continuousOn_eLift (i j : Fin 3) :
    ContinuousOn (SmoothingDeriv.eLift i j) (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) :=
  (SmoothingDeriv.continuous_eLift_clamp i j).continuousOn.congr fun s hs => by
    simp only [SmoothingDeriv.clamp_eq_self hs]

private def SmoothingDeriv.famOp (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (G : AdelicGL 3 (𝓞 ℚ) ℚ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    AdelicGL 3 (𝓞 ℚ) ℚ → ℂ :=
  fun x => ∫ y, φ y * G y x ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)

private theorem SmoothingDeriv.famOp_translateRight (φ f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    SmoothingDeriv.famOp φ (fun y => translateRight y f) = smoothingOperator φ f :=
  rfl

private theorem SmoothingDeriv.half_le_one_add (i j : Fin 3) {s : ℝ} (hs : s ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) :
    (1 / 2 : ℝ) ≤ 1 + if i = j then s else 0 := by
  split_ifs
  · linarith [hs.1]
  · norm_num

private theorem SmoothingDeriv.one_add_ne_zero_of_mem (i j : Fin 3) {s : ℝ}
    (hs : s ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) : 1 + (if i = j then s else 0) ≠ 0 := by
  have h := SmoothingDeriv.half_le_one_add i j hs
  intro h0
  rw [h0] at h
  norm_num at h

private theorem SmoothingDeriv.abs_inv_one_add_le (i j : Fin 3) {s : ℝ} (hs : s ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) :
    |((1 + if i = j then s else 0)⁻¹ : ℝ)| ≤ 2 := by
  have h := SmoothingDeriv.half_le_one_add i j hs
  have hpos : (0 : ℝ) < 1 + if i = j then s else 0 := by linarith
  rw [abs_of_pos (inv_pos.2 hpos), inv_le_comm₀ hpos (by norm_num)]
  linarith

private theorem SmoothingDeriv.archDeriv_famOp {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} {C : Set (AdelicGL 3 (𝓞 ℚ) ℚ)}
    (hC : IsCompact C) (hsupp : Function.support φ ⊆ C)
    (hφm : AEStronglyMeasurable φ (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
    (hφb : ∃ M : ℝ, ∀ g, ‖φ g‖ ≤ M)
    {G : AdelicGL 3 (𝓞 ℚ) ℚ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hG : ∀ y, WhittakerBlock.IsArchSmooth3 (G y))
    (hGc : Continuous fun q : AdelicGL 3 (𝓞 ℚ) ℚ × AdelicGL 3 (𝓞 ℚ) ℚ => G q.2 q.1) (i j : Fin 3)
    (hDc : Continuous fun q : AdelicGL 3 (𝓞 ℚ) ℚ × AdelicGL 3 (𝓞 ℚ) ℚ => WhittakerBlock.archDeriv i j (G q.2) q.1)
    (hcurve : ContinuousOn (SmoothingDeriv.eLift i j) (Set.Icc (-(1 / 2 : ℝ)) (1 / 2))) :
    WhittakerBlock.archDeriv i j (SmoothingDeriv.famOp φ G) =
      SmoothingDeriv.famOp φ (fun y => WhittakerBlock.archDeriv i j (G y)) := by
  haveI : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
  funext x

  set I : Set ℝ := Set.Icc (-(1 / 2 : ℝ)) (1 / 2) with hI
  have hI0 : I ∈ nhds (0 : ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)

  have hslice : ∀ s : ℝ, Continuous fun y => G y (x * SmoothingDeriv.eLift i j s) := fun s =>
    hGc.comp (continuous_const.prodMk continuous_id)
  have hdslice : ∀ s : ℝ, Continuous fun y => WhittakerBlock.archDeriv i j (G y) (x * SmoothingDeriv.eLift i j s) :=
    fun s => hDc.comp (continuous_const.prodMk continuous_id)
  have hint : ∀ (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), Continuous f →
      Integrable (fun y => φ y * f y) (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := by
    intro f hf
    have h := integrable_mul_of_support_subset hC hsupp hφm hφb hf 1
    simpa only [one_mul] using h

  have hK : IsCompact (I ×ˢ C) := isCompact_Icc.prod hC
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    (f := fun q : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => WhittakerBlock.archDeriv i j (G q.2) (x * SmoothingDeriv.eLift i j q.1))
    (hDc.comp_continuousOn ((continuousOn_const.mul (hcurve.comp continuousOn_fst fun q hq => hq.1)).prodMk
      continuousOn_snd))

  have hbound : ∀ᵐ y ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ), ∀ s ∈ I,
      ‖φ y * ((((1 + if i = j then s else 0)⁻¹ : ℝ)) •
        WhittakerBlock.archDeriv i j (G y) (x * SmoothingDeriv.eLift i j s))‖ ≤ 2 * B * ‖φ y‖ := by
    refine Filter.Eventually.of_forall fun y s hs => ?_
    by_cases hy : y ∈ C
    · rw [norm_mul, norm_smul, Real.norm_eq_abs, mul_comm (2 * B)]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (SmoothingDeriv.abs_inv_one_add_le i j hs) (hB (s, y) ⟨hs, hy⟩) (norm_nonneg _)
          (by norm_num))
        (norm_nonneg _)
    · have hy0 : φ y = 0 := by
        by_contra h
        exact hy (hsupp h)
      simp [hy0]
  have hdiff : ∀ᵐ y ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ), ∀ s ∈ I,
      HasDerivAt (fun u => φ y * G y (x * SmoothingDeriv.eLift i j u))
        (φ y * ((((1 + if i = j then s else 0)⁻¹ : ℝ)) •
          WhittakerBlock.archDeriv i j (G y) (x * SmoothingDeriv.eLift i j s))) s :=
    Filter.Eventually.of_forall fun y s hs =>
      (SmoothingDeriv.hasDerivAt_curve_at (hG y) i j x
        (SmoothingDeriv.one_add_ne_zero_of_mem i j hs)).const_mul (φ y)
  have hbint : Integrable (fun y => 2 * B * ‖φ y‖) (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) :=
    ((hint (fun _ => (1 : ℂ)) continuous_const).norm.const_mul (2 * B)).congr
      (Filter.Eventually.of_forall fun y => by simp)
  have hF'm : AEStronglyMeasurable
      (fun y => φ y * ((((1 + if i = j then (0 : ℝ) else 0)⁻¹ : ℝ)) • WhittakerBlock.archDeriv i j (G y)
        (x * SmoothingDeriv.eLift i j 0))) (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := by
    have h := (hint _ (hdslice 0)).aestronglyMeasurable
    simpa using h

  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)
    (F := fun (s : ℝ) (y : AdelicGL 3 (𝓞 ℚ) ℚ) => φ y * G y (x * SmoothingDeriv.eLift i j s))
    (F' := fun (s : ℝ) (y : AdelicGL 3 (𝓞 ℚ) ℚ) => φ y *
      ((((1 + if i = j then s else 0)⁻¹ : ℝ)) • WhittakerBlock.archDeriv i j (G y) (x * SmoothingDeriv.eLift i j s)))
    (x₀ := 0) (bound := fun y => 2 * B * ‖φ y‖) hI0
    (Filter.Eventually.of_forall fun s => (hint _ (hslice s)).aestronglyMeasurable) (hint _ (hslice 0))
    hF'm hbound hbint hdiff

  rw [SmoothingDeriv.archDeriv_apply]
  have hderiv := hmain.2.deriv
  simp only [SmoothingDeriv.famOp] at hderiv ⊢
  rw [hderiv]
  simp [SmoothingDeriv.eLift_zero]

private def SmoothingDeriv.derivAlong (l : List (Fin 3 × Fin 3)) (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    AdelicGL 3 (𝓞 ℚ) ℚ → ℂ :=
  l.foldr (fun p G => WhittakerBlock.archDeriv p.1 p.2 G) f

private theorem SmoothingDeriv.derivAlong_nil (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : SmoothingDeriv.derivAlong [] f = f :=
  rfl

private theorem SmoothingDeriv.derivAlong_cons (p : Fin 3 × Fin 3) (l : List (Fin 3 × Fin 3))
    (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    SmoothingDeriv.derivAlong (p :: l) f = WhittakerBlock.archDeriv p.1 p.2 (SmoothingDeriv.derivAlong l f) :=
  rfl

private theorem SmoothingDeriv.continuous_derivAlong_combList (hc : Continuous archEntries)
    (ψ : WhittakerBlock.smoothFunctions3)
    (hreg : ∀ l : List (Fin 3 × Fin 3), Continuous (SmoothingDeriv.derivAlong l (ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) :
    ∀ (m n : List (Fin 3 × Fin 3)), Continuous fun q : AdelicGL 3 (𝓞 ℚ) ℚ × AdelicGL 3 (𝓞 ℚ) ℚ =>
      SmoothingDeriv.derivAlong n (CentreConj.combList m q.2 ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (q.1 * q.2)
  | [], n => by
    simp only [CentreConj.combList]
    exact (hreg n).comp (continuous_fst.mul continuous_snd)
  | p :: m, n => by
    have hrec := SmoothingDeriv.continuous_derivAlong_combList hc ψ hreg m
    simp only [CentreConj.combList, SmoothingDeriv.derivAlong, CentreConj.foldr_archDeriv_coe_comb]
    refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => Continuous.mul ?_ ?_
    · exact Complex.continuous_ofReal.comp
        ((CentreConj.continuous_conjEntries_coeff hc (CentreConj.elemArr p.1 p.2) a b).comp continuous_snd)
    · exact hrec (n ++ [(a, b)])

private theorem SmoothingDeriv.continuous_derivAlong_translateRight (hc : Continuous archEntries)
    (ψ : WhittakerBlock.smoothFunctions3)
    (hreg : ∀ l : List (Fin 3 × Fin 3), Continuous (SmoothingDeriv.derivAlong l (ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)))
    (l : List (Fin 3 × Fin 3)) :
    Continuous fun q : AdelicGL 3 (𝓞 ℚ) ℚ × AdelicGL 3 (𝓞 ℚ) ℚ =>
      SmoothingDeriv.derivAlong l (translateRight q.2 (ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) q.1 := by
  have h := SmoothingDeriv.continuous_derivAlong_combList hc ψ hreg l []
  refine h.congr fun q => ?_
  simp only [SmoothingDeriv.derivAlong, CentreConj.transport_list, translateRight_apply, List.foldr_nil]

private theorem SmoothingDeriv.isArchSmooth3_derivAlong_translateRight (ψ : WhittakerBlock.smoothFunctions3)
    (l : List (Fin 3 × Fin 3)) (y : AdelicGL 3 (𝓞 ℚ) ℚ) :
    WhittakerBlock.IsArchSmooth3 (SmoothingDeriv.derivAlong l (translateRight y (ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) := by
  unfold SmoothingDeriv.derivAlong
  rw [CentreConj.transport_list]
  exact CentreConj.isArchSmooth3_translateRight (WhittakerBlock.mem_smoothFunctions3.1 (CentreConj.combList l y ψ).2) y

private theorem SmoothingDeriv.derivAlong_famOp (hc : Continuous archEntries) {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    {C : Set (AdelicGL 3 (𝓞 ℚ) ℚ)} (hC : IsCompact C) (hsupp : Function.support φ ⊆ C)
    (hφm : AEStronglyMeasurable φ (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
    (hφb : ∃ M : ℝ, ∀ g, ‖φ g‖ ≤ M) (ψ : WhittakerBlock.smoothFunctions3)
    (hreg : ∀ l : List (Fin 3 × Fin 3), Continuous (SmoothingDeriv.derivAlong l (ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) :
    ∀ l : List (Fin 3 × Fin 3),
      SmoothingDeriv.derivAlong l (SmoothingDeriv.famOp φ fun y => translateRight y (ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) =
        SmoothingDeriv.famOp φ fun y => SmoothingDeriv.derivAlong l (translateRight y (ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))
  | [] => rfl
  | p :: l => by
    rw [SmoothingDeriv.derivAlong_cons, SmoothingDeriv.derivAlong_famOp hc hC hsupp hφm hφb ψ hreg l]
    have hD := SmoothingDeriv.continuous_derivAlong_translateRight hc ψ hreg (p :: l)
    simp only [SmoothingDeriv.derivAlong_cons] at hD
    exact SmoothingDeriv.archDeriv_famOp hC hsupp hφm hφb
      (SmoothingDeriv.isArchSmooth3_derivAlong_translateRight ψ l)
      (SmoothingDeriv.continuous_derivAlong_translateRight hc ψ hreg l) p.1 p.2 hD
      (SmoothingDeriv.continuousOn_eLift p.1 p.2)

private theorem SmoothingDeriv.casimir1_eq (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (x : AdelicGL 3 (𝓞 ℚ) ℚ) :
    WhittakerBlock.casimir1 f x = ∑ i : Fin 3, SmoothingDeriv.derivAlong [(i, i)] f x :=
  rfl

private theorem SmoothingDeriv.casimir2_eq (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (x : AdelicGL 3 (𝓞 ℚ) ℚ) :
    WhittakerBlock.casimir2 f x = ∑ i : Fin 3, ∑ j : Fin 3, SmoothingDeriv.derivAlong [(i, j), (j, i)] f x :=
  rfl

private theorem SmoothingDeriv.casimir3_eq (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (x : AdelicGL 3 (𝓞 ℚ) ℚ) :
    WhittakerBlock.casimir3 f x =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, SmoothingDeriv.derivAlong [(i, j), (j, k), (k, i)] f x :=
  rfl

private theorem SmoothingDeriv.sum_famOp {ι : Type} (t : Finset ι) {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    {C : Set (AdelicGL 3 (𝓞 ℚ) ℚ)} (hC : IsCompact C) (hsupp : Function.support φ ⊆ C)
    (hφm : AEStronglyMeasurable φ (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
    (hφb : ∃ M : ℝ, ∀ g, ‖φ g‖ ≤ M) (G : ι → AdelicGL 3 (𝓞 ℚ) ℚ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hG : ∀ a, Continuous fun q : AdelicGL 3 (𝓞 ℚ) ℚ × AdelicGL 3 (𝓞 ℚ) ℚ => G a q.2 q.1) (x : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ∑ a ∈ t, SmoothingDeriv.famOp φ (G a) x = SmoothingDeriv.famOp φ (fun y z => ∑ a ∈ t, G a y z) x := by
  haveI : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  simp only [SmoothingDeriv.famOp, Finset.mul_sum]
  rw [integral_finsetSum]
  intro a _
  have hc : Continuous fun y => G a y x := (hG a).comp (continuous_const.prodMk continuous_id)
  have h := integrable_mul_of_support_subset hC hsupp hφm hφb hc 1
  simpa only [one_mul] using h

private theorem SmoothingDeriv.famOp_eq_smoothingOperator {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    {F : AdelicGL 3 (𝓞 ℚ) ℚ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} {h : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} {x : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hF : ∀ y, F y x = h (x * y)) : SmoothingDeriv.famOp φ F x = smoothingOperator φ h x := by
  simp only [SmoothingDeriv.famOp, smoothingOperator_apply, hF]

private theorem SmoothingDeriv.casimir_smoothingOperator_of_translate (hc : Continuous archEntries)
    {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} {C : Set (AdelicGL 3 (𝓞 ℚ) ℚ)} (hC : IsCompact C) (hsupp : Function.support φ ⊆ C)
    (hφm : AEStronglyMeasurable φ (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
    (hφb : ∃ M : ℝ, ∀ g, ‖φ g‖ ≤ M) {H : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hH : WhittakerBlock.IsArchSmooth3 H)
    (hreg : ∀ l : List (Fin 3 × Fin 3), Continuous (l.foldr (fun p G => WhittakerBlock.archDeriv p.1 p.2 G) H))
    (hK : ∀ y : AdelicGL 3 (𝓞 ℚ) ℚ,
      WhittakerBlock.casimir1 (translateRight y H) = translateRight y (WhittakerBlock.casimir1 H) ∧
        WhittakerBlock.casimir2 (translateRight y H) = translateRight y (WhittakerBlock.casimir2 H) ∧
          WhittakerBlock.casimir3 (translateRight y H) = translateRight y (WhittakerBlock.casimir3 H)) :
    WhittakerBlock.casimir1 (smoothingOperator φ H) = smoothingOperator φ (WhittakerBlock.casimir1 H) ∧
      WhittakerBlock.casimir2 (smoothingOperator φ H) = smoothingOperator φ (WhittakerBlock.casimir2 H) ∧
        WhittakerBlock.casimir3 (smoothingOperator φ H) = smoothingOperator φ (WhittakerBlock.casimir3 H) := by
  let ψ : WhittakerBlock.smoothFunctions3 := ⟨H, hH⟩
  have hreg' : ∀ l : List (Fin 3 × Fin 3),
      Continuous (SmoothingDeriv.derivAlong l (ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) := hreg
  have hL := SmoothingDeriv.derivAlong_famOp hc hC hsupp hφm hφb ψ hreg'
  have hcont := SmoothingDeriv.continuous_derivAlong_translateRight hc ψ hreg'
  have hS : smoothingOperator φ H =
      SmoothingDeriv.famOp φ fun y => translateRight y (ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) := rfl
  refine ⟨?_, ?_, ?_⟩
  · funext x
    rw [SmoothingDeriv.casimir1_eq, hS]
    simp only [hL]
    refine (SmoothingDeriv.sum_famOp Finset.univ hC hsupp hφm hφb
      (fun i y => SmoothingDeriv.derivAlong [(i, i)] (translateRight y (ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)))
      (fun i => hcont _) x).trans ?_
    refine SmoothingDeriv.famOp_eq_smoothingOperator fun y => ?_
    have h := congrFun (hK y).1 x
    rw [translateRight_apply] at h
    rw [← h]
    rfl
  · funext x
    rw [SmoothingDeriv.casimir2_eq, hS]
    simp only [hL, ← Fintype.sum_prod_type']
    refine (SmoothingDeriv.sum_famOp Finset.univ hC hsupp hφm hφb
      (fun p : Fin 3 × Fin 3 =>
        fun y => SmoothingDeriv.derivAlong [(p.1, p.2), (p.2, p.1)] (translateRight y (ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)))
      (fun p => hcont _) x).trans ?_
    refine SmoothingDeriv.famOp_eq_smoothingOperator fun y => ?_
    have h := congrFun (hK y).2.1 x
    rw [translateRight_apply] at h
    rw [← h, SmoothingDeriv.casimir2_eq, ← Fintype.sum_prod_type']
  · funext x
    rw [SmoothingDeriv.casimir3_eq, hS]
    simp only [hL, ← Fintype.sum_prod_type']
    refine (SmoothingDeriv.sum_famOp Finset.univ hC hsupp hφm hφb
      (fun p : Fin 3 × Fin 3 × Fin 3 => fun y =>
        SmoothingDeriv.derivAlong [(p.1, p.2.1), (p.2.1, p.2.2), (p.2.2, p.1)]
          (translateRight y (ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)))
      (fun p => hcont _) x).trans ?_
    refine SmoothingDeriv.famOp_eq_smoothingOperator fun y => ?_
    have h := congrFun (hK y).2.2 x
    rw [translateRight_apply, SmoothingDeriv.casimir3_eq] at h
    simp only [← Fintype.sum_prod_type'] at h
    rw [← h]

private theorem SmoothingDeriv.exists_carrier_data {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hφ : IsSmoothingKernel φ) :
    ∃ C : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact C ∧ Function.support φ ⊆ C ∧
      AEStronglyMeasurable φ (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) ∧ ∃ M : ℝ, ∀ g, ‖φ g‖ ≤ M := by
  haveI : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  obtain ⟨α, K', hα, hoc, hcof, hφeq⟩ := hφ
  have hU := isOpen_and_isCompact_setOf_forall_componentAt3_finEmbedN_mem K' (fun p => (hoc p).1)
    (fun p => (hoc p).2) hcof
  refine ⟨_, ((isCompact_setOf_archEntries_archToAdelic3_mem_tsupport hα).prod hU.2).image
    ((continuous_archToAdelic3.comp continuous_fst).mul (continuous_finEmbedN3.comp continuous_snd)),
    support_subset_image archToAdelic3 finPart3 K' hφeq archToAdelic3_archComponent3_mul_finEmbedN_finPart3
      componentAt3_archToAdelic3 archEntries_mul_finEmbedN, ?_, exists_forall_norm_le hα K' hφeq⟩
  have hL : MeasurableSet (adelicLevelSet K') := by
    rw [adelicLevelSet_eq_preimage archToAdelic3 finPart3 archToAdelic3_archComponent3_mul_finEmbedN_finPart3
      componentAt3_archToAdelic3 K']
    exact (hU.1.preimage continuous_finPart3).measurableSet
  have hφfun : φ = fun g => α (archEntries g) * (adelicLevelSet K').indicator (fun _ => (1 : ℂ)) g := funext hφeq
  rw [hφfun]
  exact (hα.1.continuous.comp continuous_archEntries).aestronglyMeasurable.mul
    (aestronglyMeasurable_const.indicator hL)

private theorem SmoothingDeriv.casimir_smoothingOperator_of_forall {φ H : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hφ : IsSmoothingKernel φ) (hH : WhittakerBlock.IsArchSmooth3 H)
    (hreg : ∀ l : List (Fin 3 × Fin 3), Continuous (l.foldr (fun p G => WhittakerBlock.archDeriv p.1 p.2 G) H))
    (hK : ∀ y : AdelicGL 3 (𝓞 ℚ) ℚ,
      WhittakerBlock.casimir1 (translateRight y H) = translateRight y (WhittakerBlock.casimir1 H) ∧
        WhittakerBlock.casimir2 (translateRight y H) = translateRight y (WhittakerBlock.casimir2 H) ∧
          WhittakerBlock.casimir3 (translateRight y H) = translateRight y (WhittakerBlock.casimir3 H)) :
    WhittakerBlock.casimir1 (smoothingOperator φ H) = smoothingOperator φ (WhittakerBlock.casimir1 H) ∧
      WhittakerBlock.casimir2 (smoothingOperator φ H) = smoothingOperator φ (WhittakerBlock.casimir2 H) ∧
        WhittakerBlock.casimir3 (smoothingOperator φ H) = smoothingOperator φ (WhittakerBlock.casimir3 H) := by
  obtain ⟨C, hC, hsupp, hφm, hφb⟩ := SmoothingDeriv.exists_carrier_data hφ
  exact SmoothingDeriv.casimir_smoothingOperator_of_translate continuous_archEntries hC hsupp hφm hφb hH hreg hK

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_smoothingOperator.SmoothingTranslation.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_smoothingOperator.SmoothingTranslation.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_smoothingOperator.SmoothingTranslation"

theorem solution
    (φ H : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hφ : IsSmoothingKernel φ) (hH : WhittakerBlock.IsArchSmooth3 H)
    (hreg : ∀ l : List (Fin 3 × Fin 3), Continuous (l.foldr (fun p G => WhittakerBlock.archDeriv p.1 p.2 G) H)) :
    WhittakerBlock.casimir1 (smoothingOperator φ H) = smoothingOperator φ (WhittakerBlock.casimir1 H) ∧
      WhittakerBlock.casimir2 (smoothingOperator φ H) = smoothingOperator φ (WhittakerBlock.casimir2 H) ∧
        WhittakerBlock.casimir3 (smoothingOperator φ H) = smoothingOperator φ (WhittakerBlock.casimir3 H) := by
  exact SmoothingDeriv.casimir_smoothingOperator_of_forall hφ hH hreg (WhittakerBlock.casimir_translateRight H hH)

end S_LanglandsTunnell_CubicInduction_SlabL2_casimir_smoothingOperator
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_smoothingOperator (solution)
