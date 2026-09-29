-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/86aba982-3095-5293-bcc2-b28d96c080f2

import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Theorems.Thm_LanglandsTunnell_CubicInduction_isOpen_and_isCompact_setOf_forall_componentAt3_finEmbedN_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm

namespace SmoothingTranslation

open LanglandsTunnell.CubicInduction

section ComponentSplice

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

end ComponentSplice

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

private theorem realCoordinateHomeomorph_apply (x : InfiniteAdeleRing ℚ) : realCoordinateHomeomorph x = realCoordinate x :=
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

section Furniture

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

end Furniture

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator.SmoothingTranslation.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator.SmoothingTranslation.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator.SmoothingTranslation.LanglandsTunnell"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator.SmoothingTranslation.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator.SmoothingTranslation.LanglandsTunnell.CubicInduction"

end Integrability
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator.SmoothingTranslation.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator.SmoothingTranslation.LanglandsTunnell.CubicInduction"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator.SmoothingTranslation.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator.SmoothingTranslation.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator.SmoothingTranslation.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator.SmoothingTranslation.LanglandsTunnell.CubicInduction"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator.SmoothingTranslation.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator.SmoothingTranslation.LanglandsTunnell.CubicInduction"

end KernelIntegrability
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator.SmoothingTranslation.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator.SmoothingTranslation.LanglandsTunnell.CubicInduction"

section Commutation

open IsDedekindDomain NumberField MeasureTheory

noncomputable section

namespace LanglandsTunnell
namespace CubicInduction

attribute [local instance] NumberField.AdelicHaar.glBorel

section PullBack

variable {G H : Type*} [Group G] [Group H]

private theorem exists_of_mem_doubleCoset_map (f : G →* H) (U : Subgroup G) (g : G) {y : H}
    (hy : y ∈ HeckePair.doubleCoset (U.map f) (f g)) :
    ∃ x ∈ HeckePair.doubleCoset U g, f x = y := by
  obtain ⟨a, ha, b, hb, rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hy
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.mp hb
  exact ⟨u * g * u', HeckePair.mem_doubleCoset_iff.mpr ⟨u, hu, u', hu', rfl⟩, by simp [map_mul]⟩

end PullBack
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator.SmoothingTranslation.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator.SmoothingTranslation.LanglandsTunnell.CubicInduction"

variable {p : HeightOneSpectrum (𝓞 ℚ)}

private theorem exists_splice {h : AdelicGL 3 (𝓞 ℚ) ℚ} (hh : componentAt3 (𝓞 ℚ) ℚ p h = 1)
    {g : AdelicGL 3 (𝓞 ℚ) ℚ} (hg : componentAt3 (𝓞 ℚ) ℚ p g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) :
    ∃ b : AdelicGL 3 (𝓞 ℚ) ℚ, componentAt3 (𝓞 ℚ) ℚ p b = 1 ∧
      ∃ y ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p, h * g = b * localToAdelic3 p y :=
  ⟨h * (g * (localToAdelic3 p (componentAt3 (𝓞 ℚ) ℚ p g))⁻¹),
    by rw [map_mul, hh, one_mul]; exact componentAt3_mul_inv_localToAdelic3 g,
    componentAt3 (𝓞 ℚ) ℚ p g, hg, by rw [mul_assoc, mul_inv_localToAdelic3_mul_localToAdelic3]⟩

private theorem apply_mul_localToAdelic3_mul_eq {f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hK : IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) f)
    (z : LocalGL3 p) {b : AdelicGL 3 (𝓞 ℚ) ℚ} (hb : componentAt3 (𝓞 ℚ) ℚ p b = 1) {y : LocalGL3 p}
    (hy : y ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) (x : AdelicGL 3 (𝓞 ℚ) ℚ) :
    f (x * localToAdelic3 p z * (b * localToAdelic3 p y)) = f (x * b * localToAdelic3 p z) := by
  have hc : localToAdelic3 p z * b = b * localToAdelic3 p z :=
    (mul_localToAdelic3_comm_of_componentAt3_eq_one hb z).symm
  have hrw : x * localToAdelic3 p z * (b * localToAdelic3 p y) = x * b * localToAdelic3 p z * localToAdelic3 p y := by
    rw [← mul_assoc (x * localToAdelic3 p z) b, mul_assoc x (localToAdelic3 p z) b, hc, ← mul_assoc x b]
  rw [hrw]
  exact hK _ _ (Subgroup.mem_map_of_mem (localToAdelic3 p) hy)

private theorem apply_mul_mul_localToAdelic3_eq {f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hK : IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) f)
    (b : AdelicGL 3 (𝓞 ℚ) ℚ) {y : LocalGL3 p} (hy : y ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) (x : AdelicGL 3 (𝓞 ℚ) ℚ) :
    f (x * (b * localToAdelic3 p y)) = f (x * b) := by
  rw [← mul_assoc]
  exact hK _ _ (Subgroup.mem_map_of_mem (localToAdelic3 p) hy)

private theorem translateRight_smoothingOperator_apply (φ f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (h x : AdelicGL 3 (𝓞 ℚ) ℚ) :
    SlabL2.translateRight h (SlabL2.smoothingOperator φ f) x = ∫ g, φ g * f (x * h * g) ∂haarGL3 := rfl

private theorem isRightInvariant_of_forall {φ f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hφp : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, φ g ≠ 0 → componentAt3 (𝓞 ℚ) ℚ p g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p)
    {h : AdelicGL 3 (𝓞 ℚ) ℚ} (hh : componentAt3 (𝓞 ℚ) ℚ p h = 1)
    (hK : IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) f) :
    IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (SlabL2.translateRight h (SlabL2.smoothingOperator φ f)) := by
  intro x u hu
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hu
  rw [translateRight_smoothingOperator_apply, translateRight_smoothingOperator_apply]
  refine congrArg (integral haarGL3) ?_
  funext g
  by_cases hg : φ g = 0
  · simp [hg]
  obtain ⟨b, hb, y, hy, hby⟩ := exists_splice hh (hφp g hg)
  rw [mul_assoc (x * localToAdelic3 p k) h g, mul_assoc x h g, hby, apply_mul_localToAdelic3_mul_eq hK k hb hy x,
    hK _ _ (Subgroup.mem_map_of_mem (localToAdelic3 p) hk), apply_mul_mul_localToAdelic3_eq hK b hy x]

private theorem isCosetEigenfunction_of_forall {φ f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hint : ∀ x : AdelicGL 3 (𝓞 ℚ) ℚ, Integrable (fun g => φ g * f (x * g)) haarGL3)
    (hφp : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, φ g ≠ 0 → componentAt3 (𝓞 ℚ) ℚ p g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p)
    {h : AdelicGL 3 (𝓞 ℚ) ℚ} (hh : componentAt3 (𝓞 ℚ) ℚ p h = 1)
    (hK : IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) f)
    {gen : LocalGL3 p} {lam : ℂ}
    (hT : IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) (localToAdelic3 p gen) f
      lam) :
    IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) (localToAdelic3 p gen)
      (SlabL2.translateRight h (SlabL2.smoothingOperator φ f)) lam := by
  intro ι _ reps hsys x
  simp only [cosetSum, translateRight_smoothingOperator_apply]
  have hsum : ∫ g, ∑ i, φ g * f (x * reps i * h * g) ∂haarGL3 = ∑ i, ∫ g, φ g * f (x * reps i * h * g) ∂haarGL3 :=
    integral_finsetSum _ fun i _ => hint (x * reps i * h)
  have hconst : ∫ g, lam * (φ g * f (x * h * g)) ∂haarGL3 = lam * ∫ g, φ g * f (x * h * g) ∂haarGL3 :=
    integral_const_mul lam _
  rw [← hsum, ← hconst]
  refine congrArg (integral haarGL3) ?_
  funext g
  by_cases hg : φ g = 0
  · simp [hg]
  obtain ⟨b, hb, y, hy, hby⟩ := exists_splice hh (hφp g hg)
  have hterm : ∀ i, f (x * reps i * h * g) = f (x * b * reps i) := by
    intro i
    obtain ⟨z, -, hz⟩ := exists_of_mem_doubleCoset_map (localToAdelic3 p) _ _ (hsys.mem_doubleCoset i)
    rw [← hz, mul_assoc (x * localToAdelic3 p z) h g, hby]
    exact apply_mul_localToAdelic3_mul_eq hK z hb hy x
  have hcs : cosetSum reps f (x * b) = lam * f (x * b) := hT ι reps hsys (x * b)
  simp only [hterm]
  rw [← Finset.mul_sum, show (∑ i, f (x * b * reps i)) = cosetSum reps f (x * b) from rfl, hcs, mul_assoc x h g,
    hby, apply_mul_mul_localToAdelic3_eq hK b hy x]
  ring

private theorem isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator_of_integrable
    (lam1 lam2 : ℂ) (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hint : ∀ x : AdelicGL 3 (𝓞 ℚ) ℚ, Integrable (fun g => φ g * f (x * g)) haarGL3)
    (hφp : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, φ g ≠ 0 → componentAt3 (𝓞 ℚ) ℚ p g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p)
    (h : AdelicGL 3 (𝓞 ℚ) ℚ) (hh : componentAt3 (𝓞 ℚ) ℚ p h = 1)
    (hK : IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) f)
    (hT1 : IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen1 p)) f lam1)
    (hT2 : IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen2 p)) f lam2) :
    IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (SlabL2.translateRight h (SlabL2.smoothingOperator φ f)) ∧
    IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen1 p)) (SlabL2.translateRight h (SlabL2.smoothingOperator φ f)) lam1 ∧
    IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen2 p)) (SlabL2.translateRight h (SlabL2.smoothingOperator φ f)) lam2 :=
  ⟨isRightInvariant_of_forall hφp hh hK, isCosetEigenfunction_of_forall hint hφp hh hK hT1,
    isCosetEigenfunction_of_forall hint hφp hh hK hT2⟩

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator.SmoothingTranslation.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator.SmoothingTranslation.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator.SmoothingTranslation.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator.SmoothingTranslation.LanglandsTunnell.CubicInduction"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator.SmoothingTranslation.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator.SmoothingTranslation.LanglandsTunnell.CubicInduction"

end Commutation
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator.SmoothingTranslation.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator.SmoothingTranslation.LanglandsTunnell.CubicInduction"

section Assembly

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
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator.SmoothingTranslation.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator.SmoothingTranslation.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator.SmoothingTranslation.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator.SmoothingTranslation.LanglandsTunnell.CubicInduction"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator.SmoothingTranslation.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator.SmoothingTranslation.LanglandsTunnell.CubicInduction"

end Assembly
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator.SmoothingTranslation.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator.SmoothingTranslation.LanglandsTunnell.CubicInduction"

end SmoothingTranslation
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator.SmoothingTranslation.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator.SmoothingTranslation.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator.SmoothingTranslation"

open LanglandsTunnell.CubicInduction SmoothingTranslation.LanglandsTunnell.CubicInduction in
theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ)) (lam1 lam2 : ℂ)
    (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (_hφ : SlabL2.IsSmoothingKernel φ)
    (_hφp : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, φ g ≠ 0 → componentAt3 (𝓞 ℚ) ℚ p g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p)
    (h : AdelicGL 3 (𝓞 ℚ) ℚ) (_hh : componentAt3 (𝓞 ℚ) ℚ p h = 1)
    (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (_hc : Continuous f)
    (_hK : IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) f)
    (_hT1 : IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen1 p)) f lam1)
    (_hT2 : IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen2 p)) f lam2) :
    IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (SlabL2.translateRight h (SlabL2.smoothingOperator φ f)) ∧
    IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen1 p)) (SlabL2.translateRight h (SlabL2.smoothingOperator φ f)) lam1 ∧
    IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen2 p)) (SlabL2.translateRight h (SlabL2.smoothingOperator φ f)) lam2 :=
  isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator_of_integrable lam1 lam2 φ f
    (integrable_mul_of_isSmoothingKernel _hφ _hc) _hφp h _hh _hK _hT1 _hT2

#print axioms solution

end S_LanglandsTunnell_CubicInduction_isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator (solution)
