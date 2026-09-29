-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.gauge3_mul_le_of_isCompact_and_norm_smoothingOperator_le_gauge3_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/56b8dff7-dde4-5fef-ac2f-2d2dcf36ce16

import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Theorems.Thm_LanglandsTunnell_CubicInduction_isOpen_and_isCompact_setOf_forall_componentAt3_finEmbedN_mem
import Mathlib.Topology.Algebra.Valued.NormedValued
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_gauge3_mul_le_of_isCompact_and_norm_smoothingOperator_le_gauge3_pow

set_option autoImplicit false

open IsDedekindDomain NumberField

section PastedComponents
open Matrix IsDedekindDomain NumberField AutomorphicForm
noncomputable section
namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "SlabL2.realCoordinate SlabL2.IsSmoothingKernel SlabL2.smoothingOperator SlabL2.smoothingOperator_apply AdelicGL localMaximalCompact3 mem_localMaximalCompact3_iff componentAt3 archComponent3 archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 gauge3_pos one_le_archGauge3 matrixAdele_ext finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN finEmbedN isOpen_and_isCompact_setOf_forall_componentAt3_finEmbedN_mem"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"
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

end LanglandsTunnell.CubicInduction
end
end PastedComponents

section PastedArchFinNouns
open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory
noncomputable section
namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "SlabL2.realCoordinate SlabL2.IsSmoothingKernel SlabL2.smoothingOperator SlabL2.smoothingOperator_apply AdelicGL localMaximalCompact3 mem_localMaximalCompact3_iff componentAt3 archComponent3 archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 gauge3_pos one_le_archGauge3 matrixAdele_ext finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN finEmbedN isOpen_and_isCompact_setOf_forall_componentAt3_finEmbedN_mem"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

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

private def archEntries3 (a : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Fin 3 → Fin 3 → ℝ :=
  fun i j => SlabL2.realCoordinate ((a : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i j)

end LanglandsTunnell.CubicInduction
end
end PastedArchFinNouns

section PastedArchHalf
open NumberField Matrix
open scoped MatrixGroups
noncomputable section
namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "SlabL2.realCoordinate SlabL2.IsSmoothingKernel SlabL2.smoothingOperator SlabL2.smoothingOperator_apply AdelicGL localMaximalCompact3 mem_localMaximalCompact3_iff componentAt3 archComponent3 archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 gauge3_pos one_le_archGauge3 matrixAdele_ext finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN finEmbedN isOpen_and_isCompact_setOf_forall_componentAt3_finEmbedN_mem"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"
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

private theorem continuous_comp_archEntries3 {α : (Fin 3 → Fin 3 → ℝ) → ℂ} (hα : IsSmoothArchFactor α) :
    Continuous fun a => α (archEntries3 a) :=
  (hα.1.continuous).comp continuous_archEntries3

end LanglandsTunnell.CubicInduction
end
end PastedArchHalf

section PastedKernelFurniture
open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory
open scoped MatrixGroups
namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "SlabL2.realCoordinate SlabL2.IsSmoothingKernel SlabL2.smoothingOperator SlabL2.smoothingOperator_apply AdelicGL localMaximalCompact3 mem_localMaximalCompact3_iff componentAt3 archComponent3 archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 gauge3_pos one_le_archGauge3 matrixAdele_ext finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN finEmbedN isOpen_and_isCompact_setOf_forall_componentAt3_finEmbedN_mem"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

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

end LanglandsTunnell.CubicInduction
end PastedKernelFurniture

section PastedFinPart
p2m_open "NumberField IsDedekindDomain LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_gauge3_mul_le_of_isCompact_and_norm_smoothingOperator_le_gauge3_pow.LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2"

private theorem continuous_generalLinearGroup_map_fin3 {A B : Type*} [CommRing A] [CommRing B] [TopologicalSpace A]
    [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B] (f : A →+* B) (hf : Continuous f) :
    Continuous (Matrix.GeneralLinearGroup.map (n := Fin 3) f) :=
  Continuous.units_map _ ((continuous_id.matrix_map hf) :
    Continuous fun m : Matrix (Fin 3) (Fin 3) A => m.map f)

private noncomputable def finPart3 : AdelicGL 3 (𝓞 ℚ) ℚ →* GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  Matrix.GeneralLinearGroup.map (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)

private theorem coe_finEmbedN3 (k : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    ((finEmbedN (Fin 3) (𝓞 ℚ) ℚ k : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      finMatN (Fin 3) (𝓞 ℚ) ℚ (k : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  rfl

private theorem coe_finPart3 (x : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ((finPart3 x : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) =
      (AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (x : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
  rfl

private theorem componentAt3_finEmbedN_finPart3 (x : AdelicGL 3 (𝓞 ℚ) ℚ)
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
    componentAt3 (𝓞 ℚ) ℚ p (finEmbedN (Fin 3) (𝓞 ℚ) ℚ (finPart3 x)) = componentAt3 (𝓞 ℚ) ℚ p x := by
  apply Units.ext
  simp only [coe_componentAt3, ← RingHom.mapMatrix_comp, RingHom.comp_apply, coe_finEmbedN3, coe_finPart3,
    mapMatrix_fin_finMatN]

private theorem archToAdelic3_archComponent3_mul_finEmbedN_finPart3 (x : AdelicGL 3 (𝓞 ℚ) ℚ) :
    archToAdelic3 (archComponent3 (𝓞 ℚ) ℚ x) * finEmbedN (Fin 3) (𝓞 ℚ) ℚ (finPart3 x) = x := by
  apply Units.ext
  rw [Units.val_mul, coe_archToAdelic3, coe_finEmbedN3]
  refine matrixAdele_ext (Fin 3) (𝓞 ℚ) ℚ ?_ ?_
  · rw [map_mul, mapMatrix_arch_archMat3, mapMatrix_arch_finMatN, mul_one, coe_archComponent3]
  · rw [map_mul, mapMatrix_fin_archMat3, mapMatrix_fin_finMatN, one_mul, coe_finPart3]
end PastedFinPart

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "SlabL2.realCoordinate SlabL2.IsSmoothingKernel SlabL2.smoothingOperator SlabL2.smoothingOperator_apply AdelicGL localMaximalCompact3 mem_localMaximalCompact3_iff componentAt3 archComponent3 archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 gauge3_pos one_le_archGauge3 matrixAdele_ext finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN finEmbedN isOpen_and_isCompact_setOf_forall_componentAt3_finEmbedN_mem"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section GaugeIntegral

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum AutomorphicForm
open scoped NNReal

section GaugeIntegral1

variable {L : Type*} [NormedField L] [IsUltrametricDist L]

omit [IsUltrametricDist L] in
private theorem nnnorm_entry_le_matrixSupSize (k : GL (Fin 3) L) (i j : Fin 3) :
    ‖(k : Matrix (Fin 3) (Fin 3) L) i j‖₊ ≤ matrixSupSize k :=
  (le_max_left _ _).trans (Finset.le_sup (f := fun ij : Fin 3 × Fin 3 =>
    max ‖(k : Matrix (Fin 3) (Fin 3) L) ij.1 ij.2‖₊ ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) ij.1 ij.2‖₊)
    (Finset.mem_univ (i, j)))

omit [IsUltrametricDist L] in
private theorem nnnorm_inv_entry_le_matrixSupSize (k : GL (Fin 3) L) (i j : Fin 3) :
    ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖₊ ≤ matrixSupSize k :=
  (le_max_right _ _).trans (Finset.le_sup (f := fun ij : Fin 3 × Fin 3 =>
    max ‖(k : Matrix (Fin 3) (Fin 3) L) ij.1 ij.2‖₊ ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) ij.1 ij.2‖₊)
    (Finset.mem_univ (i, j)))

private theorem matrixSupSize_mul_le_of_forall_nnnorm_le_one (g k : GL (Fin 3) L)
    (hk : ∀ i j, ‖(k : Matrix (Fin 3) (Fin 3) L) i j‖₊ ≤ 1)
    (hk' : ∀ i j, ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖₊ ≤ 1) :
    matrixSupSize (g * k) ≤ matrixSupSize g := by
  change Finset.univ.sup (fun ij : Fin 3 × Fin 3 =>
    max ‖((g * k : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) ij.1 ij.2‖₊
      ‖(((g * k)⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) ij.1 ij.2‖₊) ≤ matrixSupSize g
  refine Finset.sup_le fun ij _ => max_le ?_ ?_
  · rw [Units.val_mul, Matrix.mul_apply]
    refine IsUltrametricDist.nnnorm_sum_le_of_forall_le fun l _ => ?_
    calc ‖(g : Matrix (Fin 3) (Fin 3) L) ij.1 l * (k : Matrix (Fin 3) (Fin 3) L) l ij.2‖₊
        ≤ ‖(g : Matrix (Fin 3) (Fin 3) L) ij.1 l‖₊ * ‖(k : Matrix (Fin 3) (Fin 3) L) l ij.2‖₊ := nnnorm_mul_le _ _
      _ ≤ matrixSupSize g * 1 := mul_le_mul' (nnnorm_entry_le_matrixSupSize g _ _) (hk _ _)
      _ = matrixSupSize g := mul_one _
  · rw [mul_inv_rev, Units.val_mul, Matrix.mul_apply]
    refine IsUltrametricDist.nnnorm_sum_le_of_forall_le fun l _ => ?_
    calc ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) ij.1 l *
          ((g⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) l ij.2‖₊
        ≤ ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) ij.1 l‖₊ *
          ‖((g⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) l ij.2‖₊ := nnnorm_mul_le _ _
      _ ≤ 1 * matrixSupSize g := mul_le_mul' (hk' _ _) (nnnorm_inv_entry_le_matrixSupSize g _ _)
      _ = matrixSupSize g := one_mul _

private theorem matrixSupSize_mul_of_forall_nnnorm_le_one (g k : GL (Fin 3) L)
    (hk : ∀ i j, ‖(k : Matrix (Fin 3) (Fin 3) L) i j‖₊ ≤ 1)
    (hk' : ∀ i j, ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖₊ ≤ 1) :
    matrixSupSize (g * k) = matrixSupSize g := by
  refine le_antisymm (matrixSupSize_mul_le_of_forall_nnnorm_le_one g k hk hk') ?_
  have h := matrixSupSize_mul_le_of_forall_nnnorm_le_one (g * k) k⁻¹ hk' (by simpa only [inv_inv] using hk)
  rwa [mul_inv_cancel_right] at h

end GaugeIntegral1

section GaugeIntegral2

variable (v : HeightOneSpectrum (𝓞 ℚ))

example : IsUltrametricDist (v.adicCompletion ℚ) := inferInstance

private theorem nnnorm_entry_le_one_of_mem_localMaximalCompact3 {k : GL (Fin 3) (v.adicCompletion ℚ)}
    (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) (i j : Fin 3) :
    ‖(k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j‖₊ ≤ 1 := by
  rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
  exact Valued.toNormedField.norm_le_one_iff.mpr (((mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ v).mp hk).1 i j)

private theorem nnnorm_inv_entry_le_one_of_mem_localMaximalCompact3 {k : GL (Fin 3) (v.adicCompletion ℚ)}
    (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) (i j : Fin 3) :
    ‖((k⁻¹ : GL (Fin 3) (v.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j‖₊ ≤ 1 := by
  rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
  exact Valued.toNormedField.norm_le_one_iff.mpr (((mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ v).mp hk).2 i j)

private theorem matrixSupSize_mul_of_mem_localMaximalCompact3 (g : GL (Fin 3) (v.adicCompletion ℚ))
    {k : GL (Fin 3) (v.adicCompletion ℚ)} (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    matrixSupSize (g * k) = matrixSupSize g :=
  matrixSupSize_mul_of_forall_nnnorm_le_one g k (nnnorm_entry_le_one_of_mem_localMaximalCompact3 v hk)
    (nnnorm_inv_entry_le_one_of_mem_localMaximalCompact3 v hk)

end GaugeIntegral2

end

end GaugeIntegral

section GaugeArchimedean

open Matrix IsDedekindDomain NumberField AutomorphicForm

noncomputable section

section GaugeArchimedean2

variable {L : Type*} [NormedField L]

private theorem norm_entry_le_matrixSize (k : GL (Fin 3) L) (i j : Fin 3) :
    ‖(k : Matrix (Fin 3) (Fin 3) L) i j‖ ≤ matrixSize k := by
  have hrow : ‖(k : Matrix (Fin 3) (Fin 3) L) i j‖ + ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖ ≤
      ∑ j' : Fin 3,
        (‖(k : Matrix (Fin 3) (Fin 3) L) i j'‖ + ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j'‖) :=
    Finset.single_le_sum
      (f := fun j' => ‖(k : Matrix (Fin 3) (Fin 3) L) i j'‖ +
        ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j'‖)
      (fun _ _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) (Finset.mem_univ j)
  have hall : (∑ j' : Fin 3,
      (‖(k : Matrix (Fin 3) (Fin 3) L) i j'‖ + ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j'‖)) ≤
      matrixSize k :=
    Finset.single_le_sum
      (f := fun i' => ∑ j' : Fin 3,
        (‖(k : Matrix (Fin 3) (Fin 3) L) i' j'‖ + ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i' j'‖))
      (fun _ _ => Finset.sum_nonneg fun _ _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) (Finset.mem_univ i)
  have hinv : 0 ≤ ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖ := norm_nonneg _
  linarith

private theorem norm_inv_entry_le_matrixSize (k : GL (Fin 3) L) (i j : Fin 3) :
    ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖ ≤ matrixSize k := by
  have hrow : ‖(k : Matrix (Fin 3) (Fin 3) L) i j‖ + ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖ ≤
      ∑ j' : Fin 3,
        (‖(k : Matrix (Fin 3) (Fin 3) L) i j'‖ + ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j'‖) :=
    Finset.single_le_sum
      (f := fun j' => ‖(k : Matrix (Fin 3) (Fin 3) L) i j'‖ +
        ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j'‖)
      (fun _ _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) (Finset.mem_univ j)
  have hall : (∑ j' : Fin 3,
      (‖(k : Matrix (Fin 3) (Fin 3) L) i j'‖ + ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j'‖)) ≤
      matrixSize k :=
    Finset.single_le_sum
      (f := fun i' => ∑ j' : Fin 3,
        (‖(k : Matrix (Fin 3) (Fin 3) L) i' j'‖ + ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i' j'‖))
      (fun _ _ => Finset.sum_nonneg fun _ _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) (Finset.mem_univ i)
  have hent : 0 ≤ ‖(k : Matrix (Fin 3) (Fin 3) L) i j‖ := norm_nonneg _
  linarith

private theorem norm_mul_entry_le {A B : Matrix (Fin 3) (Fin 3) L} {a b : ℝ} (ha : 0 ≤ a)
    (hA : ∀ i j, ‖A i j‖ ≤ a) (hB : ∀ i j, ‖B i j‖ ≤ b) (i j : Fin 3) : ‖(A * B) i j‖ ≤ 3 * (a * b) := by
  rw [Matrix.mul_apply]
  calc ‖∑ m : Fin 3, A i m * B m j‖ ≤ ∑ m : Fin 3, ‖A i m * B m j‖ := norm_sum_le _ _
    _ ≤ ∑ _m : Fin 3, a * b := by
        refine Finset.sum_le_sum fun m _ => ?_
        rw [norm_mul]
        exact mul_le_mul (hA i m) (hB m j) (norm_nonneg _) ha
    _ = 3 * (a * b) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]

private theorem matrixSize_mul_le (k l : GL (Fin 3) L) : matrixSize (k * l) ≤ 54 * (matrixSize k * matrixSize l) := by
  have hk : 0 ≤ matrixSize k := matrixSize_nonneg k
  have hl : 0 ≤ matrixSize l := matrixSize_nonneg l
  have hprod : ((k * l : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
      (k : Matrix (Fin 3) (Fin 3) L) * (l : Matrix (Fin 3) (Fin 3) L) := rfl
  have hprodinv : (((k * l)⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
      ((l⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) * ((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) := rfl
  have hentry : ∀ i j : Fin 3,
      ‖((k * l : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖ ≤ 3 * (matrixSize k * matrixSize l) := by
    intro i j
    rw [hprod]
    exact norm_mul_entry_le hk (norm_entry_le_matrixSize k) (norm_entry_le_matrixSize l) i j
  have hinventry : ∀ i j : Fin 3,
      ‖(((k * l)⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖ ≤ 3 * (matrixSize l * matrixSize k) := by
    intro i j
    rw [hprodinv]
    exact norm_mul_entry_le hl (norm_inv_entry_le_matrixSize l) (norm_inv_entry_le_matrixSize k) i j
  have hterm : ∀ i j : Fin 3,
      ‖((k * l : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖ +
        ‖(((k * l)⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖ ≤ 6 * (matrixSize k * matrixSize l) := by
    intro i j
    have h1 := hentry i j
    have h2 := hinventry i j
    rw [mul_comm (matrixSize l) (matrixSize k)] at h2
    linarith
  calc matrixSize (k * l)
      = ∑ i : Fin 3, ∑ j : Fin 3,
          (‖((k * l : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖ +
            ‖(((k * l)⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖) := rfl
    _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, 6 * (matrixSize k * matrixSize l) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = 54 * (matrixSize k * matrixSize l) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
        ring

private theorem continuous_matrixSize : Continuous (matrixSize (L := L)) := by
  unfold matrixSize
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact ((Units.continuous_val.matrix_elem i j).norm).add ((Units.continuous_coe_inv.matrix_elem i j).norm)

end GaugeArchimedean2

section GaugeArchimedean3

variable (F : Type) [Field F] [NumberField F]

private def archTranslateConst (h : AdelicGL 3 (𝓞 F) F) : ℝ :=
  1 + 54 * ∑ w : InfinitePlace F, matrixSize (archPlaceComponent3 F w h)

private theorem one_le_archTranslateConst (h : AdelicGL 3 (𝓞 F) F) : 1 ≤ archTranslateConst F h := by
  unfold archTranslateConst
  have hsum : 0 ≤ ∑ w : InfinitePlace F, matrixSize (archPlaceComponent3 F w h) :=
    Finset.sum_nonneg fun w _ => matrixSize_nonneg _
  linarith

private theorem archGauge3_mul_le (g h : AdelicGL 3 (𝓞 F) F) :
    archGauge3 F (g * h) ≤ archTranslateConst F h * archGauge3 F g := by
  set M : ℝ := ∑ w : InfinitePlace F, matrixSize (archPlaceComponent3 F w h) with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun w _ => matrixSize_nonneg _
  have hX0 : 0 ≤ ∑ w : InfinitePlace F, matrixSize (archPlaceComponent3 F w g) :=
    Finset.sum_nonneg fun w _ => matrixSize_nonneg _
  have hterm : ∀ w : InfinitePlace F, matrixSize (archPlaceComponent3 F w (g * h)) ≤
      54 * M * matrixSize (archPlaceComponent3 F w g) := by
    intro w
    rw [map_mul]
    have h1 := matrixSize_mul_le (archPlaceComponent3 F w g) (archPlaceComponent3 F w h)
    have h2 : matrixSize (archPlaceComponent3 F w h) ≤ M :=
      Finset.single_le_sum (f := fun w' => matrixSize (archPlaceComponent3 F w' h))
        (fun _ _ => matrixSize_nonneg _) (Finset.mem_univ w)
    have h3 : 0 ≤ matrixSize (archPlaceComponent3 F w g) := matrixSize_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left h2 h3]
  have hsum : ∑ w : InfinitePlace F, matrixSize (archPlaceComponent3 F w (g * h)) ≤
      54 * M * ∑ w : InfinitePlace F, matrixSize (archPlaceComponent3 F w g) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun w _ => hterm w
  unfold archGauge3 archTranslateConst
  rw [← hM]
  nlinarith [hsum, hM0, hX0, mul_nonneg hM0 hX0]

private theorem finGauge3_nonneg (g : AdelicGL 3 (𝓞 F) F) : 0 ≤ finGauge3 F g :=
  finprod_nonneg fun _ => NNReal.coe_nonneg _

private theorem gauge3_mul_le (g h : AdelicGL 3 (𝓞 F) F) {C : ℝ} (hC : 1 ≤ C)
    (hfin : finGauge3 F (g * h) ≤ C * finGauge3 F g) :
    gauge3 F (g * h) ≤ (archTranslateConst F h * C) * gauge3 F g := by
  have hA := archGauge3_mul_le F g h
  have hA0 : 0 ≤ archGauge3 F g := zero_le_one.trans (one_le_archGauge3 F g)
  have hcA1 : 1 ≤ archTranslateConst F h := one_le_archTranslateConst F h
  have hcA0 : 0 ≤ archTranslateConst F h := zero_le_one.trans hcA1
  have hFi0 : 0 ≤ finGauge3 F (g * h) := finGauge3_nonneg F (g * h)
  have hc1 : 1 ≤ archTranslateConst F h * C := by nlinarith [hcA1, hC]
  have hc0 : 0 ≤ archTranslateConst F h * C := zero_le_one.trans hc1
  have hmain : archGauge3 F (g * h) * finGauge3 F (g * h) ≤
      (archTranslateConst F h * C) * (archGauge3 F g * finGauge3 F g) := by
    calc archGauge3 F (g * h) * finGauge3 F (g * h)
        ≤ (archTranslateConst F h * archGauge3 F g) * (C * finGauge3 F g) :=
          mul_le_mul hA hfin hFi0 (mul_nonneg hcA0 hA0)
      _ = (archTranslateConst F h * C) * (archGauge3 F g * finGauge3 F g) := by ring
  unfold gauge3
  refine max_le ?_ ?_
  · calc (1 : ℝ) ≤ (archTranslateConst F h * C) * 1 := by rw [mul_one]; exact hc1
      _ ≤ (archTranslateConst F h * C) * max 1 (archGauge3 F g * finGauge3 F g) :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) hc0
  · calc archGauge3 F (g * h) * finGauge3 F (g * h)
        ≤ (archTranslateConst F h * C) * (archGauge3 F g * finGauge3 F g) := hmain
      _ ≤ (archTranslateConst F h * C) * max 1 (archGauge3 F g * finGauge3 F g) :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) hc0

private theorem continuous_archTranslateConst_comp {X : Type*} [TopologicalSpace X] {τ : X → AdelicGL 3 (𝓞 F) F}
    (hτ : ∀ w : InfinitePlace F, Continuous fun x => archPlaceComponent3 F w (τ x)) :
    Continuous fun x => archTranslateConst F (τ x) := by
  unfold archTranslateConst
  exact continuous_const.add (continuous_const.mul
    (continuous_finsetSum _ fun w _ => continuous_matrixSize.comp (hτ w)))

private theorem exists_archTranslateConst_le_of_isCompact {X : Type*} [TopologicalSpace X] {T : Set X}
    (hT : IsCompact T) {τ : X → AdelicGL 3 (𝓞 F) F}
    (hτ : ∀ w : InfinitePlace F, Continuous fun x => archPlaceComponent3 F w (τ x)) :
    ∃ K : ℝ, ∀ x ∈ T, archTranslateConst F (τ x) ≤ K := by
  obtain ⟨K, hK⟩ := (hT.image_of_continuousOn (continuous_archTranslateConst_comp F hτ).continuousOn).bddAbove
  exact ⟨K, fun x hx => hK ⟨x, hx, rfl⟩⟩

end GaugeArchimedean3

end

end GaugeArchimedean

section GaugeSinglePlace

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NNReal

section GaugeSinglePlace1

variable {L : Type*} [NormedField L]

private theorem nnnorm_entry_le_matrixSupSize' (k : GL (Fin 3) L) (i j : Fin 3) :
    ‖(k : Matrix (Fin 3) (Fin 3) L) i j‖₊ ≤ matrixSupSize k :=
  (le_max_left _ _).trans (Finset.le_sup (f := fun ij : Fin 3 × Fin 3 =>
    max ‖(k : Matrix (Fin 3) (Fin 3) L) ij.1 ij.2‖₊ ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) ij.1 ij.2‖₊)
    (Finset.mem_univ (i, j)))

private theorem nnnorm_inv_entry_le_matrixSupSize' (k : GL (Fin 3) L) (i j : Fin 3) :
    ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖₊ ≤ matrixSupSize k :=
  (le_max_right _ _).trans (Finset.le_sup (f := fun ij : Fin 3 × Fin 3 =>
    max ‖(k : Matrix (Fin 3) (Fin 3) L) ij.1 ij.2‖₊ ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) ij.1 ij.2‖₊)
    (Finset.mem_univ (i, j)))

private theorem matrixSupSize_mul_le' [IsUltrametricDist L] (g k : GL (Fin 3) L) :
    matrixSupSize (g * k) ≤ matrixSupSize g * matrixSupSize k := by
  change Finset.univ.sup (fun ij : Fin 3 × Fin 3 =>
    max ‖((g * k : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) ij.1 ij.2‖₊
      ‖(((g * k)⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) ij.1 ij.2‖₊) ≤ matrixSupSize g * matrixSupSize k
  refine Finset.sup_le fun ij _ => max_le ?_ ?_
  · rw [Units.val_mul, Matrix.mul_apply]
    refine IsUltrametricDist.nnnorm_sum_le_of_forall_le fun l _ => ?_
    calc ‖(g : Matrix (Fin 3) (Fin 3) L) ij.1 l * (k : Matrix (Fin 3) (Fin 3) L) l ij.2‖₊
        ≤ ‖(g : Matrix (Fin 3) (Fin 3) L) ij.1 l‖₊ * ‖(k : Matrix (Fin 3) (Fin 3) L) l ij.2‖₊ := nnnorm_mul_le _ _
      _ ≤ matrixSupSize g * matrixSupSize k :=
          mul_le_mul' (nnnorm_entry_le_matrixSupSize' g _ _) (nnnorm_entry_le_matrixSupSize' k _ _)
  · rw [mul_inv_rev, Units.val_mul, Matrix.mul_apply]
    refine IsUltrametricDist.nnnorm_sum_le_of_forall_le fun l _ => ?_
    calc ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) ij.1 l *
          ((g⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) l ij.2‖₊
        ≤ ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) ij.1 l‖₊ *
          ‖((g⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) l ij.2‖₊ := nnnorm_mul_le _ _
      _ ≤ matrixSupSize k * matrixSupSize g :=
          mul_le_mul' (nnnorm_inv_entry_le_matrixSupSize' k _ _) (nnnorm_inv_entry_le_matrixSupSize' g _ _)
      _ = matrixSupSize g * matrixSupSize k := mul_comm _ _

end GaugeSinglePlace1

section GaugeSinglePlace2

private theorem finprod_le_mul_finprod_of_eq_off {ι : Type*} (f f' : ι → ℝ) (v : ι) {c : ℝ} (hc : 1 ≤ c)
    (h0 : ∀ w, 0 ≤ f w) (heq : ∀ w, w ≠ v → f' w = f w) (hv : f' v ≤ c * f v) :
    ∏ᶠ w, f' w ≤ c * ∏ᶠ w, f w := by
  classical
  have hsub : Function.mulSupport f' ⊆ Function.mulSupport f ∪ {v} := by
    intro w hw
    by_cases hwv : w = v
    · exact Or.inr (by simp [hwv])
    · exact Or.inl (by simpa only [Function.mem_mulSupport, heq w hwv] using hw)
  have hsub' : Function.mulSupport f ⊆ Function.mulSupport f' ∪ {v} := by
    intro w hw
    by_cases hwv : w = v
    · exact Or.inr (by simp [hwv])
    · exact Or.inl (by simpa only [Function.mem_mulSupport, heq w hwv] using hw)
  by_cases hfin : (Function.mulSupport f).Finite
  · have hfin' : (Function.mulSupport f').Finite := (hfin.union (Set.finite_singleton v)).subset hsub
    set s : Finset ι := (hfin.union (Set.finite_singleton v)).toFinset with hs
    have hvs : v ∈ s := by simp [hs]
    have hfs : Function.mulSupport f ⊆ ↑s := by
      intro w hw
      simp only [hs, Set.Finite.coe_toFinset]
      exact Or.inl hw
    have hfs' : Function.mulSupport f' ⊆ ↑s := by
      intro w hw
      simp only [hs, Set.Finite.coe_toFinset]
      exact hsub hw
    rw [finprod_eq_prod_of_mulSupport_subset f hfs, finprod_eq_prod_of_mulSupport_subset f' hfs',
      ← Finset.mul_prod_erase s f' hvs, ← Finset.mul_prod_erase s f hvs]
    have hrest : ∏ w ∈ s.erase v, f' w = ∏ w ∈ s.erase v, f w :=
      Finset.prod_congr rfl fun w hw => heq w (Finset.ne_of_mem_erase hw)
    have hrest0 : 0 ≤ ∏ w ∈ s.erase v, f w := Finset.prod_nonneg fun w _ => h0 w
    rw [hrest, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hv hrest0
  · have hinf' : ¬ (Function.mulSupport f').Finite := fun hfin' =>
      hfin ((hfin'.union (Set.finite_singleton v)).subset hsub')
    rw [finprod_of_infinite_mulSupport hfin, finprod_of_infinite_mulSupport hinf', mul_one]
    exact hc

end GaugeSinglePlace2

end

end GaugeSinglePlace

section PackageBody

noncomputable section

p2m_open "NumberField IsDedekindDomain AutomorphicForm MeasureTheory LanglandsTunnell.CubicInduction.SlabL2"
open scoped NNReal ENNReal MatrixGroups Pointwise

attribute [local instance] NumberField.AdelicHaar.glBorel

private theorem finprod_le_mul_finprod_of_eq_off_finset {ι : Type*} [DecidableEq ι] (f f' : ι → ℝ)
    (E : Finset ι) (c : ι → ℝ) (hc : ∀ v, 1 ≤ c v) (h0 : ∀ w, 0 ≤ f w) (h0' : ∀ w, 0 ≤ f' w)
    (heq : ∀ w, w ∉ E → f' w = f w) (hE : ∀ v ∈ E, f' v ≤ c v * f v) :
    ∏ᶠ w, f' w ≤ (∏ v ∈ E, c v) * ∏ᶠ w, f w := by
  induction E using Finset.induction_on generalizing f' with
  | empty =>
    have hf : f' = f := funext fun w => heq w (Finset.notMem_empty w)
    rw [hf, Finset.prod_empty, one_mul]
  | @insert v S hvS ih =>
    set f'' : ι → ℝ := fun w => if w = v then f w else f' w with hf''
    have h0'' : ∀ w, 0 ≤ f'' w := fun w => by
      by_cases hw : w = v
      · simp only [hf'', hw, if_true]; exact h0 v
      · simp only [hf'', hw, if_false]; exact h0' w
    have heq'' : ∀ w, w ∉ S → f'' w = f w := fun w hw => by
      by_cases hwv : w = v
      · simp only [hf'', hwv, if_true]
      · have hwE : w ∉ insert v S := fun hmem => (Finset.mem_insert.mp hmem).elim hwv hw
        simp only [hf'', hwv, if_false]
        exact heq w hwE
    have hS'' : ∀ w ∈ S, f'' w ≤ c w * f w := fun w hw => by
      have hwv : w ≠ v := fun hwv => hvS (hwv ▸ hw)
      simp only [hf'', hwv, if_false]
      exact hE w (Finset.mem_insert_of_mem hw)
    have h1 : ∏ᶠ w, f' w ≤ c v * ∏ᶠ w, f'' w := by
      refine finprod_le_mul_finprod_of_eq_off f'' f' v (hc v) h0'' (fun w hwv => ?_) ?_
      · simp only [hf'', hwv, if_false]
      · simp only [hf'', if_true]
        exact hE v (Finset.mem_insert_self v S)
    have h2 : ∏ᶠ w, f'' w ≤ (∏ w ∈ S, c w) * ∏ᶠ w, f w := ih f'' h0'' heq'' hS''
    have hcv : 0 ≤ c v := zero_le_one.trans (hc v)
    calc ∏ᶠ w, f' w ≤ c v * ∏ᶠ w, f'' w := h1
      _ ≤ c v * ((∏ w ∈ S, c w) * ∏ᶠ w, f w) := mul_le_mul_of_nonneg_left h2 hcv
      _ = (∏ w ∈ insert v S, c w) * ∏ᶠ w, f w := by rw [Finset.prod_insert hvS, mul_assoc]

private theorem finGauge3_mul_le_of_forall_notMem (g h : AdelicGL 3 (𝓞 ℚ) ℚ)
    (E : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hh : ∀ w, w ∉ E → componentAt3 (𝓞 ℚ) ℚ w h ∈ localMaximalCompact3 (𝓞 ℚ) ℚ w) :
    finGauge3 ℚ (g * h) ≤
      (∏ v ∈ E, max 1 ((matrixSupSize (componentAt3 (𝓞 ℚ) ℚ v h) : ℝ≥0) : ℝ)) * finGauge3 ℚ g := by
  classical
  unfold finGauge3
  refine finprod_le_mul_finprod_of_eq_off_finset
    (fun w : HeightOneSpectrum (𝓞 ℚ) => ((matrixSupSize (componentAt3 (𝓞 ℚ) ℚ w g) : ℝ≥0) : ℝ))
    (fun w : HeightOneSpectrum (𝓞 ℚ) => ((matrixSupSize (componentAt3 (𝓞 ℚ) ℚ w (g * h)) : ℝ≥0) : ℝ))
    E _ (fun _ => le_max_left _ _) (fun _ => NNReal.coe_nonneg _) (fun _ => NNReal.coe_nonneg _) ?_ ?_
  · intro w hw
    simp only [map_mul, matrixSupSize_mul_of_mem_localMaximalCompact3 w _ (hh w hw)]
  · intro v _
    simp only [map_mul]
    have h1 : ((matrixSupSize (componentAt3 (𝓞 ℚ) ℚ v g * componentAt3 (𝓞 ℚ) ℚ v h) : ℝ≥0) : ℝ) ≤
        ((matrixSupSize (componentAt3 (𝓞 ℚ) ℚ v g) : ℝ≥0) : ℝ) *
          ((matrixSupSize (componentAt3 (𝓞 ℚ) ℚ v h) : ℝ≥0) : ℝ) := by
      rw [← NNReal.coe_mul]
      exact NNReal.coe_le_coe.mpr (matrixSupSize_mul_le' _ _)
    calc ((matrixSupSize (componentAt3 (𝓞 ℚ) ℚ v g * componentAt3 (𝓞 ℚ) ℚ v h) : ℝ≥0) : ℝ)
        ≤ ((matrixSupSize (componentAt3 (𝓞 ℚ) ℚ v g) : ℝ≥0) : ℝ) *
            ((matrixSupSize (componentAt3 (𝓞 ℚ) ℚ v h) : ℝ≥0) : ℝ) := h1
      _ ≤ ((matrixSupSize (componentAt3 (𝓞 ℚ) ℚ v g) : ℝ≥0) : ℝ) *
            max 1 ((matrixSupSize (componentAt3 (𝓞 ℚ) ℚ v h) : ℝ≥0) : ℝ) :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) (NNReal.coe_nonneg _)
      _ = max 1 ((matrixSupSize (componentAt3 (𝓞 ℚ) ℚ v h) : ℝ≥0) : ℝ) *
            ((matrixSupSize (componentAt3 (𝓞 ℚ) ℚ v g) : ℝ≥0) : ℝ) := mul_comm _ _

private theorem continuous_componentAt3 (v : HeightOneSpectrum (𝓞 ℚ)) :
    Continuous (componentAt3 (𝓞 ℚ) ℚ v) :=
  continuous_generalLinearGroup_map_fin3 _
    ((AdelicLevel.continuous_finAdeleEval (𝓞 ℚ) ℚ v).comp (AdelicLevel.continuous_adeleFin (𝓞 ℚ) ℚ))

private theorem continuous_archComponent3' : Continuous (archComponent3 (𝓞 ℚ) ℚ) :=
  continuous_generalLinearGroup_map_fin3 _ (AdelicLevel.continuous_adeleArch (𝓞 ℚ) ℚ)

private theorem continuous_archPlaceComponent3 (w : InfinitePlace ℚ) :
    Continuous (archPlaceComponent3 ℚ w) :=
  (continuous_generalLinearGroup_map_fin3 _ (AdelicLevel.continuous_archEval ℚ w)).comp
    continuous_archComponent3'

private theorem continuous_and_hasCompactSupport_of_isSmoothingKernel (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hφ : IsSmoothingKernel φ) : Continuous φ ∧ HasCompactSupport φ := by
  obtain ⟨α, K', hα, hK, hcof, hform⟩ := hφ
  have hopen : ∀ p, IsOpen (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ))) := fun p => (hK p).1
  have hcpt : ∀ p, IsCompact (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ))) := fun p => (hK p).2
  set S : Set (AdelicGL 3 (𝓞 ℚ) ℚ) := {x | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p} with hS
  have hφeq : φ = fun g => α (archEntries g) * S.indicator (fun _ => (1 : ℂ)) g := funext hform

  have hfin : Continuous finPart3 :=
    continuous_generalLinearGroup_map_fin3 _ (AdelicLevel.continuous_adeleFin (𝓞 ℚ) ℚ)
  have harchc : Continuous (archComponent3 (𝓞 ℚ) ℚ) :=
    continuous_generalLinearGroup_map_fin3 _ (AdelicLevel.continuous_adeleArch (𝓞 ℚ) ℚ)
  have hcompc : ∀ p, Continuous (componentAt3 (𝓞 ℚ) ℚ p) := fun p =>
    continuous_generalLinearGroup_map_fin3 _
      ((AdelicLevel.continuous_finAdeleEval (𝓞 ℚ) ℚ p).comp (AdelicLevel.continuous_adeleFin (𝓞 ℚ) ℚ))

  have hlevel := isOpen_and_isCompact_setOf_forall_componentAt3_finEmbedN_mem K' hopen hcpt hcof
  have hSpre : S = finPart3 ⁻¹' {k : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ) |
      ∀ p, componentAt3 (𝓞 ℚ) ℚ p (finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) ∈ K' p} := by
    ext x
    simp only [hS, Set.mem_setOf_eq, Set.mem_preimage, componentAt3_finEmbedN_finPart3]
  have hSopen : IsOpen S := by
    rw [hSpre]
    exact hlevel.1.preimage hfin
  have hSclosed : IsClosed S := by
    rw [hS, Set.setOf_forall]
    exact isClosed_iInter fun p => ((K' p).isClosed_of_isOpen (hopen p)).preimage (hcompc p)

  have harch : Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ => α (archEntries g) :=
    (continuous_comp_archEntries3 hα).comp harchc
  refine ⟨?_, ?_⟩
  · rw [hφeq]
    exact harch.mul (IsClopen.continuous_indicator ⟨hSclosed, hSopen⟩ continuous_const)
  ·
    haveI : T2Space (Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
      inferInstanceAs (T2Space (Fin 3 → Fin 3 → AdeleRing (𝓞 ℚ) ℚ))
    have hA : IsCompact (archEntries3 ⁻¹' tsupport α) := isCompact_preimage_archEntries3 hα.2.1 hα.2.2
    have hL := hlevel.2
    have hm : Continuous fun q : GL (Fin 3) (InfiniteAdeleRing ℚ) × GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ) =>
        archToAdelic3 q.1 * finEmbedN (Fin 3) (𝓞 ℚ) ℚ q.2 :=
      (continuous_archToAdelic3.comp continuous_fst).mul (continuous_finEmbedN3.comp continuous_snd)
    refine HasCompactSupport.of_support_subset_isCompact ((hA.prod hL).image hm) ?_
    intro x hx
    rw [Function.mem_support, hform x] at hx
    have h1 : α (archEntries x) ≠ 0 := left_ne_zero_of_mul hx
    have hxS : x ∈ S := Set.mem_of_indicator_ne_zero (right_ne_zero_of_mul hx)
    refine ⟨(archComponent3 (𝓞 ℚ) ℚ x, finPart3 x), ⟨?_, ?_⟩, archToAdelic3_archComponent3_mul_finEmbedN_finPart3 x⟩
    · exact subset_tsupport α h1
    · rw [hSpre] at hxS
      exact hxS

private theorem coe_matrixSupSize_le_matrixSize {L : Type*} [NormedField L] (k : GL (Fin 3) L) :
    ((matrixSupSize k : ℝ≥0) : ℝ) ≤ matrixSize k := by
  have h : matrixSupSize k ≤ ⟨matrixSize k, matrixSize_nonneg k⟩ := by
    unfold matrixSupSize
    refine Finset.sup_le fun ij _ => max_le ?_ ?_
    · rw [← NNReal.coe_le_coe, coe_nnnorm]
      exact norm_entry_le_matrixSize k ij.1 ij.2
    · rw [← NNReal.coe_le_coe, coe_nnnorm]
      exact norm_inv_entry_le_matrixSize k ij.1 ij.2
  exact NNReal.coe_le_coe.mpr h

private theorem exists_matrixSupSize_le_of_isCompact (v : HeightOneSpectrum (𝓞 ℚ))
    {S : Set (GL (Fin 3) (v.adicCompletion ℚ))} (hS : IsCompact S) :
    ∃ B : ℝ, ∀ k ∈ S, ((matrixSupSize k : ℝ≥0) : ℝ) ≤ B := by
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn continuous_matrixSize.continuousOn
  refine ⟨B, fun k hk => (coe_matrixSupSize_le_matrixSize k).trans ?_⟩
  have h := hB k hk
  rw [Real.norm_eq_abs] at h
  exact (le_abs_self _).trans h

private def finEntry (x : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3) : FiniteAdeleRing (𝓞 ℚ) ℚ :=
  AdelicLevel.adeleFin (𝓞 ℚ) ℚ ((x : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j)

private def finInvEntry (x : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3) : FiniteAdeleRing (𝓞 ℚ) ℚ :=
  AdelicLevel.adeleFin (𝓞 ℚ) ℚ (((x⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j)

private theorem continuous_finEntry (i j : Fin 3) : Continuous fun x : AdelicGL 3 (𝓞 ℚ) ℚ => finEntry x i j :=
  (AdelicLevel.continuous_adeleFin (𝓞 ℚ) ℚ).comp (Units.continuous_val.matrix_elem i j)

private theorem continuous_finInvEntry (i j : Fin 3) :
    Continuous fun x : AdelicGL 3 (𝓞 ℚ) ℚ => finInvEntry x i j :=
  (AdelicLevel.continuous_adeleFin (𝓞 ℚ) ℚ).comp (Units.continuous_coe_inv.matrix_elem i j)

private theorem componentAt3_apply_entry (v : HeightOneSpectrum (𝓞 ℚ)) (x : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3) :
    ((componentAt3 (𝓞 ℚ) ℚ v x : GL (Fin 3) (v.adicCompletion ℚ)) :
      Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j = finEntry x i j v := by
  rw [coe_componentAt3]
  rfl

private theorem componentAt3_inv_apply_entry (v : HeightOneSpectrum (𝓞 ℚ)) (x : AdelicGL 3 (𝓞 ℚ) ℚ)
    (i j : Fin 3) :
    (((componentAt3 (𝓞 ℚ) ℚ v x)⁻¹ : GL (Fin 3) (v.adicCompletion ℚ)) :
      Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j = finInvEntry x i j v := by
  rw [← map_inv, coe_componentAt3]
  rfl

private theorem componentAt3_mem_localMaximalCompact3_of_valued_le (v : HeightOneSpectrum (𝓞 ℚ))
    (x : AdelicGL 3 (𝓞 ℚ) ℚ) (h1 : ∀ i j, Valued.v (finEntry x i j v) ≤ 1)
    (h2 : ∀ i j, Valued.v (finInvEntry x i j v) ≤ 1) :
    componentAt3 (𝓞 ℚ) ℚ v x ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  rw [mem_localMaximalCompact3_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [componentAt3_apply_entry]
    exact h1 i j
  · rw [componentAt3_inv_apply_entry]
    exact h2 i j

private def integralSet : Set (AdelicGL 3 (𝓞 ℚ) ℚ) :=
  {x | ∀ i j, finEntry x i j ∈ AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ ∧
    finInvEntry x i j ∈ AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ}

private theorem isOpen_integralSet : IsOpen integralSet := by
  have : integralSet = ⋂ i : Fin 3, ⋂ j : Fin 3,
      ((fun x : AdelicGL 3 (𝓞 ℚ) ℚ => finEntry x i j) ⁻¹' AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ ∩
        (fun x : AdelicGL 3 (𝓞 ℚ) ℚ => finInvEntry x i j) ⁻¹' AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ) := by
    ext x
    simp only [integralSet, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    ((AdelicLevel.isOpen_integralFiniteAdeles (𝓞 ℚ) ℚ).preimage (continuous_finEntry i j)).inter
      ((AdelicLevel.isOpen_integralFiniteAdeles (𝓞 ℚ) ℚ).preimage (continuous_finInvEntry i j))

private theorem one_mem_integralSet : (1 : AdelicGL 3 (𝓞 ℚ) ℚ) ∈ integralSet := by
  have hone : ∀ i j : Fin 3, AdelicLevel.adeleFin (𝓞 ℚ) ℚ
      ((1 : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j) ∈ AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · rw [map_one]
      exact AdelicLevel.one_mem_integralFiniteAdeles
    · rw [map_zero]
      exact AdelicLevel.zero_mem_integralFiniteAdeles
  intro i j
  refine ⟨?_, ?_⟩
  · simp only [finEntry, Units.val_one]
    exact hone i j
  · simp only [finInvEntry, inv_one, Units.val_one]
    exact hone i j

private theorem componentAt3_mem_of_mem_integralSet {u : AdelicGL 3 (𝓞 ℚ) ℚ} (hu : u ∈ integralSet)
    (v : HeightOneSpectrum (𝓞 ℚ)) : componentAt3 (𝓞 ℚ) ℚ v u ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v :=
  componentAt3_mem_localMaximalCompact3_of_valued_le v u
    (fun i j => AdelicLevel.valued_apply_le_one (hu i j).1 v)
    (fun i j => AdelicLevel.valued_apply_le_one (hu i j).2 v)

private theorem eventually_componentAt3_mem (x : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite,
      componentAt3 (𝓞 ℚ) ℚ v x ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  have hA : ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ∀ i j : Fin 3,
      finEntry x i j v ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => (finEntry x i j).2
  have hB : ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ∀ i j : Fin 3,
      finInvEntry x i j v ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => (finInvEntry x i j).2
  filter_upwards [hA, hB] with v h1 h2
  exact componentAt3_mem_localMaximalCompact3_of_valued_le v x
    (fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h1 i j))
    (fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h2 i j))

private noncomputable def badPlaces (x : AdelicGL 3 (𝓞 ℚ) ℚ) : Finset (HeightOneSpectrum (𝓞 ℚ)) :=
  (Filter.eventually_cofinite.mp (eventually_componentAt3_mem x)).toFinset

private theorem componentAt3_mem_of_notMem_badPlaces (x : AdelicGL 3 (𝓞 ℚ) ℚ) {v : HeightOneSpectrum (𝓞 ℚ)}
    (hv : v ∉ badPlaces x) : componentAt3 (𝓞 ℚ) ℚ v x ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  by_contra h
  exact hv ((Filter.eventually_cofinite.mp (eventually_componentAt3_mem x)).mem_toFinset.mpr h)

private theorem exists_finset_forall_mem_localMaximalCompact3_of_isCompact
    {K : Set (AdelicGL 3 (𝓞 ℚ) ℚ)} (hK : IsCompact K) :
    ∃ E : Finset (HeightOneSpectrum (𝓞 ℚ)), ∀ k ∈ K, ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ E →
      componentAt3 (𝓞 ℚ) ℚ v k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  classical
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun x => x • integralSet) fun x _ =>
    (isOpen_integralSet.smul x).mem_nhds ⟨1, one_mem_integralSet, by simp⟩
  refine ⟨t.biUnion badPlaces, fun k hk v hv => ?_⟩
  obtain ⟨x, hxt, hkx⟩ := Set.mem_iUnion₂.mp (ht hk)
  obtain ⟨u, hu, rfl⟩ := hkx
  have hvx : v ∉ badPlaces x := fun h => hv (Finset.mem_biUnion.mpr ⟨x, hxt, h⟩)
  show componentAt3 (𝓞 ℚ) ℚ v (x * u) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v
  rw [map_mul]
  exact (localMaximalCompact3 (𝓞 ℚ) ℚ v).mul_mem (componentAt3_mem_of_notMem_badPlaces x hvx)
    (componentAt3_mem_of_mem_integralSet hu v)

private theorem gauge3_mul_le_of_bounds {S : Set (AdelicGL 3 (𝓞 ℚ) ℚ)} {M : ℝ}
    (hM : ∀ k ∈ S, archTranslateConst ℚ k ≤ M) (E : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hE : ∀ k ∈ S, ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ E →
      componentAt3 (𝓞 ℚ) ℚ v k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v)
    {B : HeightOneSpectrum (𝓞 ℚ) → ℝ}
    (hB : ∀ v ∈ E, ∀ k ∈ S, ((matrixSupSize (componentAt3 (𝓞 ℚ) ℚ v k) : ℝ≥0) : ℝ) ≤ B v) :
    ∀ k ∈ S, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      gauge3 ℚ (g * k) ≤ (max 1 M * ∏ v ∈ E, max 1 (B v)) * gauge3 ℚ g := by
  intro k hk g
  have hfin := finGauge3_mul_le_of_forall_notMem g k E (fun v hv => hE k hk v hv)
  have hc1 : (1 : ℝ) ≤ ∏ v ∈ E, max 1 ((matrixSupSize (componentAt3 (𝓞 ℚ) ℚ v k) : ℝ≥0) : ℝ) := by
    have h := Finset.prod_le_prod (s := E) (f := fun _ => (1 : ℝ))
      (g := fun v => max 1 ((matrixSupSize (componentAt3 (𝓞 ℚ) ℚ v k) : ℝ≥0) : ℝ))
      (fun _ _ => zero_le_one) (fun v _ => le_max_left _ _)
    simpa using h
  have h1 := gauge3_mul_le ℚ g k hc1 hfin
  have hprod : ∏ v ∈ E, max 1 ((matrixSupSize (componentAt3 (𝓞 ℚ) ℚ v k) : ℝ≥0) : ℝ) ≤
      ∏ v ∈ E, max 1 (B v) :=
    Finset.prod_le_prod (fun v _ => zero_le_one.trans (le_max_left _ _))
      (fun v hv => max_le_max le_rfl (hB v hv k hk))
  have harch : archTranslateConst ℚ k ≤ max 1 M := (hM k hk).trans (le_max_right _ _)
  have hconst : archTranslateConst ℚ k *
      ∏ v ∈ E, max 1 ((matrixSupSize (componentAt3 (𝓞 ℚ) ℚ v k) : ℝ≥0) : ℝ) ≤
        max 1 M * ∏ v ∈ E, max 1 (B v) :=
    mul_le_mul harch hprod (zero_le_one.trans hc1) (zero_le_one.trans (le_max_left _ _))
  exact h1.trans (mul_le_mul_of_nonneg_right hconst (gauge3_pos ℚ g).le)

private theorem conj1 (K : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hK : IsCompact K) :
    ∃ C : ℝ, ∀ k ∈ K, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, gauge3 ℚ (g * k) ≤ C * gauge3 ℚ g := by
  classical
  obtain ⟨E, hE⟩ := exists_finset_forall_mem_localMaximalCompact3_of_isCompact hK
  obtain ⟨M, hM⟩ := exists_archTranslateConst_le_of_isCompact ℚ hK (τ := fun k => k)
    (fun w => continuous_archPlaceComponent3 w)
  have hB : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ B : ℝ, ∀ k ∈ K,
      ((matrixSupSize (componentAt3 (𝓞 ℚ) ℚ v k) : ℝ≥0) : ℝ) ≤ B := by
    intro v
    obtain ⟨B, hB⟩ := exists_matrixSupSize_le_of_isCompact v (hK.image (continuous_componentAt3 v))
    exact ⟨B, fun k hk => hB _ (Set.mem_image_of_mem _ hk)⟩
  choose B hB using hB
  exact ⟨_, gauge3_mul_le_of_bounds (fun k hk => hM k hk) E hE (fun v _ k hk => hB v k hk)⟩

private theorem conj2 (N : ℕ) (f φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hf : ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, ‖f g‖ ≤ C * gauge3 ℚ g ^ N)
    (hφ : SlabL2.IsSmoothingKernel φ) :
    ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, ‖SlabL2.smoothingOperator φ f g‖ ≤ C * gauge3 ℚ g ^ N := by
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
  obtain ⟨hφc, hφs⟩ := continuous_and_hasCompactSupport_of_isSmoothingKernel φ hφ
  obtain ⟨Mφ, hMφ⟩ := hφc.bounded_above_of_compact_support hφs
  have hMφ' : ∀ g, ‖φ g‖ ≤ max Mφ 0 := fun g => (hMφ g).trans (le_max_left _ _)
  have hMφ0 : (0 : ℝ) ≤ max Mφ 0 := le_max_right _ _
  obtain ⟨Cf, hCf⟩ := hf
  have hCf0 : (0 : ℝ) ≤ max Cf 0 := le_max_right _ _
  have hf' : ∀ g, ‖f g‖ ≤ max Cf 0 * gauge3 ℚ g ^ N := fun g =>
    (hCf g).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (gauge3_pos ℚ g).le N))
  obtain ⟨Cs, hCs⟩ := conj1 (tsupport φ) hφs.isCompact
  have hCs0 : (0 : ℝ) ≤ max Cs 0 := le_max_right _ _
  have htr : ∀ h ∈ tsupport φ, ∀ x : AdelicGL 3 (𝓞 ℚ) ℚ, gauge3 ℚ (x * h) ≤ max Cs 0 * gauge3 ℚ x :=
    fun h hh x => (hCs h hh x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (gauge3_pos ℚ x).le)
  have hμ : NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ (tsupport φ) < ⊤ :=
    hφs.isCompact.measure_lt_top
  refine ⟨max Mφ 0 * max Cf 0 * max Cs 0 ^ N *
    (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ (tsupport φ)).toReal, fun x => ?_⟩
  have hc0 : (0 : ℝ) ≤ max Mφ 0 * (max Cf 0 * (max Cs 0 * gauge3 ℚ x) ^ N) :=
    mul_nonneg hMφ0 (mul_nonneg hCf0 (pow_nonneg (mul_nonneg hCs0 (gauge3_pos ℚ x).le) N))
  have hpt : ∀ h : AdelicGL 3 (𝓞 ℚ) ℚ, ENNReal.ofReal ‖φ h * f (x * h)‖ ≤
      (tsupport φ).indicator
        (fun _ => ENNReal.ofReal (max Mφ 0 * (max Cf 0 * (max Cs 0 * gauge3 ℚ x) ^ N))) h := by
    intro h
    by_cases hh : h ∈ tsupport φ
    · rw [Set.indicator_of_mem hh]
      apply ENNReal.ofReal_le_ofReal
      rw [norm_mul]
      refine mul_le_mul (hMφ' h) ?_ (norm_nonneg _) hMφ0
      exact (hf' _).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (gauge3_pos ℚ _).le (htr h hh x) N) hCf0)
    · rw [image_eq_zero_of_notMem_tsupport hh]
      simp
  rw [SlabL2.smoothingOperator_apply]
  calc ‖∫ h, φ h * f (x * h) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)‖
      ≤ (∫⁻ h, ENNReal.ofReal ‖φ h * f (x * h)‖
          ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)).toReal :=
        norm_integral_le_lintegral_norm _
    _ ≤ (ENNReal.ofReal (max Mφ 0 * (max Cf 0 * (max Cs 0 * gauge3 ℚ x) ^ N)) *
          NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ (tsupport φ)).toReal := by
        apply ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hμ.ne)
        exact (lintegral_mono hpt).trans (lintegral_indicator_const_le _ _)
    _ = max Mφ 0 * (max Cf 0 * (max Cs 0 * gauge3 ℚ x) ^ N) *
          (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ (tsupport φ)).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0]
    _ = max Mφ 0 * max Cf 0 * max Cs 0 ^ N *
          (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ (tsupport φ)).toReal * gauge3 ℚ x ^ N := by
        rw [mul_pow]; ring

end

end PackageBody

end LanglandsTunnell.CubicInduction

open _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_gauge3_mul_le_of_isCompact_and_norm_smoothingOperator_le_gauge3_pow.LanglandsTunnell.CubicInduction in
theorem solution :
    (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K →
      ∃ C : ℝ, ∀ k ∈ K, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, gauge3 ℚ (g * k) ≤ C * gauge3 ℚ g) ∧
    ∀ (N : ℕ) (f φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
      (∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, ‖f g‖ ≤ C * gauge3 ℚ g ^ N) → SlabL2.IsSmoothingKernel φ →
        ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, ‖SlabL2.smoothingOperator φ f g‖ ≤ C * gauge3 ℚ g ^ N :=
  ⟨fun K hK => conj1 K hK, fun N f φ hf hφ => conj2 N f φ hf hφ⟩

end S_LanglandsTunnell_CubicInduction_gauge3_mul_le_of_isCompact_and_norm_smoothingOperator_le_gauge3_pow
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_gauge3_mul_le_of_isCompact_and_norm_smoothingOperator_le_gauge3_pow (solution)
