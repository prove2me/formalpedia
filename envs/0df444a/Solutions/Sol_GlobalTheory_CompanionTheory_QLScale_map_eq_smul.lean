-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QLScale.map_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:07:23.629714+00:00
-- url     : https://prove2.me/submissions/b957c666-02ae-48cd-b6f2-373648b2d8a4

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_CartanDecompositionGeneralLinearStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemIntegralGLIffIntegralUnitDetStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixAdditiveHaarNormalizedStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixHaarRightTranslate
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_T_matrix_additive_haar_normalized
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QLScale
open scoped ENNReal
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
variable [MeasurableSpace F] [BorelSpace F]
namespace GlobalTheory.CompanionTheory.QLScale
theorem _root_.solution (hLF : LF O ϖ nrm q) {n m : ℕ} {dx : Measure (Matrix (Fin n) (Fin m) F)}
    (hinv : dx.IsAddLeftInvariant) (h1 : dx (intMat O n m) = 1)
    (φ : Matrix (Fin n) (Fin m) F ≃ₜ+ Matrix (Fin n) (Fin m) F) :
    Measure.map φ dx = dx (φ ⁻¹' intMat O n m) • dx := by
  obtain ⟨hB, hopen, hcomp, -, hHaar, huniq⟩ := GlobalTheory.T.matrix_additive_haar_normalized hLF n m
  haveI := hB
  haveI := hinv
  haveI := hHaar dx hinv h1
  have hφc : Continuous φ := φ.continuous
  have hφm : Measurable φ := hφc.measurable
  have h0 : (0 : Matrix (Fin n) (Fin m) F) ∈ φ ⁻¹' intMat O n m := by
    show φ 0 ∈ intMat O n m
    rw [map_zero]
    show ∀ i j, (0 : Matrix (Fin n) (Fin m) F) i j ∈ O
    intro i j
    exact O.zero_mem
  have hc0 : dx (φ ⁻¹' intMat O n m) ≠ 0 := (hopen.preimage hφc).measure_ne_zero dx ⟨0, h0⟩
  have hK : IsCompact (φ ⁻¹' intMat O n m) := by
    have hset : φ ⁻¹' intMat O n m = φ.symm '' intMat O n m := by
      ext x
      constructor
      · intro hx
        exact ⟨φ x, hx, φ.symm_apply_apply x⟩
      · rintro ⟨y, hy, rfl⟩
        show φ (φ.symm y) ∈ intMat O n m
        rw [φ.apply_symm_apply]
        exact hy
    rw [hset]
    exact hcomp.image φ.symm.continuous
  have hctop : dx (φ ⁻¹' intMat O n m) ≠ ⊤ := hK.measure_lt_top.ne
  haveI hinvm : (Measure.map φ dx).IsAddLeftInvariant := by
    refine ⟨fun g => ?_⟩
    rw [Measure.map_map (measurable_const_add g) hφm]
    have hfun : ((g + ·) ∘ φ) = φ ∘ (φ.symm g + ·) := by
      funext x
      simp [map_add]
    rw [hfun, ← Measure.map_map hφm (measurable_const_add _), map_add_left_eq_self]
  have hν : ((dx (φ ⁻¹' intMat O n m))⁻¹ • Measure.map φ dx) (intMat O n m) = 1 := by
    rw [Measure.smul_apply, Measure.map_apply hφm hopen.measurableSet, smul_eq_mul,
      ENNReal.inv_mul_cancel hc0 hctop]
  have heq := huniq dx hinv h1 ((dx (φ ⁻¹' intMat O n m))⁻¹ • Measure.map φ dx) inferInstance hν
  calc Measure.map φ dx
      = dx (φ ⁻¹' intMat O n m) • ((dx (φ ⁻¹' intMat O n m))⁻¹ • Measure.map φ dx) := by
        rw [smul_smul, ENNReal.mul_inv_cancel hc0 hctop, one_smul]
    _ = dx (φ ⁻¹' intMat O n m) • dx := by rw [← heq]
end GlobalTheory.CompanionTheory.QLScale
