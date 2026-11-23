-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HaarCoord.fixed_eq_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:34:44.541289+00:00
-- url     : https://prove2.me/submissions/70cebcff-78b6-45f7-9256-f9e25d591851

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasure
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HaarCoord_sigR_tmul
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HaarCoord_half_add_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HaarCoord
variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R]
namespace GlobalTheory.CompanionTheory.SW.HaarCoord
theorem _root_.solution [CharZero F] {σ : E →ₐ[F] E} (hinv : ∀ x, σ (σ x) = x)
    (h2 : Module.finrank F E = 2) {δ : E} (hδ : δ ≠ 0) (hσδ : σ δ = -δ)
    (y : R ⊗[F] E) (hy : sigR R σ y = y) : ∃ r : R, y = r ⊗ₜ[F] (1 : E) := by
  have hli : LinearIndependent F ![(1 : E), δ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h' := congrArg σ hst
    simp only [map_add, map_smul, map_one, hσδ, map_zero, smul_neg] at h'
    have ht2 : (t + t) • δ = 0 := by
      rw [add_smul]
      have := sub_eq_zero.mpr (hst.trans h'.symm)
      rw [← this]
      abel
    have ht : t = 0 := by
      rcases smul_eq_zero.mp ht2 with h | h
      · have : (2 : F) * t = 0 := by rw [two_mul]; exact h
        simpa using this
      · exact absurd h hδ
    subst ht
    simpa using hst
  let B : Module.Basis (Fin 2) F E := basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])
  have hB : ⇑B = ![(1 : E), δ] := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  let C := Algebra.TensorProduct.basis R B
  have hC0 : C 0 = (1 : R) ⊗ₜ[F] (1 : E) := by
    simp [C, Algebra.TensorProduct.basis_apply, hB]
  have hC1 : C 1 = (1 : R) ⊗ₜ[F] δ := by
    simp [C, Algebra.TensorProduct.basis_apply, hB]
  obtain ⟨r0, r1, hy'⟩ : ∃ r0 r1 : R, y = r0 • C 0 + r1 • C 1 :=
    ⟨C.repr y 0, C.repr y 1, by
      have := C.sum_repr y
      rw [Fin.sum_univ_two] at this
      exact this.symm⟩
  have hs : sigR R σ y = r0 • C 0 + (-r1) • C 1 := by
    rw [hy', hC0, hC1]
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one, map_add, sigR_tmul, map_one, hσδ,
      TensorProduct.tmul_neg, TensorProduct.neg_tmul]
  rw [hy] at hs
  have h1 : r1 = -r1 := by
    have := congrArg (fun z => C.repr z 1) (hy'.symm.trans hs)
    simpa [Finsupp.single_apply] using this
  have h0 : r1 = 0 := by
    have : r1 + r1 = 0 := by nth_rw 1 [h1]; ring
    rw [← half_add_self (F := F) R r1, this, mul_zero]
  refine ⟨r0, ?_⟩
  rw [hy', h0, hC0]
  simp [TensorProduct.smul_tmul']
end GlobalTheory.CompanionTheory.SW.HaarCoord
