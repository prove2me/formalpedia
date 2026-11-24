-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.QIndex.OnePlus.nrm_det_one_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:47:28.349807+00:00
-- url     : https://prove2.me/submissions/922ce593-7273-4ac6-9b33-73085936b194

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemConjSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemIntegralGLIffIntegralUnitDet
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemBoxLatticeIffCongruence
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_NormalisedValue_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.QIndex
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.QIndex GlobalTheory.CompanionTheory.QL.QIndex.OnePlus
namespace GlobalTheory.CompanionTheory.QL.QIndex.OnePlus
theorem _root_.solution {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
    (hLF : LF O ϖ nrm q) {n : ℕ} {x : Matrix (Fin n) (Fin n) F}
    (hx : ∀ a b, ∃ o ∈ O, x a b = ϖ * o) : nrm (1 + x).det = 1 := by
  obtain ⟨-, hϖ, hle, hlt, -, -, -⟩ := GlobalTheory.CompanionTheory.QL.NormalisedValue.main hLF
  choose f hf hf' using hx
  let ϖ' : O := ⟨ϖ, hϖ⟩
  let y : Matrix (Fin n) (Fin n) O := fun a b => ⟨f a b, hf a b⟩
  let M : Matrix (Fin n) (Fin n) O := 1 + ϖ' • y
  have hM : O.subtype.mapMatrix M = 1 + x := by
    ext a b
    by_cases hab : a = b
    · simp [M, y, ϖ', hf', hab]
      rfl
    · simp [M, y, ϖ', hf', hab, Matrix.one_apply]
      rfl
  let π := Ideal.Quotient.mk (Ideal.span {ϖ'})
  have hπ : π ϖ' = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  have hred : π.mapMatrix M = 1 := by
    simp only [M, map_add, map_one]
    have : π.mapMatrix (ϖ' • y) = 0 := by
      ext a b
      simp [hπ]
    rw [this, add_zero]
  have hdet : π M.det = 1 := by
    rw [RingHom.map_det, hred, Matrix.det_one]
  have hmem : M.det - 1 ∈ Ideal.span {ϖ'} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one]
    exact sub_eq_zero.2 hdet
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hmem
  have hcoe : (1 + x).det = (M.det : F) := by
    rw [← hM, ← RingHom.map_det]
    rfl
  have hEq : (1 + x).det = 1 + (a : F) * ϖ := by
    have h2 := congrArg (Subtype.val) ha
    have h3 : (a : F) * ϖ = (M.det : F) - 1 := by simpa [ϖ'] using h2
    rw [hcoe, h3]
    ring
  have hin : (1 + x).det ∈ O := by
    rw [hcoe]
    exact M.det.2
  refine le_antisymm ((hle _).2 hin) (not_lt.1 fun hl => ?_)
  obtain ⟨o, ho, e⟩ := (hlt _).1 hl
  have h1 : (1 : F) = ϖ * (o - a) := by
    have : (1 : F) + (a : F) * ϖ = ϖ * o := by rw [← hEq, e]
    linear_combination this
  have h2 : nrm (1 : F) < 1 := (hlt 1).2 ⟨o - a, O.sub_mem ho a.2, h1⟩
  simp at h2
end GlobalTheory.CompanionTheory.QL.QIndex.OnePlus
