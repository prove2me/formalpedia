-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.QIndex.ConjLe.det_eq_one_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:56:27.227343+00:00
-- url     : https://prove2.me/submissions/874fc7f9-1310-4532-899f-b44f52a155f2

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemConjSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemIntegralGLIffIntegralUnitDet
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DiagonalConjugateCongruenceBox

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.QIndex GlobalTheory.CompanionTheory.QL.QIndex.ConjLe
variable {F : Type} [Field F]
namespace GlobalTheory.CompanionTheory.QL.QIndex.ConjLe
theorem _root_.solution (O : Subring F) {c : F} (hc : c ∈ O) {n : ℕ}
    {g : Matrix (Fin n) (Fin n) F} (h : Lvl O c (g - 1)) : ∃ o ∈ O, g.det = 1 + c * o := by
  classical
  have hint : IsInt O g := fun i j => by
    obtain ⟨o, ho, e⟩ := h i j
    have e' : g i j = (1 : Matrix (Fin n) (Fin n) F) i j + c * o := by
      rw [← e]; simp
    rw [e']
    refine O.add_mem ?_ (O.mul_mem hc ho)
    by_cases hij : i = j
    · subst hij; rw [Matrix.one_apply_eq]; exact O.one_mem
    · rw [Matrix.one_apply_ne hij]; exact O.zero_mem
  let M : Matrix (Fin n) (Fin n) O := fun i j => ⟨g i j, hint i j⟩
  have hM : O.subtype.mapMatrix M = g := by
    ext i j; rfl
  let c' : O := ⟨c, hc⟩
  let π := Ideal.Quotient.mk (Ideal.span {c'})
  have hc0 : π c' = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self c')
  have hπ : π.mapMatrix M = 1 := by
    ext i j
    obtain ⟨o, ho, e⟩ := h i j
    have e' : M i j = (1 : Matrix (Fin n) (Fin n) O) i j + c' * ⟨o, ho⟩ := by
      apply Subtype.ext
      have e2 : g i j = (1 : Matrix (Fin n) (Fin n) F) i j + c * o := by
        rw [← e]; simp
      by_cases hij : i = j
      · subst hij; rw [Matrix.one_apply_eq] at e2 ⊢; simpa [M, c'] using e2
      · simpa [M, c', hij] using e2
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, e', map_add, map_mul, hc0, zero_mul, add_zero]
    by_cases hij : i = j
    · subst hij; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
    · simp [hij]
  have hdet : π (M.det - 1) = 0 := by
    rw [map_sub, RingHom.map_det, hπ, Matrix.det_one, map_one, sub_self]
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 hdet)
  refine ⟨a, a.2, ?_⟩
  have h1 : (O.subtype M.det) = g.det := by
    rw [RingHom.map_det, hM]
  have h2 : (a : F) * c = (M.det : F) - 1 := by
    simpa [c'] using congrArg Subtype.val ha
  have h3 : (M.det : F) = g.det := h1
  rw [← h3]
  linear_combination -h2
end GlobalTheory.CompanionTheory.QL.QIndex.ConjLe
