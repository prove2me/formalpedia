-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.QIndex.ConjLe.mem_congGL_of_lvl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:26:48.924698+00:00
-- url     : https://prove2.me/submissions/ad900f22-ca2c-469b-a2c4-3b153beff230

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemConjSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemIntegralGLIffIntegralUnitDet
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DiagonalConjugateCongruenceBox
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_QIndex_ConjLe_det_eq_one_add
import Theorems.Thm_GlobalTheory_CompanionTheory_QLDet_mem_GLint_iff
import Theorems.Thm_GlobalTheory_T_localField_uniformizer_norm_properties


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
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
namespace GlobalTheory.CompanionTheory.QL.QIndex.ConjLe
theorem _root_.solution (hLF : LF O ϖ nrm q) {n T : ℕ} (hT : 1 ≤ T) (g : GL (Fin n) F)
    (h : Lvl O (ϖ ^ T) ((g : Matrix (Fin n) (Fin n) F) - 1)) : g ∈ congGL O (ϖ ^ T) n := by
  obtain ⟨-, hpi, hle, hlt, -, hult, -⟩ := GlobalTheory.T.localField_uniformizer_norm_properties hLF
  have hc : ϖ ^ T ∈ O := O.pow_mem hpi T
  refine ⟨(GlobalTheory.CompanionTheory.QLDet.mem_GLint_iff hLF n g).2 ⟨fun i j => ?_, ?_⟩, h⟩
  · obtain ⟨o, ho, e⟩ := h i j
    have e' : (g : Matrix (Fin n) (Fin n) F) i j = (1 : Matrix (Fin n) (Fin n) F) i j + ϖ ^ T * o := by
      rw [← e]; simp
    rw [e']
    refine O.add_mem ?_ (O.mul_mem hc ho)
    by_cases hij : i = j
    · subst hij; rw [Matrix.one_apply_eq]; exact O.one_mem
    · rw [Matrix.one_apply_ne hij]; exact O.zero_mem
  · obtain ⟨o, ho, e⟩ := det_eq_one_add O hc h
    rw [e]
    have hy : nrm (ϖ ^ T * o) < 1 := by
      refine (hlt _).2 ⟨ϖ ^ (T - 1) * o, O.mul_mem (O.pow_mem hpi _) ho, ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, T = k + 1 := ⟨T - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    apply le_antisymm
    · refine (hult _ _).trans (max_le ?_ hy.le)
      simp
    · by_contra hcon
      have hcon' : nrm (1 + ϖ ^ T * o) < 1 := not_le.1 hcon
      have h1 := hult (1 + ϖ ^ T * o) (-(ϖ ^ T * o))
      rw [add_neg_cancel_right, map_one, map_neg_eq_map] at h1
      exact absurd h1 (not_le.2 (max_lt hcon' hy))
end GlobalTheory.CompanionTheory.QL.QIndex.ConjLe
