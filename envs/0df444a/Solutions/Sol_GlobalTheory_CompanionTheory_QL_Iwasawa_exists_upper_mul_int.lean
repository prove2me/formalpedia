-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.Iwasawa.exists_upper_mul_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:48:50.248808+00:00
-- url     : https://prove2.me/submissions/d89b2596-b537-43da-8771-98386a72e8c0

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOfValILeOne
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IwasawaDecompositionUpperTriangular
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_Iwasawa_map_mem_GLint
import Theorems.Thm_GlobalTheory_ValIwasawa_iwasawa


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.Iwasawa
namespace GlobalTheory.CompanionTheory.QL.Iwasawa
theorem _root_.solution {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
    (h : LF O ϖ nrm q) (n : ℕ) (g : GL (Fin n) F) :
    ∃ b : GL (Fin n) F, (b : Matrix (Fin n) (Fin n) F).BlockTriangular id ∧
      ∃ k ∈ GLint O n, g = b * k := by
  obtain rfl := h.O_eq
  obtain ⟨k, b, hb, hg⟩ :=
    GlobalTheory.ValIwasawa.iwasawa (ValuativeRel.valuation F).valuationSubring F n g⁻¹
  refine ⟨b⁻¹, ?_, _, (GLint _ n).inv_mem (map_mem_GLint k), ?_⟩
  · let _ : Invertible (b : Matrix (Fin n) (Fin n) F) := Units.invertible b
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hb
  · rw [← _root_.mul_inv_rev, ← hg, inv_inv]
end GlobalTheory.CompanionTheory.QL.Iwasawa
