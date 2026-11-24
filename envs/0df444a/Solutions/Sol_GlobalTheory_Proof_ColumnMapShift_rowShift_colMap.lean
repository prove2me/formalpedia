-- Prove2me | solution 1 for GlobalTheory.Proof.ColumnMapShift.rowShift_colMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:54:07.341728+00:00
-- url     : https://prove2.me/submissions/ac8d9a51-0249-434e-893d-880b36543d91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_UnitaryDetClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ColumnMapShift
import Theorems.Thm_GlobalTheory_Proof_ColumnMapShift_rowShift_X_self
import Theorems.Thm_GlobalTheory_Proof_ColumnMapShift_rowShift_X_ne
import Theorems.Thm_GlobalTheory_Proof_ColumnMapShift_colMap_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Proof GlobalTheory.Proof.ColumnMapShift
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {T : Type} {r : T → ℕ} {n : ℕ} {k : Type} [Field k]
namespace GlobalTheory.Proof.ColumnMapShift
theorem _root_.solution (g : T → Fin n → Fin n → k) (σ : T) (i i' : Fin (r σ)) (t : k)
    (P : MvPolynomial (Letter T r n) k) :
    rowShift r n k σ i i' t (colMap r g P) = colMap r g (rowShift r n k σ i i' t P) := by
  have h : (rowShift r n k σ i i' t).comp (colMap r g) = (colMap r g).comp (rowShift r n k σ i i' t) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨τ, j, b⟩
    simp only [AlgHom.comp_apply]
    by_cases h : (⟨τ, j⟩ : Σ s, Fin (r s)) = ⟨σ, i⟩
    · cases h
      simp only [rowShift_X_self, colMap_X, map_sum, map_mul, map_add, algHom_C, algebraMap_eq,
        Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    · simp only [rowShift_X_ne σ i i' t τ j h, colMap_X, map_sum, map_mul, algHom_C, algebraMap_eq]
  exact DFunLike.congr_fun h P
end GlobalTheory.Proof.ColumnMapShift
