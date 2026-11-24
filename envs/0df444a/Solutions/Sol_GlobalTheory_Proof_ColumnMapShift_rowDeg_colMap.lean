-- Prove2me | solution 1 for GlobalTheory.Proof.ColumnMapShift.rowDeg_colMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:54:06.609973+00:00
-- url     : https://prove2.me/submissions/160f67e4-299c-4886-8ac6-2525dc1fc162

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_UnitaryDetClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ColumnMapShift
import Theorems.Thm_GlobalTheory_Proof_ColumnMapShift_aeval_weightedHomogeneous
import Theorems.Thm_GlobalTheory_Proof_ColumnMapShift_weight_rowWt

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
theorem _root_.solution [Fintype T] (g : T → Fin n → Fin n → k) {a : T → ℕ → ℕ}
    {P : MvPolynomial (Letter T r n) k} (hP : RowDeg r n k a P) : RowDeg r n k a (colMap r g P) := by
  intro m hm σ i
  have h1 : IsWeightedHomogeneous (rowWt n σ i) P (a σ i) := by
    intro d hd
    rw [weight_rowWt]
    exact hP d (mem_support_iff.2 hd) σ i
  have h2 : IsWeightedHomogeneous (rowWt n σ i) (colMap r g P) (a σ i) := by
    refine aeval_weightedHomogeneous h1 _ fun ℓ => ?_
    refine IsWeightedHomogeneous.sum _ _ _ fun b _ => ?_
    exact IsWeightedHomogeneous.C_mul (isWeightedHomogeneous_X k (rowWt n σ i) ⟨ℓ.1, ℓ.2.1, b⟩) _
  rw [← weight_rowWt]
  exact h2 (mem_support_iff.1 hm)
end GlobalTheory.Proof.ColumnMapShift
