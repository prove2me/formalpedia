-- Prove2me | solution 1 for GlobalTheory.SmoothForms.PermWord.symb_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:17:54.894729+00:00
-- url     : https://prove2.me/submissions/753c7537-5ded-4644-997d-a99ce1d2f706

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PermutationWordGelfandPolynomialModShorter
import Theorems.Thm_GlobalTheory_SmoothForms_PermWord_perm_sub_mem
import Theorems.Thm_GlobalTheory_SmoothForms_PermWord_order_wd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
noncomputable section
open GlobalTheory GlobalTheory.SmoothForms GlobalTheory.SmoothForms.PermWord
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}
namespace GlobalTheory.SmoothForms.PermWord
theorem _root_.solution {E : Fin n → Fin n → A} (hE : Formalism.REAL.GlRel E) {d : ℕ} {x} (hx : x ∈ symb E d) :
    x.2 - order E x.1 ∈ shorter E d := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, rfl, rfl⟩ := hx
    simp only [order_wd]
    exact perm_sub_mem hE (Multiset.coe_eq_coe.1 (Multiset.coe_toList _).symm)
  | zero => simp
  | add x y _ _ hx hy =>
    convert add_mem hx hy using 1
    simp only [Prod.snd_add, Prod.fst_add, map_add]; abel
  | smul c x _ hx =>
    convert Submodule.smul_mem _ c hx using 1
    simp [smul_sub]
end GlobalTheory.SmoothForms.PermWord
