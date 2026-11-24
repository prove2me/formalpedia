-- Prove2me | solution 1 for GlobalTheory.SW.Vac.exists_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:09:29.929608+00:00
-- url     : https://prove2.me/submissions/2cafc56e-a71b-43a2-b336-3a40fb17169f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsExOfPow
import Theorems.Thm_GlobalTheory_SW_Vac_pr_comm
import Theorems.Thm_GlobalTheory_SW_Vac_pr_add_left
import Theorems.Thm_GlobalTheory_SW_Vac_pr_neg_left
import Theorems.Thm_GlobalTheory_SW_Vac_pr_zero_left
import Theorems.Thm_GlobalTheory_SW_Vac_pr_sub_left
import Theorems.Thm_GlobalTheory_SW_Vac_exists_graph
import Theorems.Thm_GlobalTheory_SW_Vac_fg_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Vac
noncomputable section
variable {κ ι : Type} [Fintype κ] [Fintype ι]
namespace GlobalTheory.SW.Vac
theorem _root_.solution (A : AddSubgroup (Matrix κ ι ℚ × Matrix κ ι ℚ)) (hA : A.FG)
    (hd : ∀ y, y ∈ A ↔ ∀ y' ∈ A, ∃ m : ℤ, pr y.1 y'.2 - pr y'.1 y.2 = m) (b : Matrix κ ι ℚ)
    (hb : ∀ a, (a, 0) ∈ A → ∃ m : ℤ, pr b a = m) : ∃ a, (a, b) ∈ A := by
  let Γ : AddSubgroup (Matrix κ ι ℚ × ℚ) :=
    { carrier := {p | ∃ y ∈ A, y.2 = p.1 ∧ ∃ m : ℤ, p.2 - pr y.1 b = m}
      zero_mem' := ⟨0, A.zero_mem, rfl, 0, by simp [pr_zero_left]⟩
      add_mem' := by
        rintro p q ⟨y, hy, e, m, hm⟩ ⟨y', hy', e', m', hm'⟩
        refine ⟨y + y', A.add_mem hy hy', by simp [e, e'], m + m', ?_⟩
        rw [Prod.fst_add, Prod.snd_add, pr_add_left]; push_cast; linarith
      neg_mem' := by
        rintro p ⟨y, hy, e, m, hm⟩
        refine ⟨-y, A.neg_mem hy, by simp [e], -m, ?_⟩
        rw [Prod.fst_neg, Prod.snd_neg, pr_neg_left]; push_cast; linarith }
  obtain ⟨x, hx⟩ := exists_graph Γ (A.map (AddMonoidHom.snd _ _)) (fg_map hA _)
    (by rintro p ⟨y, hy, e, -⟩; exact ⟨y, hy, e⟩)
  refine ⟨x, (hd _).2 fun y hy => ?_⟩
  obtain ⟨y', hy', e, m, hm⟩ := hx (y.2, pr y.1 b) ⟨y, hy, rfl, 0, by simp⟩
  have hmem : (y'.1 - y.1, 0) ∈ A := by
    have : y' - y = (y'.1 - y.1, 0) := Prod.ext rfl (by simp [e])
    rw [← this]; exact A.sub_mem hy' hy
  obtain ⟨n, hn⟩ := hb _ hmem
  rw [pr_comm, pr_sub_left] at hn
  refine ⟨m + n, ?_⟩
  simp only at hm ⊢
  push_cast; linarith
end GlobalTheory.SW.Vac
