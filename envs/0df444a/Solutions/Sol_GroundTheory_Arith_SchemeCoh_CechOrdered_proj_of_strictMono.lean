-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.CechOrdered.proj_of_strictMono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:45:38.27196+00:00
-- url     : https://prove2.me/submissions/6b80e0ee-cfbf-4666-b521-62cc54852769

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechLeray
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechOrdered

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open CategoryTheory Opposite TopologicalSpace
universe w u
open GroundTheory.Arith.SchemeCoh.CechOrdered
variable (ι : Type w)
variable {ι}
variable [LinearOrder ι]
namespace GroundTheory.Arith.SchemeCoh.CechOrdered
theorem _root_.solution : ∀ (q : ℕ) (i : Fin (q + 1) → ι), StrictMono i →
    proj q i = Finsupp.single i 1
  | 0, i, _ => rfl
  | q + 1, i, hi => by
    change ocone (minR i) (lin (proj q) (bd q (Finsupp.single i 1))) = _
    have hmin : minR i = i 0 := le_antisymm (minR_le i 0) (by
      obtain ⟨a, ha⟩ := minR_mem i
      rw [← ha]
      exact hi.monotone (Fin.zero_le a))
    rw [lin_bd_single_apply, hmin]
    simp only [fun a : Fin (q + 2) => solution q _ (hi.comp (Fin.strictMono_succAbove a)),
      map_sum, map_zsmul, ocone_single, one_smul]
    rw [Fin.sum_univ_succ]
    have h1 : i 0 < (i ∘ (0 : Fin (q + 2)).succAbove) 0 := hi (by simp)
    have h2 : ∀ b : Fin (q + 1), ¬ i 0 < (i ∘ b.succ.succAbove) 0 := fun b => by
      simp
    simp only [h1, h2, if_true, if_false, smul_zero, Finset.sum_const_zero, add_zero,
      Fin.val_zero, pow_zero, one_smul]
    congr 1
    funext a
    cases a using Fin.cases with
    | zero => rfl
    | succ a => simp
end GroundTheory.Arith.SchemeCoh.CechOrdered
