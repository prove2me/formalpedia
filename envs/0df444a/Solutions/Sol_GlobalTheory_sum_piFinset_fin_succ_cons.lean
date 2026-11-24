-- Prove2me | solution 1 for GlobalTheory.sum_piFinset_fin_succ_cons
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:36:09.50937+00:00
-- url     : https://prove2.me/submissions/066f2429-2d90-4ea7-8070-311be29a13e8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumPiFinsetFinSuccCons

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Finset
namespace GlobalTheory
theorem _root_.solution {α K : Type} [AddCommMonoid K] (n : ℕ) (S : Finset α)
    (F : (Fin (n + 1) → α) → K) :
    ∑ t ∈ Fintype.piFinset (fun _ : Fin (n + 1) => S), F t =
      ∑ a ∈ S, ∑ t ∈ Fintype.piFinset (fun _ : Fin n => S), F (Fin.cons a t) := by
  rw [← Finset.sum_product' S (Fintype.piFinset (fun _ : Fin n => S))
    (fun a t => F (Fin.cons a t))]
  symm
  refine Finset.sum_equiv (Fin.consEquiv (fun _ => α)) ?_ ?_
  · rintro ⟨a, t⟩
    simp [Fin.forall_fin_succ, Fin.consEquiv]
  · rintro ⟨a, t⟩ _
    rfl
end GlobalTheory
