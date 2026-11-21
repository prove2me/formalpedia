-- Prove2me | solution 1 for LeanModelChecking.ABW.toNBW.lang_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:44:07.633278+00:00
-- url     : https://prove2.me/submissions/d6f61451-d7b5-4461-b0db-711d9837a9de

module
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNBWStatement
public import Definitions.Def_LeanPool_LeanModelChecking_ABW
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Order.KonigLemma
public import Definitions.Def_LeanPool_LeanModelChecking_ABWNBW

set_option autoImplicit true
@[expose] public section
public section
open LeanModelChecking
namespace LeanModelChecking
namespace ABW.toNBW
theorem _root_.solution {S Q} {A : ABW S Q} {w : Nat → S} :
    (ABW.toNBW A).language w → A.language w := by
  simp only [NBW.language, NBW.run, ge_iff_le, language, forall_exists_index, and_imp]
  intros p h1 h2 h3
  let X i := (p i).fst
  let W i := (p i).snd
  let G : RunDAG A w := {
    V := { (q, i) : _ | q ∈ X i }
    E := { ((q, i), q') : _ |
      (q ∈ X i \ W i ∧ q' ∈ X (i + 1)) ∨
      (q ∈ X i ∩ W i ∧ q' ∈ X (i + 1) ∩ (A.F ∪ W (i + 1))) }
    edge_closure := by grind
    p_root := by grind [ABW.toNBW]
    p_sat := by
      simp only [Set.mem_ofPred_eq, Prod.mk.eta, Set.mem_sdiff, Set.mem_inter_iff, Set.mem_union,
        Prod.forall]
      intros q i h10
      specialize h2 i
      rcases h2 with ⟨h11, h12⟩
      specialize h11 q h10
      grind
  }
  exists G
  simp only [RunDAG.accepting, DAG.path, ge_iff_le, forall_exists_index]
  intros pp b hp1
  have h4 : ∀ i, W (b + i) = ∅ → ∀ n, pp (i + n + 1) ∈ W (b + i + n + 1) ∨
      ∃ j, i ≤ j ∧ j ≤ b + i + n + 1 ∧ pp j ∈ A.F := by
    intros i hw n
    induction n <;> grind [ABW.toNBW]
  intros i
  rcases h3 (b + i) with ⟨start, start_gt, hstart⟩
  rcases h3 (start + 1) with ⟨endi, end_gt, hend⟩
  have eq2 : start = b + (start - b) := by omega
  specialize h4 (start - b) (eq2 ▸ hstart) (endi - start - 1)
  rcases h4 with h4 | ⟨j, h4⟩
  · exfalso
    simp only [W] at h4
    rw [show (b + (start - b) + (endi - start - 1) + 1)= endi by omega] at h4
    rw [hend] at h4
    contradiction
  · grind
end ABW.toNBW
end LeanModelChecking
