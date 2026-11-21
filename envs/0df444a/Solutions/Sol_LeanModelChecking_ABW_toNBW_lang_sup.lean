-- Prove2me | solution 1 for LeanModelChecking.ABW.toNBW.lang_sup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:47:11.432701+00:00
-- url     : https://prove2.me/submissions/ca6480f6-ee7d-4e0a-ac28-a871d0b0540e

module
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNBWStatement
public import Definitions.Def_LeanPool_LeanModelChecking_ABW
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Order.KonigLemma
public import Definitions.Def_LeanPool_LeanModelChecking_ABWNBW
public import Theorems.Thm_LeanModelChecking_LevelGraph_ex_path
public import Theorems.Thm_LeanModelChecking_PositiveBool_Sat_monotone


set_option autoImplicit true
@[expose] public section
public section
open LeanModelChecking
namespace LeanModelChecking
namespace ABW.toNBW
theorem _root_.solution {S Q} {A : ABW S Q} [Finite Q] {w : Nat → S} :
    A.language w → (ABW.toNBW A).language w := by
  simp only [language, RunDAG.accepting, ge_iff_le, forall_exists_index]
  intros G G_acc
  let p := helper.p (G := G)
  have p_path : A.toNBW.run p w := by
    simp only [NBW.run, toNBW, ne_eq]
    constructor
    · apply Set.mem_singleton
    · intros n
      induction n
      next =>
        constructor
        · intros q Hqin
          simp only [helper.p, Set.mem_singleton_iff, zero_add, level, ↓reduceIte, p] at Hqin ⊢
          subst Hqin
          obtain ⟨Y, p_sat, p_sub⟩ := G.p_sat _ G.p_root
          apply PositiveBool.Sat.monotone _ p_sat
          rw [Set.subset_def]
          intros q' q'Y
          have := G.edge_closure ((A.q₀, 0), q')
          grind
        · simp [p, helper.p, level]
      next n IH =>
        rcases IH with ⟨h1, IH⟩
        constructor
        · simp only [helper.p, level, ite_eq_left_iff, Set.mem_ofPred_eq, p] at *
          intros q hinV
          obtain ⟨Y, p_sat, p_sub⟩ := G.p_sat _ hinV
          apply PositiveBool.Sat.monotone _ p_sat
          rw [Set.subset_def]
          intros q' q'Y
          have := G.edge_closure ((q, n + 1), q')
          grind
        · rcases IH with ⟨hW, h2⟩ | ⟨hW, ⟨W'', ⟨h2, h3, h4⟩⟩⟩
          · rw [h2]
            simp only [Set.mem_sdiff, and_imp]
            by_cases hinf : ((helper.p (G := G) (n + 1)).1 ⊆ A.F)
            · left
              rw [←Set.sdiff_eq_empty] at hinf
              refine ⟨hinf, ?_⟩
              simp only [helper.p, level, hW, ↓reduceIte, Set.mem_sdiff, Set.mem_ofPred_eq,
                ite_eq_left_iff, p] at hinf ⊢
              intros; contradiction
            · right
              have hW2 : (p (n + 1)).2 ≠ ∅ := by
                rw [h2]
                intro H
                rw [Set.sdiff_eq_empty] at H
                contradiction
              rw [←Set.sdiff_eq_empty] at hinf
              refine ⟨hinf, ?_⟩
              exists (p (n + 2)).2 ∪ (A.F ∩ (p (n + 2)).1)
              simp only [Set.union_subset_iff, Set.inter_subset_right, and_true]
              refine ⟨?_, ?_, ?_⟩
              · simp [p, helper.p]
                grind
              · simp [p, helper.p, level]
                grind
              · intros q qp1 qp2
                simp only [helper.p, level, Set.mem_ofPred_eq, p] at qp1
                obtain ⟨Y, p_sat, p_sub⟩ := G.p_sat _ qp1
                apply PositiveBool.Sat.monotone _ p_sat
                intros x xY
                simp only [ne_eq, Set.mem_union, Set.mem_inter_iff, p] at *
                have := G.edge_closure ((q, n + 1), x)
                simp [helper.p, hW, level]
                grind
          · by_cases hinf : (W'' ⊆ A.F)
            · grind [helper.p]
            · right
              have hW2 : (p (n + 1)).2 ≠ ∅ := by
                rw [h2]
                intro H
                rw [Set.sdiff_eq_empty] at H
                contradiction
              refine ⟨hW2, ?_⟩
              exists (p (n + 2)).2 ∪ (A.F ∩ (p (n + 2)).1)
              simp only [Set.union_subset_iff, Set.inter_subset_right, and_true]
              refine ⟨?_, ?_, ?_⟩
              · simp [p, helper.p]
                grind
              · simp [p, helper.p, level]
                grind
              · intros q qp1
                simp only [helper.p, level, hW, ↓reduceIte, Set.mem_ofPred_eq, p] at qp1
                obtain ⟨qp1, b, qp2, qp3, qp4, qp5⟩ := qp1
                obtain ⟨Y, p_sat, p_sub⟩ := G.p_sat _ qp4
                apply PositiveBool.Sat.monotone _ p_sat
                intros x xY
                have := G.edge_closure ((q, n + 1), x)
                simp [p, helper.p, level]
                grind
  exists p
  refine ⟨p_path, ?_⟩
  have W_not_F : ∀ i, (p i).2 ∩ A.F = ∅ := by
    intros i; cases i <;> simp [p, helper.p]; grind
  by_contra H
  unfold ABW.toNBW at H
  simp only [ge_iff_le, ne_eq, Set.mem_ofPred_eq, not_forall, not_exists, not_and] at H
  rcases H with ⟨n, W_nonempty⟩
  let S' : LevelGraph := {
    level i := { v // v ∈ (p (n + i)).2 }
    E i v v' := ((v.val, n + i), v'.val) ∈ G.E
    ex_parent i v := by
      specialize W_nonempty (n + i) (by omega)
      rcases v with ⟨v, vp⟩
      simp only [helper.p, Nat.add_eq, W_nonempty, ↓reduceIte, Set.mem_ofPred_eq, p] at vp
      obtain ⟨_, y, yW, yE⟩ := vp
      exists ⟨y, by assumption⟩
      apply yE.right.right
    fin i := Subtype.finite
    nonempty i := by
      simp
      specialize W_nonempty (n + i) (by omega)
      grind
  }
  obtain ⟨⟨bad_path_f, bad_path_path⟩⟩ := S'.ex_path
  obtain ⟨j, jn, jF⟩ := G_acc (fun i => bad_path_f i) (by
    simp only [DAG.path]
    simp [S'] at bad_path_path
    exists n
  ) n
  simp only [S'] at bad_path_f
  specialize W_not_F (n + j)
  rw [←Set.disjoint_iff_inter_eq_empty] at W_not_F
  rw [Set.disjoint_left] at W_not_F
  simp_all
end ABW.toNBW
end LeanModelChecking
