-- Prove2me | solution 1 for GreedyColoringLCA969.LowerBound.observation_3_5
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T23:37:34.138808+00:00
-- url     : https://prove2.me/submissions/fd85a64c-0f37-4117-b851-bb773965e4f2

import Definitions.Def_GreedyColoringLCA969_LowerBound_GraphBasics

open scoped Classical
open SimpleGraph
namespace GreedyColoringLCA969.LowerBound

private theorem decreasing_walk {V : Type} (G : SimpleGraph V) (c : V → ℕ)
    (hc : ∀ v k, 0 < k → k < c v → ∃ u, G.Adj v u ∧ c u = k)
    (l : List ℕ) : ∀ v, List.Pairwise (· > ·) (c v :: l) →
      (∀ k ∈ l, 0 < k) →
      ∃ (w : V) (p : G.Walk v w), p.IsPath ∧ p.support.map c = c v :: l := by
  induction l with
  | nil =>
    intro v _ _
    exact ⟨v, .nil, by simp, rfl⟩
  | cons k l ih =>
    intro v hpair hpos
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hpair
    obtain ⟨u, hadj, hcolor⟩ := hc v k (hpos k (by simp)) (hhead k (by simp))
    obtain ⟨w, p, hp, hmap⟩ := ih u (hcolor ▸ htail) (fun j hj => hpos j (by simp [hj]))
    refine ⟨w, .cons hadj p, ?_, ?_⟩
    · apply (Walk.isPath_def _).mpr
      apply List.Nodup.of_map c
      change (List.map c (v :: p.support)).Nodup
      rw [List.map_cons, hmap, hcolor]
      exact hpair.imp (fun h => ne_of_gt h)
    · simp only [Walk.support_cons, List.map_cons, hmap, hcolor]

private theorem forest_color_bound {V : Type} [Fintype V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (c : V → ℕ) (hpos : ∀ v, 0 < c v)
    (hc : ∀ v k, 0 < k → k < c v → ∃ u, G.Adj v u ∧ c u = k) (v : V) :
    2 ^ (c v - 1) ≤ Fintype.card V := by
  classical
  let colors := Finset.Icc 1 (c v - 1)
  have hwalk (s : ↑colors.powerset) :
      ∃ (w : V) (p : G.Walk v w), p.IsPath ∧ p.support.map c = c v :: s.val.sort (· ≥ ·) := by
    apply decreasing_walk G c hc
    · apply List.pairwise_cons.mpr
      constructor
      · intro k hk
        have hk' := Finset.mem_Icc.mp ((Finset.mem_powerset.mp s.prop) ((Finset.mem_sort (· ≥ ·)).mp hk))
        omega
      · exact s.val.sortedGT_sort.pairwise
    · intro k hk
      exact (Finset.mem_Icc.mp ((Finset.mem_powerset.mp s.prop) ((Finset.mem_sort (· ≥ ·)).mp hk))).1
  choose endpoint path hpath hmap using hwalk
  have hinj : Function.Injective endpoint := by
    intro s t heq
    have hpaths : (path s).copy rfl heq = path t := by
      exact congrArg Subtype.val ((hG.subsingleton_path v (endpoint t)).elim
        ⟨(path s).copy rfl heq, by simpa [Walk.isPath_def] using hpath s⟩
        ⟨path t, hpath t⟩)
    have hsupp : (path s).support = (path t).support := by
      simpa using congrArg Walk.support hpaths
    have hmaps : c v :: s.val.sort (· ≥ ·) = c v :: t.val.sort (· ≥ ·) := by
      rw [← hmap s, ← hmap t, hsupp]
    have hsort := List.cons.inj hmaps |>.2
    apply Subtype.ext
    simpa using congrArg List.toFinset hsort
  have hcard := Fintype.card_le_of_injective endpoint hinj
  simpa [colors, Nat.card_Icc] using hcard

end GreedyColoringLCA969.LowerBound

open GreedyColoringLCA969.LowerBound

theorem solution (n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree)
    (c : Fin n → ℕ+) (hc : IsGreedy T c) (v : Fin n) :
    2 ^ ((c v).val - 1) ≤ n := by
  have h := forest_color_bound T hT.isAcyclic (fun w => (c w).val)
    (fun w => (c w).pos) (fun w k hk hkw => by
      obtain ⟨u, hu, hc⟩ := hc.2 w ⟨k, hk⟩ hkw
      exact ⟨u, hu, congrArg PNat.val hc⟩) v
  simpa using h
