-- Prove2me | solution 1 for OAI.RyserCoveringCounterexample.Selection.compatible_selection_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T04:31:35.598638+00:00
-- url     : https://prove2.me/submissions/91c61e8b-766e-4c1f-8ab3-6f7a3ccff32b

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIW2RY002

section
-- module Solutions.OAIW2_RyserCov.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Domination_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Selection

namespace Graph

protected theorem irrefl {V : Type*} {G : Graph V} {v : V} : ¬ G.Adj v v :=
  G.loopless.irrefl v

theorem Adj.symm {V : Type*} {G : Graph V} {v w : V}
    (h : G.Adj v w) : G.Adj w v :=
  G.symm.symm v w h

end Graph

variable {V ι : Type*} [instDecidableEqV : DecidableEq V] [DecidableEq ι]

theorem neighborsIn_subset (G : Graph V) (x : V) (U : Finset V) :
    neighborsIn G x U ⊆ U := by
  intro y hy
  exact (mem_neighborsIn.mp hy).1

theorem neighborsIn_eq_empty_iff {G : Graph V} {x : V} {U : Finset V} :
    neighborsIn G x U = ∅ ↔ ∀ y ∈ U, ¬ G.Adj x y := by
  constructor
  · intro h y hy hxy
    have hm : y ∈ neighborsIn G x U := mem_neighborsIn.mpr ⟨hy, hxy⟩
    simp [h] at hm
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro y hy
    exact h y (mem_neighborsIn.mp hy).1 (mem_neighborsIn.mp hy).2

end RyserCoveringCounterexample.Selection

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Domination_Append
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Selection

variable {V ι : Type*} [instDecidableEqV : DecidableEq V] [DecidableEq ι]

namespace DominationTrace

variable {G : Graph V} {pool : V → ι} {J : Finset ι} {root : ι} {k : ℕ}

theorem append_exists (t : DominationTrace G pool J root k) (v : V) (Y : Finset V)
    (hne : Y.Nonempty)
    (hdis : ∀ a, a < k → Disjoint Y (t.y a))
    (hreal : ∃ U, IsTransversalOn G pool J U ∧
      (∀ a, a < k → neighborsIn G (t.x a) U = t.y a) ∧ neighborsIn G v U = Y)
    (hmin : ∀ U, IsTransversalOn G pool J U →
      (∀ a, a < k → neighborsIn G (t.x a) U = t.y a) →
      Y.card ≤ (neighborsIn G v U).card)
    (horigin : pool v = root ∨ ∃ b, b < k ∧ ∃ w ∈ t.y b, pool v = pool w) :
    Nonempty (DominationTrace G pool J root (k + 1)) := let _ := instDecidableEqV; by
  classical
  let X : ℕ → V := fun a => if a = k then v else t.x a
  let Z : ℕ → Finset V := fun a => if a = k then Y else t.y a
  have hXnew : X k = v := by simp [X]
  have hZnew : Z k = Y := by simp [Z]
  have hXold (a : ℕ) (ha : a < k) : X a = t.x a := by
    simp only [X, ite_eq_right (Nat.ne_of_lt ha)]
  have hZold (a : ℕ) (ha : a < k) : Z a = t.y a := by
    simp only [Z, ite_eq_right (Nat.ne_of_lt ha)]
  refine ⟨⟨X, Z, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro a ha
    by_cases hak : a = k
    · subst a
      rw [hZnew]
      exact hne
    · have ha' : a < k := by omega
      rw [hZold a ha']
      exact t.nonempty a ha'
  · intro a ha b hb hab
    by_cases hak : a = k
    · subst a
      have hb' : b < k := by omega
      rw [hZnew, hZold b hb']
      exact hdis b hb'
    · have ha' : a < k := by omega
      by_cases hbk : b = k
      · subst b
        rw [hZold a ha', hZnew]
        exact (hdis a ha').symm
      · have hb' : b < k := by omega
        rw [hZold a ha', hZold b hb']
        exact t.disjoint a ha' b hb' hab
  · obtain ⟨U, hU, hprev, hnew⟩ := hreal
    refine ⟨U, hU, ?_⟩
    intro a ha
    by_cases hak : a = k
    · subst a
      rw [hXnew, hZnew]
      exact hnew
    · have ha' : a < k := by omega
      rw [hXold a ha', hZold a ha']
      exact hprev a ha'
  · intro a ha U hU hearlier
    by_cases hak : a = k
    · subst a
      rw [hXnew, hZnew]
      apply hmin U hU
      intro b hb
      have heq := hearlier b hb
      rw [hXold b hb, hZold b hb] at heq
      exact heq
    · have ha' : a < k := by omega
      rw [hXold a ha', hZold a ha']
      apply t.minimal a ha' U hU
      intro b hb
      have hbk : b < k := lt_trans hb ha'
      have heq := hearlier b hb
      rw [hXold b hbk, hZold b hbk] at heq
      exact heq
  · intro a ha
    by_cases hak : a = k
    · subst a
      rw [hXnew]
      rcases horigin with hr | ⟨b, hb, w, hw, hp⟩
      · exact Or.inl hr
      · apply Or.inr
        refine ⟨b, hb, w, ?_, hp⟩
        rw [hZold b hb]
        exact hw
    · have ha' : a < k := by omega
      rw [hXold a ha']
      rcases t.origin a ha' with hr | ⟨b, hb, w, hw, hp⟩
      · exact Or.inl hr
      · apply Or.inr
        refine ⟨b, hb, w, ?_, hp⟩
        rw [hZold b (lt_trans hb ha')]
        exact hw

end DominationTrace
end RyserCoveringCounterexample.Selection

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Domination_Counting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Selection

variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]

namespace DominationTrace

variable {G : Graph V} {pool : V → ι} {J : Finset ι} {root : ι} {k : ℕ}

theorem verticesY_subset_of_realized (t : DominationTrace G pool J root k)
    {U : Finset V}
    (hreal : ∀ a, a < k → neighborsIn G (t.x a) U = t.y a) :
    t.verticesY ⊆ U := by
  intro v hv
  obtain ⟨a, ha, hva⟩ := mem_verticesY.mp hv
  have hvn : v ∈ neighborsIn G (t.x a) U := by
    rw [hreal a ha]
    exact hva
  exact neighborsIn_subset G (t.x a) U hvn

theorem pool_injOn_verticesY (t : DominationTrace G pool J root k) :
    Set.InjOn pool (t.verticesY : Set V) := by
  obtain ⟨U, hU, hreal⟩ := t.realized
  intro x hx y hy hxy
  exact hU.2.1 (t.verticesY_subset_of_realized hreal hx)
    (t.verticesY_subset_of_realized hreal hy) hxy

theorem image_verticesY_subset (t : DominationTrace G pool J root k) :
    t.verticesY.image pool ⊆ J := by
  obtain ⟨U, hU, hreal⟩ := t.realized
  intro i hi
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
  rw [← hU.2.2]
  exact Finset.mem_image.mpr ⟨x, t.verticesY_subset_of_realized hreal hx, rfl⟩

theorem length_le_card_verticesY (t : DominationTrace G pool J root k) :
    k ≤ t.verticesY.card := by
  have hdisj :
      ((Finset.range k : Finset ℕ) : Set ℕ).PairwiseDisjoint t.y := by
    intro a ha b hb hab
    exact t.disjoint a (Finset.mem_range.mp ha)
      b (Finset.mem_range.mp hb) hab
  simpa only [verticesY, Finset.card_range] using
    (Finset.card_le_card_biUnion hdisj
      (fun a ha => t.nonempty a (Finset.mem_range.mp ha)))

theorem length_le_card (t : DominationTrace G pool J root k) [Fintype V] :
    k ≤ Fintype.card V :=
  t.length_le_card_verticesY.trans (Finset.card_le_univ t.verticesY)

theorem indices_nonempty (t : DominationTrace G pool J root k) :
    t.indices.Nonempty := by
  exact ⟨root, Finset.mem_insert_self root (t.verticesY.image pool)⟩

theorem mem_indices_iff (t : DominationTrace G pool J root k) {i : ι} :
    i ∈ t.indices ↔
      i = root ∨ ∃ b, b < k ∧ ∃ y ∈ t.y b, i = pool y := by
  unfold indices
  constructor
  · intro hi
    rcases Finset.mem_insert.mp hi with hi | hi
    · exact Or.inl hi
    · obtain ⟨y, hy, hpool⟩ := Finset.mem_image.mp hi
      obtain ⟨b, hb, hyb⟩ := mem_verticesY.mp hy
      exact Or.inr ⟨b, hb, y, hyb, hpool.symm⟩
  · intro hi
    apply Finset.mem_insert.mpr
    rcases hi with hi | ⟨b, hb, y, hy, hpool⟩
    · exact Or.inl hi
    · exact Or.inr (Finset.mem_image.mpr
        ⟨y, mem_verticesY.mpr ⟨b, hb, hy⟩, hpool.symm⟩)

theorem vertices_pool_mem (t : DominationTrace G pool J root k) :
    ∀ x ∈ t.vertices, pool x ∈ t.indices := by
  intro x hx
  change x ∈ t.verticesX ∪ t.verticesY at hx
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨a, ha, rfl⟩ := mem_verticesX.mp hx
    apply (mem_indices_iff t).mpr
    rcases t.origin a ha with hpool | ⟨b, hb, y, hy, hpool⟩
    · exact Or.inl hpool
    · exact Or.inr ⟨b, Nat.lt_trans hb ha, y, hy, hpool⟩
  · change pool x ∈ insert root (t.verticesY.image pool)
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x, hx, rfl⟩)

theorem card_verticesX_le (t : DominationTrace G pool J root k) :
    t.verticesX.card ≤ k := by
  simpa only [verticesX, Finset.card_range] using
    (Finset.card_image_le (s := Finset.range k) (f := t.x))

theorem card_indices (t : DominationTrace G pool J root k) (hroot : root ∉ J) :
    t.indices.card = t.verticesY.card + 1 := by
  have hnot : root ∉ t.verticesY.image pool := by
    intro hmem
    exact hroot (t.image_verticesY_subset hmem)
  rw [indices, Finset.card_insert_of_notMem hnot,
    Finset.card_image_of_injOn t.pool_injOn_verticesY]

theorem card_vertices_le (t : DominationTrace G pool J root k)
    (hroot : root ∉ J) :
    t.vertices.card ≤ 2 * (t.indices.card - 1) := by
  calc
    t.vertices.card ≤ t.verticesX.card + t.verticesY.card :=
      Finset.card_union_le t.verticesX t.verticesY
    _ ≤ t.verticesY.card + t.verticesY.card :=
      Nat.add_le_add_right (t.card_verticesX_le.trans t.length_le_card_verticesY) _
    _ = 2 * (t.indices.card - 1) := by
      rw [t.card_indices hroot]
      omega

end DominationTrace
end RyserCoveringCounterexample.Selection

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Domination_Exchange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Selection

variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]

theorem transversal_exchange {G : Graph V} {pool : V → ι}
    {J : Finset ι} {U : Finset V} {x y : V}
    (hU : IsTransversalOn G pool J U) (hy : y ∈ U)
    (hpool : pool x = pool y) (hfree : ∀ z ∈ U, ¬ G.Adj x z) :
    IsTransversalOn G pool J (insert x (U.erase y)) := by
  rcases hU with ⟨hind, hinj, himage⟩
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb
    rcases Finset.mem_insert.mp ha with hax | haErase
    · rcases Finset.mem_insert.mp hb with hbx | hbErase
      · rw [hax, hbx]
        exact G.irrefl
      · rw [hax]
        exact hfree b (Finset.mem_of_mem_erase hbErase)
    · rcases Finset.mem_insert.mp hb with hbx | hbErase
      · rw [hbx]
        intro hab
        exact hfree a (Finset.mem_of_mem_erase haErase) hab.symm
      · exact hind a (Finset.mem_of_mem_erase haErase)
          b (Finset.mem_of_mem_erase hbErase)
  · intro a ha b hb hab
    rcases Finset.mem_insert.mp ha with hax | haErase
    · rcases Finset.mem_insert.mp hb with hbx | hbErase
      · exact hax.trans hbx.symm
      · have hby : b = y :=
          hinj (Finset.mem_of_mem_erase hbErase) hy
            (hab.symm.trans ((congrArg pool hax).trans hpool))
        exact False.elim ((Finset.mem_erase.mp hbErase).1 hby)
    · rcases Finset.mem_insert.mp hb with hbx | hbErase
      · have hay : a = y :=
          hinj (Finset.mem_of_mem_erase haErase) hy
            (hab.trans ((congrArg pool hbx).trans hpool))
        exact False.elim ((Finset.mem_erase.mp haErase).1 hay)
      · exact hinj (Finset.mem_of_mem_erase haErase)
          (Finset.mem_of_mem_erase hbErase) hab
  · rw [← himage]
    ext i
    constructor
    · intro hi
      rcases Finset.mem_image.mp hi with ⟨z, hz, hzi⟩
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact Finset.mem_image.mpr ⟨y, hy, hpool.symm.trans hzi⟩
      · exact Finset.mem_image.mpr ⟨z, Finset.mem_of_mem_erase hz, hzi⟩
    · intro hi
      rcases Finset.mem_image.mp hi with ⟨z, hz, hzi⟩
      by_cases hzy : z = y
      · subst z
        exact Finset.mem_image.mpr
          ⟨x, Finset.mem_insert_self x _, hpool.trans hzi⟩
      · exact Finset.mem_image.mpr
          ⟨z, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hzy, hz⟩), hzi⟩

theorem neighborsIn_exchange (G : Graph V) (a x y : V) (U : Finset V)
    (hax : ¬ G.Adj a x) :
    neighborsIn G a (insert x (U.erase y)) = (neighborsIn G a U).erase y := by
  ext z
  simp only [mem_neighborsIn, Finset.mem_insert, Finset.mem_erase]
  constructor
  · rintro ⟨hz, haz⟩
    rcases hz with rfl | hz
    · exact (hax haz).elim
    · exact ⟨hz.1, hz.2, haz⟩
  · intro hz
    exact ⟨Or.inr ⟨hz.1, hz.2.1⟩, hz.2.2⟩

theorem neighborsIn_exchange_eq_of_not_mem (G : Graph V)
    (a x y : V) (U : Finset V) (hax : ¬ G.Adj a x)
    (hy : y ∉ neighborsIn G a U) :
    neighborsIn G a (insert x (U.erase y)) = neighborsIn G a U := by
  rw [neighborsIn_exchange G a x y U hax, Finset.erase_eq_of_notMem hy]

theorem card_neighborsIn_exchange_lt (G : Graph V)
    (a x y : V) (U : Finset V) (hax : ¬ G.Adj a x)
    (hy : y ∈ neighborsIn G a U) :
    (neighborsIn G a (insert x (U.erase y))).card < (neighborsIn G a U).card := by
  rw [neighborsIn_exchange G a x y U hax]
  exact Finset.card_erase_lt_of_mem hy

end RyserCoveringCounterexample.Selection

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Domination_Seed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Selection

variable {V ι : Type*} [instDecidableEqV : DecidableEq V] [DecidableEq ι]
variable {G : Graph V} {pool : V → ι}

theorem transversal_insert_new {J : Finset ι} {U : Finset V} {root : ι} {x : V}
    (hU : IsTransversalOn G pool J U) (hroot : root ∉ J)
    (hpool : pool x = root) (hfree : ∀ y ∈ U, ¬ G.Adj x y) :
    IsTransversalOn G pool (insert root J) (insert x U) := by
  have hpool_ne (y : V) (hy : y ∈ U) : pool y ≠ root := by
    intro heq
    apply hroot
    rw [← hU.2.2]
    exact Finset.mem_image.mpr ⟨y, hy, heq⟩
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb
    rcases Finset.mem_insert.mp ha with rfl | haU
    · rcases Finset.mem_insert.mp hb with rfl | hbU
      · exact G.irrefl
      · exact hfree b hbU
    · rcases Finset.mem_insert.mp hb with rfl | hbU
      · intro hab
        exact hfree a haU hab.symm
      · exact hU.1 a haU b hbU
  · intro a ha b hb hab
    change a ∈ insert x U at ha
    change b ∈ insert x U at hb
    rcases Finset.mem_insert.mp ha with rfl | haU
    · rcases Finset.mem_insert.mp hb with rfl | hbU
      · rfl
      · exact (hpool_ne b hbU (hab.symm.trans hpool)).elim
    · rcases Finset.mem_insert.mp hb with rfl | hbU
      · exact (hpool_ne a haU (hab.trans hpool)).elim
      · exact hU.2.1 haU hbU hab
  · rw [Finset.image_insert, hU.2.2, hpool]

theorem exists_unextendable_transversal [Fintype ι]
    (hfull : ¬ ∃ U : Finset V, IsTransversalOn G pool Finset.univ U) :
    ∃ root : ι, ∃ J : Finset ι, ∃ U : Finset V,
      root ∉ J ∧ IsTransversalOn G pool J U ∧
        ¬ ∃ U' : Finset V, IsTransversalOn G pool (insert root J) U' := let _ := instDecidableEqV; by
  classical
  let candidates : Finset (Finset ι) :=
    Finset.univ.filter (fun J => ∃ U : Finset V, IsTransversalOn G pool J U)
  have hempty : (∅ : Finset ι) ∈ candidates := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ∅, ?_⟩
    simp [IsTransversalOn, Set.InjOn]
  obtain ⟨J, hJ, hmax⟩ := Finset.exists_max_image candidates
    (fun J : Finset ι => J.card) ⟨∅, hempty⟩
  obtain ⟨U, hU⟩ := (Finset.mem_filter.mp hJ).2
  have hJne : J ≠ Finset.univ := by
    intro heq
    apply hfull
    exact ⟨U, heq ▸ hU⟩
  obtain ⟨root, hroot⟩ : ∃ root : ι, root ∉ J := by
    by_contra hnone
    apply hJne
    apply Finset.eq_univ_iff_forall.mpr
    intro i
    by_contra hi
    exact hnone ⟨i, hi⟩
  refine ⟨root, J, U, hroot, hU, ?_⟩
  intro hExt
  have hmem : insert root J ∈ candidates :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hExt⟩
  have hle := hmax (insert root J) hmem
  rw [Finset.card_insert_of_notMem hroot] at hle
  exact Nat.not_succ_le_self J.card hle

end RyserCoveringCounterexample.Selection

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Domination_Nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Selection

variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]

namespace DominationTrace

variable {G : Graph V} {pool : V → ι} {J : Finset ι}
    {root : ι} {k : ℕ}

theorem neighbors_nonempty (t : DominationTrace G pool J root k)
    (hroot : root ∉ J)
    (hno : ¬ ∃ U', IsTransversalOn G pool (insert root J) U')
    {v : V} {U : Finset V} (hU : IsTransversalOn G pool J U)
    (hreal : ∀ a, a < k → neighborsIn G (t.x a) U = t.y a)
    (hvpool : pool v ∈ t.indices)
    (hvfree : ∀ z ∈ t.vertices, ¬ G.Adj v z) :
    (neighborsIn G v U).Nonempty := by
  apply Finset.nonempty_iff_ne_empty.mpr
  intro hempty
  have hfreeU := neighborsIn_eq_empty_iff.mp hempty
  have hax (a : ℕ) (ha : a < k) : ¬ G.Adj (t.x a) v := by
    have hmem : t.x a ∈ t.vertices := by
      change t.x a ∈ t.verticesX ∪ t.verticesY
      exact Finset.mem_union_left _ (mem_verticesX.mpr ⟨a, ha, rfl⟩)
    intro hav
    exact hvfree (t.x a) hmem hav.symm
  change pool v ∈ insert root (t.verticesY.image pool) at hvpool
  rcases Finset.mem_insert.mp hvpool with hvroot | hvimage
  · exact hno ⟨insert v U, transversal_insert_new hU hroot hvroot hfreeU⟩
  · obtain ⟨y, hy, hypool⟩ := Finset.mem_image.mp hvimage
    obtain ⟨b, hb, hyb⟩ := mem_verticesY.mp hy
    have hyn : y ∈ neighborsIn G (t.x b) U := by
      rw [hreal b hb]
      exact hyb
    have hyU : y ∈ U := (mem_neighborsIn.mp hyn).1
    have hU' := transversal_exchange hU hyU hypool.symm hfreeU
    have hearlier : ∀ a, a < b →
        neighborsIn G (t.x a) (insert v (U.erase y)) = t.y a := by
      intro a ha
      have hak : a < k := lt_trans ha hb
      have hyold : y ∉ neighborsIn G (t.x a) U := by
        rw [hreal a hak]
        intro hya
        exact Finset.disjoint_left.mp
          (t.disjoint a hak b hb (Nat.ne_of_lt ha)) hya hyb
      exact (neighborsIn_exchange_eq_of_not_mem G (t.x a) v y U
        (hax a hak) hyold).trans (hreal a hak)
    have hmin := t.minimal b hb (insert v (U.erase y)) hU' hearlier
    have hstrict := card_neighborsIn_exchange_lt G (t.x b) v y U (hax b hb) hyn
    rw [hreal b hb] at hstrict
    exact Nat.not_lt_of_ge hmin hstrict

end DominationTrace
end RyserCoveringCounterexample.Selection

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Domination_Extension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Selection

variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]

namespace DominationTrace

variable {G : Graph V} {pool : V → ι} {J : Finset ι} {root : ι} {k : ℕ}

theorem extend [Fintype V] (t : DominationTrace G pool J root k)
    (hroot : root ∉ J)
    (hno : ¬ ∃ U', IsTransversalOn G pool (insert root J) U')
    (hnocert : ¬ DominationCertificate G pool) :
    Nonempty (DominationTrace G pool J root (k + 1)) := by
  classical
  have hnotdom : ¬ DominatesOn G pool t.indices t.vertices := by
    intro hd
    exact hnocert ⟨t.indices, t.vertices, t.indices_nonempty,
      t.vertices_pool_mem, t.card_vertices_le hroot, hd⟩
  unfold DominatesOn at hnotdom
  push Not at hnotdom
  obtain ⟨v, hvpool, hvout, hvfree⟩ := hnotdom
  let candidates : Finset (Finset V) := Finset.univ.filter
    (fun U => IsTransversalOn G pool J U ∧
      ∀ a, a < k → neighborsIn G (t.x a) U = t.y a)
  have hcandidates : candidates.Nonempty := by
    obtain ⟨U, hU, hreal⟩ := t.realized
    exact ⟨U, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hU, hreal⟩⟩
  obtain ⟨U, hUc, hmin⟩ := Finset.exists_min_image candidates
    (fun U => (neighborsIn G v U).card) hcandidates
  have hU := (Finset.mem_filter.mp hUc).2
  have hne := t.neighbors_nonempty hroot hno hU.1 hU.2 hvpool hvfree
  apply t.append_exists v (neighborsIn G v U) hne
  · intro a ha
    apply Finset.disjoint_left.mpr
    intro z hznew hzold
    have hzt : z ∈ t.vertices := by
      change z ∈ t.verticesX ∪ t.verticesY
      exact Finset.mem_union_right _ (mem_verticesY.mpr ⟨a, ha, hzold⟩)
    exact hvfree z hzt (mem_neighborsIn.mp hznew).2
  · exact ⟨U, hU.1, hU.2, rfl⟩
  · intro U' hU' hreal'
    exact hmin U' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hU', hreal'⟩)
  · exact (t.mem_indices_iff).mp hvpool

end DominationTrace
end RyserCoveringCounterexample.Selection

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Domination_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Selection

variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]

theorem domination_certificate_of_no_transversal [Fintype V] [Fintype ι]
    (G : Graph V) (pool : V → ι) (hpool : Function.Surjective pool)
    (hno : ¬ ∃ U, IsTransversalOn G pool Finset.univ U) :
    DominationCertificate G pool := by
  classical
  by_contra hnocert
  obtain ⟨root, J, U, hroot, hU, hnoJ⟩ := exists_unextendable_transversal hno
  obtain ⟨v, hv⟩ := hpool root
  have htraces : ∀ k, Nonempty (DominationTrace G pool J root k) := by
    intro k
    induction k with
    | zero => exact ⟨DominationTrace.empty v hU⟩
    | succ k ih =>
      obtain ⟨t⟩ := ih
      exact t.extend hroot hnoJ hnocert
  obtain ⟨t⟩ := htraces (Fintype.card V + 1)
  exact Nat.not_succ_le_self (Fintype.card V) t.length_le_card

theorem domination_of_no_transversal [Fintype V] [Fintype ι]
    (G : Graph V) (pool : V → ι) (hpool : Function.Surjective pool)
    (hno : ¬ ∃ U, IsTransversalOn G pool Finset.univ U) :
    ∃ I : Finset ι, ∃ T : Finset V, I.Nonempty ∧
      T ⊆ Finset.univ.filter (fun x => pool x ∈ I) ∧
      T.card ≤ 2 * (I.card - 1) ∧ DominatesOn G pool I T := by
  obtain ⟨I, T, hI, hT, hcard, hdom⟩ :=
    domination_certificate_of_no_transversal G pool hpool hno
  refine ⟨I, T, hI, ?_, hcard, hdom⟩
  intro x hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT x hx⟩

end RyserCoveringCounterexample.Selection

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Geometry_AffineJoins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample

variable {F : Type*} [Field F]

section Join

variable [DecidableEq F]

theorem eq_joinLine_of_incidence {p q : Point F} {l : AffineLine F}
    (hpq : p ≠ q) (hpl : Incidence p l) (hql : Incidence q l) :
    l = joinLine p q :=
  line_eq_of_two_incident_points hpq hpl hql
    (incidence_joinLine_left p q) (incidence_joinLine_right p q)

theorem projection_eq_iff_eq_joinDirection {p q : Point F} (hpq : p ≠ q)
    (d : Direction F) :
    projection d p = projection d q ↔ d = joinDirection p q := by
  constructor
  · intro hd
    have hpl : Incidence p (lineThrough d p) := rfl
    have hql : Incidence q (lineThrough d p) := by
      change projection d q = projection d p
      exact hd.symm
    have hl := eq_joinLine_of_incidence hpq hpl hql
    have hf := congrArg Prod.fst hl
    change d = joinDirection p q at hf
    exact hf
  · intro hd
    subst d
    have hq := incidence_joinLine_right p q
    change projection (joinDirection p q) q = projection (joinDirection p q) p at hq
    exact hq.symm

end Join

end RyserCoveringCounterexample

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Geometry_Cardinality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample

variable {F : Type*} [instFieldF : Field F] [Fintype F] [instDecidableEqF : DecidableEq F]

theorem card_projection_fiber (d : Direction F) (b : F) :
    (Finset.univ.filter (fun p : Point F => projection d p = b)).card =
      Fintype.card F :=
  card_linePoints (d, b)

end RyserCoveringCounterexample

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Geometry_ProjectionPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample

open scoped BigOperators

variable {F : Type*} [Field F]

theorem sum_projection_eq_indicator [Fintype F] [DecidableEq F]
    (p q : Point F) :
    (∑ d : Direction F, if projection d p = projection d q then (1 : ℝ) else 0) =
      if p = q then (Fintype.card F : ℝ) + 1 else 1 := by
  classical
  by_cases hpq : p = q
  · subst q
    simp [Nat.cast_add]
  · rw [ite_eq_right hpq]
    calc
      (∑ d : Direction F, if projection d p = projection d q then (1 : ℝ) else 0) =
          ∑ d : Direction F, if d = joinDirection p q then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro d _
        simp only [projection_eq_iff_eq_joinDirection hpq d]
      _ = 1 := Fintype.sum_ite_eq' _ _

end RyserCoveringCounterexample

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Geometry_SliceEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample

open scoped BigOperators

variable {F : Type*} [Field F] [instFintypeF : Fintype F] [DecidableEq F]

theorem sliceCount_le_card_field (U : Finset (Point F)) (d : Direction F) (t : F) :
    sliceCount U d t ≤ Fintype.card F := by
  rw [← card_projection_fiber d t]
  apply Finset.card_le_card
  intro p hp
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩

theorem sliceCount_eq_sum_indicator (U : Finset (Point F)) (d : Direction F) (t : F) :
    (sliceCount U d t : ℝ) =
      ∑ p ∈ U, if projection d p = t then (1 : ℝ) else 0 := let _ := instFintypeF; by
  exact Finset.natCast_card_filter _ _

theorem sum_sliceCount (U : Finset (Point F)) (d : Direction F) :
    (∑ t : F, (sliceCount U d t : ℝ)) = (U.card : ℝ) := by
  classical
  simp_rw [sliceCount_eq_sum_indicator]
  rw [Finset.sum_comm]
  simp

private theorem sum_projection_indicator_mul (d : Direction F) (p p' : Point F) :
    (∑ t : F, (if projection d p = t then (1 : ℝ) else 0) *
      (if projection d p' = t then (1 : ℝ) else 0)) =
      if projection d p = projection d p' then (1 : ℝ) else 0 := by
  classical
  calc
    _ = (if projection d p = projection d p then (1 : ℝ) else 0) *
        (if projection d p' = projection d p then (1 : ℝ) else 0) := by
      apply Finset.sum_eq_single (projection d p)
      · intro t _ ht
        simp [Ne.symm ht]
      · simp
    _ = _ := by simp [eq_comm]

theorem sum_sliceCount_sq (U : Finset (Point F)) (d : Direction F) :
    (∑ t : F, (sliceCount U d t : ℝ) ^ 2) =
      ∑ p ∈ U, ∑ p' ∈ U,
        if projection d p = projection d p' then (1 : ℝ) else 0 := by
  classical
  simp_rw [sliceCount_eq_sum_indicator, pow_two, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p' hp'
  exact sum_projection_indicator_mul d p p'

theorem sum_all_sliceCount_sq (U : Finset (Point F)) :
    (∑ d : Direction F, ∑ t : F, (sliceCount U d t : ℝ) ^ 2) =
      (U.card : ℝ) ^ 2 + (Fintype.card F : ℝ) * (U.card : ℝ) := by
  classical
  simp_rw [sum_sliceCount_sq]
  rw [Finset.sum_comm]
  calc
    (∑ p ∈ U, ∑ d : Direction F, ∑ p' ∈ U,
        if projection d p = projection d p' then (1 : ℝ) else 0) =
        ∑ p ∈ U, ∑ p' ∈ U,
          if p = p' then (Fintype.card F : ℝ) + 1 else 1 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p' hp'
      exact sum_projection_eq_indicator p p'
    _ = ∑ p ∈ U, ((Fintype.card F : ℝ) + (U.card : ℝ)) := by
      apply Finset.sum_congr rfl
      intro p hp
      calc
        _ = ∑ p' ∈ U, ((if p' = p then (Fintype.card F : ℝ) else 0) + 1) := by
          apply Finset.sum_congr rfl
          intro p' hp'
          by_cases h : p' = p
          · subst p'
            simp
          · simp [h, Ne.symm h]
        _ = _ := by simp [Finset.sum_add_distrib, hp]
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

theorem sliceEnergy_nonneg (U : Finset (Point F)) (d : Direction F) :
    0 ≤ sliceEnergy U d := by
  unfold sliceEnergy
  positivity

theorem sliceEnergy_eq (U : Finset (Point F)) (d : Direction F) :
    sliceEnergy U d =
      (∑ t : F, (sliceCount U d t : ℝ) ^ 2) / (Fintype.card F : ℝ) -
        (U.card : ℝ) ^ 2 / (Fintype.card F : ℝ) ^ 2 := by
  have hq : (Fintype.card F : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr Fintype.card_pos)
  have hcenter :
      (∑ t : F, ((sliceCount U d t : ℝ) -
        (U.card : ℝ) / (Fintype.card F : ℝ)) ^ 2) =
      (∑ t : F, (sliceCount U d t : ℝ) ^ 2) -
        (2 * ((U.card : ℝ) / (Fintype.card F : ℝ))) * (U.card : ℝ) +
        (Fintype.card F : ℝ) * ((U.card : ℝ) / (Fintype.card F : ℝ)) ^ 2 := by
    calc
      _ = ∑ t : F, ((sliceCount U d t : ℝ) ^ 2 -
          (2 * ((U.card : ℝ) / (Fintype.card F : ℝ))) * (sliceCount U d t : ℝ) +
          ((U.card : ℝ) / (Fintype.card F : ℝ)) ^ 2) := by
        apply Finset.sum_congr rfl
        intro t ht
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, sum_sliceCount, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul]
  unfold sliceEnergy
  rw [hcenter]
  field_simp
  ring

theorem sum_sliceEnergy (U : Finset (Point F)) :
    (∑ d : Direction F, sliceEnergy U d) =
      (U.card : ℝ) - (U.card : ℝ) ^ 2 / (Fintype.card F : ℝ) ^ 2 := by
  have hq : (Fintype.card F : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr Fintype.card_pos)
  simp_rw [sliceEnergy_eq]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, sum_all_sliceCount_sq]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    card_direction, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

theorem sum_sliceEnergy_le_card (U : Finset (Point F)) :
    (∑ d : Direction F, sliceEnergy U d) ≤ (U.card : ℝ) := by
  rw [sum_sliceEnergy]
  exact sub_le_self _ (div_nonneg (sq_nonneg _) (sq_nonneg _))

theorem sum_sliceEnergy_le_sq_card (U : Finset (Point F)) :
    (∑ d : Direction F, sliceEnergy U d) ≤ (Fintype.card F : ℝ) ^ 2 := by
  apply (sum_sliceEnergy_le_card U).trans
  have h := U.card_le_univ
  rw [card_point] at h
  exact_mod_cast h

end RyserCoveringCounterexample

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Probability_Finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample

namespace FiniteLaw

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem expectation_add (μ : FiniteLaw Ω) (f g : Ω → ℝ) :
    μ.expectation (fun ω => f ω + g ω) = μ.expectation f + μ.expectation g := by
  simp [expectation, mul_add, Finset.sum_add_distrib]

theorem expectation_sub (μ : FiniteLaw Ω) (f g : Ω → ℝ) :
    μ.expectation (fun ω => f ω - g ω) = μ.expectation f - μ.expectation g := by
  simp [expectation, mul_sub, Finset.sum_sub_distrib]

theorem expectation_smul (μ : FiniteLaw Ω) (c : ℝ) (f : Ω → ℝ) :
    μ.expectation (fun ω => c * f ω) = c * μ.expectation f := by
  simp [expectation, Finset.mul_sum, mul_left_comm]

theorem expectation_nonneg (μ : FiniteLaw Ω) {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω) :
    0 ≤ μ.expectation f :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (μ.nonneg ω) (hf ω)

theorem prob_nonneg (μ : FiniteLaw Ω) (P : Ω → Prop) : 0 ≤ μ.prob P := by
  classical
  exact Finset.sum_nonneg fun ω _ => by split_ifs <;> simp [μ.nonneg]

theorem prob_mono (μ : FiniteLaw Ω) {P Q : Ω → Prop} (hPQ : ∀ ω, P ω → Q ω) :
    μ.prob P ≤ μ.prob Q := by
  classical
  apply Finset.sum_le_sum
  intro ω _
  by_cases hp : P ω
  · simp [hp, hPQ ω hp]
  · by_cases hq : Q ω <;> simp [hp, hq, μ.nonneg ω]

theorem prob_le_one (μ : FiniteLaw Ω) (P : Ω → Prop) : μ.prob P ≤ 1 := by
  simpa using μ.prob_mono (Q := fun _ => True) (fun _ _ => trivial)

theorem prob_ge_le_expectation_div (μ : FiniteLaw Ω) (f : Ω → ℝ)
    (hf : ∀ ω, 0 ≤ f ω) {t : ℝ} (ht : 0 < t) :
    μ.prob (fun ω => t ≤ f ω) ≤ μ.expectation f / t := by
  have h := μ.prob_le_expectation (fun ω => t ≤ f ω) (fun ω => t⁻¹ * f ω)
    (fun ω => mul_nonneg (inv_nonneg.mpr ht.le) (hf ω))
    (fun ω hω => by simpa [ht.ne'] using mul_le_mul_of_nonneg_left hω (inv_nonneg.mpr ht.le))
  rw [expectation_smul] at h
  simpa [div_eq_mul_inv, mul_comm] using h

theorem expectation_prod (μ : FiniteLaw Ω) (ν : FiniteLaw Γ) (f : Ω × Γ → ℝ) :
    (μ.prod ν).expectation f = μ.expectation (fun ω => ν.expectation (fun γ => f (ω, γ))) := by
  simp [expectation, prod, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

theorem eq_uniform_of_weight_eq [Nonempty Ω] (mu : FiniteLaw Ω)
    (h : ∀ x y, mu.weight x = mu.weight y) : mu = uniform Ω := by
  apply ext_weight
  funext x
  change mu.weight x = (Fintype.card Ω : ℝ)⁻¹
  have hN : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hsum : (Fintype.card Ω : ℝ) * mu.weight x = 1 := by
    calc
      _ = ∑ y : Ω, mu.weight x := by simp
      _ = ∑ y : Ω, mu.weight y :=
        Finset.sum_congr rfl (fun y _ => (h y x).symm)
      _ = 1 := mu.total
  calc
    mu.weight x = (Fintype.card Ω : ℝ)⁻¹ *
        ((Fintype.card Ω : ℝ) * mu.weight x) := by
      rw [← mul_assoc, inv_mul_cancel₀ hN, one_mul]
    _ = (Fintype.card Ω : ℝ)⁻¹ := by rw [hsum, mul_one]

theorem uniform_expectation (Ω : Type*) [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ) :
    (uniform Ω).expectation f = (∑ x, f x) / Fintype.card Ω := by
  change (∑ x, (Fintype.card Ω : ℝ)⁻¹ * f x) = _
  rw [← Finset.mul_sum, div_eq_mul_inv, mul_comm]

end FiniteLaw

end RyserCoveringCounterexample

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Probability_Product
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.FiniteLaw

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem map_uniform_equiv [Nonempty Ω] [Nonempty Γ] (e : Ω ≃ Γ) :
    (uniform Ω).map e = uniform Γ := by
  classical
  apply ext_weight
  funext y
  simp [map, uniform, ← e.eq_symm_apply, Fintype.card_congr e]

theorem uniform_prod (Ω Γ : Type*) [Fintype Ω] [Fintype Γ]
    [Nonempty Ω] [Nonempty Γ] :
    uniform (Ω × Γ) = (uniform Ω).prod (uniform Γ) :=
  (eq_uniform_of_weight_eq ((uniform Ω).prod (uniform Γ)) (fun _ _ => rfl)).symm

theorem pi_uniform {I : Type*} [Fintype I] [DecidableEq I] {A : I → Type*}
    [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] :
    pi (fun i => uniform (A i)) = uniform (∀ i, A i) :=
  eq_uniform_of_weight_eq (pi (fun i => uniform (A i))) (fun _ _ => rfl)

theorem prob_prod_average (mu : FiniteLaw Ω) (nu : FiniteLaw Γ)
    (P : Ω × Γ → Prop) :
    (mu.prod nu).prob P = mu.expectation (fun x => nu.prob (fun y => P (x, y))) := by
  simp only [prob_eq_expectation]
  exact expectation_prod mu nu (fun z => if P z then 1 else 0)

theorem prob_prod_le_bad_add (mu : FiniteLaw Ω) (nu : FiniteLaw Γ)
    (P : Ω × Γ → Prop) (Bad : Ω → Prop) (b : ℝ) (hb : 0 ≤ b)
    (hgood : ∀ x, ¬Bad x → nu.prob (fun y => P (x, y)) ≤ b) :
    (mu.prod nu).prob P ≤ mu.prob Bad + b := by
  classical
  rw [prob_prod_average]
  calc
    _ ≤ mu.expectation (fun x => (if Bad x then (1 : ℝ) else 0) + b) := by
      apply expectation_mono
      intro x
      by_cases hx : Bad x
      · simp only [ite_eq_left hx]
        exact (nu.prob_le_one _).trans (le_add_of_nonneg_right hb)
      · simpa only [ite_eq_right hx, zero_add] using hgood x hx
    _ = mu.prob Bad + b := by
      rw [expectation_add, expectation_const, ← prob_eq_expectation]

theorem prob_uniform_prod_equiv {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Nonempty X] [Nonempty Y] [Nonempty Z]
    (e : X ≃ Y × Z) (P : X → Prop) :
    (uniform X).prob P = (uniform Y).expectation
      (fun x => (uniform Z).prob (fun y => P (e.symm (x, y)))) := by
  calc
    _ = ((uniform X).map e).prob (fun z => P (e.symm z)) := by
      rw [prob_map]
      simp only [Equiv.symm_apply_apply]
    _ = _ := by rw [map_uniform_equiv, uniform_prod, prob_prod_average]

section UniformSplit

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty Ω]

theorem prob_pi_uniform_split (p : I → Prop) [DecidablePred p]
    (P : (I → Ω) → Prop) :
    (pi (fun _ : I => uniform Ω)).prob P =
    (uniform ({i : I // p i} → Ω)).expectation (fun x =>
      (uniform ({i : I // ¬p i} → Ω)).prob (fun y =>
        P ((Equiv.piEquivPiSubtypeProd p (fun _ => Ω)).symm (x, y)))) := by
  rw [pi_uniform]
  exact prob_uniform_prod_equiv (Equiv.piEquivPiSubtypeProd p (fun _ => Ω)) P

theorem prob_pi_uniform_split_le (p : I → Prop) [DecidablePred p]
    (P : (I → Ω) → Prop) (b : ℝ)
    (h : ∀ x : {i : I // p i} → Ω,
      (uniform ({i : I // ¬p i} → Ω)).prob (fun y =>
        P ((Equiv.piEquivPiSubtypeProd p (fun _ => Ω)).symm (x, y))) ≤ b) :
    (pi (fun _ : I => uniform Ω)).prob P ≤ b := by
  rw [prob_pi_uniform_split p P]
  calc
    _ ≤ (uniform ({i : I // p i} → Ω)).expectation (fun _ => b) :=
      expectation_mono _ h
    _ = b := expectation_const _ b

end UniformSplit

end RyserCoveringCounterexample.FiniteLaw

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Probability_Variance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section

namespace RyserCoveringCounterexample
namespace FiniteLaw

variable {Ω I : Type*} [Fintype Ω]

theorem variance_nonneg (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    0 ≤ μ.variance f :=
  μ.expectation_nonneg (fun ω => sq_nonneg (f ω - μ.expectation f))

theorem covariance_self (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    μ.covariance f f = μ.variance f := by
  simp only [covariance, variance, pow_two]

theorem variance_add_sq_mean_sub_eq (μ : FiniteLaw Ω)
    (f : Ω → ℝ) (b : ℝ) :
    μ.variance f + (μ.expectation f - b) ^ 2 =
      μ.expectation (fun ω => (f ω - b) ^ 2) := by
  calc
    μ.variance f + (μ.expectation f - b) ^ 2 =
        μ.expectation (fun ω =>
          (f ω - μ.expectation f) ^ 2 +
            (2 * (μ.expectation f - b)) * (f ω - μ.expectation f) +
            (μ.expectation f - b) ^ 2) := by
      rw [expectation_add, expectation_add, expectation_smul,
        expectation_sub, expectation_const, expectation_const]
      simp [variance]
    _ = μ.expectation (fun ω => (f ω - b) ^ 2) := by
      congr 1
      funext ω
      ring

theorem variance_le_expectation_sub_const_sq (μ : FiniteLaw Ω)
    (f : Ω → ℝ) (b : ℝ) :
    μ.variance f ≤ μ.expectation (fun ω => (f ω - b) ^ 2) := by
  have h := μ.variance_add_sq_mean_sub_eq f b
  nlinarith [sq_nonneg (μ.expectation f - b)]

theorem variance_le_expectation_sq (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    μ.variance f ≤ μ.expectation (fun ω => (f ω) ^ 2) := by
  simpa only [sub_zero] using μ.variance_le_expectation_sub_const_sq f 0

theorem covariance_eq_expectation_mul_sub_mul (μ : FiniteLaw Ω)
    (f g : Ω → ℝ) :
    μ.covariance f g = μ.expectation (fun ω => f ω * g ω) -
      μ.expectation f * μ.expectation g := by
  calc
    μ.covariance f g = μ.expectation (fun ω =>
        f ω * g ω - μ.expectation g * f ω - μ.expectation f * g ω +
          μ.expectation f * μ.expectation g) := by
      unfold covariance
      congr 1
      funext ω
      ring
    _ = μ.expectation (fun ω => f ω * g ω) -
        μ.expectation f * μ.expectation g := by
      rw [expectation_add, expectation_sub, expectation_sub,
        expectation_smul, expectation_smul, expectation_const]
      ring

theorem variance_add_le (μ : FiniteLaw Ω) (f g : Ω → ℝ) :
    μ.variance (fun ω => f ω + g ω) ≤
      2 * μ.variance f + 2 * μ.variance g := by
  calc
    μ.variance (fun ω => f ω + g ω) = μ.expectation (fun ω =>
        ((f ω - μ.expectation f) + (g ω - μ.expectation g)) ^ 2) := by
      unfold variance
      rw [expectation_add]
      congr 1
      funext ω
      ring
    _ ≤ μ.expectation (fun ω =>
        2 * (f ω - μ.expectation f) ^ 2 +
          2 * (g ω - μ.expectation g) ^ 2) := by
      apply μ.expectation_mono
      intro ω
      nlinarith [sq_nonneg ((f ω - μ.expectation f) -
        (g ω - μ.expectation g))]
    _ = 2 * μ.variance f + 2 * μ.variance g := by
      rw [expectation_add, expectation_smul, expectation_smul]
      rfl

theorem expectation_finset_sum (μ : FiniteLaw Ω) (S : Finset I)
    (f : I → Ω → ℝ) :
    μ.expectation (fun ω => ∑ i ∈ S, f i ω) =
      ∑ i ∈ S, μ.expectation (f i) := by
  simp only [expectation, Finset.mul_sum]
  exact Finset.sum_comm

theorem covariance_finset_sum_left (μ : FiniteLaw Ω) (S : Finset I)
    (f : I → Ω → ℝ) (g : Ω → ℝ) :
    μ.covariance (fun ω => ∑ i ∈ S, f i ω) g =
      ∑ i ∈ S, μ.covariance (f i) g := by
  unfold covariance
  rw [expectation_finset_sum μ S f]
  simp_rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  exact expectation_finset_sum μ S
    (fun i ω => (f i ω - μ.expectation (f i)) * (g ω - μ.expectation g))

theorem covariance_finset_sum_right (μ : FiniteLaw Ω) (S : Finset I)
    (g : Ω → ℝ) (f : I → Ω → ℝ) :
    μ.covariance g (fun ω => ∑ i ∈ S, f i ω) =
      ∑ i ∈ S, μ.covariance g (f i) := by
  unfold covariance
  rw [expectation_finset_sum μ S f]
  simp_rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  exact expectation_finset_sum μ S
    (fun i ω => (g ω - μ.expectation g) * (f i ω - μ.expectation (f i)))

theorem variance_sum_le (μ : FiniteLaw Ω) (S : Finset I) (f : I → Ω → ℝ) :
    μ.variance (fun ω => ∑ i ∈ S, f i ω) ≤
      (S.card : ℝ) * ∑ i ∈ S, μ.variance (f i) := by
  classical
  calc
    μ.variance (fun ω => ∑ i ∈ S, f i ω) =
        μ.expectation (fun ω =>
          (∑ i ∈ S, (f i ω - μ.expectation (f i))) ^ 2) := by
      simp only [variance, expectation_finset_sum, Finset.sum_sub_distrib]
    _ ≤ μ.expectation (fun ω =>
        (S.card : ℝ) * ∑ i ∈ S, (f i ω - μ.expectation (f i)) ^ 2) := by
      apply μ.expectation_mono
      intro ω
      simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using
        (Finset.sum_mul_sq_le_sq_mul_sq S (fun _ : I => (1 : ℝ))
          (fun i => f i ω - μ.expectation (f i)))
    _ = (S.card : ℝ) * ∑ i ∈ S, μ.variance (f i) := by
      simp only [expectation_smul, expectation_finset_sum, variance]

theorem variance_sum_of_pairwise_covariance_zero
    (μ : FiniteLaw Ω) (S : Finset I) (f : I → Ω → ℝ)
    (hcov : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → μ.covariance (f i) (f j) = 0) :
    μ.variance (fun ω => ∑ i ∈ S, f i ω) =
      ∑ i ∈ S, μ.variance (f i) := by
  classical
  rw [← covariance_self μ (fun ω => ∑ i ∈ S, f i ω), covariance_finset_sum_left]
  apply Finset.sum_congr rfl
  intro i hi
  rw [covariance_finset_sum_right]
  calc
    (∑ j ∈ S, μ.covariance (f i) (f j)) = μ.covariance (f i) (f i) := by
      apply Finset.sum_eq_single i
      · intro j hj hji
        exact hcov i hi j hj (Ne.symm hji)
      · intro hnot
        exact (hnot hi).elim
    _ = μ.variance (f i) := covariance_self μ (f i)

theorem variance_le_sq_of_bounds (μ : FiniteLaw Ω) (f : Ω → ℝ) {L : ℝ}
    (hf0 : ∀ ω, 0 ≤ f ω) (hfL : ∀ ω, f ω ≤ L) :
    μ.variance f ≤ L ^ 2 := by
  calc
    μ.variance f ≤ μ.expectation (fun ω => (f ω) ^ 2) :=
      μ.variance_le_expectation_sq f
    _ ≤ μ.expectation (fun _ => L ^ 2) :=
      μ.expectation_mono (fun ω => pow_le_pow_left₀ (hf0 ω) (hfL ω) 2)
    _ = L ^ 2 := μ.expectation_const (L ^ 2)

theorem chebyshev (μ : FiniteLaw Ω) (f : Ω → ℝ) {t : ℝ} (ht : 0 < t) :
    μ.prob (fun ω => t ≤ |f ω - μ.expectation f|) ≤ μ.variance f / t ^ 2 := by
  calc
    μ.prob (fun ω => t ≤ |f ω - μ.expectation f|) ≤
        μ.prob (fun ω => t ^ 2 ≤ (f ω - μ.expectation f) ^ 2) := by
      apply μ.prob_mono
      intro ω hω
      simpa only [sq_abs] using pow_le_pow_left₀ ht.le hω 2
    _ ≤ μ.variance f / t ^ 2 :=
      μ.prob_ge_le_expectation_div
        (fun ω => (f ω - μ.expectation f) ^ 2)
        (fun ω => sq_nonneg (f ω - μ.expectation f)) (pow_pos ht 2)

theorem prob_gt_mean_bound_add_le (μ : FiniteLaw Ω) (f : Ω → ℝ)
    (m t : ℝ) (hm : μ.expectation f ≤ m) (ht : 0 < t) :
    μ.prob (fun ω => m + t < f ω) ≤ μ.variance f / t ^ 2 := by
  calc
    μ.prob (fun ω => m + t < f ω) ≤
        μ.prob (fun ω => t ≤ |f ω - μ.expectation f|) := by
      apply μ.prob_mono
      intro ω hω
      calc
        t ≤ f ω - μ.expectation f := by linarith
        _ ≤ |f ω - μ.expectation f| := le_abs_self _
    _ ≤ μ.variance f / t ^ 2 := μ.chebyshev f ht

end FiniteLaw
end RyserCoveringCounterexample

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Geometry_ProjectionMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section

namespace RyserCoveringCounterexample

variable {F : Type*} [Field F] [Fintype F]

theorem expectation_uniform_projection_pair (d e : Direction F) (hne : d ≠ e)
    (f g : F → ℝ) :
    (FiniteLaw.uniform (Point F)).expectation
        (fun p => f (projection d p) * g (projection e p)) =
      (FiniteLaw.uniform F).expectation f * (FiniteLaw.uniform F).expectation g := by
  calc
    _ = ((FiniteLaw.uniform (Point F)).map (projectionPairEquiv d e hne)).expectation
        (fun z : F × F => f z.1 * g z.2) := by
      rw [FiniteLaw.expectation_map]; rfl
    _ = ((FiniteLaw.uniform F).prod (FiniteLaw.uniform F)).expectation
        (fun z : F × F => f z.1 * g z.2) := by
      rw [FiniteLaw.map_uniform_equiv, FiniteLaw.uniform_prod]
    _ = (FiniteLaw.uniform F).expectation
        (fun t => f t * (FiniteLaw.uniform F).expectation g) := by
      rw [FiniteLaw.expectation_prod]
      simp only [FiniteLaw.expectation_smul]
    _ = _ := by
      simp only [FiniteLaw.expectation, ← mul_assoc, Finset.sum_mul]

theorem expectation_uniform_projection (d : Direction F) (f : F → ℝ) :
    (FiniteLaw.uniform (Point F)).expectation (fun p => f (projection d p)) =
      (FiniteLaw.uniform F).expectation f := by
  cases d with
  | none =>
      simpa only [FiniteLaw.expectation_const, mul_one] using
        expectation_uniform_projection_pair (F := F) none (some 0) (by simp)
          f (fun _ => 1)
  | some a =>
      simpa only [FiniteLaw.expectation_const, mul_one] using
        expectation_uniform_projection_pair (F := F) (some a) none (by simp)
          f (fun _ => 1)

theorem covariance_uniform_projection (d e : Direction F) (hne : d ≠ e)
    (f g : F → ℝ) :
    (FiniteLaw.uniform (Point F)).covariance
        (fun p => f (projection d p)) (fun p => g (projection e p)) = 0 := by
  rw [FiniteLaw.covariance_eq_expectation_mul_sub_mul,
    expectation_uniform_projection_pair d e hne f g,
    expectation_uniform_projection d f, expectation_uniform_projection e g,
    sub_self]

theorem expectation_uniform_projection_add (d : Direction F) (c : F) (f : F → ℝ) :
    (FiniteLaw.uniform (Point F)).expectation (fun p => f (projection d p + c)) =
      (FiniteLaw.uniform F).expectation f := by
  rw [expectation_uniform_projection d (fun t => f (t + c)),
    FiniteLaw.uniform_expectation, FiniteLaw.uniform_expectation]
  apply congrArg (fun s : ℝ => s / (Fintype.card F : ℝ))
  simpa only [Equiv.coe_addRight] using Equiv.sum_comp (Equiv.addRight c) f

variable [DecidableEq F]

theorem expectation_uniform_shifted_slice (U : Finset (Point F))
    (d : Direction F) (c : F) :
    (FiniteLaw.uniform (Point F)).expectation
        (fun p => (sliceCount U d (projection d p + c) : ℝ)) =
      (U.card : ℝ) / (Fintype.card F : ℝ) := by
  calc
    _ = (FiniteLaw.uniform F).expectation (fun t => (sliceCount U d t : ℝ)) :=
      expectation_uniform_projection_add d c _
    _ = _ := by rw [FiniteLaw.uniform_expectation, sum_sliceCount]

theorem variance_uniform_shifted_slice (U : Finset (Point F))
    (d : Direction F) (c : F) :
    (FiniteLaw.uniform (Point F)).variance
        (fun p => (sliceCount U d (projection d p + c) : ℝ)) =
      sliceEnergy U d := by
  unfold FiniteLaw.variance
  rw [expectation_uniform_shifted_slice]
  calc
    _ = (FiniteLaw.uniform F).expectation
        (fun t => ((sliceCount U d t : ℝ) -
          (U.card : ℝ) / (Fintype.card F : ℝ)) ^ 2) :=
      expectation_uniform_projection_add d c _
    _ = sliceEnergy U d := by
      rw [FiniteLaw.uniform_expectation]; rfl

end RyserCoveringCounterexample

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_AnalyticalLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace RyserCoveringCounterexample.Selection

theorem tendsto_nat_pow_mul_exp_neg_mul (m : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun K : ℕ => (K : ℝ) ^ m * Real.exp (-δ * (K : ℝ)))
      atTop (𝓝 0) := by
  simpa only [Function.comp_def, Real.rpow_natCast] using
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (m : ℝ) δ hδ).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))

theorem tendsto_nat_mul_exp_linear_sub_mul_log {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Tendsto
      (fun q : ℕ => (q : ℝ) *
        Real.exp (b * (q : ℝ) - a * (q : ℝ) * Real.log (q : ℝ)))
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun q : ℕ => a * Real.log (q : ℝ)) atTop atTop := by
    simpa only [Function.comp_def] using
      (Real.tendsto_log_atTop.comp
        (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul_atTop ha
  have hdom : Tendsto (fun q : ℕ => (q : ℝ) * Real.exp (-(q : ℝ)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, pow_one] using
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  refine squeeze_zero' ?_ ?_ hdom
  · exact Filter.Eventually.of_forall fun q : ℕ =>
      mul_nonneg (Nat.cast_nonneg q) (Real.exp_pos _).le
  · filter_upwards [hlog.eventually_ge_atTop (b + 1)] with q hq
    have hexp : b * (q : ℝ) - a * (q : ℝ) * Real.log (q : ℝ) ≤ -(q : ℝ) := by
      calc
        b * (q : ℝ) - a * (q : ℝ) * Real.log (q : ℝ)
            = (b - a * Real.log (q : ℝ)) * (q : ℝ) := by ring
        _ ≤ (-1) * (q : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg q)
        _ = -(q : ℝ) := by ring
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (Nat.cast_nonneg q)

end RyserCoveringCounterexample.Selection

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_Definitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace RyserCoveringCounterexample.Selection

variable {F : Type*} [Field F] [instDecidableEqF : DecidableEq F] {n K : ℕ}

theorem projection_add_eq (d : Direction F) (p q : Point F) :
    projection d (p + q) = projection d p + projection d q := let _ := instDecidableEqF; by
  exact RyserCoveringCounterexample.projection_add d p q

theorem conflict_iff_forbidden (data : Data F n) (i j : Fin n) (b b' : Point F) :
    Conflict data i j b b' ↔
      ∃ u ∈ data.W i, ∃ v ∈ data.W j, ∃ d ∈ data.dirs i ∪ data.dirs j,
        projection d b = projection d b' + projection d (v - u) := by
  unfold Conflict
  constructor
  · rintro ⟨u, hu, v, hv, d, hd, h⟩
    refine ⟨u, hu, v, hv, d, hd, ?_⟩
    rw [projection_sub_eq, projection_add_eq, projection_add_eq] at h
    rw [projection_sub_eq, ← add_sub_assoc]
    exact eq_sub_iff_add_eq.mpr (sub_eq_zero.mp h)
  · rintro ⟨u, hu, v, hv, d, hd, h⟩
    refine ⟨u, hu, v, hv, d, hd, ?_⟩
    rw [projection_sub_eq, ← add_sub_assoc] at h
    rw [projection_sub_eq, projection_add_eq, projection_add_eq]
    exact sub_eq_zero.mpr (eq_sub_iff_add_eq.mp h)

theorem feasible_congr (data : Data F n) (T : Finset (Position n K))
    (pool pool' : Pool F n K) (h : ∀ e ∈ T, pool e = pool' e)
    (i : Fin n) (b : Point F) :
    Feasible data T pool i b ↔ Feasible data T pool' i b := by
  unfold Feasible
  constructor <;> intro hb e he
  · simpa only [h e he] using hb e he
  · simpa only [h e he] using hb e he

end RyserCoveringCounterexample.Selection

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_PoolLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Selection

variable (F : Type*) [instFieldF : Field F] [instFintypeF : Fintype F] [instDecidableEqF : DecidableEq F] (n K : ℕ)

theorem poolLaw_eq_uniform : poolLaw F n K = FiniteLaw.uniform (Pool F n K) := let _ := instDecidableEqF;
  FiniteLaw.pi_uniform

variable {F n K}

theorem feasible_join_iff (data : Data F n) (T : Finset (Position n K))
    (x : ExposedAssignment (F := F) T) (y : FreshAssignment (F := F) T)
    (i : Fin n) (b : Point F) :
    Feasible data T (joinAssignments T x y) i b ↔
      Feasible data T (frozenPool T x) i b := by
  apply feasible_congr
  intro e he
  change joinAssignments T x y (⟨e, he⟩ : {e // e ∈ T}).val =
    joinAssignments T x (fun _ => 0) (⟨e, he⟩ : {e // e ∈ T}).val
  rw [joinAssignments_exposed, joinAssignments_exposed]

theorem poolLaw_prob_split (T : Finset (Position n K)) (P : Pool F n K → Prop) :
    (poolLaw F n K).prob P =
      (FiniteLaw.uniform (ExposedAssignment (F := F) T)).expectation (fun x =>
        (FiniteLaw.uniform (FreshAssignment (F := F) T)).prob
          (fun y => P (joinAssignments T x y))) :=
  by
    rw [poolLaw_eq_uniform]
    exact FiniteLaw.prob_uniform_prod_equiv
      (X := Pool F n K) (Y := ExposedAssignment (F := F) T)
      (Z := FreshAssignment (F := F) T)
      (Equiv.piEquivPiSubtypeProd (fun e : Position n K => e ∈ T)
        (fun _ => Point F)) P

theorem poolLaw_prob_split_le (T : Finset (Position n K))
    (P : Pool F n K → Prop) (b : ℝ)
    (h : ∀ x : ExposedAssignment (F := let _ := instDecidableEqF; F) T,
      (FiniteLaw.uniform (FreshAssignment (F := F) T)).prob
        (fun y => P (joinAssignments T x y)) ≤ b) :
    (poolLaw F n K).prob P ≤ b :=
  FiniteLaw.prob_pi_uniform_split_le (fun e : Position n K => e ∈ T) P b h

theorem poolLaw_prob_split_le_bad (T : Finset (Position n K))
    (P : Pool F n K → Prop) (Bad : ExposedAssignment (F := F) T → Prop)
    (b : ℝ) (hb : 0 ≤ b)
    (h : ∀ x : ExposedAssignment (F := F) T, ¬Bad x →
      (FiniteLaw.uniform (FreshAssignment (F := F) T)).prob
        (fun y => P (joinAssignments T x y)) ≤ b) :
    (poolLaw F n K).prob P ≤
      (FiniteLaw.uniform (ExposedAssignment (F := F) T)).prob Bad + b :=
  by
    rw [poolLaw_prob_split T P]
    simpa only [FiniteLaw.prob_prod_average] using
      FiniteLaw.prob_prod_le_bad_add
        (FiniteLaw.uniform (ExposedAssignment (F := F) T))
        (FiniteLaw.uniform (FreshAssignment (F := F) T))
        (fun z => P (joinAssignments T z.1 z.2)) Bad b hb h

end RyserCoveringCounterexample.Selection

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_FeasibleDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
namespace RyserCoveringCounterexample.Selection

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n K : ℕ}

theorem feasibleDensity_le_one (data : Data F n) (T : Finset (Position n K))
    (pool : Pool F n K) (i : Fin n) : feasibleDensity data T pool i ≤ 1 :=
  (FiniteLaw.uniform (Point F)).prob_le_one _

theorem feasibleDensity_eq_card (data : Data F n) (T : Finset (Position n K))
    (pool : Pool F n K) (i : Fin n) :
    feasibleDensity data T pool i =
      ((feasibleSet data T pool i).card : ℝ) / (Fintype.card F : ℝ) ^ 2 := by
  classical
  rw [feasibleDensity, FiniteLaw.uniform_prob, card_point, Nat.cast_pow]
  rfl

theorem sum_feasibleDensity (data : Data F n) (I : Finset (Fin n))
    (T : Finset (Position n K)) (pool : Pool F n K) :
    (∑ i ∈ I, feasibleDensity data T pool i) =
      (feasibleMass data I T pool : ℝ) / (Fintype.card F : ℝ) ^ 2 := by
  classical
  simp only [feasibleDensity_eq_card, feasibleMass, Nat.cast_sum,
    div_eq_mul_inv, Finset.sum_mul]

theorem feasibleSet_join_eq (data : Data F n) (T : Finset (Position n K))
    (x : ExposedAssignment (F := F) T) (y : FreshAssignment (F := F) T)
    (i : Fin n) :
    feasibleSet data T (joinAssignments T x y) i =
      feasibleSet data T (frozenPool T x) i := by
  ext b
  simp only [mem_feasibleSet, feasible_join_iff]

theorem feasibleMass_join_eq (data : Data F n) (I : Finset (Fin n))
    (T : Finset (Position n K)) (x : ExposedAssignment (F := F) T)
    (y : FreshAssignment (F := F) T) :
    feasibleMass data I T (joinAssignments T x y) =
      feasibleMass data I T (frozenPool T x) := by
  simp only [feasibleMass, feasibleSet_join_eq]

theorem prob_feasibleMass_lt_eq_exposed (data : Data F n) (I : Finset (Fin n))
    (T : Finset (Position n K)) (a : ℝ) :
    (poolLaw F n K).prob (fun pool => (feasibleMass data I T pool : ℝ) < a) =
      (FiniteLaw.uniform (ExposedAssignment (F := F) T)).prob
        (fun x => (feasibleMass data I T (frozenPool T x) : ℝ) < a) := by
  classical
  rw [poolLaw_prob_split T]
  simp only [feasibleMass_join_eq]
  have hc (x : ExposedAssignment (F := F) T) :
      (FiniteLaw.uniform (FreshAssignment (F := F) T)).prob
          (fun _ => (feasibleMass data I T (frozenPool T x) : ℝ) < a) =
        if (feasibleMass data I T (frozenPool T x) : ℝ) < a then 1 else 0 := by
    split_ifs with hx <;> simp [hx]
  simp_rw [hc]
  exact ((FiniteLaw.uniform (ExposedAssignment (F := F) T)).prob_eq_expectation _).symm

end RyserCoveringCounterexample.Selection

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_Forbidden
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
namespace RyserCoveringCounterexample.Selection

variable {F : Type*} [Field F] [instFintypeF : Fintype F] [DecidableEq F] {n K : ℕ}

theorem conflict_iff_equation (data : Data F n) (i j : Fin n) (b b' : Point F) :
    Conflict data i j b b' ↔ ∃ e : EquationIndex data i j, equationEvent data i j b' e b := let _ := instFintypeF; by
  rw [conflict_iff_forbidden]
  constructor
  · rintro ⟨u, hu, v, hv, d, hd, h⟩
    exact ⟨(⟨u, hu⟩, ⟨v, hv⟩, ⟨d, hd⟩), h⟩
  · rintro ⟨⟨u, v, d⟩, h⟩
    exact ⟨u.val, u.property, v.val, v.property, d.val, d.property, h⟩

theorem card_equationIndex_le {D : ℕ} (data : Data F n) (hdata : Bounded D data)
    (i j : Fin n) : Fintype.card (EquationIndex data i j) ≤ 2 * D ^ 3 := by
  have hdirs : (data.dirs i ∪ data.dirs j).card ≤ D + D :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add (hdata.2.2.1 i) (hdata.2.2.1 j))
  calc
    Fintype.card (EquationIndex data i j) =
        (data.W i).card * ((data.W j).card * (data.dirs i ∪ data.dirs j).card) := by
      simp only [EquationIndex, Fintype.card_prod, Fintype.card_coe]
    _ ≤ D * (D * (D + D)) :=
      Nat.mul_le_mul (hdata.2.1 i) (Nat.mul_le_mul (hdata.2.1 j) hdirs)
    _ = 2 * D ^ 3 := by ring

theorem prob_conflict_le {D : ℕ} (data : Data F n) (hdata : Bounded D data)
    (i j : Fin n) (b' : Point F) :
    (FiniteLaw.uniform (Point F)).prob (fun b => Conflict data i j b b') ≤
      (2 * (D : ℝ) ^ 3) / (Fintype.card F : ℝ) := by
  classical
  have hP : (fun b => Conflict data i j b b') =
      (fun b => ∃ e : EquationIndex data i j, equationEvent data i j b' e b) := by
    funext b
    exact propext (conflict_iff_equation data i j b b')
  rw [hP]
  calc
    _ ≤ ∑ e : EquationIndex data i j,
        (FiniteLaw.uniform (Point F)).prob (equationEvent data i j b' e) :=
      FiniteLaw.prob_exists_le _ _
    _ = (Fintype.card (EquationIndex data i j) : ℝ) / (Fintype.card F : ℝ) := by
      calc
        _ = ∑ _e : EquationIndex data i j, 1 / (Fintype.card F : ℝ) := by
          apply Finset.sum_congr rfl
          intro e _
          exact uniform_prob_projection e.2.2.val
            (projection e.2.2.val b' + projection e.2.2.val (e.2.1.val - e.1.val))
        _ = _ := by simp [div_eq_mul_inv]
    _ ≤ (2 * (D : ℝ) ^ 3) / (Fintype.card F : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast card_equationIndex_le data hdata i j

theorem prob_not_feasible_le {D : ℕ} (data : Data F n) (hdata : Bounded D data)
    (T : Finset (Position n K)) (pool : Pool F n K) (i : Fin n) :
    (FiniteLaw.uniform (Point F)).prob (fun b => ¬Feasible data T pool i b) ≤
      (T.card : ℝ) * ((2 * (D : ℝ) ^ 3) / (Fintype.card F : ℝ)) := by
  classical
  have hP : (fun b => ¬Feasible data T pool i b) =
      (fun b => ∃ e : ↥T, Conflict data i e.val.1 b (pool e.val)) := by
    funext b
    simp [Feasible]
  rw [hP]
  calc
    _ ≤ ∑ e : ↥T, (FiniteLaw.uniform (Point F)).prob
        (fun b => Conflict data i e.val.1 b (pool e.val)) :=
      FiniteLaw.prob_exists_le _ _
    _ ≤ ∑ _e : ↥T, ((2 * (D : ℝ) ^ 3) / (Fintype.card F : ℝ)) :=
      Finset.sum_le_sum (fun e _ => prob_conflict_le data hdata i e.val.1 (pool e.val))
    _ = _ := by simp

end RyserCoveringCounterexample.Selection

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_IndependentTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.Selection

variable {Ω A : Type*} [Fintype Ω]

theorem prob_exists_mem_le (mu : FiniteLaw Ω) (S : Finset A)
    (P : A → Ω → Prop) :
    mu.prob (fun x => ∃ a ∈ S, P a x) ≤ ∑ a ∈ S, mu.prob (P a) := by
  classical
  calc
    _ ≤ mu.expectation (fun x => ∑ a ∈ S, if P a x then (1 : ℝ) else 0) := by
      apply mu.prob_le_expectation
      · intro x
        exact Finset.sum_nonneg (fun a _ => by by_cases h : P a x <;> simp [h])
      · rintro x ⟨a, ha, hax⟩
        calc
          1 = (if P a x then (1 : ℝ) else 0) := by rw [ite_eq_left hax]
          _ ≤ ∑ b ∈ S, if P b x then (1 : ℝ) else 0 :=
            Finset.single_le_sum (f := fun b => if P b x then (1 : ℝ) else 0) (fun b _ => by by_cases h : P b x <;> simp [h]) ha
    _ = ∑ a ∈ S, mu.prob (P a) := by
      rw [FiniteLaw.expectation_finset_sum]
      simp_rw [← FiniteLaw.prob_eq_expectation]

variable {E : Type*} [Fintype E] [DecidableEq E]
  {X : E → Type*} [∀ e, Fintype (X e)]

theorem prob_pi_forall_mem (mu : ∀ e, FiniteLaw (X e))
    (S : Finset E) (P : ∀ e, X e → Prop) :
    (FiniteLaw.pi mu).prob (fun x => ∀ e ∈ S, P e (x e)) =
      ∏ e ∈ S, (mu e).prob (P e) := by
  classical
  rw [FiniteLaw.prob_pi mu (fun e x => e ∈ S → P e x)]
  have hterm (e : E) : (mu e).prob (fun x => e ∈ S → P e x) =
      if e ∈ S then (mu e).prob (P e) else 1 := by
    by_cases he : e ∈ S <;> simp [he]
  simp_rw [hterm]
  rw [← Finset.prod_filter]
  simp

theorem prob_many_coordinate_events_le (mu : ∀ e, FiniteLaw (X e))
    (S : Finset E) (P : ∀ e, X e → Prop) (r : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hP : ∀ e ∈ S, (mu e).prob (P e) ≤ p) :
    (FiniteLaw.pi mu).prob (fun x => r ≤ (S.filter (fun e => P e (x e))).card) ≤
      (2 : ℝ) ^ S.card * p ^ r := by
  classical
  have hsubset (x : ∀ e, X e)
      (hx : r ≤ (S.filter (fun e => P e (x e))).card) :
      ∃ T ∈ S.powersetCard r, ∀ e ∈ T, P e (x e) := by
    obtain ⟨T, hT, hcard⟩ := Finset.exists_subset_card_eq hx
    refine ⟨T, Finset.mem_powersetCard.mpr ⟨?_, hcard⟩, ?_⟩
    · exact fun e he => (Finset.mem_filter.mp (hT he)).1
    · exact fun e he => (Finset.mem_filter.mp (hT he)).2
  have hproduct (T : Finset E) (hT : T ∈ S.powersetCard r) :
      (FiniteLaw.pi mu).prob (fun x => ∀ e ∈ T, P e (x e)) ≤ p ^ r := by
    rcases Finset.mem_powersetCard.mp hT with ⟨hTS, hcard⟩
    rw [prob_pi_forall_mem]
    calc
      (∏ e ∈ T, (mu e).prob (P e)) ≤ ∏ _e ∈ T, p := by
        apply Finset.prod_le_prod
        · exact fun e _ => (mu e).prob_nonneg (P e)
        · exact fun e he => hP e (hTS he)
      _ = p ^ r := by simp [hcard]
  have hcount : (S.powersetCard r).card ≤ 2 ^ S.card := by
    rw [← Finset.card_powerset]
    apply Finset.card_le_card
    intro T hT
    exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hT).1
  calc
    _ ≤ (FiniteLaw.pi mu).prob
        (fun x => ∃ T ∈ S.powersetCard r, ∀ e ∈ T, P e (x e)) :=
      (FiniteLaw.pi mu).prob_mono hsubset
    _ ≤ ∑ T ∈ S.powersetCard r,
        (FiniteLaw.pi mu).prob (fun x => ∀ e ∈ T, P e (x e)) :=
      prob_exists_mem_le _ _ _
    _ ≤ ∑ _T ∈ S.powersetCard r, p ^ r := Finset.sum_le_sum hproduct
    _ = ((S.powersetCard r).card : ℝ) * p ^ r := by simp
    _ ≤ (2 : ℝ) ^ S.card * p ^ r :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) (pow_nonneg hp _)

end RyserCoveringCounterexample.Selection

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_SmallCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
namespace RyserCoveringCounterexample.Selection

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n K : ℕ}

theorem noFeasibleOutside_join_iff (data : Data F n) (I : Finset (Fin n))
    (T : Finset (Position n K)) (x : ExposedAssignment (F := F) T)
    (y : FreshAssignment (F := F) T) :
    NoFeasibleOutside data I T (joinAssignments T x y) ↔
      ∀ e ∈ freshTargets I T, ¬Feasible data T (frozenPool T x) e.val.1 (y e) := by
  constructor
  · intro h e he
    have hi := (Finset.mem_filter.mp he).2
    have hh := h e.val hi e.property
    simpa only [joinAssignments_fresh, feasible_join_iff] using hh
  · intro h e hi he
    have hmem : (⟨e, he⟩ : {e : Position n K // e ∉ T}) ∈ freshTargets I T := by
      simp only [freshTargets, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hi
    have hh := h ⟨e, he⟩ hmem
    have hj : joinAssignments T x y e = y ⟨e, he⟩ :=
      joinAssignments_fresh T x y ⟨e, he⟩
    rw [hj, feasible_join_iff]
    exact hh

theorem prob_noFeasibleOutside_le {D : ℕ} (data : Data F n) (hdata : Bounded D data)
    (I : Finset (Fin n)) (T : Finset (Position n K)) :
    (poolLaw F n K).prob (NoFeasibleOutside data I T) ≤
      ((T.card : ℝ) * ((2 * (D : ℝ) ^ 3) / (Fintype.card F : ℝ))) ^
        (freshTargets I T).card := by
  classical
  refine poolLaw_prob_split_le T (NoFeasibleOutside data I T)
    (((T.card : ℝ) * ((2 * (D : ℝ) ^ 3) / (Fintype.card F : ℝ))) ^
      (freshTargets I T).card) ?_
  intro x
  have hP :
      (fun y : FreshAssignment (F := F) T =>
        NoFeasibleOutside data I T (joinAssignments T x y)) =
      (fun y => ∀ e ∈ freshTargets I T,
        ¬Feasible data T (frozenPool T x) e.val.1 (y e)) := by
    funext y
    exact propext (noFeasibleOutside_join_iff data I T x y)
  rw [hP]
  calc
    _ = (FiniteLaw.pi (fun _ : {e : Position n K // e ∉ T} =>
        FiniteLaw.uniform (Point F))).prob
        (fun y => ∀ e ∈ freshTargets I T,
          ¬Feasible data T (frozenPool T x) e.val.1 (y e)) := by
      rw [FiniteLaw.pi_uniform]
    _ = ∏ e ∈ freshTargets I T, (FiniteLaw.uniform (Point F)).prob
        (fun b => ¬Feasible data T (frozenPool T x) e.val.1 b) :=
      prob_pi_forall_mem
        (fun _ : {e : Position n K // e ∉ T} => FiniteLaw.uniform (Point F))
        (freshTargets I T) (fun e b => ¬Feasible data T (frozenPool T x) e.val.1 b)
    _ ≤ ∏ _e ∈ freshTargets I T,
        ((T.card : ℝ) * ((2 * (D : ℝ) ^ 3) / (Fintype.card F : ℝ))) := by
      apply Finset.prod_le_prod
      · exact fun e _ => (FiniteLaw.uniform (Point F)).prob_nonneg _
      · exact fun e _ => prob_not_feasible_le data hdata T (frozenPool T x) e.val.1
    _ = _ := by simp

end RyserCoveringCounterexample.Selection

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_PoolCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
namespace RyserCoveringCounterexample.Selection

variable {n K : ℕ}

theorem image_freshTargets_val (I : Finset (Fin n)) (T : Finset (Position n K)) :
    (freshTargets I T).image (fun e => e.val) = targetPositions I K \ T := by
  ext e
  constructor
  · intro he
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_sdiff.mpr
      ⟨mem_targetPositions.mpr (Finset.mem_filter.mp hz).2, z.property⟩
  · intro he
    obtain ⟨hi, hn⟩ := Finset.mem_sdiff.mp he
    refine Finset.mem_image.mpr ⟨⟨e, hn⟩, ?_, rfl⟩
    simp only [freshTargets, Finset.mem_filter, Finset.mem_univ, true_and]
    exact mem_targetPositions.mp hi

theorem card_freshTargets_eq_sdiff (I : Finset (Fin n)) (T : Finset (Position n K)) :
    (freshTargets I T).card = (targetPositions I K \ T).card := by
  calc
    (freshTargets I T).card = ((freshTargets I T).image (fun e => e.val)).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ = (targetPositions I K \ T).card := congrArg Finset.card (image_freshTargets_val I T)

theorem card_freshTargets {I : Finset (Fin n)} {T : Finset (Position n K)}
    (hT : T ⊆ targetPositions I K) :
    (freshTargets I T).card = I.card * K - T.card := by
  rw [card_freshTargets_eq_sdiff, Finset.card_sdiff_of_subset hT, card_targetPositions]

theorem freshTargets_card_lower {I : Finset (Fin n)} {T : Finset (Position n K)}
    (hT : T ⊆ targetPositions I K) (hcard : T.card ≤ 2 * I.card) :
    (K - 2) * I.card ≤ (freshTargets I T).card := by
  rw [card_freshTargets hT, Nat.sub_mul, Nat.mul_comm K I.card]
  exact Nat.sub_le_sub_left hcard (I.card * K)

theorem sum_exposedCount {I : Finset (Fin n)} {T : Finset (Position n K)}
    (hT : T ⊆ targetPositions I K) :
    (∑ i ∈ I, exposedCount T i) = T.card := by
  have hmap : (T : Set (Position n K)).MapsTo Prod.fst I := by
    intro e he
    exact mem_targetPositions.mp (hT he)
  simpa only [exposedCount] using (Finset.card_eq_sum_card_fiberwise hmap).symm

theorem targetPositions_eq_filter (I : Finset (Fin n)) (K : ℕ) :
    targetPositions I K = Finset.univ.filter (fun e : Position n K => e.1 ∈ I) := by
  ext e
  simp only [mem_targetPositions, Finset.mem_filter, Finset.mem_univ, true_and]

theorem exposedCount_le (T : Finset (Position n K)) (i : Fin n) :
    exposedCount T i ≤ K := by
  classical
  unfold exposedCount
  calc
    (T.filter (fun e => e.1 = i)).card ≤
        (Finset.univ : Finset (Fin K)).card := by
      refine Finset.card_le_card_of_injOn
        (fun e : Position n K => e.2) ?_ ?_
      · intro e _
        exact Finset.mem_univ _
      · intro e he f hf hef
        exact Prod.ext
          ((Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm)
          hef
    _ = K := by simp

theorem card_freshTargets_fiber (I : Finset (Fin n))
    (T : Finset (Position n K)) (i : Fin n) (hi : i ∈ I) :
    ((freshTargets I T).filter (fun e => e.val.1 = i)).card =
      K - exposedCount T i := by
  classical
  let used : Finset (Fin K) := Finset.univ.filter (fun j => (i, j) ∈ T)
  let unused : Finset (Fin K) := Finset.univ.filter (fun j => (i, j) ∉ T)
  have hused : exposedCount T i = used.card := by
    unfold exposedCount
    refine Finset.card_bij (fun (e : Position n K) _ => e.2) ?_ ?_ ?_
    · intro e he
      have hepair : e = (i, e.2) :=
        Prod.ext (Finset.mem_filter.mp he).2 rfl
      have hmem : (i, e.2) ∈ T := by
        rw [← hepair]
        exact (Finset.mem_filter.mp he).1
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩
    · intro e he f hf hef
      exact Prod.ext
        ((Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm)
        hef
    · intro j hj
      refine ⟨(i, j), ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).2, rfl⟩
  have hfresh :
      ((freshTargets I T).filter (fun e => e.val.1 = i)).card = unused.card := by
    refine Finset.card_bij
      (fun (e : {e : Position n K // e ∉ T}) _ => e.val.2) ?_ ?_ ?_
    · intro e he
      have hepair : e.val = (i, e.val.2) :=
        Prod.ext (Finset.mem_filter.mp he).2 rfl
      have hnot : (i, e.val.2) ∉ T := by
        rw [← hepair]
        exact e.property
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnot⟩
    · intro e he f hf hef
      apply Subtype.ext
      exact Prod.ext
        ((Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm)
        hef
    · intro j hj
      have hjT : (i, j) ∉ T := (Finset.mem_filter.mp hj).2
      refine ⟨⟨(i, j), hjT⟩, ?_, rfl⟩
      refine Finset.mem_filter.mpr ⟨?_, rfl⟩
      simpa only [freshTargets, Finset.mem_filter, Finset.mem_univ, true_and] using hi
  have hsplit : used.card + unused.card = K := by
    simpa only [used, unused, Finset.card_univ, Fintype.card_fin] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin K)))
        (fun j : Fin K => (i, j) ∈ T))
  rw [hfresh, hused]
  exact Nat.eq_sub_of_add_eq' hsplit

theorem sum_freshTargets (I : Finset (Fin n))
    (T : Finset (Position n K)) (f : Fin n → ℝ) :
    (∑ e ∈ freshTargets I T, f e.val.1) =
      ∑ i ∈ I, ((K - exposedCount T i : ℕ) : ℝ) * f i := by
  classical
  have hmaps : ∀ e ∈ freshTargets I T, e.val.1 ∈ I := by
    intro e he
    exact (Finset.mem_filter.mp he).2
  calc
    (∑ e ∈ freshTargets I T, f e.val.1) =
        ∑ i ∈ I, ∑ e ∈ (freshTargets I T).filter (fun e => e.val.1 = i), f i :=
      (Finset.sum_fiberwise_of_maps_to'
        (s := freshTargets I T) (t := I)
        (g := fun e : {e : Position n K // e ∉ T} => e.val.1) hmaps f).symm
    _ = ∑ i ∈ I, ((K - exposedCount T i : ℕ) : ℝ) * f i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_const, nsmul_eq_mul, card_freshTargets_fiber I T i hi]

end RyserCoveringCounterexample.Selection

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_Estimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace RyserCoveringCounterexample.Selection

theorem sum_le_card_mul_add_bad_card_mul {ι : Type*} (T : Finset ι)
    (bad : ι → Prop) [DecidablePred bad] (z : ι → ℝ) (threshold cap : ℝ)
    (hthreshold : 0 ≤ threshold)
    (hregular : ∀ e ∈ T, ¬bad e → z e ≤ threshold)
    (hexception : ∀ e ∈ T, bad e → z e ≤ cap) :
    (∑ e ∈ T, z e) ≤ (T.card : ℝ) * threshold + ((T.filter bad).card : ℝ) * cap := by
  calc
    (∑ e ∈ T, z e) ≤ ∑ e ∈ T, (threshold + if bad e then cap else 0) := by
      apply Finset.sum_le_sum
      intro e he
      by_cases hb : bad e
      · simp only [ite_eq_left hb]
        linarith [hexception e he hb]
      · simpa only [ite_eq_right hb, add_zero] using hregular e he hb
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]

theorem mass_after_chunk_ge {ι : Type*} (T : Finset ι)
    (bad : ι → Prop) [DecidablePred bad] (z : ι → ℝ)
    (M M' m q C α γ : ℝ)
    (hM : 0 ≤ M) (hm : 0 ≤ m) (hq : 0 < q) (hC : 0 ≤ C) (hγ : 0 ≤ γ)
    (hhalf : C * α = 1 / 2)
    (hsize : (T.card : ℝ) ≤ α * q)
    (hbad : ((T.filter bad).card : ℝ) ≤ 2 * γ * q)
    (hregular : ∀ e ∈ T, ¬bad e → z e ≤ C * M / q + γ * m * q)
    (hexception : ∀ e ∈ T, bad e → z e ≤ C * m * q)
    (hloss : M - (∑ e ∈ T, z e) ≤ M') :
    M / 2 - (α + 2 * C) * γ * (m * q ^ 2) ≤ M' := by
  have hthreshold : 0 ≤ C * M / q + γ * m * q :=
    add_nonneg (div_nonneg (mul_nonneg hC hM) hq.le)
      (mul_nonneg (mul_nonneg hγ hm) hq.le)
  have hcap : 0 ≤ C * m * q := mul_nonneg (mul_nonneg hC hm) hq.le
  have hsum := sum_le_card_mul_add_bad_card_mul T bad z
    (C * M / q + γ * m * q) (C * m * q) hthreshold hregular hexception
  have htotal : (∑ e ∈ T, z e) ≤
      (α * q) * (C * M / q + γ * m * q) + (2 * γ * q) * (C * m * q) :=
    hsum.trans (add_le_add (mul_le_mul_of_nonneg_right hsize hthreshold)
      (mul_le_mul_of_nonneg_right hbad hcap))
  have heq : (α * q) * (C * M / q + γ * m * q) +
      (2 * γ * q) * (C * m * q) =
      (C * α) * M + (α + 2 * C) * γ * (m * q ^ 2) := by
    field_simp [hq.ne']
    ring
  rw [heq, hhalf] at htotal
  linarith

theorem mass_ge_geometric_sub_error (mass : ℕ → ℝ) (scale err : ℝ) (J : ℕ)
    (hscale : 0 ≤ scale) (herr : 0 ≤ err) (hstart : scale ≤ mass 0)
    (hstep : ∀ j < J, mass j / 2 - err * scale ≤ mass (j + 1)) :
    scale * (1 / 2 : ℝ) ^ J - 2 * err * scale ≤ mass J := by
  have hall : ∀ j ≤ J, scale * (1 / 2 : ℝ) ^ j - 2 * err * scale ≤ mass j := by
    intro j
    induction j with
    | zero =>
        intro _
        simp only [pow_zero, mul_one]
        nlinarith [mul_nonneg herr hscale]
    | succ j ih =>
        intro hj
        have hprev := ih (Nat.le_trans (Nat.le_succ j) hj)
        have hnext := hstep j (Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hj)
        rw [pow_succ]
        nlinarith
  exact hall J le_rfl

theorem mass_after_chunks_ge_density (mass : ℕ → ℝ) (scale err : ℝ) (J J0 : ℕ)
    (hscale : 0 ≤ scale) (herr : 0 ≤ err) (hstart : scale ≤ mass 0)
    (hstep : ∀ j < J, mass j / 2 - err * scale ≤ mass (j + 1))
    (hJ : J ≤ J0) (hbudget : 2 * err ≤ (1 / 2 : ℝ) ^ (J0 + 1)) :
    (1 / 2 : ℝ) ^ (J0 + 1) * scale ≤ mass J := by
  have hbase := mass_ge_geometric_sub_error mass scale err J hscale herr hstart hstep
  have hpow : (1 / 2 : ℝ) ^ J0 ≤ (1 / 2 : ℝ) ^ J :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hJ
  have hpowmul := mul_le_mul_of_nonneg_left hpow hscale
  have hbudgetmul := mul_le_mul_of_nonneg_right hbudget hscale
  calc
    (1 / 2 : ℝ) ^ (J0 + 1) * scale =
        scale * (1 / 2 : ℝ) ^ J0 - (1 / 2 : ℝ) ^ (J0 + 1) * scale := by
      rw [pow_succ]
      ring
    _ ≤ scale * (1 / 2 : ℝ) ^ J0 - 2 * err * scale := by linarith
    _ ≤ scale * (1 / 2 : ℝ) ^ J - 2 * err * scale :=
      sub_le_sub_right hpowmul _
    _ ≤ mass J := hbase

theorem unused_weight_ge {ι : Type*} (I : Finset ι) (p : ι → ℝ)
    (t : ι → ℕ) (K : ℕ) (δ m : ℝ)
    (hp : ∀ i ∈ I, p i ≤ 1) (ht : ∀ i ∈ I, t i ≤ K)
    (hdensity : δ * m ≤ ∑ i ∈ I, p i)
    (hcount : (∑ i ∈ I, (t i : ℝ)) ≤ 2 * m) :
    ((K : ℝ) * δ - 2) * m ≤ ∑ i ∈ I, ((K - t i : ℕ) : ℝ) * p i := by
  have hexposed : (∑ i ∈ I, (t i : ℝ) * p i) ≤ ∑ i ∈ I, (t i : ℝ) := by
    apply Finset.sum_le_sum
    intro i hi
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hp i hi) (Nat.cast_nonneg (t i))
  have hdense := mul_le_mul_of_nonneg_left hdensity (Nat.cast_nonneg K : (0 : ℝ) ≤ K)
  have hidentity : (∑ i ∈ I, ((K - t i : ℕ) : ℝ) * p i) =
      (K : ℝ) * (∑ i ∈ I, p i) - ∑ i ∈ I, (t i : ℝ) * p i := by
    calc
      _ = ∑ i ∈ I, ((K : ℝ) * p i - (t i : ℝ) * p i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Nat.cast_sub (ht i hi), sub_mul]
      _ = _ := by rw [Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hidentity]
  nlinarith

theorem prod_one_sub_pow_le_exp_neg_sum {ι : Type*} (I : Finset ι)
    (p : ι → ℝ) (k : ι → ℕ) (hp : ∀ i ∈ I, p i ≤ 1) :
    (∏ i ∈ I, (1 - p i) ^ k i) ≤ Real.exp (-(∑ i ∈ I, (k i : ℝ) * p i)) := by
  calc
    (∏ i ∈ I, (1 - p i) ^ k i) ≤ ∏ i ∈ I, Real.exp (-p i) ^ k i := by
      apply Finset.prod_le_prod
      · intro i hi
        exact pow_nonneg (sub_nonneg.mpr (hp i hi)) _
      · intro i hi
        exact pow_le_pow_left₀ (sub_nonneg.mpr (hp i hi)) (Real.one_sub_le_exp_neg (p i)) _
    _ = ∏ i ∈ I, Real.exp (-((k i : ℝ) * p i)) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [← Real.exp_nat_mul, mul_neg]
    _ = Real.exp (∑ i ∈ I, -((k i : ℝ) * p i)) := (Real.exp_sum I _).symm
    _ = Real.exp (-(∑ i ∈ I, (k i : ℝ) * p i)) := by rw [Finset.sum_neg_distrib]

end RyserCoveringCounterexample.Selection

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_UnusedProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace RyserCoveringCounterexample.Selection

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n K : ℕ}

theorem prob_noFeasibleOutside_join_eq_prod (data : Data F n)
    (I : Finset (Fin n)) (T : Finset (Position n K))
    (x : ExposedAssignment (F := F) T) :
    (FiniteLaw.uniform (FreshAssignment (F := F) T)).prob
      (fun y => NoFeasibleOutside data I T (joinAssignments T x y)) =
      ∏ e ∈ freshTargets I T,
        (1 - (FiniteLaw.uniform (Point F)).prob
          (Feasible data T (frozenPool T x) e.val.1)) := by
  classical
  have hP :
      (fun y : FreshAssignment (F := F) T =>
        NoFeasibleOutside data I T (joinAssignments T x y)) =
      (fun y => ∀ e ∈ freshTargets I T,
        ¬Feasible data T (frozenPool T x) e.val.1 (y e)) := by
    funext y
    exact propext (noFeasibleOutside_join_iff data I T x y)
  rw [hP]
  calc
    _ = (FiniteLaw.pi (fun _ : {e : Position n K // e ∉ T} =>
        FiniteLaw.uniform (Point F))).prob
        (fun y => ∀ e ∈ freshTargets I T,
          ¬Feasible data T (frozenPool T x) e.val.1 (y e)) := by
      rw [FiniteLaw.pi_uniform]
    _ = ∏ e ∈ freshTargets I T, (FiniteLaw.uniform (Point F)).prob
        (fun b => ¬Feasible data T (frozenPool T x) e.val.1 b) :=
      prob_pi_forall_mem
        (fun _ : {e : Position n K // e ∉ T} => FiniteLaw.uniform (Point F))
        (freshTargets I T)
        (fun e b => ¬Feasible data T (frozenPool T x) e.val.1 b)
    _ = _ := by
      apply Finset.prod_congr rfl
      intro e he
      exact (FiniteLaw.uniform (Point F)).prob_compl
        (Feasible data T (frozenPool T x) e.val.1)

theorem prob_noFeasibleOutside_join_le_exp_neg_sum (data : Data F n)
    (I : Finset (Fin n)) (T : Finset (Position n K))
    (x : ExposedAssignment (F := F) T) :
    (FiniteLaw.uniform (FreshAssignment (F := F) T)).prob
      (fun y => NoFeasibleOutside data I T (joinAssignments T x y)) ≤
      Real.exp (-(∑ e ∈ freshTargets I T, (FiniteLaw.uniform (Point F)).prob
        (Feasible data T (frozenPool T x) e.val.1))) := by
  rw [prob_noFeasibleOutside_join_eq_prod]
  simpa only [pow_one, Nat.cast_one, one_mul] using
    prod_one_sub_pow_le_exp_neg_sum (freshTargets I T)
      (fun e => (FiniteLaw.uniform (Point F)).prob
        (Feasible data T (frozenPool T x) e.val.1))
      (fun _ => 1) (fun e _ => (FiniteLaw.uniform (Point F)).prob_le_one _)

end RyserCoveringCounterexample.Selection

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_LargeCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section

namespace RyserCoveringCounterexample.Selection

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n K : ℕ}

theorem sum_fresh_feasibleDensity_ge (data : Data F n) (I : Finset (Fin n))
    (T : Finset (Position n K)) (pool : Pool F n K) (δ : ℝ)
    (hT : T ⊆ targetPositions I K) (hcard : T.card ≤ 2 * I.card)
    (hdensity : δ * (I.card : ℝ) * (Fintype.card F : ℝ) ^ 2 ≤
      (feasibleMass data I T pool : ℝ)) :
    ((K : ℝ) * δ - 2) * I.card ≤
      ∑ e ∈ freshTargets I T, feasibleDensity data T pool e.val.1 := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hmass : δ * (I.card : ℝ) ≤ ∑ i ∈ I, feasibleDensity data T pool i := by
    rw [sum_feasibleDensity]
    exact (le_div_iff₀ (pow_pos hq 2)).mpr hdensity
  have hcount : (∑ i ∈ I, (exposedCount T i : ℝ)) ≤ 2 * (I.card : ℝ) := by
    have hnat : (∑ i ∈ I, exposedCount T i) ≤ 2 * I.card := by
      rw [sum_exposedCount hT]
      exact hcard
    exact_mod_cast hnat
  rw [sum_freshTargets]
  exact unused_weight_ge I (feasibleDensity data T pool) (exposedCount T) K δ I.card
    (fun i _ => feasibleDensity_le_one data T pool i)
    (fun i _ => exposedCount_le T i) hmass hcount

theorem prob_noFeasibleOutside_join_le_of_density (data : Data F n)
    (I : Finset (Fin n)) (T : Finset (Position n K))
    (x : ExposedAssignment (F := F) T) (δ : ℝ)
    (hT : T ⊆ targetPositions I K) (hcard : T.card ≤ 2 * I.card)
    (hdensity : δ * (I.card : ℝ) * (Fintype.card F : ℝ) ^ 2 ≤
      (feasibleMass data I T (frozenPool T x) : ℝ)) :
    (FiniteLaw.uniform (FreshAssignment (F := F) T)).prob
      (fun y => NoFeasibleOutside data I T (joinAssignments T x y)) ≤
        Real.exp (-(((K : ℝ) * δ - 2) * I.card)) := by
  have hsum := sum_fresh_feasibleDensity_ge data I T (frozenPool T x) δ
    hT hcard hdensity
  refine (prob_noFeasibleOutside_join_le_exp_neg_sum data I T x).trans ?_
  exact Real.exp_le_exp.mpr (neg_le_neg hsum)

theorem prob_noFeasibleOutside_le_density_bad_add_exp (data : Data F n)
    (I : Finset (Fin n)) (T : Finset (Position n K)) (δ : ℝ)
    (hT : T ⊆ targetPositions I K) (hcard : T.card ≤ 2 * I.card) :
    (poolLaw F n K).prob (NoFeasibleOutside data I T) ≤
      (poolLaw F n K).prob (fun pool =>
        (feasibleMass data I T pool : ℝ) <
          δ * (I.card : ℝ) * (Fintype.card F : ℝ) ^ 2) +
        Real.exp (-(((K : ℝ) * δ - 2) * I.card)) := by
  have hsplit := poolLaw_prob_split_le_bad T (NoFeasibleOutside data I T)
    (fun x => (feasibleMass data I T (frozenPool T x) : ℝ) <
      δ * (I.card : ℝ) * (Fintype.card F : ℝ) ^ 2)
    (Real.exp (-(((K : ℝ) * δ - 2) * I.card))) (Real.exp_pos _).le
    (fun x hx => prob_noFeasibleOutside_join_le_of_density data I T x δ hT hcard
      (le_of_not_gt hx))
  rw [← prob_feasibleMass_lt_eq_exposed data I T
    (δ * (I.card : ℝ) * (Fintype.card F : ℝ) ^ 2)] at hsplit
  exact hsplit

end RyserCoveringCounterexample.Selection

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_Chunk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section

namespace RyserCoveringCounterexample.Selection

variable {F : Type*} [Field F] [instFintypeF : Fintype F] [DecidableEq F] {n : ℕ}

theorem equationLoss_le (U : Finset (Point F)) (d : Direction F)
    (c : F) (x : Point F) : equationLoss U d c x ≤ Fintype.card F := by
  change (sliceCount U d (projection d x + c) : ℝ) ≤ (Fintype.card F : ℝ)
  exact_mod_cast sliceCount_le_card_field U d (projection d x + c)

theorem expectation_equationLoss (U : Finset (Point F)) (d : Direction F)
    (c : F) :
    (FiniteLaw.uniform (Point F)).expectation (equationLoss U d c) =
      (U.card : ℝ) / Fintype.card F := by
  exact expectation_uniform_shifted_slice U d c

theorem variance_equationLoss (U : Finset (Point F)) (d : Direction F)
    (c : F) :
    (FiniteLaw.uniform (Point F)).variance (equationLoss U d c) =
      sliceEnergy U d := by
  exact variance_uniform_shifted_slice U d c

private theorem sum_le_of_card_le {A : Type*} (s : Finset A) (N : ℕ)
    (f : A → ℝ) (b : ℝ) (hcard : s.card ≤ N) (hb : 0 ≤ b)
    (hf : ∀ a ∈ s, f a ≤ b) : (∑ a ∈ s, f a) ≤ N * b := by
  calc
    (∑ a ∈ s, f a) ≤ ∑ _a ∈ s, b := Finset.sum_le_sum hf
    _ = (s.card : ℝ) * b := by simp
    _ ≤ (N : ℝ) * b := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hb

private theorem triple_sum_le {A B C : Type*} (s : Finset A)
    (t : Finset B) (u : Finset C) (N : ℕ) (f : A → B → C → ℝ)
    (b : ℝ) (hs : s.card ≤ N) (ht : t.card ≤ N) (hu : u.card ≤ N)
    (hb : 0 ≤ b) (hf : ∀ a ∈ s, ∀ c ∈ t, ∀ e ∈ u, f a c e ≤ b) :
    (∑ a ∈ s, ∑ c ∈ t, ∑ e ∈ u, f a c e) ≤ (N : ℝ) ^ 3 * b := by
  calc
    _ ≤ (N : ℝ) * ((N : ℝ) * ((N : ℝ) * b)) := by
      apply sum_le_of_card_le s N _ _ hs (by positivity)
      intro a ha
      apply sum_le_of_card_le t N _ _ ht (by positivity)
      intro c hc
      exact sum_le_of_card_le u N _ b hu hb (hf a ha c hc)
    _ = _ := by ring

private theorem variance_sum_le_of_card_le {A Ω : Type*} [Fintype Ω]
    (mu : FiniteLaw Ω) (s : Finset A) (N : ℕ) (f : A → Ω → ℝ)
    (hs : s.card ≤ N) :
    mu.variance (fun x => ∑ a ∈ s, f a x) ≤
      (N : ℝ) * ∑ a ∈ s, mu.variance (f a) := by
  refine (mu.variance_sum_le s f).trans ?_
  apply mul_le_mul_of_nonneg_right (by exact_mod_cast hs)
  exact Finset.sum_nonneg (fun a _ => mu.variance_nonneg (f a))

private theorem variance_triple_sum_le {A B C Ω : Type*} [Fintype Ω]
    (mu : FiniteLaw Ω) (s : Finset A) (t : Finset B) (u : Finset C)
    (N : ℕ) (f : A → B → C → Ω → ℝ)
    (hs : s.card ≤ N) (ht : t.card ≤ N) (hu : u.card ≤ N) :
    mu.variance (fun x => ∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, f a b c x) ≤
      (N : ℝ) ^ 3 * ∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, mu.variance (f a b c) := by
  calc
    _ ≤ (N : ℝ) * ∑ a ∈ s,
        mu.variance (fun x => ∑ b ∈ t, ∑ c ∈ u, f a b c x) :=
      variance_sum_le_of_card_le mu s N _ hs
    _ ≤ (N : ℝ) * ∑ a ∈ s, (N : ℝ) * ∑ b ∈ t,
        (N : ℝ) * ∑ c ∈ u, mu.variance (f a b c) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
      apply Finset.sum_le_sum
      intro a ha
      refine (variance_sum_le_of_card_le mu t N _ ht).trans ?_
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
      apply Finset.sum_le_sum
      intro b hb
      exact variance_sum_le_of_card_le mu u N _ hu
    _ = _ := by simp only [← Finset.mul_sum]; ring

theorem lossByDirections_le (D : ℕ) (data : Data F n)
    (I : Finset (Fin n)) (U : Fin n → Finset (Point F)) (j : Fin n)
    (dirs : Fin n → Finset (Direction F))
    (hW : ∀ i, (data.W i).card ≤ D) (hdirs : ∀ i, (dirs i).card ≤ D)
    (x : Point F) :
    lossByDirections data I U j dirs x ≤
      (D : ℝ) ^ 3 * I.card * Fintype.card F := by
  calc
    _ ≤ ∑ _i ∈ I, (D : ℝ) ^ 3 * Fintype.card F := by
      apply Finset.sum_le_sum
      intro i hi
      exact triple_sum_le (dirs i) (data.W i) (data.W j) D _ _
        (hdirs i) (hW i) (hW j) (Nat.cast_nonneg _) (fun d _ u _ v _ =>
          equationLoss_le (U i) d (projection d (v - u)) x)
    _ = _ := by simp; ring

theorem expectation_lossByDirections_le (D : ℕ) (data : Data F n)
    (I : Finset (Fin n)) (U : Fin n → Finset (Point F)) (j : Fin n)
    (dirs : Fin n → Finset (Direction F))
    (hW : ∀ i, (data.W i).card ≤ D) (hdirs : ∀ i, (dirs i).card ≤ D) :
    (FiniteLaw.uniform (Point F)).expectation (lossByDirections data I U j dirs) ≤
      (D : ℝ) ^ 3 * frozenMass I U / Fintype.card F := by
  calc
    _ = ∑ i ∈ I, ∑ d ∈ dirs i, ∑ u ∈ data.W i, ∑ v ∈ data.W j,
        (U i).card / (Fintype.card F : ℝ) := by
      unfold lossByDirections
      simp_rw [FiniteLaw.expectation_finset_sum]
      simp_rw [expectation_equationLoss]
    _ ≤ ∑ i ∈ I, (D : ℝ) ^ 3 * ((U i).card / (Fintype.card F : ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact triple_sum_le (dirs i) (data.W i) (data.W j) D _ _
        (hdirs i) (hW i) (hW j) (by positivity) (fun _ _ _ _ _ _ => le_rfl)
    _ = _ := by simp only [frozenMass, ← Finset.mul_sum, ← Finset.sum_div]; ring

theorem entryLoss_le (D : ℕ) (data : Data F n) (hdata : Bounded D data)
    (I : Finset (Fin n)) (U : Fin n → Finset (Point F)) (j : Fin n)
    (x : Point F) :
    entryLoss data I U j x ≤ 2 * (D : ℝ) ^ 3 * I.card * Fintype.card F := by
  have ht := lossByDirections_le D data I U j data.dirs hdata.2.1 hdata.2.2.1 x
  have hs := lossByDirections_le D data I U j (fun _ => data.dirs j)
    hdata.2.1 (fun _ => hdata.2.2.1 j) x
  unfold entryLoss targetLoss sourceLoss
  linarith

theorem expectation_entryLoss_le (D : ℕ) (data : Data F n) (hdata : Bounded D data)
    (I : Finset (Fin n)) (U : Fin n → Finset (Point F)) (j : Fin n) :
    (FiniteLaw.uniform (Point F)).expectation (entryLoss data I U j) ≤
      2 * (D : ℝ) ^ 3 * frozenMass I U / Fintype.card F := by
  have ht := expectation_lossByDirections_le D data I U j data.dirs
    hdata.2.1 hdata.2.2.1
  have hs := expectation_lossByDirections_le D data I U j (fun _ => data.dirs j)
    hdata.2.1 (fun _ => hdata.2.2.1 j)
  unfold entryLoss
  rw [FiniteLaw.expectation_add]
  change (FiniteLaw.uniform (Point F)).expectation (lossByDirections data I U j data.dirs) +
    (FiniteLaw.uniform (Point F)).expectation (lossByDirections data I U j
      (fun _ => data.dirs j)) ≤ _
  calc
    _ ≤ (D : ℝ) ^ 3 * frozenMass I U / Fintype.card F +
        (D : ℝ) ^ 3 * frozenMass I U / Fintype.card F := add_le_add ht hs
    _ = _ := by ring

theorem sourceEnergy_nonneg (data : Data F n) (I : Finset (Fin n))
    (U : Fin n → Finset (Point F)) (j : Fin n) :
    0 ≤ sourceEnergy data I U j := by
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg
    (fun d _ => sliceEnergy_nonneg (U i) d))

theorem variance_sourceLoss_le (D : ℕ) (data : Data F n) (hdata : Bounded D data)
    (I : Finset (Fin n)) (U : Fin n → Finset (Point F)) (j : Fin n) :
    (FiniteLaw.uniform (Point F)).variance (sourceLoss data I U j) ≤
      (D : ℝ) ^ 5 * I.card * sourceEnergy data I U j := by
  let mu := FiniteLaw.uniform (Point F)
  have htarget (i : Fin n) :
      mu.variance (fun x => ∑ d ∈ data.dirs j, ∑ u ∈ data.W i, ∑ v ∈ data.W j,
        equationLoss (U i) d (projection d (v - u)) x) ≤
        (D : ℝ) ^ 5 * ∑ d ∈ data.dirs j, sliceEnergy (U i) d := by
    calc
      _ ≤ (D : ℝ) ^ 3 * ∑ d ∈ data.dirs j, ∑ u ∈ data.W i, ∑ v ∈ data.W j,
          mu.variance (equationLoss (U i) d (projection d (v - u))) :=
        variance_triple_sum_le mu (data.dirs j) (data.W i) (data.W j) D _
          (hdata.2.2.1 j) (hdata.2.1 i) (hdata.2.1 j)
      _ = (D : ℝ) ^ 3 * ∑ d ∈ data.dirs j, ∑ _u ∈ data.W i, ∑ _v ∈ data.W j,
          sliceEnergy (U i) d := by simp only [mu, variance_equationLoss]
      _ ≤ (D : ℝ) ^ 3 * ∑ d ∈ data.dirs j,
          (D : ℝ) * ((D : ℝ) * sliceEnergy (U i) d) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro d hd
        apply sum_le_of_card_le (data.W i) D _ _ (hdata.2.1 i) (mul_nonneg (Nat.cast_nonneg D) (sliceEnergy_nonneg (U i) d))
        intro u hu
        exact sum_le_of_card_le (data.W j) D _ _ (hdata.2.1 j)
          (sliceEnergy_nonneg (U i) d) (fun _ _ => le_rfl)
      _ = _ := by simp only [← Finset.mul_sum]; ring
  calc
    _ ≤ (I.card : ℝ) * ∑ i ∈ I, mu.variance (fun x =>
        ∑ d ∈ data.dirs j, ∑ u ∈ data.W i, ∑ v ∈ data.W j,
          equationLoss (U i) d (projection d (v - u)) x) :=
      mu.variance_sum_le I _
    _ ≤ (I.card : ℝ) * ∑ i ∈ I, (D : ℝ) ^ 5 *
        ∑ d ∈ data.dirs j, sliceEnergy (U i) d :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => htarget i))
        (Nat.cast_nonneg _)
    _ = _ := by simp only [sourceEnergy, ← Finset.mul_sum]; ring

theorem targetDirectionGroup_nonneg (data : Data F n) (I : Finset (Fin n))
    (U : Fin n → Finset (Point F)) (j : Fin n) (d : Direction F) (t : F) :
    0 ≤ targetDirectionGroup data I U j d t := let _ := instFintypeF; by
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun u _ =>
    Finset.sum_nonneg (fun v _ => Nat.cast_nonneg _)))

theorem targetDirectionGroup_le (D : ℕ) (data : Data F n) (hdata : Bounded D data)
    (I : Finset (Fin n)) (U : Fin n → Finset (Point F)) (j : Fin n)
    (d : Direction F) (t : F) :
    targetDirectionGroup data I U j d t ≤ (D : ℝ) ^ 3 * Fintype.card F := by
  have hcount : (I.filter (fun i => d ∈ data.dirs i)).card ≤ D := by
    refine (Finset.card_le_card ?_).trans (hdata.2.2.2 d)
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
  calc
    _ ≤ (D : ℝ) * ((D : ℝ) * ((D : ℝ) * Fintype.card F)) := by
      apply sum_le_of_card_le _ D _ _ hcount (by positivity)
      intro i hi
      apply sum_le_of_card_le _ D _ _ (hdata.2.1 i) (by positivity)
      intro u hu
      apply sum_le_of_card_le _ D _ _ (hdata.2.1 j) (Nat.cast_nonneg _)
      intro v hv
      exact_mod_cast sliceCount_le_card_field (U i) d (t + projection d (v - u))
    _ = _ := by ring

theorem targetLoss_eq_sum_groups (data : Data F n) (I : Finset (Fin n))
    (U : Fin n → Finset (Point F)) (j : Fin n) (x : Point F) :
    targetLoss data I U j x =
      ∑ d ∈ I.biUnion data.dirs, targetDirectionGroup data I U j d (projection d x) := let _ := instFintypeF; by
  classical
  symm
  unfold targetDirectionGroup
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have hfilter : (I.biUnion data.dirs).filter (fun d => d ∈ data.dirs i) =
      data.dirs i := by
    ext d
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun hd => ⟨Finset.mem_biUnion.mpr ⟨i, hi, hd⟩, hd⟩⟩
  rw [← Finset.sum_filter, hfilter]
  rfl

theorem variance_targetLoss_le (D : ℕ) (data : Data F n) (hdata : Bounded D data)
    (I : Finset (Fin n)) (U : Fin n → Finset (Point F)) (j : Fin n) :
    (FiniteLaw.uniform (Point F)).variance (targetLoss data I U j) ≤
      (D : ℝ) ^ 7 * I.card * (Fintype.card F : ℝ) ^ 2 := by
  let mu := FiniteLaw.uniform (Point F)
  let S := I.biUnion data.dirs
  have hS : S.card ≤ I.card * D := by
    refine Finset.card_biUnion_le.trans ?_
    calc
      (∑ i ∈ I, (data.dirs i).card) ≤ ∑ _i ∈ I, D :=
        Finset.sum_le_sum (fun i _ => hdata.2.2.1 i)
      _ = I.card * D := by simp
  have heq : targetLoss data I U j = fun x =>
      ∑ d ∈ S, targetDirectionGroup data I U j d (projection d x) := by
    funext x
    exact targetLoss_eq_sum_groups data I U j x
  rw [heq]
  calc
    _ = ∑ d ∈ S, mu.variance (fun x =>
        targetDirectionGroup data I U j d (projection d x)) := by
      apply mu.variance_sum_of_pairwise_covariance_zero
      intro d hd e he hde
      exact covariance_uniform_projection d e hde
        (targetDirectionGroup data I U j d) (targetDirectionGroup data I U j e)
    _ ≤ ∑ _d ∈ S, ((D : ℝ) ^ 3 * Fintype.card F) ^ 2 := by
      apply Finset.sum_le_sum
      intro d hd
      exact mu.variance_le_sq_of_bounds _
        (fun x => targetDirectionGroup_nonneg data I U j d (projection d x))
        (fun x => targetDirectionGroup_le D data hdata I U j d (projection d x))
    _ = (S.card : ℝ) * ((D : ℝ) ^ 3 * Fintype.card F) ^ 2 := by simp
    _ ≤ ((I.card * D : ℕ) : ℝ) * ((D : ℝ) ^ 3 * Fintype.card F) ^ 2 :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hS) (sq_nonneg _)
    _ = _ := by simp only [Nat.cast_mul]; ring

theorem variance_entryLoss_le (D : ℕ) (data : Data F n) (hdata : Bounded D data)
    (I : Finset (Fin n)) (U : Fin n → Finset (Point F)) (j : Fin n) :
    (FiniteLaw.uniform (Point F)).variance (entryLoss data I U j) ≤
      2 * (D : ℝ) ^ 7 * I.card * (Fintype.card F : ℝ) ^ 2 +
        2 * (D : ℝ) ^ 5 * I.card * sourceEnergy data I U j := by
  have ht := variance_targetLoss_le D data hdata I U j
  have hs := variance_sourceLoss_le D data hdata I U j
  have hsum := (FiniteLaw.uniform (Point F)).variance_add_le
    (targetLoss data I U j) (sourceLoss data I U j)
  change (FiniteLaw.uniform (Point F)).variance
    (fun x => targetLoss data I U j x + sourceLoss data I U j x) ≤ _
  linarith

end RyserCoveringCounterexample.Selection

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_ChunkEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section

namespace RyserCoveringCounterexample.Selection

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n K : ℕ}

theorem card_entries_with_direction_le (D : ℕ) (data : Data F n)
    (hdata : Bounded D data) (E : Finset (Position n K)) (d : Direction F) :
    (E.filter (fun e => d ∈ data.dirs e.1)).card ≤ K * D := by
  have hsub : E.filter (fun e => d ∈ data.dirs e.1) ⊆
      (Finset.univ.filter (fun i => d ∈ data.dirs i)) ×ˢ
        (Finset.univ : Finset (Fin K)) := by
    intro e he
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (Finset.mem_filter.mp he).2⟩, Finset.mem_univ _⟩
  calc
    _ ≤ ((Finset.univ.filter (fun i => d ∈ data.dirs i)) ×ˢ
        (Finset.univ : Finset (Fin K))).card := Finset.card_le_card hsub
    _ = (Finset.univ.filter (fun i => d ∈ data.dirs i)).card * K := by simp
    _ ≤ D * K := Nat.mul_le_mul_right K (hdata.2.2.2 d)
    _ = K * D := Nat.mul_comm _ _

theorem sum_sourceEnergy_eq (data : Data F n) (I : Finset (Fin n))
    (U : Fin n → Finset (Point F)) (E : Finset (Position n K)) :
    (∑ e ∈ E, sourceEnergy data I U e.1) =
      ∑ i ∈ I, ∑ d : Direction F,
        ((E.filter (fun e => d ∈ data.dirs e.1)).card : ℝ) * sliceEnergy (U i) d := by
  classical
  unfold sourceEnergy
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    _ = ∑ e ∈ E, ∑ d : Direction F,
        if d ∈ data.dirs e.1 then sliceEnergy (U i) d else 0 := by
      apply Finset.sum_congr rfl
      intro e he
      rw [← Finset.sum_filter]
      simp
    _ = ∑ d : Direction F, ∑ e ∈ E,
        if d ∈ data.dirs e.1 then sliceEnergy (U i) d else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Finset.sum_filter]
      simp

theorem sum_sourceEnergy_le (D : ℕ) (data : Data F n) (hdata : Bounded D data)
    (I : Finset (Fin n)) (U : Fin n → Finset (Point F))
    (E : Finset (Position n K)) :
    (∑ e ∈ E, sourceEnergy data I U e.1) ≤
      (K : ℝ) * D * I.card * (Fintype.card F : ℝ) ^ 2 := by
  rw [sum_sourceEnergy_eq]
  calc
    _ ≤ ∑ i ∈ I, ∑ d : Direction F, ((K : ℝ) * D) * sliceEnergy (U i) d := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast card_entries_with_direction_le D data hdata E d)
        (sliceEnergy_nonneg (U i) d)
    _ = ∑ i ∈ I, ((K : ℝ) * D) * ∑ d : Direction F, sliceEnergy (U i) d := by
      simp only [Finset.mul_sum]
    _ ≤ ∑ _i ∈ I, ((K : ℝ) * D) * (Fintype.card F : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (sum_sliceEnergy_le_sq_card (U i)) (by positivity)
    _ = _ := by simp; ring

end RyserCoveringCounterexample.Selection

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_ChunkLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace RyserCoveringCounterexample.Selection

section FiniteSets

variable {ι ε β : Type*} [DecidableEq β]

theorem card_le_card_sdiff_biUnion_add_sum_card_inter
    (U : Finset β) (E : Finset ε) (L : ε → Finset β) :
    U.card ≤ (U \ E.biUnion L).card + ∑ e ∈ E, (U ∩ L e).card := by
  have hpartition := Finset.card_sdiff_add_card_inter U (E.biUnion L)
  have hcover : (U ∩ E.biUnion L).card ≤ ∑ e ∈ E, (U ∩ L e).card := by
    rw [Finset.inter_biUnion]
    exact Finset.card_biUnion_le
  omega

theorem sum_card_le_sum_card_sdiff_biUnion_add_sum_card_inter
    (I : Finset ι) (U : ι → Finset β) (E : Finset ε)
    (L : ε → ι → Finset β) :
    (∑ i ∈ I, (U i).card) ≤
      (∑ i ∈ I, (U i \ E.biUnion (fun e => L e i)).card) +
        ∑ e ∈ E, ∑ i ∈ I, (U i ∩ L e i).card := by
  calc
    (∑ i ∈ I, (U i).card) ≤
        ∑ i ∈ I, ((U i \ E.biUnion (fun e => L e i)).card +
          ∑ e ∈ E, (U i ∩ L e i).card) := by
      exact Finset.sum_le_sum fun i _ =>
        card_le_card_sdiff_biUnion_add_sum_card_inter (U i) E (fun e => L e i)
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_comm]

theorem sum_card_sub_sum_card_sdiff_biUnion_le
    (I : Finset ι) (U : ι → Finset β) (E : Finset ε)
    (L : ε → ι → Finset β) :
    (∑ i ∈ I, ((U i).card : ℝ)) -
      (∑ i ∈ I, ((U i \ E.biUnion (fun e => L e i)).card : ℝ)) ≤
        ∑ e ∈ E, ∑ i ∈ I, ((U i ∩ L e i).card : ℝ) := by
  have hnat := sum_card_le_sum_card_sdiff_biUnion_add_sum_card_inter I U E L
  have hreal := (Nat.cast_le (α := ℝ)).mpr hnat
  simp only [Nat.cast_add, Nat.cast_sum] at hreal
  linarith

end FiniteSets

section Configurations

variable {F : Type*} [Field F] [instFintypeF : Fintype F] [DecidableEq F] {n K : ℕ}

theorem chunkFeasibleSet_eq_sdiff_biUnion (data : Data F n)
    (U : Fin n → Finset (Point F)) (E : Finset (Position n K))
    (pool : Pool F n K) (i : Fin n) :
    chunkFeasibleSet data U E pool i =
      U i \ E.biUnion (fun e => conflictingPoints data (U i) i e.1 (pool e)) := by
  classical
  ext b
  simp only [mem_chunkFeasibleSet, Finset.mem_sdiff, Finset.mem_biUnion,
    mem_conflictingPoints, Feasible]
  constructor
  · rintro ⟨hb, hfeasible⟩
    refine ⟨hb, ?_⟩
    rintro ⟨e, he, _, hconflict⟩
    exact hfeasible e he hconflict
  · rintro ⟨hb, havoid⟩
    refine ⟨hb, ?_⟩
    intro e he hconflict
    exact havoid ⟨e, he, hb, hconflict⟩

theorem chunkFeasibleSet_feasibleSet (data : Data F n)
    (P E : Finset (Position n K)) (pool : Pool F n K) (i : Fin n) :
    chunkFeasibleSet data (feasibleSet data P pool) E pool i =
      feasibleSet data (P ∪ E) pool i := by
  classical
  ext b
  simp only [mem_chunkFeasibleSet, mem_feasibleSet, Feasible, Finset.mem_union]
  constructor
  · rintro ⟨hP, hE⟩ e (he | he)
    · exact hP e he
    · exact hE e he
  · intro h
    exact ⟨fun e he => h e (Or.inl he), fun e he => h e (Or.inr he)⟩

theorem sum_card_sub_sum_card_chunkFeasibleSet_le_conflictingPoints
    (data : Data F n) (I : Finset (Fin n)) (U : Fin n → Finset (Point F))
    (E : Finset (Position n K)) (pool : Pool F n K) :
    (∑ i ∈ I, ((U i).card : ℝ)) -
      (∑ i ∈ I, ((chunkFeasibleSet data U E pool i).card : ℝ)) ≤
        ∑ e ∈ E, ∑ i ∈ I, ((conflictingPoints data (U i) i e.1 (pool e)).card : ℝ) := by
  classical
  have h := sum_card_sub_sum_card_sdiff_biUnion_le I U E
    (fun e i => conflictingPoints data (U i) i e.1 (pool e))
  simpa only [chunkFeasibleSet_eq_sdiff_biUnion, conflictingPoints,
    Finset.inter_filter, Finset.inter_self] using h

end Configurations

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n K : ℕ}

theorem card_conflictingPoints_le_equationLoss (data : Data F n)
    (U : Finset (Point F)) (i j : Fin n) (x : Point F) :
    ((conflictingPoints data U i j x).card : ℝ) ≤
      (∑ d ∈ data.dirs i, ∑ u ∈ data.W i, ∑ v ∈ data.W j,
        equationLoss U d (projection d (v - u)) x) +
      (∑ d ∈ data.dirs j, ∑ u ∈ data.W i, ∑ v ∈ data.W j,
        equationLoss U d (projection d (v - u)) x) := by
  classical
  let slices : Direction F → Point F → Point F → Finset (Point F) :=
    fun d u v => U.filter fun b =>
      projection d b = projection d x + projection d (v - u)
  let covered : Finset (Direction F) → Finset (Point F) := fun ds =>
    ds.biUnion fun d => (data.W i).biUnion fun u =>
      (data.W j).biUnion fun v => slices d u v
  have hcover : conflictingPoints data U i j x ⊆
      covered (data.dirs i) ∪ covered (data.dirs j) := by
    intro b hb
    obtain ⟨hbU, hconflict⟩ := (mem_conflictingPoints data U i j x b).mp hb
    obtain ⟨u, hu, v, hv, d, hd, heq⟩ :=
      (conflict_iff_forbidden data i j b x).mp hconflict
    have hmem (ds : Finset (Direction F)) (hd' : d ∈ ds) : b ∈ covered ds := by
      change b ∈ ds.biUnion (fun d => (data.W i).biUnion (fun u =>
        (data.W j).biUnion (fun v => slices d u v)))
      apply Finset.mem_biUnion.mpr
      refine ⟨d, hd', Finset.mem_biUnion.mpr ?_⟩
      refine ⟨u, hu, Finset.mem_biUnion.mpr ?_⟩
      refine ⟨v, hv, ?_⟩
      exact Finset.mem_filter.mpr ⟨hbU, heq⟩
    rcases Finset.mem_union.mp hd with hdi | hdj
    · exact Finset.mem_union.mpr (Or.inl (hmem _ hdi))
    · exact Finset.mem_union.mpr (Or.inr (hmem _ hdj))
  have hcount (ds : Finset (Direction F)) :
      (covered ds).card ≤
        ∑ d ∈ ds, ∑ u ∈ data.W i, ∑ v ∈ data.W j, (slices d u v).card := by
    dsimp only [covered]
    refine Finset.card_biUnion_le.trans (Finset.sum_le_sum ?_)
    intro d hd
    refine Finset.card_biUnion_le.trans (Finset.sum_le_sum ?_)
    intro u hu
    exact Finset.card_biUnion_le
  have hnat : (conflictingPoints data U i j x).card ≤
      (∑ d ∈ data.dirs i, ∑ u ∈ data.W i, ∑ v ∈ data.W j, (slices d u v).card) +
      (∑ d ∈ data.dirs j, ∑ u ∈ data.W i, ∑ v ∈ data.W j, (slices d u v).card) :=
    (Finset.card_le_card hcover).trans
      ((Finset.card_union_le _ _).trans
        (Nat.add_le_add (hcount (data.dirs i)) (hcount (data.dirs j))))
  have hreal := (Nat.cast_le (α := ℝ)).mpr hnat
  simpa only [Nat.cast_add, Nat.cast_sum, slices, equationLoss, sliceCount] using hreal

theorem sum_card_conflictingPoints_le_entryLoss (data : Data F n)
    (I : Finset (Fin n)) (U : Fin n → Finset (Point F)) (j : Fin n) (x : Point F) :
    (∑ i ∈ I, ((conflictingPoints data (U i) i j x).card : ℝ)) ≤
      entryLoss data I U j x := by
  calc
    _ ≤ ∑ i ∈ I,
        ((∑ d ∈ data.dirs i, ∑ u ∈ data.W i, ∑ v ∈ data.W j,
          equationLoss (U i) d (projection d (v - u)) x) +
        (∑ d ∈ data.dirs j, ∑ u ∈ data.W i, ∑ v ∈ data.W j,
          equationLoss (U i) d (projection d (v - u)) x)) :=
      Finset.sum_le_sum fun i _ => card_conflictingPoints_le_equationLoss data (U i) i j x
    _ = entryLoss data I U j x := by
      rw [Finset.sum_add_distrib]
      rfl

theorem chunk_mass_loss_le_entryLoss (data : Data F n) (I : Finset (Fin n))
    (U : Fin n → Finset (Point F)) (E : Finset (Position n K))
    (pool : Pool F n K) :
    frozenMass I U - frozenMass I (chunkFeasibleSet data U E pool) ≤
      ∑ e ∈ E, entryLoss data I U e.1 (pool e) := by
  refine (sum_card_sub_sum_card_chunkFeasibleSet_le_conflictingPoints
    data I U E pool).trans ?_
  exact Finset.sum_le_sum fun e _ =>
    sum_card_conflictingPoints_le_entryLoss data I U e.1 (pool e)

end RyserCoveringCounterexample.Selection

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_RegularTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace RyserCoveringCounterexample.Selection

theorem prob_regular_target_gt_le {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (Z : Ω → ℝ) (D m q γ C M : ℝ)
    (hm : 0 < m) (hq : 0 < q) (hγ : 0 < γ)
    (hmean : μ.expectation Z ≤ C * M / q)
    (hvar : μ.variance Z ≤ 2 * D ^ 7 * m * q ^ 2 +
      2 * D ^ 5 * m ^ 2 * q * Real.sqrt q) :
    μ.prob (fun x => C * M / q + γ * m * q < Z x) ≤
      2 * D ^ 7 / (γ ^ 2 * m) + 2 * D ^ 5 / (γ ^ 2 * Real.sqrt q) := by
  have ht : 0 < γ * m * q := mul_pos (mul_pos hγ hm) hq
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  calc
    μ.prob (fun x => C * M / q + γ * m * q < Z x) ≤
        μ.variance Z / (γ * m * q) ^ 2 :=
      μ.prob_gt_mean_bound_add_le Z (C * M / q) (γ * m * q) hmean ht
    _ ≤ (2 * D ^ 7 * m * q ^ 2 + 2 * D ^ 5 * m ^ 2 * q * Real.sqrt q) /
        (γ * m * q) ^ 2 :=
      div_le_div_of_nonneg_right hvar (sq_nonneg _)
    _ = 2 * D ^ 7 / (γ ^ 2 * m) + (2 * D ^ 5 / γ ^ 2) * (Real.sqrt q / q) := by
      field_simp [hγ.ne', hm.ne', hq.ne']
    _ = 2 * D ^ 7 / (γ ^ 2 * m) + (2 * D ^ 5 / γ ^ 2) * (1 / Real.sqrt q) := by
      rw [Real.sqrt_div_self']
    _ = 2 * D ^ 7 / (γ ^ 2 * m) + 2 * D ^ 5 / (γ ^ 2 * Real.sqrt q) := by
      field_simp [hγ.ne', hm.ne', hs.ne']

theorem regular_tail_bound_le_sqrt (D m q C γ : ℝ)
    (hD : 0 ≤ D) (hm : 0 < m) (hq : 1 ≤ q)
    (hC : 0 < C) (hγ : 0 < γ) (hlarge : q / (4 * C) < m) :
    2 * D ^ 7 / (γ ^ 2 * m) + 2 * D ^ 5 / (γ ^ 2 * Real.sqrt q) ≤
      ((8 * C * D ^ 7 + 2 * D ^ 5) / γ ^ 2) / Real.sqrt q := by
  have hs : 0 < Real.sqrt q :=
    Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one hq)
  have hsle : Real.sqrt q ≤ q := Real.sqrt_le_self_iff.mpr (Or.inr hq)
  have hg2 : 0 < γ ^ 2 := pow_pos hγ 2
  have h4C : 0 < 4 * C := mul_pos (by norm_num) hC
  have hsm : Real.sqrt q ≤ (4 * C) * m := by
    calc
      Real.sqrt q ≤ q := hsle
      _ ≤ m * (4 * C) := ((div_lt_iff₀ h4C).mp hlarge).le
      _ = (4 * C) * m := mul_comm _ _
  have hcoef : 0 ≤ 2 * D ^ 7 * γ ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hD 7)) hg2.le
  have hfirst : 2 * D ^ 7 / (γ ^ 2 * m) ≤
      8 * C * D ^ 7 / (γ ^ 2 * Real.sqrt q) := by
    apply (div_le_div_iff₀ (mul_pos hg2 hm) (mul_pos hg2 hs)).mpr
    calc
      (2 * D ^ 7) * (γ ^ 2 * Real.sqrt q) =
          (2 * D ^ 7 * γ ^ 2) * Real.sqrt q := by ring
      _ ≤ (2 * D ^ 7 * γ ^ 2) * ((4 * C) * m) :=
        mul_le_mul_of_nonneg_left hsm hcoef
      _ = (8 * C * D ^ 7) * (γ ^ 2 * m) := by ring
  calc
    2 * D ^ 7 / (γ ^ 2 * m) + 2 * D ^ 5 / (γ ^ 2 * Real.sqrt q) ≤
        8 * C * D ^ 7 / (γ ^ 2 * Real.sqrt q) +
          2 * D ^ 5 / (γ ^ 2 * Real.sqrt q) := add_le_add hfirst le_rfl
    _ = ((8 * C * D ^ 7 + 2 * D ^ 5) / γ ^ 2) / Real.sqrt q := by
      rw [← add_div, div_div]

theorem prob_regular_target_gt_le_sqrt {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (Z : Ω → ℝ) (D m q γ C M : ℝ)
    (hD : 0 ≤ D) (hm : 0 < m) (hq : 1 ≤ q) (hγ : 0 < γ) (hC : 0 < C)
    (hlarge : q / (4 * C) < m)
    (hmean : μ.expectation Z ≤ C * M / q)
    (hvar : μ.variance Z ≤ 2 * D ^ 7 * m * q ^ 2 +
      2 * D ^ 5 * m ^ 2 * q * Real.sqrt q) :
    μ.prob (fun x => C * M / q + γ * m * q < Z x) ≤
      ((8 * C * D ^ 7 + 2 * D ^ 5) / γ ^ 2) / Real.sqrt q := by
  exact (prob_regular_target_gt_le μ Z D m q γ C M hm
    (lt_of_lt_of_le zero_lt_one hq) hγ hmean hvar).trans
      (regular_tail_bound_le_sqrt D m q C γ hD hm hq hC hγ hlarge)

theorem card_irregular_le {ι : Type*} (S : Finset ι) (A : ι → ℝ) (K D m q : ℝ)
    (hm : 0 < m) (hq : 0 < q) (hA : ∀ i ∈ S, 0 ≤ A i)
    (hsum : (∑ i ∈ S, A i) ≤ K * D * m * q ^ 2) :
    ((S.filter (fun i => m * q * Real.sqrt q < A i)).card : ℝ) ≤
      K * D * Real.sqrt q := by
  classical
  let T := S.filter (fun i => m * q * Real.sqrt q < A i)
  change (T.card : ℝ) ≤ K * D * Real.sqrt q
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have ht : 0 < m * q * Real.sqrt q := mul_pos (mul_pos hm hq) hs
  have hcount : (T.card : ℝ) * (m * q * Real.sqrt q) ≤ ∑ i ∈ T, A i := by
    simpa only [nsmul_eq_mul] using
      (Finset.card_nsmul_le_sum T A (m * q * Real.sqrt q)
        (fun i hi => (Finset.mem_filter.mp hi).2.le))
  have hsub : (∑ i ∈ T, A i) ≤ ∑ i ∈ S, A i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i hi _ => hA i hi)
  have hquot : (T.card : ℝ) ≤ (K * D * m * q ^ 2) / (m * q * Real.sqrt q) :=
    (le_div_iff₀ ht).mpr (hcount.trans (hsub.trans hsum))
  calc
    (T.card : ℝ) ≤ (K * D * m * q ^ 2) / (m * q * Real.sqrt q) := hquot
    _ = K * D * (q / Real.sqrt q) := by
      field_simp [hm.ne', hq.ne', hs.ne']
    _ = K * D * Real.sqrt q := by rw [Real.div_sqrt]

end RyserCoveringCounterexample.Selection

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_ChunkTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.Selection

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n K : ℕ}

theorem regularTailConstant_nonneg (D : ℕ) (γ : ℝ) :
    0 ≤ regularTailConstant D γ := by
  unfold regularTailConstant equationBound
  positivity

theorem prob_regular_entry_gt_le (D : ℕ) (hD : 1 ≤ D) (data : Data F n)
    (hdata : Bounded D data) (I : Finset (Fin n))
    (U : Fin n → Finset (Point F)) (j : Fin n) (γ : ℝ)
    (hm : 0 < (I.card : ℝ)) (hγ : 0 < γ)
    (hlarge : (Fintype.card F : ℝ) / (4 * equationBound D) < I.card)
    (hregular : RegularEntry data I U j) :
    (FiniteLaw.uniform (Point F)).prob (fun x =>
      equationBound D * frozenMass I U / Fintype.card F +
        γ * I.card * Fintype.card F < entryLoss data I U j x) ≤
      regularTailConstant D γ / Real.sqrt (Fintype.card F) := by
  have hq : (1 : ℝ) ≤ Fintype.card F := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero
  have hC : 0 < equationBound D := by
    have hDr : (0 : ℝ) < D := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
    unfold equationBound
    positivity
  have hmean : (FiniteLaw.uniform (Point F)).expectation (entryLoss data I U j) ≤
      equationBound D * frozenMass I U / Fintype.card F := by
    simpa only [equationBound] using expectation_entryLoss_le D data hdata I U j
  have hvar : (FiniteLaw.uniform (Point F)).variance (entryLoss data I U j) ≤
      2 * (D : ℝ) ^ 7 * I.card * (Fintype.card F : ℝ) ^ 2 +
        2 * (D : ℝ) ^ 5 * (I.card : ℝ) ^ 2 * Fintype.card F *
          Real.sqrt (Fintype.card F) := by
    have hactual := variance_entryLoss_le D data hdata I U j
    have hmul := mul_le_mul_of_nonneg_left hregular
      (by positivity : 0 ≤ 2 * (D : ℝ) ^ 5 * I.card)
    unfold RegularEntry at hregular
    change 2 * (D : ℝ) ^ 5 * I.card * sourceEnergy data I U j ≤
      2 * (D : ℝ) ^ 5 * I.card *
        ((I.card : ℝ) * Fintype.card F * Real.sqrt (Fintype.card F)) at hmul
    nlinarith
  exact prob_regular_target_gt_le_sqrt (FiniteLaw.uniform (Point F))
    (entryLoss data I U j) D I.card (Fintype.card F) γ (equationBound D)
    (frozenMass I U) (Nat.cast_nonneg D) hm hq hγ hC hlarge hmean hvar

theorem card_irregularEntries_le (D : ℕ) (data : Data F n) (hdata : Bounded D data)
    (I : Finset (Fin n)) (U : Fin n → Finset (Point F))
    (E : Finset (Position n K)) (hm : 0 < (I.card : ℝ)) :
    ((E.filter (fun e : Position n K => ¬ RegularEntry data I U e.1)).card : ℝ) ≤
      (K : ℝ) * D * Real.sqrt (Fintype.card F) := by
  classical
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  simpa only [RegularEntry, not_le] using card_irregular_le E
    (fun e => sourceEnergy data I U e.1) K D I.card (Fintype.card F) hm hq
    (fun e _ => sourceEnergy_nonneg data I U e.1)
    (sum_sourceEnergy_le D data hdata I U E)

theorem prob_many_regular_exceedances_le (D : ℕ) (hD : 1 ≤ D) (data : Data F n)
    (hdata : Bounded D data) (I : Finset (Fin n))
    (U : Fin n → Finset (Point F)) (E : Finset (Position n K)) (γ : ℝ)
    (hm : 0 < (I.card : ℝ)) (hγ : 0 < γ)
    (hlarge : (Fintype.card F : ℝ) / (4 * equationBound D) < I.card) :
    (FiniteLaw.pi (fun _ : Position n K => FiniteLaw.uniform (Point F))).prob
      (fun pool => Nat.ceil (γ * Fintype.card F) ≤
        ((regularEntries data I U E).filter (fun e =>
          equationBound D * frozenMass I U / Fintype.card F +
            γ * I.card * Fintype.card F < entryLoss data I U e.1 (pool e))).card) ≤
      (2 : ℝ) ^ E.card *
        (regularTailConstant D γ / Real.sqrt (Fintype.card F)) ^
          Nat.ceil (γ * Fintype.card F) := by
  classical
  have hp : 0 ≤ regularTailConstant D γ / Real.sqrt (Fintype.card F) :=
    div_nonneg (regularTailConstant_nonneg D γ) (Real.sqrt_nonneg _)
  have htail := prob_many_coordinate_events_le
    (fun _ : Position n K => FiniteLaw.uniform (Point F))
    (regularEntries data I U E)
    (fun e x => equationBound D * frozenMass I U / Fintype.card F +
      γ * I.card * Fintype.card F < entryLoss data I U e.1 x)
    (Nat.ceil (γ * Fintype.card F))
    (regularTailConstant D γ / Real.sqrt (Fintype.card F)) hp
    (fun e he => prob_regular_entry_gt_le D hD data hdata I U e.1 γ hm hγ hlarge
      (Finset.mem_filter.mp he).2)
  refine htail.trans ?_
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hp _)
  exact pow_le_pow_right₀ (by norm_num) (Finset.card_filter_le _ _)

theorem chunk_recurrence_of_few_regular_exceedances (D : ℕ) (data : Data F n)
    (hdata : Bounded D data) (I : Finset (Fin n))
    (U : Fin n → Finset (Point F)) (E : Finset (Position n K))
    (pool : Pool F n K) (α γ : ℝ) (hm : 0 < (I.card : ℝ)) (hγ : 0 ≤ γ)
    (hhalf : equationBound D * α = 1 / 2)
    (hsize : (E.card : ℝ) ≤ α * Fintype.card F)
    (hcutoff : (K : ℝ) * D * Real.sqrt (Fintype.card F) ≤ γ * Fintype.card F)
    (hfew : ((regularEntries data I U E).filter (fun e =>
      equationBound D * frozenMass I U / Fintype.card F +
        γ * I.card * Fintype.card F < entryLoss data I U e.1 (pool e))).card <
      Nat.ceil (γ * Fintype.card F)) :
    frozenMass I U / 2 - (α + 2 * equationBound D) * γ *
        ((I.card : ℝ) * (Fintype.card F : ℝ) ^ 2) ≤
      frozenMass I (chunkFeasibleSet data U E pool) := by
  classical
  let threshold := equationBound D * frozenMass I U / Fintype.card F +
    γ * I.card * Fintype.card F
  let bad : Position n K → Prop := fun e =>
    ¬ RegularEntry data I U e.1 ∨ threshold < entryLoss data I U e.1 (pool e)
  let irregular := E.filter (fun e : Position n K => ¬ RegularEntry data I U e.1)
  let exceeds := (regularEntries data I U E).filter (fun e =>
    threshold < entryLoss data I U e.1 (pool e))
  have hbadsub : E.filter bad ⊆ irregular ∪ exceeds := by
    intro e he
    obtain ⟨heE, heBad⟩ := Finset.mem_filter.mp he
    by_cases hregular : RegularEntry data I U e.1
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨heE, hregular⟩, ?_⟩
      exact heBad.resolve_left (not_not.mpr hregular)
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨heE, hregular⟩))
  have hbadnat : (E.filter bad).card ≤ irregular.card + exceeds.card :=
    (Finset.card_le_card hbadsub).trans (Finset.card_union_le _ _)
  have hirregular : (irregular.card : ℝ) ≤ γ * Fintype.card F :=
    (card_irregularEntries_le D data hdata I U E hm).trans hcutoff
  have hexceeds : (exceeds.card : ℝ) < γ * Fintype.card F := Nat.lt_ceil.mp hfew
  have hbad : ((E.filter bad).card : ℝ) ≤ 2 * γ * Fintype.card F := by
    have hbadreal : ((E.filter bad).card : ℝ) ≤
        (irregular.card : ℝ) + exceeds.card := by exact_mod_cast hbadnat
    linarith
  have hloss := chunk_mass_loss_le_entryLoss data I U E pool
  refine mass_after_chunk_ge E bad (fun e => entryLoss data I U e.1 (pool e))
    (frozenMass I U) (frozenMass I (chunkFeasibleSet data U E pool))
    I.card (Fintype.card F) (equationBound D) α γ ?_ hm.le ?_ ?_ hγ
    hhalf hsize hbad ?_ ?_ ?_
  · exact Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _)
  · exact_mod_cast Fintype.card_pos
  · unfold equationBound
    positivity
  · intro e he hgood
    exact le_of_not_gt (fun hgt => hgood (Or.inr hgt))
  · intro e he hbad
    exact entryLoss_le D data hdata I U e.1 (pool e)
  · linarith

theorem prob_chunk_recurrence_failure_le (D : ℕ) (hD : 1 ≤ D) (data : Data F n)
    (hdata : Bounded D data) (I : Finset (Fin n))
    (U : Fin n → Finset (Point F)) (E : Finset (Position n K)) (α γ : ℝ)
    (hm : 0 < (I.card : ℝ)) (hγ : 0 < γ)
    (hlarge : (Fintype.card F : ℝ) / (4 * equationBound D) < I.card)
    (hhalf : equationBound D * α = 1 / 2)
    (hsize : (E.card : ℝ) ≤ α * Fintype.card F)
    (hcutoff : (K : ℝ) * D * Real.sqrt (Fintype.card F) ≤ γ * Fintype.card F) :
    (FiniteLaw.pi (fun _ : Position n K => FiniteLaw.uniform (Point F))).prob
      (fun pool => frozenMass I (chunkFeasibleSet data U E pool) <
        frozenMass I U / 2 - (α + 2 * equationBound D) * γ *
          ((I.card : ℝ) * (Fintype.card F : ℝ) ^ 2)) ≤
      (2 : ℝ) ^ E.card *
        (regularTailConstant D γ / Real.sqrt (Fintype.card F)) ^
          Nat.ceil (γ * Fintype.card F) := by
  classical
  refine (FiniteLaw.prob_mono _ ?_).trans
    (prob_many_regular_exceedances_le D hD data hdata I U E γ hm hγ hlarge)
  intro pool hfailure
  by_contra hnot
  have hfew := Nat.lt_of_not_ge hnot
  have hgood := chunk_recurrence_of_few_regular_exceedances D data hdata I U E pool
    α γ hm hγ.le hhalf hsize hcutoff hfew
  exact (not_lt_of_ge hgood) hfailure

end RyserCoveringCounterexample.Selection

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_DensityConstants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Selection

theorem densityAlpha_pos (D : ℕ) (hD : 1 ≤ D) : 0 < densityAlpha D := by
  have hDr : (0 : ℝ) < D := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  unfold densityAlpha
  positivity

theorem densityDelta_pos (D : ℕ) : 0 < densityDelta D := by
  unfold densityDelta
  exact pow_pos (by norm_num) _

theorem densityGamma_pos (D : ℕ) (hD : 1 ≤ D) : 0 < densityGamma D := by
  have hα := densityAlpha_pos D hD
  have hδ := densityDelta_pos D
  unfold densityGamma
  positivity

theorem densityRate_pos (D : ℕ) (hD : 1 ≤ D) : 0 < densityRate D := by
  unfold densityRate
  exact div_pos (densityGamma_pos D hD) (by norm_num)

theorem equationBound_mul_densityAlpha (D : ℕ) (hD : 1 ≤ D) :
    equationBound D * densityAlpha D = 1 / 2 := by
  have hDr : (0 : ℝ) < D := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  unfold equationBound densityAlpha
  field_simp [hDr.ne']; ring

theorem density_error_budget (D : ℕ) (hD : 1 ≤ D) :
    2 * ((densityAlpha D + 2 * equationBound D) * densityGamma D) =
      densityDelta D := by
  have hα := densityAlpha_pos D hD
  have hden : densityAlpha D + 4 * (D : ℝ) ^ 3 ≠ 0 := by
    have hpos : 0 < densityAlpha D + 4 * (D : ℝ) ^ 3 := by positivity
    exact hpos.ne'
  unfold densityGamma equationBound
  field_simp [hden]; ring

theorem density_chunkCount_identity (D : ℕ) :
    (densityChunkCount D : ℝ) = 4 * (D : ℝ) / densityAlpha D + 1 := by
  simp only [densityChunkCount, densityAlpha, Nat.cast_add, Nat.cast_mul,
    Nat.cast_pow, Nat.cast_ofNat, one_div, div_inv_eq_mul]
  ring

theorem regularTailConstant_pos (D : ℕ) (hD : 1 ≤ D) (γ : ℝ) (hγ : 0 < γ) :
    0 < regularTailConstant D γ := by
  have hDr : (0 : ℝ) < D := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  unfold regularTailConstant equationBound
  positivity

end RyserCoveringCounterexample.Selection

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_KChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace RyserCoveringCounterexample.Selection

theorem tendsto_small_certificate_coefficient (A : ℝ) :
    Tendsto (fun K : ℕ => A * (K : ℝ) ^ 2 * (1 / 2 : ℝ) ^ (K - 3))
      atTop (𝓝 0) := by
  have hbase : Tendsto
      (fun K : ℕ => (8 * A) * ((K : ℝ) ^ 2 * (1 / 2 : ℝ) ^ K))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_const_mul_const_pow_of_lt_one 2
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul
        (8 * A)
  refine hbase.congr' ?_
  filter_upwards [eventually_ge_atTop (3 : ℕ)] with K hK
  have hpow : (1 / 2 : ℝ) ^ (K - 3) = 8 * (1 / 2 : ℝ) ^ K := by
    rw [pow_sub₀ (1 / 2 : ℝ) (by norm_num) hK]
    norm_num
    ring
  rw [hpow]
  ring

theorem tendsto_large_certificate_coefficient (B : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun K : ℕ => B * (K : ℝ) ^ 2 * Real.exp (2 - (K : ℝ) * δ))
      atTop (𝓝 0) := by
  have hbase : Tendsto
      (fun K : ℕ => (B * Real.exp 2) *
        ((K : ℝ) ^ 2 * Real.exp (-δ * (K : ℝ))))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_nat_pow_mul_exp_neg_mul 2 hδ).const_mul (B * Real.exp 2)
  refine hbase.congr' (Eventually.of_forall fun K : ℕ => ?_)
  change (B * Real.exp 2) * ((K : ℝ) ^ 2 * Real.exp (-δ * (K : ℝ))) =
    B * (K : ℝ) ^ 2 * Real.exp (2 - (K : ℝ) * δ)
  have hexponent : 2 - (K : ℝ) * δ = 2 + (-δ * (K : ℝ)) := by ring
  rw [hexponent, Real.exp_add]
  ring

theorem exists_pool_size (A B : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℕ, 6 ≤ K ∧
      A * (K : ℝ) ^ 2 * (1 / 2 : ℝ) ^ (K - 3) ≤ 1 / 2 ∧
      B * (K : ℝ) ^ 2 * Real.exp (2 - (K : ℝ) * δ) < 1 / 2 := by
  have hsmall : ∀ᶠ K : ℕ in atTop,
      A * (K : ℝ) ^ 2 * (1 / 2 : ℝ) ^ (K - 3) < 1 / 2 :=
    (tendsto_small_certificate_coefficient A).eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hlarge : ∀ᶠ K : ℕ in atTop,
      B * (K : ℝ) ^ 2 * Real.exp (2 - (K : ℝ) * δ) < 1 / 2 :=
    (tendsto_large_certificate_coefficient B hδ).eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hboth : ∀ᶠ K : ℕ in atTop, 6 ≤ K ∧
      A * (K : ℝ) ^ 2 * (1 / 2 : ℝ) ^ (K - 3) ≤ 1 / 2 ∧
      B * (K : ℝ) ^ 2 * Real.exp (2 - (K : ℝ) * δ) < 1 / 2 := by
    filter_upwards [eventually_ge_atTop (6 : ℕ), hsmall, hlarge] with K hK hs hl
    exact ⟨hK, hs.le, hl⟩
  exact hboth.exists

end RyserCoveringCounterexample.Selection

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_Parameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace RyserCoveringCounterexample.Selection

theorem equationBound_pos (D : ℕ) (hD : 1 ≤ D) : 0 < equationBound D := by
  have hDr : (0 : ℝ) < D := Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hD)
  unfold equationBound
  positivity

theorem selectionCutoff_pos (D : ℕ) (hD : 1 ≤ D) : 0 < selectionCutoff D := by
  unfold selectionCutoff
  exact div_pos zero_lt_one (mul_pos (by norm_num) (equationBound_pos D hD))

theorem selectionSmallFactor_pos (D : ℕ) (hD : 1 ≤ D) :
    0 < selectionSmallFactor D := by
  have hC := equationBound_pos D hD
  have hDr : (0 : ℝ) < D := Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hD)
  unfold selectionSmallFactor
  positivity

theorem selectionLargeFactor_pos (D : ℕ) (hD : 1 ≤ D) :
    0 < selectionLargeFactor D := by
  have hc := selectionCutoff_pos D hD
  have hDr : (0 : ℝ) < D := Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hD)
  unfold selectionLargeFactor
  positivity

theorem selectionSmallCoefficient_nonneg (D K : ℕ) (hD : 1 ≤ D) :
    0 ≤ selectionSmallCoefficient D K :=
  mul_nonneg (selectionSmallFactor_pos D hD).le (sq_nonneg _)

theorem selectionLargeCoefficient_nonneg (D K : ℕ) (hD : 1 ≤ D) :
    0 ≤ selectionLargeCoefficient D K :=
  mul_nonneg (selectionLargeFactor_pos D hD).le (sq_nonneg _)

theorem exists_selection_pool_size (D : ℕ) :
    ∃ K : ℕ, 6 ≤ K ∧
      selectionSmallCoefficient D K * (1 / 2 : ℝ) ^ (K - 3) ≤ 1 / 2 ∧
      selectionLargeCoefficient D K * Real.exp (2 - (K : ℝ) * densityDelta D) < 1 / 2 :=
  exists_pool_size (selectionSmallFactor D) (selectionLargeFactor D) (densityDelta_pos D)

end RyserCoveringCounterexample.Selection

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_SmallRange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Selection

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n K : ℕ}

theorem prob_noFeasibleOutside_small_le {D : ℕ} (data : Data F n)
    (hdata : Bounded D data) (I : Finset (Fin n)) (T : Finset (Position n K))
    (hT : T ⊆ targetPositions I K) (hcard : T.card ≤ 2 * I.card)
    (hsmall : (2 * (I.card : ℝ)) * ((2 * (D : ℝ) ^ 3) / (Fintype.card F : ℝ)) ≤ 1) :
    (poolLaw F n K).prob (NoFeasibleOutside data I T) ≤
      ((2 * (I.card : ℝ)) * ((2 * (D : ℝ) ^ 3) / (Fintype.card F : ℝ))) ^
        ((K - 2) * I.card) := by
  have hnonneg : 0 ≤ (2 * (D : ℝ) ^ 3) / (Fintype.card F : ℝ) :=
    div_nonneg (mul_nonneg (by norm_num) (pow_nonneg (Nat.cast_nonneg D) _))
      (Nat.cast_nonneg _)
  have hbase : (T.card : ℝ) * ((2 * (D : ℝ) ^ 3) / (Fintype.card F : ℝ)) ≤
      (2 * (I.card : ℝ)) * ((2 * (D : ℝ) ^ 3) / (Fintype.card F : ℝ)) := by
    apply mul_le_mul_of_nonneg_right _ hnonneg
    exact_mod_cast hcard
  have htarget_nonneg : 0 ≤
      (2 * (I.card : ℝ)) * ((2 * (D : ℝ) ^ 3) / (Fintype.card F : ℝ)) :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hnonneg
  calc
    _ ≤ ((T.card : ℝ) * ((2 * (D : ℝ) ^ 3) / (Fintype.card F : ℝ))) ^
        (freshTargets I T).card := prob_noFeasibleOutside_le data hdata I T
    _ ≤ ((2 * (I.card : ℝ)) * ((2 * (D : ℝ) ^ 3) / (Fintype.card F : ℝ))) ^
        (freshTargets I T).card :=
      pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hnonneg) hbase _
    _ ≤ _ := pow_le_pow_of_le_one htarget_nonneg hsmall
      (freshTargets_card_lower hT hcard)

end RyserCoveringCounterexample.Selection

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_ChunkConditioning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Selection

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n K : ℕ}

theorem joinAssignments_restrict_exposed (T : Finset (Position n K))
    (x : ExposedAssignment (F := F) T) (y : FreshAssignment (F := F) T) :
    (fun e : {e : Position n K // e ∈ T} => joinAssignments T x y e.val) = x := by
  funext e
  exact joinAssignments_exposed T x y e

theorem feasibleSet_frozenPool_restrict (data : Data F n)
    (T : Finset (Position n K)) (pool : Pool F n K) :
    feasibleSet data T
        (frozenPool T (fun e : {e : Position n K // e ∈ T} => pool e.val)) =
      feasibleSet data T pool := by
  funext i
  apply Finset.ext
  intro b
  rw [mem_feasibleSet, mem_feasibleSet]
  apply feasible_congr
  intro e he
  exact joinAssignments_exposed T (fun e => pool e.val) (fun _ => 0) ⟨e, he⟩

theorem prob_joinAssignments_eq_of_dependsOn_compl (T : Finset (Position n K))
    (Q : Pool F n K → Prop)
    (hQ : ∀ pool pool' : Pool F n K,
      (∀ e, e ∉ T → pool e = pool' e) → (Q pool ↔ Q pool'))
    (x : ExposedAssignment (F := F) T) :
    (FiniteLaw.uniform (FreshAssignment (F := F) T)).prob
        (fun y => Q (joinAssignments T x y)) =
      (poolLaw F n K).prob Q := by
  symm
  rw [poolLaw_prob_split T Q]
  calc
    _ = (FiniteLaw.uniform (ExposedAssignment (F := F) T)).expectation
        (fun _ => (FiniteLaw.uniform (FreshAssignment (F := F) T)).prob
          (fun y => Q (joinAssignments T x y))) := by
      apply congrArg (FiniteLaw.expectation
        (FiniteLaw.uniform (ExposedAssignment (F := F) T)))
      funext x'
      apply congrArg (FiniteLaw.prob
        (FiniteLaw.uniform (FreshAssignment (F := F) T)))
      funext y
      apply propext
      apply hQ
      intro e he
      exact (joinAssignments_fresh T x' y ⟨e, he⟩).trans
        (joinAssignments_fresh T x y ⟨e, he⟩).symm
    _ = _ := FiniteLaw.expectation_const _ _

theorem poolLaw_prob_adaptive_le (T : Finset (Position n K))
    (H : ExposedAssignment (F := F) T → Pool F n K → Prop) (b : ℝ)
    (hcongr : ∀ x : ExposedAssignment (F := F) T,
      ∀ pool pool' : Pool F n K,
      (∀ e, e ∉ T → pool e = pool' e) → (H x pool ↔ H x pool'))
    (hbound : ∀ x : ExposedAssignment (F := F) T,
      (poolLaw F n K).prob (H x) ≤ b) :
    (poolLaw F n K).prob
        (fun pool => H (fun e : {e : Position n K // e ∈ T} => pool e.val) pool) ≤ b := by
  apply poolLaw_prob_split_le T
  intro x
  calc
    _ = (FiniteLaw.uniform (FreshAssignment (F := F) T)).prob
        (fun y => H x (joinAssignments T x y)) := by
      apply congrArg (FiniteLaw.prob
        (FiniteLaw.uniform (FreshAssignment (F := F) T)))
      funext y
      rw [joinAssignments_restrict_exposed]
    _ = (poolLaw F n K).prob (H x) :=
      prob_joinAssignments_eq_of_dependsOn_compl T (H x) (hcongr x) x
    _ ≤ b := hbound x

end RyserCoveringCounterexample.Selection

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_ChunkPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Selection

variable {E : Type*} [DecidableEq E]

@[simp] theorem chunkRank_of_mem (T : Finset E) (e : E) (he : e ∈ T) :
    chunkRank T e = (T.equivFin ⟨e, he⟩).val := by
  simp only [chunkRank, dite_eq_left he]

theorem chunkRank_lt_card (T : Finset E) (e : E) (he : e ∈ T) :
    chunkRank T e < T.card := by
  rw [chunkRank_of_mem T e he]
  exact (T.equivFin ⟨e, he⟩).isLt

theorem chunkRank_injOn (T : Finset E) : Set.InjOn (chunkRank T) (T : Set E) := by
  intro a ha b hb hab
  have hval : (T.equivFin ⟨a, ha⟩).val = (T.equivFin ⟨b, hb⟩).val := by
    simpa only [chunkRank_of_mem T a ha, chunkRank_of_mem T b hb] using hab
  exact congrArg Subtype.val ((T.equivFin).injective (Fin.ext hval))

theorem candidateChunk_card_le (T : Finset E) (L j : ℕ) (hL : 0 < L) :
    (candidateChunk T L j).card ≤ L := by
  calc
    (candidateChunk T L j).card ≤ (Finset.range L).card := by
      apply Finset.card_le_card_of_injOn (fun e => chunkRank T e % L)
      · intro e _
        exact Finset.mem_range.mpr (Nat.mod_lt _ hL)
      · intro a ha b hb hab
        change chunkRank T a % L = chunkRank T b % L at hab
        obtain ⟨haT, haq⟩ := (mem_candidateChunk T L j a).mp ha
        obtain ⟨hbT, hbq⟩ := (mem_candidateChunk T L j b).mp hb
        apply chunkRank_injOn T haT hbT
        calc
          chunkRank T a = chunkRank T a % L + L * (chunkRank T a / L) :=
            (Nat.mod_add_div (chunkRank T a) L).symm
          _ = chunkRank T b % L + L * (chunkRank T b / L) := by
            rw [hab, haq, hbq]
          _ = chunkRank T b := Nat.mod_add_div (chunkRank T b) L
    _ = L := Finset.card_range L

theorem chunkPrefix_succ (T : Finset E) (L j : ℕ) :
    chunkPrefix T L (j + 1) = chunkPrefix T L j ∪ candidateChunk T L j := by
  ext e
  constructor
  · intro he
    obtain ⟨heT, hj⟩ := (mem_chunkPrefix T L (j + 1) e).mp he
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
    · exact Finset.mem_union.mpr (Or.inl ((mem_chunkPrefix T L j e).mpr ⟨heT, hlt⟩))
    · exact Finset.mem_union.mpr (Or.inr ((mem_candidateChunk T L j e).mpr ⟨heT, heq⟩))
  · intro he
    rcases Finset.mem_union.mp he with hp | hc
    · obtain ⟨heT, hlt⟩ := (mem_chunkPrefix T L j e).mp hp
      exact (mem_chunkPrefix T L (j + 1) e).mpr ⟨heT, Nat.lt_succ_of_lt hlt⟩
    · obtain ⟨heT, heq⟩ := (mem_candidateChunk T L j e).mp hc
      exact (mem_chunkPrefix T L (j + 1) e).mpr
        ⟨heT, Nat.lt_succ_iff_lt_or_eq.mpr (Or.inr heq)⟩

theorem disjoint_chunkPrefix_candidateChunk (T : Finset E) (L j : ℕ) :
    Disjoint (chunkPrefix T L j) (candidateChunk T L j) := by
  apply Finset.disjoint_left.mpr
  intro e hp hc
  have hlt := ((mem_chunkPrefix T L j e).mp hp).2
  have heq := ((mem_candidateChunk T L j e).mp hc).2
  exact (Nat.ne_of_lt hlt) heq

theorem chunkIndex_lt_count (T : Finset E) (L : ℕ) (e : E) (he : e ∈ T) :
    chunkRank T e / L < chunkCount T L := by
  exact Nat.lt_succ_of_le
    (Nat.div_le_div_right (Nat.le_of_lt (chunkRank_lt_card T e he)))

@[simp] theorem chunkPrefix_count (T : Finset E) (L : ℕ) :
    chunkPrefix T L (chunkCount T L) = T := by
  ext e
  constructor
  · exact fun he => ((mem_chunkPrefix T L (chunkCount T L) e).mp he).1
  · intro he
    exact (mem_chunkPrefix T L (chunkCount T L) e).mpr
      ⟨he, chunkIndex_lt_count T L e he⟩

end RyserCoveringCounterexample.Selection

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_ChunkDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section

namespace RyserCoveringCounterexample.Selection

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n K : ℕ}

theorem chunkFeasibleSet_congr (data : Data F n)
    (U : Fin n → Finset (Point F)) (E : Finset (Position n K))
    (pool pool' : Pool F n K) (h : ∀ e ∈ E, pool e = pool' e) :
    chunkFeasibleSet data U E pool = chunkFeasibleSet data U E pool' := by
  funext i
  ext b
  simp only [mem_chunkFeasibleSet]
  exact and_congr Iff.rfl (feasible_congr data E pool pool' h i b)

theorem frozenMass_feasibleSet_eq (data : Data F n) (I : Finset (Fin n))
    (T : Finset (Position n K)) (pool : Pool F n K) :
    frozenMass I (feasibleSet data T pool) = (feasibleMass data I T pool : ℝ) := by
  simp only [frozenMass, feasibleMass, Nat.cast_sum]

theorem prob_adaptive_chunk_recurrence_failure_le
    (D : ℕ) (hD : 1 ≤ D) (data : Data F n) (hdata : Bounded D data)
    (I : Finset (Fin n)) (P E : Finset (Position n K)) (hPE : Disjoint P E)
    (α γ : ℝ) (hm : 0 < (I.card : ℝ)) (hγ : 0 < γ)
    (hlarge : (Fintype.card F : ℝ) / (4 * equationBound D) < I.card)
    (hhalf : equationBound D * α = 1 / 2)
    (hsize : (E.card : ℝ) ≤ α * Fintype.card F)
    (hcutoff : (K : ℝ) * D * Real.sqrt (Fintype.card F) ≤ γ * Fintype.card F) :
    (poolLaw F n K).prob (fun pool =>
      frozenMass I (feasibleSet data (P ∪ E) pool) <
        frozenMass I (feasibleSet data P pool) / 2 -
          (α + 2 * equationBound D) * γ *
            ((I.card : ℝ) * (Fintype.card F : ℝ) ^ 2)) ≤
      (2 : ℝ) ^ E.card *
        (regularTailConstant D γ / Real.sqrt (Fintype.card F)) ^
          Nat.ceil (γ * Fintype.card F) := by
  classical
  let U : ExposedAssignment (F := F) P → Fin n → Finset (Point F) :=
    fun x => feasibleSet data P (frozenPool P x)
  let H : ExposedAssignment (F := F) P → Pool F n K → Prop := fun x pool =>
    frozenMass I (chunkFeasibleSet data (U x) E pool) < frozenMass I (U x) / 2 -
      (α + 2 * equationBound D) * γ * ((I.card : ℝ) * (Fintype.card F : ℝ) ^ 2)
  let b : ℝ := (2 : ℝ) ^ E.card *
    (regularTailConstant D γ / Real.sqrt (Fintype.card F)) ^
      Nat.ceil (γ * Fintype.card F)
  have hcongr : ∀ x : ExposedAssignment (F := F) P,
      ∀ pool pool' : Pool F n K,
      (∀ e, e ∉ P → pool e = pool' e) → (H x pool ↔ H x pool') := by
    intro x pool pool' hpool
    have heq : chunkFeasibleSet data (U x) E pool =
        chunkFeasibleSet data (U x) E pool' := by
      apply chunkFeasibleSet_congr
      intro e he
      exact hpool e (fun heP => Finset.disjoint_left.mp hPE heP he)
    dsimp only [H]
    rw [heq]
  have hbound : ∀ x : ExposedAssignment (F := F) P,
      (poolLaw F n K).prob (H x) ≤ b := by
    intro x
    exact prob_chunk_recurrence_failure_le D hD data hdata I (U x) E α γ
      hm hγ hlarge hhalf hsize hcutoff
  refine (FiniteLaw.prob_mono (poolLaw F n K) ?_).trans
    (poolLaw_prob_adaptive_le P H b hcongr hbound)
  intro pool hfailure
  dsimp only [H, U]
  rw [feasibleSet_frozenPool_restrict]
  have hsets : chunkFeasibleSet data (feasibleSet data P pool) E pool =
      feasibleSet data (P ∪ E) pool := by
    funext i
    exact chunkFeasibleSet_feasibleSet data P E pool i
  rw [hsets]
  exact hfailure

theorem prob_feasibleMass_lt_density_le
    (D : ℕ) (hD : 1 ≤ D) (data : Data F n) (hdata : Bounded D data)
    (I : Finset (Fin n)) (T : Finset (Position n K)) (L J0 : ℕ) (α γ : ℝ)
    (hm : 0 < (I.card : ℝ)) (hγ : 0 < γ)
    (hlarge : (Fintype.card F : ℝ) / (4 * equationBound D) < I.card)
    (hhalf : equationBound D * α = 1 / 2)
    (hL : 0 < L) (hLsize : (L : ℝ) ≤ α * Fintype.card F)
    (hcutoff : (K : ℝ) * D * Real.sqrt (Fintype.card F) ≤ γ * Fintype.card F)
    (hJ : chunkCount T L ≤ J0)
    (hbudget : 2 * ((α + 2 * equationBound D) * γ) ≤ (1 / 2 : ℝ) ^ (J0 + 1)) :
    (poolLaw F n K).prob (fun pool =>
      (feasibleMass data I T pool : ℝ) <
        (1 / 2 : ℝ) ^ (J0 + 1) * ((I.card : ℝ) * (Fintype.card F : ℝ) ^ 2)) ≤
      (chunkCount T L : ℝ) * (2 : ℝ) ^ L *
        (regularTailConstant D γ / Real.sqrt (Fintype.card F)) ^
          Nat.ceil (γ * Fintype.card F) := by
  classical
  let J := chunkCount T L
  let scale : ℝ := (I.card : ℝ) * (Fintype.card F : ℝ) ^ 2
  let err : ℝ := (α + 2 * equationBound D) * γ
  let mass : Pool F n K → ℕ → ℝ :=
    fun pool j => frozenMass I (feasibleSet data (chunkPrefix T L j) pool)
  let b : ℝ := (2 : ℝ) ^ L *
    (regularTailConstant D γ / Real.sqrt (Fintype.card F)) ^
      Nat.ceil (γ * Fintype.card F)
  have hscale : 0 ≤ scale := by dsimp only [scale]; positivity
  have hC : 0 ≤ equationBound D := by unfold equationBound; positivity
  have hα : 0 ≤ α := by
    by_contra hnot
    have hmul := mul_nonpos_of_nonneg_of_nonpos hC (le_of_lt (lt_of_not_ge hnot))
    rw [hhalf] at hmul
    norm_num at hmul
  have herr : 0 ≤ err :=
    mul_nonneg (add_nonneg hα (mul_nonneg (by norm_num) hC)) hγ.le
  have htail : 0 ≤ (regularTailConstant D γ / Real.sqrt (Fintype.card F)) ^
      Nat.ceil (γ * Fintype.card F) :=
    pow_nonneg (div_nonneg (regularTailConstant_nonneg D γ) (Real.sqrt_nonneg _)) _
  have hone (j : ℕ) :
      (poolLaw F n K).prob (fun pool =>
        mass pool (j + 1) < mass pool j / 2 - err * scale) ≤ b := by
    have hcard : (candidateChunk T L j).card ≤ L :=
      candidateChunk_card_le T L j hL
    have hsize : ((candidateChunk T L j).card : ℝ) ≤ α * Fintype.card F :=
      (Nat.cast_le.mpr hcard).trans hLsize
    have hchunk := prob_adaptive_chunk_recurrence_failure_le D hD data hdata I
      (chunkPrefix T L j) (candidateChunk T L j)
      (disjoint_chunkPrefix_candidateChunk T L j) α γ hm hγ hlarge hhalf hsize hcutoff
    have hbound : (2 : ℝ) ^ (candidateChunk T L j).card *
        (regularTailConstant D γ / Real.sqrt (Fintype.card F)) ^
          Nat.ceil (γ * Fintype.card F) ≤ b := by
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hcard) htail
    simpa only [mass, err, scale, chunkPrefix_succ] using hchunk.trans hbound
  have hstart (pool : Pool F n K) : scale ≤ mass pool 0 := by
    dsimp only [mass, scale]
    rw [chunkPrefix_zero]
    simp only [feasibleSet_empty, frozenMass, Finset.card_univ,
      card_point, Nat.cast_pow, Finset.sum_const, nsmul_eq_mul]; exact le_rfl
  have hterminal (pool : Pool F n K) :
      mass pool J = (feasibleMass data I T pool : ℝ) := by
    dsimp only [mass, J]
    rw [chunkPrefix_count, frozenMass_feasibleSet_eq]
  have hsubset (pool : Pool F n K)
      (hfailure : (feasibleMass data I T pool : ℝ) < (1 / 2 : ℝ) ^ (J0 + 1) * scale) :
      ∃ j ∈ Finset.range J, mass pool (j + 1) < mass pool j / 2 - err * scale := by
    by_contra hnone
    have hstep : ∀ j < J, mass pool j / 2 - err * scale ≤ mass pool (j + 1) := by
      intro j hj
      by_contra hbad
      exact hnone ⟨j, Finset.mem_range.mpr hj, lt_of_not_ge hbad⟩
    have hdensity := mass_after_chunks_ge_density (mass pool) scale err J J0
      hscale herr (hstart pool) hstep hJ hbudget
    rw [hterminal pool] at hdensity
    exact (not_lt_of_ge hdensity) hfailure
  calc
    _ ≤ (poolLaw F n K).prob (fun pool =>
        ∃ j ∈ Finset.range J, mass pool (j + 1) < mass pool j / 2 - err * scale) :=
      (poolLaw F n K).prob_mono hsubset
    _ ≤ ∑ j ∈ Finset.range J, (poolLaw F n K).prob
        (fun pool => mass pool (j + 1) < mass pool j / 2 - err * scale) :=
      prob_exists_mem_le _ _ _
    _ ≤ ∑ _j ∈ Finset.range J, b := Finset.sum_le_sum (fun j _ => hone j)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, J, b]; ring

end RyserCoveringCounterexample.Selection

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_ChunkPartitionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Selection

theorem floor_chunkSize_pos (α q : ℝ) (hlarge : 2 ≤ α * q) :
    0 < Nat.floor (α * q) := by
  apply Nat.floor_pos.mpr
  linarith

theorem floor_chunkSize_le (α q : ℝ) (hα : 0 < α) (hq : 0 < q) :
    (Nat.floor (α * q) : ℝ) ≤ α * q :=
  Nat.floor_le (mul_pos hα hq).le

theorem floor_chunkSize_ge_half (α q : ℝ) (hlarge : 2 ≤ α * q) :
    α * q / 2 ≤ (Nat.floor (α * q) : ℝ) := by
  have hfloor := Nat.lt_floor_add_one (α * q)
  linarith

variable {E : Type*} [instDecidableEqE : DecidableEq E]

theorem chunkCount_floor_le (T : Finset E) (α q D : ℝ)
    (hα : 0 < α) (hq : 0 < q) (hlarge : 2 ≤ α * q)
    (hT : (T.card : ℝ) ≤ 2 * D * q) (hD : 0 ≤ D) :
    (chunkCount T (Nat.floor (α * q)) : ℝ) ≤ 4 * D / α + 1 := let _ := instDecidableEqE; by
  have hfloorpos : 0 < (Nat.floor (α * q) : ℝ) :=
    Nat.cast_pos.mpr (floor_chunkSize_pos α q hlarge)
  have hhalfpos : 0 < α * q / 2 := div_pos (mul_pos hα hq) zero_lt_two
  have hnum : 0 ≤ 2 * D * q :=
    mul_nonneg (mul_nonneg (le_of_lt (zero_lt_two : (0 : ℝ) < 2)) hD) hq.le
  have hratio : (2 * D * q) / (α * q / 2) = 4 * D / α := by
    field_simp [ne_of_gt hα, ne_of_gt hq]
    ring
  calc
    (chunkCount T (Nat.floor (α * q)) : ℝ) =
        ((T.card / Nat.floor (α * q) : ℕ) : ℝ) + 1 := by
      simp only [chunkCount, Nat.cast_add, Nat.cast_one]
    _ ≤ (T.card : ℝ) / (Nat.floor (α * q) : ℝ) + 1 := by
      simpa only [add_comm] using
        (add_le_add_right
          (Nat.cast_div_le (α := ℝ) (m := T.card) (n := Nat.floor (α * q))) (1 : ℝ))
    _ ≤ (2 * D * q) / (Nat.floor (α * q) : ℝ) + 1 := by
      simpa only [add_comm] using
        (add_le_add_right (div_le_div_of_nonneg_right hT hfloorpos.le) (1 : ℝ))
    _ ≤ (2 * D * q) / (α * q / 2) + 1 := by
      simpa only [add_comm] using
        (add_le_add_right
          (div_le_div_of_nonneg_left hnum hhalfpos
            (floor_chunkSize_ge_half α q hlarge)) (1 : ℝ))
    _ = 4 * D / α + 1 := by rw [hratio]

end RyserCoveringCounterexample.Selection

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_ChunkTailAsymptotics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace RyserCoveringCounterexample.Selection

theorem chunk_tail_le_exp_of_log_bounds (α γ B q : ℝ)
    (hα : 0 ≤ α) (hB : 0 < B) (hq : 1 ≤ q)
    (hbase : Real.log B ≤ Real.log q / 2)
    (hbudget : (α + 1) * Real.log 2 + γ * Real.log B ≤ (γ / 4) * Real.log q) :
    (2 : ℝ) ^ Nat.ceil (α * q) * (B / Real.sqrt q) ^ Nat.ceil (γ * q) ≤
      Real.exp (-(γ / 4) * q * Real.log q) := by
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hspos : 0 < Real.sqrt q := Real.sqrt_pos.mpr hqpos
  have hratio : 0 < B / Real.sqrt q := div_pos hB hspos
  have hlogratio : Real.log (B / Real.sqrt q) = Real.log B - Real.log q / 2 := by
    rw [Real.log_div hB.ne' hspos.ne', Real.log_sqrt hqpos.le]
  have hlognonpos : Real.log (B / Real.sqrt q) ≤ 0 := by
    rw [hlogratio]
    linarith
  have hceilα : (Nat.ceil (α * q) : ℝ) ≤ (α + 1) * q := by
    calc
      (Nat.ceil (α * q) : ℝ) ≤ α * q + 1 :=
        (Nat.ceil_lt_add_one (mul_nonneg hα hqpos.le)).le
      _ ≤ (α + 1) * q := by nlinarith
  have hfirst : (Nat.ceil (α * q) : ℝ) * Real.log 2 ≤
      (α + 1) * q * Real.log 2 :=
    mul_le_mul_of_nonneg_right hceilα (Real.log_nonneg (by norm_num))
  have hsecond : (Nat.ceil (γ * q) : ℝ) * Real.log (B / Real.sqrt q) ≤
      γ * q * Real.log (B / Real.sqrt q) :=
    mul_le_mul_of_nonpos_right (Nat.le_ceil (γ * q)) hlognonpos
  have htwo : (2 : ℝ) ^ Nat.ceil (α * q) =
      Real.exp ((Nat.ceil (α * q) : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hpower : (B / Real.sqrt q) ^ Nat.ceil (γ * q) =
      Real.exp ((Nat.ceil (γ * q) : ℝ) * Real.log (B / Real.sqrt q)) := by
    rw [Real.exp_nat_mul, Real.exp_log hratio]
  rw [htwo, hpower, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  calc
    (Nat.ceil (α * q) : ℝ) * Real.log 2 +
        (Nat.ceil (γ * q) : ℝ) * Real.log (B / Real.sqrt q) ≤
        (α + 1) * q * Real.log 2 + γ * q * Real.log (B / Real.sqrt q) :=
      add_le_add hfirst hsecond
    _ = q * ((α + 1) * Real.log 2 + γ * Real.log B - (γ / 2) * Real.log q) := by
      rw [hlogratio]
      ring
    _ ≤ q * ((γ / 4) * Real.log q - (γ / 2) * Real.log q) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_right hbudget _) hqpos.le
    _ = -(γ / 4) * q * Real.log q := by ring

theorem exists_threshold_chunk_tail (α γ B : ℝ)
    (hα : 0 ≤ α) (hγ : 0 < γ) (hB : 0 < B) :
    ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q →
      (2 : ℝ) ^ Nat.ceil (α * (q : ℝ)) *
          (B / Real.sqrt (q : ℝ)) ^ Nat.ceil (γ * (q : ℝ)) ≤
        Real.exp (-(γ / 4) * (q : ℝ) * Real.log (q : ℝ)) := by
  have hlog : Tendsto (fun q : ℕ => Real.log (q : ℝ)) atTop atTop := by
    simpa only [Function.comp_def] using
      Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hhalf : Tendsto (fun q : ℕ => (1 / 2 : ℝ) * Real.log (q : ℝ)) atTop atTop :=
    hlog.const_mul_atTop (by norm_num)
  have hquarter : Tendsto (fun q : ℕ => (γ / 4) * Real.log (q : ℝ)) atTop atTop :=
    hlog.const_mul_atTop (div_pos hγ (by norm_num))
  have hev : ∀ᶠ q : ℕ in atTop,
      (2 : ℝ) ^ Nat.ceil (α * (q : ℝ)) *
          (B / Real.sqrt (q : ℝ)) ^ Nat.ceil (γ * (q : ℝ)) ≤
        Real.exp (-(γ / 4) * (q : ℝ) * Real.log (q : ℝ)) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ),
      hhalf.eventually_ge_atTop (Real.log B),
      hquarter.eventually_ge_atTop ((α + 1) * Real.log 2 + γ * Real.log B)]
      with q hq hbase hbudget
    have hqreal : (1 : ℝ) ≤ (q : ℝ) := by
      simpa only [Nat.cast_one] using (Nat.cast_le (α := ℝ)).mpr hq
    exact chunk_tail_le_exp_of_log_bounds α γ B (q : ℝ) hα hB hqreal
      (by linarith) hbudget
  exact eventually_atTop.1 hev

theorem exists_threshold_pool_budget (K D γ : ℝ) (hγ : 0 < γ) :
    ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q →
      K * D * Real.sqrt (q : ℝ) ≤ γ * (q : ℝ) := by
  have hs : Tendsto (fun q : ℕ => Real.sqrt (q : ℝ)) atTop atTop := by
    simpa only [Function.comp_def] using
      Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hr : Tendsto (fun q : ℕ => K * D / Real.sqrt (q : ℝ)) atTop (𝓝 0) :=
    hs.const_div_atTop (K * D)
  have hev : ∀ᶠ q : ℕ in atTop,
      K * D * Real.sqrt (q : ℝ) ≤ γ * (q : ℝ) := by
    filter_upwards [hr.eventually (gt_mem_nhds hγ), hs.eventually_ge_atTop 1]
      with q hq hs1
    have hspos : 0 < Real.sqrt (q : ℝ) := lt_of_lt_of_le zero_lt_one hs1
    have hKD : K * D ≤ γ * Real.sqrt (q : ℝ) :=
      (div_le_iff₀ hspos).mp hq.le
    calc
      K * D * Real.sqrt (q : ℝ) ≤
          (γ * Real.sqrt (q : ℝ)) * Real.sqrt (q : ℝ) :=
        mul_le_mul_of_nonneg_right hKD (Real.sqrt_nonneg _)
      _ = γ * (q : ℝ) := by
        rw [mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg q)]
  exact eventually_atTop.1 hev

theorem exists_threshold_chunk_tail_and_pool_budget (α γ B K D : ℝ)
    (hα : 0 ≤ α) (hγ : 0 < γ) (hB : 0 < B) :
    ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q →
      ((2 : ℝ) ^ Nat.ceil (α * (q : ℝ)) *
          (B / Real.sqrt (q : ℝ)) ^ Nat.ceil (γ * (q : ℝ)) ≤
        Real.exp (-(γ / 4) * (q : ℝ) * Real.log (q : ℝ))) ∧
      K * D * Real.sqrt (q : ℝ) ≤ γ * (q : ℝ) := by
  obtain ⟨Q₁, hQ₁⟩ := exists_threshold_chunk_tail α γ B hα hγ hB
  obtain ⟨Q₂, hQ₂⟩ := exists_threshold_pool_budget K D γ hγ
  refine ⟨max Q₁ Q₂, ?_⟩
  intro q hq
  exact ⟨hQ₁ q ((le_max_left _ _).trans hq), hQ₂ q ((le_max_right _ _).trans hq)⟩

theorem chunk_tail_le_exp_of_length_le (α γ B q : ℝ) (N : ℕ)
    (hB : 0 ≤ B) (hN : (N : ℝ) ≤ α * q)
    (hceil : (2 : ℝ) ^ Nat.ceil (α * q) *
      (B / Real.sqrt q) ^ Nat.ceil (γ * q) ≤ Real.exp (-(γ / 4) * q * Real.log q)) :
    (2 : ℝ) ^ N * (B / Real.sqrt q) ^ Nat.ceil (γ * q) ≤
      Real.exp (-(γ / 4) * q * Real.log q) := by
  have hN' : N ≤ Nat.ceil (α * q) :=
    (Nat.cast_le (α := ℝ)).mp (hN.trans (Nat.le_ceil (α * q)))
  have hpow : (2 : ℝ) ^ N ≤ (2 : ℝ) ^ Nat.ceil (α * q) :=
    pow_le_pow_right₀ (by norm_num) hN'
  exact (mul_le_mul_of_nonneg_right hpow
    (pow_nonneg (div_nonneg hB (Real.sqrt_nonneg q)) _)).trans hceil

end RyserCoveringCounterexample.Selection

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_UniformDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

namespace RyserCoveringCounterexample.Selection

theorem prob_feasibleMass_lt_densityDelta_le (D : ℕ) (hD : 1 ≤ D) (K : ℕ) :
    ∃ Q : ℕ, ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (n : ℕ) (data : Data F n), Bounded D data → Q ≤ Fintype.card F →
      ∀ (I : Finset (Fin n)) (T : Finset (Position n K)),
      (Fintype.card F : ℝ) / (4 * equationBound D) < I.card →
      T.card ≤ 2 * I.card →
      (poolLaw F n K).prob (fun pool =>
        (feasibleMass data I T pool : ℝ) <
          densityDelta D * ((I.card : ℝ) * (Fintype.card F : ℝ) ^ 2)) ≤
        (densityChunkCount D : ℝ) *
          Real.exp (-densityRate D * (Fintype.card F : ℝ) *
            Real.log (Fintype.card F : ℝ)) := by
  have hα := densityAlpha_pos D hD
  have hγ := densityGamma_pos D hD
  have hB := regularTailConstant_pos D hD (densityGamma D) hγ
  obtain ⟨Q₀, hQ₀⟩ := exists_threshold_chunk_tail_and_pool_budget
    (densityAlpha D) (densityGamma D) (regularTailConstant D (densityGamma D))
    (K : ℝ) (D : ℝ) hα.le hγ hB
  refine ⟨max Q₀ (Nat.ceil (2 / densityAlpha D)), ?_⟩
  intro F _ _ _ n data hdata hq I T hlarge hT
  have hqpos : (0 : ℝ) < Fintype.card F := Nat.cast_pos.mpr Fintype.card_pos
  have hqtail : Q₀ ≤ Fintype.card F := (le_max_left _ _).trans hq
  obtain ⟨htail, hpool⟩ := hQ₀ (Fintype.card F) hqtail
  have hqfloor : Nat.ceil (2 / densityAlpha D) ≤ Fintype.card F :=
    (le_max_right _ _).trans hq
  have hratio : 2 / densityAlpha D ≤ (Fintype.card F : ℝ) :=
    (Nat.le_ceil (2 / densityAlpha D)).trans (Nat.cast_le.mpr hqfloor)
  have hfloorlarge : 2 ≤ densityAlpha D * (Fintype.card F : ℝ) := by
    simpa only [mul_comm] using (div_le_iff₀ hα).mp hratio
  have hLpos : 0 < Nat.floor (densityAlpha D * (Fintype.card F : ℝ)) :=
    floor_chunkSize_pos (densityAlpha D) (Fintype.card F : ℝ) hfloorlarge
  have hLle : (Nat.floor (densityAlpha D * (Fintype.card F : ℝ)) : ℝ) ≤
      densityAlpha D * (Fintype.card F : ℝ) :=
    floor_chunkSize_le (densityAlpha D) (Fintype.card F : ℝ) hα hqpos
  have hIcard : I.card ≤ D * Fintype.card F := by
    have hIn : I.card ≤ n := by simpa only [Fintype.card_fin] using I.card_le_univ
    exact hIn.trans hdata.1
  have hTcard : T.card ≤ 2 * D * Fintype.card F := by
    calc
      T.card ≤ 2 * I.card := hT
      _ ≤ 2 * (D * Fintype.card F) := Nat.mul_le_mul_left 2 hIcard
      _ = _ := by ring
  have hTreal : (T.card : ℝ) ≤ 2 * (D : ℝ) * (Fintype.card F : ℝ) := by
    exact_mod_cast hTcard
  have hJreal := chunkCount_floor_le T (densityAlpha D) (Fintype.card F : ℝ)
    (D : ℝ) hα hqpos hfloorlarge hTreal (Nat.cast_nonneg D)
  rw [← density_chunkCount_identity D] at hJreal
  have hJ : chunkCount T (Nat.floor (densityAlpha D * (Fintype.card F : ℝ))) ≤
      densityChunkCount D := by exact_mod_cast hJreal
  have hC : 0 < equationBound D := by
    have hDr : (0 : ℝ) < D := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
    unfold equationBound
    positivity
  have hm : 0 < (I.card : ℝ) :=
    (div_pos hqpos (mul_pos (by norm_num) hC)).trans hlarge
  have hfinite := prob_feasibleMass_lt_density_le D hD data hdata I T
    (Nat.floor (densityAlpha D * (Fintype.card F : ℝ))) (densityChunkCount D)
    (densityAlpha D) (densityGamma D) hm hγ hlarge
    (equationBound_mul_densityAlpha D hD) hLpos hLle hpool hJ
    (density_error_budget D hD).le
  have hsmall := chunk_tail_le_exp_of_length_le
    (densityAlpha D) (densityGamma D) (regularTailConstant D (densityGamma D))
    (Fintype.card F : ℝ) (Nat.floor (densityAlpha D * (Fintype.card F : ℝ)))
    hB.le hLle htail
  have hcombined :
      (poolLaw F n K).prob (fun pool =>
        (feasibleMass data I T pool : ℝ) <
          densityDelta D * ((I.card : ℝ) * (Fintype.card F : ℝ) ^ 2)) ≤
      (chunkCount T (Nat.floor (densityAlpha D * (Fintype.card F : ℝ))) : ℝ) *
        Real.exp (-(densityGamma D / 4) * (Fintype.card F : ℝ) *
          Real.log (Fintype.card F : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_left hsmall
      (Nat.cast_nonneg (chunkCount T (Nat.floor (densityAlpha D * (Fintype.card F : ℝ)))))
    simpa only [densityDelta] using
      hfinite.trans (by simpa only [mul_assoc] using hmul)
  calc
    _ ≤ (chunkCount T (Nat.floor (densityAlpha D * (Fintype.card F : ℝ))) : ℝ) *
        Real.exp (-(densityGamma D / 4) * (Fintype.card F : ℝ) *
          Real.log (Fintype.card F : ℝ)) := hcombined
    _ ≤ (densityChunkCount D : ℝ) *
        Real.exp (-(densityGamma D / 4) * (Fintype.card F : ℝ) *
          Real.log (Fintype.card F : ℝ)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hJ) (Real.exp_pos _).le
    _ = _ := rfl

end RyserCoveringCounterexample.Selection

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_CertificateBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u
noncomputable section
namespace RyserCoveringCounterexample.Selection

theorem certificateEventBound_nonneg (D K q m : ℕ) :
    0 ≤ certificateEventBound D K q m := by
  unfold certificateEventBound smallCertificateBase densityFailureBound
  split_ifs <;> positivity

theorem smallCertificateBase_eq (D q m : ℕ) :
    smallCertificateBase D q m = 2 * equationBound D * (m : ℝ) / (q : ℝ) := by
  unfold smallCertificateBase equationBound
  ring

theorem smallCertificateBase_le_half (D q m : ℕ) (hD : 1 ≤ D) (hq : 0 < q)
    (hsmall : (m : ℝ) ≤ selectionCutoff D * (q : ℝ)) :
    smallCertificateBase D q m ≤ 1 / 2 := by
  have hC := equationBound_pos D hD
  have hqr : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hfactor : 0 ≤ 2 * equationBound D / (q : ℝ) :=
    div_nonneg (mul_nonneg (by norm_num) hC.le) hqr.le
  have hscaled := mul_le_mul_of_nonneg_left hsmall hfactor
  have hhalf : (2 * equationBound D / (q : ℝ)) *
      (selectionCutoff D * (q : ℝ)) = 1 / 2 := by
    unfold selectionCutoff
    field_simp [hC.ne', hqr.ne']; ring
  rw [hhalf] at hscaled
  rw [smallCertificateBase_eq]
  calc
    _ = (2 * equationBound D / (q : ℝ)) * (m : ℝ) := by ring
    _ ≤ 1 / 2 := hscaled

theorem exists_threshold_certificate_event_bound (D : ℕ) (hD : 1 ≤ D) (K : ℕ) :
    ∃ Q : ℕ, ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (n : ℕ) (data : Data F n), Bounded D data → Q ≤ Fintype.card F →
      ∀ (I : Finset (Fin n)) (T : Finset (Position n K)),
      T ⊆ targetPositions I K → T.card ≤ 2 * I.card →
      (poolLaw F n K).prob (NoFeasibleOutside data I T) ≤
        certificateEventBound D K (Fintype.card F) I.card := by
  obtain ⟨Q, hQ⟩ := prob_feasibleMass_lt_densityDelta_le.{u} D hD K
  refine ⟨Q, ?_⟩
  intro F _ _ _ n data hdata hq I T hT hcard
  unfold certificateEventBound
  by_cases hsmall : (I.card : ℝ) ≤ selectionCutoff D * (Fintype.card F : ℝ)
  · rw [ite_eq_left hsmall]
    have hbase := smallCertificateBase_le_half D (Fintype.card F) I.card hD
      Fintype.card_pos hsmall
    exact prob_noFeasibleOutside_small_le data hdata I T hT hcard
      (hbase.trans (by norm_num))
  · rw [ite_eq_right hsmall]
    have hlarge : (Fintype.card F : ℝ) / (4 * equationBound D) < I.card := by
      calc
        _ = selectionCutoff D * (Fintype.card F : ℝ) := by
          unfold selectionCutoff
          ring
        _ < I.card := lt_of_not_ge hsmall
    have hdensity := hQ F n data hdata hq I T hlarge hcard
    have hdensity' :
        (poolLaw F n K).prob (fun pool => (feasibleMass data I T pool : ℝ) <
          densityDelta D * (I.card : ℝ) * (Fintype.card F : ℝ) ^ 2) ≤
        densityFailureBound D (Fintype.card F) := by
      simpa only [densityFailureBound, mul_assoc] using hdensity
    exact (prob_noFeasibleOutside_le_density_bad_add_exp data I T (densityDelta D)
      hT hcard).trans (add_le_add hdensity' le_rfl)

end RyserCoveringCounterexample.Selection

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_CertificateCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Selection

open scoped BigOperators

variable {α : Type*} [instDecidableEqα : DecidableEq α]

theorem sum_powerset_pow_card_le_exp (S : Finset α) (x : ℝ) (hx : 0 ≤ x) :
    (∑ T ∈ S.powerset, x ^ T.card) ≤ Real.exp ((S.card : ℝ) * x) := let _ := instDecidableEqα; by
  calc
    (∑ T ∈ S.powerset, x ^ T.card) = ∏ _a ∈ S, (1 + x) := by
      simpa only [Finset.prod_const] using
        (Finset.prod_one_add (f := fun _ : α => x) S).symm
    _ ≤ Real.exp (∑ _a ∈ S, x) :=
      Real.prod_one_add_le_exp_sum S (fun _ => hx)
    _ = Real.exp ((S.card : ℝ) * x) := by simp

theorem card_small_subsets_mul_pow_le_exp (S : Finset α) (r : ℕ)
    (x : ℝ) (hx : 0 ≤ x) (hx_one : x ≤ 1) :
    (((S.powerset.filter (fun T => T.card ≤ r)).card : ℝ) * x ^ r) ≤
      Real.exp ((S.card : ℝ) * x) := by
  calc
    (((S.powerset.filter (fun T => T.card ≤ r)).card : ℝ) * x ^ r) =
        ∑ _T ∈ S.powerset.filter (fun T => T.card ≤ r), x ^ r := by simp
    _ ≤ ∑ T ∈ S.powerset.filter (fun T => T.card ≤ r), x ^ T.card := by
      apply Finset.sum_le_sum
      intro T hT
      exact pow_le_pow_of_le_one hx hx_one (Finset.mem_filter.mp hT).2
    _ ≤ ∑ T ∈ S.powerset, x ^ T.card :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun T _ _ => pow_nonneg hx T.card)
    _ ≤ Real.exp ((S.card : ℝ) * x) := sum_powerset_pow_card_le_exp S x hx

theorem card_fixed_subsets_mul_pow_le_exp (S : Finset α) (m : ℕ)
    (x : ℝ) (hx : 0 ≤ x) :
    (((S.powerset.filter (fun T => T.card = m)).card : ℝ) * x ^ m) ≤
      Real.exp ((S.card : ℝ) * x) := by
  calc
    (((S.powerset.filter (fun T => T.card = m)).card : ℝ) * x ^ m) =
        ∑ _T ∈ S.powerset.filter (fun T => T.card = m), x ^ m := by simp
    _ = ∑ T ∈ S.powerset.filter (fun T => T.card = m), x ^ T.card := by
      apply Finset.sum_congr rfl
      intro T hT
      rw [(Finset.mem_filter.mp hT).2]
    _ ≤ ∑ T ∈ S.powerset, x ^ T.card :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun T _ _ => pow_nonneg hx T.card)
    _ ≤ Real.exp ((S.card : ℝ) * x) := sum_powerset_pow_card_le_exp S x hx

theorem card_small_subsets_le (S : Finset α) (K m : ℕ)
    (hK : 1 ≤ K) (hcard : S.card = K * m) :
    ((S.powerset.filter (fun T => T.card ≤ 2 * m)).card : ℝ) ≤
      (3 * (K : ℝ) ^ 2) ^ m := by
  have hKr : (1 : ℝ) ≤ (K : ℝ) := by exact Nat.one_le_cast.mpr hK
  have hKpos : (0 : ℝ) < (K : ℝ) := lt_of_lt_of_le zero_lt_one hKr
  have hKne : (K : ℝ) ≠ 0 := ne_of_gt hKpos
  have he_three : Real.exp 1 ≤ (3 : ℝ) := by
    have h := Real.exp_le_two_add_div_two_sub (x := (1 : ℝ)) zero_le_one one_lt_two
    norm_num at h
    exact h
  have hweight := card_small_subsets_mul_pow_le_exp S (2 * m) (K : ℝ)⁻¹
    (inv_nonneg.mpr hKpos.le) (inv_le_one_of_one_le₀ hKr)
  have hexponent : (S.card : ℝ) * (K : ℝ)⁻¹ = (m : ℝ) := by
    rw [hcard, Nat.cast_mul]
    field_simp [hKne]
  have hexp : Real.exp (m : ℝ) = Real.exp 1 ^ m := by
    simpa only [mul_one] using Real.exp_nat_mul (1 : ℝ) m
  have hcancel :
      (3 * (K : ℝ) ^ 2) ^ m * ((K : ℝ)⁻¹) ^ (2 * m) = (3 : ℝ) ^ m := by
    rw [pow_mul, ← mul_pow]
    congr 1
    rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hKne, one_pow, mul_one]
  apply (mul_le_mul_iff_left₀ (pow_pos (inv_pos.mpr hKpos) (2 * m))).mp
  calc
    ((S.powerset.filter (fun T => T.card ≤ 2 * m)).card : ℝ) *
        ((K : ℝ)⁻¹) ^ (2 * m) ≤ Real.exp (m : ℝ) := by
      simpa only [hexponent] using hweight
    _ = Real.exp 1 ^ m := hexp
    _ ≤ (3 : ℝ) ^ m :=
      pow_le_pow_left₀ (Real.exp_pos 1).le he_three m
    _ = (3 * (K : ℝ) ^ 2) ^ m * ((K : ℝ)⁻¹) ^ (2 * m) := hcancel.symm

theorem card_fixed_subsets_le (S : Finset α) (m : ℕ) :
    ((S.powerset.filter (fun T => T.card = m)).card : ℝ) ≤
      (Real.exp 1 * (S.card : ℝ) / (m : ℝ)) ^ m := by
  by_cases hm : m = 0
  · subst m
    have hempty : S.powerset.filter (fun T => T.card = 0) = {∅} := by
      ext T
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.card_eq_zero,
        Finset.mem_singleton]
      constructor
      · exact And.right
      · intro hT
        subst T
        exact ⟨Finset.empty_subset S, rfl⟩
    rw [hempty]
    simp
  by_cases hS : S.card = 0
  · have hSempty : S = ∅ := Finset.card_eq_zero.mp hS
    subst S
    simp [hm, Ne.symm hm]
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
  have hSpos : (0 : ℝ) < (S.card : ℝ) := by exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hS)
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  have hSne : (S.card : ℝ) ≠ 0 := ne_of_gt hSpos
  have hxpos : (0 : ℝ) < (m : ℝ) / (S.card : ℝ) := div_pos hmpos hSpos
  have hweight := card_fixed_subsets_mul_pow_le_exp S m
    ((m : ℝ) / (S.card : ℝ)) hxpos.le
  have hexponent :
      (S.card : ℝ) * ((m : ℝ) / (S.card : ℝ)) = (m : ℝ) := by
    field_simp [hmne, hSne]
  have hexp : Real.exp (m : ℝ) = Real.exp 1 ^ m := by
    simpa only [mul_one] using Real.exp_nat_mul (1 : ℝ) m
  have hcancel :
      (Real.exp 1 * (S.card : ℝ) / (m : ℝ)) ^ m *
          ((m : ℝ) / (S.card : ℝ)) ^ m = Real.exp 1 ^ m := by
    rw [← mul_pow]
    congr 1
    field_simp [hmne, hSne]
  apply (mul_le_mul_iff_left₀ (pow_pos hxpos m)).mp
  calc
    ((S.powerset.filter (fun T => T.card = m)).card : ℝ) *
        ((m : ℝ) / (S.card : ℝ)) ^ m ≤ Real.exp (m : ℝ) := by
      simpa only [hexponent] using hweight
    _ = Real.exp 1 ^ m := hexp
    _ = (Real.exp 1 * (S.card : ℝ) / (m : ℝ)) ^ m *
        ((m : ℝ) / (S.card : ℝ)) ^ m := hcancel.symm

end RyserCoveringCounterexample.Selection

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_PoolGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Selection

variable {F : Type*} [Field F] [DecidableEq F] {n K : ℕ}

theorem compatibleChoice_of_transversal (data : Data F n) (pool : Pool F n K)
    {U : Finset (Position n K)}
    (hU : IsTransversalOn (candidateGraph data pool) Prod.fst Finset.univ U) :
    HasCompatibleChoice data pool := by
  classical
  have hex (i : Fin n) : ∃ k : Fin K, (i, k) ∈ U := by
    have hi : i ∈ U.image Prod.fst := by
      rw [hU.2.2]
      exact Finset.mem_univ i
    obtain ⟨⟨j, k⟩, hjk, hji⟩ := Finset.mem_image.mp hi
    change j = i at hji
    subst j
    exact ⟨k, hjk⟩
  let choice : Fin n → Fin K := fun i => Classical.choose (hex i)
  have hchoice (i : Fin n) : (i, choice i) ∈ U := Classical.choose_spec (hex i)
  refine ⟨choice, ?_⟩
  intro i j hij hconflict
  exact hU.1 (i, choice i) (hchoice i) (j, choice j) (hchoice j)
    ⟨hij, hconflict⟩

theorem transversal_of_compatibleChoice (data : Data F n) (pool : Pool F n K)
    (h : HasCompatibleChoice data pool) :
    ∃ U : Finset (Position n K),
      IsTransversalOn (candidateGraph data pool) Prod.fst Finset.univ U := by
  classical
  obtain ⟨choice, hchoice⟩ := h
  refine ⟨Finset.univ.image (fun i : Fin n => (i, choice i)), ?_, ?_, ?_⟩
  · intro e he f hf hadj
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hf
    exact hchoice i j hadj.1 hadj.2
  · intro e he f hf hfst
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hf
    change i = j at hfst
    subst j
    rfl
  · apply Finset.eq_univ_iff_forall.mpr
    intro i
    exact Finset.mem_image.mpr ⟨(i, choice i),
      Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, rfl⟩

theorem transversal_iff_hasCompatibleChoice (data : Data F n) (pool : Pool F n K) :
    (∃ U : Finset (Position n K),
      IsTransversalOn (candidateGraph data pool) Prod.fst Finset.univ U) ↔
        HasCompatibleChoice data pool := by
  constructor
  · rintro ⟨U, hU⟩
    exact compatibleChoice_of_transversal data pool hU
  · exact transversal_of_compatibleChoice data pool

theorem position_fst_surjective (hK : 0 < K) :
    Function.Surjective (Prod.fst : Position n K → Fin n) :=
  fun i => ⟨(i, ⟨0, hK⟩), rfl⟩

theorem not_hasCompatibleChoice_domination (data : Data F n) (pool : Pool F n K)
    (hK : 0 < K) (hbad : ¬ HasCompatibleChoice data pool) :
    ∃ I : Finset (Fin n), ∃ T : Finset (Position n K), I.Nonempty ∧
      T ⊆ Finset.univ.filter (fun e => e.1 ∈ I) ∧
      T.card ≤ 2 * (I.card - 1) ∧
      DominatesOn (candidateGraph data pool) Prod.fst I T := by
  apply domination_of_no_transversal (candidateGraph data pool) Prod.fst
    (position_fst_surjective hK)
  intro htransversal
  exact hbad ((transversal_iff_hasCompatibleChoice data pool).mp htransversal)

theorem not_feasible_of_dominates (data : Data F n) (pool : Pool F n K)
    {I : Finset (Fin n)} {T : Finset (Position n K)}
    (hdom : DominatesOn (candidateGraph data pool) Prod.fst I T)
    {e : Position n K} (he : e.1 ∈ I) (heT : e ∉ T) :
    ¬ Feasible data T pool e.1 (pool e) := by
  intro hfeasible
  obtain ⟨f, hf, hadj⟩ := hdom e he heT
  exact hfeasible f hf hadj.2

theorem not_hasCompatibleChoice_obstruction (data : Data F n) (pool : Pool F n K)
    (hK : 0 < K) (hbad : ¬ HasCompatibleChoice data pool) :
    ∃ I : Finset (Fin n), ∃ T : Finset (Position n K), I.Nonempty ∧
      T ⊆ Finset.univ.filter (fun e => e.1 ∈ I) ∧
      T.card ≤ 2 * I.card ∧
      ∀ e : Position n K, e.1 ∈ I → e ∉ T →
        ¬ Feasible data T pool e.1 (pool e) := by
  obtain ⟨I, T, hI, hT, hcard, hdom⟩ :=
    not_hasCompatibleChoice_domination data pool hK hbad
  refine ⟨I, T, hI, hT, ?_, ?_⟩
  · exact hcard.trans (Nat.mul_le_mul_left 2 (Nat.sub_le I.card 1))
  · intro e he heT
    exact not_feasible_of_dominates data pool hdom he heT

end RyserCoveringCounterexample.Selection

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_CertificateUnion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace RyserCoveringCounterexample.Selection

variable {F : Type*} [Field F] [instFintypeF : Fintype F] [DecidableEq F] {n K : ℕ}

theorem not_hasCompatibleChoice_mem_certificate_union (data : Data F n)
    (pool : Pool F n K) (hK : 0 < K) (hbad : ¬HasCompatibleChoice data pool) :
    ∃ I ∈ (Finset.univ : Finset (Fin n)).powerset.filter Finset.Nonempty,
      ∃ T ∈ (targetPositions I K).powerset.filter (fun T => T.card ≤ 2 * I.card),
        NoFeasibleOutside data I T pool := let _ := instFintypeF; by
  classical
  obtain ⟨I, T, hI, hT, hcard, hnone⟩ :=
    not_hasCompatibleChoice_obstruction data pool hK hbad
  have hTtarget : T ⊆ targetPositions I K := by
    simpa only [targetPositions_eq_filter] using hT
  refine ⟨I, Finset.mem_filter.mpr ⟨?_, hI⟩, T, ?_, hnone⟩
  · exact Finset.mem_powerset.mpr (Finset.subset_univ I)
  · exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hTtarget, hcard⟩

theorem sum_certificate_probs_le (data : Data F n) (I : Finset (Fin n))
    (hK : 1 ≤ K) (b : ℝ) (hb : 0 ≤ b)
    (hbound : ∀ T : Finset (Position n K), T ⊆ targetPositions I K →
      T.card ≤ 2 * I.card → (poolLaw F n K).prob (NoFeasibleOutside data I T) ≤ b) :
    (∑ T ∈ (targetPositions I K).powerset.filter (fun T => T.card ≤ 2 * I.card),
      (poolLaw F n K).prob (NoFeasibleOutside data I T)) ≤
        (3 * (K : ℝ) ^ 2) ^ I.card * b := by
  classical
  calc
    _ ≤ ∑ _T ∈ (targetPositions I K).powerset.filter (fun T => T.card ≤ 2 * I.card),
        b := by
      apply Finset.sum_le_sum
      intro T hT
      exact hbound T (Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1)
        (Finset.mem_filter.mp hT).2
    _ = (((targetPositions I K).powerset.filter
        (fun T => T.card ≤ 2 * I.card)).card : ℝ) * b := by simp
    _ ≤ (3 * (K : ℝ) ^ 2) ^ I.card * b := by
      apply mul_le_mul_of_nonneg_right _ hb
      apply card_small_subsets_le (targetPositions I K) K I.card hK
      simp [Nat.mul_comm, card_targetPositions I K]

theorem sum_certificate_probs_card_eq_le (data : Data F n) (m : ℕ)
    (hK : 1 ≤ K) (b : ℝ) (hb : 0 ≤ b)
    (hbound : ∀ I : Finset (Fin n), I.card = m →
      ∀ T : Finset (Position n K), T ⊆ targetPositions I K →
        T.card ≤ 2 * I.card →
          (poolLaw F n K).prob (NoFeasibleOutside data I T) ≤ b) :
    (∑ I ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun I => I.card = m),
      ∑ T ∈ (targetPositions I K).powerset.filter (fun T => T.card ≤ 2 * I.card),
        (poolLaw F n K).prob (NoFeasibleOutside data I T)) ≤
      ((Real.exp 1 * (n : ℝ) / (m : ℝ)) ^ m * (3 * (K : ℝ) ^ 2) ^ m) * b := by
  classical
  have hcount :
      (((Finset.univ : Finset (Fin n)).powerset.filter
        (fun I => I.card = m)).card : ℝ) ≤
      (Real.exp 1 * (n : ℝ) / (m : ℝ)) ^ m := by
    simpa using card_fixed_subsets_le (Finset.univ : Finset (Fin n)) m
  have hfactor : 0 ≤ (3 * (K : ℝ) ^ 2) ^ m * b :=
    mul_nonneg (pow_nonneg (mul_nonneg (by norm_num) (sq_nonneg (K : ℝ))) m) hb
  calc
    _ ≤ ∑ _I ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun I => I.card = m),
        (3 * (K : ℝ) ^ 2) ^ m * b := by
      apply Finset.sum_le_sum
      intro I hI
      have hcard := (Finset.mem_filter.mp hI).2
      simpa only [hcard] using sum_certificate_probs_le data I hK b hb (hbound I hcard)
    _ = (((Finset.univ : Finset (Fin n)).powerset.filter
        (fun I => I.card = m)).card : ℝ) * ((3 * (K : ℝ) ^ 2) ^ m * b) := by simp
    _ ≤ (Real.exp 1 * (n : ℝ) / (m : ℝ)) ^ m *
        ((3 * (K : ℝ) ^ 2) ^ m * b) := mul_le_mul_of_nonneg_right hcount hfactor
    _ = ((Real.exp 1 * (n : ℝ) / (m : ℝ)) ^ m *
        (3 * (K : ℝ) ^ 2) ^ m) * b := (mul_assoc _ _ _).symm

theorem not_hasCompatibleChoice_mem_size_union (data : Data F n)
    (pool : Pool F n K) (hK : 0 < K) (hbad : ¬HasCompatibleChoice data pool) :
    ∃ m ∈ (Finset.range (n + 1)).filter (fun m => 0 < m),
      ∃ I ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun I => I.card = m),
        ∃ T ∈ (targetPositions I K).powerset.filter (fun T => T.card ≤ 2 * I.card),
          NoFeasibleOutside data I T pool := by
  classical
  obtain ⟨I, hI, T, hT, hnone⟩ :=
    not_hasCompatibleChoice_mem_certificate_union data pool hK hbad
  have hpos : 0 < I.card := Finset.card_pos.mpr (Finset.mem_filter.mp hI).2
  have hcard : I.card ≤ n := by
    simpa using Finset.card_le_card (Finset.subset_univ I)
  refine ⟨I.card, ?_, I, ?_, T, hT, hnone⟩
  · exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hcard), hpos⟩
  · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hI).1, rfl⟩

theorem prob_not_hasCompatibleChoice_le_grouped_certificate_sum
    (data : Data F n) (hK : 0 < K) :
    (poolLaw F n K).prob (fun pool => ¬HasCompatibleChoice data pool) ≤
      ∑ m ∈ (Finset.range (n + 1)).filter (fun m => 0 < m),
        ∑ I ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun I => I.card = m),
          ∑ T ∈ (targetPositions I K).powerset.filter (fun T => T.card ≤ 2 * I.card),
            (poolLaw F n K).prob (NoFeasibleOutside data I T) := by
  classical
  calc
    _ ≤ (poolLaw F n K).prob (fun pool =>
        ∃ m ∈ (Finset.range (n + 1)).filter (fun m => 0 < m),
          ∃ I ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun I => I.card = m),
            ∃ T ∈ (targetPositions I K).powerset.filter (fun T => T.card ≤ 2 * I.card),
              NoFeasibleOutside data I T pool) :=
      (poolLaw F n K).prob_mono
        (fun pool hbad => not_hasCompatibleChoice_mem_size_union data pool hK hbad)
    _ ≤ ∑ m ∈ (Finset.range (n + 1)).filter (fun m => 0 < m),
        (poolLaw F n K).prob (fun pool =>
          ∃ I ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun I => I.card = m),
            ∃ T ∈ (targetPositions I K).powerset.filter (fun T => T.card ≤ 2 * I.card),
              NoFeasibleOutside data I T pool) := prob_exists_mem_le _ _ _
    _ ≤ ∑ m ∈ (Finset.range (n + 1)).filter (fun m => 0 < m),
        ∑ I ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun I => I.card = m),
          (poolLaw F n K).prob (fun pool =>
            ∃ T ∈ (targetPositions I K).powerset.filter (fun T => T.card ≤ 2 * I.card),
              NoFeasibleOutside data I T pool) := by
      apply Finset.sum_le_sum
      intro m _
      exact prob_exists_mem_le _ _ _
    _ ≤ ∑ m ∈ (Finset.range (n + 1)).filter (fun m => 0 < m),
        ∑ I ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun I => I.card = m),
          ∑ T ∈ (targetPositions I K).powerset.filter (fun T => T.card ≤ 2 * I.card),
            (poolLaw F n K).prob (NoFeasibleOutside data I T) := by
      apply Finset.sum_le_sum
      intro m _
      apply Finset.sum_le_sum
      intro I _
      exact prob_exists_mem_le _ _ _

theorem prob_not_hasCompatibleChoice_le_size_sum
    (data : Data F n) (hK : 0 < K) (b : ℕ → ℝ) (hb : ∀ m, 0 ≤ b m)
    (hbound : ∀ I : Finset (Fin n), I.Nonempty →
      ∀ T : Finset (Position n K), T ⊆ targetPositions I K →
        T.card ≤ 2 * I.card →
          (poolLaw F n K).prob (NoFeasibleOutside data I T) ≤ b I.card) :
    (poolLaw F n K).prob (fun pool => ¬HasCompatibleChoice data pool) ≤
      ∑ m ∈ (Finset.range (n + 1)).filter (fun m => 0 < m),
        ((Real.exp 1 * (n : ℝ) / (m : ℝ)) ^ m * (3 * (K : ℝ) ^ 2) ^ m) * b m := by
  classical
  refine (prob_not_hasCompatibleChoice_le_grouped_certificate_sum data hK).trans ?_
  apply Finset.sum_le_sum
  intro m hm
  apply sum_certificate_probs_card_eq_le data m (Nat.succ_le_of_lt hK) (b m) (hb m)
  intro I hI T hT hcard
  have hnonempty : I.Nonempty := Finset.card_pos.mp (by
    rw [hI]
    exact (Finset.mem_filter.mp hm).2)
  simpa only [hI] using hbound I hnonempty T hT hcard

end RyserCoveringCounterexample.Selection

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_SmallSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace RyserCoveringCounterexample.Selection

theorem sum_half_pow_Ico_eq (a b : ℕ) (hab : a ≤ b) :
    (∑ m ∈ Finset.Ico a b, (1 / 2 : ℝ) ^ m) =
      2 * ((1 / 2 : ℝ) ^ a - (1 / 2 : ℝ) ^ b) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hab
  clear hab
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.add_succ,
        Nat.Ico_succ_right_eq_insert_Ico (Nat.le_add_right a n),
        Finset.sum_insert (by simp), ih, pow_succ]
      ring

theorem sum_half_pow_Ico_le (a b : ℕ) :
    (∑ m ∈ Finset.Ico a b, (1 / 2 : ℝ) ^ m) ≤ 2 * (1 / 2 : ℝ) ^ a := by
  by_cases hab : a ≤ b
  · rw [sum_half_pow_Ico_eq a b hab]
    have hnonneg : 0 ≤ (1 / 2 : ℝ) ^ b := pow_nonneg (by norm_num) b
    exact mul_le_mul_of_nonneg_left (sub_le_self _ hnonneg) (by norm_num)
  · rw [Finset.Ico_eq_empty_of_le (Nat.le_of_lt (Nat.lt_of_not_ge hab)), Finset.sum_empty]
    exact mul_nonneg (by norm_num) (pow_nonneg (by norm_num) a)

theorem sum_half_pow_le_cutoff (T : Finset ℕ) (R : ℕ)
    (hT : ∀ m ∈ T, R < m) :
    (∑ m ∈ T, (1 / 2 : ℝ) ^ m) ≤ (1 / 2 : ℝ) ^ R := by
  have hsub : T ⊆ Finset.Ico (R + 1) (T.sup id + 1) := by
    intro m hm
    exact Finset.mem_Ico.mpr ⟨Nat.succ_le_of_lt (hT m hm),
      Nat.lt_succ_of_le (show m ≤ T.sup id from Finset.le_sup (f := id) hm)⟩
  calc
    (∑ m ∈ T, (1 / 2 : ℝ) ^ m) ≤
        ∑ m ∈ Finset.Ico (R + 1) (T.sup id + 1), (1 / 2 : ℝ) ^ m :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun m _ _ => pow_nonneg (by norm_num) m)
    _ ≤ 2 * (1 / 2 : ℝ) ^ (R + 1) := sum_half_pow_Ico_le _ _
    _ = (1 / 2 : ℝ) ^ R := by
      rw [pow_succ]
      ring

theorem sum_indexed_powers_le_cutoff (T : Finset ℕ) (R : ℕ)
    (f : ℕ → ℝ) (u : ℝ) (hu : 0 ≤ u)
    (hpositive : ∀ m ∈ T, 1 ≤ m)
    (hf0 : ∀ m ∈ T, 0 ≤ f m)
    (hfhalf : ∀ m ∈ T, f m ≤ 1 / 2)
    (hcutoff : ∀ m ∈ T, m ≤ R → f m ≤ u) :
    (∑ m ∈ T, (f m) ^ m) ≤ (R : ℝ) * u + (1 / 2 : ℝ) ^ R := by
  have hsub : T.filter (fun m => m ≤ R) ⊆ Finset.Icc 1 R := by
    intro m hm
    obtain ⟨hmT, hmR⟩ := Finset.mem_filter.mp hm
    exact Finset.mem_Icc.mpr ⟨hpositive m hmT, hmR⟩
  have hcard : (T.filter (fun m => m ≤ R)).card ≤ R := by
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using Finset.card_le_card hsub
  have hinitial : (∑ m ∈ T.filter (fun m => m ≤ R), (f m) ^ m) ≤ (R : ℝ) * u := by
    calc
      _ ≤ ∑ m ∈ T.filter (fun m => m ≤ R), u := by
        apply Finset.sum_le_sum
        intro m hm
        obtain ⟨hmT, hmR⟩ := Finset.mem_filter.mp hm
        have hmpos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one (hpositive m hmT)
        have hfone : f m ≤ 1 := (hfhalf m hmT).trans (by norm_num)
        exact (pow_le_of_le_one (hf0 m hmT) hfone hmpos.ne').trans
          (hcutoff m hmT hmR)
      _ = ((T.filter (fun m => m ≤ R)).card : ℝ) * u := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (R : ℝ) * u := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) hu
  have htail : (∑ m ∈ T.filter (fun m => ¬m ≤ R), (f m) ^ m) ≤
      (1 / 2 : ℝ) ^ R := by
    calc
      _ ≤ ∑ m ∈ T.filter (fun m => ¬m ≤ R), (1 / 2 : ℝ) ^ m := by
        apply Finset.sum_le_sum
        intro m hm
        have hmT := (Finset.mem_filter.mp hm).1
        exact pow_le_pow_left₀ (hf0 m hmT) (hfhalf m hmT) m
      _ ≤ (1 / 2 : ℝ) ^ R :=
        sum_half_pow_le_cutoff _ R (fun m hm =>
          Nat.lt_of_not_ge (Finset.mem_filter.mp hm).2)
  calc
    (∑ m ∈ T, (f m) ^ m) =
        (∑ m ∈ T.filter (fun m => m ≤ R), (f m) ^ m) +
          ∑ m ∈ T.filter (fun m => ¬m ≤ R), (f m) ^ m :=
      (Finset.sum_filter_add_sum_filter_not T (fun m => m ≤ R) (fun m => (f m) ^ m)).symm
    _ ≤ (R : ℝ) * u + (1 / 2 : ℝ) ^ R := add_le_add hinitial htail

theorem small_certificate_sum_le (T : Finset ℕ) (K R : ℕ) (A C q : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hq : 0 < q)
    (hpositive : ∀ m ∈ T, 1 ≤ m)
    (hrange : ∀ m ∈ T, 2 * C * (m : ℝ) / q ≤ 1 / 2)
    (hsmall : A * (1 / 2 : ℝ) ^ (K - 3) ≤ 1 / 2) :
    (∑ m ∈ T, (A * (2 * C * (m : ℝ) / q) ^ (K - 3)) ^ m) ≤
      (R : ℝ) * A * (2 * C * (R : ℝ) / q) ^ (K - 3) + (1 / 2 : ℝ) ^ R := by
  have hbase0 (m : ℕ) : 0 ≤ 2 * C * (m : ℝ) / q :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC) (Nat.cast_nonneg m)) hq.le
  have hnonneg (m : ℕ) : 0 ≤ A * (2 * C * (m : ℝ) / q) ^ (K - 3) :=
    mul_nonneg hA (pow_nonneg (hbase0 m) _)
  have hhalf (m : ℕ) (hm : m ∈ T) :
      A * (2 * C * (m : ℝ) / q) ^ (K - 3) ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (hbase0 m) (hrange m hm) (K - 3)) hA).trans hsmall
  have hcutoff (m : ℕ) (_hm : m ∈ T) (hmR : m ≤ R) :
      A * (2 * C * (m : ℝ) / q) ^ (K - 3) ≤
        A * (2 * C * (R : ℝ) / q) ^ (K - 3) := by
    apply mul_le_mul_of_nonneg_left _ hA
    apply pow_le_pow_left₀ (hbase0 m) _ (K - 3)
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hmR) (mul_nonneg (by norm_num) hC)) hq.le
  simpa only [mul_assoc] using
    sum_indexed_powers_le_cutoff T R
      (fun m : ℕ => A * (2 * C * (m : ℝ) / q) ^ (K - 3))
      (A * (2 * C * (R : ℝ) / q) ^ (K - 3))
      (hnonneg R) hpositive (fun m _ => hnonneg m) hhalf hcutoff

end RyserCoveringCounterexample.Selection

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_LayerBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace RyserCoveringCounterexample.Selection

theorem sum_powers_le_positive_index_bound (T : Finset ℕ) (N : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hpositive : ∀ m ∈ T, 1 ≤ m)
    (hsize : ∀ m ∈ T, m ≤ N) :
    (∑ m ∈ T, B ^ m) ≤ (N : ℝ) * (max 1 B) ^ N := by
  have hsub : T ⊆ Finset.Icc 1 N := by
    intro m hm
    exact Finset.mem_Icc.mpr ⟨hpositive m hm, hsize m hm⟩
  have hcard : T.card ≤ N := by
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using Finset.card_le_card hsub
  have hmax0 : (0 : ℝ) ≤ max 1 B := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  calc
    (∑ m ∈ T, B ^ m) ≤ ∑ _m ∈ T, (max 1 B) ^ N := by
      apply Finset.sum_le_sum
      intro m hm
      exact (pow_le_pow_left₀ hB (le_max_right 1 B) m).trans
        (pow_le_pow_right₀ (le_max_left 1 B) (hsize m hm))
    _ = (T.card : ℝ) * (max 1 B) ^ N := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) * (max 1 B) ^ N :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) (pow_nonneg hmax0 N)

theorem weighted_unused_error_eq_power (B δ : ℝ) (K m : ℕ) :
    B ^ m * Real.exp (-(((K : ℝ) * δ - 2) * (m : ℝ))) =
      (B * Real.exp (2 - (K : ℝ) * δ)) ^ m := by
  have hexponent : -(((K : ℝ) * δ - 2) * (m : ℝ)) =
      (m : ℝ) * (2 - (K : ℝ) * δ) := by ring
  rw [hexponent, Real.exp_nat_mul, mul_pow]

theorem large_layer_sum_le (T : Finset ℕ) (D K q : ℕ) (B J c c1 δ : ℝ)
    (hB : 0 ≤ B) (hJ : 0 ≤ J) (hc1 : 0 < c1)
    (hpositive : ∀ m ∈ T, 1 ≤ m)
    (hsize : ∀ m ∈ T, m ≤ D * q)
    (hlarge : ∀ m ∈ T, c1 * (q : ℝ) < (m : ℝ))
    (hratio : B * Real.exp (2 - (K : ℝ) * δ) ≤ 1 / 2) :
    (∑ m ∈ T, B ^ m *
      (J * Real.exp (-c * (q : ℝ) * Real.log (q : ℝ)) +
        Real.exp (-(((K : ℝ) * δ - 2) * (m : ℝ))))) ≤
      J * ((D : ℝ) * (q : ℝ)) * (max 1 B) ^ (D * q) *
        Real.exp (-c * (q : ℝ) * Real.log (q : ℝ)) +
          (1 / 2 : ℝ) ^ Nat.floor (c1 * (q : ℝ)) := by
  have hdensity :
      (∑ m ∈ T, B ^ m * (J * Real.exp (-c * (q : ℝ) * Real.log (q : ℝ)))) ≤
        J * ((D : ℝ) * (q : ℝ)) * (max 1 B) ^ (D * q) *
          Real.exp (-c * (q : ℝ) * Real.log (q : ℝ)) := by
    calc
      _ = (∑ m ∈ T, B ^ m) *
          (J * Real.exp (-c * (q : ℝ) * Real.log (q : ℝ))) := by
        rw [Finset.sum_mul]
      _ ≤ ((D * q : ℕ) : ℝ) * (max 1 B) ^ (D * q) *
          (J * Real.exp (-c * (q : ℝ) * Real.log (q : ℝ))) :=
        mul_le_mul_of_nonneg_right
          (sum_powers_le_positive_index_bound T (D * q) B hB hpositive hsize)
          (mul_nonneg hJ (Real.exp_pos _).le)
      _ = _ := by
        rw [Nat.cast_mul]
        ring
  have hratio0 : 0 ≤ B * Real.exp (2 - (K : ℝ) * δ) :=
    mul_nonneg hB (Real.exp_pos _).le
  have hunused :
      (∑ m ∈ T, B ^ m * Real.exp (-(((K : ℝ) * δ - 2) * (m : ℝ)))) ≤
        (1 / 2 : ℝ) ^ Nat.floor (c1 * (q : ℝ)) := by
    calc
      _ = ∑ m ∈ T, (B * Real.exp (2 - (K : ℝ) * δ)) ^ m := by
        apply Finset.sum_congr rfl
        intro m _
        exact weighted_unused_error_eq_power B δ K m
      _ ≤ ∑ m ∈ T, (1 / 2 : ℝ) ^ m :=
        Finset.sum_le_sum (fun m _ => pow_le_pow_left₀ hratio0 hratio m)
      _ ≤ (1 / 2 : ℝ) ^ Nat.floor (c1 * (q : ℝ)) := by
        apply sum_half_pow_le_cutoff
        intro m hm
        exact (Nat.floor_lt (mul_nonneg hc1.le (Nat.cast_nonneg q))).mpr (hlarge m hm)
  calc
    _ = (∑ m ∈ T, B ^ m * (J * Real.exp (-c * (q : ℝ) * Real.log (q : ℝ)))) +
        ∑ m ∈ T, B ^ m * Real.exp (-(((K : ℝ) * δ - 2) * (m : ℝ))) := by
      simp only [mul_add, Finset.sum_add_distrib]
    _ ≤ _ := add_le_add hdensity hunused

end RyserCoveringCounterexample.Selection

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_LayerNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Selection

theorem small_layer_coefficient_identity (m K : ℕ) (C D q : ℝ)
    (hm : 0 < m) (hK : 3 ≤ K) (hq : 0 < q) :
    (((Real.exp 1 * D * q / (m : ℝ)) ^ m * (3 * (K : ℝ) ^ 2) ^ m) *
        (2 * C * (m : ℝ) / q) ^ ((K - 2) * m)) =
      ((6 * C * Real.exp 1 * D * (K : ℝ) ^ 2) *
        (2 * C * (m : ℝ) / q) ^ (K - 3)) ^ m := by
  have hmreal : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hshift : K - 2 = (K - 3) + 1 := by omega
  have hcancel :
      ((Real.exp 1 * D * q / (m : ℝ)) * (3 * (K : ℝ) ^ 2)) *
          (2 * C * (m : ℝ) / q) =
        6 * C * Real.exp 1 * D * (K : ℝ) ^ 2 := by
    field_simp [hmreal.ne', hq.ne']
    ring
  have hbase :
      ((Real.exp 1 * D * q / (m : ℝ)) * (3 * (K : ℝ) ^ 2)) *
          (2 * C * (m : ℝ) / q) ^ (K - 2) =
        (6 * C * Real.exp 1 * D * (K : ℝ) ^ 2) *
          (2 * C * (m : ℝ) / q) ^ (K - 3) := by
    rw [hshift, pow_succ (2 * C * (m : ℝ) / q) (K - 3)]
    calc
      _ = (((Real.exp 1 * D * q / (m : ℝ)) * (3 * (K : ℝ) ^ 2)) *
            (2 * C * (m : ℝ) / q)) *
            (2 * C * (m : ℝ) / q) ^ (K - 3) := by ring
      _ = _ := by rw [hcancel]
  calc
    _ = (((Real.exp 1 * D * q / (m : ℝ)) * (3 * (K : ℝ) ^ 2)) *
          (2 * C * (m : ℝ) / q) ^ (K - 2)) ^ m := by
      simp only [mul_pow, pow_mul]
    _ = _ := by rw [hbase]

theorem large_layer_count_le (m K : ℕ) (D q c1 : ℝ)
    (hm : 0 < m) (hD : 0 ≤ D) (hq : 0 < q) (hc1 : 0 < c1)
    (hlarge : c1 * q < (m : ℝ)) :
    (Real.exp 1 * D * q / (m : ℝ)) ^ m * (3 * (K : ℝ) ^ 2) ^ m ≤
      ((Real.exp 1 * D / c1) * 3 * (K : ℝ) ^ 2) ^ m := by
  have hmreal : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hDexp : 0 ≤ Real.exp 1 * D := mul_nonneg (Real.exp_pos 1).le hD
  have hratio0 : 0 ≤ Real.exp 1 * D * q / (m : ℝ) :=
    div_nonneg (mul_nonneg hDexp hq.le) hmreal.le
  have hcutoff0 : 0 ≤ Real.exp 1 * D / c1 := div_nonneg hDexp hc1.le
  have hratio : Real.exp 1 * D * q / (m : ℝ) ≤ Real.exp 1 * D / c1 := by
    apply (div_le_iff₀ hmreal).mpr
    calc
      Real.exp 1 * D * q = (Real.exp 1 * D / c1) * (c1 * q) := by
        field_simp [hc1.ne']

      _ ≤ (Real.exp 1 * D / c1) * (m : ℝ) :=
        mul_le_mul_of_nonneg_left hlarge.le hcutoff0
  have hpool0 : 0 ≤ 3 * (K : ℝ) ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg _)
  have hcoefficient :
      (Real.exp 1 * D * q / (m : ℝ)) * (3 * (K : ℝ) ^ 2) ≤
        (Real.exp 1 * D / c1) * (3 * (K : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_right hratio hpool0
  calc
    _ = ((Real.exp 1 * D * q / (m : ℝ)) * (3 * (K : ℝ) ^ 2)) ^ m :=
      (mul_pow _ _ m).symm
    _ ≤ ((Real.exp 1 * D / c1) * (3 * (K : ℝ) ^ 2)) ^ m :=
      pow_le_pow_left₀ (mul_nonneg hratio0 hpool0) hcoefficient m
    _ = _ := by rw [mul_assoc]

end RyserCoveringCounterexample.Selection

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_NumericLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace RyserCoveringCounterexample.Selection

theorem tendsto_small_selection_term (K R : ℕ) (A C : ℝ) (hK : 3 < K) :
    Tendsto (fun q : ℕ => (R : ℝ) * A *
      (2 * C * (R : ℝ) / (q : ℝ)) ^ (K - 3)) atTop (𝓝 0) := by
  have hm : K - 3 ≠ 0 := (Nat.sub_pos_of_lt hK).ne'
  have hratio : Tendsto (fun q : ℕ => 2 * C * (R : ℝ) / (q : ℝ))
      atTop (𝓝 0) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_div_atTop (2 * C * (R : ℝ))
  simpa only [zero_pow hm, mul_zero] using
    (hratio.pow (K - 3)).const_mul ((R : ℝ) * A)

theorem tendsto_density_selection_term (D : ℕ) (J B c : ℝ)
    (hB : 0 < B) (hc : 0 < c) :
    Tendsto (fun q : ℕ => J * ((D : ℝ) * (q : ℝ)) * B ^ (D * q) *
      Real.exp (-c * (q : ℝ) * Real.log (q : ℝ))) atTop (𝓝 0) := by
  have hlimit : Tendsto (fun q : ℕ => (J * (D : ℝ)) * ((q : ℝ) *
      Real.exp (((D : ℝ) * Real.log B) * (q : ℝ) -
        c * (q : ℝ) * Real.log (q : ℝ)))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_nat_mul_exp_linear_sub_mul_log hc ((D : ℝ) * Real.log B)).const_mul
        (J * (D : ℝ))
  apply hlimit.congr
  intro q
  have hpow : B ^ (D * q) = Real.exp ((D : ℝ) * (q : ℝ) * Real.log B) := by
    rw [← Nat.cast_mul, Real.exp_nat_mul, Real.exp_log hB]
  have harg : ((D : ℝ) * Real.log B) * (q : ℝ) - c * (q : ℝ) * Real.log (q : ℝ) =
      (D : ℝ) * (q : ℝ) * Real.log B + (-c * (q : ℝ) * Real.log (q : ℝ)) := by ring
  rw [hpow, harg, Real.exp_add]
  ring

theorem tendsto_half_pow_nat_floor_mul {c1 : ℝ} (hc1 : 0 < c1) :
    Tendsto (fun q : ℕ => (1 / 2 : ℝ) ^ Nat.floor (c1 * (q : ℝ)))
      atTop (𝓝 0) := by
  have hpow : Tendsto (fun N : ℕ => (1 / 2 : ℝ) ^ N) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simpa only [Function.comp_def] using
    hpow.comp (tendsto_nat_floor_mul_atTop c1 hc1)

theorem tendsto_selectionFailureBound (D K R : ℕ) (A B C J c c1 : ℝ)
    (hK : 3 < K) (hB : 0 < B) (hc : 0 < c) (hc1 : 0 < c1) :
    Tendsto (selectionFailureBound D K R A B C J c c1) atTop
      (𝓝 ((1 / 2 : ℝ) ^ R)) := by
  change Tendsto
    (fun q : ℕ =>
      (R : ℝ) * A * (2 * C * (R : ℝ) / (q : ℝ)) ^ (K - 3) + (1 / 2 : ℝ) ^ R +
        J * ((D : ℝ) * (q : ℝ)) * B ^ (D * q) *
          Real.exp (-c * (q : ℝ) * Real.log (q : ℝ)) +
        (1 / 2 : ℝ) ^ Nat.floor (c1 * (q : ℝ)))
    atTop (𝓝 ((1 / 2 : ℝ) ^ R))
  simpa only [zero_add, add_zero] using
    (((tendsto_small_selection_term K R A C hK).add_const ((1 / 2 : ℝ) ^ R)).add
      (tendsto_density_selection_term D J B c hB hc)).add
        (tendsto_half_pow_nat_floor_mul hc1)

theorem exists_cutoff_threshold_selectionFailureBound (D K : ℕ) (A B C J c c1 : ℝ)
    (hK : 3 < K) (hB : 0 < B) (hc : 0 < c) (hc1 : 0 < c1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℕ, 1 ≤ R ∧ ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q →
      selectionFailureBound D K R A B C J c c1 q < ε := by
  have hpow : Tendsto (fun R : ℕ => (1 / 2 : ℝ) ^ R) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hsmall : ∀ᶠ R : ℕ in atTop, (1 / 2 : ℝ) ^ R < ε :=
    hpow.eventually (gt_mem_nhds hε)
  obtain ⟨R, hRge, hRsmall⟩ := ((eventually_ge_atTop (1 : ℕ)).and hsmall).exists
  have hbound : ∀ᶠ q : ℕ in atTop,
      selectionFailureBound D K R A B C J c c1 q < ε :=
    (tendsto_selectionFailureBound D K R A B C J c c1 hK hB hc hc1).eventually
      (gt_mem_nhds hRsmall)
  obtain ⟨Q, hQ⟩ := eventually_atTop.1 hbound
  exact ⟨R, hRge, Q, hQ⟩

end RyserCoveringCounterexample.Selection

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_Quantitative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u
noncomputable section
open scoped BigOperators

namespace RyserCoveringCounterexample.Selection

theorem layer_count_le_bounded (D n K q m : ℕ) (hn : n ≤ D * q) :
    (Real.exp 1 * (n : ℝ) / (m : ℝ)) ^ m * (3 * (K : ℝ) ^ 2) ^ m ≤
      (Real.exp 1 * (D : ℝ) * (q : ℝ) / (m : ℝ)) ^ m *
        (3 * (K : ℝ) ^ 2) ^ m := by
  have hnreal : (n : ℝ) ≤ (D : ℝ) * (q : ℝ) := by exact_mod_cast hn
  have hbase : Real.exp 1 * (n : ℝ) / (m : ℝ) ≤
      Real.exp 1 * (D : ℝ) * (q : ℝ) / (m : ℝ) := by
    simpa only [mul_assoc] using div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hnreal (Real.exp_pos 1).le) (Nat.cast_nonneg m)
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity) hbase m) (by positivity)

theorem exists_threshold_selection_failure_bound (D : ℕ) (hD : 1 ≤ D)
    (K : ℕ) (hK : 6 ≤ K)
    (hsmall : selectionSmallCoefficient D K * (1 / 2 : ℝ) ^ (K - 3) ≤ 1 / 2)
    (hlarge : selectionLargeCoefficient D K *
      Real.exp (2 - (K : ℝ) * densityDelta D) ≤ 1 / 2) :
    ∃ Q : ℕ, ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (n : ℕ) (data : Data F n), Bounded D data → Q ≤ Fintype.card F → ∀ R : ℕ,
      (poolLaw F n K).prob (fun pool => ¬HasCompatibleChoice data pool) ≤
        selectionFailureBound D K R (selectionSmallCoefficient D K)
          (max 1 (selectionLargeCoefficient D K)) (equationBound D)
          (densityChunkCount D : ℝ) (densityRate D) (selectionCutoff D)
          (Fintype.card F) := by
  classical
  obtain ⟨Q, hQ⟩ := exists_threshold_certificate_event_bound.{u} D hD K
  refine ⟨Q, ?_⟩
  intro F _ _ _ n data hdata hq R
  let q := Fintype.card F
  let S := (Finset.range (n + 1)).filter (fun m => 0 < m)
  let A := selectionSmallCoefficient D K
  let B := selectionLargeCoefficient D K
  let C := equationBound D
  let c1 := selectionCutoff D
  let J := (densityChunkCount D : ℝ)
  let c := densityRate D
  let delta := densityDelta D
  have hqpos : 0 < q := Fintype.card_pos
  have hqr : (0 : ℝ) < q := Nat.cast_pos.mpr hqpos
  have hA : 0 ≤ A := selectionSmallCoefficient_nonneg D K hD
  have hB : 0 ≤ B := selectionLargeCoefficient_nonneg D K hD
  have hC : 0 < C := equationBound_pos D hD
  have hc1 : 0 < c1 := selectionCutoff_pos D hD
  have hpos (m : ℕ) (hm : m ∈ S) : 0 < m := (Finset.mem_filter.mp hm).2
  have hsize (m : ℕ) (hm : m ∈ S) : m ≤ D * q := by
    have hmle : m ≤ n := Nat.lt_succ_iff.mp
      (Finset.mem_range.mp (Finset.mem_filter.mp hm).1)
    exact hmle.trans hdata.1
  have hprob := prob_not_hasCompatibleChoice_le_size_sum data (by omega : 0 < K)
    (certificateEventBound D K q) (certificateEventBound_nonneg D K q)
    (fun I _ T hT hcard => hQ F n data hdata hq I T hT hcard)
  have hpointwise (m : ℕ) (hm : m ∈ S) :
      ((Real.exp 1 * (n : ℝ) / (m : ℝ)) ^ m * (3 * (K : ℝ) ^ 2) ^ m) *
          certificateEventBound D K q m ≤
        if (m : ℝ) ≤ c1 * (q : ℝ) then
          (A * (2 * C * (m : ℝ) / (q : ℝ)) ^ (K - 3)) ^ m
        else B ^ m * (J * Real.exp (-c * (q : ℝ) * Real.log (q : ℝ)) +
          Real.exp (-(((K : ℝ) * delta - 2) * (m : ℝ)))) := by
    have hcount := mul_le_mul_of_nonneg_right
      (layer_count_le_bounded D n K q m hdata.1)
      (certificateEventBound_nonneg D K q m)
    refine hcount.trans ?_
    by_cases hmrange : (m : ℝ) ≤ c1 * (q : ℝ)
    · rw [ite_eq_left hmrange]
      have hevent : certificateEventBound D K q m =
          (2 * C * (m : ℝ) / (q : ℝ)) ^ ((K - 2) * m) := by
        rw [certificateEventBound, ite_eq_left hmrange, smallCertificateBase_eq]
      rw [hevent]
      exact le_of_eq (by
        simpa only [A, selectionSmallCoefficient, selectionSmallFactor, C] using
          small_layer_coefficient_identity m K C (D : ℝ) (q : ℝ)
            (hpos m hm) (by omega) hqr)
    · rw [ite_eq_right hmrange]
      have hevent : certificateEventBound D K q m =
          J * Real.exp (-c * (q : ℝ) * Real.log (q : ℝ)) +
            Real.exp (-(((K : ℝ) * delta - 2) * (m : ℝ))) := by
        rw [certificateEventBound, ite_eq_right hmrange]
        rfl
      rw [hevent]
      apply mul_le_mul_of_nonneg_right
      · simpa only [B, selectionLargeCoefficient, selectionLargeFactor, c1] using
          large_layer_count_le m K (D : ℝ) (q : ℝ) c1 (hpos m hm)
            (Nat.cast_nonneg D) hqr hc1 (lt_of_not_ge hmrange)
      · exact le_trans (certificateEventBound_nonneg D K q m) (le_of_eq hevent)
  have hsmallSum := small_certificate_sum_le
    (S.filter (fun m => (m : ℝ) ≤ c1 * (q : ℝ))) K R A C (q : ℝ)
    hA hC.le hqr
    (fun m hm => Nat.succ_le_of_lt (hpos m (Finset.mem_filter.mp hm).1))
    (fun m hm => by
      simpa only [smallCertificateBase_eq] using
        smallCertificateBase_le_half D q m hD hqpos (Finset.mem_filter.mp hm).2)
    hsmall
  have hlargeSum := large_layer_sum_le
    (S.filter (fun m => ¬(m : ℝ) ≤ c1 * (q : ℝ))) D K q B J c c1 delta
    hB (Nat.cast_nonneg _) hc1
    (fun m hm => Nat.succ_le_of_lt (hpos m (Finset.mem_filter.mp hm).1))
    (fun m hm => hsize m (Finset.mem_filter.mp hm).1)
    (fun m hm => lt_of_not_ge (Finset.mem_filter.mp hm).2) hlarge
  calc
    _ ≤ ∑ m ∈ S,
        ((Real.exp 1 * (n : ℝ) / (m : ℝ)) ^ m * (3 * (K : ℝ) ^ 2) ^ m) *
          certificateEventBound D K q m := hprob
    _ ≤ ∑ m ∈ S, if (m : ℝ) ≤ c1 * (q : ℝ) then
        (A * (2 * C * (m : ℝ) / (q : ℝ)) ^ (K - 3)) ^ m
      else B ^ m * (J * Real.exp (-c * (q : ℝ) * Real.log (q : ℝ)) +
        Real.exp (-(((K : ℝ) * delta - 2) * (m : ℝ)))) :=
      Finset.sum_le_sum hpointwise
    _ = (∑ m ∈ S.filter (fun m : ℕ => (m : ℝ) ≤ c1 * (q : ℝ)),
        (A * (2 * C * (m : ℝ) / (q : ℝ)) ^ (K - 3)) ^ m) +
      ∑ m ∈ S.filter (fun m : ℕ => ¬(m : ℝ) ≤ c1 * (q : ℝ)),
        B ^ m * (J * Real.exp (-c * (q : ℝ) * Real.log (q : ℝ)) +
          Real.exp (-(((K : ℝ) * delta - 2) * (m : ℝ)))) :=
      Finset.sum_ite _ _
    _ ≤ ((R : ℝ) * A * (2 * C * (R : ℝ) / (q : ℝ)) ^ (K - 3) +
        (1 / 2 : ℝ) ^ R) +
      (J * ((D : ℝ) * (q : ℝ)) * (max 1 B) ^ (D * q) *
        Real.exp (-c * (q : ℝ) * Real.log (q : ℝ)) +
        (1 / 2 : ℝ) ^ Nat.floor (c1 * (q : ℝ))) := add_le_add hsmallSum hlargeSum
    _ = _ := by simp only [selectionFailureBound, A, B, C, J, c, c1, q]; ring

end RyserCoveringCounterexample.Selection

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

namespace RyserCoveringCounterexample.Selection

theorem compatible_selection_uniform_oai (D : ℕ) (hD : 1 ≤ D) :
    ∃ K : ℕ, 6 ≤ K ∧
      ∀ ε : ℝ, 0 < ε → ∃ Q : ℕ,
        ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
          (n : ℕ) (data : Data F n),
          Bounded D data → Q ≤ Fintype.card F →
            1 - ε ≤ (poolLaw F n K).prob
              (fun pool => HasCompatibleChoice data pool) := by
  classical
  obtain ⟨K, hK, hsmall, hlarge⟩ := exists_selection_pool_size D
  refine ⟨K, hK, ?_⟩
  intro ε hε
  obtain ⟨Q0, hQ0⟩ :=
    exists_threshold_selection_failure_bound.{u} D hD K hK hsmall hlarge.le
  have hK3 : 3 < K := lt_of_lt_of_le (by norm_num : 3 < 6) hK
  have hB : (0 : ℝ) < max 1 (selectionLargeCoefficient D K) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  obtain ⟨R, _hR, Q1, hQ1⟩ :=
    exists_cutoff_threshold_selectionFailureBound D K
      (selectionSmallCoefficient D K)
      (max 1 (selectionLargeCoefficient D K))
      (equationBound D)
      (densityChunkCount D : ℝ)
      (densityRate D)
      (selectionCutoff D)
      hK3 hB (densityRate_pos D hD) (selectionCutoff_pos D hD) hε
  refine ⟨max Q0 Q1, ?_⟩
  intro F _ _ _ n data hdata hq
  have hq0 : Q0 ≤ Fintype.card F := (le_max_left _ _).trans hq
  have hq1 : Q1 ≤ Fintype.card F := (le_max_right _ _).trans hq
  have hfailure :
      (poolLaw F n K).prob (fun pool => ¬HasCompatibleChoice data pool) < ε :=
    (hQ0 F n data hdata hq0 R).trans_lt (hQ1 (Fintype.card F) hq1)
  rw [(poolLaw F n K).prob_compl (fun pool => HasCompatibleChoice data pool)] at hfailure
  linarith

end RyserCoveringCounterexample.Selection

end OAI
end

theorem solution.{u} : type_of% @OAI.RyserCoveringCounterexample.Selection.compatible_selection_uniform_oai.{u} := @OAI.RyserCoveringCounterexample.Selection.compatible_selection_uniform_oai.{u}
