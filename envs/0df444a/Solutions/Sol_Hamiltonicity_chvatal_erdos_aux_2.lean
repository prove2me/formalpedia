-- Prove2me | solution 2 for Hamiltonicity.chvatal_erdos_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:57:40.134461+00:00
-- url     : https://prove2.me/submissions/587d2467-2bfb-47ee-afe3-943a7554cceb

module
public import Definitions.Def_MengerHamilton_LongerCycle
public import Definitions.Def_MengerHamilton_ChvatalErdosAux
public import Theorems.Thm_Hamiltonicity_CycArr_ne_succ
public import Theorems.Thm_Hamiltonicity_exists_fan
public import Theorems.Thm_Hamiltonicity_exists_cycArr_of_conn
public import Theorems.Thm_Hamiltonicity_CycArr_eq_iff
public import Theorems.Thm_Hamiltonicity_CycArr_eq_mod
public import Theorems.Thm_Hamiltonicity_CycArr_extend
public import Theorems.Thm_Hamiltonicity_CycArr_isHamiltonian
public import Theorems.Thm_Hamiltonicity_CycArr_le_card
public import Theorems.Thm_Hamiltonicity_CycArr_pos
public import Theorems.Thm_Hamiltonicity_isHamiltonian_of_forall_adj
public import Theorems.Thm_Menger_Aux_Sep_symm


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Hamiltonicity
variable {V : Type*}
namespace Hamiltonicity
theorem _root_.solution [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hn : 3 ≤ Fintype.card V) (k : ℕ)
    (hconn : ∀ S : Set V, S.ncard < k → (G.induce Sᶜ).Connected)
    (hα : ∀ s : Set V, G.IsIndepSet s → s.ncard ≤ k) : G.IsHamiltonian := by
  classical
  by_cases hall : ∀ u v, u ≠ v → G.Adj u v
  · exact isHamiltonian_of_forall_adj hn hall
  push Not at hall
  obtain ⟨s, t, hst, hnst⟩ := hall
  have hk2 : 2 ≤ k := by
    have := hα {s, t} (by
      intro a ha b hb hab
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact absurd rfl hab
      · exact hnst
      · exact fun h => hnst h.symm
      · exact absurd rfl hab)
    rwa [Set.ncard_pair hst] at this
  obtain ⟨m0, f0, hf0⟩ := exists_cycArr_of_conn hn hk2 hconn
  -- a longest cycle
  set M := Nat.findGreatest (fun m => ∃ f, CycArr G m f) (Fintype.card V) with hM
  obtain ⟨f, hf⟩ : ∃ f, CycArr G M f :=
    Nat.findGreatest_spec (P := fun m => ∃ f, CycArr G m f) hf0.le_card ⟨f0, hf0⟩
  have hmax : ∀ m' g, CycArr G m' g → m' ≤ M := fun m' g hg =>
    Nat.le_findGreatest (P := fun m => ∃ f, CycArr G m f) hg.le_card ⟨g, hg⟩
  by_cases hMn : M = Fintype.card V
  · exact hf.isHamiltonian hMn
  have hMlt : M < Fintype.card V := lt_of_le_of_ne hf.le_card hMn
  have hM3 := hf.three_le
  -- a vertex off the cycle
  obtain ⟨x, hx⟩ : ∃ x, ∀ i, f i ≠ x := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset V) ⊆ (Finset.range M).image f := by
      intro y _
      obtain ⟨i, hi⟩ := hcon y
      rw [hf.eq_mod] at hi
      exact Finset.mem_image.2 ⟨_, Finset.mem_range.2 (Nat.mod_lt _ hf.pos), hi⟩
    have h1 := Finset.card_le_card hsub
    have h2 := (Finset.card_image_le (s := Finset.range M) (f := f)).trans_eq
      (Finset.card_range M)
    rw [Finset.card_univ] at h1
    omega
  obtain ⟨r, hr, t, P, hP, hPint, hPdisj⟩ := exists_fan hconn hf hx
  have hPlen : ∀ j, 1 ≤ (P j).length := fun j => by
    by_contra h
    push Not at h
    exact hx _ (Walk.eq_of_length_eq_zero (by omega : (P j).length = 0)).symm
  have hlonger : ∀ a b (Q : G.Walk (f a) (f b)), f a ≠ f b → Q.IsPath → 2 ≤ Q.length →
      (∀ y ∈ Q.support, ∀ i, f i = y → y = f a ∨ y = f b) → G.Adj (f (a + 1)) (f (b + 1)) →
      False := by
    intro a b Q hab hQ hQl hint hadj
    obtain ⟨g, hg⟩ := hf.extend hab Q hQ hQl hint hadj
    have := hmax _ _ hg
    omega
  have hxtail : ∀ j, x ∉ (P j).support.tail := by
    intro j hxj
    have := (hP j).support_nodup
    rw [← Walk.cons_tail_support] at this
    exact (List.nodup_cons.1 this).1 hxj
  have htinj : ∀ i j, f (t i) = f (t j) → i = j := by
    intro i j h
    by_contra hij
    exact hx _ (hPdisj i j hij _ (P i).end_mem_support (by rw [h]; exact (P j).end_mem_support))
  -- two fan paths joined at `x`
  have hcomb : ∀ i j, i ≠ j → G.Adj (f (t i + 1)) (f (t j + 1)) → False := by
    intro i j hij hadj
    have hne : f (t i) ≠ f (t j) := fun h => hij (htinj i j h)
    refine hlonger (t i) (t j) ((P i).reverse.append (P j)) hne ?_ ?_ ?_ hadj
    · rw [Walk.isPath_def, Walk.support_append, Walk.support_reverse, List.nodup_append]
      refine ⟨List.nodup_reverse.2 (hP i).support_nodup,
        (hP j).support_nodup.sublist (List.tail_sublist _), ?_⟩
      intro y hy z hz hyz
      subst hyz
      rw [List.mem_reverse] at hy
      have := hPdisj i j hij y hy (List.mem_of_mem_tail hz)
      subst this
      exact hxtail j hz
    · rw [Walk.length_append, Walk.length_reverse]
      have := hPlen i
      have := hPlen j
      omega
    · intro y hy i' hi'
      rw [Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse] at hy
      rcases hy with hy | hy
      · exact Or.inl (hPint i y hy i' hi')
      · exact Or.inr (hPint j y hy i' hi')
  -- no two consecutive endpoints
  have hnc : ∀ i j, f (t j) ≠ f (t i + 1) := by
    intro i j h
    by_cases hij : i = j
    · subst hij
      exact hf.ne_succ _ h
    · apply hcomb i j hij
      rw [← h]
      exact hf.adj _
  -- `x` is not adjacent to a successor
  have hxs : ∀ i, ¬ G.Adj x (f (t i + 1)) := by
    intro i hadj
    have hne : f (t i) ≠ f (t i + 1) := hf.ne_succ _
    have hnot : f (t i + 1) ∉ (P i).support := fun h => hne (hPint i _ h _ rfl).symm
    refine hlonger (t i) (t i + 1) ((P i).reverse.concat hadj) hne ?_ ?_ ?_ (hf.adj _)
    · rw [Walk.isPath_def, Walk.support_concat, Walk.support_reverse,
        List.nodup_append]
      refine ⟨List.nodup_reverse.2 (hP i).support_nodup, List.nodup_singleton _, ?_⟩
      intro y hy z hz hyz
      rw [List.mem_singleton] at hz
      subst hz hyz
      exact hnot (List.mem_reverse.1 hy)
    · rw [Walk.length_concat, Walk.length_reverse]
      have := hPlen i
      omega
    · intro y hy i' hi'
      rw [Walk.support_concat, List.mem_append, Walk.support_reverse,
        List.mem_reverse, List.mem_singleton] at hy
      rcases hy with hy | rfl
      · exact Or.inl (hPint i y hy i' hi')
      · exact Or.inr rfl
  -- at least `k` fan paths
  have hrk : k ≤ r := by
    by_contra hlt
    push Not at hlt
    have hMr : M ≤ r := by
      rcases le_total k M with h | h
      · rw [min_eq_left h] at hr
        omega
      · rwa [min_eq_right h] at hr
    have hr0 : 0 < r := by omega
    obtain ⟨j, hj⟩ : ∃ j, t j % M = (t ⟨0, hr0⟩ + 1) % M := by
      have himg : Finset.univ.image (fun j => t j % M) = Finset.range M := by
        apply Finset.eq_of_subset_of_card_le
        · intro z hz
          simp only [Finset.mem_image, Finset.mem_univ, true_and] at hz
          obtain ⟨j, rfl⟩ := hz
          exact Finset.mem_range.2 (Nat.mod_lt _ hf.pos)
        · rw [Finset.card_range, Finset.card_image_of_injective, Finset.card_univ,
            Fintype.card_fin]
          · exact hMr
          · intro i j h
            exact htinj i j (hf.eq_iff.2 h)
      have : (t ⟨0, hr0⟩ + 1) % M ∈ Finset.range M := Finset.mem_range.2 (Nat.mod_lt _ hf.pos)
      rw [← himg] at this
      simpa using this
    exact hnc ⟨0, hr0⟩ j (hf.eq_iff.2 hj)
  -- the set `{x} ∪ {successors}` is independent
  set S : Finset V := insert x (Finset.univ.image (fun j => f (t j + 1))) with hS
  have hScard : S.card = r + 1 := by
    rw [hS, Finset.card_insert_of_notMem, Finset.card_image_of_injective, Finset.card_univ,
      Fintype.card_fin]
    · intro i j h
      apply htinj i j
      rw [hf.eq_iff] at h ⊢
      exact Nat.ModEq.add_right_cancel' 1 h
    · simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
      intro j h
      exact hx _ h
  have hind : G.IsIndepSet (S : Set V) := by
    intro a ha b hb hab hadj
    simp only [hS, Finset.coe_insert, Finset.coe_image, Finset.coe_univ, Set.image_univ,
      Set.mem_insert_iff, Set.mem_range] at ha hb
    rcases ha with rfl | ⟨i, rfl⟩ <;> rcases hb with rfl | ⟨j, rfl⟩
    · exact hab rfl
    · exact hxs j hadj
    · exact hxs i hadj.symm
    · exact hcomb i j (fun h => hab (h ▸ rfl)) hadj
  have := hα _ hind
  rw [Set.ncard_coe_finset, hScard] at this
  omega
end Hamiltonicity
