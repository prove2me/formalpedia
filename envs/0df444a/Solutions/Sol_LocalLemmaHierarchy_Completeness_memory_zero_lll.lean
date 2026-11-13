-- Prove2me | solution 1 for LocalLemmaHierarchy.Completeness.memory_zero_lll
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:01:47.174534+00:00
-- url     : https://prove2.me/submissions/3856b5f6-b02a-4689-94c6-13730d193953

import Mathlib
import Definitions.Def_LocalLemmaHierarchy_Completeness_Representation
import Definitions.Def_LocalLemmaHierarchy_Completeness_Histories
import Definitions.Def_LocalLemmaHierarchy_Completeness_Memory
import Definitions.Def_LocalLemmaHierarchy_Completeness_Graph
import Theorems.Thm_LocalLemmaHierarchy_Completeness_theorem_3_2

section
set_option autoImplicit false

open scoped ENNReal NNReal

namespace LocalLemmaHierarchy.Completeness.Dev.MZ

open scoped Classical

variable {V : Type} (G : SimpleGraph V) [G.LocallyFinite] (o : NeighborOrders G)

theorem state_zero (s : Hist (indRep G o)) :
    IsMemState (indRep G o) 0 s ↔ ∃ v, s = indState G o v := by
  constructor
  · rintro ⟨-, h⟩
    refine ⟨s.start, ?_⟩
    have : s.moves = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp h)
    cases s
    simp_all [indState]
  · rintro ⟨v, rfl⟩
    exact ⟨⟨Set.mem_univ _, fun i hi => by simp [indState] at hi⟩, by simp [indState]⟩

theorem sum_helper {ι M : Type} [AddCommMonoid M] [Fintype ι] [Subsingleton ι] (a0 : ι)
    (s : Finset ι) (hs : a0 ∈ s) (f : ι → M) : ∑ a ∈ s, f a = f a0 :=
  Finset.sum_eq_single_of_mem a0 hs (fun b _ hb => absurd (Subsingleton.elim b a0) hb)

theorem update_zero (p : V → ℝ) (x : Hist (indRep G o) → ℝ) (v : V) :
    memUpdate (indRep G o) 0 p x (indState G o v) =
      p v * ∏ u ∈ G.neighborFinset v, (1 - x (indState G o u))⁻¹ := by
  have hD : ∀ a : (indRep G o).Opt (indState G o v).endpoint,
      (indRep G o).D (indState G o v).endpoint a \
        insert (indState G o v).endpoint (deleted (indRep G o) (indState G o v).moves)
        = G.neighborFinset v := by
    intro a
    ext u
    simp [indRep, indState, Hist.endpoint, Hist.endpointOf, deleted]
    constructor
    · rintro ⟨h | h, h2⟩
      · exact absurd h h2
      · exact h
    · intro h
      exact ⟨Or.inr h, fun e => (G.ne_of_adj h) e.symm⟩
  have hdel : deleted (indRep G o) (indState G o v).moves = ∅ := rfl
  have hst : ∀ u, memStar 0 (indState G o v) () u = indState G o u := by
    intro u
    simp [memStar, Hist.suffix, Hist.append, indState, Hist.endpointOf]
  unfold memUpdate
  have : Subsingleton ((indRep G o).Opt (indState G o v).endpoint) :=
    inferInstanceAs (Subsingleton Unit)
  refine (sum_helper (ι := (indRep G o).Opt (indState G o v).endpoint) () _
    (Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp [hdel]⟩) _).trans ?_
  show (1 : ℝ) * p v * _ = _
  rw [one_mul, hD ()]
  all_goals (try congr 1)
  all_goals exact Finset.prod_congr rfl (fun u _ => by rw [hst])

theorem cert_iff (p : V → ℝ) (x : Hist (indRep G o) → ℝ) :
    IsMemCertificate (indRep G o) 0 p x ↔
      ∀ v, 0 ≤ x (indState G o v) ∧ x (indState G o v) < 1 ∧
        p v ≤ x (indState G o v) * ∏ u ∈ G.neighborFinset v, (1 - x (indState G o u)) := by
  constructor
  · intro h v
    have hall : ∀ u, 0 ≤ x (indState G o u) ∧ x (indState G o u) < 1 := fun u =>
      ⟨(h _ ((state_zero G o _).2 ⟨u, rfl⟩)).1, (h _ ((state_zero G o _).2 ⟨u, rfl⟩)).2.1⟩
    obtain ⟨h0, h1, h2⟩ := h _ ((state_zero G o _).2 ⟨v, rfl⟩)
    rw [update_zero] at h2
    refine ⟨h0, h1, ?_⟩
    have hpos : 0 < ∏ u ∈ G.neighborFinset v, (1 - x (indState G o u)) :=
      Finset.prod_pos fun u _ => by linarith [(hall u).2]
    rw [Finset.prod_inv_distrib, ← div_eq_mul_inv, div_le_iff₀ hpos] at h2
    exact h2
  · intro h s hs
    obtain ⟨v, rfl⟩ := (state_zero G o _).1 hs
    have hall : ∀ u, 0 ≤ x (indState G o u) ∧ x (indState G o u) < 1 := fun u =>
      ⟨(h u).1, (h u).2.1⟩
    obtain ⟨h0, h1, h2⟩ := h v
    refine ⟨h0, h1, ?_⟩
    have hpos : 0 < ∏ u ∈ G.neighborFinset v, (1 - x (indState G o u)) :=
      Finset.prod_pos fun u _ => by linarith [(hall u).2]
    rw [update_zero, Finset.prod_inv_distrib, ← div_eq_mul_inv, div_le_iff₀ hpos]
    exact h2

theorem indep_insert (J : Finset V) (v : V) :
    G.IsIndepSet (↑(insert v J) : Set V) ↔
      G.IsIndepSet (↑J : Set V) ∧ ∀ w ∈ J, v ≠ w → ¬ G.Adj v w := by
  rw [SimpleGraph.isIndepSet_iff, SimpleGraph.isIndepSet_iff, Finset.coe_insert,
    Set.pairwise_insert]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun w hw hne => (h2 w hw hne).1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun w hw hne => ⟨h2 w hw hne, fun hh => h2 w hw hne hh.symm⟩⟩

theorem indep_split (U : Finset V) (v : V) (hv : v ∈ U) :
    indepPoly G U = indepPoly G (U.erase v) +
      MvPolynomial.X v * indepPoly G (U \ insert v (G.neighborFinset v)) := by
  unfold indepPoly
  rw [← Finset.sum_filter_add_sum_filter_not
    (U.powerset.filter (fun I : Finset V => G.IsIndepSet (I : Set V))) (fun I => v ∈ I)]
  have h1 : (U.powerset.filter (fun I : Finset V => G.IsIndepSet (I : Set V))).filter
      (fun I => ¬ v ∈ I) = (U.erase v).powerset.filter (fun I : Finset V => G.IsIndepSet (I : Set V)) := by
    ext I
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨fun w hw => Finset.mem_erase.2 ⟨fun e => h3 (e ▸ hw), h1 hw⟩, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨fun w hw => (Finset.mem_erase.1 (h1 hw)).2, h2⟩, fun hh => ?_⟩
      exact (Finset.mem_erase.1 (h1 hh)).1 rfl
  have h2 : (U.powerset.filter (fun I : Finset V => G.IsIndepSet (I : Set V))).filter
      (fun I => v ∈ I) = ((U \ insert v (G.neighborFinset v)).powerset.filter
        (fun I : Finset V => G.IsIndepSet (I : Set V))).image (insert v) := by
    ext I
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨I.erase v, ⟨?_, ?_⟩, Finset.insert_erase h3⟩
      · have h2' := h2
        rw [← Finset.insert_erase h3, indep_insert] at h2'
        intro w hw
        obtain ⟨hne, hwI⟩ := Finset.mem_erase.1 hw
        simp only [Finset.mem_sdiff, Finset.mem_insert, not_or, SimpleGraph.mem_neighborFinset]
        exact ⟨h1 hwI, fun e => hne e, fun hadj => h2'.2 w hw (Ne.symm hne) hadj⟩
      · have h2' := h2
        rw [← Finset.insert_erase h3, indep_insert] at h2'
        exact h2'.1
    · rintro ⟨J, ⟨h1, h2⟩, rfl⟩
      have hvJ : v ∉ J := fun hh => by
        have := h1 hh
        simp at this
      refine ⟨⟨?_, ?_⟩, Finset.mem_insert_self _ _⟩
      · intro w hw
        rcases Finset.mem_insert.1 hw with rfl | hw
        · exact hv
        · exact (Finset.mem_sdiff.1 (h1 hw)).1
      · rw [indep_insert]
        refine ⟨h2, fun w hw _ hadj => ?_⟩
        have := (Finset.mem_sdiff.1 (h1 hw)).2
        simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset, not_or] at this
        exact this.2 hadj
  rw [h1, h2, Finset.sum_image, Finset.mul_sum, add_comm]
  · congr 1
    refine Finset.sum_congr rfl fun J hJ => ?_
    have hvJ : v ∉ J := by
      simp only [Finset.mem_filter, Finset.mem_powerset] at hJ
      intro hh
      have := hJ.1 hh
      simp at this
    rw [Finset.prod_insert hvJ]
  · intro I hI J hJ hIJ
    have hvI : v ∉ I := by
      simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_setOf_eq] at hI
      intro hh
      have := hI.1 hh
      simp at this
    have hvJ : v ∉ J := by
      simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_setOf_eq] at hJ
      intro hh
      have := hJ.1 hh
      simp at this
    rw [← Finset.erase_insert hvI, hIJ, Finset.erase_insert hvJ]

theorem indep_rep : IsRepresentationOf (indRep G o) (indepPoly G) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold indepPoly
    rw [Finset.powerset_empty, Finset.filter_singleton, if_pos (by simp [SimpleGraph.isIndepSet_iff])]
    simp
  · intro U
    unfold indepPoly
    rw [map_sum, Finset.sum_eq_single ∅]
    · simp
    · intro I hI hne
      rw [map_prod]
      obtain ⟨w, hw⟩ := Finset.nonempty_iff_ne_empty.2 hne
      exact Finset.prod_eq_zero hw (by simp)
    · intro h
      exfalso
      apply h
      simp
  · intro U v hv
    have hfil : Finset.univ.filter (fun a : (indRep G o).Opt v =>
        (indRep G o).A v a ⊆ U) = Finset.univ := by
      apply Finset.filter_true_of_mem
      intro a _
      show ({v} : Finset V) ⊆ U
      simpa using hv
    rw [hfil]
    have : Subsingleton ((indRep G o).Opt v) := inferInstanceAs (Subsingleton Unit)
    rw [indep_split G U v hv]
    congr 1
    refine Eq.symm ((sum_helper (ι := (indRep G o).Opt v) () _ (Finset.mem_univ _) _).trans ?_)
    show MvPolynomial.C (1 : ℝ) * MvPolynomial.X v *
      indepPoly G (U \ insert v (G.neighborFinset v)) = _
    rw [map_one, one_mul]

end LocalLemmaHierarchy.Completeness.Dev.MZ

namespace LocalLemmaHierarchy.Completeness

open Dev.MZ in
theorem chk_memory_zero_lll {V : Type} (G : SimpleGraph V) [G.LocallyFinite] (o : NeighborOrders G)
    (p : V → ℝ) (hp : ∀ v, 0 ≤ p v) :
    (∀ x : Hist (indRep G o) → ℝ, IsMemCertificate (indRep G o) 0 p x ↔
      ∀ v, 0 ≤ x (indState G o v) ∧ x (indState G o v) < 1 ∧
        p v ≤ x (indState G o v) * ∏ u ∈ G.neighborFinset v, (1 - x (indState G o u))) ∧
    (∀ r : V → ℝ, (∀ v, 0 < r v) →
      (IsMemCertificate (indRep G o) 0 p (fun s => r s.endpoint / (1 + r s.endpoint)) ↔
        ∀ v, p v ≤ r v / (1 + r v) * ∏ u ∈ G.neighborFinset v, 1 / (1 + r u))) ∧
    ∀ x : V → ℝ, (∀ v, 0 ≤ x v ∧ x v < 1) →
      (∀ v, p v ≤ x v * ∏ u ∈ G.neighborFinset v, (1 - x u)) →
      ∀ U : Finset V, ZeroFreeOn (indepPoly G) U p := by
  refine ⟨cert_iff G o p, ?_, ?_⟩
  · intro r hr
    have hne : ∀ u, (1 + r u) ≠ 0 := fun u => by linarith [hr u]
    have e : ∀ u, 1 - r u / (1 + r u) = 1 / (1 + r u) := by
      intro u
      rw [eq_div_iff (hne u), sub_mul, div_mul_cancel₀ _ (hne u)]
      ring
    rw [cert_iff]
    constructor
    · intro h v
      have h3 := (h v).2.2
      have h3' : p v ≤ r v / (1 + r v) * ∏ u ∈ G.neighborFinset v, (1 - r u / (1 + r u)) := h3
      simpa only [e] using h3'
    · intro h v
      refine ⟨?_, ?_, ?_⟩
      · show 0 ≤ r v / (1 + r v)
        exact div_nonneg (hr v).le (by linarith [hr v])
      · show r v / (1 + r v) < 1
        rw [div_lt_one (by linarith [hr v])]; linarith
      · show p v ≤ r v / (1 + r v) * ∏ u ∈ G.neighborFinset v, (1 - r u / (1 + r u))
        simpa only [e] using h v
  · intro x hx hxp U
    have hcert : IsMemCertificate (indRep G o) 0 p (fun s => x s.endpoint) :=
      (cert_iff G o p _).2 (fun v => ⟨(hx v).1, (hx v).2, hxp v⟩)
    exact (theorem_3_2 (indRep G o) (indepPoly G) (indep_rep G o)).1 0 p hp _ hcert U

end LocalLemmaHierarchy.Completeness
end

theorem solution : type_of% @LocalLemmaHierarchy.Completeness.chk_memory_zero_lll := @LocalLemmaHierarchy.Completeness.chk_memory_zero_lll
