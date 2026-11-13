-- Prove2me | solution 1 for KSATSingleFlip.Connect.lemma_7_5
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T03:31:49.631199+00:00
-- url     : https://prove2.me/submissions/6cdef0c7-873b-46b2-ab5b-8d389180e80b

import Definitions.Def_KSATSingleFlip_Connect_Repair

open scoped Classical BigOperators

namespace KSATSingleFlip.Connect

/-- The size estimate in Lemma 7.5: assignments that agree away from U differ
on at most |U| variables. -/
theorem audit_hamming_le_card {n : ℕ} (U : Finset (Fin n))
    (x y : Fin n → Bool) (h : ∀ u, u ∉ U → x u = y u) :
    hamming x y ≤ U.card := by
  apply Finset.card_le_card
  intro u hu
  by_contra hnot
  have hxy := h u hnot
  have hne : x u ≠ y u := (Finset.mem_filter.mp hu).2
  exact hne hxy

/-- Two inputs and the repair target, all agreeing with the reference off U,
contribute at most twice the repair set's cardinality. -/
theorem audit_findPath_distance_bound {n : ℕ} (U : Finset (Fin n))
    (x y y' t : Fin n → Bool)
    (hy : ∀ u, u ∉ U → y u = x u)
    (hy' : ∀ u, u ∉ U → y' u = x u)
    (ht : ∀ u, u ∉ U → t u = x u) :
    hamming y t + hamming y' t ≤ 2 * U.card := by
  have h₁ : hamming y t ≤ U.card := audit_hamming_le_card U y t (by
    intro u hu
    rw [hy u hu, ht u hu])
  have h₂ : hamming y' t ≤ U.card := audit_hamming_le_card U y' t (by
    intro u hu
    rw [hy' u hu, ht u hu])
  omega

/-- Hamming distance satisfies the triangle inequality. -/
theorem audit_hamming_triangle {n : ℕ} (x y z : Fin n → Bool) :
    hamming x z ≤ hamming x y + hamming y z := by
  unfold hamming
  calc
    (disagree x z).card ≤ (disagree x y ∪ disagree y z).card := by
      apply Finset.card_le_card
      intro u hu
      simp only [disagree, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_union] at *
      by_cases hxy : x u = y u
      · right
        intro hyz
        exact hu (hxy.trans hyz)
      · exact Or.inl hxy
    _ ≤ (disagree x y).card + (disagree y z).card := Finset.card_union_le _ _

/-- A returned path with at most 2n flips obeys the declared cost model. -/
theorem audit_findPath_cost_bound {n q : ℕ} (p : List (Fin n → Bool))
    (hn : 0 < n) (hp : p ≠ []) (hlen : pathLength p ≤ 2 * n) :
    (findPathCost n q p : ℝ) ≤ 8 * n * (n + q) := by
  have plen : p.length = pathLength p + 1 := by
    unfold pathLength
    have : 0 < p.length := List.length_pos_iff.mpr hp
    omega
  unfold findPathCost
  push_cast
  have hlenR : (pathLength p : ℝ) ≤ 2 * n := by exact_mod_cast hlen
  have plenR : (p.length : ℝ) = pathLength p + 1 := by exact_mod_cast plen
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hqR : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  rw [plenR]
  have hmul : (0 : ℝ) ≤ (2 * n - (pathLength p : ℝ)) * (2 * n + q) :=
    mul_nonneg (by linarith) (by positivity)
  have hm2 : (0 : ℝ) ≤ ((n : ℝ) - 1) * (n + q) :=
    mul_nonneg (by linarith) (by positivity)
  nlinarith

/-- A flip toward the target removes exactly one disagreement. -/
theorem audit_disagree_flip {n : ℕ} (z t : Fin n → Bool) (u : Fin n)
    (hu : z u ≠ t u) :
    disagree (flip z u) t = (disagree z t).erase u := by
  ext v
  by_cases hv : v = u
  · subst v
    simp only [disagree, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase, ne_eq, not_true_eq_false, false_and, iff_false]
    simp only [flip, Function.update_self]
    cases hz : z u <;> cases ht : t u <;> simp_all
  · simp only [disagree, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase]
    rw [show flip z u v = z v from Function.update_of_ne hv _ _]
    simp [hv]

/-- Any single-flip walk has at least Hamming distance many steps. -/
theorem audit_chain_lower_bound {n : ℕ} (a b : Fin n → Bool)
    (l : List (Fin n → Bool))
    (hchain : (a :: l).IsChain (fun x y => hamming x y = 1))
    (hlast : (a :: l).getLast? = some b) :
    hamming a b ≤ l.length := by
  induction l generalizing a with
  | nil =>
      simp only [List.getLast?_cons, List.getLast?_nil] at hlast
      have hab : a = b := by simpa using hlast
      subst b
      simp [hamming, disagree]
  | cons c cs ih =>
      have hc := List.isChain_cons_cons.mp hchain
      have hlast' : (c :: cs).getLast? = some b := by simpa using hlast
      have htail := ih c hc.2 hlast'
      have htri := audit_hamming_triangle a c b
      simp only [List.length_cons]
      omega

/-- Hamming distance one is exactly a single Boolean flip. -/
theorem audit_distance_one_is_flip {n : ℕ} (a c : Fin n → Bool)
    (h : hamming a c = 1) : ∃ u, c = flip a u := by
  have hc : (disagree a c).card = 1 := h
  obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hc
  refine ⟨u, ?_⟩
  funext v
  by_cases hv : v = u
  · subst v
    have hne : a u ≠ c u := by
      have : u ∈ disagree a c := by rw [hu]; simp
      simpa [disagree] using this
    simp only [flip, Function.update_self]
    cases ha : a u <;> cases ht : c u <;> simp_all
  · have hn : v ∉ disagree a c := by rw [hu]; simp [hv]
    have he : a v = c v := by simpa [disagree] using hn
    rw [show flip a u v = a v from Function.update_of_ne hv _ _]
    exact he.symm

/-- A flip away from the target adds one disagreement. -/
theorem audit_disagree_flip_away {n : ℕ} (z t : Fin n → Bool) (u : Fin n)
    (hu : z u = t u) :
    disagree (flip z u) t = insert u (disagree z t) := by
  ext v
  by_cases hv : v = u
  · subst v
    simp only [disagree, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, or_true, iff_true]
    simp only [flip, Function.update_self]
    rw [← hu]
    cases h : z u <;> simp [h]
  · simp only [disagree, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    rw [show flip z u v = z v from Function.update_of_ne hv _ _]
    simp [hv]

theorem audit_hamming_flip_away {n : ℕ} (z t : Fin n → Bool) (u : Fin n)
    (hu : z u = t u) : hamming (flip z u) t = hamming z t + 1 := by
  unfold hamming
  rw [audit_disagree_flip_away z t u hu, Finset.card_insert_of_notMem]
  simp [disagree, hu]

/-- The first move of a Hamming-shortest satisfying path is a legal flip toward t. -/
theorem audit_shortest_path_has_move {n : ℕ} (Φ : GFormula (Fin n))
    (z t : Fin n → Bool) (p : List (Fin n → Bool))
    (hp : IsSatPath Φ p z t) (hlen : pathLength p = hamming z t)
    (hne : z ≠ t) : ∃ u, z u ≠ t u ∧ FSat (flip z u) Φ := by
  rcases p with _ | ⟨a, p⟩
  · simp [IsSatPath, IsPathIn] at hp
  · have ha : a = z := by simpa [IsSatPath, IsPathIn] using hp.1
    subst a
    rcases p with _ | ⟨c, cs⟩
    · have : z = t := by simpa [IsSatPath, IsPathIn] using hp.2.1
      exact (hne this).elim
    · have hc : hamming z c = 1 := (List.isChain_cons_cons.mp hp.2.2.2).1
      have htail : hamming c t ≤ cs.length := by
        apply audit_chain_lower_bound c t cs
        · exact (List.isChain_cons_cons.mp hp.2.2.2).2
        · simpa using hp.2.1
      have hlen' : cs.length + 1 = hamming z t := by simpa [pathLength] using hlen
      obtain ⟨u, rfl⟩ := audit_distance_one_is_flip z c hc
      have hmove : z u ≠ t u := by
        intro he
        have haway := audit_hamming_flip_away z t u he
        omega
      refine ⟨u, hmove, ?_⟩
      have hs := hp.2.2.1 (flip z u) (by simp)
      simpa [sols] using hs

theorem audit_hamming_flip_toward {n : ℕ} (z t : Fin n → Bool) (u : Fin n)
    (hu : z u ≠ t u) : hamming (flip z u) t + 1 = hamming z t := by
  unfold hamming
  rw [audit_disagree_flip z t u hu]
  have hm : u ∈ disagree z t := by simpa [disagree] using hu
  exact Finset.card_erase_add_one hm

theorem audit_hamming_single_flip {n : ℕ} (z : Fin n → Bool) (u : Fin n) :
    hamming z (flip z u) = 1 := by
  have hs : disagree z (flip z u) = {u} := by
    ext v
    by_cases hv : v = u
    · subst v
      have : z u ≠ flip z u u := by
        simp only [flip, Function.update_self]
        cases h : z u <;> simp
      simpa [disagree] using this
    · simp only [disagree, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      rw [show flip z u v = z v from Function.update_of_ne hv _ _]
      simp [hv]
  simp [hamming, hs]

/-- Greedy routing succeeds whenever every satisfying intermediate assignment has a
shortest satisfying continuation to t, and its flips are confined to U. -/
theorem audit_greedy_success {n : ℕ} (Φ : GFormula (Fin n))
    (x t : Fin n → Bool) (U : Finset (Fin n))
    (ht : ∀ u, u ∉ U → t u = x u)
    (H : ∀ z, z ∈ sols Φ → (∀ u, u ∉ U → z u = x u) →
      ∃ p, IsSatPath Φ p z t ∧ pathLength p = hamming z t) :
    ∀ fuel z, z ∈ sols Φ → (∀ u, u ∉ U → z u = x u) →
      hamming z t ≤ fuel →
      ∃ p, greedyWalk Φ t fuel z = some p ∧ IsSatPath Φ p z t ∧
        pathLength p = hamming z t := by
  intro fuel
  induction fuel with
  | zero =>
      intro z hz hoff hdist
      have he : z = t := by
        funext u
        by_contra hne
        have hm : u ∈ disagree z t := by simpa [disagree] using hne
        have : 0 < hamming z t := Finset.card_pos.mpr ⟨u, hm⟩
        omega
      subst z
      refine ⟨[t], ?_, ?_, ?_⟩
      · simp [greedyWalk]
      · simp [IsSatPath, IsPathIn, hz]
      · simp [pathLength, hamming, disagree]
  | succ fuel ih =>
      intro z hz hoff hdist
      by_cases he : z = t
      · subst z
        refine ⟨[t], ?_, ?_, ?_⟩
        · simp [greedyWalk]
        · simp [IsSatPath, IsPathIn, hz]
        · simp [pathLength, hamming, disagree]
      · obtain ⟨p, hp, hplen⟩ := H z hz hoff
        obtain ⟨u, hune, husat⟩ := audit_shortest_path_has_move Φ z t p hp hplen he
        let cand := Finset.univ.filter fun u => z u ≠ t u ∧ FSat (flip z u) Φ
        have hnon : cand.Nonempty := ⟨u, by simp [cand, hune, husat]⟩
        let v := cand.min' hnon
        have hvmem : v ∈ cand := Finset.min'_mem cand hnon
        have hv : z v ≠ t v ∧ FSat (flip z v) Φ := by simpa [cand] using hvmem
        have hvU : v ∈ U := by
          by_contra hn
          exact hv.1 ((hoff v hn).trans (ht v hn).symm)
        have hnext : flip z v ∈ sols Φ := by simpa [sols] using hv.2
        have hoffnext : ∀ u, u ∉ U → flip z v u = x u := by
          intro u hu
          have huv : u ≠ v := by intro h; subst u; exact hu hvU
          rw [show flip z v u = z u from Function.update_of_ne huv _ _]
          exact hoff u hu
        have hstep := audit_hamming_flip_toward z t v hv.1
        have hdnext : hamming (flip z v) t ≤ fuel := by omega
        obtain ⟨q, hq, hqpath, hqlen⟩ := ih (flip z v) hnext hoffnext hdnext
        have qne : q ≠ [] := by
          intro hnil
          subst q
          simp [IsSatPath, IsPathIn] at hqpath
        have hqhead : q.head? = some (flip z v) := hqpath.1
        refine ⟨z :: q, ?_, ?_, ?_⟩
        · simp only [greedyWalk, if_neg he]
          change (if h : cand.Nonempty then
            (greedyWalk Φ t fuel (flip z (cand.min' h))).map (z :: ·) else none) = _
          rw [dif_pos hnon]
          change Option.map (z :: ·) (greedyWalk Φ t fuel (flip z v)) = some (z :: q)
          simp [hq]
        · rcases q with _ | ⟨a, qs⟩
          · exact (qne rfl).elim
          · have ha : a = flip z v := by simpa using hqhead
            subst a
            refine ⟨rfl, ?_, ?_, ?_⟩
            · simpa using hqpath.2.1
            · intro w hw
              simp only [List.mem_cons] at hw
              rcases hw with rfl | hw
              · exact hz
              · exact hqpath.2.2.1 w (by simpa using hw)
            · exact List.isChain_cons_cons.mpr ⟨audit_hamming_single_flip z v, hqpath.2.2.2⟩
        · have hqpos : 0 < q.length := List.length_pos_iff.mpr qne
          simp only [pathLength, List.length_cons] at hqlen ⊢
          omega

theorem audit_hamming_symm {n : ℕ} (x y : Fin n → Bool) : hamming x y = hamming y x := by
  simp [hamming, disagree, ne_comm]

/-- The two paths overlap at the target, listed only once. -/
theorem audit_join_paths {n : ℕ} (Φ : GFormula (Fin n))
    (y y' t : Fin n → Bool) (p q : List (Fin n → Bool))
    (hp : IsSatPath Φ p y t) (hq : IsSatPath Φ q y' t) :
    IsSatPath Φ (p ++ q.reverse.tail) y y' ∧
      pathLength (p ++ q.reverse.tail) = pathLength p + pathLength q := by
  obtain ⟨l, hl⟩ := List.getLast?_eq_some_iff.mp hp.2.1
  have hqrev : q.reverse.head? = some t := by simpa using hq.2.1
  obtain ⟨r, hr⟩ := List.head?_eq_some_iff.mp hqrev
  have hrevchain : q.reverse.IsChain (fun a b => hamming a b = 1) := by
    apply List.isChain_reverse.mpr
    exact hq.2.2.2.imp (by intro a b h; simpa [audit_hamming_symm] using h)
  have hchain : (l ++ [t] ++ r).IsChain (fun a b => hamming a b = 1) := by
    apply List.IsChain.append_overlap (l₂ := [t])
    · simpa [hl] using hp.2.2.2
    · simpa [hr] using hrevchain
    · simp
  have htail : q.reverse.tail = r := by rw [hr]; rfl
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩
    · have hpne : p ≠ [] := by intro hh; simp [hh, IsSatPath, IsPathIn] at hp
      simpa [List.head?_append, hpne] using hp.1
    · rw [htail, hl]
      have hlast : (t :: r).getLast? = some y' := by
        rw [← hr]
        simpa using hq.1
      simpa [List.getLast?_append] using hlast
    · intro z hz
      simp only [List.mem_append] at hz
      rcases hz with hz | hz
      · exact hp.2.2.1 z hz
      · apply hq.2.2.1 z
        have : z ∈ q.reverse.tail := by simpa [htail] using hz
        exact List.mem_reverse.mp (List.mem_of_mem_tail this)
    · simpa [hl, htail] using hchain
  · have hpne : 0 < p.length := by
      apply List.length_pos_iff.mpr
      intro hh
      simp [hh, IsSatPath, IsPathIn] at hp
    have hqne : 0 < q.length := by
      apply List.length_pos_iff.mpr
      intro hh
      simp [hh, IsSatPath, IsPathIn] at hq
    simp only [pathLength, List.length_append, List.length_tail, List.length_reverse]
    omega

theorem audit_hamming_le_n {n : ℕ} (x y : Fin n → Bool) : hamming x y ≤ n := by
  simpa [hamming] using Finset.card_le_univ (disagree x y)

end KSATSingleFlip.Connect

open KSATSingleFlip.Connect OAI.FixedClauseThreshold

theorem solution :
    ∀ k : ℕ, 1 ≤ k → ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (Φp : List (ProperClause n k))
      (x : Fin n → Bool) (W U : Finset (Fin n)) (t : Fin n → Bool),
      IsRepair (ofList Φp) x W U t →
      ∀ (I : Finset (Fin (ofList Φp).length)) (y y' : Fin n → Bool),
        y ∈ sols (subF (ofList Φp) I) → y' ∈ sols (subF (ofList Φp) I) →
        (∀ u, u ∉ U → y u = x u) → (∀ u, u ∉ U → y' u = x u) →
          ∃ p, findPath (subF (ofList Φp) I) y y' t = some p ∧
            IsSatPath (subF (ofList Φp) I) p y y' ∧
            pathLength p = hamming y t + hamming y' t ∧
            hamming y t + hamming y' t ≤ 2 * U.card ∧
            (findPathCost n (subF (ofList Φp) I).length p : ℝ) ≤
              C * n * (n + (subF (ofList Φp) I).length) := by
  intro k hk
  refine ⟨8, by norm_num, ?_⟩
  intro n Φp x W U t hrepair I y y' hy hy' hoff hoff'
  let Φ := subF (ofList Φp) I
  have ht := hrepair.2.2.1
  have H : ∀ z, z ∈ sols Φ → (∀ u, u ∉ U → z u = x u) →
      ∃ p, IsSatPath Φ p z t ∧ pathLength p = hamming z t := by
    intro z hz hzo
    exact hrepair.2.2.2 I z hz hzo
  obtain ⟨p, hp, hppath, hplen⟩ :=
    audit_greedy_success Φ x t U ht H n y hy hoff (audit_hamming_le_n y t)
  obtain ⟨q, hq, hqpath, hqlen⟩ :=
    audit_greedy_success Φ x t U ht H n y' hy' hoff' (audit_hamming_le_n y' t)
  obtain ⟨hpath, hlength⟩ := audit_join_paths Φ y y' t p q hppath hqpath
  refine ⟨p ++ q.reverse.tail, ?_, hpath, ?_, ?_, ?_⟩
  · change findPath Φ y y' t = some _
    simp [findPath, hp, hq]
  · rw [hlength, hplen, hqlen]
  · exact audit_findPath_distance_bound U x y y' t hoff hoff' ht
  · by_cases hn : n = 0
    · subst n
      have hempty : Φp = [] := by
        cases Φp with
        | nil => rfl
        | cons c cs =>
          have hc := c.property
          have hz : (Finset.univ.filter fun i : Fin 0 => (c.val i).isSome) = ∅ := by
            ext i
            exact Fin.elim0 i
          rw [hz] at hc
          simp only [Finset.card_empty] at hc
          omega
      have hf : subF (ofList Φp) I = [] := by
        subst Φp
        simp [ofList, subF]
        intro a
        exact Fin.elim0 a
      simp [hf, findPathCost]
    · have hn' : 0 < n := Nat.pos_of_ne_zero hn
      have hne : p ++ q.reverse.tail ≠ [] := by
        intro hh
        have hpempty : p = [] := (List.append_eq_nil_iff.mp hh).1
        have hhead := hppath.1
        simp [hpempty] at hhead
      have hlen : pathLength (p ++ q.reverse.tail) ≤ 2 * n := by
        rw [hlength, hplen, hqlen]
        have h₁ := audit_hamming_le_n y t
        have h₂ := audit_hamming_le_n y' t
        omega
      exact audit_findPath_cost_bound _ hn' hne hlen

