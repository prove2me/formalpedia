-- Prove2me | solution 1 for HyperKCut.Structure.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T15:21:47.731904+00:00
-- url     : https://prove2.me/submissions/dd2c94b2-6472-4c34-ac38-9e1a5104dfec

import Mathlib
import Definitions.Def_HyperKCut_Structure_Model

open HyperKCut.Structure
namespace HKYWZAux

variable {V : Type} [Fintype V] [DecidableEq V]

theorem snoc2_cases {p : ℕ} (Y : Fin p → Finset V) (W Z : Finset V)
    (q : Finset V → Prop) (i : Fin (p + 2))
    (hY : ∀ j, q (Y j)) (hW : q W) (hZ : q Z) :
    q (Fin.snoc (α := fun _ => Finset V) (Fin.snoc (α := fun _ => Finset V) Y W) Z i) := by
  induction i using Fin.lastCases with
  | last => simpa using hZ
  | cast i =>
    rw [Fin.snoc_castSucc]
    induction i using Fin.lastCases with
    | last => simpa using hW
    | cast i => rw [Fin.snoc_castSucc]; exact hY i

/-- Basic facts about a partition `(Y₁,…,Yₚ,W,Z)`. -/
theorem ywz_facts {p : ℕ} (Y : Fin p → Finset V) (W Z : Finset V)
    (h : IsPartitionYWZ Y W Z) :
    (∀ i, (Y i).Nonempty) ∧ W.Nonempty ∧ Z.Nonempty ∧
    (∀ i j, i ≠ j → Disjoint (Y i) (Y j)) ∧
    (∀ i, Disjoint (Y i) W) ∧ (∀ i, Disjoint (Y i) Z) ∧ Disjoint W Z ∧
    (∀ v, (∃ i, v ∈ Y i) ∨ v ∈ W ∨ v ∈ Z) := by
  obtain ⟨hne, hdis, hcov⟩ := h
  have eY : ∀ i, Fin.snoc (α := fun _ => Finset V) (Fin.snoc (α := fun _ => Finset V) Y W) Z
      (Fin.castSucc (Fin.castSucc i)) = Y i := by intro i; simp
  have eW : Fin.snoc (α := fun _ => Finset V) (Fin.snoc (α := fun _ => Finset V) Y W) Z
      (Fin.castSucc (Fin.last p)) = W := by simp
  have eZ : Fin.snoc (α := fun _ => Finset V) (Fin.snoc (α := fun _ => Finset V) Y W) Z
      (Fin.last (p + 1)) = Z := by simp
  refine ⟨fun i => ?_, ?_, ?_, fun i j hij => ?_, fun i => ?_, fun i => ?_, ?_, fun v => ?_⟩
  · have := hne (Fin.castSucc (Fin.castSucc i)); rwa [eY] at this
  · have := hne (Fin.castSucc (Fin.last p)); rwa [eW] at this
  · have := hne (Fin.last (p + 1)); rwa [eZ] at this
  · have := hdis (Fin.castSucc (Fin.castSucc i)) (Fin.castSucc (Fin.castSucc j))
      (fun h => hij (Fin.castSucc_injective _ (Fin.castSucc_injective _ h)))
    rwa [eY, eY] at this
  · have := hdis (Fin.castSucc (Fin.castSucc i)) (Fin.castSucc (Fin.last p))
      (fun h => (Fin.castSucc_lt_last i).ne (Fin.castSucc_injective _ h))
    rwa [eY, eW] at this
  · have := hdis (Fin.castSucc (Fin.castSucc i)) (Fin.last (p + 1))
      (Fin.castSucc_lt_last _).ne
    rwa [eY, eZ] at this
  · have := hdis (Fin.castSucc (Fin.last p)) (Fin.last (p + 1)) (Fin.castSucc_lt_last _).ne
    rwa [eW, eZ] at this
  · obtain ⟨i, hi⟩ := hcov v
    revert hi
    induction i using Fin.lastCases with
    | last => intro hi; right; right; simpa using hi
    | cast i =>
      rw [Fin.snoc_castSucc]
      induction i using Fin.lastCases with
      | last => intro hi; right; left; simpa using hi
      | cast i => rw [Fin.snoc_castSucc]; intro hi; left; exact ⟨i, hi⟩

end HKYWZAux

namespace HKL33Aux

theorem select_half {p : ℕ} (n : Fin p → ℕ) :
    ∀ (m : ℕ) (s : Finset (Fin p)), 2 * m ≤ s.card →
      ∃ t ⊆ s, t.card = m ∧ 2 * (∑ i ∈ t, n i) ≤ ∑ i ∈ s, n i := by
  intro m
  induction m with
  | zero => intro s _; exact ⟨∅, Finset.empty_subset _, by simp, by simp⟩
  | succ m ih =>
    intro s hs
    have hsne : s.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨a, ha, hamax⟩ := Finset.exists_max_image s n hsne
    have hs1 : (s.erase a).card = s.card - 1 := Finset.card_erase_of_mem ha
    have hs1ne : (s.erase a).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨b, hb, hbmax⟩ := Finset.exists_max_image (s.erase a) n hs1ne
    have hs2 : ((s.erase a).erase b).card = s.card - 2 := by
      rw [Finset.card_erase_of_mem hb, hs1]; omega
    obtain ⟨t', ht's, ht'c, ht'sum⟩ := ih ((s.erase a).erase b) (by omega)
    have hbt' : b ∉ t' := fun h => by
      have := ht's h
      simp at this
    refine ⟨insert b t', ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Finset.mem_of_mem_erase hb
      · exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (ht's hx))
    · rw [Finset.card_insert_of_notMem hbt', ht'c]
    · rw [Finset.sum_insert hbt']
      have e1 := Finset.add_sum_erase s n ha
      have e2 := Finset.add_sum_erase (s.erase a) n hb
      have hba : n b ≤ n a := hamax b (Finset.mem_of_mem_erase hb)
      omega

theorem select_half_fin {p : ℕ} (n : Fin p → ℕ) (m : ℕ) (hm : 2 * m ≤ p) :
    ∃ f : Fin m → Fin p, Function.Injective f ∧
      2 * (∑ j, n (f j)) ≤ ∑ i, n i := by
  obtain ⟨t, -, htc, hsum⟩ := select_half n m Finset.univ (by simpa using hm)
  let e : Fin m ≃ t := (t.equivFin.trans (finCongr htc)).symm
  refine ⟨fun j => (e j : Fin p), fun a b hab => e.injective (Subtype.ext hab), ?_⟩
  have : ∑ j, n (e j : Fin p) = ∑ i ∈ t, n i := by
    rw [← Finset.sum_coe_sort t n]
    exact Equiv.sum_comp e (fun x : t => n (x : Fin p))
  rw [this]
  exact hsum

theorem card_filter_eq_sum {V : Type} (E : Multiset (Finset V)) (q : Finset V → Prop)
    [DecidablePred q] :
    (E.filter q).card = (E.map (fun e => if q e then 1 else 0)).sum := by
  induction E using Multiset.induction_on with
  | empty => simp
  | cons a E ih =>
    simp only [Multiset.filter_cons, Multiset.map_cons, Multiset.sum_cons]
    split_ifs <;> simp [ih] <;> omega

theorem msum_fsum {V ι : Type} (E : Multiset (Finset V)) (s : Finset ι)
    (g : ι → Finset V → ℕ) :
    (E.map (fun e => ∑ i ∈ s, g i e)).sum = ∑ i ∈ s, (E.map (g i)).sum := by
  induction E using Multiset.induction_on with
  | empty => simp
  | cons a E ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, ih, Finset.sum_add_distrib]

end HKL33Aux

open HKYWZAux HKL33Aux in
theorem solution {V : Type} [Fintype V] [DecidableEq V] (H : HyperKCut.Structure.Hypergraph V)
    (k p : ℕ)
    (hk : 2 ≤ k) (hp : 2 * k - 2 ≤ p)
    (Y : Fin p → Finset V) (W Z : Finset V)
    (hP : IsPartitionYWZ Y W Z) :
    ∃ f : Fin (k - 1) → Fin p, Function.Injective f ∧
      2 * cost H (Fin.snoc (fun j => Y (f j))
        ((Finset.univ : Finset V) \ Finset.univ.biUnion (fun j : Fin (k - 1) => Y (f j)))) ≤
      costYWZ H Y W Z + alpha H Y W Z + beta H Y Z := by
  classical
  set E := H.edges with hE
  let old : Finset V → Prop := fun e => ∃ i j, i ≠ j ∧
    Meets e (Fin.snoc (α := fun _ => Finset V) (Fin.snoc (α := fun _ => Finset V) Y W) Z i) ∧
    Meets e (Fin.snoc (α := fun _ => Finset V) (Fin.snoc (α := fun _ => Finset V) Y W) Z j)
  let al : Finset V → Prop := fun e => Meets e Z ∧
    (2 ≤ numYMet e Y ∨ (1 ≤ numYMet e Y ∧ Meets e W))
  let be : Finset V → Prop := fun e => ¬ Meets e Z ∧ 2 ≤ numYMet e Y
  let b : Fin p → Finset V → Prop := fun i e => old e ∧ ¬ al e ∧ ¬ be e ∧ Meets e (Y i)
  let n : Fin p → ℕ := fun i => (E.filter (b i)).card
  obtain ⟨f, hfinj, hf⟩ := select_half_fin n (k - 1) (by omega)
  refine ⟨f, hfinj, ?_⟩
  set Rest : Finset V := (Finset.univ : Finset V) \
    Finset.univ.biUnion (fun j : Fin (k - 1) => Y (f j)) with hRest
  set Pf : Fin (k - 1 + 1) → Finset V :=
    Fin.snoc (α := fun _ => Finset V) (fun j => Y (f j)) Rest with hPf
  let new : Finset V → Prop := fun e => ∃ a c, a ≠ c ∧ Meets e (Pf a) ∧ Meets e (Pf c)
  have eY : ∀ i, Fin.snoc (α := fun _ => Finset V) (Fin.snoc (α := fun _ => Finset V) Y W) Z
      (Fin.castSucc (Fin.castSucc i)) = Y i := by intro i; simp
  have eZ : Fin.snoc (α := fun _ => Finset V) (Fin.snoc (α := fun _ => Finset V) Y W) Z
      (Fin.last (p + 1)) = Z := by simp
  -- numYMet as a sum
  have hnum : ∀ e, numYMet e Y = ∑ i, (if Meets e (Y i) then 1 else 0) := by
    intro e
    unfold numYMet
    rw [Finset.card_filter]
  -- F1
  have F1 : ∀ e, al e ∨ be e → old e := by
    intro e h
    rcases h with ⟨hz, h⟩ | ⟨-, h⟩
    · have h1 : 1 ≤ numYMet e Y := by rcases h with h | h <;> omega
      unfold numYMet at h1
      obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ.filter
        fun i => Meets e (Y i)).card)
      rw [Finset.mem_filter] at hi
      refine ⟨Fin.castSucc (Fin.castSucc i), Fin.last (p + 1), (Fin.castSucc_lt_last _).ne,
        ?_, ?_⟩
      · rw [eY]; exact hi.2
      · rw [eZ]; exact hz
    · unfold numYMet at h
      obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < (Finset.univ.filter
        fun i => Meets e (Y i)).card)
      rw [Finset.mem_filter] at hi hj
      refine ⟨Fin.castSucc (Fin.castSucc i), Fin.castSucc (Fin.castSucc j),
        fun h => hij (Fin.castSucc_injective _ (Fin.castSucc_injective _ h)), ?_, ?_⟩
      · rw [eY]; exact hi.2
      · rw [eY]; exact hj.2
  -- F2
  have F2 : ∀ e, ¬ al e → ¬ be e → numYMet e Y ≤ 1 := by
    intro e ha hb
    by_contra h
    push_neg at h
    by_cases hz : Meets e Z
    · exact ha ⟨hz, Or.inl h⟩
    · exact hb ⟨hz, h⟩
  -- F4 and F5
  have hcov := hP.2.2
  have restNot : ∀ v j, v ∈ Rest → v ∉ Y (f j) := by
    intro v j hv hvY
    rw [hRest, Finset.mem_sdiff, Finset.mem_biUnion] at hv
    exact hv.2 ⟨j, Finset.mem_univ _, hvY⟩
  have F45 : ∀ e, new e → old e ∧ ∃ j, Meets e (Y (f j)) := by
    intro e ⟨a, c, hac, ha, hc⟩
    induction a using Fin.lastCases with
    | last =>
      induction c using Fin.lastCases with
      | last => exact absurd rfl hac
      | cast j =>
        rw [hPf, Fin.snoc_last] at ha
        rw [hPf, Fin.snoc_castSucc] at hc
        refine ⟨?_, j, hc⟩
        obtain ⟨x, hx⟩ := ha
        rw [Finset.mem_inter] at hx
        obtain ⟨o, ho⟩ := hcov x
        refine ⟨Fin.castSucc (Fin.castSucc (f j)), o, ?_, ?_, ⟨x, Finset.mem_inter.mpr ⟨hx.1, ho⟩⟩⟩
        · intro h
          rw [← h, eY] at ho
          exact restNot x j hx.2 ho
        · rw [eY]; exact hc
    | cast i =>
      rw [hPf, Fin.snoc_castSucc] at ha
      refine ⟨?_, i, ha⟩
      induction c using Fin.lastCases with
      | last =>
        rw [hPf, Fin.snoc_last] at hc
        obtain ⟨x, hx⟩ := hc
        rw [Finset.mem_inter] at hx
        obtain ⟨o, ho⟩ := hcov x
        refine ⟨Fin.castSucc (Fin.castSucc (f i)), o, ?_, ?_, ⟨x, Finset.mem_inter.mpr ⟨hx.1, ho⟩⟩⟩
        · intro h
          rw [← h, eY] at ho
          exact restNot x i hx.2 ho
        · rw [eY]; exact ha
      | cast j =>
        rw [hPf, Fin.snoc_castSucc] at hc
        have hij : i ≠ j := fun h => hac (by rw [h])
        refine ⟨Fin.castSucc (Fin.castSucc (f i)), Fin.castSucc (Fin.castSucc (f j)),
          fun h => hij (hfinj (Fin.castSucc_injective _ (Fin.castSucc_injective _ h))), ?_, ?_⟩
        · rw [eY]; exact ha
        · rw [eY]; exact hc
  -- per-edge inequality
  have hBle : ∀ e, (∑ i, (if b i e then 1 else 0)) ≤ numYMet e Y := by
    intro e
    calc (∑ i, (if b i e then 1 else 0)) ≤ ∑ i, (if Meets e (Y i) then 1 else 0) := by
          apply Finset.sum_le_sum
          intro i _
          by_cases h : b i e
          · rw [if_pos h, if_pos h.2.2.2]
          · rw [if_neg h]; exact Nat.zero_le _
      _ = numYMet e Y := (hnum e).symm
  have hB0 : ∀ e, ¬ (old e ∧ ¬ al e ∧ ¬ be e) → (∑ i, (if b i e then 1 else 0)) = 0 := by
    intro e h
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg]
    intro hb
    exact h ⟨hb.1, hb.2.1, hb.2.2.1⟩
  have perEdge : ∀ e, 2 * (if new e then 1 else 0) + (∑ i, (if b i e then 1 else 0)) ≤
      (if old e then 1 else 0) + (if al e then 1 else 0) + (if be e then 1 else 0) +
        2 * (∑ j, (if b (f j) e then 1 else 0)) := by
    intro e
    by_cases hab : al e ∨ be e
    · have ho := F1 e hab
      have h0 := hB0 e (fun h => by rcases hab with h' | h' <;> [exact h.2.1 h'; exact h.2.2 h'])
      rw [h0, if_pos ho]
      rcases hab with h' | h'
      · rw [if_pos h']; split_ifs <;> omega
      · rw [if_pos h']; split_ifs <;> omega
    · push_neg at hab
      obtain ⟨hna, hnb⟩ := hab
      rw [if_neg hna, if_neg hnb]
      by_cases ho : old e
      · rw [if_pos ho]
        have h1 := hBle e
        have h2 := F2 e hna hnb
        by_cases hn : new e
        · rw [if_pos hn]
          obtain ⟨-, j, hj⟩ := F45 e hn
          have : 1 ≤ ∑ j, (if b (f j) e then 1 else 0) := by
            have hbj : b (f j) e := ⟨ho, hna, hnb, hj⟩
            calc 1 = (if b (f j) e then 1 else 0) := by rw [if_pos hbj]
              _ ≤ ∑ j, (if b (f j) e then 1 else 0) :=
                Finset.single_le_sum (f := fun j => if b (f j) e then 1 else 0)
                  (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
          omega
        · rw [if_neg hn]; omega
      · have hn : ¬ new e := fun h => ho (F45 e h).1
        rw [if_neg ho, if_neg hn, hB0 e (fun h => ho h.1)]
        omega
  have key := Multiset.sum_map_le_sum_map _ _ (fun e (_ : e ∈ E) => perEdge e)
  simp only [Multiset.sum_map_add, Multiset.sum_map_mul_left] at key
  rw [msum_fsum, msum_fsum] at key
  have c1 : cost H Pf = (E.map (fun e => if new e then 1 else 0)).sum := by
    unfold cost; rw [card_filter_eq_sum]
  have c2 : costYWZ H Y W Z = (E.map (fun e => if old e then 1 else 0)).sum := by
    unfold costYWZ cost; rw [card_filter_eq_sum]
  have c3 : alpha H Y W Z = (E.map (fun e => if al e then 1 else 0)).sum := by
    unfold alpha; rw [card_filter_eq_sum]
  have c4 : beta H Y Z = (E.map (fun e => if be e then 1 else 0)).sum := by
    unfold beta; rw [card_filter_eq_sum]
  have c5 : ∀ i, n i = (E.map (fun e => if b i e then 1 else 0)).sum := by
    intro i; exact card_filter_eq_sum E (b i)
  simp only [← c5] at key
  rw [c1, c2, c3, c4]
  have : 2 * (∑ j, n (f j)) ≤ ∑ i, n i := hf
  omega
