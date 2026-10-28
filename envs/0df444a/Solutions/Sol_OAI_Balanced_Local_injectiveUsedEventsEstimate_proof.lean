-- Prove2me | solution 1 for OAI.Balanced.Local.injectiveUsedEventsEstimate_proof
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:20:47.677913+00:00
-- url     : https://prove2.me/submissions/1d190189-7bb0-4990-b3dc-cd11529d0c17

import Mathlib
import Definitions.Def_OAIQ63Br004

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Construction_RootChildPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.RootChildPartition

open scoped BigOperators

variable {ι α : Type*} [DecidableEq ι] [DecidableEq α]

theorem exists_maximal_roots (A : ι → Finset α) (s : Finset ι) :
    ∃ R ⊆ s, DisjointRoots A R ∧
      ∀ i ∈ s, i ∉ R → (A i ∩ R.biUnion A).Nonempty := by
  classical
  let candidates := s.powerset.filter (DisjointRoots A)
  have hempty : ∅ ∈ candidates := by simp [candidates, DisjointRoots]
  obtain ⟨R, hR, hmax⟩ := Finset.exists_max_image candidates Finset.card ⟨∅, hempty⟩
  obtain ⟨hRs, hdisj⟩ := Finset.mem_filter.mp hR
  have hsub : R ⊆ s := Finset.mem_powerset.mp hRs
  refine ⟨R, hsub, hdisj, ?_⟩
  intro i hi hin
  by_contra hnone
  have hdisjnew : DisjointRoots A (insert i R) := by
    intro j hj k hk hjk
    by_cases hji : j = i
    · subst j
      have hkR : k ∈ R := (Finset.mem_insert.mp hk).resolve_left hjk.symm
      apply Finset.disjoint_left.mpr
      intro a hai hak
      exact hnone ⟨a, Finset.mem_inter.mpr
        ⟨hai, Finset.mem_biUnion.mpr ⟨k, hkR, hak⟩⟩⟩
    · have hjR : j ∈ R := (Finset.mem_insert.mp hj).resolve_left hji
      by_cases hki : k = i
      · subst k
        apply Finset.disjoint_left.mpr
        intro a haj hai
        exact hnone ⟨a, Finset.mem_inter.mpr
          ⟨hai, Finset.mem_biUnion.mpr ⟨j, hjR, haj⟩⟩⟩
      · have hkR : k ∈ R := (Finset.mem_insert.mp hk).resolve_left hki
        exact hdisj j hjR k hkR hjk
  have hnew : insert i R ∈ candidates :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.insert_subset hi hsub), hdisjnew⟩
  have hc := hmax (insert i R) hnew
  rw [Finset.card_insert_of_notMem hin] at hc
  omega

theorem exists_roots_of_small_shared (A : ι → Finset α) (s : Finset ι)
    (hsmall : ∀ i ∈ s, (A i ∩ (s.erase i).biUnion A).card ≤ 1) :
    ∃ R ⊆ s, DisjointRoots A R ∧
      ∀ i ∈ s, i ∉ R →
        (A i ∩ R.biUnion A).card = 1 ∧
        A i ∩ (s.erase i).biUnion A ⊆ R.biUnion A := by
  obtain ⟨R, hRs, hdisj, hmeet⟩ := exists_maximal_roots A s
  refine ⟨R, hRs, hdisj, ?_⟩
  intro i hi hin
  have hRerase : R ⊆ s.erase i := by
    intro j hj
    exact Finset.mem_erase.mpr ⟨fun hji => hin (hji ▸ hj), hRs hj⟩
  have hinter : A i ∩ R.biUnion A ⊆ A i ∩ (s.erase i).biUnion A := by
    apply Finset.inter_subset_inter_left
    exact Finset.biUnion_subset_biUnion_of_subset_left A hRerase
  have hcard : (A i ∩ R.biUnion A).card = 1 := by
    have hpos := Finset.card_pos.mpr (hmeet i hi hin)
    have hle := (Finset.card_le_card hinter).trans (hsmall i hi)
    omega
  refine ⟨hcard, ?_⟩
  obtain ⟨a, ha⟩ := hmeet i hi hin
  intro x hx
  have hxa : x = a := Finset.card_le_one.mp (hsmall i hi) x hx a (hinter ha)
  exact hxa ▸ (Finset.mem_inter.mp ha).2

theorem disjointRoots_of_zero_reuse (A : ι → Finset α) (s : Finset ι)
    (hz : (∑ i ∈ s, (A i).card) - (s.biUnion A).card = 0) :
    DisjointRoots A s := by
  intro i hi j hj hij
  have hd := Balanced.family_reuse_erase A s i hi
  have hc : (A i ∩ (s.erase i).biUnion A).card = 0 := by omega
  have he := Finset.card_eq_zero.mp hc
  apply Finset.disjoint_left.mpr
  intro a hai haj
  have ha : a ∈ A i ∩ (s.erase i).biUnion A :=
    Finset.mem_inter.mpr ⟨hai, Finset.mem_biUnion.mpr
      ⟨j, Finset.mem_erase.mpr ⟨hij.symm, hj⟩, haj⟩⟩
  simp only [he, Finset.notMem_empty] at ha

theorem exists_roots_of_large_shared (A : ι → Finset α) (s : Finset ι)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (A i ∩ A j).card ≤ 1)
    (hr : (∑ i ∈ s, (A i).card) - (s.biUnion A).card ≤ 2)
    (i : ι) (hi : i ∈ s) (hbig : 2 ≤ (A i ∩ (s.erase i).biUnion A).card) :
    ∃ R ⊆ s, DisjointRoots A R ∧
      ∀ j ∈ s, j ∉ R →
        (A j ∩ R.biUnion A).card = 1 ∧
        A j ∩ (s.erase j).biUnion A ⊆ R.biUnion A := by
  classical
  have hd := Balanced.family_reuse_erase A s i hi
  have hz : (∑ j ∈ s.erase i, (A j).card) - ((s.erase i).biUnion A).card = 0 := by
    omega
  have hrest := disjointRoots_of_zero_reuse A (s.erase i) hz
  let R := insert i ((s.erase i).filter fun j => Disjoint (A j) (A i))
  have hiR : i ∈ R := Finset.mem_insert_self _ _
  have hRs : R ⊆ s := by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hi
    · exact (Finset.mem_erase.mp (Finset.mem_filter.mp hj).1).2
  have hroot : DisjointRoots A R := by
    intro j hj k hk hjk
    by_cases hji : j = i
    · subst j
      have hkf := Finset.mem_filter.mp ((Finset.mem_insert.mp hk).resolve_left hjk.symm)
      exact hkf.2.symm
    · have hjf := Finset.mem_filter.mp ((Finset.mem_insert.mp hj).resolve_left hji)
      by_cases hki : k = i
      · subst k
        exact hjf.2
      · have hkf := Finset.mem_filter.mp ((Finset.mem_insert.mp hk).resolve_left hki)
        exact hrest j hjf.1 k hkf.1 hjk
  refine ⟨R, hRs, hroot, ?_⟩
  intro j hj hjR
  have hji : j ≠ i := fun h => hjR (h ▸ hiR)
  have hjrest : j ∈ s.erase i := Finset.mem_erase.mpr ⟨hji, hj⟩
  have hnD : ¬ Disjoint (A j) (A i) := by
    intro hD
    exact hjR (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hjrest, hD⟩))
  have hshared : A j ∩ (s.erase j).biUnion A = A j ∩ A i := by
    ext a
    constructor
    · intro ha
      obtain ⟨haj, har⟩ := Finset.mem_inter.mp ha
      obtain ⟨k, hk, hak⟩ := Finset.mem_biUnion.mp har
      by_cases hki : k = i
      · exact Finset.mem_inter.mpr ⟨haj, hki ▸ hak⟩
      · have hkrest : k ∈ s.erase i :=
          Finset.mem_erase.mpr ⟨hki, (Finset.mem_erase.mp hk).2⟩
        exact (Finset.disjoint_left.mp
          (hrest j hjrest k hkrest (Finset.mem_erase.mp hk).1.symm) haj hak).elim
    · intro ha
      obtain ⟨haj, hai⟩ := Finset.mem_inter.mp ha
      exact Finset.mem_inter.mpr ⟨haj, Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_erase.mpr ⟨hji.symm, hi⟩, hai⟩⟩
  have hsharedRoots : A j ∩ (s.erase j).biUnion A ⊆ R.biUnion A := by
    rw [hshared]
    intro a ha
    exact Finset.mem_biUnion.mpr ⟨i, hiR, (Finset.mem_inter.mp ha).2⟩
  refine ⟨?_, hsharedRoots⟩
  have hRerase : R ⊆ s.erase j := by
    intro k hk
    exact Finset.mem_erase.mpr ⟨fun h => hjR (h ▸ hk), hRs hk⟩
  have hinter : A j ∩ R.biUnion A ⊆ A j ∩ A i := by
    rw [← hshared]
    apply Finset.inter_subset_inter_left
    exact Finset.biUnion_subset_biUnion_of_subset_left A hRerase
  have hle := (Finset.card_le_card hinter).trans (hpair j hj i hi hji)
  have hnon : (A j ∩ A i).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    exact hnD (Finset.disjoint_iff_inter_eq_empty.mpr he)
  obtain ⟨a, ha⟩ := hnon
  obtain ⟨haj, hai⟩ := Finset.mem_inter.mp ha
  have hpos : 0 < (A j ∩ R.biUnion A).card :=
    Finset.card_pos.mpr ⟨a, Finset.mem_inter.mpr
      ⟨haj, Finset.mem_biUnion.mpr ⟨i, hiR, hai⟩⟩⟩
  omega

theorem exists_root_child_partition (A : ι → Finset α) (s : Finset ι)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (A i ∩ A j).card ≤ 1)
    (hr : (∑ i ∈ s, (A i).card) - (s.biUnion A).card ≤ 2) :
    ∃ R ⊆ s, DisjointRoots A R ∧
      ∀ i ∈ s, i ∉ R →
        (A i ∩ R.biUnion A).card = 1 ∧
        A i ∩ (s.erase i).biUnion A ⊆ R.biUnion A := by
  by_cases hbig : ∃ i ∈ s, 2 ≤ (A i ∩ (s.erase i).biUnion A).card
  · obtain ⟨i, hi, hbig⟩ := hbig
    exact exists_roots_of_large_shared A s hpair hr i hi hbig
  · apply exists_roots_of_small_shared A s
    intro i hi
    have hn : ¬ 2 ≤ (A i ∩ (s.erase i).biUnion A).card := fun h => hbig ⟨i, hi, h⟩
    omega

theorem exists_pattern_roots {b κ : ℕ} (P : Local.EqualityPattern b κ)
    (hκ : κ ≤ 2) :
    ∃ R : Finset (Fin b),
      DisjointRoots (fun i => Finset.univ.image (P.classOf i)) R ∧
      ∀ i, i ∉ R →
        ((Finset.univ.image (P.classOf i)) ∩
          R.biUnion (fun j => Finset.univ.image (P.classOf j))).card = 1 ∧
        (Finset.univ.image (P.classOf i)) ∩
          (Finset.univ.erase i).biUnion (fun j => Finset.univ.image (P.classOf j)) ⊆
          R.biUnion (fun j => Finset.univ.image (P.classOf j)) := by
  let A : Fin b → Finset (Fin (4 * b - κ)) := fun i => Finset.univ.image (P.classOf i)
  have hcard (i : Fin b) : (A i).card = 4 := by
    dsimp only [A]
    rw [Finset.card_image_of_injective _ (P.withinTuple i)]
    simp
  have hUnion : Finset.univ.biUnion A = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro c
    obtain ⟨⟨i, j⟩, h⟩ := P.everyClass c
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
      Finset.mem_image.mpr ⟨j, Finset.mem_univ _, h⟩⟩
  have hreuse : (∑ i : Fin b, (A i).card) - (Finset.univ.biUnion A).card ≤ 2 := by
    simp only [hcard, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, hUnion]
    omega
  obtain ⟨R, hRs, hroots, hchildren⟩ := exists_root_child_partition A Finset.univ
    (fun i _ j _ hij => P.pairOverlap i j hij) hreuse
  exact ⟨R, hroots, fun i hin => hchildren i (Finset.mem_univ _) hin⟩

end Balanced.RootChildPartition

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_AffineDirectionCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

variable {F : Type*} [Field F]

theorem direction_eq_of_common_point (p r : Point F) (hne : p ≠ r)
    (d e : Direction F) (hd : OnLine r (lineThrough d p))
    (he : OnLine r (lineThrough e p)) : d = e := by
  have h := eq_of_two_common_points p r hne (lineThrough d p) (lineThrough e p)
    (onLine_lineThrough d p) hd (onLine_lineThrough e p) he
  exact congrArg Prod.fst h

variable [DecidableEq F]

variable [Fintype F]

theorem card_directions_meeting_pair_away_le_one
    (D : Finset (Direction F)) (p : Point F) (l m : Line F) (hne : l ≠ m) :
    (D.filter (fun d => ∃ x : Point F, x ≠ p ∧ OnLine x l ∧
      OnLine x m ∧ OnLine x (lineThrough d p))).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro d hd e he
  obtain ⟨x, hxp, hxl, hxm, hxd⟩ := (Finset.mem_filter.mp hd).2
  obtain ⟨y, hyp, hyl, hym, hye⟩ := (Finset.mem_filter.mp he).2
  have hxy : x = y := common_point_eq_of_lines_ne l m hne x y hxl hxm hyl hym
  subst y
  exact direction_eq_of_common_point p x (Ne.symm hxp) d e hxd hye

theorem card_projection_directions_le_one
    (D : Finset (Direction F)) (p : Point F) (l m : Line F) (hne : l ≠ m) :
    (D.filter (fun d => d ≠ l.1 ∧
      lineIntersection l (lineThrough d p) ≠ p ∧
      OnLine (lineIntersection l (lineThrough d p)) m)).card ≤ 1 := by
  classical
  apply le_trans (Finset.card_le_card ?_)
    (card_directions_meeting_pair_away_le_one D p l m hne)
  intro d hd
  obtain ⟨hdD, hdir, haway, hm⟩ := Finset.mem_filter.mp hd
  refine Finset.mem_filter.mpr ⟨hdD, lineIntersection l (lineThrough d p),
    haway, ?_, hm, ?_⟩
  · exact onLine_lineIntersection_left l (lineThrough d p) (Ne.symm hdir)
  · exact onLine_lineIntersection_right l (lineThrough d p) (Ne.symm hdir)

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_InjectionExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.InjectionExposure

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem value_mem_remaining (K : Finset I) (base e : I ↪ J)
    (he : e ∈ completions K base) (i : I) (hi : i ∉ K) :
    e i ∈ remaining K base := by
  rw [mem_remaining]
  intro h
  obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp h
  have hsame : e j = e i := (mem_completions K base e).mp he j hj |>.trans hji
  exact hi (e.injective hsame ▸ hj)

theorem base_mem_remaining (K : Finset I) (base : I ↪ J)
    (i : I) (hi : i ∉ K) : base i ∈ remaining K base :=
  value_mem_remaining K base base (by simp) i hi

omit [Fintype I] [DecidableEq I] in
theorem card_remaining (K : Finset I) (base : I ↪ J) :
    (remaining K base).card = Fintype.card J - K.card := by
  rw [remaining, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
    Finset.card_image_of_injective _ base.injective]

theorem swap_mem_completions (K : Finset I) (base e : I ↪ J)
    (he : e ∈ completions K base) (a b : J)
    (ha : a ∈ remaining K base) (hb : b ∈ remaining K base) :
    e.trans (Equiv.swap a b).toEmbedding ∈ completions K base := by
  rw [mem_completions] at he ⊢
  intro j hj
  change Equiv.swap a b (e j) = base j
  rw [he j hj]
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h
    exact (mem_remaining K base a).mp ha (Finset.mem_image.mpr ⟨j, hj, h⟩)
  · intro h
    exact (mem_remaining K base b).mp hb (Finset.mem_image.mpr ⟨j, hj, h⟩)

theorem fibre_card_eq (K : Finset I) (base : I ↪ J) (i : I)
    (a b : J) (ha : a ∈ remaining K base) (hb : b ∈ remaining K base) :
    ((completions K base).filter (fun e => e i = a)).card =
      ((completions K base).filter (fun e => e i = b)).card := by
  let swapOutput : (I ↪ J) → (I ↪ J) :=
    fun e => e.trans (Equiv.swap a b).toEmbedding
  have hinv (e : I ↪ J) : swapOutput (swapOutput e) = e := by
    ext j
    exact Equiv.swap_apply_self a b (e j)
  have hmap (e : I ↪ J)
      (he : e ∈ (completions K base).filter (fun e => e i = a)) :
      swapOutput e ∈ (completions K base).filter (fun e => e i = b) := by
    obtain ⟨he, hei⟩ := Finset.mem_filter.mp he
    refine Finset.mem_filter.mpr ⟨swap_mem_completions K base e he a b ha hb, ?_⟩
    change Equiv.swap a b (e i) = b
    rw [hei, Equiv.swap_apply_left]
  have hmap' (e : I ↪ J)
      (he : e ∈ (completions K base).filter (fun e => e i = b)) :
      swapOutput e ∈ (completions K base).filter (fun e => e i = a) := by
    obtain ⟨he, hei⟩ := Finset.mem_filter.mp he
    refine Finset.mem_filter.mpr ⟨swap_mem_completions K base e he a b ha hb, ?_⟩
    change Equiv.swap a b (e i) = a
    rw [hei, Equiv.swap_apply_right]
  exact Finset.card_bij' (fun e _ => swapOutput e) (fun e _ => swapOutput e)
    hmap hmap' (fun e _ => hinv e) (fun e _ => hinv e)

theorem card_completions_eq (K : Finset I) (base : I ↪ J)
    (i : I) (hi : i ∉ K) (a : J) (ha : a ∈ remaining K base) :
    (completions K base).card = (remaining K base).card *
      ((completions K base).filter (fun e => e i = a)).card := by
  calc
    (completions K base).card =
        ∑ b ∈ remaining K base,
          ((completions K base).filter (fun e => e i = b)).card :=
      Finset.card_eq_sum_card_fiberwise (fun e he =>
        value_mem_remaining K base e he i hi)
    _ = ∑ _b ∈ remaining K base,
          ((completions K base).filter (fun e => e i = a)).card := by
      apply Finset.sum_congr rfl
      intro b hb
      exact fibre_card_eq K base i b a hb ha
    _ = _ := by simp

theorem event_card_eq (K : Finset I) (base : I ↪ J) (i : I) (hi : i ∉ K)
    (P : J → Prop) [DecidablePred P] :
    ((completions K base).filter (fun e => P (e i))).card =
      ((remaining K base).filter P).card *
        ((completions K base).filter (fun e => e i = base i)).card := by
  calc
    ((completions K base).filter (fun e => P (e i))).card =
        ∑ b ∈ (remaining K base).filter P,
          (((completions K base).filter (fun e => P (e i))).filter
            (fun e => e i = b)).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro e he
      obtain ⟨he, hPe⟩ := Finset.mem_filter.mp he
      exact Finset.mem_filter.mpr ⟨value_mem_remaining K base e he i hi, hPe⟩
    _ = ∑ _b ∈ (remaining K base).filter P,
        ((completions K base).filter (fun e => e i = base i)).card := by
      apply Finset.sum_congr rfl
      intro b hb
      obtain ⟨hb, hPb⟩ := Finset.mem_filter.mp hb
      have hfibre : ((completions K base).filter (fun e => P (e i))).filter
          (fun e => e i = b) = (completions K base).filter (fun e => e i = b) := by
        ext e
        simp only [Finset.mem_filter]
        constructor
        · exact fun h => ⟨h.1.1, h.2⟩
        · intro h
          exact ⟨⟨h.1, h.2 ▸ hPb⟩, h.2⟩
      rw [hfibre]
      exact fibre_card_eq K base i b (base i) hb (base_mem_remaining K base i hi)
    _ = _ := by simp

theorem next_event_probability (K : Finset I) (base : I ↪ J)
    (i : I) (hi : i ∉ K) (P : J → Prop) [DecidablePred P] :
    ((PMF.uniformOfFinset (completions K base) (completions_nonempty K base)).toOuterMeasure
      {e | P (e i)}).toReal =
        (((remaining K base).filter P).card : ℝ) / ((remaining K base).card : ℝ) := by
  classical
  have hC : 0 < ((completions K base).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (completions_nonempty K base)
  have hR : 0 < ((remaining K base).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr
      (show (remaining K base).Nonempty from ⟨base i, base_mem_remaining K base i hi⟩)
  have hfactor : ((completions K base).card : ℝ) =
      ((remaining K base).card : ℝ) *
        (((completions K base).filter (fun e => e i = base i)).card : ℝ) := by
    exact_mod_cast card_completions_eq K base i hi (base i) (base_mem_remaining K base i hi)
  have hevent : (((completions K base).filter (fun e => P (e i))).card : ℝ) =
      (((remaining K base).filter P).card : ℝ) *
        (((completions K base).filter (fun e => e i = base i)).card : ℝ) := by
    exact_mod_cast event_card_eq K base i hi P
  rw [PMF.toOuterMeasure_uniformOfFinset_apply]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, Set.mem_ofPred_eq]
  apply (div_eq_div_iff (ne_of_gt hC) (ne_of_gt hR)).mpr
  rw [hfactor, hevent]
  ring

end Balanced.InjectionExposure

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_InjectionAuxiliaryExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.InjectionExposure

variable {I J Z : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem auxiliaryLaw_reveal_last (K : Finset I) (base : I ↪ J)
    (noise : (I ↪ J) → PMF Z) (hnoise : DependsOnExposed K noise) :
    auxiliaryLaw K base noise =
      (noise base).bind (fun z =>
        (PMF.uniformOfFinset (completions K base) (completions_nonempty K base)).map
          (fun e => (e, z))) := by
  classical
  let p := PMF.uniformOfFinset (completions K base) (completions_nonempty K base)
  have hconstant : auxiliaryLaw K base noise =
      p.bind (fun e => (noise base).map (fun z => (e, z))) := by
    ext x
    simp only [auxiliaryLaw, PMF.bind_apply]
    apply tsum_congr
    intro e
    by_cases he : e ∈ completions K base
    · rw [hnoise e base ((mem_completions K base e).mp he)]
    · simp [p, PMF.uniformOfFinset_apply, he]
  rw [hconstant]
  simpa only [PMF.map, Function.comp_def] using
    PMF.bind_comm p (noise base) (fun e z => PMF.pure (e, z))

variable [Fintype Z]

theorem auxiliary_next_event_probability (K : Finset I) (base : I ↪ J)
    (noise : (I ↪ J) → PMF Z) (hnoise : DependsOnExposed K noise)
    (i : I) (hi : i ∉ K) (P : Z → J → Prop) [∀ z, DecidablePred (P z)] :
    ((auxiliaryLaw K base noise).toOuterMeasure {x | P x.2 (x.1 i)}).toReal =
      ∑ z, (noise base z).toReal *
        ((((remaining K base).filter (P z)).card : ℝ) /
          ((remaining K base).card : ℝ)) := by
  classical
  rw [auxiliaryLaw_reveal_last K base noise hnoise,
    PMF.toOuterMeasure_bind_apply, tsum_fintype]
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro z _
    rw [ENNReal.toReal_mul, PMF.toOuterMeasure_map_apply]
    change (noise base z).toReal *
      ((PMF.uniformOfFinset (completions K base) (completions_nonempty K base)).toOuterMeasure
        {e | P z (e i)}).toReal = _
    rw [next_event_probability K base i hi (P z)]
  · intro z _
    apply ENNReal.mul_ne_top ((noise base).apply_ne_top z)
    rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply]
    exact PMF.tsum_coe_indicator_ne_top _ _

theorem auxiliary_next_event_probability_le (K : Finset I) (base : I ↪ J)
    (noise : (I ↪ J) → PMF Z) (hnoise : DependsOnExposed K noise)
    (i : I) (hi : i ∉ K) (P : Z → J → Prop) [∀ z, DecidablePred (P z)]
    (hP : ∀ z, ((remaining K base).filter (P z)).card ≤ 1) :
    ((auxiliaryLaw K base noise).toOuterMeasure {x | P x.2 (x.1 i)}).toReal ≤
      1 / ((remaining K base).card : ℝ) := by
  rw [auxiliary_next_event_probability K base noise hnoise i hi P]
  have hsum : ∑ z, (noise base z).toReal = 1 := by
    have hs : (∑ z : Z, noise base z) = 1 := by
      simpa only [tsum_fintype] using (noise base).tsum_coe
    rw [← ENNReal.toReal_sum (fun z _ => (noise base).apply_ne_top z), hs]
    simp
  calc
    (∑ z, (noise base z).toReal *
        ((((remaining K base).filter (P z)).card : ℝ) /
          ((remaining K base).card : ℝ))) ≤
        ∑ z, (noise base z).toReal * (1 / ((remaining K base).card : ℝ)) := by
      apply Finset.sum_le_sum
      intro z _
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      exact div_le_div_of_nonneg_right (by exact_mod_cast hP z) (Nat.cast_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, hsum, one_mul]

end Balanced.InjectionExposure

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_AffineInjectionGuards
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

variable {F I Z : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype I] [DecidableEq I] [Fintype Z]

theorem auxiliary_guarded_joining_probability_le
    (K : Finset I) (base : I ↪ Direction F) (i : I) (hi : i ∉ K)
    (noise : (I ↪ Direction F) → PMF Z)
    (hnoise : InjectionExposure.DependsOnExposed K noise)
    (p r : Z → Point F) :
    ((InjectionExposure.auxiliaryLaw K base noise).toOuterMeasure
      {x | p x.2 ≠ r x.2 ∧ OnLine (r x.2) (lineThrough (x.1 i) (p x.2))}).toReal ≤
      1 / ((Fintype.card F + 1 - K.card : ℕ) : ℝ) := by
  classical
  have h := InjectionExposure.auxiliary_next_event_probability_le K base noise hnoise i hi
    (fun z d => p z ≠ r z ∧ OnLine (r z) (lineThrough d (p z))) (by
      intro z
      apply Finset.card_le_one.mpr
      intro d hd e he
      obtain ⟨_, hp, hd⟩ := Finset.mem_filter.mp hd
      obtain ⟨_, _, he⟩ := Finset.mem_filter.mp he
      exact direction_eq_of_common_point (p z) (r z) hp d e hd he)
  simpa only [InjectionExposure.card_remaining, Direction, Fintype.card_option] using h

theorem auxiliary_guarded_projection_probability_le
    (K : Finset I) (base : I ↪ Direction F) (i : I) (hi : i ∉ K)
    (noise : (I ↪ Direction F) → PMF Z)
    (hnoise : InjectionExposure.DependsOnExposed K noise)
    (p : Z → Point F) (l m : Z → Line F) :
    ((InjectionExposure.auxiliaryLaw K base noise).toOuterMeasure
      {x | l x.2 ≠ m x.2 ∧ x.1 i ≠ (l x.2).1 ∧
        lineIntersection (l x.2) (lineThrough (x.1 i) (p x.2)) ≠ p x.2 ∧
        OnLine (lineIntersection (l x.2) (lineThrough (x.1 i) (p x.2))) (m x.2)}).toReal ≤
      1 / ((Fintype.card F + 1 - K.card : ℕ) : ℝ) := by
  classical
  have h := InjectionExposure.auxiliary_next_event_probability_le K base noise hnoise i hi
    (fun z d => l z ≠ m z ∧ d ≠ (l z).1 ∧
      lineIntersection (l z) (lineThrough d (p z)) ≠ p z ∧
      OnLine (lineIntersection (l z) (lineThrough d (p z))) (m z)) (by
      intro z
      by_cases hne : l z = m z
      · simp [hne]
      · apply le_trans (Finset.card_le_card ?_)
          (card_projection_directions_le_one (InjectionExposure.remaining K base)
            (p z) (l z) (m z) hne)
        intro d hd
        exact Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hd).1, (Finset.mem_filter.mp hd).2.2⟩)
  simpa only [InjectionExposure.card_remaining, Direction, Fintype.card_option] using h

theorem inverse_token_budget_le_two_div (q b : ℕ) (hq : 0 < q) (hb : 10 * b ≤ q) :
    (1 : ℝ) / ((q + 1 - 5 * b : ℕ) : ℝ) ≤ 2 / (q : ℝ) := by
  have hd : 0 < q + 1 - 5 * b := by omega
  have hnum : q ≤ 2 * (q + 1 - 5 * b) := by omega
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hdr : (0 : ℝ) < (q + 1 - 5 * b : ℕ) := by exact_mod_cast hd
  apply (div_le_div_iff₀ hdr hqr).mpr
  simpa only [one_mul, Nat.cast_mul, Nat.cast_ofNat] using
    (show (q : ℝ) ≤ ((2 * (q + 1 - 5 * b) : ℕ) : ℝ) by exact_mod_cast hnum)

theorem inverse_remaining_le_two_div (q k b : ℕ) (hq : 0 < q)
    (hk : k ≤ 5 * b) (hb : 10 * b ≤ q) :
    (1 : ℝ) / ((q + 1 - k : ℕ) : ℝ) ≤ 2 / (q : ℝ) := by
  apply le_trans _ (inverse_token_budget_le_two_div q b hq hb)
  apply one_div_le_one_div_of_le
  · have hd : 0 < q + 1 - 5 * b := by omega
    exact_mod_cast hd
  · exact_mod_cast Nat.sub_le_sub_left hk (q + 1)

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_AlignedFreeCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.AlignedListProbability

open TupleAlignment PartialAlignment
noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in

theorem alignedPartial_position_old_left (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : ∀ i, d i ≠ g) (c : F)
    (J : Finset (Fin 4)) (a : Fin 4 → Bool → F)
    (o : AlignedPartialOffsets d hd σ g c J a) (i : Fin 4) (hi : i ∈ J) :
    tuplePositionEquiv d hd σ o.1.1 i =
      (lineEvalEquiv (d i) g (hg i)).symm (a i (σ i), c) := by
  apply (lineEvalEquiv (d i) g (hg i)).injective
  rw [Equiv.apply_symm_apply]
  apply Prod.ext
  · change lineEval (d i) (tuplePositionEquiv d hd σ o.1.1 i) = a i (σ i)
    rw [tuplePosition_lineEval_left, o.1.2 i hi]
  · exact o.2 i

omit [Fintype F] [DecidableEq F] in

theorem alignedPartial_position_old_right (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : ∀ i, d i ≠ g) (c : F)
    (J : Finset (Fin 4)) (a : Fin 4 → Bool → F)
    (o : AlignedPartialOffsets d hd σ g c J a) (i : Fin 4) (hi : i + 1 ∈ J) :
    tuplePositionEquiv d hd σ o.1.1 i =
      (lineEvalEquiv (d (i+1)) g (hg (i+1))).symm (a (i+1) (!(σ (i+1))), c) := by
  apply (lineEvalEquiv (d (i+1)) g (hg (i+1))).injective
  rw [Equiv.apply_symm_apply]
  apply Prod.ext
  · change lineEval (d (i+1)) (tuplePositionEquiv d hd σ o.1.1 i) = a (i+1) (!(σ (i+1)))
    rw [tuplePosition_lineEval_right, o.1.2 (i+1) hi]
  · exact o.2 i

end
end Balanced.AlignedListProbability

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_EqualityPatternOrdering
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.EqualityPattern

open Finset

theorem classSet_reuse_eq {b κ : ℕ} (P : EqualityPattern b κ) (hκ : κ ≤ 4 * b) :
    (∑ i : Fin b, (P.classSet i).card) -
      (Finset.univ.biUnion P.classSet).card = κ := by
  rw [P.sum_card_classSet, P.card_biUnion_classSet]
  omega

end Balanced.Local.EqualityPattern

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_UniformConditionalProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.UniformConditionalProduct

open TupleAlignment

noncomputable section
attribute [local instance] Classical.propDecidable

theorem uniform_product_eq_bind {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] :
    PMF.uniformOfFintype (A × B) =
      (PMF.uniformOfFintype A).bind (fun a =>
        (PMF.uniformOfFintype B).map (fun b => (a, b))) := by
  classical
  ext z
  rcases z with ⟨a, b⟩
  simp [PMF.bind_apply, PMF.map_apply, PMF.uniformOfFintype_apply,
    tsum_fintype, Fintype.card_prod, Nat.cast_mul, ENNReal.mul_inv,
    ite_and]

end
end Balanced.UniformConditionalProduct

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_AlignedUnusedLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.AlignedUnused

open UniformConditionalProduct
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem conditionedOffsetProbability_eq_alignedLaw {b κ : ℕ}
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b) (p : Point F)
    (E : MergedPairs F → Prop) :
    conditionedOffsetProbability (Aligned P a bits p) E =
      ((alignedLaw P hκ a ha bits p).toOuterMeasure {M | E M}).toReal := by
  let A : MergedPairs F → Prop := Aligned P a bits p
  let : Nonempty {M : MergedPairs F // A M} := by
    obtain ⟨M, hM, _⟩ := alignment_supported P hκ a ha bits p
    exact ⟨⟨M, hM⟩⟩
  let : Nonempty ({M : MergedPairs F | A M} : Set (MergedPairs F)) := by
    obtain ⟨M, hM, _⟩ := alignment_supported P hκ a ha bits p
    exact ⟨⟨M, hM⟩⟩
  have hcard (H : MergedPairs F → Prop) :
      offsetProbability H = (Fintype.card {M // H M} : ℝ) / Fintype.card (MergedPairs F) := by
    unfold offsetProbability
    rw [← FiniteUniformFibers.probability_eq_sum H,
      PMF.toOuterMeasure_uniformOfFintype_apply, ENNReal.toReal_div]
    simp [Fintype.card_subtype]
  have hnum : Fintype.card {M : {M : MergedPairs F // A M} // E M} =
      Fintype.card {M : MergedPairs F // A M ∧ E M} :=
    Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter A E)
  change offsetProbability (fun M => A M ∧ E M) / offsetProbability A = _
  rw [hcard, hcard]
  change _ = (((PMF.uniformOfFintype (MergedPairs F)).filter {M | A M}
    (alignment_supported P hκ a ha bits p)).toOuterMeasure {M | E M}).toReal
  rw [Balanced.uniform_filter_eq_subtype_map, PMF.toOuterMeasure_map_apply,
    PMF.toOuterMeasure_uniformOfFintype_apply, ENNReal.toReal_div]
  simp only [ENNReal.toReal_natCast, Set.mem_ofPred_eq]
  change _ = (Fintype.card {M : {M : MergedPairs F // A M} // E M} : ℝ) /
    Fintype.card {M : MergedPairs F // A M}
  rw [hnum]
  have htotal : (Fintype.card (MergedPairs F) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp
  have hcardinst (f g : Fintype {M : MergedPairs F // A M ∧ E M}) :
      @Fintype.card _ f = @Fintype.card _ g := by
    cases Subsingleton.elim f g
    rfl
  exact congrArg (Nat.cast : ℕ → ℝ) (hcardinst _ _)

end
end Balanced.Local.AlignedUnused

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_RootChildCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.RootChildPartition

open scoped BigOperators
variable {ι α : Type*} [DecidableEq ι] [DecidableEq α]

omit [DecidableEq ι] in

theorem reuse_roots_eq_zero (A : ι → Finset α) (R : Finset ι)
    (hroots : DisjointRoots A R) :
    (∑ i ∈ R, (A i).card) - (R.biUnion A).card = 0 := by
  have hc : (R.biUnion A).card = ∑ i ∈ R, (A i).card :=
    Finset.card_biUnion (by intro i hi j hj hij; exact hroots i hi j hj hij)
  rw [hc, Nat.sub_self]

theorem child_overlap_intermediate (A : ι → Finset α) (s R t : Finset ι)
    (hchildren : ∀ i ∈ s, i ∉ R →
      (A i ∩ R.biUnion A).card = 1 ∧
      A i ∩ (s.erase i).biUnion A ⊆ R.biUnion A)
    (i : ι) (hi : i ∈ s) (hin : i ∉ R)
    (hRt : R ⊆ t) (ht : t ⊆ s.erase i) :
    (A i ∩ t.biUnion A).card = 1 := by
  obtain ⟨hc, hs⟩ := hchildren i hi hin
  have he : A i ∩ t.biUnion A = A i ∩ R.biUnion A := by
    apply Finset.Subset.antisymm
    · intro a ha
      obtain ⟨hai, hat⟩ := Finset.mem_inter.mp ha
      have har : a ∈ (s.erase i).biUnion A :=
        Finset.biUnion_subset_biUnion_of_subset_left A ht hat
      exact Finset.mem_inter.mpr ⟨hai, hs (Finset.mem_inter.mpr ⟨hai, har⟩)⟩
    · apply Finset.inter_subset_inter_left
      exact Finset.biUnion_subset_biUnion_of_subset_left A hRt
  rw [he, hc]

theorem child_card_eq_reuse (A : ι → Finset α) (s R : Finset ι)
    (hRs : R ⊆ s) (hroots : DisjointRoots A R)
    (hchildren : ∀ i ∈ s, i ∉ R →
      (A i ∩ R.biUnion A).card = 1 ∧
      A i ∩ (s.erase i).biUnion A ⊆ R.biUnion A) :
    (s \ R).card = (∑ i ∈ s, (A i).card) - (s.biUnion A).card := by
  have hcount (t : Finset ι) (ht : t ⊆ s \ R) :
      (∑ i ∈ R ∪ t, (A i).card) - ((R ∪ t).biUnion A).card = t.card := by
    induction t using Finset.induction_on with
    | empty => simpa using reuse_roots_eq_zero A R hroots
    | @insert i t hin ih =>
      have his : i ∈ s := (Finset.mem_sdiff.mp (ht (Finset.mem_insert_self _ _))).1
      have hinR : i ∉ R := (Finset.mem_sdiff.mp (ht (Finset.mem_insert_self _ _))).2
      have hts : t ⊆ s \ R := fun j hj => ht (Finset.mem_insert_of_mem hj)
      have hnot : i ∉ R ∪ t := by simp [hinR, hin]
      have hsub : R ∪ t ⊆ s.erase i := by
        intro j hj
        rcases Finset.mem_union.mp hj with hjR | hjt
        · exact Finset.mem_erase.mpr ⟨fun h => hinR (h ▸ hjR), hRs hjR⟩
        · exact Finset.mem_erase.mpr ⟨fun h => hin (h ▸ hjt),
            (Finset.mem_sdiff.mp (hts hjt)).1⟩
      have hoverlap := child_overlap_intermediate A s R (R ∪ t)
        hchildren i his hinR Finset.subset_union_left hsub
      rw [Finset.union_insert, Balanced.family_reuse_insert A (R ∪ t) i hnot,
        ih hts, hoverlap, Finset.card_insert_of_notMem hin]
  have h := hcount (s \ R) (fun _ h => h)
  rw [Finset.union_sdiff_of_subset hRs] at h
  exact h.symm

theorem exists_pattern_roots_exact {b κ : ℕ} (P : Local.EqualityPattern b κ)
    (hκ : κ ≤ 2) (hfit : κ ≤ 4 * b) :
    ∃ R : Finset (Fin b), DisjointRoots P.classSet R ∧
      (Finset.univ \ R).card = κ ∧
      ∀ i, i ∉ R →
        (P.classSet i ∩ R.biUnion P.classSet).card = 1 ∧
        P.classSet i ∩ (Finset.univ.erase i).biUnion P.classSet ⊆
          R.biUnion P.classSet := by
  obtain ⟨R, hroots, hchildren⟩ := exists_pattern_roots P hκ
  have hc := child_card_eq_reuse P.classSet Finset.univ R (Finset.subset_univ _)
    hroots (fun i _ hin => hchildren i hin)
  rw [P.classSet_reuse_eq hfit] at hc
  exact ⟨R, hroots, hc, hchildren⟩

theorem exists_pattern_roots_exact_of_three_le {b κ : ℕ}
    (P : Local.EqualityPattern b κ) (hb : 3 ≤ b) (hκ : κ ≤ 2) :
    ∃ R : Finset (Fin b), DisjointRoots P.classSet R ∧
      (Finset.univ \ R).card = κ ∧
      ∀ i, i ∉ R →
        (P.classSet i ∩ R.biUnion P.classSet).card = 1 ∧
        P.classSet i ∩ (Finset.univ.erase i).biUnion P.classSet ⊆
          R.biUnion P.classSet :=
  exists_pattern_roots_exact P hκ (by omega)

end Balanced.RootChildPartition

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_RootChildDependence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.RootChildPartition

open scoped BigOperators

theorem card_touchedPositions_of_card_le_one (J : Finset (Fin 4)) (hJ : J.card ≤ 1) :
    (touchedPositions J).card = 2 * J.card := by
  have h : ∀ K : Finset (Fin 4), K.card ≤ 1 →
      (touchedPositions K).card = 2 * K.card := by decide
  exact h J hJ

theorem card_rootGeneratorIndices {b κ : ℕ} (P : Local.EqualityPattern b κ)
    (R : Finset (Fin b)) (i : Fin b) :
    (rootGeneratorIndices P R i).card = (P.classSet i ∩ R.biUnion P.classSet).card := by
  have he : (rootGeneratorIndices P R i).image (P.classOf i) =
      P.classSet i ∩ R.biUnion P.classSet := by
    ext a
    simp only [rootGeneratorIndices, Local.EqualityPattern.classSet,
      Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, rfl⟩, hj⟩
    · rintro ⟨⟨j, rfl⟩, hj⟩
      exact ⟨j, hj, rfl⟩
  rw [← he, Finset.card_image_of_injective _ (P.withinTuple i)]

theorem card_dependentOccurrences {b κ : ℕ} (P : Local.EqualityPattern b κ)
    (R : Finset (Fin b))
    (hchild : ∀ i, i ∉ R → (P.classSet i ∩ R.biUnion P.classSet).card = 1) :
    (dependentOccurrences P R).card = 2 * (Finset.univ \ R).card := by
  unfold dependentOccurrences
  rw [Finset.card_biUnion]
  · calc
      (∑ i ∈ Finset.univ \ R,
          ((touchedPositions (rootGeneratorIndices P R i)).image fun j => (i, j)).card) =
          ∑ _i ∈ Finset.univ \ R, 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)]
        have hc : (rootGeneratorIndices P R i).card = 1 := by
          rw [card_rootGeneratorIndices, hchild i (Finset.mem_sdiff.mp hi).2]
        rw [card_touchedPositions_of_card_le_one _ hc.le, hc]
      _ = _ := by simp [Nat.mul_comm]
  · intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro a hai haj
    obtain ⟨x, hx, hxa⟩ := Finset.mem_image.mp hai
    obtain ⟨y, hy, hya⟩ := Finset.mem_image.mp haj
    exact hij (congrArg Prod.fst (hxa.trans hya.symm))

theorem exists_roots_with_exact_dependent_budget {b κ : ℕ}
    (P : Local.EqualityPattern b κ) (hb : 3 ≤ b) (hκ : κ ≤ 2) :
    ∃ R : Finset (Fin b), DisjointRoots P.classSet R ∧
      (Finset.univ \ R).card = κ ∧
      (dependentOccurrences P R).card = 2 * κ ∧
      ∀ i, i ∉ R →
        (P.classSet i ∩ R.biUnion P.classSet).card = 1 ∧
        P.classSet i ∩ (Finset.univ.erase i).biUnion P.classSet ⊆
          R.biUnion P.classSet := by
  obtain ⟨R, hr, hc, hchildren⟩ := exists_pattern_roots_exact_of_three_le P hb hκ
  refine ⟨R, hr, hc, ?_, hchildren⟩
  rw [card_dependentOccurrences P R (fun i hi => (hchildren i hi).1), hc]

end Balanced.RootChildPartition

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_AlignedGlobalProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.AlignedGlobal

open TupleAlignment RootChildPartition AlignedUnused
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem generated_free {b κ : ℕ} (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b) (p : Point F)
    (z : (FreeIndex P R → F) × UnusedArray P a) (ij : FreeIndex P R) :
    prescribedPoint P a bits ((coordinateEquiv P hκ R hD a ha bits p).symm z).1 ij.1 =
      ((linePointEquiv (a.1 ij.1.1) (lineEval (a.1 ij.1.1) p)).symm (z.1 ij)).1 := by
  let e := coordinateEquiv P hκ R hD a ha bits p
  have h := congrFun (congrArg Prod.fst (e.apply_symm_apply z)) ij
  change linePointEquiv (a.1 ij.1.1) (lineEval (a.1 ij.1.1) p)
      ⟨prescribedPoint P a bits (e.symm z).1 ij.1, (e.symm z).2 ij.1⟩ = z.1 ij at h
  have hp := congrArg (fun t => ((linePointEquiv (a.1 ij.1.1)
    (lineEval (a.1 ij.1.1) p)).symm t).1) h
  simpa only [Equiv.symm_apply_apply] using hp

theorem alignedLaw_eq_uniform_coordinates {b κ : ℕ} (P : EqualityPattern b κ)
    (hκ : κ ≤ 2) (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b) (p : Point F) :
    alignedLaw P hκ a ha bits p =
      (PMF.uniformOfFintype ((FreeIndex P R → F) × UnusedArray P a)).map
        (fun z => ((coordinateEquiv P hκ R hD a ha bits p).symm z).1) := by
  let e := coordinateEquiv P hκ R hD a ha bits p
  let : Nonempty (AlignedOffsets P a bits p) :=
    ⟨e.symm ((fun _ => 0), fun _ _ => 0)⟩
  let : Nonempty ({M : MergedPairs F | Aligned P a bits p M} : Set (MergedPairs F)) :=
    ⟨e.symm ((fun _ => 0), fun _ _ => 0)⟩
  unfold alignedLaw
  rw [Balanced.uniform_filter_eq_subtype_map]
  change (PMF.uniformOfFintype (AlignedOffsets P a bits p)).map Subtype.val = _
  have h := uniform_map_equiv e.symm
  rw [← h, PMF.map_comp]
  rfl

theorem conditioned_probability_eq_uniform_coordinates {b κ : ℕ}
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b) (p : Point F)
    (E : MergedPairs F → Prop) :
    conditionedOffsetProbability (Aligned P a bits p) E =
      ((PMF.uniformOfFintype ((FreeIndex P R → F) × UnusedArray P a)).toOuterMeasure
        {z | E ((coordinateEquiv P hκ R hD a ha bits p).symm z).1}).toReal := by
  rw [conditionedOffsetProbability_eq_alignedLaw P hκ a ha bits p E,
    alignedLaw_eq_uniform_coordinates P hκ R hD a ha bits p,
    PMF.toOuterMeasure_map_apply]
  rfl

end
end Balanced.Local.AlignedGlobal

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_AlignedPointExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.AlignedListProbability

open TupleAlignment PartialAlignment
noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem generatedPositions_old_left (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : ∀ i, d i ≠ g) (c : F)
    (J : Finset (Fin 4)) (hJ : J.card ≤ 1) (a : Fin 4 → Bool → F)
    (x : {i : Fin 4 // i ∈ freePositions J} → F) (i : Fin 4) (hi : i ∈ J) :
    generatedPositions d hd σ g hg c J hJ a x i =
      lineIntersection (d i, a i (σ i)) (g,c) :=
  alignedPartial_position_old_left d hd σ g hg c J a
    ((alignedFreeCoordinatesEquiv d hd σ g hg c J hJ a).symm x) i hi

theorem generatedPositions_old_right (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : ∀ i, d i ≠ g) (c : F)
    (J : Finset (Fin 4)) (hJ : J.card ≤ 1) (a : Fin 4 → Bool → F)
    (x : {i : Fin 4 // i ∈ freePositions J} → F) (i : Fin 4) (hi : i + 1 ∈ J) :
    generatedPositions d hd σ g hg c J hJ a x i =
      lineIntersection (d (i+1), a (i+1) (!(σ (i+1)))) (g,c) :=
  alignedPartial_position_old_right d hd σ g hg c J a
    ((alignedFreeCoordinatesEquiv d hd σ g hg c J hJ a).symm x) i hi

end
end Balanced.AlignedListProbability

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_AlignedProjectedExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.InjectionExposure

noncomputable section
open scoped Classical

variable {I J Z : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem auxiliaryLaw_fst_mem_completions (K : Finset I) (base : I ↪ J)
    (noise : (I ↪ J) → PMF Z) (x : (I ↪ J) × Z)
    (hx : x ∈ (auxiliaryLaw K base noise).support) : x.1 ∈ completions K base := by
  change x ∈ ((PMF.uniformOfFinset (completions K base)
    (completions_nonempty K base)).bind
      (fun e => (noise e).map (fun z => (e,z)))).support at hx
  rw [PMF.mem_support_bind_iff] at hx
  obtain ⟨e,he,hx⟩ := hx
  rw [PMF.mem_support_map_iff] at hx
  obtain ⟨z,hz,hx⟩ := hx
  have he' : e ∈ completions K base := by simpa using he
  have hf := congrArg Prod.fst hx
  simpa only [← hf] using he'

end
end Balanced.InjectionExposure

namespace Balanced.Local.TokenExposure

open AlignedListProbability PartialAlignment InjectionExposure
noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ} {Z : Type*} [Fintype Z]

theorem projected_left_probability_le
    (P : EqualityPattern b κ) (bits : Bits b) (p : Point F) (i : Fin b)
    (J : Finset (Fin 4)) (hJ : J.card ≤ 1) (j : Fin 4) (hj : j ∈ J)
    (K : Finset (DirectionToken b κ)) (base : DirectionToken b κ ↪ Direction F)
    (htarget : Sum.inl i ∉ K) (hold : Sum.inr (P.classOf i j) ∈ K)
    (noise : (DirectionToken b κ ↪ Direction F) → PMF Z)
    (hnoise : DependsOnExposed K noise)
    (a : Z → Fin 4 → Bool → F)
    (x : Z → {j : Fin 4 // j ∈ freePositions J} → F)
    (m : Z → Line F) :
    ((auxiliaryLaw K base noise).toOuterMeasure
      {ez | (tupleDirections P ez.1 i j, a ez.2 j (bits i j)) ≠ m ez.2 ∧
        pointOutput P bits p i J hJ a x ez.1 ez.2 j ≠ p ∧
        OnLine (pointOutput P bits p i J hJ a x ez.1 ez.2 j) (m ez.2)}).toReal ≤
      1 / ((Fintype.card F + 1 - K.card : ℕ) : ℝ) := by
  let l : Z → Line F := fun z => (base (Sum.inr (P.classOf i j)), a z j (bits i j))
  have h := auxiliary_guarded_projection_probability_le K base (Sum.inl i) htarget
    noise hnoise (fun _ => p) l m
  apply le_trans _ h
  apply ENNReal.toReal_mono
  · rw [PMF.toOuterMeasure_apply]
    exact PMF.tsum_coe_indicator_ne_top _ _
  · apply PMF.toOuterMeasure_mono
    intro ez hez
    have he := (mem_completions K base ez.1).mp
      (auxiliaryLaw_fst_mem_completions K base noise ez hez.2)
    have hd : tupleDirections P ez.1 i j = base (Sum.inr (P.classOf i j)) :=
      he _ hold
    have hp : pointOutput P bits p i J hJ a x ez.1 ez.2 j =
        lineIntersection (l ez.2) (lineThrough (ez.1 (Sum.inl i)) p) := by
      change generatedPositions _ _ _ _ _ _ _ _ _ _ j = _
      rw [generatedPositions_old_left _ _ _ _ _ _ J hJ _ _ j hj]
      rw [hd]
      rfl
    have hne : ez.1 (Sum.inl i) ≠ (l ez.2).1 := by
      change ez.1 (Sum.inl i) ≠ base (Sum.inr (P.classOf i j))
      rw [← hd]
      exact (tupleDirections_ne_target P ez.1 i j).symm
    exact ⟨by simpa only [l, hd] using hez.1.1, hne,
      by simpa only [hp] using hez.1.2.1,
      by simpa only [hp] using hez.1.2.2⟩

theorem projected_right_probability_le
    (P : EqualityPattern b κ) (bits : Bits b) (p : Point F) (i : Fin b)
    (J : Finset (Fin 4)) (hJ : J.card ≤ 1) (j : Fin 4) (hj : j+1 ∈ J)
    (K : Finset (DirectionToken b κ)) (base : DirectionToken b κ ↪ Direction F)
    (htarget : Sum.inl i ∉ K) (hold : Sum.inr (P.classOf i (j+1)) ∈ K)
    (noise : (DirectionToken b κ ↪ Direction F) → PMF Z)
    (hnoise : DependsOnExposed K noise)
    (a : Z → Fin 4 → Bool → F)
    (x : Z → {j : Fin 4 // j ∈ freePositions J} → F)
    (m : Z → Line F) :
    ((auxiliaryLaw K base noise).toOuterMeasure
      {ez | (tupleDirections P ez.1 i (j+1), a ez.2 (j+1) (!(bits i (j+1)))) ≠ m ez.2 ∧
        pointOutput P bits p i J hJ a x ez.1 ez.2 j ≠ p ∧
        OnLine (pointOutput P bits p i J hJ a x ez.1 ez.2 j) (m ez.2)}).toReal ≤
      1 / ((Fintype.card F + 1 - K.card : ℕ) : ℝ) := by
  let l : Z → Line F := fun z =>
    (base (Sum.inr (P.classOf i (j+1))), a z (j+1) (!(bits i (j+1))))
  have h := auxiliary_guarded_projection_probability_le K base (Sum.inl i) htarget
    noise hnoise (fun _ => p) l m
  apply le_trans _ h
  apply ENNReal.toReal_mono
  · rw [PMF.toOuterMeasure_apply]
    exact PMF.tsum_coe_indicator_ne_top _ _
  · apply PMF.toOuterMeasure_mono
    intro ez hez
    have he := (mem_completions K base ez.1).mp
      (auxiliaryLaw_fst_mem_completions K base noise ez hez.2)
    have hd : tupleDirections P ez.1 i (j+1) = base (Sum.inr (P.classOf i (j+1))) :=
      he _ hold
    have hp : pointOutput P bits p i J hJ a x ez.1 ez.2 j =
        lineIntersection (l ez.2) (lineThrough (ez.1 (Sum.inl i)) p) := by
      change generatedPositions _ _ _ _ _ _ _ _ _ _ j = _
      rw [generatedPositions_old_right _ _ _ _ _ _ J hJ _ _ j hj]
      rw [hd]
      rfl
    have hne : ez.1 (Sum.inl i) ≠ (l ez.2).1 := by
      change ez.1 (Sum.inl i) ≠ base (Sum.inr (P.classOf i (j+1)))
      rw [← hd]
      exact (tupleDirections_ne_target P ez.1 i (j+1)).symm
    exact ⟨by simpa only [l, hd] using hez.1.1, hne,
      by simpa only [hp] using hez.1.2.1,
      by simpa only [hp] using hez.1.2.2⟩

theorem projected_left_probability_le_two_div
    (P : EqualityPattern b κ) (bits : Bits b) (p : Point F) (i : Fin b)
    (J : Finset (Fin 4)) (hJ : J.card ≤ 1) (j : Fin 4) (hj : j ∈ J)
    (K : Finset (DirectionToken b κ)) (base : DirectionToken b κ ↪ Direction F)
    (htarget : Sum.inl i ∉ K) (hold : Sum.inr (P.classOf i j) ∈ K)
    (noise : (DirectionToken b κ ↪ Direction F) → PMF Z)
    (hnoise : DependsOnExposed K noise)
    (a : Z → Fin 4 → Bool → F)
    (x : Z → {j : Fin 4 // j ∈ freePositions J} → F)
    (m : Z → Line F) (hK : K.card ≤ 5 * b)
    (hb : 10 * b ≤ Fintype.card F) :
    ((auxiliaryLaw K base noise).toOuterMeasure
      {ez | (tupleDirections P ez.1 i j, a ez.2 j (bits i j)) ≠ m ez.2 ∧
        pointOutput P bits p i J hJ a x ez.1 ez.2 j ≠ p ∧
        OnLine (pointOutput P bits p i J hJ a x ez.1 ez.2 j) (m ez.2)}).toReal ≤
      2 / (Fintype.card F : ℝ) := by
  exact (projected_left_probability_le P bits p i J hJ j hj K base
    htarget hold noise hnoise a x m).trans
    (inverse_remaining_le_two_div (Fintype.card F) K.card b
      Fintype.card_pos hK hb)

theorem projected_right_probability_le_two_div
    (P : EqualityPattern b κ) (bits : Bits b) (p : Point F) (i : Fin b)
    (J : Finset (Fin 4)) (hJ : J.card ≤ 1) (j : Fin 4) (hj : j+1 ∈ J)
    (K : Finset (DirectionToken b κ)) (base : DirectionToken b κ ↪ Direction F)
    (htarget : Sum.inl i ∉ K) (hold : Sum.inr (P.classOf i (j+1)) ∈ K)
    (noise : (DirectionToken b κ ↪ Direction F) → PMF Z)
    (hnoise : DependsOnExposed K noise)
    (a : Z → Fin 4 → Bool → F)
    (x : Z → {j : Fin 4 // j ∈ freePositions J} → F)
    (m : Z → Line F) (hK : K.card ≤ 5 * b)
    (hb : 10 * b ≤ Fintype.card F) :
    ((auxiliaryLaw K base noise).toOuterMeasure
      {ez | (tupleDirections P ez.1 i (j+1), a ez.2 (j+1) (!(bits i (j+1)))) ≠ m ez.2 ∧
        pointOutput P bits p i J hJ a x ez.1 ez.2 j ≠ p ∧
        OnLine (pointOutput P bits p i J hJ a x ez.1 ez.2 j) (m ez.2)}).toReal ≤
      2 / (Fintype.card F : ℝ) := by
  exact (projected_right_probability_le P bits p i J hJ j hj K base
    htarget hold noise hnoise a x m).trans
    (inverse_remaining_le_two_div (Fintype.card F) K.card b
      Fintype.card_pos hK hb)

end
end Balanced.Local.TokenExposure

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_AlignedGlobalCurrentTuple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.AlignedListProbability
open TupleAlignment PartialAlignment
noncomputable section
open scoped Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem generatedPositions_reconstruct (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i+1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : ∀ i, d i ≠ g) (c : F)
    (J : Finset (Fin 4)) (hJ : J.card ≤ 1)
    (a o : Fin 4 → Bool → F) (hold : ∀ j ∈ J, o j = a j)
    (halign : ∀ j, OnLine (tuplePositionEquiv d hd σ o j) (g,c))
    (x : {j : Fin 4 // j ∈ freePositions J} → F)
    (hx : ∀ j, linePointEquiv g c
      ⟨tuplePositionEquiv d hd σ o j.1, halign j.1⟩ = x j) :
    generatedPositions d hd σ g hg c J hJ a x = tuplePositionEquiv d hd σ o := by
  let v : AlignedPartialOffsets d hd σ g c J a := ⟨⟨o,hold⟩,halign⟩
  let e := alignedFreeCoordinatesEquiv d hd σ g hg c J hJ a
  have he : e v = x := funext hx
  have hi : e.symm x = v := by rw [← he]; exact e.symm_apply_apply v
  change tuplePositionEquiv d hd σ (e.symm x).1.1 = _
  rw [hi]

end
end Balanced.AlignedListProbability

namespace Balanced.Local.AlignedGlobal
open RootChildPartition AlignedListProbability TupleAlignment PartialAlignment TokenExposure
noncomputable section
open scoped Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

theorem currentOldIndices_card_le_one (P : EqualityPattern b κ)
    (R : Finset (Fin b))
    (hchild : ∀ i, i ∉ R → (P.classSet i ∩ R.biUnion P.classSet).card = 1)
    (i : Fin b) : (currentOldIndices P R i).card ≤ 1 := by
  by_cases hi : i ∈ R
  · simp [currentOldIndices, hi]
  · rw [currentOldIndices, ite_eq_right hi, card_rootGeneratorIndices, hchild i hi]

theorem generated_current_tuple (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (bits : Bits b) (p : Point F) (e : DirectionToken b κ ↪ Direction F)
    (i : Fin b) (hJ : (currentOldIndices P R i).card ≤ 1)
    (z : (FreeIndex P R → F) × AlignedUnused.UnusedArray P (tokenInjectionEquiv F b κ e).1)
    (a : Fin 4 → Bool → F)
    (ha : ∀ j ∈ currentOldIndices P R i,
      ((coordinateEquiv P hκ R hD (tokenInjectionEquiv F b κ e).1
        (allTokensDistinct_eligible P _ (tokenInjectionEquiv F b κ e).2) bits p).symm z).1
          (e (Sum.inr (P.classOf i j))) = a j) :
    generatedPositions (tupleDirections P e i) (tupleDirections_adjacent P e i)
      (bits i) (e (Sum.inl i)) (tupleDirections_ne_target P e i)
      (lineEval (e (Sum.inl i)) p) (currentOldIndices P R i) hJ a
      (fun j => z.1 (currentFreeIndex P R i j)) =
      fun j => prescribedPoint P (tokenInjectionEquiv F b κ e).1 bits
        ((coordinateEquiv P hκ R hD (tokenInjectionEquiv F b κ e).1
          (allTokensDistinct_eligible P _ (tokenInjectionEquiv F b κ e).2) bits p).symm z).1
        (i,j) := by
  let A := (tokenInjectionEquiv F b κ e).1
  let hA := allTokensDistinct_eligible P A (tokenInjectionEquiv F b κ e).2
  let E := coordinateEquiv P hκ R hD A hA bits p
  let M := E.symm z
  have hm : ∀ j, OnLine (tuplePositionEquiv (tupleDirections P e i)
      (tupleDirections_adjacent P e i) (bits i)
      (fun k => M.1 (e (Sum.inr (P.classOf i k)))) j)
      (e (Sum.inl i), lineEval (e (Sum.inl i)) p) := fun j => M.2 (i,j)
  apply generatedPositions_reconstruct _ _ _ _ _ _ _ _ a
    (fun k => M.1 (e (Sum.inr (P.classOf i k)))) ha hm
  intro j
  have h := congrFun (congrArg Prod.fst (E.apply_symm_apply z)) (currentFreeIndex P R i j)
  exact h

theorem pointOutput_eq_global {Z : Type*}
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (bits : Bits b) (p : Point F) (e : DirectionToken b κ ↪ Direction F)
    (i : Fin b) (hJ : (currentOldIndices P R i).card ≤ 1)
    (z : (FreeIndex P R → F) × AlignedUnused.UnusedArray P (tokenInjectionEquiv F b κ e).1)
    (a : Z → Fin 4 → Bool → F)
    (x : Z → {j : Fin 4 // j ∈ freePositions (currentOldIndices P R i)} → F)
    (w : Z)
    (ha : ∀ j ∈ currentOldIndices P R i,
      ((coordinateEquiv P hκ R hD (tokenInjectionEquiv F b κ e).1
        (allTokensDistinct_eligible P _ (tokenInjectionEquiv F b κ e).2) bits p).symm z).1
          (e (Sum.inr (P.classOf i j))) = a w j)
    (hx : x w = fun j => z.1 (currentFreeIndex P R i j)) (j : Fin 4) :
    pointOutput P bits p i (currentOldIndices P R i) hJ a x e w j =
      prescribedPoint P (tokenInjectionEquiv F b κ e).1 bits
        ((coordinateEquiv P hκ R hD (tokenInjectionEquiv F b κ e).1
          (allTokensDistinct_eligible P _ (tokenInjectionEquiv F b κ e).2) bits p).symm z).1
        (i,j) := by
  unfold pointOutput
  rw [hx]
  exact congrFun (generated_current_tuple P hκ R hD bits p e i hJ z (a w) ha) j

end
end Balanced.Local.AlignedGlobal

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_AlignedGlobalHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.AlignedGlobal

open RootChildPartition TupleAlignment PrescribedGeometry
noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

omit [Fintype F] [DecidableEq F] in
private theorem linePointEquiv_coordinate (g : Direction F) (c : F)
    (x : {y : Point F // OnLine y (g,c)}) :
    linePointEquiv g c x = lineScalar g x.1 := by
  cases g <;> rfl

omit [Fintype F] in

theorem free_point_eq_of_scalar_eq (P : EqualityPattern b κ)
    (R : Finset (Fin b)) (a a' : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F)
    (M : AlignedOffsets P a bits p) (N : AlignedOffsets P a' bits p)
    (ij : FreeIndex P R)
    (hx : (coordinates P R a bits p M).1 ij = (coordinates P R a' bits p N).1 ij)
    (ht : a.1 ij.1.1 = a'.1 ij.1.1) :
    prescribedPoint P a bits M.1 ij.1 = prescribedPoint P a' bits N.1 ij.1 := by
  have h := hx
  change linePointEquiv (a.1 ij.1.1) (lineEval (a.1 ij.1.1) p)
      ⟨prescribedPoint P a bits M.1 ij.1, M.2 ij.1⟩ =
    linePointEquiv (a'.1 ij.1.1) (lineEval (a'.1 ij.1.1) p)
      ⟨prescribedPoint P a' bits N.1 ij.1, N.2 ij.1⟩ at h
  have hn : OnLine (prescribedPoint P a' bits N.1 ij.1)
      (lineThrough (a.1 ij.1.1) p) := by simpa only [ht] using N.2 ij.1
  let yn : {x : Point F // OnLine x (lineThrough (a.1 ij.1.1) p)} :=
    ⟨prescribedPoint P a' bits N.1 ij.1, hn⟩
  have h' : linePointEquiv (a.1 ij.1.1) (lineEval (a.1 ij.1.1) p)
      ⟨prescribedPoint P a bits M.1 ij.1, M.2 ij.1⟩ =
    linePointEquiv (a.1 ij.1.1) (lineEval (a.1 ij.1.1) p) yn := by
    erw [linePointEquiv_coordinate, linePointEquiv_coordinate] at h ⊢
    simpa only [yn, ht] using h
  exact congrArg Subtype.val ((linePointEquiv _ _).injective h')

omit [Fintype F] in
theorem free_point_eq_of_coordinate_eq (P : EqualityPattern b κ)
    (R : Finset (Fin b)) (a a' : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F)
    (M : AlignedOffsets P a bits p) (N : AlignedOffsets P a' bits p)
    (hx : (coordinates P R a bits p M).1 = (coordinates P R a' bits p N).1)
    (ij : FreeIndex P R) (ht : a.1 ij.1.1 = a'.1 ij.1.1) :
    prescribedPoint P a bits M.1 ij.1 = prescribedPoint P a' bits N.1 ij.1 :=
  free_point_eq_of_scalar_eq P R a a' bits p M N ij (congrFun hx ij) ht

omit [Fintype F] [DecidableEq F] in

theorem generator_offsets_eq_of_points (P : EqualityPattern b κ)
    (a a' : DirectionAssignment F b κ) (ha : Eligible P a) (ha' : Eligible P a')
    (bits : Bits b) (M N : MergedPairs F) (i : Fin b) (j : Fin 4)
    (hd : a.2 (P.classOf i j) = a'.2 (P.classOf i j))
    (hp : ∀ k, prescribedPoint P a bits M (i,k) =
      prescribedPoint P a' bits N (i,k)) :
    M (a.2 (P.classOf i j)) = N (a'.2 (P.classOf i j)) := by
  funext s
  by_cases hs : s = bits i j
  · have hm := prescribedPoint_on_left (M := M) (bits := bits) ha i j
    have hn := prescribedPoint_on_left (M := N) (bits := bits) ha' i j
    dsimp only [OnLine, constituent] at hm hn
    rw [hd, hp j] at hm
    simpa only [hs, hd] using hm.symm.trans hn
  · have hs' : s = !(bits i j) := by cases s <;> cases h : bits i j <;> simp_all
    have hm := prescribedPoint_on_right (M := M) (bits := bits) ha i (j-1)
    have hn := prescribedPoint_on_right (M := N) (bits := bits) ha' i (j-1)
    have hj : j - 1 + 1 = j := sub_add_cancel j 1
    dsimp only [OnLine, constituent] at hm hn
    simp only [hj] at hm hn
    rw [hd, hp (j-1)] at hm
    simpa only [hs', hd] using hm.symm.trans hn

omit [Fintype F] in
theorem root_offsets_eq_of_coordinates (P : EqualityPattern b κ)
    (R : Finset (Fin b)) (a a' : DirectionAssignment F b κ)
    (ha : Eligible P a) (ha' : Eligible P a') (bits : Bits b) (p : Point F)
    (M : AlignedOffsets P a bits p) (N : AlignedOffsets P a' bits p)
    (hx : (coordinates P R a bits p M).1 = (coordinates P R a' bits p N).1)
    (ht : ∀ i ∈ R, a.1 i = a'.1 i)
    (c : Fin (4*b-κ)) (hc : c ∈ R.biUnion P.classSet)
    (hd : a.2 c = a'.2 c) : M.1 (a.2 c) = N.1 (a'.2 c) := by
  obtain ⟨i, hi, hj⟩ := Finset.mem_biUnion.mp hc
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hj
  apply generator_offsets_eq_of_points P a a' ha ha' bits M.1 N.1 i j hd
  intro k
  apply free_point_eq_of_coordinate_eq P R a a' bits p M N hx
    ⟨(i,k), ?_⟩ (ht i hi)
  simp only [mem_dependentOccurrences, not_and]
  exact fun hnot => (hnot hi).elim

omit [Fintype F] in
theorem point_eq_of_root_history (P : EqualityPattern b κ)
    (R : Finset (Fin b)) (a a' : DirectionAssignment F b κ)
    (ha : Eligible P a) (ha' : Eligible P a') (bits : Bits b) (p : Point F)
    (M : AlignedOffsets P a bits p) (N : AlignedOffsets P a' bits p)
    (hx : (coordinates P R a bits p M).1 = (coordinates P R a' bits p N).1)
    (ht : ∀ i ∈ R, a.1 i = a'.1 i)
    (hd : ∀ c ∈ R.biUnion P.classSet, a.2 c = a'.2 c)
    (ij : Fin b × Fin 4) (hi : a.1 ij.1 = a'.1 ij.1) :
    prescribedPoint P a bits M.1 ij = prescribedPoint P a' bits N.1 ij := by
  by_cases hdep : ij ∈ dependentOccurrences P R
  · have hdep' := (mem_dependentOccurrences P R ij).mp hdep
    have htarget : lineEval (a.1 ij.1) (prescribedPoint P a bits M.1 ij) =
        lineEval (a.1 ij.1) (prescribedPoint P a' bits N.1 ij) := by
      have hm := M.2 ij
      have hn := N.2 ij
      change lineEval _ _ = _ at hm hn
      rw [hi] at hm ⊢
      exact hm.trans hn.symm
    rcases hdep'.2 with hl | hr
    · apply (lineEvalEquiv (a.2 (P.classOf ij.1 ij.2)) (a.1 ij.1)
        (ha.2.2 ij.1 ij.2)).injective
      apply Prod.ext
      · have hm := prescribedPoint_on_left (M := M.1) (bits := bits) ha ij.1 ij.2
        have hn := prescribedPoint_on_left (M := N.1) (bits := bits) ha' ij.1 ij.2
        have ho := root_offsets_eq_of_coordinates P R a a' ha ha' bits p M N hx ht
          _ hl (hd _ hl)
        dsimp only [OnLine, constituent] at hm hn
        change lineEval _ _ = lineEval _ _
        rw [hm, ho, hd _ hl]
        exact hn.symm
      · exact htarget
    · apply (lineEvalEquiv (a.2 (P.classOf ij.1 (ij.2+1))) (a.1 ij.1)
        (ha.2.2 ij.1 (ij.2+1))).injective
      apply Prod.ext
      · have hm := prescribedPoint_on_right (M := M.1) (bits := bits) ha ij.1 ij.2
        have hn := prescribedPoint_on_right (M := N.1) (bits := bits) ha' ij.1 ij.2
        have ho := root_offsets_eq_of_coordinates P R a a' ha ha' bits p M N hx ht
          _ hr (hd _ hr)
        dsimp only [OnLine, constituent] at hm hn
        change lineEval _ _ = lineEval _ _
        rw [hm, ho, hd _ hr]
        exact hn.symm
      · exact htarget
  · exact free_point_eq_of_coordinate_eq P R a a' bits p M N hx ⟨ij,hdep⟩ hi

omit [Fintype F] in
theorem history_points_eq (P : EqualityPattern b κ)
    (R S : Finset (Fin b)) (hclosed : ∀ i ∈ S, i ∉ R → R ⊆ S)
    (a a' : DirectionAssignment F b κ) (ha : Eligible P a) (ha' : Eligible P a')
    (bits : Bits b) (p : Point F)
    (M : AlignedOffsets P a bits p) (N : AlignedOffsets P a' bits p)
    (hx : (coordinates P R a bits p M).1 = (coordinates P R a' bits p N).1)
    (ht : ∀ i ∈ S, a.1 i = a'.1 i)
    (hd : ∀ c ∈ S.biUnion P.classSet, a.2 c = a'.2 c) :
    ∀ i ∈ S, ∀ j, prescribedPoint P a bits M.1 (i,j) =
      prescribedPoint P a' bits N.1 (i,j) := by
  intro i hi j
  by_cases hir : i ∈ R
  · apply free_point_eq_of_coordinate_eq P R a a' bits p M N hx
      ⟨(i,j), ?_⟩ (ht i hi)
    simp only [mem_dependentOccurrences, not_and]
    exact fun hn => (hn hir).elim
  · apply point_eq_of_root_history P R a a' ha ha' bits p M N hx
      (fun r hr => ht r (hclosed i hi hir hr)) ?_ (i,j) (ht i hi)
    intro c hc
    apply hd c
    obtain ⟨r, hr, hcr⟩ := Finset.mem_biUnion.mp hc
    exact Finset.mem_biUnion.mpr ⟨r, hclosed i hi hir hr, hcr⟩

omit [Fintype F] in
theorem history_offsets_eq (P : EqualityPattern b κ)
    (R S : Finset (Fin b)) (hclosed : ∀ i ∈ S, i ∉ R → R ⊆ S)
    (a a' : DirectionAssignment F b κ) (ha : Eligible P a) (ha' : Eligible P a')
    (bits : Bits b) (p : Point F)
    (M : AlignedOffsets P a bits p) (N : AlignedOffsets P a' bits p)
    (hx : (coordinates P R a bits p M).1 = (coordinates P R a' bits p N).1)
    (ht : ∀ i ∈ S, a.1 i = a'.1 i)
    (hd : ∀ c ∈ S.biUnion P.classSet, a.2 c = a'.2 c) :
    ∀ c ∈ S.biUnion P.classSet, M.1 (a.2 c) = N.1 (a'.2 c) := by
  intro c hc
  obtain ⟨i, hi, hj⟩ := Finset.mem_biUnion.mp hc
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hj
  exact generator_offsets_eq_of_points P a a' ha ha' bits M.1 N.1 i j
    (hd _ hc) (history_points_eq P R S hclosed a a' ha ha' bits p M N hx ht hd i hi)

theorem inverse_coordinates_fst_eq (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (a a' : DirectionAssignment F b κ) (ha : Eligible P a) (ha' : Eligible P a')
    (bits : Bits b) (p : Point F) (x : FreeIndex P R → F)
    (u : AlignedUnused.UnusedArray P a) (u' : AlignedUnused.UnusedArray P a') :
    (coordinates P R a bits p
      ((coordinateEquiv P hκ R hD a ha bits p).symm (x,u))).1 =
    (coordinates P R a' bits p
      ((coordinateEquiv P hκ R hD a' ha' bits p).symm (x,u'))).1 := by
  change ((coordinateEquiv P hκ R hD a ha bits p)
      ((coordinateEquiv P hκ R hD a ha bits p).symm (x,u))).1 =
    ((coordinateEquiv P hκ R hD a' ha' bits p)
      ((coordinateEquiv P hκ R hD a' ha' bits p).symm (x,u'))).1
  simp only [Equiv.apply_symm_apply]

theorem root_closed_of_prefix (R S : Finset (Fin b))
    (hS : S ⊆ R ∨ R ⊆ S) : ∀ i ∈ S, i ∉ R → R ⊆ S := by
  intro i hi hn
  rcases hS with hS | hS
  · exact False.elim (hn (hS hi))
  · exact hS

theorem generated_history_agree (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R S : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (hS : S ⊆ R ∨ R ⊆ S)
    (a a' : DirectionAssignment F b κ) (ha : Eligible P a) (ha' : Eligible P a')
    (bits : Bits b) (p : Point F) (x : FreeIndex P R → F)
    (u : AlignedUnused.UnusedArray P a) (u' : AlignedUnused.UnusedArray P a')
    (ht : ∀ i ∈ S, a.1 i = a'.1 i)
    (hd : ∀ c ∈ S.biUnion P.classSet, a.2 c = a'.2 c) :
    let M := (coordinateEquiv P hκ R hD a ha bits p).symm (x,u)
    let N := (coordinateEquiv P hκ R hD a' ha' bits p).symm (x,u')
    (∀ i ∈ S, ∀ j, prescribedPoint P a bits M.1 (i,j) =
      prescribedPoint P a' bits N.1 (i,j)) ∧
    (∀ c ∈ S.biUnion P.classSet, M.1 (a.2 c) = N.1 (a'.2 c)) := by
  dsimp only
  have hx := inverse_coordinates_fst_eq P hκ R hD a a' ha ha' bits p x u u'
  exact ⟨history_points_eq P R S (root_closed_of_prefix R S hS) a a' ha ha'
      bits p _ _ hx ht hd,
    history_offsets_eq P R S (root_closed_of_prefix R S hS) a a' ha ha'
      bits p _ _ hx ht hd⟩

theorem generated_point_eq_of_root_history (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (a a' : DirectionAssignment F b κ) (ha : Eligible P a) (ha' : Eligible P a')
    (bits : Bits b) (p : Point F) (x : FreeIndex P R → F)
    (u : AlignedUnused.UnusedArray P a) (u' : AlignedUnused.UnusedArray P a')
    (ht : ∀ i ∈ R, a.1 i = a'.1 i)
    (hd : ∀ c ∈ R.biUnion P.classSet, a.2 c = a'.2 c)
    (ij : Fin b × Fin 4) (hi : a.1 ij.1 = a'.1 ij.1) :
    prescribedPoint P a bits
      ((coordinateEquiv P hκ R hD a ha bits p).symm (x,u)).1 ij =
    prescribedPoint P a' bits
      ((coordinateEquiv P hκ R hD a' ha' bits p).symm (x,u')).1 ij :=
  point_eq_of_root_history P R a a' ha ha' bits p _ _
    (inverse_coordinates_fst_eq P hκ R hD a a' ha ha' bits p x u u') ht hd ij hi

omit [Fintype F] in
theorem history_points_eq_of_coordinates_on (P : EqualityPattern b κ)
    (R S : Finset (Fin b)) (hclosed : ∀ i ∈ S, i ∉ R → R ⊆ S)
    (a a' : DirectionAssignment F b κ) (ha : Eligible P a) (ha' : Eligible P a')
    (bits : Bits b) (p : Point F)
    (M : AlignedOffsets P a bits p) (N : AlignedOffsets P a' bits p)
    (hx : ∀ ij : FreeIndex P R, ij.1.1 ∈ S →
      (coordinates P R a bits p M).1 ij = (coordinates P R a' bits p N).1 ij)
    (ht : ∀ i ∈ S, a.1 i = a'.1 i)
    (hd : ∀ c ∈ S.biUnion P.classSet, a.2 c = a'.2 c) :
    ∀ i ∈ S, ∀ j, prescribedPoint P a bits M.1 (i,j) =
      prescribedPoint P a' bits N.1 (i,j) := by
  have hf (ij : FreeIndex P R) (hi : ij.1.1 ∈ S) :
      prescribedPoint P a bits M.1 ij.1 = prescribedPoint P a' bits N.1 ij.1 :=
    free_point_eq_of_scalar_eq P R a a' bits p M N ij (hx ij hi) (ht _ hi)
  intro i hi j
  by_cases hdep : (i,j) ∈ dependentOccurrences P R
  · have hh := (mem_dependentOccurrences P R (i,j)).mp hdep
    have hRS : R ⊆ S := hclosed i hi hh.1
    have hCS : R.biUnion P.classSet ⊆ S.biUnion P.classSet := by
      intro c hc
      obtain ⟨r, hr, hcr⟩ := Finset.mem_biUnion.mp hc
      exact Finset.mem_biUnion.mpr ⟨r, hRS hr, hcr⟩
    have hold (c : Fin (4*b-κ)) (hc : c ∈ R.biUnion P.classSet) :
        M.1 (a.2 c) = N.1 (a'.2 c) := by
      obtain ⟨r, hr, hcr⟩ := Finset.mem_biUnion.mp hc
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hcr
      apply generator_offsets_eq_of_points P a a' ha ha' bits M.1 N.1 r k
        (hd _ (hCS hc))
      intro l
      apply hf ⟨(r,l), ?_⟩ (hRS hr)
      simp only [mem_dependentOccurrences, not_and]
      exact fun hn => (hn hr).elim
    have htarget : lineEval (a.1 i) (prescribedPoint P a bits M.1 (i,j)) =
        lineEval (a.1 i) (prescribedPoint P a' bits N.1 (i,j)) := by
      have hm := M.2 (i,j)
      have hn := N.2 (i,j)
      change lineEval _ _ = _ at hm hn
      rw [ht i hi] at hm ⊢
      exact hm.trans hn.symm
    rcases hh.2 with hl | hr
    · apply (lineEvalEquiv (a.2 (P.classOf i j)) (a.1 i) (ha.2.2 i j)).injective
      apply Prod.ext
      · have hm := prescribedPoint_on_left (M := M.1) (bits := bits) ha i j
        have hn := prescribedPoint_on_left (M := N.1) (bits := bits) ha' i j
        dsimp only [OnLine, constituent] at hm hn
        change lineEval _ _ = lineEval _ _
        rw [hm, hold _ hl, hd _ (hCS hl)]
        exact hn.symm
      · exact htarget
    · apply (lineEvalEquiv (a.2 (P.classOf i (j+1))) (a.1 i)
        (ha.2.2 i (j+1))).injective
      apply Prod.ext
      · have hm := prescribedPoint_on_right (M := M.1) (bits := bits) ha i j
        have hn := prescribedPoint_on_right (M := N.1) (bits := bits) ha' i j
        dsimp only [OnLine, constituent] at hm hn
        change lineEval _ _ = lineEval _ _
        rw [hm, hold _ hr, hd _ (hCS hr)]
        exact hn.symm
      · exact htarget
  · exact hf ⟨(i,j),hdep⟩ hi

omit [Fintype F] in
theorem history_offsets_eq_of_coordinates_on (P : EqualityPattern b κ)
    (R S : Finset (Fin b)) (hclosed : ∀ i ∈ S, i ∉ R → R ⊆ S)
    (a a' : DirectionAssignment F b κ) (ha : Eligible P a) (ha' : Eligible P a')
    (bits : Bits b) (p : Point F)
    (M : AlignedOffsets P a bits p) (N : AlignedOffsets P a' bits p)
    (hx : ∀ ij : FreeIndex P R, ij.1.1 ∈ S →
      (coordinates P R a bits p M).1 ij = (coordinates P R a' bits p N).1 ij)
    (ht : ∀ i ∈ S, a.1 i = a'.1 i)
    (hd : ∀ c ∈ S.biUnion P.classSet, a.2 c = a'.2 c) :
    ∀ c ∈ S.biUnion P.classSet, M.1 (a.2 c) = N.1 (a'.2 c) := by
  intro c hc
  obtain ⟨i, hi, hj⟩ := Finset.mem_biUnion.mp hc
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hj
  exact generator_offsets_eq_of_points P a a' ha ha' bits M.1 N.1 i j
    (hd _ hc) (history_points_eq_of_coordinates_on P R S hclosed
      a a' ha ha' bits p M N hx ht hd i hi)

theorem generated_history_agree_on (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R S : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (hS : S ⊆ R ∨ R ⊆ S)
    (a a' : DirectionAssignment F b κ) (ha : Eligible P a) (ha' : Eligible P a')
    (bits : Bits b) (p : Point F) (x y : FreeIndex P R → F)
    (hxy : ∀ ij : FreeIndex P R, ij.1.1 ∈ S → x ij = y ij)
    (u : AlignedUnused.UnusedArray P a) (u' : AlignedUnused.UnusedArray P a')
    (ht : ∀ i ∈ S, a.1 i = a'.1 i)
    (hd : ∀ c ∈ S.biUnion P.classSet, a.2 c = a'.2 c) :
    let M := (coordinateEquiv P hκ R hD a ha bits p).symm (x,u)
    let N := (coordinateEquiv P hκ R hD a' ha' bits p).symm (y,u')
    (∀ i ∈ S, ∀ j, prescribedPoint P a bits M.1 (i,j) =
      prescribedPoint P a' bits N.1 (i,j)) ∧
    (∀ c ∈ S.biUnion P.classSet, M.1 (a.2 c) = N.1 (a'.2 c)) := by
  let M := (coordinateEquiv P hκ R hD a ha bits p).symm (x,u)
  let N := (coordinateEquiv P hκ R hD a' ha' bits p).symm (y,u')
  have hx : ∀ ij : FreeIndex P R, ij.1.1 ∈ S →
      (coordinates P R a bits p M).1 ij = (coordinates P R a' bits p N).1 ij := by
    intro ij hi
    have hm := congrFun (congrArg Prod.fst
      ((coordinateEquiv P hκ R hD a ha bits p).apply_symm_apply (x,u))) ij
    have hn := congrFun (congrArg Prod.fst
      ((coordinateEquiv P hκ R hD a' ha' bits p).apply_symm_apply (y,u'))) ij
    exact hm.trans ((hxy ij hi).trans hn.symm)
  exact ⟨history_points_eq_of_coordinates_on P R S (root_closed_of_prefix R S hS)
      a a' ha ha' bits p M N hx ht hd,
    history_offsets_eq_of_coordinates_on P R S (root_closed_of_prefix R S hS)
      a a' ha ha' bits p M N hx ht hd⟩

theorem generated_history_update (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R S : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (hS : S ⊆ R ∨ R ⊆ S)
    (a : DirectionAssignment F b κ) (ha : Eligible P a)
    (bits : Bits b) (p : Point F) (x : FreeIndex P R → F)
    (u : AlignedUnused.UnusedArray P a) (v : FreeIndex P R) (hv : v.1.1 ∉ S) (t : F) :
    let M := (coordinateEquiv P hκ R hD a ha bits p).symm (x,u)
    let N := (coordinateEquiv P hκ R hD a ha bits p).symm (Function.update x v t,u)
    (∀ i ∈ S, ∀ j, prescribedPoint P a bits M.1 (i,j) =
      prescribedPoint P a bits N.1 (i,j)) ∧
    (∀ c ∈ S.biUnion P.classSet, M.1 (a.2 c) = N.1 (a.2 c)) := by
  apply generated_history_agree_on P hκ R S hD hS a a ha ha bits p
    x (Function.update x v t) ?_ u u (fun _ _ => rfl) (fun _ _ => rfl)
  intro ij hi
  have hne : ij ≠ v := by
    intro heq
    exact hv (heq ▸ hi)
  simp only [Function.update_of_ne hne]

end
end Balanced.Local.AlignedGlobal

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_AcyclicProductBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Balanced.DependencyExtraction

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [Nonempty β]

theorem expect_coordinate_refresh (i : α) (f : (α → β) → ℝ) :
    (𝔼 x, 𝔼 y, f (Function.update x i y)) = 𝔼 x, f x := by
  classical
  have hswap := Fintype.expect_equiv (coordinateSwap (β := β) i)
    (fun z : (α → β) × β => f (Function.update z.1 i z.2))
    (fun z : (α → β) × β => f z.1) (fun _ => rfl)
  have hprod₁ := Finset.expect_product' (Finset.univ : Finset (α → β))
    (Finset.univ : Finset β) (fun x y => f (Function.update x i y))
  have hprod₂ := Finset.expect_product' (Finset.univ : Finset (α → β))
    (Finset.univ : Finset β) (fun x (_ : β) => f x)
  simpa only [Finset.univ_product_univ, Fintype.expect_const] using
    hprod₁.symm.trans (hswap.trans hprod₂)

theorem uniform_probability_eq_filter_card {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (E : Ω → Prop) [DecidablePred E] :
    ((PMF.uniformOfFintype Ω).toOuterMeasure {x | E x}).toReal =
      ((Finset.univ.filter E).card : ℝ) / Fintype.card Ω := by
  classical
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast]
  change (Fintype.card {x : Ω // E x} : ℝ) / (Fintype.card Ω : ℝ) = _
  congr 2
  exact Fintype.card_subtype E

end Balanced.DependencyExtraction

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalFiberBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Classical

namespace Balanced.LocalFiberBounds

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem line_fiber_card_le_one (S l : Line F) (hne : l ≠ S)
    (x : F → Point F) (hinj : Function.Injective x) (hx : ∀ t, OnLine (x t) S) :
    (Finset.univ.filter (fun t => OnLine (x t) l)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro t ht u hu
  apply hinj
  exact common_point_eq_of_lines_ne l S hne (x t) (x u)
    (Finset.mem_filter.mp ht).2 (hx t) (Finset.mem_filter.mp hu).2 (hx u)

theorem line_union_fiber_card_le (S : Line F) (L : Finset (Line F))
    (x : F → Point F) (hinj : Function.Injective x) (hx : ∀ t, OnLine (x t) S)
    (hne : ∀ l ∈ L, l ≠ S) :
    (Finset.univ.filter (fun t => ∃ l ∈ L, OnLine (x t) l)).card ≤ L.card := by
  have heq : Finset.univ.filter (fun t => ∃ l ∈ L, OnLine (x t) l) =
      L.biUnion (fun l => Finset.univ.filter (fun t => OnLine (x t) l)) := by
    ext t
    simp
  rw [heq]
  simpa using Finset.card_biUnion_le_card_mul L
    (fun l => Finset.univ.filter (fun t => OnLine (x t) l)) 1
    (fun l hl => line_fiber_card_le_one S l (hne l hl) x hinj hx)

theorem nonTarget_line_union_probability_le (S : Line F) (L : Finset (Line F))
    (x : F → Point F) (hinj : Function.Injective x) (hx : ∀ t, OnLine (x t) S) :
    ((PMF.uniformOfFintype F).toOuterMeasure
      {t | ∃ l ∈ L, l ≠ S ∧ OnLine (x t) l}).toReal ≤
        (L.card : ℝ) / Fintype.card F := by
  rw [DependencyExtraction.uniform_probability_eq_filter_card]
  have heq : Finset.univ.filter (fun t => ∃ l ∈ L, l ≠ S ∧ OnLine (x t) l) =
      Finset.univ.filter (fun t => ∃ l ∈ L.erase S, OnLine (x t) l) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    aesop
  rw [heq]
  have hcard := (line_union_fiber_card_le S (L.erase S) x hinj hx
    (fun l hl => (Finset.mem_erase.mp hl).1)).trans (Finset.card_le_card (Finset.erase_subset S L))
  exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) (by positivity)

end Balanced.LocalFiberBounds

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalUnusedOffsetProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.UnusedOffsetProbability

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open PrescribedGeometry

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] in

theorem offsetProbability_eq_expect (E : MergedPairs F → Prop) :
    offsetProbability E = 𝔼 M, if E M then (1 : ℝ) else 0 := by
  rw [Fintype.expect_eq_sum_div_card]
  rfl

variable {b κ : ℕ} {P : EqualityPattern b κ}
variable {a : DirectionAssignment F b κ} {bits : Bits b} {p : Point F}

omit [Fintype F] in

theorem prescribedPoint_eq_of_used_agreement (M N : MergedPairs F)
    (hMN : ∀ d ∈ Finset.univ.image a.2, M d = N d) (ij : Fin b × Fin 4) :
    prescribedPoint P a bits M ij = prescribedPoint P a bits N ij := by
  have hleft := hMN (a.2 (P.classOf ij.1 ij.2))
    (Finset.mem_image.mpr ⟨P.classOf ij.1 ij.2, Finset.mem_univ _, rfl⟩)
  have hright := hMN (a.2 (P.classOf ij.1 (ij.2 + 1)))
    (Finset.mem_image.mpr ⟨P.classOf ij.1 (ij.2 + 1), Finset.mem_univ _, rfl⟩)
  simp only [prescribedPoint, tuplePoint, prescribedTuple, constituent, hleft, hright]

theorem offsetProbability_nonneg (E : MergedPairs F → Prop) :
    0 ≤ offsetProbability E := by
  unfold offsetProbability
  positivity

omit [Field F] in

theorem offsetProbability_exists_le_sum {ι : Type*} [Fintype ι]
    (E : ι → MergedPairs F → Prop) :
    offsetProbability (fun M => ∃ i, E i M) ≤ ∑ i, offsetProbability (E i) := by
  simp_rw [offsetProbability_eq_expect]
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_le_expect
  intro M _
  by_cases h : ∃ i, E i M
  · obtain ⟨i, hi⟩ := h
    rw [ite_eq_left ⟨i, hi⟩]
    calc
      (1 : ℝ) = if E i M then 1 else 0 := by simp [hi]
      _ ≤ ∑ j, if E j M then (1 : ℝ) else 0 :=
        Finset.single_le_sum (f := fun j => if E j M then (1 : ℝ) else 0)
          (fun _ _ => by positivity) (Finset.mem_univ i)
  · rw [ite_eq_right h]
    positivity

end
end Balanced.Local.UnusedOffsetProbability

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_AlignedUsedObservable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.AlignedGlobal

open AlignedUnused TupleAlignment RootChildPartition
noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

omit [Field F] [Fintype F] in
theorem refreshUnused_unused (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (M : MergedPairs F) (u : UnusedArray P a)
    (d : {d : Direction F // d ∉ usedDirections P a}) :
    refreshUnused P a M u d.1 = u d := by
  exact congrFun (congrArg Prod.snd
    ((split P a).apply_symm_apply ((split P a M).1, u))) d

omit [Fintype F] in
theorem coordinates_refreshAligned (P : EqualityPattern b κ)
    (R : Finset (Fin b)) (a : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F) (M : AlignedOffsets P a bits p)
    (u : UnusedArray P a) :
    coordinates P R a bits p (refreshAligned P a bits p M u) =
      ((coordinates P R a bits p M).1, u) := by
  apply Prod.ext
  · funext ij
    apply congrArg (linePointEquiv (a.1 ij.1.1) (lineEval (a.1 ij.1.1) p))
    apply Subtype.ext
    exact UnusedOffsetProbability.prescribedPoint_eq_of_used_agreement
      _ _ (refreshUnused_used P a M.1 u) ij.1
  · funext d
    exact refreshUnused_unused P a M.1 u d

theorem generated_refresh (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a)
    (bits : Bits b) (p : Point F) (x : FreeIndex P R → F)
    (u v : UnusedArray P a) :
    refreshAligned P a bits p
      ((coordinateEquiv P hκ R hD a ha bits p).symm (x,u)) v =
      (coordinateEquiv P hκ R hD a ha bits p).symm (x,v) := by
  apply (coordinateEquiv P hκ R hD a ha bits p).injective
  rw [coordinateEquiv_apply, coordinates_refreshAligned]
  change ((coordinateEquiv P hκ R hD a ha bits p
    ((coordinateEquiv P hκ R hD a ha bits p).symm (x,u))).1, v) = _
  simp only [Equiv.apply_symm_apply]

theorem generated_used_agree (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a)
    (bits : Bits b) (p : Point F) (x : FreeIndex P R → F)
    (u v : UnusedArray P a) (d : Direction F) (hd : d ∈ usedDirections P a) :
    ((coordinateEquiv P hκ R hD a ha bits p).symm (x,u)).1 d =
      ((coordinateEquiv P hκ R hD a ha bits p).symm (x,v)).1 d := by
  rw [← generated_refresh P hκ R hD a ha bits p x u v]
  exact (refreshUnused_used P a _ v d hd).symm

theorem conditioned_probability_eq_uniform_free
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a)
    (bits : Bits b) (p : Point F) (E : MergedPairs F → Prop)
    (hE : ∀ M N, (∀ d ∈ usedDirections P a, M d = N d) → (E M ↔ E N)) :
    conditionedOffsetProbability (Aligned P a bits p) E =
      ((PMF.uniformOfFintype (FreeIndex P R → F)).toOuterMeasure
        {x | E (generatedZero P hκ R hD a ha bits p x)}).toReal := by
  rw [conditioned_probability_eq_uniform_coordinates P hκ R hD a ha bits p E]
  have heq : {z | E ((coordinateEquiv P hκ R hD a ha bits p).symm z).1} =
      Prod.fst ⁻¹' {x | E (generatedZero P hκ R hD a ha bits p x)} := by
    ext z
    exact hE _ _ (generated_used_agree P hκ R hD a ha bits p z.1 z.2 (fun _ _ => 0))
  rw [heq]
  have hm := congrArg (fun μ : PMF (FreeIndex P R → F) =>
      (μ.toOuterMeasure {x | E (generatedZero P hκ R hD a ha bits p x)}).toReal)
    (uniform_map_fst (α := FreeIndex P R → F) (β := UnusedArray P a))
  simpa only [PMF.toOuterMeasure_map_apply] using hm

end
end Balanced.Local.AlignedGlobal

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_AlignedHistoryKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.AlignedGlobal

open RootChildPartition InjectionExposure
noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

theorem generated_prefixObservation_eq (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R S : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (hS : S ⊆ R ∨ R ⊆ S)
    (a a' : DirectionAssignment F b κ) (ha : Eligible P a) (ha' : Eligible P a')
    (bits : Bits b) (p : Point F) (x : FreeIndex P R → F)
    (ht : ∀ i ∈ S, a.1 i = a'.1 i)
    (hd : ∀ c ∈ S.biUnion P.classSet, a.2 c = a'.2 c) :
    prefixObservation P S a bits (generatedZero P hκ R hD a ha bits p x) =
      prefixObservation P S a' bits (generatedZero P hκ R hD a' ha' bits p x) := by
  have h := generated_history_agree P hκ R S hD hS a a' ha ha' bits p x
    (fun _ _ => 0) (fun _ _ => 0) ht hd
  apply Prod.ext
  · funext i j
    exact h.1 i.1 i.2 j
  · funext c s
    apply Prod.ext
    · exact hd c.1 c.2
    · exact congrFun (h.2 c.1 c.2) s

theorem prefixNoise_dependsOnExposed (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R S : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (hS : S ⊆ R ∨ R ⊆ S) (bits : Bits b) (p : Point F)
    (K : Finset (DirectionToken b κ))
    (hKt : ∀ i ∈ S, Sum.inl i ∈ K)
    (hKg : ∀ c ∈ S.biUnion P.classSet, Sum.inr c ∈ K) :
    DependsOnExposed K (prefixNoise P hκ R S hD bits p) := by
  intro e f hef
  dsimp only [prefixNoise]
  congr 1
  funext x
  apply Prod.ext
  · rfl
  apply generated_prefixObservation_eq P hκ R S hD hS
  · intro i hi
    exact hef _ (hKt i hi)
  · intro c hc
    exact hef _ (hKg c hc)

theorem currentNoise_dependsOnExposed (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R S : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (hS : S ⊆ R ∨ R ⊆ S) (bits : Bits b) (p : Point F) (i : Fin b)
    (hphase : i ∈ R ∨ R ⊆ S)
    (K : Finset (DirectionToken b κ))
    (hKt : ∀ r ∈ S, Sum.inl r ∈ K)
    (hKg : ∀ c ∈ S.biUnion P.classSet, Sum.inr c ∈ K)
    (hi : Sum.inl i ∈ K) :
    DependsOnExposed K (currentNoise P hκ R S hD bits p i) := by
  intro e f hef
  let a := tokenInjectionEquiv F b κ e
  let a' := tokenInjectionEquiv F b κ f
  let ha := allTokensDistinct_eligible P a.1 a.2
  let ha' := allTokensDistinct_eligible P a'.1 a'.2
  have ht : ∀ r ∈ S, a.1.1 r = a'.1.1 r := fun r hr => hef _ (hKt r hr)
  have hd : ∀ c ∈ S.biUnion P.classSet, a.1.2 c = a'.1.2 c :=
    fun c hc => hef _ (hKg c hc)
  have hti : a.1.1 i = a'.1.1 i := hef _ hi
  dsimp only [currentNoise]
  congr 1
  funext x
  apply Prod.ext
  · rfl
  apply Prod.ext
  · exact generated_prefixObservation_eq P hκ R S hD hS a.1 a'.1 ha ha'
      bits p x ht hd
  · funext j
    rcases hphase with hir | hRS
    · apply free_point_eq_of_coordinate_eq P R a.1 a'.1 bits p
        ((coordinateEquiv P hκ R hD a.1 ha bits p).symm (x,fun _ _ => 0))
        ((coordinateEquiv P hκ R hD a'.1 ha' bits p).symm (x,fun _ _ => 0))
        (inverse_coordinates_fst_eq P hκ R hD a.1 a'.1 ha ha' bits p x
          (fun _ _ => 0) (fun _ _ => 0)) ⟨(i,j), ?_⟩ hti
      simp only [mem_dependentOccurrences, not_and]
      exact fun hn => (hn hir).elim
    · apply generated_point_eq_of_root_history P hκ R hD a.1 a'.1 ha ha'
        bits p x (fun _ _ => 0) (fun _ _ => 0)
        (fun r hr => ht r (hRS hr)) ?_ (i,j) hti
      intro c hc
      apply hd c
      obtain ⟨r, hr, hcr⟩ := Finset.mem_biUnion.mp hc
      exact Finset.mem_biUnion.mpr ⟨r, hRS hr, hcr⟩

end
end Balanced.Local.AlignedGlobal

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_InjectionExposureMixture
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.InjectionExposure
noncomputable section
open scoped Classical BigOperators
variable {I J Z : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem mem_completions_symm (K : Finset I) (e f : I ↪ J) :
    e ∈ completions K f ↔ f ∈ completions K e := by
  simp only [mem_completions]
  exact ⟨fun h j hj => (h j hj).symm, fun h j hj => (h j hj).symm⟩

theorem completions_eq_of_mem (K : Finset I) (e f : I ↪ J)
    (h : e ∈ completions K f) : completions K e = completions K f := by
  ext a
  simp only [mem_completions] at h ⊢
  exact ⟨fun ha j hj => (ha j hj).trans (h j hj),
    fun ha j hj => (ha j hj).trans (h j hj).symm⟩

variable [Nonempty (I ↪ J)]

theorem uniform_bind_completions (K : Finset I) :
    (PMF.uniformOfFintype (I ↪ J)).bind
      (fun e => PMF.uniformOfFinset (completions K e) (completions_nonempty K e)) =
        PMF.uniformOfFintype (I ↪ J) := by
  ext f
  rw [PMF.bind_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply]
  rw [← Finset.mul_sum]
  suffices hs : (∑ e : I ↪ J,
      PMF.uniformOfFinset (completions K e) (completions_nonempty K e) f) = 1 by
    rw [hs, mul_one]
  have heq : (∑ e : I ↪ J,
      PMF.uniformOfFinset (completions K e) (completions_nonempty K e) f) =
      ∑ e : I ↪ J, if e ∈ completions K f then
        ((completions K f).card : ENNReal)⁻¹ else 0 := by
    apply Finset.sum_congr rfl
    intro e _
    rw [PMF.uniformOfFinset_apply]
    by_cases h : e ∈ completions K f
    · have hf : f ∈ completions K e := (mem_completions_symm K e f).mp h
      rw [ite_eq_left hf, ite_eq_left h, completions_eq_of_mem K e f h]
    · have hf : f ∉ completions K e := fun hf => h ((mem_completions_symm K f e).mp hf)
      rw [ite_eq_right hf, ite_eq_right h]
  rw [heq]
  have hfilter : Finset.univ.filter (fun e => e ∈ completions K f) = completions K f := by
    ext e
    simp
  rw [← Finset.sum_filter, hfilter, Finset.sum_const, nsmul_eq_mul]
  exact ENNReal.mul_inv_cancel
    (by exact_mod_cast (completions_nonempty K f).card_pos.ne') (by simp)

theorem uniform_bind_auxiliaryLaw (K : Finset I)
    (noise : (I ↪ J) → PMF Z) :
    (PMF.uniformOfFintype (I ↪ J)).bind (fun e => auxiliaryLaw K e noise) =
      (PMF.uniformOfFintype (I ↪ J)).bind
        (fun e => (noise e).map (fun z => (e,z))) := by
  unfold auxiliaryLaw
  rw [← PMF.bind_bind, uniform_bind_completions]

theorem original_probability_eq_auxiliary_average (K : Finset I)
    (noise : (I ↪ J) → PMF Z) (E : Set ((I ↪ J) × Z)) :
    (((PMF.uniformOfFintype (I ↪ J)).bind
      (fun e => (noise e).map (fun z => (e,z)))).toOuterMeasure E).toReal =
      (∑ e : I ↪ J, ((auxiliaryLaw K e noise).toOuterMeasure E).toReal) /
        Fintype.card (I ↪ J) := by
  rw [← uniform_bind_auxiliaryLaw K noise, PMF.toOuterMeasure_bind_apply,
    tsum_fintype, ENNReal.toReal_sum]
  · simp_rw [ENNReal.toReal_mul, PMF.uniformOfFintype_apply,
      ENNReal.toReal_inv, ENNReal.toReal_natCast]
    rw [← Finset.mul_sum]
    ring
  · intro e _
    apply ENNReal.mul_ne_top ((PMF.uniformOfFintype (I ↪ J)).apply_ne_top e)
    rw [PMF.toOuterMeasure_apply]
    exact PMF.tsum_coe_indicator_ne_top _ _

theorem original_probability_le_of_auxiliary (K : Finset I)
    (noise : (I ↪ J) → PMF Z) (E : Set ((I ↪ J) × Z)) (B : ℝ)
    (h : ∀ e, ((auxiliaryLaw K e noise).toOuterMeasure E).toReal ≤ B) :
    (((PMF.uniformOfFintype (I ↪ J)).bind
      (fun e => (noise e).map (fun z => (e,z)))).toOuterMeasure E).toReal ≤ B := by
  rw [original_probability_eq_auxiliary_average K noise E]
  have hc : (0 : ℝ) < Fintype.card (I ↪ J) := by exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hc).mpr
  calc
    _ ≤ ∑ _e : I ↪ J, B := Finset.sum_le_sum (fun e _ => h e)
    _ = B * Fintype.card (I ↪ J) := by simp [mul_comm]

end
end Balanced.InjectionExposure

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_AlignedProjectedMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.TokenExposure
open AlignedListProbability PartialAlignment InjectionExposure
noncomputable section
open scoped Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ} {Z : Type*} [Fintype Z]
variable [Nonempty (DirectionToken b κ ↪ Direction F)]

theorem original_projected_left_probability_le_two_div
    (P : EqualityPattern b κ) (bits : Bits b) (p : Point F) (i : Fin b)
    (J : Finset (Fin 4)) (hJ : J.card ≤ 1) (j : Fin 4) (hj : j ∈ J)
    (K : Finset (DirectionToken b κ))
    (htarget : Sum.inl i ∉ K) (hold : Sum.inr (P.classOf i j) ∈ K)
    (noise : (DirectionToken b κ ↪ Direction F) → PMF Z)
    (hnoise : DependsOnExposed K noise)
    (a : Z → Fin 4 → Bool → F)
    (x : Z → {j : Fin 4 // j ∈ freePositions J} → F)
    (m : Z → Line F) (hK : K.card ≤ 5 * b)
    (hb : 10 * b ≤ Fintype.card F) :
    (((PMF.uniformOfFintype (DirectionToken b κ ↪ Direction F)).bind
      (fun e => (noise e).map (fun z => (e,z)))).toOuterMeasure
      {ez | (tupleDirections P ez.1 i j, a ez.2 j (bits i j)) ≠ m ez.2 ∧
        pointOutput P bits p i J hJ a x ez.1 ez.2 j ≠ p ∧
        OnLine (pointOutput P bits p i J hJ a x ez.1 ez.2 j) (m ez.2)}).toReal ≤
      2 / (Fintype.card F : ℝ) := by
  apply original_probability_le_of_auxiliary K noise
  intro base
  exact projected_left_probability_le_two_div P bits p i J hJ j hj K base
    htarget hold noise hnoise a x m hK hb

theorem original_projected_right_probability_le_two_div
    (P : EqualityPattern b κ) (bits : Bits b) (p : Point F) (i : Fin b)
    (J : Finset (Fin 4)) (hJ : J.card ≤ 1) (j : Fin 4) (hj : j+1 ∈ J)
    (K : Finset (DirectionToken b κ))
    (htarget : Sum.inl i ∉ K) (hold : Sum.inr (P.classOf i (j+1)) ∈ K)
    (noise : (DirectionToken b κ ↪ Direction F) → PMF Z)
    (hnoise : DependsOnExposed K noise)
    (a : Z → Fin 4 → Bool → F)
    (x : Z → {j : Fin 4 // j ∈ freePositions J} → F)
    (m : Z → Line F) (hK : K.card ≤ 5 * b)
    (hb : 10 * b ≤ Fintype.card F) :
    (((PMF.uniformOfFintype (DirectionToken b κ ↪ Direction F)).bind
      (fun e => (noise e).map (fun z => (e,z)))).toOuterMeasure
      {ez | (tupleDirections P ez.1 i (j+1), a ez.2 (j+1) (!(bits i (j+1)))) ≠ m ez.2 ∧
        pointOutput P bits p i J hJ a x ez.1 ez.2 j ≠ p ∧
        OnLine (pointOutput P bits p i J hJ a x ez.1 ez.2 j) (m ez.2)}).toReal ≤
      2 / (Fintype.card F : ℝ) := by
  apply original_probability_le_of_auxiliary K noise
  intro base
  exact projected_right_probability_le_two_div P bits p i J hJ j hj K base
    htarget hold noise hnoise a x m hK hb

end
end Balanced.Local.TokenExposure

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_AlignedGlobalProjectedIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.AlignedGlobal
open RootChildPartition PartialAlignment TokenExposure InjectionExposure
noncomputable section
open scoped Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

theorem projection_point_eq (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R S : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (bits : Bits b) (p : Point F) (e : DirectionToken b κ ↪ Direction F)
    (i : Fin b) (hJ : (currentOldIndices P R i).card ≤ 1)
    (hOld : ∀ j ∈ currentOldIndices P R i, P.classOf i j ∈ S.biUnion P.classSet)
    (x : FreeIndex P R → F) (j : Fin 4) :
    pointOutput P bits p i (currentOldIndices P R i) hJ
      (projectionOffsets P R S i) (projectionFree P R S i) e
      (projectionObservation P hκ R S hD bits p e x) j =
    prescribedPoint P (tokenInjectionEquiv F b κ e).1 bits
      (generatedZero P hκ R hD (tokenInjectionEquiv F b κ e).1
        (allTokensDistinct_eligible P _ (tokenInjectionEquiv F b κ e).2) bits p x) (i,j) := by
  apply pointOutput_eq_global P hκ R hD bits p e i hJ (x,fun _ _ => 0)
  · intro k hk
    funext s
    simp only [projectionOffsets, hOld k hk, dite_true, projectionObservation,
      prefixObservation, constituent, generatedZero, tokenInjectionEquiv]
    rfl
  · rfl

variable [Nonempty (DirectionToken b κ ↪ Direction F)]

theorem projection_joint_law (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R S : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (bits : Bits b) (p : Point F) :
    (PMF.uniformOfFintype ((DirectionToken b κ ↪ Direction F) × (FreeIndex P R → F))).map
      (fun ex => (ex.1,projectionObservation P hκ R S hD bits p ex.1 ex.2)) =
    (PMF.uniformOfFintype (DirectionToken b κ ↪ Direction F)).bind
      (fun e => (prefixNoise P hκ R S hD bits p e).map (fun z => (e,z))) := by
  rw [UniformConditionalProduct.uniform_product_eq_bind, PMF.map_bind]
  congr 1
  funext e
  simp only [prefixNoise, PMF.map_comp]
  rfl

theorem global_projected_left_probability_le_two_div
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R S : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (hS : S ⊆ R ∨ R ⊆ S) (bits : Bits b) (p : Point F)
    (i : Fin b) (hJ : (currentOldIndices P R i).card ≤ 1)
    (hOld : ∀ j ∈ currentOldIndices P R i, P.classOf i j ∈ S.biUnion P.classSet)
    (j : Fin 4) (hj : j ∈ currentOldIndices P R i)
    (K : Finset (DirectionToken b κ))
    (hKt : ∀ r ∈ S, Sum.inl r ∈ K)
    (hKg : ∀ c ∈ S.biUnion P.classSet, Sum.inr c ∈ K)
    (htarget : Sum.inl i ∉ K)
    (m : ProjectionData (F := F) P R S → Line F)
    (hK : K.card ≤ 5*b) (hb : 10*b ≤ Fintype.card F) :
    ((PMF.uniformOfFintype ((DirectionToken b κ ↪ Direction F) × (FreeIndex P R → F))).toOuterMeasure
      {ex | let a := tokenInjectionEquiv F b κ ex.1
            let M := generatedZero P hκ R hD a.1 (allTokensDistinct_eligible P a.1 a.2) bits p ex.2
            let z := projectionObservation P hκ R S hD bits p ex.1 ex.2
            constituent M (ex.1 (Sum.inr (P.classOf i j))) (bits i j) ≠ m z ∧
              prescribedPoint P a.1 bits M (i,j) ≠ p ∧
              OnLine (prescribedPoint P a.1 bits M (i,j)) (m z)}).toReal ≤
      2 / (Fintype.card F : ℝ) := by
  have h := original_projected_left_probability_le_two_div P bits p i
    (currentOldIndices P R i) hJ j hj K htarget (hKg _ (hOld j hj))
    (prefixNoise P hκ R S hD bits p)
    (prefixNoise_dependsOnExposed P hκ R S hD hS bits p K hKt hKg)
    (projectionOffsets P R S i) (projectionFree P R S i) m hK hb
  rw [← projection_joint_law P hκ R S hD bits p, PMF.toOuterMeasure_map_apply] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  ext ex
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, projection_point_eq P hκ R S hD bits p ex.1 i hJ hOld ex.2 j]
  simp only [projectionOffsets, hOld j hj, dite_true, projectionObservation,
    prefixObservation, tupleDirections, constituent, tokenInjectionEquiv]
  rfl

theorem global_projected_right_probability_le_two_div
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R S : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (hS : S ⊆ R ∨ R ⊆ S) (bits : Bits b) (p : Point F)
    (i : Fin b) (hJ : (currentOldIndices P R i).card ≤ 1)
    (hOld : ∀ j ∈ currentOldIndices P R i, P.classOf i j ∈ S.biUnion P.classSet)
    (j : Fin 4) (hj : j+1 ∈ currentOldIndices P R i)
    (K : Finset (DirectionToken b κ))
    (hKt : ∀ r ∈ S, Sum.inl r ∈ K)
    (hKg : ∀ c ∈ S.biUnion P.classSet, Sum.inr c ∈ K)
    (htarget : Sum.inl i ∉ K)
    (m : ProjectionData (F := F) P R S → Line F)
    (hK : K.card ≤ 5*b) (hb : 10*b ≤ Fintype.card F) :
    ((PMF.uniformOfFintype ((DirectionToken b κ ↪ Direction F) × (FreeIndex P R → F))).toOuterMeasure
      {ex | let a := tokenInjectionEquiv F b κ ex.1
            let M := generatedZero P hκ R hD a.1 (allTokensDistinct_eligible P a.1 a.2) bits p ex.2
            let z := projectionObservation P hκ R S hD bits p ex.1 ex.2
            constituent M (ex.1 (Sum.inr (P.classOf i (j+1)))) (!(bits i (j+1))) ≠ m z ∧
              prescribedPoint P a.1 bits M (i,j) ≠ p ∧
              OnLine (prescribedPoint P a.1 bits M (i,j)) (m z)}).toReal ≤
      2 / (Fintype.card F : ℝ) := by
  have h := original_projected_right_probability_le_two_div P bits p i
    (currentOldIndices P R i) hJ j hj K htarget (hKg _ (hOld (j+1) hj))
    (prefixNoise P hκ R S hD bits p)
    (prefixNoise_dependsOnExposed P hκ R S hD hS bits p K hKt hKg)
    (projectionOffsets P R S i) (projectionFree P R S i) m hK hb
  rw [← projection_joint_law P hκ R S hD bits p, PMF.toOuterMeasure_map_apply] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  ext ex
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, projection_point_eq P hκ R S hD bits p ex.1 i hJ hOld ex.2 j]
  simp only [projectionOffsets, hOld (j+1) hj, dite_true, projectionObservation,
    prefixObservation, tupleDirections, constituent, tokenInjectionEquiv]
  rfl

end
end Balanced.Local.AlignedGlobal

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_AlignedFreshCoordinate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.AlignedGlobal

open TupleAlignment RootChildPartition
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem uniform_coordinate_line_probability_le {I : Type*} [Fintype I]
    [DecidableEq I] (i : I) (S : Line F) (l : (I → F) → Line F)
    (hl : ∀ x t, l (Function.update x i t) = l x)
    (f : F → Point F) (hf : Function.Injective f) (hS : ∀ t, OnLine (f t) S) :
    ((PMF.uniformOfFintype (I → F)).toOuterMeasure
      {x | l x ≠ S ∧ OnLine (f (x i)) (l x)}).toReal ≤
      1 / (Fintype.card F : ℝ) := by
  rw [FiniteUniformFibers.probability_eq_sum, ← Fintype.expect_eq_sum_div_card,
    ← DependencyExtraction.expect_coordinate_refresh i]
  apply Finset.expect_le Finset.univ_nonempty
  intro x _
  simp_rw [hl, Function.update_self]
  have h := LocalFiberBounds.nonTarget_line_union_probability_le S {l x} f hf hS
  simp only [Finset.mem_singleton, exists_eq_left, Finset.card_singleton,
    Nat.cast_one] at h
  rw [FiniteUniformFibers.probability_eq_sum, ← Fintype.expect_eq_sum_div_card] at h
  refine le_trans (le_of_eq ?_) h; first
  | rfl
  | (apply Finset.expect_congr rfl; intro t _; split_ifs <;> rfl)

theorem generatedZero_free {b κ : ℕ} (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a)
    (bits : Bits b) (p : Point F) (x : FreeIndex P R → F) (ij : FreeIndex P R) :
    prescribedPoint P a bits (generatedZero P hκ R hD a ha bits p x) ij.1 =
      ((linePointEquiv (a.1 ij.1.1) (lineEval (a.1 ij.1.1) p)).symm (x ij)).1 :=
  generated_free P hκ R hD a ha bits p (x, fun _ _ => 0) ij

theorem generatedZero_fresh_incidence_le {b κ : ℕ}
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a)
    (bits : Bits b) (p : Point F) (ij : FreeIndex P R)
    (l : (FreeIndex P R → F) → Line F)
    (hl : ∀ x t, l (Function.update x ij t) = l x) :
    ((PMF.uniformOfFintype (FreeIndex P R → F)).toOuterMeasure
      {x | l x ≠ lineThrough (a.1 ij.1.1) p ∧
        OnLine (prescribedPoint P a bits (generatedZero P hκ R hD a ha bits p x) ij.1)
          (l x)}).toReal ≤ 1 / (Fintype.card F : ℝ) := by
  let f : F → Point F := fun t =>
    ((linePointEquiv (a.1 ij.1.1) (lineEval (a.1 ij.1.1) p)).symm t).1
  have heq : {x | l x ≠ lineThrough (a.1 ij.1.1) p ∧
      OnLine (prescribedPoint P a bits (generatedZero P hκ R hD a ha bits p x) ij.1) (l x)} =
      {x | l x ≠ lineThrough (a.1 ij.1.1) p ∧ OnLine (f (x ij)) (l x)} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    rw [generatedZero_free P hκ R hD a ha bits p x ij]
  rw [heq]
  apply uniform_coordinate_line_probability_le ij _ l hl f
  · intro t u h
    exact (linePointEquiv (a.1 ij.1.1) (lineEval (a.1 ij.1.1) p)).symm.injective
      (Subtype.ext h)
  · intro t
    exact ((linePointEquiv (a.1 ij.1.1) (lineEval (a.1 ij.1.1) p)).symm t).2

end
end Balanced.Local.AlignedGlobal

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalUnusedEventBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.UnusedOffsetProbability

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ} {P : EqualityPattern b κ}
variable {a : DirectionAssignment F b κ} {bits : Bits b} {p : Point F}

omit [Field F] in
theorem offsetProbability_mono {E G : MergedPairs F → Prop}
    (h : ∀ M, E M → G M) : offsetProbability E ≤ offsetProbability G := by
  unfold offsetProbability
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro M _
  by_cases hE : E M
  · simp only [hE, h M hE, ite_true]
    exact le_rfl
  · simp only [hE, ite_false]
    positivity

theorem conditionedOffsetProbability_mono (A : MergedPairs F → Prop)
    {E G : MergedPairs F → Prop} (h : ∀ M, E M → G M) :
    conditionedOffsetProbability A E ≤ conditionedOffsetProbability A G := by
  unfold conditionedOffsetProbability
  exact div_le_div_of_nonneg_right
    (offsetProbability_mono (fun M hM => ⟨hM.1, h M hM.2⟩))
    (offsetProbability_nonneg A)

end
end Balanced.Local.UnusedOffsetProbability

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalFourEventWitnesses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.FourEvents

noncomputable section
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

omit [Fintype F] [DecidableEq F] in

theorem common_line_eq_target_of_same_tuple (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M : MergedPairs F) (hal : Aligned P a bits p M)
    (i j : Fin b × Fin 4) (hij : i.1 = j.1)
    (hne : prescribedPoint P a bits M i ≠ prescribedPoint P a bits M j)
    (l : Line F) (hi : OnLine (prescribedPoint P a bits M i) l)
    (hj : OnLine (prescribedPoint P a bits M j) l) :
    l = lineThrough (a.1 i.1) p := by
  apply eq_of_two_common_points _ _ hne l _ hi hj (hal i)
  simpa only [hij] using hal j

theorem forbiddenCollinearTriple_indices (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M : MergedPairs F) (hal : Aligned P a bits p M)
    (h : ForbiddenCollinearTriple P a bits p M) :
    ∃ (l : Line F) (i j k : Fin b × Fin 4),
      i.1 ≠ j.1 ∧ i.1 ≠ k.1 ∧ j.1 ≠ k.1 ∧
      prescribedPoint P a bits M i ≠ prescribedPoint P a bits M j ∧
      prescribedPoint P a bits M i ≠ prescribedPoint P a bits M k ∧
      prescribedPoint P a bits M j ≠ prescribedPoint P a bits M k ∧
      OnLine (prescribedPoint P a bits M i) l ∧
      OnLine (prescribedPoint P a bits M j) l ∧
      OnLine (prescribedPoint P a bits M k) l ∧
      (∀ t, l ≠ lineThrough (a.1 t) p) ∧
      (∀ c s, l ≠ constituent M (a.2 c) s) := by
  obtain ⟨l, htarget, hconst, hcard⟩ := h
  obtain ⟨x,y,z,hx,hy,hz,hxy,hxz,hyz⟩ :=
    Finset.two_lt_card_iff.mp (show 2 <
      (prescribedDesignated P a bits M ∩ linePoints l).card by omega)
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hx).1
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hy).1
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hz).1
  have hi := (Finset.mem_filter.mp (Finset.mem_inter.mp hx).2).2
  have hj := (Finset.mem_filter.mp (Finset.mem_inter.mp hy).2).2
  have hk := (Finset.mem_filter.mp (Finset.mem_inter.mp hz).2).2
  refine ⟨l,i,j,k,?_,?_,?_,hxy,hxz,hyz,hi,hj,hk,htarget,hconst⟩
  · intro hij
    exact htarget i.1 (common_line_eq_target_of_same_tuple P a bits p M hal i j hij hxy l hi hj)
  · intro hik
    exact htarget i.1 (common_line_eq_target_of_same_tuple P a bits p M hal i k hik hxz l hi hk)
  · intro hjk
    exact htarget j.1 (common_line_eq_target_of_same_tuple P a bits p M hal j k hjk hyz l hj hk)

theorem usedPairExtra_iff_indices (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (M : MergedPairs F)
    (ha : Function.Injective a.2) :
    UsedPairExtra P a bits M ↔
      ∃ (c : Fin (4 * b - κ)) (i : Fin b × Fin 4) (s : Bool),
        (∀ j, P.classOf i.1 j ≠ c) ∧
        OnLine (prescribedPoint P a bits M i) (constituent M (a.2 c) s) := by
  constructor
  · rintro ⟨d, hd, i, hn, x, hx, hmerged⟩
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨j, rfl⟩ := (mem_tuplePoints P a bits M i x).mp hx
    have hnclass : ∀ k, P.classOf i k ≠ c := by
      intro k hk
      apply hn
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, k, congrArg a.2 hk⟩
    rcases Finset.mem_union.mp hmerged with hleft | hright
    · exact ⟨c,(i,j),false,hnclass,(Finset.mem_filter.mp hleft).2⟩
    · exact ⟨c,(i,j),true,hnclass,(Finset.mem_filter.mp hright).2⟩
  · rintro ⟨c,⟨i,j⟩,s,hn,hpoint⟩
    refine ⟨a.2 c, Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩,
      i, ?_, prescribedPoint P a bits M (i,j), ?_, ?_⟩
    · intro hi
      obtain ⟨k,hk⟩ := (Finset.mem_filter.mp hi).2
      exact hn k (ha hk)
    · exact (mem_tuplePoints P a bits M i _).mpr ⟨j,rfl⟩
    · have hm : prescribedPoint P a bits M (i,j) ∈ linePoints (constituent M (a.2 c) s) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpoint⟩
      cases s
      · exact Finset.mem_union_left _ hm
      · exact Finset.mem_union_right _ hm

theorem forbiddenCollinearTriple_joiningLine (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M : MergedPairs F) (hal : Aligned P a bits p M)
    (h : ForbiddenCollinearTriple P a bits p M) :
    ∃ i j k : Fin b × Fin 4,
      i.1 ≠ j.1 ∧ i.1 ≠ k.1 ∧ j.1 ≠ k.1 ∧
      prescribedPoint P a bits M i ≠ prescribedPoint P a bits M j ∧
      prescribedPoint P a bits M i ≠ prescribedPoint P a bits M k ∧
      prescribedPoint P a bits M j ≠ prescribedPoint P a bits M k ∧
      OnLine (prescribedPoint P a bits M k)
        (joiningLine (prescribedPoint P a bits M i) (prescribedPoint P a bits M j)) ∧
      (∀ t, joiningLine (prescribedPoint P a bits M i) (prescribedPoint P a bits M j) ≠
        lineThrough (a.1 t) p) ∧
      (∀ c s, joiningLine (prescribedPoint P a bits M i) (prescribedPoint P a bits M j) ≠
        constituent M (a.2 c) s) := by
  obtain ⟨l,i,j,k,hij,hik,hjk,hxy,hxz,hyz,hi,hj,hk,htarget,hconst⟩ :=
    forbiddenCollinearTriple_indices P a bits p M hal h
  have hl : l = joiningLine (prescribedPoint P a bits M i)
      (prescribedPoint P a bits M j) :=
    eq_of_two_common_points _ _ hxy _ _ hi hj
      (onLine_joiningLine_left _ _) (onLine_joiningLine_right _ _)
  subst l
  exact ⟨i,j,k,hij,hik,hjk,hxy,hxz,hyz,hk,htarget,hconst⟩

end
end Balanced.Local.FourEvents

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalUsedEventUnion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.UsedEventUnion

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

open UnusedOffsetProbability

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

theorem admissible_usedPairExtra_iff_exists
    (P : EqualityPattern b κ) (a : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F) (M : MergedPairs F)
    (ha : Function.Injective a.2) :
    (Admissible P a bits p M ∧ FourEvents.UsedPairExtra P a bits M) ↔
      ∃ z : UsedWitness b κ,
        usedConstituentTest P a bits p z.1 z.2.1 z.2.2 M := by
  constructor
  · rintro ⟨hA, hE⟩
    obtain ⟨c, ij, s, hn, hi⟩ :=
      (FourEvents.usedPairExtra_iff_indices P a bits M ha).mp hE
    exact ⟨(c, ij, s), hA, hn, hi⟩
  · rintro ⟨⟨c, ij, s⟩, hA, hn, hi⟩
    exact ⟨hA, (FourEvents.usedPairExtra_iff_indices P a bits M ha).mpr
      ⟨c, ij, s, hn, hi⟩⟩

theorem admissible_forbiddenTriple_imp_exists
    (P : EqualityPattern b κ) (a : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F) (M : MergedPairs F)
    (h : Admissible P a bits p M ∧
      FourEvents.ForbiddenCollinearTriple P a bits p M) :
    ∃ z : TripleWitness b, collinearTest P a bits p z.1 z.2.1 z.2.2 M := by
  obtain ⟨i, j, k, htest⟩ :=
    FourEvents.forbiddenCollinearTriple_joiningLine P a bits p M h.1.1 h.2
  exact ⟨(i, j, k), h.1, htest⟩

theorem conditionedOffsetProbability_exists_le_sum {ι : Type*} [Fintype ι]
    (A : MergedPairs F → Prop) (E : ι → MergedPairs F → Prop) :
    conditionedOffsetProbability A (fun M => ∃ i, E i M) ≤
      ∑ i, conditionedOffsetProbability A (E i) := by
  simp_rw [conditionedOffsetProbability, ← exists_and_left]
  rw [← Finset.sum_div]
  exact div_le_div_of_nonneg_right
    (offsetProbability_exists_le_sum (fun i M => A M ∧ E i M))
    (offsetProbability_nonneg A)

theorem alignedAverage_mono (P : EqualityPattern b κ) (bits : Bits b)
    (p : Point F) (w : DirectionAssignment F b κ → ℝ) (hw : ∀ a, 0 ≤ w a)
    {E G : DirectionAssignment F b κ → MergedPairs F → Prop}
    (h : ∀ a, w a ≠ 0 → ∀ M, E a M → G a M) :
    alignedAverage P bits p w E ≤ alignedAverage P bits p w G := by
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : w a = 0
  · simp only [ha, zero_mul, le_refl]
  · exact mul_le_mul_of_nonneg_left
      (conditionedOffsetProbability_mono _ (h a ha)) (hw a)

theorem alignedAverage_exists_le_sum {ι : Type*} [Fintype ι]
    (P : EqualityPattern b κ) (bits : Bits b) (p : Point F)
    (w : DirectionAssignment F b κ → ℝ) (hw : ∀ a, 0 ≤ w a)
    (E : ι → DirectionAssignment F b κ → MergedPairs F → Prop) :
    alignedAverage P bits p w (fun a M => ∃ i, E i a M) ≤
      ∑ i, alignedAverage P bits p w (E i) := by
  unfold alignedAverage
  calc
    (∑ a, w a * conditionedOffsetProbability (Aligned P a bits p)
        (fun M => ∃ i, E i a M)) ≤
        ∑ a, w a * ∑ i, conditionedOffsetProbability (Aligned P a bits p) (E i a) := by
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_left
        (conditionedOffsetProbability_exists_le_sum _ _) (hw a)
    _ = _ := by
      simp_rw [Finset.mul_sum]
      exact Finset.sum_comm

theorem card_usedWitness_le (b κ : ℕ) :
    Fintype.card (UsedWitness b κ) ≤ 32 * b ^ 2 := by
  simp only [UsedWitness, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  calc
    (4 * b - κ) * (b * 4 * 2) ≤ (4 * b) * (b * 4 * 2) :=
      Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    _ = _ := by ring

theorem card_tripleWitness (b : ℕ) :
    Fintype.card (TripleWitness b) = 64 * b ^ 3 := by
  simp only [TripleWitness, Fintype.card_prod, Fintype.card_fin]
  ring

theorem alignedAverage_usedPairExtra_le
    (P : EqualityPattern b κ) (bits : Bits b) (p : Point F)
    (w : DirectionAssignment F b κ → ℝ) (hw : ∀ a, 0 ≤ w a)
    (ha : ∀ a, w a ≠ 0 → Function.Injective a.2)
    {t : ℝ} (ht : 0 ≤ t)
    (htest : ∀ c ij s, alignedAverage P bits p w
      (fun a => usedConstituentTest P a bits p c ij s) ≤ t) :
    alignedAverage P bits p w
      (fun a M => Admissible P a bits p M ∧ FourEvents.UsedPairExtra P a bits M) ≤
        32 * (b : ℝ) ^ 2 * t := by
  have hmono := alignedAverage_mono P bits p w hw
    (fun a hwa M h => (admissible_usedPairExtra_iff_exists P a bits p M (ha a hwa)).mp h)
  apply hmono.trans
  apply (alignedAverage_exists_le_sum P bits p w hw
    (fun z : UsedWitness b κ => fun a =>
      usedConstituentTest P a bits p z.1 z.2.1 z.2.2)).trans
  calc
    (∑ z : UsedWitness b κ, alignedAverage P bits p w
        (fun a => usedConstituentTest P a bits p z.1 z.2.1 z.2.2)) ≤
        ∑ _z : UsedWitness b κ, t := Finset.sum_le_sum (fun z _ => htest z.1 z.2.1 z.2.2)
    _ = (Fintype.card (UsedWitness b κ) : ℝ) * t := by simp
    _ ≤ 32 * (b : ℝ) ^ 2 * t := by
      apply mul_le_mul_of_nonneg_right _ ht
      exact_mod_cast card_usedWitness_le b κ

theorem alignedAverage_forbiddenTriple_le
    (P : EqualityPattern b κ) (bits : Bits b) (p : Point F)
    (w : DirectionAssignment F b κ → ℝ) (hw : ∀ a, 0 ≤ w a)
    {t : ℝ}
    (htest : ∀ i j k, alignedAverage P bits p w
      (fun a => collinearTest P a bits p i j k) ≤ t) :
    alignedAverage P bits p w
      (fun a M => Admissible P a bits p M ∧
        FourEvents.ForbiddenCollinearTriple P a bits p M) ≤
        64 * (b : ℝ) ^ 3 * t := by
  have hmono := alignedAverage_mono P bits p w hw
    (fun a _ M h => admissible_forbiddenTriple_imp_exists P a bits p M h)
  apply hmono.trans
  apply (alignedAverage_exists_le_sum P bits p w hw
    (fun z : TripleWitness b => fun a => collinearTest P a bits p z.1 z.2.1 z.2.2)).trans
  calc
    (∑ z : TripleWitness b, alignedAverage P bits p w
        (fun a => collinearTest P a bits p z.1 z.2.1 z.2.2)) ≤
        ∑ _z : TripleWitness b, t := Finset.sum_le_sum (fun z _ => htest z.1 z.2.1 z.2.2)
    _ = (Fintype.card (TripleWitness b) : ℝ) * t := by simp
    _ = 64 * (b : ℝ) ^ 3 * t := by rw [card_tripleWitness]; push_cast; rfl

end
end Balanced.Local.UsedEventUnion

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_AlignedUsedTestTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.UsedEventUnion

open AlignedUnused AlignedGlobal RootChildPartition
noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

theorem admissible_usedGeometricGuards (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M : MergedPairs F) (h : Admissible P a bits p M) :
    usedGeometricGuards P a bits p M := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  intro i c s heq
  apply h.2.2.2.1 i
  rw [heq]
  exact Finset.mem_image.mpr ⟨(a.2 c,s), Finset.mem_univ _, rfl⟩

omit [Fintype F] in
theorem usedGeometricGuards_agree (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M N : MergedPairs F)
    (hMN : ∀ d ∈ usedDirections P a, M d = N d) :
    usedGeometricGuards P a bits p M ↔ usedGeometricGuards P a bits p N := by
  have hp : prescribedPoint P a bits M = prescribedPoint P a bits N := by
    funext ij
    exact UnusedOffsetProbability.prescribedPoint_eq_of_used_agreement (P := P) (bits := bits) M N hMN ij
  have hc (c : Fin (4*b-κ)) : M (a.2 c) = N (a.2 c) :=
    hMN _ (Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩)
  simp only [usedGeometricGuards, Aligned, hp, constituent, hc]

theorem usedConstituentTest_implies_geometric (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (c : Fin (4*b-κ)) (ij : Fin b × Fin 4) (s : Bool) (M : MergedPairs F)
    (h : usedConstituentTest P a bits p c ij s M) :
    geometricUsedTest P a bits p c ij s M :=
  ⟨admissible_usedGeometricGuards P a bits p M h.1, h.2⟩

theorem collinearTest_implies_geometric (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (i j k : Fin b × Fin 4) (M : MergedPairs F)
    (h : collinearTest P a bits p i j k M) :
    geometricCollinearTest P a bits p i j k M :=
  ⟨admissible_usedGeometricGuards P a bits p M h.1, h.2⟩

omit [Fintype F] in
theorem geometricUsedTest_agree (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (c : Fin (4*b-κ)) (ij : Fin b × Fin 4) (s : Bool)
    (M N : MergedPairs F) (hMN : ∀ d ∈ usedDirections P a, M d = N d) :
    geometricUsedTest P a bits p c ij s M ↔ geometricUsedTest P a bits p c ij s N := by
  have hp := UnusedOffsetProbability.prescribedPoint_eq_of_used_agreement (P := P) (bits := bits) M N hMN ij
  have hc := hMN _ (Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩)
  simp only [geometricUsedTest, usedGeometricGuards_agree P a bits p M N hMN,
    hp, constituent, hc]

omit [Fintype F] in
theorem geometricCollinearTest_agree (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (i j k : Fin b × Fin 4) (M N : MergedPairs F)
    (hMN : ∀ d ∈ usedDirections P a, M d = N d) :
    geometricCollinearTest P a bits p i j k M ↔
      geometricCollinearTest P a bits p i j k N := by
  have hp := UnusedOffsetProbability.prescribedPoint_eq_of_used_agreement (P := P) (bits := bits) M N hMN
  have hc (c : Fin (4*b-κ)) : M (a.2 c) = N (a.2 c) :=
    hMN _ (Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩)
  simp only [geometricCollinearTest, usedGeometricGuards_agree P a bits p M N hMN,
    hp, constituent, hc]

theorem conditioned_usedTest_le_uniform_free (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a)
    (bits : Bits b) (p : Point F) (c : Fin (4*b-κ)) (ij : Fin b × Fin 4) (s : Bool) :
    conditionedOffsetProbability (Aligned P a bits p)
      (usedConstituentTest P a bits p c ij s) ≤
      ((PMF.uniformOfFintype (FreeIndex P R → F)).toOuterMeasure
        {x | geometricUsedTest P a bits p c ij s
          (generatedZero P hκ R hD a ha bits p x)}).toReal := by
  exact (UnusedOffsetProbability.conditionedOffsetProbability_mono (Aligned P a bits p)
    (usedConstituentTest_implies_geometric P a bits p c ij s)).trans_eq
      (conditioned_probability_eq_uniform_free P hκ R hD a ha bits p _
        (geometricUsedTest_agree P a bits p c ij s))

theorem conditioned_collinearTest_le_uniform_free (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a)
    (bits : Bits b) (p : Point F) (i j k : Fin b × Fin 4) :
    conditionedOffsetProbability (Aligned P a bits p)
      (collinearTest P a bits p i j k) ≤
      ((PMF.uniformOfFintype (FreeIndex P R → F)).toOuterMeasure
        {x | geometricCollinearTest P a bits p i j k
          (generatedZero P hκ R hD a ha bits p x)}).toReal := by
  exact (UnusedOffsetProbability.conditionedOffsetProbability_mono (Aligned P a bits p)
    (collinearTest_implies_geometric P a bits p i j k)).trans_eq
      (conditioned_probability_eq_uniform_free P hκ R hD a ha bits p _
        (geometricCollinearTest_agree P a bits p i j k))

end
end Balanced.Local.UsedEventUnion

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_AlignedFreshHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.UsedEventUnion

open AlignedGlobal RootChildPartition
noncomputable section
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

theorem conditioned_fresh_usedTest_le
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R S : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (hS : S ⊆ R ∨ R ⊆ S)
    (a : DirectionAssignment F b κ) (ha : Eligible P a)
    (bits : Bits b) (p : Point F) (v : FreeIndex P R) (hv : v.1.1 ∉ S)
    (c : Fin (4*b-κ)) (hc : c ∈ S.biUnion P.classSet) (s : Bool) :
    conditionedOffsetProbability (Aligned P a bits p)
      (usedConstituentTest P a bits p c v.1 s) ≤ 1 / (Fintype.card F : ℝ) := by
  let M := generatedZero P hκ R hD a ha bits p
  let l : (FreeIndex P R → F) → Line F := fun x => constituent (M x) (a.2 c) s
  have hl : ∀ x t, l (Function.update x v t) = l x := by
    intro x t
    have h := (generated_history_update P hκ R S hD hS a ha bits p x
      (fun _ _ => 0) v hv t).2 c hc
    change M x (a.2 c) = M (Function.update x v t) (a.2 c) at h
    change (a.2 c, M (Function.update x v t) (a.2 c) s) = (a.2 c, M x (a.2 c) s)
    rw [← h]
  have hb := generatedZero_fresh_incidence_le P hκ R hD a ha bits p v l hl
  apply (conditioned_usedTest_le_uniform_free P hκ R hD a ha bits p c v.1 s).trans
  apply le_trans _ hb
  apply ENNReal.toReal_mono
  · rw [PMF.toOuterMeasure_apply]
    exact PMF.tsum_coe_indicator_ne_top _ _
  · apply (PMF.uniformOfFintype (FreeIndex P R → F)).toOuterMeasure.mono
    intro x hx
    exact ⟨(hx.1.2.2.2 v.1.1 c s).symm, hx.2.2⟩

theorem conditioned_fresh_collinearTest_le
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R S : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (hS : S ⊆ R ∨ R ⊆ S)
    (a : DirectionAssignment F b κ) (ha : Eligible P a)
    (bits : Bits b) (p : Point F) (v : FreeIndex P R) (hv : v.1.1 ∉ S)
    (i j : Fin b × Fin 4) (hi : i.1 ∈ S) (hj : j.1 ∈ S) :
    conditionedOffsetProbability (Aligned P a bits p)
      (collinearTest P a bits p i j v.1) ≤ 1 / (Fintype.card F : ℝ) := by
  let M := generatedZero P hκ R hD a ha bits p
  let l : (FreeIndex P R → F) → Line F := fun x =>
    joiningLine (prescribedPoint P a bits (M x) i) (prescribedPoint P a bits (M x) j)
  have hl : ∀ x t, l (Function.update x v t) = l x := by
    intro x t
    have h := (generated_history_update P hκ R S hD hS a ha bits p x
      (fun _ _ => 0) v hv t).1
    have hi' := h i.1 hi i.2
    have hj' := h j.1 hj j.2
    change prescribedPoint P a bits (M x) i =
      prescribedPoint P a bits (M (Function.update x v t)) i at hi'
    change prescribedPoint P a bits (M x) j =
      prescribedPoint P a bits (M (Function.update x v t)) j at hj'
    exact congrArg₂ joiningLine hi'.symm hj'.symm
  have hb := generatedZero_fresh_incidence_le P hκ R hD a ha bits p v l hl
  apply (conditioned_collinearTest_le_uniform_free P hκ R hD a ha bits p i j v.1).trans
  apply le_trans _ hb
  apply ENNReal.toReal_mono
  · rw [PMF.toOuterMeasure_apply]
    exact PMF.tsum_coe_indicator_ne_top _ _
  · apply (PMF.uniformOfFintype (FreeIndex P R → F)).toOuterMeasure.mono
    intro x hx
    obtain ⟨hA, hij, hiv, hjv, hxy, hxv, hyv, hhit, htarget, hconst⟩ := hx
    exact ⟨htarget v.1.1, hhit⟩

end
end Balanced.Local.UsedEventUnion

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalAsymptotics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology BigOperators

namespace Balanced.LocalAsymptotics

theorem tendsto_log_pow_div (a : ℕ) :
    Tendsto (fun x : ℝ => (Real.log x) ^ a / x) atTop (𝓝 0) := by
  have h := isLittleO_log_rpow_rpow_atTop (a : ℝ) (by norm_num : (0 : ℝ) < 1)
  simpa only [Real.rpow_natCast, Real.rpow_one] using h.tendsto_div_nhds_zero

theorem tendsto_ceil_log_pow_div (a : ℕ) :
    Tendsto (fun x : ℝ => (⌈Real.log x⌉₊ : ℝ) ^ a / x) atTop (𝓝 0) := by
  have hlog : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually_ge_atTop 1
  have hx : ∀ᶠ x : ℝ in atTop, 0 ≤ x := eventually_ge_atTop 0
  apply squeeze_zero' (hx.mono fun x hx => by positivity)
    (g := fun x : ℝ => (2 : ℝ) ^ a * ((Real.log x) ^ a / x))
  · filter_upwards [hlog, hx] with x hlog hx
    have hceil : (⌈Real.log x⌉₊ : ℝ) ≤ 2 * Real.log x := by
      have h := Nat.ceil_lt_add_one (le_trans (by norm_num : (0 : ℝ) ≤ 1) hlog)
      linarith
    calc
      (⌈Real.log x⌉₊ : ℝ) ^ a / x ≤ (2 * Real.log x) ^ a / x := by gcongr
      _ = (2 : ℝ) ^ a * ((Real.log x) ^ a / x) := by rw [mul_pow]; ring
  · simpa using (tendsto_log_pow_div a).const_mul ((2 : ℝ) ^ a)

end Balanced.LocalAsymptotics

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalInjectionBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology

namespace Balanced.LocalAsymptotics

theorem eventually_mul_ceil_log_le (c : ℕ) :
    ∀ᶠ q : ℕ in atTop, c * ⌈Real.log (q : ℝ)⌉₊ ≤ q := by
  have hlim : Tendsto (fun q : ℕ =>
      (c : ℝ) * (⌈Real.log (q : ℝ)⌉₊ : ℝ) / (q : ℝ)) atTop (𝓝 0) := by
    simpa only [pow_one, mul_div_assoc, Function.comp_def, mul_zero] using
      ((tendsto_ceil_log_pow_div 1).comp tendsto_natCast_atTop_atTop).const_mul (c : ℝ)
  filter_upwards [hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop (0 : ℕ)] with q hq hpos
  have hqr : (0 : ℝ) < q := by exact_mod_cast hpos
  have hbound : (c : ℝ) * (⌈Real.log (q : ℝ)⌉₊ : ℝ) ≤ q :=
    ((div_lt_one hqr).mp hq).le
  exact_mod_cast hbound

end Balanced.LocalAsymptotics

namespace Balanced.Local

universe u

theorem exists_logBudget_token_threshold :
    ∃ q₀ : ℕ, ∀ (F : Type u) [Fintype F], q₀ ≤ Fintype.card F →
      ∀ b : ℕ, b ≤ logBudget F → 10 * b ≤ Fintype.card F := by
  obtain ⟨q₀, hq₀⟩ := Filter.eventually_atTop.mp
    (LocalAsymptotics.eventually_mul_ceil_log_le 10)
  refine ⟨q₀, ?_⟩
  intro F _ hF b hb
  exact (Nat.mul_le_mul_left 10 hb).trans (hq₀ (Fintype.card F) hF)

end Balanced.Local

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalTwoReuseMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.TwoReuseAssembly
noncomputable section
open scoped BigOperators Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
omit [Field F] [DecidableEq F] in
theorem sum_allTokensDistinct_eq {b κ : ℕ}
    (f : DirectionAssignment F b κ → ℝ) :
    (∑ a : DirectionAssignment F b κ, if AllTokensDistinct a then f a else 0) =
      ∑ e : DirectionToken b κ ↪ Direction F, f (tokenInjectionEquiv F b κ e).1 := by
  calc
    _ = ∑ a ∈ (Finset.univ.filter (fun a : DirectionAssignment F b κ => AllTokensDistinct a)), f a := by
      rw [Finset.sum_filter]
    _ = ∑ a : {a : DirectionAssignment F b κ // AllTokensDistinct a}, f a.1 := by
      exact Finset.sum_subtype _ (by simp) _
    _ = _ := (Equiv.sum_comp (tokenInjectionEquiv F b κ) (fun a => f a.1)).symm

universe u

end
end Balanced.Local.TwoReuseAssembly

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalTwoReuseUsedEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.TwoReuseAssembly
noncomputable section
open scoped Classical BigOperators

theorem mean_le_mean_add {I : Type*} [Fintype I]
    (f g : I → ℝ) (B : ℝ) (hB : 0 ≤ B) (h : ∀ i, f i ≤ g i + B) :
    (∑ i, f i) / Fintype.card I ≤ (∑ i, g i) / Fintype.card I + B := by
  by_cases hc : Fintype.card I = 0
  · simpa [hc] using hB
  have hcR : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast hc
  calc
    _ ≤ (∑ i, (g i + B)) / Fintype.card I :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun i _ => h i)) (Nat.cast_nonneg _)
    _ = _ := by rw [Finset.sum_add_distrib]; simp; field_simp

universe u

end
end Balanced.Local.TwoReuseAssembly

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalUsedEventMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.UsedEventUnion

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

omit [Field F] [DecidableEq F] in
theorem injectionWeight_nonneg (a : DirectionAssignment F b κ) :
    0 ≤ injectionWeight F b κ a := by
  unfold injectionWeight
  split_ifs <;> positivity

omit [Field F] [DecidableEq F] in
theorem injectionWeight_support (a : DirectionAssignment F b κ)
    (ha : injectionWeight F b κ a ≠ 0) : AllTokensDistinct a := by
  by_contra h
  exact ha (by simp [injectionWeight, h])

theorem injectionAverage_eq_alignedAverage
    (P : EqualityPattern b κ) (bits : Bits b) (p : Point F)
    (E : DirectionAssignment F b κ → MergedPairs F → Prop) :
    injectionAverage P bits p E = alignedAverage P bits p (injectionWeight F b κ) E := by
  unfold injectionAverage alignedAverage injectionWeight
  rw [← TwoReuseAssembly.sum_allTokensDistinct_eq
    (fun a => conditionedOffsetProbability (Aligned P a bits p) (E a))]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : AllTokensDistinct a
  · simp only [ha, ite_true, div_eq_mul_inv, mul_comm]
  · simp only [ha, ite_false, zero_div, zero_mul]

theorem usedEventMean_eq_injectionAverage
    (P : EqualityPattern b 2) (bits : Bits b) (p : Point F) :
    TwoReuseAssembly.usedEventMean P bits p =
      injectionAverage P bits p
        (fun a M => Admissible P a bits p M ∧ FourEvents.UsedPairExtra P a bits M) +
      injectionAverage P bits p
        (fun a M => Admissible P a bits p M ∧
          FourEvents.ForbiddenCollinearTriple P a bits p M) := by
  simp only [TwoReuseAssembly.usedEventMean, TwoReuseAssembly.usedEventConditionalMass,
    injectionAverage, Finset.sum_add_distrib, add_div]

theorem usedEventMean_le_of_test_bounds
    (P : EqualityPattern b 2) (bits : Bits b) (p : Point F) (hb : 1 ≤ b)
    (hused : ∀ c ij s, injectionAverage P bits p
      (fun a => usedConstituentTest P a bits p c ij s) ≤ 2 / (Fintype.card F : ℝ))
    (htriple : ∀ i j k, injectionAverage P bits p
      (fun a => collinearTest P a bits p i j k) ≤ 2 / (Fintype.card F : ℝ)) :
    TwoReuseAssembly.usedEventMean P bits p ≤
      192 * (b : ℝ) ^ 3 / Fintype.card F := by
  have h₂ := alignedAverage_usedPairExtra_le P bits p (injectionWeight F b 2)
    injectionWeight_nonneg
    (fun a ha => (allTokensDistinct_eligible P a (injectionWeight_support a ha)).2.1)
    (show 0 ≤ 2 / (Fintype.card F : ℝ) by positivity)
    (fun c ij s => by rw [← injectionAverage_eq_alignedAverage]; exact hused c ij s)
  have h₃ := alignedAverage_forbiddenTriple_le P bits p (injectionWeight F b 2)
    injectionWeight_nonneg
    (fun i j k => by rw [← injectionAverage_eq_alignedAverage]; exact htriple i j k)
  rw [← injectionAverage_eq_alignedAverage] at h₂ h₃
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hpow : (b : ℝ) ^ 2 ≤ (b : ℝ) ^ 3 := by
    nlinarith [sq_nonneg (b : ℝ)]
  rw [usedEventMean_eq_injectionAverage]
  calc
    _ ≤ 32 * (b : ℝ) ^ 2 * (2 / (Fintype.card F : ℝ)) +
        64 * (b : ℝ) ^ 3 * (2 / (Fintype.card F : ℝ)) := add_le_add h₂ h₃
    _ ≤ 32 * (b : ℝ) ^ 3 * (2 / (Fintype.card F : ℝ)) +
        64 * (b : ℝ) ^ 3 * (2 / (Fintype.card F : ℝ)) := by
      gcongr
    _ = _ := by ring

universe u

end
end Balanced.Local.UsedEventUnion

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalInjectionLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.UsedEventUnion

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem uniform_bind_probability_eq_mean {I Ω : Type*} [Fintype I] [Nonempty I]
    (ν : I → PMF Ω) (E : I × Ω → Prop) :
    (((PMF.uniformOfFintype I).bind (fun i => (ν i).map (fun ω => (i, ω)))).toOuterMeasure
      {z | E z}).toReal =
      (∑ i, ((ν i).toOuterMeasure {ω | E (i, ω)}).toReal) / Fintype.card I := by
  rw [PMF.toOuterMeasure_bind_apply, tsum_fintype, ENNReal.toReal_sum]
  · simp_rw [ENNReal.toReal_mul, PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, PMF.toOuterMeasure_map_apply]
    rw [← Finset.mul_sum]
    simp only [Set.preimage_ofPred_eq]
    ring
  · intro i _
    apply ENNReal.mul_ne_top ((PMF.uniformOfFintype I).apply_ne_top i)
    rw [PMF.toOuterMeasure_apply]
    exact PMF.tsum_coe_indicator_ne_top _ _

end
end Balanced.Local.UsedEventUnion

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalInjectionFreeLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.UsedEventUnion

noncomputable section
open scoped BigOperators
open AlignedGlobal RootChildPartition
attribute [local instance] Classical.propDecidable

theorem uniform_product_probability_eq_mean {I Ω : Type*}
    [Fintype I] [Nonempty I] [Fintype Ω] [Nonempty Ω]
    (E : I → Ω → Prop) :
    ((PMF.uniformOfFintype (I × Ω)).toOuterMeasure {z | E z.1 z.2}).toReal =
      (∑ i, ((PMF.uniformOfFintype Ω).toOuterMeasure {ω | E i ω}).toReal) /
        Fintype.card I := by
  rw [UniformConditionalProduct.uniform_product_eq_bind,
    uniform_bind_probability_eq_mean]

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

theorem injectionAverage_le_injectionFreeProbability
    (P : EqualityPattern b κ) (R : Finset (Fin b)) (bits : Bits b) (p : Point F)
    [Nonempty (DirectionToken b κ ↪ Direction F)]
    (E : DirectionAssignment F b κ → MergedPairs F → Prop)
    (G : (DirectionToken b κ ↪ Direction F) → (FreeIndex P R → F) → Prop)
    (h : ∀ e : DirectionToken b κ ↪ Direction F,
      conditionedOffsetProbability (Aligned P (tokenInjectionEquiv F b κ e).1 bits p)
        (E (tokenInjectionEquiv F b κ e).1) ≤
      ((PMF.uniformOfFintype (FreeIndex P R → F)).toOuterMeasure {x | G e x}).toReal) :
    injectionAverage P bits p E ≤ injectionFreeProbability P R G := by
  unfold injectionFreeProbability injectionAverage
  rw [uniform_product_probability_eq_mean]
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun e _ => h e))
    (Nat.cast_nonneg _)

theorem usedTest_injectionAverage_le_free
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2 * κ)
    (bits : Bits b) (p : Point F)
    [Nonempty (DirectionToken b κ ↪ Direction F)]
    (c : Fin (4 * b - κ)) (ij : Fin b × Fin 4) (s : Bool) :
    injectionAverage P bits p (fun a => usedConstituentTest P a bits p c ij s) ≤
      injectionFreeProbability P R (fun e x =>
        geometricUsedTest P (tokenInjectionEquiv F b κ e).1 bits p c ij s
          (injectedGenerated P hκ R hD bits p e x)) := by
  apply injectionAverage_le_injectionFreeProbability
  intro e
  exact conditioned_usedTest_le_uniform_free P hκ R hD _
    (allTokensDistinct_eligible P _ (tokenInjectionEquiv F b κ e).2) bits p c ij s

theorem collinearTest_injectionAverage_le_free
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2 * κ)
    (bits : Bits b) (p : Point F)
    [Nonempty (DirectionToken b κ ↪ Direction F)]
    (i j k : Fin b × Fin 4) :
    injectionAverage P bits p (fun a => collinearTest P a bits p i j k) ≤
      injectionFreeProbability P R (fun e x =>
        geometricCollinearTest P (tokenInjectionEquiv F b κ e).1 bits p i j k
          (injectedGenerated P hκ R hD bits p e x)) := by
  apply injectionAverage_le_injectionFreeProbability
  intro e
  exact conditioned_collinearTest_le_uniform_free P hκ R hD _
    (allTokensDistinct_eligible P _ (tokenInjectionEquiv F b κ e).2) bits p i j k

end
end Balanced.Local.UsedEventUnion

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_AlignedGlobalEarlyUsedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.AlignedGlobal

open RootChildPartition UsedEventUnion
noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

omit [Fintype F] [DecidableEq F] in

theorem geometricUsedTest_constituent_ne
    (P : EqualityPattern b κ) (bits : Bits b) (p : Point F)
    (e : DirectionToken b κ ↪ Direction F) (M : MergedPairs F)
    (c : Fin (4*b-κ)) (ij : Fin b × Fin 4) (s : Bool)
    (h : geometricUsedTest P (tokenInjectionEquiv F b κ e).1 bits p c ij s M)
    (j : Fin 4) (t : Bool) :
    constituent M (e (Sum.inr (P.classOf ij.1 j))) t ≠
      constituent M ((tokenInjectionEquiv F b κ e).1.2 c) s := by
  intro heq
  have hd : e (Sum.inr (P.classOf ij.1 j)) = e (Sum.inr c) :=
    congrArg Prod.fst heq
  exact h.2.1 j (Sum.inr.inj (e.injective hd))

variable [Nonempty (DirectionToken b κ ↪ Direction F)]

theorem geometricUsedTest_projected_le
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R S : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (hS : S ⊆ R ∨ R ⊆ S) (bits : Bits b) (p : Point F)
    (i : Fin b) (hJ : (currentOldIndices P R i).card ≤ 1)
    (hOld : ∀ j ∈ currentOldIndices P R i, P.classOf i j ∈ S.biUnion P.classSet)
    (j : Fin 4) (hdep : (i,j) ∈ dependentOccurrences P R)
    (K : Finset (DirectionToken b κ))
    (hKt : ∀ r ∈ S, Sum.inl r ∈ K)
    (hKg : ∀ c ∈ S.biUnion P.classSet, Sum.inr c ∈ K)
    (htarget : Sum.inl i ∉ K)
    (c : Fin (4*b-κ)) (hc : c ∈ S.biUnion P.classSet) (s : Bool)
    (hK : K.card ≤ 5*b) (hb : 10*b ≤ Fintype.card F) :
    injectionFreeProbability P R (fun e x =>
      geometricUsedTest P (tokenInjectionEquiv F b κ e).1 bits p c (i,j) s
        (injectedGenerated P hκ R hD bits p e x)) ≤
      2 / (Fintype.card F : ℝ) := by
  let m : ProjectionData (F := F) P R S → Line F := fun z => z.2.2 ⟨c,hc⟩ s
  have hdep' := (mem_dependentOccurrences P R (i,j)).mp hdep
  rcases hdep'.2 with hl | hr
  · have hj : j ∈ currentOldIndices P R i := by
      simp only [currentOldIndices, ite_eq_right hdep'.1, rootGeneratorIndices,
        Finset.mem_filter, Finset.mem_univ, true_and]
      exact hl
    have hbound := global_projected_left_probability_le_two_div P hκ R S hD hS
      bits p i hJ hOld j hj K hKt hKg htarget m hK hb
    apply le_trans _ hbound
    unfold injectionFreeProbability
    apply ENNReal.toReal_mono
    · rw [PMF.toOuterMeasure_apply]
      exact PMF.tsum_coe_indicator_ne_top _ _
    · apply (PMF.uniformOfFintype ((DirectionToken b κ ↪ Direction F) ×
        (FreeIndex P R → F))).toOuterMeasure.mono
      intro ex hx
      change geometricUsedTest P (tokenInjectionEquiv F b κ ex.1).1 bits p c (i,j) s
        (injectedGenerated P hκ R hD bits p ex.1 ex.2) at hx
      exact ⟨geometricUsedTest_constituent_ne P bits p ex.1 _ c (i,j) s hx j (bits i j),
        hx.1.2.2.1 (i,j), hx.2.2⟩
  · have hj : j+1 ∈ currentOldIndices P R i := by
      simp only [currentOldIndices, ite_eq_right hdep'.1, rootGeneratorIndices,
        Finset.mem_filter, Finset.mem_univ, true_and]
      exact hr
    have hbound := global_projected_right_probability_le_two_div P hκ R S hD hS
      bits p i hJ hOld j hj K hKt hKg htarget m hK hb
    apply le_trans _ hbound
    unfold injectionFreeProbability
    apply ENNReal.toReal_mono
    · rw [PMF.toOuterMeasure_apply]
      exact PMF.tsum_coe_indicator_ne_top _ _
    · apply (PMF.uniformOfFintype ((DirectionToken b κ ↪ Direction F) ×
        (FreeIndex P R → F))).toOuterMeasure.mono
      intro ex hx
      change geometricUsedTest P (tokenInjectionEquiv F b κ ex.1).1 bits p c (i,j) s
        (injectedGenerated P hκ R hD bits p ex.1 ex.2) at hx
      exact ⟨geometricUsedTest_constituent_ne P bits p ex.1 _ c (i,j) s hx
          (j+1) (!(bits i (j+1))), hx.1.2.2.1 (i,j), hx.2.2⟩

theorem usedTest_injectionAverage_projected_le
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R S : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (hS : S ⊆ R ∨ R ⊆ S) (bits : Bits b) (p : Point F)
    (i : Fin b) (hJ : (currentOldIndices P R i).card ≤ 1)
    (hOld : ∀ j ∈ currentOldIndices P R i, P.classOf i j ∈ S.biUnion P.classSet)
    (j : Fin 4) (hdep : (i,j) ∈ dependentOccurrences P R)
    (K : Finset (DirectionToken b κ))
    (hKt : ∀ r ∈ S, Sum.inl r ∈ K)
    (hKg : ∀ c ∈ S.biUnion P.classSet, Sum.inr c ∈ K)
    (htarget : Sum.inl i ∉ K)
    (c : Fin (4*b-κ)) (hc : c ∈ S.biUnion P.classSet) (s : Bool)
    (hK : K.card ≤ 5*b) (hb : 10*b ≤ Fintype.card F) :
    injectionAverage P bits p (fun a => usedConstituentTest P a bits p c (i,j) s) ≤
      2 / (Fintype.card F : ℝ) :=
  (usedTest_injectionAverage_le_free P hκ R hD bits p c (i,j) s).trans
    (geometricUsedTest_projected_le P hκ R S hD hS bits p i hJ hOld j hdep
      K hKt hKg htarget c hc s hK hb)

end
end Balanced.Local.AlignedGlobal

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_AlignedGlobalGeneratorTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.AlignedGlobal
open RootChildPartition InjectionExposure TokenExposure UsedEventUnion
noncomputable section
open scoped Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

omit [Fintype F] [DecidableEq F] in

theorem constituent_eq_purposeful_line (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a)
    (bits : Bits b) (M : MergedPairs F) (i : Fin b) (j : Fin 4) (s : Bool) :
    constituent M (a.2 (P.classOf i j)) s =
      lineThrough (a.2 (P.classOf i j))
        (prescribedPoint P a bits M (i,purposefulIndex (bits i) j s)) := by
  apply line_eq_lineThrough
  unfold purposefulIndex
  split_ifs with hs
  · simpa only [hs] using PrescribedGeometry.prescribedPoint_on_left (M := M) ha i j
  · have hs' : s = !(bits i j) := by
      cases s <;> cases h : bits i j <;> simp_all
    have hj : j - 1 + 1 = j := by fin_cases j <;> decide
    simpa only [hj, hs'] using
      PrescribedGeometry.prescribedPoint_on_right (M := M) ha i (j-1)

variable [Nonempty (DirectionToken b κ ↪ Direction F)]

theorem global_later_generator_probability_le
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R S : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (hS : S ⊆ R ∨ R ⊆ S) (bits : Bits b) (p : Point F) (i : Fin b)
    (hphase : i ∈ R ∨ R ⊆ S)
    (K : Finset (DirectionToken b κ))
    (hKt : ∀ r ∈ S, Sum.inl r ∈ K)
    (hKg : ∀ c ∈ S.biUnion P.classSet, Sum.inr c ∈ K)
    (hi : Sum.inl i ∈ K) (j : Fin 4)
    (hnew : Sum.inr (P.classOf i j) ∉ K) (s : Bool)
    (r : {r : Fin b // r ∈ S}) (t : Fin 4)
    (hK : K.card ≤ 5*b) (hb : 10*b ≤ Fintype.card F) :
    injectionFreeProbability P R (fun e x =>
      let a := (tokenInjectionEquiv F b κ e).1
      let M := injectedGenerated P hκ R hD bits p e x
      prescribedPoint P a bits M (i,purposefulIndex (bits i) j s) ≠
        prescribedPoint P a bits M (r.1,t) ∧
      OnLine (prescribedPoint P a bits M (r.1,t))
        (constituent M (a.2 (P.classOf i j)) s)) ≤
      2 / (Fintype.card F : ℝ) := by
  let noise := currentNoise P hκ R S hD bits p i
  let endpoint := fun z : (FreeIndex P R → F) ×
      (PrefixData F P S × (Fin 4 → Point F)) =>
      z.2.2 (purposefulIndex (bits i) j s)
  let previous := fun z : (FreeIndex P R → F) ×
      (PrefixData F P S × (Fin 4 → Point F)) => z.2.1.1 r t
  let E : Set ((DirectionToken b κ ↪ Direction F) ×
      ((FreeIndex P R → F) × (PrefixData F P S × (Fin 4 → Point F)))) :=
    {ez | endpoint ez.2 ≠ previous ez.2 ∧
      OnLine (previous ez.2) (lineThrough (ez.1 (Sum.inr (P.classOf i j))) (endpoint ez.2))}
  have hbound : (((PMF.uniformOfFintype (DirectionToken b κ ↪ Direction F)).bind
      (fun e => (noise e).map (fun z => (e,z)))).toOuterMeasure E).toReal ≤
      2 / (Fintype.card F : ℝ) := by
    apply original_probability_le_of_auxiliary K noise E
    intro base
    exact (auxiliary_guarded_joining_probability_le K base
      (Sum.inr (P.classOf i j)) hnew noise
      (currentNoise_dependsOnExposed P hκ R S hD hS bits p i hphase K hKt hKg hi)
      endpoint previous).trans
      (inverse_remaining_le_two_div (Fintype.card F) K.card b Fintype.card_pos hK hb)
  have hevent : (fun e x =>
      let a := (tokenInjectionEquiv F b κ e).1
      let M := injectedGenerated P hκ R hD bits p e x
      prescribedPoint P a bits M (i,purposefulIndex (bits i) j s) ≠
        prescribedPoint P a bits M (r.1,t) ∧
      OnLine (prescribedPoint P a bits M (r.1,t))
        (constituent M (a.2 (P.classOf i j)) s)) =
    (fun e x =>
      let a := (tokenInjectionEquiv F b κ e).1
      let M := injectedGenerated P hκ R hD bits p e x
      prescribedPoint P a bits M (i,purposefulIndex (bits i) j s) ≠
        prescribedPoint P a bits M (r.1,t) ∧
      OnLine (prescribedPoint P a bits M (r.1,t))
        (lineThrough (e (Sum.inr (P.classOf i j)))
          (prescribedPoint P a bits M (i,purposefulIndex (bits i) j s)))) := by
    funext e x
    dsimp only
    rw [constituent_eq_purposeful_line P _
      (allTokensDistinct_eligible P _ (tokenInjectionEquiv F b κ e).2)]
    rfl
  rw [hevent]
  unfold injectionFreeProbability
  rw [UniformConditionalProduct.uniform_product_eq_bind]
  simpa only [noise, currentNoise, E, endpoint, previous, PMF.map_comp,
    PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_map_apply,
    Set.preimage_ofPred_eq, prefixObservation, injectedGenerated, Function.comp_apply] using hbound

theorem geometricUsedTest_later_generator_le
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R S : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (hS : S ⊆ R ∨ R ⊆ S) (bits : Bits b) (p : Point F) (i : Fin b)
    (hphase : i ∈ R ∨ R ⊆ S)
    (K : Finset (DirectionToken b κ))
    (hKt : ∀ r ∈ S, Sum.inl r ∈ K)
    (hKg : ∀ c ∈ S.biUnion P.classSet, Sum.inr c ∈ K)
    (hi : Sum.inl i ∈ K) (j : Fin 4)
    (hnew : Sum.inr (P.classOf i j) ∉ K) (s : Bool)
    (r : {r : Fin b // r ∈ S}) (t : Fin 4)
    (hK : K.card ≤ 5*b) (hb : 10*b ≤ Fintype.card F) :
    injectionFreeProbability P R (fun e x =>
      geometricUsedTest P (tokenInjectionEquiv F b κ e).1 bits p
        (P.classOf i j) (r.1,t) s (injectedGenerated P hκ R hD bits p e x)) ≤
      2 / (Fintype.card F : ℝ) := by
  apply le_trans _ (global_later_generator_probability_le P hκ R S hD hS bits p i
    hphase K hKt hKg hi j hnew s r t hK hb)
  apply ENNReal.toReal_mono
  · rw [PMF.toOuterMeasure_apply]
    exact PMF.tsum_coe_indicator_ne_top _ _
  · apply PMF.toOuterMeasure_mono
    intro ex hx
    refine ⟨?_, hx.1.2.2⟩
    intro heq
    have hip := hx.1.1.2.1 heq
    have hir : i = r.1 := congrArg Prod.fst hip
    exact hx.1.2.1 j (by simp only [hir])

end
end Balanced.Local.AlignedGlobal

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_AlignedProjectedCollinearTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.AlignedGlobal

open RootChildPartition UsedEventUnion
noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

theorem dependent_currentOld_cases (P : EqualityPattern b κ)
    (R : Finset (Fin b)) (k : Fin b × Fin 4)
    (hk : k ∈ dependentOccurrences P R) :
    k.2 ∈ currentOldIndices P R k.1 ∨
      k.2 + 1 ∈ currentOldIndices P R k.1 := by
  rcases (mem_dependentOccurrences P R k).mp hk with ⟨hn, hl | hr⟩
  · exact Or.inl (by simpa [currentOldIndices, hn, rootGeneratorIndices] using hl)
  · exact Or.inr (by simpa [currentOldIndices, hn, rootGeneratorIndices] using hr)

theorem geometricCollinearTest_projected_le
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R S : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (hS : S ⊆ R ∨ R ⊆ S) (bits : Bits b) (p : Point F)
    (i j k : Fin b × Fin 4) (hi : i.1 ∈ S) (hj : j.1 ∈ S)
    (hdep : k ∈ dependentOccurrences P R)
    (hJ : (currentOldIndices P R k.1).card ≤ 1)
    (hOld : ∀ t ∈ currentOldIndices P R k.1,
      P.classOf k.1 t ∈ S.biUnion P.classSet)
    (K : Finset (DirectionToken b κ))
    (hKt : ∀ r ∈ S, Sum.inl r ∈ K)
    (hKg : ∀ c ∈ S.biUnion P.classSet, Sum.inr c ∈ K)
    (htarget : Sum.inl k.1 ∉ K)
    (hK : K.card ≤ 5*b) (hb : 10*b ≤ Fintype.card F)
    [Nonempty (DirectionToken b κ ↪ Direction F)] :
    injectionFreeProbability P R (fun e x =>
      geometricCollinearTest P (tokenInjectionEquiv F b κ e).1 bits p i j k
        (injectedGenerated P hκ R hD bits p e x)) ≤
      2 / (Fintype.card F : ℝ) := by
  let m : ProjectionData (F := F) P R S → Line F := fun z =>
    joiningLine (z.2.1 ⟨i.1,hi⟩ i.2) (z.2.1 ⟨j.1,hj⟩ j.2)
  have hmono (c : Fin (4*b-κ)) (s : Bool) :
      injectionFreeProbability P R (fun e x =>
        geometricCollinearTest P (tokenInjectionEquiv F b κ e).1 bits p i j k
          (injectedGenerated P hκ R hD bits p e x)) ≤
      ((PMF.uniformOfFintype ((DirectionToken b κ ↪ Direction F) ×
          (FreeIndex P R → F))).toOuterMeasure
        {ex | let a := tokenInjectionEquiv F b κ ex.1
              let M := generatedZero P hκ R hD a.1
                (allTokensDistinct_eligible P a.1 a.2) bits p ex.2
              let z := projectionObservation P hκ R S hD bits p ex.1 ex.2
              constituent M (ex.1 (Sum.inr c)) s ≠ m z ∧
                prescribedPoint P a.1 bits M k ≠ p ∧
                OnLine (prescribedPoint P a.1 bits M k) (m z)}).toReal := by
    unfold injectionFreeProbability
    apply ENNReal.toReal_mono
    · rw [PMF.toOuterMeasure_apply]
      exact PMF.tsum_coe_indicator_ne_top _ _
    · apply (PMF.uniformOfFintype _).toOuterMeasure.mono
      intro ex hex
      rcases hex with ⟨hg, hij, hik, hjk, hxy, hxz, hyz, hinc, ht, hu⟩
      refine ⟨?_, hg.2.2.1 k, ?_⟩
      · exact (hu c s).symm
      · exact hinc
  rcases dependent_currentOld_cases P R k hdep with hl | hr
  · exact (hmono (P.classOf k.1 k.2) (bits k.1 k.2)).trans
      (global_projected_left_probability_le_two_div P hκ R S hD hS bits p
        k.1 hJ hOld k.2 hl K hKt hKg htarget m hK hb)
  · exact (hmono (P.classOf k.1 (k.2+1)) (!(bits k.1 (k.2+1)))).trans
      (global_projected_right_probability_le_two_div P hκ R S hD hS bits p
        k.1 hJ hOld k.2 hr K hKt hKg htarget m hK hb)

theorem collinearTest_injectionAverage_projected_le
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R S : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (hS : S ⊆ R ∨ R ⊆ S) (bits : Bits b) (p : Point F)
    (i j k : Fin b × Fin 4) (hi : i.1 ∈ S) (hj : j.1 ∈ S)
    (hdep : k ∈ dependentOccurrences P R)
    (hJ : (currentOldIndices P R k.1).card ≤ 1)
    (hOld : ∀ t ∈ currentOldIndices P R k.1,
      P.classOf k.1 t ∈ S.biUnion P.classSet)
    (K : Finset (DirectionToken b κ))
    (hKt : ∀ r ∈ S, Sum.inl r ∈ K)
    (hKg : ∀ c ∈ S.biUnion P.classSet, Sum.inr c ∈ K)
    (htarget : Sum.inl k.1 ∉ K)
    (hK : K.card ≤ 5*b) (hb : 10*b ≤ Fintype.card F)
    [Nonempty (DirectionToken b κ ↪ Direction F)] :
    injectionAverage P bits p (fun a => collinearTest P a bits p i j k) ≤
      2 / (Fintype.card F : ℝ) :=
  (collinearTest_injectionAverage_le_free P hκ R hD bits p i j k).trans
    (geometricCollinearTest_projected_le P hκ R S hD hS bits p i j k hi hj
      hdep hJ hOld K hKt hKg htarget hK hb)

end
end Balanced.Local.AlignedGlobal

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalTiming
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.Timing

open scoped Classical

variable {b κ : ℕ}

theorem exists_first_class_use (P : EqualityPattern b κ) (rank : Fin b → ℕ)
    (c : Fin (4*b-κ)) :
    ∃ i : Fin b, ∃ j : Fin 4, P.classOf i j = c ∧
      c ∉ (earlierTuples rank i).biUnion P.classSet := by
  let S := Finset.univ.filter (fun i : Fin b => c ∈ P.classSet i)
  have hS : S.Nonempty := by
    obtain ⟨⟨i,j⟩, hij⟩ := P.everyClass c
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hij⟩
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image S rank hS
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hi).2
  refine ⟨i, j, hj, ?_⟩
  intro hc
  obtain ⟨r, hr, hcr⟩ := Finset.mem_biUnion.mp hc
  have hlt : rank r < rank i := (Finset.mem_filter.mp hr).2
  have hle := hmin r (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcr⟩)
  omega

theorem mem_earlier_classes_iff_first_use (P : EqualityPattern b κ)
    (rank : Fin b → ℕ) (c : Fin (4*b-κ)) (first i : Fin b)
    (hfirst : c ∈ P.classSet first)
    (hnew : c ∉ (earlierTuples rank first).biUnion P.classSet) :
    c ∈ (earlierTuples rank i).biUnion P.classSet ↔ rank first < rank i := by
  constructor
  · intro hc
    obtain ⟨r, hr, hcr⟩ := Finset.mem_biUnion.mp hc
    have hri : rank r < rank i := (Finset.mem_filter.mp hr).2
    by_contra hn
    apply hnew
    refine Finset.mem_biUnion.mpr ⟨r, ?_, hcr⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by omega⟩
  · intro h
    exact Finset.mem_biUnion.mpr
      ⟨first, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, hfirst⟩

theorem exists_first_class_use_timing (P : EqualityPattern b κ)
    (rank : Fin b → ℕ) (hrank : Function.Injective rank)
    (c : Fin (4*b-κ)) (i : Fin b) (hnot : ∀ j, P.classOf i j ≠ c) :
    ∃ first : Fin b, ∃ j : Fin 4, P.classOf first j = c ∧
      c ∉ (earlierTuples rank first).biUnion P.classSet ∧
      (rank first < rank i ∨ rank i < rank first) := by
  obtain ⟨first, j, hc, hnew⟩ := exists_first_class_use P rank c
  refine ⟨first, j, hc, hnew, ?_⟩
  rcases lt_trichotomy (rank first) (rank i) with h | h | h
  · exact Or.inl h
  · have heq := hrank h
    exact False.elim (hnot j (heq ▸ hc))
  · exact Or.inr h

theorem rootsFirstRank_injective (R : Finset (Fin b)) :
    Function.Injective (rootsFirstRank R) := by
  intro i j h
  by_cases hi : i ∈ R <;> by_cases hj : j ∈ R <;>
    simp only [rootsFirstRank, hi, hj, ite_true, ite_false] at h
  all_goals apply Fin.ext; omega

theorem rootsFirstRank_prefix (R : Finset (Fin b)) (i : Fin b) :
    earlierTuples (rootsFirstRank R) i ⊆ R ∨
      R ⊆ earlierTuples (rootsFirstRank R) i := by
  by_cases hi : i ∈ R
  · left
    intro j hj
    have hlt := (Finset.mem_filter.mp hj).2
    by_contra hn
    simp only [rootsFirstRank, hi, hn, ite_true, ite_false] at hlt
    omega
  · right
    intro j hj
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simp only [rootsFirstRank, hi, hj, ite_true, ite_false]
    omega

end Balanced.Local.Timing

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalUsedEventTiming
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.UsedEventUnion

noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

omit [Fintype F] in
theorem geometricCollinearTest_rotate
    (P : EqualityPattern b κ) (a : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F) (M : MergedPairs F)
    (i j k : Fin b × Fin 4)
    (h : geometricCollinearTest P a bits p i j k M) :
    geometricCollinearTest P a bits p j k i M := by
  rcases h with ⟨hg, hij, hik, hjk, hxy, hxz, hyz, hline, ht, hu⟩
  have heq : joiningLine (prescribedPoint P a bits M j) (prescribedPoint P a bits M k) =
      joiningLine (prescribedPoint P a bits M i) (prescribedPoint P a bits M j) :=
    eq_of_two_common_points _ _ hyz _ _ (onLine_joiningLine_left _ _)
      (onLine_joiningLine_right _ _) (onLine_joiningLine_right _ _) hline
  refine ⟨hg, hjk, hij.symm, hik.symm, hyz, hxy.symm, hxz.symm, ?_, ?_, ?_⟩
  · rw [heq]
    exact onLine_joiningLine_left _ _
  · simpa only [heq] using ht
  · simpa only [heq] using hu

theorem collinearTest_rotate
    (P : EqualityPattern b κ) (a : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F) (M : MergedPairs F)
    (i j k : Fin b × Fin 4) (h : collinearTest P a bits p i j k M) :
    collinearTest P a bits p j k i M :=
  ⟨h.1, (geometricCollinearTest_rotate P a bits p M i j k
    (collinearTest_implies_geometric P a bits p i j k M h)).2⟩

theorem injectionAverage_mono
    (P : EqualityPattern b κ) (bits : Bits b) (p : Point F)
    (E G : DirectionAssignment F b κ → MergedPairs F → Prop)
    (h : ∀ a M, E a M → G a M) :
    injectionAverage P bits p E ≤ injectionAverage P bits p G := by
  unfold injectionAverage
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro e _
  exact UnusedOffsetProbability.conditionedOffsetProbability_mono _
    (h (tokenInjectionEquiv F b κ e).1)

theorem collinear_injectionAverage_le_of_latest
    (P : EqualityPattern b κ) (bits : Bits b) (p : Point F)
    (rank : Fin b → ℕ) (hrank : Function.Injective rank)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ i j k : Fin b × Fin 4,
      rank i.1 < rank k.1 → rank j.1 < rank k.1 →
      injectionAverage P bits p (fun a => collinearTest P a bits p i j k) ≤ C)
    (i j k : Fin b × Fin 4) :
    injectionAverage P bits p (fun a => collinearTest P a bits p i j k) ≤ C := by
  classical
  by_cases hij : i.1 = j.1
  · simpa [injectionAverage, conditionedOffsetProbability, offsetProbability,
      collinearTest, hij] using hC
  by_cases hik : i.1 = k.1
  · simpa [injectionAverage, conditionedOffsetProbability, offsetProbability,
      collinearTest, hik] using hC
  by_cases hjk : j.1 = k.1
  · simpa [injectionAverage, conditionedOffsetProbability, offsetProbability,
      collinearTest, hjk] using hC
  have hijr : rank i.1 ≠ rank j.1 := fun he => hij (hrank he)
  have hikr : rank i.1 ≠ rank k.1 := fun he => hik (hrank he)
  have hjkr : rank j.1 ≠ rank k.1 := fun he => hjk (hrank he)
  have hrot : injectionAverage P bits p (fun a => collinearTest P a bits p i j k) ≤
      injectionAverage P bits p (fun a => collinearTest P a bits p j k i) :=
    injectionAverage_mono P bits p _ _ (fun a M h => collinearTest_rotate P a bits p M i j k h)
  have hrot2 : injectionAverage P bits p (fun a => collinearTest P a bits p j k i) ≤
      injectionAverage P bits p (fun a => collinearTest P a bits p k i j) :=
    injectionAverage_mono P bits p _ _ (fun a M h => collinearTest_rotate P a bits p M j k i h)
  by_cases hik' : rank i.1 < rank k.1
  · by_cases hjk' : rank j.1 < rank k.1
    · exact hbound i j k hik' hjk'
    · exact (hrot.trans hrot2).trans (hbound k i j (by omega) (by omega))
  · by_cases hji : rank j.1 < rank i.1
    · exact hrot.trans (hbound j k i hji (by omega))
    · exact (hrot.trans hrot2).trans (hbound k i j (by omega) (by omega))

end
end Balanced.Local.UsedEventUnion

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalUsedFreshMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.UsedEventUnion

open AlignedGlobal RootChildPartition
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

theorem injectionAverage_le_const
    (P : EqualityPattern b κ) (bits : Bits b) (p : Point F)
    (E : DirectionAssignment F b κ → MergedPairs F → Prop)
    (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ e : DirectionToken b κ ↪ Direction F,
      conditionedOffsetProbability (Aligned P (tokenInjectionEquiv F b κ e).1 bits p)
        (E (tokenInjectionEquiv F b κ e).1) ≤ C) :
    injectionAverage P bits p E ≤ C := by
  have hm := TwoReuseAssembly.mean_le_mean_add
    (fun e : DirectionToken b κ ↪ Direction F =>
      conditionedOffsetProbability (Aligned P (tokenInjectionEquiv F b κ e).1 bits p)
        (E (tokenInjectionEquiv F b κ e).1)) (fun _ => 0) C hC
    (fun e => by simpa using h e)
  simpa [injectionAverage] using hm

theorem injectionAverage_fresh_usedTest_le
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R S : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (hS : S ⊆ R ∨ R ⊆ S) (bits : Bits b) (p : Point F)
    (v : FreeIndex P R) (hv : v.1.1 ∉ S)
    (c : Fin (4*b-κ)) (hc : c ∈ S.biUnion P.classSet) (s : Bool) :
    injectionAverage P bits p (fun a => usedConstituentTest P a bits p c v.1 s) ≤
      1 / (Fintype.card F : ℝ) := by
  apply injectionAverage_le_const P bits p _ _ (by positivity)
  intro e
  exact conditioned_fresh_usedTest_le P hκ R S hD hS _
    (allTokensDistinct_eligible P _ (tokenInjectionEquiv F b κ e).2)
    bits p v hv c hc s

theorem injectionAverage_fresh_collinearTest_le
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R S : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (hS : S ⊆ R ∨ R ⊆ S) (bits : Bits b) (p : Point F)
    (v : FreeIndex P R) (hv : v.1.1 ∉ S)
    (i j : Fin b × Fin 4) (hi : i.1 ∈ S) (hj : j.1 ∈ S) :
    injectionAverage P bits p (fun a => collinearTest P a bits p i j v.1) ≤
      1 / (Fintype.card F : ℝ) := by
  apply injectionAverage_le_const P bits p _ _ (by positivity)
  intro e
  exact conditioned_fresh_collinearTest_le P hκ R S hD hS _
    (allTokensDistinct_eligible P _ (tokenInjectionEquiv F b κ e).2)
    bits p v hv i j hi hj

theorem collinear_injectionAverage_le_of_projected_latest
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (bits : Bits b) (p : Point F)
    (rank : Fin b → ℕ) (hrank : Function.Injective rank)
    (hphase : ∀ k : Fin b,
      (Finset.univ.filter (fun t => rank t < rank k)) ⊆ R ∨
      R ⊆ (Finset.univ.filter (fun t => rank t < rank k)))
    (hprojected : ∀ i j k : Fin b × Fin 4,
      rank i.1 < rank k.1 → rank j.1 < rank k.1 →
      k ∈ dependentOccurrences P R →
      injectionAverage P bits p (fun a => collinearTest P a bits p i j k) ≤
        2 / (Fintype.card F : ℝ))
    (i j k : Fin b × Fin 4) :
    injectionAverage P bits p (fun a => collinearTest P a bits p i j k) ≤
      2 / (Fintype.card F : ℝ) := by
  classical
  apply collinear_injectionAverage_le_of_latest P bits p rank hrank _ (by positivity) _ i j k
  intro i j k hi hj
  by_cases hk : k ∈ dependentOccurrences P R
  · exact hprojected i j k hi hj hk
  · have hf := injectionAverage_fresh_collinearTest_le P hκ R
      (Finset.univ.filter (fun t => rank t < rank k.1)) hD (hphase k.1)
      bits p ⟨k,hk⟩ (by simp) i j (by simpa using hi) (by simpa using hj)
    exact hf.trans (div_le_div_of_nonneg_right (by norm_num) (Nat.cast_nonneg _))

theorem usedEventMean_le_of_remaining_tests
    (P : EqualityPattern b 2) (R : Finset (Fin b))
    (hD : (dependentOccurrences P R).card = 2*2)
    (bits : Bits b) (p : Point F) (hb : 1 ≤ b)
    (hused : ∀ c ij s,
      injectionAverage P bits p (fun a => usedConstituentTest P a bits p c ij s) ≤
        2 / (Fintype.card F : ℝ))
    (hprojected : ∀ i j k : Fin b × Fin 4,
      Timing.rootsFirstRank R i.1 < Timing.rootsFirstRank R k.1 →
      Timing.rootsFirstRank R j.1 < Timing.rootsFirstRank R k.1 →
      k ∈ dependentOccurrences P R →
      injectionAverage P bits p (fun a => collinearTest P a bits p i j k) ≤
        2 / (Fintype.card F : ℝ)) :
    TwoReuseAssembly.usedEventMean P bits p ≤
      192 * (b : ℝ)^3 / Fintype.card F := by
  apply usedEventMean_le_of_test_bounds P bits p hb hused
  intro i j k
  exact collinear_injectionAverage_le_of_projected_latest P (by decide) R hD
    bits p (Timing.rootsFirstRank R) (Timing.rootsFirstRank_injective R)
    (Timing.rootsFirstRank_prefix R) hprojected i j k

end
end Balanced.Local.UsedEventUnion

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalExposureTiming
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.Timing
open RootChildPartition AlignedGlobal UsedEventUnion
noncomputable section
open scoped Classical
variable {b κ : ℕ}

theorem card_token_set_le (K : Finset (DirectionToken b κ)) : K.card ≤ 5*b := by
  have h := Finset.card_le_univ K
  simp only [DirectionToken, Fintype.card_sum, Fintype.card_fin] at h
  omega

theorem rootsFirstRank_phase (R : Finset (Fin b)) (i : Fin b) :
    i ∈ R ∨ R ⊆ earlierTuples (rootsFirstRank R) i := by
  by_cases hi : i ∈ R
  · exact Or.inl hi
  · right
    intro j hj
    simp only [earlierTuples, Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [rootsFirstRank, hi, hj, ite_true, ite_false]
    omega

theorem currentOldIndices_in_prefix (P : EqualityPattern b κ)
    (R : Finset (Fin b)) (i : Fin b) :
    ∀ j ∈ currentOldIndices P R i,
      P.classOf i j ∈ (earlierTuples (rootsFirstRank R) i).biUnion P.classSet := by
  intro j hj
  by_cases hi : i ∈ R
  · simp [currentOldIndices, hi] at hj
  · have hc : P.classOf i j ∈ R.biUnion P.classSet := by
      simpa [currentOldIndices, hi, rootGeneratorIndices] using hj
    obtain ⟨r, hr, hcr⟩ := Finset.mem_biUnion.mp hc
    exact Finset.mem_biUnion.mpr ⟨r,
      (rootsFirstRank_phase R i).resolve_left hi hr, hcr⟩

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem injectionAverage_later_usedTest_le
    [Nonempty (DirectionToken b κ ↪ Direction F)]
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (bits : Bits b) (p : Point F) (first : Fin b) (j : Fin 4)
    (hnew : P.classOf first j ∉
      (earlierTuples (rootsFirstRank R) first).biUnion P.classSet)
    (ij : Fin b × Fin 4)
    (hearlier : rootsFirstRank R ij.1 < rootsFirstRank R first)
    (s : Bool) (hb : 10*b ≤ Fintype.card F) :
    injectionAverage P bits p
      (fun a => usedConstituentTest P a bits p (P.classOf first j) ij s) ≤
        2 / (Fintype.card F : ℝ) := by
  let S := earlierTuples (rootsFirstRank R) first
  let K := insert (Sum.inl first) (prefixTokens P S)
  have hr : ij.1 ∈ S := by simpa [S, earlierTuples] using hearlier
  apply (usedTest_injectionAverage_le_free P hκ R hD bits p
    (P.classOf first j) ij s).trans
  exact geometricUsedTest_later_generator_le P hκ R S hD
    (rootsFirstRank_prefix R first) bits p first (rootsFirstRank_phase R first) K
    (fun r hr => Finset.mem_insert_of_mem ((inl_mem_prefixTokens P S r).mpr hr))
    (fun c hc => Finset.mem_insert_of_mem ((inr_mem_prefixTokens P S c).mpr hc))
    (Finset.mem_insert_self _ _) j (by simpa [K, S] using hnew)
    s ⟨ij.1,hr⟩ ij.2 (card_token_set_le K) hb

theorem injectionAverage_usedTest_le_of_projected
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (bits : Bits b) (p : Point F) (hb : 10*b ≤ Fintype.card F)
    (hprojected : ∀ (c : Fin (4*b-κ)) (ij : Fin b × Fin 4) (s : Bool),
      ij ∈ dependentOccurrences P R →
      c ∈ (earlierTuples (rootsFirstRank R) ij.1).biUnion P.classSet →
      injectionAverage P bits p (fun a => usedConstituentTest P a bits p c ij s) ≤
        2 / (Fintype.card F : ℝ))
    (c : Fin (4*b-κ)) (ij : Fin b × Fin 4) (s : Bool) :
    injectionAverage P bits p (fun a => usedConstituentTest P a bits p c ij s) ≤
      2 / (Fintype.card F : ℝ) := by
  by_cases hI : Nonempty (DirectionToken b κ ↪ Direction F)
  · let := hI
    by_cases hnot : ∀ j, P.classOf ij.1 j ≠ c
    · obtain ⟨first, j, hc, hnew, horder⟩ := exists_first_class_use_timing
        P (rootsFirstRank R) (rootsFirstRank_injective R) c ij.1 hnot
      rcases horder with hearly | hlater
      · have hcfirst : c ∈ P.classSet first :=
          Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hc⟩
        have hcS : c ∈ (earlierTuples (rootsFirstRank R) ij.1).biUnion P.classSet :=
          (mem_earlier_classes_iff_first_use P (rootsFirstRank R) c first ij.1
            hcfirst hnew).mpr hearly
        by_cases hdep : ij ∈ dependentOccurrences P R
        · exact hprojected c ij s hdep hcS
        · exact (injectionAverage_fresh_usedTest_le P hκ R
            (earlierTuples (rootsFirstRank R) ij.1) hD
            (rootsFirstRank_prefix R ij.1) bits p ⟨ij,hdep⟩
            (by simp [earlierTuples]) c hcS s).trans
              (div_le_div_of_nonneg_right (by norm_num) (Nat.cast_nonneg _))
      · have hn : P.classOf first j ∉
            (earlierTuples (rootsFirstRank R) first).biUnion P.classSet := by
          simpa only [hc] using hnew
        simpa only [hc] using injectionAverage_later_usedTest_le
          P hκ R hD bits p first j hn ij hlater s hb
    · simp [injectionAverage, conditionedOffsetProbability, offsetProbability,
        usedConstituentTest, hnot]
      positivity
  · let : IsEmpty (DirectionToken b κ ↪ Direction F) := ⟨fun e => hI ⟨e⟩⟩
    simp [injectionAverage]
    positivity

end
end Balanced.Local.Timing

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalTwoReuseEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local
open RootChildPartition AlignedGlobal UsedEventUnion Timing
noncomputable section
open scoped Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

theorem projected_collinear_rootsFirst_le
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (hchild : ∀ i, i ∉ R → (P.classSet i ∩ R.biUnion P.classSet).card = 1)
    (bits : Bits b) (p : Point F) (hb : 10*b ≤ Fintype.card F)
    (i j k : Fin b × Fin 4)
    (hi : rootsFirstRank R i.1 < rootsFirstRank R k.1)
    (hj : rootsFirstRank R j.1 < rootsFirstRank R k.1)
    (hdep : k ∈ dependentOccurrences P R) :
    injectionAverage P bits p (fun a => collinearTest P a bits p i j k) ≤
      2 / (Fintype.card F : ℝ) := by
  by_cases hI : Nonempty (DirectionToken b κ ↪ Direction F)
  · let := hI
    let S := earlierTuples (rootsFirstRank R) k.1
    let K := prefixTokens P S
    exact collinearTest_injectionAverage_projected_le P hκ R S hD
      (rootsFirstRank_prefix R k.1) bits p i j k
      (by simpa [S,earlierTuples] using hi) (by simpa [S,earlierTuples] using hj)
      hdep (currentOldIndices_card_le_one P R hchild k.1)
      (currentOldIndices_in_prefix P R k.1) K
      (fun r hr => (inl_mem_prefixTokens P S r).mpr hr)
      (fun c hc => (inr_mem_prefixTokens P S c).mpr hc)
      (by simp [K,S,earlierTuples]) (card_token_set_le K) hb
  · let : IsEmpty (DirectionToken b κ ↪ Direction F) := ⟨fun e => hI ⟨e⟩⟩
    simp [injectionAverage]
    positivity

theorem projected_used_rootsFirst_le
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (hchild : ∀ i, i ∉ R → (P.classSet i ∩ R.biUnion P.classSet).card = 1)
    (bits : Bits b) (p : Point F) (hb : 10*b ≤ Fintype.card F)
    (c : Fin (4*b-κ)) (ij : Fin b × Fin 4) (s : Bool)
    (hdep : ij ∈ dependentOccurrences P R)
    (hc : c ∈ (earlierTuples (rootsFirstRank R) ij.1).biUnion P.classSet) :
    injectionAverage P bits p (fun a => usedConstituentTest P a bits p c ij s) ≤
      2 / (Fintype.card F : ℝ) := by
  by_cases hI : Nonempty (DirectionToken b κ ↪ Direction F)
  · let := hI
    let S := earlierTuples (rootsFirstRank R) ij.1
    let K := prefixTokens P S
    exact usedTest_injectionAverage_projected_le P hκ R S hD
      (rootsFirstRank_prefix R ij.1) bits p ij.1
      (currentOldIndices_card_le_one P R hchild ij.1)
      (currentOldIndices_in_prefix P R ij.1) ij.2 hdep K
      (fun r hr => (inl_mem_prefixTokens P S r).mpr hr)
      (fun d hd => (inr_mem_prefixTokens P S d).mpr hd)
      (by simp [K,S,earlierTuples]) c hc s (card_token_set_le K) hb
  · let : IsEmpty (DirectionToken b κ ↪ Direction F) := ⟨fun e => hI ⟨e⟩⟩
    simp [injectionAverage]
    positivity

theorem used_injectionAverage_le_two_div
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (hchild : ∀ i, i ∉ R → (P.classSet i ∩ R.biUnion P.classSet).card = 1)
    (bits : Bits b) (p : Point F) (hb : 10*b ≤ Fintype.card F)
    (c : Fin (4*b-κ)) (ij : Fin b × Fin 4) (s : Bool) :
    injectionAverage P bits p (fun a => usedConstituentTest P a bits p c ij s) ≤
      2 / (Fintype.card F : ℝ) :=
  injectionAverage_usedTest_le_of_projected P hκ R hD bits p hb
    (projected_used_rootsFirst_le P hκ R hD hchild bits p hb) c ij s

theorem usedEventMean_le_two_reuses
    (P : EqualityPattern b 2) (bits : Bits b) (p : Point F)
    (hb : 3 ≤ b) (hbudget : 10*b ≤ Fintype.card F) :
    TwoReuseAssembly.usedEventMean P bits p ≤
      192 * (b : ℝ)^3 / Fintype.card F := by
  obtain ⟨R, _, _, hD, hchildren⟩ :=
    exists_roots_with_exact_dependent_budget P hb (by decide)
  have hchild : ∀ i, i ∉ R →
      (P.classSet i ∩ R.biUnion P.classSet).card = 1 :=
    fun i hi => (hchildren i hi).1
  apply usedEventMean_le_of_remaining_tests P R hD bits p (by omega)
  · exact used_injectionAverage_le_two_div P (by decide) R hD hchild bits p hbudget
  · exact projected_collinear_rootsFirst_le P (by decide) R hD hchild bits p hbudget

universe u

theorem injectiveUsedEventsEstimate_proof_oai :
    TwoReuseAssembly.InjectiveUsedEventsEstimate.{u} := by
  obtain ⟨q₀, hq₀⟩ := exists_logBudget_token_threshold.{u}
  refine ⟨192, by norm_num, q₀, ?_⟩
  intro F _ _ _ hq b hb hB P bits p
  exact usedEventMean_le_two_reuses P bits p hb (hq₀ F hq b hB)

end
end Balanced.Local

end OAI
end

theorem solution.{u} : type_of% @OAI.Balanced.Local.injectiveUsedEventsEstimate_proof_oai.{u} := @OAI.Balanced.Local.injectiveUsedEventsEstimate_proof_oai.{u}
