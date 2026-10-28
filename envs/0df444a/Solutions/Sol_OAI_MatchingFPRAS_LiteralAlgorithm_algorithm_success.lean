-- Prove2me | solution 1 for OAI.MatchingFPRAS.LiteralAlgorithm.algorithm_success
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T18:22:53.851606+00:00
-- url     : https://prove2.me/submissions/a9dbcb6e-337c-44ac-8734-379152c18dac

import Mathlib
import Definitions.Def_MatchingFPRAS
import Definitions.Def_OAIQ051M004
import Theorems.Thm_OAI_MatchingFPRAS_FiniteTrial_ScaleState_runLaw_tv
import Theorems.Thm_OAI_MatchingFPRAS_FiniteTrial_ScaleState_sampleLaw_budget
import Theorems.Thm_OAI_MatchingFPRAS_LiteralAlgorithm_compute_mean

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Mate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Switching

open Finset
open scoped Classical symmDiff

theorem degree_one_card_le_two {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (hd : ∀ v, G.degree v ≤ 2) :
    (Finset.univ.filter fun v => G.degree v = 1).card ≤ 2 := by
  classical
  have hv := hc.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    ← G.edgeFinset_card] at hv
  have hs : (∑ v, G.degree v) +
      (Finset.univ.filter fun v => G.degree v = 1).card ≤ 2 * Fintype.card V := by
    calc
      _ = ∑ v, (G.degree v + if G.degree v = 1 then 1 else 0) := by
        simp [Finset.sum_add_distrib]
      _ ≤ ∑ _v : V, 2 := by
        apply Finset.sum_le_sum
        intro v _
        split_ifs with h
        · omega
        · simp only [add_zero]
          exact hd v
      _ = _ := by simp [mul_comm]
  rw [G.sum_degrees_eq_twice_card_edges] at hs
  omega

theorem degree_one_pair {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (hd : ∀ v, G.degree v ≤ 2)
    (a : V) (ha : G.degree a = 1) :
    ∃ b, b ≠ a ∧ ∀ v, G.degree v = 1 ↔ v = a ∨ v = b := by
  classical
  let s := Finset.univ.filter fun v => G.degree v = 1
  have he : Even s.card := by
    convert G.even_card_odd_degree_vertices using 2
    all_goals try with_reducible_and_instances rfl
    ext v
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
    have := hd v
    interval_cases hdeg : G.degree v <;> norm_num
  have hle : s.card ≤ 2 := degree_one_card_le_two G hc hd
  have hpos : 0 < s.card := Finset.card_pos.mpr ⟨a, by simp [s, ha]⟩
  have hcard : s.card = 2 := by obtain ⟨k, hk⟩ := he; omega
  obtain ⟨x, y, hxy, hs⟩ := Finset.card_eq_two.mp hcard
  have ham : a = x ∨ a = y := by simpa [hs] using (show a ∈ s by simp [s, ha])
  rcases ham with rfl | rfl
  · refine ⟨y, Ne.symm hxy, ?_⟩
    intro v
    have hm : v ∈ s ↔ G.degree v = 1 := by simp [s]
    rw [← hm, hs]
    simp
  · refine ⟨x, hxy, ?_⟩
    intro v
    have hm : v ∈ s ↔ G.degree v = 1 := by simp [s]
    rw [← hm, hs]
    simp [or_comm]

variable {V : Type*}

theorem overlay_switched (m n : Mate V) (a : V) :
    overlay (switched m n a) (switched n m a) = overlay m n := by
  classical
  ext v w
  by_cases h : (overlay m n).Reachable a v <;>
    simp [overlay_adj, switched_apply, overlay_comm n m, h, or_comm]

@[simp] theorem switched_twice (m n : Mate V) (a : V) :
    switched (switched m n a) (switched n m a) a = m := by
  classical
  apply Subtype.ext
  funext v
  by_cases h : (overlay m n).Reachable a v <;>
    simp [overlay_switched, overlay_comm n m, h]

theorem switch_injective (a : V) : Function.Injective
    (fun p : Mate V × Mate V => (switched p.1 p.2 a, switched p.2 p.1 a)) := by
  intro p q h
  have h' := congrArg
    (fun p : Mate V × Mate V => (switched p.1 p.2 a, switched p.2 p.1 a)) h
  simpa using h'

theorem mates_equal_of_adj (m n : Mate V) {v w : V}
    (hvw : (overlay m n).Adj v w) (hv : m.1 v = n.1 v) : m.1 w = n.1 w := by
  rcases hvw with ⟨rfl, _⟩ | ⟨rfl, _⟩
  · rw [mate_mate, hv, mate_mate]
  · rw [← hv, mate_mate, hv, mate_mate]

theorem mates_equal_of_reachable (m n : Mate V) {v w : V}
    (hvw : (overlay m n).Reachable v w) (hv : m.1 v = n.1 v) : m.1 w = n.1 w := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hvw
  induction hvw with
  | refl => exact hv
  | tail h hAdj ih => exact mates_equal_of_adj m n hAdj ih

theorem mates_ne_of_reachable (m n : Mate V) {a v : V}
    (hav : (overlay m n).Reachable a v) (ha : m.1 a ≠ n.1 a) : m.1 v ≠ n.1 v :=
  fun hv => ha (mates_equal_of_reachable m n hav.symm hv)

theorem overlay_degree_le_two [Fintype V] (m n : Mate V) (v : V) :
    (overlay m n).degree v ≤ 2 := by
  classical
  have hs : (overlay m n).neighborFinset v ⊆ {m.1 v, n.1 v} := by
    intro w hw
    rw [SimpleGraph.mem_neighborFinset, overlay_adj] at hw
    rcases hw with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [← h]
  calc
    _ ≤ ({m.1 v, n.1 v} : Finset V).card := Finset.card_mono hs
    _ ≤ 2 := by
      calc
        _ ≤ ({n.1 v} : Finset V).card + 1 := Finset.card_insert_le _ _
        _ = 2 := by simp

theorem overlay_degree_one_iff [Fintype V] (m n : Mate V) (v : V)
    (hne : m.1 v ≠ n.1 v) :
    (overlay m n).degree v = 1 ↔ m.1 v = v ∨ n.1 v = v := by
  classical
  rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
  constructor
  · intro h
    by_contra hn
    push Not at hn
    have hm : (overlay m n).Adj v (m.1 v) := Or.inl ⟨rfl, Ne.symm hn.1⟩
    have ht : (overlay m n).Adj v (n.1 v) := Or.inr ⟨rfl, Ne.symm hn.2⟩
    exact hne (h.unique hm ht)
  · intro h
    rcases h with hm | hn
    · have hn : n.1 v ≠ v := by intro h; exact hne (hm.trans h.symm)
      refine ⟨n.1 v, Or.inr ⟨rfl, Ne.symm hn⟩, ?_⟩
      intro w hw
      rcases hw with ⟨he, hne'⟩ | ⟨he, _⟩
      · exact (hne' (hm.symm.trans he)).elim
      · exact he.symm
    · have hm : m.1 v ≠ v := by intro h; exact hne (h.trans hn.symm)
      refine ⟨m.1 v, Or.inl ⟨rfl, Ne.symm hm⟩, ?_⟩
      intro w hw
      rcases hw with ⟨he, _⟩ | ⟨he, hne'⟩
      · exact he.symm
      · exact (hne' (hn.symm.trans he)).elim

theorem overlay_restrict (m n : Mate V) (S : Set V)
    (hm : ∀ v, m.1 v ∈ S ↔ v ∈ S) (hn : ∀ v, n.1 v ∈ S ↔ v ∈ S) :
    overlay (restrictMate m S hm) (restrictMate n S hn) = (overlay m n).induce S := by
  ext v w
  simp [overlay_adj, SimpleGraph.induce, SimpleGraph.comap, Subtype.ext_iff]

theorem active_component_endpoints [Fintype V] (m n : Mate V) (a : V)
    (hma : m.1 a = a) (hna : n.1 a ≠ a) :
    ∃ b : V, b ≠ a ∧ (overlay m n).Reachable a b ∧
      ∀ v, (overlay m n).Reachable a v →
        ((m.1 v = v ∨ n.1 v = v) ↔ v = a ∨ v = b) := by
  classical
  let C := (overlay m n).connectedComponentMk a
  have hm : ∀ v, m.1 v ∈ C.supp ↔ v ∈ C.supp := by
    intro v
    change m.1 v ∈ ((overlay m n).connectedComponentMk a).supp ↔
      v ∈ ((overlay m n).connectedComponentMk a).supp
    rw [component_mem_iff, component_mem_iff, reachable_mate_left_iff]
  have hn : ∀ v, n.1 v ∈ C.supp ↔ v ∈ C.supp := by
    intro v
    change n.1 v ∈ ((overlay m n).connectedComponentMk a).supp ↔
      v ∈ ((overlay m n).connectedComponentMk a).supp
    rw [component_mem_iff, component_mem_iff, reachable_mate_right_iff]
  let mC := restrictMate m C.supp hm
  let nC := restrictMate n C.supp hn
  let aC : C.supp := ⟨a, by change (overlay m n).connectedComponentMk a = C; rfl⟩
  have hco : (overlay mC nC).Connected := by
    dsimp only [mC, nC]
    rw [overlay_restrict]
    exact C.connected_toSimpleGraph
  have hdiff : ∀ v : C.supp, mC.1 v ≠ nC.1 v := by
    intro v he
    have hval := congrArg Subtype.val he
    have hav : (overlay m n).Reachable a v.1 := (component_mem_iff m n a v.1).mp v.2
    have han : m.1 a ≠ n.1 a := by rw [hma]; exact Ne.symm hna
    exact mates_ne_of_reachable m n hav han hval
  have hda : (overlay mC nC).degree aC = 1 := by
    rw [overlay_degree_one_iff mC nC aC (hdiff aC)]
    left
    apply Subtype.ext
    exact hma
  obtain ⟨bC, hba, hb⟩ := degree_one_pair (overlay mC nC) hco
    (overlay_degree_le_two mC nC) aC hda
  refine ⟨bC.1, ?_, (component_mem_iff m n a _).mp bC.2, ?_⟩
  · intro he
    exact hba (Subtype.ext he)
  · intro v hv
    let vC : C.supp := ⟨v, (component_mem_iff m n a v).mpr hv⟩
    have hh := hb vC
    rw [overlay_degree_one_iff mC nC vC (hdiff vC)] at hh
    simpa only [mC, nC, vC, aC, Subtype.ext_iff, restrictMate_apply] using hh

theorem weight_nonneg [Fintype V] [LinearOrder V] (w : V → V → ℝ)
    (hw : ∀ v z, 0 ≤ w v z) (m : Mate V) : 0 ≤ weight w m := by
  apply Finset.prod_nonneg
  intro v _
  split_ifs
  · exact hw _ _
  · norm_num

theorem switched_weight [Fintype V] [LinearOrder V] (w : V → V → ℝ)
    (m n : Mate V) (a : V) :
    weight w (switched m n a) * weight w (switched n m a) = weight w m * weight w n := by
  classical
  simp only [weight, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro v _
  by_cases h : (overlay m n).Reachable a v <;>
    simp [switched_apply, overlay_comm n m, h, mul_comm]

theorem hasHoles_unique (m : Mate V) {U W : Finset V}
    (hU : HasHoles m U) (hW : HasHoles m W) : U = W := by
  ext v
  exact (hU v).symm.trans (hW v)

theorem no_holes_iff (m : Mate V) : HasHoles m ∅ ↔ ∀ v, m.1 v ≠ v := by
  simp [HasHoles]

theorem switched_holes_perfect [Fintype V] [DecidableEq V] (m n : Mate V) (U : Finset V)
    (hm : HasHoles m U) (hn : HasHoles n ∅) (a : V) (ha : a ∈ U) :
    ∃ b ∈ U.erase a,
      HasHoles (switched m n a) (U \ {a, b}) ∧
      HasHoles (switched n m a) {a, b} := by
  classical
  have hnn : ∀ v, n.1 v ≠ v := (no_holes_iff n).mp hn
  obtain ⟨b, hba, hab, he⟩ := active_component_endpoints m n a ((hm a).mpr ha) (hnn a)
  have he' : ∀ v, (overlay m n).Reachable a v → (m.1 v = v ↔ v = a ∨ v = b) := by
    intro v hv
    simpa only [hnn v, or_false] using he v hv
  have hb : b ∈ U := (hm b).mp ((he' b hab).mpr (Or.inr rfl))
  refine ⟨b, Finset.mem_erase.mpr ⟨hba, hb⟩, ?_, ?_⟩
  · intro v
    by_cases hv : (overlay m n).Reachable a v
    · have hu : v ∈ U ↔ v = a ∨ v = b := (hm v).symm.trans (he' v hv)
      simp [switched_apply, hv, hnn v, hu]
      tauto
    · have hva : v ≠ a := by rintro rfl; exact hv .rfl
      have hvb : v ≠ b := by rintro rfl; exact hv hab
      simpa [switched_apply, hv, hva, hvb] using hm v
  · intro v
    by_cases hv : (overlay m n).Reachable a v
    · simpa [switched_apply, overlay_comm n m, hv] using he' v hv
    · have hva : v ≠ a := by rintro rfl; exact hv .rfl
      have hvb : v ≠ b := by rintro rfl; exact hv hab
      simp [switched_apply, overlay_comm n m, hv, hnn v, hva, hvb]

theorem partition_nonneg [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (hw : ∀ v z, 0 ≤ w v z) (U : Finset V) : 0 ≤ partition w U :=
  Finset.sum_nonneg (fun _ _ => weight_nonneg w hw _)

theorem hole_partition_comparison [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (hw : ∀ v z, 0 ≤ w v z) (U : Finset V)
    (a : V) (ha : a ∈ U) :
    partition w U * partition w ∅ ≤
      ∑ b ∈ U.erase a, partition w (U \ {a, b}) * partition w {a, b} := by
  classical
  let S := (matchings U) ×ˢ (matchings (∅ : Finset V))
  let Q := fun b : V => (matchings (U \ {a, b})) ×ˢ (matchings {a, b})
  let f := fun p : Mate V × Mate V => (switched p.1 p.2 a, switched p.2 p.1 a)
  let W := fun p : Mate V × Mate V => weight w p.1 * weight w p.2
  have hi : Function.Injective f := switch_injective a
  have hd : (↑(U.erase a) : Set V).PairwiseDisjoint Q := by
    intro b hb c hc hbc
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hpb : HasHoles p.2 {a, b} :=
      (mem_matchings p.2 _).mp (Finset.mem_product.mp hp).2
    have hpc : HasHoles p.2 {a, c} :=
      (mem_matchings p.2 _).mp (Finset.mem_product.mp hq).2
    have hbm : b ∈ ({a, c} : Finset V) := (hpc b).mp ((hpb b).mpr (by simp))
    have hba : b ≠ a := (Finset.mem_erase.mp hb).1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hbm
    exact hbc (hbm.resolve_left hba)
  have himage : S.image f ⊆ (U.erase a).biUnion Q := by
    intro p hp
    obtain ⟨⟨m, n⟩, hmn, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hm, hn⟩ := Finset.mem_product.mp hmn
    obtain ⟨b, hb, hmb, hnb⟩ := switched_holes_perfect m n U
      ((mem_matchings m U).mp hm) ((mem_matchings n ∅).mp hn) a ha
    exact Finset.mem_biUnion.mpr ⟨b, hb,
      Finset.mem_product.mpr ⟨(mem_matchings _ _).mpr hmb, (mem_matchings _ _).mpr hnb⟩⟩
  calc
    partition w U * partition w ∅ = ∑ p ∈ S, W p := by
      simp only [S, W, partition, Finset.sum_product, Finset.sum_mul_sum]
    _ = ∑ p ∈ S.image f, W p := by
      rw [Finset.sum_image hi.injOn]
      apply Finset.sum_congr rfl
      intro p _
      exact (switched_weight w p.1 p.2 a).symm
    _ ≤ ∑ p ∈ (U.erase a).biUnion Q, W p :=
      Finset.sum_le_sum_of_subset_of_nonneg himage
        (fun p _ _ => mul_nonneg (weight_nonneg w hw p.1) (weight_nonneg w hw p.2))
    _ = _ := by
      rw [Finset.sum_biUnion hd]
      apply Finset.sum_congr rfl
      intro b _
      simp only [Q, W, partition, Finset.sum_product, Finset.sum_mul_sum]

end MatchingFPRAS.Switching

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Edge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Switching
open Finset
open scoped Classical symmDiff

variable {V : Type*}
theorem switched_holes [Fintype V] [DecidableEq V]
    (m n : Mate V) (S T : Finset V) (hm : HasHoles m S) (hn : HasHoles n T)
    (a : V) (ha : a ∈ S) (hTa : a ∉ T) :
    ∃ b, b ≠ a ∧ b ∈ S ∆ T ∧
      HasHoles (switched m n a) (S ∆ {a, b}) ∧
      HasHoles (switched n m a) (T ∆ {a, b}) := by
  classical
  have hma : m.1 a = a := (hm a).mpr ha
  have hna : n.1 a ≠ a := fun h => hTa ((hn a).mp h)
  have ham : m.1 a ≠ n.1 a := by rw [hma]; exact Ne.symm hna
  obtain ⟨b, hba, hab, he⟩ := active_component_endpoints m n a hma hna
  have hnBoth : ∀ v, (overlay m n).Reachable a v → ¬(v ∈ S ∧ v ∈ T) := by
    intro v hv ⟨hs, ht⟩
    exact mates_ne_of_reachable m n hv ham (((hm v).mpr hs).trans ((hn v).mpr ht).symm)
  have hb : b ∈ S ∨ b ∈ T := by
    simpa only [hm b, hn b] using (he b hab).mpr (Or.inr rfl)
  refine ⟨b, hba, ?_, ?_, ?_⟩
  · simp only [Finset.mem_symmDiff]
    have := hnBoth b hab
    tauto
  · intro v
    by_cases hv : (overlay m n).Reachable a v
    · have hvEnd : (v ∈ S ∨ v ∈ T) ↔ (v = a ∨ v = b) := by
        simpa only [hm v, hn v] using he v hv
      have hnb := hnBoth v hv
      simp only [switched_apply, ite_eq_left hv, hn v, Finset.mem_symmDiff,
        Finset.mem_insert, Finset.mem_singleton]
      tauto
    · have hva : v ≠ a := by rintro rfl; exact hv .rfl
      have hvb : v ≠ b := by rintro rfl; exact hv hab
      simp [switched_apply, hv, hm v, Finset.mem_symmDiff, hva, hvb]
  · intro v
    by_cases hv : (overlay m n).Reachable a v
    · have hvEnd : (v ∈ S ∨ v ∈ T) ↔ (v = a ∨ v = b) := by
        simpa only [hm v, hn v] using he v hv
      have hnb := hnBoth v hv
      simp only [switched_apply, overlay_comm n m, ite_eq_left hv, hm v,
        Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
      tauto
    · have hva : v ≠ a := by rintro rfl; exact hv .rfl
      have hvb : v ≠ b := by rintro rfl; exact hv hab
      simp [switched_apply, overlay_comm n m, hv, hn v, Finset.mem_symmDiff, hva, hvb]

theorem mixed_hole_partition_comparison [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (hw : ∀ v z, 0 ≤ w v z) (S T : Finset V)
    (a : V) (ha : a ∈ S) (hTa : a ∉ T) :
    partition w S * partition w T ≤
      ∑ b ∈ (S ∆ T).erase a,
        partition w (S ∆ {a, b}) * partition w (T ∆ {a, b}) := by
  classical
  let H := (S ∆ T).erase a
  let inputs := (matchings S) ×ˢ (matchings T)
  let Q := fun b : V => (matchings (S ∆ {a, b})) ×ˢ (matchings (T ∆ {a, b}))
  let f := fun p : Mate V × Mate V => (switched p.1 p.2 a, switched p.2 p.1 a)
  let W := fun p : Mate V × Mate V => weight w p.1 * weight w p.2
  have hi : Function.Injective f := switch_injective a
  have hd : (↑H : Set V).PairwiseDisjoint Q := by
    intro b hb c hc hbc
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hpb : HasHoles p.1 (S ∆ {a, b}) :=
      (mem_matchings p.1 _).mp (Finset.mem_product.mp hp).1
    have hpc : HasHoles p.1 (S ∆ {a, c}) :=
      (mem_matchings p.1 _).mp (Finset.mem_product.mp hq).1
    have heq : (S ∆ {a, b}) = (S ∆ {a, c}) := hasHoles_unique p.1 hpb hpc
    have habc : ({a, b} : Finset V) = {a, c} := symmDiff_right_injective S heq
    have hbm : b ∈ ({a, c} : Finset V) := by rw [← habc]; simp
    have hba : b ≠ a := (Finset.mem_erase.mp hb).1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hbm
    exact hbc (hbm.resolve_left hba)
  have himage : inputs.image f ⊆ H.biUnion Q := by
    intro p hp
    obtain ⟨⟨m, n⟩, hmn, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hm, hn⟩ := Finset.mem_product.mp hmn
    obtain ⟨b, hba, hb, hmb, hnb⟩ := switched_holes m n S T
      ((mem_matchings m S).mp hm) ((mem_matchings n T).mp hn) a ha hTa
    exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_erase.mpr ⟨hba, hb⟩,
      Finset.mem_product.mpr ⟨(mem_matchings _ _).mpr hmb, (mem_matchings _ _).mpr hnb⟩⟩
  calc
    partition w S * partition w T = ∑ p ∈ inputs, W p := by
      simp only [inputs, W, partition, Finset.sum_product, Finset.sum_mul_sum]
    _ = ∑ p ∈ inputs.image f, W p := by
      rw [Finset.sum_image hi.injOn]
      apply Finset.sum_congr rfl
      intro p _
      exact (switched_weight w p.1 p.2 a).symm
    _ ≤ ∑ p ∈ H.biUnion Q, W p :=
      Finset.sum_le_sum_of_subset_of_nonneg himage
        (fun p _ _ => mul_nonneg (weight_nonneg w hw p.1) (weight_nonneg w hw p.2))
    _ = _ := by
      rw [Finset.sum_biUnion hd]
      apply Finset.sum_congr rfl
      intro b _
      simp only [Q, W, partition, Finset.sum_product, Finset.sum_mul_sum]

theorem withEdge_injOn [Fintype V] (S : Finset V) (a b : V)
    (ha : a ∈ S) (hb : b ∈ S) :
    Set.InjOn (fun m : Mate V => withEdge m a b) (matchings S) := by
  classical
  intro m hm n hn he
  have hm := (mem_matchings m S).mp hm
  have hn := (mem_matchings n S).mp hn
  apply Subtype.ext
  funext v
  by_cases hva : v = a
  · subst v
    exact ((hm a).mpr ha).trans ((hn a).mpr ha).symm
  by_cases hvb : v = b
  · subst v
    exact ((hm b).mpr hb).trans ((hn b).mpr hb).symm
  have hv := congrArg (fun p : Mate V => p.1 v) he
  simpa [withEdge_apply, (hm a).mpr ha, (hm b).mpr hb,
    (hn a).mpr ha, (hn b).mpr hb, hva, hvb] using hv

theorem withEdge_comm (m : Mate V) (a b : V) : withEdge m a b = withEdge m b a := by
  classical
  by_cases h : m.1 a = a ∧ m.1 b = b
  · apply Subtype.ext
    funext v
    simp only [withEdge_apply, h.1, h.2]
    by_cases hv : v = a
    · subst v
      by_cases hab : a = b <;> simp [hab]
    · simp [hv]
  · have h' : ¬(m.1 b = b ∧ m.1 a = a) := by tauto
    simp [withEdge, h, h']

theorem withEdge_weight_of_lt [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (m : Mate V) (a b : V)
    (ha : m.1 a = a) (hb : m.1 b = b) (hab : a < b) :
    weight w (withEdge m a b) = w a b * weight w m := by
  classical
  have hf : ∀ v : V,
      (if v < (withEdge m a b).1 v then w v ((withEdge m a b).1 v) else 1) =
      (if v = a then w a b else 1) * (if v < m.1 v then w v (m.1 v) else 1) := by
    intro v
    by_cases hva : v = a
    · subst v
      simp [withEdge_apply, ha, hb, hab]
    by_cases hvb : v = b
    · subst v
      simp [withEdge_apply, ha, hb, hab.ne', hab.not_gt]
    simp [withEdge_apply, ha, hb, hva, hvb]
  simp only [weight, hf, Finset.prod_mul_distrib]
  simp

theorem withEdge_weight [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (m : Mate V) (a b : V)
    (ha : m.1 a = a) (hb : m.1 b = b) (hab : a ≠ b) :
    weight w (withEdge m a b) = edgeActivity w a b * weight w m := by
  rcases lt_or_gt_of_ne hab with h | h
  · simpa [edgeActivity, h] using withEdge_weight_of_lt w m a b ha hb h
  · rw [withEdge_comm, edgeActivity_comm]
    simpa [edgeActivity, h] using withEdge_weight_of_lt w m b a hb ha h

theorem edge_fill_partition [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (hw : ∀ v z, 0 ≤ w v z) (S : Finset V)
    (a b : V) (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
    edgeActivity w a b * partition w S ≤ partition w (S \ {a, b}) := by
  classical
  let f := fun m : Mate V => withEdge m a b
  have hi := withEdge_injOn S a b ha hb
  have hsub : (matchings S).image f ⊆ matchings (S \ {a, b}) := by
    intro m hm
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
    exact (mem_matchings _ _).mpr
      (withEdge_holes n S ((mem_matchings n S).mp hn) a b ha hb hab)
  calc
    edgeActivity w a b * partition w S = ∑ m ∈ matchings S, weight w (f m) := by
      rw [partition, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      have hh := (mem_matchings m S).mp hm
      exact (withEdge_weight w m a b ((hh a).mpr ha) ((hh b).mpr hb) hab).symm
    _ = ∑ m ∈ (matchings S).image f, weight w m := (Finset.sum_image hi).symm
    _ ≤ partition w (S \ {a, b}) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => weight_nonneg w hw m)

theorem holeRatio_nonneg [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (hw : ∀ v z, 0 ≤ w v z) (U : Finset V) :
    0 ≤ holeRatio w U := div_nonneg (partition_nonneg w hw U) (partition_nonneg w hw ∅)

theorem holeRatio_empty [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (hz : 0 < partition w ∅) : holeRatio w ∅ = 1 := div_self hz.ne'

theorem holeRatio_pair_comm [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (a b : V) : holeRatio w {a, b} = holeRatio w {b, a} := by
  rw [Finset.pair_comm]

theorem holeRatio_comparison [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (hw : ∀ v z, 0 ≤ w v z) (hz : 0 < partition w ∅)
    (U : Finset V) (a : V) (ha : a ∈ U) :
    holeRatio w U ≤ ∑ b ∈ U.erase a, holeRatio w (U \ {a, b}) * holeRatio w {a, b} := by
  have h := hole_partition_comparison w hw U a ha
  have hzz : 0 ≤ partition w ∅ * partition w ∅ := mul_nonneg hz.le hz.le
  calc
    holeRatio w U = (partition w U * partition w ∅) / (partition w ∅ * partition w ∅) := by
      unfold holeRatio
      field_simp
    _ ≤ (∑ b ∈ U.erase a, partition w (U \ {a, b}) * partition w {a, b}) /
          (partition w ∅ * partition w ∅) := div_le_div_of_nonneg_right h hzz
    _ = _ := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro b _
      exact mul_div_mul_comm _ _ _ _

theorem four_holes [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (hw : ∀ v z, 0 ≤ w v z) (hz : 0 < partition w ∅)
    (a b c d : V) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    holeRatio w {a, b, c, d} ≤
      holeRatio w {a, b} * holeRatio w {c, d} +
      holeRatio w {a, c} * holeRatio w {b, d} +
      holeRatio w {a, d} * holeRatio w {b, c} := by
  classical
  have h := holeRatio_comparison w hw hz {a,b,c,d} a (by simp)
  have he : ({a,b,c,d} : Finset V).erase a = {b,c,d} := by
    ext v
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    grind
  have hab' : ({a,b,c,d} : Finset V) \ {a,b} = {c,d} := by
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    grind
  have hac' : ({a,b,c,d} : Finset V) \ {a,c} = {b,d} := by
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    grind
  have had' : ({a,b,c,d} : Finset V) \ {a,d} = {b,c} := by
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    grind
  rw [he, Finset.sum_insert (by simp [hbc, hbd]),
    Finset.sum_insert (by simp [hcd]), Finset.sum_singleton,
    hab', hac', had'] at h
  nlinarith only [h]

theorem mixed_holeRatio_comparison [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (hw : ∀ v z, 0 ≤ w v z) (hz : 0 < partition w ∅)
    (S T : Finset V) (a : V) (ha : a ∈ S) (hTa : a ∉ T) :
    holeRatio w S * holeRatio w T ≤
      ∑ b ∈ (S ∆ T).erase a,
        holeRatio w (S ∆ {a, b}) * holeRatio w (T ∆ {a, b}) := by
  have h := mixed_hole_partition_comparison w hw S T a ha hTa
  have hzz : 0 ≤ partition w ∅ * partition w ∅ := mul_nonneg hz.le hz.le
  calc
    holeRatio w S * holeRatio w T =
        (partition w S * partition w T) / (partition w ∅ * partition w ∅) :=
      (mul_div_mul_comm _ _ _ _).symm
    _ ≤ (∑ b ∈ (S ∆ T).erase a,
        partition w (S ∆ {a, b}) * partition w (T ∆ {a, b})) /
          (partition w ∅ * partition w ∅) := div_le_div_of_nonneg_right h hzz
    _ = _ := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro b _
      exact mul_div_mul_comm _ _ _ _

theorem edge_fill_holeRatio [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (hw : ∀ v z, 0 ≤ w v z) (hz : 0 < partition w ∅)
    (S : Finset V) (a b : V) (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
    edgeActivity w a b * holeRatio w S ≤ holeRatio w (S \ {a, b}) := by
  simpa only [holeRatio, mul_div_assoc] using
    div_le_div_of_nonneg_right (edge_fill_partition w hw S a b ha hb hab) hz.le

theorem holeRatio_le_rowMax [Fintype V] [LinearOrder V]
    (hcard : 2 ≤ Fintype.card V) (w : V → V → ℝ) (a b : V) (hab : a ≠ b) :
    holeRatio w {a,b} ≤ rowMax hcard w a := by
  exact Finset.le_sup' (fun b => holeRatio w {a,b}) (by simp [Ne.symm hab])

theorem two_holes_le_four [Fintype V] [LinearOrder V]
    (hcard : 2 ≤ Fintype.card V) (w : V → V → ℝ)
    (hr : ∀ a, rowMax hcard w a ≤ 4) (U : Finset V) (hU : U.card = 2) :
    holeRatio w U ≤ 4 := by
  obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hU
  exact (holeRatio_le_rowMax hcard w a b hab).trans (hr a)

theorem four_holes_le_fortyeight [Fintype V] [LinearOrder V]
    (hcard : 2 ≤ Fintype.card V) (w : V → V → ℝ)
    (hw : ∀ v z, 0 ≤ w v z) (hz : 0 < partition w ∅)
    (hr : ∀ a, rowMax hcard w a ≤ 4) (U : Finset V) (hU : U.card = 4) :
    holeRatio w U ≤ 48 := by
  obtain ⟨a,b,c,d,hab,hac,had,hbc,hbd,hcd,rfl⟩ := Finset.card_eq_four.mp hU
  have hpair : ∀ a b : V, a ≠ b → holeRatio w {a,b} ≤ 4 :=
    fun a b hab => (holeRatio_le_rowMax hcard w a b hab).trans (hr a)
  have hmul : ∀ (a b c d : V), a ≠ b → c ≠ d →
      holeRatio w {a,b} * holeRatio w {c,d} ≤ 16 := by
    intro a b c d hab hcd
    have h := mul_le_mul (hpair a b hab) (hpair c d hcd)
      (holeRatio_nonneg w hw {c,d}) (by norm_num : (0:ℝ) ≤ 4)
    norm_num at h ⊢
    exact h
  have hf := four_holes w hw hz a b c d hab hac had hbc hbd hcd
  have h1 := hmul a b c d hab hcd
  have h2 := hmul a c b d hac hbd
  have h3 := hmul a d b c had hbc
  linarith

theorem zero_or_two_holes_le_four [Fintype V] [LinearOrder V]
    (hcard : 2 ≤ Fintype.card V) (w : V → V → ℝ) (hz : 0 < partition w ∅)
    (hr : ∀ a, rowMax hcard w a ≤ 4) (U : Finset V)
    (hU : U.card = 0 ∨ U.card = 2) : holeRatio w U ≤ 4 := by
  rcases hU with h | h
  · have he : U = ∅ := Finset.card_eq_zero.mp h
    rw [he, holeRatio_empty w hz]
    norm_num
  · exact two_holes_le_four hcard w hr U h

theorem small_holes_le_fortyeight [Fintype V] [LinearOrder V]
    (hcard : 2 ≤ Fintype.card V) (w : V → V → ℝ)
    (hw : ∀ v z, 0 ≤ w v z) (hz : 0 < partition w ∅)
    (hr : ∀ a, rowMax hcard w a ≤ 4) (U : Finset V)
    (hU : U.card = 0 ∨ U.card = 2 ∨ U.card = 4) : holeRatio w U ≤ 48 := by
  rcases hU with h | h | h
  · exact (zero_or_two_holes_le_four hcard w hz hr U (Or.inl h)).trans (by norm_num)
  · exact (two_holes_le_four hcard w hr U h).trans (by norm_num)
  · exact four_holes_le_fortyeight hcard w hw hz hr U h

theorem symmDiff_pair_of_mem_mem [DecidableEq V] (S : Finset V) (a b : V)
    (ha : a ∈ S) (hb : b ∈ S) : S ∆ {a,b} = S \ {a,b} := by
  ext v
  simp only [Finset.mem_symmDiff, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
  grind

theorem symmDiff_pair_of_mem_notMem [DecidableEq V] (S : Finset V) (a b : V)
    (ha : a ∈ S) (hb : b ∉ S) : S ∆ {a,b} = insert b (S.erase a) := by
  ext v
  simp only [Finset.mem_symmDiff, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
  grind

end MatchingFPRAS.Switching

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_PathStrength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Switching
open Finset
open scoped Classical symmDiff

variable {V : Type*}

theorem relocated_card [DecidableEq V] (S : Finset V) (a b : V)
    (ha : a ∈ S) (hb : b ∉ S) : (insert b (S.erase a)).card = S.card := by
  have hba : b ∉ S.erase a := fun h => hb (Finset.mem_of_mem_erase h)
  rw [Finset.card_insert_of_notMem hba, Finset.card_erase_add_one ha]

theorem pair_fill_holeRatio [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (hw : ∀ v z, 0 ≤ w v z) (hz : 0 < partition w ∅)
    (a b : V) (hab : a ≠ b) :
    edgeActivity w a b * holeRatio w {a,b} ≤ 1 := by
  have h := edge_fill_holeRatio w hw hz {a,b} a b (by simp) (by simp) hab
  simpa [holeRatio_empty w hz] using h

theorem adjacent_hole_fill [Fintype V] [LinearOrder V]
    (hcard : 2 ≤ Fintype.card V) (w : V → V → ℝ)
    (hw : ∀ v z, 0 ≤ w v z) (hz : 0 < partition w ∅)
    (hrlo : ∀ a, (1:ℝ)/8 ≤ rowMax hcard w a)
    (hrhi : ∀ a, rowMax hcard w a ≤ 4)
    (S : Finset V) (hS : S.card = 2 ∨ S.card = 4)
    (a b : V) (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (B : ℝ) (hB : 0 < B) (hBa : B ≤ edgeActivity w a b) :
    holeRatio w S / rowMax hcard w a ≤ 32 / B := by
  have hfill := edge_fill_holeRatio w hw hz S a b ha hb hab
  have hhole := holeRatio_nonneg w hw S
  have hp : B * holeRatio w S ≤ holeRatio w (S \ {a,b}) :=
    (mul_le_mul_of_nonneg_right hBa hhole).trans hfill
  have hs : (S \ {a,b}).card = 0 ∨ (S \ {a,b}).card = 2 := by
    rw [sdiff_pair_card S a b ha hb hab]
    omega
  have hg := zero_or_two_holes_le_four hcard w hz hrhi (S \ {a,b}) hs
  have hra := hrlo a
  have hrap : 0 < rowMax hcard w a := by linarith
  apply (div_le_iff₀ hrap).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hB).mpr
  nlinarith only [hp,hg,hra]

theorem toggle_small_holes_card [DecidableEq V] (S : Finset V) (a b : V)
    (ha : a ∈ S) (hab : a ≠ b) (hS : S.card = 2 ∨ S.card = 4) :
    (S ∆ {a,b}).card = 0 ∨ (S ∆ {a,b}).card = 2 ∨ (S ∆ {a,b}).card = 4 := by
  by_cases hb : b ∈ S
  · rw [symmDiff_pair_of_mem_mem S a b ha hb, sdiff_pair_card S a b ha hb hab]
    omega
  · rw [symmDiff_pair_of_mem_notMem S a b ha hb, relocated_card S a b ha hb]
    omega

theorem normalized_relocation [Fintype V] [LinearOrder V]
    (hcard : 2 ≤ Fintype.card V) (w : V → V → ℝ)
    (hw : ∀ v z, 0 ≤ w v z) (hz : 0 < partition w ∅)
    (hrlo : ∀ a, (1:ℝ)/8 ≤ rowMax hcard w a)
    (hrhi : ∀ a, rowMax hcard w a ≤ 4)
    (S : Finset V) (hS : S.card = 2 ∨ S.card = 4)
    (a z : V) (ha : a ∈ S) (hzS : z ∉ S)
    (B : ℝ) (hB8 : 8 < B) (hBa : B ≤ edgeActivity w a z) :
    holeRatio w S / rowMax hcard w a ≤
      holeRatio w (insert z (S.erase a)) / rowMax hcard w z + 6144 / B := by
  have hB : 0 < B := by linarith
  have haz : a ≠ z := fun h => hzS (h ▸ ha)
  have hrap : ∀ v, 0 < rowMax hcard w v := fun v => by linarith [hrlo v]
  obtain ⟨p,hpz,hpr⟩ := rowMax_attained hcard w z
  have hfill := pair_fill_holeRatio w hw hz a z haz
  have hpair : B * holeRatio w {a,z} ≤ 1 :=
    (mul_le_mul_of_nonneg_right hBa (holeRatio_nonneg w hw {a,z})).trans hfill
  have hpa : p ≠ a := by
    intro h
    subst p
    rw [holeRatio_pair_comm w z a] at hpr
    have hlo := hrlo z
    rw [← hpr] at hlo
    nlinarith
  let R := S \ {a,p}
  let F := fun b => holeRatio w (S ∆ {a,b}) * holeRatio w ({z,p} ∆ {a,b})
  have hF : ∀ b, 0 ≤ F b := fun b => mul_nonneg
    (holeRatio_nonneg w hw _) (holeRatio_nonneg w hw _)
  have hcmp := mixed_holeRatio_comparison w hw hz S {z,p} a ha
    (by simp [haz, Ne.symm hpa])
  change holeRatio w S * holeRatio w {z,p} ≤
    ∑ b ∈ (S ∆ {z,p}).erase a, F b at hcmp
  rw [hpr] at hcmp
  have hsub : (S ∆ {z,p}).erase a ⊆ insert z (insert p R) := by
    intro x hx
    simp only [Finset.mem_erase, Finset.mem_symmDiff, Finset.mem_insert,
      Finset.mem_singleton, R, Finset.mem_sdiff] at hx ⊢
    grind
  have hcmp' : holeRatio w S * rowMax hcard w z ≤ ∑ b ∈ insert z (insert p R), F b :=
    hcmp.trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun b _ _ => hF b))
  have hzR : z ∉ R := fun h => hzS (Finset.mem_sdiff.mp h).1
  have hpR : p ∉ R := by simp [R]
  rw [Finset.sum_insert (by simp [hpz.symm, hzR]), Finset.sum_insert hpR] at hcmp'
  have htz : ({z,p} : Finset V) ∆ {a,z} = {a,p} := by
    ext v
    simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
    grind
  have htp : ({z,p} : Finset V) ∆ {a,p} = {a,z} := by
    ext v
    simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
    grind
  have hFz : F z ≤ holeRatio w (insert z (S.erase a)) * rowMax hcard w a := by
    dsimp [F]
    rw [symmDiff_pair_of_mem_notMem S a z ha hzS, htz]
    exact mul_le_mul_of_nonneg_left (holeRatio_le_rowMax hcard w a p hpa.symm)
      (holeRatio_nonneg w hw _)
  have hFp : B * F p ≤ 48 := by
    have hh := small_holes_le_fortyeight hcard w hw hz hrhi (S ∆ {a,p})
      (toggle_small_holes_card S a p ha hpa.symm hS)
    have hn := holeRatio_nonneg w hw (S ∆ {a,p})
    dsimp [F]
    rw [htp]
    nlinarith only [hpair, hh, hn]
  have hFx : ∀ x ∈ R, B * F x ≤ 16 := by
    intro x hx
    have hxS := (Finset.mem_sdiff.mp hx).1
    have hxa : x ≠ a := by
      intro h
      exact (Finset.mem_sdiff.mp hx).2 (by simp [h])
    have hxp : x ≠ p := by
      intro h
      exact (Finset.mem_sdiff.mp hx).2 (by simp [h])
    have hxz : x ≠ z := fun h => hzS (h ▸ hxS)
    have ht : ({z,p} : Finset V) ∆ {a,x} = {z,p,a,x} := by
      ext v
      simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
      grind
    have hs : (S \ {a,x}).card = 0 ∨ (S \ {a,x}).card = 2 := by
      rw [sdiff_pair_card S a x ha hxS hxa.symm]
      omega
    have hs4 := zero_or_two_holes_le_four hcard w hz hrhi (S \ {a,x}) hs
    have hs0 := holeRatio_nonneg w hw (S \ {a,x})
    have hf := edge_fill_holeRatio w hw hz {z,p,a,x} a z (by simp) (by simp) haz
    have he : ({z,p,a,x} : Finset V) \ {a,z} = {p,x} := by
      ext v
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      grind
    rw [he] at hf
    have hf' : B * holeRatio w {z,p,a,x} ≤ 4 := by
      exact ((mul_le_mul_of_nonneg_right hBa (holeRatio_nonneg w hw _)).trans hf).trans
        ((holeRatio_le_rowMax hcard w p x hxp.symm).trans (hrhi p))
    dsimp [F]
    rw [ht, symmDiff_pair_of_mem_mem S a x ha hxS]
    have hm := mul_le_mul hs4 hf' (mul_nonneg hB.le (holeRatio_nonneg w hw _))
      (by norm_num : (0:ℝ) ≤ 4)
    nlinarith only [hm]
  have hRsub : R ⊆ S.erase a := by
    intro x hx
    dsimp [R] at hx
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_erase]
    grind
  have hRcard : R.card ≤ 3 := by
    have h := Finset.card_le_card hRsub
    have hc := Finset.card_erase_add_one ha
    omega
  have hsum : B * ∑ x ∈ R, F x ≤ 48 := by
    rw [Finset.mul_sum]
    calc
      ∑ x ∈ R, B * F x ≤ ∑ _x ∈ R, (16:ℝ) := Finset.sum_le_sum hFx
      _ = (R.card:ℝ) * 16 := by simp
      _ ≤ 48 := by exact_mod_cast (by omega : R.card * 16 ≤ 48)
  have hmain : B * holeRatio w S * rowMax hcard w z ≤
      B * holeRatio w (insert z (S.erase a)) * rowMax hcard w a + 96 := by
    have hm := mul_le_mul_of_nonneg_left hcmp' hB.le
    have hmz := mul_le_mul_of_nonneg_left hFz hB.le
    nlinarith only [hm, hmz, hFp, hsum]
  have hprod := mul_le_mul (hrlo a) (hrlo z) (by norm_num : (0:ℝ) ≤ 1/8)
    (le_of_lt (hrap a))
  apply (div_le_iff₀ (hrap a)).mpr
  apply (mul_le_mul_iff_left₀ (mul_pos hB (hrap z))).mp
  have he :
      ((holeRatio w (insert z (S.erase a)) / rowMax hcard w z + 6144 / B) *
        rowMax hcard w a) * (B * rowMax hcard w z) =
      B * holeRatio w (insert z (S.erase a)) * rowMax hcard w a +
        6144 * rowMax hcard w a * rowMax hcard w z := by
    field_simp [ne_of_gt (hrap z), ne_of_gt hB]
  rw [he]
  nlinarith only [hmain, hprod]

theorem normalized_path_relocation [Fintype V] [LinearOrder V]
    (hcard : 2 ≤ Fintype.card V) (w : V → V → ℝ)
    (hw : ∀ v z, 0 ≤ w v z) (hz : 0 < partition w ∅)
    (hrlo : ∀ a, (1:ℝ)/8 ≤ rowMax hcard w a)
    (hrhi : ∀ a, rowMax hcard w a ≤ 4)
    (B : ℝ) (hB8 : 8 < B) (L : List V) (a : V)
    (S : Finset V) (hS : S.card = 2 ∨ S.card = 4) (ha : a ∈ S)
    (hpath : List.IsChain (fun x y => B ≤ edgeActivity w x y) (a :: L))
    (hnodup : (a :: L).Nodup) (hend : ∃ j ∈ L, j ∈ S) :
    holeRatio w S / rowMax hcard w a ≤ 6144 * L.length / B := by
  have hB : 0 < B := by linarith
  induction L generalizing a S with
  | nil => simp at hend
  | cons z L ih =>
    obtain ⟨hazL, hnd⟩ := List.nodup_cons.mp hnodup
    have haz : a ≠ z := fun h => hazL (by simp [h])
    obtain ⟨hBa, hp⟩ := List.isChain_cons_cons.mp hpath
    by_cases hzS : z ∈ S
    · have hf := adjacent_hole_fill hcard w hw hz hrlo hrhi S hS a z ha hzS haz B hB hBa
      apply hf.trans
      apply (div_le_div_iff_of_pos_right hB).mpr
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      have hlen : (0:ℝ) ≤ L.length := Nat.cast_nonneg _
      linarith
    · let T := insert z (S.erase a)
      have hT : T.card = 2 ∨ T.card = 4 := by
        dsimp [T]
        rw [relocated_card S a z ha hzS]
        exact hS
      have he : ∃ j ∈ L, j ∈ T := by
        obtain ⟨j,hj,hjS⟩ := hend
        have hjz : j ≠ z := fun h => hzS (h ▸ hjS)
        have hja : j ≠ a := fun h => hazL (h ▸ hj)
        refine ⟨j, ?_, ?_⟩
        · simpa [hjz] using hj
        · simp [T, hja, hjS]
      have hi := ih z T hT (by simp [T]) hp hnd he
      have hs := normalized_relocation hcard w hw hz hrlo hrhi S hS a z ha hzS B hB8 hBa
      calc
        holeRatio w S / rowMax hcard w a ≤
          holeRatio w T / rowMax hcard w z + 6144 / B := hs
        _ ≤ 6144 * (L.length:ℝ) / B + 6144 / B := add_le_add hi le_rfl
        _ = 6144 * ((z :: L).length:ℝ) / B := by
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          ring

theorem hole_relocation_of_strong_path [Fintype V] [LinearOrder V]
    (hcard : 2 ≤ Fintype.card V) (w : V → V → ℝ)
    (hw : ∀ v z, 0 ≤ w v z) (hz : 0 < partition w ∅)
    (hrlo : ∀ a, (1:ℝ)/8 ≤ rowMax hcard w a)
    (hrhi : ∀ a, rowMax hcard w a ≤ 4)
    (B : ℝ) (hB : 0 < B) (S : Finset V) (hS : S.card = 2 ∨ S.card = 4)
    (a : V) (ha : a ∈ S)
    (hpath : 8 < B → ∃ L : List V,
      List.IsChain (fun x y => B ≤ edgeActivity w x y) (a :: L) ∧
      (a :: L).Nodup ∧ ∃ j ∈ L, j ∈ S) :
    holeRatio w S ≤ 100000 * Fintype.card V / B := by
  by_cases hB8 : 8 < B
  · obtain ⟨L,hp,hn,he⟩ := hpath hB8
    have hb := normalized_path_relocation hcard w hw hz hrlo hrhi B hB8 L a S hS ha hp hn he
    have hra : 0 < rowMax hcard w a := by linarith [hrlo a]
    have hb' := (div_le_iff₀ hra).mp hb
    have hlen : L.length ≤ Fintype.card V := by
      have h := Finset.card_le_card (Finset.subset_univ (a :: L).toFinset)
      rw [List.toFinset_card_of_nodup hn, Finset.card_univ] at h
      simpa using Nat.le_trans (Nat.le_succ L.length) h
    have hlenR : (L.length:ℝ) ≤ Fintype.card V := by exact_mod_cast hlen
    apply (le_div_iff₀ hB).mpr
    have hmul := mul_le_mul_of_nonneg_right hb' hB.le
    have heq : (6144 * (L.length:ℝ) / B * rowMax hcard w a) * B =
        6144 * (L.length:ℝ) * rowMax hcard w a := by field_simp
    rw [heq] at hmul
    have hm := mul_le_mul_of_nonneg_left (hrhi a)
      (by positivity : (0:ℝ) ≤ 6144 * (L.length:ℝ))
    have hn0 : (0:ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
    nlinarith only [hmul,hm,hlenR,hn0]
  · have hc := small_holes_le_fortyeight hcard w hw hz hrhi S (by omega)
    have hn : (2:ℝ) ≤ Fintype.card V := by exact_mod_cast hcard
    have hg0 := holeRatio_nonneg w hw S
    apply (le_div_iff₀ hB).mpr
    have hm := mul_le_mul_of_nonneg_right (le_of_not_gt hB8) hg0
    nlinarith only [hc,hm,hn]

theorem edgeActivity_mono [LinearOrder V] (w u : V → V → ℝ)
    (h : ∀ a b, w a b ≤ u a b) (a b : V) : edgeActivity w a b ≤ edgeActivity u a b := by
  unfold edgeActivity
  split_ifs <;> apply h

theorem hole_relocation [Fintype V] [LinearOrder V]
    (hcard : 2 ≤ Fintype.card V) (w u : V → V → ℝ)
    (hu : ∀ v z, 0 ≤ u v z) (hz : 0 < partition u ∅)
    (hwu : ∀ a b, w a b ≤ u a b)
    (hrlo : ∀ a, (1:ℝ)/8 ≤ rowMax hcard u a)
    (hrhi : ∀ a, rowMax hcard u a ≤ 4)
    (S : Finset V) (hS : S.card = 2 ∨ S.card = 4)
    (a b : V) (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
    holeRatio u S ≤ 100000 * Fintype.card V / bottleneck w a b := by
  apply hole_relocation_of_strong_path hcard u hu hz hrlo hrhi
    (bottleneck w a b) (lt_of_lt_of_le (by norm_num) (one_le_bottleneck w a b)) S hS a ha
  intro hs
  obtain ⟨L,hp,hn,hbL⟩ := bottleneck_path w a b hab (by linarith)
  refine ⟨L, ?_,hn,b,hbL,hb⟩
  exact hp.imp fun {x y} h => h.trans (edgeActivity_mono w u hwu x y)

theorem erasePair_holes [DecidableEq V] (m : Mate V) (S : Finset V)
    (hm : HasHoles m S) (a b : V) (h : m.1 a = b) :
    HasHoles (erasePair m a b) (insert a (insert b S)) := by
  intro v
  rw [erasePair_apply m a b v h]
  by_cases hv : v = a ∨ v = b
  · rcases hv with rfl | rfl <;> simp
  · have hva := (not_or.mp hv).1
    have hvb := (not_or.mp hv).2
    simp [hva, hvb, hm v]

theorem withEdge_erasePair (m : Mate V) (a b : V) (h : m.1 a = b) :
    withEdge (erasePair m a b) a b = m := by
  have hba : m.1 b = a := by rw [← h, mate_mate]
  apply Subtype.ext
  funext v
  rw [withEdge_apply _ _ _ _ (by simp [h]) (by simp [h])]
  by_cases hva : v = a
  · subst v
    simp [h]
  by_cases hvb : v = b
  · subst v
    simp [hba, hva]
  simp [hva, hvb, h]

theorem erasePair_withEdge (m : Mate V) (a b : V)
    (ha : m.1 a = a) (hb : m.1 b = b) :
    erasePair (withEdge m a b) a b = m := by
  apply Subtype.ext
  funext v
  rw [erasePair_apply _ _ _ _ (by simp [ha,hb]), withEdge_apply m a b v ha hb]
  by_cases hva : v = a
  · subst v
    simp [ha]
  by_cases hvb : v = b
  · subst v
    simp [hb]
  simp [hva, hvb]

end MatchingFPRAS.Switching

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_AffineWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Switching
open Finset
open scoped Classical symmDiff

variable {V : Type*}
theorem erasePair_weight_of_lt [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (m : Mate V) (a b : V) (h : m.1 a = b) (hab : a < b) :
    weight w (erasePair m a b) =
      ∏ v ∈ Finset.univ.erase a, if v < m.1 v then w v (m.1 v) else 1 := by
  have hba : m.1 b = a := by rw [← h, mate_mate]
  unfold weight
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ a)]
  simp only [erasePair_apply m a b a h, true_or, ite_true, lt_self_iff_false, ite_false,
    mul_one]
  apply Finset.prod_congr rfl
  intro v hv
  have hva := (Finset.mem_erase.mp hv).1
  by_cases hvb : v = b
  · subst v
    simp [hba, erasePair_apply, h, hab.not_gt]
  · simp [erasePair_apply, h, hva, hvb]

theorem sum_erased_weights [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (S : Finset V) (a b : V)
    (ha : a ∉ S) (hb : b ∉ S) (hab : a ≠ b) :
    ∑ m ∈ (matchings S).filter (fun m => m.1 a = b), weight w (erasePair m a b) =
      partition w (insert a (insert b S)) := by
  let A := (matchings S).filter (fun m => m.1 a = b)
  let f := fun m : Mate V => erasePair m a b
  have hi : Set.InjOn f A := by
    intro m hm n hn he
    have hm' := (Finset.mem_filter.mp hm).2
    have hn' := (Finset.mem_filter.mp hn).2
    have h := congrArg (fun p => withEdge p a b) he
    simpa [f, withEdge_erasePair, hm', hn'] using h
  have himg : A.image f = matchings (insert a (insert b S)) := by
    ext m
    constructor
    · intro hm
      obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hm
      obtain ⟨hnS,hnab⟩ := Finset.mem_filter.mp hn
      exact (mem_matchings _ _).mpr
        (erasePair_holes n S ((mem_matchings n S).mp hnS) a b hnab)
    · intro hm
      have hholes := (mem_matchings m (insert a (insert b S))).mp hm
      have hma : m.1 a = a := (hholes a).mpr (by simp)
      have hmb : m.1 b = b := (hholes b).mpr (by simp)
      refine Finset.mem_image.mpr ⟨withEdge m a b, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        constructor
        · apply (mem_matchings _ _).mpr
          have hh := withEdge_holes m (insert a (insert b S)) hholes a b
            (by simp) (by simp) hab
          have he : insert a (insert b S) \ {a,b} = S := by
            ext v
            simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
            grind
          rwa [he] at hh
        · simp [hma,hmb]
      · exact erasePair_withEdge m a b hma hmb
  change ∑ m ∈ A, weight w (f m) = _
  rw [← Finset.sum_image hi, himg]
  rfl

theorem weight_hasDerivAt [Fintype V] [LinearOrder V]
    (w d : V → V → ℝ) (m : Mate V) (t : ℝ) :
    HasDerivAt (fun s => weight (affineWeights w d s) m)
      (∑ a, if a < m.1 a then d a (m.1 a) *
        weight (affineWeights w d t) (erasePair m a (m.1 a)) else 0) t := by
  have hf : ∀ a ∈ (Finset.univ : Finset V),
      HasDerivAt (fun s => if a < m.1 a then affineWeights w d s a (m.1 a) else 1)
        (if a < m.1 a then d a (m.1 a) else 0) t := by
    intro a _
    by_cases ha : a < m.1 a
    · simp only [ha, ite_true, affineWeights]
      exact (hasDerivAt_mul_const (x := t) (d a (m.1 a))).const_add (w a (m.1 a))
    · simp only [ha, ite_false]
      exact hasDerivAt_const t 1
  have hh := HasDerivAt.fun_finsetProd hf
  apply hh.congr_deriv
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a < m.1 a
  · simp only [ha, ite_true, smul_eq_mul]
    rw [erasePair_weight_of_lt _ m a (m.1 a) rfl ha]
    ring
  · simp [ha]

theorem mate_endpoints_not_holes [DecidableEq V] (m : Mate V) (S : Finset V)
    (hm : HasHoles m S) (a b : V) (h : m.1 a = b) (hab : a ≠ b) :
    a ∉ S ∧ b ∉ S := by
  constructor
  · intro ha
    exact hab (((hm a).mpr ha).symm.trans h)
  · intro hb
    have hba : m.1 b = a := by rw [← h, mate_mate]
    exact hab (hba.symm.trans ((hm b).mpr hb))

theorem partition_hasDerivAt [Fintype V] [LinearOrder V]
    (w d : V → V → ℝ) (S : Finset V) (t : ℝ) :
    HasDerivAt (fun s => partition (affineWeights w d s) S)
      (edgeSum S (fun a b => d a b *
        partition (affineWeights w d t) (insert a (insert b S)))) t := by
  have hh := HasDerivAt.fun_sum (fun m (_ : m ∈ matchings S) => weight_hasDerivAt w d m t)
  change HasDerivAt (fun s => partition (affineWeights w d s) S) _ t at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  unfold edgeSum
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_fiberwise (matchings S) (fun m => m.1 a)
    (fun m => if a < m.1 a then d a (m.1 a) *
      weight (affineWeights w d t) (erasePair m a (m.1 a)) else 0)]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hab : a < b
  · by_cases hS : a ∉ S ∧ b ∉ S
    · simp only [hab, hS.1, hS.2, and_self]
      rw [← sum_erased_weights (affineWeights w d t) S a b hS.1 hS.2 hab.ne,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      have he := (Finset.mem_filter.mp hm).2
      simp [he,hab]
    · have hempty : (matchings S).filter (fun m => m.1 a = b) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro m hm
        obtain ⟨hm,he⟩ := Finset.mem_filter.mp hm
        exact hS (mate_endpoints_not_holes m S ((mem_matchings m S).mp hm) a b he hab.ne)
      simp [hS,hempty]
  · simp only [hab, false_and, ite_false]
    symm
    apply Finset.sum_eq_zero
    intro m hm
    have he := (Finset.mem_filter.mp hm).2
    simp [he,hab]

theorem weight_mono [Fintype V] [LinearOrder V] (w u : V → V → ℝ)
    (hw : ∀ a b, 0 ≤ w a b) (hwu : ∀ a b, w a b ≤ u a b) (m : Mate V) :
    weight w m ≤ weight u m := by
  apply Finset.prod_le_prod
  · intro a _
    split_ifs
    · exact hw a (m.1 a)
    · norm_num
  · intro a _
    split_ifs
    · exact hwu a (m.1 a)
    · rfl

theorem partition_mono [Fintype V] [LinearOrder V] (w u : V → V → ℝ)
    (hw : ∀ a b, 0 ≤ w a b) (hwu : ∀ a b, w a b ≤ u a b) (S : Finset V) :
    partition w S ≤ partition u S :=
  Finset.sum_le_sum (fun m _ => weight_mono w u hw hwu m)

theorem edgeSum_div [Fintype V] [LinearOrder V] (S : Finset V)
    (f : V → V → ℝ) (c : ℝ) :
    edgeSum S (fun a b => f a b / c) = edgeSum S f / c := by
  simp only [edgeSum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> simp

theorem edgeSum_nonneg [Fintype V] [LinearOrder V] (S : Finset V)
    (f : V → V → ℝ) (hf : ∀ a b, a < b → a ∉ S → b ∉ S → 0 ≤ f a b) :
    0 ≤ edgeSum S f := by
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro b _
  split_ifs with h
  · exact hf a b h.1 h.2.1 h.2.2
  · rfl

theorem holeRatio_hasDerivAt [Fintype V] [LinearOrder V]
    (w d : V → V → ℝ) (S : Finset V) (t : ℝ)
    (hz : partition (affineWeights w d t) ∅ ≠ 0) :
    HasDerivAt (fun s => holeRatio (affineWeights w d s) S)
      (edgeSum S (fun a b => d a b *
          holeRatio (affineWeights w d t) (insert a (insert b S))) -
        holeRatio (affineWeights w d t) S *
          edgeSum ∅ (fun a b => d a b * holeRatio (affineWeights w d t) {a,b})) t := by
  have hh := (partition_hasDerivAt w d S t).div (partition_hasDerivAt w d ∅ t) hz
  apply hh.congr_deriv
  simp only [holeRatio, ← mul_div_assoc, edgeSum_div, Finset.insert_empty]
  field_simp

theorem affine_partition_pos [Fintype V] [LinearOrder V]
    (w d : V → V → ℝ) (hw : ∀ a b, 0 ≤ w a b) (hd : ∀ a b, 0 ≤ d a b)
    (hz : 0 < partition w ∅) (t : ℝ) (ht : 0 ≤ t) :
    0 < partition (affineWeights w d t) ∅ := by
  apply hz.trans_le (partition_mono w _ hw _ ∅)
  intro a b
  exact le_add_of_nonneg_right (mul_nonneg ht (hd a b))

theorem finite_family_barrier {I : Type*} [Fintype I]
    (f f' : I → ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c) (hc1 : c < 1)
    (hf : ∀ i, ContinuousOn (f i) (Set.Icc 0 1))
    (hinit : ∀ i, f i 0 ≤ 1)
    (hderiv : ∀ t ∈ Set.Ioo 0 1, (∀ i, f i t < 2) →
      ∀ i, HasDerivAt (f i) (f' i t) t ∧ f' i t ≤ c) :
    ∀ t ∈ Set.Icc 0 1, ∀ i, f i t < 2 := by
  classical
  let S : Set ℝ := {t | t ∈ Set.Icc 0 1 ∧ ∃ i, 2 ≤ f i t}
  have hsclosed : IsClosed S := by
    have he : S = ⋃ i, {t | t ∈ Set.Icc 0 1 ∧ 2 ≤ f i t} := by
      ext t
      simp only [S, Set.mem_ofPred_eq, Set.mem_iUnion]
      aesop
    rw [he]
    apply isClosed_iUnion_of_finite
    intro i
    exact (hf i).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  by_contra hfail
  push Not at hfail
  obtain ⟨t,ht,i,hi⟩ := hfail
  obtain ⟨x,hx,hxmin⟩ := (isCompact_Icc.of_isClosed_subset hsclosed
    (show S ⊆ Set.Icc (0:ℝ) 1 from fun _ h => h.1)).exists_isLeast ⟨t,ht,i,hi⟩
  obtain ⟨j,hj⟩ := hx.2
  have hxpos : 0 < x := by
    have := hinit j
    rcases hx.1.1.eq_or_lt with h | h
    · rw [← h] at hj
      linarith
    · exact h
  have hbefore : ∀ y ∈ Set.Ioo 0 x, ∀ k, f k y < 2 := by
    intro y hy k
    by_contra h
    have hym : y ∈ S := ⟨⟨hy.1.le,hy.2.le.trans hx.1.2⟩,k,le_of_not_gt h⟩
    exact (not_le_of_gt hy.2) (hxmin hym)
  have hdiff : ∀ y ∈ Set.Ioo 0 x, HasDerivAt (f j) (f' j y) y := by
    intro y hy
    exact (hderiv y ⟨hy.1,hy.2.trans_le hx.1.2⟩ (hbefore y hy) j).1
  obtain ⟨y,hy,he⟩ := exists_hasDerivAt_eq_slope (f j) (f' j) hxpos
    ((hf j).mono (Set.Icc_subset_Icc_right hx.1.2)) hdiff
  have hbound := (hderiv y ⟨hy.1,hy.2.trans_le hx.1.2⟩ (hbefore y hy) j).2
  rw [he, sub_zero] at hbound
  have hbound' := (div_le_iff₀ hxpos).mp hbound
  have hcx := mul_le_of_le_one_right hc hx.1.2
  have := hinit j
  linarith

theorem holeScale_pos [Fintype V] : 0 < holeScale V := by
  unfold holeScale
  positivity

theorem holeAugmentation_nonneg [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (a b : V) : 0 ≤ holeAugmentation w a b :=
  div_nonneg (le_trans (by norm_num) (one_le_bottleneck w a b)) holeScale_pos.le

theorem edgeSum_le_card_sq [Fintype V] [LinearOrder V] (S : Finset V)
    (f : V → V → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hf : ∀ a b, a < b → a ∉ S → b ∉ S → f a b ≤ c) :
    edgeSum S f ≤ (Fintype.card V : ℝ)^2 * c := by
  calc
    _ ≤ ∑ _a : V, ∑ _b : V, c := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      split_ifs with h
      · exact hf a b h.1 h.2.1 h.2.2
      · exact hc
    _ = _ := by simp; ring

theorem augmented_hole_summand [Fintype V] [LinearOrder V]
    (hn : 2 ≤ Fintype.card V) (w u : V → V → ℝ)
    (hu : ∀ a b, 0 ≤ u a b) (hz : 0 < partition u ∅)
    (hwu : ∀ a b, w a b ≤ u a b)
    (hrlo : ∀ a, (1:ℝ)/8 ≤ rowMax hn u a) (hrhi : ∀ a, rowMax hn u a ≤ 4)
    (S : Finset V) (hS : S.card = 0 ∨ S.card = 2)
    (a b : V) (hab : a < b) (ha : a ∉ S) (hb : b ∉ S) :
    holeAugmentation w a b * holeRatio u (insert a (insert b S)) ≤
      100000 * Fintype.card V / holeScale V := by
  have hcard : (insert a (insert b S)).card = 2 ∨
      (insert a (insert b S)).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [ha,hab.ne]),
      Finset.card_insert_of_notMem hb]
    omega
  have h := hole_relocation hn w u hu hz hwu hrlo hrhi
    (insert a (insert b S)) hcard a b (by simp) (by simp) hab.ne
  have hB : 0 < bottleneck w a b := lt_of_lt_of_le (by norm_num) (one_le_bottleneck w a b)
  have hmul : bottleneck w a b * holeRatio u (insert a (insert b S)) ≤
      100000 * Fintype.card V := by
    have hh := (le_div_iff₀ hB).mp h
    simpa only [mul_comm] using hh
  unfold holeAugmentation
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right hmul holeScale_pos.le

theorem augmented_hole_rate_le [Fintype V] [LinearOrder V]
    (hn : 2 ≤ Fintype.card V) (w u : V → V → ℝ)
    (hu : ∀ a b, 0 ≤ u a b) (hz : 0 < partition u ∅)
    (hwu : ∀ a b, w a b ≤ u a b)
    (hrlo : ∀ a, (1:ℝ)/8 ≤ rowMax hn u a) (hrhi : ∀ a, rowMax hn u a ≤ 4)
    (S : Finset V) (hS : S.card = 0 ∨ S.card = 2) :
    edgeSum S (fun a b => holeAugmentation w a b *
      holeRatio u (insert a (insert b S))) ≤ (1:ℝ)/1000 := by
  have hsum := edgeSum_le_card_sq S _ _
    (show 0 ≤ 100000 * (Fintype.card V : ℝ) / holeScale V by
      exact div_nonneg (by positivity) holeScale_pos.le)
    (augmented_hole_summand hn w u hu hz hwu hrlo hrhi S hS)
  apply hsum.trans
  rw [← mul_div_assoc, div_le_iff₀ holeScale_pos]
  have hnon : (0:ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hp : (Fintype.card V : ℝ)^3 ≤ ((Fintype.card V : ℝ)+1)^4 := by
    calc
      _ ≤ ((Fintype.card V : ℝ)+1)^3 := pow_le_pow_left₀ hnon (by linarith) 3
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega)
  unfold holeScale
  nlinarith only [hp]

theorem row_lower_of_partition_inflation [Fintype V] [LinearOrder V]
    (hn : 2 ≤ Fintype.card V) (w u : V → V → ℝ)
    (hw : ∀ a b, 0 ≤ w a b) (hz : 0 < partition w ∅) (huZ : 0 < partition u ∅)
    (hwu : ∀ a b, w a b ≤ u a b) (hinfl : partition u ∅ ≤ 2 * partition w ∅)
    (hrlo : ∀ a, (1:ℝ)/4 ≤ rowMax hn w a) :
    ∀ a, (1:ℝ)/8 ≤ rowMax hn u a := by
  intro a
  obtain ⟨b,hba,hb⟩ := rowMax_attained hn w a
  apply le_trans _ (holeRatio_le_rowMax hn u a b hba.symm)
  have hg0 : (1:ℝ)/4 ≤ holeRatio w {a,b} := by rw [hb]; exact hrlo a
  have hnum := partition_mono w u hw hwu {a,b}
  rw [holeRatio, le_div_iff₀ hz] at hg0
  rw [holeRatio, le_div_iff₀ huZ]
  linarith

theorem normalized_partition_hasDerivAt [Fintype V] [LinearOrder V]
    (w d : V → V → ℝ) (t : ℝ) (hz0 : partition w ∅ ≠ 0)
    (hzt : partition (affineWeights w d t) ∅ ≠ 0) :
    HasDerivAt (fun s => partition (affineWeights w d s) ∅ / partition w ∅)
      ((edgeSum ∅ (fun a b => d a b * holeRatio (affineWeights w d t) {a,b})) *
        (partition (affineWeights w d t) ∅ / partition w ∅)) t := by
  have hh := (partition_hasDerivAt w d ∅ t).div_const (partition w ∅)
  apply hh.congr_deriv
  simp only [holeRatio, ← mul_div_assoc, edgeSum_div, Finset.insert_empty]
  field_simp

theorem logical_inflation [Fintype V] [LinearOrder V]
    (hn : 2 ≤ Fintype.card V) (w : V → V → ℝ)
    (hw : ∀ a b, 0 ≤ w a b) (hz : 0 < partition w ∅)
    (hrlo : ∀ a, (1:ℝ)/4 ≤ rowMax hn w a) (hrhi : ∀ a, rowMax hn w a ≤ 1) :
    partition (affineWeights w (holeAugmentation w) 1) ∅ < 2 * partition w ∅ := by
  let d := holeAugmentation w
  let u := affineWeights w d
  have hd : ∀ a b, 0 ≤ d a b := holeAugmentation_nonneg w
  have hwu : ∀ t, 0 ≤ t → ∀ a b, w a b ≤ u t a b := by
    intro t ht a b
    exact le_add_of_nonneg_right (mul_nonneg ht (hd a b))
  have hun : ∀ t, 0 ≤ t → ∀ a b, 0 ≤ u t a b := by
    intro t ht a b
    exact (hw a b).trans (hwu t ht a b)
  have huz : ∀ t, 0 ≤ t → 0 < partition (u t) ∅ := by
    intro t ht
    exact affine_partition_pos w d hw hd hz t ht
  let I := Option {p : V × V // p.1 ≠ p.2}
  let f : I → ℝ → ℝ := fun i t => match i with
    | none => partition (u t) ∅ / partition w ∅
    | some p => holeRatio (u t) {p.1.1,p.1.2}
  have hf : ∀ i, ContinuousOn (f i) (Set.Icc 0 1) := by
    intro i t ht
    cases i with
    | none =>
      exact ((partition_hasDerivAt w d ∅ t).div_const (partition w ∅)).continuousAt.continuousWithinAt
    | some p =>
      exact (holeRatio_hasDerivAt w d _ t (huz t ht.1).ne').continuousAt.continuousWithinAt
  have hinit : ∀ i, f i 0 ≤ 1 := by
    intro i
    cases i with
    | none =>
      change partition (u 0) ∅ / partition w ∅ ≤ 1
      have he : u 0 = w := by funext a b; simp [u,affineWeights]
      rw [he,div_self hz.ne']
    | some p =>
      change holeRatio (u 0) {p.1.1,p.1.2} ≤ 1
      have he : u 0 = w := by funext a b; simp [u,affineWeights]
      rw [he]
      exact (holeRatio_le_rowMax hn w p.1.1 p.1.2 p.2).trans (hrhi p.1.1)
  have hderiv : ∀ t ∈ Set.Ioo 0 1, (∀ i, f i t < 2) →
      ∀ i, HasDerivAt (f i) (deriv (f i) t) t ∧ deriv (f i) t ≤ (1:ℝ)/500 := by
    intro t ht hstay
    have hZ : partition (u t) ∅ < 2 * partition w ∅ :=
      (div_lt_iff₀ hz).mp (hstay none)
    have hl := row_lower_of_partition_inflation hn w (u t) hw hz (huz t ht.1.le)
      (hwu t ht.1.le) hZ.le hrlo
    have hh : ∀ a, rowMax hn (u t) a ≤ 4 := by
      intro a
      obtain ⟨b,hba,hb⟩ := rowMax_attained hn (u t) a
      have hh := hstay (some ⟨(a,b),hba.symm⟩)
      change holeRatio (u t) {a,b} < 2 at hh
      rw [hb] at hh
      linarith
    let rate := edgeSum ∅ (fun a b => d a b * holeRatio (u t) {a,b})
    have hrate0 : 0 ≤ rate := edgeSum_nonneg ∅ _ (fun a b _ _ _ =>
      mul_nonneg (hd a b) (holeRatio_nonneg (u t) (hun t ht.1.le) {a,b}))
    have hrate : rate ≤ (1:ℝ)/1000 := by
      simpa only [Finset.insert_empty] using
        augmented_hole_rate_le hn w (u t) (hun t ht.1.le) (huz t ht.1.le)
          (hwu t ht.1.le) hl hh ∅ (Or.inl rfl)
    intro i
    cases i with
    | none =>
      have hdf := normalized_partition_hasDerivAt w d t hz.ne' (huz t ht.1.le).ne'
      change HasDerivAt (f none) (rate * f none t) t at hdf
      refine ⟨hdf.differentiableAt.hasDerivAt, ?_⟩
      rw [hdf.deriv]
      have hle : rate * f none t ≤ rate * 2 := mul_le_mul_of_nonneg_left (hstay none).le hrate0
      linarith
    | some p =>
      have hdf := holeRatio_hasDerivAt w d {p.1.1,p.1.2} t (huz t ht.1.le).ne'
      change HasDerivAt (f (some p)) _ t at hdf
      refine ⟨hdf.differentiableAt.hasDerivAt, ?_⟩
      rw [hdf.deriv]
      have hpcard : ({p.1.1,p.1.2} : Finset V).card = 2 := by simp [p.2]
      have hnum := augmented_hole_rate_le hn w (u t) (hun t ht.1.le) (huz t ht.1.le)
        (hwu t ht.1.le) hl hh {p.1.1,p.1.2} (Or.inr hpcard)
      have hg := holeRatio_nonneg (u t) (hun t ht.1.le) {p.1.1,p.1.2}
      have hprod := mul_nonneg hg hrate0
      change 0 ≤ holeRatio (u t) {p.1.1,p.1.2} * rate at hprod
      change edgeSum {p.1.1,p.1.2} (fun a b => d a b *
        holeRatio (u t) (insert a (insert b {p.1.1,p.1.2}))) -
        holeRatio (u t) {p.1.1,p.1.2} * rate ≤ (1:ℝ)/500
      change edgeSum {p.1.1,p.1.2} (fun a b => d a b *
        holeRatio (u t) (insert a (insert b {p.1.1,p.1.2}))) ≤ (1:ℝ)/1000 at hnum
      linarith
  have hstay := finite_family_barrier f (fun i => deriv (f i)) ((1:ℝ)/500)
    (by norm_num) (by norm_num) hf hinit hderiv 1 (by constructor <;> norm_num) none
  exact (div_lt_iff₀ hz).mp hstay

end MatchingFPRAS.Switching

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_FillHoles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Switching
open Finset
open scoped Classical symmDiff

variable {V : Type*}

theorem fillHoles_perfect [Fintype V] [DecidableEq V] (m q : Mate V) (S : Finset V)
    (hm : HasHoles m S) (hq : HasHoles q Sᶜ) : HasHoles (fillHoles m q S hm hq) ∅ := by
  classical
  intro v
  simp only [fillHoles_apply, Finset.notMem_empty, iff_false]
  by_cases hv : v ∈ S
  · rw [ite_eq_left hv]
    intro he
    exact (Finset.mem_compl.mp ((hq v).mp he)) hv
  · rw [ite_eq_right hv]
    intro he
    exact hv ((hm v).mp he)

theorem fillHoles_injective [Fintype V] [DecidableEq V] (q : Mate V) (S : Finset V)
    (hq : HasHoles q Sᶜ) : Function.Injective
      (fun m : {m : Mate V // HasHoles m S} => fillHoles m.1 q S m.2 hq) := by
  classical
  intro m n he
  apply Subtype.ext
  apply Subtype.ext
  funext v
  by_cases hv : v ∈ S
  · exact ((m.2 v).mpr hv).trans ((n.2 v).mpr hv).symm
  · have h := congrArg (fun r : Mate V => r.1 v) he
    simpa [hv] using h

theorem fillHoles_weight_le [Fintype V] [LinearOrder V]
    (w d u : V → V → ℝ) (hw : ∀ a b, 0 ≤ w a b) (hd : ∀ a b, 0 ≤ d a b)
    (hwu : ∀ a b, w a b ≤ u a b) (hdu : ∀ a b, d a b ≤ u a b)
    (m q : Mate V) (S : Finset V) (hm : HasHoles m S) (hq : HasHoles q Sᶜ) :
    weight w m * weight d q ≤ weight u (fillHoles m q S hm hq) := by
  classical
  unfold weight
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  · intro v _
    exact mul_nonneg (by split_ifs; exact hw _ _; norm_num)
      (by split_ifs; exact hd _ _; norm_num)
  · intro v _
    rw [fillHoles_apply]
    by_cases hv : v ∈ S
    · have hmfix := (hm v).mpr hv
      simp only [hv, ite_true, hmfix, lt_self_iff_false, ite_false, one_mul]
      split_ifs
      · exact hdu _ _
      · rfl
    · have hqfix := (hq v).mpr (Finset.mem_compl.mpr hv)
      simp only [hv, ite_false, hqfix, lt_self_iff_false, mul_one]
      split_ifs
      · exact hwu _ _
      · rfl

theorem fillHoles_partition_le [Fintype V] [LinearOrder V]
    (w d u : V → V → ℝ) (hw : ∀ a b, 0 ≤ w a b) (hd : ∀ a b, 0 ≤ d a b)
    (hwu : ∀ a b, w a b ≤ u a b) (hdu : ∀ a b, d a b ≤ u a b)
    (q : Mate V) (S : Finset V) (hq : HasHoles q Sᶜ) :
    partition w S * weight d q ≤ partition u ∅ := by
  classical
  let f : Mate V → Mate V := fun m =>
    if hm : HasHoles m S then fillHoles m q S hm hq else m
  have hi : Set.InjOn f (matchings S) := by
    intro m hm n hn he
    have hm' := (mem_matchings m S).mp hm
    have hn' := (mem_matchings n S).mp hn
    have h : (⟨m,hm'⟩ : {m : Mate V // HasHoles m S}) = ⟨n,hn'⟩ :=
      fillHoles_injective q S hq (by simpa [f,hm',hn'] using he)
    exact congrArg Subtype.val h
  have hsub : (matchings S).image f ⊆ matchings ∅ := by
    intro m hm
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hm
    have hn' := (mem_matchings n S).mp hn
    simp only [f,dite_eq_left hn',mem_matchings]
    exact fillHoles_perfect n q S hn' hq
  calc
    partition w S * weight d q = ∑ m ∈ matchings S, weight w m * weight d q :=
      Finset.sum_mul _ _ _
    _ ≤ ∑ m ∈ matchings S, weight u (f m) := by
      apply Finset.sum_le_sum
      intro m hm
      have hm' := (mem_matchings m S).mp hm
      simpa [f,hm'] using fillHoles_weight_le w d u hw hd hwu hdu m q S hm' hq
    _ = ∑ m ∈ (matchings S).image f, weight u m := (Finset.sum_image hi).symm
    _ ≤ partition u ∅ := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun m _ _ => weight_nonneg u (fun a b => (hw a b).trans (hwu a b)) m)

theorem weight_div_const [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (c : ℝ) (q : Mate V) (S : Finset V) (hq : HasHoles q Sᶜ) :
    weight (fun a b => w a b / c) q = weight w q / c^(S.card/2) := by
  have hc : (Finset.univ.filter (fun v => v < q.1 v)).card = S.card/2 := by
    have := mate_edge_count q S hq
    omega
  unfold weight
  rw [← Finset.prod_filter, ← Finset.prod_filter, Finset.prod_div_distrib]
  simp only [Finset.prod_const, hc]

theorem logical_hole_bound [Fintype V] [LinearOrder V]
    (hn : 2 ≤ Fintype.card V) (w : V → V → ℝ)
    (hw : ∀ a b, 0 ≤ w a b) (hz : 0 < partition w ∅)
    (hrlo : ∀ a, (1:ℝ)/4 ≤ rowMax hn w a) (hrhi : ∀ a, rowMax hn w a ≤ 1)
    (S : Finset V) (hS : Even S.card) :
    holeRatio w S * pairingCapacity (bottleneck w) S hS ≤
      2 * holeScale V ^ (S.card / 2) := by
  classical
  obtain ⟨q,hq,hmax⟩ := Finset.exists_mem_eq_sup'
    (show (matchings Sᶜ).Nonempty from by
      obtain ⟨q,hq⟩ := pairing_exists S hS
      exact ⟨q,(mem_matchings _ _).mpr hq⟩) (weight (bottleneck w))
  have hq' := (mem_matchings q Sᶜ).mp hq
  have hc : pairingCapacity (bottleneck w) S hS = weight (bottleneck w) q := hmax
  let d := holeAugmentation w
  let u := affineWeights w d 1
  have hd : ∀ a b, 0 ≤ d a b := holeAugmentation_nonneg w
  have hfill := fillHoles_partition_le w d u hw hd
    (fun a b => by change w a b ≤ w a b + 1*d a b; linarith [hd a b])
    (fun a b => by change d a b ≤ w a b + 1*d a b; linarith [hw a b]) q S hq'
  have hinfl := logical_inflation hn w hw hz hrlo hrhi
  have hdiv : weight d q = weight (bottleneck w) q / holeScale V ^ (S.card/2) :=
    weight_div_const (bottleneck w) (holeScale V) q S hq'
  rw [hdiv] at hfill
  rw [hc,holeRatio]
  have hpow : 0 < holeScale V ^ (S.card/2) := pow_pos holeScale_pos _
  have hmain : partition w S * weight (bottleneck w) q ≤
      2 * partition w ∅ * holeScale V ^ (S.card/2) := by
    have h' := hfill.trans hinfl.le
    rw [← mul_div_assoc, div_le_iff₀ hpow] at h'
    exact h'
  rw [div_mul_eq_mul_div, div_le_iff₀ hz]
  nlinarith only [hmain]

end MatchingFPRAS.Switching

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_ThresholdGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Switching

open Finset

variable {V : Type*}

theorem erasePair_factor [Fintype V] [LinearOrder V] (B : V → V → ℝ)
    (hB : ∀ a b, B a b = B b a) (q : Mate V) (a b : V)
    (hq : q.val a = b) (hab : a ≠ b) :
    weight B q = B a b * weight B (erasePair q a b) := by
  have ha : (erasePair q a b).val a = a := by simp [hq]
  have hb : (erasePair q a b).val b = b := by simp [hq]
  have hw := withEdge_weight B (erasePair q a b) a b ha hb hab
  rw [withEdge_erasePair q a b hq,edgeActivity_of_symmetric B hB] at hw
  exact hw

lemma ultrametric_vertex_charge {A C D T : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hD : 0 ≤ D) (hAT : A ≤ T) (hCT : C ≤ T) (htri : min A C ≤ D) :
    A*C ≤ T*D := by
  rcases le_total A C with h | h
  · rw [min_eq_left h] at htri
    exact (mul_le_mul htri hCT hC hD).trans_eq (mul_comm D T)
  · rw [min_eq_right h] at htri
    exact mul_le_mul hAT htri hC (hA.trans hAT)

lemma ultrametric_pair_charge {A B C D Tj Tk : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hAj : A ≤ Tj) (hBk : B ≤ Tk) (hCj : C ≤ Tj) (hCk : C ≤ Tk)
    (htri : min A (min C B) ≤ D) : A*B*C ≤ Tj*Tk*D := by
  have hj0 := hA.trans hAj
  have hk0 := hB.trans hBk
  rcases le_total A (min C B) with h | h
  · rw [min_eq_left h] at htri
    calc
      A*B*C ≤ D*Tk*Tj := by gcongr
      _ = Tj*Tk*D := by ring
  · rw [min_eq_right h] at htri
    rcases le_total C B with hcb | hbc
    · rw [min_eq_left hcb] at htri
      gcongr
    · rw [min_eq_right hbc] at htri
      calc
        A*B*C ≤ Tj*D*Tk := by gcongr
        _ = Tj*Tk*D := by ring

lemma pairing_mate_mem [Fintype V] [DecidableEq V] (q : Mate V) (U : Finset V)
    (hq : HasHoles q Uᶜ) (v : V) : q.val v ∈ U ↔ v ∈ U := by
  have h := mate_mem_holes_iff q Uᶜ hq v
  simpa only [Finset.mem_compl, not_iff_not] using h

theorem pairing_replace_vertex [Fintype V] [LinearOrder V]
    (B : V → V → ℝ) (hB : ∀ a b, B a b = B b a)
    (hB0 : ∀ a b, 0 ≤ B a b)
    (htri : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → min (B a c) (B c b) ≤ B a b)
    (U : Finset V) (j u : V) (hj : j ∈ U) (hu : u ∉ U)
    (T : ℝ) (hT : ∀ a, a ≠ j → B j a ≤ T)
    (q : Mate V) (hq : HasHoles q Uᶜ) :
    ∃ q' : Mate V, HasHoles q' (insert u (U.erase j))ᶜ ∧
      weight B q * B j u ≤ T * weight B q' := by
  classical
  let a := q.val j
  have hja : j ≠ a := by
    intro h
    exact (Finset.mem_compl.mp ((hq j).mp h.symm)) hj
  have haU : a ∈ U := (pairing_mate_mem q U hq j).mpr hj
  have hua : u ≠ a := fun h => hu (h ▸ haU)
  have huj : u ≠ j := fun h => hu (h ▸ hj)
  have hqj : q.val j = a := rfl
  have hqa : q.val a = j := mate_mate q j
  have hqu : q.val u = u := (hq u).mpr (Finset.mem_compl.mpr hu)
  let r := erasePair q j a
  have hra : r.val a = a := by simp [r,hqj]
  have hru : r.val u = u := by simp [r,hqj,huj,hua,hqu]
  let q' := withEdge r u a
  have he (v) : q'.val v = if v = u then a else if v = a then u
      else if v = j ∨ v = a then v else q.val v := by
    rw [show q'.val v = (withEdge r u a).val v from rfl,
      withEdge_apply r u a v hru hra,erasePair_apply q j a v hqj]
    split_ifs <;> rfl
  refine ⟨q',?_,?_⟩
  · intro v
    rw [he]
    by_cases hvu : v = u
    · subst v
      simp [hua.symm]
    by_cases hva : v = a
    · subst v
      simp [hvu,hua,haU,hja.symm]
    by_cases hvj : v = j
    · subst v
      simp [hvu,hva]
    simp only [hvu,hva,hvj,false_or,↓reduceIte]
    rw [hq]
    simp [hvu,hvj]
  · have hwq := erasePair_factor B hB q j a hqj hja
    have hwq' : weight B q' = B u a * weight B r := by
      simpa only [q',edgeActivity_of_symmetric B hB] using withEdge_weight B r u a hru hra hua
    have ht : min (B j a) (B j u) ≤ B u a := by
      have hh := htri u a j hua huj hja.symm
      simpa only [hB u j,min_comm] using hh
    have hh := ultrametric_vertex_charge (hB0 j a) (hB0 j u) (hB0 u a)
      (hT a hja.symm) (hT u huj) ht
    have hr0 := weight_nonneg B hB0 r
    have hf := mul_le_mul_of_nonneg_right hh hr0
    rw [hwq,hwq']
    dsimp only [r] at hf
    nlinarith only [hf]

theorem pairing_remove_pair [Fintype V] [LinearOrder V]
    (B : V → V → ℝ) (hB : ∀ a b, B a b = B b a)
    (hB0 : ∀ a b, 0 ≤ B a b)
    (htri : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → min (B a c) (B c b) ≤ B a b)
    (U : Finset V) (j k : V) (hj : j ∈ U) (hk : k ∈ U) (hjk : j ≠ k)
    (Tj Tk : ℝ) (hTj : ∀ a, a ≠ j → B j a ≤ Tj)
    (hTk : ∀ a, a ≠ k → B k a ≤ Tk)
    (q : Mate V) (hq : HasHoles q Uᶜ) :
    ∃ q' : Mate V, HasHoles q' (U \ {j,k})ᶜ ∧
      weight B q * B j k ≤ Tj * Tk * weight B q' := by
  classical
  have hcj : B j k ≤ Tj := hTj k hjk.symm
  have hck : B j k ≤ Tk := (hB j k).trans_le (hTk j hjk)
  by_cases hqjk : q.val j = k
  · let q' := erasePair q j k
    refine ⟨q',?_,?_⟩
    · have hh := erasePair_holes q Uᶜ hq j k hqjk
      have he : insert j (insert k Uᶜ) = (U \ {j,k})ᶜ := by ext v; simp; tauto
      rwa [he] at hh
    · rw [erasePair_factor B hB q j k hqjk hjk]
      have hv := weight_nonneg B hB0 q'
      change (B j k * weight B q') * B j k ≤ _
      calc
        _ = (B j k * B j k) * weight B q' := by ring
        _ ≤ (Tj*Tk) * weight B q' := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul hcj hck (hB0 j k) ((hB0 j k).trans hcj)) hv
  · let a := q.val j
    let b := q.val k
    have hqj : q.val j = a := rfl
    have hqk : q.val k = b := rfl
    have hqa : q.val a = j := mate_mate q j
    have hqb : q.val b = k := mate_mate q k
    have hja : j ≠ a := by
      intro h
      exact (Finset.mem_compl.mp ((hq j).mp h.symm)) hj
    have hkb : k ≠ b := by
      intro h
      exact (Finset.mem_compl.mp ((hq k).mp h.symm)) hk
    have hak : a ≠ k := hqjk
    have hbj : b ≠ j := by
      intro h
      have hh := congrArg q.val h
      rw [hqb,hqj] at hh
      exact hak hh.symm
    have hab : a ≠ b := by
      intro h
      have hh := congrArg q.val h
      rw [hqa,hqb] at hh
      exact hjk hh
    have haU : a ∈ U := (pairing_mate_mem q U hq j).mpr hj
    have hbU : b ∈ U := (pairing_mate_mem q U hq k).mpr hk
    let r := erasePair q j a
    have hrk : r.val k = b := by simp [r,hqj,hjk.symm,hak.symm,hqk]
    let z := erasePair r k b
    have hza : z.val a = a := by
      rw [show z.val a = (erasePair r k b).val a from rfl, erasePair_apply r k b a hrk]
      simp [hak,hab,r,hqj]
    have hzb : z.val b = b := by simp [z,hrk]
    let q' := withEdge z a b
    have he (v) : q'.val v = if v = a then b else if v = b then a
        else if v = k ∨ v = b then v else if v = j ∨ v = a then v else q.val v := by
      rw [show q'.val v = (withEdge z a b).val v from rfl,
        withEdge_apply z a b v hza hzb,erasePair_apply r k b v hrk,
        erasePair_apply q j a v hqj]
      split_ifs <;> rfl
    refine ⟨q',?_,?_⟩
    · intro v
      rw [he]
      by_cases hva : v = a
      · subst v
        simp [hab.symm,haU,hja.symm,hak]
      by_cases hvb : v = b
      · subst v
        simp [hva,hab,hbU,hbj,hkb.symm]
      by_cases hvj : v = j
      · subst v
        simp [hva,hvb]
      by_cases hvk : v = k
      · subst v
        simp [hva,hvb]
      simp only [hva,hvb,hvj,hvk,false_or,↓reduceIte]
      rw [hq]
      simp [hvj,hvk]
    · have hwq := erasePair_factor B hB q j a hqj hja
      have hwr := erasePair_factor B hB r k b hrk hkb
      have hwq' : weight B q' = B a b * weight B z := by
        simpa only [q',edgeActivity_of_symmetric B hB] using withEdge_weight B z a b hza hzb hab
      have ht : min (B j a) (min (B j k) (B k b)) ≤ B a b := by
        calc
          _ ≤ min (B j a) (B j b) :=
            min_le_min_left _ (htri j b k hbj.symm hjk hkb.symm)
          _ = min (B a j) (B j b) := by rw [hB j a]
          _ ≤ _ := htri a b j hab hja.symm hbj
      have hh := ultrametric_pair_charge (hB0 j a) (hB0 k b) (hB0 j k) (hB0 a b)
        (hTj a hja.symm) (hTk b hkb.symm) hcj hck ht
      have hz0 := weight_nonneg B hB0 z
      have hf := mul_le_mul_of_nonneg_right hh hz0
      rw [hwq,show weight B (erasePair q j a) = weight B r from rfl,hwr,hwq']
      change (B j a * (B k b * weight B z)) * B j k ≤ Tj*Tk*(B a b*weight B z)
      nlinarith only [hf]

lemma weight_le_pairingCapacity [Fintype V] [LinearOrder V]
    (B : V → V → ℝ) (U : Finset V) (hU : Even U.card)
    (q : Mate V) (hq : HasHoles q Uᶜ) : weight B q ≤ pairingCapacity B U hU := by
  exact Finset.le_sup' _ ((mem_matchings q Uᶜ).mpr hq)

lemma pairingCapacity_nonneg [Fintype V] [LinearOrder V]
    (B : V → V → ℝ) (hB : ∀ a b, 0 ≤ B a b)
    (U : Finset V) (hU : Even U.card) : 0 ≤ pairingCapacity B U hU := by
  obtain ⟨q,hq⟩ := pairing_exists U hU
  exact (weight_nonneg B hB q).trans (weight_le_pairingCapacity B U hU q hq)

theorem capacity_replace_vertex [Fintype V] [LinearOrder V]
    (B : V → V → ℝ) (hB : ∀ a b, B a b = B b a)
    (hB0 : ∀ a b, 0 ≤ B a b)
    (htri : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → min (B a c) (B c b) ≤ B a b)
    (U : Finset V) (hU : Even U.card) (j u : V) (hj : j ∈ U) (hu : u ∉ U)
    (hU' : Even (insert u (U.erase j)).card)
    (T : ℝ) (hT0 : 0 ≤ T) (hT : ∀ a, a ≠ j → B j a ≤ T) :
    pairingCapacity B U hU * B j u ≤ T * pairingCapacity B (insert u (U.erase j)) hU' := by
  classical
  obtain ⟨q,hq,hmax⟩ := Finset.exists_mem_eq_sup'
    (show (matchings Uᶜ).Nonempty from by
      obtain ⟨q,hq⟩ := pairing_exists U hU
      exact ⟨q,(mem_matchings _ _).mpr hq⟩) (weight B)
  have hcap : pairingCapacity B U hU = weight B q := hmax
  obtain ⟨q',hq',hle⟩ := pairing_replace_vertex B hB hB0 htri U j u hj hu T hT q
    ((mem_matchings _ _).mp hq)
  rw [hcap]
  exact hle.trans (mul_le_mul_of_nonneg_left
    (weight_le_pairingCapacity B _ hU' q' hq') hT0)

theorem capacity_remove_pair [Fintype V] [LinearOrder V]
    (B : V → V → ℝ) (hB : ∀ a b, B a b = B b a)
    (hB0 : ∀ a b, 0 ≤ B a b)
    (htri : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → min (B a c) (B c b) ≤ B a b)
    (U : Finset V) (hU : Even U.card) (j k : V) (hj : j ∈ U) (hk : k ∈ U) (hjk : j ≠ k)
    (hU' : Even (U \ {j,k}).card)
    (Tj Tk : ℝ) (hj0 : 0 ≤ Tj) (hk0 : 0 ≤ Tk)
    (hTj : ∀ a, a ≠ j → B j a ≤ Tj) (hTk : ∀ a, a ≠ k → B k a ≤ Tk) :
    pairingCapacity B U hU * B j k ≤ Tj * Tk * pairingCapacity B (U \ {j,k}) hU' := by
  classical
  obtain ⟨q,hq,hmax⟩ := Finset.exists_mem_eq_sup'
    (show (matchings Uᶜ).Nonempty from by
      obtain ⟨q,hq⟩ := pairing_exists U hU
      exact ⟨q,(mem_matchings _ _).mpr hq⟩) (weight B)
  have hcap : pairingCapacity B U hU = weight B q := hmax
  obtain ⟨q',hq',hle⟩ := pairing_remove_pair B hB hB0 htri U j k hj hk hjk Tj Tk hTj hTk q
    ((mem_matchings _ _).mp hq)
  rw [hcap]
  exact hle.trans (mul_le_mul_of_nonneg_left
    (weight_le_pairingCapacity B _ hU' q' hq') (mul_nonneg hj0 hk0))

theorem capacity_charged_remove [Fintype V] [LinearOrder V]
    (B : V → V → ℝ) (hB : ∀ a b, B a b = B b a) (hB0 : ∀ a b, 0 ≤ B a b)
    (htri : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → min (B a c) (B c b) ≤ B a b)
    (U : Finset V) (hU : Even U.card) (j k : V) (hj : j ∈ U) (hk : k ∈ U)
    (hjk : j ≠ k) (hU' : Even (U \ {j,k}).card) (Tj Tk f : ℝ)
    (hj0 : 0 < Tj) (hk0 : 0 < Tk) (hTj : ∀ a, a ≠ j → B j a ≤ Tj)
    (hTk : ∀ a, a ≠ k → B k a ≤ Tk) (hf : f*Tj*Tk ≤ B j k) :
    pairingCapacity B U hU * f ≤ pairingCapacity B (U \ {j,k}) hU' := by
  have hc := capacity_remove_pair B hB hB0 htri U hU j k hj hk hjk hU'
    Tj Tk hj0.le hk0.le hTj hTk
  have hs := mul_le_mul_of_nonneg_left hf (pairingCapacity_nonneg B hB0 U hU)
  have hprod : 0 < Tj*Tk := mul_pos hj0 hk0
  apply (mul_le_mul_iff_of_pos_right hprod).mp
  calc
    _ = pairingCapacity B U hU * (f*Tj*Tk) := by ring
    _ ≤ pairingCapacity B U hU * B j k := hs
    _ ≤ _ := by nlinarith only [hc]

theorem capacity_charged_replace [Fintype V] [LinearOrder V]
    (B : V → V → ℝ) (hB : ∀ a b, B a b = B b a) (hB0 : ∀ a b, 0 ≤ B a b)
    (htri : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → min (B a c) (B c b) ≤ B a b)
    (U : Finset V) (hU : Even U.card) (j u : V) (hj : j ∈ U) (hu : u ∉ U)
    (hU' : Even (insert u (U.erase j)).card) (T f : ℝ)
    (hT0 : 0 < T) (hT : ∀ a, a ≠ j → B j a ≤ T) (hf : f*T ≤ B j u) :
    pairingCapacity B U hU * f ≤ pairingCapacity B (insert u (U.erase j)) hU' := by
  have hc := capacity_replace_vertex B hB hB0 htri U hU j u hj hu hU' T hT0.le hT
  have hs := mul_le_mul_of_nonneg_left hf (pairingCapacity_nonneg B hB0 U hU)
  apply (mul_le_mul_iff_of_pos_right hT0).mp
  calc
    _ = pairingCapacity B U hU * (f*T) := by ring
    _ ≤ pairingCapacity B U hU * B j u := hs
    _ ≤ _ := by nlinarith only [hc]

lemma ChargeTrace.card_le [DecidableEq V] {B : V → V → ℝ}
    {U W : Finset V} {F : ℝ} (h : ChargeTrace B U W F) : W.card ≤ U.card := by
  induction h with
  | done => rfl
  | remove U W j k hj hk hjk Tj Tk f F hj0 hk0 hf0 hF0 hTj hTk hf next ih =>
    exact ih.trans (Finset.card_le_card Finset.sdiff_subset)
  | replace U W j u hj hu T f F hT0 hf0 hF0 hT hf next ih =>
    have hnu : u ∉ U.erase j := fun h => hu (Finset.mem_of_mem_erase h)
    rw [Finset.card_insert_of_notMem hnu,Finset.card_erase_of_mem hj] at ih
    have : 0 < U.card := Finset.card_pos.mpr ⟨j,hj⟩
    omega

lemma even_remove_two [DecidableEq V] (U : Finset V) (hU : Even U.card)
    (j k : V) (hj : j ∈ U) (hk : k ∈ U) (hjk : j ≠ k) :
    Even (U \ {j,k}).card := by
  have he : U \ {j,k} = (U.erase j).erase k := by ext a; simp; tauto
  have hk' : k ∈ U.erase j := Finset.mem_erase.mpr ⟨hjk.symm,hk⟩
  rw [he,Finset.card_erase_of_mem hk',Finset.card_erase_of_mem hj]
  have h2 : 2 ≤ U.card := by
    apply (Finset.card_pair hjk).symm.trans_le
    apply Finset.card_le_card
    intro a ha
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl | rfl <;> assumption
  exact (Nat.even_iff.mpr (by have := Nat.even_iff.mp hU; omega))

lemma even_replace_one [DecidableEq V] (U : Finset V) (hU : Even U.card)
    (j u : V) (hj : j ∈ U) (hu : u ∉ U) : Even (insert u (U.erase j)).card := by
  have hnu : u ∉ U.erase j := fun h => hu (Finset.mem_of_mem_erase h)
  rw [Finset.card_insert_of_notMem hnu,Finset.card_erase_of_mem hj]
  have : 0 < U.card := Finset.card_pos.mpr ⟨j,hj⟩
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ U.card)] using hU

theorem ChargeTrace.capacity_bound [Fintype V] [LinearOrder V]
    {B : V → V → ℝ} (hB : ∀ a b, B a b = B b a) (hB0 : ∀ a b, 0 ≤ B a b)
    (htri : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → min (B a c) (B c b) ≤ B a b)
    {U W : Finset V} {F : ℝ} (h : ChargeTrace B U W F) (hU : Even U.card) :
    ∃ hW : Even W.card, pairingCapacity B U hU * F ≤ pairingCapacity B W hW := by
  induction h with
  | done U => exact ⟨hU,by simp⟩
  | remove U W j k hj hk hjk Tj Tk f F hj0 hk0 hf0 hF0 hTj hTk hf next ih =>
    have he := even_remove_two U hU j k hj hk hjk
    obtain ⟨hW,hWb⟩ := ih he
    refine ⟨hW,?_⟩
    calc
      _ = (pairingCapacity B U hU * f) * F := by ring
      _ ≤ pairingCapacity B (U \ {j,k}) he * F := mul_le_mul_of_nonneg_right
        (capacity_charged_remove B hB hB0 htri U hU j k hj hk hjk he Tj Tk f
          hj0 hk0 hTj hTk hf) hF0
      _ ≤ _ := hWb
  | replace U W j u hj hu T f F hT0 hf0 hF0 hT hf next ih =>
    have he := even_replace_one U hU j u hj hu
    obtain ⟨hW,hWb⟩ := ih he
    refine ⟨hW,?_⟩
    calc
      _ = (pairingCapacity B U hU * f) * F := by ring
      _ ≤ pairingCapacity B (insert u (U.erase j)) he * F := mul_le_mul_of_nonneg_right
        (capacity_charged_replace B hB hB0 htri U hU j u hj hu he T f hT0 hT hf) hF0
      _ ≤ _ := hWb

lemma ChargeTrace.trans [DecidableEq V] {B : V → V → ℝ}
    {U W X : Finset V} {F G : ℝ} (h : ChargeTrace B U W F)
    (h' : ChargeTrace B W X G) (hG : 0 ≤ G) : ChargeTrace B U X (F*G) := by
  induction h with
  | done U => simpa using h'
  | remove U W j k hj hk hjk Tj Tk f F hj0 hk0 hf0 hF0 hTj hTk hf next ih =>
    have ht := ChargeTrace.remove U X j k hj hk hjk Tj Tk f (F*G) hj0 hk0 hf0
      (mul_nonneg hF0 hG) hTj hTk hf (ih h')
    simpa [mul_assoc] using ht
  | replace U W j u hj hu T f F hT0 hf0 hF0 hT hf next ih =>
    have ht := ChargeTrace.replace U X j u hj hu T f (F*G) hT0 hf0
      (mul_nonneg hF0 hG) hT hf (ih h')
    simpa [mul_assoc] using ht

theorem charge_remove_list [DecidableEq V] (B : V → V → ℝ) (T : V → ℝ)
    (f : V × V → ℝ) (xs : List (V × V)) (U : Finset V)
    (hnd : (pairVertices xs).Nodup) (hsub : ∀ a ∈ pairVertices xs, a ∈ U)
    (hlocal : ∀ q ∈ xs,
      0 < T q.1 ∧ 0 < T q.2 ∧ 0 ≤ f q ∧
      (∀ a, a ≠ q.1 → B q.1 a ≤ T q.1) ∧
      (∀ a, a ≠ q.2 → B q.2 a ≤ T q.2) ∧ f q*T q.1*T q.2 ≤ B q.1 q.2) :
    ChargeTrace B U (U \ (pairVertices xs).toFinset) (xs.map f).prod := by
  induction xs generalizing U with
  | nil => simpa [pairVertices] using ChargeTrace.done (B := B) U
  | cons q xs ih =>
    obtain ⟨j,k⟩ := q
    have hn : j ≠ k ∧ j ∉ pairVertices xs ∧ k ∉ pairVertices xs ∧ (pairVertices xs).Nodup := by
      simpa [pairVertices,List.nodup_cons,and_assoc] using hnd
    have hj : j ∈ U := hsub j (by simp [pairVertices])
    have hk : k ∈ U := hsub k (by simp [pairVertices])
    have hs : ∀ a ∈ pairVertices xs, a ∈ U \ {j,k} := by
      intro a ha
      have haj : a ≠ j := fun he => hn.2.1 (he ▸ ha)
      have hak : a ≠ k := fun he => hn.2.2.1 (he ▸ ha)
      simp only [Finset.mem_sdiff,Finset.mem_insert,Finset.mem_singleton,not_or]
      exact ⟨hsub a (by simp [pairVertices] at ha ⊢; exact Or.inr (Or.inr ha)),haj,hak⟩
    have hl : ∀ q ∈ xs,
      0 < T q.1 ∧ 0 < T q.2 ∧ 0 ≤ f q ∧
      (∀ a, a ≠ q.1 → B q.1 a ≤ T q.1) ∧
      (∀ a, a ≠ q.2 → B q.2 a ≤ T q.2) ∧ f q*T q.1*T q.2 ≤ B q.1 q.2 :=
      fun q hq => hlocal q (List.mem_cons_of_mem _ hq)
    have ht := ih (U \ {j,k}) hn.2.2.2 hs hl
    have hp : 0 ≤ (xs.map f).prod := by
      apply List.prod_nonneg
      intro a ha
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ha
      exact (hl q hq).2.2.1
    have he : (U \ {j,k}) \ (pairVertices xs).toFinset =
        U \ (pairVertices ((j,k)::xs)).toFinset := by
      ext a
      simp [pairVertices]
      tauto
    obtain ⟨hTj,hTk,hf,hjrow,hkrow,hbound⟩ := hlocal (j,k) (by simp)
    have hr := ChargeTrace.remove U _ j k hj hk hn.1 (T j) (T k) (f (j,k))
      (xs.map f).prod hTj hTk hf hp hjrow hkrow hbound ht
    simpa only [List.map_cons,List.prod_cons,he] using hr

theorem charge_replace_list [DecidableEq V] (B : V → V → ℝ) (T : V → ℝ)
    (f : V × V → ℝ) (xs : List (V × V)) (U : Finset V)
    (hsrc : (xs.map Prod.fst).Nodup) (hdst : (xs.map Prod.snd).Nodup)
    (hsub : ∀ q ∈ xs, q.1 ∈ U) (hfresh : ∀ q ∈ xs, q.2 ∉ U)
    (hlocal : ∀ q ∈ xs, 0 < T q.1 ∧ 0 ≤ f q ∧
      (∀ a, a ≠ q.1 → B q.1 a ≤ T q.1) ∧ f q*T q.1 ≤ B q.1 q.2) :
    ChargeTrace B U ((U \ (xs.map Prod.fst).toFinset) ∪ (xs.map Prod.snd).toFinset)
      (xs.map f).prod := by
  induction xs generalizing U with
  | nil => simpa using ChargeTrace.done (B := B) U
  | cons q xs ih =>
    obtain ⟨j,u⟩ := q
    have hsrc' : j ∉ xs.map Prod.fst ∧ (xs.map Prod.fst).Nodup := by simpa using hsrc
    have hdst' : u ∉ xs.map Prod.snd ∧ (xs.map Prod.snd).Nodup := by simpa using hdst
    have hj : j ∈ U := hsub (j,u) (by simp)
    have hu : u ∉ U := hfresh (j,u) (by simp)
    have hs : ∀ q ∈ xs, q.1 ∈ insert u (U.erase j) := by
      intro q hq
      have hn : q.1 ≠ j := by
        intro he; exact hsrc'.1 (he ▸ List.mem_map.mpr ⟨q,hq,rfl⟩)
      simp only [Finset.mem_insert,Finset.mem_erase]
      exact Or.inr ⟨hn,hsub q (by simp [hq])⟩
    have hf : ∀ q ∈ xs, q.2 ∉ insert u (U.erase j) := by
      intro q hq
      have hn : q.2 ≠ u := by
        intro he; exact hdst'.1 (he ▸ List.mem_map.mpr ⟨q,hq,rfl⟩)
      simp only [Finset.mem_insert,Finset.mem_erase,not_or,not_and]
      exact ⟨hn,fun _ => hfresh q (by simp [hq])⟩
    have hl : ∀ q ∈ xs, 0 < T q.1 ∧ 0 ≤ f q ∧
      (∀ a, a ≠ q.1 → B q.1 a ≤ T q.1) ∧ f q*T q.1 ≤ B q.1 q.2 :=
      fun q hq => hlocal q (List.mem_cons_of_mem _ hq)
    have ht := ih (insert u (U.erase j)) hsrc'.2 hdst'.2 hs hf hl
    have hp : 0 ≤ (xs.map f).prod := by
      apply List.prod_nonneg
      intro a ha
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ha
      exact (hl q hq).2.1
    have hus : u ∉ xs.map Prod.fst := by
      rintro h
      obtain ⟨q,hq,he⟩ := List.mem_map.mp h
      exact hu (he ▸ hsub q (by simp [hq]))
    have he : ((insert u (U.erase j)) \ (xs.map Prod.fst).toFinset) ∪ (xs.map Prod.snd).toFinset =
        (U \ (((j,u)::xs).map Prod.fst).toFinset) ∪ (((j,u)::xs).map Prod.snd).toFinset := by
      ext a
      by_cases hau : a=u
      · subst a; simp [hus]
      · simp only [List.map_cons,List.toFinset_cons,Finset.mem_union,Finset.mem_sdiff,
          Finset.mem_insert,Finset.mem_erase,List.mem_toFinset,hau,false_or]
        tauto
    obtain ⟨hT,hf0,hrow,hbound⟩ := hlocal (j,u) (by simp)
    have hr := ChargeTrace.replace U _ j u hj hu (T j) (f (j,u)) (xs.map f).prod
      hT hf0 hp hrow hbound ht
    simpa only [List.map_cons,List.prod_cons,he] using hr

end MatchingFPRAS.Switching

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_SumLiftMate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Switching

section

open Finset

variable {V W : Type*}

lemma sumRetractMate_inl (q : Mate (V ⊕ W)) (hfix : ∀ w, q.val (Sum.inr w)=Sum.inr w) (a : V) :
    Sum.inl ((sumRetractMate q hfix).val a)=q.val (Sum.inl a) := by
  cases he : q.val (Sum.inl a) with
  | inl b => simp [sumRetractMate,he]
  | inr w =>
    have hh := q.property (Sum.inl a)
    rw [he,hfix] at hh
    contradiction

lemma sumLift_retract (q : Mate (V ⊕ W)) (hfix : ∀ w, q.val (Sum.inr w)=Sum.inr w) :
    sumLiftMate (sumRetractMate q hfix)=q := by
  apply Subtype.ext; funext a
  cases a with
  | inl a => exact sumRetractMate_inl q hfix a
  | inr w => exact (hfix w).symm

lemma sumLift_weight [Fintype V] [Fintype W] [LinearOrder V] [LinearOrder (V ⊕ W)]
    (hord : ∀ a b : V, ((Sum.inl a : V ⊕ W) < Sum.inl b) ↔ a < b)
    (B : V → V → ℝ) (B' : (V ⊕ W) → (V ⊕ W) → ℝ)
    (hB : ∀ a b, B' (Sum.inl a) (Sum.inl b)=B a b) (m : Mate V) :
    weight B' (sumLiftMate m)=weight B m := by
  simp [weight,Fintype.prod_sum_type,hord,hB]

theorem pairingCapacity_sum_inl [Fintype V] [Fintype W] [LinearOrder V] [LinearOrder (V ⊕ W)]
    (hord : ∀ a b : V, ((Sum.inl a : V ⊕ W) < Sum.inl b) ↔ a < b)
    (B : V → V → ℝ) (B' : (V ⊕ W) → (V ⊕ W) → ℝ)
    (hB : ∀ a b, B' (Sum.inl a) (Sum.inl b)=B a b)
    (R : Finset V) (hR : Even R.card)
    (hR' : Even (R.map ⟨Sum.inl,Sum.inl_injective (β := W)⟩).card) :
    pairingCapacity B' (R.map ⟨Sum.inl,Sum.inl_injective⟩) hR'=pairingCapacity B R hR := by
  classical
  apply le_antisymm
  · apply Finset.sup'_le
    intro q hq
    have hholes := (mem_matchings q _).mp hq
    have hfix : ∀ w, q.val (Sum.inr w)=Sum.inr w := by
      intro w
      exact (hholes (Sum.inr w)).mpr (by simp)
    let m := sumRetractMate q hfix
    have hqm : sumLiftMate m=q := sumLift_retract q hfix
    have hm : HasHoles m Rᶜ := by
      intro a
      have hh := hholes (Sum.inl a)
      rw [← hqm] at hh
      simpa using hh
    rw [← hqm,sumLift_weight hord B B' hB]
    exact weight_le_pairingCapacity B R hR m hm
  · apply Finset.sup'_le
    intro m hm
    have hholes := (mem_matchings m _).mp hm
    rw [← sumLift_weight hord B B' hB]
    apply weight_le_pairingCapacity B' _ hR' (sumLiftMate m)
    intro a
    cases a with
    | inl a => simpa using hholes a
    | inr a => simp

theorem ChargeTrace.capacity_bound_decidable [Fintype V] [LinearOrder V]
    (dec : DecidableEq V) {B : V → V → ℝ}
    (hB : ∀ a b, B a b = B b a) (hB0 : ∀ a b, 0 ≤ B a b)
    (htri : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → min (B a c) (B c b) ≤ B a b)
    {U W : Finset V} {F : ℝ} (h : @ChargeTrace V dec B U W F) (hU : Even U.card) :
    ∃ hW : Even W.card, pairingCapacity B U hU * F ≤ pairingCapacity B W hW := by
  have he : dec = (inferInstance : LinearOrder V).toDecidableEq := Subsingleton.elim _ _
  subst dec
  exact h.capacity_bound hB hB0 htri hU

end

variable {V : Type*}

lemma ChargeTrace.factor_nonneg [DecidableEq V] {B : V → V → ℝ}
    {U W : Finset V} {F : ℝ} (h : ChargeTrace B U W F) : 0 ≤ F := by
  cases h with
  | done => norm_num
  | remove _ _ _ _ _ _ _ _ _ _ _ _ _ hf hF => exact mul_nonneg hf hF
  | replace _ _ _ _ _ _ _ _ _ _ hf hF => exact mul_nonneg hf hF

end MatchingFPRAS.Switching

namespace MatchingFPRAS.Subdivision

open Finset

 theorem paired_prefix_weight (a : Bool) (xs ys : List ℝ) :
    wordWeight a (duplicate xs ++ ys) = xs.prod * wordWeight a ys := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, mul_assoc]

theorem profile_weight (a : Bool) (left right : List ℝ) (lam : ℝ) :
    wordWeight a (duplicate left ++ [lam] ++ duplicate right) =
      left.prod * right.prod * (if a then lam else 1) := by
  rw [List.append_assoc, paired_prefix_weight]
  simp only [List.singleton_append, wordWeight]
  have h := paired_prefix_weight (!a) right []
  simp only [List.append_nil, wordWeight_nil, mul_one] at h
  rw [h]
  ring

theorem wordWeight_ofFn (n : ℕ) (w : Fin n → ℝ) (a : Bool) :
    wordWeight a (List.ofFn w) = ∏ i, (if alternating a i.val then w i else 1) := by
  induction n generalizing a with
  | zero => simp [List.ofFn_zero]
  | succ n ih =>
    rw [List.ofFn_succ, Fin.prod_univ_succ]
    simp only [wordWeight, Fin.val_zero, alternating_zero]
    rw [ih]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    simp

 theorem intact_weight {m : ℕ} (w : Fin (m+1) → ℝ) (b : Selection m)
    (h : Valid ∅ b) : selectedWeight w b = wordWeight (b 0) (List.ofFn w) := by
  rw [wordWeight_ofFn]
  unfold selectedWeight
  apply Finset.prod_congr rfl
  intro i _
  rw [(intact_iff b).mp h]

end MatchingFPRAS.Subdivision

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Profile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Subdivision

open Finset

 theorem profileActivity_ofFn (p : ℕ) (B Hu Hv lam : ℝ) :
    List.ofFn (profileActivity p B Hu Hv lam) = profile p B Hu Hv lam := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_ofFn, profileActivity, List.get_eq_getElem, Fin.val_cast]

 theorem exact_profile_weight (p : ℕ) (B Hu Hv lam : ℝ) (a : Bool) :
    selectedWeight (profileActivity p B Hu Hv lam)
      (fun i => alternating a i.val) =
        ((∏ r : Fin p, max B (Hu / 2^r.val)) *
         (∏ r : Fin p, max B (Hv / 2^r.val))) * (if a then lam else 1) := by
  rw [intact_weight _ _ (alternating_valid _ _),profileActivity_ofFn]
  simpa [profile,List.prod_ofFn] using
    profile_weight a (List.ofFn fun r : Fin p => max B (Hu / 2^r.val))
      ((List.ofFn fun r : Fin p => max B (Hv / 2^r.val)).reverse) lam

section Deletion

variable {V E : Type*} [Fintype V] [Fintype E]

omit [Fintype V] [Fintype E] in
 theorem deletion_weight [Fintype V] [Fintype E] {m : ℕ} (u v : E → V) (R₀ : Finset V)
    (U : E → Finset (Fin m)) (base b : E → Selection m)
    (hb0 : FamilyHoles u v m R₀ U base) (hb : FamilyHoles u v m R₀ U b)
    (w : E → Fin (m+1) → ℝ) (left right : E → List ℝ) (lam : E → ℝ)
    (hw : ∀ e, List.ofFn (w e) = duplicate (left e) ++ [lam e] ++ duplicate (right e)) :
    (∏ e, selectedWeight (w e) (b e)) =
      deletionConstant U base w (fun e => (left e).prod * (right e).prod) *
        ∏ e, if extract U b e then lam e else 1 := by
  classical
  unfold deletionConstant
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e _
  by_cases he : (U e).Nonempty
  · have heq := broken_unique he (hb0.1 e) (hb.1 e)
    simp [extract,he,heq]
  · have he' : U e = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    simp only [extract,he,↓reduceIte]
    rw [intact_weight _ _ (by simpa [he'] using hb.1 e),hw e,profile_weight]

theorem deletion_partition_identity {m : ℕ} (hm : Even m) (u v : E → V) (R₀ : Finset V)
    (U : E → Finset (Fin m)) (base : E → Selection m)
    (hb : FamilyHoles u v m R₀ U base)
    (w : E → Fin (m+1) → ℝ) (left right : E → List ℝ) (lam : E → ℝ)
    (hw : ∀ e, List.ofFn (w e) = duplicate (left e) ++ [lam e] ++ duplicate (right e)) :
    realHolePartition u v m R₀ U w =
      deletionConstant U base w (fun e => (left e).prod * (right e).prod) *
        logicalHolePartition u v (residualHoles u v R₀ U base) (broken U) lam := by
  classical
  let := Fintype.ofFinite {b : E → Selection m // FamilyHoles u v m R₀ U b}
  let := Fintype.ofFinite {s : E → Bool //
    LogicalHoles u v (residualHoles u v R₀ U base) (broken U) s}
  unfold realHolePartition logicalHolePartition
  rw [Finset.mul_sum]
  apply Fintype.sum_equiv (deletionEquiv hm u v R₀ U base hb)
  intro b
  exact deletion_weight u v R₀ U base b.val hb b.property w left right lam hw

end Deletion

theorem selectedWeight_vertex_factor {m : ℕ} (U : Finset (Fin m))
    (b : Selection m) (hb : Valid U b) (z : Fin (m+2) → ℝ) :
    selectedWeight (fun i => z i.castSucc * z i.succ) b =
      (if b 0 then z 0 else 1) * (if b (Fin.last m) then z (Fin.last (m+1)) else 1) *
        ∏ i : Fin m, if i ∈ U then 1 else z i.succ.castSucc := by
  classical
  unfold selectedWeight
  have hsplit (i : Fin (m+1)) :
      (if b i then z i.castSucc * z i.succ else 1) =
      (if b i then z i.castSucc else 1) * (if b i then z i.succ else 1) := by
    cases b i <;> simp
  simp_rw [hsplit]
  rw [Finset.prod_mul_distrib,
    Fin.prod_univ_succ (fun i : Fin (m+1) => if b i then z i.castSucc else 1),
    Fin.prod_univ_castSucc (fun i : Fin (m+1) => if b i then z i.succ else 1)]
  have he : ∀ i : Fin m,
      (if b i.succ then z i.succ.castSucc else 1) *
        (if b i.castSucc then z i.castSucc.succ else 1) =
      if i ∈ U then 1 else z i.succ.castSucc := by
    intro i
    have hz : i.castSucc.succ = i.succ.castSucc := rfl
    rw [hz]
    have h := hb i
    by_cases hi : i ∈ U
    · simp only [hi,↓reduceIte] at h ⊢
      simp [h.1,h.2]
    · simp only [hi,↓reduceIte] at h ⊢
      cases h₁ : b i.castSucc <;> cases h₂ : b i.succ <;> simp_all
  calc
    _ = (if b 0 then z 0 else 1) * (if b (Fin.last m) then z (Fin.last (m+1)) else 1) *
        ∏ i : Fin m, ((if b i.succ then z i.succ.castSucc else 1) *
          (if b i.castSucc then z i.castSucc.succ else 1)) := by
      rw [Finset.prod_mul_distrib]
      simp only [Fin.castSucc_zero, Fin.succ_last]
      ring
    _ = _ := by simp_rw [he]

theorem valid_interval {m : ℕ} {U : Finset (Fin m)} {b : Selection m}
    (hb : Valid U b) (a k : ℕ) (hak : a+k ≤ m)
    (hfree : ∀ i : Fin m, a ≤ i.val → i.val < a+k → i ∉ U) :
    b ⟨a+k,by omega⟩ = alternating (b ⟨a,by omega⟩) k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hai : a+k < m := by omega
    have hf := hb ⟨a+k,hai⟩
    simp only [hfree ⟨a+k,hai⟩ (by dsimp; omega) (by dsimp; omega),↓reduceIte] at hf
    have he := (bool_ne_iff_eq_not _ _).mp hf
    have hi := ih (by omega) (fun i hi hj => hfree i hi (by omega))
    simpa only [Fin.succ_mk, Fin.castSucc_mk, Nat.add_assoc,
      alternating_succ, hi] using he

theorem first_hole_terminal {m : ℕ} {U : Finset (Fin m)} {b : Selection m}
    (hb : Valid U b) (j : Fin m) (hj : j ∈ U)
    (hfirst : ∀ i ∈ U, j ≤ i) :
    b 0 = true ↔ j.val % 2 = 1 := by
  have hv := valid_interval hb 0 j.val (by omega) (by
    intro i hi hij him
    have hh := hfirst i him
    have : j.val ≤ i.val := hh
    omega)
  have hz : b j.castSucc = false := by
    have h := hb j
    simp only [hj,↓reduceIte] at h
    exact h.1
  have he : b j.castSucc = alternating (b 0) j.val := by
    have ez : (⟨0,by omega⟩ : Fin (m+1)) = 0 := Fin.ext rfl
    have ee : (⟨0+j.val,by omega⟩ : Fin (m+1)) = j.castSucc := by
      apply Fin.ext; dsimp; omega
    rw [ee,ez] at hv
    exact hv
  rw [hz] at he
  by_cases h : j.val%2=0
  · simp only [alternating,h,↓reduceIte] at he
    simp [← he,h]
  · have h1 : j.val%2=1 := by omega
    simp only [alternating,h,↓reduceIte] at he
    cases hbool : b 0
    · rw [hbool] at he; contradiction
    · simp only [h1]

end MatchingFPRAS.Subdivision

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_HoleBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Subdivision
open Finset

theorem last_hole_terminal {m : ℕ} (hm : Even m) {U : Finset (Fin m)}
    {b : Selection m} (hb : Valid U b) (j : Fin m) (hj : j ∈ U)
    (hlast : ∀ i ∈ U, i ≤ j) :
    b (Fin.last m) = true ↔ j.val % 2 = 0 := by
  have hv := valid_interval hb (j.val+1) (m-(j.val+1)) (by omega) (by
    intro i hi hij him
    have hh := hlast i him
    have : i.val ≤ j.val := hh
    omega)
  have hz : b j.succ = false := by
    have h := hb j
    simp only [hj,↓reduceIte] at h
    exact h.2
  have he : b (Fin.last m) = alternating false (m-(j.val+1)) := by
    have e1 : (⟨j.val+1+(m-(j.val+1)),by omega⟩ : Fin (m+1)) = Fin.last m := by
      apply Fin.ext; dsimp; omega
    have e2 : (⟨j.val+1,by omega⟩ : Fin (m+1)) = j.succ := rfl
    rw [e1,e2,hz] at hv
    exact hv
  have hme := Nat.even_iff.mp hm
  by_cases h : j.val%2=0
  · have hk : (m-(j.val+1))%2=1 := by omega
    simp [he,alternating,h,hk]
  · have hk : (m-(j.val+1))%2=0 := by omega
    simp [he,alternating,h,hk]

theorem successive_holes_parity {m : ℕ} {U : Finset (Fin m)} {b : Selection m}
    (hb : Valid U b) (i j : Fin m) (hi : i ∈ U) (hj : j ∈ U) (hij : i < j)
    (hbetween : ∀ k ∈ U, ¬ (i < k ∧ k < j)) :
    i.val % 2 ≠ j.val % 2 := by
  have hv := valid_interval hb (i.val+1) (j.val-(i.val+1)) (by omega) (by
    intro k hk hkj hku
    apply hbetween k hku
    constructor <;> omega)
  have hi0 : b i.succ = false := by
    have h := hb i
    simp only [hi,↓reduceIte] at h
    exact h.2
  have hj0 : b j.castSucc = false := by
    have h := hb j
    simp only [hj,↓reduceIte] at h
    exact h.1
  have he : false = alternating false (j.val-(i.val+1)) := by
    convert hv using 1
    · rw [show (⟨i.val+1+(j.val-(i.val+1)),by omega⟩ : Fin (m+1)) = j.castSucc
        by apply Fin.ext; dsimp; omega,hj0]
    · rw [show (⟨i.val+1,by omega⟩ : Fin (m+1)) = i.succ by rfl,hi0]
  have heven : (j.val-(i.val+1))%2=0 := by
    by_contra h
    simp [alternating,h] at he
  omega

theorem sorted_holes_alternate {m : ℕ} {U : Finset (Fin m)} {b : Selection m}
    (hb : Valid U b) :
    (U.sort (· ≤ ·)).IsChain (fun i j => i.val%2 ≠ j.val%2) := by
  let xs := U.sort (· ≤ ·)
  have hsort : xs.Pairwise (· < ·) := (Finset.sortedLT_sort U).pairwise
  rw [List.isChain_iff_getElem]
  intro r hr
  have hri : r < xs.length := by exact Nat.lt_trans (Nat.lt_succ_self r) hr
  have him : xs[r] ∈ U := (Finset.mem_sort _).mp (List.getElem_mem hri)
  have hjm : xs[r+1] ∈ U := (Finset.mem_sort _).mp (List.getElem_mem hr)
  have hij : xs[r] < xs[r+1] :=
    (List.pairwise_iff_getElem.mp hsort) r (r+1) hri hr (by omega)
  apply successive_holes_parity hb (xs[r]) (xs[r+1]) him hjm hij
  intro k hk hbet
  have hkm : k ∈ xs := (Finset.mem_sort _).mpr hk
  obtain ⟨s,hs,hks⟩ := List.mem_iff_getElem.mp hkm
  by_cases hsr : s ≤ r
  · by_cases heq : s=r
    · subst s; rw [hks] at hbet; exact lt_irrefl _ hbet.1
    · have hlt := (List.pairwise_iff_getElem.mp hsort) s r hs hri (by omega)
      rw [hks] at hlt
      exact (not_lt_of_ge hlt.le) hbet.1
  · by_cases heq : s=r+1
    · subst s; rw [hks] at hbet; exact lt_irrefl _ hbet.2
    · have hlt := (List.pairwise_iff_getElem.mp hsort) (r+1) s hr hs (by omega)
      rw [hks] at hlt
      exact (not_lt_of_ge hlt.le) hbet.2

theorem neutral_blocks {m : ℕ} (xs : List (Fin m))
    (ha : xs.IsChain (fun i j => i.val%2 ≠ j.val%2))
    (hh : ∀ i ∈ xs.head?, i.val%2=0) :
    ∃ (pairs : List (Fin m × Fin m)) (right : Option (Fin m)),
      xs = pairs.flatMap (fun q => [q.1,q.2]) ++ right.toList ∧
      (∀ q ∈ pairs, q.1.val%2=0 ∧ q.2.val%2=1) ∧
      (∀ j ∈ right, j.val%2=0) := by
  induction xs using List.twoStepInduction with
  | nil => exact ⟨[],none,by simp⟩
  | singleton j => exact ⟨[],some j,by simpa using hh⟩
  | cons_cons j k xs ih ih' =>
    have hj : j.val%2=0 := hh j (by simp)
    have hne := (List.isChain_cons_cons.mp ha).1
    have hk : k.val%2=1 := by omega
    have htail := (List.isChain_cons_cons.mp ha).2
    have hh' : ∀ i ∈ xs.head?, i.val%2=0 := by
      intro i hi
      have hki : k.val%2 ≠ i.val%2 := (List.isChain_cons.mp htail).1 i hi
      omega
    obtain ⟨pairs,right,he,hp,hr⟩ := ih htail.tail hh'
    refine ⟨(j,k)::pairs,right,?_,?_,hr⟩
    · simp [he]
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨hj,hk⟩
      · exact hp q hq

theorem hole_blocks_exist {m : ℕ} {U : Finset (Fin m)} {b : Selection m}
    (hb : Valid U b) :
    ∃ d : HoleBlocks m, d.flatten = U.sort (· ≤ ·) ∧ d.Parity := by
  have ha := sorted_holes_alternate hb
  generalize he : U.sort (· ≤ ·)=xs at ha ⊢
  cases xs with
  | nil => exact ⟨⟨none,[],none⟩,rfl,by simp [HoleBlocks.Parity]⟩
  | cons j xs =>
    by_cases hj : j.val%2=0
    · obtain ⟨pairs,right,heq,hp,hr⟩ := neutral_blocks (j::xs) ha (by simpa using hj)
      exact ⟨⟨none,pairs,right⟩,by simpa [HoleBlocks.flatten] using heq.symm,
        by simpa [HoleBlocks.Parity] using And.intro hp hr⟩
    · have hj1 : j.val%2=1 := by omega
      have hh : ∀ i ∈ xs.head?, i.val%2=0 := by
        intro i hi
        have hji := (List.isChain_cons.mp ha).1 i hi
        omega
      obtain ⟨pairs,right,heq,hp,hr⟩ := neutral_blocks xs ha.tail hh
      refine ⟨⟨some j,pairs,right⟩,?_,?_⟩
      · simp [HoleBlocks.flatten,heq]
      · simpa [HoleBlocks.Parity] using And.intro hj1 (And.intro hp hr)

theorem selectedWeight_hole_product {m : ℕ} (hm : Even m)
    (U : Finset (Fin m)) (b : Selection m) (hb : Valid U b) (z : Fin (m+2) → ℝ) :
    selectedWeight (fun i => z i.castSucc * z i.succ) b *
        (∏ j ∈ U, z j.succ.castSucc) =
      selectedWeight (fun i => z i.castSucc * z i.succ)
        (fun i => alternating false i.val) *
      (if b 0 then z 0 else 1) * (if b (Fin.last m) then z (Fin.last (m+1)) else 1) := by
  classical
  rw [selectedWeight_vertex_factor U b hb z,
    selectedWeight_vertex_factor ∅ _ (alternating_valid m false) z]
  have hbool : alternating false (Fin.last m).val = false := by
    simp [alternating,Nat.even_iff.mp hm]
  simp only [Fin.val_zero,alternating_zero,Bool.false_eq_true,↓reduceIte,
    hbool,Finset.notMem_empty,one_mul]
  have hp : (∏ i : Fin m, if i ∈ U then 1 else z i.succ.castSucc) *
      (∏ j ∈ U, z j.succ.castSucc) = ∏ i : Fin m, z i.succ.castSucc := by
    have hU : (∏ j ∈ U, z j.succ.castSucc) =
        ∏ i : Fin m, if i ∈ U then z i.succ.castSucc else 1 := by
      rw [← Finset.prod_filter]
      simp
    rw [hU,← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    by_cases him : i ∈ U <;> simp [him]
  calc
    _ = (if b 0 then z 0 else 1) * (if b (Fin.last m) then z (Fin.last (m+1)) else 1) *
      ((∏ i : Fin m, if i ∈ U then 1 else z i.succ.castSucc) *
        (∏ j ∈ U, z j.succ.castSucc)) := by ring
    _ = _ := by rw [hp]; ring

theorem profile_vertexPotential (p : ℕ) (B Hu Hv lam : ℝ) (hlam : lam ≠ 0)
    (i : Fin (4*p+1)) : profileActivity p B Hu Hv lam i =
      vertexPotential p B Hu Hv lam i.val * vertexPotential p B Hu Hv lam (i.val+1) := by
  have hi := i.isLt
  rcases lt_trichotomy i.val (2*p) with hleft | hcenter | hright
  · rw [profile_left _ _ _ _ _ _ hleft]
    have hi0 : i.val ≤ 2*p := by omega
    have hi1 : i.val+1 ≤ 2*p := by omega
    simp only [vertexPotential,ite_eq_left hi0,ite_eq_left hi1]
    by_cases he : Even i.val
    · have hn : ¬ Even (i.val+1) := by simpa [Nat.even_add_one] using he
      have hdiv : (i.val+1)/2=i.val/2 := by have := Nat.even_iff.mp he; omega
      simp [he,hn,hdiv]
    · have hn : Even (i.val+1) := by simpa [Nat.even_add_one] using he
      simp [he,hn]
  · have hic : i=⟨2*p,by omega⟩ := Fin.ext hcenter
    rw [hic]
    simp [vertexPotential,show ¬ 2*p+1 ≤ 2*p by omega]
  · rw [profile_right _ _ _ _ _ _ hright]
    have hi0 : ¬ i.val ≤ 2*p := by omega
    have hi1 : ¬ i.val+1 ≤ 2*p := by omega
    simp only [vertexPotential,ite_eq_right hi0,ite_eq_right hi1]
    by_cases he : Even i.val
    · have hn : ¬ Even (i.val+1) := by simpa [Nat.even_add_one] using he
      have hdiv : (4*p+1-i.val)/2=(4*p-i.val)/2 := by have := Nat.even_iff.mp he; omega
      simp [he,hn,hdiv,hlam]
    · have hn : Even (i.val+1) := by simpa [Nat.even_add_one] using he
      have hdiv : 4*p+1-(i.val+1)=4*p-i.val := by omega
      simp [he,hn,hdiv,hlam,mul_div_cancel₀]

lemma vertexPotential_pos (p : ℕ) (B Hu Hv lam : ℝ) (hB : 0 < B) (hlam : 0 < lam)
    (i : ℕ) : 0 < vertexPotential p B Hu Hv lam i := by
  unfold vertexPotential
  split_ifs
  · norm_num
  · exact hB.trans_le (le_max_left _ _)
  · exact div_pos (hB.trans_le (le_max_left _ _)) hlam
  · exact hlam

lemma consumed_left_potential (p : ℕ) (B Hu Hv lam : ℝ) (j : Fin (4*p))
    (hj : j.val%2=1) :
    vertexPotential p B Hu Hv lam (j.val+1) =
      if j.val < 2*p then 1 else internalStrength p B Hu Hv j/lam := by
  have he : Even (j.val+1) := Nat.even_iff.mpr (by omega)
  have hi : j.val+1 ≤ 2*p ↔ j.val < 2*p := by omega
  simp only [vertexPotential,he,↓reduceIte,hi]
  by_cases hs : j.val < 2*p
  · simp [hs]
  · have hd : (4*p-j.val)/2=(4*p-(j.val+1))/2 := by
      have := j.isLt; omega
    simp [hs,internalStrength,hd]

lemma consumed_right_potential (p : ℕ) (B Hu Hv lam : ℝ) (j : Fin (4*p))
    (hj : j.val%2=0) :
    vertexPotential p B Hu Hv lam (j.val+1) =
      if j.val < 2*p then internalStrength p B Hu Hv j else lam := by
  have he : ¬ Even (j.val+1) := by rw [Nat.even_iff]; omega
  have hi : j.val+1 ≤ 2*p ↔ j.val < 2*p := by omega
  have hd : (j.val+1)/2=j.val/2 := by omega
  simp only [vertexPotential,he,↓reduceIte,hi,hd]
  by_cases hs : j.val < 2*p
  · simp [hs,internalStrength]
  · simp [hs]

end MatchingFPRAS.Subdivision

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_FirstHoleSortedCons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Subdivision

section

open Finset

lemma first_hole_of_sorted_cons {m : ℕ} {U : Finset (Fin m)} {b : Selection m}
    (hb : Valid U b) (j : Fin m) (xs : List (Fin m)) (he : U.sort (· ≤ ·)=j::xs) :
    b 0=true ↔ j.val%2=1 := by
  apply first_hole_terminal hb j
  · exact (Finset.mem_sort (· ≤ ·)).mp (he ▸ List.mem_cons_self)
  · intro i hi
    have hmem : i ∈ j::xs := he ▸ (Finset.mem_sort (· ≤ ·)).mpr hi
    have hsort := U.pairwise_sort (· ≤ ·)
    rw [he] at hsort
    rcases List.mem_cons.mp hmem with rfl | hmem
    · rfl
    · exact (List.pairwise_cons.mp hsort).1 i hmem

lemma last_hole_of_sorted_append {m : ℕ} (hm : Even m) {U : Finset (Fin m)} {b : Selection m}
    (hb : Valid U b) (j : Fin m) (xs : List (Fin m)) (he : U.sort (· ≤ ·)=xs++[j]) :
    b (Fin.last m)=true ↔ j.val%2=0 := by
  apply last_hole_terminal hm hb j
  · exact (Finset.mem_sort (· ≤ ·)).mp (he ▸ (by simp))
  · intro i hi
    have hmem : i ∈ xs++[j] := he ▸ (Finset.mem_sort (· ≤ ·)).mpr hi
    have hsort := U.pairwise_sort (· ≤ ·)
    rw [he] at hsort
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact (List.pairwise_append.mp hsort).2.2 i hmem j (by simp)
    · have hij : i=j := by simpa using hmem
      exact hij.le

theorem HoleBlocks.left_uses {m : ℕ} {U : Finset (Fin m)} {b : Selection m}
    (hb : Valid U b) (hU : U.Nonempty) (d : HoleBlocks m)
    (he : d.flatten=U.sort (· ≤ ·)) (hp : d.Parity) :
    b 0=true ↔ d.left.isSome := by
  cases hl : d.left with
  | some j =>
    have hs : U.sort (· ≤ ·)=j::(d.neutral.flatMap (fun q => [q.1,q.2])++d.right.toList) := by
      simpa [HoleBlocks.flatten,hl,List.append_assoc] using he.symm
    have hj := hp.1 j (by simp [hl])
    simpa [hl,hj] using first_hole_of_sorted_cons hb j _ hs
  | none =>
    cases hn : d.neutral with
    | cons q xs =>
      have hs : U.sort (· ≤ ·)=q.1::(q.2::(xs.flatMap (fun q => [q.1,q.2])++d.right.toList)) := by
        simpa [HoleBlocks.flatten,hl,hn,List.append_assoc] using he.symm
      have hj := (hp.2.1 q (by simp [hn])).1
      simpa [hl,hj] using first_hole_of_sorted_cons hb q.1 _ hs
    | nil =>
      cases hr : d.right with
      | some j =>
        have hs : U.sort (· ≤ ·)=[j] := by simpa [HoleBlocks.flatten,hl,hn,hr] using he.symm
        have hj := hp.2.2 j (by simp [hr])
        simpa [hl,hj] using first_hole_of_sorted_cons hb j [] hs
      | none =>
        have hs : U.sort (· ≤ ·)=[] := by simpa [HoleBlocks.flatten,hl,hn,hr] using he.symm
        obtain ⟨j,hj⟩ := hU
        have : j ∈ U.sort (· ≤ ·) := (Finset.mem_sort (· ≤ ·)).mpr hj
        simp [hs] at this

theorem HoleBlocks.right_uses {m : ℕ} (hm : Even m) {U : Finset (Fin m)} {b : Selection m}
    (hb : Valid U b) (hU : U.Nonempty) (d : HoleBlocks m)
    (he : d.flatten=U.sort (· ≤ ·)) (hp : d.Parity) :
    b (Fin.last m)=true ↔ d.right.isSome := by
  cases hr : d.right with
  | some j =>
    have hs : U.sort (· ≤ ·)=(d.left.toList++d.neutral.flatMap (fun q => [q.1,q.2]))++[j] := by
      simpa [HoleBlocks.flatten,hr] using he.symm
    have hj := hp.2.2 j (by simp [hr])
    simpa [hr,hj] using last_hole_of_sorted_append hm hb j _ hs
  | none =>
    generalize hn : d.neutral=xs at hp he
    cases xs using List.reverseRecOn with
    | nil =>
      cases hl : d.left with
      | some j =>
        have hs : U.sort (· ≤ ·)=[]++[j] := by simpa [HoleBlocks.flatten,hl,hn,hr] using he.symm
        have hj := hp.1 j (by simp [hl])
        simpa [hr,hj] using last_hole_of_sorted_append hm hb j [] hs
      | none =>
        have hs : U.sort (· ≤ ·)=[] := by simpa [HoleBlocks.flatten,hl,hn,hr] using he.symm
        obtain ⟨j,hj⟩ := hU
        have : j ∈ U.sort (· ≤ ·) := (Finset.mem_sort (· ≤ ·)).mpr hj
        simp [hs] at this
    | append_singleton xs q =>
      have hs : U.sort (· ≤ ·)=(d.left.toList++xs.flatMap (fun q => [q.1,q.2])++[q.1])++[q.2] := by
        simpa [HoleBlocks.flatten,hr,hn,List.flatMap_append,List.append_assoc] using he.symm
      have hj := (hp.2.1 q (by simp [hn])).2
      simpa [hr,hj] using last_hole_of_sorted_append hm hb q.2 _ hs

theorem HoleBlocks.neutral_lt {m : ℕ} {U : Finset (Fin m)} (d : HoleBlocks m)
    (he : d.flatten=U.sort (· ≤ ·)) (q : Fin m × Fin m) (hq : q ∈ d.neutral) :
    q.1.val < q.2.val := by
  have hp : d.flatten.Pairwise (· < ·) := he ▸ U.sortedLT_sort.pairwise
  have hn : (d.neutral.flatMap (fun q => [q.1,q.2])).Pairwise (· < ·) :=
    (List.pairwise_append.mp (List.pairwise_append.mp hp).1).2.1
  have hq' := (List.pairwise_flatMap.mp hn).1 q hq
  simpa using hq'

lemma HoleBlocks.flatten_nodup {m : ℕ} {U : Finset (Fin m)} (d : HoleBlocks m)
    (he : d.flatten=U.sort (· ≤ ·)) : d.flatten.Nodup := he ▸ U.sort_nodup (· ≤ ·)

lemma HoleBlocks.left_mem {m : ℕ} {U : Finset (Fin m)} (d : HoleBlocks m)
    (he : d.flatten=U.sort (· ≤ ·)) {j : Fin m} (hj : j ∈ d.left) : j ∈ U := by
  apply (Finset.mem_sort (· ≤ ·)).mp
  rw [← he]
  simp only [HoleBlocks.flatten,List.mem_append,Option.mem_toList]
  exact Or.inl (Or.inl hj)

lemma HoleBlocks.right_mem {m : ℕ} {U : Finset (Fin m)} (d : HoleBlocks m)
    (he : d.flatten=U.sort (· ≤ ·)) {j : Fin m} (hj : j ∈ d.right) : j ∈ U := by
  apply (Finset.mem_sort (· ≤ ·)).mp
  rw [← he]
  simp only [HoleBlocks.flatten,List.mem_append,Option.mem_toList]
  exact Or.inr hj

lemma HoleBlocks.reorder {m : ℕ} (d : HoleBlocks m) :
    d.flatten.Perm (d.neutral.flatMap (fun q => [q.1,q.2]) ++ (d.left.toList++d.right.toList)) := by
  unfold HoleBlocks.flatten
  exact (List.perm_append_comm.append_right _).trans (by rw [List.append_assoc])

lemma HoleBlocks.reordered_nodup {m : ℕ} {U : Finset (Fin m)} (d : HoleBlocks m)
    (he : d.flatten=U.sort (· ≤ ·)) :
    (d.neutral.flatMap (fun q => [q.1,q.2]) ++ (d.left.toList++d.right.toList)).Nodup :=
  d.reorder.nodup_iff.mp (d.flatten_nodup he)

end

variable {V E : Type*} [Fintype V] [Fintype E]

omit [Fintype V] [Fintype E] in
lemma uses_not_hole [Fintype V] [Fintype E]
    {m : ℕ} {u v : E → V} {R₀ : Finset V} {U : E → Finset (Fin m)}
    {b : E → Selection m} (hb : FamilyHoles u v m R₀ U b) {e : E} {x : V}
    (he : Uses u v b e x) : x ∉ R₀ := fun hx => hb.2.1 x hx e he

lemma uses_unique {m : ℕ} {u v : E → V} {R₀ : Finset V} {U : E → Finset (Fin m)}
    {b : E → Selection m} (hb : FamilyHoles u v m R₀ U b) {e e' : E} {x : V}
    (he : Uses u v b e x) (he' : Uses u v b e' x) : e=e' :=
  (hb.2.2 x (uses_not_hole hb he)).unique he he'

omit [Fintype V] [Fintype E] in
lemma left_consumes [Fintype V] [Fintype E]
    {m : ℕ} {u v : E → V} {R₀ : Finset V} {U : E → Finset (Fin m)}
    {b : E → Selection m} (hb : FamilyHoles u v m R₀ U b)
    (d : E → HoleBlocks m) (he : ∀ e, (d e).flatten=(U e).sort (· ≤ ·))
    (hp : ∀ e, (d e).Parity) (e : E) {j : Fin m} (hj : j ∈ (d e).left) :
    Uses u v b e (u e) := by
  have hU : (U e).Nonempty := ⟨j,(d e).left_mem (he e) hj⟩
  have hs : (d e).left.isSome := by cases h : (d e).left <;> simp [h] at hj ⊢
  exact Or.inl ⟨((d e).left_uses (hb.1 e) hU (he e) (hp e)).mpr hs,rfl⟩

omit [Fintype V] [Fintype E] in
lemma right_consumes [Fintype V] [Fintype E]
    {m : ℕ} (hm : Even m) {u v : E → V} {R₀ : Finset V} {U : E → Finset (Fin m)}
    {b : E → Selection m} (hb : FamilyHoles u v m R₀ U b)
    (d : E → HoleBlocks m) (he : ∀ e, (d e).flatten=(U e).sort (· ≤ ·))
    (hp : ∀ e, (d e).Parity) (e : E) {j : Fin m} (hj : j ∈ (d e).right) :
    Uses u v b e (v e) := by
  have hU : (U e).Nonempty := ⟨j,(d e).right_mem (he e) hj⟩
  have hs : (d e).right.isSome := by cases h : (d e).right <;> simp [h] at hj ⊢
  exact Or.inr ⟨((d e).right_uses hm (hb.1 e) hU (he e) (hp e)).mpr hs,rfl⟩

end MatchingFPRAS.Subdivision

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_PathActivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Enlargement

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open Finset

variable {V E : Type*} [Fintype V] [LinearOrder V] [Fintype E] [LinearOrder E]

lemma leftFactor_eq_potential (p : ℕ) (B Hu Hv lam : ℝ) (j : Fin (4*p))
    (hj : j.val%2=1) :
    leftFactor p B Hu Hv lam j = (vertexPotential p B Hu Hv lam (j.val+1))⁻¹ := by
  rw [consumed_left_potential p B Hu Hv lam j hj]
  unfold leftFactor
  split_ifs <;> simp

lemma rightFactor_eq_potential (p : ℕ) (B Hu Hv lam : ℝ) (hlam : lam ≠ 0)
    (j : Fin (4*p)) (hj : j.val%2=0) :
    rightFactor p B Hu Hv lam j = lam / vertexPotential p B Hu Hv lam (j.val+1) := by
  rw [consumed_right_potential p B Hu Hv lam j hj]
  unfold rightFactor
  split_ifs <;> simp [hlam]

lemma neutralFactor_eq_potential (p : ℕ) (B Hu Hv lam : ℝ) (hlam : lam ≠ 0)
    (j k : Fin (4*p)) (hjk : j.val < k.val) (hj : j.val%2=0) (hk : k.val%2=1) :
    neutralFactor p B Hu Hv lam j k =
      (vertexPotential p B Hu Hv lam (j.val+1) * vertexPotential p B Hu Hv lam (k.val+1))⁻¹ := by
  rw [consumed_right_potential p B Hu Hv lam j hj,consumed_left_potential p B Hu Hv lam k hk]
  unfold neutralFactor
  by_cases hk' : k.val < 2*p
  · have hj' : j.val < 2*p := by omega
    simp [hk',hj']
  · by_cases hj' : j.val < 2*p
    · simp [hk',hj',div_eq_mul_inv,mul_inv_rev,inv_inv]
      ring
    · simp only [ite_eq_right hk',ite_eq_right hj']
      have he : lam * (internalStrength p B Hu Hv k / lam) = internalStrength p B Hu Hv k := by
        field_simp [hlam]
      rw [he]

lemma leftFactor_nonneg (p : ℕ) (B Hu Hv lam : ℝ) (hB : 0 < B) (hlam : 0 ≤ lam)
    (j : Fin (4*p)) : 0 ≤ leftFactor p B Hu Hv lam j := by
  unfold leftFactor
  split_ifs
  · norm_num
  · exact div_nonneg hlam ((hB.trans_le (le_internalStrength _ _ _ _ _)).le)

lemma rightFactor_nonneg (p : ℕ) (B Hu Hv lam : ℝ) (hB : 0 < B) (hlam : 0 ≤ lam)
    (j : Fin (4*p)) : 0 ≤ rightFactor p B Hu Hv lam j := by
  unfold rightFactor
  split_ifs
  · exact div_nonneg hlam ((hB.trans_le (le_internalStrength _ _ _ _ _)).le)
  · norm_num

lemma neutralFactor_nonneg (p : ℕ) (B Hu Hv lam : ℝ) (hB : 0 < B) (hlam : 0 ≤ lam)
    (j k : Fin (4*p)) : 0 ≤ neutralFactor p B Hu Hv lam j k := by
  have hj := (hB.trans_le (le_internalStrength p B Hu Hv j)).le
  have hk := (hB.trans_le (le_internalStrength p B Hu Hv k)).le
  unfold neutralFactor
  split_ifs
  · exact inv_nonneg.mpr hj
  · exact div_nonneg hlam (mul_nonneg hj hk)
  · exact inv_nonneg.mpr hk

theorem neutral_local_charge (u v : E → V) (huv : ∀ e, u e ≠ v e)
    (p : ℕ) (hp : 1 ≤ p) (B Hu Hv lam : E → ℝ) (hB : ∀ e, 0 < B e)
    (hHu : ∀ e, 0 ≤ Hu e) (hHv : ∀ e, 0 ≤ Hv e) (hlam : ∀ e, lam e ≤ B e)
    (e : E) (j k : Fin (4*p)) (hjk : j.val < k.val) :
    neutralFactor p (B e) (Hu e) (Hv e) (lam e) j k *
      internalStrength p (B e) (Hu e) (Hv e) j * internalStrength p (B e) (Hu e) (Hv e) k ≤
      realBottleneck u v p B Hu Hv lam (Sum.inr (e,j)) (Sum.inr (e,k)) := by
  have hj0 := hB e |>.trans_le (le_internalStrength p (B e) (Hu e) (Hv e) j)
  have hk0 := hB e |>.trans_le (le_internalStrength p (B e) (Hu e) (Hv e) k)
  unfold neutralFactor
  by_cases hk : k.val < 2*p
  · rw [ite_eq_left hk,inv_mul_cancel₀ hj0.ne',one_mul]
    have h := interval_le_bottleneck u v (4*p) (by omega) huv
      (pathActivity p B Hu Hv lam) e j.succ.castSucc k.succ.castSucc
      (by simpa only [Fin.val_castSucc,Fin.val_succ,Nat.add_lt_add_iff_right] using hjk) _
      (fun i _ hi => internalStrength_left_leg p (B e) (Hu e) (Hv e) (lam e)
        (hHu e) k hk i (by simp only [Fin.val_castSucc,Fin.val_succ] at hi; omega))
    simpa only [atVertex_zero,atVertex_internal,atVertex_last,realBottleneck] using h
  · rw [ite_eq_right hk]
    by_cases hj : j.val < 2*p
    · rw [ite_eq_left hj]
      have heq : lam e / (internalStrength p (B e) (Hu e) (Hv e) j *
          internalStrength p (B e) (Hu e) (Hv e) k) *
          internalStrength p (B e) (Hu e) (Hv e) j * internalStrength p (B e) (Hu e) (Hv e) k=lam e := by
        field_simp [hj0.ne',hk0.ne']
      rw [heq]
      have h := interval_le_bottleneck u v (4*p) (by omega) huv
        (pathActivity p B Hu Hv lam) e j.succ.castSucc k.succ.castSucc
        (by simpa only [Fin.val_castSucc,Fin.val_succ,Nat.add_lt_add_iff_right] using hjk) _
        (fun i _ _ => profile_lower p (B e) (Hu e) (Hv e) (lam e) (hlam e) i)
      simpa only [atVertex_zero,atVertex_internal,atVertex_last,realBottleneck] using h
    · rw [ite_eq_right hj]
      have heq : (internalStrength p (B e) (Hu e) (Hv e) k)⁻¹ *
          internalStrength p (B e) (Hu e) (Hv e) j * internalStrength p (B e) (Hu e) (Hv e) k=
          internalStrength p (B e) (Hu e) (Hv e) j := by field_simp [hk0.ne']
      rw [heq]
      have h := interval_le_bottleneck u v (4*p) (by omega) huv
        (pathActivity p B Hu Hv lam) e j.succ.castSucc k.succ.castSucc
        (by simpa only [Fin.val_castSucc,Fin.val_succ,Nat.add_lt_add_iff_right] using hjk) _
        (fun i hi _ => internalStrength_right_leg p (B e) (Hu e) (Hv e) (lam e)
          (hHv e) j hj i (by simpa only [Fin.val_castSucc,Fin.val_succ] using hi))
      simpa only [atVertex_zero,atVertex_internal,atVertex_last,realBottleneck] using h

theorem left_local_charge (u v : E → V) (huv : ∀ e, u e ≠ v e)
    (p : ℕ) (hp : 1 ≤ p) (B Hu Hv lam : E → ℝ) (hB : ∀ e, 0 < B e)
    (hHu : ∀ e, 0 ≤ Hu e) (hlam : ∀ e, lam e ≤ B e) (e : E) (j : Fin (4*p)) :
    leftFactor p (B e) (Hu e) (Hv e) (lam e) j * internalStrength p (B e) (Hu e) (Hv e) j ≤
      realBottleneck u v p B Hu Hv lam (Sum.inr (e,j)) (Sum.inl (u e)) := by
  have hj0 := hB e |>.trans_le (le_internalStrength p (B e) (Hu e) (Hv e) j)
  unfold leftFactor
  by_cases hj : j.val < 2*p
  · rw [ite_eq_left hj,one_mul]
    exact realBottleneck_left_home u v huv p hp B Hu Hv lam hHu e j hj
  · rw [ite_eq_right hj,div_mul_cancel₀ _ hj0.ne']
    rw [realBottleneck,bottleneck_comm]
    have h := interval_le_bottleneck u v (4*p) (by omega) huv
      (pathActivity p B Hu Hv lam) e 0 j.succ.castSucc (by simp) _
      (fun i _ _ => profile_lower p (B e) (Hu e) (Hv e) (lam e) (hlam e) i)
    simpa only [atVertex_zero,atVertex_internal] using h

theorem right_local_charge (u v : E → V) (huv : ∀ e, u e ≠ v e)
    (p : ℕ) (hp : 1 ≤ p) (B Hu Hv lam : E → ℝ) (hB : ∀ e, 0 < B e)
    (hHv : ∀ e, 0 ≤ Hv e) (hlam : ∀ e, lam e ≤ B e) (e : E) (j : Fin (4*p)) :
    rightFactor p (B e) (Hu e) (Hv e) (lam e) j * internalStrength p (B e) (Hu e) (Hv e) j ≤
      realBottleneck u v p B Hu Hv lam (Sum.inr (e,j)) (Sum.inl (v e)) := by
  have hj0 := hB e |>.trans_le (le_internalStrength p (B e) (Hu e) (Hv e) j)
  unfold rightFactor
  by_cases hj : j.val < 2*p
  · rw [ite_eq_left hj,div_mul_cancel₀ _ hj0.ne']
    have h := interval_le_bottleneck u v (4*p) (by omega) huv
      (pathActivity p B Hu Hv lam) e j.succ.castSucc (Fin.last (4*p+1))
      (by simp only [Fin.val_castSucc,Fin.val_succ,Fin.val_last]; omega) _
      (fun i _ _ => profile_lower p (B e) (Hu e) (Hv e) (lam e) (hlam e) i)
    simpa only [atVertex_internal,atVertex_last,realBottleneck] using h
  · rw [ite_eq_right hj,one_mul]
    exact realBottleneck_right_home u v huv p hp B Hu Hv lam hHv e j hj

omit [Fintype V] [LinearOrder V] [LinearOrder E] in
lemma tagged_nodup [Fintype V] [LinearOrder V] [LinearOrder E]
    {m : ℕ} (xs : E → List (Fin m)) (hx : ∀ e, (xs e).Nodup) :
    (Finset.univ.toList.flatMap (fun e => (xs e).map (fun j => (Sum.inr (e,j) : Vertex V E m)))).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨fun e _ => (hx e).map (fun _ _ h => congrArg Prod.snd (Sum.inr_injective h)),?_⟩
  apply (Finset.nodup_toList _).imp
  intro e e' hne
  apply List.disjoint_left.mpr
  intro a ha ha'
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ha
  obtain ⟨j',hj',he⟩ := List.mem_map.mp ha'
  exact hne (congrArg Prod.fst (Sum.inr_injective he)).symm

omit [Fintype V] [LinearOrder V] [LinearOrder E] in
lemma pairVertices_neutral [Fintype V] [LinearOrder V] [LinearOrder E]
    (m : ℕ) (d : E → HoleBlocks m) :
    pairVertices (neutralPairs (V := V) m d)=
      Finset.univ.toList.flatMap (fun e =>
        ((d e).neutral.flatMap (fun q => [q.1,q.2])).map (fun j => Sum.inr (e,j))) := by
  simp [pairVertices,neutralPairs,List.flatMap_assoc,List.flatMap_map,List.map_flatMap]

omit [Fintype V] [LinearOrder V] [LinearOrder E] in
lemma consumed_sources [Fintype V] [LinearOrder V] [LinearOrder E]
    (u v : E → V) (m : ℕ) (d : E → HoleBlocks m) :
    (consumedPairs u v m d).map Prod.fst=
      Finset.univ.toList.flatMap (fun e =>
        ((d e).left.toList++(d e).right.toList).map (fun j => Sum.inr (e,j))) := by
  simp [consumedPairs,List.map_flatMap,List.map_append,List.map_map,Function.comp_def]

theorem source_lists_nodup {m : ℕ} (u v : E → V) (U : E → Finset (Fin m))
    (d : E → HoleBlocks m) (he : ∀ e, (d e).flatten=(U e).sort (· ≤ ·)) :
    (pairVertices (neutralPairs (V := V) m d) ++ (consumedPairs u v m d).map Prod.fst).Nodup := by
  rw [pairVertices_neutral,consumed_sources]
  apply List.nodup_append.mpr
  refine ⟨tagged_nodup _ (fun e => (List.nodup_append.mp ((d e).reordered_nodup (he e))).1),
    tagged_nodup _ (fun e => (List.nodup_append.mp ((d e).reordered_nodup (he e))).2.1),?_⟩
  intro a ha b hb hab
  subst b
  obtain ⟨e,he',ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ha
  obtain ⟨e',he'',hb⟩ := List.mem_flatMap.mp hb
  obtain ⟨j',hj',heq⟩ := List.mem_map.mp hb
  have heq' := Sum.inr_injective heq
  cases heq'
  exact (List.nodup_append.mp ((d e).reordered_nodup (he e))).2.2 j hj j hj' rfl

end MatchingFPRAS.Enlargement

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Related
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Hierarchy

variable {V : Type*} [Fintype V]

variable (B : V → V → ℝ)

variable (hsym : ∀ a b, B a b = B b a)

variable (htri : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → min (B a c) (B c b) ≤ B a b)

variable (hfloor : ∀ a b, 1 ≤ B a b)

omit [Fintype V] in
lemma memberships_card_le_two {H : ℕ} (S : Finset (Label B hsym htri H)) (x : V)
    (hmem : ∀ a ∈ S, Mem B hsym htri a x)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, a.1.val ≤ b.1.val+1) : S.card ≤ 2 := by
  classical
  by_cases hne : S.Nonempty
  · obtain ⟨a,ha,hmin⟩ := S.exists_min_image (fun a => a.1.val) hne
    have hinj : Set.InjOn (fun a : Label B hsym htri H => a.1.val) S := by
      intro b hb c hc he
      exact eq_of_level_of_mem B hsym htri b c (Fin.ext he) (hmem b hb) (hmem c hc)
    have hsub : S.image (fun a => a.1.val) ⊆ {a.1.val,a.1.val+1} := by
      intro k hk
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hk
      have h₁ := hmin b hb
      have h₂ := hsep b hb a ha
      simp only [Finset.mem_insert,Finset.mem_singleton]
      omega
    calc
      S.card = (S.image (fun a => a.1.val)).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ ({a.1.val,a.1.val+1} : Finset ℕ).card := Finset.card_le_card hsub
      _ ≤ 2 := by simp
  · simp [Finset.not_nonempty_iff_eq_empty.mp hne]

variable {E : Type*} [Fintype E] (left right : E → V) (H : ℕ)

variable (hupper : ∀ e, B (left e) (right e) < (2:ℝ)^(H+1))

variable (hnear : ∀ x e f, Incident left right e x → Incident left right f x →
  B (left e) (right e) ≤ 2*B (left f) (right f))

omit [Fintype V] in
include hfloor hupper hnear in
lemma membership_count (x : V) : (memberships B hsym htri left right H x).card ≤ 2 := by
  apply memberships_card_le_two B hsym htri _ x
  · intro a ha; exact membership_mem B hsym htri hfloor left right H ha
  · intro a ha b hb
    exact memberships_level_near B hsym htri hfloor left right H hupper hnear ha hb

omit [Fintype V] in
include hfloor in
lemma common_height_le {x y : V} {l : Label B hsym htri H} (hxy : x≠y)
    (hx : l ∈ memberships B hsym htri left right H x)
    (hy : l ∈ memberships B hsym htri left right H y) : (2:ℝ)^l.1.val ≤ B x y := by
  exact (related_of_mem B hsym htri l
    (membership_mem B hsym htri hfloor left right H hx)
    (membership_mem B hsym htri hfloor left right H hy)).resolve_left hxy

end MatchingFPRAS.Hierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Height
attribute [-instance] _root_.OAI.MatchingFPRAS.Transport.Sparse.decideMatching _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Enlargement

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy Finset

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

lemma sourceBag_card_le_two (w : V → V → ℝ) (K : ℕ)
    (hw : ∀ x y, x ≠ y → edgeActivity w x y ≤ (4:ℝ)^K) (x : SourceVertex V K) :
    (sourceBags w K x).card ≤ 2 := by
  apply membership_count
  · exact sourceRealB_floor w K
  · intro e
    exact (source_strength_le_max w K hw e).trans_lt (maxSourceHeight_lt w K hw)
  · exact source_strength_incident_near w K hw

lemma sourceBag_height (w : V → V → ℝ) (K : ℕ) {x y : SourceVertex V K}
    (hxy : x ≠ y) (l : SourceLabel w K) (hx : l ∈ sourceBags w K x)
    (hy : l ∈ sourceBags w K y) : (2:ℝ)^l.1.val ≤ sourceRealB w K x y := by
  exact common_height_le _ _ _ (sourceRealB_floor w K) (realLeft K) (realRight K)
    (sourceLevels w K) hxy hx hy

end MatchingFPRAS.Enlargement

namespace MatchingFPRAS.Transport

section

open Finset

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

variable (inc : E → V → Prop)

theorem partition_add {R : Type*} [CommSemiring R] (r v : E → R)
    (hinc : ∀ e, ∃ x, inc e x) :
    partitionWeight inc (fun e => r e+v e) univ =
      ∑ Q : Partial inc, (∏ e ∈ Q.val, v e) * partitionWeight inc r (univ \ support inc Q.val) := by
  classical
  unfold partitionWeight
  have hex (M : Matchings inc univ) :
      (∏ e ∈ M.val, (r e+v e)) =
        ∑ Q : {Q : Finset E // Q⊆M.val}, (∏ e ∈ Q.val, v e) * ∏ e ∈ M.val \ Q.val, r e := by
    rw [show (∏ e ∈ M.val, (r e+v e))=(∏ e ∈ M.val, (v e+r e)) by
      apply Finset.prod_congr rfl; intro e he; exact add_comm _ _]
    rw [Finset.prod_add]
    exact Finset.sum_subtype _ (fun Q => Finset.mem_powerset)
      (fun Q => (∏ e ∈ Q, v e) * ∏ e ∈ M.val \ Q, r e)
  simp_rw [hex,Finset.mul_sum]
  have h := (expansionEquiv inc hinc).sum_comp
    (fun a => (∏ e ∈ a.1.val, v e) * ∏ e ∈ a.2.val, r e)
  rw [Fintype.sum_sigma,Fintype.sum_sigma] at h
  exact h

end

open Finset

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

variable (inc : E → V → Prop)

omit [Fintype E] [DecidableEq V] [DecidableEq E] in
lemma partial_eq_empty_iff (Q : Partial inc) : Q=emptyPartial inc ↔ Q.val=∅ := by
  exact Subtype.ext_iff

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
lemma partitionWeight_nonneg (r : E → ℝ) (hr : ∀ e,0 ≤ r e) (U : Finset V) :
    0≤partitionWeight inc r U := Finset.sum_nonneg (fun _ _ => Finset.prod_nonneg (fun e _ => hr e))

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
lemma partitionWeight_mono (r w : E → ℝ) (hr : ∀ e,0 ≤ r e) (hrw : ∀ e,r e≤w e)
    (U : Finset V) : partitionWeight inc r U≤partitionWeight inc w U :=
  Finset.sum_le_sum (fun _ _ => Finset.prod_le_prod (fun e _ => hr e) (fun e _ => hrw e))

lemma pow_mul_linear_le_one (x : ℝ) (hx : 0≤x) (m : ℕ) :
    (1+x)^m * (1-(m:ℝ)*x) ≤ 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ,Nat.cast_succ]
    have hp : 0≤(1+x)^m := pow_nonneg (by linarith) _
    have h : (1+x) * (1-((m:ℝ)+1)*x) ≤ 1-(m:ℝ)*x := by
      have hm : 0≤(m:ℝ) := Nat.cast_nonneg _
      nlinarith [sq_nonneg x,mul_nonneg hm (sq_nonneg x)]
    calc
      _ = (1+x)^m * ((1+x) * (1-((m:ℝ)+1)*x)) := by ring
      _ ≤ (1+x)^m * (1-(m:ℝ)*x) := mul_le_mul_of_nonneg_left h hp
      _ ≤ 1 := ih

lemma pow_small_le (x : ℝ) (hx : 0≤x) (m : ℕ) (hm : (m:ℝ)*x≤1/100) :
    (1+x)^m≤100/99 := by
  have hp : 0≤(1+x)^m := pow_nonneg (by linarith) _
  have h := pow_mul_linear_le_one x hx m
  nlinarith [mul_nonneg hp (show 0≤1/100-(m:ℝ)*x by linarith)]

lemma all_subsets_pow (x : ℝ) :
    (∑ Q : Finset E, x^Q.card)=(1+x)^Fintype.card E := by
  classical
  have h := Finset.prod_add (fun _ : E => x) (fun _ => (1:ℝ)) univ
  simpa [Finset.prod_const,Finset.prod_const_one,add_comm] using h.symm

omit [DecidableEq V] in
lemma partial_pow_sum_le (x : ℝ) (hx : 0≤x) :
    (∑ Q : Partial inc, x^Q.val.card) ≤ (1+x)^Fintype.card E := by
  classical
  rw [←all_subsets_pow]
  calc
    _ = ∑ Q ∈ univ.image (Subtype.val : Partial inc → Finset E), x^Q.card :=
      (Finset.sum_image (fun a _ b _ h => Subtype.ext h)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun Q _ _ => pow_nonneg hx _)

theorem finite_inflation (r v : E → ℝ) (hr : ∀ e,0 ≤ r e) (hv : ∀ e,0≤v e)
    (hinc : ∀ e,∃ x,inc e x) (hz : 0<partitionWeight inc r univ)
    (x : ℝ) (hx : 0≤x) (hm : (Fintype.card E:ℝ)*x≤1/100)
    (hlocal : ∀ Q : Partial inc, Q.val≠∅ →
      (∏ e ∈ Q.val, v e) * partitionWeight inc r (univ \ support inc Q.val) /
        partitionWeight inc r univ ≤ 2*x^Q.val.card) :
    1 ≤ partitionWeight inc (fun e => r e+v e) univ / partitionWeight inc r univ ∧
    partitionWeight inc (fun e => r e+v e) univ / partitionWeight inc r univ ≤ 2 := by
  classical
  constructor
  · apply (le_div_iff₀ hz).mpr
    simpa using partitionWeight_mono inc r (fun e => r e+v e) hr (fun e => le_add_of_nonneg_right (hv e)) univ
  · let mass (Q : Partial inc) := (∏ e ∈ Q.val, v e) *
      partitionWeight inc r (univ \ support inc Q.val) / partitionWeight inc r univ
    have hmass : ∀ Q : Partial inc, mass Q+(if Q=emptyPartial inc then 1 else 0)≤2*x^Q.val.card := by
      intro Q
      by_cases he : Q=emptyPartial inc
      · subst Q
        norm_num [mass,emptyPartial,hz.ne']
      · simpa only [ite_eq_right he,add_zero] using hlocal Q (fun h => he ((partial_eq_empty_iff inc Q).mpr h))
    have hs := Finset.sum_le_sum (s := (univ : Finset (Partial inc))) (fun Q _ => hmass Q)
    simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
      ←Finset.mul_sum] at hs
    have hsum := partial_pow_sum_le inc x hx
    have hpow := pow_small_le x hx (Fintype.card E) hm
    rw [partition_add inc r v hinc,Finset.sum_div]
    change (∑ Q : Partial inc, mass Q) ≤ 2
    linarith

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_HoleStrength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Enlargement

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open Finset

variable {V E : Type*} [Fintype V] [LinearOrder V] [Fintype E] [LinearOrder E]

lemma consumed_destination_injective {m : ℕ} (hm : Even m) (u v : E → V)
    (huv : ∀ e, u e ≠ v e) (R₀ : Finset V) (U : E → Finset (Fin m))
    (b : E → Selection m) (hb : FamilyHoles u v m R₀ U b)
    (d : E → HoleBlocks m) (he : ∀ e, (d e).flatten=(U e).sort (· ≤ ·)) (hp : ∀ e, (d e).Parity)
    (q : Vertex V E m × Vertex V E m) (hq : q ∈ consumedPairs u v m d)
    (q' : Vertex V E m × Vertex V E m) (hq' : q' ∈ consumedPairs u v m d)
    (hqq : q.2=q'.2) : q=q' := by
  obtain ⟨e,j,h | h⟩ := (mem_consumedPairs u v d q).mp hq
  · obtain ⟨hj,rfl⟩ := h
    obtain ⟨e',j',h' | h'⟩ := (mem_consumedPairs u v d q').mp hq'
    · obtain ⟨hj',rfl⟩ := h'
      have hx : u e=u e' := Sum.inl_injective hqq
      have hee := uses_unique hb (left_consumes hb d he hp e hj)
        (hx.symm ▸ left_consumes hb d he hp e' hj')
      subst e'
      have hjj := Option.mem_unique hj hj'
      subst j'
      rfl
    · obtain ⟨hj',rfl⟩ := h'
      have hx : u e=v e' := Sum.inl_injective hqq
      have hee := uses_unique hb (left_consumes hb d he hp e hj)
        (hx.symm ▸ right_consumes hm hb d he hp e' hj')
      subst e'
      exact (huv e hx).elim
  · obtain ⟨hj,rfl⟩ := h
    obtain ⟨e',j',h' | h'⟩ := (mem_consumedPairs u v d q').mp hq'
    · obtain ⟨hj',rfl⟩ := h'
      have hx : v e=u e' := Sum.inl_injective hqq
      have hee := uses_unique hb (right_consumes hm hb d he hp e hj)
        (hx.symm ▸ left_consumes hb d he hp e' hj')
      subst e'
      exact (huv e hx.symm).elim
    · obtain ⟨hj',rfl⟩ := h'
      have hx : v e=v e' := Sum.inl_injective hqq
      have hee := uses_unique hb (right_consumes hm hb d he hp e hj)
        (hx.symm ▸ right_consumes hm hb d he hp e' hj')
      subst e'
      have hjj := Option.mem_unique hj hj'
      subst j'
      rfl

lemma destination_nodup {m : ℕ} (hm : Even m) (u v : E → V)
    (huv : ∀ e, u e ≠ v e) (R₀ : Finset V) (U : E → Finset (Fin m))
    (b : E → Selection m) (hb : FamilyHoles u v m R₀ U b)
    (d : E → HoleBlocks m) (he : ∀ e, (d e).flatten=(U e).sort (· ≤ ·)) (hp : ∀ e, (d e).Parity) :
    ((consumedPairs u v m d).map Prod.snd).Nodup := by
  have hn := (List.nodup_append.mp (source_lists_nodup u v U d he)).2.1
  have hnd : (consumedPairs u v m d).Nodup := List.Nodup.of_map Prod.fst hn
  exact List.Nodup.map_on (consumed_destination_injective hm u v huv R₀ U b hb d he hp) hnd

lemma consumed_fresh {m : ℕ} (hm : Even m) (u v : E → V)
    (R₀ : Finset V) (U : E → Finset (Fin m)) (b : E → Selection m)
    (hb : FamilyHoles u v m R₀ U b) (d : E → HoleBlocks m)
    (he : ∀ e, (d e).flatten=(U e).sort (· ≤ ·)) (hp : ∀ e, (d e).Parity)
    (q : Vertex V E m × Vertex V E m) (hq : q ∈ consumedPairs u v m d) :
    q.2 ∉ enlargedHoles m R₀ U := by
  obtain ⟨e,j,h | h⟩ := (mem_consumedPairs u v d q).mp hq
  · obtain ⟨hj,rfl⟩ := h
    simpa using uses_not_hole hb (left_consumes hb d he hp e hj)
  · obtain ⟨hj,rfl⟩ := h
    simpa using uses_not_hole hb (right_consumes hm hb d he hp e hj)

@[simp] lemma mem_neutral_vertex_left (m : ℕ) (d : E → HoleBlocks m) (x : V) :
    Sum.inl x ∉ pairVertices (neutralPairs m d) := by
  rw [pairVertices_neutral]
  simp

@[simp] lemma mem_neutral_vertex_right (m : ℕ) (d : E → HoleBlocks m) (e : E) (j : Fin m) :
    Sum.inr (e,j) ∈ pairVertices (neutralPairs (V := V) m d) ↔
      j ∈ (d e).neutral.flatMap (fun q => [q.1,q.2]) := by
  rw [pairVertices_neutral]
  simp only [List.mem_flatMap,Finset.mem_toList,Finset.mem_univ,true_and,List.mem_map,
    Sum.inr.injEq,Prod.mk.injEq]
  constructor
  · rintro ⟨e',j',hj,hee,hjj⟩
    subst e'; subst j'; exact hj
  · intro hj; exact ⟨e,j,hj,rfl,rfl⟩

@[simp] lemma mem_consumed_source_left (u v : E → V) (m : ℕ) (d : E → HoleBlocks m) (x : V) :
    Sum.inl x ∉ (consumedPairs u v m d).map Prod.fst := by
  rw [consumed_sources]
  simp

@[simp] lemma mem_consumed_source_right (u v : E → V) (m : ℕ) (d : E → HoleBlocks m)
    (e : E) (j : Fin m) : Sum.inr (e,j) ∈ (consumedPairs u v m d).map Prod.fst ↔
      j ∈ (d e).left ∨ j ∈ (d e).right := by
  rw [consumed_sources]
  simp only [List.mem_flatMap,Finset.mem_toList,Finset.mem_univ,true_and,List.mem_map,
    Sum.inr.injEq,Prod.mk.injEq,List.mem_append,Option.mem_toList]
  constructor
  · rintro ⟨e',j',hj,hee,hjj⟩
    subst e'; subst j'; exact hj
  · intro hj; exact ⟨e,j,hj,rfl,rfl⟩




lemma mem_consumed_destination_left {m : ℕ} (hm : Even m) (u v : E → V)
    (R₀ : Finset V) (U : E → Finset (Fin m)) (b : E → Selection m)
    (hb : FamilyHoles u v m R₀ U b) (d : E → HoleBlocks m)
    (he : ∀ e, (d e).flatten=(U e).sort (· ≤ ·)) (hp : ∀ e, (d e).Parity) (x : V) :
    Sum.inl x ∈ (consumedPairs u v m d).map Prod.snd ↔
      ∃ e ∈ broken U, Uses u v b e x := by
  constructor
  · rintro h
    obtain ⟨q,hq,hqx⟩ := List.mem_map.mp h
    obtain ⟨e,j,h | h⟩ := (mem_consumedPairs u v d q).mp hq
    · obtain ⟨hj,rfl⟩ := h
      have hx : u e=x := Sum.inl_injective hqx
      refine ⟨e,(mem_broken U e).mpr ⟨j,(d e).left_mem (he e) hj⟩,?_⟩
      exact hx ▸ left_consumes hb d he hp e hj
    · obtain ⟨hj,rfl⟩ := h
      have hx : v e=x := Sum.inl_injective hqx
      refine ⟨e,(mem_broken U e).mpr ⟨j,(d e).right_mem (he e) hj⟩,?_⟩
      exact hx ▸ right_consumes hm hb d he hp e hj
  · rintro ⟨e,hbr,hus⟩
    have hU : (U e).Nonempty := (mem_broken U e).mp hbr
    rcases hus with ⟨hleft,hx⟩ | ⟨hright,hx⟩
    · have hsome := ((d e).left_uses (hb.1 e) hU (he e) (hp e)).mp hleft
      obtain ⟨j,hj⟩ := Option.isSome_iff_exists.mp hsome
      apply List.mem_map.mpr
      refine ⟨(Sum.inr (e,j),Sum.inl (u e)),?_,by simp only [hx]⟩
      apply (mem_consumedPairs u v d _).mpr
      exact ⟨e,j,Or.inl ⟨hj,rfl⟩⟩
    · have hsome := ((d e).right_uses hm (hb.1 e) hU (he e) (hp e)).mp hright
      obtain ⟨j,hj⟩ := Option.isSome_iff_exists.mp hsome
      apply List.mem_map.mpr
      refine ⟨(Sum.inr (e,j),Sum.inl (v e)),?_,by simp only [hx]⟩
      apply (mem_consumedPairs u v d _).mpr
      exact ⟨e,j,Or.inr ⟨hj,rfl⟩⟩

lemma internal_covered {m : ℕ} (u v : E → V) (U : E → Finset (Fin m))
    (d : E → HoleBlocks m) (he : ∀ e, (d e).flatten=(U e).sort (· ≤ ·)) (e : E) (j : Fin m) :
    j ∈ U e ↔ Sum.inr (e,j) ∈ pairVertices (neutralPairs (V := V) m d) ∨
      Sum.inr (e,j) ∈ (consumedPairs u v m d).map Prod.fst := by
  rw [mem_neutral_vertex_right,mem_consumed_source_right,← Finset.mem_sort (· ≤ ·),← he e]
  simp only [HoleBlocks.flatten,List.mem_append,Option.mem_toList]
  tauto

theorem charged_set_eq {m : ℕ} (hm : Even m) (u v : E → V)
    (R₀ : Finset V) (U : E → Finset (Fin m)) (b : E → Selection m)
    (hb : FamilyHoles u v m R₀ U b) (d : E → HoleBlocks m)
    (he : ∀ e, (d e).flatten=(U e).sort (· ≤ ·)) (hp : ∀ e, (d e).Parity) :
    ((enlargedHoles m R₀ U \ (pairVertices (neutralPairs m d)).toFinset) \
      ((consumedPairs u v m d).map Prod.fst).toFinset) ∪
      ((consumedPairs u v m d).map Prod.snd).toFinset =
      (residualHoles u v R₀ U b).map ⟨Sum.inl,Sum.inl_injective⟩ := by
  classical
  ext a
  cases a with
  | inl x =>
    simp only [Finset.mem_union,Finset.mem_sdiff,List.mem_toFinset,mem_enlargedHoles_left,
      mem_neutral_vertex_left,mem_consumed_source_left,not_false_eq_true,and_true,
      Finset.mem_map,Function.Embedding.coeFn_mk,Sum.inl.injEq,exists_eq_right,
      mem_residualHoles,mem_consumed_destination_left hm u v R₀ U b hb d he hp]
  | inr a =>
    obtain ⟨e,j⟩ := a
    simp only [Finset.mem_union,Finset.mem_sdiff,List.mem_toFinset,mem_enlargedHoles_right,
      mem_consumed_destination_right,or_false,Finset.mem_map,Function.Embedding.coeFn_mk,
      Sum.inl_ne_inr,and_false,exists_false]
    have hc := (internal_covered u v U d he e j).mp
    tauto

theorem deletion_charge_trace (u v : E → V) (huv : ∀ e, u e ≠ v e)
    (p : ℕ) (hp : 1 ≤ p) (B Hu Hv lam : E → ℝ) (hB : ∀ e, 1 ≤ B e)
    (hHu : ∀ e, 0 ≤ Hu e) (hHv : ∀ e, 0 ≤ Hv e) (hlam0 : ∀ e, 0 ≤ lam e)
    (hlam : ∀ e, lam e ≤ B e) (R₀ : Finset V) (U : E → Finset (Fin (4*p)))
    (b : E → Selection (4*p)) (hb : FamilyHoles u v (4*p) R₀ U b)
    (d : E → HoleBlocks (4*p)) (he : ∀ e, (d e).flatten=(U e).sort (· ≤ ·))
    (hpar : ∀ e, (d e).Parity) :
    ChargeTrace (realBottleneck u v p B Hu Hv lam) (enlargedHoles (4*p) R₀ U)
      ((residualHoles u v R₀ U b).map ⟨Sum.inl,Sum.inl_injective⟩)
      (totalDeletionCharge u v p B Hu Hv lam d) := by
  classical
  have hm : Even (4*p) := ⟨2*p,by omega⟩
  have hB0 : ∀ e, 0 < B e := fun e => lt_of_lt_of_le zero_lt_one (hB e)
  have hs := source_lists_nodup u v U d he
  let N := neutralPairs (V := V) (4*p) d
  let C := consumedPairs u v (4*p) d
  let H := enlargedHoles (4*p) R₀ U
  let BB := realBottleneck u v p B Hu Hv lam
  let T := holeStrength (V := V) p B Hu Hv
  let fN := neutralCharge (V := V) p B Hu Hv lam
  let fC := consumedCharge u p B Hu Hv lam
  have hsubN : ∀ a ∈ pairVertices N, a ∈ H := by
    intro a ha
    cases a with
    | inl x => exact (mem_neutral_vertex_left (4*p) d x ha).elim
    | inr a =>
      obtain ⟨e,j⟩ := a
      exact (mem_enlargedHoles_right (4*p) R₀ U e j).mpr
        ((internal_covered u v U d he e j).mpr (Or.inl ha))
  have hlocalN : ∀ q ∈ N, 0 < T q.1 ∧ 0 < T q.2 ∧ 0 ≤ fN q ∧
      (∀ a, a ≠ q.1 → BB q.1 a ≤ T q.1) ∧
      (∀ a, a ≠ q.2 → BB q.2 a ≤ T q.2) ∧ fN q*T q.1*T q.2 ≤ BB q.1 q.2 := by
    intro q hq
    obtain ⟨e,r,hr,rfl⟩ := (mem_neutralPairs d q).mp hq
    refine ⟨(hB0 e).trans_le (le_internalStrength _ _ _ _ _),
      (hB0 e).trans_le (le_internalStrength _ _ _ _ _),
      neutralFactor_nonneg p _ _ _ _ (hB0 e) (hlam0 e) _ _,?_,?_,?_⟩
    · intro a _; exact realBottleneck_internal_cap u v p hp B Hu Hv lam hB hHu hHv hlam e r.1 a
    · intro a _; exact realBottleneck_internal_cap u v p hp B Hu Hv lam hB hHu hHv hlam e r.2 a
    · exact neutral_local_charge u v huv p hp B Hu Hv lam hB0 hHu hHv hlam e r.1 r.2
        ((d e).neutral_lt (he e) r hr)
  have hsubC : ∀ q ∈ C, q.1 ∈ H \ (pairVertices N).toFinset := by
    intro q hq
    have hq' : q.1 ∈ C.map Prod.fst := List.mem_map.mpr ⟨q,hq,rfl⟩
    refine Finset.mem_sdiff.mpr ⟨?_,?_⟩
    · cases hqa : q.1 with
      | inl x => exact (mem_consumed_source_left u v (4*p) d x (hqa ▸ hq')).elim
      | inr a =>
        obtain ⟨e,j⟩ := a
        rw [mem_enlargedHoles_right]
        exact (internal_covered u v U d he e j).mpr (Or.inr (hqa ▸ hq'))
    · intro hn
      exact (List.nodup_append.mp hs).2.2 q.1 (List.mem_toFinset.mp hn) q.1 hq' rfl
  have hfresh : ∀ q ∈ C, q.2 ∉ H \ (pairVertices N).toFinset := by
    intro q hq hmem
    exact consumed_fresh hm u v R₀ U b hb d he hpar q hq (Finset.mem_sdiff.mp hmem).1
  have hlocalC : ∀ q ∈ C, 0 < T q.1 ∧ 0 ≤ fC q ∧
      (∀ a, a ≠ q.1 → BB q.1 a ≤ T q.1) ∧ fC q*T q.1 ≤ BB q.1 q.2 := by
    intro q hq
    obtain ⟨e,j,h | h⟩ := (mem_consumedPairs u v d q).mp hq
    · obtain ⟨hj,rfl⟩ := h
      have hc : fC (Sum.inr (e,j),Sum.inl (u e))=leftFactor p (B e) (Hu e) (Hv e) (lam e) j := by
        simp [fC,consumedCharge]
      rw [hc]
      refine ⟨(hB0 e).trans_le (le_internalStrength _ _ _ _ _),
        leftFactor_nonneg p _ _ _ _ (hB0 e) (hlam0 e) _,?_,?_⟩
      · intro a _; exact realBottleneck_internal_cap u v p hp B Hu Hv lam hB hHu hHv hlam e j a
      · exact left_local_charge u v huv p hp B Hu Hv lam hB0 hHu hlam e j
    · obtain ⟨hj,rfl⟩ := h
      have hc : fC (Sum.inr (e,j),Sum.inl (v e))=rightFactor p (B e) (Hu e) (Hv e) (lam e) j := by
        simp [fC,consumedCharge,(huv e).symm]
      rw [hc]
      refine ⟨(hB0 e).trans_le (le_internalStrength _ _ _ _ _),
        rightFactor_nonneg p _ _ _ _ (hB0 e) (hlam0 e) _,?_,?_⟩
      · intro a _; exact realBottleneck_internal_cap u v p hp B Hu Hv lam hB hHu hHv hlam e j a
      · exact right_local_charge u v huv p hp B Hu Hv lam hB0 hHv hlam e j
  have htN := charge_remove_list BB T fN N H (List.nodup_append.mp hs).1 hsubN hlocalN
  have htC := charge_replace_list BB T fC C (H \ (pairVertices N).toFinset)
    (List.nodup_append.mp hs).2.1 (destination_nodup hm u v huv R₀ U b hb d he hpar) hsubC hfresh hlocalC
  have hC0 : 0 ≤ (C.map fC).prod := by
    apply List.prod_nonneg
    intro a ha
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ha
    exact (hlocalC q hq).2.1
  have htrace := htN.trans htC hC0
  change ChargeTrace _ _ _ (totalDeletionCharge u v p B Hu Hv lam d) at htrace
  simpa only [N,C,H,charged_set_eq hm u v R₀ U b hb d he hpar] using htrace

theorem deletion_capacity_bound (w : V → V → ℝ) (hw : ∀ a b, 0 < w a b)
    (p : ℕ) (hp : 1 ≤ p) (Hu Hv : LogicalEdge V → ℝ)
    (hHu : ∀ e, 0 ≤ Hu e) (hHv : ∀ e, 0 ≤ Hv e)
    (R₀ : Finset V) (U : LogicalEdge V → Finset (Fin (4*p)))
    (b : LogicalEdge V → Selection (4*p)) (hb : FamilyHoles source target (4*p) R₀ U b)
    (d : LogicalEdge V → HoleBlocks (4*p)) (he : ∀ e, (d e).flatten=(U e).sort (· ≤ ·))
    (hpar : ∀ e, (d e).Parity) (hH : Even (enlargedHoles (4*p) R₀ U).card) :
    ∃ hR : Even (residualHoles source target R₀ U b).card,
      pairingCapacity (realBottleneck source target p
        (fun e => bottleneck w (source e) (target e)) Hu Hv (logicalActivity w))
        (enlargedHoles (4*p) R₀ U) hH *
      totalDeletionCharge source target p (fun e => bottleneck w (source e) (target e))
        Hu Hv (logicalActivity w) d ≤
      pairingCapacity (bottleneck w) (residualHoles source target R₀ U b) hR := by
  classical
  have ht := deletion_charge_trace source target source_ne_target p hp
    (fun e => bottleneck w (source e) (target e)) Hu Hv (logicalActivity w)
    (fun e => one_le_bottleneck w _ _) hHu hHv
    (fun e => by unfold logicalActivity edgeActivity; split_ifs <;> exact (hw _ _).le)
    (fun e => edgeActivity_le_bottleneck w _ _ (source_ne_target e)) R₀ U b hb d he hpar
  obtain ⟨hR,hle⟩ := ChargeTrace.capacity_bound_decidable _
    (fun a b => bottleneck_comm _ a b)
    (fun a b => zero_le_one.trans (one_le_bottleneck _ a b))
    (fun a b c hab hac hbc => bottleneck_ultrametric _ a b c hab hac hbc) ht hH
  have hR' : Even (residualHoles source target R₀ U b).card := by simpa using hR
  refine ⟨hR',?_⟩
  have hx := pairingCapacity_sum_inl (terminal_lt_iff (4*p)) (bottleneck w) _
    (terminal_bottleneck w p hp Hu Hv) _ hR' hR
  apply hle.trans_eq
  convert hx using 1
  all_goals try with_reducible_and_instances rfl
  rfl

lemma blockCharge_potential (p : ℕ) (B Hu Hv lam : ℝ) (hlam : lam ≠ 0)
    (U : Finset (Fin (4*p))) (d : HoleBlocks (4*p))
    (he : d.flatten=U.sort (· ≤ ·)) (hp : d.Parity) :
    blockCharge p B Hu Hv lam d =
      (if d.right.isSome then lam else 1) *
      ((d.flatten.map (fun j => vertexPotential p B Hu Hv lam (j.val+1))).prod)⁻¹ := by
  let z := fun j : Fin (4*p) => vertexPotential p B Hu Hv lam (j.val+1)
  have hleft : (d.left.toList.map (leftFactor p B Hu Hv lam)).prod =
      ((d.left.toList.map z).prod)⁻¹ := by
    cases hl : d.left with
    | none => simp
    | some j =>
      have hj := hp.1 j (by simp [hl])
      simpa [hl,z] using leftFactor_eq_potential p B Hu Hv lam j hj
  have hright : (d.right.toList.map (rightFactor p B Hu Hv lam)).prod =
      (if d.right.isSome then lam else 1) * ((d.right.toList.map z).prod)⁻¹ := by
    cases hr : d.right with
    | none => simp
    | some j =>
      have hj := hp.2.2 j (by simp [hr])
      simpa [hr,z,div_eq_mul_inv] using rightFactor_eq_potential p B Hu Hv lam hlam j hj
  have hneutral : (d.neutral.map (fun q => neutralFactor p B Hu Hv lam q.1 q.2)).prod =
      (((d.neutral.flatMap (fun q => [q.1,q.2])).map z).prod)⁻¹ := by
    have hh : d.neutral.map (fun q => neutralFactor p B Hu Hv lam q.1 q.2)=
        d.neutral.map (fun q => (z q.1*z q.2)⁻¹) := by
      apply List.map_congr_left
      intro q hq
      exact neutralFactor_eq_potential p B Hu Hv lam hlam q.1 q.2
        (d.neutral_lt he q hq) (hp.2.1 q hq).1 (hp.2.1 q hq).2
    rw [hh]
    simp only [List.flatMap_def]
    simp [List.prod_inv,Function.comp_def]
  unfold blockCharge
  rw [hleft,hright,hneutral]
  simp only [HoleBlocks.flatten,List.map_append,List.prod_append,mul_inv_rev]
  change _ = (if d.right.isSome then lam else 1) * _
  ring

lemma forcing_weight_charge (p : ℕ) (B Hu Hv lam : ℝ) (hB : 0 < B) (hlam : 0 < lam)
    (U : Finset (Fin (4*p))) (b : Selection (4*p)) (hb : Valid U b)
    (d : HoleBlocks (4*p)) (he : d.flatten=U.sort (· ≤ ·)) (hp : d.Parity) :
    (if U.Nonempty then selectedWeight (profileActivity p B Hu Hv lam) b else pathConstant p B Hu Hv) =
      pathConstant p B Hu Hv * blockCharge p B Hu Hv lam d := by
  classical
  rw [blockCharge_potential p B Hu Hv lam hlam.ne' U d he hp]
  by_cases hU : U.Nonempty
  · rw [ite_eq_left hU]
    let z : Fin (4*p+2) → ℝ := fun i => vertexPotential p B Hu Hv lam i.val
    have hprof : (fun i : Fin (4*p+1) => z i.castSucc*z i.succ)=profileActivity p B Hu Hv lam := by
      funext i
      exact (profile_vertexPotential p B Hu Hv lam hlam.ne' i).symm
    have hh := selectedWeight_hole_product (show Even (4*p) from ⟨2*p,by omega⟩) U b hb z
    rw [hprof,exact_profile_weight] at hh
    have hprod : (d.flatten.map (fun j => vertexPotential p B Hu Hv lam (j.val+1))).prod =
        ∏ j ∈ U, z j.succ.castSucc := by
      rw [he,((Finset.sort_perm_toList U (· ≤ ·)).map _).prod_eq,Finset.prod_map_toList]
      rfl
    have hz0 : z 0=1 := vertexPotential_zero p B Hu Hv lam
    have hzlast : z (Fin.last (4*p+1))=lam := vertexPotential_last p B Hu Hv lam
    have hr : (b (Fin.last (4*p))=true) ↔ d.right.isSome :=
      d.right_uses ⟨2*p,by omega⟩ hb hU he hp
    have hl : (if b 0 then z 0 else 1)=1 := by rw [hz0]; split_ifs <;> rfl
    simp only [Bool.false_eq_true,ite_false,mul_one,hl,hzlast] at hh
    simp only [hr] at hh
    have hz : (∏ j ∈ U, z j.succ.castSucc) ≠ 0 := by
      apply ne_of_gt
      apply Finset.prod_pos
      intro j hj
      exact vertexPotential_pos p B Hu Hv lam hB hlam _
    rw [hprod]
    change _=pathConstant p B Hu Hv * ((if d.right.isSome then lam else 1)*_)
    apply (mul_right_cancel₀ hz)
    rw [mul_assoc,mul_assoc,inv_mul_cancel₀ hz,mul_one]
    exact hh
  · rw [ite_eq_right hU]
    have hh : d.flatten=[] := by rw [he,Finset.not_nonempty_iff_eq_empty.mp hU]; simp
    have hr : d.right=none := by
      have he' := hh
      simp only [HoleBlocks.flatten,List.append_eq_nil_iff] at he'
      cases hr : d.right <;> simp_all
    simp [hh,hr]

end MatchingFPRAS.Enlargement

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Incident
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Enlargement

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open Finset

variable {V E : Type*} [Fintype V] [LinearOrder V] [Fintype E] [LinearOrder E]

omit [Fintype V] [LinearOrder E] in
lemma totalDeletionCharge_eq_blocks [Fintype V] [LinearOrder E]
    (u v : E → V) (huv : ∀ e, u e ≠ v e)
    (p : ℕ) (B Hu Hv lam : E → ℝ) (d : E → HoleBlocks (4*p)) :
    totalDeletionCharge u v p B Hu Hv lam d =
      ∏ e, blockCharge p (B e) (Hu e) (Hv e) (lam e) (d e) := by
  classical
  simp only [totalDeletionCharge,neutralPairs,consumedPairs,
    List.flatMap_def,List.map_flatten,List.prod_flatten,List.map_map,Function.comp_def,
    List.map_append,List.prod_append]
  simp only [neutralCharge,consumedCharge,ite_true,(huv _).symm,ite_false]
  simp only [Finset.prod_map_toList,blockCharge,Finset.prod_mul_distrib]
  ring

theorem deletionConstant_eq_charge (u v : E → V) (huv : ∀ e, u e ≠ v e)
    (p : ℕ) (B Hu Hv lam : E → ℝ) (hB : ∀ e, 0 < B e) (hlam : ∀ e, 0 < lam e)
    (R₀ : Finset V) (U : E → Finset (Fin (4*p))) (b : E → Selection (4*p))
    (hb : FamilyHoles u v (4*p) R₀ U b)
    (d : E → HoleBlocks (4*p)) (he : ∀ e, (d e).flatten=(U e).sort (· ≤ ·))
    (hpar : ∀ e, (d e).Parity) :
    deletionConstant U b (pathActivity p B Hu Hv lam) (fun e => pathConstant p (B e) (Hu e) (Hv e)) =
      (∏ e, pathConstant p (B e) (Hu e) (Hv e)) * totalDeletionCharge u v p B Hu Hv lam d := by
  rw [totalDeletionCharge_eq_blocks u v huv,← Finset.prod_mul_distrib]
  unfold deletionConstant
  apply Finset.prod_congr rfl
  intro e _
  exact forcing_weight_charge p (B e) (Hu e) (Hv e) (lam e) (hB e) (hlam e)
    (U e) (b e) (hb.1 e) (d e) (he e) (hpar e)

theorem real_partition_charge_identity (u v : E → V) (huv : ∀ e, u e ≠ v e)
    (p : ℕ) (B Hu Hv lam : E → ℝ) (hB : ∀ e, 0 < B e) (hlam : ∀ e, 0 < lam e)
    (R₀ : Finset V) (U : E → Finset (Fin (4*p))) (b : E → Selection (4*p))
    (hb : FamilyHoles u v (4*p) R₀ U b)
    (d : E → HoleBlocks (4*p)) (he : ∀ e, (d e).flatten=(U e).sort (· ≤ ·))
    (hpar : ∀ e, (d e).Parity) :
    realHolePartition u v (4*p) R₀ U (pathActivity p B Hu Hv lam) =
      (∏ e, pathConstant p (B e) (Hu e) (Hv e)) * totalDeletionCharge u v p B Hu Hv lam d *
      logicalHolePartition u v (residualHoles u v R₀ U b) (broken U) lam := by
  classical
  have hid := deletion_partition_identity (show Even (4*p) from ⟨2*p,by omega⟩)
    u v R₀ U b hb (pathActivity p B Hu Hv lam)
    (fun e => List.ofFn fun r : Fin p => max (B e) (Hu e/2^r.val))
    (fun e => (List.ofFn fun r : Fin p => max (B e) (Hv e/2^r.val)).reverse) lam
    (fun e => profileActivity_ofFn p (B e) (Hu e) (Hv e) (lam e))
  simp only [List.prod_reverse,List.prod_ofFn] at hid
  change realHolePartition _ _ _ _ _ _ =
    deletionConstant U b (pathActivity p B Hu Hv lam)
      (fun e => pathConstant p (B e) (Hu e) (Hv e)) * _ at hid
  rw [hid,deletionConstant_eq_charge u v huv p B Hu Hv lam hB hlam R₀ U b hb d he hpar]

end MatchingFPRAS.Enlargement

namespace MatchingFPRAS.Representation

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.Enlargement
open Finset

variable {V : Type*} [Fintype V] [LinearOrder V]

variable (R : Finset V) (s : LogicalEdge V → Bool)
    (hs : LogicalHoles source target R ∅ s)

variable {R s hs}

lemma selection_weight (w : V → V → ℝ) (m : Mate V) :
    (∏ e : LogicalEdge V, if select m e then logicalActivity w e else 1)=weight w m := by
  classical
  unfold weight
  rw [← Finset.prod_filter,← Finset.prod_filter]
  apply Finset.prod_bij (fun e _ => source e)
  · intro e he
    have hh := (select_eq_true m e).mp (Finset.mem_filter.mp he).2
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    rw [hh]
    exact e.property
  · intro e he f hf h
    have he' := (select_eq_true m e).mp (Finset.mem_filter.mp he).2
    have hf' := (select_eq_true m f).mp (Finset.mem_filter.mp hf).2
    exact Subtype.ext (Prod.ext h (he'.symm.trans ((congrArg m.val h).trans hf')))
  · intro x hx
    have hx' := (Finset.mem_filter.mp hx).2
    refine ⟨⟨(x,m.val x),hx'⟩,?_,rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp [select,source,target]⟩
  · intro e he
    have he' := (select_eq_true m e).mp (Finset.mem_filter.mp he).2
    simp only [logicalActivity,edgeActivity,show source e < target e from e.property,ite_true,he']

lemma asMate_weight (w : V → V → ℝ) :
    (∏ e : LogicalEdge V, if s e then logicalActivity w e else 1)=weight w (asMate R s hs) := by
  rw [← selection_weight,select_asMate]

theorem logical_partition_eq (w : V → V → ℝ) (R : Finset V) :
    logicalHolePartition source target R ∅ (logicalActivity w)=partition w R := by
  classical
  let := Fintype.ofFinite {s : LogicalEdge V → Bool // LogicalHoles source target R ∅ s}
  let := Fintype.ofFinite {m : Mate V // HasHoles m R}
  unfold logicalHolePartition partition
  rw [Finset.sum_subtype (matchings R) (fun m => mem_matchings m R)]
  apply Fintype.sum_equiv (matchingEquiv R)
  intro s
  exact asMate_weight w

theorem logical_partition_forbidden_le (w : V → V → ℝ) (hw : ∀ a b, 0 ≤ w a b)
    (R : Finset V) (forbidden : Finset (LogicalEdge V)) :
    logicalHolePartition source target R forbidden (logicalActivity w) ≤ partition w R := by
  classical
  let := Fintype.ofFinite {s : LogicalEdge V → Bool // LogicalHoles source target R forbidden s}
  let := Fintype.ofFinite {s : LogicalEdge V → Bool // LogicalHoles source target R ∅ s}
  rw [← logical_partition_eq]
  unfold logicalHolePartition
  let f : {s : LogicalEdge V → Bool // LogicalHoles source target R forbidden s} →
      {s : LogicalEdge V → Bool // LogicalHoles source target R ∅ s} :=
    fun s => ⟨s.val,⟨by simp,s.property.2⟩⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg
      (fun z : {s : LogicalEdge V → Bool // LogicalHoles source target R ∅ s} => z.val) hab)
  let g := fun s : {s : LogicalEdge V → Bool // LogicalHoles source target R ∅ s} =>
    ∏ e, if s.val e then logicalActivity w e else 1
  calc
    _ = ∑ y ∈ Finset.univ.image f, g y := by
      rw [Finset.sum_image hf.injOn]
    _ ≤ ∑ y, g y := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro s _ _
      apply Finset.prod_nonneg
      intro e _
      split_ifs
      · unfold logicalActivity edgeActivity
        split_ifs <;> exact hw _ _
      · norm_num

end MatchingFPRAS.Representation

namespace MatchingFPRAS.Enlargement

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Representation
open Finset

variable {V : Type*} [Fintype V] [LinearOrder V]

lemma pathConstant_pos (p : ℕ) (B Hu Hv : ℝ) (hB : 0 < B) :
    0 < pathConstant p B Hu Hv := by
  apply mul_pos <;> apply Finset.prod_pos <;> intro i hi <;> exact hB.trans_le (le_max_left _ _)

theorem intact_partition_identity (w : V → V → ℝ) (hz : 0 < partition w ∅)
    (p : ℕ) (B Hu Hv : LogicalEdge V → ℝ) :
    realHolePartition source target (4*p) ∅ (fun _ => ∅)
      (pathActivity p B Hu Hv (logicalActivity w)) =
      (∏ e, pathConstant p (B e) (Hu e) (Hv e)) * partition w ∅ := by
  classical
  have hn : (matchings (∅ : Finset V)).Nonempty := by
    by_contra hn
    have hz0 : partition w ∅=0 := by
      simp [partition,Finset.not_nonempty_iff_eq_empty.mp hn]
    linarith
  obtain ⟨m,hm⟩ := hn
  let b := fun (e : LogicalEdge V) (i : Fin (4*p+1)) => alternating (select m e) i.val
  have hb := intact_family p m ((mem_matchings m ∅).mp hm)
  have hid := deletion_partition_identity (show Even (4*p) from ⟨2*p,by omega⟩)
    source target ∅ (fun _ => ∅) b hb (pathActivity p B Hu Hv (logicalActivity w))
    (fun e => List.ofFn fun r : Fin p => max (B e) (Hu e/2^r.val))
    (fun e => (List.ofFn fun r : Fin p => max (B e) (Hv e/2^r.val)).reverse) _
    (fun e => profileActivity_ofFn p (B e) (Hu e) (Hv e) (logicalActivity w e))
  simpa [residualHoles,broken,deletionConstant,List.prod_ofFn,pathConstant,
    logical_partition_eq] using hid

theorem lifted_hole_bound_feasible (hn : 2 ≤ Fintype.card V)
    (w : V → V → ℝ) (hw : ∀ a b, 0 < w a b) (hz : 0 < partition w ∅)
    (hrlo : ∀ a, (1:ℝ)/4 ≤ rowMax hn w a) (hrhi : ∀ a, rowMax hn w a ≤ 1)
    (p : ℕ) (hp : 1 ≤ p) (Hu Hv : LogicalEdge V → ℝ)
    (hHu : ∀ e, 0 ≤ Hu e) (hHv : ∀ e, 0 ≤ Hv e)
    (R₀ : Finset V) (U : LogicalEdge V → Finset (Fin (4*p)))
    (b : LogicalEdge V → Selection (4*p)) (hb : FamilyHoles source target (4*p) R₀ U b)
    (hH : Even (enlargedHoles (4*p) R₀ U).card) :
    realHolePartition source target (4*p) R₀ U
        (pathActivity p (fun e => bottleneck w (source e) (target e)) Hu Hv (logicalActivity w)) /
      realHolePartition source target (4*p) ∅ (fun _ => ∅)
        (pathActivity p (fun e => bottleneck w (source e) (target e)) Hu Hv (logicalActivity w)) *
      pairingCapacity (realBottleneck source target p
        (fun e => bottleneck w (source e) (target e)) Hu Hv (logicalActivity w))
        (enlargedHoles (4*p) R₀ U) hH ≤
      2 * holeScale V ^ ((enlargedHoles (4*p) R₀ U).card/2) := by
  classical
  choose d he hpar using (fun e => hole_blocks_exist (hb.1 e))
  let B := fun e : LogicalEdge V => bottleneck w (source e) (target e)
  let R := residualHoles source target R₀ U b
  let F := totalDeletionCharge source target p B Hu Hv (logicalActivity w) d
  let C := ∏ e, pathConstant p (B e) (Hu e) (Hv e)
  let Zf := logicalHolePartition source target R (broken U) (logicalActivity w)
  have hB : ∀ e, 0 < B e := fun e => lt_of_lt_of_le zero_lt_one (one_le_bottleneck _ _ _)
  have hlam : ∀ e, 0 < logicalActivity w e := by
    intro e
    unfold logicalActivity edgeActivity
    split_ifs <;> exact hw _ _
  have hC : 0 < C := Finset.prod_pos (fun e _ => pathConstant_pos p _ _ _ (hB e))
  have htrace := deletion_charge_trace source target source_ne_target p hp B Hu Hv (logicalActivity w)
    (fun e => one_le_bottleneck w _ _) hHu hHv (fun e => (hlam e).le)
    (fun e => edgeActivity_le_bottleneck w _ _ (source_ne_target e)) R₀ U b hb d he hpar
  have hF : 0 ≤ F := htrace.factor_nonneg
  have hcard : R.card ≤ (enlargedHoles (4*p) R₀ U).card := by
    simpa using htrace.card_le
  obtain ⟨hR,hcap⟩ := deletion_capacity_bound w hw p hp Hu Hv hHu hHv R₀ U b hb d he hpar hH
  have hZf : 0 ≤ Zf := by
    unfold Zf logicalHolePartition
    apply Finset.sum_nonneg
    intro s _
    apply Finset.prod_nonneg
    intro e _
    split_ifs <;> first | exact (hlam e).le | norm_num
  have hZf_le : Zf ≤ partition w R := logical_partition_forbidden_le w (fun a b => (hw a b).le) R _
  rw [real_partition_charge_identity source target source_ne_target p B Hu Hv (logicalActivity w)
    hB hlam R₀ U b hb d he hpar,intact_partition_identity w hz p B Hu Hv]
  change (C * F * Zf) / (C * partition w ∅) * _ ≤ _
  calc
    _ = (Zf / partition w ∅) * (pairingCapacity (realBottleneck source target p B Hu Hv (logicalActivity w))
      (enlargedHoles (4*p) R₀ U) hH * F) := by field_simp [hC.ne',hz.ne']; ring
    _ ≤ (Zf / partition w ∅) * pairingCapacity (bottleneck w) R hR :=
      mul_le_mul_of_nonneg_left hcap (div_nonneg hZf hz.le)
    _ ≤ (partition w R / partition w ∅) * pairingCapacity (bottleneck w) R hR :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hZf_le hz.le)
        (pairingCapacity_nonneg _ (fun a b => zero_le_one.trans (one_le_bottleneck w a b)) R hR)
    _ ≤ 2 * holeScale V ^ (R.card/2) := logical_hole_bound hn w (fun a b => (hw a b).le) hz hrlo hrhi R hR
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply pow_le_pow_right₀ _ (Nat.div_le_div_right hcard)
      unfold holeScale
      have hN : (1:ℝ) ≤ (Fintype.card V : ℝ)+1 := by have := Nat.cast_nonneg (α := ℝ) (Fintype.card V); linarith
      have hp4 := one_le_pow₀ hN (n := 4)
      linarith

theorem lifted_hole_bound (hn : 2 ≤ Fintype.card V)
    (w : V → V → ℝ) (hw : ∀ a b, 0 < w a b) (hz : 0 < partition w ∅)
    (hrlo : ∀ a, (1:ℝ)/4 ≤ rowMax hn w a) (hrhi : ∀ a, rowMax hn w a ≤ 1)
    (p : ℕ) (hp : 1 ≤ p) (Hu Hv : LogicalEdge V → ℝ)
    (hHu : ∀ e, 0 ≤ Hu e) (hHv : ∀ e, 0 ≤ Hv e)
    (R₀ : Finset V) (U : LogicalEdge V → Finset (Fin (4*p)))
    (hH : Even (enlargedHoles (4*p) R₀ U).card) :
    realHolePartition source target (4*p) R₀ U
        (pathActivity p (fun e => bottleneck w (source e) (target e)) Hu Hv (logicalActivity w)) /
      realHolePartition source target (4*p) ∅ (fun _ => ∅)
        (pathActivity p (fun e => bottleneck w (source e) (target e)) Hu Hv (logicalActivity w)) *
      pairingCapacity (realBottleneck source target p
        (fun e => bottleneck w (source e) (target e)) Hu Hv (logicalActivity w))
        (enlargedHoles (4*p) R₀ U) hH ≤
      2 * holeScale V ^ ((enlargedHoles (4*p) R₀ U).card/2) := by
  classical
  by_cases h : ∃ b, FamilyHoles source target (4*p) R₀ U b
  · obtain ⟨b,hb⟩ := h
    exact lifted_hole_bound_feasible hn w hw hz hrlo hrhi p hp Hu Hv hHu hHv R₀ U b hb hH
  · have hempty : IsEmpty {b : LogicalEdge V → Selection (4*p) //
        FamilyHoles source target (4*p) R₀ U b} := ⟨fun b => h ⟨b.val,b.property⟩⟩
    have hzero : realHolePartition source target (4*p) R₀ U
        (pathActivity p (fun e => bottleneck w (source e) (target e)) Hu Hv (logicalActivity w)) = 0 := by
      let := hempty
      unfold realHolePartition
      exact Finset.sum_eq_zero (fun b _ => isEmptyElim b)
    rw [hzero,zero_div,zero_mul]
    unfold holeScale
    positivity

end MatchingFPRAS.Enlargement

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_EdgeLow
attribute [-instance] _root_.OAI.MatchingFPRAS.Transport.Sparse.decideMatching _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.allowedDec _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.edgeDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

section

open Finset MatchingFPRAS.Switching

variable {V E : Type*} [Fintype V] [LinearOrder V]

variable (edge : E → Sym2 V) (hnd : ∀ e, ¬(edge e).IsDiag)

local notation "inc" => (fun (e : E) (x : V) => x ∈ edge e)

omit [Fintype V] in
lemma edgeHigh_mem (s : Sym2 V) : edgeHigh s ∈ s := by
  induction s using Sym2.inductionOn with
  | hf x y => by_cases h : x≤y <;> simp [max_def,h]

variable (Q : Partial (fun (e : E) (x : V) => x ∈ edge e))

omit [Fintype V] in
lemma edgeLow_ne_high (s : Sym2 V) (hs : ¬s.IsDiag) : edgeLow s ≠ edgeHigh s :=
  (edgeLow_lt_high s hs).ne

lemma partial_weight (B : V → V → ℝ) :
    (∏ e ∈ Q.val, B (edgeLow (edge e)) (edgeHigh (edge e)))=weight B (partialMate edge hnd Q) := by
  classical
  unfold weight
  rw [←Finset.prod_filter]
  apply Finset.prod_bij (fun e _ => edgeLow (edge e))
    (partial_low_mem edge hnd Q) (partial_low_injective edge Q)
    (partial_low_surjective edge hnd Q)
  intro e he
  change B _ _ = B _ (partialMateFun edge Q _)
  rw [partialMate_low edge Q e he]

theorem partial_height_le_capacity (B : V → V → ℝ) (height : E → ℝ)
    (h0 : ∀ e, 0≤height e)
    (hh : ∀ e, height e ≤ B (edgeLow (edge e)) (edgeHigh (edge e))) :
    (∏ e ∈ Q.val, height e) ≤ pairingCapacity B (support inc Q.val) (partial_even edge hnd Q) := by
  calc
    _ ≤ ∏ e ∈ Q.val, B (edgeLow (edge e)) (edgeHigh (edge e)) :=
      Finset.prod_le_prod (fun e _ => h0 e) (fun e _ => hh e)
    _ = weight B (partialMate edge hnd Q) := partial_weight edge hnd Q B
    _ ≤ _ := Finset.le_sup' (f := weight B) ((mem_matchings _ _).mpr (partialMate_holes edge hnd Q))

end

section

open Finset

variable {V L : Type*} [Fintype V] [Fintype L] [LinearOrder V] [DecidableEq L]

variable (bags : V → Finset L)

lemma bag_color_card_le_two (hb : ∀ x,(bags x).card≤2) (s : {s : Sym2 V // ¬s.IsDiag}) :
    Fintype.card {l : L // ∀ x, x∈s.val → l∈bags x} ≤ 2 := by
  let f : {l : L // ∀ x, x∈s.val → l∈bags x} → {l : L // l∈bags (edgeLow s.val)} :=
    fun l => ⟨l.val,l.property _ (edgeLow_mem _)⟩
  have hi : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun z : {l : L // l∈bags (edgeLow s.val)} => z.val) h
  have := Fintype.card_le_of_injective f hi
  rw [Fintype.card_coe] at this
  exact this.trans (hb _)

attribute [local instance] OAI.MatchingFPRAS.Transport.edgeLowCardinalityBagEdgeFintype
theorem bagEdge_card_le_square (hb : ∀ x,(bags x).card≤2) :
    Fintype.card (BagEdge bags) ≤ (Fintype.card V)^2 := by
  classical
  rw [Fintype.card_congr (bagEdgeSigmaEquiv bags),Fintype.card_sigma]
  calc
    _ ≤ ∑ _s : {s : Sym2 V // ¬s.IsDiag}, 2 :=
      Finset.sum_le_sum (fun s _ => bag_color_card_le_two bags hb s)
    _ = 2*(Fintype.card V).choose 2 := by
      rw [Finset.sum_const,Finset.card_univ,smul_eq_mul,Sym2.card_subtype_not_diag,mul_comm]
    _ ≤ Fintype.card V*(Fintype.card V-1) := by rw [Nat.choose_two_right]; omega
    _ ≤ (Fintype.card V)^2 := by
      rw [pow_two]
      exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)

end

open Finset MatchingFPRAS.Switching

variable {V L : Type*} [Fintype V] [Fintype L] [LinearOrder V] [DecidableEq L]

variable (bags : V → Finset L)

attribute [local instance] OAI.MatchingFPRAS.Transport.edgeLowInflationBagEdgeFintype
theorem bag_inflation_of_hole_estimate (hN : 0<Fintype.card V)
    (hb : ∀ x,(bags x).card≤2) (B : V → V → ℝ)
    (height : L → ℝ) (hheight : ∀ l,0≤height l)
    (hcommon : ∀ e : BagEdge bags, height e.val.val.2 ≤ B (edgeLow e.val.val.1) (edgeHigh e.val.val.1))
    (r : BagEdge bags → ℝ) (hr : ∀ e,0 ≤ r e)
    (hz : 0<partitionWeight BagEdge.Incident r univ)
    (D₀ : ℝ) (hD₀ : 0<D₀)
    (hhole : ∀ U : Finset V, ∀ hU : Even U.card,
      partitionWeight BagEdge.Incident r (univ \ U) / partitionWeight BagEdge.Incident r univ *
        pairingCapacity B U hU ≤ 2*D₀^(U.card/2)) :
    let D := inflationScale (V := V) D₀
    1 ≤ partitionWeight BagEdge.Incident (fun e => r e+height e.val.val.2/D) univ /
      partitionWeight BagEdge.Incident r univ ∧
    partitionWeight BagEdge.Incident (fun e => r e+height e.val.val.2/D) univ /
      partitionWeight BagEdge.Incident r univ ≤ 2 := by
  classical
  let D := inflationScale (V := V) D₀
  have hNp : 0<(Fintype.card V:ℝ) := Nat.cast_pos.mpr hN
  have hD : 0<D := by dsimp [D,inflationScale]; positivity
  apply finite_inflation BagEdge.Incident r (fun e => height e.val.val.2/D) hr
    (fun e => div_nonneg (hheight _) hD.le)
    (fun e => ⟨edgeLow e.val.val.1,edgeLow_mem _⟩) hz (D₀/D) (div_nonneg hD₀.le hD.le)
  · have hcard : (Fintype.card (BagEdge bags):ℝ) ≤ (Fintype.card V:ℝ)^2 := by
      exact_mod_cast bagEdge_card_le_square bags hb
    rw [←mul_div_assoc]
    apply (div_le_iff₀ hD).mpr
    change (Fintype.card (BagEdge bags):ℝ)*D₀ ≤ 1/100*D
    dsimp [D,inflationScale]
    nlinarith [mul_le_mul_of_nonneg_right hcard hD₀.le]
  · intro Q _
    let edge : BagEdge bags → Sym2 V := fun e => e.val.val.1
    have hnd : ∀ e,¬(edge e).IsDiag := fun e => e.val.property
    have heven := partial_even edge hnd Q
    let g := partitionWeight BagEdge.Incident r (univ \ support BagEdge.Incident Q.val) /
      partitionWeight BagEdge.Incident r univ
    have hg : 0≤g := div_nonneg (partitionWeight_nonneg _ r hr _) hz.le
    have hc := partial_height_le_capacity edge hnd Q B (fun e => height e.val.val.2)
      (fun e => hheight _) hcommon
    have hh := hhole _ heven
    have hcard := partial_card edge hnd Q
    change (support BagEdge.Incident Q.val).card=2*Q.val.card at hcard
    change g * pairingCapacity B (support BagEdge.Incident Q.val) heven ≤ 2*D₀^((support BagEdge.Incident Q.val).card/2) at hh
    have hpow : (support BagEdge.Incident Q.val).card/2=Q.val.card := by omega
    rw [hpow] at hh
    rw [Finset.prod_div_distrib,Finset.prod_const]
    change (∏ e∈Q.val,height e.val.val.2) / D^Q.val.card *
      partitionWeight BagEdge.Incident r (univ \ support BagEdge.Incident Q.val) /
      partitionWeight BagEdge.Incident r univ ≤ _
    calc
      _ = g*(∏ e∈Q.val,height e.val.val.2) / D^Q.val.card := by dsimp [g]; ring
      _ ≤ g*pairingCapacity B (support BagEdge.Incident Q.val) heven / D^Q.val.card :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hc hg) (pow_nonneg hD.le _)
      _ ≤ (2*D₀^Q.val.card)/D^Q.val.card := div_le_div_of_nonneg_right hh (pow_nonneg hD.le _)
      _ = 2*(D₀/D)^Q.val.card := by rw [div_pow]; ring

end MatchingFPRAS.Transport

namespace MatchingFPRAS.RealGeometry

open Finset MatchingFPRAS.Subdivision MatchingFPRAS.Transport

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

variable (u v : E → V) (m : ℕ)

omit [DecidableEq E] in
lemma selectedSet_weight (w : E → Fin (m+1) → ℝ) (b : E → Selection m) :
    (∏ q ∈ selectedSet m b,w q.1 q.2)=∏ e,selectedWeight (w e) (b e) := by
  classical
  simp only [selectedSet,Finset.prod_filter,selectedWeight,Fintype.prod_prod_type]

omit [DecidableEq V] in
theorem realMatching_partition (huv : ∀ e,u e≠v e) (R : Finset V) (U : E → Finset (Fin m))
    (w : E → Fin (m+1) → ℝ) :
    partitionWeight (fun (q : E × Fin (m+1)) x => x∈edge u v m q.1 q.2) (fun q => w q.1 q.2) (survivors m R U)=
      realHolePartition u v m R U w := by
  classical
  let := Fintype.ofFinite {b : E → Selection m // FamilyHoles u v m R U b}
  unfold partitionWeight realHolePartition
  rw [←(realMatchingEquiv u v m huv R U).sum_comp]
  apply Finset.sum_congr rfl
  intro b _
  exact selectedSet_weight m w b.val

end MatchingFPRAS.RealGeometry

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_MatchingMap
attribute [-instance] _root_.OAI.MatchingFPRAS.Transport.Sparse.decideMatching _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.allowedDec _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.edgeDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

open Finset

variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]

variable [DecidableEq V] [DecidableEq E] [DecidableEq F]

variable (inc : E → V → Prop) (inc' : F → V → Prop) (f : E ↪ F)

variable (hinc : ∀ e x,inc' (f e) x ↔ inc e x)

lemma matchingMap_injective (U : Finset V) : Function.Injective (matchingMap inc inc' f hinc U) := by
  intro a b h
  apply Subtype.ext
  exact Finset.map_injective f (congrArg Subtype.val h)

omit [Fintype F] [DecidableEq E] in
lemma edgeExtension_on [Fintype F] [DecidableEq E] (w : E → ℝ) (e : E) : edgeExtension f w (f e)=w e := by
  classical
  unfold edgeExtension
  rw [dite_eq_left ⟨e,rfl⟩]
  exact congrArg w (f.injective (Exists.choose_spec (show ∃ e',f e'=f e from ⟨e,rfl⟩)))

omit [Fintype F] [DecidableEq E] in
lemma edgeExtension_off [Fintype F] [DecidableEq E] (w : E → ℝ) (q : F) (hq : ¬∃ e,f e=q) : edgeExtension f w q=0 := by
  classical
  simp [edgeExtension,hq]

omit [Fintype F] [DecidableEq E] in
lemma edgeExtension_nonneg [Fintype F] [DecidableEq E] (w : E → ℝ) (hw : ∀ e,0≤w e) (q : F) : 0≤edgeExtension f w q := by
  classical
  unfold edgeExtension
  split_ifs <;> first | exact hw _ | norm_num

lemma matchingMap_weight (w : E → ℝ) (U : Finset V) (M : Matchings inc U) :
    (∏ q∈(matchingMap inc inc' f hinc U M).val,edgeExtension f w q)=∏ e∈M.val,w e := by
  dsimp [matchingMap]
  rw [Finset.prod_map]
  simp_rw [edgeExtension_on]

include hinc in

theorem partition_embedding (w : E → ℝ) (U : Finset V) :
    partitionWeight inc' (edgeExtension f w) U=partitionWeight inc w U := by
  classical
  unfold partitionWeight
  symm
  apply Finset.sum_bij_ne_zero (fun M _ _ => matchingMap inc inc' f hinc U M)
  · intros; exact Finset.mem_univ _
  · intro a _ _ b _ _ h
    exact matchingMap_injective inc inc' f hinc U h
  · intro N _ hN
    have hr : ∀ q∈N.val,∃ e,f e=q := by
      intro q hq
      by_contra hn
      apply hN
      exact Finset.prod_eq_zero hq (edgeExtension_off f w q hn)
    let S := univ.filter fun e : E => f e∈N.val
    have hS : S.map f=N.val := by
      ext q
      constructor
      · intro hq
        obtain ⟨e,he,rfl⟩ := Finset.mem_map.mp hq
        exact (Finset.mem_filter.mp he).2
      · intro hq
        obtain ⟨e,rfl⟩ := hr q hq
        exact Finset.mem_map.mpr ⟨e,by simp [S,hq],rfl⟩
    let M : Matchings inc U := ⟨S,(matching_map_iff inc inc' f hinc S U).mp (hS.symm ▸ N.property)⟩
    have hM : matchingMap inc inc' f hinc U M=N := Subtype.ext hS
    refine ⟨M,Finset.mem_univ _,?_,hM⟩
    rw [←matchingMap_weight inc inc' f hinc w U M,hM]
    exact hN
  · intro M _ _
    exact (matchingMap_weight inc inc' f hinc w U M).symm

end MatchingFPRAS.Transport

namespace MatchingFPRAS.Enlargement

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport Finset

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

attribute [local instance] OAI.MatchingFPRAS.Enlargement.instDecidableEqSourceLabel
attribute [local instance] OAI.MatchingFPRAS.Enlargement.instFintypeBagEdgeSourceVertexSourceLabelSourceBags
lemma sourceRealPortion_partition (w : V → V → ℝ) (K : ℕ)
    (R : Finset V) (U : LogicalEdge V → Finset (Fin (4*(2*K+2)))) :
    partitionWeight BagEdge.Incident (sourceRealPortion w K) (survivors (4*(2*K+2)) R U)=
    realHolePartition source target (4*(2*K+2)) R U
      (pathActivity (2*K+2) (fun e => bottleneck w (source e) (target e))
        (fun e => sourceHeight w (source e)) (fun e => sourceHeight w (target e)) (logicalActivity w)) := by
  classical
  rw [show sourceRealPortion w K=edgeExtension (sourceRealEmbedding w K) (sourceRealActivity w K) from rfl]
  rw [partition_embedding (fun (q : SourceRealEdge V K) x => x∈edge source target (4*(2*K+2)) q.1 q.2)
    BagEdge.Incident (sourceRealEmbedding w K) (fun _ _ => Iff.rfl)]
  exact realMatching_partition source target (4*(2*K+2)) source_ne_target R U _

omit [Nontrivial V] in
lemma hole_decomposition [Nontrivial V] (K : ℕ) (H : Finset (SourceVertex V K)) :
    enlargedHoles (4*(2*K+2)) (holeTerminals K H) (holeInternals K H)=H := by
  ext x
  cases x with
  | inl x => simp [holeTerminals]
  | inr ei => rcases ei with ⟨e,i⟩; simp [holeInternals]

omit [Nontrivial V] in
lemma survivors_decomposition [Nontrivial V] (K : ℕ) (H : Finset (SourceVertex V K)) :
    survivors (4*(2*K+2)) (holeTerminals K H) (holeInternals K H)=univ \ H := by
  ext x
  cases x with
  | inl x => simp [holeTerminals]
  | inr ei => rcases ei with ⟨e,i⟩; simp [holeInternals]

lemma sourceRealActivity_pos (w : V → V → ℝ) (hw : ∀ x y,0<w x y) (K : ℕ)
    (e : SourceRealEdge V K) : 0 < sourceRealActivity w K e := by
  have hl : 0<logicalActivity w e.1 := by
    unfold logicalActivity edgeActivity
    split_ifs <;> exact hw _ _
  exact hl.trans_le (profile_lower _ _ _ _ _
    (edgeActivity_le_bottleneck w _ _ (source_ne_target e.1)) e.2)

lemma sourceRealPortion_nonneg (w : V → V → ℝ) (hw : ∀ x y,0<w x y) (K : ℕ)
    (e : BagEdge (sourceBags w K)) : 0 ≤ sourceRealPortion w K e := by
  classical
  exact edgeExtension_nonneg _ _ (fun q => (sourceRealActivity_pos w hw K q).le) e

lemma sourceRealPortion_full (w : V → V → ℝ) (hz : 0<partition w ∅) (K : ℕ) :
    partitionWeight BagEdge.Incident (sourceRealPortion w K) univ =
      (∏ e, pathConstant (2*K+2) (bottleneck w (source e) (target e))
        (sourceHeight w (source e)) (sourceHeight w (target e))) * partition w ∅ := by
  rw [←survivors_empty (V := V) K,sourceRealPortion_partition]
  exact intact_partition_identity w hz _ _ _ _

lemma sourceRealPortion_full_pos (w : V → V → ℝ) (hz : 0<partition w ∅) (K : ℕ) :
    0<partitionWeight BagEdge.Incident (sourceRealPortion w K) univ := by
  rw [sourceRealPortion_full w hz K]
  apply mul_pos _ hz
  exact Finset.prod_pos fun e _ => pathConstant_pos _ _ _ _
    (zero_lt_one.trans_le (one_le_bottleneck w _ _))

lemma sourceRealPortion_hole_bound (hn : 2≤Fintype.card V)
    (w : V → V → ℝ) (hw : ∀ x y,0<w x y) (hz : 0<partition w ∅)
    (hrlo : ∀ x,(1:ℝ)/4 ≤ rowMax hn w x) (hrhi : ∀ x,rowMax hn w x≤1)
    (K : ℕ) (H : Finset (SourceVertex V K)) (hH : Even H.card) :
    partitionWeight BagEdge.Incident (sourceRealPortion w K) (univ \ H) /
      partitionWeight BagEdge.Incident (sourceRealPortion w K) univ *
      pairingCapacity (sourceRealB w K) H hH ≤ 2*holeScale V^(H.card/2) := by
  have heven : Even (enlargedHoles (4*(2*K+2)) (holeTerminals K H) (holeInternals K H)).card :=
    (hole_decomposition K H).symm ▸ hH
  have ht := lifted_hole_bound hn w hw hz hrlo hrhi (2*K+2) (by omega)
    (fun e => sourceHeight w (source e)) (fun e => sourceHeight w (target e))
    (fun e => sourceHeight_nonneg w _) (fun e => sourceHeight_nonneg w _)
    (holeTerminals K H) (holeInternals K H) heven
  rw [←sourceRealPortion_partition w K,←sourceRealPortion_partition w K,
    survivors_empty,survivors_decomposition] at ht
  simpa only [hole_decomposition, sourceRealB] using ht

theorem source_bag_inflation (hn : 2≤Fintype.card V)
    (w : V → V → ℝ) (hw : ∀ x y,0<w x y) (hz : 0<partition w ∅)
    (hrlo : ∀ x,(1:ℝ)/4 ≤ rowMax hn w x) (hrhi : ∀ x,rowMax hn w x≤1)
    (K : ℕ) (hK : ∀ x y,x≠y → edgeActivity w x y≤(4:ℝ)^K) :
    let D := inflationScale (V := SourceVertex V K) (holeScale V)
    let realZ := partitionWeight BagEdge.Incident (sourceRealPortion w K) univ
    let bagZ := partitionWeight BagEdge.Incident
      (fun e => sourceRealPortion w K e+(2:ℝ)^e.val.val.2.1.val/D) univ
    1≤bagZ/realZ ∧ bagZ/realZ≤2 := by
  classical
  apply bag_inflation_of_hole_estimate (sourceBags w K) (Fintype.card_pos)
    (sourceBag_card_le_two w K hK) (sourceRealB w K)
    (fun l => (2:ℝ)^l.1.val) (fun _ => by positivity)
  · intro e
    apply sourceBag_height w K (edgeLow_ne_high e.val.val.1 e.val.property)
    · exact e.property _ (edgeLow_mem _)
    · exact e.property _ (edgeHigh_mem _)
  · exact sourceRealPortion_nonneg w hw K
  · exact sourceRealPortion_full_pos w hz K
  · exact holeScale_pos
  · intro H hH
    convert sourceRealPortion_hole_bound hn w hw hz hrlo hrhi K H hH using 1
    all_goals try with_reducible_and_instances rfl
    congr 3
    ext x
    simp



open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport Finset

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

noncomputable local instance instDecidableEqSourceLabel_1_r2631ec_1 (w : V → V → ℝ) (K : ℕ) : DecidableEq (SourceLabel w K) := Classical.decEq _
lemma bagHeight_one (w : V → V → ℝ) (K : ℕ) (l : SourceLabel w K) : 1 ≤ bagHeight w K l := by
  exact one_le_pow₀ (by norm_num)

lemma bagHeight_pos (w : V → V → ℝ) (K : ℕ) (l : SourceLabel w K) : 0 < bagHeight w K l :=
  zero_lt_one.trans_le (bagHeight_one w K l)

omit [Nontrivial V] in
lemma sourceD_cast [Nontrivial V] (K : ℕ) :
    (sourceD (V:=V) K:ℝ)=inflationScale (V:=SourceVertex V K) (holeScale V) := by
  simp only [sourceD,inflationScale,holeScale,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]

end MatchingFPRAS.Enlargement

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_PM
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Subdivision

open Finset

lemma probeWord_valid (p : ℕ) (hp : 1≤p) : Valid (probeHoles p hp) (probeWord p) := by
  intro i
  by_cases h : i.val=2*p-1 ∨ i.val=2*p
  · have hm : i∈probeHoles p hp := by simpa [probeHoles,Fin.ext_iff] using h
    rw [ite_eq_left hm]
    rcases h with h | h
    · have _hm : i.val%2=1 := by omega
      simp [probeWord,Fin.val_castSucc,Fin.val_succ,h,show 2*p-1+1=2*p by omega,
        alternating,show (2*p-1)%2=1 by omega,show 2*p-1≠2*p by omega]
    · simp [probeWord,Fin.val_castSucc,Fin.val_succ,h,alternating,Nat.add_mod]
  · have hm : i∉probeHoles p hp := by simpa [probeHoles,Fin.ext_iff] using h
    rw [ite_eq_right hm]
    have h₁ : i.val≠2*p := by omega
    have h₂ : i.val+1≠2*p := by omega
    simp only [probeWord,Fin.val_castSucc,Fin.val_succ,ite_eq_right h₁,ite_eq_right h₂,alternating_succ]
    cases alternating true i.val <;> decide

lemma probeHoles_nonempty (p : ℕ) (hp : 1≤p) : (probeHoles p hp).Nonempty := by
  simp [probeHoles]

lemma probeWord_unique (p : ℕ) (hp : 1≤p) (b : Selection (4*p))
    (hb : Valid (probeHoles p hp) b) : b=probeWord p :=
  broken_unique (probeHoles_nonempty p hp) hb (probeWord_valid p hp)

lemma probe_weight (p : ℕ) (B Hu Hv lam : ℝ) :
    selectedWeight (profileActivity p B Hu Hv lam) (probeWord p)=
      (∏ r : Fin p,max B (Hu/2^r.val))*(∏ r : Fin p,max B (Hv/2^r.val)) := by
  have he : selectedWeight (profileActivity p B Hu Hv lam) (probeWord p)=
      selectedWeight (profileActivity p B Hu Hv 1) (fun i => alternating true i.val) := by
    unfold selectedWeight
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i.val=2*p
    · have hfi : i=⟨2*p,by omega⟩ := Fin.ext hi
      rw [hfi]
      simp [probeWord,alternating]
    · simp only [probeWord,ite_eq_right hi]
      congr 1
      rcases lt_or_gt_of_ne hi with h | h
      · rw [profile_left _ _ _ _ _ _ h,profile_left _ _ _ _ _ _ h]
      · rw [profile_right _ _ _ _ _ _ h,profile_right _ _ _ _ _ _ h]
  rw [he,exact_profile_weight]
  simp


variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

variable (u v : E → V) (p : ℕ) (hp : 1≤p) (e₀ : E)

@[simp] lemma broken_singleProbe : broken (singleProbeHoles p hp e₀)={e₀} := by
  ext e
  by_cases he : e=e₀ <;> simp [singleProbeHoles,he,probeHoles_nonempty]

omit [Fintype V] [Fintype E] [DecidableEq V] in
lemma singleProbe_word (b : E → Selection (4*p))
    (hb : FamilyHoles u v (4*p) ∅ (singleProbeHoles p hp e₀) b) : b e₀=probeWord p := by
  exact probeWord_unique p hp (b e₀) (by simpa [singleProbeHoles] using hb.1 e₀)

lemma residual_singleProbe (b : E → Selection (4*p))
    (hb : FamilyHoles u v (4*p) ∅ (singleProbeHoles p hp e₀) b) :
    residualHoles u v ∅ (singleProbeHoles p hp e₀) b={u e₀,v e₀} := by
  ext x
  simp only [mem_residualHoles,notMem_empty,broken_singleProbe,mem_singleton,
    exists_eq_left,false_or,Uses,singleProbe_word u v p hp e₀ b hb,
    probeWord_first p hp,probeWord_last p hp,true_and,mem_insert,mem_singleton]
  exact or_congr eq_comm eq_comm

include hp in
omit [Fintype V] [Fintype E] [DecidableEq V] in
lemma insertProbe_uses (s : E → Bool) (e : E) (x : V) :
    Uses u v (insertProbe p e₀ s) e x ↔
      if e=e₀ then u e₀=x ∨ v e₀=x else s e=true ∧ (u e=x ∨ v e=x) := by
  by_cases he : e=e₀
  · subst e; simp [Uses,insertProbe,probeWord_first p hp,probeWord_last p hp]
  · simp [Uses,insertProbe,he,alternating,and_or_left,Nat.mul_mod]

omit [Fintype V] [Fintype E] in
lemma insertProbe_family (_hne : u e₀≠v e₀) (s : E → Bool)
    (hs : LogicalHoles u v {u e₀,v e₀} {e₀} s) :
    FamilyHoles u v (4*p) ∅ (singleProbeHoles p hp e₀) (insertProbe p e₀ s) := by
  refine ⟨?_,by simp,?_⟩
  · intro e
    by_cases he : e=e₀
    · subst e; simpa [singleProbeHoles,insertProbe] using probeWord_valid p hp
    · simpa [singleProbeHoles,insertProbe,he] using alternating_valid (4*p) (s e)
  · intro x _
    by_cases hx : x∈({u e₀,v e₀} : Finset V)
    · refine ⟨e₀,?_,?_⟩
      · change Uses u v (insertProbe p e₀ s) e₀ x
        rw [insertProbe_uses u v p hp e₀,ite_eq_left rfl]
        simpa only [mem_insert,mem_singleton,eq_comm] using hx
      · intro e he
        by_contra hen
        rw [insertProbe_uses u v p hp e₀,ite_eq_right hen] at he
        exact hs.2.1 x hx e he
    · obtain ⟨e,he,hu⟩ := hs.2.2 x hx
      have he₀ : e≠e₀ := by
        intro h
        subst e
        exact (Bool.noConfusion (he.1.symm.trans (hs.1 e₀ (mem_singleton_self _))))
      refine ⟨e,(insertProbe_uses u v p hp e₀ s e x).mpr (by simpa [he₀] using he),?_⟩
      intro f hf
      by_cases hf₀ : f=e₀
      · subst f
        rw [insertProbe_uses u v p hp e₀,ite_eq_left rfl] at hf
        exact False.elim (hx (by simpa only [mem_insert,mem_singleton,eq_comm] using hf))
      · rw [insertProbe_uses u v p hp e₀,ite_eq_right hf₀] at hf
        exact hu f hf

omit [Fintype V] [DecidableEq V] in
lemma singleProbe_deletionConstant (b : E → Selection (4*p))
    (hb : FamilyHoles u v (4*p) ∅ (singleProbeHoles p hp e₀) b)
    (B Hu Hv lam : E → ℝ) :
    deletionConstant (singleProbeHoles p hp e₀) b
      (fun e => profileActivity p (B e) (Hu e) (Hv e) (lam e))
      (fun e => (∏ r : Fin p,max (B e) (Hu e/2^r.val))*(∏ r : Fin p,max (B e) (Hv e/2^r.val))) =
    ∏ e,(∏ r : Fin p,max (B e) (Hu e/2^r.val))*(∏ r : Fin p,max (B e) (Hv e/2^r.val)) := by
  unfold deletionConstant
  apply Finset.prod_congr rfl
  intro e _
  by_cases he : e=e₀
  · subst e
    simp only [singleProbeHoles,probeHoles_nonempty,ite_true,
      singleProbe_word u v p hp e₀ b hb,probe_weight]
  · simp [singleProbeHoles,he]

theorem singleProbe_partition (hne : u e₀≠v e₀) (B Hu Hv lam : E → ℝ) :
    realHolePartition u v (4*p) ∅ (singleProbeHoles p hp e₀)
      (fun e => profileActivity p (B e) (Hu e) (Hv e) (lam e)) =
    (∏ e,(∏ r : Fin p,max (B e) (Hu e/2^r.val))*(∏ r : Fin p,max (B e) (Hv e/2^r.val))) *
      logicalHolePartition u v {u e₀,v e₀} {e₀} lam := by
  classical
  by_cases h : ∃ b,FamilyHoles u v (4*p) ∅ (singleProbeHoles p hp e₀) b
  · obtain ⟨b,hb⟩ := h
    have hid := deletion_partition_identity (show Even (4*p) from ⟨2*p,by omega⟩)
      u v ∅ (singleProbeHoles p hp e₀) b hb
      (fun e => profileActivity p (B e) (Hu e) (Hv e) (lam e))
      (fun e => List.ofFn fun r : Fin p => max (B e) (Hu e/2^r.val))
      (fun e => (List.ofFn fun r : Fin p => max (B e) (Hv e/2^r.val)).reverse) lam
      (fun e => profileActivity_ofFn p (B e) (Hu e) (Hv e) (lam e))
    simp only [List.prod_reverse,List.prod_ofFn] at hid
    rw [singleProbe_deletionConstant u v p hp e₀ b hb,residual_singleProbe u v p hp e₀ b hb,
      broken_singleProbe] at hid
    exact hid
  · have hl : ¬∃ s,LogicalHoles u v {u e₀,v e₀} {e₀} s := by
      rintro ⟨s,hs⟩
      exact h ⟨insertProbe p e₀ s,insertProbe_family u v p hp e₀ hne s hs⟩
    have hz : realHolePartition u v (4*p) ∅ (singleProbeHoles p hp e₀)
        (fun e => profileActivity p (B e) (Hu e) (Hv e) (lam e))=0 := by
      unfold realHolePartition
      apply Finset.sum_eq_zero
      intro b _
      exact False.elim (h ⟨b.val,b.property⟩)
    have hz' : logicalHolePartition u v {u e₀,v e₀} {e₀} lam=0 := by
      unfold logicalHolePartition
      apply Finset.sum_eq_zero
      intro s _
      exact False.elim (hl ⟨s.val,s.property⟩)
    rw [hz,hz',mul_zero]


end MatchingFPRAS.Subdivision

namespace MatchingFPRAS.Representation

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.Enlargement Finset

variable {V : Type*} [Fintype V] [LinearOrder V]

omit [Fintype V] in
lemma forbidden_endpoint_redundant (R : Finset V) (e₀ : LogicalEdge V)
    (he : source e₀∈R) (s : LogicalEdge V → Bool) :
    LogicalHoles source target R {e₀} s ↔ LogicalHoles source target R ∅ s := by
  constructor
  · intro h; exact ⟨by simp,h.2⟩
  · intro h
    refine ⟨?_,h.2⟩
    intro e hem
    have heq : e=e₀ := mem_singleton.mp hem
    subst e
    cases hs : s e₀ with
    | false => rfl
    | true => exact False.elim (h.2.1 (source e₀) he e₀ ⟨hs,Or.inl rfl⟩)

lemma logical_partition_redundant (w : V → V → ℝ) (R : Finset V) (e₀ : LogicalEdge V)
    (he : source e₀∈R) :
    logicalHolePartition source target R {e₀} (logicalActivity w)=partition w R := by
  classical
  let := Fintype.ofFinite {s : LogicalEdge V → Bool // LogicalHoles source target R {e₀} s}
  let := Fintype.ofFinite {s : LogicalEdge V → Bool // LogicalHoles source target R ∅ s}
  rw [← logical_partition_eq]
  unfold logicalHolePartition
  apply Fintype.sum_equiv (Equiv.subtypeEquivRight (forbidden_endpoint_redundant R e₀ he))
  intro s
  rfl

end MatchingFPRAS.Representation

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Marked
attribute [-instance] _root_.OAI.MatchingFPRAS.Transport.Sparse.decideMatching _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.allowedDec _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.edgeDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Marking

open Finset MatchingFPRAS.Transport

variable {V E I : Type*} [Fintype V] [Fintype E] [Fintype I]

variable [DecidableEq V] [DecidableEq E] [DecidableEq I]

variable (inc : E → V → Prop)

omit [Fintype E] [DecidableEq V] [DecidableEq I] in
lemma sum_marks (part : E → I → ℝ) (M : Matchings inc univ) :
    (∑ m : (↥M.val → I),mass inc part ⟨M,m⟩)=∏ e ∈ M.val,collapse part e := by
  classical
  rw [Finset.prod_subtype M.val (fun _ => Iff.rfl)]
  exact (Fintype.prod_sum (fun e : M.val => part e.val)).symm

omit [DecidableEq V] [DecidableEq I] in
theorem total_mass (part : E → I → ℝ) :
    (∑ a : Marked (I:=I) inc,mass inc part a)=partitionWeight inc (collapse part) univ := by
  rw [Fintype.sum_sigma]
  exact Finset.sum_congr rfl fun M _ => sum_marks inc part M

omit [Fintype E] [Fintype I] [DecidableEq V] [DecidableEq E] [DecidableEq I] in
lemma mass_nonneg (part : E → I → ℝ) (hp : ∀ e i,0 ≤ part e i) (a : Marked (I:=I) inc) :
    0 ≤ mass inc part a := Finset.prod_nonneg fun _ _ => hp _ _

omit [DecidableEq V] [DecidableEq I] in
lemma law_sum (part : E → I → ℝ) (hz : partitionWeight inc (collapse part) univ ≠ 0) :
    ∑ a : Marked (I:=I) inc,law inc part a=1 := by
  simp only [law,←Finset.sum_div,total_mass,div_self hz]

omit [DecidableEq V] in
lemma pattern_sum (part : E → I → ℝ)
    (pattern : (M : Matchings inc univ) → ↥M.val → I)
    (u : Matchings inc univ → ℝ) :
    (∑ a : Marked (I:=I) inc, if a.2=pattern a.1 then mass inc part a*u a.1 else 0)=
      ∑ M : Matchings inc univ,(∏ e : M.val,part e.val (pattern M e))*u M := by
  classical
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro M _
  simp only [Finset.sum_ite_eq',mem_univ,ite_true,mass]

omit [DecidableEq V] in
lemma allReal_mean (part : E → I → ℝ) (real : I) (u : E → ℝ) :
    (∑ a : Marked (I:=I) inc,law inc part a *
      (if a.2=(fun _ => real) then ∏ e ∈ a.1.val,u e else 0))=
    partitionWeight inc (fun e => part e real*u e) univ /
      partitionWeight inc (collapse part) univ := by
  classical
  calc
    _ = (∑ a : Marked (I:=I) inc,
        if a.2=(fun _ => real) then mass inc part a*(∏ e ∈ a.1.val,u e) else 0) /
        partitionWeight inc (collapse part) univ := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp only [law,mul_zero,zero_div,div_mul_eq_mul_div]
    _ = _ := by
      congr 1
      rw [pattern_sum inc part (fun _ _ => real) (fun M => ∏ e ∈ M.val,u e)]
      unfold partitionWeight
      apply Finset.sum_congr rfl
      intro M _
      rw [←Finset.prod_subtype M.val (fun _ => Iff.rfl) (fun e => part e real),
        ←Finset.prod_mul_distrib]

lemma completion_sum (hinc : ∀ e,∃ x,inc e x) (Q : Partial inc) (r : E → ℝ) :
    (∑ M : {M : Matchings inc univ // Q.val⊆M.val},∏ e ∈ M.val.val \ Q.val,r e)=
      partitionWeight inc r (univ \ support inc Q.val) := by
  exact Fintype.sum_equiv (completionEquiv inc hinc Q) _ _ (fun _ => rfl)

omit [DecidableEq V] [DecidableEq E] [DecidableEq I] in
lemma law_from_reveal (part : E → I → ℝ) (hc : ∀ e,collapse part e≠0)
    (a : Marked (I:=I) inc) :
    ((∏ e ∈ a.1.val,collapse part e)/partitionWeight inc (collapse part) univ) *
      conditional inc part a.1 a.2 = law inc part a := by
  classical
  rw [conditional,Finset.prod_div_distrib,←Finset.prod_subtype a.1.val (fun _ => Iff.rfl)]
  have hn : (∏ e ∈ a.1.val,collapse part e)≠0 := Finset.prod_ne_zero_iff.mpr (fun e _ => hc e)
  unfold law mass
  field_simp

omit [Fintype E] [Fintype I] [DecidableEq V] [DecidableEq I] in
lemma fixed_pattern_mass (part : E → I → ℝ) (real probe : I)
    (Q : Finset E) (M : Matchings inc univ) (hQ : Q⊆M.val) :
    (∏ e : M.val,part e.val (if e.val∈Q then probe else real))=
      (∏ e ∈ Q,part e probe)*(∏ e ∈ M.val \ Q,part e real) := by
  classical
  rw [←Finset.prod_subtype M.val (fun _ => Iff.rfl)
    (fun e : E => part e (if e∈Q then probe else real))]
  calc
    _ = (∏ e ∈ Q,part e (if e∈Q then probe else real))*
        (∏ e ∈ M.val \ Q,part e (if e∈Q then probe else real)) := by
      rw [←Finset.prod_union (Finset.disjoint_left.mpr (fun e he hf => (Finset.mem_sdiff.mp hf).2 he)),Finset.union_sdiff_of_subset hQ]
    _ = _ := by
      congr 1
      · apply Finset.prod_congr rfl; intro e he; simp only [ite_eq_left he]
      · apply Finset.prod_congr rfl; intro e he; simp only [ite_eq_right (mem_sdiff.mp he).2]

lemma sum_if_subtype {A : Type*} [Fintype A] (P : A → Prop) [DecidablePred P]
    (f : A → ℝ) :
    (∑ a,if P a then f a else 0)=∑ a : {a // P a},f a.val := by
  classical
  rw [←Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) f

omit [Fintype I] [DecidableEq I] in
lemma fixed_pattern_sum (hinc : ∀ e,∃ x,inc e x)
    (part : E → I → ℝ) (real probe : I) (Q : Partial inc) (u : E → ℝ) :
    (∑ M : Matchings inc univ,
      (∏ e : M.val,part e.val (if e.val∈Q.val then probe else real))*
      (if Q.val⊆M.val then ∏ e ∈ M.val \ Q.val,u e else 0))=
    (∏ e ∈ Q.val,part e probe)*partitionWeight inc (fun e => part e real*u e)
      (univ \ support inc Q.val) := by
  classical
  have he (M : Matchings inc univ) :
      (∏ e : M.val,part e.val (if e.val∈Q.val then probe else real))*
      (if Q.val⊆M.val then ∏ e ∈ M.val \ Q.val,u e else 0)=
      (∏ e ∈ Q.val,part e probe)*
        (if Q.val⊆M.val then ∏ e ∈ M.val \ Q.val,part e real*u e else 0) := by
    by_cases hs : Q.val⊆M.val
    · simp only [ite_eq_left hs,fixed_pattern_mass inc part real probe Q.val M hs]
      rw [mul_assoc,←Finset.prod_mul_distrib]
    · simp only [ite_eq_right hs,mul_zero]
  simp_rw [he]
  rw [←Finset.mul_sum,sum_if_subtype]
  rw [completion_sum inc hinc Q]

theorem fixed_probe_mean (hinc : ∀ e,∃ x,inc e x)
    (part : E → I → ℝ) (real probe : I) (Q : Partial inc) (u : E → ℝ) :
    (∑ a : Marked (I:=I) inc,law inc part a *
      (if Q.val⊆a.1.val ∧ a.2=(fun e => if e.val∈Q.val then probe else real)
        then ∏ e ∈ a.1.val \ Q.val,u e else 0))=
    ((∏ e ∈ Q.val,part e probe)*partitionWeight inc (fun e => part e real*u e)
      (univ \ support inc Q.val))/partitionWeight inc (collapse part) univ := by
  classical
  calc
    _ = (∑ a : Marked (I:=I) inc,
        if a.2=(fun e => if e.val∈Q.val then probe else real) then
          mass inc part a*(if Q.val⊆a.1.val then ∏ e ∈ a.1.val \ Q.val,u e else 0)
        else 0)/partitionWeight inc (collapse part) univ := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a _
      by_cases hQ : Q.val⊆a.1.val <;>
        by_cases hm : a.2=(fun e => if e.val∈Q.val then probe else real) <;>
        simp only [hQ,hm,and_true,and_false,ite_true,ite_false,
          law,mul_zero,zero_div,div_mul_eq_mul_div]
    _ = _ := by
      congr 1
      rw [pattern_sum inc part (fun M e => if e.val∈Q.val then probe else real)
        (fun M => if Q.val⊆M.val then ∏ e ∈ M.val \ Q.val,u e else 0)]
      exact fixed_pattern_sum inc hinc part real probe Q u

end MatchingFPRAS.Marking

namespace MatchingFPRAS.Enlargement

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport MatchingFPRAS.Representation Finset

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

attribute [local instance] OAI.MatchingFPRAS.Enlargement.instDecidableEqSourceLabel_3
lemma sourceC_pos (w : V → V → ℝ) (K : ℕ) : 0 < sourceC w K := by
  exact Finset.prod_pos fun e _ => pathConstant_pos _ _ _ _
    (zero_lt_one.trans_le (one_le_bottleneck _ _ _))

attribute [local instance] OAI.MatchingFPRAS.Enlargement.instFintypeBagEdgeSourceVertexSourceLabelSourceBags_4
lemma frozenPortion_partition (w w₁ : V → V → ℝ) (K : ℕ)
    (R : Finset V) (U : LogicalEdge V → Finset (Fin (4*(2*K+2)))) :
    partitionWeight BagEdge.Incident (frozenPortion w w₁ K) (survivors (4*(2*K+2)) R U)=
    realHolePartition source target (4*(2*K+2)) R U
      (pathActivity (2*K+2) (fun e => bottleneck w (source e) (target e))
        (fun e => sourceHeight w (source e)) (fun e => sourceHeight w (target e)) (logicalActivity w₁)) := by
  classical
  rw [show frozenPortion w w₁ K=edgeExtension (sourceRealEmbedding w K) (frozenActivity w w₁ K) from rfl]
  rw [partition_embedding (fun (q : SourceRealEdge V K) x => x∈edge source target (4*(2*K+2)) q.1 q.2)
    BagEdge.Incident (sourceRealEmbedding w K) (fun _ _ => Iff.rfl)]
  exact realMatching_partition source target (4*(2*K+2)) source_ne_target R U _

lemma frozenPortion_full (w w₁ : V → V → ℝ) (hz : 0 < partition w₁ ∅) (K : ℕ) :
    partitionWeight BagEdge.Incident (frozenPortion w w₁ K) univ=sourceC w K*partition w₁ ∅ := by
  rw [←survivors_empty (V:=V) K,frozenPortion_partition,intact_partition_identity w₁ hz]
  rfl

lemma frozenPortion_probe (w w₁ : V → V → ℝ) (K : ℕ) (e₀ : LogicalEdge V) :
    partitionWeight BagEdge.Incident (frozenPortion w w₁ K)
      (survivors (4*(2*K+2)) ∅ (singleProbeHoles (2*K+2) (by omega) e₀))=
    sourceC w K*partition w₁ {source e₀,target e₀} := by
  rw [frozenPortion_partition]
  change realHolePartition source target (4*(2*K+2)) ∅
    (singleProbeHoles (2*K+2) (by omega) e₀)
    (fun e => profileActivity (2*K+2) (bottleneck w (source e) (target e))
      (sourceHeight w (source e)) (sourceHeight w (target e)) (logicalActivity w₁ e))=_
  rw [singleProbe_partition _ _ _ _ _ (source_ne_target e₀),
    logical_partition_redundant w₁ _ e₀ (by simp)]
  rfl

lemma profile_reweight (p : ℕ) (B Hu Hv lam r : ℝ) (i : Fin (4*p+1)) :
    profileActivity p B Hu Hv (lam*r) i =
      profileActivity p B Hu Hv lam i*(if i.val=2*p then r else 1) := by
  rcases lt_trichotomy i.val (2*p) with hi|hi|hi
  · rw [profile_left _ _ _ _ _ _ hi,profile_left _ _ _ _ _ _ hi,ite_eq_right (ne_of_lt hi),mul_one]
  · have he : i=⟨2*p,by omega⟩ := Fin.ext hi
    rw [he]; simp
  · rw [profile_right _ _ _ _ _ _ hi,profile_right _ _ _ _ _ _ hi,ite_eq_right (ne_of_gt hi),mul_one]

lemma bagReweight_identity (w w₁ : V → V → ℝ) (hw : ∀ x y,0 < w x y) (K : ℕ) :
    (fun e => sourceRealPortion w K e*bagReweight w w₁ K e)=frozenPortion w w₁ K := by
  classical
  funext e
  by_cases he : ∃ q,sourceRealEmbedding w K q=e
  · obtain ⟨q,rfl⟩ := he
    rw [sourceRealPortion,frozenPortion,edgeExtension_on,edgeExtension_on,bagReweight_on]
    have hl : logicalActivity w q.1≠0 := by
      unfold logicalActivity edgeActivity
      split_ifs <;> exact (hw _ _).ne'
    dsimp only [sourceRealActivity,frozenActivity,pathActivity,rawReweight]
    rw [←profile_reweight,mul_div_cancel₀ _ hl]
  · rw [sourceRealPortion,frozenPortion,edgeExtension_off _ _ _ he,edgeExtension_off _ _ _ he,zero_mul]

lemma bagReweight_range (w w₁ : V → V → ℝ) (hw : ∀ x y,0 < w x y)
    (hw₁ : ∀ x y,0 ≤ w₁ x y) (hle : ∀ x y,w₁ x y ≤ w x y) (K : ℕ)
    (e : BagEdge (sourceBags w K)) : 0 ≤ bagReweight w w₁ K e ∧ bagReweight w w₁ K e ≤ 1 := by
  classical
  unfold bagReweight
  split_ifs with he
  · unfold rawReweight
    split_ifs
    · have h₀ : 0 < logicalActivity w he.choose.1 := by
        unfold logicalActivity edgeActivity; split_ifs <;> exact hw _ _
      have h₁ : 0 ≤ logicalActivity w₁ he.choose.1 := by
        unfold logicalActivity edgeActivity; split_ifs <;> exact hw₁ _ _
      have h₂ : logicalActivity w₁ he.choose.1 ≤ logicalActivity w he.choose.1 := by
        unfold logicalActivity edgeActivity; split_ifs <;> exact hle _ _
      exact ⟨div_nonneg h₁ h₀.le,(div_le_one h₀).mpr h₂⟩
    · norm_num
  · norm_num

lemma probePortion_on (w : V → V → ℝ) (K D : ℕ) (e : LogicalEdge V) :
    probePortion w K D (centralEdge w K e)=1/(D:ℝ) := by
  classical
  simp [probePortion]

lemma sourcePortions_collapse (w : V → V → ℝ) (K D : ℕ) :
    Marking.collapse (sourcePortions w K D)=sourceBagWeight w K D := by
  funext e
  simp [Marking.collapse,sourcePortions,Fin.sum_univ_succ,sourceBagWeight]

lemma sourcePortions_nonneg (w : V → V → ℝ) (hw : ∀ x y,0 < w x y) (K D : ℕ)
    (e : BagEdge (sourceBags w K)) (i : Fin 3) : 0 ≤ sourcePortions w K D e i := by
  classical
  fin_cases i
  · exact sourceRealPortion_nonneg w hw K e
  · change 0 ≤ bagHeight w K e.val.val.2/D-probePortion w K D e
    apply sub_nonneg.mpr
    unfold probePortion
    split_ifs
    · exact div_le_div_of_nonneg_right (bagHeight_one w K _) (Nat.cast_nonneg D)
    · exact div_nonneg (bagHeight_pos w K _).le (Nat.cast_nonneg D)
  · change 0 ≤ probePortion w K D e
    unfold probePortion
    split_ifs <;> positivity

lemma centralEdge_ends (w : V → V → ℝ) (K : ℕ) (e : LogicalEdge V) :
    (centralEdge w K e).val.val.1 =
    s((Sum.inr (e,(⟨2*(2*K+2)-1,by omega⟩ : Fin (4*(2*K+2)))) : SourceVertex V K),
      Sum.inr (e,⟨2*(2*K+2),by omega⟩)) := by
  change edge source target (4*(2*K+2)) e ⟨2*(2*K+2),by omega⟩=_
  simp only [edge,atVertex,Fin.val_castSucc,Fin.val_succ]
  simp only [show 2*(2*K+2)≠0 by omega,show 2*(2*K+2)≠4*(2*K+2)+1 by omega,
    show 2*(2*K+2)+1≠0 by omega, show 2*(2*K+2)+1≠4*(2*K+2)+1 by omega,
    dite_false,Nat.add_sub_cancel]

lemma probe_support (w : V → V → ℝ) (K : ℕ) (e₀ : LogicalEdge V) :
    support BagEdge.Incident {centralEdge w K e₀}=
      enlargedHoles (4*(2*K+2)) ∅ (singleProbeHoles (2*K+2) (by omega) e₀) := by
  classical
  ext x
  rw [mem_support]
  simp only [mem_singleton,exists_eq_left,BagEdge.Incident,ColoredEdge.Incident,centralEdge_ends,Sym2.mem_iff]
  cases x with
  | inl x => simp
  | inr ei =>
    rcases ei with ⟨e,i⟩
    by_cases he : e=e₀
    · subst e
      simp [singleProbeHoles,probeHoles]
    · simp [singleProbeHoles,he]

lemma probe_survivors (w : V → V → ℝ) (K : ℕ) (e₀ : LogicalEdge V) :
    univ \ support BagEdge.Incident {centralEdge w K e₀}=
      survivors (4*(2*K+2)) ∅ (singleProbeHoles (2*K+2) (by omega) e₀) := by
  rw [probe_support]
  ext x
  cases x with
  | inl x => simp
  | inr ei => rcases ei with ⟨e,i⟩; simp

open scoped Classical

lemma sourceLaw_sum (w : V → V → ℝ) (K D : ℕ) (hz : sourceBagZ w K D≠0) :
    ∑ a : SourceMarked w K,sourceLaw w K D a=1 := by
  apply Marking.law_sum
  simpa only [sourcePortions_collapse,sourceBagZ] using hz

lemma sourceLaw_nonneg (w : V → V → ℝ) (hw : ∀ x y,0 < w x y) (K D : ℕ)
    (hz : 0 ≤ sourceBagZ w K D) (a : SourceMarked w K) : 0 ≤ sourceLaw w K D a := by
  unfold sourceLaw Marking.law
  rw [sourcePortions_collapse]
  exact div_nonneg (Marking.mass_nonneg _ _ (sourcePortions_nonneg w hw K D) a) hz

theorem observableA_mean (w : V → V → ℝ) (hz : 0 < partition w ∅) (K D : ℕ) :
    (∑ a : SourceMarked w K,sourceLaw w K D a*observableA w K a)=
      sourceC w K*partition w ∅/sourceBagZ w K D := by
  classical
  have h := Marking.allReal_mean BagEdge.Incident (sourcePortions w K D) (0 : Fin 3) (fun _ => 1)
  simpa only [sourceLaw,observableA,Finset.prod_const_one,sourcePortions,Matrix.cons_val_zero,
    mul_one,sourcePortions_collapse,sourceRealPortion_full w hz,sourceC,sourceBagZ] using h

theorem observableD_mean (w w₁ : V → V → ℝ) (hw : ∀ x y,0 < w x y)
    (hz₁ : 0 < partition w₁ ∅) (K D : ℕ) :
    (∑ a : SourceMarked w K,sourceLaw w K D a*observableD w w₁ K a)=
      sourceC w K*partition w₁ ∅/sourceBagZ w K D := by
  classical
  have h := Marking.allReal_mean BagEdge.Incident (sourcePortions w K D) (0 : Fin 3) (bagReweight w w₁ K)
  simp only [sourcePortions,Matrix.cons_val_zero] at h
  rw [bagReweight_identity w w₁ hw K,frozenPortion_full w w₁ hz₁] at h
  simpa only [sourceLaw,observableD,sourcePortions_collapse,sourceBagZ] using h

theorem observableProbe_mean (w w₁ : V → V → ℝ) (hw : ∀ x y,0 < w x y)
    (K D : ℕ) (e₀ : LogicalEdge V) :
    (∑ a : SourceMarked w K,sourceLaw w K D a*observableProbe w w₁ K e₀ a)=
      (sourceC w K*partition w₁ {source e₀,target e₀}/D)/sourceBagZ w K D := by
  classical
  have h := Marking.fixed_probe_mean BagEdge.Incident BagEdge.exists_incident
    (sourcePortions w K D) (0 : Fin 3) 2 (probePartial w K e₀) (bagReweight w w₁ K)
  simp only [sourcePortions,Matrix.cons_val_zero,Matrix.cons_val_two,
    probePartial,Finset.prod_singleton,probePortion_on] at h
  rw [bagReweight_identity w w₁ hw K,probe_survivors,frozenPortion_probe] at h
  calc
    _ = ((1/(D:ℝ))*(sourceC w K*partition w₁ {source e₀,target e₀}))/sourceBagZ w K D := by
      simpa [sourceLaw,observableProbe,sourcePortions_collapse,sourceBagZ,Matrix.vecHead,Matrix.vecTail] using h
    _ = _ := by ring

lemma observableD_range (w w₁ : V → V → ℝ) (hw : ∀ x y,0 < w x y)
    (hw₁ : ∀ x y,0 ≤ w₁ x y) (hle : ∀ x y,w₁ x y ≤ w x y)
    (K : ℕ) (a : SourceMarked w K) :
    0 ≤ observableD w w₁ K a ∧ observableD w w₁ K a ≤ 1 := by
  classical
  unfold observableD
  split_ifs
  · exact ⟨Finset.prod_nonneg (fun e _ => (bagReweight_range w w₁ hw hw₁ hle K e).1),
      Finset.prod_le_one (fun e _ => (bagReweight_range w w₁ hw hw₁ hle K e).1)
        (fun e _ => (bagReweight_range w w₁ hw hw₁ hle K e).2)⟩
  · norm_num

end MatchingFPRAS.Enlargement

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Probability_Tv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Variation

open Finset
open scoped Classical

variable {Ω Ψ : Type*} [Fintype Ω] [Fintype Ψ]

theorem event_sub_le (p q : Ω → ℝ) (hs : ∑ x,p x=∑ x,q x) (P : Ω → Prop) :
    |event p P-event q P| ≤ tv p q := by
  let A : Finset Ω := univ.filter P
  have hz : ∑ x,(p x-q x)=0 := by rw [sum_sub_distrib,hs,sub_self]
  have he : event p P-event q P=∑ x ∈ A,(p x-q x) := by
    simp only [event,←sum_sub_distrib,A,sum_filter]
    apply sum_congr rfl
    intro x _
    split_ifs <;> simp
  have hc : ∑ x ∈ Aᶜ,(p x-q x)= -(∑ x ∈ A,(p x-q x)) := by
    have h := Finset.sum_add_sum_compl A (fun x => p x-q x)
    rw [hz] at h
    linarith
  have ha := abs_sum_le_sum_abs (fun x => p x-q x) A
  have hb := abs_sum_le_sum_abs (fun x => p x-q x) Aᶜ
  rw [hc,abs_neg] at hb
  have hab := Finset.sum_add_sum_compl A (fun x => |p x-q x|)
  rw [he]
  unfold tv
  linarith


end MatchingFPRAS.Variation

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_MetropolisChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Variation

open Finset
open scoped Classical

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

omit [Fintype C] in
lemma imageLaw_comp_equiv (e : A ≃ B) (f : B → C) : imageLaw (f ∘ e)=imageLaw f := by
  funext c
  unfold imageLaw push uniform
  rw [Fintype.card_congr e,←e.sum_comp (fun b=>if f b=c then (1:ℝ)/Fintype.card B else 0)]
  rfl

lemma uniform_prod (a : A×B) : uniform (A×B) a=uniform A a.1*uniform B a.2 := by
  simp [uniform,Fintype.card_prod,Nat.cast_mul,mul_comm]

variable {D : Type*} [Fintype D]

omit [Fintype C] in
lemma imageLaw_pair (f : A → B → C) :
    imageLaw (fun x : A×B=>f x.1 x.2)=bind (uniform A) (fun a=>imageLaw (f a)) := by
  funext c
  simp only [imageLaw,push,bind,Fintype.sum_prod_type,uniform_prod,mul_sum]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  split_ifs <;> simp

omit [Fintype C] in
lemma bind_push (p : A → ℝ) (f : A → B) (k : B → C → ℝ) :
    bind (push p f) k=bind p (fun a=>k (f a)) := by
  funext c
  simp only [bind,push,sum_mul,ite_mul,zero_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  simp

omit [Fintype C] in
lemma imageLaw_adaptive_pair (d : A → D) (f : D → B → C) :
    imageLaw (fun x : A×B=>f (d x.1) x.2)=bind (imageLaw d) (fun a=>imageLaw (f a)) := by
  rw [imageLaw_pair (fun a b=>f (d a) b), imageLaw,bind_push]

open Finset
open scoped Classical

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

omit [Fintype C] in
lemma imageLaw_ignore [Nonempty A] (f : B → C) :
    imageLaw (fun x : A×B=>f x.2)=imageLaw f := by
  rw [imageLaw_pair (fun _ b=>f b)]
  funext c
  simp only [bind,←sum_mul,uniform_sum,one_mul]

lemma imageLaw_subsingleton [Nonempty A] [Subsingleton B] (f : A → B) :
    imageLaw f=uniform B := by
  let : Nonempty B := ⟨f (Classical.choice (inferInstance : Nonempty A))⟩
  funext b
  simp only [imageLaw,push,Subsingleton.elim (f _) b,ite_true,uniform_sum]
  let : Unique B := ⟨⟨b⟩,fun x=>Subsingleton.elim x b⟩
  simp [uniform]

open scoped Classical

end MatchingFPRAS.Variation

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_ExperimentSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalStream.Experiment
variable {α β : Type}
lemma all_bind (p : Experiment α) (q : α → Experiment β) (P : β → Prop) :
    All (p.bind q) P ↔ All p (fun a=>All (q a) P) := by
  induction p with
  | done a => rfl
  | read p ih => simp only [bind,All,ih]
  | delay n p ih => exact ih
lemma all_map (p : Experiment α) (f : α → β) (P : β → Prop) :
    All (p.map f) P ↔ All p (fun a=>P (f a)) := by
  rw [map,all_bind]; rfl

end MatchingFPRAS.PhysicalStream.Experiment

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_OnlineUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalStream
open Finset

variable {A B C : Type} [Fintype A] [Fintype B]
omit [Fintype B] in
lemma qaverage_congr (f g : A → ℚ) (h : ∀ a,f a=g a) : qaverage f=qaverage g := by
  rw [show f=g from funext h]
end MatchingFPRAS.PhysicalStream

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Related2
attribute [-instance] _root_.OAI.MatchingFPRAS.NumberedHierarchy.treeDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumberedHierarchy

open Finset

variable {V : Type*} [Fintype V] [LinearOrder V]

variable (B : V → V → ℚ)

variable (hsym : ∀ x y,B x y=B y x)

variable (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)

lemma labelEquiv_level {H : ℕ} (l : Hierarchy.Label (fun x y=>(B x y:ℝ))
    (symmetric B hsym) (triangular B htri) H) :
    (labelEquiv B hsym htri H l).1=l.1 := rfl

end MatchingFPRAS.NumberedHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_LabelOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.RationalSource

open Finset MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport MatchingFPRAS.Enlargement

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype

attribute [local instance] UnitRefresh.Computable.allowedDec

lemma realPortion_on (w : V → V → ℚ) (K : ℕ) (q : SourceRealEdge V K) :
    realPortion w K (coloredReal w K q)=pathActivity w K q.1 q.2 := by
  simp only [realPortion,(coloredReal_injective w K).eq_iff,sum_ite_eq',mem_univ,ite_true]

lemma realPortion_off (w : V → V → ℚ) (K : ℕ) (e : BagEdge (bags w K))
    (he : ¬∃ q,coloredReal w K q=e) : realPortion w K e=0 := by
  apply sum_eq_zero
  intro q _
  exact ite_eq_right (fun h=>he ⟨q,h⟩)

open MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder MatchingFPRAS.Variation

attribute [local instance] prodOrder sumOrder

end MatchingFPRAS.RationalSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_RelabelMore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.RationalSource

open MatchingFPRAS Switching Subdivision RealGeometry Hierarchy Enlargement Transport Finset

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype

attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder

lemma labelCast_level {X : Type*} [Fintype X] {B B' : X → X → ℝ}
    (s : ∀ x y,B x y=B y x)
    (t : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
    (s' : ∀ x y,B' x y=B' y x)
    (t' : ∀ x y z,x≠y → x≠z → y≠z → min (B' x z) (B' z y)≤B' x y)
    {H H' : ℕ} (hB : B=B') (hH : H=H') (l : Hierarchy.Label B s t H) :
    (labelCast s t s' t' hB hH l).1.val=l.1.val := by
  cases hB;cases hH;rfl

lemma labelsEquiv_level (w : V → V → ℚ) (K : ℕ)
    (l : SourceLabel (fun x y=>(w x y:ℝ)) K) :
    (labelsEquiv w K l).1.val=l.1.val := by
  unfold labelsEquiv
  simp only [Equiv.trans_apply,NumberedHierarchy.labelEquiv_level,labelCast_level]

end MatchingFPRAS.RationalSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_RelabelWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Enlargement
open Transport

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] OAI.MatchingFPRAS.Enlargement.relabelWeightsSourceLabelDecidableEq
attribute [local instance] OAI.MatchingFPRAS.Enlargement.relabelWeightsSourceBagEdgeFintype
lemma realPortion_on (w : V → V → ℝ) (K : ℕ) (q : SourceRealEdge V K) :
    sourceRealPortion w K (sourceColoredReal w K q)=sourceRealActivity w K q := by
  classical
  exact edgeExtension_on (sourceRealEmbedding w K) (sourceRealActivity w K) q
lemma realPortion_off (w : V → V → ℝ) (K : ℕ) (e : BagEdge (sourceBags w K))
    (he : ¬∃ q,sourceColoredReal w K q=e) : sourceRealPortion w K e=0 := by
  classical
  exact edgeExtension_off (sourceRealEmbedding w K) (sourceRealActivity w K) e he
end MatchingFPRAS.Enlargement
namespace MatchingFPRAS.RationalSource
open MatchingFPRAS Transport Enlargement Finset

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
attribute [local instance] OAI.MatchingFPRAS.RationalSource.instDecidableEqSourceLabelCastReal
lemma sourceEdgeEquiv_color (w : V → V → ℚ) (K : ℕ)
    (e : BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) :
    (sourceEdgeEquiv w K e).color=labelsEquiv w K e.color := rfl
lemma bagHeight_cast (w : V → V → ℚ) (K : ℕ) (l : SourceLabel (fun x y=>(w x y:ℝ)) K) :
    (bagHeight w K (labelsEquiv w K l):ℝ)=Enlargement.bagHeight (fun x y=>(w x y:ℝ)) K l := by
  simp only [bagHeight,Enlargement.bagHeight,labelsEquiv_level]
  norm_cast
lemma realPortion_cast (w : V → V → ℚ) (K : ℕ)
    (e : BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) :
    (realPortion w K (sourceEdgeEquiv w K e):ℝ)=sourceRealPortion (fun x y=>(w x y:ℝ)) K e := by
  classical
  by_cases he : ∃ q,sourceColoredReal (fun x y=>(w x y:ℝ)) K q=e
  · obtain ⟨q,rfl⟩:=he
    rw [sourceEdgeEquiv_real,realPortion_on,Enlargement.realPortion_on]
    exact pathActivity_cast w K q.1 q.2
  · rw [realPortion_off w K _ ?_,Enlargement.realPortion_off _ _ _ he]
    norm_num
    rintro ⟨q,hq⟩
    apply he
    refine ⟨q,(sourceEdgeEquiv w K).injective ?_⟩
    rwa [sourceEdgeEquiv_real]
end MatchingFPRAS.RationalSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_CompleteGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS



lemma graph_edges_subset_complete (G : GraphInput) : G.edges ⊆ (completeGraph G.n).edges := by
  classical
  intro e he
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, G.increasing e he⟩

lemma mem_perfectMatchings (G : GraphInput) (M) : M ∈ perfectMatchings G ↔ Perfect G M := by
  classical
  simp only [perfectMatchings, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨fun h => h.2, fun h => ⟨h.1,h⟩⟩

lemma pm_subset_complete (G : GraphInput) : perfectMatchings G ⊆ perfectMatchings (completeGraph G.n) := by
  intro M hM
  apply (mem_perfectMatchings _ _).mpr
  have h := (mem_perfectMatchings _ _).mp hM
  exact ⟨h.1.trans (graph_edges_subset_complete G), h.2⟩

lemma rawWeight_nonneg (G : GraphInput) (x : ℚ) (hx : 0 ≤ x) (M) : 0 ≤ rawWeight G x M := by
  classical
  apply Finset.prod_nonneg
  intro e he
  split_ifs <;> positivity

lemma rawWeight_one (G : GraphInput) (x : ℚ) (M) (hM : M ⊆ G.edges) : rawWeight G x M = 1 := by
  classical
  apply Finset.prod_eq_one
  intro e he
  simp [hM he]

lemma rawWeight_bad (G : GraphInput) (x : ℚ) (hx : 0 ≤ x) (hx1 : x ≤ 1) (M)
    (hM : ¬ M ⊆ G.edges) : rawWeight G x M ≤ x := by
  classical
  obtain ⟨e, he, hbad⟩ := Finset.not_subset.mp hM
  have hp : (∏ f ∈ M.erase e, if f ∈ G.edges then (1:ℚ) else x) ≤ 1 := by
    apply Finset.prod_le_one (fun f _ => by split_ifs <;> positivity)
    intro f hf
    split_ifs <;> simp_all
  change (∏ f ∈ M, if f ∈ G.edges then (1:ℚ) else x) ≤ x
  rw [← Finset.mul_prod_erase M _ he, ite_eq_right hbad]
  simpa using mul_le_mul_of_nonneg_left hp hx



theorem raw_padding_bound (G : GraphInput) (x : ℚ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    (Z G : ℚ) ≤ rawPartition G x ∧
    rawPartition G x ≤ (Z G : ℚ) + (Z (completeGraph G.n) : ℚ)*x := by
  classical
  let full := perfectMatchings (completeGraph G.n)
  let good := perfectMatchings G
  let indicator : Finset (Fin G.n × Fin G.n) → ℚ := fun M => if M ∈ good then 1 else 0
  have hind : (∑ M ∈ full, indicator M) = (Z G : ℚ) := by
    have heq := Finset.sum_subset (f := indicator) (pm_subset_complete G)
      (fun M _ hnot => ite_eq_right hnot)
    change (∑ M ∈ good, indicator M) = ∑ M ∈ full, indicator M at heq
    rw [← heq]
    simp [indicator,good,Z]
  have hlo (M : Finset (Fin G.n × Fin G.n)) (hMF : M ∈ full) : indicator M ≤ rawWeight G x M := by
    by_cases hM : M ∈ good
    · have hsub := ((mem_perfectMatchings G M).mp hM).1
      have hi : indicator M = 1 := ite_eq_left hM
      rw [hi, rawWeight_one G x M hsub]
    · have hi : indicator M = 0 := ite_eq_right hM
      rw [hi]
      exact rawWeight_nonneg G x hx M
  have hup (M : Finset (Fin G.n × Fin G.n)) (hMF : M ∈ full) : rawWeight G x M ≤ indicator M+x := by
    by_cases hM : M ∈ good
    · have hsub := ((mem_perfectMatchings G M).mp hM).1
      have hi : indicator M = 1 := ite_eq_left hM
      rw [hi, rawWeight_one G x M hsub]
      linarith
    · have hsub : ¬ M ⊆ G.edges := by
        intro hh
        apply hM
        apply (mem_perfectMatchings G M).mpr
        exact ⟨hh, ((mem_perfectMatchings (completeGraph G.n) M).mp hMF).2⟩
      have hi : indicator M = 0 := ite_eq_right hM
      rw [hi, zero_add]
      exact rawWeight_bad G x hx hx1 M hsub
  constructor
  · rw [← hind]
    exact Finset.sum_le_sum hlo
  · calc
      rawPartition G x ≤ ∑ M ∈ full, (indicator M+x) := Finset.sum_le_sum hup
      _ = (Z G : ℚ) + (Z (completeGraph G.n) : ℚ)*x := by
        rw [Finset.sum_add_distrib, hind]
        simp [Z,full]



theorem perfect_vertex_factor (G : GraphInput) (M : Finset (Fin G.n × Fin G.n))
    (hM : Perfect G M) (s : Fin G.n → ℚ) :
    (∏ e ∈ M, s e.1*s e.2) = ∏ v, s v := by
  classical
  let ends : Fin G.n × Fin G.n → Finset (Fin G.n) := fun e => {e.1,e.2}
  have hends (e : Fin G.n × Fin G.n) (v) : v ∈ ends e ↔ e.1=v ∨ e.2=v := by
    simp [ends, eq_comm]
  have hpair : (M : Set (Fin G.n × Fin G.n)).PairwiseDisjoint ends := by
    intro e he f hf hne
    apply Finset.disjoint_left.mpr
    intro v hv hw
    have hve : e ∈ M ∧ (e.1=v ∨ e.2=v) := ⟨he,(hends e v).mp hv⟩
    have hvf : f ∈ M ∧ (f.1=v ∨ f.2=v) := ⟨hf,(hends f v).mp hw⟩
    exact hne ((hM.2 v).unique hve hvf)
  have hall : M.biUnion ends = Finset.univ := by
    ext v
    simp only [Finset.mem_univ, iff_true]
    obtain ⟨e,he,_⟩ := hM.2 v
    exact Finset.mem_biUnion.mpr ⟨e,he.1,(hends e v).mpr he.2⟩
  calc
    (∏ e ∈ M, s e.1*s e.2) = ∏ e ∈ M, ∏ v ∈ ends e, s v := by
      apply Finset.prod_congr rfl
      intro e he
      have hne : e.1 ≠ e.2 := (G.increasing e (hM.1 he)).ne
      simp [ends,hne]
    _ = ∏ v ∈ M.biUnion ends, s v := (Finset.prod_biUnion hpair).symm
    _ = ∏ v, s v := by rw [hall]



end MatchingFPRAS

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_RatWeight
attribute [-instance] _root_.OAI.MatchingFPRAS.Transport.Sparse.decideMatching _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.allowedDec _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.edgeDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.StageAnalysis

open Finset MatchingFPRAS.Switching MatchingFPRAS.Initializer

variable {V : Type*} [Fintype V] [LinearOrder V]

lemma selected_card (m : Mate V) (R : Finset V) (hm : HasHoles m R) :
    (univ.filter fun x => x < m.val x).card=(Fintype.card V-R.card)/2 := by
  have hh : HasHoles m Rᶜᶜ := by simpa using hm
  have hc := mate_edge_count m Rᶜ hh
  rw [Finset.card_compl] at hc
  omega

lemma weight_factor (t : ℝ) (w : V → V → ℝ) (m : Mate V) (R : Finset V) (hm : HasHoles m R) :
    weight (fun x y => t*w x y) m=t^((Fintype.card V-R.card)/2)*weight w m := by
  unfold weight
  rw [←prod_filter (fun x => x < m.val x) (fun x => t*w x (m.val x)),
    ←prod_filter (fun x => x < m.val x) (fun x => w x (m.val x)),
    prod_mul_distrib,prod_const,selected_card m R hm]

lemma weight_mono (w w₁ : V → V → ℝ) (hw : ∀ x y,0 ≤ w x y)
    (hle : ∀ x y,x≠y → w x y ≤ w₁ x y) (m : Mate V) : weight w m ≤ weight w₁ m := by
  apply Finset.prod_le_prod
  · intro x _
    split_ifs <;> first | exact hw _ _ | norm_num
  · intro x _
    split_ifs with h
    · exact hle _ _ h.ne
    · rfl

theorem partition_reweight (w w₁ : V → V → ℝ) (hw : ∀ x y,0 ≤ w x y)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hlo : ∀ x y,x≠y → t*w x y ≤ w₁ x y)
    (hhi : ∀ x y,x≠y → w₁ x y ≤ w x y) (R : Finset V) :
    t^(Fintype.card V/2)*partition w R ≤ partition w₁ R ∧
      partition w₁ R ≤ partition w R := by
  have hw₁ : ∀ m : Mate V,0 ≤ weight w₁ m := by
    intro m
    unfold weight
    apply prod_nonneg
    intro x _
    split_ifs with h
    · exact (mul_nonneg ht (hw _ _)).trans (hlo _ _ h.ne)
    · norm_num
  constructor
  · rw [partition,mul_sum]
    apply sum_le_sum
    intro m hm
    have hcard : (Fintype.card V-R.card)/2 ≤ Fintype.card V/2 := Nat.div_le_div_right (Nat.sub_le _ _)
    calc
      _ ≤ t^((Fintype.card V-R.card)/2)*weight w m :=
        mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one ht ht1 hcard) (weight_nonneg w hw m)
      _ = weight (fun x y => t*w x y) m := (weight_factor t w m R ((mem_matchings _ _).mp hm)).symm
      _ ≤ weight w₁ m := weight_mono _ _ (fun x y => mul_nonneg ht (hw x y)) hlo m
  · apply sum_le_sum
    intro m _
    apply Finset.prod_le_prod
    · intro x _
      split_ifs with h
      · exact (mul_nonneg ht (hw _ _)).trans (hlo _ _ h.ne)
      · norm_num
    · intro x _
      split_ifs with h
      · exact hhi _ _ h.ne
      · rfl

lemma cooling_half (n : ℕ) (hn : 2 ≤ n) :
    (1:ℝ)/2 ≤ ((1+1/(n:ℝ))⁻¹)^(n/2) := by
  have hnp : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hb : 0 < 1+1/(n:ℝ) := by positivity
  have hp : (1+1/(n:ℝ))^(n/2) ≤ Real.exp ((n/2:ℕ)/n) := by
    have h := pow_le_pow_left₀ hb.le (by simpa [add_comm] using Real.add_one_le_exp (1/(n:ℝ))) (n/2)
    simpa only [←Real.exp_nat_mul,div_eq_mul_inv,one_mul] using h
  have he : ((n/2:ℕ):ℝ)/(n:ℝ) ≤ 1/2 := by
    apply (div_le_iff₀ hnp).mpr
    have h : (n/2)*2 ≤ n := Nat.div_mul_le_self n 2
    have h' : ((n/2:ℕ):ℝ)*2 ≤ n := by exact_mod_cast h
    linarith
  have hexp : Real.exp (1/2:ℝ)<2 := by
    have hs : (Real.exp (1/2:ℝ))^2=Real.exp 1 := by rw [←Real.exp_nat_mul]; norm_num
    have h := Real.exp_one_lt_three
    have hpos := Real.exp_pos (1/2:ℝ)
    nlinarith
  rw [inv_pow]
  exact (le_inv_comm₀ (by norm_num) (pow_pos hb _)).mpr (by
    norm_num
    simpa only [one_div] using hp.trans ((Real.exp_le_exp.mpr he).trans hexp.le))

theorem partition_cooling (hn : 2 ≤ Fintype.card V)
    (w w₁ : V → V → ℝ) (hw : ∀ x y,0 ≤ w x y)
    (hlo : ∀ x y,x≠y → (1+1/(Fintype.card V:ℝ))⁻¹*w x y ≤ w₁ x y)
    (hhi : ∀ x y,x≠y → w₁ x y ≤ w x y) (R : Finset V) :
    partition w R/2 ≤ partition w₁ R ∧ partition w₁ R ≤ partition w R := by
  have ht : 0 ≤ (1+1/(Fintype.card V:ℝ))⁻¹ := by positivity
  have ht1 : (1+1/(Fintype.card V:ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by
    have h : 0 ≤ 1/(Fintype.card V:ℝ) := by positivity
    linarith)
  have h := partition_reweight w w₁ hw _ ht ht1 hlo hhi R
  refine ⟨?_,h.2⟩
  have hh := mul_le_mul_of_nonneg_right (cooling_half _ hn) (partition_nonneg w hw R)
  linarith

theorem holeRatio_cooling (w w₁ : V → V → ℝ)
    (hw : ∀ x y,0 ≤ w x y) (hz : 0 < partition w ∅)
    (h : ∀ R,partition w R/2 ≤ partition w₁ R ∧ partition w₁ R ≤ partition w R)
    (R : Finset V) : Switching.holeRatio w R/2 ≤ Switching.holeRatio w₁ R ∧ Switching.holeRatio w₁ R ≤ 2*Switching.holeRatio w R := by
  have hz₁ : 0 < partition w₁ ∅ := lt_of_lt_of_le (half_pos hz) (h ∅).1
  have hR := partition_nonneg w hw R
  have hR₁ : 0 ≤ partition w₁ R := (by positivity : 0 ≤ partition w R/2).trans (h R).1
  unfold Switching.holeRatio
  constructor
  · apply (le_div_iff₀ hz₁).mpr
    have hd : partition w R/partition w ∅/2*partition w₁ ∅ ≤ partition w R/2 := by
      calc
        _ ≤ partition w R/partition w ∅/2*partition w ∅ :=
          mul_le_mul_of_nonneg_left (h ∅).2 (by positivity)
        _ = _ := by field_simp [hz.ne']
    exact hd.trans (h R).1
  · apply (div_le_iff₀ hz₁).mpr
    have hd : partition w R ≤ (2*(partition w R/partition w ∅))*partition w₁ ∅ := by
      calc
        _ = (2*(partition w R/partition w ∅))*(partition w ∅/2) := by field_simp [hz.ne']
        _ ≤ _ := mul_le_mul_of_nonneg_left (h ∅).1 (by positivity)
    exact (h R).2.trans hd



open Finset MatchingFPRAS.Switching

variable {V : Type*} [Fintype V] [LinearOrder V]

lemma mate_vertex_product (s : V → ℝ) (m : Mate V) (R : Finset V) (hm : HasHoles m R) :
    (∏ x ∈ univ.filter (fun x => x < m.val x),s x*s (m.val x))=∏ x ∈ Rᶜ,s x := by
  let L := univ.filter fun x => x < m.val x
  let H := univ.filter fun x => m.val x < x
  have himg : L.image m.val=H := by
    ext x
    simp only [L,H,mem_image,mem_filter,mem_univ,true_and]
    constructor
    · rintro ⟨a,ha,rfl⟩
      simpa using ha
    · intro hx
      exact ⟨m.val x,by simpa using hx,mate_mate m x⟩
  have hdis : Disjoint L H := by
    apply disjoint_left.mpr
    intro x hx hy
    exact lt_asymm (mem_filter.mp hx).2 (mem_filter.mp hy).2
  have hunion : L∪H=Rᶜ := by
    ext x
    simp only [L,H,mem_union,mem_filter,mem_univ,true_and,mem_compl]
    rw [←ne_iff_lt_or_gt]
    simpa only [ne_eq,eq_comm] using not_congr (hm x)
  have hp : (∏ x ∈ L,s (m.val x))=∏ x ∈ H,s x := by
    rw [←himg]
    exact (prod_image m.property.injective.injOn).symm
  change (∏ x ∈ L,s x*s (m.val x))=_
  rw [prod_mul_distrib,hp,←prod_union hdis,hunion]

theorem weight_vertex_scaling (w : V → V → ℝ) (s : V → ℝ)
    (m : Mate V) (R : Finset V) (hm : HasHoles m R) :
    weight (fun x y => w x y*s x*s y) m=weight w m*(∏ x ∈ Rᶜ,s x) := by
  unfold weight
  rw [←prod_filter (fun x => x < m.val x) (fun x => w x (m.val x)*s x*s (m.val x)),
    ←prod_filter (fun x => x < m.val x) (fun x => w x (m.val x))]
  calc
    _ = (∏ x ∈ univ.filter (fun x => x < m.val x),w x (m.val x)*(s x*s (m.val x))) := by
      apply prod_congr rfl
      intro x _
      ring
    _ = _ := by rw [prod_mul_distrib,mate_vertex_product s m R hm]

theorem partition_vertex_scaling (w : V → V → ℝ) (s : V → ℝ) (R : Finset V) :
    partition (fun x y => w x y*s x*s y) R=partition w R*(∏ x ∈ Rᶜ,s x) := by
  unfold partition
  rw [sum_mul]
  exact sum_congr rfl fun m hm => weight_vertex_scaling w s m R ((mem_matchings _ _).mp hm)

theorem holeRatio_vertex_scaling (w : V → V → ℝ) (s : V → ℝ) (hs : ∀ x,0 < s x) (R : Finset V) :
    Switching.holeRatio (fun x y => w x y*s x*s y) R=Switching.holeRatio w R/(∏ x ∈ R,s x) := by
  have hp : (∏ x : V,s x)≠0 := prod_ne_zero_iff.mpr (fun x _ => (hs x).ne')
  have hR : (∏ x ∈ R,s x)≠0 := prod_ne_zero_iff.mpr (fun x _ => (hs x).ne')
  have hc : (∏ x ∈ Rᶜ,s x)≠0 := prod_ne_zero_iff.mpr (fun x _ => (hs x).ne')
  have he : (∏ x ∈ R,s x)*(∏ x ∈ Rᶜ,s x)=∏ x,s x := prod_mul_prod_compl R s
  unfold Switching.holeRatio
  rw [partition_vertex_scaling,partition_vertex_scaling,compl_empty]
  by_cases hz : partition w ∅=0
  · simp [hz]
  · rw [←he]
    field_simp

end MatchingFPRAS.StageAnalysis

namespace MatchingFPRAS.Enlargement

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport MatchingFPRAS.StageAnalysis Finset

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

open scoped Classical

attribute [local instance] OAI.MatchingFPRAS.Enlargement.instDecidableEqSourceLabel_6
attribute [local instance] OAI.MatchingFPRAS.Enlargement.instFintypeBagEdgeSourceVertexSourceLabelSourceBags_7
lemma sourceBagZ_pos (w : V → V → ℝ) (hw : ∀ x y,0 < w x y)
    (hz : 0 < partition w ∅) (K D : ℕ) : 0 < sourceBagZ w K D := by
  apply (sourceRealPortion_full_pos w hz K).trans_le
  apply partitionWeight_mono BagEdge.Incident _ _ (sourceRealPortion_nonneg w hw K)
  intro e
  exact le_add_of_nonneg_right (div_nonneg (bagHeight_pos w K _).le (Nat.cast_nonneg D))

lemma sourceBagZ_bounds (hn : 2 ≤ Fintype.card V) (w : V → V → ℝ)
    (hw : ∀ x y,0 < w x y) (hz : 0 < partition w ∅)
    (hrlo : ∀ x,(1:ℝ)/4 ≤ rowMax hn w x) (hrhi : ∀ x,rowMax hn w x ≤ 1)
    (K : ℕ) (hK : ∀ x y,x≠y → edgeActivity w x y ≤ (4:ℝ)^K) :
    sourceC w K*partition w ∅ ≤ sourceBagZ w K (sourceD (V:=V) K) ∧
      sourceBagZ w K (sourceD (V:=V) K) ≤ 2*(sourceC w K*partition w ∅) := by
  have h := source_bag_inflation hn w hw hz hrlo hrhi K hK
  change 1 ≤ _ / _ ∧ _ / _ ≤ 2 at h
  have he : partitionWeight BagEdge.Incident (sourceRealPortion w K) univ=sourceC w K*partition w ∅ :=
    sourceRealPortion_full w hz K
  have hb : sourceBagZ w K (sourceD (V:=V) K)=
      partitionWeight BagEdge.Incident (fun e : BagEdge (sourceBags w K) =>
        sourceRealPortion w K e+(2:ℝ)^e.val.val.2.1.val/inflationScale (V:=SourceVertex V K) (holeScale V)) univ := by
    unfold sourceBagZ sourceBagWeight bagHeight
    rw [sourceD_cast]
  rw [←hb,he] at h
  have hp := mul_pos (sourceC_pos w K) hz
  exact ⟨by simpa using (le_div_iff₀ hp).mp h.1,(div_le_iff₀ hp).mp h.2⟩

theorem source_observable_means (hn : 2 ≤ Fintype.card V) (w w₁ : V → V → ℝ)
    (hw : ∀ x y,0 < w x y) (hz : 0 < partition w ∅)
    (hrlo : ∀ x,(1:ℝ)/4 ≤ rowMax hn w x) (hrhi : ∀ x,rowMax hn w x ≤ 1)
    (hlo : ∀ x y,x≠y → (1+1/(Fintype.card V:ℝ))⁻¹*w x y ≤ w₁ x y)
    (hhi : ∀ x y,x≠y → w₁ x y ≤ w x y)
    (K : ℕ) (hK : ∀ x y,x≠y → edgeActivity w x y ≤ (4:ℝ)^K) :
    let D := sourceD (V:=V) K
    let a := ∑ q : SourceMarked w K,sourceLaw w K D q*observableA w K q
    let d := ∑ q : SourceMarked w K,sourceLaw w K D q*observableD w w₁ K q
    (∑ q : SourceMarked w K,sourceLaw w K D q)=1 ∧
    (∀ q : SourceMarked w K,0 ≤ sourceLaw w K D q) ∧
    (1:ℝ)/2 ≤ a ∧ (1:ℝ)/4 ≤ d ∧
    d/a=partition w₁ ∅/partition w ∅ ∧ (1:ℝ)/2 ≤ d/a ∧ d/a ≤ 1 ∧
    (∀ e : LogicalEdge V,
      (D:ℝ)*(∑ q : SourceMarked w K,sourceLaw w K D q*observableProbe w w₁ K e q)/d=
        Switching.holeRatio w₁ {source e,target e}) := by
  dsimp only
  let D := sourceD (V:=V) K
  have hp := sourceBagZ_pos w hw hz K D
  have hb := sourceBagZ_bounds hn w hw hz hrlo hrhi K hK
  have hc := partition_cooling hn w w₁ (fun x y => (hw x y).le) hlo hhi ∅
  have hz₁ : 0 < partition w₁ ∅ := (half_pos hz).trans_le hc.1
  have hC := sourceC_pos w K
  have hDn : (D:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt (sourceD_one (V:=V) K))
  refine ⟨sourceLaw_sum w K D hp.ne',sourceLaw_nonneg w hw K D hp.le,?_,?_,?_,?_,?_,?_⟩
  · rw [observableA_mean w hz]
    apply (le_div_iff₀ hp).mpr
    nlinarith [hb.2]
  · rw [observableD_mean w w₁ hw hz₁]
    apply (le_div_iff₀ hp).mpr
    nlinarith [mul_le_mul_of_nonneg_left hc.1 hC.le,hb.2]
  · rw [observableD_mean w w₁ hw hz₁,observableA_mean w hz]
    field_simp [hC.ne',hz.ne',hp.ne']
    simpa only [D] using div_self hp.ne'
  · rw [observableD_mean w w₁ hw hz₁,observableA_mean w hz]
    have he : (sourceC w K*partition w₁ ∅/sourceBagZ w K D)/
        (sourceC w K*partition w ∅/sourceBagZ w K D)=partition w₁ ∅/partition w ∅ := by
      field_simp [hC.ne',hz.ne',hp.ne']
    rw [he]
    exact (le_div_iff₀ hz).mpr (by linarith)
  · rw [observableD_mean w w₁ hw hz₁,observableA_mean w hz]
    have he : (sourceC w K*partition w₁ ∅/sourceBagZ w K D)/
        (sourceC w K*partition w ∅/sourceBagZ w K D)=partition w₁ ∅/partition w ∅ := by
      field_simp [hC.ne',hz.ne',hp.ne']
    rw [he]
    exact (div_le_one hz).mpr hc.2
  · intro e
    rw [observableProbe_mean w w₁ hw,observableD_mean w w₁ hw hz₁]
    unfold Switching.holeRatio
    dsimp only [D] at hDn hp ⊢
    field_simp [hC.ne',hz₁.ne',hp.ne',hDn]

end MatchingFPRAS.Enlargement

noncomputable section

namespace MatchingFPRAS.RealStage

open Finset



open Finset

variable {n : ℕ}

lemma ScaleInvariant.pos {G : Fin n → Fin n → ℝ} {v : Fin n → ℝ}
    (hv : ScaleInvariant G v) (i) : 0 < v i := lt_of_lt_of_le (by norm_num [alpha]) (hv.lower i)

lemma rowMaximum_le (hn : 2 ≤ n) (G : Fin n → Fin n → ℝ) (v : Fin n → ℝ)
    (hv : ScaleInvariant G v) (i) : rowMaximum hn G v i ≤ v i := by
  apply Finset.sup'_le
  intro j hj
  exact (div_le_iff₀ (hv.pos j)).mpr (hv.feasible i j (mem_erase.mp hj).1.symm)

lemma ratio_le_rowMaximum (hn : 2 ≤ n) (G : Fin n → Fin n → ℝ) (v : Fin n → ℝ)
    (i j) (hji : j≠i) : G i j/v j ≤ rowMaximum hn G v i :=
  Finset.le_sup' (fun j => G i j/v j) (mem_erase.mpr ⟨hji,mem_univ _⟩)

lemma rowMaximum_lower (hn : 2 ≤ n) (G : Fin n → Fin n → ℝ) (v : Fin n → ℝ)
    (hG : ∀ i j, i≠j → alpha ≤ G i j) (hv : ScaleInvariant G v) (i) :
    alpha/2 ≤ rowMaximum hn G v i := by
  obtain ⟨j,hj⟩ := others_nonempty hn i
  have hji := (mem_erase.mp hj).1
  apply le_trans _ (ratio_le_rowMaximum hn G v i j hji)
  apply (le_div_iff₀ (hv.pos j)).mpr
  have hGi := hG i j hji.symm
  have hvi := hv.upper j
  norm_num [alpha] at *
  linarith

lemma scaleUpdate_le (hn : 2 ≤ n) (G : Fin n → Fin n → ℝ) (v : Fin n → ℝ)
    (hv : ScaleInvariant G v) (i j) : scaleUpdate hn G v i j ≤ v j := by
  by_cases hji : j=i
  · subst j; simpa [scaleUpdate] using rowMaximum_le hn G v hv i
  · simp [scaleUpdate,Function.update_of_ne hji]

lemma scaleUpdate_invariant (hn : 2 ≤ n) (G : Fin n → Fin n → ℝ) (v : Fin n → ℝ)
    (hsym : ∀ i j, G i j=G j i) (hG : ∀ i j, i≠j → alpha ≤ G i j)
    (hv : ScaleInvariant G v) (i) : ScaleInvariant G (scaleUpdate hn G v i) := by
  constructor
  · intro j
    by_cases hji : j=i
    · subst j; simpa [scaleUpdate] using rowMaximum_lower hn G v hG hv i
    · simpa [scaleUpdate,Function.update_of_ne hji] using hv.lower j
  · intro j; exact (scaleUpdate_le hn G v hv i j).trans (hv.upper j)
  · intro a b hab
    by_cases hai : a=i
    · subst a
      have hb := (div_le_iff₀ (hv.pos b)).mp (ratio_le_rowMaximum hn G v i b hab.symm)
      simpa [scaleUpdate,Function.update_of_ne hab.symm] using hb
    · by_cases hbi : b=i
      · subst b
        have ha := (div_le_iff₀ (hv.pos a)).mp (ratio_le_rowMaximum hn G v i a hai)
        simpa [scaleUpdate,Function.update_of_ne hai,hsym i a,mul_comm] using ha
      · simpa [scaleUpdate,Function.update_of_ne hai,Function.update_of_ne hbi] using hv.feasible a b hab

lemma scaleUpdate_tight (hn : 2 ≤ n) (G : Fin n → Fin n → ℝ) (v : Fin n → ℝ)
    (hv : ScaleInvariant G v) (i) :
    ∃ j, j≠i ∧ scaleUpdate hn G v i i*scaleUpdate hn G v i j=G i j := by
  obtain ⟨j,hj,heq⟩ := Finset.exists_mem_eq_sup' (others_nonempty hn i) (fun j => G i j/v j)
  have hji := (mem_erase.mp hj).1
  refine ⟨j,hji,?_⟩
  change rowMaximum hn G v i = G i j/v j at heq
  simp only [scaleUpdate,Function.update_self,Function.update_of_ne hji]
  rw [heq]
  exact div_mul_cancel₀ _ (hv.pos j).ne'

lemma tight_persists (G : Fin n → Fin n → ℝ) (v v' : Fin n → ℝ)
    (hv : ScaleInvariant G v) (hv' : ScaleInvariant G v') (hdown : ∀ i, v' i ≤ v i)
    (i j) (hji : j≠i) (hij : v i*v j=G i j) : v' i*v' j=G i j := by
  apply le_antisymm
  · calc
      _ ≤ v i*v j := mul_le_mul (hdown i) (hdown j) (hv'.pos j).le (hv.pos i).le
      _ = _ := hij
  · exact hv'.feasible i j hji.symm

end MatchingFPRAS.RealStage

end

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_RowPeak
attribute [-instance] _root_.OAI.MatchingFPRAS.Transport.Sparse.decideMatching _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.allowedDec _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.edgeDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace MatchingFPRAS.RealStage

open Finset

variable {n : ℕ}

lemma scalingTrace_invariant (hn : 2 ≤ n) (G : Fin n → Fin n → ℝ)
    (hsym : ∀ i j, G i j=G j i) (hG : ∀ i j, i≠j → alpha ≤ G i j ∧ G i j ≤ 3)
    (k : ℕ) : ScaleInvariant G (scalingTrace hn G k) ∧
      ∀ i, i.val<k → ∃ j, j≠i ∧ scalingTrace hn G k i*scalingTrace hn G k j=G i j := by
  induction k with
  | zero =>
    constructor
    · constructor
      · intro i; norm_num [scalingTrace,alpha]
      · intro i; simp [scalingTrace]
      · intro i j h; have := (hG i j h).2; simp only [scalingTrace]; linarith
    · intro i hi; omega
  | succ k ih =>
    by_cases hk : k<n
    · let i : Fin n := ⟨k,hk⟩
      have hinv := scaleUpdate_invariant hn G (scalingTrace hn G k) hsym (fun i j h => (hG i j h).1) ih.1 i
      have htrace : scalingTrace hn G (k+1)=scaleUpdate hn G (scalingTrace hn G k) i := by
        simp [scalingTrace,hk,i]
      rw [htrace]
      refine ⟨hinv,?_⟩
      intro a ha
      by_cases hak : a.val<k
      · obtain ⟨j,hj,he⟩ := ih.2 a hak
        refine ⟨j,hj,?_⟩
        exact tight_persists G _ _ ih.1 hinv (scaleUpdate_le hn G _ ih.1 i) a j hj he
      · have hai : a=i := Fin.ext (by dsimp [i]; omega)
        subst a
        exact scaleUpdate_tight hn G _ ih.1 i
    · have htrace : scalingTrace hn G (k+1)=scalingTrace hn G k := by simp [scalingTrace,hk]
      rw [htrace]
      refine ⟨ih.1,?_⟩
      intro i _
      exact ih.2 i (by have := i.isLt; omega)



open Finset

theorem one_pass_scaling {n : ℕ} (hn : 2 ≤ n) (G : Fin n → Fin n → ℝ)
    (hsym : ∀ i j, G i j=G j i) (hG : ∀ i j, i≠j → alpha ≤ G i j ∧ G i j ≤ 3) :
    (∀ k i, scalingTrace hn G (k+1) i ≤ scalingTrace hn G k i) ∧
    (∀ i, alpha/2 ≤ scalingTrace hn G n i ∧ scalingTrace hn G n i ≤ 2) ∧
    (∀ i j, i≠j → G i j ≤ scalingTrace hn G n i * scalingTrace hn G n j) ∧
    (∀ i, ∃ j, j≠i ∧ scalingTrace hn G n i * scalingTrace hn G n j=G i j) := by
  have htrace := scalingTrace_invariant hn G hsym hG
  refine ⟨?_,(htrace n).1.lower |> fun h => ?_⟩
  · intro k i
    by_cases hk : k<n
    · change (if h : k<n then scaleUpdate hn G (scalingTrace hn G k) ⟨k,h⟩ else scalingTrace hn G k) i ≤ _
      rw [dite_eq_left hk]
      exact scaleUpdate_le hn G _ (htrace k).1 ⟨k,hk⟩ i
    · simp [scalingTrace,hk]
  · refine ⟨fun i => ⟨h i,(htrace n).1.upper i⟩,(htrace n).1.feasible,?_⟩
    intro i
    exact (htrace n).2 i i.isLt




theorem one_pass_restores_balance {n : ℕ} (hn : 2 ≤ n) (g G : Fin n → Fin n → ℝ)
    (hGsym : ∀ i j, G i j=G j i)
    (hG : ∀ i j, i≠j → alpha ≤ G i j ∧ G i j ≤ 3)
    (hpre : ∀ i, (1:ℝ)/8 ≤ rowPeak hn g i)
    (haccuracy : ∀ i j, i≠j → g i j ≤ G i j ∧ G i j ≤ g i j+2*alpha) :
    (∀ i, (1:ℝ)/16 ≤ scalingTrace hn G n i) ∧
      BalancedRows hn (scaledHoleMatrix g (scalingTrace hn G n)) := by
  let v := scalingTrace hn G n
  have hv := (scalingTrace_invariant hn G hGsym hG n).1
  have hlow (i : Fin n) : (1:ℝ)/16 ≤ v i := by
    obtain ⟨j,hj,heq⟩ := Finset.exists_mem_eq_sup' (others_nonempty hn i) (g i)
    have hji := (mem_erase.mp hj).1
    change rowPeak hn g i=g i j at heq
    have hgij : (1:ℝ)/8 ≤ g i j := by rw [← heq]; exact hpre i
    have hGi := (haccuracy i j hji.symm).1
    have hfeas := hv.feasible i j hji.symm
    have hup := mul_le_mul_of_nonneg_left (hv.upper j) (hv.pos i).le
    dsimp [v]
    linarith
  refine ⟨hlow,?_⟩
  intro i
  constructor
  · obtain ⟨j,hji,heq⟩ := (one_pass_scaling hn G hGsym hG).2.2.2 i
    have hprod : (1:ℝ)/256 ≤ v i*v j := by
      calc
        (1:ℝ)/256 = ((1:ℝ)/16)*((1:ℝ)/16) := by norm_num
        _ ≤ v i*v j := mul_le_mul (hlow i) (hlow j) (by norm_num) (hv.pos i).le
    have hacc := (haccuracy i j hji.symm).2
    have hg : (1:ℝ)/4 ≤ scaledHoleMatrix g v i j := by
      apply (le_div_iff₀ (mul_pos (hv.pos i) (hv.pos j))).mpr
      change v i*v j=G i j at heq
      norm_num [alpha] at hacc
      nlinarith
    apply hg.trans
    exact Finset.le_sup' (scaledHoleMatrix g v i) (mem_erase.mpr ⟨hji,mem_univ _⟩)
  · apply Finset.sup'_le
    intro j hj
    have hji := (mem_erase.mp hj).1
    apply (div_le_one (mul_pos (hv.pos i) (hv.pos j))).mpr
    exact ((haccuracy i j hji.symm).1).trans (hv.feasible i j hji.symm)



lemma sigma_nonneg (D K : ℕ) (epsilon : ℝ) (he : 0 ≤ epsilon) : 0  ≤  sigma D K epsilon := by
  unfold sigma alpha; positivity

lemma sigma_small (D K : ℕ) (hD : 1 ≤ D) (epsilon : ℝ) : sigma D K epsilon  ≤  (1:ℝ)/10000000 := by
  have hDr : (1:ℝ) ≤ D := by exact_mod_cast hD
  apply (min_le_left _ _).trans
  apply (div_le_iff₀ (by positivity : 0  <  (100:ℝ)*D)).mpr
  norm_num [alpha]
  linarith

lemma sigma_times_D (D K : ℕ) (hD : 1 ≤ D) (epsilon : ℝ) : (D:ℝ)*sigma D K epsilon  ≤  alpha/100 := by
  have hDr : (1:ℝ) ≤ D := by exact_mod_cast hD
  have hs : sigma D K epsilon  ≤  alpha/(100*D) := min_le_left _ _
  have hm := (le_div_iff₀ (by positivity : 0  <  (100:ℝ)*D)).mp hs
  norm_num [alpha] at hm ⊢
  nlinarith only [hm]

lemma sigma_relative (D K : ℕ) (epsilon : ℝ) : 10*sigma D K epsilon  ≤  epsilon/(100*K) := by
  have h : sigma D K epsilon  ≤  epsilon/(1000*K) := min_le_right _ _
  calc
    _  ≤  10*(epsilon/(1000*K)) := mul_le_mul_of_nonneg_left h (by norm_num)
    _ = _ := by ring

lemma ratio_error (s a d abar dbar : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ (1:ℝ)/100)
    (ha : (1:ℝ)/2 ≤ a) (hR : (1:ℝ)/2 ≤ d/a  ∧  d/a ≤ 1)
    (haerr : |abar-a| ≤ s) (hderr : |dbar-d| ≤ s) :
    |ratioEstimate abar dbar/(d/a)-1|  ≤  10*s := by
  have hab := abs_le.mp haerr
  have hdb := abs_le.mp hderr
  have hap : 0 < a := by linarith
  have habp : 0 < abar := by linarith
  have hRp : 0 < d/a := by linarith [hR.1]
  have hden : (1:ℝ)/5  ≤  (d/a)*abar := by
    have hbar : (1:ℝ)/2-s  ≤  abar := by linarith
    have hm := mul_le_mul hR.1 hbar (by linarith : 0  ≤  (1:ℝ)/2-s) hRp.le
    nlinarith
  have hnum : |dbar-(d/a)*abar|  ≤  2*s := by
    have hid : dbar-(d/a)*abar=(dbar-d)+(d/a)*(a-abar) := by
      have hm : (d/a)*a=d := div_mul_cancel₀ d hap.ne'
      nlinarith
    rw [hid]
    calc
      _  ≤  |dbar-d|+|(d/a)*(a-abar)| := abs_add_le _ _
      _ = |dbar-d|+(d/a)*|abar-a| := by rw [abs_mul,abs_of_pos hRp,abs_sub_comm a abar]
      _  ≤  s+(d/a)*s := add_le_add hderr (mul_le_mul_of_nonneg_left haerr hRp.le)
      _  ≤  2*s := by nlinarith [mul_le_mul_of_nonneg_right hR.2 hs]
  have hid : ratioEstimate abar dbar/(d/a)-1=(dbar-(d/a)*abar)/((d/a)*abar) := by
    simp only [ratioEstimate, ite_eq_left habp]
    have hdne : d ≠ 0 := by intro hh; simp [hh] at hRp
    field_simp [hap.ne', habp.ne', hdne]
  rw [hid,abs_div,abs_of_pos (mul_pos hRp habp)]
  apply (div_le_iff₀ (mul_pos hRp habp)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hden (show 0 ≤ 10*s by positivity)]



lemma upper_error (D : ℕ) (hD : 1 ≤ D) (s d z dbar zbar : ℝ)
    (hs : 0 ≤ s) (hs1 : s ≤ (1:ℝ)/100)
    (hDs : (D:ℝ)*s ≤ alpha/100) (hd : (1:ℝ)/4 ≤ d)
    (hg : 0 ≤ (D:ℝ)*z/d ∧ (D:ℝ)*z/d ≤ 2)
    (hderr : |dbar-d| ≤ s) (hzerr : |zbar-z| ≤ s) :
    alpha ≤ upperEstimate D dbar zbar ∧ upperEstimate D dbar zbar ≤ 3 ∧
    (D:ℝ)*z/d ≤ upperEstimate D dbar zbar ∧
    upperEstimate D dbar zbar ≤ (D:ℝ)*z/d+2*alpha := by
  have hDr : (1:ℝ) ≤ D := by exact_mod_cast hD
  have hdp : 0 < d := by linarith
  have hdb := abs_le.mp hderr
  have hbar : (1:ℝ)/5 ≤ dbar := by linarith
  have hbarp : 0 < dbar := by linarith
  let g := (D:ℝ)*z/d
  have hg0 : 0 ≤ g := hg.1
  have hg2 : g ≤ 2 := hg.2
  have hnum : |(D:ℝ)*(zbar-z)+g*(d-dbar)| ≤ ((D:ℝ)+2)*s := by
    calc
      _ ≤ |(D:ℝ)*(zbar-z)|+|g*(d-dbar)| := abs_add_le _ _
      _ = (D:ℝ)*|zbar-z|+g*|dbar-d| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg D), abs_of_nonneg hg0,
          abs_sub_comm d dbar]
      _ ≤ (D:ℝ)*s+g*s := add_le_add (mul_le_mul_of_nonneg_left hzerr (Nat.cast_nonneg D))
        (mul_le_mul_of_nonneg_left hderr hg0)
      _ ≤ ((D:ℝ)+2)*s := by nlinarith [mul_le_mul_of_nonneg_right hg2 hs]
  have hid : (D:ℝ)*zbar/dbar-g=((D:ℝ)*(zbar-z)+g*(d-dbar))/dbar := by
    dsimp [g]
    field_simp [hdp.ne', hbarp.ne']
    ring
  have hraw : |(D:ℝ)*zbar/dbar-g| ≤ alpha := by
    rw [hid, abs_div, abs_of_pos hbarp]
    apply (div_le_iff₀ hbarp).mpr
    have hsm : s ≤ (D:ℝ)*s := by nlinarith [mul_le_mul_of_nonneg_right hDr hs]
    have ha : 0 < alpha := by norm_num [alpha]
    have hm := mul_le_mul_of_nonneg_left hbar ha.le
    norm_num [alpha] at hDs hm ⊢
    nlinarith only [hDs, hm, hnum, hsm]
  have hbounds := abs_le.mp hraw
  unfold upperEstimate
  rw [ite_eq_left hbarp]
  refine ⟨le_max_left _ _, ?_, ?_, ?_⟩
  · apply max_le
    · norm_num [alpha]
    · exact min_le_left _ _
  · apply le_max_of_le_right
    exact le_min (by linarith) (by linarith)
  · apply max_le
    · have ha : 0 ≤ alpha := by norm_num [alpha]
      linarith
    · exact (min_le_right _ _).trans (by linarith)



theorem successful_stage_estimates (D K : ℕ) (hD : 1 ≤ D) (_hK : 1 ≤ K)
    (epsilon : ℝ) (he : 0<epsilon) (he1 : epsilon<1)
    (a d z abar dbar zbar : ℝ) (ha : (1:ℝ)/2 ≤ a) (hd : (1:ℝ)/4 ≤ d)
    (hR : (1:ℝ)/2 ≤ d/a ∧ d/a ≤ 1)
    (hg : 0 ≤ (D:ℝ)*z/d ∧ (D:ℝ)*z/d ≤ 2)
    (haerr : |abar-a| ≤ sigma D K epsilon)
    (hderr : |dbar-d| ≤ sigma D K epsilon)
    (hzerr : |zbar-z| ≤ sigma D K epsilon) :
    0<abar ∧ 0<dbar ∧
    |ratioEstimate abar dbar/(d/a)-1| ≤ 10*sigma D K epsilon ∧
    10*sigma D K epsilon ≤ epsilon/(100*K) ∧
    alpha ≤ upperEstimate D dbar zbar ∧ upperEstimate D dbar zbar ≤ 3 ∧
    (D:ℝ)*z/d ≤ upperEstimate D dbar zbar ∧
    upperEstimate D dbar zbar ≤ (D:ℝ)*z/d+2*alpha := by
  have hs := sigma_nonneg D K epsilon he.le
  have hs1 : sigma D K epsilon ≤ (1:ℝ)/100 :=
    (sigma_small D K hD epsilon).trans (by norm_num)
  have hab := abs_le.mp haerr
  have hdb := abs_le.mp hderr
  refine ⟨by linarith, by linarith, ?_, sigma_relative D K epsilon, ?_⟩
  · exact ratio_error _ _ _ _ _ hs hs1 ha hR haerr hderr
  · exact upper_error D hD _ _ _ _ _ hs hs1 (sigma_times_D D K hD epsilon) hd hg hderr hzerr

end MatchingFPRAS.RealStage

end

namespace MatchingFPRAS.Enlargement

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport MatchingFPRAS.StageAnalysis Finset
open scoped Classical

variable {V : Type*} [Fintype V] [LinearOrder V]

omit [Fintype V] in
lemma pairEdge_holes (i j : V) (hij : i≠j) :
    ({source (pairEdge i j hij),target (pairEdge i j hij)} : Finset V)={i,j} := by
  rcases le_total i j with h|h
  · simp [pairEdge,source,target,min_eq_left h,max_eq_right h]
  · simp [pairEdge,source,target,min_eq_right h,max_eq_left h,Finset.pair_comm]

omit [Fintype V] in
lemma estimateMatrix_symm (D : ℕ) (dbar : ℝ) (zbar : LogicalEdge V → ℝ) (i j : V) :
    estimateMatrix D dbar zbar i j=estimateMatrix D dbar zbar j i := by
  rw [estimateMatrix,estimateMatrix,probeMatrix_symm]

lemma rowMax_cooling_lower (hn : 2 ≤ Fintype.card V) (w w₁ : V → V → ℝ)
    (hw : ∀ x y,0 ≤ w x y) (hz : 0 < partition w ∅)
    (hr : ∀ i,(1:ℝ)/4 ≤ rowMax hn w i)
    (hc : ∀ R,partition w R/2 ≤ partition w₁ R ∧ partition w₁ R ≤ partition w R) (i : V) :
    (1:ℝ)/8 ≤ rowMax hn w₁ i := by
  obtain ⟨j,hji,hj⟩ := rowMax_attained hn w i
  have h := (holeRatio_cooling w w₁ hw hz hc {i,j}).1
  have hu := holeRatio_le_rowMax hn w₁ i j hji.symm
  rw [hj] at h
  linarith [hr i]

variable [Nontrivial V]

variable {n : ℕ} [Nontrivial (Fin n)]

attribute [local instance] OAI.MatchingFPRAS.Enlargement.instDecidableEqSourceLabel_7
noncomputable local instance instDecidableEqSourceLabelFin_r2631ec_1 (w : Fin n → Fin n → ℝ) (K : ℕ) : DecidableEq (SourceLabel w K) := Classical.decEq _
omit [Nontrivial (Fin n)] in
lemma rowPeak_holeMatrix (hn : 2 ≤ n) (w : Fin n → Fin n → ℝ) (i : Fin n) :
    RealStage.rowPeak hn (fun i j => Switching.holeRatio w {i,j}) i=
      rowMax (by simpa using hn) w i := rfl

variable {K T : ℕ}

omit [Nontrivial (Fin n)] in
lemma StageData.cooling (c : StageData n K T) (R : Finset (Fin n)) :
    partition c.w R/2 ≤ partition c.next R ∧ partition c.next R ≤ partition c.w R := by
  apply partition_cooling (by simpa using c.hn) c.w c.next (fun i j => (c.positive i j).le)
  · simpa using c.cool_lower
  · exact c.cool_upper

attribute [local instance] OAI.MatchingFPRAS.Enlargement.instFintypeBagEdgeSourceVertexSourceLabelSourceBags_8
noncomputable local instance instFintypeBagEdgeSourceVertexFinSourceLabelSourceBags_r2631ec_1 (w : Fin n → Fin n → ℝ) (K : ℕ) : Fintype (BagEdge (sourceBags w K)) := Fintype.ofFinite _
lemma StageData.mean_bounds (c : StageData n K T) :
    (1:ℝ)/2 ≤ meanA c.w K ∧ (1:ℝ)/4 ≤ meanD c.w c.next K ∧
    meanD c.w c.next K/meanA c.w K=partition c.next ∅/partition c.w ∅ ∧
    (1:ℝ)/2 ≤ meanD c.w c.next K/meanA c.w K ∧ meanD c.w c.next K/meanA c.w K ≤ 1 ∧
    (∀ e,(sourceD (V:=Fin n) K:ℝ)*meanProbe c.w c.next K e/meanD c.w c.next K=
      Switching.holeRatio c.next {source e,target e}) := by
  have h := source_observable_means (V:=Fin n) (by simpa using c.hn) c.w c.next c.positive c.partition_positive
    c.lower c.upper (by simpa using c.cool_lower) c.cool_upper K c.cap
  unfold meanA meanD meanProbe
  exact h.2.2

omit [Nontrivial (Fin n)] in
lemma StageData.hole_upper (c : StageData n K T) (i j : Fin n) (hij : i≠j) :
    Switching.holeRatio c.next {i,j} ≤ 2 := by
  have h := (holeRatio_cooling c.w c.next (fun i j => (c.positive i j).le)
    c.partition_positive c.cooling {i,j}).2
  have hr := (holeRatio_le_rowMax (by simpa using c.hn) c.w i j hij).trans (c.upper i)
  linarith

theorem actual_stage_statistics (c : StageData n K T) (b : EmpiricalData c) (i j : Fin n) (hij : i≠j) :
    let G := estimateMatrix (sourceD (V:=Fin n) K) b.dbar b.zbar
    0 < b.abar ∧ 0 < b.dbar ∧
    |RealStage.ratioEstimate b.abar b.dbar/(partition c.next ∅/partition c.w ∅)-1| ≤ c.epsilon/(100*T) ∧
    RealStage.alpha ≤ G i j ∧ G i j ≤ 3 ∧
    Switching.holeRatio c.next {i,j} ≤ G i j ∧
    G i j ≤ Switching.holeRatio c.next {i,j}+2*RealStage.alpha := by
  dsimp only
  have hm := c.mean_bounds
  have hem := hm.2.2.2.2.2 (pairEdge i j hij)
  rw [pairEdge_holes] at hem
  have hg0 := holeRatio_nonneg c.next (fun x y => (c.next_positive x y).le) {i,j}
  have h := RealStage.successful_stage_estimates (sourceD (V:=Fin n) K) T (sourceD_one K)
    c.stages c.epsilon c.epsilon_positive c.epsilon_lt_one
    (meanA c.w K) (meanD c.w c.next K) (meanProbe c.w c.next K (pairEdge i j hij))
    b.abar b.dbar (b.zbar (pairEdge i j hij)) hm.1 hm.2.1
    ⟨hm.2.2.2.1,hm.2.2.2.2.1⟩
    ⟨by rw [hem]; exact hg0,by rw [hem]; exact c.hole_upper i j hij⟩
    b.errorA b.errorD (b.errorProbe _)
  refine ⟨h.1,h.2.1,?_,?_⟩
  · have he := h.2.2.1.trans h.2.2.2.1
    rwa [hm.2.2.1] at he
  · simpa only [estimateMatrix,probeMatrix_off _ _ _ hij,hem] using h.2.2.2.2

theorem actual_successful_stage (c : StageData n K T) (b : EmpiricalData c) :
    let G := estimateMatrix (sourceD (V:=Fin n) K) b.dbar b.zbar
    let v := RealStage.scalingTrace c.hn G n
    (∀ i,(1:ℝ)/16 ≤ v i ∧ v i ≤ 2) ∧
    (∀ i,(1:ℝ)/4 ≤ rowMax (by simpa using c.hn) (fun x y => c.next x y*v x*v y) i ∧
      rowMax (by simpa using c.hn) (fun x y => c.next x y*v x*v y) i ≤ 1) ∧
    |RealStage.ratioEstimate b.abar b.dbar/(partition c.next ∅/partition c.w ∅)-1| ≤ c.epsilon/(100*T) := by
  dsimp only
  let G := estimateMatrix (sourceD (V:=Fin n) K) b.dbar b.zbar
  let g := fun i j => Switching.holeRatio c.next {i,j}
  have hest := actual_stage_statistics c b
  have hGs := estimateMatrix_symm (sourceD (V:=Fin n) K) b.dbar b.zbar
  have hGb : ∀ i j,i≠j → RealStage.alpha ≤ G i j ∧ G i j ≤ 3 := by
    intro i j hij
    exact ⟨(hest i j hij).2.2.2.1,(hest i j hij).2.2.2.2.1⟩
  have hGa : ∀ i j,i≠j → g i j ≤ G i j ∧ G i j ≤ g i j+2*RealStage.alpha := by
    intro i j hij
    exact (hest i j hij).2.2.2.2.2
  have hpre : ∀ i,(1:ℝ)/8 ≤ RealStage.rowPeak c.hn g i := by
    intro i
    rw [show g=(fun i j => Switching.holeRatio c.next {i,j}) from rfl,rowPeak_holeMatrix]
    exact rowMax_cooling_lower (by simpa using c.hn) c.w c.next (fun x y => (c.positive x y).le)
      c.partition_positive c.lower c.cooling i
  have hb := RealStage.one_pass_restores_balance c.hn g G hGs hGb hpre hGa
  let v := RealStage.scalingTrace c.hn G n
  have hv := (RealStage.scalingTrace_invariant c.hn G hGs hGb n).1
  have heq (i j : Fin n) (hij : i≠j) :
      Switching.holeRatio (fun x y => c.next x y*v x*v y) {i,j}=RealStage.scaledHoleMatrix g v i j := by
    rw [holeRatio_vertex_scaling c.next v (fun x => hv.pos x),Finset.prod_pair hij]
    rfl
  have hb' (i : Fin n) : (1:ℝ)/4 ≤ rowMax (by simpa using c.hn) (fun x y => c.next x y*v x*v y) i ∧
      rowMax (by simpa using c.hn) (fun x y => c.next x y*v x*v y) i ≤ 1 := by
    have he : rowMax (by simpa using c.hn) (fun x y => c.next x y*v x*v y) i=
        RealStage.rowPeak c.hn (RealStage.scaledHoleMatrix g v) i := by
      unfold rowMax RealStage.rowPeak
      apply Finset.sup'_congr _ rfl
      intro j hj
      exact heq i j (Finset.mem_erase.mp hj).1.symm
    rw [he]
    exact hb.2 i
  refine ⟨fun i => ⟨hb.1 i,hv.upper i⟩,hb',?_⟩
  let i : Fin n := ⟨0,by have := c.hn; omega⟩
  let j : Fin n := ⟨1,by have := c.hn; omega⟩
  have hij : i≠j := by intro h; have := Fin.val_eq_of_eq h; dsimp [i,j] at this; omega
  exact (hest i j hij).2.2.1

end MatchingFPRAS.Enlargement

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Probability_FinitePMF
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Enlargement

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport MatchingFPRAS.StageAnalysis Finset
open scoped Classical

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

variable {n K T S : ℕ} [Nontrivial (Fin n)]

attribute [local instance] OAI.MatchingFPRAS.Enlargement.instDecidableEqSourceLabel_8
lemma StageData.sigma_pos (c : StageData n K T) : 0 < RealStage.sigma (sourceD (V:=Fin n) K) T c.epsilon := by
  unfold RealStage.sigma RealStage.alpha
  have hD : 0 < sourceD (V:=Fin n) K := sourceD_one K
  have ht : 0 < T := c.stages
  have he := c.epsilon_positive
  exact lt_min (by positivity) (by positivity)

lemma StageData.sampleCount_pos (c : StageData n K T) :
    0 < stageSampleCount n (sourceD (V:=Fin n) K) T c.epsilon := by
  unfold stageSampleCount
  apply Nat.ceil_pos.mpr
  have hs := c.sigma_pos
  positivity



open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport Finset
open MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder
open scoped Classical

end MatchingFPRAS.Enlargement

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_Endpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.GraphBridge

open Finset MatchingFPRAS.Enlargement MatchingFPRAS.Subdivision MatchingFPRAS.Representation MatchingFPRAS.Switching

variable {n : ℕ}

lemma selected_prod {A : Type*} [CommMonoid A] (s : LogicalEdge (Fin n) → Bool)
    (w : Fin n × Fin n → A) :
    (∏ e ∈ selectedEdges s,w e)=∏ e : LogicalEdge (Fin n),if s e then w e.val else 1 := by
  rw [selectedEdges,prod_map]
  exact prod_filter (fun e => s e=true) (fun e => w e.val)

theorem weighted_partition (w : Fin n → Fin n → ℝ) :
    (∑ M ∈ perfectMatchings (completeGraph n),∏ e ∈ M,w e.1 e.2)=partition w ∅ := by
  classical
  rw [←logical_partition_eq w ∅]
  let := Fintype.ofFinite {s : LogicalEdge (Fin n) → Bool // LogicalHoles source target ∅ ∅ s}
  let := Fintype.ofFinite {M : Finset (Fin n × Fin n) // Perfect (completeGraph n) M}
  rw [Finset.sum_subtype (perfectMatchings (completeGraph n)) (mem_perfectMatchings _)]
  unfold logicalHolePartition
  symm
  apply Fintype.sum_equiv perfectEquiv
  intro s
  rw [show (perfectEquiv s).val=selectedEdges s.val from rfl,selected_prod]
  apply prod_congr rfl
  intro e _
  simp [logicalActivity,edgeActivity,source,target,e.property]

theorem raw_partition (G : GraphInput) (x : ℚ) :
    (rawPartition G x:ℝ)=partition (rawActivity G x) ∅ := by
  unfold rawPartition rawWeight
  push_cast
  rw [←weighted_partition]
  apply sum_congr rfl
  intro M hM
  apply prod_congr rfl
  intro e he
  have hi := (completeGraph G.n).increasing e (((mem_perfectMatchings (completeGraph G.n) M).mp hM).1 he)
  simp only [rawActivity,min_eq_left hi.le,max_eq_right hi.le]
  split_ifs <;> simp

theorem complete_count :
    Z (completeGraph n)=UnitRefresh.pairingCount n := by
  have h := weighted_partition (n:=n) (fun _ _ => 1)
  simp only [prod_const_one,sum_const,nsmul_eq_mul,mul_one] at h
  rw [Initializer.uniform_partition,card_empty,Nat.sub_zero,one_pow,mul_one,Fintype.card_fin] at h
  exact_mod_cast h

end MatchingFPRAS.GraphBridge

namespace MatchingFPRAS.Trial

open Finset Switching Subdivision RealGeometry Hierarchy Transport Enlargement StageAnalysis
open scoped Classical

lemma raw_partition_pos (G : GraphInput) (he : Even G.n) (j : ℕ) : 0<partition (raw G j) ∅ := by
  apply partition_pos_of_even _ (raw_pos G j)
  simpa using he

variable {G : GraphInput} {j K S : ℕ}

lemma ScaleState.ratio (s : ScaleState G j) :
    partition s.nextActivity ∅/partition s.activity ∅=
      partition (raw G (j+1)) ∅/partition (raw G j) ∅ := by
  unfold ScaleState.activity ScaleState.nextActivity
  rw [partition_vertex_scaling,partition_vertex_scaling]
  have hp : (∏ x ∈ (∅:Finset (Fin G.n))ᶜ,s.scale x)≠0 :=
    ne_of_gt (prod_pos fun x _ => s.positive x)
  exact mul_div_mul_right _ _ hp

end MatchingFPRAS.Trial

namespace MatchingFPRAS.Counting

theorem stage_product_error (K : ℕ) (hK : 1 ≤ K) (epsilon : ℝ)
    (he : 0 < epsilon) (he1 : epsilon < 1) (factors : Fin K → ℝ)
    (herr : ∀ j, |factors j-1| ≤ epsilon/(100*K)) :
    1-epsilon/100 ≤ ∏ j, factors j ∧ ∏ j, factors j ≤ 1+epsilon/50 := by
  classical
  have hKr : (1:ℝ) ≤ K := by exact_mod_cast hK
  have hKp : (0:ℝ) < K := by linarith
  let t : ℝ := epsilon/(100*K)
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ epsilon/100 := by
    dsimp [t]
    apply (div_le_iff₀ (by positivity : 0 < (100:ℝ)*K)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hKr he.le]
  have hkt : (K:ℝ)*t=epsilon/100 := by dsimp [t]; field_simp
  have hlo (j : Fin K) : 1-t ≤ factors j := by
    have h := (abs_le.mp (herr j)).1
    change -t ≤ factors j-1 at h
    linarith
  have hup (j : Fin K) : factors j ≤ 1+t := by
    have h := (abs_le.mp (herr j)).2
    change factors j-1 ≤ t at h
    linarith
  have hf0 (j : Fin K) : 0 ≤ factors j := by have := hlo j; linarith
  constructor
  · have hpow : 1-epsilon/100 ≤ (1-t)^K := by
      have h := one_add_mul_le_pow (a := -t) (by linarith : (-2:ℝ) ≤ -t) K
      simpa only [← sub_eq_add_neg, mul_neg, hkt] using h
    apply hpow.trans
    calc
      (1-t)^K = ∏ _j : Fin K, (1-t) := by simp
      _ ≤ ∏ j, factors j := Finset.prod_le_prod (fun _ _ => by linarith) (fun j _ => hlo j)
  · have hprod : (∏ j, factors j) ≤ Real.exp (epsilon/100) := by
      calc
        _ ≤ ∏ _j : Fin K, (1+t) := Finset.prod_le_prod (fun j _ => hf0 j) (fun j _ => hup j)
        _ ≤ Real.exp (∑ _j : Fin K, t) := Real.prod_one_add_le_exp_sum _ (fun _ => ht0)
        _ = Real.exp (epsilon/100) := by simp [hkt]
    apply hprod.trans
    have hh := Real.exp_le_two_add_div_two_sub (x := epsilon/100) (by positivity) (by linarith)
    apply hh.trans
    apply (div_le_iff₀ (by linarith : 0 < 2-epsilon/100)).mpr
    nlinarith [sq_nonneg epsilon]



lemma positive_telescope (Z : ℕ → ℝ) (hZ : ∀ j, 0 < Z j) (K : ℕ) :
    (∏ j : Fin K, Z (j.val+1)/Z j.val)=Z K/Z 0 := by
  induction K with
  | zero => simp [(hZ 0).ne']
  | succ K ih =>
    rw [Fin.prod_univ_castSucc]
    change (∏ j : Fin K, Z (j.val+1)/Z j.val)*(Z (K+1)/Z K)=_
    rw [ih]
    field_simp [(hZ K).ne', (hZ 0).ne']

end MatchingFPRAS.Counting

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Probability_AdaptiveLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.Counting.scheduleDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Counting

theorem trial_output_error (K : ℕ) (hK : 1 ≤ K) (epsilon : ℝ)
    (he : 0 < epsilon) (he1 : epsilon < 1) (Z : ℕ → ℝ)
    (hZ : ∀ j, 0 < Z j) (estimates : Fin K → ℝ)
    (herr : ∀ j, |estimates j/(Z (j.val+1)/Z j.val)-1| ≤ epsilon/(100*K)) :
    (1-epsilon/100)*Z K ≤ productEstimate (Z 0) estimates ∧
    productEstimate (Z 0) estimates ≤ (1+epsilon/50)*Z K := by
  let f : Fin K → ℝ := fun j => estimates j/(Z (j.val+1)/Z j.val)
  have hprod := stage_product_error K hK epsilon he he1 f herr
  have hid : productEstimate (Z 0) estimates = (∏ j, f j)*Z K := by
    rw [show (∏ j, f j)=(∏ j, estimates j)/(∏ j : Fin K, Z (j.val+1)/Z j.val) from
      Finset.prod_div_distrib _ _]
    rw [positive_telescope Z hZ K]
    unfold productEstimate
    field_simp [(hZ 0).ne', (hZ K).ne']
  rw [hid]
  exact ⟨mul_le_mul_of_nonneg_right hprod.1 (hZ K).le,
    mul_le_mul_of_nonneg_right hprod.2 (hZ K).le⟩

end MatchingFPRAS.Counting

namespace MatchingFPRAS.UnitRefresh

lemma pairingCount_le_half_power (n : ℕ) : pairingCount n ≤ n^(n/2) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih ih' =>
    rw [pairingCount_add_two,show (n+2)/2=n/2+1 by omega,pow_succ]
    calc
      (n+1)*pairingCount n ≤ (n+2)*((n+2)^(n/2)) :=
        Nat.mul_le_mul (by omega) (ih.trans (Nat.pow_le_pow_left (by omega) (n/2)))
      _ = (n+2)^(n/2)*(n+2) := Nat.mul_comm _ _

end MatchingFPRAS.UnitRefresh

namespace MatchingFPRAS.Trial

open Finset Switching

lemma initial_raw_partition (G : GraphInput) : partition (raw G 0) ∅=(Z (completeGraph G.n):ℝ) := by
  rw [raw_zero,Initializer.uniform_partition,Finset.card_empty,Nat.sub_zero,one_pow,mul_one,
    Fintype.card_fin,GraphBridge.complete_count]

theorem final_padding (G : GraphInput) (ε : ℚ) (hε : 0<ε) (K : ℕ)
    (hK : Counting.scheduleAdmissible G.n ε K) (hZ : 0<Z G) :
    (Z G:ℝ) ≤ partition (raw G K) ∅ ∧
      partition (raw G K) ∅ ≤ (1+(ε:ℝ)/32)*(Z G:ℝ) := by
  let x : ℚ := ((1+1/(G.n:ℚ))⁻¹)^K
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hx1 : x ≤ 1 := by
    apply pow_le_one₀ (by positivity)
    apply inv_le_one_of_one_le₀
    have hh : (0:ℚ)≤1/(G.n:ℚ) := by positivity
    linarith
  have hcast : (x:ℝ)=cooling G.n^K := by
    dsimp [x,cooling]
    push_cast
    rfl
  have hp : (rawPartition G x:ℝ)=partition (raw G K) ∅ := by
    rw [GraphBridge.raw_partition,hcast]
    rfl
  have hb := raw_padding_bound G x hx hx1
  have hb0 : (Z G:ℝ)≤partition (raw G K) ∅ := by rw [←hp]; exact_mod_cast hb.1
  have hb1 : partition (raw G K) ∅≤(Z G:ℝ)+(Z (completeGraph G.n):ℝ)*(x:ℝ) := by
    rw [←hp]; exact_mod_cast hb.2
  have hcount : (Z (completeGraph G.n):ℝ)≤(G.n:ℝ)^(G.n/2) := by
    rw [GraphBridge.complete_count]
    exact_mod_cast UnitRefresh.pairingCount_le_half_power G.n
  have hsmall : (G.n:ℝ)^(G.n/2)*(x:ℝ) ≤ (ε:ℝ)/32 := by
    have hq : (G.n:ℚ)^(G.n/2)*x ≤ ε/32 := by
      simpa only [x,div_eq_mul_inv,inv_pow] using hK.2
    exact_mod_cast hq
  have hz1 : (1:ℝ)≤Z G := by exact_mod_cast hZ
  have he0 : (0:ℝ)<ε := by exact_mod_cast hε
  have hh := mul_le_mul_of_nonneg_right hcount (by exact_mod_cast hx : (0:ℝ)≤x)
  refine ⟨hb0,?_⟩
  nlinarith

theorem final_trial_interval (G : GraphInput) (heven : Even G.n) (ε : ℚ)
    (hε : 0<ε) (hε1 : ε<1) (K : ℕ) (hK : Counting.scheduleAdmissible G.n ε K)
    (hZ : 0<Z G) (r : Fin K → ℝ)
    (hr : ∀ j,|r j/(partition (raw G (j.val+1)) ∅/partition (raw G j.val) ∅)-1|≤(ε:ℝ)/(100*K)) :
    let Y := (Z (completeGraph G.n):ℝ)*∏ j,r j
    (1-(ε:ℝ))*(Z G:ℝ)≤Y ∧ Y≤(1+(ε:ℝ))*(Z G:ℝ) := by
  dsimp only
  have he : (0:ℝ)<ε := by exact_mod_cast hε
  have he1 : (ε:ℝ)<1 := by exact_mod_cast hε1
  have h := Counting.trial_output_error K hK.1 ε he he1
    (fun j=>partition (raw G j) ∅) (raw_partition_pos G heven) r hr
  simp only [Counting.productEstimate,initial_raw_partition] at h
  have hb := final_padding G ε hε K hK hZ
  have hz : (0:ℝ)≤Z G := Nat.cast_nonneg _
  constructor
  · have hmul := mul_le_mul_of_nonneg_left hb.1 (by linarith : (0:ℝ)≤1-(ε:ℝ)/100)
    nlinarith [mul_nonneg he.le hz]
  · have hmul := mul_le_mul_of_nonneg_left hb.2 (by positivity : (0:ℝ)≤1+(ε:ℝ)/50)
    have hscalar : (1+(ε:ℝ)/50)*(1+(ε:ℝ)/32)≤1+(ε:ℝ) := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hscalar hz
    nlinarith

end MatchingFPRAS.Trial

namespace MatchingFPRAS.Adaptive

open Finset

variable {Ω : Type*} [Fintype Ω]

lemma Law.event_nonneg (μ : Law Ω) (P : Ω → Prop) : 0 ≤ μ.event P := by
  classical
  apply sum_nonneg
  intro x _
  split_ifs
  · exact μ.nonneg x
  · rfl

lemma Law.event_le_one (μ : Law Ω) (P : Ω → Prop) : μ.event P ≤ 1 := by
  classical
  rw [← μ.total]
  apply sum_le_sum
  intro x _
  split_ifs
  · rfl
  · exact μ.nonneg x



open Finset
open scoped Classical

variable {Ω : Type*} [Fintype Ω] {Ψ : Ω → Type*} [∀ x,Fintype (Ψ x)]

lemma Law.sigma_event (μ : Law Ω) (ν : ∀ x,Law (Ψ x)) (P : Sigma Ψ → Prop) :
    (μ.sigma ν).event P=∑ x,μ x*(ν x).event (fun y=>P ⟨x,y⟩) := by
  unfold Law.event
  rw [Fintype.sum_sigma]
  apply sum_congr rfl
  intro x _
  rw [mul_sum]
  apply sum_congr rfl
  intro y _
  split_ifs <;> simp [Law.sigma]

lemma Law.event_mono (μ : Law Ω) {P Q : Ω → Prop} (h : ∀ x,P x→Q x) :
    μ.event P ≤ μ.event Q := by
  unfold Law.event
  apply sum_le_sum
  intro x _
  split_ifs with hp hq hq
  · rfl
  · exact False.elim (hq (h x hp))
  · exact μ.nonneg x
  · rfl

lemma first_failure_sigma (μ : Law Ω) (ν : ∀ x,Law (Ψ x))
    (P : Ω → Prop) (Q : Sigma Ψ → Prop) (η : ℝ) (hη : 0≤η)
    (h : ∀ x,P x→(ν x).event (fun y=>¬Q ⟨x,y⟩) ≤ η) :
    (μ.sigma ν).event (fun z=>¬Q z) ≤ μ.event (fun x=>¬P x)+η := by
  rw [Law.sigma_event,←mul_one η,←μ.total,mul_sum]
  unfold Law.event
  rw [←sum_add_distrib]
  apply sum_le_sum
  intro x _
  by_cases hx : P x
  · have hh := mul_le_mul_of_nonneg_left (h x hx) (μ.nonneg x)
    simpa [Law.event,hx,mul_comm] using hh
  · have hh := mul_le_mul_of_nonneg_left ((ν x).event_le_one (fun y=>¬Q ⟨x,y⟩)) (μ.nonneg x)
    have hz := mul_nonneg hη (μ.nonneg x)
    dsimp [Law.event] at hh
    dsimp [Law.event]
    simp only [hx,not_false_eq_true,ite_true]
    nlinarith



open Finset
open MatchingFPRAS.Enlargement MatchingFPRAS.Transport MatchingFPRAS.Replica.Ladder
open scoped Classical

end MatchingFPRAS.Adaptive

namespace MatchingFPRAS.Trial

open Finset Switching Subdivision RealGeometry Hierarchy Transport Enlargement StageAnalysis
open MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder MatchingFPRAS.Adaptive
open scoped Classical

variable {G : GraphInput} [Nontrivial (Fin G.n)]

noncomputable local instance instDecidableEqSourceLabelFinN_1_r2631ec_1 (w : Fin G.n → Fin G.n → ℝ) (K : ℕ) : DecidableEq (SourceLabel w K) := Classical.decEq _
lemma Parameters.S_pos (p : Parameters G) : 0<p.S := p.initialData.sampleCount_pos

attribute [instance] Layer.finite

end MatchingFPRAS.Trial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_ProductBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Variation

open Finset
open scoped Classical

variable {Ω : Type*} [Fintype Ω]

lemma uniform_fun {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A] (x : I → A) :
    uniform (I → A) x=∏ i,uniform A (x i) := by
  simp [uniform,Nat.cast_pow]

omit [Fintype Ω] in
lemma imageLaw_componentwise [Fintype Ω] {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
    (f : I → A → Ω) : imageLaw (fun x : I → A=>fun i=>f i (x i))=
      product (fun i=>imageLaw (f i)) := by
  funext y
  let : DecidableEq (I → Ω) := Classical.decEq _
  have he (x : I → A) : (if (fun i=>f i (x i))=y then uniform (I → A) x else 0)=
      ∏ i,if f i (x i)=y i then uniform A (x i) else 0 := by
    by_cases h : (fun i=>f i (x i))=y
    · rw [ite_eq_left h,uniform_fun]
      apply prod_congr rfl
      intro i _
      rw [ite_eq_left (congrFun h i)]
    · rw [ite_eq_right h]
      obtain ⟨i,hi⟩ : ∃ i,f i (x i)≠y i := by
        by_contra hn
        apply h
        funext i
        exact Classical.not_not.mp (fun hi=>hn ⟨i,hi⟩)
      symm
      exact prod_eq_zero (mem_univ i) (ite_eq_right hi)
  unfold imageLaw push product
  simp_rw [he]
  exact (Fintype.prod_sum (fun i a=>if f i a=y i then uniform A a else 0)).symm

end MatchingFPRAS.Variation

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Probability_Marking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.RationalSource
open Finset Transport Variation Enlargement

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance instDecidableEqBagPMSourceVertexLabelBags_2_r2631ec_1 (w : V → V → ℚ) (K : ℕ) : DecidableEq (BagPM (bags w K)) := Classical.decEq _
lemma markingTable_law (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D : ℕ) (hD : 0<D)
    (e : BagEdge (bags w K)) (i : Fin 3) :
    (markingTable w hw K D hD e).law i=portions w K D e i/bagWeight w K D e := by
  change (∑ j : Fin 3,if j=i then portions w K D e j/bagWeight w K D e else 0)=_
  simp only [sum_ite_eq',mem_univ,ite_true]

end MatchingFPRAS.RationalSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_RelabelMarking
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport
open Finset

variable {V E F I : Type*} [Fintype V] [DecidableEq V]
variable [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F] [Fintype I]
variable {inc : E → V → Prop} {j : F → V → Prop}
omit [DecidableEq V] [Fintype E] [Fintype F] [Fintype I] in
lemma mass_markedEquiv (e : E ≃ F) (he : ∀ a v,j (e a) v ↔ inc a v)
    (part : F → I → ℝ) (a : Marking.Marked (I:=I) inc) :
    Marking.mass j part (markedEquiv e he a)=Marking.mass inc (part ∘ e) a := by
  apply Fintype.prod_equiv (selectedEquiv e he a.1).symm
  intro x
  change part x.val ((markedEquiv e he a).2 x)=part (e ((selectedEquiv e he a.1).symm x).val) (a.2 ((selectedEquiv e he a.1).symm x))
  rw [←markedEquiv_mark e he a]
  simp only [Equiv.apply_symm_apply]
  congr 1
  exact (e.apply_symm_apply x.val).symm
lemma partitionWeight_pmEquiv (e : E ≃ F) (he : ∀ a v,j (e a) v ↔ inc a v)
    (w : F → ℝ) : partitionWeight j w univ=partitionWeight inc (w ∘ e) univ := by
  classical
  unfold partitionWeight
  symm
  apply Fintype.sum_equiv (pmEquiv e he)
  intro M
  exact (matchingWeight_pmEquiv e he w M).symm
lemma law_markedEquiv (e : E ≃ F) (he : ∀ a v,j (e a) v ↔ inc a v)
    (part : F → I → ℝ) (a : Marking.Marked (I:=I) inc) :
    Marking.law j part (markedEquiv e he a)=Marking.law inc (part ∘ e) a := by
  unfold Marking.law
  rw [mass_markedEquiv,partitionWeight_pmEquiv e he]
  rfl
end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_MarkBridge
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.RationalSource
open Finset Transport Variation Enlargement

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
attribute [local instance] OAI.MatchingFPRAS.RationalSource.instDecidableEqSourceLabelCastReal_1
noncomputable local instance instDecidableEqBagPMSourceVertexLabelBags_3_r2631ec_1 (w : V → V → ℚ) (K : ℕ) :
    DecidableEq (BagPM (bags w K)) := Classical.decEq _
lemma sourceEdgeEquiv_central (w : V → V → ℚ) (K : ℕ) (q : LogicalEdge V) :
    sourceEdgeEquiv w K (Enlargement.centralEdge (fun x y=>(w x y:ℝ)) K q)=centralEdge w K q :=
  sourceEdgeEquiv_real w K _
lemma probePortion_cast (w : V → V → ℚ) (K D : ℕ)
    (e : BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) :
    (probePortion w K D (sourceEdgeEquiv w K e):ℝ)=Enlargement.probePortion (fun x y=>(w x y:ℝ)) K D e := by
  classical
  have he : (∃ q,centralEdge w K q=sourceEdgeEquiv w K e) ↔
      ∃ q,Enlargement.centralEdge (fun x y=>(w x y:ℝ)) K q=e := by
    constructor
    · rintro ⟨q,hq⟩
      exact ⟨q,(sourceEdgeEquiv w K).injective ((sourceEdgeEquiv_central w K q).trans hq)⟩
    · rintro ⟨q,rfl⟩
      exact ⟨q,(sourceEdgeEquiv_central w K q).symm⟩
  simp only [probePortion,Enlargement.probePortion,he]
  split_ifs <;> push_cast <;> rfl
lemma portions_cast (w : V → V → ℚ) (K D : ℕ)
    (e : BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) (i : Fin 3) :
    (portions w K D (sourceEdgeEquiv w K e) i:ℝ)=sourcePortions (fun x y=>(w x y:ℝ)) K D e i := by
  fin_cases i
  · exact realPortion_cast w K e
  · change ((bagHeight w K (sourceEdgeEquiv w K e).color/D-probePortion w K D (sourceEdgeEquiv w K e):ℚ):ℝ)=_
    rw [Rat.cast_sub,Rat.cast_div,Rat.cast_natCast,probePortion_cast,sourceEdgeEquiv_color,bagHeight_cast]
    rfl
  · exact probePortion_cast w K D e
lemma portions_collapse (w : V → V → ℚ) (K D : ℕ) :
    Marking.collapse (fun e i=>(portions w K D e i:ℝ))=fun e=>(bagWeight w K D e:ℝ) := by
  funext e
  change (∑ i : Fin 3,(portions w K D e i:ℝ))=(bagWeight w K D e:ℝ)
  exact_mod_cast portions_sum w K D e
attribute [local instance] OAI.MatchingFPRAS.RationalSource.instFintypeBagEdgeSourceVertexSourceLabelCastRealSourceBags_1
lemma markedLaw_eq (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D : ℕ) (hD : 0<D)
    (a : Marked w K) :
    markedLaw w K D a=Marking.law BagEdge.Incident (fun e i=>(portions w K D e i:ℝ)) a := by
  have hc : ∀ e,Marking.collapse (fun e i=>(portions w K D e i:ℝ)) e≠0 := by
    intro e
    rw [portions_collapse]
    dsimp only
    exact_mod_cast (bagWeight_pos w hw K D hD e).ne'
  have h:=Marking.law_from_reveal BagEdge.Incident (fun e i=>(portions w K D e i:ℝ)) hc a
  rw [portions_collapse] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [markedLaw,Variation.sigmaLift,product,gibbs,matchingWeight,partition,Marking.conditional,
    portions_collapse,Rat.cast_div,partitionWeight]
  all_goals (try congr 3)
  all_goals (try ext)
  all_goals (try simp)
lemma markedLaw_equiv (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D : ℕ) (hD : 0<D)
    (a : SourceMarked (fun x y=>(w x y:ℝ)) K) :
    markedLaw w K D (sourceMarkedEquiv w K a)=sourceLaw (fun x y=>(w x y:ℝ)) K D a := by
  rw [markedLaw_eq w hw K D hD]
  change Marking.law BagEdge.Incident (fun e i=>(portions w K D e i:ℝ))
    (markedEquiv (inc:=BagEdge.Incident (bags:=sourceBags (fun x y=>(w x y:ℝ)) K))
    (j:=BagEdge.Incident (bags:=bags w K)) (sourceEdgeEquiv w K) (fun _ _=>Iff.rfl) a)=_
  rw [law_markedEquiv (inc:=BagEdge.Incident (bags:=sourceBags (fun x y=>(w x y:ℝ)) K))
    (j:=BagEdge.Incident (bags:=bags w K)) (sourceEdgeEquiv w K) (fun _ _=>Iff.rfl)]
  have hp : ((fun e i=>(portions w K D e i:ℝ)) ∘ sourceEdgeEquiv w K)=
        sourcePortions (fun x y=>(w x y:ℝ)) K D := by
    funext e i
    exact portions_cast w K D e i
  rw [hp]
  rfl
end MatchingFPRAS.RationalSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_RationalObservables
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport
open Finset

variable {V E F I : Type*} [Fintype V] [DecidableEq V]
variable [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F] [Fintype I]
variable {inc : E → V → Prop} {j : F → V → Prop}
omit [DecidableEq V] [Fintype E] [Fintype F] in
lemma markedEquiv_probe (e : E ≃ F) (he : ∀ a v,j (e a) v ↔ inc a v)
    (a : Marking.Marked (I:=Fin 3) inc) (u : E) :
    ({e u}⊆(markedEquiv e he a).1.val ∧
      (markedEquiv e he a).2=(fun x=>if x.val∈({e u}:Finset _) then 2 else 0)) ↔
    ({u}⊆a.1.val ∧ a.2=(fun x=>if x.val∈({u}:Finset _) then 2 else 0)) := by
  rw [markedEquiv_marks_eq e he a (fun x=>if x∈({e u}:Finset F) then 2 else 0)]
  rw [singleton_subset_iff,singleton_subset_iff]
  change (e u∈a.1.val.image e ∧ _) ↔ (u∈a.1.val ∧ _)
  simp only [mem_singleton,e.injective.eq_iff,
    mem_image,exists_eq_right]
omit [DecidableEq V] [Fintype E] [Fintype F] in
lemma pmEquiv_product_erase {R : Type*} [CommMonoid R]
    (e : E ≃ F) (he : ∀ a v,j (e a) v ↔ inc a v) (M : PM inc) (u : E) (f : F → R) :
    (∏ x ∈ (pmEquiv e he M).val \ {e u},f x)=∏ x ∈ M.val \ {u},f (e x) := by
  have hh : (pmEquiv e he M).val \ {e u}=(M.val \ {u}).image e := by
    change M.val.image e \ {e u}=(M.val \ {u}).image e
    ext x
    simp only [mem_sdiff,mem_image,mem_singleton]
    constructor
    · rintro ⟨⟨y,hy,rfl⟩,hu⟩
      exact ⟨y,⟨hy,fun h=>hu (congrArg e h)⟩,rfl⟩
    · rintro ⟨y,⟨hy,hu⟩,rfl⟩
      exact ⟨⟨y,hy,rfl⟩,fun h=>hu (e.injective h)⟩
  rw [hh]
  exact prod_image (fun _ _ _ _ h=>e.injective h)
end MatchingFPRAS.Transport
namespace MatchingFPRAS.RationalSource
open Finset Transport Variation Enlargement

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
attribute [local instance] OAI.MatchingFPRAS.RationalSource.instDecidableEqSourceLabelCastReal_3
lemma observableProbe_cast (w w₁ : V → V → ℚ) (K : ℕ) (u : LogicalEdge V)
    (a : SourceMarked (fun x y=>(w x y:ℝ)) K) :
    (observableProbe w w₁ K u (sourceMarkedEquiv w K a):ℝ)=
      Enlargement.observableProbe (fun x y=>(w x y:ℝ)) (fun x y=>(w₁ x y:ℝ)) K u a := by
  have hh:=markedEquiv_probe (inc:=BagEdge.Incident (bags:=sourceBags (fun x y=>(w x y:ℝ)) K))
    (j:=BagEdge.Incident (bags:=bags w K)) (sourceEdgeEquiv w K) (sourceEdgeEquiv_incidence w K) a
    (Enlargement.centralEdge (fun x y=>(w x y:ℝ)) K u)
  rw [sourceEdgeEquiv_central] at hh
  change ({centralEdge w K u}⊆(sourceMarkedEquiv w K a).1.val ∧
    (sourceMarkedEquiv w K a).2=(fun e=>if e.val∈({centralEdge w K u}:Finset _) then 2 else 0)) ↔ _ at hh
  simp only [observableProbe,Enlargement.observableProbe,hh]
  simp only [mem_singleton] at hh ⊢
  split_ifs <;> try contradiction
  · push_cast
    rw [←sourceEdgeEquiv_central w K u]
    change (∏ e ∈ (pmEquiv (inc:=BagEdge.Incident (bags:=sourceBags (fun x y=>(w x y:ℝ)) K))
    (j:=BagEdge.Incident (bags:=bags w K)) (sourceEdgeEquiv w K) (sourceEdgeEquiv_incidence w K) a.1).val \
      {sourceEdgeEquiv w K (Enlargement.centralEdge (fun x y=>(w x y:ℝ)) K u)},
      (bagReweight w w₁ K e:ℝ))=_
    rw [pmEquiv_product_erase (sourceEdgeEquiv w K) (sourceEdgeEquiv_incidence w K)]
    refine prod_congr (by ext; simp) ?_
    intro e _
    exact bagReweight_cast w w₁ K e
  · norm_cast
end MatchingFPRAS.RationalSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_RationalScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Counting
open Finset

variable {n : ℕ}
lemma rowMaximum_cast (hn : 2≤n) (G : Fin n → Fin n → ℚ) (v : Fin n → ℚ) (i : Fin n) :
    (rowMaximum hn G v i:ℝ)=RealStage.rowMaximum hn (fun i j=>(G i j:ℝ)) (fun i=>(v i:ℝ)) i := by
  unfold rowMaximum RealStage.rowMaximum
  rw [Finset.apply_sup'_eq_sup'_comp _ (fun q : ℚ=>(q:ℝ)) (by intro a b; exact Rat.cast_max a b)]
  simp only [Function.comp_apply,Rat.cast_div]
lemma scaleUpdate_cast (hn : 2≤n) (G : Fin n → Fin n → ℚ) (v : Fin n → ℚ) (i j : Fin n) :
    (scaleUpdate hn G v i j:ℝ)=RealStage.scaleUpdate hn (fun i j=>(G i j:ℝ)) (fun i=>(v i:ℝ)) i j := by
  by_cases h : j=i
  · subst j
    simp only [scaleUpdate,RealStage.scaleUpdate,Function.update_self,rowMaximum_cast]
  · simp only [scaleUpdate,RealStage.scaleUpdate,Function.update_of_ne h]
lemma scalingTrace_cast (hn : 2≤n) (G : Fin n → Fin n → ℚ) (k : ℕ) (i : Fin n) :
    (scalingTrace hn G k i:ℝ)=RealStage.scalingTrace hn (fun i j=>(G i j:ℝ)) k i := by
  induction k generalizing i with
  | zero => norm_num [scalingTrace,RealStage.scalingTrace]
  | succ k ih =>
    simp only [scalingTrace,RealStage.scalingTrace]
    split_ifs with h
    · rw [scaleUpdate_cast]
      have hi : (fun j=>(Counting.scalingTrace hn G k j:ℝ))=RealStage.scalingTrace hn (fun i j=>(G i j:ℝ)) k := by
        funext j
        exact ih j
      rw [hi]
    · exact ih i
lemma upperEstimate_cast (D : ℕ) (d z : ℚ) :
    (upperEstimate D d z:ℝ)=RealStage.upperEstimate D d z := by
  simp only [upperEstimate,RealStage.upperEstimate]
  have hp : (0:ℝ)<d ↔ (0:ℚ)<d := by exact_mod_cast Iff.rfl
  simp only [hp]
  split_ifs <;> push_cast <;> norm_num [alpha,RealStage.alpha]
end MatchingFPRAS.Counting

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_RationalEstimator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.FiniteTrial
open Finset Enlargement Transport

variable {V : Type*} [LinearOrder V]
lemma estimateMatrix_cast (D : ℕ) (dbar : ℚ) (zbar : LogicalEdge V → ℚ) (i j : V) :
    (estimateMatrix D dbar zbar i j:ℝ)=Enlargement.estimateMatrix D dbar (fun e=>(zbar e:ℝ)) i j := by
  rw [estimateMatrix,Counting.upperEstimate_cast,probeMatrix_cast]
  rfl

variable {G : GraphInput} {j K S : ℕ} [Nontrivial (Fin G.n)]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance instDecidableEqSourceLabelFinNCastReal_r2631ec_1 (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
omit [Nontrivial (Fin G.n)] in
lemma sourceD_eq (K : ℕ) : sourceD (G:=G) K=Enlargement.sourceD (V:=Fin G.n) K := by
  simp only [sourceD,Enlargement.sourceD,Fintype.card_fin]

lemma ScaleState.update_activity (hn : 2≤G.n) (s : ScaleState G j)
    (x : Fin S → RationalSource.Marked s.activity K) :
    (s.update hn x).activity=(fun a b=>s.nextActivity a b*s.updateVector hn x a*s.updateVector hn x b) := by
  funext a b
  simp only [ScaleState.activity,ScaleState.update,ScaleState.nextActivity]
  ring

lemma average_Probe (w w₁ : Fin G.n → Fin G.n → ℚ) (K : ℕ) (e : LogicalEdge (Fin G.n))
    (x : Fin S → SourceMarked (fun a b=>(w a b:ℝ)) K) :
    (sampleAverage (RationalSource.observableProbe w w₁ K e) (RationalSource.sourceMarkedEquiv w K ∘ x):ℝ)=
      Enlargement.sampleAverage (Enlargement.observableProbe (fun a b=>(w a b:ℝ)) (fun a b=>(w₁ a b:ℝ)) K e) x := by
  simp only [sampleAverage,Enlargement.sampleAverage,Rat.cast_div,Rat.cast_sum,Rat.cast_natCast,Function.comp_apply,
    RationalSource.observableProbe_cast]
lemma ScaleState.matrix_cast (s : ScaleState G j)
    (x : Fin S → SourceMarked (fun a b=>(s.activity a b:ℝ)) K) :
    (fun a b=>(s.matrix (RationalSource.sourceMarkedEquiv s.activity K ∘ x) a b:ℝ))=
      Enlargement.estimateMatrix (sourceD (G:=G) K)
        (Enlargement.sampleAverage (Enlargement.observableD (fun a b=>(s.activity a b:ℝ))
          (fun a b=>(s.nextActivity a b:ℝ)) K) x)
        (fun e=>Enlargement.sampleAverage (Enlargement.observableProbe (fun a b=>(s.activity a b:ℝ))
          (fun a b=>(s.nextActivity a b:ℝ)) K e) x) := by
  funext a b
  simp only [ScaleState.matrix,estimateMatrix_cast,average_D,average_Probe]
end MatchingFPRAS.FiniteTrial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_FiniteStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Variation
open Finset

lemma sum_instances {A : Type*} (F₁ F₂ : Fintype A) (p : A → ℝ) :
    (letI:=F₁; ∑ a,p a)=(letI:=F₂; ∑ a,p a) := by
  cases Subsingleton.elim F₁ F₂
  rfl
lemma imageLaw_output_equiv {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (e : B ≃ C) (f : A → B) : imageLaw (e ∘ f)=imageLaw f ∘ e.symm := by
  classical
  funext c
  unfold imageLaw push
  apply sum_congr rfl
  intro a _
  simp only [Function.comp_apply,←Equiv.eq_symm_apply]
end MatchingFPRAS.Variation

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_RationalUpdate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.FiniteTrial
open Finset Enlargement Transport Switching

variable {G : GraphInput} {j K S : ℕ} [Nontrivial (Fin G.n)]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance instDecidableEqSourceLabelFinNCastReal_1_r2631ec_1 (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
omit [Nontrivial (Fin G.n)] in
lemma initial_balanced (hn : 2≤G.n) (he : Even G.n) : (initialScaleState G hn).Balanced hn :=
  Trial.initial_balanced G hn he

theorem successful_update (p : Trial.Parameters G) (hj : j≤p.K) (s : ScaleState G j)
    (hs : s.Balanced p.hn) (x : Fin S → SourceMarked (fun a b=>(s.activity a b:ℝ)) p.K)
    (hx : StageGood (fun a b=>(s.activity a b:ℝ)) (fun a b=>(s.nextActivity a b:ℝ)) p.K p.sigma x) :
    (s.update p.hn (RationalSource.sourceMarkedEquiv s.activity p.K ∘ x)).Balanced p.hn ∧
      |(s.ratioEstimate (RationalSource.sourceMarkedEquiv s.activity p.K ∘ x):ℝ)/
        (partition (Trial.raw G (j+1)) ∅/partition (Trial.raw G j) ∅)-1|≤(p.epsilon:ℝ)/(100*p.K) := by
  let c:=stageData p hj s hs
  let obs : EmpiricalData c:=empiricalData c x hx
  have hh:=actual_successful_stage c obs
  dsimp only at hh
  let y:=RationalSource.sourceMarkedEquiv s.activity p.K ∘ x
  have hm : (fun a b=>(s.matrix y a b:ℝ))=Enlargement.estimateMatrix (Enlargement.sourceD (V:=Fin G.n) p.K) obs.dbar obs.zbar := by
    rw [s.matrix_cast,sourceD_eq]
    rfl
  have hv : (fun i=>(s.updateVector p.hn y i:ℝ))=
      RealStage.scalingTrace c.hn (Enlargement.estimateMatrix (Enlargement.sourceD (V:=Fin G.n) p.K) obs.dbar obs.zbar) G.n := by
    funext i
    rw [ScaleState.updateVector,Counting.scalingTrace_cast,hm]
  constructor
  · unfold ScaleState.Balanced Trial.ScaleState.Balanced
    rw [←ScaleState.activity_cast,ScaleState.update_activity]
    have ha : (fun a b=>((s.nextActivity a b*s.updateVector p.hn y a*s.updateVector p.hn y b:ℚ):ℝ))=
        (fun a b=>c.next a b*(RealStage.scalingTrace c.hn (Enlargement.estimateMatrix
          (Enlargement.sourceD (V:=Fin G.n) p.K) obs.dbar obs.zbar) G.n a)*
          (RealStage.scalingTrace c.hn (Enlargement.estimateMatrix
          (Enlargement.sourceD (V:=Fin G.n) p.K) obs.dbar obs.zbar) G.n b)) := by
      funext a z
      simp only [Rat.cast_mul,congrFun hv]
      rfl
    rw [ha]
    exact ⟨fun i=>(hh.2.1 i).1,fun i=>(hh.2.1 i).2⟩
  · rw [s.ratioEstimate_cast]
    have hr : partition c.next ∅/partition c.w ∅=
        partition (Trial.raw G (j+1)) ∅/partition (Trial.raw G j) ∅ := by
      change partition (fun a b=>(s.nextActivity a b:ℝ)) ∅/partition (fun a b=>(s.activity a b:ℝ)) ∅=_
      rw [s.nextActivity_cast,s.activity_cast,s.toReal.ratio]
    rw [←hr]
    exact hh.2.2

end MatchingFPRAS.FiniteTrial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_FiniteTrial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.FiniteTrial
open Finset Switching Transport Enlargement Adaptive Initializer
open scoped Classical

variable {G : GraphInput} [Nontrivial (Fin G.n)]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder

attribute [instance] Layer.finite

noncomputable local instance instDecidableEqSourceLabelFinNCastReal_2_r2631ec_1 (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
theorem Layer.append_good (p : Trial.Parameters G) {j : ℕ} (hj : j ≤ p.K) (L : Layer p j) (x : L.Ω)
    (hx : L.good p x) (y : Fin p.S → SourceMarked (fun a b=>((L.state x).activity a b:ℝ)) p.K)
    (hy : StageGood (fun a b=>((L.state x).activity a b:ℝ)) (fun a b=>((L.state x).nextActivity a b:ℝ)) p.K p.sigma y) :
    (L.append p hj).good p ⟨x,y⟩ := by
  have h := successful_update p hj (L.state x) hx.1 y hy
  refine ⟨h.1,?_⟩
  intro i
  refine Fin.lastCases ?_ (fun i=>?_) i
  · simpa [Layer.append] using h.2
  · simpa [Layer.append] using hx.2 i

attribute [local instance] OAI.MatchingFPRAS.FiniteTrial.instFintypeSourceMarkedFinNCastReal_1
theorem Layer.append_failure (p : Trial.Parameters G) {j : ℕ} (hj : j ≤ p.K) (L : Layer p j) :
    (L.append p hj).law.event (fun x=>¬(L.append p hj).good p x) ≤
      L.law.event (fun x=>¬L.good p x)+13/(1000*p.K) := by
  apply first_failure_sigma L.law (fun x=>(L.state x).sampleLaw p hj) (L.good p)
    ((L.append p hj).good p) _ (by positivity)
  intro x hx
  apply le_trans ((L.state x).sampleLaw p hj |>.event_mono ?_)
    ((L.state x).sampleLaw_budget p hj).le
  intro y hy hgood
  exact hy (L.append_good p hj x hx y hgood)

theorem layers_failure (p : Trial.Parameters G) (j : ℕ) (hj : j ≤ p.K) :
    (layers p j hj).law.event (fun x=>¬(layers p j hj).good p x) ≤ j*(13/(1000*p.K)) := by
  induction j with
  | zero =>
    have hg : ∀ x,(firstLayer p).good p x := by
      intro x
      constructor
      · exact initial_balanced p.hn p.even
      · intro i; exact Fin.elim0 i
    simp [layers,Law.event,hg]
  | succ j ih =>
    refine le_trans ((layers p j (by omega)).append_failure p (by omega)) ?_
    calc
      _ ≤ (j:ℝ)*(13/(1000*p.K))+13/(1000*p.K) := by linarith only [ih (by omega)]
      _ = _ := by push_cast; ring

lemma output_nonneg (p : Trial.Parameters G) (x : (layers p p.K le_rfl).Ω) : 0 ≤ output p x := by
  apply mul_nonneg (Nat.cast_nonneg _)
  exact prod_nonneg fun i _=>(layers p p.K le_rfl).ratios_nonneg x i

theorem good_output (p : Trial.Parameters G) (hZ : 0<Z G) (x : (layers p p.K le_rfl).Ω)
    (hx : (layers p p.K le_rfl).good p x) : Accurate p (output p x) := by
  have h:=Trial.final_trial_interval G p.even p.epsilon p.epsilon_pos p.epsilon_lt_one p.K p.schedule hZ
    (fun i=>((layers p p.K le_rfl).ratios x i:ℝ)) hx.2
  unfold Accurate output
  dsimp only at h
  exact_mod_cast h

end MatchingFPRAS.FiniteTrial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_SortedList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Amplification
open Finset

variable {k : ℕ}

lemma sortedValue_monotone (x : Fin (2*k+1) → ℚ) : Monotone (sortedValue x) := by
  intro i j hij
  exact ((List.ofFn x).sortedLE_mergeSort).getElem_le_getElem_of_le hij

lemma ofFn_sortedValue (x : Fin (2*k+1) → ℚ) : List.ofFn (sortedValue x)=sortedList x := by
  apply List.ext_getElem
  · simp [sortedList_length]
  · intro i hi hj
    rw [List.getElem_ofFn]
    rfl

lemma majority_sorted (f : Fin (2*k+1) → ℚ) (hf : Monotone f) (a b : ℚ)
    (h : k < (univ.filter fun i => a ≤ f i ∧ f i ≤ b).card) :
    a ≤ f ⟨k,by omega⟩ ∧ f ⟨k,by omega⟩ ≤ b := by
  let z : Fin (2*k+1) := ⟨k,by omega⟩
  constructor
  · by_contra hc
    have hc' : f z < a := lt_of_not_ge hc
    have hs : (univ.filter fun i => a ≤ f i ∧ f i ≤ b) ⊆ Ioi z := by
      intro i hi
      apply mem_Ioi.mpr
      by_contra hnot
      have hlow := (mem_filter.mp hi).2.1
      have hm := hf (le_of_not_gt hnot)
      exact (not_lt_of_ge (hlow.trans hm)) hc'
    have hh := card_le_card hs
    rw [Fin.card_Ioi] at hh
    dsimp [z] at hh
    omega
  · by_contra hc
    have hc' : b < f z := lt_of_not_ge hc
    have hs : (univ.filter fun i => a ≤ f i ∧ f i ≤ b) ⊆ Iio z := by
      intro i hi
      apply mem_Iio.mpr
      by_contra hnot
      have hupp := (mem_filter.mp hi).2.2
      have hm := hf (le_of_not_gt hnot)
      exact (not_lt_of_ge (hm.trans hupp)) hc'
    have hh := card_le_card hs
    rw [Fin.card_Iio] at hh
    dsimp [z] at hh
    omega

lemma good_count (x : Fin (2*k+1) → ℚ) (a b : ℚ) :
    (univ.filter fun i => a ≤ x i ∧ x i ≤ b).card=
      ((List.ofFn x).map (fun q => if a ≤ q ∧ q ≤ b then 1 else 0)).sum := by
  rw [List.map_ofFn,List.sum_ofFn]
  exact Finset.card_filter _ _

lemma sorted_good_count (x : Fin (2*k+1) → ℚ) (a b : ℚ) :
    (univ.filter fun i => a ≤ sortedValue x i ∧ sortedValue x i ≤ b).card=
      (univ.filter fun i => a ≤ x i ∧ x i ≤ b).card := by
  rw [good_count,good_count,ofFn_sortedValue]
  exact ((List.mergeSort_perm (List.ofFn x) (· ≤ ·)).map _).sum_eq

theorem median_majority (x : Fin (2*k+1) → ℚ) (a b : ℚ)
    (h : k < (univ.filter fun i => a ≤ x i ∧ x i ≤ b).card) :
    a ≤ median x ∧ median x ≤ b := by
  apply majority_sorted (sortedValue x) (sortedValue_monotone x) a b
  rwa [sorted_good_count]

open Finset MatchingFPRAS.Adaptive MatchingFPRAS.Transport
open scoped Classical

variable {Ω : Type*} [Fintype Ω]

omit [Fintype Ω] in
lemma product_bad (r : ℕ) (B : Ω → Prop) (x : Fin r → Ω) :
    (∏ i : Fin r, (if B (x i) then (10:ℝ) else 1)) =
      (10:ℝ)^(univ.filter fun i=>B (x i)).card := by
  rw [← prod_filter]
  simp

lemma product_moment (μ : Law Ω) (r : ℕ) (B : Ω → Prop) :
    ∑ x : Fin r → Ω,(μ.iid r) x * (∏ i,if B (x i) then (10:ℝ) else 1) =
      (1+9*μ.event B)^r := by
  have he : (∑ x : Ω, μ x*(if B x then (10:ℝ) else 1))=1+9*μ.event B := by
    calc
      _ = ∑ x : Ω, (μ x+9*(if B x then μ x else 0)) := by
        apply sum_congr rfl
        intro x _
        split_ifs <;> ring
      _ = _ := by rw [sum_add_distrib,←mul_sum,μ.total]; rfl
  change (∑ x : Fin r → Ω,(∏ i,μ (x i)) * ∏ i,if B (x i) then (10:ℝ) else 1) = _
  simp_rw [←prod_mul_distrib]
  rw [←Fintype.prod_sum (fun (_ : Fin r) (x : Ω)=>μ x*(if B x then (10:ℝ) else 1))]
  simp only [he,prod_const,card_univ,Fintype.card_fin]

lemma majority_tail (μ : Law Ω) (B : Ω → Prop) (hB : μ.event B≤1/10) (k : ℕ) :
    (μ.iid (2*k+1)).event (fun x=>k<(univ.filter fun i=>B (x i)).card) ≤ (2:ℝ)⁻¹^k := by
  have hM : (10:ℝ)^(k+1) * (μ.iid (2*k+1)).event
      (fun x=>k<(univ.filter fun i=>B (x i)).card) ≤ (1+9*μ.event B)^(2*k+1) := by
    rw [←product_moment μ (2*k+1) B]
    unfold Law.event
    rw [mul_sum]
    apply sum_le_sum
    intro x _
    rw [product_bad]
    split_ifs with hx
    · exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega))
        ((μ.iid (2*k+1)).nonneg x) |>.trans_eq (mul_comm _ _)
    · rw [mul_zero]
      exact mul_nonneg ((μ.iid (2*k+1)).nonneg x) (by positivity)
  have hn : 0≤1+9*μ.event B := by have := μ.event_nonneg B; linarith
  have hu : (1+9*μ.event B)^(2*k+1) ≤ (2:ℝ)^(2*k+1) :=
    pow_le_pow_left₀ hn (by linarith) _
  have hdiv : (μ.iid (2*k+1)).event (fun x=>k<(univ.filter fun i=>B (x i)).card) ≤ (2:ℝ)^(2*k+1)/10^(k+1) := (le_div_iff₀ (by positivity : (0:ℝ)<10^(k+1))).mpr (by rw [mul_comm]; exact hM.trans hu)
  apply hdiv.trans
  calc
    (2:ℝ)^(2*k+1)/10^(k+1) = (1/5:ℝ)*(4/10)^k := by
      rw [pow_add,pow_add,pow_mul]
      simp only [pow_one]
      rw [div_mul_eq_div_mul_one_div,div_pow]
      ring
    _ ≤ (1/2:ℝ)^k := by
      have hpow : (4/10:ℝ)^k ≤ (1/2:ℝ)^k := pow_le_pow_left₀ (by norm_num) (by norm_num) _
      calc
        _ ≤ (1:ℝ)*(4/10)^k := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
        _ ≤ _ := by simpa using hpow
    _ = _ := by norm_num

lemma median_failure (μ : Law Ω) (out : Ω → ℚ) (a b : ℚ)
    (h : μ.event (fun x=>¬(a≤out x ∧ out x≤b))≤1/10) (k : ℕ) :
    (μ.iid (2*k+1)).event (fun x=>¬(a ≤ median (fun i=>out (x i)) ∧ median (fun i=>out (x i))≤b))
      ≤ (2:ℝ)⁻¹^k := by
  apply (Law.event_mono _ (fun x hx=>?_)).trans (majority_tail μ (fun y=>¬(a≤out y ∧ out y≤b)) h k)
  by_contra hh
  have hb := not_lt.mp hh
  have hs := card_filter_add_card_filter_not (s:=univ) (p:=fun i : Fin (2*k+1)=>a≤out (x i) ∧ out (x i)≤b)
  simp only [card_univ,Fintype.card_fin] at hs
  apply hx
  apply median_majority (k:=k) (fun i=>out (x i)) a b
  have hc : (univ.filter fun i : Fin (2*k+1)=>¬(a≤out (x i) ∧ out (x i)≤b)).card ≤ k := by
    convert hb using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext i
    simp
  omega

omit [Fintype Ω] in
lemma median_nonneg {k : ℕ} (out : Fin (2*k+1) → ℚ) (h : ∀ i,0≤out i) : 0 ≤ median out := by
  unfold median sortedValue
  have hp := List.mergeSort_perm (List.ofFn out) (· ≤ ·)
  have hx : (sortedList out)[k]'(by rw [sortedList_length]; omega) ∈ List.ofFn out :=
    hp.mem_iff.mp (List.getElem_mem _)
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hx
  rw [←hi]
  exact h i

open Finset MatchingFPRAS.Adaptive
open scoped Classical

lemma amplification_precision (δ : ℚ) (hδ : 0<δ) : (2:ℝ)⁻¹^(halfRepetitions δ)≤(δ:ℝ) := by
  let m := Nat.clog 2 ⌈δ⁻¹⌉₊
  have hc : (δ:ℝ)⁻¹≤(⌈δ⁻¹⌉₊:ℝ) := by
    exact_mod_cast Nat.le_ceil (δ⁻¹)
  have hp : (⌈δ⁻¹⌉₊:ℝ)≤(2:ℝ)^m := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1<2) ⌈δ⁻¹⌉₊
  have hd : (0:ℝ)<δ := by exact_mod_cast hδ
  have hh : (2:ℝ)⁻¹^m≤(δ:ℝ) := by
    rw [inv_pow]
    apply (inv_le_iff_one_le_mul₀ (by positivity)).mpr
    nlinarith [hc.trans hp,inv_pos.mpr hd,mul_inv_cancel₀ hd.ne']
  apply (pow_le_pow_of_le_one (by norm_num : (0:ℝ)≤2⁻¹) (by norm_num) (show m≤halfRepetitions δ by dsimp [m,halfRepetitions]; omega)).trans hh

variable {Ω : Type*} [Fintype Ω]
lemma median_delta (μ : Law Ω) (out : Ω → ℚ) (a b : ℚ)
    (h : μ.event (fun x=>¬(a≤out x ∧ out x≤b))≤1/10) (δ : ℚ) (hδ : 0<δ) :
    (μ.iid (2*halfRepetitions δ+1)).event
      (fun x=>¬(a≤ median (fun i=>out (x i)) ∧ median (fun i=>out (x i))≤b)) ≤ (δ:ℝ) :=
  (median_failure μ out a b h _).trans (amplification_precision δ hδ)
end MatchingFPRAS.Amplification

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_OutputLengthBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Variation
open Transport

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
omit [Fintype C] in
lemma imageLaw_ignore_right [Nonempty B] (f : A → C) :
    imageLaw (fun x : A×B=>f x.1)=imageLaw f := by
  have hh:=imageLaw_comp_equiv (Equiv.prodComm A B) (fun x : B×A=>f x.2)
  exact hh.trans (imageLaw_ignore f)
omit [Fintype A] in
lemma padSampler_law {k B : ℕ} (h : k≤B) (f : (Fin k → Bool) → A) :
    imageLaw (padSampler h f)=imageLaw f :=
  (imageLaw_comp_equiv (paddedBits h) (fun x=>f x.1)).trans (imageLaw_ignore_right f)
end MatchingFPRAS.Variation
namespace MatchingFPRAS.RationalSource
open Transport Enlargement Variation

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance instDecidableEqSourceLabelCastReal_4_r2631ec_1 (w : V → V → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
attribute [local instance] OAI.MatchingFPRAS.RationalSource.instFintypeBagEdgeSourceVertexSourceLabelCastRealSourceBags_4
noncomputable local instance instDecidableEqBagPMSourceVertexLabelBags_5_r2631ec_1 (w : V → V → ℚ) (K : ℕ) :
    DecidableEq (BagPM (bags w K)) := Classical.decEq _
attribute [local instance] OAI.MatchingFPRAS.RationalSource.instFintypeMarked_2
attribute [local instance] OAI.MatchingFPRAS.RationalSource.instFintypeSourceMarkedCastReal_2
attribute [local instance] OAI.MatchingFPRAS.RationalSource.instFintypeProdForallFinBoolForallBagEdgeSourceVertexLabelBags_1
lemma bitSampler_law (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D m : ℕ)
    (hD : 0<D) (hN : 0<Fintype.card (SourceVertex V K))
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K)
    (hq : 0<ladderQ (Fintype.card (SourceVertex V K)) D) (M : BagPM (bags w K)) (η : ℚ) :
    imageLaw (bitSampler w hw K D m hD hN h hq M η)=finiteSourceLaw w hw K D m hD hN h hq M η := by
  dsimp only [bitSampler,samplerBitCount]
  erw [←Function.comp_assoc,imageLaw_comp_equiv,imageLaw_output_equiv]
  rfl
lemma fixedSampler_law (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D m : ℕ)
    (hD : 0<D) (hN : 0<Fintype.card (SourceVertex V K))
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K)
    (hq : 0<ladderQ (Fintype.card (SourceVertex V K)) D) (M : BagPM (bags w K)) (η : ℚ) :
    imageLaw (fixedSampler w hw K D m hD hN h hq M η)=finiteSourceLaw w hw K D m hD hN h hq M η := by
  rw [fixedSampler,padSampler_law,bitSampler_law]
end MatchingFPRAS.RationalSource

namespace MatchingFPRAS.Variation
open Finset
open scoped Classical

variable {A B X Y : Type*} [Fintype A] [Fintype B] [Fintype X]
variable {E : X → Type*} [∀ x,Fintype (E x)]
omit [∀ x,Fintype (E x)] in
lemma imageLaw_sigma_pair (f : A → X) (g : ∀ x,B → E x) :
    imageLaw (fun z : A×B=>(⟨f z.1,g (f z.1) z.2⟩ : Sigma E))=
      sigmaLift (imageLaw f) (fun x=>imageLaw (g x)) := by
  rw [imageLaw_adaptive_pair f (fun x b=>(⟨x,g x b⟩ : Sigma E))]
  funext ⟨x,y⟩
  unfold bind sigmaLift
  dsimp only
  have he : imageLaw (fun b=>(⟨x,g x b⟩ : Sigma E)) ⟨x,y⟩=imageLaw (g x) y := by
    unfold imageLaw push
    simp only [Sigma.mk.inj_iff,heq_eq_eq,true_and]
  rw [←he]
  apply sum_eq_single x
  · intro a _ ha
    have hz : imageLaw (fun b=>(⟨a,g a b⟩ : Sigma E)) ⟨x,y⟩=0 := by
      unfold imageLaw push
      apply sum_eq_zero
      intro b _
      exact ite_eq_right (fun hh=>ha (congrArg Sigma.fst hh))
    rw [hz,mul_zero]
  · simp
end MatchingFPRAS.Variation

namespace MatchingFPRAS.FiniteTrial
open Transport Enlargement Variation Adaptive

variable {G : GraphInput} [Nontrivial (Fin G.n)]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance instDecidableEqSourceLabelFinNCastReal_4_r2631ec_1 (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
attribute [local instance] OAI.MatchingFPRAS.FiniteTrial.instFintypeSourceMarkedFinNCastReal_3
lemma ScaleState.drawOne_law (p : Trial.Parameters G) {j : ℕ} (hj : j≤p.K) (s : ScaleState G j) :
    imageLaw (s.drawOne p hj)=(s.runLaw p hj).mass := by
  exact RationalSource.fixedSampler_law _ _ _ _ _ _ _ _ _ _ _
lemma ScaleState.drawStage_law (p : Trial.Parameters G) {j : ℕ} (hj : j≤p.K) (s : ScaleState G j) :
    imageLaw (s.drawStage p hj)=(s.sampleLaw p hj).mass := by
  unfold ScaleState.drawStage
  erw [imageLaw_comp_equiv,imageLaw_componentwise]
  rw [ScaleState.drawOne_law]
  rfl

open Transport Enlargement Variation Adaptive

variable {G : GraphInput} [Nontrivial (Fin G.n)]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance instDecidableEqSourceLabelFinNCastReal_5_r2631ec_1 (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
noncomputable local instance instFintypeSourceMarkedFinNCastReal_4_r2631ec_1 (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    Fintype (SourceMarked (fun x y=>(w x y:ℝ)) K) := Fintype.ofFinite _
lemma Layer.drawAppend_law (p : Trial.Parameters G) {j : ℕ} (hj : j≤p.K)
    (L : Layer p j) {a : ℕ} (f : (Fin a → Bool) → L.Ω) (hf : imageLaw f=L.law.mass) :
    imageLaw (L.drawAppend p hj f)=(L.append p hj).law.mass := by
  change imageLaw ((fun b : (Fin a → Bool) × (Fin (stageBits p) → Bool) =>
    (⟨f b.1,(L.state (f b.1)).drawStage p hj b.2⟩ :
      Σ x : L.Ω, Fin p.S → SourceMarked (fun v w=>((L.state x).activity v w:ℝ)) p.K)) ∘
    pairBitsEquiv a (stageBits p)) = _
  erw [imageLaw_comp_equiv]
  change imageLaw _ = sigmaLift L.law.mass (fun x=>(L.state x).sampleLaw p hj |>.mass)
  rw [imageLaw_sigma_pair f (fun x=>(L.state x).drawStage p hj)]
  simp_rw [ScaleState.drawStage_law]
  rw [hf]
lemma drawLayer_law (p : Trial.Parameters G) (j : ℕ) (hj : j≤p.K) :
    imageLaw (drawLayer p j hj)=(layers p j hj).law.mass := by
  induction j with
  | zero =>
    change imageLaw (fun _ : Fin (0*stageBits p) → Bool=>PUnit.unit)=(firstLayer p).law.mass
    rw [imageLaw_subsingleton]
    funext x
    simp [uniform,firstLayer]
  | succ j ih =>
    unfold drawLayer
    erw [imageLaw_comp_equiv]
    exact Layer.drawAppend_law p (by omega) (layers p j (by omega)) _ (ih (by omega))
end MatchingFPRAS.FiniteTrial

namespace MatchingFPRAS.Variation
open Finset
open scoped Classical

variable {A B : Type*} [Fintype A] [Fintype B]
lemma event_push (p : A → ℝ) (f : A → B) (P : B → Prop) :
    event (push p f) P=event p (fun x=>P (f x)) := by
  unfold event push
  have h : (∑ y,if P y then ∑ x,if f x=y then p x else 0 else 0)=
      ∑ y,∑ x,if f x=y then (if P y then p x else 0) else 0 := by
    apply sum_congr rfl
    intro y _
    by_cases hy:P y <;> simp [hy]
  rw [h,sum_comm]
  simp
lemma event_imageLaw (f : A → B) (P : B → Prop) :
    event (imageLaw f) P=((univ.filter (fun x=>P (f x))).card:ℝ)/Fintype.card A := by
  rw [imageLaw,event_push]
  unfold event uniform
  rw [show (∑ x,if P (f x) then (1:ℝ)/Fintype.card A else 0)=
    (∑ x,if P (f x) then (1:ℝ) else 0)/Fintype.card A by
      simp only [sum_div,ite_div,zero_div]]
  simp
lemma event_complement (p : A → ℝ) (P : A → Prop) :
    event p P+event p (fun x=>¬P x)=∑ x,p x := by
  unfold event
  rw [←sum_add_distrib]
  apply sum_congr rfl
  intro x _
  by_cases hx:P x <;> simp [hx]
end MatchingFPRAS.Variation

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_Guard
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.WeightedOptions
open Finset FiniteChoice

lemma draw_law_pos {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (c : WeightedOptions Ω) (k : ℕ) (bits : Fin k → Bool) :
    0 < c.law (c.draw k bits) := by
  let i := chooseBits c.mass c.total k bits
  have hi : 0 < c.mass i := chooseBits_pos c.mass c.total k bits
  apply hi.trans_le
  unfold law
  calc
    c.mass i = (if c.out i = c.draw k bits then c.mass i else 0) := by simp [draw, i]
    _ ≤ ∑ j, if c.out j = c.draw k bits then c.mass j else 0 :=
      single_le_sum (f := fun j => if c.out j = c.draw k bits then c.mass j else 0)
        (fun j _ => by split_ifs <;> [exact c.nonneg j; exact le_rfl]) (mem_univ i)

end MatchingFPRAS.WeightedOptions

namespace MatchingFPRAS.Enlargement
open Finset Switching Subdivision RealGeometry MatchingFPRAS.Representation

theorem intact_partition_identity_even {V : Type*} [Fintype V] [LinearOrder V]
    (he : Even (Fintype.card V)) (w : V → V → ℝ)
    (p : ℕ) (B Hu Hv : LogicalEdge V → ℝ) :
    realHolePartition source target (4*p) ∅ (fun _ => ∅)
      (pathActivity p B Hu Hv (logicalActivity w)) =
      (∏ e, pathConstant p (B e) (Hu e) (Hv e)) * partition w ∅ := by
  classical
  have hz := StageAnalysis.partition_pos_of_even (fun _ _ : V => (1:ℝ)) (by intros; norm_num) ∅
    (by simpa using he)
  have hn : (matchings (∅ : Finset V)).Nonempty := by
    by_contra hn
    have hz0 : partition (fun _ _ : V => (1:ℝ)) ∅ = 0 := by
      simp [partition, Finset.not_nonempty_iff_eq_empty.mp hn]
    linarith
  obtain ⟨m, hm⟩ := hn
  let b := fun (e : LogicalEdge V) (i : Fin (4*p+1)) => alternating (select m e) i.val
  have hb := intact_family p m ((mem_matchings m ∅).mp hm)
  have hid := deletion_partition_identity (show Even (4*p) from ⟨2*p,by omega⟩)
    source target ∅ (fun _ => ∅) b hb (pathActivity p B Hu Hv (logicalActivity w))
    (fun e => List.ofFn fun r : Fin p => max (B e) (Hu e/2^r.val))
    (fun e => (List.ofFn fun r : Fin p => max (B e) (Hv e/2^r.val)).reverse) _
    (fun e => profileActivity_ofFn p (B e) (Hu e) (Hv e) (logicalActivity w e))
  simpa [residualHoles, broken, deletionConstant, List.prod_ofFn, pathConstant,
    logical_partition_eq] using hid

open Transport
open scoped Classical

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

attribute [local instance] OAI.MatchingFPRAS.Enlargement.instDecidableEqSourceLabel_11
attribute [local instance] OAI.MatchingFPRAS.Enlargement.instFintypeBagEdgeSourceVertexSourceLabelSourceBags_12
theorem frozenPortion_full_even (he : Even (Fintype.card V))
    (w w₁ : V → V → ℝ) (K : ℕ) :
    Transport.partitionWeight BagEdge.Incident (frozenPortion w w₁ K) Finset.univ =
      sourceC w K * Switching.partition w₁ ∅ := by
  rw [←survivors_empty (V:=V) K, frozenPortion_partition,
    intact_partition_identity_even he w₁]
  rfl

theorem observableD_mean_even (he : Even (Fintype.card V))
    (w w₁ : V → V → ℝ) (hw : ∀ x y, 0 < w x y) (K D : ℕ) :
    (∑ a : SourceMarked w K, sourceLaw w K D a * observableD w w₁ K a) =
      sourceC w K * Switching.partition w₁ ∅ / sourceBagZ w K D := by
  classical
  have h := Marking.allReal_mean BagEdge.Incident (sourcePortions w K D) (0 : Fin 3) (bagReweight w w₁ K)
  simp only [sourcePortions, Matrix.cons_val_zero] at h
  rw [bagReweight_identity w w₁ hw K, frozenPortion_full_even he w w₁] at h
  simpa only [sourceLaw, observableD, sourcePortions_collapse, sourceBagZ] using h

theorem observableD_zero_of_partition_zero (he : Even (Fintype.card V))
    (w w₁ : V → V → ℝ) (hw : ∀ x y, 0 < w x y)
    (hw₁ : ∀ x y, 0 ≤ w₁ x y) (hle : ∀ x y, w₁ x y ≤ w x y)
    (hz : 0 < Switching.partition w ∅) (K D : ℕ)
    (hz₁ : Switching.partition w₁ ∅ = 0) (a : SourceMarked w K)
    (ha : 0 < sourceLaw w K D a) : observableD w w₁ K a = 0 := by
  have hB : 0 < sourceBagZ w K D := sourceBagZ_pos w hw hz K D
  have hmean := observableD_mean_even he w w₁ hw K D
  rw [hz₁, mul_zero, zero_div] at hmean
  have hnonneg (b : SourceMarked w K) : 0 ≤ sourceLaw w K D b * observableD w w₁ K b :=
    mul_nonneg (sourceLaw_nonneg w hw K D hB.le b)
      (observableD_range w w₁ hw hw₁ hle K b).1
  have hz' := (sum_eq_zero_iff_of_nonneg (fun b _ => hnonneg b)).mp hmean a (mem_univ a)
  exact (mul_eq_zero.mp hz').resolve_left ha.ne'

end MatchingFPRAS.Enlargement

namespace MatchingFPRAS.TableMarking
open Finset Transport Variation

variable {V E I : Type*} [Fintype V] [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
variable (inc : E → V → Prop)
variable {A : Type*} [Fintype A] [Nonempty A]

omit [Fintype A] [Nonempty A] [DecidableEq E] in
lemma draw_law_pos [DecidableEq E] (f : A → PM inc) (w : E → ℝ) (hw : ∀ e, 0 < w e)
    (c : E → WeightedOptions I) (k : ℕ) (bits : A × (E → Fin k → Bool)) :
    0 < law inc w c (draw inc f c k bits) := by
  classical
  change 0 < gibbs w (f bits.1) * ∏ e : (f bits.1).val, ((c e.val).law ((c e.val).draw k (bits.2 e.val)) : ℝ)
  apply mul_pos (gibbs_pos w hw _)
  exact Finset.prod_pos fun e _ => by exact_mod_cast (c e.val).draw_law_pos k (bits.2 e.val)

end MatchingFPRAS.TableMarking

namespace MatchingFPRAS.RationalSource
open Finset Transport Variation Enlargement

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder

noncomputable local instance instDecidableEqSourceLabelCastReal_5_r2631ec_1 (w : V → V → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
noncomputable local instance instFintypeBagEdgeSourceVertexSourceLabelCastRealSourceBags_5_r2631ec_1 (w : V → V → ℚ) (K : ℕ) :
    Fintype (BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) := Fintype.ofFinite _
noncomputable local instance instDecidableEqBagPMSourceVertexLabelBags_6_r2631ec_1 (w : V → V → ℚ) (K : ℕ) :
    DecidableEq (BagPM (bags w K)) := Classical.decEq _
lemma marking_law_eq (w : V → V → ℚ) (hw : ∀ x y, 0 < w x y)
    (K D : ℕ) (hD : 0 < D) :
    TableMarking.law BagEdge.Incident (fun e => (bagWeight w K D e : ℝ))
      (markingTable w hw K D hD) = markedLaw w K D := by
  funext a
  simp only [TableMarking.law, markedLaw, Variation.sigmaLift, Variation.product, TableMarking.portion, markingTable_law]

theorem source_draw_support {A : Type*} [Fintype A] [Nonempty A]
    (w : V → V → ℚ) (hw : ∀ x y, 0 < w x y) (K D k : ℕ) (hD : 0 < D)
    (f : A → BagPM (bags w K)) (bits : A × (BagEdge (bags w K) → Fin k → Bool)) :
    0 < sourceLaw (fun x y => (w x y : ℝ)) K D
      ((sourceMarkedEquiv w K).symm
        (TableMarking.draw BagEdge.Incident f (markingTable w hw K D hD) k bits)) := by
  rw [←markedLaw_equiv w hw K D hD, Equiv.apply_symm_apply, ←marking_law_eq w hw K D hD]
  apply TableMarking.draw_law_pos
  intro e
  exact_mod_cast bagWeight_pos w hw K D hD e

end MatchingFPRAS.RationalSource

namespace MatchingFPRAS.GraphBridge
open Finset Switching

lemma unpadded_partition (G : GraphInput) :
    partition (rawActivity G 0) ∅ = (Z G : ℝ) := by
  have h := raw_padding_bound G 0 (by norm_num) (by norm_num)
  have he : rawPartition G 0 = (Z G : ℚ) := le_antisymm (by simpa using h.2) h.1
  have hc := raw_partition G 0
  rw [he] at hc
  simpa using hc.symm

end MatchingFPRAS.GraphBridge

namespace MatchingFPRAS.Trial
open Finset Switching Transport Enlargement StageAnalysis
open scoped Classical

variable {G : GraphInput} {j K : ℕ} [Nontrivial (Fin G.n)]

noncomputable local instance instDecidableEqSourceLabelFinN_2_r2631ec_1 (w : Fin G.n → Fin G.n → ℝ) (K : ℕ) :
    DecidableEq (SourceLabel w K) := Classical.decEq _
omit [Nontrivial (Fin G.n)] in
lemma ScaleState.certificateActivity_nonneg (s : ScaleState G j) (a b : Fin G.n) :
    0 ≤ s.certificateActivity a b := by
  unfold ScaleState.certificateActivity GraphBridge.rawActivity
  split_ifs
  · simpa only [one_mul] using mul_nonneg (s.positive a).le (s.positive b).le
  · simp

omit [Nontrivial (Fin G.n)] in
lemma ScaleState.certificateActivity_le (s : ScaleState G j) (a b : Fin G.n) :
    s.certificateActivity a b ≤ s.activity a b := by
  unfold ScaleState.certificateActivity ScaleState.activity raw GraphBridge.rawActivity
  split_ifs
  · rfl
  · simp only [zero_mul]
    exact mul_nonneg (mul_nonneg (pow_pos (cooling_pos G.n) j).le (s.positive a).le) (s.positive b).le

omit [Nontrivial (Fin G.n)] in
lemma ScaleState.certificateActivity_partition (s : ScaleState G j) :
    Switching.partition s.certificateActivity ∅ = (Z G : ℝ) * ∏ i, s.scale i := by
  change Switching.partition (fun a b => GraphBridge.rawActivity G 0 a b * s.scale a * s.scale b) ∅ = _
  rw [partition_vertex_scaling, GraphBridge.unpadded_partition]
  simp

theorem ScaleState.certificate_zero (s : ScaleState G j) (he : Even G.n)
    (hZ : Z G = 0) (D : ℕ) (a : SourceMarked s.activity K)
    (ha : 0 < sourceLaw s.activity K D a) :
    observableD s.activity s.certificateActivity K a = 0 := by
  apply observableD_zero_of_partition_zero (by simpa using he) s.activity s.certificateActivity
    s.activity_pos s.certificateActivity_nonneg s.certificateActivity_le
    (s.partition_pos he) K D
  · rw [s.certificateActivity_partition, hZ]
    simp
  · exact ha

open Finset Switching Transport Enlargement StageAnalysis
open scoped Classical

variable {G : GraphInput} [Nontrivial (Fin G.n)]

noncomputable local instance instFintypeBagEdgeSourceVertexFinNSourceLabelSourceBags_2_r2631ec_1 (w : Fin G.n → Fin G.n → ℝ) (K : ℕ) :
    Fintype (BagEdge (sourceBags w K)) := Fintype.ofFinite _
noncomputable local instance instDecidableEqSourceLabelFinN_3_r2631ec_1 (w : Fin G.n → Fin G.n → ℝ) (K : ℕ) :
    DecidableEq (SourceLabel w K) := Classical.decEq _
attribute [local instance] OAI.MatchingFPRAS.Trial.instFintypeBagEdgeSourceVertexFinNSourceLabelSourceBags_3
theorem ScaleState.certificate_mean_lower (p : Parameters G) (s : ScaleState G p.K)
    (hs : s.Balanced p.hn) (hZ : 0 < Z G) :
    (1:ℝ)/4 ≤ ∑ a : SourceMarked s.activity p.K,
      sourceLaw s.activity p.K p.D a * observableD s.activity s.certificateActivity p.K a := by
  have hm : (∑ a : SourceMarked s.activity p.K,
      sourceLaw s.activity p.K p.D a * observableD s.activity s.certificateActivity p.K a) =
      sourceC s.activity p.K * partition s.certificateActivity ∅ / sourceBagZ s.activity p.K p.D := by
    convert observableD_mean_even (by simpa using p.even) s.activity s.certificateActivity
      s.activity_pos p.K p.D using 1
    all_goals try with_reducible_and_instances rfl
    exact Variation.sum_instances _ _ _
  rw [hm]
  have hB := (sourceBagZ_bounds (by simpa using p.hn) s.activity s.activity_pos
    (s.partition_pos p.even) hs.1 hs.2 p.K (s.cap le_rfl)).2
  have hp := (final_padding G p.epsilon p.epsilon_pos p.K p.schedule hZ).2
  have hsmall : partition (raw G p.K) ∅ ≤ 2 * (Z G : ℝ) := by
    have hz : (0:ℝ) ≤ Z G := Nat.cast_nonneg _
    have he := p.epsilon_real_lt_one
    nlinarith
  have hprod : 0 < ∏ i, s.scale i := prod_pos fun i _ => s.positive i
  have hact : partition s.activity ∅ ≤ 2 * partition s.certificateActivity ∅ := by
    rw [s.certificateActivity_partition]
    change partition (fun a b => raw G p.K a b * s.scale a * s.scale b) ∅ ≤ _
    rw [partition_vertex_scaling]
    simpa [mul_assoc] using mul_le_mul_of_nonneg_right hsmall hprod.le
  have hc := sourceC_pos s.activity p.K
  have hb0 := sourceBagZ_pos s.activity s.activity_pos (s.partition_pos p.even) p.K p.D
  apply (le_div_iff₀ hb0).mpr
  change sourceBagZ s.activity p.K (sourceD (V:=Fin G.n) p.K) ≤ _ at hB
  have hmul := mul_le_mul_of_nonneg_left hact hc.le
  change (1:ℝ)/4 * sourceBagZ s.activity p.K (sourceD (V:=Fin G.n) p.K) ≤ _
  nlinarith

end MatchingFPRAS.Trial

namespace MatchingFPRAS.Variation
open Finset
open scoped Classical

variable {Ω : Type*} [Fintype Ω]

lemma mean_le_positive_event (p X : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hX : ∀ x, 0 ≤ X x ∧ X x ≤ 1) :
    (∑ x, p x * X x) ≤ event p (fun x => 0 < X x) := by
  apply sum_le_sum
  intro x _
  change p x * X x ≤ if 0 < X x then p x else 0
  by_cases hx : 0 < X x
  · simp only [hx, ite_true]
    exact mul_le_of_le_one_right (hp x) (hX x).2
  · have hz : X x = 0 := le_antisymm (le_of_not_gt hx) (hX x).1
    simp [hz]

end MatchingFPRAS.Variation

namespace MatchingFPRAS.RationalSource
open Finset Transport Variation Enlargement

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder

noncomputable local instance instDecidableEqSourceLabelCastReal_6_r2631ec_1 (w : V → V → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
noncomputable local instance instFintypeBagEdgeSourceVertexSourceLabelCastRealSourceBags_6_r2631ec_1 (w : V → V → ℚ) (K : ℕ) :
    Fintype (BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) := Fintype.ofFinite _
noncomputable local instance instDecidableEqBagPMSourceVertexLabelBags_7_r2631ec_1 (w : V → V → ℚ) (K : ℕ) :
    DecidableEq (BagPM (bags w K)) := Classical.decEq _
theorem fixedSampler_support (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D m : ℕ)
    (hD : 0<D) (hN : 0<Fintype.card (SourceVertex V K))
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K)
    (hq : 0<ladderQ (Fintype.card (SourceVertex V K)) D) (M : BagPM (bags w K)) (η : ℚ)
    (bits : Fin (totalBitsPolynomial (Fintype.card (SourceVertex V K)) D K m ⌈η⁻¹⌉₊) → Bool) :
    0 < sourceLaw (fun x y => (w x y : ℝ)) K D
      (fixedSampler w hw K D m hD hN h hq M η bits) := by
  simp only [fixedSampler, padSampler, bitSampler, Function.comp_apply, markedSampler]
  exact source_draw_support w hw K D _ hD _ _

end MatchingFPRAS.RationalSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_GuardProbability
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.FiniteTrial
open Finset Switching Transport Enlargement Adaptive Variation
open scoped Classical

variable {G : GraphInput} [Nontrivial (Fin G.n)]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance instDecidableEqSourceLabelFinNCastReal_6_r2631ec_1 (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
omit [Nontrivial (Fin G.n)] in
lemma ScaleState.certificateActivity_cast [Nontrivial (Fin G.n)] {j : ℕ} (s : ScaleState G j) :
    (fun a b => (s.certificateActivity a b : ℝ)) = s.toReal.certificateActivity := by
  funext a b
  unfold ScaleState.certificateActivity Trial.ScaleState.certificateActivity GraphBridge.rawActivity
  split_ifs <;> simp [ScaleState.toReal]

lemma ScaleState.certificate_cast {j : ℕ} (s : ScaleState G j) (K : ℕ)
    (a : SourceMarked (fun x y => (s.activity x y : ℝ)) K) :
    (s.certificate K a : ℝ) = observableD (fun x y => (s.activity x y : ℝ))
      (fun x y => (s.certificateActivity x y : ℝ)) K a :=
  RationalSource.observableD_cast _ _ _ _

lemma ScaleState.certificate_range {j : ℕ} (s : ScaleState G j) (K : ℕ)
    (a : SourceMarked (fun x y => (s.activity x y : ℝ)) K) :
    0 ≤ s.certificate K a ∧ s.certificate K a ≤ 1 := by
  have h : 0 ≤ (s.certificate K a : ℝ) ∧ (s.certificate K a : ℝ) ≤ 1 := by
    rw [s.certificate_cast]
    apply observableD_range _ _ (fun x y => by exact_mod_cast s.activity_pos x y)
    · intro x y
      have hc := s.toReal.certificateActivity_nonneg x y
      rw [←s.certificateActivity_cast] at hc
      exact hc
    · intro x y
      have hc := s.toReal.certificateActivity_le x y
      rw [←s.certificateActivity_cast, ←s.activity_cast] at hc
      exact hc
  exact_mod_cast h

theorem ScaleState.drawOne_certificate_zero (p : Trial.Parameters G) {j : ℕ}
    (hj : j ≤ p.K) (s : ScaleState G j) (hZ : Z G = 0) (b : Fin (oneBits p) → Bool) :
    s.certificate p.K (s.drawOne p hj b) = 0 := by
  have hs : 0 < sourceLaw (fun x y => (s.activity x y : ℝ)) p.K p.D (s.drawOne p hj b) :=
    RationalSource.fixedSampler_support _ _ _ _ _ _ _ _ _ _ _ _
  have hc := s.toReal.certificate_zero (K:=p.K) p.even hZ p.D
  rw [←s.activity_cast, ←s.certificateActivity_cast] at hc
  have hh := hc (s.drawOne p hj b) hs
  rw [←s.certificate_cast] at hh
  exact_mod_cast hh

attribute [local instance] OAI.MatchingFPRAS.FiniteTrial.instFintypeBagEdgeSourceVertexFinNSourceLabelCastRealSourceBags_6
attribute [local instance] OAI.MatchingFPRAS.FiniteTrial.instFintypeSourceMarkedFinNCastReal_5
lemma ScaleState.certificate_mean_lower (p : Trial.Parameters G) (s : ScaleState G p.K)
    (hs : s.Balanced p.hn) (hZ : 0 < Z G) :
    (1:ℝ)/4 ≤ ∑ a : SourceMarked (fun x y => (s.activity x y : ℝ)) p.K,
      sourceLaw (fun x y => (s.activity x y : ℝ)) p.K p.D a * (s.certificate p.K a : ℝ) := by
  have h := s.toReal.certificate_mean_lower p hs hZ
  rw [←s.activity_cast, ←s.certificateActivity_cast] at h
  simp_rw [←s.certificate_cast] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  exact Variation.sum_instances _ _ _

theorem ScaleState.guard_success (p : Trial.Parameters G) (s : ScaleState G p.K)
    (hs : s.Balanced p.hn) (hZ : 0 < Z G) :
    (1:ℝ)/5 ≤ (s.runLaw p le_rfl).event (fun a => 0 < s.certificate p.K a) := by
  let q := sourceLaw (fun x y => (s.activity x y : ℝ)) p.K p.D
  have hz : 0 < sourceBagZ (fun x y => (s.activity x y : ℝ)) p.K p.D := by
    rw [s.activity_cast]
    exact sourceBagZ_pos _ s.toReal.activity_pos (s.toReal.partition_pos p.even) _ _
  have hq0 : ∀ a, 0 ≤ q a := sourceLaw_nonneg _ (fun x y => by exact_mod_cast s.activity_pos x y) _ _ hz.le
  have hq1 : ∑ a, q a = 1 := by
    convert sourceLaw_sum (fun x y => (s.activity x y : ℝ)) p.K p.D hz.ne' using 1
    all_goals try with_reducible_and_instances rfl
    exact Variation.sum_instances _ _ _
  have hm := (s.certificate_mean_lower p hs hZ).trans
    (mean_le_positive_event q (fun a => (s.certificate p.K a : ℝ)) hq0
      (fun a => by exact_mod_cast s.certificate_range p.K a))
  have hev : event q (fun a => 0 < (s.certificate p.K a : ℝ)) =
      event q (fun a => 0 < s.certificate p.K a) := by
    congr 1
    ext a
    exact_mod_cast Iff.rfl
  rw [hev] at hm
  have hd := event_sub_le (s.runLaw p le_rfl).mass q ((s.runLaw p le_rfl).total.trans hq1.symm)
    (fun a => 0 < s.certificate p.K a)
  have ht := s.runLaw_tv p le_rfl
  have hk : (1:ℝ) ≤ p.K := by exact_mod_cast p.K_pos
  have hS : (1:ℝ) ≤ p.S := by exact_mod_cast p.S_pos
  have hc : 3/(1000*(p.K:ℝ)*p.S) ≤ (3:ℝ)/1000 := by
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    nlinarith [mul_le_mul hk hS (by norm_num) (by positivity)]
  have hh := (abs_sub_le_iff.mp hd).2
  change 1/5 ≤ event (s.runLaw p le_rfl).mass (fun a => 0 < s.certificate p.K a)
  dsimp only [q] at *
  linarith

end MatchingFPRAS.FiniteTrial

namespace MatchingFPRAS.Adaptive
open Finset
open scoped Classical

variable {Ω : Type*} [Fintype Ω]

lemma Law.iid_all (μ : Law Ω) (r : ℕ) (P : Ω → Prop) :
    (μ.iid r).event (fun x => ∀ i, P (x i)) = (μ.event P)^r := by
  unfold Law.event Law.iid Variation.iid
  calc
    _ = ∑ x : Fin r → Ω, ∏ i, if P (x i) then μ (x i) else 0 := by
      apply sum_congr rfl
      intro x _
      by_cases hx : ∀ i, P (x i)
      · simp [hx]
      · obtain ⟨i, hi⟩ := not_forall.mp hx
        simp only [hx, ite_false]
        symm
        apply prod_eq_zero (mem_univ i)
        simp [hi]
    _ = ∏ _ : Fin r, (∑ x, if P x then μ x else 0) := by
      convert (Fintype.prod_sum (fun (_ : Fin r) (x : Ω) => if P x then μ x else 0)).symm using 1
      all_goals try with_reducible_and_instances rfl
    _ = _ := by simp

lemma Law.iid_no_certificate (μ : Law Ω) (P : Ω → Prop) (hP : (1:ℝ)/5 ≤ μ.event P) :
    (μ.iid 16).event (fun x => ¬∃ i, P (x i)) ≤ 1/16 := by
  have hc : μ.event (fun x => ¬P x) ≤ 4/5 := by
    have h := Variation.event_complement μ.mass P
    change μ.event P + μ.event (fun x => ¬P x) = ∑ x, μ.mass x at h
    rw [μ.total] at h
    linarith
  have he : (fun x : Fin 16 → Ω => ¬∃ i, P (x i)) = (fun x => ∀ i, ¬P (x i)) := by
    funext x
    simp
  rw [he]
  have hi := μ.iid_all 16 (fun x => ¬P x)
  change Variation.event _ _ = _ at hi
  have hie : (μ.iid 16).event (fun x => ∀ i, ¬P (x i)) = (μ.event (fun x => ¬P x))^16 := by
    convert hi using 1
    all_goals try with_reducible_and_instances rfl
    exact Variation.sum_instances _ _ _
  rw [hie]
  calc
    _ ≤ (4/5:ℝ)^16 := pow_le_pow_left₀ (μ.event_nonneg _) hc _
    _ ≤ 1/16 := by norm_num

end MatchingFPRAS.Adaptive

namespace MatchingFPRAS.FiniteTrial
open Finset Switching Transport Enlargement Adaptive Variation
open scoped Classical

variable {G : GraphInput} [Nontrivial (Fin G.n)]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance instDecidableEqSourceLabelFinNCastReal_7_r2631ec_1 (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
attribute [local instance] OAI.MatchingFPRAS.FiniteTrial.instFintypeSourceMarkedFinNCastReal_6
lemma guard_failure (p : Trial.Parameters G) (s : ScaleState G p.K)
    (hs : s.Balanced p.hn) (hZ : 0 < Z G) :
    (guardLaw p s).event (fun x => ¬guardPass p s x) ≤ 1/16 := by
  have h := (s.runLaw p le_rfl).iid_no_certificate
    (fun x => 0 < s.certificate p.K x) (s.guard_success p hs hZ)
  exact h

lemma guardedOutput_nonneg (p : Trial.Parameters G) (x : GuardedTrial p) : 0 ≤ guardedOutput p x := by
  unfold guardedOutput
  split_ifs
  · exact output_nonneg _ _
  · rfl

theorem guarded_trial_failure (p : Trial.Parameters G) (hZ : 0 < Z G) :
    (guardedLaw p).event (fun x => ¬Accurate p (guardedOutput p x)) ≤ 1/10 := by
  have hf := first_failure_sigma (layers p p.K le_rfl).law
    (fun x => guardLaw p ((layers p p.K le_rfl).state x))
    ((layers p p.K le_rfl).good p) (fun x => Accurate p (guardedOutput p x)) (1/16) (by norm_num)
    (fun x hx => ((guardLaw p ((layers p p.K le_rfl).state x)).event_mono
      (fun y hy hp => by
        apply hy
        simp only [guardedOutput, hp, ite_true]
        exact good_output p hZ x hx)).trans (guard_failure p _ hx.1 hZ))
  have hb := layers_failure p p.K le_rfl
  have hk : (p.K:ℝ) ≠ 0 := by exact_mod_cast p.K_pos.ne'
  have he : (p.K:ℝ) * (13/(1000*p.K)) = 13/1000 := by field_simp
  rw [he] at hb
  change (guardedLaw p).event _ ≤ _ at hf
  linarith

end MatchingFPRAS.FiniteTrial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Probability_OnlineLayerLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalStream
lemma qaverage_const {A : Type} [Fintype A] [Nonempty A] (q : ℚ) :
    qaverage (fun _ : A=>q)=q := by
  simp only [qaverage,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have h : (Fintype.card A:ℚ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
end MatchingFPRAS.PhysicalStream

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_GuardBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.FiniteTrial
open Transport Enlargement Variation Adaptive Amplification Finset
open scoped Classical

variable {G : GraphInput} [Nontrivial (Fin G.n)]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance instDecidableEqSourceLabelFinNCastReal_8_r2631ec_1 (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
attribute [local instance] OAI.MatchingFPRAS.FiniteTrial.instFintypeSourceMarkedFinNCastReal_7
lemma ScaleState.drawGuard_law (p : Trial.Parameters G) (s : ScaleState G p.K) :
    imageLaw (s.drawGuard p)=(guardLaw p s).mass := by
  unfold ScaleState.drawGuard
  erw [imageLaw_comp_equiv,imageLaw_componentwise]
  rw [ScaleState.drawOne_law]
  rfl
lemma ScaleState.drawGuard_no_certificate (p : Trial.Parameters G) (s : ScaleState G p.K)
    (hZ : Z G = 0) (b : Fin (guardBits p) → Bool) : ¬guardPass p s (s.drawGuard p b) := by
  dsimp only [guardBits] at b
  dsimp only [guardPass, ScaleState.drawGuard, guardBits, Function.comp_apply]
  simp only [s.drawOne_certificate_zero p le_rfl hZ, lt_self_iff_false, exists_const, not_false_eq_true]

lemma drawGuarded_law (p : Trial.Parameters G) : imageLaw (drawGuarded p)=(guardedLaw p).mass := by
  change imageLaw ((fun c : (Fin (p.K*stageBits p) → Bool) × (Fin (guardBits p) → Bool) =>
    (⟨drawLayer p p.K le_rfl c.1,
      ((layers p p.K le_rfl).state (drawLayer p p.K le_rfl c.1)).drawGuard p c.2⟩ : GuardedTrial p)) ∘
    pairBitsEquiv (p.K*stageBits p) (guardBits p)) = _
  erw [imageLaw_comp_equiv]
  change imageLaw _ = sigmaLift (layers p p.K le_rfl).law.mass (fun x=>(guardLaw p ((layers p p.K le_rfl).state x)).mass)
  rw [imageLaw_sigma_pair (drawLayer p p.K le_rfl) (fun x=>((layers p p.K le_rfl).state x).drawGuard p)]
  simp_rw [ScaleState.drawGuard_law]
  rw [drawLayer_law]
theorem guardedBitOutput_zero (p : Trial.Parameters G) (hZ : Z G=0) (b : Fin (guardedBits p) → Bool) :
    guardedBitOutput p b=0 := by
  unfold guardedBitOutput drawGuarded
  simp only [Function.comp_apply, guardedOutput]
  exact ite_eq_right (ScaleState.drawGuard_no_certificate p _ hZ _)

lemma drawGuardedTrials_law (p : Trial.Parameters G) (δ : ℚ) :
    imageLaw (drawGuardedTrials p δ)=((guardedLaw p).iid (2*halfRepetitions δ+1)).mass := by
  unfold drawGuardedTrials
  erw [imageLaw_comp_equiv,imageLaw_componentwise]
  rw [drawGuarded_law]
  rfl
lemma guardedAmplifiedBitOutput_nonneg (p : Trial.Parameters G) (δ : ℚ)
    (b : Fin (guardedAmplifiedBits p δ) → Bool) : 0≤guardedAmplifiedBitOutput p δ b :=
  median_nonneg _ (fun _=>guardedOutput_nonneg p _)

omit [Nontrivial (Fin G.n)] in
lemma median_eq_of_constant {k : ℕ} (x : Fin (2*k+1) → ℚ) (a : ℚ) (hx : ∀ i,x i=a) : median x=a := by
  unfold median sortedValue
  have hp := List.mergeSort_perm (List.ofFn x) (· ≤ ·)
  have hm : (sortedList x)[k]'(by rw [sortedList_length]; omega) ∈ List.ofFn x :=
    hp.mem_iff.mp (List.getElem_mem _)
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hm
  rw [←hi, hx]

theorem guardedAmplifiedBitOutput_zero (p : Trial.Parameters G) (hZ : Z G=0) (δ : ℚ)
    (b : Fin (guardedAmplifiedBits p δ) → Bool) : guardedAmplifiedBitOutput p δ b=0 := by
  apply median_eq_of_constant
  intro i
  exact guardedBitOutput_zero p hZ _

theorem guardedAmplifiedBitOutput_success (p : Trial.Parameters G) (hZ : 0<Z G) (δ : ℚ) (hδ : 0<δ) :
    ((guardedAccurateBits p δ).card:ℚ)/(2:ℚ)^(guardedAmplifiedBits p δ)≥1-δ := by
  have hf := median_delta (guardedLaw p) (guardedOutput p) ((1-p.epsilon)*(Z G:ℚ))
    ((1+p.epsilon)*(Z G:ℚ)) (guarded_trial_failure p hZ) δ hδ
  have hc:=event_complement ((guardedLaw p).iid (2*halfRepetitions δ+1)).mass
    (fun x=>Accurate p (guardedAmplifiedOutput p δ x))
  rw [Law.total] at hc
  have hh : 1-(δ:ℝ) ≤ event ((guardedLaw p).iid (2*halfRepetitions δ+1)).mass
      (fun x=>Accurate p (guardedAmplifiedOutput p δ x)) := by
    change event _ (fun x=>¬Accurate p (guardedAmplifiedOutput p δ x))≤(δ:ℝ) at hf
    linarith only [hc,hf]
  rw [←drawGuardedTrials_law,event_imageLaw] at hh
  have he : Fintype.card (Fin (guardedAmplifiedBits p δ) → Bool)=2^(guardedAmplifiedBits p δ) := by simp
  rw [he] at hh
  change 1-(δ:ℝ) ≤ ((guardedAccurateBits p δ).card:ℝ)/(2^(guardedAmplifiedBits p δ):ℕ) at hh
  have hr : ((1-δ:ℚ):ℝ) ≤ (((((guardedAccurateBits p δ).card:ℚ)/(2:ℚ)^(guardedAmplifiedBits p δ)):ℚ):ℝ) := by
    push_cast
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using hh
  exact Rat.cast_le.mp hr

end MatchingFPRAS.FiniteTrial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_Endpoints2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS
lemma vertex_bound_of_perfect {G : GraphInput} {M : Finset (Fin G.n×Fin G.n)}
    (hM : Perfect G M) : G.n≤2*G.edges.card := by
  classical
  have hc : (Finset.univ : Finset (Fin G.n))⊆M.image Prod.fst ∪ M.image Prod.snd := by
    intro v _
    obtain ⟨e,he,-⟩:=hM.2 v
    rcases he.2 with hv|hv
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e,he.1,hv⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e,he.1,hv⟩)
  have h₁:=Finset.card_le_card hc
  have h₂:=Finset.card_union_le (M.image Prod.fst) (M.image Prod.snd)
  have h₃:=Finset.card_image_le (s:=M) (f:=Prod.fst)
  have h₄:=Finset.card_image_le (s:=M) (f:=Prod.snd)
  have h₅:=Finset.card_le_card hM.1
  simp only [Finset.card_univ,Fintype.card_fin] at h₁
  omega

lemma zero_of_vertex_bound {G : GraphInput} (h : 2*G.edges.card<G.n) : Z G=0 := by
  classical
  by_contra hz
  obtain ⟨M,hM⟩:=Finset.card_pos.mp (Nat.pos_of_ne_zero hz)
  have hb:=vertex_bound_of_perfect ((mem_perfectMatchings G M).mp hM)
  omega

lemma even_of_perfect {G : GraphInput} {M : Finset (Fin G.n×Fin G.n)}
    (hM : Perfect G M) : Even G.n := by
  have h:=perfect_vertex_factor G M hM (fun _=>(-1:ℚ))
  have hh : (-1:ℚ)^G.n=1 := by
    simpa using h.symm
  exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1:ℚ)≠1)).mp hh

lemma zero_of_not_even {G : GraphInput} (he : ¬Even G.n) : Z G=0 := by
  by_contra hz
  obtain ⟨M,hM⟩:=Finset.card_pos.mp (Nat.pos_of_ne_zero hz)
  exact he (even_of_perfect ((mem_perfectMatchings G M).mp hM))

lemma count_empty_graph {G : GraphInput} (hn : G.n=0) : Z G=1 := by
  classical
  have hv (v : Fin G.n) : False := by have := v.isLt; omega
  have he : G.edges=∅ := Finset.eq_empty_of_forall_notMem (fun e _=>hv e.1)
  have hp : Perfect G ∅ := ⟨Finset.empty_subset _,fun v=>False.elim (hv v)⟩
  simp only [Z,perfectMatchings,he,Finset.powerset_empty]
  have hf : Finset.filter (Perfect G) {∅}=({∅} : Finset (Finset (Fin G.n×Fin G.n))) := by
    ext M
    simp only [Finset.mem_filter,Finset.mem_singleton]
    constructor
    · exact And.left
    · rintro rfl
      exact ⟨rfl,hp⟩
  rw [hf]
  rfl

end MatchingFPRAS

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_Codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralCodec
open TreeTyped TreeData TreeFunction

lemma natWord_eq (n : ℕ) : natWord n=encodeNat n := rfl

lemma ratWord_repr (q : ℚ) (hq : 0≤q) : ratWord (TreeFraction.repr q)=encodeRat q := by
  have hn : ¬q.num<0 := not_lt.mpr (Rat.num_nonneg.mpr hq)
  simp only [ratWord,TreeFraction.repr,natWord_eq,encodeRat,encodeInt,ite_eq_right hn,List.singleton_append]
end MatchingFPRAS.LiteralCodec

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_Parse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralParse
open TreeTyped TreeData TreeFunction Polynomial LiteralCodec

lemma bits_fold (n : ℕ) (ns : List ℕ) :
    (n.bits.map fromBit).foldr (fun a ns=>numStep (a,ns)) (0::ns)=n::ns := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn,List.map_cons,List.foldr_cons,ih]
    cases b <;> simp [fromBit,numStep,Nat.bit]
lemma encodeNat_fold (n : ℕ) (ns : List ℕ) :
    (encodeNat n).foldr (fun a ns=>numStep (a,ns)) ns=n::ns := by
  change (n.bits.map fromBit++[3]).foldr _ ns=_
  rw [List.foldr_append]
  change (n.bits.map fromBit).foldr (fun a ns=>numStep (a,ns)) (0::ns)=_
  exact bits_fold n ns
lemma encodeInt_fold (z : ℤ) (ns : List ℕ) :
    (encodeInt z).foldr (fun a ns=>numStep (a,ns)) ns=z.natAbs::ns := by
  unfold encodeInt
  rw [List.foldr_append,encodeNat_fold]
  split_ifs <;> simp [numStep]
lemma encodeRat_fold (q : ℚ) (ns : List ℕ) :
    (encodeRat q).foldr (fun a ns=>numStep (a,ns)) ns=q.num.natAbs::q.den::ns := by
  rw [encodeRat,List.foldr_append,encodeNat_fold,encodeInt_fold]
end MatchingFPRAS.LiteralParse

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_Input
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralInput
open TreeTyped TreeFunction Polynomial LiteralParse

lemma pair_pair (i j : ℕ) (es : List (ℕ×ℕ)) :
    pairStep (i,pairStep (j,((false,0),es)))=((false,0),(i,j)::es) := rfl
lemma pairs_reverse (es : List (ℕ×ℕ)) (acc : List (ℕ×ℕ)) :
    ((es.flatMap (fun e=>[e.1,e.2])).reverse.foldl (fun s n=>pairStep (n,s)) ((false,0),acc))=
      ((false,0),es++acc) := by
  induction es generalizing acc with
  | nil => rfl
  | cons e es ih =>
    simp only [List.flatMap_cons,List.reverse_append,List.reverse_cons,List.reverse_nil,
      List.nil_append,List.singleton_append,List.foldl_append,ih,List.foldl_cons,List.foldl_nil,pair_pair]
    rfl

lemma edges_fold (es : List (ℕ×ℕ)) (ns : List ℕ) :
    (es.flatMap (fun e=>encodeNat e.1++encodeNat e.2)).foldr (fun a ns=>numStep (a,ns)) ns=
      es.flatMap (fun e=>[e.1,e.2])++ns := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.flatMap_cons,List.foldr_append,ih,encodeNat_fold]
    rfl
lemma parse_source (G : GraphInput) (ε δ : ℚ) : LiteralParse.parse (encodeInput G ε δ)=
    G.n::G.edges.card::(edgeNumbers G).flatMap (fun e=>[e.1,e.2])++[ε.num.natAbs,ε.den,δ.num.natAbs,δ.den] := by
  unfold encodeInput LiteralParse.parse
  simp only [List.foldr_append,encodeNat_fold,encodeRat_fold]
  rw [show (((G.edges.map toLex.toEmbedding).sort (·≤·)).flatMap fun e=>encodeNat (ofLex e).1.val++encodeNat (ofLex e).2.val)=
    (edgeNumbers G).flatMap (fun e=>encodeNat e.1++encodeNat e.2) by simp only [edgeNumbers,List.flatMap_map]]
  rw [edges_fold]
  rfl
lemma parseInput_source (G : GraphInput) (ε δ : ℚ) :
    parseInput (encodeInput G ε δ)=(G.n,(edgeNumbers G,(TreeFraction.repr ε,TreeFraction.repr δ))) := by
  rw [parseInput,parse_source]
  unfold fromNumbers
  simp only [List.cons_append,List.headD_cons,List.tail_cons,
    List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append]
  unfold ratTail
  simp only [List.headD_cons,List.tail_cons]
  unfold pairs
  rw [pairs_reverse]
  simp only [List.append_nil]
  rfl
end MatchingFPRAS.LiteralInput

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_Algorithm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralAlgorithm
open TreeTyped TreeFraction PhysicalStream LiteralInput Polynomial

lemma edgeNumbers_length (G : GraphInput) : (edgeNumbers G).length=G.edges.card := by
  simp only [edgeNumbers,List.length_map,Finset.length_sort,Finset.card_map]
end MatchingFPRAS.LiteralAlgorithm

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_OnlineHistoryCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalStream.Experiment
lemma all_of_qaverage {A B : Type} [Fintype B] [Nonempty B] (p : Experiment A) (f : B→A)
    (hm : ∀ h,p.mean h=qaverage (h ∘ f)) (P : A→Prop) (hf : ∀ b,P (f b)) : p.All P := by
  classical
  rw [all_indicator,hm]
  calc
    _=qaverage (fun _ : B=>(0:ℚ)) := by
      apply qaverage_congr
      intro b
      simp only [Function.comp_apply,ite_eq_left (hf b)]
    _=0 := qaverage_const 0
end MatchingFPRAS.PhysicalStream.Experiment

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_AlgorithmLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalStream
lemma qaverage_mono {A : Type} [Fintype A] (f g : A→ℚ) (h : ∀ a,f a≤g a) : qaverage f≤qaverage g := by
  unfold qaverage
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun a _=>h a)) (Nat.cast_nonneg _)
lemma qaverage_indicator {A : Type} [Fintype A] (P : A→Prop) [DecidablePred P] :
    qaverage (fun a=>if P a then 1 else 0)=((Finset.univ.filter P).card:ℚ)/Fintype.card A := by
  simp only [qaverage,Finset.sum_boole]
namespace Experiment
lemma mean_indicator_eq_one {A : Type} (p : Experiment A) (P : A→Prop) [DecidablePred P]
    (h : p.All P) : p.mean (fun a=>if P a then 1 else 0)=1 := by
  induction p with
  | done value => exact ite_eq_left h
  | delay ticks experiment ih => exact ih h
  | read next ih => norm_num [mean,ih false h.1,ih true h.2]
end Experiment
end MatchingFPRAS.PhysicalStream

namespace MatchingFPRAS.LiteralAlgorithm
open scoped Classical
open TreeTyped TreeFraction PhysicalStream LiteralInput

lemma empty_source (G : GraphInput) (ε δ : ℚ) : empty (parseInput (encodeInput G ε δ))=decide (G.n=0) := by
  rw [parseInput_source];rfl
lemma invalid_source (G : GraphInput) (ε δ : ℚ) : invalid (parseInput (encodeInput G ε δ))=
    (!(decide (G.n%2=0)) || decide (2*G.edges.card<G.n)) := by
  rw [parseInput_source]
  simp only [invalid,ExecutableInput.tooSparse,edgeNumbers_length]
lemma invalid_zero (G : GraphInput) (ε δ : ℚ) (h : invalid (parseInput (encodeInput G ε δ))=true) : Z G=0 := by
  rw [invalid_source] at h
  by_cases he : Even G.n
  · have he' : G.n%2=0 := Nat.even_iff.mp he
    simp only [he',decide_true,Bool.not_true,Bool.false_or] at h
    exact zero_of_vertex_bound (of_decide_eq_true h)
  · exact zero_of_not_even he
lemma valid_even (G : GraphInput) (ε δ : ℚ) (h : invalid (parseInput (encodeInput G ε δ))=false) : Even G.n := by
  rw [invalid_source] at h
  by_contra he
  have he' : ¬G.n%2=0 := fun hm=>he (Nat.even_iff.mpr hm)
  simp only [he',decide_false,Bool.not_false,Bool.true_or,Bool.true_eq_false] at h
lemma valid_two (G : GraphInput) (ε δ : ℚ) (he : empty (parseInput (encodeInput G ε δ))=false)
    (hi : invalid (parseInput (encodeInput G ε δ))=false) : 2≤G.n := by
  have h0 := of_decide_eq_false (show decide (G.n=0)=false by rwa [empty_source] at he)
  have hev:=Nat.even_iff.mp (valid_even G ε δ hi)
  omega

lemma algorithm_proper (G : GraphInput) (ε δ : ℚ) (he : 0<ε) (he1 : ε<1) (hd : 0≤δ) :
    (algorithm (encodeInput G ε δ)).All (Proper G) := by
  unfold algorithm
  rw [Experiment.all_map]
  have hen : LiteralCodec.ratWord (1,1)=encodeRat 1 := LiteralCodec.ratWord_repr 1 (by norm_num)
  have hzero : LiteralCodec.ratWord (0,1)=encodeRat 0 := LiteralCodec.ratWord_repr 0 (by norm_num)
  cases hE:empty (parseInput (encodeInput G ε δ)) with
  | true =>
    have hn : G.n=0 := of_decide_eq_true (by rwa [empty_source] at hE)
    have hz:=count_empty_graph hn
    simp only [count,hE,ite_true,Experiment.All]
    exact ⟨1,by norm_num,hen,by intro h;omega⟩
  | false =>
    cases hI:invalid (parseInput (encodeInput G ε δ)) with
    | true =>
      simp only [count,hE,hI,Bool.false_eq_true,ite_false,ite_true,Experiment.All]
      exact ⟨0,by norm_num,hzero,fun _=>rfl⟩
    | false =>
      simp only [count,hE,hI,Bool.false_eq_true,ite_false]
      have hn:=valid_two G ε δ hE hI
      have hev:=valid_even G ε δ hI
      let : Nontrivial (Fin G.n):=Fin.nontrivial_iff_two_le.mpr hn
      apply Experiment.all_of_qaverage _ (fun b=>TreeFraction.repr
        (FiniteTrial.guardedAmplifiedBitOutput (FiniteTrial.parameters G hn hev ε he he1) δ b))
      · exact compute_mean hn hev ε δ he he1 hd
      · intro b
        let p:=FiniteTrial.parameters G hn hev ε he he1
        have hq:=FiniteTrial.guardedAmplifiedBitOutput_nonneg p δ b
        exact ⟨_,hq,LiteralCodec.ratWord_repr _ hq,fun hz=>FiniteTrial.guardedAmplifiedBitOutput_zero p hz δ b⟩

lemma accurate_zero (G : GraphInput) (ε : ℚ) (hz : Z G=0) : AccurateWord G ε (encodeRat 0) := by
  refine ⟨0,rfl,?_,?_⟩ <;> simp [hz]
lemma proper_accurate_zero (G : GraphInput) (ε : ℚ) (hz : Z G=0) (as : List Symbol) (ha : Proper G as) :
    AccurateWord G ε as := by
  obtain ⟨q,_,rfl,hq⟩:=ha
  rw [hq hz]
  exact accurate_zero G ε hz

lemma algorithm_success_oai (G : GraphInput) (ε δ : ℚ) (he : 0<ε) (he1 : ε<1) (hd : 0<δ) :
    1-δ≤(algorithm (encodeInput G ε δ)).mean (fun as=>if AccurateWord G ε as then 1 else 0) := by
  classical
  by_cases hz:Z G=0
  · rw [Experiment.mean_indicator_eq_one _ _ ((algorithm_proper G ε δ he he1 hd.le).mono
      (proper_accurate_zero G ε hz))]
    linarith
  have hZ:0<Z G:=Nat.pos_of_ne_zero hz
  cases hE:empty (parseInput (encodeInput G ε δ)) with
  | true =>
    have hn : G.n=0 := of_decide_eq_true (by rwa [empty_source] at hE)
    have hz:=count_empty_graph hn
    have hq : AccurateWord G ε (LiteralCodec.ratWord (1,1)) := by
      refine ⟨1,LiteralCodec.ratWord_repr 1 (by norm_num),?_,?_⟩ <;> rw [hz] <;> norm_num <;> linarith
    simp only [algorithm,Experiment.mean_map,count,hE,ite_true,Experiment.mean,ite_eq_left hq]
    linarith
  | false =>
    have hI:invalid (parseInput (encodeInput G ε δ))=false := by
      cases hi:invalid (parseInput (encodeInput G ε δ)) with
      | false => rfl
      | true => exact False.elim (hz (invalid_zero G ε δ hi))
    have hn:=valid_two G ε δ hE hI
    have hev:=valid_even G ε δ hI
    let : Nontrivial (Fin G.n):=Fin.nontrivial_iff_two_le.mpr hn
    let p:=FiniteTrial.parameters G hn hev ε he he1
    have hs:=FiniteTrial.guardedAmplifiedBitOutput_success p hZ δ hd
    have hb : qaverage (fun b=>if FiniteTrial.Accurate p (FiniteTrial.guardedAmplifiedBitOutput p δ b) then 1 else 0)≥1-δ := by
      rw [qaverage_indicator]
      simpa only [FiniteTrial.guardedAccurateBits,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,Nat.cast_pow,Nat.cast_ofNat] using hs
    simp only [algorithm,Experiment.mean_map,count,hE,hI,Bool.false_eq_true,ite_false]
    rw [compute_mean hn hev ε δ he he1 hd.le]
    apply hb.trans (qaverage_mono _ _ (fun b=>?_))
    split_ifs with ha hword hword
    · rfl
    · exfalso
      apply hword
      exact ⟨_,LiteralCodec.ratWord_repr _ (FiniteTrial.guardedAmplifiedBitOutput_nonneg p δ b),ha⟩
    · norm_num
    · rfl
end MatchingFPRAS.LiteralAlgorithm

end OAI
end

theorem solution : type_of% @OAI.MatchingFPRAS.LiteralAlgorithm.algorithm_success_oai := @OAI.MatchingFPRAS.LiteralAlgorithm.algorithm_success_oai
