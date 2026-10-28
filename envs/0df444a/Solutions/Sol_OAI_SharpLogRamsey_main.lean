-- Prove2me | solution 1 for OAI.SharpLogRamsey.main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T12:32:29.406027+00:00
-- url     : https://prove2.me/submissions/6d6bb0fc-3767-4447-8962-cacf61bebdb8

import Mathlib
import Definitions.Def_SharpLogRamsey
import Definitions.Def_OAIQ045S000
import Definitions.Def_OAIQ045S001
import Theorems.Thm_OAI_SharpLogRamsey_LowerTransfer_prime_construction

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_Weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incidence bounds for rich lines and finite point configurations. -/

section
section
section
section
open scoped BigOperators Classical
open Finset
namespace SharpLogRamsey.Sampling
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [DecidableEq V] in

theorem mem_selected (f : V → Bool) (v : V) : v ∈ selected f ↔ f v = true := by
  simp [selected]
omit [DecidableEq V] in

theorem weight_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (f : V → Bool) :
    0 ≤ weight p f := by
  apply prod_nonneg
  intro v _
  split <;> linarith

theorem sum_weight (p : ℝ) : ∑ f : V → Bool, weight p f = 1 := by
  simp_rw [weight]
  rw [← Fintype.prod_sum (fun (_v : V) (b : Bool) => if b then p else 1-p)]
  simp

theorem containment_moment (p : ℝ) (A : Finset V) :
    (∑ f : V → Bool, weight p f * (if A ⊆ selected f then 1 else 0)) = p^A.card := by
  have hi (f : V → Bool) :
      (if A ⊆ selected f then (1 : ℝ) else 0) =
        ∏ v : V, if v ∈ A then (if f v then 1 else 0) else 1 := by
    by_cases h : A ⊆ selected f
    · rw [ite_eq_left h]
      symm
      apply prod_eq_one
      intro v _
      by_cases hv : v ∈ A
      · simp [hv, (mem_selected f v).mp (h hv)]
      · simp [hv]
    · rw [ite_eq_right h]
      obtain ⟨v, hv, hfv⟩ := not_subset.mp h
      symm
      apply prod_eq_zero (mem_univ v)
      simp only [mem_selected, Bool.not_eq_true] at hfv
      simp [hv, hfv]
  simp_rw [hi, weight, ← prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (v : V) (b : Bool) =>
    (if b then p else 1-p) * (if v ∈ A then (if b then (1:ℝ) else 0) else 1))]
  calc
    _ = ∏ v : V, if v ∈ A then p else 1 := by
      apply prod_congr rfl
      intro v _
      by_cases hv : v ∈ A <;> simp [hv]
    _ = p^A.card := by simp

theorem family_moment (p : ℝ) (F : Finset (Finset V)) {a : ℕ}
    (hF : ∀ A ∈ F, A.card = a) :
    (∑ f : V → Bool, weight p f * count F (selected f)) = p^a * F.card := by
  have hc (S : Finset V) : (count F S : ℝ) = ∑ A ∈ F, if A ⊆ S then 1 else 0 := by
    simp [count, sum_boole]
  simp_rw [hc, mul_sum]
  rw [sum_comm]
  simp_rw [containment_moment]
  rw [sum_congr rfl (fun A hA => by rw [hF A hA])]
  simp [mul_comm]

theorem size_moment (p : ℝ) :
    (∑ f : V → Bool, weight p f * (selected f).card) = p * Fintype.card V := by
  have hc (f : V → Bool) : ((selected f).card : ℝ) =
      ∑ v : V, if ({v} : Finset V) ⊆ selected f then 1 else 0 := by
    simp [selected, sum_boole]
  simp_rw [hc, mul_sum]
  rw [sum_comm]
  simp_rw [containment_moment]
  simp [mul_comm]

theorem exists_ge_mean {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (X : (V → Bool) → ℝ) : ∃ f, (∑ g, weight p g * X g) ≤ X f := by
  obtain ⟨f, _, hf⟩ := exists_max_image (univ : Finset (V → Bool)) X univ_nonempty
  refine ⟨f, ?_⟩
  calc
    (∑ g, weight p g * X g) ≤ ∑ g, weight p g * X f := by
      exact sum_le_sum (fun g _ => mul_le_mul_of_nonneg_left (hf g (mem_univ g))
        (weight_nonneg hp hp1 g))
    _ = X f := by rw [← sum_mul, sum_weight, one_mul]

end SharpLogRamsey.Sampling

end

end

end

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Bounds_Upper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The off-diagonal Ramsey upper bound. -/

section
open scoped BigOperators Classical
open Finset
namespace SharpLogRamsey

namespace Foundation
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

omit [Fintype V] [DecidableEq V] in
theorem indepNum_lt_of_cliqueFree_compl {t : ℕ} (ht : Gᶜ.CliqueFree t) :
    G.indepNum < t := by
  by_contra! h
  obtain ⟨A, hA⟩ := G.exists_isNIndepSet_indepNum
  exact (ht.mono h) A (G.isNClique_compl.mpr hA)

omit [DecidableEq V] in
theorem maximum_indep_dominates {A : Finset V} (hA : G.IsMaximumIndepSet A)
    (x : V) : x ∈ A ∨ ∃ y ∈ A, G.Adj x y := by
  by_contra! hn
  have hi : G.IsIndepSet ((insert x A : Finset V) : Set V) := by
    intro u hu v hv huv
    simp only [mem_coe, mem_insert] at hu hv
    rcases hu with rfl | hu <;> rcases hv with rfl | hv
    · simp
    · exact hn.2 v hv
    · exact fun h => hn.2 u hu h.symm
    · exact hA.1 hu hv huv
  have hc := hA.2 (insert x A) hi
  rw [card_insert_of_notMem hn.1] at hc
  omega

theorem card_le_mul_indepNum {B : ℕ} (hdeg : ∀ x, G.degree x + 1 ≤ B) :
    Fintype.card V ≤ B * G.indepNum := by
  obtain ⟨A, hA⟩ := G.maximumIndepSet_exists
  have hcover : (univ : Finset V) ⊆ A.biUnion (fun x => insert x (G.neighborFinset x)) := by
    intro v _
    obtain hv | ⟨x, hx, hadj⟩ := maximum_indep_dominates G hA v
    · exact mem_biUnion.mpr ⟨v, hv, by simp⟩
    · exact mem_biUnion.mpr ⟨x, hx, by simp [hadj.symm]⟩
  calc
    Fintype.card V = (univ : Finset V).card := (card_univ).symm
    _ ≤ (A.biUnion (fun x => insert x (G.neighborFinset x))).card := card_le_card hcover
    _ ≤ ∑ x ∈ A, (insert x (G.neighborFinset x)).card := card_biUnion_le
    _ ≤ ∑ _x ∈ A, B := by
      apply sum_le_sum
      intro x _
      simpa using hdeg x
    _ = B * G.indepNum := by
      simp [G.maximumIndepSet_card_eq_indepNum A hA, mul_comm]

omit [Fintype V] [DecidableEq V] in
theorem cliqueFree_neighbor {s : ℕ} (hs : G.CliqueFree (s+1)) (x : V) :
    (G.induce (G.neighborSet x)).CliqueFree s := by
  rw [G.cliqueFree_induce_iff]
  have hc : G.CliqueFreeOn Set.univ (s+1) := (G.cliqueFreeOn_univ).mpr hs
  simpa using SimpleGraph.CliqueFreeOn.of_succ G hc (a := x) (Set.mem_univ x)

omit [Fintype V] [DecidableEq V] in
theorem cliqueFree_induce {s : ℕ} (hs : G.CliqueFree s) (U : Set V) :
    (G.induce U).CliqueFree s := by
  rw [G.cliqueFree_induce_iff]
  intro A _ hA
  exact hs A hA
omit [Fintype V] [DecidableEq V] in

theorem compl_cliqueFree_induce {t : ℕ} (ht : Gᶜ.CliqueFree t) (U : Set V) :
    (G.induce U)ᶜ.CliqueFree t := by
  have he : (G.induce U)ᶜ = Gᶜ.induce U := by ext u v; simp [Subtype.val_inj]
  rw [he]
  exact cliqueFree_induce Gᶜ ht U

theorem order_avoiding_lt_pow (n : ℕ) {t : ℕ} (ht : 1 ≤ t) :
    ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    G.CliqueFree (n+2) → Gᶜ.CliqueFree t → Fintype.card V < t^(n+1) := by
  induction n with
  | zero =>
    intro V _ _ G hs hi
    have hg : G = ⊥ := G.cliqueFree_two.mp hs
    have hn := card_le_mul_indepNum G (B := 1) (by intro x; simp [hg])
    have hh := indepNum_lt_of_cliqueFree_compl G hi
    simpa using hn.trans_lt (by simpa using hh)
  | succ n ih =>
    intro V _ _ G hs hi
    have hd : ∀ x, G.degree x + 1 ≤ t^(n+1) := by
      intro x
      have hc := cliqueFree_neighbor G (s := n+2) (by simpa [Nat.add_assoc] using hs) x
      have hci := compl_cliqueFree_induce G hi (G.neighborSet x)
      have hh := ih (G.induce (G.neighborSet x)) hc hci
      rw [G.card_neighborSet_eq_degree] at hh
      omega
    have hn := card_le_mul_indepNum G hd
    have hi' := indepNum_lt_of_cliqueFree_compl G hi
    have hp : 0 < t^(n+1) := pow_pos (by omega) _
    have hm := Nat.mul_lt_mul_of_pos_left hi' hp
    calc
      Fintype.card V ≤ t^(n+1) * G.indepNum := hn
      _ < t^(n+1) * t := hm
      _ = t^(n+1+1) := (pow_succ _ _).symm

theorem ramseyProperty_pow (n : ℕ) {t : ℕ} (ht : 1 ≤ t) :
    RamseyProperty (n+2) t (t^(n+1)) := by
  intro G
  by_cases hs : G.CliqueFree (n+2)
  · right
    by_contra! hi
    have hh := order_avoiding_lt_pow n ht G hs hi
    simp at hh
  · left
    simpa only [SimpleGraph.CliqueFree, not_forall, not_not] using hs

theorem ramseyProperty_nonempty {s t : ℕ} (hs : 2 ≤ s) (ht : 1 ≤ t) :
    {N | RamseyProperty s t N}.Nonempty := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hs
  exact ⟨t^(n+1), by simpa [Nat.add_comm] using ramseyProperty_pow n ht⟩

theorem ramsey_has_property {s t : ℕ} (hs : 2 ≤ s) (ht : 1 ≤ t) :
    RamseyProperty s t (ramsey s t) := Nat.sInf_mem (ramseyProperty_nonempty hs ht)

omit [Fintype V] [DecidableEq V] in
 theorem clique_map_embedding {U : Type*} (f : U ↪ V) {n : ℕ} {A : Finset U}
    (hA : (G.comap f).IsNClique n A) : G.IsNClique n (A.map f) := by
  constructor
  · intro u hu v hv huv
    obtain ⟨a, ha, rfl⟩ := mem_map.mp hu
    obtain ⟨b, hb, rfl⟩ := mem_map.mp hv
    exact hA.1 ha hb (fun h => huv (congrArg f h))
  · simpa using hA.2

omit [Fintype V] [DecidableEq V] in
 theorem compl_comap_embedding {U : Type*} (f : U ↪ V) :
    (G.comap f)ᶜ = Gᶜ.comap f := by
  ext u v
  simp [SimpleGraph.comap_adj, f.injective.eq_iff]

omit [DecidableEq V] in
theorem property_for_finite_type {s t N : ℕ} (hN : RamseyProperty s t N)
    (hcard : N ≤ Fintype.card V) :
    (∃ A, G.IsNClique s A) ∨ (∃ B, Gᶜ.IsNClique t B) := by
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin N) (β := V) (by simpa using hcard)
  obtain ⟨A, hA⟩ | ⟨B, hB⟩ := hN (G.comap f)
  · exact Or.inl ⟨A.map f, clique_map_embedding G f hA⟩
  · rw [compl_comap_embedding G f] at hB
    exact Or.inr ⟨B.map f, clique_map_embedding Gᶜ f hB⟩
omit [DecidableEq V] in

theorem order_lt_ramsey {s t : ℕ} (hs : 2 ≤ s) (ht : 1 ≤ t)
    (hGs : G.CliqueFree s) (hGt : Gᶜ.CliqueFree t) :
    Fintype.card V < ramsey s t := by
  by_contra! h
  obtain ⟨A, hA⟩ | ⟨B, hB⟩ := property_for_finite_type G (ramsey_has_property hs ht) h
  · exact hGs A hA
  · exact hGt B hB

theorem ramsey_le_of_property {s t N : ℕ} (hN : RamseyProperty s t N) :
    ramsey s t ≤ N := Nat.sInf_le hN

theorem ramsey_le_pow {s t : ℕ} (hs : 2 ≤ s) (ht : 1 ≤ t) :
    ramsey s t ≤ t^(s-1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hs
  have hh := ramsey_le_of_property (ramseyProperty_pow n ht)
  simpa [Nat.add_comm] using hh

theorem le_ramsey {s t : ℕ} (hs : 2 ≤ s) (ht : 1 ≤ t) : t ≤ ramsey s t := by
  obtain ⟨A,hA⟩ | ⟨B,hB⟩ := ramsey_has_property hs ht (⊥ : SimpleGraph (Fin (ramsey s t)))
  · exact False.elim ((SimpleGraph.cliqueFree_bot (by omega : 1 < s)) A hA)
  · have hb := card_le_card (subset_univ B)
    simpa [hB.2] using hb

theorem ramsey_two {t : ℕ} (ht : 1 ≤ t) : ramsey 2 t = t := by
  apply Nat.le_antisymm
  · simpa using ramsey_le_pow (s := 2) (by omega) ht
  · exact le_ramsey (by omega) ht

omit [Fintype V] [DecidableEq V] in
theorem cliqueFree_common {s : ℕ} (hs : G.CliqueFree (s+2))
    {x y : V} (hxy : G.Adj x y) :
    (G.induce (G.commonNeighbors x y)).CliqueFree s := by
  rw [G.cliqueFree_induce_iff]
  have hc : G.CliqueFreeOn Set.univ (s+2) := (G.cliqueFreeOn_univ).mpr hs
  have hn : G.CliqueFreeOn (G.neighborSet x) (s+1) := by
    simpa using SimpleGraph.CliqueFreeOn.of_succ G hc (a := x) (Set.mem_univ x)
  exact SimpleGraph.CliqueFreeOn.of_succ G hn hxy

theorem exists_avoiding_pred {s t : ℕ} (hs : 2 ≤ s) (ht : 2 ≤ t) :
    ∃ G : SimpleGraph (Fin (ramsey s t - 1)), G.CliqueFree s ∧ Gᶜ.CliqueFree t := by
  have hr : 2 ≤ ramsey s t := ht.trans (le_ramsey hs (by omega))
  have hn : ¬ RamseyProperty s t (ramsey s t - 1) := by
    intro h
    have hh := ramsey_le_of_property h
    omega
  simp only [RamseyProperty, not_forall, not_or, not_exists] at hn
  exact hn

end Foundation
end SharpLogRamsey

open scoped BigOperators Classical
open Finset
namespace SharpLogRamsey.TriangleFree
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem independentSets_nonempty : (independentSets G).Nonempty := by
  refine ⟨∅, ?_⟩
  simp [SimpleGraph.IsIndepSet]

theorem admissible_outside (x : V) {S : Finset V}
    (hS : S ∈ independentSets G) : Admissible G x (outside G x S) := by
  constructor
  · exact (mem_independentSets G S |>.mp hS).mono (by
      intro u hu; exact (mem_outside G x u S |>.mp hu).1)
  · exact disjoint_left.mpr (fun u hu hc => (Finset.mem_sdiff.mp hu).2 hc)

theorem admissible_not_center {x : V} {J : Finset V}
    (hJ : Admissible G x J) : x ∉ J := by
  intro hx
  exact disjoint_left.mp hJ.2 hx (by simp)

theorem admissible_not_adj {x u : V} {J : Finset V}
    (hJ : Admissible G x J) (hu : u ∈ J) : ¬G.Adj x u := by
  intro h
  exact disjoint_left.mp hJ.2 hu (by simp [h])

theorem available_disjoint {x : V} {J : Finset V}
    (hJ : Admissible G x J) : Disjoint J (available G x J) := by
  apply disjoint_left.mpr
  intro u hJ' hu
  exact admissible_not_adj G hJ hJ' (mem_available G x u J |>.mp hu).1

theorem independent_insert_center {x : V} {J : Finset V}
    (hJ : Admissible G x J) : G.IsIndepSet ((insert x J : Finset V) : Set V) := by
  intro u hu v hv huv
  simp only [mem_coe, mem_insert] at hu hv
  rcases hu with rfl | hu
  · rcases hv with rfl | hv
    · simp
    · exact admissible_not_adj G hJ hv
  · rcases hv with rfl | hv
    · exact fun h => admissible_not_adj G hJ hu h.symm
    · exact hJ.1 hu hv huv

theorem independent_extend (htri : G.CliqueFree 3) {x : V} {J K : Finset V}
    (hJ : Admissible G x J) (hK : K ⊆ available G x J) :
    G.IsIndepSet ((J ∪ K : Finset V) : Set V) := by
  intro u hu v hv huv
  simp only [mem_coe, mem_union] at hu hv
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · exact hJ.1 hu hv huv
  · exact fun h => (mem_available G x v J |>.mp (hK hv)).2 u hu h.symm
  · exact (mem_available G x u J |>.mp (hK hu)).2 v hv
  · exact (G.isIndepSet_neighborSet_of_triangleFree htri x)
      (mem_available G x u J |>.mp (hK hu)).1
      (mem_available G x v J |>.mp (hK hv)).1 huv

theorem outside_insert_center {x : V} {J : Finset V}
    (hJ : Admissible G x J) : outside G x (insert x J) = J := by
  ext u
  simp only [mem_outside, mem_insert]
  constructor
  · rintro ⟨h, hne, _⟩
    exact h.resolve_left hne
  · intro hu
    exact ⟨Or.inr hu, fun h => admissible_not_center G hJ (h ▸ hu),
      admissible_not_adj G hJ hu⟩

theorem outside_extend {x : V} {J K : Finset V}
    (hJ : Admissible G x J) (hK : K ⊆ available G x J) :
    outside G x (J ∪ K) = J := by
  ext u
  simp only [mem_outside, mem_union]
  constructor
  · rintro ⟨hu | hu, _, hna⟩
    · exact hu
    · exact False.elim (hna (mem_available G x u J |>.mp (hK hu)).1)
  · intro hu
    exact ⟨Or.inl hu, fun h => admissible_not_center G hJ (h ▸ hu),
      admissible_not_adj G hJ hu⟩

theorem fiber_eq (htri : G.CliqueFree 3) {x : V} {J : Finset V}
    (hJ : Admissible G x J) :
    fiber G x J = insert (insert x J)
      ((available G x J).powerset.image (fun K => J ∪ K)) := by
  ext S
  simp only [fiber, mem_filter, mem_independentSets, mem_insert, mem_image,
    mem_powerset]
  constructor
  · rintro ⟨hS, hout⟩
    by_cases hx : x ∈ S
    · left
      ext u
      simp only [mem_insert]
      constructor
      · intro hu
        by_cases hux : u = x
        · exact Or.inl hux
        · right
          rw [← hout, mem_outside]
          exact ⟨hu, hux, hS hx hu (Ne.symm hux)⟩
      · rintro (rfl | hu)
        · exact hx
        · rw [← hout, mem_outside] at hu
          exact hu.1
    · right
      refine ⟨S ∩ G.neighborFinset x, ?_, ?_⟩
      · intro u hu
        simp only [mem_inter, SimpleGraph.mem_neighborFinset] at hu
        apply (mem_available G x u J).mpr
        refine ⟨hu.2, ?_⟩
        intro v hv hadj
        have hvS : v ∈ S := by rw [← hout, mem_outside] at hv; exact hv.1
        exact hS hu.1 hvS hadj.ne hadj
      · ext u
        simp only [mem_union, mem_inter, SimpleGraph.mem_neighborFinset]
        constructor
        · rintro (hu | hu)
          · rw [← hout, mem_outside] at hu; exact hu.1
          · exact hu.1
        · intro hu
          by_cases hax : G.Adj x u
          · exact Or.inr ⟨hu, hax⟩
          · left
            rw [← hout, mem_outside]
            exact ⟨hu, fun h => hx (h ▸ hu), hax⟩
  · rintro (rfl | ⟨K, hK, rfl⟩)
    · exact ⟨independent_insert_center G hJ, outside_insert_center G hJ⟩
    · exact ⟨independent_extend G htri hJ hK, outside_extend G hJ hK⟩

theorem extend_injective {x : V} {J : Finset V} (hJ : Admissible G x J) :
    Set.InjOn (fun K => J ∪ K) ((available G x J).powerset : Set (Finset V)) := by
  intro K hK L hL heq
  have hdK : Disjoint J K := (available_disjoint G hJ).mono_right (mem_powerset.mp hK)
  have hdL : Disjoint J L := (available_disjoint G hJ).mono_right (mem_powerset.mp hL)
  simpa [union_sdiff_cancel_left hdK, union_sdiff_cancel_left hdL] using
    congrArg (fun S => S \ J) heq

theorem center_choice_not_image {x : V} {J : Finset V} (hJ : Admissible G x J) :
    insert x J ∉ (available G x J).powerset.image (fun K => J ∪ K) := by
  rintro h
  obtain ⟨K, hK, heq⟩ := mem_image.mp h
  have hx : x ∈ J ∪ K := heq ▸ mem_insert_self x J
  rcases mem_union.mp hx with hx | hx
  · exact admissible_not_center G hJ hx
  · exact center_not_available G x J (mem_powerset.mp hK hx)

theorem card_fiber (htri : G.CliqueFree 3) {x : V} {J : Finset V}
    (hJ : Admissible G x J) : (fiber G x J).card = 1 + 2^(available G x J).card := by
  rw [fiber_eq G htri hJ, card_insert_of_notMem (center_choice_not_image G hJ),
    card_image_of_injOn (extend_injective G hJ), card_powerset]
  omega

theorem sum_fiber (htri : G.CliqueFree 3) {x : V} {J : Finset V}
    (hJ : Admissible G x J) (f : Finset V → ℝ) :
    ∑ S ∈ fiber G x J, f S = f (insert x J) +
      ∑ K ∈ (available G x J).powerset, f (J ∪ K) := by
  rw [fiber_eq G htri hJ, sum_insert (center_choice_not_image G hJ),
    sum_image (extend_injective G hJ)]

omit [Fintype V] in

theorem twice_sum_powerset_card (A : Finset V) :
    2 * (∑ K ∈ A.powerset, (K.card : ℝ)) = A.card * (2:ℝ)^A.card := by
  have hc : ∑ K ∈ A.powerset, ((A \ K).card : ℝ) =
      ∑ K ∈ A.powerset, (K.card : ℝ) := by
    apply sum_bij (fun K _ => A \ K)
    · intro K _; exact mem_powerset.mpr sdiff_subset
    · intro K hK L hL heq
      have := congrArg (fun X => A \ X) heq
      simpa [Finset.sdiff_sdiff_eq_self (mem_powerset.mp hK),
        Finset.sdiff_sdiff_eq_self (mem_powerset.mp hL)] using this
    · intro K hK
      exact ⟨A \ K, mem_powerset.mpr sdiff_subset,
        Finset.sdiff_sdiff_eq_self (mem_powerset.mp hK)⟩
    · intro K _; rfl
  have hsum : ∑ K ∈ A.powerset, (((A \ K).card : ℝ) + K.card) =
      A.card * (2:ℝ)^A.card := by
    calc
      _ = ∑ _K ∈ A.powerset, (A.card : ℝ) := by
        apply sum_congr rfl
        intro K hK
        exact_mod_cast card_sdiff_add_card_eq_card (mem_powerset.mp hK)
      _ = _ := by simp [card_powerset]; ring
  rw [sum_add_distrib, hc] at hsum
  linarith

theorem center_neighbor_inter {x : V} {J : Finset V}
    (hJ : Admissible G x J) : insert x J ∩ G.neighborFinset x = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro u hu
  simp only [mem_inter, mem_insert, SimpleGraph.mem_neighborFinset] at hu
  rcases hu.1 with rfl | huJ
  · exact G.irrefl hu.2
  · exact admissible_not_adj G hJ huJ hu.2

theorem extend_neighbor_inter {x : V} {J K : Finset V}
    (hJ : Admissible G x J) (hK : K ⊆ available G x J) :
    (J ∪ K) ∩ G.neighborFinset x = K := by
  ext u
  simp only [mem_inter, mem_union, SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨hu | hu, hadj⟩
    · exact False.elim (admissible_not_adj G hJ hu hadj)
    · exact hu
  · intro hu
    exact ⟨Or.inr hu, (mem_available G x u J |>.mp (hK hu)).1⟩

end SharpLogRamsey.TriangleFree
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Bounds_SumFiberCenter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The off-diagonal Ramsey upper bound. -/

section
open scoped BigOperators Classical
open Finset
open scoped BigOperators Classical
open Finset
namespace SharpLogRamsey.TriangleFree
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
theorem sum_fiber_center (htri : G.CliqueFree 3) {x : V} {J : Finset V}
    (hJ : Admissible G x J) : ∑ S ∈ fiber G x J, (if x ∈ S then (1:ℝ) else 0) = 1 := by
  rw [sum_fiber G htri hJ]
  simp only [mem_insert_self, ite_true]
  have hx : ∀ K ∈ (available G x J).powerset, x ∉ J ∪ K := by
    intro K hK h
    rcases mem_union.mp h with hx | hx
    · exact admissible_not_center G hJ hx
    · exact center_not_available G x J (mem_powerset.mp hK hx)
  rw [sum_eq_zero (fun K hK => ite_eq_right (hx K hK)), add_zero]

theorem twice_sum_fiber_neighbors (htri : G.CliqueFree 3) {x : V} {J : Finset V}
    (hJ : Admissible G x J) :
    2 * (∑ S ∈ fiber G x J, ((S ∩ G.neighborFinset x).card : ℝ)) =
      (available G x J).card * (2:ℝ)^(available G x J).card := by
  rw [sum_fiber G htri hJ, center_neighbor_inter G hJ, card_empty, Nat.cast_zero,
    zero_add]
  have he : ∑ K ∈ (available G x J).powerset,
      (((J ∪ K) ∩ G.neighborFinset x).card : ℝ) =
      ∑ K ∈ (available G x J).powerset, (K.card : ℝ) := by
    apply sum_congr rfl
    intro K hK
    rw [extend_neighbor_inter G hJ (mem_powerset.mp hK)]
  rw [he]
  exact twice_sum_powerset_card (available G x J)

theorem fiber_empty_of_not_admissible {x : V} {J : Finset V}
    (hJ : ¬Admissible G x J) : fiber G x J = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro S hS
  obtain ⟨hS, hout⟩ := mem_filter.mp hS
  exact hJ (hout ▸ admissible_outside G x hS)

theorem sum_fiber_Z (x : V) (J : Finset V) (f : ℕ → ℝ) :
    ∑ S ∈ fiber G x J, f (Z G x S) = (fiber G x J).card * f (available G x J).card := by
  calc
    _ = ∑ _S ∈ fiber G x J, f (available G x J).card := by
      apply sum_congr rfl
      intro S hS
      simp only [Z, (mem_filter.mp hS).2]
    _ = _ := by simp

theorem exp_neg_log_two_mul (z : ℕ) :
    Real.exp (-(Real.log 2) * z) = ((2:ℝ)^z)⁻¹ := by
  rw [show -(Real.log 2) * z = -((z:ℝ) * Real.log 2) by ring,
    Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num)]

theorem half_sum_exp_le_center (htri : G.CliqueFree 3) (x : V) :
    (∑ S ∈ independentSets G, Real.exp (-Real.log 2 * Z G x S)) / 2 ≤
      ∑ S ∈ independentSets G, (if x ∈ S then (1:ℝ) else 0) := by
  rw [← Finset.sum_fiberwise (independentSets G) (outside G x)
       (fun S => Real.exp (-Real.log 2 * Z G x S)),
    ← Finset.sum_fiberwise (independentSets G) (outside G x)
       (fun S => if x ∈ S then (1:ℝ) else 0), sum_div]
  apply sum_le_sum
  intro J _
  change (∑ S ∈ fiber G x J, _) / 2 ≤ ∑ S ∈ fiber G x J, _
  by_cases hJ : Admissible G x J
  · rw [sum_fiber_Z G x J (fun z => Real.exp (-Real.log 2 * z)),
      card_fiber G htri hJ, sum_fiber_center G htri hJ, exp_neg_log_two_mul]
    push_cast
    have hp : (1:ℝ) ≤ 2^(available G x J).card := one_le_pow₀ (by norm_num)
    have hpp : (0:ℝ) < 2^(available G x J).card := by positivity
    field_simp
    nlinarith
  · rw [fiber_empty_of_not_admissible G hJ]
    simp

theorem sum_Z_le_four_neighbors (htri : G.CliqueFree 3) (x : V) :
    (∑ S ∈ independentSets G, (Z G x S : ℝ)) ≤
      4 * ∑ S ∈ independentSets G, ((S ∩ G.neighborFinset x).card : ℝ) := by
  rw [← Finset.sum_fiberwise (independentSets G) (outside G x)
       (fun S => (Z G x S : ℝ)),
    ← Finset.sum_fiberwise (independentSets G) (outside G x)
       (fun S => ((S ∩ G.neighborFinset x).card : ℝ)), mul_sum]
  apply sum_le_sum
  intro J _
  change (∑ S ∈ fiber G x J, _) ≤ 4 * ∑ S ∈ fiber G x J, _
  by_cases hJ : Admissible G x J
  · rw [sum_fiber_Z G x J (fun z => (z:ℝ)), card_fiber G htri hJ]
    have hn := twice_sum_fiber_neighbors G htri hJ
    have hp : (1:ℝ) ≤ 2^(available G x J).card := one_le_pow₀ (by norm_num)
    have hz : (0:ℝ) ≤ (available G x J).card := by positivity
    push_cast
    nlinarith
  · rw [fiber_empty_of_not_admissible G hJ]
    simp

theorem sum_center (S : Finset V) :
    (∑ x : V, if x ∈ S then (1:ℝ) else 0) = S.card := by
  simp

theorem sum_neighbors (S : Finset V) :
    (∑ x : V, ((S ∩ G.neighborFinset x).card : ℝ)) =
      ∑ v ∈ S, (G.degree v : ℝ) := by
  calc
    _ = ∑ x : V, ∑ v ∈ S, (if G.Adj x v then (1:ℝ) else 0) := by
      apply sum_congr rfl
      intro x _
      rw [← sum_filter]
      simp only [sum_const, nsmul_eq_mul, mul_one]
      congr 2
      ext v
      simp []
    _ = ∑ v ∈ S, ∑ x : V, (if G.Adj x v then (1:ℝ) else 0) := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro v _
      simp_rw [G.adj_comm]
      rw [← sum_filter]
      have he : univ.filter (G.Adj v) = G.neighborFinset v := by ext x; simp
      rw [he]
      simp

theorem exp_mean_le {α : Type*} (A : Finset α) (hA : A.Nonempty) (f : α → ℝ) :
    Real.exp ((∑ i ∈ A, f i) / A.card) ≤ (∑ i ∈ A, Real.exp (f i)) / A.card := by
  have hc : (0:ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hsum : ∑ _i ∈ A, ((A.card:ℝ)⁻¹) = 1 := by
    simp [hc.ne']
  have hj := convexOn_exp.map_sum_le (t := A) (w := fun _ => (A.card:ℝ)⁻¹)
    (p := f) (fun _ _ => inv_nonneg.mpr hc.le) hsum (fun _ _ => Set.mem_univ _)
  simp only [smul_eq_mul, ← mul_sum] at hj
  simpa only [div_eq_mul_inv, mul_comm] using hj

theorem occupation_lower_bound {D μ : ℝ} (hD : 1 ≤ D) (hμ : 0 ≤ μ)
    (hkey : Real.exp (-4 * D * μ * Real.log 2) ≤ 2 * μ) :
    Real.log (D+1) / (8 * (D+1)) ≤ μ := by
  by_contra! hbad
  have hu : 0 < D + 1 := by linarith
  have hlog : 0 < Real.log (D+1) := Real.log_pos (by linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 < 1 := by
    convert Real.log_lt_sub_one_of_pos (x := (2:ℝ)) (by norm_num) (by norm_num) using 1 ; norm_num
  have hb : 8 * (D+1) * μ < Real.log (D+1) := by
    have := (lt_div_iff₀ (show 0 < 8*(D+1) by positivity)).mp hbad
    nlinarith
  have hDμ : 0 ≤ D * μ := mul_nonneg (by linarith) hμ
  have he : -Real.log (D+1)/2 < -4 * D * μ * Real.log 2 := by
    have hh := mul_le_mul_of_nonneg_left hl2'.le hDμ
    nlinarith
  have hlow : Real.exp (-Real.log (D+1)/2) < 2 * μ :=
    (Real.exp_lt_exp.mpr he).trans_le hkey
  have hid : (D+1) * Real.exp (-Real.log (D+1)/2) =
      Real.exp (Real.log (D+1)/2) := by
    conv_lhs => lhs; rw [← Real.exp_log hu]
    rw [← Real.exp_add]
    congr 1
    ring
  have hupper := Real.add_one_le_exp (Real.log (D+1)/2)
  have hmul := mul_lt_mul_of_pos_left hlow (show 0 < 4*(D+1) by positivity)
  nlinarith

theorem exists_occupation (htri : G.CliqueFree 3) [Nonempty V]
    {D : ℝ} (hD : ∀ x, (G.degree x : ℝ) ≤ D) :
    ∃ μ : ℝ, 0 ≤ μ ∧ (Fintype.card V : ℝ) * μ ≤ G.indepNum ∧
      Real.exp (-4 * D * μ * Real.log 2) ≤ 2 * μ := by
  let A := independentSets G
  let Ω := (univ : Finset V) ×ˢ A
  let M : ℝ := ∑ S ∈ A, (S.card : ℝ)
  let m : ℝ := (Fintype.card V : ℝ) * A.card
  have hn : (0:ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have ha : (0:ℝ) < A.card := by exact_mod_cast (independentSets_nonempty G).card_pos
  have hm : 0 < m := mul_pos hn ha
  have hmcard : (Ω.card:ℝ) = m := by simp [Ω, m]
  have hM : 0 ≤ M := sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have he : (∑ a ∈ Ω, Real.exp (-Real.log 2 * Z G a.1 a.2)) ≤ 2*M := by
    have hh := sum_le_sum (s := (univ : Finset V))
      (fun x _ => half_sum_exp_le_center G htri x)
    rw [← sum_div] at hh
    have hcenter : (∑ x : V, ∑ S ∈ independentSets G,
        (if x ∈ S then (1:ℝ) else 0)) = M := by
      rw [sum_comm]
      simp only [sum_center]
      rfl
    rw [hcenter] at hh
    unfold Ω
    rw [sum_product]
    dsimp only
    change (∑ x : V, ∑ S ∈ independentSets G, _) ≤ 2*M
    linarith
  have hz : (∑ a ∈ Ω, (Z G a.1 a.2 : ℝ)) ≤ 4*D*M := by
    have hh := sum_le_sum (s := (univ : Finset V))
      (fun x _ => sum_Z_le_four_neighbors G htri x)
    rw [← mul_sum] at hh
    have hneigh : (∑ x : V, ∑ S ∈ independentSets G,
        ((S ∩ G.neighborFinset x).card:ℝ)) =
        ∑ S ∈ independentSets G, ∑ v ∈ S, (G.degree v:ℝ) := by
      rw [sum_comm]
      simp_rw [sum_neighbors]
    rw [hneigh] at hh
    have hd : (∑ S ∈ independentSets G, ∑ v ∈ S, (G.degree v : ℝ)) ≤ D*M := by
      calc
        _ ≤ ∑ S ∈ independentSets G, ∑ _v ∈ S, D := by
          apply sum_le_sum
          intro S _
          exact sum_le_sum (fun v _ => hD v)
        _ = D*M := by simp [M, A, mul_sum, mul_comm]
    unfold Ω
    rw [sum_product]
    dsimp only
    change (∑ x : V, ∑ S ∈ independentSets G, _) ≤ 4*D*M
    linarith
  have hind : M ≤ (A.card:ℝ) * G.indepNum := by
    calc
      M ≤ ∑ _S ∈ A, (G.indepNum : ℝ) := by
        apply sum_le_sum
        intro S hS
        exact_mod_cast (mem_independentSets G S |>.mp hS).card_le_indepNum
      _ = _ := by simp
  refine ⟨M/m, div_nonneg hM hm.le, ?_, ?_⟩
  · rw [← mul_div_assoc]
    apply (div_le_iff₀ hm).mpr
    dsimp only [m]
    nlinarith [mul_le_mul_of_nonneg_left hind hn.le]
  · have hΩ : Ω.Nonempty := nonempty_product.mpr ⟨univ_nonempty, independentSets_nonempty G⟩
    have hj := exp_mean_le Ω hΩ (fun a => -Real.log 2 * Z G a.1 a.2)
    rw [hmcard, ← mul_sum] at hj
    have hl : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num : (1:ℝ)<2)).le
    have hexp : Real.exp (-4*D*(M/m)*Real.log 2) ≤
        Real.exp (-Real.log 2 * (∑ a ∈ Ω, (Z G a.1 a.2:ℝ)) / m) := by
      apply Real.exp_le_exp.mpr
      rw [show -4*D*(M/m)*Real.log 2 = (-4*D*M*Real.log 2)/m by ring]
      apply (div_le_div_iff_of_pos_right hm).mpr
      have hh := mul_le_mul_of_nonpos_left hz (neg_nonpos.mpr hl)
      convert hh using 1 <;> first | rfl | ring
    have hfinal := hexp.trans hj
    have hdiv := div_le_div_of_nonneg_right he hm.le
    calc
      _ ≤ (∑ a ∈ Ω, Real.exp (-Real.log 2 * Z G a.1 a.2))/m := hfinal
      _ ≤ 2*M/m := hdiv
      _ = 2*(M/m) := by ring

theorem indepNum_lower_bound (htri : G.CliqueFree 3) [Nonempty V]
    {D : ℝ} (hD : 1 ≤ D) (hdeg : ∀ x, (G.degree x : ℝ) ≤ D) :
    (Fintype.card V : ℝ) * Real.log (D+1) / (8*(D+1)) ≤ G.indepNum := by
  obtain ⟨μ, hμ, hind, hkey⟩ := exists_occupation G htri hdeg
  have hb := occupation_lower_bound hD hμ hkey
  have hh := mul_le_mul_of_nonneg_left hb
    (show (0:ℝ) ≤ Fintype.card V by positivity)
  rw [← mul_div_assoc] at hh
  exact hh.trans hind

end SharpLogRamsey.TriangleFree

open scoped BigOperators Classical
open Finset
namespace SharpLogRamsey.Sampling
variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V)

theorem degreeMass_pair_sum (S : Finset V) :
    (degreeMass G S : ℝ) = ∑ x : V, ∑ y : V,
      if G.Adj x y then (if ({x,y} : Finset V) ⊆ S then 1 else 0) else 0 := by
  have hi (x : V) : (∑ y : V,
      if G.Adj x y then (if ({x,y} : Finset V) ⊆ S then (1:ℝ) else 0) else 0) =
      if x ∈ S then (internalDegree G S x : ℝ) else 0 := by
    by_cases hx : x ∈ S
    · rw [ite_eq_left hx]
      have he : S = univ.filter (· ∈ S) := by simp
      change _ = ((S.filter (G.Adj x)).card : ℝ)
      conv_rhs => rw [he]
      rw [filter_filter, ← sum_boole]
      apply sum_congr rfl
      intro y _
      simp only [insert_subset_iff, singleton_subset_iff, hx, true_and]
      by_cases h : G.Adj x y <;> by_cases hy : y ∈ S <;> simp [h, hy]
    · simp [insert_subset_iff, singleton_subset_iff, hx]
  simp_rw [hi]
  rw [← sum_filter]
  simp [degreeMass, Nat.cast_sum]

theorem degreeMass_moment (p : ℝ) :
    (∑ f : V → Bool, weight p f * degreeMass G (selected f)) =
      p^2 * ∑ x : V, (G.degree x : ℝ) := by
  simp_rw [degreeMass_pair_sum, mul_sum]
  rw [sum_comm]
  calc
    _ = ∑ x : V, ∑ y : V, if G.Adj x y then p^2 else 0 := by
      apply sum_congr rfl
      intro x _
      rw [sum_comm]
      apply sum_congr rfl
      intro y _
      by_cases h : G.Adj x y
      · simp only [ite_eq_left h]
        rw [containment_moment]
        simp [h.ne]
      · simp [h]
    _ = p^2 * ∑ x : V, (G.degree x : ℝ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro x _
      rw [← sum_filter]
      simp [← G.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_def,
        mul_comm]
    _ = _ := by simp [mul_sum]

omit [Fintype V] in

theorem exists_avoid_family (F : Finset (Finset V))
    (hF : ∀ A ∈ F, A.Nonempty) (S : Finset V) :
    ∃ U ⊆ S, S.card ≤ U.card + F.card ∧ ∀ A ∈ F, ¬ A ⊆ U := by
  induction F using Finset.induction_on generalizing S with
  | empty => exact ⟨S, Subset.rfl, by simp, by simp⟩
  | @insert A F hAF ih =>
    obtain ⟨U, hUS, hUcard, hU⟩ := ih (fun B hB => hF B (mem_insert_of_mem hB)) S
    by_cases hAU : A ⊆ U
    · obtain ⟨x, hx⟩ := hF A (mem_insert_self A F)
      refine ⟨U.erase x, (erase_subset x U).trans hUS, ?_, ?_⟩
      · have he := card_erase_of_mem (hAU hx)
        rw [card_insert_of_notMem hAF]
        omega
      · intro B hB hBU
        rcases mem_insert.mp hB with rfl | hB
        · exact (notMem_erase x U) (hBU hx)
        · exact hU B hB (hBU.trans (erase_subset x U))
    · refine ⟨U, hUS, ?_, ?_⟩
      · rw [card_insert_of_notMem hAF]
        omega
      · intro B hB hBU
        rcases mem_insert.mp hB with rfl | hB
        · exact hAU hBU
        · exact hU B hB hBU

theorem prune (S : Finset V) {D : ℝ} (hD : 0 < D) :
    ∃ U ⊆ S,
      (S.card : ℝ) - degreeMass G S / D - count (G.cliqueFinset 3) S ≤ U.card ∧
      (∀ x ∈ U, (internalDegree G U x : ℝ) ≤ D) ∧
      (G.induce (U : Set V)).CliqueFree 3 := by
  let bad := S.filter (fun x => D < (internalDegree G S x : ℝ))
  have hbad : (bad.card : ℝ) ≤ degreeMass G S / D := by
    apply (le_div_iff₀ hD).mpr
    calc
      (bad.card : ℝ) * D = ∑ _x ∈ bad, D := by simp
      _ ≤ ∑ x ∈ bad, (internalDegree G S x : ℝ) := by
        exact sum_le_sum (fun x hx => (mem_filter.mp hx).2.le)
      _ ≤ ∑ x ∈ S, (internalDegree G S x : ℝ) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)
      _ = degreeMass G S := by simp [degreeMass, Nat.cast_sum]
  let T := S \ bad
  let F := (G.cliqueFinset 3).filter (· ⊆ S)
  have hF : ∀ A ∈ F, A.Nonempty := by
    intro A hA
    have ha := (SimpleGraph.mem_cliqueFinset_iff.mp (mem_filter.mp hA).1).2
    exact card_pos.mp (by omega)
  obtain ⟨U, hUT, hcard, havoid⟩ := exists_avoid_family F hF T
  have hUS : U ⊆ S := hUT.trans sdiff_subset
  refine ⟨U, hUS, ?_, ?_, ?_⟩
  · have hc : (S.card : ℝ) ≤ T.card + bad.card := by
      exact_mod_cast card_le_card_sdiff_add_card
    have hu : (T.card : ℝ) ≤ U.card + F.card := by exact_mod_cast hcard
    change (S.card : ℝ) - degreeMass G S / D - F.card ≤ _
    linarith
  · intro x hx
    have hxT := mem_sdiff.mp (hUT hx)
    have hd : (internalDegree G S x : ℝ) ≤ D := by
      by_contra! hh
      exact hxT.2 (mem_filter.mpr ⟨hxT.1, hh⟩)
    exact (Nat.cast_le.mpr (card_le_card (filter_subset_filter _ hUS))).trans hd
  · rw [G.cliqueFree_induce_iff]
    intro A hAU hA
    have hAF : A ∈ F := mem_filter.mpr
      ⟨SimpleGraph.mem_cliqueFinset_iff.mpr hA, (show A ⊆ U from hAU).trans hUS⟩
    exact havoid A hAF hAU

omit [Fintype V] [DecidableEq V] in
theorem induced_degree (U : Finset V) (x : (U : Set V)) :
    (G.induce (U : Set V)).degree x = internalDegree G U x := by
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  let e : ((G.induce (U : Set V)).neighborSet x) ≃
      {y : V // y ∈ U.filter (G.Adj x)} :=
    { toFun := fun y => ⟨y.1, mem_filter.mpr ⟨y.1.2, y.2⟩⟩
      invFun := fun y => ⟨⟨y.1, (mem_filter.mp y.2).1⟩, (mem_filter.mp y.2).2⟩
      left_inv := by intro y; rfl
      right_inv := by intro y; rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_coe (U.filter (G.Adj x)))

theorem sample_prune {p D : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (hD : 0 < D) :
    ∃ U : Finset V,
      p * Fintype.card V - p^2 * (∑ x, (G.degree x : ℝ)) / D -
        p^3 * (G.cliqueFinset 3).card ≤ U.card ∧
      (∀ x : (U : Set V), ((G.induce (U : Set V)).degree x : ℝ) ≤ D) ∧
      (G.induce (U : Set V)).CliqueFree 3 := by
  let X (f : V → Bool) : ℝ := (selected f).card -
    degreeMass G (selected f) / D - count (G.cliqueFinset 3) (selected f)
  have hmean : (∑ f, weight p f * X f) =
      p * Fintype.card V - p^2 * (∑ x, (G.degree x : ℝ)) / D -
        p^3 * (G.cliqueFinset 3).card := by
    simp only [X, mul_sub, ← mul_div_assoc, sum_sub_distrib, ← sum_div]
    rw [size_moment, degreeMass_moment, family_moment]
    intro A hA
    exact (SimpleGraph.mem_cliqueFinset_iff.mp hA).2
  obtain ⟨f, hf⟩ := exists_ge_mean hp hp1 X
  rw [hmean] at hf
  obtain ⟨U, _hUS, hU, hdeg, htri⟩ := prune G (selected f) hD
  refine ⟨U, hf.trans hU, ?_, htri⟩
  intro x
  rw [induced_degree]
  exact hdeg x x.2

theorem triangle_count_le {h m : ℕ} (hdeg : ∀ x, G.degree x ≤ h)
    (hcommon : ∀ x y, G.Adj x y → Fintype.card (G.commonNeighbors x y) ≤ m) :
    (G.cliqueFinset 3).card ≤ Fintype.card V * h * m := by
  let T := Σ x : V, Σ y : G.neighborSet x, G.commonNeighbors x y
  have hex (A : {A // A ∈ G.cliqueFinset 3}) :
      ∃ t : T, A.1 = {t.1, t.2.1.1, t.2.2.1} := by
    obtain ⟨x,y,z,hxy,hxz,hyz,hA⟩ := SimpleGraph.is3Clique_iff.mp
      (SimpleGraph.mem_cliqueFinset_iff.mp A.2)
    exact ⟨⟨x, ⟨y,hxy⟩, ⟨z,hxz,hyz⟩⟩, hA⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro A B hAB
    apply Subtype.ext
    rw [hf A, hf B, hAB]
  calc
    (G.cliqueFinset 3).card = Fintype.card {A // A ∈ G.cliqueFinset 3} := (Fintype.card_coe _).symm
    _ ≤ Fintype.card T := Fintype.card_le_of_injective f hinj
    _ = ∑ x : V, ∑ y : G.neighborSet x, Fintype.card (G.commonNeighbors x y) := by
      simp [T, Fintype.card_sigma]
    _ ≤ ∑ x : V, ∑ _y : G.neighborSet x, m := by
      exact sum_le_sum (fun x _ => sum_le_sum (fun y _ => hcommon x y y.2))
    _ ≤ ∑ _x : V, h*m := by
      apply sum_le_sum
      intro x _
      simpa [G.card_neighborSet_eq_degree] using Nat.mul_le_mul_right m (hdeg x)
    _ = Fintype.card V * h * m := by simp [mul_assoc]

end SharpLogRamsey.Sampling

open scoped BigOperators
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Bounds_SamplingParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The off-diagonal Ramsey upper bound. -/

section
open scoped BigOperators Classical
open Finset
open scoped BigOperators Classical
open Finset
open scoped BigOperators Classical
open Finset
open scoped BigOperators
namespace SharpLogRamsey.Upper
theorem sampling_parameter {h m t : ℝ} (hh : 1 ≤ h) (hm : 1 ≤ m)
    (ht : 65536 ≤ t) (hratio : m * Real.sqrt t ≤ h) :
    ∃ p : ℝ, 0 < p ∧ p ≤ 1 ∧ 1 ≤ p*h ∧ p^2*h*m ≤ 1/8 ∧
      Real.log t ≤ 8 * Real.log (p*h) := by
  have hh0 : 0 < h := by linarith
  have hm0 : 0 < m := by linarith
  have ht0 : 0 < t := by linarith
  have hs : 0 < Real.sqrt (h*m) := Real.sqrt_pos.mpr (mul_pos hh0 hm0)
  let p := 1 / (4 * Real.sqrt (h*m))
  have hp : 0 < p := by dsimp [p]; positivity
  have hs1 : 1 ≤ Real.sqrt (h*m) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith
  have hp1 : p ≤ 1 := by
    dsimp [p]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hsq := Real.sq_sqrt (show 0 ≤ h*m by positivity)
  have hmoment : p^2*h*m = 1/16 := by
    dsimp [p]
    field_simp
    nlinarith
  have hlog : Real.log (p*h) = (Real.log h - Real.log m)/2 - Real.log 4 := by
    dsimp [p]
    rw [Real.log_mul (by positivity) hh0.ne', Real.log_div (by norm_num) (by positivity),
      Real.log_one, Real.log_mul (by norm_num) hs.ne', Real.log_sqrt (by positivity : 0 ≤ h*m),
      Real.log_mul hh0.ne' hm0.ne']
    ring
  have hratio' := Real.log_le_log (mul_pos hm0 (Real.sqrt_pos.mpr ht0)) hratio
  rw [Real.log_mul hm0.ne' (Real.sqrt_pos.mpr ht0).ne', Real.log_sqrt ht0.le] at hratio'
  have htlog := Real.log_le_log (show (0:ℝ) < 65536 by norm_num) ht
  have h65536 : Real.log (65536:ℝ) = 8 * Real.log 4 := by
    rw [show (65536:ℝ) = 4^8 by norm_num, Real.log_pow]
    norm_num
  rw [h65536] at htlog
  have hl : Real.log t ≤ 8 * Real.log (p*h) := by linarith
  have hl0 : 0 ≤ Real.log (p*h) := by
    have htl : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
    linarith
  have hph : 1 ≤ p*h := by
    exact (Real.log_nonneg_iff (by positivity)).mp hl0
  exact ⟨p,hp,hp1,hph,by linarith,hl⟩

end SharpLogRamsey.Upper

namespace SharpLogRamsey.Upper
open Foundation Sampling
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

theorem alteration_bound {h m t : ℕ} (ht : 1 ≤ t)
    (hG : Gᶜ.CliqueFree t) (hdeg : ∀ x, G.degree x ≤ h)
    (hcommon : ∀ x y, G.Adj x y → Fintype.card (G.commonNeighbors x y) ≤ m)
    {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hph : 1 ≤ p*h) (hmoment : p^2*h*m ≤ 1/8) :
    (Fintype.card V : ℝ) * Real.log (p*h) ≤ 256 * t * h := by
  let n : ℝ := Fintype.card V
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hhp : (0:ℝ) < h := by nlinarith
  have hD : 0 < 12*p*h := by positivity
  obtain ⟨U,hU,hUd,hUt⟩ := sample_prune G hp.le hp1 hD
  have hsum : (∑ x : V, (G.degree x : ℝ)) ≤ n*h := by
    calc
      _ ≤ ∑ _x : V, (h : ℝ) := sum_le_sum (fun x _ => by exact_mod_cast hdeg x)
      _ = n*h := by simp [n]
  have htri : ((G.cliqueFinset 3).card : ℝ) ≤ n*h*m := by
    dsimp [n]
    exact_mod_cast triangle_count_le G hdeg hcommon
  have hloss : p^2 * (∑ x : V, (G.degree x : ℝ)) / (12*p*h) ≤ n*p/12 := by
    apply (div_le_iff₀ hD).mpr
    calc
      _ ≤ p^2*(n*h) := mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
      _ = n*p/12*(12*p*h) := by ring
  have htri' : p^3 * ((G.cliqueFinset 3).card : ℝ) ≤ n*p/8 := by
    calc
      _ ≤ p^3*(n*h*m) := mul_le_mul_of_nonneg_left htri (by positivity)
      _ = n*p*(p^2*h*m) := by ring
      _ ≤ n*p*(1/8) := mul_le_mul_of_nonneg_left hmoment (by positivity)
      _ = n*p/8 := by ring
  have hUsize : 3/4*n*p ≤ (U.card : ℝ) := by dsimp [n] at *; linarith
  have hlog : 0 ≤ Real.log (p*h) := Real.log_nonneg hph
  by_cases hn0 : n = 0
  · change n * _ ≤ _
    rw [hn0, zero_mul]
    positivity
  have hnpos : 0 < n := lt_of_le_of_ne hn (Ne.symm hn0)
  have hUpos : 0 < U.card := by
    have hu : (0:ℝ) < U.card := lt_of_lt_of_le (by positivity) hUsize
    exact_mod_cast hu
  obtain ⟨x,hx⟩ := card_pos.mp hUpos
  let : Nonempty (U : Set V) := ⟨⟨x,hx⟩⟩
  have ha := TriangleFree.indepNum_lower_bound (G.induce (U : Set V)) hUt
    (by nlinarith : (1:ℝ) ≤ 12*p*h) hUd
  have hat : ((G.induce (U : Set V)).indepNum : ℝ) < t := by
    exact_mod_cast indepNum_lt_of_cliqueFree_compl (G.induce (U : Set V))
      (compl_cliqueFree_induce G hG _)
  have ha' : (U.card : ℝ) * Real.log (12*p*h+1) < t*(8*(12*p*h+1)) := by
    have H := ha.trans_lt hat
    rw [div_lt_iff₀ (by positivity)] at H
    have hc : Fintype.card (U : Set V) = U.card := Fintype.card_coe U
    simpa only [hc] using H
  have hl : Real.log (p*h) ≤ Real.log (12*p*h+1) :=
    Real.log_le_log (by positivity) (by nlinarith)
  have hu : (3/4*n*p) * Real.log (p*h) ≤
      (U.card : ℝ) * Real.log (12*p*h+1) :=
    mul_le_mul hUsize hl hlog (Nat.cast_nonneg _)
  have hd : t*(8*(12*p*h+1)) ≤ 104*t*p*h := by
    have ht0 : (0:ℝ) ≤ t := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hph ht0]
  have H := (hu.trans_lt ha').trans_le hd
  have ht0 : (0:ℝ) ≤ t := Nat.cast_nonneg _
  change n*Real.log (p*h) ≤ _
  have : p*(n*Real.log (p*h)) ≤ p*(256*t*h) := by nlinarith
  exact (mul_le_mul_iff_right₀ hp).mp this

theorem graph_recurrence (j : ℕ) {t : ℕ} (ht : 65536 ≤ t)
    (hs : G.CliqueFree (j+4)) (hi : Gᶜ.CliqueFree t) :
    (Fintype.card V : ℝ) ≤
      t*((t:ℝ)^(j+1)*Real.sqrt t+1) +
        2048*t*(ramsey (j+3) t)/Real.log t := by
  let h := G.maxDegree
  let m := ramsey (j+2) t
  have ht1 : 1 ≤ t := by omega
  have ht0 : (0:ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hlog : 0 < Real.log t := Real.log_pos (by exact_mod_cast (show 1 < t by omega))
  have hm1 : 1 ≤ m := ht1.trans (le_ramsey (by omega) ht1)
  have hmb : (m : ℝ) ≤ (t:ℝ)^(j+1) := by
    have H := ramsey_le_pow (s := j+2) (by omega) ht1
    norm_num at H
    exact_mod_cast H
  have hcommon : ∀ x y, G.Adj x y → Fintype.card (G.commonNeighbors x y) ≤ m := by
    intro x y hxy
    exact (order_lt_ramsey (G.induce (G.commonNeighbors x y)) (by omega) ht1
      (cliqueFree_common G hs hxy) (compl_cliqueFree_induce G hi _)).le
  have hdeg : ∀ x, G.degree x ≤ h := G.degree_le_maxDegree
  have hhr : h ≤ ramsey (j+3) t := by
    apply G.maxDegree_le_of_forall_degree_le
    intro x
    have H := order_lt_ramsey (G.induce (G.neighborSet x)) (by omega) ht1
      (cliqueFree_neighbor G hs x) (compl_cliqueFree_induce G hi _)
    rw [G.card_neighborSet_eq_degree] at H
    exact H.le
  have hright : 0 ≤ 2048*(t:ℝ)*(ramsey (j+3) t)/Real.log t := by positivity
  by_cases hsmall : (h:ℝ) ≤ m*Real.sqrt t
  · have hn := card_le_mul_indepNum G (B := h+1) (by intro x; exact Nat.add_le_add_right (hdeg x) 1)
    have hia := indepNum_lt_of_cliqueFree_compl G hi
    have Hnat : Fintype.card V ≤ (h+1)*t := hn.trans (Nat.mul_le_mul_left _ hia.le)
    have H : (Fintype.card V : ℝ) ≤ ((h:ℝ)+1)*t := by exact_mod_cast Hnat
    have hm' := mul_le_mul_of_nonneg_right hmb (Real.sqrt_nonneg (t:ℝ))
    have H' := mul_le_mul_of_nonneg_right (add_le_add_right (hsmall.trans hm') 1) ht0.le
    nlinarith
  · have hh : (1:ℝ) ≤ h := by
      have hsqrt : 1 ≤ Real.sqrt (t:ℝ) := by
        rw [Real.le_sqrt (by norm_num) ht0.le]
        exact_mod_cast ht1
      have hm1' : (1:ℝ) ≤ m := by exact_mod_cast hm1
      nlinarith
    obtain ⟨p,hp,hp1,hph,hpm,hl⟩ := sampling_parameter hh (by exact_mod_cast hm1)
      (by exact_mod_cast ht) (le_of_not_ge hsmall)
    have hab := alteration_bound G ht1 hi hdeg hcommon hp hp1 hph hpm
    have hn0 : (0:ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
    have H : (Fintype.card V : ℝ)*Real.log t ≤ 2048*t*h := by
      nlinarith [mul_le_mul_of_nonneg_left hl hn0]
    have H' : (Fintype.card V : ℝ) ≤ 2048*t*h/Real.log t :=
      (le_div_iff₀ hlog).mpr H
    have H'' : 2048*(t:ℝ)*h/Real.log t ≤ 2048*t*(ramsey (j+3) t)/Real.log t := by
      apply div_le_div_of_nonneg_right _ hlog.le
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hhr) (by positivity)
    have hleft : 0 ≤ (t:ℝ)*((t:ℝ)^(j+1)*Real.sqrt t+1) := by positivity
    linarith

theorem ramsey_recurrence (j : ℕ) {t : ℕ} (ht : 65536 ≤ t) :
    (ramsey (j+4) t : ℝ) ≤
      t*((t:ℝ)^(j+1)*Real.sqrt t+1) +
        2048*t*(ramsey (j+3) t)/Real.log t + 1 := by
  classical
  obtain ⟨G,hG,hGi⟩ := exists_avoiding_pred (s := j+4) (by omega) (by omega : 2 ≤ t)
  have H := graph_recurrence G j ht hG hGi
  simp only [Fintype.card_fin] at H
  have hr : 1 ≤ ramsey (j+4) t :=
    (by omega : 1 ≤ t).trans (le_ramsey (by omega) (by omega))
  rw [Nat.cast_sub hr, Nat.cast_one] at H
  linarith

theorem ramsey_three {t : ℕ} (ht : 2 ≤ t) :
    (ramsey 3 t : ℝ)*Real.log t ≤ 17*(t:ℝ)^2 := by
  classical
  obtain ⟨G,hG,hGi⟩ := exists_avoiding_pred (s := 3) (by omega) ht
  have hr : 2 ≤ ramsey 3 t := ht.trans (le_ramsey (by omega) (by omega))
  have hnon : 0 < ramsey 3 t - 1 := by omega
  let : Nonempty (Fin (ramsey 3 t - 1)) := Fin.pos_iff_nonempty.mp hnon
  have hd : ∀ x, (G.degree x : ℝ) ≤ t := by
    intro x
    have H := order_lt_ramsey (G.induce (G.neighborSet x)) (by omega : 2 ≤ 2)
      (by omega : 1 ≤ t) (cliqueFree_neighbor G hG x) (compl_cliqueFree_induce G hGi _)
    rw [G.card_neighborSet_eq_degree, ramsey_two (by omega)] at H
    exact_mod_cast H.le
  have ht0 : (0:ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have ht1 : (1:ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
  have hl : 0 ≤ Real.log (t:ℝ) := Real.log_nonneg ht1
  have H := TriangleFree.indepNum_lower_bound G hG ht1 hd
  have hi : (G.indepNum : ℝ) < t := by
    exact_mod_cast indepNum_lt_of_cliqueFree_compl G hGi
  have H' := H.trans_lt hi
  rw [div_lt_iff₀ (by positivity)] at H'
  have hc : (Fintype.card (Fin (ramsey 3 t - 1)) : ℝ) = (ramsey 3 t : ℝ)-1 := by
    rw [Fintype.card_fin, Nat.cast_sub (by omega), Nat.cast_one]
  rw [hc] at H'
  have hl' : Real.log (t:ℝ) ≤ Real.log ((t:ℝ)+1) := Real.log_le_log ht0 (by linarith)
  have hn : 0 ≤ (ramsey 3 t : ℝ)-1 := by
    have H : (2:ℝ) ≤ ramsey 3 t := by exact_mod_cast hr
    linarith
  have hh := mul_le_mul_of_nonneg_left hl' hn
  have hlt := Real.log_le_self ht0.le
  nlinarith [sq_nonneg ((t:ℝ)-1)]

open Filter in
 theorem eventually_log_pow_le_sqrt (j : ℕ) :
    ∀ᶠ t : ℕ in atTop, (Real.log (t:ℝ))^j ≤ Real.sqrt t := by
  have H := (isLittleO_log_rpow_rpow_atTop (j:ℝ) (by norm_num : (0:ℝ)<1/2)).bound
    (by norm_num : (0:ℝ)<1)
  have Hn := tendsto_natCast_atTop_atTop.eventually H
  filter_upwards [Hn, eventually_ge_atTop (1:ℕ)] with t ht ht1
  have hlog := Real.log_nonneg (show (1:ℝ) ≤ t by exact_mod_cast ht1)
  simpa only [Real.rpow_natCast, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hlog _),
    ← Real.sqrt_eq_rpow, abs_of_nonneg (Real.sqrt_nonneg _), one_mul] using ht

open Filter in

 theorem ramsey_upper_scaled (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℕ in atTop,
      (ramsey (j+3) t : ℝ)*(Real.log (t:ℝ))^(j+1) ≤ C*(t:ℝ)^(j+2) := by
  induction j with
  | zero =>
    refine ⟨17, by norm_num, ?_⟩
    filter_upwards [eventually_ge_atTop (2:ℕ)] with t ht
    simpa using ramsey_three ht
  | succ j ih =>
    obtain ⟨C,hC,hCb⟩ := ih
    refine ⟨3+2048*C, by positivity, ?_⟩
    filter_upwards [hCb, eventually_log_pow_le_sqrt (j+2),
      eventually_ge_atTop (65536:ℕ)] with t hCt hL ht
    have ht1 : (1:ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
    have ht0 : (0:ℝ) < t := by exact_mod_cast (show 0 < t by omega)
    have hl : 0 < Real.log (t:ℝ) := Real.log_pos (by exact_mod_cast (show 1 < t by omega))
    have hs := Real.sqrt_nonneg (t:ℝ)
    have hs2 := Real.sq_sqrt ht0.le
    have hst : Real.sqrt (t:ℝ) ≤ t := by
      rw [Real.sqrt_le_iff]
      exact ⟨ht0.le, by nlinarith⟩
    have hpow : (t:ℝ)^2 ≤ (t:ℝ)^(j+3) := pow_le_pow_right₀ ht1 (by omega)
    have hsmall : (t*((t:ℝ)^(j+1)*Real.sqrt t+1)+1)*(Real.log (t:ℝ))^(j+2) ≤
        3*(t:ℝ)^(j+3) := by
      calc
        _ ≤ (t*((t:ℝ)^(j+1)*Real.sqrt t+1)+1)*Real.sqrt t :=
          mul_le_mul_of_nonneg_left hL (by positivity)
        _ = (t:ℝ)^(j+1)*t*(Real.sqrt t)^2+(t+1)*Real.sqrt t := by ring
        _ = (t:ℝ)^(j+3)+(t+1)*Real.sqrt t := by
          rw [hs2]
          simp only [pow_succ]
        _ ≤ (t:ℝ)^(j+3)+2*(t:ℝ)^2 := by
          have H := mul_le_mul_of_nonneg_left hst (by positivity : (0:ℝ) ≤ t+1)
          nlinarith
        _ ≤ 3*(t:ℝ)^(j+3) := by linarith
    have hmain : (2048*t*(ramsey (j+3) t)/Real.log t)*(Real.log (t:ℝ))^(j+2) ≤
        (2048*C)*(t:ℝ)^(j+3) := by
      calc
        _ = 2048*t*((ramsey (j+3) t : ℝ)*(Real.log (t:ℝ))^(j+1)) := by
          rw [show j+2 = (j+1)+1 from by omega, pow_succ]
          field_simp
        _ ≤ 2048*t*(C*(t:ℝ)^(j+2)) :=
          mul_le_mul_of_nonneg_left hCt (by positivity)
        _ = (2048*C)*(t:ℝ)^(j+3) := by
          rw [show j+3 = (j+2)+1 from by omega, pow_succ]; ring
    have H := mul_le_mul_of_nonneg_right (ramsey_recurrence j ht)
      (pow_nonneg hl.le (j+2))
    linear_combination H + hsmall + hmain

open Filter in
 theorem ramsey_upper {s : ℕ} (hs : 3 ≤ s) :
    ∃ C : ℝ, 0 < C ∧ ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
      (ramsey s t : ℝ) ≤ C*(t:ℝ)^(s-1)/(Real.log (t:ℝ))^(s-2) := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hs
  obtain ⟨C,hC,hCb⟩ := ramsey_upper_scaled j
  refine ⟨C,hC,?_⟩
  have H : ∀ᶠ t : ℕ in atTop,
      (ramsey (3+j) t : ℝ) ≤ C*(t:ℝ)^(3+j-1)/(Real.log (t:ℝ))^(3+j-2) := by
    filter_upwards [hCb, eventually_ge_atTop (2:ℕ)] with t ht ht2
    have hl : 0 < Real.log (t:ℝ) := Real.log_pos (by exact_mod_cast (show 1 < t by omega))
    apply (le_div_iff₀ (pow_pos hl _)).mpr
    simpa [show 3+j = j+3 from by omega] using ht
  exact eventually_atTop.mp H

end SharpLogRamsey.Upper

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Bounds_Lower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer of finite prime-field graph constructions to all sufficiently large orders. -/

section
namespace SharpLogRamsey.LowerTransfer
open Filter Real
open scoped Topology
noncomputable section

theorem prime_interval (x : ℝ) (hx : 4 ≤ x) :
    ∃ q : ℕ, q.Prime ∧ x/4 ≤ q ∧ (q:ℝ) ≤ x := by
  let n := ⌊x/2⌋₊
  have hn : 1 ≤ n := (Nat.one_le_floor_iff _).mpr (by linarith)
  obtain ⟨q,hq,hnq,hqn⟩ := Nat.exists_prime_lt_and_le_two_mul n (by omega)
  refine ⟨q,hq,?_,?_⟩
  · have hnf := Nat.lt_floor_add_one (x/2)
    have hnqr : (n:ℝ)+1 ≤ q := by exact_mod_cast hnq
    dsimp [n] at hnqr
    linarith
  · have hnf := Nat.floor_le (show 0≤x/2 by linarith)
    have hqn' : (q:ℝ) ≤ 2*n := by exact_mod_cast hqn
    dsimp [n] at hqn'
    linarith

theorem witness_bound (d q t : ℕ) (η : ℝ) (hd : 1≤d) (ht : 1≤t)
    (G : SimpleGraph (Fin ⌊(q:ℝ)^d * Real.log q⌋₊))
    (hG : G.CliqueFree (d+1))
    (hI : G.indepNum < ⌊(q:ℝ)*(Real.log q)^(1+η)⌋₊)
    (hqt : (q:ℝ)*(Real.log q)^(1+η) ≤ t) :
    (q:ℝ)^d * Real.log q < (ramsey (d+1) t : ℝ) := by
  have hk : ⌊(q:ℝ)*(Real.log q)^(1+η)⌋₊ ≤ t := Nat.floor_le_of_le hqt
  have hf : Gᶜ.CliqueFree t := by
    intro A hA
    have hi := G.isNClique_compl.mp hA
    have hle := hi.isIndepSet.card_le_indepNum
    have hc := hi.card_eq
    omega
  have hr := Foundation.order_lt_ramsey G (by omega) ht hG hf
  simp only [Fintype.card_fin] at hr
  have hr' : (⌊(q:ℝ)^d * Real.log q⌋₊ :ℝ)+1 ≤ ramsey (d+1) t := by
    exact_mod_cast hr
  exact (Nat.lt_floor_add_one _).trans_le hr'

theorem eventual_scale (η : ℝ) : ∀ᶠ t : ℝ in atTop,
    1 < t ∧ 1 ≤ Real.log t ∧
    4*t^((1:ℝ)/2) ≤ t/(Real.log t)^(1+η) := by
  have h := (isLittleO_log_rpow_rpow_atTop (1+η) (show 0<(1:ℝ)/2 by norm_num)).bound
    (show 0<(1:ℝ)/4 by norm_num)
  filter_upwards [h,eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop 1]
    with t ht ht1 hl
  refine ⟨ht1,hl,?_⟩
  have ht0 : 0<t := by linarith
  have hl0 : 0<Real.log t := by linarith
  simp only [Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hl0 _),
    abs_of_pos (Real.rpow_pos_of_pos ht0 _)] at ht
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hl0 _)).mpr
  have hp : t^((1:ℝ)/2)*t^((1:ℝ)/2)=t := by
    rw [←Real.rpow_add ht0]; norm_num
  nlinarith [mul_le_mul_of_nonneg_left ht (Real.rpow_nonneg ht0.le ((1:ℝ)/2))]

theorem interval_bounds (η t q : ℝ) (hη : 0≤η) (ht : 1<t) (hl : 1≤Real.log t)
    (hscale : 4*t^((1:ℝ)/2) ≤ t/(Real.log t)^(1+η))
    (hqlo : (t/(Real.log t)^(1+η))/4 ≤ q)
    (hqhi : q ≤ t/(Real.log t)^(1+η)) :
    0<q ∧ Real.log t/2 ≤ Real.log q ∧
    q*(Real.log q)^(1+η) ≤ t := by
  have ht0 : 0<t := by linarith
  have hl0 : 0<Real.log t := by linarith
  have hp : 0<(Real.log t)^(1+η) := Real.rpow_pos_of_pos hl0 _
  have hqs : t^((1:ℝ)/2)≤q := by linarith
  have hq0 : 0<q := (Real.rpow_pos_of_pos ht0 _).trans_le hqs
  refine ⟨hq0,?_,?_⟩
  · have hlog := Real.log_le_log (Real.rpow_pos_of_pos ht0 _) hqs
    rw [Real.log_rpow ht0] at hlog
    linarith
  · have hden : 1≤(Real.log t)^(1+η) := Real.one_le_rpow hl (by linarith)
    have hqt : q≤t := hqhi.trans (div_le_self ht0.le hden)
    have hq1 : 1≤q := (Real.one_le_rpow ht.le (by norm_num)).trans hqs
    have hlogq : 0≤Real.log q := Real.log_nonneg hq1
    have hpow : (Real.log q)^(1+η)≤(Real.log t)^(1+η) :=
      Real.rpow_le_rpow hlogq (Real.log_le_log hq0 hqt) (by linarith)
    calc
      q*(Real.log q)^(1+η) ≤ q*(Real.log t)^(1+η) := mul_le_mul_of_nonneg_left hpow hq0.le
      _ ≤ (t/(Real.log t)^(1+η))*(Real.log t)^(1+η) :=
        mul_le_mul_of_nonneg_right hqhi hp.le
      _ = t := div_mul_cancel₀ _ hp.ne'

theorem scalar_lower (d : ℕ) (hd : 1≤d) (η ε t q : ℝ)
    (ht : 0≤t) (hl : 0<Real.log t) (hq : 0≤q)
    (hqlo : (t/(Real.log t)^(1+η))/4 ≤ q)
    (hlog : Real.log t/2 ≤ Real.log q)
    (habsorb : 2*(4:ℝ)^d ≤ (Real.log t)^(ε-(d:ℝ)*η)) :
    t^d/(Real.log t)^(((d-1:ℕ):ℝ)+ε) ≤ q^d*Real.log q := by
  let a : ℝ := ((d-1:ℕ):ℝ)+(d:ℝ)*η
  have he : (1+η)*(d:ℝ)=a+1 := by
    dsimp [a]
    rw [Nat.cast_sub hd]
    norm_num
    ring
  have he' : ((d-1:ℕ):ℝ)+ε=a+(ε-(d:ℝ)*η) := by dsimp [a];ring
  have hpow : ((Real.log t)^(1+η))^d=(Real.log t)^a*Real.log t := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hl.le,he,Real.rpow_add_one hl.ne']
  have hp : 0<(Real.log t)^a := Real.rpow_pos_of_pos hl _
  have hp' : 0<(Real.log t)^(ε-(d:ℝ)*η) := Real.rpow_pos_of_pos hl _
  have h4 : 0<(4:ℝ)^d := by positivity
  have hden : ((Real.log t)^a)*(2*(4:ℝ)^d) ≤
      ((Real.log t)^a)*(Real.log t)^(ε-(d:ℝ)*η) :=
    mul_le_mul_of_nonneg_left habsorb hp.le
  calc
    t^d/(Real.log t)^(((d-1:ℕ):ℝ)+ε) =
        t^d/((Real.log t)^a*(Real.log t)^(ε-(d:ℝ)*η)) := by rw [he',Real.rpow_add hl]
    _ ≤ t^d/((Real.log t)^a*(2*(4:ℝ)^d)) :=
      div_le_div_of_nonneg_left (pow_nonneg ht _) (by positivity) hden
    _ = ((t/(Real.log t)^(1+η))/4)^d*(Real.log t/2) := by
      rw [div_pow,div_pow,hpow]
      field_simp
    _ ≤ q^d*Real.log q := by
      apply mul_le_mul
      · exact pow_le_pow_left₀ (by positivity) hqlo _
      · exact hlog
      · positivity
      · exact pow_nonneg hq _

theorem lower_from_prime_construction (d : ℕ) (hd : 1≤d) (hprime : PrimeConstruction d)
    (η ε : ℝ) (hη : 0<η) (hη' : η<1/10) (hε : (d:ℝ)*η<ε) :
    ∀ᶠ t : ℕ in atTop,
      (t:ℝ)^d/(Real.log t)^(((d-1:ℕ):ℝ)+ε) ≤ (ramsey (d+1) t :ℝ) := by
  obtain ⟨q₀,hq₀⟩ := eventually_atTop.mp (hprime η hη hη')
  have hcoef : ∀ᶠ t : ℝ in atTop,
      2*(4:ℝ)^d ≤ (Real.log t)^(ε-(d:ℝ)*η) :=
    ((tendsto_rpow_atTop (by linarith : 0<ε-(d:ℝ)*η)).comp
      Real.tendsto_log_atTop).eventually_ge_atTop _
  have hsqr : ∀ᶠ t : ℝ in atTop, max 1 (q₀:ℝ) ≤ t^((1:ℝ)/2) :=
    (tendsto_rpow_atTop (by norm_num : 0<(1:ℝ)/2)).eventually_ge_atTop _
  have H : ∀ᶠ t : ℝ in atTop,
      1<t ∧ 1≤Real.log t ∧ 4*t^((1:ℝ)/2)≤t/(Real.log t)^(1+η) ∧
        max 1 (q₀:ℝ)≤t^((1:ℝ)/2) ∧
          2*(4:ℝ)^d≤(Real.log t)^(ε-(d:ℝ)*η) := by
    filter_upwards [eventual_scale η,hsqr,hcoef] with t ht hs hc
    exact ⟨ht.1,ht.2.1,ht.2.2,hs,hc⟩
  filter_upwards [tendsto_natCast_atTop_atTop.eventually H] with t ht
  obtain ⟨ht1,hl,hs,hqmin,hcoef⟩ := ht
  have hx4 : 4 ≤ (t:ℝ)/(Real.log t)^(1+η) := by
    have := (le_max_left (1:ℝ) q₀).trans hqmin
    linarith
  obtain ⟨q,hq,hql,hqu⟩ := prime_interval _ hx4
  have hq₀' : q₀≤q := by
    have hreal : (q₀:ℝ)≤q := by
      have := (le_max_right (1:ℝ) q₀).trans hqmin
      linarith
    exact_mod_cast hreal
  obtain ⟨G,hG,hI⟩ := hq₀ q hq₀' hq
  obtain ⟨hqpos,hlog,hsize⟩ := interval_bounds η t q hη.le ht1 hl hs hql hqu
  have hr := witness_bound d q t η hd (by exact_mod_cast ht1.le) G hG hI hsize
  exact (scalar_lower d hd η ε t q (by positivity) (by linarith) hqpos.le hql hlog hcoef).trans hr.le

theorem all_epsilon_lower (d : ℕ) (hd : 1≤d) (hprime : PrimeConstruction d)
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ t : ℕ in atTop,
      (t:ℝ)^d/(Real.log t)^(((d-1:ℕ):ℝ)+ε) ≤ (ramsey (d+1) t :ℝ) := by
  let η := min (1/20:ℝ) (ε/(2*(d:ℝ)))
  have hd0 : 0<(d:ℝ) := by exact_mod_cast (show 0<d by omega)
  have hη : 0<η := lt_min (by norm_num) (by positivity)
  have hη' : η<1/10 := (min_le_left _ _).trans_lt (by norm_num)
  have hηε : (d:ℝ)*η<ε := by
    have h := mul_le_mul_of_nonneg_left (min_le_right (1/20:ℝ) (ε/(2*(d:ℝ)))) hd0.le
    have he : (d:ℝ)*(ε/(2*(d:ℝ)))=ε/2 := by field_simp
    rw [he] at h
    exact h.trans_lt (by linarith)
  exact lower_from_prime_construction d hd hprime η ε hη hη' hηε

end
end SharpLogRamsey.LowerTransfer

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Bounds_FromConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two-sided Ramsey bounds and the logarithmic limit from a prime-field construction. -/

section
namespace SharpLogRamsey

theorem mainLimit_of_mainBounds (s : ℕ) (h : MainBounds s) : MainLimit s := by
  obtain ⟨C,hC,h⟩ := h
  have hlog : Filter.Tendsto (fun t : ℕ => Real.log (t:ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Filter.Tendsto (fun t : ℕ => Real.log (Real.log (t:ℝ)))
      Filter.atTop Filter.atTop := Real.tendsto_log_atTop.comp hlog
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨t₀,ht₀⟩ := h (ε/2) (by positivity)
  obtain ⟨t₁,ht₁⟩ := Filter.eventually_atTop.mp
    (hloglog.eventually (Filter.eventually_gt_atTop (max 0 (2*|Real.log C|/ε))))
  refine ⟨max (max t₀ t₁) 2, fun t ht => ?_⟩
  have htl : t₀≤t := (le_max_left t₀ t₁).trans ((le_max_left _ _).trans ht)
  have htll : t₁≤t := (le_max_right t₀ t₁).trans ((le_max_left _ _).trans ht)
  have ht2 : 2≤t := (le_max_right _ _).trans ht
  have htp : (0:ℝ)<t := by exact_mod_cast (by omega : 0<t)
  have hlt : 0<Real.log (t:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1<t))
  have hll0 : 0<Real.log (Real.log (t:ℝ)) := (le_max_left _ _).trans_lt (ht₁ t htll)
  have hllbig : 2*|Real.log C|/ε<Real.log (Real.log (t:ℝ)) :=
    (le_max_right _ _).trans_lt (ht₁ t htll)
  obtain ⟨hl,hu⟩ := ht₀ t htl
  have hp : 0<(t:ℝ)^(s-1)/Real.rpow (Real.log (t:ℝ)) ((s-2:ℕ)+(ε/2)) :=
    div_pos (pow_pos htp _) (Real.rpow_pos_of_pos hlt _)
  have hr : 0<(ramsey s t:ℝ) := hp.trans_le hl
  have hl' := Real.log_le_log hp hl
  change Real.log ((t:ℝ)^(s-1)/(Real.log (t:ℝ))^(((s-2:ℕ):ℝ)+ε/2)) ≤ Real.log (ramsey s t:ℝ) at hl'
  rw [Real.log_div (pow_ne_zero (s-1) (ne_of_gt htp))
    (ne_of_gt (Real.rpow_pos_of_pos hlt (((s-2:ℕ):ℝ)+(ε/2)))), Real.log_pow,Real.log_rpow hlt] at hl'
  have hu' := Real.log_le_log hr hu
  rw [Real.log_div (mul_ne_zero (ne_of_gt hC) (pow_ne_zero (s-1) (ne_of_gt htp)))
    (pow_ne_zero (s-2) (ne_of_gt hlt)), Real.log_mul (ne_of_gt hC)
      (pow_ne_zero (s-1) (ne_of_gt htp)),Real.log_pow,Real.log_pow] at hu'
  have herr : |Real.log C| < (ε/2)*Real.log (Real.log (t:ℝ)) := by
    have he := (div_lt_iff₀ hε).mp hllbig
    nlinarith
  have hlow : ((s-2:ℕ):ℝ)-ε/2 <
    (((s-1:ℕ):ℝ)*Real.log (t:ℝ)-Real.log (ramsey s t:ℝ))/
      Real.log (Real.log (t:ℝ)) := by
    apply (lt_div_iff₀ hll0).mpr
    have habs := le_abs_self (Real.log C)
    nlinarith
  have hupp : (((s-1:ℕ):ℝ)*Real.log (t:ℝ)-Real.log (ramsey s t:ℝ))/
      Real.log (Real.log (t:ℝ)) ≤ ((s-2:ℕ):ℝ)+ε/2 := by
    apply (div_le_iff₀ hll0).mpr
    nlinarith
  rw [Real.dist_eq,abs_lt]
  constructor <;> linarith
end SharpLogRamsey

namespace SharpLogRamsey

theorem main_of_primeConstruction (s : ℕ) (hs : 6 ≤ s)
    (hprime : LowerTransfer.PrimeConstruction (s-1)) : MainBounds s ∧ MainLimit s := by
  have hb : MainBounds s := by
    obtain ⟨C,hC,t₀,ht₀⟩ := Upper.ramsey_upper (by omega : 3 ≤ s)
    refine ⟨C,hC,fun ε hε => ?_⟩
    have hl := LowerTransfer.all_epsilon_lower (s-1) (by omega) hprime ε hε
    have he : s-1+1=s := by omega
    have he' : s-1-1=s-2 := by omega
    rw [he,he'] at hl
    obtain ⟨t₁,ht₁⟩ := Filter.eventually_atTop.mp hl
    exact ⟨max t₀ t₁,fun t ht => ⟨ht₁ t ((le_max_right _ _).trans ht),
      ht₀ t ((le_max_left _ _).trans ht)⟩⟩
  exact ⟨hb,mainLimit_of_mainBounds s hb⟩
end SharpLogRamsey

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers. -/

section
namespace SharpLogRamsey

theorem main_oai (s : ℕ) (hs : 6 ≤ s) : MainBounds s ∧ MainLimit s :=
  main_of_primeConstruction s hs (LowerTransfer.prime_construction (s-1) (by omega))
end SharpLogRamsey

end

end OAI
end

theorem solution : type_of% @OAI.SharpLogRamsey.main_oai := @OAI.SharpLogRamsey.main_oai
