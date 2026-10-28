-- Prove2me | solution 1 for OAI.Balanced.pencilReuse_proof
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:23:50.513325+00:00
-- url     : https://prove2.me/submissions/902cc745-f1d0-40a5-823e-40f8701ed119

import Mathlib
import Definitions.Def_OAIQ63Br004

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

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_PartialAlignment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.PartialAlignment
open TupleAlignment

variable {F : Type*}

theorem alignment_exponent_identity (J : Finset (Fin 4)) :
    (freePositions J).card + (4 - (fixedPositions J).card) =
      2 * (freshGenerators J).card := by
  have h : ∀ J : Finset (Fin 4),
      (freePositions J).card + (4 - (fixedPositions J).card) =
        2 * (freshGenerators J).card := by decide
  exact h J

variable [Field F]

section Finite
variable [Fintype F] [DecidableEq F]

theorem card_alignedPartialOffsets_le (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : ∀ i, d i ≠ g) (c : F)
    (J : Finset (Fin 4)) (a : Fin 4 → Bool → F) :
    Fintype.card (AlignedPartialOffsets d hd σ g c J a) ≤
      Fintype.card F ^ (freePositions J).card := by
  calc
    Fintype.card (AlignedPartialOffsets d hd σ g c J a) ≤
        Fintype.card ({i : Fin 4 // i ∈ freePositions J} → F) :=
      Fintype.card_le_of_injective _
        (alignedFreeCoordinates_injective d hd σ g hg c J a)
    _ = _ := by simp

theorem partial_alignment_probability_le (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : ∀ i, d i ≠ g) (c : F)
    (J : Finset (Fin 4)) (a : Fin 4 → Bool → F) :
    ((PMF.uniformOfFintype (PartialOffsets J a)).toOuterMeasure
      {o | ∀ i, OnLine (tuplePositionEquiv d hd σ o.1 i) (g,c)}).toReal ≤
      (Fintype.card F : ℝ)⁻¹ ^ (4 - (fixedPositions J).card) := by
  rw [PMF.toOuterMeasure_uniformOfFintype_apply, ENNReal.toReal_div]
  simp only [ENNReal.toReal_natCast]
  change (Fintype.card (AlignedPartialOffsets d hd σ g c J a) : ℝ) /
    (Fintype.card (PartialOffsets J a) : ℝ) ≤ _
  rw [card_partialOffsets, Nat.cast_pow]
  have hcard : (Fintype.card (AlignedPartialOffsets d hd σ g c J a) : ℝ) ≤
      (Fintype.card F : ℝ) ^ (freePositions J).card := by
    exact_mod_cast card_alignedPartialOffsets_le d hd σ g hg c J a
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    (Fintype.card (AlignedPartialOffsets d hd σ g c J a) : ℝ) /
        (Fintype.card F : ℝ) ^ (2 * (freshGenerators J).card) ≤
      (Fintype.card F : ℝ) ^ (freePositions J).card /
        (Fintype.card F : ℝ) ^ (2 * (freshGenerators J).card) :=
      div_le_div_of_nonneg_right hcard (by positivity)
    _ = _ := by
      rw [← alignment_exponent_identity J, pow_add, div_mul_eq_div_div,
        div_self (pow_ne_zero _ hq), one_div, inv_pow]

end Finite
end Balanced.PartialAlignment

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_ReuseWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open Finset

theorem repetition_mono {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) {s t : Finset α} (hst : s ⊆ t) :
    s.card - (s.image f).card ≤ t.card - (t.image f).card := by
  have himg : t.image f ⊆ s.image f ∪ (t \ s).image f := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    by_cases has : a ∈ s
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem f has)
    · exact Finset.mem_union_right _
        (Finset.mem_image_of_mem f (Finset.mem_sdiff.mpr ⟨ha, has⟩))
  have hcard := Finset.card_le_card himg
  have hunion := Finset.card_union_le (s.image f) ((t \ s).image f)
  have hdiff := Finset.card_sdiff_of_subset hst
  have hdiffimg := Finset.card_image_le (s := t \ s) (f := f)
  have hsimg := Finset.card_image_le (s := s) (f := f)
  have htimg := Finset.card_image_le (s := t) (f := f)
  have hstcard := Finset.card_le_card hst
  omega

theorem exists_small_repetition_witness {α β : Type*}
    [DecidableEq α] [DecidableEq β] (f : α → β) (s : Finset α) (k : ℕ)
    (hk : k ≤ s.card - (s.image f).card) :
    ∃ t ⊆ s, t.card ≤ 2 * k ∧ t.card - (t.image f).card = k := by
  obtain ⟨r, hrs, hinj, himage⟩ :=
    Finset.exists_subset_injOn_image_eq_of_surjOn (s : Set α) (s.image f)
      (show Set.SurjOn f (s : Set α) (s.image f) from by
        intro b hb
        exact Finset.mem_image.mp hb)
  have hrs' : r ⊆ s := hrs
  have hrcard : r.card = (s.image f).card := by
    rw [← himage, Finset.card_image_of_injOn hinj]
  have hk' : k ≤ (s \ r).card := by
    rw [Finset.card_sdiff_of_subset hrs', hrcard]
    exact hk
  obtain ⟨w, hw, hwcard⟩ := Finset.exists_subset_card_eq hk'
  have hws : w ⊆ s := fun a ha => (Finset.mem_sdiff.mp (hw ha)).1
  have hsurj : Set.SurjOn f (r : Set α) (w.image f) := by
    intro b hb
    have hbs : b ∈ s.image f := Finset.image_subset_image hws hb
    rw [← himage] at hbs
    exact Finset.mem_image.mp hbs
  obtain ⟨r', hr'r, hinj', himage'⟩ :=
    Finset.exists_subset_injOn_image_eq_of_surjOn (r : Set α) (w.image f) hsurj
  have hr'r' : r' ⊆ r := hr'r
  have hdisj : Disjoint w r' := by
    apply Finset.disjoint_left.mpr
    intro a haw har
    exact (Finset.mem_sdiff.mp (hw haw)).2 (hr'r' har)
  have hrcard' : r'.card = (w.image f).card := by
    rw [← himage', Finset.card_image_of_injOn hinj']
  have hbound : r'.card ≤ k := by
    rw [hrcard', ← hwcard]
    exact Finset.card_image_le
  refine ⟨w ∪ r', Finset.union_subset hws (hr'r'.trans hrs'), ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hdisj, hwcard]
    omega
  · rw [Finset.card_union_of_disjoint hdisj, Finset.image_union, himage',
      Finset.union_self, hwcard, hrcard']
    omega

theorem image_snd_sigma {ι α : Type*} [DecidableEq α]
    (s : Finset ι) (A : ι → Finset α) :
    (s.sigma A).image (fun x => x.2) = s.biUnion A := by
  ext a
  simp only [Finset.mem_image, Finset.mem_sigma, Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨i, x⟩, ⟨hi, hx⟩, rfl⟩
    exact ⟨i, hi, hx⟩
  · rintro ⟨i, hi, ha⟩
    exact ⟨⟨i, a⟩, ⟨hi, ha⟩, rfl⟩

theorem exists_small_family_reuse_witness {ι α : Type*}
    [DecidableEq ι] [DecidableEq α] (s : Finset ι) (A : ι → Finset α) (k : ℕ)
    (hk : k ≤ (∑ i ∈ s, (A i).card) - (s.biUnion A).card) :
    ∃ t ⊆ s, t.card ≤ 2 * k ∧
      k ≤ (∑ i ∈ t, (A i).card) - (t.biUnion A).card := by
  have hk' : k ≤ (s.sigma A).card -
      ((s.sigma A).image (fun x => x.2)).card := by
    simpa only [Finset.card_sigma, image_snd_sigma] using hk
  obtain ⟨w, hw, hwcard, hwreuse⟩ :=
    exists_small_repetition_witness (fun x : Sigma (fun _ : ι => α) => x.2)
      (s.sigma A) k hk'
  let t := w.image Sigma.fst
  have hts : t ⊆ s := by
    intro i hi
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
    exact (Finset.mem_sigma.mp (hw hx)).1
  have hwt : w ⊆ t.sigma A := by
    intro x hx
    exact Finset.mem_sigma.mpr
      ⟨Finset.mem_image_of_mem Sigma.fst hx, (Finset.mem_sigma.mp (hw hx)).2⟩
  refine ⟨t, hts, (Finset.card_image_le).trans hwcard, ?_⟩
  have hmono := repetition_mono (fun x : Sigma (fun _ : ι => α) => x.2) hwt
  rw [hwreuse, Finset.card_sigma, image_snd_sigma] at hmono
  exact hmono

theorem exists_six_tuple_reuse_witness {ι α : Type*}
    [DecidableEq ι] [DecidableEq α] (s : Finset ι) (A : ι → Finset α)
    (hfour : ∀ i ∈ s, (A i).card = 4)
    (hreuse : 3 ≤ 4 * s.card - (s.biUnion A).card) :
    ∃ t ⊆ s, t.card ≤ 6 ∧ 3 ≤ 4 * t.card - (t.biUnion A).card := by
  have hsum : (∑ i ∈ s, (A i).card) = 4 * s.card := by
    calc
      (∑ i ∈ s, (A i).card) = ∑ _i ∈ s, 4 :=
        Finset.sum_congr rfl hfour
      _ = 4 * s.card := by simp [Nat.mul_comm]
  obtain ⟨t, hts, htcard, htr⟩ :=
    exists_small_family_reuse_witness s A 3 (by simpa only [hsum] using hreuse)
  refine ⟨t, hts, htcard, ?_⟩
  have hsumt : (∑ i ∈ t, (A i).card) = 4 * t.card := by
    calc
      (∑ i ∈ t, (A i).card) = ∑ _i ∈ t, 4 :=
        Finset.sum_congr rfl (fun i hi => hfour i (hts hi))
      _ = 4 * t.card := by simp [Nat.mul_comm]
  simpa only [hsumt] using htr

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_ReuseOrdering
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open Finset

theorem reuseSaving_eq_of_le_two {j : ℕ} (hj : j ≤ 2) : reuseSaving j = j := by
  simp [reuseSaving, hj]

theorem reuseSaving_pos {j : ℕ} (hj : 0 < j) : 1 ≤ reuseSaving j := by
  unfold reuseSaving
  split_ifs <;> omega

theorem reuseExposureScore_eq_reuse_of_small {ι α : Type*}
    [DecidableEq ι] [DecidableEq α] (A : ι → Finset α) (l : List ι)
    (hnd : l.Nodup)
    (hsmall : ∀ i ∈ l, (A i ∩ (l.toFinset.erase i).biUnion A).card ≤ 2) :
    reuseExposureScore A l =
      (∑ i ∈ l.toFinset, (A i).card) - (l.toFinset.biUnion A).card := by
  induction l with
  | nil => simp [reuseExposureScore]
  | cons i l ih =>
    have hni : i ∉ l := (List.nodup_cons.mp hnd).1
    have hnl : l.Nodup := (List.nodup_cons.mp hnd).2
    have hint : (A i ∩ l.toFinset.biUnion A).card ≤ 2 := by
      simpa [List.toFinset_cons, hni] using hsmall i (by simp)
    have hsmalltail : ∀ j ∈ l,
        (A j ∩ (l.toFinset.erase j).biUnion A).card ≤ 2 := by
      intro j hj
      apply le_trans (Finset.card_le_card ?_) (hsmall j (by simp [hj]))
      apply Finset.inter_subset_inter_left
      apply Finset.biUnion_subset_biUnion_of_subset_left
      exact Finset.erase_subset_erase _ (by simp : l.toFinset ⊆ (i :: l).toFinset)
    rw [reuseExposureScore, reuseSaving_eq_of_le_two hint, ih hnl hsmalltail,
      List.toFinset_cons, family_reuse_insert A l.toFinset i (by simpa using hni)]

theorem reuseExposureScore_cons_ge_one {ι α : Type*}
    [DecidableEq ι] [DecidableEq α] (A : ι → Finset α) (i : ι) (l : List ι)
    (j : ι) (hj : j ∈ l) (hoverlap : (A i ∩ A j).Nonempty) :
    reuseExposureScore A l + 1 ≤ reuseExposureScore A (i :: l) := by
  have hpos : 0 < (A i ∩ l.toFinset.biUnion A).card := by
    apply Finset.card_pos.mpr
    obtain ⟨a, ha⟩ := hoverlap
    obtain ⟨hai, haj⟩ := Finset.mem_inter.mp ha
    exact ⟨a, Finset.mem_inter.mpr
      ⟨hai, Finset.mem_biUnion.mpr ⟨j, by simpa using hj, haj⟩⟩⟩
  exact Nat.add_le_add_left (reuseSaving_pos hpos) _

theorem exists_three_reuse_neighbors {ι α : Type*}
    [DecidableEq ι] [DecidableEq α] (A : ι → Finset α) (s : Finset ι)
    (hcompat : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (A i ∩ A j).card ≤ 1)
    (i : ι) (hi : i ∈ s)
    (hlarge : 3 ≤ (A i ∩ (s.erase i).biUnion A).card) :
    ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s,
      a ≠ i ∧ b ≠ i ∧ c ≠ i ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      (A a ∩ A i).Nonempty ∧ (A b ∩ A i).Nonempty ∧ (A c ∩ A i).Nonempty := by
  let n := (s.erase i).filter fun j => (A i ∩ A j).Nonempty
  have hni : ∀ j ∈ n, j ∈ s ∧ j ≠ i ∧ (A j ∩ A i).Nonempty := by
    intro j hj
    obtain ⟨hj, hov⟩ := Finset.mem_filter.mp hj
    obtain ⟨hne, hjs⟩ := Finset.mem_erase.mp hj
    exact ⟨hjs, hne, by simpa [Finset.inter_comm] using hov⟩
  have heq : A i ∩ (s.erase i).biUnion A =
      n.biUnion (fun j => A i ∩ A j) := by
    ext a
    simp only [Finset.mem_inter, Finset.mem_biUnion]
    constructor
    · rintro ⟨hai, j, hj, haj⟩
      exact ⟨j, Finset.mem_filter.mpr ⟨hj, ⟨a, Finset.mem_inter.mpr ⟨hai, haj⟩⟩⟩, hai, haj⟩
    · rintro ⟨j, hj, hai, haj⟩
      exact ⟨hai, j, (Finset.mem_filter.mp hj).1, haj⟩
  have hncard : 3 ≤ n.card := by
    calc
      3 ≤ (A i ∩ (s.erase i).biUnion A).card := hlarge
      _ = (n.biUnion (fun j => A i ∩ A j)).card := congrArg Finset.card heq
      _ ≤ ∑ j ∈ n, (A i ∩ A j).card := Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ n, 1 := Finset.sum_le_sum (fun j hj =>
        hcompat i hi j (hni j hj).1 (Ne.symm (hni j hj).2.1))
      _ = n.card := by simp
  obtain ⟨w, hwn, hwcard⟩ := Finset.exists_subset_card_eq hncard
  obtain ⟨a, b, c, hab, hac, hbc, hw⟩ := Finset.card_eq_three.mp hwcard
  have ha := hni a (hwn (by simp [hw]))
  have hb := hni b (hwn (by simp [hw]))
  have hc := hni c (hwn (by simp [hw]))
  exact ⟨a, ha.1, b, hb.1, c, hc.1, ha.2.1, hb.2.1, hc.2.1,
    hab, hac, hbc, ha.2.2, hb.2.2, hc.2.2⟩

theorem exists_star_reuse_order {ι α : Type*}
    [DecidableEq ι] [DecidableEq α] (A : ι → Finset α) (s : Finset ι)
    (hcompat : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (A i ∩ A j).card ≤ 1)
    (i : ι) (hi : i ∈ s)
    (hlarge : 3 ≤ (A i ∩ (s.erase i).biUnion A).card) :
    ∃ l : List ι, l.Nodup ∧ l.toFinset ⊆ s ∧ l.length = 4 ∧
      3 ≤ reuseExposureScore A l := by
  obtain ⟨a, ha, b, hb, c, hc, hai, hbi, hci, hab, hac, hbc, hai', hbi', hci'⟩ :=
    exists_three_reuse_neighbors A s hcompat i hi hlarge
  refine ⟨[c, b, a, i], ?_, ?_, rfl, ?_⟩
  · simp [hai, hbi, hci, Ne.symm hab, Ne.symm hac, Ne.symm hbc]
  · intro j hj
    simp only [List.toFinset_cons, List.toFinset_nil, Finset.mem_insert,
      Finset.notMem_empty, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl
    · exact hc
    · exact hb
    · exact ha
    · exact hi
  · have h₁ := reuseExposureScore_cons_ge_one A a [i] i (by simp) hai'
    have h₂ := reuseExposureScore_cons_ge_one A b [a, i] i (by simp) hbi'
    have h₃ := reuseExposureScore_cons_ge_one A c [b, a, i] i (by simp) hci'
    omega

theorem exists_six_tuple_reuse_order {ι α : Type*}
    [DecidableEq ι] [DecidableEq α] (A : ι → Finset α) (s : Finset ι)
    (hfour : ∀ i ∈ s, (A i).card = 4)
    (hcompat : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (A i ∩ A j).card ≤ 1)
    (hreuse : 3 ≤ 4 * s.card - (s.biUnion A).card) :
    ∃ l : List ι, l.Nodup ∧ l.toFinset ⊆ s ∧ l.length ≤ 6 ∧
      3 ≤ reuseExposureScore A l := by
  obtain ⟨t, hts, htcard, htr⟩ := exists_six_tuple_reuse_witness s A hfour hreuse
  by_cases hlarge : ∃ i ∈ t, 3 ≤ (A i ∩ (t.erase i).biUnion A).card
  · obtain ⟨i, hi, hlarge⟩ := hlarge
    obtain ⟨l, hnd, hlt, hlen, hscore⟩ := exists_star_reuse_order A t
      (fun a ha b hb hne => hcompat a (hts ha) b (hts hb) hne) i hi hlarge
    exact ⟨l, hnd, hlt.trans hts, by omega, hscore⟩
  · have hsmall : ∀ i ∈ t, (A i ∩ (t.erase i).biUnion A).card ≤ 2 := by
      intro i hi
      have hn : ¬ 3 ≤ (A i ∩ (t.erase i).biUnion A).card :=
        fun h => hlarge ⟨i, hi, h⟩
      omega
    refine ⟨t.toList, t.nodup_toList, by simpa using hts, by simpa using htcard, ?_⟩
    rw [reuseExposureScore_eq_reuse_of_small A t.toList t.nodup_toList
      (by simpa using hsmall)]
    have hsum : (∑ i ∈ t, (A i).card) = 4 * t.card := by
      calc
        (∑ i ∈ t, (A i).card) = ∑ _i ∈ t, 4 :=
          Finset.sum_congr rfl (fun i hi => hfour i (hts hi))
        _ = 4 * t.card := by simp [Nat.mul_comm]
    simpa only [Finset.toList_toFinset, hsum] using htr

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_ReuseExtensionArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

theorem reuse_extension_exponent_le : ∀ old : Finset (Fin 4),
    (4 - (old.card : ℤ)) +
        (if (fixedGeneratorPositions old).card = 0 then (1 : ℤ) else 0) -
        (4 - ((fixedGeneratorPositions old).card : ℤ)) - 1 ≤
      -(reuseSaving old.card : ℤ) := by
  decide

theorem reuse_extension_scale_le (q : ℝ) (hq : 1 ≤ q) (old : Finset (Fin 4)) :
    q ^ (4 - old.card) *
        (if (fixedGeneratorPositions old).card = 0 then q else 1) /
        q ^ (4 - (fixedGeneratorPositions old).card) / q ≤
      1 / q ^ reuseSaving old.card := by
  have hq0 : q ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hq)
  have hj : old.card ≤ 4 := by simpa using Finset.card_le_univ old
  have hf : (fixedGeneratorPositions old).card ≤ 4 := by
    simpa using Finset.card_le_univ (fixedGeneratorPositions old)
  have hjcast : (4 : ℤ) - (old.card : ℤ) = ((4 - old.card : ℕ) : ℤ) :=
    (Int.ofNat_sub hj).symm
  have hfcast : (4 : ℤ) - ((fixedGeneratorPositions old).card : ℤ) =
      ((4 - (fixedGeneratorPositions old).card : ℕ) : ℤ) :=
    (Int.ofNat_sub hf).symm
  calc
    q ^ (4 - old.card) *
        (if (fixedGeneratorPositions old).card = 0 then q else 1) /
        q ^ (4 - (fixedGeneratorPositions old).card) / q =
      q ^ ((4 - (old.card : ℤ)) +
        (if (fixedGeneratorPositions old).card = 0 then (1 : ℤ) else 0) -
        (4 - ((fixedGeneratorPositions old).card : ℤ)) - 1) := by
      rw [hjcast, hfcast, zpow_sub₀ hq0, zpow_sub₀ hq0, zpow_add₀ hq0]
      simp only [zpow_natCast, zpow_one]
      split_ifs <;> simp
    _ ≤ q ^ (-(reuseSaving old.card : ℤ)) :=
      zpow_le_zpow_right₀ hq (reuse_extension_exponent_le old)
    _ = 1 / q ^ reuseSaving old.card := by
      simp [zpow_neg, div_eq_mul_inv]

theorem reuse_extension_scale_mul_le (q K : ℝ) (hq : 1 ≤ q) (hK : 0 ≤ K)
    (old : Finset (Fin 4)) :
    K * (q ^ (4 - old.card) *
        (if (fixedGeneratorPositions old).card = 0 then q else 1) /
        q ^ (4 - (fixedGeneratorPositions old).card) / q) ≤
      K / q ^ reuseSaving old.card := by
  have h := mul_le_mul_of_nonneg_left (reuse_extension_scale_le q hq old) hK
  simpa only [mul_one_div] using h

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_TupleExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] [Fintype F] in
theorem image_oldGeneratorIndices (T : FourTuple F) (old : Finset (Direction F)) :
    (oldGeneratorIndices T old).image T.generator = generatorSet T ∩ old := by
  ext d
  simp only [oldGeneratorIndices, generatorSet, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_inter]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, rfl⟩, hi⟩
  · rintro ⟨⟨i, rfl⟩, hi⟩
    exact ⟨i, hi, rfl⟩

omit [Field F] [Fintype F] in
theorem card_oldGeneratorIndices (T : FourTuple F) (old : Finset (Direction F))
    (hT : Function.Injective T.generator) :
    (oldGeneratorIndices T old).card = (generatorSet T ∩ old).card := by
  rw [← image_oldGeneratorIndices, Finset.card_image_of_injective _ hT]

theorem Configuration.exists_six_tuple_reuse_order (C : Configuration F)
    (hvalid : C.Valid) (hcompatible : C.Compatible) (s : Finset (Slot F))
    (hreuse : 3 ≤ 4 * s.card -
      (s.biUnion (fun i => generatorSet (C.choice i).tuple)).card) :
    ∃ l : List (Slot F), l.Nodup ∧ l.toFinset ⊆ s ∧ l.length ≤ 6 ∧
      3 ≤ reuseExposureScore (fun i => generatorSet (C.choice i).tuple) l := by
  apply Balanced.exists_six_tuple_reuse_order _ s ?_ ?_ hreuse
  · intro i _hi
    rw [generatorSet, Finset.card_image_of_injective _ (hvalid.2 i).2.2.1]
    simp
  · intro i _hi j _hj hij
    exact hcompatible.2.1 i j hij

end
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_ReuseTargetSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.PartialAlignment
open TupleAlignment

noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem externalAlignmentProbability_le (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (p : Point F) (g : Direction F) (hg : ∀ i, d i ≠ g)
    (J : Finset (Fin 4)) (a : Fin 4 → Bool → F) :
    externalAlignmentProbability d hd σ p g J a ≤
      (Fintype.card F : ℝ)⁻¹ ^ (4 - (fixedPositions J).card) := by
  apply le_trans ?_ (partial_alignment_probability_le d hd σ g hg (lineEval g p) J a)
  unfold externalAlignmentProbability
  rw [PMF.toOuterMeasure_uniformOfFintype_apply,
    PMF.toOuterMeasure_uniformOfFintype_apply, ENNReal.toReal_div, ENNReal.toReal_div]
  simp only [ENNReal.toReal_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Fintype.card_le_of_injective
    (fun o : externalAlignmentEvent d hd σ p g J a =>
      (⟨o.1, o.2.1⟩ : AlignedPartialOffsets d hd σ g (lineEval g p) J a))
    (by
      intro o r h
      apply Subtype.ext
      exact congrArg (fun z : AlignedPartialOffsets d hd σ g (lineEval g p) J a => z.1) h)

omit [Fintype F] [DecidableEq F] in
theorem tuplePosition_fixed (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (J : Finset (Fin 4)) (a : Fin 4 → Bool → F)
    (o : PartialOffsets J a) (i : Fin 4) (hi : i ∈ fixedPositions J) :
    tuplePositionEquiv d hd σ o.1 i = tuplePositionEquiv d hd σ a i := by
  obtain ⟨_, hi, hnext⟩ := Finset.mem_filter.mp hi
  simp only [tuplePositionEquiv_apply, o.2 i hi, o.2 (i + 1) hnext]

theorem card_possibleExternalTargets_le_one (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (p : Point F) (J : Finset (Fin 4)) (a : Fin 4 → Bool → F)
    (hfixed : (fixedPositions J).Nonempty) :
    (possibleExternalTargets d hd σ p J a).card ≤ 1 := by
  obtain ⟨i, hi⟩ := hfixed
  apply Finset.card_le_one.mpr
  intro g hg h hh
  obtain ⟨o, ho⟩ := (Finset.mem_filter.mp hg).2
  obtain ⟨r, hr⟩ := (Finset.mem_filter.mp hh).2
  have haway := ho.2 i
  have hon := ho.1 i
  have hother := hr.1 i
  rw [tuplePosition_fixed d hd σ J a o i hi] at haway hon
  rw [tuplePosition_fixed d hd σ J a r i hi] at hother
  exact direction_eq_of_common_point p _ haway.symm g h hon hother

theorem externalAlignmentProbability_eq_zero_of_not_possible
    (d : Fin 4 → Direction F) (hd : ∀ i, d i ≠ d (i + 1))
    (σ : Fin 4 → Bool) (p : Point F) (g : Direction F)
    (J : Finset (Fin 4)) (a : Fin 4 → Bool → F)
    (hg : g ∉ possibleExternalTargets d hd σ p J a) :
    externalAlignmentProbability d hd σ p g J a = 0 := by
  have hempty : externalAlignmentEvent d hd σ p g J a = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro o ho
    exact hg (Finset.mem_filter.mpr ⟨Finset.mem_univ _, o, ho⟩)
  simp [externalAlignmentProbability, hempty]

theorem sum_externalAlignmentProbability_le
    (d : Fin 4 → Direction F) (hd : ∀ i, d i ≠ d (i + 1))
    (σ : Fin 4 → Bool) (p : Point F) (J : Finset (Fin 4))
    (a : Fin 4 → Bool → F) :
    (∑ g ∈ (Finset.univ.filter (fun g : Direction F => ∀ i, d i ≠ g)),
      externalAlignmentProbability d hd σ p g J a) ≤
      (if (fixedPositions J).card = 0 then (Fintype.card F : ℝ) + 1 else 1) *
        ((Fintype.card F : ℝ)⁻¹ ^ (4 - (fixedPositions J).card)) := by
  let eligible := Finset.univ.filter (fun g : Direction F => ∀ i, d i ≠ g)
  let possible := possibleExternalTargets d hd σ p J a
  have hsum : (∑ g ∈ eligible ∩ possible, externalAlignmentProbability d hd σ p g J a) =
      ∑ g ∈ eligible, externalAlignmentProbability d hd σ p g J a := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro g hg hnot
    apply externalAlignmentProbability_eq_zero_of_not_possible
    intro hp
    exact hnot (Finset.mem_inter.mpr ⟨hg, hp⟩)
  rw [← hsum]
  calc
    (∑ g ∈ eligible ∩ possible, externalAlignmentProbability d hd σ p g J a) ≤
        ((eligible ∩ possible).card : ℝ) *
          ((Fintype.card F : ℝ)⁻¹ ^ (4 - (fixedPositions J).card)) := by
      simpa only [nsmul_eq_mul] using Finset.sum_le_card_nsmul (eligible ∩ possible)
        (fun g => externalAlignmentProbability d hd σ p g J a) _
        (fun g hg => externalAlignmentProbability_le d hd σ p g
          (Finset.mem_filter.mp (Finset.mem_inter.mp hg).1).2 J a)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      split_ifs with hzero
      · have hc := Finset.card_le_univ (eligible ∩ possible)
        simpa only [Direction, Fintype.card_option, Nat.cast_add, Nat.cast_one] using
          (Nat.cast_le.mpr hc : ((eligible ∩ possible).card : ℝ) ≤ _)
      · have hc := (Finset.card_le_card (Finset.inter_subset_right :
            eligible ∩ possible ⊆ possible)).trans
          (card_possibleExternalTargets_le_one d hd σ p J a
            (Finset.card_pos.mp (Nat.pos_of_ne_zero hzero)))
        exact_mod_cast hc

theorem fixedPositions_eq_fixedGeneratorPositions (J : Finset (Fin 4)) :
    fixedPositions J = fixedGeneratorPositions J := by
  ext i
  simp [fixedPositions, fixedGeneratorPositions]

theorem scaled_sum_externalAlignmentProbability_le
    (d : Fin 4 → Direction F) (hd : ∀ i, d i ≠ d (i + 1))
    (σ : Fin 4 → Bool) (p : Point F) (J : Finset (Fin 4))
    (a : Fin 4 → Bool → F) (K : ℝ) (hK : 0 ≤ K) :
    (Fintype.card F : ℝ) ^ (4 - J.card) *
      (∑ g ∈ (Finset.univ.filter (fun g : Direction F => ∀ i, d i ≠ g)),
        externalAlignmentProbability d hd σ p g J a) * (K / Fintype.card F) ≤
      2 * K / (Fintype.card F : ℝ) ^ reuseSaving J.card := by
  let q : ℝ := Fintype.card F
  have hq : 1 ≤ q := by
    change (1 : ℝ) ≤ (Fintype.card F : ℝ)
    exact_mod_cast (show 1 ≤ Fintype.card F from Fintype.card_pos)
  have hsum := sum_externalAlignmentProbability_le d hd σ p J a
  rw [fixedPositions_eq_fixedGeneratorPositions] at hsum
  have htarget :
      (if (fixedGeneratorPositions J).card = 0 then q + 1 else 1) ≤
        2 * (if (fixedGeneratorPositions J).card = 0 then q else 1) := by
    split_ifs <;> linarith
  calc
    q ^ (4 - J.card) *
        (∑ g ∈ (Finset.univ.filter (fun g : Direction F => ∀ i, d i ≠ g)),
          externalAlignmentProbability d hd σ p g J a) * (K / q) ≤
      q ^ (4 - J.card) *
        ((if (fixedGeneratorPositions J).card = 0 then q + 1 else 1) *
          (q⁻¹ ^ (4 - (fixedGeneratorPositions J).card))) * (K / q) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ q ^ (4 - J.card) *
        (2 * (if (fixedGeneratorPositions J).card = 0 then q else 1) *
          (q⁻¹ ^ (4 - (fixedGeneratorPositions J).card))) * (K / q) := by
      gcongr
    _ = (2 * K) * (q ^ (4 - J.card) *
        (if (fixedGeneratorPositions J).card = 0 then q else 1) /
        q ^ (4 - (fixedGeneratorPositions J).card) / q) := by
      simp only [inv_pow, div_eq_mul_inv]
      ring
    _ ≤ 2 * K / q ^ reuseSaving J.card :=
      reuse_extension_scale_mul_le q (2 * K) hq (by positivity) J

end
end Balanced.PartialAlignment

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_GeneratorEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open Finset

section FiniteLabels
variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
theorem card_restrictedGeneratorLabels (old : Finset α) (mask : Finset (Fin 4)) :
    (restrictedGeneratorLabels old mask).card =
      old.card ^ mask.card * Fintype.card α ^ (4 - mask.card) := by
  rw [restrictedGeneratorLabels, Fintype.card_piFinset]
  simp only [apply_ite Finset.card, Finset.card_univ]
  rw [Finset.prod_ite]
  have hcomp : ((Finset.univ : Finset (Fin 4)) \ mask).card = 4 - mask.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp
  simp [← Finset.sdiff_eq_filter, hcomp]

theorem generatorLabelsWithOldCount_subset (old : Finset α) (j : ℕ) :
    generatorLabelsWithOldCount old j ⊆
      (Finset.univ.powersetCard j).biUnion (restrictedGeneratorLabels old) := by
  intro g hg
  let mask : Finset (Fin 4) := Finset.univ.filter (fun i => g i ∈ old)
  have hmask : mask.card = j := (Finset.mem_filter.mp hg).2
  refine Finset.mem_biUnion.mpr ⟨mask,
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hmask⟩, ?_⟩
  apply Fintype.mem_piFinset.mpr
  intro i
  by_cases hi : i ∈ mask
  · simpa only [ite_eq_left hi] using (Finset.mem_filter.mp hi).2
  · simp [hi]

theorem card_generatorLabelsWithOldCount_le (old : Finset α) (j : ℕ) :
    (generatorLabelsWithOldCount old j).card ≤
      Nat.choose 4 j * old.card ^ j * Fintype.card α ^ (4 - j) := by
  calc
    (generatorLabelsWithOldCount old j).card ≤
        ((Finset.univ.powersetCard j).biUnion (restrictedGeneratorLabels old)).card :=
      Finset.card_le_card (generatorLabelsWithOldCount_subset old j)
    _ ≤ ∑ mask ∈ Finset.univ.powersetCard j, (restrictedGeneratorLabels old mask).card :=
      Finset.card_biUnion_le
    _ = ∑ _mask ∈ (Finset.univ : Finset (Fin 4)).powersetCard j,
        old.card ^ j * Fintype.card α ^ (4 - j) := by
      apply Finset.sum_congr rfl
      intro mask hmask
      rw [card_restrictedGeneratorLabels, (Finset.mem_powersetCard.mp hmask).2]
    _ = Nat.choose 4 j * old.card ^ j * Fintype.card α ^ (4 - j) := by
      simp [Nat.mul_assoc]

theorem card_tupleCodesWithOldCount_le (old : Finset α) (j : ℕ) :
    (tupleCodesWithOldCount old j).card ≤
      16 * (Nat.choose 4 j * old.card ^ j * Fintype.card α ^ (4 - j)) := by
  rw [tupleCodesWithOldCount, Finset.product_eq_sprod, Finset.card_product, Finset.card_univ]
  have hbits : Fintype.card (Fin 4 → Bool) = 16 := by decide
  rw [hbits, Nat.mul_comm]
  exact Nat.mul_le_mul_left 16 (card_generatorLabelsWithOldCount_le old j)

theorem card_tupleCodesWithOldCount_le_uniform (old : Finset α) (j : ℕ)
    (hold : old.card ≤ 24) (hj : j ≤ 4) :
    (tupleCodesWithOldCount old j).card ≤
      (256 * 24 ^ 4) * Fintype.card α ^ (4 - j) := by
  have hchoose : Nat.choose 4 j ≤ 16 := by
    interval_cases j <;> decide
  have hpow : old.card ^ j ≤ 24 ^ 4 := by
    calc
      old.card ^ j ≤ 24 ^ j := Nat.pow_le_pow_left hold j
      _ ≤ 24 ^ 4 := Nat.pow_le_pow_right (by omega) hj
  calc
    (tupleCodesWithOldCount old j).card ≤
        16 * (Nat.choose 4 j * old.card ^ j * Fintype.card α ^ (4 - j)) :=
      card_tupleCodesWithOldCount_le old j
    _ ≤ 16 * (16 * 24 ^ 4 * Fintype.card α ^ (4 - j)) := by gcongr
    _ = (256 * 24 ^ 4) * Fintype.card α ^ (4 - j) := by ring

end FiniteLabels

theorem card_tupleCodesWithOldCount_le_field {F : Type*} [Fintype F]
    [Nonempty F] [DecidableEq F] (old : Finset (Direction F)) (j : ℕ)
    (hold : old.card ≤ 24) (hj : j ≤ 4) :
    (tupleCodesWithOldCount old j).card ≤
      (4096 * 24 ^ 4) * Fintype.card F ^ (4 - j) := by
  have hq : 0 < Fintype.card F := Fintype.card_pos
  have hdir : Fintype.card (Direction F) ≤ 2 * Fintype.card F := by
    simp only [Direction, Fintype.card_option]
    omega
  have htwo : 2 ^ (4 - j) ≤ 16 := by
    calc
      2 ^ (4 - j) ≤ 2 ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
      _ = 16 := rfl
  calc
    (tupleCodesWithOldCount old j).card ≤
        (256 * 24 ^ 4) * Fintype.card (Direction F) ^ (4 - j) :=
      card_tupleCodesWithOldCount_le_uniform old j hold hj
    _ ≤ (256 * 24 ^ 4) * (2 * Fintype.card F) ^ (4 - j) := by gcongr
    _ = (256 * 24 ^ 4) * (2 ^ (4 - j) * Fintype.card F ^ (4 - j)) := by rw [Nat.mul_pow]
    _ ≤ (256 * 24 ^ 4) * (16 * Fintype.card F ^ (4 - j)) := by gcongr
    _ = (4096 * 24 ^ 4) * Fintype.card F ^ (4 - j) := by ring

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_ReuseExtensionSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced
open PartialAlignment

noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem tupleCodeTargetMass_scaled_le (old : Finset (Direction F))
    (M : MergedPairs F) (p : Point F)
    (c : (Fin 4 → Direction F) × (Fin 4 → Bool)) (j : ℕ)
    (hc : c ∈ tupleCodesWithOldCount old j) (K : ℝ) (hK : 0 ≤ K) :
    (Fintype.card F : ℝ) ^ (4 - j) * tupleCodeTargetMass old M p c *
      (K / Fintype.card F) ≤ 2 * K / (Fintype.card F : ℝ) ^ reuseSaving j := by
  obtain ⟨hgen, _⟩ := Finset.mem_product.mp hc
  have hJ : (oldGeneratorIndices (⟨c.1, c.2⟩ : FourTuple F) old).card = j :=
    (Finset.mem_filter.mp hgen).2
  unfold tupleCodeTargetMass
  split_ifs with hinj
  · simpa only [hJ] using scaled_sum_externalAlignmentProbability_le c.1
      (fun i h => cyclic_index_ne_next i (hinj h)) c.2 p
      (oldGeneratorIndices ⟨c.1, c.2⟩ old) (fun i => M (c.1 i)) K hK
  · simp only [mul_zero, zero_mul]
    positivity

theorem sum_tupleCodeTargetMass_extension_le (old : Finset (Direction F))
    (M : MergedPairs F) (p : Point F) (j : ℕ)
    (hold : old.card ≤ 24) (hj : j ≤ 4) (K : ℝ) (hK : 0 ≤ K) :
    2 * (∑ c ∈ tupleCodesWithOldCount old j,
      tupleCodeTargetMass old M p c * (K / Fintype.card F)) ≤
      (4 * (4096 * 24 ^ 4) : ℝ) * K /
        (Fintype.card F : ℝ) ^ reuseSaving j := by
  let q : ℝ := Fintype.card F
  have hq : 0 < q := by
    change (0 : ℝ) < (Fintype.card F : ℝ)
    exact_mod_cast Fintype.card_pos (α := F)
  have hqpow : 0 < q ^ (4 - j) := pow_pos hq _
  have hcount : ((tupleCodesWithOldCount old j).card : ℝ) ≤
      (4096 * 24 ^ 4 : ℝ) * q ^ (4 - j) := by
    dsimp [q]
    exact_mod_cast card_tupleCodesWithOldCount_le_field old j hold hj
  have hscaled :
      q ^ (4 - j) * (∑ c ∈ tupleCodesWithOldCount old j,
        tupleCodeTargetMass old M p c * (K / q)) ≤
        (4096 * 24 ^ 4 : ℝ) * q ^ (4 - j) * (2 * K / q ^ reuseSaving j) := by
    calc
      q ^ (4 - j) * (∑ c ∈ tupleCodesWithOldCount old j,
          tupleCodeTargetMass old M p c * (K / q)) =
        ∑ c ∈ tupleCodesWithOldCount old j,
          q ^ (4 - j) * tupleCodeTargetMass old M p c * (K / q) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c _
        ring
      _ ≤ ∑ _c ∈ tupleCodesWithOldCount old j, 2 * K / q ^ reuseSaving j := by
        apply Finset.sum_le_sum
        intro c hc
        exact tupleCodeTargetMass_scaled_le old M p c j hc K hK
      _ = ((tupleCodesWithOldCount old j).card : ℝ) * (2 * K / q ^ reuseSaving j) := by
        simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcount (by positivity)
  have hsingle :
      (∑ c ∈ tupleCodesWithOldCount old j,
        tupleCodeTargetMass old M p c * (K / q)) ≤
        (4096 * 24 ^ 4 : ℝ) * (2 * K / q ^ reuseSaving j) := by
    apply (mul_le_mul_iff_right₀ hqpow).mp
    nlinarith [hscaled]
  change 2 * (∑ c ∈ tupleCodesWithOldCount old j,
    tupleCodeTargetMass old M p c * (K / q)) ≤ _
  calc
    _ ≤ 2 * ((4096 * 24 ^ 4 : ℝ) * (2 * K / q ^ reuseSaving j)) := by
      gcongr
    _ = _ := by ring

end
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_ReuseGlobalExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced
open PartialAlignment TupleAlignment

noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem global_external_alignment_probability_eq (T : FourTuple F)
    (hT : Function.Injective T.generator) (p : Point F) (g : Direction F)
    (old : Finset (Direction F)) (a : MergedPairs F) :
    (((offsetLaw F).filter {M | ∀ d, d ∈ old → M d = a d}
      (canonical_exposure_supported old a)).toOuterMeasure
      {M | (∀ i, OnLine (tuplePoint M T i) (lineThrough g p)) ∧
        ∀ i, tuplePoint M T i ≠ p}).toReal =
      externalAlignmentProbability T.generator (adjacent_ne_of_injective T hT)
        T.side p g (oldGeneratorIndices T old) (fun i => a (T.generator i)) := by
  let hd := adjacent_ne_of_injective T hT
  let E : Set (Fin 4 → Bool → F) :=
    {o | (∀ i, OnLine (tuplePositionEquiv T.generator hd T.side o i) (lineThrough g p)) ∧
      ∀ i, tuplePositionEquiv T.generator hd T.side o i ≠ p}
  have h := congrArg (fun law => (law.toOuterMeasure E).toReal)
    (global_exposed_tuple_law T hT old a)
  have hJ : exposedTupleIndices T old = oldGeneratorIndices T old := by
    ext i
    simp [exposedTupleIndices, oldGeneratorIndices]
  rw [hJ] at h
  rw [partialOffsets_conditional_law, PMF.toOuterMeasure_map_apply,
    PMF.toOuterMeasure_map_apply] at h
  simp only [E, Set.preimage_ofPred_eq, tuplePositionEquiv_apply] at h
  simp only [offsetLaw_eq_uniform, externalAlignmentProbability,
    externalAlignmentEvent, tuplePositionEquiv_apply, tuplePoint, constituent]
  exact h

theorem globalTupleCodeTargetMass_eq (old : Finset (Direction F))
    (a : MergedPairs F) (p : Point F)
    (c : (Fin 4 → Direction F) × (Fin 4 → Bool)) :
    globalTupleCodeTargetMass old a p c = tupleCodeTargetMass old a p c := by
  unfold globalTupleCodeTargetMass tupleCodeTargetMass
  split_ifs with hinj
  · apply Finset.sum_congr rfl
    intro g _
    exact global_external_alignment_probability_eq ⟨c.1, c.2⟩ hinj p g old a
  · rfl

theorem sum_globalTupleCodeTargetMass_extension_le (old : Finset (Direction F))
    (a : MergedPairs F) (p : Point F) (j : ℕ)
    (hold : old.card ≤ 24) (hj : j ≤ 4) (K : ℝ) (hK : 0 ≤ K) :
    2 * (∑ c ∈ tupleCodesWithOldCount old j,
      globalTupleCodeTargetMass old a p c * (K / Fintype.card F)) ≤
      (4 * (4096 * 24 ^ 4) : ℝ) * K /
        (Fintype.card F : ℝ) ^ reuseSaving j := by
  simp_rw [globalTupleCodeTargetMass_eq]
  exact sum_tupleCodeTargetMass_extension_le old a p j hold hj K hK

end
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_ReuseConditionalSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ReuseConditional

open PartialAlignment
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] [DecidableEq F] in
private theorem sum_slot_tuple (f : Local.TupleCode F → Direction F → ℝ) :
    (∑ r : Slot F × Local.TupleCode F, f r.2 r.1.1) =
      2 * ∑ c : Local.TupleCode F, ∑ g : Direction F, f c g := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Slot, Fintype.sum_prod_type, Fintype.sum_bool, ← two_mul]
  simp only [← Finset.mul_sum]

theorem full_code_extension_le (old : Finset (Direction F)) (a : MergedPairs F)
    (p : Point F) (j : ℕ) (hold : old.card ≤ 24) (hj : j ≤ 4)
    (K : ℝ) (hK : 0 ≤ K) :
    (∑ r : Slot F × Local.TupleCode F,
      if Function.Injective r.2.1 ∧ (∀ i, r.2.1 i ≠ r.1.1) ∧
          (oldGeneratorIndices (Local.decodeTuple r.2) old).card = j then
        (((offsetLaw F).filter {M | ∀ d, d ∈ old → M d = a d}
          (canonical_exposure_supported old a)).toOuterMeasure
          {M | (∀ i, OnLine (tuplePoint M (Local.decodeTuple r.2) i)
            (lineThrough r.1.1 p)) ∧
            ∀ i, tuplePoint M (Local.decodeTuple r.2) i ≠ p}).toReal *
          (K / Fintype.card F)
      else 0) ≤
      (4 * (4096 * 24 ^ 4) : ℝ) * K /
        (Fintype.card F : ℝ) ^ reuseSaving j := by
  let mass : Local.TupleCode F → Direction F → ℝ := fun c g =>
    (((offsetLaw F).filter {M | ∀ d, d ∈ old → M d = a d}
      (canonical_exposure_supported old a)).toOuterMeasure
      {M | (∀ i, OnLine (tuplePoint M (Local.decodeTuple c) i) (lineThrough g p)) ∧
        ∀ i, tuplePoint M (Local.decodeTuple c) i ≠ p}).toReal
  have heq :
      (∑ r : Slot F × Local.TupleCode F,
        if Function.Injective r.2.1 ∧ (∀ i, r.2.1 i ≠ r.1.1) ∧
            (oldGeneratorIndices (Local.decodeTuple r.2) old).card = j then
          mass r.2 r.1.1 * (K / Fintype.card F) else 0) =
      2 * ∑ c ∈ tupleCodesWithOldCount old j,
        globalTupleCodeTargetMass old a p c * (K / Fintype.card F) := by
    rw [sum_slot_tuple (fun c g =>
      if Function.Injective c.1 ∧ (∀ i, c.1 i ≠ g) ∧
          (oldGeneratorIndices (Local.decodeTuple c) old).card = j then
        mass c g * (K / Fintype.card F) else 0)]
    congr 1
    have hcodes : tupleCodesWithOldCount old j =
        Finset.univ.filter (fun c : Local.TupleCode F =>
          (oldGeneratorIndices (Local.decodeTuple c) old).card = j) := by
      ext c
      rw [Finset.mem_filter_univ]
      simp [tupleCodesWithOldCount, generatorLabelsWithOldCount,
        oldGeneratorIndices, Local.decodeTuple]
      rfl
    rw [hcodes, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro c _
    by_cases hjc : (oldGeneratorIndices (Local.decodeTuple c) old).card = j
    · simp only [hjc, and_true, ite_true]
      by_cases hinj : Function.Injective c.1
      · simp only [hinj, true_and, globalTupleCodeTargetMass, ite_true,
          Finset.sum_filter, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro g _
        by_cases hg : ∀ i, c.1 i ≠ g
        · rw [ite_eq_left hg, ite_eq_left hg]
          rfl
        · rw [ite_eq_right hg, ite_eq_right hg, zero_mul]
      · simp only [hinj, false_and, ite_false, globalTupleCodeTargetMass,
          zero_mul, Finset.sum_const_zero]
    · simp only [hjc, and_false, ite_false, Finset.sum_const_zero]
  exact heq.trans_le (sum_globalTupleCodeTargetMass_extension_le old a p j hold hj K hK)

end
end Balanced.ReuseConditional

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_ConfigurationStructure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced
namespace ConfigurationStructure

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F)

theorem split_multiplicity_le_one_of_designated (hC : C.Compatible)
    {s : Slot F} {p : Point F} (hp : p ∈ designated C.merged (C.choice s)) :
    C.splitMultiplicity p ≤ 1 := by
  have hsub : C.splitLinesAt p ⊆ {(C.choice s).line} := by
    intro l hl
    obtain ⟨hlS, hpl⟩ := Finset.mem_filter.mp hl
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hlS
    have hst := designated_slot_unique C hC hp hpl
    simp only [Finset.mem_singleton]
    rw [hst]
  have hc := Finset.card_le_card hsub
  simpa only [Finset.card_singleton, Configuration.splitMultiplicity] using hc

theorem center_not_designated (hC : C.Compatible) {p : Point F}
    (hb : 2 ≤ C.splitMultiplicity p) (s : Slot F) :
    p ∉ designated C.merged (C.choice s) := by
  intro hp
  have hle := split_multiplicity_le_one_of_designated C hC hp
  omega

end ConfigurationStructure
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_ConfigurationReuse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem Configuration.exists_pencil_reuse_witness (C : Configuration F)
    (hvalid : C.Valid) (hcompatible : C.Compatible) (p : Point F)
    (hreuse : 3 ≤ Local.reuseCount C p) :
    ∃ l : List (Slot F), l.Nodup ∧
      (∀ s ∈ l, OnLine p (C.choice s).line) ∧ l.length ≤ 6 ∧
      3 ≤ reuseExposureScore (fun s => generatorSet (C.choice s).tuple) l := by
  have hcount := ConfigurationStructure.split_multiplicity_eq_slots C hvalid hcompatible p
  have hreuse' : 3 ≤
      4 * (Finset.univ.filter (fun s : Slot F => OnLine p (C.choice s).line)).card -
      ((Finset.univ.filter (fun s : Slot F => OnLine p (C.choice s).line)).biUnion
        (fun s => generatorSet (C.choice s).tuple)).card := by
    simpa only [Local.reuseCount, Local.generatorUnionAt, hcount] using hreuse
  obtain ⟨l, hnodup, hsub, hlength, hscore⟩ :=
    C.exists_six_tuple_reuse_order hvalid hcompatible _ hreuse'
  refine ⟨l, hnodup, ?_, hlength, hscore⟩
  intro s hs
  exact (Finset.mem_filter.mp (hsub (List.mem_toFinset.mpr hs))).2

theorem Configuration.tuplePoint_ne_pencil_center (C : Configuration F)
    (hcompatible : C.Compatible) (p : Point F)
    (hmultiplicity : 2 ≤ C.splitMultiplicity p) (s : Slot F) (i : Fin 4) :
    tuplePoint C.merged (C.choice s).tuple i ≠ p := by
  intro heq
  have hp : p ∈ designated C.merged (C.choice s) := by
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, heq⟩
  exact ConfigurationStructure.center_not_designated C hcompatible hmultiplicity s hp

end
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_PatternMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.PatternMoments

open scoped BigOperators

variable {Ω A Y : Type*} [Fintype Ω] [Fintype A] [Fintype Y]

theorem weighted_fiber_bound [DecidableEq Y] (p Z f : Ω → ℝ) (expose : Ω → Y) (M : ℝ)
    (hf : ∀ ω, 0 ≤ f ω)
    (hconst : ∀ ω ω', expose ω = expose ω' → f ω = f ω')
    (hbound : ∀ y, (∑ ω : {ω // expose ω = y}, p ω * Z ω) ≤
      M * ∑ ω : {ω // expose ω = y}, p ω) :
    expectation p (fun ω => f ω * Z ω) ≤ M * expectation p f := by
  classical
  unfold expectation
  rw [← Fintype.sum_fiberwise expose (fun ω => p ω * (f ω * Z ω)),
    ← Fintype.sum_fiberwise expose (fun ω => p ω * f ω), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y _
  cases isEmpty_or_nonempty {ω // expose ω = y} with
  | inl h =>
      let := h
      simp
  | inr h =>
      obtain ⟨x⟩ := h
      have heq (ω : {ω // expose ω = y}) : f ω = f x :=
        hconst ω x (ω.property.trans x.property.symm)
      simp_rw [heq]
      calc
        (∑ ω : {ω // expose ω = y}, p ω * (f x * Z ω)) =
            f x * ∑ ω : {ω // expose ω = y}, p ω * Z ω := by
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro ω _
          ring
        _ ≤ f x * (M * ∑ ω : {ω // expose ω = y}, p ω) :=
          mul_le_mul_of_nonneg_left (hbound y) (hf x)
        _ = M * ∑ ω : {ω // expose ω = y}, p ω * f x := by
          rw [← Finset.sum_mul]
          ring

lemma scheduleCost_nonneg {M L : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L)
    (schedule : List Bool) : 0 ≤ scheduleCost M L schedule := by
  induction schedule with
  | nil => simp [scheduleCost]
  | cons root rest ih =>
      simp only [scheduleCost]
      exact mul_nonneg (by split <;> assumption) ih

theorem scheduledWeight_le
    (W : List A → ℝ) (overlap : List A → A → Prop)
    [∀ pre a, Decidable (overlap pre a)]
    (N : ℕ) (M L : ℝ) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hfree : ∀ pre, pre.length < N →
      (∑ a, W (a :: pre)) ≤ M * W pre)
    (htouch : ∀ pre, pre.length < N →
      (∑ a, if overlap pre a then W (a :: pre) else 0) ≤ L * W pre)
    (schedule : List Bool) (pre : List A)
    (hlen : pre.length + schedule.length ≤ N) :
    scheduledWeight W overlap schedule pre ≤
      scheduleCost M L schedule * W pre := by
  classical
  induction schedule generalizing pre with
  | nil => simp [scheduledWeight, scheduleCost]
  | cons root rest ih =>
      have hshort : pre.length < N := by simp only [List.length_cons] at hlen; omega
      have hrest (a : A) : (a :: pre).length + rest.length ≤ N := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlen
      have hnonneg := scheduleCost_nonneg hM hL rest
      calc
        scheduledWeight W overlap (root :: rest) pre ≤
            ∑ a, if root = true ∨ overlap pre a then
              scheduleCost M L rest * W (a :: pre) else 0 := by
          apply Finset.sum_le_sum
          intro a _
          split_ifs
          · exact ih (a :: pre) (hrest a)
          · exact le_rfl
        _ = scheduleCost M L rest *
            (∑ a, if root = true ∨ overlap pre a then W (a :: pre) else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          split_ifs <;> simp
        _ ≤ scheduleCost M L rest * ((if root then M else L) * W pre) := by
          apply mul_le_mul_of_nonneg_left _ hnonneg
          cases root with
          | false => simpa using htouch pre hshort
          | true => simpa using hfree pre hshort
        _ = scheduleCost M L (root :: rest) * W pre := by
          simp only [scheduleCost]
          ring

attribute [local instance] Classical.propDecidable

theorem scheduledWeight_eq_sum
    (W : List A → ℝ) (overlap : List A → A → Prop)
    [∀ pre a, Decidable (overlap pre a)]
    (schedule : List Bool) (pre : List A) :
    scheduledWeight W overlap schedule pre =
      ∑ a : Fin schedule.length → A,
        if scheduleAllowed overlap schedule (List.ofFn a) pre then
          W ((List.ofFn a).reverse ++ pre) else 0 := by
  classical
  induction schedule generalizing pre with
  | nil => simp [scheduledWeight, scheduleAllowed]
  | cons root rest ih =>
      simp only [List.length_cons]
      rw [← (Fin.consEquiv (fun _ : Fin (rest.length + 1) => A)).sum_comp
        (fun a => if scheduleAllowed overlap (root :: rest) (List.ofFn a) pre then
          W ((List.ofFn a).reverse ++ pre) else 0), Fintype.sum_prod_type]
      simp only [scheduledWeight]
      apply Finset.sum_congr rfl
      intro a _
      rw [ih]
      by_cases ha : root = true ∨ overlap pre a
      · simp [ha, Fin.consEquiv, scheduleAllowed, List.reverse_cons,
          List.append_assoc]
      · simp [ha, Fin.consEquiv, scheduleAllowed]

theorem scheduledWeight_eq_sum_of_length
    (W : List A → ℝ) (overlap : List A → A → Prop)
    [∀ pre a, Decidable (overlap pre a)]
    (schedule : List Bool) (pre : List A) (n : ℕ) (hlen : schedule.length = n) :
    scheduledWeight W overlap schedule pre =
      ∑ a : Fin n → A, if scheduleAllowed overlap schedule (List.ofFn a) pre then
        W ((List.ofFn a).reverse ++ pre) else 0 := by
  subst n
  exact scheduledWeight_eq_sum W overlap schedule pre

end Balanced.PatternMoments

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_ReuseTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ReuseTower

open scoped BigOperators
noncomputable section
open scoped Classical

section FiniteTower
variable {Ω Y A : Type*} [Fintype Ω] [Nonempty Ω] [Fintype Y] [DecidableEq Y]
  [Fintype A]

theorem uniform_probability_eq_average (E : Ω → Prop) :
    ((PMF.uniformOfFintype Ω).toOuterMeasure {ω | E ω}).toReal =
      (∑ ω, if E ω then (1 : ℝ) else 0) / Fintype.card Ω := by
  rw [PMF.toOuterMeasure_uniformOfFintype_apply, ENNReal.toReal_div]
  simp only [ENNReal.toReal_natCast, Fintype.card_subtype]
  simp

omit [Fintype Y] in
theorem conditional_probability_eq_average (expose : Ω → Y) (a : Ω)
    (E : Ω → Prop) :
    (((PMF.uniformOfFintype Ω).filter {ω | expose ω = expose a}
      (fiber_supported expose a)).toOuterMeasure {ω | E ω}).toReal =
      (∑ ω : {ω // expose ω = expose a}, if E ω then (1 : ℝ) else 0) /
        Fintype.card {ω // expose ω = expose a} := by
  let : Nonempty {ω // expose ω = expose a} := ⟨⟨a, rfl⟩⟩
  let : Nonempty ({ω | expose ω = expose a} : Set Ω) := ⟨⟨a, rfl⟩⟩
  rw [Balanced.uniform_filter_eq_subtype_map, PMF.toOuterMeasure_map_apply]
  exact uniform_probability_eq_average (fun ω : {ω // expose ω = expose a} => E ω)

omit [Nonempty Ω] in
theorem weighted_uniform_fiber_bound (expose : Ω → Y) (Z f : Ω → ℝ) (C : ℝ)
    (hf : ∀ ω, 0 ≤ f ω)
    (hconst : ∀ ω ω', expose ω = expose ω' → f ω = f ω')
    (hbound : ∀ a : Ω,
      (∑ ω : {ω // expose ω = expose a}, Z ω) /
        Fintype.card {ω // expose ω = expose a} ≤ C) :
    (∑ ω, f ω * Z ω) / Fintype.card Ω ≤
      C * ((∑ ω, f ω) / Fintype.card Ω) := by
  have h := PatternMoments.weighted_fiber_bound
    (fun _ : Ω => (1 : ℝ)) Z f expose C hf hconst ?_
  · simpa only [PatternMoments.expectation, one_mul, mul_div_assoc] using
      (div_le_div_of_nonneg_right h (Nat.cast_nonneg (Fintype.card Ω)))
  intro y
  cases isEmpty_or_nonempty {ω // expose ω = y} with
  | inl h =>
      let := h
      simp
  | inr h =>
      obtain ⟨a, ha⟩ := h
      have hb := hbound a
      rw [ha] at hb
      have hcard : (0 : ℝ) < Fintype.card {ω // expose ω = y} := by
        let : Nonempty {ω // expose ω = y} := ⟨⟨a, ha⟩⟩
        exact_mod_cast (Fintype.card_pos (α := {ω // expose ω = y}))
      simpa only [one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        mul_one] using (div_le_iff₀ hcard).mp hb

theorem event_extension_bound (expose : Ω → Y) (E : A → Ω → Prop)
    (P : Ω → Prop) (C : ℝ)
    (hP : ∀ ω ω', expose ω = expose ω' → (P ω ↔ P ω'))
    (hbound : ∀ a : Ω,
      (∑ i : A, (((PMF.uniformOfFintype Ω).filter
        {ω | expose ω = expose a} (fiber_supported expose a)).toOuterMeasure
          {ω | E i ω}).toReal) ≤ C) :
    (∑ i : A, ((PMF.uniformOfFintype Ω).toOuterMeasure
      {ω | P ω ∧ E i ω}).toReal) ≤
      C * ((PMF.uniformOfFintype Ω).toOuterMeasure {ω | P ω}).toReal := by
  simp_rw [uniform_probability_eq_average]
  rw [← Finset.sum_div]
  have h := weighted_uniform_fiber_bound expose
    (fun ω => ∑ i : A, if E i ω then (1 : ℝ) else 0)
    (fun ω => if P ω then (1 : ℝ) else 0) C
    (fun _ => by split_ifs <;> norm_num)
    (fun ω ω' heq => by simp only [hP ω ω' heq]) ?_
  · convert h using 1
    all_goals try with_reducible_and_instances rfl
    rw [Finset.sum_comm]
    apply congrArg (fun x : ℝ => x / Fintype.card Ω)
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hp : P ω <;> simp [hp]
  intro a
  have hb := hbound a
  simp_rw [conditional_probability_eq_average] at hb
  rw [← Finset.sum_div, Finset.sum_comm] at hb
  exact hb

end FiniteTower
end
end Balanced.ReuseTower

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_ReusePrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ReuseTower

open scoped BigOperators
noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] in
theorem tuplePoint_eq_of_expose_eq (pre : List (Prescription F))
    (r : Prescription F) (hr : r ∈ pre) (M N : MergedPairs F)
    (hMN : expose (exposedDirections pre) M = expose (exposedDirections pre) N)
    (i : Fin 4) :
    tuplePoint M (prescriptionTuple r) i = tuplePoint N (prescriptionTuple r) i := by
  have hg (j : Fin 4) : (prescriptionTuple r).generator j ∈ exposedDirections pre := by
    apply Finset.mem_biUnion.mpr
    exact ⟨r, List.mem_toFinset.mpr hr, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
  have heq := (expose_eq_iff _ _ _).mp hMN
  simp only [tuplePoint, constituent, heq _ (hg i), heq _ (hg (i + 1))]

omit [Fintype F] in
theorem prefixEvent_depends_on_exposed (p : Point F) (pre : List (Prescription F))
    (M N : MergedPairs F)
    (hMN : expose (exposedDirections pre) M = expose (exposedDirections pre) N) :
    prefixEvent p pre M ↔ prefixEvent p pre N := by
  unfold prefixEvent prescriptionEvent
  apply forall_congr'
  intro r
  apply forall_congr'
  intro hr
  simp only [tuplePoint_eq_of_expose_eq pre r hr M N hMN]

omit [Field F] [Fintype F] in
theorem exposedDirections_card_le (pre : List (Prescription F)) :
    (exposedDirections pre).card ≤ 4 * pre.length := by
  calc
    (exposedDirections pre).card ≤ ∑ r ∈ pre.toFinset, (prescriptionGenerators r).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _r ∈ pre.toFinset, 4 := by
      apply Finset.sum_le_sum
      intro r _
      exact (Finset.card_image_le).trans (by simp)
    _ ≤ 4 * pre.length := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      nlinarith [List.toFinset_card_le pre]

theorem prefixWeight_nonneg (K : ℝ) (hK : 0 ≤ K) (p : Point F)
    (pre : List (Prescription F)) : 0 ≤ prefixWeight K p pre := by
  unfold prefixWeight Local.offsetProbability
  positivity

theorem offsetProbability_eq_uniform (E : MergedPairs F → Prop) :
    Local.offsetProbability E =
      ((PMF.uniformOfFintype (MergedPairs F)).toOuterMeasure {M | E M}).toReal :=
  (uniform_probability_eq_average E).symm

end
end Balanced.ReuseTower

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_ReusePrefixExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ReuseTower

open PartialAlignment
open scoped BigOperators
noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private theorem static_event_probability {Ω : Type*} (μ : PMF Ω)
    (A : Prop) (E : Ω → Prop) :
    (μ.toOuterMeasure {ω | A ∧ E ω}).toReal =
      if A then (μ.toOuterMeasure {ω | E ω}).toReal else 0 := by
  by_cases hA : A
  · simp only [hA, true_and, ite_true]
  · simp [hA]

private theorem exposed_filter_eq (old : Finset (Direction F)) (a : MergedPairs F) :
    (PMF.uniformOfFintype (MergedPairs F)).filter
      {M | expose old M = expose old a} (fiber_supported (expose old) a) =
    (offsetLaw F).filter {M | ∀ d ∈ old, M d = a d}
      (canonical_exposure_supported old a) := by
  have hs : {M | expose old M = expose old a} =
      {M | ∀ d ∈ old, M d = a d} := Set.ext (fun M => expose_eq_iff old M a)
  ext M
  simp only [PMF.filter_apply, hs, offsetLaw_eq_uniform]

private theorem conditional_prescription_probability (pre : List (Prescription F))
    (a : MergedPairs F) (p : Point F) (j : ℕ) (r : Prescription F) :
    (((PMF.uniformOfFintype (MergedPairs F)).filter
      {M | expose (exposedDirections pre) M = expose (exposedDirections pre) a}
      (fiber_supported (expose (exposedDirections pre)) a)).toOuterMeasure
      {M | oldCount pre r = j ∧ prescriptionEvent p r M}).toReal =
    if Function.Injective r.2.1 ∧ (∀ i, r.2.1 i ≠ r.1.1) ∧
        (oldGeneratorIndices (Local.decodeTuple r.2) (exposedDirections pre)).card = j then
      (((offsetLaw F).filter {M | ∀ d ∈ exposedDirections pre, M d = a d}
        (canonical_exposure_supported (exposedDirections pre) a)).toOuterMeasure
        {M | (∀ i, OnLine (tuplePoint M (Local.decodeTuple r.2) i)
          (lineThrough r.1.1 p)) ∧
          ∀ i, tuplePoint M (Local.decodeTuple r.2) i ≠ p}).toReal else 0 := by
  rw [exposed_filter_eq]
  have hs : {M : MergedPairs F | oldCount pre r = j ∧ prescriptionEvent p r M} =
      {M | (Function.Injective r.2.1 ∧ (∀ i, r.2.1 i ≠ r.1.1) ∧
          (oldGeneratorIndices (Local.decodeTuple r.2) (exposedDirections pre)).card = j) ∧
        ((∀ i, OnLine (tuplePoint M (Local.decodeTuple r.2) i) (lineThrough r.1.1 p)) ∧
          ∀ i, tuplePoint M (Local.decodeTuple r.2) i ≠ p)} := by
    ext M
    simp only [Set.mem_ofPred_eq, prescriptionEvent, oldCount, prescriptionTuple]
    tauto
  rw [hs, static_event_probability]
  split_ifs <;> rfl

theorem conditional_prescription_sum_le (pre : List (Prescription F))
    (hpre : pre.length < 6) (a : MergedPairs F) (p : Point F)
    (j : ℕ) (hj : j ≤ 4) :
    (∑ r : Prescription F,
      (((PMF.uniformOfFintype (MergedPairs F)).filter
        {M | expose (exposedDirections pre) M = expose (exposedDirections pre) a}
        (fiber_supported (expose (exposedDirections pre)) a)).toOuterMeasure
        {M | oldCount pre r = j ∧ prescriptionEvent p r M}).toReal) ≤
      (4 * (4096 * 24 ^ 4) : ℝ) * Fintype.card F /
        (Fintype.card F : ℝ) ^ reuseSaving j := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  have hold : (exposedDirections pre).card ≤ 24 := by
    have h := exposedDirections_card_le pre
    omega
  have h := ReuseConditional.full_code_extension_le (exposedDirections pre) a p j
    hold hj (Fintype.card F) hq.le
  rw [div_self hq.ne'] at h
  simp only [mul_one] at h
  apply le_trans (le_of_eq ?_) h
  exact Finset.sum_congr rfl (fun r _ => conditional_prescription_probability pre a p j r)

theorem prefixWeight_extension_le (K : ℝ) (hK : 0 ≤ K) (p : Point F)
    (pre : List (Prescription F)) (hpre : pre.length < 6) (j : ℕ) (hj : j ≤ 4) :
    (∑ r : Prescription F, if oldCount pre r = j then prefixWeight K p (r :: pre) else 0) ≤
      ((4 * (4096 * 24 ^ 4) : ℝ) * K /
        (Fintype.card F : ℝ) ^ reuseSaving j) * prefixWeight K p pre := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  have hstep := event_extension_bound
    (expose (exposedDirections pre))
    (fun r M => oldCount pre r = j ∧ prescriptionEvent p r M)
    (prefixEvent p pre)
    ((4 * (4096 * 24 ^ 4) : ℝ) * Fintype.card F /
      (Fintype.card F : ℝ) ^ reuseSaving j)
    (prefixEvent_depends_on_exposed p pre)
    (fun a => conditional_prescription_sum_le pre hpre a p j hj)
  have hevent (r : Prescription F) :
      ((PMF.uniformOfFintype (MergedPairs F)).toOuterMeasure
        {M | prefixEvent p pre M ∧ oldCount pre r = j ∧ prescriptionEvent p r M}).toReal =
      if oldCount pre r = j then Local.offsetProbability (prefixEvent p (r :: pre)) else 0 := by
    by_cases hr : oldCount pre r = j
    · rw [ite_eq_left hr, offsetProbability_eq_uniform]
      congr 2
      ext M
      simp only [hr, true_and, prefixEvent, List.mem_cons, forall_eq_or_imp,
        Set.mem_ofPred_eq, and_comm]
    · rw [ite_eq_right hr]
      have hset : {M | prefixEvent p pre M ∧ oldCount pre r = j ∧ prescriptionEvent p r M} =
          (∅ : Set (MergedPairs F)) := by
        ext M
        simp only [hr, false_and, and_false, Set.mem_ofPred_eq, Set.mem_empty_iff_false]
      rw [hset]
      simp
  simp_rw [hevent] at hstep
  rw [← offsetProbability_eq_uniform] at hstep
  calc
    (∑ r : Prescription F, if oldCount pre r = j then prefixWeight K p (r :: pre) else 0) =
        (K / Fintype.card F) ^ (pre.length + 1) *
          ∑ r : Prescription F, if oldCount pre r = j then
            Local.offsetProbability (prefixEvent p (r :: pre)) else 0 := by
      simp only [prefixWeight, List.length_cons, Finset.mul_sum, mul_ite, mul_zero]
    _ ≤ (K / Fintype.card F) ^ (pre.length + 1) *
        (((4 * (4096 * 24 ^ 4) : ℝ) * Fintype.card F /
          (Fintype.card F : ℝ) ^ reuseSaving j) *
          Local.offsetProbability (prefixEvent p pre)) :=
      mul_le_mul_of_nonneg_left hstep (pow_nonneg (div_nonneg hK hq.le) _)
    _ = _ := by
      unfold prefixWeight
      rw [pow_succ]
      field_simp

end
end Balanced.ReuseTower

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.KernelBridge

open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*}

variable [Field F] [Fintype F] [DecidableEq F]

theorem selectedProbability_mono (w : Kernel F) (hw : ∀ M v, 0 ≤ w M v)
    {E G : Configuration F → Prop} (h : ∀ C, E C → G C) :
    selectedProbability w E ≤ selectedProbability w G := by
  unfold selectedProbability
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro M _
  apply Finset.sum_le_sum
  intro v _
  by_cases hE : E (configuration M v)
  · simp only [hE, h _ hE, ite_true]
    exact le_rfl
  · simp only [hE, ite_false]
    split_ifs
    · exact hw M v
    · exact le_rfl

theorem selected_prescription_and_offset_le
    (Q : RetentionRule F) (w : Kernel F) (K : ℝ)
    (hw : KernelConditions Q w K) (S : Finset (Slot F))
    (t : MergedPairs F → Slot F → TupleCode F) (E : MergedPairs F → Prop) :
    selectedProbability w (fun C => E C.merged ∧
      ∀ s ∈ S, encodeTuple (C.choice s).tuple = t C.merged s) ≤
      (K / Fintype.card F) ^ S.card * offsetProbability E := by
  let r : ℝ := (K / Fintype.card F) ^ S.card
  have hpoint : ∀ M : MergedPairs F,
      (∑ v : Output F, if E M ∧ (∀ s ∈ S, (v s).2 = t M s)
        then w M v else 0) ≤ if E M then r else 0 := by
    intro M
    by_cases hE : E M
    · simpa only [hE, true_and, ite_true] using hw.2.2.2 M S (t M)
    · simp [hE]
  have hsum : (∑ M : MergedPairs F, if E M then r else 0) =
      r * ∑ M : MergedPairs F, if E M then (1 : ℝ) else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro M _
    split_ifs <;> simp
  have hform : selectedProbability w (fun C => E C.merged ∧
      ∀ s ∈ S, encodeTuple (C.choice s).tuple = t C.merged s) =
      (∑ M : MergedPairs F, ∑ v : Output F,
        if E M ∧ (∀ s ∈ S, (v s).2 = t M s) then w M v else 0) /
          Fintype.card (MergedPairs F) := by
    unfold selectedProbability
    congr 1
    apply Finset.sum_congr rfl
    intro M _
    apply Finset.sum_congr rfl
    intro v _
    simp [configuration, decodeChoice, encodeTuple, decodeTuple]
  rw [hform]
  calc
    _ ≤ (∑ M : MergedPairs F, if E M then r else 0) /
        Fintype.card (MergedPairs F) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun M _ => hpoint M)) (by positivity)
    _ = r * offsetProbability E := by rw [hsum]; simp [offsetProbability, div_eq_mul_inv, mul_assoc]

end
end Balanced.Local.KernelBridge

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_ReuseScore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ReuseTower

open scoped BigOperators
noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] [Fintype F] in
theorem oldCount_eq_generator_overlap (pre : List (Prescription F))
    (r : Prescription F) (hr : Function.Injective r.2.1) :
    oldCount pre r =
      (prescriptionGenerators r ∩ pre.toFinset.biUnion prescriptionGenerators).card := by
  exact card_oldGeneratorIndices (prescriptionTuple r) (exposedDirections pre) hr

omit [Field F] [Fintype F] in
theorem prefixScore_eq_reuseExposureScore (pre : List (Prescription F))
    (hvalid : ∀ r ∈ pre, Function.Injective r.2.1) :
    prefixScore pre = reuseExposureScore prescriptionGenerators pre := by
  induction pre with
  | nil => rfl
  | cons r pre ih =>
      have hr := hvalid r (by simp)
      have hpre : ∀ s ∈ pre, Function.Injective s.2.1 := by
        intro s hs
        exact hvalid s (by simp [hs])
      rw [prefixScore, reuseExposureScore, ih hpre,
        oldCount_eq_generator_overlap pre r hr]

theorem prefixWeight_eq_zero_of_not_injective (K : ℝ) (p : Point F)
    (pre : List (Prescription F))
    (hinvalid : ¬ ∀ r ∈ pre, Function.Injective r.2.1) :
    prefixWeight K p pre = 0 := by
  have hempty : ∀ M : MergedPairs F, ¬ prefixEvent p pre M := by
    intro M h
    exact hinvalid (fun r hr => (h r hr).1)
  simp [prefixWeight, Local.offsetProbability, hempty]

theorem score_cutoff_weight_eq (K : ℝ) (p : Point F)
    (pre : List (Prescription F)) (m : ℕ) :
    (if m ≤ reuseExposureScore prescriptionGenerators pre then prefixWeight K p pre else 0) =
      (if m ≤ prefixScore pre then prefixWeight K p pre else 0) := by
  by_cases hvalid : ∀ r ∈ pre, Function.Injective r.2.1
  · rw [prefixScore_eq_reuseExposureScore pre hvalid]
  · simp [prefixWeight_eq_zero_of_not_injective K p pre hvalid]

omit [Field F] [Fintype F] in
theorem prescriptionGenerators_card_le_four (r : Prescription F) :
    (prescriptionGenerators r).card ≤ 4 := by
  exact (Finset.card_image_le).trans (by simp)

theorem category_cutoff_weight_eq (K : ℝ) (p : Point F)
    (pre : List (Prescription F)) (r : Prescription F) (j : ℕ) :
    (if (prescriptionGenerators r ∩ pre.toFinset.biUnion prescriptionGenerators).card = j
      then prefixWeight K p (r :: pre) else 0) =
      (if oldCount pre r = j then prefixWeight K p (r :: pre) else 0) := by
  by_cases hr : Function.Injective r.2.1
  · rw [oldCount_eq_generator_overlap pre r hr]
  · have hz : prefixWeight K p (r :: pre) = 0 :=
      prefixWeight_eq_zero_of_not_injective K p (r :: pre)
        (fun h => hr (h r (by simp)))
    simp [hz]

omit [Fintype F] [DecidableEq F] in
theorem prefixEvent_iff (p : Point F) (pre : List (Prescription F)) (M : MergedPairs F) :
    prefixEvent p pre M ↔
      (∀ r ∈ pre, Function.Injective r.2.1 ∧ ∀ i, r.2.1 i ≠ r.1.1) ∧
      (∀ r ∈ pre, (∀ i, OnLine (tuplePoint M (prescriptionTuple r) i)
          (lineThrough r.1.1 p)) ∧
        ∀ i, tuplePoint M (prescriptionTuple r) i ≠ p) := by
  constructor
  · intro h
    exact ⟨fun r hr => ⟨(h r hr).1, (h r hr).2.1⟩,
      fun r hr => (h r hr).2.2⟩
  · rintro ⟨hstatic, hgeom⟩ r hr
    exact ⟨(hstatic r hr).1, (hstatic r hr).2, hgeom r hr⟩

end
end Balanced.ReuseTower

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_ReusePrescriptions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ReusePrescription

open Local Local.KernelBridge
open scoped BigOperators

noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem reuseExposureScore_map {α β γ : Type*}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (A : β → Finset γ) (f : α → β) (l : List α) :
    reuseExposureScore A (l.map f) = reuseExposureScore (fun x => A (f x)) l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have hset : (l.map f).toFinset.biUnion A =
        l.toFinset.biUnion (fun x => A (f x)) := by
      ext x
      simp
    simp only [List.map_cons, reuseExposureScore, ih, hset]

theorem exists_of_configuration (C : Configuration F)
    (hv : C.Valid) (hc : C.Compatible) (p : Point F)
    (hb : 2 ≤ C.splitMultiplicity p) (hr : 3 ≤ reuseCount C p) :
    ∃ l : List (Code F), l.length ≤ 6 ∧ Eligible l ∧
      AlignedExternal p l C.merged ∧ Matches l C := by
  obtain ⟨l, hnd, hthrough, hlen, hscore⟩ :=
    C.exists_pencil_reuse_witness hv hc p hr
  refine ⟨l.map (encode C), by simpa using hlen, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · simpa [encode, List.map_map, Function.comp_def] using hnd
    · intro c hc'
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hc'
      exact ⟨(hv.2 s).2.2.1, (hv.2 s).2.2.2.1⟩
    · simpa [reuseExposureScore_map, generators, encode] using hscore
  · intro c hc'
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hc'
    have heq : (C.choice s).line = lineThrough s.1 p := by
      rw [line_eq_lineThrough p _ (hthrough s hs), (hv.2 s).1]
    constructor
    · intro i
      simpa [encode, heq] using (hv.2 s).2.2.2.2.2.1 i
    · intro i
      simpa [encode] using C.tuplePoint_ne_pencil_center hc p hb s i
  · intro c hc'
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hc'
    rfl

omit [Field F] [Fintype F] in
theorem matches_codeAt {l : List (Code F)} {C : Configuration F}
    (h : Matches l C) :
    ∀ s ∈ slots l, encodeTuple (C.choice s).tuple = codeAt l s := by
  intro s hs
  have hex : ∃ c ∈ l, c.1 = s := by
    simpa [slots] using hs
  obtain ⟨hc, heq⟩ := Classical.choose_spec hex
  rw [codeAt, dite_eq_left hex]
  exact (congrArg (fun t => encodeTuple (C.choice t).tuple) heq).symm.trans (h _ hc)

omit [Field F] [Fintype F] in
theorem slots_card {l : List (Code F)} (h : (l.map Prod.fst).Nodup) :
    (slots l).card = l.length := by
  simp [slots, List.toFinset_card_of_nodup h]

theorem selected_list_le (Q : RetentionRule F) (w : Kernel F) (K : ℝ)
    (hw : KernelConditions Q w K) (p : Point F) (l : List (Code F))
    (hnd : (l.map Prod.fst).Nodup) :
    selectedProbability w (fun C => AlignedExternal p l C.merged ∧ Matches l C) ≤
      (K / Fintype.card F) ^ l.length * offsetProbability (AlignedExternal p l) := by
  calc
    _ ≤ selectedProbability w (fun C => AlignedExternal p l C.merged ∧
        ∀ s ∈ slots l, encodeTuple (C.choice s).tuple = codeAt l s) :=
      selectedProbability_mono w hw.1 (fun _ h => ⟨h.1, matches_codeAt h.2⟩)
    _ ≤ (K / Fintype.card F) ^ (slots l).card *
        offsetProbability (AlignedExternal p l) :=
      selected_prescription_and_offset_le Q w K hw (slots l)
        (fun _ => codeAt l) (AlignedExternal p l)
    _ = _ := by rw [slots_card hnd]

theorem selected_union_le {ι : Type*} (S : Finset ι)
    (w : Kernel F) (hw : ∀ M v, 0 ≤ w M v)
    (E : Configuration F → Prop) (A : ι → Configuration F → Prop)
    (hcover : ∀ M v, 0 < w M v → E (configuration M v) →
      ∃ i ∈ S, A i (configuration M v)) :
    selectedProbability w E ≤ ∑ i ∈ S, selectedProbability w (A i) := by
  have hpoint (M : MergedPairs F) (v : Output F) :
      (if E (configuration M v) then w M v else 0) ≤
        ∑ i ∈ S, if A i (configuration M v) then w M v else 0 := by
    have hn i : 0 ≤ if A i (configuration M v) then w M v else 0 := by
      split_ifs <;> simp_all
    by_cases hE : E (configuration M v)
    · simp only [hE, ite_true]
      by_cases hz : w M v = 0
      · simp [hz]
      · obtain ⟨i, hi, hA⟩ := hcover M v (lt_of_le_of_ne (hw M v) (Ne.symm hz)) hE
        calc
          w M v = if A i (configuration M v) then w M v else 0 := by simp [hA]
          _ ≤ ∑ j ∈ S, if A j (configuration M v) then w M v else 0 :=
            Finset.single_le_sum (fun j _ => hn j) hi
    · simp only [hE, ite_false]
      exact Finset.sum_nonneg (fun i _ => hn i)
  unfold selectedProbability
  calc
    _ ≤ (∑ M : MergedPairs F, ∑ v : Output F,
        ∑ i ∈ S, if A i (configuration M v) then w M v else 0) /
        Fintype.card (MergedPairs F) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact Finset.sum_le_sum (fun M _ => Finset.sum_le_sum (fun v _ => hpoint M v))
    _ = _ := by
      simp_rw [Finset.sum_div]
      let f (M : MergedPairs F) (v : Output F) (i : ι) : ℝ :=
        (if A i (configuration M v) then w M v else 0) /
          Fintype.card (MergedPairs F)
      change (∑ M, ∑ v, ∑ i ∈ S, f M v i) = ∑ i ∈ S, ∑ M, ∑ v, f M v i
      calc
        _ = ∑ M, ∑ i ∈ S, ∑ v, f M v i :=
          Finset.sum_congr rfl (fun M _ => Finset.sum_comm)
        _ = _ := Finset.sum_comm

theorem selected_reuse_le_witness_sum
    (Q : RetentionRule F) (w : Kernel F) (K : ℝ)
    (hw : KernelConditions Q w K) (p : Point F) :
    selectedProbability w (fun C => 2 ≤ C.splitMultiplicity p ∧ 3 ≤ reuseCount C p) ≤
      ∑ l ∈ witnesses F,
        (K / Fintype.card F) ^ l.length * offsetProbability (AlignedExternal p l) := by
  calc
    _ ≤ ∑ l ∈ witnesses F,
        selectedProbability w (fun C => AlignedExternal p l C.merged ∧ Matches l C) := by
      apply selected_union_le (witnesses F) w hw.1
      intro M v hpos hevent
      obtain ⟨hv, hc, _⟩ := hw.2.2.1 M v hpos
      obtain ⟨l, hlen, hel, halt, hmatch⟩ :=
        exists_of_configuration (configuration M v) hv hc p hevent.1 hevent.2
      exact ⟨l, mem_witnesses l |>.mpr ⟨hlen, hel⟩, halt, hmatch⟩
    _ ≤ _ := Finset.sum_le_sum (fun l hl =>
      selected_list_le Q w K hw p l ((mem_witnesses l).mp hl).2.1)

theorem allLists_eq_image {α : Type*} [Fintype α] [DecidableEq α] (n : ℕ) :
    allLists α n = (Finset.univ : Finset (Fin n → α)).image List.ofFn := by
  ext l
  rw [mem_allLists, Finset.mem_image]
  constructor
  · intro hlen
    subst n
    exact ⟨l.get, Finset.mem_univ _, List.ofFn_get l⟩
  · rintro ⟨f, _, rfl⟩
    simp

theorem sum_allLists {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (f : List α → ℝ) :
    (∑ l ∈ allLists α n, f l) = ∑ t : Fin n → α, f (List.ofFn t) := by
  rw [allLists_eq_image, Finset.sum_image]
  exact fun a _ b _ h => List.ofFn_injective h

omit [Fintype F] [DecidableEq F] in
theorem alignedExternal_eq_prefixEvent (p : Point F) (l : List (Code F))
    (hel : ∀ c ∈ l, TupleEligible c) :
    AlignedExternal p l = ReuseTower.prefixEvent p l := by
  funext M
  apply propext
  rw [ReuseTower.prefixEvent_iff]
  exact ⟨fun h => ⟨hel, h⟩, fun h => h.2⟩

theorem witness_weight_eq (K : ℝ) (p : Point F) (l : List (Code F))
    (hel : Eligible l) :
    (K / Fintype.card F) ^ l.length * offsetProbability (AlignedExternal p l) =
      ReuseTower.prefixWeight K p l := by
  rw [ReuseTower.prefixWeight, alignedExternal_eq_prefixEvent p l hel.2.1]

theorem selected_reuse_le_prefix_sum
    (Q : RetentionRule F) (w : Kernel F) (K : ℝ)
    (hw : KernelConditions Q w K) (p : Point F) :
    selectedProbability w (fun C => 2 ≤ C.splitMultiplicity p ∧ 3 ≤ reuseCount C p) ≤
      ∑ l ∈ witnesses F, ReuseTower.prefixWeight K p l := by
  calc
    _ ≤ _ := selected_reuse_le_witness_sum Q w K hw p
    _ = _ := Finset.sum_congr rfl (fun l hl =>
      witness_weight_eq K p l ((mem_witnesses l).mp hl).2)

theorem witness_prefix_sum_le
    (K : ℝ) (hK : 0 ≤ K) (p : Point F) :
    (∑ l ∈ witnesses F, ReuseTower.prefixWeight K p l) ≤
      ∑ n ∈ Finset.range 7, ∑ t : Fin n → Code F,
        if 3 ≤ ReuseTower.prefixScore (List.ofFn t)
        then ReuseTower.prefixWeight K p (List.ofFn t) else 0 := by
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range 7) : Set ℕ)
      (fun n => (allLists (Code F) n).filter Eligible) := by
    intro n hn m hm hne
    apply Finset.disjoint_left.mpr
    intro l hln hlm
    have hn' := (mem_allLists l n).mp (Finset.mem_filter.mp hln).1
    have hm' := (mem_allLists l m).mp (Finset.mem_filter.mp hlm).1
    exact hne (hn'.symm.trans hm')
  rw [witnesses, Finset.sum_biUnion hdisj]
  apply Finset.sum_le_sum
  intro n hn
  calc
    _ ≤ ∑ l ∈ (allLists (Code F) n).filter
          (fun l => 3 ≤ reuseExposureScore generators l), ReuseTower.prefixWeight K p l := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro l hl
        obtain ⟨hl, hel⟩ := Finset.mem_filter.mp hl
        exact Finset.mem_filter.mpr ⟨hl, hel.2.2⟩
      · intro l _ _
        exact ReuseTower.prefixWeight_nonneg K hK p l
    _ = ∑ t : Fin n → Code F,
        if 3 ≤ reuseExposureScore generators (List.ofFn t)
        then ReuseTower.prefixWeight K p (List.ofFn t) else 0 := by
      rw [Finset.sum_filter, sum_allLists]
    _ = _ := Finset.sum_congr rfl (fun t _ =>
      ReuseTower.score_cutoff_weight_eq K p (List.ofFn t) 3)

theorem selected_reuse_le_function_sum
    (Q : RetentionRule F) (w : Kernel F) (K : ℝ) (hK : 0 ≤ K)
    (hw : KernelConditions Q w K) (p : Point F) :
    selectedProbability w (fun C => 2 ≤ C.splitMultiplicity p ∧ 3 ≤ reuseCount C p) ≤
      ∑ n ∈ Finset.range 7, ∑ t : Fin n → ReuseTower.Prescription F,
        if 3 ≤ ReuseTower.prefixScore (List.ofFn t)
        then ReuseTower.prefixWeight K p (List.ofFn t) else 0 :=
  (selected_reuse_le_prefix_sum Q w K hw p).trans (witness_prefix_sum_le K hK p)

theorem sum_allLists_reverse {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (f : List α → ℝ) :
    (∑ l ∈ allLists α n, f l) = ∑ l ∈ allLists α n, f l.reverse := by
  apply Finset.sum_bij (fun l _ => l.reverse)
  · intro l hl
    simpa using hl
  · intro a ha b hb hab
    exact List.reverse_injective hab
  · intro l hl
    exact ⟨l.reverse, by simpa using hl, by simp⟩
  · intro l hl
    simp

theorem sum_ofFn_eq_sum_reverse {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (f : List α → ℝ) :
    (∑ t : Fin n → α, f (List.ofFn t)) =
      ∑ t : Fin n → α, f (List.ofFn t).reverse := by
  calc
    _ = ∑ l ∈ allLists α n, f l := (sum_allLists n f).symm
    _ = ∑ l ∈ allLists α n, f l.reverse := sum_allLists_reverse n f
    _ = _ := sum_allLists n (fun l => f l.reverse)

theorem selected_reuse_le_reversed_function_sum
    (Q : RetentionRule F) (w : Kernel F) (K : ℝ) (hK : 0 ≤ K)
    (hw : KernelConditions Q w K) (p : Point F) :
    selectedProbability w (fun C => 2 ≤ C.splitMultiplicity p ∧ 3 ≤ reuseCount C p) ≤
      ∑ n ∈ Finset.range 7, ∑ t : Fin n → ReuseTower.Prescription F,
        if 3 ≤ ReuseTower.prefixScore (List.ofFn t).reverse
        then ReuseTower.prefixWeight K p (List.ofFn t).reverse else 0 := by
  calc
    _ ≤ _ := selected_reuse_le_function_sum Q w K hK hw p
    _ = _ := Finset.sum_congr rfl (fun n _ => sum_ofFn_eq_sum_reverse n
      (fun l => if 3 ≤ ReuseTower.prefixScore l then ReuseTower.prefixWeight K p l else 0))

end
end Balanced.ReusePrescription

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_ReuseSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ReuseSchedule

open scoped BigOperators

noncomputable section
open scoped Classical

variable {A J : Type*} [Fintype A] [Fintype J] [DecidableEq J]

theorem sum_category_weight (category : A → J) (cost : J → ℝ) (W : A → ℝ) :
    (∑ a, cost (category a) * W a) =
      ∑ j, cost j * (∑ a, if category a = j then W a else 0) := by
  classical
  calc
    (∑ a, cost (category a) * W a) =
        ∑ a, ∑ j, if category a = j then cost j * W a else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      simp
    _ = ∑ j, cost j * (∑ a, if category a = j then W a else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp

theorem weighted_step_le (W : List A → ℝ) (score : List A → ℕ)
    (category : List A → A → J) (saving : J → ℕ)
    (q C : ℝ) (hq : 0 < q) (pre : List A)
    (hscore : ∀ a, score (a :: pre) = score pre + saving (category pre a))
    (hstep : ∀ j, (∑ a, if category pre a = j then W (a :: pre) else 0) ≤
      (C / q ^ saving j) * W pre) :
    (∑ a, q ^ score (a :: pre) * W (a :: pre)) ≤
      ((Fintype.card J : ℝ) * C) * (q ^ score pre * W pre) := by
  classical
  calc
    (∑ a, q ^ score (a :: pre) * W (a :: pre)) =
        q ^ score pre * ∑ a, q ^ saving (category pre a) * W (a :: pre) := by
      simp_rw [hscore, pow_add]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = q ^ score pre * ∑ j,
        q ^ saving j * (∑ a, if category pre a = j then W (a :: pre) else 0) := by
      rw [sum_category_weight (category pre) (fun j => q ^ saving j)
        (fun a => W (a :: pre))]
    _ ≤ q ^ score pre * ∑ _j : J, C * W pre := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hq.le _)
      apply Finset.sum_le_sum
      intro j _
      calc
        q ^ saving j * (∑ a, if category pre a = j then W (a :: pre) else 0) ≤
            q ^ saving j * ((C / q ^ saving j) * W pre) :=
          mul_le_mul_of_nonneg_left (hstep j) (pow_nonneg hq.le _)
        _ = C * W pre := by
          field_simp
    _ = ((Fintype.card J : ℝ) * C) * (q ^ score pre * W pre) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

omit [Fintype A] in
private theorem scheduleAllowed_all_true
    (overlap : List A → A → Prop) (n : ℕ) (labels pre : List A) :
    PatternMoments.scheduleAllowed overlap (List.replicate n true) labels pre ↔
      labels.length = n := by
  induction n generalizing labels pre with
  | zero => cases labels <;> simp [PatternMoments.scheduleAllowed]
  | succ n ih =>
      cases labels with
      | nil => simp [PatternMoments.scheduleAllowed]
      | cons a labels =>
          simpa [List.replicate_succ, PatternMoments.scheduleAllowed] using ih labels (a :: pre)

private theorem scheduleCost_all_true (C L : ℝ) (n : ℕ) :
    PatternMoments.scheduleCost C L (List.replicate n true) = C ^ n := by
  induction n with
  | zero => simp [PatternMoments.scheduleCost]
  | succ n ih => simp [List.replicate_succ, PatternMoments.scheduleCost, ih, pow_succ, mul_comm]

theorem sum_words_le (W : List A → ℝ) (N n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hstep : ∀ pre, pre.length < N → (∑ a, W (a :: pre)) ≤ C * W pre)
    (pre : List A) (hlen : pre.length + n ≤ N) :
    (∑ a : Fin n → A, W ((List.ofFn a).reverse ++ pre)) ≤ C ^ n * W pre := by
  classical
  let overlap : List A → A → Prop := fun _ _ => False
  have hexpand := PatternMoments.scheduledWeight_eq_sum_of_length W overlap
    (List.replicate n true) pre n (List.length_replicate ..)
  have hallowed (a : Fin n → A) : PatternMoments.scheduleAllowed overlap
      (List.replicate n true) (List.ofFn a) pre :=
    (scheduleAllowed_all_true overlap n (List.ofFn a) pre).mpr (List.length_ofFn ..)
  simp only [hallowed, ite_true] at hexpand
  rw [← hexpand]
  have h := PatternMoments.scheduledWeight_le W overlap N C 0 hC le_rfl hstep
    (by intro pre _; simp [overlap]) (List.replicate n true) pre
    (by simpa using hlen)
  simpa only [scheduleCost_all_true] using h

theorem sum_weighted_words_le (W : List A → ℝ) (score : List A → ℕ)
    (category : List A → A → J) (saving : J → ℕ)
    (N n : ℕ) (q C : ℝ) (hq : 0 < q) (hC : 0 ≤ C)
    (hscore : ∀ pre a, score (a :: pre) = score pre + saving (category pre a))
    (hstep : ∀ pre, pre.length < N → ∀ j,
      (∑ a, if category pre a = j then W (a :: pre) else 0) ≤
        (C / q ^ saving j) * W pre)
    (pre : List A) (hlen : pre.length + n ≤ N) :
    (∑ a : Fin n → A,
      q ^ score ((List.ofFn a).reverse ++ pre) * W ((List.ofFn a).reverse ++ pre)) ≤
      ((Fintype.card J : ℝ) * C) ^ n * (q ^ score pre * W pre) := by
  apply sum_words_le (fun l => q ^ score l * W l) N n
    ((Fintype.card J : ℝ) * C) (mul_nonneg (Nat.cast_nonneg _) hC) _ pre hlen
  intro pre hpre
  exact weighted_step_le W score category saving q C hq pre (hscore pre)
    (hstep pre hpre)

theorem sum_high_score_words_le (W : List A → ℝ) (score : List A → ℕ)
    (category : List A → A → J) (saving : J → ℕ)
    (N n m : ℕ) (q C : ℝ) (hq : 1 ≤ q) (hC : 0 ≤ C)
    (hW : ∀ pre, 0 ≤ W pre) (hzero : score [] = 0)
    (hscore : ∀ pre a, score (a :: pre) = score pre + saving (category pre a))
    (hstep : ∀ pre, pre.length < N → ∀ j,
      (∑ a, if category pre a = j then W (a :: pre) else 0) ≤
        (C / q ^ saving j) * W pre)
    (hlen : n ≤ N) :
    (∑ a : Fin n → A, if m ≤ score (List.ofFn a).reverse then
      W (List.ofFn a).reverse else 0) ≤
      ((Fintype.card J : ℝ) * C) ^ n * W [] / q ^ m := by
  classical
  have hqpos : 0 < q := lt_of_lt_of_le (by norm_num) hq
  apply (le_div_iff₀ (pow_pos hqpos m)).mpr
  calc
    (∑ a : Fin n → A, if m ≤ score (List.ofFn a).reverse then
        W (List.ofFn a).reverse else 0) * q ^ m ≤
        ∑ a : Fin n → A,
          q ^ score (List.ofFn a).reverse * W (List.ofFn a).reverse := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro a _
      by_cases hs : m ≤ score (List.ofFn a).reverse
      · rw [ite_eq_left hs, mul_comm]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hq hs) (hW _)
      · rw [ite_eq_right hs, zero_mul]
        exact mul_nonneg (pow_nonneg hqpos.le _) (hW _)
    _ ≤ ((Fintype.card J : ℝ) * C) ^ n * W [] := by
      have h := sum_weighted_words_le W score category saving N n q C hqpos hC
        hscore hstep [] (by simpa using hlen)
      simpa only [List.append_nil, hzero, pow_zero, one_mul] using h

theorem sum_reuse_witness_weights_le {D : Type*} [DecidableEq A] [DecidableEq D]
    (G : A → Finset D) (hfour : ∀ a, (G a).card ≤ 4)
    (W : List A → ℝ) (N n m : ℕ) (q C : ℝ) (hq : 1 ≤ q) (hC : 0 ≤ C)
    (hW : ∀ pre, 0 ≤ W pre)
    (hstep : ∀ pre, pre.length < N → ∀ j : ℕ, j ≤ 4 →
      (∑ a, if (G a ∩ pre.toFinset.biUnion G).card = j then W (a :: pre) else 0) ≤
        (C / q ^ reuseSaving j) * W pre)
    (hlen : n ≤ N) :
    (∑ a : Fin n → A, if m ≤ reuseExposureScore G (List.ofFn a).reverse then
      W (List.ofFn a).reverse else 0) ≤ (5 * C) ^ n * W [] / q ^ m := by
  classical
  let category : List A → A → Fin 5 := fun pre a =>
    ⟨(G a ∩ pre.toFinset.biUnion G).card, by
      have h := (Finset.card_le_card (Finset.inter_subset_left :
        G a ∩ pre.toFinset.biUnion G ⊆ G a)).trans (hfour a)
      omega⟩
  have hstep' (pre : List A) (hp : pre.length < N) (j : Fin 5) :
      (∑ a, if category pre a = j then W (a :: pre) else 0) ≤
        (C / q ^ reuseSaving j.val) * W pre := by
    simpa only [category, Fin.ext_iff] using hstep pre hp j.val (by omega)
  have h := sum_high_score_words_le W (reuseExposureScore G) category
    (fun j : Fin 5 => reuseSaving j.val) N n m q C hq hC hW rfl
    (fun _ _ => rfl) (by
      intro pre hp j
      simpa only using hstep' pre hp j) hlen
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using h

end
end Balanced.ReuseSchedule

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_ReuseScheduleAggregation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ReuseSchedule

open scoped BigOperators

theorem schedule_count : (∑ n : Fin 7, (5 : ℝ) ^ n.val) = 19531 := by
  norm_num [Fin.sum_univ_succ]

theorem sum_reweighted_costs_le (A q : ℝ) (hA : 0 ≤ A) (hq : 1 ≤ q) :
    (∑ n : Fin 7, (5 * A) ^ n.val / q ^ 3) ≤
      19531 * (max 1 A) ^ 6 / q ^ 3 := by
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  calc
    _ ≤ ∑ n : Fin 7, (5 : ℝ) ^ n.val * ((max 1 A) ^ 6 / q ^ 3) := by
      apply Finset.sum_le_sum
      intro n _
      have hnum : A ^ n.val ≤ (max 1 A) ^ 6 :=
        (pow_le_pow_left₀ hA (le_max_right _ _) _).trans
          (pow_le_pow_right₀ (le_max_left _ _) (by omega))
      rw [mul_pow, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hnum (le_of_lt (pow_pos hqpos _)))
        (by positivity)
    _ = _ := by rw [← Finset.sum_mul, schedule_count]; ring

theorem sum_length_masses_le (A q : ℝ) (hA : 0 ≤ A) (hq : 1 ≤ q)
    (mass : Fin 7 → ℝ)
    (hmass : ∀ n, mass n ≤ (5 * A) ^ n.val / q ^ 3) :
    (∑ n : Fin 7, mass n) ≤ 19531 * (max 1 A) ^ 6 / q ^ 3 := by
  apply le_trans _ (sum_reweighted_costs_le A q hA hq)
  exact Finset.sum_le_sum (fun n _ => hmass n)

theorem aggregate_constant_pos (A : ℝ) : 0 < 19531 * (max 1 A) ^ 6 := by
  have : 0 < max 1 A := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  positivity

end Balanced.ReuseSchedule

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_ReuseWeightedBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ReuseTower

open scoped BigOperators
noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem reuseBoundConstant_pos (K : ℝ) : 0 < reuseBoundConstant K :=
  ReuseSchedule.aggregate_constant_pos (extensionConstant * K)

theorem sum_weightedWitnessMass_le_of_prefix_extensions (K : ℝ) (hK : 0 ≤ K)
    (p : Point F)
    (hstep : ∀ pre : List (Prescription F), pre.length < 6 →
      ∀ j : ℕ, j ≤ 4 →
      (∑ r : Prescription F, if oldCount pre r = j then
        prefixWeight K p (r :: pre) else 0) ≤
        (extensionConstant * K / (Fintype.card F : ℝ) ^ reuseSaving j) *
          prefixWeight K p pre) :
    (∑ n : Fin 7, weightedWitnessMass K p n.val) ≤
      reuseBoundConstant K / (Fintype.card F : ℝ) ^ 3 := by
  have hq : (1 : ℝ) ≤ Fintype.card F := by
    exact_mod_cast (show 1 ≤ Fintype.card F from Fintype.card_pos)
  have hC : 0 ≤ extensionConstant * K := by
    unfold extensionConstant
    positivity
  apply ReuseSchedule.sum_length_masses_le (extensionConstant * K)
    (Fintype.card F) hC hq (fun n => weightedWitnessMass K p n.val)
  intro n
  have h := ReuseSchedule.sum_reuse_witness_weights_le
    prescriptionGenerators prescriptionGenerators_card_le_four
    (prefixWeight K p) 6 n.val 3 (Fintype.card F) (extensionConstant * K) hq hC
    (prefixWeight_nonneg K hK p) ?_ (by omega)
  · simpa only [weightedWitnessMass, prefixWeight_nil, mul_one] using h
  intro pre hp j hj
  simp_rw [category_cutoff_weight_eq]
  exact hstep pre hp j hj

end
end Balanced.ReuseTower

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_PencilReuseEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open scoped BigOperators
noncomputable section
open scoped Classical

universe u

theorem pencilReuse_proof_oai : Local.PencilReuseResult.{u} := by
  intro K hK
  refine ⟨ReuseTower.reuseBoundConstant K, ReuseTower.reuseBoundConstant_pos K,
    0, ?_⟩
  intro F _ _ _ _ Q w hw p
  have hsum := ReuseTower.sum_weightedWitnessMass_le_of_prefix_extensions
    K hK.le p (fun pre hpre j hj =>
      ReuseTower.prefixWeight_extension_le K hK.le p pre hpre j hj)
  have hselected := ReusePrescription.selected_reuse_le_reversed_function_sum
    Q w K hK.le hw p
  apply hselected.trans
  calc
    (∑ n ∈ Finset.range 7, ∑ t : Fin n → ReuseTower.Prescription F,
        if 3 ≤ ReuseTower.prefixScore (List.ofFn t).reverse
        then ReuseTower.prefixWeight K p (List.ofFn t).reverse else 0) =
        ∑ n ∈ Finset.range 7, ReuseTower.weightedWitnessMass K p n := by
      apply Finset.sum_congr rfl
      intro n hn
      unfold ReuseTower.weightedWitnessMass
      apply Finset.sum_congr rfl
      intro t ht
      exact (ReuseTower.score_cutoff_weight_eq K p (List.ofFn t).reverse 3).symm
    _ = ∑ n : Fin 7, ReuseTower.weightedWitnessMass K p n.val := by
      rw [Fin.sum_univ_eq_sum_range]
    _ ≤ _ := hsum

end
end Balanced

end OAI
end

theorem solution.{u} : type_of% @OAI.Balanced.pencilReuse_proof_oai.{u} := @OAI.Balanced.pencilReuse_proof_oai.{u}
