-- Prove2me | solution 1 for OAI.UniformKServer.ControllerBound.suffix
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:00:25.862258+00:00
-- url     : https://prove2.me/submissions/5055699a-a9bd-46b9-8ea2-96cefd4c9299

import Mathlib
import Definitions.Def_UniformKServer
import Definitions.Def_Q220Uk008
import Theorems.Thm_OAI_UniformKServer_ControllerBound_groups

section
-- module Solutions.Q220_UK.UniformKServer_BitPaths
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.BitSampling

theorem mean_const {A : Type*} [Fintype A] [Nonempty A] (c : ℝ) :
    mean (fun _ : A => c) = c := by
  have hc : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast (Fintype.card_ne_zero (α:=A))
  simp [mean, hc]

end UniformKServer.BitSampling



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_BoundedFilter
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions _root_.OAI.UniformKServer.OffsetParameters.acceptableDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer

private theorem distance_nonneg {n : ℕ} (d : RationalMetric n) (x y : Fin n) :
    (0 : ℝ) ≤ d.distance x y := by exact_mod_cast d.nonneg x y

theorem costAlong_nonneg {n k : ℕ} (d : RationalMetric n)
    (s : Configuration n k) (h : History n k) : 0 ≤ costAlong d s h := by
  induction h generalizing s with
  | nil => rfl
  | cons a h ih =>
    rcases a with ⟨r,j⟩
    exact add_nonneg (distance_nonneg d _ _) (ih _)

end UniformKServer



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawBlockCharge
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions _root_.OAI.UniformKServer.OffsetParameters.acceptableDecidable
attribute [-simp] _root_.OAI.UniformKServer.Fallback.mem_coverers _root_.OAI.UniformKServer.RawBinary.distances_length _root_.OAI.UniformKServer.RawControl.initial_state _root_.OAI.UniformKServer.RawMarks.covers_bits _root_.OAI.UniformKServer.lazyPath_nil_iff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.RawBlockCharge

theorem paid_or_covered {n k : ℕ} (d : RationalMetric n) (δ : ℝ) (_hδ : 0 ≤ δ)
    (hsep : ∀ x y, x ≠ y → δ ≤ (d.distance x y : ℝ))
    (h : History n k) (s : Configuration n k) :
    δ ≤ costAlong d s h ∨ (∀ r ∈ h.map Prod.fst, ∃ j, s j = r) := by
  induction h generalizing s with
  | nil => exact Or.inr (by simp)
  | cons a h ih =>
    rcases a with ⟨r,j⟩
    by_cases hj : s j = r
    · have he : serve s r j = s := by
        unfold serve
        conv_lhs => arg 3; rw [← hj]
        exact Function.update_eq_self _ _
      have hz : (d.distance (s j) r : ℝ) = 0 := by
        rw [hj, (d.eq_zero r r).mpr rfl, Rat.cast_zero]
      rcases ih s with hp | hc
      · exact Or.inl (by simpa only [costAlong, hz, he, zero_add] using hp)
      · right
        intro x hx
        simp only [List.map_cons, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact ⟨j,hj⟩
        · exact hc x hx
    · left
      exact (hsep _ _ hj).trans (le_add_of_nonneg_right (costAlong_nonneg d _ _))

theorem one_block {n k : ℕ} (d : RationalMetric n) (δ : ℝ) (hδ : 0 ≤ δ)
    (hsep : ∀ x y, x ≠ y → δ ≤ (d.distance x y : ℝ))
    (s : Configuration n k) (h : History n k)
    (hc : k < (h.map Prod.fst).toFinset.card) : δ ≤ costAlong d s h := by
  classical
  rcases paid_or_covered d δ hδ hsep h s with hp | hs
  · exact hp
  · have hsub : (h.map Prod.fst).toFinset ⊆ Finset.univ.image s := by
      intro r hr
      obtain ⟨j,hj⟩ := hs r (List.mem_toFinset.mp hr)
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩
    have hn : (h.map Prod.fst).toFinset.card ≤ k := calc
      _ ≤ (Finset.univ.image s).card := Finset.card_le_card hsub
      _ ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_image_le
      _ = k := by simp
    omega

theorem split_history {n k : ℕ} (h : History n k) (w v : List (Fin n))
    (hw : h.map Prod.fst = w++v) :
    ∃ g t, h = g++t ∧ g.map Prod.fst = w ∧ t.map Prod.fst = v := by
  refine ⟨h.take w.length, h.drop w.length, (List.take_append_drop _ _).symm, ?_, ?_⟩
  · rw [List.map_take, hw, List.take_left]
  · rw [List.map_drop, hw, List.drop_left]

theorem tail_blocks {n k : ℕ} (d : RationalMetric n) (δ : ℝ) (hδ : 0 ≤ δ)
    (hsep : ∀ x y, x ≠ y → δ ≤ (d.distance x y : ℝ))
    (blocks : List (List (Fin n))) (hb : ∀ b ∈ blocks, k < b.toFinset.card)
    (tail : List (Fin n)) (s : Configuration n k) (h : History n k)
    (hw : h.map Prod.fst = blocks.flatten ++ tail) :
    (blocks.length : ℝ)*δ ≤ costAlong d s h := by
  induction blocks generalizing s h with
  | nil => simpa only [List.length_nil, Nat.cast_zero, zero_mul] using costAlong_nonneg d s h
  | cons b blocks ih =>
    obtain ⟨g,t,rfl,hg,ht⟩ := split_history h b (blocks.flatten++tail)
      (by simpa only [List.flatten_cons, List.append_assoc] using hw)
    have hgcost := one_block d δ hδ hsep s g (by rw [hg]; exact hb b (by simp))
    have htCost := ih (fun b' hb' => hb b' (by simp [hb'])) (finish s g) t ht
    rw [cost_append]
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith

theorem word_blocks {n k : ℕ} (d : RationalMetric n) (δ : ℝ) (hδ : 0 ≤ δ)
    (hsep : ∀ x y, x ≠ y → δ ≤ (d.distance x y : ℝ))
    (blocks : List (List (Fin n))) (hb : ∀ b ∈ blocks, k < b.toFinset.card)
    (pre tail : List (Fin n)) (s : Configuration n k) (h : History n k)
    (hw : h.map Prod.fst = pre ++ blocks.flatten ++ tail) :
    (blocks.length : ℝ)*δ ≤ costAlong d s h := by
  obtain ⟨g,t,rfl,hg,ht⟩ := split_history h pre (blocks.flatten++tail)
    (by simpa only [List.append_assoc] using hw)
  have hp := tail_blocks d δ hδ hsep blocks hb tail (finish s g) t ht
  rw [cost_append]
  linarith [costAlong_nonneg d s g]

theorem offline_blocks {n k : ℕ} (hk : 0 < k) (d : RationalMetric n)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hsep : ∀ x y, x ≠ y → δ ≤ (d.distance x y : ℝ))
    (blocks : List (List (Fin n))) (hb : ∀ b ∈ blocks, k < b.toFinset.card)
    (pre tail : List (Fin n)) (s : Configuration n k) :
    (blocks.length : ℝ)*δ ≤ offlineCost d s (pre ++ blocks.flatten ++ tail) := by
  apply le_csInf
  · let h : History n k := (pre++blocks.flatten++tail).map (fun r => (r,⟨0,hk⟩))
    refine ⟨costAlong d s h, h, ?_, rfl⟩
    change ((pre++blocks.flatten++tail).map (fun r => (r, (⟨0,hk⟩ : Fin k)))).map Prod.fst = _
    rw [List.map_map]
    exact List.map_id _
  · rintro c ⟨h,hw,rfl⟩
    exact word_blocks d δ hδ hsep blocks hb pre tail s h hw

end UniformKServer.RawBlockCharge


end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawPartition
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions _root_.OAI.UniformKServer.OffsetParameters.acceptableDecidable
attribute [-simp] _root_.OAI.UniformKServer.RawBinary.distances_length _root_.OAI.UniformKServer.RawControl.initial_state _root_.OAI.UniformKServer.RawFallback.nextSeen_bits _root_.OAI.UniformKServer.RawMarks.covers_bits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.RawPartition
open EpochShadow

theorem flatten_pack {n : ℕ} (k : ℕ) (acc w : List (Fin n)) :
    (pack k acc w).flatten = acc++w := by
  induction w generalizing acc with
  | nil => by_cases h : acc = []; simp [pack,h]; simp [pack,h]
  | cons r w ih =>
    simp only [pack]
    split
    · simp only [List.flatten_cons, ih, List.nil_append, List.append_assoc,
        List.singleton_append]
    · simpa only [List.append_assoc, List.singleton_append] using ih (acc++[r])

theorem pack_good {n : ℕ} (k : ℕ) (acc w : List (Fin n))
    (ha : acc.toFinset.card ≤ k) : ∀ b ∈ pack k acc w, GoodBlock k b := by
  induction w generalizing acc with
  | nil =>
    simp only [pack]
    split
    · simp
    · intro b hb
      have he : b = acc := by simpa using hb
      subst b
      have hne : acc ≠ [] := by assumption
      refine ⟨acc.dropLast,acc.getLast hne,(List.dropLast_append_getLast hne).symm,?_⟩
      apply (Finset.card_le_card ?_).trans ha
      intro x hx
      exact List.mem_toFinset.mpr ((List.dropLast_sublist acc).subset (List.mem_toFinset.mp hx))
  | cons r w ih =>
    simp only [pack]
    split
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ⟨acc,r,rfl,ha⟩
      · exact ih [] (by simp) b hb
    · exact ih (acc++[r]) (by omega)

theorem pack_complete {n : ℕ} (k : ℕ) (acc w : List (Fin n)) :
    ∀ b ∈ (pack k acc w).dropLast, k < b.toFinset.card := by
  induction w generalizing acc with
  | nil => by_cases h : acc = []; simp [pack,h]; simp [pack,h]
  | cons r w ih =>
    simp only [pack]
    split
    · rename_i hc
      cases he : pack k [] w with
      | nil => simp
      | cons b bs =>
        simp only [List.dropLast_cons_cons]
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hc
        · apply ih [] a
          simpa only [he] using ha
    · exact ih (acc++[r])

theorem no_endpoint_prefix {n k : ℕ} (seen : Finset (Fin n)) (p q : List (Fin n))
    (hp : (seen ∪ p.toFinset).card ≤ k) :
    blockCount (k:=k) seen (p++q) = blockCount (k:=k) (seen ∪ p.toFinset) q := by
  induction p generalizing seen with
  | nil => simp
  | cons r p ih =>
    have hsub : insert r seen ⊆ seen ∪ (r::p).toFinset := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_union, List.toFinset_cons] at *
      aesop
    have hr : (insert r seen).card ≤ k := (Finset.card_le_card hsub).trans hp
    have he : insert r seen ∪ p.toFinset = seen ∪ (r::p).toFinset := by
      ext x
      simp only [Finset.mem_union, Finset.mem_insert, List.toFinset_cons]
      tauto
    simp only [List.cons_append, blockCount, ite_eq_right (by omega : ¬ k < (insert r seen).card),
      Nat.zero_add, bookStep]
    rw [ih (insert r seen) (by rwa [he]), he]

theorem good_count {n k : ℕ} {b : List (Fin n)} (hb : GoodBlock k b) :
    blockCount (k:=k) ∅ b ≤ 1 := by
  obtain ⟨p,r,rfl,hp⟩ := hb
  rw [no_endpoint_prefix ∅ p [r] (by simpa using hp)]
  simp only [Finset.empty_union, blockCount, bookStep]
  split
  · simp
  · split <;> simp_all

theorem complete_append {n k : ℕ} {b : List (Fin n)} (hb : GoodBlock k b)
    (hc : k < b.toFinset.card) (w : List (Fin n)) :
    blockCount (k:=k) ∅ (b++w) = 1 + blockCount (k:=k) ∅ w := by
  obtain ⟨p,r,rfl,hp⟩ := hb
  rw [List.append_assoc, no_endpoint_prefix ∅ p ([r]++w) (by simpa using hp)]
  have hr : k < (insert r p.toFinset).card := by simpa using hc
  simp [blockCount, bookStep, hr]

theorem block_count_bound {n k : ℕ} (bs : List (List (Fin n)))
    (hg : ∀ b ∈ bs, GoodBlock k b)
    (hc : ∀ b ∈ bs.dropLast, k < b.toFinset.card) :
    blockCount (k:=k) ∅ bs.flatten ≤ bs.length := by
  induction bs with
  | nil => simp [blockCount]
  | cons b bs ih =>
    cases bs with
    | nil => simpa using good_count (hg b (by simp))
    | cons c cs =>
      have hb : k < b.toFinset.card := hc b (by simp)
      have ht := ih (fun a ha => hg a (by simp_all)) (by
        intro a ha
        exact hc a (by simp_all))
      simpa only [List.flatten_cons, complete_append (hg b (by simp)) hb,
        List.length_cons, Nat.add_comm] using Nat.add_le_add_left ht 1

theorem completed_charge {n k : ℕ} (hk : 0 < k) (d : RationalMetric n)
    (δ : ℝ) (hδ : 0 ≤ δ) (hsep : ∀ x y, x ≠ y → δ ≤ (d.distance x y : ℝ))
    (pre w : List (Fin n)) (s : Configuration n k) :
    (((pack k [] w).length - 1 : ℕ) : ℝ)*δ ≤ offlineCost d s (pre++w) := by
  let bs := pack k [] w
  by_cases hnil : bs = []
  · have hw : w = [] := by
      have hh := flatten_pack k [] w
      change bs.flatten = []++w at hh
      simpa [hnil] using hh.symm
    subst w
    simp only [pack, ↓reduceIte, List.length_nil, Nat.zero_sub, Nat.cast_zero, zero_mul]
    rw [List.append_nil]
    apply le_csInf
    · refine ⟨costAlong d s (pre.map (fun r => (r,⟨0,hk⟩))),_,?_,rfl⟩
      simp only [List.map_map]
      exact List.map_id _
    · rintro c ⟨h,_,rfl⟩
      exact UniformKServer.costAlong_nonneg d s h
  · have hsplit : bs.dropLast ++ [bs.getLast hnil] = bs := List.dropLast_append_getLast hnil
    have hf : bs.dropLast.flatten ++ bs.getLast hnil = w := by
      have hh := congrArg List.flatten hsplit
      simpa [bs, flatten_pack] using hh
    have hc := RawBlockCharge.offline_blocks hk d δ hδ hsep bs.dropLast
      (pack_complete k [] w) pre (bs.getLast hnil) s
    rw [List.append_assoc, hf] at hc
    simpa only [List.length_dropLast] using hc

end UniformKServer.RawPartition


end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_EpochPartition
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions _root_.OAI.UniformKServer.OffsetParameters.acceptableDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.EpochPartition
open RawPartition EpochShadow

theorem chunks_flatten {α : Type} (R : ℕ) (hR : 0 < R) (bs : List α) :
    (chunks R hR bs).flatten = bs := by
  induction bs using chunks.induct R hR with
  | case1 => simp [chunks]
  | case2 b bs ih =>
    rw [chunks, List.flatten_cons, ih, List.take_append_drop]

theorem chunks_nil {α : Type} (R : ℕ) (hR : 0 < R) (bs : List α) :
    chunks R hR bs = [] ↔ bs = [] := by
  cases bs <;> simp [chunks]

theorem sublist_dropLast {α : Type} {bs cs : List α} (h : bs.Sublist cs) :
    bs.dropLast.Sublist cs.dropLast := by
  induction h with
  | slnil => simp
  | @cons l₁ l₂ a h ih =>
    cases l₂ with
    | nil => simpa using ih
    | cons c cs =>
      simpa only [List.dropLast_cons_cons] using List.Sublist.cons a ih
  | @cons_cons l₁ l₂ a h ih =>
    cases l₁ with
    | nil => simp
    | cons b bs =>
      cases l₂ with
      | nil => have hh := h.length_le; simp at hh
      | cons c cs => simpa only [List.dropLast_cons_cons] using List.Sublist.cons_cons a ih

theorem chunks_sublist {α : Type} (R : ℕ) (hR : 0 < R) (bs : List α) :
    ∀ c ∈ chunks R hR bs, c.Sublist bs ∧ c.length ≤ R := by
  induction bs using chunks.induct R hR with
  | case1 => simp [chunks]
  | case2 b bs ih =>
    rw [chunks]
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨List.take_sublist _ _, by simp [List.length_take]⟩
    · obtain ⟨hs,hl⟩ := ih c hc
      exact ⟨hs.trans (List.drop_sublist _ _),hl⟩

theorem chunks_number {α : Type} (R : ℕ) (hR : 0 < R) (bs : List α) :
    ((chunks R hR bs).length - 1)*R ≤ bs.length - 1 := by
  induction bs using chunks.induct R hR with
  | case1 => simp [chunks]
  | case2 b bs ih =>
    rw [chunks]
    simp only [List.length_cons, Nat.add_sub_cancel]
    by_cases he : (b::bs).drop R = []
    · rw [he, chunks]
      simp
    · have hd : 0 < ((b::bs).drop R).length := List.length_pos_iff.mpr he
      have hn : 0 < (chunks R hR ((b::bs).drop R)).length :=
        List.length_pos_iff.mpr (mt (chunks_nil R hR _).mp he)
      have hmul : (chunks R hR ((b::bs).drop R)).length * R =
          ((chunks R hR ((b::bs).drop R)).length - 1)*R + R := by
        conv_lhs => rw [← Nat.sub_add_cancel hn]
        simp [Nat.add_mul]
      rw [hmul]
      have hlen : R + ((b::bs).drop R).length = (b::bs).length := by
        simp only [List.length_drop] at *
        omega
      simp only [List.length_cons] at hlen
      omega

theorem epochs_flatten {n : ℕ} (k R : ℕ) (hR : 0 < R) (w : List (Fin n)) :
    (epochs k R hR w).flatten = w := by
  unfold epochs
  rw [← List.flatten_flatten, chunks_flatten, flatten_pack]
  rfl

theorem epoch_blocks {n : ℕ} (k R : ℕ) (hR : 0 < R) (w : List (Fin n)) :
    ∀ e ∈ epochs k R hR w, blockCount (k:=k) ∅ e ≤ R := by
  intro e he
  obtain ⟨bs,hbs,rfl⟩ := List.mem_map.mp he
  obtain ⟨hs,hl⟩ := chunks_sublist R hR (pack k [] w) bs hbs
  apply (block_count_bound bs ?_ ?_).trans hl
  · intro b hb
    exact pack_good k [] w (by simp) b (hs.subset hb)
  · intro b hb
    exact pack_complete k [] w b ((sublist_dropLast hs).subset hb)

theorem epoch_charge {n k : ℕ} (hk : 0 < k) (d : RationalMetric n)
    (R : ℕ) (hR : 0 < R) (δ : ℝ) (hδ : 0 ≤ δ)
    (hsep : ∀ x y, x ≠ y → δ ≤ (d.distance x y : ℝ))
    (pre w : List (Fin n)) (s : Configuration n k) :
    (((epochs k R hR w).length - 1 : ℕ) : ℝ)*R*δ ≤ offlineCost d s (pre++w) := by
  have hn := chunks_number R hR (pack k [] w)
  have hn' : (((chunks R hR (pack k [] w)).length - 1 : ℕ) : ℝ)*R ≤
      (((pack k [] w).length - 1 : ℕ) : ℝ) := by exact_mod_cast hn
  have hp := mul_le_mul_of_nonneg_right hn' hδ
  have hc := completed_charge hk d δ hδ hsep pre w s
  simpa only [epochs, List.length_map] using hp.trans hc

end UniformKServer.EpochPartition




end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_BoundaryPartition
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                        
section

namespace UniformKServer.BoundaryPartition
open EpochShadow RawPartition EpochPartition

theorem join_last {A : Type} (R c : ℕ) (acc b : List A) (hb : b≠[]) :
    join R c acc [b]=[acc++b] := by
  have hab : acc++b≠[] := by simp [hb]
  simp [join,hab]

theorem split_join {n : ℕ} (k R : ℕ) (c : ℕ) (pre p w : List (Fin n)) :
    split k R p.toFinset c (pre++p) w = join R c pre (pack k p w) := by
  induction w generalizing c pre p with
  | nil =>
    by_cases hp : p=[]
    · simp [split,pack,join,hp]
    · rw [pack,ite_eq_right hp,join_last R c pre p hp]
      have hh : pre++p≠[] := by simp [hp]
      simp [split,hh]
  | cons r w ih =>
    have he : (p++[r]).toFinset=insert r p.toFinset := by ext x;simp
    by_cases hend : k<(insert r p.toFinset).card
    · simp only [split,pack,he,ite_eq_left hend]
      by_cases hc : c+1=R
      · simp only [ite_eq_left hc,join]
        rw [←ih 0 [] []]
        simp
      · simp only [ite_eq_right hc,join]
        rw [←ih (c+1) (pre++(p++[r])) []]
        simp [List.append_assoc]
    · simp only [split,pack,he,ite_eq_right hend]
      simpa only [he,List.append_assoc] using ih c pre (p++[r])

theorem join_formula {A : Type} (R : ℕ) (c : ℕ) (hc : c<R) (acc : List A)
    (bs : List (List A)) (hbs : bs≠[]) (hb : ∀b∈bs,b≠[]) :
    join R c acc bs = (acc++(bs.take (R-c)).flatten)::join R 0 [] (bs.drop (R-c)) := by
  induction bs generalizing c acc with
  | nil => contradiction
  | cons b bs ih =>
    by_cases he : c+1=R
    · have hr : R-c=1 := by omega
      simp [join,he,hr]
    · have hr : R-c=(R-(c+1))+1 := by omega
      have hc' : c+1<R := by omega
      cases bs with
      | nil =>
        have hbn := hb b (by simp)
        rw [join_last R c acc b hbn]
        simp [hr,join]
      | cons b' bs =>
        have htail : ∀a∈b'::bs,a≠[] := fun a ha => hb a (by simp_all)
        rw [join,ite_eq_right he,ih (c+1) hc' (acc++b) (by simp) htail]
        simp only [hr,List.take_succ_cons,List.drop_succ_cons,List.flatten_cons,List.append_assoc]

theorem join_chunks {A : Type} (R : ℕ) (hR : 0<R) (bs : List (List A))
    (hb : ∀b∈bs,b≠[]) :
    join R 0 [] bs = (chunks R hR bs).map List.flatten := by
  induction bs using chunks.induct R hR with
  | case1 => simp [join,chunks]
  | case2 b bs ih =>
    rw [join_formula R 0 hR [] (b::bs) (by simp) hb]
    simp only [Nat.sub_zero,List.nil_append,chunks,List.map_cons]
    congr 1
    exact ih (fun a ha => hb a (List.mem_of_mem_drop ha))

theorem streamed_epochs {n : ℕ} (k R : ℕ) (hR : 0<R) (w : List (Fin n)) :
    split k R ∅ 0 [] w = epochs k R hR w := by
  have hh := split_join k R 0 [] [] w
  simp only [List.toFinset_nil,List.append_nil] at hh
  rw [hh,join_chunks R hR]
  · rfl
  · intro b hb
    obtain ⟨p,r,he,-⟩ := pack_good k [] w (by simp) b hb
    simp [he]

end UniformKServer.BoundaryPartition

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_EpochCut
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
attribute [-simp] _root_.OAI.UniformKServer.RawFallback.nextSeen_bits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                               
section

namespace UniformKServer.EpochCut
open EpochShadow BoundaryPartition

theorem cut_append {n : ℕ} (k R : ℕ) (seen : Finset (Fin n)) (c : ℕ) (w : List (Fin n)) :
    (cut k R seen c w).1++(cut k R seen c w).2=w := by
  induction w generalizing seen c with
  | nil => rfl
  | cons r w ih =>
    by_cases h : k<(insert r seen).card ∧ c+1=R
    · simp only [cut,ite_eq_left h,List.singleton_append]
    · simpa only [cut,ite_eq_right h,List.cons_append,List.cons.injEq,true_and] using
        ih (bookStep seen r) (c+if k<(insert r seen).card then 1 else 0)

theorem cut_nonempty {n : ℕ} (k R : ℕ) (seen : Finset (Fin n)) (c : ℕ)
    (r : Fin n) (w : List (Fin n)) : (cut k R seen c (r::w)).1≠[] := by
  rw [cut]
  split_ifs <;> simp

theorem tail_shorter {n : ℕ} (k R : ℕ) (seen : Finset (Fin n)) (c : ℕ)
    (r : Fin n) (w : List (Fin n)) : (cut k R seen c (r::w)).2.length<(r::w).length := by
  have hh := congrArg List.length (cut_append k R seen c (r::w))
  have hn := List.length_pos_iff.mpr (cut_nonempty k R seen c r w)
  simp only [List.length_append] at hh
  omega

theorem split_cut {n : ℕ} (k R : ℕ) (seen : Finset (Fin n)) (c : ℕ)
    (acc w : List (Fin n)) (hw : w≠[]) :
    split k R seen c acc w =
      (acc++(cut k R seen c w).1)::split k R ∅ 0 [] (cut k R seen c w).2 := by
  induction w generalizing seen c acc with
  | nil => contradiction
  | cons r w ih =>
    by_cases he : k<(insert r seen).card
    · by_cases hc : c+1=R
      · simp [cut,split,he,hc]
      · simp only [cut,he,hc,and_false,ite_false, if_false,split,ite_true, if_true,bookStep]
        cases w with
        | nil => simp [split,cut]
        | cons r' w =>
          simpa only [List.append_assoc,List.singleton_append] using ih ∅ (c+1) (acc++[r]) (by simp)
    · simp only [cut,he,false_and,ite_false, if_false,split,bookStep,Nat.add_zero]
      cases w with
      | nil => simp [split,cut]
      | cons r' w =>
        simpa only [List.append_assoc,List.singleton_append] using ih (insert r seen) c (acc++[r]) (by simp)

end UniformKServer.EpochCut

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TapeController
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions _root_.OAI.UniformKServer.OffsetParameters.acceptableDecidable
attribute [-simp] _root_.OAI.UniformKServer.RawBinary.distances_length _root_.OAI.UniformKServer.RawControl.initial_state _root_.OAI.UniformKServer.RawFallback.nextSeen_bits _root_.OAI.UniformKServer.RawFilter.allCover_state _root_.OAI.UniformKServer.RawFilter.births_entry _root_.OAI.UniformKServer.RawFilter.cover_entry _root_.OAI.UniformKServer.RawGlobal.boundary_state _root_.OAI.UniformKServer.RawGlobal.chosen_state _root_.OAI.UniformKServer.RawGlobal.initial_state _root_.OAI.UniformKServer.RawMarks.covers_bits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                     
section

namespace UniformKServer.TapeController
open EpochShadow EpochExpectation

theorem step_seen {n k : ℕ} (hk : 0<k) (M : ℕ) (T : Selector n k)
    (s : EpochControl.State n k) (r : Fin n) :
    (EpochControl.step hk M T s r).seen=bookStep (k:=k) s.seen r := by
  unfold EpochControl.step
  split_ifs with ht hc
  · simp only [EpochControl.asRaw,Fallback.rawStep,Fallback.isEndpoint,bookStep]
    split_ifs with h <;> simp [h]
  · rfl
  · rfl

theorem step_loaded {n k M R b : ℕ} (hk : 0<k) (hR : 0<R) (u : Configuration n k)
    (N : BState n k → Fin n → Fin k → ℕ) (hN : ∀s r,∑j,N s r j=2^b)
    (s : State n k M R b) (r : Fin n) (coins fresh : Tape k M b) :
    step hk hR u N hN (loaded s coins) r fresh=step hk hR u N hN (loaded s coins) r coins := by
  unfold step
  split_ifs <;> rfl

theorem loaded_cons {n k M R b : ℕ} (hk : 0<k) (hR : 0<R) (d : RationalMetric n)
    (u : Configuration n k) (N : BState n k → Fin n → Fin k → ℕ) (hN : ∀s r,∑j,N s r j=2^b)
    (z : State n k M R b) (s : Configuration n k) (r : Fin n) (w : List (Fin n))
    (coins : Tape k M b) :
    expected hk hR d u N hN (loaded z coins) s (r::w)=
      (d.distance (s (choose hk N hN (loaded z coins) r coins)) r : ℝ)+
        expected hk hR d u N hN (step hk hR u N hN (loaded z coins) r coins)
          (serve s r (choose hk N hN (loaded z coins) r coins)) w := by
  rw [expected]
  have he : ∀fresh,choose hk N hN (loaded z coins) r fresh=
      choose hk N hN (loaded z coins) r coins := fun _ => rfl
  simp_rw [he,step_loaded]
  exact BitSampling.mean_const (A:=Tape k M b) _

theorem fresh_mean {n k M R b : ℕ} (hk : 0<k) (hR : 0<R) (d : RationalMetric n)
    (u : Configuration n k) (N : BState n k → Fin n → Fin k → ℕ) (hN : ∀s r,∑j,N s r j=2^b)
    (z : State n k M R b) (hz : z.tape=none) (s : Configuration n k) (w : List (Fin n)) :
    expected hk hR d u N hN z s w=
      BitSampling.mean (fun coins : Tape k M b => expected hk hR d u N hN (loaded z coins) s w) := by
  cases w with
  | nil => simp [expected,BitSampling.mean_const]
  | cons r w =>
    rw [expected]
    congr 1
    funext coins
    rw [loaded_cons]
    have hl : choose hk N hN z r coins=choose hk N hN (loaded z coins) r coins := by
      simp [choose,chosen,loaded,hz]
    rw [hl]
    congr 2
    have hb : boundary (loaded z coins) r=boundary z r := rfl
    by_cases h : boundary z r
    · simp only [step,hb,dite_eq_left h]
    · have hn : ¬boundary (loaded z coins) r := h
      simp only [step,dite_eq_right h,dite_eq_right hn]
      simp only [loaded,chosen,hz,Option.getD_none,Option.getD_some]
      rfl

end UniformKServer.TapeController

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ControllerEpoch
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions _root_.OAI.UniformKServer.OffsetParameters.acceptableDecidable
attribute [-simp] _root_.OAI.UniformKServer.RawBinary.distances_length _root_.OAI.UniformKServer.RawControl.initial_state _root_.OAI.UniformKServer.RawFallback.nextSeen_bits _root_.OAI.UniformKServer.RawGlobal.boundary_state _root_.OAI.UniformKServer.RawGlobal.chosen_state _root_.OAI.UniformKServer.RawGlobal.initial_state _root_.OAI.UniformKServer.RawMarks.covers_bits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                      
section

namespace UniformKServer.TapeController
open EpochShadow EpochExpectation EpochCut

variable {n k M R b : ℕ} (hk : 0<k) (hR : 0<R) (d : RationalMetric n)
  (u : Configuration n k) (N : BState n k → Fin n → Fin k → ℕ)
  (hN : ∀s r,∑j,N s r j=2^b)

/-- Deterministic evolution under the already loaded epoch tape, up to the next
raw-block boundary. No future requests are needed by the controller. -/
theorem cut_expected (z : State n k M R b) (s : Configuration n k)
    (coins : Tape k M b) (w : List (Fin n)) :
    let parts := cut k R z.localState.val.seen z.completed.val w
    let g := EpochControl.runTrace hk M (selector N hN (extend coins)) z.localState.val parts.1
    expected hk hR d u N hN (loaded z coins) s w = costAlong d s g+
      expected hk hR d u N hN (initial (M:=M) hR u) (finish s g) parts.2 := by
  induction w generalizing z s with
  | nil => simp [cut,EpochControl.runTrace,costAlong,expected]
  | cons r w ih =>
    dsimp only
    rw [loaded_cons]
    have hl : choose hk N hN (loaded z coins) r coins=
      EpochControl.label hk (selector N hN (extend coins)) z.localState.val r := rfl
    rw [hl]
    by_cases hb : boundary z r
    · have hb' : boundary (loaded z coins) r := hb
      simp only [cut,show k<(insert r z.localState.val.seen).card ∧ z.completed.val+1=R from hb,
        ite_eq_left,step,dite_eq_left hb']
      simp [EpochControl.runTrace,costAlong,finish]
    · have hb' : ¬boundary (loaded z coins) r := hb
      let z' := step hk hR u N hN (loaded z coins) r coins
      have hloc : z'.localState.val=EpochControl.step hk M (selector N hN (extend coins)) z.localState.val r := by
        simp only [z',step,dite_eq_right hb']
        rfl
      have hseen : z'.localState.val.seen=bookStep (k:=k) z.localState.val.seen r := by
        rw [hloc,step_seen]
      have hcomp : z'.completed.val=z.completed.val+if k<(insert r z.localState.val.seen).card then 1 else 0 := by
        simp only [z',step,dite_eq_right hb']
        rfl
      have hload : loaded z' coins=z' := by
        simp only [z',step,dite_eq_right hb']
        rfl
      have hh := ih z' (serve s r (EpochControl.label hk (selector N hN (extend coins)) z.localState.val r))
      dsimp only at hh
      rw [hload,hseen,hcomp,hloc] at hh
      simp only [cut,show ¬(k<(insert r z.localState.val.seen).card ∧ z.completed.val+1=R) from hb,ite_false, if_false,EpochControl.runTrace,costAlong,finish]
      change _+expected hk hR d u N hN z' _ w=_
      rw [hh]
      simp only [add_assoc]

end UniformKServer.TapeController

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ControllerGroups
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions _root_.OAI.UniformKServer.OffsetParameters.acceptableDecidable
attribute [-simp] _root_.OAI.UniformKServer.RawBinary.distances_length _root_.OAI.UniformKServer.RawControl.initial_state _root_.OAI.UniformKServer.RawGlobal.boundary_state _root_.OAI.UniformKServer.RawGlobal.chosen_state _root_.OAI.UniformKServer.RawGlobal.initial_state _root_.OAI.UniformKServer.RawMarks.covers_bits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                       
section

namespace UniformKServer.TapeController
open EpochShadow EpochExpectation EpochCut BoundaryPartition

variable {n k M R b : ℕ} (hk : 0<k) (hR : 0<R) (d : RationalMetric n)
  (u : Configuration n k) (N : BState n k → Fin n → Fin k → ℕ)
  (hN : ∀s r,∑j,N s r j=2^b)

theorem expected_groups (s : Configuration n k) (w : List (Fin n)) :
    expected hk hR d u N hN (initial (M:=M) hR u) s w=
      groupExpected (M:=M) hk d u N hN s (split k R ∅ 0 [] w) := by
  induction w using (measure List.length).wf.induction generalizing s with
  | _ w ih =>
    cases w with
    | nil => simp [expected,split,groupExpected]
    | cons r w =>
      rw [split_cut k R ∅ 0 [] (r::w) (by simp),List.nil_append]
      rw [fresh_mean hk hR d u N hN (initial (M:=M) hR u) rfl]
      rw [groupExpected]
      apply congrArg BitSampling.mean
      funext coins
      rw [cut_expected hk hR d u N hN]
      congr 1
      exact ih _ (tail_shorter k R ∅ 0 r w) _

theorem expected_epochs (s : Configuration n k) (w : List (Fin n)) :
    expected hk hR d u N hN (initial (M:=M) hR u) s w=
      groupExpected (M:=M) hk d u N hN s (EpochPartition.epochs k R hR w) := by
  rw [expected_groups,streamed_epochs]

end UniformKServer.TapeController

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_OffsetSuffix
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions _root_.OAI.UniformKServer.OffsetParameters.acceptableDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                   
section

namespace UniformKServer.OffsetSuffix
open EffectiveLP EpochShadow EpochPartition

theorem cost_nonneg {n k : ℕ} (d : RationalMetric n) (s : Configuration n k) (h : History n k) :
    0 ≤ costAlong d s h := by
  induction h generalizing s with
  | nil => rfl
  | cons x h ih => exact add_nonneg (by exact_mod_cast d.nonneg (s x.2) x.1) (ih _)


end UniformKServer.OffsetSuffix

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ControllerBound
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions _root_.OAI.UniformKServer.OffsetParameters.acceptableDecidable
attribute [-simp] _root_.OAI.UniformKServer.RawBinary.distances_length _root_.OAI.UniformKServer.RawControl.initial_state _root_.OAI.UniformKServer.RawGlobal.chosen_state _root_.OAI.UniformKServer.RawGlobal.initial_state _root_.OAI.UniformKServer.RawMarks.covers_bits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                      
section

namespace UniformKServer.ControllerBound
open EpochShadow EpochExpectation EpochPartition TapeController
variable {n k b M R : ℕ} [NeZero k] (hk2 : 2≤k) (d : RationalMetric n)
  (u : Configuration n k) (hu : Function.Injective u)
  (N : BState n k→Fin n→Fin k→ℕ) (hN : ∀s r,∑j,N s r j=2^b)
  (hLazy : ∀s r j,(∃i,s.2 i=r)→s.2 j≠r→N s r j=0)
  (D δ A E : ℝ) (hD : 0≤D) (hδ : 0≤δ) (hA : 0≤A)
  (hdiam : ∀x y,(d.distance x y:ℝ)≤D)
  (hsep : ∀x y,x≠y→δ≤(d.distance x y:ℝ))
  (hcap : R*(k+1)*D≤(M+1)*δ)
  (hTable : ∀w : List (Fin n),w.length≤horizon k M→
    BitSampling.mean (BitSampling.runCost N hN next (charge d) ([],u) w)≤
      A*offlineCost d u w+E+D)

include hk2 hu hLazy hD hδ hA hdiam hsep hcap hTable in
theorem suffix_oai (hR : 0<R) (hE : 0≤E)
    (hpay : (2*A+1)*k*D+2*E+2*D≤(2*A+4)*R*δ)
    (pre w : List (Fin n)) (original actual : Configuration n k) :
    TapeController.expected (NeZero.pos k) hR d u N hN (TapeController.initial (M:=M) hR u) actual w≤
      (4*A+4)*offlineCost d original (pre++w)+((2*A+1)*k*D+2*E+2*D) := by
  rw [expected_epochs]
  let K : ℝ := (2*A+1)*k*D+2*E+2*D
  have hK : 0≤K := by dsimp [K] <;> positivity
  obtain ⟨g,hg,hcost⟩:=OfflineDynamic.optRat_attained d original (pre++w)
  rw [←OfflineDynamic.offline_eq_optRat] at hcost
  obtain ⟨gp,gw,rfl,hgp,hgw⟩:=RawBlockCharge.split_history g pre w hg
  have hcostw : costAlong d (finish original gp) gw≤offlineCost d original (pre++w) := by
    rw [←hcost,RawBlockCharge.cost_append]
    exact le_add_of_nonneg_left (OffsetSuffix.cost_nonneg d original gp)
  have he:=groups hk2 d u hu N hN hLazy D δ A E hD hδ hA hdiam hsep hcap hTable
    (epochs k R hR w) (epoch_blocks k R hR w) actual (finish original gp) gw
    (by rw [epochs_flatten];exact hgw)
  have hc:=epoch_charge (NeZero.pos k) d R hR δ hδ hsep pre w original
  have hc' : (((epochs k R hR w).length-1:ℕ):ℝ)*K≤(2*A+4)*offlineCost d original (pre++w) := by
    have hh:=mul_le_mul_of_nonneg_left hpay
      (show (0:ℝ)≤(((epochs k R hR w).length-1:ℕ):ℝ) by positivity)
    have ht:=mul_le_mul_of_nonneg_left hc (show 0≤2*A+4 by positivity)
    dsimp [K]
    nlinarith only [hh,ht]
  have hn : (epochs k R hR w).length≤(epochs k R hR w).length-1+1 := by omega
  have hn' : ((epochs k R hR w).length:ℝ)≤(((epochs k R hR w).length-1:ℕ):ℝ)+1 := by exact_mod_cast hn
  have hcount:=mul_le_mul_of_nonneg_left hn' hK
  have hcompare:=mul_le_mul_of_nonneg_left hcostw (show 0≤2*A by positivity)
  change groupExpected (M:=M) (NeZero.pos k) d u N hN actual _≤(4*A+4)*offlineCost d original (pre++w)+K
  change groupExpected (M:=M) (NeZero.pos k) d u N hN actual _≤
    2*A*costAlong d (finish original gp) gw+K*(epochs k R hR w).length at he
  nlinarith only [he,hcount,hc',hcompare]

end UniformKServer.ControllerBound

end


end

end OAI
end

theorem solution : type_of% @OAI.UniformKServer.ControllerBound.suffix_oai := @OAI.UniformKServer.ControllerBound.suffix_oai
