-- Prove2me | solution 1 for OAI.TreeEdit.cycle_charging
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:41:03.439672+00:00
-- url     : https://prove2.me/submissions/3c2178ce-1ec7-494d-b2f3-907749f38691

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/CycleCharging.lean:L161-L206
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.cycle_charging. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison
import Theorems.Thm_OAI_TreeEdit_card_block_fiber

-- ---- from OAI.Combinatorics.TreeEdit.Alignments ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

namespace TreeEdit

universe u

variable {α : Type u} {x y z : List α}

namespace Alignment

variable {n : ℕ}

end Alignment

theorem mem_indexSpan {N L : ℕ} (f : Fin N ↪o Fin L) {s : Finset (Fin N)}
    {i : Fin N} (hi : i ∈ s) : f i ∈ indexSpan f s := by
  have hs : s.Nonempty := ⟨i, hi⟩
  simp only [indexSpan, dite_eq_left hs, Finset.mem_Icc]
  exact ⟨f.monotone (s.min'_le i hi), f.monotone (s.le_max' i hi)⟩

theorem card_le_indexSpan {N L : ℕ} (f : Fin N ↪o Fin L) (s : Finset (Fin N)) :
    s.card ≤ (indexSpan f s).card := by
  exact Finset.card_le_card_of_injOn f (fun _ hi => mem_indexSpan f hi) f.injective.injOn

theorem indexSpan_disjoint {N L K : ℕ} (f : Fin N ↪o Fin L)
    (key : Fin N → Fin K) (hk : Monotone key) {a b : Fin K} (hab : a ≠ b) :
    Disjoint (indexSpan f (Finset.univ.filter (fun i => key i = a)))
      (indexSpan f (Finset.univ.filter (fun i => key i = b))) := by
  classical
  let sa := Finset.univ.filter (fun i => key i = a)
  let sb := Finset.univ.filter (fun i => key i = b)
  change Disjoint (indexSpan f sa) (indexSpan f sb)
  by_cases ha : sa.Nonempty
  · by_cases hb : sb.Nonempty
    · have hamin : key (sa.min' ha) = a :=
        (Finset.mem_filter.mp (sa.min'_mem ha)).2
      have hamax : key (sa.max' ha) = a :=
        (Finset.mem_filter.mp (sa.max'_mem ha)).2
      have hbmin : key (sb.min' hb) = b :=
        (Finset.mem_filter.mp (sb.min'_mem hb)).2
      have hbmax : key (sb.max' hb) = b :=
        (Finset.mem_filter.mp (sb.max'_mem hb)).2
      refine Finset.disjoint_left.mpr ?_
      intro p hp hq
      simp only [indexSpan, dite_eq_left ha, dite_eq_left hb, Finset.mem_Icc] at hp hq
      rcases lt_or_gt_of_ne hab with hab | hba
      · have hh : sa.max' ha < sb.min' hb := by
          by_contra hn
          have := hk (le_of_not_gt hn)
          rw [hbmin, hamax] at this
          exact (not_le_of_gt hab) this
        exact (not_le_of_gt (f.strictMono hh)) (hq.1.trans hp.2)
      · have hh : sb.max' hb < sa.min' ha := by
          by_contra hn
          have := hk (le_of_not_gt hn)
          rw [hamin, hbmax] at this
          exact (not_le_of_gt hba) this
        exact (not_le_of_gt (f.strictMono hh)) (hp.1.trans hq.2)
    · simp [indexSpan, hb]
  · simp [indexSpan, ha]

theorem sum_span_card_le {N L K : ℕ} (f : Fin N ↪o Fin L)
    (key : Fin N → Fin K) (hk : Monotone key) :
    (∑ k : Fin K, (indexSpan f (Finset.univ.filter (fun i => key i = k))).card) ≤ L := by
  have hd : ((Finset.univ : Finset (Fin K)) : Set (Fin K)).PairwiseDisjoint
      (fun k => indexSpan f (Finset.univ.filter (fun i => key i = k))) := by
    intro a _ b _ hab
    exact indexSpan_disjoint f key hk hab
  rw [← Finset.card_biUnion hd]
  simpa using Finset.card_le_univ
    (Finset.univ.biUnion (fun k => indexSpan f (Finset.univ.filter (fun i => key i = k))))

theorem sum_span_gaps_le {N L K : ℕ} (f : Fin N ↪o Fin L)
    (key : Fin N → Fin K) (hk : Monotone key) :
    (∑ k : Fin K, ((indexSpan f (Finset.univ.filter (fun i => key i = k))).card -
      (Finset.univ.filter (fun i => key i = k)).card)) ≤ L - N := by
  rw [Finset.sum_tsub_distrib _ (fun _ _ => card_le_indexSpan f _)]
  have he : (∑ k : Fin K, (Finset.univ.filter (fun i => key i = k)).card) = N := by
    simpa using (Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ) (t := Finset.univ) (f := key) (by simp)).symm
  rw [he]
  exact Nat.sub_le_sub_right (sum_span_card_le f key hk) N

end TreeEdit

end OAI

-- ---- from OAI.Combinatorics.TreeEdit.SegmentComparison ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace TreeEdit

universe u

variable {α : Type u} {x y z : List α}

theorem span_length_formula {N L : ℕ} (f : Fin N ↪o Fin L) (s : Finset (Fin N))
    (hs : s.Nonempty) :
    (f (s.min' hs)).val + (indexSpan f s).card = (f (s.max' hs)).val + 1 := by
  rw [indexSpan, dite_eq_left hs, Fin.card_Icc]
  have hle := f.monotone (s.min'_le_max' hs)
  omega

end TreeEdit

end OAI

-- ---- from OAI.Combinatorics.TreeEdit.CycleCharging ----
namespace OAI

namespace TreeEdit

universe u

attribute [local instance] Classical.propDecidable

lemma cycle_coordinates (m B n : ℕ) :
    n = n / (m * B) * (m * B) + (n / B % m) * B + n % B := by
  have h₁ := Nat.mod_add_div n B
  have h₂ := Nat.mod_add_div (n / B) m
  have hd : n / B / m = n / (m * B) := by rw [Nat.div_div_eq_div_mul, Nat.mul_comm]
  rw [hd] at h₂
  nlinarith

lemma split_cycle_gap {m B p p' q q' : ℕ} (hm : 2 ≤ m) (hB : 0 < B)
    (hp : p / (m * B) = p' / (m * B))
    (hq : q / (m * B) < q' / (m * B))
    (hc : p / B % m = q / B % m) (hc' : p' / B % m = q' / B % m) :
    q + p' + (m - 2) * B ≤ q' + p := by
  have hp0 := cycle_coordinates m B p
  have hp1 := cycle_coordinates m B p'
  have hq0 := cycle_coordinates m B q
  have hq1 := cycle_coordinates m B q'
  rw [hp, hc] at hp0
  rw [hc'] at hp1
  have hpm := Nat.mod_lt p hB
  have hpm' := Nat.mod_lt p' hB
  have hqm := Nat.mod_lt q hB
  have hqm' := Nat.mod_lt q' hB
  have ht := Nat.mul_le_mul_right (m * B) (Nat.succ_le_of_lt hq)
  have hm' : (m - 2) * B + 2 * B = m * B := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hm]
  simp only [Nat.succ_mul] at ht
  omega

lemma blockIndex_monotone {M P N : ℕ} (hP : 0 < P)
    (f : Fin N ↪o Fin (M * P)) : Monotone (fun i => blockIndex hP (f i)) := by
  intro i j hij
  exact Nat.div_le_div_right (f.monotone hij)

lemma sum_block_losses {M P N : ℕ} (hP : 0 < P)
    (f : Fin N ↪o Fin (M * P)) :
    (∑ a : Fin M, (P - (Finset.univ.filter
      (fun i => blockIndex hP (f i) = a)).card)) = M * P - N := by
  rw [Finset.sum_tsub_distrib _ (fun a _ => card_block_fiber hP f a)]
  have he : (∑ a : Fin M, (Finset.univ.filter
      (fun i => blockIndex hP (f i) = a)).card) = N := by
    simpa using (Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ) (t := Finset.univ)
      (f := fun i => blockIndex hP (f i)) (by simp)).symm
  simp [he]

lemma split_cycle_span_gap {m B T N : ℕ} (hm : 2 ≤ m) (hB : 0 < B)
    (f g : Fin N ↪o Fin (T * (m * B)))
    (hc : ∀ i, (f i).val / B % m = (g i).val / B % m)
    (a : Fin T) (hC : 0 < m * B)
    (hs : (Finset.univ.filter (fun i => blockIndex hC (f i) = a)).Nonempty)
    (hsp : blockIndex hC (g ((Finset.univ.filter
      (fun i => blockIndex hC (f i) = a)).min' hs)) ≠
      blockIndex hC (g ((Finset.univ.filter
      (fun i => blockIndex hC (f i) = a)).max' hs))) :
    (m - 2) * B ≤ (indexSpan g (Finset.univ.filter
      (fun i => blockIndex hC (f i) = a))).card -
        (Finset.univ.filter (fun i => blockIndex hC (f i) = a)).card := by
  let s := Finset.univ.filter (fun i => blockIndex hC (f i) = a)
  let i := s.min' hs
  let j := s.max' hs
  have hi : blockIndex hC (f i) = a := (Finset.mem_filter.mp (s.min'_mem hs)).2
  have hj : blockIndex hC (f j) = a := (Finset.mem_filter.mp (s.max'_mem hs)).2
  have hij : i ≤ j := s.min'_le _ (s.max'_mem hs)
  have hg : (g i).val / (m * B) < (g j).val / (m * B) := by
    have hle := blockIndex_monotone hC g hij
    have hne : (blockIndex hC (g i)) ≠ blockIndex hC (g j) := hsp
    exact (show blockIndex hC (g i) < blockIndex hC (g j) from lt_of_le_of_ne hle hne)
  have hp : (f i).val / (m * B) = (f j).val / (m * B) :=
    congrArg Fin.val (hi.trans hj.symm)
  have hgap := split_cycle_gap hm hB hp hg (hc i) (hc j)
  have hfcard := card_le_indexSpan f s
  have hflen := span_length_formula f s hs
  have hglen := span_length_formula g s hs
  change (m - 2) * B ≤ (indexSpan g s).card - s.card
  dsimp [i, j] at hgap
  omega

lemma cycle_charging {m B T N : ℕ} (hm : 2 ≤ m) (hB : 0 < B)
    (f g : Fin N ↪o Fin (T * (m * B)))
    (hc : ∀ i, (f i).val / B % m = (g i).val / B % m)
    (δ : ℝ) (hδ : δ ≤ ((m - 2) * B : ℕ))
    (hsmall : ∀ (a b : Fin T),
      (∀ i ∈ Finset.univ.filter (fun i => blockIndex (by positivity : 0 < m * B) (f i) = a),
        blockIndex (by positivity : 0 < m * B) (g i) = b) →
      δ ≤ ((m * B - (Finset.univ.filter
          (fun i => blockIndex (by positivity : 0 < m * B) (f i) = a)).card : ℕ) : ℝ)) :
    (T : ℝ) * δ ≤ 2 * ((T * (m * B) - N : ℕ) : ℝ) := by
  classical
  have hC : 0 < m * B := by positivity
  let key := fun i => blockIndex hC (f i)
  let s := fun a : Fin T => Finset.univ.filter (fun i => key i = a)
  have hlocal (a : Fin T) : δ ≤ ((m * B - (s a).card : ℕ) : ℝ) +
      (((indexSpan g (s a)).card - (s a).card : ℕ) : ℝ) := by
    by_cases hs : (s a).Nonempty
    · by_cases he : blockIndex hC (g ((s a).min' hs)) =
          blockIndex hC (g ((s a).max' hs))
      · have hh := hsmall a (blockIndex hC (g ((s a).min' hs))) (by
          intro i hi
          have hl := blockIndex_monotone hC g ((s a).min'_le i hi)
          have hr := blockIndex_monotone hC g ((s a).le_max' i hi)
          change blockIndex hC (g i) ≤ blockIndex hC (g ((s a).max' hs)) at hr
          rw [← he] at hr
          exact le_antisymm hr hl)
        exact hh.trans (le_add_of_nonneg_right (Nat.cast_nonneg _))
      · have hg := split_cycle_span_gap hm hB f g hc a hC hs he
        have hh : δ ≤ (((indexSpan g (s a)).card - (s a).card : ℕ) : ℝ) :=
          hδ.trans (by exact_mod_cast hg)
        exact hh.trans (le_add_of_nonneg_left (Nat.cast_nonneg _))
    · have he : s a = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      rw [he]
      simp only [Finset.card_empty, Nat.sub_zero, indexSpan_empty, Nat.cast_zero, add_zero]
      exact hδ.trans (by exact_mod_cast Nat.mul_le_mul_right B (Nat.sub_le m 2))
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin T))) => hlocal a)
  have htarget := sum_span_gaps_le g key (blockIndex_monotone hC f)
  have hsource := sum_block_losses hC f
  have htarget' : (∑ a : Fin T, (((indexSpan g (s a)).card - (s a).card : ℕ) : ℝ)) ≤
      ((T * (m * B) - N : ℕ) : ℝ) := by exact_mod_cast htarget
  have hsource' : (∑ a : Fin T, ((m * B - (s a).card : ℕ) : ℝ)) =
      ((T * (m * B) - N : ℕ) : ℝ) := by exact_mod_cast hsource
  simp only [Finset.sum_add_distrib] at hsum
  rw [hsource'] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  linarith

end TreeEdit

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.TreeEdit.cycle_charging := @_root_.OAI.TreeEdit.cycle_charging
