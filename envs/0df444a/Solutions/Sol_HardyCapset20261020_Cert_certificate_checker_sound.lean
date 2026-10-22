-- Prove2me | solution 1 for HardyCapset20261020.Cert.certificate_checker_sound
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-20T15:31:34.396558+00:00
-- url     : https://prove2.me/submissions/f28ce177-95f3-4071-97c9-3e4151411376

import Definitions.Def_HardyCapsetCertificateModel20261020
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace HardyCapset20261020.Cert

theorem decode_inj (q r : ℕ) (hq : q < 6561) (hr : r < 6561)
    (h : decode q = decode r) : q = r := by
  have h0 := congrArg (fun p : Point => (p 0).val) h
  have h1 := congrArg (fun p : Point => (p 1).val) h
  have h2 := congrArg (fun p : Point => (p 2).val) h
  have h3 := congrArg (fun p : Point => (p 3).val) h
  have h4 := congrArg (fun p : Point => (p 4).val) h
  have h5 := congrArg (fun p : Point => (p 5).val) h
  have h6 := congrArg (fun p : Point => (p 6).val) h
  have h7 := congrArg (fun p : Point => (p 7).val) h
  norm_num [decode, ZMod.val_natCast] at h0 h1 h2 h3 h4 h5 h6 h7
  omega

theorem baseline_ids_nodup : baselineIds.Nodup := by
  have hs : List.IsChain (· < ·) baselineIds := by decide
  have hp : List.Pairwise (· < ·) baselineIds := List.isChain_iff_pairwise.mp hs
  exact hp.imp (fun h => Nat.ne_of_lt h)

theorem baseline_ids_range : ∀ q ∈ baselineIds, q < 6561 := by
  have h : baselineIds.all (fun q => q < 6561) = true := by decide
  simpa using List.all_eq_true.mp h

theorem decode_list_nodup {l : List ℕ} (hn : l.Nodup)
    (hr : ∀ q ∈ l, q < 6561) : (l.map decode).Nodup := by
  exact hn.map_on (fun q hq r hr' he => decode_inj q r (hr q hq) (hr r hr') he)

theorem cast_dot (n q : ℕ) :
    (∑ i : Fin 8, decode n i * decode q i) = (dotCode n q : ZMod 3) := by
  simp [decode, dotCode, natDot, digit, Nat.cast_sum, Nat.cast_mul]

theorem dot_iff (n q t : ℕ) (ht : t < 3) :
    (∑ i : Fin 8, decode n i * decode q i) = (t : ZMod 3) ↔ dotCode n q = t := by
  rw [cast_dot]
  constructor
  · intro h
    have hv := congrArg ZMod.val h
    simpa [ZMod.val_natCast, dotCode, Nat.mod_eq_of_lt ht] using hv
  · intro h
    rw [h]

theorem line_sound {a b c : ℕ} (h : LineCode a b c) :
    decode a + decode b + decode c = 0 := by
  funext i
  have hi := h i
  have hc := congrArg (fun q : ℕ => (q : ZMod 3)) hi
  simpa [decode, digit, Nat.cast_add] using hc

theorem entry_eq (a : Array ℕ) (i : Fin a.size) : entry a i.val = a[i] := by
  simp [entry]

theorem entry_mem {a : Array ℕ} {i : ℕ} (hi : i < a.size) : entry a i ∈ a.toList := by
  rw [entry_eq a ⟨i, hi⟩]
  exact Array.getElem_mem_toList hi

theorem base_mem (i : ℕ) (hi : i < baseArray.size) : baseAt i ∈ baselineIds := by
  have h := entry_mem hi
  simpa [baseAt, baseArray] using h

theorem base_range (i : ℕ) (hi : i < baseArray.size) : baseAt i < 6561 :=
  baseline_ids_range _ (base_mem i hi)

theorem fixed_anchor_mem (c : Certificate) (ht : c.level < 3)
    (a : ℕ) (ha : FixedAnchor c a) : decode (baseAt a) ∈ fixedSet c := by
  apply Finset.mem_sdiff.mpr
  refine ⟨?_, ?_⟩
  · apply List.mem_toFinset.mpr
    exact List.mem_map.mpr ⟨baseAt a, base_mem a ha.1, rfl⟩
  · intro h
    have hd := (Finset.mem_filter.mp h).2
    exact ha.2 ((dot_iff c.normal (baseAt a) c.level ht).mp hd)

theorem decode_surjective : Function.Surjective (fun q : Fin 6561 => decode q.val) := by
  have hinj : Function.Injective (fun q : Fin 6561 => decode q.val) := by
    intro q r h
    apply Fin.ext
    exact decode_inj q.val r.val q.isLt r.isLt h
  apply ((Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, ?_⟩).2
  norm_num [Point, Fintype.card_pi]

theorem deleted_count_eq (c : Certificate) (ht : c.level < 3) :
    (baseline ∩ hyperplane (decode c.normal) c.level).card = deletedCount c := by
  let l := baselineIds.filter (fun q => dotCode c.normal q = c.level)
  have hn : (l.map decode).Nodup := decode_list_nodup
    (baseline_ids_nodup.filter _) (fun q hq => baseline_ids_range q (List.mem_filter.mp hq).1)
  have hs : baseline ∩ hyperplane (decode c.normal) c.level = (l.map decode).toFinset := by
    ext x
    constructor
    · intro hx
      obtain ⟨hb, hh⟩ := Finset.mem_inter.mp hx
      obtain ⟨q, hq, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hb)
      apply List.mem_toFinset.mpr
      apply List.mem_map.mpr
      refine ⟨q, List.mem_filter.mpr ⟨hq, ?_⟩, he⟩
      have hd := (dot_iff c.normal q c.level ht).mp
        (by simpa [← he] using (Finset.mem_filter.mp hh).2)
      simpa using hd
    · intro hx
      obtain ⟨q, hq, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
      obtain ⟨hqb, hqd⟩ := List.mem_filter.mp hq
      apply Finset.mem_inter.mpr
      constructor
      · exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨q, hqb, he⟩)
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [← he]
        exact (dot_iff c.normal q c.level ht).mpr (of_decide_eq_true hqd)
  rw [hs, List.toFinset_card_of_nodup hn, List.length_map]
  rfl

end HardyCapset20261020.Cert

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace HardyCapset20261020.Cert

theorem decode_ne {a b : ℕ} (ha : a < 6561) (hb : b < 6561) (hne : a ≠ b) :
    decode a ≠ decode b := fun he => hne (decode_inj a b ha hb he)

theorem candidate_complete (c : Certificate) (ht : c.level < 3)
    (hblock : ∀ q : Fin 6561, BlockOK c q.val c.blockers[q.val]!)
    (A : Finset Point) (hA : IsCap A) (hF : fixedSet c ⊆ A)
    (p : Point) (hp : p ∈ A \ fixedSet c) :
    ∃ j : Fin c.pool.size, vertex c j.val = p := by
  obtain ⟨q, hq⟩ := decode_surjective p
  change decode q.val = p at hq
  have hc := hblock q
  obtain ⟨hpA, hpF⟩ := Finset.mem_sdiff.mp hp
  generalize hab : c.blockers[q.val]! = ab at hc
  unfold BlockOK at hc
  split_ifs at hc with ha he
  · obtain ⟨hf, heq⟩ := hc
    exfalso
    apply hpF
    rw [← hq, heq]
    exact fixed_anchor_mem c ht ab.1 hf
  · obtain ⟨hfa, hfb, hne, hline⟩ := hc
    have hma := fixed_anchor_mem c ht ab.1 hfa
    have hmb := fixed_anchor_mem c ht ab.2 hfb
    have hneq := decode_ne (base_range ab.1 hfa.1) (base_range ab.2 hfb.1) hne
    have hna : decode (baseAt ab.1) ≠ p := fun heq => hpF (heq ▸ hma)
    have hnb : decode (baseAt ab.2) ≠ p := fun heq => hpF (heq ▸ hmb)
    exfalso
    apply hA _ (hF hma) _ (hF hmb) p hpA hneq hna hnb
    simpa [hq] using line_sound hline
  · obtain ⟨hj, heq⟩ := hc
    refine ⟨⟨ab.1 - baseArray.size, hj⟩, ?_⟩
    simp only [vertex, heq, hq]

theorem row_point_range (c : Certificate)
    (hrange : ∀ q ∈ c.pool.toList, q < 6561)
    (r : Row) (hvars : ∀ j ∈ r.vars.toList, j < c.pool.size)
    (k : ℕ) (hk : k < r.vars.size) : rowPoint c r k < 6561 := by
  exact hrange _ (entry_mem (hvars _ (entry_mem hk)))

theorem row_pattern_legal (c : Certificate) (ht : c.level < 3)
    (hrange : ∀ q ∈ c.pool.toList, q < 6561)
    (A : Finset Point) (hA : IsCap A) (hF : fixedSet c ⊆ A)
    (r : Row) (hr : RowOK c r) :
    LegalPattern r (fun k : Fin r.vars.size =>
      decide (vertex c (entry r.vars k.val) ∈ A \ fixedSet c)) := by
  let B := A \ fixedSet c
  let s : Fin r.vars.size → Bool := fun k => decide (vertex c (entry r.vars k.val) ∈ B)
  change LegalPattern r s
  obtain ⟨hcoeff, hvars, hedges, htriples, hpat⟩ := hr
  constructor
  · intro e he hs
    obtain ⟨hl, hrr, hanchor, hne, hline⟩ := hedges e he
    have hpl : vertex c (entry r.vars e.left) ∈ B := by
      simpa [s, bit, hl] using hs.1
    have hpr : vertex c (entry r.vars e.right) ∈ B := by
      simpa [s, bit, hrr] using hs.2
    obtain ⟨hpla, hplf⟩ := Finset.mem_sdiff.mp hpl
    obtain ⟨hpra, hprf⟩ := Finset.mem_sdiff.mp hpr
    have hf := fixed_anchor_mem c ht e.anchor hanchor
    have hneq := decode_ne (row_point_range c hrange r hvars _ hl)
      (row_point_range c hrange r hvars _ hrr) hne
    apply hA _ hpla _ hpra _ (hF hf) hneq
      (fun heq => hplf (heq.symm ▸ hf)) (fun heq => hprf (heq.symm ▸ hf))
    exact line_sound hline
  · intro e he hs
    obtain ⟨h1, h2, h3, h12, h13, h23, hline⟩ := htriples e he
    have hp1 : vertex c (entry r.vars e.first) ∈ B := by
      simpa [s, bit, h1] using hs.1
    have hp2 : vertex c (entry r.vars e.second) ∈ B := by
      simpa [s, bit, h2] using hs.2.1
    have hp3 : vertex c (entry r.vars e.third) ∈ B := by
      simpa [s, bit, h3] using hs.2.2
    have hn12 := decode_ne (row_point_range c hrange r hvars _ h1)
      (row_point_range c hrange r hvars _ h2) h12
    have hn13 := decode_ne (row_point_range c hrange r hvars _ h1)
      (row_point_range c hrange r hvars _ h3) h13
    have hn23 := decode_ne (row_point_range c hrange r hvars _ h2)
      (row_point_range c hrange r hvars _ h3) h23
    apply hA _ (Finset.mem_sdiff.mp hp1).1 _ (Finset.mem_sdiff.mp hp2).1
      _ (Finset.mem_sdiff.mp hp3).1 hn12 hn13 hn23
    exact line_sound hline

def selected (c : Certificate) (B : Finset Point) : Finset (Fin c.pool.size) :=
  Finset.univ.filter (fun j => vertex c j.val ∈ B)

theorem row_selected_sum (c : Certificate) (B : Finset Point) (r : Row)
    (hvars : ∀ j ∈ r.vars.toList, j < c.pool.size) :
    (∑ j ∈ selected c B, coefficient r j.val) =
    ∑ k : Fin r.vars.size,
      if vertex c (entry r.vars k.val) ∈ B then entry r.coeff k.val else 0 := by
  unfold coefficient
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  have hv := hvars _ (entry_mem k.isLt)
  let v : Fin c.pool.size := ⟨entry r.vars k.val, hv⟩
  have heq : (fun j : Fin c.pool.size =>
      if entry r.vars k.val = j.val then entry r.coeff k.val else 0) =
      (fun j : Fin c.pool.size => if j = v then entry r.coeff k.val else 0) := by
    funext j
    simp [v, Fin.ext_iff, eq_comm]
  rw [heq]
  simp [selected, v]

theorem scaled_cover_bound {α ρ : Type*} [DecidableEq α]
    (T : Finset α) (R : Finset ρ) (D : ℕ) (w : ρ → ℕ)
    (f : ρ → α → ℕ) (rhs : ρ → ℕ)
    (hcover : ∀ j ∈ T, D ≤ ∑ r ∈ R, w r * f r j)
    (hvalid : ∀ r ∈ R, ∑ j ∈ T, f r j ≤ rhs r) :
    D * T.card ≤ ∑ r ∈ R, w r * rhs r := by
  calc
    D * T.card = ∑ _j ∈ T, D := by simp [Nat.mul_comm]
    _ ≤ ∑ j ∈ T, ∑ r ∈ R, w r * f r j := Finset.sum_le_sum hcover
    _ = ∑ r ∈ R, w r * (∑ j ∈ T, f r j) := by
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
    _ ≤ ∑ r ∈ R, w r * rhs r := by
      apply Finset.sum_le_sum
      intro r hr
      exact Nat.mul_le_mul_left _ (hvalid r hr)

theorem nodup_list_sum (l : List ℕ) (f : ℕ → ℕ) (hn : l.Nodup) :
    (l.map f).sum = ∑ r ∈ l.toFinset, f r := by
  induction l with
  | nil => simp
  | cons a l ih =>
      obtain ⟨hna, hnl⟩ := List.nodup_cons.mp hn
      simp only [List.map_cons, List.sum_cons, List.toFinset_cons]
      rw [Finset.sum_insert (by simpa using hna), ih hnl]

theorem local_cover_sound (c : Certificate) (j : ℕ) (h : LocalCoverOK c j) :
    c.denominator ≤ cover c j := by
  obtain ⟨hn, hb, hsum⟩ := h
  let l := c.coverRows[j]!.toList
  let f := fun r : ℕ => c.rows[r]!.weight * coefficient c.rows[r]! j
  have hs : l.toFinset ⊆ Finset.range c.rows.size := by
    intro r hr
    exact Finset.mem_range.mpr (hb r (List.mem_toFinset.mp hr))
  calc
    c.denominator ≤ (l.map f).sum := hsum
    _ = ∑ r ∈ l.toFinset, f r := nodup_list_sum l f hn
    _ ≤ ∑ r ∈ Finset.range c.rows.size, f r :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => Nat.zero_le _)
    _ = cover c j := by
      rw [← Fin.sum_univ_eq_sum_range f]
      apply Finset.sum_congr rfl
      intro r hr
      simp [f, cover, r.isLt]

theorem checked_remainder_bound (c : Certificate) (hc : Check c)
    (A : Finset Point) (hA : IsCap A) (hF : fixedSet c ⊆ A) :
    (A \ fixedSet c).card ≤ deletedCount c := by
  obtain ⟨hn, ht, hD, hrange, hbs, hblocks, hrows, hcs, hcover, hcost⟩ := hc
  let B := A \ fixedSet c
  let T := selected c B
  have himage : Finset.image (fun j : Fin c.pool.size => vertex c j.val) T = B := by
    ext p
    constructor
    · intro hp
      obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hp
      simpa [he] using (Finset.mem_filter.mp hj).2
    · intro hp
      obtain ⟨j, hj⟩ := candidate_complete c ht hblocks A hA hF p hp
      apply Finset.mem_image.mpr
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [hj] using hp⟩, hj⟩
  have hcard : B.card ≤ T.card := by
    rw [← himage]
    exact Finset.card_image_le
  have hvalid : ∀ r : Fin c.rows.size,
      (∑ j ∈ T, coefficient c.rows[r] j.val) ≤ c.rows[r].bound := by
    intro r
    have hr := hrows _ (Array.getElem_mem_toList r.isLt)
    rw [row_selected_sum c B c.rows[r] hr.2.1]
    have hh := row_pattern_legal c ht hrange A hA hF c.rows[r] hr
    have hb := hr.2.2.2.2 _ hh
    simpa [Fin.getElem_fin, B] using hb
  have hscaled : c.denominator * T.card ≤ cost c := by
    apply scaled_cover_bound T Finset.univ c.denominator
      (fun r : Fin c.rows.size => c.rows[r].weight)
      (fun r j => coefficient c.rows[r] j.val)
      (fun r => c.rows[r].bound)
    · intro j hj
      simpa [cover] using local_cover_sound c j.val (hcover j)
    · intro r hr
      exact hvalid r
  have hlt : c.denominator * T.card < c.denominator * (deletedCount c + 1) :=
    lt_of_le_of_lt hscaled hcost
  have htcard : T.card < deletedCount c + 1 := Nat.lt_of_mul_lt_mul_left hlt
  change B.card ≤ deletedCount c
  omega

theorem baseline_card_checked : baseline.card = 512 := by
  have hn := decode_list_nodup baseline_ids_nodup baseline_ids_range
  rw [baseline, List.toFinset_card_of_nodup hn, List.length_map]
  decide

theorem check_sound (c : Certificate) (hc : Check c) :
    CompletionBound (decode c.normal) c.level := by
  intro A hA hF
  have hb := checked_remainder_bound c hc A hA hF
  have hs := Finset.card_sdiff_add_card_inter baseline (hyperplane (decode c.normal) c.level)
  rw [deleted_count_eq c hc.2.1, baseline_card_checked] at hs
  have ht := Finset.card_sdiff_add_card_eq_card hF
  change (A \ core (decode c.normal) c.level).card ≤ deletedCount c at hb
  change (core (decode c.normal) c.level).card + deletedCount c = 512 at hs
  omega

end HardyCapset20261020.Cert
open HardyCapset20261020 HardyCapset20261020.Cert
theorem solution (c : Certificate) (hc : Check c) :
    CompletionBound (decode c.normal) c.level := check_sound c hc
#print axioms solution
