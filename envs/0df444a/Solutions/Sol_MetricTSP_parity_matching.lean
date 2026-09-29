-- Prove2me | solution 1 for MetricTSP.parity_matching
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-24T23:57:31.348658+00:00
-- url     : https://prove2.me/submissions/122ef33d-8bc2-4e7b-99ff-f1f35ebd67d6

import Mathlib
import Definitions.Def_MetricTSP_model
import Theorems.Thm_MetricTSP_even_set_matching
import Theorems.Thm_MetricTSP_eliminate_steiner2

set_option maxHeartbeats 1000000

namespace MetricTSP

open Finset

variable {n : ℕ}

/-- A valid pairing of the set `T`: a fixed-point-free involution on `T`,
the identity elsewhere. -/
def IsPairing (T : Finset (Fin n)) (f : Fin n → Fin n) : Prop :=
  (∀ v ∈ T, f v ∈ T ∧ f (f v) = v ∧ f v ≠ v) ∧ (∀ v ∉ T, f v = v)

/-- Extend a pairing by swapping a fresh pair. -/
def swapExt (a b : Fin n) (f : Fin n → Fin n) : Fin n → Fin n :=
  fun v => if v = a then b else if v = b then a else f v

lemma swapExt_eval (a b : Fin n) (f : Fin n → Fin n) (v : Fin n) :
    swapExt a b f v = if v = a then b else if v = b then a else f v := rfl

/-- Every even set admits a pairing. -/
lemma exists_pairing : ∀ (T : Finset (Fin n)), Even T.card →
    ∃ f : Fin n → Fin n, IsPairing T f := by
  intro T
  induction T using Finset.strongInduction with
  | _ T ih =>
    intro hT
    rcases Finset.eq_empty_or_nonempty T with rfl | ⟨a, ha⟩
    · exact ⟨id, fun v hv => absurd hv (Finset.notMem_empty v), fun v _ => rfl⟩
    · have hcard : 2 ≤ T.card := by
        rcases hT with ⟨t, ht⟩
        have h1 : 1 ≤ T.card := Finset.card_pos.mpr ⟨a, ha⟩
        omega
      have hbex : ∃ b ∈ T, b ≠ a := by
        by_contra hb
        push_neg at hb
        have hsub : T ⊆ {a} := fun v hv => Finset.mem_singleton.mpr (hb v hv)
        have := Finset.card_le_card hsub
        rw [Finset.card_singleton] at this
        omega
      obtain ⟨b, hb, hba⟩ := hbex
      have hT'sub : T \ {a, b} ⊂ T := by
        refine Finset.ssubset_iff_of_subset Finset.sdiff_subset |>.mpr ⟨a, ha, ?_⟩
        intro hcon
        exact (Finset.mem_sdiff.mp hcon).2 (Finset.mem_insert_self a {b})
      have habT : ({a, b} : Finset (Fin n)) ⊆ T := by
        intro v hv
        rw [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl
        · exact ha
        · exact hb
      have hT'card : (T \ {a, b}).card = T.card - 2 := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr habT,
          Finset.card_insert_of_notMem (by simpa using Ne.symm hba),
          Finset.card_singleton]
      obtain ⟨f', hf'⟩ := ih (T \ {a, b}) hT'sub (by
        rcases hT with ⟨t, ht⟩
        rw [hT'card]
        exact ⟨t - 1, by omega⟩)
      have hga : swapExt a b f' a = b := by
        rw [swapExt_eval, if_pos rfl]
      have hgb : swapExt a b f' b = a := by
        rw [swapExt_eval, if_neg hba, if_pos rfl]
      refine ⟨swapExt a b f', ?_, ?_⟩
      · intro v hv
        by_cases hva : v = a
        · rw [hva, hga, hgb]
          exact ⟨hb, rfl, hba⟩
        · by_cases hvb : v = b
          · rw [hvb, hgb, hga]
            exact ⟨ha, rfl, Ne.symm hba⟩
          · have hvT' : v ∈ T \ {a, b} := by
              rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
              push_neg
              exact ⟨hv, hva, hvb⟩
            have h1 := hf'.1 v hvT'
            have hfv' := h1.1
            rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hfv'
            push_neg at hfv'
            have hgv : swapExt a b f' v = f' v := by
              rw [swapExt_eval, if_neg hva, if_neg hvb]
            have hgfv : swapExt a b f' (f' v) = f' (f' v) := by
              rw [swapExt_eval, if_neg hfv'.2.1, if_neg hfv'.2.2]
            rw [hgv, hgfv]
            exact ⟨hfv'.1, h1.2.1, h1.2.2⟩
      · intro v hv
        have hva : v ≠ a := fun hcon => hv (hcon ▸ ha)
        have hvb : v ≠ b := fun hcon => hv (hcon ▸ hb)
        have hvT' : v ∉ T \ {a, b} := fun hcon =>
          hv (Finset.sdiff_subset hcon)
        rw [swapExt_eval, if_neg hva, if_neg hvb, hf'.2 v hvT']

/-- Reduce an exact bound to bounds with arbitrarily small slack, via the
finitely many candidate pairings. -/
lemma pairing_of_eps (c : Fin n → Fin n → ℝ) (T : Finset (Fin n)) (hT : Even T.card)
    (B : ℝ)
    (heps : ∀ ε : ℝ, 0 < ε → ∃ f : Fin n → Fin n, IsPairing T f ∧
      ∑ v ∈ T, c v (f v) ≤ B + ε) :
    ∃ f : Fin n → Fin n, IsPairing T f ∧ ∑ v ∈ T, c v (f v) ≤ B := by
  classical
  set F : Finset (Fin n → Fin n) := Finset.univ.filter (fun f => IsPairing T f) with hF
  have hFne : F.Nonempty := by
    obtain ⟨f, hf⟩ := exists_pairing T hT
    exact ⟨f, by rw [hF, Finset.mem_filter]; exact ⟨Finset.mem_univ f, hf⟩⟩
  obtain ⟨f0, hf0F, hf0min⟩ := Finset.exists_min_image F
    (fun f => ∑ v ∈ T, c v (f v)) hFne
  rw [hF, Finset.mem_filter] at hf0F
  refine ⟨f0, hf0F.2, le_of_forall_pos_le_add (fun ε hε => ?_)⟩
  obtain ⟨f, hf, hfB⟩ := heps ε hε
  have := hf0min f (by rw [hF, Finset.mem_filter]; exact ⟨Finset.mem_univ f, hf⟩)
  linarith

/-! ### Rationalizing a Held–Karp point -/

/-- The uniform fractional tour. -/
def uPt (n : ℕ) : Fin n → Fin n → ℚ :=
  fun u v => if u = v then 0 else 2 / (n - 1)

lemma uPt_symm (u v : Fin n) : uPt n u v = uPt n v u := by
  unfold uPt
  by_cases h : u = v
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

lemma uPt_nonneg (hn : 3 ≤ n) (u v : Fin n) : 0 ≤ uPt n u v := by
  unfold uPt
  by_cases h : u = v
  · rw [if_pos h]
  · rw [if_neg h]
    have hpos : (0 : ℚ) < (n : ℚ) - 1 := by
      have : (3 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
      linarith
    positivity

lemma uPt_deg (hn : 3 ≤ n) (v : Fin n) : ∑ u, uPt n v u = 2 := by
  have hcard : (Finset.univ.erase v).card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ,
      Fintype.card_fin]
  have hzero : uPt n v v = 0 := by
    unfold uPt
    rw [if_pos rfl]
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ v), hzero, zero_add]
  have hconst : ∀ u ∈ Finset.univ.erase v, uPt n v u = 2 / ((n : ℚ) - 1) := by
    intro u hu
    unfold uPt
    rw [if_neg (Ne.symm (Finset.ne_of_mem_erase hu))]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, hcard, nsmul_eq_mul]
  have hn1 : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by
    have : 1 ≤ n := by omega
    push_cast [this]
    ring
  rw [hn1]
  have hne : (n : ℚ) - 1 ≠ 0 := by
    have : (3 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
    linarith
  field_simp

/-- Cut mass of the uniform point: `|S| (n - |S|) · 2/(n-1)`. -/
lemma uPt_cut (hn : 3 ≤ n) (S : Finset (Fin n)) (h1 : S.Nonempty) (h2 : S ≠ Finset.univ) :
    2 ≤ ∑ u ∈ S, ∑ v ∈ Sᶜ, uPt n u v := by
  have hdisj : ∀ u ∈ S, ∀ v ∈ Sᶜ, uPt n u v = 2 / ((n : ℚ) - 1) := by
    intro u hu v hv
    unfold uPt
    rw [if_neg]
    intro hcon
    rw [hcon] at hu
    exact (Finset.mem_compl.mp hv) hu
  rw [Finset.sum_congr rfl (fun u hu => Finset.sum_congr rfl (hdisj u hu))]
  rw [Finset.sum_congr rfl (fun u _ => Finset.sum_const _), Finset.sum_const]
  have hcards : Sᶜ.card = n - S.card := by
    rw [Finset.card_compl, Fintype.card_fin]
  rw [hcards]
  have hs1 : 1 ≤ S.card := Finset.card_pos.mpr h1
  have hsn : S.card ≤ n - 1 := by
    have hle := Finset.card_le_univ S
    rw [Fintype.card_fin] at hle
    rcases Nat.lt_or_ge S.card n with h | h
    · omega
    · exfalso
      apply h2
      apply Finset.eq_univ_of_card
      rw [Fintype.card_fin]
      omega
  have hprod : (n - 1 : ℕ) ≤ S.card * (n - S.card) := by
    have ha : (0:ℤ) ≤ (S.card : ℤ) - 1 := by
      have : (1 : ℤ) ≤ (S.card : ℤ) := by exact_mod_cast hs1
      omega
    have hb : (0:ℤ) ≤ (n : ℤ) - (S.card : ℤ) - 1 := by
      have h1 : (S.card : ℤ) ≤ ((n - 1 : ℕ) : ℤ) := by exact_mod_cast hsn
      have h2 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
        push_cast [show 1 ≤ n from by omega]
        ring
      omega
    zify [show S.card ≤ n from by omega, show 1 ≤ n from by omega]
    nlinarith [mul_nonneg ha hb]
  have hnQ : (0 : ℚ) < (n : ℚ) - 1 := by
    have : (3 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
    linarith
  have hpos : (0 : ℚ) < 2 / ((n : ℚ) - 1) := div_pos two_pos hnQ
  have hcast : (n : ℚ) - 1 ≤ ((S.card * (n - S.card) : ℕ) : ℚ) := by
    calc (n : ℚ) - 1 = ((n - 1 : ℕ) : ℚ) := by
          push_cast [show 1 ≤ n from by omega]
          ring
      _ ≤ _ := by exact_mod_cast hprod
  have hcalc : ((n : ℚ) - 1) * (2 / ((n : ℚ) - 1)) = 2 := by
    field_simp
  rw [smul_smul, nsmul_eq_mul]
  calc (2 : ℚ) = ((n : ℚ) - 1) * (2 / ((n : ℚ) - 1)) := hcalc.symm
    _ ≤ ((S.card * (n - S.card) : ℕ) : ℚ) * (2 / ((n : ℚ) - 1)) :=
        mul_le_mul_of_nonneg_right hcast (le_of_lt hpos)
    _ = _ := by push_cast; ring

/-- Strong cut bound for the uniform point on middle-sized sets. -/
lemma uPt_cut_strong (hn : 3 ≤ n) (S : Finset (Fin n)) (h2 : 2 ≤ S.card)
    (hn2 : S.card ≤ n - 2) :
    2 + 2 * ((n : ℚ) - 3) / ((n : ℚ) - 1) ≤ ∑ u ∈ S, ∑ v ∈ Sᶜ, uPt n u v := by
  have hdisj : ∀ u ∈ S, ∀ v ∈ Sᶜ, uPt n u v = 2 / ((n : ℚ) - 1) := by
    intro u hu v hv
    unfold uPt
    rw [if_neg]
    intro hcon
    rw [hcon] at hu
    exact (Finset.mem_compl.mp hv) hu
  rw [Finset.sum_congr rfl (fun u hu => Finset.sum_congr rfl (hdisj u hu))]
  rw [Finset.sum_congr rfl (fun u _ => Finset.sum_const _), Finset.sum_const,
    Finset.card_compl, Fintype.card_fin, smul_smul, nsmul_eq_mul]
  have hprod : 2 * (n - 2) ≤ S.card * (n - S.card) := by
    have ha : (0:ℤ) ≤ (S.card : ℤ) - 2 := by
      have : (2 : ℤ) ≤ (S.card : ℤ) := by exact_mod_cast h2
      omega
    have hb : (0:ℤ) ≤ (n : ℤ) - (S.card : ℤ) - 2 := by
      have h1 : (S.card : ℤ) ≤ ((n - 2 : ℕ) : ℤ) := by exact_mod_cast hn2
      have h2' : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by
        push_cast [show 2 ≤ n from by omega]
        ring
      omega
    zify [show S.card ≤ n from by omega, show 2 ≤ n from by omega]
    nlinarith [mul_nonneg ha hb]
  have hnQ : (0 : ℚ) < (n : ℚ) - 1 := by
    have : (3 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
    linarith
  have hpos : (0 : ℚ) < 2 / ((n : ℚ) - 1) := div_pos two_pos hnQ
  have hcast : 2 * ((n : ℚ) - 2) ≤ ((S.card * (n - S.card) : ℕ) : ℚ) := by
    calc 2 * ((n : ℚ) - 2) = ((2 * (n - 2) : ℕ) : ℚ) := by
          push_cast [show 2 ≤ n from by omega]
          ring
      _ ≤ _ := by exact_mod_cast hprod
  calc 2 + 2 * ((n : ℚ) - 3) / ((n : ℚ) - 1)
      = (2 * ((n : ℚ) - 2)) * (2 / ((n : ℚ) - 1)) := by
        field_simp
        ring
    _ ≤ ((S.card * (n - S.card) : ℕ) : ℚ) * (2 / ((n : ℚ) - 1)) :=
        mul_le_mul_of_nonneg_right hcast (le_of_lt hpos)
    _ = _ := by push_cast; ring

/-- Row sums of the symmetric defect-repair matrix. -/
lemma repair_deg (hn : 3 ≤ n) (d : Fin n → ℚ) (v : Fin n) :
    ∑ u, (if u = v then 0 else (d v + d u) / ((n:ℚ) - 2)
      - (∑ w, d w) / (((n:ℚ) - 1) * ((n:ℚ) - 2))) = d v := by
  have hn1 : ((n:ℚ) - 1) ≠ 0 := by
    have : (3:ℚ) ≤ (n:ℚ) := by exact_mod_cast hn
    linarith
  have hn2 : ((n:ℚ) - 2) ≠ 0 := by
    have : (3:ℚ) ≤ (n:ℚ) := by exact_mod_cast hn
    linarith
  have hcard : (Finset.univ.erase v).card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ,
      Fintype.card_fin]
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ v), if_pos rfl, zero_add]
  have h1 : ∀ u ∈ Finset.univ.erase v,
      (if u = v then (0:ℚ) else (d v + d u) / ((n:ℚ) - 2)
        - (∑ w, d w) / (((n:ℚ) - 1) * ((n:ℚ) - 2)))
      = (d v / ((n:ℚ) - 2) + d u / ((n:ℚ) - 2))
        - (∑ w, d w) / (((n:ℚ) - 1) * ((n:ℚ) - 2)) := by
    intro u hu
    rw [if_neg (Finset.ne_of_mem_erase hu), add_div]
  rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.sum_const, hcard, ← Finset.sum_div]
  have herase : ∑ u ∈ Finset.univ.erase v, d u = (∑ w, d w) - d v := by
    have := Finset.add_sum_erase Finset.univ d (Finset.mem_univ v)
    linarith
  rw [herase, nsmul_eq_mul, nsmul_eq_mul]
  have hcast : ((n - 1 : ℕ) : ℚ) = (n:ℚ) - 1 := by
    push_cast [show 1 ≤ n from by omega]
    ring
  rw [hcast]
  field_simp
  ring

/-- Every real Held–Karp point admits rational Held–Karp points of arbitrarily
close cost. -/
lemma rationalize (hn : 3 ≤ n) (c : Fin n → Fin n → ℝ) (x : Fin n → Fin n → ℝ)
    (hx : IsHeldKarp x) (ε : ℝ) (hε : 0 < ε) :
    ∃ q : Fin n → Fin n → ℚ,
      (∀ u v, q u v = q v u) ∧ (∀ v, q v v = 0) ∧ (∀ u v, 0 ≤ q u v) ∧
      (∀ v, ∑ u, q v u = 2) ∧
      (∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ →
        2 ≤ ∑ u ∈ S, ∑ v ∈ Sᶜ, q u v) ∧
      (∑ u, ∑ v, (q u v : ℝ) * c u v) ≤ (∑ u, ∑ v, x u v * c u v) + ε := by
  obtain ⟨hxs, hxd, hxn, hx1, hxdeg, hxcut⟩ := hx
  have hnR : (3:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hn1R : (0:ℝ) < (n:ℝ) - 1 := by linarith
  set Cb : ℝ := (∑ u, ∑ v, |c u v|) + 1 with hCb
  have hCb0 : 0 < Cb := by
    have h0 : (0:ℝ) ≤ ∑ u, ∑ v, |c u v| :=
      Finset.sum_nonneg (fun u _ => Finset.sum_nonneg (fun v _ => abs_nonneg _))
    rw [hCb]
    linarith
  set δ : ℝ := min (ε / (2 * Cb)) (1/2) with hδdef
  have hδ0 : 0 < δ := by
    rw [hδdef]
    apply lt_min
    · positivity
    · norm_num
  have hδ1 : δ ≤ 1/2 := min_le_right _ _
  have hδε : δ * Cb ≤ ε / 2 := by
    have h1 : δ ≤ ε / (2 * Cb) := min_le_left _ _
    calc δ * Cb ≤ (ε / (2 * Cb)) * Cb := by
          apply mul_le_mul_of_nonneg_right h1 (le_of_lt hCb0)
      _ = ε / 2 := by
          field_simp
  set x' : Fin n → Fin n → ℝ := fun u v => (1 - δ) * x u v + δ * (uPt n u v : ℝ)
    with hx'def
  have hx'eval : ∀ u v, x' u v = (1 - δ) * x u v + δ * (uPt n u v : ℝ) :=
    fun u v => rfl
  have huR : ∀ u v : Fin n, u ≠ v → (uPt n u v : ℝ) = 2 / ((n:ℝ) - 1) := by
    intro u v huv
    unfold uPt
    rw [if_neg huv]
    push_cast
    ring
  have huRd : ∀ v : Fin n, (uPt n v v : ℝ) = 0 := by
    intro v
    unfold uPt
    rw [if_pos rfl]
    norm_num
  set μ : ℝ := δ * (2 / ((n:ℝ) - 1)) with hμdef
  have hμ0 : 0 < μ := by
    rw [hμdef]
    positivity
  have hx'lb : ∀ u v : Fin n, u ≠ v → μ ≤ x' u v := by
    intro u v huv
    rw [hx'eval, huR u v huv, hμdef]
    have := hxn u v
    nlinarith
  have hx'symm : ∀ u v, x' u v = x' v u := by
    intro u v
    rw [hx'eval, hx'eval, hxs u v, uPt_symm]
  have hx'diag : ∀ v, x' v v = 0 := by
    intro v
    rw [hx'eval, hxd v, huRd v]
    ring
  have hx'deg : ∀ v, ∑ u, x' v u = 2 := by
    intro v
    have hu2 : ∑ u, (uPt n v u : ℝ) = 2 := by
      have := uPt_deg hn v
      have hcast : ((∑ u, uPt n v u : ℚ) : ℝ) = ∑ u, (uPt n v u : ℝ) := by
        push_cast
        rfl
      rw [← hcast, this]
      norm_num
    calc ∑ u, x' v u = (1 - δ) * (∑ u, x v u) + δ * (∑ u, (uPt n v u : ℝ)) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      _ = 2 := by
          rw [hxdeg v, hu2]
          ring
  -- slack parameter for middle cuts
  set γ : ℝ := if 4 ≤ n then 2 * ((n:ℝ) - 3) / ((n:ℝ) - 1) else 1 with hγdef
  have hγ0 : 0 < γ := by
    rw [hγdef]
    by_cases h4 : 4 ≤ n
    · rw [if_pos h4]
      have : (4:ℝ) ≤ (n:ℝ) := by exact_mod_cast h4
      exact div_pos (by linarith) (by linarith)
    · rw [if_neg h4]
      norm_num
  set η : ℝ := min (min (μ / 20) (δ * γ / (20 * (n:ℝ)^2 + 20))) (ε / (40 * Cb))
    with hηdef
  have hη0 : 0 < η := by
    rw [hηdef]
    have hn2 : (0:ℝ) < 20 * (n:ℝ)^2 + 20 := by positivity
    apply lt_min
    · apply lt_min
      · positivity
      · exact div_pos (mul_pos hδ0 hγ0) hn2
    · positivity
  -- rational approximation strictly above x'
  have hch : ∀ u v : Fin n, ∃ r : ℚ, x' u v < (r:ℝ) ∧ ((r:ℝ)) < x' u v + η :=
    fun u v => exists_rat_btwn (by linarith)
  choose r hr1 hr2 using hch
  set q0 : Fin n → Fin n → ℚ := fun u v =>
    if u = v then 0 else if u ≤ v then r u v else r v u with hq0def
  have hq0eval : ∀ u v, q0 u v =
      if u = v then 0 else if u ≤ v then r u v else r v u := fun u v => rfl
  have hq0symm : ∀ u v, q0 u v = q0 v u := by
    intro u v
    rw [hq0eval, hq0eval]
    by_cases h : u = v
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
      rcases le_total u v with hle | hle
      · rw [if_pos hle, if_neg (by
          intro hc
          exact h (le_antisymm hle hc))]
      · rw [if_neg (by
          intro hc
          exact h (le_antisymm hc hle)), if_pos hle]
  have hq0diag : ∀ v, q0 v v = 0 := by
    intro v
    rw [hq0eval, if_pos rfl]
  have hq0lb : ∀ u v : Fin n, u ≠ v → x' u v < (q0 u v : ℝ) := by
    intro u v huv
    rw [hq0eval, if_neg huv]
    by_cases hle : u ≤ v
    · rw [if_pos hle]
      exact hr1 u v
    · rw [if_neg hle]
      rw [hx'symm]
      exact hr1 v u
  have hq0ub : ∀ u v : Fin n, u ≠ v → (q0 u v : ℝ) < x' u v + η := by
    intro u v huv
    rw [hq0eval, if_neg huv]
    by_cases hle : u ≤ v
    · rw [if_pos hle]
      exact hr2 u v
    · rw [if_neg hle]
      rw [hx'symm]
      exact hr2 v u
  -- defects and repair
  set d : Fin n → ℚ := fun v => 2 - ∑ u, q0 v u with hddef
  set D : ℚ := ∑ w, d w with hDdef
  set R : Fin n → Fin n → ℚ := fun a b =>
    if b = a then 0 else (d a + d b) / ((n:ℚ) - 2) - D / (((n:ℚ) - 1) * ((n:ℚ) - 2))
    with hRdef
  have hReval : ∀ a b, R a b = if b = a then 0
      else (d a + d b) / ((n:ℚ) - 2) - D / (((n:ℚ) - 1) * ((n:ℚ) - 2)) :=
    fun a b => rfl
  have hRsymm : ∀ a b, R a b = R b a := by
    intro a b
    rw [hReval, hReval]
    by_cases h : a = b
    · rw [if_pos h.symm, if_pos h]
    · rw [if_neg (Ne.symm h), if_neg h, add_comm]
  have hRdiag : ∀ v, R v v = 0 := by
    intro v
    rw [hReval, if_pos rfl]
  have hRrow : ∀ v, ∑ u, R v u = d v := by
    intro v
    have := repair_deg hn d v
    rw [← this]
  set q : Fin n → Fin n → ℚ := fun u v => q0 u v + R u v with hqdef
  have hqeval : ∀ u v, q u v = q0 u v + R u v := fun u v => rfl
  have hqsymm : ∀ u v, q u v = q v u := by
    intro u v
    rw [hqeval, hqeval, hq0symm, hRsymm]
  have hqdiag : ∀ v, q v v = 0 := by
    intro v
    rw [hqeval, hq0diag, hRdiag]
    ring
  have hqdeg : ∀ v, ∑ u, q v u = 2 := by
    intro v
    rw [Finset.sum_congr rfl (fun u (_ : u ∈ Finset.univ) => hqeval v u),
      Finset.sum_add_distrib, hRrow, hddef]
    ring
  -- quantitative bounds on the defects
  have herane : ∀ v : Fin n, (Finset.univ.erase v).Nonempty := by
    intro v
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ v),
      Finset.card_univ, Fintype.card_fin]
    omega
  have heracard : ∀ v : Fin n, (Finset.univ.erase v).card = n - 1 := by
    intro v
    rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ,
      Fintype.card_fin]
  have hq0sum : ∀ v, (2:ℝ) < ∑ u, ((q0 v u : ℚ):ℝ) ∧
      (∑ u, ((q0 v u : ℚ):ℝ)) < 2 + ((n:ℝ) - 1) * η := by
    intro v
    have hdq : ((q0 v v : ℚ):ℝ) = 0 := by
      rw [hq0diag]
      norm_num
    have hsplit : ∑ u, ((q0 v u : ℚ):ℝ) = ∑ u ∈ Finset.univ.erase v, ((q0 v u : ℚ):ℝ) := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ v), hdq, zero_add]
    have hxsplit : ∑ u ∈ Finset.univ.erase v, x' v u = 2 := by
      have := hx'deg v
      have h2 : ∑ u, x' v u = x' v v + ∑ u ∈ Finset.univ.erase v, x' v u :=
        (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ v)).symm
      rw [hx'diag v] at h2
      linarith
    constructor
    · rw [hsplit, ← hxsplit]
      apply Finset.sum_lt_sum_of_nonempty (herane v)
      intro u hu
      exact hq0lb v u (Ne.symm (Finset.ne_of_mem_erase hu))
    · rw [hsplit]
      calc ∑ u ∈ Finset.univ.erase v, ((q0 v u : ℚ):ℝ)
          < ∑ u ∈ Finset.univ.erase v, (x' v u + η) := by
            apply Finset.sum_lt_sum_of_nonempty (herane v)
            intro u hu
            exact hq0ub v u (Ne.symm (Finset.ne_of_mem_erase hu))
        _ = 2 + ((n:ℝ) - 1) * η := by
            rw [Finset.sum_add_distrib, hxsplit, Finset.sum_const, heracard,
              nsmul_eq_mul]
            have hcast : ((n - 1 : ℕ) : ℝ) = (n:ℝ) - 1 := by
              push_cast [show 1 ≤ n from by omega]
              ring
            rw [hcast]
    -- (end hq0sum)
  have hdcast : ∀ v, ((d v : ℚ) : ℝ) = 2 - ∑ u, ((q0 v u : ℚ):ℝ) := by
    intro v
    rw [hddef]
    push_cast
    ring
  have hdb : ∀ v, -(((n:ℝ) - 1) * η) < ((d v : ℚ):ℝ) ∧ ((d v : ℚ):ℝ) < 0 := by
    intro v
    have h1 := (hq0sum v).1
    have h2 := (hq0sum v).2
    rw [hdcast v]
    constructor <;> linarith
  have hDb : |((D : ℚ):ℝ)| ≤ (n:ℝ) * (((n:ℝ) - 1) * η) := by
    have hcast : ((D : ℚ):ℝ) = ∑ w, ((d w : ℚ):ℝ) := by
      rw [hDdef]
      push_cast
      rfl
    rw [hcast]
    calc |∑ w, ((d w : ℚ):ℝ)| ≤ ∑ w, |((d w : ℚ):ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _w : Fin n, ((n:ℝ) - 1) * η := by
          apply Finset.sum_le_sum
          intro w _
          have := hdb w
          rw [abs_le]
          constructor <;> linarith
      _ = (n:ℝ) * (((n:ℝ) - 1) * η) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn2R : (0:ℝ) < (n:ℝ) - 2 := by linarith
  have hRb : ∀ a b, -(7 * η) ≤ ((R a b : ℚ):ℝ) ∧ ((R a b : ℚ):ℝ) ≤ 7 * η := by
    intro a b
    rw [hReval]
    by_cases h : b = a
    · rw [if_pos h]
      push_cast
      constructor
      · nlinarith [hη0]
      · nlinarith [hη0]
    · rw [if_neg h]
      set da : ℝ := ((d a : ℚ):ℝ) with hda
      set db' : ℝ := ((d b : ℚ):ℝ) with hdb'
      set D' : ℝ := ((D : ℚ):ℝ) with hD'
      have hcast : ((((d a + d b) / ((n:ℚ) - 2)
          - D / (((n:ℚ) - 1) * ((n:ℚ) - 2))) : ℚ) : ℝ)
          = (da + db') / ((n:ℝ) - 2) - D' / (((n:ℝ) - 1) * ((n:ℝ) - 2)) := by
        rw [hda, hdb', hD']
        push_cast
        ring
      rw [hcast]
      have hA1 : da + db' ≤ 0 := by
        have h1 := (hdb a).2
        have h2 := (hdb b).2
        rw [← hda] at h1
        rw [← hdb'] at h2
        linarith
      have hA2 : -(2 * (((n:ℝ) - 1) * η)) ≤ da + db' := by
        have h1 := (hdb a).1
        have h2 := (hdb b).1
        rw [← hda] at h1
        rw [← hdb'] at h2
        linarith
      have hB := hDb
      rw [abs_le] at hB
      have hval_eq : (da + db') / ((n:ℝ) - 2) - D' / (((n:ℝ) - 1) * ((n:ℝ) - 2))
          = ((da + db') * ((n:ℝ) - 1) - D') / (((n:ℝ) - 1) * ((n:ℝ) - 2)) := by
        field_simp
      rw [hval_eq]
      have hden : (0:ℝ) < ((n:ℝ) - 1) * ((n:ℝ) - 2) := mul_pos hn1R hn2R
      have hnum_ub : (da + db') * ((n:ℝ) - 1) - D' ≤ (n:ℝ) * (((n:ℝ) - 1) * η) := by
        have h1 : (da + db') * ((n:ℝ) - 1) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hA1 (by linarith)
        linarith [hB.1]
      have hnum_lb : -(2 * (((n:ℝ) - 1) * η)) * ((n:ℝ) - 1) - (n:ℝ) * (((n:ℝ) - 1) * η)
          ≤ (da + db') * ((n:ℝ) - 1) - D' := by
        have h1 : -(2 * (((n:ℝ) - 1) * η)) * ((n:ℝ) - 1) ≤ (da + db') * ((n:ℝ) - 1) :=
          mul_le_mul_of_nonneg_right hA2 (by linarith)
        linarith [hB.2]
      have hgap : (0:ℝ) ≤ η * ((n:ℝ) - 1) * (6 * (n:ℝ) - 14) := by
        apply mul_nonneg (mul_nonneg (le_of_lt hη0) (by linarith))
        linarith
      constructor
      · rw [le_div_iff₀ hden]
        nlinarith [hgap]
      · rw [div_le_iff₀ hden]
        nlinarith [hgap]
  have hqx' : ∀ u v : Fin n, u ≠ v →
      -(7 * η) ≤ ((q u v : ℚ):ℝ) - x' u v ∧ ((q u v : ℚ):ℝ) - x' u v ≤ 8 * η := by
    intro u v huv
    have hq0l := hq0lb u v huv
    have hq0u := hq0ub u v huv
    have hR := hRb u v
    have hcast : ((q u v : ℚ):ℝ) = ((q0 u v : ℚ):ℝ) + ((R u v : ℚ):ℝ) := by
      rw [hqeval]
      push_cast
      ring
    rw [hcast]
    constructor <;> linarith
  have hqnn : ∀ u v, (0:ℚ) ≤ q u v := by
    intro u v
    by_cases huv : u = v
    · rw [huv, hqdiag]
    · have h1 := (hqx' u v huv).1
      have h2 := hx'lb u v huv
      have hη20 : η ≤ μ / 20 := le_trans (min_le_left _ _) (min_le_left _ _)
      have : (0:ℝ) ≤ ((q u v : ℚ):ℝ) := by linarith
      exact_mod_cast this
  -- cut constraints
  have hqcut : ∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ →
      (2:ℚ) ≤ ∑ u ∈ S, ∑ v ∈ Sᶜ, q u v := by
    intro S hS1 hS2
    have hs1 : 1 ≤ S.card := Finset.card_pos.mpr hS1
    have hsn : S.card ≤ n - 1 := by
      have hle := Finset.card_le_univ S
      rw [Fintype.card_fin] at hle
      rcases Nat.lt_or_ge S.card n with h | h
      · omega
      · exfalso
        apply hS2
        apply Finset.eq_univ_of_card
        rw [Fintype.card_fin]
        omega
    by_cases hc1 : S.card = 1
    · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hc1
      rw [Finset.sum_singleton]
      have hsplit := Finset.sum_add_sum_compl ({v} : Finset (Fin n)) (fun w => q v w)
      rw [Finset.sum_singleton, hqdiag v, zero_add] at hsplit
      rw [hsplit, hqdeg v]
    · by_cases hc2 : S.card = n - 1
      · have hccard : Sᶜ.card = 1 := by
          rw [Finset.card_compl, Fintype.card_fin]
          omega
        obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hccard
        rw [hw]
        have hSeq : S = ({w} : Finset (Fin n))ᶜ := by
          rw [← hw, compl_compl]
        rw [hSeq]
        have hswap : ∀ u ∈ ({w} : Finset (Fin n))ᶜ, ∑ v ∈ ({w} : Finset (Fin n)),
            q u v = q w u := by
          intro u _
          rw [Finset.sum_singleton, hqsymm]
        rw [Finset.sum_congr rfl hswap]
        have hsplit := Finset.sum_add_sum_compl ({w} : Finset (Fin n)) (fun u => q w u)
        rw [Finset.sum_singleton, hqdiag w, zero_add] at hsplit
        rw [hsplit, hqdeg w]
      · -- middle case: 2 ≤ |S| ≤ n-2, so n ≥ 4
        have hs2 : 2 ≤ S.card := by omega
        have hsn2 : S.card ≤ n - 2 := by omega
        have hn4 : 4 ≤ n := by omega
        have hγeq : γ = 2 * ((n:ℝ) - 3) / ((n:ℝ) - 1) := by
          rw [hγdef, if_pos hn4]
        -- real-valued estimate
        have hkey : (2:ℝ) ≤ ∑ u ∈ S, ∑ v ∈ Sᶜ, ((q u v : ℚ):ℝ) := by
          have hpair : ∀ u ∈ S, ∀ v ∈ Sᶜ, u ≠ v := by
            intro u hu v hv hcon
            rw [hcon] at hu
            exact (Finset.mem_compl.mp hv) hu
          have hlow : ∀ u ∈ S, ∀ v ∈ Sᶜ, x' u v - 7 * η ≤ ((q u v : ℚ):ℝ) := by
            intro u hu v hv
            have := (hqx' u v (hpair u hu v hv)).1
            linarith
          have hsum1 : ∑ u ∈ S, ∑ v ∈ Sᶜ, (x' u v - 7 * η)
              ≤ ∑ u ∈ S, ∑ v ∈ Sᶜ, ((q u v : ℚ):ℝ) :=
            Finset.sum_le_sum (fun u hu => Finset.sum_le_sum (fun v hv => hlow u hu v hv))
          have hexpand : ∑ u ∈ S, ∑ v ∈ Sᶜ, (x' u v - 7 * η)
              = (∑ u ∈ S, ∑ v ∈ Sᶜ, x' u v) - (S.card * Sᶜ.card : ℕ) * (7 * η) := by
            rw [Finset.sum_congr rfl (fun u (_ : u ∈ S) =>
              Finset.sum_sub_distrib (f := fun v => x' u v) (g := fun _ => 7 * η))]
            rw [Finset.sum_sub_distrib]
            congr 1
            rw [Finset.sum_congr rfl (fun u (_ : u ∈ S) => Finset.sum_const _)]
            rw [Finset.sum_const]
            push_cast
            rw [smul_smul, nsmul_eq_mul]
            push_cast
            ring
          have hx'cut : 2 + δ * γ ≤ ∑ u ∈ S, ∑ v ∈ Sᶜ, x' u v := by
            have hxpart : (2:ℝ) ≤ ∑ u ∈ S, ∑ v ∈ Sᶜ, x u v := hxcut S hS1 hS2
            have hupart : 2 + 2 * ((n:ℝ) - 3) / ((n:ℝ) - 1)
                ≤ ∑ u ∈ S, ∑ v ∈ Sᶜ, ((uPt n u v : ℚ):ℝ) := by
              have hQ := uPt_cut_strong hn S hs2 hsn2
              have hcast : ((∑ u ∈ S, ∑ v ∈ Sᶜ, uPt n u v : ℚ):ℝ)
                  = ∑ u ∈ S, ∑ v ∈ Sᶜ, ((uPt n u v : ℚ):ℝ) := by
                push_cast
                rfl
              have hc2' : ((2 + 2 * ((n:ℚ) - 3) / ((n:ℚ) - 1) : ℚ) : ℝ)
                  = 2 + 2 * ((n:ℝ) - 3) / ((n:ℝ) - 1) := by
                push_cast
                ring
              calc 2 + 2 * ((n:ℝ) - 3) / ((n:ℝ) - 1)
                  = ((2 + 2 * ((n:ℚ) - 3) / ((n:ℚ) - 1) : ℚ) : ℝ) := hc2'.symm
                _ ≤ ((∑ u ∈ S, ∑ v ∈ Sᶜ, uPt n u v : ℚ):ℝ) := by exact_mod_cast hQ
                _ = _ := hcast
            have hsum : ∑ u ∈ S, ∑ v ∈ Sᶜ, x' u v
                = (1 - δ) * (∑ u ∈ S, ∑ v ∈ Sᶜ, x u v)
                  + δ * (∑ u ∈ S, ∑ v ∈ Sᶜ, ((uPt n u v : ℚ):ℝ)) := by
              rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro u _
              rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
            rw [hsum, hγeq]
            nlinarith [hδ0, hδ1]
          have hcard_bound : (S.card * Sᶜ.card : ℕ) ≤ n * n := by
            apply Nat.mul_le_mul
            · have := Finset.card_le_univ S
              rw [Fintype.card_fin] at this
              exact this
            · have := Finset.card_le_univ Sᶜ
              rw [Fintype.card_fin] at this
              exact this
          have hηcut : ((n * n : ℕ) : ℝ) * (7 * η) ≤ δ * γ := by
            have hη2 : η ≤ δ * γ / (20 * (n:ℝ)^2 + 20) :=
              le_trans (min_le_left _ _) (min_le_right _ _)
            have hn2pos : (0:ℝ) < 20 * (n:ℝ)^2 + 20 := by positivity
            have hδγ : 0 ≤ δ * γ := mul_nonneg (le_of_lt hδ0) (le_of_lt hγ0)
            have hcast : ((n * n : ℕ) : ℝ) = (n:ℝ)^2 := by
              push_cast
              ring
            rw [hcast]
            have h1 : (n:ℝ)^2 * (7 * η)
                ≤ (n:ℝ)^2 * (7 * (δ * γ / (20 * (n:ℝ)^2 + 20))) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              linarith
            have h2 : (n:ℝ)^2 * (7 * (δ * γ / (20 * (n:ℝ)^2 + 20))) ≤ δ * γ := by
              have heq : (n:ℝ)^2 * (7 * (δ * γ / (20 * (n:ℝ)^2 + 20)))
                  = (δ * γ) * ((7 * (n:ℝ)^2) / (20 * (n:ℝ)^2 + 20)) := by
                field_simp
              rw [heq]
              apply mul_le_of_le_one_right hδγ
              rw [div_le_one hn2pos]
              nlinarith [sq_nonneg (n:ℝ)]
            linarith
          have hcardR : ((S.card * Sᶜ.card : ℕ) : ℝ) * (7 * η)
              ≤ ((n * n : ℕ) : ℝ) * (7 * η) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact_mod_cast hcard_bound
          rw [hexpand] at hsum1
          linarith [hx'cut, hηcut, hcardR, hsum1]
        exact_mod_cast hkey
  -- cost bound
  have hqabs : ∀ u v, |((q u v : ℚ):ℝ) - x' u v| ≤ 8 * η := by
    intro u v
    by_cases huv : u = v
    · rw [huv]
      have h1 : ((q v v : ℚ):ℝ) = 0 := by
        rw [hqdiag]
        norm_num
      rw [h1, hx'diag v]
      simp only [sub_zero, abs_zero]
      positivity
    · have h := hqx' u v huv
      rw [abs_le]
      constructor <;> linarith [h.1, h.2, hη0]
  have huptx : ∀ u v, |((uPt n u v : ℚ):ℝ) - x u v| ≤ 1 := by
    intro u v
    by_cases huv : u = v
    · rw [huv, huRd v, hxd v]
      norm_num
    · rw [huR u v huv]
      have h1 := hxn u v
      have h2 := hx1 u v
      have h3 : (0:ℝ) ≤ 2 / ((n:ℝ) - 1) := by positivity
      have h4 : 2 / ((n:ℝ) - 1) ≤ 1 := by
        rw [div_le_one hn1R]
        linarith
      rw [abs_le]
      constructor <;> linarith
  have hqcost : (∑ u, ∑ v, ((q u v : ℚ):ℝ) * c u v)
      ≤ (∑ u, ∑ v, x u v * c u v) + ε := by
    have hstep1 : ∀ u v, ((q u v : ℚ):ℝ) * c u v
        ≤ x' u v * c u v + 8 * η * |c u v| := by
      intro u v
      have h1 : (((q u v : ℚ):ℝ) - x' u v) * c u v ≤ 8 * η * |c u v| := by
        calc (((q u v : ℚ):ℝ) - x' u v) * c u v
            ≤ |(((q u v : ℚ):ℝ) - x' u v) * c u v| := le_abs_self _
          _ = |((q u v : ℚ):ℝ) - x' u v| * |c u v| := abs_mul _ _
          _ ≤ 8 * η * |c u v| :=
              mul_le_mul_of_nonneg_right (hqabs u v) (abs_nonneg _)
      nlinarith [h1]
    have hstep2 : ∀ u v, x' u v * c u v
        ≤ x u v * c u v + δ * |c u v| := by
      intro u v
      have hxx : x' u v - x u v = δ * (((uPt n u v : ℚ):ℝ) - x u v) := by
        rw [hx'eval]
        ring
      have h1 : (x' u v - x u v) * c u v ≤ δ * |c u v| := by
        calc (x' u v - x u v) * c u v ≤ |(x' u v - x u v) * c u v| := le_abs_self _
          _ = |x' u v - x u v| * |c u v| := abs_mul _ _
          _ ≤ δ * 1 * |c u v| := by
              apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
              rw [hxx, abs_mul, abs_of_pos hδ0]
              apply mul_le_mul_of_nonneg_left (huptx u v) (le_of_lt hδ0)
          _ = δ * |c u v| := by ring
      nlinarith [h1]
    have hsum1 : (∑ u, ∑ v, ((q u v : ℚ):ℝ) * c u v)
        ≤ (∑ u, ∑ v, x u v * c u v) + (δ + 8 * η) * ((∑ u, ∑ v, |c u v|)) := by
      have hpt : ∀ u v, ((q u v : ℚ):ℝ) * c u v
          ≤ x u v * c u v + (δ + 8 * η) * |c u v| := by
        intro u v
        have h1 := hstep1 u v
        have h2 := hstep2 u v
        nlinarith
      calc (∑ u, ∑ v, ((q u v : ℚ):ℝ) * c u v)
          ≤ ∑ u, ∑ v, (x u v * c u v + (δ + 8 * η) * |c u v|) :=
            Finset.sum_le_sum (fun u _ => Finset.sum_le_sum (fun v _ => hpt u v))
        _ = (∑ u, ∑ v, x u v * c u v) + (δ + 8 * η) * ((∑ u, ∑ v, |c u v|)) := by
            rw [Finset.sum_congr rfl (fun u (_ : u ∈ Finset.univ) =>
              Finset.sum_add_distrib (f := fun v => x u v * c u v)
                (g := fun v => (δ + 8 * η) * |c u v|))]
            rw [Finset.sum_add_distrib]
            congr 1
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro u _
            rw [Finset.mul_sum]
    have hCb1 : (∑ u, ∑ v, |c u v|) ≤ Cb := by
      rw [hCb]
      linarith
    have hCbnn : (0:ℝ) ≤ ∑ u, ∑ v, |c u v| :=
      Finset.sum_nonneg (fun u _ => Finset.sum_nonneg (fun v _ => abs_nonneg _))
    have hηε : 8 * η * Cb ≤ ε / 5 := by
      have hη3 : η ≤ ε / (40 * Cb) := min_le_right _ _
      have h1 : 8 * η * Cb ≤ 8 * (ε / (40 * Cb)) * Cb := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt hCb0)
        linarith
      have h2 : 8 * (ε / (40 * Cb)) * Cb = ε / 5 := by
        field_simp
        ring
      linarith
    have hfinal : (δ + 8 * η) * (∑ u, ∑ v, |c u v|) ≤ ε / 2 + ε / 5 := by
      have h1 : (δ + 8 * η) * (∑ u, ∑ v, |c u v|) ≤ (δ + 8 * η) * Cb := by
        apply mul_le_mul_of_nonneg_left hCb1
        have := hη0
        have := hδ0
        linarith
      have h2 : (δ + 8 * η) * Cb = δ * Cb + 8 * η * Cb := by ring
      linarith [hδε, hηε]
    calc (∑ u, ∑ v, ((q u v : ℚ):ℝ) * c u v)
        ≤ (∑ u, ∑ v, x u v * c u v) + (δ + 8 * η) * ((∑ u, ∑ v, |c u v|)) := hsum1
      _ ≤ (∑ u, ∑ v, x u v * c u v) + (ε / 2 + ε / 5) := by linarith
      _ ≤ (∑ u, ∑ v, x u v * c u v) + ε := by linarith
  refine ⟨q, hqsymm, hqdiag, hqnn, hqdeg, hqcut, ?_⟩
  have hcastsum : (∑ u, ∑ v, ((q u v : ℚ):ℝ) * c u v)
      = ∑ u, ∑ v, ((q u v : ℚ):ℝ) * c u v := rfl
  exact hqcost

/-- Scale a rational Held–Karp point to an integer multigraph. -/
lemma scale_to_multigraph (hn : 3 ≤ n) (q : Fin n → Fin n → ℚ)
    (hsym : ∀ u v, q u v = q v u) (hdiag : ∀ v, q v v = 0)
    (hnn : ∀ u v, 0 ≤ q u v) (hdeg : ∀ v, ∑ u, q v u = 2)
    (hcut : ∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ →
      2 ≤ ∑ u ∈ S, ∑ v ∈ Sᶜ, q u v) :
    ∃ (N : ℕ) (H : Fin n → Fin n → ℕ), 1 ≤ N ∧
      (∀ u v, ((H u v : ℕ) : ℚ) = q u v * N) ∧
      (∀ u v, H u v = H v u) ∧ (∀ v, H v v = 0) ∧
      (∀ v, ∑ u, H v u = 2 * N) ∧
      (∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ →
        2 * N ≤ ∑ u ∈ S, ∑ v ∈ Sᶜ, H u v) := by
  classical
  set N : ℕ := ∏ p ∈ (Finset.univ ×ˢ Finset.univ : Finset (Fin n × Fin n)),
    (q p.1 p.2).den with hNdef
  have hN1 : 1 ≤ N := by
    rw [hNdef]
    apply Nat.one_le_iff_ne_zero.mpr
    apply Finset.prod_ne_zero_iff.mpr
    intro p _
    exact (q p.1 p.2).den_nz
  have hdvd : ∀ u v, (q u v).den ∣ N := by
    intro u v
    rw [hNdef]
    exact Finset.dvd_prod_of_mem (f := fun p => (q p.1 p.2).den) (a := (u, v))
      (by
        rw [Finset.mem_product]
        exact ⟨Finset.mem_univ u, Finset.mem_univ v⟩)
  set H : Fin n → Fin n → ℕ := fun u v => (q u v).num.toNat * (N / (q u v).den)
    with hHdef
  have hHcast : ∀ u v, ((H u v : ℕ) : ℚ) = q u v * N := by
    intro u v
    have hnum : (0:ℤ) ≤ (q u v).num := Rat.num_nonneg.mpr (hnn u v)
    have hden0 : ((q u v).den : ℚ) ≠ 0 := by
      exact_mod_cast (q u v).den_nz
    show (((q u v).num.toNat * (N / (q u v).den) : ℕ) : ℚ) = q u v * N
    have htn : (((q u v).num.toNat : ℕ) : ℚ) = ((q u v).num : ℚ) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) (Int.toNat_of_nonneg hnum)
    push_cast
    rw [htn, Nat.cast_div (hdvd u v) hden0]
    conv_rhs => rw [← Rat.num_div_den (q u v)]
    ring
  have hHsym : ∀ u v, H u v = H v u := by
    intro u v
    show (q u v).num.toNat * (N / (q u v).den) = (q v u).num.toNat * (N / (q v u).den)
    rw [hsym u v]
  have hHdiag : ∀ v, H v v = 0 := by
    intro v
    show (q v v).num.toNat * (N / (q v v).den) = 0
    rw [hdiag v]
    norm_num
  have hHdeg : ∀ v, ∑ u, H v u = 2 * N := by
    intro v
    have hQ : ((∑ u, H v u : ℕ) : ℚ) = ((2 * N : ℕ) : ℚ) := by
      push_cast
      calc ∑ u, ((H v u : ℕ):ℚ) = ∑ u, q v u * N := by
            apply Finset.sum_congr rfl
            intro u _
            exact hHcast v u
        _ = (∑ u, q v u) * N := by rw [Finset.sum_mul]
        _ = 2 * N := by rw [hdeg v]
    exact_mod_cast hQ
  have hHcut : ∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ →
      2 * N ≤ ∑ u ∈ S, ∑ v ∈ Sᶜ, H u v := by
    intro S h1 h2
    have hQ : ((2 * N : ℕ) : ℚ) ≤ ((∑ u ∈ S, ∑ v ∈ Sᶜ, H u v : ℕ) : ℚ) := by
      push_cast
      have hqc := hcut S h1 h2
      calc (2 : ℚ) * N ≤ (∑ u ∈ S, ∑ v ∈ Sᶜ, q u v) * N := by
            apply mul_le_mul_of_nonneg_right hqc
            exact_mod_cast Nat.zero_le N
        _ = ∑ u ∈ S, ∑ v ∈ Sᶜ, ((q u v) * N) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro u _
            rw [Finset.sum_mul]
        _ = ∑ u ∈ S, ∑ v ∈ Sᶜ, ((H u v : ℕ):ℚ) := by
            apply Finset.sum_congr rfl
            intro u _
            apply Finset.sum_congr rfl
            intro v _
            exact (hHcast u v).symm
    exact_mod_cast hQ
  exact ⟨N, H, hN1, hHcast, hHsym, hHdiag, hHdeg, hHcut⟩

/-- **The parity correction.** A perfect matching on any even city set within
half the Held–Karp objective. -/
theorem parity_matching_thm (n : ℕ) (hn : 3 ≤ n) (c : Fin n → Fin n → ℝ)
    (hc : IsMetricCost c) (x : Fin n → Fin n → ℝ) (hx : IsHeldKarp x)
    (T : Finset (Fin n)) (hT : Even T.card) :
    ∃ f : Fin n → Fin n, (∀ v ∈ T, f v ∈ T ∧ f (f v) = v ∧ f v ≠ v) ∧
      (∀ v ∉ T, f v = v) ∧
      ∑ v ∈ T, c v (f v) ≤ (1 / 2) * ∑ u, ∑ v, c u v * x u v := by
  have hc0 : ∀ u v, 0 ≤ c u v := by
    intro u v
    have h1 := hc.2.2 u v u
    have h2 := hc.2.1 u
    have h3 := hc.1 v u
    nlinarith
  have hB0 : 0 ≤ (1 / 2) * ∑ u, ∑ v, c u v * x u v := by
    have h : 0 ≤ ∑ u, ∑ v, c u v * x u v :=
      Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ =>
        mul_nonneg (hc0 u v) (hx.2.2.1 u v)
    linarith
  rcases Finset.eq_empty_or_nonempty T with rfl | hTne
  · refine ⟨id, fun v hv => absurd hv (Finset.notMem_empty v), fun v _ => rfl, ?_⟩
    rw [Finset.sum_empty]
    exact hB0
  · have heps : ∀ ε : ℝ, 0 < ε → ∃ f : Fin n → Fin n, IsPairing T f ∧
        ∑ v ∈ T, c v (f v) ≤ (1 / 2) * (∑ u, ∑ v, c u v * x u v) + ε := by
      intro ε hε
      have hxc_comm : ∑ u, ∑ v, x u v * c u v = ∑ u, ∑ v, c u v * x u v := by
        apply Finset.sum_congr rfl
        intro u _
        apply Finset.sum_congr rfl
        intro v _
        ring
      obtain ⟨q, hqs, hqd, hqn, hqdeg, hqcut, hqcost⟩ :=
        rationalize hn c x hx ε hε
      obtain ⟨N, H, hN1, hHcast, hHs, hHd, hHdeg, hHcut⟩ :=
        scale_to_multigraph hn q hqs hqd hqn hqdeg hqcut
      have hNR : (0:ℝ) < 2 * N := by
        have : (1:ℝ) ≤ N := by exact_mod_cast hN1
        linarith
      have hcutT : ∀ S : Finset (Fin n), (S ∩ T).Nonempty → (Sᶜ ∩ T).Nonempty →
          2 * N ≤ ∑ u ∈ S, ∑ v ∈ Sᶜ, H u v := by
        intro S h1 h2
        apply hHcut S
        · obtain ⟨a, ha⟩ := h1
          exact ⟨a, (Finset.mem_inter.mp ha).1⟩
        · obtain ⟨b, hb⟩ := h2
          intro hcon
          have hbS := (Finset.mem_inter.mp hb).1
          rw [hcon, Finset.compl_univ] at hbS
          exact Finset.notMem_empty b hbS
      have heven : ∀ v, Even (∑ u, H v u) := by
        intro v
        rw [hHdeg v]
        exact ⟨N, by ring⟩
      have hT2 : 2 ≤ T.card := by
        rcases hT with ⟨t, ht⟩
        have h1 : 1 ≤ T.card := Finset.card_pos.mpr hTne
        omega
      obtain ⟨H', hH's, hH'd, hH'supp, hH'deg, hH'cut, hH'cost⟩ :=
        eliminate_steiner2 n c hc T hT2 N hN1 H hHs hHd hHdeg hcutT
      set y : Fin n → Fin n → ℝ := fun u v => (H' u v : ℝ) / (2 * N) with hydef
      have hyeval : ∀ u v, y u v = (H' u v : ℝ) / (2 * N) := fun u v => rfl
      have hysym : ∀ u v, y u v = y v u := by
        intro u v
        rw [hyeval, hyeval, hH's u v]
      have hynn : ∀ u v, 0 ≤ y u v := by
        intro u v
        rw [hyeval]
        positivity
      have hydiag : ∀ v, y v v = 0 := by
        intro v
        rw [hyeval, hH'd v]
        norm_num
      have hysupp : ∀ u v, y u v ≠ 0 → u ∈ T ∧ v ∈ T := by
        intro u v hne
        apply hH'supp
        intro hz
        apply hne
        rw [hyeval, hz]
        norm_num
      have hydeg : ∀ v ∈ T, ∑ u, y v u = 1 := by
        intro v hv
        have hsum : ∑ u, (H' v u : ℝ) = ((∑ u, H' v u : ℕ) : ℝ) := by
          push_cast
          rfl
        rw [Finset.sum_congr rfl (fun u (_ : u ∈ Finset.univ) => hyeval v u),
          ← Finset.sum_div, hsum, hH'deg v hv]
        push_cast
        field_simp
      have hycut : ∀ S : Finset (Fin n), S ⊆ T → S.Nonempty → S ≠ T →
          1 ≤ ∑ u ∈ S, ∑ v ∈ T \ S, y u v := by
        intro S hsub hne hneT
        have hTS : (T \ S).Nonempty := by
          rw [Finset.sdiff_nonempty]
          intro hcon
          exact hneT (Finset.Subset.antisymm hsub hcon)
        have hHkey := hH'cut S (by
            obtain ⟨a, ha⟩ := hne
            exact ⟨a, Finset.mem_inter.mpr ⟨ha, hsub ha⟩⟩) (by
            obtain ⟨t, ht⟩ := hTS
            rw [Finset.mem_sdiff] at ht
            exact ⟨t, Finset.mem_inter.mpr ⟨Finset.mem_compl.mpr ht.2, ht.1⟩⟩)
        -- restrict the complement sum to T \ S
        have hrestrict : ∀ u ∈ S, ∑ v ∈ Sᶜ, (H' u v : ℝ) = ∑ v ∈ T \ S, (H' u v : ℝ) := by
          intro u _
          apply (Finset.sum_subset ?_ ?_).symm
          · intro v hv
            rw [Finset.mem_sdiff] at hv
            exact Finset.mem_compl.mpr hv.2
          · intro v hv hnv
            rw [Finset.mem_compl] at hv
            rw [Finset.mem_sdiff] at hnv
            push_neg at hnv
            by_contra hnz
            have hvT := (hH'supp u v (by
              intro hz
              apply hnz
              rw [hz]
              norm_num)).2
            exact hv (hnv hvT)
        have hcast : ((∑ u ∈ S, ∑ v ∈ Sᶜ, H' u v : ℕ) : ℝ) ≥ ((2 * N : ℕ) : ℝ) := by
          exact_mod_cast hHkey
        have hsplit : ∑ u ∈ S, ∑ v ∈ T \ S, y u v
            = (∑ u ∈ S, ∑ v ∈ Sᶜ, (H' u v : ℝ)) / (2 * N) := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro u hu
          rw [hrestrict u hu, Finset.sum_div]
        rw [hsplit]
        rw [ge_iff_le] at hcast
        have hc2 : ((2 * N : ℕ) : ℝ) = 2 * N := by push_cast; ring
        have hc3 : ((∑ u ∈ S, ∑ v ∈ Sᶜ, H' u v : ℕ) : ℝ)
            = ∑ u ∈ S, ∑ v ∈ Sᶜ, (H' u v : ℝ) := by
          push_cast
          rfl
        rw [le_div_iff₀ hNR]
        rw [hc2, hc3] at hcast
        linarith
      obtain ⟨f, hf1, hf2, hfcost⟩ := even_set_matching n c hc T hT hTne y
        hysym hynn hydiag hysupp hydeg hycut
      refine ⟨f, ⟨hf1, hf2⟩, ?_⟩
      -- cost chain
      have hHR : ∀ u v, (H u v : ℝ) = ((q u v : ℚ) : ℝ) * N := by
        intro u v
        have := hHcast u v
        have hcast2 : ((H u v : ℕ) : ℝ) = (((q u v * N : ℚ)) : ℝ) := by
          exact_mod_cast congrArg (fun z : ℚ => (z : ℝ)) this
        rw [hcast2]
        push_cast
        ring
      have hyc : ∑ u, ∑ v, y u v * c u v ≤ (∑ u, ∑ v, ((q u v : ℚ):ℝ) * c u v) / 2 := by
        have h1 : ∑ u, ∑ v, y u v * c u v
            = (∑ u, ∑ v, (H' u v : ℝ) * c u v) / (2 * N) := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro u _
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro v _
          rw [hyeval]
          ring
        have h2 : ∑ u, ∑ v, (H u v : ℝ) * c u v
            = N * (∑ u, ∑ v, ((q u v : ℚ):ℝ) * c u v) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro u _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro v _
          rw [hHR u v]
          ring
        rw [h1]
        rw [div_le_div_iff₀ hNR (by norm_num : (0:ℝ) < 2)]
        have h3 := hH'cost
        calc (∑ u, ∑ v, (H' u v : ℝ) * c u v) * 2
            ≤ (∑ u, ∑ v, (H u v : ℝ) * c u v) * 2 := by linarith
          _ = (∑ u, ∑ v, ((q u v : ℚ):ℝ) * c u v) * (2 * N) := by
              rw [h2]
              ring
      have hεhalf : (∑ u, ∑ v, ((q u v : ℚ):ℝ) * c u v) / 2
          ≤ (1 / 2) * ∑ u, ∑ v, c u v * x u v + ε := by
        rw [← hxc_comm]
        linarith [hqcost]
      calc ∑ v ∈ T, c v (f v) ≤ ∑ u, ∑ v, y u v * c u v := hfcost
        _ ≤ (∑ u, ∑ v, ((q u v : ℚ):ℝ) * c u v) / 2 := hyc
        _ ≤ (1 / 2) * ∑ u, ∑ v, c u v * x u v + ε := hεhalf

    obtain ⟨f, hf, hcost⟩ := pairing_of_eps c T hT
      ((1 / 2) * ∑ u, ∑ v, c u v * x u v) heps
    exact ⟨f, hf.1, hf.2, hcost⟩

end MetricTSP

open MetricTSP

theorem solution (n : ℕ) (hn : 3 ≤ n) (c : Fin n → Fin n → ℝ)
    (hc : IsMetricCost c) (x : Fin n → Fin n → ℝ) (hx : IsHeldKarp x)
    (T : Finset (Fin n)) (hT : Even T.card) :
    ∃ f : Fin n → Fin n, (∀ v ∈ T, f v ∈ T ∧ f (f v) = v ∧ f v ≠ v) ∧
      (∀ v ∉ T, f v = v) ∧
      ∑ v ∈ T, c v (f v) ≤ (1 / 2) * ∑ u, ∑ v, c u v * x u v :=
  MetricTSP.parity_matching_thm n hn c hc x hx T hT
