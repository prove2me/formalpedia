-- Prove2me | solution 1 for OAI.Blocks.block_estimates
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T14:47:57.105101+00:00
-- url     : https://prove2.me/submissions/1d1dd7c5-f768-4a34-bfc2-597eb0276f6d

import Mathlib
import Definitions.Def_OAIQ16Cd000

section
-- module Solutions.OAIQ16_CD.Compat
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_BlockTerminal
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1

namespace BlockTerminal
open Finset
variable {I : Type u_1} [Fintype I] [DecidableEq I]

lemma merge_exists (P : Finpartition (univ : Finset I))
    (H : Finset (Finset I)) (hH : H ⊆ P.parts) (hH2 : 2 ≤ H.card) :
    ∃ Q : Finpartition (univ : Finset I),
      Q.parts = insert (H.biUnion id) (P.parts \ H) ∧ Q.parts.card < P.parts.card := by
  classical
  let W := H.biUnion id
  have hHne : H.Nonempty := card_pos.mp (by omega)
  have hW : W.Nonempty := by
    obtain ⟨A, hAH⟩ := hHne
    obtain ⟨i, hi⟩ := P.nonempty_of_mem_parts (hH hAH)
    exact ⟨i, mem_biUnion.mpr ⟨A, hAH, hi⟩⟩
  have hcover (i : I) : ∃! A, A ∈ insert W (P.parts \ H) ∧ i ∈ A := by
    obtain ⟨A, hA, hiA⟩ := P.exists_mem (mem_univ i)
    by_cases hAH : A ∈ H
    · refine ⟨W, ⟨mem_insert_self _ _, mem_biUnion.mpr ⟨A, hAH, hiA⟩⟩, ?_⟩
      rintro B ⟨hB, hiB⟩
      rcases mem_insert.mp hB with rfl | hB
      · rfl
      · have hBA := P.eq_of_mem_parts (mem_sdiff.mp hB).1 hA hiB hiA
        exact False.elim ((mem_sdiff.mp hB).2 (hBA ▸ hAH))
    · refine ⟨A, ⟨mem_insert_of_mem (mem_sdiff.mpr ⟨hA,hAH⟩), hiA⟩, ?_⟩
      rintro B ⟨hB, hiB⟩
      rcases mem_insert.mp hB with hBW | hB
      · rw [hBW] at hiB
        obtain ⟨C, hCH, hiC⟩ := mem_biUnion.mp hiB
        have hCA := P.eq_of_mem_parts (hH hCH) hA hiC hiA
        exact False.elim (hAH (hCA ▸ hCH))
      · exact P.eq_of_mem_parts (mem_sdiff.mp hB).1 hA hiB hiA
  let Q := Finpartition.ofExistsUnique (insert W (P.parts \ H))
    (fun _ _ => subset_univ _) (fun i _ => hcover i) (by
      simp only [Finset.mem_insert, Finset.mem_sdiff, not_or]
      exact ⟨fun he => hW.ne_empty he.symm, fun h => P.empty_notMem_parts h.1⟩)
  refine ⟨Q, rfl, ?_⟩
  change (insert W (P.parts \ H)).card < P.parts.card
  have hcard := card_sdiff_add_card_eq_card hH
  have hins := card_insert_le W (P.parts \ H)
  omega

lemma exists_terminal (Good : Finset I → Prop) (hsingle : ∀ i, Good {i}) :
    ∃ P : Finpartition (univ : Finset I),
      (∀ S ∈ P.parts, Good S) ∧
      ∀ H ⊆ P.parts, 2 ≤ H.card → ¬Good (H.biUnion id) := by
  classical
  have hex : ∃ k : ℕ, ∃ P : Finpartition (univ : Finset I),
      (∀ S ∈ P.parts, Good S) ∧ P.parts.card = k := by
    refine ⟨(⊥ : Finpartition (univ : Finset I)).parts.card, ⊥, ?_, rfl⟩
    intro S hS
    rw [Finpartition.parts_bot] at hS
    obtain ⟨i, _, hi⟩ := mem_map.mp hS
    simpa only [Function.Embedding.coeFn_mk, ← hi] using hsingle i
  obtain ⟨P, hP, hc⟩ := Nat.find_spec hex
  refine ⟨P, hP, ?_⟩
  intro H hH hH2 hg
  obtain ⟨Q, hQ, hlt⟩ := merge_exists P H hH hH2
  have hQgood : ∀ S ∈ Q.parts, Good S := by
    intro S hS
    rw [hQ] at hS
    rcases mem_insert.mp hS with rfl | hS
    · exact hg
    · exact hP S (mem_sdiff.mp hS).1
  have hmin := Nat.find_min' hex ⟨Q, hQgood, rfl⟩
  omega

end BlockTerminal

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_BlockGeometry
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1

namespace BlockGeometry
open Finset
variable {I : Type u_1}

lemma radius_nonneg (d : I → I → ℝ) (S : Finset I) : 0 ≤ radius d S := by
  classical
  unfold radius
  split_ifs with h
  · apply le_inf'
    intro j _
    obtain ⟨i,hi⟩ := h
    exact (sq_nonneg _).trans (le_sup' (fun i => d j i ^ 2) hi)
  · rfl

lemma radius_le (d : I → I → ℝ) {S : Finset I} {j : I} (hj : j ∈ S)
    {R : ℝ} (hR : ∀ i ∈ S, d j i ^ 2 ≤ R) : radius d S ≤ R := by
  classical
  have hS : S.Nonempty := ⟨j,hj⟩
  rw [radius, dite_eq_left hS]
  exact (inf'_le _ hj).trans (sup'_le _ _ hR)

lemma exists_center (d : I → I → ℝ) {S : Finset I} (hS : S.Nonempty) :
    ∃ j ∈ S, ∀ i ∈ S, d j i ^ 2 ≤ radius d S := by
  classical
  obtain ⟨j,hj,he⟩ := exists_mem_eq_inf' hS (fun j => S.sup' hS (fun i => d j i ^ 2))
  refine ⟨j,hj,fun i hi => ?_⟩
  rw [radius, dite_eq_left hS, he]
  exact le_sup' (fun i => d j i ^ 2) hi

lemma radius_singleton (d : I → I → ℝ) (hd : ∀ i, d i i = 0) (i : I) :
    radius d {i} = 0 := by
  exact le_antisymm (radius_le d (mem_singleton_self _) (by simp [hd]))
    (radius_nonneg d _)

lemma anchor_distance (d : I → I → ℝ) (hn : ∀ i j, 0 ≤ d i j)
    (hs : ∀ i j, d i j = d j i)
    (ht : ∀ i j k, d i k ≤ d i j + d j k)
    {S : Finset I} {a i : I} (ha : a ∈ S) (hi : i ∈ S) :
    d a i ≤ 2*Real.sqrt (radius d S) := by
  obtain ⟨j,_,hj⟩ := exists_center d ⟨a,ha⟩
  have hja : d j a ≤ Real.sqrt (radius d S) :=
    (Real.le_sqrt (hn j a) (radius_nonneg d S)).mpr (hj a ha)
  have hji : d j i ≤ Real.sqrt (radius d S) :=
    (Real.le_sqrt (hn j i) (radius_nonneg d S)).mpr (hj i hi)
  have := ht a j i
  rw [hs a j] at this
  linarith

lemma loss_nonneg {L : ℝ} (hL : 0 ≤ L) (d : I → I → ℝ) (S : Finset I) :
    0 ≤ loss L d S := by
  unfold loss
  split_ifs with h
  · rfl
  · apply mul_nonneg hL
    have hc : (1:ℝ) ≤ S.card := by exact_mod_cast (by omega : 1 ≤ S.card)
    have := Real.log_nonneg hc
    have := radius_nonneg d S
    linarith

lemma radius_le_loss {L : ℝ} (hL : 0 < L) (d : I → I → ℝ)
    (hd : ∀ i, d i i = 0) (S : Finset I) : radius d S ≤ loss L d S / L := by
  classical
  unfold loss
  split_ifs with h
  · by_cases he : S = ∅
    · simp [he, radius]
    · have hc : S.card = 1 := by have := card_pos.mpr (nonempty_iff_ne_empty.mpr he); omega
      obtain ⟨i,rfl⟩ := card_eq_one.mp hc
      simp [radius_singleton d hd]
  · rw [mul_div_cancel_left₀ _ hL.ne']
    have hc : (1:ℝ) ≤ S.card := by exact_mod_cast (by omega : 1 ≤ S.card)
    have := Real.log_nonneg hc
    linarith

lemma loss_singleton (L : ℝ) (d : I → I → ℝ) (i : I) : loss L d {i} = 0 := by
  simp [loss]

lemma exists_terminal [Fintype I] [DecidableEq I] {L ζ R : ℝ} (hR : 0 ≤ R) (hζ : 0 ≤ ζ)
    (d : I → I → ℝ) (hd : ∀ i, d i i = 0) :
    ∃ P : Finpartition (univ : Finset I),
      (∀ S ∈ P.parts, radius d S ≤ R ∧ loss L d S ≤ ζ*S.card) ∧
      ∀ H ⊆ P.parts, 2 ≤ H.card →
        ¬(radius d (H.biUnion id) ≤ R ∧ loss L d (H.biUnion id) ≤ ζ*(H.biUnion id).card) := by
  apply BlockTerminal.exists_terminal
  intro i
  simp only [radius_singleton d hd, loss_singleton, Finset.card_singleton, Nat.cast_one, mul_one]
  exact ⟨hR,hζ⟩

lemma nearby_union_radius [DecidableEq I] {L t u : ℝ} (hL : 0 < L) (ht : 0 ≤ t) (hu : 0 ≤ u)
    (d : I → I → ℝ) (hn : ∀ i j, 0 ≤ d i j) (hd : ∀ i, d i i = 0)
    (hs : ∀ i j, d i j = d j i) (htri : ∀ i j k, d i k ≤ d i j+d j k)
    (H : Finset (Finset I)) (hH : H.Nonempty) (a : Finset I → I) (z : I)
    (ha : ∀ S ∈ H, a S ∈ S)
    (hclose : ∀ S ∈ H, d z (a S)^2 ≤ t)
    (hloss : ∀ S ∈ H, loss L d S ≤ u) :
    radius d (H.biUnion id) ≤ 8*t+8*u/L := by
  obtain ⟨S0,hS0⟩ := hH
  have ha0 : a S0 ∈ H.biUnion id := mem_biUnion.mpr ⟨S0,hS0,ha S0 hS0⟩
  apply radius_le d ha0
  intro i hi
  obtain ⟨S,hS,hiS⟩ := mem_biUnion.mp hi
  have h0 : d (a S0) z ≤ Real.sqrt t := by
    rw [hs]
    exact (Real.le_sqrt (hn _ _) ht).mpr (hclose _ hS0)
  have h1 : d z (a S) ≤ Real.sqrt t :=
    (Real.le_sqrt (hn _ _) ht).mpr (hclose _ hS)
  have h2 : d (a S) i ≤ 2*Real.sqrt (u/L) := by
    apply (anchor_distance d hn hs htri (ha S hS) hiS).trans
    apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt _) (by norm_num)
    exact (radius_le_loss hL d hd S).trans ((div_le_div_iff_of_pos_right hL).mpr (hloss S hS))
  have h3 := htri (a S0) z i
  have h4 := htri z (a S) i
  have hb : d (a S0) i ≤ 2*Real.sqrt t+2*Real.sqrt (u/L) := by linarith
  have hz := hn (a S0) i
  have hsqt := Real.sq_sqrt ht
  have hsqu := Real.sq_sqrt (div_nonneg hu hL.le)
  have hab := sq_nonneg (Real.sqrt t-Real.sqrt (u/L))
  have he : d (a S0) i ^ 2 ≤ (2*Real.sqrt t+2*Real.sqrt (u/L))^2 :=
    pow_le_pow_left₀ hz hb 2
  calc
    _ ≤ (2*Real.sqrt t+2*Real.sqrt (u/L))^2 := he
    _ ≤ 8*t+8*(u/L) := by nlinarith [hab]
    _ = _ := by ring

end BlockGeometry

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_BlockCount
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1

namespace BlockCount
open Finset Filter BlockGeometry
open scoped Topology
variable {I : Type u_1} [DecidableEq I] [Fintype I]

omit [DecidableEq I] [Fintype I] in
lemma log_absorption {L ζ : ℝ} (hL : 0 < L) (hζ : 0 < ζ) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → L*Real.log N ≤ ζ*N/2 := by
  have hlim : Tendsto (fun N : ℕ => Real.log N / N) atTop (nhds 0) := by
    simpa only [Function.comp_def, one_mul, add_zero, pow_one] using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hev := hlim.eventually_lt_const (div_pos hζ (by positivity : (0:ℝ)<2*L))
  obtain ⟨N0,hN0⟩ := eventually_atTop.mp hev
  refine ⟨max N0 2, le_max_right _ _, ?_⟩
  intro N hN
  have hn : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
  have hh := hN0 N (le_trans (le_max_left _ _) hN)
  have hh' := (div_lt_iff₀ hn).mp hh
  have he : L * (ζ/(2*L)*(N:ℝ)) = ζ*N/2 := by field_simp
  rw [← he]
  exact (mul_le_mul_of_nonneg_left hh'.le hL.le)

lemma subfamily_card_union (P : Finpartition (univ : Finset I))
    (H : Finset (Finset I)) (hH : H ⊆ P.parts) : H.card ≤ (H.biUnion id).card := by
  apply card_le_card_biUnion
  · intro S hS T hT hST
    exact P.disjoint (hH hS) (hH hT) hST
  · intro S hS
    exact P.nonempty_of_mem_parts (hH hS)

lemma terminal_count {L ζ R t u : ℝ} (hL : 0 < L) (hζ : 0 < ζ)
    (ht : 0 ≤ t) (hu : 0 ≤ u)
    (d : I → I → ℝ) (hn : ∀ i j, 0 ≤ d i j) (hd : ∀ i, d i i = 0)
    (hs : ∀ i j, d i j = d j i) (htri : ∀ i j k, d i k ≤ d i j+d j k)
    (P : Finpartition (univ : Finset I))
    (hterm : ∀ H ⊆ P.parts, 2 ≤ H.card →
      ¬(radius d (H.biUnion id) ≤ R ∧ loss L d (H.biUnion id) ≤ ζ*(H.biUnion id).card))
    (N0 : ℕ) (hN02 : 2 ≤ N0)
    (hlog : ∀ N : ℕ, N0 ≤ N → L*Real.log N ≤ ζ*N/2)
    (H : Finset (Finset I)) (hH : H ⊆ P.parts) (a : Finset I → I) (z : I)
    (ha : ∀ S ∈ H, a S ∈ S)
    (hc : ∀ S ∈ H, d z (a S)^2 ≤ t)
    (hloss : ∀ S ∈ H, loss L d S ≤ u)
    (hR : 8*t+8*u/L ≤ R) :
    (H.card : ℝ) < N0 + (2*L/ζ)*(1+8*t+8*u/L) := by
  by_cases hsmall : H.card < N0
  · have hnonneg : 0 ≤ (2*L/ζ)*(1+8*t+8*u/L) := by positivity
    have hcast : (H.card:ℝ)<N0 := by exact_mod_cast hsmall
    linarith
  · have hN0H : N0 ≤ H.card := by omega
    by_contra! hbig
    have hH2 : 2 ≤ H.card := hN02.trans hN0H
    have hHne : H.Nonempty := card_pos.mp (by omega)
    have hrad := nearby_union_radius hL ht hu d hn hd hs htri H hHne a z ha hc hloss
    have hcard := subfamily_card_union P H hH
    have hN0W := hN0H.trans hcard
    have hlogW := hlog _ hN0W
    have hNc : (H.card:ℝ) ≤ (H.biUnion id).card := by exact_mod_cast hcard
    have hN0nonneg : (0:ℝ) ≤ N0 := Nat.cast_nonneg _
    have hlarge : (2*L/ζ)*(1+8*t+8*u/L) ≤ (H.biUnion id).card := by linarith
    have hm : L*(1+8*t+8*u/L) ≤ ζ*(H.biUnion id).card/2 := by
      have hmul := mul_le_mul_of_nonneg_left hlarge hζ.le
      have he : ζ*((2*L/ζ)*(1+8*t+8*u/L)) = 2*(L*(1+8*t+8*u/L)) := by
        field_simp
      rw [he] at hmul
      linarith
    apply hterm H hH hH2
    refine ⟨hrad.trans hR, ?_⟩
    rw [loss, ite_eq_right (by omega)]
    have hrm := mul_le_mul_of_nonneg_left hrad hL.le
    nlinarith

end BlockCount

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_RowGrouping
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2

namespace RowGrouping
open Finset
lemma binary_sum (q : ℝ) (J : ℕ) :
    ∑ k ∈ range J, (q+k+1)*(1/2:ℝ)^k =
      2*q+4-(2*q+2*J+4)*(1/2:ℝ)^J := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [sum_range_succ, ih, pow_succ]
    push_cast
    ring

lemma binary_sum_le {q : ℝ} (hq : 0 ≤ q) (J : ℕ) :
    ∑ k ∈ range J, (q+k+1)*(1/2:ℝ)^k ≤ 2*q+4 := by
  rw [binary_sum]
  have hp : 0 ≤ (2*q+2*J+4)*(1/2:ℝ)^J := by positivity
  linarith

lemma weight_decompose {w : ℝ} (hw : w ≤ 1) (J : ℕ) :
    w ≤ (1/2:ℝ)^J + ∑ k ∈ range J, if (1/2:ℝ)^(k+1) < w then (1/2:ℝ)^k else 0 := by
  induction J with
  | zero => simpa using hw
  | succ J ih =>
    rw [sum_range_succ]
    by_cases h : (1/2:ℝ)^(J+1)<w
    · rw [ite_eq_left h]
      have hp : 0 ≤ (1/2:ℝ)^(J+1) := by positivity
      linarith
    · rw [ite_eq_right h]
      have hp : 0 ≤ ∑ k ∈ range J, if (1/2:ℝ)^(k+1)<w then (1/2:ℝ)^k else 0 := by
        apply sum_nonneg
        intro k _
        split_ifs <;> positivity
      linarith

lemma sum_bound {T : Type u_1} (S : Finset T) (w : T → ℝ)
    (hw : ∀ i ∈ S, w i ≤ 1) {C q : ℝ} (hC : 0 ≤ C) (hq : 0 ≤ q)
    (J : ℕ) (hcount : ∀ k < J,
      ((S.filter fun i => (1/2:ℝ)^(k+1)<w i).card : ℝ) ≤ C*(q+k+1)) :
    ∑ i ∈ S, w i ≤ S.card*(1/2:ℝ)^J+C*(2*q+4) := by
  classical
  calc
    _ ≤ ∑ i ∈ S, ((1/2:ℝ)^J+∑ k ∈ range J,
        if (1/2:ℝ)^(k+1)<w i then (1/2:ℝ)^k else 0) :=
      sum_le_sum fun i hi => weight_decompose (hw i hi) J
    _ = S.card*(1/2:ℝ)^J + ∑ k ∈ range J,
        ((S.filter fun i => (1/2:ℝ)^(k+1)<w i).card : ℝ)*(1/2:ℝ)^k := by
      rw [sum_add_distrib, sum_comm]
      simp only [sum_const, nsmul_eq_mul]
      congr 1
      apply sum_congr rfl
      intro k _
      rw [← sum_filter]
      simp
    _ ≤ S.card*(1/2:ℝ)^J + ∑ k ∈ range J, C*(q+k+1)*(1/2:ℝ)^k := by
      gcongr with k hk
      exact hcount k (mem_range.mp hk)
    _ = S.card*(1/2:ℝ)^J + C*(∑ k ∈ range J, (q+k+1)*(1/2:ℝ)^k) := by
      rw [mul_sum]
      congr 1
      apply sum_congr rfl
      intro _ _
      ring
    _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_left (binary_sum_le hq J) hC) _

lemma log_row {T : Type u_2} (S : Finset T) (w : T → ℝ)
    (hn : ∀ i ∈ S, 0 ≤ w i) (hw : ∀ i ∈ S, w i ≤ 1)
    {C q q0 : ℝ} (hC : 0 ≤ C) (hq0 : 0 < q0) (hq : q0 ≤ q)
    (J : ℕ) (htail : (S.card:ℝ)*(1/2:ℝ)^J ≤ 1)
    (hcount : ∀ k < J,
      ((S.filter fun i => (1/2:ℝ)^(k+1)<w i).card : ℝ) ≤ C*(q+k+1)) :
    Real.log (1+∑ i ∈ S,w i) ≤ (2*C+(1+4*C)/q0)*q := by
  have hs := sum_bound S w hw hC (hq0.le.trans hq) J hcount
  have hn' : 0 ≤ ∑ i ∈ S,w i := sum_nonneg hn
  have hlog := Real.log_le_sub_one_of_pos (by linarith : 0 < 1+∑ i ∈ S,w i)
  have hmul : (1+4*C) ≤ ((1+4*C)/q0)*q := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hq0]
    exact mul_le_mul_of_nonneg_left hq (by positivity)
  nlinarith

end RowGrouping

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_BlockWeights
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace BlockWeights

lemma bin_parameters {w q s ell ell' C c D k : ℝ}
    (hC : 1 ≤ C) (hc : 0 < c) (hq : 0 ≤ q) (hk : 0 ≤ k)
    (hl : ell ≤ q) (hl' : ell' ≤ s)
    (htrivial : w ≤ Real.exp (-|q-s|/2))
    (haff : w ≤ C*Real.exp ((ell+ell')/2-c*D))
    (hbin : Real.exp (-(k+1)) < w) :
    s < q+2*(k+1) ∧ ell' < 2*(q+k+1) ∧
      D ≤ ((Real.log C+2)/c)*(q+k+1) := by
  have hpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hb := Real.exp_lt_exp.mp (hbin.trans_le htrivial)
  have habs := neg_le_abs (q-s)
  have hs : s < q+2*(k+1) := by linarith
  refine ⟨hs, by linarith, ?_⟩
  have he : C*Real.exp ((ell+ell')/2-c*D) =
      Real.exp (Real.log C+(ell+ell')/2-c*D) := by
    rw [show Real.log C+(ell+ell')/2-c*D =
      Real.log C+((ell+ell')/2-c*D) by ring, Real.exp_add, Real.exp_log hpos]
  rw [he] at haff
  have hdist := Real.exp_lt_exp.mp (hbin.trans_le haff)
  have hlog := Real.log_nonneg hC
  have hmul := mul_nonneg hlog (by linarith : 0 ≤ q+k)
  have hD : c*D ≤ (Real.log C+2)*(q+k+1) := by nlinarith
  calc
    D ≤ (Real.log C+2)*(q+k+1)/c := (le_div_iff₀ hc).mpr (by nlinarith)
    _ = _ := by ring

lemma binary_above_exp (k : ℕ) : Real.exp (-((k:ℝ)+1)) ≤ (1/2:ℝ)^(k+1) := by
  have he : (2:ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1:ℝ); norm_num at this ⊢; exact this
  have hhalf : Real.exp (-1) ≤ (1/2:ℝ) := by
    rw [Real.exp_neg]
    simpa only [one_div] using (inv_le_inv₀ (Real.exp_pos _) (by norm_num : (0:ℝ)<2)).mpr he
  have hp := pow_le_pow_left₀ (Real.exp_pos (-1)).le hhalf (k+1)
  rw [← Real.exp_nat_mul] at hp
  simpa only [Nat.cast_add, Nat.cast_one, mul_neg, mul_one] using hp

end BlockWeights

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_BlockRow
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1

namespace BlockRow
open Finset BlockGeometry BlockCount BlockWeights
variable {I : Type u_1} [Fintype I] [DecidableEq I]

lemma logarithmic_row {L ζ R C0 c0 q0 : ℝ}
    (hL : 0 < L) (hζ : 0 < ζ) (hC0 : 1 ≤ C0) (hc0 : 0 < c0) (hq0 : 0 < q0)
    (d : I → I → ℝ) (hn : ∀ i j, 0 ≤ d i j) (hd : ∀ i, d i i = 0)
    (hs : ∀ i j, d i j = d j i) (htri : ∀ i j k, d i k ≤ d i j+d j k)
    (P : Finpartition (univ : Finset I))
    (hterm : ∀ H ⊆ P.parts, 2 ≤ H.card →
      ¬(radius d (H.biUnion id) ≤ R ∧ loss L d (H.biUnion id) ≤ ζ*(H.biUnion id).card))
    (N0 : ℕ) (hN02 : 2 ≤ N0)
    (hlog : ∀ N : ℕ, N0 ≤ N → L*Real.log N ≤ ζ*N/2)
    (a : Finset I → I) (ha : ∀ T ∈ P.parts, a T ∈ T)
    (q : Finset I → ℝ) (hql : ∀ T ∈ P.parts, loss L d T ≤ q T)
    (S : Finset I) (hS : S ∈ P.parts) (hq : q0 ≤ q S)
    (w : Finset I → ℝ) (hw0 : ∀ T ∈ P.parts.erase S, 0 ≤ w T)
    (hw1 : ∀ T ∈ P.parts.erase S, w T ≤ 1)
    (hwt : ∀ T ∈ P.parts.erase S, w T ≤ Real.exp (-|q S-q T|/2))
    (hwa : ∀ T ∈ P.parts.erase S,
      w T ≤ C0*Real.exp ((loss L d S+loss L d T)/2-c0*d (a S) (a T)^2))
    (J : ℕ) (htail : ((P.parts.erase S).card:ℝ)*(1/2:ℝ)^J ≤ 1)
    (hcutoff : ∀ k < J,
      (8*((Real.log C0+2)/c0)+16/L)*(q S+k+1) ≤ R) :
    let C := (N0:ℝ)+(2*L/ζ)*(1+8*((Real.log C0+2)/c0)+16/L)
    Real.log (1+∑ T ∈ P.parts.erase S,w T) ≤ (2*C+(1+4*C)/q0)*q S := by
  classical
  dsimp only
  let A := (Real.log C0+2)/c0
  let C := (N0:ℝ)+(2*L/ζ)*(1+8*A+16/L)
  have hA : 0 ≤ A := div_nonneg (by linarith [Real.log_nonneg hC0]) hc0.le
  have hC : 0 ≤ C := by dsimp [C]; positivity
  apply RowGrouping.log_row (P.parts.erase S) w hw0 hw1 hC hq0 hq J htail
  intro k hk
  let H := (P.parts.erase S).filter fun T => (1/2:ℝ)^(k+1)<w T
  let Q := q S+(k:ℝ)+1
  have hQ : 1 ≤ Q := by dsimp [Q]; linarith [show (0:ℝ) ≤ k from Nat.cast_nonneg k]
  have hH : H ⊆ P.parts := fun T hT => mem_of_mem_erase (mem_filter.mp hT).1
  have hparams (T : Finset I) (hT : T ∈ H) :
      loss L d T < 2*Q ∧ d (a S) (a T)^2 ≤ A*Q := by
    obtain ⟨hTP,hbin⟩ := mem_filter.mp hT
    have hb := bin_parameters hC0 hc0 (hq0.le.trans hq) (Nat.cast_nonneg k)
      (hql S hS) (hql T (mem_of_mem_erase hTP)) (hwt T hTP) (hwa T hTP)
      ((binary_above_exp k).trans_lt hbin)
    exact ⟨hb.2.1, hb.2.2⟩
  have hcount := terminal_count hL hζ (mul_nonneg hA (by linarith))
    (show 0 ≤ 2*Q by linarith) d hn hd hs htri P hterm N0 hN02 hlog H hH a (a S)
    (fun T hT => ha T (hH hT)) (fun T hT => (hparams T hT).2)
    (fun T hT => (hparams T hT).1.le) (by
      convert hcutoff k hk using 1
      all_goals try with_reducible_and_instances rfl
      dsimp [A,Q]
      ring)
  have hN0 : (0:ℝ) ≤ N0 := Nat.cast_nonneg _
  have hmul := mul_nonneg (div_nonneg (by positivity : (0:ℝ) ≤ 2*L) hζ.le)
    (sub_nonneg.mpr hQ)
  have hNQ := mul_nonneg hN0 (sub_nonneg.mpr hQ)
  change (H.card:ℝ) ≤ C*Q
  dsimp [C]
  have he : (2*L/ζ)*(1+8*(A*Q)+8*(2*Q)/L) =
      (2*L/ζ)*((1+8*A+16/L)*Q-(Q-1)) := by ring
  rw [he] at hcount
  nlinarith

end BlockRow

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_BlockDimension
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1

namespace BlockDimension
open Finset BlockGeometry BlockCount BlockRow
variable {I : Type u_1} [Fintype I] [DecidableEq I]

lemma binary_cutoff {u : ℝ} (hu : 1 ≤ u) :
    let J := ⌈3*u/Real.log 2⌉₊
    (J:ℝ) ≤ (3/Real.log 2+1)*u ∧
      Real.exp (2*u)*(1/2:ℝ)^J ≤ 1 := by
  dsimp only
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnon : 0 ≤ 3*u/Real.log 2 := div_nonneg (by linarith) hl.le
  have hceil := (Nat.ceil_lt_add_one hnon).le
  have hlo := Nat.le_ceil (3*u/Real.log 2)
  constructor
  · simp only [div_eq_mul_inv] at hceil ⊢
    nlinarith
  · have he : (1/2:ℝ)^⌈3*u/Real.log 2⌉₊ =
        Real.exp (-((⌈3*u/Real.log 2⌉₊:ℕ):ℝ)*Real.log 2) := by
      rw [neg_mul, Real.exp_neg, Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
      simp [one_div]
    rw [he, ← Real.exp_add]
    apply Real.exp_le_one_iff.mpr
    have hh := (div_le_iff₀ hl).mp hlo
    linarith

lemma uniform_row {L ζ C0 c0 q0 u : ℝ}
    (hL : 0 < L) (hζ : 0 < ζ) (hC0 : 1 ≤ C0) (hc0 : 0 < c0) (hq0 : 0 < q0)
    (hu : 1 ≤ u) (hcard : (Fintype.card I:ℝ) ≤ Real.exp (2*u))
    (d : I → I → ℝ) (hn : ∀ i j, 0 ≤ d i j) (hd : ∀ i, d i i = 0)
    (hs : ∀ i j, d i j = d j i) (htri : ∀ i j k, d i k ≤ d i j+d j k)
    (P : Finpartition (univ : Finset I))
    (hterm : ∀ H ⊆ P.parts, 2 ≤ H.card →
      ¬(radius d (H.biUnion id) ≤
          ((8*((Real.log C0+2)/c0)+16/L)*(2+3/Real.log 2))*u ∧
        loss L d (H.biUnion id) ≤ ζ*(H.biUnion id).card))
    (N0 : ℕ) (hN02 : 2 ≤ N0)
    (hlog : ∀ N : ℕ, N0 ≤ N → L*Real.log N ≤ ζ*N/2)
    (a : Finset I → I) (ha : ∀ T ∈ P.parts, a T ∈ T)
    (q : Finset I → ℝ) (hql : ∀ T ∈ P.parts, loss L d T ≤ q T)
    (S : Finset I) (hS : S ∈ P.parts) (hq : q0 ≤ q S)
    (w : Finset I → ℝ) (hw0 : ∀ T ∈ P.parts.erase S, 0 ≤ w T)
    (hw1 : ∀ T ∈ P.parts.erase S, w T ≤ 1)
    (hwt : ∀ T ∈ P.parts.erase S, w T ≤ Real.exp (-|q S-q T|/2))
    (hwa : ∀ T ∈ P.parts.erase S,
      w T ≤ C0*Real.exp ((loss L d S+loss L d T)/2-c0*d (a S) (a T)^2)) :
    let C := (N0:ℝ)+(2*L/ζ)*(1+8*((Real.log C0+2)/c0)+16/L)
    Real.log (1+∑ T ∈ P.parts.erase S,w T) ≤ max (2*C+(1+4*C)/q0) 3*q S := by
  dsimp only
  let C := (N0:ℝ)+(2*L/ζ)*(1+8*((Real.log C0+2)/c0)+16/L)
  have hqpos : 0 ≤ q S := hq0.le.trans hq
  have hct : ((P.parts.erase S).card:ℝ) ≤ Real.exp (2*u) := by
    apply le_trans _ hcard
    exact_mod_cast (card_erase_le.trans P.card_parts_le_card)
  by_cases hqu : q S ≤ u
  · let J := ⌈3*u/Real.log 2⌉₊
    obtain ⟨hJ,ht⟩ := binary_cutoff hu
    have htail : ((P.parts.erase S).card:ℝ)*(1/2:ℝ)^J ≤ 1 :=
      (mul_le_mul_of_nonneg_right hct (by positivity)).trans ht
    have hcut (k : ℕ) (hk : k < J) :
        (8*((Real.log C0+2)/c0)+16/L)*(q S+k+1) ≤
          ((8*((Real.log C0+2)/c0)+16/L)*(2+3/Real.log 2))*u := by
      have hk' : (k:ℝ)+1 ≤ J := by exact_mod_cast hk
      have ha : 0 ≤ (Real.log C0+2)/c0 := div_nonneg (by linarith [Real.log_nonneg hC0]) hc0.le
      have hf : 0 ≤ 8*((Real.log C0+2)/c0)+16/L := by positivity
      have hbase : q S+k+1 ≤ (2+3/Real.log 2)*u := by dsimp [J] at hk'; nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hbase hf]
    have hrow := logarithmic_row hL hζ hC0 hc0 hq0 d hn hd hs htri P hterm
      N0 hN02 hlog a ha q hql S hS hq w hw0 hw1 hwt hwa J htail hcut
    exact hrow.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hqpos)
  · have hsum : ∑ T ∈ P.parts.erase S,w T ≤ Real.exp (2*u) := by
      calc _ ≤ ∑ _T ∈ P.parts.erase S,(1:ℝ) := sum_le_sum hw1
           _ = ((P.parts.erase S).card:ℝ) := by simp
           _ ≤ _ := hct
    have h2 : Real.log 2 ≤ u := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
      linarith
    have hExp : 1+Real.exp (2*u) ≤ Real.exp (3*u) := by
      have h1 : 1 ≤ Real.exp (2*u) := Real.one_le_exp_iff.mpr (by linarith)
      have h2' : 2 ≤ Real.exp u := by simpa only [Real.exp_log (by norm_num : (0:ℝ)<2)] using Real.exp_le_exp.mpr h2
      have he : Real.exp (3*u) = Real.exp (2*u)*Real.exp u := by rw [← Real.exp_add]; congr 1; ring
      rw [he]
      nlinarith [Real.exp_pos (2*u)]
    have hleftpos : 0 < 1+∑ T ∈ P.parts.erase S,w T := by
      have := sum_nonneg hw0
      linarith
    have hbd : Real.log (1+∑ T ∈ P.parts.erase S,w T) ≤ 3*u := by
      have hp := Real.log_le_log hleftpos (show 1+∑ T ∈ P.parts.erase S,w T ≤ Real.exp (3*u) by linarith)
      simpa only [Real.log_exp] using hp
    exact hbd.trans ((by nlinarith : 3*u ≤ 3*q S).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hqpos))

end BlockDimension

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_MeasureCut
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology

universe u_1

namespace MeasureCut

lemma continuous_cdf (ν : Measure ℝ) [IsFiniteMeasure ν] [NullSingletonClass ν] :
    Continuous (fun x : ℝ => ν.real (Iic x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hi : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Iic (x+1)) ν :=
    (integrable_const (1 : ℝ)).integrableOn
  have hc := hi.continuousOn_Iic_primitive_Iic
  have heq : (fun y : ℝ => ∫ t in Iic y, (1 : ℝ) ∂ν) =
      (fun y : ℝ => ν.real (Iic y)) := by
    funext y
    simp [integral_const, measureReal_def]
  rw [heq] at hc
  exact hc.continuousAt (Iic_mem_nhds (by linarith))

lemma cdf_atBot (ν : Measure ℝ) [IsFiniteMeasure ν] :
    Tendsto (fun x : ℝ => ν.real (Iic x)) atBot (nhds 0) := by
  have hi : (⋂ x : ℝ, Iic x) = ∅ := by
    ext y
    simp only [mem_iInter, mem_Iic, mem_empty_iff_false, iff_false]
    intro h
    have := h (y-1)
    linarith
  have ht := tendsto_measure_iInter_atBot
    (fun x : ℝ => (measurableSet_Iic : MeasurableSet (Iic x)).nullMeasurableSet (μ := ν))
    (fun x y h => Iic_subset_Iic.mpr h) ⟨0, measure_ne_top ν _⟩
  rw [hi, measure_empty] at ht
  simpa only [Function.comp_def, ENNReal.toReal_zero, measureReal_def] using
    (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp ht

lemma exists_cdf_eq (ν : Measure ℝ) [IsFiniteMeasure ν] [NullSingletonClass ν]
    {r : ℝ} (hr : 0 < r) (hr' : r < ν.real univ) :
    ∃ x : ℝ, ν.real (Iic x) = r := by
  have ht : Tendsto (fun x : ℝ => ν.real (Iic x)) atTop (nhds (ν.real univ)) := by
    exact (ENNReal.tendsto_toReal (measure_ne_top ν univ)).comp (tendsto_measure_Iic_atTop ν)
  have hab := isPreconnected_univ.intermediate_value_Ioo
    (by simp) (by simp) (continuous_cdf ν).continuousOn (cdf_atBot ν) ht ⟨hr, hr'⟩
  simpa only [mem_image, mem_univ, true_and] using hab

lemma exists_subset_measure {Ω : Type u_1} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] [NullSingletonClass μ]
    {E : Set Ω} (hE : MeasurableSet E) {r : ℝ}
    (hr : 0 ≤ r) (hrE : r ≤ μ.real E) :
    ∃ A : Set Ω, MeasurableSet A ∧ A ⊆ E ∧ μ.real A = r := by
  classical
  by_cases hzero : r = 0
  · exact ⟨∅, MeasurableSet.empty, empty_subset _, by simp [hzero]⟩
  by_cases hfull : r = μ.real E
  · exact ⟨E, hE, Subset.rfl, hfull.symm⟩
  let f := embeddingReal Ω
  have hf : MeasurableEmbedding f := measurableEmbedding_embeddingReal Ω
  let ν := (μ.restrict E).map f
  have : IsFiniteMeasure ν := inferInstance
  have : NullSingletonClass ν := ⟨fun x => by
    rw [show ν {x} = (μ.restrict E) (f ⁻¹' {x}) from hf.map_apply _ _]
    exact (Set.subsingleton_singleton.preimage hf.injective).measure_zero _⟩
  have htotal : ν.real univ = μ.real E := by
    simp [ν, measureReal_def, hf.map_apply]
  obtain ⟨x,hx⟩ := exists_cdf_eq ν (lt_of_le_of_ne hr (Ne.symm hzero))
    (by rw [htotal]; exact lt_of_le_of_ne hrE hfull)
  refine ⟨E ∩ f ⁻¹' Iic x, hE.inter (hf.measurable measurableSet_Iic), inter_subset_left, ?_⟩
  rw [← hx, measureReal_def, measureReal_def, hf.map_apply, Measure.restrict_apply
    (hf.measurable measurableSet_Iic)]
  congr 1
  exact congrArg μ (inter_comm _ _)

end MeasureCut

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_BlockSets
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology

universe u_1 u_2

namespace BlockSets
open MeasureTheory Finset BlockGeometry
open scoped BigOperators
variable {Ω : Type u_1} {I : Type u_2} [MeasurableSpace Ω]

lemma clipped_pos (μ : Measure Ω) (C : I → Set Ω) (hc : ∀ i, 0 < μ.real (C i))
    (i : I) : 0 < clipped μ C i := lt_min (hc i) (by norm_num)

lemma cost_ge (μ : Measure Ω) (C : I → Set Ω) (hc : ∀ i, 0 < μ.real (C i))
    (i : I) : Real.log 2 ≤ cost μ C i := by
  have hb := Real.log_le_log (clipped_pos μ C hc i) (min_le_right (μ.real (C i)) (1/2))
  change _ ≤ -Real.log (clipped μ C i)
  rw [Real.log_div one_ne_zero (by norm_num), Real.log_one] at hb
  linarith

lemma common_measurable (C : I → Set Ω) (hC : ∀ i, MeasurableSet (C i)) (S : Finset I) :
    MeasurableSet (common C S) := by
  exact MeasurableSet.biInter S.finite_toSet.countable (fun i _ => hC i)

omit [MeasurableSpace Ω] in
lemma common_subset (C : I → Set Ω) {S : Finset I} {i : I} (hi : i ∈ S) :
    common C S ⊆ C i := by
  intro x hx
  exact Set.mem_iInter₂.mp hx i hi

lemma choose_sets [StandardBorelSpace Ω] [Fintype I] [DecidableEq I] (μ : Measure Ω) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (C : I → Set Ω) (hC : ∀ i, MeasurableSet (C i))
    (hc : ∀ i, 0 < μ.real (C i)) {L R : ℝ}
    (d : I → I → ℝ) (P : Finpartition (univ : Finset I))
    (a : Finset I → I) (ha : ∀ S ∈ P.parts, a S ∈ S)
    (hR : ∀ S ∈ P.parts, radius d S ≤ R)
    (hlens : ∀ S ∈ P.parts, radius d S ≤ R →
      Real.exp (-L*(1+radius d S+Real.log S.card))*clipped μ C (a S) ≤ μ.real (common C S)) :
    ∃ E : Finset I → Set Ω, ∀ S ∈ P.parts,
      MeasurableSet (E S) ∧ E S ⊆ common C S ∧
      μ.real (E S) = Real.exp (-loss L d S)*clipped μ C (a S) := by
  classical
  have hex (S : Finset I) (hS : S ∈ P.parts) :
      ∃ E : Set Ω, MeasurableSet E ∧ E ⊆ common C S ∧
        μ.real E = Real.exp (-loss L d S)*clipped μ C (a S) := by
    apply MeasureCut.exists_subset_measure μ (common_measurable C hC S)
    · exact mul_nonneg (Real.exp_pos _).le (clipped_pos μ C hc _).le
    · by_cases hsmall : S.card ≤ 1
      · have hnon := P.nonempty_of_mem_parts hS
        have hc1 : S.card = 1 := by have := card_pos.mpr hnon; omega
        obtain ⟨i,hi⟩ := card_eq_one.mp hc1
        have hai : a S = i := by simpa [hi] using ha S hS
        simp only [loss, ite_eq_left hsmall, neg_zero, Real.exp_zero, one_mul, hai]
        have hcommon : common C S = C i := by simp [common,hi]
        rw [hcommon]
        exact min_le_left _ _
      · rw [loss, ite_eq_right hsmall]
        convert hlens S hS (hR S hS) using 1
        all_goals try with_reducible_and_instances rfl
        congr 2
        ring
  choose E hE using hex
  let F : Finset I → Set Ω := fun S => if hS : S ∈ P.parts then E S hS else ∅
  refine ⟨F, fun S hS => ?_⟩
  simpa only [F,dite_eq_left hS] using hE S hS

lemma intensity_cost {ell b : ℝ} (hell : 0 ≤ ell) (hb : 0 < b) (hb' : b ≤ 1/2) :
    0 < Real.exp (-ell)*b ∧ Real.exp (-ell)*b ≤ 1/2 ∧
      -Real.log (Real.exp (-ell)*b) = -Real.log b+ell := by
  have he : Real.exp (-ell) ≤ 1 := by simpa using Real.exp_le_exp.mpr (neg_nonpos.mpr hell)
  refine ⟨mul_pos (Real.exp_pos _) hb, (mul_le_of_le_one_left hb.le he).trans hb', ?_⟩
  rw [Real.log_mul (Real.exp_ne_zero _) hb.ne', Real.log_exp]
  ring

lemma sum_cost [Fintype I] [DecidableEq I] (μ : Measure Ω) (C : I → Set Ω) (hc : ∀ i, 0 < μ.real (C i))
    {L ζ : ℝ} (d : I → I → ℝ) (P : Finpartition (univ : Finset I))
    (a : Finset I → I) (ha : ∀ S ∈ P.parts, a S ∈ S)
    (hloss : ∀ S ∈ P.parts, loss L d S ≤ ζ*S.card) :
    ∑ S ∈ P.parts, (cost μ C (a S)+loss L d S) ≤
      ∑ i, cost μ C i + ζ*Fintype.card I := by
  have hn (i : I) : 0 ≤ cost μ C i :=
    (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)).trans (cost_ge μ C hc i)
  calc
    _ ≤ ∑ S ∈ P.parts, ((∑ i ∈ S, cost μ C i)+ζ*S.card) := by
      apply sum_le_sum
      intro S hS
      exact add_le_add (single_le_sum (fun i _ => hn i) (ha S hS)) (hloss S hS)
    _ = _ := by
      have hsum := sum_biUnion (f := cost μ C) P.disjoint
      simp only [id_eq,P.biUnion_parts] at hsum
      rw [sum_add_distrib, ← hsum, ← mul_sum]
      congr 1
      have hh := congrArg (fun x : ℕ => (x:ℝ)) P.sum_card_parts
      simpa only [Nat.cast_sum, card_univ] using congrArg (fun x : ℝ => ζ*x) hh

end BlockSets

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_BlockWeightMeasure
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology

universe u_1

namespace BlockWeightMeasure
open MeasureTheory
variable {Ω : Type u_1} [MeasurableSpace Ω]

lemma denom_at_least {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.sqrt (x*y) ≤ Real.sqrt (x*(1+x)*y*(1+y)) := by
  apply Real.sqrt_le_sqrt
  have hxy : 0 ≤ x*y := mul_nonneg hx.le hy.le
  have h1 : 1 ≤ (1+x)*(1+y) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h1 hxy]

lemma normalized_le_basic {z x y : ℝ} (hz : 0 ≤ z) (hx : 0 < x) (hy : 0 < y) :
    z / Real.sqrt (x*(1+x)*y*(1+y)) ≤ z / Real.sqrt (x*y) :=
  div_le_div_of_nonneg_left hz (Real.sqrt_pos.mpr (mul_pos hx hy)) (denom_at_least hx hy)

lemma trivial_bound {z q s : ℝ} (hz : 0 ≤ z)
    (hzq : z ≤ Real.exp (-q)) (hzs : z ≤ Real.exp (-s)) :
    z / Real.sqrt (Real.exp (-q)*(1+Real.exp (-q))*
      Real.exp (-s)*(1+Real.exp (-s))) ≤ Real.exp (-|q-s|/2) := by
  apply (normalized_le_basic hz (Real.exp_pos _) (Real.exp_pos _)).trans
  rw [← Real.exp_add, ← Real.exp_half]
  rw [div_le_iff₀ (Real.exp_pos _), ← Real.exp_add]
  rcases le_total q s with hqs | hsq
  · rw [abs_of_nonpos (sub_nonpos.mpr hqs)]
    convert hzs using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring_nf
  · rw [abs_of_nonneg (sub_nonneg.mpr hsq)]
    convert hzq using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring_nf

lemma affine_bound {z b b' ell ell' H c D : ℝ}
    (hz : 0 ≤ z) (hb : 0 < b) (hb' : 0 < b')
    (h : z / Real.sqrt (b*b') ≤ H*Real.exp (-c*D)) :
    z / Real.sqrt ((Real.exp (-ell)*b)*(1+Real.exp (-ell)*b)*
      (Real.exp (-ell')*b')*(1+Real.exp (-ell')*b')) ≤
      H*Real.exp ((ell+ell')/2-c*D) := by
  apply (normalized_le_basic hz (mul_pos (Real.exp_pos _) hb)
    (mul_pos (Real.exp_pos _) hb')).trans
  have heq : (Real.exp (-ell)*b)*(Real.exp (-ell')*b') =
      Real.exp (-(ell+ell'))*(b*b') := by rw [neg_add,Real.exp_add]; ring
  rw [heq, Real.sqrt_mul (Real.exp_pos _).le, ← Real.exp_half]
  have hepos := Real.exp_pos ((ell+ell')/2)
  have hid : z/(Real.exp (-(ell+ell')/2)*Real.sqrt (b*b')) =
      (z/Real.sqrt (b*b'))*Real.exp ((ell+ell')/2) := by
    rw [show -(ell+ell')/2 = -((ell+ell')/2) by ring, Real.exp_neg]
    field_simp
  rw [hid]
  calc
    _ ≤ (H*Real.exp (-c*D))*Real.exp ((ell+ell')/2) := mul_le_mul_of_nonneg_right h hepos.le
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

lemma measure_trivial (μ : Measure Ω) [IsFiniteMeasure μ] {E F : Set Ω}
    (hE : 0 < μ.real E) (hF : 0 < μ.real F) :
    μ.real (E ∩ F) /
      Real.sqrt (μ.real E*(1+μ.real E)*μ.real F*(1+μ.real F)) ≤
      Real.exp (-|(-Real.log (μ.real E))-(-Real.log (μ.real F))|/2) := by
  have he : Real.exp (-(-Real.log (μ.real E))) = μ.real E := by rw [neg_neg,Real.exp_log hE]
  have hf : Real.exp (-(-Real.log (μ.real F))) = μ.real F := by rw [neg_neg,Real.exp_log hF]
  have hmE : μ.real (E ∩ F) ≤ μ.real E := measureReal_mono Set.inter_subset_left
  have hmF : μ.real (E ∩ F) ≤ μ.real F := measureReal_mono Set.inter_subset_right
  simpa only [he,hf] using trivial_bound (q := -Real.log (μ.real E)) (s := -Real.log (μ.real F))
    (measureReal_nonneg) (by simpa only [he] using hmE)
    (by simpa only [hf] using hmF)

end BlockWeightMeasure

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_Blocks
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology

universe u_1 u_2

namespace Blocks
universe u₁ u₂
open Finset MeasureTheory BlockGeometry BlockSets
open scoped BigOperators
variable {Ω : Type u_1} {I : Type u_2} [MeasurableSpace Ω]

lemma first_budget_point {lam : ℝ} (hpos : 0 < lam) (hsmall : lam ≤ 1/2) :
    Real.log (1+lam⁻¹) ≤ 2*(-Real.log lam) := by
  have hq : Real.log 2 ≤ -Real.log lam := by
    have hh := Real.log_le_log hpos hsmall
    rw [Real.log_div one_ne_zero (by norm_num),Real.log_one] at hh
    linarith
  have hi : 1 ≤ lam⁻¹ := by
    rw [inv_eq_one_div,le_div_iff₀ hpos]
    linarith
  have hp : 0 < 1+lam⁻¹ := by positivity
  have hh := Real.log_le_log hp (show 1+lam⁻¹ ≤ 2*lam⁻¹ by linarith)
  rw [Real.log_mul (by norm_num) (inv_ne_zero hpos.ne'),Real.log_inv] at hh
  linarith

lemma loss_bound [Fintype I] {L B u : ℝ} (hL : 0 ≤ L) (hB : 0 ≤ B) (hu : 1 ≤ u)
    (hcard : (Fintype.card I:ℝ) ≤ Real.exp (2*u)) (d : I → I → ℝ)
    (S : Finset I) (hS : S.Nonempty) (hr : radius d S ≤ B*u) :
    loss L d S ≤ (L*(B+3))*u := by
  have hm : 0 < (S.card:ℝ) := by exact_mod_cast card_pos.mpr hS
  have hsize : (S.card:ℝ) ≤ Fintype.card I := by exact_mod_cast S.card_le_univ
  have hsc : (S.card:ℝ) ≤ Real.exp (2*u) := hsize.trans hcard
  have hslog := (Real.log_le_iff_le_exp hm).mpr hsc
  unfold loss
  split_ifs
  · positivity
  · nlinarith [mul_le_mul_of_nonneg_left hr hL, mul_le_mul_of_nonneg_left hslog hL,
      mul_le_mul_of_nonneg_left hu hL]

lemma anchors [Nonempty I] [Fintype I] [DecidableEq I] (c : I → ℝ)
    (P : Finpartition (univ : Finset I)) :
    ∃ a : Finset I → I, ∀ S ∈ P.parts, a S ∈ S ∧ ∀ i ∈ S, c (a S) ≤ c i := by
  classical
  have hex (S : Finset I) : ∃ i : I, S ∈ P.parts → i ∈ S ∧ ∀ j ∈ S, c i ≤ c j := by
    by_cases hS : S ∈ P.parts
    · obtain ⟨i,hi,hmin⟩ := S.exists_min_image c (P.nonempty_of_mem_parts hS)
      exact ⟨i,fun _ => ⟨hi,hmin⟩⟩
    · exact ⟨Classical.arbitrary I, fun h => (hS h).elim⟩
  choose a ha using hex
  exact ⟨a,ha⟩

theorem block_estimates_oai {L C0 c0 : ℝ} (hL : 1 ≤ L) (hC0 : 1 ≤ C0) (hc0 : 0 < c0) :
    ∃ B K C : ℝ, 0 < B ∧ 0 < K ∧ 0 < C ∧
    ∀ (Ω : Type u₁) (I : Type u₂) [MeasurableSpace Ω] [StandardBorelSpace Ω]
      [Fintype I] [Nonempty I] [DecidableEq I] (μ : Measure Ω)
      [IsFiniteMeasure μ] [NullSingletonClass μ],
    ∀ (u : ℝ), 1 ≤ u → (Fintype.card I:ℝ) ≤ Real.exp (2*u) →
    ∀ (caps : I → Set Ω), (∀ i, MeasurableSet (caps i)) → (∀ i, 0 < μ.real (caps i)) →
    ∀ (d : I → I → ℝ), (∀ i j, 0 ≤ d i j) → (∀ i, d i i = 0) →
      (∀ i j, d i j = d j i) → (∀ i j k, d i k ≤ d i j+d j k) →
    (∀ i j, μ.real (caps i ∩ caps j)/Real.sqrt (clipped μ caps i*clipped μ caps j) ≤
      C0*Real.exp (-c0*d i j^2)) →
    (∀ S : Finset I, S.Nonempty → radius d S ≤ B*u →
      ∀ a ∈ S, (∀ i ∈ S, μ.real (caps a) ≤ μ.real (caps i)) →
      Real.exp (-L*(1+radius d S+Real.log S.card))*clipped μ caps a ≤ μ.real (common caps S)) →
    ∃ (P : Finpartition (univ : Finset I)) (a : Finset I → I) (E : Finset I → Set Ω),
      (∀ S ∈ P.parts, a S ∈ S ∧ (∀ i ∈ S, μ.real (caps (a S)) ≤ μ.real (caps i)) ∧
        MeasurableSet (E S) ∧ E S ⊆ common caps S ∧
        Real.exp (-K*u)*clipped μ caps (a S) ≤ μ.real (E S) ∧
        0 < μ.real (E S) ∧ μ.real (E S) ≤ 1/2) ∧
      (∑ S ∈ P.parts, -Real.log (μ.real (E S))) ≤ ∑ i, cost μ caps i+(Fintype.card I:ℝ)/10 ∧
      (∑ S ∈ P.parts, Real.log (1+(μ.real (E S))⁻¹)) ≤ C*((Fintype.card I:ℝ)+∑ i,cost μ caps i) ∧
      (∑ S ∈ P.parts, Real.log (1+∑ T ∈ P.parts.erase S,weight μ (E S) (E T))) ≤
        C*((Fintype.card I:ℝ)+∑ i,cost μ caps i) := by
  classical
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hζ : (0:ℝ) < 1/10 := by norm_num
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let A := (Real.log C0+2)/c0
  let B := (8*A+16/L)*(2+3/Real.log 2)
  have hAp : 0 < A := div_pos (by linarith [Real.log_nonneg hC0]) hc0
  have hBp : 0 < B := by dsimp [B]; positivity
  obtain ⟨N0,hN02,hN0log⟩ := BlockCount.log_absorption hLp hζ
  let Cbin := (N0:ℝ)+(2*L/(1/10))*(1+8*A+16/L)
  let Crow := max (2*Cbin+(1+4*Cbin)/Real.log 2) 3
  let C := max 2 Crow
  have hCp : 0 < C := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨B,L*(B+3),C,hBp,by positivity,hCp,?_⟩
  intro Ω I _ _ _ _ _ μ _ _ u hu hcard caps hmeas hpos d hn hd hs htri haff hlens
  obtain ⟨P,hprops,hterm⟩ := BlockGeometry.exists_terminal (L := L) (R := B*u)
    (mul_nonneg hBp.le (show 0 ≤ u by linarith)) hζ.le d hd
  obtain ⟨a,ha⟩ := anchors (fun i => μ.real (caps i)) P
  obtain ⟨E,hE⟩ := choose_sets μ caps hmeas hpos d P a (fun S hS => (ha S hS).1)
    (fun S hS => (hprops S hS).1) (fun S hS hr =>
      hlens S (P.nonempty_of_mem_parts hS) hr (a S) (ha S hS).1 (ha S hS).2)
  let q := fun S => -Real.log (μ.real (E S))
  have hi (S : Finset I) (hS : S ∈ P.parts) :
      0 < μ.real (E S) ∧ μ.real (E S) ≤ 1/2 ∧ q S = cost μ caps (a S)+loss L d S := by
    dsimp only [q,cost]
    rw [(hE S hS).2.2]
    exact intensity_cost (loss_nonneg hLp.le d S) (clipped_pos μ caps hpos _) (min_le_right _ _)
  have hqeq (S : Finset I) (hS : S ∈ P.parts) :
      q S = cost μ caps (a S)+loss L d S := (hi S hS).2.2
  have hqge (S : Finset I) (hS : S ∈ P.parts) : Real.log 2 ≤ q S := by
    rw [hqeq S hS]
    linarith [cost_ge μ caps hpos (a S),loss_nonneg hLp.le d S]
  have hqsum : ∑ S ∈ P.parts,q S ≤ ∑ i,cost μ caps i + (Fintype.card I:ℝ)/10 := by
    simp_rw [sum_congr rfl (fun S hS => hqeq S hS)]
    convert sum_cost μ caps hpos d P a (fun S hS => (ha S hS).1)
      (fun S hS => (hprops S hS).2) using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hqtotal : ∑ S ∈ P.parts,q S ≤ (Fintype.card I:ℝ)+∑ i,cost μ caps i := by
    have hm : (0:ℝ) ≤ Fintype.card I := Nat.cast_nonneg _
    linarith
  have hrow (S : Finset I) (hS : S ∈ P.parts) :
      Real.log (1+∑ T ∈ P.parts.erase S,weight μ (E S) (E T)) ≤ Crow*q S := by
    apply BlockDimension.uniform_row hLp hζ hC0 hc0 hlog2 hu hcard d hn hd hs htri P
      hterm N0 hN02 hN0log a (fun T hT => (ha T hT).1) q
      (fun T hT => by rw [hqeq T hT]; linarith [cost_ge μ caps hpos (a T)]) S hS (hqge S hS)
    · intro T _; exact div_nonneg measureReal_nonneg (Real.sqrt_nonneg _)
    · intro T hT
      apply (BlockWeightMeasure.measure_trivial μ (hi S hS).1 (hi T (mem_of_mem_erase hT)).1).trans
      exact Real.exp_le_one_iff.mpr (by have := abs_nonneg (q S-q T); linarith)
    · intro T hT
      exact BlockWeightMeasure.measure_trivial μ (hi S hS).1 (hi T (mem_of_mem_erase hT)).1
    · intro T hT
      have hTP := mem_of_mem_erase hT
      have hsub : E S ∩ E T ⊆ caps (a S) ∩ caps (a T) :=
        Set.inter_subset_inter ((hE S hS).2.1.trans (common_subset caps (ha S hS).1))
          ((hE T hTP).2.1.trans (common_subset caps (ha T hTP).1))
      have hinter := measureReal_mono (μ := μ) hsub
      have hbasic : μ.real (E S ∩ E T)/Real.sqrt (clipped μ caps (a S)*clipped μ caps (a T)) ≤
          C0*Real.exp (-c0*d (a S) (a T)^2) :=
        (div_le_div_of_nonneg_right hinter (Real.sqrt_nonneg _)).trans (haff _ _)
      have hh := BlockWeightMeasure.affine_bound (ell := loss L d S) (ell' := loss L d T)
        measureReal_nonneg (clipped_pos μ caps hpos _) (clipped_pos μ caps hpos _) hbasic
      simpa only [weight,(hE S hS).2.2,(hE T hTP).2.2] using hh
  refine ⟨P,a,E,?_,hqsum,?_,?_⟩
  · intro S hS
    refine ⟨(ha S hS).1,(ha S hS).2,(hE S hS).1,(hE S hS).2.1,?_,(hi S hS).1,(hi S hS).2.1⟩
    rw [(hE S hS).2.2]
    apply mul_le_mul_of_nonneg_right _ (clipped_pos μ caps hpos _).le
    apply Real.exp_le_exp.mpr
    have hh := loss_bound hLp.le hBp.le hu hcard d S (P.nonempty_of_mem_parts hS) (hprops S hS).1
    linarith
  · calc
      _ ≤ ∑ S ∈ P.parts,2*q S := sum_le_sum (fun S hS => first_budget_point (hi S hS).1 (hi S hS).2.1)
      _ = 2*∑ S ∈ P.parts,q S := by rw [mul_sum]
      _ ≤ C*∑ S ∈ P.parts,q S := mul_le_mul_of_nonneg_right (le_max_left _ _)
        (sum_nonneg (fun S hS => hlog2.le.trans (hqge S hS)))
      _ ≤ _ := mul_le_mul_of_nonneg_left hqtotal hCp.le
  · calc
      _ ≤ ∑ S ∈ P.parts,Crow*q S := sum_le_sum hrow
      _ = Crow*∑ S ∈ P.parts,q S := by rw [mul_sum]
      _ ≤ C*∑ S ∈ P.parts,q S := mul_le_mul_of_nonneg_right (le_max_right _ _)
        (sum_nonneg (fun S hS => hlog2.le.trans (hqge S hS)))
      _ ≤ _ := mul_le_mul_of_nonneg_left hqtotal hCp.le

end Blocks

end OAI
end

theorem solution.{u₁, u₂} : type_of% @OAI.Blocks.block_estimates_oai.{u₁, u₂} := @OAI.Blocks.block_estimates_oai.{u₁, u₂}
