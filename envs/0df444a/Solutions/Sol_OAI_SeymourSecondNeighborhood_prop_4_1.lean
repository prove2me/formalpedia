-- Prove2me | solution 1 for OAI.SeymourSecondNeighborhood.prop_4_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-13T21:10:41.349992+00:00
-- url     : https://prove2.me/submissions/ba16d838-4329-4512-a808-fc786caa5913
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SeymourSecondNeighborhood
import Definitions.Def_SeymourSecondNeighborhood_Image
import Theorems.Thm_OAI_SeymourSecondNeighborhood_Pruning_lemma_3_1

set_option autoImplicit false
open Finset

namespace OAI.SeymourSecondNeighborhood.Sol_OAI_SeymourSecondNeighborhood_prop_4_1

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable section

/-! ### The two "advance" operators on families of pairs -/

/-- Advance the first coordinate along an arc: `(i, j) ∈ F1 P ↔ ∃ p, (p, j) ∈ P ∧ p → i`. -/
def F1 (r : V → V → Prop) (P : Finset (V × V)) : Finset (V × V) := by
  classical
  exact univ.filter (fun z : V × V => ∃ p, (p, z.2) ∈ P ∧ r p z.1)

/-- Advance the second coordinate along an arc: `(i, j) ∈ F2 Q ↔ ∃ s, (i, s) ∈ Q ∧ s → j`. -/
def F2 (r : V → V → Prop) (Q : Finset (V × V)) : Finset (V × V) := by
  classical
  exact univ.filter (fun z : V × V => ∃ s, (z.1, s) ∈ Q ∧ r s z.2)

/-- The diagonal. -/
def Δ : Finset (V × V) := univ.filter (fun z : V × V => z.1 = z.2)

/-- The number of points not covered by `F1 P ∪ F2 Q`. -/
def d (r : V → V → Prop) (P Q : Finset (V × V)) : ℕ := (univ \ (F1 r P ∪ F2 r Q)).card

/-- The finite set of admissible pairs of families. -/
def Ω (r : V → V → Prop) : Finset (Finset (V × V) × Finset (V × V)) := by
  classical
  exact ((univ : Finset (V × V)).powerset ×ˢ (univ : Finset (V × V)).powerset).filter
    (fun pq => Disjoint (F1 r pq.1) (F2 r pq.2) ∧ Δ ⊆ pq.1 ∧ Δ ⊆ pq.2)

/-- Column `j` of a family. -/
def col (P : Finset (V × V)) (j : V) : Finset V :=
  (P.filter (fun z : V × V => z.2 = j)).image Prod.fst

theorem mem_F1 {r : V → V → Prop} {P : Finset (V × V)} {z : V × V} :
    z ∈ F1 r P ↔ ∃ p, (p, z.2) ∈ P ∧ r p z.1 := by
  simp only [F1, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_F2 {r : V → V → Prop} {Q : Finset (V × V)} {z : V × V} :
    z ∈ F2 r Q ↔ ∃ s, (z.1, s) ∈ Q ∧ r s z.2 := by
  simp only [F2, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_Δ {z : V × V} : z ∈ (Δ : Finset (V × V)) ↔ z.1 = z.2 := by
  simp only [Δ, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_Ω {r : V → V → Prop} {pq : Finset (V × V) × Finset (V × V)} :
    pq ∈ Ω r ↔ Disjoint (F1 r pq.1) (F2 r pq.2) ∧ Δ ⊆ pq.1 ∧ Δ ⊆ pq.2 := by
  simp only [Ω, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset, Finset.subset_univ,
    true_and]

omit [DecidableEq V] in
theorem mem_fwd {r : V → V → Prop} {U : Finset V} {y : V} :
    y ∈ fwd r U ↔ ∃ x ∈ U, r x y := by
  simp only [fwd, Finset.mem_filter, Finset.mem_univ, true_and]

omit [Fintype V] in
theorem mem_col {P : Finset (V × V)} {j p : V} : p ∈ col P j ↔ (p, j) ∈ P := by
  unfold col
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨z1, z2⟩, ⟨hz, hz2⟩, rfl⟩
    simp only at hz2
    subst hz2
    exact hz
  · intro h
    exact ⟨(p, j), ⟨h, rfl⟩, rfl⟩

theorem col_F1 (r : V → V → Prop) (P : Finset (V × V)) (j : V) :
    col (F1 r P) j = fwd r (col P j) := by
  ext i
  rw [mem_col, mem_F1, mem_fwd]
  simp only [mem_col]

omit [Fintype V] in
theorem card_fiber (P : Finset (V × V)) (j : V) :
    (P.filter (fun z : V × V => z.2 = j)).card = (col P j).card := by
  unfold col
  rw [Finset.card_image_of_injOn]
  intro z hz w hw hzw
  simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hz hw
  exact Prod.ext hzw (hz.2.trans hw.2.symm)

theorem card_eq_sum_col (P : Finset (V × V)) : P.card = ∑ j, (col P j).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (s := P) (t := univ)
    (fun _ _ => Finset.mem_univ _)]
  exact Finset.sum_congr rfl (fun j _ => card_fiber P j)

theorem column_ineq [Nonempty V] {r : V → V → Prop} (hexp : StrictExpander r)
    {P : Finset (V × V)} (h : ∀ j, (col P j).Nonempty ∧ col P j ≠ univ) :
    P.card + (F1 r (F1 r P)).card < 2 * (F1 r P).card := by
  classical
  rw [card_eq_sum_col P, card_eq_sum_col (F1 r (F1 r P)), card_eq_sum_col (F1 r P)]
  simp only [col_F1]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
  intro j _
  exact hexp _ (h j).1 (h j).2

/-! ### Rows via the swap -/

omit [Fintype V] in
theorem mem_image_swap {Q : Finset (V × V)} {z : V × V} :
    z ∈ Q.image Prod.swap ↔ z.swap ∈ Q := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa [Prod.swap_swap] using ha
  · intro h
    exact ⟨z.swap, h, Prod.swap_swap z⟩

omit [Fintype V] in
theorem image_swap_image_swap (Q : Finset (V × V)) :
    (Q.image Prod.swap).image Prod.swap = Q := by
  ext z
  simp only [mem_image_swap, Prod.swap_swap]

omit [Fintype V] in
theorem card_image_swap (Q : Finset (V × V)) : (Q.image Prod.swap).card = Q.card :=
  Finset.card_image_of_injective _ Prod.swap_injective

theorem F2_eq_swap (r : V → V → Prop) (Q : Finset (V × V)) :
    F2 r Q = (F1 r (Q.image Prod.swap)).image Prod.swap := by
  ext ⟨a, b⟩
  rw [mem_F2, mem_image_swap, mem_F1]
  simp only [Prod.swap_prod_mk, mem_image_swap]

theorem row_ineq [Nonempty V] {r : V → V → Prop} (hexp : StrictExpander r)
    {Q : Finset (V × V)}
    (h : ∀ i, (col (Q.image Prod.swap) i).Nonempty ∧ col (Q.image Prod.swap) i ≠ univ) :
    Q.card + (F2 r (F2 r Q)).card < 2 * (F2 r Q).card := by
  have key := column_ineq hexp h
  have hQ := card_image_swap Q
  simp only [F2_eq_swap, card_image_swap, image_swap_image_swap]
  omega

/-! ### Hypotheses of the column/row inequalities -/

theorem col_P_hyp {r : V → V → Prop} (hin : PosIndeg r) {P Q : Finset (V × V)}
    (hΔP : Δ ⊆ P) (hΔQ : Δ ⊆ Q) (hc : Disjoint (F1 r P) (F2 r Q)) (j : V) :
    (col P j).Nonempty ∧ col P j ≠ univ := by
  refine ⟨⟨j, mem_col.2 (hΔP (mem_Δ.2 rfl))⟩, ?_⟩
  intro hu
  obtain ⟨w, hw⟩ := hin j
  obtain ⟨p, hp⟩ := hin w
  have h1 : (w, j) ∈ F1 r P := mem_F1.2 ⟨p, mem_col.1 (hu ▸ Finset.mem_univ p), hp⟩
  have h2 : (w, j) ∈ F2 r Q := mem_F2.2 ⟨w, hΔQ (mem_Δ.2 rfl), hw⟩
  exact Finset.disjoint_left.1 hc h1 h2

theorem col_Q_hyp {r : V → V → Prop} (hin : PosIndeg r) {P Q : Finset (V × V)}
    (hΔP : Δ ⊆ P) (hΔQ : Δ ⊆ Q) (hc : Disjoint (F1 r P) (F2 r Q)) (i : V) :
    (col (Q.image Prod.swap) i).Nonempty ∧ col (Q.image Prod.swap) i ≠ univ := by
  refine ⟨⟨i, mem_col.2 (mem_image_swap.2 (hΔQ (mem_Δ.2 rfl)))⟩, ?_⟩
  intro hu
  obtain ⟨w, hw⟩ := hin i
  obtain ⟨s, hs⟩ := hin w
  have h1 : (i, w) ∈ F1 r P := mem_F1.2 ⟨w, hΔP (mem_Δ.2 rfl), hw⟩
  have hiw : (i, s) ∈ Q := by
    have := mem_image_swap.1 (mem_col.1 (hu ▸ Finset.mem_univ s) : (s, i) ∈ Q.image Prod.swap)
    simpa using this
  have h2 : (i, w) ∈ F2 r Q := mem_F2.2 ⟨s, hiw, hs⟩
  exact Finset.disjoint_left.1 hc h1 h2

/-! ### Basic facts about the extremal configuration -/

theorem compat_Δ {r : V → V → Prop} (hr : IsOriented r) :
    Disjoint (F1 r (Δ : Finset (V × V))) (F2 r Δ) := by
  rw [Finset.disjoint_left]
  intro z h1 h2
  obtain ⟨p, hp, hpz⟩ := mem_F1.1 h1
  obtain ⟨s, hs, hsz⟩ := mem_F2.1 h2
  have hp' : p = z.2 := mem_Δ.1 hp
  have hs' : z.1 = s := mem_Δ.1 hs
  subst hp'
  subst hs'
  exact hr.asymmetric hpz hsz

theorem compat_of_noconf {r : V → V → Prop} {R' C' : Finset (V × V)}
    (h : ∀ l ∈ R', ∀ c ∈ C', ¬ Pruning.Conflict r l c) : Disjoint (F1 r R') (F2 r C') := by
  rw [Finset.disjoint_left]
  intro z h1 h2
  obtain ⟨p, hp, hpz⟩ := mem_F1.1 h1
  obtain ⟨s, hs, hsz⟩ := mem_F2.1 h2
  exact h _ hp _ hs ⟨hpz, hsz⟩

theorem Δ_sub_R {r : V → V → Prop} {P Q : Finset (V × V)}
    (hΔP : Δ ⊆ P) (hc : Disjoint (F1 r P) (F2 r Q)) :
    (Δ : Finset (V × V)) ⊆ univ \ F2 r (F2 r Q) := by
  intro z hz
  obtain ⟨v, w⟩ := z
  have hvw : v = w := mem_Δ.1 hz
  subst hvw
  rw [Finset.mem_sdiff]
  refine ⟨Finset.mem_univ _, fun h => ?_⟩
  obtain ⟨s, hs, hsv⟩ := mem_F2.1 h
  have h1 : (v, s) ∈ F1 r P := mem_F1.2 ⟨s, hΔP (mem_Δ.2 rfl), hsv⟩
  exact Finset.disjoint_left.1 hc h1 hs

theorem Δ_sub_C {r : V → V → Prop} {P Q : Finset (V × V)}
    (hΔQ : Δ ⊆ Q) (hc : Disjoint (F1 r P) (F2 r Q)) :
    (Δ : Finset (V × V)) ⊆ univ \ F1 r (F1 r P) := by
  intro z hz
  obtain ⟨v, w⟩ := z
  have hvw : v = w := mem_Δ.1 hz
  subst hvw
  rw [Finset.mem_sdiff]
  refine ⟨Finset.mem_univ _, fun h => ?_⟩
  obtain ⟨p, hp, hpv⟩ := mem_F1.1 h
  have h2 : (p, v) ∈ F2 r Q := mem_F2.2 ⟨p, hΔQ (mem_Δ.2 rfl), hpv⟩
  exact Finset.disjoint_left.1 hc hp h2

/-- A diagonal left member conflicts with no right member of `C`. -/
theorem diag_free_L {r : V → V → Prop} {P : Finset (V × V)} (hΔP : Δ ⊆ P) (v : V)
    (c : V × V) (hcC : c ∈ univ \ F1 r (F1 r P)) : ¬ Pruning.Conflict r (v, v) c := by
  obtain ⟨i, s⟩ := c
  rintro ⟨hvi, hsv⟩
  have h1 : (v, s) ∈ F1 r P := mem_F1.2 ⟨s, hΔP (mem_Δ.2 rfl), hsv⟩
  have h2 : (i, s) ∈ F1 r (F1 r P) := mem_F1.2 ⟨v, h1, hvi⟩
  exact (Finset.mem_sdiff.1 hcC).2 h2

/-- A diagonal right member conflicts with no left member of `R`. -/
theorem diag_free_R {r : V → V → Prop} {Q : Finset (V × V)} (hΔQ : Δ ⊆ Q) (v : V)
    (l : V × V) (hlR : l ∈ univ \ F2 r (F2 r Q)) : ¬ Pruning.Conflict r l (v, v) := by
  obtain ⟨p, j⟩ := l
  rintro ⟨hpv, hvj⟩
  have h1 : (p, v) ∈ F2 r Q := mem_F2.2 ⟨p, hΔQ (mem_Δ.2 rfl), hpv⟩
  have h2 : (p, j) ∈ F2 r (F2 r Q) := mem_F2.2 ⟨v, h1, hvj⟩
  exact (Finset.mem_sdiff.1 hlR).2 h2

omit [Fintype V] [DecidableEq V] in
theorem mem_conflicts {r : V → V → Prop} {R C : Finset (V × V)} {lc : (V × V) × (V × V)} :
    lc ∈ Pruning.conflicts r R C ↔ (lc.1 ∈ R ∧ lc.2 ∈ C) ∧ Pruning.Conflict r lc.1 lc.2 := by
  simp only [Pruning.conflicts, Finset.mem_filter, Finset.mem_product]

omit [Fintype V] in
theorem mem_pointsH {r : V → V → Prop} {R C : Finset (V × V)} {h : V × V} :
    h ∈ Pruning.pointsH r R C ↔ ∃ lc ∈ Pruning.conflicts r R C, (lc.1.1, lc.2.2) = h := by
  simp only [Pruning.pointsH, Finset.mem_image]

theorem mem_uncovered {r : V → V → Prop} {R C R' C' : Finset (V × V)} {z : V × V} :
    z ∈ Pruning.uncovered r R C R' C' ↔ z ∈ Pruning.pointsZ r R C ∧
      (∀ l ∈ R', ¬ Pruning.CoversL r l z) ∧ (∀ c ∈ C', ¬ Pruning.CoversR r c z) := by
  simp only [Pruning.uncovered, Finset.mem_filter]

theorem pointsH_card_le {r : V → V → Prop} {P Q : Finset (V × V)} :
    (Pruning.pointsH r (univ \ F2 r (F2 r Q)) (univ \ F1 r (F1 r P))).card ≤ d r P Q := by
  apply Finset.card_le_card
  intro h hh
  rw [mem_pointsH] at hh
  obtain ⟨⟨⟨p, j⟩, ⟨i, s⟩⟩, hlc, rfl⟩ := hh
  rw [mem_conflicts] at hlc
  obtain ⟨⟨hl, hc'⟩, hpi, hsj⟩ := hlc
  simp only at hpi hsj
  rw [Finset.mem_sdiff, Finset.mem_union]
  refine ⟨Finset.mem_univ _, ?_⟩
  rintro (h1 | h2)
  · have h3 : (i, s) ∈ F1 r (F1 r P) := mem_F1.2 ⟨p, h1, hpi⟩
    exact (Finset.mem_sdiff.1 hc').2 h3
  · have h3 : (p, j) ∈ F2 r (F2 r Q) := mem_F2.2 ⟨s, h2, hsj⟩
    exact (Finset.mem_sdiff.1 hl).2 h3

theorem uncovered_card_le {r : V → V → Prop} {R C R' C' : Finset (V × V)} :
    (Pruning.uncovered r R C R' C').card ≤ d r R' C' := by
  apply Finset.card_le_card
  intro z hz
  rw [mem_uncovered] at hz
  obtain ⟨_, hL, hR⟩ := hz
  rw [Finset.mem_sdiff, Finset.mem_union]
  refine ⟨Finset.mem_univ _, ?_⟩
  rintro (h1 | h2)
  · obtain ⟨p, hp, hpz⟩ := mem_F1.1 h1
    exact hL (p, z.2) hp ⟨rfl, hpz⟩
  · obtain ⟨s, hs, hsz⟩ := mem_F2.1 h2
    exact hR (z.1, s) hs ⟨rfl, hsz⟩

end

end OAI.SeymourSecondNeighborhood.Sol_OAI_SeymourSecondNeighborhood_prop_4_1

open OAI.SeymourSecondNeighborhood in
open OAI.SeymourSecondNeighborhood.Sol_OAI_SeymourSecondNeighborhood_prop_4_1 in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (r : V → V → Prop)
    (hr : IsOriented r) (hin : PosIndeg r) : ¬ StrictExpander r := by
  intro hexp
  have hΩne : (Ω r).Nonempty := ⟨(Δ, Δ), mem_Ω.2 ⟨compat_Δ hr, subset_rfl, subset_rfl⟩⟩
  obtain ⟨⟨P, Q⟩, hPQ, hmax⟩ :=
    Finset.exists_max_image (Ω r) (fun pq => pq.1.card + pq.2.card + d r pq.1 pq.2) hΩne
  rw [mem_Ω] at hPQ
  obtain ⟨hc, hΔP, hΔQ⟩ := hPQ
  dsimp only at hc hΔP hΔQ hmax
  have hcol := column_ineq hexp (col_P_hyp hin hΔP hΔQ hc)
  have hrow := row_ineq hexp (col_Q_hyp hin hΔP hΔQ hc)
  have hRcard : (univ \ F2 r (F2 r Q)).card + (F2 r (F2 r Q)).card = (univ : Finset (V × V)).card :=
    Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _)
  have hCcard : (univ \ F1 r (F1 r P)).card + (F1 r (F1 r P)).card = (univ : Finset (V × V)).card :=
    Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _)
  have hd : d r P Q + (F1 r P ∪ F2 r Q).card = (univ : Finset (V × V)).card :=
    Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _)
  have hun : (F1 r P ∪ F2 r Q).card = (F1 r P).card + (F2 r Q).card :=
    Finset.card_union_of_disjoint hc
  obtain ⟨R', hR'R, C', hC'C, hnoconf, hretL, hretR, hbound⟩ :=
    Pruning.lemma_3_1 r (univ \ F2 r (F2 r Q)) (univ \ F1 r (F1 r P))
  have hR'card := Finset.card_sdiff_add_card_eq_card hR'R
  have hC'card := Finset.card_sdiff_add_card_eq_card hC'C
  have hH := pointsH_card_le (r := r) (P := P) (Q := Q)
  have hU := uncovered_card_le (r := r) (R := univ \ F2 r (F2 r Q)) (C := univ \ F1 r (F1 r P))
    (R' := R') (C' := C')
  have hΔR' : Δ ⊆ R' := by
    intro z hz
    obtain ⟨v, w⟩ := z
    have hvw : v = w := mem_Δ.1 hz
    subst hvw
    exact hretL _ (Δ_sub_R hΔP hc hz) (fun c hcC => diag_free_L hΔP v c hcC)
  have hΔC' : Δ ⊆ C' := by
    intro z hz
    obtain ⟨v, w⟩ := z
    have hvw : v = w := mem_Δ.1 hz
    subst hvw
    exact hretR _ (Δ_sub_C hΔQ hc hz) (fun l hlR => diag_free_R hΔQ v l hlR)
  have hΩ' : (R', C') ∈ Ω r := mem_Ω.2 ⟨compat_of_noconf hnoconf, hΔR', hΔC'⟩
  have hle := hmax (R', C') hΩ'
  simp only at hle
  omega
