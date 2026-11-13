-- Prove2me | solution 1 for LocalLemmaHierarchy.Completeness.theorem_3_7
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:44:00.65021+00:00
-- url     : https://prove2.me/submissions/040f5f00-32f8-4b5f-a0c3-98a3b75dc41b

import Mathlib
import Definitions.Def_LocalLemmaHierarchy_Completeness_Representation
import Definitions.Def_LocalLemmaHierarchy_Completeness_Histories
import Definitions.Def_LocalLemmaHierarchy_Completeness_Memory
import Theorems.Thm_LocalLemmaHierarchy_Completeness_theorem_3_2
import Theorems.Thm_LocalLemmaHierarchy_Completeness_proposition_3_4
import Theorems.Thm_LocalLemmaHierarchy_Completeness_lemma_3_6
import Theorems.Thm_LocalLemmaHierarchy_Completeness_lemma_3_5
import Theorems.Thm_LocalLemmaHierarchy_Completeness_proposition_2_4

section
set_option autoImplicit false

open scoped ENNReal NNReal

namespace LocalLemmaHierarchy.Completeness.Dev.T32

open scoped Classical

variable {V T : Type} {R : PosLocalDeletionRep V T}

theorem endpointOf_append (s : V) (l1 l2 : List (Move R)) :
    Hist.endpointOf s (l1 ++ l2) = Hist.endpointOf (Hist.endpointOf s l1) l2 := by
  unfold Hist.endpointOf
  rw [List.getLast?_append]
  cases h2 : l2.getLast? <;> simp

theorem mem_deleted (ms : List (Move R)) (w : V) :
    w ∈ deleted R ms ↔ ∃ m ∈ ms, w ∈ departure R m := by
  induction ms with
  | nil => simp [deleted]
  | cons m ms ih =>
    have : deleted R (m :: ms) = departure R m ∪ deleted R ms := by simp [deleted]
    rw [this, Finset.mem_union, ih]
    simp

theorem deleted_mono {l l' : List (Move R)} (h : ∀ m ∈ l, m ∈ l') : deleted R l ⊆ deleted R l' := by
  intro w hw
  rw [mem_deleted] at hw ⊢
  obtain ⟨m, hm, hw⟩ := hw
  exact ⟨m, h m hm, hw⟩

/-- A suffix of a history exact in `U` is an ambient exact history of at most `j` moves. -/
theorem suffix_state {U : Set V} {h : Hist R} (he : IsExact R U h) (j : ℕ) :
    IsMemState R j (h.suffix j) := by
  refine ⟨⟨Set.mem_univ _, ?_⟩, ?_⟩
  · intro i hi
    set k := h.moves.length - j with hk
    have hi' : i < (h.moves.drop k).length := hi
    rw [List.length_drop] at hi'
    have hki : k + i < h.moves.length := by omega
    have hget : (h.suffix j).moves[i] = h.moves[k + i] := by
      simp only [Hist.suffix]
      rw [List.getElem_drop]
    have htake : h.moves.take (k + i) = h.moves.take k ++ (h.moves.drop k).take i := by
      rw [List.take_add]
    have hleg := he.2 (k + i) hki
    obtain ⟨h1, h2, h3, h4⟩ := hleg
    have hsub : deleted R ((h.suffix j).moves.take i) ⊆ deleted R (h.moves.take (k + i)) := by
      apply deleted_mono
      intro m hm
      rw [htake]
      exact List.mem_append_right _ hm
    have hend : Hist.endpointOf (h.suffix j).start ((h.suffix j).moves.take i)
        = Hist.endpointOf h.start (h.moves.take (k + i)) := by
      rw [htake, endpointOf_append]
      rfl
    show LegalExactStep R Set.univ (h.suffix j).start ((h.suffix j).moves.take i)
        ((h.suffix j).moves[i])
    rw [hget]
    refine ⟨by rw [hend]; exact h1, ?_, ?_, h4⟩
    · intro w hw
      have := h2 hw
      simp only [Set.mem_sdiff, Set.mem_univ, true_and, Finset.mem_coe] at this ⊢
      exact fun hh => this.2 (hsub hh)
    · refine ⟨h3.1, Set.mem_sdiff_of_mem (Set.mem_univ _) ?_⟩
      intro hh
      have := h3.2
      simp only [Set.mem_sdiff, Finset.mem_coe] at this
      exact this.2 (hsub hh)
  · show ((h.moves).drop (h.moves.length - j)).length ≤ j
    simp only [List.length_drop]
    omega

/-- Appending a legal move to an exact history. -/
theorem append_exact {U : Set V} {s : Hist R} (hs : IsExact R U s) (m : Move R)
    (hm : LegalExactStep R U s.start s.moves m) : IsExact R U (s.append m) := by
  refine ⟨hs.1, ?_⟩
  intro i hi
  have hi' : i < s.moves.length + 1 := by
    simpa [Hist.append] using hi
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hlt | heq
  · have := hs.2 i hlt
    have e1 : (s.append m).moves.take i = s.moves.take i := by
      simp only [Hist.append]
      rw [List.take_append_of_le_length hlt.le]
    have e2 : (s.append m).moves[i] = s.moves[i] := by
      simp only [Hist.append]
      rw [List.getElem_append_left hlt]
    show LegalExactStep R U s.start ((s.append m).moves.take i) ((s.append m).moves[i])
    rw [e1, e2]
    exact this
  · subst heq
    have e1 : (s.append m).moves.take s.moves.length = s.moves := by
      simp [Hist.append]
    have e2 : (s.append m).moves[s.moves.length] = m := by
      simp [Hist.append]
    show LegalExactStep R U s.start ((s.append m).moves.take s.moves.length)
      ((s.append m).moves[s.moves.length])
    rw [e1, e2]
    exact hm

end LocalLemmaHierarchy.Completeness.Dev.T32
end

section
set_option autoImplicit false

open scoped ENNReal NNReal

namespace LocalLemmaHierarchy.Completeness.Dev.T37

open scoped Classical

variable {V T : Type} {R : PosLocalDeletionRep V T} {Z : Finset V → MvPolynomial T ℝ}

/-- evaluation of the deletion identity at the uniform point `t`. -/
theorem eval_step (hRZ : IsRepresentationOf R Z) (t : ℝ) (U : Finset V) (v : V) (hv : v ∈ U) :
    MvPolynomial.eval (fun _ : T => t) (Z U) =
      MvPolynomial.eval (fun _ : T => t) (Z (U.erase v)) +
        ∑ a ∈ Finset.univ.filter (fun a : R.Opt v => R.A v a ⊆ U),
          R.c v a * t * MvPolynomial.eval (fun _ : T => t) (Z (U \ R.D v a)) := by
  conv_lhs => rw [hRZ.2.2 U v hv]
  simp [map_add, map_sum]

theorem card_lt_sdiff (U : Finset V) (v : V) (hv : v ∈ U) (D : Finset V) (hD : v ∈ D) :
    (U \ D).card < U.card :=
  Finset.card_lt_card ⟨Finset.sdiff_subset, fun h => (Finset.mem_sdiff.mp (h hv)).2 hD⟩

theorem Z_eval_ge_one (hRZ : IsRepresentationOf R Z) (t : ℝ) (ht : 0 ≤ t) :
    ∀ n : ℕ, ∀ U : Finset V, U.card = n → 1 ≤ MvPolynomial.eval (fun _ : T => t) (Z U) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro U hU
    rcases U.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
    · rw [hRZ.1]; simp
    · rw [eval_step hRZ t U v hv]
      have h1 : 1 ≤ MvPolynomial.eval (fun _ : T => t) (Z (U.erase v)) :=
        ih _ (by rw [← hU]; exact Finset.card_erase_lt_of_mem hv) _ rfl
      have h2 : 0 ≤ ∑ a ∈ Finset.univ.filter (fun a : R.Opt v => R.A v a ⊆ U),
          R.c v a * t * MvPolynomial.eval (fun _ : T => t) (Z (U \ R.D v a)) := by
        apply Finset.sum_nonneg
        intro a ha
        have hvD : v ∈ R.D v a := R.A_subset_D v a (R.self_mem_A v a)
        have := ih _ (by rw [← hU]; exact card_lt_sdiff U v hv _ hvD) (U \ R.D v a) rfl
        exact mul_nonneg (mul_nonneg (R.c_pos v a).le ht) (by linarith)
      linarith

theorem Z_eq_one_of_no_opt (hRZ : IsRepresentationOf R Z) (hno : ¬ ∃ v : V, Nonempty (R.Opt v)) :
    ∀ n : ℕ, ∀ U : Finset V, U.card = n → Z U = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro U hU
    rcases U.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
    · exact hRZ.1
    · have hE : IsEmpty (R.Opt v) := not_nonempty_iff.mp (fun h => hno ⟨v, h⟩)
      rw [hRZ.2.2 U v hv]
      simp [ih _ (by rw [← hU]; exact Finset.card_erase_lt_of_mem hv) (U.erase v) rfl]

theorem Z_ne_one_of_opt (hRZ : IsRepresentationOf R Z) (v : V) (a : R.Opt v) :
    Z (R.A v a) ≠ 1 := by
  intro h
  set U := R.A v a with hUdef
  have hv : v ∈ U := R.self_mem_A v a
  have h1 := eval_step hRZ 1 U v hv
  rw [h] at h1
  simp only [map_one] at h1
  have e1 : 1 ≤ MvPolynomial.eval (fun _ : T => (1 : ℝ)) (Z (U.erase v)) :=
    Z_eval_ge_one hRZ 1 zero_le_one _ _ rfl
  have hnn : ∀ a' ∈ Finset.univ.filter (fun a : R.Opt v => R.A v a ⊆ U),
      0 ≤ R.c v a' * 1 * MvPolynomial.eval (fun _ : T => (1 : ℝ)) (Z (U \ R.D v a')) := by
    intro a' _
    have := Z_eval_ge_one hRZ 1 zero_le_one _ _ (rfl : (U \ R.D v a').card = _)
    exact mul_nonneg (mul_nonneg (R.c_pos v a').le zero_le_one) (by linarith)
  have hmem : a ∈ Finset.univ.filter (fun a : R.Opt v => R.A v a ⊆ U) := by
    simp [hUdef]
  have hs := Finset.single_le_sum hnn hmem
  have e2 : 1 ≤ MvPolynomial.eval (fun _ : T => (1 : ℝ)) (Z (U \ R.D v a)) :=
    Z_eval_ge_one hRZ 1 zero_le_one _ _ rfl
  have := R.c_pos v a
  nlinarith

theorem nonconstant_iff (hRZ : IsRepresentationOf R Z) :
    IsNonconstant Z ↔ ∃ v : V, Nonempty (R.Opt v) := by
  constructor
  · rintro ⟨U, hU⟩
    by_contra hno
    exact hU (Z_eq_one_of_no_opt hRZ hno _ U rfl)
  · rintro ⟨v, ⟨a⟩⟩
    exact ⟨_, Z_ne_one_of_opt hRZ v a⟩

end LocalLemmaHierarchy.Completeness.Dev.T37
end

section
set_option autoImplicit false

open scoped ENNReal NNReal

namespace LocalLemmaHierarchy.Completeness.Dev.T37

open scoped Classical
open LocalLemmaHierarchy.Completeness.Dev.T32

variable {V T : Type} {R : PosLocalDeletionRep V T}

theorem cstar_le (v : V) (a : R.Opt v) : R.cstar ≤ R.c v a := by
  obtain ⟨c₀, h0, hc⟩ := R.cstar_pos
  exact ciInf_le ⟨c₀, by rintro _ ⟨p, rfl⟩; exact hc p.1 p.2⟩ (⟨v, a⟩ : Σ v : V, R.Opt v)

theorem cstar_pos' (hne : ∃ v : V, Nonempty (R.Opt v)) : 0 < R.cstar := by
  obtain ⟨c₀, h0, hc⟩ := R.cstar_pos
  obtain ⟨v, ⟨a⟩⟩ := hne
  have : Nonempty (Σ v : V, R.Opt v) := ⟨⟨v, a⟩⟩
  exact lt_of_lt_of_le h0 (le_ciInf fun p => hc p.1 p.2)

/-- rows of the abstract system of Lemma 3.5 -/
noncomputable def rowA (R : PosLocalDeletionRep V T) (q : ℕ) (s : Hist R) :
    Finset (Σ s : Hist R, R.Opt s.endpoint) :=
  if IsMemState R q s then
    (Finset.univ.filter (fun a : R.Opt s.endpoint =>
      Disjoint (R.A s.endpoint a) (deleted R s.moves))).image (fun a => ⟨s, a⟩)
  else ∅

noncomputable def rowT (R : PosLocalDeletionRep V T) (ν : ℝ) (_ : Hist R)
    (i : Σ s : Hist R, R.Opt s.endpoint) : ℝ := R.c i.1.endpoint i.2 * ν

noncomputable def rowC (R : PosLocalDeletionRep V T) (q : ℕ) (_ : Hist R)
    (i : Σ s : Hist R, R.Opt s.endpoint) : Multiset (Hist R) :=
  (R.D i.1.endpoint i.2 \ insert i.1.endpoint (deleted R i.1.moves)).val.map
    (fun u => memStar q i.1 i.2 u)

theorem row_eq (q : ℕ) (ν : ℝ) (x : Hist R → ℝ) (s : Hist R) (hs : IsMemState R q s) :
    productRowUpdate (rowA R q) (rowT R ν) (rowC R q) x s = memUpdate R q (fun _ => ν) x s := by
  unfold productRowUpdate rowA
  rw [if_pos hs, Finset.sum_image (fun a _ b _ h => eq_of_heq (Sigma.mk.inj h).2)]
  unfold memUpdate
  refine Finset.sum_congr rfl (fun a _ => ?_)
  simp only [rowT, rowC, Multiset.map_map, Function.comp]
  rw [Finset.prod_eq_multiset_prod]

theorem row_nonstate (q : ℕ) (ν : ℝ) (x : Hist R → ℝ) (s : Hist R) (hs : ¬ IsMemState R q s) :
    productRowUpdate (rowA R q) (rowT R ν) (rowC R q) x s = 0 := by
  simp [productRowUpdate, rowA, hs]

theorem child_state (q : ℕ) (s : Hist R) (hs : IsMemState R q s) (a : R.Opt s.endpoint)
    (ha : Disjoint (R.A s.endpoint a) (deleted R s.moves)) (u : V)
    (hu : u ∈ R.D s.endpoint a \ insert s.endpoint (deleted R s.moves)) :
    IsMemState R q (memStar q s a u) := by
  simp only [Finset.mem_sdiff, Finset.mem_insert, not_or] at hu
  have hex : IsExact R Set.univ (s.append ⟨s.endpoint, a, u⟩) := by
    refine append_exact hs.1 _ ⟨rfl, ?_, ⟨hu.1, ?_⟩, hu.2.1⟩
    · intro w hw
      simp only [Set.mem_sdiff, Set.mem_univ, true_and, Finset.mem_coe]
      exact fun h => Finset.disjoint_left.mp ha hw h
    · simp only [Set.mem_sdiff, Set.mem_univ, true_and, Finset.mem_coe]
      exact hu.2.2
  exact suffix_state hex q

theorem one_le_inv_of {y : ℝ} (h0 : 0 ≤ y) (h1 : y < 1) : 1 ≤ (1 - y)⁻¹ := by
  rw [one_le_inv₀ (by linarith)]; linarith

theorem memUpdate_ge (q : ℕ) (ν : ℝ) (hν : 0 < ν) (x : Hist R → ℝ)
    (hx : ∀ s, 0 ≤ x s ∧ x s < 1) (s : Hist R) (a : R.Opt s.endpoint)
    (ha : Disjoint (R.A s.endpoint a) (deleted R s.moves)) :
    R.cstar * ν ≤ memUpdate R q (fun _ => ν) x s := by
  have hprod : ∀ a' : R.Opt s.endpoint, 1 ≤ ∏ u ∈ R.D s.endpoint a' \ insert s.endpoint (deleted R s.moves),
      (1 - x (memStar q s a' u))⁻¹ := by
    intro a'
    calc (1 : ℝ) = ∏ u ∈ R.D s.endpoint a' \ insert s.endpoint (deleted R s.moves), (1 : ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one)
          (fun u _ => one_le_inv_of (hx _).1 (hx _).2)
  have hnn : ∀ a' ∈ Finset.univ.filter
      (fun a : R.Opt s.endpoint => Disjoint (R.A s.endpoint a) (deleted R s.moves)),
      0 ≤ R.c s.endpoint a' * ν * ∏ u ∈ R.D s.endpoint a' \ insert s.endpoint (deleted R s.moves),
        (1 - x (memStar q s a' u))⁻¹ := by
    intro a' _
    exact mul_nonneg (mul_nonneg (R.c_pos _ _).le hν.le) (le_trans zero_le_one (hprod a'))
  have hmem : a ∈ Finset.univ.filter
      (fun a : R.Opt s.endpoint => Disjoint (R.A s.endpoint a) (deleted R s.moves)) := by
    simp [ha]
  have hs := Finset.single_le_sum hnn hmem
  have h1 : R.cstar * ν ≤ R.c s.endpoint a * ν :=
    mul_le_mul_of_nonneg_right (cstar_le _ _) hν.le
  have h2 : R.c s.endpoint a * ν ≤ R.c s.endpoint a * ν *
      ∏ u ∈ R.D s.endpoint a \ insert s.endpoint (deleted R s.moves), (1 - x (memStar q s a u))⁻¹ :=
    le_mul_of_one_le_right (mul_nonneg (R.c_pos _ _).le hν.le) (hprod a)
  unfold memUpdate
  linarith

theorem memUpdate_scale (q : ℕ) (ν l : ℝ) (hν : 0 < ν) (x : Hist R → ℝ) (s : Hist R) :
    memUpdate R q (fun _ => l) x s = l / ν * memUpdate R q (fun _ => ν) x s := by
  unfold memUpdate
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  field_simp

theorem memUpdate_noopt (q : ℕ) (p : T → ℝ) (x : Hist R → ℝ) (s : Hist R)
    (h : ∀ a : R.Opt s.endpoint, ¬ Disjoint (R.A s.endpoint a) (deleted R s.moves)) :
    memUpdate R q p x s = 0 := by
  unfold memUpdate
  apply Finset.sum_eq_zero
  intro a ha
  exact absurd (Finset.mem_filter.mp ha).2 (h a)

end LocalLemmaHierarchy.Completeness.Dev.T37
end

section
set_option autoImplicit false

open scoped ENNReal NNReal
open Filter Topology

namespace LocalLemmaHierarchy.Completeness.Dev.T37

open scoped Classical
open LocalLemmaHierarchy.Completeness.Dev.T32

variable {V T : Type} {R : PosLocalDeletionRep V T} {Z : Finset V → MvPolynomial T ℝ}

theorem mem_le_unif (hRZ : IsRepresentationOf R Z) (q : ℕ) : memRadius R q ≤ uniformRadius Z := by
  have h := (theorem_3_2 R Z hRZ).2
  rcases q with _ | q
  · exact (h 0).1.trans (h 0).2
  · exact (h q).2

theorem one_site_exact (v : V) : IsExact R Set.univ (⟨v, []⟩ : Hist R) :=
  ⟨Set.mem_univ _, fun i hi => absurd hi (by simp)⟩

theorem radius_le (hRZ : IsRepresentationOf R Z) (hne : ∃ v : V, Nonempty (R.Opt v)) :
    uniformRadius Z ≤ ENNReal.ofReal (1 / R.cstar) := by
  by_contra hlt
  rw [not_le] at hlt
  have hcs := cstar_pos' hne
  obtain ⟨v, ⟨a⟩⟩ := hne
  have hν : 0 < 1 / R.cstar := by positivity
  have h34 := proposition_3_4 R Z hRZ (1 / R.cstar) hν hlt
  have hex := one_site_exact (R := R) v
  have hav : HasAvailableOption R (⟨v, []⟩ : Hist R) :=
    ⟨a, by simp [deleted]⟩
  have h1 := h34.2.2.2.2.1 _ hex hav
  have h2 := (h34.2.1 _ hex).2.2.2
  have : R.cstar * (1 / R.cstar) = 1 := by field_simp
  linarith

theorem zero_case (hRZ : IsRepresentationOf R Z) (hno : ¬ ∃ v : V, Nonempty (R.Opt v)) :
    uniformRadius Z = ⊤ ∧ ∀ q, memRadius R q = ⊤ := by
  have hZ : ∀ U, Z U = 1 := fun U => Z_eq_one_of_no_opt hRZ hno _ U rfl
  refine ⟨?_, fun q => ?_⟩
  · unfold uniformRadius
    refine le_antisymm le_top (le_iInf fun U => ?_)
    exact ((proposition_2_4 R Z hRZ U).2.2.1.mpr (hZ U)).ge
  · refine le_antisymm le_top ?_
    refine ENNReal.le_of_forall_nnreal_lt fun r _ => ?_
    refine le_iSup₂_of_le r ⟨fun _ => 0, ?_⟩ le_rfl
    intro s _
    refine ⟨le_rfl, zero_lt_one, ?_⟩
    rw [memUpdate_noopt q _ _ s (fun a => absurd ⟨_, ⟨a⟩⟩ hno)]

theorem lower_cert (hRZ : IsRepresentationOf R Z) (hne : ∃ v : V, Nonempty (R.Opt v))
    (q : ℕ) (hq : 1 ≤ q) (r : ℝ≥0) (Rr : ℝ) (hRr : uniformRadius Z = ENNReal.ofReal Rr)
    (hr : (r : ℝ) < Rr - 1 / (R.cstar * q)) :
    ∃ x : Hist R → ℝ, IsMemCertificate R q (fun _ => (r : ℝ)) x := by
  have hcs := cstar_pos' hne
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hcq : 0 < 1 / (R.cstar * q) := by positivity
  have hr0 : (0 : ℝ) ≤ r := r.2
  have hRpos : 0 < Rr := by linarith
  set ν : ℝ := ((r : ℝ) + 1 / (R.cstar * q) + Rr) / 2 with hνdef
  have hν1 : (r : ℝ) + 1 / (R.cstar * q) < ν := by rw [hνdef]; linarith
  have hν2 : ν < Rr := by rw [hνdef]; linarith
  have hν : 0 < ν := by linarith
  have hνR : ENNReal.ofReal ν < uniformRadius Z := by
    rw [hRr]; exact (ENNReal.ofReal_lt_ofReal_iff hRpos).mpr hν2
  have h34 := proposition_3_4 R Z hRZ ν hν hνR
  set b : ℝ := ν / Rr with hbdef
  have hb0 : 0 ≤ b := by positivity
  have hb1 : b < 1 := by rw [hbdef, div_lt_one hRpos]; exact hν2
  have hX : ∀ h : Hist R, IsExact R Set.univ h →
      0 ≤ canonicalBranch R ν h ∧ canonicalBranch R ν h ≤ b := by
    intro h hh
    obtain ⟨_, h0, h1, _⟩ := h34.2.1 h hh
    refine ⟨h0, ?_⟩
    rw [hRr, ← ENNReal.ofReal_div_of_pos hRpos, ENNReal.ofReal_le_ofReal_iff hb0] at h1
    exact h1
  set Y : ℕ → Hist R → ℝ := fun j s =>
    if IsMemState R q s then canonicalBranch R ν (s.suffix j) else 0 with hYdef
  have hY : ∀ j ≤ q, ∀ s, 0 ≤ Y j s ∧ Y j s ≤ b := by
    intro j _ s
    by_cases hs : IsMemState R q s
    · simp only [hYdef, if_pos hs]
      exact hX _ (suffix_state hs.1 j).1
    · simp only [hYdef, if_neg hs]; exact ⟨le_rfl, hb0⟩
  have hF : ∀ j, 1 ≤ j → j ≤ q → ∀ s, productRowUpdate (rowA R q) (rowT R ν) (rowC R q) (Y j) s
      ≤ Y (j - 1) s := by
    intro j hj1 hjq s
    by_cases hs : IsMemState R q s
    · rw [row_eq q ν _ s hs]
      have h36 := lemma_3_6 R Z hRZ ν hν hνR q j hj1 hjq s hs
      have : memUpdate R q (fun _ => ν) (Y j) s =
          memUpdate R q (fun _ => ν) (fun s' => canonicalBranch R ν (s'.suffix j)) s := by
        unfold memUpdate
        refine Finset.sum_congr rfl (fun a ha => ?_)
        congr 1
        refine Finset.prod_congr rfl (fun u hu => ?_)
        have hc := child_state q s hs a (Finset.mem_filter.mp ha).2 u hu
        simp only [hYdef, if_pos hc]
      rw [this]
      simp only [hYdef, if_pos hs]
      exact h36
    · rw [row_nonstate q ν _ s hs]
      simp only [hYdef, if_neg hs]; exact le_rfl
  have key := lemma_3_5 (rowA R q) (rowT R ν) (rowC R q)
    (fun s i _ => mul_pos (R.c_pos _ _) hν) q hq b hb0 hb1 Y hY hF
  obtain ⟨hx, hx2⟩ := key
  refine ⟨fun s => 1 - (∏ j ∈ Finset.Icc 1 q, (1 - Y j s)) ^ ((1 : ℝ) / q), ?_⟩
  intro s hs
  have hxs : ∀ s', 0 ≤ (1 - (∏ j ∈ Finset.Icc 1 q, (1 - Y j s')) ^ ((1 : ℝ) / q)) ∧
      (1 - (∏ j ∈ Finset.Icc 1 q, (1 - Y j s')) ^ ((1 : ℝ) / q)) < 1 :=
    fun s' => ⟨(hx s').1, lt_of_le_of_lt (hx s').2 hb1⟩
  refine ⟨(hxs s).1, (hxs s).2, ?_⟩
  set x : Hist R → ℝ := fun s => 1 - (∏ j ∈ Finset.Icc 1 q, (1 - Y j s)) ^ ((1 : ℝ) / q) with hxdef
  have hM : memUpdate R q (fun _ => ν) x s ≤ x s + 1 / q := by
    rw [← row_eq q ν x s hs]; exact (hx2 s).1.trans (hx2 s).2
  by_cases hav : ∃ a : R.Opt s.endpoint, Disjoint (R.A s.endpoint a) (deleted R s.moves)
  · obtain ⟨a, ha⟩ := hav
    have hge := memUpdate_ge q ν hν x hxs s a ha
    rw [memUpdate_scale q ν (r : ℝ) hν x s]
    have hu0 : 0 ≤ 1 - (r : ℝ) / ν := by
      rw [sub_nonneg, div_le_one hν]; linarith
    have hkey : 1 / (q : ℝ) ≤ (ν - r) * R.cstar := by
      calc 1 / (q : ℝ) = (1 / (R.cstar * q)) * R.cstar := by field_simp
        _ ≤ (ν - r) * R.cstar := mul_le_mul_of_nonneg_right (by linarith) hcs.le
    have h1 := mul_le_mul_of_nonneg_left hge hu0
    have h2 : (1 - (r : ℝ) / ν) * (R.cstar * ν) = (ν - r) * R.cstar := by field_simp
    have h3 : (r : ℝ) / ν * memUpdate R q (fun _ => ν) x s =
        memUpdate R q (fun _ => ν) x s - (1 - (r : ℝ) / ν) * memUpdate R q (fun _ => ν) x s := by ring
    linarith
  · push Not at hav
    rw [memUpdate_noopt q _ x s hav]
    exact (hxs s).1

end LocalLemmaHierarchy.Completeness.Dev.T37

namespace LocalLemmaHierarchy.Completeness

open Dev.T37 in
theorem chk_theorem_3_7 {V T : Type} (R : PosLocalDeletionRep V T)
    (Z : Finset V → MvPolynomial T ℝ) (hRZ : IsRepresentationOf R Z) :
    Monotone (fun q => memRadius R q) ∧
    Tendsto (fun q => memRadius R q) atTop (𝓝 (uniformRadius Z)) ∧
    (IsNonconstant Z ↔ ∃ v : V, Nonempty (R.Opt v)) ∧
    (IsNonconstant Z →
      uniformRadius Z ≤ ENNReal.ofReal (1 / R.cstar) ∧
      ∀ q : ℕ, 1 ≤ q →
        ENNReal.ofReal ((uniformRadius Z).toReal - 1 / (R.cstar * q)) ≤ memRadius R q ∧
        memRadius R q ≤ uniformRadius Z) := by
  have hmono : Monotone (fun q => memRadius R q) :=
    monotone_nat_of_le_succ (fun q => ((theorem_3_2 R Z hRZ).2 q).1)
  by_cases hne : ∃ v : V, Nonempty (R.Opt v)
  · have hle := radius_le hRZ hne
    have hcs := cstar_pos' hne
    have hRfin : uniformRadius Z ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
    have hlow : ∀ q : ℕ, 1 ≤ q →
        ENNReal.ofReal ((uniformRadius Z).toReal - 1 / (R.cstar * q)) ≤ memRadius R q := by
      intro q hq
      refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
      have hr' : (r : ℝ) < (uniformRadius Z).toReal - 1 / (R.cstar * q) := by
        have := (ENNReal.lt_ofReal_iff_toReal_lt ENNReal.coe_ne_top).mp hr
        simpa using this
      have cert := lower_cert hRZ hne q hq r (uniformRadius Z).toReal
        (ENNReal.ofReal_toReal hRfin).symm hr'
      exact le_iSup₂_of_le r cert le_rfl
    refine ⟨hmono, ?_, nonconstant_iff hRZ,
      fun _ => ⟨hle, fun q hq => ⟨hlow q hq, mem_le_unif hRZ q⟩⟩⟩
    have h0 : Tendsto (fun q : ℕ => 1 / (R.cstar * (q : ℝ))) atTop (𝓝 0) := by
      have := tendsto_const_div_atTop_nhds_zero_nat (1 / R.cstar)
      refine this.congr (fun q => ?_)
      simp [div_eq_mul_inv, mul_comm]
    have hT : Tendsto (fun q : ℕ => ENNReal.ofReal ((uniformRadius Z).toReal - 1 / (R.cstar * q)))
        atTop (𝓝 (uniformRadius Z)) := by
      have := ENNReal.tendsto_ofReal ((tendsto_const_nhds (x := (uniformRadius Z).toReal)).sub h0)
      rw [sub_zero, ENNReal.ofReal_toReal hRfin] at this
      exact this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hT tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with q hq using hlow q hq
    · exact Filter.Eventually.of_forall (mem_le_unif hRZ)
  · obtain ⟨hU, hM⟩ := zero_case hRZ hne
    refine ⟨hmono, ?_, nonconstant_iff hRZ, fun h => absurd ((nonconstant_iff hRZ).mp h) hne⟩
    simp only [hU, hM]
    exact tendsto_const_nhds

end LocalLemmaHierarchy.Completeness
end

theorem solution : type_of% @LocalLemmaHierarchy.Completeness.chk_theorem_3_7 := @LocalLemmaHierarchy.Completeness.chk_theorem_3_7
