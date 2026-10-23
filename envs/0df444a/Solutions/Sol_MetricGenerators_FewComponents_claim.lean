-- Prove2me | solution 1 for MetricGenerators.FewComponents.claim
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T16:24:30.655282+00:00
-- url     : https://prove2.me/submissions/65c34bff-c240-4fde-9104-76b56b5208f1

import Mathlib
import Definitions.Def_MetricGenerators_FewComponents_TJoin
import Definitions.Def_MetricGenerators_FewComponents_ThreeDM
import Definitions.Def_MetricGenerators_FewComponents_Gadget

set_option autoImplicit false

open MetricGenerators.FewComponents in
theorem fc_not_adj_tt {q : ℕ} {H : Finset (Fin q × Fin q × Fin q)} (a b : Fin 4 × Fin q) :
    ¬ (gadget q H).Adj (GVert.t a) (GVert.t b) := by
  simp [gadget, gadgetAdj]

open MetricGenerators.FewComponents in
theorem fc_sum_le (q : ℕ) (H : Finset (Fin q × Fin q × Fin q)) (F : Finset (Sym2 (GVert q H)))
    (hF : (↑F : Set (Sym2 (GVert q H))) ⊆ (gadget q H).edgeSet) :
    ∑ a : Fin 4 × Fin q, edgeDeg F (GVert.t a) ≤ F.card := by
  unfold edgeDeg
  rw [← Finset.card_biUnion]
  · apply Finset.card_le_card
    intro e he
    simp only [Finset.mem_biUnion, Finset.mem_filter] at he
    obtain ⟨_, _, he, _⟩ := he
    exact he
  · intro a _ b _ hab
    rw [Function.onFun, Finset.disjoint_left]
    intro e he1 he2
    simp only [Finset.mem_filter] at he1 he2
    have hne : GVert.t (H := H) a ≠ GVert.t b := fun h => hab (GVert.t.inj h)
    have := (Sym2.mem_and_mem_iff hne).1 ⟨he1.2, he2.2⟩
    have hadj := hF he1.1
    rw [this, SimpleGraph.mem_edgeSet] at hadj
    exact fc_not_adj_tt a b hadj

open MetricGenerators.FewComponents in
theorem fc_card_ge (q : ℕ) (H : Finset (Fin q × Fin q × Fin q)) (F : Finset (Sym2 (GVert q H)))
    (hF : IsTJoin (gadget q H) (gadgetT q H) F) : 4 * q ≤ F.card := by
  have h1 : ∀ a ∈ (Finset.univ : Finset (Fin 4 × Fin q)), 1 ≤ edgeDeg F (GVert.t a) := fun a _ => by
    have : Odd (edgeDeg F (GVert.t a)) := (hF.2 _).2 (by simp [gadgetT])
    exact this.pos
  calc 4 * q = ∑ a : Fin 4 × Fin q, 1 := by simp
    _ ≤ ∑ a : Fin 4 × Fin q, edgeDeg F (GVert.t a) := Finset.sum_le_sum h1
    _ ≤ F.card := fc_sum_le q H F hF.1

def fc_sw : Fin 4 → Fin 4 := fun i => if i = 0 then 1 else if i = 1 then 0 else if i = 2 then 3 else 2

theorem fc_sw_sw : ∀ i, fc_sw (fc_sw i) = i := by decide

theorem fc_sw_ne : ∀ i, fc_sw i ≠ i := by decide

def fc_p {q : ℕ} (a : Fin 4 × Fin q) : Fin 4 × Fin q := (fc_sw a.1, a.2)

theorem fc_p_p {q : ℕ} (a : Fin 4 × Fin q) : fc_p (fc_p a) = a := by
  simp [fc_p, fc_sw_sw]

theorem fc_p_ne {q : ℕ} (a : Fin 4 × Fin q) : fc_p a ≠ a := by
  intro h
  exact fc_sw_ne a.1 (congrArg Prod.fst h)

theorem fc_nd {q : ℕ} (a : Fin 4 × Fin q) : ¬ (s(a, fc_p a)).IsDiag := by
  rw [Sym2.mk_isDiag_iff]; exact (fc_p_ne a).symm

theorem fc_pair_eq {q : ℕ} (a b : Fin 4 × Fin q) :
    s(a, fc_p a) = s(b, fc_p b) ↔ a = b ∨ a = fc_p b := by
  rw [Sym2.eq_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl ⟨h, by rw [h]⟩
    · exact Or.inr ⟨h, by rw [h, fc_p_p]⟩

open MetricGenerators.FewComponents in
def fc_E (q : ℕ) (H : Finset (Fin q × Fin q × Fin q)) (a : Fin 4 × Fin q) : Sym2 (GVert q H) :=
  s(GVert.t a, GVert.mid ⟨s(a, fc_p a), fc_nd a⟩)

open MetricGenerators.FewComponents in
def fc_F0 (q : ℕ) (H : Finset (Fin q × Fin q × Fin q)) : Finset (Sym2 (GVert q H)) :=
  Finset.univ.image (fc_E q H)

open MetricGenerators.FewComponents in
theorem fc_E_inj (q : ℕ) (H : Finset (Fin q × Fin q × Fin q)) : Function.Injective (fc_E q H) := by
  intro a b h
  simp [fc_E] at h
  exact h.1

open MetricGenerators.FewComponents in
theorem fc_deg_F0 (q : ℕ) (H : Finset (Fin q × Fin q × Fin q)) (v : GVert q H) :
    edgeDeg (fc_F0 q H) v = (Finset.univ.filter (fun a => v ∈ fc_E q H a)).card := by
  unfold edgeDeg fc_F0
  rw [Finset.filter_image, Finset.card_image_of_injective _ (fc_E_inj q H)]

open MetricGenerators.FewComponents in
theorem fc_F0_tjoin (q : ℕ) (H : Finset (Fin q × Fin q × Fin q)) :
    IsTJoin (gadget q H) (gadgetT q H) (fc_F0 q H) := by
  refine ⟨?_, ?_⟩
  · intro e he
    simp only [fc_F0, Finset.coe_image, Set.mem_image, Finset.coe_univ, Set.mem_univ,
      true_and] at he
    obtain ⟨a, rfl⟩ := he
    rw [fc_E, SimpleGraph.mem_edgeSet]
    show a ∈ s(a, fc_p a)
    exact Sym2.mem_mk_left _ _
  · intro v
    rw [fc_deg_F0]
    cases v with
    | t b =>
      have : Finset.univ.filter (fun a => GVert.t b ∈ fc_E q H a) = {b} := by
        ext a; simp [fc_E, eq_comm]
      rw [this]; simp [gadgetT]
    | mid e =>
      have hT : GVert.mid e ∉ gadgetT q H := by simp [gadgetT]
      simp only [hT, iff_false]
      by_cases hb : ∃ b, e.1 = s(b, fc_p b)
      · obtain ⟨b, hb⟩ := hb
        have : Finset.univ.filter (fun a => GVert.mid e ∈ fc_E q H a) = {b, fc_p b} := by
          ext a
          simp only [fc_E, Finset.mem_filter, Finset.mem_univ, true_and, Sym2.mem_iff,
            reduceCtorEq, false_or, GVert.mid.injEq, Subtype.ext_iff, hb, Finset.mem_insert,
            Finset.mem_singleton]
          rw [eq_comm, fc_pair_eq]
        rw [this, Finset.card_pair (fc_p_ne b).symm]
        decide
      · have : Finset.univ.filter (fun a => GVert.mid e ∈ fc_E q H a) = ∅ := by
          ext a
          simp only [fc_E, Finset.mem_filter, Finset.mem_univ, true_and, Sym2.mem_iff,
            reduceCtorEq, false_or, GVert.mid.injEq, Subtype.ext_iff, Finset.notMem_empty,
            iff_false]
          intro h
          exact hb ⟨a, h⟩
        rw [this]; simp
    | h m =>
      have : Finset.univ.filter (fun a => GVert.h m ∈ fc_E q H a) = ∅ := by
        ext a; simp [fc_E]
      rw [this]; simp [gadgetT]

open MetricGenerators.FewComponents in
theorem fc_card_F0 (q : ℕ) (H : Finset (Fin q × Fin q × Fin q)) : (fc_F0 q H).card ≤ 4 * q := by
  unfold fc_F0
  exact Finset.card_image_le.trans (by simp)

open MetricGenerators.FewComponents in
theorem fc_deg_one (q : ℕ) (H : Finset (Fin q × Fin q × Fin q)) (F : Finset (Sym2 (GVert q H)))
    (hF : IsMinTJoin (gadget q H) (gadgetT q H) F) : ∀ a, edgeDeg F (GVert.t a) = 1 := by
  have hle : F.card ≤ 4 * q := (hF.2 _ (fc_F0_tjoin q H)).trans (fc_card_F0 q H)
  have h1 : ∀ a ∈ (Finset.univ : Finset (Fin 4 × Fin q)), 1 ≤ edgeDeg F (GVert.t a) :=
    fun a _ => ((hF.1.2 _).2 (by simp [gadgetT])).pos
  have hs := fc_sum_le q H F hF.1.1
  have heq : ∑ a : Fin 4 × Fin q, (1:ℕ) = ∑ a : Fin 4 × Fin q, edgeDeg F (GVert.t a) := by
    apply le_antisymm (Finset.sum_le_sum h1)
    calc _ ≤ F.card := hs
      _ ≤ 4 * q := hle
      _ = _ := by simp
  intro a
  exact ((Finset.sum_eq_sum_iff_of_le h1).1 heq a (Finset.mem_univ _)).symm

open MetricGenerators.FewComponents in
theorem fc_center (q : ℕ) (H : Finset (Fin q × Fin q × Fin q)) (F : Finset (Sym2 (GVert q H)))
    (hFG : (↑F : Set (Sym2 (GVert q H))) ⊆ (gadget q H).edgeSet)
    (h1 : ∀ a, edgeDeg F (GVert.t a) = 1) (a : Fin 4 × Fin q) :
    ∃ v, s(GVert.t a, v) ∈ F ∧ (gadget q H).Adj (GVert.t a) v ∧
      ∀ w, s(GVert.t a, w) ∈ F → w = v := by
  have h1a := h1 a
  unfold edgeDeg at h1a
  obtain ⟨e, he⟩ := Finset.card_eq_one.1 h1a
  have hmem : e ∈ F.filter (fun e => GVert.t a ∈ e) := by rw [he]; exact Finset.mem_singleton_self e
  rw [Finset.mem_filter] at hmem
  obtain ⟨hmF, hma⟩ := hmem
  obtain ⟨v, rfl⟩ := Sym2.mem_iff_exists.1 hma
  refine ⟨v, hmF, (SimpleGraph.mem_edgeSet _).1 (hFG hmF), ?_⟩
  intro w hw
  have : s(GVert.t a, w) ∈ F.filter (fun e => GVert.t a ∈ e) :=
    Finset.mem_filter.2 ⟨hw, Sym2.mem_mk_left _ _⟩
  rw [he, Finset.mem_singleton] at this
  exact Sym2.congr_right.1 this

open MetricGenerators.FewComponents in
def fc_phi {q : ℕ} {H : Finset (Fin q × Fin q × Fin q)} (c : Fin 4 × Fin q → GVert q H) :
    GVert q H → GVert q H
  | .t a => c a
  | .mid e => .mid e
  | .h m => .h m

open MetricGenerators.FewComponents in
theorem fc_phi_adj (q : ℕ) (H : Finset (Fin q × Fin q × Fin q)) (F : Finset (Sym2 (GVert q H)))
    (hFG : (↑F : Set (Sym2 (GVert q H))) ⊆ (gadget q H).edgeSet)
    (c : Fin 4 × Fin q → GVert q H) (hc : ∀ a w, s(GVert.t a, w) ∈ F → w = c a)
    (u v : GVert q H) (huv : (edgeGraph F).Adj u v) : fc_phi c u = fc_phi c v := by
  rw [edgeGraph, SimpleGraph.fromEdgeSet_adj] at huv
  have hadj : (gadget q H).Adj u v := (SimpleGraph.mem_edgeSet _).1 (hFG huv.1)
  rcases u with a | e | m <;> rcases v with b | e' | m' <;> simp only [fc_phi]
  all_goals first
    | exact (hc _ _ huv.1).symm
    | exact hc _ _ (by rw [Sym2.eq_swap]; exact huv.1)
    | exact absurd hadj (by simp [gadget, gadgetAdj])

open MetricGenerators.FewComponents in
theorem fc_phi_reach (q : ℕ) (H : Finset (Fin q × Fin q × Fin q)) (F : Finset (Sym2 (GVert q H)))
    (hFG : (↑F : Set (Sym2 (GVert q H))) ⊆ (gadget q H).edgeSet)
    (c : Fin 4 × Fin q → GVert q H) (hc : ∀ a w, s(GVert.t a, w) ∈ F → w = c a)
    (u v : GVert q H) (huv : (edgeGraph F).Reachable u v) : fc_phi c u = fc_phi c v := by
  obtain ⟨p⟩ := huv
  induction p with
  | nil => rfl
  | cons hadj _ ih => exact (fc_phi_adj q H F hFG c hc _ _ hadj).trans ih

open MetricGenerators.FewComponents in
theorem fc_phi_c {q : ℕ} {H : Finset (Fin q × Fin q × Fin q)} (c : Fin 4 × Fin q → GVert q H)
    (hcadj : ∀ a, (gadget q H).Adj (GVert.t a) (c a)) (a : Fin 4 × Fin q) :
    fc_phi c (c a) = c a := by
  have := hcadj a
  generalize c a = w at this ⊢
  cases w with
  | t b => exact absurd this (fc_not_adj_tt a b)
  | mid e => rfl
  | h m => rfl

open MetricGenerators.FewComponents in
instance fc_finite (q : ℕ) (H : Finset (Fin q × Fin q × Fin q)) : Finite (GVert q H) := by
  refine Finite.of_injective (fun v : GVert q H => match v with
    | .t a => (Sum.inl a : (Fin 4 × Fin q) ⊕ ({e : Sym2 (Fin 4 × Fin q) // ¬ e.IsDiag} ⊕ ↥H))
    | .mid e => Sum.inr (Sum.inl e)
    | .h m => Sum.inr (Sum.inr m)) ?_
  intro u v huv
  cases u <;> cases v <;> simp_all


def fc_key {q : ℕ} (i : Fin 4) (m : Fin q × Fin q × Fin q) : Fin q :=
  if i = 0 then m.1 else if i = 1 then m.2.1 else if i = 2 then m.2.2 else m.1

def fc_A (q : ℕ) : Finset (Fin 4 × Fin q) := Finset.univ.filter (fun a : Fin 4 × Fin q => a.1 ≠ 3)

theorem fc_A_card (q : ℕ) : (fc_A q).card = 3 * q := by
  have : fc_A q = (Finset.univ.filter (fun i : Fin 4 => i ≠ 3)) ×ˢ (Finset.univ : Finset (Fin q)) := by
    ext a; simp [fc_A]
  have h3 : (Finset.univ.filter (fun i : Fin 4 => i ≠ 3)).card = 3 := by decide
  rw [this, Finset.card_product, h3, Finset.card_univ, Fintype.card_fin]

open MetricGenerators.FewComponents in
theorem fc_hnbr_key {q : ℕ} {m : Fin q × Fin q × Fin q} {i : Fin 4} {j : Fin q}
    (h : HNbr m (i, j)) (hi : i ≠ 3) : j = fc_key i m := by
  rcases h with h | h | h | h
  · simp only [Prod.mk.injEq] at h; rw [h.1, h.2]; simp [fc_key]
  · simp only [Prod.mk.injEq] at h; rw [h.1, h.2]; simp [fc_key]
  · simp only [Prod.mk.injEq] at h; rw [h.1, h.2]; simp [fc_key]
  · exact absurd h hi

open MetricGenerators.FewComponents in
theorem fc_fiber {q : ℕ} {H : Finset (Fin q × Fin q × Fin q)} (c : Fin 4 × Fin q → GVert q H)
    (hcadj : ∀ a, (gadget q H).Adj (GVert.t a) (c a)) (v : GVert q H) :
    ((fc_A q).filter (fun a => c a = v)).card ≤ 3 ∧
    (((fc_A q).filter (fun a => c a = v)).card = 3 →
      ∃ m : H, v = GVert.h m ∧ ∀ i : Fin 4, i ≠ 3 → c (i, fc_key i m.1) = v) := by
  cases v with
  | t b =>
    have : (fc_A q).filter (fun a => c a = GVert.t b) = ∅ := by
      ext a
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro _ hca
      exact fc_not_adj_tt a b (hca ▸ hcadj a)
    rw [this]; simp
  | mid e =>
    rcases e with ⟨e, he⟩
    induction e using Sym2.ind with
    | h x y =>
      have hsub : (fc_A q).filter (fun a => c a = GVert.mid ⟨s(x, y), he⟩) ⊆ {x, y} := by
        intro a ha
        rw [Finset.mem_filter] at ha
        have hadj := hcadj a
        rw [ha.2] at hadj
        have : a ∈ s(x, y) := hadj
        simpa [Sym2.mem_iff] using this
      have := (Finset.card_le_card hsub).trans Finset.card_le_two
      exact ⟨by omega, fun h3 => by omega⟩
  | h m =>
    have hsub : (fc_A q).filter (fun a => c a = GVert.h m) ⊆
        {(0, m.1.1), (1, m.1.2.1), (2, m.1.2.2)} := by
      intro a ha
      rw [Finset.mem_filter] at ha
      have hadj := hcadj a
      rw [ha.2] at hadj
      have : HNbr m.1 a := hadj
      have ha3 : a.1 ≠ 3 := by simpa [fc_A] using ha.1
      rcases this with h | h | h | h
      · simp [h]
      · simp [h]
      · simp [h]
      · exact absurd h ha3
    refine ⟨(Finset.card_le_card hsub).trans Finset.card_le_three, fun h3 => ⟨m, rfl, ?_⟩⟩
    have heq : (fc_A q).filter (fun a => c a = GVert.h m) = {(0, m.1.1), (1, m.1.2.1), (2, m.1.2.2)} :=
      Finset.eq_of_subset_of_card_le hsub (by rw [h3]; exact Finset.card_le_three)
    have hin : ∀ a ∈ ({(0, m.1.1), (1, m.1.2.1), (2, m.1.2.2)} : Finset (Fin 4 × Fin q)),
        c a = GVert.h m := by
      intro a ha
      rw [← heq] at ha
      exact (Finset.mem_filter.1 ha).2
    intro i hi
    fin_cases i
    · exact hin _ (by simp [fc_key])
    · exact hin _ (by simp [fc_key])
    · exact hin _ (by simp [fc_key])
    · exact absurd rfl hi

open MetricGenerators.FewComponents in
theorem fc_forward (q : ℕ) (H : Finset (Fin q × Fin q × Fin q)) (F : Finset (Sym2 (GVert q H)))
    (hF : IsMinTJoin (gadget q H) (gadgetT q H) F) (hk : numComponents F ≤ q) :
    ∃ M ⊆ H, IsMatching q M := by
  classical
  have hFG := hF.1.1
  have h1 := fc_deg_one q H F hF
  choose c hcF hcadj hcu using fc_center q H F hFG h1
  have hc : ∀ a w, s(GVert.t a, w) ∈ F → w = c a := hcu
  have hsupp : ∀ v ∈ (fc_A q).image c, v ∈ edgeSupport F := by
    intro v hv
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hv
    exact ⟨_, hcF a, Sym2.mem_mk_right _ _⟩
  have hCk : ((fc_A q).image c).card ≤ numComponents F := by
    unfold numComponents
    have hinj : Function.Injective (fun v : ↥((fc_A q).image c) =>
        (⟨(edgeGraph F).connectedComponentMk v.1, v.1, hsupp v.1 v.2, rfl⟩ : ↥(components F))) := by
      rintro ⟨v, hv⟩ ⟨w, hw⟩ hvw
      have hvw' : (edgeGraph F).connectedComponentMk v = (edgeGraph F).connectedComponentMk w :=
        congrArg Subtype.val hvw
      have := fc_phi_reach q H F hFG c hc _ _ (SimpleGraph.ConnectedComponent.eq.1 hvw')
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hv
      obtain ⟨b, _, rfl⟩ := Finset.mem_image.1 hw
      rw [fc_phi_c c hcadj, fc_phi_c c hcadj] at this
      exact Subtype.ext this
    have := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_eq_fintype_card (α := ↥((fc_A q).image c)), Fintype.card_coe] at this
    exact this
  have hsum := Finset.card_eq_sum_card_image c (fc_A q)
  have hle3 : ∀ v ∈ (fc_A q).image c, ((fc_A q).filter (fun a => c a = v)).card ≤ 3 :=
    fun v _ => (fc_fiber c hcadj v).1
  have hall : ∀ v ∈ (fc_A q).image c, ((fc_A q).filter (fun a => c a = v)).card = 3 := by
    have h2 : ∑ v ∈ (fc_A q).image c, ((fc_A q).filter (fun a => c a = v)).card =
        ∑ v ∈ (fc_A q).image c, 3 := by
      apply le_antisymm (Finset.sum_le_sum hle3)
      rw [← hsum, fc_A_card, Finset.sum_const, smul_eq_mul]
      omega
    exact (Finset.sum_eq_sum_iff_of_le hle3).1 h2
  have hstruct : ∀ v ∈ (fc_A q).image c,
      ∃ m : H, v = GVert.h m ∧ ∀ i : Fin 4, i ≠ 3 → c (i, fc_key i m.1) = v :=
    fun v hv => (fc_fiber c hcadj v).2 (hall v hv)
  refine ⟨H.filter (fun m => ∃ hm : m ∈ H, GVert.h ⟨m, hm⟩ ∈ (fc_A q).image c),
    Finset.filter_subset _ _, ?_⟩
  have hmatch : ∀ i : Fin 4, i ≠ 3 → ∀ j : Fin q,
      ((H.filter (fun m => ∃ hm : m ∈ H, GVert.h ⟨m, hm⟩ ∈ (fc_A q).image c)).filter
        (fun m => fc_key i m = j)).card = 1 := by
    intro i hi j
    have ha : (i, j) ∈ fc_A q := by simp [fc_A, hi]
    have hcC : c (i, j) ∈ (fc_A q).image c := Finset.mem_image_of_mem c ha
    obtain ⟨m, hm, hmi⟩ := hstruct _ hcC
    have hnb : HNbr m.1 (i, j) := by have := hcadj (i, j); rw [hm] at this; exact this
    have hj : j = fc_key i m.1 := fc_hnbr_key hnb hi
    rw [Finset.card_eq_one]
    refine ⟨m.1, ?_⟩
    ext m'
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨_, hm'H, hm'C⟩, hkey⟩
      obtain ⟨m'', hm'', hm''i⟩ := hstruct _ hm'C
      have h2 := hm''i i hi
      have hm3 : (⟨m', hm'H⟩ : ↥H) = m'' := GVert.h.inj hm''
      subst hm3
      have h3 : c (i, j) = GVert.h ⟨m', hm'H⟩ := by rw [← hkey]; exact h2
      rw [hm] at h3
      exact (congrArg Subtype.val (GVert.h.inj h3)).symm
    · rintro rfl
      exact ⟨⟨m.2, m.2, by rw [← hm]; exact hcC⟩, hj.symm⟩
  refine ⟨fun w => ?_, fun x => ?_, fun y => ?_⟩
  · simpa [fc_key] using hmatch 0 (by decide) w
  · simpa [fc_key] using hmatch 1 (by decide) x
  · simpa [fc_key] using hmatch 2 (by decide) y

open MetricGenerators.FewComponents in
def fc_E1 {q : ℕ} {H : Finset (Fin q × Fin q × Fin q)} (ν : Fin q → ↥H) (p : Fin q × Fin 4) :
    Sym2 (GVert q H) :=
  s(GVert.h (ν p.1), GVert.t (p.2, fc_key p.2 (ν p.1).1))

open MetricGenerators.FewComponents in
theorem fc_E1_inj {q : ℕ} {H : Finset (Fin q × Fin q × Fin q)} (ν : Fin q → ↥H)
    (hν : Function.Injective ν) : Function.Injective (fc_E1 ν) := by
  rintro ⟨w, i⟩ ⟨w', i'⟩ h
  simp [fc_E1] at h
  obtain ⟨h1, h2, _⟩ := h
  rw [hν h1, h2]

open MetricGenerators.FewComponents in
theorem fc_backward_core (q : ℕ) (H : Finset (Fin q × Fin q × Fin q)) (ν : Fin q → ↥H)
    (hν : Function.Injective ν)
    (hk : ∀ i j, (Finset.univ.filter (fun w => fc_key i (ν w).1 = j)).card = 1) :
    ∃ F : Finset (Sym2 (GVert q H)),
      IsMinTJoin (gadget q H) (gadgetT q H) F ∧ numComponents F ≤ q := by
  classical
  have hdeg : ∀ v, edgeDeg ((Finset.univ : Finset (Fin q × Fin 4)).image (fc_E1 ν)) v =
      (Finset.univ.filter (fun p => v ∈ fc_E1 ν p)).card := by
    intro v
    unfold edgeDeg
    rw [Finset.filter_image, Finset.card_image_of_injective _ (fc_E1_inj ν hν)]
  have hTJ : IsTJoin (gadget q H) (gadgetT q H)
      ((Finset.univ : Finset (Fin q × Fin 4)).image (fc_E1 ν)) := by
    refine ⟨?_, ?_⟩
    · intro e he
      simp only [Finset.coe_image, Set.mem_image, Finset.coe_univ, Set.mem_univ,
        true_and] at he
      obtain ⟨⟨w, i⟩, rfl⟩ := he
      rw [fc_E1, SimpleGraph.mem_edgeSet]
      show HNbr (ν w).1 (i, fc_key i (ν w).1)
      fin_cases i <;> simp [HNbr, fc_key]
    · intro v
      rw [hdeg]
      cases v with
      | t a =>
        obtain ⟨i, j⟩ := a
        have : Finset.univ.filter (fun p => GVert.t (i, j) ∈ fc_E1 ν p) =
            (Finset.univ.filter (fun w => fc_key i (ν w).1 = j)) ×ˢ {i} := by
          ext ⟨w, i'⟩
          simp only [fc_E1, Finset.mem_filter, Finset.mem_univ, true_and, Sym2.mem_iff,
            reduceCtorEq, false_or, GVert.t.injEq, Prod.mk.injEq, Finset.mem_product,
            Finset.mem_singleton]
          constructor
          · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
          · rintro ⟨h1, rfl⟩; exact ⟨rfl, h1.symm⟩
        rw [this, Finset.card_product, hk, Finset.card_singleton]
        simp [gadgetT]
      | mid e =>
        have : Finset.univ.filter (fun p => GVert.mid e ∈ fc_E1 ν p) = ∅ := by
          ext p; simp [fc_E1]
        rw [this]; simp [gadgetT]
      | h m =>
        have hT : GVert.h m ∉ gadgetT q H := by simp [gadgetT]
        simp only [hT, iff_false]
        by_cases hw : ∃ w0, ν w0 = m
        · obtain ⟨w0, rfl⟩ := hw
          have : Finset.univ.filter (fun p => GVert.h (ν w0) ∈ fc_E1 ν p) =
              {w0} ×ˢ (Finset.univ : Finset (Fin 4)) := by
            ext ⟨w, i⟩
            simp only [fc_E1, Finset.mem_filter, Finset.mem_univ, true_and, Sym2.mem_iff,
              reduceCtorEq, or_false, GVert.h.injEq, Finset.mem_product, Finset.mem_singleton,
              and_true]
            exact ⟨fun h => (hν h).symm, fun h => h ▸ rfl⟩
          rw [this, Finset.card_product]
          simp
          decide
        · have : Finset.univ.filter (fun p => GVert.h m ∈ fc_E1 ν p) = ∅ := by
            ext ⟨w, i⟩
            simp only [fc_E1, Finset.mem_filter, Finset.mem_univ, true_and, Sym2.mem_iff,
              reduceCtorEq, or_false, GVert.h.injEq, Finset.notMem_empty, iff_false]
            intro h
            exact hw ⟨w, h.symm⟩
          rw [this]; simp
  refine ⟨(Finset.univ : Finset (Fin q × Fin 4)).image (fc_E1 ν), ⟨hTJ, ?_⟩, ?_⟩
  · intro F' hF'
    calc ((Finset.univ : Finset (Fin q × Fin 4)).image (fc_E1 ν)).card ≤ q * 4 :=
          Finset.card_image_le.trans (by simp)
      _ = 4 * q := by ring
      _ ≤ F'.card := fc_card_ge q H F' hF'
  · unfold numComponents
    set F1 := (Finset.univ : Finset (Fin q × Fin 4)).image (fc_E1 ν) with hF1
    have hsupp : ∀ w, GVert.h (ν w) ∈ edgeSupport F1 := fun w =>
      ⟨fc_E1 ν (w, 0), Finset.mem_image_of_mem _ (Finset.mem_univ _), Sym2.mem_mk_left _ _⟩
    have hsurj : Function.Surjective (fun w : Fin q =>
        (⟨(edgeGraph F1).connectedComponentMk (GVert.h (ν w)), _, hsupp w, rfl⟩ :
          ↥(components F1))) := by
      rintro ⟨cc, v, ⟨e, he, hve⟩, rfl⟩
      obtain ⟨⟨w, i⟩, _, rfl⟩ := Finset.mem_image.1 he
      refine ⟨w, ?_⟩
      apply Subtype.ext
      show (edgeGraph F1).connectedComponentMk (GVert.h (ν w)) =
        (edgeGraph F1).connectedComponentMk v
      rw [SimpleGraph.ConnectedComponent.eq]
      rcases Sym2.mem_iff.1 hve with rfl | rfl
      · exact SimpleGraph.Reachable.refl _
      · apply SimpleGraph.Adj.reachable
        rw [edgeGraph, SimpleGraph.fromEdgeSet_adj]
        exact ⟨he, by simp⟩
    have := Nat.card_le_card_of_surjective _ hsurj
    simpa using this

open MetricGenerators.FewComponents in
theorem fc_backward (q : ℕ) (H : Finset (Fin q × Fin q × Fin q))
    (M : Finset (Fin q × Fin q × Fin q)) (hMH : M ⊆ H) (hM : IsMatching q M) :
    ∃ F : Finset (Sym2 (GVert q H)),
      IsMinTJoin (gadget q H) (gadgetT q H) F ∧ numComponents F ≤ q := by
  classical
  choose μ hμ using fun w => Finset.card_eq_one.1 (hM.1 w)
  have hμmem : ∀ w, μ w ∈ M.filter (fun m => m.1 = w) := fun w => by
    rw [hμ w]; exact Finset.mem_singleton_self _
  have hμM : ∀ w, μ w ∈ M := fun w => (Finset.mem_filter.1 (hμmem w)).1
  have hμ1 : ∀ w, (μ w).1 = w := fun w => (Finset.mem_filter.1 (hμmem w)).2
  have h0 : ∀ w w', μ w = μ w' → w = w' := fun w w' h => by rw [← hμ1 w, ← hμ1 w', h]
  have hX : ∀ w w', (μ w).2.1 = (μ w').2.1 → μ w = μ w' := by
    intro w w' h
    obtain ⟨m0, hm0⟩ := Finset.card_eq_one.1 (hM.2.1 (μ w').2.1)
    have h1 : μ w ∈ M.filter (fun m => m.2.1 = (μ w').2.1) := Finset.mem_filter.2 ⟨hμM w, h⟩
    have h2 : μ w' ∈ M.filter (fun m => m.2.1 = (μ w').2.1) := Finset.mem_filter.2 ⟨hμM w', rfl⟩
    rw [hm0, Finset.mem_singleton] at h1 h2
    rw [h1, h2]
  have hY : ∀ w w', (μ w).2.2 = (μ w').2.2 → μ w = μ w' := by
    intro w w' h
    obtain ⟨m0, hm0⟩ := Finset.card_eq_one.1 (hM.2.2 (μ w').2.2)
    have h1 : μ w ∈ M.filter (fun m => m.2.2 = (μ w').2.2) := Finset.mem_filter.2 ⟨hμM w, h⟩
    have h2 : μ w' ∈ M.filter (fun m => m.2.2 = (μ w').2.2) := Finset.mem_filter.2 ⟨hμM w', rfl⟩
    rw [hm0, Finset.mem_singleton] at h1 h2
    rw [h1, h2]
  let ν : Fin q → ↥H := fun w => ⟨μ w, hMH (hμM w)⟩
  have hνinj : Function.Injective ν := fun w w' h => h0 w w' (congrArg Subtype.val h)
  have hkinj : ∀ i : Fin 4, Function.Injective (fun w => fc_key i (ν w).1) := by
    intro i w w' hww
    simp only [ν] at hww
    fin_cases i
    · simpa [fc_key, hμ1] using hww
    · exact h0 _ _ (hX _ _ (by simpa [fc_key] using hww))
    · exact h0 _ _ (hY _ _ (by simpa [fc_key] using hww))
    · simpa [fc_key, hμ1] using hww
  have hk : ∀ i j, (Finset.univ.filter (fun w => fc_key i (ν w).1 = j)).card = 1 := by
    intro i j
    obtain ⟨w0, hw0⟩ := (Finite.injective_iff_surjective.1 (hkinj i)) j
    rw [Finset.card_eq_one]
    refine ⟨w0, ?_⟩
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h => hkinj i (h.trans hw0.symm), fun h => h ▸ hw0⟩
  exact fc_backward_core q H ν hνinj hk

open MetricGenerators.FewComponents in
theorem solution (q : ℕ) (H : Finset (Fin q × Fin q × Fin q)) :
    (∃ F : Finset (Sym2 (GVert q H)),
        IsMinTJoin (gadget q H) (gadgetT q H) F ∧ numComponents F ≤ q) ↔
      ∃ M ⊆ H, IsMatching q M := by
  constructor
  · rintro ⟨F, hF, hk⟩
    exact fc_forward q H F hF hk
  · rintro ⟨M, hMH, hM⟩
    exact fc_backward q H M hMH hM
