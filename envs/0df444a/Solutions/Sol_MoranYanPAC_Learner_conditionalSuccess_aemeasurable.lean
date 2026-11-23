-- Prove2me | solution 1 for MoranYanPAC.Learner.conditionalSuccess_aemeasurable
-- status  : ACCEPTED   (disprove)
-- author  : @Shuze Chen
-- created : 2026-11-23T05:19:16.341017+00:00
-- url     : https://prove2.me/submissions/ebd21bdd-5f70-4645-a07a-f5942638c3f6

import Mathlib
import Definitions.Def_UnderstandingML_Online
import Definitions.Def_MoranYanPAC_Main_Candidates
import Definitions.Def_MoranYanPAC_Main_PACExperiment
import Definitions.Def_MoranYanPAC_Learner


-- ===== part A =====

set_option autoImplicit false

open MeasureTheory Set

namespace ChildDisproof

/-- the rational subgroup of ℝ -/
noncomputable def QSub : AddSubgroup ℝ := (Rat.castHom ℝ).toAddMonoidHom.range

lemma mem_QSub {x : ℝ} : x ∈ QSub ↔ ∃ q : ℚ, (q : ℝ) = x := by
  simp [QSub]

noncomputable def rep (c : ℝ ⧸ QSub) : ℝ := c.out - ⌊c.out⌋

lemma rep_mem (c : ℝ ⧸ QSub) : rep c ∈ Ico (0 : ℝ) 1 := by
  unfold rep
  constructor
  · linarith [Int.floor_le c.out]
  · linarith [Int.lt_floor_add_one c.out]

lemma mk_rep (c : ℝ ⧸ QSub) : (QuotientAddGroup.mk (rep c) : ℝ ⧸ QSub) = c := by
  conv_rhs => rw [← Quotient.out_eq' c]
  rw [QuotientAddGroup.eq]
  unfold rep
  rw [mem_QSub]
  refine ⟨((⌊c.out⌋ : ℤ) : ℚ), ?_⟩
  push_cast
  show _ = -(Quotient.out c - ⌊Quotient.out c⌋) + Quotient.out c
  ring

/-- The Vitali set. -/
noncomputable def vitali : Set ℝ := range rep

lemma vitali_sub : vitali ⊆ Icc 0 1 := by
  rintro _ ⟨c, rfl⟩
  exact Ico_subset_Icc_self (rep_mem c)

lemma vitali_eq_of_sub {a b : ℝ} (ha : a ∈ vitali) (hb : b ∈ vitali) (hq : a - b ∈ QSub) :
    a = b := by
  obtain ⟨c, rfl⟩ := ha
  obtain ⟨c', rfl⟩ := hb
  have : c' = c := by
    rw [← mk_rep c, ← mk_rep c', QuotientAddGroup.eq]
    have : -rep c' + rep c = rep c - rep c' := by ring
    rw [this]; exact hq
  rw [this]

/-- translates indexed by rationals in [-1,1] -/
def QI : Type := {q : ℚ // -1 ≤ q ∧ q ≤ 1}

instance : Countable QI := by unfold QI; infer_instance

instance : Infinite QI := by
  refine Infinite.of_injective (fun n : ℕ => (⟨1 / ((n : ℚ) + 1), ?_, ?_⟩ : QI)) ?_
  · have : (0 : ℚ) ≤ 1 / ((n : ℚ) + 1) := by positivity
    linarith
  · rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℚ) ≤ n)]
  · intro a b h
    have h2 : (1 : ℚ) / ((a : ℚ) + 1) = 1 / ((b : ℚ) + 1) := congrArg (fun x : QI => x.1) h
    have h' : ((a : ℚ) + 1) = (b : ℚ) + 1 := by
      have ha : (0 : ℚ) < (a : ℚ) + 1 := by positivity
      have hb : (0 : ℚ) < (b : ℚ) + 1 := by positivity
      rw [div_eq_div_iff ha.ne' hb.ne'] at h2
      linarith
    exact_mod_cast (by linarith : (a : ℚ) = b)

noncomputable def trans (q : QI) : Set ℝ := (fun x => x + -((q.1 : ℚ) : ℝ)) ⁻¹' vitali

lemma trans_disjoint : Pairwise (Function.onFun Disjoint trans) := by
  intro q q' hne
  rw [Function.onFun, Set.disjoint_left]
  intro x hx hx'
  simp only [trans, mem_preimage] at hx hx'
  have := vitali_eq_of_sub hx hx' (by
    rw [mem_QSub]
    exact ⟨(q'.1 : ℚ) - q.1, by push_cast; ring⟩)
  apply hne
  apply Subtype.ext
  have : ((q.1 : ℚ) : ℝ) = ((q'.1 : ℚ) : ℝ) := by linarith
  exact_mod_cast this

lemma Icc_sub_union : Icc (0 : ℝ) 1 ⊆ ⋃ q, trans q := by
  intro x hx
  set c : ℝ ⧸ QSub := QuotientAddGroup.mk x
  have hr := rep_mem c
  have hq : x - rep c ∈ QSub := by
    have h1 : (QuotientAddGroup.mk (rep c) : ℝ ⧸ QSub) = QuotientAddGroup.mk x := mk_rep c
    rw [QuotientAddGroup.eq] at h1
    have : x - rep c = -rep c + x := by ring
    rw [this]; exact h1
  obtain ⟨q, hq⟩ := mem_QSub.mp hq
  have hq1 : (-1 : ℝ) ≤ (q : ℝ) := by rw [hq]; linarith [hx.1, hr.2]
  have hq2 : (q : ℝ) ≤ 1 := by rw [hq]; linarith [hx.2, hr.1]
  refine mem_iUnion.mpr ⟨⟨q, by exact_mod_cast hq1, by exact_mod_cast hq2⟩, ?_⟩
  simp only [trans, mem_preimage]
  have : x + -(q : ℝ) = rep c := by rw [hq]; ring
  rw [this]; exact ⟨c, rfl⟩

lemma union_sub_Icc : (⋃ q, trans q) ⊆ Icc (-1 : ℝ) 2 := by
  intro x hx
  obtain ⟨q, hx⟩ := mem_iUnion.mp hx
  simp only [trans, mem_preimage] at hx
  have h := vitali_sub hx
  have h1 : (-1 : ℝ) ≤ ((q.1 : ℚ) : ℝ) := by exact_mod_cast q.2.1
  have h2 : ((q.1 : ℚ) : ℝ) ≤ 1 := by exact_mod_cast q.2.2
  constructor <;> linarith [h.1, h.2]

theorem vitali_not_nullMeasurable : ¬ NullMeasurableSet vitali volume := by
  intro hN
  have hmeas : ∀ q, NullMeasurableSet (trans q) volume := fun q =>
    hN.preimage (measurePreserving_add_right volume _).quasiMeasurePreserving
  have hval : ∀ q, volume (trans q) = volume vitali := fun q =>
    measure_preimage_add_right volume _ vitali
  have hU : volume (⋃ q, trans q) = ∑' _q : QI, volume vitali := by
    rw [measure_iUnion₀ (trans_disjoint.mono fun _ _ h => h.aedisjoint) hmeas]
    simp [hval]
  by_cases h0 : volume vitali = 0
  · have : volume (Icc (0 : ℝ) 1) ≤ 0 := by
      calc volume (Icc (0 : ℝ) 1) ≤ volume (⋃ q, trans q) := measure_mono Icc_sub_union
        _ = 0 := by rw [hU, h0]; simp
    simp at this
  · have : (⊤ : ENNReal) ≤ volume (Icc (-1 : ℝ) 2) := by
      calc (⊤ : ENNReal) = ∑' _q : QI, volume vitali := (ENNReal.tsum_const_eq_top_of_ne_zero h0).symm
        _ = volume (⋃ q, trans q) := hU.symm
        _ ≤ _ := measure_mono union_sub_Icc
    simp at this

theorem vitali_not_nullMeasurable_restrict :
    ¬ NullMeasurableSet vitali (volume.restrict (Icc (0 : ℝ) 1)) := by
  intro h
  apply vitali_not_nullMeasurable
  have h2 : NullMeasurableSet (vitali ∩ Icc 0 1) volume :=
    (nullMeasurableSet_restrict measurableSet_Icc.nullMeasurableSet).mp h
  rwa [inter_eq_left.mpr vitali_sub] at h2

theorem vitali_two : ∀ a : ℝ, ∃ s ∈ vitali, s ≠ a := by
  intro a
  by_contra h
  push Not at h
  apply vitali_not_nullMeasurable
  have : vitali ⊆ {a} := fun s hs => h s hs
  exact (Set.Subsingleton.anti (subsingleton_singleton) this).measurableSet.nullMeasurableSet

end ChildDisproof

-- ===== part B =====

set_option autoImplicit false

open Set UnderstandingML

namespace ChildDisproof

section Ldim
variable {X : Type*}

lemma shatters_mono {G : Set (X → Bool)} {m : ℕ} {v : List Bool → X} (h : ShattersTree G m v)
    {k : ℕ} (hk : k ≤ m) : ShattersTree G k v := by
  intro y
  obtain ⟨g, hg, hy⟩ := h (fun t => if ht : (t : ℕ) < k then y ⟨t, ht⟩ else false)
  refine ⟨g, hg, fun t => ?_⟩
  have := hy ⟨t, lt_of_lt_of_le t.2 hk⟩
  simp only [t.2, dite_true] at this
  convert this using 3
  apply List.ofFn_inj.mpr
  funext j
  simp [lt_trans j.2 t.2]

lemma prefix_eq {k : ℕ} {y y' : Fin k → Bool} (t : Fin k) (h : ∀ j : Fin k, j < t → y j = y' j) :
    List.ofFn (fun j : Fin (t : ℕ) => y ⟨j, lt_trans j.2 t.2⟩) =
      List.ofFn (fun j : Fin (t : ℕ) => y' ⟨j, lt_trans j.2 t.2⟩) := by
  apply List.ofFn_inj.mpr
  funext j
  exact h _ j.2

lemma card_le_of_shatters {G : Set (X → Bool)} {k : ℕ} {v : List Bool → X}
    (h : ShattersTree G k v) (F : Finset (X → Bool)) (hF : G ⊆ ↑F) : 2 ^ k ≤ F.card := by
  classical
  choose g hg hy using h
  have hinj : Function.Injective g := by
    intro y y' hyy
    by_contra hne
    have hex : ∃ t : Fin k, y t ≠ y' t := by
      by_contra hc; push Not at hc; exact hne (funext hc)
    have hne' : (Finset.univ.filter fun t : Fin k => y t ≠ y' t).Nonempty := by
      obtain ⟨s, hs⟩ := hex; exact ⟨s, by simp [hs]⟩
    let t := Finset.min' _ hne'
    have htmem : y t ≠ y' t := by
      have := Finset.min'_mem _ hne'
      simpa using this
    have hbefore : ∀ j : Fin k, j < t → y j = y' j := by
      intro j hj
      by_contra hc
      have : t ≤ j := Finset.min'_le _ j (by simp [hc])
      exact absurd hj (not_lt.mpr this)
    have h1 := hy y t
    have h2 := hy y' t
    rw [prefix_eq t hbefore, hyy] at h1
    exact htmem (h1.symm.trans h2)
  have : (Finset.univ : Finset (Fin k → Bool)).card ≤ F.card :=
    Finset.card_le_card_of_injOn g (fun y _ => hF (hg y)) (fun a _ b _ hab => hinj hab)
  simpa using this

lemma ldim_le_of_no_tree {G : Set (X → Bool)} {k : ℕ} (h : ∀ v, ¬ ShattersTree G (k + 1) v) :
    ldim G ≤ k := by
  unfold ldim
  refine iSup₂_le fun d ⟨v, hv⟩ => ?_
  by_contra hlt
  push Not at hlt
  have hlt' : k < d := by exact_mod_cast hlt
  have : k + 1 ≤ d := hlt'
  exact h v (shatters_mono hv this)

lemma le_ldim_of_tree {G : Set (X → Bool)} {k : ℕ} {v : List Bool → X}
    (h : ShattersTree G k v) : (k : ℕ∞) ≤ ldim G :=
  le_iSup₂ (f := fun (d : ℕ) (_ : ∃ v : List Bool → X, ShattersTree G d v) => (d : ℕ∞)) k ⟨v, h⟩

lemma ldim_eq_zero_of_subsingleton {G : Set (X → Bool)} (h : G.Subsingleton) : ldim G = 0 := by
  classical
  apply le_antisymm _ bot_le
  refine ldim_le_of_no_tree fun v hv => ?_
  rcases G.eq_empty_or_nonempty with hG | ⟨g, hg⟩
  · obtain ⟨g, hg, _⟩ := hv (fun _ => false)
    rw [hG] at hg; exact hg
  · have := card_le_of_shatters hv {g} (fun x hx => by simp [h hx hg])
    simp at this

lemma tree1 {G : Set (X → Bool)} (x : X) (h0 : ∃ g ∈ G, g x = false) (h1 : ∃ g ∈ G, g x = true) :
    ShattersTree G 1 (fun _ => x) := by
  intro y
  cases hy : y 0
  · obtain ⟨g, hg, hgx⟩ := h0
    exact ⟨g, hg, fun t => by rw [Fin.fin_one_eq_zero t, hy]; exact hgx⟩
  · obtain ⟨g, hg, hgx⟩ := h1
    exact ⟨g, hg, fun t => by rw [Fin.fin_one_eq_zero t, hy]; exact hgx⟩

lemma one_le_ldim {G : Set (X → Bool)} (x : X) (h0 : ∃ g ∈ G, g x = false)
    (h1 : ∃ g ∈ G, g x = true) : (1 : ℕ∞) ≤ ldim G := by
  exact_mod_cast le_ldim_of_tree (tree1 x h0 h1)

lemma tree2 {G : Set (X → Bool)} (r x0 x1 : X)
    (h : ∀ a b : Bool, ∃ g ∈ G, g r = a ∧ g (if a then x1 else x0) = b) :
    ShattersTree G 2 (fun l => if l = [] then r else if l = [true] then x1 else x0) := by
  intro y
  obtain ⟨g, hg, h1, h2⟩ := h (y 0) (y 1)
  refine ⟨g, hg, fun t => ?_⟩
  fin_cases t
  · simpa using h1
  · cases hy : y 0 <;> simp_all

lemma two_le_ldim {G : Set (X → Bool)} (r x0 x1 : X)
    (h : ∀ a b : Bool, ∃ g ∈ G, g r = a ∧ g (if a then x1 else x0) = b) : (2 : ℕ∞) ≤ ldim G := by
  exact_mod_cast le_ldim_of_tree (tree2 r x0 x1 h)

lemma subtree {G : Set (X → Bool)} {k : ℕ} {v : List Bool → X} (h : ShattersTree G (k + 1) v)
    (b : Bool) : ShattersTree {g ∈ G | g (v []) = b} k (fun l => v (b :: l)) := by
  intro y
  obtain ⟨g, hg, hy⟩ := h (Fin.cons b y)
  refine ⟨g, ⟨hg, by simpa using hy 0⟩, fun t => ?_⟩
  have := hy t.succ
  simp only [Fin.cons_succ] at this
  convert this using 2
  simp only [Fin.val_succ, List.ofFn_succ]
  congr 1

end Ldim

end ChildDisproof

-- ===== part C =====

set_option autoImplicit false

open Set UnderstandingML PrivLittlestone MoranYanPAC.Main

namespace ChildDisproof

def Pt : Type := {p : ℝ × Bool // p.2 = false ∨ p.1 ∈ vitali}

instance : MeasurableSpace Pt := Subtype.instMeasurableSpace

def base (t : ℝ) : Pt := ⟨(t, false), Or.inl rfl⟩
def partner (t : ℝ) (ht : t ∈ vitali) : Pt := ⟨(t, true), Or.inr ht⟩

noncomputable def fb (t : ℝ) : Pt → Bool := fun z => decide (z.1.1 = t ∧ z.1.2 = false)
noncomputable def fp (t : ℝ) : Pt → Bool := fun z => decide (z.1.1 = t)
def c0 : Pt → Bool := fun _ => false
def c1 : Pt → Bool := fun _ => true

def Hc : Set (Pt → Bool) := {c0, c1} ∪ range fb ∪ range fp

noncomputable instance : DecidableEq Pt := Classical.decEq _
noncomputable instance decEqFun : DecidableEq (Pt → Bool) := Classical.decEq _

@[simp] lemma base_fst (t : ℝ) : (base t).1.1 = t := rfl
@[simp] lemma partner_fst (t : ℝ) (h : t ∈ vitali) : (partner t h).1.1 = t := rfl
@[simp] lemma fb_base (t s : ℝ) : fb t (base s) = decide (s = t) := by
  unfold fb base; rw [decide_eq_decide]; simp
@[simp] lemma fp_base (t s : ℝ) : fp t (base s) = decide (s = t) := by
  unfold fp base; rw [decide_eq_decide]
@[simp] lemma fb_partner (t s : ℝ) (hs : s ∈ vitali) : fb t (partner s hs) = false := by
  unfold fb partner; simp
@[simp] lemma fp_partner (t s : ℝ) (hs : s ∈ vitali) : fp t (partner s hs) = decide (s = t) := by
  unfold fp partner; rw [decide_eq_decide]
@[simp] lemma c0_apply (z : Pt) : c0 z = false := rfl
@[simp] lemma c1_apply (z : Pt) : c1 z = true := rfl
@[simp] lemma base_ne_partner (t s : ℝ) (h : s ∈ vitali) : base t ≠ partner s h := by
  intro e; have := congrArg (fun z : Pt => z.1.2) e; simp [base, partner] at this
@[simp] lemma base_inj (t s : ℝ) : base t = base s ↔ t = s := by
  constructor
  · intro e; exact congrArg (fun z : Pt => z.1.1) e
  · rintro rfl; rfl

lemma pt_cases (z : Pt) : (∃ t, z = base t) ∨ ∃ t, ∃ h : t ∈ vitali, z = partner t h := by
  obtain ⟨⟨t, b⟩, hz⟩ := z
  cases b
  · left; exact ⟨t, rfl⟩
  · right
    have : t ∈ vitali := by simpa using hz
    exact ⟨t, this, rfl⟩

lemma fp_eq_fb {t : ℝ} (ht : t ∉ vitali) : fp t = fb t := by
  funext z
  rcases pt_cases z with ⟨s, rfl⟩ | ⟨s, hv, rfl⟩
  · simp
  · simp only [fp_partner, fb_partner, decide_eq_false_iff_not]
    intro hst; exact ht (hst ▸ hv)

lemma mem_Hc {g : Pt → Bool} : g ∈ Hc ↔ g = c0 ∨ g = c1 ∨ (∃ t, g = fb t) ∨ (∃ t, g = fp t) := by
  simp only [Hc, mem_union, mem_insert_iff, mem_singleton_iff, mem_range]
  constructor
  · rintro (((h | h) | ⟨t, rfl⟩) | ⟨t, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl ⟨t, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨t, rfl⟩))
  · rintro (h | h | ⟨t, rfl⟩ | ⟨t, rfl⟩)
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr ⟨t, rfl⟩)
    · exact Or.inr ⟨t, rfl⟩

lemma c0_mem : c0 ∈ Hc := mem_Hc.mpr (Or.inl rfl)
lemma c1_mem : c1 ∈ Hc := mem_Hc.mpr (Or.inr (Or.inl rfl))
lemma fb_mem (t : ℝ) : fb t ∈ Hc := mem_Hc.mpr (Or.inr (Or.inr (Or.inl ⟨t, rfl⟩)))
lemma fp_mem (t : ℝ) : fp t ∈ Hc := mem_Hc.mpr (Or.inr (Or.inr (Or.inr ⟨t, rfl⟩)))

lemma exists_fresh (S : Finset ℝ) : ∃ r : ℝ, r ∉ S := Infinite.exists_notMem_finset S

/-! ### The local universe equals `Hc` -/

lemma agree {u : Pt → Bool} (hu : u ∈ localUniverse Hc 2) (A : Finset Pt) (hA : A.card ≤ 3) :
    ∃ g ∈ Hc, ∀ x ∈ A, g x = u x := by
  obtain ⟨g, hg, h⟩ := hu A hA
  exact ⟨g, hg, h⟩

lemma card3 (a b c : Pt) : ({a, b, c} : Finset Pt).card ≤ 3 := Finset.card_le_three

lemma localUniverse_eq : localUniverse Hc 2 = Hc := by
  ext u
  constructor
  swap
  · intro hu A _
    exact ⟨u, hu, fun _ _ => rfl⟩
  intro hu
  by_cases hb : ∃ s, u (base s) = true
  · obtain ⟨s, hs⟩ := hb
    by_cases hb2 : ∃ s', s' ≠ s ∧ u (base s') = true
    · obtain ⟨s', hss, hs'⟩ := hb2
      have : u = c1 := by
        funext z
        obtain ⟨g, hg, hga⟩ := agree hu {base s, base s', z} (card3 _ _ _)
        have h1 := hga (base s) (by simp)
        have h2 := hga (base s') (by simp)
        have h3 := hga z (by simp)
        rw [hs] at h1; rw [hs'] at h2
        rcases mem_Hc.mp hg with rfl | rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩
        · simp at h1
        · simpa using h3.symm
        · simp at h1 h2; exact absurd (h2.trans h1.symm) hss
        · simp at h1 h2; exact absurd (h2.trans h1.symm) hss
      rw [this]; exact c1_mem
    · push Not at hb2
      have hbase : ∀ s', s' ≠ s → u (base s') = false := by
        intro s' hs'
        cases hu' : u (base s')
        · rfl
        · exact absurd (hb2 _ hs' hu') (by simp)
      have hoffp : ∀ t (ht : t ∈ vitali), t ≠ s → u (partner t ht) = false := by
        intro t ht hts
        obtain ⟨r, hr⟩ := exists_fresh {s, t}
        have hrs : r ≠ s := fun h => hr (by simp [h])
        have hrt : r ≠ t := fun h => hr (by simp [h])
        have hur := hbase r hrs
        by_contra hz'
        have hzt : u (partner t ht) = true := by simpa using hz'
        obtain ⟨g, hg, hga⟩ := agree hu {partner t ht, base s, base r} (card3 _ _ _)
        have h1 := hga (partner t ht) (by simp)
        have h2 := hga (base s) (by simp)
        have h3 := hga (base r) (by simp)
        rw [hzt] at h1; rw [hs] at h2; rw [hur] at h3
        rcases mem_Hc.mp hg with rfl | rfl | ⟨t', rfl⟩ | ⟨t', rfl⟩
        · simp at h1
        · simp at h3
        · simp at h1
        · simp at h1 h2; exact hts (h1.trans h2.symm)
      by_cases hp : ∃ hv : s ∈ vitali, u (partner s hv) = true
      · obtain ⟨hv, hpu⟩ := hp
        have : u = fp s := by
          funext z
          rcases pt_cases z with ⟨t, rfl⟩ | ⟨t, ht, rfl⟩
          · by_cases hts : t = s
            · subst hts; simp [hs]
            · rw [hbase t hts]; simp [hts]
          · by_cases hts : t = s
            · subst hts; simp [hpu]
            · rw [hoffp t ht hts]; simp [hts]
        rw [this]; exact fp_mem s
      · push Not at hp
        have : u = fb s := by
          funext z
          rcases pt_cases z with ⟨t, rfl⟩ | ⟨t, ht, rfl⟩
          · by_cases hts : t = s
            · subst hts; simp [hs]
            · rw [hbase t hts]; simp [hts]
          · by_cases hts : t = s
            · subst hts; simpa using hp ht
            · rw [hoffp t ht hts]; simp
        rw [this]; exact fb_mem s
  · push Not at hb
    have : u = c0 := by
      funext z
      rcases pt_cases z with ⟨t, rfl⟩ | ⟨t, ht, rfl⟩
      · simpa using hb t
      · by_contra hz'
        have hzt : u (partner t ht) = true := by simpa using hz'
        obtain ⟨g, hg, hga⟩ := agree hu {partner t ht, base t, base t} (card3 _ _ _)
        have h1 := hga (partner t ht) (by simp)
        have h2 := hga (base t) (by simp)
        rw [hzt] at h1
        have hb' : u (base t) = false := by simpa using hb t
        rw [hb'] at h2
        rcases mem_Hc.mp hg with rfl | rfl | ⟨t', rfl⟩ | ⟨t', rfl⟩
        · simp at h1
        · simp at h2
        · simp at h1
        · simp at h1 h2; exact h2 h1
    rw [this]; exact c0_mem

/-! ### Littlestone dimension of `Hc` -/

lemma true_side_sub (z : Pt) : {g ∈ Hc | g z = true} ⊆ ↑({c1, fb z.1.1, fp z.1.1} : Finset (Pt → Bool)) := by
  rintro g ⟨hg, hgz⟩
  rcases mem_Hc.mp hg with rfl | rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩
  · simp at hgz
  · simp
  · have : z.1.1 = t := by unfold fb at hgz; simp at hgz; exact hgz.1
    simp [this]
  · have : z.1.1 = t := by unfold fp at hgz; simpa using hgz
    simp [this]

lemma ldim_true_side_le (z : Pt) : ldim {g ∈ Hc | g z = true} ≤ 1 := by
  refine ldim_le_of_no_tree fun v hv => ?_
  have := card_le_of_shatters hv _ (true_side_sub z)
  have h3 := Finset.card_le_three (a := c1) (b := fb z.1.1) (c := fp z.1.1)
  norm_num at this
  omega

lemma ldim_Hc : ldim Hc = 2 := by
  apply le_antisymm
  · refine ldim_le_of_no_tree fun v hv => ?_
    have h := subtree hv true
    have := card_le_of_shatters h _ (true_side_sub (v []))
    have h3 := Finset.card_le_three (a := c1) (b := fb (v []).1.1) (c := fp (v []).1.1)
    norm_num at this
    omega
  · refine two_le_ldim (base 0) (base 1) (base 2) fun a b => ?_
    cases a <;> cases b
    · exact ⟨c0, c0_mem, rfl, rfl⟩
    · exact ⟨fb 1, fb_mem 1, by simp, by simp⟩
    · exact ⟨fb 0, fb_mem 0, by simp, by norm_num⟩
    · exact ⟨c1, c1_mem, rfl, rfl⟩

end ChildDisproof

-- ===== part D =====

set_option autoImplicit false

open Set UnderstandingML PrivLittlestone MoranYanPAC.Main

namespace ChildDisproof

lemma fresh_finset (A : Finset Pt) (S : Finset ℝ) : ∃ r : ℝ, r ∉ S ∧ ∀ x ∈ A, x.1.1 ≠ r := by
  obtain ⟨r, hr⟩ := exists_fresh (S ∪ A.image (fun x : Pt => x.1.1))
  refine ⟨r, fun h => hr (Finset.mem_union_left _ h), fun x hx he => hr ?_⟩
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, hx, he⟩)

lemma fb_off {r : ℝ} {x : Pt} (h : x.1.1 ≠ r) : fb r x = false := by
  unfold fb; simp [h]
lemma fp_off {r : ℝ} {x : Pt} (h : x.1.1 ≠ r) : fp r x = false := by
  unfold fp; simp [h]

lemma c0_layer1 : c0 ∈ rankLayer Hc 2 1 := by
  refine ⟨by simp only [rankLayer, localUniverse_eq]; exact c0_mem, fun A _ => ?_⟩
  obtain ⟨r, -, hr⟩ := fresh_finset A ∅
  refine one_le_ldim (base r) ⟨c0, ⟨c0_mem, fun _ _ => rfl⟩, rfl⟩
    ⟨fb r, ⟨fb_mem r, fun x hx => fb_off (hr x hx)⟩, by simp⟩

lemma exists_vitali_off (A : Finset Pt) (hA : A.card ≤ 1) : ∃ s ∈ vitali, ∀ x ∈ A, x.1.1 ≠ s := by
  rcases A.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · obtain ⟨s, hs, -⟩ := vitali_two 0
    exact ⟨s, hs, by simp⟩
  · obtain ⟨s, hs, hsa⟩ := vitali_two a.1.1
    refine ⟨s, hs, fun x hx he => hsa ?_⟩
    rw [Finset.card_le_one.mp hA x hx a ha] at he
    exact he.symm

lemma c0_layer2 : c0 ∈ rankLayer Hc 2 2 := by
  refine ⟨c0_layer1, fun A hA => ?_⟩
  obtain ⟨s, hs, hsA⟩ := exists_vitali_off A (by simpa using hA)
  obtain ⟨r, hr, hrA⟩ := fresh_finset A {s}
  have hrs : r ≠ s := fun h => hr (by simp [h])
  refine two_le_ldim (base s) (base r) (partner s hs) fun a b => ?_
  cases a <;> cases b
  · exact ⟨c0, ⟨c0_mem, fun _ _ => rfl⟩, rfl, rfl⟩
  · exact ⟨fb r, ⟨fb_mem r, fun x hx => fb_off (hrA x hx)⟩, by simp [Ne.symm hrs], by simp⟩
  · exact ⟨fb s, ⟨fb_mem s, fun x hx => fb_off (hsA x hx)⟩, by simp, by simp⟩
  · exact ⟨fp s, ⟨fp_mem s, fun x hx => fp_off (hsA x hx)⟩, by simp, by simp⟩

/-- every member other than `c0` is pinned by at most two points -/
lemma pinned (h : Pt → Bool) (hh : h ∈ Hc) (h0 : h ≠ c0) :
    ∃ A : Finset Pt, A.card ≤ 2 ∧ ∀ f ∈ restrictCls Hc h A, f = h := by
  rcases mem_Hc.mp hh with rfl | rfl | ⟨s, rfl⟩ | ⟨s, rfl⟩
  · exact absurd rfl h0
  · refine ⟨{base 0, base 1}, Finset.card_le_two, fun f ⟨hf, hfA⟩ => ?_⟩
    have h1 := hfA (base 0) (by simp)
    have h2 := hfA (base 1) (by simp)
    rcases mem_Hc.mp hf with rfl | rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩
    · simp at h1
    · rfl
    · simp at h1 h2; norm_num [← h1] at h2
    · simp at h1 h2; norm_num [← h1] at h2
  · by_cases hs : s ∈ vitali
    · refine ⟨{base s, partner s hs}, Finset.card_le_two, fun f ⟨hf, hfA⟩ => ?_⟩
      have h1 := hfA (base s) (by simp)
      have h2 := hfA (partner s hs) (by simp)
      rcases mem_Hc.mp hf with rfl | rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩
      · simp at h1
      · simp at h2
      · simp at h1; rw [h1]
      · simp at h1 h2; exact absurd h1 h2
    · refine ⟨{base s, base (s + 1)}, Finset.card_le_two, fun f ⟨hf, hfA⟩ => ?_⟩
      have h1 := hfA (base s) (by simp)
      have h2 := hfA (base (s + 1)) (by simp)
      rcases mem_Hc.mp hf with rfl | rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩
      · simp at h1
      · simp at h2
      · simp at h1; rw [h1]
      · simp at h1; subst h1; exact fp_eq_fb hs
  · by_cases hs : s ∈ vitali
    · refine ⟨{partner s hs, base (s + 1)}, Finset.card_le_two, fun f ⟨hf, hfA⟩ => ?_⟩
      have h1 := hfA (partner s hs) (by simp)
      have h2 := hfA (base (s + 1)) (by simp)
      rcases mem_Hc.mp hf with rfl | rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩
      · simp at h1
      · simp at h2
      · simp at h1
      · simp at h1; rw [h1]
    · rw [fp_eq_fb hs] at h0 ⊢
      refine ⟨{base s, base (s + 1)}, Finset.card_le_two, fun f ⟨hf, hfA⟩ => ?_⟩
      have h1 := hfA (base s) (by simp)
      have h2 := hfA (base (s + 1)) (by simp)
      rcases mem_Hc.mp hf with rfl | rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩
      · simp at h1
      · simp at h2
      · simp at h1; rw [h1]
      · simp at h1; subst h1; exact fp_eq_fb hs

lemma restrict_eq_singleton {h : Pt → Bool} (hh : h ∈ Hc) {A : Finset Pt}
    (hA : ∀ f ∈ restrictCls Hc h A, f = h) : restrictCls Hc h A = {h} := by
  ext f
  constructor
  · intro hf; exact hA f hf
  · rintro rfl; exact ⟨hh, fun _ _ => rfl⟩

lemma not_layer1 (h : Pt → Bool) (hh : h ∈ Hc) (h0 : h ≠ c0) : h ∉ rankLayer Hc 2 1 := by
  rintro ⟨-, hl⟩
  obtain ⟨A, hA, hpin⟩ := pinned h hh h0
  have := hl A (by simpa using hA)
  rw [restrict_eq_singleton hh hpin, ldim_eq_zero_of_subsingleton subsingleton_singleton] at this
  simp at this

lemma layer_mono (s : ℕ) : rankLayer Hc 2 (s + 1) ⊆ rankLayer Hc 2 s := fun _ h => h.1

lemma layer_sub_Hc (s : ℕ) : rankLayer Hc 2 s ⊆ Hc := by
  induction s with
  | zero => intro h hh; simpa [rankLayer, localUniverse_eq] using hh
  | succ s ih => exact (layer_mono s).trans ih

lemma rankOf_c0 : rankOf Hc 2 c0 = 2 := by
  classical
  unfold rankOf
  rw [Nat.findGreatest_eq_iff]
  refine ⟨le_rfl, fun _ => c0_layer2, fun k hk hk2 => by omega⟩

lemma rankOf_other (h : Pt → Bool) (hh : h ∈ Hc) (h0 : h ≠ c0) : rankOf Hc 2 h = 0 := by
  classical
  unfold rankOf
  rw [Nat.findGreatest_eq_zero_iff]
  intro k hk hk2
  have h1 := not_layer1 h hh h0
  interval_cases k
  · exact h1
  · exact fun h2 => h1 (layer_mono 1 h2)

lemma layer2_eq : rankLayer Hc 2 2 = {c0} := by
  ext h
  constructor
  · intro hh
    by_contra hne
    exact not_layer1 h (layer_sub_Hc 2 hh) hne (layer_mono 1 hh)
  · rintro rfl; exact c0_layer2

/-! ### The witness assignment -/

open Classical in
noncomputable def Aw (h : Pt → Bool) : Finset Pt :=
  if hx : h ≠ c0 ∧ ∃ A : Finset Pt, A.card ≤ 2 ∧ ∀ f ∈ restrictCls Hc h A, f = h then hx.2.choose
  else ∅

lemma Aw_c0 : Aw c0 = ∅ := by unfold Aw; simp

lemma Aw_spec (h : Pt → Bool) (hh : h ∈ Hc) (h0 : h ≠ c0) :
    (Aw h).card ≤ 2 ∧ ∀ f ∈ restrictCls Hc h (Aw h), f = h := by
  have hx : h ≠ c0 ∧ ∃ A : Finset Pt, A.card ≤ 2 ∧ ∀ f ∈ restrictCls Hc h A, f = h :=
    ⟨h0, pinned h hh h0⟩
  unfold Aw
  rw [dif_pos hx]
  exact hx.2.choose_spec

lemma restrict_empty (h : Pt → Bool) : restrictCls Hc h ∅ = Hc := by
  ext f; simp [restrictCls]

lemma witnessSpace_c0 : witnessSpace Hc 2 Aw c0 = Hc := by
  ext f; simp [witnessSpace, Aw_c0, localUniverse_eq]

lemma soa_singleton (h : Pt → Bool) : SOA ({h} : Set (Pt → Bool)) = h := by
  funext x
  unfold SOA ldimBot
  cases hx : h x
  · have e1 : {g ∈ ({h} : Set (Pt → Bool)) | g x = false} = {h} := by
      ext g; simp only [mem_ofPred_eq, mem_singleton_iff]; constructor
      · exact fun h' => h'.1
      · rintro rfl; exact ⟨rfl, hx⟩
    have e2 : {g ∈ ({h} : Set (Pt → Bool)) | g x = true} = ∅ := by
      ext g; simp only [mem_ofPred_eq, mem_singleton_iff, mem_empty_iff_false, iff_false, not_and]
      rintro rfl; simp [hx]
    rw [e1, e2]; simp
  · have e1 : {g ∈ ({h} : Set (Pt → Bool)) | g x = true} = {h} := by
      ext g; simp only [mem_ofPred_eq, mem_singleton_iff]; constructor
      · exact fun h' => h'.1
      · rintro rfl; exact ⟨rfl, hx⟩
    have e2 : {g ∈ ({h} : Set (Pt → Bool)) | g x = false} = ∅ := by
      ext g; simp only [mem_ofPred_eq, mem_singleton_iff, mem_empty_iff_false, iff_false, not_and]
      rintro rfl; simp [hx]
    rw [e1, e2]
    simp [ldim_eq_zero_of_subsingleton subsingleton_singleton]

lemma soa_Hc : SOA Hc = c0 := by
  funext z
  unfold SOA ldimBot
  have hT : {g ∈ Hc | g z = true}.Nonempty := ⟨c1, c1_mem, rfl⟩
  have hF : {g ∈ Hc | g z = false}.Nonempty := ⟨c0, c0_mem, rfl⟩
  rw [if_pos hF, if_pos hT]
  simp only [c0_apply, decide_eq_false_iff_not, not_lt]
  obtain ⟨r, -, hr⟩ := fresh_finset {z} ∅
  have h1 : (1 : ℕ∞) ≤ ldim {g ∈ Hc | g z = false} :=
    one_le_ldim (base r) ⟨c0, ⟨c0_mem, rfl⟩, rfl⟩ ⟨fb r, ⟨fb_mem r, fb_off (hr z (by simp))⟩, by simp⟩
  have h2 := ldim_true_side_le z
  exact_mod_cast h2.trans h1

theorem sourceWitnesses : SourceWitnesses Hc 2 Aw := by
  refine ⟨fun h hh => ?_, fun h hh => ?_⟩
  · rw [localUniverse_eq] at hh
    by_cases h0 : h = c0
    · subst h0
      rw [rankOf_c0, Aw_c0, restrict_empty, ldim_Hc, witnessSpace_c0, layer2_eq]
      exact ⟨by simp, ⟨c0, c0_mem⟩, rfl, by simp [c0_mem]⟩
    · obtain ⟨hc, hpin⟩ := Aw_spec h hh h0
      rw [rankOf_other h hh h0, restrict_eq_singleton hh hpin,
        ldim_eq_zero_of_subsingleton subsingleton_singleton]
      refine ⟨by simpa using hc, singleton_nonempty h, rfl, ?_⟩
      ext f
      simp only [witnessSpace, rankLayer, localUniverse_eq, mem_inter_iff, mem_ofPred_eq,
        mem_singleton_iff]
      constructor
      · rintro ⟨⟨hf, hfA⟩, -⟩; exact hpin f ⟨hf, hfA⟩
      · rintro rfl; exact ⟨⟨hh, fun _ _ => rfl⟩, hh⟩
  · rw [localUniverse_eq] at hh
    by_cases h0 : h = c0
    · subst h0; rw [Aw_c0, restrict_empty, soa_Hc]
    · obtain ⟨-, hpin⟩ := Aw_spec h hh h0
      rw [restrict_eq_singleton hh hpin, soa_singleton]

end ChildDisproof

-- ===== part E =====

set_option autoImplicit false

open Set UnderstandingML PrivLittlestone MoranYanPAC.Main MoranYanPAC.Learner
open scoped ENNReal

namespace ChildDisproof

lemma gibbs_event {Y : Type*} (out : Finset Y) (hne : out.Nonempty) (f : Y → ℝ) (E : Set Y)
    [DecidablePred (· ∈ E)] :
    eventProbability (finiteGibbs out hne f) E =
      (∑ h ∈ out.filter (· ∈ E), ENNReal.ofReal (Real.exp (f h))) *
        (∑ h ∈ out, ENNReal.ofReal (Real.exp (f h)))⁻¹ := by
  unfold eventProbability finiteGibbs
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply]
  rw [tsum_fintype, Finset.sum_filter,
    ← Finset.sum_coe_sort out (fun h => if h ∈ E then ENNReal.ofReal (Real.exp (f h)) else 0),
    ← Finset.sum_coe_sort out (fun h => ENNReal.ofReal (Real.exp (f h))), Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  classical
  rw [Set.indicator_apply, PMF.normalize_apply, tsum_fintype]
  simp only [Set.mem_preimage]
  split_ifs <;> simp

lemma rank_eq (h : Pt → Bool) (hh : h ∈ Hc) : rankOf Hc 2 h = if h = c0 then 2 else 0 := by
  split_ifs with h0
  · subst h0; exact rankOf_c0
  · exact rankOf_other h hh h0

lemma selD_c0 (V : Set (Pt → Bool)) (hV : V ⊆ Hc) (h0 : c0 ∈ V) : selD Hc 2 Aw V = {c0} := by
  ext h
  simp only [selD, selDesc, Nat.reduceAdd, Nat.reduceLeDiff, if_true, mem_union, mem_ofPred_eq,
    mem_singleton_iff]
  constructor
  · rintro ((⟨hV', hr⟩ | ⟨hV', hr, -⟩) | ⟨hV', hr, hw⟩)
    · rw [rank_eq h (hV hV')] at hr; split_ifs at hr with hc; exact hc
    · rw [rank_eq h (hV hV')] at hr; split_ifs at hr <;> omega
    · exfalso
      refine hw c0 (Or.inl ⟨h0, rankOf_c0⟩) ?_
      rw [witnessSpace_c0]; exact hV hV'
  · rintro rfl; exact Or.inl (Or.inl ⟨h0, rankOf_c0⟩)

lemma selD_no_c0 (V : Set (Pt → Bool)) (hV : V ⊆ Hc) (h0 : c0 ∉ V) : selD Hc 2 Aw V = V := by
  ext h
  simp only [selD, selDesc, Nat.reduceAdd, Nat.reduceLeDiff, if_true, mem_union, mem_ofPred_eq]
  constructor
  · rintro ((⟨hV', -⟩ | ⟨hV', -⟩) | ⟨hV', -⟩) <;> exact hV'
  · intro hV'
    have hne : h ≠ c0 := fun e => h0 (e ▸ hV')
    refine Or.inr ⟨hV', by rw [rank_eq h (hV hV'), if_neg hne], fun g hg => ?_⟩
    exfalso
    rcases hg with ⟨hgV, hgr⟩ | ⟨hgV, hgr, -⟩
    · rw [rank_eq g (hV hgV)] at hgr; split_ifs at hgr with hc; exact h0 (hc ▸ hgV)
    · rw [rank_eq g (hV hgV)] at hgr; split_ifs at hgr <;> omega

lemma true_at_base (t : ℝ) : {h ∈ Hc | h (base t) = true} = {c1, fb t, fp t} := by
  ext h
  simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨hh, ht⟩
    rcases mem_Hc.mp hh with rfl | rfl | ⟨s, rfl⟩ | ⟨s, rfl⟩
    · simp at ht
    · exact Or.inl rfl
    · simp at ht; subst ht; exact Or.inr (Or.inl rfl)
    · simp at ht; subst ht; exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact ⟨c1_mem, rfl⟩
    · exact ⟨fb_mem t, by simp⟩
    · exact ⟨fp_mem t, by simp⟩

lemma candidates_one (t : ℝ) (y : Bool) :
    candidates Hc 2 Aw [(base t, y)] = {c0, c1, fb t, fp t} := by
  have hcell : ∀ v : Fin [(base t, y)].length → Bool,
      versionCell Hc 2 [(base t, y)] v = {h ∈ Hc | h (base t) = v ⟨0, by simp⟩} := by
    intro v
    ext h
    simp only [versionCell, localUniverse_eq, mem_ofPred_eq]
    constructor
    · rintro ⟨hh, hv⟩; exact ⟨hh, hv ⟨0, by simp⟩⟩
    · rintro ⟨hh, hv⟩
      refine ⟨hh, fun i => ?_⟩
      have : i = ⟨0, by simp⟩ := Fin.ext (by
        have h := i.isLt; simp only [List.length_cons, List.length_nil] at h; show (i : ℕ) = 0; omega)
      subst this; exact hv
  have hsel : ∀ v : Fin [(base t, y)].length → Bool,
      selD Hc 2 Aw (versionCell Hc 2 [(base t, y)] v) =
        if v ⟨0, by simp⟩ then {c1, fb t, fp t} else {c0} := by
    intro v
    rw [hcell v]
    cases hv : v ⟨0, by simp⟩
    · exact selD_c0 _ (fun h hh => hh.1) ⟨c0_mem, rfl⟩
    · rw [selD_no_c0 _ (fun h hh => hh.1) (fun h => by simp at h), true_at_base]; rfl
  ext h
  simp only [candidates, mem_iUnion, hsel]
  constructor
  · rintro ⟨v, hv⟩
    split_ifs at hv
    · simp only [mem_insert_iff, mem_singleton_iff] at hv ⊢; tauto
    · simp only [mem_insert_iff, mem_singleton_iff] at hv ⊢; tauto
  · intro hh
    simp only [mem_insert_iff, mem_singleton_iff] at hh
    rcases hh with rfl | hh
    · exact ⟨fun _ => false, by simp⟩
    · exact ⟨fun _ => true, by simp only [if_true, mem_insert_iff, mem_singleton_iff]; tauto⟩

lemma candidateOut_one (t : ℝ) (y : Bool) :
    candidateOut Hc 2 Aw [(base t, y)] = {c0, c1, fb t, fp t} := by
  have hfin : (candidates Hc 2 Aw [(base t, y)]).Finite ∧ (candidates Hc 2 Aw [(base t, y)]).Nonempty := by
    rw [candidates_one]; exact ⟨toFinite _, insert_nonempty _ _⟩
  unfold candidateOut
  rw [dif_pos hfin]
  apply Finset.coe_injective
  rw [Set.Finite.coe_toFinset, candidates_one]
  simp

lemma c0_ne_c1 : c0 ≠ c1 := fun e => by have := congrFun e (base 0); simp at this
lemma c0_ne_fb (t : ℝ) : c0 ≠ fb t := fun e => by have := congrFun e (base t); simp at this
lemma c0_ne_fp (t : ℝ) : c0 ≠ fp t := fun e => by have := congrFun e (base t); simp at this
lemma c1_ne_fb (t : ℝ) : c1 ≠ fb t := fun e => by have := congrFun e (base (t + 1)); simp at this
lemma c1_ne_fp (t : ℝ) : c1 ≠ fp t := fun e => by have := congrFun e (base (t + 1)); simp at this
lemma fb_ne_fp {t : ℝ} (ht : t ∈ vitali) : fb t ≠ fp t := fun e => by
  have := congrFun e (partner t ht); simp at this

/-- The Gibbs exponent of the learner on the sample `[(base t, false)]`. -/
noncomputable def expo (ε δ : ℝ) (t : ℝ) (h : Pt → Bool) : ℝ :=
  (ε / (2 * 1)) * ((candidateData Hc 2 Aw).score [(base t, false)] h +
    rankBonus ε δ 1 (4 * (((2 : ℕ) : ℝ) + 1)) * ((candidateData Hc 2 Aw).rank h : ℝ))

lemma expo_true (ε δ t : ℝ) (h : Pt → Bool) (hh : h ∈ Hc) (h0 : h ≠ c0) (ht : h (base t) = true) :
    ENNReal.ofReal (Real.exp (expo ε δ t h)) = 1 := by
  have hr : (candidateData Hc 2 Aw).rank h = 0 := rankOf_other h hh h0
  have hs : (candidateData Hc 2 Aw).score [(base t, false)] h = 0 := by
    show ((([(base t, false)] : List (Pt × Bool)).length : ℝ) - (empiricalLoss [(base t, false)] h : ℝ)) = 0
    simp [empiricalLoss, ht]
  simp [expo, hr, hs]

noncomputable def A0 (ε δ t : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (expo ε δ t c0))

lemma A0_ne_top (ε δ t : ℝ) : A0 ε δ t ≠ ⊤ := ENNReal.ofReal_ne_top

open Classical in
lemma condSuccess_one (t : ℝ) (P : MeasureTheory.Measure (Pt × Bool)) (α ε δ : ℝ)
    (hL0 : populationLoss P c0 ≤ α) (hL1 : ¬ populationLoss P c1 ≤ α)
    (hLb : populationLoss P (fb t) ≤ α) (hLp : populationLoss P (fp t) ≤ α) :
    conditionalSuccess (littlestoneLearner Hc 2 Aw ε δ) P α [(base t, false)] =
      if t ∈ vitali then (A0 ε δ t + 2) * (A0 ε δ t + 3)⁻¹
      else (A0 ε δ t + 1) * (A0 ε δ t + 2)⁻¹ := by
  classical
  unfold conditionalSuccess littlestoneLearner structuralMechanism
  rw [gibbs_event]
  have hout : (candidateData Hc 2 Aw).out [(base t, false)] = {c0, c1, fb t, fp t} :=
    candidateOut_one t false
  rw [hout]
  have e1 := expo_true ε δ t c1 c1_mem c0_ne_c1.symm rfl
  have e2 := expo_true ε δ t (fb t) (fb_mem t) (c0_ne_fb t).symm (by simp)
  have e3 := expo_true ε δ t (fp t) (fp_mem t) (c0_ne_fp t).symm (by simp)
  change (∑ h ∈ _, ENNReal.ofReal (Real.exp (expo ε δ t h))) *
    (∑ h ∈ _, ENNReal.ofReal (Real.exp (expo ε δ t h)))⁻¹ = _
  split_ifs with ht
  · have hn1 : c0 ∉ ({c1, fb t, fp t} : Finset (Pt → Bool)) := by
      simp [c0_ne_c1, c0_ne_fb, c0_ne_fp]
    have hn2 : c1 ∉ ({fb t, fp t} : Finset (Pt → Bool)) := by simp [c1_ne_fb, c1_ne_fp]
    have hn3 : fb t ∉ ({fp t} : Finset (Pt → Bool)) := by simp [fb_ne_fp ht]
    rw [Finset.filter_insert, Finset.filter_insert, Finset.filter_insert, Finset.filter_singleton]
    simp only [mem_ofPred_eq, hL0, hL1, hLb, hLp, if_true, if_false]
    rw [Finset.sum_insert hn1, Finset.sum_insert hn2, Finset.sum_insert hn3, Finset.sum_singleton,
      Finset.sum_insert (by simp [c0_ne_fb, c0_ne_fp]), Finset.sum_insert hn3,
      Finset.sum_singleton, e1, e2, e3]
    unfold A0
    congr 1
    · ring
    · congr 1; ring
  · have hp : fp t = fb t := fp_eq_fb ht
    rw [hp]
    have hn1 : c0 ∉ ({c1, fb t} : Finset (Pt → Bool)) := by simp [c0_ne_c1, c0_ne_fb]
    have hn2 : c1 ∉ ({fb t} : Finset (Pt → Bool)) := by simp [c1_ne_fb]
    have hdup : ({c0, c1, fb t, fb t} : Finset (Pt → Bool)) = {c0, c1, fb t} := by
      ext x; simp
    rw [hdup, Finset.filter_insert, Finset.filter_insert, Finset.filter_singleton]
    rw [hp] at hLp
    simp only [mem_ofPred_eq, hL0, hL1, hLb, if_true, if_false]
    rw [Finset.sum_insert hn1, Finset.sum_insert hn2, Finset.sum_singleton,
      Finset.sum_pair (c0_ne_fb t), e1, e2]
    unfold A0
    congr 1
    · congr 1; ring

end ChildDisproof

-- ===== part F =====

set_option autoImplicit false

open Set UnderstandingML PrivLittlestone MoranYanPAC.Main MoranYanPAC.Learner MeasureTheory
open scoped ENNReal

namespace ChildDisproof

/-! ### Measurability basics -/

lemma meas_decide {Ω : Type*} [MeasurableSpace Ω] {p : Ω → Prop} [DecidablePred p]
    (hp : MeasurableSet {ω | p ω}) : Measurable (fun ω => decide (p ω)) := by
  refine measurable_to_countable' fun b => ?_
  cases b
  · convert hp.compl using 1; ext a; simp
  · convert hp using 1; ext a; simp

lemma measSet_ne_bool {Ω : Type*} [MeasurableSpace Ω] {F G : Ω → Bool} (hF : Measurable F)
    (hG : Measurable G) : MeasurableSet {ω | F ω ≠ G ω} :=
  (hF.prodMk hG) (Set.to_countable {p : Bool × Bool | p.1 ≠ p.2}).measurableSet

lemma meas_coord : Measurable (fun z : Pt => z.1.1) := measurable_fst.comp measurable_subtype_coe
lemma meas_tag : Measurable (fun z : Pt => z.1.2) := measurable_snd.comp measurable_subtype_coe

lemma measurable_base : Measurable base :=
  (measurable_id.prodMk measurable_const).subtype_mk

lemma meas_fb_gen {Ω : Type*} [MeasurableSpace Ω] {r : Ω → ℝ} {z : Ω → Pt} (hr : Measurable r)
    (hz : Measurable z) : Measurable (fun ω => fb (r ω) (z ω)) := by
  unfold fb
  refine meas_decide ?_
  exact (measurableSet_eq_fun (meas_coord.comp hz) hr).inter
    ((meas_tag.comp hz) (measurableSet_singleton false))

lemma meas_fp_gen {Ω : Type*} [MeasurableSpace Ω] {r : Ω → ℝ} {z : Ω → Pt} (hr : Measurable r)
    (hz : Measurable z) : Measurable (fun ω => fp (r ω) (z ω)) := by
  unfold fp
  exact meas_decide (measurableSet_eq_fun (meas_coord.comp hz) hr)

lemma measurable_Hc {h : Pt → Bool} (hh : h ∈ Hc) : Measurable h := by
  rcases mem_Hc.mp hh with rfl | rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩
  · exact measurable_const
  · exact measurable_const
  · exact meas_fb_gen measurable_const measurable_id
  · exact meas_fp_gen measurable_const measurable_id

lemma lossSet_meas {h : Pt → Bool} (hm : Measurable h) :
    MeasurableSet {z : Pt × Bool | h z.1 ≠ z.2} :=
  measSet_ne_bool (hm.comp measurable_fst) measurable_snd

/-! ### The distribution -/

noncomputable def μ0 : Measure ℝ := volume.restrict (Icc 0 1)

instance : IsProbabilityMeasure μ0 := ⟨by simp [μ0]⟩

noncomputable def emb (r : ℝ) : Pt × Bool := (base r, false)

lemma measurable_emb : Measurable emb := measurable_base.prodMk measurable_const

noncomputable def Pm : Measure (Pt × Bool) := μ0.map emb

instance : IsProbabilityMeasure Pm := Measure.isProbabilityMeasure_map measurable_emb.aemeasurable

lemma popLoss_eq {h : Pt → Bool} (hm : Measurable h) :
    populationLoss Pm h = (μ0 {r | h (base r) = true}).toReal := by
  unfold populationLoss Pm
  rw [Measure.map_apply measurable_emb (lossSet_meas hm)]
  congr 2
  ext r; simp [emb]

lemma popLoss_c0 : populationLoss Pm c0 = 0 := by
  rw [popLoss_eq (measurable_Hc c0_mem)]; simp
lemma popLoss_c1 : populationLoss Pm c1 = 1 := by
  rw [popLoss_eq (measurable_Hc c1_mem)]; simp
lemma popLoss_fb (t : ℝ) : populationLoss Pm (fb t) = 0 := by
  rw [popLoss_eq (measurable_Hc (fb_mem t))]
  have : {r : ℝ | fb t (base r) = true} = {t} := by ext r; simp
  rw [this]
  have : μ0 {t} = 0 := le_antisymm ((Measure.restrict_le_self _).trans (by simp)) bot_le
  simp [this]
lemma popLoss_fp (t : ℝ) : populationLoss Pm (fp t) = 0 := by
  rw [popLoss_eq (measurable_Hc (fp_mem t))]
  have : {r : ℝ | fp t (base r) = true} = {t} := by ext r; simp
  rw [this]
  have : μ0 {t} = 0 := le_antisymm ((Measure.restrict_le_self _).trans (by simp)) bot_le
  simp [this]

lemma realizable : Realizable Hc Pm := by
  refine ⟨c0, c0_mem, ?_⟩
  unfold Pm
  have hS : MeasurableSet {z : Pt × Bool | c0 z.1 = z.2} := by
    have : {z : Pt × Bool | c0 z.1 = z.2} = Prod.snd ⁻¹' {false} := by
      ext z; simp only [mem_ofPred_eq, mem_preimage, mem_singleton_iff, c0_apply]; exact eq_comm
    rw [this]; exact measurable_snd (measurableSet_singleton false)
  rw [ae_map_iff measurable_emb.aemeasurable hS]
  exact Filter.Eventually.of_forall fun r => rfl

end ChildDisproof

-- ===== part G =====

set_option autoImplicit false

open Set UnderstandingML PrivLittlestone MoranYanPAC.Main MoranYanPAC.Learner MeasureTheory
open scoped ENNReal

namespace ChildDisproof

lemma empLoss_ofFn {k : ℕ} (s : Fin k → Pt × Bool) (h : Pt → Bool) :
    (empiricalLoss (List.ofFn s) h : ℝ) = ∑ j, if h (s j).1 ≠ (s j).2 then (1 : ℝ) else 0 := by
  induction k with
  | zero => simp [empiricalLoss]
  | succ k ih =>
    rw [List.ofFn_succ, Fin.sum_univ_succ, ← ih (fun i => s i.succ)]
    unfold empiricalLoss
    rw [List.filter_cons]
    split_ifs with h1 h2 h2 <;> simp_all <;> ring

lemma meas_emp {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (σ : Ω → Fin k → Pt × Bool)
    (g : Ω → Pt → Bool) (hg : ∀ j, MeasurableSet {ω | g ω (σ ω j).1 ≠ (σ ω j).2}) :
    Measurable (fun ω => empiricalRate (List.ofFn (σ ω)) (g ω)) := by
  unfold empiricalRate
  simp only [List.length_ofFn, empLoss_ofFn]
  exact (Finset.measurable_sum _ fun j _ => Measurable.ite (hg j) measurable_const
    measurable_const).div_const _

lemma emp_congr (l : List (Pt × Bool)) {g h : Pt → Bool} (hgh : ∀ z ∈ l, g z.1 = h z.1) :
    empiricalRate l g = empiricalRate l h := by
  unfold empiricalRate empiricalLoss
  congr 3
  exact List.filter_congr (fun z hz => by simp [hgh z hz])

/-- finite family of hypotheses indexed by the sample points -/
noncomputable def famG {ι : Type} (q : ι → Pt) : Bool ⊕ (ι × Bool) → (Pt → Bool)
  | Sum.inl false => c0
  | Sum.inl true => c1
  | Sum.inr (i, false) => fb (q i).1.1
  | Sum.inr (i, true) => fp (q i).1.1

def lossK {ι : Type} : Bool ⊕ (ι × Bool) → ℝ
  | Sum.inl true => 1
  | _ => 0

lemma famG_mem {ι : Type} (q : ι → Pt) (k : Bool ⊕ (ι × Bool)) : famG q k ∈ Hc := by
  rcases k with (_ | _) | ⟨i, _ | _⟩
  · exact c0_mem
  · exact c1_mem
  · exact fb_mem _
  · exact fp_mem _

lemma popLoss_famG {ι : Type} (q : ι → Pt) (k : Bool ⊕ (ι × Bool)) :
    populationLoss Pm (famG q k) = lossK k := by
  rcases k with (_ | _) | ⟨i, _ | _⟩
  · exact popLoss_c0
  · exact popLoss_c1
  · exact popLoss_fb _
  · exact popLoss_fp _

lemma reduce {ι : Type} (q : ι → Pt) (h : Pt → Bool) (hh : h ∈ Hc) :
    ∃ k, (∀ i, famG q k (q i) = h (q i)) ∧ populationLoss Pm (famG q k) = populationLoss Pm h := by
  classical
  rcases mem_Hc.mp hh with rfl | rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩
  · exact ⟨Sum.inl false, fun _ => rfl, rfl⟩
  · exact ⟨Sum.inl true, fun _ => rfl, rfl⟩
  · by_cases hex : ∃ i, (q i).1.1 = t
    · obtain ⟨i, hi⟩ := hex
      refine ⟨Sum.inr (i, false), fun j => ?_, ?_⟩ <;> simp [famG, hi]
    · push Not at hex
      refine ⟨Sum.inl false, fun j => (fb_off (hex j)).symm, ?_⟩
      rw [popLoss_fb]; exact popLoss_c0
  · by_cases hex : ∃ i, (q i).1.1 = t
    · obtain ⟨i, hi⟩ := hex
      refine ⟨Sum.inr (i, true), fun j => ?_, ?_⟩ <;> simp [famG, hi]
    · push Not at hex
      refine ⟨Sum.inl false, fun j => (fp_off (hex j)).symm, ?_⟩
      rw [popLoss_fp]; exact popLoss_c0

lemma meas_famG {Ω ι : Type} [MeasurableSpace Ω] (pts : Ω → ι → Pt)
    (hpts : ∀ i, Measurable (fun ω => pts ω i)) (z : Ω → Pt × Bool) (hz : Measurable z)
    (k : Bool ⊕ (ι × Bool)) : MeasurableSet {ω | famG (pts ω) k (z ω).1 ≠ (z ω).2} := by
  rcases k with (_ | _) | ⟨i, _ | _⟩
  · exact measSet_ne_bool measurable_const (measurable_snd.comp hz)
  · exact measSet_ne_bool measurable_const (measurable_snd.comp hz)
  · exact measSet_ne_bool (meas_fb_gen (meas_coord.comp (hpts i)) (measurable_fst.comp hz))
      (measurable_snd.comp hz)
  · exact measSet_ne_bool (meas_fp_gen (meas_coord.comp (hpts i)) (measurable_fst.comp hz))
      (measurable_snd.comp hz)

def pts1 {n : ℕ} (s : Fin n → Pt × Bool) : Fin n → Pt := fun j => (s j).1

def pts2 {n m : ℕ} (p : (Fin n → Pt × Bool) × (Fin m → Pt × Bool)) : Fin n ⊕ Fin m → Pt :=
  Sum.elim (fun i => (p.1 i).1) (fun j => (p.2 j).1)


theorem vcEvents : VCEventsMeasurable (localUniverse Hc 2) Pm := by
  rw [localUniverse_eq]
  refine ⟨fun h hh => lossSet_meas (measurable_Hc hh), fun n a b => ?_, fun n m a b => ?_⟩
  · have hpts : ∀ i, Measurable (fun s : Fin n → Pt × Bool => pts1 s i) :=
      fun i => measurable_fst.comp (measurable_pi_apply i)
    have : {s : Fin n → Pt × Bool | ∃ h ∈ Hc, empiricalRate (List.ofFn s) h ≤ a ∧
        b < populationLoss Pm h} = ⋃ k : Bool ⊕ (Fin n × Bool),
          {s | empiricalRate (List.ofFn s) (famG (pts1 s) k) ≤ a} ∩ {_s | b < lossK k} := by
      ext s
      simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
      constructor
      · rintro ⟨h, hh, he, hl⟩
        obtain ⟨k, hk, hkl⟩ := reduce (pts1 s) h hh
        refine ⟨k, ?_, ?_⟩
        · rw [emp_congr _ (h := h) (fun z hz => by
            obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz; exact hk j)]
          exact he
        · rw [← popLoss_famG (pts1 s) k, hkl]; exact hl
      · rintro ⟨k, he, hl⟩
        exact ⟨famG (pts1 s) k, famG_mem _ k, he, by rw [popLoss_famG]; exact hl⟩
    rw [this]
    exact MeasurableSet.iUnion fun k => (measurableSet_le (meas_emp (fun s => s) _
      (fun j => meas_famG pts1 hpts _ (measurable_pi_apply j) k)) measurable_const).inter
      (MeasurableSet.const _)
  · have hpts : ∀ i, Measurable (fun p : (Fin n → Pt × Bool) × (Fin m → Pt × Bool) => pts2 p i) := by
      rintro (i | j)
      · exact measurable_fst.comp ((measurable_pi_apply i).comp measurable_fst)
      · exact measurable_fst.comp ((measurable_pi_apply j).comp measurable_snd)
    have : {p : (Fin n → Pt × Bool) × (Fin m → Pt × Bool) | ∃ h ∈ Hc,
        empiricalRate (List.ofFn p.1) h ≤ a ∧ b < empiricalRate (List.ofFn p.2) h} =
        ⋃ k : Bool ⊕ ((Fin n ⊕ Fin m) × Bool),
          {p | empiricalRate (List.ofFn p.1) (famG (pts2 p) k) ≤ a} ∩
            {p | b < empiricalRate (List.ofFn p.2) (famG (pts2 p) k)} := by
      ext p
      simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
      constructor
      · rintro ⟨h, hh, he, hl⟩
        obtain ⟨k, hk, -⟩ := reduce (pts2 p) h hh
        refine ⟨k, ?_, ?_⟩
        · rw [emp_congr _ (h := h) (fun z hz => by
            obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz; exact hk (Sum.inl j))]
          exact he
        · rw [emp_congr _ (h := h) (fun z hz => by
            obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz; exact hk (Sum.inr j))]
          exact hl
      · rintro ⟨k, he, hl⟩
        exact ⟨famG (pts2 p) k, famG_mem _ k, he, hl⟩
    rw [this]
    refine MeasurableSet.iUnion fun k => ?_
    have h1 : Measurable (fun p : (Fin n → Pt × Bool) × (Fin m → Pt × Bool) =>
        empiricalRate (List.ofFn p.1) (famG (pts2 p) k)) := by
      refine meas_emp (Ω := (Fin n → Pt × Bool) × (Fin m → Pt × Bool)) (k := n) (fun p => p.1)
        (fun p => famG (pts2 p) k) fun j => ?_
      have hz : Measurable (fun p : (Fin n → Pt × Bool) × (Fin m → Pt × Bool) => p.1 j) :=
        (measurable_pi_apply j).comp measurable_fst
      exact meas_famG pts2 hpts (fun p => p.1 j) hz k
    have h2 : Measurable (fun p : (Fin n → Pt × Bool) × (Fin m → Pt × Bool) =>
        empiricalRate (List.ofFn p.2) (famG (pts2 p) k)) := by
      refine meas_emp (Ω := (Fin n → Pt × Bool) × (Fin m → Pt × Bool)) (k := m) (fun p => p.2)
        (fun p => famG (pts2 p) k) fun j => ?_
      have hz : Measurable (fun p : (Fin n → Pt × Bool) × (Fin m → Pt × Bool) => p.2 j) :=
        (measurable_pi_apply j).comp measurable_snd
      exact meas_famG pts2 hpts (fun p => p.2 j) hz k
    exact (measurableSet_le h1 measurable_const).inter (measurableSet_lt measurable_const h2)

end ChildDisproof

-- ===== part H =====

set_option autoImplicit false

open Set UnderstandingML PrivLittlestone MoranYanPAC.Main MoranYanPAC.Learner MeasureTheory
open scoped ENNReal

namespace ChildDisproof

lemma A0_const (ε δ t : ℝ) : A0 ε δ t = A0 ε δ 0 := by
  have h : ∀ t : ℝ, expo ε δ t c0 =
      (ε / (2 * 1)) * (1 + rankBonus ε δ 1 (4 * (((2 : ℕ) : ℝ) + 1)) * 2) := by
    intro t
    have hs : (candidateData Hc 2 Aw).score [(base t, false)] c0 = 1 := by
      show ((([(base t, false)] : List (Pt × Bool)).length : ℝ) -
        (empiricalLoss [(base t, false)] c0 : ℝ)) = 1
      simp [empiricalLoss]
    have hr : ((candidateData Hc 2 Aw).rank c0 : ℝ) = 2 := by
      show ((rankOf Hc 2 c0 : ℕ) : ℝ) = 2
      rw [rankOf_c0]; norm_num
    rw [expo, hs, hr]
  unfold A0; rw [h t, h 0]

lemma vals_ne (a : ℝ) (ha : 0 ≤ a) :
    (ENNReal.ofReal a + 2) * (ENNReal.ofReal a + 3)⁻¹ ≠
      (ENNReal.ofReal a + 1) * (ENNReal.ofReal a + 2)⁻¹ := by
  intro h
  have h2 := congrArg ENNReal.toReal h
  have e1 : (ENNReal.ofReal a + 2).toReal = a + 2 := by
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top (by simp), ENNReal.toReal_ofReal ha]; simp
  have e2 : (ENNReal.ofReal a + 3).toReal = a + 3 := by
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top (by simp), ENNReal.toReal_ofReal ha]; simp
  have e3 : (ENNReal.ofReal a + 1).toReal = a + 1 := by
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top (by simp), ENNReal.toReal_ofReal ha]; simp
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_inv, e1, e2, e3]
    at h2
  have hp2 : (0 : ℝ) < a + 2 := by linarith
  have hp3 : (0 : ℝ) < a + 3 := by linarith
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff hp3.ne' hp2.ne'] at h2
  nlinarith

noncomputable def ι1 (r : ℝ) : Fin 1 → Pt × Bool := fun _ => emb r

lemma measurable_ι1 : Measurable ι1 := measurable_pi_lambda _ fun _ => measurable_emb

lemma sampleLaw_one : sampleLaw Pm 1 = μ0.map ι1 := by
  have hmp := (measurePreserving_funUnique Pm (Fin 1)).symm
  unfold sampleLaw iidLaw
  refine hmp.map_eq.symm.trans ?_
  rw [Pm, Measure.map_map (MeasurableEquiv.measurable _) measurable_emb]
  congr 1

theorem not_aemeasurable :
    ¬ AEMeasurable (fun s : Fin 1 → Pt × Bool =>
      conditionalSuccess (littlestoneLearner Hc 2 Aw 1 (1 / 2)) Pm (1 / 2) (List.ofFn s))
      (sampleLaw Pm 1) := by
  classical
  intro hF
  rw [sampleLaw_one] at hF
  have hG := hF.comp_measurable measurable_ι1
  set A := A0 1 (1 / 2) 0
  have hval : ∀ r : ℝ, ((fun s : Fin 1 → Pt × Bool =>
      conditionalSuccess (littlestoneLearner Hc 2 Aw 1 (1 / 2)) Pm (1 / 2) (List.ofFn s)) ∘ ι1) r =
      if r ∈ vitali then (A + 2) * (A + 3)⁻¹ else (A + 1) * (A + 2)⁻¹ := by
    intro r
    have hl : List.ofFn (ι1 r) = [(base r, false)] := by simp [ι1, emb]
    simp only [Function.comp_apply, hl]
    rw [condSuccess_one r Pm (1 / 2) 1 (1 / 2) (by rw [popLoss_c0]; norm_num)
      (by rw [popLoss_c1]; norm_num) (by rw [popLoss_fb]; norm_num) (by rw [popLoss_fp]; norm_num),
      A0_const]
  have hne : (A + 2) * (A + 3)⁻¹ ≠ (A + 1) * (A + 2)⁻¹ :=
    vals_ne _ (Real.exp_pos _).le
  have hpre : ((fun s : Fin 1 → Pt × Bool =>
      conditionalSuccess (littlestoneLearner Hc 2 Aw 1 (1 / 2)) Pm (1 / 2) (List.ofFn s)) ∘ ι1) ⁻¹'
      {(A + 2) * (A + 3)⁻¹} = vitali := by
    ext r
    simp only [mem_preimage, mem_singleton_iff, hval]
    split_ifs with hr
    · simp [hr]
    · simp only [hr, iff_false]; exact fun h => hne h.symm
  have := hG.nullMeasurable (measurableSet_singleton ((A + 2) * (A + 3)⁻¹))
  rw [hpre] at this
  exact vitali_not_nullMeasurable_restrict this

end ChildDisproof

open MoranYanPAC.Main MoranYanPAC.Learner MeasureTheory in
theorem solution : ¬ (∀ {X : Type} [MeasurableSpace X]
    (H : Set (X → Bool)) (d : ℕ) (hH : H.Nonempty) (hd : UnderstandingML.ldim H = d) (hd1 : 1 ≤ d)
    (Aw : (X → Bool) → Finset X) (hAw : SourceWitnesses H d Aw)
    (α ε δ : ℝ) (hα : 0 < α) (hα1 : α < 1) (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (P : Measure (X × Bool)) (hP : IsProbabilityMeasure P)
    (hPm : VCEventsMeasurable (PrivLittlestone.localUniverse H d) P) (hR : Realizable H P)
    (n : ℕ),
    AEMeasurable (fun s : Fin n → X × Bool =>
      conditionalSuccess (littlestoneLearner H d Aw ε δ) P α (List.ofFn s)) (sampleLaw P n)) := by
  intro hall
  exact ChildDisproof.not_aemeasurable
    (hall (X := ChildDisproof.Pt) ChildDisproof.Hc 2 ⟨ChildDisproof.c0, ChildDisproof.c0_mem⟩
      (by rw [ChildDisproof.ldim_Hc]; rfl) (by norm_num) ChildDisproof.Aw
      ChildDisproof.sourceWitnesses (1 / 2) 1 (1 / 2) (by norm_num) (by norm_num) (by norm_num)
      le_rfl (by norm_num) (by norm_num) ChildDisproof.Pm inferInstance ChildDisproof.vcEvents
      ChildDisproof.realizable 1)
