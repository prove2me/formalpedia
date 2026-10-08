-- Prove2me | solution 1 for MechanismDesign.IncentiveCompat.rich_weaklyMonotone_implementable
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T06:37:59.605294+00:00
-- url     : https://prove2.me/submissions/cd11b976-1325-40a3-ae76-b2426d6d91cc

import Definitions.Def_MechanismDesign_IncentiveCompat_Model
set_option autoImplicit false

set_option autoImplicit false
namespace RochetRichAnchor
open MechanismDesign.IncentiveCompat
variable {A Θ : Type*}

theorem exists_range_maximal [Finite A] [Nonempty Θ] (q : Θ → A)
    (R : A → A → Prop) (hrefl : ∀ a, R a a)
    (htrans : ∀ a b c, R a b → R b c → R a c) :
    ∃ K ∈ Set.range q, ∀ b ∈ Set.range q, R b K → R K b := by
  letI : Preorder A := {
    le := fun a b => R b a
    le_refl := fun a => hrefl a
    le_trans := fun a b c hab hbc => htrans c b a hbc hab }
  obtain ⟨K, hK, hmax⟩ := (Set.toFinite (Set.range q)).exists_maximal (Set.range_nonempty q)
  exact ⟨K, hK, fun b hb hbk => hmax hb hbk⟩

def marginSet (u : A → Θ → ℝ) (R : A → A → Prop) (q : Θ → A) (K b : A) : Set ℝ :=
  (fun x => u K x - u b x) '' {x | R (q x) K}

noncomputable def price (u : A → Θ → ℝ) (R : A → A → Prop) (q : Θ → A)
    (K b : A) : ℝ := -sInf (marginSet u R q K b)

variable (u : A → Θ → ℝ) (R : A → A → Prop) (q : Θ → A) (K : A)
    (hrefl : ∀ a, R a a) (hcons : IsConsistentWRT u R)
    (hq : WeaklyMonotone u q) (hK : K ∈ Set.range q)
    (hmax : ∀ b ∈ Set.range q, R b K → R K b)

include hcons hmax in
theorem upper_alloc_utility_eq {b : A} (hb : b ∈ Set.range q) (hbk : R b K) (x : Θ) :
    u b x = u K x :=
  le_antisymm (hcons x K b (hmax b hb hbk)) (hcons x b K hbk)

include hrefl hK in
theorem margin_nonempty (b : A) : (marginSet u R q K b).Nonempty := by
  obtain ⟨x, hx⟩ := hK
  exact ⟨u K x - u b x, x, by change R (q x) K; rw [hx]; exact hrefl K, rfl⟩

include hcons hq hmax in
theorem margin_lower_bound {b : A} (y : Θ) (hy : q y = b) :
    ∀ z ∈ marginSet u R q K b, u K y - u b y ≤ z := by
  rintro z ⟨x, hx, rfl⟩
  have h := hq x y
  have hxy := upper_alloc_utility_eq u R q K hcons hmax ⟨x, rfl⟩ hx y
  have hxx := upper_alloc_utility_eq u R q K hcons hmax ⟨x, rfl⟩ hx x
  rw [hy, hxy, hxx] at h
  exact h

include hcons hq hmax in
theorem margin_bddBelow {b : A} (hb : b ∈ Set.range q) :
    BddBelow (marginSet u R q K b) := by
  obtain ⟨y, hy⟩ := hb
  exact ⟨u K y - u b y, margin_lower_bound u R q K hcons hq hmax y hy⟩

include hrefl hcons hq hK hmax in
theorem selected_net_ge_anchor (x : Θ) :
    u K x ≤ u (q x) x - price u R q K (q x) := by
  have h := le_csInf (margin_nonempty u R q K hrefl hK (q x))
    (margin_lower_bound u R q K hcons hq hmax x rfl)
  dsimp [price]
  linarith

include hcons hq hmax in
theorem anchor_selected_net_le {x : Θ} (hx : R (q x) K)
    {b : A} (hb : b ∈ Set.range q) :
    u b x - price u R q K b ≤ u K x := by
  have h := csInf_le (margin_bddBelow u R q K hcons hq hmax hb)
    (show u K x - u b x ∈ marginSet u R q K b from ⟨x, hx, rfl⟩)
  dsimp [price]
  linarith

include hrefl hcons hq hK hmax in
theorem ordered_prices {a b : A} (ha : a ∈ Set.range q) (hb : b ∈ Set.range q)
    (hba : R b a) : price u R q K a ≤ price u R q K b := by
  have h : sInf (marginSet u R q K b) ≤ sInf (marginSet u R q K a) := by
    apply le_csInf (margin_nonempty u R q K hrefl hK a)
    rintro z ⟨x, hx, rfl⟩
    have hmem := csInf_le (margin_bddBelow u R q K hcons hq hmax hb)
      (show u K x - u b x ∈ marginSet u R q K b from ⟨x, hx, rfl⟩)
    have hval := hcons x b a hba
    linarith
  dsimp [price]
  linarith

include hrefl hcons hK hmax in
theorem upper_alloc_price_zero {b : A} (hb : b ∈ Set.range q) (hbk : R b K) :
    price u R q K b = 0 := by
  have hset : marginSet u R q K b = {0} := by
    apply Set.Subset.antisymm
    · rintro z ⟨x, hx, rfl⟩
      have h := upper_alloc_utility_eq u R q K hcons hmax hb hbk x
      simp [h]
    · intro z hz
      have hz' : z = 0 := hz
      subst z
      obtain ⟨x, hx⟩ := hK
      refine ⟨x, ?_, ?_⟩
      · change R (q x) K
        rw [hx]
        exact hrefl K
      · change u K x - u b x = 0
        rw [upper_alloc_utility_eq u R q K hcons hmax hb hbk x]
        exact sub_self _
  simp [price, hset]

end RochetRichAnchor

set_option autoImplicit false
namespace RochetRichPerturbation
open MechanismDesign.IncentiveCompat
variable {A : Type*}

/-- Choose a positive amount below a positive cap and every positive gap in
a finite valuation vector; the set of positive gaps may be empty. -/
theorem finite_positive_small [Finite A] (V : A → ℝ) (a : A) (cap : ℝ) (hcap : 0 < cap) :
    ∃ ε : ℝ, 0 < ε ∧ ε < cap ∧ ∀ c, V a < V c → ε < V c - V a := by
  classical
  letI := Fintype.ofFinite A
  let s : Finset ℝ := insert cap ((Finset.univ.filter (fun c => V a < V c)).image
    (fun c => V c - V a))
  have hs : s.Nonempty := ⟨cap, Finset.mem_insert_self _ _⟩
  have hpos : ∀ r ∈ s, 0 < r := by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact hcap
    · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hr
      exact sub_pos.mpr (Finset.mem_filter.mp hc).2
  let m : ℝ := s.min' hs
  have hm : 0 < m := hpos m (Finset.min'_mem s hs)
  refine ⟨m / 2, by positivity, ?_, ?_⟩
  · have h := Finset.min'_le s cap (Finset.mem_insert_self _ _)
    change m ≤ cap at h
    linarith
  · intro c hc
    have h := Finset.min'_le s (V c - V a) (Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩, rfl⟩))
    change m ≤ V c - V a at h
    linarith

noncomputable def perturb (R : A → A → Prop) (V : A → ℝ) (K a : A)
    (γ ε : ℝ) (c : A) : ℝ := by
  classical
  exact V c + if R c K then γ else if R c a ∧ V c = V a then ε else 0

/-- Boosting the upper cone and the equal-valued upper set preserves the
original preorder, including comparisons with unallocated alternatives. -/
theorem perturb_represents (R : A → A → Prop)
    (htrans : ∀ c d e, R c d → R d e → R c e)
    (V : A → ℝ) (hV : Represents R V) (K a : A) (γ ε : ℝ)
    (hε : 0 ≤ ε) (hγ : ε ≤ γ)
    (hgap : ∀ c, V a < V c → ε < V c - V a) :
    Represents R (perturb R V K a γ ε) := by
  classical
  intro c d hcd
  have hv := hV c d hcd
  by_cases hdH : R d K
  · have hcH := htrans c d K hcd hdH
    simp only [perturb, if_pos hdH, if_pos hcH]
    linarith
  by_cases hcH : R c K
  · simp only [perturb, if_neg hdH, if_pos hcH]
    split_ifs <;> linarith
  simp only [perturb, if_neg hdH, if_neg hcH]
  by_cases hdT : R d a ∧ V d = V a
  · by_cases hcT : R c a ∧ V c = V a
    · simp only [if_pos hdT, if_pos hcT]
      linarith
    · have hca := htrans c d a hcd hdT.1
      have hne : V c ≠ V a := by intro heq; exact hcT ⟨hca, heq⟩
      have hlt : V a < V c := by rw [hdT.2] at hv; exact lt_of_le_of_ne hv (Ne.symm hne)
      have hg := hgap c hlt
      simp only [if_pos hdT, if_neg hcT]
      linarith [hdT.2]
  · simp only [if_neg hdT]
    split_ifs <;> linarith

end RochetRichPerturbation

set_option autoImplicit false
open MechanismDesign.IncentiveCompat
open RochetRichAnchor RochetRichPerturbation

theorem solution {A Θ : Type*} [Finite A] [Nonempty Θ]
    (u : A → Θ → ℝ) (R : A → A → Prop) (hrefl : ∀ a, R a a)
    (htrans : ∀ a b c, R a b → R b c → R a c) (hrich : IsRichWRT u R)
    (hcons : IsConsistentWRT u R) (q : Θ → A) (hq : WeaklyMonotone u q) :
    Implementable u q := by
  classical
  obtain ⟨K, hK, hmax⟩ := exists_range_maximal q R hrefl htrans
  let p : A → ℝ := price u R q K
  refine ⟨fun θ => p (q θ), ?_⟩
  intro θ η
  let a := q θ
  let b := q η
  let V : A → ℝ := fun c => u c θ
  change V b - p b ≤ V a - p a
  by_contra hbad
  have hprofit : V a - p a < V b - p b := lt_of_not_ge hbad
  have ha : a ∈ Set.range q := ⟨θ, rfl⟩
  have hb : b ∈ Set.range q := ⟨η, rfl⟩
  have hanchor := selected_net_ge_anchor u R q K hrefl hcons hq hK hmax θ
  change V K ≤ V a - p a at hanchor
  have haH : ¬R a K := by
    intro h
    have heq := upper_alloc_utility_eq u R q K hcons hmax ha h θ
    have hp := upper_alloc_price_zero u R q K hrefl hcons hK hmax ha h
    have hu := anchor_selected_net_le u R q K hcons hq hmax h hb
    change V a = V K at heq
    change p a = 0 at hp
    change V b - p b ≤ V K at hu
    linarith
  have hbH : ¬R b K := by
    intro h
    have heq := upper_alloc_utility_eq u R q K hcons hmax hb h θ
    have hp := upper_alloc_price_zero u R q K hrefl hcons hK hmax hb h
    change V b = V K at heq
    change p b = 0 at hp
    linarith
  have hbT : ¬(R b a ∧ V b = V a) := by
    rintro ⟨hba, heq⟩
    have hp := ordered_prices u R q K hrefl hcons hq hK hmax ha hb hba
    change p a ≤ p b at hp
    linarith
  let L := V a - p a - V K
  let U := V b - p b - V K
  let γ := (L + U) / 2
  have hL : 0 ≤ L := by dsimp [L]; linarith
  have hLU : L < U := by dsimp [L, U]; linarith
  have hγL : L < γ := by dsimp [γ]; linarith
  have hγU : γ < U := by dsimp [γ]; linarith
  obtain ⟨ε, hε, hcap, hgap⟩ := finite_positive_small V a (γ - L) (by linarith)
  have hεγ : ε ≤ γ := by linarith
  let W := perturb R V K a γ ε
  have hW : Represents R W := perturb_represents R htrans V (hcons θ) K a γ ε hε.le hεγ hgap
  obtain ⟨θ', hval⟩ := hrich W hW
  let d := q θ'
  have hd : d ∈ Set.range q := ⟨θ', rfl⟩
  have hWa : W a = V a + ε := by
    simp [W, perturb, haH, hrefl a]
  have hWb : W b = V b := by
    simp only [W, perturb, if_neg hbH, if_neg hbT, add_zero]
  have hWK : W K = V K + γ := by
    simp only [W, perturb, if_pos (hrefl K)]
  by_cases hdH : R d K
  · have h := anchor_selected_net_le u R q K hcons hq hmax hdH hb
    change u b θ' - p b ≤ u K θ' at h
    rw [hval b, hval K, hWb, hWK] at h
    change γ < V b - p b - V K at hγU
    linarith
  by_cases hdT : R d a ∧ V d = V a
  · have hWd : W d = V d + ε := by
      simp only [W, perturb, if_neg hdH, if_pos hdT]
    have hp := ordered_prices u R q K hrefl hcons hq hK hmax ha hd hdT.1
    have h := selected_net_ge_anchor u R q K hrefl hcons hq hK hmax θ'
    change p a ≤ p d at hp
    change u K θ' ≤ u d θ' - p d at h
    rw [hval K, hval d, hWK, hWd, hdT.2] at h
    change ε < γ - (V a - p a - V K) at hcap
    linarith
  have hWd : W d = V d := by
    simp only [W, perturb, if_neg hdH, if_neg hdT, add_zero]
  have h := hq θ θ'
  change u a θ' - u d θ' ≤ V a - V d at h
  rw [hval a, hval d, hWa, hWd] at h
  linarith

#print axioms solution
