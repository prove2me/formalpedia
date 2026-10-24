-- Prove2me | solution 1 for LPCommunity.SBMRecovery.theorem_6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T10:15:58.993476+00:00
-- url     : https://prove2.me/submissions/e9d56d22-f752-49a9-b103-ab334a6deb75
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Setting
import Theorems.Thm_LPCommunity_LPRecovery_theorem_4
import Theorems.Thm_LPCommunity_SBMRecovery_proposition_3
import Theorems.Thm_LPCommunity_SBMRecovery_proposition_4

open Finset Filter Topology
open scoped Classical

namespace LP5Aux

open LPCommunity.SBMRecovery

/-- graphs on `Fin n` are the same as Boolean functions on the pairs `i < j`. -/
noncomputable def graphEquiv (n : ℕ) :
    SimpleGraph (Fin n) ≃ ({p : Fin n × Fin n // p ∈ pairs n} → Bool) where
  toFun G := fun p => decide (G.Adj p.1.1 p.1.2)
  invFun g :=
    { Adj := fun i j => (∃ h : (i, j) ∈ pairs n, g ⟨(i, j), h⟩ = true) ∨
          (∃ h : (j, i) ∈ pairs n, g ⟨(j, i), h⟩ = true)
      symm := ⟨fun _ _ h => Or.symm h⟩
      loopless := ⟨fun i h => by
        rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [pairs] at h⟩ }
  left_inv G := by
    ext i j
    rcases lt_trichotomy i j with hij | rfl | hij
    · have h1 : (i, j) ∈ pairs n := by simp [pairs, hij]
      have h2 : (j, i) ∉ pairs n := by simp [pairs, hij.le]
      constructor
      · rintro (⟨h, hg⟩ | ⟨h, hg⟩)
        · simpa using hg
        · exact absurd h h2
      · intro hG; exact Or.inl ⟨h1, by simpa using hG⟩
    · simp [pairs]
    · have h1 : (j, i) ∈ pairs n := by simp [pairs, hij]
      have h2 : (i, j) ∉ pairs n := by simp [pairs, hij.le]
      constructor
      · rintro (⟨h, hg⟩ | ⟨h, hg⟩)
        · exact absurd h h2
        · simpa [G.adj_comm] using hg
      · intro hG; exact Or.inr ⟨h1, by simpa [G.adj_comm] using hG⟩
  right_inv g := by
    funext ⟨⟨i, j⟩, h⟩
    have hij : i < j := by simpa [pairs] using h
    have h2 : (j, i) ∉ pairs n := by simp [pairs, hij.le]
    simp only
    cases hg : g ⟨(i, j), h⟩
    · simp only [decide_eq_false_iff_not]
      rintro (⟨h', hg'⟩ | ⟨h', _⟩)
      · rw [hg] at hg'; exact Bool.false_ne_true hg'
      · exact h2 h'
    · simp only [decide_eq_true_eq]
      exact Or.inl ⟨h, hg⟩

lemma edgeWeight_sum {n : ℕ} (r : Fin n → Fin n → ℝ) :
    ∑ G : SimpleGraph (Fin n), edgeWeight G r = 1 := by
  set f : {p : Fin n × Fin n // p ∈ pairs n} → Bool → ℝ :=
    fun p b => if b then clamp01 (r p.1.1 p.1.2) else 1 - clamp01 (r p.1.1 p.1.2) with hf
  have h1 : ∏ i, ∑ b ∈ (univ : Finset Bool), f i b = 1 := by
    apply Finset.prod_eq_one
    intro i _
    simp [hf]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ] at h1
  rw [← h1]
  refine Fintype.sum_equiv (graphEquiv n) _ _ (fun G => ?_)
  unfold edgeWeight
  rw [← Finset.prod_coe_sort]
  refine Finset.prod_congr rfl (fun p _ => ?_)
  simp [hf, graphEquiv]

lemma edgeWeight_nonneg {n : ℕ} (G : SimpleGraph (Fin n)) (r : Fin n → Fin n → ℝ) :
    0 ≤ edgeWeight G r := by
  unfold edgeWeight
  apply Finset.prod_nonneg
  intro p _
  have h0 : 0 ≤ clamp01 (r p.1 p.2) := le_max_left _ _
  have h1 : clamp01 (r p.1 p.2) ≤ 1 := max_le zero_le_one (min_le_left _ _)
  split_ifs <;> linarith

lemma bisections_nonempty (m : ℕ) : (bisections (2 * m)).Nonempty := by
  obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq (s := (univ : Finset (Fin (2 * m))))
    (n := m) (by simp; omega)
  exact ⟨S, by simp [bisections, LPCommunity.MinBisect.IsBisection, hS]⟩

lemma sbmProb_true (m : ℕ) (p q : ℝ) :
    sbmProb (2 * m) p q (fun _ _ => True) = 1 := by
  unfold sbmProb
  simp only [if_true, mul_one, edgeWeight_sum, Finset.sum_const, nsmul_eq_mul]
  have : ((bisections (2 * m)).card : ℝ) ≠ 0 := by
    exact_mod_cast (bisections_nonempty m).card_pos.ne'
  field_simp

lemma sbmProb_mono {n : ℕ} (p q : ℝ) (E F : Finset (Fin n) → SimpleGraph (Fin n) → Prop)
    (h : ∀ V1 ∈ bisections n, ∀ G, E V1 G → F V1 G) :
    sbmProb n p q E ≤ sbmProb n p q F := by
  unfold sbmProb
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro V1 hV1
  apply Finset.sum_le_sum
  intro G _
  apply mul_le_mul_of_nonneg_left _ (edgeWeight_nonneg _ _)
  by_cases hE : E V1 G
  · simp [hE, h V1 hV1 G hE]
  · simp only [hE, if_false]; split_ifs <;> norm_num

lemma sbmProb_le_one (m : ℕ) (p q : ℝ) (E : Finset (Fin (2 * m)) → SimpleGraph (Fin (2 * m)) → Prop) :
    sbmProb (2 * m) p q E ≤ 1 := by
  rw [← sbmProb_true m p q]
  exact sbmProb_mono p q _ _ (fun _ _ _ _ => trivial)

lemma sbmProb_or_le {n : ℕ} (p q : ℝ) (E F : Finset (Fin n) → SimpleGraph (Fin n) → Prop) :
    sbmProb n p q (fun V G => E V G ∨ F V G) ≤ sbmProb n p q E + sbmProb n p q F := by
  unfold sbmProb
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro V1 _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro G _
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (edgeWeight_nonneg _ _)
  split_ifs <;> simp_all

lemma sbmProb_compl {n : ℕ} (p q : ℝ) (E : Finset (Fin n) → SimpleGraph (Fin n) → Prop) :
    sbmProb n p q E + sbmProb n p q (fun V G => ¬ E V G) = sbmProb n p q (fun _ _ => True) := by
  unfold sbmProb
  rw [← mul_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun V1 _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun G _ => ?_)
  by_cases h : E V1 G <;> simp [h]

lemma tendsto_and {p q : ℕ → ℝ}
    (E F : (m : ℕ) → Finset (Fin (2 * m)) → SimpleGraph (Fin (2 * m)) → Prop)
    (hE : Filter.Tendsto (fun m => sbmProb (2 * m) (p m) (q m) (E m)) Filter.atTop (nhds 1))
    (hF : Filter.Tendsto (fun m => sbmProb (2 * m) (p m) (q m) (F m)) Filter.atTop (nhds 1)) :
    Filter.Tendsto (fun m => sbmProb (2 * m) (p m) (q m) (fun V G => E m V G ∧ F m V G))
      Filter.atTop (nhds 1) := by
  have key : ∀ m, sbmProb (2 * m) (p m) (q m) (E m) + sbmProb (2 * m) (p m) (q m) (F m) - 1 ≤
      sbmProb (2 * m) (p m) (q m) (fun V G => E m V G ∧ F m V G) := by
    intro m
    have h1 := sbmProb_compl (p m) (q m) (E m)
    have h2 := sbmProb_compl (p m) (q m) (F m)
    have h3 := sbmProb_compl (p m) (q m) (fun V G => E m V G ∧ F m V G)
    have h4 := sbmProb_or_le (p m) (q m) (fun V G => ¬ E m V G) (fun V G => ¬ F m V G)
    have h5 : sbmProb (2 * m) (p m) (q m) (fun V G => ¬ (E m V G ∧ F m V G)) ≤
        sbmProb (2 * m) (p m) (q m) (fun V G => ¬ E m V G ∨ ¬ F m V G) :=
      sbmProb_mono _ _ _ _ (fun V _ G h => by tauto)
    rw [sbmProb_true] at h1 h2 h3
    linarith
  have hlow : Filter.Tendsto (fun m => sbmProb (2 * m) (p m) (q m) (E m) +
      sbmProb (2 * m) (p m) (q m) (F m) - 1) Filter.atTop (nhds 1) := by
    have := (hE.add hF).sub_const 1
    norm_num at this
    exact this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds key
    (fun m => sbmProb_le_one m _ _ _)

lemma tendsto_of_imp {p q : ℕ → ℝ}
    (E F : (m : ℕ) → Finset (Fin (2 * m)) → SimpleGraph (Fin (2 * m)) → Prop)
    (hE : Filter.Tendsto (fun m => sbmProb (2 * m) (p m) (q m) (E m)) Filter.atTop (nhds 1))
    (hEF : ∀ᶠ m in Filter.atTop, ∀ V1 ∈ bisections (2 * m), ∀ G, E m V1 G → F m V1 G) :
    Filter.Tendsto (fun m => sbmProb (2 * m) (p m) (q m) (F m)) Filter.atTop (nhds 1) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hE tendsto_const_nhds ?_
    (Filter.Eventually.of_forall (fun m => sbmProb_le_one m _ _ _))
  filter_upwards [hEF] with m hm
  exact sbmProb_mono _ _ _ _ hm


section WSec
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def W (a : ι → ℝ) (x : ι → Bool) : ℝ := ∏ i, if x i then a i else 1 - a i

lemma sum_W_mul_prod (a : ι → ℝ) (φ : ι → Bool → ℝ) :
    ∑ x : ι → Bool, W a x * ∏ i, φ i (x i) =
      ∏ i, (a i * φ i true + (1 - a i) * φ i false) := by
  have h := Finset.prod_univ_sum (fun _ : ι => (univ : Finset Bool))
    (fun i b => (if b then a i else 1 - a i) * φ i b)
  rw [Fintype.piFinset_univ] at h
  simp only [W, ← Finset.prod_mul_distrib]
  rw [← h]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  simp [Fintype.sum_bool]

lemma sum_W_indicator {κ : Type*} [Fintype κ] [DecidableEq κ] (a : ι → ℝ) (φ : κ ↪ ι) (y : κ → Bool) :
    ∑ x : ι → Bool, W a x * (if x ∘ φ = y then 1 else 0) = W (a ∘ φ) y := by
  set ψ : ι → Bool → ℝ := fun i b =>
    if h : ∃ k, φ k = i then (if b = y h.choose then 1 else 0) else 1 with hψ
  have hprod : ∀ x : ι → Bool, (if x ∘ φ = y then (1:ℝ) else 0) = ∏ i, ψ i (x i) := by
    intro x
    split_ifs with hxy
    · symm
      apply Finset.prod_eq_one
      intro i _
      by_cases h : ∃ k, φ k = i
      · have hx : x i = y h.choose := by
          rw [← hxy]; simp [h.choose_spec]
        simp [hψ, dif_pos h, hx]
      · simp [hψ, dif_neg h]
    · symm
      have : ∃ k, x (φ k) ≠ y k := by
        by_contra hc
        push Not at hc
        exact hxy (funext hc)
      obtain ⟨k, hk⟩ := this
      apply Finset.prod_eq_zero (Finset.mem_univ (φ k))
      have h : ∃ k', φ k' = φ k := ⟨k, rfl⟩
      have hc : h.choose = k := φ.injective h.choose_spec
      simp only [hψ, dif_pos h]
      rw [if_neg]
      rw [hc]; exact hk
  simp_rw [hprod]
  rw [sum_W_mul_prod]
  unfold W
  rw [← Finset.prod_subset (Finset.subset_univ (univ.map φ))]
  · rw [Finset.prod_map]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    have h : ∃ k', φ k' = φ k := ⟨k, rfl⟩
    have hc : h.choose = k := φ.injective h.choose_spec
    simp only [hψ, dif_pos h, hc, Function.comp_apply]
    cases y k <;> simp
  · intro i _ hi
    have h : ¬ ∃ k, φ k = i := by
      rintro ⟨k, rfl⟩
      exact hi (Finset.mem_map_of_mem _ (mem_univ k))
    simp [hψ, dif_neg h]

lemma sum_W_comp {κ : Type*} [Fintype κ] [DecidableEq κ] (a : ι → ℝ) (φ : κ ↪ ι) (F : (κ → Bool) → ℝ) :
    ∑ x : ι → Bool, W a x * F (x ∘ φ) = ∑ y : κ → Bool, W (a ∘ φ) y * F y := by
  have hF : ∀ x : ι → Bool, F (x ∘ φ) = ∑ y, (if x ∘ φ = y then 1 else 0) * F y := by
    intro x
    simp
  simp_rw [hF, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [← sum_W_indicator a φ y, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun x _ => by ring)

lemma sum_W_congr (P : ι → Prop) (a a' : ι → ℝ) (haa : ∀ i, P i → a i = a' i)
    (g : (ι → Bool) → ℝ) (hg : ∀ x x', (∀ i, P i → x i = x' i) → g x = g x') :
    ∑ x, W a x * g x = ∑ x, W a' x * g x := by
  let φ : {i // P i} ↪ ι := ⟨Subtype.val, Subtype.val_injective⟩
  let ext : ({i // P i} → Bool) → (ι → Bool) := fun y i => if h : P i then y ⟨i, h⟩ else false
  have hgx : ∀ x, g x = (g ∘ ext) (x ∘ φ) := fun x =>
    hg _ _ (fun i hi => by simp [ext, hi, φ])
  have e1 : ∀ b : ι → ℝ, ∑ x, W b x * g x = ∑ x, W b x * (g ∘ ext) (x ∘ φ) := by
    intro b
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← hgx]
  rw [e1 a, e1 a', sum_W_comp, sum_W_comp]
  have : a ∘ φ = a' ∘ φ := funext fun i => haa i.1 i.2
  rw [this]

end WSec

/-- the edge probabilities of `r`, clamped, as a function on pairs. -/
noncomputable def aR {n : ℕ} (r : Fin n → Fin n → ℝ) : {p : Fin n × Fin n // p ∈ pairs n} → ℝ :=
  fun p => clamp01 (r p.1.1 p.1.2)

lemma edgeWeight_eq {n : ℕ} (G : SimpleGraph (Fin n)) (r : Fin n → Fin n → ℝ) :
    edgeWeight G r = W (aR r) (graphEquiv n G) := by
  unfold edgeWeight W
  rw [← Finset.prod_coe_sort]
  refine Finset.prod_congr rfl (fun p _ => ?_)
  simp [aR, graphEquiv]

lemma sum_graph {n : ℕ} (r : Fin n → Fin n → ℝ) (f : SimpleGraph (Fin n) → ℝ) :
    ∑ G, edgeWeight G r * f G = ∑ x, W (aR r) x * f ((graphEquiv n).symm x) := by
  rw [← (graphEquiv n).symm.sum_comp]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [edgeWeight_eq, Equiv.apply_symm_apply]

/-- the complete bipartite graph across the partition `V1, V1ᶜ`. -/
def cross {n : ℕ} (V1 : Finset (Fin n)) : SimpleGraph (Fin n) where
  Adj i j := ¬ LPCommunity.MinBisect.sameSide V1 i j
  symm := ⟨fun i j h h' => h (Iff.symm h')⟩
  loopless := ⟨fun i h => h Iff.rfl⟩

lemma inf_cross_le {n : ℕ} (V1 : Finset (Fin n)) (x x' : {p : Fin n × Fin n // p ∈ pairs n} → Bool)
    (h : ∀ p, ¬ LPCommunity.MinBisect.sameSide V1 p.1.1 p.1.2 → x p = x' p) :
    (graphEquiv n).symm x ⊓ cross V1 ≤ (graphEquiv n).symm x' ⊓ cross V1 := by
  intro i j hij
  obtain ⟨hx, hs⟩ := hij
  refine ⟨?_, hs⟩
  have hs1 : ¬ LPCommunity.MinBisect.sameSide V1 i j := hs
  have hs2 : ¬ LPCommunity.MinBisect.sameSide V1 j i := fun h' => hs1 (Iff.symm h')
  change (∃ h : (i, j) ∈ pairs n, x ⟨(i, j), h⟩ = true) ∨
    (∃ h : (j, i) ∈ pairs n, x ⟨(j, i), h⟩ = true) at hx
  change (∃ h : (i, j) ∈ pairs n, x' ⟨(i, j), h⟩ = true) ∨
    (∃ h : (j, i) ∈ pairs n, x' ⟨(j, i), h⟩ = true)
  rcases hx with ⟨hp, hv⟩ | ⟨hp, hv⟩
  · exact Or.inl ⟨hp, by rw [← h ⟨(i, j), hp⟩ hs1]; exact hv⟩
  · exact Or.inr ⟨hp, by rw [← h ⟨(j, i), hp⟩ hs2]; exact hv⟩

lemma sum_cross_congr {n : ℕ} (V1 : Finset (Fin n)) (r r' : Fin n → Fin n → ℝ)
    (hr : ∀ i j, ¬ LPCommunity.MinBisect.sameSide V1 i j → r i j = r' i j)
    (E : SimpleGraph (Fin n) → Prop) :
    ∑ G, edgeWeight G r * (if E (G ⊓ cross V1) then 1 else 0) =
      ∑ G, edgeWeight G r' * (if E (G ⊓ cross V1) then 1 else 0) := by
  rw [sum_graph r (fun G => if E (G ⊓ cross V1) then 1 else 0),
    sum_graph r' (fun G => if E (G ⊓ cross V1) then 1 else 0)]
  refine sum_W_congr (fun p => ¬ LPCommunity.MinBisect.sameSide V1 p.1.1 p.1.2) _ _ ?_ _ ?_
  · intro p hp
    simp [aR, hr _ _ hp]
  · intro x x' hxx
    have : (graphEquiv n).symm x ⊓ cross V1 = (graphEquiv n).symm x' ⊓ cross V1 :=
      le_antisymm (inf_cross_le V1 x x' hxx)
        (inf_cross_le V1 x' x (fun p hp => (hxx p hp).symm))
    simp only [this]

/-- the pairs map induced by an order embedding. -/
def pairMap {m n : ℕ} (e : Fin m ↪o Fin n) :
    {p : Fin m × Fin m // p ∈ pairs m} ↪ {p : Fin n × Fin n // p ∈ pairs n} where
  toFun p := ⟨(e p.1.1, e p.1.2), by
    have h := p.2
    simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
    exact e.strictMono h⟩
  inj' := by
    intro p p' h
    simp only [Subtype.mk.injEq, Prod.mk.injEq] at h
    apply Subtype.ext
    exact Prod.ext (e.injective h.1) (e.injective h.2)

lemma comap_symm {m n : ℕ} (e : Fin m ↪o Fin n) (x : {p : Fin n × Fin n // p ∈ pairs n} → Bool) :
    ((graphEquiv n).symm x).comap e = (graphEquiv m).symm (x ∘ pairMap e) := by
  apply (graphEquiv m).injective
  rw [Equiv.apply_symm_apply]
  funext p
  have := congrFun ((graphEquiv n).apply_symm_apply x) (pairMap e p)
  show decide _ = x (pairMap e p)
  rw [← this]
  rfl

lemma sum_comap {m n : ℕ} (e : Fin m ↪o Fin n) (r : Fin n → Fin n → ℝ) (p : ℝ)
    (hr : ∀ i j : Fin m, i < j → r (e i) (e j) = p) (f : SimpleGraph (Fin m) → ℝ) :
    ∑ G : SimpleGraph (Fin n), edgeWeight G r * f (G.comap e) =
      ∑ G : SimpleGraph (Fin m), edgeWeight G (fun _ _ => p) * f G := by
  rw [sum_graph r (fun G => f (G.comap e)), sum_graph (fun _ _ => p) f]
  simp_rw [comap_symm]
  rw [sum_W_comp (aR r) (pairMap e) (fun y => f ((graphEquiv m).symm y))]
  have : aR r ∘ pairMap e = aR (fun _ _ => p) := by
    funext q
    have hq : q.1.1 < q.1.2 := by
      have h := q.2
      simpa [pairs] using h
    simp only [Function.comp_apply, aR]
    show clamp01 (r (e q.1.1) (e q.1.2)) = clamp01 p
    rw [hr _ _ hq]
  rw [this]


open LPCommunity.MinBisect

lemma mem_bisections {m : ℕ} (V1 : Finset (Fin (2 * m))) :
    V1 ∈ bisections (2 * m) ↔ V1.card = m := by
  unfold bisections
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, IsBisection]
  omega

lemma card_compl_eq {m : ℕ} (V1 : Finset (Fin (2 * m))) (h : V1.card = m) : V1ᶜ.card = m := by
  rw [Finset.card_compl, Fintype.card_fin]
  omega

/-- an event about the graph induced on the side `S` (of size `m`), read through the increasing
enumeration of `S`. -/
def evIn {m : ℕ} (E : SimpleGraph (Fin m) → Prop) (S : Finset (Fin (2 * m)))
    (G : SimpleGraph (Fin (2 * m))) : Prop :=
  if h : S.card = m then E (G.comap (S.orderEmbOfFin h)) else True

lemma sbmProb_in {m : ℕ} (p q : ℝ) (E : SimpleGraph (Fin m) → Prop)
    (side : Finset (Fin (2 * m)) → Finset (Fin (2 * m)))
    (hside : ∀ V1 ∈ bisections (2 * m), (side V1).card = m ∧
      ∀ i j, i ∈ side V1 → j ∈ side V1 → sameSide V1 i j) :
    sbmProb (2 * m) p q (fun V1 G => evIn E (side V1) G) = erProb m p E := by
  unfold sbmProb erProb
  have hS : ∀ V1 ∈ bisections (2 * m),
      ∑ G : SimpleGraph (Fin (2 * m)), edgeWeight G (fun i j => if sameSide V1 i j then p else q) *
        (if evIn E (side V1) G then 1 else 0) =
      ∑ G : SimpleGraph (Fin m), edgeWeight G (fun _ _ => p) * (if E G then 1 else 0) := by
    intro V1 hV1
    obtain ⟨hc, hss⟩ := hside V1 hV1
    calc ∑ G : SimpleGraph (Fin (2 * m)), edgeWeight G (fun i j => if sameSide V1 i j then p else q) *
          (if evIn E (side V1) G then 1 else 0)
        = ∑ G : SimpleGraph (Fin (2 * m)), edgeWeight G (fun i j => if sameSide V1 i j then p else q) *
          (fun G' => if E G' then (1:ℝ) else 0) (G.comap ((side V1).orderEmbOfFin hc)) := by
          refine Finset.sum_congr rfl (fun G _ => ?_)
          simp only [evIn, dif_pos hc]
      _ = _ := by
          refine sum_comap ((side V1).orderEmbOfFin hc) _ p (fun i j _ => ?_)
            (fun G' => if E G' then (1:ℝ) else 0)
          rw [if_pos (hss _ _ (Finset.orderEmbOfFin_mem _ hc i) (Finset.orderEmbOfFin_mem _ hc j))]
  rw [Finset.sum_congr rfl hS, Finset.sum_const, nsmul_eq_mul]
  have : ((bisections (2 * m)).card : ℝ) ≠ 0 := by
    exact_mod_cast (bisections_nonempty m).card_pos.ne'
  field_simp

lemma sbmProb_cross {n : ℕ} (p q : ℝ) (E : Finset (Fin n) → SimpleGraph (Fin n) → Prop) :
    sbmProb n p q (fun V1 G => E V1 (G ⊓ cross V1)) = sbmProb n 0 q (fun V1 G => E V1 (G ⊓ cross V1)) := by
  unfold sbmProb
  congr 1
  refine Finset.sum_congr rfl (fun V1 _ => ?_)
  exact sum_cross_congr V1 _ _ (fun i j h => by simp only [if_neg h]) (E V1)

lemma deg_side {m n : ℕ} (V1 : Finset (Fin n)) (e : Fin m ↪ Fin n) (H' : SimpleGraph (Fin m))
    (K : SimpleGraph (Fin n)) (hS : ∀ i u, sameSide V1 (e i) u ↔ ∃ j, e j = u)
    (hK : ∀ i u, ¬ K.Adj (e i) u) (i : Fin m) :
    inDeg (H'.map e ⊔ K) V1 (e i) = H'.degree i := by
  unfold inDeg
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← Finset.card_map e]
  congr 1
  ext u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    SimpleGraph.mem_neighborFinset, SimpleGraph.sup_adj, SimpleGraph.map_adj]
  constructor
  · rintro ⟨(⟨a, b, hab, ha, rfl⟩ | hk), -⟩
    · exact ⟨b, by rwa [e.injective ha] at hab, rfl⟩
    · exact absurd hk (hK i u)
  · rintro ⟨b, hb, rfl⟩
    exact ⟨Or.inl ⟨i, b, hb, rfl, rfl⟩, (hS i (e b)).2 ⟨b, rfl⟩⟩

lemma det {m : ℕ} (G : SimpleGraph (Fin (2 * m))) (V1 : Finset (Fin (2 * m))) (hV1 : V1.card = m)
    (din dout : ℕ) (H0 : SimpleGraph (Fin (2 * m))) (hH0a : G ⊓ cross V1 ≤ H0)
    (hH0b : ∀ i j, H0.Adj i j → ¬ sameSide V1 i j) (hH0c : ∀ v, H0.degree v = dout)
    (H1 H2 : SimpleGraph (Fin m)) (hH1 : H1 ≤ G.comap (V1.orderEmbOfFin hV1))
    (hd1 : ∀ v, H1.degree v = din)
    (hH2 : H2 ≤ G.comap (V1ᶜ.orderEmbOfFin (card_compl_eq V1 hV1))) (hd2 : ∀ v, H2.degree v = din)
    (h : (din : ℝ) - dout ≥ ((2 * m : ℕ) : ℝ) / 4) : LPCommunity.LPRecovery.LPRecovers G V1 := by
  set e1 := V1.orderEmbOfFin hV1 with he1
  set e2 := V1ᶜ.orderEmbOfFin (card_compl_eq V1 hV1) with he2
  have m1 : ∀ i, e1 i ∈ V1 := fun i => Finset.orderEmbOfFin_mem _ hV1 i
  have m2 : ∀ i, e2 i ∉ V1 := fun i => by
    have := Finset.orderEmbOfFin_mem _ (card_compl_eq V1 hV1) i
    exact Finset.mem_compl.1 this
  have r1 : ∀ v ∈ V1, ∃ i, e1 i = v := by
    intro v hv
    have : v ∈ Set.range e1 := by rw [he1, Finset.range_orderEmbOfFin]; exact hv
    exact this
  have r2 : ∀ v, v ∉ V1 → ∃ i, e2 i = v := by
    intro v hv
    have : v ∈ Set.range e2 := by
      rw [he2, Finset.range_orderEmbOfFin]; simpa using hv
    exact this
  apply LPCommunity.LPRecovery.theorem_4 G V1 (by unfold IsBisection; omega) din dout ?_ ?_ h
  · refine ⟨H1.map e1.toEmbedding ⊔ H2.map e2.toEmbedding, ?_, ?_⟩
    · intro i j hij
      rw [SimpleGraph.sup_adj, SimpleGraph.map_adj, SimpleGraph.map_adj] at hij
      rcases hij with ⟨a, b, hab, rfl, rfl⟩ | ⟨a, b, hab, rfl, rfl⟩
      · refine ⟨?_, hH1 hab⟩
        show (e1 a ∈ V1 ↔ e1 b ∈ V1)
        exact iff_of_true (m1 a) (m1 b)
      · refine ⟨?_, hH2 hab⟩
        show (e2 a ∈ V1 ↔ e2 b ∈ V1)
        exact iff_of_false (m2 a) (m2 b)
    · intro v
      by_cases hv : v ∈ V1
      · obtain ⟨i, rfl⟩ := r1 v hv
        have := deg_side V1 e1.toEmbedding H1 (H2.map e2.toEmbedding) ?_ ?_ i
        · rw [← hd1 i]; exact this
        · intro i u
          show (e1 i ∈ V1 ↔ u ∈ V1) ↔ ∃ j, e1 j = u
          constructor
          · intro h'; exact r1 u (h'.1 (m1 i))
          · rintro ⟨j, rfl⟩; exact iff_of_true (m1 i) (m1 j)
        · intro i u hk
          rw [SimpleGraph.map_adj] at hk
          obtain ⟨a, b, -, ha, -⟩ := hk
          exact m2 a (by rw [show e2 a = e1 i from ha]; exact m1 i)
      · obtain ⟨i, rfl⟩ := r2 v hv
        have := deg_side V1 e2.toEmbedding H2 (H1.map e1.toEmbedding) ?_ ?_ i
        · rw [sup_comm, ← hd2 i]; exact this
        · intro i u
          show (e2 i ∈ V1 ↔ u ∈ V1) ↔ ∃ j, e2 j = u
          constructor
          · intro h'; exact r2 u (fun hu => m2 i (h'.2 hu))
          · rintro ⟨j, rfl⟩; exact iff_of_false (m2 i) (m2 j)
        · intro i u hk
          rw [SimpleGraph.map_adj] at hk
          obtain ⟨a, b, -, ha, -⟩ := hk
          exact m2 i (by rw [show e2 i = e1 a from ha.symm]; exact m1 a)
  · refine ⟨H0, hH0b, fun i j hG hs => hH0a ⟨hG, hs⟩, fun v => ?_⟩
    unfold outDeg
    rw [← hH0c v, ← SimpleGraph.card_neighborFinset_eq_degree]
    congr 1
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.mem_neighborFinset]
    exact ⟨fun h' => h'.1, fun h' => ⟨h', hH0b _ _ h'⟩⟩

lemma sqrt_small (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, Real.sqrt (m * Real.log m) ≤ δ * m := by
  have h1 := Real.isLittleO_log_id_atTop.bound (pow_pos hδ 2)
  have h2 := tendsto_natCast_atTop_atTop.eventually h1
  filter_upwards [h2] with m hm
  simp only [Real.norm_eq_abs, id] at hm
  have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
  rw [abs_of_nonneg hm0] at hm
  have hlog : Real.log m ≤ δ ^ 2 * m := le_trans (le_abs_self _) hm
  have hml : (m : ℝ) * Real.log m ≤ m * (δ ^ 2 * m) := mul_le_mul_of_nonneg_left hlog hm0
  calc Real.sqrt (m * Real.log m) ≤ Real.sqrt ((δ * m) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    _ = δ * m := Real.sqrt_sq (by positivity)

end LP5Aux

open LP5Aux LPCommunity.SBMRecovery in
theorem solution (p q : ℝ) (hq : 0 < q) (hqp : q < p) (hp : p < 1) (h : p - q > 1 / 2) :
    Tendsto (fun m : ℕ => sbmProb (2 * m) p q (fun V1 G => LPCommunity.LPRecovery.LPRecovers G V1))
      atTop (𝓝 1) := by
  obtain ⟨C2, hC2, h3⟩ := LPCommunity.SBMRecovery.proposition_3
  obtain ⟨C1, hC1, h4⟩ := LPCommunity.SBMRecovery.proposition_4
  have h3' := h3 q hq (by linarith)
  have h4' := h4 p (by linarith) hp
  let E3 : (m : ℕ) → Finset (Fin (2 * m)) → SimpleGraph (Fin (2 * m)) → Prop := fun m V1 G =>
    ∃ H : SimpleGraph (Fin (2 * m)), G ≤ H ∧
      (∀ i j, H.Adj i j → ¬ LPCommunity.MinBisect.sameSide V1 i j) ∧
      ∀ v, (H.degree v : ℤ) = ⌊q * m + C2 * Real.sqrt (m * Real.log m)⌋
  let E4 : (n : ℕ) → SimpleGraph (Fin n) → Prop := fun n G =>
    ∃ H : SimpleGraph (Fin n), H ≤ G ∧
      ∀ v, (H.degree v : ℤ) = 2 * ⌈(p * n - C1 * Real.sqrt (n * Real.log n)) / 2⌉
  have hA : Tendsto (fun m => sbmProb (2 * m) p q (fun V1 G => E3 m V1 (G ⊓ cross V1)))
      atTop (𝓝 1) := by
    have e : (fun m => sbmProb (2 * m) p q (fun V1 G => E3 m V1 (G ⊓ cross V1))) =
        (fun m => sbmProb (2 * m) 0 q (fun V1 G => E3 m V1 (G ⊓ cross V1))) :=
      funext fun m => sbmProb_cross p q _
    rw [e]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le h3' tendsto_const_nhds
      (fun m => sbmProb_mono 0 q (E3 m) _ (fun V1 _ G hG => ?_)) (fun m => sbmProb_le_one m _ _ _)
    obtain ⟨H, hGH, hH⟩ := hG
    exact ⟨H, le_trans inf_le_left hGH, hH⟩
  have hB1 : Tendsto (fun m => sbmProb (2 * m) p q (fun V1 G => evIn (E4 m) V1 G))
      atTop (𝓝 1) := by
    have e : (fun m => sbmProb (2 * m) p q (fun V1 G => evIn (E4 m) V1 G)) =
        (fun m => erProb m p (E4 m)) :=
      funext fun m => sbmProb_in p q (E4 m) id (fun V1 hV1 =>
        ⟨(mem_bisections V1).1 hV1, fun i j hi hj => iff_of_true hi hj⟩)
    rw [e]
    exact h4'
  have hB2 : Tendsto (fun m => sbmProb (2 * m) p q (fun V1 G => evIn (E4 m) V1ᶜ G))
      atTop (𝓝 1) := by
    have e : (fun m => sbmProb (2 * m) p q (fun V1 G => evIn (E4 m) V1ᶜ G)) =
        (fun m => erProb m p (E4 m)) :=
      funext fun m => sbmProb_in p q (E4 m) (fun V1 => V1ᶜ) (fun V1 hV1 =>
        ⟨card_compl_eq V1 ((mem_bisections V1).1 hV1), fun i j hi hj =>
          iff_of_false (by simpa using hi) (by simpa using hj)⟩)
    rw [e]
    exact h4'
  have hAll := tendsto_and (p := fun _ => p) (q := fun _ => q)
    (fun m V1 G => E3 m V1 (G ⊓ cross V1))
    (fun m V1 G => evIn (E4 m) V1 G ∧ evIn (E4 m) V1ᶜ G) hA
    (tendsto_and (p := fun _ => p) (q := fun _ => q) (fun m V1 G => evIn (E4 m) V1 G)
      (fun m V1 G => evIn (E4 m) V1ᶜ G) hB1 hB2)
  have hCpos : 0 < C1 + C2 := by linarith
  have hδ : 0 < (p - q - 1 / 2) / (C1 + C2) := div_pos (by linarith) hCpos
  refine tendsto_of_imp (p := fun _ => p) (q := fun _ => q) _
    (fun m V1 G => LPCommunity.LPRecovery.LPRecovers G V1) hAll ?_
  filter_upwards [sqrt_small _ hδ] with m hm
  intro V1 hV1 G hG
  obtain ⟨hGA, hG1, hG2⟩ := hG
  have hc : V1.card = m := (mem_bisections V1).1 hV1
  obtain ⟨H0, hH0a, hH0b, hH0c⟩ := hGA
  simp only [evIn, dif_pos hc, dif_pos (card_compl_eq V1 hc)] at hG1 hG2
  obtain ⟨H1, hH1, hd1⟩ := hG1
  obtain ⟨H2, hH2, hd2⟩ := hG2
  set s := Real.sqrt (m * Real.log m) with hs
  set Z : ℤ := 2 * ⌈(p * m - C1 * s) / 2⌉ with hZ
  set Y : ℤ := ⌊q * m + C2 * s⌋ with hY
  refine det G V1 hc Z.toNat Y.toNat H0 hH0a hH0b (fun v => by have := hH0c v; omega)
    H1 H2 hH1 (fun v => by have := hd1 v; omega) hH2 (fun v => by have := hd2 v; omega) ?_
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
  have hZle : (Z : ℝ) ≤ ((Z.toNat : ℕ) : ℝ) := by exact_mod_cast Int.self_le_toNat Z
  have hZ2 : p * m - C1 * s ≤ (Z : ℝ) := by
    rw [hZ]; push_cast
    linarith [Int.le_ceil ((p * m - C1 * s) / 2)]
  have hY0 : 0 ≤ Y := Int.floor_nonneg.2 (by positivity)
  have hYeq : ((Y.toNat : ℕ) : ℝ) = (Y : ℝ) := by
    have : ((Y.toNat : ℤ)) = Y := Int.toNat_of_nonneg hY0
    exact_mod_cast this
  have hY2 : (Y : ℝ) ≤ q * m + C2 * s := Int.floor_le _
  have key : (C1 + C2) * s ≤ (p - q - 1 / 2) * m := by
    have := mul_le_mul_of_nonneg_left hm (le_of_lt hCpos)
    rwa [show (C1 + C2) * ((p - q - 1 / 2) / (C1 + C2) * m) = (p - q - 1 / 2) * m by
      field_simp] at this
  push_cast
  linarith
