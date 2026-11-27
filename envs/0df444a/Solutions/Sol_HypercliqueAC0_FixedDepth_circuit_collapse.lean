-- Prove2me | solution 1 for HypercliqueAC0.FixedDepth.circuit_collapse
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T01:24:24.132159+00:00
-- url     : https://prove2.me/submissions/ae6cc650-88f8-4de1-beac-61b92381a6f3

import Mathlib
import Definitions.Def_HypercliqueAC0_FixedDepth_Planting
import Definitions.Def_HypercliqueAC0_FixedDepth_Switching
import Theorems.Thm_HypercliqueAC0_FixedDepth_switching_lemma_dnf

noncomputable section
namespace HypercliqueAC0.FixedDepth
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators

/-! ### Decision trees -/

theorem CC_dt_mono {X : Type} {t : ℕ} {f : (X → Bool) → Bool} (hf : DTDepthLE t f) :
    ∀ {t'}, t ≤ t' → DTDepthLE t' f := by
  induction hf with
  | const t b => intro t' _; exact DTDepthLE.const t' b
  | query t i f h0 h1 ih0 ih1 =>
    intro t' ht
    obtain ⟨s, rfl⟩ : ∃ s, t' = s + 1 := ⟨t' - 1, by omega⟩
    exact DTDepthLE.query s i f (ih0 (by omega)) (ih1 (by omega))

theorem CC_dt_not {X : Type} {t : ℕ} {f : (X → Bool) → Bool} (hf : DTDepthLE t f) :
    DTDepthLE t (fun x => !f x) := by
  induction hf with
  | const t b => exact DTDepthLE.const t (!b)
  | query t i f h0 h1 ih0 ih1 => exact DTDepthLE.query t i _ ih0 ih1

theorem CC_dt_not_iff {X : Type} {t : ℕ} {f : (X → Bool) → Bool} :
    DTDepthLE t (fun x => !f x) ↔ DTDepthLE t f := by
  constructor
  · intro h
    have := CC_dt_not h
    simpa using this
  · exact CC_dt_not

theorem CC_dt_congr {X : Type} {t : ℕ} {f g : (X → Bool) → Bool} (hf : DTDepthLE t f)
    (h : ∀ x, f x = g x) : DTDepthLE t g := by
  have : f = g := funext h
  exact this ▸ hf

theorem CC_dt_restrict {X : Type} {t : ℕ} {f : (X → Bool) → Bool} (hf : DTDepthLE t f)
    (ρ : X → Option Bool) : DTDepthLE t (restrictFn ρ f) := by
  induction hf with
  | const t b => exact DTDepthLE.const t b
  | query t i f h0 h1 ih0 ih1 =>
    cases hρ : ρ i with
    | none =>
      refine DTDepthLE.query t i _ (CC_dt_congr ih0 ?_) (CC_dt_congr ih1 ?_)
      all_goals
        intro x
        simp only [restrictFn]
        congr 1
        funext e
        by_cases he : e = i
        · subst he; simp [hρ]
        · simp [Function.update_of_ne he]
    | some c =>
      have key : ∀ x, restrictFn ρ (fun x => f (Function.update x i c)) x = restrictFn ρ f x := by
        intro x
        simp only [restrictFn]
        congr 1
        funext e
        by_cases he : e = i
        · subst he; simp [hρ]
        · simp [Function.update_of_ne he]
      cases c
      · exact CC_dt_mono (CC_dt_congr ih0 key) (by omega)
      · exact CC_dt_mono (CC_dt_congr ih1 key) (by omega)

/-! ### DNFs -/

theorem CC_termValue_insert {X : Type} (l : X × Bool) (T : Finset (X × Bool)) (x : X → Bool) :
    termValue (insert l T) x = (decide (x l.1 = l.2) && termValue T x) := by
  simp [termValue]

theorem CC_dt_dnf {X : Type} {t : ℕ} {f : (X → Bool) → Bool} (hf : DTDepthLE t f) :
    ∃ F : Finset (Finset (X × Bool)), (∀ T ∈ F, T.card ≤ t) ∧ ∀ x, f x = dnfValue F x := by
  induction hf with
  | const t b =>
    cases b
    · exact ⟨∅, by simp, by simp [dnfValue]⟩
    · refine ⟨{∅}, by simp, ?_⟩
      intro x; simp [dnfValue, termValue]
  | query t i f h0 h1 ih0 ih1 =>
    obtain ⟨F0, hF0w, hF0⟩ := ih0
    obtain ⟨F1, hF1w, hF1⟩ := ih1
    refine ⟨F0.image (insert (i, false)) ∪ F1.image (insert (i, true)), ?_, ?_⟩
    · intro T hT
      simp only [Finset.mem_union, Finset.mem_image] at hT
      rcases hT with ⟨T', hT', rfl⟩ | ⟨T', hT', rfl⟩
      · exact (Finset.card_insert_le _ _).trans (by have := hF0w T' hT'; omega)
      · exact (Finset.card_insert_le _ _).trans (by have := hF1w T' hT'; omega)
    · intro x
      have e0 : f (Function.update x i false) = dnfValue F0 x := hF0 x
      have e1 : f (Function.update x i true) = dnfValue F1 x := hF1 x
      cases hx : x i
      · have : Function.update x i false = x := by rw [← hx]; simp
        rw [this] at e0
        rw [e0]
        simp only [dnfValue, Finset.mem_union, Finset.mem_image]
        simp only [decide_eq_decide]
        constructor
        · rintro ⟨T, hT, hv⟩
          exact ⟨_, Or.inl ⟨T, hT, rfl⟩, by rw [CC_termValue_insert]; simp [hx, hv]⟩
        · rintro ⟨T, (⟨T', hT', rfl⟩ | ⟨T', hT', rfl⟩), hv⟩
          · rw [CC_termValue_insert] at hv; simp at hv; exact ⟨T', hT', hv.2⟩
          · rw [CC_termValue_insert] at hv; simp [hx] at hv
      · have : Function.update x i true = x := by rw [← hx]; simp
        rw [this] at e1
        rw [e1]
        simp only [dnfValue, Finset.mem_union, Finset.mem_image]
        simp only [decide_eq_decide]
        constructor
        · rintro ⟨T, hT, hv⟩
          exact ⟨_, Or.inr ⟨T, hT, rfl⟩, by rw [CC_termValue_insert]; simp [hx, hv]⟩
        · rintro ⟨T, (⟨T', hT', rfl⟩ | ⟨T', hT', rfl⟩), hv⟩
          · rw [CC_termValue_insert] at hv; simp [hx] at hv
          · rw [CC_termValue_insert] at hv; simp at hv; exact ⟨T', hT', hv.2⟩

theorem CC_any_dnf {X α : Type} {t : ℕ} (φ : α → (X → Bool) → Bool) :
    ∀ l : List α, (∀ a ∈ l, DTDepthLE t (φ a)) →
    ∃ F : Finset (Finset (X × Bool)), (∀ T ∈ F, T.card ≤ t) ∧
      ∀ x, l.any (fun a => φ a x) = dnfValue F x := by
  intro l
  induction l with
  | nil => intro _; exact ⟨∅, by simp, by simp [dnfValue]⟩
  | cons a l ih =>
    intro hl
    obtain ⟨F, hFw, hF⟩ := ih (fun b hb => hl b (List.mem_cons_of_mem _ hb))
    obtain ⟨G, hGw, hG⟩ := CC_dt_dnf (hl a List.mem_cons_self)
    refine ⟨G ∪ F, ?_, ?_⟩
    · intro T hT
      rcases Finset.mem_union.1 hT with h | h
      · exact hGw T h
      · exact hFw T h
    · intro x
      rw [List.any_cons, hF x, hG x]
      simp only [dnfValue, Finset.mem_union]
      apply Bool.eq_iff_iff.2
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      constructor
      · rintro (⟨T, hT, h⟩ | ⟨T, hT, h⟩)
        · exact ⟨T, Or.inl hT, h⟩
        · exact ⟨T, Or.inr hT, h⟩
      · rintro ⟨T, (hT | hT), h⟩
        · exact Or.inl ⟨T, hT, h⟩
        · exact Or.inr ⟨T, hT, h⟩

/-! ### Restriction probabilities -/

/-- Composition of restrictions: first `ρ1`, then `ρ2` on the remaining stars. -/
def CC_or {X : Type} (ρ1 ρ2 : X → Option Bool) : X → Option Bool := fun e => (ρ1 e).or (ρ2 e)

theorem CC_restrict_comp {X : Type} (ρ1 ρ2 : X → Option Bool) (f : (X → Bool) → Bool) :
    restrictFn ρ2 (restrictFn ρ1 f) = restrictFn (CC_or ρ1 ρ2) f := by
  funext x
  simp only [restrictFn, CC_or]
  congr 1; funext e
  cases ρ1 e <;> rfl

theorem CC_starWeight_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (z : Option Bool) :
    0 ≤ starWeight p z := by
  cases z <;> simp [starWeight] <;> linarith

theorem CC_weight_nonneg {X : Type} [Fintype X] {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (ρ : X → Option Bool) : 0 ≤ restrictionWeight p ρ :=
  Finset.prod_nonneg fun _ _ => CC_starWeight_nonneg h0 h1 _

theorem CC_weight_sum {X : Type} [Fintype X] (p : ℝ) :
    ∑ ρ : X → Option Bool, restrictionWeight p ρ = 1 := by
  unfold restrictionWeight
  rw [← Fintype.prod_sum]
  have : ∑ z : Option Bool, starWeight p z = 1 := by
    simp [Fintype.sum_option, starWeight]; ring
  rw [this, Finset.prod_const_one]

theorem CC_push {X : Type} [Fintype X] (p1 p2 : ℝ) (G : (X → Option Bool) → ℝ) :
    ∑ ρ, restrictionWeight (p1 * p2) ρ * G ρ =
      ∑ ρ1, ∑ ρ2, restrictionWeight p1 ρ1 * restrictionWeight p2 ρ2 * G (CC_or ρ1 ρ2) := by
  have hc : ∀ z : Option Bool, starWeight (p1 * p2) z =
      ∑ uv : Option Bool × Option Bool,
        if uv.1.or uv.2 = z then starWeight p1 uv.1 * starWeight p2 uv.2 else 0 := by
    intro z
    rw [Fintype.sum_prod_type]
    rcases z with _ | b
    · simp [Fintype.sum_option, starWeight]
    · cases b <;> simp [Fintype.sum_option, starWeight] <;> ring
  calc ∑ ρ, restrictionWeight (p1 * p2) ρ * G ρ
      = ∑ ρ, ∑ π : X → Option Bool × Option Bool,
          (if (fun e => (π e).1.or (π e).2) = ρ then
            (∏ e, starWeight p1 (π e).1) * (∏ e, starWeight p2 (π e).2) * G ρ else 0) := by
        refine Finset.sum_congr rfl fun ρ _ => ?_
        simp only [restrictionWeight, hc]
        rw [Fintype.prod_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun π _ => ?_
        by_cases h : (fun e => (π e).1.or (π e).2) = ρ
        · rw [if_pos h, ← Finset.prod_mul_distrib]
          congr 1
          refine Finset.prod_congr rfl fun e _ => ?_
          rw [if_pos (congrFun h e)]
        · rw [if_neg h]
          obtain ⟨e, he⟩ : ∃ e, (π e).1.or (π e).2 ≠ ρ e := by
            by_contra hh; push Not at hh; exact h (funext hh)
          rw [Finset.prod_eq_zero (Finset.mem_univ e) (if_neg he), zero_mul]
    _ = ∑ π : X → Option Bool × Option Bool, (∏ e, starWeight p1 (π e).1) *
          (∏ e, starWeight p2 (π e).2) * G (fun e => (π e).1.or (π e).2) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun π _ => ?_
        rw [Finset.sum_ite_eq]; simp
    _ = _ := by
        rw [← Fintype.sum_prod_type']
        exact Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow X _ _) _ _ (fun π => rfl)

theorem CC_prob_eq {X : Type} [Fintype X] (p : ℝ) (E : (X → Option Bool) → Prop) :
    restrictionProb p E = ∑ ρ, restrictionWeight p ρ * (if E ρ then 1 else 0) := by
  unfold restrictionProb
  refine Finset.sum_congr rfl fun ρ _ => ?_
  split_ifs <;> simp

theorem CC_prob_mono {X : Type} [Fintype X] {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)
    {E E' : (X → Option Bool) → Prop} (h : ∀ ρ, E ρ → E' ρ) :
    restrictionProb p E ≤ restrictionProb p E' := by
  unfold restrictionProb
  refine Finset.sum_le_sum fun ρ _ => ?_
  by_cases hE : E ρ
  · rw [if_pos hE, if_pos (h ρ hE)]
  · rw [if_neg hE]
    split_ifs
    · exact CC_weight_nonneg h0 h1 ρ
    · exact le_rfl

theorem CC_step {X ι : Type} [Fintype X] {q p c : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hc : 0 ≤ c)
    (A B : (X → Option Bool) → Prop) (S : Finset ι)
    (E : ι → (X → Option Bool) → (X → Option Bool) → Prop)
    (hcover : ∀ ρA ρB, B (CC_or ρA ρB) → A ρA ∨ ∃ k ∈ S, E k ρA ρB)
    (hsw : ∀ ρA, ¬ A ρA → ∀ k ∈ S, restrictionProb p (E k ρA) ≤ c) :
    restrictionProb (q * p) B ≤ restrictionProb q A + S.card * c := by
  have hρA : ∀ ρA, ∑ ρB, restrictionWeight q ρA * restrictionWeight p ρB *
      (if B (CC_or ρA ρB) then (1:ℝ) else 0) ≤
      restrictionWeight q ρA * (if A ρA then 1 else 0) + S.card * c * restrictionWeight q ρA := by
    intro ρA
    have hWq := CC_weight_nonneg hq0 hq1 ρA
    by_cases hA : A ρA
    · calc _ ≤ ∑ ρB, restrictionWeight q ρA * restrictionWeight p ρB := by
            refine Finset.sum_le_sum fun ρB _ => ?_
            refine mul_le_of_le_one_right
              (mul_nonneg hWq (CC_weight_nonneg hp0 hp1 ρB)) ?_
            split_ifs <;> norm_num
        _ = restrictionWeight q ρA := by rw [← Finset.mul_sum, CC_weight_sum, mul_one]
        _ ≤ _ := by
            rw [if_pos hA, mul_one]
            have := mul_nonneg (mul_nonneg (Nat.cast_nonneg S.card) hc) hWq
            linarith
    · have hpt : ∀ ρB, (if B (CC_or ρA ρB) then (1:ℝ) else 0) ≤
          ∑ k ∈ S, (if E k ρA ρB then (1:ℝ) else 0) := by
        intro ρB
        by_cases hB : B (CC_or ρA ρB)
        · rw [if_pos hB]
          rcases hcover ρA ρB hB with hA' | ⟨k, hk, hE⟩
          · exact absurd hA' hA
          · have := Finset.single_le_sum (f := fun k => (if E k ρA ρB then (1:ℝ) else 0))
              (fun k _ => by split_ifs <;> norm_num) hk
            simpa [hE] using this
        · rw [if_neg hB]
          exact Finset.sum_nonneg fun k _ => by split_ifs <;> norm_num
      calc _ ≤ ∑ ρB, ∑ k ∈ S, restrictionWeight q ρA *
              (restrictionWeight p ρB * (if E k ρA ρB then (1:ℝ) else 0)) := by
            refine Finset.sum_le_sum fun ρB _ => ?_
            rw [← Finset.mul_sum, ← Finset.mul_sum, mul_assoc]
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (hpt ρB) (CC_weight_nonneg hp0 hp1 ρB)) hWq
        _ = ∑ k ∈ S, restrictionWeight q ρA * restrictionProb p (E k ρA) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [← Finset.mul_sum, CC_prob_eq]
        _ ≤ ∑ k ∈ S, restrictionWeight q ρA * c :=
            Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left (hsw ρA hA k hk) hWq
        _ = _ := by
            rw [Finset.sum_const, if_neg hA, nsmul_eq_mul]; ring
  rw [CC_prob_eq, CC_push]
  calc _ ≤ ∑ ρA, (restrictionWeight q ρA * (if A ρA then 1 else 0) +
          S.card * c * restrictionWeight q ρA) := Finset.sum_le_sum fun ρA _ => hρA ρA
    _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, CC_weight_sum, CC_prob_eq]; ring

/-! ### Folds defining gate values and depths -/

theorem CC_fold_prefix {α β : Type} (F : List β → α → β) :
    ∀ (l : List α) (init : List β), init <+: l.foldl (fun acc g => acc ++ [F acc g]) init := by
  intro l
  induction l with
  | nil => intro init; exact List.prefix_refl _
  | cons a l ih =>
    intro init
    rw [List.foldl_cons]
    exact (List.prefix_append _ _).trans (ih _)

theorem CC_fold_length {α β : Type} (F : List β → α → β) :
    ∀ (l : List α) (init : List β),
      (l.foldl (fun acc g => acc ++ [F acc g]) init).length = init.length + l.length := by
  intro l
  induction l with
  | nil => intro init; simp
  | cons a l ih =>
    intro init
    rw [List.foldl_cons, ih]; simp; omega

theorem CC_fold_get {α β : Type} (F : List β → α → β) (l : List α) (k : ℕ) (hk : k < l.length)
    (d : β) :
    (l.foldl (fun acc g => acc ++ [F acc g]) []).getD k d =
      F ((l.foldl (fun acc g => acc ++ [F acc g]) []).take k) l[k] := by
  set L := l.foldl (fun acc g => acc ++ [F acc g]) [] with hL
  have hsplit : ∀ m, m ≤ l.length →
      (l.take m).foldl (fun acc g => acc ++ [F acc g]) [] = L.take m := by
    intro m hm
    have hp := CC_fold_prefix F (l.drop m) ((l.take m).foldl (fun acc g => acc ++ [F acc g]) [])
    rw [← List.foldl_append, List.take_append_drop] at hp
    have hlen := CC_fold_length F (l.take m) []
    rw [List.prefix_iff_eq_take] at hp
    rw [hp, hlen]
    simp [List.length_take, Nat.min_eq_left hm]
    rfl
  have h1 := hsplit (k + 1) hk
  rw [← List.take_concat_get' l k hk, List.foldl_append, hsplit k hk.le] at h1
  simp only [List.foldl_cons, List.foldl_nil] at h1
  have hlenL : L.length = l.length := by rw [hL, CC_fold_length]; simp
  have : L.getD k d = (L.take (k + 1)).getD k d := by
    simp [List.getD_eq_getElem?_getD]
  rw [this, ← h1]
  have hlenk : (L.take k).length = k := by simp [List.length_take]; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlenk]
  simp

/-! ### Circuit facts -/

theorem CC_getD_take {β : Type} (L : List β) (k i : ℕ) (hi : i < k) (d : β) :
    (L.take k).getD i d = L.getD i d := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem CC_all_congr {α : Type} (l : List α) (f g : α → Bool) (h : ∀ a ∈ l, f a = g a) :
    l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons]
    rw [h a List.mem_cons_self, ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem CC_any_congr {α : Type} (l : List α) (f g : α → Bool) (h : ∀ a ∈ l, f a = g a) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons]
    rw [h a List.mem_cons_self, ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem CC_gateValues_get {X : Type} (C : MantriCVQ.ACCircuit X) (x : X → Bool) (k : ℕ)
    (hk : k < C.gates.length) :
    (gateValues C x).getD k false =
      if C.gates[k].isAnd then C.gates[k].inputs.all (MantriCVQ.Src.eval x (gateValues C x))
      else C.gates[k].inputs.any (MantriCVQ.Src.eval x (gateValues C x)) := by
  have h := CC_fold_get (fun vals (g : MantriCVQ.ACGate X) => if g.isAnd then
      g.inputs.all (MantriCVQ.Src.eval x vals) else g.inputs.any (MantriCVQ.Src.eval x vals))
    C.gates k hk false
  change (gateValues C x).getD k false = (if C.gates[k].isAnd then
      C.gates[k].inputs.all (MantriCVQ.Src.eval x ((gateValues C x).take k)) else
      C.gates[k].inputs.any (MantriCVQ.Src.eval x ((gateValues C x).take k))) at h
  rw [h]
  have hc : ∀ s ∈ C.gates[k].inputs, MantriCVQ.Src.eval x ((gateValues C x).take k) s =
      MantriCVQ.Src.eval x (gateValues C x) s := by
    intro s hs
    cases s with
    | lit v b => rfl
    | const b => rfl
    | gate i => exact CC_getD_take _ k i (C.wf k hk _ hs i rfl) false
  rw [CC_all_congr _ _ _ hc, CC_any_congr _ _ _ hc]

theorem CC_le_foldr_max (l : List ℕ) (a : ℕ) (ha : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 ha with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem CC_gateDepths_get {X : Type} (C : MantriCVQ.ACCircuit X) (k : ℕ)
    (hk : k < C.gates.length) :
    (gateDepths C).getD k 0 =
      1 + (C.gates[k].inputs.map (MantriCVQ.Src.depth (gateDepths C))).foldr max 0 := by
  have h := CC_fold_get (fun ds (g : MantriCVQ.ACGate X) =>
      1 + (g.inputs.map (MantriCVQ.Src.depth ds)).foldr max 0) C.gates k hk 0
  change (gateDepths C).getD k 0 = 1 + (C.gates[k].inputs.map
      (MantriCVQ.Src.depth ((gateDepths C).take k))).foldr max 0 at h
  rw [h]
  congr 2
  refine List.map_congr_left fun s hs => ?_
  cases s with
  | lit v b => rfl
  | const b => rfl
  | gate i => exact CC_getD_take _ k i (C.wf k hk _ hs i rfl) 0

theorem CC_gateDepth_pos {X : Type} (C : MantriCVQ.ACCircuit X) (k : Fin C.gates.length) :
    1 ≤ gateDepth C k := by
  unfold gateDepth
  rw [CC_gateDepths_get C k.val k.isLt]
  omega

theorem CC_gateDepth_lt {X : Type} (C : MantriCVQ.ACCircuit X) (k : Fin C.gates.length)
    (i : ℕ) (hs : MantriCVQ.Src.gate i ∈ C.gates[k.val].inputs) (hi : i < C.gates.length) :
    gateDepth C ⟨i, hi⟩ < gateDepth C k := by
  show (gateDepths C).getD i 0 < (gateDepths C).getD k.val 0
  rw [CC_gateDepths_get C k.val k.isLt]
  have := CC_le_foldr_max _ _ (List.mem_map_of_mem (f := MantriCVQ.Src.depth (gateDepths C)) hs)
  simp only [MantriCVQ.Src.depth] at this
  omega

theorem CC_dt_lit {X : Type} (v : X) (b : Bool) : DTDepthLE 1 (fun x : X → Bool => x v == b) :=
  DTDepthLE.query 0 v _ (CC_dt_congr (DTDepthLE.const 0 (false == b)) (fun x => by simp))
    (CC_dt_congr (DTDepthLE.const 0 (true == b)) (fun x => by simp))

/-! ### One gate under one stage: the switching lemma -/

theorem CC_gate_switch {X α : Type} [Fintype X] (w t : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp2 : p ≤ 1 / 2)
    (g : (X → Bool) → Bool) (isAnd : Bool) (l : List α) (φ : α → (X → Bool) → Bool)
    (hg : ∀ x, g x = if isAnd then l.all (fun a => φ a x) else l.any (fun a => φ a x))
    (hφ : ∀ a ∈ l, DTDepthLE t (φ a)) :
    restrictionProb p (fun ρ => ¬ DTDepthLE w (restrictFn ρ g)) ≤ (16 * p * (t : ℝ)) ^ w := by
  cases isAnd
  · obtain ⟨F, hFw, hF⟩ := CC_any_dnf φ l hφ
    have : g = dnfValue F := funext fun x => by rw [hg x, ← hF x]; rfl
    rw [this]
    exact switching_lemma_dnf t w p hp hp2 F hFw
  · obtain ⟨F, hFw, hF⟩ := CC_any_dnf (fun a x => !φ a x) l (fun a ha => CC_dt_not (hφ a ha))
    have hgF : ∀ ρ, restrictFn ρ g = fun x => !(restrictFn ρ (dnfValue F) x) := by
      intro ρ; funext x
      simp only [restrictFn]
      rw [hg, ← hF]
      simp only [if_true]
      generalize (fun e => (ρ e).getD (x e)) = y
      clear hF hφ hg
      induction l with
      | nil => rfl
      | cons a l ih => simp [List.all_cons, List.any_cons, ih]
    have : (fun ρ => ¬ DTDepthLE w (restrictFn ρ g)) =
        (fun ρ => ¬ DTDepthLE w (restrictFn ρ (dnfValue F))) := by
      funext ρ; rw [hgF, CC_dt_not_iff]
    rw [this]
    exact switching_lemma_dnf t w p hp hp2 F hFw

/-! ### The stages -/

def CC_Bad {X : Type} (C : MantriCVQ.ACCircuit X) (w j : ℕ) (ρ : X → Option Bool) : Prop :=
  ∃ k : Fin C.gates.length, gateDepth C k ≤ j ∧ ¬ DTDepthLE w (restrictFn ρ (gateValue C k))

def CC_W (w j : ℕ) : ℕ := if j = 0 then 1 else w

def CC_P (w j : ℕ) : ℝ := 1 / (32 * (CC_W w j : ℝ))

def CC_Q (w : ℕ) : ℕ → ℝ
  | 0 => 1
  | j + 1 => CC_Q w j * CC_P w j

theorem CC_W_pos {w : ℕ} (hw : 1 ≤ w) (j : ℕ) : 1 ≤ CC_W w j := by
  unfold CC_W; split_ifs <;> omega

theorem CC_P_bounds {w : ℕ} (hw : 1 ≤ w) (j : ℕ) : 0 ≤ CC_P w j ∧ CC_P w j ≤ 1 / 2 := by
  have h1 : (1 : ℝ) ≤ CC_W w j := by exact_mod_cast CC_W_pos hw j
  unfold CC_P
  constructor
  · positivity
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith

theorem CC_P_mul {w : ℕ} (hw : 1 ≤ w) (j : ℕ) : 16 * CC_P w j * (CC_W w j : ℝ) = 1 / 2 := by
  have h1 : (1 : ℝ) ≤ CC_W w j := by exact_mod_cast CC_W_pos hw j
  unfold CC_P
  field_simp
  ring

theorem CC_Q_bounds {w : ℕ} (hw : 1 ≤ w) : ∀ j, 0 ≤ CC_Q w j ∧ CC_Q w j ≤ 1 := by
  intro j
  induction j with
  | zero => simp [CC_Q]
  | succ j ih =>
    obtain ⟨h0, h1⟩ := CC_P_bounds hw j
    simp only [CC_Q]
    constructor
    · exact mul_nonneg ih.1 h0
    · nlinarith [ih.1, ih.2]

theorem CC_Q_succ (w : ℕ) : ∀ j, CC_Q w (j + 1) = (1 / 32) * (1 / (32 * (w : ℝ))) ^ j := by
  intro j
  induction j with
  | zero => simp [CC_Q, CC_P, CC_W]
  | succ j ih =>
    rw [CC_Q, ih, pow_succ]
    simp [CC_P, CC_W]
    ring

theorem CC_input_dt {X : Type} (C : MantriCVQ.ACCircuit X) (w : ℕ) (hw : 1 ≤ w) (j : ℕ)
    (ρA : X → Option Bool) (hA : ¬ CC_Bad C w j ρA) (k : Fin C.gates.length)
    (hk : gateDepth C k = j + 1) (s : MantriCVQ.Src X) (hs : s ∈ C.gates[k.val].inputs) :
    DTDepthLE (CC_W w j) (restrictFn ρA (fun x => s.eval x (gateValues C x))) := by
  cases s with
  | lit v b => exact CC_dt_mono (CC_dt_restrict (CC_dt_lit v b) ρA) (CC_W_pos hw j)
  | const b => exact CC_dt_restrict (DTDepthLE.const _ b) ρA
  | gate i =>
    have hik : i < k.val := C.wf k.val k.isLt _ hs i rfl
    have hi : i < C.gates.length := by omega
    have hlt := CC_gateDepth_lt C k i hs hi
    have hpos := CC_gateDepth_pos C ⟨i, hi⟩
    have hW : CC_W w j = w := by unfold CC_W; rw [if_neg (by omega)]
    rw [hW]
    by_contra hc
    exact hA ⟨⟨i, hi⟩, by omega, hc⟩

theorem CC_main {X : Type} [Fintype X] (C : MantriCVQ.ACCircuit X) (w : ℕ) (hw : 1 ≤ w) :
    ∀ j, restrictionProb (CC_Q w j) (CC_Bad C w j) ≤
      ∑ k : Fin C.gates.length, if gateDepth C k ≤ j then ((1 : ℝ) / 2) ^ w else 0 := by
  intro j
  induction j with
  | zero =>
    have hno : ∀ ρ, ¬ CC_Bad C w 0 ρ := by
      rintro ρ ⟨k, hk, -⟩
      have := CC_gateDepth_pos C k
      omega
    calc restrictionProb (CC_Q w 0) (CC_Bad C w 0) = 0 := by
          unfold restrictionProb
          exact Finset.sum_eq_zero fun ρ _ => if_neg (hno ρ)
      _ ≤ _ := Finset.sum_nonneg fun k _ => by split_ifs <;> positivity
  | succ j ih =>
    obtain ⟨hQ0, hQ1⟩ := CC_Q_bounds hw j
    obtain ⟨hP0, hP1⟩ := CC_P_bounds hw j
    have hstep := CC_step (q := CC_Q w j) (p := CC_P w j) (c := ((1 : ℝ) / 2) ^ w) hQ0 hQ1 hP0
      (by linarith) (by positivity) (CC_Bad C w j) (CC_Bad C w (j + 1))
      (Finset.univ.filter fun k => gateDepth C k = j + 1)
      (fun k ρA ρB => ¬ DTDepthLE w (restrictFn ρB (restrictFn ρA (gateValue C k)))) ?cover ?sw
    · have hcard : (((Finset.univ.filter fun k => gateDepth C k = j + 1).card : ℕ) : ℝ) *
          ((1 : ℝ) / 2) ^ w = ∑ k : Fin C.gates.length,
            if gateDepth C k = j + 1 then ((1 : ℝ) / 2) ^ w else 0 := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      calc restrictionProb (CC_Q w (j + 1)) (CC_Bad C w (j + 1))
          ≤ _ := hstep
        _ ≤ _ := add_le_add_left ih _
        _ = _ := by
          rw [hcard, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun k _ => ?_
          split_ifs <;> first | omega | simp
    case cover =>
      intro ρA ρB hB
      by_cases hA : CC_Bad C w j ρA
      · exact Or.inl hA
      · right
        obtain ⟨k, hk, hk2⟩ := hB
        rw [← CC_restrict_comp] at hk2
        have hkd : gateDepth C k = j + 1 := by
          by_contra hne
          apply hA
          refine ⟨k, by omega, fun hdt => hk2 (CC_dt_restrict hdt ρB)⟩
        exact ⟨k, by simp [hkd], hk2⟩
    case sw =>
      intro ρA hA k hk
      have hkd : gateDepth C k = j + 1 := by simpa using hk
      calc _ ≤ (16 * CC_P w j * (CC_W w j : ℝ)) ^ w :=
            CC_gate_switch w (CC_W w j) (CC_P w j) hP0 hP1 (restrictFn ρA (gateValue C k))
              C.gates[k.val].isAnd C.gates[k.val].inputs
              (fun s => restrictFn ρA (fun x => s.eval x (gateValues C x)))
              (fun x => CC_gateValues_get C _ k.val k.isLt)
              (fun s hs => CC_input_dt C w hw j ρA hA k hkd s hs)
        _ = _ := by rw [CC_P_mul hw]

theorem CC_out_bad {X : Type} (C : MantriCVQ.ACCircuit X) (w : ℕ) (hw : 1 ≤ w) (h : ℕ)
    (hC : C.depth ≤ h) (ρ : X → Option Bool) (hρ : ¬ DTDepthLE w (restrictFn ρ C.eval)) :
    CC_Bad C w h ρ := by
  have heval : C.eval = fun x => C.output.eval x (gateValues C x) := rfl
  have hdepth : C.depth = C.output.depth (gateDepths C) := rfl
  have hwf := C.wf_output
  rw [heval] at hρ
  rw [hdepth] at hC
  cases ho : C.output with
  | lit v b =>
    rw [ho] at hρ
    exact absurd (CC_dt_mono (CC_dt_restrict (CC_dt_lit v b) ρ) hw) hρ
  | const b =>
    rw [ho] at hρ
    exact absurd (CC_dt_restrict (DTDepthLE.const w b) ρ) hρ
  | gate i =>
    rw [ho] at hρ hC
    exact ⟨⟨i, hwf i ho⟩, hC, hρ⟩

end HypercliqueAC0.FixedDepth

open HypercliqueAC0.FixedDepth in
attribute [local instance] Classical.propDecidable Classical.decEq in
theorem solution {X : Type} [Fintype X] (h w : ℕ) (hh : 1 ≤ h) (hw : 1 ≤ w)
    (C : MantriCVQ.ACCircuit X) (hC : C.depth ≤ h) :
    restrictionProb ((1 / 32) * (1 / (32 * (w : ℝ))) ^ (h - 1))
        (fun ρ => ¬ DTDepthLE w (restrictFn ρ C.eval)) ≤
      (C.gates.length : ℝ) * (2 : ℝ) ^ (-(w : ℝ)) := by
  obtain ⟨j, rfl⟩ : ∃ j, h = j + 1 := ⟨h - 1, by omega⟩
  rw [Nat.add_sub_cancel, ← CC_Q_succ]
  obtain ⟨hQ0, hQ1⟩ := CC_Q_bounds hw (j + 1)
  have hc : (2 : ℝ) ^ (-(w : ℝ)) = ((1 : ℝ) / 2) ^ w := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div, inv_pow]
  rw [hc]
  calc _ ≤ restrictionProb (CC_Q w (j + 1)) (CC_Bad C w (j + 1)) :=
        CC_prob_mono hQ0 hQ1 (fun ρ hρ => CC_out_bad C w hw (j + 1) hC ρ hρ)
    _ ≤ _ := CC_main C w hw (j + 1)
    _ ≤ ∑ k : Fin C.gates.length, ((1 : ℝ) / 2) ^ w :=
        Finset.sum_le_sum fun k _ => by split_ifs <;> first | exact le_rfl | positivity
    _ = _ := by simp

