-- Prove2me | solution 1 for HypercliqueAC0.FixedDepth.lemma_4_1_depth
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T01:21:58.311665+00:00
-- url     : https://prove2.me/submissions/4c65950c-138f-4077-a0d9-9ace2b4527d4

import Mathlib
import Definitions.Def_HypercliqueAC0_FixedDepth_Planting

noncomputable section
namespace HypercliqueAC0.FixedDepth
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators

theorem L41_foldl_len {β γ : Type} (step : List β → γ → β) (l : List γ) (init : List β) :
    (l.foldl (fun ds g => ds ++ [step ds g]) init).length = init.length + l.length := by
  induction l generalizing init with
  | nil => simp
  | cons g l ih => simp only [List.foldl_cons, ih, List.length_append, List.length_cons,
      List.length_nil]; omega

theorem L41_foldl_prefix {β γ : Type} (step : List β → γ → β) (l : List γ) (init : List β) :
    ∃ t, l.foldl (fun ds g => ds ++ [step ds g]) init = init ++ t := by
  induction l generalizing init with
  | nil => exact ⟨[], by simp⟩
  | cons g l ih =>
    obtain ⟨t, ht⟩ := ih (init ++ [step init g])
    exact ⟨[step init g] ++ t, by simp [List.foldl_cons, ht]⟩

theorem L41_foldl_getD {β γ : Type} (step : List β → γ → β) (l : List γ) (k : ℕ)
    (hk : k < l.length) (d : β) :
    (l.foldl (fun ds g => ds ++ [step ds g]) []).getD k d =
      step ((l.take k).foldl (fun ds g => ds ++ [step ds g]) []) l[k] := by
  have hl : l = l.take k ++ ([l[k]] ++ l.drop (k+1)) := by
    simp
  obtain ⟨t, ht⟩ := L41_foldl_prefix step (l.drop (k+1))
    ((l.take k).foldl (fun ds g => ds ++ [step ds g]) [] ++
      [step ((l.take k).foldl (fun ds g => ds ++ [step ds g]) []) l[k]])
  have hlen := L41_foldl_len step (l.take k) []
  simp only [List.length_nil, Nat.zero_add, List.length_take, Nat.min_eq_left hk.le] at hlen
  conv_lhs => rw [hl, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil, ht]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hlen]),
    List.getElem?_append_right (by simp [hlen])]
  simp [hlen]

theorem L41_foldl_getD_lt {β γ : Type} (step : List β → γ → β) (l : List γ) (k i : ℕ)
    (hi : i < k) (d : β) :
    (l.foldl (fun ds g => ds ++ [step ds g]) []).getD i d =
      ((l.take k).foldl (fun ds g => ds ++ [step ds g]) []).getD i d := by
  rcases Nat.lt_or_ge k l.length with hk | hk
  · obtain ⟨t, ht⟩ := L41_foldl_prefix step (l.drop k)
      ((l.take k).foldl (fun ds g => ds ++ [step ds g]) [])
    have hlen := L41_foldl_len step (l.take k) []
    conv_lhs => rw [← List.take_append_drop k l, List.foldl_append, ht]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by simp at hlen ⊢; omega)]
  · rw [List.take_of_length_le hk]

theorem L41_gateDepth_eq {X : Type} (C : MantriCVQ.ACCircuit X) (α : Fin C.gates.length) :
    gateDepth C α = 1 + (C.gates[α.val].inputs.map (MantriCVQ.Src.depth (gateDepths C))).foldr
      max 0 := by
  unfold gateDepth
  rw [show gateDepths C = C.gates.foldl (fun ds g => ds ++
    [(fun ds (g : MantriCVQ.ACGate X) => 1 + (g.inputs.map (MantriCVQ.Src.depth ds)).foldr max 0)
      ds g]) [] from rfl]
  rw [L41_foldl_getD _ _ _ α.isLt]
  congr 2
  apply List.map_congr_left
  intro s hs
  cases s with
  | lit v b => rfl
  | const b => rfl
  | gate i =>
    have hi := C.wf α.val α.isLt _ hs i rfl
    simp only [MantriCVQ.Src.depth]
    exact (L41_foldl_getD_lt _ C.gates α.val i hi 0).symm

theorem L41_foldr_max_le_iff (l : List ℕ) (b : ℕ) : l.foldr max 0 ≤ b ↔ ∀ x ∈ l, x ≤ b := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.foldr_cons, ih]

theorem L41_le_foldr_max (l : List ℕ) (x : ℕ) (hx : x ∈ l) : x ≤ l.foldr max 0 :=
  (L41_foldr_max_le_iff l _).1 le_rfl x hx


/-! ## Möbius algebra for `multilinearCoeff` -/

theorem L41_coeff_insert {Y : Type*} (f : (Y → Bool) → ℝ) (E : Finset Y) (a : Y) (ha : a ∉ E) :
    multilinearCoeff f (insert a E) = ∑ T ∈ E.powerset, (-1 : ℝ) ^ (E \ T).card *
      (f (indicator (insert a T)) - f (indicator T)) := by
  unfold multilinearCoeff
  rw [Finset.sum_powerset_insert ha, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro T hT
  rw [Finset.mem_powerset] at hT
  have haT : a ∉ T := fun h => ha (hT h)
  have h1 : insert a E \ T = insert a (E \ T) := by
    ext x; by_cases hx : x = a
    · subst hx; simp [haT]
    · simp [hx]
  have h2 : insert a E \ insert a T = E \ T := by
    ext x; by_cases hx : x = a
    · subst hx; simp [ha]
    · simp [hx]
  rw [h1, h2, Finset.card_insert_of_notMem (by simp [ha]), pow_succ]
  ring

theorem L41_ind_update_true {Y : Type*} (U : Finset Y) (a : Y) :
    Function.update (indicator U) a true = indicator (insert a U) := by
  funext e
  by_cases h : e = a
  · subst h; simp [indicator]
  · simp [indicator, h]

theorem L41_ind_update_false {Y : Type*} (U : Finset Y) (a : Y) (ha : a ∉ U) :
    Function.update (indicator U) a false = indicator U := by
  funext e
  by_cases h : e = a
  · subst h; simp [indicator, ha]
  · simp [indicator, Function.update_of_ne h]

theorem L41_mobius {Y : Type*} (T : Finset Y) :
    ∀ f : (Y → Bool) → ℝ, f (indicator T) = ∑ E ∈ T.powerset, multilinearCoeff f E := by
  induction T using Finset.induction_on with
  | empty => intro f; simp [multilinearCoeff]
  | @insert a T ha ih =>
    intro f
    rw [Finset.sum_powerset_insert ha]
    have hD : ∀ E ∈ T.powerset, multilinearCoeff f (insert a E) =
        multilinearCoeff (fun z => f (Function.update z a true) - f (Function.update z a false))
          E := by
      intro E hE
      rw [Finset.mem_powerset] at hE
      rw [L41_coeff_insert f E a (fun h => ha (hE h))]
      unfold multilinearCoeff
      apply Finset.sum_congr rfl
      intro U hU
      have haU : a ∉ U := fun h => ha (hE (Finset.mem_powerset.1 hU h))
      simp only [L41_ind_update_true, L41_ind_update_false _ _ haU]
    rw [Finset.sum_congr rfl hD, ← ih, ← ih]
    simp only [L41_ind_update_true, L41_ind_update_false _ _ ha]
    ring

theorem L41_unique {Y : Type*} (f : (Y → Bool) → ℝ) (c : Finset Y → ℝ)
    (hc : ∀ T : Finset Y, f (indicator T) = ∑ E ∈ T.powerset, c E) (E : Finset Y) :
    multilinearCoeff f E = c E := by
  have hd : ∀ T : Finset Y, ∑ E ∈ T.powerset, (multilinearCoeff f E - c E) = 0 := by
    intro T; rw [Finset.sum_sub_distrib, ← L41_mobius, ← hc, sub_self]
  induction E using Finset.strongInduction with
  | H E ih =>
    have h := hd E
    rw [← Finset.add_sum_erase _ _ (Finset.mem_powerset.2 (subset_refl E))] at h
    rw [Finset.sum_eq_zero] at h
    · linarith
    · intro E' hE'
      rw [Finset.mem_erase, Finset.mem_powerset] at hE'
      rw [ih E' (Finset.ssubset_iff_subset_ne.2 ⟨hE'.2, hE'.1⟩), sub_self]

theorem L41_coeff_mul {Y : Type*} (F G : (Y → Bool) → ℝ) (E : Finset Y) :
    multilinearCoeff (fun z => F z * G z) E = ∑ E₁ ∈ E.powerset, ∑ E₂ ∈ E.powerset,
      if E₁ ∪ E₂ = E then multilinearCoeff F E₁ * multilinearCoeff G E₂ else 0 := by
  apply L41_unique (fun z => F z * G z) (fun E => ∑ E₁ ∈ E.powerset, ∑ E₂ ∈ E.powerset,
      if E₁ ∪ E₂ = E then multilinearCoeff F E₁ * multilinearCoeff G E₂ else 0)
  intro T
  show F (indicator T) * G (indicator T) = _
  rw [L41_mobius T F, L41_mobius T G, Finset.sum_mul_sum]
  have step : ∀ E ∈ T.powerset, (∑ E₁ ∈ E.powerset, ∑ E₂ ∈ E.powerset,
      if E₁ ∪ E₂ = E then multilinearCoeff F E₁ * multilinearCoeff G E₂ else 0) =
      ∑ E₁ ∈ T.powerset, ∑ E₂ ∈ T.powerset,
      if E₁ ∪ E₂ = E then multilinearCoeff F E₁ * multilinearCoeff G E₂ else 0 := by
    intro E hE
    rw [Finset.mem_powerset] at hE
    have inner : ∀ E₁, (∑ E₂ ∈ E.powerset,
        if E₁ ∪ E₂ = E then multilinearCoeff F E₁ * multilinearCoeff G E₂ else 0) =
        ∑ E₂ ∈ T.powerset,
        if E₁ ∪ E₂ = E then multilinearCoeff F E₁ * multilinearCoeff G E₂ else 0 := by
      intro E₁
      apply Finset.sum_subset (Finset.powerset_mono.2 hE)
      intro E₂ _ hE₂
      rw [if_neg]
      intro h; apply hE₂; rw [Finset.mem_powerset, ← h]; exact Finset.subset_union_right
    rw [Finset.sum_congr rfl (fun E₁ _ => inner E₁)]
    apply Finset.sum_subset (Finset.powerset_mono.2 hE)
    intro E₁ _ hE₁
    apply Finset.sum_eq_zero
    intro E₂ _
    rw [if_neg]
    intro h; apply hE₁; rw [Finset.mem_powerset, ← h]; exact Finset.subset_union_left
  symm
  rw [Finset.sum_congr rfl step, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro E₁ hE₁
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro E₂ hE₂
  rw [Finset.sum_ite_eq, if_pos]
  rw [Finset.mem_powerset] at *
  exact Finset.union_subset hE₁ hE₂

theorem L41_mul_ne_zero {Y : Type*} (F G : (Y → Bool) → ℝ) (E : Finset Y)
    (h : multilinearCoeff (fun z => F z * G z) E ≠ 0) :
    ∃ E₁ E₂, E₁ ⊆ E ∧ E₂ ⊆ E ∧ (∀ e ∈ E, e ∈ E₁ ∨ e ∈ E₂) ∧ multilinearCoeff F E₁ ≠ 0 ∧
      multilinearCoeff G E₂ ≠ 0 := by
  rw [L41_coeff_mul] at h
  obtain ⟨E₁, hE₁, h1⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨E₂, hE₂, h2⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  by_cases hu : E₁ ∪ E₂ = E
  · rw [if_pos hu] at h2
    exact ⟨E₁, E₂, Finset.mem_powerset.1 hE₁, Finset.mem_powerset.1 hE₂,
      fun e he => by rw [← hu] at he; exact Finset.mem_union.1 he,
      left_ne_zero_of_mul h2, right_ne_zero_of_mul h2⟩
  · rw [if_neg hu] at h2; exact absurd rfl h2

theorem L41_coeff_or {Y : Type*} (F G : (Y → Bool) → ℝ) (E : Finset Y) :
    multilinearCoeff (fun z => F z + G z - F z * G z) E =
      multilinearCoeff F E + multilinearCoeff G E - multilinearCoeff (fun z => F z * G z) E := by
  unfold multilinearCoeff
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro T _; ring

theorem L41_local {Y : Type*} (f : (Y → Bool) → ℝ) (S : Finset Y)
    (hf : ∀ z z' : Y → Bool, (∀ y ∈ S, z y = z' y) → f z = f z') (E : Finset Y)
    (hE : multilinearCoeff f E ≠ 0) : E ⊆ S := by
  intro y hy
  by_contra hyS
  apply hE
  rw [← Finset.insert_erase hy, L41_coeff_insert f _ y (Finset.notMem_erase y E)]
  apply Finset.sum_eq_zero
  intro T _
  rw [hf (indicator (insert y T)) (indicator T), sub_self, mul_zero]
  intro y' hy'
  have : y' ≠ y := fun h => hyS (h ▸ hy')
  simp [indicator, this]

theorem L41_coeff_map {Y Y' : Type*} (φ : Y' ↪ Y) (f' : (Y' → Bool) → ℝ) (f : (Y → Bool) → ℝ)
    (h : ∀ T : Finset Y', f' (indicator T) = f (indicator (T.map φ))) (E : Finset Y') :
    multilinearCoeff f' E = multilinearCoeff f (E.map φ) := by
  unfold multilinearCoeff
  rw [Finset.map_eq_image, Finset.powerset_image,
    Finset.sum_image (fun a _ b _ hab => Finset.image_injective φ.injective hab)]
  apply Finset.sum_congr rfl
  intro T _
  rw [← Finset.map_eq_image, ← Finset.map_eq_image, ← Finset.map_sdiff, Finset.card_map, h]


/-! ## Circuit facts -/

theorem L41_all_congr {α : Type*} (l : List α) (p q : α → Bool) (h : ∀ a ∈ l, p a = q a) :
    l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.all_cons, h a List.mem_cons_self,
      ih (fun b hb => h b (List.mem_cons_of_mem a hb))]

theorem L41_any_congr {α : Type*} (l : List α) (p q : α → Bool) (h : ∀ a ∈ l, p a = q a) :
    l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.any_cons, h a List.mem_cons_self,
      ih (fun b hb => h b (List.mem_cons_of_mem a hb))]

/-- The function computed by an input of a gate. -/
def L41_inFn {X : Type} (C : MantriCVQ.ACCircuit X) (s : MantriCVQ.Src X) :
    (X → Bool) → Bool := fun x => s.eval x (gateValues C x)

theorem L41_prefix_zero {X : Type} (C : MantriCVQ.ACCircuit X) (α : Fin C.gates.length)
    (x : X → Bool) : gatePrefix C α 0 x = C.gates[α.val].isAnd := by
  unfold gatePrefix abstractPrefix
  split_ifs with h <;> simp [h]

theorem L41_prefix_succ {X : Type} (C : MantriCVQ.ACCircuit X) (α : Fin C.gates.length) (j : ℕ)
    (hj : j < C.gates[α.val].inputs.length) (x : X → Bool) :
    gatePrefix C α (j+1) x = if C.gates[α.val].isAnd then
      (gatePrefix C α j x && L41_inFn C (C.gates[α.val].inputs[j]) x)
      else (gatePrefix C α j x || L41_inFn C (C.gates[α.val].inputs[j]) x) := by
  unfold gatePrefix abstractPrefix gateInputs
  rw [List.take_add_one, List.getElem?_map, List.getElem?_eq_getElem hj]
  split_ifs <;> simp [List.all_append, List.any_append, L41_inFn]

theorem L41_gateValue_eq {X : Type} (C : MantriCVQ.ACCircuit X) (β : Fin C.gates.length) :
    gateValue C β = gatePrefix C β C.gates[β.val].inputs.length := by
  funext x
  unfold gateValue
  rw [show gateValues C x = C.gates.foldl (fun vals g => vals ++
    [(fun vals (g : MantriCVQ.ACGate X) => if g.isAnd then g.inputs.all (MantriCVQ.Src.eval x vals)
      else g.inputs.any (MantriCVQ.Src.eval x vals)) vals g]) [] from rfl]
  rw [L41_foldl_getD _ _ _ β.isLt]
  unfold gatePrefix abstractPrefix gateInputs
  rw [show ∀ (l : List (MantriCVQ.Src X)) (f : MantriCVQ.Src X → ((X → Bool) → Bool)),
    (l.map f).take l.length = l.map f from fun l f => List.take_of_length_le (by simp),
    List.all_map, List.any_map]
  have hc : ∀ s ∈ C.gates[β.val].inputs, MantriCVQ.Src.eval x
      ((C.gates.take β.val).foldl (fun vals g => vals ++
    [(fun vals (g : MantriCVQ.ACGate X) => if g.isAnd then g.inputs.all (MantriCVQ.Src.eval x vals)
      else g.inputs.any (MantriCVQ.Src.eval x vals)) vals g]) []) s =
      ((fun f => f x) ∘ fun s x => MantriCVQ.Src.eval x (gateValues C x) s) s := by
    intro s hs
    cases s with
    | lit v b => rfl
    | const b => rfl
    | gate i =>
      have hi := C.wf β.val β.isLt _ hs i rfl
      simp only [MantriCVQ.Src.eval, Function.comp]
      exact (L41_foldl_getD_lt _ C.gates β.val i hi false).symm
  split_ifs
  · exact L41_all_congr _ _ _ hc
  · exact L41_any_congr _ _ _ hc

theorem L41_depth_lt {X : Type} (C : MantriCVQ.ACCircuit X) (α : Fin C.gates.length) (γ : ℕ)
    (hγ : MantriCVQ.Src.gate γ ∈ C.gates[α.val].inputs) (hγlt : γ < C.gates.length) :
    gateDepth C ⟨γ, hγlt⟩ < gateDepth C α := by
  rw [L41_gateDepth_eq C α]
  have := L41_le_foldr_max _ _ (List.mem_map_of_mem (f := MantriCVQ.Src.depth (gateDepths C)) hγ)
  simp only [MantriCVQ.Src.depth] at this
  unfold gateDepth
  simp only
  omega

/-! ## Restrictions -/

theorem L41_R_and {m r : ℕ} (G : Edge m r → Bool) (H : Hypergraph m r)
    (a b : (Edge m r → Bool) → Bool) :
    restricted G H (boolReal (fun x => a x && b x)) =
      fun z => restricted G H (boolReal a) z * restricted G H (boolReal b) z := by
  funext z
  simp only [restricted, boolReal]
  by_cases ha : a (rho G H z) = true <;> by_cases hb : b (rho G H z) = true <;> simp [ha, hb]

theorem L41_R_or {m r : ℕ} (G : Edge m r → Bool) (H : Hypergraph m r)
    (a b : (Edge m r → Bool) → Bool) :
    restricted G H (boolReal (fun x => a x || b x)) =
      fun z => restricted G H (boolReal a) z + restricted G H (boolReal b) z -
        restricted G H (boolReal a) z * restricted G H (boolReal b) z := by
  funext z
  simp only [restricted, boolReal]
  by_cases ha : a (rho G H z) = true <;> by_cases hb : b (rho G H z) = true <;> simp [ha, hb]

theorem L41_small_of_local {m r : ℕ} (G : Edge m r → Bool) (H : Hypergraph m r)
    (g : (Edge m r → Bool) → ℝ) (W : Finset (Edge m r))
    (hg : ∀ x x' : Edge m r → Bool, (∀ e ∈ W, x e = x' e) → g x = g x')
    (E : Finset (FreeEdge G H)) (hE : isMonomial (restricted G H g) E) :
    (verticesOf (E.image (fun e => e.val))).card ≤ (verticesOf W).card := by
  have hsub := L41_local (restricted G H g) (Finset.univ.filter (fun y => y.val ∈ W)) ?_ E hE
  · apply Finset.card_le_card
    unfold verticesOf
    apply Finset.biUnion_subset_biUnion_of_subset_left
    intro e he
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 he
    have := hsub hy
    simpa using this
  · intro z z' hzz
    unfold restricted
    apply hg
    intro e he
    unfold rho
    split_ifs with h
    · apply hzz; simp [he]
    · rfl

theorem L41_verticesOf_singleton {m r : ℕ} (v : Edge m r) : (verticesOf {v}).card = r := by
  unfold verticesOf
  rw [Finset.singleton_biUnion]
  exact v.property

theorem L41_verticesOf_empty {m r : ℕ} : (verticesOf (∅ : Finset (Edge m r))).card = 0 := by
  simp [verticesOf]

/-- Embedding of the free edges of a smaller hypergraph into those of a larger one. -/
def L41_emb {m r : ℕ} (G : Edge m r → Bool) (H H' : Hypergraph m r)
    (hHH : H'.edges ⊆ H.edges) : FreeEdge G H' ↪ FreeEdge G H :=
  ⟨fun y => ⟨y.val, hHH y.prop.1, y.prop.2⟩, by
    intro a b h; apply Subtype.ext; have := congrArg Subtype.val h; exact this⟩

theorem L41_rho_eq {m r : ℕ} (G : Edge m r → Bool) (H H' : Hypergraph m r)
    (hHH : H'.edges ⊆ H.edges) (T : Finset (FreeEdge G H')) :
    rho G H' (indicator T) = rho G H (indicator (T.map (L41_emb G H H' hHH))) := by
  funext e
  unfold rho indicator
  by_cases h' : e ∈ H'.edges ∧ G e = false
  · have h : e ∈ H.edges ∧ G e = false := ⟨hHH h'.1, h'.2⟩
    rw [dif_pos h', dif_pos h]
    simp only [decide_eq_decide, Finset.mem_map]
    constructor
    · intro hm; exact ⟨_, hm, rfl⟩
    · rintro ⟨y, hy, hye⟩
      have : y = ⟨e, h'⟩ := Subtype.ext (by have := congrArg Subtype.val hye; exact this)
      rw [← this]; exact hy
  · rw [dif_neg h']
    by_cases h : e ∈ H.edges ∧ G e = false
    · rw [dif_pos h]
      have hn : (⟨e, h⟩ : FreeEdge G H) ∉ T.map (L41_emb G H H' hHH) := by
        rw [Finset.mem_map]
        rintro ⟨y, _, hye⟩
        apply h'
        have := congrArg Subtype.val hye
        simp only [L41_emb] at this
        rw [← this]; exact y.prop
      simp [hn, h.2]
    · rw [dif_neg h]

theorem L41_transfer {m r : ℕ} (G : Edge m r → Bool) (g : (Edge m r → Bool) → ℝ)
    (A B₁ B₂ : Finset (Fin m)) (h1 : B₁ ⊆ A) (h2 : B₂ ⊆ A)
    (E : Finset (FreeEdge G (complete r A)))
    (hE : ∀ e ∈ E, e.val.val ⊆ B₁ ∨ e.val.val ⊆ B₂)
    (hmon : isMonomial (restricted G (complete r A) g) E)
    (hV : B₁ ∪ B₂ ⊆ verticesOf (E.image (fun e => e.val))) :
    spans G (hypergraphUnion (complete r B₁) (complete r B₂)) g := by
  have hHH : (hypergraphUnion (complete r B₁) (complete r B₂)).edges ⊆
      (complete r A).edges := by
    intro e he
    simp only [hypergraphUnion, complete, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and] at he ⊢
    rcases he with he | he
    · exact he.trans h1
    · exact he.trans h2
  set φ := L41_emb G _ _ hHH with hφ
  let E' : Finset (FreeEdge G (hypergraphUnion (complete r B₁) (complete r B₂))) :=
    Finset.univ.filter (fun y => φ y ∈ E)
  have hE' : E'.map φ = E := by
    ext e
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, E']
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro he
      have hmem : e.val ∈ (hypergraphUnion (complete r B₁) (complete r B₂)).edges := by
        simp only [hypergraphUnion, complete, Finset.mem_union, Finset.mem_filter,
          Finset.mem_univ, true_and]
        exact hE e he
      have hφe : φ ⟨e.val, hmem, e.prop.2⟩ = e := Subtype.ext rfl
      exact ⟨⟨e.val, hmem, e.prop.2⟩, by rw [hφe]; exact he, hφe⟩
  refine ⟨E', ?_, ?_⟩
  · unfold isMonomial
    rw [L41_coeff_map φ _ (restricted G (complete r A) g) (fun T => by
      simp only [restricted]; rw [L41_rho_eq G _ _ hHH T]) E', hE']
    exact hmon
  · have : E'.image (fun e => e.val) = E.image (fun e => e.val) := by
      rw [← hE', Finset.map_eq_image, Finset.image_image]
      rfl
    rw [this]
    exact hV

/-! ## The walk -/

/-- The conclusion of Lemma 4.1 with depth bound `d`. -/
def L41_Concl (m r s : ℕ) (G : Edge m r → Bool) (A : Finset (Fin m))
    (C : MantriCVQ.ACCircuit (Edge m r)) (d : ℕ) : Prop :=
  ∃ (α : Fin C.gates.length) (j : ℕ) (B₁ B₂ : Finset (Fin m)),
      1 ≤ j ∧ j ≤ C.gates[α.val].inputs.length ∧
      B₁ ⊆ A ∧ B₂ ⊆ A ∧ B₁.card ≤ s ∧ B₂.card ≤ s ∧ s < (B₁ ∪ B₂).card ∧
      spans G (hypergraphUnion (complete r B₁) (complete r B₂))
        (boolReal (gatePrefix C α j)) ∧
      gateDepth C α ≤ d

theorem L41_Concl_mono {m r s : ℕ} {G : Edge m r → Bool} {A : Finset (Fin m)}
    {C : MantriCVQ.ACCircuit (Edge m r)} {d d' : ℕ} (hd : d ≤ d')
    (h : L41_Concl m r s G A C d) : L41_Concl m r s G A C d' := by
  obtain ⟨α, j, B₁, B₂, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
  exact ⟨α, j, B₁, B₂, a1, a2, a3, a4, a5, a6, a7, a8, a9.trans hd⟩

theorem L41_verticesOf_sub {m r : ℕ} (G : Edge m r → Bool) (A : Finset (Fin m))
    (E : Finset (FreeEdge G (complete r A))) :
    verticesOf (E.image (fun e => e.val)) ⊆ A := by
  intro x hx
  simp only [verticesOf, Finset.mem_biUnion, Finset.mem_image] at hx
  obtain ⟨_, ⟨e, _, rfl⟩, hxe⟩ := hx
  have := e.prop.1
  simp only [complete, Finset.mem_filter, Finset.mem_univ, true_and] at this
  exact this hxe

theorem L41_edge_sub {m r : ℕ} (G : Edge m r → Bool) (A : Finset (Fin m))
    (E : Finset (FreeEdge G (complete r A))) (e : FreeEdge G (complete r A)) (he : e ∈ E) :
    e.val.val ⊆ verticesOf (E.image (fun e => e.val)) := by
  intro x hx
  simp only [verticesOf, Finset.mem_biUnion, Finset.mem_image]
  exact ⟨e.val, ⟨e, he, rfl⟩, hx⟩

theorem L41_verticesOf_union {m r : ℕ} (G : Edge m r → Bool) (A : Finset (Fin m))
    (E₁ E₂ : Finset (FreeEdge G (complete r A))) :
    verticesOf ((E₁ ∪ E₂).image (fun e => e.val)) =
      verticesOf (E₁.image (fun e => e.val)) ∪ verticesOf (E₂.image (fun e => e.val)) := by
  unfold verticesOf
  rw [Finset.image_union, Finset.union_biUnion]

theorem L41_stop {m r s : ℕ} (G : Edge m r → Bool) (A : Finset (Fin m))
    (C : MantriCVQ.ACCircuit (Edge m r)) (α : Fin C.gates.length) (j : ℕ)
    (hj : j + 1 ≤ C.gates[α.val].inputs.length)
    (E₁ E₂ : Finset (FreeEdge G (complete r A)))
    (hE : isMonomial (restricted G (complete r A) (boolReal (gatePrefix C α (j+1)))) (E₁ ∪ E₂))
    (hc : s < (verticesOf ((E₁ ∪ E₂).image (fun e => e.val))).card)
    (hc1 : (verticesOf (E₁.image (fun e => e.val))).card ≤ s)
    (hc2 : (verticesOf (E₂.image (fun e => e.val))).card ≤ s) :
    L41_Concl m r s G A C (gateDepth C α) := by
  rw [L41_verticesOf_union] at hc
  refine ⟨α, j+1, _, _, by omega, hj, L41_verticesOf_sub G A E₁, L41_verticesOf_sub G A E₂,
    hc1, hc2, hc, ?_, le_rfl⟩
  apply L41_transfer G _ A _ _ (L41_verticesOf_sub G A E₁) (L41_verticesOf_sub G A E₂) _ _ hE
  · rw [L41_verticesOf_union]
  · intro e he
    rcases Finset.mem_union.1 he with h | h
    · exact Or.inl (L41_edge_sub G A E₁ e h)
    · exact Or.inr (L41_edge_sub G A E₂ e h)

theorem L41_main (m r s : ℕ) (hs : r ≤ s) (G : Edge m r → Bool) (A : Finset (Fin m))
    (C : MantriCVQ.ACCircuit (Edge m r)) :
    ∀ (n : ℕ) (α : Fin C.gates.length), α.val = n → ∀ (j : ℕ),
      j ≤ C.gates[α.val].inputs.length →
      ∀ E : Finset (FreeEdge G (complete r A)),
        isMonomial (restricted G (complete r A) (boolReal (gatePrefix C α j))) E →
        s < (verticesOf (E.image (fun e => e.val))).card →
        L41_Concl m r s G A C (gateDepth C α) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro α hαn j
  induction j with
  | zero =>
    intro _ E hE hcard
    have := L41_small_of_local G _ _ ∅ (fun x x' _ => by
      simp only [boolReal, L41_prefix_zero]) E hE
    rw [L41_verticesOf_empty] at this
    omega
  | succ j ihj =>
    intro hj E hE hcard
    have hjlt : j < C.gates[α.val].inputs.length := hj
    obtain ⟨src, hsrc⟩ : ∃ src, C.gates[α.val].inputs[j] = src := ⟨_, rfl⟩
    have hsrcmem : src ∈ C.gates[α.val].inputs := hsrc ▸ List.getElem_mem hjlt
    have hpre := L41_prefix_succ C α j hjlt
    rw [hsrc] at hpre
    by_cases h1 : ∃ E' ⊆ E, isMonomial (restricted G (complete r A)
        (boolReal (gatePrefix C α j))) E' ∧ s < (verticesOf (E'.image (fun e => e.val))).card
    · obtain ⟨E', _, hE', hc⟩ := h1
      exact ihj (by omega) E' hE' hc
    by_cases h2 : ∃ E' ⊆ E, isMonomial (restricted G (complete r A)
        (boolReal (L41_inFn C src))) E' ∧ s < (verticesOf (E'.image (fun e => e.val))).card
    · obtain ⟨E', _, hE', hc⟩ := h2
      cases src with
      | lit v b =>
        have := L41_small_of_local G _ _ {v} (fun x x' hx => by
          have hv : L41_inFn C (MantriCVQ.Src.lit v b) x = L41_inFn C (MantriCVQ.Src.lit v b) x' := by
            simp only [L41_inFn, MantriCVQ.Src.eval, hx v (Finset.mem_singleton_self v)]
          unfold boolReal
          rw [hv]) E' hE'
        rw [L41_verticesOf_singleton] at this
        omega
      | const b =>
        have := L41_small_of_local G _ _ ∅ (fun x x' _ => rfl) E' hE'
        rw [L41_verticesOf_empty] at this
        omega
      | gate γ =>
        have hγα : γ < α.val := C.wf α.val α.isLt _ hsrcmem γ rfl
        have hγlt : γ < C.gates.length := lt_trans hγα α.isLt
        have hfun : L41_inFn C (MantriCVQ.Src.gate γ) =
            gatePrefix C ⟨γ, hγlt⟩ C.gates[γ].inputs.length := by
          rw [← L41_gateValue_eq]; rfl
        rw [hfun] at hE'
        exact L41_Concl_mono (L41_depth_lt C α γ hsrcmem hγlt).le
          (ihn γ (by omega) ⟨γ, hγlt⟩ rfl _ le_rfl E' hE' hc)
    simp only [not_exists, not_and, not_lt] at h1 h2
    obtain ⟨E₁, E₂, hE₁, hE₂, hcov, hc₁, hc₂⟩ : ∃ E₁ E₂, E₁ ⊆ E ∧ E₂ ⊆ E ∧
        (∀ e ∈ E, e ∈ E₁ ∨ e ∈ E₂) ∧
        isMonomial (restricted G (complete r A) (boolReal (gatePrefix C α j))) E₁ ∧
        isMonomial (restricted G (complete r A) (boolReal (L41_inFn C src))) E₂ := by
      by_cases hand : C.gates[α.val].isAnd = true
      · have : restricted G (complete r A) (boolReal (gatePrefix C α (j+1))) =
            fun z => restricted G (complete r A) (boolReal (gatePrefix C α j)) z *
              restricted G (complete r A) (boolReal (L41_inFn C src)) z := by
          rw [← L41_R_and]
          congr 2
          funext x
          rw [hpre x, if_pos hand]
        unfold isMonomial at hE
        rw [this] at hE
        exact L41_mul_ne_zero _ _ E hE
      · have : restricted G (complete r A) (boolReal (gatePrefix C α (j+1))) =
            fun z => restricted G (complete r A) (boolReal (gatePrefix C α j)) z +
              restricted G (complete r A) (boolReal (L41_inFn C src)) z -
              restricted G (complete r A) (boolReal (gatePrefix C α j)) z *
              restricted G (complete r A) (boolReal (L41_inFn C src)) z := by
          rw [← L41_R_or]
          congr 2
          funext x
          rw [hpre x, if_neg hand]
        unfold isMonomial at hE
        rw [this, L41_coeff_or] at hE
        have hF0 : multilinearCoeff (restricted G (complete r A)
            (boolReal (gatePrefix C α j))) E = 0 := by
          by_contra h
          exact absurd hcard (not_lt.2 (h1 E subset_rfl h))
        have hG0 : multilinearCoeff (restricted G (complete r A)
            (boolReal (L41_inFn C src))) E = 0 := by
          by_contra h
          exact absurd hcard (not_lt.2 (h2 E subset_rfl h))
        rw [hF0, hG0] at hE
        apply L41_mul_ne_zero _ _ E
        intro h
        apply hE
        rw [h]
        ring
    have hU : E₁ ∪ E₂ = E := by
      ext e
      rw [Finset.mem_union]
      constructor
      · rintro (h | h)
        · exact hE₁ h
        · exact hE₂ h
      · exact hcov e
    subst hU
    exact L41_stop G A C α j hj E₁ E₂ hE hcard (h1 E₁ hE₁ hc₁) (h2 E₂ hE₂ hc₂)

end HypercliqueAC0.FixedDepth

open HypercliqueAC0.FixedDepth in
attribute [local instance] Classical.propDecidable Classical.decEq in
theorem solution (m r s : ℕ) (hs : r ≤ s) (G : Edge m r → Bool)
    (A : Finset (Fin m)) (C : MantriCVQ.ACCircuit (Edge m r)) (β : Fin C.gates.length)
    (hβ : hasLargeMonomial G (complete r A) (boolReal (gateValue C β)) s) :
    ∃ (α : Fin C.gates.length) (j : ℕ) (B₁ B₂ : Finset (Fin m)),
      1 ≤ j ∧ j ≤ C.gates[α.val].inputs.length ∧
      B₁ ⊆ A ∧ B₂ ⊆ A ∧ B₁.card ≤ s ∧ B₂.card ≤ s ∧ s < (B₁ ∪ B₂).card ∧
      spans G (hypergraphUnion (complete r B₁) (complete r B₂))
        (boolReal (gatePrefix C α j)) ∧
      gateDepth C α ≤ gateDepth C β := by
  obtain ⟨E, hE, hc⟩ := hβ
  rw [L41_gateValue_eq] at hE
  exact L41_main m r s hs G A C β.val β rfl _ le_rfl E hE hc
