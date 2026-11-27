-- Prove2me | solution 1 for HypercliqueAC0.FixedDepth.lemma_4_5
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T01:30:06.27741+00:00
-- url     : https://prove2.me/submissions/052b3932-b9ae-4a05-b2ed-67534380c96c

import Mathlib
import Definitions.Def_HypercliqueAC0_FixedDepth_Planting
import Theorems.Thm_HypercliqueAC0_FixedDepth_lemma_4_1_depth
import Theorems.Thm_HypercliqueAC0_FixedDepth_prefix_circuit
import Theorems.Thm_HypercliqueAC0_FixedDepth_lemma_4_3
import Theorems.Thm_HypercliqueAC0_FixedDepth_lemma_4_4
import Theorems.Thm_HypercliqueAC0_FixedDepth_tail_biased_weak

noncomputable section
namespace HypercliqueAC0.FixedDepth
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators

lemma L45_weight_nonneg {X : Type*} [Fintype X] {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (x : X → Bool) : 0 ≤ weight p x := by
  unfold weight OAI.Problem313.BiasedFourier.weight
  refine Finset.prod_nonneg fun i _ => ?_
  unfold OAI.Problem313.BiasedFourier.scalarWeight
  split_ifs <;> linarith

lemma L45_prob_nonneg {X : Type*} [Fintype X] {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (E : (X → Bool) → Prop) : 0 ≤ probability p E := by
  unfold probability expectation
  refine Finset.sum_nonneg fun x _ => mul_nonneg (L45_weight_nonneg hp hp1 x) ?_
  beta_reduce
  split_ifs <;> norm_num

lemma L45_prob_union {X : Type*} [Fintype X] {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    {ι : Type*} (S : Finset ι) (E : (X → Bool) → Prop) (F : ι → (X → Bool) → Prop)
    (hE : ∀ x, E x → ∃ i ∈ S, F i x) :
    probability p E ≤ ∑ i ∈ S, probability p (F i) := by
  unfold probability expectation
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (L45_weight_nonneg hp hp1 x)
  beta_reduce
  by_cases hx : E x
  · obtain ⟨i, hi, hFi⟩ := hE x hx
    rw [if_pos hx]
    calc (1 : ℝ) = if F i x then 1 else 0 := by rw [if_pos hFi]
      _ ≤ ∑ j ∈ S, if F j x then (1 : ℝ) else 0 :=
        Finset.single_le_sum (f := fun j => if F j x then (1 : ℝ) else 0)
          (fun j _ => by split_ifs <;> norm_num) hi
  · rw [if_neg hx]
    exact Finset.sum_nonneg fun j _ => by split_ifs <;> norm_num

lemma L45_joint_union {v m r : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    {ι : Type*} (S : Finset ι) (ev : (Fin v ↪ Fin m) → (Edge m r → Bool) → Prop)
    (F : ι → (Fin v ↪ Fin m) → (Edge m r → Bool) → Prop)
    (hE : ∀ φ x, ev φ x → ∃ i ∈ S, F i φ x) :
    jointProbability p ev ≤ ∑ i ∈ S, jointProbability p (F i) := by
  unfold jointProbability
  rw [← Finset.mul_sum, Finset.sum_comm]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact Finset.sum_le_sum fun φ _ => L45_prob_union hp hp1 S _ _ (hE φ)

/-- Averaging over the restriction of a uniform injection. -/
lemma L45_avg {v ℓ m : ℕ} (hℓ : ℓ ≤ m) (e : Fin v ↪ Fin ℓ) (g : (Fin v ↪ Fin m) → ℝ) :
    (Fintype.card (Fin ℓ ↪ Fin m) : ℝ)⁻¹ * ∑ φ : Fin ℓ ↪ Fin m, g (e.trans φ) =
      (Fintype.card (Fin v ↪ Fin m) : ℝ)⁻¹ * ∑ κ : Fin v ↪ Fin m, g κ := by
  set N : (Fin v ↪ Fin m) → ℕ := fun κ =>
    (Finset.univ.filter (fun φ : Fin ℓ ↪ Fin m => e.trans φ = κ)).card with hN
  have hconst : ∀ κ κ', N κ = N κ' := by
    intro κ κ'
    have := Equiv.Perm.isMultiplyPretransitive (Fin m) v
    obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (Equiv.Perm (Fin m)) κ κ'
    refine Finset.card_bij (fun φ _ => φ.trans σ.toEmbedding) ?_ ?_ ?_
    · intro φ hφ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hφ ⊢
      rw [← hσ, ← hφ]
      ext i; rfl
    · intro φ₁ _ φ₂ _ h
      ext i
      have := congrArg (fun f => f i) h
      simp only [Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
        EmbeddingLike.apply_eq_iff_eq] at this
      rw [this]
    · intro ψ hψ
      refine ⟨ψ.trans σ.symm.toEmbedding, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hψ ⊢
        ext i
        have := congrArg (fun f : Fin v ↪ Fin m => f i) hψ
        have h2 := congrArg (fun f : Fin v ↪ Fin m => f i) hσ
        simp only [Function.Embedding.trans_apply] at this
        change σ (κ i) = κ' i at h2
        simp only [Function.Embedding.trans_apply, Equiv.toEmbedding_apply]
        rw [this, ← h2]; simp
      · ext i; simp
  have hsum : ∀ g : (Fin v ↪ Fin m) → ℝ, ∑ φ : Fin ℓ ↪ Fin m, g (e.trans φ) =
      ∑ κ : Fin v ↪ Fin m, (N κ : ℝ) * g κ := by
    intro g
    rw [← Finset.sum_fiberwise Finset.univ (fun φ : Fin ℓ ↪ Fin m => e.trans φ)]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => g κ) (fun φ hφ => by
      rw [(Finset.mem_filter.mp hφ).2])]
    simp [hN]
  -- a base point
  have hne : Nonempty (Fin ℓ ↪ Fin m) := ⟨Fin.castLEEmb hℓ⟩
  obtain ⟨φ₀⟩ := hne
  set κ₀ := e.trans φ₀
  have hcard : (Fintype.card (Fin ℓ ↪ Fin m) : ℝ) =
      (N κ₀ : ℝ) * Fintype.card (Fin v ↪ Fin m) := by
    have := hsum (fun _ => 1)
    simp only [mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
    rw [this, Finset.sum_congr rfl (fun κ _ => by rw [hconst κ κ₀])]
    simp [mul_comm]
  have hN0 : (N κ₀ : ℝ) ≠ 0 := by
    have : 0 < N κ₀ := Finset.card_pos.mpr ⟨φ₀, by simp [κ₀]⟩
    exact_mod_cast this.ne'
  rw [hsum g, Finset.sum_congr rfl (fun κ _ => by rw [hconst κ κ₀]), ← Finset.mul_sum, hcard,
    mul_inv, mul_assoc, mul_comm (Fintype.card _ : ℝ)⁻¹, ← mul_assoc, ← mul_assoc,
    inv_mul_cancel₀ hN0, one_mul]
  ring


lemma L45_hyp_ext {m r : ℕ} (H J : Hypergraph m r) (hv : H.vertices = J.vertices)
    (he : H.edges = J.edges) : H = J := by
  cases H; cases J; cases hv; cases he; rfl

lemma L45_image_eq {v m r : ℕ} (Q₁ Q₂ : Finset (Fin v)) (hQ : Q₁ ∪ Q₂ = Finset.univ)
    (κ : Fin v ↪ Fin m) :
    imageHypergraph ((Q₁.powersetCard r ∪ Q₂.powersetCard r).subtype (fun E => E.card = r)) κ =
      hypergraphUnion (complete r (Q₁.map κ)) (complete r (Q₂.map κ)) := by
  apply L45_hyp_ext
  · simp only [imageHypergraph, hypergraphUnion, complete]
    rw [← Finset.map_union, hQ]
  · simp only [imageHypergraph, hypergraphUnion, complete]
    ext E
    simp only [Finset.mem_image, Finset.mem_subtype, Finset.mem_union, Finset.mem_powersetCard,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨E₀, hE₀, rfl⟩
      rcases hE₀ with ⟨h, _⟩ | ⟨h, _⟩
      · left; exact Finset.map_subset_map.mpr h
      · right; exact Finset.map_subset_map.mpr h
    · intro hE
      rcases hE with h | h
      · obtain ⟨u, hu, hEu⟩ := Finset.subset_map_iff.mp h
        have hc : u.card = r := by rw [← E.property, hEu, Finset.card_map]
        refine ⟨⟨u, hc⟩, Or.inl ⟨hu, hc⟩, ?_⟩
        apply Subtype.ext; simp [mapEdge, hEu]
      · obtain ⟨u, hu, hEu⟩ := Finset.subset_map_iff.mp h
        have hc : u.card = r := by rw [← E.property, hEu, Finset.card_map]
        refine ⟨⟨u, hc⟩, Or.inr ⟨hu, hc⟩, ?_⟩
        apply Subtype.ext; simp [mapEdge, hEu]

lemma L45_coeff_sub {X : Type*} [Fintype X] (p : ℝ) (f g : (X → Bool) → ℝ) (S : Finset X) :
    fourierCoeff p (fun x => f x - g x) S = fourierCoeff p f S - fourierCoeff p g S := by
  unfold fourierCoeff OAI.Problem313.BiasedFourier.coeff
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

lemma L45_tail_sub {X : Type*} [Fintype X] (p : ℝ) (f g : (X → Bool) → ℝ) (D : ℕ) :
    fourierTailGT p (fun x => f x - g x) D ≤ 2 * fourierTailGT p f D + 2 * fourierTailGT p g D := by
  unfold fourierTailGT
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun S _ => ?_
  rw [L45_coeff_sub]
  split_ifs
  · nlinarith [sq_nonneg (fourierCoeff p f S + fourierCoeff p g S)]
  · norm_num

lemma L45_tail_nonneg {X : Type*} [Fintype X] (p : ℝ) (f : (X → Bool) → ℝ) (D : ℕ) :
    0 ≤ fourierTailGT p f D := by
  unfold fourierTailGT
  refine Finset.sum_nonneg fun S _ => ?_
  split_ifs
  · positivity
  · norm_num

lemma L45_tail_zero {X : Type*} [Fintype X] (p : ℝ) (f : (X → Bool) → ℝ) (D : ℕ)
    (hf : ∀ x, f x = 0) : fourierTailGT p f D = 0 := by
  unfold fourierTailGT
  refine Finset.sum_eq_zero fun S _ => ?_
  have : fourierCoeff p f S = 0 := by
    unfold fourierCoeff OAI.Problem313.BiasedFourier.coeff
    exact Finset.sum_eq_zero fun x _ => by rw [hf x]; ring
  rw [this]; simp

lemma L45_tail_GT_GE {X : Type*} [Fintype X] (p : ℝ) (f : (X → Bool) → ℝ) (D : ℕ) :
    fourierTailGT p f D = fourierTailGE p f ((D : ℝ) + 1) := by
  unfold fourierTailGT fourierTailGE
  refine Finset.sum_congr rfl fun S _ => ?_
  have : (D < S.card) ↔ ((D : ℝ) + 1 ≤ (S.card : ℝ)) := by
    constructor
    · intro h; exact_mod_cast h
    · intro h; exact_mod_cast h
  simp only [this]

lemma L45_prefix_dup {X : Type} (isAnd : Bool) (inputs : List ((X → Bool) → Bool)) (n : ℕ)
    (hn : n < inputs.length) (hdup : inputs[n] ∈ inputs.take n) :
    abstractPrefix isAnd inputs (n + 1) = abstractPrefix isAnd inputs n := by
  funext x
  unfold abstractPrefix
  rw [List.take_add_one, List.getElem?_eq_getElem hn]
  cases isAnd
  · simp only [Bool.false_eq_true, if_false, Option.toList_some, List.any_append, List.any_cons,
      List.any_nil, Bool.or_false]
    cases hx : inputs[n] x
    · simp
    · have : (List.take n inputs).any (fun f => f x) = true :=
        List.any_eq_true.mpr ⟨_, hdup, hx⟩
      simp [this]
  · simp only [if_true, Option.toList_some, List.all_append, List.all_cons,
      List.all_nil, Bool.and_true]
    cases hx : inputs[n] x
    · have : (List.take n inputs).all (fun f => f x) = false := by
        rw [Bool.eq_false_iff]
        intro h
        have := List.all_eq_true.mp h _ hdup
        rw [hx] at this; exact Bool.false_ne_true this
      simp [this]
    · simp

/-- Only the first occurrence of each input contributes an increment. -/
lemma L45_sum_incr {X : Type} [Fintype X] (p : ℝ) (isAnd : Bool)
    (inputs : List ((X → Bool) → Bool)) (D : ℕ) (b : ℝ)
    (hb : ∀ i ∈ Finset.Icc 1 inputs.length, fourierTailGT p (prefixIncrement isAnd inputs i) D ≤ b) :
    ∑ i ∈ Finset.Icc 1 inputs.length, fourierTailGT p (prefixIncrement isAnd inputs i) D ≤
      (inputs.toFinset.card : ℝ) * b := by
  set I := (Finset.Icc 1 inputs.length).filter
    (fun i => inputs.getD (i - 1) (fun _ => false) ∉ inputs.take (i - 1)) with hI
  have hzero : ∀ i ∈ Finset.Icc 1 inputs.length, i ∉ I →
      fourierTailGT p (prefixIncrement isAnd inputs i) D = 0 := by
    intro i hi hiI
    rw [Finset.mem_Icc] at hi
    have hdup : inputs.getD (i - 1) (fun _ => false) ∈ inputs.take (i - 1) := by
      by_contra hc
      exact hiI (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr hi, hc⟩)
    have hlt : i - 1 < inputs.length := by omega
    rw [List.getD_eq_getElem _ _ hlt] at hdup
    have := L45_prefix_dup isAnd inputs (i - 1) hlt hdup
    obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
    apply L45_tail_zero
    intro x
    simp only [Nat.add_sub_cancel] at this
    unfold prefixIncrement
    simp only [Nat.add_sub_cancel, this, sub_self]
  have hsplit : ∑ i ∈ Finset.Icc 1 inputs.length, fourierTailGT p (prefixIncrement isAnd inputs i) D
      = ∑ i ∈ I, fourierTailGT p (prefixIncrement isAnd inputs i) D := by
    exact (Finset.sum_subset (Finset.filter_subset _ _) hzero).symm
  have hcard : I.card ≤ inputs.toFinset.card := by
    refine Finset.card_le_card_of_injOn (fun i => inputs.getD (i - 1) (fun _ => false)) ?_ ?_
    · intro i hi
      have hi' := Finset.mem_Icc.mp (Finset.mem_filter.mp hi).1
      simp only [Finset.mem_coe, List.mem_toFinset]
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact List.getElem_mem _
    · intro i hi j hj hij
      have hi' := Finset.mem_filter.mp hi
      have hj' := Finset.mem_filter.mp hj
      have hi1 := Finset.mem_Icc.mp hi'.1
      have hj1 := Finset.mem_Icc.mp hj'.1
      simp only at hij
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · apply hj'.2
        rw [← hij, List.getD_eq_getElem _ _ (by omega)]
        rw [List.mem_iff_getElem]
        refine ⟨i - 1, by simp; omega, ?_⟩
        simp
      · apply hi'.2
        rw [hij, List.getD_eq_getElem _ _ (by omega)]
        rw [List.mem_iff_getElem]
        refine ⟨j - 1, by simp; omega, ?_⟩
        simp
  rcases Nat.eq_zero_or_pos inputs.length with h0 | h0
  · have hnil : inputs = [] := List.eq_nil_of_length_eq_zero h0
    subst hnil
    simp
  have hb0 : 0 ≤ b := by
    exact (L45_tail_nonneg _ _ _).trans (hb 1 (Finset.mem_Icc.mpr ⟨le_refl _, h0⟩))
  rw [hsplit]
  calc ∑ i ∈ I, fourierTailGT p (prefixIncrement isAnd inputs i) D ≤ ∑ i ∈ I, b :=
        Finset.sum_le_sum fun i hi => hb i (Finset.mem_filter.mp hi).1
    _ = I.card * b := by simp
    _ ≤ inputs.toFinset.card * b :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hb0


lemma L45_inputs_card {X : Type} [Fintype X] (C : MantriCVQ.ACCircuit X)
    (k : Fin C.gates.length) :
    (gateInputs C k).toFinset.card ≤ C.gates.length + 2 * Fintype.card X + 2 := by
  set S : Finset (MantriCVQ.Src X) :=
    ((Finset.univ : Finset (X × Bool)).image (fun eb => MantriCVQ.Src.lit eb.1 eb.2) ∪
      (Finset.univ : Finset Bool).image MantriCVQ.Src.const) ∪
      (Finset.range C.gates.length).image MantriCVQ.Src.gate with hS
  have hsub : C.gates[k.val].inputs.toFinset ⊆ S := by
    intro s hs
    rw [List.mem_toFinset] at hs
    rw [hS]
    cases s with
    | lit v b => simp
    | const b => simp
    | gate i =>
      have := C.wf k.val k.isLt _ hs i rfl
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
      right; exact ⟨i, by omega, rfl⟩
  have hcS : S.card ≤ C.gates.length + 2 * Fintype.card X + 2 := by
    rw [hS]
    have u1 := Finset.card_union_le
      ((Finset.univ : Finset (X × Bool)).image (fun eb => MantriCVQ.Src.lit eb.1 eb.2) ∪
        (Finset.univ : Finset Bool).image MantriCVQ.Src.const)
      ((Finset.range C.gates.length).image MantriCVQ.Src.gate)
    have u2 := Finset.card_union_le
      ((Finset.univ : Finset (X × Bool)).image (fun eb => MantriCVQ.Src.lit eb.1 eb.2))
        ((Finset.univ : Finset Bool).image MantriCVQ.Src.const)
    have h1 := (Finset.card_image_le (s := (Finset.univ : Finset (X × Bool)))
      (f := fun eb => (MantriCVQ.Src.lit eb.1 eb.2 : MantriCVQ.Src X)))
    have h2 := (Finset.card_image_le (s := (Finset.univ : Finset Bool))
      (f := (MantriCVQ.Src.const : Bool → MantriCVQ.Src X)))
    have h3 := (Finset.card_image_le (s := Finset.range C.gates.length)
      (f := (MantriCVQ.Src.gate : ℕ → MantriCVQ.Src X)))
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_bool, Finset.card_range] at h1 h2 h3
    omega
  unfold gateInputs
  set φ : MantriCVQ.Src X → (X → Bool) → Bool := fun s x => MantriCVQ.Src.eval x (gateValues C x) s
  have h2 : (List.map φ C.gates[k.val].inputs).toFinset ⊆ S.image φ := by
    intro f hf
    rw [List.mem_toFinset, List.mem_map] at hf
    obtain ⟨s, hs, rfl⟩ := hf
    exact Finset.mem_image_of_mem _ (hsub (List.mem_toFinset.mpr hs))
  exact (Finset.card_le_card h2).trans (Finset.card_image_le.trans hcS)

/-- The event for a fixed gate `α` and a fixed pair `(P₁, P₂)`. -/
def L45_ev {m r ℓ : ℕ} (C : MantriCVQ.ACCircuit (Edge m r)) (α : Fin C.gates.length)
    (P₁ P₂ : Finset (Fin ℓ)) (φ : Fin ℓ ↪ Fin m) (G : Edge m r → Bool) : Prop :=
  ∃ j : ℕ, 1 ≤ j ∧ j ≤ (gateInputs C α).length ∧
    spans G (hypergraphUnion (complete r (P₁.map φ)) (complete r (P₂.map φ)))
      (boolReal (gatePrefix C α j))

lemma L45_event (m r s ℓ : ℕ) (hr : 2 ≤ r) (hs : r ≤ s) (hℓm : ℓ < m) (p Λ : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hΛ : 0 < Λ) (hΛ1 : Λ ≤ 1)
    (hlog : (Nat.choose (s - 1) (r - 1) : ℝ) * Real.log (1 / p) ≤ Real.log (1 / Λ))
    (C : MantriCVQ.ACCircuit (Edge m r)) (α : Fin C.gates.length)
    (P₁ P₂ : Finset (Fin ℓ)) (hP₁ : P₁.card ≤ s) (hP₂ : P₂.card ≤ s)
    (hU : s < (P₁ ∪ P₂).card) (D : ℕ) (hD : ℓ ≤ D)
    (hfirst : Real.exp 1 * (D : ℝ) / (m : ℝ) ≤ Λ) (b : ℝ) (hb0 : 0 ≤ b)
    (hb : ∀ i ∈ Finset.Icc 1 (gateInputs C α).length,
      fourierTailGT p (prefixIncrement C.gates[α.val].isAnd (gateInputs C α) i) D ≤ b) :
    jointProbability p (L45_ev C α P₁ P₂) ≤
      Λ ^ s * p ^ (-(Nat.choose s r : ℝ)) +
        p ^ (-(2 * Nat.choose s r : ℝ)) * (((m ^ r) ^ ℓ : ℕ) : ℝ) *
          (((C.gates.length + 2 * Fintype.card (Edge m r) + 2 : ℕ) : ℝ) * b) := by
  set U := P₁ ∪ P₂ with hUdef
  set v := U.card with hv
  set e : Fin v ↪ Fin ℓ := (U.orderEmbOfFin rfl).toEmbedding with he
  have he_mem : ∀ i, e i ∈ U := fun i => U.orderEmbOfFin_mem rfl i
  have he_surj : ∀ a ∈ U, ∃ i, e i = a := by
    intro a ha
    have : a ∈ Set.range (U.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]; exact ha
    obtain ⟨i, hi⟩ := this
    exact ⟨i, hi⟩
  set Q₁ := Finset.univ.filter (fun i => e i ∈ P₁) with hQ₁
  set Q₂ := Finset.univ.filter (fun i => e i ∈ P₂) with hQ₂
  have hQmap : ∀ P : Finset (Fin ℓ), P ⊆ U → (Finset.univ.filter (fun i => e i ∈ P)).map e = P := by
    intro P hP
    ext a
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hi
    · intro ha
      obtain ⟨i, rfl⟩ := he_surj a (hP ha)
      exact ⟨i, ha, rfl⟩
  have hQ₁map : Q₁.map e = P₁ := hQmap P₁ Finset.subset_union_left
  have hQ₂map : Q₂.map e = P₂ := hQmap P₂ Finset.subset_union_right
  have hQU : Q₁ ∪ Q₂ = Finset.univ := by
    ext i
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true, hQ₁, hQ₂]
    exact Finset.mem_union.mp (he_mem i)
  set H₀ := (Q₁.powersetCard r ∪ Q₂.powersetCard r).subtype (fun E => E.card = r) with hH₀
  have hH₀card : H₀.card = (Q₁.powersetCard r ∪ Q₂.powersetCard r).card := by
    rw [hH₀, Finset.card_subtype, Finset.filter_true_of_mem]
    intro E hE
    rcases Finset.mem_union.mp hE with h | h <;> exact (Finset.mem_powersetCard.mp h).2
  -- relabeling
  have hrel : jointProbability p (L45_ev C α P₁ P₂) =
      prefixSpanningProbability p H₀ C.gates[α.val].isAnd (gateInputs C α) := by
    unfold prefixSpanningProbability jointProbability
    rw [← L45_avg hℓm.le e]
    congr 1
    refine Finset.sum_congr rfl fun φ _ => ?_
    congr 1
    funext G
    simp only [L45_ev]
    rw [hH₀, L45_image_eq Q₁ Q₂ hQU, ← Finset.map_map, ← Finset.map_map, hQ₁map, hQ₂map]
    rfl
  have hv1 : 1 ≤ v := by omega
  have hvℓ : v ≤ ℓ := by
    have := Finset.card_le_univ U
    simpa using this
  have h43 := lemma_4_3 m r v hv1 (by omega) p hp hp1 H₀ C.gates[α.val].isAnd (gateInputs C α) D
    (by omega)
  have hQ₁c : Q₁.card ≤ s := by rw [← Finset.card_map e, hQ₁map]; exact hP₁
  have hQ₂c : Q₂.card ≤ s := by rw [← Finset.card_map e, hQ₂map]; exact hP₂
  have hQUc : (Q₁ ∪ Q₂).card = v := by rw [hQU, Finset.card_univ, Fintype.card_fin]
  have h44 := lemma_4_4 r s hr hs Λ p hΛ hΛ1 hp hp1 hlog Q₁ Q₂ hQ₁c hQ₂c
    (by convert hU using 1; convert hQUc)
  have h44' : Λ ^ v * p ^ (-(H₀.card : ℝ)) ≤ Λ ^ s * p ^ (-(Nat.choose s r : ℝ)) := by
    convert h44 using 4
    · convert hQUc.symm
    · rw [hH₀card]; congr!
  -- bounds on |H₀|
  have hH₀le : H₀.card ≤ 2 * Nat.choose s r := by
    rw [hH₀card]
    refine (Finset.card_union_le _ _).trans ?_
    rw [Finset.card_powersetCard, Finset.card_powersetCard]
    have := Nat.choose_le_choose r hQ₁c
    have := Nat.choose_le_choose r hQ₂c
    omega
  have hH₀le2 : H₀.card + 1 ≤ m ^ r := by
    have h1 : H₀.card ≤ v ^ r := by
      rw [hH₀card]
      have hsub : Q₁.powersetCard r ∪ Q₂.powersetCard r ⊆ (Finset.univ : Finset (Fin v)).powersetCard r :=
        Finset.union_subset (Finset.powersetCard_mono (Finset.subset_univ _))
          (Finset.powersetCard_mono (Finset.subset_univ _))
      refine (Finset.card_le_card hsub).trans ?_
      rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
      exact Nat.choose_le_pow _ _
    have h2 : v ^ r + 1 ≤ (v + 1) ^ r := by
      obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      clear * -
      induction r' with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, pow_succ (v + 1)]
        nlinarith [Nat.zero_le (v ^ (k + 1))]
    have h3 : (v + 1) ^ r ≤ m ^ r := Nat.pow_le_pow_left (by omega) r
    omega
  have hpow : (H₀.card + 1) ^ v ≤ (m ^ r) ^ ℓ := by
    calc (H₀.card + 1) ^ v ≤ (m ^ r) ^ v := Nat.pow_le_pow_left hH₀le2 v
      _ ≤ (m ^ r) ^ ℓ := Nat.pow_le_pow_right (Nat.pow_pos (n := r) (by omega : 0 < m)) hvℓ
  rw [hrel]
  refine h43.trans ?_
  have hpH : p ^ (-(H₀.card : ℝ)) ≤ p ^ (-(2 * Nat.choose s r : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_ge hp hp1.le
    have : (H₀.card : ℝ) ≤ 2 * (Nat.choose s r : ℝ) := by exact_mod_cast hH₀le
    linarith
  have hpH0 : 0 ≤ p ^ (-(H₀.card : ℝ)) := (Real.rpow_pos_of_pos hp _).le
  have hfirst0 : 0 ≤ Real.exp 1 * (D : ℝ) / (m : ℝ) := by positivity
  have hsum := L45_sum_incr p C.gates[α.val].isAnd (gateInputs C α) D b hb
  have hT := L45_inputs_card C α
  have hsum2 : ∑ i ∈ Finset.Icc 1 (gateInputs C α).length,
      fourierTailGT p (prefixIncrement C.gates[α.val].isAnd (gateInputs C α) i) D ≤
      ((C.gates.length + 2 * Fintype.card (Edge m r) + 2 : ℕ) : ℝ) * b :=
    hsum.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hT) hb0)
  have hpowR : ((H₀.card : ℝ) + 1) ^ v ≤ (((m ^ r) ^ ℓ : ℕ) : ℝ) := by exact_mod_cast hpow
  rw [mul_add]
  apply add_le_add
  · calc p ^ (-(H₀.card : ℝ)) * (Real.exp 1 * (D : ℝ) / (m : ℝ)) ^ v
        ≤ p ^ (-(H₀.card : ℝ)) * Λ ^ v :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hfirst0 hfirst v) hpH0
      _ = Λ ^ v * p ^ (-(H₀.card : ℝ)) := mul_comm _ _
      _ ≤ _ := h44'
  · have hS0 : 0 ≤ ∑ i ∈ Finset.Icc 1 (gateInputs C α).length,
        fourierTailGT p (prefixIncrement C.gates[α.val].isAnd (gateInputs C α) i) D :=
      Finset.sum_nonneg fun i _ => by
        unfold fourierTailGT
        exact Finset.sum_nonneg fun S _ => by split_ifs <;> positivity
    rw [← mul_assoc]
    apply mul_le_mul _ hsum2 hS0 (by positivity)
    exact mul_le_mul hpH hpowR (by positivity) (Real.rpow_pos_of_pos hp _).le


lemma L45_numeric (m r s ℓ G w : ℕ) (p κ Λ : ℝ) (hr : 2 ≤ r) (hs : r ≤ s) (hsℓ : s < ℓ)
    (hM : 32 ≤ (m : ℝ)) (hp : 0 < p) (hp1 : p < 1) (hκr : (r : ℝ) + 1 ≤ κ)
    (hκℓ : (ℓ : ℝ) ≤ 2 * κ) (hΛ : 0 < Λ) (hΛm : 1 ≤ Λ * m)
    (hlog : (Nat.choose (s - 1) (r - 1) : ℝ) * Real.log (1 / p) ≤ Real.log (1 / Λ))
    (hG : (G : ℝ) ≤ (m : ℝ) ^ κ / 2)
    (hw : (2 * r + 10 : ℝ) * κ * Real.logb 2 m ≤ w) :
    (G : ℝ) * 4 ^ ℓ * (p ^ (-(2 * Nat.choose s r : ℝ)) * (((m ^ r) ^ ℓ : ℕ) : ℝ) *
      (((G + 2 * Nat.choose m r + 2 : ℕ) : ℝ) * (16 * ((G : ℝ) + 2) * (2 : ℝ) ^ (-(w : ℝ))))) ≤
      (m : ℝ) ^ (-κ) := by
  set M : ℝ := (m : ℝ) with hMdef
  have hM0 : 0 < M := by linarith
  have hM1 : 1 ≤ M := by linarith
  have hκ0 : 0 ≤ κ := by linarith
  have hκ1 : 1 ≤ κ := by
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  set N : ℝ := M ^ κ with hN
  have hN32 : 32 ≤ N := by
    calc (32 : ℝ) ≤ M := hM
      _ = M ^ (1 : ℝ) := (Real.rpow_one M).symm
      _ ≤ N := Real.rpow_le_rpow_of_exponent_le hM1 hκ1
  have hN0 : 0 < N := by linarith
  -- powers of M as powers of N
  have hMN : ∀ a : ℕ, M ^ ((a : ℝ) * κ) = N ^ a := by
    intro a
    rw [hN, ← Real.rpow_natCast, ← Real.rpow_mul hM0.le, mul_comm]
  -- (a) G ≤ N
  have hGN : (G : ℝ) ≤ N := by linarith
  -- (b) 4^ℓ ≤ N
  have h4 : (4 : ℝ) ^ ℓ ≤ N := by
    calc (4 : ℝ) ^ ℓ = (4 : ℝ) ^ (ℓ : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ (4 : ℝ) ^ (2 * κ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hκℓ
      _ = ((4 : ℝ) ^ (2 : ℝ)) ^ κ := Real.rpow_mul (by norm_num) _ _
      _ = (16 : ℝ) ^ κ := by norm_num
      _ ≤ N := Real.rpow_le_rpow (by norm_num) (by linarith) hκ0
  -- (c) p^{-2C(s,r)} ≤ N^4
  have hlogp : 0 ≤ Real.log (1 / p) := by
    apply Real.log_nonneg; rw [le_div_iff₀ hp]; linarith
  have hlogΛ : Real.log (1 / Λ) ≤ Real.log M := by
    apply Real.log_le_log (by positivity)
    rw [div_le_iff₀ hΛ]; linarith
  have hchoose : (Nat.choose s r : ℝ) ≤ s * (Nat.choose (s - 1) (r - 1) : ℝ) := by
    have h := Nat.add_one_mul_choose_eq (s - 1) (r - 1)
    have e1 : s - 1 + 1 = s := by omega
    have e2 : r - 1 + 1 = r := by omega
    rw [e1, e2] at h
    have : Nat.choose s r ≤ s * Nat.choose (s - 1) (r - 1) := by
      rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
    exact_mod_cast this
  have hsκ : (s : ℝ) ≤ 2 * κ := by
    have : (s : ℝ) < ℓ := by exact_mod_cast hsℓ
    linarith
  have hpC : p ^ (-(2 * Nat.choose s r : ℝ)) ≤ N ^ 4 := by
    rw [← hMN 4, Real.rpow_def_of_pos hp, Real.rpow_def_of_pos hM0]
    apply Real.exp_le_exp.mpr
    have hl : Real.log p = - Real.log (1 / p) := by
      rw [one_div, Real.log_inv]; ring
    rw [hl]
    have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM1
    have h1 : (Nat.choose s r : ℝ) * Real.log (1 / p) ≤
        s * ((Nat.choose (s - 1) (r - 1) : ℝ) * Real.log (1 / p)) := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hchoose hlogp
    have h2 : (s : ℝ) * ((Nat.choose (s - 1) (r - 1) : ℝ) * Real.log (1 / p)) ≤ s * Real.log M :=
      mul_le_mul_of_nonneg_left (hlog.trans hlogΛ) (by positivity)
    have h3 : (s : ℝ) * Real.log M ≤ 2 * κ * Real.log M := mul_le_mul_of_nonneg_right hsκ hlogM
    push_cast
    nlinarith
  -- (d) (m^r)^ℓ ≤ N^{2r}
  have hmr : (((m ^ r) ^ ℓ : ℕ) : ℝ) ≤ N ^ (2 * r) := by
    rw [← hMN]
    push_cast
    rw [← pow_mul, ← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hM1
    push_cast
    have : (r : ℝ) * ℓ ≤ r * (2 * κ) := mul_le_mul_of_nonneg_left hκℓ (by positivity)
    linarith
  -- (e) T ≤ 2N
  have hT : (((G + 2 * Nat.choose m r + 2 : ℕ) : ℝ)) ≤ 2 * N := by
    have hc : (Nat.choose m r : ℝ) ≤ M ^ r := by
      rw [hMdef]; exact_mod_cast Nat.choose_le_pow m r
    have hMr1 : 1 ≤ M ^ r := one_le_pow₀ hM1
    have hMr : M ^ r * M ≤ N := by
      rw [← pow_succ, ← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le hM1
      push_cast; linarith
    push_cast
    nlinarith
  -- (f) G + 2 ≤ N
  have hG2 : (G : ℝ) + 2 ≤ N := by linarith
  -- (g) N^{2r+10} 2^{-w} ≤ 1
  have hw2 : N ^ (2 * r + 10) * (2 : ℝ) ^ (-(w : ℝ)) ≤ 1 := by
    have hM2 : M = (2 : ℝ) ^ Real.logb 2 M := (Real.rpow_logb (by norm_num) (by norm_num) hM0).symm
    have : N ^ (2 * r + 10) ≤ (2 : ℝ) ^ (w : ℝ) := by
      rw [← hMN, hM2, ← Real.rpow_mul (by norm_num)]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    rw [Real.rpow_neg (by norm_num), ← div_eq_mul_inv, div_le_one (by positivity)]
    exact this
  have hz0 : 0 ≤ (2 : ℝ) ^ (-(w : ℝ)) := by positivity
  have hpC0 : 0 ≤ p ^ (-(2 * Nat.choose s r : ℝ)) := by positivity
  rw [Real.rpow_neg hM0.le, ← hN, inv_eq_one_div, le_div_iff₀ hN0]
  calc (G : ℝ) * 4 ^ ℓ * (p ^ (-(2 * Nat.choose s r : ℝ)) * (((m ^ r) ^ ℓ : ℕ) : ℝ) *
      (((G + 2 * Nat.choose m r + 2 : ℕ) : ℝ) * (16 * ((G : ℝ) + 2) * (2 : ℝ) ^ (-(w : ℝ))))) * N
      ≤ N * N * (N ^ 4 * N ^ (2 * r) * ((2 * N) * (16 * N * (2 : ℝ) ^ (-(w : ℝ))))) * N := by
        gcongr
    _ = 32 * N ^ (2 * r + 9) * (2 : ℝ) ^ (-(w : ℝ)) := by ring
    _ ≤ N * N ^ (2 * r + 9) * (2 : ℝ) ^ (-(w : ℝ)) := by gcongr
    _ = N ^ (2 * r + 10) * (2 : ℝ) ^ (-(w : ℝ)) := by ring
    _ ≤ 1 := hw2

/-- Every increment of a gate of depth at most `h` has a small tail. -/
lemma L45_incr_bound {X : Type} [Fintype X] (h : ℕ) (K : ℝ)
    (hK : ∀ (p : ℝ) (C : MantriCVQ.ACCircuit X) (w : ℕ),
      0 < p → p < 1 → C.depth ≤ h → ∀ D : ℝ, K * (w : ℝ) ^ h ≤ D →
        fourierTailGE p (boolReal C.eval) D ≤
          4 * ((C.gates.length : ℝ) + 1) * (2 : ℝ) ^ (-(w : ℝ)))
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (C : MantriCVQ.ACCircuit X) (α : Fin C.gates.length)
    (hα : gateDepth C α ≤ h) (w D : ℕ) (hD : K * (w : ℝ) ^ h ≤ (D : ℝ) + 1) (i : ℕ) :
    fourierTailGT p (prefixIncrement C.gates[α.val].isAnd (gateInputs C α) i) D ≤
      16 * ((C.gates.length : ℝ) + 2) * (2 : ℝ) ^ (-(w : ℝ)) := by
  have hj : ∀ j, fourierTailGT p (boolReal (abstractPrefix C.gates[α.val].isAnd
      (gateInputs C α) j)) D ≤ 4 * ((C.gates.length : ℝ) + 2) * (2 : ℝ) ^ (-(w : ℝ)) := by
    intro j
    obtain ⟨C', hd, hl, hev⟩ := prefix_circuit C α j
    have he : boolReal (abstractPrefix C.gates[α.val].isAnd (gateInputs C α) j) =
        boolReal C'.eval := by
      funext x; unfold boolReal; rw [hev x]; rfl
    rw [he, L45_tail_GT_GE]
    have := hK p C' w hp hp1 (hd.trans hα) _ hD
    rw [hl] at this
    push_cast at this
    linarith
  have := L45_tail_sub p (boolReal (abstractPrefix C.gates[α.val].isAnd (gateInputs C α) i))
    (boolReal (abstractPrefix C.gates[α.val].isAnd (gateInputs C α) (i - 1))) D
  have h1 := hj i
  have h2 := hj (i - 1)
  unfold prefixIncrement
  linarith

end HypercliqueAC0.FixedDepth

open HypercliqueAC0.FixedDepth in
attribute [local instance] Classical.propDecidable Classical.decEq in
theorem solution (h r : ℕ) (hh : 1 ≤ h) (hr : 2 ≤ r) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ (s ℓ : ℕ) (p κ Λ : ℝ),
      r ≤ s → 1 ≤ ℓ → ℓ < m → 0 < p → p < 1 →
      max ((r : ℝ) + 1) ((ℓ : ℝ) / 2) ≤ κ → 0 < Λ → Λ ≤ 1 →
      κ ^ h * (Real.logb 2 (m : ℝ)) ^ (h + 1) ≤ Λ * (m : ℝ) →
      (Nat.choose (s - 1) (r - 1) : ℝ) * Real.log (1 / p) ≤ Real.log (1 / Λ) →
      ∀ C : MantriCVQ.ACCircuit (Edge m r), C.depth ≤ h + 1 →
        (C.gates.length : ℝ) ≤ (m : ℝ) ^ κ / 2 →
        largeGateProbability p ℓ h s C ≤
          (C.gates.length : ℝ) * (4 : ℝ) ^ ℓ * Λ ^ s *
            p ^ (-(Nat.choose s r : ℝ)) + (m : ℝ) ^ (-κ) := by
  obtain ⟨K₀, hK₀, hK⟩ := tail_biased_weak h hh
  set K : ℝ := max K₀ 1 with hKdef
  have hK1 : 1 ≤ K := le_max_right _ _
  have hK0 : 0 < K := by linarith
  have hKK : ∀ (X : Type) [Fintype X] (p : ℝ) (C : MantriCVQ.ACCircuit X) (w : ℕ),
      0 < p → p < 1 → C.depth ≤ h → ∀ D : ℝ, K * (w : ℝ) ^ h ≤ D →
        fourierTailGE p (boolReal C.eval) D ≤
          4 * ((C.gates.length : ℝ) + 1) * (2 : ℝ) ^ (-(w : ℝ)) := by
    intro X _ p C w hp hp1 hC D hD
    exact hK X p C w hp hp1 hC D
      (le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) hD)
  set c₁ : ℝ := Real.exp 1 * (K * (2 * r + 11 : ℝ) ^ h + 1) with hc₁
  refine ⟨max 32 ⌈(2 : ℝ) ^ c₁⌉₊, ?_⟩
  intro m hm s ℓ p κ Λ hs hℓ hℓm hp hp1 hκ hΛ hΛ1 hmain hlog C hdepth hG
  set M : ℝ := (m : ℝ) with hMdef
  set L : ℝ := Real.logb 2 M with hLdef
  have hM32 : (32 : ℝ) ≤ M := by
    have : 32 ≤ m := le_of_max_le_left hm
    rw [hMdef]; exact_mod_cast this
  have hM0 : 0 < M := by linarith
  have hLc : c₁ ≤ L := by
    rw [hLdef, Real.le_logb_iff_rpow_le (by norm_num) hM0]
    calc (2 : ℝ) ^ c₁ ≤ (⌈(2 : ℝ) ^ c₁⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ M := by rw [hMdef]; exact_mod_cast le_of_max_le_right hm
  have hexp : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have hc1 : 1 ≤ c₁ := by
    have : 0 ≤ K * (2 * r + 11 : ℝ) ^ h := by positivity
    rw [hc₁]; nlinarith
  have hL1 : 1 ≤ L := hc1.trans hLc
  have hκr : (r : ℝ) + 1 ≤ κ := le_of_max_le_left hκ
  have hκℓ : (ℓ : ℝ) ≤ 2 * κ := by
    have := le_of_max_le_right hκ; linarith
  have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hκ1 : 1 ≤ κ := by linarith
  have hκL : 1 ≤ κ * L := by nlinarith
  set w : ℕ := ⌈(2 * r + 10 : ℝ) * κ * L⌉₊ with hwdef
  have hw1 : (2 * r + 10 : ℝ) * κ * L ≤ w := Nat.le_ceil _
  have hw2 : (w : ℝ) ≤ (2 * r + 11 : ℝ) * (κ * L) := by
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (2 * r + 10 : ℝ) * κ * L by positivity)
    rw [← hwdef] at this
    nlinarith
  set D : ℕ := ⌈K * (w : ℝ) ^ h⌉₊ with hDdef
  have hD1 : K * (w : ℝ) ^ h ≤ D := Nat.le_ceil _
  have hD2 : (D : ℝ) ≤ K * (w : ℝ) ^ h + 1 :=
    (Nat.ceil_lt_add_one (show (0 : ℝ) ≤ K * (w : ℝ) ^ h by positivity)).le
  have hℓw : (ℓ : ℝ) ≤ w := by nlinarith
  have hw1' : (1 : ℝ) ≤ w := by
    have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    linarith
  have hDℓ : ℓ ≤ D := by
    have : (ℓ : ℝ) ≤ D := by
      calc (ℓ : ℝ) ≤ w := hℓw
        _ ≤ (w : ℝ) ^ h := le_self_pow₀ hw1' (by omega)
        _ ≤ K * (w : ℝ) ^ h := le_mul_of_one_le_left (by positivity) hK1
        _ ≤ D := hD1
    exact_mod_cast this
  have hfirst : Real.exp 1 * (D : ℝ) / (m : ℝ) ≤ Λ := by
    rw [div_le_iff₀ hM0]
    have hpw : (w : ℝ) ^ h ≤ ((2 * r + 11 : ℝ) * (κ * L)) ^ h :=
      pow_le_pow_left₀ (by positivity) hw2 h
    rw [mul_pow] at hpw
    have h1 : 1 ≤ (κ * L) ^ h := one_le_pow₀ hκL
    have hexp0 : 0 < Real.exp 1 := Real.exp_pos 1
    calc Real.exp 1 * (D : ℝ) ≤ Real.exp 1 * (K * (w : ℝ) ^ h + 1) :=
          mul_le_mul_of_nonneg_left hD2 hexp0.le
      _ ≤ Real.exp 1 * (K * ((2 * r + 11 : ℝ) ^ h * (κ * L) ^ h) + (κ * L) ^ h) := by
          gcongr
      _ = c₁ * (κ * L) ^ h := by rw [hc₁]; ring
      _ ≤ L * (κ * L) ^ h := mul_le_mul_of_nonneg_right hLc (by positivity)
      _ = κ ^ h * L ^ (h + 1) := by ring
      _ ≤ Λ * M := hmain
  have hΛm : 1 ≤ Λ * M := by
    have : 1 ≤ κ ^ h * L ^ (h + 1) := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hκ1)
      (one_le_pow₀ hL1)
    linarith
  -- increments
  set b : ℝ := 16 * ((C.gates.length : ℝ) + 2) * (2 : ℝ) ^ (-(w : ℝ)) with hbdef
  have hb0 : 0 ≤ b := by positivity
  have hb : ∀ α : Fin C.gates.length, gateDepth C α ≤ h → ∀ i,
      fourierTailGT p (prefixIncrement C.gates[α.val].isAnd (gateInputs C α) i) D ≤ b :=
    fun α hα i => L45_incr_bound h K (hKK (Edge m r)) p hp hp1 C α hα w D (by linarith) i
  -- index set
  set pairs : Finset (Finset (Fin ℓ) × Finset (Fin ℓ)) := Finset.univ.filter
    (fun P => P.1.card ≤ s ∧ P.2.card ≤ s ∧ s < (P.1 ∪ P.2).card) with hpairs
  set S := (Finset.univ.filter (fun α : Fin C.gates.length => gateDepth C α ≤ h)) ×ˢ pairs
    with hS
  have hunion : largeGateProbability p ℓ h s C ≤
      ∑ x ∈ S, jointProbability p (L45_ev C x.1 x.2.1 x.2.2) := by
    unfold largeGateProbability
    apply L45_joint_union hp.le hp1.le S
    rintro φ G ⟨k, hk, hlarge⟩
    obtain ⟨α, j, B₁, B₂, hj1, hjlen, hB₁, hB₂, hc₁', hc₂', hcu, hspan, hdα⟩ :=
      lemma_4_1_depth m r s hs G _ C k hlarge
    have hPmap : ∀ B ⊆ Finset.univ.map φ, (Finset.univ.filter (fun a => φ a ∈ B)).map φ = B := by
      intro B hB
      ext y
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨a, ha, rfl⟩; exact ha
      · intro hy
        obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp (hB hy)
        exact ⟨a, hy, rfl⟩
    have h1 := hPmap B₁ hB₁
    have h2 := hPmap B₂ hB₂
    refine ⟨(α, (Finset.univ.filter (fun a => φ a ∈ B₁), Finset.univ.filter (fun a => φ a ∈ B₂))),
      ?_, ?_⟩
    · simp only [hS, hpairs, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hdα.trans hk, ?_, ?_, ?_⟩
      · rw [← Finset.card_map φ, h1]; exact hc₁'
      · rw [← Finset.card_map φ, h2]; exact hc₂'
      · rw [← Finset.card_map φ, Finset.map_union, h1, h2]; exact hcu
    · refine ⟨j, hj1, ?_, ?_⟩
      · simpa [gateInputs] using hjlen
      · simp only
        rw [h1, h2]; exact hspan
  have hcardS : (S.card : ℝ) ≤ (C.gates.length : ℝ) * 4 ^ ℓ := by
    have : S.card ≤ C.gates.length * 4 ^ ℓ := by
      rw [hS, Finset.card_product]
      apply Nat.mul_le_mul
      · exact (Finset.card_filter_le _ _).trans (by simp)
      · refine (Finset.card_filter_le _ _).trans ?_
        simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_finset, Fintype.card_fin]
        rw [← mul_pow]; exact le_of_eq (by norm_num)
    exact_mod_cast this
  set A : ℝ := Λ ^ s * p ^ (-(Nat.choose s r : ℝ)) with hA
  set Bev : ℝ := p ^ (-(2 * Nat.choose s r : ℝ)) * (((m ^ r) ^ ℓ : ℕ) : ℝ) *
          (((C.gates.length + 2 * Fintype.card (Edge m r) + 2 : ℕ) : ℝ) * b) with hBev
  have hev : ∀ x ∈ S, jointProbability p (L45_ev C x.1 x.2.1 x.2.2) ≤ A + Bev := by
    intro x hx
    simp only [hS, hpairs, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact L45_event m r s ℓ hr hs hℓm p Λ hp hp1 hΛ hΛ1 hlog C x.1 x.2.1 x.2.2 hx.2.1 hx.2.2.1
      hx.2.2.2 D hDℓ hfirst b hb0 (fun i _ => hb x.1 hx.1 i)
  have hA0 : 0 ≤ A := by positivity
  have hBev0 : 0 ≤ Bev := by positivity
  have hRHS0 : 0 ≤ (m : ℝ) ^ (-κ) := by positivity
  by_cases hsℓ : s < ℓ
  · have hEdge : Fintype.card (Edge m r) = m.choose r := by
      simp [Edge, Fintype.card_finset_len]
    have hnum := L45_numeric m r s ℓ C.gates.length w p κ Λ hr hs hsℓ hM32 hp hp1 hκr hκℓ hΛ hΛm
      hlog hG hw1
    calc largeGateProbability p ℓ h s C
        ≤ ∑ x ∈ S, jointProbability p (L45_ev C x.1 x.2.1 x.2.2) := hunion
      _ ≤ ∑ x ∈ S, (A + Bev) := Finset.sum_le_sum hev
      _ = (S.card : ℝ) * (A + Bev) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (C.gates.length : ℝ) * 4 ^ ℓ * (A + Bev) :=
          mul_le_mul_of_nonneg_right hcardS (by positivity)
      _ = (C.gates.length : ℝ) * 4 ^ ℓ * A + (C.gates.length : ℝ) * 4 ^ ℓ * Bev := by ring
      _ ≤ (C.gates.length : ℝ) * 4 ^ ℓ * A + (m : ℝ) ^ (-κ) := by
          gcongr
          rw [hBev, hEdge, hbdef]
          exact hnum
      _ = _ := by rw [hA]; ring
  · have hSe : S = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      simp only [hS, hpairs, Finset.mem_product, Finset.mem_filter, Finset.mem_univ,
        true_and] at hx
      have := Finset.card_le_univ (x.2.1 ∪ x.2.2)
      simp only [Fintype.card_fin] at this
      omega
    rw [hSe, Finset.sum_empty] at hunion
    refine hunion.trans ?_
    have : 0 ≤ (C.gates.length : ℝ) * (4 : ℝ) ^ ℓ * Λ ^ s * p ^ (-(Nat.choose s r : ℝ)) := by
      positivity
    linarith


