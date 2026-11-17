-- Prove2me | solution 1 for LinearSetReconciliation327.Main.lemma_5_4
-- status  : ACCEPTED   (prove)
-- author  : @djwj233
-- created : 2026-11-16T16:31:57.109261+00:00
-- url     : https://prove2.me/submissions/09eb0ef5-e023-4fbc-853c-e28ff3b84170

import Mathlib
import Theorems.Thm_LinearSetReconciliation327_Main_lemma_4_8
import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_Framework
import Definitions.Def_LinearSetReconciliation327_Main_HintSketch

set_option autoImplicit false
set_option maxHeartbeats 8000000

open scoped ENNReal
open Finset

namespace LinearSetReconciliation327.Main

/-! ## Toolkit reproduced from Lemma 5.3's development (platform modules export statements only)

The platform's `Theorems.Thm_X` module exports only the theorem `X`, never the helper lemmas of the
file that proved it.  Lemma 5.4 needs two of those internals — the sharp row bound `row_final_sharp`
and the overloaded-mass bound `claim2` — plus the elementary tools they rest on.  Everything below is
copied verbatim from `Solutions/Sol_lemma_5_3.lean` (lines 10–2364), in the same order, so that this
file is self-contained. -/

lemma prU_congr' {α : Type} [Fintype α] {P Q : α → Prop} (h : ∀ a, P a ↔ Q a) :
    prU P = prU Q := by
  classical
  have hf : Finset.univ.filter P = Finset.univ.filter Q := by
    ext a; simp [h a]
  unfold prU
  rw [hf]

lemma prU_mono' {α : Type} [Fintype α] [Nonempty α] {P Q : α → Prop} (h : ∀ a, P a → Q a) :
    prU P ≤ prU Q := by
  classical
  have hpos : (0 : ℝ) < (Fintype.card α : ℝ) := by
    exact_mod_cast (Fintype.card_pos (α := α))
  have hsub : Finset.univ.filter P ⊆ Finset.univ.filter Q := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact h x hx
  have hcard : ((Finset.univ.filter P).card : ℝ) ≤ ((Finset.univ.filter Q).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  unfold prU
  exact (div_le_div_iff_of_pos_right hpos).mpr hcard

lemma prU_le_one {α : Type} [Fintype α] (P : α → Prop) : prU P ≤ 1 := by
  classical
  unfold prU
  rcases Nat.eq_zero_or_pos (Fintype.card α) with h | h
  · have hisempty : IsEmpty α := Fintype.card_eq_zero_iff.mp h
    have h0 : (Finset.univ.filter P).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      exact fun x _ => hisempty.false x
    rw [h0]; simp
  · have hpos : (0:ℝ) < (Fintype.card α : ℝ) := by exact_mod_cast h
    rw [div_le_one hpos]
    exact_mod_cast Finset.card_le_univ _

lemma prU_le_sum' {α ι : Type} [Fintype α] [Nonempty α] (P : α → Prop)
    (s : Finset ι) (Q : ι → α → Prop) (h : ∀ a, P a → ∃ i ∈ s, Q i a) :
    prU P ≤ ∑ i ∈ s, prU (Q i) := by
  classical
  have hsub : Finset.univ.filter P ⊆ s.biUnion (fun i => Finset.univ.filter (Q i)) := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    obtain ⟨i, hi, hia⟩ := h a ha
    exact Finset.mem_biUnion.mpr ⟨i, hi, by simp [hia]⟩
  have hcard : (Finset.univ.filter P).card ≤ ∑ i ∈ s, (Finset.univ.filter (Q i)).card := by
    calc (Finset.univ.filter P).card
        ≤ (s.biUnion (fun i => Finset.univ.filter (Q i))).card := Finset.card_le_card hsub
      _ ≤ ∑ i ∈ s, (Finset.univ.filter (Q i)).card := Finset.card_biUnion_le
  have hcardR : ((Finset.univ.filter P).card : ℝ)
      ≤ ∑ i ∈ s, ((Finset.univ.filter (Q i)).card : ℝ) := by
    exact_mod_cast hcard
  have hpos : (0 : ℝ) < (Fintype.card α : ℝ) := by
    exact_mod_cast (Fintype.card_pos (α := α))
  have hterm : ∀ i ∈ s, ((Finset.univ.filter (Q i)).card : ℝ) / (Fintype.card α : ℝ)
      = prU (Q i) := by
    intro i _; unfold prU; rfl
  unfold prU
  calc ((Finset.univ.filter P).card : ℝ) / (Fintype.card α : ℝ)
      ≤ (∑ i ∈ s, ((Finset.univ.filter (Q i)).card : ℝ)) / (Fintype.card α : ℝ) := by
        apply (div_le_div_iff_of_pos_right hpos).mpr
        exact hcardR
    _ = ∑ i ∈ s, (((Finset.univ.filter (Q i)).card : ℝ) / (Fintype.card α : ℝ)) := by
        rw [Finset.sum_div]
    _ = ∑ i ∈ s, prU (Q i) := Finset.sum_congr rfl hterm

/-- **Zero-fibre of a surjective linear map.** For a surjective `𝔽₂`-linear map the preimage of `0`
carries probability `1/|W|`. -/
lemma prU_ker_eq' {V W : Type} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    [AddCommGroup W] [Module (ZMod 2) W] [Fintype W]
    (ψ : V →ₗ[ZMod 2] W) (hsurj : Function.Surjective ψ) :
    prU (fun x => ψ x = 0) = (Fintype.card W : ℝ)⁻¹ := by
  classical
  have hker : Nat.card (LinearMap.ker ψ)
      = (Finset.univ.filter (fun x : V => ψ x = 0)).card := by
    rw [Nat.card_eq_fintype_card]
    rw [Fintype.card_subtype]
    try simp [LinearMap.mem_ker]
  have hquot : Nat.card (V ⧸ LinearMap.ker ψ) = Fintype.card W := by
    rw [Nat.card_congr (LinearMap.quotKerEquivRange ψ).toEquiv]
    rw [LinearMap.range_eq_top.mpr hsurj]
    rw [Nat.card_congr Submodule.topEquiv.toEquiv, Nat.card_eq_fintype_card]
  have hmain : Nat.card V = (Finset.univ.filter (fun x : V => ψ x = 0)).card * Fintype.card W := by
    rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker ψ), hker, hquot]
  have hcast : (Fintype.card V : ℝ)
      = ((Finset.univ.filter (fun x : V => ψ x = 0)).card : ℝ) * (Fintype.card W : ℝ) := by
    have h := hmain
    rw [Nat.card_eq_fintype_card] at h
    rw [h]
    push_cast
    ring
  have hne : ((Finset.univ.filter (fun x : V => ψ x = 0)).card : ℝ) ≠ 0 := by
    have hmem : (0 : V) ∈ Finset.univ.filter (fun x : V => ψ x = 0) := by simp
    have hpos : 0 < (Finset.univ.filter (fun x : V => ψ x = 0)).card :=
      Finset.card_pos.mpr ⟨0, hmem⟩
    exact_mod_cast hpos.ne'
  have hW : (Fintype.card W : ℝ) ≠ 0 := by
    have hpos : 0 < Fintype.card W := Fintype.card_pos_iff.mpr ⟨0⟩
    exact_mod_cast hpos.ne'
  unfold prU
  rw [hcast]
  field_simp

/-! ## `rowBit` basics -/

lemma rowBit_symmDiff {ℓ K : ℕ} (β : Fin ℓ → Fin K → ZMod 2) (C C' : Finset ℕ) (s : Fin ℓ) :
    HintParams.rowBit β (symmDiff C C') s
      = HintParams.rowBit β C s + HintParams.rowBit β C' s :=
  sum_symmDiff_char_two (fun a : ZMod 2 => CharTwo.add_self_eq_zero a) C C'
    (fun v => if h : v < K then β s ⟨v, h⟩ else 0)

lemma rowBit_add {ℓ K : ℕ} (β β' : Fin ℓ → Fin K → ZMod 2) (C : Finset ℕ) (s : Fin ℓ) :
    HintParams.rowBit (β + β') C s
      = HintParams.rowBit β C s + HintParams.rowBit β' C s := by
  rw [HintParams.rowBit, HintParams.rowBit, HintParams.rowBit]
  have hfun : (fun v => if h : v < K then (β + β') s ⟨v, h⟩ else 0)
      = fun v => (if h : v < K then β s ⟨v, h⟩ else 0)
          + (if h : v < K then β' s ⟨v, h⟩ else 0) := by
    funext v
    by_cases hv : v < K <;> simp [hv, Pi.add_apply]
  rw [hfun, Finset.sum_add_distrib]

lemma rowBit_smul {ℓ K : ℕ} (c : ZMod 2) (β : Fin ℓ → Fin K → ZMod 2) (C : Finset ℕ)
    (s : Fin ℓ) :
    HintParams.rowBit (c • β) C s = c * HintParams.rowBit β C s := by
  rw [HintParams.rowBit, HintParams.rowBit, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  by_cases hv : v < K
  · simp [hv, Pi.smul_apply, smul_eq_mul]
  · simp [hv]

/-! ## The single-candidate separation estimate -/

/-- **Part (c) of the paper's row-recovery proof**, as in the paper (Lemma 4.2,
`lem:random-separation`): for a fixed candidate support `C ≠ S` the probability that the first `a`
row measurements of `C` and `S` agree is `2^{-a}`, provided both lie in `range Nj` with `Nj ≤ K`. -/
theorem prU_prefix_eq {ℓ K Nj a : ℕ} (ha : a ≤ ℓ) (hNjK : Nj ≤ K)
    {C S : Finset ℕ} (hC : C ⊆ range Nj) (hS : S ⊆ range Nj) (hCS : C ≠ S) :
    prU (fun β : Fin ℓ → Fin K → ZMod 2 =>
        ∀ i : Fin a, HintParams.rowBit β C ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩
          = HintParams.rowBit β S ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩)
      = ((2 : ℝ) ^ (a : ℝ))⁻¹ := by
  classical
  set D : Finset ℕ := symmDiff C S with hD
  have hDsub : D ⊆ range Nj := by
    intro x hx
    rw [hD, Finset.mem_symmDiff] at hx
    rcases hx with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hC h1
    · exact hS h1
  have hDne : D.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    apply hCS
    have h1 : ∀ x, x ∈ C ↔ x ∈ S := by
      intro x
      constructor
      · intro hx
        by_contra hxs
        have hmem : x ∈ D := by rw [hD, Finset.mem_symmDiff]; exact Or.inl ⟨hx, hxs⟩
        rw [h] at hmem; exact Finset.notMem_empty x hmem
      · intro hx
        by_contra hxc
        have hmem : x ∈ D := by rw [hD, Finset.mem_symmDiff]; exact Or.inr ⟨hx, hxc⟩
        rw [h] at hmem; exact Finset.notMem_empty x hmem
    ext x; exact h1 x
  obtain ⟨v₀, hv₀⟩ := hDne
  have hv₀K : v₀ < K := Nat.lt_of_lt_of_le (Finset.mem_range.mp (hDsub hv₀)) hNjK
  -- the linear map
  set Φ : (Fin ℓ → Fin K → ZMod 2) →ₗ[ZMod 2] (Fin a → ZMod 2) :=
    { toFun := fun β i => HintParams.rowBit β D ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩
      map_add' := by
        intro x y
        ext i
        exact rowBit_add x y D ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩
      map_smul' := by
        intro c x
        ext i
        simp only [Pi.smul_apply, RingHom.id_apply]
        exact rowBit_smul c x D ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩ } with hΦ
  have hsurj : Function.Surjective Φ := by
    intro w
    refine ⟨fun s w' => if (w' : ℕ) = v₀ then (if h : s.val < a then w ⟨s.val, h⟩ else 0) else 0,
      ?_⟩
    ext i
    have hi : i.val < a := i.isLt
    simp only [hΦ, LinearMap.coe_mk, AddHom.coe_mk]
    rw [HintParams.rowBit, Finset.sum_eq_single v₀]
    · simp [hi, hv₀K]
    · intro b hbD hbne
      have hbK : b < K := Nat.lt_of_lt_of_le (Finset.mem_range.mp (hDsub hbD)) hNjK
      simp [hbK, hbne]
    · intro hnot
      exact absurd hv₀ hnot
  have hiff : ∀ β : Fin ℓ → Fin K → ZMod 2, (Φ β = 0) ↔
      (∀ i : Fin a, HintParams.rowBit β C ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩
        = HintParams.rowBit β S ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩) := by
    intro β
    constructor
    · intro h i
      have h1 := congr_fun h i
      simp only [hΦ, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at h1
      have h2 : HintParams.rowBit β D ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩
          = HintParams.rowBit β C ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩
            + HintParams.rowBit β S ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩ := by
        rw [hD]; exact rowBit_symmDiff β C S _
      rw [h2] at h1
      have hy : HintParams.rowBit β S ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩
          + HintParams.rowBit β S ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩ = 0 :=
        CharTwo.add_self_eq_zero _
      have hh : HintParams.rowBit β C ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩
            + HintParams.rowBit β S ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩
          = HintParams.rowBit β S ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩
            + HintParams.rowBit β S ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩ := by
        rw [h1, hy]
      exact add_right_cancel hh
    · intro h
      funext i
      simp only [hΦ, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
      have h2 : HintParams.rowBit β D ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩
          = HintParams.rowBit β C ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩
            + HintParams.rowBit β S ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩ := by
        rw [hD]; exact rowBit_symmDiff β C S _
      rw [h2, h i]
      exact CharTwo.add_self_eq_zero _
  rw [prU_congr' (fun β => (hiff β).symm)]
  rw [prU_ker_eq' Φ hsurj]
  have hcard : Fintype.card (Fin a → ZMod 2) = 2 ^ a := by
    rw [Fintype.card_fun, Fintype.card_fin, ZMod.card]
  rw [hcard, Nat.cast_pow, ← Real.rpow_natCast]
  norm_num

/-! ## Union bound over the candidate family -/

/-- If `C ≠ S`, the first `a` row measurements of `C` and `S` agree with probability `2^{-a}`; a union
bound over the candidate family `Ah` gives the failure probability. -/
theorem prU_exists_prefix_eq {ℓ K Nj a : ℕ} (ha : a ≤ ℓ) (hNjK : Nj ≤ K)
    {S : Finset ℕ} (hS : S ⊆ range Nj) (Ah : Finset (Finset ℕ))
    (hAh : ∀ C ∈ Ah, C ⊆ range Nj) :
    prU (fun β : Fin ℓ → Fin K → ZMod 2 =>
        ∃ C ∈ Ah.erase S, ∀ i : Fin a,
          HintParams.rowBit β C ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩
            = HintParams.rowBit β S ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩)
      ≤ ((Ah.erase S).card : ℝ) * ((2 : ℝ) ^ (a : ℝ))⁻¹ := by
  classical
  haveI : Nonempty (Fin ℓ → Fin K → ZMod 2) := ⟨fun _ _ => 0⟩
  have hub := prU_le_sum'
    (P := fun β : Fin ℓ → Fin K → ZMod 2 =>
      ∃ C ∈ Ah.erase S, ∀ i : Fin a,
        HintParams.rowBit β C ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩
          = HintParams.rowBit β S ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩)
    (s := Ah.erase S)
    (Q := fun C β => ∀ i : Fin a,
        HintParams.rowBit β C ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩
          = HintParams.rowBit β S ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩)
    (fun _ hβ => hβ)
  calc prU (fun β : Fin ℓ → Fin K → ZMod 2 =>
        ∃ C ∈ Ah.erase S, ∀ i : Fin a,
          HintParams.rowBit β C ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩
            = HintParams.rowBit β S ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩)
      ≤ ∑ C ∈ Ah.erase S, prU (fun β : Fin ℓ → Fin K → ZMod 2 => ∀ i : Fin a,
          HintParams.rowBit β C ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩
            = HintParams.rowBit β S ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩) := hub
    _ = ∑ C ∈ Ah.erase S, ((2 : ℝ) ^ (a : ℝ))⁻¹ := by
        refine Finset.sum_congr rfl (fun C hC => ?_)
        exact prU_prefix_eq ha hNjK (hAh C (Finset.mem_erase.mp hC).2) hS
          (Finset.mem_erase.mp hC).1
    _ = ((Ah.erase S).card : ℝ) * ((2 : ℝ) ^ (a : ℝ))⁻¹ := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-! ## Counting the candidate supports -/

/-- The candidate supports in `range Nj` with at most `y` coordinates outside `Jj`. -/
def candSet (Nj : ℕ) (Jj : Finset ℕ) (y : ℕ) : Finset (Finset ℕ) :=
  (range Nj).powerset.filter (fun C => (C \ Jj).card ≤ y)

/-- `(C ∩ Jj) ∪ (C \ Jj) = C`. -/
lemma eq_inter_union_sdiff (C Jj : Finset ℕ) : (C ∩ Jj) ∪ (C \ Jj) = C := by
  ext x
  simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
  tauto

/-- The number of supports in `range Nj` with exactly `r` coordinates outside `Jj`. -/
lemma card_candidates_eq {Nj : ℕ} (Jj : Finset ℕ) (hJj : Jj ⊆ range Nj) (r : ℕ) :
    ((range Nj).powerset.filter (fun C => (C \ Jj).card = r)).card
      = 2 ^ Jj.card * (Nj - Jj.card).choose r := by
  classical
  set D : Finset ℕ := range Nj \ Jj with hDdef
  have hDcard : D.card = Nj - Jj.card := by
    rw [hDdef, Finset.card_sdiff, Finset.inter_eq_left.mpr hJj, Finset.card_range]
  have hbij : ((range Nj).powerset.filter (fun C => (C \ Jj).card = r)).card
      = (Jj.powerset ×ˢ D.powersetCard r).card := by
    refine Finset.card_bij (fun C _ => (C ∩ Jj, C \ Jj)) ?_ ?_ ?_
    · intro C hC
      simp only [Finset.mem_filter, Finset.mem_powerset] at hC
      obtain ⟨hCsub, hCcard⟩ := hC
      rw [Finset.mem_product, Finset.mem_powersetCard, Finset.mem_powerset]
      refine ⟨Finset.inter_subset_right, ?_, hCcard⟩
      intro x hx
      rw [hDdef, Finset.mem_sdiff]
      exact ⟨hCsub (Finset.mem_sdiff.mp hx).1, (Finset.mem_sdiff.mp hx).2⟩
    · intro C1 _ C2 _ heq
      simp only [Prod.mk.injEq] at heq
      obtain ⟨h1, h2⟩ := heq
      calc C1 = (C1 ∩ Jj) ∪ (C1 \ Jj) := (eq_inter_union_sdiff C1 Jj).symm
        _ = (C2 ∩ Jj) ∪ (C2 \ Jj) := by rw [h1, h2]
        _ = C2 := eq_inter_union_sdiff C2 Jj
    · intro p hp
      rw [Finset.mem_product, Finset.mem_powersetCard, Finset.mem_powerset] at hp
      obtain ⟨hPsub, hQsub, hQcard⟩ := hp
      have hQJ : ∀ x, x ∈ p.2 → x ∉ Jj := by
        intro x hx
        have h := hQsub hx
        rw [hDdef, Finset.mem_sdiff] at h
        exact h.2
      have hCJ : (p.1 ∪ p.2) ∩ Jj = p.1 := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨hx | hx, hxj⟩
          · exact hx
          · exact absurd hxj (hQJ x hx)
        · intro hx; exact ⟨Or.inl hx, hPsub hx⟩
      have hCsd : (p.1 ∪ p.2) \ Jj = p.2 := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨hx | hx, hxj⟩
          · exact absurd (hPsub hx) hxj
          · exact hx
        · intro hx; exact ⟨Or.inr hx, hQJ x hx⟩
      refine ⟨p.1 ∪ p.2, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_powerset]
        refine ⟨?_, by rw [hCsd, hQcard]⟩
        intro x hx
        rcases Finset.mem_union.mp hx with h | h
        · exact hJj (hPsub h)
        · have h' := hQsub h
          rw [hDdef, Finset.mem_sdiff] at h'
          exact h'.1
      · simp only [hCJ, hCsd]
  rw [hbij, Finset.card_product, Finset.card_powerset, Finset.card_powersetCard, hDcard]

/-- The number of supports in `range Nj` with at most `y` coordinates outside `Jj`. -/
lemma card_candidates_le_eq {Nj : ℕ} (Jj : Finset ℕ) (hJj : Jj ⊆ range Nj) (y : ℕ) :
    ((range Nj).powerset.filter (fun C => (C \ Jj).card ≤ y)).card
      = 2 ^ Jj.card * ∑ h ∈ range (y + 1), (Nj - Jj.card).choose h := by
  classical
  set A : Finset (Finset ℕ) := (range Nj).powerset.filter (fun C => (C \ Jj).card ≤ y) with hA
  have hmap : Set.MapsTo (fun C => (C \ Jj).card) ↑A ↑(range (y + 1)) := by
    intro C hC
    simp only [hA, Finset.coe_filter, Set.mem_setOf_eq] at hC
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hC.2)
  have hfib : ∀ r ∈ range (y + 1),
      {C ∈ A | (C \ Jj).card = r}.card = 2 ^ Jj.card * (Nj - Jj.card).choose r := by
    intro r hr
    have hrle : r ≤ y := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    have hset : {C ∈ A | (C \ Jj).card = r}
        = (range Nj).powerset.filter (fun C => (C \ Jj).card = r) := by
      ext C
      simp only [hA, Finset.mem_filter, Finset.mem_powerset]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by rw [h3]; exact hrle⟩, h3⟩
    rw [hset, card_candidates_eq Jj hJj r]
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  calc ∑ r ∈ range (y + 1), {C ∈ A | (C \ Jj).card = r}.card
      = ∑ r ∈ range (y + 1), 2 ^ Jj.card * (Nj - Jj.card).choose r :=
        Finset.sum_congr rfl hfib
    _ = 2 ^ Jj.card * ∑ r ∈ range (y + 1), (Nj - Jj.card).choose r := by
        rw [Finset.mul_sum]

/-- The candidate family of supports with at most `y` outside coordinates is no larger than
`2 ^ σ_{j,y}`. -/
theorem card_candidates_le_two_pow_sigma {Nj : ℕ} (Jj : Finset ℕ) (hJj : Jj ⊆ range Nj) (y : ℕ) :
    ((candSet Nj Jj y).card : ℝ)
      ≤ (2 : ℝ) ^ (HintParams.sigma Jj.card Nj y : ℝ) := by
  classical
  have hval0 : candSet Nj Jj y = (range Nj).powerset.filter (fun C => (C \ Jj).card ≤ y) := rfl
  rw [hval0]
  set X : ℕ := 2 ^ Jj.card * ∑ h ∈ range (y + 1), (Nj - Jj.card).choose h with hX
  have hXpos : 0 < X := by
    rw [hX]
    have h1 : 0 < 2 ^ Jj.card := by positivity
    have h2 : 0 < ∑ h ∈ range (y + 1), (Nj - Jj.card).choose h := by
      have hmem : 0 ∈ range (y + 1) := Finset.mem_range.mpr (Nat.succ_pos y)
      have hle := Finset.single_le_sum (f := fun h => (Nj - Jj.card).choose h)
        (fun i _ => Nat.zero_le _) hmem
      rw [Nat.choose_zero_right] at hle
      exact Nat.lt_of_lt_of_le Nat.one_pos hle
    exact Nat.mul_pos h1 h2
  have hval : (((range Nj).powerset.filter (fun C => (C \ Jj).card ≤ y)).card : ℝ) = (X : ℝ) := by
    rw [card_candidates_le_eq Jj hJj y, hX]
  rw [hval]
  have hceil : Real.logb 2 (X : ℝ) ≤ (HintParams.sigma Jj.card Nj y : ℝ) := by
    rw [HintParams.sigma]
    exact Nat.le_ceil _
  calc (X : ℝ) = (2 : ℝ) ^ Real.logb 2 (X : ℝ) := by
        rw [Real.rpow_logb (by norm_num) (by norm_num) (by exact_mod_cast hXpos)]
    _ ≤ (2 : ℝ) ^ (HintParams.sigma Jj.card Nj y : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hceil

/-! ## Auxiliary list facts -/

lemma mem_take_finRange {ℓ a : ℕ} {x : Fin ℓ} (h : x ∈ List.take a (List.finRange ℓ)) :
    x.val < a := by
  rw [List.mem_take_iff_getElem] at h
  obtain ⟨j, hj, hje⟩ := h
  have hj2 : j < (List.finRange ℓ).length := by omega
  have h1 : (List.finRange ℓ)[j]'hj2 = x := by rw [← hje]
  have h2 : ((List.finRange ℓ)[j]'hj2).val = j := by
    rw [List.getElem_finRange]
    simp
  have hx : x.val = j := by rw [← h1]; exact h2
  omega

/-- Pointwise form of equality of the two prefixes. -/
lemma forall_prefix_eq_iff {ℓ a : ℕ} (ha : a ≤ ℓ) {β β' : Fin ℓ → ZMod 2} :
    (List.take a (List.finRange ℓ)).map β = (List.take a (List.finRange ℓ)).map β'
      ↔ ∀ i : Fin a, β ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩
          = β' ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩ := by
  rw [List.map_inj_left]
  constructor
  · intro h i
    refine h ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩ ?_
    rw [List.mem_take_iff_getElem]
    refine ⟨i.val, ?_, ?_⟩
    · rw [List.length_finRange]
      exact Nat.lt_min.mpr ⟨i.isLt, Nat.lt_of_lt_of_le i.isLt ha⟩
    · rw [List.getElem_finRange]
      exact Fin.ext rfl
  · intro h s hs
    have := mem_take_finRange (ℓ := ℓ) (a := a) hs
    exact h ⟨s.val, this⟩

/-- **Part (c) of the paper's row-recovery proof, union-bound form**, as in the paper
(Lemma 4.2, `lem:random-separation`) combined with a union bound: the probability that *some*
candidate in `Ah \ {S}` matches the first `a` measurements is at most `|Ah| · 2^{-a}`.  At `a = ℓ`
this is the paper's `2^{-ℓ}` separation step. -/
theorem prU_exists_prefix_eq_list {ℓ K Nj a : ℕ} (ha : a ≤ ℓ) (hNjK : Nj ≤ K)
    {S : Finset ℕ} (hS : S ⊆ range Nj) (Ah : Finset (Finset ℕ))
    (hAh : ∀ C ∈ Ah, C ⊆ range Nj) :
    prU (fun β : Fin ℓ → Fin K → ZMod 2 =>
        ∃ C ∈ Ah.erase S, (List.take a (List.finRange ℓ)).map (HintParams.rowBit β C)
          = (List.take a (List.finRange ℓ)).map (HintParams.rowBit β S))
      ≤ ((Ah.erase S).card : ℝ) * ((2 : ℝ) ^ (a : ℝ))⁻¹ := by
  classical
  have hiff : ∀ β : Fin ℓ → Fin K → ZMod 2,
      (∃ C ∈ Ah.erase S, (List.take a (List.finRange ℓ)).map (HintParams.rowBit β C)
          = (List.take a (List.finRange ℓ)).map (HintParams.rowBit β S))
      ↔ (∃ C ∈ Ah.erase S, ∀ i : Fin a,
          HintParams.rowBit β C ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩
            = HintParams.rowBit β S ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩) := by
    intro β
    constructor
    · rintro ⟨C, hC, hCe⟩
      exact ⟨C, hC, (forall_prefix_eq_iff ha).mp hCe⟩
    · rintro ⟨C, hC, hCe⟩
      exact ⟨C, hC, (forall_prefix_eq_iff ha).mpr hCe⟩
  rw [prU_congr' hiff]
  exact prU_exists_prefix_eq ha hNjK hS Ah hAh

/-- `Option.map` of the head of the singleton list. -/
lemma toList_head?_singleton_map {α β : Type} (a : α) (f : α → β) :
    Option.map f (({a} : Finset α).toList.head?) = some (f a) := by
  rw [Finset.toList_singleton]
  rfl
/-! ## Numeric facts about the row geometry -/

/-- Under the standing assumptions of a non-leaf node, there is at least one row. -/
lemma rows_pos (P : HintParams) (N X Y : ℕ) (hargs : P.NodeArgs N X Y) (hnl : P.NonLeaf N X Y) :
    1 ≤ P.rows X Y := by
  by_contra h
  have hm0 : P.rows X Y = 0 := by omega
  have hlgn : 0 < P.lgn := by
    rw [HintParams.lgn, lg]
    exact Real.logb_pos (by norm_num) (by exact_mod_cast hargs.1)
  have hY : Y = 0 := by
    have h1 : Y ≤ P.rows X Y := le_max_left _ _
    omega
  have hX : X = 0 := by
    have hc : ⌈(X:ℝ) / P.lgn ^ 3⌉₊ = 0 := by
      have h2 : ⌈(X:ℝ)/P.lgn^3⌉₊ ≤ P.rows X Y := le_max_right _ _
      omega
    have hpos : (0:ℝ) < P.lgn ^ 3 := by positivity
    have hle : (X:ℝ) ≤ 0 := by
      by_contra hh
      rw [not_le] at hh
      have h3 : 0 < (X:ℝ)/P.lgn^3 := div_pos hh hpos
      have h4 := Nat.le_ceil ((X:ℝ)/P.lgn^3)
      rw [hc] at h4
      simp at h4
      linarith
    have h5 : (X:ℝ) = 0 := le_antisymm hle (Nat.cast_nonneg X)
    exact_mod_cast h5
  have hD : HintParams.D N X Y = 0 := by
    rw [HintParams.D, hX, hY]
    simp
  have hrule : P.rule N X Y = HintParams.Rule.cheap := by
    rw [HintParams.rule, hD]
    simp only [Nat.cast_zero]
    rw [if_pos (show (0:ℝ) ≤ (N:ℝ) / P.lgn ^ 10 by positivity)]
  rcases hnl with hh | hh
  · rw [hrule] at hh
    exact absurd hh (by decide)
  · rw [hrule] at hh
    exact absurd hh (by decide)

/-- A row of `m ≥ 1` rows has at most `⌈N/m⌉` coordinates. -/
lemma rowLen_le_Nmax (N m j : ℕ) (hm : 1 ≤ m) :
    rowLen N m j ≤ ⌈(N : ℝ) / (m : ℝ)⌉₊ := by
  classical
  have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  unfold rowLen
  have hmaps : ∀ p ∈ (range N).filter (fun p => p % m = j),
      p / m ∈ range ⌈(N:ℝ)/(m:ℝ)⌉₊ := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_range] at hp
    rw [Finset.mem_range]
    have hpN' : (p : ℝ) < (N : ℝ) := by exact_mod_cast hp.1
    have hdiv : (p : ℝ) / (m : ℝ) < (N : ℝ) / (m : ℝ) := div_lt_div_of_pos_right hpN' hmpos
    have hpm : ((p / m : ℕ) : ℝ) ≤ (p : ℝ) / (m : ℝ) := Nat.cast_div_le
    have h3 : ((p / m : ℕ) : ℝ) < (⌈(N:ℝ)/(m:ℝ)⌉₊ : ℝ) := by
      have h4 := Nat.le_ceil ((N:ℝ)/(m:ℝ))
      linarith
    exact_mod_cast h3
  have hinj : Set.InjOn (fun p => p / m) ↑((range N).filter (fun p => p % m = j)) := by
    intro p hp q hq heq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hp hq
    have heq' : p / m = q / m := heq
    have e1 : p = m * (p/m) + j := by rw [← hp.2]; exact (Nat.div_add_mod p m).symm
    have e2 : q = m * (q/m) + j := by rw [← hq.2]; exact (Nat.div_add_mod q m).symm
    rw [e1, e2, heq']
  have hres := Finset.card_le_card_of_injOn (fun p => p / m) (by
    intro p hp
    exact hmaps p (by simpa using hp)) hinj
  simpa [Finset.card_range] using hres

lemma card_powersetCard_filter_subset {N : ℕ} (A : Finset (Fin N)) {K : ℕ} (hA : A.card ≤ K) :
    ((powersetCard K (univ : Finset (Fin N))).filter (fun S => A ⊆ S)).card
      = (N - A.card).choose (K - A.card) := by
  classical
  have hcard : (univ \ A : Finset (Fin N)).card = N - A.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ A), Finset.card_univ,
      Fintype.card_fin]
  have key : ((powersetCard K (univ : Finset (Fin N))).filter (fun S => A ⊆ S)).card
      = (powersetCard (K - A.card) (univ \ A)).card := by
    refine Finset.card_bij (fun S _ => S \ A) ?_ ?_ ?_
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_powersetCard] at hS ⊢
      obtain ⟨⟨-, hScard⟩, hAS⟩ := hS
      refine ⟨?_, ?_⟩
      · intro x hx
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hx ⊢
        exact hx.2
      · rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hAS, hScard]
    · intro S1 hS1 S2 hS2 heq
      simp only [Finset.mem_filter] at hS1 hS2
      rw [← Finset.union_sdiff_of_subset hS1.2, ← Finset.union_sdiff_of_subset hS2.2, heq]
    · intro T hT
      simp only [Finset.mem_powersetCard] at hT
      obtain ⟨hTsub, hTcard⟩ := hT
      have hTdisj : Disjoint A T := Finset.disjoint_left.mpr fun x hxA hxT => by
        have hx := hTsub hxT
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hx
        exact hx hxA
      refine ⟨A ∪ T, ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨by simp, ?_⟩,
          Finset.subset_union_left⟩
        rw [Finset.card_union_of_disjoint hTdisj, hTcard]
        omega
      · ext x
        simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨hxA | hxT, hxnA⟩
          · exact absurd hxA hxnA
          · exact hxT
        · intro hxT
          have hx := hTsub hxT
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hx
          exact ⟨Or.inr hxT, hx⟩
  rw [key, Finset.card_powersetCard, hcard]

/-- `C(N-r, K-r) * (N)_r = C(N,K) * (K)_r` where `(x)_r` is the falling factorial. -/
lemma choose_mul_descFactorial {N K r : ℕ} (hKN : K ≤ N) (hr : r ≤ K) :
    (N - r).choose (K - r) * N.descFactorial r = N.choose K * K.descFactorial r := by
  have h1 : (N - r).choose (K - r) * (K - r).factorial * (N - K).factorial = (N - r).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (n := N - r) (k := K - r) (by omega)
    rwa [show N - r - (K - r) = N - K by omega] at h
  have h2 : N.choose K * K.factorial * (N - K).factorial = N.factorial :=
    Nat.choose_mul_factorial_mul_factorial (n := N) (k := K) hKN
  have h3 : (N - r).factorial * N.descFactorial r = N.factorial := by
    have h := Nat.descFactorial_mul_descFactorial (k := r) (m := N) (n := N) (by omega : r ≤ N)
    rwa [Nat.descFactorial_self, Nat.descFactorial_self] at h
  have h4 : (K - r).factorial * K.descFactorial r = K.factorial := by
    have h := Nat.descFactorial_mul_descFactorial (k := r) (m := K) (n := K) hr
    rwa [Nat.descFactorial_self, Nat.descFactorial_self] at h
  have hmain : ((N - r).choose (K - r) * N.descFactorial r)
        * ((K - r).factorial * (N - K).factorial)
      = (N.choose K * K.descFactorial r) * ((K - r).factorial * (N - K).factorial) := by
    calc ((N - r).choose (K - r) * N.descFactorial r) * ((K - r).factorial * (N - K).factorial)
        = ((N - r).choose (K - r) * (K - r).factorial * (N - K).factorial)
            * N.descFactorial r := by ring
      _ = (N - r).factorial * N.descFactorial r := by rw [h1]
      _ = N.factorial := h3
      _ = (N.choose K * K.factorial) * (N - K).factorial := by rw [h2]
      _ = (N.choose K * K.descFactorial r) * ((K - r).factorial * (N - K).factorial) := by
            rw [← h4]; ring
  exact Nat.mul_right_cancel (by positivity) hmain

/-- `(K)_r * N^r ≤ (N)_r * K^r`. -/
lemma descFactorial_mul_pow_le {N K r : ℕ} (hKN : K ≤ N) (hr : r ≤ K) :
    K.descFactorial r * N ^ r ≤ N.descFactorial r * K ^ r := by
  have hL : (∏ i ∈ Finset.range r, (K - i)) * N ^ r = ∏ i ∈ Finset.range r, ((K - i) * N) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  have hR : (∏ i ∈ Finset.range r, (N - i)) * K ^ r = ∏ i ∈ Finset.range r, ((N - i) * K) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  rw [Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_prod_range, hL, hR]
  refine Finset.prod_le_prod' fun i hi => ?_
  simp only [Finset.mem_range] at hi
  have hiK : i ≤ K := by omega
  have hiN : i ≤ N := by omega
  rw [Nat.sub_mul, Nat.sub_mul, Nat.mul_comm K N]
  exact Nat.sub_le_sub_left (Nat.mul_le_mul_left i hKN) _

/-- The hypergeometric ratio bound: `C(N-r,K-r) * N^r ≤ C(N,K) * K^r`. -/
lemma choose_sub_mul_pow_le {N K r : ℕ} (hKN : K ≤ N) (hr : r ≤ K) :
    (N - r).choose (K - r) * N ^ r ≤ N.choose K * K ^ r := by
  have hstar := choose_mul_descFactorial hKN hr
  have hprod := descFactorial_mul_pow_le hKN hr
  have key : (N - r).choose (K - r) * N.descFactorial r * N ^ r
      ≤ N.choose K * N.descFactorial r * K ^ r := by
    rw [hstar]
    calc N.choose K * K.descFactorial r * N ^ r = N.choose K * (K.descFactorial r * N ^ r) := by
          ring
      _ ≤ N.choose K * (N.descFactorial r * K ^ r) := Nat.mul_le_mul_left _ hprod
      _ = N.choose K * N.descFactorial r * K ^ r := by ring
  have hrN : r ≤ N := le_trans hr hKN
  have hD : 0 < N.descFactorial r := Nat.descFactorial_pos.mpr hrN
  refine Nat.le_of_mul_le_mul_left ?_ hD
  calc N.descFactorial r * ((N - r).choose (K - r) * N ^ r)
      = (N - r).choose (K - r) * N.descFactorial r * N ^ r := by ring
    _ ≤ N.choose K * N.descFactorial r * K ^ r := key
    _ = N.descFactorial r * (N.choose K * K ^ r) := by ring

/-- The hypergeometric ratio bound in the form used below. -/
lemma choose_sub_le_pow_mul {N K r : ℕ} (hN : 0 < N) (hKN : K ≤ N) (hr : r ≤ K) :
    ((N - r).choose (K - r) : ℝ) ≤ ((K : ℝ) / (N : ℝ)) ^ r * (N.choose K : ℝ) := by
  have hnat := choose_sub_mul_pow_le hKN hr
  have hcast : ((N - r).choose (K - r) : ℝ) * (N : ℝ) ^ r
      ≤ (N.choose K : ℝ) * (K : ℝ) ^ r := by
    exact_mod_cast hnat
  have hNr : (0 : ℝ) < (N : ℝ) ^ r := pow_pos (by exact_mod_cast hN) r
  rw [div_pow]
  have h2 : (K : ℝ) ^ r / (N : ℝ) ^ r * (N.choose K : ℝ)
      = (K : ℝ) ^ r * (N.choose K : ℝ) / (N : ℝ) ^ r := by ring
  rw [h2, le_div_iff₀ hNr]
  linarith [hcast]

/-- The moment generating function bound for the hypergeometric law, in counting form:
`∑_{|S|=K} (1+u)^{|S∩I|} ≤ C(N,K) · exp(μ u)` where `μ = K|I|/N`. -/
theorem mgf_le {N K : ℕ} (hN : 0 < N) (hKN : K ≤ N) (I : Finset (Fin N)) {u : ℝ} (hu : 0 ≤ u) :
    ∑ S ∈ powersetCard K (univ : Finset (Fin N)), (1 + u) ^ ((S ∩ I).card)
      ≤ (N.choose K : ℝ) * Real.exp ((K : ℝ) * (I.card : ℝ) / (N : ℝ) * u) := by
  classical
  -- STEP 1: expand `(1+u)^{|S∩I|}` as a sum over the subsets of `S ∩ I`
  have hterm : ∀ S ∈ powersetCard K (univ : Finset (Fin N)),
      (1 + u) ^ ((S ∩ I).card) = ∑ A ∈ I.powerset, if A ⊆ S then u ^ A.card else 0 := by
    intro S _
    have hexp : (1 + u) ^ ((S ∩ I).card) = ∑ A ∈ (S ∩ I).powerset, u ^ A.card := by
      have h := Finset.sum_pow_mul_eq_add_pow u (1 : ℝ) (S ∩ I)
      simpa [add_comm] using h.symm
    have hset : (S ∩ I).powerset = I.powerset.filter (fun A => A ⊆ S) := by
      ext A
      simp only [Finset.mem_powerset, Finset.mem_filter]
      constructor
      · intro h
        refine ⟨?_, ?_⟩
        · intro x hx; exact (Finset.mem_inter.mp (h hx)).2
        · intro x hx; exact (Finset.mem_inter.mp (h hx)).1
      · rintro ⟨h1, h2⟩ x hx
        exact Finset.mem_inter.mpr ⟨h2 hx, h1 hx⟩
    rw [hexp, hset, Finset.sum_filter]
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  -- STEP 2: evaluate the inner sum
  have hinner : ∀ A ∈ I.powerset,
      ∑ S ∈ powersetCard K (univ : Finset (Fin N)), (if A ⊆ S then u ^ A.card else 0)
        = u ^ A.card *
            (((powersetCard K (univ : Finset (Fin N))).filter (fun S => A ⊆ S)).card : ℝ) := by
    intro A _
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl hinner]
  -- STEP 3: bound each term by the binomial ratio bound
  have hbound : ∀ A ∈ I.powerset,
      u ^ A.card *
          (((powersetCard K (univ : Finset (Fin N))).filter (fun S => A ⊆ S)).card : ℝ)
        ≤ u ^ A.card * (((K : ℝ) / (N : ℝ)) ^ A.card * (N.choose K : ℝ)) := by
    intro A _
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hu _)
    by_cases haK : A.card ≤ K
    · rw [card_powersetCard_filter_subset A haK]
      exact choose_sub_le_pow_mul hN hKN haK
    · have haK' : K < A.card := not_le.mp haK
      have hzero : ((powersetCard K (univ : Finset (Fin N))).filter (fun S => A ⊆ S)).card = 0 := by
        have hempty : (powersetCard K (univ : Finset (Fin N))).filter (fun S => A ⊆ S) = ∅ := by
          refine Finset.filter_false_of_mem ?_
          intro S hS hAS
          simp only [Finset.mem_powersetCard] at hS
          have hle : A.card ≤ S.card := Finset.card_le_card hAS
          omega
        rw [hempty, Finset.card_empty]
      rw [hzero, Nat.cast_zero]
      positivity
  refine le_trans (Finset.sum_le_sum hbound) ?_
  -- STEP 4: sum the geometric-type series
  have hsum : ∑ A ∈ I.powerset, u ^ A.card * (((K : ℝ) / (N : ℝ)) ^ A.card * (N.choose K : ℝ))
      = (N.choose K : ℝ) * (1 + u * ((K : ℝ) / (N : ℝ))) ^ I.card := by
    have h1 : ∀ A ∈ I.powerset, u ^ A.card * (((K : ℝ) / (N : ℝ)) ^ A.card * (N.choose K : ℝ))
        = (N.choose K : ℝ) * ((u * ((K : ℝ) / (N : ℝ))) ^ A.card) := by
      intro A _
      rw [mul_pow]
      ring
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
    have h2 : ∑ A ∈ I.powerset, (u * ((K : ℝ) / (N : ℝ))) ^ A.card
        = (u * ((K : ℝ) / (N : ℝ)) + 1) ^ I.card := by
      have h := Finset.sum_pow_mul_eq_add_pow (u * ((K : ℝ) / (N : ℝ))) (1 : ℝ) I
      simpa using h
    rw [h2]
    ring
  rw [hsum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hs : (0 : ℝ) ≤ u * ((K : ℝ) / (N : ℝ)) :=
    mul_nonneg hu (by positivity)
  have hexp : (1 + u * ((K : ℝ) / (N : ℝ))) ≤ Real.exp (u * ((K : ℝ) / (N : ℝ))) := by
    have h := Real.add_one_le_exp (u * ((K : ℝ) / (N : ℝ)))
    linarith
  have hpow : (1 + u * ((K : ℝ) / (N : ℝ))) ^ I.card
      ≤ (Real.exp (u * ((K : ℝ) / (N : ℝ)))) ^ I.card := by
    apply pow_le_pow_left₀ (by linarith) hexp
  refine le_trans hpow ?_
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have harg : (I.card : ℝ) * (u * ((K : ℝ) / (N : ℝ))) = (K : ℝ) * (I.card : ℝ) / (N : ℝ) * u := by
    rw [div_eq_mul_inv]
    ring
  linarith [harg]

/-- The elementary log inequality behind the Chernoff bound:
`δ²/(2(1+δ)) ≤ (1+δ)log(1+δ) - δ` for `δ ≥ 0`. -/
lemma log_chernoff_aux {δ : ℝ} (hδ : 0 ≤ δ) :
    δ ^ 2 / (2 * (1 + δ)) ≤ (1 + δ) * Real.log (1 + δ) - δ := by
  have h1δ : (0:ℝ) < 1 + δ := by linarith
  have hlog : 2 * δ / (δ + 2) ≤ Real.log (1 + δ) := Real.le_log_one_add_of_nonneg hδ
  have hstep : (1 + δ) * (2 * δ / (δ + 2)) ≤ (1 + δ) * Real.log (1 + δ) :=
    mul_le_mul_of_nonneg_left hlog h1δ.le
  have heq : (1 + δ) * (2 * δ / (δ + 2)) - δ = δ ^ 2 / (δ + 2) := by
    field_simp
    ring
  have h2 : δ ^ 2 / (2 * (1 + δ)) ≤ δ ^ 2 / (δ + 2) := by
    gcongr
    linarith
  linarith

open Classical in
/-- Lemma 4.1 (Chernoff bound for hypergeometric random variables), PDF p.16 (printed p.15). `S` is
uniform among the `K`-subsets of `[N]`. -/
theorem lemma_4_1 (N K : ℕ) (hK : K ≤ N) (I : Finset (Fin N))
    (hμ : 0 < (K : ℝ) * I.card / N) :
    let μ : ℝ := (K : ℝ) * I.card / N
    let Pr : (Finset (Fin N) → Prop) → ℝ := fun E =>
      (((powersetCard K (univ : Finset (Fin N))).filter E).card : ℝ) /
        ((powersetCard K (univ : Finset (Fin N))).card : ℝ)
    (∀ t : ℝ, 0 ≤ t →
      Pr (fun S => μ + t ≤ ((S ∩ I).card : ℝ)) ≤ Real.exp (-(t ^ 2 / (2 * (μ + t))))) ∧
    (∀ k : ℝ, 2 * μ ≤ k → Pr (fun S => k ≤ ((S ∩ I).card : ℝ)) ≤ Real.exp (-(k / 8))) := by
  classical
  dsimp only
  set μ : ℝ := (K : ℝ) * (I.card : ℝ) / (N : ℝ) with hμdef
  set D : ℝ := ((powersetCard K (univ : Finset (Fin N))).card : ℝ) with hDdef
  have hNne : (N : ℝ) ≠ 0 := by
    intro h0
    rw [hμdef, h0] at hμ
    simp at hμ
  have hNpos : 0 < N := by
    have h1 : (0:ℝ) < (N : ℝ) := by
      rcases lt_or_eq_of_le (Nat.cast_nonneg N : (0:ℝ) ≤ (N:ℝ)) with hh | hh
      · exact hh
      · exact absurd hh.symm hNne
    exact_mod_cast h1
  have hμpos : 0 < μ := hμ
  have hDval : D = (N.choose K : ℝ) := by
    rw [hDdef, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hDpos : 0 < D := by
    rw [hDval]
    exact_mod_cast Nat.choose_pos hK
  have key : ∀ t : ℝ, 0 ≤ t →
      (((powersetCard K (univ : Finset (Fin N))).filter
          (fun S => μ + t ≤ ((S ∩ I).card : ℝ))).card : ℝ) / D
        ≤ Real.exp (-(t ^ 2 / (2 * (μ + t)))) := by
    intro t ht
    set δ : ℝ := t / μ with hδdef
    have hδ : 0 ≤ δ := div_nonneg ht hμpos.le
    have ht_eq : t = μ * δ := by
      rw [hδdef]
      field_simp
    have hδpos : (0:ℝ) < 1 + δ := by linarith
    set θ : ℝ := Real.log (1 + δ) with hθdef
    have hexpθ : Real.exp θ = 1 + δ := by
      rw [hθdef]
      exact Real.exp_log hδpos
    have hθ : 0 ≤ θ := by
      rw [hθdef]
      exact Real.log_nonneg (by linarith)
    have hu : 0 ≤ Real.exp θ - 1 := by rw [hexpθ]; linarith
    set z : ℝ := μ + t with hzdef
    have hz : z = μ * (1 + δ) := by rw [hzdef, ht_eq]; ring
    -- Markov's inequality, step 1: bound by the exponential moment
    have hstep1 : (((powersetCard K (univ : Finset (Fin N))).filter
          (fun S => z ≤ ((S ∩ I).card : ℝ))).card : ℝ) * Real.exp (θ * z)
        ≤ ∑ S ∈ powersetCard K (univ : Finset (Fin N)), Real.exp (θ * ((S ∩ I).card : ℝ)) := by
      have h1 : (((powersetCard K (univ : Finset (Fin N))).filter
            (fun S => z ≤ ((S ∩ I).card : ℝ))).card : ℝ) * Real.exp (θ * z)
          = ∑ S ∈ (powersetCard K (univ : Finset (Fin N))).filter
              (fun S => z ≤ ((S ∩ I).card : ℝ)), Real.exp (θ * z) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      rw [h1, Finset.sum_filter]
      refine Finset.sum_le_sum fun S _ => ?_
      by_cases hp : z ≤ ((S ∩ I).card : ℝ)
      · simp only [hp, if_true]
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hp hθ)
      · simp only [hp, if_false]
        positivity
    -- step 2: the exponential moment bound
    have hstep2 : ∑ S ∈ powersetCard K (univ : Finset (Fin N)),
        Real.exp (θ * ((S ∩ I).card : ℝ)) ≤ D * Real.exp (μ * (Real.exp θ - 1)) := by
      have hpt : ∀ S ∈ powersetCard K (univ : Finset (Fin N)),
          Real.exp (θ * ((S ∩ I).card : ℝ)) = (1 + (Real.exp θ - 1)) ^ ((S ∩ I).card) := by
        intro S _
        rw [show (1:ℝ) + (Real.exp θ - 1) = Real.exp θ by ring]
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      rw [Finset.sum_congr rfl hpt]
      have h := mgf_le hNpos hK I (u := Real.exp θ - 1) hu
      simpa [← hDval, hμdef] using h
    -- divide by `exp (θ z)`
    have hA : (((powersetCard K (univ : Finset (Fin N))).filter
          (fun S => z ≤ ((S ∩ I).card : ℝ))).card : ℝ)
        ≤ D * Real.exp (μ * (Real.exp θ - 1) - θ * z) := by
      have hcomb := le_trans hstep1 hstep2
      have hpos : (0:ℝ) < Real.exp (θ * z) := Real.exp_pos _
      have hexp_split : Real.exp (μ * (Real.exp θ - 1))
          = Real.exp (μ * (Real.exp θ - 1) - θ * z) * Real.exp (θ * z) := by
        rw [← Real.exp_add]; congr 1; ring
      have hkey : D * Real.exp (μ * (Real.exp θ - 1))
          = (D * Real.exp (μ * (Real.exp θ - 1) - θ * z)) * Real.exp (θ * z) := by
        rw [hexp_split]; ring
      rw [hkey] at hcomb
      exact (mul_le_mul_iff_of_pos_right hpos).mp hcomb
    -- the final numerical comparison
    have hfinal : Real.exp (μ * (Real.exp θ - 1) - θ * z) ≤ Real.exp (-(t ^ 2 / (2 * z))) := by
      apply Real.exp_le_exp.mpr
      have hnum := log_chernoff_aux hδ
      have h1 : μ * (Real.exp θ - 1) - θ * z = -(μ * ((1 + δ) * Real.log (1 + δ) - δ)) := by
        rw [hexpθ, hθdef, hz]
        ring
      have h2 : t ^ 2 / (2 * z) = μ * (δ ^ 2 / (2 * (1 + δ))) := by
        rw [hz, ht_eq]
        field_simp
      have h3 : μ * (δ ^ 2 / (2 * (1 + δ))) ≤ μ * ((1 + δ) * Real.log (1 + δ) - δ) :=
        mul_le_mul_of_nonneg_left hnum hμpos.le
      rw [h1, h2]
      linarith
    rw [div_le_iff₀ hDpos]
    calc (((powersetCard K (univ : Finset (Fin N))).filter
          (fun S => z ≤ ((S ∩ I).card : ℝ))).card : ℝ)
        ≤ D * Real.exp (μ * (Real.exp θ - 1) - θ * z) := hA
      _ ≤ D * Real.exp (-(t ^ 2 / (2 * z))) := mul_le_mul_of_nonneg_left hfinal hDpos.le
      _ = Real.exp (-(t ^ 2 / (2 * z))) * D := by ring
  refine ⟨key, ?_⟩
  intro k hk
  have hkpos : (0:ℝ) < k := by linarith
  have ht : 0 ≤ k - μ := by linarith
  have h1 := key (k - μ) ht
  have heq1 : μ + (k - μ) = k := by ring
  rw [heq1] at h1
  refine le_trans h1 (Real.exp_le_exp.mpr ?_)
  have htarget : k / 8 ≤ (k - μ) ^ 2 / (2 * k) := by
    rw [le_div_iff₀ (by linarith : (0:ℝ) < 2 * k)]
    have h1 : 0 ≤ k - 2 * μ := by linarith
    have h2 : 0 ≤ 3 * k - 2 * μ := by linarith
    nlinarith [mul_nonneg h1 h2]
  linarith

/-! ## Crude counting bound for the candidate supports -/

/-- **Part (b) of the paper's row-recovery proof**, as in the paper (`lem:hint-final`): a support
family with at most `y` outside coordinates has at most `2 ^ (|Jj| + y) * Nj ^ y` members, i.e.
`2^{|J_j|} · ∑_{r ≤ y} binom(N_j - |J_j|, r)`, provided the row is nonempty.  Instantiated at
`|J_j| ≤ B_X`, `y ≤ B_Y`, `N_j ≤ N_max` this is the paper's `2^{B_X}(eN_max)^{B_Y}` (footnote:
`∑_{r=0}^{B_Y} binom(N_max, r) ≤ (eN_max)^{B_Y}`). -/
lemma card_candSet_le (Nj : ℕ) (hNj : 0 < Nj) (Jj : Finset ℕ) (hJj : Jj ⊆ range Nj) (y : ℕ) :
    (candSet Nj Jj y).card ≤ 2 ^ (Jj.card + y) * Nj ^ y := by
  classical
  have hval : candSet Nj Jj y = (range Nj).powerset.filter (fun C => (C \ Jj).card ≤ y) := rfl
  by_cases hy : y ≤ Nj - Jj.card
  · rw [hval, card_candidates_le_eq Jj hJj y]
    have hsum : ∑ h ∈ range (y + 1), (Nj - Jj.card).choose h ≤ 2 ^ y * Nj ^ y := by
      have h1 : ∀ h ∈ range (y + 1), (Nj - Jj.card).choose h ≤ Nj ^ y := by
        intro h hh
        have hhy : h ≤ y := Nat.lt_succ_iff.mp (Finset.mem_range.mp hh)
        calc (Nj - Jj.card).choose h ≤ (Nj - Jj.card) ^ h := Nat.choose_le_pow _ h
          _ ≤ Nj ^ h := Nat.pow_le_pow_left (Nat.sub_le _ _) h
          _ ≤ Nj ^ y := Nat.pow_le_pow_right hNj hhy
      calc ∑ h ∈ range (y + 1), (Nj - Jj.card).choose h ≤ ∑ h ∈ range (y + 1), Nj ^ y :=
            Finset.sum_le_sum h1
        _ = (y + 1) * Nj ^ y := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
        _ ≤ 2 ^ y * Nj ^ y :=
            Nat.mul_le_mul_right _ (by have := Nat.lt_two_pow_self (n := y); omega)
    calc 2 ^ Jj.card * ∑ h ∈ range (y + 1), (Nj - Jj.card).choose h
        ≤ 2 ^ Jj.card * (2 ^ y * Nj ^ y) := Nat.mul_le_mul_left _ hsum
      _ = 2 ^ (Jj.card + y) * Nj ^ y := by rw [pow_add]; ring
  · push Not at hy
    have hEq : (range Nj).powerset.filter (fun C => (C \ Jj).card ≤ y) = (range Nj).powerset := by
      apply Finset.filter_true_of_mem
      intro C hC
      have hCN : C ⊆ range Nj := Finset.mem_powerset.mp hC
      have h1 : (C \ Jj).card ≤ (range Nj \ Jj).card := by
        apply Finset.card_le_card
        intro x hx
        exact Finset.mem_sdiff.mpr ⟨hCN (Finset.mem_sdiff.mp hx).1, (Finset.mem_sdiff.mp hx).2⟩
      have h2 : (range Nj \ Jj).card = Nj - Jj.card := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hJj, Finset.card_range]
      omega
    rw [hval, hEq, Finset.card_powerset, Finset.card_range]
    have h1 : Nj ≤ Jj.card + y := by omega
    have h2 : 2 ^ Nj ≤ 2 ^ (Jj.card + y) := Nat.pow_le_pow_right (by norm_num) h1
    have h3 : 0 < Nj ^ y := pow_pos hNj y
    calc 2 ^ Nj = 2 ^ Nj * 1 := by rw [mul_one]
      _ ≤ 2 ^ (Jj.card + y) * Nj ^ y := Nat.mul_le_mul h2 h3

/-! ## The numerical core of the row-recovery bound -/

/-- `W ^ BY ≤ 2 ^ (BY * ⌈log (e W)⌉)`. -/
lemma pow_le_rpow_ceil (W BY : ℕ) (hW : 0 < W) :
    (W : ℝ) ^ (BY : ℝ) ≤ (2 : ℝ) ^ ((BY : ℝ) * (⌈lg (Real.exp 1 * (W : ℝ))⌉₊ : ℝ)) := by
  have h2 : (0:ℝ) < 2 := by norm_num
  have hWr : (0:ℝ) < (W:ℝ) := by exact_mod_cast hW
  have hlogb : (2:ℝ)^(lg (W:ℝ)) = (W:ℝ) :=
    Real.rpow_logb (b := 2) (by norm_num) (by norm_num) hWr
  have h1 : (W:ℝ) ^ (BY:ℝ) = (2:ℝ)^((BY:ℝ) * lg (W:ℝ)) := by
    conv_lhs => rw [← hlogb]
    rw [← Real.rpow_mul (le_of_lt h2), mul_comm]
  rw [h1]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
  have hle : lg (Real.exp 1 * (W:ℝ)) ≤ ((⌈lg (Real.exp 1 * (W:ℝ))⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hexp : (1:ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
  have hlt : lg (W:ℝ) < lg (Real.exp 1 * (W:ℝ)) := by
    apply Real.logb_lt_logb (by norm_num) hWr
    nlinarith
  have hBY : (0:ℝ) ≤ (BY:ℝ) := Nat.cast_nonneg _
  refine mul_le_mul_of_nonneg_left ?_ hBY
  linarith

/-- **Part (d) of the paper's row-recovery proof**, as in the paper — the exponent bookkeeping of
`ℓ`'s definition, equation (16).  With `ℓ = B_X + B_Y⌈lg(eN_max)⌉ + B_Y + t + 10` this gives
`2^{B_X+B_Y⌈lg(eN_max)⌉+B_Y−ℓ} = 2^{-t}/1024`, i.e. the paper's inequality
`2^{B_X+B_Y⌈lg(eN_max)⌉−ℓ} ≤ η²/8` *before* the `η²/8` simplification
(`inv_two_pow_ceil_le` performs that last step). -/
lemma arith_le (BX BY W L t : ℕ) (hW : 0 < W)
    (hL : L = BX + BY * ⌈lg (Real.exp 1 * (W:ℝ))⌉₊ + BY + t + 10) :
    (2:ℝ)^(BX:ℝ) * (2:ℝ)^(BY:ℝ) * (W:ℝ)^(BY:ℝ) * ((2:ℝ)^(L:ℝ))⁻¹
      ≤ ((2:ℝ)^(t:ℝ))⁻¹ / 1024 := by
  have h2 : (0:ℝ) < 2 := by norm_num
  have hWle := pow_le_rpow_ceil W BY hW
  have hRHS : (2:ℝ)^(BX:ℝ) * (2:ℝ)^(BY:ℝ)
      * (2:ℝ)^((BY:ℝ) * (⌈lg (Real.exp 1 * (W:ℝ))⌉₊ : ℝ)) * ((2:ℝ)^(L:ℝ))⁻¹
      = ((2:ℝ)^(t:ℝ))⁻¹ / 1024 := by
    have hLc : (L:ℝ) = (BX:ℝ) + (BY:ℝ) * (⌈lg (Real.exp 1 * (W:ℝ))⌉₊ : ℝ) + (BY:ℝ)
        + (t:ℝ) + 10 := by
      rw [hL]; push_cast; ring
    have hcomb : (2:ℝ)^(BX:ℝ) * (2:ℝ)^(BY:ℝ)
        * (2:ℝ)^((BY:ℝ) * (⌈lg (Real.exp 1 * (W:ℝ))⌉₊ : ℝ))
        = (2:ℝ)^((BX:ℝ) + (BY:ℝ) + (BY:ℝ) * (⌈lg (Real.exp 1 * (W:ℝ))⌉₊ : ℝ)) := by
      rw [mul_assoc, ← Real.rpow_add h2, ← Real.rpow_add h2]
      congr 1
      ring
    rw [hcomb, hLc, ← div_eq_mul_inv, ← Real.rpow_sub h2]
    have harg : (BX:ℝ) + (BY:ℝ) + (BY:ℝ) * (⌈lg (Real.exp 1 * (W:ℝ))⌉₊ : ℝ)
        - ((BX:ℝ) + (BY:ℝ) * (⌈lg (Real.exp 1 * (W:ℝ))⌉₊ : ℝ) + (BY:ℝ) + (t:ℝ) + 10)
        = -((t:ℝ) + 10) := by ring
    rw [harg]
    rw [show -((t:ℝ) + 10) = -(t:ℝ) - 10 by ring, Real.rpow_sub h2, Real.rpow_neg (le_of_lt h2)]
    have h1024 : (2:ℝ)^(10:ℝ) = 1024 := by norm_num
    rw [h1024]
  refine le_trans ?_ (le_of_eq hRHS)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hWle (by positivity)) (by positivity)

/-- `2^{-⌈log(16/ε)⌉} / 1024 ≤ ε/8`. -/
lemma inv_two_pow_ceil_le (ε : ℝ) (hε : 0 < ε) :
    ((2:ℝ)^((⌈lg (16/ε)⌉₊ : ℕ) : ℝ))⁻¹ / 1024 ≤ ε / 8 := by
  set t : ℕ := ⌈lg (16/ε)⌉₊ with ht
  have hpos : (0:ℝ) < 16/ε := by positivity
  have hlog : lg (16/ε) ≤ ((t:ℕ):ℝ) := by
    rw [ht]; exact Nat.le_ceil _
  have hlogb : (2:ℝ) ^ lg (16/ε) = 16/ε :=
    Real.rpow_logb (b := 2) (by norm_num) (by norm_num) hpos
  have hpow : (16:ℝ)/ε ≤ (2:ℝ)^((t:ℝ)) := by
    calc (16:ℝ)/ε = (2:ℝ)^(lg (16/ε)) := hlogb.symm
      _ ≤ (2:ℝ)^((t:ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hlog
  have hinv : ((2:ℝ)^((t:ℝ)))⁻¹ ≤ ε/16 := by
    have h1 : ((2:ℝ)^((t:ℝ)))⁻¹ ≤ ((16:ℝ)/ε)⁻¹ :=
      (inv_le_inv₀ (by positivity) hpos).mpr hpow
    have h2' : ((16:ℝ)/ε)⁻¹ = ε/16 := by field_simp
    rwa [h2'] at h1
  calc ((2:ℝ)^((t:ℝ)))⁻¹ / 1024 ≤ (ε/16)/1024 :=
        div_le_div_of_nonneg_right hinv (by norm_num)
    _ ≤ ε/8 := by linarith

/-! ## The final recovery of a regular row -/

/-- **Part (a) of the paper's row-recovery proof**, as in the paper (`lem:hint-final`): if the final
recovery of a row differs from the true support, then some *other* support with at most `BY` outside
coordinates matches the whole transcript — the wrong estimate forces another candidate `C` with
`(C \ J_j).card ≤ B_Y`. -/
theorem workerFinal_fail_imp
    (N m L K BX BY : ℕ) (j : Fin m) (β : Fin L → Fin K → ZMod 2) (Jj : Finset ℕ)
    (z : List (ZMod 2)) (Sj : Finset ℕ)
    (hz : z = (List.take L (List.finRange L)).map (HintParams.rowBit β Sj))
    (hBX : ¬ BX < Jj.card)
    (hyBY : (Sj \ Jj).card ≤ BY)
    (hyNj : (Sj \ Jj).card ≤ rowLen N m j.val - Jj.card)
    (hSj : Sj ⊆ range (rowLen N m j.val))
    (hfail : HintParams.workerFinal N m L K BX BY j β Jj z ≠ Sj) :
    ∃ C ∈ (candSet (rowLen N m j.val) Jj BY).erase Sj,
      (List.take L (List.finRange L)).map (HintParams.rowBit β C)
        = (List.take L (List.finRange L)).map (HintParams.rowBit β Sj) := by
  classical
  set Nj := rowLen N m j.val with hNj
  set y := (Sj \ Jj).card with hy
  have hzl : z.length = L := by
    rw [hz, List.length_map, List.length_take, List.length_finRange, Nat.min_eq_left (le_refl L)]
  have htake : List.take z.length (List.finRange L) = List.take L (List.finRange L) := by rw [hzl]
  have hSfam : Sj ∈ HintParams.family Nj β Jj y z := by
    simp only [HintParams.family, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hSj, by rw [hy], by rw [htake, hz]⟩
  have hU : Sj ∈ (range (min BY (Nj - Jj.card) + 1)).biUnion (fun r => HintParams.family Nj β Jj r z) := by
    refine Finset.mem_biUnion.mpr ⟨y, ?_, hSfam⟩
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (le_min (by simpa only [hy] using hyBY)
      (by simpa only [hy, hNj] using hyNj))
  have hfinal : HintParams.workerFinal N m L K BX BY j β Jj z =
      (if ((range (min BY (Nj - Jj.card) + 1)).biUnion
            (fun r => HintParams.family Nj β Jj r z)).card = 1
        then (((range (min BY (Nj - Jj.card) + 1)).biUnion
            (fun r => HintParams.family Nj β Jj r z)).toList.head?).getD ∅
        else ∅) := by
    rw [HintParams.workerFinal]
    try simp only []
    rw [if_neg hBX]
  have hhead : ∀ (h1 : ((range (min BY (Nj - Jj.card) + 1)).biUnion
      (fun r => HintParams.family Nj β Jj r z)).card = 1),
      (((range (min BY (Nj - Jj.card) + 1)).biUnion
        (fun r => HintParams.family Nj β Jj r z)).toList.head?).getD ∅ = Sj := by
    intro h1
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
    have haS : a = Sj := by
      have hmem : Sj ∈ ({a} : Finset (Finset ℕ)) := ha ▸ hU
      simpa only [Finset.mem_singleton, eq_comm] using hmem
    rw [ha, ← haS, Finset.toList_singleton]
    rfl
  have hU1 : ((range (min BY (Nj - Jj.card) + 1)).biUnion
      (fun r => HintParams.family Nj β Jj r z)).card ≠ 1 := by
    intro h1
    exact hfail (by rw [hfinal, if_pos h1]; exact hhead h1)
  have hSne : Sj ≠ ∅ := by
    intro h0
    apply hfail
    rw [hfinal]
    by_cases h1 : ((range (min BY (Nj - Jj.card) + 1)).biUnion
        (fun r => HintParams.family Nj β Jj r z)).card = 1
    · rw [if_pos h1, hhead h1]
    · rw [if_neg h1]; exact h0.symm
  have hex : ∃ C ∈ (range (min BY (Nj - Jj.card) + 1)).biUnion
      (fun r => HintParams.family Nj β Jj r z), C ≠ Sj := by
    by_contra hcon
    push Not at hcon
    have hsub : (range (min BY (Nj - Jj.card) + 1)).biUnion
        (fun r => HintParams.family Nj β Jj r z) ⊆ {Sj} := by
      intro C hC
      simp only [Finset.mem_singleton]
      exact hcon C hC
    have h1 : ((range (min BY (Nj - Jj.card) + 1)).biUnion
        (fun r => HintParams.family Nj β Jj r z)).card ≤ 1 := by
      simpa using Finset.card_le_card hsub
    have h2 : 0 < ((range (min BY (Nj - Jj.card) + 1)).biUnion
        (fun r => HintParams.family Nj β Jj r z)).card := Finset.card_pos.mpr ⟨Sj, hU⟩
    omega
  obtain ⟨C, hCU, hCS⟩ := hex
  obtain ⟨r, hr, hCfam⟩ := Finset.mem_biUnion.mp hCU
  rw [HintParams.family, Finset.mem_filter, Finset.mem_powerset] at hCfam
  obtain ⟨hCsub, hCcard, hCpre⟩ := hCfam
  have hCpre' : (List.take L (List.finRange L)).map (HintParams.rowBit β C) = z := by
    rw [← htake]; exact hCpre
  refine ⟨C, Finset.mem_erase.mpr ⟨hCS, ?_⟩, ?_⟩
  · rw [candSet]
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hCsub, by
      rw [hCcard]
      exact le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)) (min_le_left _ _)⟩
  · rw [hCpre', hz]

/-! ## The first claim of Lemma 5.3 -/

/-- **The paper's row-recovery inequality, unweakened form.**

This is the bound that the chain of §5.3 (PDF p.21) actually produces, *before* the `η²/8`
simplification: with `t = ⌈lg(16/η²)⌉` and `ℓ` as in equation (16) (`HintParams.ell`), the
candidate-count and separation steps give

`Pr[final ≠ S_j] ≤ 2^{B_X + B_Y⌈lg(e N_max)⌉ + B_Y - ℓ} = 2^{-t - 10}`,

which is the paper's inequality with the `ξ`-dependent factors cancelled *exactly* (`arith_le`
below performs the exponent bookkeeping, equation (16) being chosen so that it closes).

The milestone statement of Lemma 5.3 is the corollary `claim1`, obtained by the crude
`2^{-⌈lg(16/η²)⌉} ≤ η²/16` (`inv_two_pow_ceil_le`).  The sharp form is kept separate because
Lemma 5.4 needs the extra `2^{-B_Y}·1024^{-1}` decay that the `η²/8` form throws away. -/
theorem row_final_sharp (P : HintParams) (N X Y : ℕ) (hargs : P.NodeArgs N X Y)
    (hnl : P.NonLeaf N X Y) (j : Fin (P.rows X Y)) (Jj Sj : Finset ℕ)
    (hJj : Jj ⊆ range (rowLen N (P.rows X Y) j.val))
    (hSj : Sj ⊆ range (rowLen N (P.rows X Y) j.val))
    (hreg : ¬ P.Overloaded N X Y Jj Sj) :
    prU (fun β : (P.scheme N X Y).Rand =>
        (P.scheme N X Y).final j β Jj ((P.scheme N X Y).truePrefix j β Sj (P.scheme N X Y).ℓ) ≠ Sj)
      ≤ ((2 : ℝ) ^ ((⌈lg (16 / P.eta ^ 2)⌉₊ : ℕ) : ℝ))⁻¹ / 1024 := by
  classical
  have hm1 : 1 ≤ P.rows X Y := rows_pos P N X Y hargs hnl
  have hNjW : rowLen N (P.rows X Y) j.val ≤ P.Nmax N X Y :=
    rowLen_le_Nmax N (P.rows X Y) j.val hm1
  have hjcard : ¬ P.BX N X Y < Jj.card := by
    intro h; exact hreg (Or.inl h)
  have hyBY : (Sj \ Jj).card ≤ P.BY N X Y := by
    by_contra h
    exact hreg (Or.inr (by omega))
  have hyNj : (Sj \ Jj).card ≤ rowLen N (P.rows X Y) j.val - Jj.card := by
    have hsub : Sj \ Jj ⊆ range (rowLen N (P.rows X Y) j.val) \ Jj := by
      intro x hx
      exact Finset.mem_sdiff.mpr ⟨hSj (Finset.mem_sdiff.mp hx).1, (Finset.mem_sdiff.mp hx).2⟩
    calc (Sj \ Jj).card ≤ (range (rowLen N (P.rows X Y) j.val) \ Jj).card := Finset.card_le_card hsub
      _ = rowLen N (P.rows X Y) j.val - Jj.card := by
          rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hJj, Finset.card_range]
  have hmono : prU (fun β : (P.scheme N X Y).Rand =>
      (P.scheme N X Y).final j β Jj ((P.scheme N X Y).truePrefix j β Sj (P.ell N X Y)) ≠ Sj)
      ≤ prU (fun β : (P.scheme N X Y).Rand =>
        ∃ C ∈ (candSet (rowLen N (P.rows X Y) j.val) Jj (P.BY N X Y)).erase Sj,
          (List.take (P.ell N X Y) (List.finRange (P.ell N X Y))).map (HintParams.rowBit β C)
            = (List.take (P.ell N X Y) (List.finRange (P.ell N X Y))).map
                (HintParams.rowBit β Sj)) :=
    prU_mono' (fun β hf => workerFinal_fail_imp N (P.rows X Y) (P.ell N X Y) (P.Nmax N X Y)
      (P.BX N X Y) (P.BY N X Y) j β Jj _ Sj rfl hjcard hyBY hyNj hSj hf)
  have hstep := prU_exists_prefix_eq_list (ℓ := P.ell N X Y) (K := P.Nmax N X Y)
    (Nj := rowLen N (P.rows X Y) j.val) (a := P.ell N X Y) (le_refl _) hNjW hSj
    (candSet (rowLen N (P.rows X Y) j.val) Jj (P.BY N X Y))
    (fun C hC => by
      rw [candSet] at hC
      exact Finset.mem_powerset.mp (Finset.mem_filter.mp hC).1)
  have hcard : ((candSet (rowLen N (P.rows X Y) j.val) Jj (P.BY N X Y)).erase Sj).card
      ≤ 2 ^ (P.BX N X Y + P.BY N X Y) * (P.Nmax N X Y) ^ (P.BY N X Y) := by
    rcases Nat.eq_zero_or_pos (rowLen N (P.rows X Y) j.val) with hNj0 | hNjpos
    · have hempty : (candSet (rowLen N (P.rows X Y) j.val) Jj (P.BY N X Y)).erase Sj = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro C hC
        rw [Finset.mem_erase, candSet, Finset.mem_filter, Finset.mem_powerset] at hC
        obtain ⟨hCS, hCsub, -⟩ := hC
        have hC0 : C = ∅ := Finset.subset_empty.mp (by simpa [hNj0] using hCsub)
        have hSj0 : Sj = ∅ := Finset.subset_empty.mp (by simpa [hNj0] using hSj)
        exact hCS (hC0.trans hSj0.symm)
      rw [hempty, Finset.card_empty]
      exact Nat.zero_le _
    · have h1 : ((candSet (rowLen N (P.rows X Y) j.val) Jj (P.BY N X Y)).erase Sj).card
          ≤ (candSet (rowLen N (P.rows X Y) j.val) Jj (P.BY N X Y)).card :=
        Finset.card_le_card (Finset.erase_subset _ _)
      have h2 := card_candSet_le (rowLen N (P.rows X Y) j.val) hNjpos Jj hJj (P.BY N X Y)
      have h3 : 2 ^ (Jj.card + P.BY N X Y) ≤ 2 ^ (P.BX N X Y + P.BY N X Y) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have h4 : (rowLen N (P.rows X Y) j.val) ^ (P.BY N X Y) ≤ (P.Nmax N X Y) ^ (P.BY N X Y) :=
        Nat.pow_le_pow_left hNjW _
      calc ((candSet (rowLen N (P.rows X Y) j.val) Jj (P.BY N X Y)).erase Sj).card
          ≤ (candSet (rowLen N (P.rows X Y) j.val) Jj (P.BY N X Y)).card := h1
        _ ≤ 2 ^ (Jj.card + P.BY N X Y) * (rowLen N (P.rows X Y) j.val) ^ (P.BY N X Y) := h2
        _ ≤ 2 ^ (P.BX N X Y + P.BY N X Y) * (P.Nmax N X Y) ^ (P.BY N X Y) :=
            Nat.mul_le_mul h3 h4
  have hcardR : (((candSet (rowLen N (P.rows X Y) j.val) Jj (P.BY N X Y)).erase Sj).card : ℝ)
      ≤ (2 : ℝ) ^ (P.BX N X Y + P.BY N X Y) * (P.Nmax N X Y : ℝ) ^ (P.BY N X Y) := by
    have h : (((candSet (rowLen N (P.rows X Y) j.val) Jj (P.BY N X Y)).erase Sj).card : ℝ)
        ≤ ((2 ^ (P.BX N X Y + P.BY N X Y) * (P.Nmax N X Y) ^ (P.BY N X Y) : ℕ) : ℝ) := by
      exact_mod_cast hcard
    simpa using h
  have hlgn : 0 < P.lgn := by
    rw [HintParams.lgn, lg]
    exact Real.logb_pos (by norm_num) (by exact_mod_cast hargs.1)
  have heta : 0 < P.eta := by
    rw [HintParams.eta]; positivity
  have heta2 : 0 < P.eta ^ 2 := pow_pos heta 2
  have hWpos : 0 < P.Nmax N X Y := by
    rw [HintParams.Nmax]
    apply Nat.ceil_pos.mpr
    have h1 : (0:ℝ) < (N:ℝ) := by exact_mod_cast hargs.2.2.1
    have h2 : (0:ℝ) < (P.rows X Y : ℝ) := by exact_mod_cast hm1
    positivity
  have hmid : ((candSet (rowLen N (P.rows X Y) j.val) Jj (P.BY N X Y)).erase Sj).card
      * ((2 : ℝ) ^ ((P.ell N X Y : ℝ)))⁻¹
      ≤ ((2 : ℝ) ^ (P.BX N X Y + P.BY N X Y) * (P.Nmax N X Y : ℝ) ^ (P.BY N X Y))
        * ((2 : ℝ) ^ ((P.ell N X Y : ℝ)))⁻¹ := by
    apply mul_le_mul_of_nonneg_right hcardR
    positivity
  have hfin : ((2 : ℝ) ^ (P.BX N X Y + P.BY N X Y) * (P.Nmax N X Y : ℝ) ^ (P.BY N X Y))
      * ((2 : ℝ) ^ ((P.ell N X Y : ℝ)))⁻¹
      ≤ ((2 : ℝ) ^ ((⌈lg (16 / P.eta ^ 2)⌉₊ : ℕ) : ℝ))⁻¹ / 1024 := by
    have h1 : (2:ℝ) ^ (P.BX N X Y + P.BY N X Y)
        = (2:ℝ)^((P.BX N X Y:ℝ)) * (2:ℝ)^((P.BY N X Y:ℝ)) := by
      rw [pow_add, ← Real.rpow_natCast (2:ℝ) (P.BX N X Y),
        ← Real.rpow_natCast (2:ℝ) (P.BY N X Y)]
    have h2 : (P.Nmax N X Y : ℝ) ^ (P.BY N X Y) = ((P.Nmax N X Y : ℝ))^((P.BY N X Y:ℝ)) := by
      rw [Real.rpow_natCast]
    rw [h1, h2]
    exact arith_le (P.BX N X Y) (P.BY N X Y) (P.Nmax N X Y) (P.ell N X Y)
      (⌈lg (16 / P.eta ^ 2)⌉₊) hWpos (by rw [HintParams.ell])
  exact le_trans hmono (le_trans hstep (le_trans hmid hfin))

/-- First claim of Lemma 5.3: a regular row of a non-leaf node is recovered except with
probability at most `η²/8`.  This is the milestone (weakened) form of `row_final_sharp`, obtained
by `2^{-⌈lg(16/η²)⌉} ≤ η²/16` (`inv_two_pow_ceil_le`). -/
theorem claim1 (P : HintParams) (N X Y : ℕ) (hargs : P.NodeArgs N X Y) (hnl : P.NonLeaf N X Y)
    (j : Fin (P.rows X Y)) (Jj Sj : Finset ℕ)
    (hJj : Jj ⊆ range (rowLen N (P.rows X Y) j.val))
    (hSj : Sj ⊆ range (rowLen N (P.rows X Y) j.val))
    (hreg : ¬ P.Overloaded N X Y Jj Sj) :
    prU (fun β : (P.scheme N X Y).Rand =>
        (P.scheme N X Y).final j β Jj ((P.scheme N X Y).truePrefix j β Sj (P.scheme N X Y).ℓ) ≠ Sj)
      ≤ P.eta ^ 2 / 8 := by
  have hlgn : 0 < P.lgn := by
    rw [HintParams.lgn, lg]
    exact Real.logb_pos (by norm_num) (by exact_mod_cast hargs.1)
  have heta : 0 < P.eta := by
    rw [HintParams.eta]; positivity
  have heta2 : 0 < P.eta ^ 2 := pow_pos heta 2
  exact le_trans (row_final_sharp P N X Y hargs hnl j Jj Sj hJj hSj hreg)
    (inv_two_pow_ceil_le (P.eta ^ 2) heta2)
/-! ## Claim 2: the expected overloaded mass -/

lemma prU_eq_card' {α : Type} [Fintype α] (P : α → Prop) [DecidablePred P] :
    prU P = ((Finset.univ.filter P).card : ℝ) / (Fintype.card α : ℝ) := by
  unfold prU
  exact congrArg (fun n : ℕ => (n : ℝ) / (Fintype.card α : ℝ))
    (congrArg Finset.card (Finset.filter_congr_decidable Finset.univ P _))

/-- `S ⊆ [N]`, as a finset of `Fin N`. -/
def finSet {N : ℕ} (S : Finset ℕ) : Finset (Fin N) := univ.filter (fun i => i.val ∈ S)

lemma card_finSet {N : ℕ} (S : Finset ℕ) (hS : S ⊆ range N) :
    (finSet (N := N) S).card = S.card := by
  classical
  refine Finset.card_bij (fun (i : Fin N) (_ : i ∈ finSet (N := N) S) => i.val) ?_ ?_ ?_
  · intro i hi
    rw [finSet, Finset.mem_filter] at hi
    exact hi.2
  · intro i _ j _ hij
    exact Fin.ext hij
  · intro x hx
    exact ⟨⟨x, Finset.mem_range.mp (hS hx)⟩,
      by rw [finSet, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hx⟩, rfl⟩

lemma rowImage_subset {N m : ℕ} (π : Equiv.Perm (Fin N)) (j : ℕ) (S : Finset ℕ) :
    rowImage N m π j S ⊆ ((range N).filter (fun p => p % m = j)).image (fun p => p / m) := by
  classical
  intro q hq
  rw [rowImage, Finset.mem_image] at hq
  obtain ⟨i, hi, rfl⟩ := hq
  rw [Finset.mem_filter] at hi
  exact Finset.mem_image.mpr ⟨(π i).val,
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (π i).isLt, hi.2.2⟩, rfl⟩

lemma div_injOn_row {N m j : ℕ} :
    Set.InjOn (fun p => p / m) ↑((range N).filter (fun p => p % m = j)) := by
  intro p hp q hq heq
  simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hp hq
  have heq' : p / m = q / m := heq
  have e1 : p = m * (p/m) + j := by rw [← hp.2]; exact (Nat.div_add_mod p m).symm
  have e2 : q = m * (q/m) + j := by rw [← hq.2]; exact (Nat.div_add_mod q m).symm
  rw [e1, e2, heq']

lemma rowImage_card_le_rowLen {N m j : ℕ} (π : Equiv.Perm (Fin N)) (S : Finset ℕ) :
    (rowImage N m π j S).card ≤ rowLen N m j := by
  classical
  have hcard : (((range N).filter (fun p => p % m = j)).image (fun p => p / m)).card
      = rowLen N m j := by
    rw [Finset.card_image_of_injOn div_injOn_row]
    rfl
  exact le_trans (Finset.card_le_card (rowImage_subset π j S)) (le_of_eq hcard)

/-- The load of a row is the intersection of the image of `S` with the row's positions. -/
lemma rowImage_card_eq {N m : ℕ} (π : Equiv.Perm (Fin N)) (j : ℕ) (S : Finset ℕ) :
    (rowImage N m π j S).card
      = (((finSet S).image π).filter (fun q => q.val % m = j)).card := by
  classical
  set T : Finset (Fin N) := univ.filter (fun i : Fin N => i.val ∈ S ∧ (π i).val % m = j) with hT
  have hL : rowImage N m π j S = T.image (fun i => (π i).val / m) := by
    ext q
    simp only [rowImage, Finset.mem_image]
    constructor
    · rintro ⟨i, hi, rfl⟩
      rw [Finset.mem_filter] at hi
      exact ⟨i, by rw [hT, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hi.2.1, hi.2.2⟩, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      rw [hT, Finset.mem_filter] at hi
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi.2.1, hi.2.2⟩, rfl⟩
  have hinj : Set.InjOn (fun i : Fin N => (π i).val / m) ↑T := by
    intro i hi j' hj' heq
    rw [hT, Finset.coe_filter] at hi hj'
    simp only [Set.mem_setOf_eq, Finset.mem_univ, true_and] at hi hj'
    have h1 : (π i).val = m * ((π i).val / m) + j := by
      rw [← hi.2]; exact (Nat.div_add_mod _ _).symm
    have h2 : (π j').val = m * ((π j').val / m) + j := by
      rw [← hj'.2]; exact (Nat.div_add_mod _ _).symm
    have heq' : (π i).val / m = (π j').val / m := heq
    exact π.injective (Fin.ext (by rw [h1, h2, heq']))
  have hcardL : (rowImage N m π j S).card = T.card := by
    rw [hL, Finset.card_image_of_injOn hinj]
  have hR : ((finSet S).image π).filter (fun q => q.val % m = j) = T.image π := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_image, finSet, Finset.mem_univ, true_and, hT]
    constructor
    · rintro ⟨⟨i, hiS, rfl⟩, hq⟩
      exact ⟨i, ⟨hiS, hq⟩, rfl⟩
    · rintro ⟨i, ⟨hiS, hq⟩, rfl⟩
      exact ⟨⟨i, hiS, rfl⟩, hq⟩
  rw [hcardL, hR, Finset.card_image_of_injective _ π.injective]

lemma image_perm_inj {N : ℕ} (σ : Equiv.Perm (Fin N)) {A B : Finset (Fin N)}
    (h : A.image σ = B.image σ) : A = B := by
  have h2 : ∀ X : Finset (Fin N), (X.image σ).image σ.symm = X := by
    intro X
    rw [Finset.image_image]
    ext x
    simp
  rw [← h2 A, h, h2 B]

open Classical in
/-- **Fibre-counting transfer** (second claim), as in the paper: the row image of a fixed set under a
uniform permutation is a uniform subset of the same size — the fibres of `π ↦ J_f.image π` over the
`|J_f|`-subsets of `[N]` are equinumerous, so a probability over permutations equals the average over
uniform subsets.  This is what lets the hypergeometric tail `hypergeom_tail` be applied to a row's
load. -/
theorem prU_image_eq {N : ℕ} (Jf : Finset (Fin N)) (Q : Finset (Fin N) → Prop) :
    prU (fun π : Equiv.Perm (Fin N) => Q (Jf.image π))
      = (((powersetCard Jf.card (univ : Finset (Fin N))).filter Q).card : ℝ)
        / ((powersetCard Jf.card (univ : Finset (Fin N))).card : ℝ) := by
  classical
  haveI : Nonempty (Equiv.Perm (Fin N)) := ⟨1⟩
  set k := Jf.card with hk
  set c : ℕ := (univ.filter (fun (π : Equiv.Perm (Fin N)) => Jf.image π = Jf)).card with hc
  have hcpos : 0 < c := by
    have hmem : (1 : Equiv.Perm (Fin N)) ∈
        univ.filter (fun (π : Equiv.Perm (Fin N)) => Jf.image π = Jf) := by
      simp
    exact Finset.card_pos.mpr ⟨_, hmem⟩
  have hmemP : ∀ π : Equiv.Perm (Fin N),
      Jf.image π ∈ powersetCard k (univ : Finset (Fin N)) := by
    intro π
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, by rw [Finset.card_image_of_injective _ π.injective]⟩
  have hconst : ∀ A ∈ powersetCard k (univ : Finset (Fin N)),
      (univ.filter (fun (π : Equiv.Perm (Fin N)) => Jf.image π = A)).card = c := by
    intro A hA
    rw [Finset.mem_powersetCard] at hA
    obtain ⟨-, hAcard⟩ := hA
    obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq A Jf (by rw [hAcard, hk])
    have hσi : A.image σ = Jf := by
      have h := hσ
      rw [Finset.map_eq_image] at h
      simpa using h
    let F : Equiv.Perm (Fin N) ≃ Equiv.Perm (Fin N) :=
      { toFun := fun π => π.trans σ
        invFun := fun π => π.trans σ.symm
        left_inv := by intro π; ext x; simp
        right_inv := by intro π; ext x; simp }
    have hF : ∀ π : Equiv.Perm (Fin N), Jf.image (F π) = (Jf.image π).image σ := by
      intro π
      show Jf.image (π.trans σ) = (Jf.image π).image σ
      rw [Finset.image_image]
      rfl
    have hmem2 : ∀ π : Equiv.Perm (Fin N),
        (π ∈ univ.filter (fun (π : Equiv.Perm (Fin N)) => Jf.image π = A))
          ↔ (F π ∈ univ.filter (fun (π : Equiv.Perm (Fin N)) => Jf.image π = Jf)) := by
      intro π
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hF]
      constructor
      · intro h; rw [h, hσi]
      · intro h
        have h' : (Jf.image π).image σ = A.image σ := by rw [h, hσi]
        exact image_perm_inj σ h'
    have hbij : (univ.filter (fun (π : Equiv.Perm (Fin N)) => Jf.image π = A)).card
        = (univ.filter (fun (π : Equiv.Perm (Fin N)) => Jf.image π = Jf)).card := by
      refine Finset.card_bij (fun π _ => F π) ?_ ?_ ?_
      · intro π hπ
        exact (hmem2 π).mp hπ
      · intro π1 _ π2 _ heq
        exact F.injective heq
      · intro π hπ
        refine ⟨F.symm π, (hmem2 _).mpr ?_, F.apply_symm_apply π⟩
        rwa [Equiv.apply_symm_apply]
    rw [hbij, hc]
  have htotal : (Fintype.card (Equiv.Perm (Fin N)) : ℕ)
      = ∑ A ∈ powersetCard k (univ : Finset (Fin N)),
          (univ.filter (fun (π : Equiv.Perm (Fin N)) => Jf.image π = A)).card := by
    have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Equiv.Perm (Fin N))))
      (t := powersetCard k (univ : Finset (Fin N)))
      (f := fun π : Equiv.Perm (Fin N) => Jf.image π) (fun a _ => hmemP a)
    simpa using h
  have hpc : (powersetCard k (univ : Finset (Fin N))).card = N.choose k := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hnum : (univ.filter (fun (π : Equiv.Perm (Fin N)) => Q (Jf.image π))).card
      = c * ((powersetCard k (univ : Finset (Fin N))).filter Q).card := by
    have h1 : (univ.filter (fun (π : Equiv.Perm (Fin N)) => Q (Jf.image π))).card
        = ∑ A ∈ powersetCard k (univ : Finset (Fin N)),
            ((univ.filter (fun (π : Equiv.Perm (Fin N)) => Q (Jf.image π))).filter
              (fun (π : Equiv.Perm (Fin N)) => Jf.image π = A)).card := by
      have h := Finset.card_eq_sum_card_fiberwise
        (s := univ.filter (fun (π : Equiv.Perm (Fin N)) => Q (Jf.image π)))
        (t := powersetCard k (univ : Finset (Fin N)))
        (f := fun π : Equiv.Perm (Fin N) => Jf.image π) (fun a _ => hmemP a)
      simpa using h
    rw [h1]
    have h2 : ∀ A ∈ powersetCard k (univ : Finset (Fin N)),
        ((univ.filter (fun (π : Equiv.Perm (Fin N)) => Q (Jf.image π))).filter
            (fun (π : Equiv.Perm (Fin N)) => Jf.image π = A)).card = if Q A then c else 0 := by
      intro A hA
      by_cases hQ : Q A
      · rw [if_pos hQ]
        have hset : (univ.filter (fun (π : Equiv.Perm (Fin N)) => Q (Jf.image π))).filter
            (fun (π : Equiv.Perm (Fin N)) => Jf.image π = A)
            = univ.filter (fun (π : Equiv.Perm (Fin N)) => Jf.image π = A) := by
          ext π
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨-, h⟩; exact h
          · intro h; exact ⟨by rw [h]; exact hQ, h⟩
        rw [hset, hconst A hA]
      · rw [if_neg hQ]
        have hset : (univ.filter (fun (π : Equiv.Perm (Fin N)) => Q (Jf.image π))).filter
            (fun (π : Equiv.Perm (Fin N)) => Jf.image π = A) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro π hπ
          rw [Finset.mem_filter] at hπ
          have h1 : Q (Jf.image π) := (Finset.mem_filter.mp hπ.1).2
          exact hQ (hπ.2 ▸ h1)
        rw [hset, Finset.card_empty]
    rw [Finset.sum_congr rfl h2]
    have h3 : c * ((powersetCard k (univ : Finset (Fin N))).filter Q).card
        = ∑ A ∈ (powersetCard k (univ : Finset (Fin N))).filter Q, c := by
      rw [Finset.sum_const, smul_eq_mul, mul_comm]
    rw [h3, ← Finset.sum_filter]
  have htot2 : (Fintype.card (Equiv.Perm (Fin N)) : ℕ)
      = c * (powersetCard k (univ : Finset (Fin N))).card := by
    rw [htotal]
    have h3 : ∑ A ∈ powersetCard k (univ : Finset (Fin N)), c
        = c * (powersetCard k (univ : Finset (Fin N))).card := by
      rw [Finset.sum_const, smul_eq_mul, mul_comm]
    rw [← h3]
    exact Finset.sum_congr rfl (fun A hA => hconst A hA)
  have hCpos : 0 < N.choose k := by
    rw [← hpc]
    exact Finset.card_pos.mpr ⟨Jf, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩⟩
  have hnumR : ((univ.filter (fun (π : Equiv.Perm (Fin N)) => Q (Jf.image π))).card : ℝ)
      = (c : ℝ) * (((powersetCard k (univ : Finset (Fin N))).filter Q).card : ℝ) := by
    rw [hnum]; push_cast; ring
  have hdenR : ((Fintype.card (Equiv.Perm (Fin N))) : ℝ)
      = (c : ℝ) * (((powersetCard k (univ : Finset (Fin N))).card : ℕ) : ℝ) := by
    rw [htot2]; push_cast; ring
  rw [prU_eq_card' (fun π : Equiv.Perm (Fin N) => Q (Jf.image π)), hnumR, hdenR, hpc]
  have hc0 : (c : ℝ) ≠ 0 := by exact_mod_cast hcpos.ne'
  have hC0 : ((N.choose k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hCpos.ne'
  field_simp


/-! ## Expectation helpers -/

lemma expU_sum' {α ι : Type} [Fintype α] (s : Finset ι) (f : ι → α → ℝ) :
    expU (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, expU (fun a => f i a) := by
  unfold expU
  have hL : (∑ a : α, ∑ i ∈ s, f i a) = ∑ i ∈ s, ∑ a : α, f i a := Finset.sum_comm
  rw [hL, Finset.sum_div]

open Classical in
lemma expU_indicator {α : Type} [Fintype α] (Q : α → Prop) (c : ℝ) :
    expU (fun a => if Q a then c else 0) = c * prU Q := by
  classical
  unfold expU prU
  rw [← Finset.sum_filter]
  have h2 : (∑ _x ∈ univ.filter Q, c) = ((univ.filter Q).card : ℝ) * c := by
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [h2]
  ring

lemma expU_mono' {α : Type} [Fintype α] [Nonempty α] {f g : α → ℝ} (h : ∀ a, f a ≤ g a) :
    expU f ≤ expU g := by
  unfold expU
  have hpos : (0:ℝ) < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun a _ => h a)) hpos.le

lemma expU_const_mul' {α : Type} [Fintype α] (c : ℝ) (f : α → ℝ) :
    expU (fun a => c * f a) = c * expU f := by
  unfold expU
  rw [← Finset.mul_sum]
  ring

lemma prU_or_le' {α : Type} [Fintype α] [Nonempty α] (P Q : α → Prop) :
    prU (fun a => P a ∨ Q a) ≤ prU P + prU Q := by
  classical
  have hcard : (univ.filter (fun a => P a ∨ Q a)).card
      ≤ (univ.filter P).card + (univ.filter Q).card := by
    have hsub : univ.filter (fun a => P a ∨ Q a)
        ⊆ (univ.filter P) ∪ (univ.filter Q) := by
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at ha ⊢
      exact ha
    calc (univ.filter (fun a => P a ∨ Q a)).card
        ≤ ((univ.filter P) ∪ (univ.filter Q)).card := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_union_le _ _
  have hpos : (0:ℝ) ≤ (Fintype.card α : ℝ) := by positivity
  rw [prU_eq_card' (fun a => P a ∨ Q a), prU_eq_card' P, prU_eq_card' Q, ← add_div]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) hpos

/-- The outside-hint part of a row is contained in the image of the difference. -/
lemma rowImage_sdiff_subset {N m : ℕ} (π : Equiv.Perm (Fin N)) (j : ℕ) (T S : Finset ℕ) :
    rowImage N m π j T \ rowImage N m π j S ⊆ rowImage N m π j (T \ S) := by
  classical
  intro q hq
  rw [Finset.mem_sdiff] at hq
  obtain ⟨hqT, hqS⟩ := hq
  rw [rowImage, Finset.mem_image] at hqT hqS ⊢
  obtain ⟨i, hi, hdiv⟩ := hqT
  rw [Finset.mem_filter] at hi
  obtain ⟨-, hiT, hmod⟩ := hi
  refine ⟨i, ?_, hdiv⟩
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, Finset.mem_sdiff.mpr ⟨hiT, fun hiS =>
    hqS ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiS, hmod⟩, hdiv⟩⟩, hmod⟩

/-! ## The hypergeometric tail bound -/

lemma hypergeom_tail (N k W θ : ℕ) (hN : 0 < N) (hkN : k ≤ N)
    (hW : (k:ℝ) * (W:ℝ) / (N:ℝ) ≤ (θ:ℝ)) (hθ : 0 < θ)
    (I : Finset (Fin N)) (hI : I.card ≤ W) :
    (((powersetCard k (univ : Finset (Fin N))).filter
        (fun A => θ ≤ (A ∩ I).card)).card : ℝ)
        / ((powersetCard k (univ : Finset (Fin N))).card : ℝ)
      ≤ Real.exp (-(((θ:ℝ) - (k:ℝ) * (W:ℝ) / (N:ℝ))^2 / (2 * (θ:ℝ)))) := by
  classical
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hμle : (k:ℝ) * (I.card:ℝ) / (N:ℝ) ≤ (k:ℝ) * (W:ℝ) / (N:ℝ) := by
    have h1 : (I.card:ℝ) ≤ (W:ℝ) := by exact_mod_cast hI
    apply div_le_div_of_nonneg_right _ hNpos.le
    exact mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg k)
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · have hempty : (powersetCard k (univ : Finset (Fin N))).filter
        (fun A => θ ≤ (A ∩ I).card) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro A hA
      rw [Finset.mem_filter] at hA
      have hAcard : A.card = 0 := by rw [← hk0]; exact (Finset.mem_powersetCard.mp hA.1).2
      rw [Finset.card_eq_zero.mp hAcard] at hA
      simp only [Finset.empty_inter, Finset.card_empty] at hA
      omega
    rw [hempty, Finset.card_empty, Nat.cast_zero, zero_div]
    try positivity
  rcases Nat.eq_zero_or_pos I.card with hI0 | hIpos
  · have hIe : I = ∅ := Finset.card_eq_zero.mp hI0
    have hempty : (powersetCard k (univ : Finset (Fin N))).filter
        (fun A => θ ≤ (A ∩ I).card) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro A hA
      rw [Finset.mem_filter] at hA
      rw [hIe] at hA
      simp only [Finset.inter_empty, Finset.card_empty] at hA
      omega
    rw [hempty, Finset.card_empty, Nat.cast_zero, zero_div]
    try positivity
  · have hμpos : 0 < (k:ℝ) * (I.card:ℝ) / (N:ℝ) := by
      have h1 : (0:ℝ) < (k:ℝ) := by exact_mod_cast hkpos
      have h2 : (0:ℝ) < (I.card:ℝ) := by exact_mod_cast hIpos
      positivity
    have ht : 0 ≤ (θ:ℝ) - (k:ℝ) * (I.card:ℝ) / (N:ℝ) := by linarith
    have hkey := (lemma_4_1 N k hkN I hμpos).1 ((θ:ℝ) - (k:ℝ) * (I.card:ℝ) / (N:ℝ)) ht
    have hfe : ((powersetCard k (univ : Finset (Fin N))).filter
          (fun A => θ ≤ (A ∩ I).card)).card
        = ((powersetCard k (univ : Finset (Fin N))).filter
          (fun A => (k:ℝ) * (I.card:ℝ) / (N:ℝ) + ((θ:ℝ) - (k:ℝ) * (I.card:ℝ) / (N:ℝ))
            ≤ ((A ∩ I).card : ℝ))).card := by
      congr 1
      apply Finset.filter_congr
      intro A _
      rw [show (k:ℝ) * (I.card:ℝ) / (N:ℝ) + ((θ:ℝ) - (k:ℝ) * (I.card:ℝ) / (N:ℝ))
          = (θ:ℝ) by ring]
      exact Nat.cast_le.symm
    rw [hfe]
    refine le_trans hkey (Real.exp_le_exp.mpr ?_)
    have ht2 : (0:ℝ) < (θ:ℝ) := by exact_mod_cast hθ
    have hsum : (k:ℝ) * (I.card:ℝ) / (N:ℝ) + ((θ:ℝ) - (k:ℝ) * (I.card:ℝ) / (N:ℝ))
        = (θ:ℝ) := by ring
    rw [hsum]
    have hnn : 0 ≤ (θ:ℝ) - (k:ℝ) * (W:ℝ) / (N:ℝ) := by linarith
    have hsq : ((θ:ℝ) - (k:ℝ) * (W:ℝ) / (N:ℝ))^2
        ≤ ((θ:ℝ) - (k:ℝ) * (I.card:ℝ) / (N:ℝ))^2 :=
      by nlinarith [hnn, hμle]
    have hdiv := div_le_div_of_nonneg_right hsq (by linarith : (0:ℝ) ≤ 2 * (θ:ℝ))
    linarith

/-! ## Claim 2 of Lemma 5.3: the expected overloaded mass is at most `D η²` -/

/-! ### The arithmetic of the two thresholds -/

lemma arith_L (A C : ℕ) (L : ℝ) (hL : 1 ≤ L) (hA : 1 ≤ A) (hC : 1000 * A + 1000 ≤ C) :
    (2 * (A:ℝ) + 12) * Real.log L + Real.log 4 ≤ (C:ℝ) * L / 32 := by
  have hA1 : (1:ℝ) ≤ (A:ℝ) := by exact_mod_cast hA
  have hC1 : 1000 * (A:ℝ) + 1000 ≤ (C:ℝ) := by exact_mod_cast hC
  have hL0 : (0:ℝ) ≤ L := by linarith
  have hlog : Real.log L ≤ L := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < L by linarith)
    linarith
  have hlog4 : Real.log 4 ≤ 4 := by
    have h : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
    have h2 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9
      linarith
    linarith
  have hkey : 2 * (A:ℝ) + 12 + 4 ≤ (C:ℝ) / 32 := by linarith
  have h1 : (2 * (A:ℝ) + 12) * Real.log L ≤ (2 * (A:ℝ) + 12) * L :=
    mul_le_mul_of_nonneg_left hlog (by linarith)
  calc (2 * (A:ℝ) + 12) * Real.log L + Real.log 4
      ≤ (2 * (A:ℝ) + 12) * L + 4 := by linarith
    _ ≤ (2 * (A:ℝ) + 12) * L + 4 * L := by linarith
    _ = (2 * (A:ℝ) + 12 + 4) * L := by ring
    _ ≤ ((C:ℝ) / 32) * L := mul_le_mul_of_nonneg_right hkey hL0
    _ = (C:ℝ) * L / 32 := by ring

lemma arith_M (A C : ℕ) (L : ℝ) (hL : 1 ≤ L) (hA : 1 ≤ A) (hC : 1000 * A + 1000 ≤ C) :
    (2 * (A:ℝ) + 12) * Real.log L + Real.log 4 ≤ ((C:ℝ) * lg (L + 2) + 5) / 8 := by
  have hA1 : (1:ℝ) ≤ (A:ℝ) := by exact_mod_cast hA
  have hC1 : 1000 * (A:ℝ) + 1000 ≤ (C:ℝ) := by exact_mod_cast hC
  have hL0 : (0:ℝ) ≤ L := by linarith
  have hln2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hln2le : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9
    linarith
  have hL20 : (0:ℝ) < L + 2 := by linarith
  have hg1 : (1:ℝ) ≤ lg (L + 2) := by
    rw [lg, Real.le_logb_iff_rpow_le (by norm_num : (1:ℝ) < 2) hL20]
    simpa using (show (2:ℝ) ≤ L + 2 by linarith)
  have hgl : (0:ℝ) ≤ lg (L + 2) := by linarith
  have hlogL2 : Real.log L ≤ lg (L + 2) := by
    have h1 : Real.log L ≤ Real.log (L + 2) := Real.log_le_log (by linarith) (by linarith)
    have h2 : Real.log (L + 2) ≤ lg (L + 2) := by
      rw [lg, Real.logb, le_div_iff₀ hln2]
      nlinarith [Real.log_nonneg (by linarith : (1:ℝ) ≤ L + 2), hln2le]
    linarith
  have hlog4 : Real.log 4 ≤ 4 := by
    have h : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
    have h2 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9
      linarith
    linarith
  have hkey : 2 * (A:ℝ) + 12 + 4 ≤ (C:ℝ) / 8 := by linarith
  have h1 : (2 * (A:ℝ) + 12) * Real.log L ≤ (2 * (A:ℝ) + 12) * lg (L + 2) :=
    mul_le_mul_of_nonneg_left hlogL2 (by linarith)
  calc (2 * (A:ℝ) + 12) * Real.log L + Real.log 4
      ≤ (2 * (A:ℝ) + 12) * lg (L + 2) + 4 := by linarith
    _ ≤ (2 * (A:ℝ) + 12) * lg (L + 2) + 4 * lg (L + 2) := by nlinarith
    _ = (2 * (A:ℝ) + 12 + 4) * lg (L + 2) := by ring
    _ ≤ ((C:ℝ) / 8) * lg (L + 2) := mul_le_mul_of_nonneg_right hkey hgl
    _ = (C:ℝ) * lg (L + 2) / 8 := by ring
    _ ≤ ((C:ℝ) * lg (L + 2) + 5) / 8 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        linarith

/-- `η² = exp (-(2 A log log n))`. -/
lemma eta_sq_exp (P : HintParams) (hP : 0 < P.lgn) :
    P.eta ^ 2 = Real.exp (-(2 * (P.A:ℝ) * Real.log P.lgn)) := by
  have hA : P.eta = Real.exp (-((P.A:ℝ) * Real.log P.lgn)) := by
    rw [HintParams.eta, ← Real.rpow_natCast P.lgn P.A, ← Real.rpow_neg hP.le,
      Real.rpow_def_of_pos hP]
    congr 1
    ring
  rw [hA, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The `L ^ (-12)` factor as an exponential. -/
lemma rpow_neg_twelve (L : ℝ) (hL : 0 < L) :
    L ^ (-12:ℝ) = Real.exp (-(12 * Real.log L)) := by
  rw [Real.rpow_def_of_pos hL]
  congr 1
  ring

lemma b1_le (P : HintParams) (hA : 1 ≤ P.A) (hC : 1000 * P.A + 1000 ≤ P.C)
    (hL1 : 1 ≤ P.lgn) :
    Real.exp (-((P.C:ℝ) * P.lgn / 32)) ≤ P.eta ^ 2 * P.lgn ^ (-12:ℝ) / 4 := by
  have hP : 0 < P.lgn := by linarith
  have harith := arith_L P.A P.C P.lgn hL1 hA hC
  have hexp : Real.exp (-((P.C:ℝ) * P.lgn / 32))
      ≤ Real.exp (-((2 * (P.A:ℝ) + 12) * Real.log P.lgn + Real.log 4)) := by
    apply Real.exp_le_exp.mpr
    linarith
  refine le_trans hexp (le_of_eq ?_)
  rw [eta_sq_exp P hP, rpow_neg_twelve P.lgn hP]
  rw [div_eq_mul_inv, show (4:ℝ)⁻¹ = Real.exp (-(Real.log 4)) by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

lemma b2_le (P : HintParams) (hA : 1 ≤ P.A) (hC : 1000 * P.A + 1000 ≤ P.C)
    (hL1 : 1 ≤ P.lgn) :
    Real.exp (-(((P.C:ℝ) * lg (P.lgn + 2) + 5) / 8)) ≤ P.eta ^ 2 * P.lgn ^ (-12:ℝ) / 4 := by
  have hP : 0 < P.lgn := by linarith
  have harith := arith_M P.A P.C P.lgn hL1 hA hC
  have hexp : Real.exp (-(((P.C:ℝ) * lg (P.lgn + 2) + 5) / 8))
      ≤ Real.exp (-((2 * (P.A:ℝ) + 12) * Real.log P.lgn + Real.log 4)) := by
    apply Real.exp_le_exp.mpr
    linarith
  refine le_trans hexp (le_of_eq ?_)
  rw [eta_sq_exp P hP, rpow_neg_twelve P.lgn hP]
  rw [div_eq_mul_inv, show (4:ℝ)⁻¹ = Real.exp (-(Real.log 4)) by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-! ### Per-row probability bounds -/

/-- `⌈x⌉ ≤ x + 1` for `x ≥ 0`. -/
lemma ceil_le_add_one {x : ℝ} (hx : 0 ≤ x) : ((⌈x⌉₊ : ℕ) : ℝ) ≤ x + 1 :=
  le_of_lt (Nat.ceil_lt_add_one hx)

/-- `1 ≤ L ⇒ 1 ≤ L²`. -/
lemma one_le_sq_lgn (P : HintParams) (h : 1 ≤ P.lgn) : (1:ℝ) ≤ P.lgn ^ 2 := by
  have h0 : (0:ℝ) ≤ P.lgn := by linarith
  have h2 : (1:ℝ) ≤ P.lgn * P.lgn := by
    have := mul_le_mul h h (by norm_num : (0:ℝ) ≤ 1) h0
    simpa using this
  have h4 : P.lgn * P.lgn = P.lgn ^ 2 := by ring
  linarith

/-- `1 ≤ L ⇒ 1 ≤ L³`. -/
lemma one_le_cu_lgn (P : HintParams) (h : 1 ≤ P.lgn) : (1:ℝ) ≤ P.lgn ^ 3 := by
  have h0 : (0:ℝ) ≤ P.lgn := by linarith
  have h2 : (1:ℝ) ≤ P.lgn * P.lgn := by
    have := mul_le_mul h h (by norm_num : (0:ℝ) ≤ 1) h0
    simpa using this
  have h3 : (1:ℝ) ≤ (P.lgn * P.lgn) * P.lgn := by
    have := mul_le_mul h2 h (by norm_num : (0:ℝ) ≤ 1) (by positivity : (0:ℝ) ≤ P.lgn * P.lgn)
    simpa using this
  have h4 : (P.lgn * P.lgn) * P.lgn = P.lgn ^ 3 := by ring
  linarith

/-- **Second claim, hint regime**, as in the paper (`lem:balanced-load` = Lemma 4.1, applied to the
hypergeometric hint load of one row): the load of the hint `J` in row `j` exceeds `B_X` with
probability at most `e^{-C log n/32}`.  If `B_X = N_max` then the load can never exceed it (the row
has at most `N_max` positions), so the probability is `0` — this is the first of the paper's two
`B_X` regimes ("if `B_X` ... is capped at `N_max`, the corresponding condition must hold"). -/
lemma row_prU_hint (P : HintParams) (N X Y : ℕ) (hargs : P.NodeArgs N X Y)
    (hnl : P.NonLeaf N X Y) (hA : 1 ≤ P.A) (hC : 1000 * P.A + 1000 ≤ P.C)
    (J : Finset ℕ) (hJ : J ⊆ range N) (hJX : J.card ≤ X) (j : ℕ) :
    prU (fun π : Equiv.Perm (Fin N) =>
        P.BX N X Y < (rowImage N (P.rows X Y) π j J).card)
      ≤ (if P.BX N X Y = P.Nmax N X Y then 0
          else Real.exp (-((P.C:ℝ) * P.lgn / 32))) := by
  classical
  have hm1 : 1 ≤ P.rows X Y := rows_pos P N X Y hargs hnl
  have hN1 : 1 ≤ N := hargs.2.2.1
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN1
  have hC1 : (1:ℝ) ≤ (P.C:ℝ) := by
    have h : 1 ≤ P.C := by omega
    exact_mod_cast h
  have hlgn : 0 < P.lgn := by
    rw [HintParams.lgn, lg]
    exact Real.logb_pos (by norm_num) (by exact_mod_cast hargs.1)
  have hn2 : (2:ℝ) ≤ (P.n:ℝ) := by exact_mod_cast hargs.1
  have hlgn1 : 1 ≤ P.lgn := by
    rw [HintParams.lgn, lg, Real.le_logb_iff_rpow_le (by norm_num : (1:ℝ) < 2)
      (by linarith : (0:ℝ) < (P.n:ℝ))]
    simpa using hn2
  have hlgn3 : (1:ℝ) ≤ P.lgn ^ 3 := one_le_cu_lgn P hlgn1
  have hlgn3pos : (0:ℝ) < P.lgn ^ 3 := by linarith
  have hmpos : (0:ℝ) < (P.rows X Y : ℝ) := by exact_mod_cast hm1
  by_cases hcase : P.BX N X Y = P.Nmax N X Y
  · rw [if_pos hcase]
    rw [prU_eq_card']
    have hempty : (univ.filter (fun π : Equiv.Perm (Fin N) =>
        P.BX N X Y < (rowImage N (P.rows X Y) π j J).card)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro π hπ
      rw [Finset.mem_filter] at hπ
      have h1 : (rowImage N (P.rows X Y) π j J).card ≤ P.BX N X Y := by
        rw [hcase]
        exact le_trans (rowImage_card_le_rowLen (N := N) (m := P.rows X Y) (j := j) π J)
          (rowLen_le_Nmax N (P.rows X Y) j hm1)
      omega
    rw [hempty, Finset.card_empty, Nat.cast_zero, zero_div]
  · rw [if_neg hcase]
    have hBXeq : P.BX N X Y = ⌈P.lgn ^ 3 + (P.C:ℝ) * P.lgn ^ 2⌉₊ := by
      rw [HintParams.BX]
      rcases min_cases (P.Nmax N X Y) ⌈P.lgn ^ 3 + (P.C:ℝ) * P.lgn ^ 2⌉₊ with h | h
      · exact absurd h.1 hcase
      · exact h.1
    set K : ℕ := (finSet J).card with hK
    have hKJ : K = J.card := hK.trans (card_finSet J hJ)
    set I : Finset (Fin N) := univ.filter (fun q : Fin N => q.val % (P.rows X Y) = j) with hI
    have hIN : I.card = rowLen N (P.rows X Y) j := by
      rw [hI]
      unfold rowLen
      refine Finset.card_bij
        (fun (q : Fin N) (_ : q ∈ univ.filter (fun q : Fin N => q.val % (P.rows X Y) = j)) =>
          q.val) ?_ ?_ ?_
      · intro q hq
        rw [Finset.mem_filter] at hq
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr q.isLt, hq.2⟩
      · intro q1 h1 q2 h2 heq
        exact Fin.ext heq
      · intro p hp
        rw [Finset.mem_filter] at hp
        exact ⟨⟨p, Finset.mem_range.mp hp.1⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.2⟩, rfl⟩
    have hIle : I.card ≤ P.Nmax N X Y := by
      rw [hIN]
      exact rowLen_le_Nmax N (P.rows X Y) j hm1
    have hKN : K ≤ N := by
      rw [hKJ]
      calc J.card ≤ (range N).card := Finset.card_le_card hJ
        _ = N := Finset.card_range N
    have hKX : (K:ℝ) ≤ (X:ℝ) := by
      rw [hKJ]
      exact_mod_cast hJX
    have hWle : (P.Nmax N X Y : ℝ) ≤ (N:ℝ) / (P.rows X Y : ℝ) + 1 := by
      have h1 : ((⌈(N:ℝ) / (P.rows X Y : ℝ)⌉₊ : ℕ) : ℝ) ≤ (N:ℝ) / (P.rows X Y : ℝ) + 1 :=
        ceil_le_add_one (by positivity)
      exact h1
    have hXm : (X:ℝ) ≤ P.lgn ^ 3 * (P.rows X Y : ℝ) := by
      have h2 : ⌈(X:ℝ) / P.lgn ^ 3⌉₊ ≤ P.rows X Y := le_max_right _ _
      have h2' : ((⌈(X:ℝ) / P.lgn ^ 3⌉₊ : ℕ) : ℝ) ≤ (P.rows X Y : ℝ) := by exact_mod_cast h2
      have h3 : (X:ℝ) / P.lgn ^ 3 ≤ ((⌈(X:ℝ) / P.lgn ^ 3⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      have h1 : (X:ℝ) / P.lgn ^ 3 ≤ (P.rows X Y : ℝ) := le_trans h3 h2'
      rw [div_le_iff₀ hlgn3pos] at h1
      linarith
    have hKW : (K:ℝ) * (P.Nmax N X Y : ℝ) ≤ P.lgn ^ 3 * (N:ℝ) + (N:ℝ) := by
      have h1 : (K:ℝ) * (P.Nmax N X Y : ℝ)
          ≤ (X:ℝ) * ((N:ℝ) / (P.rows X Y : ℝ) + 1) :=
        mul_le_mul hKX hWle (by positivity) (by linarith)
      have h2 : (X:ℝ) * ((N:ℝ) / (P.rows X Y : ℝ)) ≤ P.lgn ^ 3 * (N:ℝ) := by
        have h3 : (X:ℝ) / (P.rows X Y : ℝ) ≤ P.lgn ^ 3 := by
          rw [div_le_iff₀ hmpos]
          linarith
        calc (X:ℝ) * ((N:ℝ) / (P.rows X Y : ℝ)) = ((X:ℝ) / (P.rows X Y : ℝ)) * (N:ℝ) := by ring
          _ ≤ P.lgn ^ 3 * (N:ℝ) := mul_le_mul_of_nonneg_right h3 (by linarith)
      have h5 : (X:ℝ) * ((N:ℝ) / (P.rows X Y : ℝ) + 1) ≤ P.lgn ^ 3 * (N:ℝ) + (N:ℝ) := by
        have h6 : (X:ℝ) * ((N:ℝ) / (P.rows X Y : ℝ) + 1)
            = (X:ℝ) * ((N:ℝ) / (P.rows X Y : ℝ)) + (X:ℝ) := by ring
        have h7 : (X:ℝ) ≤ (N:ℝ) := by exact_mod_cast hargs.2.2.2.2.1
        rw [h6]
        linarith
      linarith
    have hmean : (K:ℝ) * (P.Nmax N X Y : ℝ) / (N:ℝ) ≤ (P.BX N X Y : ℝ) + 1 := by
      have hC2 : (1:ℝ) ≤ (P.C:ℝ) * P.lgn ^ 2 := by
        have h1 : (1:ℝ) ≤ P.lgn ^ 2 := one_le_sq_lgn P hlgn1
        calc (1:ℝ) = 1 * 1 := by norm_num
          _ ≤ (P.C:ℝ) * P.lgn ^ 2 := mul_le_mul hC1 h1 (by norm_num) (by linarith)
      have h6 : P.lgn ^ 3 * (N:ℝ) + (N:ℝ)
          ≤ (P.lgn ^ 3 + (P.C:ℝ) * P.lgn ^ 2) * (N:ℝ) := by
        have h7 : (0:ℝ) ≤ (P.C:ℝ) * P.lgn ^ 2 * (N:ℝ) := by positivity
        nlinarith
      have h8 : (P.lgn ^ 3 + (P.C:ℝ) * P.lgn ^ 2)
          ≤ ((⌈P.lgn ^ 3 + (P.C:ℝ) * P.lgn ^ 2⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      have h9 : (P.lgn ^ 3 + (P.C:ℝ) * P.lgn ^ 2) * (N:ℝ)
          ≤ ((⌈P.lgn ^ 3 + (P.C:ℝ) * P.lgn ^ 2⌉₊ : ℕ) : ℝ) * (N:ℝ) :=
        mul_le_mul_of_nonneg_right h8 (by linarith)
      have h10 : (P.lgn ^ 3 + (P.C:ℝ) * P.lgn ^ 2) * (N:ℝ)
          ≤ (P.BX N X Y : ℝ) * (N:ℝ) := by rw [hBXeq]; exact h9
      rw [div_le_iff₀ hNpos]
      have h11 : (K:ℝ) * (P.Nmax N X Y : ℝ) ≤ (P.BX N X Y : ℝ) * (N:ℝ) := by
        nlinarith [hKW, h6, h10]
      nlinarith [h11]
    have htail := hypergeom_tail N K (P.Nmax N X Y) (P.BX N X Y + 1) hN1 hKN
      (by push_cast; linarith [hmean]) (Nat.succ_pos _) I hIle
    have hbridge : prU (fun π : Equiv.Perm (Fin N) =>
          P.BX N X Y < (rowImage N (P.rows X Y) π j J).card)
        = (((powersetCard K (univ : Finset (Fin N))).filter
            (fun A => P.BX N X Y + 1 ≤ (A ∩ I).card)).card : ℝ)
          / ((powersetCard K (univ : Finset (Fin N))).card : ℝ) := by
      have h1 : ((fun π : Equiv.Perm (Fin N) =>
          P.BX N X Y < (rowImage N (P.rows X Y) π j J).card))
          = (fun π : Equiv.Perm (Fin N) =>
            P.BX N X Y + 1 ≤ (rowImage N (P.rows X Y) π j J).card) := by
        funext π; exact propext (Nat.lt_iff_add_one_le ..)
      rw [h1]
      have h2 : ((fun π : Equiv.Perm (Fin N) =>
          P.BX N X Y + 1 ≤ (rowImage N (P.rows X Y) π j J).card))
          = (fun π : Equiv.Perm (Fin N) =>
            P.BX N X Y + 1 ≤ ((((finSet J).image π).filter
              (fun q => q.val % (P.rows X Y) = j)).card)) := by
        funext π; rw [rowImage_card_eq]
      rw [h2]
      have hQ : ∀ A : Finset (Fin N),
          A.filter (fun q => q.val % (P.rows X Y) = j) = A ∩ I := by
        intro A
        ext q
        simp [hI]
      simp only [hQ]
      rw [prU_image_eq (finSet J) (fun A => P.BX N X Y + 1 ≤ (A ∩ I).card)]
      rw [show (finSet J).card = K from hK.symm]
      rw [Finset.filter_congr_decidable (powersetCard K (univ : Finset (Fin N)))
        (fun A => P.BX N X Y + 1 ≤ (A ∩ I).card)]
    rw [hbridge]
    refine le_trans htail (Real.exp_le_exp.mpr ?_)
    push_cast
    set Tm : ℝ := (K:ℝ) * (P.Nmax N X Y : ℝ) / (N:ℝ) with hTm
    set T : ℝ := (P.BX N X Y : ℝ) + 1 with hT
    have hTpos : (0:ℝ) < T := by rw [hT]; positivity
    have hTmle : Tm ≤ P.lgn ^ 3 + 1 := by
      rw [hTm, div_le_iff₀ hNpos]
      linarith [hKW]
    have hCX : (P.C:ℝ) * P.lgn ^ 2 ≤ T - Tm := by
      have h8 : (P.BX N X Y : ℝ) = ((⌈P.lgn ^ 3 + (P.C:ℝ) * P.lgn ^ 2⌉₊ : ℕ) : ℝ) := by
        rw [hBXeq]
      have h9 : P.lgn ^ 3 + (P.C:ℝ) * P.lgn ^ 2
          ≤ ((⌈P.lgn ^ 3 + (P.C:ℝ) * P.lgn ^ 2⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      have h10 : ((⌈P.lgn ^ 3 + (P.C:ℝ) * P.lgn ^ 2⌉₊ : ℕ) : ℝ)
          ≤ P.lgn ^ 3 + (P.C:ℝ) * P.lgn ^ 2 + 1 := ceil_le_add_one (by positivity)
      rw [hT, h8]
      linarith
    have hTub : T ≤ 4 * ((P.C:ℝ) * P.lgn ^ 3) := by
      have h8 : (P.BX N X Y : ℝ) = ((⌈P.lgn ^ 3 + (P.C:ℝ) * P.lgn ^ 2⌉₊ : ℕ) : ℝ) := by
        rw [hBXeq]
      have h9 : P.lgn ^ 3 + (P.C:ℝ) * P.lgn ^ 2
          ≤ ((⌈P.lgn ^ 3 + (P.C:ℝ) * P.lgn ^ 2⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      have hA1 : (1:ℝ) ≤ (P.C:ℝ) * P.lgn ^ 3 := by
        calc (1:ℝ) = 1 * 1 := by norm_num
          _ ≤ (P.C:ℝ) * P.lgn ^ 3 := mul_le_mul hC1 hlgn3 (by norm_num) (by linarith)
      have hB1 : P.lgn ^ 3 ≤ (P.C:ℝ) * P.lgn ^ 3 := by
        have h := mul_le_mul_of_nonneg_right hC1 (by linarith : (0:ℝ) ≤ P.lgn ^ 3)
        simpa using h
      have hC2 : (P.C:ℝ) * P.lgn ^ 2 ≤ (P.C:ℝ) * P.lgn ^ 3 := by
        have h3 : P.lgn ^ 2 ≤ P.lgn ^ 3 := by
          calc P.lgn ^ 2 = P.lgn ^ 2 * 1 := by ring
            _ ≤ P.lgn ^ 2 * P.lgn := mul_le_mul_of_nonneg_left hlgn1 (by positivity)
            _ = P.lgn ^ 3 := by ring
        exact mul_le_mul_of_nonneg_left h3 (by linarith)
      have h10 : ((⌈P.lgn ^ 3 + (P.C:ℝ) * P.lgn ^ 2⌉₊ : ℕ) : ℝ)
          ≤ P.lgn ^ 3 + (P.C:ℝ) * P.lgn ^ 2 + 1 := ceil_le_add_one (by positivity)
      rw [hT, h8]
      linarith
    have hCl : (0:ℝ) ≤ (P.C:ℝ) * P.lgn ^ 2 := by positivity
    have hsq : ((P.C:ℝ) * P.lgn ^ 2)^2 ≤ (T - Tm)^2 := by
      have h := mul_self_le_mul_self hCl hCX
      calc ((P.C:ℝ) * P.lgn ^ 2)^2 = ((P.C:ℝ) * P.lgn ^ 2) * ((P.C:ℝ) * P.lgn ^ 2) := by ring
        _ ≤ (T - Tm) * (T - Tm) := h
        _ = (T - Tm)^2 := by ring
    have hstep : (P.C:ℝ) * P.lgn / 32 * (2 * T) ≤ ((P.C:ℝ) * P.lgn ^ 2)^2 / 4 := by
      have h1 : (P.C:ℝ) * P.lgn / 32 * (2 * T)
          ≤ (P.C:ℝ) * P.lgn / 32 * (2 * (4 * ((P.C:ℝ) * P.lgn ^ 3))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
      have h2 : (P.C:ℝ) * P.lgn / 32 * (2 * (4 * ((P.C:ℝ) * P.lgn ^ 3)))
          = ((P.C:ℝ) * P.lgn ^ 2)^2 / 4 := by ring
      linarith [h1, h2]
    have hexp1 : (P.C:ℝ) * P.lgn / 32 ≤ (T - Tm)^2 / (2 * T) := by
      rw [le_div_iff₀ (by linarith : (0:ℝ) < 2 * T)]
      nlinarith [hstep, hsq]
    calc -((T - Tm)^2 / (2 * T)) ≤ -((P.C:ℝ) * P.lgn / 32) := by linarith
      _ = -((P.C:ℝ) * P.lgn / 32) := rfl

/-- **Second claim, outside-hint regime**, as in the paper (`lem:balanced-load` = Lemma 4.1, applied to
the hypergeometric outside-hint load of one row): the load of the outside hint `x \ J` in row `j`
exceeds `B_Y` with probability at most `e^{-(C lg(log n + 2) + 5)/8}`.  If `B_Y = N_max` then the
load can never exceed it, so the probability is `0` — the second of the paper's two `B_X`/`B_Y`
regimes. -/
lemma row_prU_outside (P : HintParams) (N X Y : ℕ) (hargs : P.NodeArgs N X Y)
    (hnl : P.NonLeaf N X Y) (K : Finset ℕ) (hK : K ⊆ range N) (hKY : K.card ≤ Y) (j : ℕ) :
    prU (fun π : Equiv.Perm (Fin N) =>
        P.BY N X Y < (rowImage N (P.rows X Y) π j K).card)
      ≤ (if P.BY N X Y = P.Nmax N X Y then 0
          else Real.exp (-(((P.C:ℝ) * lg (P.lgn + 2) + 5) / 8))) := by
  classical
  have hm1 : 1 ≤ P.rows X Y := rows_pos P N X Y hargs hnl
  have hN1 : 1 ≤ N := hargs.2.2.1
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN1
  have hmpos : (0:ℝ) < (P.rows X Y : ℝ) := by exact_mod_cast hm1
  have hlgn : 0 < P.lgn := by
    rw [HintParams.lgn, lg]
    exact Real.logb_pos (by norm_num) (by exact_mod_cast hargs.1)
  by_cases hcase : P.BY N X Y = P.Nmax N X Y
  · rw [if_pos hcase]
    rw [prU_eq_card']
    have hempty : (univ.filter (fun π : Equiv.Perm (Fin N) =>
        P.BY N X Y < (rowImage N (P.rows X Y) π j K).card)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro π hπ
      rw [Finset.mem_filter] at hπ
      have h1 : (rowImage N (P.rows X Y) π j K).card ≤ P.BY N X Y := by
        rw [hcase]
        exact le_trans (rowImage_card_le_rowLen (N := N) (m := P.rows X Y) (j := j) π K)
          (rowLen_le_Nmax N (P.rows X Y) j hm1)
      omega
    rw [hempty, Finset.card_empty, Nat.cast_zero, zero_div]
  · rw [if_neg hcase]
    have hBYeq : P.BY N X Y = ⌈(P.C:ℝ) * lg (P.lgn + 2)⌉₊ + 4 := by
      rw [HintParams.BY]
      rcases min_cases (P.Nmax N X Y) (⌈(P.C:ℝ) * lg (P.lgn + 2)⌉₊ + 4) with h | h
      · exact absurd h.1 hcase
      · exact h.1
    set Kc : ℕ := (finSet K).card with hKs
    have hKsJ : Kc = K.card := hKs.trans (card_finSet K hK)
    set I : Finset (Fin N) := univ.filter (fun q : Fin N => q.val % (P.rows X Y) = j) with hI
    have hIN : I.card = rowLen N (P.rows X Y) j := by
      rw [hI]
      unfold rowLen
      refine Finset.card_bij
        (fun (q : Fin N) (_ : q ∈ univ.filter (fun q : Fin N => q.val % (P.rows X Y) = j)) =>
          q.val) ?_ ?_ ?_
      · intro q hq
        rw [Finset.mem_filter] at hq
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr q.isLt, hq.2⟩
      · intro q1 h1 q2 h2 heq
        exact Fin.ext heq
      · intro p hp
        rw [Finset.mem_filter] at hp
        exact ⟨⟨p, Finset.mem_range.mp hp.1⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.2⟩, rfl⟩
    have hIle : I.card ≤ P.Nmax N X Y := by
      rw [hIN]
      exact rowLen_le_Nmax N (P.rows X Y) j hm1
    have hKN : Kc ≤ N := by
      rw [hKsJ]
      calc K.card ≤ (range N).card := Finset.card_le_card hK
        _ = N := Finset.card_range N
    have hWle : (P.Nmax N X Y : ℝ) ≤ (N:ℝ) / (P.rows X Y : ℝ) + 1 := by
      have h1 : ((⌈(N:ℝ) / (P.rows X Y : ℝ)⌉₊ : ℕ) : ℝ) ≤ (N:ℝ) / (P.rows X Y : ℝ) + 1 :=
        ceil_le_add_one (by positivity)
      exact h1
    have hKY' : (Kc:ℝ) ≤ (Y:ℝ) := by
      rw [hKsJ]
      exact_mod_cast hKY
    have hmY : (Y:ℝ) ≤ (P.rows X Y : ℝ) := by
      have h := le_max_left (Y : ℕ) ⌈(X:ℝ) / P.lgn ^ 3⌉₊
      rw [← HintParams.rows] at h
      exact_mod_cast h
    have hBY4 : 4 ≤ P.BY N X Y := by
      rw [hBYeq]
      omega
    have hmean : (Kc:ℝ) * (P.Nmax N X Y : ℝ) / (N:ℝ) ≤ ((P.BY N X Y : ℝ) + 1) / 2 := by
      have h1 : (Kc:ℝ) * (P.Nmax N X Y : ℝ)
          ≤ (Y:ℝ) * ((N:ℝ) / (P.rows X Y : ℝ) + 1) :=
        mul_le_mul hKY' hWle (by positivity) (by linarith)
      have h2 : (Y:ℝ) * ((N:ℝ) / (P.rows X Y : ℝ)) ≤ (N:ℝ) := by
        have h3 : (Y:ℝ) / (P.rows X Y : ℝ) ≤ 1 := by
          rw [div_le_one hmpos]
          exact hmY
        calc (Y:ℝ) * ((N:ℝ) / (P.rows X Y : ℝ)) = ((Y:ℝ) / (P.rows X Y : ℝ)) * (N:ℝ) := by ring
          _ ≤ 1 * (N:ℝ) := mul_le_mul_of_nonneg_right h3 (by linarith)
          _ = (N:ℝ) := one_mul _
      have h4 : (Kc:ℝ) * (P.Nmax N X Y : ℝ) ≤ 2 * (N:ℝ) := by
        have hYN' : (Y:ℝ) ≤ (N:ℝ) := by exact_mod_cast hargs.2.2.2.2.2
        nlinarith [h1, h2, hYN']
      have h6 : 4 ≤ (P.BY N X Y : ℝ) + 1 := by
        have h7 : 4 ≤ (P.BY N X Y : ℝ) := by exact_mod_cast hBY4
        linarith
      calc (Kc:ℝ) * (P.Nmax N X Y : ℝ) / (N:ℝ) ≤ 2 * (N:ℝ) / (N:ℝ) :=
            div_le_div_of_nonneg_right h4 hNpos.le
        _ = 2 := by field_simp
        _ ≤ ((P.BY N X Y : ℝ) + 1) / 2 := by
            rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
            linarith
    have htail := hypergeom_tail N Kc (P.Nmax N X Y) (P.BY N X Y + 1) hN1 hKN
      (by push_cast; linarith [hmean]) (Nat.succ_pos _) I hIle
    have hbridge : prU (fun π : Equiv.Perm (Fin N) =>
          P.BY N X Y < (rowImage N (P.rows X Y) π j K).card)
        = (((powersetCard Kc (univ : Finset (Fin N))).filter
            (fun A => P.BY N X Y + 1 ≤ (A ∩ I).card)).card : ℝ)
          / ((powersetCard Kc (univ : Finset (Fin N))).card : ℝ) := by
      have h1 : ((fun π : Equiv.Perm (Fin N) =>
          P.BY N X Y < (rowImage N (P.rows X Y) π j K).card))
          = (fun π : Equiv.Perm (Fin N) =>
            P.BY N X Y + 1 ≤ (rowImage N (P.rows X Y) π j K).card) := by
        funext π; exact propext (Nat.lt_iff_add_one_le ..)
      rw [h1]
      have h2 : ((fun π : Equiv.Perm (Fin N) =>
          P.BY N X Y + 1 ≤ (rowImage N (P.rows X Y) π j K).card))
          = (fun π : Equiv.Perm (Fin N) =>
            P.BY N X Y + 1 ≤ ((((finSet K).image π).filter
              (fun q => q.val % (P.rows X Y) = j)).card)) := by
        funext π; rw [rowImage_card_eq]
      rw [h2]
      have hQ : ∀ A : Finset (Fin N),
          A.filter (fun q => q.val % (P.rows X Y) = j) = A ∩ I := by
        intro A
        ext q
        simp [hI]
      simp only [hQ]
      rw [prU_image_eq (finSet K) (fun A => P.BY N X Y + 1 ≤ (A ∩ I).card)]
      rw [show (finSet K).card = Kc from hKs.symm]
      rw [Finset.filter_congr_decidable (powersetCard Kc (univ : Finset (Fin N)))
        (fun A => P.BY N X Y + 1 ≤ (A ∩ I).card)]
    rw [hbridge]
    refine le_trans htail (Real.exp_le_exp.mpr ?_)
    push_cast
    set Tm : ℝ := (Kc:ℝ) * (P.Nmax N X Y : ℝ) / (N:ℝ) with hTm
    set T : ℝ := (P.BY N X Y : ℝ) + 1 with hT
    have hTpos : 0 < T := by rw [hT]; positivity
    have hT4 : 4 ≤ T := by
      rw [hT]
      have h7 : 4 ≤ (P.BY N X Y : ℝ) := by exact_mod_cast hBY4
      linarith
    have hTmle : Tm ≤ T / 2 := hmean
    have hkey : T / 8 ≤ (T - Tm)^2 / (2 * T) := by
      have hhalf : T / 2 ≤ T - Tm := by linarith
      have h2 : (0:ℝ) ≤ T / 2 := by linarith
      have hsq : (T/2) * (T/2) ≤ (T - Tm) * (T - Tm) := mul_self_le_mul_self h2 hhalf
      rw [le_div_iff₀ (by linarith : (0:ℝ) < 2 * T)]
      nlinarith [hsq]
    have h11 : ((P.C:ℝ) * lg (P.lgn + 2) + 5) / 8 ≤ (T - Tm)^2 / (2 * T) := by
      have h14 : (P.C:ℝ) * lg (P.lgn + 2) + 5 ≤ T := by
        rw [hT, hBYeq]
        have h13 := Nat.le_ceil ((P.C:ℝ) * lg (P.lgn + 2))
        push_cast
        linarith
      have h17 : ((P.C:ℝ) * lg (P.lgn + 2) + 5) / 8 ≤ T / 8 :=
        div_le_div_of_nonneg_right h14 (by norm_num)
      linarith
    calc -((T - Tm)^2 / (2 * T)) ≤ -(((P.C:ℝ) * lg (P.lgn + 2) + 5) / 8) := by linarith
      _ = -(((P.C:ℝ) * lg (P.lgn + 2) + 5) / 8) := rfl
/-! ### The assembly -/

/-- **Second claim of Lemma 5.3, as in the paper** ("For the last claim, fix a coordinate in
`J ∪ supp(x)` and condition on its row"): by linearity of expectation over the rows (`expU_sum'`),
each row contributes at most `N_max · (P[hint load > B_X] + P[outside load > B_Y])`; summing over the
`m` rows and using `m · N_max ≤ 2N` gives `2N · 2 · η² L^{-12}/4 = N η² L^{-12}`.  Since the node is
not in the `cheap` rule (`hnl`), `N ≤ D · log^{10} n`, so the extra `L^{-2}` leaves `D η²`.

*Forced deviation from the paper's phrasing (noted):* the paper "fixes a coordinate of `J ∪ supp(x)`
and conditions on its row"; here each row's whole mass is bounded by `N_max` times that row's
overload probability and the sum over rows is taken (`expU_sum'`).  This is coarser by a factor
`m·N_max/N ≤ 2` but avoids conditioning a uniform permutation on the row of a fixed coordinate; the
loss is paid for by the `log^{-12}` slack and by excluding the `cheap` rule via `hnl`, giving the
same `D η²` bound. -/
theorem claim2 (P : HintParams) (N X Y : ℕ) (hargs : P.NodeArgs N X Y) (hnl : P.NonLeaf N X Y)
    (hA : 1 ≤ P.A) (hC : 1000 * P.A + 1000 ≤ P.C) (x J : Finset ℕ)
    (hvalid : Node.Valid N X Y x J) :
    expU (fun π : Equiv.Perm (Fin N) => (P.overloadedMass N X Y π x J : ℝ)) ≤
      (HintParams.D N X Y : ℝ) * P.eta ^ 2 := by
  classical
  haveI : Nonempty (Equiv.Perm (Fin N)) := ⟨1⟩
  obtain ⟨hx, hJ, hJcard, hxcard⟩ := hvalid
  set m : ℕ := P.rows X Y with hm
  set W : ℕ := P.Nmax N X Y with hW
  have hm1 : 1 ≤ m := by rw [hm]; exact rows_pos P N X Y hargs hnl
  have hN1 : 1 ≤ N := hargs.2.2.1
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN1
  have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm1
  have hXN : X ≤ N := hargs.2.2.2.2.1
  have hYN : Y ≤ N := hargs.2.2.2.2.2
  have hlgn : 0 < P.lgn := by
    rw [HintParams.lgn, lg]
    exact Real.logb_pos (by norm_num) (by exact_mod_cast hargs.1)
  have hn2 : (2:ℝ) ≤ (P.n:ℝ) := by exact_mod_cast hargs.1
  have hlgn1 : 1 ≤ P.lgn := by
    rw [HintParams.lgn, lg, Real.le_logb_iff_rpow_le (by norm_num : (1:ℝ) < 2)
      (by linarith : (0:ℝ) < (P.n:ℝ))]
    simpa using hn2
  have hmN : m ≤ N := by
    rw [hm, HintParams.rows]
    apply max_le hYN
    rw [Nat.ceil_le]
    have h4 : (0:ℝ) < P.lgn ^ 3 := by linarith [one_le_cu_lgn P hlgn1]
    rw [div_le_iff₀ h4]
    have h5 : (X:ℝ) ≤ (N:ℝ) := by exact_mod_cast hXN
    have h6 : (1:ℝ) ≤ P.lgn ^ 3 := one_le_cu_lgn P hlgn1
    nlinarith
  have hWpos : 0 < W := by
    rw [hW, HintParams.Nmax]
    apply Nat.ceil_pos.mpr
    positivity
  have hWle : (W:ℝ) ≤ (N:ℝ) / (m:ℝ) + 1 := by
    have h1 : ((⌈(N:ℝ) / (P.rows X Y : ℝ)⌉₊ : ℕ) : ℝ) ≤ (N:ℝ) / (P.rows X Y : ℝ) + 1 :=
      ceil_le_add_one (by positivity)
    exact h1
  have hmW : (m:ℝ) * (W:ℝ) ≤ 2 * (N:ℝ) := by
    have h1 : (m:ℝ) * ((N:ℝ) / (m:ℝ)) = (N:ℝ) := by field_simp
    have h2 : (m:ℝ) * (W:ℝ) ≤ (m:ℝ) * ((N:ℝ) / (m:ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hWle hmpos.le
    have h3 : (m:ℝ) * ((N:ℝ) / (m:ℝ) + 1) = (N:ℝ) + (m:ℝ) := by rw [mul_add, h1, mul_one]
    have h4 : (m:ℝ) ≤ (N:ℝ) := by exact_mod_cast hmN
    linarith
  set b1 : ℝ := Real.exp (-((P.C:ℝ) * P.lgn / 32)) with hb1def
  set b2 : ℝ := Real.exp (-(((P.C:ℝ) * lg (P.lgn + 2) + 5) / 8)) with hb2def
  have hb1pos : 0 ≤ b1 := by rw [hb1def]; positivity
  have hb2pos : 0 ≤ b2 := by rw [hb2def]; positivity
  have hb1 : b1 ≤ P.eta ^ 2 * P.lgn ^ (-12:ℝ) / 4 := by
    rw [hb1def]; exact b1_le P hA hC hlgn1
  have hb2 : b2 ≤ P.eta ^ 2 * P.lgn ^ (-12:ℝ) / 4 := by
    rw [hb2def]; exact b2_le P hA hC hlgn1
  have hrowX : ∀ j : ℕ, prU (fun π : Equiv.Perm (Fin N) =>
      P.BX N X Y < (rowImage N m π j J).card) ≤ b1 := by
    intro j
    refine le_trans (row_prU_hint P N X Y hargs hnl hA hC J hJ hJcard j) ?_
    by_cases hc : P.BX N X Y = P.Nmax N X Y
    · rw [if_pos hc]
      simpa using hb1pos
    · rw [if_neg hc]
  have hrowY : ∀ j : ℕ, prU (fun π : Equiv.Perm (Fin N) =>
      P.BY N X Y < (rowImage N m π j (x \ J)).card) ≤ b2 := by
    intro j
    have hsub : x \ J ⊆ range N := fun a ha => hx (Finset.mem_sdiff.mp ha).1
    refine le_trans (row_prU_outside P N X Y hargs hnl (x \ J) hsub hxcard j) ?_
    by_cases hc : P.BY N X Y = P.Nmax N X Y
    · rw [if_pos hc]
      simpa using hb2pos
    · rw [if_neg hc]
  have hsum : expU (fun π : Equiv.Perm (Fin N) => (P.overloadedMass N X Y π x J : ℝ))
      = ∑ j ∈ range m, expU (fun π : Equiv.Perm (Fin N) =>
          if P.Overloaded N X Y (rowImage N m π j J) (rowImage N m π j x)
          then ((rowImage N m π j (J ∪ x)).card : ℝ) else 0) := by
    unfold HintParams.overloadedMass
    rw [← hm]
    push_cast
    exact expU_sum' _ _
  rw [hsum]
  have hrow : ∀ j ∈ range m, expU (fun π : Equiv.Perm (Fin N) =>
        (if P.Overloaded N X Y (rowImage N m π j J) (rowImage N m π j x)
         then ((rowImage N m π j (J ∪ x)).card : ℝ) else 0)) ≤ (W:ℝ) * (b1 + b2) := by
    intro j hj
    have hPt : ∀ π : Equiv.Perm (Fin N),
        (if P.Overloaded N X Y (rowImage N m π j J) (rowImage N m π j x)
         then ((rowImage N m π j (J ∪ x)).card : ℝ) else 0)
        ≤ (W:ℝ) * (if P.Overloaded N X Y (rowImage N m π j J) (rowImage N m π j x)
            then (1:ℝ) else 0) := by
      intro π
      by_cases h : P.Overloaded N X Y (rowImage N m π j J) (rowImage N m π j x)
      · rw [if_pos h, if_pos h, mul_one]
        have h1 : (rowImage N m π j (J ∪ x)).card ≤ W := by
          rw [hW]
          exact le_trans (rowImage_card_le_rowLen (N := N) (m := m) (j := j) π (J ∪ x))
            (rowLen_le_Nmax N m j hm1)
        exact_mod_cast h1
      · rw [if_neg h, if_neg h, mul_zero]
    have hOv : prU (fun π : Equiv.Perm (Fin N) =>
          P.Overloaded N X Y (rowImage N m π j J) (rowImage N m π j x))
        ≤ prU (fun π : Equiv.Perm (Fin N) => P.BX N X Y < (rowImage N m π j J).card)
          + prU (fun π : Equiv.Perm (Fin N) =>
              P.BY N X Y < (rowImage N m π j x \ rowImage N m π j J).card) := by
      refine le_trans (prU_mono' ?_) (prU_or_le' (fun π : Equiv.Perm (Fin N) =>
        P.BX N X Y < (rowImage N m π j J).card) (fun π : Equiv.Perm (Fin N) =>
        P.BY N X Y < (rowImage N m π j x \ rowImage N m π j J).card))
      intro π h
      simpa only [HintParams.Overloaded] using h
    have h2 : prU (fun π : Equiv.Perm (Fin N) =>
          P.BY N X Y < (rowImage N m π j x \ rowImage N m π j J).card)
        ≤ prU (fun π : Equiv.Perm (Fin N) =>
            P.BY N X Y < (rowImage N m π j (x \ J)).card) := by
      apply prU_mono'
      intro π h
      have h3 : (rowImage N m π j x \ rowImage N m π j J).card
          ≤ (rowImage N m π j (x \ J)).card :=
        Finset.card_le_card (rowImage_sdiff_subset π j x J)
      omega
    calc expU (fun π : Equiv.Perm (Fin N) =>
          (if P.Overloaded N X Y (rowImage N m π j J) (rowImage N m π j x)
           then ((rowImage N m π j (J ∪ x)).card : ℝ) else 0))
        ≤ expU (fun π : Equiv.Perm (Fin N) =>
            (W:ℝ) * (if P.Overloaded N X Y (rowImage N m π j J) (rowImage N m π j x)
              then (1:ℝ) else 0)) := expU_mono' hPt
      _ = (W:ℝ) * prU (fun π : Equiv.Perm (Fin N) =>
            P.Overloaded N X Y (rowImage N m π j J) (rowImage N m π j x)) := by
          rw [expU_const_mul', expU_indicator]
          ring
      _ ≤ (W:ℝ) * (b1 + b2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith [hOv, h2, hrowX j, hrowY j]
  calc ∑ j ∈ range m, expU (fun π : Equiv.Perm (Fin N) =>
        (if P.Overloaded N X Y (rowImage N m π j J) (rowImage N m π j x)
         then ((rowImage N m π j (J ∪ x)).card : ℝ) else 0))
      ≤ ∑ j ∈ range m, (W:ℝ) * (b1 + b2) := Finset.sum_le_sum hrow
    _ = (m:ℝ) * ((W:ℝ) * (b1 + b2)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = ((m:ℝ) * (W:ℝ)) * (b1 + b2) := by ring
    _ ≤ (2 * (N:ℝ)) * (b1 + b2) := by
        apply mul_le_mul_of_nonneg_right hmW
        linarith
    _ ≤ (2 * (N:ℝ)) * (P.eta ^ 2 * P.lgn ^ (-12:ℝ) / 4 + P.eta ^ 2 * P.lgn ^ (-12:ℝ) / 4) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
    _ = (N:ℝ) * (P.eta ^ 2 * P.lgn ^ (-12:ℝ)) := by ring
    _ ≤ (HintParams.D N X Y : ℝ) * P.eta ^ 2 := by
        have hcheap : ¬ ((HintParams.D N X Y : ℝ) ≤ (N:ℝ) / P.lgn ^ 10) := by
          intro h
          have h1 : P.rule N X Y = .cheap := by
            rw [HintParams.rule]
            exact if_pos h
          rcases hnl with hh | hh
          · rw [h1] at hh
            exact absurd hh (by decide)
          · rw [h1] at hh
            exact absurd hh (by decide)
        have hND : (N:ℝ) ≤ (HintParams.D N X Y : ℝ) * P.lgn ^ 10 := by
          have h1 : (N:ℝ) / P.lgn ^ 10 < (HintParams.D N X Y : ℝ) := not_le.mp hcheap
          have h2 : (0:ℝ) < P.lgn ^ 10 := by positivity
          rw [div_lt_iff₀ h2] at h1
          linarith
        have h2le : P.lgn ^ (-2:ℝ) ≤ 1 := by
          rw [Real.rpow_neg hlgn.le]
          rw [inv_le_one₀ (by positivity)]
          exact Real.one_le_rpow hlgn1 (by norm_num)
        have hreal : (N:ℝ) * P.lgn ^ (-12:ℝ) ≤ (HintParams.D N X Y : ℝ) * P.lgn ^ (-2:ℝ) := by
          have h1 : (N:ℝ) * P.lgn ^ (-12:ℝ)
              ≤ ((HintParams.D N X Y : ℝ) * P.lgn ^ 10) * P.lgn ^ (-12:ℝ) :=
            mul_le_mul_of_nonneg_right hND (by positivity)
          have h2 : ((HintParams.D N X Y : ℝ) * P.lgn ^ 10) * P.lgn ^ (-12:ℝ)
              = (HintParams.D N X Y : ℝ) * P.lgn ^ (-2:ℝ) := by
            have h3 : P.lgn ^ 10 * P.lgn ^ (-12:ℝ) = P.lgn ^ (-2:ℝ) := by
              rw [show P.lgn ^ 10 = P.lgn ^ (10:ℝ) by exact (Real.rpow_natCast P.lgn 10).symm]
              rw [← Real.rpow_add hlgn]
              congr 1
              norm_num
            calc ((HintParams.D N X Y : ℝ) * P.lgn ^ 10) * P.lgn ^ (-12:ℝ)
                = (HintParams.D N X Y : ℝ) * (P.lgn ^ 10 * P.lgn ^ (-12:ℝ)) := by ring
              _ = (HintParams.D N X Y : ℝ) * P.lgn ^ (-2:ℝ) := by rw [h3]
          linarith [h1, h2]
        have h6 : (0:ℝ) ≤ P.eta ^ 2 := by positivity
        calc (N:ℝ) * (P.eta ^ 2 * P.lgn ^ (-12:ℝ))
            = ((N:ℝ) * P.lgn ^ (-12:ℝ)) * P.eta ^ 2 := by ring
          _ ≤ ((HintParams.D N X Y : ℝ) * P.lgn ^ (-2:ℝ)) * P.eta ^ 2 :=
              mul_le_mul_of_nonneg_right hreal h6
          _ = (HintParams.D N X Y : ℝ) * (P.eta ^ 2 * P.lgn ^ (-2:ℝ)) := by ring
          _ ≤ (HintParams.D N X Y : ℝ) * (P.eta ^ 2 * 1) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              nlinarith [h2le, h6]
          _ = (HintParams.D N X Y : ℝ) * P.eta ^ 2 := by ring


/-! ## Seeds: the local seed is a product, and the one-coordinate marginal

A node's local seed is `Equiv.Perm (Fin N) × (Fin m → Rand)` — a public permutation and one coin set
per row — so the uniform law on it is the product of the two uniform laws (the "average of averages").
The second group of lemmas is the one-coordinate marginal used for the regular rows: averaging over
all coin vectors after looking at row `j` alone is the same as averaging over that row's coins. -/

/-- `expU` over a product seed is the average of averages. -/
lemma expU_prod'' {α β : Type} [Fintype α] [Fintype β] (f : α → β → ℝ) :
    expU (fun p : α × β => f p.1 p.2) = expU (fun a => expU (fun b => f a b)) := by
  have hmul : ((Fintype.card α : ℝ)) * ((Fintype.card β : ℝ))
      = ((Fintype.card β : ℝ)) * ((Fintype.card α : ℝ)) := mul_comm _ _
  have hL : expU (fun p : α × β => f p.1 p.2)
      = (∑ a : α, ∑ b : β, f a b) / ((Fintype.card α : ℝ) * (Fintype.card β : ℝ)) := by
    unfold expU
    rw [Fintype.sum_prod_type (fun p : α × β => f p.1 p.2), Fintype.card_prod]
    push_cast
    rfl
  have hR : expU (fun a => expU (fun b => f a b))
      = ((∑ a : α, ∑ b : β, f a b) / (Fintype.card β : ℝ)) / (Fintype.card α : ℝ) := by
    unfold expU
    rw [← Finset.sum_div]
  rw [hL, hR, div_div, hmul]

/-- The local seed form of `expU_prod''`. -/
lemma expU_localSeed' {N m : ℕ} {R : Type} [Fintype R]
    (f : Equiv.Perm (Fin N) × (Fin m → R) → ℝ) :
    expU f = expU (fun π => expU (fun g => f (π, g))) := by
  have h := expU_prod'' (α := Equiv.Perm (Fin N)) (β := Fin m → R) (fun π g => f (π, g))
  rw [show (fun p : Equiv.Perm (Fin N) × (Fin m → R) => f (p.1, p.2)) = f from rfl] at h
  exact h

/-- The local-seed form of `expU_prod''`, stated for the `LocalSeed` abbreviation itself (so that the
`Fintype` instance of the ambient goal is the one used). -/
lemma expU_localSeed_local (P : HintParams) (N X Y : ℕ) (f : (P.scheme N X Y).LocalSeed → ℝ) :
    expU f = expU (fun π : Equiv.Perm (Fin N) =>
      expU (fun g : Fin (P.rows X Y) → (P.scheme N X Y).Rand => f (π, g))) :=
  expU_localSeed' f

/-- `expU` of a constant. -/
lemma expU_const' {α : Type} [Fintype α] [Nonempty α] (c : ℝ) :
    expU (fun _ : α => c) = c := by
  unfold expU
  have hpos : (0:ℝ) < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [div_eq_iff hpos.ne']
  ring

/-- `expU` is additive. -/
lemma expU_add' {α : Type} [Fintype α] (f g : α → ℝ) :
    expU (fun a => f a + g a) = expU f + expU g := by
  unfold expU
  rw [Finset.sum_add_distrib, add_div]

/-- `expU` of an affine function of `f`. -/
lemma expU_affine' {α : Type} [Fintype α] [Nonempty α] (c d : ℝ) (f : α → ℝ) :
    expU (fun a => c * f a + d) = c * expU f + d := by
  rw [expU_add', expU_const_mul', expU_const']

/-- `expU` of an indicator, with the `Decidable` instance kept as an argument so that it can be used
whatever instance the ambient goal carries. -/
lemma expU_indicator'' {α : Type} [Fintype α] [Nonempty α] (Q : α → Prop) [DecidablePred Q]
    (c : ℝ) : expU (fun a => if Q a then c else 0) = c * prU Q := by
  have hsum : (∑ a : α, (if Q a then c else 0)) = ((Finset.univ.filter Q).card : ℝ) * c := by
    simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  unfold expU
  rw [hsum, prU_eq_card']
  set A : ℝ := ((Finset.univ.filter Q).card : ℝ) with hA
  set Nc : ℝ := (Fintype.card α : ℝ) with hNc
  ring

/-- `expU` of a finite sum, in the `Fin`-indexed form used below. -/
lemma expU_sum_fin' {α : Type} [Fintype α] {n : ℕ} (f : Fin n → α → ℝ) :
    expU (fun a => ∑ i : Fin n, f i a) = ∑ i : Fin n, expU (fun a => f i a) := by
  have h := expU_sum' (Finset.univ : Finset (Fin n)) f
  simpa using h

open Classical in
/-- The fibre of `f ↦ f j` over `b` in `Fin m → α` has cardinality `|α| ^ (m-1)`: such an `f` is the
same thing as an arbitrary function on the other `m-1` coordinates. -/
lemma card_eval_fiber' {m : ℕ} {α : Type} [Fintype α] (j : Fin m) (b : α) :
    (Finset.univ.filter (fun f : Fin m → α => f j = b)).card = Fintype.card α ^ (m - 1) := by
  classical
  haveI : Nonempty α := ⟨b⟩
  have hcard : Fintype.card {f : Fin m → α // f j = b} = Fintype.card α ^ (m - 1) := by
    have e : {f : Fin m → α // f j = b} ≃ ({i : Fin m // i ≠ j} → α) :=
      { toFun := fun f i => f.1 i.1
        invFun := fun g => ⟨fun i => if h : i = j then b else g ⟨i, h⟩, by simp⟩
        left_inv := by
          intro f
          refine Subtype.ext (funext fun i => ?_)
          by_cases h : i = j
          · subst h
            simp [f.2]
          · simp [h]
        right_inv := by
          intro g
          funext i
          simp [i.2] }
    rw [Fintype.card_congr e, Fintype.card_fun]
    have hsub : Fintype.card {i : Fin m // i ≠ j} = m - 1 := by
      have hset : (Finset.univ.filter (fun i : Fin m => i ≠ j))
          = (Finset.univ : Finset (Fin m)).erase j := by
        ext i
        simp [Finset.mem_erase, ne_comm]
      rw [Fintype.card_subtype, hset, Finset.card_erase_of_mem (Finset.mem_univ j),
        Finset.card_univ, Fintype.card_fin]
    rw [hsub]
  rw [← Fintype.card_subtype]
  exact hcard

/-- **One-coordinate marginal.** The uniform law on `Fin m → α`, pushed forward along `f ↦ f j`,
is the uniform law on `α` (the fibres of `f ↦ f j` are equinumerous). -/
lemma prU_pi_apply {m : ℕ} {α : Type} [Fintype α] [Nonempty α] (j : Fin m) (Q : α → Prop) :
    prU (fun f : Fin m → α => Q (f j)) = prU Q := by
  classical
  set R : ℕ := Fintype.card α with hRdef
  have hR1 : 1 ≤ R := Fintype.card_pos_iff.mpr ‹Nonempty α›
  have hRpos : (0:ℝ) < (R:ℝ) := by
    have h : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR1
    linarith
  have hfib : ∀ b : α, (Finset.univ.filter (fun f : Fin m → α => f j = b)).card = R ^ (m - 1) := by
    intro b
    rw [hRdef]
    exact card_eval_fiber' j b
  have hsplit : (Finset.univ.filter (fun f : Fin m → α => Q (f j))).card
      = (Finset.univ.filter Q).card * R ^ (m - 1) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun f : Fin m → α => f j)
      (s := Finset.univ.filter (fun f : Fin m → α => Q (f j)))
      (t := Finset.univ.filter Q) (by
        intro b hb
        simpa using hb)]
    have hterm : ∀ b ∈ Finset.univ.filter Q,
        ((Finset.univ.filter (fun f : Fin m → α => Q (f j))).filter (fun f => f j = b)).card
          = R ^ (m - 1) := by
      intro b hb
      have hQb : Q b := by simpa using hb
      have hset : (Finset.univ.filter (fun f : Fin m → α => Q (f j))).filter (fun f => f j = b)
          = Finset.univ.filter (fun f : Fin m → α => f j = b) := by
        ext f
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨-, h⟩
          exact h
        · intro h
          exact ⟨by rw [h]; exact hQb, h⟩
      rw [hset, hfib b]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul, mul_comm]
  have htot : Fintype.card (Fin m → α) = R ^ m := by
    rw [hRdef, Fintype.card_fun, Fintype.card_fin]
  have hm1 : 1 ≤ m := by have h := j.isLt; omega
  have hpow : R ^ m = R ^ (m - 1) * R := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega]
    rw [pow_succ]
  have hPpos : (0:ℝ) < (R:ℝ) ^ (m - 1) := by positivity
  have hPR : (0:ℝ) < (R:ℝ) ^ (m - 1) * R := by positivity
  unfold prU
  rw [hsplit, htot, hpow]
  push_cast
  rw [div_eq_div_iff hPR.ne' hRpos.ne']
  ring

lemma mem_assemble_iff' (N m : ℕ) (π : Equiv.Perm (Fin N)) (F : ℕ → Finset ℕ) (p : ℕ) :
    p ∈ assemble N m π F ↔
      ∃ i : Fin N, i.val = p ∧ (π i).val / m ∈ F ((π i).val % m) := by
  classical
  simp only [assemble, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun ⟨i, h1, h2⟩ => ⟨i, h2, h1⟩, fun ⟨i, h1, h2⟩ => ⟨i, h2, h1⟩⟩

/-! ## Row fibres: the positions of `[N]` split into the `m` rows -/

/-- The positions of `[N]` that fall in row `j`. -/
def rowFiber (N m j : ℕ) : Finset ℕ := (range N).filter (fun p => p % m = j)

lemma rowFiber_card (N m j : ℕ) : (rowFiber N m j).card = rowLen N m j := rfl

lemma rowFiber_subset (N m j : ℕ) : rowFiber N m j ⊆ range N := Finset.filter_subset _ _

/-- The local index of the `q`-th position of row `j`. -/
lemma pos_div (m j q : ℕ) (hj : j < m) : (m * q + j) / m = q := by
  rw [Nat.mul_add_div (by omega : 0 < m), Nat.div_eq_of_lt hj, Nat.add_zero]

lemma pos_mod (m j q : ℕ) (hj : j < m) : (m * q + j) % m = j := by
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj]

/-- A position of row `j` has local index below the row length. -/
lemma div_lt_rowLen {N m j p : ℕ} (hm : 1 ≤ m) (hj : j < m) (hpN : p < N) (hpj : p % m = j) :
    p / m < rowLen N m j := by
  classical
  have hA : (rowFiber N m j).filter (fun p' => p' ≤ p)
      = (range (p / m + 1)).image (fun t => m * t + j) := by
    ext p'
    simp only [rowFiber, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨⟨hp'N, hp'j⟩, hp'le⟩
      refine ⟨p' / m, ?_, ?_⟩
      · exact Nat.lt_succ_of_le (Nat.div_le_div_right hp'le)
      · rw [← hp'j]; exact Nat.div_add_mod p' m
    · rintro ⟨t, ht, rfl⟩
      have htle : t ≤ p / m := by omega
      have h1 : m * t ≤ m * (p / m) := Nat.mul_le_mul_left m htle
      have h3 : m * t + j ≤ p := by
        have h2 : m * (p / m) + j = p := by rw [← hpj]; exact Nat.div_add_mod p m
        omega
      refine ⟨⟨by omega, pos_mod m j t hj⟩, h3⟩
  have hcard : ((rowFiber N m j).filter (fun p' => p' ≤ p)).card = p / m + 1 := by
    rw [hA, Finset.card_image_of_injOn (s := range (p / m + 1)) (f := fun t => m * t + j)]
    · simp
    · intro a _ b _ hab
      simp only at hab
      have h1 : m * a = m * b := by omega
      exact Nat.mul_left_cancel (by omega) h1
  have hle := Finset.card_le_card (Finset.filter_subset (fun p' => p' ≤ p) (s := rowFiber N m j))
  rw [hcard, rowFiber_card] at hle
  omega

/-- Row `j` consists of the positions `m*q+j`. -/
lemma rowFiber_eq_image (N m j : ℕ) (hm : 1 ≤ m) (hj : j < m) :
    rowFiber N m j = (range (rowLen N m j)).image (fun q => m * q + j) := by
  classical
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro p hp
    obtain ⟨hpN, hpj⟩ := Finset.mem_filter.mp hp
    refine Finset.mem_image.mpr ⟨p / m, Finset.mem_range.mpr (div_lt_rowLen hm hj (Finset.mem_range.mp hpN) hpj), ?_⟩
    rw [← hpj]; exact Nat.div_add_mod p m
  · rw [Finset.card_image_of_injOn (s := range (rowLen N m j)) (f := fun q => m * q + j), Finset.card_range,
      rowFiber_card]
    intro a _ b _ hab
    simp only at hab
    have h1 : m * a = m * b := by omega
    exact Nat.mul_left_cancel (by omega) h1

lemma mem_rowFiber_iff (N m j q : ℕ) (hm : 1 ≤ m) (hj : j < m) :
    m * q + j ∈ rowFiber N m j ↔ q < rowLen N m j := by
  rw [rowFiber_eq_image N m j hm hj, Finset.mem_image]
  constructor
  · rintro ⟨q', hq', heq⟩
    have h1 : m * q' = m * q := by omega
    have h2 : q' = q := Nat.mul_left_cancel (by omega) h1
    rw [← h2]; exact Finset.mem_range.mp hq'
  · intro hq
    exact ⟨q, Finset.mem_range.mpr hq, rfl⟩

/-- Membership in the row-local image. -/
lemma mem_rowImage_iff (N m j : ℕ) (π : Equiv.Perm (Fin N)) (S : Finset ℕ) (p : ℕ) :
    p ∈ rowImage N m π j S ↔
      ∃ i : Fin N, i.val ∈ S ∧ (π i).val % m = j ∧ (π i).val / m = p := by
  classical
  simp only [rowImage, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, and_assoc]
/-- A coordinate is in `S` iff its position lies in the row-local image of `S`. -/
lemma mem_rowImage_apply (N m : ℕ) (π : Equiv.Perm (Fin N)) (S : Finset ℕ) (i : Fin N) :
    i.val ∈ S ↔ (π i).val / m ∈ rowImage N m π ((π i).val % m) S := by
  constructor
  · intro hi
    exact (mem_rowImage_iff N m ((π i).val % m) π S ((π i).val / m)).mpr ⟨i, hi, rfl, rfl⟩
  · intro hi
    obtain ⟨i', hi', hmod, hdiv⟩ := (mem_rowImage_iff N m ((π i).val % m) π S ((π i).val / m)).mp hi
    have hpos : π i' = π i := by
      have h1 : (π i').val = m * ((π i').val / m) + (π i').val % m := (Nat.div_add_mod (π i').val m).symm
      have h2 : (π i).val = m * ((π i).val / m) + (π i).val % m := (Nat.div_add_mod (π i).val m).symm
      rw [hmod, hdiv] at h1
      exact Fin.ext (by omega)
    have hii : i' = i := π.injective hpos
    rwa [hii] at hi'

/-- The row-local image lies in the row length. -/
lemma rowImage_subset_rowLen (N m j : ℕ) (hm : 1 ≤ m) (hj : j < m) (π : Equiv.Perm (Fin N))
    (S : Finset ℕ) : rowImage N m π j S ⊆ range (rowLen N m j) := by
  intro p hp
  obtain ⟨i, -, hmod, hdiv⟩ := (mem_rowImage_iff N m j π S p).mp hp
  rw [← hdiv]
  exact Finset.mem_range.mpr (div_lt_rowLen hm hj (π i).isLt hmod)

lemma rowImage_mono (N m j : ℕ) (π : Equiv.Perm (Fin N)) {S T : Finset ℕ} (h : S ⊆ T) :
    rowImage N m π j S ⊆ rowImage N m π j T := by
  intro p hp
  obtain ⟨i, hi, hmod, hdiv⟩ := (mem_rowImage_iff N m j π S p).mp hp
  exact (mem_rowImage_iff N m j π T p).mpr ⟨i, h hi, hmod, hdiv⟩

/-- A local index occurs in row `j` iff it is below the row length. -/
lemma exists_pos_iff (N m j p : ℕ) (hm : 1 ≤ m) (hj : j < m) (π : Equiv.Perm (Fin N)) :
    (∃ i : Fin N, (π i).val % m = j ∧ (π i).val / m = p) ↔ p < rowLen N m j := by
  constructor
  · rintro ⟨i, hmod, hdiv⟩
    rw [← hdiv]
    exact div_lt_rowLen hm hj (π i).isLt hmod
  · intro hp
    have hfib := (mem_rowFiber_iff N m j p hm hj).mpr hp
    obtain ⟨hN, hmod⟩ := Finset.mem_filter.mp hfib
    refine ⟨π.symm ⟨m * p + j, Finset.mem_range.mp hN⟩, ?_, ?_⟩
    · rw [Equiv.apply_symm_apply]; exact hmod
    · rw [Equiv.apply_symm_apply]; exact pos_div m j p hj

/-- Assembling and then restricting to a row is the same as restricting the estimate. -/
lemma rowImage_assemble (N m j : ℕ) (hm : 1 ≤ m) (hj : j < m) (π : Equiv.Perm (Fin N))
    (F : ℕ → Finset ℕ) :
    rowImage N m π j (assemble N m π F) = F j ∩ range (rowLen N m j) := by
  classical
  ext p
  rw [mem_rowImage_iff, Finset.mem_inter]
  constructor
  · rintro ⟨i, hi, hmod, hdiv⟩
    obtain ⟨i', hieq, hF⟩ := (mem_assemble_iff' N m π F i.val).mp hi
    have hii : i' = i := Fin.ext hieq
    rw [hii] at hF
    refine ⟨?_, ?_⟩
    · rw [hmod, hdiv] at hF
      exact hF
    · rw [← hdiv]
      exact Finset.mem_range.mpr (div_lt_rowLen hm hj (π i).isLt hmod)
  · rintro ⟨hpF, hpN⟩
    have hlt : p < rowLen N m j := Finset.mem_range.mp hpN
    obtain ⟨i, hmod, hdiv⟩ := (exists_pos_iff N m j p hm hj π).mpr hlt
    refine ⟨i, ?_, hmod, hdiv⟩
    refine (mem_assemble_iff' N m π F i.val).mpr ⟨i, rfl, ?_⟩
    rw [hmod, hdiv]
    exact hpF

/-- Counting the coordinates of one row: the positions of row `j` that land in the estimate. -/
lemma card_fiber_row (N m j : ℕ) (hm : 1 ≤ m) (hj : j < m) (π : Equiv.Perm (Fin N))
    (W : ℕ → Finset ℕ) (hW : W j ⊆ range (rowLen N m j)) :
    (((univ : Finset (Fin N)).filter (fun i => (π i).val / m ∈ W ((π i).val % m))).filter
        (fun i => (π i).val % m = j)).card = (W j).card := by
  classical
  have hset : (((univ : Finset (Fin N)).filter (fun i => (π i).val / m ∈ W ((π i).val % m))).filter
        (fun i => (π i).val % m = j))
      = (univ : Finset (Fin N)).filter (fun i => (π i).val % m = j ∧ (π i).val / m ∈ W j) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, by rw [← h2]; exact h1⟩
    · rintro ⟨h2, h1⟩
      exact ⟨by rw [h2]; exact h1, h2⟩
  rw [hset]
  refine Finset.card_bij (fun (i : Fin N) _ => (π i).val / m) ?_ ?_ ?_
  · intro i hi
    exact (Finset.mem_filter.mp hi).2.2
  · intro i1 hi1 i2 hi2 heq
    have h2 : (π i1).val % m = j := (Finset.mem_filter.mp hi1).2.1
    have h3 : (π i2).val % m = j := (Finset.mem_filter.mp hi2).2.1
    have e1 : (π i1).val = m * ((π i1).val / m) + (π i1).val % m := (Nat.div_add_mod (π i1).val m).symm
    have e2 : (π i2).val = m * ((π i2).val / m) + (π i2).val % m := (Nat.div_add_mod (π i2).val m).symm
    have hpos : π i1 = π i2 := Fin.ext (by rw [e1, e2, heq, h2, h3])
    exact π.injective hpos
  · intro q hq
    have hqlt : q < rowLen N m j := Finset.mem_range.mp (hW hq)
    obtain ⟨i, hmod, hdiv⟩ := (exists_pos_iff N m j q hm hj π).mpr hqlt
    refine ⟨i, ?_, hdiv⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmod, by rw [hdiv]; exact hq⟩

/-- The `m` row maps together are a bijection `[N] ≅ ⨆_j [rowLen j]`. -/
lemma card_symmDiff_eq_sum_rowImage (N m : ℕ) (hm : 1 ≤ m) (π : Equiv.Perm (Fin N))
    {S T : Finset ℕ} (hS : S ⊆ range N) (hT : T ⊆ range N) :
    (symmDiff S T).card =
      ∑ j ∈ range m, (symmDiff (rowImage N m π j S) (rowImage N m π j T)).card := by
  classical
  have hsub : symmDiff S T ⊆ range N := by
    intro p hp
    rw [Finset.mem_symmDiff] at hp
    exact hp.elim (fun h => hS h.1) (fun h => hT h.1)
  have h1 : (symmDiff S T).card
      = ((univ : Finset (Fin N)).filter (fun i => i.val ∈ symmDiff S T)).card := by
    refine (Finset.card_bij (fun (i : Fin N) _ => i.val) ?_ ?_ ?_).symm
    · intro i hi; exact (Finset.mem_filter.mp hi).2
    · intro i1 _ i2 _ heq; exact Fin.ext heq
    · intro p hp
      exact ⟨⟨p, Finset.mem_range.mp (hsub hp)⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩, rfl⟩
  have h2 : ((univ : Finset (Fin N)).filter (fun i => i.val ∈ symmDiff S T)).card
      = ((univ : Finset (Fin N)).filter
          (fun i => (π i).val / m ∈ symmDiff (rowImage N m π ((π i).val % m) S)
            (rowImage N m π ((π i).val % m) T))).card := by
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Finset.mem_symmDiff, Finset.mem_symmDiff,
      mem_rowImage_apply N m π S i, mem_rowImage_apply N m π T i]
  rw [h1, h2]
  set W : ℕ → Finset ℕ := fun j => symmDiff (rowImage N m π j S) (rowImage N m π j T) with hW
  rw [Finset.card_eq_sum_card_fiberwise (s := (univ : Finset (Fin N)).filter
      (fun i => (π i).val / m ∈ W ((π i).val % m))) (t := range m)
      (f := fun i => (π i).val % m) (fun i _ => Finset.mem_range.mpr (Nat.mod_lt _ (by omega)))]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hjlt : j < m := Finset.mem_range.mp hj
  have hWsub : W j ⊆ range (rowLen N m j) := by
    intro p hp
    rw [hW] at hp
    simp only at hp
    rw [Finset.mem_symmDiff] at hp
    exact hp.elim (fun h => rowImage_subset_rowLen N m j hm hjlt π S h.1)
      (fun h => rowImage_subset_rowLen N m j hm hjlt π T h.1)
  exact card_fiber_row N m j hm hjlt π W hWsub

/-! ## `Z` as the sum of the per-row errors -/

/-- The per-row error of `Z` in row `j`: the row-local symmetric difference of the true row support
and the row-local image of the assembled exact estimate. -/
noncomputable def rowErr (P : HintParams) (N X Y : ℕ) (lr : (P.scheme N X Y).LocalSeed) (x J : Finset ℕ)
    (j : ℕ) : ℕ :=
  (symmDiff (rowImage N (P.rows X Y) lr.1 j x)
    (rowImage N (P.rows X Y) lr.1 j ((P.scheme N X Y).exactEstimate lr x J))).card

/-- `Z` is the sum of the `m` per-row errors. -/
lemma Z_eq_sum_rows (P : HintParams) (N X Y : ℕ) (hm : 1 ≤ P.rows X Y) (x J : Finset ℕ)
    (hx : x ⊆ range N) (lr : (P.scheme N X Y).LocalSeed) :
    (P.scheme N X Y).Z lr x J = ∑ j : Fin (P.rows X Y), rowErr P N X Y lr x J j.val := by
  classical
  have hsub : (P.scheme N X Y).exactEstimate lr x J ⊆ range N := by
    intro p hp
    rw [RowScheme.exactEstimate, RowScheme.assembled] at hp
    obtain ⟨i, hieq, -⟩ := (mem_assemble_iff' N (P.rows X Y) lr.1 _ p).mp hp
    exact Finset.mem_range.mpr (by rw [← hieq]; exact i.isLt)
  have hmain : (P.scheme N X Y).Z lr x J
      = ∑ j ∈ range (P.rows X Y), rowErr P N X Y lr x J j := by
    rw [RowScheme.Z, card_symmDiff_eq_sum_rowImage N (P.rows X Y) hm lr.1 hx hsub]
    rfl
  rw [hmain]
  exact (Fin.sum_univ_eq_sum_range (fun j => rowErr P N X Y lr x J j) (P.rows X Y)).symm

/-- The row-local error, written with the final row estimate clipped to the row length. -/
lemma rowErr_eq_est (P : HintParams) (N X Y : ℕ) (hm : 1 ≤ P.rows X Y)
    (lr : (P.scheme N X Y).LocalSeed) (x J : Finset ℕ) (j : Fin (P.rows X Y)) :
    rowErr P N X Y lr x J j.val
      = (symmDiff (rowImage N (P.rows X Y) lr.1 j.val x)
          ((P.scheme N X Y).exactRowEst lr x J j ∩ range (rowLen N (P.rows X Y) j.val))).card := by
  have hjm : j.val < P.rows X Y := j.isLt
  have h1 : (P.scheme N X Y).exactEstimate lr x J
      = assemble N (P.rows X Y) lr.1 (fun p => if h : p < P.rows X Y then
          (P.scheme N X Y).exactRowEst lr x J ⟨p, h⟩ else ∅) := rfl
  rw [rowErr, h1]
  rw [rowImage_assemble N (P.rows X Y) j.val hm hjm lr.1 (fun p => if h : p < P.rows X Y then
    (P.scheme N X Y).exactRowEst lr x J ⟨p, h⟩ else ∅)]
  simp only [dif_pos hjm]
  rfl

/-! ## Per-row estimates -/

/-- The head of a singleton family of supports lies in it. -/
lemma head?_getD_mem {U : Finset (Finset ℕ)} (h : U.card = 1) :
    (U.toList.head?).getD ∅ ∈ U := by
  obtain ⟨C, hC⟩ := Finset.card_eq_one.mp h
  rw [hC, Finset.toList_singleton]
  simp

/-- In a regular row the final estimate has at most `B_X + B_Y` coordinates. -/
lemma card_exactRowEst_le (P : HintParams) (N X Y : ℕ) (hm : 1 ≤ P.rows X Y)
    (j : Fin (P.rows X Y)) (lr : (P.scheme N X Y).LocalSeed) (x J : Finset ℕ)
    (hnot : ¬ P.Overloaded N X Y ((P.scheme N X Y).rowOf lr J j) ((P.scheme N X Y).rowOf lr x j)) :
    ((P.scheme N X Y).exactRowEst lr x J j).card ≤ P.BX N X Y + P.BY N X Y := by
  classical
  have hb : ¬ P.BX N X Y < ((P.scheme N X Y).rowOf lr J j).card := fun h => hnot (Or.inl h)
  have hJl : ((P.scheme N X Y).rowOf lr J j).card ≤ P.BX N X Y := by omega
  have hest : (P.scheme N X Y).exactRowEst lr x J j
      = HintParams.workerFinal N (P.rows X Y) (P.ell N X Y) (P.Nmax N X Y) (P.BX N X Y) (P.BY N X Y) j
          (lr.2 j) ((P.scheme N X Y).rowOf lr J j)
          ((P.scheme N X Y).truePrefix j (lr.2 j) ((P.scheme N X Y).rowOf lr x j) (P.ell N X Y)) := rfl
  rw [hest]
  unfold HintParams.workerFinal
  rw [if_neg hb]
  dsimp only
  set U := (range (min (P.BY N X Y)
      (rowLen N (P.rows X Y) j.val - ((P.scheme N X Y).rowOf lr J j).card) + 1)).biUnion
      (fun r => HintParams.family (rowLen N (P.rows X Y) j.val) (lr.2 j)
        ((P.scheme N X Y).rowOf lr J j) r
        ((P.scheme N X Y).truePrefix j (lr.2 j) ((P.scheme N X Y).rowOf lr x j) (P.ell N X Y))) with hU
  split_ifs with h1
  · have hmem : (U.toList.head?).getD ∅ ∈ U := head?_getD_mem h1
    rw [hU] at hmem
    obtain ⟨r, hr, hCr⟩ := Finset.mem_biUnion.mp hmem
    have hrle : r ≤ P.BY N X Y := by
      have := Finset.mem_range.mp hr
      omega
    simp only [HintParams.family, Finset.mem_filter, Finset.mem_powerset] at hCr
    have hcardr : (U.toList.head?.getD ∅ \ (P.scheme N X Y).rowOf lr J j).card = r := hCr.2.1
    have hsub : U.toList.head?.getD ∅ ⊆ (P.scheme N X Y).rowOf lr J j ∪
        (U.toList.head?.getD ∅ \ (P.scheme N X Y).rowOf lr J j) := by
      intro a ha
      by_cases h : a ∈ (P.scheme N X Y).rowOf lr J j
      · exact Finset.mem_union.mpr (Or.inl h)
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨ha, h⟩))
    calc (U.toList.head?.getD ∅).card
        ≤ ((P.scheme N X Y).rowOf lr J j ∪
            (U.toList.head?.getD ∅ \ (P.scheme N X Y).rowOf lr J j)).card := Finset.card_le_card hsub
      _ ≤ ((P.scheme N X Y).rowOf lr J j).card +
            (U.toList.head?.getD ∅ \ (P.scheme N X Y).rowOf lr J j).card := Finset.card_union_le _ _
      _ = ((P.scheme N X Y).rowOf lr J j).card + r := by rw [hcardr]
      _ ≤ P.BX N X Y + P.BY N X Y := by omega
  · simp

/- **The sharp form of Lemma 5.3 (row recovery)**, imported from the finished Lemma 5.3 milestone as
`LinearSetReconciliation327.Main.row_final_sharp`: the final recovery of one regular row fails
with probability at most `2^{-⌈log(16/η²)⌉}/1024`.

This is the paper's inequality *before* the `η²/8` simplification of `claim1`; the extra factor
`2^{-10}` (equivalently `η²/16384` instead of `η²/8`) is what Lemma 5.4's expectation bound uses, so
that only `η·K ≲ 1` — not `η·K ≲ 1/8` — is needed of the row size `K = B_X + B_Y`; see the note at
`expU_Z_le`.  The sharp form is *not* re-proved here. -/

/-! ## Basic bounds on `Z` and on the parameter `K = B_X + B_Y` -/

/-- `Z ≤ N`: both `x` and the assembled estimate lie in `[N]`. -/
lemma Z_le_N (P : HintParams) (N X Y : ℕ) (x J : Finset ℕ) (hx : x ⊆ range N)
    (lr : (P.scheme N X Y).LocalSeed) : (P.scheme N X Y).Z lr x J ≤ N := by
  classical
  have hsub : (P.scheme N X Y).exactEstimate lr x J ⊆ range N := by
    intro p hp
    rw [RowScheme.exactEstimate, RowScheme.assembled] at hp
    obtain ⟨i, hieq, -⟩ := (mem_assemble_iff' N (P.rows X Y) lr.1 _ p).mp hp
    exact Finset.mem_range.mpr (by rw [← hieq]; exact i.isLt)
  have h1 : (symmDiff x ((P.scheme N X Y).exactEstimate lr x J)).card ≤ N := by
    have h2 : symmDiff x ((P.scheme N X Y).exactEstimate lr x J)
        ⊆ x ∪ ((P.scheme N X Y).exactEstimate lr x J) := by
      intro a ha
      rw [symmDiff_def, Finset.sup_eq_union, Finset.mem_union, Finset.mem_sdiff,
        Finset.mem_sdiff] at ha
      rcases ha with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact Finset.mem_union.mpr (Or.inl h1)
      · exact Finset.mem_union.mpr (Or.inr h1)
    calc (symmDiff x ((P.scheme N X Y).exactEstimate lr x J)).card
        ≤ (range N).card :=
          Finset.card_le_card (Finset.Subset.trans h2 (Finset.union_subset hx hsub))
      _ = N := Finset.card_range N
  calc (P.scheme N X Y).Z lr x J
      = (symmDiff x ((P.scheme N X Y).exactEstimate lr x J)).card := rfl
    _ ≤ N := h1

/-- `2^{-⌈log(16/ε)⌉}/1024 ≤ ε/16384`; the sharp row bound divided by `1024` is at most `η²/16384`.
This is `inv_two_pow_ceil_le` with the exact constant that Lemma 5.4 needs. -/
lemma inv_two_pow_ceil_le_div (ε : ℝ) (hε : 0 < ε) :
    ((2:ℝ)^((⌈lg (16/ε)⌉₊ : ℕ) : ℝ))⁻¹ / 1024 ≤ ε / 16384 := by
  set t : ℕ := ⌈lg (16/ε)⌉₊ with ht
  have hpos : (0:ℝ) < 16/ε := by positivity
  have hlog : lg (16/ε) ≤ ((t:ℕ):ℝ) := by
    rw [ht]; exact Nat.le_ceil _
  have hlogb : (2:ℝ) ^ lg (16/ε) = 16/ε :=
    Real.rpow_logb (b := 2) (by norm_num) (by norm_num) hpos
  have hpow : (16:ℝ)/ε ≤ (2:ℝ)^((t:ℝ)) := by
    calc (16:ℝ)/ε = (2:ℝ)^(lg (16/ε)) := hlogb.symm
      _ ≤ (2:ℝ)^((t:ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hlog
  have hinv : ((2:ℝ)^((t:ℝ)))⁻¹ ≤ ε/16 := by
    have h1 : ((2:ℝ)^((t:ℝ)))⁻¹ ≤ ((16:ℝ)/ε)⁻¹ :=
      (inv_le_inv₀ (by positivity) hpos).mpr hpow
    have h2' : ((16:ℝ)/ε)⁻¹ = ε/16 := by field_simp
    rwa [h2'] at h1
  calc ((2:ℝ)^((t:ℝ)))⁻¹ / 1024 ≤ (ε/16)/1024 :=
        div_le_div_of_nonneg_right hinv (by norm_num)
    _ = ε/16384 := by ring

/-- `1/2 ≤ log 2`. -/
lemma log_two_ge_half : (1/2:ℝ) ≤ Real.log 2 := by
  have h := Real.log_two_gt_d9
  linarith

/-- `log₂(L+2) ≤ 6L` for `L ≥ 1`. -/
lemma lg_add_two_le (L : ℝ) (hL : 1 ≤ L) : lg (L + 2) ≤ 6 * L := by
  have hln2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hln2g : (1/2:ℝ) ≤ Real.log 2 := log_two_ge_half
  have h20 : (0:ℝ) < L + 2 := by linarith
  rw [lg, Real.logb, div_le_iff₀ hln2]
  have hlog : Real.log (L + 2) ≤ L + 1 := by
    have h := Real.log_le_sub_one_of_pos h20
    linarith
  have hml2 : L * (1/2:ℝ) ≤ L * Real.log 2 :=
    mul_le_mul_of_nonneg_left hln2g (by linarith)
  nlinarith

/-- `B_X + B_Y ≤ 16 C log³ n`: the paper's `K = B_X + B_Y = O(C log³ n)`. -/
lemma K_le_C (P : HintParams) (N X Y : ℕ) (hC1 : 1 ≤ P.C) (hL : 1 ≤ P.lgn) :
    ((P.BX N X Y + P.BY N X Y : ℕ) : ℝ) ≤ 16 * (P.C : ℝ) * P.lgn ^ 3 := by
  have hC0 : (1:ℝ) ≤ (P.C : ℝ) := by exact_mod_cast hC1
  have hLpos : 0 < P.lgn := by linarith
  have hbx : ((P.BX N X Y : ℕ) : ℝ) ≤ P.lgn^3 + (P.C:ℝ)*P.lgn^2 + 1 := by
    have h1 : ((P.BX N X Y : ℕ) : ℝ) ≤ ((⌈P.lgn ^ 3 + (P.C : ℝ) * P.lgn ^ 2⌉₊ : ℕ) : ℝ) := by
      rw [HintParams.BX]
      exact_mod_cast min_le_right (P.Nmax N X Y) _
    refine le_trans h1 ?_
    exact ceil_le_add_one (by positivity)
  have hby : ((P.BY N X Y : ℕ) : ℝ) ≤ 6 * (P.C:ℝ) * P.lgn + 5 := by
    have h1 : ((P.BY N X Y : ℕ) : ℝ)
        ≤ ((⌈(P.C : ℝ) * lg (P.lgn + 2)⌉₊ + 4 : ℕ) : ℝ) := by
      rw [HintParams.BY]
      exact_mod_cast min_le_right (P.Nmax N X Y) _
    have h2 : ((⌈(P.C : ℝ) * lg (P.lgn + 2)⌉₊ : ℕ) : ℝ) ≤ (P.C:ℝ) * lg (P.lgn+2) + 1 := by
      apply ceil_le_add_one
      have hlt : (0:ℝ) ≤ lg (P.lgn + 2) :=
        Real.logb_nonneg (by norm_num : (1:ℝ) < 2) (by linarith)
      positivity
    have h3 : lg (P.lgn + 2) ≤ 6 * P.lgn := lg_add_two_le P.lgn hL
    have h4 : (0:ℝ) ≤ (P.C:ℝ) := by linarith
    push_cast at h1 ⊢
    nlinarith
  have hL3 : (1:ℝ) ≤ P.lgn^3 := one_le_cu_lgn P hL
  have hsq : (1:ℝ) ≤ P.lgn^2 := one_le_sq_lgn P hL
  have hL2le3 : P.lgn^2 ≤ P.lgn^3 := by
    have h2 : (0:ℝ) < P.lgn^2 := by positivity
    calc P.lgn^2 = P.lgn^2 * 1 := by ring
      _ ≤ P.lgn^2 * P.lgn := mul_le_mul_of_nonneg_left hL h2.le
      _ = P.lgn^3 := by ring
  have hLle3 : P.lgn ≤ P.lgn^3 := by
    calc P.lgn = P.lgn * 1 := by ring
      _ ≤ P.lgn * P.lgn^2 := mul_le_mul_of_nonneg_left hsq (by linarith)
      _ = P.lgn^3 := by ring
  have e1 : P.lgn^3 ≤ (P.C:ℝ) * P.lgn^3 := by
    calc P.lgn^3 = 1 * P.lgn^3 := by ring
      _ ≤ (P.C:ℝ) * P.lgn^3 := mul_le_mul_of_nonneg_right hC0 (by positivity)
  have e2 : (P.C:ℝ) * P.lgn^2 ≤ (P.C:ℝ) * P.lgn^3 :=
    mul_le_mul_of_nonneg_left hL2le3 (by linarith)
  have e3 : (P.C:ℝ) * P.lgn ≤ (P.C:ℝ) * P.lgn^3 :=
    mul_le_mul_of_nonneg_left hLle3 (by linarith)
  have h6 : (1:ℝ) ≤ (P.C:ℝ) * P.lgn^3 := by
    calc (1:ℝ) = 1*1 := by ring
      _ ≤ (P.C:ℝ) * P.lgn^3 := mul_le_mul hC0 hL3 (by norm_num) (by linarith)
  have hsum : ((P.BX N X Y + P.BY N X Y : ℕ) : ℝ)
      = ((P.BX N X Y : ℕ) : ℝ) + ((P.BY N X Y : ℕ) : ℝ) := by push_cast; ring
  rw [hsum]
  calc ((P.BX N X Y : ℕ) : ℝ) + ((P.BY N X Y : ℕ) : ℝ)
      ≤ (P.lgn^3 + (P.C:ℝ)*P.lgn^2 + 1) + (6*(P.C:ℝ)*P.lgn + 5) := by linarith
    _ ≤ ((P.C:ℝ)*P.lgn^3 + (P.C:ℝ)*P.lgn^3 + 1) + (6*((P.C:ℝ)*P.lgn^3) + 5) := by
        linarith [e1, e2, e3]
    _ = 8 * ((P.C:ℝ)*P.lgn^3) + 6 := by ring
    _ ≤ 16 * (P.C:ℝ) * P.lgn^3 := by nlinarith [h6]

/-- The final row estimate has at most `K = B_X + B_Y` coordinates, with *no* hypothesis on the row
(the decoder abstains, i.e. outputs `∅`, when `|J_j| > B_X`). -/
lemma card_exactRowEst_le_of_not_big (P : HintParams) (N X Y : ℕ) (hm : 1 ≤ P.rows X Y)
    (j : Fin (P.rows X Y)) (lr : (P.scheme N X Y).LocalSeed) (x J : Finset ℕ)
    (hb : ¬ P.BX N X Y < ((P.scheme N X Y).rowOf lr J j).card) :
    ((P.scheme N X Y).exactRowEst lr x J j).card ≤ P.BX N X Y + P.BY N X Y := by
  classical
  have hest : (P.scheme N X Y).exactRowEst lr x J j
      = HintParams.workerFinal N (P.rows X Y) (P.ell N X Y) (P.Nmax N X Y) (P.BX N X Y) (P.BY N X Y) j
          (lr.2 j) ((P.scheme N X Y).rowOf lr J j)
          ((P.scheme N X Y).truePrefix j (lr.2 j) ((P.scheme N X Y).rowOf lr x j) (P.ell N X Y)) := rfl
  rw [hest]
  unfold HintParams.workerFinal
  rw [if_neg hb]
  dsimp only
  set U := (range (min (P.BY N X Y)
      (rowLen N (P.rows X Y) j.val - ((P.scheme N X Y).rowOf lr J j).card) + 1)).biUnion
      (fun r => HintParams.family (rowLen N (P.rows X Y) j.val) (lr.2 j)
        ((P.scheme N X Y).rowOf lr J j) r
        ((P.scheme N X Y).truePrefix j (lr.2 j) ((P.scheme N X Y).rowOf lr x j) (P.ell N X Y))) with hU
  split_ifs with h1
  · have hmem : (U.toList.head?).getD ∅ ∈ U := head?_getD_mem h1
    rw [hU] at hmem
    obtain ⟨r, hr, hCr⟩ := Finset.mem_biUnion.mp hmem
    have hrle : r ≤ P.BY N X Y := by
      have := Finset.mem_range.mp hr
      omega
    simp only [HintParams.family, Finset.mem_filter, Finset.mem_powerset] at hCr
    have hcardr : (U.toList.head?.getD ∅ \ (P.scheme N X Y).rowOf lr J j).card = r := hCr.2.1
    have hsub : U.toList.head?.getD ∅ ⊆ (P.scheme N X Y).rowOf lr J j ∪
        (U.toList.head?.getD ∅ \ (P.scheme N X Y).rowOf lr J j) := by
      intro a ha
      by_cases h : a ∈ (P.scheme N X Y).rowOf lr J j
      · exact Finset.mem_union.mpr (Or.inl h)
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨ha, h⟩))
    calc (U.toList.head?.getD ∅).card
        ≤ ((P.scheme N X Y).rowOf lr J j ∪
            (U.toList.head?.getD ∅ \ (P.scheme N X Y).rowOf lr J j)).card := Finset.card_le_card hsub
      _ ≤ ((P.scheme N X Y).rowOf lr J j).card +
            (U.toList.head?.getD ∅ \ (P.scheme N X Y).rowOf lr J j).card := Finset.card_union_le _ _
      _ = ((P.scheme N X Y).rowOf lr J j).card + r := by rw [hcardr]
      _ ≤ P.BX N X Y + P.BY N X Y := by omega
  · simp

/-- The general form: `|Ŝ_j| ≤ K` for *every* row. -/
lemma card_exactRowEst_le_any (P : HintParams) (N X Y : ℕ) (hm : 1 ≤ P.rows X Y)
    (j : Fin (P.rows X Y)) (lr : (P.scheme N X Y).LocalSeed) (x J : Finset ℕ) :
    ((P.scheme N X Y).exactRowEst lr x J j).card ≤ P.BX N X Y + P.BY N X Y := by
  classical
  by_cases hb : P.BX N X Y < ((P.scheme N X Y).rowOf lr J j).card
  · have h0 : ((P.scheme N X Y).exactRowEst lr x J j).card = 0 := by
      have hest : (P.scheme N X Y).exactRowEst lr x J j
          = HintParams.workerFinal N (P.rows X Y) (P.ell N X Y) (P.Nmax N X Y)
              (P.BX N X Y) (P.BY N X Y) j (lr.2 j) ((P.scheme N X Y).rowOf lr J j)
              ((P.scheme N X Y).truePrefix j (lr.2 j) ((P.scheme N X Y).rowOf lr x j)
                (P.ell N X Y)) := rfl
      rw [hest]
      unfold HintParams.workerFinal
      rw [if_pos hb]
      simp
    rw [h0]
    exact Nat.zero_le _
  · exact card_exactRowEst_le_of_not_big P N X Y hm j lr x J hb

/-! ## Numeric facts about the parameters at a non-leaf node -/

lemma lgn_pos_args (P : HintParams) (N X Y : ℕ) (hargs : P.NodeArgs N X Y) : 0 < P.lgn := by
  have hn2 : (2:ℝ) ≤ (P.n:ℝ) := by exact_mod_cast hargs.1
  rw [HintParams.lgn, lg]
  exact Real.logb_pos (by norm_num) (by linarith)

lemma one_le_lgn_args (P : HintParams) (N X Y : ℕ) (hargs : P.NodeArgs N X Y) : 1 ≤ P.lgn := by
  have hn2 : (2:ℝ) ≤ (P.n:ℝ) := by exact_mod_cast hargs.1
  rw [HintParams.lgn, lg,
    Real.le_logb_iff_rpow_le (by norm_num : (1:ℝ) < 2) (by linarith : (0:ℝ) < (P.n:ℝ))]
  simpa using hn2

/-- `m ≤ D`: the number of rows never exceeds the hint + slack capacity. -/
lemma rows_le_D (P : HintParams) (N X Y : ℕ) (hargs : P.NodeArgs N X Y) :
    P.rows X Y ≤ HintParams.D N X Y := by
  have hn2 : (2:ℝ) ≤ (P.n:ℝ) := by exact_mod_cast hargs.1
  have hlgn1 : 1 ≤ P.lgn := one_le_lgn_args P N X Y hargs
  have hL3 : (1:ℝ) ≤ P.lgn ^ 3 := one_le_cu_lgn P hlgn1
  have hL3pos : (0:ℝ) < P.lgn ^ 3 := by linarith
  have hXN : X ≤ N := hargs.2.2.2.2.1
  have hYN : Y ≤ N := hargs.2.2.2.2.2
  have hX : (X:ℝ) ≤ (N:ℝ) := by exact_mod_cast hXN
  rw [HintParams.D]
  apply le_min
  · rw [HintParams.rows]
    apply max_le hYN
    rw [Nat.ceil_le]
    rw [div_le_iff₀ hL3pos]
    nlinarith
  · rw [HintParams.rows]
    apply max_le (by omega)
    rw [Nat.ceil_le]
    have hX' : (X:ℝ) ≤ (X:ℝ) + (Y:ℝ) := by
      have h0 : (0:ℝ) ≤ (Y:ℝ) := by positivity
      linarith
    have h1 : (X:ℝ) / P.lgn ^ 3 ≤ (X:ℝ) := by
      rw [div_le_iff₀ hL3pos]
      nlinarith
    have h2 : ((X + Y : ℕ) : ℝ) = (X:ℝ) + (Y:ℝ) := by push_cast; ring
    rw [h2]
    linarith

/-- `K = B_X + B_Y = O(log¹³ n)` at a non-cheap node: since `D ≤ X + Y` and `N < D log¹⁰ n` there, the
row count `m` satisfies `N/m ≲ log¹³ n`, and `K ≤ 2 N_max ≤ 2⌈N/m⌉`.  This is the paper's
`K = B_X + B_Y ≤ 2N_max = O(log¹³ n)`. -/
lemma K_le_log13 (P : HintParams) (N X Y : ℕ) (hargs : P.NodeArgs N X Y) (hnl : P.NonLeaf N X Y)
    (hL : (10/7:ℝ) ≤ P.lgn) :
    ((P.BX N X Y + P.BY N X Y : ℕ) : ℝ) ≤ 4 * P.lgn ^ 13 + 2 := by
  have hL1 : (1:ℝ) ≤ P.lgn := by linarith
  have hLpos : 0 < P.lgn := by linarith
  have hL3pos : (0:ℝ) < P.lgn ^ 3 := by positivity
  have hLe3 : (1:ℝ) ≤ P.lgn ^ 3 := one_le_cu_lgn P hL1
  have hm1 : 1 ≤ P.rows X Y := rows_pos P N X Y hargs hnl
  have hmpos : (0:ℝ) < (P.rows X Y : ℝ) := by exact_mod_cast hm1
  -- the node is not `cheap`: `N ≤ D log¹⁰ n`
  have hcheap : ¬ ((HintParams.D N X Y : ℝ) ≤ (N:ℝ) / P.lgn ^ 10) := by
    intro h
    have h1 : P.rule N X Y = .cheap := by rw [HintParams.rule]; exact if_pos h
    rcases hnl with hh | hh <;> (rw [h1] at hh <;> exact absurd hh (by decide))
  have hND : (N:ℝ) ≤ (HintParams.D N X Y : ℝ) * P.lgn ^ 10 := by
    have h1 : (N:ℝ) / P.lgn ^ 10 < (HintParams.D N X Y : ℝ) := not_le.mp hcheap
    have h2 : (0:ℝ) < P.lgn ^ 10 := by positivity
    rw [div_lt_iff₀ h2] at h1
    linarith
  -- `X ≤ m log³ n` and `Y ≤ m`
  have hX : (X:ℝ) ≤ (P.rows X Y : ℝ) * P.lgn ^ 3 := by
    have h3 : ((⌈(X:ℝ) / P.lgn ^ 3⌉₊ : ℕ) : ℝ) ≤ (P.rows X Y : ℝ) := by
      have h4 : ⌈(X:ℝ) / P.lgn ^ 3⌉₊ ≤ P.rows X Y := by
        rw [HintParams.rows]
        exact le_max_right _ _
      exact_mod_cast h4
    have h5 : (X:ℝ) / P.lgn ^ 3 ≤ ((⌈(X:ℝ) / P.lgn ^ 3⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h6 : (X:ℝ) / P.lgn ^ 3 ≤ (P.rows X Y : ℝ) := le_trans h5 h3
    rw [div_le_iff₀ hL3pos] at h6
    exact h6
  have hY : (Y:ℝ) ≤ (P.rows X Y : ℝ) := by
    have h3 : Y ≤ P.rows X Y := by rw [HintParams.rows]; exact le_max_left _ _
    exact_mod_cast h3
  have hDXY : (HintParams.D N X Y : ℝ) ≤ (X:ℝ) + (Y:ℝ) := by
    have h3 : HintParams.D N X Y ≤ X + Y := by
      rw [HintParams.D]
      exact min_le_right _ _
    have h4 : ((HintParams.D N X Y : ℕ) : ℝ) ≤ ((X + Y : ℕ) : ℝ) := by exact_mod_cast h3
    push_cast at h4
    exact h4
  -- hence `N ≤ 2 m log¹³ n`
  have hNm : (N:ℝ) ≤ 2 * (P.rows X Y : ℝ) * P.lgn ^ 13 := by
    have hmle : (P.rows X Y : ℝ) ≤ (P.rows X Y : ℝ) * P.lgn ^ 3 := by
      calc (P.rows X Y : ℝ) = (P.rows X Y : ℝ) * 1 := by ring
        _ ≤ (P.rows X Y : ℝ) * P.lgn ^ 3 := mul_le_mul_of_nonneg_left hLe3 (by positivity)
    have hXY : (X:ℝ) + (Y:ℝ) ≤ 2 * (P.rows X Y : ℝ) * P.lgn ^ 3 := by linarith
    have hL13 : P.lgn ^ 3 * P.lgn ^ 10 = P.lgn ^ 13 := by rw [← pow_add]
    calc (N:ℝ) ≤ (HintParams.D N X Y : ℝ) * P.lgn ^ 10 := hND
      _ ≤ ((X:ℝ) + (Y:ℝ)) * P.lgn ^ 10 := mul_le_mul_of_nonneg_right hDXY (by positivity)
      _ ≤ (2 * (P.rows X Y : ℝ) * P.lgn ^ 3) * P.lgn ^ 10 :=
          mul_le_mul_of_nonneg_right hXY (by positivity)
      _ = 2 * (P.rows X Y : ℝ) * P.lgn ^ 13 := by
          have h13 : P.lgn ^ 13 = P.lgn ^ 3 * P.lgn ^ 10 := by rw [← pow_add]
          rw [h13]
          ring
  have hNmax : ((P.Nmax N X Y : ℕ) : ℝ) ≤ 2 * P.lgn ^ 13 + 1 := by
    have h1 : ((⌈(N:ℝ) / (P.rows X Y : ℝ)⌉₊ : ℕ) : ℝ) ≤ (N:ℝ) / (P.rows X Y : ℝ) + 1 :=
      ceil_le_add_one (by positivity)
    have h2 : (N:ℝ) / (P.rows X Y : ℝ) ≤ 2 * P.lgn ^ 13 := by
      rw [div_le_iff₀ hmpos]
      linarith
    rw [HintParams.Nmax]
    linarith
  have hK2 : ((P.BX N X Y + P.BY N X Y : ℕ) : ℝ) ≤ 2 * ((P.Nmax N X Y : ℕ) : ℝ) := by
    have h1 : P.BX N X Y ≤ P.Nmax N X Y := min_le_left _ _
    have h2 : P.BY N X Y ≤ P.Nmax N X Y := min_le_left _ _
    have h1' : ((P.BX N X Y : ℕ) : ℝ) ≤ ((P.Nmax N X Y : ℕ) : ℝ) := by exact_mod_cast h1
    have h2' : ((P.BY N X Y : ℕ) : ℝ) ≤ ((P.Nmax N X Y : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast
    linarith
  linarith [hK2, hNmax]

/-- The paper's `η·K ≲ 1`, in the form needed at the end: `η·(K + 1 + K/8192) ≤ 1`.  This is where
`A ≥ 20` (so `η = log^{-A} n ≤ log^{-20} n`) and the `log¹³` bound on `K` are used. -/
lemma eta_mul_K_bound (P : HintParams) (N X Y : ℕ) (hargs : P.NodeArgs N X Y)
    (hnl : P.NonLeaf N X Y) (hA : 20 ≤ P.A) (hL : (10/7:ℝ) ≤ P.lgn) :
    P.eta * ((((P.BX N X Y + P.BY N X Y : ℕ) : ℝ) + 1)
      + ((P.BX N X Y + P.BY N X Y : ℕ) : ℝ) / 8192) ≤ 1 := by
  set K : ℝ := ((P.BX N X Y + P.BY N X Y : ℕ) : ℝ) with hK
  have hL1 : (1:ℝ) ≤ P.lgn := by linarith
  have hLpos : 0 < P.lgn := by linarith
  have hKb : K ≤ 4 * P.lgn ^ 13 + 2 := K_le_log13 P N X Y hargs hnl hL
  have h13 : (1:ℝ) ≤ P.lgn ^ 13 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hL1 13
    simpa using h
  have h13b : (3:ℝ) ≤ P.lgn ^ 13 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 10/7) hL 13
    have h3 : (3:ℝ) ≤ ((10/7:ℝ)) ^ 13 := by norm_num
    linarith
  have hK0 : (0:ℝ) ≤ K := by rw [hK]; positivity
  -- `K + 1 + K/8192 ≤ 6 log¹³ n`
  have hKdiv : K / 8192 ≤ P.lgn ^ 13 := by
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 8192)]
    nlinarith [hKb, h13]
  have hsum6 : K + 1 + K / 8192 ≤ 6 * P.lgn ^ 13 := by linarith
  -- `6 log¹³ n ≤ log²⁰ n`, and `η ≤ log^{-20} n`
  have hpow20 : P.lgn ^ 20 = P.lgn ^ 13 * P.lgn ^ 7 := by rw [← pow_add]
  have hL7 : (6:ℝ) ≤ P.lgn ^ 7 := by
    have h7le : ((10/7:ℝ)) ^ 7 ≤ P.lgn ^ 7 := pow_le_pow_left₀ (by norm_num) hL 7
    have h6 : (6:ℝ) ≤ ((10/7:ℝ)) ^ 7 := by norm_num
    linarith
  have h6L : 6 * P.lgn ^ 13 ≤ P.lgn ^ 20 := by
    rw [hpow20]
    calc 6 * P.lgn ^ 13 = P.lgn ^ 13 * 6 := by ring
      _ ≤ P.lgn ^ 13 * P.lgn ^ 7 := mul_le_mul_of_nonneg_left hL7 (by positivity)
  have h20pos : (0:ℝ) < P.lgn ^ 20 := by positivity
  have hstep : (K + 1 + K / 8192) * (P.lgn ^ 20)⁻¹ ≤ 1 := by
    calc (K + 1 + K / 8192) * (P.lgn ^ 20)⁻¹ ≤ P.lgn ^ 20 * (P.lgn ^ 20)⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          linarith
      _ = 1 := by rw [mul_inv_cancel₀ h20pos.ne']
  -- `η = log^{-A} n ≤ log^{-20} n`
  have hmono : (1:ℝ) ≤ P.lgn ^ (P.A - 20) := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hL1 (P.A - 20)
    simpa using h
  have hA20 : P.A = 20 + (P.A - 20) := by omega
  have h20A : P.lgn ^ 20 ≤ P.lgn ^ P.A := by
    have hEq : P.lgn ^ P.A = P.lgn ^ 20 * P.lgn ^ (P.A - 20) := by
      conv_lhs => rw [hA20]
      rw [pow_add]
    rw [hEq]
    calc P.lgn ^ 20 = P.lgn ^ 20 * 1 := by ring
      _ ≤ P.lgn ^ 20 * P.lgn ^ (P.A - 20) := mul_le_mul_of_nonneg_left hmono (by positivity)
  have hinv : (P.lgn ^ P.A)⁻¹ ≤ (P.lgn ^ 20)⁻¹ :=
    (inv_le_inv₀ (by positivity) h20pos).mpr h20A
  rw [HintParams.eta, mul_comm]
  calc (K + 1 + K / 8192) * (P.lgn ^ P.A)⁻¹ ≤ (K + 1 + K / 8192) * (P.lgn ^ 20)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv (by linarith)
    _ ≤ 1 := hstep

/-! ## The per-row error bounds of the paper's `Z = ∑_j |S_j △ Ŝ_j|` -/

/-- An **overloaded** row: the decoder abstains or outputs at most `K` coordinates, so the row error is
at most `|S_j| + K`; since `J_j ∪ S_j ≠ ∅` for an overloaded row this is at most
`(K+1)·|J_j ∪ S_j| ≤ (K+1)·|(J ∪ x)_j|`, exactly the mass counted by `overloadedMass`. -/
lemma rowErr_le_ov (P : HintParams) (N X Y : ℕ) (hm : 1 ≤ P.rows X Y)
    (lr : (P.scheme N X Y).LocalSeed) (x J : Finset ℕ) (j : Fin (P.rows X Y))
    (hov : P.Overloaded N X Y (rowImage N (P.rows X Y) lr.1 j.val J)
      (rowImage N (P.rows X Y) lr.1 j.val x)) :
    rowErr P N X Y lr x J j.val
      ≤ (P.BX N X Y + P.BY N X Y + 1) * (rowImage N (P.rows X Y) lr.1 j.val (J ∪ x)).card := by
  classical
  have hsym : (symmDiff (rowImage N (P.rows X Y) lr.1 j.val x)
      ((P.scheme N X Y).exactRowEst lr x J j ∩ range (rowLen N (P.rows X Y) j.val))).card
      ≤ (rowImage N (P.rows X Y) lr.1 j.val x).card + (P.BX N X Y + P.BY N X Y) := by
    have hsub : symmDiff (rowImage N (P.rows X Y) lr.1 j.val x)
        ((P.scheme N X Y).exactRowEst lr x J j ∩ range (rowLen N (P.rows X Y) j.val))
        ⊆ (rowImage N (P.rows X Y) lr.1 j.val x)
          ∪ ((P.scheme N X Y).exactRowEst lr x J j ∩ range (rowLen N (P.rows X Y) j.val)) := by
      intro a ha
      rw [Finset.mem_symmDiff] at ha
      rcases ha with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact Finset.mem_union.mpr (Or.inl h1)
      · exact Finset.mem_union.mpr (Or.inr h1)
    have hle : ((P.scheme N X Y).exactRowEst lr x J j
        ∩ range (rowLen N (P.rows X Y) j.val)).card ≤ P.BX N X Y + P.BY N X Y :=
      le_trans (Finset.card_le_card Finset.inter_subset_left)
        (card_exactRowEst_le_any P N X Y hm j lr x J)
    calc (symmDiff (rowImage N (P.rows X Y) lr.1 j.val x)
          ((P.scheme N X Y).exactRowEst lr x J j ∩ range (rowLen N (P.rows X Y) j.val))).card
        ≤ ((rowImage N (P.rows X Y) lr.1 j.val x)
          ∪ ((P.scheme N X Y).exactRowEst lr x J j
            ∩ range (rowLen N (P.rows X Y) j.val))).card := Finset.card_le_card hsub
      _ ≤ (rowImage N (P.rows X Y) lr.1 j.val x).card
          + ((P.scheme N X Y).exactRowEst lr x J j
            ∩ range (rowLen N (P.rows X Y) j.val)).card := Finset.card_union_le _ _
      _ ≤ (rowImage N (P.rows X Y) lr.1 j.val x).card + (P.BX N X Y + P.BY N X Y) := by omega
  have h1 : (rowImage N (P.rows X Y) lr.1 j.val x).card
      ≤ (rowImage N (P.rows X Y) lr.1 j.val (J ∪ x)).card :=
    Finset.card_le_card (rowImage_mono N (P.rows X Y) j.val lr.1 Finset.subset_union_right)
  have h2 : 0 < (rowImage N (P.rows X Y) lr.1 j.val (J ∪ x)).card := by
    rcases hov with hov | hov
    · have hpos : 0 < (rowImage N (P.rows X Y) lr.1 j.val J).card := by omega
      obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
      exact Finset.card_pos.mpr
        ⟨a, rowImage_mono N (P.rows X Y) j.val lr.1 Finset.subset_union_left ha⟩
    · have hle : ((rowImage N (P.rows X Y) lr.1 j.val x)
          \ (rowImage N (P.rows X Y) lr.1 j.val J)).card
          ≤ (rowImage N (P.rows X Y) lr.1 j.val x).card :=
        Finset.card_le_card Finset.sdiff_subset
      have hpos : 0 < (rowImage N (P.rows X Y) lr.1 j.val x).card := by omega
      obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
      exact Finset.card_pos.mpr
        ⟨a, rowImage_mono N (P.rows X Y) j.val lr.1 Finset.subset_union_right ha⟩
  have h3 : P.BX N X Y + P.BY N X Y
      ≤ (P.BX N X Y + P.BY N X Y) * (rowImage N (P.rows X Y) lr.1 j.val (J ∪ x)).card :=
    Nat.le_mul_of_pos_right _ h2
  rw [rowErr_eq_est P N X Y hm lr x J j]
  calc (symmDiff (rowImage N (P.rows X Y) lr.1 j.val x)
        ((P.scheme N X Y).exactRowEst lr x J j ∩ range (rowLen N (P.rows X Y) j.val))).card
      ≤ (rowImage N (P.rows X Y) lr.1 j.val x).card + (P.BX N X Y + P.BY N X Y) := hsym
    _ ≤ (rowImage N (P.rows X Y) lr.1 j.val (J ∪ x)).card
        + (P.BX N X Y + P.BY N X Y) * (rowImage N (P.rows X Y) lr.1 j.val (J ∪ x)).card := by
        omega
    _ = (P.BX N X Y + P.BY N X Y + 1) * (rowImage N (P.rows X Y) lr.1 j.val (J ∪ x)).card := by
        ring

/-- A **regular** row: `Ŝ_j ≠ S_j` is the only way the row can contribute, and then the contribution is
at most `|S_j| + K ≤ 2K` (both `|S_j|` and `|Ŝ_j|` are at most `K`).  An empty row recovers exactly
(`∅` is always a consistent candidate, so the decoder outputs `∅`), so the indicator form below holds
without a case distinction on `S_j = ∅`. -/
lemma rowErr_le_reg (P : HintParams) (N X Y : ℕ) (hm : 1 ≤ P.rows X Y)
    (lr : (P.scheme N X Y).LocalSeed) (x J : Finset ℕ) (j : Fin (P.rows X Y))
    (hreg : ¬ P.Overloaded N X Y (rowImage N (P.rows X Y) lr.1 j.val J)
      (rowImage N (P.rows X Y) lr.1 j.val x)) :
    (rowErr P N X Y lr x J j.val : ℝ)
      ≤ 2 * ((P.BX N X Y + P.BY N X Y : ℕ) : ℝ)
        * (if (P.scheme N X Y).exactRowEst lr x J j = rowImage N (P.rows X Y) lr.1 j.val x
            then (0:ℝ) else 1) := by
  classical
  have hsub : rowImage N (P.rows X Y) lr.1 j.val x ⊆ range (rowLen N (P.rows X Y) j.val) :=
    rowImage_subset_rowLen N (P.rows X Y) j.val hm j.isLt lr.1 x
  by_cases hfail : (P.scheme N X Y).exactRowEst lr x J j = rowImage N (P.rows X Y) lr.1 j.val x
  · -- the row is recovered exactly
    have hempty : symmDiff (rowImage N (P.rows X Y) lr.1 j.val x)
        ((P.scheme N X Y).exactRowEst lr x J j ∩ range (rowLen N (P.rows X Y) j.val)) = ∅ := by
      rw [hfail]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a ha
      rw [Finset.mem_symmDiff] at ha
      rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact h2 (Finset.mem_inter.mpr ⟨h1, hsub h1⟩)
      · exact h2 (Finset.mem_inter.mp h1).1
    have hzero : rowErr P N X Y lr x J j.val = 0 := by
      rw [rowErr_eq_est P N X Y hm lr x J j, hempty, Finset.card_empty]
    rw [if_pos hfail, hzero]
    simp
  · -- the row fails, and then contributes at most `2K`
    have h1 : ¬ (P.BX N X Y < (rowImage N (P.rows X Y) lr.1 j.val J).card) :=
      fun h => hreg (Or.inl h)
    have h2 : ¬ (P.BY N X Y
        < ((rowImage N (P.rows X Y) lr.1 j.val x) \ (rowImage N (P.rows X Y) lr.1 j.val J)).card) :=
      fun h => hreg (Or.inr h)
    have hS : (rowImage N (P.rows X Y) lr.1 j.val x).card ≤ P.BX N X Y + P.BY N X Y := by
      have hsub2 : rowImage N (P.rows X Y) lr.1 j.val x
          ⊆ ((rowImage N (P.rows X Y) lr.1 j.val x) ∩ (rowImage N (P.rows X Y) lr.1 j.val J))
            ∪ ((rowImage N (P.rows X Y) lr.1 j.val x) \ (rowImage N (P.rows X Y) lr.1 j.val J)) := by
        intro a ha
        by_cases hc : a ∈ rowImage N (P.rows X Y) lr.1 j.val J
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨ha, hc⟩))
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨ha, hc⟩))
      have hle1 : ((rowImage N (P.rows X Y) lr.1 j.val x)
          ∩ (rowImage N (P.rows X Y) lr.1 j.val J)).card
          ≤ (rowImage N (P.rows X Y) lr.1 j.val J).card :=
        Finset.card_le_card Finset.inter_subset_right
      have h3 : (rowImage N (P.rows X Y) lr.1 j.val x).card
          ≤ ((rowImage N (P.rows X Y) lr.1 j.val x) ∩ (rowImage N (P.rows X Y) lr.1 j.val J)).card
            + ((rowImage N (P.rows X Y) lr.1 j.val x)
              \ (rowImage N (P.rows X Y) lr.1 j.val J)).card := by
        calc (rowImage N (P.rows X Y) lr.1 j.val x).card
            ≤ (((rowImage N (P.rows X Y) lr.1 j.val x)
                ∩ (rowImage N (P.rows X Y) lr.1 j.val J))
              ∪ ((rowImage N (P.rows X Y) lr.1 j.val x)
                \ (rowImage N (P.rows X Y) lr.1 j.val J))).card := Finset.card_le_card hsub2
          _ ≤ _ := Finset.card_union_le _ _
      omega
    have hE : ((P.scheme N X Y).exactRowEst lr x J j
        ∩ range (rowLen N (P.rows X Y) j.val)).card ≤ P.BX N X Y + P.BY N X Y :=
      le_trans (Finset.card_le_card Finset.inter_subset_left)
        (card_exactRowEst_le_any P N X Y hm j lr x J)
    have hsym : (symmDiff (rowImage N (P.rows X Y) lr.1 j.val x)
        ((P.scheme N X Y).exactRowEst lr x J j ∩ range (rowLen N (P.rows X Y) j.val))).card
        ≤ 2 * (P.BX N X Y + P.BY N X Y) := by
      have hsub3 : symmDiff (rowImage N (P.rows X Y) lr.1 j.val x)
          ((P.scheme N X Y).exactRowEst lr x J j ∩ range (rowLen N (P.rows X Y) j.val))
          ⊆ (rowImage N (P.rows X Y) lr.1 j.val x)
            ∪ ((P.scheme N X Y).exactRowEst lr x J j ∩ range (rowLen N (P.rows X Y) j.val)) := by
        intro a ha
        rw [Finset.mem_symmDiff] at ha
        rcases ha with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact Finset.mem_union.mpr (Or.inl h1)
        · exact Finset.mem_union.mpr (Or.inr h1)
      calc (symmDiff (rowImage N (P.rows X Y) lr.1 j.val x)
            ((P.scheme N X Y).exactRowEst lr x J j ∩ range (rowLen N (P.rows X Y) j.val))).card
          ≤ _ := Finset.card_le_card hsub3
        _ ≤ (rowImage N (P.rows X Y) lr.1 j.val x).card
            + ((P.scheme N X Y).exactRowEst lr x J j
              ∩ range (rowLen N (P.rows X Y) j.val)).card := Finset.card_union_le _ _
        _ ≤ 2 * (P.BX N X Y + P.BY N X Y) := by omega
    have hcast : ((2 * (P.BX N X Y + P.BY N X Y) : ℕ) : ℝ)
        = 2 * ((P.BX N X Y + P.BY N X Y : ℕ) : ℝ) := by push_cast; ring
    have hmain : ((symmDiff (rowImage N (P.rows X Y) lr.1 j.val x)
        ((P.scheme N X Y).exactRowEst lr x J j ∩ range (rowLen N (P.rows X Y) j.val))).card : ℝ)
        ≤ 2 * ((P.BX N X Y + P.BY N X Y : ℕ) : ℝ) := by
      rw [← hcast]
      exact_mod_cast hsym
    rw [if_neg hfail, rowErr_eq_est P N X Y hm lr x J j]
    simpa using hmain

/-- **The expectation part of Lemma 5.4**, the paper's `E Z ≤ η(D+1)`, given the expected overloaded
mass (`claim2` of Lemma 5.3).

The paper's route: each row contributes at most `|S_j| + K`; overloaded rows are charged
`(K+1)|J_j ∪ S_j|`, whose total expectation is `(K+1)Dη²` (`claim2`), and regular rows are charged
`2K·Pr[fail]`, with `Pr[fail]` from Lemma 5.3's row recovery.

*Deviations from the paper (forced, and the reason the sharp row bound is imported):*

* The paper bounds a regular row by `2K·η²/8`.  That is only usable together with `η·K ≲ 1`, which is
  false at the milestone's `A ≥ 1` (take `Y = 1`, `X = 0`, `N = n`: then `K ≈ C log² n`, `D = 1`, so
  `K D η² ≈ C` while `η(D+1) = 2/log n`).  We therefore assume `20 ≤ A` (the caller raises `A₀` to
  `20`) and use the *sharp* bound `row_final_sharp ≤ 2^{-⌈lg(16/η²)⌉}/1024 ≤ η²/16384` instead of
  `η²/8`: the regular contribution is then `2K·D·η²/16384 = KDη²/8192` in total, and
  `(K+1)Dη² + KDη²/8192 = Dη²(K+1+K/8192) = η·(η(K+1+K/8192))·D ≤ ηD ≤ η(D+1)`
  once `η(K+1+K/8192) ≤ 1` (`eta_mul_K_bound`, which needs `K ≤ 4log¹³n + 2` from `hnl`, i.e.
  `D > N/log¹⁰ n`).  Weakening the sharp bound back to `η²/8` is *not* possible here.
* The paper counts "at most `D` nonempty regular rows"; we instead sum the per-row bounds over all `m`
  rows and use `m ≤ D`.  Same bound.
* The degenerate case `n = 2` (`η = 1`, `log n = 1`, where `η·K ≲ 1` fails) is handled separately: if
  `1 ≤ X + Y` then `1 ≤ D` and `Z ≤ N ≤ 2 = D+1`; if `X = Y = 0` then `x = J = ∅`, `m = 0`, the
  assembled estimate is `∅` and `Z = 0` (the empty support is always a consistent candidate). -/
theorem expU_Z_le (P : HintParams) (N X Y : ℕ) (hargs : P.NodeArgs N X Y)
    (hnl : P.NonLeaf N X Y) (hA : 20 ≤ P.A)
    (hmass : ∀ x J : Finset ℕ, Node.Valid N X Y x J →
      expU (fun π : Equiv.Perm (Fin N) => (P.overloadedMass N X Y π x J : ℝ)) ≤
        (HintParams.D N X Y : ℝ) * P.eta ^ 2) :
    ∀ x J : Finset ℕ, Node.Valid N X Y x J →
      expU (fun lr : (P.scheme N X Y).LocalSeed => ((P.scheme N X Y).Z lr x J : ℝ)) ≤
        P.eta * ((HintParams.D N X Y : ℝ) + 1) := by
  intro x J hvalid
  classical
  obtain ⟨hx, hJ, hJcard, hxcard⟩ := hvalid
  have hvalid' : Node.Valid N X Y x J := ⟨hx, hJ, hJcard, hxcard⟩
  rcases Nat.lt_or_ge P.n 3 with hnlt | hnge
  · -- ## the degenerate case `n = 2`: `η = 1` and `Z ≤ N ≤ D + 1`
    have hn2 : P.n = 2 := by
      have h1 : P.n < 3 := hnlt
      have h2 : 2 ≤ P.n := hargs.1
      omega
    have hlgn : P.lgn = 1 := by
      have h2 : ((2:ℕ):ℝ) = 2 := by norm_num
      rw [HintParams.lgn, hn2, lg, h2]
      exact Real.logb_self_eq_one (by norm_num)
    have heta1 : P.eta = 1 := by
      rw [HintParams.eta, hlgn]
      simp
    haveI : Nonempty (P.scheme N X Y).LocalSeed :=
      ⟨(1, fun _ => Classical.arbitrary ((P.scheme N X Y).Rand))⟩
    have hZN : ∀ lr : (P.scheme N X Y).LocalSeed, ((P.scheme N X Y).Z lr x J : ℝ) ≤ (N:ℝ) :=
      fun lr => by exact_mod_cast Z_le_N P N X Y x J hx lr
    have hZle : expU (fun lr : (P.scheme N X Y).LocalSeed => ((P.scheme N X Y).Z lr x J : ℝ)) ≤ (N:ℝ) :=
      calc expU (fun lr : (P.scheme N X Y).LocalSeed => ((P.scheme N X Y).Z lr x J : ℝ))
          ≤ expU (fun _ : (P.scheme N X Y).LocalSeed => (N:ℝ)) := expU_mono' hZN
        _ = (N:ℝ) := expU_const' (α := (P.scheme N X Y).LocalSeed) (N:ℝ)
    rcases Nat.eq_zero_or_pos (X + Y) with hXY | hXY
    · -- ## `X + Y = 0`: then `x = J = ∅`, `m = 0` and `Z = 0`
      have hX0 : X = 0 := by omega
      have hY0 : Y = 0 := by omega
      have hJ0 : J = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro a ha
        have h1 : 0 < J.card := Finset.card_pos.mpr ⟨a, ha⟩
        omega
      have hx0 : x = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro a ha
        have h1 : a ∈ x \ J := Finset.mem_sdiff.mpr ⟨ha, by rw [hJ0]; exact Finset.notMem_empty a⟩
        have h2 : 0 < (x \ J).card := Finset.card_pos.mpr ⟨a, h1⟩
        omega
      have hm0 : P.rows X Y = 0 := by
        rw [HintParams.rows, hX0, hY0]
        simp
      have hZ0 : ∀ lr : (P.scheme N X Y).LocalSeed, (P.scheme N X Y).Z lr x J = 0 := by
        intro lr
        have hA : (P.scheme N X Y).exactEstimate lr x J = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro p hp
          rw [RowScheme.exactEstimate, RowScheme.assembled] at hp
          obtain ⟨i, -, hfin⟩ := (mem_assemble_iff' N (P.rows X Y) lr.1
            (fun p => if h : p < P.rows X Y then (P.scheme N X Y).exactRowEst lr x J ⟨p, h⟩ else ∅) p).mp hp
          have hF0 : ∀ q : ℕ, (if h : q < P.rows X Y then
                (P.scheme N X Y).exactRowEst lr x J ⟨q, h⟩ else ∅) = (∅ : Finset ℕ) := by
            intro q
            split_ifs with h
            · rw [hm0] at h
              exact absurd h (Nat.not_lt_zero q)
            · rfl
          have hfin' : (lr.1 i).val / P.rows X Y ∈ (∅ : Finset ℕ) := by
            rw [← hF0 ((lr.1 i).val % P.rows X Y)]
            exact hfin
          exact Finset.notMem_empty _ hfin'
        rw [RowScheme.Z, hA, hx0]
        simp
      have hD0 : HintParams.D N X Y = 0 := by
        rw [HintParams.D, hXY]
        simp
      calc expU (fun lr : (P.scheme N X Y).LocalSeed => ((P.scheme N X Y).Z lr x J : ℝ))
          = expU (fun _ : (P.scheme N X Y).LocalSeed => (0:ℝ)) := by simp [hZ0]
        _ = 0 := expU_const' (α := (P.scheme N X Y).LocalSeed) (0:ℝ)
        _ ≤ P.eta * ((HintParams.D N X Y : ℝ) + 1) := by
            rw [hD0]
            have h1 : (0:ℝ) < P.eta := by rw [heta1]; norm_num
            positivity
    · -- ## `1 ≤ X + Y`: then `D ≥ 1`, so `D + 1 ≥ 2 ≥ N ≥ Z`
      have hD1 : 1 ≤ HintParams.D N X Y := by
        rw [HintParams.D]
        exact le_min hargs.2.2.1 hXY
      have hN2 : (N:ℝ) ≤ 2 := by
        have h1 : N ≤ P.n := hargs.2.2.2.1
        have h2 : N ≤ 2 := by omega
        exact_mod_cast h2
      calc expU (fun lr : (P.scheme N X Y).LocalSeed => ((P.scheme N X Y).Z lr x J : ℝ))
          ≤ (N:ℝ) := hZle
        _ ≤ 2 := hN2
        _ ≤ (HintParams.D N X Y : ℝ) + 1 := by
            have h1 : (1:ℝ) ≤ (HintParams.D N X Y : ℝ) := by exact_mod_cast hD1
            linarith
        _ = P.eta * ((HintParams.D N X Y : ℝ) + 1) := by rw [heta1, one_mul]
  · -- ## `n ≥ 3`
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hn3 : (3:ℝ) ≤ (P.n:ℝ) := by exact_mod_cast hnge
    have hlgn107 : (10/7:ℝ) ≤ P.lgn := by
      have hlog3gt : (1:ℝ) < Real.log 3 := by
        rw [← Real.log_exp 1]
        exact Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
      have hlog2le : Real.log 2 ≤ 0.7 := by have h := Real.log_two_lt_d9; linarith
      have h1 : Real.log 3 ≤ Real.log (P.n:ℝ) := Real.log_le_log (by norm_num) hn3
      rw [HintParams.lgn, lg, Real.logb, le_div_iff₀ hlog2pos]
      nlinarith
    have hlgn1 : 1 ≤ P.lgn := by linarith
    have heta : 0 < P.eta := by rw [HintParams.eta]; positivity
    have heta2 : (0:ℝ) < P.eta ^ 2 := by positivity
    have hm1 : 1 ≤ P.rows X Y := rows_pos P N X Y hargs hnl
    have hmD : P.rows X Y ≤ HintParams.D N X Y := rows_le_D P N X Y hargs
    have hDpos : (0:ℝ) < (HintParams.D N X Y : ℝ) := by
      have h1 : (1:ℝ) ≤ (HintParams.D N X Y : ℝ) := by
        have h2 : 1 ≤ HintParams.D N X Y := le_trans hm1 hmD
        exact_mod_cast h2
      linarith
    haveI : Nonempty (Equiv.Perm (Fin N)) := ⟨1⟩
    -- ### the sharp row bound of Lemma 5.3, divided by `1024`
    have hsharp : ∀ (π : Equiv.Perm (Fin N)) (j : Fin (P.rows X Y)),
        ¬ P.Overloaded N X Y (rowImage N (P.rows X Y) π j.val J)
            (rowImage N (P.rows X Y) π j.val x) →
        prU (fun β : (P.scheme N X Y).Rand =>
          (P.scheme N X Y).final j β (rowImage N (P.rows X Y) π j.val J)
            ((P.scheme N X Y).truePrefix j β (rowImage N (P.rows X Y) π j.val x)
              (P.scheme N X Y).ℓ)
          ≠ rowImage N (P.rows X Y) π j.val x) ≤ P.eta ^ 2 / 16384 := by
      intro π j hreg
      have hJj : rowImage N (P.rows X Y) π j.val J ⊆ range (rowLen N (P.rows X Y) j.val) :=
        rowImage_subset_rowLen N (P.rows X Y) j.val hm1 j.isLt π J
      have hSj : rowImage N (P.rows X Y) π j.val x ⊆ range (rowLen N (P.rows X Y) j.val) :=
        rowImage_subset_rowLen N (P.rows X Y) j.val hm1 j.isLt π x
      exact le_trans (row_final_sharp P N X Y hargs hnl j _ _ hJj hSj hreg)
        (inv_two_pow_ceil_le_div (P.eta ^ 2) heta2)
    -- ### the per-row estimate: split the seed, charge overloaded and regular rows differently
    have hinner : ∀ (π : Equiv.Perm (Fin N)) (j : Fin (P.rows X Y)),
        expU (fun f : Fin (P.rows X Y) → (P.scheme N X Y).Rand =>
            (rowErr P N X Y (π, f) x J j.val : ℝ))
        ≤ (if P.Overloaded N X Y (rowImage N (P.rows X Y) π j.val J)
              (rowImage N (P.rows X Y) π j.val x)
            then (((P.BX N X Y + P.BY N X Y : ℕ) : ℝ) + 1)
              * ((rowImage N (P.rows X Y) π j.val (J ∪ x)).card : ℝ)
            else 2 * ((P.BX N X Y + P.BY N X Y : ℕ) : ℝ) * (P.eta ^ 2 / 16384)) := by
      intro π j
      by_cases hov : P.Overloaded N X Y (rowImage N (P.rows X Y) π j.val J)
          (rowImage N (P.rows X Y) π j.val x)
      · rw [if_pos hov]
        have hpt : ∀ f : Fin (P.rows X Y) → (P.scheme N X Y).Rand,
            (rowErr P N X Y (π, f) x J j.val : ℝ)
              ≤ (((P.BX N X Y + P.BY N X Y : ℕ) : ℝ) + 1)
                * ((rowImage N (P.rows X Y) π j.val (J ∪ x)).card : ℝ) := by
          intro f
          have h := rowErr_le_ov P N X Y hm1 (π, f) x J j hov
          have h2 : (rowErr P N X Y (π, f) x J j.val : ℝ)
              ≤ (((P.BX N X Y + P.BY N X Y + 1)
                * (rowImage N (P.rows X Y) π j.val (J ∪ x)).card : ℕ) : ℝ) := by
            exact_mod_cast h
          push_cast at h2 ⊢
          linarith
        calc expU (fun f : Fin (P.rows X Y) → (P.scheme N X Y).Rand =>
              (rowErr P N X Y (π, f) x J j.val : ℝ))
            ≤ expU (fun _ : Fin (P.rows X Y) → (P.scheme N X Y).Rand =>
                (((P.BX N X Y + P.BY N X Y : ℕ) : ℝ) + 1)
                  * ((rowImage N (P.rows X Y) π j.val (J ∪ x)).card : ℝ)) := expU_mono' hpt
          _ = (((P.BX N X Y + P.BY N X Y : ℕ) : ℝ) + 1)
                * ((rowImage N (P.rows X Y) π j.val (J ∪ x)).card : ℝ) := expU_const' _
      · rw [if_neg hov]
        have hpt : ∀ f : Fin (P.rows X Y) → (P.scheme N X Y).Rand,
            (rowErr P N X Y (π, f) x J j.val : ℝ)
              ≤ (if (P.scheme N X Y).exactRowEst (π, f) x J j
                    ≠ rowImage N (P.rows X Y) π j.val x
                  then 2 * ((P.BX N X Y + P.BY N X Y : ℕ) : ℝ) else 0) := by
          intro f
          have h := rowErr_le_reg P N X Y hm1 (π, f) x J j hov
          by_cases hh : (P.scheme N X Y).exactRowEst (π, f) x J j
              = rowImage N (P.rows X Y) π j.val x
          · have h3 : (if (P.scheme N X Y).exactRowEst (π, f) x J j
                = rowImage N (P.rows X Y) π j.val x then (0:ℝ) else 1) = 0 := by
              rw [if_pos hh]
            rw [h3, mul_zero] at h
            rw [if_neg (by simp [hh])]
            linarith
          · have h3 : (if (P.scheme N X Y).exactRowEst (π, f) x J j
                = rowImage N (P.rows X Y) π j.val x then (0:ℝ) else 1) = 1 := by
              rw [if_neg hh]
            rw [h3, mul_one] at h
            rw [if_pos (by simpa using hh)]
            linarith
        have hmarginal : prU (fun f : Fin (P.rows X Y) → (P.scheme N X Y).Rand =>
              (P.scheme N X Y).exactRowEst (π, f) x J j
                ≠ rowImage N (P.rows X Y) π j.val x)
            = prU (fun β : (P.scheme N X Y).Rand =>
                (P.scheme N X Y).final j β (rowImage N (P.rows X Y) π j.val J)
                  ((P.scheme N X Y).truePrefix j β (rowImage N (P.rows X Y) π j.val x)
                    (P.scheme N X Y).ℓ)
                ≠ rowImage N (P.rows X Y) π j.val x) := by
          refine Eq.trans ?_ (prU_pi_apply (α := (P.scheme N X Y).Rand) j
            (fun β => (P.scheme N X Y).final j β (rowImage N (P.rows X Y) π j.val J)
              ((P.scheme N X Y).truePrefix j β (rowImage N (P.rows X Y) π j.val x)
                (P.scheme N X Y).ℓ) ≠ rowImage N (P.rows X Y) π j.val x))
          apply prU_congr'
          intro f
          constructor <;> intro hh <;> exact hh
        calc expU (fun f : Fin (P.rows X Y) → (P.scheme N X Y).Rand =>
              (rowErr P N X Y (π, f) x J j.val : ℝ))
            ≤ expU (fun f : Fin (P.rows X Y) → (P.scheme N X Y).Rand =>
                (if (P.scheme N X Y).exactRowEst (π, f) x J j
                    ≠ rowImage N (P.rows X Y) π j.val x
                  then 2 * ((P.BX N X Y + P.BY N X Y : ℕ) : ℝ) else 0)) := expU_mono' hpt
          _ = 2 * ((P.BX N X Y + P.BY N X Y : ℕ) : ℝ)
                * prU (fun f : Fin (P.rows X Y) → (P.scheme N X Y).Rand =>
                    (P.scheme N X Y).exactRowEst (π, f) x J j
                      ≠ rowImage N (P.rows X Y) π j.val x) :=
              expU_indicator''
                (Q := fun f : Fin (P.rows X Y) → (P.scheme N X Y).Rand =>
                  (P.scheme N X Y).exactRowEst (π, f) x J j
                    ≠ rowImage N (P.rows X Y) π j.val x)
                (c := 2 * ((P.BX N X Y + P.BY N X Y : ℕ) : ℝ))
          _ = 2 * ((P.BX N X Y + P.BY N X Y : ℕ) : ℝ)
                * prU (fun β : (P.scheme N X Y).Rand =>
                    (P.scheme N X Y).final j β (rowImage N (P.rows X Y) π j.val J)
                      ((P.scheme N X Y).truePrefix j β (rowImage N (P.rows X Y) π j.val x)
                        (P.scheme N X Y).ℓ)
                    ≠ rowImage N (P.rows X Y) π j.val x) := by rw [hmarginal]
          _ ≤ 2 * ((P.BX N X Y + P.BY N X Y : ℕ) : ℝ) * (P.eta ^ 2 / 16384) :=
              mul_le_mul_of_nonneg_left (hsharp π j hov) (by positivity)
    -- ### the row bound, after taking the expectation over the permutation
    have hrow : ∀ j : Fin (P.rows X Y),
        expU (fun π : Equiv.Perm (Fin N) =>
            expU (fun f : Fin (P.rows X Y) → (P.scheme N X Y).Rand =>
              (rowErr P N X Y (π, f) x J j.val : ℝ)))
        ≤ (((P.BX N X Y + P.BY N X Y : ℕ) : ℝ) + 1)
            * expU (fun π : Equiv.Perm (Fin N) =>
                (if P.Overloaded N X Y (rowImage N (P.rows X Y) π j.val J)
                    (rowImage N (P.rows X Y) π j.val x)
                 then ((rowImage N (P.rows X Y) π j.val (J ∪ x)).card : ℝ) else 0))
          + 2 * ((P.BX N X Y + P.BY N X Y : ℕ) : ℝ) * (P.eta ^ 2 / 16384) := by
      intro j
      have hpt : ∀ π : Equiv.Perm (Fin N),
          expU (fun f : Fin (P.rows X Y) → (P.scheme N X Y).Rand =>
            (rowErr P N X Y (π, f) x J j.val : ℝ))
          ≤ (((P.BX N X Y + P.BY N X Y : ℕ) : ℝ) + 1)
              * (if P.Overloaded N X Y (rowImage N (P.rows X Y) π j.val J)
                    (rowImage N (P.rows X Y) π j.val x)
                 then ((rowImage N (P.rows X Y) π j.val (J ∪ x)).card : ℝ) else 0)
            + 2 * ((P.BX N X Y + P.BY N X Y : ℕ) : ℝ) * (P.eta ^ 2 / 16384) := by
        intro π
        refine le_trans (hinner π j) ?_
        by_cases hov : P.Overloaded N X Y (rowImage N (P.rows X Y) π j.val J)
            (rowImage N (P.rows X Y) π j.val x)
        · rw [if_pos hov, if_pos hov]
          have h0 : (0:ℝ) ≤ 2 * ((P.BX N X Y + P.BY N X Y : ℕ) : ℝ) * (P.eta ^ 2 / 16384) := by
            positivity
          linarith
        · rw [if_neg hov, if_neg hov]
          simp
      have h := expU_affine' (α := Equiv.Perm (Fin N)) (((P.BX N X Y + P.BY N X Y : ℕ) : ℝ) + 1)
        (2 * ((P.BX N X Y + P.BY N X Y : ℕ) : ℝ) * (P.eta ^ 2 / 16384))
        (fun π : Equiv.Perm (Fin N) =>
          (if P.Overloaded N X Y (rowImage N (P.rows X Y) π j.val J)
              (rowImage N (P.rows X Y) π j.val x)
           then ((rowImage N (P.rows X Y) π j.val (J ∪ x)).card : ℝ) else 0))
      exact le_trans (expU_mono' hpt) (le_of_eq h)
    -- ### summing the rows: the overloaded part is `overloadedMass`
    have hsum_mass : ∑ j : Fin (P.rows X Y),
          expU (fun π : Equiv.Perm (Fin N) =>
            (if P.Overloaded N X Y (rowImage N (P.rows X Y) π j.val J)
                (rowImage N (P.rows X Y) π j.val x)
             then ((rowImage N (P.rows X Y) π j.val (J ∪ x)).card : ℝ) else 0))
        ≤ (HintParams.D N X Y : ℝ) * P.eta ^ 2 := by
      have hfun : (fun π : Equiv.Perm (Fin N) => ∑ j : Fin (P.rows X Y),
            (if P.Overloaded N X Y (rowImage N (P.rows X Y) π j.val J)
                (rowImage N (P.rows X Y) π j.val x)
             then ((rowImage N (P.rows X Y) π j.val (J ∪ x)).card : ℝ) else 0))
          = (fun π : Equiv.Perm (Fin N) => (P.overloadedMass N X Y π x J : ℝ)) := by
        funext π
        have h1 : ((P.overloadedMass N X Y π x J : ℕ) : ℝ)
            = ∑ j ∈ Finset.range (P.rows X Y),
                (if P.Overloaded N X Y (rowImage N (P.rows X Y) π j J)
                    (rowImage N (P.rows X Y) π j x)
                 then ((rowImage N (P.rows X Y) π j (J ∪ x)).card : ℝ) else 0) := by
          dsimp only [HintParams.overloadedMass]
          push_cast
          rfl
        rw [h1]
        first
          | exact Fin.sum_univ_eq_sum_range (fun j => (if P.Overloaded N X Y
                (rowImage N (P.rows X Y) π j J) (rowImage N (P.rows X Y) π j x)
              then ((rowImage N (P.rows X Y) π j (J ∪ x)).card : ℝ) else 0)) (P.rows X Y)
          | exact (Fin.sum_univ_eq_sum_range (fun j => (if P.Overloaded N X Y
                (rowImage N (P.rows X Y) π j J) (rowImage N (P.rows X Y) π j x)
              then ((rowImage N (P.rows X Y) π j (J ∪ x)).card : ℝ) else 0)) (P.rows X Y)).symm
      have hswap : ∑ j : Fin (P.rows X Y),
            expU (fun π : Equiv.Perm (Fin N) =>
              (if P.Overloaded N X Y (rowImage N (P.rows X Y) π j.val J)
                  (rowImage N (P.rows X Y) π j.val x)
               then ((rowImage N (P.rows X Y) π j.val (J ∪ x)).card : ℝ) else 0))
          = expU (fun π : Equiv.Perm (Fin N) => ∑ j : Fin (P.rows X Y),
              (if P.Overloaded N X Y (rowImage N (P.rows X Y) π j.val J)
                  (rowImage N (P.rows X Y) π j.val x)
               then ((rowImage N (P.rows X Y) π j.val (J ∪ x)).card : ℝ) else 0)) :=
        (expU_sum_fin' (fun (j : Fin (P.rows X Y)) (π : Equiv.Perm (Fin N)) =>
          (if P.Overloaded N X Y (rowImage N (P.rows X Y) π j.val J)
              (rowImage N (P.rows X Y) π j.val x)
           then ((rowImage N (P.rows X Y) π j.val (J ∪ x)).card : ℝ) else 0))).symm
      rw [hswap, hfun]
      exact hmass x J hvalid'
    -- ### the final numeric assembly
    have hstep : (((P.BX N X Y + P.BY N X Y : ℕ) : ℝ) + 1)
          * (∑ j : Fin (P.rows X Y), expU (fun π : Equiv.Perm (Fin N) =>
              (if P.Overloaded N X Y (rowImage N (P.rows X Y) π j.val J)
                  (rowImage N (P.rows X Y) π j.val x)
               then ((rowImage N (P.rows X Y) π j.val (J ∪ x)).card : ℝ) else 0)))
          + (P.rows X Y : ℝ)
            * (2 * ((P.BX N X Y + P.BY N X Y : ℕ) : ℝ) * (P.eta ^ 2 / 16384))
        ≤ P.eta * ((HintParams.D N X Y : ℝ) + 1) := by
      have h1 : (((P.BX N X Y + P.BY N X Y : ℕ) : ℝ) + 1)
          * (∑ j : Fin (P.rows X Y), expU (fun π : Equiv.Perm (Fin N) =>
              (if P.Overloaded N X Y (rowImage N (P.rows X Y) π j.val J)
                  (rowImage N (P.rows X Y) π j.val x)
               then ((rowImage N (P.rows X Y) π j.val (J ∪ x)).card : ℝ) else 0)))
          ≤ (((P.BX N X Y + P.BY N X Y : ℕ) : ℝ) + 1)
            * ((HintParams.D N X Y : ℝ) * P.eta ^ 2) :=
        mul_le_mul_of_nonneg_left hsum_mass (by positivity)
      have h2 : (P.rows X Y : ℝ)
            * (2 * ((P.BX N X Y + P.BY N X Y : ℕ) : ℝ) * (P.eta ^ 2 / 16384))
          ≤ (HintParams.D N X Y : ℝ)
            * (2 * ((P.BX N X Y + P.BY N X Y : ℕ) : ℝ) * (P.eta ^ 2 / 16384)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast hmD
      have h3 : (((P.BX N X Y + P.BY N X Y : ℕ) : ℝ) + 1)
            * ((HintParams.D N X Y : ℝ) * P.eta ^ 2)
          + (HintParams.D N X Y : ℝ)
            * (2 * ((P.BX N X Y + P.BY N X Y : ℕ) : ℝ) * (P.eta ^ 2 / 16384))
          = (HintParams.D N X Y : ℝ) * P.eta ^ 2
            * ((((P.BX N X Y + P.BY N X Y : ℕ) : ℝ) + 1)
              + 2 * ((P.BX N X Y + P.BY N X Y : ℕ) : ℝ) / 16384) := by ring
      have h4 : (HintParams.D N X Y : ℝ) * P.eta ^ 2
            * ((((P.BX N X Y + P.BY N X Y : ℕ) : ℝ) + 1)
              + 2 * ((P.BX N X Y + P.BY N X Y : ℕ) : ℝ) / 16384)
          = P.eta * (HintParams.D N X Y : ℝ)
            * (P.eta * ((((P.BX N X Y + P.BY N X Y : ℕ) : ℝ) + 1)
              + ((P.BX N X Y + P.BY N X Y : ℕ) : ℝ) / 8192)) := by ring
      have h5 : P.eta * ((((P.BX N X Y + P.BY N X Y : ℕ) : ℝ) + 1)
            + ((P.BX N X Y + P.BY N X Y : ℕ) : ℝ) / 8192) ≤ 1 :=
        eta_mul_K_bound P N X Y hargs hnl hA hlgn107
      have h6 : (0:ℝ) ≤ P.eta * (HintParams.D N X Y : ℝ) := by positivity
      have h7 : P.eta * (HintParams.D N X Y : ℝ)
            * (P.eta * ((((P.BX N X Y + P.BY N X Y : ℕ) : ℝ) + 1)
              + ((P.BX N X Y + P.BY N X Y : ℕ) : ℝ) / 8192))
          ≤ P.eta * (HintParams.D N X Y : ℝ) * 1 := mul_le_mul_of_nonneg_left h5 h6
      have h8 : P.eta * (HintParams.D N X Y : ℝ) ≤ P.eta * ((HintParams.D N X Y : ℝ) + 1) := by
        have h9 := heta.le
        nlinarith
      linarith [h1, h2, h3, h4, h7, h8]
    -- ### `Z` as the sum of the row errors, and the split of the seed
    have htot : expU (fun lr : (P.scheme N X Y).LocalSeed => ((P.scheme N X Y).Z lr x J : ℝ))
        = ∑ j : Fin (P.rows X Y), expU (fun π : Equiv.Perm (Fin N) =>
            expU (fun f : Fin (P.rows X Y) → (P.scheme N X Y).Rand =>
              (rowErr P N X Y (π, f) x J j.val : ℝ))) := by
      have hfun : ∀ lr : (P.scheme N X Y).LocalSeed,
          ((P.scheme N X Y).Z lr x J : ℝ)
            = ∑ j : Fin (P.rows X Y), (rowErr P N X Y lr x J j.val : ℝ) := by
        intro lr
        rw [Z_eq_sum_rows P N X Y hm1 x J hx lr]
        push_cast
        rfl
      calc expU (fun lr : (P.scheme N X Y).LocalSeed => ((P.scheme N X Y).Z lr x J : ℝ))
          = expU (fun lr : (P.scheme N X Y).LocalSeed =>
              ∑ j : Fin (P.rows X Y), (rowErr P N X Y lr x J j.val : ℝ)) := by simp only [hfun]
        _ = expU (fun π : Equiv.Perm (Fin N) =>
              expU (fun f : Fin (P.rows X Y) → (P.scheme N X Y).Rand =>
                ∑ j : Fin (P.rows X Y), (rowErr P N X Y (π, f) x J j.val : ℝ))) :=
              expU_localSeed_local P N X Y
                (fun lr => ∑ j : Fin (P.rows X Y), (rowErr P N X Y lr x J j.val : ℝ))
        _ = expU (fun π : Equiv.Perm (Fin N) => ∑ j : Fin (P.rows X Y),
              expU (fun f : Fin (P.rows X Y) → (P.scheme N X Y).Rand =>
                (rowErr P N X Y (π, f) x J j.val : ℝ))) := by
              have h3 : ∀ π : Equiv.Perm (Fin N),
                  expU (fun f : Fin (P.rows X Y) → (P.scheme N X Y).Rand =>
                    ∑ j : Fin (P.rows X Y), (rowErr P N X Y (π, f) x J j.val : ℝ))
                    = ∑ j : Fin (P.rows X Y), expU (fun f : Fin (P.rows X Y) → (P.scheme N X Y).Rand =>
                        (rowErr P N X Y (π, f) x J j.val : ℝ)) :=
                fun π => expU_sum_fin'
                  (fun (j : Fin (P.rows X Y)) (f : Fin (P.rows X Y) → (P.scheme N X Y).Rand) =>
                    (rowErr P N X Y (π, f) x J j.val : ℝ))
              simp only [h3]
        _ = ∑ j : Fin (P.rows X Y), expU (fun π : Equiv.Perm (Fin N) =>
              expU (fun f : Fin (P.rows X Y) → (P.scheme N X Y).Rand =>
                (rowErr P N X Y (π, f) x J j.val : ℝ))) :=
              expU_sum_fin'
                (fun (j : Fin (P.rows X Y)) (π : Equiv.Perm (Fin N)) =>
                  expU (fun f : Fin (P.rows X Y) → (P.scheme N X Y).Rand =>
                    (rowErr P N X Y (π, f) x J j.val : ℝ)))
    rw [htot]
    refine le_trans (Finset.sum_le_sum (fun j _ => hrow j)) ?_
    have hsum_eq : ∑ j : Fin (P.rows X Y),
          ((((P.BX N X Y + P.BY N X Y : ℕ) : ℝ) + 1)
            * expU (fun π : Equiv.Perm (Fin N) =>
                (if P.Overloaded N X Y (rowImage N (P.rows X Y) π j.val J)
                    (rowImage N (P.rows X Y) π j.val x)
                 then ((rowImage N (P.rows X Y) π j.val (J ∪ x)).card : ℝ) else 0))
          + 2 * ((P.BX N X Y + P.BY N X Y : ℕ) : ℝ) * (P.eta ^ 2 / 16384))
        = (((P.BX N X Y + P.BY N X Y : ℕ) : ℝ) + 1)
            * (∑ j : Fin (P.rows X Y), expU (fun π : Equiv.Perm (Fin N) =>
                (if P.Overloaded N X Y (rowImage N (P.rows X Y) π j.val J)
                    (rowImage N (P.rows X Y) π j.val x)
                 then ((rowImage N (P.rows X Y) π j.val (J ∪ x)).card : ℝ) else 0)))
          + (P.rows X Y : ℝ)
            * (2 * ((P.BX N X Y + P.BY N X Y : ℕ) : ℝ) * (P.eta ^ 2 / 16384)) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      simp
    rw [hsum_eq]
    exact hstep

/-- **The tail part of Lemma 5.4, as in the paper** ("For `t < N`, Lemma 4.8 gives ..."):
concentration (Lemma 4.8, from the Lemma 4.8 milestone, as `lemma_4_8`) around
`E Z ≤ η(D+1)` gives `Pr[Z > resid] ≤ 2^{-λ_*}`.  The sensitivities are the paper's `4K`/`2K` with
denominator `20DK²`, and the "not small" stopping rule (`D > C³λ_* log⁶ n/η²`, since the node is not
in the `small` case) together with `K = O(C log³ n)` yields the exponent `Ω(Cλ_*)`. -/
theorem prU_Z_gt_resid (P : HintParams) (N X Y : ℕ) (hargs : P.NodeArgs N X Y)
    (hnl : P.NonLeaf N X Y) (hC : 2000 ≤ P.C)
    (hmean : ∀ x J : Finset ℕ, Node.Valid N X Y x J →
      expU (fun lr : (P.scheme N X Y).LocalSeed => ((P.scheme N X Y).Z lr x J : ℝ)) ≤
        P.eta * ((HintParams.D N X Y : ℝ) + 1)) :
    ∀ x J : Finset ℕ, Node.Valid N X Y x J →
      prU (fun lr : (P.scheme N X Y).LocalSeed => P.resid N X Y < (P.scheme N X Y).Z lr x J) ≤
        ((2 : ℝ) ^ P.lamStar)⁻¹ := by
  intro x J hvalid
  classical
  obtain ⟨hx, hJ, hJcard, hxcard⟩ := hvalid
  have hvalid' : Node.Valid N X Y x J := ⟨hx, hJ, hJcard, hxcard⟩
  have hN1 : 1 ≤ N := hargs.2.2.1
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN1
  have hn2 : (2:ℝ) ≤ (P.n:ℝ) := by exact_mod_cast hargs.1
  have hlgnpos : 0 < P.lgn := by
    rw [HintParams.lgn, lg]
    exact Real.logb_pos (by norm_num) (by linarith)
  have hlgn1 : 1 ≤ P.lgn := by
    rw [HintParams.lgn, lg,
      Real.le_logb_iff_rpow_le (by norm_num : (1:ℝ) < 2) (by linarith : (0:ℝ) < (P.n:ℝ))]
    simpa using hn2
  have heta : 0 < P.eta := by rw [HintParams.eta]; positivity
  have hC1 : 1 ≤ P.C := by omega
  have hm1 : 1 ≤ P.rows X Y := rows_pos P N X Y hargs hnl
  have hmpos : (0:ℝ) < (P.rows X Y : ℝ) := by exact_mod_cast hm1
  -- the node is not `cheap`, so `D ≥ 1`
  have hcheap : P.rule N X Y ≠ .cheap := by
    intro h
    rcases hnl with h' | h' <;> (rw [h] at h' <;> exact absurd h' (by decide))
  have hDcheap : ¬ ((HintParams.D N X Y : ℝ) ≤ (N:ℝ) / P.lgn ^ 10) := by
    intro h
    exact hcheap (by rw [HintParams.rule]; exact if_pos h)
  have hDgt : (N:ℝ) / P.lgn ^ 10 < (HintParams.D N X Y : ℝ) := not_le.mp hDcheap
  have hlgn10 : (0:ℝ) < P.lgn ^ 10 := by positivity
  have hD1 : 0 < HintParams.D N X Y := by
    have h1 : (0:ℝ) < (HintParams.D N X Y : ℝ) := by
      have := div_pos hNpos hlgn10
      linarith
    exact_mod_cast h1
  have hDpos : (0:ℝ) < (HintParams.D N X Y : ℝ) := by exact_mod_cast hD1
  have hZN : ∀ lr, (P.scheme N X Y).Z lr x J ≤ N := fun lr => Z_le_N P N X Y x J hx lr
  by_cases hbig : P.resid N X Y = N
  · -- `resid = N`: `Z ≤ N` always, so the event is empty
    have hempty : ∀ lr : (P.scheme N X Y).LocalSeed,
        ¬ (P.resid N X Y < (P.scheme N X Y).Z lr x J) := by
      intro lr h
      have h1 := hZN lr
      omega
    have h0 : prU (fun lr : (P.scheme N X Y).LocalSeed =>
        P.resid N X Y < (P.scheme N X Y).Z lr x J) = 0 := by
      have hc : prU (fun lr : (P.scheme N X Y).LocalSeed =>
            P.resid N X Y < (P.scheme N X Y).Z lr x J)
          = prU (fun _ : (P.scheme N X Y).LocalSeed => False) :=
        prU_congr' (fun lr => ⟨fun h => absurd h (hempty lr), fun h => h.elim⟩)
      rw [hc]
      unfold prU
      simp
    rw [h0]
    positivity
  · have hres_eq : P.resid N X Y = ⌈2 * P.eta * ((HintParams.D N X Y : ℝ) + 1)⌉₊ := by
      rw [HintParams.resid]
      have hlt : ⌈2 * P.eta * ((HintParams.D N X Y : ℝ) + 1)⌉₊ < N := by
        by_contra hle
        exact hbig (by rw [HintParams.resid]; exact min_eq_left (not_lt.mp hle))
      exact min_eq_right (le_of_lt hlt)
    have hΔpos : 0 < P.eta * ((HintParams.D N X Y : ℝ) + 1) := by positivity
    -- the row count and the hint size are bounded by `D`
    have hDm : P.rows X Y ≤ HintParams.D N X Y := by
      rw [HintParams.D]
      apply le_min
      · have hYN : Y ≤ N := hargs.2.2.2.2.2
        have h3 : (1:ℝ) ≤ P.lgn ^ 3 := one_le_cu_lgn P hlgn1
        have hX : (X:ℝ) ≤ (N:ℝ) := by exact_mod_cast hargs.2.2.2.2.1
        have hL3 : (0:ℝ) < P.lgn ^ 3 := by positivity
        rw [HintParams.rows]
        apply max_le hYN
        rw [Nat.ceil_le, div_le_iff₀ hL3]
        have h4 : (N:ℝ) ≤ (N:ℝ) * P.lgn^3 := by
          calc (N:ℝ) = (N:ℝ) * 1 := by ring
            _ ≤ (N:ℝ) * P.lgn^3 := mul_le_mul_of_nonneg_left h3 (by positivity)
        linarith
      · have h3 : (1:ℝ) ≤ P.lgn ^ 3 := one_le_cu_lgn P hlgn1
        have hL3 : (0:ℝ) < P.lgn ^ 3 := by positivity
        have hXnn : (0:ℝ) ≤ (X:ℝ) := by positivity
        rw [HintParams.rows]
        apply max_le (by omega)
        rw [Nat.ceil_le]
        have h1 : (X:ℝ) / P.lgn^3 ≤ (X:ℝ) := by
          rw [div_le_iff₀ hL3]
          nlinarith
        have h2 : (X:ℝ) ≤ ((X + Y : ℕ) : ℝ) := by push_cast; linarith
        linarith
    have hDJ : (J ∪ x).card ≤ HintParams.D N X Y := by
      rw [HintParams.D]
      apply le_min
      · have hsub : J ∪ x ⊆ range N := Finset.union_subset hJ hx
        calc (J ∪ x).card ≤ (range N).card := Finset.card_le_card hsub
          _ = N := Finset.card_range N
      · have hsub : J ∪ x ⊆ J ∪ (x \ J) := by
          intro a ha
          rcases Finset.mem_union.mp ha with h | h
          · exact Finset.mem_union.mpr (Or.inl h)
          · by_cases hJ' : a ∈ J
            · exact Finset.mem_union.mpr (Or.inl hJ')
            · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨h, hJ'⟩))
        have h1 : (J ∪ x).card ≤ J.card + (x \ J).card :=
          le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
        omega
    -- `K = B_X + B_Y ≥ 1` and the universal estimate bound
    have hK1 : 1 ≤ P.BX N X Y + P.BY N X Y := by
      have h1 : 1 ≤ P.BX N X Y := by
        rw [HintParams.BX]
        apply le_min
        · rw [HintParams.Nmax]
          exact Nat.ceil_pos.mpr (by positivity)
        · exact Nat.ceil_pos.mpr (by positivity)
      omega
    have hest : ∀ (lr : (P.scheme N X Y).LocalSeed) (j : Fin (P.rows X Y)),
        ((P.scheme N X Y).exactRowEst lr x J j).card ≤ P.BX N X Y + P.BY N X Y :=
      fun lr j => card_exactRowEst_le_any P N X Y hm1 j lr x J
    -- Lemma 4.8 (concentration)
    have h48 := lemma_4_8 (P.scheme N X Y) x J hx hJ hm1 (HintParams.D N X Y) hDm hDJ
      (P.BX N X Y + P.BY N X Y) hK1 hest (P.eta * ((HintParams.D N X Y : ℝ) + 1)) hΔpos
    have htail := h48.2.2
    refine le_trans ?_ (le_trans htail ?_)
    · -- `resid < Z` forces `E Z + Δ < Z`
      apply prU_mono'
      intro lr h
      have hZ : (P.resid N X Y : ℝ) < ((P.scheme N X Y).Z lr x J : ℝ) := by exact_mod_cast h
      have hceil : 2 * P.eta * ((HintParams.D N X Y : ℝ) + 1) ≤ (P.resid N X Y : ℝ) := by
        rw [hres_eq]
        exact Nat.le_ceil _
      have hme := hmean x J hvalid'
      linarith
    · -- the exponent is `Ω(C λ_*) ≥ λ_* log 2`
      have hKb : ((P.BX N X Y + P.BY N X Y : ℕ) : ℝ) ≤ 16 * (P.C:ℝ) * P.lgn^3 :=
        K_le_C P N X Y hC1 hlgn1
      have hnotsmall : ¬ ((HintParams.D N X Y : ℝ)
          ≤ (P.C:ℝ)^3 * (P.lamStar:ℝ) * P.lgn^6 / P.eta^2) := by
        intro h
        have hrule : P.rule N X Y = .small := by
          rw [HintParams.rule]
          rw [if_neg hDcheap, if_pos h]
        rcases hnl with h' | h' <;> (rw [hrule] at h' <;> exact absurd h' (by decide))
      have hns : (P.C:ℝ)^3 * (P.lamStar:ℝ) * P.lgn^6
          < (HintParams.D N X Y : ℝ) * P.eta^2 := by
        have h1 := not_le.mp hnotsmall
        have heta2 : (0:ℝ) < P.eta^2 := by positivity
        rw [div_lt_iff₀ heta2] at h1
        linarith
      have hln2 : Real.log 2 ≤ 0.7 := by
        have := Real.log_two_lt_d9
        linarith
      have hlamnn : (0:ℝ) ≤ (P.lamStar:ℝ) := by positivity
      have hCbig : (2000:ℝ) ≤ (P.C:ℝ) := by exact_mod_cast hC
      have hKpos : (0:ℝ) < ((P.BX N X Y + P.BY N X Y : ℕ) : ℝ) := by
        have : 0 < P.BX N X Y + P.BY N X Y := by omega
        exact_mod_cast this
      have hmain : (P.lamStar:ℝ) * Real.log 2
          ≤ (P.eta * ((HintParams.D N X Y : ℝ) + 1))^2
            / (10 * (HintParams.D N X Y : ℝ) * (((P.BX N X Y + P.BY N X Y : ℕ) : ℝ))^2) := by
        have hD1' : (1:ℝ) ≤ (HintParams.D N X Y : ℝ) := by exact_mod_cast hD1
        have hK2 : (((P.BX N X Y + P.BY N X Y : ℕ) : ℝ))^2 ≤ 256 * (P.C:ℝ)^2 * P.lgn^6 := by
          have h2 : (0:ℝ) ≤ 16 * (P.C:ℝ) * P.lgn^3 := by positivity
          have h3 : (((P.BX N X Y + P.BY N X Y : ℕ) : ℝ))^2
              ≤ (16 * (P.C:ℝ) * P.lgn^3)^2 := by
            nlinarith [hKb, hKpos, h2]
          calc (((P.BX N X Y + P.BY N X Y : ℕ) : ℝ))^2
              ≤ (16 * (P.C:ℝ) * P.lgn^3)^2 := h3
            _ = 256 * (P.C:ℝ)^2 * P.lgn^6 := by ring
        have hnsD : (P.C:ℝ)^3 * (P.lamStar:ℝ) * P.lgn^6 * (HintParams.D N X Y : ℝ)
            < ((HintParams.D N X Y : ℝ))^2 * P.eta^2 := by
          have h := mul_lt_mul_of_pos_right hns hDpos
          calc (P.C:ℝ)^3 * (P.lamStar:ℝ) * P.lgn^6 * (HintParams.D N X Y : ℝ)
              < ((HintParams.D N X Y : ℝ) * P.eta^2) * (HintParams.D N X Y : ℝ) := h
            _ = ((HintParams.D N X Y : ℝ))^2 * P.eta^2 := by ring
        have hden : (0:ℝ) < 10 * (HintParams.D N X Y : ℝ)
            * (((P.BX N X Y + P.BY N X Y : ℕ) : ℝ))^2 := by positivity
        rw [le_div_iff₀ hden]
        have step1 : (P.lamStar:ℝ) * Real.log 2
            * (10 * (HintParams.D N X Y : ℝ) * (((P.BX N X Y + P.BY N X Y : ℕ) : ℝ))^2)
            ≤ 7 * ((P.lamStar:ℝ) * (HintParams.D N X Y : ℝ)
              * (((P.BX N X Y + P.BY N X Y : ℕ) : ℝ))^2) := by
          have hX : (0:ℝ) ≤ (P.lamStar:ℝ) * (HintParams.D N X Y : ℝ)
              * (((P.BX N X Y + P.BY N X Y : ℕ) : ℝ))^2 := by positivity
          nlinarith [hln2, hX]
        have step2 : 7 * ((P.lamStar:ℝ) * (HintParams.D N X Y : ℝ)
              * (((P.BX N X Y + P.BY N X Y : ℕ) : ℝ))^2)
            ≤ 1792 * ((P.lamStar:ℝ) * (HintParams.D N X Y : ℝ) * (P.C:ℝ)^2 * P.lgn^6) := by
          have hpos : (0:ℝ) ≤ 7 * ((P.lamStar:ℝ) * (HintParams.D N X Y : ℝ)) := by positivity
          have h := mul_le_mul_of_nonneg_left hK2 hpos
          calc 7 * ((P.lamStar:ℝ) * (HintParams.D N X Y : ℝ)
                * (((P.BX N X Y + P.BY N X Y : ℕ) : ℝ))^2)
              = (7 * ((P.lamStar:ℝ) * (HintParams.D N X Y : ℝ))
                * (((P.BX N X Y + P.BY N X Y : ℕ) : ℝ))^2) := by ring
            _ ≤ (7 * ((P.lamStar:ℝ) * (HintParams.D N X Y : ℝ)))
                * (256 * (P.C:ℝ)^2 * P.lgn^6) := h
            _ = 1792 * ((P.lamStar:ℝ) * (HintParams.D N X Y : ℝ) * (P.C:ℝ)^2 * P.lgn^6) := by
                ring
        have step3 : 1792 * ((P.lamStar:ℝ) * (HintParams.D N X Y : ℝ) * (P.C:ℝ)^2 * P.lgn^6)
            ≤ ((HintParams.D N X Y : ℝ))^2 * P.eta^2 := by
          have hy : (0:ℝ) ≤ (P.lamStar:ℝ) * (HintParams.D N X Y : ℝ) * (P.C:ℝ)^2 * P.lgn^6 :=
            by positivity
          have h1 : 1792 * ((P.lamStar:ℝ) * (HintParams.D N X Y : ℝ) * (P.C:ℝ)^2 * P.lgn^6)
              ≤ (P.C:ℝ) * ((P.lamStar:ℝ) * (HintParams.D N X Y : ℝ)
                * (P.C:ℝ)^2 * P.lgn^6) := by nlinarith [hCbig, hy]
          have h2 : (P.C:ℝ) * ((P.lamStar:ℝ) * (HintParams.D N X Y : ℝ) * (P.C:ℝ)^2 * P.lgn^6)
              = (P.C:ℝ)^3 * (P.lamStar:ℝ) * P.lgn^6 * (HintParams.D N X Y : ℝ) := by ring
          linarith [h1, h2, hnsD]
        have step4 : ((HintParams.D N X Y : ℝ))^2 * P.eta^2
            ≤ (P.eta * ((HintParams.D N X Y : ℝ) + 1))^2 := by
          nlinarith [hDpos, hD1', sq_nonneg P.eta]
        linarith [step1, step2, step3, step4]
      have h2exp : ((2:ℝ) ^ P.lamStar)⁻¹ = Real.exp (-((P.lamStar:ℝ) * Real.log 2)) := by
        rw [← Real.rpow_natCast (2:ℝ) P.lamStar, ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
          Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
        congr 1
        ring
      calc Real.exp (-((P.eta * ((HintParams.D N X Y : ℝ) + 1))^2
            / (10 * (HintParams.D N X Y : ℝ) * (((P.BX N X Y + P.BY N X Y : ℕ) : ℝ))^2)))
          ≤ Real.exp (-((P.lamStar:ℝ) * Real.log 2)) := Real.exp_le_exp.mpr (by linarith)
        _ = ((2:ℝ) ^ P.lamStar)⁻¹ := h2exp.symm

/-! ## Lemma 5.4 -/

/-- Lemma 5.4 (Remaining errors), PDF p.22 (printed p.21). `A`, then `C`, are sufficiently large.
(`A₀ = 20` is what the expectation bound `expU_Z_le` needs; see the note there.) -/
theorem lemma_5_4 :
    ∃ A₀ : ℕ, ∀ A ≥ A₀, ∃ C₀ : ℕ, ∀ C ≥ C₀, ∀ (n lam N X Y : ℕ),
      let P : HintParams := ⟨A, C, n, lam⟩
      P.NodeArgs N X Y → P.NonLeaf N X Y →
      ∀ x J : Finset ℕ, Node.Valid N X Y x J →
        let sch := P.scheme N X Y
        expU (fun lr : sch.LocalSeed => (sch.Z lr x J : ℝ)) ≤
            P.eta * ((HintParams.D N X Y : ℝ) + 1) ∧
        prU (fun lr : sch.LocalSeed => P.resid N X Y < sch.Z lr x J) ≤
            ((2 : ℝ) ^ P.lamStar)⁻¹ := by
  refine ⟨20, fun A hA' => ⟨max (1000 * A + 1000) 2000, fun C hC' => ?_⟩⟩
  have hC₀ : 1000 * A + 1000 ≤ C := le_trans (le_max_left _ _) hC'
  have hC2000 : 2000 ≤ C := le_trans (le_max_right _ _) hC'
  intro n lam N X Y
  dsimp only
  intro hargs hnl x J hvalid
  have hA1 : 1 ≤ A := by omega
  have hmass : ∀ x J : Finset ℕ, Node.Valid N X Y x J →
      expU (fun π : Equiv.Perm (Fin N) => (({ A := A, C := C, n := n, lam := lam } : HintParams).overloadedMass N X Y π x J : ℝ)) ≤
        (HintParams.D N X Y : ℝ) * ({ A := A, C := C, n := n, lam := lam } : HintParams).eta ^ 2 :=
    fun x J h => claim2 ⟨A, C, n, lam⟩ N X Y hargs hnl hA1 hC₀ x J h
  have h1 := expU_Z_le ⟨A, C, n, lam⟩ N X Y hargs hnl hA' hmass x J hvalid
  exact ⟨h1, prU_Z_gt_resid ⟨A, C, n, lam⟩ N X Y hargs hnl hC2000
    (expU_Z_le ⟨A, C, n, lam⟩ N X Y hargs hnl hA' hmass) x J hvalid⟩

end LinearSetReconciliation327.Main

open LinearSetReconciliation327.Main in
/-- Lemma 5.4 (Remaining errors), PDF p.22 (printed p.21). `A`, then `C`, are sufficiently large. -/
theorem solution :
    ∃ A₀ : ℕ, ∀ A ≥ A₀, ∃ C₀ : ℕ, ∀ C ≥ C₀, ∀ (n lam N X Y : ℕ),
      let P : HintParams := ⟨A, C, n, lam⟩
      P.NodeArgs N X Y → P.NonLeaf N X Y →
      ∀ x J : Finset ℕ, Node.Valid N X Y x J →
        let sch := P.scheme N X Y
        expU (fun lr : sch.LocalSeed => (sch.Z lr x J : ℝ)) ≤
            P.eta * ((HintParams.D N X Y : ℝ) + 1) ∧
        prU (fun lr : sch.LocalSeed => P.resid N X Y < sch.Z lr x J) ≤
            ((2 : ℝ) ^ P.lamStar)⁻¹ :=
  LinearSetReconciliation327.Main.lemma_5_4


