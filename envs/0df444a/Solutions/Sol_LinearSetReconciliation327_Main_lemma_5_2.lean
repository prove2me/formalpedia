-- Prove2me | solution 1 for LinearSetReconciliation327.Main.lemma_5_2
-- status  : ACCEPTED   (prove)
-- author  : @djwj233
-- created : 2026-11-15T13:52:17.617627+00:00
-- url     : https://prove2.me/submissions/f89c133a-8a6d-47c1-ad18-315aeb1b4e08

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_Framework
import Definitions.Def_LinearSetReconciliation327_Main_HintSketch

open scoped ENNReal
open Finset

namespace LinearSetReconciliation327.Main

/-! ## Generic probability helpers -/

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

/-- For a fixed candidate support `C ≠ S`, the probability that the first `a` row measurements of `C`
and `S` agree is `2^{-a}`, provided both lie in `range Nj` with `Nj ≤ K`. -/
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

/-- The list form of the union-bound separation estimate. -/
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

/-! ## The structural analysis of one row worker -/

/-- If no wrong candidate with at most `y` outside-hint positions matches the prefix, the worker
predicts the true bit. -/
theorem wp_correct
    {ℓ K N m : ℕ} {BX BY cc : ℕ} {j : Fin m} {β : Fin ℓ → Fin K → ZMod 2}
    {Jj S : Finset ℕ} {z : List (ZMod 2)} {a : ℕ}
    (hz : z = (List.take a (List.finRange ℓ)).map (HintParams.rowBit β S))
    (hzl : z.length = a)
    (haL : a < ℓ)
    (hSn : S ⊆ range (rowLen N m j.val))
    (hBX : ¬ BX < Jj.card)
    (hyBY : (S \ Jj).card ≤ BY)
    (hyNj : (S \ Jj).card ≤ rowLen N m j.val - Jj.card)
    (hσa : HintParams.sigma Jj.card (rowLen N m j.val) (S \ Jj).card + cc ≤ a)
    (hnobad : ∀ C ∈ (range (rowLen N m j.val)).powerset, (C \ Jj).card ≤ (S \ Jj).card →
        (List.take a (List.finRange ℓ)).map (HintParams.rowBit β C)
          = (List.take a (List.finRange ℓ)).map (HintParams.rowBit β S) → C = S) :
    HintParams.workerPredict N m ℓ K BX BY cc j β Jj z
      = some (HintParams.rowBit β S ⟨a, haL⟩) := by
  classical
  set Nj := rowLen N m j.val with hNj
  set y := (S \ Jj).card with hy
  have hyBY' : y ≤ BY := by rw [hy]; exact hyBY
  have hyNj' : y ≤ Nj - Jj.card := by rw [hy, hNj]; exact hyNj
  have htake : List.take z.length (List.finRange ℓ) = List.take a (List.finRange ℓ) := by rw [hzl]
  have hp_eq : (List.take a (List.finRange ℓ)).map (HintParams.rowBit β S) = z := hz.symm
  have hSfam : S ∈ HintParams.family Nj β Jj y z := by
    simp only [HintParams.family, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hSn, by rw [hy], by rw [htake, hp_eq]⟩
  have hfam1 : (HintParams.family Nj β Jj y z).card = 1 := by
    have hsub : HintParams.family Nj β Jj y z ⊆ {S} := by
      intro C hC
      simp only [HintParams.family, Finset.mem_filter, Finset.mem_powerset] at hC
      obtain ⟨hCsub, hCcard, hCpre⟩ := hC
      rw [htake] at hCpre
      have hle : (C \ Jj).card ≤ (S \ Jj).card := by rw [hCcard, hy]
      have hpre : (List.take a (List.finRange ℓ)).map (HintParams.rowBit β C)
          = (List.take a (List.finRange ℓ)).map (HintParams.rowBit β S) := by
        rw [hCpre, hp_eq]
      rw [hnobad C (Finset.mem_powerset.mpr hCsub) hle hpre]
      simp
    have h2 := Finset.card_le_card hsub
    rw [Finset.card_singleton] at h2
    have h3 := Finset.card_pos.mpr ⟨S, hSfam⟩
    omega
  have hp : (fun r => decide (HintParams.sigma Jj.card Nj r + cc ≤ z.length ∧
      (HintParams.family Nj β Jj r z).card = 1)) y = true := by
    rw [decide_eq_true_iff]
    exact ⟨by rw [hzl, hy]; exact hσa, hfam1⟩
  have hlt0 : ∀ r < y, (fun r => decide (HintParams.sigma Jj.card Nj r + cc ≤ z.length ∧
      (HintParams.family Nj β Jj r z).card = 1)) r = false := by
    intro r hr
    rw [decide_eq_false_iff_not]
    rintro ⟨-, hcard⟩
    obtain ⟨C₀, hC₀⟩ := Finset.card_eq_one.mp hcard
    have hC₀mem : C₀ ∈ HintParams.family Nj β Jj r z := by rw [hC₀]; simp
    simp only [HintParams.family, Finset.mem_filter, Finset.mem_powerset] at hC₀mem
    obtain ⟨hCsub, hCcard, hCpre⟩ := hC₀mem
    rw [htake] at hCpre
    have hle : (C₀ \ Jj).card ≤ (S \ Jj).card := by rw [hCcard, ← hy]; exact Nat.le_of_lt hr
    have hpre : (List.take a (List.finRange ℓ)).map (HintParams.rowBit β C₀)
        = (List.take a (List.finRange ℓ)).map (HintParams.rowBit β S) := by
      rw [hCpre, hp_eq]
    have hCS : C₀ = S := hnobad C₀ (Finset.mem_powerset.mpr hCsub) hle hpre
    rw [hCS, ← hy] at hCcard
    omega
  have hlt : ∀ r < y, (!(fun r => decide (HintParams.sigma Jj.card Nj r + cc ≤ z.length ∧
      (HintParams.family Nj β Jj r z).card = 1)) r) = true := by
    intro r hr
    rw [hlt0 r hr]
    rfl
  have hfind : (List.range (min BY (Nj - Jj.card) + 1)).find? (fun r =>
      decide (HintParams.sigma Jj.card Nj r + cc ≤ z.length ∧
        (HintParams.family Nj β Jj r z).card = 1)) = some y := by
    rw [List.find?_range_eq_some]
    exact ⟨hp, List.mem_range.mpr (by omega), hlt⟩
  have hfam : HintParams.family Nj β Jj y z = {S} := by
    obtain ⟨C₀, hC₀⟩ := Finset.card_eq_one.mp hfam1
    have hC₀S : S = C₀ := by
      have hmem : S ∈ ({C₀} : Finset (Finset ℕ)) := hC₀ ▸ hSfam
      simpa using hmem
    rw [hC₀, ← hC₀S]
  rw [HintParams.workerPredict]
  try simp only []
  rw [if_neg hBX]
  try simp only []
  rw [hfind]
  try simp only []
  rw [dif_pos (by omega : z.length < ℓ)]
  rw [hfam, toList_head?_singleton_map]
  simp only [Option.some_inj]
  congr 1
  exact Fin.ext hzl

/-- If the worker returns `⊥` although the true support was in reach, some wrong candidate with at
most `y` outside-hint positions matches the prefix. -/
theorem wp_none_bad
    {ℓ K N m : ℕ} {BX BY cc : ℕ} {j : Fin m} {β : Fin ℓ → Fin K → ZMod 2}
    {Jj S : Finset ℕ} {z : List (ZMod 2)} {a : ℕ}
    (haL : a < ℓ)
    (hz : z = (List.take a (List.finRange ℓ)).map (HintParams.rowBit β S))
    (hzl : z.length = a)
    (hSn : S ⊆ range (rowLen N m j.val))
    (hBX : ¬ BX < Jj.card)
    (hyBY : (S \ Jj).card ≤ BY)
    (hyNj : (S \ Jj).card ≤ rowLen N m j.val - Jj.card)
    (hσa : HintParams.sigma Jj.card (rowLen N m j.val) (S \ Jj).card + cc ≤ a)
    (hnone : HintParams.workerPredict N m ℓ K BX BY cc j β Jj z = none) :
    ∃ C ∈ candSet (rowLen N m j.val) Jj (S \ Jj).card, C ≠ S ∧
      (List.take a (List.finRange ℓ)).map (HintParams.rowBit β C)
        = (List.take a (List.finRange ℓ)).map (HintParams.rowBit β S) := by
  classical
  set Nj := rowLen N m j.val with hNj
  set y := (S \ Jj).card with hy
  have htake : List.take z.length (List.finRange ℓ) = List.take a (List.finRange ℓ) := by rw [hzl]
  have hp_eq : (List.take a (List.finRange ℓ)).map (HintParams.rowBit β S) = z := hz.symm
  have hSfam : S ∈ HintParams.family Nj β Jj y z := by
    simp only [HintParams.family, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hSn, by rw [hy], by rw [htake, hp_eq]⟩
  rw [HintParams.workerPredict] at hnone
  try simp only [] at hnone
  rw [if_neg hBX] at hnone
  try simp only [] at hnone
  rcases hf : (List.range (min BY (Nj - Jj.card) + 1)).find? (fun r =>
      decide (HintParams.sigma Jj.card Nj r + cc ≤ z.length ∧
        (HintParams.family Nj β Jj r z).card = 1)) with _ | r
  · have hfalse : (fun r => decide (HintParams.sigma Jj.card Nj r + cc ≤ z.length ∧
        (HintParams.family Nj β Jj r z).card = 1)) y = false := by
      have hnot := (List.find?_eq_none.mp hf) y (List.mem_range.mpr (by omega))
      cases hb : (fun r => decide (HintParams.sigma Jj.card Nj r + cc ≤ z.length ∧
          (HintParams.family Nj β Jj r z).card = 1)) y
      · rfl
      · exact absurd hb hnot
    rw [decide_eq_false_iff_not] at hfalse
    have hge2 : 1 < (HintParams.family Nj β Jj y z).card := by
      have hpos := Finset.card_pos.mpr ⟨S, hSfam⟩
      have hne1 : (HintParams.family Nj β Jj y z).card ≠ 1 :=
        fun h1 => hfalse ⟨by rw [hzl, hy]; exact hσa, h1⟩
      omega
    have hw : ∃ C ∈ HintParams.family Nj β Jj y z, C ≠ S := by
      by_contra hh
      have hh' : ∀ C, C ∈ HintParams.family Nj β Jj y z → C = S := by
        intro C hC
        by_contra hne
        exact hh ⟨C, hC, hne⟩
      have hsub : HintParams.family Nj β Jj y z ⊆ {S} := fun C hC => by
        simp [hh' C hC]
      have h2 := Finset.card_le_card hsub
      rw [Finset.card_singleton] at h2
      omega
    obtain ⟨C, hCmem, hCS⟩ := hw
    simp only [HintParams.family, Finset.mem_filter, Finset.mem_powerset] at hCmem
    obtain ⟨hCsub, hCcard, hCpre⟩ := hCmem
    rw [htake] at hCpre
    refine ⟨C, ?_, hCS, ?_⟩
    · simp only [candSet, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hCsub, by rw [hCcard, hy]⟩
    · rw [hCpre, hp_eq]
  · rw [hf] at hnone
    try simp only [] at hnone
    rw [dif_pos (by omega : z.length < ℓ)] at hnone
    have hp : (fun r => decide (HintParams.sigma Jj.card Nj r + cc ≤ z.length ∧
        (HintParams.family Nj β Jj r z).card = 1)) r = true :=
      (List.find?_range_eq_some.mp hf).1
    rw [decide_eq_true_iff] at hp
    obtain ⟨-, hcard1⟩ := hp
    have hcard0 : (HintParams.family Nj β Jj r z).card = 0 := by
      have hnil : (HintParams.family Nj β Jj r z).toList = [] := by
        cases htl : (HintParams.family Nj β Jj r z).toList with
        | nil => rfl
        | cons a l =>
          rw [htl] at hnone
          exact absurd hnone (by simp)
      rw [← Finset.length_toList, hnil]
      rfl
    omega

/-- If the worker predicts a wrong bit, the qualifying candidate came from a family whose index is
within the `σ + c ≤ a` budget. -/
theorem wp_wrong_elig
    {ℓ K N m : ℕ} {BX BY cc : ℕ} {j : Fin m} {β : Fin ℓ → Fin K → ZMod 2}
    {Jj S : Finset ℕ} {z : List (ZMod 2)} {a : ℕ}
    (haL : a < ℓ)
    (hz : z = (List.take a (List.finRange ℓ)).map (HintParams.rowBit β S))
    (hzl : z.length = a)
    (hwr : ∃ b, HintParams.workerPredict N m ℓ K BX BY cc j β Jj z = some b ∧
      b ≠ HintParams.rowBit β S ⟨a, haL⟩) :
    ∃ C ∈ (range (rowLen N m j.val)).powerset, C ≠ S ∧
      (C \ Jj).card ∈ (range (min BY (rowLen N m j.val - Jj.card) + 1)).filter
          (fun r => HintParams.sigma Jj.card (rowLen N m j.val) r + cc ≤ a) ∧
      (List.take a (List.finRange ℓ)).map (HintParams.rowBit β C)
        = (List.take a (List.finRange ℓ)).map (HintParams.rowBit β S) := by
  classical
  set Nj := rowLen N m j.val with hNj
  obtain ⟨b, hb, hbne⟩ := hwr
  have htake : List.take z.length (List.finRange ℓ) = List.take a (List.finRange ℓ) := by rw [hzl]
  rw [HintParams.workerPredict] at hb
  try simp only [] at hb
  by_cases hBX : BX < Jj.card
  · rw [if_pos hBX] at hb
    simp at hb
  · rw [if_neg hBX] at hb
    try simp only [] at hb
    rcases hf : (List.range (min BY (Nj - Jj.card) + 1)).find? (fun r =>
        decide (HintParams.sigma Jj.card Nj r + cc ≤ z.length ∧
          (HintParams.family Nj β Jj r z).card = 1)) with _ | r
    · rw [hf] at hb
      simp only [] at hb
      simp at hb
    · rw [hf] at hb
      try simp only [] at hb
      by_cases hlt : z.length < ℓ
      · rw [dif_pos hlt] at hb
        rw [Option.map_eq_some_iff] at hb
        obtain ⟨C, hChead, hCb⟩ := hb
        have hCmem : C ∈ HintParams.family Nj β Jj r z :=
          Finset.mem_toList.mp (List.mem_of_mem_head? hChead)
        obtain ⟨hp, hrmem, -⟩ := List.find?_range_eq_some.mp hf
        rw [decide_eq_true_iff] at hp
        obtain ⟨hσr, -⟩ := hp
        simp only [HintParams.family, Finset.mem_filter, Finset.mem_powerset] at hCmem
        obtain ⟨hCsub, hCcard, hCpre⟩ := hCmem
        rw [htake] at hCpre
        have hCS : C ≠ S := by
          intro hCS
          rw [hCS] at hCb
          exact hbne (by rw [← hCb]; congr 1; exact Fin.ext hzl)
        refine ⟨C, Finset.mem_powerset.mpr hCsub, hCS, ?_, ?_⟩
        · rw [hCcard]
          refine Finset.mem_filter.mpr ⟨?_, ?_⟩
          · rw [Finset.mem_range]
            exact List.mem_range.mp hrmem
          · rw [hzl] at hσr; exact hσr
        · rw [hCpre, hz]
      · rw [dif_neg hlt] at hb
        simp at hb

/-! ## The cardinality of the qualifying family -/

/-- The family of supports whose index qualifies for the `σ + c ≤ a` budget has at most
`2^{a-c}` elements. -/
theorem card_elig_le {Nj cc a BY : ℕ} (Jj : Finset ℕ) (hJj : Jj ⊆ range Nj) :
    let Ae := (range Nj).powerset.filter (fun C => (C \ Jj).card ∈
        (range (min BY (Nj - Jj.card) + 1)).filter
          (fun r => HintParams.sigma Jj.card Nj r + cc ≤ a))
    (Ae.card : ℝ) ≤ (2 : ℝ) ^ ((a : ℝ) - (cc : ℝ)) := by
  classical
  dsimp only
  set R' : Finset ℕ := (range (min BY (Nj - Jj.card) + 1)).filter
      (fun r => HintParams.sigma Jj.card Nj r + cc ≤ a) with hR'
  set Ae : Finset (Finset ℕ) := (range Nj).powerset.filter (fun C => (C \ Jj).card ∈ R') with hAe
  by_cases hne : R'.Nonempty
  · set Rmax := R'.max' hne with hRmax
    have hRmaxmem : Rmax ∈ R' := Finset.max'_mem R' hne
    have hRmaxle : ∀ r ∈ R', r ≤ Rmax := fun r hr => Finset.le_max' R' r hr
    have hσR : HintParams.sigma Jj.card Nj Rmax + cc ≤ a :=
      (Finset.mem_filter.mp hRmaxmem).2
    have hsub : Ae ⊆ candSet Nj Jj Rmax := by
      intro C hC
      simp only [hAe, candSet, Finset.mem_filter, Finset.mem_powerset] at hC ⊢
      exact ⟨hC.1, hRmaxle _ hC.2⟩
    have h1 : (Ae.card : ℝ) ≤ ((candSet Nj Jj Rmax).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have h2 : ((candSet Nj Jj Rmax).card : ℝ)
        ≤ (2 : ℝ) ^ (HintParams.sigma Jj.card Nj Rmax : ℝ) :=
      card_candidates_le_two_pow_sigma Jj hJj Rmax
    have h3 : (2 : ℝ) ^ (HintParams.sigma Jj.card Nj Rmax : ℝ)
        ≤ (2 : ℝ) ^ ((a : ℝ) - (cc : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have h4 : (HintParams.sigma Jj.card Nj Rmax : ℝ) + (cc : ℝ) ≤ (a : ℝ) := by
        exact_mod_cast hσR
      linarith
    exact le_trans h1 (le_trans h2 h3)
  · have hempty : R' = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun x hx => hne ⟨x, hx⟩)
    have hAe0 : Ae = ∅ := by
      rw [hAe, hempty]
      simp
    rw [hAe0, Finset.card_empty, Nat.cast_zero]
    positivity


/-! ## Lemma 5.2 -/

/-- Lemma 5.2, PDF p.21 (printed p.20): for a regular row of a non-leaf node, after `a < ℓ` recovered
bits of the true transcript. The probability is over the coins of the row. -/
theorem lemma_5_2 (P : HintParams) (N X Y : ℕ) (hargs : P.NodeArgs N X Y) (hnl : P.NonLeaf N X Y)
    (j : Fin (P.rows X Y)) (Jj Sj : Finset ℕ)
    (hJj : Jj ⊆ range (rowLen N (P.rows X Y) j.val)) (hSj : Sj ⊆ range (rowLen N (P.rows X Y) j.val))
    (hreg : ¬ P.Overloaded N X Y Jj Sj) (a : Fin (P.ell N X Y)) :
    let sch := P.scheme N X Y
    let σ : ℝ := (HintParams.sigma Jj.card (rowLen N (P.rows X Y) j.val) (Sj \ Jj).card : ℝ)
    let c : ℝ := (P.c N X Y : ℝ)
    let q : sch.Rand → Option (ZMod 2) := fun β =>
      sch.predict j β Jj (sch.truePrefix j β Sj a.val)
    prU (fun β : sch.Rand => q β = none) ≤ G a.val (σ + c) ∧
    prU (fun β : sch.Rand => ∃ b, q β = some b ∧ b ≠ sch.code j β Sj a) ≤
      ((2 : ℝ) ^ (P.c N X Y))⁻¹ * G a.val (σ + c) := by
  classical
  dsimp only
  set Nj := rowLen N (P.rows X Y) j.val with hNj
  set cc : ℕ := P.c N X Y with hcc
  set σn : ℕ := HintParams.sigma Jj.card Nj (Sj \ Jj).card with hσn
  -- basic numeric facts
  have hm1 : 1 ≤ P.rows X Y := rows_pos P N X Y hargs hnl
  have hNK : Nj ≤ P.Nmax N X Y := by rw [hNj]; exact rowLen_le_Nmax N (P.rows X Y) j.val hm1
  have hJcard : Jj.card ≤ P.BX N X Y := by
    by_contra hh
    exact hreg (Or.inl (by omega))
  have hyBY : (Sj \ Jj).card ≤ P.BY N X Y := by
    by_contra hh
    exact hreg (Or.inr (by omega))
  have hyNj : (Sj \ Jj).card ≤ Nj - Jj.card := by
    have hsub : Sj \ Jj ⊆ range Nj \ Jj := by
      intro x hx
      exact Finset.mem_sdiff.mpr ⟨hSj (Finset.mem_sdiff.mp hx).1, (Finset.mem_sdiff.mp hx).2⟩
    calc (Sj \ Jj).card ≤ (range Nj \ Jj).card := Finset.card_le_card hsub
      _ = Nj - Jj.card := by
          rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hJj, Finset.card_range]
  -- the true prefix
  have hzdef : ∀ β : (P.scheme N X Y).Rand,
      (P.scheme N X Y).truePrefix j β Sj a.val
        = (List.take a.val (List.finRange (P.ell N X Y))).map (HintParams.rowBit β Sj) :=
    fun β => rfl
  have hzlen : ∀ β : (P.scheme N X Y).Rand,
      ((P.scheme N X Y).truePrefix j β Sj a.val).length = a.val := by
    intro β
    rw [hzdef β, List.length_map, List.length_take, List.length_finRange,
      Nat.min_eq_left (le_of_lt a.isLt)]
  -- the two candidate families
  set Ah1 : Finset (Finset ℕ) := candSet Nj Jj (Sj \ Jj).card with hAh1
  set R' : Finset ℕ := (range (min (P.BY N X Y) (Nj - Jj.card) + 1)).filter
      (fun r => HintParams.sigma Jj.card Nj r + cc ≤ a.val) with hR'
  set Ae : Finset (Finset ℕ) := (range Nj).powerset.filter (fun C => (C \ Jj).card ∈ R') with hAe
  -- the bad events
  have hbad1 : ∀ β : (P.scheme N X Y).Rand, σn + cc ≤ a.val →
      (P.scheme N X Y).predict j β Jj ((P.scheme N X Y).truePrefix j β Sj a.val) = none ∨
      (∃ b, (P.scheme N X Y).predict j β Jj ((P.scheme N X Y).truePrefix j β Sj a.val) = some b ∧
        b ≠ (P.scheme N X Y).code j β Sj a) →
      (∃ C ∈ Ah1.erase Sj, (List.take a.val (List.finRange (P.ell N X Y))).map
          (HintParams.rowBit β C)
        = (List.take a.val (List.finRange (P.ell N X Y))).map (HintParams.rowBit β Sj)) := by
    intro β hσa hcase
    have hσa' : HintParams.sigma Jj.card (rowLen N (P.rows X Y) j.val) (Sj \ Jj).card + cc
        ≤ a.val := hσa
    rcases hcase with hnone | ⟨b, hb, hbne⟩
    · obtain ⟨C, hCmem, hCS, hCmat⟩ :=
        wp_none_bad (haL := a.isLt) (hz := hzdef β) (hzl := hzlen β) hSj (by omega : ¬ P.BX N X Y < Jj.card) hyBY hyNj hσa' hnone
      refine ⟨C, Finset.mem_erase.mpr ⟨hCS, ?_⟩, hCmat⟩
      rwa [hAh1]
    · by_contra hno
      have hgood : ∀ C ∈ (range (rowLen N (P.rows X Y) j.val)).powerset,
          (C \ Jj).card ≤ (Sj \ Jj).card →
          (List.take a.val (List.finRange (P.ell N X Y))).map (HintParams.rowBit β C)
            = (List.take a.val (List.finRange (P.ell N X Y))).map (HintParams.rowBit β Sj) →
          C = Sj := by
        intro C hCpow hCcard hCmat
        by_contra hCS
        exact hno ⟨C, Finset.mem_erase.mpr ⟨hCS, by
          rw [hAh1]
          exact Finset.mem_filter.mpr ⟨hCpow, hCcard⟩⟩, hCmat⟩
      have hq := wp_correct (haL := a.isLt) (hz := hzdef β) (hzl := hzlen β) hSj
        (by omega : ¬ P.BX N X Y < Jj.card) hyBY hyNj hσa' hgood
      have hq' : (P.scheme N X Y).predict j β Jj ((P.scheme N X Y).truePrefix j β Sj a.val)
          = some ((P.scheme N X Y).code j β Sj a) := hq
      rw [hq'] at hb
      exact hbne (by simpa using hb.symm)
  -- the second bad event
  have hbad2 : ∀ β : (P.scheme N X Y).Rand,
      (∃ b, (P.scheme N X Y).predict j β Jj ((P.scheme N X Y).truePrefix j β Sj a.val) = some b ∧
        b ≠ (P.scheme N X Y).code j β Sj a) →
      (∃ C ∈ Ae.erase Sj, (List.take a.val (List.finRange (P.ell N X Y))).map
          (HintParams.rowBit β C)
        = (List.take a.val (List.finRange (P.ell N X Y))).map (HintParams.rowBit β Sj)) := by
    intro β hwr
    have hwr' : ∃ b, HintParams.workerPredict N (P.rows X Y) (P.ell N X Y) (P.Nmax N X Y)
        (P.BX N X Y) (P.BY N X Y) (P.c N X Y) j β Jj
        ((P.scheme N X Y).truePrefix j β Sj a.val) = some b ∧
        b ≠ HintParams.rowBit β Sj ⟨a.val, a.isLt⟩ := by
      obtain ⟨b, hb, hbne⟩ := hwr
      exact ⟨b, hb, fun hcontra => hbne hcontra⟩
    obtain ⟨C, hCpow, hCS, hCidx, hCmat⟩ :=
      wp_wrong_elig (haL := a.isLt) (hz := hzdef β) (hzl := hzlen β) hwr'
    refine ⟨C, Finset.mem_erase.mpr ⟨hCS, ?_⟩, hCmat⟩
    rw [hAe]
    exact Finset.mem_filter.mpr ⟨hCpow, hCidx⟩
  -- cardinality bounds
  have hAh1card : ((Ah1.erase Sj).card : ℝ) ≤ (2:ℝ)^(σn:ℝ) := by
    have h1 : ((Ah1.erase Sj).card : ℝ) ≤ (Ah1.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.erase_subset Sj Ah1)
    have h2 : (Ah1.card : ℝ) ≤ (2:ℝ)^(σn:ℝ) := by
      rw [hAh1]
      exact card_candidates_le_two_pow_sigma Jj hJj (Sj \ Jj).card
    exact le_trans h1 h2
  have hAecard : ((Ae.erase Sj).card : ℝ) ≤ (2:ℝ)^((a.val:ℝ) - (cc:ℝ)) := by
    have h1 : ((Ae.erase Sj).card : ℝ) ≤ (Ae.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.erase_subset Sj Ae)
    have h2 : (Ae.card : ℝ) ≤ (2:ℝ)^((a.val:ℝ) - (cc:ℝ)) := by
      have h3 := card_elig_le (Nj := Nj) (cc := cc) (a := a.val) (BY := P.BY N X Y) Jj hJj
      simpa only [hAe, hR'] using h3
    exact le_trans h1 h2
  -- the probabilities of the bad events
  have hpowpos : (0:ℝ) < ((2:ℝ)^((a.val:ℝ)))⁻¹ := by
    apply inv_pos.mpr
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hPr1 : prU (fun β : (P.scheme N X Y).Rand =>
      ∃ C ∈ Ah1.erase Sj, (List.take a.val (List.finRange (P.ell N X Y))).map
          (HintParams.rowBit β C)
        = (List.take a.val (List.finRange (P.ell N X Y))).map (HintParams.rowBit β Sj))
      ≤ ((2:ℝ)^(σn:ℝ)) * ((2:ℝ)^(a.val:ℝ))⁻¹ := by
    refine le_trans (prU_exists_prefix_eq_list (ℓ := P.ell N X Y) (K := P.Nmax N X Y)
      (Nj := Nj) (a := a.val) (le_of_lt a.isLt) hNK hSj Ah1 ?_) ?_
    · intro C hC
      have := Finset.mem_filter.mp hC
      exact Finset.mem_powerset.mp this.1
    · exact mul_le_mul_of_nonneg_right hAh1card (le_of_lt hpowpos)
  have hPr2 : prU (fun β : (P.scheme N X Y).Rand =>
      ∃ C ∈ Ae.erase Sj, (List.take a.val (List.finRange (P.ell N X Y))).map
          (HintParams.rowBit β C)
        = (List.take a.val (List.finRange (P.ell N X Y))).map (HintParams.rowBit β Sj))
      ≤ ((2:ℝ)^((a.val:ℝ) - (cc:ℝ))) * ((2:ℝ)^(a.val:ℝ))⁻¹ := by
    refine le_trans (prU_exists_prefix_eq_list (ℓ := P.ell N X Y) (K := P.Nmax N X Y)
      (Nj := Nj) (a := a.val) (le_of_lt a.isLt) hNK hSj Ae ?_) ?_
    · intro C hC
      have := Finset.mem_filter.mp hC
      exact Finset.mem_powerset.mp this.1
    · exact mul_le_mul_of_nonneg_right hAecard (le_of_lt hpowpos)
  -- arithmetic
  have hA : ((2:ℝ)^(σn:ℝ)) * ((2:ℝ)^(a.val:ℝ))⁻¹ = (2:ℝ)^((σn:ℝ) - (a.val:ℝ)) := by
    rw [Real.rpow_sub (by norm_num), div_eq_mul_inv]
  have hB : ((2:ℝ)^((a.val:ℝ) - (cc:ℝ))) * ((2:ℝ)^(a.val:ℝ))⁻¹ = ((2:ℝ)^(cc:ℝ))⁻¹ := by
    have h1 : ((a.val:ℝ) - (cc:ℝ)) = (a.val:ℝ) + (-(cc:ℝ)) := by ring
    rw [h1, Real.rpow_add (by norm_num), Real.rpow_neg (show (0:ℝ) ≤ 2 by norm_num)]
    field_simp
  have hB' : a.val < σn + cc → ((2:ℝ)^(cc:ℝ))⁻¹ ≤ (2:ℝ)^((σn:ℝ) - (a.val:ℝ)) := by
    intro hlt
    calc ((2:ℝ)^(cc:ℝ))⁻¹ = (2:ℝ)^(-(cc:ℝ)) :=
          (Real.rpow_neg (show (0:ℝ) ≤ 2 by norm_num) _).symm
      _ ≤ (2:ℝ)^((σn:ℝ) - (a.val:ℝ)) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          have h4 : (a.val:ℝ) < (σn:ℝ) + (cc:ℝ) := by exact_mod_cast hlt
          linarith
  -- final assembly
  constructor
  · by_cases hcase : σn + cc ≤ a.val
    · have hmono : prU (fun β : (P.scheme N X Y).Rand =>
          (P.scheme N X Y).predict j β Jj ((P.scheme N X Y).truePrefix j β Sj a.val) = none)
          ≤ prU (fun β : (P.scheme N X Y).Rand =>
          ∃ C ∈ Ah1.erase Sj, (List.take a.val (List.finRange (P.ell N X Y))).map
              (HintParams.rowBit β C)
            = (List.take a.val (List.finRange (P.ell N X Y))).map (HintParams.rowBit β Sj)) :=
        prU_mono' (fun β hnone => hbad1 β hcase (Or.inl hnone))
      calc prU (fun β : (P.scheme N X Y).Rand =>
            (P.scheme N X Y).predict j β Jj ((P.scheme N X Y).truePrefix j β Sj a.val) = none)
          ≤ (2:ℝ)^((σn:ℝ) - (a.val:ℝ)) := le_trans hmono (le_trans hPr1 (le_of_eq hA))
        _ ≤ G a.val ((σn:ℝ) + (cc:ℝ)) := by
            rw [G]
            apply le_min
            · have hz : (σn:ℝ) - (a.val:ℝ) ≤ 0 := by
                have h1 : (σn:ℝ) + (cc:ℝ) ≤ (a.val:ℝ) := by exact_mod_cast hcase
                have h2 : (0:ℝ) ≤ (cc:ℝ) := Nat.cast_nonneg cc
                linarith
              calc (2:ℝ)^((σn:ℝ) - (a.val:ℝ)) ≤ (2:ℝ)^(0:ℝ) :=
                    Real.rpow_le_rpow_of_exponent_le (by norm_num) hz
                _ = 1 := Real.rpow_zero 2
            · apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
              have h2 : (0:ℝ) ≤ (cc:ℝ) := Nat.cast_nonneg cc
              linarith
    · have hcase' : a.val < σn + cc := by omega
      calc prU (fun β : (P.scheme N X Y).Rand =>
            (P.scheme N X Y).predict j β Jj ((P.scheme N X Y).truePrefix j β Sj a.val) = none)
          ≤ 1 := prU_le_one _
        _ = G a.val ((σn:ℝ) + (cc:ℝ)) := by
            rw [G]
            have hlt' : (a.val:ℝ) < (σn:ℝ) + (cc:ℝ) := by exact_mod_cast hcase'
            have hz : (0:ℝ) ≤ (σn:ℝ) + (cc:ℝ) - (a.val:ℝ) := by linarith
            have hone : (1:ℝ) ≤ (2:ℝ)^((σn:ℝ) + (cc:ℝ) - (a.val:ℝ)) := by
              calc (1:ℝ) = (2:ℝ)^(0:ℝ) := (Real.rpow_zero 2).symm
                _ ≤ (2:ℝ)^((σn:ℝ) + (cc:ℝ) - (a.val:ℝ)) :=
                    Real.rpow_le_rpow_of_exponent_le (by norm_num) hz
            exact (min_eq_left hone).symm
  · have hmono2 : prU (fun β : (P.scheme N X Y).Rand =>
        ∃ b, (P.scheme N X Y).predict j β Jj ((P.scheme N X Y).truePrefix j β Sj a.val) = some b ∧
          b ≠ (P.scheme N X Y).code j β Sj a)
        ≤ prU (fun β : (P.scheme N X Y).Rand =>
        ∃ C ∈ Ae.erase Sj, (List.take a.val (List.finRange (P.ell N X Y))).map
            (HintParams.rowBit β C)
          = (List.take a.val (List.finRange (P.ell N X Y))).map (HintParams.rowBit β Sj)) :=
      prU_mono' (fun β hwr => hbad2 β hwr)
    have hle2 : prU (fun β : (P.scheme N X Y).Rand =>
        ∃ b, (P.scheme N X Y).predict j β Jj ((P.scheme N X Y).truePrefix j β Sj a.val) = some b ∧
          b ≠ (P.scheme N X Y).code j β Sj a)
        ≤ ((2:ℝ)^(cc:ℝ))⁻¹ := le_trans hmono2 (le_trans hPr2 (le_of_eq hB))
    have hle1 : prU (fun β : (P.scheme N X Y).Rand =>
        ∃ b, (P.scheme N X Y).predict j β Jj ((P.scheme N X Y).truePrefix j β Sj a.val) = some b ∧
          b ≠ (P.scheme N X Y).code j β Sj a)
        ≤ (2:ℝ)^((σn:ℝ) - (a.val:ℝ)) := by
      by_cases hcase : σn + cc ≤ a.val
      · have hmono1 : prU (fun β : (P.scheme N X Y).Rand =>
            ∃ b, (P.scheme N X Y).predict j β Jj ((P.scheme N X Y).truePrefix j β Sj a.val) = some b ∧
              b ≠ (P.scheme N X Y).code j β Sj a)
            ≤ prU (fun β : (P.scheme N X Y).Rand =>
            ∃ C ∈ Ah1.erase Sj, (List.take a.val (List.finRange (P.ell N X Y))).map
                (HintParams.rowBit β C)
              = (List.take a.val (List.finRange (P.ell N X Y))).map (HintParams.rowBit β Sj)) :=
          prU_mono' (fun β hwr => hbad1 β hcase (Or.inr hwr))
        exact le_trans hmono1 (le_trans hPr1 (le_of_eq hA))
      · have hcase' : a.val < σn + cc := by omega
        exact le_trans hle2 (hB' hcase')
    calc prU (fun β : (P.scheme N X Y).Rand =>
          ∃ b, (P.scheme N X Y).predict j β Jj ((P.scheme N X Y).truePrefix j β Sj a.val) = some b ∧
            b ≠ (P.scheme N X Y).code j β Sj a)
        ≤ min ((2:ℝ)^((σn:ℝ) - (a.val:ℝ))) ((2:ℝ)^(cc:ℝ))⁻¹ := le_min hle1 hle2
      _ = ((2:ℝ)^(P.c N X Y))⁻¹ * G a.val ((σn:ℝ) + (cc:ℝ)) := by
          have hnat : ((2:ℝ)^(P.c N X Y))⁻¹ = ((2:ℝ)^(cc:ℝ))⁻¹ := by
            rw [← hcc, ← Real.rpow_natCast]
          rw [hnat]
          have hG : ((2:ℝ)^(cc:ℝ))⁻¹ * G a.val ((σn:ℝ) + (cc:ℝ))
              = min ((2:ℝ)^((σn:ℝ) - (a.val:ℝ))) ((2:ℝ)^(cc:ℝ))⁻¹ := by
            rw [G, mul_min_of_nonneg (1:ℝ) _ (by positivity), mul_one]
            have hneg : ((2:ℝ)^(cc:ℝ))⁻¹ = (2:ℝ)^(-(cc:ℝ)) :=
              (Real.rpow_neg (show (0:ℝ) ≤ 2 by norm_num) _).symm
            rw [hneg, ← Real.rpow_add (by norm_num)]
            have harg : -(cc:ℝ) + ((σn:ℝ) + (cc:ℝ) - (a.val:ℝ)) = (σn:ℝ) - (a.val:ℝ) := by
              ring
            rw [harg, min_comm]
          exact hG.symm

end LinearSetReconciliation327.Main

open LinearSetReconciliation327.Main in
/-- Lemma 5.2 (row prediction) — submission wrapper matching the target statement. -/
theorem solution (P : HintParams) (N X Y : ℕ) (hargs : P.NodeArgs N X Y) (hnl : P.NonLeaf N X Y)
    (j : Fin (P.rows X Y)) (Jj Sj : Finset ℕ)
    (hJj : Jj ⊆ range (rowLen N (P.rows X Y) j.val)) (hSj : Sj ⊆ range (rowLen N (P.rows X Y) j.val))
    (hreg : ¬ P.Overloaded N X Y Jj Sj) (a : Fin (P.ell N X Y)) :
    let sch := P.scheme N X Y
    let σ : ℝ := (HintParams.sigma Jj.card (rowLen N (P.rows X Y) j.val) (Sj \ Jj).card : ℝ)
    let c : ℝ := (P.c N X Y : ℝ)
    let q : sch.Rand → Option (ZMod 2) := fun β =>
      sch.predict j β Jj (sch.truePrefix j β Sj a.val)
    prU (fun β : sch.Rand => q β = none) ≤ G a.val (σ + c) ∧
    prU (fun β : sch.Rand => ∃ b, q β = some b ∧ b ≠ sch.code j β Sj a) ≤
      ((2 : ℝ) ^ (P.c N X Y))⁻¹ * G a.val (σ + c) :=
  LinearSetReconciliation327.Main.lemma_5_2 P N X Y hargs hnl j Jj Sj hJj hSj hreg a