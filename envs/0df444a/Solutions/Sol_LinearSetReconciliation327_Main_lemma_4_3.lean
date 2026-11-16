-- Prove2me | solution 1 for LinearSetReconciliation327.Main.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @djwj233
-- created : 2026-11-15T12:58:29.543492+00:00
-- url     : https://prove2.me/submissions/4a153425-130e-4113-9fbf-44bd67b9c64b

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic

open scoped ENNReal
open Finset

namespace LinearSetReconciliation327.Main

/-! ## Auxiliary lemmas for Lemma 4.3 (separation by random binary measurements) -/

/-- The finite space `(𝔽₂^q)^N` of binary `q`-bit measurements on `N` coordinates. -/
abbrev MeasSpace (N q : ℕ) := Fin N → Fin q → ZMod 2

/-- If two finite sets differ, some point lies in exactly one of them. -/
lemma exists_mem_xor {α : Type*} [DecidableEq α] {C S : Finset α} (h : C ≠ S) :
    ∃ v, (v ∈ C ∧ v ∉ S) ∨ (v ∈ S ∧ v ∉ C) := by
  by_contra hv
  apply h
  ext v
  constructor
  · intro hvc
    by_contra hvs
    exact absurd ⟨v, Or.inl ⟨hvc, hvs⟩⟩ hv
  · intro hvs
    by_contra hvc
    exact absurd ⟨v, Or.inr ⟨hvs, hvc⟩⟩ hv

/-- Sum of a vector supported at a single coordinate. -/
lemma sum_update_zero {ι : Type*} [DecidableEq ι] {G : Type*} [AddCommGroup G]
    (s : Finset ι) (v₀ : ι) (y : G) :
    (∑ v ∈ s, Function.update (0 : ι → G) v₀ y v) = if v₀ ∈ s then y else 0 := by
  classical
  by_cases hv : v₀ ∈ s
  · rw [if_pos hv]
    have h1 : (∑ v ∈ s, Function.update (0 : ι → G) v₀ y v)
        = Function.update (0 : ι → G) v₀ y v₀ :=
      Finset.sum_eq_single v₀ (fun b _ hb => by simp [hb])
        (fun hc => absurd hv hc)
    rw [h1, Function.update_self]
  · rw [if_neg hv]
    refine Finset.sum_eq_zero (fun b hb => ?_)
    have hbne : b ≠ v₀ := fun h => hv (h ▸ hb)
    simp [hbne]

/-- `prU` only depends on the truth set of the predicate. -/
lemma prU_congr {α : Type} [Fintype α] {P Q : α → Prop} (h : ∀ a, P a ↔ Q a) :
    prU P = prU Q := by
  classical
  have hf : Finset.univ.filter P = Finset.univ.filter Q := by
    ext a
    simp [h a]
  unfold prU
  rw [hf]

/-- Union bound for `prU`. -/
lemma prU_le_sum {α ι : Type} [Fintype α] [Nonempty α] (P : α → Prop)
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
    intro i _
    unfold prU
    rfl
  unfold prU
  calc ((Finset.univ.filter P).card : ℝ) / (Fintype.card α : ℝ)
      ≤ (∑ i ∈ s, ((Finset.univ.filter (Q i)).card : ℝ)) / (Fintype.card α : ℝ) := by
        apply (div_le_div_iff_of_pos_right hpos).mpr
        exact hcardR
    _ = ∑ i ∈ s, (((Finset.univ.filter (Q i)).card : ℝ) / (Fintype.card α : ℝ)) := by
        rw [Finset.sum_div]
    _ = ∑ i ∈ s, prU (Q i) := Finset.sum_congr rfl hterm

/-- The linear map `β ↦ ∑_{v∈C} β v - ∑_{v∈S} β v`. -/
def sumDiff (N q : ℕ) (C S : Finset (Fin N)) :
    MeasSpace N q →ₗ[ZMod 2] (Fin q → ZMod 2) where
  toFun β := ∑ v ∈ C, β v - ∑ v ∈ S, β v
  map_add' a b := by
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    abel
  map_smul' c a := by
    simp only [Pi.smul_apply, smul_sub, Finset.smul_sum, RingHom.id_apply]

@[simp] lemma sumDiff_apply (N q : ℕ) (C S : Finset (Fin N)) (β : MeasSpace N q) :
    sumDiff N q C S β = ∑ v ∈ C, β v - ∑ v ∈ S, β v := rfl

/-- `sumDiff` is surjective as soon as `C ≠ S`. -/
lemma sumDiff_surjective (N q : ℕ) {C S : Finset (Fin N)} (hCS : C ≠ S) :
    Function.Surjective (sumDiff N q C S) := by
  intro y
  obtain ⟨v₀, hv₀ | hv₀⟩ := exists_mem_xor hCS
  · refine ⟨Function.update (0 : MeasSpace N q) v₀ y, ?_⟩
    rw [sumDiff_apply]
    rw [sum_update_zero C v₀ y, sum_update_zero S v₀ y, if_pos hv₀.1, if_neg hv₀.2]
    simp
  · refine ⟨Function.update (0 : MeasSpace N q) v₀ (-y), ?_⟩
    rw [sumDiff_apply]
    rw [sum_update_zero C v₀ (-y), sum_update_zero S v₀ (-y), if_neg hv₀.2, if_pos hv₀.1]
    simp

/-- **Zero-fibre of a surjective linear map.** For a surjective `𝔽₂`-linear map the preimage of `0`
carries probability `1/|W|`. -/
lemma prU_ker_eq {V W : Type} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    [AddCommGroup W] [Module (ZMod 2) W] [Fintype W]
    (ψ : V →ₗ[ZMod 2] W) (hsurj : Function.Surjective ψ) :
    prU (fun x => ψ x = 0) = (Fintype.card W : ℝ)⁻¹ := by
  classical
  -- cardinality of the kernel
  have hker : Nat.card (LinearMap.ker ψ)
      = (Finset.univ.filter (fun x : V => ψ x = 0)).card := by
    rw [Nat.card_eq_fintype_card]
    rw [Fintype.card_subtype]
    try simp [LinearMap.mem_ker]
  -- cardinality of the quotient by the kernel
  have hquot : Nat.card (V ⧸ LinearMap.ker ψ) = Fintype.card W := by
    rw [Nat.card_congr (LinearMap.quotKerEquivRange ψ).toEquiv]
    rw [LinearMap.range_eq_top.mpr hsurj]
    rw [Nat.card_congr Submodule.topEquiv.toEquiv, Nat.card_eq_fintype_card]
  -- counting identity `|V| = |ker ψ| * |W|`
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
    have hmem : (0 : V) ∈ Finset.univ.filter (fun x : V => ψ x = 0) := by
      simp
    have hpos : 0 < (Finset.univ.filter (fun x : V => ψ x = 0)).card :=
      Finset.card_pos.mpr ⟨0, hmem⟩
    exact_mod_cast hpos.ne'
  have hW : (Fintype.card W : ℝ) ≠ 0 := by
    have hpos : 0 < Fintype.card W := Fintype.card_pos_iff.mpr ⟨0⟩
    exact_mod_cast hpos.ne'
  unfold prU
  rw [hcast]
  field_simp

/-- Lemma 4.3 (Separation by random binary measurements), PDF p.17 (printed p.16). -/
theorem lemma_4_3 (N q : ℕ) (S : Finset (Fin N)) (A : Finset (Finset (Fin N))) :
    prU (fun β : Fin N → Fin q → ZMod 2 =>
        ∃ C ∈ A.erase S, ∑ v ∈ C, β v = ∑ v ∈ S, β v) ≤
      ((A.erase S).card : ℝ) * ((2 : ℝ) ^ q)⁻¹ := by
  classical
  -- the cardinality of `𝔽₂^q`
  have hcardH : (Fintype.card (Fin q → ZMod 2) : ℝ) = (2 : ℝ) ^ q := by
    rw [Fintype.card_fun, Fintype.card_fin, ZMod.card]
    push_cast
    ring
  -- every single event has probability `2^{-q}`
  have hsingle : ∀ C ∈ A.erase S,
      prU (fun β : Fin N → Fin q → ZMod 2 => ∑ v ∈ C, β v = ∑ v ∈ S, β v)
        = ((2 : ℝ) ^ q)⁻¹ := by
    intro C hC
    have hne : C ≠ S := (Finset.mem_erase.mp hC).1
    have hEq : prU (fun β : Fin N → Fin q → ZMod 2 => ∑ v ∈ C, β v = ∑ v ∈ S, β v)
        = prU (fun β : Fin N → Fin q → ZMod 2 => sumDiff N q C S β = 0) :=
      prU_congr (fun β => by rw [sumDiff_apply, sub_eq_zero])
    rw [hEq, prU_ker_eq (sumDiff N q C S) (sumDiff_surjective N q hne), hcardH]
  -- union bound
  have hub := prU_le_sum
    (P := fun β : Fin N → Fin q → ZMod 2 =>
      ∃ C ∈ A.erase S, ∑ v ∈ C, β v = ∑ v ∈ S, β v)
    (s := A.erase S) (Q := fun C β => ∑ v ∈ C, β v = ∑ v ∈ S, β v)
    (fun _ hβ => hβ)
  calc prU (fun β : Fin N → Fin q → ZMod 2 =>
        ∃ C ∈ A.erase S, ∑ v ∈ C, β v = ∑ v ∈ S, β v)
      ≤ ∑ C ∈ A.erase S,
          prU (fun β : Fin N → Fin q → ZMod 2 => ∑ v ∈ C, β v = ∑ v ∈ S, β v) := hub
    _ = ∑ C ∈ A.erase S, ((2 : ℝ) ^ q)⁻¹ := Finset.sum_congr rfl hsingle
    _ = ((A.erase S).card : ℝ) * ((2 : ℝ) ^ q)⁻¹ := by
        rw [Finset.sum_const, nsmul_eq_mul]

end LinearSetReconciliation327.Main

open LinearSetReconciliation327.Main in
/-- Lemma 4.3 (Separation by random binary measurements) — submission wrapper. -/
theorem solution (N q : ℕ) (S : Finset (Fin N)) (A : Finset (Finset (Fin N))) :
    prU (fun β : Fin N → Fin q → ZMod 2 =>
        ∃ C ∈ A.erase S, ∑ v ∈ C, β v = ∑ v ∈ S, β v) ≤
      ((A.erase S).card : ℝ) * ((2 : ℝ) ^ q)⁻¹ :=
  LinearSetReconciliation327.Main.lemma_4_3 N q S A