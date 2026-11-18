-- Prove2me | solution 1 for HILL.PRG.flat_conditional_leftover_hash
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-18T00:46:53.669505+00:00
-- url     : https://prove2.me/submissions/75eb36ad-8007-41b1-bb8c-21b8c0e23d21

import Definitions.Def_HILL_PRG_Model
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

open HILL.PRG
open scoped BigOperators

namespace HILL.PRG.FlatConditionalSubmission

section
variable {α β κ ζ : Type*}
variable [DecidableEq α] [DecidableEq β] [DecidableEq κ] [DecidableEq ζ]

def fiberCardOn (S : Finset α) (f : α → β) (y : β) : ℕ :=
  (S.filter (fun x => f x = y)).card

noncomputable def smallFiberProb
    (S : Finset α) (f : α → β) (L : ℝ) : ℝ := by
  classical
  exact uniformProb S (fun x => (fiberCardOn S f (f x) : ℝ) < L)

def CollisionUniversalOn
    (S : Finset α) (R : Finset κ) (Z : Finset ζ)
    (h : κ → α → ζ) : Prop :=
  ∀ x ∈ S, ∀ x' ∈ S, x ≠ x' →
    (Z.card : ℝ) * ((R.filter (fun r => h r x = h r x')).card : ℝ)
      ≤ (R.card : ℝ)

def hashSupportOn
    (S : Finset α) (R : Finset κ) (Z : Finset ζ)
    (f : α → β) : Finset (β × (κ × ζ)) :=
  (S.image f) ×ˢ (R ×ˢ Z)

noncomputable def hashActualOn
    (S : Finset α) (R : Finset κ)
    (f : α → β) (h : κ → α → ζ) : β × (κ × ζ) → ℝ :=
  lawOn (S ×ˢ R) (fun xr => (f xr.1, (xr.2, h xr.2 xr.1)))

noncomputable def hashIdealOn
    (S : Finset α) (R : Finset κ) (Z : Finset ζ)
    (f : α → β) : β × (κ × ζ) → ℝ :=
  lawOn ((S ×ˢ R) ×ˢ Z)
    (fun xrz => (f xrz.1.1, (xrz.1.2, xrz.2)))

def FlatLeftoverHashStatement : Prop :=
  ∀ (S : Finset α) (R : Finset κ) (Z : Finset ζ) (h : κ → α → ζ),
    S.Nonempty → R.Nonempty → Z.Nonempty →
    (∀ r ∈ R, ∀ x ∈ S, h r x ∈ Z) →
    CollisionUniversalOn S R Z h →
    statDistOn (R ×ˢ Z)
      (lawOn (S ×ˢ R) (fun xr => (xr.2, h xr.2 xr.1)))
      (lawOn (R ×ˢ Z) id)
      ≤ (1 / 2 : ℝ) * Real.sqrt ((Z.card : ℝ) / (S.card : ℝ))

def FlatConditionalHashStatement : Prop :=
  ∀ (S : Finset α) (R : Finset κ) (Z : Finset ζ)
    (f : α → β) (h : κ → α → ζ),
    S.Nonempty → R.Nonempty → Z.Nonempty →
    (∀ r ∈ R, ∀ x ∈ S, h r x ∈ Z) →
    CollisionUniversalOn S R Z h →
    ∀ L : ℝ, 0 < L →
    statDistOn (hashSupportOn S R Z f)
      (hashActualOn S R f h) (hashIdealOn S R Z f)
      ≤ smallFiberProb S f L +
        (1 / 2 : ℝ) * Real.sqrt ((Z.card : ℝ) / L)

end

end HILL.PRG.FlatConditionalSubmission

namespace HILL.PRG.FlatConditionalSubmission

/- The finite second-moment argument is adapted from Wentao Li's proof of
HILL.PRG.lemma_4_8.
https://prove2.me/theorems/0d655459-ea71-432d-b377-a9a49c03a0ce -/

set_option maxHeartbeats 1000000 in
private lemma finite_hash_bound {α β κ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq κ]
    (X : Finset α) (Y : Finset β) (K : Finset κ) (D : α → ℝ) (h : κ → α → β)
    (hD : ∀ x ∈ X, 0 ≤ D x) (hsum : ∑ x ∈ X, D x = 1)
    (hY : 0 < Y.card) (hK : 0 < K.card)
    (hmap : ∀ k ∈ K, ∀ x ∈ X, h k x ∈ Y)
    (hcoll : ∀ x ∈ X, ∀ x' ∈ X, x ≠ x' →
      (∑ k ∈ K, if h k x = h k x' then (1 : ℝ) else 0) ≤
        (K.card : ℝ) / Y.card) :
    let P := fun k a => ∑ x ∈ X, if h k x = a then D x else 0
    (∑ k ∈ K, ∑ a ∈ Y, |P k a - 1 / (Y.card : ℝ)|) ^ 2 ≤
      (Y.card : ℝ) * (K.card : ℝ) ^ 2 * (∑ x ∈ X, (D x) ^ 2) := by
  classical
  intro P
  let M : ℝ := Y.card
  let N : ℝ := K.card
  let C : ℝ := ∑ x ∈ X, (D x) ^ 2
  have hM : 0 < M := by dsimp [M]; exact_mod_cast hY
  have hN : 0 < N := by dsimp [N]; exact_mod_cast hK
  have hp (k : κ) (hk : k ∈ K) : ∑ a ∈ Y, P k a = 1 := by
    dsimp [P]
    rw [Finset.sum_comm]
    calc
      _ = ∑ x ∈ X, D x := by
        apply Finset.sum_congr rfl
        intro x hx
        simp [hmap k hk x hx, eq_comm]
      _ = 1 := hsum
  have hmoment (k : κ) (hk : k ∈ K) :
      ∑ a ∈ Y, (P k a) ^ 2 =
        ∑ x ∈ X, ∑ x' ∈ X, if h k x = h k x' then D x * D x' else 0 := by
    simp_rw [P, pow_two, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x' hx'
    have hprod (a : β) :
        (if h k x = a then D x else 0) * (if h k x' = a then D x' else 0) =
          if h k x = a then (if h k x' = a then D x * D x' else 0) else 0 := by
      split_ifs <;> simp_all
    simp_rw [hprod]
    simp [hmap k hk x hx, eq_comm]
  have htotal : (∑ k ∈ K, ∑ a ∈ Y, (P k a) ^ 2) ≤ N * C + N / M := by
    calc
      _ = ∑ x ∈ X, ∑ x' ∈ X,
          (D x * D x') * (∑ k ∈ K, if h k x = h k x' then (1 : ℝ) else 0) := by
        simp_rw [Finset.sum_congr rfl (fun k hk => hmoment k hk)]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x' hx'
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        split_ifs <;> simp
      _ ≤ ∑ x ∈ X, ∑ x' ∈ X,
          (N * (if x = x' then (D x) ^ 2 else 0) + (N / M) * (D x * D x')) := by
        apply Finset.sum_le_sum
        intro x hx
        apply Finset.sum_le_sum
        intro x' hx'
        by_cases hxx : x = x'
        · subst x'
          simp only [ite_true, Finset.sum_const, nsmul_eq_mul, mul_one]
          dsimp only [N]
          nlinarith [mul_nonneg (div_nonneg hN.le hM.le) (sq_nonneg (D x))]
        · rw [if_neg hxx]
          have hh := mul_le_mul_of_nonneg_left (hcoll x hx x' hx' hxx)
            (mul_nonneg (hD x hx) (hD x' hx'))
          simpa only [mul_zero, zero_add, mul_comm] using hh
      _ = N * C + N / M := by
        simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        have hdiag : (∑ x ∈ X, ∑ x' ∈ X, if x = x' then (D x) ^ 2 else 0) = C := by
          apply Finset.sum_congr rfl
          intro x hx
          simp [hx]
        have hall : (∑ x ∈ X, ∑ x' ∈ X, D x * D x') = 1 := by
          rw [← Finset.sum_mul_sum, hsum, one_mul]
        rw [hdiag]; simp only [hsum, mul_one]
  have hvariance (k : κ) (hk : k ∈ K) :
      ∑ a ∈ Y, (P k a - 1 / M) ^ 2 = (∑ a ∈ Y, (P k a) ^ 2) - 1 / M := by
    have heq (a : β) : (P k a - 1 / M) ^ 2 =
        (P k a) ^ 2 - (2 / M) * P k a + (1 / M) ^ 2 := by ring
    simp_rw [heq, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hp k hk, Finset.sum_const, nsmul_eq_mul]
    dsimp only [M]
    field_simp
    ring
  have hv : (∑ k ∈ K, ∑ a ∈ Y, (P k a - 1 / M) ^ 2) ≤ N * C := by
    simp_rw [Finset.sum_congr rfl (fun k hk => hvariance k hk)]
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    have heq : N * (1 / M) = N / M := by ring
    rw [heq]
    linarith
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (K ×ˢ Y)
    (fun z => |P z.1 z.2 - 1 / M|) (fun _ => (1 : ℝ))
  simp only [mul_one, sq_abs, one_pow, Finset.sum_const, nsmul_eq_mul,
    Finset.card_product, Nat.cast_mul, Finset.sum_product] at hcs
  calc
    _ ≤ (∑ k ∈ K, ∑ a ∈ Y, (P k a - 1 / M) ^ 2) * (N * M) := hcs
    _ ≤ (N * C) * (N * M) := mul_le_mul_of_nonneg_right hv (by positivity)
    _ = _ := by ring


private lemma cast_card_filter {τ : Type*} (A : Finset τ) (p : τ → Prop)
    [DecidablePred p] :
    ((A.filter p).card : ℝ) = ∑ x ∈ A, if p x then (1 : ℝ) else 0 := by
  rw [← Finset.sum_filter]
  simp

variable {α β κ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq κ]

/-- Leftover hashing for a finite uniform source and collision-universal keys. -/
theorem flatLeftoverHash : FlatLeftoverHashStatement (α := α) (ζ := β) (κ := κ) := by
  intro S R Z h hS hR hZ hmap hcoll
  obtain ⟨hSpos, hRpos, hZpos⟩ : (0 : ℝ) < S.card ∧
      (0 : ℝ) < R.card ∧ (0 : ℝ) < Z.card :=
    ⟨Nat.cast_pos.mpr (Finset.card_pos.mpr hS),
     Nat.cast_pos.mpr (Finset.card_pos.mpr hR),
     Nat.cast_pos.mpr (Finset.card_pos.mpr hZ)⟩
  have hcoll' (x : α) (hx : x ∈ S) (y : α) (hy : y ∈ S) (hne : x ≠ y) :
      (∑ r ∈ R, if h r x = h r y then (1 : ℝ) else 0) ≤ (R.card : ℝ) / Z.card := by
    rw [← cast_card_filter]
    exact (le_div_iff₀ hZpos).2 (by simpa only [mul_comm] using hcoll x hx y hy hne)
  have hMoment := finite_hash_bound S Z R (fun _ => 1 / (S.card : ℝ)) h
    (fun _ _ => by positivity)
    (by simp [Finset.sum_const, nsmul_eq_mul, hSpos.ne'])
    (Finset.card_pos.mpr hZ) (Finset.card_pos.mpr hR) hmap hcoll'
  have hSquareWeight : (∑ _x ∈ S, (1 / (S.card : ℝ)) ^ 2) = 1 / (S.card : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    field_simp
  let P (r : κ) (z : β) := ∑ x ∈ S, if h r x = z then 1 / (S.card : ℝ) else 0
  have hL1 : (∑ r ∈ R, ∑ z ∈ Z, |P r z - 1 / (Z.card : ℝ)|) ≤
      (R.card : ℝ) * Real.sqrt ((Z.card : ℝ) / S.card) := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).1
    calc
      _ ≤ (Z.card : ℝ) * (R.card : ℝ) ^ 2 * ∑ _x ∈ S, (1 / (S.card : ℝ)) ^ 2 := hMoment
      _ = _ := by rw [hSquareWeight, mul_pow, Real.sq_sqrt (by positivity)]; ring
  have hActual (r : κ) (hr : r ∈ R) (z : β) :
      lawOn (S ×ˢ R) (fun xr => (xr.2, h xr.2 xr.1)) (r, z) =
        P r z / (R.card : ℝ) := by
    unfold lawOn
    have hFilter :
        (S ×ˢ R).filter (fun xr => (xr.2, h xr.2 xr.1) = (r, z)) =
          (S.filter (fun x => h r x = z)) ×ˢ {r} := by
      ext xr
      rcases xr with ⟨x, r'⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨hx, _⟩, rfl, he⟩
        exact ⟨⟨hx, he⟩, rfl⟩
      · rintro ⟨⟨hx, he⟩, rfl⟩
        exact ⟨⟨hx, hr⟩, rfl, he⟩
    rw [hFilter, Finset.card_product, Finset.card_singleton, mul_one,
      Finset.card_product, Nat.cast_mul]
    simp only [P, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    ring
  have hUniform (r : κ) (hr : r ∈ R) (z : β) (hz : z ∈ Z) :
      lawOn (R ×ˢ Z) id (r, z) = 1 / ((Z.card : ℝ) * R.card) := by
    unfold lawOn
    have hFilter : (R ×ˢ Z).filter (fun x => id x = (r, z)) = {(r, z)} := by
      ext p
      simp only [Finset.mem_filter, id_eq, Finset.mem_singleton]
      exact ⟨And.right, fun e => ⟨e.symm ▸ Finset.mem_product.mpr ⟨hr, hz⟩, e⟩⟩
    rw [hFilter, Finset.card_singleton, Nat.cast_one, Finset.card_product, Nat.cast_mul, mul_comm]
  have hAbs (r : κ) (hr : r ∈ R) (z : β) (hz : z ∈ Z) :
      |lawOn (S ×ˢ R) (fun xr => (xr.2, h xr.2 xr.1)) (r, z) -
        lawOn (R ×ˢ Z) id (r, z)| = |P r z - 1 / (Z.card : ℝ)| / (R.card : ℝ) := by
    rw [hActual r hr z, hUniform r hr z hz]
    rw [show P r z / (R.card : ℝ) - 1 / ((Z.card : ℝ) * R.card) =
      (P r z - 1 / (Z.card : ℝ)) / (R.card : ℝ) by ring, abs_div, abs_of_pos hRpos]
  unfold statDistOn
  rw [Finset.sum_product]
  have hSum :
      (∑ r ∈ R, ∑ z ∈ Z,
        |lawOn (S ×ˢ R) (fun xr => (xr.2, h xr.2 xr.1)) (r, z) -
          lawOn (R ×ˢ Z) id (r, z)|) =
        (∑ r ∈ R, ∑ z ∈ Z, |P r z - 1 / (Z.card : ℝ)|) / (R.card : ℝ) := by
    simp only [Finset.sum_div]
    exact Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun z hz => hAbs r hr z hz
  rw [hSum]
  calc
    _ ≤ Real.sqrt ((Z.card : ℝ) / S.card) / 2 :=
      div_le_div_of_nonneg_right
        ((div_le_iff₀ hRpos).2 (by simpa only [mul_comm] using hL1)) (by norm_num)
    _ = _ := by ring

end HILL.PRG.FlatConditionalSubmission

namespace HILL.PRG.FlatConditionalSubmission

variable {α β κ ζ : Type*} [DecidableEq β] [DecidableEq κ] [DecidableEq ζ]

private theorem actualOnFiber (S : Finset α) (R : Finset κ) (f : α → β)
    (h : κ → α → ζ) (hR : R.Nonempty) {y : β} (hy : y ∈ S.image f) (r : κ) (z : ζ) :
    hashActualOn S R f h (y, (r, z)) =
      lawOn S f y *
        lawOn ((S.filter (fun x => f x = y)) ×ˢ R) (fun xr => (xr.2, h xr.2 xr.1)) (r, z) := by
  unfold hashActualOn lawOn
  have hFilter :
      (S ×ˢ R).filter (fun xr => (f xr.1, (xr.2, h xr.2 xr.1)) = (y, (r, z))) =
        ((S.filter (fun x => f x = y)) ×ˢ R).filter (fun xr => (xr.2, h xr.2 xr.1) = (r, z)) := by
    ext xr
    simp only [Finset.mem_filter, Finset.mem_product, Prod.mk.injEq]
    tauto
  rw [hFilter]
  simp only [Finset.card_product, Nat.cast_mul]
  have hFc : ((S.filter (fun x => f x = y)).card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr ((Finset.fiber_card_ne_zero_iff_mem_image S f y).2 hy)
  have hSc : (S.card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.card_ne_zero_of_mem (Finset.mem_image.mp hy).choose_spec.1)
  have hRc : (R.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hR.card_ne_zero
  field_simp [hFc, hSc, hRc]

private theorem idealOnFiber (S : Finset α) (R : Finset κ) (Z : Finset ζ) (f : α → β)
    {r : κ} (hr : r ∈ R) {z : ζ} (hz : z ∈ Z) (y : β) :
    hashIdealOn S R Z f (y, (r, z)) =
      lawOn S f y * lawOn (R ×ˢ Z) id (r, z) := by
  unfold hashIdealOn lawOn
  have hFilter :
      ((S ×ˢ R) ×ˢ Z).filter (fun xrz => (f xrz.1.1, (xrz.1.2, xrz.2)) = (y, (r, z))) =
        ((S.filter (fun x => f x = y)) ×ˢ {r}) ×ˢ {z} := by
    ext p
    rcases p with ⟨⟨x, r'⟩, z'⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨hx, _⟩, _⟩, he, hr', hz'⟩
      exact ⟨⟨⟨hx, he⟩, hr'⟩, hz'⟩
    · rintro ⟨⟨⟨hx, he⟩, rfl⟩, rfl⟩
      exact ⟨⟨⟨hx, hr⟩, hz⟩, he, rfl, rfl⟩
  have hUniform : (R ×ˢ Z).filter (fun p => id p = (r, z)) = {(r, z)} := by
    ext p
    simp only [Finset.mem_filter, id_eq, Finset.mem_singleton]
    exact ⟨And.right, fun e => ⟨e.symm ▸ Finset.mem_product.mpr ⟨hr, hz⟩, e⟩⟩
  rw [hFilter, hUniform]
  simp only [Finset.card_product, Finset.card_singleton, mul_one, Nat.cast_mul, Nat.cast_one]
  ring

/-- Retaining the output label makes joint variation distance a weighted sum
of the variation distances on the individual fibers. -/
theorem conditionalHashDistance_eq (S : Finset α) (R : Finset κ) (Z : Finset ζ)
    (f : α → β) (h : κ → α → ζ) (hR : R.Nonempty) :
    statDistOn (hashSupportOn S R Z f) (hashActualOn S R f h) (hashIdealOn S R Z f) =
      ∑ y ∈ S.image f, lawOn S f y *
        statDistOn (R ×ˢ Z)
          (lawOn ((S.filter (fun x => f x = y)) ×ˢ R) (fun xr => (xr.2, h xr.2 xr.1)))
          (lawOn (R ×ˢ Z) id) := by
  unfold statDistOn hashSupportOn
  rw [Finset.sum_product, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y hy
  rw [← mul_div_assoc, Finset.mul_sum]
  apply congrArg (fun x : ℝ => x / 2)
  refine Finset.sum_congr rfl ?_
  rintro ⟨r, z⟩ hrz
  rw [actualOnFiber S R f h hR hy r z,
    idealOnFiber S R Z f (Finset.mem_product.mp hrz).1 (Finset.mem_product.mp hrz).2 y,
    ← mul_sub, abs_mul, abs_of_nonneg
      (show 0 ≤ lawOn S f y from div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]

private theorem lawOn_isProbOn {A B : Type*} [DecidableEq B] (S : Finset A) (Z : Finset B)
    (f : A → B) (hS : S.Nonempty) (hZ : ∀ x ∈ S, f x ∈ Z) :
    IsProbOn Z (lawOn S f) := by
  refine ⟨fun _ _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), ?_⟩
  have hS0 : (S.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hS.card_ne_zero
  simp only [lawOn, ← Finset.sum_div, ← Nat.cast_sum,
    ← Finset.card_eq_sum_card_fiberwise hZ, div_self hS0]

private theorem statDist_le_one {A : Type*} [DecidableEq A] (S : Finset A) (D E : A → ℝ)
    (hD : IsProbOn S D) (hE : IsProbOn S E) :
    statDistOn S D E ≤ 1 := by
  unfold statDistOn
  calc
    _ ≤ (∑ x ∈ S, (D x + E x)) / 2 :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum fun x hx => by
        simpa only [sub_eq_add_neg, abs_neg, abs_of_nonneg (hD.1 x hx),
          abs_of_nonneg (hE.1 x hx)] using abs_add_le (D x) (-E x)) (by norm_num)
    _ = 1 := by rw [Finset.sum_add_distrib, hD.2, hE.2]; norm_num

private theorem smallFiberProb_eq_sum {A B : Type*} [DecidableEq A] [DecidableEq B]
    (S : Finset A) (f : A → B) (L : ℝ) :
    smallFiberProb S f L =
      ∑ y ∈ S.image f, lawOn S f y * (if (fiberCardOn S f y : ℝ) < L then 1 else 0) := by
  classical
  unfold smallFiberProb uniformProb
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  simp only [Nat.cast_one]
  rw [← Finset.sum_fiberwise_of_maps_to' (fun x hx => Finset.mem_image_of_mem f hx)
    (fun y => if (fiberCardOn S f y : ℝ) < L then (1 : ℝ) else 0), Finset.sum_div]
  exact Finset.sum_congr rfl fun y _ => by
    simp only [Finset.sum_const, nsmul_eq_mul, lawOn, div_mul_eq_mul_div]

variable [DecidableEq α]

/-- Conditional leftover hashing for the flat fibers of a deterministic map. -/
theorem flatConditionalHash :
    FlatConditionalHashStatement (α := α) (β := β) (κ := κ) (ζ := ζ) := by
  intro S R Z f h hS hR hZ hmap hcoll L hL
  rw [conditionalHashDistance_eq S R Z f h hR]
  let C := (1 / 2 : ℝ) * Real.sqrt ((Z.card : ℝ) / L)
  have hFiber (y : β) (hy : y ∈ S.image f) :
      statDistOn (R ×ˢ Z)
        (lawOn ((S.filter (fun x => f x = y)) ×ˢ R) (fun xr => (xr.2, h xr.2 xr.1)))
        (lawOn (R ×ˢ Z) id) ≤
      (if (fiberCardOn S f y : ℝ) < L then 1 else 0) + C := by
    let T := S.filter (fun x => f x = y)
    have hT : T.Nonempty :=
      Finset.card_ne_zero.mp ((Finset.fiber_card_ne_zero_iff_mem_image S f y).mpr hy)
    have hTmap : ∀ r ∈ R, ∀ x ∈ T, h r x ∈ Z :=
      fun r hr x hx => hmap r hr x (Finset.mem_filter.mp hx).1
    change statDistOn (R ×ˢ Z)
      (lawOn (T ×ˢ R) (fun xr => (xr.2, h xr.2 xr.1))) (lawOn (R ×ˢ Z) id) ≤
        (if (T.card : ℝ) < L then 1 else 0) + C
    split_ifs with hSmall
    · exact (statDist_le_one (R ×ˢ Z)
          (lawOn (T ×ˢ R) (fun xr => (xr.2, h xr.2 xr.1))) (lawOn (R ×ˢ Z) id)
          (lawOn_isProbOn _ _ _ (hT.product hR) (fun p hp =>
            let hm := Finset.mem_product.mp hp
            Finset.mem_product.mpr ⟨hm.2, hTmap p.2 hm.2 p.1 hm.1⟩))
          (lawOn_isProbOn _ _ _ (hR.product hZ) (fun _ hp => hp))).trans
          (le_add_of_nonneg_right (by dsimp [C]; positivity))
    · calc
        _ ≤ (1 / 2 : ℝ) * Real.sqrt ((Z.card : ℝ) / T.card) :=
          flatLeftoverHash T R Z h hT hR hZ hTmap (fun x hx x' hx' hne =>
            hcoll x (Finset.mem_filter.mp hx).1 x' (Finset.mem_filter.mp hx').1 hne)
        _ ≤ _ := by
          simpa only [zero_add, C] using mul_le_mul_of_nonneg_left
            (Real.sqrt_le_sqrt
              (div_le_div_of_nonneg_left (Nat.cast_nonneg (α := ℝ) Z.card) hL
                (le_of_not_gt hSmall))) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  calc
    _ ≤ ∑ y ∈ S.image f, lawOn S f y *
        ((if (fiberCardOn S f y : ℝ) < L then 1 else 0) + C) :=
      Finset.sum_le_sum fun y hy => mul_le_mul_of_nonneg_left (hFiber y hy)
        (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    _ = _ := by
      simp_rw [mul_add, Finset.sum_add_distrib]
      rw [← smallFiberProb_eq_sum S f L, ← Finset.sum_mul,
        (lawOn_isProbOn S (S.image f) f hS (fun _ hx => Finset.mem_image_of_mem f hx)).2,
        one_mul]

end HILL.PRG.FlatConditionalSubmission

/-- Conditional leftover hashing with the bad-fiber probability counted over the seed set. -/
theorem solution {α β κ ζ : Type*} [DecidableEq α] [DecidableEq β]
    [DecidableEq κ] [DecidableEq ζ]
    (S : Finset α) (R : Finset κ) (Z : Finset ζ) (f : α → β) (h : κ → α → ζ)
    (hS : S.Nonempty) (hR : R.Nonempty) (hZ : Z.Nonempty)
    (hmap : ∀ r ∈ R, ∀ x ∈ S, h r x ∈ Z)
    (hcoll : ∀ x ∈ S, ∀ x' ∈ S, x ≠ x' →
      (Z.card : ℝ) * ((R.filter (fun r => h r x = h r x')).card : ℝ) ≤ (R.card : ℝ))
    (L : ℝ) (hL : 0 < L) :
    statDistOn ((S.image f) ×ˢ (R ×ˢ Z))
      (lawOn (S ×ˢ R) (fun xr => (f xr.1, (xr.2, h xr.2 xr.1))))
      (lawOn ((S ×ˢ R) ×ˢ Z) (fun xrz => (f xrz.1.1, (xrz.1.2, xrz.2))))
      ≤ (by
          classical
          exact uniformProb S (fun x => ((S.filter (fun u => f u = f x)).card : ℝ) < L)) +
        (1 / 2 : ℝ) * Real.sqrt ((Z.card : ℝ) / L) := by
  exact HILL.PRG.FlatConditionalSubmission.flatConditionalHash S R Z f h hS hR hZ hmap hcoll L hL
