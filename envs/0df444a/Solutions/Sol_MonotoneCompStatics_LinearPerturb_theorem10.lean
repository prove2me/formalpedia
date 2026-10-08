-- Prove2me | solution 1 for MonotoneCompStatics.LinearPerturb.theorem10
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-08T00:30:58.535667+00:00
-- url     : https://prove2.me/submissions/51410a04-9c26-4f4c-a60d-4afd81f957c1

-- SPDX-License-Identifier: Apache-2.0
-- Complete proof of Prove2Me c12b11eb-529d-4ddc-acad-ee83b858f056.
-- New proof; conceptual relation to miao fixed-x converse noted in provenance.
import Definitions.Def_MonotoneCompStatics_Monotonicity_QuasiSupermodularOn
import Definitions.Def_MonotoneCompStatics_Monotonicity_SingleCrossing
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
import Mathlib

set_option autoImplicit false


-- BEGIN MODULE PriceChoice
section

set_option autoImplicit false

namespace MonotoneCompStatics.LinearPerturb.Proof

variable {n : ℕ}

lemma strict_coordinate_of_le_ne (x y : Fin n → ℝ) (hxy : x ≤ y) (hne : x ≠ y) :
    ∃ i, x i < y i := by
  by_contra h
  push Not at h
  exact hne (funext (fun i => le_antisymm (hxy i) (h i)))

lemma exists_price_gap (x y : Fin n → ℝ) (hxy : x ≤ y) (hne : x ≠ y) (a : ℝ) :
    ∃ p : Fin n → ℝ, p ⬝ᵥ y - p ⬝ᵥ x = a := by
  obtain ⟨i, hi⟩ := strict_coordinate_of_le_ne x y hxy hne
  refine ⟨Pi.single i (a / (y i - x i)), ?_⟩
  simp only [single_dotProduct]
  have hn : y i - x i ≠ 0 := (sub_pos.mpr hi).ne'
  field_simp

lemma exists_nonneg_cost_gap (x y : Fin n → ℝ) (hxy : x ≤ y) (hne : x ≠ y)
    (a : ℝ) (ha : 0 ≤ a) :
    ∃ w : Fin n → ℝ, 0 ≤ w ∧ w ⬝ᵥ y - w ⬝ᵥ x = a := by
  obtain ⟨i, hi⟩ := strict_coordinate_of_le_ne x y hxy hne
  have hcoef : 0 ≤ a / (y i - x i) := div_nonneg ha (sub_pos.mpr hi).le
  refine ⟨Pi.single i (a / (y i - x i)), ?_, ?_⟩
  · intro j
    simp only [Pi.single_apply]
    split_ifs
    · exact hcoef
    · exact le_rfl
  · simp only [single_dotProduct]
    have hn : y i - x i ≠ 0 := (sub_pos.mpr hi).ne'
    field_simp
  
end MonotoneCompStatics.LinearPerturb.Proof
end
-- END MODULE PriceChoice

-- BEGIN MODULE JointBridge
section

namespace MonotoneCompStatics.LinearPerturb.Proof
open Supermodularity.Monotonicity MonotoneCompStatics.Monotonicity

variable {n : ℕ}
def HasIncreasingDifferences (f : (Fin n → ℝ) → ℝ → ℝ) : Prop :=
  ∀ x y, x ≤ y → ∀ s t : ℝ, s ≤ t → f x t + f y s ≤ f x s + f y t

lemma joint_to_sections (f : (Fin n → ℝ) → ℝ → ℝ)
    (h : SupermodularOn (fun z : (Fin n → ℝ) × ℝ => f z.1 z.2) Set.univ) :
    ∀ t, SupermodularOn (fun x => f x t) Set.univ := by
  intro t x _ y _
  have hh := h (x := (x,t)) (by trivial) (y := (y,t)) (by trivial)
  simpa using hh

lemma joint_to_increasing (f : (Fin n → ℝ) → ℝ → ℝ)
    (h : SupermodularOn (fun z : (Fin n → ℝ) × ℝ => f z.1 z.2) Set.univ) :
    HasIncreasingDifferences f := by
  intro x y hxy s t hst
  have hh := h (x := (y,s)) (by trivial) (y := (x,t)) (by trivial)
  have he1 : (y,s) ⊔ (x,t) = (y,t) := by
    apply Prod.ext
    · exact sup_eq_left.mpr hxy
    · exact sup_eq_right.mpr hst
  have he2 : (y,s) ⊓ (x,t) = (x,s) := by
    apply Prod.ext
    · exact inf_eq_right.mpr hxy
    · exact inf_eq_left.mpr hst
  rw [he1,he2] at hh
  dsimp at hh
  linarith

lemma joint_of_sections_increasing (f : (Fin n → ℝ) → ℝ → ℝ)
    (hsec : ∀ t, SupermodularOn (fun x => f x t) Set.univ)
    (hinc : HasIncreasingDifferences f) :
    SupermodularOn (fun z : (Fin n → ℝ) × ℝ => f z.1 z.2) Set.univ := by
  have ho : ∀ (x y : Fin n → ℝ) (s t : ℝ), s ≤ t →
      f x s + f y t ≤ f (x ⊔ y) t + f (x ⊓ y) s := by
    intro x y s t hst
    have hs := hsec s (x := x) (by trivial) (y := y) (by trivial)
    have hi := hinc y (x ⊔ y) le_sup_right s t hst
    linarith
  rintro ⟨x,s⟩ _ ⟨y,t⟩ _
  rcases le_total s t with hst | hts
  · have hh := ho x y s t hst
    simpa [sup_eq_right.mpr hst,inf_eq_left.mpr hst] using hh
  · have hh := ho y x t s hts
    simpa [sup_eq_left.mpr hts,inf_eq_right.mpr hts,sup_comm,inf_comm,add_comm] using hh

lemma joint_from_sections_increasing (f : (Fin n → ℝ) → ℝ → ℝ)
    (hsec : ∀ t, SupermodularOn (fun x => f x t) Set.univ)
    (hinc : ∀ x y, x ≤ y → ∀ t s : ℝ, t ≤ s → f y t - f x t ≤ f y s - f x s) :
    SupermodularOn (fun z : (Fin n → ℝ) × ℝ => f z.1 z.2) Set.univ := by
  apply joint_of_sections_increasing f hsec
  intro x y hxy s t hst
  have hh := hinc x y hxy s t hst
  linarith

lemma linear_modular (p x y : Fin n → ℝ) :
    p ⬝ᵥ x + p ⬝ᵥ y = p ⬝ᵥ (x ⊔ y) + p ⬝ᵥ (x ⊓ y) := by
  unfold dotProduct
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change p i * x i + p i * y i = p i * max (x i) (y i) + p i * min (x i) (y i)
  rw [← mul_add,← mul_add,max_add_min]

lemma supermodular_linear_add (g : (Fin n → ℝ) → ℝ)
    (h : SupermodularOn g Set.univ) (p : Fin n → ℝ) :
    SupermodularOn (fun x => g x + p ⬝ᵥ x) Set.univ := by
  intro x _ y _
  have hh := h (x := x) (by trivial) (y := y) (by trivial)
  have hm := linear_modular p x y
  linarith

lemma qsm_of_supermodular (g : (Fin n → ℝ) → ℝ)
    (h : SupermodularOn g Set.univ) : QuasiSupermodularOn g Set.univ := by
  intro x _ y _
  have hh := h (x := x) (by trivial) (y := y) (by trivial)
  constructor <;> intro hc <;> linarith

lemma singleCrossing_of_increasing (f : (Fin n → ℝ) → ℝ → ℝ)
    (h : HasIncreasingDifferences f) (p : Fin n → ℝ) :
    SingleCrossing (fun x t => f x t + p ⬝ᵥ x) := by
  intro y x hxy t s hst
  have hi := h x y hxy.le s t hst.le
  constructor <;> intro hc <;> linarith

lemma linear_perturb_forward (f : (Fin n → ℝ) → ℝ → ℝ)
    (h : SupermodularOn (fun z : (Fin n → ℝ) × ℝ => f z.1 z.2) Set.univ)
    (p : Fin n → ℝ) :
    (∀ t, QuasiSupermodularOn (fun x => f x t + p ⬝ᵥ x) Set.univ) ∧
      SingleCrossing (fun x t => f x t + p ⬝ᵥ x) := by
  exact ⟨fun t => qsm_of_supermodular _ (supermodular_linear_add _ (joint_to_sections f h t) p),
    singleCrossing_of_increasing f (joint_to_increasing f h) p⟩

end MonotoneCompStatics.LinearPerturb.Proof
end
-- END MODULE JointBridge

-- BEGIN MODULE Converse
section

set_option autoImplicit false
namespace MonotoneCompStatics.LinearPerturb.Proof
open Supermodularity.Monotonicity MonotoneCompStatics.Monotonicity
variable {n : ℕ}

lemma price_sections (f : (Fin n → ℝ) → ℝ → ℝ)
    (h : ∀ p : Fin n → ℝ, ∀ t, QuasiSupermodularOn (fun x => f x t + p ⬝ᵥ x) Set.univ) :
    ∀ t, SupermodularOn (fun x => f x t) Set.univ := by
  intro t x _ y _
  by_cases he : x ⊓ y = x
  · have hxy : x ≤ y := inf_eq_left.mp he
    simp [sup_eq_right.mpr hxy, he, add_comm]
  · obtain ⟨p, hp⟩ := exists_price_gap (x ⊓ y) x inf_le_left he (f (x ⊓ y) t - f x t)
    have hq := (h p t (x := x) (by trivial) (y := y) (by trivial)).1 (by linarith)
    have hm := linear_modular p x y
    dsimp at hq
    linarith

lemma price_increasing (f : (Fin n → ℝ) → ℝ → ℝ)
    (h : ∀ p : Fin n → ℝ, SingleCrossing (fun x t => f x t + p ⬝ᵥ x)) :
    HasIncreasingDifferences f := by
  intro x y hxy s t hst
  by_cases he : x = y
  · subst y; linarith
  by_cases ht : s = t
  · subst t; linarith
  obtain ⟨p, hp⟩ := exists_price_gap x y hxy he (f x s - f y s)
  have hq := (h p (lt_of_le_of_ne hxy he) (lt_of_le_of_ne hst ht)).2 (by linarith)
  dsimp at hq
  linarith

lemma cost_sections (f : (Fin n → ℝ) → ℝ → ℝ)
    (hf : ∀ t, Monotone (fun x => f x t))
    (h : ∀ w : Fin n → ℝ, 0 ≤ w → ∀ t,
      QuasiSupermodularOn (fun x => f x t - w ⬝ᵥ x) Set.univ) :
    ∀ t, SupermodularOn (fun x => f x t) Set.univ := by
  intro t x _ y _
  by_cases he : x ⊓ y = x
  · have hxy : x ≤ y := inf_eq_left.mp he
    simp [sup_eq_right.mpr hxy, he, add_comm]
  · obtain ⟨w, hw, hp⟩ := exists_nonneg_cost_gap (x ⊓ y) x inf_le_left he
      (f x t - f (x ⊓ y) t) (sub_nonneg.mpr (hf t inf_le_left))
    have hq := (h w hw t (x := x) (by trivial) (y := y) (by trivial)).1 (by linarith)
    have hm := linear_modular w x y
    dsimp at hq
    linarith

lemma cost_increasing (f : (Fin n → ℝ) → ℝ → ℝ)
    (hf : ∀ t, Monotone (fun x => f x t))
    (h : ∀ w : Fin n → ℝ, 0 ≤ w → SingleCrossing (fun x t => f x t - w ⬝ᵥ x)) :
    HasIncreasingDifferences f := by
  intro x y hxy s t hst
  by_cases he : x = y
  · subst y; linarith
  by_cases ht : s = t
  · subst t; linarith
  obtain ⟨w, hw, hp⟩ := exists_nonneg_cost_gap x y hxy he (f y s - f x s)
    (sub_nonneg.mpr (hf s hxy))
  have hq := (h w hw (lt_of_le_of_ne hxy he) (lt_of_le_of_ne hst ht)).2 (by linarith)
  dsimp at hq
  linarith
end MonotoneCompStatics.LinearPerturb.Proof
end
-- END MODULE Converse

-- BEGIN MODULE FullCharacterization
section

namespace MonotoneCompStatics.LinearPerturb

/-- Milgrom and Shannon (1994), p. 166, Theorem 10. Let `f : ℝⁿ × ℝ → ℝ` (curried).
(1) `f(x, t) + p · x` is quasisupermodular in `x` and has the single crossing property in
`(x; t)` for all `p ∈ ℝⁿ` iff `f` is supermodular (jointly in `(x, t)` on `ℝⁿ × ℝ`).
(2) If `f` is nondecreasing in `x`, then `f(x, t) − w · x` is quasisupermodular in `x` and has the
single crossing property in `(x; t)` for all nonnegative `w ∈ ℝⁿ` iff `f` is supermodular. -/
theorem theorem10 {n : ℕ} (f : (Fin n → ℝ) → ℝ → ℝ) :
    ((∀ p : Fin n → ℝ, (∀ t, MonotoneCompStatics.Monotonicity.QuasiSupermodularOn (fun x => f x t + p ⬝ᵥ x) Set.univ) ∧
        MonotoneCompStatics.Monotonicity.SingleCrossing (fun x t => f x t + p ⬝ᵥ x)) ↔
      Supermodularity.Monotonicity.SupermodularOn
        (fun z : (Fin n → ℝ) × ℝ => f z.1 z.2) Set.univ) ∧
    ((∀ t, Monotone (fun x => f x t)) →
      ((∀ w : Fin n → ℝ, 0 ≤ w →
          (∀ t, MonotoneCompStatics.Monotonicity.QuasiSupermodularOn (fun x => f x t - w ⬝ᵥ x) Set.univ) ∧
          MonotoneCompStatics.Monotonicity.SingleCrossing (fun x t => f x t - w ⬝ᵥ x)) ↔
        Supermodularity.Monotonicity.SupermodularOn
          (fun z : (Fin n → ℝ) × ℝ => f z.1 z.2) Set.univ)) := by
  constructor
  · constructor
    · intro h
      exact Proof.joint_of_sections_increasing f
        (Proof.price_sections f (fun p => (h p).1))
        (Proof.price_increasing f (fun p => (h p).2))
    · intro h p
      exact Proof.linear_perturb_forward f h p
  · intro hf
    constructor
    · intro h
      exact Proof.joint_of_sections_increasing f
        (Proof.cost_sections f hf (fun w hw => (h w hw).1))
        (Proof.cost_increasing f hf (fun w hw => (h w hw).2))
    · intro h w _hw
      simpa only [neg_dotProduct, sub_eq_add_neg] using Proof.linear_perturb_forward f h (-w)

end MonotoneCompStatics.LinearPerturb

end
-- END MODULE FullCharacterization

-- BEGIN MODULE PublicSolution
section

theorem solution {n : ℕ} (f : (Fin n → ℝ) → ℝ → ℝ) :
    ((∀ p : Fin n → ℝ, (∀ t, MonotoneCompStatics.Monotonicity.QuasiSupermodularOn (fun x => f x t + p ⬝ᵥ x) Set.univ) ∧
        MonotoneCompStatics.Monotonicity.SingleCrossing (fun x t => f x t + p ⬝ᵥ x)) ↔
      Supermodularity.Monotonicity.SupermodularOn
        (fun z : (Fin n → ℝ) × ℝ => f z.1 z.2) Set.univ) ∧
    ((∀ t, Monotone (fun x => f x t)) →
      ((∀ w : Fin n → ℝ, 0 ≤ w →
          (∀ t, MonotoneCompStatics.Monotonicity.QuasiSupermodularOn (fun x => f x t - w ⬝ᵥ x) Set.univ) ∧
          MonotoneCompStatics.Monotonicity.SingleCrossing (fun x t => f x t - w ⬝ᵥ x)) ↔
        Supermodularity.Monotonicity.SupermodularOn
          (fun z : (Fin n → ℝ) × ℝ => f z.1 z.2) Set.univ)) := by
  exact MonotoneCompStatics.LinearPerturb.theorem10 f


end
-- END MODULE PublicSolution

#print axioms MonotoneCompStatics.LinearPerturb.theorem10
#print axioms solution
