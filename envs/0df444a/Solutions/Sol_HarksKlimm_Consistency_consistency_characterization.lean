-- Prove2me | solution 1 for HarksKlimm.Consistency.consistency_characterization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T12:34:44.268812+00:00
-- url     : https://prove2.me/submissions/1c2d5d70-4e0b-4002-a207-602c31fe3aca

import Mathlib
import Definitions.Def_HarksKlimm_Consistency_Consistent
import Definitions.Def_HarksKlimm_Consistency_FIPConsistent
import Definitions.Def_HarksKlimm_Consistency_IsAffine
import Definitions.Def_HarksKlimm_Consistency_IsExponential
import Theorems.Thm_HarksKlimm_Consistency_extended_monotonicity
import Theorems.Thm_HarksKlimm_Consistency_individual_classification
import Theorems.Thm_HarksKlimm_Consistency_affine_dependence

set_option autoImplicit false

open scoped NNReal

namespace X4HK

open HarksKlimm.Consistency Finset

variable {n m : ℕ}

/-- an exact (up to positive player weights) potential gives the finite improvement property -/
lemma fip_of_pot (G : Game n m) (Φ : G.Profile → ℝ) (κ : Fin n → ℝ) (hκ : ∀ i, 0 < κ i)
    (hΦ : ∀ (s : G.Profile) (i : Fin n) (t : G.Strategy i),
      Φ (Function.update s i t) - Φ s =
        κ i * (privateCost G (Function.update s i t) i - privateCost G s i)) :
    MondererShapley.Improvement.HasFIP (fun i t => -privateCost G t i) := by
  rintro ⟨y, d, h⟩
  have step : ∀ k, y (k + 1) = Function.update (y k) (d k) (y (k + 1) (d k)) := by
    intro k
    funext j
    by_cases hj : j = d k
    · subst hj; simp
    · rw [Function.update_of_ne hj]; exact (h k).1.2 j hj
  have hdec : ∀ k, Φ (y (k + 1)) < Φ (y k) := by
    intro k
    have h1 := hΦ (y k) (d k) (y (k + 1) (d k))
    rw [← step k] at h1
    have h2 := (h k).2
    simp only at h2
    nlinarith [hκ (d k)]
  have hanti : StrictAnti (Φ ∘ y) := strictAnti_nat_of_succ_lt hdec
  exact not_injective_infinite_finite y (fun a b hab => hanti.injective (by simp [hab]))

/-- the finite improvement property gives a pure Nash equilibrium -/
lemma pne_of_fip (G : Game n m)
    (hF : MondererShapley.Improvement.HasFIP (fun i t => -privateCost G t i)) :
    ∃ s : G.Profile, AGT.IsPureNash (fun i t => -privateCost G t i) s := by
  by_contra hno
  push_neg at hno
  have hex : ∀ s : G.Profile, ∃ i : Fin n, ∃ t : G.Strategy i,
      -privateCost G s i < -privateCost G (Function.update s i t) i := by
    intro s
    have := hno s
    unfold AGT.IsPureNash at this
    push_neg at this
    exact this
  choose who nxt hnxt using hex
  let s0 : G.Profile := fun i => ⟨(G.strategies_nonempty i).choose, (G.strategies_nonempty i).choose_spec⟩
  let y : ℕ → G.Profile := fun k => (fun s => Function.update s (who s) (nxt s))^[k] s0
  refine hF ⟨y, fun k => who (y k), fun k => ?_⟩
  have hy : y (k + 1) = Function.update (y k) (who (y k)) (nxt (y k)) := by
    simp only [y]; rw [Function.iterate_succ_apply']
  rw [hy]
  refine ⟨⟨?_, fun j hj => Function.update_of_ne hj _ _⟩, hnxt (y k)⟩
  rw [Function.update_self]
  intro heq
  have := hnxt (y k)
  rw [heq, Function.update_eq_self] at this
  exact lt_irrefl _ this

/-- the load seen by facility `f` from players other than `i` -/
noncomputable def others (G : Game n m) (s : G.Profile) (i : Fin n) (f : Fin m) : ℝ≥0 :=
  ∑ j ∈ univ.erase i, if f ∈ (s j).val then G.demand j else 0

lemma load_s (G : Game n m) (s : G.Profile) (i : Fin n) (f : Fin m) :
    load G s f = others G s i f + (if f ∈ (s i).val then G.demand i else 0) := by
  unfold load others
  rw [← Finset.add_sum_erase _ _ (mem_univ i), add_comm]

lemma load_u (G : Game n m) (s : G.Profile) (i : Fin n) (t : G.Strategy i) (f : Fin m) :
    load G (Function.update s i t) f = others G s i f + (if f ∈ t.val then G.demand i else 0) := by
  unfold load others
  rw [← Finset.add_sum_erase _ _ (mem_univ i), add_comm, Function.update_self]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (ne_of_mem_erase hj)]

lemma pc_s (G : Game n m) (s : G.Profile) (i : Fin n) :
    privateCost G s i = ∑ f ∈ (s i).val, (G.demand i : ℝ) * G.cost f (others G s i f + G.demand i) := by
  unfold privateCost
  refine Finset.sum_congr rfl fun f hf => ?_
  rw [load_s G s i f, if_pos hf]

lemma pc_u (G : Game n m) (s : G.Profile) (i : Fin n) (t : G.Strategy i) :
    privateCost G (Function.update s i t) i =
      ∑ f ∈ t.val, (G.demand i : ℝ) * G.cost f (others G s i f + G.demand i) := by
  unfold privateCost
  rw [Function.update_self]
  refine Finset.sum_congr rfl fun f hf => ?_
  rw [load_u G s i t f, if_pos hf]

/-- the potential -/
noncomputable def pot (G : Game n m) (g : Fin m → ℝ≥0 → ℝ) (h : ℝ≥0 → Fin m → ℝ)
    (s : G.Profile) : ℝ :=
  ∑ f, g f (load G s f) + ∑ j, ∑ f ∈ (s j).val, h (G.demand j) f

lemma ite_diff (g : ℝ≥0 → ℝ) (L d : ℝ≥0) (p q : Prop) [Decidable p] [Decidable q] :
    g (L + if q then d else 0) - g (L + if p then d else 0) =
      (if q then g (L + d) - g L else 0) - (if p then g (L + d) - g L else 0) := by
  split_ifs <;> simp

lemma pot_diff (G : Game n m) (g : Fin m → ℝ≥0 → ℝ) (h : ℝ≥0 → Fin m → ℝ)
    (s : G.Profile) (i : Fin n) (t : G.Strategy i) :
    pot G g h (Function.update s i t) - pot G g h s =
      ∑ f ∈ t.val, (g f (others G s i f + G.demand i) - g f (others G s i f) + h (G.demand i) f) -
      ∑ f ∈ (s i).val, (g f (others G s i f + G.demand i) - g f (others G s i f) + h (G.demand i) f) := by
  unfold pot
  have hp : ∑ j, ∑ f ∈ (Function.update s i t j).val, h (G.demand j) f =
      ∑ f ∈ t.val, h (G.demand i) f + ∑ j ∈ univ.erase i, ∑ f ∈ (s j).val, h (G.demand j) f := by
    rw [← Finset.add_sum_erase _ _ (mem_univ i), Function.update_self]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (ne_of_mem_erase hj)]
  have hq : ∑ j, ∑ f ∈ (s j).val, h (G.demand j) f =
      ∑ f ∈ (s i).val, h (G.demand i) f + ∑ j ∈ univ.erase i, ∑ f ∈ (s j).val, h (G.demand j) f := by
    rw [← Finset.add_sum_erase _ _ (mem_univ i)]
  have hf : ∑ f, g f (load G (Function.update s i t) f) - ∑ f, g f (load G s f) =
      ∑ f ∈ t.val, (g f (others G s i f + G.demand i) - g f (others G s i f)) -
      ∑ f ∈ (s i).val, (g f (others G s i f + G.demand i) - g f (others G s i f)) := by
    rw [← Finset.sum_sub_distrib]
    rw [Finset.sum_congr rfl (fun f _ => by rw [load_u G s i t f, load_s G s i f, ite_diff])]
    simp only [Finset.sum_sub_distrib, Finset.sum_ite_mem, univ_inter]
  rw [hp, hq, Finset.sum_add_distrib, Finset.sum_add_distrib]
  linear_combination hf

lemma fip_gen (G : Game n m) (g : Fin m → ℝ≥0 → ℝ) (h : ℝ≥0 → Fin m → ℝ) (κ : ℝ≥0 → ℝ)
    (hκ : ∀ d : ℝ≥0, 0 < d → 0 < κ d)
    (hg : ∀ f x d, 0 < d → g f (x + d) - g f x + h d f = κ d * G.cost f (x + d)) :
    MondererShapley.Improvement.HasFIP (fun i t => -privateCost G t i) := by
  refine fip_of_pot G (pot G g h) (fun i => κ (G.demand i) / (G.demand i : ℝ))
    (fun i => div_pos (hκ _ (G.demand_pos i)) (by exact_mod_cast G.demand_pos i)) ?_
  intro s i t
  have hd : (0 : ℝ) < G.demand i := by exact_mod_cast G.demand_pos i
  rw [pot_diff, pc_u, pc_s]
  simp only [hg _ _ _ (G.demand_pos i)]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  field_simp

lemma fip_affine (G : Game n m) (haff : ∀ f, IsAffine (G.cost f)) :
    MondererShapley.Improvement.HasFIP (fun i t => -privateCost G t i) := by
  choose a b hab using haff
  refine fip_gen G (fun f x => a f / 2 * (x : ℝ) ^ 2 + b f * x) (fun d f => a f / 2 * (d : ℝ) ^ 2)
    (fun d => d) (fun d hd => by exact_mod_cast hd) ?_
  intro f x d _
  rw [hab]; push_cast; ring

lemma kappa_pos (φ : ℝ) (hφ : φ ≠ 0) (d : ℝ) (hd : 0 < d) : 0 < (1 - Real.exp (-(φ * d))) / φ := by
  rcases lt_or_gt_of_ne hφ with h | h
  · apply div_pos_of_neg_of_neg _ h
    have : 0 < -(φ * d) := by nlinarith
    linarith [Real.add_one_lt_exp (ne_of_gt this)]
  · apply div_pos _ h
    have : -(φ * d) < 0 := by nlinarith
    linarith [Real.exp_lt_one_iff.mpr this]  

lemma fip_exp (G : Game n m) (φ : ℝ) (hφ : φ ≠ 0) (hexp : ∀ f, IsExponential φ (G.cost f)) :
    MondererShapley.Improvement.HasFIP (fun i t => -privateCost G t i) := by
  choose a b hab using hexp
  refine fip_gen G (fun f x => a f / φ * Real.exp (φ * x))
    (fun d f => b f * ((1 - Real.exp (-(φ * d))) / φ))
    (fun d => (1 - Real.exp (-(φ * d))) / φ) (fun d hd => kappa_pos φ hφ d (by exact_mod_cast hd)) ?_
  intro f x d _
  rw [hab]
  push_cast
  have h1 : Real.exp (φ * (x + d)) * Real.exp (-(φ * d)) = Real.exp (φ * x) := by
    rw [← Real.exp_add]; ring_nf
  field_simp
  linear_combination (a f) * h1

lemma fip_of_class (C : Set (ℝ≥0 → ℝ))
    (hcl : (∀ c ∈ C, IsAffine c) ∨ (∃ φ : ℝ, ∀ c ∈ C, IsExponential φ c)) : FIPConsistent C := by
  intro n m G hG
  rcases hcl with haff | ⟨φ, hexp⟩
  · exact fip_affine G fun f => haff _ (hG f)
  · by_cases hφ : φ = 0
    · refine fip_affine G fun f => ?_
      obtain ⟨a, b, hab⟩ := hexp _ (hG f)
      exact ⟨0, a + b, fun x => by rw [hab, hφ]; simp⟩
    · exact fip_exp G φ hφ fun f => hexp _ (hG f)

lemma cons_of_fip (C : Set (ℝ≥0 → ℝ)) (h : FIPConsistent C) : Consistent C :=
  fun n m G hG => pne_of_fip G (h n m G hG)

lemma mono_one (C : Set (ℝ≥0 → ℝ)) (hmon : ∀ h ∈ IntegerHull C, IsMonotonic h) (c : ℝ≥0 → ℝ)
    (hc : c ∈ C) : IsMonotonic c :=
  hmon c ⟨1, fun _ => 1, fun _ => 0, fun _ => c, fun _ => hc, fun x => by simp⟩

lemma class_of_cons (C : Set (ℝ≥0 → ℝ)) (hC : ∀ c ∈ C, Continuous c) (hcons : Consistent C) :
    (∀ c ∈ C, IsAffine c) ∨ (∃ φ : ℝ, ∀ c ∈ C, IsExponential φ c) := by
  by_cases hall : ∀ c ∈ C, IsAffine c
  · exact Or.inl hall
  right
  push_neg at hall
  obtain ⟨c0, hc0, hna⟩ := hall
  have hmon := extended_monotonicity C hC hcons
  have shift : ∀ h ∈ ShiftHull C, IsMonotonic h := by
    rintro h ⟨a1, a2, c, δ, hc, _, hx⟩
    refine hmon h ⟨2, ![a1, a2], ![0, δ], ![c, c], fun k => by fin_cases k <;> simpa, fun x => ?_⟩
    simp [Fin.sum_univ_two, hx]
  rcases (individual_classification C hC).1 shift c0 hc0 with ⟨φ, hφ⟩ | haff
  swap; · exact absurd haff hna
  refine ⟨φ, fun c hc => ?_⟩
  by_cases hnc : ∃ x y, c x ≠ c y
  · have hnc0 : ∃ x y, c0 x ≠ c0 y := by
      by_contra hk
      push_neg at hk
      exact hna ⟨0, c0 0, fun x => by simp [hk x 0]⟩
    have two : ∀ a₁ a₂ : ℤ, IsMonotonic (fun x => (a₁ : ℝ) * c0 x + (a₂ : ℝ) * c x) := by
      intro a₁ a₂
      refine hmon _ ⟨2, ![a₁, a₂], ![0, 0], ![c0, c], fun k => by fin_cases k <;> simpa, fun x => ?_⟩
      simp [Fin.sum_univ_two]
    obtain ⟨α, β, hαβ⟩ := (affine_dependence c0 c (hC c0 hc0) (hC c hc) (mono_one C hmon c0 hc0)
      (mono_one C hmon c hc) hnc0 hnc).1 two
    obtain ⟨a, b, hab⟩ := hφ
    exact ⟨α * a, α * b + β, fun x => by rw [hαβ, hab]; ring⟩
  · push_neg at hnc
    exact ⟨0, c 0, fun x => by simp [hnc x 0]⟩

end X4HK

open scoped NNReal in
open HarksKlimm.Consistency in
theorem solution (C : Set (ℝ≥0 → ℝ))
    (hC : ∀ c ∈ C, Continuous c) :
    (Consistent C ↔ FIPConsistent C) ∧
    (FIPConsistent C ↔
      ((∀ c ∈ C, IsAffine c) ∨ (∃ φ : ℝ, ∀ c ∈ C, IsExponential φ c))) :=
  ⟨⟨fun h => X4HK.fip_of_class C (X4HK.class_of_cons C hC h), X4HK.cons_of_fip C⟩,
    ⟨fun h => X4HK.class_of_cons C hC (X4HK.cons_of_fip C h), X4HK.fip_of_class C⟩⟩
