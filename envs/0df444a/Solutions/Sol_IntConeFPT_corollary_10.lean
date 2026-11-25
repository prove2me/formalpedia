-- Prove2me | solution 1 for IntConeFPT.corollary_10
-- status  : ACCEPTED   (prove)
-- author  : @ohnesorgefelix
-- created : 2026-11-25T15:40:33.110878+00:00
-- url     : https://prove2.me/submissions/b09f0ca6-3f7a-4778-a657-15a9a9b7a3f9

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encInt
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_OnlineCRS_Combine_encVec
import Definitions.Def_IntConeFPT_Instance
import Definitions.Def_IntConeFPT_Problem
import Definitions.Def_IntConeFPT_Residue
import Definitions.Def_IntConeFPT_Formulation
import Theorems.Thm_IntConeFPT_lemma_7

set_option autoImplicit false

open OnlineCRS.Combine
open IntConeFPT

namespace IntConeFPT.Corollary10Proof

open scoped Classical

/-! ### 1. Basic algebra for `aggr`, `count`, `costOf`, `fracCost`, and `EReal` -/

private lemma aggr_zero {d k : ℕ} : aggr (d := d) (k := k) 0 = 0 := by simp [aggr]

private lemma aggr_add {d k : ℕ} (μ₁ μ₂ : Gen d k →₀ ℕ) :
    aggr (μ₁ + μ₂) = aggr μ₁ + aggr μ₂ := by
  unfold aggr
  exact Finsupp.sum_add_index' (fun _ => by simp)
    (fun _ _ _ => by simp only [Nat.cast_add, add_smul])

private lemma aggr_sum {d k : ℕ} {ι : Type*} (s : Finset ι) (h : ι → Gen d k →₀ ℕ) :
    aggr (∑ i ∈ s, h i) = ∑ i ∈ s, aggr (h i) := by
  induction s using Finset.induction_on with
  | empty => simp [aggr_zero]
  | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, aggr_add, ih]

private lemma aggr_single {d k : ℕ} (g : Gen d k) (n : ℕ) :
    aggr (Finsupp.single g n) = (n : ℝ) • g.toReal := by
  unfold aggr
  exact Finsupp.sum_single_index (by simp)

private lemma count_zero {d k : ℕ} : count (d := d) (k := k) 0 = 0 := by simp [count]

private lemma count_add {d k : ℕ} (μ₁ μ₂ : Gen d k →₀ ℕ) :
    count (μ₁ + μ₂) = count μ₁ + count μ₂ := by
  unfold count
  exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

private lemma count_sum {d k : ℕ} {ι : Type*} (s : Finset ι) (h : ι → Gen d k →₀ ℕ) :
    count (∑ i ∈ s, h i) = ∑ i ∈ s, count (h i) := by
  induction s using Finset.induction_on with
  | empty => simp [count_zero]
  | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, count_add, ih]

private lemma count_single {d k : ℕ} (g : Gen d k) (n : ℕ) :
    count (Finsupp.single g n) = n := by
  unfold count
  exact Finsupp.sum_single_index rfl

private lemma costOf_zero {d k : ℕ} (f : (Fin d → ℝ) → ℝ) :
    costOf (d := d) (k := k) f 0 = 0 := by simp [costOf]

private lemma costOf_add {d k : ℕ} (f : (Fin d → ℝ) → ℝ) (μ₁ μ₂ : Gen d k →₀ ℕ) :
    costOf f (μ₁ + μ₂) = costOf f μ₁ + costOf f μ₂ := by
  unfold costOf
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by push_cast; ring)

private lemma costOf_sum {d k : ℕ} (f : (Fin d → ℝ) → ℝ) {ι : Type*} (s : Finset ι)
    (h : ι → Gen d k →₀ ℕ) :
    costOf f (∑ i ∈ s, h i) = ∑ i ∈ s, costOf f (h i) := by
  induction s using Finset.induction_on with
  | empty => simp [costOf_zero]
  | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, costOf_add, ih]

private lemma costOf_single {d k : ℕ} (f : (Fin d → ℝ) → ℝ) (g : Gen d k) (n : ℕ) :
    costOf f (Finsupp.single g n) = (n : ℝ) * f (fun i => (g.1 i : ℝ)) := by
  unfold costOf
  exact Finsupp.sum_single_index (by simp)

private lemma coe_finset_sum_ereal {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, ((f i : ℝ) : EReal) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [Finset.sum_insert ha, ih]

private lemma finset_sum_le_sum_ereal {ι : Type*} (s : Finset ι) (f g : ι → EReal)
    (h : ∀ i ∈ s, f i ≤ g i) : ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact add_le_add (h a (Finset.mem_insert_self a s))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private lemma isFracRep_add {d k : ℕ} {T : Set (Gen d k)} {θ₁ θ₂ : Gen d k →₀ ℝ}
    {ξ₁ ξ₂ : Pt d k}
    (h₁ : IsFracRep T θ₁ ξ₁) (h₂ : IsFracRep T θ₂ ξ₂) :
    IsFracRep T (θ₁ + θ₂) (ξ₁ + ξ₂) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g hg
    rcases Finset.mem_union.mp (Finsupp.support_add hg) with h | h
    · exact h₁.1 h
    · exact h₂.1 h
  · intro g
    exact add_nonneg (h₁.2.1 g) (h₂.2.1 g)
  · rw [Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by simp [add_smul]),
      h₁.2.2.1, h₂.2.2.1]
    rfl
  · rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), h₁.2.2.2, h₂.2.2.2]
    rfl

private lemma isFracRep_single {d k : ℕ} {T : Set (Gen d k)} {g : Gen d k} (hg : g ∈ T)
    {c : ℝ} (hc : 0 ≤ c) :
    IsFracRep T (Finsupp.single g c) ((c • g.toReal).1, (c • g.toReal).2, c) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hx)]
    exact hg
  · intro x
    by_cases hx : x = g
    · subst hx; simp [hc]
    · simp [Ne.symm hx]
  · rw [Finsupp.sum_single_index (by simp)]
  · rw [Finsupp.sum_single_index rfl]

private lemma isFracRep_sum {d k : ℕ} {T : Set (Gen d k)} {ι : Type*} (s : Finset ι)
    (θ : ι → Gen d k →₀ ℝ) (ξ : ι → Pt d k)
    (h : ∀ i ∈ s, IsFracRep T (θ i) (ξ i)) :
    IsFracRep T (∑ i ∈ s, θ i) (∑ i ∈ s, ξ i) := by
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨by simp, by simp, ?_, ?_⟩
      · ext <;> simp
      · simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact isFracRep_add (h a (Finset.mem_insert_self a s))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private lemma isFracRep_smul {d k : ℕ} {T : Set (Gen d k)} {θ : Gen d k →₀ ℝ} {ξ : Pt d k}
    {a : ℝ} (ha : 0 ≤ a) (h : IsFracRep T θ ξ) :
    IsFracRep T (a • θ) (a • ξ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g hg
    exact h.1 (Finsupp.support_smul hg)
  · intro g
    exact mul_nonneg ha (h.2.1 g)
  · have hsub : (a • θ).support ⊆ θ.support := Finsupp.support_smul
    have heq0 : ∀ g ∈ θ.support, g ∉ (a • θ).support → ((a • θ) g) • g.toReal = 0 := by
      intro g _ hg
      rw [Finsupp.notMem_support_iff.mp hg, zero_smul]
    change ∑ g ∈ (a • θ).support, ((a • θ) g) • g.toReal = ((a • ξ).1, (a • ξ).2.1)
    rw [Finset.sum_subset hsub heq0]
    have heq : ∑ x ∈ θ.support, ((a • θ) x) • x.toReal = a • ∑ x ∈ θ.support, θ x • x.toReal := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      simp [Finsupp.coe_smul, mul_smul]
    have h1 : (∑ x ∈ θ.support, θ x • x.toReal) = (ξ.1, ξ.2.1) := h.2.2.1
    rw [heq, h1]
    rfl
  · have hsub : (a • θ).support ⊆ θ.support := Finsupp.support_smul
    have heq0 : ∀ g ∈ θ.support, g ∉ (a • θ).support → (a • θ) g = 0 := fun g _ hg =>
      Finsupp.notMem_support_iff.mp hg
    change ∑ g ∈ (a • θ).support, (a • θ) g = (a • ξ).2.2
    rw [Finset.sum_subset hsub heq0]
    have heq : ∑ x ∈ θ.support, (a • θ) x = a * ∑ x ∈ θ.support, θ x := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun g _ => by simp [Finsupp.coe_smul]
    have h2 : (∑ x ∈ θ.support, θ x) = ξ.2.2 := h.2.2.2
    rw [heq, h2]
    rfl

private lemma fracCost_add {d k : ℕ} (f : (Fin d → ℝ) → ℝ) (θ₁ θ₂ : Gen d k →₀ ℝ) :
    fracCost f (θ₁ + θ₂) = fracCost f θ₁ + fracCost f θ₂ := by
  unfold fracCost
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring)

private lemma fracCost_sub {d k : ℕ} (f : (Fin d → ℝ) → ℝ) (θ₁ θ₂ : Gen d k →₀ ℝ) :
    fracCost f (θ₁ - θ₂) = fracCost f θ₁ - fracCost f θ₂ := by
  have h : θ₁ = (θ₁ - θ₂) + θ₂ := (sub_add_cancel θ₁ θ₂).symm
  have h' := congr_arg (fracCost f) h
  rw [fracCost_add] at h'
  linarith

private lemma fracCost_single {d k : ℕ} (f : (Fin d → ℝ) → ℝ) (g : Gen d k) (c : ℝ) :
    fracCost f (Finsupp.single g c) = c * f (fun i => (g.1 i : ℝ)) := by
  unfold fracCost
  exact Finsupp.sum_single_index (by simp)

private lemma fracCost_sum {d k : ℕ} (f : (Fin d → ℝ) → ℝ) {ι : Type*} (s : Finset ι)
    (θ : ι → Gen d k →₀ ℝ) :
    fracCost f (∑ i ∈ s, θ i) = ∑ i ∈ s, fracCost f (θ i) := by
  induction s using Finset.induction_on with
  | empty => simp [fracCost]
  | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fracCost_add, ih]

private lemma fracCost_smul {d k : ℕ} (f : (Fin d → ℝ) → ℝ) (a : ℝ) (θ : Gen d k →₀ ℝ) :
    fracCost f (a • θ) = a * fracCost f θ := by
  unfold fracCost
  have hsub : (a • θ).support ⊆ θ.support := Finsupp.support_smul
  have heq0 : ∀ g ∈ θ.support, g ∉ (a • θ).support →
      (a • θ) g * f (fun i => (g.1 i : ℝ)) = 0 := fun g _ hg => by
    rw [Finsupp.notMem_support_iff.mp hg, zero_mul]
  change ∑ g ∈ (a • θ).support, (a • θ) g * f (fun i => (g.1 i : ℝ)) =
    a * ∑ g ∈ θ.support, θ g * f (fun i => (g.1 i : ℝ))
  rw [Finset.sum_subset hsub heq0, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => by simp [Finsupp.coe_smul, mul_assoc]

/-! ### 2. Polytope, fiber compactness, extreme points, and `Vr` finiteness -/

private lemma convex_P (I : Instance) (t : Fin I.τ) : Convex ℝ (I.P t) := by
  intro p₁ hp₁ p₂ hp₂ a b ha hb hab i
  have h1 := hp₁ i
  have h2 := hp₂ i
  have hcomb :
      (∑ j, (I.Aloc t i j : ℝ) * (a • p₁ + b • p₂).1 j) +
        (∑ j, (I.Bloc t i j : ℝ) * (a • p₁ + b • p₂).2 j) =
      a * ((∑ j, (I.Aloc t i j : ℝ) * p₁.1 j) + (∑ j, (I.Bloc t i j : ℝ) * p₁.2 j)) +
        b * ((∑ j, (I.Aloc t i j : ℝ) * p₂.1 j) + (∑ j, (I.Bloc t i j : ℝ) * p₂.2 j)) := by
    simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    simp_rw [mul_add, Finset.sum_add_distrib]
    have ha1 : (∑ j, (I.Aloc t i j : ℝ) * (a * p₁.1 j)) =
        a * ∑ j, (I.Aloc t i j : ℝ) * p₁.1 j := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
    have hb1 : (∑ j, (I.Aloc t i j : ℝ) * (b * p₂.1 j)) =
        b * ∑ j, (I.Aloc t i j : ℝ) * p₂.1 j := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
    have ha2 : (∑ j, (I.Bloc t i j : ℝ) * (a * p₁.2 j)) =
        a * ∑ j, (I.Bloc t i j : ℝ) * p₁.2 j := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
    have hb2 : (∑ j, (I.Bloc t i j : ℝ) * (b * p₂.2 j)) =
        b * ∑ j, (I.Bloc t i j : ℝ) * p₂.2 j := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
    rw [ha1, hb1, ha2, hb2]
    ring
  rw [hcomb]
  calc a * ((∑ j, (I.Aloc t i j : ℝ) * p₁.1 j) + (∑ j, (I.Bloc t i j : ℝ) * p₁.2 j)) +
        b * ((∑ j, (I.Aloc t i j : ℝ) * p₂.1 j) + (∑ j, (I.Bloc t i j : ℝ) * p₂.2 j))
    _ ≤ a * (I.bloc t i : ℝ) + b * (I.bloc t i : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)
    _ = (a + b) * (I.bloc t i : ℝ) := by ring
    _ = (I.bloc t i : ℝ) := by rw [hab, one_mul]

private lemma isClosed_P (I : Instance) (t : Fin I.τ) : IsClosed (I.P t) := by
  have hEq : I.P t = ⋂ i : Fin (I.m t),
      {p : (Fin I.d → ℝ) × (Fin I.k → ℝ) |
        (∑ j, (I.Aloc t i j : ℝ) * p.1 j) + (∑ j, (I.Bloc t i j : ℝ) * p.2 j) ≤
          (I.bloc t i : ℝ)} := by
    ext p
    simp [Instance.P]
  rw [hEq]
  refine isClosed_iInter fun i => isClosed_le ?_ continuous_const
  refine Continuous.add ?_ ?_
  · refine continuous_finsetSum _ fun j _ => ?_
    exact continuous_const.mul ((continuous_apply j).comp continuous_fst)
  · refine continuous_finsetSum _ fun j _ => ?_
    exact continuous_const.mul ((continuous_apply j).comp continuous_snd)

private lemma discreteJensen_of_valid (I : Instance) (hI : I.Valid) (t : Fin I.τ) :
    DiscreteJensen {x : Fin I.d → ℤ | (fun i => (x i : ℝ)) ∈ Prod.fst '' I.P t}
      (fun x => I.f t (fun i => (x i : ℝ))) := by
  intro x hx m θ xs hxs hθ0 hθ1 hcomb
  have hxPx : (fun i => (x i : ℝ)) ∈ I.Px t := hx
  have hxsPx : ∀ i ∈ Finset.univ, (fun j => (xs i j : ℝ)) ∈ I.Px t := fun i _ => hxs i
  have hmap := (hI.convex t).map_sum_le (fun i _ => hθ0 i) hθ1 hxsPx
  simp only [smul_eq_mul] at hmap
  rw [← hcomb] at hmap
  exact hmap

private lemma convex_fiber (I : Instance) (t : Fin I.τ) (x : Fin I.d → ℤ) :
    Convex ℝ (I.fiber t x) := by
  intro u₁ hu₁ u₂ hu₂ a b ha hb hab
  change ((fun i => (x i : ℝ)), a • u₁ + b • u₂) ∈ I.P t
  have hmem := convex_P I t hu₁ hu₂ ha hb hab
  have heq : (a • ((fun i => (x i : ℝ)), u₁) + b • ((fun i => (x i : ℝ)), u₂)) =
      ((fun i => (x i : ℝ)), a • u₁ + b • u₂) := by
    ext j
    · simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      calc a * (x j : ℝ) + b * (x j : ℝ) = (a + b) * (x j : ℝ) := by ring
        _ = (x j : ℝ) := by rw [hab, one_mul]
    · simp only [Prod.snd_add, Prod.smul_snd]
  rwa [← heq]

private lemma isCompact_fiber (I : Instance) (hI : I.Valid) (t : Fin I.τ) (x : Fin I.d → ℤ) :
    IsCompact (I.fiber t x) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · have heq : I.fiber t x = (fun u => ((fun i => (x i : ℝ)), u)) ⁻¹' I.P t := rfl
    rw [heq]
    exact (isClosed_P I t).preimage (continuous_const.prodMk continuous_id)
  · have hsub : I.fiber t x ⊆ Prod.snd '' I.P t := fun u hu => ⟨(_, u), hu, rfl⟩
    exact (LipschitzWith.prod_snd.isBounded_image (hI.bounded t)).subset hsub

private lemma finite_X (I : Instance) (hI : I.Valid) (t : Fin I.τ) : (I.X t).Finite := by
  have hPx_bdd : Bornology.IsBounded (I.Px t) :=
    LipschitzWith.prod_fst.isBounded_image (hI.bounded t)
  obtain ⟨R, hR⟩ := hPx_bdd.subset_closedBall (0 : Fin I.d → ℝ)
  let M : ℕ := Nat.ceil (max R 0)
  have hsub : I.X t ⊆
      ((Fintype.piFinset fun _ : Fin I.d => Finset.Icc (-(M : ℤ)) (M : ℤ) :
          Finset (Fin I.d → ℤ)) : Set (Fin I.d → ℤ)) := by
    intro x hx
    have hxball : (fun i => (x i : ℝ)) ∈ Metric.closedBall (0 : Fin I.d → ℝ) R := hR hx
    rw [Metric.mem_closedBall, dist_zero_right] at hxball
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro i
    have hi : |(x i : ℝ)| ≤ (M : ℝ) := by
      calc |(x i : ℝ)| = ‖(x i : ℝ)‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖fun j => (x j : ℝ)‖ := norm_le_pi_norm (fun j => (x j : ℝ)) i
        _ ≤ R := hxball
        _ ≤ max R 0 := le_max_left _ _
        _ ≤ (M : ℝ) := Nat.le_ceil _
    have hiZ : |x i| ≤ (M : ℤ) := by
      exact_mod_cast hi
    exact Finset.mem_Icc.mpr (abs_le.mp hiZ)
  exact (Finset.finite_toSet _).subset hsub

private lemma finite_extremePoints_fiber (I : Instance) (t : Fin I.τ) (x : Fin I.d → ℤ) :
    (Set.extremePoints ℝ (I.fiber t x)).Finite := by
  let act : (Fin I.k → ℝ) → Finset (Fin (I.m t)) := fun u =>
    Finset.univ.filter fun i =>
      (∑ j, (I.Aloc t i j : ℝ) * (x j : ℝ)) + (∑ j, (I.Bloc t i j : ℝ) * u j) =
        (I.bloc t i : ℝ)
  refine Set.Finite.of_finite_image (f := act) (Set.toFinite _) ?_
  intro u₁ hu₁ u₂ hu₂ hact
  by_contra hne
  let d : Fin I.k → ℝ := u₂ - u₁
  let S : Finset (Fin (I.m t)) := Finset.univ.filter fun i => i ∉ act u₁
  let rhs : Fin (I.m t) → ℝ := fun i => (I.bloc t i : ℝ) - ∑ j, (I.Aloc t i j : ℝ) * (x j : ℝ)
  let slack : Fin (I.m t) → ℝ := fun i => rhs i - ∑ j, (I.Bloc t i j : ℝ) * u₁ j
  let stepRatio : Fin (I.m t) → ℝ := fun i => slack i / (|∑ j, (I.Bloc t i j : ℝ) * d j| + 1)
  have hu₁_mem : ∀ i, (∑ j, (I.Bloc t i j : ℝ) * u₁ j) ≤ rhs i := fun i => by
    have h := hu₁.1 i
    dsimp only [rhs]
    linarith
  have hu₂_mem : ∀ i, (∑ j, (I.Bloc t i j : ℝ) * u₂ j) ≤ rhs i := fun i => by
    have h := hu₂.1 i
    dsimp only [rhs]
    linarith
  have hact_iff : ∀ u i, i ∈ act u ↔ (∑ j, (I.Bloc t i j : ℝ) * u j) = rhs i := fun u i => by
    simp only [act, Finset.mem_filter, Finset.mem_univ, true_and, rhs]
    constructor <;> intro h <;> linarith
  have hd_zero : ∀ i ∈ act u₁, (∑ j, (I.Bloc t i j : ℝ) * d j) = 0 := fun i hi => by
    have hi1 := (hact_iff u₁ i).mp hi
    have hi2 := (hact_iff u₂ i).mp (hact ▸ hi)
    have hlin : (∑ j, (I.Bloc t i j : ℝ) * d j) =
        (∑ j, (I.Bloc t i j : ℝ) * u₂ j) - (∑ j, (I.Bloc t i j : ℝ) * u₁ j) := by
      simp only [d, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    rw [hlin, hi1, hi2, sub_self]
  have hslack_pos : ∀ i ∈ S, 0 < slack i := fun i hi => by
    have hnot : i ∉ act u₁ := (Finset.mem_filter.mp hi).2
    have hne_rhs : (∑ j, (I.Bloc t i j : ℝ) * u₁ j) ≠ rhs i :=
      fun h => hnot ((hact_iff u₁ i).mpr h)
    have hle := hu₁_mem i
    dsimp only [slack]
    exact lt_of_le_of_ne (sub_nonneg.mpr hle) (fun h => hne_rhs (by linarith))
  let ε : ℝ := if hS : S.Nonempty then S.inf' hS stepRatio else 1
  have hε_pos : 0 < ε := by
    by_cases hS : S.Nonempty
    · simp only [ε, dif_pos hS, Finset.lt_inf'_iff]
      intro i hi
      exact div_pos (hslack_pos i hi) (by positivity)
    · simp [ε, dif_neg hS]
  have hε_bound : ∀ i ∈ S, ε * |∑ j, (I.Bloc t i j : ℝ) * d j| ≤ slack i := fun i hi => by
    have hS : S.Nonempty := ⟨i, hi⟩
    have hle : ε ≤ stepRatio i := by
      simp only [ε, dif_pos hS]
      exact Finset.inf'_le _ hi
    have hdenom : 0 < |∑ j, (I.Bloc t i j : ℝ) * d j| + 1 := by positivity
    calc ε * |∑ j, (I.Bloc t i j : ℝ) * d j|
      _ ≤ stepRatio i * |∑ j, (I.Bloc t i j : ℝ) * d j| :=
          mul_le_mul_of_nonneg_right hle (abs_nonneg _)
      _ ≤ stepRatio i * (|∑ j, (I.Bloc t i j : ℝ) * d j| + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (div_nonneg (hslack_pos i hi).le hdenom.le)
      _ = slack i := by
          dsimp only [stepRatio]
          exact div_mul_cancel₀ _ hdenom.ne'
  have hmem_pm : ∀ sgn : ℝ, |sgn| = 1 → u₁ + (sgn * ε) • d ∈ I.fiber t x := fun sgn hsgn i => by
    have hlin : (∑ j, (I.Aloc t i j : ℝ) * (x j : ℝ)) +
          (∑ j, (I.Bloc t i j : ℝ) * (u₁ + (sgn * ε) • d) j) =
        (I.bloc t i : ℝ) - slack i + sgn * (ε * ∑ j, (I.Bloc t i j : ℝ) * d j) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
        slack, rhs]
      have hmul : ∑ j, (I.Bloc t i j : ℝ) * (sgn * ε * d j) =
          sgn * (ε * ∑ j, (I.Bloc t i j : ℝ) * d j) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring
      rw [hmul]
      ring
    rw [hlin]
    by_cases hi : i ∈ act u₁
    · have hs0 : slack i = 0 := by
        dsimp only [slack]
        rw [(hact_iff u₁ i).mp hi, sub_self]
      rw [hd_zero i hi, hs0]
      linarith
    · have hiS : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
      have h1 : sgn * (ε * ∑ j, (I.Bloc t i j : ℝ) * d j) ≤
          ε * |∑ j, (I.Bloc t i j : ℝ) * d j| := by
        calc sgn * (ε * ∑ j, (I.Bloc t i j : ℝ) * d j)
          _ ≤ |sgn * (ε * ∑ j, (I.Bloc t i j : ℝ) * d j)| := le_abs_self _
          _ = |sgn| * (|ε| * |∑ j, (I.Bloc t i j : ℝ) * d j|) := by
              rw [abs_mul, abs_mul]
          _ = ε * |∑ j, (I.Bloc t i j : ℝ) * d j| := by
              rw [hsgn, one_mul, abs_of_pos hε_pos]
      linarith [hε_bound i hiS]
  let p₁ := u₁ + (1 * ε) • d
  let p₂ := u₁ + ((-1) * ε) • d
  have hp₁ : p₁ ∈ I.fiber t x := hmem_pm 1 (by norm_num)
  have hp₂ : p₂ ∈ I.fiber t x := hmem_pm (-1) (by norm_num)
  have hseg : u₁ ∈ openSegment ℝ p₁ p₂ := by
    rw [openSegment_eq_image]
    refine ⟨(1 / 2 : ℝ), ⟨by norm_num, by norm_num⟩, ?_⟩
    ext j
    simp only [p₁, p₂, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hp₁_eq : p₁ = u₁ := hu₁.2 hp₁ hp₂ hseg
  have hd0 : ε • d = 0 := by
    have : u₁ + ε • d = u₁ := by simpa [p₁] using hp₁_eq
    exact add_left_cancel (this.trans (add_zero u₁).symm)
  have hdz : d = 0 := (smul_eq_zero.mp hd0).resolve_left hε_pos.ne'
  exact hne (sub_eq_zero.mp hdz).symm

private lemma convexHull_extremePoints_fiber (I : Instance) (hI : I.Valid) (t : Fin I.τ)
    (x : Fin I.d → ℤ) :
    convexHull ℝ (Set.extremePoints ℝ (I.fiber t x)) = I.fiber t x := by
  have hcomp : IsCompact (convexHull ℝ (Set.extremePoints ℝ (I.fiber t x))) :=
    (finite_extremePoints_fiber I t x).isCompact_convexHull ℝ
  have hcl := closure_convexHull_extremePoints (isCompact_fiber I hI t x) (convex_fiber I t x)
  rwa [hcomp.isClosed.closure_eq] at hcl

private lemma finite_Vr (I : Instance) (hI : I.Valid) (t : Fin I.τ) (r : Residue I.d) :
    (I.Vr t r).Finite := by
  have hsub : I.Vr t r ⊆
      ⋃ x ∈ I.X t, (fun u => (x, u)) '' Set.extremePoints ℝ (I.fiber t x) := by
    intro g hg
    refine Set.mem_iUnion₂.mpr ⟨g.1, ?_, g.2, hg.2, rfl⟩
    exact ⟨g.toReal, hg.1.1, rfl⟩
  refine ((finite_X I hI t).biUnion fun x _ =>
    (finite_extremePoints_fiber I t x).image _).subset hsub

/-! ### 3. Expanding generators of `Sr` to `Vr` -/

private lemma expand_Sr_to_Vr (I : Instance) (hI : I.Valid) (t : Fin I.τ) (r : Residue I.d)
    {g : Gen I.d I.k} (hg : g ∈ I.Sr t r) :
    ∃ θ : Gen I.d I.k →₀ ℝ,
      IsFracRep (I.Vr t r) θ (g.toReal.1, g.toReal.2, 1) ∧
      (∀ v ∈ θ.support, v.1 = g.1) := by
  have hg_fib : g.2 ∈ convexHull ℝ (Set.extremePoints ℝ (I.fiber t g.1)) := by
    rw [convexHull_extremePoints_fiber I hI t g.1]
    exact hg.1
  rw [convexHull_eq] at hg_fib
  rcases hg_fib with ⟨ι, s, w, z, hw0, hw1, hz, hcm⟩
  let θ : Gen I.d I.k →₀ ℝ := ∑ i ∈ s, Finsupp.single (g.1, z i) (w i)
  refine ⟨θ, ?_, ?_⟩
  · have hterm : ∀ i ∈ s,
        IsFracRep (I.Vr t r) (Finsupp.single ((g.1, z i) : Gen I.d I.k) (w i))
          ((w i • Gen.toReal ((g.1, z i) : Gen I.d I.k)).1,
           (w i • Gen.toReal ((g.1, z i) : Gen I.d I.k)).2, w i) := by
      intro i hi
      refine isFracRep_single ?_ (hw0 i hi)
      refine ⟨⟨?_, hg.2⟩, hz i hi⟩
      change ((fun j => (g.1 j : ℝ)), z i) ∈ I.P t
      exact (hz i hi).1
    have hsum := isFracRep_sum s (fun i => Finsupp.single ((g.1, z i) : Gen I.d I.k) (w i))
      (fun i => ((w i • Gen.toReal ((g.1, z i) : Gen I.d I.k)).1,
                 (w i • Gen.toReal ((g.1, z i) : Gen I.d I.k)).2, w i)) hterm
    refine ⟨hsum.1, hsum.2.1, ?_, ?_⟩
    · rw [hsum.2.2.1]
      ext j
      · simp only [Prod.fst_sum, Prod.smul_fst, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
          Gen.toReal]
        rw [← Finset.sum_mul, hw1, one_mul]
      · simp only [Prod.snd_sum, Prod.fst_sum, Prod.smul_snd, Gen.toReal]
        have hcm_eq : s.centerMass w z = ∑ i ∈ s, w i • z i := by
          simp [Finset.centerMass, hw1]
        rw [← hcm_eq, hcm]
    · rw [hsum.2.2.2]
      simpa [Prod.snd_sum] using hw1
  · intro v hv
    have hv' := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hv)
    rcases hv' with ⟨i, _, hvi⟩
    have hveq : v = (g.1, z i) := Finset.mem_singleton.mp (Finsupp.support_single_subset hvi)
    rw [hveq]

private lemma expand_fracRep_Sr_to_Vr (I : Instance) (hI : I.Valid) (t : Fin I.τ) (r : Residue I.d)
    {θ : Gen I.d I.k →₀ ℝ} {ξ : Pt I.d I.k} (hθ : IsFracRep (I.Sr t r) θ ξ) :
    ∃ θ' : Gen I.d I.k →₀ ℝ,
      IsFracRep (I.Vr t r) θ' ξ ∧
      fracCost (I.f t) θ' = fracCost (I.f t) θ ∧
      (∀ φ : (Fin I.d → ℤ) → ℝ,
        θ'.sum (fun g c => c * φ g.1) = θ.sum (fun g c => c * φ g.1)) := by
  have hex : ∀ g : Gen I.d I.k, ∃ η : Gen I.d I.k →₀ ℝ,
      g ∈ θ.support →
        IsFracRep (I.Vr t r) η (g.toReal.1, g.toReal.2, 1) ∧
        (∀ v ∈ η.support, v.1 = g.1) := fun g => by
    by_cases hg : g ∈ θ.support
    · obtain ⟨η, h1, h2⟩ := expand_Sr_to_Vr I hI t r (hθ.1 hg)
      exact ⟨η, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hg⟩
  choose η hη using hex
  let θ' : Gen I.d I.k →₀ ℝ := ∑ g ∈ θ.support, (θ g) • η g
  have hterm : ∀ g ∈ θ.support,
      IsFracRep (I.Vr t r) ((θ g) • η g)
        ((θ g • g.toReal).1, (θ g • g.toReal).2, θ g) := fun g hg => by
    have h1 := isFracRep_smul (hθ.2.1 g) (hη g hg).1
    refine ⟨h1.1, h1.2.1, ?_, ?_⟩
    · rw [h1.2.2.1]; rfl
    · rw [h1.2.2.2]; simp
  have hsum := isFracRep_sum θ.support (fun g => (θ g) • η g)
    (fun g => ((θ g • g.toReal).1, (θ g • g.toReal).2, θ g)) hterm
  have hsum_ξ : (∑ g ∈ θ.support, ((θ g • g.toReal).1, (θ g • g.toReal).2, θ g)) = ξ := by
    have h1 := hθ.2.2.1
    have h2 := hθ.2.2.2
    unfold Finsupp.sum at h1 h2
    ext j
    · simp only [Prod.fst_sum, Prod.smul_fst, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have hj := congr_arg (fun p : (Fin I.d → ℝ) × (Fin I.k → ℝ) => p.1 j) h1
      simpa [Prod.fst_sum, Prod.smul_fst, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hj
    · simp only [Prod.snd_sum, Prod.fst_sum, Prod.smul_snd, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul]
      have hj := congr_arg (fun p : (Fin I.d → ℝ) × (Fin I.k → ℝ) => p.2 j) h1
      simpa [Prod.snd_sum, Prod.smul_snd, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hj
    · simp only [Prod.snd_sum]
      exact h2
  have hφ : ∀ φ : (Fin I.d → ℤ) → ℝ,
      θ'.sum (fun g c => c * φ g.1) = θ.sum (fun g c => c * φ g.1) := by
    intro φ
    have hsum_add : ∀ s : Finset (Gen I.d I.k), ∀ F : Gen I.d I.k → (Gen I.d I.k →₀ ℝ),
        (∑ x ∈ s, F x).sum (fun g c => c * φ g.1) =
          ∑ x ∈ s, (F x).sum (fun g c => c * φ g.1) := by
      intro s F
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha,
            Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring), ih]
    rw [show θ' = ∑ g ∈ θ.support, (θ g) • η g from rfl, hsum_add]
    unfold Finsupp.sum
    refine Finset.sum_congr rfl fun g hg => ?_
    have hsupp_smul : ((θ g) • η g).support ⊆ (η g).support := Finsupp.support_smul
    have heq0 : ∀ v ∈ (η g).support, v ∉ ((θ g) • η g).support →
        ((θ g • η g) v) * φ v.1 = 0 := fun v _ hv => by
      rw [Finsupp.notMem_support_iff.mp hv, zero_mul]
    rw [Finset.sum_subset hsupp_smul heq0]
    have h1 : ∀ v ∈ (η g).support, ((θ g • η g) v) * φ v.1 = (θ g * φ g.1) * (η g v) :=
      fun v hv => by
        rw [(hη g hg).2 v hv, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
        ring
    have hsum1 : (∑ x ∈ (η g).support, η g x) = 1 := (hη g hg).1.2.2.2
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, hsum1, mul_one]
  refine ⟨θ', ?_, ?_, hφ⟩
  · rwa [hsum_ξ] at hsum
  · exact hφ (fun x => I.f t (fun i => (x i : ℝ)))

/-! ### 4. Residue maps and `Phi 0 = 0` -/

private def resOf {d : ℕ} (x : Fin d → ℤ) : Residue d :=
  fun i => ⟨(x i % (2 ^ d : ℤ)).toNat, by
    have hpos : (0 : ℤ) < (2 ^ d : ℤ) := by positivity
    have h1 : 0 ≤ x i % (2 ^ d : ℤ) := Int.emod_nonneg _ hpos.ne'
    have h2 : x i % (2 ^ d : ℤ) < ((2 ^ d : ℕ) : ℤ) := by
      simpa using Int.emod_lt_of_pos (x i) hpos
    exact Int.toNat_lt h1 |>.mpr (by exact_mod_cast h2)⟩

private lemma resOf_spec {d : ℕ} (x : Fin d → ℤ) (i : Fin d) :
    x i ≡ ((resOf x i : ℕ) : ℤ) [ZMOD 2 ^ d] := by
  have hpos : (0 : ℤ) < (2 ^ d : ℤ) := by positivity
  have hnonneg : 0 ≤ x i % (2 ^ d : ℤ) := Int.emod_nonneg _ hpos.ne'
  change x i % (2 ^ d : ℤ) = (((x i % (2 ^ d : ℤ)).toNat : ℤ) % (2 ^ d : ℤ))
  rw [Int.toNat_of_nonneg hnonneg, Int.emod_emod]

private def aVec {d : ℕ} (r : Residue d) (x : Fin d → ℤ) : Fin d → ℤ :=
  fun i => (x i - (r i : ℕ)) / (2 ^ d : ℤ)

private lemma eq_r_add_two_pow_mul_aVec {d : ℕ} {r : Residue d} {x : Fin d → ℤ}
    (hx : ∀ i, x i ≡ ((r i : ℕ) : ℤ) [ZMOD 2 ^ d]) (i : Fin d) :
    x i = ((r i : ℕ) : ℤ) + (2 ^ d : ℤ) * aVec r x i := by
  have hmod : x i ≡ ((r i : ℕ) : ℤ) [ZMOD (2 ^ d : ℤ)] := by simpa using hx i
  have hdvd : (2 ^ d : ℤ) ∣ x i - (r i : ℕ) := Int.modEq_iff_dvd.mp hmod.symm
  have hmul : (2 ^ d : ℤ) * aVec r x i = x i - (r i : ℕ) := Int.mul_ediv_cancel' hdvd
  linarith

private lemma Phi_zero (I : Instance) (t : Fin I.τ) (r : Residue I.d) :
    I.Phi t r 0 = 0 := by
  unfold Instance.Phi
  refine le_antisymm ?_ ?_
  · refine iInf₂_le_of_le 0 ?_ (by simp [fracCost])
    refine ⟨by simp, by simp, by ext <;> simp, by simp⟩
  · refine le_iInf₂ fun θ hθ => ?_
    have hθ0 : ∀ g, θ g = 0 := fun g => by
      by_contra hne
      have hg : g ∈ θ.support := Finsupp.mem_support_iff.mpr hne
      have hpos : 0 < θ g := lt_of_le_of_ne (hθ.2.1 g) (Ne.symm hne)
      have hle : θ g ≤ ∑ x ∈ θ.support, θ x :=
        Finset.single_le_sum (fun x _ => hθ.2.1 x) hg
      have hsum : (∑ x ∈ θ.support, θ x) = 0 := hθ.2.2.2
      linarith
    have hcost0 : fracCost (I.f t) θ = 0 := by
      simp [fracCost, Finsupp.sum, hθ0]
    rw [hcost0]
    simp

/-! ### 5. One-block integer reconstruction (Soundness of `K_R(γ)` / Lemma 6) -/

private lemma list_count_sum {α M : Type*} [BEq α] [LawfulBEq α] [AddCommMonoid M]
    (l : List α) (S : Finset α) (hl : ∀ g ∈ l, g ∈ S) (F : α → M) :
    (l.map F).sum = ∑ g ∈ S, (l.count g) • F g := by
  classical
  induction l with
  | nil => simp
  | cons a tl ih =>
      have htl := ih (fun g hg => hl g (List.mem_cons_of_mem a hg))
      have ha : a ∈ S := hl a List.mem_cons_self
      simp only [List.map_cons, List.sum_cons, htl]
      have hcnt : ∀ g ∈ S, (a :: tl).count g = tl.count g + (if g = a then 1 else 0) :=
        fun g _ => by
          rw [List.count_cons]
          by_cases hga : a = g
          · subst hga; simp
          · simp [beq_false_of_ne hga, Ne.symm hga]
      calc F a + ∑ g ∈ S, tl.count g • F g
        _ = (∑ g ∈ S, (if g = a then (1 : ℕ) else 0) • F g) +
              ∑ g ∈ S, tl.count g • F g := by
            congr 1
            have hite : (∑ g ∈ S, if g = a then F g else 0) = F a := by
              rw [Finset.sum_ite_eq' S a F, if_pos ha]
            rw [← hite]
            refine Finset.sum_congr rfl fun g _ => by split_ifs <;> simp
        _ = ∑ g ∈ S, ((if g = a then (1 : ℕ) else 0) + tl.count g) • F g := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun g _ => (add_smul _ _ _).symm
        _ = ∑ g ∈ S, (a :: tl).count g • F g := by
            refine Finset.sum_congr rfl fun g hg => ?_
            rw [hcnt g hg, add_comm]

private lemma list_map_sum_toList {α M : Type*} [AddCommMonoid M] (S : Finset α) (f : α → M) :
    (S.toList.map f).sum = ∑ x ∈ S, f x := by
  let _ : BEq α := instBEqOfDecidableEq
  have hl : ∀ g ∈ S.toList, g ∈ S := fun g hg => Finset.mem_toList.mp hg
  rw [list_count_sum S.toList S hl f]
  refine Finset.sum_congr rfl fun g hg => ?_
  have hcnt : S.toList.count g = 1 :=
    List.count_eq_one_of_mem S.nodup_toList (Finset.mem_toList.mpr hg)
  rw [hcnt, one_smul]

private lemma list_chunk_sum {α M : Type*} [BEq α] [LawfulBEq α] [AddCommMonoid M]
    (l : List α) (S : Finset α) (hl : ∀ g ∈ l, g ∈ S)
    {a b : ℕ} (hle : a * b = l.length) (F : α → M) :
    ∑ j : Fin a, ∑ m : Fin b, F (l.get ((finProdFinEquiv (j, m)).cast hle)) =
      ∑ g ∈ S, (l.count g) • F g := by
  rw [← list_count_sum l S hl F]
  have hprod : ∑ j : Fin a, ∑ m : Fin b, F (l.get ((finProdFinEquiv (j, m)).cast hle)) =
      ∑ p : Fin a × Fin b, F (l.get ((finProdFinEquiv p).cast hle)) :=
    (Fintype.sum_prod_type
      (fun p : Fin a × Fin b => F (l.get ((finProdFinEquiv p).cast hle)))).symm
  rw [hprod]
  let e : Fin a × Fin b ≃ Fin l.length := finProdFinEquiv.trans (finCongr hle)
  have hcomp : ∑ p : Fin a × Fin b, F (l.get (e p)) =
      ∑ idx : Fin l.length, F (l.get idx) :=
    Equiv.sum_comp e (fun idx => F (l.get idx))
  change ∑ p : Fin a × Fin b, F (l.get (e p)) = (l.map F).sum
  rw [hcomp, ← List.sum_ofFn]
  congr 1
  exact List.ext_get (by simp) (fun i hi1 hi2 => by simp)

private lemma block_reconstruct (I : Instance) (hI : I.Valid) (t : Fin I.τ) (r : Residue I.d)
    (z : Fin I.d → ℤ) (w : Fin I.k → ℝ) (n : ℕ)
    (hCr : ((fun j => (z j : ℝ)), w, (n : ℝ)) ∈ I.Cr t r) :
    ∃ μ_blk : Gen I.d I.k →₀ ℕ,
      (↑μ_blk.support : Set (Gen I.d I.k)) ⊆ I.S t ∧
      aggr μ_blk = ((fun j => (z j : ℝ)), w) ∧
      count μ_blk = n ∧
      ((costOf (I.f t) μ_blk : ℝ) : EReal) ≤ I.Phi t r ((fun j => (z j : ℝ)), w, (n : ℝ)) := by
  by_cases hn0 : n = 0
  · subst hn0
    have hz0 : ((fun j => (z j : ℝ)), w, (0 : ℝ)) = 0 := by
      rcases hCr with h | h
      · simp only [Nat.cast_zero] at h
        exact Set.mem_singleton_iff.mp h
      · simp at h
    refine ⟨0, by simp, ?_, count_zero, ?_⟩
    · have hzw : ((fun j => (z j : ℝ)), w) = 0 := by
        ext j
        · exact congr_arg (fun p : Pt I.d I.k => p.1 j) hz0
        · exact congr_arg (fun p : Pt I.d I.k => p.2.1 j) hz0
      rw [hzw, aggr_zero]
    · have hz0' : ((fun j => (z j : ℝ)), w, ((0 : ℕ) : ℝ)) = 0 := by simpa using hz0
      rw [hz0', Phi_zero, costOf_zero]
      simp
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
  have hnR_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
  let ξ : Pt I.d I.k := ((fun j => (z j : ℝ)), w, (n : ℝ))
  -- Step 3a: Compact attainment on `I.Vr t r`
  let V : Finset (Gen I.d I.k) := (finite_Vr I hI t r).toFinset
  have hV_mem : ∀ v : V, v.1 ∈ I.Vr t r := fun v =>
    (finite_Vr I hI t r).mem_toFinset.mp v.2
  let F : Set (V → ℝ) := {c | (∀ v, 0 ≤ c v) ∧ (∑ v : V, c v = (n : ℝ)) ∧
    (∑ v : V, c v • v.1.toReal = ((fun j => (z j : ℝ)), w))}
  have hCr_pos : ((n : ℝ)⁻¹ • ξ.1, (n : ℝ)⁻¹ • ξ.2.1) ∈ I.Pr t r := by
    rcases hCr with h0 | hpos
    · exfalso
      have := congr_arg (fun p : Pt I.d I.k => p.2.2) h0
      simp at this
      exact hn0 this
    · exact hpos.2
  have hF_nonempty : F.Nonempty := by
    have hPr := hCr_pos
    rw [Instance.Pr, convexHull_eq] at hPr
    rcases hPr with ⟨ι, s, wts, pts, hw0, hw1, hpts, hcm⟩
    choose g hgSr hg_eq using fun i (hi : i ∈ s) => hpts i hi
    let θ_sr : Gen I.d I.k →₀ ℝ :=
      ∑ i ∈ s, if hi : i ∈ s then Finsupp.single (g i hi) ((n : ℝ) * wts i) else 0
    have hθ_sr_rep : IsFracRep (I.Sr t r) θ_sr ξ := by
      have hterm : ∀ i ∈ s, IsFracRep (I.Sr t r)
          (if hi : i ∈ s then Finsupp.single (g i hi) ((n : ℝ) * wts i) else 0)
          (if hi : i ∈ s then
            ((((n : ℝ) * wts i) • (g i hi).toReal).1,
             (((n : ℝ) * wts i) • (g i hi).toReal).2, (n : ℝ) * wts i) else 0) := by
        intro i hi
        simp only [dif_pos hi]
        exact isFracRep_single (hgSr i hi) (mul_nonneg hnR_pos.le (hw0 i hi))
      have hsum := isFracRep_sum s _ _ hterm
      refine ⟨hsum.1, hsum.2.1, ?_, ?_⟩
      · rw [hsum.2.2.1]
        have hcm' : (∑ i ∈ s, wts i • pts i) = ((n : ℝ)⁻¹ • ξ.1, (n : ℝ)⁻¹ • ξ.2.1) := by
          simpa [Finset.centerMass, hw1] using hcm
        have hsum_eq1 :
            (∑ i ∈ s, if hi : i ∈ s then
              ((((n : ℝ) * wts i) • (g i hi).toReal).1,
               (((n : ℝ) * wts i) • (g i hi).toReal).2, (n : ℝ) * wts i) else 0).1 =
            (n : ℝ) • (∑ i ∈ s, wts i • pts i).1 := by
          ext j
          simp only [Prod.fst_sum, Prod.smul_fst, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [dif_pos hi]
          simp only [Pi.smul_apply, smul_eq_mul]
          have h1 : (g i hi).toReal.1 j = (pts i).1 j :=
            congr_arg (fun p : (Fin I.d → ℝ) × (Fin I.k → ℝ) => p.1 j) (hg_eq i hi)
          rw [h1]
          ring
        have hsum_eq2 :
            (∑ i ∈ s, if hi : i ∈ s then
              ((((n : ℝ) * wts i) • (g i hi).toReal).1,
               (((n : ℝ) * wts i) • (g i hi).toReal).2, (n : ℝ) * wts i) else 0).2.1 =
            (n : ℝ) • (∑ i ∈ s, wts i • pts i).2 := by
          ext j
          simp only [Prod.snd_sum, Prod.fst_sum, Prod.smul_snd, Finset.sum_apply,
            Pi.smul_apply, smul_eq_mul]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [dif_pos hi]
          simp only [Pi.smul_apply, smul_eq_mul]
          have h2 : (g i hi).toReal.2 j = (pts i).2 j :=
            congr_arg (fun p : (Fin I.d → ℝ) × (Fin I.k → ℝ) => p.2 j) (hg_eq i hi)
          rw [h2]
          ring
        ext j
        · have h1 := congr_arg (fun f : Fin I.d → ℝ => f j) hsum_eq1
          rw [hcm'] at h1
          simpa [ξ, hnR_pos.ne'] using h1
        · have h2 := congr_arg (fun f : Fin I.k → ℝ => f j) hsum_eq2
          rw [hcm'] at h2
          simpa [ξ, hnR_pos.ne'] using h2
      · rw [hsum.2.2.2]
        have hsum_eq3 :
            (∑ i ∈ s, if hi : i ∈ s then
              ((((n : ℝ) * wts i) • (g i hi).toReal).1,
               (((n : ℝ) * wts i) • (g i hi).toReal).2, (n : ℝ) * wts i) else 0).2.2 =
            ∑ i ∈ s, (n : ℝ) * wts i := by
          simp only [Prod.snd_sum]
          refine Finset.sum_congr rfl fun i hi => by simp [dif_pos hi]
        rw [hsum_eq3, ← Finset.mul_sum, hw1, mul_one]
    obtain ⟨θ_V, hθV, _, _⟩ := expand_fracRep_Sr_to_Vr I hI t r hθ_sr_rep
    refine ⟨fun v => θ_V v.1, ?_, ?_, ?_⟩
    · exact fun v => hθV.2.1 v.1
    · have hsub : θ_V.support ⊆ V := fun g hg => (finite_Vr I hI t r).mem_toFinset.mpr (hθV.1 hg)
      calc ∑ v : V, θ_V v.1
        _ = ∑ g ∈ V, θ_V g := (Finset.sum_coe_sort V (fun g => θ_V g))
        _ = ∑ g ∈ θ_V.support, θ_V g :=
            (Finset.sum_subset hsub (fun g _ hg => Finsupp.notMem_support_iff.mp hg)).symm
        _ = (n : ℝ) := hθV.2.2.2
    · have hsub : θ_V.support ⊆ V := fun g hg => (finite_Vr I hI t r).mem_toFinset.mpr (hθV.1 hg)
      calc ∑ v : V, θ_V v.1 • v.1.toReal
        _ = ∑ g ∈ V, θ_V g • g.toReal := Finset.sum_coe_sort V (fun g => θ_V g • g.toReal)
        _ = ∑ g ∈ θ_V.support, θ_V g • g.toReal :=
            (Finset.sum_subset hsub (fun g _ hg => by
              simp [Finsupp.notMem_support_iff.mp hg])).symm
        _ = ((fun j => (z j : ℝ)), w) := hθV.2.2.1
  have hF_closed : IsClosed F := by
    have h1 : IsClosed {c : V → ℝ | ∀ v, 0 ≤ c v} := by
      rw [Set.ofPred_forall]
      exact isClosed_iInter fun v => isClosed_le continuous_const (continuous_apply v)
    have h2 : IsClosed {c : V → ℝ | ∑ v : V, c v = (n : ℝ)} :=
      isClosed_eq (continuous_finsetSum _ fun v _ => continuous_apply v) continuous_const
    have h3 : IsClosed {c : V → ℝ | ∑ v : V, c v • v.1.toReal = ((fun j => (z j : ℝ)), w)} :=
      isClosed_eq
        (continuous_finsetSum _ fun v _ => (continuous_apply v).smul continuous_const)
        continuous_const
    exact h1.inter (h2.inter h3)
  have hF_bdd : Bornology.IsBounded F := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨(n : ℝ), fun c hc => ?_⟩
    rw [pi_norm_le_iff_of_nonneg hnR_pos.le]
    intro v
    rw [Real.norm_eq_abs, abs_of_nonneg (hc.1 v)]
    calc c v ≤ ∑ u : V, c u := Finset.single_le_sum (fun u _ => hc.1 u) (Finset.mem_univ v)
      _ = (n : ℝ) := hc.2.1
  have hF_compact : IsCompact F := Metric.isCompact_of_isClosed_isBounded hF_closed hF_bdd
  let J₁ : (V → ℝ) → ℝ := fun c => ∑ v : V, c v * I.f t (fun j => (v.1.1 j : ℝ))
  have hJ₁_cont : Continuous J₁ :=
    continuous_finsetSum _ fun v _ => (continuous_apply v).mul continuous_const
  obtain ⟨c₁, hc₁F, hc₁_min⟩ := hF_compact.exists_isMinOn hF_nonempty hJ₁_cont.continuousOn
  let Φstar : ℝ := J₁ c₁
  let potGen : (Fin I.d → ℤ) → ℝ := fun x => ∑ j : Fin I.d, (aVec r x j : ℝ) ^ 2
  let J₂ : (V → ℝ) → ℝ := fun c => ∑ v : V, c v * potGen v.1.1
  have hJ₂_cont : Continuous J₂ :=
    continuous_finsetSum _ fun v _ => (continuous_apply v).mul continuous_const
  let F_opt : Set (V → ℝ) := F ∩ {c | J₁ c = Φstar}
  have hF_opt_nonempty : F_opt.Nonempty := ⟨c₁, hc₁F, rfl⟩
  have hF_opt_compact : IsCompact F_opt :=
    hF_compact.inter_right (isClosed_eq hJ₁_cont continuous_const)
  obtain ⟨cstar, hcstar_mem, hcstar_min⟩ :=
    hF_opt_compact.exists_isMinOn hF_opt_nonempty hJ₂_cont.continuousOn
  let θ₀ : Gen I.d I.k →₀ ℝ := ∑ v : V, Finsupp.single v.1 (cstar v)
  have hθ₀_coeff : ∀ v : V, θ₀ v.1 = cstar v := fun v => by
    have heq : (∑ u : V, Finsupp.single u.1 (cstar u)) v.1 = cstar v := by
      simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
      rw [Finset.sum_eq_single v]
      · simp
      · intro u _ huv
        have hne : u.1 ≠ v.1 := fun h => huv (Subtype.ext h)
        simp [hne]
      · intro hv
        exact absurd (Finset.mem_univ v) hv
    exact heq
  have hθ₀_rep : IsFracRep (I.Vr t r) θ₀ ξ := by
    have hterm : ∀ v ∈ (Finset.univ : Finset V),
        IsFracRep (I.Vr t r) (Finsupp.single v.1 (cstar v))
          ((cstar v • v.1.toReal).1, (cstar v • v.1.toReal).2, cstar v) := fun v _ =>
      isFracRep_single (hV_mem v) (hcstar_mem.1.1 v)
    have hsum := isFracRep_sum (Finset.univ : Finset V) _ _ hterm
    refine ⟨hsum.1, hsum.2.1, ?_, ?_⟩
    · rw [hsum.2.2.1]
      have h1 := hcstar_mem.1.2.2
      ext j
      · simpa [Prod.fst_sum] using congr_arg (fun p : (Fin I.d → ℝ) × (Fin I.k → ℝ) => p.1 j) h1
      · simpa [Prod.snd_sum, Prod.fst_sum] using
          congr_arg (fun p : (Fin I.d → ℝ) × (Fin I.k → ℝ) => p.2 j) h1
    · rw [hsum.2.2.2]
      simpa [Prod.snd_sum] using hcstar_mem.1.2.1
  have hθ₀_cost : fracCost (I.f t) θ₀ = Φstar := by
    unfold θ₀
    rw [fracCost_sum]
    simp_rw [fracCost_single]
    exact hcstar_mem.2
  have hΦ_eq : I.Phi t r ξ = ((Φstar : ℝ) : EReal) := by
    unfold Instance.Phi
    refine le_antisymm ?_ ?_
    · exact iInf₂_le_of_le θ₀ hθ₀_rep (by rw [hθ₀_cost])
    · refine le_iInf₂ fun θ hθ => ?_
      have hsub : θ.support ⊆ V := fun g hg => (finite_Vr I hI t r).mem_toFinset.mpr (hθ.1 hg)
      let c : V → ℝ := fun v => θ v.1
      have hcF : c ∈ F := by
        refine ⟨fun v => hθ.2.1 v.1, ?_, ?_⟩
        · calc ∑ v : V, θ v.1
            _ = ∑ g ∈ V, θ g := Finset.sum_coe_sort V (fun g => θ g)
            _ = ∑ g ∈ θ.support, θ g :=
                (Finset.sum_subset hsub (fun g _ hg => Finsupp.notMem_support_iff.mp hg)).symm
            _ = (n : ℝ) := hθ.2.2.2
        · calc ∑ v : V, θ v.1 • v.1.toReal
            _ = ∑ g ∈ V, θ g • g.toReal := Finset.sum_coe_sort V (fun g => θ g • g.toReal)
            _ = ∑ g ∈ θ.support, θ g • g.toReal :=
                (Finset.sum_subset hsub (fun g _ hg => by
                  simp [Finsupp.notMem_support_iff.mp hg])).symm
            _ = ((fun j => (z j : ℝ)), w) := hθ.2.2.1
      have hcost_c : J₁ c = fracCost (I.f t) θ := by
        dsimp only [J₁, c, fracCost, Finsupp.sum]
        calc ∑ v : V, θ v.1 * I.f t (fun j => (v.1.1 j : ℝ))
          _ = ∑ g ∈ V, θ g * I.f t (fun j => (g.1 j : ℝ)) :=
              Finset.sum_coe_sort V (fun g => θ g * I.f t (fun j => (g.1 j : ℝ)))
          _ = ∑ g ∈ θ.support, θ g * I.f t (fun j => (g.1 j : ℝ)) :=
              (Finset.sum_subset hsub (fun g _ hg => by
                simp [Finsupp.notMem_support_iff.mp hg])).symm
      rw [EReal.coe_le_coe_iff, ← hcost_c]
      exact hc₁_min hcF
  have hθ₀_pot_val : θ₀.sum (fun g c => c * potGen g.1) = J₂ cstar := by
    have hsub : θ₀.support ⊆ V := fun g hg => (finite_Vr I hI t r).mem_toFinset.mpr (hθ₀_rep.1 hg)
    unfold Finsupp.sum
    calc ∑ g ∈ θ₀.support, θ₀ g * potGen g.1
      _ = ∑ g ∈ V, θ₀ g * potGen g.1 :=
          Finset.sum_subset hsub (fun g _ hg => by simp [Finsupp.notMem_support_iff.mp hg])
      _ = ∑ v : V, θ₀ v.1 * potGen v.1.1 :=
          (Finset.sum_coe_sort V (fun g => θ₀ g * potGen g.1)).symm
      _ = J₂ cstar := by
          dsimp only [J₂]
          refine Finset.sum_congr rfl fun v _ => by rw [hθ₀_coeff v]
  have hglobal_opt : ∀ θ : Gen I.d I.k →₀ ℝ, IsFracRep (I.Sr t r) θ ξ →
      Φstar ≤ fracCost (I.f t) θ ∧
      (fracCost (I.f t) θ = Φstar →
        θ₀.sum (fun g c => c * potGen g.1) ≤ θ.sum (fun g c => c * potGen g.1)) := by
    intro θ hθ
    obtain ⟨θ', hθ'rep, hθ'cost, hθ'φ⟩ := expand_fracRep_Sr_to_Vr I hI t r hθ
    have hsub : θ'.support ⊆ V := fun g hg => (finite_Vr I hI t r).mem_toFinset.mpr (hθ'rep.1 hg)
    let c : V → ℝ := fun v => θ' v.1
    have hcF : c ∈ F := by
      refine ⟨fun v => hθ'rep.2.1 v.1, ?_, ?_⟩
      · calc ∑ v : V, θ' v.1
          _ = ∑ g ∈ V, θ' g := Finset.sum_coe_sort V (fun g => θ' g)
          _ = ∑ g ∈ θ'.support, θ' g :=
              (Finset.sum_subset hsub (fun g _ hg => Finsupp.notMem_support_iff.mp hg)).symm
          _ = (n : ℝ) := hθ'rep.2.2.2
      · calc ∑ v : V, θ' v.1 • v.1.toReal
          _ = ∑ g ∈ V, θ' g • g.toReal := Finset.sum_coe_sort V (fun g => θ' g • g.toReal)
          _ = ∑ g ∈ θ'.support, θ' g • g.toReal :=
              (Finset.sum_subset hsub (fun g _ hg => by
                simp [Finsupp.notMem_support_iff.mp hg])).symm
          _ = ((fun j => (z j : ℝ)), w) := hθ'rep.2.2.1
    have hJ₁c : J₁ c = fracCost (I.f t) θ := by
      rw [← hθ'cost]
      dsimp only [J₁, c, fracCost, Finsupp.sum]
      calc ∑ v : V, θ' v.1 * I.f t (fun j => (v.1.1 j : ℝ))
        _ = ∑ g ∈ V, θ' g * I.f t (fun j => (g.1 j : ℝ)) :=
            Finset.sum_coe_sort V (fun g => θ' g * I.f t (fun j => (g.1 j : ℝ)))
        _ = ∑ g ∈ θ'.support, θ' g * I.f t (fun j => (g.1 j : ℝ)) :=
            (Finset.sum_subset hsub (fun g _ hg => by
              simp [Finsupp.notMem_support_iff.mp hg])).symm
    refine ⟨hJ₁c ▸ hc₁_min hcF, fun hcost_eq => ?_⟩
    have hc_opt : c ∈ F_opt := ⟨hcF, hJ₁c.trans hcost_eq⟩
    have hJ₂c : J₂ c = θ.sum (fun g c => c * potGen g.1) := by
      rw [← hθ'φ potGen]
      dsimp only [J₂, c, Finsupp.sum]
      calc ∑ v : V, θ' v.1 * potGen v.1.1
        _ = ∑ g ∈ V, θ' g * potGen g.1 := Finset.sum_coe_sort V (fun g => θ' g * potGen g.1)
        _ = ∑ g ∈ θ'.support, θ' g * potGen g.1 :=
            (Finset.sum_subset hsub (fun g _ hg => by
              simp [Finsupp.notMem_support_iff.mp hg])).symm
    rw [hθ₀_pot_val, ← hJ₂c]
    exact hcstar_min hc_opt
  -- Step 3b: Collapse same-`x` generators and reduce support to `≤ 2^d`
  let Xsupp := θ₀.support.image Prod.fst
  let Wx : (Fin I.d → ℤ) → ℝ := fun x => ∑ g ∈ θ₀.support.filter (fun g => g.1 = x), θ₀ g
  let ux : (Fin I.d → ℤ) → (Fin I.k → ℝ) := fun x =>
    (Wx x)⁻¹ • ∑ g ∈ θ₀.support.filter (fun g => g.1 = x), θ₀ g • g.2
  have hWx_pos : ∀ x ∈ Xsupp, 0 < Wx x := fun x hx => by
    rw [Finset.mem_image] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    have hpos : 0 < θ₀ g :=
      lt_of_le_of_ne (hθ₀_rep.2.1 g) (Ne.symm (Finsupp.mem_support_iff.mp hg))
    exact lt_of_lt_of_le hpos (Finset.single_le_sum (fun y _ => hθ₀_rep.2.1 y)
      (Finset.mem_filter.mpr ⟨hg, rfl⟩))
  have hgx_Sr : ∀ x ∈ Xsupp, (x, ux x) ∈ I.Sr t r := fun x hx => by
    let Sx := θ₀.support.filter (fun g => g.1 = x)
    have hWpos := hWx_pos x hx
    have hmemP : ∀ g ∈ Sx, g.toReal ∈ I.P t := fun g hg =>
      (hθ₀_rep.1 (Finset.mem_filter.mp hg).1).1.1
    have hcm := (convex_P I t).centerMass_mem (fun g _ => hθ₀_rep.2.1 g) (by
      simpa [Sx, Wx] using hWpos) hmemP
    have hcm_eq : Sx.centerMass (fun g => θ₀ g) Gen.toReal =
        Gen.toReal ((x, ux x) : Gen I.d I.k) := by
      simp only [Finset.centerMass, show (∑ g ∈ Sx, θ₀ g) = Wx x from rfl]
      ext j
      · simp only [Prod.smul_fst, Prod.fst_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
          Gen.toReal]
        have hid : (∑ g ∈ Sx, θ₀ g * (g.1 j : ℝ)) = Wx x * (x j : ℝ) := by
          dsimp only [Wx]
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun g hg => ?_
          rw [(Finset.mem_filter.mp hg).2]
        rw [hid, inv_mul_cancel_left₀ hWpos.ne']
      · simp only [Prod.smul_snd, Prod.snd_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
          Gen.toReal, ux, Sx]
    have hP : Gen.toReal ((x, ux x) : Gen I.d I.k) ∈ I.P t := by rw [← hcm_eq]; exact hcm
    obtain ⟨g, hg, hgx⟩ := Finset.mem_image.mp hx
    have hmod := (hθ₀_rep.1 hg).1.2
    refine ⟨hP, fun i => ?_⟩
    simpa [hgx] using hmod i
  let θ : Gen I.d I.k →₀ ℝ := ∑ x ∈ Xsupp, Finsupp.single (x, ux x) (Wx x)
  have hfiber_sum : ∀ {M : Type} [AddCommMonoid M] (F : Gen I.d I.k → M),
      ∑ x ∈ Xsupp, ∑ g ∈ θ₀.support.filter (fun g => g.1 = x), F g =
        ∑ g ∈ θ₀.support, F g := fun F =>
    Finset.sum_fiberwise_of_maps_to (s := θ₀.support) (t := Xsupp) (g := Prod.fst)
      (fun g hg => Finset.mem_image_of_mem _ hg) F
  have hθ_rep : IsFracRep (I.Sr t r) θ ξ := by
    have hterm : ∀ x ∈ Xsupp, IsFracRep (I.Sr t r) (Finsupp.single (x, ux x) (Wx x))
        ((Wx x • Gen.toReal ((x, ux x) : Gen I.d I.k)).1,
         (Wx x • Gen.toReal ((x, ux x) : Gen I.d I.k)).2, Wx x) := fun x hx =>
      isFracRep_single (hgx_Sr x hx) (hWx_pos x hx).le
    have hsum := isFracRep_sum Xsupp _ _ hterm
    refine ⟨hsum.1, hsum.2.1, ?_, ?_⟩
    · rw [hsum.2.2.1, ← hθ₀_rep.2.2.1]
      have hterm_aggr : ∀ x ∈ Xsupp,
          Wx x • Gen.toReal ((x, ux x) : Gen I.d I.k) =
            ∑ g ∈ θ₀.support.filter (fun g => g.1 = x), θ₀ g • g.toReal := fun x hx => by
        have hWne := (hWx_pos x hx).ne'
        ext j
        · simp only [Prod.smul_fst, Prod.fst_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
            Gen.toReal, Wx]
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun g hg => ?_
          rw [(Finset.mem_filter.mp hg).2]
        · simp only [Prod.smul_snd, Prod.snd_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
            Gen.toReal, ux]
          rw [mul_inv_cancel_left₀ hWne]
      have heq1 : (∑ x ∈ Xsupp, ((Wx x • Gen.toReal ((x, ux x) : Gen I.d I.k)).1,
            (Wx x • Gen.toReal ((x, ux x) : Gen I.d I.k)).2, Wx x)).1 =
          (∑ x ∈ Xsupp, Wx x • Gen.toReal ((x, ux x) : Gen I.d I.k)).1 := by
        simp [Prod.fst_sum]
      have heq2 : (∑ x ∈ Xsupp, ((Wx x • Gen.toReal ((x, ux x) : Gen I.d I.k)).1,
            (Wx x • Gen.toReal ((x, ux x) : Gen I.d I.k)).2, Wx x)).2.1 =
          (∑ x ∈ Xsupp, Wx x • Gen.toReal ((x, ux x) : Gen I.d I.k)).2 := by
        simp [Prod.snd_sum, Prod.fst_sum]
      ext j
      · rw [heq1, Finset.sum_congr rfl hterm_aggr, hfiber_sum]; rfl
      · rw [heq2, Finset.sum_congr rfl hterm_aggr, hfiber_sum]; rfl
    · rw [hsum.2.2.2, ← hθ₀_rep.2.2.2]
      simpa [Prod.snd_sum, Wx, Finsupp.sum] using hfiber_sum (fun g => θ₀ g)
  have hθ_sum_φ : ∀ φ : (Fin I.d → ℤ) → ℝ,
      θ.sum (fun g c => c * φ g.1) = θ₀.sum (fun g c => c * φ g.1) := by
    intro φ
    have hsum_add : ∀ s : Finset (Fin I.d → ℤ), ∀ F : (Fin I.d → ℤ) → (Gen I.d I.k →₀ ℝ),
        (∑ x ∈ s, F x).sum (fun g c => c * φ g.1) =
          ∑ x ∈ s, (F x).sum (fun g c => c * φ g.1) := by
      intro s F
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha,
            Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring), ih]
    rw [show θ = ∑ x ∈ Xsupp, Finsupp.single (x, ux x) (Wx x) from rfl, hsum_add]
    have h1 : ∀ x ∈ Xsupp, (Finsupp.single (x, ux x) (Wx x)).sum (fun g c => c * φ g.1) =
        ∑ g ∈ θ₀.support.filter (fun g => g.1 = x), θ₀ g * φ g.1 := fun x _ => by
      rw [Finsupp.sum_single_index (by simp)]
      dsimp only [Wx]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun g hg => ?_
      rw [(Finset.mem_filter.mp hg).2]
    rw [Finset.sum_congr rfl h1]
    exact hfiber_sum (fun g => θ₀ g * φ g.1)
  have hθ_cost : fracCost (I.f t) θ = Φstar := by
    rw [show fracCost (I.f t) θ = θ.sum (fun g c => c * I.f t (fun i => (g.1 i : ℝ))) from rfl,
      hθ_sum_φ (fun x => I.f t (fun i => (x i : ℝ))), ← hθ₀_cost]
    rfl
  have hθ_pot : θ.sum (fun g c => c * potGen g.1) = θ₀.sum (fun g c => c * potGen g.1) :=
    hθ_sum_φ potGen
  have hθ_inj : ∀ g₁ ∈ θ.support, ∀ g₂ ∈ θ.support, g₁ ≠ g₂ → g₁.1 ≠ g₂.1 := by
    intro g₁ hg₁ g₂ hg₂ hne heq1
    have h1 := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hg₁)
    have h2 := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hg₂)
    obtain ⟨x₁, _, hgx₁⟩ := h1
    obtain ⟨x₂, _, hgx₂⟩ := h2
    have hge1 : g₁ = (x₁, ux x₁) := Finset.mem_singleton.mp (Finsupp.support_single_subset hgx₁)
    have hge2 : g₂ = (x₂, ux x₂) := Finset.mem_singleton.mp (Finsupp.support_single_subset hgx₂)
    have hxeq : x₁ = x₂ := by
      have h1' : g₁.1 = x₁ := by rw [hge1]
      have h2' : g₂.1 = x₂ := by rw [hge2]
      rw [← h1', ← h2', heq1]
    exact hne (by rw [hge1, hge2, hxeq])
  have hθ_card : θ.support.card ≤ 2 ^ I.d := by
    by_contra hcard
    have hlt : (Finset.univ : Finset (Fin I.d → Bool)).card < θ.support.card := by
      simpa [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using Nat.lt_of_not_ge hcard
    let parity : Gen I.d I.k → (Fin I.d → Bool) := fun g i => decide (aVec r g.1 i % 2 = 0)
    have hmaps : Set.MapsTo parity (θ.support : Set (Gen I.d I.k))
        ((Finset.univ : Finset (Fin I.d → Bool)) : Set (Fin I.d → Bool)) :=
      fun _ _ => Finset.mem_univ _
    obtain ⟨ga, hga, gb, hgb, hne, hpar⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
    have hxne : ga.1 ≠ gb.1 := hθ_inj ga hga gb hgb hne
    have haVec_ne : aVec r ga.1 ≠ aVec r gb.1 := by
      intro heq
      apply hxne
      ext i
      rw [eq_r_add_two_pow_mul_aVec (hθ_rep.1 hga).2 i,
        eq_r_add_two_pow_mul_aVec (hθ_rep.1 hgb).2 i]
      rw [congrFun heq i]
    have hmod : ∀ i : Fin I.d, aVec r ga.1 i % 2 = 0 ↔ aVec r gb.1 i % 2 = 0 := fun i =>
      decide_eq_decide.mp (congrFun hpar i)
    have hdiv : ∀ i : Fin I.d, 2 ∣ aVec r ga.1 i + aVec r gb.1 i := fun i => by
      have := hmod i
      omega
    let x₀ : Fin I.d → ℤ := fun i =>
      ((r i : ℕ) : ℤ) + (2 ^ I.d : ℤ) * ((aVec r ga.1 i + aVec r gb.1 i) / 2)
    let u₀ : Fin I.k → ℝ := (1 / 2 : ℝ) • ga.2 + (1 / 2 : ℝ) • gb.2
    let g₀ : Gen I.d I.k := (x₀, u₀)
    have hx₀_mod : ∀ i, x₀ i ≡ ((r i : ℕ) : ℤ) [ZMOD 2 ^ I.d] := fun i => by
      rw [Int.modEq_iff_dvd]
      refine ⟨-((aVec r ga.1 i + aVec r gb.1 i) / 2), ?_⟩
      dsimp only [x₀]
      ring
    have hx₀_real : (fun i => (x₀ i : ℝ)) =
        (1 / 2 : ℝ) • (fun i => (ga.1 i : ℝ)) + (1 / 2 : ℝ) • (fun i => (gb.1 i : ℝ)) := by
      ext i
      have h2x : 2 * x₀ i = ga.1 i + gb.1 i := by
        have ha := eq_r_add_two_pow_mul_aVec (hθ_rep.1 hga).2 i
        have hb := eq_r_add_two_pow_mul_aVec (hθ_rep.1 hgb).2 i
        have hc : 2 * ((aVec r ga.1 i + aVec r gb.1 i) / 2) = aVec r ga.1 i + aVec r gb.1 i :=
          Int.mul_ediv_cancel' (hdiv i)
        dsimp only [x₀]
        calc 2 * (((r i : ℕ) : ℤ) + (2 ^ I.d : ℤ) * ((aVec r ga.1 i + aVec r gb.1 i) / 2))
          _ = 2 * ((r i : ℕ) : ℤ) + (2 ^ I.d : ℤ) * (2 * ((aVec r ga.1 i + aVec r gb.1 i) / 2)) := by
              ring
          _ = 2 * ((r i : ℕ) : ℤ) + (2 ^ I.d : ℤ) * (aVec r ga.1 i + aVec r gb.1 i) := by rw [hc]
          _ = (((r i : ℕ) : ℤ) + (2 ^ I.d : ℤ) * aVec r ga.1 i) +
              (((r i : ℕ) : ℤ) + (2 ^ I.d : ℤ) * aVec r gb.1 i) := by ring
          _ = ga.1 i + gb.1 i := by rw [← ha, ← hb]
      have h2xR : (2 : ℝ) * (x₀ i : ℝ) = (ga.1 i : ℝ) + (gb.1 i : ℝ) := by exact_mod_cast h2x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linarith
    have hg₀_Sr : g₀ ∈ I.Sr t r := by
      refine ⟨?_, hx₀_mod⟩
      have hmem := convex_P I t (hθ_rep.1 hga).1 (hθ_rep.1 hgb).1
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      have heq : (1 / 2 : ℝ) • ga.toReal + (1 / 2 : ℝ) • gb.toReal = g₀.toReal := by
        ext i
        · exact (congrFun hx₀_real i).symm
        · rfl
      change g₀.toReal ∈ I.P t
      rwa [← heq]
    let α : ℝ := min (θ ga) (θ gb)
    have hα_pos : 0 < α := lt_min
      (lt_of_le_of_ne (hθ_rep.2.1 ga) (Ne.symm (Finsupp.mem_support_iff.mp hga)))
      (lt_of_le_of_ne (hθ_rep.2.1 gb) (Ne.symm (Finsupp.mem_support_iff.mp hgb)))
    let θ' : Gen I.d I.k →₀ ℝ :=
      θ - Finsupp.single ga α - Finsupp.single gb α + Finsupp.single g₀ (2 * α)
    have hθ'_nonneg : ∀ g, 0 ≤ θ' g := fun g => by
      dsimp only [θ']
      simp only [Finsupp.coe_add, Finsupp.coe_sub, Pi.add_apply, Pi.sub_apply,
        Finsupp.single_apply]
      by_cases h1 : ga = g <;> by_cases h2 : gb = g <;> by_cases h3 : g₀ = g
      · exact absurd (h1.trans h2.symm) hne
      · exact absurd (h1.trans h2.symm) hne
      · subst h1; simp only [↓reduceIte, h2, h3]; linarith [min_le_left (θ ga) (θ gb)]
      · subst h1; simp only [↓reduceIte, h2, h3]; linarith [min_le_left (θ ga) (θ gb)]
      · subst h2; simp only [↓reduceIte, h1, h3]; linarith [min_le_right (θ ga) (θ gb)]
      · subst h2; simp only [↓reduceIte, h1, h3]; linarith [min_le_right (θ ga) (θ gb)]
      · subst h3; simp only [↓reduceIte, h1, h2]; linarith [hθ_rep.2.1 g₀]
      · simp only [h1, h2, h3, ↓reduceIte]; linarith [hθ_rep.2.1 g]
    have hθ'_supp : (↑θ'.support : Set (Gen I.d I.k)) ⊆ I.Sr t r := fun g hg => by
      by_cases hg₀ : g = g₀
      · rwa [hg₀]
      · have hne0 : θ' g ≠ 0 := Finsupp.mem_support_iff.mp hg
        have hθg_ne0 : θ g ≠ 0 := by
          intro h0
          dsimp only [θ'] at hne0
          simp only [Finsupp.coe_add, Finsupp.coe_sub, Pi.add_apply, Pi.sub_apply,
            Finsupp.single_apply, h0, if_neg (Ne.symm hg₀)] at hne0
          by_cases h1 : ga = g <;> by_cases h2 : gb = g
          · exact hne (h1.trans h2.symm)
          · subst h1; linarith [min_le_left (θ ga) (θ gb), hθ_rep.2.1 ga]
          · subst h2; linarith [min_le_right (θ ga) (θ gb), hθ_rep.2.1 gb]
          · simp [h1, h2] at hne0
        exact hθ_rep.1 (Finsupp.mem_support_iff.mpr hθg_ne0)
    have hθ'_sum_gen : ∀ {M : Type} [AddCommGroup M] (F : Gen I.d I.k → ℝ → M)
        (_ : ∀ g, F g 0 = 0) (_ : ∀ g a b, F g (a + b) = F g a + F g b),
        θ'.sum F = θ.sum F - F ga α - F gb α + F g₀ (2 * α) := by
      intro M _ F hF0 hFadd
      have hsub : ∀ ν₁ ν₂ : Gen I.d I.k →₀ ℝ, (ν₁ - ν₂).sum F = ν₁.sum F - ν₂.sum F := by
        intro ν₁ ν₂
        have h := congr_arg (fun ν : Gen I.d I.k →₀ ℝ => ν.sum F) (sub_add_cancel ν₁ ν₂)
        rw [Finsupp.sum_add_index' hF0 hFadd] at h
        exact eq_sub_of_add_eq h
      dsimp only [θ']
      rw [Finsupp.sum_add_index' hF0 hFadd, hsub, hsub,
        Finsupp.sum_single_index (hF0 ga), Finsupp.sum_single_index (hF0 gb),
        Finsupp.sum_single_index (hF0 g₀)]
    have hθ'_rep : IsFracRep (I.Sr t r) θ' ξ := by
      refine ⟨hθ'_supp, hθ'_nonneg, ?_, ?_⟩
      · have heq := hθ'_sum_gen (fun g c => c • g.toReal) (fun _ => by simp)
          (fun _ _ _ => by simp [add_smul])
        rw [heq, hθ_rep.2.2.1]
        have h2g₀ : (2 * α) • g₀.toReal = α • ga.toReal + α • gb.toReal := by
          ext i
          · have hxi := congrFun hx₀_real i
            simp only [Prod.smul_fst, Prod.fst_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
              Gen.toReal, g₀] at hxi ⊢
            rw [hxi]
            ring
          · simp only [Prod.smul_snd, Prod.snd_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
              Gen.toReal, g₀, u₀]
            ring
        rw [h2g₀]
        abel
      · have heq := hθ'_sum_gen (fun _ c => c) (fun _ => rfl) (fun _ _ _ => rfl)
        rw [heq, hθ_rep.2.2.2]
        ring
    have hf_mid : I.f t (fun i => (x₀ i : ℝ)) ≤
        (1 / 2 : ℝ) * I.f t (fun i => (ga.1 i : ℝ)) +
          (1 / 2 : ℝ) * I.f t (fun i => (gb.1 i : ℝ)) := by
      have hdJ := discreteJensen_of_valid I hI t
      have hx₀X : x₀ ∈ {x : Fin I.d → ℤ | (fun i => (x i : ℝ)) ∈ Prod.fst '' I.P t} :=
        ⟨g₀.toReal, hg₀_Sr.1, rfl⟩
      have hxsX : ∀ i : Fin 2, ![ga.1, gb.1] i ∈
          {x : Fin I.d → ℤ | (fun i => (x i : ℝ)) ∈ Prod.fst '' I.P t} := by
        intro i; fin_cases i
        · exact ⟨ga.toReal, (hθ_rep.1 hga).1, rfl⟩
        · exact ⟨gb.toReal, (hθ_rep.1 hgb).1, rfl⟩
      have h := hdJ x₀ hx₀X 2 (fun _ => (1 / 2 : ℝ)) ![ga.1, gb.1] hxsX
        (fun _ => by norm_num) (by norm_num) (by
          ext i
          have hxi := congrFun hx₀_real i
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_two,
            Matrix.cons_val_zero, Matrix.cons_val_one] at hxi ⊢
          exact hxi)
      simpa [Fin.sum_univ_two] using h
    have hθ'_cost : fracCost (I.f t) θ' ≤ Φstar := by
      have heq := hθ'_sum_gen (fun g c => c * I.f t (fun i => (g.1 i : ℝ)))
        (fun _ => by simp) (fun _ _ _ => by ring)
      change θ'.sum (fun g c => c * I.f t (fun i => (g.1 i : ℝ))) ≤ Φstar
      rw [heq, show θ.sum (fun g c => c * I.f t (fun i => (g.1 i : ℝ))) = fracCost (I.f t) θ
        from rfl, hθ_cost]
      nlinarith
    have hθ'_cost_eq : fracCost (I.f t) θ' = Φstar :=
      le_antisymm hθ'_cost (hglobal_opt θ' hθ'_rep).1
    have hpot_lt : θ'.sum (fun g c => c * potGen g.1) < θ.sum (fun g c => c * potGen g.1) := by
      have heq := hθ'_sum_gen (fun g c => c * potGen g.1)
        (fun _ => by simp) (fun _ _ _ => by ring)
      rw [heq]
      have haVec_x₀ : ∀ i, aVec r x₀ i = (aVec r ga.1 i + aVec r gb.1 i) / 2 := fun i => by
        dsimp only [aVec, x₀]
        have hpos : (2 ^ I.d : ℤ) ≠ 0 := by positivity
        calc (((r i : ℕ) : ℤ) + (2 ^ I.d : ℤ) * ((aVec r ga.1 i + aVec r gb.1 i) / 2) -
                ((r i : ℕ) : ℤ)) / (2 ^ I.d : ℤ)
          _ = ((aVec r ga.1 i + aVec r gb.1 i) / 2 * (2 ^ I.d : ℤ)) / (2 ^ I.d : ℤ) := by
              congr 1; ring
          _ = (aVec r ga.1 i + aVec r gb.1 i) / 2 := Int.mul_ediv_cancel _ hpos
      have hpar_le : ∀ i : Fin I.d,
          (2 : ℝ) * (aVec r x₀ i : ℝ) ^ 2 ≤
            (aVec r ga.1 i : ℝ) ^ 2 + (aVec r gb.1 i : ℝ) ^ 2 := fun i => by
        have hc : 2 * ((aVec r ga.1 i + aVec r gb.1 i) / 2) = aVec r ga.1 i + aVec r gb.1 i :=
          Int.mul_ediv_cancel' (hdiv i)
        have hcR : (2 : ℝ) * (aVec r x₀ i : ℝ) = (aVec r ga.1 i : ℝ) + (aVec r gb.1 i : ℝ) := by
          rw [haVec_x₀ i]
          exact_mod_cast hc
        have hid : (4 : ℝ) * (aVec r x₀ i : ℝ) ^ 2 +
              ((aVec r ga.1 i : ℝ) - (aVec r gb.1 i : ℝ)) ^ 2 =
            2 * ((aVec r ga.1 i : ℝ) ^ 2 + (aVec r gb.1 i : ℝ) ^ 2) := by
          linear_combination (2 * (aVec r x₀ i : ℝ) + (aVec r ga.1 i : ℝ) + (aVec r gb.1 i : ℝ)) * hcR
        linarith [sq_nonneg ((aVec r ga.1 i : ℝ) - (aVec r gb.1 i : ℝ))]
      obtain ⟨i₀, hi₀⟩ : ∃ i : Fin I.d, aVec r ga.1 i ≠ aVec r gb.1 i := by
        by_contra h
        push Not at h
        exact haVec_ne (funext h)
      have hpar_lt : (2 : ℝ) * (aVec r x₀ i₀ : ℝ) ^ 2 <
          (aVec r ga.1 i₀ : ℝ) ^ 2 + (aVec r gb.1 i₀ : ℝ) ^ 2 := by
        have hc : 2 * ((aVec r ga.1 i₀ + aVec r gb.1 i₀) / 2) = aVec r ga.1 i₀ + aVec r gb.1 i₀ :=
          Int.mul_ediv_cancel' (hdiv i₀)
        have hcR : (2 : ℝ) * (aVec r x₀ i₀ : ℝ) =
            (aVec r ga.1 i₀ : ℝ) + (aVec r gb.1 i₀ : ℝ) := by
          rw [haVec_x₀ i₀]
          exact_mod_cast hc
        have hneR : (aVec r ga.1 i₀ : ℝ) ≠ (aVec r gb.1 i₀ : ℝ) := by exact_mod_cast hi₀
        have hsq : 0 < ((aVec r ga.1 i₀ : ℝ) - (aVec r gb.1 i₀ : ℝ)) ^ 2 :=
          sq_pos_of_ne_zero (sub_ne_zero.mpr hneR)
        have hid : (4 : ℝ) * (aVec r x₀ i₀ : ℝ) ^ 2 +
              ((aVec r ga.1 i₀ : ℝ) - (aVec r gb.1 i₀ : ℝ)) ^ 2 =
            2 * ((aVec r ga.1 i₀ : ℝ) ^ 2 + (aVec r gb.1 i₀ : ℝ) ^ 2) := by
          linear_combination (2 * (aVec r x₀ i₀ : ℝ) + (aVec r ga.1 i₀ : ℝ) + (aVec r gb.1 i₀ : ℝ)) * hcR
        linarith
      have hpot_diff : 2 * potGen x₀ < potGen ga.1 + potGen gb.1 := by
        dsimp only [potGen, g₀]
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_lt_sum (fun i _ => hpar_le i) ⟨i₀, Finset.mem_univ _, hpar_lt⟩
      change θ.sum (fun g c => c * potGen g.1) - α * potGen ga.1 - α * potGen gb.1 +
          2 * α * potGen g₀.1 < θ.sum (fun g c => c * potGen g.1)
      nlinarith
    have hopt_le := (hglobal_opt θ' hθ'_rep).2 hθ'_cost_eq
    linarith [hθ_pot, hopt_le, hpot_lt]
  -- Step 3c: Lemma 6 rounding & pool averaging
  let S_supp := θ.support
  let q : Gen I.d I.k → ℕ := fun g => Nat.floor (θ g)
  let δ : Gen I.d I.k → ℝ := fun g => θ g - (q g : ℝ)
  have hδ_nonneg : ∀ g, 0 ≤ δ g := fun g => sub_nonneg.mpr (Nat.floor_le (hθ_rep.2.1 g))
  have hδ_lt_one : ∀ g, δ g < 1 := fun g => by
    dsimp only [δ, q]
    linarith [Nat.lt_floor_add_one (θ g)]
  have hq_sum_le : ∑ g ∈ S_supp, q g ≤ n := by
    rw [← Nat.cast_le (α := ℝ), Nat.cast_sum]
    calc ∑ g ∈ S_supp, (q g : ℝ)
      _ ≤ ∑ g ∈ S_supp, θ g := Finset.sum_le_sum fun g _ => Nat.floor_le (hθ_rep.2.1 g)
      _ = (n : ℝ) := hθ_rep.2.2.2
  let ℓ : ℕ := n - ∑ g ∈ S_supp, q g
  have hℓ_eq : (ℓ : ℝ) = ∑ g ∈ S_supp, δ g := by
    have hq_cast : (ℓ : ℝ) = (n : ℝ) - ∑ g ∈ S_supp, (q g : ℝ) := by
      dsimp only [ℓ]
      rw [Nat.cast_sub hq_sum_le, Nat.cast_sum]
    have hsum_θ : ∑ g ∈ S_supp, θ g = (n : ℝ) := hθ_rep.2.2.2
    rw [hq_cast, ← hsum_θ]
    dsimp only [δ]
    rw [Finset.sum_sub_distrib]
  by_cases hℓ0 : ℓ = 0
  · have hδ0 : ∀ g ∈ S_supp, δ g = 0 := by
      have hsum0 : ∑ g ∈ S_supp, δ g = 0 := by rw [← hℓ_eq, hℓ0]; simp
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun g _ => hδ_nonneg g)).mp hsum0
    have hθ_eq_q : ∀ g ∈ S_supp, θ g = (q g : ℝ) := fun g hg => by
      have h := hδ0 g hg
      dsimp only [δ] at h
      linarith
    let μ_blk : Gen I.d I.k →₀ ℕ := ∑ g ∈ S_supp, Finsupp.single g (q g)
    refine ⟨μ_blk, ?_, ?_, ?_, ?_⟩
    · intro g hg
      have hg' := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hg)
      obtain ⟨g', hg'S, hgg'⟩ := hg'
      rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hgg')]
      exact (hθ_rep.1 hg'S).1
    · rw [aggr_sum]
      simp_rw [aggr_single]
      rw [← hθ_rep.2.2.1]
      refine Finset.sum_congr rfl fun g hg => ?_
      rw [hθ_eq_q g hg]
    · rw [count_sum]
      simp_rw [count_single]
      omega
    · rw [hΦ_eq, EReal.coe_le_coe_iff, ← hθ_cost, costOf_sum]
      simp_rw [costOf_single]
      refine le_of_eq ?_
      change ∑ g ∈ S_supp, (q g : ℝ) * I.f t (fun i => (g.1 i : ℝ)) =
        ∑ g ∈ S_supp, θ g * I.f t (fun i => (g.1 i : ℝ))
      refine Finset.sum_congr rfl fun g hg => by rw [hθ_eq_q g hg]
  have hℓ_pos : 0 < ℓ := Nat.pos_of_ne_zero hℓ0
  have hS_ne : S_supp.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.sum_empty] at hℓ_eq
    have : (0 : ℝ) < (ℓ : ℝ) := Nat.cast_pos.mpr hℓ_pos
    linarith
  let ρ : Gen I.d I.k → ℕ := fun g => Nat.floor ((2 ^ I.d : ℝ) * δ g)
  have hρ_sum_ge : 2 ^ I.d * (ℓ - 1) ≤ ∑ g ∈ S_supp, ρ g := by
    have hlt_R : (2 ^ I.d : ℝ) * (ℓ : ℝ) - (∑ g ∈ S_supp, (ρ g : ℝ)) < (2 ^ I.d : ℝ) := by
      have h1 : (2 ^ I.d : ℝ) * (ℓ : ℝ) - ∑ g ∈ S_supp, (ρ g : ℝ) =
          ∑ g ∈ S_supp, ((2 ^ I.d : ℝ) * δ g - (ρ g : ℝ)) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← hℓ_eq]
      have h2 : ∑ g ∈ S_supp, ((2 ^ I.d : ℝ) * δ g - (ρ g : ℝ)) < ∑ _g ∈ S_supp, (1 : ℝ) := by
        refine Finset.sum_lt_sum (fun g _ => ?_) ⟨hS_ne.choose, hS_ne.choose_spec, ?_⟩
        · linarith [Nat.lt_floor_add_one ((2 ^ I.d : ℝ) * δ g)]
        · linarith [Nat.lt_floor_add_one ((2 ^ I.d : ℝ) * δ hS_ne.choose)]
      have hcardR : (S_supp.card : ℝ) ≤ (2 ^ I.d : ℝ) := by exact_mod_cast hθ_card
      calc (2 ^ I.d : ℝ) * (ℓ : ℝ) - ∑ g ∈ S_supp, (ρ g : ℝ)
        _ = ∑ g ∈ S_supp, ((2 ^ I.d : ℝ) * δ g - (ρ g : ℝ)) := h1
        _ < ∑ _g ∈ S_supp, (1 : ℝ) := h2
        _ = (S_supp.card : ℝ) := by simp
        _ ≤ (2 ^ I.d : ℝ) := hcardR
    have hlt_sub : ((2 ^ I.d * (ℓ - 1) : ℕ) : ℝ) < ((∑ g ∈ S_supp, ρ g : ℕ) : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_sub hℓ_pos, Nat.cast_one,
        Nat.cast_sum]
      linarith
    exact le_of_lt (Nat.cast_lt.mp hlt_sub)
  let pool : List (Gen I.d I.k) := S_supp.toList.flatMap fun g => List.replicate (ρ g) g
  let used : List (Gen I.d I.k) := pool.take (2 ^ I.d * (ℓ - 1))
  have hpool_len : pool.length = ∑ g ∈ S_supp, ρ g := by
    simp only [pool, List.length_flatMap, List.length_replicate]
    exact list_map_sum_toList S_supp ρ
  have hused_len : used.length = 2 ^ I.d * (ℓ - 1) := by
    simp only [used, List.length_take, hpool_len]
    exact min_eq_left hρ_sum_ge
  have hused_mem : ∀ g ∈ used, g ∈ S_supp := fun g hg => by
    have h1 := List.mem_of_mem_take hg
    rw [List.mem_flatMap] at h1
    rcases h1 with ⟨g', hg', hrep⟩
    rw [List.eq_of_mem_replicate hrep]
    exact Finset.mem_toList.mp hg'
  have hpool_count : ∀ g ∈ S_supp, pool.count g = ρ g := fun g hg => by
    dsimp only [pool]
    rw [List.count_flatMap]
    have hmap : S_supp.toList.map (List.count g ∘ fun x => List.replicate (ρ x) x) =
        S_supp.toList.map (fun x => if x = g then ρ x else 0) := by
      refine List.map_congr_left fun a _ => ?_
      simp only [Function.comp_def, List.count_replicate]
      by_cases hag : a = g
      · subst hag; simp
      · simp [hag]
    rw [hmap, list_map_sum_toList S_supp (fun x => if x = g then ρ x else 0)]
    simp [Finset.sum_ite_eq', hg]
  have hused_count : ∀ g ∈ S_supp, used.count g ≤ ρ g := fun g hg =>
    (List.take_sublist _ _).count_le g |>.trans (hpool_count g hg).le
  have hused_count_sum : ∑ g ∈ S_supp, used.count g = 2 ^ I.d * (ℓ - 1) := by
    have h1 := list_count_sum used S_supp hused_mem (fun _ => (1 : ℕ))
    simp only [List.map_const', List.sum_replicate, smul_eq_mul, mul_one, hused_len] at h1
    exact h1.symm
  have hlen_eq : (ℓ - 1) * 2 ^ I.d = used.length := by rw [hused_len, mul_comm]
  let chunk : Fin (ℓ - 1) → Fin (2 ^ I.d) → Gen I.d I.k := fun j m =>
    used.get ((finProdFinEquiv (j, m)).cast hlen_eq)
  have hchunk_mem : ∀ j m, chunk j m ∈ S_supp := fun j m =>
    hused_mem _ (List.get_mem _ _)
  have hchunk_sum : ∀ {M : Type} [AddCommMonoid M] (F : Gen I.d I.k → M),
      ∑ j : Fin (ℓ - 1), ∑ m : Fin (2 ^ I.d), F (chunk j m) =
        ∑ g ∈ S_supp, (used.count g) • F g := fun F =>
    list_chunk_sum used S_supp hused_mem hlen_eq F
  have h2d_pos : (0 : ℝ) < (2 ^ I.d : ℝ) := by positivity
  let x_avg : Fin (ℓ - 1) → Fin I.d → ℤ := fun j i =>
    ((r i : ℕ) : ℤ) + ∑ m : Fin (2 ^ I.d), aVec r (chunk j m).1 i
  let u_avg : Fin (ℓ - 1) → Fin I.k → ℝ := fun j =>
    ((2 ^ I.d : ℝ)⁻¹) • ∑ m : Fin (2 ^ I.d), (chunk j m).2
  let g_avg : Fin (ℓ - 1) → Gen I.d I.k := fun j => (x_avg j, u_avg j)
  have hx_avg_real : ∀ j i, (x_avg j i : ℝ) =
      ((2 ^ I.d : ℝ)⁻¹) * ∑ m : Fin (2 ^ I.d), ((chunk j m).1 i : ℝ) := fun j i => by
    have hmul : (2 ^ I.d : ℤ) * x_avg j i = ∑ m : Fin (2 ^ I.d), (chunk j m).1 i := by
      dsimp only [x_avg]
      rw [mul_add, Finset.mul_sum]
      calc (2 ^ I.d : ℤ) * ((r i : ℕ) : ℤ) +
            ∑ m : Fin (2 ^ I.d), (2 ^ I.d : ℤ) * aVec r (chunk j m).1 i
        _ = (∑ _m : Fin (2 ^ I.d), ((r i : ℕ) : ℤ)) +
              ∑ m : Fin (2 ^ I.d), (2 ^ I.d : ℤ) * aVec r (chunk j m).1 i := by
            simp [mul_comm]
        _ = ∑ m : Fin (2 ^ I.d), (((r i : ℕ) : ℤ) + (2 ^ I.d : ℤ) * aVec r (chunk j m).1 i) :=
            (Finset.sum_add_distrib).symm
        _ = ∑ m : Fin (2 ^ I.d), (chunk j m).1 i := by
            refine Finset.sum_congr rfl fun m _ => ?_
            exact (eq_r_add_two_pow_mul_aVec (hθ_rep.1 (hchunk_mem j m)).2 i).symm
    have hmulR : (2 ^ I.d : ℝ) * (x_avg j i : ℝ) = ∑ m : Fin (2 ^ I.d), ((chunk j m).1 i : ℝ) := by
      exact_mod_cast hmul
    exact eq_inv_mul_iff_mul_eq₀ h2d_pos.ne' |>.mpr hmulR
  have hg_avg_S : ∀ j, g_avg j ∈ I.S t := fun j => by
    have hmemP : ∀ m ∈ (Finset.univ : Finset (Fin (2 ^ I.d))),
        (chunk j m).toReal ∈ I.P t := fun m _ => (hθ_rep.1 (hchunk_mem j m)).1
    have hcm := (convex_P I t).centerMass_mem (fun _ _ => by positivity)
      (by simp : (0 : ℝ) < ∑ _m : Fin (2 ^ I.d), (1 : ℝ)) hmemP
    have hcm_eq : (Finset.univ : Finset (Fin (2 ^ I.d))).centerMass (fun _ => (1 : ℝ))
        (fun m => (chunk j m).toReal) = (g_avg j).toReal := by
      simp only [Finset.centerMass, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat]
      ext i
      · simp only [Prod.smul_fst, Prod.fst_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
          one_smul, Gen.toReal, g_avg]
        exact (hx_avg_real j i).symm
      · simp only [Prod.smul_snd, Prod.snd_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
          one_smul, Gen.toReal, g_avg, u_avg]
    change (g_avg j).toReal ∈ I.P t
    rw [← hcm_eq]
    exact hcm
  have hf_avg : ∀ j, I.f t (fun i => (x_avg j i : ℝ)) ≤
      ((2 ^ I.d : ℝ)⁻¹) * ∑ m : Fin (2 ^ I.d), I.f t (fun i => ((chunk j m).1 i : ℝ)) := fun j => by
    have hdJ := discreteJensen_of_valid I hI t
    have hxX : x_avg j ∈ {x : Fin I.d → ℤ | (fun i => (x i : ℝ)) ∈ Prod.fst '' I.P t} :=
      ⟨(g_avg j).toReal, hg_avg_S j, rfl⟩
    have hxsX : ∀ m : Fin (2 ^ I.d), (chunk j m).1 ∈
        {x : Fin I.d → ℤ | (fun i => (x i : ℝ)) ∈ Prod.fst '' I.P t} := fun m =>
      ⟨(chunk j m).toReal, (hθ_rep.1 (hchunk_mem j m)).1, rfl⟩
    have h := hdJ (x_avg j) hxX (2 ^ I.d) (fun _ => (2 ^ I.d : ℝ)⁻¹) (fun m => (chunk j m).1)
      hxsX (fun _ => by positivity) (by simp [h2d_pos.ne']) (by
        ext i
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
        exact hx_avg_real j i)
    simpa [Finset.mul_sum] using h
  let β : Gen I.d I.k → ℝ := fun g => δ g - (used.count g : ℝ) / (2 ^ I.d : ℝ)
  have hβ_nonneg : ∀ g ∈ S_supp, 0 ≤ β g := fun g hg => by
    have hc1 : (used.count g : ℝ) ≤ (ρ g : ℝ) := by exact_mod_cast hused_count g hg
    have hc2 : (ρ g : ℝ) ≤ (2 ^ I.d : ℝ) * δ g :=
      Nat.floor_le (mul_nonneg h2d_pos.le (hδ_nonneg g))
    have hle : (used.count g : ℝ) / (2 ^ I.d : ℝ) ≤ δ g :=
      (div_le_iff₀ h2d_pos).mpr (by linarith)
    exact sub_nonneg.mpr hle
  have hβ_sum : ∑ g ∈ S_supp, β g = 1 := by
    dsimp only [β]
    rw [Finset.sum_sub_distrib, ← hℓ_eq, ← Finset.sum_div, ← Nat.cast_sum, hused_count_sum]
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_div_cancel_left₀ _ h2d_pos.ne']
    rw [Nat.cast_sub hℓ_pos, Nat.cast_one]
    ring
  let x_final : Fin I.d → ℤ := fun i =>
    z i - (∑ g ∈ S_supp, (q g : ℤ) * g.1 i) - (∑ j : Fin (ℓ - 1), x_avg j i)
  let u_final : Fin I.k → ℝ := ∑ g ∈ S_supp, β g • g.2
  let g_final : Gen I.d I.k := (x_final, u_final)
  have hx_final_real : ∀ i, (x_final i : ℝ) = ∑ g ∈ S_supp, β g * (g.1 i : ℝ) := fun i => by
    have hz_eq : (z i : ℝ) = ∑ g ∈ S_supp, θ g * (g.1 i : ℝ) := by
      have h := congr_arg (fun p : (Fin I.d → ℝ) × (Fin I.k → ℝ) => p.1 i) hθ_rep.2.2.1
      simpa [Finsupp.sum, Prod.fst_sum, Finset.sum_apply, Gen.toReal] using h.symm
    have havg_sum : (∑ j : Fin (ℓ - 1), (x_avg j i : ℝ)) =
        ∑ g ∈ S_supp, ((used.count g : ℝ) / (2 ^ I.d : ℝ)) * (g.1 i : ℝ) := by
      simp_rw [hx_avg_real]
      rw [← Finset.mul_sum]
      have hcs := hchunk_sum (fun g => (g.1 i : ℝ))
      simp only [nsmul_eq_mul] at hcs
      rw [hcs, Finset.mul_sum]
      refine Finset.sum_congr rfl fun g _ => by ring
    dsimp only [x_final, β]
    push_cast
    rw [hz_eq, havg_sum]
    calc (∑ g ∈ S_supp, θ g * (g.1 i : ℝ)) - (∑ g ∈ S_supp, (q g : ℝ) * (g.1 i : ℝ)) -
          (∑ g ∈ S_supp, ((used.count g : ℝ) / (2 ^ I.d : ℝ)) * (g.1 i : ℝ))
      _ = ∑ g ∈ S_supp, (θ g * (g.1 i : ℝ) - (q g : ℝ) * (g.1 i : ℝ) -
            ((used.count g : ℝ) / (2 ^ I.d : ℝ)) * (g.1 i : ℝ)) := by
          rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      _ = ∑ g ∈ S_supp, (δ g - (used.count g : ℝ) / (2 ^ I.d : ℝ)) * (g.1 i : ℝ) := by
          refine Finset.sum_congr rfl fun g _ => by dsimp only [δ]; ring
  have hg_final_S : g_final ∈ I.S t := by
    have hmemP : ∀ g ∈ S_supp, g.toReal ∈ I.P t := fun g hg => (hθ_rep.1 hg).1
    have hcm := (convex_P I t).centerMass_mem hβ_nonneg (by rw [hβ_sum]; exact zero_lt_one) hmemP
    have hcm_eq : S_supp.centerMass β Gen.toReal = g_final.toReal := by
      simp only [Finset.centerMass, hβ_sum, inv_one, one_smul]
      ext i
      · simp only [Prod.fst_sum, Prod.smul_fst, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
          Gen.toReal, g_final]
        exact (hx_final_real i).symm
      · simp only [Prod.snd_sum, Prod.smul_snd, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
          Gen.toReal, g_final, u_final]
    change g_final.toReal ∈ I.P t
    rw [← hcm_eq]
    exact hcm
  have hf_final : I.f t (fun i => (x_final i : ℝ)) ≤
      ∑ g ∈ S_supp, β g * I.f t (fun i => (g.1 i : ℝ)) := by
    have hxsX : ∀ g : Gen I.d I.k, g ∈ S_supp →
        (fun i => (g.1 i : ℝ)) ∈ I.Px t := fun g hg =>
      ⟨g.toReal, (hθ_rep.1 hg).1, rfl⟩
    have hmap := (hI.convex t).map_sum_le hβ_nonneg hβ_sum hxsX
    have hsum_fn : (fun i => (x_final i : ℝ)) =
        ∑ g ∈ S_supp, β g • (fun i => (g.1 i : ℝ)) := by
      ext i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact hx_final_real i
    rw [← hsum_fn] at hmap
    simpa [smul_eq_mul] using hmap
  let μ_blk : Gen I.d I.k →₀ ℕ :=
    (∑ g ∈ S_supp, Finsupp.single g (q g)) +
    (∑ j : Fin (ℓ - 1), Finsupp.single (g_avg j) 1) +
    Finsupp.single g_final 1
  refine ⟨μ_blk, ?_, ?_, ?_, ?_⟩
  · intro g hg
    dsimp only [μ_blk] at hg
    rcases Finset.mem_union.mp (Finsupp.support_add hg) with h12 | h3
    · rcases Finset.mem_union.mp (Finsupp.support_add h12) with h1 | h2
      · obtain ⟨g', hg'S, hgg'⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum h1)
        rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hgg')]
        exact (hθ_rep.1 hg'S).1
      · obtain ⟨j, _, hgj⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum h2)
        rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hgj)]
        exact hg_avg_S j
    · rw [Finset.mem_singleton.mp (Finsupp.support_single_subset h3)]
      exact hg_final_S
  · dsimp only [μ_blk]
    rw [aggr_add, aggr_add, aggr_sum, aggr_sum, aggr_single]
    simp_rw [aggr_single]
    have havg_snd : (∑ j : Fin (ℓ - 1), (1 : ℝ) • u_avg j) =
        ∑ g ∈ S_supp, ((used.count g : ℝ) / (2 ^ I.d : ℝ)) • g.2 := by
      simp_rw [one_smul]
      dsimp only [u_avg]
      rw [← Finset.smul_sum]
      have hcs := hchunk_sum (fun g => g.2)
      simp_rw [← Nat.cast_smul_eq_nsmul ℝ] at hcs
      rw [hcs, Finset.smul_sum]
      refine Finset.sum_congr rfl fun g _ => by
        rw [← mul_smul, div_eq_inv_mul]
    have hw_eq : w = ∑ g ∈ S_supp, θ g • g.2 := by
      have h := congr_arg Prod.snd hθ_rep.2.2.1
      simpa [Finsupp.sum, Prod.snd_sum, Gen.toReal] using h.symm
    ext i
    · simp only [Prod.fst_add, Prod.fst_sum, Prod.smul_fst, Finset.sum_apply,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_one, one_mul, Gen.toReal, g_avg,
        g_final, x_final]
      push_cast
      ring
    · simp only [Prod.snd_add, Prod.snd_sum, Prod.smul_snd, Finset.sum_apply,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_one, one_smul, Gen.toReal, g_avg,
        g_final]
      have hsub := congrFun havg_snd i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, one_smul] at hsub
      have hw_i := congrFun hw_eq i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hw_i
      rw [hsub]
      dsimp only [u_final]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, β]
      rw [hw_i]
      calc (∑ g ∈ S_supp, (q g : ℝ) * g.2 i) +
            (∑ g ∈ S_supp, ((used.count g : ℝ) / (2 ^ I.d : ℝ)) * g.2 i) +
            ∑ g ∈ S_supp, (δ g - (used.count g : ℝ) / (2 ^ I.d : ℝ)) * g.2 i
        _ = ∑ g ∈ S_supp, ((q g : ℝ) * g.2 i +
              ((used.count g : ℝ) / (2 ^ I.d : ℝ)) * g.2 i +
              (δ g - (used.count g : ℝ) / (2 ^ I.d : ℝ)) * g.2 i) := by
            rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        _ = ∑ g ∈ S_supp, θ g * g.2 i := by
            refine Finset.sum_congr rfl fun g _ => by dsimp only [δ]; ring
  · dsimp only [μ_blk]
    rw [count_add, count_add, count_sum, count_sum, count_single]
    simp_rw [count_single]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    omega
  · rw [hΦ_eq, EReal.coe_le_coe_iff, ← hθ_cost]
    dsimp only [μ_blk]
    rw [costOf_add, costOf_add, costOf_sum, costOf_sum, costOf_single]
    simp_rw [costOf_single, Nat.cast_one, one_mul]
    have havg_f_sum : (∑ j : Fin (ℓ - 1), I.f t (fun i => (x_avg j i : ℝ))) ≤
        ∑ g ∈ S_supp, ((used.count g : ℝ) / (2 ^ I.d : ℝ)) * I.f t (fun i => (g.1 i : ℝ)) := by
      refine le_trans (Finset.sum_le_sum fun j _ => hf_avg j) ?_
      rw [← Finset.mul_sum]
      have hcs := hchunk_sum (fun g => I.f t (fun i => (g.1 i : ℝ)))
      simp only [nsmul_eq_mul] at hcs
      rw [hcs, Finset.mul_sum]
      exact le_of_eq (Finset.sum_congr rfl fun g _ => by ring)
    have hsum_cost : (∑ g ∈ S_supp, (q g : ℝ) * I.f t (fun i => (g.1 i : ℝ))) +
          (∑ g ∈ S_supp, ((used.count g : ℝ) / (2 ^ I.d : ℝ)) * I.f t (fun i => (g.1 i : ℝ))) +
          ∑ g ∈ S_supp, β g * I.f t (fun i => (g.1 i : ℝ)) =
        fracCost (I.f t) θ := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      change ∑ g ∈ S_supp, ((q g : ℝ) * I.f t (fun i => (g.1 i : ℝ)) +
          ((used.count g : ℝ) / (2 ^ I.d : ℝ)) * I.f t (fun i => (g.1 i : ℝ)) +
          (δ g - (used.count g : ℝ) / (2 ^ I.d : ℝ)) * I.f t (fun i => (g.1 i : ℝ))) =
        θ.sum (fun g c => c * I.f t (fun i => (g.1 i : ℝ)))
      refine Finset.sum_congr rfl fun g _ => by dsimp only [δ]; ring
    linarith [hf_final]

end IntConeFPT.Corollary10Proof

open IntConeFPT.Corollary10Proof

theorem solution (I : Instance) (hI : I.Valid) (Nmax : ℕ) (γ : ℚ) :
    (∃ μ, I.FeasibleN Nmax μ ∧ I.cost μ ≤ γ) ↔
      ∃ R : Cand I, IsCandidate I R ∧ ∃ zn ∈ Khat I R Nmax γ, IsIntegral zn := by
  classical
  constructor
  · rintro ⟨μ, ⟨⟨hSupp, hQ, hA⟩, hN⟩, hcost⟩
    obtain ⟨μ', hμ'Supp, hμ'agg, hμ'cost, hμ'card, _⟩ :=
      IntConeFPT.lemma_7 hI.one_le_d I.P (convex_P I) hI.bounded I.f
        (discreteJensen_of_valid I hI) μ hSupp
    let R : Cand I := fun t => ((μ' t).support.image (fun g => resOf g.1)).toList
    have hR : IsCandidate I R := fun t => by
      refine ⟨Finset.nodup_toList _, ?_⟩
      calc (R t).length = ((μ' t).support.image (fun g => resOf g.1)).card := Finset.length_toList _
        _ ≤ (μ' t).support.card := Finset.card_image_le
        _ ≤ 2 ^ I.d := hμ'card t
    let μ_blk : (t : Fin I.τ) → Fin (R t).length → (Gen I.d I.k →₀ ℕ) := fun t i =>
      ∑ g ∈ (μ' t).support.filter (fun g => resOf g.1 = (R t).get i), Finsupp.single g (μ' t g)
    let ξ : Blocks I R := fun t i =>
      ((aggr (μ_blk t i)).1, (aggr (μ_blk t i)).2, (count (μ_blk t i) : ℝ))
    let zn : (t : Fin I.τ) → Fin (R t).length → (Fin I.d → ℝ) × ℝ := fun t i =>
      ((ξ t i).1, (ξ t i).2.2)
    have hblk_part : ∀ t, ∑ i : Fin (R t).length, μ_blk t i = μ' t := fun t => by
      have hsub : ((μ' t).support.image (fun g => resOf g.1)).toList.Nodup := Finset.nodup_toList _
      have hsum_eq : ∑ i : Fin (R t).length, μ_blk t i =
          ∑ r ∈ (μ' t).support.image (fun g => resOf g.1),
            ∑ g ∈ (μ' t).support.filter (fun g => resOf g.1 = r), Finsupp.single g (μ' t g) := by
        let e : Fin (R t).length ≃ ((μ' t).support.image (fun g => resOf g.1)) :=
          { toFun := fun i => ⟨(R t).get i, Finset.mem_toList.mp (List.get_mem _ _)⟩
            invFun := fun r => ⟨(R t).idxOf r.1,
              List.idxOf_lt_length_of_mem (Finset.mem_toList.mpr r.2)⟩
            left_inv := fun i => Fin.ext (List.get_idxOf hsub i)
            right_inv := fun r => Subtype.ext
              (List.idxOf_get (List.idxOf_lt_length_of_mem (Finset.mem_toList.mpr r.2))) }
        exact Equiv.sum_comp e (fun r =>
          ∑ g ∈ (μ' t).support.filter (fun g => resOf g.1 = r.1), Finsupp.single g (μ' t g)) |>.trans
          (Finset.sum_coe_sort _ (fun r =>
            ∑ g ∈ (μ' t).support.filter (fun g => resOf g.1 = r), Finsupp.single g (μ' t g)))
      rw [hsum_eq, Finset.sum_fiberwise_of_maps_to (fun g hg => Finset.mem_image_of_mem _ hg)]
      exact Finsupp.sum_single (μ' t)
    have hblockAgg : ∀ t, blockAgg ξ t = aggr (μ t) := fun t => by
      rw [← (hμ'agg t).1, ← hblk_part t, aggr_sum]
      rfl
    have hblockCount : ∀ t, blockCount ξ t = (count (μ t) : ℝ) := fun t => by
      rw [← (hμ'agg t).2, ← hblk_part t, count_sum]
      simp [blockCount, ξ]
    have hblk_Sr : ∀ t i g, g ∈ (μ_blk t i).support → g ∈ I.Sr t ((R t).get i) := fun t i g hg => by
      have hg' := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hg)
      obtain ⟨g', hg'f, hgg'⟩ := hg'
      rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hgg')]
      have hg'm := Finset.mem_filter.mp hg'f
      refine ⟨hμ'Supp t hg'm.1, ?_⟩
      intro j
      rw [← hg'm.2]
      exact resOf_spec g'.1 j
    have hξ_Cr : ∀ t i, ξ t i ∈ I.Cr t ((R t).get i) := fun t i => by
      by_cases hc0 : count (μ_blk t i) = 0
      · left
        have hzero : μ_blk t i = 0 := by
          by_contra hne
          obtain ⟨g, hg⟩ := Finsupp.support_nonempty_iff.mpr hne
          have hpos : 0 < μ_blk t i g := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg)
          have hle : μ_blk t i g ≤ count (μ_blk t i) :=
            Finset.single_le_sum (fun _ _ => Nat.zero_le _) hg
          omega
        simp [ξ, hzero, aggr_zero, count_zero]
      · right
        have hc_pos : (0 : ℝ) < (count (μ_blk t i) : ℝ) :=
          Nat.cast_pos.mpr (Nat.pos_of_ne_zero hc0)
        refine ⟨hc_pos, ?_⟩
        let S_i := (μ_blk t i).support
        have hmemSr : ∀ g ∈ S_i, g.toReal ∈ Gen.toReal '' I.Sr t ((R t).get i) := fun g hg =>
          ⟨g, hblk_Sr t i g hg, rfl⟩
        have hcm := convex_convexHull ℝ (Gen.toReal '' I.Sr t ((R t).get i))
        have hwpos : 0 < ∑ g ∈ S_i, (μ_blk t i g : ℝ) := by
          simpa [S_i, count, Finsupp.sum] using hc_pos
        have hcm_mem := hcm.centerMass_mem (fun g _ => Nat.cast_nonneg (μ_blk t i g))
          hwpos (fun g hg => subset_convexHull ℝ _ (hmemSr g hg))
        have hcm_eq : S_i.centerMass (fun g => (μ_blk t i g : ℝ)) Gen.toReal =
            ((ξ t i).2.2⁻¹ • (ξ t i).1, (ξ t i).2.2⁻¹ • (ξ t i).2.1) := by
          have hsum_w : (∑ g ∈ S_i, (μ_blk t i g : ℝ)) = (ξ t i).2.2 := by
            simp [S_i, ξ, count, Finsupp.sum]
          have hag : (∑ g ∈ S_i, (μ_blk t i g : ℝ) • g.toReal) = aggr (μ_blk t i) := by
            simp [S_i, aggr, Finsupp.sum]
          rw [Finset.centerMass, hsum_w, hag]
          simp only [ξ]
          ext <;> rfl
        change ((ξ t i).2.2⁻¹ • (ξ t i).1, (ξ t i).2.2⁻¹ • (ξ t i).2.1) ∈ I.Pr t ((R t).get i)
        rw [← hcm_eq]
        exact hcm_mem
    have hPhi_le : ∀ t i, I.Phi t ((R t).get i) (ξ t i) ≤
        ((costOf (I.f t) (μ_blk t i) : ℝ) : EReal) := fun t i => by
      let θ_sr : Gen I.d I.k →₀ ℝ :=
        ∑ g ∈ (μ_blk t i).support, Finsupp.single g ((μ_blk t i g : ℝ))
      have hθ_sr : IsFracRep (I.Sr t ((R t).get i)) θ_sr (ξ t i) := by
        have hterm : ∀ g ∈ (μ_blk t i).support,
            IsFracRep (I.Sr t ((R t).get i)) (Finsupp.single g ((μ_blk t i g : ℝ)))
              ((((μ_blk t i g : ℝ)) • g.toReal).1, (((μ_blk t i g : ℝ)) • g.toReal).2,
                (μ_blk t i g : ℝ)) := fun g hg =>
          isFracRep_single (hblk_Sr t i g hg) (Nat.cast_nonneg _)
        have hsum := isFracRep_sum (μ_blk t i).support _ _ hterm
        refine ⟨hsum.1, hsum.2.1, ?_, ?_⟩
        · rw [hsum.2.2.1]
          ext j
          · simp [ξ, aggr, Finsupp.sum, Prod.fst_sum]
          · simp [ξ, aggr, Finsupp.sum, Prod.snd_sum, Prod.fst_sum]
        · rw [hsum.2.2.2]
          simp [ξ, count, Finsupp.sum, Prod.snd_sum]
      obtain ⟨θ', hθ'rep, hθ'cost, _⟩ :=
        expand_fracRep_Sr_to_Vr I hI t ((R t).get i) hθ_sr
      have hcost_eq : fracCost (I.f t) θ_sr = costOf (I.f t) (μ_blk t i) := by
        dsimp only [θ_sr]
        rw [fracCost_sum]
        simp_rw [fracCost_single]
        rfl
      rw [← hcost_eq, ← hθ'cost]
      exact iInf₂_le_of_le θ' hθ'rep le_rfl
    have hPhi_total : ∑ t, ∑ i, I.Phi t ((R t).get i) (ξ t i) ≤ ((γ : ℝ) : EReal) := by
      have h1 : ∑ t, ∑ i, I.Phi t ((R t).get i) (ξ t i) ≤
          ∑ t : Fin I.τ, ∑ i : Fin (R t).length, ((costOf (I.f t) (μ_blk t i) : ℝ) : EReal) :=
        finset_sum_le_sum_ereal Finset.univ _ _ fun t _ =>
          finset_sum_le_sum_ereal Finset.univ _ _ fun i _ => hPhi_le t i
      have h2 : (∑ t : Fin I.τ, ∑ i : Fin (R t).length, ((costOf (I.f t) (μ_blk t i) : ℝ) : EReal)) =
          ((I.cost μ' : ℝ) : EReal) := by
        simp_rw [← coe_finset_sum_ereal]
        congr 1
        unfold Instance.cost
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [← hblk_part t, costOf_sum]
      have h3 : I.cost μ' ≤ (γ : ℝ) := by
        have hc : I.cost μ' ≤ I.cost μ := Finset.sum_le_sum fun t _ => hμ'cost t
        exact hc.trans hcost
      exact h1.trans (h2 ▸ (EReal.coe_le_coe_iff.mpr h3))
    refine ⟨R, hR, zn, ⟨ξ, ⟨?_, hξ_Cr, ?_, ?_, hPhi_total⟩, fun t i => ⟨rfl, rfl⟩⟩, ?_⟩
    · have heq : (∑ t, blockAgg ξ t) = I.totalAgg μ := by
        unfold Instance.totalAgg
        exact Finset.sum_congr rfl fun t _ => hblockAgg t
      rwa [heq]
    · have heq : (fun t => ((blockAgg ξ t).1, (blockAgg ξ t).2, blockCount ξ t)) =
          (fun t => I.typeAgg μ t) := by
        ext t <;> simp [Instance.typeAgg, hblockAgg t, hblockCount t]
      rwa [heq]
    · have heq : (∑ t, blockCount ξ t) = (I.totalCount μ : ℝ) := by
        unfold Instance.totalCount
        push_cast
        exact Finset.sum_congr rfl fun t _ => hblockCount t
      rw [heq]
      exact Nat.cast_le.mpr hN
    · intro t i
      refine ⟨fun j => ?_, ?_⟩
      · refine ⟨∑ g ∈ (μ_blk t i).support, (μ_blk t i g : ℤ) * g.1 j, ?_⟩
        simp only [zn, ξ, aggr, Finsupp.sum, Prod.fst_sum, Prod.smul_fst, Finset.sum_apply,
          Pi.smul_apply, smul_eq_mul, Gen.toReal]
        push_cast
        rfl
      · exact ⟨(count (μ_blk t i) : ℤ), rfl⟩
  · rintro ⟨R, _, zn, ⟨ξ, ⟨hQ, hCr, hA, hN, hPhi⟩, hξzn⟩, hInt⟩
    have hblk : ∀ t (i : Fin (R t).length),
        ∃ μ_blk : Gen I.d I.k →₀ ℕ,
          (↑μ_blk.support : Set (Gen I.d I.k)) ⊆ I.S t ∧
          aggr μ_blk = ((ξ t i).1, (ξ t i).2.1) ∧
          (count μ_blk : ℝ) = (ξ t i).2.2 ∧
          ((costOf (I.f t) μ_blk : ℝ) : EReal) ≤ I.Phi t ((R t).get i) (ξ t i) := fun t i => by
      obtain ⟨z_int, hz_int⟩ : ∃ z : Fin I.d → ℤ, ∀ j, (ξ t i).1 j = (z j : ℝ) := by
        choose z hz using (hInt t i).1
        exact ⟨z, fun j => (congrFun (hξzn t i).1 j).trans (hz j)⟩
      obtain ⟨n_int, hn_int⟩ := (hInt t i).2
      have hn_nonneg : 0 ≤ (ξ t i).2.2 := by
        rcases hCr t i with h0 | hpos
        · rw [Set.mem_singleton_iff.mp h0]; simp
        · exact hpos.1.le
      have hnZ_nonneg : 0 ≤ n_int := by
        have h1 : (n_int : ℝ) = (ξ t i).2.2 := (hn_int.symm).trans (hξzn t i).2.symm
        exact_mod_cast (h1 ▸ hn_nonneg)
      let n_nat : ℕ := n_int.toNat
      have hn_nat : (n_nat : ℝ) = (ξ t i).2.2 := by
        have h1 : (n_nat : ℤ) = n_int := Int.toNat_of_nonneg hnZ_nonneg
        calc (n_nat : ℝ) = (n_int : ℝ) := by exact_mod_cast h1
          _ = (zn t i).2 := hn_int.symm
          _ = (ξ t i).2.2 := (hξzn t i).2.symm
      have hξ_eq : ξ t i = ((fun j => (z_int j : ℝ)), (ξ t i).2.1, (n_nat : ℝ)) := by
        ext j
        · exact hz_int j
        · rfl
        · exact hn_nat.symm
      have hCr' : ((fun j => (z_int j : ℝ)), (ξ t i).2.1, (n_nat : ℝ)) ∈ I.Cr t ((R t).get i) :=
        hξ_eq ▸ hCr t i
      obtain ⟨μ_blk, h1, h2, h3, h4⟩ :=
        block_reconstruct I hI t ((R t).get i) z_int (ξ t i).2.1 n_nat hCr'
      refine ⟨μ_blk, h1, ?_, ?_, ?_⟩
      · ext j
        · simpa [hz_int j] using congr_arg (fun p : (Fin I.d → ℝ) × (Fin I.k → ℝ) => p.1 j) h2
        · exact (congr_arg (fun p : (Fin I.d → ℝ) × (Fin I.k → ℝ) => p.2 j) h2 :)
      · rw [h3, hn_nat]
      · rwa [← hξ_eq] at h4
    choose μ_blk hblk_supp hblk_aggr hblk_count hblk_cost using fun t =>
      fun i : Fin (R t).length => hblk t i
    let μ : Mult I := fun t => ∑ i : Fin (R t).length, μ_blk t i
    have hSupp : I.Supported μ := fun t g hg => by
      obtain ⟨i, _, hgi⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hg)
      exact hblk_supp t i hgi
    have hAggr : ∀ t, aggr (μ t) = blockAgg ξ t := fun t => by
      dsimp only [μ, blockAgg]
      rw [aggr_sum]
      exact Finset.sum_congr rfl fun i _ => hblk_aggr t i
    have hCount : ∀ t, (count (μ t) : ℝ) = blockCount ξ t := fun t => by
      dsimp only [μ, blockCount]
      rw [count_sum]
      push_cast
      exact Finset.sum_congr rfl fun i _ => hblk_count t i
    refine ⟨μ, ⟨⟨hSupp, ?_, ?_⟩, ?_⟩, ?_⟩
    · have heq : I.totalAgg μ = ∑ t, blockAgg ξ t := by
        unfold Instance.totalAgg
        exact Finset.sum_congr rfl fun t _ => hAggr t
      rwa [heq]
    · have heq : (fun t => I.typeAgg μ t) =
          (fun t => ((blockAgg ξ t).1, (blockAgg ξ t).2, blockCount ξ t)) := by
        ext t <;> simp [Instance.typeAgg, hAggr t, hCount t]
      rwa [heq]
    · rw [← Nat.cast_le (α := ℝ)]
      have heq : (I.totalCount μ : ℝ) = ∑ t, blockCount ξ t := by
        unfold Instance.totalCount
        push_cast
        exact Finset.sum_congr rfl fun t _ => hCount t
      rwa [heq]
    · rw [← EReal.coe_le_coe_iff]
      have h1 : ((I.cost μ : ℝ) : EReal) =
          ∑ t : Fin I.τ, ∑ i : Fin (R t).length, ((costOf (I.f t) (μ_blk t i) : ℝ) : EReal) := by
        simp_rw [← coe_finset_sum_ereal]
        congr 1
        unfold Instance.cost
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [costOf_sum]
      have h2 : (∑ t : Fin I.τ, ∑ i : Fin (R t).length, ((costOf (I.f t) (μ_blk t i) : ℝ) : EReal)) ≤
          ∑ t : Fin I.τ, ∑ i : Fin (R t).length, I.Phi t ((R t).get i) (ξ t i) :=
        finset_sum_le_sum_ereal Finset.univ _ _ fun t _ =>
          finset_sum_le_sum_ereal Finset.univ _ _ fun i _ => hblk_cost t i
      exact h1.le.trans (h2.trans hPhi)

