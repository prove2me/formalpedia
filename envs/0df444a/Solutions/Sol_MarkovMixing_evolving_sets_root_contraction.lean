-- Prove2me | solution 1 for MarkovMixing.evolving_sets_root_contraction
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:56:28.955249+00:00
-- url     : https://prove2.me/submissions/e455d684-1e5e-49ee-b9d4-f73c34b6846a

import Mathlib
import Mathlib.Analysis.SpecialFunctions.Sqrt

import Definitions.Def_mm_martingale
import Definitions.Def_mm_lower
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Definitions.Def_mm_mixing
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

/-
Accepted proof by MKPynnic: theorem c4b511c4-603e-44bb-bb5a-645050436ea7, submission 26e7a008-e9dc-42cf-b380-cf03d2708615.
Original SHA-256: c5a2db1ac0dc5de1012a62517b1c0effb9fdaa9700906e0919e4889147a12e1d.

Accepted proof by allychan327: theorem bfad9713-bd4c-4c03-8aef-16ccacf2b6b7, submission 0ec31cb4-a807-45d9-81d5-5048e76b6067.
Original SHA-256: f141dcb4abf71601c49595e501fd85a935a617fd3eab6754d862b658135a9263.

Accepted proof by ann: theorem 6e6862c3-cf73-4aee-89dc-edab1af3f858, submission 97c937f0-69af-489e-9c61-8e34d8ba8085.
Original SHA-256: a06e907997f20f6a7a1cff5204302177f456aac82264f3d946b1fe393642bb20.

All reused proof bodies are included below. No platform theorem import is used.
The local assembly manifest records exact source selections and transformations.
-/

/-!
# Recovering `P^t` from the evolving-set process (LPW Lemma 17.12)

The identity `π(x) P^t(x,y) = π(y) P_{{x}}{y ∈ S_t}` is proved by induction on
`t`.  The inductive step needs exactly one fact about a single evolving-set
step, namely the *column identity*

`π(y) ∑_{T ∋ y} P_ES(S,T) = ∑_{z ∈ S} π(z) P(z,y)`,

i.e. the chance that `y` survives into the next set is `Q(S,y)/π(y)`.  That is
proved as in Lemma 17.13: the transition probability `P_ES(S,T)` is the length
of the interval of uniform thresholds whose superlevel set is `T`, those
intervals are pairwise disjoint, and the ones belonging to sets containing `y`
cover `(0, Q(S,y)/π(y)]`.
-/

namespace MarkovMixing

open scoped BigOperators

private noncomputable def lvlU {V : Type*} [Fintype V] [DecidableEq V]
    (f : V → ℝ) (T : Finset V) : ℝ :=
  if h : T.Nonempty then T.inf' h f else 1

/-- The lower endpoint of the `u`-interval producing the superlevel set `T`. -/
private noncomputable def lvlL {V : Type*} [Fintype V] [DecidableEq V]
    (f : V → ℝ) (T : Finset V) : ℝ :=
  if h : Tᶜ.Nonempty then Tᶜ.sup' h f else 0

private lemma lvlU_le {V : Type*} [Fintype V] [DecidableEq V] (f : V → ℝ)
    {T : Finset V} {y : V} (hy : y ∈ T) : lvlU f T ≤ f y := by
  rw [lvlU, dif_pos ⟨y, hy⟩]
  exact Finset.inf'_le f hy

private lemma le_lvlL {V : Type*} [Fintype V] [DecidableEq V] (f : V → ℝ)
    {T : Finset V} {y : V} (hy : y ∈ Tᶜ) : f y ≤ lvlL f T := by
  rw [lvlL, dif_pos ⟨y, hy⟩]
  exact Finset.le_sup' f hy

private lemma lvlL_nonneg {V : Type*} [Fintype V] [DecidableEq V] (f : V → ℝ)
    (hf0 : ∀ z : V, 0 ≤ f z) (T : Finset V) : 0 ≤ lvlL f T := by
  rw [lvlL]
  split
  · rename_i h
    obtain ⟨z, hz⟩ := h
    exact le_trans (hf0 z) (Finset.le_sup' f hz)
  · exact le_refl 0

private lemma lvl_union {V : Type*} [Fintype V] [DecidableEq V] (f : V → ℝ)
    (hf0 : ∀ z : V, 0 ≤ f z) (y : V) :
    (⋃ T ∈ Finset.univ.filter (fun T : Finset V => y ∈ T),
      Set.Ioc (lvlL f T) (lvlU f T)) = Set.Ioc 0 (f y) := by
  classical
  ext u
  simp only [Set.mem_iUnion, Set.mem_Ioc, Finset.mem_filter, Finset.mem_univ, true_and,
    exists_prop]
  constructor
  · rintro ⟨T, hyT, hlo, hhi⟩
    exact ⟨lt_of_le_of_lt (lvlL_nonneg f hf0 T) hlo, le_trans hhi (lvlU_le f hyT)⟩
  · rintro ⟨hu0, huy⟩
    refine ⟨Finset.univ.filter (fun z : V => u ≤ f z), ?_, ?_, ?_⟩
    · simp [huy]
    · rw [lvlL]
      split
      · rename_i h
        rw [Finset.sup'_lt_iff]
        intro z hz
        simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
          not_le] at hz
        exact hz
      · exact hu0
    · rw [lvlU, dif_pos ⟨y, by simp [huy]⟩]
      refine Finset.le_inf' _ _ ?_
      intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
      exact hz

private lemma lvl_disjoint {V : Type*} [Fintype V] [DecidableEq V] (f : V → ℝ) (y : V) :
    (↑(Finset.univ.filter (fun T : Finset V => y ∈ T)) : Set (Finset V)).PairwiseDisjoint
      (fun T => Set.Ioc (lvlL f T) (lvlU f T)) := by
  classical
  have key : ∀ (R : Finset V) (u : ℝ), u ∈ Set.Ioc (lvlL f R) (lvlU f R) →
      R = Finset.univ.filter (fun z : V => u ≤ f z) := by
    intro R u hu
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hz
      exact le_trans hu.2 (lvlU_le f hz)
    · intro hz
      by_contra hzR
      have hle : f z ≤ lvlL f R := le_lvlL f (Finset.mem_compl.mpr hzR)
      have := hu.1
      linarith
  intro T _ T' _ hne
  simp only [Function.onFun]
  rw [Set.disjoint_left]
  intro u huT huT'
  exact hne ((key T u huT).trans (key T' u huT').symm)

private lemma lvl_col_sum {V : Type*} [Fintype V] [DecidableEq V] (f : V → ℝ)
    (hf0 : ∀ z : V, 0 ≤ f z) (y : V) :
    ∑ T ∈ Finset.univ.filter (fun T : Finset V => y ∈ T),
      max 0 (lvlU f T - lvlL f T) = f y := by
  classical
  have hm := MeasureTheory.measure_biUnion_finset (μ := MeasureTheory.volume)
    (lvl_disjoint f y) (fun T _ => measurableSet_Ioc)
  rw [lvl_union f hf0 y] at hm
  simp only [Real.volume_Ioc] at hm
  have hto := congrArg ENNReal.toReal hm
  rw [ENNReal.toReal_sum (fun T _ => ENNReal.ofReal_ne_top)] at hto
  simp only [ENNReal.toReal_ofReal', sub_zero, max_eq_left (hf0 y)] at hto
  rw [hto]
  exact Finset.sum_congr rfl fun T _ => max_comm _ _

/-- The column identity for one evolving-set step. -/
private lemma es_col {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (π : V → ℝ)
    (hπ : IsStationary P π) (hpos : ∀ x : V, 0 < π x) (S : Finset V) (y : V) :
    π y * ∑ T ∈ Finset.univ.filter (fun T : Finset V => y ∈ T), evolvingSets P π S T
      = ∑ z ∈ S, π z * P z y := by
  classical
  have hf0 : ∀ z : V, 0 ≤ min 1 (max 0 (esThresh P π S z)) :=
    fun _ => le_min zero_le_one (le_max_left _ _)
  have hev : ∀ T : Finset V, evolvingSets P π S T
      = max 0 (lvlU (fun z : V => min 1 (max 0 (esThresh P π S z))) T
               - lvlL (fun z : V => min 1 (max 0 (esThresh P π S z))) T) := fun _ => rfl
  have hcol : ∑ T ∈ Finset.univ.filter (fun T : Finset V => y ∈ T), evolvingSets P π S T
      = min 1 (max 0 (esThresh P π S y)) := by
    rw [Finset.sum_congr rfl fun T _ => hev T]
    exact lvl_col_sum _ hf0 y
  have hQ0 : 0 ≤ ∑ z ∈ S, π z * P z y :=
    Finset.sum_nonneg fun z _ => mul_nonneg (le_of_lt (hpos z)) (hP.1 z y)
  have hQle : ∑ z ∈ S, π z * P z y ≤ π y := by
    have hsub : ∑ z ∈ S, π z * P z y ≤ ∑ z : V, π z * P z y :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        (fun z _ _ => mul_nonneg (le_of_lt (hpos z)) (hP.1 z y))
    have hstat : ∑ z : V, π z * P z y = π y := by
      have h := congrFun hπ.2 y
      simpa [Matrix.vecMul, dotProduct] using h
    linarith
  have hπy : (0 : ℝ) < π y := hpos y
  have hne : π y ≠ 0 := ne_of_gt hπy
  have h1 : max 0 (esThresh P π S y) = esThresh P π S y :=
    max_eq_right (div_nonneg hQ0 (le_of_lt hπy))
  have h2 : min 1 (esThresh P π S y) = esThresh P π S y := by
    refine min_eq_right ?_
    rw [esThresh, div_le_one hπy]
    exact hQle
  rw [hcol, h1, h2, esThresh]
  field_simp

/-- Swapping a sum over subsets against a sum over elements. -/
private lemma subset_sum_swap {V : Type*} [Fintype V] [DecidableEq V]
    (A : Finset V → ℝ) (c : V → ℝ) :
    ∑ S : Finset V, A S * (∑ z ∈ S, c z)
      = ∑ z : V, c z * ∑ S ∈ Finset.univ.filter (fun S : Finset V => z ∈ S), A S := by
  classical
  have step1 : ∀ S : Finset V, A S * (∑ z ∈ S, c z)
      = ∑ z : V, (if z ∈ S then A S * c z else 0) := by
    intro S
    rw [Finset.mul_sum, ← Finset.sum_filter]
    congr 1
    ext z
    simp
  calc ∑ S : Finset V, A S * (∑ z ∈ S, c z)
      = ∑ S : Finset V, ∑ z : V, (if z ∈ S then A S * c z else 0) :=
        Finset.sum_congr rfl fun S _ => step1 S
    _ = ∑ z : V, ∑ S : Finset V, (if z ∈ S then A S * c z else 0) := Finset.sum_comm
    _ = ∑ z : V, c z * ∑ S ∈ Finset.univ.filter (fun S : Finset V => z ∈ S), A S := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [← Finset.sum_filter, Finset.mul_sum]
        exact Finset.sum_congr rfl fun S _ => mul_comm _ _

private lemma es_pow_key {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (π : V → ℝ)
    (hπ : IsStationary P π) (hpos : ∀ x : V, 0 < π x) (x : V) (t : ℕ) :
    ∀ y : V, π x * ((P ^ t) x y)
      = π y * ∑ T ∈ Finset.univ.filter (fun T : Finset V => y ∈ T),
          ((evolvingSets P π) ^ t) {x} T := by
  classical
  induction t with
  | zero =>
      intro y
      have h0 : ∑ T ∈ Finset.univ.filter (fun T : Finset V => y ∈ T),
          ((evolvingSets P π) ^ 0) ({x} : Finset V) T
          = if y ∈ ({x} : Finset V) then (1 : ℝ) else 0 := by
        simp only [pow_zero, Matrix.one_apply]
        rw [Finset.sum_ite_eq (Finset.univ.filter (fun T : Finset V => y ∈ T))
          ({x} : Finset V) (fun _ => (1 : ℝ))]
        simp
      rw [h0]
      simp only [pow_zero, Matrix.one_apply, Finset.mem_singleton]
      by_cases h : y = x
      · subst h; simp
      · simp [h, Ne.symm h]
  | succ n ih =>
      intro y
      have hpow : ∀ T : Finset V, ((evolvingSets P π) ^ (n + 1)) ({x} : Finset V) T
          = ∑ S : Finset V, ((evolvingSets P π) ^ n) ({x} : Finset V) S
              * evolvingSets P π S T := by
        intro T
        rw [pow_succ]
        simp [Matrix.mul_apply]
      have e1 : π y * ∑ T ∈ Finset.univ.filter (fun T : Finset V => y ∈ T),
            ((evolvingSets P π) ^ (n + 1)) ({x} : Finset V) T
          = ∑ S : Finset V, ((evolvingSets P π) ^ n) ({x} : Finset V) S
              * (∑ z ∈ S, π z * P z y) := by
        rw [Finset.sum_congr rfl fun T _ => hpow T]
        rw [Finset.sum_comm]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [← Finset.mul_sum, ← es_col P hP π hπ hpos S y]
        ring
      rw [e1, subset_sum_swap]
      have e2 : ∀ z : V, (π z * P z y) *
            ∑ S ∈ Finset.univ.filter (fun S : Finset V => z ∈ S),
              ((evolvingSets P π) ^ n) ({x} : Finset V) S
          = P z y * (π x * ((P ^ n) x z)) := by
        intro z
        rw [ih z]
        ring
      rw [Finset.sum_congr rfl fun z _ => e2 z]
      rw [pow_succ, Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun z _ => by ring

end MarkovMixing

open MarkovMixing

/-- **Lemma 17.12** (LPW). -/
theorem MarkovMixing.evolving_sets_identity {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P)
    (π : V → ℝ) (hπ : IsStationary P π) (hpos : ∀ x : V, 0 < π x)
    (x y : V) (t : ℕ) :
    (P ^ t) x y = π y / π x *
      ∑ T ∈ Finset.univ.filter (fun T : Finset V => y ∈ T),
        ((evolvingSets P π) ^ t) {x} T := by
  have hx : π x ≠ 0 := ne_of_gt (hpos x)
  have hkey := es_pow_key P hP π hπ hpos x t y
  field_simp
  linarith [hkey]

open scoped BigOperators
open MarkovMixing

theorem MarkovMixing.tv_eq_half_l1 {V : Type*} [Fintype V] [DecidableEq V]
    (μ ν : V → ℝ) (hμ : IsDist μ) (hν : IsDist ν) :
    tvDist μ ν = 2⁻¹ * ∑ x, |μ x - ν x| ∧
    tvDist μ ν = ∑ x ∈ Finset.univ.filter (fun x : V => ν x ≤ μ x), (μ x - ν x) := by
  classical
  set p : V → Prop := fun x => ν x ≤ μ x with hp
  set B : Finset V := Finset.univ.filter p with hB
  set s : ℝ := ∑ x ∈ B, (μ x - ν x) with hs
  have hzero : ∑ x, (μ x - ν x) = 0 := by
    rw [Finset.sum_sub_distrib, hμ.2, hν.2, sub_self]
  have hsplit : ∑ x ∈ B, (μ x - ν x)
      + ∑ x ∈ Finset.univ.filter (fun x => ¬ p x), (μ x - ν x) = 0 := by
    rw [hB, Finset.sum_filter_add_sum_filter_not Finset.univ p (fun x => μ x - ν x)]
    exact hzero
  have hcompl : ∑ x ∈ Finset.univ.filter (fun x => ¬ p x), (μ x - ν x) = -s := by
    rw [hs]; linarith [hsplit]
  have hBnn : ∀ x ∈ B, 0 ≤ μ x - ν x := by
    intro x hx
    rw [hB, Finset.mem_filter] at hx
    linarith [hx.2]
  have hBcnp : ∀ x ∈ Finset.univ.filter (fun x => ¬ p x), μ x - ν x ≤ 0 := by
    intro x hx
    rw [Finset.mem_filter] at hx
    have := hx.2
    rw [hp] at this
    push_neg at this
    linarith
  have hs_nonneg : 0 ≤ s := by
    rw [hs]
    exact Finset.sum_nonneg hBnn
  -- the ℓ¹ identity
  have hl1 : ∑ x, |μ x - ν x| = 2 * s := by
    have hsp := Finset.sum_filter_add_sum_filter_not Finset.univ p (fun x => |μ x - ν x|)
    have h1 : ∑ x ∈ B, |μ x - ν x| = s := by
      rw [hs, hB]
      exact Finset.sum_congr rfl fun x hx => abs_of_nonneg (hBnn x (by rw [hB]; exact hx))
    have h2 : ∑ x ∈ Finset.univ.filter (fun x => ¬ p x), |μ x - ν x| = s := by
      have : ∑ x ∈ Finset.univ.filter (fun x => ¬ p x), |μ x - ν x|
          = ∑ x ∈ Finset.univ.filter (fun x => ¬ p x), -(μ x - ν x) :=
        Finset.sum_congr rfl fun x hx => abs_of_nonpos (hBcnp x hx)
      rw [this, Finset.sum_neg_distrib, hcompl, neg_neg]
    rw [← hsp, hB] at *
    linarith [h1, h2]
  -- the supremum is attained at `B`
  have hbdd : BddAbove (Set.range fun A : Finset V => |∑ x ∈ A, μ x - ∑ x ∈ A, ν x|) :=
    Set.Finite.bddAbove (Set.range fun A : Finset V => |∑ x ∈ A, μ x - ∑ x ∈ A, ν x|).toFinite
  have hupper : ∀ A : Finset V, |∑ x ∈ A, μ x - ∑ x ∈ A, ν x| ≤ s := by
    intro A
    have hrw : ∑ x ∈ A, μ x - ∑ x ∈ A, ν x = ∑ x ∈ A, (μ x - ν x) := by
      rw [Finset.sum_sub_distrib]
    rw [hrw, abs_le]
    have hAsp := Finset.sum_filter_add_sum_filter_not A p (fun x => μ x - ν x)
    have hA1 : ∑ x ∈ A.filter p, (μ x - ν x) ≤ s := by
      rw [hs]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun x hx _ => hBnn x hx)
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [hB, Finset.mem_filter]
      exact ⟨Finset.mem_univ x, hx.2⟩
    have hA1nn : 0 ≤ ∑ x ∈ A.filter p, (μ x - ν x) :=
      Finset.sum_nonneg fun x hx => hBnn x (by
        rw [Finset.mem_filter] at hx
        rw [hB, Finset.mem_filter]
        exact ⟨Finset.mem_univ x, hx.2⟩)
    have hA2np : ∑ x ∈ A.filter (fun x => ¬ p x), (μ x - ν x) ≤ 0 :=
      Finset.sum_nonpos fun x hx => hBcnp x (by
        rw [Finset.mem_filter] at hx
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ x, hx.2⟩)
    have hA2ge : -s ≤ ∑ x ∈ A.filter (fun x => ¬ p x), (μ x - ν x) := by
      rw [← hcompl]
      have hsub : ∑ x ∈ Finset.univ.filter (fun x => ¬ p x), (μ x - ν x)
          ≤ ∑ x ∈ A.filter (fun x => ¬ p x), (μ x - ν x) := by
        have hneg : ∑ x ∈ A.filter (fun x => ¬ p x), (-(μ x - ν x))
            ≤ ∑ x ∈ Finset.univ.filter (fun x => ¬ p x), (-(μ x - ν x)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun x hx _ => ?_)
          · intro x hx
            rw [Finset.mem_filter] at hx
            rw [Finset.mem_filter]
            exact ⟨Finset.mem_univ x, hx.2⟩
          · have := hBcnp x hx
            linarith
        rw [Finset.sum_neg_distrib, Finset.sum_neg_distrib] at hneg
        linarith
      linarith
    constructor <;> linarith [hAsp, hA1, hA1nn, hA2np, hA2ge]
  have hattain : |∑ x ∈ B, μ x - ∑ x ∈ B, ν x| = s := by
    have hrw : ∑ x ∈ B, μ x - ∑ x ∈ B, ν x = s := by
      rw [hs, Finset.sum_sub_distrib]
    rw [hrw, abs_of_nonneg hs_nonneg]
  have htv : tvDist μ ν = s := by
    refine le_antisymm (ciSup_le hupper) ?_
    rw [← hattain]
    exact le_ciSup hbdd B
  exact ⟨by rw [htv, hl1]; ring, by rw [htv, hs, hB]⟩

/-!
# Mixing from the evolving-set process (Morris–Peres; LPW Theorem 17.10)
-/

namespace MarkovMixing

noncomputable section
open scoped BigOperators
open Finset MeasureTheory

section LayerCake

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (P : Matrix V V ℝ) (π : V → ℝ) (S : Finset V)

/-- The clamped threshold function whose superlevel sets are the possible
successors of `S`. -/
private def cth (y : V) : ℝ := min 1 (max 0 (esThresh P π S y))

private lemma cth_nonneg (y : V) : 0 ≤ cth P π S y := by
  simp only [cth, le_min_iff]
  exact ⟨by norm_num, le_max_left _ _⟩

private lemma cth_le_one (y : V) : cth P π S y ≤ 1 := min_le_left _ _

/-- The superlevel set at level `u`. -/
private def lev (u : ℝ) : Finset V := Finset.univ.filter (fun y => u ≤ cth P π S y)

private lemma esUpper_le_one (T : Finset V) : esUpper P π S T ≤ 1 := by
  rw [esUpper]
  split_ifs with h
  · exact Finset.inf'_le_of_le _ h.choose_spec (cth_le_one P π S _)
  · exact le_refl 1

private lemma esLower_nonneg (T : Finset V) : 0 ≤ esLower P π S T := by
  rw [esLower]
  split_ifs with h
  · exact le_trans (cth_nonneg P π S h.choose) (Finset.le_sup' _ h.choose_spec)
  · exact le_refl 0

private lemma lev_eq_of_mem_Ioc {T : Finset V} {u : ℝ}
    (hu : u ∈ Set.Ioc (esLower P π S T) (esUpper P π S T)) : lev P π S u = T := by
  obtain ⟨hl, hup⟩ := hu
  ext y
  simp only [lev, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hy
    by_contra hyT
    have hmem : y ∈ Tᶜ := Finset.mem_compl.mpr hyT
    have hne : (Tᶜ : Finset V).Nonempty := ⟨y, hmem⟩
    have : cth P π S y ≤ esLower P π S T := by
      rw [esLower, dif_pos hne]
      exact Finset.le_sup' _ hmem
    linarith
  · intro hy
    have hne : T.Nonempty := ⟨y, hy⟩
    have : esUpper P π S T ≤ cth P π S y := by
      rw [esUpper, dif_pos hne]
      exact Finset.inf'_le _ hy
    linarith

private lemma mem_Ioc_lev {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    u ∈ Set.Ioc (esLower P π S (lev P π S u)) (esUpper P π S (lev P π S u)) := by
  constructor
  · rw [esLower]
    split_ifs with h
    · rw [Finset.sup'_lt_iff]
      intro y hy
      have hy' : y ∉ lev P π S u := by
        simpa using Finset.mem_compl.mp hy
      simp only [lev, Finset.mem_filter, Finset.mem_univ, true_and] at hy'
      show cth P π S y < u
      exact not_le.mp hy' 
    · exact hu
  · rw [esUpper]
    split_ifs with h
    · rw [Finset.le_inf'_iff]
      intro y hy
      simp only [lev, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      exact hy
    · exact hu1

private lemma es_eq_volume (T : Finset V) :
    evolvingSets P π S T
      = (volume (Set.Ioc (esLower P π S T) (esUpper P π S T))).toReal := by
  rw [evolvingSets, Real.volume_Ioc, ENNReal.toReal_ofReal']
  exact max_comm _ _

private lemma es_pairwise_disjoint :
    ∀ T ∈ (Finset.univ : Finset (Finset V)), ∀ T' ∈ (Finset.univ : Finset (Finset V)),
      T ≠ T' → Disjoint (Set.Ioc (esLower P π S T) (esUpper P π S T))
        (Set.Ioc (esLower P π S T') (esUpper P π S T')) := by
  intro T _ T' _ hne
  rw [Set.disjoint_left]
  intro u hu hu'
  exact hne ((lev_eq_of_mem_Ioc P π S hu).symm.trans (lev_eq_of_mem_Ioc P π S hu'))

private lemma es_sum_one : ∑ T : Finset V, evolvingSets P π S T = 1 := by
  have hmeas : ∀ T : Finset V,
      MeasurableSet (Set.Ioc (esLower P π S T) (esUpper P π S T)) := fun T => measurableSet_Ioc
  have hunion : (⋃ T ∈ (Finset.univ : Finset (Finset V)),
      Set.Ioc (esLower P π S T) (esUpper P π S T)) = Set.Ioc (0 : ℝ) 1 := by
    ext u
    simp only [Set.mem_iUnion, Finset.mem_univ, exists_prop, true_and, Set.mem_Ioc]
    constructor
    · rintro ⟨T, hT⟩
      exact ⟨lt_of_le_of_lt (esLower_nonneg P π S T) hT.1,
        le_trans hT.2 (esUpper_le_one P π S T)⟩
    · rintro ⟨h0, h1⟩
      exact ⟨lev P π S u, mem_Ioc_lev P π S h0 h1⟩
  have hvol := measure_biUnion_finset (μ := (volume : Measure ℝ))
    (s := (Finset.univ : Finset (Finset V)))
    (f := fun T => Set.Ioc (esLower P π S T) (esUpper P π S T))
    (by
      intro T hT T' hT' hne
      exact es_pairwise_disjoint P π S T hT T' hT' hne)
    (fun T _ => hmeas T)
  rw [hunion, Real.volume_Ioc] at hvol
  have := congrArg ENNReal.toReal hvol
  rw [ENNReal.toReal_sum (fun T _ => by
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)] at this
  rw [Finset.sum_congr rfl (fun T _ => es_eq_volume P π S T), ← this]
  simp

private lemma es_sum_mem (y : V) :
    ∑ T ∈ Finset.univ.filter (fun T : Finset V => y ∈ T), evolvingSets P π S T
      = cth P π S y := by
  have hmeas : ∀ T : Finset V,
      MeasurableSet (Set.Ioc (esLower P π S T) (esUpper P π S T)) := fun T => measurableSet_Ioc
  have hunion : (⋃ T ∈ (Finset.univ.filter (fun T : Finset V => y ∈ T)),
      Set.Ioc (esLower P π S T) (esUpper P π S T)) = Set.Ioc (0 : ℝ) (cth P π S y) := by
    ext u
    simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and, exists_prop,
      Set.mem_Ioc]
    constructor
    · rintro ⟨T, hyT, hu⟩
      refine ⟨lt_of_le_of_lt (esLower_nonneg P π S T) hu.1, ?_⟩
      have := lev_eq_of_mem_Ioc P π S hu
      rw [← this] at hyT
      simpa [lev] using hyT
    · rintro ⟨h0, h1⟩
      refine ⟨lev P π S u, ?_, mem_Ioc_lev P π S h0 (le_trans h1 (cth_le_one P π S y))⟩
      simp only [lev, Finset.mem_filter, Finset.mem_univ, true_and]
      exact h1
  have hvol := measure_biUnion_finset (μ := (volume : Measure ℝ))
    (s := (Finset.univ.filter (fun T : Finset V => y ∈ T)))
    (f := fun T => Set.Ioc (esLower P π S T) (esUpper P π S T))
    (by
      intro T hT T' hT' hne
      exact es_pairwise_disjoint P π S T (Finset.mem_univ T) T' (Finset.mem_univ T') hne)
    (fun T _ => hmeas T)
  rw [hunion, Real.volume_Ioc] at hvol
  have h2 := congrArg ENNReal.toReal hvol
  rw [ENNReal.toReal_sum (fun T _ => by
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)] at h2
  rw [Finset.sum_congr rfl (fun T _ => es_eq_volume P π S T), ← h2, sub_zero,
    ENNReal.toReal_ofReal (cth_nonneg P π S y)]

end LayerCake

/-! ### Threshold bounds from laziness -/

section Thresholds

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {P : Matrix V V ℝ} {π : V → ℝ}

private lemma thresh_nonneg (hP : IsStochastic P) (hpos : ∀ x, 0 < π x)
    (S : Finset V) (y : V) : 0 ≤ esThresh P π S y :=
  div_nonneg (Finset.sum_nonneg fun x _ => mul_nonneg (hpos x).le (hP.1 x y)) (hpos y).le

private lemma sum_all_eq (hπ : IsStationary P π) (y : V) : ∑ x, π x * P x y = π y := by
  have := congrFun hπ.2 y
  simpa [Matrix.vecMul, dotProduct] using this

private lemma thresh_le_one (hP : IsStochastic P) (hπ : IsStationary P π)
    (hpos : ∀ x, 0 < π x) (S : Finset V) (y : V) : esThresh P π S y ≤ 1 := by
  rw [esThresh, div_le_one (hpos y)]
  calc ∑ x ∈ S, π x * P x y ≤ ∑ x, π x * P x y :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
          (fun x _ _ => mul_nonneg (hpos x).le (hP.1 x y))
    _ = π y := sum_all_eq hπ y

private lemma cth_eq_thresh (hP : IsStochastic P) (hπ : IsStationary P π)
    (hpos : ∀ x, 0 < π x) (S : Finset V) (y : V) :
    cth P π S y = esThresh P π S y := by
  rw [cth, max_eq_right (thresh_nonneg hP hpos S y),
    min_eq_right (thresh_le_one hP hπ hpos S y)]

private lemma thresh_ge_half (hP : IsStochastic P) (hpos : ∀ x, 0 < π x)
    (hlazy : ∀ x : V, 2⁻¹ ≤ P x x) {S : Finset V} {y : V} (hy : y ∈ S) :
    2⁻¹ ≤ esThresh P π S y := by
  rw [esThresh, le_div_iff₀ (hpos y)]
  calc 2⁻¹ * π y ≤ π y * P y y := by nlinarith [hlazy y, hpos y]
    _ ≤ ∑ x ∈ S, π x * P x y :=
        Finset.single_le_sum (f := fun x => π x * P x y)
          (fun x _ => mul_nonneg (hpos x).le (hP.1 x y)) hy

private lemma thresh_le_half (hP : IsStochastic P) (hπ : IsStationary P π)
    (hpos : ∀ x, 0 < π x) (hlazy : ∀ x : V, 2⁻¹ ≤ P x x) {S : Finset V} {y : V}
    (hy : y ∉ S) : esThresh P π S y ≤ 2⁻¹ := by
  rw [esThresh, div_le_iff₀ (hpos y)]
  have hsub : S ⊆ Finset.univ.erase y := by
    intro z hz
    exact Finset.mem_erase.mpr ⟨fun hc => hy (hc ▸ hz), Finset.mem_univ z⟩
  have h1 : ∑ x ∈ S, π x * P x y ≤ ∑ x ∈ Finset.univ.erase y, π x * P x y :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun x _ _ => mul_nonneg (hpos x).le (hP.1 x y))
  have h2 : ∑ x ∈ Finset.univ.erase y, π x * P x y + π y * P y y = π y := by
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ y)]
    exact sum_all_eq hπ y
  nlinarith [hlazy y, hpos y]

/-- With a lazy chain the evolving set moves monotonically. -/
private lemma es_monotone (hP : IsStochastic P) (hπ : IsStationary P π)
    (hpos : ∀ x, 0 < π x) (hlazy : ∀ x : V, 2⁻¹ ≤ P x x) (S T : Finset V)
    (hw : 0 < evolvingSets P π S T) : S ⊆ T ∨ T ⊆ S := by
  have hlt : esLower P π S T < esUpper P π S T := by
    by_contra hc
    push_neg at hc
    rw [evolvingSets] at hw
    simp only [lt_max_iff] at hw
    rcases hw with h | h
    · exact lt_irrefl 0 h
    · linarith
  by_cases hcase : esUpper P π S T ≤ 2⁻¹
  · -- the level is at most 1/2, so `S ⊆ T`
    left
    intro y hy
    have hT : lev P π S (esUpper P π S T) = T :=
      lev_eq_of_mem_Ioc P π S ⟨hlt, le_refl _⟩
    rw [← hT]
    simp only [lev, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [cth_eq_thresh hP hπ hpos]
    exact le_trans hcase (thresh_ge_half hP hpos hlazy hy)
  · -- the level exceeds 1/2, so `T ⊆ S`
    right
    push_neg at hcase
    intro y hy
    by_contra hyS
    have hu : max (esLower P π S T) 2⁻¹ < esUpper P π S T := by
      rw [max_lt_iff]
      exact ⟨hlt, hcase⟩
    set u : ℝ := (max (esLower P π S T) 2⁻¹ + esUpper P π S T) / 2 with hudef
    have hu1 : esLower P π S T < u := by
      have := le_max_left (esLower P π S T) (2⁻¹ : ℝ)
      rw [hudef]; linarith
    have hu2 : u ≤ esUpper P π S T := by rw [hudef]; linarith
    have hu3 : (2⁻¹ : ℝ) < u := by
      have := le_max_right (esLower P π S T) (2⁻¹ : ℝ)
      rw [hudef]; linarith
    have hT : lev P π S u = T := lev_eq_of_mem_Ioc P π S ⟨hu1, hu2⟩
    rw [← hT] at hy
    simp only [lev, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    rw [cth_eq_thresh hP hπ hpos] at hy
    have := thresh_le_half hP hπ hpos hlazy hyS
    linarith

end Thresholds

/-! ### The mean and the mean displacement of `π(S₁)` -/

section Moments

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {P : Matrix V V ℝ} {π : V → ℝ}

private def piS (π : V → ℝ) (S : Finset V) : ℝ := ∑ y ∈ S, π y

private def qflow (P : Matrix V V ℝ) (π : V → ℝ) (S : Finset V) : ℝ :=
  ∑ x ∈ S, ∑ y ∈ Sᶜ, π x * P x y

private lemma pi_thresh (hpos : ∀ x, 0 < π x) (S : Finset V) (y : V) :
    π y * esThresh P π S y = ∑ x ∈ S, π x * P x y := by
  rw [esThresh, mul_div_cancel₀ _ (ne_of_gt (hpos y))]

private lemma es_mean (hP : IsStochastic P) (hπ : IsStationary P π)
    (hpos : ∀ x, 0 < π x) (S : Finset V) :
    ∑ T : Finset V, evolvingSets P π S T * piS π T = piS π S := by
  classical
  have hswap : ∑ T : Finset V, evolvingSets P π S T * piS π T
      = ∑ y : V, π y * ∑ T ∈ Finset.univ.filter (fun T : Finset V => y ∈ T),
          evolvingSets P π S T := by
    have h1 : ∀ T : Finset V, evolvingSets P π S T * piS π T
        = ∑ y : V, (if y ∈ T then π y * evolvingSets P π S T else 0) := by
      intro T
      rw [piS, Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [Finset.sum_congr rfl (fun T _ => h1 T), Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_filter]
  rw [hswap, Finset.sum_congr rfl (fun y (_ : y ∈ Finset.univ) => by
      rw [es_sum_mem P π S y, cth_eq_thresh hP hπ hpos, pi_thresh hpos] :
    ∀ y ∈ Finset.univ, π y * ∑ T ∈ Finset.univ.filter (fun T : Finset V => y ∈ T),
        evolvingSets P π S T = ∑ x ∈ S, π x * P x y)]
  rw [Finset.sum_comm, piS]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.mul_sum, hP.2 x, mul_one]

private def dsym (π : V → ℝ) (S T : Finset V) : ℝ :=
  ∑ y : V, π y * |(if y ∈ T then (1:ℝ) else 0) - (if y ∈ S then (1:ℝ) else 0)|

private lemma abs_piS_eq_dsym (hpos : ∀ x, 0 < π x) {S T : Finset V}
    (h : S ⊆ T ∨ T ⊆ S) : |piS π T - piS π S| = dsym π S T := by
  classical
  rcases h with h | h
  · have hd : piS π T - piS π S = ∑ y ∈ T \ S, π y := by
      rw [piS, piS, ← Finset.sum_sdiff h]
      ring
    have hd2 : dsym π S T = ∑ y ∈ T \ S, π y := by
      rw [dsym, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun y => y ∈ T \ S)]
      have h1 : ∑ y ∈ Finset.univ.filter (fun y => y ∈ T \ S),
          π y * |(if y ∈ T then (1:ℝ) else 0) - (if y ∈ S then (1:ℝ) else 0)|
          = ∑ y ∈ T \ S, π y := by
        rw [show Finset.univ.filter (fun y => y ∈ T \ S) = T \ S from by
          ext y; simp]
        refine Finset.sum_congr rfl fun y hy => ?_
        rw [Finset.mem_sdiff] at hy
        rw [if_pos hy.1, if_neg hy.2]
        norm_num
      have h2 : ∑ y ∈ Finset.univ.filter (fun y => ¬ (y ∈ T \ S)),
          π y * |(if y ∈ T then (1:ℝ) else 0) - (if y ∈ S then (1:ℝ) else 0)| = 0 := by
        refine Finset.sum_eq_zero fun y hy => ?_
        have hy' : ¬ (y ∈ T \ S) := (Finset.mem_filter.mp hy).2
        rw [Finset.mem_sdiff] at hy'
        push_neg at hy'
        by_cases hyS : y ∈ S
        · rw [if_pos (h hyS), if_pos hyS]; norm_num
        · rw [if_neg (fun hc => hyS (hy' hc)), if_neg hyS]; norm_num
      rw [h1, h2, add_zero]
    rw [hd, hd2, abs_of_nonneg (Finset.sum_nonneg fun y _ => (hpos y).le)]
  · have hd : piS π S - piS π T = ∑ y ∈ S \ T, π y := by
      rw [piS, piS, ← Finset.sum_sdiff h]
      ring
    have hd2 : dsym π S T = ∑ y ∈ S \ T, π y := by
      rw [dsym, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun y => y ∈ S \ T)]
      have h1 : ∑ y ∈ Finset.univ.filter (fun y => y ∈ S \ T),
          π y * |(if y ∈ T then (1:ℝ) else 0) - (if y ∈ S then (1:ℝ) else 0)|
          = ∑ y ∈ S \ T, π y := by
        rw [show Finset.univ.filter (fun y => y ∈ S \ T) = S \ T from by
          ext y; simp]
        refine Finset.sum_congr rfl fun y hy => ?_
        rw [Finset.mem_sdiff] at hy
        rw [if_neg hy.2, if_pos hy.1]
        norm_num
      have h2 : ∑ y ∈ Finset.univ.filter (fun y => ¬ (y ∈ S \ T)),
          π y * |(if y ∈ T then (1:ℝ) else 0) - (if y ∈ S then (1:ℝ) else 0)| = 0 := by
        refine Finset.sum_eq_zero fun y hy => ?_
        have hy' : ¬ (y ∈ S \ T) := (Finset.mem_filter.mp hy).2
        rw [Finset.mem_sdiff] at hy'
        push_neg at hy'
        by_cases hyT : y ∈ T
        · rw [if_pos hyT, if_pos (h hyT)]; norm_num
        · rw [if_neg hyT, if_neg (fun hc => hyT (hy' hc))]; norm_num
      rw [h1, h2, add_zero]
    rw [abs_sub_comm, hd, hd2, abs_of_nonneg (Finset.sum_nonneg fun y _ => (hpos y).le)]

private lemma es_l1 (hP : IsStochastic P) (hπ : IsStationary P π)
    (hpos : ∀ x, 0 < π x) (hlazy : ∀ x : V, 2⁻¹ ≤ P x x) (S : Finset V) :
    ∑ T : Finset V, evolvingSets P π S T * |piS π T - piS π S| = 2 * qflow P π S := by
  classical
  have hnn : ∀ T : Finset V, 0 ≤ evolvingSets P π S T := fun T => le_max_left _ _
  have hstep : ∀ T : Finset V, evolvingSets P π S T * |piS π T - piS π S|
      = evolvingSets P π S T * dsym π S T := by
    intro T
    rcases eq_or_lt_of_le (hnn T) with h | h
    · rw [← h]; ring
    · rw [abs_piS_eq_dsym hpos (es_monotone hP hπ hpos hlazy S T h)]
  rw [Finset.sum_congr rfl (fun T _ => hstep T)]
  have hswap : ∑ T : Finset V, evolvingSets P π S T * dsym π S T
      = ∑ y : V, π y * (∑ T : Finset V, evolvingSets P π S T *
          |(if y ∈ T then (1:ℝ) else 0) - (if y ∈ S then (1:ℝ) else 0)|) := by
    simp only [dsym, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun T _ => by ring
  rw [hswap]
  have hin : ∀ y : V, (∑ T : Finset V, evolvingSets P π S T *
      |(if y ∈ T then (1:ℝ) else 0) - (if y ∈ S then (1:ℝ) else 0)|)
      = if y ∈ S then 1 - esThresh P π S y else esThresh P π S y := by
    intro y
    have hmem : ∑ T : Finset V, (if y ∈ T then evolvingSets P π S T else 0)
        = esThresh P π S y := by
      rw [← Finset.sum_filter, es_sum_mem P π S y, cth_eq_thresh hP hπ hpos]
    by_cases hy : y ∈ S
    · rw [if_pos hy]
      have hrw : ∀ T : Finset V, evolvingSets P π S T *
          |(if y ∈ T then (1:ℝ) else 0) - 1|
          = evolvingSets P π S T - (if y ∈ T then evolvingSets P π S T else 0) := by
        intro T
        by_cases hyT : y ∈ T
        · rw [if_pos hyT, if_pos hyT]; norm_num
        · rw [if_neg hyT, if_neg hyT]; norm_num
      rw [Finset.sum_congr rfl (fun T _ => hrw T), Finset.sum_sub_distrib,
        es_sum_one P π S, hmem, if_pos hy]
    · rw [if_neg hy]
      have hrw : ∀ T : Finset V, evolvingSets P π S T *
          |(if y ∈ T then (1:ℝ) else 0) - 0|
          = (if y ∈ T then evolvingSets P π S T else 0) := by
        intro T
        by_cases hyT : y ∈ T
        · rw [if_pos hyT, if_pos hyT]; norm_num
        · rw [if_neg hyT, if_neg hyT]; norm_num
      rw [Finset.sum_congr rfl (fun T _ => hrw T), hmem, if_neg hy]
  rw [Finset.sum_congr rfl (fun y (_ : y ∈ Finset.univ) => by rw [hin y] :
    ∀ y ∈ Finset.univ, π y * (∑ T : Finset V, evolvingSets P π S T *
      |(if y ∈ T then (1:ℝ) else 0) - (if y ∈ S then (1:ℝ) else 0)|)
      = π y * (if y ∈ S then 1 - esThresh P π S y else esThresh P π S y))]
  rw [← Finset.sum_add_sum_compl S
    (fun y => π y * (if y ∈ S then 1 - esThresh P π S y else esThresh P π S y))]
  have hA : ∑ y ∈ S, π y * (if y ∈ S then 1 - esThresh P π S y else esThresh P π S y)
      = ∑ y ∈ S, (π y - ∑ x ∈ S, π x * P x y) := by
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [if_pos hy, mul_sub, mul_one, pi_thresh hpos]
  have hB : ∑ y ∈ Sᶜ, π y * (if y ∈ S then 1 - esThresh P π S y else esThresh P π S y)
      = ∑ y ∈ Sᶜ, ∑ x ∈ S, π x * P x y := by
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [if_neg (Finset.mem_compl.mp hy), pi_thresh hpos]
  rw [hA, hB]
  have hB' : ∑ y ∈ Sᶜ, ∑ x ∈ S, π x * P x y = qflow P π S := by
    rw [qflow, Finset.sum_comm]
  have hrow : ∀ x ∈ S, π x = ∑ y ∈ S, π x * P x y + ∑ y ∈ Sᶜ, π x * P x y := by
    intro x _
    rw [Finset.sum_add_sum_compl, ← Finset.mul_sum, hP.2 x, mul_one]
  have hA' : ∑ y ∈ S, (π y - ∑ x ∈ S, π x * P x y) = qflow P π S := by
    rw [Finset.sum_sub_distrib]
    have h1 : ∑ y ∈ S, π y = ∑ x ∈ S, (∑ y ∈ S, π x * P x y + ∑ y ∈ Sᶜ, π x * P x y) :=
      Finset.sum_congr rfl hrow
    have h2 : ∑ y ∈ S, ∑ x ∈ S, π x * P x y = ∑ x ∈ S, ∑ y ∈ S, π x * P x y :=
      Finset.sum_comm
    rw [h1, h2, Finset.sum_add_distrib, qflow]
    ring
  rw [hA', hB']
  ring

end Moments

/-! ### The one-step contraction of `√(z(1-z))` -/

section Contraction

private def ff (z : ℝ) : ℝ := Real.sqrt (z * (1 - z))

private lemma ff_nonneg (z : ℝ) : 0 ≤ ff z := Real.sqrt_nonneg _

private lemma ff_sq {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) : ff z ^ 2 = z * (1 - z) :=
  Real.sq_sqrt (by nlinarith)

private lemma ff_symm (z : ℝ) : ff (1 - z) = ff z := by
  rw [ff, ff]; congr 1; ring

private lemma ff_pos {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) : 0 < ff z :=
  Real.sqrt_pos.mpr (by nlinarith)

private lemma ff_le_half {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) : ff z ≤ 2⁻¹ := by
  have h := ff_sq hz0 hz1
  nlinarith [ff_nonneg z, sq_nonneg (z - 2⁻¹)]

private lemma key_ineq {z Z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hZ0 : 0 < Z) (hZ1 : Z < 1) :
    ff z * ff Z ≤ (z * (1 - Z) + (1 - z) * Z) / 2 - (z - Z) ^ 2 / (4 * (z + Z)) := by
  have hA0 : (0:ℝ) ≤ z * (1 - Z) := by nlinarith
  have hB0 : (0:ℝ) ≤ (1 - z) * Z := by nlinarith
  set A := Real.sqrt (z * (1 - Z)) with hAdef
  set B := Real.sqrt ((1 - z) * Z) with hBdef
  have hA : A ^ 2 = z * (1 - Z) := Real.sq_sqrt hA0
  have hB : B ^ 2 = (1 - z) * Z := Real.sq_sqrt hB0
  have hAn : 0 ≤ A := Real.sqrt_nonneg _
  have hBn : 0 ≤ B := Real.sqrt_nonneg _
  have hAB : ff z * ff Z = A * B := by
    rw [ff, ff, hAdef, hBdef, ← Real.sqrt_mul (by nlinarith), ← Real.sqrt_mul hA0]
    congr 1
    ring
  have hzZ : 0 < z + Z := by linarith
  have hsq : (z - Z) ^ 2 ≤ (A - B) ^ 2 * (2 * (z + Z)) := by
    have h1 : ((A - B) * (A + B)) ^ 2 = (z - Z) ^ 2 := by
      have : (A - B) * (A + B) = A ^ 2 - B ^ 2 := by ring
      rw [this, hA, hB]
      ring_nf
    have h2 : (A + B) ^ 2 ≤ 2 * (z + Z) := by nlinarith [sq_nonneg (A - B)]
    nlinarith [sq_nonneg (A - B), sq_nonneg (A + B)]
  have hfin : (z - Z) ^ 2 / (4 * (z + Z)) ≤ (A - B) ^ 2 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith [hsq]
  rw [hAB]
  nlinarith [hfin, hA, hB]

private lemma weighted_contract {ι : Type*} (s : Finset ι) (w z : ι → ℝ)
    (Z q : ℝ) (hw : ∀ i ∈ s, 0 < w i) (hw1 : ∑ i ∈ s, w i = 1)
    (hz0 : ∀ i ∈ s, 0 ≤ z i) (hz1 : ∀ i ∈ s, z i ≤ 1)
    (hmean : ∑ i ∈ s, w i * z i = Z) (hq : 2 * q ≤ ∑ i ∈ s, w i * |z i - Z|)
    (hq0 : 0 ≤ q) (hZ0 : 0 < Z) (hZ1 : Z < 1) :
    ∑ i ∈ s, w i * ff (z i) ≤ ff Z - q ^ 2 / (2 * Z * ff Z) := by
  have hffZ : 0 < ff Z := ff_pos hZ0 hZ1
  have hffZ2 : ff Z ^ 2 = Z * (1 - Z) := ff_sq hZ0.le hZ1.le
  -- the Engel form of Cauchy-Schwarz
  have hgpos : ∀ i ∈ s, 0 < w i * (z i + Z) := fun i hi =>
    mul_pos (hw i hi) (by have := hz0 i hi; linarith)
  have hden : ∑ i ∈ s, w i * (z i + Z) = 2 * Z := by
    have : ∀ i ∈ s, w i * (z i + Z) = w i * z i + Z * w i := fun i _ => by ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, hmean, ← Finset.mul_sum, hw1]
    ring
  have hCS := sq_sum_div_le_sum_sq_div s (fun i => w i * |z i - Z|)
    (g := fun i => w i * (z i + Z)) hgpos
  rw [hden] at hCS
  have hterm : ∀ i ∈ s, (w i * |z i - Z|) ^ 2 / (w i * (z i + Z))
      = w i * ((z i - Z) ^ 2 / (z i + Z)) := by
    intro i hi
    have hwi := hw i hi
    have hzi : 0 < z i + Z := by have := hz0 i hi; linarith
    rw [mul_pow, sq_abs]
    field_simp
    try ring
  rw [Finset.sum_congr rfl hterm] at hCS
  have hqsum : 0 ≤ ∑ i ∈ s, w i * |z i - Z| :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi).le (abs_nonneg _)
  have hSig : 2 * q ^ 2 / Z ≤ ∑ i ∈ s, w i * ((z i - Z) ^ 2 / (z i + Z)) := by
    refine le_trans ?_ hCS
    have h4 : (2 * q) ^ 2 ≤ (∑ i ∈ s, w i * |z i - Z|) ^ 2 :=
      pow_le_pow_left₀ (by linarith) hq 2
    rw [div_le_div_iff₀ hZ0 (by linarith)]
    nlinarith [h4, hZ0]
  -- the pointwise inequality summed
  have hmain : (∑ i ∈ s, w i * ff (z i)) * ff Z
      ≤ Z * (1 - Z) - (∑ i ∈ s, w i * ((z i - Z) ^ 2 / (z i + Z))) / 4 := by
    have hstep : ∀ i ∈ s, w i * ff (z i) * ff Z
        ≤ w i * ((z i * (1 - Z) + (1 - z i) * Z) / 2
            - (z i - Z) ^ 2 / (4 * (z i + Z))) := by
      intro i hi
      have hk := key_ineq (hz0 i hi) (hz1 i hi) hZ0 hZ1
      calc w i * ff (z i) * ff Z = w i * (ff (z i) * ff Z) := by ring
        _ ≤ w i * ((z i * (1 - Z) + (1 - z i) * Z) / 2
              - (z i - Z) ^ 2 / (4 * (z i + Z))) :=
            mul_le_mul_of_nonneg_left hk (hw i hi).le
    rw [Finset.sum_mul]
    refine le_trans (Finset.sum_le_sum hstep) ?_
    have hexp : ∀ i ∈ s, w i * ((z i * (1 - Z) + (1 - z i) * Z) / 2
          - (z i - Z) ^ 2 / (4 * (z i + Z)))
        = ((1 - Z) / 2) * (w i * z i) + (Z / 2) * (w i - w i * z i)
          - (1/4) * (w i * ((z i - Z) ^ 2 / (z i + Z))) := by
      intro i hi
      have hzi : (0:ℝ) < z i + Z := by have := hz0 i hi; linarith
      field_simp
      try ring
    refine le_of_eq ?_
    rw [Finset.sum_congr rfl hexp, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_sub_distrib,
      hmean, hw1]
    ring
  rw [← hffZ2] at hmain
  have hfinal : (∑ i ∈ s, w i * ff (z i)) * ff Z ≤ ff Z ^ 2 - q ^ 2 / (2 * Z) := by
    have hSig' : 2 * q ^ 2 ≤ (∑ i ∈ s, w i * ((z i - Z) ^ 2 / (z i + Z))) * Z := by
      rw [div_le_iff₀ hZ0] at hSig
      linarith
    have : (∑ i ∈ s, w i * ((z i - Z) ^ 2 / (z i + Z))) / 4 ≥ q ^ 2 / (2 * Z) := by
      rw [ge_iff_le, div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith [hSig']
    linarith
  have hrw : ff Z - q ^ 2 / (2 * Z * ff Z) = (ff Z ^ 2 - q ^ 2 / (2 * Z)) / ff Z := by
    field_simp
    try ring
  rw [hrw, le_div_iff₀ hffZ]
  exact hfinal

private lemma weighted_contract' {ι : Type*} (s : Finset ι) (w z : ι → ℝ)
    (Z q : ℝ) (hw : ∀ i ∈ s, 0 < w i) (hw1 : ∑ i ∈ s, w i = 1)
    (hz0 : ∀ i ∈ s, 0 ≤ z i) (hz1 : ∀ i ∈ s, z i ≤ 1)
    (hmean : ∑ i ∈ s, w i * z i = Z) (hq : 2 * q ≤ ∑ i ∈ s, w i * |z i - Z|)
    (hq0 : 0 ≤ q) (hZ0 : 0 < Z) (hZ1 : Z < 1) :
    ∑ i ∈ s, w i * ff (z i) ≤ ff Z - q ^ 2 / (2 * (1 - Z) * ff Z) := by
  have hmean' : ∑ i ∈ s, w i * (1 - z i) = 1 - Z := by
    have : ∀ i ∈ s, w i * (1 - z i) = w i - w i * z i := fun i _ => by ring
    rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, hw1, hmean]
  have hq' : 2 * q ≤ ∑ i ∈ s, w i * |(1 - z i) - (1 - Z)| := by
    refine le_trans hq (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    congr 1
    rw [show (1 - z i) - (1 - Z) = -(z i - Z) from by ring, abs_neg]
  have h := weighted_contract s w (fun i => 1 - z i) (1 - Z) q hw hw1
    (fun i hi => by linarith [hz1 i hi]) (fun i hi => by linarith [hz0 i hi])
    hmean' hq' hq0 (by linarith) (by linarith)
  simpa only [ff_symm, sub_sub_cancel] using h

private lemma weighted_final {ι : Type*} (s : Finset ι) (w z : ι → ℝ)
    (Z q Φ : ℝ) (hw : ∀ i ∈ s, 0 < w i) (hw1 : ∑ i ∈ s, w i = 1)
    (hz0 : ∀ i ∈ s, 0 ≤ z i) (hz1 : ∀ i ∈ s, z i ≤ 1)
    (hmean : ∑ i ∈ s, w i * z i = Z) (hq : 2 * q ≤ ∑ i ∈ s, w i * |z i - Z|)
    (hq0 : 0 ≤ q) (hZ0 : 0 < Z) (hZ1 : Z < 1)
    (hΦ0 : 0 ≤ Φ) (hqmin : Φ * min Z (1 - Z) ≤ q) :
    ∑ i ∈ s, w i * ff (z i) ≤ (1 - Φ ^ 2 / 2) * ff Z := by
  have hffZ : 0 < ff Z := ff_pos hZ0 hZ1
  have hffZ2 : ff Z ^ 2 = Z * (1 - Z) := ff_sq hZ0.le hZ1.le
  rcases le_or_gt Z 2⁻¹ with hc | hc
  · rw [min_eq_left (by linarith)] at hqmin
    have h1 := weighted_contract s w z Z q hw hw1 hz0 hz1 hmean hq hq0 hZ0 hZ1
    have hqq : (Φ * Z) ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ (by positivity) hqmin 2
    have h2 : Φ ^ 2 / 2 * ff Z ≤ q ^ 2 / (2 * Z * ff Z) := by
      rw [le_div_iff₀ (by positivity),
        show Φ ^ 2 / 2 * ff Z * (2 * Z * ff Z) = Φ ^ 2 * Z * ff Z ^ 2 from by ring, hffZ2]
      nlinarith [hqq, mul_nonneg (sq_nonneg (Φ * Z)) hZ0.le, hZ0.le, hZ1.le]
    linarith
  · rw [min_eq_right (by linarith)] at hqmin
    have h1 := weighted_contract' s w z Z q hw hw1 hz0 hz1 hmean hq hq0 hZ0 hZ1
    have hqq : (Φ * (1 - Z)) ^ 2 ≤ q ^ 2 :=
      pow_le_pow_left₀ (by positivity) hqmin 2
    have h2 : Φ ^ 2 / 2 * ff Z ≤ q ^ 2 / (2 * (1 - Z) * ff Z) := by
      rw [le_div_iff₀ (by positivity),
        show Φ ^ 2 / 2 * ff Z * (2 * (1 - Z) * ff Z) = Φ ^ 2 * (1 - Z) * ff Z ^ 2 from by ring,
        hffZ2]
      nlinarith [hqq, mul_nonneg (sq_nonneg (Φ * (1 - Z))) (by linarith : (0:ℝ) ≤ 1 - Z),
        hZ0.le, hZ1.le]
    linarith

end Contraction

/-! ### The one-step contraction for the evolving-set chain -/

section OneStep

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {P : Matrix V V ℝ} {π : V → ℝ}

private lemma weighted_degenerate {ι : Type*} (s : Finset ι) (w z : ι → ℝ) (Z : ℝ)
    (hw : ∀ i ∈ s, 0 < w i) (hz0 : ∀ i ∈ s, 0 ≤ z i) (hz1 : ∀ i ∈ s, z i ≤ 1)
    (hw1 : ∑ i ∈ s, w i = 1) (hmean : ∑ i ∈ s, w i * z i = Z)
    (hZ : Z = 0 ∨ Z = 1) : ∑ i ∈ s, w i * ff (z i) = 0 := by
  refine Finset.sum_eq_zero fun i hi => ?_
  rcases hZ with h | h
  · have hz : z i = 0 := by
      have hsum : ∑ j ∈ s, w j * z j = 0 := by rw [hmean, h]
      have := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j hj => mul_nonneg (hw j hj).le (hz0 j hj))).mp hsum i hi
      rcases mul_eq_zero.mp this with h1 | h1
      · exact absurd h1 (ne_of_gt (hw i hi))
      · exact h1
    rw [hz, ff]
    norm_num
  · have hz : z i = 1 := by
      have hsum : ∑ j ∈ s, w j * (1 - z j) = 0 := by
        have : ∀ j ∈ s, w j * (1 - z j) = w j - w j * z j := fun j _ => by ring
        rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, hw1, hmean, h, sub_self]
      have := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j hj => mul_nonneg (hw j hj).le (by linarith [hz1 j hj]))).mp hsum i hi
      rcases mul_eq_zero.mp this with h1 | h1
      · exact absurd h1 (ne_of_gt (hw i hi))
      · linarith
    rw [hz, ff]
    norm_num

private lemma piS_nonneg (hpos : ∀ x, 0 < π x) (T : Finset V) : 0 ≤ piS π T :=
  Finset.sum_nonneg fun y _ => (hpos y).le

private lemma piS_le_one (hπ : IsStationary P π) (hpos : ∀ x, 0 < π x) (T : Finset V) :
    piS π T ≤ 1 := by
  rw [piS, ← hπ.1.2]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
    (fun y _ _ => (hpos y).le)

private lemma qflow_nonneg (hP : IsStochastic P) (hpos : ∀ x, 0 < π x) (S : Finset V) :
    0 ≤ qflow P π S :=
  Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => mul_nonneg (hpos x).le (hP.1 x y)

private lemma es_one_step (hP : IsStochastic P) (hπ : IsStationary P π)
    (hpos : ∀ x, 0 < π x) (hlazy : ∀ x : V, 2⁻¹ ≤ P x x) (Φ : ℝ) (hΦ0 : 0 ≤ Φ)
    (hbn : ∀ S : Finset V, 0 < piS π S → piS π S < 1 →
      Φ * min (piS π S) (1 - piS π S) ≤ qflow P π S)
    (S : Finset V) :
    ∑ T : Finset V, evolvingSets P π S T * ff (piS π T)
      ≤ (1 - Φ ^ 2 / 2) * ff (piS π S) := by
  classical
  set w : Finset V → ℝ := fun T => evolvingSets P π S T with hwdef
  set z : Finset V → ℝ := fun T => piS π T with hzdef
  have hwnn : ∀ T : Finset V, 0 ≤ w T := fun T => le_max_left _ _
  set s : Finset (Finset V) := Finset.univ.filter (fun T : Finset V => 0 < w T) with hsdef
  have hrestrict : ∀ g : Finset V → ℝ, ∑ T ∈ s, w T * g T = ∑ T : Finset V, w T * g T := by
    intro g
    refine Finset.sum_subset (Finset.subset_univ s) fun T _ hT => ?_
    have : w T = 0 := le_antisymm (by simpa [hsdef] using hT) (hwnn T)
    rw [this, zero_mul]
  have hw : ∀ T ∈ s, 0 < w T := fun T hT => (Finset.mem_filter.mp hT).2
  have hz0 : ∀ T ∈ s, 0 ≤ z T := fun T _ => piS_nonneg hpos T
  have hz1 : ∀ T ∈ s, z T ≤ 1 := fun T _ => piS_le_one hπ hpos T
  have hw1 : ∑ T ∈ s, w T = 1 := by
    have h := hrestrict (fun _ => (1:ℝ))
    simp only [mul_one] at h
    rw [h]
    exact es_sum_one P π S
  have hmean : ∑ T ∈ s, w T * z T = piS π S := by
    rw [hrestrict]
    exact es_mean hP hπ hpos S
  have hq : 2 * qflow P π S ≤ ∑ T ∈ s, w T * |z T - piS π S| := by
    rw [hrestrict]
    exact le_of_eq (es_l1 hP hπ hpos hlazy S).symm
  have hZ0' : 0 ≤ piS π S := piS_nonneg hpos S
  have hZ1' : piS π S ≤ 1 := piS_le_one hπ hpos S
  rw [← hrestrict (fun T => ff (z T))]
  rcases eq_or_lt_of_le hZ0' with h0 | h0
  · rw [weighted_degenerate s w z (piS π S) hw hz0 hz1 hw1 hmean (Or.inl h0.symm), ← h0]
    rw [ff]
    norm_num
  · rcases eq_or_lt_of_le hZ1' with h1 | h1
    · rw [weighted_degenerate s w z (piS π S) hw hz0 hz1 hw1 hmean (Or.inr h1), h1, ff]
      norm_num
    · exact weighted_final s w z (piS π S) (qflow P π S) Φ hw hw1 hz0 hz1 hmean hq
        (qflow_nonneg hP hpos S) h0 h1 hΦ0 (hbn S h0 h1)

end OneStep

/-! ### Iterating the contraction -/

section Iterate

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {P : Matrix V V ℝ} {π : V → ℝ}

private lemma es_pow_nonneg (P : Matrix V V ℝ) (π : V → ℝ) :
    ∀ (t : ℕ) (A B : Finset V), 0 ≤ ((evolvingSets P π) ^ t) A B := by
  intro t
  induction t with
  | zero => intro A B; rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ t ih =>
      intro A B
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun C _ => mul_nonneg (ih A C) (le_max_left _ _)

private lemma es_pow_sum (hP : IsStochastic P) (hπ : IsStationary P π)
    (hpos : ∀ x, 0 < π x) :
    ∀ (t : ℕ) (A : Finset V), ∑ B : Finset V, ((evolvingSets P π) ^ t) A B = 1 := by
  intro t
  induction t with
  | zero => intro A; simp [Matrix.one_apply]
  | succ t ih =>
      intro A
      rw [Finset.sum_congr rfl fun B _ => by rw [pow_succ, Matrix.mul_apply], Finset.sum_comm]
      rw [Finset.sum_congr rfl fun C _ =>
        (Finset.mul_sum Finset.univ (fun B => evolvingSets P π C B)
          (((evolvingSets P π) ^ t) A C)).symm]
      rw [Finset.sum_congr rfl fun C _ => by rw [es_sum_one P π C, mul_one]]
      exact ih A

private lemma es_pow_mean (hP : IsStochastic P) (hπ : IsStationary P π)
    (hpos : ∀ x, 0 < π x) :
    ∀ (t : ℕ) (A : Finset V),
      ∑ B : Finset V, ((evolvingSets P π) ^ t) A B * piS π B = piS π A := by
  intro t
  induction t with
  | zero => intro A; simp [Matrix.one_apply, Finset.sum_ite_eq]
  | succ t ih =>
      intro A
      rw [Finset.sum_congr rfl fun B _ => by
        rw [pow_succ, Matrix.mul_apply, Finset.sum_mul], Finset.sum_comm]
      rw [Finset.sum_congr rfl fun C (_ : C ∈ Finset.univ) => by
        rw [Finset.sum_congr rfl fun B (_ : B ∈ Finset.univ) => mul_assoc _ _ _,
          ← Finset.mul_sum, es_mean hP hπ hpos C]]
      exact ih A

private lemma es_decay (hP : IsStochastic P) (hπ : IsStationary P π)
    (hpos : ∀ x, 0 < π x) (hlazy : ∀ x : V, 2⁻¹ ≤ P x x) (Φ : ℝ) (hΦ0 : 0 ≤ Φ) (hΦ1 : Φ ≤ 1)
    (hbn : ∀ S : Finset V, 0 < piS π S → piS π S < 1 →
      Φ * min (piS π S) (1 - piS π S) ≤ qflow P π S) :
    ∀ (t : ℕ) (A : Finset V),
      ∑ B : Finset V, ((evolvingSets P π) ^ t) A B * ff (piS π B)
        ≤ (1 - Φ ^ 2 / 2) ^ t * ff (piS π A) := by
  have hρ : (0:ℝ) ≤ 1 - Φ ^ 2 / 2 := by nlinarith
  intro t
  induction t with
  | zero => intro A; simp [Matrix.one_apply, Finset.sum_ite_eq]
  | succ t ih =>
      intro A
      have hstep : ∑ B : Finset V, ((evolvingSets P π) ^ (t + 1)) A B * ff (piS π B)
          = ∑ C : Finset V, ((evolvingSets P π) ^ t) A C *
              (∑ B : Finset V, evolvingSets P π C B * ff (piS π B)) := by
        rw [Finset.sum_congr rfl fun B _ => by
          rw [pow_succ, Matrix.mul_apply, Finset.sum_mul], Finset.sum_comm]
        refine Finset.sum_congr rfl fun C _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun B _ => by ring
      rw [hstep]
      have h1 : ∑ C : Finset V, ((evolvingSets P π) ^ t) A C *
            (∑ B : Finset V, evolvingSets P π C B * ff (piS π B))
          ≤ ∑ C : Finset V, ((evolvingSets P π) ^ t) A C * ((1 - Φ ^ 2 / 2) * ff (piS π C)) :=
        Finset.sum_le_sum fun C _ =>
          mul_le_mul_of_nonneg_left (es_one_step hP hπ hpos hlazy Φ hΦ0 hbn C)
            (es_pow_nonneg P π t A C)
      refine le_trans h1 ?_
      have h2 : ∑ C : Finset V, ((evolvingSets P π) ^ t) A C * ((1 - Φ ^ 2 / 2) * ff (piS π C))
          = (1 - Φ ^ 2 / 2) * ∑ C : Finset V, ((evolvingSets P π) ^ t) A C * ff (piS π C) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun C _ => by ring
      rw [h2, pow_succ]
      calc (1 - Φ ^ 2 / 2) * ∑ C : Finset V, ((evolvingSets P π) ^ t) A C * ff (piS π C)
          ≤ (1 - Φ ^ 2 / 2) * ((1 - Φ ^ 2 / 2) ^ t * ff (piS π A)) :=
            mul_le_mul_of_nonneg_left (ih A) hρ
        _ = (1 - Φ ^ 2 / 2) ^ t * (1 - Φ ^ 2 / 2) * ff (piS π A) := by ring

end Iterate

/-! ### From the evolving-set decay to total variation -/

section Assembly

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable {P : Matrix V V ℝ} {π : V → ℝ}

private lemma P_pow_nonneg (hP : IsStochastic P) :
    ∀ (t : ℕ) (x y : V), 0 ≤ (P ^ t) x y := by
  intro t
  induction t with
  | zero => intro x y; rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ t ih =>
      intro x y
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun z _ => mul_nonneg (ih x z) (hP.1 z y)

private lemma P_pow_sum (hP : IsStochastic P) :
    ∀ (t : ℕ) (x : V), ∑ y, (P ^ t) x y = 1 := by
  intro t
  induction t with
  | zero => intro x; simp [Matrix.one_apply]
  | succ t ih =>
      intro x
      rw [Finset.sum_congr rfl fun y _ => by rw [pow_succ, Matrix.mul_apply], Finset.sum_comm]
      rw [Finset.sum_congr rfl fun z _ =>
        (Finset.mul_sum Finset.univ (fun y => P z y) ((P ^ t) x z)).symm]
      rw [Finset.sum_congr rfl fun z _ => by rw [hP.2 z, mul_one]]
      exact ih x

private lemma row_isDist (hP : IsStochastic P) (t : ℕ) (x : V) :
    IsDist (rowDist P t x) := ⟨fun y => P_pow_nonneg hP t x y, P_pow_sum hP t x⟩

private lemma pi_compl (hπ : IsStationary P π) (T : Finset V) :
    ∑ y ∈ Tᶜ, π y = 1 - piS π T := by
  have h := Finset.sum_add_sum_compl T π
  rw [hπ.1.2] at h
  rw [piS]
  linarith

private lemma sum_abs_ind (hπ : IsStationary P π) (hpos : ∀ x, 0 < π x) (T : Finset V) :
    ∑ y : V, π y * |(if y ∈ T then (1:ℝ) else 0) - piS π T|
      = 2 * (piS π T * (1 - piS π T)) := by
  have hz0 : 0 ≤ piS π T := piS_nonneg hpos T
  have hz1 : piS π T ≤ 1 := piS_le_one hπ hpos T
  rw [← Finset.sum_add_sum_compl T
    (fun y => π y * |(if y ∈ T then (1:ℝ) else 0) - piS π T|)]
  have h1 : ∑ y ∈ T, π y * |(if y ∈ T then (1:ℝ) else 0) - piS π T|
      = piS π T * (1 - piS π T) := by
    rw [Finset.sum_congr rfl (fun y hy => by
      rw [if_pos hy, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - piS π T)] :
      ∀ y ∈ T, π y * |(if y ∈ T then (1:ℝ) else 0) - piS π T| = π y * (1 - piS π T))]
    rw [← Finset.sum_mul, ← piS]
  have h2 : ∑ y ∈ Tᶜ, π y * |(if y ∈ T then (1:ℝ) else 0) - piS π T|
      = (1 - piS π T) * piS π T := by
    rw [Finset.sum_congr rfl (fun y hy => by
      rw [if_neg (Finset.mem_compl.mp hy), zero_sub, abs_neg, abs_of_nonneg hz0] :
      ∀ y ∈ Tᶜ, π y * |(if y ∈ T then (1:ℝ) else 0) - piS π T| = π y * piS π T)]
    rw [← Finset.sum_mul, pi_compl hπ T]
  rw [h1, h2]
  ring

private lemma tv_bound (hP : IsStochastic P) (hπ : IsStationary P π)
    (hpos : ∀ x, 0 < π x) (hlazy : ∀ x : V, 2⁻¹ ≤ P x x) (Φ : ℝ) (hΦ0 : 0 ≤ Φ) (hΦ1 : Φ ≤ 1)
    (hbn : ∀ S : Finset V, 0 < piS π S → piS π S < 1 →
      Φ * min (piS π S) (1 - piS π S) ≤ qflow P π S)
    (x : V) (t : ℕ) :
    tvDist (rowDist P t x) π ≤ (1 - Φ ^ 2 / 2) ^ t / (2 * Real.sqrt (π x)) := by
  classical
  have hpx := hpos x
  have hsq : 0 < Real.sqrt (π x) := Real.sqrt_pos.mpr hpx
  set mt : V → ℝ := fun y =>
    ∑ T ∈ Finset.univ.filter (fun T : Finset V => y ∈ T), ((evolvingSets P π) ^ t) {x} T
    with hmtdef
  have hid : ∀ y : V, (P ^ t) x y = π y / π x * mt y := fun y =>
    evolving_sets_identity P hP π hπ hpos x y t
  have hmean : ∑ T : Finset V, ((evolvingSets P π) ^ t) {x} T * piS π T = π x := by
    rw [es_pow_mean hP hπ hpos t {x}, piS, Finset.sum_singleton]
  have hmt : ∀ y : V, mt y
      = ∑ T : Finset V, ((evolvingSets P π) ^ t) {x} T * (if y ∈ T then (1:ℝ) else 0) := by
    intro y
    rw [hmtdef]
    simp only [Finset.sum_filter, mul_ite, mul_one, mul_zero]
  have hkey : ∀ y : V, |mt y - π x|
      ≤ ∑ T : Finset V, ((evolvingSets P π) ^ t) {x} T
          * |(if y ∈ T then (1:ℝ) else 0) - piS π T| := by
    intro y
    have hd : mt y - π x
        = ∑ T : Finset V, ((evolvingSets P π) ^ t) {x} T
            * ((if y ∈ T then (1:ℝ) else 0) - piS π T) := by
      rw [hmt y, ← hmean, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun T _ => by ring
    rw [hd]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq (Finset.sum_congr rfl fun T _ => ?_))
    rw [abs_mul, abs_of_nonneg (es_pow_nonneg P π t {x} T)]
  -- the ℓ¹ estimate
  have hL : ∑ y : V, |(P ^ t) x y - π y|
      ≤ (1 / π x) * ∑ T : Finset V, ((evolvingSets P π) ^ t) {x} T * ff (piS π T) := by
    have hstep1 : ∀ y : V, |(P ^ t) x y - π y| = (π y / π x) * |mt y - π x| := by
      intro y
      rw [hid y, show π y / π x * mt y - π y = (π y / π x) * (mt y - π x) from by
        field_simp, abs_mul,
        abs_of_nonneg (div_nonneg (hpos y).le (hpos x).le)]
    rw [Finset.sum_congr rfl (fun y (_ : y ∈ Finset.univ) => hstep1 y)]
    have hstep2 : ∑ y : V, (π y / π x) * |mt y - π x|
        ≤ ∑ y : V, (π y / π x) * ∑ T : Finset V, ((evolvingSets P π) ^ t) {x} T
            * |(if y ∈ T then (1:ℝ) else 0) - piS π T| :=
      Finset.sum_le_sum fun y _ =>
        mul_le_mul_of_nonneg_left (hkey y) (div_nonneg (hpos y).le (hpos x).le)
    refine le_trans hstep2 ?_
    have hswap : ∑ y : V, (π y / π x) * ∑ T : Finset V, ((evolvingSets P π) ^ t) {x} T
          * |(if y ∈ T then (1:ℝ) else 0) - piS π T|
        = (1 / π x) * ∑ T : Finset V, ((evolvingSets P π) ^ t) {x} T
            * (∑ y : V, π y * |(if y ∈ T then (1:ℝ) else 0) - piS π T|) := by
      have hLL : ∑ y : V, (π y / π x) * ∑ T : Finset V, ((evolvingSets P π) ^ t) {x} T
            * |(if y ∈ T then (1:ℝ) else 0) - piS π T|
          = ∑ y : V, ∑ T : Finset V, (1 / π x) * (π y * (((evolvingSets P π) ^ t) {x} T
            * |(if y ∈ T then (1:ℝ) else 0) - piS π T|)) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun T _ => by field_simp
      have hRR : (1 / π x) * ∑ T : Finset V, ((evolvingSets P π) ^ t) {x} T
            * (∑ y : V, π y * |(if y ∈ T then (1:ℝ) else 0) - piS π T|)
          = ∑ T : Finset V, ∑ y : V, (1 / π x) * (π y * (((evolvingSets P π) ^ t) {x} T
            * |(if y ∈ T then (1:ℝ) else 0) - piS π T|)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun T _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => by ring
      rw [hLL, hRR, Finset.sum_comm]
    rw [hswap]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine Finset.sum_le_sum fun T _ => ?_
    rw [sum_abs_ind hπ hpos T]
    have hz0 : 0 ≤ piS π T := piS_nonneg hpos T
    have hz1 : piS π T ≤ 1 := piS_le_one hπ hpos T
    have hfs : ff (piS π T) ^ 2 = piS π T * (1 - piS π T) := ff_sq hz0 hz1
    have hfh : ff (piS π T) ≤ 2⁻¹ := ff_le_half hz0 hz1
    have hfn : 0 ≤ ff (piS π T) := ff_nonneg _
    refine mul_le_mul_of_nonneg_left ?_ (es_pow_nonneg P π t {x} T)
    nlinarith [hfs, hfh, hfn]
  -- combine with the decay
  have hdec := es_decay hP hπ hpos hlazy Φ hΦ0 hΦ1 hbn t {x}
  rw [show piS π ({x} : Finset V) = π x from by rw [piS, Finset.sum_singleton]] at hdec
  have hffx : ff (π x) ≤ Real.sqrt (π x) := by
    rw [ff]
    exact Real.sqrt_le_sqrt (by nlinarith [hpx, sq_nonneg (π x)])
  have hpxs : Real.sqrt (π x) * Real.sqrt (π x) = π x := Real.mul_self_sqrt hpx.le
  have hρ : (0:ℝ) ≤ (1 - Φ ^ 2 / 2) ^ t := by
    refine pow_nonneg ?_ t
    nlinarith
  have hdiv : ff (π x) / π x ≤ 1 / Real.sqrt (π x) := by
    rw [div_le_div_iff₀ hpx hsq, one_mul]
    calc ff (π x) * Real.sqrt (π x) ≤ Real.sqrt (π x) * Real.sqrt (π x) :=
          mul_le_mul_of_nonneg_right hffx (le_of_lt hsq)
      _ = π x := hpxs
  have hfinal : ∑ y : V, |(P ^ t) x y - π y| ≤ (1 - Φ ^ 2 / 2) ^ t / Real.sqrt (π x) := by
    have h1 : (1 / π x) * ∑ T : Finset V, ((evolvingSets P π) ^ t) {x} T * ff (piS π T)
        ≤ (1 / π x) * ((1 - Φ ^ 2 / 2) ^ t * ff (π x)) :=
      mul_le_mul_of_nonneg_left hdec (by positivity)
    have h2 : (1 / π x) * ((1 - Φ ^ 2 / 2) ^ t * ff (π x))
        ≤ (1 - Φ ^ 2 / 2) ^ t / Real.sqrt (π x) := by
      have he : (1 / π x) * ((1 - Φ ^ 2 / 2) ^ t * ff (π x))
          = (1 - Φ ^ 2 / 2) ^ t * (ff (π x) / π x) := by ring
      rw [he, div_eq_mul_one_div ((1 - Φ ^ 2 / 2) ^ t)]
      exact mul_le_mul_of_nonneg_left hdiv hρ
    linarith [hL, h1, h2]
  have htv := (tv_eq_half_l1 (rowDist P t x) π (row_isDist hP t x) hπ.1).1
  rw [htv]
  have hrw : ∑ y : V, |rowDist P t x y - π y| = ∑ y : V, |(P ^ t) x y - π y| := rfl
  rw [hrw]
  refine le_trans (mul_le_mul_of_nonneg_left hfinal (by norm_num : (0:ℝ) ≤ 2⁻¹)) (le_of_eq ?_)
  field_simp

end Assembly

/-! ### The bottleneck constant -/

section Bottleneck

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {P : Matrix V V ℝ} {π : V → ℝ}

private lemma bratio_eq (S : Finset V) :
    bottleneckRatio P π S = qflow P π S / piS π S := rfl

private lemma qflow_compl (hP : IsStochastic P) (hπ : IsStationary P π) (S : Finset V) :
    qflow P π Sᶜ = qflow P π S := by
  have h1 : ∑ x ∈ S, ∑ y ∈ S, π x * P x y + ∑ x ∈ S, ∑ y ∈ Sᶜ, π x * P x y = piS π S := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_add_sum_compl, ← Finset.mul_sum, hP.2 x, mul_one]
  have h2 : ∑ x ∈ S, ∑ y ∈ S, π x * P x y + ∑ x ∈ Sᶜ, ∑ y ∈ S, π x * P x y = piS π S := by
    rw [Finset.sum_comm (s := S) (t := S), Finset.sum_comm (s := Sᶜ) (t := S),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_add_sum_compl]
    exact sum_all_eq hπ y
  rw [qflow, qflow, compl_compl]
  linarith

private lemma closed_of_qflow_zero (hP : IsStochastic P) (hpos : ∀ x, 0 < π x)
    {S : Finset V} (h : qflow P π S = 0) :
    ∀ (t : ℕ) (x : V), x ∈ S → ∀ y : V, y ∉ S → (P ^ t) x y = 0 := by
  have hedge : ∀ x ∈ S, ∀ y ∈ Sᶜ, P x y = 0 := by
    intro x hx y hy
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun x _ => Finset.sum_nonneg fun y _ => mul_nonneg (hpos x).le (hP.1 x y))).mp h x hx
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun y _ => mul_nonneg (hpos x).le (hP.1 x y))).mp hz y hy
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 (ne_of_gt (hpos x))
    · exact h1
  intro t
  induction t with
  | zero =>
      intro x hx y hy
      rw [pow_zero, Matrix.one_apply, if_neg (fun hc : x = y => hy (by rw [← hc]; exact hx))]
  | succ t ih =>
      intro x hx y hy
      rw [pow_succ, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun z _ => ?_
      by_cases hz : z ∈ S
      · rw [hedge z hz y (Finset.mem_compl.mpr hy), mul_zero]
      · rw [ih x hx z hz, zero_mul]

private lemma qflow_pos (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P) (hpos : ∀ x, 0 < π x)
    {S : Finset V} (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) : 0 < qflow P π S := by
  rcases lt_or_eq_of_le (qflow_nonneg hP hpos S) with h | h
  · exact h
  · exfalso
    obtain ⟨x, hx⟩ := hS
    obtain ⟨y, hy⟩ := hSc
    obtain ⟨t, ht⟩ := hirr x y
    rw [closed_of_qflow_zero hP hpos h.symm t x hx y (Finset.mem_compl.mp hy)] at ht
    exact lt_irrefl 0 ht

end Bottleneck

end

end MarkovMixing

open scoped BigOperators
open MarkovMixing

namespace MarkovMixing

private lemma stationary_pos_direct {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (π : V → ℝ) (hπ : IsStationary P π) : ∀ x, 0 < π x := by
  classical
  have hex : ∃ a, 0 < π a := by
    by_contra h
    push_neg at h
    have hz : ∀ a, π a = 0 := fun a => le_antisymm (h a) (hπ.1.1 a)
    have hs := hπ.1.2
    simp only [hz, Finset.sum_const_zero] at hs
    norm_num at hs
  obtain ⟨a, ha⟩ := hex
  have hpownonneg : ∀ n : ℕ, ∀ x y, 0 ≤ (P ^ n) x y := by
    intro n
    induction n with
    | zero =>
        intro x y
        simp only [pow_zero, Matrix.one_apply]
        split_ifs <;> norm_num
    | succ n ih =>
        intro x y
        rw [pow_succ, Matrix.mul_apply]
        exact Finset.sum_nonneg fun z _ => mul_nonneg (ih x z) (hP.1 z y)
  have hstatpow : ∀ n : ℕ, Matrix.vecMul π (P ^ n) = π := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, hπ.2]
  intro x
  obtain ⟨n, hn⟩ := hirr a x
  have hterm : π a * (P ^ n) a x ≤ ∑ w, π w * (P ^ n) w x :=
    Finset.single_le_sum
      (fun w _ => mul_nonneg (hπ.1.1 w) (hpownonneg n w x)) (Finset.mem_univ a)
  have hvalue : (∑ w, π w * (P ^ n) w x) = π x := congrFun (hstatpow n) x
  rw [hvalue] at hterm
  exact lt_of_lt_of_le (mul_pos ha hn) hterm

end MarkovMixing

open MarkovMixing

theorem reused_tv_decay {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (hlazy : ∀ x : V, 2⁻¹ ≤ P x x)
    (π : V → ℝ) (hπ : IsStationary P π) :
    ∀ t : ℕ, distStationary P π t ≤
      1 / (⨅ x : V, π x) * (1 - bottleneckStar P π ^ 2 / 2) ^ t := by
  classical
  have hpos := MarkovMixing.stationary_pos_direct P hP hirr π hπ
  intro t
  by_cases hsub : ∀ x y : V, x = y
  · have hπone : ∀ y : V, π y = 1 := by
      intro y
      have huniv : (Finset.univ : Finset V) = {y} := by
        ext z
        simp [hsub z y]
      have hs := hπ.1.2
      rwa [huniv, Finset.sum_singleton] at hs
    have hrow : ∀ x : V, rowDist P t x = π := by
      intro x
      funext y
      have huniv : (Finset.univ : Finset V) = {y} := by
        ext z
        simp [hsub z y]
      have hs := MarkovMixing.P_pow_sum hP t x
      rw [huniv, Finset.sum_singleton] at hs
      exact hs.trans (hπone y).symm
    have hzero : bottleneckStar P π = 0 := by
      haveI : IsEmpty {S : Finset V // S.Nonempty ∧ ∑ x ∈ S, π x ≤ 2⁻¹} := ⟨by
        rintro ⟨S, hne, hhalf⟩
        obtain ⟨x, hx⟩ := hne
        have hS : S = {x} := by
          ext y
          simp only [Finset.mem_singleton]
          exact ⟨fun _ => hsub y x, fun hy => hy ▸ hx⟩
        rw [hS, Finset.sum_singleton, hπone] at hhalf
        norm_num at hhalf⟩
      simp [bottleneckStar]
    have hdist : distStationary P π t = 0 := by
      simp only [distStationary, hrow, tvDist, sub_self, abs_zero, ciSup_const]
    rw [hdist, hzero]
    simp only [zero_pow (by norm_num : 2 ≠ 0), zero_div, sub_zero, one_pow, mul_one]
    have hmin : (⨅ x : V, π x) = 1 := by simp only [hπone, ciInf_const]
    rw [hmin]
    norm_num
  ·
    push_neg at hsub
    obtain ⟨x₁, y₁, hxy₁⟩ := hsub
    -- the minimum of `π`
    have hmemr : sInf (Set.range π) ∈ Set.range π :=
      (Set.range_nonempty π).csInf_mem (Set.finite_range π)
    obtain ⟨x₀, hx₀⟩ := hmemr
    have hinf_eq : (⨅ x : V, π x) = π x₀ := hx₀.symm
    have hbddπ : BddBelow (Set.range π) := ⟨0, by rintro r ⟨x, rfl⟩; exact (hpos x).le⟩
    have hmin_le : ∀ x : V, (⨅ x : V, π x) ≤ π x := fun x => ciInf_le hbddπ x
    have hminpos : 0 < (⨅ x : V, π x) := by rw [hinf_eq]; exact hpos x₀
    have hminle1 : (⨅ x : V, π x) ≤ 1 := le_trans (hmin_le x₀) (by
      rw [← hπ.1.2]
      exact Finset.single_le_sum (fun y _ => (hpos y).le) (Finset.mem_univ x₀))
    -- the admissible index type is nonempty
    have hpair : (⨅ x : V, π x) ≤ 2⁻¹ := by
      have h2 : π x₁ + π y₁ ≤ 1 := by
        rw [← hπ.1.2, ← Finset.sum_pair hxy₁]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun z _ _ => (hpos z).le)
      have := hmin_le x₁
      have := hmin_le y₁
      linarith
    have hS0 : ({x₀} : Finset V).Nonempty := ⟨x₀, Finset.mem_singleton_self x₀⟩
    have hpiS0 : ∑ x ∈ ({x₀} : Finset V), π x ≤ 2⁻¹ := by
      rw [Finset.sum_singleton, ← hinf_eq]
      exact hpair
    have hIne : Nonempty {S : Finset V // S.Nonempty ∧ ∑ x ∈ S, π x ≤ 2⁻¹} :=
      ⟨⟨{x₀}, hS0, hpiS0⟩⟩
    -- basic facts about the bottleneck constant
    have hbdd : BddBelow (Set.range fun S : {S : Finset V // S.Nonempty ∧ ∑ x ∈ S, π x ≤ 2⁻¹} =>
        bottleneckRatio P π S.1) := by
      refine ⟨0, ?_⟩
      rintro r ⟨S, rfl⟩
      exact div_nonneg (qflow_nonneg hP hpos S.1) (piS_nonneg hpos S.1)
    have hattain : bottleneckStar P π ∈ Set.range
        (fun S : {S : Finset V // S.Nonempty ∧ ∑ x ∈ S, π x ≤ 2⁻¹} =>
          bottleneckRatio P π S.1) :=
      (Set.range_nonempty _).csInf_mem (Set.finite_range _)
    obtain ⟨S₀, hS₀⟩ := hattain
    have hpiSlt : piS π S₀.1 < 1 := by
      have := S₀.2.2
      rw [piS]
      linarith
    have hS₀c : (S₀.1ᶜ : Finset V).Nonempty := by
      rw [← Finset.card_pos]
      by_contra hc
      have : S₀.1ᶜ = ∅ := Finset.card_eq_zero.mp (by omega)
      have huniv : S₀.1 = Finset.univ := by
        rw [← compl_compl S₀.1, this, Finset.compl_empty]
      rw [huniv] at hpiSlt
      rw [piS, hπ.1.2] at hpiSlt
      exact lt_irrefl 1 hpiSlt
    have hpiS0pos : 0 < piS π S₀.1 := Finset.sum_pos (fun x _ => hpos x) S₀.2.1
    have hS₀' : bottleneckStar P π = bottleneckRatio P π S₀.1 := hS₀.symm
    have hΦpos : 0 < bottleneckStar P π := by
      rw [hS₀', bratio_eq]
      exact div_pos (qflow_pos hP hirr hpos S₀.2.1 hS₀c) hpiS0pos
    have hqle : ∀ S : Finset V, qflow P π S ≤ piS π S := by
      intro S
      rw [qflow, piS]
      refine Finset.sum_le_sum fun x _ => ?_
      calc ∑ y ∈ Sᶜ, π x * P x y ≤ ∑ y : V, π x * P x y :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Sᶜ)
              (fun y _ _ => mul_nonneg (hpos x).le (hP.1 x y))
        _ = π x := by rw [← Finset.mul_sum, hP.2 x, mul_one]
    have hΦle : bottleneckStar P π ≤ 1 := by
      rw [hS₀', bratio_eq, div_le_one hpiS0pos]
      exact hqle S₀.1
    -- the bottleneck bound for an arbitrary set
    have hbn : ∀ S : Finset V, 0 < piS π S → piS π S < 1 →
        bottleneckStar P π * min (piS π S) (1 - piS π S) ≤ qflow P π S := by
      intro S h0 h1
      rcases le_or_gt (piS π S) 2⁻¹ with hc | hc
      · rw [min_eq_left (by linarith)]
        have hSne : S.Nonempty := by
          rw [← Finset.card_pos]
          by_contra hcc
          have : S = ∅ := Finset.card_eq_zero.mp (by omega)
          rw [this, piS, Finset.sum_empty] at h0
          exact lt_irrefl 0 h0
        have hle : bottleneckStar P π ≤ bottleneckRatio P π S :=
          ciInf_le hbdd ⟨S, hSne, hc⟩
        rw [bratio_eq, le_div_iff₀ h0] at hle
        exact hle
      · rw [min_eq_right (by linarith)]
        have hcpi : piS π Sᶜ = 1 - piS π S := by rw [piS]; exact pi_compl hπ S
        have hSne : (Sᶜ : Finset V).Nonempty := by
          rw [← Finset.card_pos]
          by_contra hcc
          have hce : Sᶜ = ∅ := Finset.card_eq_zero.mp (by omega)
          rw [hce, piS, Finset.sum_empty] at hcpi
          linarith
        have hle : bottleneckStar P π ≤ bottleneckRatio P π Sᶜ :=
          ciInf_le hbdd ⟨Sᶜ, hSne, by rw [show ∑ x ∈ Sᶜ, π x = piS π Sᶜ from rfl, hcpi]; linarith⟩
        rw [bratio_eq, hcpi, le_div_iff₀ (by linarith), qflow_compl hP hπ] at hle
        exact hle
    have hρ : 0 ≤ (1 - bottleneckStar P π ^ 2 / 2) ^ t := by
      apply pow_nonneg
      nlinarith [hΦpos, hΦle]
    rw [distStationary]
    refine ciSup_le fun x => ?_
    have htv := MarkovMixing.tv_bound hP hπ hpos hlazy (bottleneckStar P π)
      hΦpos.le hΦle hbn x t
    have hs : 0 < Real.sqrt (π x) := Real.sqrt_pos.mpr (hpos x)
    have hx1 : π x ≤ 1 := by
      rw [← hπ.1.2]
      exact Finset.single_le_sum (fun y _ => (hpos y).le) (Finset.mem_univ x)
    have hs1 : Real.sqrt (π x) ≤ 1 := by
      simpa using Real.sqrt_le_sqrt hx1
    have hsq : Real.sqrt (π x) ^ 2 = π x := Real.sq_sqrt (hpos x).le
    have hden : (⨅ y : V, π y) ≤ 2 * Real.sqrt (π x) := by
      have hm := hmin_le x
      nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hs1)]
    calc
      tvDist (rowDist P t x) π ≤
          (1 - bottleneckStar P π ^ 2 / 2) ^ t / (2 * Real.sqrt (π x)) := htv
      _ ≤ (1 - bottleneckStar P π ^ 2 / 2) ^ t / (⨅ y : V, π y) :=
        div_le_div_of_nonneg_left hρ hminpos hden
      _ = 1 / (⨅ y : V, π y) * (1 - bottleneckStar P π ^ 2 / 2) ^ t := by ring

#print axioms reused_tv_decay


set_option autoImplicit false

namespace RootMinProof

private lemma sqrt_deficit {z Z : ℝ} (hz : 0 ≤ z) (hZ : 0 < Z) :
    Real.sqrt z * Real.sqrt Z ≤ (z + Z) / 2 - (z - Z) ^ 2 / (4 * (z + Z)) := by
  have ha := Real.sq_sqrt hz
  have hb := Real.sq_sqrt hZ.le
  have hden : 0 < z + Z := by linarith
  have hsum : (Real.sqrt z + Real.sqrt Z) ^ 2 ≤ 2 * (z + Z) := by
    nlinarith [sq_nonneg (Real.sqrt z - Real.sqrt Z)]
  have hfactor : (z - Z) ^ 2 =
      (Real.sqrt z - Real.sqrt Z) ^ 2 * (Real.sqrt z + Real.sqrt Z) ^ 2 := by
    calc (z - Z) ^ 2 = (Real.sqrt z ^ 2 - Real.sqrt Z ^ 2) ^ 2 := by rw [ha, hb]
      _ = _ := by ring
  have hbound : (z - Z) ^ 2 ≤ (Real.sqrt z - Real.sqrt Z) ^ 2 * (2 * (z + Z)) := by
    rw [hfactor]
    exact mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
  have hdiv : (z - Z) ^ 2 / (4 * (z + Z)) ≤
      (Real.sqrt z - Real.sqrt Z) ^ 2 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  nlinarith

lemma weighted_sqrt_contract {ι : Type*} (s : Finset ι) (w z : ι → ℝ)
    (Z q : ℝ) (hw : ∀ i ∈ s, 0 < w i) (hw1 : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 ≤ z i) (hmean : ∑ i ∈ s, w i * z i = Z)
    (hq : 2 * q ≤ ∑ i ∈ s, w i * |z i - Z|) (hq0 : 0 ≤ q) (hZ : 0 < Z) :
    ∑ i ∈ s, w i * Real.sqrt (z i) ≤ Real.sqrt Z - q ^ 2 / (2 * Z * Real.sqrt Z) := by
  have hs : 0 < Real.sqrt Z := Real.sqrt_pos.mpr hZ
  have hs2 : Real.sqrt Z ^ 2 = Z := Real.sq_sqrt hZ.le
  have hgpos : ∀ i ∈ s, 0 < w i * (z i + Z) := fun i hi =>
    mul_pos (hw i hi) (by linarith [hz i hi])
  have hden : ∑ i ∈ s, w i * (z i + Z) = 2 * Z := by
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, hmean, ← Finset.sum_mul, hw1]
    ring
  have hCS := Finset.sq_sum_div_le_sum_sq_div s (fun i => w i * |z i - Z|)
    (g := fun i => w i * (z i + Z)) hgpos
  rw [hden] at hCS
  have hterm : ∀ i ∈ s, (w i * |z i - Z|) ^ 2 / (w i * (z i + Z)) =
      w i * ((z i - Z) ^ 2 / (z i + Z)) := by
    intro i hi
    have hwi := ne_of_gt (hw i hi)
    have hzi : z i + Z ≠ 0 := ne_of_gt (by linarith [hz i hi])
    rw [mul_pow, sq_abs]
    field_simp
  rw [Finset.sum_congr rfl hterm] at hCS
  have hqsum : 0 ≤ ∑ i ∈ s, w i * |z i - Z| :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi).le (abs_nonneg _)
  have hSig : 2 * q ^ 2 / Z ≤ ∑ i ∈ s, w i * ((z i - Z) ^ 2 / (z i + Z)) := by
    refine le_trans ?_ hCS
    have h4 : (2 * q) ^ 2 ≤ (∑ i ∈ s, w i * |z i - Z|) ^ 2 :=
      pow_le_pow_left₀ (by linarith) hq 2
    rw [div_le_div_iff₀ hZ (by linarith)]
    nlinarith
  have hmain : (∑ i ∈ s, w i * Real.sqrt (z i)) * Real.sqrt Z ≤
      Z - (∑ i ∈ s, w i * ((z i - Z) ^ 2 / (z i + Z))) / 4 := by
    have hstep : ∀ i ∈ s, w i * Real.sqrt (z i) * Real.sqrt Z ≤
        w i * ((z i + Z) / 2 - (z i - Z) ^ 2 / (4 * (z i + Z))) := by
      intro i hi
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left (sqrt_deficit (hz i hi) hZ) (hw i hi).le
    rw [Finset.sum_mul]
    refine le_trans (Finset.sum_le_sum hstep) (le_of_eq ?_)
    have hexp : ∀ i ∈ s, w i * ((z i + Z) / 2 - (z i - Z) ^ 2 / (4 * (z i + Z))) =
        w i * (z i + Z) / 2 - (w i * ((z i - Z) ^ 2 / (z i + Z))) / 4 := by
      intro i hi
      field_simp
    rw [Finset.sum_congr rfl hexp, Finset.sum_sub_distrib, ← Finset.sum_div,
      ← Finset.sum_div, hden]
    ring
  have hfinal : (∑ i ∈ s, w i * Real.sqrt (z i)) * Real.sqrt Z ≤
      Z - q ^ 2 / (2 * Z) := by
    have hSig' : 2 * q ^ 2 ≤ (∑ i ∈ s, w i * ((z i - Z) ^ 2 / (z i + Z))) * Z :=
      (div_le_iff₀ hZ).mp hSig
    have hquarter : q ^ 2 / (2 * Z) ≤
        (∑ i ∈ s, w i * ((z i - Z) ^ 2 / (z i + Z))) / 4 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    linarith
  have hrw : Real.sqrt Z - q ^ 2 / (2 * Z * Real.sqrt Z) =
      (Z - q ^ 2 / (2 * Z)) / Real.sqrt Z := by
    field_simp
    nlinarith [hs2]
  rw [hrw, le_div_iff₀ hs]
  exact hfinal

lemma weighted_root_min_contract {ι : Type*} (s : Finset ι) (w z : ι → ℝ)
    (Z q Φ : ℝ) (hw : ∀ i ∈ s, 0 < w i) (hw1 : ∑ i ∈ s, w i = 1)
    (hz0 : ∀ i ∈ s, 0 ≤ z i) (hz1 : ∀ i ∈ s, z i ≤ 1)
    (hmean : ∑ i ∈ s, w i * z i = Z)
    (hq : 2 * q ≤ ∑ i ∈ s, w i * |z i - Z|) (hq0 : 0 ≤ q)
    (hZ0 : 0 < Z) (hZ1 : Z < 1) (hΦ0 : 0 ≤ Φ)
    (hqmin : Φ * min Z (1 - Z) ≤ q) :
    ∑ i ∈ s, w i * Real.sqrt (min (z i) (1 - z i)) ≤
      (1 - Φ ^ 2 / 2) * Real.sqrt (min Z (1 - Z)) := by
  have hsmall (Z' : ℝ) (z' : ι → ℝ) (hz' : ∀ i ∈ s, 0 ≤ z' i)
      (hm' : ∑ i ∈ s, w i * z' i = Z') (hq' : 2 * q ≤ ∑ i ∈ s, w i * |z' i - Z'|)
      (hZ' : 0 < Z') (hPhi : Φ * Z' ≤ q) :
      ∑ i ∈ s, w i * Real.sqrt (z' i) ≤ (1 - Φ ^ 2 / 2) * Real.sqrt Z' := by
    have h := weighted_sqrt_contract s w z' Z' q hw hw1 hz' hm' hq' hq0 hZ'
    have hs : 0 < Real.sqrt Z' := Real.sqrt_pos.mpr hZ'
    have hs2 := Real.sq_sqrt hZ'.le
    have hqq := pow_le_pow_left₀ (mul_nonneg hΦ0 hZ'.le) hPhi 2
    have hloss : Φ ^ 2 / 2 * Real.sqrt Z' ≤ q ^ 2 / (2 * Z' * Real.sqrt Z') := by
      rw [le_div_iff₀ (by positivity)]
      calc Φ ^ 2 / 2 * Real.sqrt Z' * (2 * Z' * Real.sqrt Z') =
          Φ ^ 2 * Z' * Real.sqrt Z' ^ 2 := by ring
        _ = (Φ * Z') ^ 2 := by rw [hs2]; ring
        _ ≤ q ^ 2 := hqq
    linarith
  rcases le_or_gt Z (1 - Z) with hc | hc
  · rw [min_eq_left hc] at hqmin ⊢
    refine le_trans (Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (min_le_left _ _)) (hw i hi).le) ?_
    exact hsmall Z z hz0 hmean hq hZ0 hqmin
  · rw [min_eq_right hc.le] at hqmin ⊢
    have hm' : ∑ i ∈ s, w i * (1 - z i) = 1 - Z := by
      simp_rw [mul_sub, mul_one]
      rw [Finset.sum_sub_distrib, hw1, hmean]
    have hq' : 2 * q ≤ ∑ i ∈ s, w i * |(1 - z i) - (1 - Z)| := by
      simpa only [show ∀ i, (1 - z i) - (1 - Z) = -(z i - Z) from fun i => by ring,
        abs_neg] using hq
    refine le_trans (Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (min_le_right _ _)) (hw i hi).le) ?_
    exact hsmall (1 - Z) (fun i => 1 - z i) (fun i hi => by linarith [hz1 i hi])
      hm' hq' (by linarith) hqmin

end RootMinProof

#print axioms RootMinProof.weighted_root_min_contract


namespace MarkovMixing

private lemma root_min_degenerate {ι : Type*} (s : Finset ι) (w z : ι → ℝ) (Z : ℝ)
    (hw : ∀ i ∈ s, 0 < w i) (hz0 : ∀ i ∈ s, 0 ≤ z i) (hz1 : ∀ i ∈ s, z i ≤ 1)
    (hw1 : ∑ i ∈ s, w i = 1) (hmean : ∑ i ∈ s, w i * z i = Z)
    (hZ : Z = 0 ∨ Z = 1) :
    ∑ i ∈ s, w i * Real.sqrt (min (z i) (1 - z i)) = 0 := by
  refine Finset.sum_eq_zero fun i hi => ?_
  rcases hZ with h | h
  · have hz : z i = 0 := by
      have hsum : ∑ j ∈ s, w j * z j = 0 := by rw [hmean, h]
      have := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j hj => mul_nonneg (hw j hj).le (hz0 j hj))).mp hsum i hi
      exact (mul_eq_zero.mp this).resolve_left (ne_of_gt (hw i hi))
    rw [hz]
    norm_num
  · have hz : z i = 1 := by
      have hsum : ∑ j ∈ s, w j * (1 - z j) = 0 := by
        simp_rw [mul_sub, mul_one]
        rw [Finset.sum_sub_distrib, hw1, hmean, h, sub_self]
      have := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j hj => mul_nonneg (hw j hj).le (by linarith [hz1 j hj]))).mp hsum i hi
      have := (mul_eq_zero.mp this).resolve_left (ne_of_gt (hw i hi))
      linarith
    rw [hz]
    norm_num

private lemma root_min_one_step {V : Type*} [Fintype V] [DecidableEq V]
    {P : Matrix V V ℝ} {π : V → ℝ}
    (hP : IsStochastic P) (hπ : IsStationary P π)
    (hpos : ∀ x, 0 < π x) (hlazy : ∀ x : V, 2⁻¹ ≤ P x x) (Φ : ℝ) (hΦ0 : 0 ≤ Φ)
    (hbn : ∀ S : Finset V, 0 < piS π S → piS π S < 1 →
      Φ * min (piS π S) (1 - piS π S) ≤ qflow P π S)
    (S : Finset V) :
    ∑ T : Finset V, evolvingSets P π S T * Real.sqrt (min (piS π T) (1 - piS π T)) ≤
      (1 - Φ ^ 2 / 2) * Real.sqrt (min (piS π S) (1 - piS π S)) := by
  classical
  let w : Finset V → ℝ := fun T => evolvingSets P π S T
  let z : Finset V → ℝ := fun T => piS π T
  have hwnn : ∀ T : Finset V, 0 ≤ w T := fun T => le_max_left _ _
  let s : Finset (Finset V) := Finset.univ.filter (fun T : Finset V => 0 < w T)
  have hrestrict : ∀ g : Finset V → ℝ, ∑ T ∈ s, w T * g T = ∑ T : Finset V, w T * g T := by
    intro g
    refine Finset.sum_subset (Finset.subset_univ s) fun T _ hT => ?_
    have : w T = 0 := le_antisymm (by simpa [s] using hT) (hwnn T)
    rw [this, zero_mul]
  have hw : ∀ T ∈ s, 0 < w T := fun T hT => (Finset.mem_filter.mp hT).2
  have hz0 : ∀ T ∈ s, 0 ≤ z T := fun T _ => piS_nonneg hpos T
  have hz1 : ∀ T ∈ s, z T ≤ 1 := fun T _ => piS_le_one hπ hpos T
  have hw1 : ∑ T ∈ s, w T = 1 := by
    have h := hrestrict (fun _ => (1 : ℝ))
    simp only [mul_one] at h
    rw [h]
    exact es_sum_one P π S
  have hmean : ∑ T ∈ s, w T * z T = piS π S := by
    rw [hrestrict]
    exact es_mean hP hπ hpos S
  have hq : 2 * qflow P π S ≤ ∑ T ∈ s, w T * |z T - piS π S| := by
    rw [hrestrict]
    exact le_of_eq (es_l1 hP hπ hpos hlazy S).symm
  have hZ0' : 0 ≤ piS π S := piS_nonneg hpos S
  have hZ1' : piS π S ≤ 1 := piS_le_one hπ hpos S
  rw [← hrestrict (fun T => Real.sqrt (min (z T) (1 - z T)))]
  rcases eq_or_lt_of_le hZ0' with h0 | h0
  · rw [root_min_degenerate s w z (piS π S) hw hz0 hz1 hw1 hmean (Or.inl h0.symm), ← h0]
    norm_num
  · rcases eq_or_lt_of_le hZ1' with h1 | h1
    · rw [root_min_degenerate s w z (piS π S) hw hz0 hz1 hw1 hmean (Or.inr h1), h1]
      norm_num
    · exact RootMinProof.weighted_root_min_contract s w z (piS π S) (qflow P π S) Φ
        hw hw1 hz0 hz1 hmean hq (qflow_nonneg hP hpos S) h0 h1 hΦ0 (hbn S h0 h1)

private lemma root_min_bottleneck_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    {P : Matrix V V ℝ} {π : V → ℝ} (hP : IsStochastic P) (hpos : ∀ x, 0 < π x) :
    0 ≤ bottleneckStar P π := by
  classical
  let I := {S : Finset V // S.Nonempty ∧ ∑ x ∈ S, π x ≤ 2⁻¹}
  by_cases hI : Nonempty I
  · letI := hI
    exact le_ciInf (fun S : I => div_nonneg (qflow_nonneg hP hpos S.1) (piS_nonneg hpos S.1))
  · haveI : IsEmpty I := not_nonempty_iff.mp hI
    change 0 ≤ ⨅ S : I, bottleneckRatio P π S.1
    simp

private lemma root_min_bottleneck_bound {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {P : Matrix V V ℝ} {π : V → ℝ} (hP : IsStochastic P) (hπ : IsStationary P π)
    (hpos : ∀ x, 0 < π x) (S : Finset V) (h0 : 0 < piS π S) (h1 : piS π S < 1) :
    bottleneckStar P π * min (piS π S) (1 - piS π S) ≤ qflow P π S := by
  classical
  have hbdd : BddBelow (Set.range fun T :
      {T : Finset V // T.Nonempty ∧ ∑ x ∈ T, π x ≤ 2⁻¹} => bottleneckRatio P π T.1) := by
    refine ⟨0, ?_⟩
    rintro r ⟨T, rfl⟩
    exact div_nonneg (qflow_nonneg hP hpos T.1) (piS_nonneg hpos T.1)
  rcases le_or_gt (piS π S) 2⁻¹ with hc | hc
  · rw [min_eq_left (by linarith)]
    have hSne : S.Nonempty := by
      by_contra h
      have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      simp [he, piS] at h0
    have hle : bottleneckStar P π ≤ bottleneckRatio P π S := ciInf_le hbdd ⟨S, hSne, hc⟩
    rw [bratio_eq, le_div_iff₀ h0] at hle
    exact hle
  · rw [min_eq_right (by linarith)]
    have hcpi : piS π Sᶜ = 1 - piS π S := by rw [piS]; exact pi_compl hπ S
    have hSne : (Sᶜ : Finset V).Nonempty := by
      by_contra h
      have he : Sᶜ = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      simp only [he, piS, Finset.sum_empty] at hcpi
      change 0 = 1 - piS π S at hcpi
      linarith
    have hle : bottleneckStar P π ≤ bottleneckRatio P π Sᶜ :=
      ciInf_le hbdd ⟨Sᶜ, hSne, by change piS π Sᶜ ≤ 2⁻¹; rw [hcpi]; linarith⟩
    rw [bratio_eq, hcpi, le_div_iff₀ (by linarith), qflow_compl hP hπ] at hle
    exact hle

end MarkovMixing

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : IsStochastic P)
    (π : V → ℝ) (hπ : IsStationary P π) (hpos : ∀ x : V, 0 < π x)
    (hlazy : ∀ x : V, 2⁻¹ ≤ P x x) (S : Finset V) :
    (∑ T : Finset V, evolvingSets P π S T *
      Real.sqrt (min (∑ x ∈ T, π x) (1 - ∑ x ∈ T, π x))) ≤
      (1 - bottleneckStar P π ^ 2 / 2) *
        Real.sqrt (min (∑ x ∈ S, π x) (1 - ∑ x ∈ S, π x)) := by
  exact MarkovMixing.root_min_one_step hP hπ hpos hlazy (bottleneckStar P π)
    (MarkovMixing.root_min_bottleneck_nonneg hP hpos)
    (MarkovMixing.root_min_bottleneck_bound hP hπ hpos) S

#print axioms solution
