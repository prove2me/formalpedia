-- Prove2me | solution 1 for NatureSLT.GrowthFunction.vcDimReal_linear_functions
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T13:58:12.313073+00:00
-- url     : https://prove2.me/submissions/06474526-59c9-4622-8994-44e83cd5a726

import Mathlib
import Definitions.Def_NatureSLT_GrowthFunction_vcDimReal
open NatureSLT.GrowthFunction
theorem g70slt_not_shatter {n : ℕ} {Λ : Type*} (Q : Λ → EuclideanSpace ℝ (Fin n) → Bool)
    (hQ : ∀ α, ∃ (w : Fin n → ℝ) (c : ℝ), ∀ z, Q α z = stepFunction (∑ p, w p * z p + c))
    {h : ℕ} (hh : n + 2 ≤ h) (z : Fin h → EuclideanSpace ℝ (Fin n)) : ¬ Shatters Q z := by
  classical
  intro hs
  set f : Fin (n+2) → EuclideanSpace ℝ (Fin n) := fun i => z (Fin.castLE hh i) with hf
  have hdep : ¬ AffineIndependent ℝ f := by
    rw [← finrank_vectorSpan_le_iff_not_affineIndependent ℝ f (n := n) (by simp)]
    exact (Submodule.finrank_le _).trans (by simp)
  obtain ⟨I, p, hp1, hp2⟩ := Convex.radon_partition hdep
  obtain ⟨α, hα⟩ := hs (fun j => decide (∃ i ∈ I, Fin.castLE hh i = j))
  obtain ⟨w, c, hQ⟩ := hQ α
  let L : EuclideanSpace ℝ (Fin n) → ℝ := fun z => ∑ p, w p * z p
  have hL : IsLinearMap ℝ L := by
    constructor
    · intro x y; simp [L, mul_add, Finset.sum_add_distrib]
    · intro a x; simp [L, Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
  have h1 : convexHull ℝ (f '' I) ⊆ {z | -c ≤ L z} := by
    refine convexHull_min ?_ (convex_halfSpace_ge hL _)
    rintro _ ⟨i, hi, rfl⟩
    have := hα (Fin.castLE hh i)
    rw [hQ] at this
    have hd : decide (∃ i' ∈ I, Fin.castLE hh i' = Fin.castLE hh i) = true := by
      simp only [decide_eq_true_eq]; exact ⟨i, hi, rfl⟩
    rw [hd] at this
    simp only [stepFunction, decide_eq_true_eq] at this
    simp only [Set.mem_ofPred_eq, L, hf]; linarith
  have h2 : convexHull ℝ (f '' Iᶜ) ⊆ {z | L z < -c} := by
    refine convexHull_min ?_ (convex_halfSpace_lt hL _)
    rintro _ ⟨i, hi, rfl⟩
    have := hα (Fin.castLE hh i)
    rw [hQ] at this
    have hd : decide (∃ i' ∈ I, Fin.castLE hh i' = Fin.castLE hh i) = false := by
      simp only [decide_eq_false_iff_not, not_exists, not_and]
      intro i' hi' heq
      exact hi (Fin.castLE_injective hh heq ▸ hi')
    rw [hd] at this
    simp only [stepFunction, decide_eq_false_iff_not, not_le] at this
    simp only [Set.mem_ofPred_eq, L, hf]; linarith
  have a1 := h1 hp1
  have a2 := h2 hp2
  simp only [Set.mem_ofPred_eq] at a1 a2
  linarith

theorem g70slt_shatter (n : ℕ) :
    ∃ z : Fin (n + 1) → EuclideanSpace ℝ (Fin n),
      Shatters (fun (α : (Fin n → ℝ) × ℝ) (z : EuclideanSpace ℝ (Fin n)) =>
        stepFunction (∑ p : Fin n, α.1 p * z p + α.2)) z := by
  refine ⟨Fin.cases 0 (fun i => EuclideanSpace.single i 1), ?_⟩
  intro δ
  set b : ℝ := if δ 0 then 0 else -1 with hb
  refine ⟨(fun p => (if δ p.succ then 1 else -1) - b, b), ?_⟩
  intro i
  refine Fin.cases ?_ (fun q => ?_) i
  · simp only [Fin.cases_zero, stepFunction]
    cases h : δ 0 <;> simp [hb, h]
  · simp only [Fin.cases_succ, stepFunction]
    have key : ∑ p : Fin n, ((if δ p.succ then (1:ℝ) else -1) - b) *
        (EuclideanSpace.single q (1:ℝ) : EuclideanSpace ℝ (Fin n)) p
        = (if δ q.succ then (1:ℝ) else -1) - b := by
      rw [Finset.sum_eq_single q]
      · simp
      · intro p _ hp; simp [EuclideanSpace.single_apply, hp]
      · simp
    simp only [key]
    cases h : δ q.succ <;> simp [h] <;> norm_num

theorem g70slt_vcDim_eq {n : ℕ} {Λ : Type*} (Q : Λ → EuclideanSpace ℝ (Fin n) → Bool)
    (hQ : ∀ α, ∃ (w : Fin n → ℝ) (c : ℝ), ∀ z, Q α z = stepFunction (∑ p, w p * z p + c))
    (hQ' : ∀ (w : Fin n → ℝ) (c : ℝ), ∃ α, ∀ z, Q α z = stepFunction (∑ p, w p * z p + c)) :
    vcDim Q = ((n + 1 : ℕ) : ℕ∞) := by
  apply le_antisymm
  · refine iSup₂_le fun h ⟨z, hz⟩ => ?_
    by_contra hlt
    have : n + 2 ≤ h := by
      by_contra h'; apply hlt; exact_mod_cast (by omega : h ≤ n + 1)
    exact g70slt_not_shatter Q hQ this z hz
  · obtain ⟨z, hz⟩ := g70slt_shatter n
    refine le_iSup₂_of_le (n + 1) ⟨z, ?_⟩ le_rfl
    intro δ
    obtain ⟨α, hα⟩ := hz δ
    obtain ⟨β, hβ⟩ := hQ' α.1 α.2
    exact ⟨β, fun i => (hβ _).trans (hα i)⟩



/-- Vapnik, *The Nature of Statistical Learning Theory*, 2nd ed., §3.6, p. 81, Example 1(ii): the
VC dimension of the set of linear functions `Q(z, α) = ∑_{p=1}^n α_p z_p + α₀`,
`α₀, …, α_n ∈ (−∞, ∞)`, in `n`-dimensional coordinate space, is `h = n + 1`. The VC dimension of
real functions is that of the indicators `θ{Q(z, α) − β}`, `β ∈ (A, B)`, here with
`A = −∞`, `B = ∞`. -/
theorem solution (n : ℕ) :
    vcDimReal (fun (α : (Fin n → ℝ) × ℝ) (z : EuclideanSpace ℝ (Fin n)) =>
      ∑ p : Fin n, α.1 p * z p + α.2) ⊥ ⊤ = ((n + 1 : ℕ) : ℕ∞) := by
  unfold vcDimReal
  refine g70slt_vcDim_eq _ (fun p => ⟨p.1.1.1, p.1.1.2 - p.1.2, fun z => ?_⟩)
    (fun w c => ⟨⟨((w, c), 0), by simp⟩, fun z => ?_⟩)
  · simp only [realIndicators]; congr 1; ring
  · simp only [realIndicators]; congr 1; ring

