-- Prove2me | solution 1 for NisanRonen.Rounding.report_subset_optimum_le_singletons
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T08:02:13.548669+00:00
-- url     : https://prove2.me/submissions/d207ae64-9b1b-466f-9f44-77c9f3339289

import Definitions.Def_NisanRonen_Rounding_CertificateCriterion

open NisanRonen.Rounding
open scoped BigOperators

set_option autoImplicit false

private noncomputable def rowLoad {n k : ℕ} (δ : ℝ) (x : Fin k → Fin n)
    (d : Fin n → Fin k → ℝ) (l : Fin n) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => x j = l), roundUp δ (d l j)

private noncomputable def span {n k : ℕ} [NeZero n] (δ : ℝ) (x : Fin k → Fin n)
    (d : Fin n → Fin k → ℝ) : ℝ :=
  roundedMakespan δ x (corrStar x d)

private theorem span_eq {n k : ℕ} [NeZero n] (δ : ℝ) (x : Fin k → Fin n)
    (d : Fin n → Fin k → ℝ) :
    span δ x d = Finset.univ.sup' Finset.univ_nonempty (rowLoad δ x d) := by
  unfold span roundedMakespan makespan
  congr 1
  funext l
  unfold rowLoad load
  apply Finset.sum_congr rfl
  intro j hj
  simp [corrStar, (Finset.mem_filter.1 hj).2]

theorem solution {n k : ℕ} [NeZero n] {a b δ C : ℝ}
    (f : List (Fin n → ℕ) → List (Fin n)) (hf : IsExactRoundedSolver f δ a b)
    (t d : Fin n → Fin k → ℝ) (ht : ∀ l j, a ≤ t l j ∧ t l j ≤ b)
    (hd : ∀ l j, a ≤ d l j ∧ d l j ≤ b)
    (hop : ∀ i, DeclarationOptimal f δ a b i (t i) (d i))
    (y : Fin k → Fin n) (hy : roundedMakespan δ y (corrStar y t) ≤ C)
    (hsingle : ∀ i, let v := Function.update t i (d i)
      roundedMakespan δ (allocOf f δ v) (corrStar (allocOf f δ v) v) ≤ C)
    (S : Finset (Fin n)) :
    let v (l : Fin n) := if l ∈ S then d l else t l
    roundedMakespan δ (allocOf f δ v) (corrStar (allocOf f δ v) v) ≤ C := by
  classical
  dsimp only
  let mix (S : Finset (Fin n)) (l : Fin n) := if l ∈ S then d l else t l
  have hMix (S : Finset (Fin n)) (l : Fin n) (j : Fin k) :
      a ≤ mix S l j ∧ mix S l j ≤ b := by
    by_cases h : l ∈ S <;> simp [mix, h, ht, hd]
  change span δ (allocOf f δ (mix S)) (mix S) ≤ C
  induction S using Finset.strongInductionOn
  rename_i S ih
  by_cases hempty : S = ∅
  · subst S
    have h : mix ∅ = t := by funext l; simp [mix]
    rw [h]
    exact ((hf k t ht).2 y).trans hy
  obtain ⟨j₀, hj₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  by_cases hS : S = {j₀}
  · subst S
    have he : mix {j₀} = Function.update t j₀ (d j₀) := by
      funext l
      by_cases h : l = j₀ <;> simp [mix, h]
    rw [he]
    exact hsingle j₀
  let x := allocOf f δ (mix S)
  obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (rowLoad δ x (mix S))
  have hmax : span δ x (mix S) = rowLoad δ x (mix S) p := by
    rw [span_eq]
    exact hp
  have hDiff : ∃ j ∈ S, j ≠ p := by
    by_contra hn
    push Not at hn
    apply hS
    ext l
    simp only [Finset.mem_singleton]
    exact ⟨fun hl => (hn l hl).trans (hn j₀ hj₀).symm, fun hl => hl ▸ hj₀⟩
  obtain ⟨j, hj, hjp⟩ := hDiff
  let v := mix (S.erase j)
  have hv : Function.update (mix S) j (t j) = v := by
    funext l
    by_cases h : l = j
    · subst l; simp [v, mix]
    · simp [v, mix, h, Finset.mem_erase]
  have hreport : mix S j = d j := by simp [mix, hj]
  have hcorrect : span δ x v ≤ span δ (allocOf f δ v) v := by
    have h : span δ x (Function.update (mix S) j (t j)) ≤
        span δ (allocOf f δ v) (Function.update (mix S) j (t j)) :=
      hop j (mix S) (hMix S) hreport (allocOf f δ v)
    rwa [hv] at h
  have hs : v p = mix S p := by rw [← hv]; simp [Ne.symm hjp]
  refine le_trans ?_ (hcorrect.trans (ih (S.erase j) (Finset.erase_ssubset hj)))
  rw [hmax, ← show rowLoad δ x v p = rowLoad δ x (mix S) p by simp [rowLoad, hs], span_eq]
  exact Finset.le_sup' _ (Finset.mem_univ p)
