-- Prove2me | solution 1 for MulticlassDS.Compress.fact14_leave_one_out
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T09:28:28.880977+00:00
-- url     : https://prove2.me/submissions/bfb47538-34e4-48e2-bc7d-4992b08dce27

import Mathlib
import Definitions.Def_MulticlassDS_Compress_Probability
open scoped ENNReal

set_option autoImplicit false

open MulticlassDS.Compress in
theorem dd2b0edc_iidProb_perm {Z : Type*} (D : PMF Z) (m : ℕ) (σ : Equiv.Perm (Fin m))
    (E : Set (Fin m → Z)) :
    iidProb D m {s | s ∘ σ ∈ E} = iidProb D m E := by
  unfold iidProb
  let e : (Fin m → Z) ≃ (Fin m → Z) :=
    { toFun := fun t => t ∘ σ.symm
      invFun := fun s => s ∘ σ
      left_inv := fun t => by funext i; simp
      right_inv := fun s => by funext i; simp }
  rw [← e.tsum_eq]
  congr 1
  funext t
  have h1 : (∏ i, D ((e t) i)) = ∏ i, D (t i) := by
    show (∏ i, D (t (σ.symm i))) = ∏ i, D (t i)
    exact Equiv.prod_comp σ.symm (fun i => D (t i))
  have h2 : (e t) ∘ σ = t := by funext i; simp [e]
  have h3 : (e t ∈ {s : Fin m → Z | s ∘ σ ∈ E}) ↔ t ∈ E := by
    show (e t ∘ σ ∈ E) ↔ _
    rw [h2]
  rw [h1]
  congr 1
  simp only [Set.indicator]
  by_cases ht : t ∈ E
  · rw [if_pos (h3.mpr ht), if_pos ht]
    rfl
  · rw [if_neg (mt h3.mp ht), if_neg ht]

theorem dd2b0edc_snoc_inj (n : ℕ) (I : Fin (n + 1)) :
    Function.Injective (Fin.snoc (α := fun _ => Fin (n + 1)) I.succAbove I) := by
  intro a b h
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last => rfl
    | cast j =>
      simp only [Fin.snoc_last, Fin.snoc_castSucc] at h
      exact absurd h.symm (Fin.succAbove_ne I j)
  | cast i =>
    induction b using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last, Fin.snoc_castSucc] at h
      exact absurd h (Fin.succAbove_ne I i)
    | cast j =>
      simp only [Fin.snoc_castSucc] at h
      rw [Fin.succAbove_right_inj.mp h]

open scoped ENNReal in open MulticlassDS.Compress in
theorem solution {Z : Type*} (D : PMF Z) (n : ℕ) (hn : 0 < n)
    (E : Set (Fin (n + 1) → Z)) :
    iidProb D (n + 1) E = (1 / ((n : ℝ≥0∞) + 1)) * ∑ I : Fin (n + 1),
      iidProb D (n + 1) {s | Fin.snoc (s ∘ I.succAbove) (s I) ∈ E} := by
  have key : ∀ I : Fin (n + 1),
      iidProb D (n + 1) {s | Fin.snoc (s ∘ I.succAbove) (s I) ∈ E} = iidProb D (n + 1) E := by
    intro I
    let σ : Equiv.Perm (Fin (n + 1)) :=
      Equiv.ofBijective _ (Finite.injective_iff_bijective.mp (dd2b0edc_snoc_inj n I))
    have hs : ∀ s : Fin (n + 1) → Z,
        (Fin.snoc (α := fun _ => Z) (s ∘ I.succAbove) (s I)) = s ∘ σ := by
      intro s
      funext j
      induction j using Fin.lastCases with
      | last => simp [σ]
      | cast j => simp [σ]
    have hset : {s : Fin (n + 1) → Z | Fin.snoc (s ∘ I.succAbove) (s I) ∈ E}
        = {s | s ∘ σ ∈ E} := by
      ext s
      simp only [Set.mem_ofPred_eq, hs]
    rw [hset, dd2b0edc_iidProb_perm]
  simp only [key, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  rw [← mul_assoc, one_div, ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]
