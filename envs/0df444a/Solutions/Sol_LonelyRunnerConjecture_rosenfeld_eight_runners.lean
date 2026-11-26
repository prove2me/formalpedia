-- Prove2me | solution 1 for LonelyRunnerConjecture.rosenfeld_eight_runners
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-26T21:55:28.439841+00:00
-- url     : https://prove2.me/submissions/d3a7a3f1-872c-4743-a19b-0f6341753352
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LonelyRunnerConjecture_Defs
import Theorems.Thm_LonelyRunnerConjecture_classical_small_cases
import Theorems.Thm_LonelyRunnerConjecture_mss_finite_checking
import Theorems.Thm_LefebvreVariations_lonely_runner_seven_small_gcd_sum

set_option autoImplicit false

open LonelyRunnerConjecture

/-! The variation, verbatim (the only open step that belongs to it). -/

private lemma core (n : ℕ) (hn : 1 ≤ n)
    (mss : ∀ v : Fin n → ℕ, (∀ i, 0 < v i) → Finset.gcd Finset.univ v = 1 →
      (∑ S ∈ Finset.univ.powerset, Finset.gcd S v) > Nat.choose (n + 1) 2 ^ (n - 1) →
      ∃ t : ℝ, ∀ i, (1 : ℝ) / (n + 1 : ℝ) ≤ distToNearestInt (t * (v i : ℝ)))
    (var : ∀ v : Fin n → ℕ, (∀ i, 0 < v i) → Finset.gcd Finset.univ v = 1 →
      (∑ S ∈ Finset.univ.powerset, Finset.gcd S v) ≤ Nat.choose (n + 1) 2 ^ (n - 1) →
      ∃ t : ℝ, ∀ i, (1 : ℝ) / (n + 1 : ℝ) ≤ distToNearestInt (t * (v i : ℝ))) :
    LRC n := by
  intro S hS hpos
  have hSne : S.Nonempty := by
    rw [← Finset.card_pos]; omega
  set g := S.gcd id with hg
  have hdvd : ∀ s ∈ S, g ∣ s := fun s hs => Finset.gcd_dvd (f := id) hs
  have hgpos : 0 < g := by
    obtain ⟨a, ha⟩ := hSne
    exact Nat.pos_of_dvd_of_pos (hdvd a ha) (hpos a ha)
  set S' : Finset ℕ := S.image (· / g) with hS'
  have hinj : Set.InjOn (· / g) (S : Set ℕ) := by
    intro a ha b hb hab
    have h1 := Nat.div_mul_cancel (hdvd a ha)
    have h2 := Nat.div_mul_cancel (hdvd b hb)
    simp only at hab
    rw [← h1, ← h2, hab]
  have hcard : S'.card = n := by
    rw [hS', Finset.card_image_of_injOn hinj, hS]
  have hpos' : ∀ s ∈ S', 0 < s := by
    intro s hs
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hs
    exact Nat.div_pos (Nat.le_of_dvd (hpos a ha) (hdvd a ha)) hgpos
  have hgcd' : S'.gcd id = 1 := by
    set d := S'.gcd id
    have hd : g * d ∣ g := by
      apply Finset.dvd_gcd
      intro s hs
      have h1 : d ∣ s / g := Finset.gcd_dvd (f := id) (Finset.mem_image_of_mem _ hs)
      have h2 := Nat.div_mul_cancel (hdvd s hs)
      rw [← h2, mul_comm (s / g) g]
      exact Nat.mul_dvd_mul_left g h1
    have h1 : g * d ∣ g * 1 := by simpa using hd
    exact Nat.dvd_one.mp (Nat.dvd_of_mul_dvd_mul_left hgpos h1)
  let v : Fin n → ℕ := fun i => S'.orderEmbOfFin hcard i
  have hvmem : ∀ i, v i ∈ S' := fun i => Finset.orderEmbOfFin_mem S' hcard i
  have hrange : Finset.univ.image v = S' := Finset.image_orderEmbOfFin_univ S' hcard
  have hvpos : ∀ i, 0 < v i := fun i => hpos' _ (hvmem i)
  have hvgcd : Finset.gcd Finset.univ v = 1 := by
    have : (Finset.univ.image v).gcd id = Finset.univ.gcd (id ∘ v) := Finset.gcd_image _
    rw [hrange, hgcd'] at this
    simpa [Function.comp_def] using this.symm
  obtain ⟨t, ht⟩ : ∃ t : ℝ, ∀ i, (1 : ℝ) / (n + 1 : ℝ) ≤ distToNearestInt (t * (v i : ℝ)) := by
    by_cases hs : (∑ S ∈ Finset.univ.powerset, Finset.gcd S v) ≤ Nat.choose (n + 1) 2 ^ (n - 1)
    · exact var v hvpos hvgcd hs
    · exact mss v hvpos hvgcd (not_le.mp hs)
  refine ⟨t / g, fun s hs => ?_⟩
  have hs' : s / g ∈ S' := Finset.mem_image_of_mem _ hs
  rw [← hrange] at hs'
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hs'
  have hcast : (s : ℝ) = (g : ℝ) * ((s / g : ℕ) : ℝ) := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' (hdvd s hs)]
  have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hgpos.ne'
  have : t / g * (s : ℝ) = t * (v i : ℝ) := by
    rw [hcast, ← hi]; field_simp
  rw [this]
  have := ht i
  norm_num at this ⊢
  exact this

private lemma step (n : ℕ) (hn : 1 ≤ n) (hprev : LRC (n - 1))
    (var : ∀ v : Fin n → ℕ, (∀ i, 0 < v i) → Finset.gcd Finset.univ v = 1 →
      (∑ S ∈ Finset.univ.powerset, Finset.gcd S v) ≤ Nat.choose (n + 1) 2 ^ (n - 1) →
      ∃ t : ℝ, ∀ i, (1 : ℝ) / (n + 1 : ℝ) ≤ distToNearestInt (t * (v i : ℝ))) :
    LRC n :=
  core n hn (fun v hp hg hs => mss_finite_checking n hn hprev v hp hg hs) var


theorem solution : LRC 7 :=
  step 7 (by norm_num) (classical_small_cases 6 le_rfl)
    (fun v hp hg hs => LefebvreVariations.lonely_runner_seven_small_gcd_sum v hp hg hs)
