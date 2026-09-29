-- Prove2me | solution 1 for KServer.workFnU_growth_card_succ_inj
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T07:21:48.191346+00:00
-- url     : https://prove2.me/submissions/e3923799-5a17-4bc5-9482-dcaf7c7f76a7

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Theorems.Thm_KServer_workFnU_perm
import Theorems.Thm_KServer_workFnU_mono
import Theorems.Thm_KServer_workFn_nonneg
import Theorems.Thm_KServer_workFn_lipschitz
import Theorems.Thm_KServer_workFn_approx_offlineCost

open KServer

private theorem mc_perm {k : ℕ} {M : Type} [MetricSpace M] (Y Z : Config k M)
    (π : Equiv.Perm (Fin k)) :
    moveCost (Y ∘ (π : Equiv.Perm (Fin k))) (Z ∘ (π : Equiv.Perm (Fin k)))
      = moveCost Y Z := by
  unfold moveCost
  exact Fintype.sum_equiv π (fun i => dist (Y (π i)) (Z (π i))) (fun j => dist (Y j) (Z j))
    (fun i => rfl)

private theorem wfU_le {k : ℕ} {M : Type} [MetricSpace M] (C₀ : Config k M) (σ : List M)
    (X : Config k M) (π : Equiv.Perm (Fin k)) :
    workFnU C₀ σ X ≤ workFn C₀ σ (X ∘ π) :=
  ciInf_le (Finite.bddBelow_range _) π

private theorem wfU_exists {k : ℕ} {M : Type} [MetricSpace M] (C₀ : Config k M) (σ : List M)
    (X : Config k M) : ∃ π : Equiv.Perm (Fin k), workFn C₀ σ (X ∘ π) = workFnU C₀ σ X :=
  exists_eq_ciInf_of_finite

private theorem wfU_self {k : ℕ} {M : Type} [MetricSpace M] (C₀ : Config k M) (σ : List M)
    (X : Config k M) : workFnU C₀ σ X ≤ workFn C₀ σ X := by
  simpa using wfU_le C₀ σ X 1

private theorem wfU_nonneg (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) : 0 ≤ workFnU C₀ σ X := by
  obtain ⟨π, hπ⟩ := wfU_exists C₀ σ X
  rw [← hπ]
  exact workFn_nonneg k hk M C₀ σ (X ∘ π)

private theorem wfU_lipschitz (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X Y : Config k M) :
    workFnU C₀ σ X ≤ workFnU C₀ σ Y + moveCost Y X := by
  obtain ⟨π, hπ⟩ := wfU_exists C₀ σ Y
  have h1 := wfU_le C₀ σ X π
  have h2 := workFn_lipschitz k hk M C₀ σ (X ∘ π) (Y ∘ π)
  have h3 := mc_perm Y X π
  rw [hπ] at h2
  linarith

/-- Two injective configurations with the same range differ by a relabelling. -/
private theorem perm_of_range_eq {k : ℕ} {M : Type} (X : Fin k → M)
    (hX : Function.Injective X) (Y : Fin k → M) (hY : Function.Injective Y)
    (h : Set.range X = Set.range Y) : ∃ π : Equiv.Perm (Fin k), Y ∘ π = X := by
  refine ⟨(Equiv.ofInjective X hX).trans
    ((Equiv.setCongr h).trans (Equiv.ofInjective Y hY).symm), ?_⟩
  funext i
  simp only [Function.comp_apply, Equiv.trans_apply]
  exact congrArg Subtype.val
    ((Equiv.ofInjective Y hY).apply_symm_apply ((Equiv.setCongr h) ((Equiv.ofInjective X hX) i)))

/-- **The total growth of the unordered work function on a space of `k+1` points is at most
`k+1` times the optimum**, at injective configurations. -/
theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M] [Fintype M]
    (hM : Fintype.card M = k + 1) (C₀ : Config k M) :
    ∃ c : ℝ, ∀ σ : List M, ∃ u : ℕ → ℝ,
      (∀ t : ℕ, t < σ.length → ∀ X : Config k M, Function.Injective X →
          workFnU C₀ (σ.take (t + 1)) X ≤ workFnU C₀ (σ.take t) X + u t) ∧
      (∑ t ∈ Finset.range σ.length, u t) ≤ ((k : ℝ) + 1) * offlineCost C₀ σ + c := by
  classical
  -- the diameter of `M`
  have hpos : 0 < Fintype.card M := by rw [hM]; omega
  obtain ⟨m₀⟩ := Fintype.card_pos_iff.mp hpos
  set Δ : ℝ := (Finset.univ : Finset (M × M)).sup' ⟨(m₀, m₀), Finset.mem_univ _⟩
    (fun q : M × M => dist q.1 q.2) with hΔdef
  have hdle : ∀ p q : M, dist p q ≤ Δ := by
    intro p q
    rw [hΔdef]
    exact Finset.le_sup' (fun q : M × M => dist q.1 q.2) (Finset.mem_univ (p, q))
  have hΔ0 : (0:ℝ) ≤ Δ := le_trans dist_nonneg (hdle m₀ m₀)
  -- a hole configuration for each point
  have hex : ∀ p : M, ∃ g : Fin k → M, Function.Injective g ∧ ∀ i, g i ≠ p := by
    intro p
    have hc : Fintype.card {x : M // x ≠ p} = k := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, hM]; omega
    refine ⟨fun i => ((Fintype.equivFinOfCardEq hc).symm i : M), ?_,
      fun i => ((Fintype.equivFinOfCardEq hc).symm i).2⟩
    intro a b hab
    exact (Fintype.equivFinOfCardEq hc).symm.injective (Subtype.ext hab)
  choose H hHinj hHne using hex
  -- every injective configuration is a relabelling of some `H p`
  have hclass : ∀ X : Config k M, Function.Injective X →
      ∃ p : M, ∃ π : Equiv.Perm (Fin k), H p ∘ π = X := by
    intro X hX
    have hcardim : (Finset.univ.image X).card = k := by
      rw [Finset.card_image_of_injective _ hX, Finset.card_univ, Fintype.card_fin]
    have hcompl : ((Finset.univ : Finset M) \ Finset.univ.image X).card = 1 := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hM, hcardim]; omega
    obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hcompl
    have hpnot : p ∉ Finset.univ.image X := by
      have hmem : p ∈ (Finset.univ : Finset M) \ Finset.univ.image X := by rw [hp]; simp
      exact (Finset.mem_sdiff.mp hmem).2
    have hXne : ∀ i, X i ≠ p := by
      intro i hi
      exact hpnot (by rw [← hi]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i))
    have hcarderase : ((Finset.univ : Finset M).erase p).card = k := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ, hM]
      omega
    have himX : Finset.univ.image X = (Finset.univ : Finset M).erase p := by
      refine Finset.eq_of_subset_of_card_le ?_ (by rw [hcarderase, hcardim])
      intro y hy
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_erase.mpr ⟨hXne i, Finset.mem_univ _⟩
    have himH : Finset.univ.image (H p) = (Finset.univ : Finset M).erase p := by
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro y hy
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
        exact Finset.mem_erase.mpr ⟨hHne p i, Finset.mem_univ _⟩
      · rw [hcarderase, Finset.card_image_of_injective _ (hHinj p), Finset.card_univ,
          Fintype.card_fin]
    have hrange : Set.range X = Set.range (H p) := by
      have e1 : Set.range X = ↑(Finset.univ.image X) := by
        rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
      have e2 : Set.range (H p) = ↑(Finset.univ.image (H p)) := by
        rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
      rw [e1, e2, himX, himH]
    obtain ⟨π, hπ⟩ := perm_of_range_eq X hX (H p) (hHinj p) hrange
    exact ⟨p, π, hπ⟩
  -- the constant
  refine ⟨((k : ℝ) + 1) * ((k : ℝ) * Δ), fun σ => ?_⟩
  set n := σ.length with hn
  refine ⟨fun t => ∑ p : M, (workFnU C₀ (σ.take (t + 1)) (H p)
      - workFnU C₀ (σ.take t) (H p)), ?_, ?_⟩
  · -- the growth bound at injective configurations
    intro t ht X hX
    obtain ⟨p, π, hπ⟩ := hclass X hX
    have hts : σ.take (t + 1) = σ.take t ++ [σ[t]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem ht]; rfl
    have hnonneg : ∀ q : M, q ∈ (Finset.univ : Finset M) →
        0 ≤ workFnU C₀ (σ.take (t + 1)) (H q) - workFnU C₀ (σ.take t) (H q) := by
      intro q _
      have := workFnU_mono k hk M C₀ (σ.take t) σ[t] (H q)
      rw [← hts] at this
      linarith
    have hsingle := Finset.single_le_sum hnonneg (Finset.mem_univ p)
    have e1 : workFnU C₀ (σ.take (t + 1)) X = workFnU C₀ (σ.take (t + 1)) (H p) := by
      rw [← hπ]; exact workFnU_perm k M C₀ (σ.take (t + 1)) (H p) π
    have e2 : workFnU C₀ (σ.take t) X = workFnU C₀ (σ.take t) (H p) := by
      rw [← hπ]; exact workFnU_perm k M C₀ (σ.take t) (H p) π
    rw [e1, e2]
    linarith
  · -- the summed bound
    have hswap : ∑ t ∈ Finset.range n, ∑ p : M,
        (workFnU C₀ (σ.take (t + 1)) (H p) - workFnU C₀ (σ.take t) (H p))
        = ∑ p : M, ∑ t ∈ Finset.range n,
          (workFnU C₀ (σ.take (t + 1)) (H p) - workFnU C₀ (σ.take t) (H p)) :=
      Finset.sum_comm
    have htel : ∀ p : M, ∑ t ∈ Finset.range n,
        (workFnU C₀ (σ.take (t + 1)) (H p) - workFnU C₀ (σ.take t) (H p))
        = workFnU C₀ σ (H p) - workFnU C₀ [] (H p) := by
      intro p
      rw [Finset.sum_range_sub (fun t => workFnU C₀ (σ.take t) (H p)) n, hn,
        List.take_length, List.take_zero]
    have hupper : ∀ p : M, workFnU C₀ σ (H p) ≤ offlineCost C₀ σ + (k : ℝ) * Δ := by
      intro p
      refine le_of_forall_pos_le_add ?_
      intro ε hε
      obtain ⟨X, hX⟩ := workFn_approx_offlineCost k hk M C₀ σ ε hε
      have h1 := wfU_lipschitz k hk M C₀ σ (H p) X
      have h2 := wfU_self C₀ σ X
      have h3 : moveCost X (H p) ≤ (k : ℝ) * Δ := by
        unfold moveCost
        calc ∑ i, dist (X i) (H p i) ≤ ∑ _i : Fin k, Δ :=
              Finset.sum_le_sum fun i _ => hdle _ _
          _ = (k : ℝ) * Δ := by simp [mul_comm]
      linarith
    have hterm : ∀ p : M, workFnU C₀ σ (H p) - workFnU C₀ [] (H p)
        ≤ offlineCost C₀ σ + (k : ℝ) * Δ := by
      intro p
      have := wfU_nonneg k hk M C₀ ([] : List M) (H p)
      have := hupper p
      linarith
    calc ∑ t ∈ Finset.range n, ∑ p : M,
          (workFnU C₀ (σ.take (t + 1)) (H p) - workFnU C₀ (σ.take t) (H p))
        = ∑ p : M, (workFnU C₀ σ (H p) - workFnU C₀ [] (H p)) := by
          rw [hswap]; exact Finset.sum_congr rfl fun p _ => htel p
      _ ≤ ∑ _p : M, (offlineCost C₀ σ + (k : ℝ) * Δ) :=
          Finset.sum_le_sum fun p _ => hterm p
      _ = ((k : ℝ) + 1) * (offlineCost C₀ σ + (k : ℝ) * Δ) := by
          rw [Finset.sum_const, Finset.card_univ, hM]
          push_cast
          ring
      _ = ((k : ℝ) + 1) * offlineCost C₀ σ + ((k : ℝ) + 1) * ((k : ℝ) * Δ) := by ring
