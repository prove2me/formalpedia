-- Prove2me | solution 1 for GlobalTheory.InvariantLift.exists_invariant_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:08:35.624249+00:00
-- url     : https://prove2.me/submissions/6162cd12-d9cd-4e0b-a695-c07653309385

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsInvariantMatrixLiftOfAdicComplete
import Theorems.Thm_GlobalTheory_InvariantLift_average_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.InvariantLift
variable {G : Type} [Group G] {A : Type} [CommRing A] {r : ℕ}
namespace GlobalTheory.InvariantLift
theorem _root_.solution : ∀ (G : Type) [Group G] (A : Type) [CommRing A] (π : A), IsAdicComplete (Ideal.span {π}) A → ∀ (σ : G → A →+* A), (∀ g h a, σ (g * h) a = σ g (σ h a)) → (∀ g, σ g π = π) → ∀ (r : ℕ) (M : G →* Matrix (Fin r) (Fin r) A), (∀ g h i j, σ g (M h i j) = M h i j) → ∀ (S : Set (Subgroup G)), (∀ N ∈ S, N.Normal ∧ Finite (G ⧸ N) ∧ ∃ τ : A, (∀ g ∈ N, σ g τ = τ) ∧ ∑ᶠ x : G ⧸ N, σ x.out τ = 1) → (∀ N ∈ S, ∀ k : ℕ, ∃ N' ∈ S, N' ≤ N ∧ ∀ g ∈ N', ∀ i j, π ^ k ∣ (M g - 1) i j) → ∀ (W₀ : Matrix (Fin r) (Fin r) A), (∃ N ∈ S, ∀ g ∈ N, W₀.map (σ g) = W₀) → (∀ g i j, π ∣ (M g * W₀.map (σ g) - W₀) i j) → ∃ W : Matrix (Fin r) (Fin r) A, (∀ i j, π ∣ (W - W₀) i j) ∧ ∀ g, M g * W.map (σ g) = W := by
  intro G _ A _ π hA σ hσ hσπ r M hM S hS hSk W₀ hW₀ hW₀c
  classical

  have hstep : ∀ (k : ℕ) (N : Subgroup G) (W : Matrix (Fin r) (Fin r) A), N ∈ S →
      (∀ g ∈ N, W.map (σ g) = W) → (∀ g i j, π ^ (k + 1) ∣ (M g * W.map (σ g) - W) i j) →
      ∃ (N' : Subgroup G) (W' : Matrix (Fin r) (Fin r) A), N' ∈ S ∧ (∀ g ∈ N', W'.map (σ g) = W') ∧
        (∀ g i j, π ^ (k + 1 + 1) ∣ (M g * W'.map (σ g) - W') i j) ∧
        ∀ i j, π ^ (k + 1) ∣ (W - W') i j := by
    intro k N W hNS hWN hWc
    obtain ⟨N', hN'S, hN'N, hN'd⟩ := hSk N hNS (k + 1 + 1)
    obtain ⟨hN'n, hN'f, τ, hτ, hτ1⟩ := hS N' hN'S
    haveI := hN'n
    haveI := hN'f
    obtain ⟨W', h1, h2, h3⟩ := GlobalTheory.InvariantLift.average_step σ hσ M hM N' τ hτ hτ1
      (π ^ (k + 1)) (π ^ (k + 1 + 1)) hN'd W (fun g hg => hWN g (hN'N hg)) hWc
    exact ⟨N', W', hN'S, h2, h3, h1⟩
  choose! Nf Wf hNf hWf hcf hdf using hstep
  obtain ⟨N₀, hN₀S, hN₀W⟩ := hW₀
  obtain ⟨seq, hseq0, hseqs⟩ : ∃ seq : ℕ → Subgroup G × Matrix (Fin r) (Fin r) A,
      seq 0 = (N₀, W₀) ∧ ∀ k, seq (k + 1) = (Nf k (seq k).1 (seq k).2, Wf k (seq k).1 (seq k).2) :=
    ⟨fun k => Nat.rec (N₀, W₀) (fun k q => (Nf k q.1 q.2, Wf k q.1 q.2)) k, rfl, fun _ => rfl⟩
  have hP : ∀ k, (seq k).1 ∈ S ∧ (∀ g ∈ (seq k).1, (seq k).2.map (σ g) = (seq k).2) ∧
      ∀ g i j, π ^ (k + 1) ∣ (M g * (seq k).2.map (σ g) - (seq k).2) i j := by
    intro k
    induction k with
    | zero => exact ⟨by simp [hseq0, hN₀S], by simpa [hseq0] using hN₀W,
        by simpa [hseq0] using hW₀c⟩
    | succ k ih =>
      rw [hseqs]
      exact ⟨hNf k _ _ ih.1 ih.2.1 ih.2.2, hWf k _ _ ih.1 ih.2.1 ih.2.2, hcf k _ _ ih.1 ih.2.1 ih.2.2⟩
  have hd : ∀ k i j, π ^ (k + 1) ∣ (seq k).2 i j - (seq (k + 1)).2 i j := by
    intro k i j
    have := hdf k _ _ (hP k).1 (hP k).2.1 (hP k).2.2 i j
    rw [hseqs]
    simpa [Matrix.sub_apply] using this
  have hcauchy : ∀ m n, m ≤ n → ∀ i j, π ^ m ∣ (seq m).2 i j - (seq n).2 i j := by
    intro m n hmn i j
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have e : (seq m).2 i j - (seq (n + 1)).2 i j =
          ((seq m).2 i j - (seq n).2 i j) + ((seq n).2 i j - (seq (n + 1)).2 i j) := by ring
      rw [e]
      exact dvd_add ih ((pow_dvd_pow π (by omega)).trans (hd n i j))

  have hmod : ∀ (n : ℕ) (x y : A),
      x ≡ y [SMOD ((Ideal.span {π}) ^ n • (⊤ : Submodule A A))] ↔ π ^ n ∣ x - y := by
    intro n x y
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
  have hlim : ∀ i j, ∃ L : A, ∀ n, π ^ n ∣ (seq n).2 i j - L := by
    intro i j
    obtain ⟨L, hL⟩ := hA.toIsPrecomplete.prec (f := fun n => (seq n).2 i j)
      (fun {m n} hmn => (hmod m _ _).mpr (hcauchy m n hmn i j))
    exact ⟨L, fun n => (hmod n _ _).mp (hL n)⟩
  choose L hL using hlim
  refine ⟨Matrix.of L, ?_, ?_⟩
  · intro i j
    have a := hd 0 i j
    have b := hL i j 1
    rw [hseq0] at a
    simp only [zero_add, pow_one] at a b
    have c : π ∣ W₀ i j - L i j := by
      have e : W₀ i j - L i j = (W₀ i j - (seq 1).2 i j) + ((seq 1).2 i j - L i j) := by ring
      rw [e]
      exact dvd_add a b
    simpa [Matrix.sub_apply] using dvd_sub_comm.mp c
  · intro g
    ext i j
    apply sub_eq_zero.mp
    rw [← Matrix.sub_apply]
    apply hA.toIsHausdorff.haus
    intro n
    rw [hmod, sub_zero]
    have key : (M g * (Matrix.of L).map (σ g) - Matrix.of L) i j =
        (∑ k, M g i k * σ g (L k j - (seq n).2 k j)) +
          (M g * (seq n).2.map (σ g) - (seq n).2) i j + ((seq n).2 i j - L i j) := by
      simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, map_sub,
        mul_sub, Finset.sum_sub_distrib]
      ring
    rw [key]
    refine dvd_add (dvd_add (Finset.dvd_sum fun k _ => ?_) ?_) (hL i j n)
    · obtain ⟨e, he⟩ := dvd_sub_comm.mp (hL k j n)
      refine dvd_mul_of_dvd_right ⟨σ g e, ?_⟩ _
      rw [he, map_mul, map_pow, hσπ]
    · exact (pow_dvd_pow π (Nat.le_succ n)).trans ((hP n).2.2 g i j)
end GlobalTheory.InvariantLift
