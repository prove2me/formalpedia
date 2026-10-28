-- Prove2me | solution 1 for ImpulsiveISS.SmallGain.jump_estimate
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:31:14.445504+00:00
-- url     : https://prove2.me/submissions/f37c75b3-8c84-4164-95f5-081127bb8bfa

import Mathlib
import Definitions.Def_SmallGainISS_Lyapunov_Gains
import Definitions.Def_ProcessingNetworks_LyapunovCriteria_DiniDerivative
import Definitions.Def_ImpulsiveISS_SmallGain_System
import Definitions.Def_ImpulsiveISS_SmallGain_Interconnection
open scoped NNReal
open SmallGainISS.Lyapunov ProcessingNetworks.LyapunovCriteria

open ImpulsiveISS.SmallGain in
theorem solution {n : ℕ} {Xi : Fin n → Type*} [∀ i, NormedAddCommGroup (Xi i)]
    [∀ i, NormedSpace ℝ (Xi i)] [∀ i, CompleteSpace (Xi i)]
    {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
    (S : ImpulsiveSystem ((i : Fin n) → Xi i) U)
    (V : (i : Fin n) → Xi i → ℝ≥0) (ψ₁ ψ₂ : Fin n → ℝ≥0 → ℝ≥0)
    (χ : Fin n → Fin n → ℝ≥0 → ℝ≥0) (χu : Fin n → ℝ≥0 → ℝ≥0) (φ α : Fin n → ℝ≥0 → ℝ≥0)
    (hV : IsSubsystemISSLyapunov S V ψ₁ ψ₂ χ χu φ α)
    (σ : ℝ≥0 → Fin n → ℝ≥0) (τ : Fin n → ℝ≥0 → ℝ≥0) (hσ : IsOmegaPath (gainOp χ) σ τ)
    (αstar : ℝ≥0 → ℝ≥0) (hαstar : IsK αstar) (hαstar_ge : ∀ r, alphaTilde σ τ α r ≤ αstar r) :
    ∀ (x : (i : Fin n) → Xi i) (ξ : U),
      smallGainV τ V (S.jump x ξ) ≤
        max (αstar (smallGainV τ V x)) (max (etaGain σ τ χ (smallGainV τ V x)) (smallGainChi τ χu ‖ξ‖₊)) := by
  intro x ξ
  have hσmono : ∀ i, StrictMono (fun r => σ r i) := fun i => (hσ.2.1 i).1.2.1
  have hσ0 : ∀ i, σ 0 i = 0 := fun i => (hσ.2.1 i).1.2.2
  have hτσ : ∀ i r, τ i (σ r i) = r := fun i r => (hσ.2.2.1 i).1 r
  have hστ : ∀ i v, σ (τ i v) i = v := fun i v => (hσ.2.2.1 i).2 v
  have hτmono : ∀ i, Monotone (τ i) := by
    intro i a b hab
    by_contra h
    push Not at h
    have := hσmono i h
    simp only [hστ] at this
    exact absurd hab (not_le.mpr this)
  have hτ0 : ∀ i, τ i 0 = 0 := fun i => by
    have := hτσ i 0
    rwa [hσ0 i] at this
  have hαmono : Monotone αstar := hαstar.2.1.monotone
  have hχmono : ∀ i j, Monotone (χ i j) := by
    intro i j
    by_cases hij : i = j
    · subst hij; rw [hV.2.2.2.2.1 i]; exact fun _ _ _ => le_rfl
    · exact (hV.2.2.2.1 i j hij).2.1.monotone
  set r := smallGainV τ V x with hr
  have hs : ∀ i, τ i (V i (x i)) ≤ r := fun i =>
    Finset.le_sup (f := fun i => τ i (V i (x i))) (Finset.mem_univ i)
  unfold smallGainV
  refine Finset.sup_le fun i _ => ?_
  have hjump := hV.2.2.2.2.2.2.2.2.2 i x ξ
  refine ((hτmono i) hjump).trans ?_
  rw [(hτmono i).map_max, (hτmono i).map_max]
  refine max_le_max ?_ (max_le_max ?_ ?_)
  · -- α term
    have e : V i (x i) = σ (τ i (V i (x i))) i := (hστ i _).symm
    calc τ i (α i (V i (x i))) = τ i (α i (σ (τ i (V i (x i))) i)) := by rw [← e]
      _ ≤ alphaTilde σ τ α (τ i (V i (x i))) :=
          Finset.le_sup (f := fun i' => τ i' (α i' (σ (τ i (V i (x i))) i'))) (Finset.mem_univ i)
      _ ≤ αstar (τ i (V i (x i))) := hαstar_ge _
      _ ≤ αstar r := hαmono (hs i)
  · -- χ term
    obtain ⟨j0, -, hj0⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin n))
      ⟨i, Finset.mem_univ i⟩ (fun j => χ i j (V j (x j)))
    rw [hj0]
    by_cases hij : j0 = i
    · subst hij
      rw [hV.2.2.2.2.1 j0]
      simp [hτ0]
    · have hVj : V j0 (x j0) ≤ σ r j0 := by
        rw [← hστ j0 (V j0 (x j0))]
        exact (hσmono j0).monotone (hs j0)
      calc τ i (χ i j0 (V j0 (x j0))) ≤ τ i (χ i j0 (σ r j0)) :=
            hτmono i (hχmono i j0 hVj)
        _ ≤ (Finset.univ.filter fun j => j ≠ i).sup fun j => τ i (χ i j (σ r j)) :=
            Finset.le_sup (f := fun j => τ i (χ i j (σ r j)))
              (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩)
        _ ≤ etaGain σ τ χ r :=
            Finset.le_sup (f := fun i' => (Finset.univ.filter fun j => j ≠ i').sup
              fun j => τ i' (χ i' j (σ r j))) (Finset.mem_univ i)
  · -- input term
    exact Finset.le_sup (f := fun i' => τ i' (χu i' ‖ξ‖₊)) (Finset.mem_univ i)
