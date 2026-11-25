-- Prove2me | solution 1 for GlobalTheory.CompareIterDegree.iteration_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:16:08.365804+00:00
-- url     : https://prove2.me/submissions/747a3f63-f559-4080-ae0e-33efcb4f3f6e

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSFdeg
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_DegreeProportionalWords
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_GapSubsetOfSetBoundIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ENNReal
noncomputable section
open GlobalTheory GlobalTheory.CompareIterDegree
open Formalism.QuantumDeterminants Formalism.HermitianLatticeCounting.ExpansionTerms GlobalTheory.IndefiniteRowSideFullHecke.DegreeProportionalWords
namespace GlobalTheory.CompareIterDegree
theorem _root_.solution : IteratedHighestWeightBound ↔ Iteration := by
  constructor
  · intro h A V ι _ _ _ N M j D w lam R Γ hN hM hΓ hone L μ hμ
    have hsub : ∀ (P : A → ℝ), IsGauge P → ∀ x y, ⌈P (x + y)⌉₊ ≤ ⌈P x⌉₊ + ⌈P y⌉₊ := fun P hP x y =>
      (Nat.ceil_mono (hP.2 x y)).trans (Nat.ceil_add_le _ _)
    obtain ⟨a, ha, hb, hc⟩ := h V A ι j D w (fun x => ⌈N x⌉₊) (fun x => ⌈M x⌉₊) μ Γ 0 (wordWt w L) hΓ
      (hsub N hN) (hsub M hM) (by simp [hN.1]) (by simp [hM.1]) (by
        intro κ i hκ
        have h1 : N (κ - μ) ≤ (wordWt w L : ℝ) := Nat.ceil_le.1 (by simpa using hκ)
        have h2 := hN.2 (κ - μ) (μ - lam)
        rw [sub_add_sub_cancel] at h2
        obtain ⟨a, ha, hs, hl⟩ := hone i κ (by linarith)
        exact ⟨a, ha, hl, fun ν hν => ⟨Nat.ceil_le.2 (hs ν hν).1,
          Nat.ceil_le.2 (by simpa using (hs ν hν).2)⟩⟩) μ L (by simp [hN.1, wordWt])
    exact ⟨a, ha, fun ν hν => ⟨Nat.ceil_le.1 (hc ν hν).1, Nat.ceil_le.1 (hc ν hν).2⟩, hb⟩
  · intro h V P Λ _ _ _ jh Dop wt N1 Ninf lam Gam c0 q0 hG h1 h2 h3 h4 hone μ al hμ
    obtain ⟨a, ha, hs, hl⟩ := h P V Λ (fun x => (N1 x : ℝ)) (fun x => (Ninf x : ℝ)) jh Dop wt lam
      ((q0 : ℝ) - c0) Gam ⟨by simp [h3], fun x y => by beta_reduce; exact_mod_cast h1 x y⟩
      ⟨by simp [h4], fun x y => by beta_reduce; exact_mod_cast h2 x y⟩ hG (by
        intro i κ hκ
        have hκ' : N1 (κ - lam) + c0 ≤ q0 := by
          have : ((N1 (κ - lam) + c0 : ℕ) : ℝ) ≤ q0 := by push_cast; linarith
          exact_mod_cast this
        obtain ⟨a, ha, hl, hs⟩ := hone κ i hκ'
        exact ⟨a, ha, fun ν hν => ⟨by beta_reduce; exact_mod_cast (hs ν hν).1,
          by beta_reduce; exact_mod_cast (hs ν hν).2⟩, hl⟩)
      al μ (by
        have : ((N1 (μ - lam) + (al.map wt).sum + c0 : ℕ) : ℝ) ≤ q0 := by exact_mod_cast hμ
        rw [Nat.cast_add, Nat.cast_add] at this
        simp only [wordWt]
        linarith)
    exact ⟨a, ha, hl, fun ν hν => ⟨by have := (hs ν hν).1; simp only [wordWt] at this; exact_mod_cast this,
      Nat.cast_le.1 (hs ν hν).2⟩⟩
end GlobalTheory.CompareIterDegree
