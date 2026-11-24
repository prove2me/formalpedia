-- Prove2me | solution 1 for GlobalTheory.SplitDict.inversion_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:53:47.308878+00:00
-- url     : https://prove2.me/submissions/db017247-9991-4fae-8c46-6a79c8a55346

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_GL2CharacterZeros
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBoxInvariantSnd
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_fourier_inversion_pi
import Theorems.Thm_GlobalTheory_SplitWeil_measureReal_cball
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_mul
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_one
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi GlobalTheory.IndefiniteRowSideFullHecke.GLMatrixJoining
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitDict
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n] [DecidableEq n] {T : Type} [TopologicalSpace T] [T2Space T]
variable {ψ : AddChar k Circle} {c : kˣ}
variable [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.SplitDict
theorem _root_.solution (m : Measure k) [m.IsAddHaarMeasure] (h : HasConductor ψ c)
    {f : (n → k) → ℂ} (hf : f ∈ SB (n → k)) :
    ∫ y : n → k, (∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => m)) ∂(Measure.pi fun _ => m) =
      (((m.real (𝒪[k] : Set k) ^ 2 * nabs k c) ^ Fintype.card n : ℝ) : ℂ) * f 0 := by
  haveI := secondCountable k
  obtain ⟨s, hs⟩ := fourier_inversion_pi (Measure.pi fun _ : n => m) h hf
  have hbox : ∀ r : kˣ, (Measure.pi fun _ : n => m).real (box n r) =
      (nabs k r * m.real (𝒪[k] : Set k)) ^ Fintype.card n := by
    intro r
    have hc := measureReal_cball m r
    simp only [Measure.real] at hc ⊢
    rw [box, Measure.pi_pi, ENNReal.toReal_prod, hc, Finset.prod_const, Finset.card_univ]
  have h1 : nabs k s * nabs k (c * s⁻¹) = nabs k c := by
    rw [nabs_mul k, mul_left_comm, ← nabs_mul k, mul_inv_cancel, nabs_one k, mul_one]
  have h2 : nabs k s * m.real (𝒪[k] : Set k) * (nabs k (c * s⁻¹) * m.real (𝒪[k] : Set k)) =
      m.real (𝒪[k] : Set k) ^ 2 * nabs k c := by
    rw [← h1]; ring
  rw [hs, hbox, hbox, ← mul_pow, h2]
end GlobalTheory.SplitDict
