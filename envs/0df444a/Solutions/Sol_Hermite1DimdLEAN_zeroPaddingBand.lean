-- Prove2me | solution 1 for Hermite1DimdLEAN.zeroPaddingBand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:42:24.358024+00:00
-- url     : https://prove2.me/submissions/69c65e47-7f78-4018-860b-ffa551851348

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_DegreeBookkeeping
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real



set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate
noncomputable section
open Hermite1DimdLEAN
namespace Hermite1DimdLEAN
theorem _root_.solution
    (N L : ℕ) (E : Finset ℕ) (b : ℕ → ℂ)
    (hE : ∀ n ∈ E, N ≤ n ∧ n < N + L) :
    ∃ c : Fin L → ℂ,
      positiveFrequencyPolynomial E b =
        bandLimitedPolynomial N L c := by
  /-
  Scaffolding guidance:
  this is the bridge from the finite degree set `S_j(G)` to the imported
  band-limited circle estimate.
  -/
  classical
  by_cases hL : L = 0
  · refine ⟨fun m => False.elim (by simpa [hL] using m.2), ?_⟩
    have hEempty : E = ∅ := by
      by_contra hne
      have hnonempty : E.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
      rcases hnonempty with ⟨n, hn⟩
      obtain ⟨_, hlt⟩ := hE n hn
      omega
    subst hEempty
    subst hL
    ext t
    simp [positiveFrequencyPolynomial, bandLimitedPolynomial]
  · let c : Fin L → ℂ := fun m => if N + m.1 ∈ E then b (N + m.1) else 0
    refine ⟨c, ?_⟩
    ext t
    have hfilter :
        (∑ m : Fin L, (if N + m.1 ∈ E then b (N + m.1) else 0) *
          fourier ((N + m.1 : ℕ) : ℤ) t) =
        Finset.sum (Finset.univ.filter fun m : Fin L => N + m.1 ∈ E)
          (fun m => b (N + m.1) * fourier ((N + m.1 : ℕ) : ℤ) t) := by
      simp_rw [ite_mul, zero_mul]
      rw [← Finset.sum_filter]
    rw [positiveFrequencyPolynomial, bandLimitedPolynomial, hfilter]
    symm
    refine Finset.sum_bij (fun m hm => N + m.1) ?_ ?_ ?_ ?_
    · simp_all
    · intro m₁ hm₁ m₂ hm₂ hEq
      exact Fin.ext (Nat.add_left_cancel hEq)
    · intro n hn
      obtain ⟨hlo, hhi⟩ := hE n hn
      refine ⟨⟨n - N, by omega⟩, ?_, ?_⟩
      · simp [hlo, hn]
      · simp_all
    · simp_all
end Hermite1DimdLEAN
