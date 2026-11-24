-- Prove2me | solution 1 for Hermite1DimdLEAN.zeroFrequencyAbsent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:42:27.246317+00:00
-- url     : https://prove2.me/submissions/f283ee9b-b1ec-4d5b-bb55-1e6ebf9a84e3

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_DegreeBookkeeping
public import Theorems.Thm_Hermite1DimdLEAN_orthogonalToNu_iff_coeff_zero
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
    {d : ℕ} (κ : MultiIndex d) (j : MultiIndex d) (M : ℕ) (G : FiniteHermiteSum d)
    (horth : hermiteInnerNu κ G = 0) :
    0 ∉ localDegreeSet j M G := by
  /-
  Scaffolding guidance:
  this standalone lemma is what licenses the positive-frequency circle estimate
  on low annuli.
  -/
  classical
  have hcoeff0 : G.coeff 0 = 0 := (orthogonalToNu_iff_coeff_zero κ G).mp horth
  have hzero_support : (0 : MultiIndex d) ∉ G.support := by
    simpa [FiniteHermiteSum.support, Finsupp.mem_support_iff] using hcoeff0
  intro h0
  rcases Finset.mem_image.mp h0 with ⟨α, hαloc, hαdeg⟩
  have hcoord0 : ∀ q : Fin d, α q = 0 := by
    intro q
    have hle : α q ≤ totalDegree α := by
      dsimp [totalDegree]
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simp)
    omega
  have hαzero : α = 0 := funext hcoord0
  have hαsupp : α ∈ G.support := (Finset.mem_filter.mp hαloc).1
  exact hzero_support (hαzero ▸ hαsupp)
end Hermite1DimdLEAN
