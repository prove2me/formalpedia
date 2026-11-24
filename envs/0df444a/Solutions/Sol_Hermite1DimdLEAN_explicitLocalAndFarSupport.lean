-- Prove2me | solution 1 for Hermite1DimdLEAN.explicitLocalAndFarSupport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:04:33.348827+00:00
-- url     : https://prove2.me/submissions/a3d83388-d002-4f53-984f-d26f57cd9e79

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_MissingMathlib
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_BlockLocalization
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
    {d : ℕ} (j : MultiIndex d) (M : ℕ) (G : FiniteHermiteSum d) :
    Disjoint (localCoeffSet j M G) (farCoeffSet j M G) ∧
      localCoeffSet j M G ∪ farCoeffSet j M G = G.support ∧
      (localPart j M G).support = localCoeffSet j M G ∧
      (remainderPart j M G).support = farCoeffSet j M G := by
  /-
  Scaffolding guidance:
  later files need the explicit finite sets, not an opaque decomposition lemma.
  This is where regrouping by total degree starts.
  -/
  classical
  have hdisj : Disjoint (localCoeffSet j M G) (farCoeffSet j M G) := by
    refine Finset.disjoint_left.mpr fun α hlocal hfar => ?_
    exact absurd (Finset.mem_filter.mp hfar).2 (not_lt_of_ge (Finset.mem_filter.mp hlocal).2)
  have hunion : localCoeffSet j M G ∪ farCoeffSet j M G = G.support := by
    ext α
    simp only [localCoeffSet, farCoeffSet, mem_union, mem_filter]
    constructor
    · rintro (⟨hsupp, _⟩ | ⟨hsupp, _⟩) <;> exact hsupp
    · intro hsupp
      by_cases hlocal : blockDistance j (blockIndexMulti α) ≤ M
      · exact Or.inl ⟨hsupp, hlocal⟩
      · exact Or.inr ⟨hsupp, Nat.lt_of_not_ge hlocal⟩
  have hlocal_support : (localPart j M G).support = localCoeffSet j M G := by
    ext α
    simp [FiniteHermiteSum.support, localPart, localCoeffSet, Finsupp.mem_support_iff, and_comm]
  have hfar_support : (remainderPart j M G).support = farCoeffSet j M G := by
    ext α
    simp [FiniteHermiteSum.support, remainderPart, farCoeffSet, Finsupp.mem_support_iff, and_comm]
  exact ⟨hdisj, hunion, hlocal_support, hfar_support⟩
end Hermite1DimdLEAN
