-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyBoxSpectral.forwardFace_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.72687+00:00
-- url     : https://prove2.me/submissions/996486c2-5c06-470b-a09f-4d79142cf0c0

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyBoxSpectral_boxVertex_card
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyBoxSpectral_upperFace_card

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators Matrix Topology
open MetricCodes.Spherical.HigherHierarchyBoxSpectral
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherChannel
namespace MetricCodes.Spherical.HigherHierarchyBoxSpectral
theorem _root_.solution {r m : ℕ} (i : Fin (r + 1)) :
    ((Finset.univ : Finset (BoxVertex r m)).filter
      (fun v => (v i).val < m)).card = m * (m + 1) ^ r := by
  classical
  have hcomplement :
      ((Finset.univ : Finset (BoxVertex r m)).filter
        (fun v => v i = Fin.last m)).card +
        ((Finset.univ : Finset (BoxVertex r m)).filter
          (fun v => ¬ v i = Fin.last m)).card =
          (Finset.univ : Finset (BoxVertex r m)).card :=
    Finset.card_filter_add_card_filter_not _
  have hfilter :
      (Finset.univ : Finset (BoxVertex r m)).filter
          (fun v => ¬ v i = Fin.last m) =
        (Finset.univ : Finset (BoxVertex r m)).filter
          (fun v => (v i).val < m) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hne
      have hle := (v i).isLt
      have hval : (v i).val ≠ m := by
        intro heq
        exact hne (Fin.ext heq)
      omega
    · intro hlt heq
      have hval := congrArg Fin.val heq
      simp at hval
      omega
  rw [upperFace_card, hfilter] at hcomplement
  have hfull :
      (Finset.univ : Finset (BoxVertex r m)).card =
        (m + 1) ^ (r + 1) := boxVertex_card r m
  rw [hfull] at hcomplement
  have hfactor :
      (m + 1) ^ (r + 1) =
        (m + 1) ^ r + m * (m + 1) ^ r := by
    rw [pow_succ]
    ring
  omega
end MetricCodes.Spherical.HigherHierarchyBoxSpectral
