-- Prove2me | solution 1 for OAI.KervaireRibbon.OuterRibbon.value_base
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:41:01.729059+00:00
-- url     : https://prove2.me/submissions/7da54170-f96e-41f3-b8a8-999d5faa1746

import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralMeasures
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralLogarithm
import Definitions.Def_OAI_GroupTheory_Kervaire_ScalarPhase
import Definitions.Def_OAI_GroupTheory_Kervaire_TraceCalculus
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralApproximation
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseSubadditivity
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseNaturality
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseGrids
import Definitions.Def_OAI_GroupTheory_Kervaire_RegularOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixTrace
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixShifts
import Definitions.Def_OAI_GroupTheory_Kervaire_WeightedCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseFaithfulness
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseDimension
import Definitions.Def_OAI_GroupTheory_Kervaire_MixingOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_HaarCurrents
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentPullback
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceSpaces
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceTangent
import Definitions.Def_OAI_GroupTheory_Kervaire_UnitaryHomotopy
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceDegree
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentExistence
import Definitions.Def_OAI_GroupTheory_Kervaire_SignedIncidence
import Definitions.Def_OAI_GroupTheory_Kervaire_FixedSpaces
import Definitions.Def_OAI_GroupTheory_Kervaire_Traversal
import Definitions.Def_OAI_GroupTheory_Kervaire_BoundaryFlow
import Definitions.Def_OAI_GroupTheory_Kervaire_RelatorRigidity
import Definitions.Def_OAI_GroupTheory_Kervaire_VertexJoin
import Definitions.Def_OAI_GroupTheory_Kervaire_Circles
import Definitions.Def_OAI_GroupTheory_Kervaire_Splicing
import Definitions.Def_OAI_GroupTheory_Kervaire_Capping
import Definitions.Def_OAI_GroupTheory_Kervaire_OuterRibbon
import Definitions.Def_OAI_GroupTheory_Kervaire_RibbonProducts
import Definitions.Def_OAI_GroupTheory_Kervaire_Conjugation
import Definitions.Def_OAI_GroupTheory_Kervaire_Inversion
import Definitions.Def_OAI_GroupTheory_Kervaire_Realization
import Definitions.Def_OAI_GroupTheory_Kervaire_Annulus

open OAI OAI.KervaireRibbon
open Equiv Equiv.Perm Monoid Multiplicative
open scoped Classical
variable {I A : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [Group A]


theorem solution (ρ : Perm I) (hρ : ∀ i j, ρ.SameCycle i j) (a : I → A)
    (s : I → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1) (i : I) (l : List I)
    (hc : Circle ρ i l) (hn : (i::l).Nodup) (hcover : ∀ j, j ∈ i::l) :
    (OuterRibbon.base ρ hρ a s hs i l hc hn hcover).value = dartEval s a (i::l) := by
  have hcorner : ∀ j : I, corner (markAnnulus ρ i) (pairing.sumCongr (1 : Perm (PUnit : Type)))
      (basePotential ρ a i) (Sum.inl (Sum.inr j)) = a j := by
    intro j
    simp only [corner, markAnnulus_outside]
    by_cases h : ρ j = i
    · subst h; simp [basePotential, pairing]
    · simp [h, basePotential, pairing]
  have hm : corner (markAnnulus ρ i) (pairing.sumCongr (1 : Perm (PUnit : Type)))
      (basePotential ρ a i) (Sum.inr PUnit.unit) = 1 := by
    simp only [corner, markAnnulus_marker]; simp [basePotential]
  change dartEval (baseSign s) (corner (markAnnulus ρ i) (pairing.sumCongr (1 : Perm (PUnit : Type)))
      (basePotential ρ a i)) (Sum.inr PUnit.unit :: (i::l).map (fun j ↦ Sum.inl (Sum.inr j))) = _
  rw [dartEval_cons]
  have h1 : dartLetter (baseSign s) (corner (markAnnulus ρ i) (pairing.sumCongr (1 : Perm (PUnit : Type)))
      (basePotential ρ a i)) (Sum.inr PUnit.unit) = 1 := by
    simp only [dartLetter, hm]; simp [baseSign]
  rw [h1, one_mul]
  unfold dartEval
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro j _
  simp only [Function.comp, dartLetter, hcorner]
  rfl

