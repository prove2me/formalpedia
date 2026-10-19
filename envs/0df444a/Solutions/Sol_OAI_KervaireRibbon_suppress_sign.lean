-- Prove2me | solution 1 for OAI.KervaireRibbon.suppress_sign
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:34:13.795994+00:00
-- url     : https://prove2.me/submissions/17e463a7-10d6-4aef-974a-78f716614c73

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

open OAI OAI.KervaireRibbon
open Equiv Equiv.Perm
open scoped Classical
variable {D A : Type*} [Fintype D] [DecidableEq D] [Group A]


omit [Fintype D] in
theorem solution (θ : Perm D) (hθ : ∀ d, θ (θ d) = d)
    (t : D → ℤ) (ht : ∀ d, t (θ d) = -t d)
    {x y : D} (hxy : x ≠ y) (hx : θ x ≠ x) (hy : θ y ≠ y) (hpair : t y = -t x) :
    ∀ d, capSign t x y (suppress θ x y d) = - capSign t x y d := by
  intro d
  have hs : ∀ d, suppress θ x y d = swap x y (swap y (θ x) (θ (swap y (θ x) d))) := by
    intro d; rfl
  have hxa : x ≠ θ x := fun h => hx h.symm
  have hsx : suppress θ x y x = x := by
    rw [hs, swap_apply_of_ne_of_ne hxy hxa, swap_apply_right, swap_apply_right]
  have hsy : suppress θ x y y = y := by
    rw [hs, swap_apply_left, hθ, swap_apply_of_ne_of_ne hxy hxa, swap_apply_left]
  by_cases hdx : d = x
  · subst hdx; rw [hsx]; simp [capSign]
  by_cases hdy : d = y
  · subst hdy; rw [hsy]; simp [capSign]
  have hinj := (suppress θ x y).injective
  have h1 : suppress θ x y d ≠ x := fun e => hdx (hinj (e.trans hsx.symm))
  have h2 : suppress θ x y d ≠ y := fun e => hdy (hinj (e.trans hsy.symm))
  simp only [capSign, h1, h2, hdx, hdy, or_self, if_false]
  by_cases hda : d = θ x
  · subst hda
    have hb1 : θ y ≠ y := hy
    have hb2 : θ y ≠ θ x := fun e => hxy (θ.injective e).symm
    have hb3 : θ y ≠ x := fun e => hdy (by rw [← e, hθ])
    rw [hs, swap_apply_right, swap_apply_of_ne_of_ne hb1 hb2, swap_apply_of_ne_of_ne hb3 hb1, ht, ht]
    linarith
  rw [hs, swap_apply_of_ne_of_ne hdy hda]
  by_cases hey : θ d = y
  · have hay : θ x ≠ y := fun e => hdx (θ.injective (hey.trans e.symm))
    rw [hey, swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm hxa) hay, ht]
    have := ht d; rw [hey] at this; linarith
  have hea : θ d ≠ θ x := fun e => hdx (θ.injective e)
  have hex : θ d ≠ x := fun e => hda (by rw [← e, hθ])
  rw [swap_apply_of_ne_of_ne hey hea, swap_apply_of_ne_of_ne hex hey, ht]

