-- Prove2me | solution 1 for GlobalTheory.SectionKernel.mem_map_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:37:32.078825+00:00
-- url     : https://prove2.me/submissions/06ce98cd-3e6a-4b43-89f6-8f3363e99e3b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSectionEqMulOfVanishingModElement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SectionKernel
namespace GlobalTheory.SectionKernel
theorem _root_.solution {R B : Type} [CommRing R] [CommRing B] (c : R →+* B) (hf : c.Flat)
    {I : Ideal R} {ε : R} (h : ∀ x, ε * x = 0 → x ∈ I) (b : B) (hb : c ε * b = 0) :
    b ∈ I.map c := by
  letI := c.toAlgebra
  haveI : Module.Flat R B := hf
  obtain ⟨l, d, y, hy, hc⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := R) (M := B)
    (f := fun _ : Unit => ε) (x := fun _ => b)
    (by rw [Fintype.sum_unique, Algebra.smul_def]; exact hb)
  have : b = ∑ j, d () j • y j := hy ()
  rw [this]
  refine Ideal.sum_mem _ fun j _ => ?_
  rw [Algebra.smul_def]
  refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem c (h _ ?_))
  have h := hc j
  rwa [Fintype.sum_unique] at h
end GlobalTheory.SectionKernel
