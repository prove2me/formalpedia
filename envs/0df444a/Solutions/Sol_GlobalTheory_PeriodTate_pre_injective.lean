-- Prove2me | solution 1 for GlobalTheory.PeriodTate.pre_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:02:05.590048+00:00
-- url     : https://prove2.me/submissions/f4f1b38f-8944-4ffd-af3b-b432bff57e6f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsTateIsoOfPeriods

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.PeriodTate
namespace GlobalTheory.PeriodTate
theorem _root_.solution {k : Type} [Field k] (β : ℂ →+* k) (A : Over (Sp ℂ)) :
    Function.Injective fun x : 𝟙_ (Over (Sp ℂ)) ⟶ A => toUnit (Over.mk (spMap β)) ≫ x := by
  intro x y h
  have e : (toUnit (Over.mk (spMap β))).left = spMap β := by
    simpa using Over.w (toUnit (Over.mk (spMap β)))
  have hf : Flat (spMap β) := by
    rw [Flat.SpecMap_iff]
    letI := β.toAlgebra
    exact (inferInstance : Module.Flat ℂ k)
  have hs : Surjective (spMap β) := ⟨fun p => ⟨default, Subsingleton.elim (α := PrimeSpectrum ℂ) _ _⟩⟩
  have : Epi (spMap β) := Flat.epi_of_flat_of_surjective _
  apply Over.OverMorphism.ext
  have h' := congrArg (fun z => z.left) h
  simp only [Over.comp_left, e] at h'
  exact (cancel_epi (spMap β)).1 h'
end GlobalTheory.PeriodTate
