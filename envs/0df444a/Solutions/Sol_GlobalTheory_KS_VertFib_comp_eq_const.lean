-- Prove2me | solution 1 for GlobalTheory.KS.VertFib.comp_eq_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:28:28.166301+00:00
-- url     : https://prove2.me/submissions/88d5479e-27f2-4bdb-b9e3-f1f0b0a563cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GermDerivationIffDualNumberPointStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GermDerivationOfFibreOfKillsBase
import Theorems.Thm_GlobalTheory_KS_VertFib_ringVal_constFn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.VertFib
namespace GlobalTheory.KS.VertFib
theorem _root_.solution {R : Type} [CommRing R] (x₀ : R →+* ℂ) {X : Scheme.{0}} (p : X ⟶ Sp R)
    (v : Sp (DualNumber ℂ) ⟶ X) (h₁ : epsPt ≫ v ≫ p = spMap x₀)
    (h₂ : ∀ r, TrivSqZeroExt.snd (ringVal v ⊤ le_top (constFn p ⊤ r)) = 0) :
    v ≫ p = epsStr ≫ spMap x₀ := by
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (v ≫ p)
  have hφ : v ≫ p = spMap ψ.hom := hψ.symm
  rw [hφ, ← Spec.map_comp] at h₁
  have h₃ := Spec.map_injective h₁
  rw [hφ, ← Spec.map_comp]
  congr 1
  refine RingHom.ext fun r => ?_
  have h₄ : TrivSqZeroExt.snd (ψ.hom r : DualNumber ℂ) = 0 :=
    (congrArg TrivSqZeroExt.snd (ringVal_constFn v p ψ.hom hφ le_top r)).symm.trans (h₂ r)
  have h₅ : TrivSqZeroExt.fst (ψ.hom r : DualNumber ℂ) = x₀ r := congrArg (fun g => g.hom r) h₃
  exact TrivSqZeroExt.ext h₅ h₄
end GlobalTheory.KS.VertFib
