-- Prove2me | solution 1 for GlobalTheory.SemiAbTorsion.finite_hom_range_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:58:44.485844+00:00
-- url     : https://prove2.me/submissions/e9908808-c5c3-46e0-b285-0e349235087b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_JacobsonClosedPointsToolsInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SemiAbelianTorsionFiniteAndClosedPointFiniteOrde
import Theorems.Thm_GlobalTheory_SemiAbTorsion_finite_ringHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.SemiAbTorsion
namespace GlobalTheory.SemiAbTorsion
theorem _root_.solution {X : Scheme.{0}} (π : X ⟶ Sp ℤ) [LocallyOfFiniteType π]
    (F : CommRingCat.{0}) [Finite F] (V : X.Opens) (hV : IsAffineOpen V) :
    {f : Spec F ⟶ X | Set.range f ⊆ V}.Finite := by
  have h : LocallyOfFiniteType (hV.fromSpec ≫ π) := inferInstance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hV.fromSpec ≫ π)
  rw [← hφ, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h
  have e : φ.hom = algebraMap ℤ Γ(X, V) := RingHom.ext_int _ _
  have h' : (algebraMap ℤ Γ(X, V)).FiniteType := e ▸ h
  have : Algebra.FiniteType ℤ Γ(X, V) := RingHom.finiteType_algebraMap.mp h'
  haveI := finite_ringHom Γ(X, V) F
  refine (Set.finite_range fun ψ : Γ(X, V) →+* F =>
    Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec).subset fun f hf => ?_
  have hf' : Set.range f ⊆ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hf
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (IsOpenImmersion.lift hV.fromSpec f hf')
  refine ⟨ψ.hom, ?_⟩
  change Spec.map ψ ≫ _ = _
  rw [hψ, IsOpenImmersion.lift_fac]
end GlobalTheory.SemiAbTorsion
