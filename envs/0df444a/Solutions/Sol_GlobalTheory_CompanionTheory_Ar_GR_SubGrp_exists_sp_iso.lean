-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.GR.SubGrp.exists_sp_iso
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:47:14.499308+00:00
-- url     : https://prove2.me/submissions/4756d60c-4224-46a6-a8a8-a34bbdb5a754

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_CommutativeAlgebra_IsFinFlatSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFlatSubgroupScheme

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.GR GlobalTheory.CompanionTheory.Ar.GR.SubGrp
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.Ar.GR.SubGrp
theorem _root_.solution (T : Over (Spec (CommRingCat.of R))) [IsAffine T.left] :
    ∃ (S : Type) (_ : CommRing S) (_ : Algebra R S) (j : sp (R₀ := R) S ⟶ T), IsIso j := by
  have hU := isAffineOpen_top T.left
  obtain ⟨ρ, hρ⟩ := Spec.map_surjective (hU.fromSpec ≫ T.hom)
  letI : Algebra R Γ(T.left, ⊤) := ρ.hom.toAlgebra
  let j : sp (R₀ := R) Γ(T.left, ⊤) ⟶ T := Over.homMk hU.fromSpec hρ.symm
  have : IsIso j.left := by
    change IsIso hU.fromSpec
    rw [IsAffineOpen.fromSpec_top]
    infer_instance
  have hj : IsIso ((Over.forget _).map j) := ‹IsIso j.left›
  exact ⟨Γ(T.left, ⊤), inferInstance, inferInstance, j, isIso_of_reflects_iso j (Over.forget _)⟩
end GlobalTheory.CompanionTheory.Ar.GR.SubGrp
