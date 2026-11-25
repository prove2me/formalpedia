-- Prove2me | solution 1 for GlobalTheory.AbLaw.secOn_finitePresentation_projective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:13:51.889197+00:00
-- url     : https://prove2.me/submissions/0e0eb91f-3c69-4546-b87c-4f83a583396f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SecOnBasicOpenLocalization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SecOnFinitePresentationProjective
import Theorems.Thm_GlobalTheory_AbLaw_SecOn_isLocalizedModule_chartBasicOpen
import Theorems.Thm_GlobalTheory_Descent_flat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
open GlobalTheory GlobalTheory.AbLaw
variable {Y : Scheme.{0}} {M : LB Y} {V : Y.Opens}
namespace GlobalTheory.AbLaw
theorem _root_.solution :
    ∀ (Y : Scheme.{0}) (M : LB Y) (V : Y.Opens), M.IsLB → IsAffineOpen V → Module.FinitePresentation Γ(Y, V) (SecOn M V) ∧ Module.Projective Γ(Y, V) (SecOn M V) := by
  intro Y M V hM hV
  let s : Set Γ(Y, V) := {a | ∃ i, Y.basicOpen a ≤ M.U i}
  have hs : Ideal.span s = ⊤ := by
    rw [← hV.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hM.cover.ge (Set.mem_univ x))
    obtain ⟨f, hf, hxf⟩ := hV.exists_basicOpen_le ⟨x, hi⟩ hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨f, i, hf⟩, hxf⟩
  choose c hc using fun g : s => g.2
  have hl (g : s) := hV.isLocalization_basicOpen g.1
  have hm (g : s) := SecOn.isLocalizedModule_chartBasicOpen hM hV (c g) g.1 (hc g)
  have hfp : Module.FinitePresentation Γ(Y, V) (SecOn M V) :=
    Module.FinitePresentation.of_localizationSpan' s hs
      (Rₚ := fun g => Γ(Y, Y.basicOpen g.1))
      (fun g => SecOn.chartBasicOpen hM (c g) g.1 (hc g)) fun _ => inferInstance
  have hfl : Module.Flat Γ(Y, V) (SecOn M V) :=
    Module.flat_of_isLocalized_span Γ(Y, V) (SecOn M V) s hs (fun g => Γ(Y, Y.basicOpen g.1))
      (fun g => SecOn.chartBasicOpen hM (c g) g.1 (hc g))
      fun g => IsLocalization.flat _ (Submonoid.powers g.1)
  exact ⟨hfp, Module.Flat.projective_of_finitePresentation⟩
end GlobalTheory.AbLaw
