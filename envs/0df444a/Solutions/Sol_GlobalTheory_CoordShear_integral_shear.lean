-- Prove2me | solution 1 for GlobalTheory.CoordShear.integral_shear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:46:53.927202+00:00
-- url     : https://prove2.me/submissions/4700dc8a-36f8-4f77-bd5c-74dfc41fd0a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IntegralCoordinateShearHaarLocalField
import Theorems.Thm_GlobalTheory_CoordShear_measurePreserving_shear
import Theorems.Thm_GlobalTheory_StepData_IntM_add
import Theorems.Thm_GlobalTheory_StepData_MaxM_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
open GlobalTheory GlobalTheory.CoordShear
namespace GlobalTheory.CoordShear
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (J : Type) [Fintype J] [DecidableEq J] (S : Finset J) (g : (J → k) → (J → k)), Continuous g → (∀ y y' : J → k, (∀ j, j ∉ S → y j = y' j) → g y = g y') → (∀ (y : J → k) j, j ∉ S → g y j = 0) → ∀ F : (J → k) → ℂ, ∫ y, F (y + g y) ∂(Measure.pi fun _ => ν) = ∫ y, F y ∂(Measure.pi fun _ => ν) := by
  intro k _ _ _ _ _ _ ν hν J _ _ S g hg h1 h2 F

  have : SecondCountableTopology k := by
    let := IsTopologicalAddGroup.rightUniformSpace k
    have := isUniformAddGroup_of_addCommGroup (G := k)
    let : (Valued.v (R := k)).RankOne :=
      { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
        strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
          MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
    let : NontriviallyNormedField k := Valued.toNontriviallyNormedField k (ValueGroupWithZero k)
    have : ProperSpace k := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k
    exact secondCountable_of_proper
  have := hν
  have hgm : Measurable g := hg.measurable
  have hmp := measurePreserving_shear ν S g hgm h1 h2
  have hfix : ∀ y, g (y + g y) = g y := fun y => h1 _ _ fun j hj => by simp [h2 y j hj]
  have hfix' : ∀ y, g (y - g y) = g y := fun y => h1 _ _ fun j hj => by simp [h2 y j hj]
  have hsurj : Function.Surjective (fun y : J → k => y + g y) :=
    fun y => ⟨y - g y, by simp [hfix']⟩
  have hemb : MeasurableEmbedding (fun y : J → k => y + g y) :=
    MeasurableEmbedding.of_measurable_inverse (g := fun y => y - g y) (measurable_id.add hgm)
      (by rw [hsurj.range_eq]; exact MeasurableSet.univ) (measurable_id.sub hgm)
      (fun y => by simp [hfix])
  exact hmp.integral_comp hemb F
end GlobalTheory.CoordShear
