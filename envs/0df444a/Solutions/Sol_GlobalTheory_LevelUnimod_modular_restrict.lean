-- Prove2me | solution 1 for GlobalTheory.LevelUnimod.modular_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:22:52.179205+00:00
-- url     : https://prove2.me/submissions/649fdb85-aaab-4a67-8aef-8c3069a6725e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsMulLeftInvariantVolGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_GlCharacterEqOneOfTransposeInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsUnimodularBlockUpperTriangularSymmetricLevels
import Theorems.Thm_GlobalTheory_LevelUnimod_modular_aut

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open scoped Topology
open GlobalTheory GlobalTheory.LevelUnimod
namespace GlobalTheory.LevelUnimod
theorem _root_.solution {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (S : Subgroup G)
    [LocallyCompactSpace S] [SecondCountableTopology S] [MeasurableSpace S] [BorelSpace S]
    (E : G ≃* G) (hc : Continuous E) (hc' : Continuous E.symm) (h1 : ∀ g ∈ S, E g ∈ S)
    (h2 : ∀ g ∈ S, E.symm g ∈ S) (g g' : S) (h : (g' : G) = E g) :
    Measure.modularCharacter g' = Measure.modularCharacter g := by
  let e : S ≃* S :=
    { toFun := fun x => ⟨E x, h1 x x.2⟩
      invFun := fun x => ⟨E.symm x, h2 x x.2⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp) }
  have : g' = e g := Subtype.ext h
  rw [this]
  exact modular_aut e (Continuous.subtype_mk (hc.comp continuous_subtype_val) _)
    (Continuous.subtype_mk (hc'.comp continuous_subtype_val) _) g
end GlobalTheory.LevelUnimod
