-- Prove2me | solution 1 for GlobalTheory.Mass.ProdMass.wt_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:30:25.969908+00:00
-- url     : https://prove2.me/submissions/55bab3ba-8ebf-4126-8cb5-b1dee1797e43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitStabilizerMassProdEqMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.ProdMass
namespace GlobalTheory.Mass.ProdMass
theorem _root_.solution (G : Type) [Group G] {α : Type} [MulAction G α] (X : Set α) (hX : Stable G X)
    {x y : α} (h : MulAction.orbitRel G α x y) : wt G X x = wt G X y := by
  have hc : ENat.card (MulAction.stabilizer G x) = ENat.card (MulAction.stabilizer G y) :=
    ENat.card_congr (MulAction.stabilizerEquivStabilizerOfOrbitRel h).toEquiv
  obtain ⟨g, hg⟩ := h
  simp only at hg
  have hm : x ∈ X ↔ y ∈ X := by
    constructor
    · intro hx
      have := hX g⁻¹ x hx
      rwa [← hg, inv_smul_smul] at this
    · intro hy
      rw [← hg]; exact hX g y hy
  unfold wt
  rw [hc]
  simp only [hm]
end GlobalTheory.Mass.ProdMass
