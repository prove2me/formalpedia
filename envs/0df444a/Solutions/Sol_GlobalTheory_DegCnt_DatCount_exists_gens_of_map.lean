-- Prove2me | solution 1 for GlobalTheory.DegCnt.DatCount.exists_gens_of_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:13:22.64336+00:00
-- url     : https://prove2.me/submissions/9ff1e902-29df-47bd-9653-3242c4ea2b86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeQuotientGensAndIntermediateCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardEmbeddedDataWithGivenFixedLattice
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_Mass_LatticeGens_exists_gens_of_between
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.DatCount
variable {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
namespace GlobalTheory.DegCnt.DatCount
theorem _root_.solution [IsDedekindDomain R] (f : V →ₗ[R] W) (B : Submodule R V) (A : Submodule R W)
    (m : R) (hm : m ≠ 0) (T : Finset W) (hT : ∀ x ∈ T, m • x ∈ A)
    (hB : B.map f ≤ A ⊔ Submodule.span R (T : Set W)) :
    ∃ t : Finset V, t.card ≤ T.card ∧ B = (B ⊓ A.comap f) ⊔ Submodule.span R (t : Set V) := by
  obtain ⟨t', hc, ht'⟩ := GlobalTheory.Mass.LatticeGens.exists_gens_of_between A m hm T hT (A ⊔ B.map f) le_sup_left
    (sup_le le_sup_left hB)
  have h1 : ∀ w ∈ t', ∃ v ∈ B, w - f v ∈ A := by
    intro w hw
    have : w ∈ A ⊔ B.map f := by
      rw [ht']; exact Submodule.mem_sup_right (Submodule.subset_span hw)
    obtain ⟨a, ha, _, ⟨v, hv, rfl⟩, rfl⟩ := Submodule.mem_sup.1 this
    exact ⟨v, hv, by simpa using ha⟩
  choose! φ hφB hφA using h1
  have hsp : Submodule.span R ((t'.image φ : Finset V) : Set V) ≤ B := by
    rw [Submodule.span_le]
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hv
    exact hφB w hw
  refine ⟨t'.image φ, Finset.card_image_le.trans hc, le_antisymm (fun v hv => ?_) (sup_le inf_le_left hsp)⟩
  have h2 : A ⊔ B.map f ≤ A ⊔ (Submodule.span R ((t'.image φ : Finset V) : Set V)).map f := by
    rw [ht']
    refine sup_le le_sup_left (Submodule.span_le.2 fun w hw => ?_)
    have e : w = (w - f (φ w)) + f (φ w) := by abel
    rw [e]
    exact Submodule.add_mem_sup (hφA w hw)
      (Submodule.mem_map_of_mem (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem φ hw))))
  obtain ⟨a, ha, _, ⟨s, hs, rfl⟩, e⟩ :=
    Submodule.mem_sup.1 (h2 (Submodule.mem_sup_right (Submodule.mem_map_of_mem hv)))
  have e' : v = (v - s) + s := by abel
  rw [e']
  refine Submodule.add_mem_sup ⟨B.sub_mem hv (hsp hs), ?_⟩ hs
  change f (v - s) ∈ A
  rw [map_sub, ← e]
  simpa using ha
end GlobalTheory.DegCnt.DatCount
