-- Prove2me | solution 1 for GlobalTheory.Mass.PrimDisc.gens_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:53:00.738878+00:00
-- url     : https://prove2.me/submissions/05d7918d-960e-4ae7-957a-58ad755e9e37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionTotallyDefiniteHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodulaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeQuotientGensAndIntermediateCountStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimitiveHermitianSublatticeDiscriminantGenerato
import Theorems.Thm_GlobalTheory_Mass_PrimDisc_latIn_le

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
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.PrimDisc
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
omit [StarRing K] [FiniteDimensional K V] [NumberField K]
namespace GlobalTheory.Mass.PrimDisc
theorem _root_.solution (A B : Submodule K V) (p : V →ₗ[K] A) (q : V →ₗ[K] B)
    (hp : ∀ a : A, p a = a) (hpq : ∀ x, (p x : V) + q x = x) (L : Submodule (𝓞 K) V) (t : Finset B)
    (ht : L.map (q.restrictScalars (𝓞 K)) = latIn B L ⊔ Submodule.span (𝓞 K) (t : Set B)) :
    ∃ t' : Finset A, t'.card ≤ t.card ∧
      L.map (p.restrictScalars (𝓞 K)) = latIn A L ⊔ Submodule.span (𝓞 K) (t' : Set A) := by
  have hl : ∀ b : t, ∃ l ∈ L, q l = b := fun b => by
    have : (b : B) ∈ L.map (q.restrictScalars (𝓞 K)) := by
      rw [ht]
      exact Submodule.mem_sup_right (Submodule.subset_span b.2)
    exact this
  choose f hf1 hf2 using hl
  refine ⟨Finset.univ.image fun b => p (f b), Finset.card_image_le.trans (by simp), ?_⟩
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hq : q x ∈ latIn B L ⊔ Submodule.span (𝓞 K) (t : Set B) := ht ▸ ⟨x, hx, rfl⟩
    have e : (t : Set B) = (q.restrictScalars (𝓞 K)) '' Set.range f := by
      ext b
      constructor
      · intro hb
        exact ⟨f ⟨b, hb⟩, ⟨_, rfl⟩, hf2 _⟩
      · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
        have : q (f c) ∈ t := by rw [hf2]; exact c.2
        exact this
    rw [e, ← Submodule.map_span] at hq
    obtain ⟨s, hs, _, ⟨y, hy, rfl⟩, hsy⟩ := Submodule.mem_sup.1 hq
    have hyL : y ∈ L := (Submodule.span_le.2 (by rintro _ ⟨c, rfl⟩; exact hf1 c)) hy
    refine Submodule.mem_sup.2 ⟨p (x - y), ?_, p y, ?_, by simp⟩
    · have e1 : q (x - y) = s := by
        rw [map_sub, ← hsy]; simp
      have e2 := hpq (x - y)
      rw [e1] at e2
      change (p (x - y) : V) ∈ L
      rw [eq_sub_of_add_eq e2]
      exact L.sub_mem (L.sub_mem hx hyL) hs
    · have : p y ∈ (Submodule.span (𝓞 K) (Set.range f)).map (p.restrictScalars (𝓞 K)) := ⟨y, hy, rfl⟩
      rw [Submodule.map_span, ← Set.range_comp] at this
      simpa [Function.comp_def] using this
  · refine sup_le (latIn_le A p hp L) (Submodule.span_le.2 ?_)
    intro a ha
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ] at ha
    obtain ⟨b, rfl⟩ := ha
    exact ⟨f b, hf1 b, rfl⟩
end GlobalTheory.Mass.PrimDisc
