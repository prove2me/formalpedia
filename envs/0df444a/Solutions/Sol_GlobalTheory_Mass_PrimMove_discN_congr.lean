-- Prove2me | solution 1 for GlobalTheory.Mass.PrimMove.discN_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:31:11.602941+00:00
-- url     : https://prove2.me/submissions/27cde410-8433-4b3a-8b77-6879fcc6ef69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimitiveSublatticesMoveWithIsometries

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
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.PrimMove
variable {R K : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
namespace GlobalTheory.Mass.PrimMove
theorem _root_.solution {V W : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    [AddCommGroup W] [Module K W] [Module R W] [IsScalarTower R K W]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (k : W →ₗ⋆[K] W →ₗ[K] K) (e : V ≃ₗ[K] W)
    (he : ∀ x y, k (e x) (e y) = h x y) (A : Submodule R V) (B : Submodule R W)
    (hAB : ∀ x, e x ∈ B ↔ x ∈ A) : discN k B = discN h A := by
  have hd : ∀ x, e x ∈ dual k B ↔ x ∈ dual h A := by
    intro x
    unfold dual Formalism.E.hdual
    simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
    constructor
    · intro H y hy
      rw [← he]
      exact H _ ((hAB y).2 hy)
    · intro H y hy
      obtain ⟨z, rfl⟩ := e.surjective y
      rw [he]
      exact H _ ((hAB z).1 hy)
  have hm : ∀ (A : Submodule R V) (B : Submodule R W), (∀ x, e x ∈ B ↔ x ∈ A) →
      B.toAddSubgroup = A.toAddSubgroup.map (e : V →+ W) := by
    intro A B H
    ext y
    obtain ⟨z, rfl⟩ := e.surjective y
    constructor
    · intro hy
      exact ⟨z, (H z).1 hy, rfl⟩
    · rintro ⟨w, hw, hwz⟩
      have : e w = e z := hwz
      rw [← this]
      exact (H w).2 hw
  unfold discN idxN
  rw [hm A B hAB, hm _ _ hd]
  exact AddSubgroup.relIndex_map_map_of_injective (f := (e : V →+ W)) _ _ e.injective
end GlobalTheory.Mass.PrimMove
