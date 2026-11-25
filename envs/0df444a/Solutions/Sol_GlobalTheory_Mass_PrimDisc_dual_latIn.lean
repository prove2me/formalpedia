-- Prove2me | solution 1 for GlobalTheory.Mass.PrimDisc.dual_latIn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:12:23.281118+00:00
-- url     : https://prove2.me/submissions/12b2237f-15de-4e5f-9685-509da06c2c8b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionTotallyDefiniteHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodulaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeQuotientGensAndIntermediateCountStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimitiveHermitianSublatticeDiscriminantGenerato
import Theorems.Thm_GlobalTheory_Mass_PrimDisc_mem_dual
import Theorems.Thm_GlobalTheory_Mass_PrimDisc_star_range
import Theorems.Thm_GlobalTheory_Mass_PrimDisc_nondeg
import Theorems.Thm_GlobalTheory_Mass_PrimDisc_lat_map
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualLattice


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
namespace GlobalTheory.Mass.PrimDisc
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) (hp : PD h) (A : Submodule K V)
    (hsA : (hRes h A).IsSymm) (hpA : PD (hRes h A)) (p : V →ₗ[K] A) (hsur : Function.Surjective p)
    (hh : ∀ (x : V) (a : A), h (p x : V) (a : V) = h x a)
    (L : Submodule (𝓞 K) V) (hL : IsIntLat h L) :
    IsIntLat (hRes h A) (latIn A L) ∧
      dual (hRes h A) (latIn A L) = (dual h L).map (p.restrictScalars (𝓞 K)) := by
  obtain ⟨h1, h2, -⟩ := dualLattice (𝓞 K) K V h hs (nondeg h hp) star_range L hL.1
  obtain ⟨k1, k2, -⟩ := dualLattice (𝓞 K) K A (hRes h A) hsA (nondeg _ hpA) star_range _
    (lat_map A p hsur _ h1)
  have e : dual (hRes h A) ((dual h L).map (p.restrictScalars (𝓞 K))) = latIn A L := by
    ext a
    have : a ∈ latIn A L ↔ (a : V) ∈ dual h (dual h L) := by rw [h2]; rfl
    rw [this, mem_dual, mem_dual]
    constructor
    · intro H y hy
      rw [← hh]
      exact H (p y) ⟨y, hy, rfl⟩
    · rintro H _ ⟨y, hy, rfl⟩
      have := H y hy
      rw [← hh] at this
      exact this
  rw [e] at k1 k2
  exact ⟨⟨k1, fun x hx y hy => hL.2 x hx y hy⟩, k2⟩
end GlobalTheory.Mass.PrimDisc
