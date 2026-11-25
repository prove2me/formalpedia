-- Prove2me | solution 1 for GlobalTheory.DegCnt.FixDisc.disc_latIn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:02:26.76953+00:00
-- url     : https://prove2.me/submissions/0eedc29b-b68f-46a5-8040-9748045304fa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MinkowskiNumberDvdFactorial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DiscriminantOrderCommonFixedLatticeEmbeddedData
import Theorems.Thm_GlobalTheory_DegCnt_FixDisc_lattice_map
import Theorems.Thm_GlobalTheory_DegCnt_FixDisc_aniso
import Theorems.Thm_GlobalTheory_DegCnt_FixDisc_flip_nondeg
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualBasic_mem_dual
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualLattice


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.FixDisc
open GlobalTheory.Mass GlobalTheory.Mass.DiscOrder Formalism.HermitianLatticesTheory
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.DegCnt.FixDisc
theorem _root_.solution {H : HermSpace K V} (hP : PD H.B.flip) {U : Submodule K V} (p : V →ₗ[K] U)
    (p1 : ∀ t : U, p t = t) (p2 : ∀ (x : V) (t : U), H.B t (p x) = H.B t x) {A : Submodule (𝓞 K) V}
    (hA : Submodule.IsLattice K A) :
    discN (hRes H.B.flip U) (latIn U A) =
      idxN (Formalism.HermitianLatticesTheory.dual H.B.flip A) ((latIn U A).comap (p.restrictScalars (𝓞 K))) := by
  have dl := dualLattice (𝓞 K) K V H.B.flip (flip_isSymm H) (flip_nondeg hP) star_algebraMap_ringOfIntegers_mem_range A hA
  have hs : (hRes H.B.flip U).IsSymm := ⟨fun x y => H.herm y x⟩
  have hn : (hRes H.B.flip U).Nondegenerate :=
    ⟨fun x hx => Subtype.ext (aniso hP x (hx x)), fun x hx => Subtype.ext (aniso hP x (hx x))⟩
  have hL := lattice_map dl.1 p (fun t => ⟨t, p1 t⟩)
  have dl' := dualLattice (𝓞 K) K U (hRes H.B.flip U) hs hn star_algebraMap_ringOfIntegers_mem_range _ hL
  have e : Formalism.HermitianLatticesTheory.dual (hRes H.B.flip U) ((Formalism.HermitianLatticesTheory.dual H.B.flip A).map (p.restrictScalars (𝓞 K))) =
      latIn U A := by
    ext t
    change _ ↔ (t : V) ∈ A
    have e0 : (t : V) ∈ A ↔ (t : V) ∈ Formalism.HermitianLatticesTheory.dual H.B.flip (Formalism.HermitianLatticesTheory.dual H.B.flip A) := by rw [dl.2.1]
    rw [e0, dualBasic_mem_dual, dualBasic_mem_dual H.B.flip _ (t : V)]
    constructor
    · intro h y hy
      have := h (p y) ⟨y, hy, rfl⟩
      change H.B t (p y) ∈ _ at this
      rw [p2] at this
      exact this
    · rintro h _ ⟨y, hy, rfl⟩
      change H.B t (p y) ∈ _
      rw [p2]
      exact h y hy
  rw [discN, ← e, dl'.2.1, e]
  exact (AddSubgroup.relIndex_comap (latIn U A).toAddSubgroup (p.restrictScalars (𝓞 K)).toAddMonoidHom
    (Formalism.HermitianLatticesTheory.dual H.B.flip A).toAddSubgroup).symm
end GlobalTheory.DegCnt.FixDisc
