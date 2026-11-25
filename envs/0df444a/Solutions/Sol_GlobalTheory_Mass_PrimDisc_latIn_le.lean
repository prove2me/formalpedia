-- Prove2me | solution 1 for GlobalTheory.Mass.PrimDisc.latIn_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:56:55.210626+00:00
-- url     : https://prove2.me/submissions/f65effa3-f42b-4b57-8e20-e19fbd12c7b3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionTotallyDefiniteHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodulaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeQuotientGensAndIntermediateCountStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimitiveHermitianSublatticeDiscriminantGenerato

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
theorem _root_.solution (A : Submodule K V) (p : V →ₗ[K] A) (hp : ∀ a : A, p a = a)
    (L : Submodule (𝓞 K) V) : latIn A L ≤ L.map (p.restrictScalars (𝓞 K)) :=
  fun a ha => ⟨a, ha, hp a⟩
end GlobalTheory.Mass.PrimDisc
