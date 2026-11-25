-- Prove2me | solution 1 for GlobalTheory.DegCnt.NormOneCount.card_torsion_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:52:03.670915+00:00
-- url     : https://prove2.me/submissions/a8b7d558-ba50-40cc-bfd4-df4f921ef9d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IdealsOfNormEqIndexSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfMulMem
import Theorems.Thm_GlobalTheory_DegCnt_NormOneCount_le_totient_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
noncomputable section
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.NormOneCount
namespace GlobalTheory.DegCnt.NormOneCount
theorem _root_.solution (K : Type) [Field K] [NumberField K] :
    Nat.card (Units.torsion K) ≤ 2 * Module.finrank ℚ K ^ 2 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Units.torsion K)
  have h1 : IsPrimitiveRoot g (Nat.card (Units.torsion K)) := hg ▸ IsPrimitiveRoot.orderOf g
  have h2 : IsPrimitiveRoot (g : (𝓞 K)ˣ) (Nat.card (Units.torsion K)) :=
    h1.map_of_injective (f := (Units.torsion K).subtype) Subtype.val_injective
  have h3 : IsPrimitiveRoot ((g : (𝓞 K)ˣ) : 𝓞 K) (Nat.card (Units.torsion K)) :=
    IsPrimitiveRoot.coe_units_iff.2 h2
  have h4 : IsPrimitiveRoot (algebraMap (𝓞 K) K ((g : (𝓞 K)ˣ) : 𝓞 K)) (Nat.card (Units.torsion K)) :=
    h3.map_of_injective (RingOfIntegers.coe_injective)
  have hpos : 0 < Nat.card (Units.torsion K) := Nat.card_pos
  have h5 := IsPrimitiveRoot.lcm_totient_le_finrank (K := ℚ) h4 h4
    (by rw [Nat.lcm_self]; exact Polynomial.cyclotomic.irreducible_rat hpos)
  rw [Nat.lcm_self] at h5
  exact (le_totient_sq _).1.trans (by gcongr)
end GlobalTheory.DegCnt.NormOneCount
