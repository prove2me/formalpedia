-- Prove2me | solution 1 for GlobalTheory.DegCnt.PosIso.Xa_le_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:59:22.871225+00:00
-- url     : https://prove2.me/submissions/d537c613-3379-4688-9abe-265884b74cec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormIdealDivisibility
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_e_mem_Ia
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_e_mem_Xa


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.PosIso
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {H : HermSpace K V} {r : ℕ}
omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.DegCnt.PosIso
theorem _root_.solution (N : NF H r) (n : ℕ) : N.F.Xa n ≤ N.F.Xa N.j ⊔ Ia N n := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨b, hb, rfl⟩
  by_cases h : b.val < N.j
  · exact Submodule.mem_sup_left (e_mem_Xa N.F b h)
  · exact Submodule.mem_sup_right (e_mem_Ia N b (not_lt.1 h) hb)
end GlobalTheory.DegCnt.PosIso
