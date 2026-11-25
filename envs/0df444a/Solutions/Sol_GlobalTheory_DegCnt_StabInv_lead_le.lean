-- Prove2me | solution 1 for GlobalTheory.DegCnt.StabInv.lead_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:52:09.550824+00:00
-- url     : https://prove2.me/submissions/bca22661-0e04-447c-8823-9299f8798629

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommonUnipotentStabiliserPreservesTermsAndDatum
import Theorems.Thm_GlobalTheory_DegCnt_StabInv_apply_mem_smul

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
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.StabInv
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}
namespace GlobalTheory.DegCnt.StabInv
theorem _root_.solution {F : FlagD H r} {s : V ≃ₗ[K] V} (h : Keeps F s) (Λ : Submodule (𝓞 K) V)
    (a : Fin (r + 1)) : lead F Λ a ≤ lead F (s • Λ) a := by
  intro t ht
  obtain ⟨l, hl, x, hx, he⟩ := Submodule.mem_sup.1 ht
  have he' : l + x = t • F.e a := he
  refine Submodule.mem_sup.2 ⟨s l, apply_mem_smul s hl, s x - t • (s (F.e a) - F.e a),
    sub_mem ((h.flag _ _).2 hx) (Submodule.smul_mem (F.Xa a.val) t (h.vec a)), ?_⟩
  show _ = t • F.e a
  rw [smul_sub, ← map_smul, ← he', map_add]
  abel
end GlobalTheory.DegCnt.StabInv
