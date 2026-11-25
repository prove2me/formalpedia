-- Prove2me | solution 1 for GlobalTheory.DegCnt.DatCount.div_mem_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:13:47.476298+00:00
-- url     : https://prove2.me/submissions/24ac197f-68fe-4ef5-80a8-bc7e5ccf9586

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeQuotientGensAndIntermediateCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardEmbeddedDataWithGivenFixedLattice
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualBasic_mem_dual
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
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
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
omit [NumberField K]
namespace GlobalTheory.DegCnt.DatCount
theorem _root_.solution {H : HermSpace K V} {g : 𝓞 K} (hg : g ≠ 0) {L' L : Submodule (𝓞 K) V}
    {Γ : Submodule (𝓞 K) (V × V)} (hΓ : IsModIso H g L' L Γ) {s y : V} (h : (s, y) ∈ Γ) :
    (algebraMap (𝓞 K) K g)⁻¹ • (s - y) ∈ Formalism.HermitianLatticesTheory.dual H.B.flip (fixLat Γ) := by
  rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
  intro a ha
  obtain ⟨t, ht⟩ := hΓ.2.2.2.2.2.2 (s, y) h (a, a) ha
  have h3 : algebraMap (𝓞 K) K g ≠ 0 := by simpa using hg
  refine Submodule.mem_one.2 ⟨t, ?_⟩
  rw [map_smul, map_sub, smul_eq_mul]
  change _ = _ * (H.B s a - H.B y a)
  rw [ht, map_mul, ← mul_assoc, inv_mul_cancel₀ h3, one_mul]
end GlobalTheory.DegCnt.DatCount
