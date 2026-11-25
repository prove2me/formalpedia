-- Prove2me | solution 1 for GlobalTheory.DegCnt.Unimod.isLattice_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:01:53.350507+00:00
-- url     : https://prove2.me/submissions/29b15ab1-eebd-4979-876a-9fa86a3c7b27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolMulPosLeConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntSmulLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsBisTer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexNeZero
import Theorems.Thm_GlobalTheory_DegCnt_Unimod_exists_mul_mem
import Theorems.Thm_GlobalTheory_DegCnt_Unimod_mem_smul_iff

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
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.Unimod
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.DegCnt.Unimod
theorem _root_.solution (g : V ≃ₗ[K] V) {Λ : Submodule (𝓞 K) V} (hΛ : Submodule.IsLattice K Λ) :
    Submodule.IsLattice K (g • Λ) := by
  refine ⟨?_, ?_⟩
  · exact hΛ.fg.map _
  · rw [eq_top_iff]
    intro x _
    obtain ⟨N, hN, h⟩ := exists_mul_mem hΛ.span_eq_top (g⁻¹ x)
    have h1 : N • x ∈ g • Λ := by rw [mem_smul_iff, map_zsmul]; exact h
    have h2 : x = (N : K)⁻¹ • (N • x) := by
      rw [← Int.cast_smul_eq_zsmul K, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hN), one_smul]
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h1)
end GlobalTheory.DegCnt.Unimod
