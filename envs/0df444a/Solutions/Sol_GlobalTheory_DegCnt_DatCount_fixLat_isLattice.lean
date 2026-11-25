-- Prove2me | solution 1 for GlobalTheory.DegCnt.DatCount.fixLat_isLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:29:56.379307+00:00
-- url     : https://prove2.me/submissions/78720efc-aaaa-4d0a-b2ed-077fc23527b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeQuotientGensAndIntermediateCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardEmbeddedDataWithGivenFixedLattice
import Theorems.Thm_GlobalTheory_DegCnt_DatCount_fixLat_le
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_Mass_DiscOrder_idxN_ne_zero
import Theorems.Thm_GlobalTheory_Mass_LatticeGens_idxN_smul_mem
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
namespace GlobalTheory.DegCnt.DatCount
theorem _root_.solution {H : HermSpace K V} {g : 𝓞 K} (hg : g ≠ 0) {L' L : Submodule (𝓞 K) V}
    {Γ : Submodule (𝓞 K) (V × V)} (hL' : Submodule.IsLattice K L') (hL : Submodule.IsLattice K L)
    (hΓ : IsModIso H g L' L Γ) : Submodule.IsLattice K (fixLat Γ) := by
  refine ⟨hL.fg.of_le (fixLat_le hΓ).2, ?_⟩
  rw [eq_top_iff, ← hL.span_eq_top, Submodule.span_le]
  intro y hy
  have hn := GlobalTheory.Mass.DiscOrder.idxN_ne_zero hL' hL.fg
  set n : 𝓞 K := ((GlobalTheory.Mass.idxN L L' : ℕ) : 𝓞 K) with hn'
  have hn0 : n ≠ 0 := Nat.cast_ne_zero.2 hn
  have h1 : n • y ∈ L' := GlobalTheory.Mass.LatticeGens.idxN_smul_mem L' L hy
  have h2 : (g * n) • y ∈ fixLat Γ := by
    rw [mul_smul]
    exact hΓ.2.1 ⟨⟨_, h1, rfl⟩, ⟨_, L.smul_mem n hy, rfl⟩⟩
  have h3 : algebraMap (𝓞 K) K (g * n) ≠ 0 := by simpa using ⟨hg, hn0⟩
  have h4 : y = (algebraMap (𝓞 K) K (g * n))⁻¹ • ((g * n) • y) := by
    rw [← algebraMap_smul K (g * n) y, smul_smul, inv_mul_cancel₀ h3, one_smul]
  rw [h4]
  exact Submodule.smul_mem _ _ (Submodule.subset_span h2)
end GlobalTheory.DegCnt.DatCount
