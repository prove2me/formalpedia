-- Prove2me | solution 1 for GlobalTheory.DegCnt.StabInv.isUnimod_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:08:44.565777+00:00
-- url     : https://prove2.me/submissions/17bf1dd3-1ca2-4dec-97c3-a924a3b4e1aa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommonUnipotentStabiliserPreservesTermsAndDatum
import Theorems.Thm_GlobalTheory_DegCnt_StabInv_apply_mem_smul
import Theorems.Thm_GlobalTheory_DegCnt_StabInv_exists_of_mem_smul
import Theorems.Thm_GlobalTheory_DegCnt_StabInv_apply_mem_smul_iff
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HermLat_isLatMod_top_bot_iff
import Theorems.Thm_GlobalTheory_HermLat_mem_dual_iff
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
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.StabInv
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}
namespace GlobalTheory.DegCnt.StabInv
theorem _root_.solution {s : V ≃ₗ[K] V} (h : ∀ x y, H.B (s x) (s y) = H.B x y)
    {Λ : Submodule (𝓞 K) V} (hΛ : IsUnimod H Λ) : IsUnimod H (s • Λ) := by
  obtain ⟨h1, h2⟩ := hΛ
  have hL := (isLatMod_top_bot_iff Λ).1 h1
  have hspan : Submodule.span K ((s • Λ : Submodule (𝓞 K) V) : Set V) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, rfl⟩ := s.surjective x
    have hy : y ∈ Submodule.span K (Λ : Set V) := by rw [hL.span_eq_top]; trivial
    induction hy using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (apply_mem_smul s hy)
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact add_mem (ha trivial) (hb trivial)
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c (ha trivial)
  refine ⟨(isLatMod_top_bot_iff _).2 ⟨Submodule.FG.map _ hL.fg, hspan⟩, ?_⟩
  ext x
  obtain ⟨y, rfl⟩ := s.surjective x
  rw [apply_mem_smul_iff, mem_dual_iff, hspan]
  conv_rhs => rw [← h2, mem_dual_iff, hL.span_eq_top]
  refine and_congr (by simp) ⟨fun hh x hx => ?_, fun hh x hx => ?_⟩
  · rw [← h]; exact hh _ (apply_mem_smul s hx)
  · obtain ⟨z, hz, rfl⟩ := exists_of_mem_smul hx
    rw [h]; exact hh z hz
end GlobalTheory.DegCnt.StabInv
