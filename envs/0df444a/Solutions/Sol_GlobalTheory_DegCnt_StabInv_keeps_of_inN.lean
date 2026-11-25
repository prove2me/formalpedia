-- Prove2me | solution 1 for GlobalTheory.DegCnt.StabInv.keeps_of_inN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:13:11.80532+00:00
-- url     : https://prove2.me/submissions/37f34bf0-5509-47ce-a17d-80d27ea87e6c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommonUnipotentStabiliserPreservesTermsAndDatum
import Theorems.Thm_GlobalTheory_DegCnt_StabInv_xa_mono
import Theorems.Thm_Formalism_H_dualEquiv_apply
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
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.StabInv
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}
omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.DegCnt.StabInv
theorem _root_.solution [FiniteDimensional K V] {F : FlagD H r} {s : V ≃ₗ[K] V}
    (h : F.InN (s : V →ₗ[K] V)) : Keeps F s := by
  obtain ⟨h1, -, h3, h4⟩ := h
  have hmem : ∀ b : Fin r, F.e b.castSucc ∈ F.X := fun b =>
    Submodule.subset_span ⟨b, b.2, rfl⟩
  refine ⟨h1, fun a x => ?_, fun a => ?_, fun y hy => ?_⟩
  · have hle : (F.Xa a).map (s : V →ₗ[K] V) ≤ F.Xa a := by
      rw [Submodule.map_le_iff_le_comap]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨b, hb, rfl⟩
      have hb1 : F.e b.castSucc ∈ F.Xa a := Submodule.subset_span ⟨b, hb, rfl⟩
      have hb2 := xa_mono F (le_of_lt hb) (h3 b)
      simpa using add_mem hb2 hb1
    have heq : (F.Xa a).map (s : V →ₗ[K] V) = F.Xa a :=
      Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq s _)
    constructor
    · intro hx
      rw [← heq] at hx
      obtain ⟨y, hy, hxy⟩ := hx
      rwa [← s.injective hxy]
    · intro hx
      exact hle ⟨x, hx, rfl⟩
  · induction a using Fin.lastCases with
    | last => exact h4 _ F.zperp
    | cast b => exact h3 b
  · refine h4 y fun b => ?_
    rw [← H.herm, hy _ (hmem b), star_zero]
end GlobalTheory.DegCnt.StabInv
