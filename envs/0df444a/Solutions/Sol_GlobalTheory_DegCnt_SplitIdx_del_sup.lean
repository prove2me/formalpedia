-- Prove2me | solution 1 for GlobalTheory.DegCnt.SplitIdx.del_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:34:00.155588+00:00
-- url     : https://prove2.me/submissions/19225b05-6208-47a9-89ce-fc8a017d4bc3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfLatMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFlagPairLatticeSumDiscriminantEqNormMinorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormTerminalDeterminant
import Theorems.Thm_GlobalTheory_DegCnt_SplitIdx_idx_congr
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_DegCnt_DelScale_idx_sup
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
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.SplitIdx
open GlobalTheory.Mass GlobalTheory.Mass.DiscOrder GlobalTheory.DegCnt.DelScale
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
omit [FiniteDimensional K V]
namespace GlobalTheory.DegCnt.SplitIdx
theorem _root_.solution (H : HermSpace K V) (M : Submodule (𝓞 K) V) (I : Submodule K V)
    (h0 : I ⊓ Submodule.span K (M : Set V) = ⊥)
    (hI : ∀ i ∈ I, ∀ y ∈ Submodule.span K (M : Set V) ⊔ I, H.B i y = 0) :
    del H (M ⊔ rs (𝓞 K) I) = del H M := by
  have hs : Submodule.span K ((M ⊔ rs (𝓞 K) I : Submodule (𝓞 K) V) : Set V) = Submodule.span K (M : Set V) ⊔ I := by
    refine le_antisymm (Submodule.span_le.2 fun x hx => ?_) (sup_le (Submodule.span_mono (le_sup_left (a := M)))
      fun x hx => Submodule.subset_span (Submodule.mem_sup_right hx))
    obtain ⟨m, hm, i, hi, rfl⟩ := Submodule.mem_sup.1 hx
    exact Submodule.add_mem_sup (Submodule.subset_span hm) hi
  have hI' : ∀ i ∈ I, ∀ y ∈ Submodule.span K (M : Set V) ⊔ I, H.B y i = 0 := fun i hi y hy => by
    rw [← H.herm, hI i hi y hy, star_zero]
  have hd : dual H (M ⊔ rs (𝓞 K) I) = dual H M ⊔ rs (𝓞 K) I := by
    ext y
    rw [mem_dual_iff, hs]
    constructor
    · rintro ⟨hy, h⟩
      obtain ⟨s, hs, i, hi, rfl⟩ := Submodule.mem_sup.1 hy
      refine Submodule.add_mem_sup ((mem_dual_iff H M s).2 ⟨hs, fun x hx => ?_⟩) hi
      have := h x (Submodule.mem_sup_left hx)
      rwa [map_add, LinearMap.add_apply, hI i hi x (Submodule.mem_sup_left (Submodule.subset_span hx)),
        add_zero] at this
    · intro hy
      obtain ⟨s, hs, i, hi, rfl⟩ := Submodule.mem_sup.1 hy
      rw [mem_dual_iff] at hs
      refine ⟨Submodule.add_mem_sup hs.1 hi, fun x hx => ?_⟩
      obtain ⟨m, hm, i', hi', rfl⟩ := Submodule.mem_sup.1 hx
      rw [map_add, hI' i' hi' _ (Submodule.add_mem_sup hs.1 hi), add_zero, map_add, LinearMap.add_apply,
        hI i hi m (Submodule.mem_sup_left (Submodule.subset_span hm)), add_zero]
      exact hs.2 m hm
  have key : ∀ {A B : Submodule (𝓞 K) V}, A ≤ rs (𝓞 K) (Submodule.span K (M : Set V)) →
      B ≤ rs (𝓞 K) (Submodule.span K (M : Set V)) → idx (A ⊔ rs (𝓞 K) I) (B ⊔ rs (𝓞 K) I) = idx A B := by
    intro A B hA hB
    rw [idx_sup le_sup_right]
    refine idx_congr (le_antisymm ?_ (inf_le_inf_left _ le_sup_left))
    rintro x ⟨hx, h⟩
    obtain ⟨b, hb, i, hi, rfl⟩ := Submodule.mem_sup.1 h
    have : i ∈ I ⊓ Submodule.span K (M : Set V) :=
      ⟨hi, by simpa using (Submodule.span K (M : Set V)).sub_mem (hA hx) (hB hb)⟩
    rw [h0, Submodule.mem_bot] at this
    subst this
    exact ⟨hx, by simpa using hb⟩
  have a : M ≤ rs (𝓞 K) (Submodule.span K (M : Set V)) := fun x hx => Submodule.subset_span hx
  have b : dual H M ≤ rs (𝓞 K) (Submodule.span K (M : Set V)) := inf_le_left
  rw [del, del, hd, gidx, gidx, key a b, key b a]
end GlobalTheory.DegCnt.SplitIdx
