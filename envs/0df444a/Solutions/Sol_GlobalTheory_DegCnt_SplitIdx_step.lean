-- Prove2me | solution 1 for GlobalTheory.DegCnt.SplitIdx.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:53:57.155278+00:00
-- url     : https://prove2.me/submissions/11eaece2-69a9-43d0-9473-04e7addf0e66

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
import Theorems.Thm_GlobalTheory_DegCnt_SplitIdx_idx_comap
import Theorems.Thm_GlobalTheory_DegCnt_SplitIdx_Xa_mono
import Theorems.Thm_GlobalTheory_DegCnt_SplitIdx_e_mem
import Theorems.Thm_GlobalTheory_DegCnt_SplitIdx_mem_Xa_succ
import Theorems.Thm_GlobalTheory_DegCnt_SplitIdx_mem_lead
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Xa_mono
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_DegCnt_DelScale_idx_sup
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
variable {H : HermSpace K V} {r : ℕ}
omit [NumberField K] [FiniteDimensional K V]
namespace GlobalTheory.DegCnt.SplitIdx
theorem _root_.solution (F : FlagD H r) {Λ J : Submodule (𝓞 K) V} (hJ : J ≤ Λ) (a : Fin r) :
    idx (latF F Λ (a.val + 1) ⊔ J) (latF F Λ a.val ⊔ J) = idx (lead F Λ a.castSucc) (lead F J a.castSucc) := by
  rw [idx_sup le_sup_right]
  have e : idx (lead F Λ a.castSucc) (lead F J a.castSucc) = _ := idx_comap _ _ (J ⊔ rs (𝓞 K) (F.Xa a.val))
  rw [e, ← idx_sup (I := rs (𝓞 K) (F.Xa a.val)) (B := J ⊔ _) le_sup_right]
  have e2 : (lead F Λ a.castSucc).map ((LinearMap.toSpanSingleton K V (F.e a.castSucc)).restrictScalars (𝓞 K)) ⊔
      rs (𝓞 K) (F.Xa a.val) = latF F Λ (a.val + 1) ⊔ rs (𝓞 K) (F.Xa a.val) := by
    refine le_antisymm (sup_le ?_ le_sup_right) (sup_le ?_ le_sup_right)
    · rintro _ ⟨t, ht, rfl⟩
      obtain ⟨x, hx, h⟩ := (mem_lead F Λ a t).1 ht
      refine Submodule.mem_sup.2 ⟨x, ⟨hx, ?_⟩, _, (F.Xa a.val).neg_mem h, ?_⟩
      · change x ∈ F.Xa (a.val + 1)
        simpa using Submodule.add_mem _ (Xa_mono F (Nat.le_succ _) h)
          (Submodule.smul_mem _ t (e_mem F (Nat.lt_succ_self a.val)))
      · change _ = t • F.e a.castSucc
        abel
    · rintro x ⟨hx, hx'⟩
      obtain ⟨t, ht⟩ := mem_Xa_succ F a hx'
      refine Submodule.mem_sup.2 ⟨_, ⟨t, (mem_lead F Λ a t).2 ⟨x, hx, ht⟩, rfl⟩, _, ht, ?_⟩
      change t • F.e a.castSucc + _ = _
      abel
  rw [e2, idx_sup le_sup_right]
  refine idx_congr (le_antisymm (inf_le_inf_left _ (sup_le (le_sup_of_le_right inf_le_right) le_sup_left)) ?_)
  rintro x ⟨hx, h⟩
  obtain ⟨i, hi, y, hy, rfl⟩ := Submodule.mem_sup.1 h
  refine ⟨hx, ?_⟩
  rw [add_comm]
  exact Submodule.add_mem_sup ⟨by simpa using Λ.sub_mem hx.1 (hJ hi), hy⟩ hi
end GlobalTheory.DegCnt.SplitIdx
