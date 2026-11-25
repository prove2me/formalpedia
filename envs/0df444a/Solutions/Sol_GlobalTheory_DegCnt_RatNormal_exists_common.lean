-- Prove2me | solution 1 for GlobalTheory.DegCnt.RatNormal.exists_common
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:50:07.350512+00:00
-- url     : https://prove2.me/submissions/f17a6654-9cf6-4abe-a418-f1f3385f5abb

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsInvLower
import Theorems.Thm_GlobalTheory_DegCnt_RatNormal_exists_perp
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_B_swap0
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Dl_injL
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_X_iso
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Xa_le_X
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_level_ne_zero
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_level_unique
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_pairing_isotropicSpan_lastVector
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
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.HermitianLatticeCounting.P
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.RatNormal
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}
namespace GlobalTheory.DegCnt.RatNormal
theorem _root_.solution (F F' : FlagD H r) {j : ℕ} (hj : j ≤ r) {c : K} (hS : NFShape F F' j c)
    (hD : Dl F F' j (hj.trans (Nat.le_succ r)) ≠ 0) (a : Fin (r + 1)) (ha : j ≤ a.val) :
    ∃ y, y - F.e a ∈ F.Xa a.val ∧ c • y - F'.e a ∈ F'.Xa a.val := by
  obtain ⟨hc, -, h3, h4, -, -, hX, -, hz⟩ := hS
  induction a using Fin.lastCases with
  | last =>
    obtain ⟨x, hx, hp⟩ := exists_perp F F' hj hD F.z
    refine ⟨F.z - x, ?_, ?_⟩
    · have : F.z - x - F.e (Fin.last r) = -x := by simp [FlagD.z]
      rw [this]
      exact Submodule.neg_mem _ (Xa_le_X F _ hx)
    · obtain ⟨x1, hx1, x', hx', hs⟩ := Submodule.mem_sup.mp hz
      rw [hX] at hx1
      obtain ⟨x2, hx2, i, hi, rfl⟩ := Submodule.mem_sup.mp hx1
      have hv : i + x' ∈ F'.X := Submodule.add_mem _ hi.2 hx'
      have he : x2 + c • x = F'.z - c • (F.z - x) - (i + x') := by
        rw [smul_sub, ← sub_add, ← hs]; abel
      have h0 : x2 + c • x = 0 := by
        refine Dl_injL F F' hj hD (Submodule.add_mem _ hx2 (Submodule.smul_mem _ _ hx)) fun u hu => B_swap0 H ?_
        have hu' := Xa_le_X F' _ hu
        rw [he, map_sub, map_sub, map_smulₛₗ, hp u hu, pairing_isotropicSpan_lastVector F' hu', X_iso F' hu' hv]
        simp
      rw [h0] at he
      have : c • (F.z - x) - F'.e (Fin.last r) = -(i + x') := by
        rw [← sub_eq_zero.mp he.symm]; simp [FlagD.z]
      rw [this]
      exact Submodule.neg_mem _ hv
  | cast a =>
    obtain ⟨x, hx, al, al', hl, hl'⟩ := h4 a ha
    obtain ⟨b, bl, bl', hb, hb', -, hbc⟩ := h3 x hx (level_ne_zero F hl)
    obtain ⟨-, rfl⟩ := level_unique F hl hb
    obtain ⟨-, rfl⟩ := level_unique F' hl' hb'
    refine ⟨al⁻¹ • x, ?_, ?_⟩
    · have := Submodule.smul_mem _ al⁻¹ hl.2
      rwa [smul_sub, smul_smul, inv_mul_cancel₀ hl.1, one_smul] at this
    · have := Submodule.smul_mem _ al'⁻¹ hl'.2
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hl'.1, one_smul] at this
      have h2 : c * al⁻¹ = al'⁻¹ := by rw [hbc]; field_simp
      rwa [smul_smul, h2]
end GlobalTheory.DegCnt.RatNormal
