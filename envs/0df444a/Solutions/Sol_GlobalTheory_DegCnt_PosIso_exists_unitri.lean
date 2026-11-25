-- Prove2me | solution 1 for GlobalTheory.DegCnt.PosIso.exists_unitri
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:32:36.366944+00:00
-- url     : https://prove2.me/submissions/7f8a04a1-e3cf-41dc-acb4-c4b638a07d9d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormIdealDivisibility
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_Ia_le
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_Xa_ist
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_exists_shear
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Xa_le_X
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Xa_mono
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_e_mem_X
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_e_mem_Xa
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
noncomputable section
open NumberField Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.PosIso
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {H : HermSpace K V} {r : ℕ}
omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.DegCnt.PosIso
theorem _root_.solution (N : NF H r) (v : Fin r → V)
    (hv : ∀ b : Fin r, N.j ≤ b.val → v b - N.F.e b.castSucc ∈ Ia N b.val) :
    ∃ u ∈ Gs N, u N.F.z = N.F.z ∧ ∀ b : Fin r, N.j ≤ b.val → u (v b) = N.F.e b.castSucc := by
  have key : ∀ m : ℕ, ∃ u ∈ Gs N, u N.F.z = N.F.z ∧ ∀ b : Fin r, N.j ≤ b.val →
      u (v b) = if r ≤ b.val + m then N.F.e b.castSucc else v b := by
    intro m
    induction m with
    | zero => exact ⟨1, one_mem _, rfl, fun b _ => by rw [if_neg (by have := b.isLt; omega)]; rfl⟩
    | succ m ih =>
      obtain ⟨u, hu, huz, h⟩ := ih
      by_cases hm : N.j + m + 1 ≤ r
      · let b0 : Fin r := ⟨r - m - 1, by omega⟩
        have hb0 : N.j ≤ b0.val := by show N.j ≤ r - m - 1; omega
        have hb1 : b0.val = r - m - 1 := rfl
        obtain ⟨s, hs, hsz, hs'⟩ := exists_shear N b0 hb0 (neg_mem (hv b0 hb0))
        refine ⟨s * u, mul_mem hs hu, by simp [huz, hsz], fun b hb => ?_⟩
        have hvX : v b ∈ N.F.Xa (b.val + 1) := by
          have := add_mem (Xa_mono N.F (Nat.le_succ _) (Ia_le N _ (hv b hb))) (e_mem_Xa N.F b (Nat.lt_succ_self _))
          simpa using this
        rw [LinearEquiv.mul_apply, h b hb]
        by_cases h1 : r ≤ b.val + m
        · rw [if_pos h1, if_pos (by omega), hs' _ (e_mem_X _ _), N.ist_e b b0 hb0,
            if_neg (by rintro rfl; omega)]
          simp
        · rw [if_neg h1, hs' _ (Xa_le_X _ _ hvX)]
          by_cases h2 : b = b0
          · subst h2
            have h3 := Xa_ist N b0 hb0 _ (Ia_le N _ (hv b0 hb0))
            rw [map_sub, LinearMap.sub_apply, N.ist_e b0 b0 hb0, if_pos rfl, sub_eq_zero] at h3
            rw [if_pos (by omega), h3]; simp
          · have h3 : b.val ≠ b0.val := fun h' => h2 (Fin.ext h')
            rw [if_neg (by omega), Xa_ist N b0 hb0 _ (Xa_mono N.F (by omega) hvX)]
            simp
      · refine ⟨u, hu, huz, fun b hb => ?_⟩
        rw [h b hb, if_pos (by omega), if_pos (by omega)]
  obtain ⟨u, hu, huz, h⟩ := key r
  exact ⟨u, hu, huz, fun b hb => by rw [h b hb, if_pos (by omega)]⟩
end GlobalTheory.DegCnt.PosIso
