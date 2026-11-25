-- Prove2me | solution 1 for GlobalTheory.DegCnt.RatNormal.exists_ist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:11:50.274341+00:00
-- url     : https://prove2.me/submissions/da2851c7-732b-459c-b944-9dc347c012a6

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsInvLower
import Theorems.Thm_GlobalTheory_DegCnt_RatNormal_exists_dual
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_B_swap0
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_X_iso
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Xa_le_X
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_e_X
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_e_mem_X
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_pairing_isotropicSpan_lastVector
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_pairing_lastVector_lastVector
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_z_X
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
theorem _root_.solution [FiniteDimensional K V] [CharZero K] (G G' : FlagD H r) {j : ℕ} (hj : j ≤ r) {c : K} (hc : c ≠ 0)
    (same : ∀ a : Fin (r + 1), j ≤ a.val → G'.e a = c • G.e a)
    (hs : ∀ y, ∃ x ∈ G.X, ∀ u ∈ G'.Xa j, H.B u (y - x) = 0) :
    ∃ ist : Fin r → V, (∀ a b : Fin r, H.B (G.e a.castSucc) (ist b) = if a = b then 1 else 0) ∧
      (∀ b, ∀ u ∈ G'.Xa j, H.B u (ist b) = 0) ∧ (∀ b, H.B G.z (ist b) = 0) ∧
      ∀ a b : Fin r, j ≤ a.val → j ≤ b.val → H.B (ist a) (ist b) = 0 := by
  have hp : ∀ a : Fin (r + 1), j ≤ a.val → ∀ u ∈ G'.Xa j, H.B u (G.e a) = 0 := fun a ha u hu => by
    have h := e_X G' a (Xa_le_X G' _ hu)
    rw [same a ha, map_smul, LinearMap.smul_apply, smul_eq_mul] at h
    exact B_swap0 H ((mul_eq_zero.mp h).resolve_left hc)
  have h1 : ∀ b : Fin r, ∃ y, (∀ a : Fin r, H.B (G.e a.castSucc) y = if a = b then 1 else 0) ∧
      (∀ u ∈ G'.Xa j, H.B u y = 0) ∧ H.B G.z y = 0 := fun b => by
    obtain ⟨y, hy⟩ := exists_dual G b
    obtain ⟨x, hx, hxp⟩ := hs y
    refine ⟨y - x + star (H.B G.z (y - x) / G.T) • G.z, fun a => ?_, fun u hu => ?_, ?_⟩
    · rw [map_add, map_sub, map_smulₛₗ, hy, e_X G _ hx, pairing_isotropicSpan_lastVector G (e_mem_X G a)]; simp
    · have := hp (Fin.last r) hj u hu
      rw [map_add, hxp u hu, map_smulₛₗ, FlagD.z, this]; simp
    · rw [map_add, map_smulₛₗ, pairing_lastVector_lastVector]
      have := G.hT
      simp only [starRingEnd_apply, star_star, smul_eq_mul]
      field_simp
      ring
  choose y hy1 hy2 hy3 using h1
  obtain ⟨s, hsd⟩ : ∃ s : Fin r → V, ∀ b, s b = ∑ a ∈ Finset.univ.filter (fun a : Fin r => j ≤ a.val),
      (H.B (y b) (y a) / 2) • G.e a.castSucc := ⟨_, fun _ => rfl⟩
  have hsX : ∀ b, s b ∈ G.X := fun b => by
    rw [hsd]; exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (e_mem_X G a)
  have hsy : ∀ a b : Fin r, j ≤ b.val → H.B (s a) (y b) = H.B (y a) (y b) / 2 := fun a b hb => by
    rw [hsd, map_sum, LinearMap.sum_apply]
    simp [hy1, hb]
  refine ⟨fun b => y b - s b, fun a b => ?_, fun b u hu => ?_, fun b => ?_, fun a b ha hb => ?_⟩
  · rw [map_sub, hy1, e_X G _ (hsX b), sub_zero]
  · rw [map_sub, hy2 b u hu, hsd, map_sum, Finset.sum_eq_zero, sub_zero]
    intro a ha
    rw [map_smulₛₗ, hp a.castSucc (Finset.mem_filter.mp ha).2 u hu, smul_zero]
  · rw [map_sub, hy3, z_X G (hsX b), sub_zero]
  · have h2 : H.B (y a) (s b) = H.B (y a) (y b) / 2 := by
      rw [← H.herm (s b), hsy b a ha, star_div₀, H.herm]; simp
    simp only [map_sub, LinearMap.sub_apply, h2, hsy a b hb, X_iso G (hsX a) (hsX b)]
    ring
end GlobalTheory.DegCnt.RatNormal
