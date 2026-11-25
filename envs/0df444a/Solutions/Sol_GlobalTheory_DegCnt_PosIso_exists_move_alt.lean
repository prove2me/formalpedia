-- Prove2me | solution 1 for GlobalTheory.DegCnt.PosIso.exists_move_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:56:06.655929+00:00
-- url     : https://prove2.me/submissions/a2aa77a5-d19f-4659-a487-091c9f257efd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormIdealDivisibility
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_Ia_X
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_hermForm_second_flag_X_z_eq_zero
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_exists_eich
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_X_iso
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
noncomputable section
open NumberField Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.PosIso
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {H : HermSpace K V} {r : ℕ}
omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.DegCnt.PosIso
theorem _root_.solution (N : NF H r) {x : V} (hx : x ∈ Ia N r) :
    ∃ s ∈ Gs N, s N.F.z = N.F.z - x ∧ ∀ y ∈ N.F.X, s y = y := by
  have hz : ∀ y, H.B y (star N.F.T⁻¹ • N.F.z) = N.F.T⁻¹ * H.B y N.F.z := by
    intro y; rw [LinearMap.map_smulₛₗ, starRingEnd_apply, star_star, smul_eq_mul]
  obtain ⟨s, hs, h⟩ := exists_eich N x (star N.F.T⁻¹ • N.F.z)
    (-H.B (star N.F.T⁻¹ • N.F.z) (star N.F.T⁻¹ • N.F.z) / 2) hx
    (by rw [hz, pairing_isotropicSpan_lastVector N.F (Ia_X N hx), mul_zero])
    (by rw [star_div₀, star_neg, H.herm, star_ofNat]; ring)
    (fun a _ => by rw [hz, pairing_isotropicSpan_lastVector N.F (e_mem_X _ _)]; simp)
    (fun a _ => by rw [hz, pairing_isotropicSpan_lastVector N.F (e_mem_X _ _)]; simp)
    (fun a _ => by rw [hz, hermForm_second_flag_X_z_eq_zero N (e_mem_X _ _)]; simp)
    (Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_insert _ _)))))
  refine ⟨s, hs, ?_, fun y hy => ?_⟩
  · rw [h _ (z_X N.F (Ia_X N hx)), hz, pairing_lastVector_lastVector, mul_neg, inv_mul_cancel₀ N.F.hT]; module
  · rw [h _ (X_iso N.F hy (Ia_X N hx)), hz, pairing_isotropicSpan_lastVector N.F hy]; simp
end GlobalTheory.DegCnt.PosIso
