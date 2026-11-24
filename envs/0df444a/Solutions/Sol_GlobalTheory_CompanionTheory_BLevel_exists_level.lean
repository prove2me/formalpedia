-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BLevel.exists_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:51:01.666273+00:00
-- url     : https://prove2.me/submissions/bd4b69bf-32ee-4709-b717-cda1f2a737b1

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTerLast
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_LatticeCongruenceSubgroupsOpenCompact
import Theorems.Thm_GlobalTheory_CompanionTheory_BLevel_exists_near_of_mem_nhds
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
noncomputable section
open CompanionTheory.Rg.FlB CompanionTheory.Rg.Fl Topology Filter
open scoped Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BLevel
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {m : ℕ}
namespace GlobalTheory.CompanionTheory.BLevel
theorem _root_.solution {W : Set (GL (Fin m) L)} (hW : W ∈ 𝓝 (1 : GL (Fin m) L)) :
    ∃ π : L, π ≠ 0 ∧ ‖π‖ < 1 ∧ ∀ g : GL (Fin m) L, IsNear ‖π‖ g.1 → g ∈ W := by
  rw [Units.isEmbedding_embedProduct.isInducing.nhds_eq_comap, Filter.mem_comap] at hW
  obtain ⟨t, ht, hsub⟩ := hW
  have ht' : t ∈ 𝓝 ((1 : Matrix (Fin m) (Fin m) L), MulOpposite.op (1 : Matrix (Fin m) (Fin m) L)) := by
    simpa using ht
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 ht'
  have hv' : MulOpposite.op ⁻¹' v ∈ 𝓝 (1 : Matrix (Fin m) (Fin m) L) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds hv
  obtain ⟨ε, hε, h⟩ := exists_near_of_mem_nhds (L := L) (m := m) (c := (1 : Matrix (Fin m) (Fin m) L))
    (A := u ∩ MulOpposite.op ⁻¹' v) (Filter.inter_mem hu hv')
  obtain ⟨π, hπ0, hπ⟩ := NormedField.exists_norm_lt L (lt_min hε one_pos)
  have hπ1 : ‖π‖ < 1 := hπ.trans_le (min_le_right _ _)
  have hπε : ‖π‖ ≤ ε := (hπ.trans_le (min_le_left _ _)).le
  refine ⟨π, norm_pos_iff.1 hπ0, hπ1, fun g hg => hsub ?_⟩
  have hg' : IsNear ‖π‖ (g⁻¹).1 := (congS ‖π‖ (norm_nonneg _) hπ1).inv_mem (show g ∈ congS ‖π‖ (norm_nonneg _) hπ1 from hg)
  apply huv
  exact ⟨(h g.1 fun i j => (hg i j).trans hπε).1, (h (g⁻¹).1 fun i j => (hg' i j).trans hπε).2⟩
end GlobalTheory.CompanionTheory.BLevel
