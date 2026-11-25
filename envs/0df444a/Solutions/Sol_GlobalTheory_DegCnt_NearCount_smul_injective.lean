-- Prove2me | solution 1 for GlobalTheory.DegCnt.NearCount.smul_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:34:17.137836+00:00
-- url     : https://prove2.me/submissions/c11d1ace-5423-40ef-8056-c4dad222830b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_DedekindLFunctions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardLatticesNearReferenceLatticeLe
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
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.NearCount
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.DegCnt.NearCount
theorem _root_.solution (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) :
    Function.Injective fun P : Submodule (𝓞 K) V => m • P := by
  obtain ⟨a, ham, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  obtain ⟨J, hJ⟩ : m ∣ Ideal.span {a} := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 ham)
  have key : ∀ P Q : Submodule (𝓞 K) V, m • P = m • Q → P ≤ Q := by
    intro P Q h x hx
    have h2 : Ideal.span {a} • P = Ideal.span {a} • Q := by
      rw [hJ, mul_comm, Submodule.mul_smul, Submodule.mul_smul, h]
    have h3 : a • x ∈ Ideal.span {a} • Q := h2 ▸ Submodule.smul_mem_smul (Ideal.mem_span_singleton_self a) hx
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h3
    obtain ⟨y, hy, hxy⟩ := h3
    have ha' : algebraMap (𝓞 K) K a ≠ 0 := by simpa using ha
    rw [← algebraMap_smul K a y, ← algebraMap_smul K a x] at hxy
    rwa [← smul_right_injective V ha' hxy]
  intro P Q h
  exact le_antisymm (key P Q h) (key Q P h.symm)
end GlobalTheory.DegCnt.NearCount
