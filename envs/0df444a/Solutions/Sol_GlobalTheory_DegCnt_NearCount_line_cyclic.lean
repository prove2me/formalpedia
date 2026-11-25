-- Prove2me | solution 1 for GlobalTheory.DegCnt.NearCount.line_cyclic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:34:16.455634+00:00
-- url     : https://prove2.me/submissions/8574ebd1-2976-40a9-9711-1f32575d28f4

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
theorem _root_.solution (I : FractionalIdeal (𝓞 K)⁰ K) (v : V) (n : Ideal (𝓞 K)) (hn : n ≠ ⊥) :
    ∃ u ∈ line (I : Submodule (𝓞 K) K) v,
      line (I : Submodule (𝓞 K) K) v ≤ n • line (I : Submodule (𝓞 K) K) v ⊔ Submodule.span (𝓞 K) {u} := by
  obtain ⟨a, J, ha, hI⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
  let φ : 𝓞 K →ₗ[𝓞 K] V := LinearMap.toSpanSingleton (𝓞 K) V ((algebraMap (𝓞 K) K a)⁻¹ • v)
  have hφ : line (I : Submodule (𝓞 K) K) v = Submodule.map φ J := by
    ext x
    simp only [line, Submodule.mem_map, hI, FractionalIdeal.mem_coe, FractionalIdeal.mem_singleton_mul,
      FractionalIdeal.mem_coeIdeal, φ, LinearMap.toSpanSingleton_apply, LinearMap.restrictScalars_apply]
    constructor
    · rintro ⟨y, ⟨_, ⟨z, hz, rfl⟩, rfl⟩, rfl⟩
      refine ⟨z, hz, ?_⟩
      rw [mul_comm, mul_smul, algebraMap_smul]
    · rintro ⟨z, hz, rfl⟩
      refine ⟨_, ⟨_, ⟨z, hz, rfl⟩, rfl⟩, ?_⟩
      rw [mul_comm, mul_smul, algebraMap_smul]
  rw [hφ]
  by_cases hJ : J = ⊥
  · exact ⟨0, zero_mem _, by simp [hJ]⟩
  obtain ⟨b, hb⟩ := IsDedekindDomain.exists_sup_span_eq (I := n * J) (J := J) Ideal.mul_le_right
    (mul_ne_zero hn hJ)
  have hbJ : b ∈ J := by
    rw [← hb]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self b)
  refine ⟨φ b, Submodule.mem_map_of_mem hbJ, ?_⟩
  conv_lhs => rw [← hb]
  rw [Submodule.map_sup, ← Ideal.smul_eq_mul, Submodule.map_smul'']
  refine sup_le_sup_left ?_ _
  rw [← Ideal.submodule_span_eq, Submodule.map_span, Set.image_singleton]
end GlobalTheory.DegCnt.NearCount
