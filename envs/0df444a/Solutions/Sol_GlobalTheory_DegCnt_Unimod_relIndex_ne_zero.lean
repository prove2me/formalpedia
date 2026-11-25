-- Prove2me | solution 1 for GlobalTheory.DegCnt.Unimod.relIndex_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:13:51.846348+00:00
-- url     : https://prove2.me/submissions/edbb1c70-4847-4fa2-a148-7fd3ef46c1c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolMulPosLeConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntSmulLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsBisTer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexNeZero
import Theorems.Thm_GlobalTheory_DegCnt_Unimod_exists_mul_le
import Theorems.Thm_GlobalTheory_DegCnt_Unimod_finite_between
import Theorems.Thm_GlobalTheory_DegCnt_Unimod_mem_smul_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.Unimod
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.DegCnt.Unimod
theorem _root_.solution (G : Subgroup (V ≃ₗ[K] V)) {Λ Λ' : Submodule (𝓞 K) V}
    (hΛ : Submodule.IsLattice K Λ) (hΛ' : Submodule.IsLattice K Λ') :
    (G ⊓ MulAction.stabilizer (V ≃ₗ[K] V) Λ).relIndex
      (G ⊓ MulAction.stabilizer (V ≃ₗ[K] V) Λ') ≠ 0 := by
  obtain ⟨a, ha, h₁⟩ := exists_mul_le hΛ.span_eq_top hΛ'.fg
  obtain ⟨b, hb, h₂⟩ := exists_mul_le hΛ'.span_eq_top hΛ.fg
  set H := G ⊓ MulAction.stabilizer (V ≃ₗ[K] V) Λ' with hH
  have e : (G ⊓ MulAction.stabilizer (V ≃ₗ[K] V) Λ).relIndex H = (MulAction.stabilizer H Λ).index := by
    rw [Subgroup.relIndex]
    congr 1
    ext g
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨g.2.1, h⟩⟩
  rw [e, MulAction.index_stabilizer]
  refine Set.ncard_ne_zero_of_mem (MulAction.mem_orbit_self Λ) ?_
  refine (finite_between hΛ'.fg ha hb).subset ?_
  rintro _ ⟨g, rfl⟩
  have hg : (g : V ≃ₗ[K] V) • Λ' = Λ' := g.2.2
  have hg' : ∀ x, (g : V ≃ₗ[K] V)⁻¹ x ∈ Λ' ↔ x ∈ Λ' := fun x => by rw [← mem_smul_iff, hg]
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · change a • x ∈ (g : V ≃ₗ[K] V) • Λ
    rw [mem_smul_iff, map_zsmul]
    exact h₁ _ ((hg' x).2 hx)
  · have hx' : x ∈ (g : V ≃ₗ[K] V) • Λ := hx
    rw [mem_smul_iff] at hx'
    rw [← hg', map_zsmul]
    exact h₂ _ hx'
end GlobalTheory.DegCnt.Unimod
