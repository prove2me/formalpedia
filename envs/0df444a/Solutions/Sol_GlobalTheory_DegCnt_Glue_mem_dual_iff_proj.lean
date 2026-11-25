-- Prove2me | solution 1 for GlobalTheory.DegCnt.Glue.mem_dual_iff_proj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:32:16.36024+00:00
-- url     : https://prove2.me/submissions/f55d72dc-d7f5-4307-8d11-ad6e67ff806b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfLatMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardUnimodularHermGluingsLe
import Theorems.Thm_GlobalTheory_DegCnt_Glue_span_inf
import Theorems.Thm_GlobalTheory_DegCnt_Glue_integral
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HermLat_isLatMod_top_bot_iff
import Theorems.Thm_GlobalTheory_HermLat_mem_dual_iff
import Theorems.Thm_GlobalTheory_HermLat_mem_perp_iff
import Theorems.Thm_GlobalTheory_UnimodQuot_exists_lattice_rep
import Theorems.Thm_GlobalTheory_UnimodQuot_mem_of_perp_perp
import Theorems.Thm_GlobalTheory_UnimodQuot_mem_one_iff
import Theorems.Thm_GlobalTheory_UnimodQuot_star_mem_one
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
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.Glue
open TensorProduct
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable (H : HermSpace K V) {U : Submodule K V} (hc : IsCompl U (perp H U)) {L : Submodule (𝓞 K) V}
  (hU : IsUnimod H L) {p : V →ₗ[K] V} (hp : ∀ v, p v ∈ U) (hq : ∀ v, v - p v ∈ perp H U)
include hc hU hp hq
namespace GlobalTheory.DegCnt.Glue
theorem _root_.solution (d : V) : d ∈ dual H (L ⊓ rs (𝓞 K) (perp H U)) ↔ ∃ v ∈ L, v - p v = d := by
  have hsp := span_inf ((isLatMod_top_bot_iff L).1 hU.1) (perp H U)
  have h0 : ∀ v, ∀ b ∈ perp H U, H.B b (p v) = 0 := fun v b hb => (mem_perp_iff H U _).1 hb _ (hp v)
  rw [mem_dual_iff, hsp]
  constructor
  · rintro ⟨hy, hyM⟩
    have hx : ∀ x : ↥(L ⊓ rs (𝓞 K) (perp H U)), IsIntegral ℤ (H.B x d) := by
      intro x
      rw [← GlobalTheory.UnimodQuot.mem_one_iff, ← H.herm]
      exact GlobalTheory.UnimodQuot.star_mem_one (hyM x x.2)
    let φ : ↥(L ⊓ rs (𝓞 K) (perp H U)) →ₗ[𝓞 K] 𝓞 K :=
      { toFun := fun x => ⟨H.B x d, hx x⟩
        map_add' := fun a b => by
          apply RingOfIntegers.ext
          show H.B ((a : V) + b) d = H.B a d + H.B b d
          simp
        map_smul' := fun a b => by
          apply RingOfIntegers.ext
          show H.B (a • (b : V)) d = algebraMap (𝓞 K) K a * H.B b d
          rw [← algebraMap_smul K a, map_smul]
          rfl }
    obtain ⟨v, hv, h'⟩ := GlobalTheory.UnimodQuot.exists_lattice_rep H hU (perp H U) φ
    refine ⟨v, hv, sub_eq_zero.1 ?_⟩
    have h1 : v - p v - d ∈ U := by
      apply GlobalTheory.UnimodQuot.mem_of_perp_perp H U
      intro x hx
      rw [← hsp] at hx
      have : Submodule.span K ((L ⊓ rs (𝓞 K) (perp H U) : Submodule (𝓞 K) V) : Set V) ≤
          LinearMap.ker (H.B.flip (v - p v - d)) := by
        rw [Submodule.span_le]
        intro b hb
        have h2 : H.B b v = H.B b d := h' ⟨b, hb⟩
        show H.B b (v - p v - d) = 0
        rw [map_sub, map_sub, h0 v b hb.2, h2, sub_zero, sub_self]
      exact this hx
    exact (Submodule.disjoint_def.1 hc.disjoint) _ h1 ((perp H U).sub_mem (hq v) hy)
  · rintro ⟨v, hv, rfl⟩
    refine ⟨hq v, fun b hb => ?_⟩
    have : H.B (p v) b = 0 := by rw [← H.herm, h0 v b hb.2, star_zero]
    rw [map_sub, LinearMap.sub_apply, this, sub_zero]
    exact integral H hU hv hb.1
end GlobalTheory.DegCnt.Glue
