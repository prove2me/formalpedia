-- Prove2me | solution 1 for GlobalTheory.UnimodQuot.isUnimodMod_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:58:32.003903+00:00
-- url     : https://prove2.me/submissions/f21f7ffe-fa70-48ec-9003-c2a019c11119

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLocalizedModuleSubtype
import Theorems.Thm_GlobalTheory_UnimodQuot_mem_of_perp_perp
import Theorems.Thm_GlobalTheory_UnimodQuot_mem_one_iff
import Theorems.Thm_GlobalTheory_UnimodQuot_star_mem_one
import Theorems.Thm_GlobalTheory_UnimodQuot_exists_smul_mem
import Theorems.Thm_GlobalTheory_UnimodQuot_exists_lattice_rep
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HermLat_isLatMod_top_bot_iff
import Theorems.Thm_GlobalTheory_HermLat_mem_dual_iff
import Theorems.Thm_GlobalTheory_HermLat_mem_perp_iff
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
open GlobalTheory GlobalTheory.UnimodQuot
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.UnimodQuot
theorem _root_.solution (H : HermSpace K V) {L : Submodule (𝓞 K) V} (hU : IsUnimod H L) {I : Submodule K V}
    (hI : ∀ x ∈ I, ∀ y ∈ I, H.B x y = 0) :
    IsUnimodMod H ((L ⊓ rs (𝓞 K) (perp H I)) ⊔ rs (𝓞 K) I) (perp H I) I := by
  have hL := (isLatMod_top_bot_iff L).1 hU.1
  have hint : ∀ y ∈ L, ∀ x ∈ L, H.B y x ∈ (1 : Submodule (𝓞 K) K) := by
    intro y hy
    rw [← hU.2, mem_dual_iff] at hy
    exact hy.2
  have hIp : I ≤ perp H I := fun x hx => (mem_perp_iff H I x).2 (hI x hx)
  have hsat : ∀ v ∈ perp H I, ∃ c : K, c ≠ 0 ∧ c • v ∈ L ⊓ rs (𝓞 K) (perp H I) := by
    intro v hv
    obtain ⟨s, hs⟩ := exists_smul_mem hL v
    refine ⟨algebraMap (𝓞 K) K s, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2, ?_,
      (perp H I).smul_mem _ hv⟩
    rw [algebraMap_smul]
    exact hs
  have hspan : Submodule.span K (((L ⊓ rs (𝓞 K) (perp H I)) ⊔ rs (𝓞 K) I : Submodule (𝓞 K) V) : Set V)
      = perp H I := by
    apply le_antisymm
    · rw [Submodule.span_le]
      have : (L ⊓ rs (𝓞 K) (perp H I)) ⊔ rs (𝓞 K) I ≤ rs (𝓞 K) (perp H I) := sup_le inf_le_right hIp
      exact this
    · intro v hv
      obtain ⟨c, hc, h⟩ := hsat v hv
      rw [← Submodule.smul_mem_iff _ hc]
      exact Submodule.subset_span (Submodule.mem_sup_left h)
  refine ⟨⟨⟨_, ?_, rfl⟩, hspan⟩, ?_⟩
  · have : IsNoetherian (𝓞 K) L := inferInstance
    have : IsNoetherian (𝓞 K) ↥(L ⊓ rs (𝓞 K) (perp H I)) := isNoetherian_of_le inf_le_left
    rw [← Module.Finite.iff_fg]
    infer_instance
  ext y
  rw [mem_dual_iff, hspan]
  constructor
  · rintro ⟨hy, hyM⟩
    have hx : ∀ x : ↥(L ⊓ rs (𝓞 K) (perp H I)), IsIntegral ℤ (H.B x y) := by
      intro x
      rw [← mem_one_iff, ← H.herm]
      exact star_mem_one (hyM x (Submodule.mem_sup_left x.2))
    let φ : ↥(L ⊓ rs (𝓞 K) (perp H I)) →ₗ[𝓞 K] 𝓞 K :=
      { toFun := fun x => ⟨H.B x y, hx x⟩
        map_add' := fun a b => by
          apply RingOfIntegers.ext
          show H.B ((a : V) + b) y = H.B a y + H.B b y
          simp
        map_smul' := fun a b => by
          apply RingOfIntegers.ext
          show H.B (a • (b : V)) y = algebraMap (𝓞 K) K a * H.B b y
          rw [← algebraMap_smul K a, map_smul]
          rfl }
    obtain ⟨y', hy', h'⟩ := exists_lattice_rep H hU (perp H I) φ
    have hd : y - y' ∈ I := by
      apply mem_of_perp_perp H I
      intro v hv
      obtain ⟨c, hc, h⟩ := hsat v hv
      have h1 : H.B (c • v) y' = H.B (c • v) y := h' ⟨_, h⟩
      rw [map_smul, LinearMap.smul_apply, LinearMap.smul_apply] at h1
      rw [map_sub, smul_right_injective K hc h1, sub_self]
    have hy'p : y' ∈ perp H I := by
      have := (perp H I).sub_mem hy (hIp hd)
      simpa using this
    exact Submodule.mem_sup.2 ⟨y', ⟨hy', hy'p⟩, y - y', hd, by abel⟩
  · intro hy
    obtain ⟨a, ⟨haL, hap⟩, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
    refine ⟨(perp H I).add_mem hap (hIp hb), fun x hx => ?_⟩
    obtain ⟨c, ⟨hcL, hcp⟩, d, hd, rfl⟩ := Submodule.mem_sup.1 hx
    have h1 : H.B a d = 0 := (mem_perp_iff H I a).1 hap d hd
    have h2 : H.B b c = 0 := by rw [← H.herm, (mem_perp_iff H I c).1 hcp b hb, star_zero]
    have h3 : H.B b d = 0 := hI b hb d hd
    simp only [map_add, LinearMap.add_apply, h1, h2, h3, add_zero]
    exact hint a haL c hcL
end GlobalTheory.UnimodQuot
