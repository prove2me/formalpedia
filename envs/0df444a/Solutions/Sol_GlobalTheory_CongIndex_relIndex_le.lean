-- Prove2me | solution 1 for GlobalTheory.CongIndex.relIndex_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:04:16.789374+00:00
-- url     : https://prove2.me/submissions/b54a6f58-e943-49e5-ae97-d7f10d7422c1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexCongruenceSubgroupLeAbsNormPow
import Theorems.Thm_GlobalTheory_CongIndex_card_hom_quot_smul_top
import Theorems.Thm_GlobalTheory_CongIndex_finrank_le_finrank_span
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
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.CongIndex
namespace GlobalTheory.CongIndex
theorem _root_.solution : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (G : Subgroup (V ≃ₗ[K] V)) (M : Submodule (𝓞 K) V) (𝔪 : Ideal (𝓞 K)) (B : Subgroup (V ≃ₗ[K] V)), M.FG → 𝔪 ≠ ⊥ → (∀ s ∈ G, s • M = M) → (∀ s ∈ G, (∀ x ∈ M, s x - x ∈ 𝔪 • M) → s ∈ B) → B.relIndex G ≠ 0 ∧ B.relIndex G ≤ Ideal.absNorm 𝔪 ^ (Module.finrank K (Submodule.span K (M : Set V)) ^ 2) := by
  intro K V _ _ _ _ _ _ _ G M 𝔪 B hM h𝔪 hG hB
  have : Module.Finite (𝓞 K) M := Module.Finite.iff_fg.2 hM
  have : Module.IsTorsionFree (𝓞 K) V := Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K V
  have : Module.Flat (𝓞 K) M := inferInstance
  have : Module.FinitePresentation (𝓞 K) M := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 K) M := Module.Flat.projective_of_finitePresentation
  have : Finite (𝓞 K ⧸ 𝔪) := Ideal.finiteQuotientOfFreeOfNeBot 𝔪 h𝔪
  obtain ⟨hfin, hcard⟩ := card_hom_quot_smul_top (R := 𝓞 K) (N := M) 𝔪
  have hmem : ∀ s ∈ G, ∀ x ∈ M, s x ∈ M := by
    intro s hs x hx
    rw [← hG s hs]
    exact Submodule.smul_mem_pointwise_smul x s M hx
  have hmem' : ∀ s ∈ G, ∀ x ∈ 𝔪 • M, s x ∈ 𝔪 • M := by
    intro s hs x hx
    refine Submodule.smul_induction_on hx (fun a ha y hy => ?_) (fun y z hy hz => ?_)
    · rw [LinearMapClass.map_smul_of_tower]
      exact Submodule.smul_mem_smul ha (hmem s hs y hy)
    · rw [map_add]; exact Submodule.add_mem _ hy hz
  let ρ : G → (M →ₗ[𝓞 K] M) := fun s =>
    (((s : V ≃ₗ[K] V) : V →ₗ[K] V).restrictScalars (𝓞 K)).restrict (hmem s s.2)
  let Φ : G → (M →ₗ[𝓞 K] M ⧸ (𝔪 • ⊤ : Submodule (𝓞 K) M)) := fun s => (Submodule.mkQ _).comp (ρ s)
  have hΦ : ∀ s t : G, Φ s = Φ t → s⁻¹ * t ∈ B.subgroupOf G := by
    intro s t hst
    refine hB _ (s⁻¹ * t).2 fun x hx => ?_
    have h1 : ρ t ⟨x, hx⟩ - ρ s ⟨x, hx⟩ ∈ (𝔪 • ⊤ : Submodule (𝓞 K) M) :=
      (Submodule.Quotient.eq _).1 (LinearMap.congr_fun hst ⟨x, hx⟩).symm
    have h2 : (t : V ≃ₗ[K] V) x - (s : V ≃ₗ[K] V) x ∈ 𝔪 • M := by
      have := Submodule.mem_map_of_mem (f := M.subtype) h1
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype] at this
      exact this
    have h3 := hmem' _ (s⁻¹).2 _ h2
    simpa using h3
  let Ψ : G ⧸ B.subgroupOf G → _ := fun q => Φ q.out
  have hΨ : Function.Injective Ψ := by
    intro q q' h
    rw [← q.out_eq, ← q'.out_eq]
    exact QuotientGroup.eq.2 (hΦ _ _ h)
  have : Finite (G ⧸ B.subgroupOf G) := Finite.of_injective Ψ hΨ
  refine ⟨Subgroup.index_ne_zero_of_finite, ?_⟩
  refine (Nat.card_le_card_of_injective Ψ hΨ).trans (hcard.trans ?_)
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact Nat.pow_le_pow_right Nat.card_pos (Nat.pow_le_pow_left (finrank_le_finrank_span M) 2)
end GlobalTheory.CongIndex
