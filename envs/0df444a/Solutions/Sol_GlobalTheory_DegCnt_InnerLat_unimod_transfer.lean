-- Prove2me | solution 1 for GlobalTheory.DegCnt.InnerLat.unimod_transfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:54:41.841218+00:00
-- url     : https://prove2.me/submissions/3906b3f6-af1d-4c6d-97d7-e45b1b07b990

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairInnerLatticesUnimodularPrimitive
import Theorems.Thm_GlobalTheory_DegCnt_InnerLat_exists_mult
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HermLat_isLatMod_top_bot_iff
import Theorems.Thm_GlobalTheory_HermLat_mem_dual_iff
import Theorems.Thm_GlobalTheory_HermLat_mem_perp_iff
import Theorems.Thm_GlobalTheory_UnimodQuot_isUnimodMod_quot
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
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.InnerLat
open GlobalTheory.UnimodQuot
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.DegCnt.InnerLat
theorem _root_.solution [FiniteDimensional K V] (H : HermSpace K V) {Λ : Submodule (𝓞 K) V} (hU : IsUnimod H Λ)
    {X U I : Submodule K V} (hX : ∀ x ∈ X, ∀ y ∈ X, H.B x y = 0) (hUX : U ≤ perp H X)
    (h1 : perp H X ≤ U ⊔ X) (h2 : U ⊓ X = I) :
    IsUnimodMod H (rs (𝓞 K) U ⊓ (Λ ⊔ rs (𝓞 K) X)) U I := by
  have hΛ := (isLatMod_top_bot_iff Λ).1 hU.1
  obtain ⟨⟨⟨N, hN, hNe⟩, hsp⟩, hd⟩ := isUnimodMod_quot H hU hX
  have hXp : X ≤ perp H X := fun x hx => (mem_perp_iff H X x).2 (hX x hx)
  set M := (Λ ⊓ rs (𝓞 K) (perp H X)) ⊔ rs (𝓞 K) X with hM
  set L := rs (𝓞 K) U ⊓ (Λ ⊔ rs (𝓞 K) X) with hL
  have hMp : ∀ m ∈ M, m ∈ perp H X := fun m hm => hsp ▸ Submodule.subset_span hm
  have hLM : L ≤ M := by
    rintro y ⟨hyU, hy⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
    refine Submodule.add_mem_sup ⟨ha, ?_⟩ hb
    have := (perp H X).sub_mem (hUX hyU) (hXp hb)
    simpa using this
  have hML : ∀ m ∈ M, m ∈ U → m ∈ L := fun m hm hmU =>
    ⟨hmU, (sup_le_sup_right inf_le_left _ : M ≤ Λ ⊔ rs (𝓞 K) X) hm⟩
  have hdec : ∀ m ∈ M, ∃ l ∈ L, m - l ∈ X := by
    intro m hm
    obtain ⟨u, hu, x, hx, rfl⟩ := Submodule.mem_sup.1 (h1 (hMp m hm))
    refine ⟨u, hML u ?_ hu, by simpa using hx⟩
    have := M.sub_mem hm (Submodule.mem_sup_right (show x ∈ rs (𝓞 K) X from hx))
    simpa using this
  have hspan : Submodule.span K (L : Set V) = U := by
    apply le_antisymm
    · rw [Submodule.span_le]
      exact fun y hy => hy.1
    · intro v hv
      obtain ⟨c, hc, h⟩ := exists_mult hΛ v
      rw [← Submodule.smul_mem_iff _ hc]
      exact Submodule.subset_span ⟨U.smul_mem c hv, Submodule.mem_sup_left h⟩
  refine ⟨⟨?_, hspan⟩, ?_⟩
  · obtain ⟨s, rfl⟩ := hN
    have hs : ∀ m : s, ∃ l ∈ L, (m : V) - l ∈ X := fun m =>
      hdec m (hNe ▸ Submodule.mem_sup_left (Submodule.subset_span m.2))
    choose f hf hfX using hs
    have hfL : Submodule.span (𝓞 K) (Set.range f) ≤ L := by
      rw [Submodule.span_le]
      rintro _ ⟨m, rfl⟩
      exact hf m
    have hle : M ≤ Submodule.span (𝓞 K) (Set.range f) ⊔ rs (𝓞 K) X := by
      rw [hNe]
      refine sup_le ?_ le_sup_right
      rw [Submodule.span_le]
      intro m hm
      exact Submodule.mem_sup.2 ⟨f ⟨m, hm⟩, Submodule.subset_span ⟨_, rfl⟩, _, hfX ⟨m, hm⟩, by abel⟩
    refine ⟨Submodule.span (𝓞 K) (Set.range f), Submodule.fg_span (Set.finite_range f), le_antisymm ?_ ?_⟩
    · intro y hy
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hle (hLM hy))
      refine Submodule.add_mem_sup ha (show b ∈ I from h2 ▸ ⟨?_, hb⟩)
      have := U.sub_mem hy.1 (hfL ha).1
      simpa using this
    · refine sup_le hfL fun x hx => ?_
      have hx' : x ∈ U ⊓ X := h2 ▸ hx
      exact ⟨hx'.1, Submodule.mem_sup_right hx'.2⟩
  · ext y
    rw [mem_dual_iff, hspan]
    constructor
    · rintro ⟨hy, h⟩
      refine hML y ?_ hy
      rw [← hd, mem_dual_iff, hsp]
      refine ⟨hUX hy, fun m hm => ?_⟩
      obtain ⟨l, hl, hx⟩ := hdec m hm
      have h0 := (mem_perp_iff H X y).1 (hUX hy) _ hx
      rw [map_sub, sub_eq_zero] at h0
      rw [h0]
      exact h l hl
    · intro hy
      have := hLM hy
      rw [← hd, mem_dual_iff] at this
      exact ⟨hy.1, fun x hx => this.2 x (hLM hx)⟩
end GlobalTheory.DegCnt.InnerLat
