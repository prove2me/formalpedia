-- Prove2me | solution 1 for GlobalTheory.TraceCount.fibre_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:32:33.344026+00:00
-- url     : https://prove2.me/submissions/f0887c9f-3c57-43bf-bde9-0963cc1c6813

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexCongruenceSubgroupLeAbsNormPow
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardSublatticesIndexFixedTraceLe
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
open GlobalTheory GlobalTheory.TraceCount
namespace GlobalTheory.TraceCount
theorem _root_.solution {R V W : Type} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (f : V →ₗ[R] W) (L M : Submodule R V) (C : Submodule R W) (m s : ℕ)
    (hm : M.toAddSubgroup.relIndex (L ⊓ LinearMap.ker f).toAddSubgroup = m) (hm0 : m ≠ 0)
    (c : Fin s → W) (hc : ∀ i, c i ∈ C)
    (hgen : ∀ y ∈ C, ∃ (r : Fin s → R) (d : W), d ∈ C ∧ y = ∑ i, r i • c i + m • d) :
    {La : Submodule R V | La ≤ L ∧ La.map f = C ∧ La ⊓ LinearMap.ker f = M}.encard ≤ (m ^ s : ℕ) := by
  set S := {La : Submodule R V | La ≤ L ∧ La.map f = C ∧ La ⊓ LinearMap.ker f = M} with hS
  rcases S.eq_empty_or_nonempty with h0 | ⟨L₁, hL₁⟩
  · simp [h0]
  have hlift : ∀ La : S, ∀ y ∈ C, ∃ a ∈ La.1, f a = y := fun La y hy => by
    have : y ∈ La.1.map f := La.2.2.1.symm ▸ hy
    exact this
  choose a ha hfa using fun (La : S) (i : Fin s) => hlift La (c i) (hc i)
  set K₀ := (L ⊓ LinearMap.ker f).toAddSubgroup with hK₀
  have hmem : ∀ (La : S) i, a La i - a ⟨L₁, hL₁⟩ i ∈ K₀ := fun La i =>
    ⟨sub_mem (La.2.1 (ha La i)) (hL₁.1 (ha ⟨L₁, hL₁⟩ i)), by simp [hfa]⟩
  let Φ : S → (Fin s → K₀ ⧸ M.toAddSubgroup.addSubgroupOf K₀) := fun La i => QuotientAddGroup.mk ⟨_, hmem La i⟩
  have hle : ∀ La La' : S, Φ La = Φ La' → La.1 ≤ La'.1 := by
    intro La La' h y hy
    have hML : M ≤ La'.1 := La'.2.2.2 ▸ inf_le_left
    have h1 : ∀ i, a La i ∈ La'.1 := fun i => by
      have h2 := QuotientAddGroup.eq.1 (congrFun h i)
      rw [AddSubgroup.mem_addSubgroupOf] at h2
      have h3 : -(a La i - a ⟨L₁, hL₁⟩ i) + (a La' i - a ⟨L₁, hL₁⟩ i) ∈ La'.1 := hML h2
      have h4 := sub_mem (ha La' i) h3
      convert h4 using 1
      abel
    have hfy : f y ∈ C := La.2.2.1 ▸ Submodule.mem_map_of_mem hy
    obtain ⟨r, d, hd, hyd⟩ := hgen _ hfy
    obtain ⟨b, hb, hfb⟩ := hlift La d hd
    obtain ⟨b', hb', hfb'⟩ := hlift La' d hd
    have h5 : y - (∑ i, r i • a La i + m • b) ∈ M := by
      rw [← La.2.2.2]
      refine ⟨sub_mem hy (add_mem (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (ha La i))
        (nsmul_mem hb _)), ?_⟩
      simp [hfa, hfb, ← hyd]
    have h6 : m • (b - b') ∈ M := by
      have h7 : b - b' ∈ K₀ := ⟨sub_mem (La.2.1 hb) (La'.2.1 hb'), by simp [hfb, hfb']⟩
      have h8 := AddSubgroup.nsmul_index_mem (M.toAddSubgroup.addSubgroupOf K₀) ⟨_, h7⟩
      rw [AddSubgroup.mem_addSubgroupOf] at h8
      have h9 : (M.toAddSubgroup.addSubgroupOf K₀).index = m := hm
      rw [h9] at h8
      exact h8
    have h10 := add_mem (hML h5) (add_mem (Submodule.sum_mem _ fun i (_ : i ∈ Finset.univ) =>
      Submodule.smul_mem _ (r i) (h1 i)) (add_mem (hML h6) (nsmul_mem hb' m)))
    convert h10 using 1
    rw [smul_sub]
    abel
  have hΦ : Function.Injective Φ := fun La La' h => Subtype.ext (le_antisymm (hle _ _ h) (hle _ _ h.symm))
  have hcard : Nat.card (K₀ ⧸ M.toAddSubgroup.addSubgroupOf K₀) = m := hm
  have : Finite (K₀ ⧸ M.toAddSubgroup.addSubgroupOf K₀) := Nat.finite_of_card_ne_zero (hcard ▸ hm0)
  have hfin : Finite S := Finite.of_injective Φ hΦ
  have h11 := Nat.card_le_card_of_injective Φ hΦ
  rw [Nat.card_fun, hcard, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin] at h11
  rw [← (Set.toFinite S).cast_ncard_eq]
  exact_mod_cast h11
end GlobalTheory.TraceCount
