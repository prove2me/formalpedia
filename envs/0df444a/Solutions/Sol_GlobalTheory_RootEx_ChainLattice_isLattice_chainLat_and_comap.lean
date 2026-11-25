-- Prove2me | solution 1 for GlobalTheory.RootEx.ChainLattice.isLattice_chainLat_and_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:07:47.735529+00:00
-- url     : https://prove2.me/submissions/8f39cc8e-2d1d-467e-9ee0-1dbd97ebd1fc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ScaledBasisMemChainLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ImportsAlt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLatticeChainLatAndComap
import Theorems.Thm_GlobalTheory_RootEx_ChainLattice_exists_smul_mem
import Theorems.Thm_GlobalTheory_RootEx_ChainLattice_span_eq_top_of_smul_mem
import Theorems.Thm_GlobalTheory_RootEx_UnfoldShape_inX_apply
import Theorems.Thm_GlobalTheory_RootEx_UnfoldShape_inX_mem_chainLat
import Theorems.Thm_GlobalTheory_RootEx_UnfoldShape_scaled_basis_mem_chainLattice


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.ChainLattice
namespace GlobalTheory.RootEx.ChainLattice
theorem _root_.solution :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (n : Type) [Fintype n] [DecidableEq n] (c : ℕ),
      (∀ (ϖ : 𝒪[k]), (ϖ : k) ≠ 0 → ∀ L : Submodule 𝒪[k] (n → k), Submodule.IsLattice k L →
        Submodule.IsLattice k (chainLat ϖ c L)) ∧
      ∀ Λ : Submodule 𝒪[k] (n ⊕ Fin c → k), Submodule.IsLattice k Λ →
        Submodule.IsLattice k (Λ.comap (inX k n c)) := by
  intro k _ _ _ _ n _ _ c
  refine ⟨fun ϖ hϖ L hL => ⟨?_, ?_⟩, fun Λ hΛ => ⟨?_, ?_⟩⟩
  · exact (hL.fg.map _).sup (Submodule.fg_span (Set.finite_range _))
  · rw [eq_top_iff]
    intro v _
    have hv : v = inX k n c (fun r => v (Sum.inl r)) +
        ∑ i : Fin c, (v (Sum.inr i) / (ϖ : k) ^ ((i : ℕ) + 1)) •
          ((ϖ : k) ^ ((i : ℕ) + 1) • aux k n i) := by
      have h : ∀ i : Fin c, (v (Sum.inr i) / (ϖ : k) ^ ((i : ℕ) + 1)) •
          ((ϖ : k) ^ ((i : ℕ) + 1) • aux k n i) = v (Sum.inr i) • aux k n i := by
        intro i
        rw [smul_smul, div_mul_cancel₀ _ (pow_ne_zero _ hϖ)]
      simp only [h]
      funext j
      rcases j with r | j
      · simp [inX_apply, aux, Finset.sum_apply]
      · simp [inX_apply, aux, Finset.sum_apply, Pi.single_apply]
    rw [hv]
    refine Submodule.add_mem _ ?_ (Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (scaled_basis_mem_chainLattice ϖ L i)))
    obtain ⟨a, ha, hav⟩ := exists_smul_mem (K := k) L (v := fun r => v (Sum.inl r))
      (by rw [hL.span_eq_top]; trivial)
    have h1 : algebraMap 𝒪[k] k a ≠ 0 := by simpa using ha
    have : inX k n c (fun r => v (Sum.inl r)) =
        (algebraMap 𝒪[k] k a)⁻¹ • inX k n c (a • fun r => v (Sum.inl r)) := by
      rw [map_smul, ← algebraMap_smul k a, smul_smul, inv_mul_cancel₀ h1, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (inX_mem_chainLat.2 hav))
  · refine Submodule.fg_of_fg_map_injective (inX k n c) ?_
      (hΛ.fg.of_le (Submodule.map_comap_le _ _))
    intro x y hxy
    funext r
    have := congrFun hxy (Sum.inl r)
    simpa [inX_apply] using this
  · refine span_eq_top_of_smul_mem _ fun v => ?_
    obtain ⟨a, ha, hav⟩ := exists_smul_mem (K := k) Λ (v := inX k n c v)
      (by rw [hΛ.span_eq_top]; trivial)
    exact ⟨a, ha, by rw [Submodule.mem_comap, map_smul]; exact hav⟩
end GlobalTheory.RootEx.ChainLattice
