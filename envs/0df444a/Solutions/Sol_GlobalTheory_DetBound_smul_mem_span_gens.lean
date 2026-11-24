-- Prove2me | solution 1 for GlobalTheory.DetBound.smul_mem_span_gens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:27:41.878532+00:00
-- url     : https://prove2.me/submissions/204cebed-54be-4eae-8f2b-5ee9e987b637

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodTraceIntegral
import Theorems.Thm_GlobalTheory_DetBound_inK_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
noncomputable section
open GlobalTheory GlobalTheory.DetBound
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
namespace GlobalTheory.DetBound
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] {c : Ideal (OF E)}
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type} [Field K] [Algebra O K]
    [IsFractionRing O K] {D : O} {I : Type} [Fintype I] {φ : I → E →+* K} (hφ : IsCMTypeIn φ)
    {H : Type} [AddCommGroup H] [Module O H] {ρ : orderC c →+* Module.End O H} {Fil : Submodule O H}
    {B : LinearMap.BilinForm O H} (hL : IsCMLattice φ ρ Fil B) (hE : EigenClaims φ ρ Fil B D) {e f : I → H}
    (hG : IsGens φ ρ e f) (e' : I → Fil) (he' : ∀ i, (e' i : H) = e i) (x : Fil) :
    D • x ∈ Submodule.span O (Set.range e') := by
  haveI : Module.Free O H := hL.1
  have hind : iSupIndep (fun σ : E →+* K => eigK ρ σ) := hE.1.submodule_iSupIndep
  have hxK : inK (O := O) K H (D • (x : H)) ∈ ⨆ i, eigK ρ (φ i) := by
    rw [← hL.2.2.2.2.2.1]
    exact Submodule.tmul_mem_baseChange_of_mem 1 (Fil.smul_mem D x.2)
  obtain ⟨F, hF, hFs⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 (hE.2.2.1.2 (x : H))
  have hzero : ∀ σ, σ ∉ Set.range φ → F σ = 0 := by
    intro σ₀ hσ₀
    apply inK_injective (O := O) K H
    rw [map_zero]
    have h1 : inK (O := O) K H (F σ₀) ∈ eigK ρ σ₀ := hF σ₀
    have h2 : inK (O := O) K H (F σ₀) ∈ ⨆ (j : E →+* K) (_ : j ≠ σ₀), eigK ρ j := by
      have hsum : inK (O := O) K H (F σ₀) = inK (O := O) K H (D • (x : H)) - ∑ σ ∈ F.support.erase σ₀, inK (O := O) K H (F σ) := by
        rw [← hFs, Finsupp.sum, map_sum]
        by_cases hm : σ₀ ∈ F.support
        · rw [← Finset.add_sum_erase _ _ hm, add_sub_cancel_right]
        · rw [Finsupp.notMem_support_iff.1 hm, map_zero, Finset.erase_eq_of_notMem hm, sub_self]
      rw [hsum]
      refine Submodule.sub_mem _ ?_ (Submodule.sum_mem _ fun σ hσ => ?_)
      · have hle : (⨆ i, eigK ρ (φ i)) ≤ ⨆ (j : E →+* K) (_ : j ≠ σ₀), eigK ρ j := iSup_le fun i =>
          le_iSup₂_of_le (f := fun (j : E →+* K) (_ : j ≠ σ₀) => eigK ρ j) (φ i) (fun h => hσ₀ ⟨i, h⟩) le_rfl
        exact hle hxK
      · exact (le_iSup₂_of_le (f := fun (j : E →+* K) (_ : j ≠ σ₀) => eigK ρ j) σ
          (Finset.ne_of_mem_erase hσ) le_rfl) (hF σ)
    exact Submodule.disjoint_def.1 (hind σ₀) _ h1 h2
  have hH : D • (x : H) ∈ Submodule.span O (Set.range e) := by
    rw [← hFs, Finsupp.sum]
    refine Submodule.sum_mem _ fun σ _ => ?_
    by_cases hσ : σ ∈ Set.range φ
    · obtain ⟨i, rfl⟩ := hσ
      have h := hF (φ i)
      rw [(hG i).1, Submodule.mem_span_singleton] at h
      obtain ⟨a, ha⟩ := h
      rw [← ha]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [hzero σ hσ]; exact Submodule.zero_mem _
  have hspan : Submodule.span O (Set.range e) = (Submodule.span O (Set.range e')).map Fil.subtype := by
    rw [Submodule.map_span, ← Set.range_comp]
    congr 2
    funext i
    exact (he' i).symm
  rw [hspan] at hH
  obtain ⟨y, hy, hyx⟩ := hH
  have : y = D • x := Subtype.ext hyx
  exact this ▸ hy
end GlobalTheory.DetBound
