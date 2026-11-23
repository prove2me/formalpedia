-- Prove2me | solution 1 for GlobalTheory.setIntegral_fundamentalDomain_add_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:23:30.357448+00:00
-- url     : https://prove2.me/submissions/b34d3f88-59df-4c38-9a94-3a28a64b24db

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_TileIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MeasureTheory
variable {V κ : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Fintype κ]
namespace GlobalTheory
theorem _root_.solution {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (μ : Measure V) [μ.IsAddHaarMeasure] (b : Module.Basis κ ℝ V)
    (f : V → E) (hb : ∀ γ ∈ Submodule.span ℤ (Set.range b), ∀ v, f (v + γ) = f v) (a : V) :
    ∫ v in ZSpan.fundamentalDomain b, f (v + a) ∂μ = ∫ v in ZSpan.fundamentalDomain b, f v ∂μ := by
  have hA := ZSpan.isAddFundamentalDomain' b μ
  have hT : IsAddFundamentalDomain (Submodule.span ℤ (Set.range b)).toAddSubgroup
      ((fun x => x - a) ⁻¹' ZSpan.fundamentalDomain b) μ := by
    refine IsAddFundamentalDomain.mk' ?_ fun x => ?_
    · exact ((ZSpan.fundamentalDomain_measurableSet b).preimage
        (measurable_sub_const a)).nullMeasurableSet
    · obtain ⟨g, hg, hu⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain b (x - a)
      refine ⟨⟨g, g.2⟩, ?_, ?_⟩
      · change (g : V) + x - a ∈ ZSpan.fundamentalDomain b
        rw [add_sub_assoc]; exact hg
      · rintro ⟨y, hy⟩ h
        change y + x - a ∈ ZSpan.fundamentalDomain b at h
        rw [add_sub_assoc] at h
        exact Subtype.ext (congrArg Subtype.val (hu ⟨y, hy⟩ h))
  have hper : ∀ (g : (Submodule.span ℤ (Set.range b)).toAddSubgroup) (x : V),
      f (g +ᵥ x) = f x := by
    intro g x
    change f ((g : V) + x) = f x
    rw [add_comm]
    exact hb g g.2 x
  rw [hA.setIntegral_eq hT hper]
  have e := (measurePreserving_sub_right μ a).setIntegral_preimage_emb
    (measurableEmbedding_subRight a) (fun y => f (y + a)) (ZSpan.fundamentalDomain b)
  simp only [sub_add_cancel] at e
  exact e.symm
end GlobalTheory
