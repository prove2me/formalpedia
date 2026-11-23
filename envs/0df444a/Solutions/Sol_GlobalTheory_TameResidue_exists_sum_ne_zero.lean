-- Prove2me | solution 1 for GlobalTheory.TameResidue.exists_sum_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:24:36.703809+00:00
-- url     : https://prove2.me/submissions/af2e2bbc-f0de-492b-825b-45dec8e165ca

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FiniteSeparableOfSumMem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory GlobalTheory.TameResidue
namespace GlobalTheory.TameResidue
theorem _root_.solution {D k K : Type} [Group D] [Fintype D] [Field k] [Field K] [Algebra k K]
    (φ : D →* (K ≃ₐ[k] K)) (h : (Nat.card φ.ker : K) ≠ 0) : ∃ w : K, ∑ g, φ g w ≠ 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  have hf : Function.Injective (fun σ : K ≃ₐ[k] K => (σ : K →* K)) :=
    fun σ τ hστ => AlgEquiv.ext fun x => DFunLike.congr_fun hστ x
  have hli := (linearIndependent_monoidHom K K).comp _ hf
  have hfib : ∀ σ ∈ Finset.univ.image φ,
      (Finset.univ.filter fun g => φ g = σ).card = Nat.card φ.ker := by
    intro σ hσ
    obtain ⟨g0, -, rfl⟩ := Finset.mem_image.1 hσ
    rw [MonoidHom.card_fiber_eq_of_mem_range φ ⟨g0, rfl⟩ ⟨1, rfl⟩, map_one,
      ← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun g => by simp [MonoidHom.mem_ker])
  have hsum : ∀ w : K, ∑ g, φ g w = ∑ σ ∈ Finset.univ.image φ, (Nat.card φ.ker : K) * σ w := by
    intro w
    rw [← Finset.sum_fiberwise_of_maps_to (g := φ) (t := Finset.univ.image φ)
      (fun g _ => Finset.mem_image_of_mem φ (Finset.mem_univ g))]
    refine Finset.sum_congr rfl fun σ hσ => ?_
    rw [Finset.sum_congr rfl (fun g hg => by rw [(Finset.mem_filter.1 hg).2]), Finset.sum_const,
      hfib σ hσ, nsmul_eq_mul]
  refine h (linearIndependent_iff'.1 hli (Finset.univ.image φ) (fun _ => (Nat.card φ.ker : K)) ?_ (φ 1)
    (Finset.mem_image_of_mem _ (Finset.mem_univ 1)))
  funext w
  have hw := hcon w
  rw [hsum w] at hw
  simpa [Finset.sum_apply] using hw
end GlobalTheory.TameResidue
