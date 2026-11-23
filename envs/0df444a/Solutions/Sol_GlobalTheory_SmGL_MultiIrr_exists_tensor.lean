-- Prove2me | solution 1 for GlobalTheory.SmGL.MultiIrr.exists_tensor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:39.636886+00:00
-- url     : https://prove2.me/submissions/3833ef2e-ce8b-417b-a4ae-1c20a1b51c37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LowerEquivUpperSwap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsIrreducibleIffOfLinearEquiv
import Theorems.Thm_GlobalTheory_SmGL_MultiIrr_coord_lTensor
import Theorems.Thm_GlobalTheory_SmGL_MultiIrr_exists_sum_coord
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel Matrix
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.MultiIrr
variable {F G H M V W U : Type} [Field F] [Group G] [Group H] [Group M] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup U] [Module F U]
variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] [IsTopologicalGroup H]
omit [TopologicalSpace G] [IsTopologicalGroup G]
namespace GlobalTheory.SmGL.MultiIrr
theorem _root_.solution {P : Subgroup H} (ρ : Representation F P W) {K : Set H} (hK : IsCompact K)
    (hPK : ∀ x, ∃ p : P, ∃ w ∈ K, x = p * w) (f : H → V ⊗[F] W)
    (hf : ∀ (p : P) x, f (p * x) = (ρ p).lTensor V (f x))
    (hs : ∀ᶠ u in nhds (1 : H), ∀ x, f (x * u) = f x) :
    ∃ t : V ⊗[F] smoothPart (ind P ρ), ∀ x, (ev ρ x).lTensor V t = f x := by
  classical
  let b := Module.Basis.ofVectorSpace F V
  have hlc : IsLocallyConstant f := by
    refine (IsLocallyConstant.iff_eventually_eq f).2 fun x => ?_
    have : Filter.Tendsto (fun y => x⁻¹ * y) (nhds x) (nhds 1) :=
      (continuous_const.mul continuous_id).tendsto' _ _ (by simp)
    filter_upwards [this.eventually hs] with y hy
    simpa using hy x
  have hfin : (f '' K).Finite := by
    haveI := isCompact_iff_compactSpace.1 hK
    rw [Set.image_eq_range]
    exact (hlc.comp_continuous continuous_subtype_val).range_finite
  choose s h1 h2 using exists_sum_coord (W := W) b
  let S := hfin.toFinset.biUnion s
  let c : ∀ i, smoothPart (ind P ρ) := fun i => ⟨⟨fun x => coord (b.coord i) W (f x), fun p x => by
      show coord _ W (f (p * x)) = _
      rw [hf, coord_lTensor]⟩, mem_smooth_of_eventually _ (hs.mono fun u hu x => by
      show coord _ W (f (x * u)) = _
      rw [hu])⟩
  refine ⟨∑ i ∈ S, b i ⊗ₜ c i, fun x => ?_⟩
  obtain ⟨p, w, hw, rfl⟩ := hPK x
  rw [hf, h2 (f w) S (Finset.subset_biUnion_of_mem s (hfin.mem_toFinset.2 ⟨w, hw, rfl⟩)), map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.lTensor_tmul, LinearMap.lTensor_tmul]
  exact congrArg _ ((c i).1.2 p w)
end GlobalTheory.SmGL.MultiIrr
