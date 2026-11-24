-- Prove2me | solution 1 for GlobalTheory.SmGL.Stages.tensor_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:50:25.934163+00:00
-- url     : https://prove2.me/submissions/e6e6664e-1f70-4c69-8680-2e543ca0eb05

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyInv
import Theorems.Thm_GlobalTheory_SmGL_Stages_coord_rTensor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Topology Filter
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.Stages
variable {F G M W X Y Z : Type} [Field F] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group M] [TopologicalSpace M] [IsTopologicalGroup M] [AddCommGroup W] [Module F W]
  [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y] [AddCommGroup Z] [Module F Z]
namespace GlobalTheory.SmGL.Stages
theorem _root_.solution {P : Subgroup M} (σ : Representation F P W) {K : Set M} (hK : IsCompact K)
    (hPK : ∀ m, ∃ p : P, ∃ c ∈ K, m = p * c) (ψ : M → W ⊗[F] X)
    (h1 : ∀ (p : P) m, ψ (p * m) = (σ p).rTensor X (ψ m))
    (h2 : ∀ᶠ u in 𝓝 (1 : M), ∀ x, ψ (x * u) = ψ x) :
    ∃ y : smoothPart (ind P σ) ⊗[F] X, ∀ m, (evalAt σ m).rTensor X y = ψ m := by
  classical
  let b := Module.Free.chooseBasis F X
  let E := TensorProduct.equivFinsuppOfBasisRight (M := W) b
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun x => {z | ψ z = ψ x}) fun x _ => by
    have hc : Tendsto (fun z : M => x⁻¹ * z) (𝓝 x) (𝓝 1) :=
      Continuous.tendsto' (by fun_prop) _ _ (by simp)
    exact (hc.eventually h2).mono fun z hz => by simpa using hz x
  let f := fun i => mkInd σ (fun m => E (ψ m) i) (fun p m => by rw [h1, coord_rTensor])
    (h2.mono fun u hu x => by rw [hu])
  have hf : ∀ i, f i ≠ 0 → i ∈ t.biUnion fun x => (E (ψ x)).support := fun i hi => by
    by_contra hn
    apply hi
    ext m
    obtain ⟨p, c, hc, rfl⟩ := hPK m
    obtain ⟨x, hx, hcx⟩ := Set.mem_iUnion₂.1 (ht hc)
    have h0 : E (ψ x) i = 0 := by
      by_contra h0
      exact hn (Finset.mem_biUnion.2 ⟨x, hx, Finsupp.mem_support_iff.2 h0⟩)
    show E (ψ (p * c)) i = 0
    rw [h1, coord_rTensor, show ψ c = ψ x from hcx, h0, map_zero]
  refine ⟨(TensorProduct.equivFinsuppOfBasisRight b).symm (Finsupp.onFinset _ f hf), fun m => ?_⟩
  apply E.injective
  ext i
  rw [coord_rTensor, LinearEquiv.apply_symm_apply]
  rfl
end GlobalTheory.SmGL.Stages
