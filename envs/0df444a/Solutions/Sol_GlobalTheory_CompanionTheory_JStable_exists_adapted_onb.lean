-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.JStable.exists_adapted_onb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:08:19.848123+00:00
-- url     : https://prove2.me/submissions/07f4cfaf-29aa-4061-972d-923cd91fb6de

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ExistsOrthogonalHermitianSubspace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.JStable
open Module
namespace GlobalTheory.CompanionTheory.JStable
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Submodule ℂ (EuclideanSpace ℂ ι)) :
    ∃ (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι)) (T : Set ι),
      W = Submodule.span ℂ (b '' T) := by
  classical
  let v : Set (EuclideanSpace ℂ ι) := Set.range (fun i => ((stdOrthonormalBasis ℂ W i : W) : EuclideanSpace ℂ ι))
  have hon : Orthonormal ℂ (fun i => ((stdOrthonormalBasis ℂ W i : W) : EuclideanSpace ℂ ι)) :=
    (stdOrthonormalBasis ℂ W).orthonormal.comp_linearIsometry W.subtypeₗᵢ
  have hv : Orthonormal ℂ ((↑) : v → EuclideanSpace ℂ ι) :=
    (orthonormal_subtype_range hon.linearIndependent.injective).2 hon
  obtain ⟨u, bu, hvu, hbu⟩ := hv.exists_orthonormalBasis_extension
  have hcard : Fintype.card u = Fintype.card ι :=
    (finrank_eq_card_basis bu.toBasis).symm.trans finrank_euclideanSpace
  let e : u ≃ ι := Fintype.equivOfCardEq hcard
  refine ⟨bu.reindex e, e '' {x | (x : EuclideanSpace ℂ ι) ∈ v}, ?_⟩
  have himg : (bu.reindex e) '' (e '' {x | (x : EuclideanSpace ℂ ι) ∈ v}) = v := by
    rw [Set.image_image]
    ext y
    simp only [OrthonormalBasis.reindex_apply, Equiv.symm_apply_apply, hbu, Set.mem_image,
      Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨⟨y, hvu hy⟩, hy, rfl⟩
  rw [himg]
  have hr : W.subtype '' Set.range (stdOrthonormalBasis ℂ W) = v := (Set.range_comp _ _).symm
  rw [← hr, Submodule.span_image, ← (stdOrthonormalBasis ℂ W).coe_toBasis,
    (stdOrthonormalBasis ℂ W).toBasis.span_eq, Submodule.map_subtype_top]
end GlobalTheory.CompanionTheory.JStable
