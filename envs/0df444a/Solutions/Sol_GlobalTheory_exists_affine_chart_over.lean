-- Prove2me | solution 1 for GlobalTheory.exists_affine_chart_over
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:47:55.44527+00:00
-- url     : https://prove2.me/submissions/0b0ec466-8227-484f-982c-98e5b14a1607

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanFinrankMaximalIdealLeNcardOfLeSupSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing
open GlobalTheory
universe u
open AlgebraicGeometry CategoryTheory Topology
namespace GlobalTheory
theorem _root_.solution {O : Type u} [CommRing O] {X : Scheme.{u}} (f : X ⟶ Spec (.of O))
    (x : X) : ∃ (A : Type u) (_ : CommRing A) (_ : Algebra O A) (j : Spec (.of A) ⟶ X)
      (_ : IsOpenImmersion j) (q : PrimeSpectrum A), j q = x ∧
      j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap O A)) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hU : IsAffineOpen U := hU
  let φ := Spec.preimage (hU.fromSpec ≫ f)
  obtain ⟨q, hq⟩ : x ∈ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    exact hxU
  exact ⟨Γ(X, U), inferInstance, φ.hom.toAlgebra, hU.fromSpec, inferInstance, q, hq,
    (Spec.map_preimage _).symm⟩
end GlobalTheory
