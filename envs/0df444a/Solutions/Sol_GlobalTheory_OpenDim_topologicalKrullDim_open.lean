-- Prove2me | solution 1 for GlobalTheory.OpenDim.topologicalKrullDim_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:22:54.403389+00:00
-- url     : https://prove2.me/submissions/4dac33ad-43c4-4995-84a8-a47c01d0eab5

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TopologicalKrullDimEqOfIsIsoRestrict
import Theorems.Thm_GlobalTheory_OpenDim_ringKrullDim_affineOpen
import Theorems.Thm_GlobalTheory_topologicalKrullDim_eq_of_forall_exists_isOpen
import Theorems.Thm_GlobalTheory_topologicalKrullDim_eq_of_isEmbedding


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.OpenDim
namespace GlobalTheory.OpenDim
theorem _root_.solution (F : Type) [Field F] {Y : Scheme.{0}} [IsIntegral Y]
    (f : Y ⟶ Sp F) [LocallyOfFiniteType f] (V : Y.Opens) (hne : (V : Set Y).Nonempty) :
    topologicalKrullDim (V : Set Y) = topologicalKrullDim Y := by
  let := (Spec.preimage (Y.fromSpecStalk (genericPoint Y) ≫ f)).hom.toAlgebra

  have chart : ∀ (V : Y.Opens) (x : Y), x ∈ V → ∃ U : Y.Opens, IsAffineOpen U ∧ x ∈ U ∧ U ≤ V :=
    fun V x hx ↦ by
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
        Y.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen
      exact ⟨U, hU, hxU, hUV⟩
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨U₀, hU₀, hx₀U₀, -⟩ := chart V x₀ hx₀
  obtain ⟨d₀, -, hd₀⟩ := ringKrullDim_affineOpen F f hU₀ ⟨x₀, hx₀U₀⟩
  have affDim : ∀ U : Y.Opens, IsAffineOpen U → (U : Set Y).Nonempty →
      topologicalKrullDim (U : Set Y) = d₀ := fun U hU hUne ↦ by
    obtain ⟨d, h₁, h₂⟩ := ringKrullDim_affineOpen F f hU hUne
    obtain rfl : d = d₀ := by exact_mod_cast h₂.symm.trans hd₀
    rw [← h₁, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding
      hU.range_fromSpec
  have openDim : ∀ V : Y.Opens, (V : Set Y).Nonempty → topologicalKrullDim (V : Set Y) = d₀ :=
    fun V hV ↦ topologicalKrullDim_eq_of_forall_exists_isOpen hV fun x hx ↦ by
      obtain ⟨U, hU, hxU, hUV⟩ := chart V x hx
      refine ⟨U, U.isOpen, hxU, ?_⟩
      rw [Set.inter_eq_left.mpr hUV]
      exact affDim U hU ⟨x, hxU⟩
  have htop := openDim ⊤ ⟨x₀, trivial⟩
  rw [openDim V ⟨x₀, hx₀⟩, ← htop]
  exact (topologicalKrullDim_eq_of_isEmbedding Topology.IsEmbedding.id
    (Z := ((⊤ : Y.Opens) : Set Y)) (by simp))
end GlobalTheory.OpenDim
