-- Prove2me | solution 1 for GlobalTheory.PointsCompact.compact_of_sections
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:57:44.944918+00:00
-- url     : https://prove2.me/submissions/033b49df-9faa-4e48-849b-0003e2864a12

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CompactSpacePointsPolAV
import Theorems.Thm_GlobalTheory_PointsCompact_exists_compact_of_affine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.PointsCompact
namespace GlobalTheory.PointsCompact
theorem _root_.solution (h1 : ValueRules) (h2 : AffinePoints) (X : Over (Sp ℂ))
    (L : LB X.left) {M : ℕ} (s : Fin (M + 1) → LB.Sec L)
    (hcov : ⨆ i, Out.nonzeroLocus (s i) = ⊤)
    (H : ∀ i, IsAffineOpen (Out.nonzeroLocus (s i)) ∧
      ∃ r : Fin (M + 1) → Γ(X.left, Out.nonzeroLocus (s i)),
        (∀ j k, resG X.left (inf_le_right : Out.nonzeroLocus (s i) ⊓ L.U k ≤ L.U k) ((s j).f k) =
          resG X.left (inf_le_left : Out.nonzeroLocus (s i) ⊓ L.U k ≤ _) (r j) *
          resG X.left (inf_le_right : Out.nonzeroLocus (s i) ⊓ L.U k ≤ L.U k) ((s i).f k)) ∧
        ∃ c : ℂ →+* Γ(X.left, Out.nonzeroLocus (s i)), (∀ a, c a = constFn X.hom _ a) ∧
          Function.Surjective (MvPolynomial.eval₂Hom c r)) :
    @CompactSpace _ (pointTopology X) := by
  letI := pointTopology X
  choose hA r hr c hc hsurj using H
  have hC := fun i => exists_compact_of_affine h1 h2 X _ (hA i) (r i) (c i) (hc i) (hsurj i)
  choose C hCc hCmem using hC
  refine ⟨(isCompact_iUnion hCc).of_isClosed_subset isClosed_univ fun x _ => ?_⟩
  have hx0 : x.left (default : PrimeSpectrum ℂ) ∈ (⨆ i, Out.nonzeroLocus (s i)) := by
    rw [hcov]; trivial
  unfold Out.nonzeroLocus at hx0
  simp only [TopologicalSpace.Opens.mem_iSup] at hx0
  obtain ⟨i, k, hik⟩ := hx0
  set a : Fin (M + 1) → ℂ := fun j => valAt' x.left (L.U k) ((s j).f k) with ha
  obtain ⟨i0, hi0⟩ := Finite.exists_max (fun j => ‖a j‖)
  have hai : a i ≠ 0 := ((h1 _ x.left).2.2.2.2.1 _ _).1 (((h1 _ x.left).1 _).2 hik)
  have hai0 : a i0 ≠ 0 := by
    intro h0
    have := hi0 i
    rw [h0, norm_zero] at this
    exact hai (norm_le_zero_iff.1 this)
  have hb0 : ⊤ ≤ x.left ⁻¹ᵁ X.left.basicOpen ((s i0).f k) := ((h1 _ x.left).2.2.2.2.1 _ _).2 hai0
  have hmem0 : x.left (default : PrimeSpectrum ℂ) ∈ X.left.basicOpen ((s i0).f k) := ((h1 _ x.left).1 _).1 hb0
  have hN : ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus (s i0) := by
    refine ((h1 _ x.left).1 _).2 ?_
    unfold Out.nonzeroLocus
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hmem0⟩
  have hNk : ⊤ ≤ x.left ⁻¹ᵁ (Out.nonzeroLocus (s i0) ⊓ L.U k) :=
    ((h1 _ x.left).1 _).2 ⟨((h1 _ x.left).1 _).1 hN, X.left.basicOpen_le _ hmem0⟩
  refine Set.mem_iUnion.2 ⟨i0, hCmem i0 x hN fun j => ?_⟩
  have hrel : a j = valAt' x.left (Out.nonzeroLocus (s i0)) (r i0 j) * a i0 := by
    obtain ⟨e, he⟩ := (h1 _ x.left).2.1 _ hNk
    have := congrArg e (hr i0 j k)
    rw [map_mul, ← he, ← he, ← he, (h1 _ x.left).2.2.1 _ _ _ _ hNk, (h1 _ x.left).2.2.1 _ _ _ _ hNk,
      (h1 _ x.left).2.2.1 _ _ _ _ hNk] at this
    exact this
  have hle := hi0 j
  rw [hrel, norm_mul] at hle
  have hpos : 0 < ‖a i0‖ := norm_pos_iff.2 hai0
  nlinarith
end GlobalTheory.PointsCompact
