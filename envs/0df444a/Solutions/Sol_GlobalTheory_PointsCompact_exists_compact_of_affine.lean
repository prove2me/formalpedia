-- Prove2me | solution 1 for GlobalTheory.PointsCompact.exists_compact_of_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:41:30.758837+00:00
-- url     : https://prove2.me/submissions/4138c753-37d4-4817-8df6-c1e9400955d8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CompactSpacePointsPolAV
import Theorems.Thm_GlobalTheory_PointsCompact_continuous_of_affine

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
    (U : X.left.Opens) (hU : IsAffineOpen U) {n : ℕ} (r : Fin n → Γ(X.left, U))
    (c : ℂ →+* Γ(X.left, U)) (hc : ∀ a, c a = constFn X.hom U a)
    (hs : Function.Surjective (MvPolynomial.eval₂Hom c r)) :
    ∃ C : Set (𝟙_ (Over (Sp ℂ)) ⟶ X), @IsCompact _ (pointTopology X) C ∧
      ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ X, ⊤ ≤ x.left ⁻¹ᵁ U → (∀ j, ‖valAt' x.left U (r j)‖ ≤ 1) → x ∈ C := by
  letI := pointTopology X
  have hXw : ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ X, x.left ≫ X.hom = 𝟙 _ := fun x => by
    simpa using Over.w x
  set K : Set (Fin n → ℂ) := {z | (∀ j, ‖z j‖ ≤ 1) ∧
    ∀ p ∈ RingHom.ker (MvPolynomial.eval₂Hom c r), MvPolynomial.eval z p = 0} with hK
  have hKc : IsCompact K := by
    refine (isCompact_closedBall (0 : Fin n → ℂ) 1).of_isClosed_subset ?_ ?_
    · have hKe : K = (⋂ j, {z : Fin n → ℂ | ‖z j‖ ≤ 1}) ∩
          ⋂ p ∈ RingHom.ker (MvPolynomial.eval₂Hom c r), {z | MvPolynomial.eval z p = 0} := by
        ext z
        simp [hK]
      rw [hKe]
      refine IsClosed.inter (isClosed_iInter fun j => ?_) (isClosed_biInter fun p _ => ?_)
      · exact isClosed_le (continuous_norm.comp (continuous_apply j)) continuous_const
      · exact isClosed_eq (MvPolynomial.continuous_eval p) continuous_const
    · intro z hz
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (pi_norm_le_iff_of_nonneg zero_le_one).2 hz.1
  let e : K → (Γ(X.left, U) →+* ℂ) := fun z =>
    (MvPolynomial.eval₂Hom c r).liftOfSurjective hs ⟨MvPolynomial.eval z.1, fun p hp => z.2.2 p hp⟩
  have he : ∀ z : K, ∀ p, e z (MvPolynomial.eval₂Hom c r p) = MvPolynomial.eval z.1 p := fun z p =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ _
  have hconst : ∀ z : K, ∀ a, e z (constFn X.hom U a) = a := fun z a => by
    rw [← hc, ← MvPolynomial.eval₂Hom_C c r a, he]
    simp
  have hex := fun z : K => (h2 X U hU (e z) (hconst z))
  choose σ hσ hσu using hex
  have hσc : Continuous σ := continuous_of_affine h1 X U hU σ (fun z => (hσ z).1) (fun f => by
    obtain ⟨p, rfl⟩ := hs f
    refine ((MvPolynomial.continuous_eval p).comp continuous_subtype_val).congr fun z => ?_
    rw [(hσ z).2, he]
    rfl)
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  refine ⟨Set.range σ, isCompact_range hσc, fun x hx hle => ?_⟩
  obtain ⟨ex, hex⟩ := (h1 _ x.left).2.1 U hx
  have hcomp : ex.comp (MvPolynomial.eval₂Hom c r) = MvPolynomial.eval (fun j => valAt' x.left U (r j)) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
    · simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.eval_C]
      rw [← hex, hc]
      exact (h1 _ x.left).2.2.2.2.2 X.hom (hXw x) U a hx
    · simp [hex]
  have hz : (fun j => valAt' x.left U (r j)) ∈ K := by
    refine ⟨hle, fun p hp => ?_⟩
    rw [← hcomp, RingHom.comp_apply, RingHom.mem_ker.1 hp, map_zero]
  refine ⟨⟨_, hz⟩, ?_⟩
  refine (hσu ⟨_, hz⟩ x ⟨hx, fun f => ?_⟩).symm
  obtain ⟨p, rfl⟩ := hs f
  rw [he, ← hcomp, RingHom.comp_apply, hex]
end GlobalTheory.PointsCompact
