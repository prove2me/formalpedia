-- Prove2me | solution 1 for GlobalTheory.PointsCompact.continuous_of_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:27:04.595384+00:00
-- url     : https://prove2.me/submissions/179a62b1-ff76-40b2-ad8d-403c5a1b6d88

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CompactSpacePointsPolAV

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
theorem _root_.solution (h1 : ValueRules) (X : Over (Sp ℂ)) (U : X.left.Opens)
    (hU : IsAffineOpen U) {Z : Type} [TopologicalSpace Z] (σ : Z → (𝟙_ (Over (Sp ℂ)) ⟶ X))
    (hσ : ∀ w, ⊤ ≤ (σ w).left ⁻¹ᵁ U)
    (hc : ∀ f : Γ(X.left, U), Continuous fun w => valAt' (σ w).left U f) :
    @Continuous _ _ _ (pointTopology X) σ := by
  refine continuous_generateFrom_iff.2 ?_
  rintro S ⟨V, f, O, hO, rfl⟩
  rw [isOpen_iff_mem_nhds]
  rintro w ⟨hwV, hwO⟩
  have hpU : (σ w).left (default : PrimeSpectrum ℂ) ∈ U := ((h1 _ (σ w).left).1 U).1 (hσ w)
  have hpV : (σ w).left (default : PrimeSpectrum ℂ) ∈ V := ((h1 _ (σ w).left).1 V).1 hwV
  obtain ⟨g, hgV, hpg⟩ := hU.exists_basicOpen_le ⟨_, hpV⟩ hpU
  letI := (X.left.presheaf.map (homOfLE <| X.left.basicOpen_le g).op).hom.toAlgebra
  haveI := hU.isLocalization_basicOpen g
  obtain ⟨⟨a, _, ⟨n, rfl⟩⟩, ha⟩ := IsLocalization.surj (Submonoid.powers g) (resG X.left hgV f)
  simp only [RingHom.algebraMap_toAlgebra] at ha

  have key : ∀ q : Sp ℂ ⟶ X.left, ⊤ ≤ q ⁻¹ᵁ X.left.basicOpen g →
      valAt' q V f * valAt' q U g ^ n = valAt' q U a := by
    intro q hq
    have hqU : ⊤ ≤ q ⁻¹ᵁ U := ((h1 _ q).1 U).2 (X.left.basicOpen_le g (((h1 _ q).1 _).1 hq))
    obtain ⟨e, he⟩ := (h1 _ q).2.1 _ hq
    obtain ⟨e', he'⟩ := (h1 _ q).2.1 _ hqU
    have := congrArg e ha
    rw [map_mul] at this
    rw [← (h1 _ q).2.2.1 V _ hgV f hq, ← (h1 _ q).2.2.1 U _ (X.left.basicOpen_le g) a hq,
      he, he, he', ← map_pow, ← he', ← (h1 _ q).2.2.1 U _ (X.left.basicOpen_le g) _ hq, he]
    simpa using this
  set F : Z → ℂ := fun w => valAt' (σ w).left U a / valAt' (σ w).left U g ^ n with hF
  have hopen : IsOpen {w | valAt' (σ w).left U g ≠ 0} := isOpen_ne_fun (hc g) continuous_const
  have hFc : ContinuousOn F {w | valAt' (σ w).left U g ≠ 0} :=
    (hc a).continuousOn.div ((hc g).pow n).continuousOn (fun w hw => pow_ne_zero _ hw)
  refine Filter.mem_of_superset ((hFc.isOpen_inter_preimage hopen hO).mem_nhds ?_) ?_
  · have hq : ⊤ ≤ (σ w).left ⁻¹ᵁ X.left.basicOpen g := ((h1 _ (σ w).left).1 _).2 hpg
    have hne : valAt' (σ w).left U g ≠ 0 := ((h1 _ (σ w).left).2.2.2.2.1 U g).1 hq
    refine ⟨hne, ?_⟩
    show valAt' (σ w).left U a / valAt' (σ w).left U g ^ n ∈ O
    rw [← key _ hq, mul_div_cancel_right₀ _ (pow_ne_zero _ hne)]
    exact hwO
  · rintro w' ⟨hne, hw'⟩
    have hq : ⊤ ≤ (σ w').left ⁻¹ᵁ X.left.basicOpen g := ((h1 _ (σ w').left).2.2.2.2.1 U g).2 hne
    refine ⟨((h1 _ (σ w').left).1 V).2 (hgV (((h1 _ (σ w').left).1 _).1 hq)), ?_⟩
    have h' : valAt' (σ w').left U a / valAt' (σ w').left U g ^ n ∈ O := hw'
    rwa [← key _ hq, mul_div_cancel_right₀ _ (pow_ne_zero _ hne)] at h'
end GlobalTheory.PointsCompact
