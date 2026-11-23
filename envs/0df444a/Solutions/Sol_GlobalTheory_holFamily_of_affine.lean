-- Prove2me | solution 1 for GlobalTheory.holFamily_of_affine
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:01:38.949816+00:00
-- url     : https://prove2.me/submissions/0765942a-07f1-487a-a6fb-82388a8c887c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback

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
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution
    (hv : (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)))
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Set E) (Z : Scheme.{0}) (c : E → (Sp ℂ ⟶ Z))
    (hc : ∀ w ∈ W, ∃ V : Z.Opens, IsAffineOpen V ∧ ⊤ ≤ c w ⁻¹ᵁ V ∧ IsOpen {w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ V} ∧
      ∀ g : Γ(Z, V), DifferentiableOn ℂ (fun w => valAt' (c w) V g) {w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ V})
    (U : Z.Opens) (f : Γ(Z, U)) :
    IsOpen {w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun w => valAt' (c w) U f) {w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ U} := by
  have hpt : ∀ (Y : Scheme.{0}) (x : Sp ℂ ⟶ Y) (O : Y.Opens),
      ⊤ ≤ x ⁻¹ᵁ O ↔ x (default : PrimeSpectrum ℂ) ∈ O := fun Y x O => (hv Y x).1 O

  have key : ∀ w₀ ∈ {w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ U}, ∃ N : Set E, IsOpen N ∧ w₀ ∈ N ∧
      N ⊆ {w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (c w) U f) N := by
    rintro w₀ ⟨hw₀, hU₀⟩
    obtain ⟨V, hVa, hV₀, hVo, hVd⟩ := hc w₀ hw₀
    obtain ⟨g, hgU, hg₀⟩ := hVa.exists_basicOpen_le (V := U)
      ⟨c w₀ (default : PrimeSpectrum ℂ), (hpt _ _ _).1 hU₀⟩ ((hpt _ _ _).1 hV₀)
    have hDV : Z.basicOpen g ≤ V := Z.basicOpen_le g
    let := hVa.isLocalization_basicOpen g
    obtain ⟨⟨h, ⟨_, n, rfl⟩⟩, hh⟩ := IsLocalization.surj (Submonoid.powers g) (resG Z hgU f)
    have hh' : resG Z hgU f * resG Z hDV g ^ n = resG Z hDV h := by
      rw [← map_pow]
      exact hh
    refine ⟨{w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ V} ∩ (fun w => valAt' (c w) V g) ⁻¹' {0}ᶜ,
      (hVd g).continuousOn.isOpen_inter_preimage hVo isOpen_compl_singleton, ?_, ?_, ?_⟩
    · refine ⟨⟨hw₀, hV₀⟩, ?_⟩
      exact ((hv Z (c w₀)).2.2.2.2.1 V g).1 ((hpt _ _ _).2 hg₀)
    · rintro w ⟨⟨hw, -⟩, hg⟩
      have hD : ⊤ ≤ c w ⁻¹ᵁ Z.basicOpen g := ((hv Z (c w)).2.2.2.2.1 V g).2 hg
      exact ⟨hw, (hpt _ _ _).2 (hgU ((hpt _ _ _).1 hD))⟩
    · have hq : DifferentiableOn ℂ (fun w => valAt' (c w) V h * (valAt' (c w) V g ^ n)⁻¹)
          ({w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ V} ∩ (fun w => valAt' (c w) V g) ⁻¹' {0}ᶜ) :=
        by
        apply DifferentiableOn.fun_mul
        · exact (hVd h).mono Set.inter_subset_left
        · apply DifferentiableOn.fun_inv
          · exact ((hVd g).mono Set.inter_subset_left).fun_pow n
          · intro w hw
            exact pow_ne_zero _ hw.2
      refine hq.congr fun w ⟨⟨hw, hwV⟩, hg⟩ => ?_
      have hg' : valAt' (c w) V g ≠ 0 := hg
      have hD : ⊤ ≤ c w ⁻¹ᵁ Z.basicOpen g := ((hv Z (c w)).2.2.2.2.1 V g).2 hg'
      obtain ⟨e, he⟩ := (hv Z (c w)).2.1 _ hD
      have h1 := (hv Z (c w)).2.2.1 U _ hgU f hD
      have h2 := (hv Z (c w)).2.2.1 V _ hDV g hD
      have h3 := (hv Z (c w)).2.2.1 V _ hDV h hD
      rw [he] at h1 h2 h3
      have h4 := congrArg e hh'
      rw [map_mul, map_pow, h1, h2, h3] at h4
      rw [← div_eq_mul_inv]
      exact eq_div_of_mul_eq (pow_ne_zero _ hg') h4
  refine ⟨isOpen_iff_forall_mem_open.2 fun w hw => ?_, fun w hw => ?_⟩
  · obtain ⟨N, hNo, hwN, hNs, -⟩ := key w hw
    exact ⟨N, hNs, hNo, hwN⟩
  · obtain ⟨N, hNo, hwN, -, hNd⟩ := key w hw
    exact (hNd.differentiableAt (hNo.mem_nhds hwN)).differentiableWithinAt
end GlobalTheory
