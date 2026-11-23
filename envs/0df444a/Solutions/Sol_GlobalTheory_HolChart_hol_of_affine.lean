-- Prove2me | solution 1 for GlobalTheory.HolChart.hol_of_affine
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:01:43.468366+00:00
-- url     : https://prove2.me/submissions/06e66852-3db2-4a2e-84da-3a0490e5bf64

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEtaleCoordsVanishing

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
open GlobalTheory GlobalTheory.HolChart
namespace GlobalTheory.HolChart
theorem _root_.solution
    (hval : (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)))
    {g : ℕ} {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {W : Set (Fin g → ℂ)} (hW : IsOpen W)
    (s : (Fin g → ℂ) → (Sp ℂ ⟶ X)) (hs : ∀ w ∈ W, ⊤ ≤ s w ⁻¹ᵁ U)
    (hd : ∀ a : Γ(X, U), DifferentiableOn ℂ (fun w => valAt' (s w) U a) W)
    (V : X.Opens) (f : Γ(X, V)) :
    IsOpen {w | w ∈ W ∧ ⊤ ≤ s w ⁻¹ᵁ V} ∧
      DifferentiableOn ℂ (fun w => valAt' (s w) V f) {w | w ∈ W ∧ ⊤ ≤ s w ⁻¹ᵁ V} := by
  have key : ∀ w₀ ∈ {w | w ∈ W ∧ ⊤ ≤ s w ⁻¹ᵁ V}, {w | w ∈ W ∧ ⊤ ≤ s w ⁻¹ᵁ V} ∈ 𝓝 w₀ ∧
      DifferentiableAt ℂ (fun w => valAt' (s w) V f) w₀ := by
    rintro w₀ ⟨hw₀, hV⟩
    obtain ⟨h, hhV, hh⟩ := hU.exists_basicOpen_le (V := V) ⟨_, ((hval X (s w₀)).1 V).1 hV⟩
      (((hval X (s w₀)).1 U).1 (hs w₀ hw₀))
    have hB₀ : ⊤ ≤ s w₀ ⁻¹ᵁ X.basicOpen h := ((hval X (s w₀)).1 _).2 hh
    have hne₀ : valAt' (s w₀) U h ≠ 0 := ((hval X (s w₀)).2.2.2.2.1 U h).1 hB₀
    have hWn : W ∈ 𝓝 w₀ := hW.mem_nhds hw₀
    have hda : ∀ a : Γ(X, U), DifferentiableAt ℂ (fun w => valAt' (s w) U a) w₀ := fun a =>
      (hd a w₀ hw₀).differentiableAt hWn
    have hN : ∀ᶠ w in 𝓝 w₀, w ∈ W ∧ valAt' (s w) U h ≠ 0 :=
      Filter.Eventually.and hWn ((hda h).continuousAt.eventually_ne hne₀)
    have _ := hU.isLocalization_basicOpen h
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj h (resG X hhV f)
    refine ⟨hN.mono fun w hw => ⟨hw.1, ?_⟩, ?_⟩
    · exact ((hval X (s w)).1 V).2
        (hhV (((hval X (s w)).1 _).1 (((hval X (s w)).2.2.2.2.1 U h).2 hw.2)))
    · have hq : DifferentiableAt ℂ (fun w => valAt' (s w) U a * (valAt' (s w) U h ^ n)⁻¹) w₀ :=
        (hda a).mul (((hda h).pow n).inv (pow_ne_zero n hne₀))
      refine DifferentiableAt.congr_of_eventuallyEq hq (hN.mono fun w hw => ?_)
      have hB : ⊤ ≤ s w ⁻¹ᵁ X.basicOpen h := ((hval X (s w)).2.2.2.2.1 U h).2 hw.2
      obtain ⟨ev, hev⟩ := (hval X (s w)).2.1 _ hB
      have r1 := (hval X (s w)).2.2.1 V _ hhV f hB
      have r2 := (hval X (s w)).2.2.1 U _ (X.basicOpen_le h) a hB
      have r3 := (hval X (s w)).2.2.1 U _ (X.basicOpen_le h) h hB
      have ha' : resG X hhV f * resG X (X.basicOpen_le h) h ^ n = resG X (X.basicOpen_le h) a := ha
      have := congrArg ev ha'
      rw [map_mul, map_pow, ← hev, ← hev, ← hev, r1, r2, r3] at this
      show valAt' (s w) V f = valAt' (s w) U a * (valAt' (s w) U h ^ n)⁻¹
      rw [← this, mul_inv_cancel_right₀ (pow_ne_zero n hw.2)]
  exact ⟨isOpen_iff_mem_nhds.2 fun w hw => (key w hw).1,
    fun w hw => (key w hw).2.differentiableWithinAt⟩
end GlobalTheory.HolChart
