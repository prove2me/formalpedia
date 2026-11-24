-- Prove2me | solution 1 for GlobalTheory.ComplexPointsGroup.isContFamily_of_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:56:06.873792+00:00
-- url     : https://prove2.me/submissions/89d2b71c-1e52-47f5-af6a-39b9d6bf786d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsTopologicalGroupComplexPoints

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
open GlobalTheory GlobalTheory.ComplexPointsGroup
variable {T : Type} [TopologicalSpace T]
variable (hv : ∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a))
include hv
namespace GlobalTheory.ComplexPointsGroup
theorem _root_.solution {X : Scheme.{0}} {e : T → (Sp ℂ ⟶ X)}
    (h : ∀ t₀, ∃ P : X.Opens, IsAffineOpen P ∧ ⊤ ≤ e t₀ ⁻¹ᵁ P ∧ IsOpen {t | ⊤ ≤ e t ⁻¹ᵁ P} ∧
      ∀ g : Γ(X, P), ContinuousOn (fun t => valAt' (e t) P g) {t | ⊤ ≤ e t ⁻¹ᵁ P}) :
    IsContFamily e := by
  intro U f O hO
  rw [isOpen_iff_forall_mem_open]
  rintro t₀ ⟨hU, hf⟩
  obtain ⟨P, hP, h₀, hopen, hcont⟩ := h t₀
  obtain ⟨s, hsU, hs₀⟩ := hP.exists_basicOpen_le (V := U) ⟨_, ((hv X _).1 U).1 hU⟩ (((hv X _).1 P).1 h₀)
  obtain ⟨n, g, hg⟩ := exists_eq_pow_mul_of_isAffineOpen X P hP s (resG X hsU f)
  have key : ∀ t, ⊤ ≤ e t ⁻¹ᵁ X.basicOpen s →
      valAt' (e t) U f = valAt' (e t) P g / valAt' (e t) P s ^ n := by
    intro t ht
    have hne := ((hv X (e t)).2.2.2.2.1 P s).1 ht
    obtain ⟨ev, hev⟩ := (hv X (e t)).2.1 _ ht
    have h1 := (hv X (e t)).2.2.1 P _ (X.basicOpen_le s) g ht
    have h2 := (hv X (e t)).2.2.1 P _ (X.basicOpen_le s) s ht
    have h3 := (hv X (e t)).2.2.1 U _ hsU f ht
    have hg' : resG X (X.basicOpen_le s) g = resG X (X.basicOpen_le s) s ^ n * resG X hsU f := hg
    rw [eq_div_iff (pow_ne_zero n hne), ← h1, ← h2, ← h3, hg', hev, hev, hev, map_mul, map_pow, mul_comm]
  have hN : {t | ⊤ ≤ e t ⁻¹ᵁ X.basicOpen s} =
      {t | ⊤ ≤ e t ⁻¹ᵁ P} ∩ (fun t => valAt' (e t) P s) ⁻¹' {0}ᶜ := by
    ext t
    constructor
    · intro ht
      exact ⟨le_trans ht ((e t).preimage_mono (X.basicOpen_le s)), ((hv X (e t)).2.2.2.2.1 P s).1 ht⟩
    · intro ht
      exact ((hv X (e t)).2.2.2.2.1 P s).2 ht.2
  have hNo : IsOpen {t | ⊤ ≤ e t ⁻¹ᵁ X.basicOpen s} := by
    rw [hN]
    exact (hcont s).isOpen_inter_preimage hopen isOpen_compl_singleton
  have hsub : {t | ⊤ ≤ e t ⁻¹ᵁ X.basicOpen s} ⊆ {t | ⊤ ≤ e t ⁻¹ᵁ P} := by
    rw [hN]; exact Set.inter_subset_left
  have hc : ContinuousOn (fun t => valAt' (e t) U f) {t | ⊤ ≤ e t ⁻¹ᵁ X.basicOpen s} := by
    refine ContinuousOn.congr (f := fun t => valAt' (e t) P g / valAt' (e t) P s ^ n) ?_ key
    exact ((hcont g).mono hsub).div (((hcont s).mono hsub).pow n)
      fun t ht => pow_ne_zero n (((hv X (e t)).2.2.2.2.1 P s).1 ht)
  refine ⟨{t | ⊤ ≤ e t ⁻¹ᵁ X.basicOpen s} ∩ (fun t => valAt' (e t) U f) ⁻¹' O, ?_,
    hc.isOpen_inter_preimage hNo hO, ((hv X _).1 _).2 hs₀, hf⟩
  rintro t ⟨ht, hto⟩
  exact ⟨le_trans ht ((e t).preimage_mono hsU), hto⟩
end GlobalTheory.ComplexPointsGroup
