-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ultra.exists_limit_point
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:37:28.492804+00:00
-- url     : https://prove2.me/submissions/7f34b861-38c6-4a3d-a24d-77c34f70f8e3

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_CubeTheorem_SchemeModels
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteAffineCover
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsProperSpreadsOut
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_base_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_exists_family
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_exists_finite_affine_cover
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_exists_of_finite
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_exists_pt_of_isLocalRing
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_homOf_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_rep_homOf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ultra
variable {R₀ R : Type} [CommRing R₀] [CommRing R] {X Y : Scheme.{0}}
  (f₀ : X ⟶ Spec (CommRingCat.of R₀))
variable {f₀}
variable (f₀)
variable {ι : Type} (U : Ultrafilter ι) {T V K : ι → Type} [∀ i, CommRing (T i)]
  [∀ i, CommRing (V i)] [∀ i, IsDomain (V i)] [∀ i, ValuationRing (V i)] [∀ i, Field (K i)]
  [∀ i, Algebra (V i) (K i)] [∀ i, IsFractionRing (V i) (K i)]
  (ψ : ∀ i, R₀ →+* T i)
  (a : ∀ i, Spec (CommRingCat.of (K i)) ⟶ pullback f₀ (Spec.map (CommRingCat.ofHom (ψ i))))
  (β : ∀ i, T i →+* V i)
namespace GlobalTheory.CompanionTheory.Ultra
theorem _root_.solution [CompactSpace X] (φ : R₀ →+* R)
    (hsq : ∀ i, a i ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom ((algebraMap (V i) (K i)).comp (β i))))
    (ρ : R →+* Ult U V) (hρ : ∀ r, ρ (φ r) = mk U (fun i => β i (ψ i r))) :
    ∃ (W₁ : X.affineOpens) (h₁ : ∀ i, Γ(X, W₁.1) → K i) (P : Γ(X, W₁.1) →+* Ult U K),
      Rep U h₁ P ∧
      (∀ᶠ i in (U : Filter ι), ∃ p : Γ(X, W₁.1) →+* K i, ⇑p = h₁ i ∧
        a i ≫ pullback.fst _ _ = pt W₁ p) ∧
      P.comp (baseHom f₀ W₁) = (algebraMap (Ult U V) (Ult U K)).comp (ρ.comp φ) := by
  obtain ⟨S, hSf, -, hS2⟩ := exists_finite_affine_cover (⊤ : X.Opens) (by simpa using isCompact_univ)
  have hQ : ∀ᶠ i in (U : Filter ι), ∃ W ∈ S, ∃ p : Γ(X, W.1) →+* K i,
      a i ≫ pullback.fst _ _ = pt W p := by
    refine Filter.Eventually.of_forall fun i => ?_
    obtain ⟨W, hW, hx⟩ := hS2 ((a i ≫ pullback.fst _ _)
      (IsLocalRing.closedPoint (K i) : PrimeSpectrum (K i))) trivial
    exact ⟨W, hW, exists_pt_of_isLocalRing _ W hx⟩
  obtain ⟨W₁, -, hQ⟩ := exists_of_finite U hSf hQ
  obtain ⟨h₁, hh⟩ := exists_family U hQ
  have ae : IsAEHom U h₁ := by
    filter_upwards [hh] with i ⟨p, hp, _⟩
    exact ⟨p, hp⟩
  refine ⟨W₁, h₁, homOf U h₁ ae, rep_homOf U h₁ ae, hh, ?_⟩
  refine RingHom.ext fun r => ?_
  rw [RingHom.comp_apply, homOf_apply, RingHom.comp_apply, RingHom.comp_apply, hρ, algebraMap_mk,
    mk_eq_mk_iff]
  filter_upwards [hh] with i ⟨p, hp, e⟩
  have := base_eq f₀ (ψ i) W₁ p ((algebraMap (V i) (K i)).comp (β i)) (a i) e (hsq i)
  rw [← hp]
  exact RingHom.congr_fun this r
end GlobalTheory.CompanionTheory.Ultra
