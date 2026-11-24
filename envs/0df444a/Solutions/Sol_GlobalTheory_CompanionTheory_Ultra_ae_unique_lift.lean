-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ultra.ae_unique_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:42:52.105137+00:00
-- url     : https://prove2.me/submissions/a81dd26f-8c55-4260-882b-83a0a636fb51

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_CubeTheorem_SchemeModels
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteAffineCover
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsProperSpreadsOut
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_spec_comp
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_ae_exists_lift
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_not_ae_two_lifts

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
theorem _root_.solution [CompactSpace X] [QuasiSeparatedSpace X] [Algebra.FiniteType ℤ R₀]
    (hfp : ∀ W : X.affineOpens, Algebra.FinitePresentation ℤ Γ(X, W.1))
    {φ : R₀ →+* R} {f : Y ⟶ Spec (CommRingCat.of R)} {π : Y ⟶ X}
    (hpb : IsPullback π f f₀ (Spec.map (CommRingCat.ofHom φ))) (hval : ValuativeCriterion f)
    {ι : Type} (U : Ultrafilter ι) {T : ι → Type} [∀ i, CommRing (T i)] (ψ : ∀ i, R₀ →+* T i)
    (S : ∀ i, ValuativeCommSq (pullback.snd f₀ (Spec.map (CommRingCat.ofHom (ψ i)))))
    (β : ∀ i, T i →+* (S i).R) (hβ : ∀ i, (S i).i₂ = Spec.map (CommRingCat.ofHom (β i)))
    (ρ : R →+* Ult U (fun i => (S i).R))
    (hρ : ∀ r, ρ (φ r) = mk U (fun i => β i (ψ i r))) :
    ∀ᶠ i in (U : Filter ι), Nonempty (Unique (S i).commSq.LiftStruct) := by
  have hsq : ∀ i, (S i).i₁ ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom
      ((algebraMap (S i).R (S i).K).comp (β i))) := fun i => by
    rw [(S i).commSq.w, hβ, spec_comp]
  have E := ae_exists_lift f₀ U (V := fun i => (S i).R) (K := fun i => (S i).K) ψ
    (fun i => (S i).i₁) β hfp hpb hval hsq ρ hρ
  have Uq : ∀ᶠ i in (U : Filter ι), Subsingleton (S i).commSq.LiftStruct := by
    by_contra hc
    have hc' := Ultrafilter.eventually_not.2 hc
    refine not_ae_two_lifts f₀ U (V := fun i => (S i).R) (K := fun i => (S i).K) ψ
      (fun i => (S i).i₁) β hfp hpb hval hsq ρ hρ ?_
    filter_upwards [hc'] with i hi
    obtain ⟨l₁, l₂, hne⟩ := (not_subsingleton_iff_nontrivial.1 hi).exists_pair_ne
    exact ⟨l₁.l, l₂.l, fun h => hne (CommSq.LiftStruct.ext h), l₁.fac_left, l₂.fac_left,
      l₁.fac_right.trans (hβ i), l₂.fac_right.trans (hβ i)⟩
  filter_upwards [E, Uq] with i ⟨l, h1, h2⟩ hs
  have hn : Nonempty (S i).commSq.LiftStruct := ⟨⟨l, h1, h2.trans (hβ i).symm⟩⟩
  exact unique_iff_subsingleton_and_nonempty _ |>.2 ⟨hs, hn⟩
end GlobalTheory.CompanionTheory.Ultra
