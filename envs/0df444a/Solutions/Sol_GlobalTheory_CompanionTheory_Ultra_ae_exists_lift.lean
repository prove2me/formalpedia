-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ultra.ae_exists_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:50:32.892803+00:00
-- url     : https://prove2.me/submissions/02c9885d-37d4-4e65-81f2-54019a8b4a42

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_CubeTheorem_SchemeModels
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteAffineCover
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsProperSpreadsOut
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_spec_comp
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_spec_inj
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_pt_comp
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_val_lift
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_isLocalRing_ult
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_rep_alg
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_exists_limit_point
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_ae_eq_of_fg
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_ae_pt_eq_of_pt_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_exists_affine_le
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_exists_pt_of_isLocalRing
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_exists_rep
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_map_pt


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
theorem _root_.solution [CompactSpace X] [Algebra.FiniteType ℤ R₀]
    (hfp : ∀ W : X.affineOpens, Algebra.FinitePresentation ℤ Γ(X, W.1))
    {φ : R₀ →+* R} {f : Y ⟶ Spec (CommRingCat.of R)} {π : Y ⟶ X}
    (hpb : IsPullback π f f₀ (Spec.map (CommRingCat.ofHom φ))) (hval : ValuativeCriterion f)
    (hsq : ∀ i, a i ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom ((algebraMap (V i) (K i)).comp (β i))))
    (ρ : R →+* Ult U V) (hρ : ∀ r, ρ (φ r) = mk U (fun i => β i (ψ i r))) :
    ∀ᶠ i in (U : Filter ι), ∃ l : Spec (CommRingCat.of (V i)) ⟶
        pullback f₀ (Spec.map (CommRingCat.ofHom (ψ i))),
      Spec.map (CommRingCat.ofHom (algebraMap (V i) (K i))) ≫ l = a i ∧
      l ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (β i)) := by
  obtain ⟨W₁, h₁, P, rP, ha, hP⟩ := exists_limit_point f₀ U ψ a β φ hsq ρ hρ
  have H : pt W₁ P ≫ f₀ = Spec.map (CommRingCat.ofHom
      ((algebraMap (Ult U V) (Ult U K)).comp (ρ.comp φ))) := by rw [pt_comp, hP]
  obtain ⟨⟨ℓ, e1, e2⟩, -⟩ := val_lift hpb hval ρ (pt W₁ P) H
  haveI := isLocalRing_ult U (V := V)
  obtain ⟨W₂, hx, -⟩ := exists_affine_le (show ℓ (IsLocalRing.closedPoint (Ult U V) :
    PrimeSpectrum (Ult U V)) ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨γ, rfl⟩ := exists_pt_of_isLocalRing ℓ W₂ hx
  haveI := hfp W₂
  obtain ⟨h₂, r₂⟩ := exists_rep U γ
  have hγ : γ.comp (baseHom f₀ W₂) = ρ.comp φ := spec_inj (by rw [← pt_comp, e1])
  have c1 : ∀ᶠ i in (U : Filter ι), (fun b => h₂ i (baseHom f₀ W₂ b)) = fun r => β i (ψ i r) := by
    refine ae_eq_of_fg U (h := fun i b => h₂ i (baseHom f₀ W₂ b)) (h' := fun i r => β i (ψ i r))
      ?_ (Filter.Eventually.of_forall fun i => ⟨(β i).comp (ψ i), rfl⟩) ?_
    · filter_upwards [r₂.1] with i ⟨p, hp⟩
      exact ⟨p.comp (baseHom f₀ W₂), by funext b; simp [← hp]⟩
    · intro r
      rw [← r₂.2, ← hρ]
      exact RingHom.congr_fun hγ r
  have c2 := ae_pt_eq_of_pt_eq U hfp (rep_alg U (K := K) r₂) rP (by rw [← map_pt, e2])
  filter_upwards [r₂.1, c1, c2, ha] with i ⟨p, hp⟩ d1 d2 ⟨q, hq, eq⟩
  have hb : p.comp (baseHom f₀ W₂) = (β i).comp (ψ i) := by
    refine RingHom.ext fun r => ?_
    have := congrFun d1 r
    rw [← hp] at this
    exact this
  refine ⟨pullback.lift (pt W₂ p) (Spec.map (CommRingCat.ofHom (β i)))
    (by rw [pt_comp, hb, spec_comp]), ?_, pullback.lift_snd _ _ _⟩
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, map_pt, eq]
    exact d2 ((algebraMap (V i) (K i)).comp p) q (by funext b; simp [← hp]) hq
  · rw [Category.assoc, pullback.lift_snd, hsq, spec_comp]
end GlobalTheory.CompanionTheory.Ultra
