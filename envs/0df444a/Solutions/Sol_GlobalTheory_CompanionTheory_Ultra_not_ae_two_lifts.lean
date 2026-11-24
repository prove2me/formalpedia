-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ultra.not_ae_two_lifts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:25:01.728723+00:00
-- url     : https://prove2.me/submissions/28091f5c-eb0e-4d38-a359-9eaf899b0c32

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_CubeTheorem_SchemeModels
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteAffineCover
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsProperSpreadsOut
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_pt_comp
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_val_lift
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_isLocalRing_ult
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_exists_limit_point
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_limit_lift
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_ae_pt_eq_of_pt_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_exists_family
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_exists_finite_affine_cover
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_exists_of_finite
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_exists_pt_of_isLocalRing
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
theorem _root_.solution [CompactSpace X] [QuasiSeparatedSpace X] [Algebra.FiniteType ℤ R₀]
    (hfp : ∀ W : X.affineOpens, Algebra.FinitePresentation ℤ Γ(X, W.1))
    {φ : R₀ →+* R} {f : Y ⟶ Spec (CommRingCat.of R)} {π : Y ⟶ X}
    (hpb : IsPullback π f f₀ (Spec.map (CommRingCat.ofHom φ))) (hval : ValuativeCriterion f)
    (hsq : ∀ i, a i ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom ((algebraMap (V i) (K i)).comp (β i))))
    (ρ : R →+* Ult U V) (hρ : ∀ r, ρ (φ r) = mk U (fun i => β i (ψ i r)))
    (H : ∀ᶠ i in (U : Filter ι), ∃ l₁ l₂ : Spec (CommRingCat.of (V i)) ⟶
        pullback f₀ (Spec.map (CommRingCat.ofHom (ψ i))), l₁ ≠ l₂ ∧
      Spec.map (CommRingCat.ofHom (algebraMap (V i) (K i))) ≫ l₁ = a i ∧
      Spec.map (CommRingCat.ofHom (algebraMap (V i) (K i))) ≫ l₂ = a i ∧
      l₁ ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (β i)) ∧
      l₂ ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (β i))) : False := by
  obtain ⟨W₁, h₁, P, rP, ha, hP⟩ := exists_limit_point f₀ U ψ a β φ hsq ρ hρ
  have HP : pt W₁ P ≫ f₀ = Spec.map (CommRingCat.ofHom
      ((algebraMap (Ult U V) (Ult U K)).comp (ρ.comp φ))) := by rw [pt_comp, hP]
  haveI := isLocalRing_ult U (V := V)
  obtain ⟨S, hSf, -, hS2⟩ := exists_finite_affine_cover (⊤ : X.Opens) (by simpa using isCompact_univ)
  have hQ : ∀ᶠ i in (U : Filter ι), ∃ w ∈ S ×ˢ S, ∃ (p : Γ(X, w.1.1) →+* V i)
      (q : Γ(X, w.2.1) →+* V i) (l₁ l₂ : Spec (CommRingCat.of (V i)) ⟶
        pullback f₀ (Spec.map (CommRingCat.ofHom (ψ i)))), l₁ ≠ l₂ ∧
      Spec.map (CommRingCat.ofHom (algebraMap (V i) (K i))) ≫ l₁ = a i ∧
      Spec.map (CommRingCat.ofHom (algebraMap (V i) (K i))) ≫ l₂ = a i ∧
      l₁ ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (β i)) ∧
      l₂ ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (β i)) ∧
      l₁ ≫ pullback.fst _ _ = pt w.1 p ∧ l₂ ≫ pullback.fst _ _ = pt w.2 q := by
    filter_upwards [H] with i ⟨l₁, l₂, hne, a1, a2, s1, s2⟩
    obtain ⟨A₁, hA₁, x₁⟩ := hS2 ((l₁ ≫ pullback.fst _ _)
      (IsLocalRing.closedPoint (V i) : PrimeSpectrum (V i))) trivial
    obtain ⟨A₂, hA₂, x₂⟩ := hS2 ((l₂ ≫ pullback.fst _ _)
      (IsLocalRing.closedPoint (V i) : PrimeSpectrum (V i))) trivial
    obtain ⟨p, hp⟩ := exists_pt_of_isLocalRing _ A₁ x₁
    obtain ⟨q, hq⟩ := exists_pt_of_isLocalRing _ A₂ x₂
    exact ⟨(A₁, A₂), ⟨hA₁, hA₂⟩, p, q, l₁, l₂, hne, a1, a2, s1, s2, hp, hq⟩
  obtain ⟨⟨W₂, W₃⟩, -, hQ⟩ := exists_of_finite U (hSf.prod hSf) hQ
  dsimp only at hQ
  obtain ⟨h₂, hh₂⟩ := exists_family U hQ
  have hQ' : ∀ᶠ i in (U : Filter ι), ∃ (q : Γ(X, W₃.1) →+* V i) (p : Γ(X, W₂.1) →+* V i)
      (l₁ l₂ : Spec (CommRingCat.of (V i)) ⟶
        pullback f₀ (Spec.map (CommRingCat.ofHom (ψ i)))), ⇑p = h₂ i ∧ l₁ ≠ l₂ ∧
      Spec.map (CommRingCat.ofHom (algebraMap (V i) (K i))) ≫ l₁ = a i ∧
      Spec.map (CommRingCat.ofHom (algebraMap (V i) (K i))) ≫ l₂ = a i ∧
      l₁ ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (β i)) ∧
      l₂ ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (β i)) ∧
      l₁ ≫ pullback.fst _ _ = pt W₂ p ∧ l₂ ≫ pullback.fst _ _ = pt W₃ q := by
    filter_upwards [hh₂] with i ⟨p, hp, q, l₁, l₂, hne, a1, a2, s1, s2, f1, f2⟩
    exact ⟨q, p, l₁, l₂, hp, hne, a1, a2, s1, s2, f1, f2⟩
  obtain ⟨h₃, hh₃⟩ := exists_family U hQ'
  have ae₂ : IsAEHom U h₂ := by
    filter_upwards [hh₂] with i ⟨p, hp, _⟩
    exact ⟨p, hp⟩
  have ae₃ : IsAEHom U h₃ := by
    filter_upwards [hh₃] with i ⟨p, hp, _⟩
    exact ⟨p, hp⟩
  have L₂ := limit_lift f₀ U ψ a β ρ hρ (rep_homOf U h₂ ae₂) rP (by
    filter_upwards [hh₃, ha] with i ⟨q, hq, p, l₁, l₂, hp, hne, a1, a2, s1, s2, f1, f2⟩ ⟨t, ht, et⟩
    exact ⟨p, t, l₁, hp, ht, f1, s1, a1, et⟩)
  have L₃ := limit_lift f₀ U ψ a β ρ hρ (rep_homOf U h₃ ae₃) rP (by
    filter_upwards [hh₃, ha] with i ⟨q, hq, p, l₁, l₂, hp, hne, a1, a2, s1, s2, f1, f2⟩ ⟨t, ht, et⟩
    exact ⟨q, t, l₂, hq, ht, f2, s2, a2, et⟩)
  have E := (val_lift hpb hval ρ (pt W₁ P) HP).2 _ _ L₂.1 L₃.1 L₂.2 L₃.2
  have c := ae_pt_eq_of_pt_eq U hfp (rep_homOf U h₂ ae₂) (rep_homOf U h₃ ae₃) E
  obtain ⟨i, d, q, hq, p, l₁, l₂, hp, hne, a1, a2, s1, s2, f1, f2⟩ := (c.and hh₃).exists
  apply hne
  apply pullback.hom_ext
  · rw [f1, f2]
    exact d p q hp hq
  · rw [s1, s2]
end GlobalTheory.CompanionTheory.Ultra
