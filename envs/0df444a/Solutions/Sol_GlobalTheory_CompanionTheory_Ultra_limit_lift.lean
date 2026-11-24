-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ultra.limit_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:06:52.821036+00:00
-- url     : https://prove2.me/submissions/a8dd95e7-75cc-4415-8514-7f630dadfb49

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_CubeTheorem_SchemeModels
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteAffineCover
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsProperSpreadsOut
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_pt_comp
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_base_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_rep_alg
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_map_pt
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_pt_eq_of_ae_pt_eq


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
theorem _root_.solution [QuasiSeparatedSpace X] {φ : R₀ →+* R}
    (ρ : R →+* Ult U V) (hρ : ∀ r, ρ (φ r) = mk U (fun i => β i (ψ i r)))
    {W W₁ : X.affineOpens} {h : ∀ i, Γ(X, W.1) → V i} {G : Γ(X, W.1) →+* Ult U V} (r : Rep U h G)
    {h₁ : ∀ i, Γ(X, W₁.1) → K i} {P : Γ(X, W₁.1) →+* Ult U K} (rP : Rep U h₁ P)
    (H : ∀ᶠ i in (U : Filter ι), ∃ (p : Γ(X, W.1) →+* V i) (q : Γ(X, W₁.1) →+* K i)
      (l : Spec (CommRingCat.of (V i)) ⟶ pullback f₀ (Spec.map (CommRingCat.ofHom (ψ i)))),
      ⇑p = h i ∧ ⇑q = h₁ i ∧ l ≫ pullback.fst _ _ = pt W p ∧
      l ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (β i)) ∧
      Spec.map (CommRingCat.ofHom (algebraMap (V i) (K i))) ≫ l = a i ∧
      a i ≫ pullback.fst _ _ = pt W₁ q) :
    pt W G ≫ f₀ = Spec.map (CommRingCat.ofHom (ρ.comp φ)) ∧
    Spec.map (CommRingCat.ofHom (algebraMap (Ult U V) (Ult U K))) ≫ pt W G = pt W₁ P := by
  refine ⟨?_, ?_⟩
  · rw [pt_comp]
    congr 2
    refine RingHom.ext fun x => ?_
    rw [RingHom.comp_apply, r.2, RingHom.comp_apply, hρ, mk_eq_mk_iff]
    filter_upwards [H] with i ⟨p, q, l, hp, hq, h1, h2, h3, h4⟩
    have := base_eq f₀ (ψ i) W p (β i) l h1 h2
    rw [← hp]
    exact RingHom.congr_fun this x
  · rw [map_pt]
    refine pt_eq_of_ae_pt_eq U (rep_alg U (K := K) r) rP ?_
    filter_upwards [H] with i ⟨p, q, l, hp, hq, h1, h2, h3, h4⟩
    refine ⟨(algebraMap (V i) (K i)).comp p, q, by funext b; simp [← hp], hq, ?_⟩
    rw [← map_pt, ← h1, ← Category.assoc, h3, h4]
end GlobalTheory.CompanionTheory.Ultra
