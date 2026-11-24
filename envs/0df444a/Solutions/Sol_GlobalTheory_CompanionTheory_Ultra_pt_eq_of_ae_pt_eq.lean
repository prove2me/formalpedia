-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ultra.pt_eq_of_ae_pt_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:50:29.749947+00:00
-- url     : https://prove2.me/submissions/678c3f6a-e173-4c09-ad64-2f325126d15d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteAffineCover
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_homOf_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_exists_family
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_pt_injective
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_pt_res
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_pt_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_exists_pt_of_isLocalRing
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_exists_of_finite
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_exists_finite_affine_cover

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
open Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ultra
variable {ι : Type} (U : Ultrafilter ι)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
variable {X : Scheme.{0}}
variable {A : ι → Type} [∀ i, CommRing (A i)]
namespace GlobalTheory.CompanionTheory.Ultra
theorem _root_.solution [QuasiSeparatedSpace X] [∀ i, IsLocalRing (A i)]
    {W₁ W₂ : X.affineOpens} {h₁ : ∀ i, Γ(X, W₁.1) → A i} {h₂ : ∀ i, Γ(X, W₂.1) → A i}
    {g₁ : Γ(X, W₁.1) →+* Ult U A} {g₂ : Γ(X, W₂.1) →+* Ult U A}
    (r₁ : Rep U h₁ g₁) (r₂ : Rep U h₂ g₂)
    (H : ∀ᶠ i in (U : Filter ι), ∃ (p : Γ(X, W₁.1) →+* A i) (q : Γ(X, W₂.1) →+* A i),
      ⇑p = h₁ i ∧ ⇑q = h₂ i ∧ pt W₁ p = pt W₂ q) :
    pt W₁ g₁ = pt W₂ g₂ := by
  have hc : IsCompact (((W₁.1 ⊓ W₂.1 : X.Opens)) : Set X) :=
    QuasiSeparatedSpace.inter_isCompact _ _ W₁.1.2 W₁.2.isCompact W₂.1.2 W₂.2.isCompact
  obtain ⟨S, hSf, hS1, hS2⟩ := exists_finite_affine_cover (W₁.1 ⊓ W₂.1) hc
  have hQ : ∀ᶠ i in (U : Filter ι), ∃ W ∈ S, ∃ t : Γ(X, W.1) →+* A i,
      ∃ (p : Γ(X, W₁.1) →+* A i) (q : Γ(X, W₂.1) →+* A i),
        ⇑p = h₁ i ∧ ⇑q = h₂ i ∧ pt W t = pt W₁ p ∧ pt W t = pt W₂ q := by
    filter_upwards [H] with i ⟨p, q, hp, hq, e⟩
    have hx₁ : (pt W₁ p) (IsLocalRing.closedPoint (A i) : PrimeSpectrum (A i)) ∈ W₁.1 :=
      pt_mem _ _ _
    have hx₂ : (pt W₁ p) (IsLocalRing.closedPoint (A i) : PrimeSpectrum (A i)) ∈ W₂.1 := by
      rw [e]; exact pt_mem _ _ _
    obtain ⟨W, hW, hxW⟩ := hS2 _ (show _ ∈ W₁.1 ⊓ W₂.1 from ⟨hx₁, hx₂⟩)
    obtain ⟨t, ht⟩ := exists_pt_of_isLocalRing (pt W₁ p) W hxW
    exact ⟨W, hW, t, p, q, hp, hq, ht.symm, ht.symm.trans e⟩
  obtain ⟨W, hW, hQ⟩ := exists_of_finite U hSf hQ
  obtain ⟨h, hh⟩ := exists_family U hQ
  have ae : IsAEHom U h := by
    filter_upwards [hh] with i ⟨t, ht, _⟩
    exact ⟨t, ht⟩
  have hle₁ : W.1 ≤ W₁.1 := (hS1 W hW).trans inf_le_left
  have hle₂ : W.1 ≤ W₂.1 := (hS1 W hW).trans inf_le_right
  have e₁ : g₁ = (homOf U h ae).comp (res hle₁) := by
    refine RingHom.ext fun b => ?_
    rw [r₁.2, RingHom.comp_apply, homOf_apply, mk_eq_mk_iff]
    filter_upwards [hh] with i ⟨t, ht, p, q, hp, hq, e1, e2⟩
    have : p = t.comp (res hle₁) := pt_injective W₁ (by rw [pt_res]; exact e1.symm)
    rw [← hp, ← ht, this]
    rfl
  have e₂ : g₂ = (homOf U h ae).comp (res hle₂) := by
    refine RingHom.ext fun b => ?_
    rw [r₂.2, RingHom.comp_apply, homOf_apply, mk_eq_mk_iff]
    filter_upwards [hh] with i ⟨t, ht, p, q, hp, hq, e1, e2⟩
    have : q = t.comp (res hle₂) := pt_injective W₂ (by rw [pt_res]; exact e2.symm)
    rw [← hq, ← ht, this]
    rfl
  rw [e₁, e₂, pt_res, pt_res]
end GlobalTheory.CompanionTheory.Ultra
