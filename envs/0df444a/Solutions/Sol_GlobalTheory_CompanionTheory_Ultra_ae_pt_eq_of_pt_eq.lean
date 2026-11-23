-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ultra.ae_pt_eq_of_pt_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:18:54.888803+00:00
-- url     : https://prove2.me/submissions/6210f99b-362f-43f0-978b-c2f9f5261391

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteAffineCover
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_ae_eq_of_fg
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_exists_rep
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_pt_injective
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_pt_res
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_pt_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_exists_pt_of_isLocalRing
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_exists_affine_le

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
theorem _root_.solution [IsLocalRing (Ult U A)]
    (hfp : ∀ W : X.affineOpens, Algebra.FinitePresentation ℤ Γ(X, W.1))
    {W₁ W₂ : X.affineOpens} {h₁ : ∀ i, Γ(X, W₁.1) → A i} {h₂ : ∀ i, Γ(X, W₂.1) → A i}
    {g₁ : Γ(X, W₁.1) →+* Ult U A} {g₂ : Γ(X, W₂.1) →+* Ult U A}
    (r₁ : Rep U h₁ g₁) (r₂ : Rep U h₂ g₂) (H : pt W₁ g₁ = pt W₂ g₂) :
    ∀ᶠ i in (U : Filter ι), ∀ (p : Γ(X, W₁.1) →+* A i) (q : Γ(X, W₂.1) →+* A i),
      ⇑p = h₁ i → ⇑q = h₂ i → pt W₁ p = pt W₂ q := by
  set x : X := (pt W₁ g₁) (IsLocalRing.closedPoint (Ult U A) : PrimeSpectrum (Ult U A)) with hx
  have hx₁ : x ∈ W₁.1 := pt_mem _ _ _
  have hx₂ : x ∈ W₂.1 := by rw [hx, H]; exact pt_mem _ _ _
  obtain ⟨W, hxW, hle⟩ := exists_affine_le (show x ∈ W₁.1 ⊓ W₂.1 from ⟨hx₁, hx₂⟩)
  have hle₁ : W.1 ≤ W₁.1 := hle.trans inf_le_left
  have hle₂ : W.1 ≤ W₂.1 := hle.trans inf_le_right
  obtain ⟨T, hT⟩ := exists_pt_of_isLocalRing (pt W₁ g₁) W hxW
  have e₁ : g₁ = T.comp (res hle₁) := pt_injective W₁ (by rw [pt_res]; exact hT)
  have e₂ : g₂ = T.comp (res hle₂) := pt_injective W₂ (by rw [pt_res, ← H]; exact hT)
  haveI := hfp W
  haveI := hfp W₁
  haveI := hfp W₂
  obtain ⟨h, hr⟩ := exists_rep U T
  have aeh : ∀ {W' : X.affineOpens} (hl : W.1 ≤ W'.1),
      IsAEHom U (fun i b => h i (res hl b)) := by
    intro W' hl
    filter_upwards [hr.1] with i ⟨t, ht⟩
    exact ⟨t.comp (res hl), by funext b; simp [← ht]⟩
  have a₁ := ae_eq_of_fg U r₁.1 (aeh hle₁) (fun b => by
    rw [← r₁.2, e₁]; exact hr.2 _)
  have a₂ := ae_eq_of_fg U r₂.1 (aeh hle₂) (fun b => by
    rw [← r₂.2, e₂]; exact hr.2 _)
  filter_upwards [a₁, a₂, hr.1] with i b₁ b₂ ⟨t, ht⟩ p q hp hq
  have p_eq : p = t.comp (res hle₁) := by
    ext b
    have := congrFun b₁ b
    rw [← hp] at this
    simpa [← ht] using this
  have q_eq : q = t.comp (res hle₂) := by
    ext b
    have := congrFun b₂ b
    rw [← hq] at this
    simpa [← ht] using this
  rw [p_eq, q_eq, pt_res, pt_res]
end GlobalTheory.CompanionTheory.Ultra
