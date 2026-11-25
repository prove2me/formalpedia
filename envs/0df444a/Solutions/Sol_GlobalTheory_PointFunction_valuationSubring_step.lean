-- Prove2me | solution 1 for GlobalTheory.PointFunction.valuationSubring_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:05:53.782382+00:00
-- url     : https://prove2.me/submissions/b809ba49-5780-498a-8166-617f32905048

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NonemptyAlgHomAlgebraicClosure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PointFunction
open IsLocalRing
namespace GlobalTheory.PointFunction
theorem _root_.solution (K : Type) [Field K] (A : Type) [CommRing A] [Algebra K A]
    (W : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra K k], (A →ₐ[K] k) → k)
    (h2 : ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Algebra K V],
      IsAlgClosed (FractionRing V) → ∀ ι : A →ₐ[K] V, ∃ v : V,
        ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra K k] (φ : V →ₐ[K] k),
          W k (φ.comp ι) = φ v)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (ι : A →ₐ[K] Ω)
    (V : ValuationSubring Ω) (h : ∀ a, ι a ∈ V) :
    W Ω ι ∈ V ∧ ∃ (_ : Algebra K (AlgebraicClosure (ResidueField V)))
      (φ : A →ₐ[K] AlgebraicClosure (ResidueField V)),
      (∀ a, φ a = 0 ↔ (⟨ι a, h a⟩ : V) ∈ maximalIdeal V) ∧
        ∀ r, ι r = W Ω ι → W _ φ = φ r := by
  let j : A →+* V := ι.toRingHom.codRestrict V.toSubring h
  letI : Algebra K V := (j.comp (algebraMap K A)).toAlgebra
  let jA : A →ₐ[K] V := { j with commutes' := fun _ => rfl }
  let s : V →ₐ[K] Ω := { V.subtype with commutes' := fun x => ι.commutes x }
  have hs : s.comp jA = ι := by ext a; rfl
  have hcl : IsAlgClosed (FractionRing V) :=
    IsAlgClosed.of_ringEquiv Ω _ (FractionRing.algEquiv V Ω).symm.toRingEquiv
  obtain ⟨v, hv⟩ := h2 V hcl jA
  have hw : W Ω ι = v := by rw [← hs, hv]; rfl
  refine ⟨hw ▸ v.2, ?_⟩
  let ρ : V →+* AlgebraicClosure (ResidueField V) :=
    (algebraMap (ResidueField V) _).comp (residue V)
  letI alg : Algebra K (AlgebraicClosure (ResidueField V)) := (ρ.comp (algebraMap K V)).toAlgebra
  let ρA : V →ₐ[K] AlgebraicClosure (ResidueField V) := { ρ with commutes' := fun _ => rfl }
  refine ⟨alg, ρA.comp jA, fun a => ?_, fun r hr => ?_⟩
  · change algebraMap (ResidueField V) (AlgebraicClosure (ResidueField V)) (residue V ⟨ι a, h a⟩) = 0 ↔ _
    rw [map_eq_zero, residue_eq_zero_iff]
  · rw [hv]
    have : v = jA r := Subtype.ext (by rw [← hw, ← hr]; rfl)
    rw [this]; rfl
end GlobalTheory.PointFunction
