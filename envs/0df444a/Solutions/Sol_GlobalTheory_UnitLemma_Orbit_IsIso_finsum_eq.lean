-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Orbit.IsIso.finsum_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:58:43.300508+00:00
-- url     : https://prove2.me/submissions/084a49a4-edb8-4ae7-93b9-dcb5633f3463

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfNotPrimary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit
open GlobalTheory.UnitLemma Polynomial IsLocalRing ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion
variable {K : UQ}
open GlobalTheory.UnitLemma.Orbit.IsIso
variable {B C : InvAlg K} {φ : B.A ≃ₐ[K.E] C.A}
namespace GlobalTheory.UnitLemma.Orbit.IsIso
theorem _root_.solution (h : IsIso φ) (F : C.A → ℚ) (hF : ∀ (x : C.A) (u : C.Aˣ), F (x * (u * C.σ (u : C.A))) = F x) :
    ∑ᶠ k : C.Cl, F k.rep = ∑ᶠ k : B.Cl, F (φ k.rep) := by
  set ψ := Units.mapEquiv φ.toMulEquiv with hψ
  have hv : ∀ t : B.Aˣ, ((ψ t : C.Aˣ) : C.A) = φ t := fun t => rfl
  let e : {x : B.Aˣ // B.σ (x : B.A) = x} ≃ {x : C.Aˣ // C.σ (x : C.A) = x} :=
    ψ.toEquiv.subtypeEquiv fun t => by
      change _ ↔ C.σ (φ t) = φ t
      rw [← h.1, φ.injective.eq_iff]
  have he : ∀ x, (((e x).1 : C.Aˣ) : C.A) = φ x.1 := fun x => rfl
  let q : B.Cl ≃ C.Cl := Quot.congr e (by
    intro x y
    rw [ψ.surjective.exists]
    simp only [he, hv, ← h.1, ← map_mul, φ.injective.eq_iff])
  let W : C.Cl → ℚ := Quot.lift (fun x => F x.1) (by
    rintro x y ⟨u, hu⟩
    simp only [hu, hF])
  have hW : ∀ k : C.Cl, F k.rep = W k := fun k => by
    conv_rhs => rw [← Quot.out_eq k]
    rfl
  rw [← finsum_comp_equiv q]
  refine finsum_congr fun k => ?_
  rw [hW]
  conv_lhs => rw [← Quot.out_eq k]
  rfl
end GlobalTheory.UnitLemma.Orbit.IsIso
