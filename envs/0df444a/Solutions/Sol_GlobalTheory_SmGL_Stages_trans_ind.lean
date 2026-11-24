-- Prove2me | solution 1 for GlobalTheory.SmGL.Stages.trans_ind
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:04:17.173043+00:00
-- url     : https://prove2.me/submissions/b9a2c7e1-c8c3-4255-b5fd-6aa9ba9777ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyInv
import Theorems.Thm_GlobalTheory_SmGL_Stages_eventually_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Topology Filter
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.Stages
variable {F G M W X Y Z : Type} [Field F] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group M] [TopologicalSpace M] [IsTopologicalGroup M] [AddCommGroup W] [Module F W]
  [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y] [AddCommGroup Z] [Module F Z]
namespace GlobalTheory.SmGL.Stages
theorem _root_.solution {Q R : Subgroup G} (hRQ : R ≤ Q) (Θ : Representation F Q Y) (ρ : Representation F R Z)
    (ev : Y →ₗ[F] Z) (hev : ∀ (r : R) y, ev (Θ ⟨r, hRQ r.2⟩ y) = ρ r (ev y))
    (hinj : ∀ y, (∀ q, ev (Θ q y) = 0) → y = 0)
    (hsurj : ∀ φ : Q → Z, (∀ (r : R) q, φ (⟨r, hRQ r.2⟩ * q) = ρ r (φ q)) →
      (∀ᶠ u in 𝓝 (1 : Q), ∀ q, φ (q * u) = φ q) → ∃ y, ∀ q, ev (Θ q y) = φ q) :
    Nonempty ((smInd Q Θ).Equiv (smInd R ρ)) := by
  let T : smoothPart (ind Q Θ) →ₗ[F] smoothPart (ind R ρ) :=
    { toFun := fun f => mkInd ρ (fun g => ev (f.1.1 g))
        (fun r g => by rw [← hev, ← f.1.2 ⟨r, hRQ r.2⟩ g])
        ((eventually_inv f).mono fun u hu x => by rw [hu])
      map_add' := fun f g => by ext x; exact map_add ev _ _
      map_smul' := fun c f => by ext x; exact map_smul ev _ _ }
  have hext : ∀ y y', (∀ q, ev (Θ q y) = ev (Θ q y')) → y = y' := fun y y' h =>
    sub_eq_zero.1 (hinj _ fun q => by rw [map_sub, map_sub, h, sub_self])
  have h1 : Function.Injective T := by
    intro f f' h
    ext g
    refine hext _ _ fun q => ?_
    rw [← f.1.2 q g, ← f'.1.2 q g]
    exact congrFun (congrArg (fun φ => φ.1.1) h) _
  have h2 : Function.Surjective T := by
    intro h
    have key : ∀ g : G, ∃ y, ∀ q : Q, ev (Θ q y) = h.1.1 (q * g) := fun g => by
      refine hsurj (fun q => h.1.1 (q * g)) (fun r q => ?_) ?_
      · rw [← h.1.2 r, ← mul_assoc]; rfl
      · have hc : Tendsto (fun u : Q => g⁻¹ * u * g) (𝓝 1) (𝓝 1) :=
          Continuous.tendsto' (by fun_prop) _ _ (by simp)
        refine (hc.eventually (eventually_inv h)).mono fun u hu q => ?_
        rw [← hu (q * g)]
        simp [mul_assoc]
    choose y hy using key
    refine ⟨mkInd Θ y (fun p g => hext _ _ fun q => ?_)
      ((eventually_inv h).mono fun u hu x => hext _ _ fun q => ?_), ?_⟩
    · rw [← Module.End.mul_apply, ← map_mul, hy, hy, ← mul_assoc]; rfl
    · rw [hy, hy, ← mul_assoc, hu]
    · ext g
      exact (by simpa using hy g 1 : ev (y g) = h.1.1 g)
  exact ⟨.mk (LinearEquiv.ofBijective T ⟨h1, h2⟩) fun g => by ext f x; rfl⟩
end GlobalTheory.SmGL.Stages
