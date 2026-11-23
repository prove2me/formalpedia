-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgTransfer.cos_exists
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:34:30.834316+00:00
-- url     : https://prove2.me/submissions/e71059b1-6f4e-4ec1-8f36-890c9c4b12e2

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CorrESymmCoe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgTransfer
variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {G' : Type} [Group G'] [TopologicalSpace G']
variable {Γ K Q : Subgroup G} {Γ' K' : Subgroup G'} {π : Q →* G'} {ι : G' →* Q} {c₀ : G → ℂ}
variable {P : Subgroup G} {P' : Subgroup G'} {c : G → ℂ} {c' : G' → ℂ}
namespace GlobalTheory.CompanionTheory.RgTransfer
theorem _root_.solution (hL : IsLevi Γ K Q Γ' K' π ι c₀) (hP : IsPull Q P P' π c₀ c c') :
    ∃ φ : Cos P (Γ ⊓ Q) ≃ Cos P' Γ', ∀ x, ∃ hq : rep x ∈ Q, ∃ γ ∈ Γ', γ ∈ P' ∧
      π ⟨rep x, hq⟩ = γ * rep (φ x) := by
  let f : ↥(Γ ⊓ Q) → ↥Γ' := fun d => ⟨π ⟨d, d.2.2⟩, hL.πΓ _ d.2.1⟩
  have hf : ∀ a b : ↥(Γ ⊓ Q), b * a⁻¹ ∈ P.subgroupOf (Γ ⊓ Q) ↔ f b * (f a)⁻¹ ∈ P'.subgroupOf Γ' := by
    intro a b
    have hπ : ∀ h, π ⟨((b * a⁻¹ : ↥(Γ ⊓ Q)) : G), h⟩ = ((f b * (f a)⁻¹ : ↥Γ') : G') := by
      intro h
      simp only [f, Subgroup.coe_mul, InvMemClass.coe_inv]
      rw [← map_inv, ← map_mul]
      rfl
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hP.mem]
    constructor
    · rintro ⟨h, h2⟩
      rwa [hπ h] at h2
    · intro h
      have hq : ((b * a⁻¹ : ↥(Γ ⊓ Q)) : G) ∈ Q := (b * a⁻¹).2.2
      exact ⟨hq, by rwa [hπ hq]⟩
  let φ₀ : Cos P (Γ ⊓ Q) → Cos P' Γ' := Quotient.map' f (fun a b h =>
    QuotientGroup.rightRel_apply.2 ((hf a b).1 (QuotientGroup.rightRel_apply.1 h)))
  have hbij : Function.Bijective φ₀ := by
    constructor
    · intro x y
      induction x using Quotient.inductionOn with | _ a => ?_
      induction y using Quotient.inductionOn with | _ b => ?_
      intro h
      have h2 := Quotient.exact h
      exact Quotient.sound (QuotientGroup.rightRel_apply.2
        ((hf a b).2 (QuotientGroup.rightRel_apply.1 h2)))
    · intro y
      induction y using Quotient.inductionOn with | _ m => ?_
      refine ⟨Quotient.mk _ ⟨ι m, hL.ιΓ m m.2, (ι m).2⟩, ?_⟩
      show Quotient.mk _ (f _) = _
      congr 1
      apply Subtype.ext
      exact hL.sect m
  refine ⟨Equiv.ofBijective φ₀ hbij, fun x => ?_⟩
  set d := Quotient.out x with hd
  have hx : Quotient.mk _ d = x := Quotient.out_eq x
  set e := Quotient.out (Equiv.ofBijective φ₀ hbij x) with he
  have he' : Quotient.mk _ e = Equiv.ofBijective φ₀ hbij x := Quotient.out_eq _
  have h1 : Equiv.ofBijective φ₀ hbij x = Quotient.mk _ (f d) :=
    (congrArg (Equiv.ofBijective φ₀ hbij) hx).symm
  have hrel := Quotient.exact (he'.trans h1)
  have hmem := Subgroup.mem_subgroupOf.1 (QuotientGroup.rightRel_apply.1 hrel)
  refine ⟨d.2.2, ((f d * e⁻¹ : ↥Γ') : G'), (f d * e⁻¹).2, hmem, ?_⟩
  show π ⟨d, d.2.2⟩ = ((f d * e⁻¹ : ↥Γ') : G') * (e : G')
  simp [f]
end GlobalTheory.CompanionTheory.RgTransfer
