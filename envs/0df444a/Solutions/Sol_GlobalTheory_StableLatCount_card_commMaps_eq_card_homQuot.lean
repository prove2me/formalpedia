-- Prove2me | solution 1 for GlobalTheory.StableLatCount.card_commMaps_eq_card_homQuot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:57:16.696139+00:00
-- url     : https://prove2.me/submissions/da7c774f-ac5b-40f2-9a76-56571677686a

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdEApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardCommMapsEqCardHomQuot
import Theorems.Thm_GlobalTheory_StableLatCount_adE_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.StableLatCount Polynomial
noncomputable section
open GlobalTheory GlobalTheory.StableLatCount
namespace GlobalTheory.StableLatCount
theorem _root_.solution : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (E : Type) [Field E] [Algebra O E] [IsFractionRing O E] (A₁ A₂ : Type) [CommRing A₁] [CommRing A₂] [Algebra E A₁] [Algebra E A₂] [Algebra O A₁] [Algebra O A₂] [IsScalarTower O E A₁] [IsScalarTower O E A₂] [Module.Finite E A₁] [Module.Finite E A₂] (g₁ : A₁) (g₂ : A₂) (M₁ : Submodule O A₁) (M₂ : Submodule O A₂), IsLat O E M₂ → (∀ y ∈ M₁, g₁ * y ∈ M₁) → (∀ y ∈ M₂, g₂ * y ∈ M₂) → Nat.card {φ : M₂ →ₗ[O] A₁ ⧸ M₁ // ∀ x y : M₂, (y : A₂) = g₂ * x → ∀ a : A₁, φ x = Submodule.Quotient.mk a → φ y = Submodule.Quotient.mk (g₁ * a)} = Nat.card {z : (A₂ →ₗ[E] A₁) ⧸ homLat E M₁ M₂ // ∀ ψ : A₂ →ₗ[E] A₁, Submodule.Quotient.mk ψ = z → adE E g₁ g₂ ψ ∈ homLat E M₁ M₂} := by
  intro O _ _ _ E _ _ _ A₁ A₂ _ _ _ _ _ _ _ _ _ _ g₁ g₂ M₁ M₂ hM₂ hg₁ hg₂
  classical
  let F : (A₂ →ₗ[E] A₁) →ₗ[O] (M₂ →ₗ[O] A₁ ⧸ M₁) :=
    { toFun := fun ψ => M₁.mkQ ∘ₗ (ψ.restrictScalars O) ∘ₗ M₂.subtype
      map_add' := fun ψ χ => by ext x; simp
      map_smul' := fun c ψ => by ext x; simp }
  have hF : ∀ ψ (x : M₂), F ψ x = Submodule.Quotient.mk (ψ (x : A₂)) := fun _ _ => rfl
  have hsurj : Function.Surjective F := by
    intro φ
    haveI : Module.Finite O M₂ := Module.Finite.iff_fg.2 hM₂.1
    haveI : Module.IsTorsionFree O A₂ := Module.IsTorsionFree.of_smul_eq_zero fun r m h => by
      by_cases hr : r = 0
      · exact Or.inl hr
      right
      rw [← algebraMap_smul E r m] at h
      have hr' : algebraMap O E r ≠ 0 := by
        intro h0
        exact hr ((IsFractionRing.injective O E) (by rw [h0, map_zero]))
      exact (smul_eq_zero.1 h).resolve_left hr'
    haveI : Module.Free O M₂ := Module.free_of_finite_type_torsion_free'
    let b := Module.Free.chooseBasis O M₂
    let bs : Module.Free.ChooseBasisIndex O M₂ → A₂ := fun i => (b i : A₂)
    have hli : LinearIndependent O bs := b.linearIndependent.map' M₂.subtype (Submodule.ker_subtype M₂)
    have hliE : LinearIndependent E bs := (LinearIndependent.iff_fractionRing O E).1 hli
    have hspan : ⊤ ≤ Submodule.span E (Set.range bs) := by
      rw [← hM₂.2, Submodule.span_le]
      intro x hx
      have h1 : (⟨x, hx⟩ : M₂) ∈ Submodule.span O (Set.range b) := by
        rw [b.span_eq]; exact Submodule.mem_top
      have h2 := Submodule.mem_map_of_mem (f := M₂.subtype) h1
      rw [Submodule.map_span, ← Set.range_comp] at h2
      exact Submodule.span_le_restrictScalars O E _ h2
    let bE := Module.Basis.mk hliE hspan
    let lift : Module.Free.ChooseBasisIndex O M₂ → A₁ := fun i =>
      Classical.choose (Submodule.Quotient.mk_surjective M₁ (φ (b i)))
    have hlift : ∀ i, Submodule.Quotient.mk (p := M₁) (lift i) = φ (b i) := fun i =>
      Classical.choose_spec (Submodule.Quotient.mk_surjective M₁ (φ (b i)))
    refine ⟨bE.constr E lift, b.ext fun i => ?_⟩
    rw [hF, ← hlift i]
    congr 1
    have : ((b i : M₂) : A₂) = bE i := by simp [bE, bs]
    rw [this, Module.Basis.constr_basis]
  have hker : LinearMap.ker F = homLat E M₁ M₂ := by
    ext ψ
    rw [LinearMap.mem_ker]
    constructor
    · intro h x hx
      have := congrArg (fun f => f ⟨x, hx⟩) h
      simp only [hF, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero] at this
      exact this
    · intro h
      ext x
      rw [hF, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
      exact h x x.2
  let e : ((A₂ →ₗ[E] A₁) ⧸ homLat E M₁ M₂) ≃ (M₂ →ₗ[O] A₁ ⧸ M₁) :=
    ((Submodule.quotEquivOfEq _ _ hker.symm).trans (F.quotKerEquivOfSurjective hsurj)).toEquiv
  have he : ∀ ψ, e (Submodule.Quotient.mk ψ) = F ψ := fun ψ => rfl
  refine (Nat.card_congr (e.subtypeEquiv fun z => ?_)).symm
  induction z using Submodule.Quotient.induction_on with
  | H ψ₀ => ?_
  rw [he]
  constructor
  · intro h x y hxy a ha
    have hA : ∀ x ∈ M₂, g₁ * ψ₀ x - ψ₀ (g₂ * x) ∈ M₁ := fun x hx => by
      have := h ψ₀ rfl x hx
      rwa [adE_apply] at this
    rw [hF] at ha ⊢
    rw [Submodule.Quotient.eq] at ha ⊢
    have := M₁.add_mem (M₁.neg_mem (hA x x.2)) (hg₁ _ ha)
    convert this using 1
    rw [hxy]
    ring
  · intro h ψ hψ x hx
    rw [Submodule.Quotient.eq] at hψ
    have hd : ∀ x ∈ M₂, ψ x - ψ₀ x ∈ M₁ := fun x hx => by
      have := hψ x hx
      rwa [LinearMap.sub_apply] at this
    have hc := h ⟨x, hx⟩ ⟨g₂ * x, hg₂ x hx⟩ rfl (ψ₀ x) (hF ψ₀ ⟨x, hx⟩)
    rw [hF, Submodule.Quotient.eq] at hc
    rw [adE_apply]
    have := M₁.sub_mem (M₁.sub_mem (hg₁ _ (hd x hx)) (hd _ (hg₂ x hx))) hc
    convert this using 1
    simp only
    ring
end GlobalTheory.StableLatCount
