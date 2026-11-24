-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PerfKerCoh.ker_equiv_cohomology
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:29:13.853405+00:00
-- url     : https://prove2.me/submissions/a704b596-a27b-4fe1-a395-0cfbe33e1da2

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_KernelEquivCohomologyOfQuasiIsomorphism
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PerfKerCoh
namespace GlobalTheory.CompanionTheory.PerfKerCoh
theorem _root_.solution : ∀ (S P₀ P₁ P₂ T B₀ B₁ B₂ : Type) [CommRing S] [AddCommGroup P₀] [Module S P₀] [AddCommGroup P₁] [Module S P₁] [AddCommGroup P₂] [Module S P₂] [AddCommGroup T] [Module S T] [AddCommGroup B₀] [Module S B₀] [AddCommGroup B₁] [Module S B₁] [AddCommGroup B₂] [Module S B₂] (a₀ : P₀ →ₗ[S] P₁) (a₁ : P₁ →ₗ[S] P₂) (π : P₁ →ₗ[S] T) (dT : T →ₗ[S] P₂) (Z : Submodule S B₁) (dB : B₀ →ₗ[S] Z) (b₁ : B₁ →ₗ[S] B₂) (f : P₁ →ₗ[S] B₁) (ψ₀ : P₀ →ₗ[S] B₀), Function.Surjective π → Function.Exact a₀ π → dT ∘ₗ π = a₁ → (∀ z, z ∈ Z ↔ b₁ z = 0) → (∀ x, a₁ x = 0 → b₁ (f x) = 0) → (∀ y, f (a₀ y) = (dB (ψ₀ y) : B₁)) → QIsoAt a₀ a₁ (Z.subtype ∘ₗ dB) b₁ f → Nonempty (LinearMap.ker dT ≃ₗ[S] Z ⧸ LinearMap.range dB) := by
  intro S P₀ P₁ P₂ T B₀ B₁ B₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a₀ a₁ π dT Z dB b₁ f ψ₀ hπ hex hdT hZ hf hψ hq
  have hdTπ : ∀ x, dT (π x) = a₁ x := fun x => LinearMap.congr_fun hdT x
  let H : LinearMap.ker a₁ →ₗ[S] LinearMap.ker dT :=
    (π.comp (LinearMap.ker a₁).subtype).codRestrict (LinearMap.ker dT) fun x => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply, hdTπ]
      exact x.2
  let G : LinearMap.ker a₁ →ₗ[S] Z ⧸ LinearMap.range dB :=
    (LinearMap.range dB).mkQ.comp ((f.comp (LinearMap.ker a₁).subtype).codRestrict Z fun x =>
      (hZ _).2 (hf _ x.2))
  have hH : Function.Surjective H := by
    rintro ⟨t, ht⟩
    obtain ⟨x, rfl⟩ := hπ t
    have hx : a₁ x = 0 := by
      rw [← hdTπ]
      exact ht
    exact ⟨⟨x, hx⟩, rfl⟩
  have hG : Function.Surjective G := by
    intro q
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨x, y, hx, hxy⟩ := hq.2 z ((hZ z).1 z.2)
    refine ⟨⟨x, hx⟩, ?_⟩
    show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    rw [Submodule.Quotient.eq]
    exact ⟨y, Subtype.ext hxy.symm⟩
  have hker : LinearMap.ker H = LinearMap.ker G := by
    ext ⟨x, hx⟩
    rw [LinearMap.mem_ker, LinearMap.mem_ker]
    constructor
    · intro h
      have h' : π x = 0 := congrArg Subtype.val h
      obtain ⟨y, rfl⟩ := (hex x).1 h'
      show Submodule.Quotient.mk _ = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact ⟨ψ₀ y, Subtype.ext (hψ y).symm⟩
    · intro h
      have h' : (⟨f x, (hZ _).2 (hf _ hx)⟩ : Z) ∈ LinearMap.range dB :=
        (Submodule.Quotient.mk_eq_zero _).1 h
      obtain ⟨y, hy⟩ := h'
      obtain ⟨y', rfl⟩ := hq.1 x hx ⟨y, congrArg Subtype.val hy⟩
      exact Subtype.ext ((hex _).2 ⟨y', rfl⟩)
  exact ⟨(LinearMap.quotKerEquivOfSurjective H hH).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans (LinearMap.quotKerEquivOfSurjective G hG))⟩
end GlobalTheory.CompanionTheory.PerfKerCoh
