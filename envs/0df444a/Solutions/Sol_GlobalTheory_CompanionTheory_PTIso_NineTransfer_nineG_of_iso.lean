-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PTIso.NineTransfer.nineG_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:27:58.906898+00:00
-- url     : https://prove2.me/submissions/8f3ef0f7-abf6-4532-bf7f-b1d73ee966fc

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_GelfandSpectralNormalisation_NormalisedInvariants_PTConclAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NineTermExactIff
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TransportA
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PoitouTateSequenceTransport
import Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_NineTransfer_nine_ladder
import Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_NineTransfer_piE_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_NineTransfer_twDual_transfer
import Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_NineTransfer_loc_transfer
import Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_NineTransfer_local_degree_zero_square
import Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_NineTransfer_local_degree_one_square
import Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_NineTransfer_local_degree_two_square
import Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_NineTransfer_trace_pairing_degree_zero_square
import Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_NineTransfer_trace_pairing_degree_two_square
import Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_NineTransfer_trace_pairing_degree_one_square
import Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_subgroupIso_coe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CompanionTheory.PTIso.subgroupIso_coe


attribute [local simp] GlobalTheory.CompanionTheory.PTIso.NineTransfer.piE_apply

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso ReciprocityTheory.Neutral.Bridge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PTIso GlobalTheory.CompanionTheory.PTIso.NineTransfer
namespace GlobalTheory.CompanionTheory.PTIso.NineTransfer
theorem _root_.solution {R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
    {Γ Γ' : Type} [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ'] {I I' : Type}
    [Fintype I] [Fintype I'] {D : I → Type} {D' : I' → Type} [∀ i, Group (D i)]
    [∀ i, TopologicalSpace (D i)] [∀ i, Group (D' i)] [∀ i, TopologicalSpace (D' i)]
    (φ : ∀ i, D i →* Γ) (hφ : ∀ i, Continuous (φ i)) (φ' : ∀ i, D' i →* Γ')
    (hφ' : ∀ i, Continuous (φ' i)) (χ : Γ →* Rˣ) (χ' : Γ' →* Rˣ) {M : Type} [AddCommGroup M]
    [Module R M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R Γ M)
    (ρ' : Representation R Γ' M) (eG : Γ ≃ₜ* Γ') (eI : I ≃ I') (eD : ∀ i, D i ≃ₜ* D' (eI i)) :
    (∀ i d, φ' (eI i) (eD i d) = eG (φ i d)) → (∀ g, χ' (eG g) = χ g) →
    (∀ g m, ρ' (eG g) m = ρ g m) →
    ∀ (j : ∀ i, H2 ((charRep χ).comp (φ i)) →ₗ[R] R)
      (j' : ∀ i, H2 ((charRep χ').comp (φ' i)) →ₗ[R] R)
      (hρ : ContAction ρ) (hρ' : ContAction ρ'),
      (∀ (i : I) (z : Z2 ((charRep χ).comp (φ i))) (z' : Z2 ((charRep χ').comp (φ' (eI i)))),
        (∀ g h, z'.1 (eD i g, eD i h) = z.1 (g, h)) →
          j' (eI i) (Submodule.Quotient.mk z') = j i (Submodule.Quotient.mk z)) →
      NineG φ' hφ' χ' j' ρ' hρ' → NineG φ hφ χ j ρ hρ := by
  intro hD hχ hc j j' hρ hρ' hj hN
  have hd := twDual_transfer χ χ' ρ ρ' eG hχ hc
  have hl := loc_transfer φ φ' ρ ρ' eG eI eD hD hc
  unfold NineG at hN ⊢
  have dual_sq : ∀ {A A' : Type} [AddCommGroup A] [Module R A] [AddCommGroup A'] [Module R A']
      {Y Y' : Type} [AddCommGroup Y] [Module R Y] [AddCommGroup Y'] [Module R Y']
      (β : A' ≃ₗ[R] A) (p : Y' ≃ₗ[R] Y) (t : Y →ₗ[R] Module.Dual R A)
      (t' : Y' →ₗ[R] Module.Dual R A') (_ : ∀ x y, t (p x) (β y) = t' x y) (x : Y'),
      t (p x) = β.symm.dualMap (t' x) := by
    intro A A' _ _ _ _ Y Y' _ _ _ _ β p t t' h x
    refine LinearMap.ext fun y => ?_
    obtain ⟨y', rfl⟩ := β.surjective y
    simp [LinearEquiv.dualMap_apply, h]
  exact nine_ladder (equivH0OfIso eG ρ' ρ hc) (equivH1OfIso eG ρ' ρ hc) (equivH2OfIso eG ρ' ρ hc)
    (P0 φ φ' ρ ρ' eI eD hl) (P1 φ φ' ρ ρ' eI eD hl) (P2 φ φ' ρ ρ' eI eD hl)
    (equivH2OfIso eG _ _ hd).symm.dualMap (equivH1OfIso eG _ _ hd).symm.dualMap (equivH0OfIso eG _ _ hd).symm.dualMap
    (local_degree_zero_square φ φ' ρ ρ' eG eI eD hc hl) (local_degree_one_square φ hφ φ' hφ' ρ ρ' eG eI eD hD hc hl)
    (local_degree_two_square φ hφ φ' hφ' ρ ρ' eG eI eD hD hc hl)
    (dual_sq _ _ _ _ (trace_pairing_degree_zero_square φ hφ φ' hφ' χ χ' ρ ρ' eG eI eD hD hd hl j j' hj))
    (dual_sq _ _ _ _ (trace_pairing_degree_one_square φ hφ φ' hφ' χ χ' ρ ρ' eG eI eD hD hc hd hl j j' hj hρ hρ'))
    (dual_sq _ _ _ _ (trace_pairing_degree_two_square φ φ' χ χ' ρ ρ' eG eI eD hd hl j j' hj)) hN
end GlobalTheory.CompanionTheory.PTIso.NineTransfer
