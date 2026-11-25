-- Prove2me | solution 1 for GlobalTheory.InertiaMovesRoot.exists_mem_Ine_apply_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:18:18.349938+00:00
-- url     : https://prove2.me/submissions/576c1561-2e06-4398-a8b5-613d2286b82e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsCongOfCongOnFixed
import Theorems.Thm_GlobalTheory_InertiaMovesRoot_cong_on_adjoin
import Theorems.Thm_GlobalTheory_InertiaMovesRoot_mem_Ine_of_cong
import Theorems.Thm_GlobalTheory_InertiaMovesRoot_exists_cong_of_cong_on_fixed
import Theorems.Thm_ReciprocityTheory_Gal_continuousSMul_intCl


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne Pointwise
open GlobalTheory GlobalTheory.InertiaMovesRoot
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
namespace GlobalTheory.InertiaMovesRoot
theorem _root_.solution : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (l : ℕ), l.Prime → ∀ (ϖ : 𝓞 E), ϖ ∈ w.asIdeal → ϖ ∉ w.asIdeal ^ 2 → ∀ x : Ω,
    x ^ l = algebraMap E Ω (ϖ : E) → ∃ σ ∈ Ine (F := E) A, σ x ≠ x := by
  intro E Ω _ _ _ _ _ A w h l hl ϖ h1 h2 x hx
  obtain ⟨hx1, hx2⟩ := cong_on_adjoin h hl.two_le h1 h2 hx
  obtain ⟨g, hg⟩ : ∃ g : Ω ≃ₐ[E] Ω, g x ≠ x := by
    by_contra hc
    push Not at hc
    exact hx1 ((InfiniteGalois.mem_bot_iff_fixed x).mpr hc)
  letI : TopologicalSpace (IntCl E Ω) := ⊥
  haveI : DiscreteTopology (IntCl E Ω) := ⟨rfl⟩
  haveI := continuousSMul_intCl E Ω
  let H := MulAction.stabilizer (Ω ≃ₐ[E] Ω) x
  have hH : IsClosed (H : Set (Ω ≃ₐ[E] Ω)) :=
    H.isClosed_of_isOpen (stabilizer_isOpen_of_isIntegral (K := E) x)
  haveI : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  obtain ⟨k, hk, k', hk', hc⟩ := exists_cong_of_cong_on_fixed (R := 𝓞 E) H (primeBelow (F := E) A) g
    (fun b hb => by
      refine hx2 g b ?_ (valuation_le_one_intCl A b)
      rw [← InfiniteGalois.fixedField_fixingSubgroup (IntermediateField.adjoin E {x}),
        IntermediateField.mem_fixedField_iff]
      intro f hf
      exact congrArg Subtype.val (hb f (hf ⟨x, IntermediateField.mem_adjoin_simple_self E x⟩)))
  refine ⟨k' * g * k, mem_Ine_of_cong hc, fun he => hg ?_⟩
  have e1 : k x = x := hk
  have e2 : k' x = x := hk'
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, e1] at he
  exact k'.injective (he.trans e2.symm)
end GlobalTheory.InertiaMovesRoot
