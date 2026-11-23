-- Prove2me | solution 1 for GroundTheory.Global.exists_ringEquiv_extend_of_isTranscendenceBasis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:16:11.142001+00:00
-- url     : https://prove2.me/submissions/e069c531-d2dd-4757-875a-0d17ce8c1197

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ExistsRingEquivExtendOfIsTranscendenceBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Cardinal Polynomial IntermediateField
variable {Ω : Type*} [Field Ω] [IsAlgClosed Ω]
namespace GroundTheory.Global
theorem _root_.solution
    {F₁ F₂ : Type*} [Field F₁] [Field F₂] [Algebra F₁ Ω] [Algebra F₂ Ω]
    (e : F₁ ≃+* F₂) {ι κ : Type*} {v₁ : ι → Ω} {v₂ : κ → Ω}
    (h₁ : IsTranscendenceBasis F₁ v₁) (h₂ : IsTranscendenceBasis F₂ v₂) (φ : ι ≃ κ) :
    ∃ σ : Ω ≃+* Ω, (∀ a : F₁, σ (algebraMap F₁ Ω a) = algebraMap F₂ Ω (e a)) ∧
      ∀ i, σ (v₁ i) = v₂ (φ i) := by
  have := IsAlgClosed.isAlgClosure_of_transcendence_basis v₁ h₁
  have := IsAlgClosed.isAlgClosure_of_transcendence_basis v₂ h₂
  let e' : Algebra.adjoin F₁ (Set.range v₁) ≃+* Algebra.adjoin F₂ (Set.range v₂) :=
    h₁.1.aevalEquiv.symm.toRingEquiv.trans <| (MvPolynomial.mapEquiv ι e).trans <|
      (MvPolynomial.renameEquiv F₂ φ).toRingEquiv.trans h₂.1.aevalEquiv.toRingEquiv
  have key : ∀ p : MvPolynomial ι F₁,
      IsAlgClosure.equivOfEquiv Ω Ω e' (MvPolynomial.aeval v₁ p) =
        MvPolynomial.aeval v₂ (MvPolynomial.rename φ (MvPolynomial.map (e : F₁ →+* F₂) p)) := by
    intro p
    rw [← h₁.1.algebraMap_aevalEquiv, IsAlgClosure.equivOfEquiv_algebraMap,
      ← h₂.1.algebraMap_aevalEquiv]
    congr 1
    simp [e']
  refine ⟨IsAlgClosure.equivOfEquiv Ω Ω e', fun a => ?_, fun i => ?_⟩
  · simpa using key (MvPolynomial.C a)
  · simpa using key (MvPolynomial.X i)
end GroundTheory.Global
