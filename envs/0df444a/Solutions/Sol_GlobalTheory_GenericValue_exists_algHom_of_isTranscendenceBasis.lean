-- Prove2me | solution 1 for GlobalTheory.GenericValue.exists_algHom_of_isTranscendenceBasis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:02:52.05375+00:00
-- url     : https://prove2.me/submissions/4df8e187-a6b5-4888-a918-f85b404e3806

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsAlgHomOfIsTranscendenceBasis

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
open GlobalTheory GlobalTheory.GenericValue
open MvPolynomial
variable {K : Type} [Field K]
namespace GlobalTheory.GenericValue
theorem _root_.solution {E Ω ι : Type} [Field E] [Algebra K E] [Field Ω] [IsAlgClosed Ω]
    [Algebra K Ω] {v : ι → E} (hv : IsTranscendenceBasis K v) {T : ι → Ω} (hT : AlgebraicIndependent K T) :
    ∃ j : E →ₐ[K] Ω, ∀ i, j (v i) = T i := by
  let A := Algebra.adjoin K (Set.range v)
  let g : A →ₐ[K] Ω := (aeval T).comp hv.1.aevalEquiv.symm.toAlgHom
  have hg : Function.Injective g := fun p q h =>
    hv.1.aevalEquiv.symm.injective (algebraicIndependent_iff_injective_aeval.1 hT h)
  letI : Algebra A Ω := g.toRingHom.toAlgebra
  haveI : IsScalarTower K A Ω := IsScalarTower.of_algebraMap_eq fun a => (g.commutes a).symm
  haveI : FaithfulSMul A Ω := (faithfulSMul_iff_algebraMap_injective A Ω).2 hg
  haveI := hv.isAlgebraic
  let j : E →ₐ[A] Ω := IsAlgClosed.lift
  refine ⟨j.restrictScalars K, fun i => ?_⟩
  have h := j.commutes (hv.1.aevalEquiv (X i))
  have e : algebraMap A E (hv.1.aevalEquiv (X i)) = v i := by
    rw [hv.1.algebraMap_aevalEquiv, aeval_X]
  rw [e] at h
  refine h.trans ?_
  show aeval T (hv.1.aevalEquiv.symm (hv.1.aevalEquiv (X i))) = T i
  rw [AlgEquiv.symm_apply_apply, aeval_X]
end GlobalTheory.GenericValue
