-- Prove2me | solution 1 for GlobalTheory.PadicComplexIso.exists_ringEquiv_over
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:36:10.916797+00:00
-- url     : https://prove2.me/submissions/52197279-8b8f-44f0-9a39-76e49fa8131a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MkLeContinuumOfDenseRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open Cardinal
open GlobalTheory GlobalTheory.PadicComplexIso
namespace GlobalTheory.PadicComplexIso
theorem _root_.solution (R K L : Type) [Field R] [Field K] [Field L] [IsAlgClosed K]
    [IsAlgClosed L] [Algebra R K] [Algebra R L] (hR : #R ≤ ℵ₀) (hK : ℵ₀ < #K) (hKL : #K = #L) :
    ∃ e : K ≃+* L, ∀ x : R, e (algebraMap R K x) = algebraMap R L x := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis R K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis R L
  have hL : ℵ₀ < #L := hKL ▸ hK
  have hsK : #K = #s := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ hs hR hK
  have htL : #L = #t := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ ht hR hL
  obtain ⟨e⟩ : Nonempty (s ≃ t) := Cardinal.eq.1 (hsK.symm.trans (hKL.trans htL))
  let _ := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hs
  let _ := IsAlgClosed.isAlgClosure_of_transcendence_basis _ ht
  let e0 : Algebra.adjoin R (Set.range ((↑) : s → K)) ≃ₐ[R] Algebra.adjoin R (Set.range ((↑) : t → L)) :=
    hs.1.aevalEquiv.symm.trans ((MvPolynomial.renameEquiv R e).trans ht.1.aevalEquiv)
  refine ⟨IsAlgClosure.equivOfEquiv K L e0.toRingEquiv, fun x => ?_⟩
  rw [IsScalarTower.algebraMap_apply R (Algebra.adjoin R (Set.range ((↑) : s → K))) K,
    IsAlgClosure.equivOfEquiv_algebraMap, AlgEquiv.coe_ringEquiv,
    AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
end GlobalTheory.PadicComplexIso
