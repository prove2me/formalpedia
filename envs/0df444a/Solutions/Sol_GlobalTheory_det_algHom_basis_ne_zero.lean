-- Prove2me | solution 1 for GlobalTheory.det_algHom_basis_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:24:55.393414+00:00
-- url     : https://prove2.me/submissions/b1e4066e-9ed6-4627-93fe-89f714d8576d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableSpanSpanOfDetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDiscreteValuationRing Polynomial
open scoped TensorProduct
open GlobalTheory
variable {R S L ι : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing L] [IsDomain L]
  [Algebra R L] [Fintype ι] [DecidableEq ι]
namespace GlobalTheory
theorem _root_.solution (e : Basis ι R S) {P : ι → (S →ₐ[R] L)}
    (hP : Function.Injective P) : (Matrix.of fun i j => P j (e i)).det ≠ 0 := by
  intro h
  obtain ⟨c, hc, hc₀⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  have hli := (linearIndependent_algHom_toLinearMap R S L).comp P hP
  rw [Fintype.linearIndependent_iff] at hli
  refine hc (funext (hli c (e.ext fun i => ?_)))
  have := congrFun hc₀ i
  simpa [Matrix.mulVec, dotProduct, mul_comm] using this
end GlobalTheory
