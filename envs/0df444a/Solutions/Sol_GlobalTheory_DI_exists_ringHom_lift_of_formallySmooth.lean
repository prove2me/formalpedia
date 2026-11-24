-- Prove2me | solution 1 for GlobalTheory.DI.exists_ringHom_lift_of_formallySmooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:09:09.268857+00:00
-- url     : https://prove2.me/submissions/a3fa76e4-6fe7-40ef-82e2-f0bf34eab063

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRingHomLiftOfFormallySmooth

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
open GlobalTheory GlobalTheory.DI
namespace GlobalTheory.DI
theorem _root_.solution {R A C : Type} [CommRing R] [CommRing A] [CommRing C]
    (φ : R →+* A) (hφ : φ.FormallySmooth) (ψ : R →+* C) (I : Ideal C) (hI : IsNilpotent I)
    (g : A →+* C ⧸ I) (hg : g.comp φ = (Ideal.Quotient.mk I).comp ψ) :
    ∃ F : A →+* C, (∀ x, Ideal.Quotient.mk I (F x) = g x) ∧ ∀ r, F (φ r) = ψ r := by
  letI := φ.toAlgebra
  letI := ψ.toAlgebra
  haveI : Algebra.FormallySmooth R A := hφ
  let g' : A →ₐ[R] C ⧸ I :=
    { g with
      commutes' := fun r => by
        have := congrArg (· r) hg
        exact this }
  refine ⟨(Algebra.FormallySmooth.lift I hI g').toRingHom, fun x => ?_, fun r => ?_⟩
  · exact Algebra.FormallySmooth.mk_lift I hI g' x
  · have := (Algebra.FormallySmooth.lift I hI g').commutes r
    simpa [RingHom.algebraMap_toAlgebra] using this
end GlobalTheory.DI
