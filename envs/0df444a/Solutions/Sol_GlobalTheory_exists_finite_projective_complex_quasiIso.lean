-- Prove2me | solution 1 for GlobalTheory.exists_finite_projective_complex_quasiIso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:36:15.767023+00:00
-- url     : https://prove2.me/submissions/d0c3aec8-90bf-4a54-9039-5714e79a1b97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Theorems.Thm_GlobalTheory_quasiIso_tensorLeft_of_flat
import Theorems.Thm_GlobalTheory_quasiIso_extendScalars_of_flat
import Theorems.Thm_GlobalTheory_exists_finite_complex_quasiIso
import Theorems.Thm_GlobalTheory_flat_zero_of_quasiIso

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory TensorProduct
universe u v w
open GlobalTheory
open Limits
variable {R : Type u} [CommRing R]
namespace GlobalTheory
theorem _root_.solution [IsNoetherianRing R]
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) (hn : ∀ p, n < p → IsZero (C.X p))
    (hflat : ∀ p, Module.Flat R (C.X p)) (hfin : ∀ p, Module.Finite R (C.homology p)) :
    ∃ (K : CochainComplex (ModuleCat.{u} R) ℕ) (φ : K ⟶ C),
      (∀ p, n < p → IsZero (K.X p)) ∧ (∀ p, Module.Finite R (K.X p)) ∧
      (∀ p, 1 ≤ p → Module.Free R (K.X p)) ∧ (∀ p, Module.Projective R (K.X p)) ∧
      QuasiIso φ ∧
      (∀ M : ModuleCat.{u} R,
        QuasiIso (((MonoidalCategory.tensorLeft M).mapHomologicalComplex _).map φ)) ∧
      (∀ (S : Type w) [CommRing S] [Algebra R S], QuasiIso
        (((ModuleCat.extendScalars.{u, w, u} (algebraMap R S)).mapHomologicalComplex _).map φ)) := by
  obtain ⟨K, φ, h1, h2, h3, h4⟩ := exists_finite_complex_quasiIso C n hn hfin
  have h5 : ∀ p, 1 ≤ p → Module.Flat R (K.X p) := fun p hp => by
    have := h3 p hp
    infer_instance
  have h6 : ∀ p, Module.Flat R (K.X p) := by
    rintro (_ | p)
    · exact flat_zero_of_quasiIso φ h5 hflat n h1 hn
    · exact h5 _ (Nat.le_add_left 1 p)
  refine ⟨K, φ, h1, h2, h3, fun p => ?_, h4,
    quasiIso_tensorLeft_of_flat φ h6 hflat n h1 hn,
    fun S _ _ => quasiIso_extendScalars_of_flat φ h6 hflat n h1 hn _⟩
  have := Module.finitePresentation_of_finite R (K.X p)
  exact Module.Flat.projective_of_finitePresentation
end GlobalTheory
