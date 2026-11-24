-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.EichlerTransf.eichler_transformation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:53:23.905461+00:00
-- url     : https://prove2.me/submissions/f2970490-a338-4e11-9d52-380c8f153382

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ExtendByZeroApplyOfNe
import Theorems.Thm_GlobalTheory_CompanionTheory_EichlerTransf_eichler_of_involution
import Theorems.Thm_Formalism_REAL_Jm_conjTranspose
import Theorems.Thm_Formalism_REAL_Jm_mul_self


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EichlerTransf
open scoped ComplexOrder
variable {n m : ℕ}
namespace GlobalTheory.CompanionTheory.EichlerTransf
theorem _root_.solution : ∀ {n m : ℕ} (ε : Fin n → Bool) (x y : Matrix (Fin n) (Fin m) ℂ) (A : Set (Fin m)),
    xᴴ * Formalism.REAL.Jm ε * x = 0 → xᴴ * Formalism.REAL.Jm ε * y = 1 →
    ∃ (u : Matrix (Fin m) (Fin n) ℂ) (w : Matrix (Fin n) (Fin m) ℂ), (∀ i v, i ∉ A → u i v = 0) ∧
      (∀ v i, i ∉ A → w v i = 0) ∧ (∀ i j, j ∈ A → (u * x) i j = 0) ∧
      1 + x * u + w * xᴴ * Formalism.REAL.Jm ε ∈ Formalism.QuantumDeterminants.UH (Formalism.REAL.Jm ε) ∧
      ∀ v ∈ Submodule.span ℂ (Set.range (fun i : A => (1 + x * u + w * xᴴ * Formalism.REAL.Jm ε) *ᵥ fun j => x j i) ∪
          Set.range (fun i : A => (1 + x * u + w * xᴴ * Formalism.REAL.Jm ε) *ᵥ fun j => y j i)),
        Formalism.REAL.Jm ε *ᵥ v ∈ Submodule.span ℂ (Set.range (fun i : A => (1 + x * u + w * xᴴ * Formalism.REAL.Jm ε) *ᵥ fun j => x j i) ∪
          Set.range (fun i : A => (1 + x * u + w * xᴴ * Formalism.REAL.Jm ε) *ᵥ fun j => y j i)) :=
  fun ε x y A h1 h2 => eichler_of_involution (Formalism.REAL.Jm ε) (Formalism.REAL.Jm_mul_self ε)
    (Formalism.REAL.Jm_conjTranspose ε) x y A h1 h2
end GlobalTheory.CompanionTheory.EichlerTransf
