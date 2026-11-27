-- Prove2me | solution 1 for GlobalTheory.cech_kuenneth_of_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:36:03.703684+00:00
-- url     : https://prove2.me/submissions/4394a809-f7dd-4869-bcbc-3e07035c413f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_RangeRestrictCompSubtypeOfOrthogonalOfNe
import Theorems.Thm_P2M_GlobalTheory_Cube_nonempty_trunc__iso_extTensor_3b8acd97ce73
import Theorems.Thm_GlobalTheory_cech_kuenneth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits HomologicalComplex TensorProduct
universe v u
open GlobalTheory
open GlobalTheory.Cube Finset.HasAntidiagonal Module
variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] [Finite ι] [Finite κ] {K : Type u} [Field K]
namespace GlobalTheory
theorem _root_.solution (A : Cube.{v} ι K) (B : Cube.{v} κ K)
    (C : Cube.{v} (ι ⊕ₗ κ) K)
    (μ : ∀ (s : Finset ι) (t : Finset κ), s.Nonempty → t.Nonempty →
      A.obj s ⊗[K] B.obj t →ₗ[K] C.obj (sumVertex s t))
    (hμ : ∀ s t hs ht, Function.Bijective (μ s t hs ht))
    (hnat : ∀ {s s' : Finset ι} {t t' : Finset κ} (hs : s.Nonempty) (ht : t.Nonempty)
      (h : s ⊆ s') (h' : t ⊆ t') (a : A.obj s) (b : B.obj t),
      μ s' t' (hs.mono h) (ht.mono h') (res A h a ⊗ₜ res B h' b) =
        res C (sumVertex_mono h h') (μ s t hs ht (a ⊗ₜ b)))
    (hA : ∀ p, Module.Finite K ((cechComplex A).homology p))
    (hB : ∀ q, Module.Finite K ((cechComplex B).homology q)) (n : ℕ) :
    Module.Finite K ((cubeComplex (trunc₂ C)).homology (n + 2)) ∧
      finrank K ((cubeComplex (trunc₂ C)).homology (n + 2)) = ∑ x ∈ antidiagonal n,
        finrank K ((cechComplex A).homology x.1) * finrank K ((cechComplex B).homology x.2) := by
  obtain ⟨φ⟩ := nonempty_trunc₂_iso_extTensor A B C μ hμ hnat
  obtain ⟨h1, h2⟩ := cech_kuenneth A B hA hB n
  let E := (cubeHomologyMapIso φ (n + 2)).toLinearEquiv
  exact ⟨Module.Finite.equiv E.symm, E.finrank_eq.trans h2⟩
end GlobalTheory
