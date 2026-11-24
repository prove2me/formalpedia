-- Prove2me | solution 1 for GlobalTheory.NormVal.length_eq_sum_tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:31:00.244325+00:00
-- url     : https://prove2.me/submissions/af2eb9c6-8087-4a3a-9af0-454012c35e5c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsDiscreteValuationRingLocalizationOfIsDedekindD
import Theorems.Thm_GlobalTheory_NormVal_length_quot_maximal
import Theorems.Thm_GlobalTheory_NormVal_length_localization_quot_maximal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsDiscreteValuationRing IsLocalRing Module TensorProduct
open GlobalTheory.NormVal
variable (R : Type*) {S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
  [Module.Finite R S]
variable [Fintype (MaximalSpectrum S)] (A : MaximalSpectrum S → Type*) [∀ n, CommRing (A n)]
  [∀ n, Algebra S (A n)] [∀ n, IsLocalization.AtPrime (A n) n.asIdeal]
namespace GlobalTheory.NormVal
theorem _root_.solution {X : Type*} [AddCommGroup X] [Module S X] (hX : IsFiniteLength S X) :
    ∀ [Module R X] [IsScalarTower R S X], Module.length R X =
      ∑ n : MaximalSpectrum S, Module.length (A n) (A n ⊗[S] X) * n.asIdeal.inertiaDeg R := by
  classical
  induction hX with
  | of_subsingleton => intro _ _; simp
  | @of_simple_quotient X _ _ N hs _ ih =>
    intro _ _
    obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hs
    let f : N →ₗ[S] X := N.subtype
    let g : X →ₗ[S] S ⧸ m := e.toLinearMap.comp N.mkQ
    have hf : Function.Injective f := N.subtype_injective
    have hg : Function.Surjective g := e.surjective.comp N.mkQ_surjective
    have hfg : Function.Exact f g := LinearMap.exact_iff.mpr (by simp [f, g])
    rw [length_eq_add_of_exact (f.restrictScalars R) (g.restrictScalars R) hf hg hfg, ih,
      length_quot_maximal]
    have key : ∀ n : MaximalSpectrum S,
        Module.length (A n) (A n ⊗[S] X) =
        Module.length (A n) (A n ⊗[S] N) + if n = ⟨m, hm⟩ then 1 else 0 := by
      intro n
      have : Module.Flat S (A n) := IsLocalization.flat (A n) n.asIdeal.primeCompl
      rw [length_eq_add_of_exact (AlgebraTensorModule.lTensor (A n) (A n) f)
        (AlgebraTensorModule.lTensor (A n) (A n) g)
        (Module.Flat.lTensor_preserves_injective_linearMap f hf)
        (LinearMap.lTensor_surjective (A n) hg) (Module.Flat.lTensor_exact (A n) hfg),
        ← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (A n) m).toLinearEquiv.length_eq,
        ← length_localization_quot_maximal ⟨m, hm⟩ n (A n)]
    simp_rw [key, add_mul, Finset.sum_add_distrib]
    simp
end GlobalTheory.NormVal
