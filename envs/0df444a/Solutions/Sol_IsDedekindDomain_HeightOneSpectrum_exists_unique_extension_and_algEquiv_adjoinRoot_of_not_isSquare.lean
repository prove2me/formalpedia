-- Prove2me | solution 1 for IsDedekindDomain.HeightOneSpectrum.exists_unique_extension_and_algEquiv_adjoinRoot_of_not_isSquare
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/4b04e56f-a711-56b7-befa-06405ffc4553

import Definitions.Def_DedekindDomain_Completion_BaseChange
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_exists_unique_extension_algEquiv_adicCompletion_of_isField_tensor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDedekindDomain_HeightOneSpectrum_exists_unique_extension_and_algEquiv_adjoinRoot_of_not_isSquare

set_option autoImplicit false

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Polynomial

namespace QMBAux

open Polynomial

theorem isField_and_nonempty_algEquiv (F A : Type) [Field F] [CommRing A] [Algebra F A]
    (a : F) (ha : ¬ IsSquare a) (hA : Module.finrank F A = 2) (s : A)
    (hs : s ^ 2 = algebraMap F A a) :
    IsField A ∧ Nonempty (A ≃ₐ[F] AdjoinRoot (X ^ 2 - C a)) := by
  have hirr : Irreducible (X ^ 2 - C a : F[X]) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two (fun b hb => ha ⟨b, by rw [← hb, sq]⟩)
  have hf0 : (X ^ 2 - C a : F[X]) ≠ 0 := hirr.ne_zero

  have hRF : IsField (AdjoinRoot (X ^ 2 - C a : F[X])) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp
      (PrincipalIdealRing.isMaximal_of_irreducible hirr)
  have hdimR : Module.finrank F (AdjoinRoot (X ^ 2 - C a : F[X])) = 2 := by
    rw [(AdjoinRoot.powerBasis hf0).finrank, AdjoinRoot.powerBasis_dim, natDegree_X_pow_sub_C]
  haveI : Nontrivial A := Module.nontrivial_of_finrank_pos (R := F) (by rw [hA]; exact two_pos)
  haveI : Module.Finite F A := Module.finite_of_finrank_pos (by rw [hA]; exact two_pos)
  haveI : Module.Finite F (AdjoinRoot (X ^ 2 - C a : F[X])) :=
    Module.finite_of_finrank_pos (by rw [hdimR]; exact two_pos)
  have heval : (X ^ 2 - C a : F[X]).eval₂ (Algebra.ofId F A) s = 0 := by
    simp [hs]
  let φ : AdjoinRoot (X ^ 2 - C a : F[X]) →ₐ[F] A :=
    AdjoinRoot.liftAlgHom _ (Algebra.ofId F A) s heval
  have hiff := LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := φ.toLinearMap)
    (hdimR.trans hA.symm)
  have hinj : Function.Injective φ := by
    letI := hRF.toField
    exact φ.toRingHom.injective
  have hsurj : Function.Surjective φ := hiff.mp hinj
  let e := AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩
  exact ⟨e.symm.toMulEquiv.isField hRF, ⟨e.symm⟩⟩

open scoped TensorProduct in
open scoped TensorProduct.RightActions in

theorem tensor_step (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K']
    [Algebra K K'] (hdeg : Module.finrank K K' = 2) (d : K) (r : K')
    (hr : r ^ 2 = algebraMap K K' d) (v : HeightOneSpectrum (𝓞 K))
    (hd : ¬ IsSquare (algebraMap K (v.adicCompletion K) d)) :
    ∃ w : v.Extension (𝓞 K'),
      (∀ w' : v.Extension (𝓞 K'), w' = w) ∧
      Module.finrank (v.adicCompletion K) (w.1.adicCompletion K') = 2 ∧
      (algebraMap K' (w.1.adicCompletion K') r) ^ 2 =
        algebraMap (v.adicCompletion K) (w.1.adicCompletion K')
          (algebraMap K (v.adicCompletion K) d) := by
  have hsq : (r ⊗ₜ[K] (1 : v.adicCompletion K)) ^ 2 =
      algebraMap (v.adicCompletion K) (K' ⊗[K] v.adicCompletion K)
        (algebraMap K (v.adicCompletion K) d) := by
    rw [Algebra.TensorProduct.tmul_pow, one_pow, hr, TensorProduct.RightActions.algebraMap_eval,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hA : Module.finrank (v.adicCompletion K) (K' ⊗[K] v.adicCompletion K) = 2 := by
    rw [TensorProduct.finrank_rightAlgebra, hdeg]
  have hF : IsField (K' ⊗[K] v.adicCompletion K) :=
    (isField_and_nonempty_algEquiv (v.adicCompletion K) (K' ⊗[K] v.adicCompletion K) _ hd hA _
      hsq).1
  obtain ⟨w, e, huniq, hex, hfin⟩ :=
    IsDedekindDomain.HeightOneSpectrum.exists_unique_extension_algEquiv_adicCompletion_of_isField_tensor
      K K' v hF
  refine ⟨w, huniq, hfin.trans hdeg, ?_⟩
  rw [← hex, ← map_pow, hsq, AlgEquiv.commutes]

end QMBAux

theorem solution
    (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (hdeg : Module.finrank K K' = 2)
    (d : K) (r : K') (hr : r ^ 2 = algebraMap K K' d) (hgen : Algebra.adjoin K {r} = ⊤)
    (v : HeightOneSpectrum (𝓞 K))
    (hd : ¬ IsSquare (algebraMap K (v.adicCompletion K) d)) :
    (∀ 𝔳 𝔳' : v.Extension (𝓞 K'), 𝔳 = 𝔳') ∧
    ∀ 𝔳 : v.Extension (𝓞 K'),
      Nonempty (𝔳.1.adicCompletion K' ≃ₐ[v.adicCompletion K]
        AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C (algebraMap K (v.adicCompletion K) d))) := by
  have _ := hgen
  obtain ⟨w, huniq, hfin, hsq⟩ := QMBAux.tensor_step K K' hdeg d r hr v hd
  refine ⟨fun 𝔳 𝔳' => (huniq 𝔳).trans (huniq 𝔳').symm, fun 𝔳 => ?_⟩
  obtain rfl := huniq 𝔳
  exact (QMBAux.isField_and_nonempty_algEquiv (v.adicCompletion K) (𝔳.1.adicCompletion K') _ hd
    hfin _ hsq).2

end S_IsDedekindDomain_HeightOneSpectrum_exists_unique_extension_and_algEquiv_adjoinRoot_of_not_isSquare
end P2MW
export P2MW.S_IsDedekindDomain_HeightOneSpectrum_exists_unique_extension_and_algEquiv_adjoinRoot_of_not_isSquare (solution)
