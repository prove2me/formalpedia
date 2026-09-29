-- Prove2me | solution 1 for HopfAlgebra.exists_finite_nTorsion_quotient_of_normOneTorus_generators
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/10168c9e-a7b5-51b6-b56f-d80e537393e3

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_HopfAlgebra_exists_cocomm_adjoin_nTorsion_quotient_of_normOneTorus_generators
import Theorems.Thm_HopfAlgebra_finite_of_normOneTorus_nTorsion_generators_and_points
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_finite_nTorsion_quotient_of_normOneTorus_generators

open scoped TensorProduct

theorem solution
    (K : Type) [Field K] [CharZero K] (c : K) (hc : c ≠ 0) (hnsq : ¬ IsSquare c)
    (n : ℕ) [Fact n.Prime]
    (δ : AlgebraicClosure K) (hδ : δ * δ = algebraMap K (AlgebraicClosure K) c)
    (B : Type) [CommRing B] [HopfAlgebra K B] (u v : B)
    (hrel : u ^ 2 - algebraMap K B c * v ^ 2 = 1)
    (hcu : Coalgebra.comul (R := K) u = u ⊗ₜ[K] u + c • (v ⊗ₜ[K] v))
    (hcv : Coalgebra.comul (R := K) v = u ⊗ₜ[K] v + v ⊗ₜ[K] u)
    (hliftB : ∀ (w z : AlgebraicClosure K),
      w ^ 2 - algebraMap K (AlgebraicClosure K) c * z ^ 2 = 1 →
      ∃! f : B →ₐ[K] AlgebraicClosure K, f u = w ∧ f v = z) :
    ∃ (A : Type) (_ : CommRing A) (_ : HopfAlgebra K A),
      Module.Finite K A ∧ Coalgebra.IsCocomm K A ∧
      ∃ (u' v' : A),
        (u' ^ 2 - algebraMap K A c * v' ^ 2 = 1) ∧
        (Coalgebra.comul (R := K) u' = u' ⊗ₜ[K] u' + c • (v' ⊗ₜ[K] v')) ∧
        (Coalgebra.comul (R := K) v' = u' ⊗ₜ[K] v' + v' ⊗ₜ[K] u') ∧
        (∀ f : A →ₐ[K] AlgebraicClosure K, (f u' + f v' * δ) ^ n = 1) ∧
        (∀ (w z : AlgebraicClosure K),
          w ^ 2 - algebraMap K (AlgebraicClosure K) c * z ^ 2 = 1 →
          (w + z * δ) ^ n = 1 →
          ∃! f : A →ₐ[K] AlgebraicClosure K, f u' = w ∧ f v' = z) := by
  obtain ⟨A, iCR, iHA, hcc, u', v', hgen, hrel', hcu', hcv', hn', hlift'⟩ :=
    HopfAlgebra.exists_cocomm_adjoin_nTorsion_quotient_of_normOneTorus_generators
      K c hc hnsq n δ hδ B u v hrel hcu hcv hliftB
  have hfin : Module.Finite K A := by
    letI := iCR; letI := iHA
    exact HopfAlgebra.finite_of_normOneTorus_nTorsion_generators_and_points
      K c hc hnsq n δ hδ A u' v' hgen hrel' hn' hlift'
  exact ⟨A, iCR, iHA, hfin, hcc, u', v', hrel', hcu', hcv', hn', hlift'⟩

end S_HopfAlgebra_exists_finite_nTorsion_quotient_of_normOneTorus_generators
end P2MW
export P2MW.S_HopfAlgebra_exists_finite_nTorsion_quotient_of_normOneTorus_generators (solution)
