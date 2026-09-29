-- Prove2me | solution 1 for HorizontalPadicL.disjointRamification_seededFrobeniusClass_exists_v4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-25T14:18:22.562637+00:00
-- url     : https://prove2.me/submissions/c1b35dba-8456-4200-8608-1bf75bda9c3c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_HorizontalPadicL_eigenform_residualGaloisRepresentation_exists_v2
import Theorems.Thm_HorizontalPadicL_residualKernel_discr_prime_dvd_level_mul_p
import Theorems.Thm_HorizontalPadicL_SeedCyclotomicGaloisCharacterDataV2_exists_fullOrder_value_v2
import Theorems.Thm_HorizontalPadicL_coprimeDiscriminant_simultaneousSeededFrobeniusClass_exists_v2

set_option autoImplicit false

namespace HorizontalPadicL

theorem _root_.solution
    {N k p : ℕ} [Fact p.Prime]
    (hN : 0 < N) (hk : 2 ≤ k) (_heven : Even k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (η : DirichletCharacterWithLevel)
    (m B : ℕ) (hB : 0 < B)
    (hηcoprime : Nat.Coprime (N * p) η.2.conductor)
    (V : SeededEigenformPadicPlaceData (p := p) f η)
    (_R : ResidualEigenformRepresentationData f η V)
    (C : SeedCyclotomicGaloisCharacterDataV2 N p m η) :
    Nonempty (SeededOrderlyFrobeniusClassData f η m B V) := by
  obtain ⟨D⟩ := eigenform_residualGaloisRepresentation_exists_v2
    hN hk ι f V.embedding
  obtain ⟨a, ha⟩ := C.exists_fullOrder_value_v2 η
  exact coprimeDiscriminant_simultaneousSeededFrobeniusClass_exists_v2
    hN hk ι f η m B hB hηcoprime V D a ha
      (residualKernel_discr_prime_dvd_level_mul_p hN hk f V.embedding D)

end HorizontalPadicL
