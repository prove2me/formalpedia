-- Prove2me | solution 1 for IsArtinianRing.flat_and_finite_and_isNoetherianRing_tensorProduct_int_of_finite_residueField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/614ad7ac-cb19-5339-9c0d-f06811e44c8e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsArtinianRing_flat_and_finite_and_isNoetherianRing_tensorProduct_int_of_finite_residueField

set_option autoImplicit false

open IsLocalRing TensorProduct

theorem solution
    (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [Finite (ResidueField C)]
    (O : Type) [CommRing O] [IsNoetherianRing O] [Module.Flat ℤ O] :
    Module.Flat C (C ⊗[ℤ] O) ∧ (Algebra.TensorProduct.includeRight : O →ₐ[ℤ] C ⊗[ℤ] O).toRingHom.Finite ∧
      IsNoetherianRing (C ⊗[ℤ] O) ∧
      IsNilpotent (Ideal.map (algebraMap C (C ⊗[ℤ] O)) (maximalIdeal C)) := by

  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := C)
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hn

  haveI : Finite C := by
    have hfin : Finite (C ⧸ (⊥ : Ideal C)) :=
      IsLocalRing.finite_quotient_iff.2 ⟨n, by rw [hn, Ideal.zero_eq_bot]⟩
    exact Finite.of_equiv _ (RingEquiv.quotientBot C).toEquiv
  haveI : Module.Finite ℤ C := Module.Finite.of_finite
  have hfinO : Module.Finite O (O ⊗[ℤ] C) := inferInstance

  have hb : (Algebra.TensorProduct.includeRight : O →ₐ[ℤ] C ⊗[ℤ] O).toRingHom.Finite := by
    have heq : (Algebra.TensorProduct.includeRight : O →ₐ[ℤ] C ⊗[ℤ] O).toRingHom =
        (Algebra.TensorProduct.comm ℤ O C).toRingHom.comp (algebraMap O (O ⊗[ℤ] C)) := by
      ext o
      simp [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.comm_tmul,
        Algebra.TensorProduct.algebraMap_apply]
    rw [heq]
    exact RingHom.Finite.comp (RingHom.Finite.of_surjective _ (Algebra.TensorProduct.comm ℤ O C).surjective)
      (RingHom.finite_algebraMap.2 hfinO)
  refine ⟨inferInstance, hb, ?_, ⟨n, ?_⟩⟩
  ·
    letI : Algebra O (C ⊗[ℤ] O) := (Algebra.TensorProduct.includeRight : O →ₐ[ℤ] C ⊗[ℤ] O).toRingHom.toAlgebra
    haveI : Module.Finite O (C ⊗[ℤ] O) := hb
    exact IsNoetherianRing.of_finite O (C ⊗[ℤ] O)
  ·
    rw [← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot, Ideal.zero_eq_bot]

end S_IsArtinianRing_flat_and_finite_and_isNoetherianRing_tensorProduct_int_of_finite_residueField
end P2MW
export P2MW.S_IsArtinianRing_flat_and_finite_and_isNoetherianRing_tensorProduct_int_of_finite_residueField (solution)
