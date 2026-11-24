-- Prove2me | solution 1 for GlobalTheory.adicCompletion_tensor_quotient_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:20:20.315879+00:00
-- url     : https://prove2.me/submissions/691a56e1-d59e-4d1b-897c-8e10ef166484

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdicCompletionTensorQuotientRingEquiv
import Theorems.Thm_GlobalTheory_AdicSurj_tensor_ringEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
namespace GlobalTheory
theorem _root_.solution :
    ∀ (R₀ R K : Type) [CommRing R₀] [IsLocalRing R₀] [IsNoetherianRing R₀] [CommRing R] [IsLocalRing R]
      [Algebra R₀ R] [CommRing K] [Algebra R K] [Algebra R₀ K] [IsScalarTower R₀ R K],
      Function.Surjective (algebraMap R₀ R) →
        Nonempty (AdicCompletion (maximalIdeal R) R ⊗[R] K ≃+*
          AdicCompletion (maximalIdeal R₀) R₀ ⊗[R₀] K) := by
  intro R₀ R K _ _ _ _ _ _ _ _ _ _ hs
  have hk : RingHom.ker (algebraMap R₀ R) ≤ maximalIdeal R₀ :=
    le_maximalIdeal (RingHom.ker_ne_top _)
  have hmax : ((maximalIdeal R₀).map (algebraMap R₀ R)).IsMaximal := by
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective (hf := hs) (H := maximalIdeal.isMaximal R₀) with h | h
    · exfalso
      have h1 : (1 : R) ∈ (maximalIdeal R₀).map (algebraMap R₀ R) := h ▸ Submodule.mem_top
      obtain ⟨a, ha, hfa⟩ := (Ideal.mem_map_iff_of_surjective _ hs).mp h1
      have h2 : 1 - a ∈ maximalIdeal R₀ := hk (by rw [RingHom.mem_ker, map_sub, hfa, map_one, sub_self])
      have h3 : (1 : R₀) ∈ maximalIdeal R₀ := by simpa using add_mem h2 ha
      exact (maximalIdeal.isMaximal R₀).ne_top ((Ideal.eq_top_iff_one _).mpr h3)
    · exact h
  exact GlobalTheory.AdicSurj.tensor_ringEquiv (maximalIdeal R₀) hs _ (eq_maximalIdeal hmax).symm K
end GlobalTheory
