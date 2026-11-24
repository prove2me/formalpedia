-- Prove2me | solution 1 for GlobalTheory.UnRep.exists_norm_one_isUnit_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:10:29.429798+00:00
-- url     : https://prove2.me/submissions/d222ab60-8dcd-4cac-9479-c48ccdbe1500

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_NormOneInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_AdelicUnitaryScalingUnit
import Theorems.Thm_GlobalTheory_UnRep_finite_not_isUnit_det
import Theorems.Thm_GlobalTheory_UnRep_finite_primes_one_sub
import Theorems.Thm_GlobalTheory_UnRep_infinite_norm_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep
namespace GlobalTheory.UnRep
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E), Module.finrank F E = 2 → (∀ x, c (c x) = x) → c ≠ 1 → ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) (RA F E)) (e : FiniteAdeleRing (𝓞 F) F), e * e = e → {v | e v ≠ 0}.Finite → ∃ lam : E, lam * c lam = 1 ∧ IsUnit (1 + ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] lam) • ((e ⊗ₜ[F] (1 : E)) • g + ((1 - e) ⊗ₜ[F] (1 : E)) • (1 : Matrix (Fin n) (Fin n) (RA F E)))).det := by
  intro F E _ _ _ _ _ c hrk hc hc1 n g e he hfin
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  have hsub : ((1 - e) ⊗ₜ[F] (1 : E) : RA F E) = 1 - e ⊗ₜ[F] (1 : E) := by
    rw [TensorProduct.sub_tmul, Algebra.TensorProduct.one_def]
  have hM : {M : Ideal (RA F E) | M.IsMaximal ∧ 1 - e ⊗ₜ[F] (1 : E) ∈ M}.Finite := by
    refine ((finite_primes_one_sub F e hfin).biUnion fun P _ =>
      Algebra.QuasiFinite.finite_primesOver (S := RA F E) P).subset ?_
    rintro M ⟨hM, h⟩
    haveI := hM.isPrime
    refine Set.mem_biUnion (x := M.under (FiniteAdeleRing (𝓞 F) F)) ⟨inferInstance, ?_⟩
      ⟨inferInstance, inferInstance⟩
    rw [← hsub] at h
    exact h
  have hbad := finite_not_isUnit_det
    (Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E).toRingHom g (e ⊗ₜ[F] (1 : E))
    (by rw [Algebra.TensorProduct.tmul_mul_tmul, he, mul_one]) hM
  obtain ⟨l, hl, hl'⟩ := (infinite_norm_one c hc hc1).exists_notMem_finite hbad
  refine ⟨l, hl, ?_⟩
  rw [hsub]
  exact not_not.1 hl'
end GlobalTheory.UnRep
