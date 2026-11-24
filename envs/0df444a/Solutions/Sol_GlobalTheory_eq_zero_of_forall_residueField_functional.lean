-- Prove2me | solution 1 for GlobalTheory.eq_zero_of_forall_residueField_functional
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:37:06.147043+00:00
-- url     : https://prove2.me/submissions/a70ed28d-df36-4a40-bffc-c41255eda206

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqZeroOfForallResidueFieldFunctional

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (A M : Type) [CommRing A] [IsReduced A]
    [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.Projective A M] (x : M)
    (hx : ∀ (p : Ideal A) [p.IsPrime] (l : M →ₗ[A] p.ResidueField), l x = 0) : x = 0 := by
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective A M
  have hg : g x = 0 := by
    funext i
    have hmem : g x i ∈ nilradical A := by
      rw [nilradical_eq_sInf, Ideal.mem_sInf]
      intro (p : Ideal A) (hp : p.IsPrime)
      have h := hx p ((Algebra.linearMap A p.ResidueField) ∘ₗ (LinearMap.proj i) ∘ₗ g)
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj,
        Function.eval, Algebra.linearMap_apply] at h
      have h' : g x i ∈ RingHom.ker (algebraMap A p.ResidueField) := h
      rwa [Ideal.ker_algebraMap_residueField] at h'
    exact (mem_nilradical.mp hmem).eq_zero
  have := congrArg (fun y => f y) hg
  simpa [← LinearMap.comp_apply, hfg] using this
end GlobalTheory
