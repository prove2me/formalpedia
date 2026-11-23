-- Prove2me | solution 1 for GlobalTheory.alternating_map_sum_smul_eq_det_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:51.114841+00:00
-- url     : https://prove2.me/submissions/2c630248-27c7-4d04-88af-6316cbeb89f1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped BigOperators
variable {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
  {D : ℕ}
namespace GlobalTheory
theorem _root_.solution {n : ℕ} (ω : M [⋀^Fin n]→ₗ[A] N)
    (a : Matrix (Fin n) (Fin n) A) (w : Fin n → M) :
    ω (fun i => ∑ k, a i k • w k) = a.det • ω w := by
  classical
  let φ : (Fin n → A) →ₗ[A] M := Fintype.linearCombination A w
  have key : ω.compLinearMap φ
      = ((LinearMap.toSpanSingleton A N (ω w)).compAlternatingMap Matrix.detRowAlternating) := by
    refine Module.Basis.ext_alternating (Pi.basisFun A (Fin n)) fun v hv => ?_
    have hb : Function.Bijective v := Finite.injective_iff_bijective.mp hv
    let σ : Equiv.Perm (Fin n) := Equiv.ofBijective v hb
    have e1 : (fun i => (Pi.basisFun A (Fin n)) (v i)) = (Pi.basisFun A (Fin n)) ∘ σ := rfl
    rw [e1, AlternatingMap.map_perm, AlternatingMap.map_perm]
    congr 1
    have e2 : (Matrix.detRowAlternating : (Fin n → A) [⋀^Fin n]→ₗ[A] A) (Pi.basisFun A (Fin n))
        = 1 := by
      rw [← Matrix.det_one (n := Fin n)]
      change Matrix.det _ = _
      congr 1
      ext i j
      simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    simp only [LinearMap.compAlternatingMap_apply, e2, LinearMap.toSpanSingleton_apply, one_smul,
      AlternatingMap.compLinearMap_apply]
    congr 1
    funext i
    simp [φ]
  have := congrArg (fun F : (Fin n → A) [⋀^Fin n]→ₗ[A] N => F a) key
  have e3 : (fun i => ∑ k, a i k • w k) = fun i => φ (a i) := by
    funext i
    exact (Fintype.linearCombination_apply A w (a i)).symm
  rw [e3]
  exact this
end GlobalTheory
