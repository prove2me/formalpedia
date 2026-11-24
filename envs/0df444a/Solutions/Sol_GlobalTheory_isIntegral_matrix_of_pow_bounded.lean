-- Prove2me | solution 1 for GlobalTheory.isIntegral_matrix_of_pow_bounded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:03:31.03418+00:00
-- url     : https://prove2.me/submissions/d743de07-501d-4859-9389-45c0677cb4ab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralOfIsCompactClosureZpowers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory
open NumberField IsDedekindDomain
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution {O K : Type} [CommRing O] [IsNoetherianRing O]
    [Field K] [Algebra O K] {n : ℕ} (g : Matrix (Fin n) (Fin n) K) (a : K) (ha : a ≠ 0)
    (h : ∀ (k : ℕ) (i j : Fin n), ∃ b : O, algebraMap O K b = a * (g ^ k) i j) :
    IsIntegral O g := by
  classical
  let ψ : (Fin n → Fin n → O) →ₗ[O] Matrix (Fin n) (Fin n) K :=
    { toFun := fun b => Matrix.of fun i j => algebraMap O K (b i j)
      map_add' := fun b c => by ext i j; simp
      map_smul' := fun c b => by ext i j; simp [Algebra.smul_def] }
  let φ : Matrix (Fin n) (Fin n) K →ₗ[O] Matrix (Fin n) (Fin n) K :=
    { toFun := fun A => a • A
      map_add' := fun A B => smul_add a A B
      map_smul' := fun c A => smul_comm a c A }
  have hφ : Function.Injective φ := fun A B hAB => smul_right_injective _ ha hAB
  have hP : (LinearMap.range ψ).FG := by
    rw [LinearMap.range_eq_map]; exact Submodule.FG.map _ Module.Finite.fg_top
  haveI := isNoetherian_of_fg_of_noetherian _ hP
  have hle : Submodule.map φ (Subalgebra.toSubmodule (Algebra.adjoin O {g})) ≤
      LinearMap.range ψ := by
    rw [Algebra.adjoin_eq_span, ← Submonoid.powers_eq_closure, Submodule.map_span_le]
    rintro _ ⟨k, rfl⟩
    choose b hb using h k
    exact ⟨b, by ext i j; simp [ψ, φ, hb]⟩
  exact IsIntegral.of_mem_of_fg _ (Submodule.fg_of_fg_map_injective φ hφ
    (Submodule.FG.of_le_of_isNoetherian hle)) g (Algebra.self_mem_adjoin_singleton O g)
end _root_.GlobalTheory
end GlobalTheory
