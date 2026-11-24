-- Prove2me | solution 1 for GlobalTheory.matrix_exists_rightInverse_of_saturated_rows
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:19:52.568263+00:00
-- url     : https://prove2.me/submissions/fcf1d24f-fc6e-4fcb-8fdb-33cb16cafad1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralBasisChangeDeterminant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Matrix
namespace GlobalTheory
theorem _root_.solution {O : Type} [CommRing O] [IsDomain O]
    [IsPrincipalIdealRing O] {m n : ℕ} (N : Matrix (Fin m) (Fin n) O)
    (hinj : ∀ b, Matrix.vecMul b N = 0 → b = 0)
    (hsat : ∀ (r : O) (x : Fin n → O) (b : Fin m → O), r ≠ 0 → r • x = Matrix.vecMul b N →
      ∃ b', x = Matrix.vecMul b' N) :
    ∃ Q : Matrix (Fin n) (Fin m) O, N * Q = 1 := by
  let g : (Fin m → O) →ₗ[O] (Fin n → O) := Matrix.vecMulLinear N
  have hg : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro b hb
    exact hinj b hb
  haveI : Module.IsTorsionFree O ((Fin n → O) ⧸ LinearMap.range g) := by
    refine Module.IsTorsionFree.of_smul_eq_zero ?_
    intro r x h
    by_cases hr : r = 0
    · exact Or.inl hr
    right
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
    obtain ⟨b, hb⟩ := h
    obtain ⟨b', hb'⟩ := hsat r x b hr hb.symm
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨b', hb'.symm⟩
  haveI : Module.Free O ((Fin n → O) ⧸ LinearMap.range g) := inferInstance
  have hex : Function.Exact g (LinearMap.range g).mkQ := LinearMap.exact_map_mkQ_range g
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective (LinearMap.range g).mkQ
    (Submodule.range_mkQ _)
  have hs' : ∃ s, (LinearMap.range g).mkQ ∘ₗ s = LinearMap.id := ⟨s, hs⟩
  have hl' : ∃ l, l ∘ₗ g = LinearMap.id :=
    ((hex.split_tfae hg (Submodule.mkQ_surjective _)).out 0 1).mp hs'
  obtain ⟨l, hl⟩ := hl'
  refine ⟨LinearMap.toMatrixRight' l, ?_⟩
  ext i j
  have h1 : ∀ x, Matrix.vecMul x (LinearMap.toMatrixRight' l) = l x := by
    intro x
    have := LinearMap.toMatrixRight'.symm_apply_apply l
    conv_rhs => rw [← this]
    rfl
  have h2 : Matrix.vecMul (Pi.single i 1) (N * LinearMap.toMatrixRight' l) = Pi.single i 1 := by
    rw [← Matrix.vecMul_vecMul, h1]
    exact LinearMap.congr_fun hl _
  have := congrFun h2 j
  rw [Matrix.single_one_vecMul] at this
  simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using this
end GlobalTheory
