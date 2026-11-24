-- Prove2me | solution 1 for GlobalTheory.hermitian_adjoint_exists_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:59:13.659631+00:00
-- url     : https://prove2.me/submissions/f54e731a-68f5-44ef-9401-d50a85aeac91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HermitianAdjointExistsUniqueOfPosDef

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexConjugate
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (A C : Type) [AddCommGroup A] [Module ℂ A] [AddCommGroup C] [Module ℂ C] [FiniteDimensional ℂ C]
      (ipA : A →ₗ[ℂ] A →ₗ⋆[ℂ] ℂ) (ip : C →ₗ[ℂ] C →ₗ⋆[ℂ] ℂ),
      (∀ x y, ip x y = conj (ip y x)) → (∀ x, x ≠ 0 → 0 < (ip x x).re) →
      ∀ (io : C →ₗ[ℂ] A) (u : A), ∃! x : C, ∀ y, ip y x = ipA (io y) u := by
  intro A C _ _ _ _ _ ipA ip _hsym hpos io u

  let g : C →ₗ[ℝ] (C →ₗ[ℂ] ℂ) :=
    { toFun := fun x => ip.flip x
      map_add' := fun x y => by simp
      map_smul' := fun r x => by
        ext y
        have h1 : (r • x : C) = (r : ℂ) • x := rfl
        have h2 : (r • ip.flip x : C →ₗ[ℂ] ℂ) y = (r : ℂ) * ip y x := by
          show ((r : ℂ) • ip.flip x) y = _
          simp
        simp only [RingHom.id_apply]
        rw [h2, h1, LinearMap.map_smulₛₗ]
        simp [Complex.conj_ofReal] }
  have hg : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hne
    have h0 : ip x x = 0 := by
      have := LinearMap.congr_fun hx x
      simpa [g] using this
    have := hpos x hne
    rw [h0] at this
    simp at this
  have hrank : Module.finrank ℝ C = Module.finrank ℝ (C →ₗ[ℂ] ℂ) := by
    rw [finrank_real_of_complex, finrank_real_of_complex, Module.finrank_linearMap, Module.finrank_self, mul_one]
  have hs : Function.Surjective g := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hg
  obtain ⟨x, hx⟩ := hs ((ipA.flip u).comp io)
  refine ⟨x, fun y => ?_, fun x' hx' => ?_⟩
  · have := LinearMap.congr_fun hx y
    simpa [g] using this
  · apply hg
    ext y
    have hy := LinearMap.congr_fun hx y
    simp only [g, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.flip_apply] at hy ⊢
    rw [hx' y, hy]
    rfl
end GlobalTheory
