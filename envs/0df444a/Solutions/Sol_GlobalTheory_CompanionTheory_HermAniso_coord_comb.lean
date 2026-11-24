-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermAniso.coord_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:38:10.021935+00:00
-- url     : https://prove2.me/submissions/d257cdcc-bd7f-4950-9ecb-75c67fec538c

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AnisotropicOfHenselAndSandwich

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HermAniso
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
  {s : L →+* L} {h : V → V → L}
namespace GlobalTheory.CompanionTheory.HermAniso
theorem _root_.solution [FiniteDimensional L V] (hh : IsHerm s h) {m : ℕ} (b : Module.Basis (Fin m) L V) :
    ∃ M : Fin m → Fin m → L, ∀ x i, b.repr x i = ∑ j, M i j * h (b j) x := by
  have h1 := hh.2.2.1
  let φ : V →ₗ[L] (Fin m → L) :=
    { toFun := fun x j => h (b j) x
      map_add' := fun x y => by ext j; simp [hh.1]
      map_smul' := fun a x => by ext j; simp [hh.2.1] }
  have hker : LinearMap.ker φ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    let ℓ : V →ₗ[L] L :=
      { toFun := fun y => h x y
        map_add' := fun y z => hh.1 x y z
        map_smul' := fun a y => by simp [hh.2.1] }
    have hl : ℓ = 0 := by
      refine b.ext fun j => ?_
      have : h (b j) x = 0 := congrFun hx j
      change h x (b j) = 0
      rw [h1 (b j) x, this, map_zero]
    exact hh.2.2.2 x fun y => LinearMap.congr_fun hl y
  obtain ⟨ψ, hψ⟩ := φ.exists_leftInverse_of_injective hker
  refine ⟨fun i j => ((b.coord i) ∘ₗ ψ) (fun k => if j = k then 1 else 0), fun x i => ?_⟩
  have e : ψ (φ x) = x := LinearMap.congr_fun hψ x
  have := LinearMap.pi_apply_eq_sum_univ ((b.coord i) ∘ₗ ψ) (φ x)
  simp only [LinearMap.comp_apply, Module.Basis.coord_apply, smul_eq_mul, e] at this
  rw [this]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]
  rfl
end GlobalTheory.CompanionTheory.HermAniso
