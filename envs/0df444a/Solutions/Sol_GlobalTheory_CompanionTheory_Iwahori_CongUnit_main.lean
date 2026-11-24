-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.CongUnit.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:30:54.223087+00:00
-- url     : https://prove2.me/submissions/165312e5-d53f-4946-a326-6c3eca4b611e

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CongruenceEndomorphismInverseExists
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_CongUnit_eq_zero_of_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_CongUnit_mem_of_apply_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Iwahori GlobalTheory.CompanionTheory.Iwahori.CongUnit
variable {L V : Type} [NontriviallyNormedField L] [IsUltrametricDist L] [AddCommGroup V]
  [Module L V]
namespace GlobalTheory.CompanionTheory.Iwahori.CongUnit
theorem _root_.solution : ∀ {L V : Type} [NontriviallyNormedField L] [IsUltrametricDist L] [AddCommGroup V]
    [Module L V] [FiniteDimensional L V] (Λ : AddSubgroup V), IsLat L Λ → ∀ π : L, ‖π‖ < 1 →
    ∀ g ∈ GlobalTheory.CompanionTheory.Iwahori.congJ Λ π, ∃ g' ∈ GlobalTheory.CompanionTheory.Iwahori.congJ Λ π,
      (1 + g) * (1 + g') = 1 ∧ (1 + g') * (1 + g) = 1 := by
  intro L V _ _ _ _ _ Λ hΛ π hπ g hg
  obtain ⟨m, b, hb⟩ := hΛ
  have hker : LinearMap.ker (1 + g) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    exact eq_zero_of_apply b hb hπ hg hx
  obtain ⟨u, hu⟩ := (LinearMap.isUnit_iff_ker_eq_bot (1 + g)).2 hker
  have hGH : (1 + g) * (↑u⁻¹ : Module.End L V) = 1 := by rw [← hu]; exact u.mul_inv
  have hHG : (↑u⁻¹ : Module.End L V) * (1 + g) = 1 := by rw [← hu]; exact u.inv_mul
  set H : Module.End L V := ↑u⁻¹ with hH
  have hGHx : ∀ x, (1 + g) (H x) = x := fun x => by
    have := congrArg (fun f : Module.End L V => f x) hGH
    simpa only [Module.End.mul_apply, Module.End.one_apply] using this
  have hHGx : ∀ x, H ((1 + g) x) = x := fun x => by
    have := congrArg (fun f : Module.End L V => f x) hHG
    simpa only [Module.End.mul_apply, Module.End.one_apply] using this
  have hHmem : ∀ x ∈ Λ, H x ∈ Λ := fun x hx =>
    mem_of_apply_mem b hb hπ hg (by rw [hGHx]; exact hx)
  refine ⟨H - 1, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, hgy⟩ := hg x hx
    refine ⟨-H y, Λ.neg_mem (hHmem y hy), ?_⟩
    have h1 : H x + H (g x) = x := by
      have := hHGx x
      rwa [LinearMap.add_apply, Module.End.one_apply, map_add] at this
    have h2 : (H - 1) x = H x - x := by
      rw [LinearMap.sub_apply, Module.End.one_apply]
    rw [h2, smul_neg, ← map_smul, ← hgy]
    rw [eq_neg_iff_add_eq_zero, sub_add_eq_add_sub, h1, sub_self]
  · rw [add_sub_cancel]; exact hGH
  · rw [add_sub_cancel]; exact hHG
end GlobalTheory.CompanionTheory.Iwahori.CongUnit
