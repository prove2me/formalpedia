-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.CongUnit.exists_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:56:30.430212+00:00
-- url     : https://prove2.me/submissions/52e0038d-68b2-4660-8e10-f37daf062ca5

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CongruenceEndomorphismInverseExists
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_CongUnit_norm_one_add_of_lt

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
theorem _root_.solution {m : ℕ} (b : Module.Basis (Fin m) L V) {Λ : AddSubgroup V}
    (hb : ∀ x, x ∈ Λ ↔ ∀ i, ‖b.repr x i‖ ≤ 1) {π : L} (hπ : ‖π‖ < 1)
    {g : Module.End L V} (hg : g ∈ congJ Λ π) {x : V} (hx : x ≠ 0) :
    ∃ i, (∀ j, ‖b.repr x j‖ ≤ ‖b.repr x i‖) ∧ b.repr x i ≠ 0 ∧
      ‖b.repr ((1 + g) x) i‖ = ‖b.repr x i‖ := by
  have hne : ∃ j, b.repr x j ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hx
    have : b.repr x = 0 := by
      ext j
      simpa using hcon j
    simpa using this
  obtain ⟨j₀, hj₀⟩ := hne
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => ‖b.repr x j‖)
    ⟨j₀, Finset.mem_univ _⟩
  have hmax : ∀ j, ‖b.repr x j‖ ≤ ‖b.repr x i‖ := fun j => hi j (Finset.mem_univ _)
  have hc : b.repr x i ≠ 0 := by
    intro h0
    have := hmax j₀
    rw [h0, norm_zero] at this
    exact hj₀ (norm_le_zero_iff.mp this)
  refine ⟨i, hmax, hc, ?_⟩
  set c := b.repr x i with hcdef
  have hy : c⁻¹ • x ∈ Λ := by
    rw [hb]
    intro j
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul, norm_inv]
    exact inv_mul_le_one_of_le₀ (hmax j) (norm_nonneg _)
  obtain ⟨z, hz, hgz⟩ := hg _ hy
  have hzi : ‖b.repr z i‖ ≤ 1 := (hb z).1 hz i
  have hval : g x = c • π • z := by
    have h1 : g (c⁻¹ • x) = c⁻¹ • g x := map_smul g _ _
    rw [h1] at hgz
    rw [← hgz, smul_smul, mul_inv_cancel₀ hc, one_smul]
  have hGx : b.repr ((1 + g) x) i = c * (1 + π * b.repr z i) := by
    have : (1 + g) x = x + c • π • z := by
      rw [LinearMap.add_apply, Module.End.one_apply, hval]
    rw [this, map_add, map_smul, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
      Finsupp.smul_apply, smul_eq_mul, smul_eq_mul, ← hcdef]
    ring
  have ht : ‖π * b.repr z i‖ < 1 := by
    rw [norm_mul]
    calc ‖π‖ * ‖b.repr z i‖ ≤ ‖π‖ * 1 := by gcongr
      _ < 1 := by simpa using hπ
  rw [hGx, norm_mul, norm_one_add_of_lt ht, mul_one]
end GlobalTheory.CompanionTheory.Iwahori.CongUnit
