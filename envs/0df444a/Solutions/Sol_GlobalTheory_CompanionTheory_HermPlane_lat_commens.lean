-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermPlane.lat_commens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:38:08.102579+00:00
-- url     : https://prove2.me/submissions/bd1d9dd0-88e8-4398-9665-2415988f5044

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_PlaneOfHenselAndPairing

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HermPlane
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {V : Type} [AddCommGroup V] [Module L V]
namespace GlobalTheory.CompanionTheory.HermPlane
theorem _root_.solution {Λ M : AddSubgroup V} (hΛ : IsLat L Λ) (hM : IsLat L M) {p : L} (hp0 : p ≠ 0)
    (hp1 : ‖p‖ < 1) : ∃ r : ℕ, ∀ x ∈ M, p ^ r • x ∈ Λ := by
  obtain ⟨m, b, hb⟩ := hΛ
  obtain ⟨m', b', hb'⟩ := hM
  set C : ℝ := ∑ i, ∑ j, ‖b.repr (b' j) i‖ + 1 with hC
  have hC0 : 0 < C := by
    have : 0 ≤ ∑ i, ∑ j, ‖b.repr (b' j) i‖ :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith
  obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hC0) hp1
  refine ⟨r, fun x hx => ?_⟩
  rw [hb]
  intro i
  have hx' := (hb' x).1 hx
  have hexp : b.coord i x = ∑ j, b'.repr x j * b.coord i (b' j) := by
    conv_lhs => rw [← b'.sum_repr x]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
  have hbound : ‖b.repr x i‖ ≤ C := by
    have h1 : ‖b.repr x i‖ ≤ ∑ j, ‖b.repr (b' j) i‖ := by
      have : b.repr x i = ∑ j, b'.repr x j * b.repr (b' j) i := by simpa using hexp
      rw [this]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hx' j)
    have h2 : ∑ j, ‖b.repr (b' j) i‖ ≤ ∑ i, ∑ j, ‖b.repr (b' j) i‖ :=
      Finset.single_le_sum (f := fun i => ∑ j, ‖b.repr (b' j) i‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)
    linarith
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul, norm_pow]
  calc ‖p‖ ^ r * ‖b.repr x i‖ ≤ C⁻¹ * C :=
        mul_le_mul hr.le hbound (norm_nonneg _) (inv_pos.mpr hC0).le
    _ = 1 := inv_mul_cancel₀ hC0.ne'
end GlobalTheory.CompanionTheory.HermPlane
