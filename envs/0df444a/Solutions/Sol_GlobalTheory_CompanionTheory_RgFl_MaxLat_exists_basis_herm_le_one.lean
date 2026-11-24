-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgFl.MaxLat.exists_basis_herm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:08:29.547385+00:00
-- url     : https://prove2.me/submissions/738e45b6-5213-4f51-a6d1-43a9f31bd25e

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExistenceOfSandwichStatement

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgFl GlobalTheory.CompanionTheory.RgFl.MaxLat
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L]
  {V : Type} [AddCommGroup V] [Module L V]
namespace GlobalTheory.CompanionTheory.RgFl.MaxLat
theorem _root_.solution [FiniteDimensional L V] {s : L →+* L} {h : V → V → L}
    (hs : IsInv s) (hh : IsHerm s h) :
    ∃ (m : ℕ) (b : Module.Basis (Fin m) L V), ∀ i j, ‖h (b i) (b j)‖ ≤ 1 := by
  let e := Module.finBasis L V
  let K : ℝ := ∑ i, ∑ j, ‖h (e i) (e j)‖
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hKij : ∀ i j, ‖h (e i) (e j)‖ ≤ K := fun i j =>
    (Finset.single_le_sum (f := fun j => ‖h (e i) (e j)‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, ‖h (e i) (e j)‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))
  obtain ⟨t, ht0, ht⟩ := NormedField.exists_norm_lt L (show (0 : ℝ) < 1 / (K + 1) by positivity)
  have htK : ‖t‖ * (K + 1) ≤ 1 := by
    rw [lt_div_iff₀ (by positivity)] at ht
    exact ht.le
  have ht1 : ‖t‖ ≤ 1 := by nlinarith [norm_nonneg t]
  have htK' : ‖t‖ * K ≤ 1 := by nlinarith [norm_nonneg t]
  have tne : t ≠ 0 := norm_pos_iff.1 ht0
  have hu : ∀ i : Fin (Module.finrank L V), IsUnit ((fun _ => t) i : L) :=
    fun _ => isUnit_iff_ne_zero.2 tne
  refine ⟨_, e.isUnitSMul hu, fun i j => ?_⟩
  simp only [Module.Basis.isUnitSMul_apply]
  have e1 : h (t • e i) (t • e j) = t * (s t * h (e i) (e j)) := by
    rw [hh.2.1, hh.2.2.1 (e j) (t • e i), hh.2.1, map_mul, ← hh.2.2.1 (e j) (e i)]
  rw [e1, norm_mul, norm_mul, hs.2.1]
  calc ‖t‖ * (‖t‖ * ‖h (e i) (e j)‖) ≤ 1 * (‖t‖ * K) := by
        gcongr
        exact hKij i j
    _ ≤ 1 := by linarith
end GlobalTheory.CompanionTheory.RgFl.MaxLat
