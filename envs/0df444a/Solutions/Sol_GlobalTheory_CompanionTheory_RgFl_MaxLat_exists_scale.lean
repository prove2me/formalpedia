-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgFl.MaxLat.exists_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:08:30.613818+00:00
-- url     : https://prove2.me/submissions/4ae31db5-6217-4c5d-84fc-a68f8a748a34

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExistenceOfSandwichStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RgFl_MaxLat_herm_eq_sum

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
theorem _root_.solution {s : L →+* L} {h : V → V → L} (hh : IsHerm s h) (B : ℝ) (hB : 0 ≤ B)
    {m : ℕ} (b : Module.Basis (Fin m) L V) :
    ∃ c : L, c ≠ 0 ∧ ∀ x, (∀ j, ‖h (b j) x‖ ≤ B) → c • x ∈ ball b := by
  let T : V →ₗ[L] (Fin m → L) := LinearMap.pi fun j => hLin hh (b j)
  have hT : LinearMap.ker T = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun x hx => hh.2.2.2 x fun y => ?_
    have hj : ∀ j, h (b j) x = 0 := fun j => congrFun hx j
    rw [herm_eq_sum hh b]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [hh.2.2.1 (b j) x, hj j, map_zero, mul_zero]
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective T hT
  let w : Fin m → V := fun k => g fun j => if k = j then 1 else 0
  have hx : ∀ x, x = ∑ k, h (b k) x • w k := fun x => by
    have h1 : g (T x) = x := by simpa using LinearMap.congr_fun hg x
    have h2 := LinearMap.pi_apply_eq_sum_univ g (T x)
    rw [h1] at h2
    exact h2
  let C : ℝ := ∑ k, ∑ i, ‖b.repr (w k) i‖
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hCki : ∀ k i, ‖b.repr (w k) i‖ ≤ C := fun k i =>
    (Finset.single_le_sum (f := fun i => ‖b.repr (w k) i‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ i)).trans
      (Finset.single_le_sum (f := fun k => ∑ i, ‖b.repr (w k) i‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ k))
  obtain ⟨c, hc0, hc⟩ :=
    NormedField.exists_norm_lt L (show (0 : ℝ) < 1 / (B * C + 1) by positivity)
  have hcK : ‖c‖ * (B * C + 1) ≤ 1 := by
    rw [lt_div_iff₀ (by positivity)] at hc
    exact hc.le
  refine ⟨c, norm_pos_iff.1 hc0, fun x hxB i => ?_⟩
  have hr : b.repr x i = ∑ k, h (b k) x * b.repr (w k) i := by
    conv_lhs => rw [hx x]
    simp [map_sum, Finsupp.finset_sum_apply]
  have hbound : ‖b.repr x i‖ ≤ B * C := by
    rw [hr]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun k _ => ?_
    rw [norm_mul]
    exact mul_le_mul (hxB k) (hCki k i) (norm_nonneg _) hB
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul]
  nlinarith [norm_nonneg c, norm_nonneg (b.repr x i)]
end GlobalTheory.CompanionTheory.RgFl.MaxLat
