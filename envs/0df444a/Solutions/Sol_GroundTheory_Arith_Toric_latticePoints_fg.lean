-- Prove2me | solution 1 for GroundTheory.Arith.Toric.latticePoints_fg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:40:57.194037+00:00
-- url     : https://prove2.me/submissions/9ad2eedd-58f4-480e-9f0c-957f3cd3107a

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ExistsDualNegOfNotMemHullFinset
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Lattice
import Theorems.Thm_GroundTheory_Arith_Toric_mem_hull_image_finset_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Toric
open Module PointedCone TensorProduct
variable {N : Type*} [AddCommGroup N]
variable [Module.Free ℤ N] [Module.Finite ℤ N]
namespace GroundTheory.Arith.Toric
theorem _root_.solution {τ : PointedCone ℝ (Dual ℝ (ℝ ⊗[ℤ] N))}
    (hτ : IsRationalPolyhedral (toRealDual N) τ) : (latticePoints (toRealDual N) τ).FG := by
  classical
  obtain ⟨T, rfl⟩ := hτ
  let e := Module.Free.chooseBasis ℤ N
  let B : Module.Free.ChooseBasisIndex ℤ N → ℤ := fun j => ∑ t ∈ T, |t (e j)|
  let K : Set (Dual ℤ N) := {m | m ∈ latticePoints (toRealDual N) (hull ℝ (toRealDual N '' T)) ∧
    ∀ j, m (e j) ∈ Set.Icc (-B j) (B j)}
  have hKfin : K.Finite := by
    have hbig : ((fun m : Dual ℤ N => fun j => m (e j)) ⁻¹'
        Set.univ.pi (fun j => Set.Icc (-B j) (B j))).Finite :=
      (Set.Finite.pi (fun j => Set.finite_Icc _ _)).preimage
        (fun m _ m' _ h => e.ext fun j => congrFun h j)
    exact hbig.subset fun m hm => Set.mem_preimage.2 (Set.mem_univ_pi.2 fun j => hm.2 j)
  refine ⟨(hKfin.union T.finite_toSet).toFinset, ?_⟩
  rw [Set.Finite.coe_toFinset]
  apply le_antisymm
  · rw [AddSubmonoid.closure_le]
    rintro m (hm | hm)
    · exact hm.1
    · exact subset_hull ⟨m, hm, rfl⟩
  · intro m hm
    obtain ⟨c, hc, hcm⟩ := (mem_hull_image_finset_iff T (toRealDual N)).1 hm
    replace hcm : ∑ t ∈ T, c t • toRealDual N t = toRealDual N m := hcm
    set m' := m - ∑ t ∈ T, (⌊c t⌋₊) • t with hm'
    have him' : toRealDual N m' = ∑ t ∈ T, (c t - ⌊c t⌋₊) • toRealDual N t := by
      rw [hm', map_sub, map_sum, ← hcm, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ]
      exact (sub_smul _ _ _).symm
    have hm'K : m' ∈ K := by
      refine ⟨?_, fun j => ?_⟩
      · rw [mem_latticePoints, him']
        exact (mem_hull_image_finset_iff T (toRealDual N)).2
          ⟨fun t => c t - ⌊c t⌋₊, fun t => sub_nonneg.2 (Nat.floor_le (hc t)), rfl⟩
      · have hval : (m' (e j) : ℝ) = ∑ t ∈ T, (c t - ⌊c t⌋₊) * (t (e j) : ℝ) := by
          rw [← toRealDual_apply_toRealSpan, him']
          change Dual.eval ℝ (ℝ ⊗[ℤ] N) (toRealSpan N (e j))
            (∑ t ∈ T, (c t - ⌊c t⌋₊) • toRealDual N t) = _
          rw [map_sum]
          simp
        have hbound : |(m' (e j) : ℝ)| ≤ (B j : ℝ) := by
          rw [hval]
          simp only [B]
          push_cast
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t _ => ?_)
          rw [abs_mul]
          have h0 : 0 ≤ c t - ⌊c t⌋₊ := sub_nonneg.2 (Nat.floor_le (hc t))
          have h1 : c t - ⌊c t⌋₊ ≤ 1 := by linarith [Nat.lt_floor_add_one (c t)]
          rw [abs_of_nonneg h0]
          exact mul_le_of_le_one_left (abs_nonneg _) h1
        have h2 : |m' (e j)| ≤ B j := by exact_mod_cast hbound
        exact Set.mem_Icc.2 (abs_le.1 h2)
    have hmeq : m = m' + ∑ t ∈ T, (⌊c t⌋₊) • t := by rw [hm', sub_add_cancel]
    rw [hmeq]
    exact add_mem (AddSubmonoid.subset_closure (Or.inl hm'K))
      (AddSubmonoid.sum_mem _ fun t ht => AddSubmonoid.nsmul_mem _
        (AddSubmonoid.subset_closure (show t ∈ K ∪ (T : Set (Dual ℤ N)) from Or.inr ht)) _)
end GroundTheory.Arith.Toric
