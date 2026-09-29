-- Prove2me | solution 1 for ModularCurve.natCard_componentGroup_eq_kirchhoffCount
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/bca8cc37-3d04-583a-92a2-6058308b4241

import Definitions.Def_ModularCurve_ComponentGroupKirchhoff
import Theorems.Thm_ModularCurve_natCard_componentGroup_eq_natAbs_det_diffChar
import Theorems.Thm_ModularCurve_gramMatrixOf_diffChar_marked_apply
import Theorems.Thm_Matrix_det_diagonal_add_const_int
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_natCard_componentGroup_eq_kirchhoffCount

open ModularCurve Module Finset

section Helpers
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommSemiring R]

theorem prod_subtype_ne (f : ι → R) (x₀ : ι) :
    ∏ i : {y : ι // y ≠ x₀}, f i.1 = ∏ y ∈ Finset.univ.erase x₀, f y :=
  (Finset.prod_subtype (Finset.univ.erase x₀) (fun x => by simp [Finset.mem_erase]) f).symm

theorem sum_subtype_ne (f : ι → R) (x₀ : ι) :
    ∑ i : {y : ι // y ≠ x₀}, f i.1 = ∑ y ∈ Finset.univ.erase x₀, f y :=
  (Finset.sum_subtype (Finset.univ.erase x₀) (fun x => by simp [Finset.mem_erase]) f).symm

theorem prod_erase_subtype_ne (f : ι → R) (x₀ : ι) (i : {y : ι // y ≠ x₀}) :
    ∏ j ∈ (Finset.univ : Finset {y : ι // y ≠ x₀}).erase i, f j.1 =
      ∏ y ∈ (Finset.univ.erase x₀).erase i.1, f y := by
  have h1 : ∏ j ∈ (Finset.univ : Finset {y : ι // y ≠ x₀}).erase i, f j.1 =
      ∏ j : {y : ι // y ≠ x₀}, (if j.1 = i.1 then 1 else f j.1) := by
    rw [← Finset.prod_erase Finset.univ
      (f := fun j : {y : ι // y ≠ x₀} => if j.1 = i.1 then 1 else f j.1) (a := i) (if_pos rfl)]
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [if_neg fun h => Finset.ne_of_mem_erase hj (Subtype.ext h)]
  have h2 := prod_subtype_ne (fun y => if y = i.1 then 1 else f y) x₀
  have h3 : ∏ y ∈ Finset.univ.erase x₀, (if y = i.1 then 1 else f y) =
      ∏ y ∈ (Finset.univ.erase x₀).erase i.1, f y := by
    rw [← Finset.prod_erase (Finset.univ.erase x₀)
      (f := fun y => if y = i.1 then 1 else f y) (a := i.1) (if_pos rfl)]
    exact Finset.prod_congr rfl fun y hy => if_neg (Finset.ne_of_mem_erase hy)
  rw [h1, h2, h3]

theorem sum_prod_erase_eq_marked (f : ι → R) (x₀ : ι) :
    ∑ x : ι, ∏ y ∈ Finset.univ.erase x, f y =
      (∏ i : {y : ι // y ≠ x₀}, f i.1) +
        f x₀ * ∑ i : {y : ι // y ≠ x₀},
          ∏ j ∈ (Finset.univ : Finset {y : ι // y ≠ x₀}).erase i, f j.1 := by
  rw [prod_subtype_ne f x₀]
  have hsum : ∑ i : {y : ι // y ≠ x₀},
      ∏ j ∈ (Finset.univ : Finset {y : ι // y ≠ x₀}).erase i, f j.1 =
      ∑ x ∈ Finset.univ.erase x₀, ∏ y ∈ (Finset.univ.erase x₀).erase x, f y := by
    rw [← sum_subtype_ne (fun x => ∏ y ∈ (Finset.univ.erase x₀).erase x, f y) x₀]
    exact Finset.sum_congr rfl fun i _ => prod_erase_subtype_ne f x₀ i
  rw [hsum, ← Finset.add_sum_erase Finset.univ
    (fun x => ∏ y ∈ Finset.univ.erase x, f y) (Finset.mem_univ x₀)]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx₀ : x₀ ∈ Finset.univ.erase x :=
    Finset.mem_erase.mpr ⟨(Finset.ne_of_mem_erase hx).symm, Finset.mem_univ x₀⟩
  rw [← Finset.mul_prod_erase (Finset.univ.erase x) f hx₀, Finset.erase_right_comm]

variable {e : ι → ℕ}

theorem det_gramMatrixOf_diffChar_marked (he : ∀ x, 0 < e x) (x₀ : ι) :
    (gramMatrixOf e (diffChar (Equiv.optionSubtypeNe x₀))).det = (kirchhoffCount e : ℤ) := by
  have hmat : gramMatrixOf e (diffChar (Equiv.optionSubtypeNe x₀)) =
      Matrix.of fun (y z : {b : ι // b ≠ x₀}) =>
        (if y = z then ((e y.1 : ℤ)) else 0) + (e x₀ : ℤ) := by
    ext y z
    rw [ModularCurve.gramMatrixOf_diffChar_marked_apply]
    rfl
  rw [hmat, Matrix.det_diagonal_add_const_int (fun y : {b : ι // b ≠ x₀} => (e y.1 : ℤ)) (e x₀ : ℤ)
    (fun y => Int.natCast_ne_zero.mpr (he y.1).ne')]
  have hcast : ((kirchhoffCount e : ℕ) : ℤ) =
      ∑ x : ι, ∏ y ∈ Finset.univ.erase x, ((e y : ℤ)) := by
    rw [kirchhoffCount_def]; push_cast; rfl
  rw [hcast, sum_prod_erase_eq_marked (fun y => (e y : ℤ)) x₀]

end Helpers

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {e : ι → ℕ}
    [Nonempty ι] (he : ∀ x, 0 < e x) :
    Nat.card (ModularCurve.componentGroup e) = ModularCurve.kirchhoffCount e := by
  obtain ⟨x₀⟩ := ‹Nonempty ι›
  rw [ModularCurve.natCard_componentGroup_eq_natAbs_det_diffChar he (Equiv.optionSubtypeNe x₀),
    det_gramMatrixOf_diffChar_marked he x₀, Int.natAbs_natCast]

end S_ModularCurve_natCard_componentGroup_eq_kirchhoffCount
end P2MW
export P2MW.S_ModularCurve_natCard_componentGroup_eq_kirchhoffCount (solution)
