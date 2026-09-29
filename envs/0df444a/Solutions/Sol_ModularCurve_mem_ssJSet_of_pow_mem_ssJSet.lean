-- Prove2me | solution 1 for ModularCurve.mem_ssJSet_of_pow_mem_ssJSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/512f7d59-d947-5fee-b90b-f67f1fd1bdf3

import Mathlib
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_mem_ssJSet_of_pow_mem_ssJSet

set_option autoImplicit false

open ModularCurve

namespace SSFROBJ_body

open WeierstrassCurve

variable {K : Type*} [Field K] [DecidableEq K]

noncomputable def pointMap {L : Type*} [Field L] [DecidableEq L] (W : WeierstrassCurve K)
    (f : K →+* L) : W.toAffine.Point →+ (W.map f).toAffine.Point where
  toFun P := match P with
    | 0 => 0
    | .some (x := x) (y := y) h => .some (x := f x) (y := f y)
        ((Affine.map_nonsingular W.toAffine f.injective x y).mpr h)
  map_zero' := rfl
  map_add' := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals rfl
    by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
    · rw [Affine.Point.add_of_Y_eq hxy.left hxy.right,
        Affine.Point.add_of_Y_eq (congr_arg _ hxy.left) (by rw [hxy.right, Affine.map_negY])]
    · have hxy' : ¬ (f x₁ = f x₂ ∧ f y₁ = (W.map f).toAffine.negY (f x₂) (f y₂)) := by
        intro h
        exact hxy ⟨f.injective h.1, f.injective (by rw [← Affine.map_negY]; exact h.2)⟩
      rw [Affine.Point.add_some hxy, Affine.Point.add_some hxy']
      simp only [Affine.map_addX, Affine.map_addY, Affine.map_slope]

theorem pointMap_injective {L : Type*} [Field L] [DecidableEq L] (W : WeierstrassCurve K)
    (f : K →+* L) : Function.Injective (pointMap W f) := by
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h
  · rfl
  · exact absurd h (by simp [pointMap])
  · exact absurd h (by simp [pointMap])
  · simp only [pointMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Affine.Point.some.injEq] at h
    simp only [Affine.Point.some.injEq]
    exact ⟨f.injective h.1, f.injective h.2⟩

end SSFROBJ_body

theorem solution
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [DecidableEq K] [CharP K p]
    (e : ℕ) (j : K) (h : j ^ (p ^ e) ∈ ssJSet p K) : j ∈ ssJSet p K := by
  classical
  haveI : ExpChar K p := ExpChar.prime (Fact.out)
  intro W _ hWj P hP
  set f : K →+* K := iterateFrobenius K p e
  have hj' : (W.map f).j = j ^ (p ^ e) := by
    rw [WeierstrassCurve.map_j, hWj]; rfl
  have hinj := SSFROBJ_body.pointMap_injective W f
  have h0 : SSFROBJ_body.pointMap W f P = 0 := by
    refine h (W.map f) hj' _ ?_
    rw [← map_nsmul, hP, map_zero]
  exact hinj (by rw [h0, map_zero])

end S_ModularCurve_mem_ssJSet_of_pow_mem_ssJSet
end P2MW
export P2MW.S_ModularCurve_mem_ssJSet_of_pow_mem_ssJSet (solution)
