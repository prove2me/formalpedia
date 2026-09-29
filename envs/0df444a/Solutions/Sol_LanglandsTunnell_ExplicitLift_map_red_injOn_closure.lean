-- Prove2me | solution 1 for LanglandsTunnell.ExplicitLift.map_red_injOn_closure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/bf4afce5-a77c-5fcb-a621-be6985f0e3ec

import Definitions.Def_LanglandsTunnell_ExplicitLift
import Mathlib.Algebra.Group.Submonoid.Membership
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_ExplicitLift_map_red_injOn_closure

set_option autoImplicit false

namespace LanglandsTunnell
namespace P0

open FLT.ExplicitLift Matrix

abbrev Mat : Type := Matrix (Fin 2) (Fin 2) (ℤ√(-2))

def K48 : List Mat := [
  !![⟨1, 0⟩, ⟨0, 0⟩; ⟨0, 0⟩, ⟨1, 0⟩],
  !![⟨-1, 0⟩, ⟨1, 0⟩; ⟨-1, 0⟩, ⟨0, 0⟩],
  !![⟨1, 0⟩, ⟨-1, 0⟩; ⟨0, -1⟩, ⟨-1, 1⟩],
  !![⟨0, 0⟩, ⟨-1, 0⟩; ⟨1, 0⟩, ⟨-1, 0⟩],
  !![⟨-1, -1⟩, ⟨0, 1⟩; ⟨-1, 0⟩, ⟨1, 0⟩],
  !![⟨0, 0⟩, ⟨1, 0⟩; ⟨1, 0⟩, ⟨0, -1⟩],
  !![⟨1, 1⟩, ⟨0, -1⟩; ⟨2, 0⟩, ⟨-1, -1⟩],
  !![⟨0, 1⟩, ⟨1, -1⟩; ⟨1, 1⟩, ⟨0, -1⟩],
  !![⟨1, 0⟩, ⟨-1, -1⟩; ⟨0, 0⟩, ⟨-1, 0⟩],
  !![⟨1, -1⟩, ⟨-1, 0⟩; ⟨-1, -1⟩, ⟨0, 1⟩],
  !![⟨-1, 0⟩, ⟨0, 0⟩; ⟨-1, 1⟩, ⟨1, 0⟩],
  !![⟨0, -1⟩, ⟨-1, 1⟩; ⟨-1, 0⟩, ⟨1, 1⟩],
  !![⟨-1, 0⟩, ⟨1, 1⟩; ⟨-1, 1⟩, ⟨2, 0⟩],
  !![⟨-1, 1⟩, ⟨1, 0⟩; ⟨0, 1⟩, ⟨1, 0⟩],
  !![⟨-1, 0⟩, ⟨0, 1⟩; ⟨-1, 0⟩, ⟨1, 1⟩],
  !![⟨-2, 0⟩, ⟨1, 1⟩; ⟨-1, 1⟩, ⟨1, 0⟩],
  !![⟨0, 1⟩, ⟨1, 0⟩; ⟨1, 0⟩, ⟨0, 0⟩],
  !![⟨-1, 1⟩, ⟨2, 0⟩; ⟨0, 1⟩, ⟨1, -1⟩],
  !![⟨0, 1⟩, ⟨1, -1⟩; ⟨1, 0⟩, ⟨-1, -1⟩],
  !![⟨1, 0⟩, ⟨0, 0⟩; ⟨1, -1⟩, ⟨-1, 0⟩],
  !![⟨1, 0⟩, ⟨0, -1⟩; ⟨0, -1⟩, ⟨-1, 0⟩],
  !![⟨2, 0⟩, ⟨-1, -1⟩; ⟨1, -1⟩, ⟨-2, 0⟩],
  !![⟨0, -1⟩, ⟨-1, 0⟩; ⟨-1, -1⟩, ⟨-1, 1⟩],
  !![⟨1, -1⟩, ⟨-2, 0⟩; ⟨-1, -1⟩, ⟨-1, 1⟩],
  !![⟨0, -1⟩, ⟨-1, 1⟩; ⟨-1, -1⟩, ⟨0, 1⟩],
  !![⟨-1, 0⟩, ⟨0, 0⟩; ⟨0, 0⟩, ⟨-1, 0⟩],
  !![⟨1, -1⟩, ⟨-1, 0⟩; ⟨0, -1⟩, ⟨-1, 0⟩],
  !![⟨1, 0⟩, ⟨-1, -1⟩; ⟨1, -1⟩, ⟨-2, 0⟩],
  !![⟨1, -1⟩, ⟨-2, 0⟩; ⟨0, -1⟩, ⟨-1, 1⟩],
  !![⟨0, -1⟩, ⟨-1, 0⟩; ⟨-1, 0⟩, ⟨0, 0⟩],
  !![⟨-1, -1⟩, ⟨-1, 1⟩; ⟨-1, 0⟩, ⟨0, 1⟩],
  !![⟨-1, -1⟩, ⟨-1, 1⟩; ⟨-2, 0⟩, ⟨1, 1⟩],
  !![⟨-1, 0⟩, ⟨0, 1⟩; ⟨0, 1⟩, ⟨1, 0⟩],
  !![⟨-2, 0⟩, ⟨1, 1⟩; ⟨-1, 1⟩, ⟨2, 0⟩],
  !![⟨-1, 0⟩, ⟨1, 0⟩; ⟨0, 1⟩, ⟨1, -1⟩],
  !![⟨-1, 1⟩, ⟨1, 0⟩; ⟨1, 1⟩, ⟨0, -1⟩],
  !![⟨-1, 0⟩, ⟨1, 1⟩; ⟨0, 0⟩, ⟨1, 0⟩],
  !![⟨-1, 1⟩, ⟨2, 0⟩; ⟨1, 1⟩, ⟨1, -1⟩],
  !![⟨0, 1⟩, ⟨1, 0⟩; ⟨1, 1⟩, ⟨1, -1⟩],
  !![⟨1, 1⟩, ⟨1, -1⟩; ⟨2, 0⟩, ⟨-1, -1⟩],
  !![⟨1, 1⟩, ⟨1, -1⟩; ⟨1, 0⟩, ⟨0, -1⟩],
  !![⟨1, 0⟩, ⟨0, -1⟩; ⟨1, 0⟩, ⟨-1, -1⟩],
  !![⟨2, 0⟩, ⟨-1, -1⟩; ⟨1, -1⟩, ⟨-1, 0⟩],
  !![⟨1, 0⟩, ⟨-1, 0⟩; ⟨1, 0⟩, ⟨0, 0⟩],
  !![⟨1, 1⟩, ⟨0, -1⟩; ⟨1, 0⟩, ⟨-1, 0⟩],
  !![⟨0, 0⟩, ⟨-1, 0⟩; ⟨-1, 0⟩, ⟨0, 1⟩],
  !![⟨-1, -1⟩, ⟨0, 1⟩; ⟨-2, 0⟩, ⟨1, 1⟩],
  !![⟨0, 0⟩, ⟨1, 0⟩; ⟨-1, 0⟩, ⟨1, 0⟩]
]

def W48 : List (List (Fin 2)) := [
  [],
  [0],
  [1],
  [0, 0],
  [0, 1],
  [1, 0],
  [1, 1],
  [0, 0, 1],
  [0, 1, 0],
  [0, 1, 1],
  [1, 0, 0],
  [1, 0, 1],
  [1, 1, 0],
  [1, 1, 1],
  [0, 0, 1, 0],
  [0, 0, 1, 1],
  [0, 1, 0, 0],
  [0, 1, 0, 1],
  [0, 1, 1, 0],
  [0, 1, 1, 1],
  [1, 0, 1, 0],
  [1, 0, 1, 1],
  [1, 1, 0, 0],
  [1, 1, 0, 1],
  [1, 1, 1, 0],
  [1, 1, 1, 1],
  [0, 0, 1, 0, 0],
  [0, 0, 1, 0, 1],
  [0, 0, 1, 1, 0],
  [0, 0, 1, 1, 1],
  [0, 1, 0, 1, 0],
  [0, 1, 0, 1, 1],
  [0, 1, 1, 0, 0],
  [0, 1, 1, 0, 1],
  [0, 1, 1, 1, 0],
  [1, 0, 1, 0, 0],
  [1, 0, 1, 0, 1],
  [1, 0, 1, 1, 0],
  [1, 0, 1, 1, 1],
  [1, 1, 0, 1, 0],
  [1, 1, 0, 1, 1],
  [1, 1, 1, 0, 0],
  [1, 1, 1, 0, 1],
  [1, 1, 1, 1, 0],
  [0, 0, 1, 1, 1, 0],
  [0, 1, 1, 1, 0, 0],
  [1, 0, 1, 1, 1, 0],
  [1, 1, 1, 1, 0, 0]
]

def evalWord : List (Fin 2) → Mat
  | [] => 1
  | 0 :: w => Slift * evalWord w
  | 1 :: w => Tlift * evalWord w

theorem K48_eq_map_evalWord : K48 = W48.map evalWord := by decide

theorem length_K48 : K48.length = 48 := by decide

theorem nodup_K48 : K48.Nodup := by decide

theorem one_mem_K48 : (1 : Mat) ∈ K48 := by decide

theorem Slift_mem_K48 : Slift ∈ K48 := by decide

theorem Tlift_mem_K48 : Tlift ∈ K48 := by decide

theorem Slift_mul_mem_K48 : ∀ k ∈ K48, Slift * k ∈ K48 := by decide

theorem Tlift_mul_mem_K48 : ∀ k ∈ K48, Tlift * k ∈ K48 := by decide

theorem evalWord_mem_closure (w : List (Fin 2)) :
    evalWord w ∈ Submonoid.closure ({Slift, Tlift} : Set Mat) := by
  induction w with
  | nil => exact Submonoid.one_mem _
  | cons a w ih =>
    match a with
    | 0 => exact Submonoid.mul_mem _ (Submonoid.subset_closure (by simp)) ih
    | 1 => exact Submonoid.mul_mem _ (Submonoid.subset_closure (by simp)) ih

theorem mem_closure_iff_mem_K48 (k : Mat) :
    k ∈ Submonoid.closure ({Slift, Tlift} : Set Mat) ↔ k ∈ K48 := by
  constructor
  · intro hk
    induction hk using Submonoid.closure_induction_left with
    | one => exact one_mem_K48
    | mul_left x hx y hy ih =>
      rcases hx with rfl | rfl
      · exact Slift_mul_mem_K48 y ih
      · exact Tlift_mul_mem_K48 y ih
  · intro hk
    have h := K48_eq_map_evalWord ▸ hk
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 h
    exact evalWord_mem_closure w

def redc (z : ℤ√(-2)) : ZMod 3 := ((z.re - z.im : ℤ) : ZMod 3)

theorem red_eq_redc (z : ℤ√(-2)) : red z = redc z := by
  rw [show z = ⟨z.re, z.im⟩ from rfl]
  simp [red, redc, Zsqrtd.lift, sub_eq_add_neg]

theorem map_red_eq_map_redc (m : Mat) : m.map red = m.map redc := by
  ext i j; simp [Matrix.map_apply, red_eq_redc]

theorem eq_one_of_mem_K48_of_map_redc_eq_one :
    ∀ k ∈ K48, k.map redc = 1 → k = 1 := by decide

theorem mem_map_redc_K48_of_det_ne_zero :
    ∀ m : Matrix (Fin 2) (Fin 2) (ZMod 3), m.det ≠ 0 → m ∈ K48.map (·.map redc) := by decide

theorem K48_map_redc_injective : ∀ M ∈ K48, ∀ N ∈ K48, M.map redc = N.map redc → M = N := by decide

end LanglandsTunnell.P0

open LanglandsTunnell.P0 in

theorem LanglandsTunnell.ExplicitLift.map_red_injOn_closure_impl :
    Set.InjOn (fun M : Matrix (Fin 2) (Fin 2) (ℤ√(-2)) => M.map FLT.ExplicitLift.red)
      (Submonoid.closure
        ({FLT.ExplicitLift.Slift, FLT.ExplicitLift.Tlift} : Set (Matrix (Fin 2) (Fin 2) (ℤ√(-2))))) := by
  intro M hM N hN h
  have hMK : M ∈ K48 := (mem_closure_iff_mem_K48 M).1 hM
  have hNK : N ∈ K48 := (mem_closure_iff_mem_K48 N).1 hN
  refine K48_map_redc_injective M hMK N hNK ?_
  have h' : M.map FLT.ExplicitLift.red = N.map FLT.ExplicitLift.red := h
  rwa [map_red_eq_map_redc, map_red_eq_map_redc] at h'

#print axioms LanglandsTunnell.ExplicitLift.map_red_injOn_closure_impl

theorem solution :
    Set.InjOn (fun M : Matrix (Fin 2) (Fin 2) (ℤ√(-2)) => M.map FLT.ExplicitLift.red)
      (Submonoid.closure
        ({FLT.ExplicitLift.Slift, FLT.ExplicitLift.Tlift} : Set (Matrix (Fin 2) (Fin 2) (ℤ√(-2))))) := by
  exact LanglandsTunnell.ExplicitLift.map_red_injOn_closure_impl

end S_LanglandsTunnell_ExplicitLift_map_red_injOn_closure
end P2MW
export P2MW.S_LanglandsTunnell_ExplicitLift_map_red_injOn_closure (solution)
