-- Prove2me | solution 1 for MartinetReg.VI.eq7
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T13:35:32.455905+00:00
-- url     : https://prove2.me/submissions/5d8d96c1-2e0e-4b41-af16-33c273303c0e

import Definitions.Def_MartinetReg_VI_Setting
set_option autoImplicit false
section
set_option autoImplicit false
open Filter Topology
namespace MartinetVICodex
open MartinetReg.VI
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem minty_forward (T : H → StrongDual ℝ H) (C : Set H)
    (hmono : MonotoneOnSet T C) {z : H} (hz : z ∈ solSet T C) :
    z ∈ C ∧ ∀ y ∈ C, 0 ≤ T y (y-z) := by
  refine ⟨hz.1, fun y hy => ?_⟩
  have hm := hmono y hy z hz.1
  have hs := hz.2 y hy
  change 0 ≤ T y (y-z)-T z (y-z) at hm
  linarith

theorem minty_reverse (T : H → StrongDual ℝ H) (C : Set H)
    (hC : Convex ℝ C) (hhemi : HemicontinuousOn T C) {z : H}
    (hz : z ∈ C ∧ ∀ y ∈ C, 0 ≤ T y (y-z)) : z ∈ solSet T C := by
  refine ⟨hz.1, fun y hy => ?_⟩
  let a : ℕ → ℝ := fun n => 1/(n+1 : ℝ)
  have ha (n : ℕ) : 0 < a n ∧ a n ≤ 1 := by
    dsimp [a]; constructor
    · positivity
    · apply (div_le_iff₀ (by positivity : 0 < (n+1 : ℝ))).mpr
      linarith [Nat.cast_nonneg (α := ℝ) n]
  have hn (n : ℕ) : 0 ≤ T ((1-a n) • z+a n • y) (y-z) := by
    have hc : (1-a n) • z+a n • y ∈ C :=
      hC hz.1 hy (by linarith [(ha n).2]) (ha n).1.le (by ring)
    have hp := hz.2 _ hc
    have he : (1-a n) • z+a n • y-z = a n • (y-z) := by
      rw [smul_sub,sub_smul,one_smul]; abel
    rw [he,map_smul] at hp
    simp only [smul_eq_mul] at hp
    exact nonneg_of_mul_nonneg_right hp (ha n).1
  have hat : Tendsto a atTop (𝓝[Set.Icc (0 : ℝ) 1] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall ?_⟩
    intro n; exact ⟨(ha n).1.le,(ha n).2⟩
  have ht := (hhemi z hz.1 y hy (y-z) 0 (by simp)).tendsto.comp hat
  have ht' : Tendsto (fun n => T ((1-a n) • z+a n • y) (y-z)) atTop
      (𝓝 (T z (y-z))) := by simpa only [Function.comp_def, sub_zero, zero_smul, one_smul, add_zero] using ht
  exact (isClosed_Ici : IsClosed (Set.Ici (0 : ℝ))).mem_of_tendsto ht'
    (Eventually.of_forall hn)

theorem minty (T : H → StrongDual ℝ H) (C : Set H) (hS : Standing T C) :
    solSet T C = {z | z ∈ C ∧ ∀ y ∈ C, 0 ≤ T y (y-z)} := by
  ext z; exact ⟨minty_forward T C hS.mono, minty_reverse T C hS.convex hS.hemi⟩
end MartinetVICodex

end

section
set_option autoImplicit false
open Filter Topology
namespace MartinetVICodex
open MartinetReg.VI
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem iterates_mem (T : H → StrongDual ℝ H) (C : Set H) (x : ℕ → H)
    (hx : IsRegSeq T C x) (n : ℕ) : x n ∈ C := by
  cases n with
  | zero => exact hx.1
  | succ n => exact (hx.2 n).1

theorem step_energy (T : H → StrongDual ℝ H) (C : Set H)
    (hmono : MonotoneOnSet T C) {xn y z : H}
    (hy : IsRegStep T C xn y) (hz : z ∈ solSet T C) :
    ‖y-z‖^2 ≤ ‖xn-z‖^2-‖y-xn‖^2 := by
  have hm := (minty_forward T C hmono hz).2 y hy.1
  have hs := hy.2 z hz.1
  have hT : T y (z-y) = -T y (y-z) := by rw [← neg_sub y z,map_neg]
  have hi : inner ℝ (y-xn) (z-y) = -inner ℝ (y-xn) (y-z) := by
    rw [← neg_sub y z,inner_neg_right]
  rw [hT,hi] at hs
  have hinner : inner ℝ (y-xn) (y-z) ≤ 0 := by linarith
  have he : xn-z = (y-z)-(y-xn) := by abel
  have hn := norm_sub_sq_real (y-z) (y-xn)
  rw [← he] at hn
  have hc : inner ℝ (y-z) (y-xn) = inner ℝ (y-xn) (y-z) := real_inner_comm _ _
  rw [hc] at hn
  nlinarith

theorem eq7 (T : H → StrongDual ℝ H) (C : Set H) (hS : Standing T C)
    (x : ℕ → H) (hx : IsRegSeq T C x) (z : H) (hz : z ∈ solSet T C) (n : ℕ) :
    ‖x (n+1)-z‖^2 ≤ ‖x n-z‖^2-‖x (n+1)-x n‖^2 :=
  step_energy T C hS.mono (hx.2 n) hz
end MartinetVICodex

end

set_option autoImplicit false
open MartinetReg.VI Filter Topology
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H → StrongDual ℝ H) (C : Set H) (hS : Standing T C)
    (x : ℕ → H) (hx : IsRegSeq T C x) (xbar : H) (hxbar : xbar ∈ solSet T C) (n : ℕ) :
    ‖x (n + 1) - xbar‖ ^ 2 ≤ ‖x n - xbar‖ ^ 2 - ‖x (n + 1) - x n‖ ^ 2 := by
  exact MartinetVICodex.eq7 T C hS x hx xbar hxbar n



#print axioms solution
