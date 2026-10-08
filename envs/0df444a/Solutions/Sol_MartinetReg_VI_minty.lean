-- Prove2me | solution 1 for MartinetReg.VI.minty
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T13:34:31.174247+00:00
-- url     : https://prove2.me/submissions/49101bf2-8877-40ec-ba8d-df1eb1a0c015

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

set_option autoImplicit false
open MartinetReg.VI Filter Topology
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H → StrongDual ℝ H) (C : Set H) (hS : Standing T C) :
    solSet T C = {xbar | xbar ∈ C ∧ ∀ y ∈ C, 0 ≤ T y (y - xbar)} := by
  exact MartinetVICodex.minty T C hS



#print axioms solution
