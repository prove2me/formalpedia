-- Prove2me | solution 1 for LanglandsTunnell.Converse.DiscreteFamily.W_archWeightChar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/e84f02c3-4655-502e-9cdc-cc4be828054c

import Definitions.Def_LanglandsTunnell_Converse_ExplicitWhittakerFunctions
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_DiscreteFamily_W_archWeightChar

set_option autoImplicit false

open Complex

noncomputable section

namespace DiscreteRotation

open LanglandsTunnell.Converse.ArchR LanglandsTunnell.Converse.DiscreteFamily AutomorphicForm

local notation "M₂" => Matrix (Fin 2) (Fin 2) ℝ

section SO2

variable (r : M₂) (h10 : r 1 0 = -r 0 1) (h11 : r 1 1 = r 0 0) (hab : r 0 0 ^ 2 + r 0 1 ^ 2 = 1)

include h10 h11 in
private theorem mul_so2_apply (x : M₂) (i : Fin 2) :
    (x * r) i 0 = x i 0 * r 0 0 - x i 1 * r 0 1 ∧ (x * r) i 1 = x i 0 * r 0 1 + x i 1 * r 0 0 := by
  constructor
  · simp only [Matrix.mul_apply, Fin.sum_univ_two, h10]; ring
  · simp only [Matrix.mul_apply, Fin.sum_univ_two, h11]

include h10 h11 hab in
private theorem so2_det : r.det = 1 := by
  rw [Matrix.det_fin_two, h10, h11]; linear_combination hab

include h10 h11 hab in
private theorem nsq_mul_so2 (x : M₂) : nsq (x * r) = nsq x := by
  obtain ⟨e0, e1⟩ := mul_so2_apply r h10 h11 x 1
  unfold nsq; rw [e0, e1]
  linear_combination (x 1 0 ^ 2 + x 1 1 ^ 2) * hab

include h10 h11 hab in
private theorem det_mul_so2 (x : M₂) : (x * r).det = x.det := by
  rw [Matrix.det_mul, so2_det r h10 h11 hab, mul_one]

include h10 h11 hab in
private theorem iy_mul_so2 (x : M₂) : iy (x * r) = iy x := by
  unfold iy; rw [det_mul_so2 r h10 h11 hab, nsq_mul_so2 r h10 h11 hab]

include h10 h11 hab in
private theorem ix_mul_so2 (x : M₂) : ix (x * r) = ix x := by
  obtain ⟨a0, a1⟩ := mul_so2_apply r h10 h11 x 0
  obtain ⟨b0, b1⟩ := mul_so2_apply r h10 h11 x 1
  unfold ix; rw [nsq_mul_so2 r h10 h11 hab, a0, a1, b0, b1]
  congr 1
  linear_combination (x 0 0 * x 1 0 + x 0 1 * x 1 1) * hab

include h10 h11 hab in
private theorem detPow_mul_so2 (u₀ : ℂ) (x : M₂) : detPow u₀ (x * r) = detPow u₀ x := by
  unfold detPow; rw [det_mul_so2 r h10 h11 hab]

include h10 h11 hab in
private theorem kap_mul_so2 (x : M₂) : kap (x * r) = (⟨r 0 0, r 0 1⟩ : ℂ) * kap x := by
  obtain ⟨b0, b1⟩ := mul_so2_apply r h10 h11 x 1
  unfold kap; rw [nsq_mul_so2 r h10 h11 hab, b0, b1, mul_div_assoc']
  congr 1
  apply Complex.ext <;> simp <;> ring

include h10 h11 hab in

private theorem W_mul_so2 (u₀ : ℂ) (k₀ : ℕ) (x : M₂) :
    W u₀ k₀ (x * r) = (⟨r 0 0, r 0 1⟩ : ℂ) ^ (k₀ + 1) * W u₀ k₀ x := by
  unfold W
  rw [det_mul_so2 r h10 h11 hab]
  split_ifs with h
  · rw [ix_mul_so2 r h10 h11 hab, iy_mul_so2 r h10 h11 hab, nsq_mul_so2 r h10 h11 hab,
      detPow_mul_so2 r h10 h11 hab, kap_mul_so2 r h10 h11 hab, mul_pow]
    ring
  · simp

end SO2

private theorem archWeightCharℝ_val (n : ℤ) (r : rowIsometrySubgroup₀ ℝ) :
    ((archWeightCharℝ n r : ℂˣ) : ℂ) =
      (⟨((r : GL (Fin 2) ℝ) : M₂) 0 0, ((r : GL (Fin 2) ℝ) : M₂) 0 1⟩ : ℂ) ^ n := by
  simp only [archWeightCharℝ, MonoidHom.coe_comp, Function.comp_apply, zpowGroupHom_apply,
    Units.val_zpow_eq_zpow_val]
  rfl

private theorem archWeightCharℝ_natCast_succ (k₀ : ℕ) (r : rowIsometrySubgroup₀ ℝ) :
    ((archWeightCharℝ ((k₀ : ℤ) + 1) r : ℂˣ) : ℂ) =
      (⟨((r : GL (Fin 2) ℝ) : M₂) 0 0, ((r : GL (Fin 2) ℝ) : M₂) 0 1⟩ : ℂ) ^ (k₀ + 1) := by
  rw [archWeightCharℝ_val, show ((k₀ : ℤ) + 1) = ((k₀ + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]

end DiscreteRotation

end

open LanglandsTunnell LanglandsTunnell.RealArchParam LanglandsTunnell.Converse AutomorphicForm
open LanglandsTunnell.Converse.DiscreteFamily

theorem solution (u₀ : ℂ) (k₀ : ℕ) :
    ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      W u₀ k₀ ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ ((k₀ : ℤ) + 1) r : ℂ) * W u₀ k₀ (x : Matrix (Fin 2) (Fin 2) ℝ) := by
  intro r x
  obtain ⟨h10, h11, hab⟩ := entries_of_mem_rowIsometrySubgroup₀ r.2
  rw [Units.val_mul, DiscreteRotation.W_mul_so2 _ h10 h11 hab u₀ k₀, DiscreteRotation.archWeightCharℝ_natCast_succ]

end S_LanglandsTunnell_Converse_DiscreteFamily_W_archWeightChar
end P2MW
export P2MW.S_LanglandsTunnell_Converse_DiscreteFamily_W_archWeightChar (solution)
