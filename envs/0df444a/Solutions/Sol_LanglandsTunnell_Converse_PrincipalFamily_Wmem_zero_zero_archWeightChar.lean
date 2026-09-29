-- Prove2me | solution 1 for LanglandsTunnell.Converse.PrincipalFamily.Wmem_zero_zero_archWeightChar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/27ea0a14-683c-55b0-8d35-32bc096c6511

import Definitions.Def_LanglandsTunnell_Converse_ExplicitWhittakerFunctions
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_PrincipalFamily_Wmem_zero_zero_archWeightChar

set_option autoImplicit false

open Complex MeasureTheory AutomorphicForm

noncomputable section

namespace WhittakerRotation

open LanglandsTunnell.Converse.ArchR LanglandsTunnell.Converse.PrincipalFamily

local notation "M₂" => Matrix (Fin 2) (Fin 2) ℝ

private def innerGen (Φ : ℝ → ℝ → ℂ) (h : M₂) (t : ℝ) : ℂ :=
  ∫ x : ℝ, Φ (-(t * (h 0 0 + x * h 1 0))) (-(t * (h 0 1 + x * h 1 1))) * psi (-x)

private def Wgen (Φ : ℝ → ℝ → ℂ) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) (g : M₂) : ℂ :=
  ((|g.det| : ℝ) : ℂ) * quasiChar u₁ a₁ g.det * ∫ t : ℝ, innerGen Φ g t * quasiChar (u₁ - u₂) (a₁ + a₂) t

private def phiEven (v₀ v₁ : ℝ) : ℂ := phiStd 0 v₀ * phiStd 0 v₁

private theorem Wmem_zero_zero_eq_Wgen_phiEven (u₁ u₂ : ℂ) (g : M₂) :
    Wmem u₁ u₂ 0 0 g = Wgen phiEven u₁ u₂ 0 0 g := rfl

section SO2

variable (r : M₂) (h10 : r 1 0 = -r 0 1) (h11 : r 1 1 = r 0 0) (hab : r 0 0 ^ 2 + r 0 1 ^ 2 = 1)

include h10 h11 in
private theorem mul_so2_entries (g : M₂) :
    (g * r) 0 0 = g 0 0 * r 0 0 - g 0 1 * r 0 1 ∧ (g * r) 1 0 = g 1 0 * r 0 0 - g 1 1 * r 0 1 ∧
      (g * r) 0 1 = g 0 0 * r 0 1 + g 0 1 * r 0 0 ∧ (g * r) 1 1 = g 1 0 * r 0 1 + g 1 1 * r 0 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Matrix.mul_apply, Fin.sum_univ_two, h10, h11] <;> ring

include h10 h11 hab in
private theorem det_so2 : r.det = 1 := by
  rw [Matrix.det_fin_two, h10, h11]; linear_combination hab

include h10 h11 hab in
private theorem det_mul_so2 (g : M₂) : (g * r).det = g.det := by
  rw [Matrix.det_mul, det_so2 r h10 h11 hab, mul_one]

include h10 h11 in

private theorem innerGen_mul_so2 {Φ : ℝ → ℝ → ℂ} {lam : ℂ}
    (hΦ : ∀ v₀ v₁ : ℝ, Φ (r 0 0 * v₀ - r 0 1 * v₁) (r 0 1 * v₀ + r 0 0 * v₁) = lam * Φ v₀ v₁) (g : M₂) (t : ℝ) :
    innerGen Φ (g * r) t = lam * innerGen Φ g t := by
  unfold innerGen
  rw [← MeasureTheory.integral_const_mul]
  congr 1
  funext x
  obtain ⟨e00, e10, e01, e11⟩ := mul_so2_entries r h10 h11 g
  rw [e00, e10, e01, e11,
    show -(t * (g 0 0 * r 0 0 - g 0 1 * r 0 1 + x * (g 1 0 * r 0 0 - g 1 1 * r 0 1))) =
        r 0 0 * (-(t * (g 0 0 + x * g 1 0))) - r 0 1 * (-(t * (g 0 1 + x * g 1 1))) by ring,
    show -(t * (g 0 0 * r 0 1 + g 0 1 * r 0 0 + x * (g 1 0 * r 0 1 + g 1 1 * r 0 0))) =
        r 0 1 * (-(t * (g 0 0 + x * g 1 0))) + r 0 0 * (-(t * (g 0 1 + x * g 1 1))) by ring,
    hΦ, mul_assoc]

include h10 h11 hab in

private theorem Wgen_mul_so2 {Φ : ℝ → ℝ → ℂ} {lam : ℂ}
    (hΦ : ∀ v₀ v₁ : ℝ, Φ (r 0 0 * v₀ - r 0 1 * v₁) (r 0 1 * v₀ + r 0 0 * v₁) = lam * Φ v₀ v₁)
    (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) (g : M₂) :
    Wgen Φ u₁ u₂ a₁ a₂ (g * r) = lam * Wgen Φ u₁ u₂ a₁ a₂ g := by
  unfold Wgen
  rw [det_mul_so2 r h10 h11 hab]
  have hfun : (fun t => innerGen Φ (g * r) t * quasiChar (u₁ - u₂) (a₁ + a₂) t) =
      fun t => lam * (innerGen Φ g t * quasiChar (u₁ - u₂) (a₁ + a₂) t) := by
    funext t; rw [innerGen_mul_so2 r h10 h11 hΦ]; ring
  rw [hfun, MeasureTheory.integral_const_mul]; ring

include hab in

private theorem phiEven_so2 (v₀ v₁ : ℝ) :
    phiEven (r 0 0 * v₀ - r 0 1 * v₁) (r 0 1 * v₀ + r 0 0 * v₁) = 1 * phiEven v₀ v₁ := by
  simp only [phiEven, phiStd, if_true, one_mul]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Real.exp_add, ← Real.exp_add]
  congr 2
  linear_combination (-Real.pi) * (v₀ ^ 2 + v₁ ^ 2) * hab

include h10 h11 hab in

private theorem Wgen_phiEven_mul_so2 (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) (g : M₂) :
    Wgen phiEven u₁ u₂ a₁ a₂ (g * r) = Wgen phiEven u₁ u₂ a₁ a₂ g := by
  rw [Wgen_mul_so2 r h10 h11 hab (fun v₀ v₁ => phiEven_so2 r hab v₀ v₁), one_mul]

end SO2

private theorem archWeightCharℝ_coe_eq (n : ℤ) (r : rowIsometrySubgroup₀ ℝ) :
    ((archWeightCharℝ n r : ℂˣ) : ℂ) =
      (⟨((r : GL (Fin 2) ℝ) : M₂) 0 0, ((r : GL (Fin 2) ℝ) : M₂) 0 1⟩ : ℂ) ^ n := by
  simp only [archWeightCharℝ, MonoidHom.coe_comp, Function.comp_apply, zpowGroupHom_apply,
    Units.val_zpow_eq_zpow_val]
  rfl

private theorem Wgen_phiEven_weight (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ) :
    Wgen phiEven u₁ u₂ a₁ a₂ ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : M₂) =
      ((archWeightCharℝ 0 r : ℂˣ) : ℂ) * Wgen phiEven u₁ u₂ a₁ a₂ (x : M₂) := by
  obtain ⟨h10, h11, hab⟩ := entries_of_mem_rowIsometrySubgroup₀ r.2
  rw [Units.val_mul, Wgen_phiEven_mul_so2 _ h10 h11 hab, archWeightCharℝ_coe_eq, zpow_zero, one_mul]

private theorem Wmem_zero_zero_weight (u₁ u₂ : ℂ) (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ) :
    Wmem u₁ u₂ 0 0 ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : M₂) =
      ((archWeightCharℝ 0 r : ℂˣ) : ℂ) * Wmem u₁ u₂ 0 0 (x : M₂) :=
  Wgen_phiEven_weight u₁ u₂ 0 0 r x

end WhittakerRotation

end

open LanglandsTunnell LanglandsTunnell.RealArchParam LanglandsTunnell.Converse AutomorphicForm
open LanglandsTunnell.Converse.PrincipalFamily

theorem solution (u₁ u₂ : ℂ) :
    ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      Wmem u₁ u₂ 0 0 ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ (0 : ℤ) r : ℂ) * Wmem u₁ u₂ 0 0 (x : Matrix (Fin 2) (Fin 2) ℝ) := by
  intro r x
  rw [WhittakerRotation.Wmem_zero_zero_eq_Wgen_phiEven, WhittakerRotation.Wmem_zero_zero_eq_Wgen_phiEven]
  exact WhittakerRotation.Wgen_phiEven_weight u₁ u₂ 0 0 r x

end S_LanglandsTunnell_Converse_PrincipalFamily_Wmem_zero_zero_archWeightChar
end P2MW
export P2MW.S_LanglandsTunnell_Converse_PrincipalFamily_Wmem_zero_zero_archWeightChar (solution)
