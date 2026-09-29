-- Prove2me | solution 1 for LanglandsTunnell.Converse.ArchDatumR.W_eq_zero_of_det_neg_of_principal_of_ne_of_archWeightChar_one_of_isCasimirEigen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/d5cc8299-9962-598f-b32f-345de5c22a4f

import Mathlib
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_negSheet_ode_and_growth_and_mellin_eq_of_archWeightChar_of_isCasimirEigen
import Theorems.Thm_LanglandsTunnell_whittaker_ode_neg_weight_eq_zero_of_moderateGrowth_of_mellin_eq_GammaC_mul
import Theorems.Thm_LanglandsTunnell_Converse_ArchR_eq_mul_of_unip_law_of_central_law_of_archWeightChar_of_torus_eq_of_sign_det
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_ArchDatumR_W_eq_zero_of_det_neg_of_principal_of_ne_of_archWeightChar_one_of_isCasimirEigen

set_option autoImplicit false

noncomputable section

open Real Complex
open NumberField AutomorphicForm
p2m_open "LanglandsTunnell P2MW.S_LanglandsTunnell_Converse_ArchDatumR_W_eq_zero_of_det_neg_of_principal_of_ne_of_archWeightChar_one_of_isCasimirEigen.LanglandsTunnell LanglandsTunnell.RealArchParam LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_ArchDatumR_W_eq_zero_of_det_neg_of_principal_of_ne_of_archWeightChar_one_of_isCasimirEigen.LanglandsTunnell.Converse"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR RealArchParam signShift signShift_zero signShift_one RealArchParam.centralExponent RealArchParam.principal Converse.ArchDatumR.negSheet_ode_and_growth_and_mellin_eq_of_archWeightChar_of_isCasimirEigen whittaker_ode_neg_weight_eq_zero_of_moderateGrowth_of_mellin_eq_GammaC_mul Converse.ArchR.eq_mul_of_unip_law_of_central_law_of_archWeightChar_of_torus_eq_of_sign_det"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.quasiChar ArchR.centralChar ArchDatumR ArchCasimir.IsCasimirEigen ArchDatumR.negSheet_ode_and_growth_and_mellin_eq_of_archWeightChar_of_isCasimirEigen ArchR.eq_mul_of_unip_law_of_central_law_of_archWeightChar_of_torus_eq_of_sign_det"
namespace DZGlue1
p2m_open "LanglandsTunnell.Converse LanglandsTunnell"

variable {P : RealArchParam}

theorem centralChar_of_pos (t : ℝ) (ht : 0 < t) : ArchR.centralChar P t = (t : ℂ) ^ P.centralExponent := by
  rw [ArchR.centralChar, ArchR.quasiChar, abs_of_pos ht]
  split_ifs
  · rw [mul_one]
  · rw [sign_pos ht]; simp

theorem central_pos (D : ArchDatumR P) (t : ℝ) (x : Matrix (Fin 2) (Fin 2) ℝ) (ht : 0 < t) :
    D.W (t • x) = (t : ℂ) ^ (P.centralExponent + 1) * D.W x := by
  rw [D.central_law t x ht.ne', centralChar_of_pos t ht, abs_of_pos ht,
    cpow_add _ _ (ofReal_ne_zero.2 ht.ne'), cpow_one]

theorem W_eq_zero_of_ray (D : ArchDatumR P) (k : ℤ)
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ k r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (hray : ∀ y : ℝ, 0 < y → D.W !![-Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹] = 0)
    (x : Matrix (Fin 2) (Fin 2) ℝ) (hx : x.det < 0) : D.W x = 0 := by
  have h := LanglandsTunnell.Converse.ArchR.eq_mul_of_unip_law_of_central_law_of_archWeightChar_of_torus_eq_of_sign_det
    D.W (fun _ => 0) k (P.centralExponent + 1) 0
    (fun t x _ => D.unip_law t x) (fun t x _ => by simp)
    (fun t x ht _ => central_pos D t x ht) (fun t x _ _ => by simp)
    hDW (fun r x => by simp) (-1) (Or.inr rfl)
    (fun y hy => by rw [neg_one_mul, hray y hy]; simp) x (by nlinarith)
  simpa using h

end LanglandsTunnell.Converse.DZGlue1

open LanglandsTunnell.Converse.DZGlue1 in
theorem solution
    (u₀ : ℂ) (a₁ a₂ : ZMod 2) (ha : a₁ ≠ a₂) (D : ArchDatumR (RealArchParam.principal u₀ a₁ u₀ a₂))
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ 1 r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (hDE : ArchCasimir.IsCasimirEigen D)
    (x : Matrix (Fin 2) (Fin 2) ℝ) (hx : x.det < 0) :
    D.W x = 0 := by
  have hν : (RealArchParam.principal u₀ a₁ u₀ a₂).laplaceEigenvalue = 1 / 4 - (0 : ℂ) ^ 2 := by
    rw [laplaceEigenvalue_principal]; ring
  have hA : ∀ (a : ZMod 2) (s : ℂ), ((RealArchParam.principal u₀ a₁ u₀ a₂).twist 0 a).archFactor s =
      Complex.Gammaℂ (s + u₀) := by
    intro a s
    have ha2 : a₂ = a₁ + 1 := by
      fin_cases a₁ <;> fin_cases a₂ <;> first | exact absurd rfl ha | rfl
    have key := Complex.Gammaℝ_mul_Gammaℝ_add_one (s + u₀)
    have hb : ∀ b : ZMod 2,
        Complex.Gammaℝ (s + (u₀ + 0 + signShift b)) * Complex.Gammaℝ (s + (u₀ + 0 + signShift (b + 1))) =
          Complex.Gammaℂ (s + u₀) := by
      intro b
      obtain rfl | rfl : b = 0 ∨ b = 1 := by
        fin_cases b
        · exact Or.inl rfl
        · exact Or.inr rfl
      · simp only [zero_add, signShift_zero, signShift_one, add_zero]
        rw [← key]; ring_nf
      · have h11 : (1 : ZMod 2) + 1 = 0 := by decide
        simp only [h11, signShift_zero, signShift_one, add_zero]
        rw [← key, mul_comm]; ring_nf
    subst ha2
    show (Multiset.map (fun μ => Complex.Gammaℝ (s + μ))
        {u₀ + 0 + signShift (a₁ + a), u₀ + 0 + signShift (a₁ + 1 + a)}).prod *
      (Multiset.map (fun ν => Complex.Gammaℂ (s + ν)) 0).prod = Complex.Gammaℂ (s + u₀)
    rw [Multiset.map_zero, Multiset.prod_zero, mul_one, Multiset.insert_eq_cons, Multiset.map_cons,
      Multiset.prod_cons, Multiset.map_singleton, Multiset.prod_singleton,
      show a₁ + 1 + a = a₁ + a + 1 by ring]
    exact hb (a₁ + a)
  obtain ⟨⟨hf, hf', hode⟩, hgr, σ₀, Ψ, hΨ, hmel⟩ :=
    LanglandsTunnell.Converse.ArchDatumR.negSheet_ode_and_growth_and_mellin_eq_of_archWeightChar_of_isCasimirEigen
      (RealArchParam.principal u₀ a₁ u₀ a₂) D 1 hDW hDE 0 hν u₀ hA
  have hexp : ∀ s : ℂ, s + (u₀ - ((RealArchParam.principal u₀ a₁ u₀ a₂).centralExponent - 1) / 2) =
      s + 1 / 2 + (0 : ℂ) := by
    intro s; simp only [RealArchParam.centralExponent]; ring
  have hray : ∀ y : ℝ, 0 < y → D.W !![-Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹] = 0 := fun y hy =>
    LanglandsTunnell.whittaker_ode_neg_weight_eq_zero_of_moderateGrowth_of_mellin_eq_GammaC_mul
      0 0 (by simp) ((1 : ℤ) : ℝ) (by norm_num) _ hf hf' hode hgr σ₀ Ψ hΨ
      (fun s hs => by obtain ⟨h1, h2⟩ := hmel s hs; exact ⟨h1, by rw [h2, hexp]⟩) y hy
  exact W_eq_zero_of_ray D 1 hDW hray x hx

end

end S_LanglandsTunnell_Converse_ArchDatumR_W_eq_zero_of_det_neg_of_principal_of_ne_of_archWeightChar_one_of_isCasimirEigen
end P2MW
export P2MW.S_LanglandsTunnell_Converse_ArchDatumR_W_eq_zero_of_det_neg_of_principal_of_ne_of_archWeightChar_one_of_isCasimirEigen (solution)
