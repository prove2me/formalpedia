-- Prove2me | solution 1 for LanglandsTunnell.Converse.exists_archDatumR_archWeightChar_minimalType_isCasimirEigen_W_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/187555e4-7574-5e4a-ad72-a5fb60fc2509

import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_LanglandsTunnell_Converse_ExplicitWhittakerFunctions
import Theorems.Thm_LanglandsTunnell_Converse_PrincipalFamily_exists_archDatumR_W_eq
import Theorems.Thm_LanglandsTunnell_Converse_DiscreteFamily_exists_archDatumR_W_eq
import Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_exists_lincomb
import Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_exists_sgnTwist
import Theorems.Thm_LanglandsTunnell_Converse_PrincipalFamily_Wmem_zero_zero_archWeightChar
import Theorems.Thm_LanglandsTunnell_Converse_PrincipalFamily_oddComb_archWeightChar
import Theorems.Thm_LanglandsTunnell_Converse_DiscreteFamily_W_archWeightChar
import Theorems.Thm_LanglandsTunnell_Converse_PrincipalFamily_isCasimirEigen_of_W_eq_comb
import Theorems.Thm_LanglandsTunnell_Converse_DiscreteFamily_matrixCasimir_W
import Theorems.Thm_LanglandsTunnell_Converse_PrincipalFamily_exists_Wmem_ne_zero
import Theorems.Thm_LanglandsTunnell_Converse_PrincipalFamily_exists_oddComb_ne_zero
import Theorems.Thm_LanglandsTunnell_Converse_DiscreteFamily_exists_W_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_exists_archDatumR_archWeightChar_minimalType_isCasimirEigen_W_ne_zero
p2m_attr_erase "simp" "LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply"

set_option autoImplicit false

open LanglandsTunnell LanglandsTunnell.RealArchParam LanglandsTunnell.Converse AutomorphicForm

namespace ArchDatumMinimalWeight

private theorem det_coe_rotation (r : rowIsometrySubgroup₀ ℝ) :
    ((r : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 :=
  ((mem_rowIsometrySubgroup₀_iff ℝ).mp r.2).1

private theorem sign_det_mul_rotation (x : GL (Fin 2) ℝ) (r : rowIsometrySubgroup₀ ℝ) :
    SignType.sign ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det =
      SignType.sign (x : Matrix (Fin 2) (Fin 2) ℝ).det := by
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, det_coe_rotation, mul_one]

private theorem sign_det_ne_zero (g : GL (Fin 2) ℝ) :
    ((SignType.sign (g : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ) ≠ 0 := by
  rcases (Matrix.GeneralLinearGroup.det_ne_zero g).lt_or_gt with h | h
  · rw [sign_neg h]; simp
  · rw [sign_pos h]; simp

private theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

private theorem exists_oddDatum (u₁ u₂ : ℂ) :
    ∃ D : ArchDatumR (RealArchParam.principal u₁ 1 u₂ 0),
      D.W = fun g => PrincipalFamily.Wmem u₁ u₂ 1 0 g +
        Complex.I * (((SignType.sign g.det : ℝ) : ℂ) * PrincipalFamily.Wmem u₁ u₂ 0 1 g) := by
  obtain ⟨D₁, h₁⟩ := PrincipalFamily.exists_archDatumR_W_eq u₁ u₂ 1 0
  obtain ⟨D₂, h₂⟩ := PrincipalFamily.exists_archDatumR_W_eq u₁ u₂ 0 1
  obtain ⟨D₃, h₃⟩ : ∃ D' : ArchDatumR (RealArchParam.principal u₁ 1 u₂ 0),
      D'.W = fun g => ((SignType.sign g.det : ℝ) : ℂ) * D₂.W g :=
    ArchDatumR.exists_sgnTwist u₁ u₂ 0 1 D₂
  obtain ⟨D, hD⟩ := ArchDatumR.exists_lincomb D₁ D₃ 1 Complex.I
  exact ⟨D, by funext g; simp only [hD, h₁, h₃, h₂, one_mul]⟩

end ArchDatumMinimalWeight

theorem solution
    (P : RealArchParam)
    (hgen : (∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P = RealArchParam.principal u₁ a₁ u₂ a₂ →
      ∀ p : ℤ, p ≠ 0 → u₁ - u₂ = (p : ℂ) → a₁ - a₂ ≠ ((p + 1 : ℤ) : ZMod 2))) :
    ∃ (D : ArchDatumR P) (k₀ : ℤ),
      (∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P = RealArchParam.principal u₁ a₁ u₂ a₂ →
        (k₀ = 0 ∨ k₀ = 1) ∧ ((k₀ : ZMod 2) = a₁ + a₂)) ∧
      (∀ (u : ℂ) (m : ℕ) (hm : 1 ≤ m), P = RealArchParam.discrete u m hm → k₀ = (m : ℤ) + 1) ∧
      (∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ k₀ r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ)) ∧
      ArchCasimir.IsCasimirEigen D ∧
      ∃ g : GL (Fin 2) ℝ, D.W g ≠ 0 := by
  have _ := hgen
  cases P with
  | discrete u m hm =>
    obtain ⟨D, hDW⟩ := DiscreteFamily.exists_archDatumR_W_eq u m hm
    refine ⟨D, (m : ℤ) + 1, ?_, ?_, ?_, ?_, ?_⟩
    · intro u₁ u₂ a₁ a₂ h; cases h
    · intro u' m' hm' h; cases h; rfl
    · intro r x; rw [hDW]; exact DiscreteFamily.W_archWeightChar u m r x
    · intro x hx; rw [hDW]; exact DiscreteFamily.matrixCasimir_W u m hm x hx
    · obtain ⟨g, hg⟩ := DiscreteFamily.exists_W_ne_zero u m
      exact ⟨g, by rw [hDW]; exact hg⟩
  | principal u₁ a₁ u₂ a₂ =>
    rcases ArchDatumMinimalWeight.zmod_two_cases a₁ with rfl | rfl <;>
      rcases ArchDatumMinimalWeight.zmod_two_cases a₂ with rfl | rfl
    ·
      obtain ⟨D, hDW⟩ := PrincipalFamily.exists_archDatumR_W_eq u₁ u₂ 0 0
      refine ⟨D, 0, ?_, ?_, ?_, ?_, ?_⟩
      · intro v₁ v₂ b₁ b₂ h; cases h; exact ⟨Or.inl rfl, by simp⟩
      · intro u m hm h; cases h
      · intro r x; rw [hDW]; exact PrincipalFamily.Wmem_zero_zero_archWeightChar u₁ u₂ r x
      · exact PrincipalFamily.isCasimirEigen_of_W_eq_comb D 1 0 0 0 0 0 0 0 (by funext g; simp only [hDW]; ring)
      · obtain ⟨g, hg⟩ := PrincipalFamily.exists_Wmem_ne_zero u₁ u₂ 0 0
        exact ⟨g, by rw [hDW]; exact hg⟩
    ·
      obtain ⟨D₀, hW₀⟩ := ArchDatumMinimalWeight.exists_oddDatum u₁ u₂
      obtain ⟨D, hD⟩ : ∃ D : ArchDatumR (RealArchParam.principal u₁ 0 u₂ 1),
          D.W = fun g => ((SignType.sign g.det : ℝ) : ℂ) * D₀.W g :=
        ArchDatumR.exists_sgnTwist u₁ u₂ 1 0 D₀
      have hW : D.W = fun g => ((SignType.sign g.det : ℝ) : ℂ) * (PrincipalFamily.Wmem u₁ u₂ 1 0 g +
          Complex.I * (((SignType.sign g.det : ℝ) : ℂ) * PrincipalFamily.Wmem u₁ u₂ 0 1 g)) := by
        simp only [hD, hW₀]
      refine ⟨D, 1, ?_, ?_, ?_, ?_, ?_⟩
      · intro v₁ v₂ b₁ b₂ h; cases h; exact ⟨Or.inr rfl, by simp⟩
      · intro u m hm h; cases h
      · intro r x
        simp only [hW]
        rw [PrincipalFamily.oddComb_archWeightChar u₁ u₂ r x, ArchDatumMinimalWeight.sign_det_mul_rotation x r]
        ring
      · exact PrincipalFamily.isCasimirEigen_of_W_eq_comb D 1 Complex.I 1 2 1 0 0 1
          (by funext g; simp only [hW]; ring)
      · obtain ⟨g, hg⟩ := PrincipalFamily.exists_oddComb_ne_zero u₁ u₂
        exact ⟨g, by simp only [hW]; exact mul_ne_zero (ArchDatumMinimalWeight.sign_det_ne_zero g) hg⟩
    ·
      obtain ⟨D, hW⟩ := ArchDatumMinimalWeight.exists_oddDatum u₁ u₂
      refine ⟨D, 1, ?_, ?_, ?_, ?_, ?_⟩
      · intro v₁ v₂ b₁ b₂ h; cases h; exact ⟨Or.inr rfl, by simp⟩
      · intro u m hm h; cases h
      · intro r x; rw [hW]; exact PrincipalFamily.oddComb_archWeightChar u₁ u₂ r x
      · exact PrincipalFamily.isCasimirEigen_of_W_eq_comb D 1 Complex.I 0 1 1 0 0 1
          (by funext g; simp only [hW]; ring)
      · obtain ⟨g, hg⟩ := PrincipalFamily.exists_oddComb_ne_zero u₁ u₂
        exact ⟨g, by rw [hW]; exact hg⟩
    ·
      obtain ⟨D₀, h₀⟩ := PrincipalFamily.exists_archDatumR_W_eq u₁ u₂ 0 0
      obtain ⟨D, hD⟩ : ∃ D : ArchDatumR (RealArchParam.principal u₁ 1 u₂ 1),
          D.W = fun g => ((SignType.sign g.det : ℝ) : ℂ) * D₀.W g :=
        ArchDatumR.exists_sgnTwist u₁ u₂ 0 0 D₀
      have hW : D.W = fun g => ((SignType.sign g.det : ℝ) : ℂ) * PrincipalFamily.Wmem u₁ u₂ 0 0 g := by
        simp only [hD, h₀]
      refine ⟨D, 0, ?_, ?_, ?_, ?_, ?_⟩
      · intro v₁ v₂ b₁ b₂ h; cases h; exact ⟨Or.inl rfl, by simp only [Int.cast_zero]; decide⟩
      · intro u m hm h; cases h
      · intro r x
        simp only [hW]
        rw [PrincipalFamily.Wmem_zero_zero_archWeightChar u₁ u₂ r x,
          ArchDatumMinimalWeight.sign_det_mul_rotation x r]
        ring
      · exact PrincipalFamily.isCasimirEigen_of_W_eq_comb D 1 0 1 0 0 0 0 0 (by funext g; simp only [hW]; ring)
      · obtain ⟨g, hg⟩ := PrincipalFamily.exists_Wmem_ne_zero u₁ u₂ 0 0
        exact ⟨g, by simp only [hW]; exact mul_ne_zero (ArchDatumMinimalWeight.sign_det_ne_zero g) hg⟩

end S_LanglandsTunnell_Converse_exists_archDatumR_archWeightChar_minimalType_isCasimirEigen_W_ne_zero
end P2MW
export P2MW.S_LanglandsTunnell_Converse_exists_archDatumR_archWeightChar_minimalType_isCasimirEigen_W_ne_zero (solution)
