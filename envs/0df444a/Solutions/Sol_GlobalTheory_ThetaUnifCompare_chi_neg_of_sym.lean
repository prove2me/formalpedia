-- Prove2me | solution 1 for GlobalTheory.ThetaUnifCompare.chi_neg_of_sym
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:32:44.327726+00:00
-- url     : https://prove2.me/submissions/48e4f040-462c-4b20-bf84-d8cd7bd30057

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_HermitianTensorPowers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ConstOfNormPeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ChiEqOneOrOfSym
import Theorems.Thm_GlobalTheory_CubeValues_ex_add_period
import Theorems.Thm_GlobalTheory_FrameValue_chi_ne_zero
import Theorems.Thm_GlobalTheory_FrameValue_const_of_norm_periodic
import Theorems.Thm_GlobalTheory_FrameValue_differentiable_genVal
import Theorems.Thm_GlobalTheory_FrameValue_genVal_add_period
import Theorems.Thm_GlobalTheory_FrameValue_genVal_ne_zero
import Theorems.Thm_GlobalTheory_FrameValue_hermForm_neg_left
import Theorems.Thm_GlobalTheory_FrameValue_hermForm_neg_right
import Theorems.Thm_GlobalTheory_SymmetricSemicharacter_ex_neg_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.ThetaUnifCompare
open GlobalTheory.FrameValue GlobalTheory.IndefiniteRowSideFullHecke.HermitianTensorPowers CubeValues SymmetricSemicharacter EigenNorm
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} {u : HolUnif A L g}
  {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
namespace GlobalTheory.ThetaUnifCompare
theorem _root_.solution (hL : L.IsLB) (hs : Out.Sym A L) (h : u.IsAH Hm χ) (l : u.Λ) : χ (-l) = χ l := by
  obtain ⟨U, hU, s, hs⟩ := hs (default : PrimeSpectrum ℂ)
  have hr : Set.range (𝟙 A.left : A.left ⟶ A.left) ⊆ Set.range (A.hom ⁻¹ᵁ U).ι := by
    rintro x -
    refine ⟨⟨x, ?_⟩, rfl⟩
    have e : A.hom x = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    show A.hom x ∈ U
    rw [e]; exact hU
  obtain ⟨p, hp⟩ : ∃ p : A.left ⟶ (A.hom ⁻¹ᵁ U).toScheme, p ≫ (A.hom ⁻¹ᵁ U).ι = 𝟙 _ :=
    ⟨_, IsOpenImmersion.lift_fac _ _ hr⟩
  have hz : ∀ w, IsLift u (K := Fin 2) ![(A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left, (A.hom ⁻¹ᵁ U).ι]
      ((u.ex w).left ≫ p) ![-w, w] := fun w k => by
    fin_cases k
    · show ((u.ex w).left ≫ p) ≫ (A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left = (u.ex (-w)).left
      rw [Category.assoc, reassoc_of% hp]
      exact ex_neg_left u w
    · show ((u.ex w).left ≫ p) ≫ (A.hom ⁻¹ᵁ U).ι = (u.ex w).left
      rw [Category.assoc, hp, Category.comp_id]
  have hd : Differentiable ℂ fun w => genVal u hL s ((u.ex w).left ≫ p) ![-w, w] :=
    differentiable_genVal hL hs p (q := id) differentiable_id (z := fun w => ![-w, w])
      (fun k => by fin_cases k <;> simp <;> fun_prop) hz
  have hper : ∀ (l : u.Λ) w, genVal u hL s ((u.ex (w + l)).left ≫ p) ![-(w + l), w + l] =
      χ (-l) / χ l * genVal u hL s ((u.ex w).left ≫ p) ![-w, w] := fun l w => by
    have e₂ : ![-(w + l), w + l] = fun k => ![-w, w] k + ((![-l, l] : Fin 2 → u.Λ) k : Fin g → ℂ) := by
      funext k
      fin_cases k <;> simp [add_comm]
    rw [ex_add_period u w l l.2, e₂, genVal_add_period hL h s (hz w)]
    congr 1
    have n := chi_ne_zero h l
    simp [ahFactor, hermForm_neg_left, hermForm_neg_right]
    field_simp
  have hc := const_of_norm_periodic u hd (fun l w => by
    rw [hper, norm_mul, norm_div, h.2.2.1, h.2.2.1, div_one, _root_.one_mul])
  have e := hper l 0
  rw [hc _ 0] at e
  exact (div_eq_one_iff_eq (chi_ne_zero h l)).1
    (mul_right_cancel₀ (genVal_ne_zero hL s (hz 0)) (e.symm.trans (_root_.one_mul _).symm))
end GlobalTheory.ThetaUnifCompare
