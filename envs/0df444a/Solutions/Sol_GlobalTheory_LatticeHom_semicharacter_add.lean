-- Prove2me | solution 1 for GlobalTheory.LatticeHom.semicharacter_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:55:40.853904+00:00
-- url     : https://prove2.me/submissions/ad6442a9-2377-4694-98d3-2da2ee5ab4f3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_SectionsPowThetaFunctions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_HermFormSwapOfIsHermitian
import Theorems.Thm_GlobalTheory_LatticeHom_hermForm_swap_of_isHermitian
import Theorems.Thm_GlobalTheory_LatticeHom_hermForm_add_add
import Theorems.Thm_GlobalTheory_SectionTheta_ex_add_lattice
import Theorems.Thm_GlobalTheory_SymmetricSemicharacter_exists_chart
import Theorems.Thm_GlobalTheory_SymmetricSemicharacter_valueRules


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LatticeHom
variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {g g' : ℕ}
namespace GlobalTheory.LatticeHom
theorem _root_.solution (u : HolUnif A L g) (hL : L.IsLB) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    (h : u.IsAH Hm χ) (l m : u.Λ) :
    χ (l + m) = χ l * χ m * cexp (Real.pi * I * (hermForm Hm l m).im) := by
  obtain ⟨i, hi⟩ := GlobalTheory.SymmetricSemicharacter.exists_chart u GlobalTheory.SymmetricSemicharacter.valueRules hL 0
  have hfr := h.2.2.2
  have hl : ⊤ ≤ (u.ex (0 + (l : Fin g → ℂ))).left ⁻¹ᵁ L.U i := by
    rw [GlobalTheory.SectionTheta.ex_add_lattice]; exact hi
  have hex : u.ex ((l : Fin g → ℂ) + m) = u.ex 0 := by
    simpa using GlobalTheory.SectionTheta.ex_add_lattice u 0 (l + m)
  have hX : u.fr i ((l : Fin g → ℂ) + m) ≠ 0 := u.fr_ne i _ (by rw [hex]; exact hi)
  have hz : ∀ x, hermForm Hm 0 x = 0 := fun x => by simp [hermForm]
  have e1 : u.fr i 0 = χ (l + m) * cexp (Real.pi * hermForm Hm 0 ((l + m : u.Λ) : Fin g → ℂ) +
      Real.pi / 2 * hermForm Hm ((l + m : u.Λ) : Fin g → ℂ) ((l + m : u.Λ) : Fin g → ℂ)) *
      u.fr i (0 + ((l + m : u.Λ) : Fin g → ℂ)) := hfr (l + m) i 0 hi
  have e2 : u.fr i 0 = χ l * cexp (Real.pi * hermForm Hm 0 l + Real.pi / 2 * hermForm Hm l l) *
      u.fr i (0 + (l : Fin g → ℂ)) := hfr l i 0 hi
  have e3 : u.fr i (0 + (l : Fin g → ℂ)) = χ m * cexp (Real.pi * hermForm Hm (0 + (l : Fin g → ℂ)) m +
      Real.pi / 2 * hermForm Hm m m) * u.fr i (0 + (l : Fin g → ℂ) + m) := hfr m i (0 + l) hl
  simp only [hz, zero_add, mul_zero, Submodule.coe_add] at e1 e2 e3
  rw [e3] at e2
  rw [e2] at e1
  have hb : hermForm Hm (m : Fin g → ℂ) l = (starRingEnd ℂ) (hermForm Hm l m) :=
    hermForm_swap_of_isHermitian h.1 l m
  have hsc := Complex.sub_conj (hermForm Hm l m)
  have hexp : cexp (Real.pi / 2 * hermForm Hm l l) * cexp (Real.pi * hermForm Hm l m + Real.pi / 2 * hermForm Hm m m) =
      cexp (Real.pi / 2 * hermForm Hm ((l : Fin g → ℂ) + m) ((l : Fin g → ℂ) + m)) *
        cexp (Real.pi * I * (hermForm Hm l m).im) := by
    rw [← Complex.exp_add, ← Complex.exp_add, hermForm_add_add, hb]
    congr 1
    push_cast at hsc ⊢
    linear_combination (Real.pi / 2 : ℂ) * hsc
  have hC := Complex.exp_ne_zero (Real.pi / 2 * hermForm Hm ((l : Fin g → ℂ) + m) ((l : Fin g → ℂ) + m))
  have key : (χ (l + m) - χ l * χ m * cexp (Real.pi * I * (hermForm Hm l m).im)) *
      (cexp (Real.pi / 2 * hermForm Hm ((l : Fin g → ℂ) + m) ((l : Fin g → ℂ) + m)) *
        u.fr i ((l : Fin g → ℂ) + m)) = 0 := by
    linear_combination -e1 + (χ l * χ m * u.fr i ((l : Fin g → ℂ) + m)) * hexp
  rcases mul_eq_zero.1 key with h1 | h1
  · exact sub_eq_zero.1 h1
  · exact absurd h1 (mul_ne_zero hC hX)
end GlobalTheory.LatticeHom
