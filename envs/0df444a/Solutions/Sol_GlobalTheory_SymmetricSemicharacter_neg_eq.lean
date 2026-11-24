-- Prove2me | solution 1 for GlobalTheory.SymmetricSemicharacter.neg_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:13:29.997235+00:00
-- url     : https://prove2.me/submissions/4697b89f-1cd0-4a51-a12b-58a3e5cabd5b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeTrivialisationOnUniformisingSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Theorems.Thm_GlobalTheory_SymmetricSemicharacter_exists_chart
import Theorems.Thm_GlobalTheory_SymmetricSemicharacter_exists_symmetry_values
import Theorems.Thm_GlobalTheory_CubeValues_ex_add_period
import Theorems.Thm_GlobalTheory_CubeValues_le_preimage_inf
import Theorems.Thm_GlobalTheory_CubeValues_val_unit_ne_zero
import Theorems.Thm_GlobalTheory_appellHumbert_trivial_of_nowhere_vanishing


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
open GlobalTheory.SymmetricSemicharacter
open CubeValues
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
namespace GlobalTheory.SymmetricSemicharacter
theorem _root_.solution (hv : ValueRules) (hL : L.IsLB) (hs : Out.Sym A L)
    {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    (h : u.IsAH Hm χ) (l : u.Λ) : χ (-l) = χ l := by
  obtain ⟨T, hTd, hT0, hTc, hTp⟩ := exists_symmetry_values u hv hs
  choose ch hch using exists_chart u hv hL
  let R : L.ι → L.ι → (Fin g → ℂ) → ℂ := fun i j z => T i j z * u.fr j z / u.fr i (-z)
  let r : (Fin g → ℂ) → ℂ := fun z => R (ch (-z)) (ch z) z
  have hrR : ∀ i j z, ⊤ ≤ (u.ex (-z)).left ⁻¹ᵁ L.U i → ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U j →
      r z = R i j z := fun i j z hi hj => by
    have k1 := (le_preimage_inf _ _ _).2 ⟨hch (-z), hi⟩
    have k2 := (le_preimage_inf _ _ _).2 ⟨hch z, hj⟩
    have n1 := val_unit_ne_zero _ hv k1 (L.g _ _)
    have n2 := val_unit_ne_zero _ hv k2 (L.g _ _)
    have n3 := u.fr_ne i _ hi
    simp only [r, R]
    rw [hTc _ _ i j z (hch _) (hch _) hi hj, u.fr_compat _ _ _ k1, u.fr_compat _ _ _ k2]
    field_simp
  have hopen : ∀ i, IsOpen {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i} := fun i => (u.hol _ 0).1
  have hd : Differentiable ℂ r := fun z => by
    set i := ch (-z)
    set j := ch z
    have ho : IsOpen {w | ⊤ ≤ (u.ex (-w)).left ⁻¹ᵁ L.U i ∧ ⊤ ≤ (u.ex w).left ⁻¹ᵁ L.U j} :=
      ((hopen i).preimage continuous_neg).inter (hopen j)
    have hR : DifferentiableOn ℂ (R i j)
        {w | ⊤ ≤ (u.ex (-w)).left ⁻¹ᵁ L.U i ∧ ⊤ ≤ (u.ex w).left ⁻¹ᵁ L.U j} := by
      simp only [R, div_eq_mul_inv]
      refine ((hTd i j).fun_mul ((u.fr_hol j).mono fun w hw => hw.2)).fun_mul
        (DifferentiableOn.fun_inv ?_ fun w hw => u.fr_ne i _ hw.1)
      exact (u.fr_hol i).comp (f := fun w => -w) (by fun_prop) fun w hw => hw.1
    exact (hR.congr fun w hw => hrR i j w hw.1 hw.2).differentiableAt
      (ho.mem_nhds ⟨hch _, hch _⟩)
  have hne : ∀ z, r z ≠ 0 := fun z =>
    div_ne_zero (mul_ne_zero (hT0 _ _ _ (hch _) (hch _)) (u.fr_ne _ _ (hch _))) (u.fr_ne _ _ (hch _))
  have hχ : ∀ l, χ l ≠ 0 := fun l h0 => by simpa [h0] using h.2.2.1 l
  haveI := u.discrete
  have key := (appellHumbert_trivial_of_nowhere_vanishing g u.Λ u.full 0
    (fun l => χ (-l) / χ l) r Matrix.isHermitian_zero
    (fun l => by rw [norm_div, h.2.2.1, h.2.2.1, div_one]) hd hne (fun l z => ?_)).2.1 l
  · exact (div_eq_one_iff_eq (hχ l)).1 key
  have e : -(z + (l : Fin g → ℂ)) = -z + ((-l : u.Λ) : Fin g → ℂ) := by
    rw [Submodule.coe_neg, neg_add]
  have hi : ⊤ ≤ (u.ex (-(z + l))).left ⁻¹ᵁ L.U (ch (-z)) := by
    rw [e, ex_add_period u _ _ (-l).2]; exact hch _
  have hj : ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ L.U (ch z) := by
    rw [ex_add_period u _ _ l.2]; exact hch _
  rw [hrR _ _ _ hi hj]
  have n1 := u.fr_ne _ _ hi
  have n2 := hχ l
  have n3 := hχ (-l)
  simp only [r, R]
  rw [hTp, h.2.2.2 l _ z (hch _), h.2.2.2 (-l) _ (-z) (hch _), ← e]
  simp only [hermForm, Matrix.zero_mulVec, dotProduct_zero, mul_zero, add_zero, Complex.exp_zero,
    Submodule.coe_neg, star_neg, Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg]
  have n4 := Complex.exp_ne_zero (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
        Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))
  field_simp
end GlobalTheory.SymmetricSemicharacter
