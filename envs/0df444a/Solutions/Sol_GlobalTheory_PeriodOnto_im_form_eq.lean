-- Prove2me | solution 1 for GlobalTheory.PeriodOnto.im_form_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:23:00.787197+00:00
-- url     : https://prove2.me/submissions/54a85c46-f76c-400a-86a8-eb6e0dd22873

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqIffConjNe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsFrameOfIsPeriod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexOrder ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.PeriodOnto
variable {ι : Type} [Fintype ι] {g r : ℕ} (idx : Fin g ≃ ι × Fin r) (q : ℕ)
variable {Λ : Type} (P : Λ → Fin g → ℂ) (hspan : Submodule.span ℝ (Set.range P) = ⊤)
  (e : ι → Λ → Fin r → ℂ) (M : ι → Matrix (Fin r) (Fin r) ℂ)
  (hM : ∀ v t, blockOf idx q t (P v) = M t *ᵥ e t v)
include hspan
namespace GlobalTheory.PeriodOnto
theorem _root_.solution (A : ι → Matrix (Fin r) (Fin r) ℂ) (s : ι → ℝ) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (h : ∀ x y, (hermForm Hm (P x) (P y)).im =
      ∑ t, -2 * s t * (blockOf idx q t (P x) ⬝ᵥ A t *ᵥ star (blockOf idx q t (P y))).im)
    (z z' : Fin g → ℂ) : (hermForm Hm z z').im =
      ∑ t, -2 * s t * (blockOf idx q t z ⬝ᵥ A t *ᵥ star (blockOf idx q t z')).im := by
  have hz : z ∈ Submodule.span ℝ (Set.range P) := by rw [hspan]; trivial
  have hz' : z' ∈ Submodule.span ℝ (Set.range P) := by rw [hspan]; trivial
  unfold hermForm at *
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, rfl⟩ := hz
    induction hz' using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨y, rfl⟩ := hz
      exact h x y
    | zero => simp
    | add _ _ _ _ h1 h2 =>
      simp only [star_add, mulVec_add, dotProduct_add, Complex.add_im, map_add, h1, h2, mul_add,
        Finset.sum_add_distrib]
    | smul c _ _ h1 =>
      simp only [star_smul, star_trivial, mulVec_smul, dotProduct_smul, Complex.smul_im, map_smul, h1,
        smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
  | zero => simp
  | add _ _ _ _ h1 h2 =>
    simp only [add_dotProduct, Complex.add_im, map_add, h1, h2, mul_add, Finset.sum_add_distrib]
  | smul c _ _ h1 =>
    simp only [smul_dotProduct, Complex.smul_im, map_smul, h1, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
end GlobalTheory.PeriodOnto
