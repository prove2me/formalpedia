-- Prove2me | solution 1 for GlobalTheory.CharGerm.coeff_mem_of_mem_truncI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:02:33.71251+00:00
-- url     : https://prove2.me/submissions/f78c71de-d05c-48b7-ad59-a3e0e77d710f

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitOfBijectiveMulNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqOneOfPowEqOneOfCompEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsSeriesOfTorsionCharacters
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.CharGerm
variable {R₀ κ : Type} [CommRing R₀]
namespace GlobalTheory.CharGerm
theorem _root_.solution [DecidableEq κ] {p N : ℕ}
    {q : MvPolynomial κ R₀} (hq : q ∈ truncI R₀ κ p N) :
    ∀ m : κ →₀ ℕ, (∀ j, m j < N) → MvPolynomial.coeff m q ∈ Ideal.span {(p : R₀) ^ N} := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hq
  · rintro _ (rfl | ⟨j, rfl⟩) m hm
    · have : (p : MvPolynomial κ R₀) ^ N = MvPolynomial.C ((p : R₀) ^ N) := by simp
      rw [this, MvPolynomial.coeff_C]
      split_ifs
      · exact Ideal.mem_span_singleton_self _
      · exact zero_mem _
    · simp only [MvPolynomial.coeff_X_pow]
      rw [if_neg]
      · exact zero_mem _
      rintro rfl
      simpa using hm j
  · intro m _; simp
  · intro x y _ _ hx hy m hm
    rw [MvPolynomial.coeff_add]
    exact add_mem (hx m hm) (hy m hm)
  · intro r x _ hx m hm
    rw [smul_eq_mul, MvPolynomial.coeff_mul]
    refine Ideal.sum_mem _ fun e he => Ideal.mul_mem_left _ _ (hx e.2 ?_)
    intro j
    have : e.1 + e.2 = m := by simpa using he
    have h2 := hm j
    rw [← this, Finsupp.add_apply] at h2
    omega
end GlobalTheory.CharGerm
