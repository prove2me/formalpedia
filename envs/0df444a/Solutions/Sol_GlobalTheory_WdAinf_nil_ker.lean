-- Prove2me | solution 1 for GlobalTheory.WdAinf.nil_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:12:10.774519+00:00
-- url     : https://prove2.me/submissions/3a185813-0711-4304-b341-ceffd13609d3

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ModPToValuationResidueFieldSurjective
import Theorems.Thm_GlobalTheory_WdAinf_pow_mem_of_nonunit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.WdAinf
open WittVector Ideal
variable (p : ℕ) [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
namespace GlobalTheory.WdAinf
theorem _root_.solution (hv : v.Integers O) (ϖ : PreTilt O p) (hϖ : ϖ.untilt = (p : O)) (w : WRing p O ϖ)
    (hw : rho1 p O hv (piW p O ϖ hϖ w) = 0) : IsNilpotent w := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective w
  have h1 : resO O hv (fontaineTheta O p a) = 0 := hw
  obtain ⟨n, c, hc⟩ := pow_mem_of_nonunit p O hv _ ((resO_eq_zero O hv _).1 h1)
  have h2 : (Ideal.Quotient.mk _ a : WRing p O ϖ) ^ n ∈ RingHom.ker (piW p O ϖ hϖ) := by
    rw [RingHom.mem_ker, map_pow, piW_mk, ← map_pow, hc, map_mul, map_natCast, modP_valuationIntegers_prime_eq_zero, zero_mul]
  rw [ker_piW p O hv ϖ hϖ] at h2
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h2
  refine ⟨n * 2, ?_⟩
  rw [pow_mul, ← hy, mul_pow, p_sq, mul_zero]
end GlobalTheory.WdAinf
