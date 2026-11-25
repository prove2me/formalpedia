-- Prove2me | solution 1 for GlobalTheory.WdAinf.pow_mem_of_nonunit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:00:17.813408+00:00
-- url     : https://prove2.me/submissions/7f7418c4-7f6e-42fe-99b3-e0d1171ebe5a

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ModPToValuationResidueFieldSurjective

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
theorem _root_.solution (hv : v.Integers O) (x : O) (hx : ¬IsUnit x) :
    ∃ n : ℕ, (p : O) ∣ x ^ n := by
  have h1 : v (algebraMap O C x) < 1 :=
    lt_of_le_of_ne (hv.map_le_one x) (fun e => hx (hv.isUnit_of_one' e))
  have h2 : 0 < v (p : C) :=
    pos_iff_ne_zero.2 fun h => Nat.cast_ne_zero.2 hp.out.ne_zero ((Valuation.zero_iff v).1 h)
  obtain ⟨n, hn⟩ := NNReal.exists_pow_lt_of_lt_one h2 h1
  refine ⟨n, hv.dvd_of_le ?_⟩
  rw [map_pow, map_pow, map_natCast]
  exact hn.le
end GlobalTheory.WdAinf
