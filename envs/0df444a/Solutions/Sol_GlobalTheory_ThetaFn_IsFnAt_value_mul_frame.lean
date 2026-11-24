-- Prove2me | solution 1 for GlobalTheory.ThetaFn.IsFnAt.value_mul_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:06:17.196506+00:00
-- url     : https://prove2.me/submissions/08910094-edd4-427a-9232-5237bd34a989

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
import Theorems.Thm_GlobalTheory_ThetaFn_mem_ptChart_iff
import Theorems.Thm_P2M_GlobalTheory_ThetaFn_IsFnAt_valAt__ptSecT_57da73e55bb0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.ThetaFn
open CubeValues SymmetricSemicharacter
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
  {T : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ T)
variable {u p}
variable (u p)
variable {u p}
namespace GlobalTheory.ThetaFn
namespace IsFnAt
theorem _root_.solution {k : ℤ} {s : LB.Sec (LPow A L k T)} {θ : (Fin g → ℂ) → ℂ}
    (h : IsFnAt u p k s θ) {x : T ⟶ A} {z : Fin g → ℂ} (hx : p ≫ x = u.ex z)
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => k))}
    {v : Γ(T.left, ⊤)} (hv : IsValueAt A L k s x τ v) (j : Fin 1 → L.ι)
    (hj : ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j 0)) :
    valAt' p.left ⊤ v * valAt' p.left (LB.wchart L (fun _ : Fin 1 => x.left) j) (τ.s j).val =
      θ z * u.fr (j 0) z ^ k := by
  have hj' := (mem_ptChart_iff hx j).2 hj
  rw [← h.valAt'_ptSecT hx j hj', hv j, valAt'_mul _ hj', valAt'_res _ _ hj']
end IsFnAt
end GlobalTheory.ThetaFn
