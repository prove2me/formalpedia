-- Prove2me | solution 1 for GlobalTheory.VVRank.ofSec_eq_zero_of_twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:23:25.468853+00:00
-- url     : https://prove2.me/submissions/a7d0a59d-10b9-4e00-858c-92a8a4bc29b4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ForallGeometricallyIntegralOfSmoothOfGeometrical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomFromSpecResidueField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatAndSurjectiveOfIsFiniteAbelianEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MulAFiniteFlatSurjectiveEtale
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpanEqTopOfFunctionals
import Theorems.Thm_GlobalTheory_VVRank_sv_of_isTwistPull
import Theorems.Thm_GlobalTheory_MulFinite_isUnit_gs
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_exists_chart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.VVRank
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
open scoped CategoryTheory.Obj
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left}
namespace GlobalTheory.VVRank
theorem _root_.solution (hL : L.IsLB) {T : Over S} [IsReduced (T ⊗ A).left]
    {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A} {hm : ψ ≫ snd T A = m} {a b : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])}
    (hψ : Surjective ψ.left) {s : LB.Sec (LPow A L b T)} {s' : LB.Sec (LPow A L a T)}
    (H : IsTwistPull A L ψ m hm a b α s s') (h0 : (SecM.ofSec A s' : SecM A L a T) = 0) :
    (SecM.ofSec A s : SecM A L b T) = 0 := by
  refine Subtype.ext (funext fun j => eq_zero_of_basicOpen_eq_bot (s.f j) (eq_bot_iff.2 fun y hy => ?_))
  exfalso
  obtain ⟨z, rfl⟩ := ψ.left.surjective y
  have hz : ψ.left z ∈ (LPow A L b T).U j := (T ⊗ A).left.basicOpen_le _ hy
  have hu := (MulFinite.isUnit_gs ψ.left z _ hz _).2 hy
  choose J hJ using fun χ : (T ⊗ A).left ⟶ A.left => exists_chart hL (χ z)
  have e := sv_of_isTwistPull A H (𝟙 _) z hJ
  have e0 : sv A s' (𝟙 _) z J = 0 := by
    have : ∀ j, s'.f j = 0 := fun j => congrFun (congrArg Subtype.val h0) j
    refine (congrArg (gs _ z _) (this _)).trans ((gs_eq _ z _ (Good.mem hJ _ _) _).trans ?_)
    exact (congrArg _ (map_zero _)).trans (map_zero _)
  rw [e0, Category.id_comp, eq_comm, Units.mul_right_eq_zero] at e
  have e' := sec_trans (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s ψ.left z hz
    (Good.mem hJ _ _)
  exact hu.ne_zero (e'.trans ((congrArg _ e).trans (mul_zero _)))
end GlobalTheory.VVRank
