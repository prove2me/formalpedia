-- Prove2me | solution 1 for GlobalTheory.WitnessData.value_of_genRel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:45:02.152183+00:00
-- url     : https://prove2.me/submissions/4ab72db0-7022-4b2c-8953-92b7fb3020f8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AdmissibleBasePowerSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataIsoOfTwoWitnesses
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_genRel_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.WitnessData
namespace GlobalTheory.WitnessData
theorem _root_.solution {F : Type} [Field F] {B B' B₀ : Scheme.{0}} {M : LB B} {M' : LB B'} {M₀ : LB B₀} {K : Type}
    [Fintype K] {ε : K → ℤ} {φ : B ⟶ B₀} {Φ : B' ⟶ B} {w : LB.Iso M (M₀.pull φ)} {wD : LB.Iso M' (M.pull Φ)}
    {w' : LB.Iso M' (M₀.pull (Φ ≫ φ))} (T : Tri w wD w') (hM₀ : M₀.IsLB) {pt : K → (Sp F ⟶ B)}
    {pt' : K → (Sp F ⟶ B')} {pt₀ : K → (Sp F ⟶ B₀)} (hc : ∀ k, pt' k ≫ Φ = pt k)
    {t : LB.Gen (LB.LinComb M pt ε)} {t' : LB.Gen (LB.LinComb M' pt' ε)} {t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)} {x : F}
    (h : GenRel w t t₀ x) (h' : GenRel w' t' t₀ x) (z : Sp F) (p : K → M.ι) (q : K → M'.ι)
    (hp : ∀ k, Φ (pt' k z) ∈ M.U (p k)) (hq : ∀ k, pt' k z ∈ M'.U (q k)) :
    gm (𝟙 _) z (LB.wchart M pt p) (t.s p) =
      (∏ k, gw wD (pt' k) z (p k) (q k) ^ ε k) * gm (𝟙 _) z (LB.wchart M' pt' q) (t'.s q) := by
  have pe : ∀ k, pt k z = Φ (pt' k z) := fun k => congrArg (fun g => g z) (hc k).symm
  choose j hj using fun k => exists_chart hM₀ (φ (Φ (pt' k z)))
  have a := T.prod (ε := ε) (h' := 𝟙 _) (fun k => (hc k).trans (Category.id_comp _).symm) _ (𝟙 _) z j p q hj hp hq
  simp only [Category.id_comp] at a
  have b := ((genRel_iff w t t₀ x z).1 h).2 p j (fun k => by rw [pe]; exact hj k) (fun k => by rw [pe]; exact hp k)
  have b' := ((genRel_iff w' t' t₀ x z).1 h').2 q j hj hq
  have e := Units.ext (b.trans b'.symm)
  rw [a, _root_.mul_assoc] at e
  exact mul_left_cancel e
end GlobalTheory.WitnessData
