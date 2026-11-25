-- Prove2me | solution 1 for GlobalTheory.FrameUnits.val_eq_one_of_corr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:36:37.713865+00:00
-- url     : https://prove2.me/submissions/7d76eecc-ecfc-4fe5-a486-7325540482fc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HermFormPullEqOfLbIsoPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AppellHumbertDataOfIsoCube
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TripleProductTorusPeriodicBounded
import Theorems.Thm_GlobalTheory_CubeValues_le_preimage_inf
import Theorems.Thm_GlobalTheory_CubeValues_le_preimage_wchart
import Theorems.Thm_GlobalTheory_CubeValues_val_pullU
import Theorems.Thm_GlobalTheory_CubeValues_val_res
import Theorems.Thm_P2M_GlobalTheory_valAt__one_9935cf2928d8
import Theorems.Thm_P2M_GlobalTheory_valAt__rules_bb0546efa0f1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
open GlobalTheory.JetSer (IsNormRos primφ primε)
open GlobalTheory.CubeValues GlobalTheory.AppellHumbertTrivial
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.FrameUnits
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
namespace GlobalTheory.FrameUnits
theorem _root_.solution {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (h : Z ⟶ Y)
    (hc : LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ ε t h) (LB.oneGen L)) (x : Sp ℂ ⟶ Z) (j : L.ι)
    (hx : ∀ k, ⊤ ≤ ((x ≫ h) ≫ φ k) ⁻¹ᵁ L.U j) :
    valAt' (x ≫ h) (L.wchart φ fun _ => j) (t.s fun _ => j).val = 1 := by
  have hv : ValueRules := valAt'_rules
  have e := hc (fun _ => j) PEmpty.elim (fun _ _ _ => rfl) (fun k => k.elim) (fun _ k => k.elim)
  have h1 : ⊤ ≤ x ⁻¹ᵁ L.wchart (fun k => h ≫ φ k) (fun _ => j) :=
    (le_preimage_wchart x L _ _).2 fun k => by simpa only [Category.assoc] using hx k
  have h2 : ⊤ ≤ x ⁻¹ᵁ L.wchart (Y := Z) (K := PEmpty) PEmpty.elim PEmpty.elim :=
    (le_preimage_wchart x L _ _).2 fun k => k.elim
  have h3 := (le_preimage_inf x _ _).2 ⟨h1, h2⟩
  have e' := (val_res x hv inf_le_left h3 _).symm.trans
    ((congrArg (fun f : Γ(Z, _)ˣ => valAt' x _ f.val) e).trans (val_res x hv inf_le_right h3 _))
  refine ((val_res x hv _ h1 _).trans (val_pullU x hv h _ _)).symm.trans (e'.trans ?_)
  exact valAt'_one x h2
end GlobalTheory.FrameUnits
