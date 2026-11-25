-- Prove2me | solution 1 for GlobalTheory.ZH.WtGen.pure_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:11:44.409006+00:00
-- url     : https://prove2.me/submissions/ff6790cf-1066-4d0c-a539-887171b6c296

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueIsRatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsPartPartSec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GroupAlgebraSingleOneMemOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPowEqTorus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_PureSectionRatiosGenerateFunctions
import Theorems.Thm_GlobalTheory_ZH_WtGen_eq_mono
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
noncomputable section
open GlobalTheory GlobalTheory.ZH GlobalTheory.ZH.WtGen
open GlobalTheory.ZH.WtPart
variable {k : Type} [Field k] (Φ : FibPre k)
namespace GlobalTheory.ZH.WtGen
theorem _root_.solution {α : Φ.E.X} {φ : (Φ.H 1).Sec} (hφ : Φ.Pure α φ) (l : Φ.N₀.ι) {W : Φ.E.B.left.Opens}
    (h : W ≤ Φ.N₀.U l) : ∃ c : Γ(Φ.E.B.left, W), resG _ (Φ.D.q.left.preimage_mono h) (φ.f l) =
      (Φ.D.q.left.app W).hom c * mono Φ.D (Φ.ch l) W (h.trans (Φ.le l)) (Multiplicative.ofAdd α) := by
  have e := eq_mono (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l)) (s := φ.f l) (α := α)
    (fun χ hχ => by
      by_contra hne
      exact hχ (hφ ⟨l, hne⟩))
  obtain ⟨c, hc⟩ := res_mono Φ.D (Φ.le l) (h.trans (Φ.le l)) h α
  refine ⟨resG _ h (Φ.wt φ α l) * c, (congrArg (resG _ (Φ.D.q.left.preimage_mono h)) e).trans
    ((map_mul (resG _ (Φ.D.q.left.preimage_mono h)) _ _).trans ?_)⟩
  rw [hc, rapp, map_mul, _root_.mul_assoc]
  rfl
end GlobalTheory.ZH.WtGen
