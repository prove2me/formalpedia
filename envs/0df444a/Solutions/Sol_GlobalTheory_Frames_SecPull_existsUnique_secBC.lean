-- Prove2me | solution 1 for GlobalTheory.Frames.SecPull.existsUnique_secBC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:50:58.666459+00:00
-- url     : https://prove2.me/submissions/ce2567f4-6c9d-4a6f-9bce-dbd2762e3653

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueScaledBaseChangeFibreSection
import Theorems.Thm_GlobalTheory_Frames_SecPull_exists_pull_linComb
import Theorems.Thm_GlobalTheory_Frames_SecPull_lbSec_ext
import Theorems.Thm_GlobalTheory_Frames_SecPull_ppx_chart_le
import Theorems.Thm_GlobalTheory_Frames_SecPull_gxMap_snd
import Theorems.Thm_GlobalTheory_Frames_SecPull_gxMap_fst
import Theorems.Thm_GlobalTheory_Frames_SecPull_gx_hom_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Frames GlobalTheory.Frames.SecPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
namespace GlobalTheory.Frames.SecPull
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S T : Type) [CommRing S] [CommRing T] (φ : S →+* T) (a : S) (x : Sp S ⟶ Xo.X) (x' : Sp T ⟶ Xo.X), x' = spMap φ ≫ x → ∀ s : LB.Sec (PPx x), ∃! s' : LB.Sec (PPx x'), SecBC φ a x x' s s' := by
  intro E _ _ _ H Dw l Xo S T _ _ φ a x x' hx s
  have hs := gxMap_snd φ x x' hx.symm
  have hf := gxMap_fst φ x x' hx.symm
  obtain ⟨s', hs'⟩ := exists_pull_linComb Xo.univ.t.PP.L (K := Fin 1)
    (fun _ => (snd (Over.mk x) Xo.univ.t.G).left) (fun _ => (snd (Over.mk x') Xo.univ.t.G).left) _
    (gxMap φ x x' hx.symm) (funext fun _ => hs) (scalSec x a s)
  refine ⟨s', ⟨_, hs, hf, hs'⟩, ?_⟩
  rintro t ⟨pm, ps, pf, ht⟩
  obtain rfl : pm = gxMap φ x x' hx.symm :=
    gx_hom_ext _ _ (pf.trans hf.symm) (ps.trans hs.symm)
  exact lbSec_ext fun i => (ht i (ppx_chart_le _ hs i)).symm.trans (hs' i (ppx_chart_le _ hs i))
end GlobalTheory.Frames.SecPull
