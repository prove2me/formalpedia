-- Prove2me | solution 1 for GlobalTheory.RawFrameBC.sq_of_ring
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:31:46.406518+00:00
-- url     : https://prove2.me/submissions/afb8919b-2e50-4c23-808a-ce3e32fec6f2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_JetSubstPCompJetBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsRawChartFramesBaseChange
import Theorems.Thm_GlobalTheory_RawFrameBC_spMap_comp_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.RawFrameBC
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X) (d : ℕ)
namespace GlobalTheory.RawFrameBC
theorem _root_.solution {m n n' : ℕ} (f : Jet S (Fin n × Fin d) m →ₐ[S] Jet S (Fin n' × Fin d) m)
    (f' : Jet S' (Fin n × Fin d) m →ₐ[S'] Jet S' (Fin n' × Fin d) m)
    (h : f'.toRingHom.comp (jetBC ψ _ m) = (jetBC ψ _ m).comp f.toRingHom) :
    homAt (spMap ψ ≫ x0) f' ≫ rjBC ψ x0 d m n = rjBC ψ x0 d m n' ≫ homAt x0 f := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, Formalism.L2.Pj.homAt, rjBC, Over.homMk_left]
  rw [spMap_comp_eq, spMap_comp_eq]
  congr 1
end GlobalTheory.RawFrameBC
