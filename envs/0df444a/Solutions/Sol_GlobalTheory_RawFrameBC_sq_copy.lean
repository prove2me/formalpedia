-- Prove2me | solution 1 for GlobalTheory.RawFrameBC.sq_copy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:51:57.802553+00:00
-- url     : https://prove2.me/submissions/84936bb2-fc6b-4aee-b1cc-c45ef971ba2a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_JetSubstPCompJetBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsRawChartFramesBaseChange
import Theorems.Thm_GlobalTheory_RawFrameBC_sq_of_ring
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetSubstP_comp_jetBC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.RawFrameBC
section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X) (d : ℕ)
private theorem jetCopy_eq_lemma {R : Type} [CommRing R] {d n : ℕ} (m : ℕ) (i : Fin n) :
    (jetCopy d m i : Jet R (Fin 1 × Fin d) m →ₐ[R] Jet R (Fin n × Fin d) m) =
      jetSubstP m (fun p : Fin 1 × Fin d => (MvPolynomial.X (i, p.2) : MvPolynomial (Fin n × Fin d) R)) := by
  unfold jetCopy jetSubstP
  congr 1
  funext p
  simp
end
end GlobalTheory.RawFrameBC
end
end

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
theorem _root_.solution {n : ℕ} (m : ℕ) (i : Fin n) :
    homAt (spMap ψ ≫ x0) (jetCopy d m i) ≫ rjBC ψ x0 d m 1 = rjBC ψ x0 d m n ≫ homAt x0 (jetCopy d m i) := by
  rw [jetCopy_eq_lemma, jetCopy_eq_lemma]
  have := sq_of_ring ψ x0 d _ _
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.jetSubstP_comp_jetBC ψ m
      (fun p : Fin 1 × Fin d => (MvPolynomial.X (i, p.2) : MvPolynomial (Fin n × Fin d) S)))
  simpa only [MvPolynomial.map_X] using this
end GlobalTheory.RawFrameBC
