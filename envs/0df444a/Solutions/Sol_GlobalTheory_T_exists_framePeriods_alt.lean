-- Prove2me | solution 1 for GlobalTheory.T.exists_framePeriods_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:12:19.636787+00:00
-- url     : https://prove2.me/submissions/c00bd577-7ddd-4634-9bbf-c3d35617fb8a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsFramePeriods
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsFramePeriodsStatement
import Theorems.Thm_GlobalTheory_exists_framePeriods


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), GoodEmb c σ → ModelBase M → NegXi M → ∀ k, ∃ Pf, IsPerFr e F M k Pf ∧ (∀ Pf', IsPerFr e F M k Pf' → Pf' = Pf) ∧ (∀ x ∈ (M.X k).dom, IsPeriod (F.Di k) (fun j => relab c σ (e j).1) (Pf x)) ∧ (∀ a, DifferentiableOn ℂ (fun x => Pf x a) (M.X k).dom) ∧ ∀ P, IsPeriod (F.Di k) (fun j => relab c σ (e j).1) P → ∃ x ∈ (M.X k).dom, Pf x = P := by
  first | exact @GlobalTheory.exists_framePeriods | exact GlobalTheory.exists_framePeriods | (intros; apply GlobalTheory.exists_framePeriods <;> assumption)
end _root_.GlobalTheory.T
