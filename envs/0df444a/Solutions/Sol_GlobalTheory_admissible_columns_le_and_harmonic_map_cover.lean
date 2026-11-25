-- Prove2me | solution 1 for GlobalTheory.admissible_columns_le_and_harmonic_map_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:43:47.340238+00:00
-- url     : https://prove2.me/submissions/ac3fa1b7-107b-49e9-bf3a-0f016b0f32b2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsLevMove
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AdmissibleColumnsLeAndHarmonicMapCover
import Theorems.Thm_GlobalTheory_map_mem_HHa
import Theorems.Thm_GlobalTheory_finrank_le_of_span_sup_smul_top
import Theorems.Thm_GlobalTheory_Mfr_ne_top

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
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), (∀ (rk : Bool) (x0 : Fin n → Dw.La), AdmX (l := l) rk x0 → Dw.p + Dw.q ≤ n) ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P ∈ HHa Dw.mult n d.c₂.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) := by
  intro E _ _ _ H Dw l Xo c n d
  refine ⟨fun rk x0 hx => ?_, fun a P hP => ?_⟩
  swap
  · have hs : Function.Surjective (d.eF : c.F →+* d.c₂.F) := fun y => ⟨d.eF.symm y, d.eF.apply_symm_apply y⟩
    generalize (d.eF : c.F →+* d.c₂.F) = f at hs ⊢
    exact map_mem_HHa Dw.mult n f hs _ _ _ P hP
  haveI := Dw.fin
  haveI := Dw.proj
  rw [← Dw.rank]
  refine finrank_le_of_span_sup_smul_top x0 (Mfr l) (Mfr_ne_top l) ?_
  unfold AdmX at hx
  refine top_le_iff.1 (hx.ge.trans ?_)
  exact sup_le_sup_right (Submodule.span_mono (Set.image_subset_range _ _)) _
end GlobalTheory
