-- Prove2me | solution 1 for GlobalTheory.DatumInverseCharacter.exists_quot_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:46:46.670086+00:00
-- url     : https://prove2.me/submissions/196d6dd0-11ea-412a-86f7-801c1fbb1a43

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsLevMove
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsQuotEquiv
import Theorems.Thm_GlobalTheory_DatumInverseCharacter_mem_of_modN

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
open GlobalTheory GlobalTheory.DatumInverseCharacter
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace GlobalTheory.DatumInverseCharacter
theorem _root_.solution (D : Datum H) {n : ℕ} {K : Ideal (𝓞 E)} (hK : (n : 𝓞 E) ∈ K)
    (f g : D.La →ₗ[𝓞 E] D.La) (h : ∀ a, D.ModN n (g (f a) - a) ∧ D.ModN n (f (g a) - a)) :
    ∃ k : (D.La ⧸ (K • ⊤ : Submodule (𝓞 E) D.La)) ≃ₗ[𝓞 E] (D.La ⧸ (K • ⊤ : Submodule (𝓞 E) D.La)),
      ∀ a, k (Submodule.Quotient.mk a) = Submodule.Quotient.mk (f a) := by
  have hle : ∀ φ : D.La →ₗ[𝓞 E] D.La,
      (K • ⊤ : Submodule (𝓞 E) D.La) ≤ (K • ⊤ : Submodule (𝓞 E) D.La).comap φ := by
    intro φ
    rw [Submodule.smul_le]
    intro r hr x _
    rw [Submodule.mem_comap, map_smul]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  refine ⟨LinearEquiv.ofLinear ((K • ⊤ : Submodule (𝓞 E) D.La).mapQ _ f (hle f))
    ((K • ⊤ : Submodule (𝓞 E) D.La).mapQ _ g (hle g)) ?_ ?_, fun a => rfl⟩
  · ext a
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
      LinearMap.id_apply]
    exact (Submodule.Quotient.eq _).2 (mem_of_modN D hK (h a).2)
  · ext a
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
      LinearMap.id_apply]
    exact (Submodule.Quotient.eq _).2 (mem_of_modN D hK (h a).1)
end GlobalTheory.DatumInverseCharacter
