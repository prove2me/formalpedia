-- Prove2me | solution 1 for GlobalTheory.finrank_le_of_span_sup_smul_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:56:48.381909+00:00
-- url     : https://prove2.me/submissions/d7498c74-834c-447a-8029-7af73860d6aa

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsLevMove
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AdmissibleColumnsLeAndHarmonicMapCover

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
theorem _root_.solution {R M : Type} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] {n : ℕ} (x : Fin n → M) (I : Ideal R) (hI : I ≠ ⊤)
    (h : Submodule.span R (Set.range x) ⊔ (I • ⊤ : Submodule R M) = ⊤) : Module.finrank R M ≤ n := by
  set N := Submodule.span R (Set.range x) with hN
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
    (N := N) (N' := ⊤) (P := ⊤) (I := I) Module.Finite.fg_top le_rfl (by rw [h])
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply hI
    rw [Ideal.eq_top_iff_one]
    simpa using I.neg_mem hr1
  have hmem : ∀ m : M, (r • (LinearMap.id : M →ₗ[R] M)) m ∈ N := fun m =>
    hr (Submodule.smul_mem_pointwise_smul m r ⊤ Submodule.mem_top)
  have hinj : Function.Injective ((r • (LinearMap.id : M →ₗ[R] M)).codRestrict N hmem) := by
    intro u v huv
    have : r • u = r • v := congrArg Subtype.val huv
    exact smul_right_injective M hr0 this
  haveI : Module.Finite R N := Module.Finite.span_of_finite R (Set.finite_range x)
  have h1 := LinearMap.finrank_le_finrank_of_injective hinj
  have h2 : Module.finrank R N ≤ n := by
    simpa [Set.finrank] using finrank_range_le_card (R := R) x
  exact h1.trans h2
end GlobalTheory
