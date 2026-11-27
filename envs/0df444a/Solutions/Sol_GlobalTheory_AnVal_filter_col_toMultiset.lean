-- Prove2me | solution 1 for GlobalTheory.AnVal.filter_col_toMultiset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:40:43.898862+00:00
-- url     : https://prove2.me/submissions/a9111a47-0cfe-498d-a94f-fe5d4edfbca7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_Taylor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_PolyDerivProdColumnFunctions

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AnVal
open scoped ContDiff
namespace GlobalTheory.AnVal
theorem _root_.solution {T : Type} [Fintype T] {r : T → ℕ} {n : ℕ}
    (m : Formalism.L2.Pj.Letter T r n →₀ ℕ) (b : Fin n) :
    (Finsupp.toMultiset m).filter (fun ℓ => ℓ.2.2 = b) =
      (Finsupp.toMultiset (Finsupp.equivFunOnFinite.symm
        fun ℓ : (Σ τ : T, Fin (r τ)) => m ⟨ℓ.1, ℓ.2, b⟩)).map
        (fun ℓ : (Σ τ : T, Fin (r τ)) => (⟨ℓ.1, ℓ.2, b⟩ : Formalism.L2.Pj.Letter T r n)) := by
  classical
  have hinj : Function.Injective
      (fun ℓ : (Σ τ : T, Fin (r τ)) => (⟨ℓ.1, ℓ.2, b⟩ : Formalism.L2.Pj.Letter T r n)) := by
    intro x y h
    exact congrArg (fun ℓ : Formalism.L2.Pj.Letter T r n => (⟨ℓ.1, ℓ.2.1⟩ : Σ τ : T, Fin (r τ))) h
  ext ⟨τ, i, c⟩
  rw [Multiset.count_filter]
  by_cases h : c = b
  · subst h
    rw [if_pos rfl]
    have := Multiset.count_map_eq_count' _ (Finsupp.toMultiset (Finsupp.equivFunOnFinite.symm
        fun ℓ : (Σ τ : T, Fin (r τ)) => m ⟨ℓ.1, ℓ.2, c⟩)) hinj ⟨τ, i⟩
    rw [this]
    simp [Finsupp.count_toMultiset]
  · rw [if_neg h]
    symm
    rw [Multiset.count_eq_zero, Multiset.mem_map]
    rintro ⟨x, -, hx⟩
    exact h (congrArg (fun ℓ : Formalism.L2.Pj.Letter T r n => ℓ.2.2) hx).symm
end GlobalTheory.AnVal
