-- Prove2me | solution 1 for GlobalTheory.UnitLemma.PairClass.exists_degreeLT_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:58:58.236167+00:00
-- url     : https://prove2.me/submissions/9ade36d8-56e0-4800-9ac9-2b662dc3f890

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ExistsNeZeroAevalEqZero
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_UniNilp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAevalEqOfSeparable
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_exists_annihilator_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.PairClass
namespace GlobalTheory.UnitLemma.PairClass
theorem _root_.solution (F V : Type) [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (f : V →ₗ[F] V) (P : F[X]) (hP : f.charpoly = P) (hs : P.Separable) :
    ∃ (e₀ : V) (ψ : degreeLT F P.natDegree ≃ₗ[F] V), ∀ p, ψ p = aeval f (p : F[X]) e₀ := by
  subst hP
  obtain ⟨e₀, -, he⟩ := Formalism.IrreducibleCountingLemmas.Z.exists_annihilator_eq f hs f.charpoly dvd_rfl
  let ψ : degreeLT F f.charpoly.natDegree →ₗ[F] V :=
    ((LinearMap.applyₗ e₀) ∘ₗ (aeval f).toLinearMap) ∘ₗ (degreeLT F _).subtype
  have hinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro q hq
    have h1 : f.charpoly ∣ (q : F[X]) := he _ hq
    have h2 : (q : F[X]).degree < f.charpoly.degree := by
      rw [degree_eq_natDegree f.charpoly_monic.ne_zero]
      exact mem_degreeLT.1 q.2
    exact Subtype.ext (eq_zero_of_dvd_of_degree_lt h1 h2)
  have : FiniteDimensional F (degreeLT F f.charpoly.natDegree) :=
    (degreeLTEquiv F _).symm.finiteDimensional
  have hdim : Module.finrank F (degreeLT F f.charpoly.natDegree) = Module.finrank F V := by
    rw [(degreeLTEquiv F _).finrank_eq, Module.finrank_fin_fun, LinearMap.charpoly_natDegree]
  exact ⟨e₀, LinearMap.linearEquivOfInjective ψ hinj hdim, fun p => rfl⟩
end GlobalTheory.UnitLemma.PairClass
