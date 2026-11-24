-- Prove2me | solution 1 for GlobalTheory.UnitLemma.PairClass.exists_intertwine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:09:36.002805+00:00
-- url     : https://prove2.me/submissions/d5b624be-caea-4ca2-b13f-43548b1f1792

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ExistsNeZeroAevalEqZero
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_UniNilp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAevalEqOfSeparable
import Theorems.Thm_GlobalTheory_UnitLemma_PairClass_exists_degreeLT_equiv

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
theorem _root_.solution (F V W : Type) [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W] (f : V →ₗ[F] V) (g : W →ₗ[F] W)
    (hs : f.charpoly.Separable) (he : f.charpoly = g.charpoly) : ∃ e : V ≃ₗ[F] W, ∀ v, e (f v) = g (e v) := by
  set P := f.charpoly with hPdef
  have hP : P.Monic := f.charpoly_monic
  obtain ⟨e₁, ψ₁, hψ₁⟩ := exists_degreeLT_equiv F V f P rfl hs
  obtain ⟨e₂, ψ₂, hψ₂⟩ := exists_degreeLT_equiv F W g P he.symm hs
  refine ⟨ψ₁.symm.trans ψ₂, fun v => ?_⟩
  obtain ⟨p, rfl⟩ := ψ₁.surjective v
  have hm : (X * (p : F[X])) %ₘ P ∈ degreeLT F P.natDegree := by
    rw [mem_degreeLT, ← degree_eq_natDegree hP.ne_zero]
    exact degree_modByMonic_lt _ hP
  have h1 : f (ψ₁ p) = ψ₁ ⟨_, hm⟩ := by
    rw [hψ₁, hψ₁, aeval_modByMonic_eq_self_of_root (LinearMap.aeval_self_charpoly f), map_mul, aeval_X,
      Module.End.mul_apply]
  have h2 : ψ₂ ⟨_, hm⟩ = g (ψ₂ p) := by
    rw [hψ₂, hψ₂, aeval_modByMonic_eq_self_of_root (show aeval g P = 0 by rw [he]; exact LinearMap.aeval_self_charpoly g),
      map_mul, aeval_X, Module.End.mul_apply]
  rw [h1, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, h2, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply]
end GlobalTheory.UnitLemma.PairClass
