-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.RowTrans.exists_linearEquiv_apply_eq_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:47:31.704738+00:00
-- url     : https://prove2.me/submissions/a0edb2fa-6dd9-4d0e-b070-68703b7ba90f

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GLTransitiveNonzeroVectors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.RowTrans
namespace GlobalTheory.CompanionTheory.TyFin.RowTrans
theorem _root_.solution {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) : ∃ e : V ≃ₗ[K] V, e x = y := by
  have hx1 : (LinearEquiv.toSpanNonzeroSingleton K V x hx).symm
      ⟨x, Submodule.mem_span_singleton_self x⟩ = 1 := by
    rw [LinearEquiv.symm_apply_eq, LinearEquiv.toSpanNonzeroSingleton_one]
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq
    ((LinearEquiv.toSpanNonzeroSingleton K V x hx).symm.trans
      (LinearEquiv.toSpanNonzeroSingleton K V y hy))
  refine ⟨g, ?_⟩
  have h := hg ⟨x, Submodule.mem_span_singleton_self x⟩
  rw [LinearEquiv.trans_apply, hx1, LinearEquiv.toSpanNonzeroSingleton_one] at h
  exact h.symm
end GlobalTheory.CompanionTheory.TyFin.RowTrans
