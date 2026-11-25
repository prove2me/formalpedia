-- Prove2me | solution 1 for GlobalTheory.exists_basis_kaehler_of_trdeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:08:46.491797+00:00
-- url     : https://prove2.me/submissions/4a735f2f-7186-40f9-bd05-c8ed6948050b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent
import Theorems.Thm_GlobalTheory_exists_basis_kaehler_uniformiser
import Theorems.Thm_GlobalTheory_trdeg_eq_of_basis_kaehler

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped BigOperators TensorProduct nonZeroDivisors
open Module KaehlerDifferential IsLocalRing
variable (K : Type*) {V : Type*} [Field K] [PerfectField K] [CommRing V] [IsDomain V]
  [IsDiscreteValuationRing V] [Algebra K V] [Algebra.EssFiniteType K V]
  [Algebra.FormallySmooth K V]
variable (F : Type*) [Field F] [Algebra V F] [IsFractionRing V F] [Algebra K F]
  [IsScalarTower K V F]
namespace GlobalTheory
theorem _root_.solution {n : ℕ} (hn : Algebra.trdeg K F = n) {t : V}
    (ht : Irreducible t) :
    ∃ (h : 0 < n) (z : Fin n → V) (b : Basis (Fin n) V Ω[V⁄K]),
      z ⟨0, h⟩ = t ∧ ∀ k, b k = D K V (z k) := by
  obtain ⟨m, z, b, h₀, hb⟩ := exists_basis_kaehler_uniformiser K ht
  have := trdeg_eq_of_basis_kaehler K F b
  rw [hn, Nat.cast_inj] at this
  subst this
  exact ⟨m.succ_pos, z, b, h₀, hb⟩
end GlobalTheory
