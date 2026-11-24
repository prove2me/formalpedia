-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.span_pow_eq_top_of_separable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:01:49.800838+00:00
-- url     : https://prove2.me/submissions/84904823-fc64-4940-9f44-c3f6f5e73315

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfNotPrimary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SpanPowGeneratorEqTopOfCharpolySeparable
import Theorems.Thm_GlobalTheory_CuspGL_irreducible_dvd_of_dvd_charpoly_of_aeval_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr
open GlobalTheory.UnitLemma Polynomial
namespace GlobalTheory.UnitLemma.Unr
theorem _root_.solution (K : UQ) (B : InvAlg K) (hs : B.P.Separable) :
    Submodule.span K.E (Set.range fun i : ℕ => B.g ^ i) = ⊤ := by
  classical
  have hP : B.P ≠ 0 := hs.ne_zero
  have hint : IsIntegral K.E B.g := Algebra.IsIntegral.isIntegral _
  have hz : minpoly K.E B.g ≠ 0 := minpoly.ne_zero hint
  have h0 : aeval (LinearMap.mulLeft K.E B.g) (minpoly K.E B.g) = 0 := by
    have := Polynomial.aeval_algHom_apply (Algebra.lmul K.E B.A) B.g (minpoly K.E B.g)
    rw [minpoly.aeval, map_zero] at this
    exact this
  have hdvd : B.P ∣ minpoly K.E B.g := by
    rw [UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hP hz,
      Multiset.le_iff_subset ((UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hP).1 hs.squarefree)]
    intro p hp
    rw [Polynomial.mem_normalizedFactors_iff hP] at hp
    rw [Polynomial.mem_normalizedFactors_iff hz]
    exact ⟨hp.1, hp.2.1, GlobalTheory.CuspGL.irreducible_dvd_of_dvd_charpoly_of_aeval_eq_zero _ _ _ hp.1 hp.2.2 h0⟩
  have hle : Module.finrank K.E B.A ≤ (minpoly K.E B.g).natDegree := by
    have h1 : B.P.natDegree = Module.finrank K.E B.A := LinearMap.charpoly_natDegree _
    rw [← h1]
    exact natDegree_le_of_dvd hdvd hz
  have hli : LinearIndependent K.E fun i : Fin (minpoly K.E B.g).natDegree => B.g ^ (i : ℕ) :=
    linearIndependent_pow B.g
  have hge := hli.fintype_card_le_finrank
  have htop := hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin] at hge ⊢; omega)
  rw [eq_top_iff, ← htop]
  exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨i, rfl⟩)
end GlobalTheory.UnitLemma.Unr
