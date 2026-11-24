-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Centraliser.exists_aeval_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:13:16.806333+00:00
-- url     : https://prove2.me/submissions/7575adc6-a6b3-4c17-9d2d-2e431eb8b6f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_UniNilp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyDvdPowOfAevalEqZero
import Theorems.Thm_GlobalTheory_UnitLemma_Centraliser_P_dvd_of_aeval_eq_zero
import Theorems.Thm_GlobalTheory_UnitLemma_Centraliser_aeval_g_P

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Centraliser
namespace GlobalTheory.UnitLemma.Centraliser
theorem _root_.solution {K : UQ} (B : InvAlg K) (hsep : B.P.Separable) (y : B.A) :
    ∃ p : K.E[X], aeval B.g p = y := by
  have hm : B.P.Monic := LinearMap.charpoly_monic _
  have hP : eval₂ (↑(Algebra.ofId K.E B.A)) B.g B.P = 0 := aeval_g_P B
  let φ := AdjoinRoot.liftAlgHom B.P (Algebra.ofId K.E B.A) B.g hP
  let pb := AdjoinRoot.powerBasis' hm
  haveI : Module.Finite K.E (AdjoinRoot B.P) := pb.finite
  have hrank : Module.finrank K.E (AdjoinRoot B.P) = Module.finrank K.E B.A := by
    rw [pb.finrank, AdjoinRoot.powerBasis'_dim]
    exact LinearMap.charpoly_natDegree _
  have hinj : Function.Injective φ.toLinearMap := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
    rw [AdjoinRoot.mk_eq_zero]
    apply P_dvd_of_aeval_eq_zero B hsep
    simpa [φ, AdjoinRoot.liftAlgHom_mk, aeval_def] using hz
  obtain ⟨z, hz⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).1 hinj y
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
  exact ⟨p, by simpa [φ, AdjoinRoot.liftAlgHom_mk, aeval_def] using hz⟩
end GlobalTheory.UnitLemma.Centraliser
