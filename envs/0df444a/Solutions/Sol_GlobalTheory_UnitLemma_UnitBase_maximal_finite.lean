-- Prove2me | solution 1 for GlobalTheory.UnitLemma.UnitBase.maximal_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:01:48.011335+00:00
-- url     : https://prove2.me/submissions/d8407dfd-6902-4e13-88da-7e9a3de9c973

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitBasePointAdjoinTwistedSigma

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.UnitBase
open GlobalTheory.UnitLemma Polynomial
namespace GlobalTheory.UnitLemma.UnitBase
theorem _root_.solution {K : UQ} (B : InvAlg K) (hint : IsIntegral K.O B.g) :
    {M : Ideal (Algebra.adjoin K.O {B.g}) | M.IsMaximal}.Finite := by
  haveI : Module.Finite K.O (Algebra.adjoin K.O {B.g}) := Module.Finite.iff_fg.mpr hint.fg_adjoin_singleton
  refine (Algebra.QuasiFinite.finite_primesOver (IsLocalRing.maximalIdeal K.O)).subset ?_
  intro M hM
  have hM' : M.IsMaximal := hM
  have hc : (M.comap (algebraMap K.O (Algebra.adjoin K.O {B.g}))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
  exact ⟨hM'.isPrime, ⟨(IsLocalRing.eq_maximalIdeal hc).symm⟩⟩
end GlobalTheory.UnitLemma.UnitBase
