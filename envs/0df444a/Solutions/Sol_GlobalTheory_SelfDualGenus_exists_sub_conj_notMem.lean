-- Prove2me | solution 1 for GlobalTheory.SelfDualGenus.exists_sub_conj_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:12:17.299908+00:00
-- url     : https://prove2.me/submissions/bfcd901a-cf94-4456-80f5-fb673090706f

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing
open scoped Matrix TensorProduct nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LocalLattice
noncomputable section
open GlobalTheory GlobalTheory.SelfDualGenus
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
namespace GlobalTheory.SelfDualGenus
theorem _root_.solution [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] (w : Ideal (𝓞 E))
    (hw : w ≠ ⊤) : ∃ x : 𝓞 E, x - IsCMField.ringOfIntegersComplexConj E x ∉ w := by
  by_contra h
  push Not at h
  have key : (IsCMField.ringOfIntegersComplexConj E).toAlgHom = AlgHom.id (𝓞 (maximalRealSubfield E)) (𝓞 E) :=
    Algebra.FormallyUnramified.ext_of_iInf w (Ideal.iInf_pow_eq_bot_of_isDomain w hw) fun x => by
      rw [eq_comm, Ideal.Quotient.eq]; exact h x
  refine IsCMField.complexConj_ne_one E (AlgEquiv.ext fun x => ?_)
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  have e : ∀ a : 𝓞 E, IsCMField.complexConj E (algebraMap (𝓞 E) E a) = algebraMap (𝓞 E) E a :=
    fun a => congrArg (algebraMap (𝓞 E) E) (DFunLike.congr_fun key a)
  rw [map_div₀, e, e]; rfl
end GlobalTheory.SelfDualGenus
