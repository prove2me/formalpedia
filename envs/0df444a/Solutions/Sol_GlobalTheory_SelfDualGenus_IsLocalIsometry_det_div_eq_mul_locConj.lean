-- Prove2me | solution 1 for GlobalTheory.SelfDualGenus.IsLocalIsometry.det_div_eq_mul_locConj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:41:17.110801+00:00
-- url     : https://prove2.me/submissions/09f86e52-60ea-46ee-afb9-68ae165dd4af

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
variable {G G' : Matrix (Fin r) (Fin r) E} {L L' : Submodule (𝓞 E) (Fin r → E)}
namespace GlobalTheory.SelfDualGenus
namespace IsLocalIsometry
theorem _root_.solution {v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))}
    {γ : GL (Fin r) (LocAlg v)} (h : IsLocalIsometry v G L G' L' γ) (hd' : G'.det ≠ 0) :
    ∃ z : LocAlg v, locEmb v (G.det / G'.det) = z * locConj v z := by
  have h1 := congrArg Matrix.det h.1
  rw [UnramifiedHermitian.det_congr, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det, ← RingHom.map_det] at h1
  obtain ⟨z, hz⟩ := ((Matrix.isUnit_iff_isUnit_det _).1 γ.isUnit).exists_left_inv
  have hz' := congrArg (locConj v) hz
  rw [map_mul, map_one] at hz'
  have h2 : locEmb v G'.det * locEmb v G'.det⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hd', map_one]
  refine ⟨z, ?_⟩
  rw [div_eq_mul_inv, map_mul]
  calc locEmb v G.det * locEmb v G'.det⁻¹
      = (z * (γ : Matrix (Fin r) (Fin r) (LocAlg v)).det) *
        (locConj v z * locConj v (γ : Matrix (Fin r) (Fin r) (LocAlg v)).det) *
          locEmb v G.det * locEmb v G'.det⁻¹ := by rw [hz, hz', one_mul, one_mul]
    _ = z * locConj v z * (locEmb v G'.det * locEmb v G'.det⁻¹) := by rw [h1]; ring
    _ = z * locConj v z := by rw [h2, mul_one]
end IsLocalIsometry
end GlobalTheory.SelfDualGenus
