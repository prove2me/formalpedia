-- Prove2me | solution 1 for GlobalTheory.CMVal.Conv.summable_norm_rpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:37:22.594847+00:00
-- url     : https://prove2.me/submissions/0da211b0-fce1-48aa-91f9-8fab4447ecf7

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CountableIdealSummableAbsNormRpow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdicCompactDensity_ExistsNatLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemIntegersOfMemHatO
import Theorems.Thm_GlobalTheory_CMVal_Conv_exists_denominator
import Theorems.Thm_GlobalTheory_CMVal_Conv_exists_generator
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_CMVal_out_mem_lattice
import Theorems.Thm_GlobalTheory_countable_ideal_and_summable_absNorm_rpow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Conv
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.Conv
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (y : (Af E)ˣ) (t : ℝ), c ≠ ⊥ → 1 < t → Summable fun q : modUnits (lattice c y) => |(Algebra.norm ℚ (q.1.out : E) : ℝ)| ^ (-t) := by
  intro E _ _ _ c y t _ ht
  obtain ⟨n, hn, hL⟩ := exists_denominator c y
  choose b hb using fun q : modUnits (lattice c y) => hL _ (out_mem_lattice q).1
  obtain ⟨g, hg⟩ := exists_generator (E := E)
  choose u hu using hg
  have hn' : (n : E) ≠ 0 := by exact_mod_cast hn.ne'
  let f : modUnits (lattice c y) → Units.torsion E × Ideal (𝓞 E) :=
    fun q => (IsCMField.unitsMulComplexConjInv E (u (b q)), Ideal.span {b q})
  have hf : Function.Injective f := by
    intro q q' h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    have h3 : u (b q') * (u (b q))⁻¹ ∈ IsCMField.realUnits E := by
      rw [← IsCMField.unitsMulComplexConjInv_ker, MonoidHom.mem_ker, map_mul, map_inv, h1, mul_inv_cancel]
    obtain ⟨v, hv⟩ := (IsCMField.mem_realUnits_iff E _).1 h3
    have h4 : b q' = algebraMap (OF E) (𝓞 E) v * b q := by
      rw [hv]
      have e1 := hu (b q)
      have e2 := hu (b q')
      rw [← h2] at e2
      rw [Units.val_mul]
      linear_combination (-1 : 𝓞 E) * e2 + ((u (b q') : 𝓞 E) * (↑(u (b q))⁻¹ : 𝓞 E)) * e1
        - (g (Ideal.span {b q}) * (u (b q') : 𝓞 E)) * (u (b q)).mul_inv
    have h5 : (q'.1.out : E) = algebraMap (OF E) E v * q.1.out := by
      apply mul_left_cancel₀ hn'
      rw [← hb q', h4, map_mul, hb q, mul_left_comm]; rfl
    apply Subtype.ext
    rw [← Quotient.out_eq q.1, ← Quotient.out_eq q'.1]
    exact Quotient.sound ⟨v, h5⟩
  have hI := ((GlobalTheory.countable_ideal_and_summable_absNorm_rpow E).2 t ht).1
  have hP : Summable fun p : Units.torsion E × Ideal (𝓞 E) => (Ideal.absNorm p.2 : ℝ) ^ (-t) := by
    refine (summable_prod_of_nonneg fun p => Real.rpow_nonneg (Nat.cast_nonneg _) _).2 ⟨fun _ => hI, ?_⟩
    exact Summable.of_finite
  have hN : (0 : ℝ) < |(Algebra.norm ℚ (n : E) : ℝ)| := by
    rw [abs_pos]
    exact_mod_cast (Algebra.norm_ne_zero_iff.2 hn')
  refine ((hP.comp_injective hf).mul_left (|(Algebra.norm ℚ (n : E) : ℝ)| ^ t)).congr fun q => ?_
  have h1 : (Ideal.absNorm (Ideal.span {b q}) : ℝ) =
      |(Algebra.norm ℚ (n : E) : ℝ)| * |(Algebra.norm ℚ (q.1.out : E) : ℝ)| := by
    rw [Ideal.absNorm_span_singleton, ← abs_mul, ← Rat.cast_mul, ← map_mul, ← hb q, Nat.cast_natAbs, Int.cast_abs,
      ← Algebra.coe_norm_int]
    simp
  show _ * (Ideal.absNorm (Ideal.span {b q}) : ℝ) ^ (-t) = _
  rw [h1, Real.mul_rpow hN.le (abs_nonneg _), ← mul_assoc, ← Real.rpow_add hN]
  simp
end GlobalTheory.CMVal.Conv
