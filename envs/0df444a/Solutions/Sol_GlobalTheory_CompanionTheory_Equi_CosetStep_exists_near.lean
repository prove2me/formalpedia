-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Equi.CosetStep.exists_near
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:26:27.32884+00:00
-- url     : https://prove2.me/submissions/2fda7494-be18-403f-a904-641aac01dff8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetCongruenceRefinement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Equi GlobalTheory.CompanionTheory.Equi.CosetStep
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.CompanionTheory.Equi.CosetStep
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) (c : Fv F v) :
    ∃ a : F, algebraMap F (Fv F v) a - c ∈ ballV v k := by
  have hd : DenseRange (algebraMap F (Fv F v)) := HeightOneSpectrum.denseRange_algebraMap F v
  have hval : ∀ t : F, Valued.v (algebraMap F (Fv F v) t) = v.valuation F t := fun t => by
    first
      | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation v t
      | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v t
      | rfl
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer (K := F) v
  have hvp : Valued.v (algebraMap F (Fv F v) (π ^ k)) = WithZero.exp (-(k : ℤ)) := by
    rw [hval, map_pow, hπ, ← WithZero.exp_nsmul, nsmul_eq_mul, mul_neg, mul_one]
  have hp0 : algebraMap F (Fv F v) (π ^ k) ≠ 0 := by
    intro h
    rw [h, map_zero] at hvp
    exact absurd hvp.symm (by simp)
  have hopen : IsOpen {z : Fv F v | Valued.v z ≤ WithZero.exp (-(k : ℤ))} := by
    have h1 := Valued.isOpen_closedBall (R := Fv F v)
      (r := (Valued.v : Valuation (Fv F v) _).restrict (algebraMap F (Fv F v) (π ^ k)))
      ((Valuation.ne_zero_iff _).mpr hp0)
    convert h1 using 2
    funext z
    rw [Valuation.restrict_le_iff, hvp]
  have ho : IsOpen {z : Fv F v | Valued.v (z - c) ≤ WithZero.exp (-(k : ℤ))} :=
    hopen.preimage (continuous_id.sub continuous_const)
  have hmem : {z : Fv F v | Valued.v (z - c) ≤ WithZero.exp (-(k : ℤ))} ∈ 𝓝 c :=
    ho.mem_nhds (by simp)
  obtain ⟨a, ha⟩ := hd.mem_nhds hmem
  exact ⟨a, ha⟩
end GlobalTheory.CompanionTheory.Equi.CosetStep
