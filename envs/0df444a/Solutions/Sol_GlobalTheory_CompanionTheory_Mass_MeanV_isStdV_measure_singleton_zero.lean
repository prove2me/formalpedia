-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Mass.MeanV.isStdV_measure_singleton_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:51:14.039969+00:00
-- url     : https://prove2.me/submissions/86cede90-f57c-4d68-a0ef-ddd8b78012dd

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TsumNeZeroEqSum
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalHaarMeasureSingleton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Mass GlobalTheory.CompanionTheory.Mass.MeanV
namespace GlobalTheory.CompanionTheory.Mass.MeanV
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (lam : Measure (Fv F v)), IsStdV v lam → lam {0} = 0 := by
  intro F _ _ v lam hstd
  obtain ⟨hH, h1⟩ := hstd
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI : CharZero (Fv F v) :=
    charZero_of_injective_algebraMap (algebraMap F (Fv F v)).injective
  have hs : ∀ x : Fv F v, lam {x} = lam {0} := by
    intro x
    rw [← measure_preimage_add lam x ({x} : Set (Fv F v))]
    congr 1
    ext y
    simp
  by_contra h0
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_mul_gt h0 ENNReal.one_ne_top
  have hcard : ((Finset.range N).image (fun n : ℕ => (n : Fv F v))).card = N := by
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
  have hsum : lam (((Finset.range N).image (fun n : ℕ => (n : Fv F v)) : Finset (Fv F v)) : Set (Fv F v))
      = N * lam {0} := by
    rw [← sum_measure_singleton, Finset.sum_congr rfl (fun x _ => hs x), Finset.sum_const, hcard,
      nsmul_eq_mul]
  have hsub : (((Finset.range N).image (fun n : ℕ => (n : Fv F v)) : Finset (Fv F v)) : Set (Fv F v))
      ⊆ (v.adicCompletionIntegers F : Set (Fv F v)) := by
    intro x hx
    simp only [Finset.coe_image, Set.mem_image] at hx
    obtain ⟨n, -, rfl⟩ := hx
    exact natCast_mem (v.adicCompletionIntegers F) n
  have hle := measure_mono (μ := lam) hsub
  rw [hsum, h1] at hle
  exact absurd hN (not_lt.2 hle)
end GlobalTheory.CompanionTheory.Mass.MeanV
