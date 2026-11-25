-- Prove2me | solution 1 for GroundTheory.Global.primeIdealZetaSum_primesAbove
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:09:15.462816+00:00
-- url     : https://prove2.me/submissions/4756d1fa-1d2b-4614-88dc-838bed99b5b9

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOneDensity
import Theorems.Thm_GroundTheory_Global_ncard_primesOver_of_splitsCompletely
import Theorems.Thm_GroundTheory_Global_summable_absNorm_rpow_neg_subtype


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain Filter Topology Set Ideal
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L]
  [Algebra K L]
namespace GroundTheory.Global
theorem _root_.solution {T : Set (HeightOneSpectrum (𝓞 K))}
    (hT : ∀ v ∈ T, SplitsCompletely L v) {s : ℝ} (hs : 1 < s) :
    (primesAbove L T).primeIdealZetaSum s = Module.finrank K L * T.primeIdealZetaSum s := by
  classical
  let π : primesAbove L T → T := fun w => ⟨w.1.under (𝓞 K), w.2⟩
  have hlies : ∀ (v : T) (w : {w // π w = v}), w.1.1.asIdeal.LiesOver v.1.asIdeal := by
    intro v w
    refine ⟨?_⟩
    have := congrArg (fun x : T => x.1.asIdeal) w.2
    exact this.symm
  have hnorm : ∀ (v : T) (w : {w // π w = v}),
      (absNorm w.1.1.asIdeal : ℝ) ^ (-s) = (absNorm v.1.asIdeal : ℝ) ^ (-s) := by
    intro v w
    have := hlies v w
    have hf := (hT v.1 v.2 w.1.1 this).2
    rw [← Ideal.absNorm_pow_inertiaDeg v.1.asIdeal w.1.1.asIdeal, hf, pow_one]
  have hcard : ∀ v : T, Nat.card {w // π w = v} = Module.finrank K L := by
    intro v
    rw [← ncard_primesOver_of_splitsCompletely L (hT v.1 v.2), ← Nat.card_coe_set_eq]
    refine Nat.card_eq_of_bijective
      (fun w => (⟨w.1.1.asIdeal, w.1.1.isPrime, hlies v w⟩ : v.1.asIdeal.primesOver (𝓞 L)))
      ⟨?_, ?_⟩
    · intro a b h
      exact Subtype.ext (Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val h)))
    · intro q
      have hq0 : q.1 ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver v.1.ne_bot q.2
      have hu : (⟨q.1, q.2.1, hq0⟩ : HeightOneSpectrum (𝓞 L)).under (𝓞 K) = v.1 :=
        HeightOneSpectrum.ext q.2.2.over.symm
      have hmem : (⟨q.1, q.2.1, hq0⟩ : HeightOneSpectrum (𝓞 L)) ∈ primesAbove L T := by
        show HeightOneSpectrum.under (𝓞 K) ⟨q.1, q.2.1, hq0⟩ ∈ T
        rw [hu]
        exact v.2
      exact ⟨⟨⟨⟨q.1, q.2.1, hq0⟩, hmem⟩, Subtype.ext hu⟩, rfl⟩
  have hfin : ∀ v : T, Finite {w // π w = v} := fun v =>
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Module.finrank_pos.ne')
  have hsumL := summable_absNorm_rpow_neg_subtype (primesAbove L T) hs
  rw [Set.primeIdealZetaSum_def, Set.primeIdealZetaSum_def,
    ← (Equiv.sigmaFiberEquiv π).tsum_eq,
    Summable.tsum_sigma'
      (f := fun p => (absNorm ((Equiv.sigmaFiberEquiv π) p).1.asIdeal : ℝ) ^ (-s))
      (fun v => by have := hfin v; exact Summable.of_finite)
      ((Equiv.sigmaFiberEquiv π).summable_iff.mpr hsumL :),
    ← tsum_mul_left]
  refine tsum_congr fun v => ?_
  have := hfin v
  let _ := Fintype.ofFinite {w // π w = v}
  rw [tsum_fintype]
  calc ∑ w : {w // π w = v}, (absNorm (Equiv.sigmaFiberEquiv π ⟨v, w⟩).1.asIdeal : ℝ) ^ (-s)
      = ∑ _w : {w // π w = v}, (absNorm v.1.asIdeal : ℝ) ^ (-s) :=
        Finset.sum_congr rfl fun w _ => hnorm v w
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hcard, nsmul_eq_mul]
end GroundTheory.Global
