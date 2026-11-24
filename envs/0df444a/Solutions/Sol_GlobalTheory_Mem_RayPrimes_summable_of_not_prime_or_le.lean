-- Prove2me | solution 1 for GlobalTheory.Mem.RayPrimes.summable_of_not_prime_or_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:16:25.264437+00:00
-- url     : https://prove2.me/submissions/49c1df5b-2d63-40d8-9071-d7e61d85013e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayClassPartialZetaContinuationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProduct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLNonvanishingAtOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InfinitelyManyPrimesInRayClass
import Theorems.Thm_GlobalTheory_Mem_RayPrimes_eq_span_of_not_prime
import Theorems.Thm_GlobalTheory_Mem_PosDirichlet_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
open Filter Topology Asymptotics Set
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.RayPrimes
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.Mem.RayPrimes
theorem _root_.solution (h2 : Module.finrank ℚ K = 2) (N : ℕ) {ι : Type}
    (f : ι → HeightOneSpectrum (𝓞 K)) (hf : Function.Injective f)
    (h : ∀ i, (Ideal.absNorm (f i).asIdeal).Prime → Ideal.absNorm (f i).asIdeal ≤ N) :
    Summable fun i => ((Ideal.absNorm (f i).asIdeal : ℕ) : ℝ)⁻¹ := by
  have hfin : {i | Ideal.absNorm (f i).asIdeal ≤ N}.Finite := by
    have h1 : {I : Ideal (𝓞 K) | Ideal.absNorm I ≤ N}.Finite := Ideal.finite_setOfPred_absNorm_le N
    refine Set.Finite.preimage (f := fun i => (f i).asIdeal) ?_ h1
    intro i _ j _ hij
    exact hf (HeightOneSpectrum.ext hij)
  rw [← hfin.summable_compl_iff]
  have hex : ∀ i : ↥({i | Ideal.absNorm (f i).asIdeal ≤ N}ᶜ : Set ι), ∃ p : ℕ,
      (f i).asIdeal = Ideal.span {(p : 𝓞 K)} ∧ Ideal.absNorm (f i).asIdeal = p ^ 2 :=
    fun i => eq_span_of_not_prime h2 _ fun hp => i.2 (h i hp)
  choose p hp1 hp2 using hex
  have hinj : Function.Injective p := fun i j hij =>
    Subtype.ext (hf (HeightOneSpectrum.ext (by rw [hp1, hp1, hij])))
  have := (Real.summable_nat_pow_inv.2 one_lt_two).comp_injective hinj
  refine this.congr fun i => ?_
  simp [hp2]
end GlobalTheory.Mem.RayPrimes
