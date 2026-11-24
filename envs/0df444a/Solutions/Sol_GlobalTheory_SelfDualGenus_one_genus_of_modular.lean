-- Prove2me | solution 1 for GlobalTheory.SelfDualGenus.one_genus_of_modular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:21:07.705841+00:00
-- url     : https://prove2.me/submissions/5f19fd90-bfdf-47c6-a47b-6c247d42daf4

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Theorems.Thm_GlobalTheory_SelfDualGenus_finite_setOf_locLattice_ne
import Theorems.Thm_GlobalTheory_SelfDualGenus_isLocalIsometry_one_iff
import Theorems.Thm_GlobalTheory_SelfDualGenus_exists_isLocalIsometry_of_modular

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
variable [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] {𝔟 : FractionalIdeal (𝓞 E)⁰ E}
namespace GlobalTheory.SelfDualGenus
theorem _root_.solution (h𝔟 : 𝔟 ≠ 0) (hc : ∀ z ∈ 𝔟, cc z ∈ 𝔟)
    (hG : ∀ a b, cc (G a b) = G b a) (hd : G.det ≠ 0)
    (hL : ReciprocityTheory.MultiplicativeHeights.IsLattice L) (hL' : ReciprocityTheory.MultiplicativeHeights.IsLattice L')
    (hmod : ∀ x, x ∈ L ↔ ∀ y ∈ L, herm G x y ∈ 𝔟) (hmod' : ∀ x, x ∈ L' ↔ ∀ y ∈ L', herm G x y ∈ 𝔟) :
    ∃ γ : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), GL (Fin r) (LocAlg v),
      (∀ v, IsLocalIsometry v G L G L' (γ v)) ∧ {v | γ v ≠ 1}.Finite := by
  classical
  choose γ hγ using exists_isLocalIsometry_of_modular h𝔟 hc hG hG hd hd hL hL' hmod hmod'
  refine ⟨fun v => if locLattice v L' = locLattice v L then 1 else γ v, fun v => ?_,
    (finite_setOf_locLattice_ne hL' hL).subset fun v hv h => hv (if_pos h)⟩
  beta_reduce
  split_ifs with h
  exacts [(isLocalIsometry_one_iff v).2 h, hγ v]
end GlobalTheory.SelfDualGenus
