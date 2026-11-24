-- Prove2me | solution 1 for GlobalTheory.SelfDualGenus.congr_of_modular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:21:06.352828+00:00
-- url     : https://prove2.me/submissions/4cd815e4-3dbc-46c6-be74-27aba1d6d8ed

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Theorems.Thm_GlobalTheory_SelfDualGenus_IsLocalIsometry_det_div_eq_mul_locConj
import Theorems.Thm_GlobalTheory_SelfDualGenus_congr_of_local_norm
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
theorem _root_.solution (H : Published.Landherr) (H' : Published.HasseNormSt)
    (h𝔟 : 𝔟 ≠ 0) (hc : ∀ z ∈ 𝔟, cc z ∈ 𝔟)
    (hG : ∀ a b, cc (G a b) = G b a) (hG' : ∀ a b, cc (G' a b) = G' b a)
    (hd : G.det ≠ 0) (hd' : G'.det ≠ 0)
    (hL : ReciprocityTheory.MultiplicativeHeights.IsLattice L) (hL' : ReciprocityTheory.MultiplicativeHeights.IsLattice L')
    (hmod : ∀ x, x ∈ L ↔ ∀ y ∈ L, herm G x y ∈ 𝔟) (hmod' : ∀ x, x ∈ L' ↔ ∀ y ∈ L', herm G' x y ∈ 𝔟)
    (hs : ∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
      G'.map τ = Qᵀ * G.map τ * Q.map conj) :
    ∃ P : Matrix (Fin r) (Fin r) E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map cc :=
  congr_of_local_norm H H' hG hG' hd hd' hs fun v => by
    obtain ⟨γ, hγ⟩ := exists_isLocalIsometry_of_modular h𝔟 hc hG hG' hd hd' hL hL' hmod hmod' v
    exact hγ.det_div_eq_mul_locConj hd'
end GlobalTheory.SelfDualGenus
