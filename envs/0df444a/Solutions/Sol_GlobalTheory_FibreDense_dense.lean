-- Prove2me | solution 1 for GlobalTheory.FibreDense.dense
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:15:51.136371+00:00
-- url     : https://prove2.me/submissions/0eb090d5-664d-4aff-8a48-435d064d120b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchemeTheoreticallyDominantOfGermInjectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FibreDenseAffineChartPrimesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AnnihilatorAvoidsFibreMinimalPrimesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmoothAlgebraLocalizationEqZeroOfAvoidFibreMinimStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NonZeroDivisorLocalizationGeneralOfNoetherianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HomExtOfAgreeOnFibreDenseOpenSmooth
import Theorems.Thm_GlobalTheory_FibreDense_alg
import Theorems.Thm_GlobalTheory_T_mem_closure_annihilator_primes_inter_fibre
import Theorems.Thm_GlobalTheory_T_schemeTheoreticallyDominant_of_germ_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory GlobalTheory.FibreDense
namespace GlobalTheory.FibreDense
theorem _root_.solution (X T : Scheme.{0}) (p : X ⟶ T) [Smooth p] (W : X.Opens)
    (hW : ∀ x : X, x ∈ closure ((W : Set X) ∩ p ⁻¹' {p x})) : IsSchemeTheoreticallyDominant W.ι := by
  refine GlobalTheory.T.schemeTheoreticallyDominant_of_germ_injective X T p W fun U V hU hV e b hb => ?_
  letI := (p.appLE V U e).hom.toAlgebra
  haveI : Algebra.Smooth Γ(T, V) Γ(X, U) := HasRingHomProperty.appLE @Smooth p ‹_› ⟨V, hV⟩ ⟨U, hU⟩ e
  exact alg Γ(T, V) Γ(X, U) b (GlobalTheory.T.mem_closure_annihilator_primes_inter_fibre X T p W U V hU hV e hW b hb)
end GlobalTheory.FibreDense
