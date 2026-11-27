-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.exists_isFrobSS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:35:05.339934+00:00
-- url     : https://prove2.me/submissions/435a82f7-8ed5-4e8a-bd50-008820147eb0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ToZModPowKummerEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsFrobeniusSemisimplification
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsNilpotentZpowSubOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsAevalEqSmulOnEigenspace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_CharpolyEqOfIsNilpotentSub
import Theorems.Thm_GlobalTheory_WeilDeligne_isFrobSS_of_unipotent
import Theorems.Thm_GlobalTheory_WeilDeligne_exists_frobenius_semisimplification


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module
open GlobalTheory GlobalTheory.WeilDeligne
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
namespace GlobalTheory.WeilDeligne
theorem _root_.solution (ρ : Representation ℂ (Weil h) V) (N : End ℂ V) (hρ : IsSmooth ρ)
    (hN : IsNilpotent N) (hc : ∀ g, ρ g * N = ((normV w : ℕ) : ℂ) ^ deg g • (N * ρ g)) :
    ∃ a : WDRep h V, IsFrobSS ρ N a := by
  obtain ⟨a, u, h1, h2, -, h3, h4⟩ :=
    exists_frobenius_semisimplification E Ω A w h V ρ N hρ hN hc
  exact ⟨a, h1 ▸ isFrobSS_of_unipotent u h2 h3 h4⟩
end GlobalTheory.WeilDeligne
