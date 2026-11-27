-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.surjective_kummerChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:39:05.363744+00:00
-- url     : https://prove2.me/submissions/5dd20383-a85e-4949-b1cb-3616fd95fb98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ToZModPowKummerEqIff
import Theorems.Thm_GlobalTheory_WeilDeligne_toZModPow_kummer_eq_iff
import Theorems.Thm_GlobalTheory_WeilDeligne_continuous_kummerChar
import Theorems.Thm_GlobalTheory_WeilDeligne_surjective_of_isUnit
import Theorems.Thm_GlobalTheory_WeilDeligne_compactSpace_Ine


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
variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.WeilDeligne
theorem _root_.solution (h : IsPlaceOver A w) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (a : Eˣ)
    {σ : G E Ω} (hσ : σ ∈ Ine (F := E) A) (hx : σ (rootOf Ω l (a : E) 1) ≠ rootOf Ω l (a : E) 1) :
    Function.Surjective (kummerChar h hl a) := by
  have := compactSpace_Ine (E := E) A
  refine surjective_of_isUnit (continuous_kummerChar h hl a) (σ := ⟨σ, hσ⟩) ?_
  rw [toAdd_kummerChar, ← IsLocalRing.notMem_maximalIdeal, PadicInt.maximalIdeal_eq_span_p,
    ← pow_one (l : ℤ_[l]), ← PadicInt.ker_toZModPow, RingHom.mem_ker]
  intro h0
  refine hx ((toZModPow_kummer_eq_iff l a σ 1 1).mp ?_)
  rw [h0, kummer_one, map_zero]
end GlobalTheory.WeilDeligne
