-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.WD.induction_lpSum_twist_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:21:43.704502+00:00
-- url     : https://prove2.me/submissions/44bbc324-b622-4087-8152-8d6b4b9a5f6c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_Mono0OfLpDimEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsAevalEqSmulOnEigenspace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilDeligneInductionPrinciple
import Theorems.Thm_GlobalTheory_WeilDeligne_exists_of_lpSum_twist_finite
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_ind


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
namespace GlobalTheory.WeilDeligne
namespace WD
theorem _root_.solution : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (S : WD h → Prop), (∀ x y, S x → S y → S (x.lpSum y)) → (∀ x y, (∀ σ, x.charPol σ = y.charPol σ) → S x → S y) → (∀ (n : ℕ) (a : WDRep h (Fin n → ℂ)) (μ : Weil h →* ℂˣ) (hμ : IsSmooth μ), (Set.range a.ρ).Finite → S (WD.mk (a.twist μ hμ))) → ∀ x, S x := by
  intro E Ω _ _ _ _ _ A w h S hsum hchar hfin x
  induction x using WD.ind with
  | hP n a =>
  obtain ⟨y, hy, hyc⟩ := exists_of_lpSum_twist_finite S hsum hfin _ (Fin n → ℂ) rfl a.ρ a.smooth
    a.semisimple
  exact hchar y _ (fun σ => by rw [hyc, WD.charPol_mk]) hy
end WD
end GlobalTheory.WeilDeligne
