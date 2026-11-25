-- Prove2me | solution 1 for GlobalTheory.Published.CohDimTwoGlobal.of_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:05:30.871811+00:00
-- url     : https://prove2.me/submissions/f3756bad-d342-4488-9cdf-c475cdc69a3d

import Mathlib
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__CohDimTwoLocalOfLocalFiniteness_b2c2e165733ad400
import Theorems.Thm_GlobalTheory_Published_subsingleton_Hn_of_action_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation ReciprocityTheory.Gal Formalism.ConjugateSelfDual
open GlobalTheory GlobalTheory.Published
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  (l : ℕ) [Fact l.Prime] {R : Type*} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Finite M] [TopologicalSpace M] [DiscreteTopology M]
namespace GlobalTheory.Published
namespace CohDimTwoGlobal
theorem _root_.solution (h : CohDimTwoGlobal) [IsTotallyComplex F] (r : ℕ)
    (hM : ∀ m : M, (l ^ r) • m = 0) {S : Finset (HeightOneSpectrum (𝓞 F))}
    (rhoS : Representation R (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
    (hS : ContainsAbove S l) (hc : ContAction rhoS) (n : ℕ) (hn : 3 ≤ n) :
    Subsingleton (Hn rhoS n) := by
  letI : Module (ZMod (l ^ r)) M := AddCommGroup.zmodModule hM
  exact subsingleton_Hn_of_action_eq rhoS (zmodRep (l ^ r) rhoS) (fun _ _ => rfl) n (by omega)
    (h F Ω l r M S (zmodRep (l ^ r) rhoS) hS hc n hn)
end CohDimTwoGlobal
end GlobalTheory.Published
