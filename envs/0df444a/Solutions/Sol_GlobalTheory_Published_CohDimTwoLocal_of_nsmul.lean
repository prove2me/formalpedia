-- Prove2me | solution 1 for GlobalTheory.Published.CohDimTwoLocal.of_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:05:34.302913+00:00
-- url     : https://prove2.me/submissions/228e96aa-7ac9-4d67-b743-917b72176156

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
namespace CohDimTwoLocal
theorem _root_.solution (h : CohDimTwoLocal) (r : ℕ)
    (hM : ∀ m : M, (l ^ r) • m = 0) {v : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω}
    (rho : Representation R (Dec (F := F) A) M)
    (hA : IsPlaceOver A v) (hc : ContAction rho) (n : ℕ) (hn : 3 ≤ n) :
    Subsingleton (Hn rho n) := by
  letI : Module (ZMod (l ^ r)) M := AddCommGroup.zmodModule hM
  exact subsingleton_Hn_of_action_eq rho (zmodRep (l ^ r) rho) (fun _ _ => rfl) n (by omega)
    (h F Ω l r M v A (zmodRep (l ^ r) rho) hA hc n hn)
end CohDimTwoLocal
end GlobalTheory.Published
