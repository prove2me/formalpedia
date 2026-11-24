-- Prove2me | solution 1 for GlobalTheory.Published.PoitouTate.toMuLoc_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:13:18.462818+00:00
-- url     : https://prove2.me/submissions/1cd63165-fd4d-4ba1-aa0f-b157f620271d

import Mathlib
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.PoitouTate
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {r : ℕ} (S : Finset (HeightOneSpectrum (𝓞 F)))
  (Av : S → ValuationSubring Ω)
  (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
namespace GlobalTheory.Published.PoitouTate
theorem _root_.solution (hμ : μ.comp (toGS Ω _) = cycMod F Ω l r) (v : S) :
    Function.Bijective (toMuLoc S Av μ hμ v) := by

  have hback : ∀ (g : Dec (F := F) (Av v)) (m : ZMod (l ^ r)),
      (LinearMap.id : ZMod (l ^ r) →ₗ[ZMod (l ^ r)] ZMod (l ^ r)) (muLoc F l r (Av v) g m) =
        ((charRep μ).comp (locFam S Av v)) g
          ((LinearMap.id : ZMod (l ^ r) →ₗ[ZMod (l ^ r)] ZMod (l ^ r)) m) :=
    fun g m => (locFam_apply_eq S Av μ hμ v g m).symm
  refine Function.bijective_iff_has_inverse.mpr
    ⟨mapH2 _ _ LinearMap.id continuous_id hback, fun c => ?_, fun c => ?_⟩
  · exact Submodule.Quotient.induction_on _ c fun z => rfl
  · exact Submodule.Quotient.induction_on _ c fun z => rfl
end GlobalTheory.Published.PoitouTate
