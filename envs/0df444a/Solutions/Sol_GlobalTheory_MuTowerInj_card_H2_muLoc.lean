-- Prove2me | solution 1 for GlobalTheory.MuTowerInj.card_H2_muLoc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:00:38.943476+00:00
-- url     : https://prove2.me/submissions/f708ccdc-d5d8-4da1-81b5-530e33f2478b

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__ContinuousCycMod_abd9886c27059cc0
import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MuCocycleCoboundaryLift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GlobalTheory GlobalTheory.MuTowerInj
namespace GlobalTheory.MuTowerInj
theorem _root_.solution (hD : LocalTateDuality) (F Ω : Type) [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 F)) (hA : IsPlaceOver A v) (r : ℕ) :
    Nat.card (H2 (muLoc F l r A)) = l ^ r := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  ·
    have : Subsingleton (ZMod (l ^ 0)) := by rw [pow_zero]; infer_instance
    have : Subsingleton (H2 (muLoc F l 0 A)) := ⟨fun x y => by
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact congrArg _ (Subtype.ext (funext fun _ => Subsingleton.elim _ _))⟩
    exact (Nat.card_of_subsingleton (0 : H2 (muLoc F l 0 A))).trans (pow_zero l).symm
  · obtain ⟨⟨e⟩, -⟩ := hD F Ω l r (ZMod (l ^ r)) A (muLoc F l r A) v hr hA
      (GlobalTheory.TameQuot.contAction_muDec A l r)
    exact (Nat.card_congr e.toEquiv).trans (Nat.card_zmod _)
end GlobalTheory.MuTowerInj
