-- Prove2me | solution 1 for GlobalTheory.T.mu_cocycle_coboundary_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:19:32.347182+00:00
-- url     : https://prove2.me/submissions/9687b6d2-f4c7-4273-9a33-cf73f517da57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MuCocycleCoboundaryLift
import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__ContinuousCycMod_abd9886c27059cc0
import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MuCocycleCoboundaryLiftStatement
import Theorems.Thm_GlobalTheory_MuTowerInj_mk_eq_zero_of_coboundary


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : LocalTateDuality → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ (n : ℕ) (w : Z2 (muLoc F l 1 A)) (a : Dec (F := F) A → ZMod (l ^ (n + 1))), Continuous a → (∀ g h : Dec (F := F) A, ((cycMod F Ω l (n + 1) g : (ZMod (l ^ (n + 1)))ˣ) : ZMod (l ^ (n + 1))) * a h - a (g * h) + a g = ((l ^ n * (w.1 (g, h)).val : ℕ) : ZMod (l ^ (n + 1)))) → (Submodule.Quotient.mk w : H2 (muLoc F l 1 A)) = 0 := by
  first | exact @GlobalTheory.MuTowerInj.mk_eq_zero_of_coboundary | exact GlobalTheory.MuTowerInj.mk_eq_zero_of_coboundary | (intros; apply GlobalTheory.MuTowerInj.mk_eq_zero_of_coboundary <;> assumption)
end _root_.GlobalTheory.T
