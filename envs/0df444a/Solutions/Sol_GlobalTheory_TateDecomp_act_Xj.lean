-- Prove2me | solution 1 for GlobalTheory.TateDecomp.act_Xj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:03:09.274309+00:00
-- url     : https://prove2.me/submissions/cbba31bf-35ee-4e96-8a92-2fa9b8ae3eb5

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
import Theorems.Thm_GlobalTheory_TateDecomp_map_Xj
import Theorems.Thm_GlobalTheory_TateDecomp_gal_Ks
import Theorems.Thm_GlobalTheory_Cyc_IsCyc_continuous


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.TateDecomp
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.TateDecomp
theorem _root_.solution {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (ha : IsActC act)
    {K : FinExt l} {j : ℕ} {g : GQ l} (hg : g ∈ (K0 K).fixingSubgroup) {x : PadicComplex l}
    (hx : x ∈ Xj K j) : act g x ∈ Xj K j := by
  have hc : Continuous ((act g).toRingHom.toAddMonoidHom) :=
    (AddMonoidHomClass.isometry_of_norm _ (ha.2 g)).continuous
  refine map_Xj (act g).toRingHom.toAddMonoidHom hc ?_ hx
  intro i _ ζ w hζ hw
  refine AddSubgroup.subset_closure ⟨act g ζ, act g w, hζ.map_of_injective (act g).injective,
    ⟨?_, by rw [ha.2]; exact hw.2⟩, by simp⟩
  obtain ⟨v, hv, rfl⟩ := hw.1
  exact ⟨g v, gal_Ks hg _ hv, (ha.1 g v).symm⟩
end GlobalTheory.TateDecomp
