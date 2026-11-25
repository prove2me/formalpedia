-- Prove2me | solution 1 for GlobalTheory.BoxCosetSum.isOpen_boxSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:29:55.194626+00:00
-- url     : https://prove2.me/submissions/b640dc4a-99c1-422f-a8a0-60892bc5b053

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ScalingOpenSubgroupsFinite
import Theorems.Thm_GlobalTheory_BoxCosetSum_isOpen_box
import Theorems.Thm_GlobalTheory_BoxCosetSum_mem_boxSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open GlobalTheory GlobalTheory.BoxCosetSum
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.BoxCosetSum
theorem _root_.solution (κ : Type) [Finite κ] (B : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F))
    (hBo : ∀ v, IsOpen (B v : Set (v.adicCompletion F)))
    (hBO : ∀ v, (B v : Set (v.adicCompletion F)) ⊆ v.adicCompletionIntegers F)
    (hBf : ∀ᶠ v in Filter.cofinite, (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F) :
    IsOpen (boxSub κ B : Set (κ → FiniteAdeleRing (𝓞 F) F)) := by
  have e : (boxSub κ B : Set (κ → FiniteAdeleRing (𝓞 F) F)) =
      ⋂ i, (fun u : κ → FiniteAdeleRing (𝓞 F) F => u i) ⁻¹'
        {x : FiniteAdeleRing (𝓞 F) F | ∀ v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v x ∈ B v} := by
    ext u
    simp only [SetLike.mem_coe, mem_boxSub, Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq]
  rw [e]
  exact isOpen_iInter_of_finite fun i => (isOpen_box B hBo hBO hBf).preimage (continuous_apply i)
end GlobalTheory.BoxCosetSum
