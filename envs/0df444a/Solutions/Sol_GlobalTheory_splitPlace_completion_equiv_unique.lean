-- Prove2me | solution 1 for GlobalTheory.splitPlace_completion_equiv_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:33:49.246826+00:00
-- url     : https://prove2.me/submissions/9885e543-8279-43cc-92ce-0b6e91348e55

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_SplitPlaceCompletionEquivUnique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open GlobalTheory
open NumberField IsDedekindDomain
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : _root_.ReciprocityTheory.Aut.SplitPlace L)
    (i i' : s.v.adicCompletion (NumberField.maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous i → Continuous i' →
    (∀ x : L, i (s.i x) = algebraMap L (s.w.adicCompletion L) x) → (∀ x : L, i' (s.i x) = algebraMap L (s.w.adicCompletion L) x) →
    i = i' := by
  intro L _ _ _ s i i' hi hi' h h'
  have hd := HeightOneSpectrum.denseRange_algebraMap (K := NumberField.maximalRealSubfield L) s.v
  have key : (i : _ → _) = i' := by
    refine hd.equalizer hi hi' (funext fun a => ?_)
    have ha : algebraMap (NumberField.maximalRealSubfield L) (s.v.adicCompletion (NumberField.maximalRealSubfield L)) a
        = s.i (algebraMap (NumberField.maximalRealSubfield L) L a) := (s.i.commutes a).symm
    simp only [Function.comp_apply, ha, h, h']
  exact RingEquiv.ext (congrFun key)
end _root_.GlobalTheory
end GlobalTheory
