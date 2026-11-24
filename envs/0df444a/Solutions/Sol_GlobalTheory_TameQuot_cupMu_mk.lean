-- Prove2me | solution 1 for GlobalTheory.TameQuot.cupMu_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:12:46.197685+00:00
-- url     : https://prove2.me/submissions/d45a1ca0-70f9-4232-a9c8-4e78dc0720d9

import Mathlib
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__ContinuousCycMod_abd9886c27059cc0

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
open GlobalTheory GlobalTheory.TameQuot
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
namespace GlobalTheory.TameQuot
theorem _root_.solution {A : ValuationSubring Ω} {l : ℕ} [Fact l.Prime] {n : ℕ}
    (z : Z1 (trivDec F A l n)) (y : Z1 (muDec F A l n)) (f : Z2 (muDec F A l n))
    (hf : ∀ g h, f.1 (g, h) = z.1 g * muDec F A l n g (y.1 h)) :
    cupMu F A l n (Submodule.Quotient.mk z) (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk f := by
  obtain rfl : f = cupCocycleZ1Z1 (trivDec F A l n) (muDec F A l n) (muDec F A l n) (LinearMap.mul _ _)
      continuous_of_discreteTopology
      (fun g x y => by
        simp only [Representation.trivial_apply, charRep_apply, LinearMap.mul_apply']
        ring)
      (contAction_muDec A l n) z y := Subtype.ext (funext fun p => hf p.1 p.2)
  rfl
end GlobalTheory.TameQuot
