-- Prove2me | solution 1 for GlobalTheory.LatPair.sum_withKer_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:47.600852+00:00
-- url     : https://prove2.me/submissions/5757975c-810e-4f9b-8675-b5248118be78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.LatPair
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (φ : Form k n M)
variable [Fintype n] [DecidableEq n]
namespace GlobalTheory.LatPair
theorem _root_.solution {A : Type*} [AddCommMonoid A] (g : GL n k) (L : Submodule 𝒪[k] (n → k)) (F : Pair k n → A) :
    ∑ P ∈ withKer (g • L), F P = ∑ P ∈ withKer L, F (g • P) :=
  (Finset.sum_equiv (MulAction.toPerm g) (fun P => by simp) fun _ _ => rfl).symm
end GlobalTheory.LatPair
