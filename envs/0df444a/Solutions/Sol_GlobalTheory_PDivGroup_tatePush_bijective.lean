-- Prove2me | solution 1 for GlobalTheory.PDivGroup.tatePush_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:09:24.401465+00:00
-- url     : https://prove2.me/submissions/2764be21-43c4-47fb-8d06-2c280d550a56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FibreRankCompOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Theorems.Thm_GlobalTheory_IsBicharacter_map


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv Module CategoryTheory
open GlobalTheory
open PDiv
open GlobalTheory.PDivGroup
attribute [instance] commRing hopf cocomm finite projective
variable {p : ℕ} {O : Type} [CommRing O]
variable {G H K : PDivGroup p O} {B B' : Type} [CommRing B] [Algebra O B] [CommRing B']
  [Algebra O B']
variable [Fact p.Prime]
variable (G B)
namespace GlobalTheory.PDivGroup
theorem _root_.solution [IsIntegrallyClosedIn O B] :
    Function.Bijective (G.tatePush (Algebra.ofId O B)) := by
  have hi : Function.Injective (Algebra.ofId O B) := IsIntegralClosure.algebraMap_injective O O B
  refine ⟨fun x y h => TateOver.ext (funext fun n => AlgHom.ext fun a =>
    hi (congrArg (fun z => z.pt n a) h)), fun y => ?_⟩
  have hm : ∀ n a, y.pt n a ∈ (Algebra.ofId O B).range := fun n a =>
    IsIntegrallyClosedIn.isIntegral_iff.1 ((Algebra.IsIntegral.isIntegral a).map (y.pt n))
  let e := AlgEquiv.ofInjective _ hi
  let x : ∀ n, G.A n →ₐ[O] O := fun n =>
    (e.symm : (Algebra.ofId O B).range →ₐ[O] O).comp ((y.pt n).codRestrict _ (hm n))
  have hx : ∀ n a, Algebra.ofId O B (x n a) = y.pt n a := fun n a =>
    congrArg Subtype.val (e.apply_symm_apply ⟨y.pt n a, hm n a⟩)
  refine ⟨⟨x, fun n => AlgHom.ext fun a => hi ?_⟩, TateOver.ext (funext fun n => AlgHom.ext (hx n))⟩
  rw [hx, ← y.pt_mulP]
  exact hx _ _
end GlobalTheory.PDivGroup
