-- Prove2me | solution 1 for GlobalTheory.finite_setOf_pow_eq_one_torus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:49:58.538705+00:00
-- url     : https://prove2.me/submissions/7633d189-7d99-48bd-99df-5a556c871e8a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteOfIsClosedTorusZariskiOfPowEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology
open GlobalTheory
open AddMonoidAlgebra
variable {R : Type*} [CommRing R] {X : Type*} [AddCommGroup X]
variable [IsDomain R]
namespace GlobalTheory
theorem _root_.solution [Module.Finite ℤ X] {m : ℕ} (hm : m ≠ 0) :
    {s : Multiplicative X →* Rˣ | s ^ m = 1}.Finite := by
  haveI : NeZero m := ⟨hm⟩
  haveI : AddGroup.FG X := Module.Finite.iff_addGroup_fg.1 inferInstance
  obtain ⟨T, hT⟩ := (Group.fg_def.1 (inferInstance : Group.FG (Multiplicative X)))
  let φ : {s : Multiplicative X →* Rˣ | s ^ m = 1} → (T → rootsOfUnity m R) := fun s x =>
    ⟨s.1 x, by simpa using DFunLike.congr_fun (show s.1 ^ m = 1 from s.2) x.1⟩
  refine Finite.of_injective φ fun s t h => Subtype.ext ?_
  refine MonoidHom.eq_of_eqOn_dense hT fun x hx => ?_
  exact congrArg Subtype.val (congrFun h ⟨x, hx⟩)
end GlobalTheory
