-- Prove2me | solution 1 for MatchingLogic.Pattern.AvoidsBinder.captureFree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:24:17.54981+00:00
-- url     : https://prove2.me/submissions/e65b3d3d-a383-4aba-8968-0c03f47decfb

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Fresh
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CaptureAvoiding

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}
open MatchingLogic.Pattern
open scoped BigOperators
namespace MatchingLogic.Pattern
namespace AvoidsBinder
theorem _root_.solution {y x : Nat} {p : Pattern S Nat}
    (h : AvoidsBinder y p) : CaptureFree x y p := by
  induction p with
  | var z => trivial
  | bot => trivial
  | app sigma args ih => exact fun i => ih i (h i)
  | imp p q ihp ihq => exact ⟨ihp h.1, ihq h.2⟩
  | ex z p ih =>
      by_cases hzx : z = x
      · exact Or.inl hzx
      · exact Or.inr (Or.inr ⟨h.1, ih h.2⟩)
end AvoidsBinder
end MatchingLogic.Pattern
