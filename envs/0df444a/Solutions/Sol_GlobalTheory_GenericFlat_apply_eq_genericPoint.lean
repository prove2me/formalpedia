-- Prove2me | solution 1 for GlobalTheory.GenericFlat.apply_eq_genericPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:18:26.033812+00:00
-- url     : https://prove2.me/submissions/e5c1d995-54ca-43ca-95df-c72cf030620e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InjectiveOfApplyEqGenericPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.GenericFlat
open AlgebraicGeometry CategoryTheory Limits
namespace GlobalTheory.GenericFlat
namespace _root_.GlobalTheory.GenericFlat
theorem _root_.solution {O : Type} [CommRing O] [IsDomain O]
    {T : Scheme.{0}} (s : T ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O) [Flat s]
    {t : T} (ht : t ∈ genericPoints T) : s t = genericPoint (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O) := by
  obtain ⟨t', hspec, heq⟩ := Flat.generalizingMap s
    ((genericPoint_spec (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O)).specializes (Set.mem_univ (s t)))
  have hsub : closure {t} ⊆ closure {t'} := specializes_iff_closure_subset.mp hspec
  have hcl : closure {t} = closure {t'} :=
    (show closure {t} ∈ irreducibleComponents T from ht).eq_of_le
      isIrreducible_singleton.closure hsub
  have hback : t ⤳ t' := specializes_iff_closure_subset.mpr hcl.ge
  rw [← heq, (hspec.antisymm hback).eq]
end _root_.GlobalTheory.GenericFlat
end GlobalTheory.GenericFlat
