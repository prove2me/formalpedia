-- Prove2me | solution 1 for GroundTheory.GroupCoh.tate_natTrans_eq_of_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:49:14.165407+00:00
-- url     : https://prove2.me/submissions/2e07c464-77e0-4cfd-8b53-6be8c77f252c

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CohTrivialBasic
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_TateUnique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits Rep
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
omit [Fintype G]
namespace GroundTheory.GroupCoh
theorem _root_.solution {U V : Type u} [Group U] [Group V] [Fintype U] [Fintype V]
    (E : Rep.{u} k G ⥤ Rep.{u} k U) (E' : Rep.{u} k G ⥤ Rep.{u} k V)
    [E.PreservesZeroMorphisms] [E'.PreservesZeroMorphisms]
    (hE : ∀ {X : ShortComplex (Rep.{u} k G)}, X.ShortExact → (X.map E).ShortExact)
    (hE' : ∀ {X : ShortComplex (Rep.{u} k G)}, X.ShortExact → (X.map E').ShortExact)
    (hEc : ∀ A : Rep.{u} k G, TateAcyclic (E.obj (coindSES.obj A).X₂))
    (hEi : ∀ A : Rep.{u} k G, TateAcyclic (E'.obj (indSES.obj A).X₂))
    (α β : ∀ n : ℤ, E ⋙ tateCohomologyFunctor n ⟶ E' ⋙ tateCohomologyFunctor n)
    (hα : ∀ {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) (n : ℤ),
      TateCohomology.δ (hE hX) n ≫ (α (n + 1)).app X.X₁ =
        (α n).app X.X₃ ≫ TateCohomology.δ (hE' hX) n)
    (hβ : ∀ {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) (n : ℤ),
      TateCohomology.δ (hE hX) n ≫ (β (n + 1)).app X.X₁ =
        (β n).app X.X₃ ≫ TateCohomology.δ (hE' hX) n)
    (h0 : α 0 = β 0) (n : ℤ) : α n = β n := by
  have up : ∀ m : ℤ, α m = β m → α (m + 1) = β (m + 1) := by
    intro m hm
    refine NatTrans.ext (funext fun A => ?_)
    have hX := coindSES_shortExact A
    have : IsIso (TateCohomology.δ (hE hX) m) :=
      isIso_δ_of_tateAcyclic (hE hX) (hEc A) m
    refine (cancel_epi (TateCohomology.δ (hE hX) m)).1 ?_
    exact (hα hX m).trans ((congrArg (fun t => t.app _ ≫ _) hm).trans (hβ hX m).symm)
  have down : ∀ m : ℤ, α (m + 1) = β (m + 1) → α m = β m := by
    intro m hm
    refine NatTrans.ext (funext fun A => ?_)
    have hX := indSES_shortExact A
    have : IsIso (TateCohomology.δ (hE' hX) m) :=
      isIso_δ_of_tateAcyclic (hE' hX) (hEi A) m
    refine (cancel_mono (TateCohomology.δ (hE' hX) m)).1 ?_
    exact (hα hX m).symm.trans ((congrArg (fun t => _ ≫ t.app _) hm).trans (hβ hX m))
  induction n using Int.induction_on with
  | zero => exact h0
  | succ i ih => exact up _ ih
  | pred i ih => exact down _ (by rwa [sub_add_cancel])
end GroundTheory.GroupCoh
