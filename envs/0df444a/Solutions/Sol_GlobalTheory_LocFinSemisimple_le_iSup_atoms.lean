-- Prove2me | solution 1 for GlobalTheory.LocFinSemisimple.le_iSup_atoms
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:37:45.367575+00:00
-- url     : https://prove2.me/submissions/4af1c3e0-6154-4dce-925b-13b5ec056fdd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegralConjInnerMulInnerOfIsEmptyEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_IsSemisimpleOfLocallyFiniteCompactGroup
import Theorems.Thm_GlobalTheory_LocFinSemisimple_exists_isAtom_le
import Theorems.Thm_GlobalTheory_LocFinSemisimple_isSemisimple_ofInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LocFinSemisimple
variable {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ K V}
variable [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
namespace GlobalTheory.LocFinSemisimple
theorem _root_.solution
    (H : ∀ v : V, ∃ U : Submodule ℂ V, v ∈ U ∧ FiniteDimensional ℂ U ∧ (∀ k, ∀ u ∈ U, ρ k u ∈ U) ∧
      ∀ (ℓ : Module.Dual ℂ V), ∀ u ∈ U, Continuous fun k => ℓ (ρ k u))
    (X : Subrepresentation ρ) :
    X.toSubmodule ≤ ⨆ (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X), S.toSubmodule := by
  set N := ⨆ (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X), S.toSubmodule with hNdef
  have hNX : N ≤ X.toSubmodule := iSup₂_le fun S hS => hS.2
  have hNinv : ∀ k, ∀ x ∈ N, ρ k x ∈ N := by
    intro k
    have : N ≤ N.comap (ρ k) := iSup₂_le fun S hS x hx =>
      (le_iSup₂ (f := fun (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X) => S.toSubmodule) S hS)
        (S.apply_mem_toSubmodule k hx)
    exact fun x hx => this hx
  intro x hxX
  obtain ⟨U, hxU, hfd, hU, hc⟩ := H x
  let R := ofInvariant U hU
  haveI : ComplementedLattice (Subrepresentation R.toRepresentation) :=
    isSemisimple_ofInvariant U hU hfd hc
  let W : Subrepresentation R.toRepresentation :=
    ⟨N.comap U.subtype, fun k w hw => hNinv k _ hw⟩
  obtain ⟨W', hW'⟩ := exists_isCompl W
  have hdis : W.toSubmodule ⊓ W'.toSubmodule = ⊥ :=
    congrArg Subrepresentation.toSubmodule hW'.inf_eq_bot
  have hsup : W.toSubmodule ⊔ W'.toSubmodule = ⊤ :=
    congrArg Subrepresentation.toSubmodule hW'.sup_eq_top
  let Xc : Submodule ℂ U := X.toSubmodule.comap U.subtype
  let Y : Subrepresentation ρ := ⟨(W'.toSubmodule ⊓ Xc).map U.subtype, by
    rintro k _ ⟨u, ⟨hu1, hu2⟩, rfl⟩
    exact ⟨R.toRepresentation k u, ⟨W'.apply_mem_toSubmodule k hu1,
      X.apply_mem_toSubmodule k hu2⟩, rfl⟩⟩
  have hY : Y = ⊥ := by
    by_contra hne
    haveI : FiniteDimensional ℂ Y.toSubmodule := Submodule.finiteDimensional_of_le
      (S₂ := U) (fun y hy => by obtain ⟨u, _, rfl⟩ := Submodule.mem_map.1 hy; exact u.2)
    obtain ⟨T, hT, hTY⟩ := exists_isAtom_le _ Y this rfl hne
    have hTX : T ≤ X := by
      intro t ht
      obtain ⟨u, ⟨_, hu2⟩, rfl⟩ := hTY ht
      exact hu2
    have hTN : T.toSubmodule ≤ N :=
      le_iSup₂ (f := fun (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X) => S.toSubmodule) T ⟨hT, hTX⟩
    have hT0 : T.toSubmodule ≠ ⊥ := fun h => hT.1 (Subrepresentation.toSubmodule_injective h)
    obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hT0
    obtain ⟨u, ⟨hu1, _⟩, rfl⟩ := hTY ht
    have hu : u ∈ W.toSubmodule ⊓ W'.toSubmodule := ⟨hTN ht, hu1⟩
    rw [hdis] at hu
    have hu0 : ((u : R.toSubmodule) : V) = 0 :=
      congrArg Subtype.val ((Submodule.mem_bot ℂ (M := R.toSubmodule) (x := u)).1 hu)
    exact ht0 hu0
  have hx' : (⟨x, hxU⟩ : R.toSubmodule) ∈ W.toSubmodule ⊔ W'.toSubmodule := by rw [hsup]; trivial
  obtain ⟨w, hw, w', hw', hww⟩ := Submodule.mem_sup.1 hx'
  have hsum : (w : V) + (w' : V) = x := congrArg Subtype.val hww
  have hw'X : w' ∈ Xc := by
    have h1 : (w : V) ∈ X.toSubmodule := hNX hw
    have h2 : (w' : V) = x - w := by
      rw [← hsum]; abel
    show (w' : V) ∈ X.toSubmodule
    rw [h2]
    exact X.toSubmodule.sub_mem hxX h1
  have hw'0 : (w' : V) ∈ Y.toSubmodule := ⟨w', ⟨hw', hw'X⟩, rfl⟩
  rw [hY] at hw'0
  have : (w' : V) = 0 := (Submodule.mem_bot ℂ).1 hw'0
  have hxw : x = w := by
    rw [← hsum, ‹(w' : V) = 0›, add_zero]
  rw [hxw]
  exact hw
end GlobalTheory.LocFinSemisimple
