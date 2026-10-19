-- Prove2me | solution 1 for OAI.Barnette.BMatching.data_of_gadget
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T04:27:52.02642+00:00
-- url     : https://prove2.me/submissions/04985be4-1784-4f7a-b901-ba3151360857

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/BMatching.lean:L161-L209
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.BMatching.data_of_gadget. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Bonds
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Quotients
import Definitions.Def_OAI_Combinatorics_Hamiltonian_DiskRegions
import Definitions.Def_OAI_Combinatorics_Hamiltonian_StateDisk
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Circulation
import Definitions.Def_OAI_Combinatorics_Hamiltonian_TriangleSystem
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ColoredDual
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CycleReversal
import Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPhases
import Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPolynomials
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Forest
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Contraction
import Definitions.Def_OAI_Combinatorics_Hamiltonian_MinorDuality
import Definitions.Def_OAI_Combinatorics_Hamiltonian_BMatching

-- ---- from OAI.Combinatorics.Hamiltonian.BMatching ----
namespace OAI

/-! Integral flows, capacitated matchings, and incidence-state pairs. -/

namespace Barnette.BMatching
noncomputable section
open scoped Classical
variable {A B : Type*} [Fintype A] [Fintype B]

end
end Barnette.BMatching
namespace Barnette.BMatching
noncomputable section
open scoped Classical
variable {A B : Type*} [Fintype A] [Fintype B]

omit [Fintype A] [Fintype B] in
lemma data_of_gadget (R : A → B → Prop) (f : Left R ≃ Right R)
    (hf : ∀ l, gadget R l (f l)) : Nonempty (FactorData R) := by
  have hleft : ∀ ak : A × Fin 2, ∃ e : Inc R, f (.inl ak) = .inr e ∧ e.val.1 = ak.1 := by
    intro ak
    have h := hf (.inl ak)
    cases he : f (.inl ak) with
    | inl bk => rw [he] at h; exact h.elim
    | inr e => rw [he] at h; exact ⟨e,rfl,h⟩
  have hright : ∀ bk : B × Fin 2, ∃ e : Inc R, f (.inr e) = .inl bk ∧ e.val.2 = bk.1 := by
    intro bk
    obtain ⟨l,hl⟩ := f.surjective (.inl bk)
    have h := hf l
    rw [hl] at h
    cases l with
    | inl ak => exact h.elim
    | inr e => exact ⟨e,hl,h⟩
  choose l hl hlc using hleft
  choose r hr hrc using hright
  have hli : Function.Injective l := by
    intro a b h
    exact Sum.inl.inj (f.injective ((hl a).trans ((congrArg Sum.inr h).trans (hl b).symm)))
  have hri : Function.Injective r := by
    intro a b h
    exact Sum.inl.inj ((hr a).symm.trans ((congrArg (fun e => f (.inr e)) h).trans (hr b)))
  refine ⟨⟨⟨l,hli⟩,⟨r,hri⟩,fun a k => hlc (a,k),fun b k => hrc (b,k),?_⟩⟩
  ext e
  constructor
  · rintro ⟨ak,rfl⟩
    have h := hf (.inr (l ak))
    cases he : f (.inr (l ak)) with
    | inl bk =>
      exact ⟨bk,Sum.inr.inj (f.injective ((hr bk).trans he.symm))⟩
    | inr d =>
      rw [he] at h
      change l ak = d at h
      have hh : Sum.inl ak = Sum.inr (l ak) := f.injective ((hl ak).trans (by simpa [h] using he.symm))
      cases hh
  · rintro ⟨bk,rfl⟩
    obtain ⟨z,hz⟩ := f.surjective (.inr (r bk))
    have h := hf z
    rw [hz] at h
    cases z with
    | inl ak => exact ⟨ak,Sum.inr.inj ((hl ak).symm.trans hz)⟩
    | inr e =>
      change e = r bk at h
      subst e
      have hh := (hr bk).symm.trans hz
      cases hh

end
end Barnette.BMatching
namespace Barnette.TriangleSystem.State
variable {A V : Type*} {T : TriangleSystem A V} {X : Set V}
end Barnette.TriangleSystem.State

namespace Barnette.Network.ColoredDual
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  {N : Network V E} {D : Network F E} (M : N.ColoredDual D)

end
end Barnette.Network.ColoredDual

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.BMatching
open scoped Classical


theorem solution : type_of% @_root_.OAI.Barnette.BMatching.data_of_gadget := @_root_.OAI.Barnette.BMatching.data_of_gadget
