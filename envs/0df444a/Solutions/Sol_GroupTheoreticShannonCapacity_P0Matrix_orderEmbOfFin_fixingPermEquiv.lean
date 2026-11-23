-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.P0Matrix.orderEmbOfFin_fixingPermEquiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:41:06.126799+00:00
-- url     : https://prove2.me/submissions/8a8bd6ff-a19d-4af9-bdb0-4b1a5385ac0d

import Mathlib.Topology.Instances.Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.P0Matrix
open Matrix Finset
namespace GroupTheoreticShannonCapacity.P0Matrix
theorem _root_.solution (n : ℕ) (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n))
    (hfix : ∀ i ∈ Sᶜ, σ i = i) (j : Fin S.card) :
    S.orderEmbOfFin rfl (fixingPermEquiv n S ⟨σ, hfix⟩ j) = σ (S.orderEmbOfFin rfl j) := by
  have hS_eq : ∀ x, σ x ∈ S ↔ x ∈ S := fun x => (perm_mem_of_fixing n σ S hfix x).symm
  unfold fixingPermEquiv orderEmbEquiv
  simp only [Equiv.trans_apply, Equiv.permCongr_apply, Equiv.symm_symm]
  -- Goal: emb (iso⁻¹ (σ.subtypePerm _ (iso j))) = σ (emb j)
  -- where iso = orderIsoOfFin and emb = orderEmbOfFin
  -- Key: iso⁻¹ ∘ Subtype.val⁻¹ ∘ emb = id, and emb ∘ iso⁻¹ ∘ Subtype.val⁻¹ = Subtype.val
  have hj_mem : S.orderEmbOfFin rfl j ∈ S := S.orderEmbOfFin_mem rfl j
  have hσj_mem : σ (S.orderEmbOfFin rfl j) ∈ S := hS_eq _ |>.mpr hj_mem
  -- The LHS simplifies step by step:
  -- iso j = ⟨emb j, hj_mem⟩ (as subtype)
  -- σ.subtypePerm (iso j) = ⟨σ (emb j), hσj_mem⟩
  -- iso⁻¹ ⟨σ (emb j), hσj_mem⟩ = position of σ (emb j) in S
  -- emb (that position) = σ (emb j)
  -- The key lemma: emb (iso⁻¹ ⟨x, hx⟩) = x for x ∈ S
  have hemb_iso_inv : ∀ (x : Fin n) (hx : x ∈ S),
      S.orderEmbOfFin rfl ((S.orderIsoOfFin rfl).symm ⟨x, hx⟩) = x := by
    intro x hx
    have h := (S.orderIsoOfFin rfl).apply_symm_apply ⟨x, hx⟩
    exact congrArg Subtype.val h
  -- The inner term simplifies to σ.subtypePerm applied to (orderIsoOfFin j)
  -- which gives ⟨σ (orderIsoOfFin j).val, _⟩ = ⟨σ (orderEmbOfFin j), _⟩
  -- Then orderIsoOfFin.symm of that gives the position, and orderEmbOfFin recovers the value
  change S.orderEmbOfFin rfl ((S.orderIsoOfFin rfl).symm
    ⟨σ ((S.orderIsoOfFin rfl j).val), (hS_eq _).mpr (S.orderIsoOfFin rfl j).prop⟩) =
    σ (S.orderEmbOfFin rfl j)
  rw [hemb_iso_inv]
  rfl
end GroupTheoreticShannonCapacity.P0Matrix
