-- Prove2me | solution 1 for IsAlgClosed.algHom_symmetricPower_equiv_sym
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-25T06:58:12.417906+00:00
-- url     : https://prove2.me/submissions/25040474-cbe0-416e-9b67-3e7543b1b612

import Mathlib
import Definitions.Def_RPLib_F2_009

set_option autoImplicit false

open RamanujanPetersson.JacSym in
theorem solution
    {k : Type*} [Field k] [IsAlgClosed k] {B : Type*} [CommRing B] [Algebra k B] (g : ℕ)
    (S : Subalgebra k (PiTensorProduct k (fun _ : Fin g => B)))
    (hS : ∀ x, x ∈ S ↔ ∀ σ : Equiv.Perm (Fin g), PiTensorProduct.reindex k (fun _ : Fin g => B) σ x = x) :
    ∃ e : (S →ₐ[k] k) ≃ Sym (B →ₐ[k] k) g,
      ∀ ψ : PiTensorProduct k (fun _ : Fin g => B) →ₐ[k] k,
        (e (ψ.comp S.val) : Multiset (B →ₐ[k] k)) =
          Finset.univ.val.map (fun i : Fin g => ψ.comp (PiTensorProduct.singleAlgHom i)) := by
  have hEq : S = SymRing k B g := by
    ext x
    rw [hS, mem_symRing]
    refine forall_congr' fun σ => ?_
    have hlin : (permHom σ : XPow k B g →ₐ[k] XPow k B g).toLinearMap =
        (PiTensorProduct.reindex k (fun _ : Fin g => B) σ).toLinearMap :=
      PiTensorProduct.ext (MultilinearMap.ext fun b => by
        simp [permHom_tprod]; rfl)
    rw [perm_smul_def, show permHom σ x = PiTensorProduct.reindex k (fun _ : Fin g => B) σ x from
      LinearMap.congr_fun hlin x]
  subst hEq
  have hsurj : ∀ (n : ℕ) (s : Sym (B →ₐ[k] k) n), ∃ a : Fin n → (B →ₐ[k] k), mset a = s := by
    intro n s
    obtain ⟨m, hm⟩ := s
    induction m using Quotient.inductionOn with
    | h l =>
      have hl : l.length = n := by simpa using hm
      subst hl
      refine ⟨fun i => l.get i, Sym.coe_injective ?_⟩
      rw [mset_coe, Fin.univ_val_map, List.ofFn_get]
      rfl
  let f : (SymRing k B g →ₐ[k] k) → Sym (B →ₐ[k] k) g := fun φ => mset (liftTuple φ)
  have hf : Function.Bijective f := ⟨fun φ φ' h => by
      rw [← symPt_liftTuple φ, ← symPt_liftTuple φ']
      exact symPt_eq_of_mset_eq _ _ h,
    fun s => by
      obtain ⟨a, rfl⟩ := hsurj g s
      exact ⟨symPt a, mset_eq_of_symPt_eq _ _ (symPt_liftTuple (symPt a))⟩⟩
  refine ⟨Equiv.ofBijective f hf, fun ψ => ?_⟩
  have h2 : ψ.comp (SymRing k B g).val = symPt (ptsEquiv.symm ψ) := by
    rw [symPt, ← ptsEquiv_apply, Equiv.apply_symm_apply]
  rw [h2, Equiv.ofBijective_apply]
  change (mset (liftTuple (symPt (ptsEquiv.symm ψ))) : Multiset (B →ₐ[k] k)) = _
  rw [mset_eq_of_symPt_eq _ _ (symPt_liftTuple (symPt (ptsEquiv.symm ψ))), mset_coe]
  rfl
