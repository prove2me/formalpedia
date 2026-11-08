-- Prove2me | solution 1 for HigherComm.higherComm_perm
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-07T07:35:32.785753+00:00
-- url     : https://prove2.me/submissions/f1fe991b-b03d-4213-aef7-f1bd8c93c515

import Definitions.Def_HigherComm_defs
import Theorems.Thm_HigherComm_centralAt_of_centralAt

universe u₁ v₁ w₁

set_option linter.unusedSectionVars false

open FirstOrder FirstOrder.Language

namespace HigherComm
namespace HCPerm

variable {L : FirstOrder.Language.{u₁, v₁}} {M : Type w₁} [L.Structure M]

/-- Congruences with the same relation are equal. -/
theorem cong_ext {φ ψ : Congruence (L := L) M} (h : ∀ x y, φ.r x y ↔ ψ.r x y) : φ = ψ := by
  obtain ⟨⟨r, hr⟩, f1, r1⟩ := φ
  obtain ⟨⟨s, hs⟩, f2, r2⟩ := ψ
  have : r = s := funext fun x => funext fun y => propext (h x y)
  subst this
  rfl

theorem update_comp {K : ℕ} (σ : Equiv.Perm (Fin K)) (F : Fin K → Bool) (j : Fin K) (c : Bool) :
    Function.update F (σ j) c ∘ σ = Function.update (F ∘ σ) j c := by
  funext i
  simp only [Function.comp_apply, Function.update_apply, σ.injective.eq_iff]

/-- Permuting the coordinates of a `T ∘ σ`-matrix gives a `T`-matrix. -/
theorem isTMatrix_perm {K : ℕ} (T : Fin K → Congruence (L := L) M) (σ : Equiv.Perm (Fin K))
    {m : (Fin K → Bool) → M} (hm : IsTMatrix (T ∘ σ) m) :
    IsTMatrix T (fun F => m (F ∘ σ)) := by
  obtain ⟨r, t, a, b, hab, ht⟩ := hm
  let E : (Σ i' : Fin K, Fin (r (σ.symm i'))) ≃ Σ i : Fin K, Fin (r i) :=
    Equiv.sigmaCongrLeft (β := fun i => Fin (r i)) σ.symm
  refine ⟨fun i' => r (σ.symm i'), t.relabel (Sum.map E.symm id),
    fun i' => a (σ.symm i'), fun i' => b (σ.symm i'), fun i' p => ?_, fun F => ?_⟩
  · have := hab (σ.symm i') p
    change (T (σ (σ.symm i'))).r _ _ at this
    rwa [Equiv.apply_symm_apply] at this
  · show m (F ∘ σ) = _
    rw [ht]
    unfold cubeEval
    rw [Term.realize_relabel]
    congr 1
    funext x
    rcases x with x | c
    · obtain ⟨y, rfl⟩ := E.surjective x
      simp only [Function.comp_apply, Sum.map_inl, Equiv.symm_apply_apply, Sum.elim_inl]
      obtain ⟨i', p⟩ := y
      simp [E, Equiv.sigmaCongrLeft_apply]
      rfl
    · rfl

/-- `C(T; σ j; δ) → C(T ∘ σ; j; δ)`. -/
theorem centralAt_comp_perm {K : ℕ} (T : Fin K → Congruence (L := L) M) (σ : Equiv.Perm (Fin K))
    (j : Fin K) (δ : Congruence (L := L) M) (h : CentralAt T (σ j) δ) :
    CentralAt (T ∘ σ) j δ := by
  intro m hm hS
  have key := h _ (isTMatrix_perm T σ hm) (fun F ⟨i', hi', hF⟩ => by
    unfold LineRel
    simp only [update_comp]
    exact hS (F ∘ σ) ⟨σ.symm i', fun hh => hi' (by rw [← hh, Equiv.apply_symm_apply]),
      by simpa using hF⟩)
  unfold PivotRel LineRel at key ⊢
  simp only [update_comp] at key
  exact key

theorem centralAt_comp_perm_iff {K : ℕ} (T : Fin K → Congruence (L := L) M)
    (σ : Equiv.Perm (Fin K)) (j : Fin K) (δ : Congruence (L := L) M) :
    CentralAt (T ∘ σ) j δ ↔ CentralAt T (σ j) δ := by
  refine ⟨fun h => ?_, centralAt_comp_perm T σ j δ⟩
  have := centralAt_comp_perm (T ∘ σ) σ.symm (σ j) δ (by rw [Equiv.symm_apply_apply]; exact h)
  have e : (T ∘ σ) ∘ σ.symm = T := by funext i; simp
  rwa [e] at this

theorem perm_main [L.IsAlgebraic] {n k : ℕ} (m : Fin (n + 1) → L.Term (Fin 4))
    (hm : IsDayTerms M m) (T : Fin (k + 2) → Congruence (L := L) M)
    (σ : Equiv.Perm (Fin (k + 2))) : higherComm (T ∘ σ) = higherComm T := by
  have hc : ∀ δ, CentralAt (T ∘ σ) (Fin.last (k + 1)) δ ↔ CentralAt T (Fin.last (k + 1)) δ := by
    intro δ
    rw [centralAt_comp_perm_iff]
    exact ⟨fun h => centralAt_of_centralAt m hm T δ _ h _,
      fun h => centralAt_of_centralAt m hm T δ _ h _⟩
  apply cong_ext
  intro x y
  exact ⟨fun H δ hδ => H δ ((hc δ).mpr hδ), fun H δ hδ => H δ ((hc δ).mp hδ)⟩

end HCPerm
end HigherComm

theorem solution {L : FirstOrder.Language.{u₁, v₁}} {M : Type w₁} [L.Structure M]
    [L.IsAlgebraic] {n k : ℕ} (m : Fin (n + 1) → L.Term (Fin 4)) (hm : HigherComm.IsDayTerms M m)
    (T : Fin (k + 2) → HigherComm.Congruence (L := L) M) (σ : Equiv.Perm (Fin (k + 2))) :
    HigherComm.higherComm (T ∘ σ) = HigherComm.higherComm T :=
  HigherComm.HCPerm.perm_main m hm T σ
