-- Prove2me | solution 1 for GroundTheory.Automorphic.IsSubquotient.exists_piece
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:05:30.047801+00:00
-- url     : https://prove2.me/submissions/41cc5681-74ea-451f-8272-b3cc37a8e354

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteLengthLattice
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteLengthSubquotient
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_exists_ne_zero_of_isIrreducible
import Theorems.Thm_GroundTheory_Automorphic_frobenius_apply
import Theorems.Thm_GroundTheory_Automorphic_frobenius_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Measures.adUnipotentHom_apply
attribute [local simp] GroundTheory.Automorphic.coinvariantsTranslate_mk
attribute [local simp] GroundTheory.Automorphic.frobenius_apply
attribute [local simp] GroundTheory.Automorphic.frobenius_symm_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Function Parabolic
universe u
variable {G : Type*} [Group G] {V W U : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W] [AddCommGroup U] [Module ℂ U]
variable {π : Representation ℂ G W} {ρ : Representation ℂ G V} {θ : Representation ℂ G U}
namespace GroundTheory.Automorphic
namespace IsSubquotient
theorem _root_.solution [π.IsIrreducible] (h : IsSubquotient π ρ) {k : ℕ}
    (Vf : ℕ → Submodule ℂ V) (hV : ∀ i (g : G), Vf i ≤ (Vf i).comap (ρ g)) (h0 : Vf 0 = ⊥)
    (hk : Vf k = ⊤) {X : Fin k → Type*} [∀ j, AddCommGroup (X j)] [∀ j, Module ℂ (X j)]
    (σ : ∀ j, Representation ℂ G (X j))
    (Ψ : ∀ j : Fin k,
      Representation.IntertwiningMap (ρ.subrepresentation (Vf (j + 1)) (hV (j + 1))) (σ j))
    (hΨ : ∀ (j : Fin k) x, Ψ j x = 0 ↔ (x : V) ∈ Vf j) :
    ∃ j, IsSubquotient π (σ j) := by
  classical
  obtain ⟨C, p, hp⟩ := h

  have hex : ∃ j, j < k ∧ ∃ c : C.toSubmodule, (c : V) ∈ Vf (j + 1) ∧ p c ≠ 0 := by
    obtain ⟨x, hx⟩ := exists_ne_zero_of_isIrreducible (ρ := π)
    obtain ⟨c, rfl⟩ := hp x
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [h0] at hk
      have : (c : V) ∈ (⊤ : Submodule ℂ V) := trivial
      rw [← hk, Submodule.mem_bot] at this
      exact hx (by rw [show c = 0 from Subtype.ext this, map_zero])
    refine ⟨k - 1, by omega, c, ?_, hx⟩
    rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0), hk]
    trivial
  let j₀ := Nat.find hex
  obtain ⟨hj₀k, c₀, hc₀V, hc₀⟩ := Nat.find_spec hex
  have hbelow : ∀ c : C.toSubmodule, (c : V) ∈ Vf j₀ → p c = 0 := by
    intro c hc
    rcases Nat.eq_zero_or_pos j₀ with h | h
    · rw [h, h0, Submodule.mem_bot] at hc
      rw [show c = 0 from Subtype.ext hc, map_zero]
    · by_contra hpc
      obtain ⟨m, hm⟩ : ∃ m, j₀ = m + 1 := ⟨j₀ - 1, by omega⟩
      exact Nat.find_min hex (m := m) (by omega) ⟨by omega, c, by rw [← hm]; exact hc, hpc⟩
  set j : Fin k := ⟨j₀, hj₀k⟩

  let D : Subrepresentation (ρ.subrepresentation (Vf (j + 1)) (hV (j + 1))) :=
    ⟨C.toSubmodule.comap (Vf (j + 1)).subtype, fun g x hx => C.apply_mem_toSubmodule g hx⟩
  let toC : D.toSubmodule →ₗ[ℂ] C.toSubmodule :=
    { toFun := fun d => ⟨((d : Vf (j + 1)) : V), d.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let P : D.toSubmodule →ₗ[ℂ] W := p.toLinearMap ∘ₗ toC
  let Q : D.toSubmodule →ₗ[ℂ] X j := (Ψ j).toLinearMap ∘ₗ D.toSubmodule.subtype
  have hker : LinearMap.ker Q ≤ LinearMap.ker P := by
    intro d hd
    have : ((d : Vf (j + 1)) : V) ∈ Vf j₀ := (hΨ j d).1 hd
    exact hbelow _ this

  have hPsurj : Surjective P := by
    let R : Subrepresentation π := ⟨LinearMap.range P, by
      rintro g _ ⟨d, rfl⟩
      refine ⟨(D.toRepresentation g) d, ?_⟩
      show p (toC (D.toRepresentation g d)) = π g (p (toC d))
      rw [← Representation.IntertwiningMap.isIntertwining]
      rfl⟩
    have hR : R ≠ ⊥ := by
      intro hR
      have hmem : P ⟨⟨c₀, hc₀V⟩, c₀.2⟩ ∈ R.toSubmodule := ⟨_, rfl⟩
      rw [hR] at hmem
      exact hc₀ ((Submodule.mem_bot ℂ).1 hmem)
    have := (eq_bot_or_eq_top R).resolve_left hR
    intro y
    have hy : y ∈ R.toSubmodule := by rw [this]; trivial
    exact hy

  let E : Subrepresentation (σ j) := ⟨LinearMap.range Q, by
    rintro g _ ⟨d, rfl⟩
    refine ⟨(D.toRepresentation g) d, ?_⟩
    show Ψ j ((ρ.subrepresentation (Vf (j + 1)) (hV (j + 1)) g) d) = σ j g (Ψ j d)
    exact Representation.IntertwiningMap.isIntertwining _ _ (Ψ j) g d⟩
  let e := Q.quotKerEquivRange
  let lift : LinearMap.range Q →ₗ[ℂ] W :=
    (LinearMap.ker Q).liftQ P hker ∘ₗ e.symm.toLinearMap
  have hlift : ∀ d, lift (Q.rangeRestrict d) = P d := by
    intro d
    simp only [lift, LinearMap.coe_comp, comp_apply, LinearEquiv.coe_coe]
    rw [show Q.rangeRestrict d = e (Submodule.Quotient.mk d) from rfl, LinearEquiv.symm_apply_apply]
    rfl
  refine ⟨j, E, ⟨lift, fun g => LinearMap.ext fun y => ?_⟩, fun y => ?_⟩
  · obtain ⟨d, rfl⟩ := Q.surjective_rangeRestrict y
    have h1 : (E.toRepresentation g (Q.rangeRestrict d) : LinearMap.range Q) =
        Q.rangeRestrict (D.toRepresentation g d) :=
      Subtype.ext (Representation.IntertwiningMap.isIntertwining _ _ (Ψ j) g d).symm
    simp only [LinearMap.coe_comp, comp_apply]
    rw [h1, hlift, hlift]
    show p (toC (D.toRepresentation g d)) = π g (p (toC d))
    rw [← Representation.IntertwiningMap.isIntertwining]
    rfl
  · obtain ⟨d, rfl⟩ := hPsurj y
    exact ⟨Q.rangeRestrict d, hlift d⟩
end IsSubquotient
end GroundTheory.Automorphic
