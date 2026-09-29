-- Prove2me | solution 1 for MvPowerSeries.subst_sumElim_injective_of_finite_projective_quotient_of_X_pow_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/5ddd5adf-13b4-59e8-a7a9-01ee54d980b4

import Mathlib
import Theorems.Thm_MvPowerSeries_subst_injective_of_finite_projective_quotient_of_X_pow_mem_span
import Theorems.Thm_MvPowerSeries_exists_algEquiv_quotient_sum_tensorProduct_quotient_apply_mk_rename_mul_rename
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPowerSeries_subst_sumElim_injective_of_finite_projective_quotient_of_X_pow_mem_span
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false

open scoped TensorProduct

namespace Ws28K2G3

open MvPowerSeries

variable {B : Type} [CommRing B] {n : ℕ}

noncomputable def rho2 (ρ : Fin n → MvPowerSeries (Fin n) B) : Fin n ⊕ Fin n → MvPowerSeries (Fin n ⊕ Fin n) B :=
  Sum.elim (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) B)) (ρ j))
    (fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) B)) (ρ j))

theorem rho2_inl (ρ : Fin n → MvPowerSeries (Fin n) B) (j : Fin n) :
    rho2 ρ (Sum.inl j) = rename (Sum.inl : Fin n → Fin n ⊕ Fin n) (ρ j) := by
  rw [rename_eq_subst]; rfl

theorem rho2_inr (ρ : Fin n → MvPowerSeries (Fin n) B) (j : Fin n) :
    rho2 ρ (Sum.inr j) = rename (Sum.inr : Fin n → Fin n ⊕ Fin n) (ρ j) := by
  rw [rename_eq_subst]; rfl

theorem range_rho2 (ρ : Fin n → MvPowerSeries (Fin n) B) :
    Set.range (rho2 ρ) = Set.range (fun i => rename (Sum.inl : Fin n → Fin n ⊕ Fin n) (ρ i)) ∪
      Set.range (fun i => rename (Sum.inr : Fin n → Fin n ⊕ Fin n) (ρ i)) := by
  rw [rho2, Set.Sum.elim_range]
  congr 1 <;> (ext x; simp only [Set.mem_range, rename_eq_subst]; rfl)

theorem constantCoeff_rho2 (ρ : Fin n → MvPowerSeries (Fin n) B) (hρ0 : ∀ i, constantCoeff (ρ i) = 0)
    (s : Fin n ⊕ Fin n) : constantCoeff (rho2 ρ s) = 0 := by
  rcases s with j | j
  · show constantCoeff (subst _ (ρ j)) = 0
    exact constantCoeff_subst_eq_zero (HasSubst.X_comp _) (fun l => constantCoeff_X _) (hρ0 j)
  · show constantCoeff (subst _ (ρ j)) = 0
    exact constantCoeff_subst_eq_zero (HasSubst.X_comp _) (fun l => constantCoeff_X _) (hρ0 j)

theorem X_pow_mem_span_rho2 (ρ : Fin n → MvPowerSeries (Fin n) B) {N : ℕ}
    (hN : ∀ i : Fin n, (X i : MvPowerSeries (Fin n) B) ^ N ∈ Ideal.span (Set.range ρ)) (s : Fin n ⊕ Fin n) :
    (X s : MvPowerSeries (Fin n ⊕ Fin n) B) ^ N ∈ Ideal.span (Set.range (rho2 ρ)) := by
  rcases s with i | i
  · have h := Ideal.mem_map_of_mem (rename (Sum.inl : Fin n → Fin n ⊕ Fin n) : MvPowerSeries (Fin n) B →ₐ[B] _).toRingHom (hN i)
    rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_pow, rename_X, Ideal.map_span] at h
    refine Ideal.span_mono ?_ h
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    exact ⟨Sum.inl j, (rho2_inl ρ j)⟩
  · have h := Ideal.mem_map_of_mem (rename (Sum.inr : Fin n → Fin n ⊕ Fin n) : MvPowerSeries (Fin n) B →ₐ[B] _).toRingHom (hN i)
    rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_pow, rename_X, Ideal.map_span] at h
    refine Ideal.span_mono ?_ h
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    exact ⟨Sum.inr j, (rho2_inr ρ j)⟩

end Ws28K2G3

open Ws28K2G3 MvPowerSeries in
theorem solution
    {B : Type} [CommRing B] [IsNoetherianRing B] {n : ℕ} (ρ : Fin n → MvPowerSeries (Fin n) B) (hρ0 : ∀ i, MvPowerSeries.constantCoeff (ρ i) = 0)
    (hN : ∃ N : ℕ, ∀ i : Fin n, (MvPowerSeries.X i : MvPowerSeries (Fin n) B) ^ N ∈ Ideal.span (Set.range ρ))
    (hfin : Module.Finite B (MvPowerSeries (Fin n) B ⧸ Ideal.span (Set.range ρ)))
    (hproj : Module.Projective B (MvPowerSeries (Fin n) B ⧸ Ideal.span (Set.range ρ))) :
(∀ H H' : MvPowerSeries (Fin n ⊕ Fin n) B,
      MvPowerSeries.subst (Sum.elim
          (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) B)) (ρ j))
          (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) B)) (ρ j))) H =
      MvPowerSeries.subst (Sum.elim
          (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) B)) (ρ j))
          (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) B)) (ρ j))) H' → H = H') := by
  classical
  intro H H' h
  change subst (rho2 ρ) H = subst (rho2 ρ) H' at h

  let e : Fin n ⊕ Fin n ≃ Fin (n + n) := finSumFinEquiv
  let R : MvPowerSeries (Fin n ⊕ Fin n) B ≃ₐ[B] MvPowerSeries (Fin (n + n)) B := renameEquiv B e
  have hR : ∀ x, R x = subst (X ∘ e) x := fun x => by
    show rename e x = _; exact rename_eq_subst _ x
  have hρ2 : HasSubst (rho2 ρ) := hasSubst_of_constantCoeff_zero (constantCoeff_rho2 ρ hρ0)
  have hXe : HasSubst (X ∘ e : Fin n ⊕ Fin n → MvPowerSeries (Fin (n + n)) B) := HasSubst.X_comp _

  let ρ'' : Fin (n + n) → MvPowerSeries (Fin (n + n)) B := fun m => R (rho2 ρ (e.symm m))
  have hρ''0 : ∀ m, constantCoeff (ρ'' m) = 0 := fun m => by
    show constantCoeff (R (rho2 ρ (e.symm m))) = 0
    rw [hR]
    exact constantCoeff_subst_eq_zero hXe (fun l => constantCoeff_X _) (constantCoeff_rho2 ρ hρ0 _)
  have hρ'' : HasSubst ρ'' := hasSubst_of_constantCoeff_zero hρ''0

  have key : ∀ G, R (subst (rho2 ρ) G) = subst ρ'' (R G) := by
    intro G
    rw [hR, hR, subst_comp_subst_apply hρ2 hXe, subst_comp_subst_apply hXe hρ'']
    congr 1
    funext s
    show subst (X ∘ e) (rho2 ρ s) = subst ρ'' ((X ∘ ⇑e) s)
    rw [Function.comp_apply, subst_X hρ'']
    show subst (X ∘ e) (rho2 ρ s) = R (rho2 ρ (e.symm (e s)))
    rw [Equiv.symm_apply_apply, hR]

  have hspan : Ideal.span (Set.range ρ'') = (Ideal.span (Set.range (rho2 ρ))).map (R : _ →+* _) := by
    rw [Ideal.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨m, rfl⟩; exact ⟨rho2 ρ (e.symm m), ⟨e.symm m, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨s, rfl⟩, rfl⟩; exact ⟨e s, by show R (rho2 ρ (e.symm (e s))) = R (rho2 ρ s); rw [Equiv.symm_apply_apply]⟩

  obtain ⟨N, hNN⟩ := hN
  have hN'' : ∃ N : ℕ, ∀ m : Fin (n + n), (X m : MvPowerSeries (Fin (n + n)) B) ^ N ∈ Ideal.span (Set.range ρ'') := by
    refine ⟨N, fun m => ?_⟩
    have h1 := X_pow_mem_span_rho2 ρ hNN (e.symm m)
    have h2 := Ideal.mem_map_of_mem (R : MvPowerSeries (Fin n ⊕ Fin n) B →+* MvPowerSeries (Fin (n + n)) B) h1
    rw [map_pow, ← hspan] at h2
    have : (R : MvPowerSeries (Fin n ⊕ Fin n) B →+* MvPowerSeries (Fin (n + n)) B) (X (e.symm m)) = X m := by
      show rename e (X (e.symm m)) = X m
      rw [rename_X, Equiv.apply_symm_apply]
    rwa [this] at h2

  obtain ⟨eQ, -⟩ := MvPowerSeries.exists_algEquiv_quotient_sum_tensorProduct_quotient_apply_mk_rename_mul_rename ρ ⟨N, hNN⟩
  rw [← range_rho2 ρ] at eQ
  let eR : (MvPowerSeries (Fin n ⊕ Fin n) B ⧸ Ideal.span (Set.range (rho2 ρ))) ≃ₐ[B]
      (MvPowerSeries (Fin (n + n)) B ⧸ Ideal.span (Set.range ρ'')) :=
    Ideal.quotientEquivAlg _ _ R hspan
  have hfin'' : Module.Finite B (MvPowerSeries (Fin (n + n)) B ⧸ Ideal.span (Set.range ρ'')) :=
    Module.Finite.equiv (eQ.symm.trans eR).toLinearEquiv
  have hproj'' : Module.Projective B (MvPowerSeries (Fin (n + n)) B ⧸ Ideal.span (Set.range ρ'')) :=
    Module.Projective.of_equiv (eQ.symm.trans eR).toLinearEquiv

  have hRH : R H = R H' := by
    refine MvPowerSeries.subst_injective_of_finite_projective_quotient_of_X_pow_mem_span ρ'' hρ''0 hN'' hfin'' hproj''
      (R H) (R H') ?_
    rw [← key, ← key, h]
  exact R.injective hRH

end S_MvPowerSeries_subst_sumElim_injective_of_finite_projective_quotient_of_X_pow_mem_span
end P2MW
export P2MW.S_MvPowerSeries_subst_sumElim_injective_of_finite_projective_quotient_of_X_pow_mem_span (solution)
