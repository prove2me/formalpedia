-- Prove2me | solution 1 for ModularCurve.UniformizedHeckeCurve.exists_mul_prod_smul_eq_of_forall_mem_support_corr
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/8f10636d-be39-560b-8724-8ea0a32bc14b

import Mathlib
import Definitions.Def_ModularCurve_UniformizedHeckeCurve
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UniformizedHeckeCurve_exists_mul_prod_smul_eq_of_forall_mem_support_corr

set_option autoImplicit false

open scoped MatrixGroups Topology
open ModularCurve

namespace P2mKcHeckeFixedPoint

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {Fc : Type} [Field Fc] [Algebra ℂ Fc]

theorem exists_mem_of_mem_support_sum_map_single {ι : Type*} (m : Multiset (GL (Fin 2) ℝ))
    (g : GL (Fin 2) ℝ → ι) (x : ι)
    (hx : x ∈ ((m.map fun δ => Finsupp.single (g δ) (1 : ℤ)).sum).support) :
    ∃ δ ∈ m, x = g δ := by
  classical
  induction m using Multiset.induction_on with
  | empty => simp at hx
  | cons a m ih =>
      rw [Multiset.map_cons, Multiset.sum_cons] at hx
      rcases Finset.mem_union.mp (Finsupp.support_add hx) with h | h
      · have := Finsupp.support_single_subset h
        rw [Finset.mem_singleton] at this
        exact ⟨a, Multiset.mem_cons_self a m, this⟩
      · obtain ⟨δ, hδ, rfl⟩ := ih h
        exact ⟨δ, Multiset.mem_cons_of_mem hδ, rfl⟩

theorem exists_heckePoint_of_mem_support (U : UniformizedHeckeCurve Γ Fc) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (τ : UpperHalfPlane) (P : AlgebraicCurve.Place ℂ Fc)
    (hP : P ∈ (U.corr ℓ hℓ (Finsupp.single (U.pt τ) 1)).support) :
    ∃ δ ∈ U.heckePoints ℓ hℓ, P = U.pt (δ • τ) := by
  rw [U.corr_single_pt ℓ hℓ τ] at hP
  exact exists_mem_of_mem_support_sum_map_single _ (fun δ => U.pt (δ • τ)) P hP

theorem prod_reverse_ofFn_snoc (e : ℕ) (δ' : Fin e → GL (Fin 2) ℝ) (x : GL (Fin 2) ℝ) :
    (List.ofFn (Fin.snoc δ' x : Fin (e + 1) → GL (Fin 2) ℝ)).reverse.prod = x * (List.ofFn δ').reverse.prod := by
  rw [List.ofFn_succ']
  simp [Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append, List.reverse_append]

theorem exists_heckePoints_pt_prod_smul_eq (U : UniformizedHeckeCurve Γ Fc) :
    ∀ (e : ℕ) (ℓ : Fin e → ℕ) (hℓ : ∀ j, (ℓ j).Prime) (P : Fin (e + 1) → AlgebraicCurve.Place ℂ Fc)
      (τ₀ : UpperHalfPlane), U.pt τ₀ = P 0 →
      (∀ j : Fin e, P j.succ ∈ (U.corr (ℓ j) (hℓ j) (Finsupp.single (P j.castSucc) 1)).support) →
      ∃ δ : Fin e → GL (Fin 2) ℝ, (∀ j, δ j ∈ U.heckePoints (ℓ j) (hℓ j)) ∧
        U.pt (((List.ofFn δ).reverse).prod • τ₀) = P (Fin.last e) := by
  intro e
  induction e with
  | zero =>
      intro ℓ hℓ P τ₀ h0 _
      refine ⟨Fin.elim0, fun j => Fin.elim0 j, ?_⟩
      simpa using h0
  | succ e ih =>
      intro ℓ hℓ P τ₀ h0 hstep

      obtain ⟨δ', hδ', hpt'⟩ := ih (fun j => ℓ j.castSucc) (fun j => hℓ j.castSucc) (fun j => P j.castSucc) τ₀ h0
        (fun j => by simpa [Fin.castSucc_succ] using hstep j.castSucc)

      have hlast := hstep (Fin.last e)
      rw [Fin.succ_last, ← hpt'] at hlast
      obtain ⟨x, hx, hPx⟩ := exists_heckePoint_of_mem_support U _ _ _ _ hlast
      refine ⟨Fin.snoc δ' x, ?_, ?_⟩
      · intro j
        induction j using Fin.lastCases with
        | last => simpa [Fin.snoc_last] using hx
        | cast j => simpa [Fin.snoc_castSucc] using hδ' j
      · rw [prod_reverse_ofFn_snoc, mul_smul, ← hPx]

end P2mKcHeckeFixedPoint

open P2mKcHeckeFixedPoint in
theorem solution
    {Γ : Subgroup (GL (Fin 2) ℝ)} {Fc : Type} [Field Fc] [Algebra ℂ Fc] (U : UniformizedHeckeCurve Γ Fc)
    (e : ℕ) (ℓ : Fin e → ℕ) (hℓ : ∀ j, (ℓ j).Prime) (P : Fin (e + 1) → AlgebraicCurve.Place ℂ Fc)
    (τ₀ : UpperHalfPlane) (h0 : U.pt τ₀ = P 0)
    (hstep : ∀ j : Fin e, P j.succ ∈ (U.corr (ℓ j) (hℓ j) (Finsupp.single (P j.castSucc) 1)).support)
    (hlast : P (Fin.last e) = P 0) :
    ∃ (δ : Fin e → GL (Fin 2) ℝ) (γ : GL (Fin 2) ℝ),
      (∀ j, δ j ∈ U.heckePoints (ℓ j) (hℓ j)) ∧ γ ∈ Γ ∧
      (γ * ((List.ofFn δ).reverse).prod) • τ₀ = τ₀ := by
  obtain ⟨δ, hδ, hpt⟩ := exists_heckePoints_pt_prod_smul_eq U e ℓ hℓ P τ₀ h0 hstep
  rw [hlast, ← h0] at hpt
  obtain ⟨γ, hγ, hfix⟩ := (U.pt_eq_pt_iff _ _).mp hpt
  exact ⟨δ, γ, hδ, hγ, by rw [mul_smul, hfix]⟩

end S_ModularCurve_UniformizedHeckeCurve_exists_mul_prod_smul_eq_of_forall_mem_support_corr
end P2MW
export P2MW.S_ModularCurve_UniformizedHeckeCurve_exists_mul_prod_smul_eq_of_forall_mem_support_corr (solution)
