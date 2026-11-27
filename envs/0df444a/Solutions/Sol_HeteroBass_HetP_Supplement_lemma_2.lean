-- Prove2me | solution 1 for HeteroBass.HetP.Supplement.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:20:29.278366+00:00
-- url     : https://prove2.me/submissions/1817af7b-93aa-47da-977a-fcc7a013b690

import Mathlib
import Definitions.Def_HeteroBass_HetP_Supplement_Subset

open HeteroBass
open HeteroBass.HetP
open HeteroBass.HetP.Supplement

theorem solution {M : ℕ} (hM : 0 < M) (p : Fin M → ℝ)
    (Q : Fin M → Fin M → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hQ : ∀ k j, k ≠ j → 0 ≤ Q k j)
    (hin : ∀ j, 0 < ∑ k ∈ Finset.univ.erase j, Q k j) :
    (∀ U : Finset (Fin M), U.Nonempty → U ≠ Finset.univ →
      ∀ t : ℝ, 0 ≤ t →
        HasDerivWithinAt (subsetNonadoption p Q U)
          (-((∑ i ∈ U, p i) + ∑ l ∈ Uᶜ, ∑ i ∈ U, Q l i) * subsetNonadoption p Q U t
            + ∑ l ∈ Uᶜ, (∑ i ∈ U, Q l i) * subsetNonadoption p Q (insert l U) t)
          (Set.Ici 0) t) ∧
    (∀ t : ℝ, 0 ≤ t →
      HasDerivWithinAt (subsetNonadoption p Q Finset.univ)
        (-(∑ i, p i) * subsetNonadoption p Q Finset.univ t) (Set.Ici 0) t) ∧
    (∀ U : Finset (Fin M), U.Nonempty → subsetNonadoption p Q U 0 = 1) := by
      classical
      -- the generator acting on a function
      have hG : ∀ (g : Finset (Fin M) → ℝ) (S : Finset (Fin M)),
          ∑ T, generator p Q S T * g T
            = ∑ j ∈ Sᶜ, adoptRate p Q S j * (g (insert j S) - g S) := by
        intro g S
        have hSS : adopterJumpRate p Q S S = 0 := by
          unfold adopterJumpRate
          apply Finset.sum_eq_zero
          intro j hj
          rw [if_neg]
          intro h
          have : j ∈ S := by rw [h]; exact Finset.mem_insert_self j S
          exact (Finset.mem_compl.mp hj) this
        have hsum : ∀ f : Finset (Fin M) → ℝ, ∑ T, adopterJumpRate p Q S T * f T
            = ∑ j ∈ Sᶜ, adoptRate p Q S j * f (insert j S) := by
          intro f
          unfold adopterJumpRate
          simp only [Finset.sum_mul]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          simp [ite_mul]
        have hgen : ∀ T, generator p Q S T = adopterJumpRate p Q S T
            - (if T = S then ∑ U, adopterJumpRate p Q S U else 0) := by
          intro T
          unfold generator finiteJumpGenerator
          by_cases h : S = T
          · subst h
            have : ∀ U, (if U = S then 0 else adopterJumpRate p Q S U) = adopterJumpRate p Q S U := by
              intro U
              split_ifs with hU
              · rw [hU, hSS]
              · rfl
            simp [this, hSS]
          · have h' : ¬ T = S := fun e => h e.symm
            simp [h, h']
        have h1 := hsum (fun _ => 1)
        simp only [mul_one] at h1
        simp only [hgen, sub_mul, Finset.sum_sub_distrib, hsum, h1, mul_sub, ite_mul, zero_mul,
          Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_mul]
      -- general derivative for linear functionals of the transition row
      have hD : ∀ (U : Finset (Fin M)) (t : ℝ),
          HasDerivAt (subsetNonadoption p Q U)
            (∑ S, transition p Q t ∅ S *
              ∑ T, generator p Q S T * (if Disjoint T U then 1 else 0)) t := by
        intro U t
        letI : NormedRing (Matrix (Finset (Fin M)) (Finset (Fin M)) ℝ) := Matrix.linftyOpNormedRing
        letI : NormedAlgebra ℝ (Matrix (Finset (Fin M)) (Finset (Fin M)) ℝ) :=
          Matrix.linftyOpNormedAlgebra
        let L : Matrix (Finset (Fin M)) (Finset (Fin M)) ℝ →ₗ[ℝ] ℝ :=
          { toFun := fun X => ∑ A, X ∅ A * (if Disjoint A U then 1 else 0)
            map_add' := by
              intro X Y
              simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib]
            map_smul' := by
              intro c X
              simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc] }
        have h1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) (generator p Q) t
        have h2 := (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt t h1
        have e1 : subsetNonadoption p Q U = fun s => L (transition p Q s) := by
          funext s
          simp only [subsetNonadoption, L, LinearMap.coe_mk, AddHom.coe_mk, mul_ite, mul_one, mul_zero]
        rw [e1]
        have e2 : (∑ S, transition p Q t ∅ S *
              ∑ T, generator p Q S T * (if Disjoint T U then 1 else 0))
            = L (transition p Q t * generator p Q) := by
          simp only [L, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_apply, Finset.sum_mul,
            Finset.mul_sum]
          rw [Finset.sum_comm]
          simp only [mul_assoc]
        rw [e2]
        exact h2
      have hcomb : ∀ (U S : Finset (Fin M)),
          ∑ T, generator p Q S T * (if Disjoint T U then 1 else 0)
            = -((∑ i ∈ U, p i) + ∑ l ∈ Uᶜ, ∑ i ∈ U, Q l i) * (if Disjoint S U then 1 else 0)
              + ∑ l ∈ Uᶜ, (∑ i ∈ U, Q l i) * (if Disjoint S (insert l U) then 1 else 0) := by
        intro U S
        rw [hG]
        by_cases hSU : Disjoint S U
        · have hUS : U ⊆ Sᶜ := by
            intro x hx
            rw [Finset.mem_compl]
            exact fun h => (Finset.disjoint_left.mp hSU h) hx
          have hSUc : S ⊆ Uᶜ := by
            intro x hx
            rw [Finset.mem_compl]
            exact Finset.disjoint_left.mp hSU hx
          have l1 : ∑ j ∈ Sᶜ, adoptRate p Q S j * ((if Disjoint (insert j S) U then (1:ℝ) else 0)
              - (if Disjoint S U then 1 else 0)) = ∑ j ∈ U, -adoptRate p Q S j := by
            rw [← Finset.sum_subset hUS]
            · apply Finset.sum_congr rfl
              intro j hj
              simp [Finset.disjoint_insert_left, hj, hSU]
            · intro j _ hj
              simp [Finset.disjoint_insert_left, hj, hSU]
          have l2 : ∑ l ∈ Uᶜ, (∑ i ∈ U, Q l i) * (if Disjoint S (insert l U) then (1:ℝ) else 0)
              = ∑ l ∈ Uᶜ, (∑ i ∈ U, Q l i) - ∑ l ∈ S, ∑ i ∈ U, Q l i := by
            have : ∑ l ∈ S, ∑ i ∈ U, Q l i = ∑ l ∈ Uᶜ, if l ∈ S then ∑ i ∈ U, Q l i else 0 := by
              rw [← Finset.sum_filter]
              apply Finset.sum_congr _ (fun _ _ => rfl)
              ext x
              simp only [Finset.mem_filter]
              exact ⟨fun h => ⟨hSUc h, h⟩, fun h => h.2⟩
            rw [this, ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro l _
            by_cases hl : l ∈ S <;> simp [Finset.disjoint_insert_right, hl, hSU]
          rw [l1, l2]
          simp only [adoptRate, hSU, if_true, mul_one, Finset.sum_neg_distrib, Finset.sum_add_distrib]
          rw [Finset.sum_comm (s := U) (t := S)]
          ring
        · simp [Finset.disjoint_insert_left, Finset.disjoint_insert_right, hSU]
      have hmain : ∀ (U : Finset (Fin M)) (t : ℝ),
          HasDerivAt (subsetNonadoption p Q U)
              (-((∑ i ∈ U, p i) + ∑ l ∈ Uᶜ, ∑ i ∈ U, Q l i) * subsetNonadoption p Q U t
                + ∑ l ∈ Uᶜ, (∑ i ∈ U, Q l i) * subsetNonadoption p Q (insert l U) t) t := by
        intro U t
        have h := hD U t
        have hval : ∀ V : Finset (Fin M), subsetNonadoption p Q V t
            = ∑ S, transition p Q t ∅ S * (if Disjoint S V then 1 else 0) := by
          intro V
          simp only [subsetNonadoption, mul_ite, mul_one, mul_zero]
        convert h using 1
        simp only [hcomb, hval, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        · apply Finset.sum_congr rfl
          intro S _
          ring
        · rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro S _
          apply Finset.sum_congr rfl
          intro l _
          ring
      refine ⟨fun U _ _ t _ => (hmain U t).hasDerivWithinAt, fun t _ => ?_, fun U _ => ?_⟩
      · have h := (hmain Finset.univ t).hasDerivWithinAt (s := Set.Ici 0)
        simpa using h
      · have h0 : transition p Q 0 = 1 := by
          unfold transition
          rw [zero_smul]
          exact NormedSpace.exp_zero
        unfold subsetNonadoption
        rw [h0, Finset.sum_eq_single ∅]
        · simp
        · intro A _ hA
          simp [Matrix.one_apply, Ne.symm hA]
        · simp
