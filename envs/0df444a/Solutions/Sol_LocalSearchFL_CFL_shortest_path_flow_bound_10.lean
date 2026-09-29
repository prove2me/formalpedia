-- Prove2me | solution 1 for LocalSearchFL.CFL.shortest_path_flow_bound_10
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:29:30.118771+00:00
-- url     : https://prove2.me/submissions/6be28d15-aaf6-4465-943f-06e714b78086

import Mathlib
import Definitions.Def_LocalSearchFL_CFL_IsCFLLocalOpt

namespace LocalSearchFL.CFL

/-- Facility–facility distance is bounded through any client. -/
theorem aux_spfb10_cf_le {Cl Fa : Type} (I : MetricInstance Cl Fa) (j : Cl) (a b : Fa) :
    I.cf a b ≤ I.c j a + I.c j b := by
  unfold MetricInstance.cf MetricInstance.c
  have h := I.triangle (Sum.inr a) (Sum.inl j) (Sum.inr b)
  rw [I.symm (Sum.inr a) (Sum.inl j)] at h
  exact h

end LocalSearchFL.CFL

open LocalSearchFL.CFL

theorem solution {Cl Fa : Type} [Fintype Cl]
    (I : MetricInstance Cl Fa) (u : Fa → ℕ) (hu : ∀ i, 0 < u i) (f : Fa → ℝ) (hf : ∀ i, 0 ≤ f i)
    (X O : CFLSol Cl Fa u) (hO : 0 < O.n) :
    ∃ τ : Fin X.n → Fin O.n,
      (∀ s o, I.cf (X.loc s) (O.loc (τ s)) + f (O.loc (τ s)) / (u (O.loc (τ s)) : ℝ) ≤
        I.cf (X.loc s) (O.loc o) + f (O.loc o) / (u (O.loc o) : ℝ)) ∧
      ∑ o, ∑ s ∈ Finset.univ.filter (fun s => τ s = o),
          ((X.nbhd s).card : ℝ) * (I.cf (X.loc s) (O.loc o) + f (O.loc o) / (u (O.loc o) : ℝ)) ≤
        costS I X + costS I O + costF f O := by
  classical
  have : Nonempty (Fin O.n) := ⟨⟨0, hO⟩⟩
  set g : Fin X.n → Fin O.n → ℝ :=
    fun s o => I.cf (X.loc s) (O.loc o) + f (O.loc o) / (u (O.loc o) : ℝ) with hg
  have hex : ∀ s, ∃ o, ∀ o', g s o ≤ g s o' := fun s => by
    obtain ⟨o, -, ho⟩ := Finset.exists_min_image Finset.univ (g s) Finset.univ_nonempty
    exact ⟨o, fun o' => ho o' (Finset.mem_univ _)⟩
  choose τ hτ using hex
  refine ⟨τ, hτ, ?_⟩
  change ∑ o, ∑ s ∈ Finset.univ.filter (fun s => τ s = o), ((X.nbhd s).card : ℝ) * g s o ≤ _
  have h1 : ∑ o, ∑ s ∈ Finset.univ.filter (fun s => τ s = o), ((X.nbhd s).card : ℝ) * g s o
      = ∑ s, ((X.nbhd s).card : ℝ) * g s (τ s) := by
    rw [← Finset.sum_fiberwise Finset.univ τ (fun s => ((X.nbhd s).card : ℝ) * g s (τ s))]
    apply Finset.sum_congr rfl
    intro o _
    apply Finset.sum_congr rfl
    intro s hs
    rw [(Finset.mem_filter.1 hs).2]
  have h2 : ∑ s, ((X.nbhd s).card : ℝ) * g s (τ s) = ∑ j, g (X.σ j) (τ (X.σ j)) := by
    rw [← Finset.sum_fiberwise Finset.univ X.σ (fun j => g (X.σ j) (τ (X.σ j)))]
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.sum_congr rfl (g := fun _ => g s (τ s))]
    · simp [CFLSol.nbhd, Finset.sum_const, nsmul_eq_mul]
    · intro j hj
      rw [(Finset.mem_filter.1 hj).2]
  have h3 : ∀ j, g (X.σ j) (τ (X.σ j)) ≤ I.c j (X.loc (X.σ j)) + I.c j (O.loc (O.σ j)) +
      f (O.loc (O.σ j)) / (u (O.loc (O.σ j)) : ℝ) := by
    intro j
    refine le_trans (hτ (X.σ j) (O.σ j)) ?_
    simp only [hg]
    have := aux_spfb10_cf_le I j (X.loc (X.σ j)) (O.loc (O.σ j))
    linarith
  have h4 : ∑ j, f (O.loc (O.σ j)) / (u (O.loc (O.σ j)) : ℝ) ≤ costF f O := by
    unfold costF
    rw [← Finset.sum_fiberwise Finset.univ O.σ
      (fun j => f (O.loc (O.σ j)) / (u (O.loc (O.σ j)) : ℝ))]
    apply Finset.sum_le_sum
    intro o _
    rw [Finset.sum_congr rfl (g := fun _ => f (O.loc o) / (u (O.loc o) : ℝ))]
    · rw [Finset.sum_const, nsmul_eq_mul]
      have hcap := O.cap o
      have hupos : (0 : ℝ) < (u (O.loc o) : ℝ) := by exact_mod_cast hu (O.loc o)
      have hcap' : ((Finset.univ.filter (fun j => O.σ j = o)).card : ℝ) ≤ (u (O.loc o) : ℝ) := by
        exact_mod_cast hcap
      have hdiv : 0 ≤ f (O.loc o) / (u (O.loc o) : ℝ) := div_nonneg (hf _) hupos.le
      calc ((Finset.univ.filter (fun j => O.σ j = o)).card : ℝ) * (f (O.loc o) / (u (O.loc o) : ℝ))
          ≤ (u (O.loc o) : ℝ) * (f (O.loc o) / (u (O.loc o) : ℝ)) :=
            mul_le_mul_of_nonneg_right hcap' hdiv
        _ = f (O.loc o) := by field_simp
    · intro j hj
      rw [(Finset.mem_filter.1 hj).2]
  rw [h1, h2]
  calc ∑ j, g (X.σ j) (τ (X.σ j))
      ≤ ∑ j, (I.c j (X.loc (X.σ j)) + I.c j (O.loc (O.σ j)) +
          f (O.loc (O.σ j)) / (u (O.loc (O.σ j)) : ℝ)) := Finset.sum_le_sum (fun j _ => h3 j)
    _ = costS I X + costS I O + ∑ j, f (O.loc (O.σ j)) / (u (O.loc (O.σ j)) : ℝ) := by
      unfold costS
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ costS I X + costS I O + costF f O := by linarith
