-- Prove2me | solution 1 for LocalLemma.exists_good_coloring
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:28:08.666865+00:00
-- url     : https://prove2.me/submissions/a36a4e39-feb4-46f6-aa29-29dd957f8ed0

module
public import Mathlib
public import Definitions.Def_LocalLemmaLib_Coin
public import Definitions.Def_LocalLemmaLib_LocalLemma
public import Theorems.Thm_LocalLemma_lll_symmetric
public import Theorems.Thm_LocalLemma_CoordDep_measurableSet
public import Theorems.Thm_LocalLemma_coin_dependency
public import Theorems.Thm_LocalLemma_coin_mono_le


set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory
open LocalLemma
namespace LocalLemma
theorem _root_.solution {ι : Type*} [Finite ι] {m : ℕ} (D : Fin m → Finset ι)
    (Γ : SimpleGraph (Fin m)) [DecidableRel Γ.Adj]
    (hΓ : ∀ i j, j ≠ i → ¬ Γ.Adj i j → Disjoint (D i) (D j)) {d k : ℕ}
    (hD : ∀ i, k ≤ (D i).card) (hd : ∀ i, Γ.degree i ≤ d)
    (hc : Real.exp 1 * (2 * (1 / 2) ^ k) * (d + 1) ≤ 1) :
    ∃ ω : ι → Bool, ∀ i, ¬ ∃ b, ∀ v ∈ D i, ω v = b := by
  have := Fintype.ofFinite ι
  set A : Fin m → Set (ι → Bool) := fun i => {ω | ∃ b, ∀ v ∈ D i, ω v = b} with hAdef
  have hdep : IsDependencyGraph (coinMeasure ι) A Γ := by
    refine coin_dependency A D (fun i ω ω' h hω => ?_) Γ hΓ
    obtain ⟨b, hb⟩ := hω
    exact ⟨b, fun v hv => (h v hv).symm.trans (hb v hv)⟩
  have hp : ∀ i, (coinMeasure ι).real (A i) ≤ 2 * (1 / 2) ^ k := by
    intro i
    refine (coin_mono_le (D i)).trans ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) (hD i))
      (by norm_num)
  have hpos := lll_symmetric (coinMeasure ι) A (fun _ => (Set.toFinite _).measurableSet) Γ hdep
    hp hd hc
  obtain ⟨ω, hω⟩ : (⋂ i, (A i)ᶜ).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne] at hpos
    simp at hpos
  refine ⟨ω, fun i => ?_⟩
  have := Set.mem_iInter.1 hω i
  exact this
end LocalLemma
