-- Prove2me | solution 1 for HardyCausaloid.fiducial_spanning_states
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T20:01:36.87521+00:00
-- url     : https://prove2.me/submissions/cc2c9d99-0767-49cc-91cb-0fcbc3156669

import Definitions.Def_HardyCausaloid_Fiducial

namespace HardyCausaloid

private theorem sufficient_iff_row_span {A S : Type*} (q : A → S → ℝ) (Ω : Finset A) :
    Sufficient q Ω ↔ ∀ a, q a ∈ Submodule.span ℝ (q '' (Ω : Set A)) := by
  have himg : q '' (Ω : Set A) = Set.range (fun i : Ω => q i.val) := by
    ext v
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, i.property, rfl⟩
  simp_rw [himg, Submodule.mem_span_range_iff_exists_fun ℝ]
  constructor
  · intro h a
    obtain ⟨r, hr⟩ := h a
    refine ⟨r, funext fun s => ?_⟩
    simpa [dotProduct, stateVec, Finset.sum_apply] using (hr s).symm
  · intro h a
    obtain ⟨r, hr⟩ := h a
    refine ⟨r, fun s => ?_⟩
    simpa [dotProduct, stateVec, Finset.sum_apply] using (congrFun hr s).symm

private theorem fiducial_rows_independent {A S : Type*} (q : A → S → ℝ) (Ω : Finset A)
    (hΩ : Fiducial q Ω) : LinearIndependent ℝ (fun i : Ω => q i.val) := by
  classical
  change LinearIndepOn ℝ q (Ω : Set A)
  apply linearIndepOn_iff_notMem_span.mpr
  intro i hi mem
  apply hΩ.2 (Ω.erase i) (Finset.erase_ssubset hi)
  apply (sufficient_iff_row_span q _).2
  have small : q i ∈ Submodule.span ℝ (q '' (↑(Ω.erase i) : Set A)) := by
    simpa only [Finset.coe_erase] using mem
  have le : Submodule.span ℝ (q '' (Ω : Set A)) ≤
      Submodule.span ℝ (q '' (↑(Ω.erase i) : Set A)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, hj, rfl⟩
    by_cases h : j = i
    · subst j
      exact small
    · exact Submodule.subset_span ⟨j, Finset.mem_erase.mpr ⟨h, hj⟩, rfl⟩
  exact fun a => le ((sufficient_iff_row_span q Ω).1 hΩ.1 a)

end HardyCausaloid

open HardyCausaloid

theorem solution {A S : Type*} (q : A → S → ℝ) (Ω : Finset A)
    (hΩ : Fiducial q Ω) :
    Submodule.span ℝ (Set.range (stateVec q Ω)) = ⊤ ∧
    (∃ s : Ω → S, LinearIndependent ℝ (fun l => stateVec q Ω (s l))) ∧
    (∀ α : A, ∃! r : Ω → ℝ, ∀ s : S, q α s = r ⬝ᵥ stateVec q Ω s) := by
  classical
  have hli := fiducial_rows_independent q Ω hΩ
  let e := Pi.basisFun ℝ Ω
  have expand (f : (Ω → ℝ) →ₗ[ℝ] ℝ) (x : Ω → ℝ) :
      f x = ∑ i, x i * f (e i) := by
    conv_lhs => rw [← e.sum_repr x]
    simp [map_sum, e]
  have span : Submodule.span ℝ (Set.range (stateVec q Ω)) = ⊤ := by
    by_contra hn
    obtain ⟨f, hf, hk⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hn)
    have vanish : ∑ i : Ω, f (e i) • q i.val = 0 := by
      ext s
      have zero : f (stateVec q Ω s) = 0 :=
        hk (Submodule.subset_span (Set.mem_range_self s))
      rw [expand] at zero
      simpa [Finset.sum_apply, stateVec, mul_comm] using zero
    have hc := Fintype.linearIndependent_iff.mp hli _ vanish
    apply hf
    apply LinearMap.ext
    intro x
    change f x = 0
    rw [expand]
    simp [hc]
  refine ⟨span, ?_, ?_⟩
  · obtain ⟨κ, a, _, hs, hi⟩ := exists_linearIndependent' ℝ (stateVec q Ω)
    let b := Module.Basis.mk hi (hs.trans span).ge
    let equiv := e.indexEquiv b
    exact ⟨a ∘ equiv, hi.comp equiv equiv.injective⟩
  · intro α
    obtain ⟨r, hr⟩ := hΩ.1 α
    refine ⟨r, hr, ?_⟩
    intro t ht
    apply funext
    apply Fintype.linearIndependent_iffₛ.mp hli t r
    ext s
    simpa [Finset.sum_apply, dotProduct, stateVec] using (ht s).symm.trans (hr s)

