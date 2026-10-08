-- Prove2me | solution 1 for MechanismDesign.Robust.payoff_types_conditionally_independent
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:40:12.326555+00:00
-- url     : https://prove2.me/submissions/030c1233-ed7a-42f6-93e5-2805a48b0ead

import Mathlib
import Definitions.Def_MechanismDesign_Robust_TypeSpaces

open scoped ENNReal


namespace MechanismDesign.Robust

section ci
open Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
variable {ι : Type} [Fintype ι] [DecidableEq ι] {Θ : ι → Type*} {T : ι → Type*}

theorem ci_join_others (i : ι) (τ : ∀ j, T j) : join i (τ i) (others τ i) = τ := by
  funext j
  by_cases h : j = i
  · subst h; simp [join]
  · simp [join, h, others]

theorem ci_update_eq (i : ι) (σ : ∀ j, T j) (x : T i) :
    Function.update σ i x = join i x (others σ i) := by
  funext j
  by_cases h : j = i
  · subst h; simp [join]
  · simp [join, h, others, Function.update_of_ne h]

theorem pmf_om_ne_top {α : Type*} (μ : PMF α) (S : Set α) : μ.toOuterMeasure S ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (by
    rw [PMF.toOuterMeasure_apply, ← μ.tsum_coe]
    exact ENNReal.tsum_le_tsum fun a => Set.indicator_le_self _ _ a)

theorem ci_core [∀ i, Fintype (T i)] (ts : TypeSpace Θ T)
    (μ : PMF (∀ i, T i)) (hμ : ts.IsCommonPrior μ) (hfull : ∀ τ, μ τ ≠ 0)
    (β : ∀ i, PMF (Others T i)) (hβ : ∀ i, β i ∈ Set.range (ts.β i)) (θ : ∀ i, Θ i) :
    condProb μ {τ | ts.payoff τ = θ} {τ | ts.beliefs τ = β} =
      ∏ i, condProb μ {τ | ts.payoff τ i = θ i} {τ | ts.beliefs τ = β} := by
  -- marginals
  set m : ∀ i, T i → ℝ≥0∞ := fun i a => μ.toOuterMeasure {τ | τ i = a} with hm
  have hne : ∀ i, Nonempty (T i) := ts.nonempty
  have hm0 : ∀ i a, m i a ≠ 0 := by
    intro i a h
    rw [hm] at h
    simp only at h
    rw [PMF.toOuterMeasure_apply_eq_zero_iff] at h
    let τ0 : ∀ j, T j := Function.update (fun j => Classical.arbitrary (T j)) i a
    exact Set.disjoint_left.1 h ((PMF.mem_support_iff _ _).2 (hfull τ0)) (by simp [τ0])
  have hmt : ∀ i a, m i a ≠ ⊤ := fun i a => pmf_om_ne_top _ _
  -- prior factorization
  have hfac : ∀ i (τ : ∀ j, T j), μ τ = ts.β i (τ i) (others τ i) * m i (τ i) := by
    intro i τ
    rw [hμ i (τ i) (hm0 i (τ i)) (others τ i), ci_join_others,
      ENNReal.div_mul_cancel (hm0 i (τ i)) (hmt i (τ i))]
  choose τs hτs using hβ
  set Bf : ∀ i, Finset (T i) := fun i => Finset.univ.filter (fun a => ts.β i a = β i) with hBf
  set Ef : ∀ i, Finset (T i) := fun i => (Bf i).filter (fun a => ts.θhat i a = θ i) with hEf
  have hEB : ∀ i, Ef i ⊆ Bf i := fun i => Finset.filter_subset _ _
  have hτsB : ∀ i, τs i ∈ Bf i := fun i => by simp [hBf, hτs i]
  -- key swap identity
  have hswap : ∀ (σ : ∀ j, T j), (∀ j, σ j ∈ Bf j) → ∀ a (x : T a), x ∈ Bf a →
      μ (Function.update σ a x) * m a (σ a) = μ σ * m a x := by
    intro σ hσ a x hx
    have h1 := hfac a (Function.update σ a x)
    rw [Function.update_self] at h1
    have ho : others (Function.update σ a x) a = others σ a := by
      funext j; simp [others, Function.update_of_ne j.2]
    rw [ho] at h1
    have hb : ts.β a x = ts.β a (σ a) := by
      have h2 := hσ a; simp only [hBf, Finset.mem_filter] at h2 hx; rw [hx.2, h2.2]
    rw [h1, hb, hfac a σ]; ring
  -- product form
  have hprod : ∀ τ : ∀ j, T j, (∀ j, τ j ∈ Bf j) →
      μ τ * ∏ i, m i (τs i) = μ τs * ∏ i, m i (τ i) := by
    intro τ hτ
    have : ∀ s : Finset ι, μ (fun j => if j ∈ s then τ j else τs j) * ∏ i ∈ s, m i (τs i) =
        μ τs * ∏ i ∈ s, m i (τ i) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        have hmix : (fun j => if j ∈ insert a s then τ j else τs j) =
            Function.update (fun j => if j ∈ s then τ j else τs j) a (τ a) := by
          funext j
          by_cases hj : j = a
          · subst hj; simp
          · simp [hj, Function.update_of_ne hj]
        have hσ : ∀ j, (fun j => if j ∈ s then τ j else τs j) j ∈ Bf j := by
          intro j; by_cases hj : j ∈ s <;> simp [hj, hτ j, hτsB j]
        have hsw := hswap _ hσ a (τ a) (hτ a)
        simp only [ha, if_false] at hsw
        rw [Finset.prod_insert ha, Finset.prod_insert ha, hmix]
        calc μ (Function.update (fun j => if j ∈ s then τ j else τs j) a (τ a)) *
              (m a (τs a) * ∏ i ∈ s, m i (τs i))
            = (μ (Function.update (fun j => if j ∈ s then τ j else τs j) a (τ a)) *
              m a (τs a)) * ∏ i ∈ s, m i (τs i) := by ring
          _ = μ (fun j => if j ∈ s then τ j else τs j) * m a (τ a) * ∏ i ∈ s, m i (τs i) := by
              rw [hsw]
          _ = (μ (fun j => if j ∈ s then τ j else τs j) * ∏ i ∈ s, m i (τs i)) * m a (τ a) := by
              ring
          _ = μ τs * (m a (τ a) * ∏ i ∈ s, m i (τ i)) := by rw [ih]; ring
    have h := this Finset.univ
    simpa using h
  set P := ∏ i, m i (τs i) with hP
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hm0 i _
  have hPt : P ≠ ⊤ := ENNReal.prod_ne_top fun i _ => hmt i _
  set K := μ τs / P with hK
  have hform : ∀ τ : ∀ j, T j, (∀ j, τ j ∈ Bf j) → μ τ = K * ∏ i, m i (τ i) := by
    intro τ hτ
    have h := hprod τ hτ
    rw [hK, div_eq_mul_inv, mul_right_comm, ← h, mul_assoc, ENNReal.mul_inv_cancel hP0 hPt,
      mul_one]
  have hmeas : ∀ S : ∀ i, Finset (T i), (∀ i, S i ⊆ Bf i) →
      μ.toOuterMeasure {τ | ∀ i, τ i ∈ S i} = K * ∏ i, ∑ a ∈ S i, m i a := by
    intro S hS
    rw [PMF.toOuterMeasure_apply_fintype, Finset.prod_univ_sum, Finset.mul_sum]
    rw [← Finset.sum_subset (Finset.subset_univ (Fintype.piFinset S))]
    · refine Finset.sum_congr rfl fun τ hτ => ?_
      rw [Fintype.mem_piFinset] at hτ
      rw [Set.indicator_of_mem (by exact hτ), hform τ fun j => hS j (hτ j)]
    · intro τ _ hτ
      rw [Fintype.mem_piFinset] at hτ
      exact Set.indicator_of_notMem (by simpa using hτ) _
  have hK0 : K ≠ 0 := by
    rw [hK]; exact ENNReal.div_ne_zero.2 ⟨hfull τs, hPt⟩
  have hKt : K ≠ ⊤ := by
    rw [hK]; exact ENNReal.div_ne_top (PMF.apply_ne_top _ _) hP0
  -- sets
  have hB : {τ | ts.beliefs τ = β} = {τ : ∀ j, T j | ∀ i, τ i ∈ Bf i} := by
    ext τ; simp [hBf, TypeSpace.beliefs, funext_iff]
  have hE : {τ | ts.payoff τ = θ} ∩ {τ | ts.beliefs τ = β} = {τ : ∀ j, T j | ∀ i, τ i ∈ Ef i} := by
    ext τ; simp [hEf, hBf, TypeSpace.beliefs, TypeSpace.payoff, funext_iff]
    exact ⟨fun h i => ⟨h.2 i, h.1 i⟩, fun h => ⟨fun i => (h i).2, fun i => (h i).1⟩⟩
  have hEi : ∀ i, {τ | ts.payoff τ i = θ i} ∩ {τ | ts.beliefs τ = β} =
      {τ : ∀ j, T j | ∀ j, τ j ∈ Function.update Bf i (Ef i) j} := by
    intro i; ext τ
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, hB]
    constructor
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj; simp [hEf, h2 j]; exact h1
      · rw [Function.update_of_ne hj]; exact h2 j
    · intro h
      refine ⟨?_, fun j => ?_⟩
      · have := h i; simp [hEf] at this; exact this.2
      · by_cases hj : j = i
        · subst hj; have := h j; simp only [Function.update_self] at this; exact hEB j this
        · have := h j; rwa [Function.update_of_ne hj] at this
  set hb : ∀ i, ℝ≥0∞ := fun i => ∑ a ∈ Bf i, m i a with hhb
  set he : ∀ i, ℝ≥0∞ := fun i => ∑ a ∈ Ef i, m i a with hhe
  have hb0 : ∀ i, hb i ≠ 0 := fun i => by
    simp only [hhb]
    intro h
    rw [Finset.sum_eq_zero_iff] at h
    exact hm0 i _ (h _ (hτsB i))
  have hbt : ∀ i, hb i ≠ ⊤ := fun i => ENNReal.sum_ne_top.2 fun a _ => hmt i a
  have het : ∀ i, he i ≠ ⊤ := fun i => ENNReal.sum_ne_top.2 fun a _ => hmt i a
  have hupd : ∀ i, (∀ j, Function.update Bf i (Ef i) j ⊆ Bf j) := by
    intro i j
    by_cases hj : j = i
    · subst hj; simp only [Function.update_self]; exact hEB j
    · rw [Function.update_of_ne hj]
  have hprodupd : ∀ i, ∏ j, ∑ a ∈ Function.update Bf i (Ef i) j, m j a =
      he i * ∏ j ∈ Finset.univ.erase i, hb j := by
    intro i
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    rw [Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  unfold condProb
  rw [hE]
  simp only [hEi]
  rw [hB, hmeas Ef hEB, hmeas Bf (fun _ => le_rfl)]
  simp only [hmeas _ (hupd _), hprodupd]
  -- now real arithmetic via toReal
  have hQ0 : ∏ i, hb i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hb0 i
  have hQt : ∏ i, hb i ≠ ⊤ := ENNReal.prod_ne_top fun i _ => hbt i
  have lhs_ne : (K * ∏ i, he i) / (K * ∏ i, hb i) ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.mul_ne_top hKt (ENNReal.prod_ne_top fun i _ => het i))
      (mul_ne_zero hK0 hQ0)
  have rhs_ne : ∏ i, K * (he i * ∏ j ∈ Finset.univ.erase i, hb j) / (K * ∏ i, hb i) ≠ ⊤ :=
    ENNReal.prod_ne_top fun i _ => ENNReal.div_ne_top (ENNReal.mul_ne_top hKt
      (ENNReal.mul_ne_top (het i) (ENNReal.prod_ne_top fun j _ => hbt j))) (mul_ne_zero hK0 hQ0)
  change (K * ∏ i, he i) / (K * ∏ i, hb i) =
    ∏ i, K * (he i * ∏ j ∈ Finset.univ.erase i, hb j) / (K * ∏ i, hb i)
  rw [← ENNReal.toReal_eq_toReal_iff' lhs_ne rhs_ne]
  simp only [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_prod]
  have hKr : K.toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hK0, hKt⟩
  have hbr : ∀ i, (hb i).toReal ≠ 0 := fun i => ENNReal.toReal_ne_zero.2 ⟨hb0 i, hbt i⟩
  have hsplit : ∀ i, ∏ j, (hb j).toReal = (hb i).toReal * ∏ j ∈ Finset.univ.erase i, (hb j).toReal :=
    fun i => (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  have hfac2 : ∀ i, K.toReal * ((he i).toReal * ∏ j ∈ Finset.univ.erase i, (hb j).toReal) /
      (K.toReal * ∏ j, (hb j).toReal) = (he i).toReal / (hb i).toReal := by
    intro i
    have hpe : ∏ j ∈ Finset.univ.erase i, (hb j).toReal ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun j _ => hbr j
    rw [hsplit i]
    field_simp
  rw [Finset.prod_congr rfl fun i _ => hfac2 i, Finset.prod_div_distrib]
  have hQr : ∏ j, (hb j).toReal ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hbr j
  field_simp

end ci
end MechanismDesign.Robust

open MechanismDesign.Robust


theorem solution {ι : Type} [Fintype ι] [DecidableEq ι]
    {Θ : ι → Type*} {T : ι → Type*} [∀ i, Fintype (T i)] (ts : TypeSpace Θ T)
    (μ : PMF (∀ i, T i)) (hμ : ts.IsCommonPrior μ) (hfull : ∀ τ, μ τ ≠ 0)
    (β : ∀ i, PMF (Others T i)) (hβ : ∀ i, β i ∈ Set.range (ts.β i)) (θ : ∀ i, Θ i) :
    condProb μ {τ | ts.payoff τ = θ} {τ | ts.beliefs τ = β} =
      ∏ i, condProb μ {τ | ts.payoff τ i = θ i} {τ | ts.beliefs τ = β} := by
  exact ci_core ts μ hμ hfull β hβ θ
