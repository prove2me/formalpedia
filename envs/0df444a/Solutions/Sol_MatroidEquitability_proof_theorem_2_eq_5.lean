-- Prove2me | solution 1 for MatroidEquitability.proof_theorem_2_eq_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:07:47.714413+00:00
-- url     : https://prove2.me/submissions/0da8e105-b0f8-4f3f-ad7c-1d755ba596ed

import Mathlib
import Definitions.Def_MatroidEquitability_setWeight
import Definitions.Def_MatroidEquitability_IsPrimalOptimal
import Definitions.Def_MatroidEquitability_dualVector
import Definitions.Def_MatroidEquitability_IsDualOptimal

section
set_option autoImplicit false

namespace MatroidEquitability.Dev.Core

open Finset

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Finite minimax / LP duality for the matrix game `a`. -/
theorem minimax [Nonempty ι] (a : ι → κ → ℝ) :
    ∃ (u : κ → ℝ) (l : ι → ℝ), (∀ e, 0 ≤ u e ∧ u e ≤ 1) ∧ (∀ p, 0 ≤ l p) ∧ ∑ p, l p = 1 ∧
      ∀ p, ∑ e, max 0 (∑ q, l q * a q e) ≤ ∑ e, u e * a p e := by
  classical
  let ev : (κ → ℝ) → ι → ℝ := fun u p => ∑ e, u e * a p e
  have hevc : ∀ p, Continuous fun u : κ → ℝ => ∑ e, u e * a p e := by
    intro p; fun_prop
  let g : (κ → ℝ) → ℝ := fun u => Finset.univ.inf' Finset.univ_nonempty (fun p => ev u p)
  have hg : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro u
    have h := ContinuousAt.finset_inf'_apply (s := (Finset.univ : Finset ι)) (x := u)
      (f := fun p (u : κ → ℝ) => ∑ e, u e * a p e) Finset.univ_nonempty
      (fun p _ => (hevc p).continuousAt)
    exact h
  let K : Set (κ → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (0:ℝ) 1)
  have hK : IsCompact K := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hKne : K.Nonempty := ⟨0, fun e _ => ⟨le_refl _, zero_le_one⟩⟩
  obtain ⟨u0, hu0K, hu0⟩ := hK.exists_isMaxOn hKne hg.continuousOn
  set γ := g u0 with hγ
  have hγ0 : 0 ≤ γ := by
    have := hu0 (show (0 : κ → ℝ) ∈ K from fun e _ => ⟨le_refl _, zero_le_one⟩)
    have h0 : g 0 = 0 := by simp [g, ev]
    simp only [Set.mem_ofPred_eq] at this
    linarith
  have hγle : ∀ p, γ ≤ ∑ e, u0 e * a p e := fun p =>
    Finset.inf'_le (fun p => ev u0 p) (Finset.mem_univ p)
  -- Find l with sum of positive parts ≤ γ
  let y : (ι → ℝ) →ₗ[ℝ] (κ → ℝ) :=
    { toFun := fun l e => ∑ q, l q * a q e
      map_add' := by intro l m; ext e; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by intro c l; ext e; simp [Finset.mul_sum, mul_assoc] }
  have hy : ∀ l e, y l e = ∑ q, l q * a q e := fun l e => rfl
  let P : Set (κ → ℝ) := y '' stdSimplex ℝ ι
  have hPc : IsCompact P := (isCompact_stdSimplex ℝ ι).image y.continuous_of_finiteDimensional
  have hPv : Convex ℝ P := (convex_stdSimplex ℝ ι).linear_image y
  let N : Set (κ → ℝ) := {n | ∑ e, max 0 (n e) ≤ γ}
  have hNc : IsClosed N := isClosed_le (by fun_prop) continuous_const
  have hNv : Convex ℝ N := by
    intro n hn m hm s t hs ht hst
    simp only [N, Set.mem_ofPred_eq] at hn hm ⊢
    calc ∑ e, max 0 ((s • n + t • m) e) ≤ ∑ e, (s * max 0 (n e) + t * max 0 (m e)) := by
          apply Finset.sum_le_sum
          intro e _
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          have h1 := le_max_right 0 (n e)
          have h2 := le_max_right 0 (m e)
          have h3 := le_max_left 0 (n e)
          have h4 := le_max_left 0 (m e)
          apply max_le
          · positivity
          · nlinarith
      _ = s * ∑ e, max 0 (n e) + t * ∑ e, max 0 (m e) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ γ := by nlinarith
  by_cases hex : ∃ z ∈ P, z ∈ N
  · obtain ⟨_, ⟨l, hl, rfl⟩, hz⟩ := hex
    refine ⟨u0, l, fun e => ?_, fun p => hl.1 p, hl.2, fun p => ?_⟩
    · have := hu0K e (Set.mem_univ e); exact this
    · have : ∑ e, max 0 (∑ q, l q * a q e) ≤ γ := hz
      exact this.trans (hγle p)
  exfalso
  have hdisj : Disjoint P N := by
    rw [Set.disjoint_left]; intro z hzP hzN; exact hex ⟨z, hzP, hzN⟩
  obtain ⟨f, s, v, hs, hsv, hv⟩ := geometric_hahn_banach_compact_closed hPv hPc hNv hNc hdisj
  let fl : (κ → ℝ) →ₗ[ℝ] ℝ := f
  have hfx : ∀ x : κ → ℝ, f x = ∑ e, x e * f (fun j => if e = j then 1 else 0) := by
    intro x
    have := LinearMap.pi_apply_eq_sum_univ fl x
    simp only [smul_eq_mul] at this
    exact this
  set c : κ → ℝ := fun e => f (fun j => if e = j then 1 else 0) with hc
  have hsingle : ∀ (e : κ) (t : ℝ), f (fun j => if e = j then t else 0) = t * c e := by
    intro e t
    have := hfx (fun j => if e = j then t else 0)
    rw [this]
    simp [Finset.sum_ite_eq, c, ite_mul]
  have hN0 : ∀ b : κ → ℝ, (∀ j, b j ≤ 0) → b ∈ N := by
    intro b hb
    have : ∑ e, max 0 (b e) = 0 := Finset.sum_eq_zero (fun e _ => max_eq_left (hb e))
    show ∑ e, max 0 (b e) ≤ γ
    rw [this]; exact hγ0
  have hv0 : v < 0 := by
    have := hv 0 (hN0 0 (fun _ => le_refl _))
    simpa using this
  have hcle : ∀ e, c e ≤ 0 := by
    intro e
    by_contra hpos
    push Not at hpos
    set t : ℝ := (-v) / c e + 1 with ht
    have ht0 : 0 ≤ t := by
      have : 0 ≤ (-v) / c e := div_nonneg (by linarith) hpos.le
      linarith
    have hb : (fun j => if e = j then -t else 0) ∈ N := by
      apply hN0
      intro j; split_ifs <;> linarith
    have := hv _ hb
    rw [hsingle] at this
    have h2 : t * c e = -v + c e := by
      rw [ht]; field_simp
    nlinarith
  have hk : ∀ k, γ * (-c k) < -v := by
    intro k
    have hb : (fun j => if k = j then γ else 0) ∈ N := by
      show ∑ e, max 0 ((fun j => if k = j then γ else 0) e) ≤ γ
      have : ∀ e, max 0 ((fun j => if k = j then γ else 0) e) = if k = e then γ else 0 := by
        intro e; by_cases h : k = e <;> simp [h, hγ0]
      simp [this]
    have := hv _ hb
    rw [hsingle] at this
    linarith
  have hP : ∀ l ∈ stdSimplex ℝ ι, ∑ e, y l e * c e < s := by
    intro l hl
    have := hs (y l) ⟨l, hl, rfl⟩
    rwa [hfx] at this
  obtain ⟨p00⟩ := ‹Nonempty ι›
  have hl00 : (Pi.single p00 1 : ι → ℝ) ∈ stdSimplex ℝ ι := single_mem_stdSimplex ℝ p00
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · have := hP _ hl00
    simp at this
    linarith
  obtain ⟨k0, -, hk0⟩ := Finset.exists_max_image Finset.univ (fun e => -c e) Finset.univ_nonempty
  set m : ℝ := -c k0 with hm
  have hmpos : 0 < m := by
    by_contra hneg
    push Not at hneg
    have hall : ∀ e, c e = 0 := by
      intro e
      have := hk0 e (Finset.mem_univ e)
      have := hcle e
      linarith
    have := hP _ hl00
    simp [hall] at this
    linarith
  let ustar : κ → ℝ := fun e => (-c e) / m
  have hustarK : ustar ∈ K := by
    intro e _
    constructor
    · exact div_nonneg (by linarith [hcle e]) hmpos.le
    · rw [div_le_one hmpos]; exact hk0 e (Finset.mem_univ e)
  obtain ⟨p0, -, hp0⟩ := Finset.exists_min_image Finset.univ
    (fun p => ∑ e, ustar e * a p e) Finset.univ_nonempty
  have hl0 : (Pi.single p0 1 : ι → ℝ) ∈ stdSimplex ℝ ι := single_mem_stdSimplex ℝ p0
  have h1 := hP _ hl0
  have hy0 : ∀ e, y (Pi.single p0 1) e = a p0 e := by
    intro e; rw [hy]; simp [Pi.single_apply]
  simp only [hy0] at h1
  have h2 : ∑ e, a p0 e * c e = - m * ∑ e, ustar e * a p0 e := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    simp only [ustar]
    field_simp
  have h3 := hk k0
  have h4 : γ < ∑ e, ustar e * a p0 e := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have h5 : γ < g ustar := by
    apply lt_of_lt_of_le h4
    apply Finset.le_inf'
    intro p _
    exact hp0 p (Finset.mem_univ p)
  have h6 : g ustar ≤ γ := hu0 hustarK
  linarith

end MatroidEquitability.Dev.Core

namespace MatroidEquitability
namespace Dev.Eq5

open Finset

lemma setWeight_eq_sum {α : Type*} {E : Set α} (hE : E.Finite) {A : Set α} (hA : A ⊆ E)
    (f : α → ℝ) : setWeight f A = ∑ e ∈ hE.toFinset, A.indicator f e := by
  unfold setWeight
  rw [finsum_mem_def]
  apply finsum_eq_sum_of_support_subset
  intro e he
  have h1 : e ∈ A := Set.support_indicator_subset he
  simpa using hA h1

lemma setWeight_E {α : Type*} {E : Set α} (hE : E.Finite) (f : α → ℝ) :
    setWeight f E = ∑ e ∈ hE.toFinset, f e := by
  unfold setWeight
  exact finsum_mem_eq_finite_toFinset_sum f hE

lemma indicator_eq {α : Type*} (A : Set α) (f : α → ℝ) (e : α) :
    A.indicator f e = f e * A.indicator (1 : α → ℝ) e := by
  by_cases h : e ∈ A <;> simp [h]

lemma setWeight_sub {α : Type*} {E : Set α} (hE : E.Finite) {B D : Set α} (hB : B ⊆ E)
    (hD : D ⊆ E) (u : α → ℝ) :
    setWeight u B - setWeight u D =
      ∑ e ∈ hE.toFinset, u e * (B.indicator (1 : α → ℝ) e - D.indicator (1 : α → ℝ) e) := by
  rw [setWeight_eq_sum hE hB, setWeight_eq_sum hE hD, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rw [indicator_eq B, indicator_eq D]; ring

lemma weak_sum {α : Type*} {E : Set α} (hE : E.Finite) (Fp Fm : Finset (Set α))
    (hFpE : ∀ B ∈ Fp, B ⊆ E) (hFmE : ∀ D ∈ Fm, D ⊆ E) (u : α → ℝ)
    (lam : Set α → Set α → ℝ) :
    ∑ B ∈ Fp, ∑ D ∈ Fm, lam B D * (setWeight u B - setWeight u D) =
      ∑ e ∈ hE.toFinset, u e * dualVector Fp Fm lam e := by
  have h1 : ∀ B ∈ Fp, ∀ D ∈ Fm, lam B D * (setWeight u B - setWeight u D) =
      ∑ e ∈ hE.toFinset, u e * (lam B D * (B.indicator (1 : α → ℝ) e - D.indicator (1 : α → ℝ) e)) := by
    intro B hB D hD
    rw [setWeight_sub hE (hFpE B hB) (hFmE D hD), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _; ring
  rw [Finset.sum_congr rfl (fun B hB => Finset.sum_congr rfl (fun D hD => h1 B hB D hD))]
  unfold dualVector
  simp only [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun B _ => Finset.sum_comm)]
  exact Finset.sum_comm


lemma slack_identity {α : Type*} {E : Set α} (hE : E.Finite) (Fp Fm : Finset (Set α))
    (hFpE : ∀ B ∈ Fp, B ⊆ E) (hFmE : ∀ D ∈ Fm, D ⊆ E) (u : α → ℝ) (γ : ℝ)
    (lam : Set α → Set α → ℝ) (x : α → ℝ) (hsum : ∑ B ∈ Fp, ∑ D ∈ Fm, lam B D = 1) :
    ∑ e ∈ hE.toFinset, x e - γ =
      ∑ B ∈ Fp, ∑ D ∈ Fm, lam B D * (setWeight u B - setWeight u D - γ) +
      ∑ e ∈ hE.toFinset, u e * (x e - dualVector Fp Fm lam e) +
      ∑ e ∈ hE.toFinset, (1 - u e) * x e := by
  have A : ∑ B ∈ Fp, ∑ D ∈ Fm, lam B D * (setWeight u B - setWeight u D - γ) =
      ∑ e ∈ hE.toFinset, u e * dualVector Fp Fm lam e - γ := by
    have h0 : ∀ B D, lam B D * (setWeight u B - setWeight u D - γ) =
        lam B D * (setWeight u B - setWeight u D) - lam B D * γ := fun _ _ => by ring
    simp_rw [h0, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum]
    rw [weak_sum hE Fp Fm hFpE hFmE u lam]; ring
  rw [A]
  have : ∑ e ∈ hE.toFinset, x e =
      ∑ e ∈ hE.toFinset, (u e * (x e - dualVector Fp Fm lam e) + (1 - u e) * x e + u e * dualVector Fp Fm lam e) := by
    apply Finset.sum_congr rfl; intro e _; ring
  rw [this, Finset.sum_add_distrib, Finset.sum_add_distrib]; ring


lemma exists_saddle {α : Type*} {E : Set α} (hE : E.Finite) (Fp Fm : Finset (Set α))
    (hFp : Fp.Nonempty) (hFm : Fm.Nonempty)
    (hFpE : ∀ B ∈ Fp, B ⊆ E) (hFmE : ∀ D ∈ Fm, D ⊆ E) :
    ∃ (u : α → ℝ) (lam : Set α → Set α → ℝ), (∀ e ∈ E, 0 ≤ u e ∧ u e ≤ 1) ∧
      (∀ B ∈ Fp, ∀ D ∈ Fm, 0 ≤ lam B D) ∧ ∑ B ∈ Fp, ∑ D ∈ Fm, lam B D = 1 ∧
      ∀ B ∈ Fp, ∀ D ∈ Fm, ∑ e ∈ hE.toFinset, max 0 (dualVector Fp Fm lam e) ≤
        setWeight u B - setWeight u D := by
  classical
  have : Nonempty (Fp × Fm) := by
    obtain ⟨B, hB⟩ := hFp
    obtain ⟨D, hD⟩ := hFm
    exact ⟨(⟨B, hB⟩, ⟨D, hD⟩)⟩
  let a : (Fp × Fm) → hE.toFinset → ℝ := fun q e =>
    (q.1 : Set α).indicator (1 : α → ℝ) e - (q.2 : Set α).indicator (1 : α → ℝ) e
  obtain ⟨u₀, l₀, hu₀, hl₀, hl₀s, hmin⟩ := Core.minimax a
  let u : α → ℝ := fun e => if h : e ∈ hE.toFinset then u₀ ⟨e, h⟩ else 0
  let lam : Set α → Set α → ℝ := fun B D =>
    if h : B ∈ Fp ∧ D ∈ Fm then l₀ (⟨B, h.1⟩, ⟨D, h.2⟩) else 0
  have hu_val : ∀ e : hE.toFinset, u e = u₀ e := by
    intro e; show (if h : (e : α) ∈ hE.toFinset then _ else _) = _
    rw [dif_pos e.2]
  have hlam_val : ∀ (B : Fp) (D : Fm), lam B D = l₀ (B, D) := by
    intro B D; simp [lam, B.2, D.2]
  have hdual : ∀ e : hE.toFinset, dualVector Fp Fm lam e = ∑ q, l₀ q * a q e := by
    intro e
    unfold dualVector
    rw [← Finset.sum_coe_sort Fp]
    simp_rw [← Finset.sum_coe_sort Fm]
    rw [Fintype.sum_prod_type]
    simp only [hlam_val, a]
  refine ⟨u, lam, ?_, ?_, ?_, ?_⟩
  · intro e he
    have he' : e ∈ hE.toFinset := hE.mem_toFinset.2 he
    have := hu₀ ⟨e, he'⟩
    rwa [← hu_val ⟨e, he'⟩] at this
  · intro B hB D hD
    have := hlam_val ⟨B, hB⟩ ⟨D, hD⟩
    simp only at this
    rw [this]; exact hl₀ _
  · rw [← Finset.sum_coe_sort Fp]
    simp_rw [← Finset.sum_coe_sort Fm]
    calc ∑ x : Fp, ∑ y : Fm, lam x y = ∑ x : Fp, ∑ y : Fm, l₀ (x, y) := by
          simp only [hlam_val]
      _ = ∑ q, l₀ q := (Fintype.sum_prod_type (fun q : Fp × Fm => l₀ q)).symm
      _ = 1 := hl₀s
  · intro B hB D hD
    rw [setWeight_sub hE (hFpE B hB) (hFmE D hD)]
    have h1 := hmin (⟨B, hB⟩, ⟨D, hD⟩)
    rw [← Finset.sum_coe_sort hE.toFinset] 
    rw [← Finset.sum_coe_sort hE.toFinset (fun e => u e * _)]
    simp_rw [hdual, hu_val]
    exact h1


lemma terms_nonneg {α : Type*} {E : Set α} (hE : E.Finite) (Fp Fm : Finset (Set α))
    (u : α → ℝ) (γ : ℝ) (lam : Set α → Set α → ℝ) (x : α → ℝ)
    (hP : IsPrimalFeasible E Fp Fm u γ) (hD : IsDualFeasible E Fp Fm lam x) :
    (∀ B ∈ Fp, ∀ D ∈ Fm, 0 ≤ lam B D * (setWeight u B - setWeight u D - γ)) ∧
    (∀ e ∈ hE.toFinset, 0 ≤ u e * (x e - dualVector Fp Fm lam e)) ∧
    (∀ e ∈ hE.toFinset, 0 ≤ (1 - u e) * x e) := by
  refine ⟨fun B hB D hD' => mul_nonneg (hD.1 B hB D hD') (by linarith [hP.2 B hB D hD']), ?_, ?_⟩
  · intro e he
    have he' := hE.mem_toFinset.1 he
    exact mul_nonneg (hP.1 e he').1 (by linarith [(hD.2.2 e he').2])
  · intro e he
    have he' := hE.mem_toFinset.1 he
    exact mul_nonneg (by linarith [(hP.1 e he').2]) (hD.2.2 e he').1

lemma weak_duality {α : Type*} {E : Set α} (hE : E.Finite) (Fp Fm : Finset (Set α))
    (hFpE : ∀ B ∈ Fp, B ⊆ E) (hFmE : ∀ D ∈ Fm, D ⊆ E) (u : α → ℝ) (γ : ℝ)
    (lam : Set α → Set α → ℝ) (x : α → ℝ)
    (hP : IsPrimalFeasible E Fp Fm u γ) (hD : IsDualFeasible E Fp Fm lam x) :
    γ ≤ ∑ e ∈ hE.toFinset, x e := by
  have hid := slack_identity hE Fp Fm hFpE hFmE u γ lam x hD.2.1
  obtain ⟨h1, h2, h3⟩ := terms_nonneg hE Fp Fm u γ lam x hP hD
  have := Finset.sum_nonneg (fun B hB => Finset.sum_nonneg (fun D hD' => h1 B hB D hD'))
  have := Finset.sum_nonneg h2
  have := Finset.sum_nonneg h3
  linarith

end Dev.Eq5

theorem chk_proof_theorem_2_eq_5 {α : Type*} (E : Set α) (hE : E.Finite) (Fp Fm : Finset (Set α))
    (hFp : Fp.Nonempty) (hFm : Fm.Nonempty) (hFpE : ∀ B ∈ Fp, B ⊆ E) (hFmE : ∀ D ∈ Fm, D ⊆ E) :
    (∃ u γ, IsPrimalOptimal E Fp Fm u γ) ∧ (∃ lam x, IsDualOptimal E Fp Fm lam x) ∧
      ∀ u γ lam x, IsPrimalOptimal E Fp Fm u γ → IsDualOptimal E Fp Fm lam x →
        γ = Fp.inf' hFp (setWeight u) - Fm.sup' hFm (setWeight u) ∧
        (∀ e ∈ E, x e = max 0 (dualVector Fp Fm lam e)) ∧
        (∀ B ∈ Fp, ∀ D ∈ Fm, 0 < lam B D → setWeight u B - setWeight u D = γ) ∧
        ∀ e ∈ E,
          (u e = 0 → dualVector Fp Fm lam e ≤ 0) ∧
          (0 < u e → u e < 1 → dualVector Fp Fm lam e = 0) ∧
          (u e = 1 → 0 ≤ dualVector Fp Fm lam e) := by
  classical
  obtain ⟨u0, lam0, hu0, hl0, hs0, hmin⟩ := Dev.Eq5.exists_saddle hE Fp Fm hFp hFm hFpE hFmE
  let x0 : α → ℝ := fun e => max 0 (dualVector Fp Fm lam0 e)
  let γ0 : ℝ := ∑ e ∈ hE.toFinset, x0 e
  have hP0 : IsPrimalFeasible E Fp Fm u0 γ0 := ⟨hu0, hmin⟩
  have hD0 : IsDualFeasible E Fp Fm lam0 x0 :=
    ⟨hl0, hs0, fun e _ => ⟨le_max_left _ _, le_max_right _ _⟩⟩
  have hsw : ∀ x : α → ℝ, setWeight x E = ∑ e ∈ hE.toFinset, x e := Dev.Eq5.setWeight_E hE
  refine ⟨⟨u0, γ0, hP0, fun u' γ' hf => ?_⟩, ⟨lam0, x0, hD0, fun lam' x' hf => ?_⟩, ?_⟩
  · exact Dev.Eq5.weak_duality hE Fp Fm hFpE hFmE u' γ' lam0 x0 hf hD0
  · rw [hsw, hsw]
    exact Dev.Eq5.weak_duality hE Fp Fm hFpE hFmE u0 γ0 lam' x' hP0 hf
  intro u γ lam x hP hD
  have hγ : ∑ e ∈ hE.toFinset, x e = γ := by
    have h1 := hP.2 u0 γ0 hP0
    have h2 := hD.2 lam0 x0 hD0
    rw [hsw, hsw] at h2
    have h3 := Dev.Eq5.weak_duality hE Fp Fm hFpE hFmE u γ lam x hP.1 hD.1
    linarith
  have hid := Dev.Eq5.slack_identity hE Fp Fm hFpE hFmE u γ lam x hD.1.2.1
  obtain ⟨h1, h2, h3⟩ := Dev.Eq5.terms_nonneg hE Fp Fm u γ lam x hP.1 hD.1
  have s1 := Finset.sum_nonneg (fun B hB => Finset.sum_nonneg (fun D hD' => h1 B hB D hD'))
  have s2 := Finset.sum_nonneg h2
  have s3 := Finset.sum_nonneg h3
  have z1 : ∑ B ∈ Fp, ∑ D ∈ Fm, lam B D * (setWeight u B - setWeight u D - γ) = 0 := by
    linarith
  have z2 : ∑ e ∈ hE.toFinset, u e * (x e - dualVector Fp Fm lam e) = 0 := by linarith
  have z3 : ∑ e ∈ hE.toFinset, (1 - u e) * x e = 0 := by linarith
  have t1 : ∀ B ∈ Fp, ∀ D ∈ Fm, lam B D * (setWeight u B - setWeight u D - γ) = 0 := by
    intro B hB D hD'
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun B hB => Finset.sum_nonneg (fun D hD' => h1 B hB D hD'))).1 z1 B hB
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun D hD' => h1 B hB D hD')).1 this D hD'
  have t2 := (Finset.sum_eq_zero_iff_of_nonneg h2).1 z2
  have t3 := (Finset.sum_eq_zero_iff_of_nonneg h3).1 z3
  have hslack : ∀ B ∈ Fp, ∀ D ∈ Fm, 0 < lam B D → setWeight u B - setWeight u D = γ := by
    intro B hB D hD' hpos
    have := t1 B hB D hD'
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  have hpt : ∀ e ∈ E, (u e = 0 → x e = 0) ∧ (u e = 1 → x e = dualVector Fp Fm lam e) ∧
      (0 < u e → u e < 1 → x e = 0 ∧ x e = dualVector Fp Fm lam e) := by
    intro e he
    have he' := hE.mem_toFinset.2 he
    have a2 := t2 e he'
    have a3 := t3 e he'
    refine ⟨fun h0 => ?_, fun h1' => ?_, fun hp hq => ?_⟩
    · rw [h0] at a3; simpa using a3
    · rw [h1'] at a2; linarith
    · have : x e = 0 := by
        rcases mul_eq_zero.1 a3 with h | h
        · linarith
        · exact h
      refine ⟨this, ?_⟩
      rcases mul_eq_zero.1 a2 with h | h
      · linarith
      · linarith
  refine ⟨?_, ?_, hslack, ?_⟩
  · -- γ = inf' - sup'
    obtain ⟨B1, hB1, hB1e⟩ := Finset.exists_mem_eq_inf' hFp (setWeight u)
    obtain ⟨D1, hD1, hD1e⟩ := Finset.exists_mem_eq_sup' hFm (setWeight u)
    have hge : γ ≤ Fp.inf' hFp (setWeight u) - Fm.sup' hFm (setWeight u) := by
      rw [hB1e, hD1e]; exact hP.1.2 B1 hB1 D1 hD1
    have hpos : ∃ B ∈ Fp, ∃ D ∈ Fm, 0 < lam B D := by
      by_contra hcon
      push Not at hcon
      have : ∑ B ∈ Fp, ∑ D ∈ Fm, lam B D = 0 :=
        Finset.sum_eq_zero fun B hB => Finset.sum_eq_zero fun D hD' =>
          le_antisymm (hcon B hB D hD') (hD.1.1 B hB D hD')
      linarith [hD.1.2.1]
    obtain ⟨B, hB, D, hD', hlp⟩ := hpos
    have hle : Fp.inf' hFp (setWeight u) - Fm.sup' hFm (setWeight u) ≤ γ := by
      have := hslack B hB D hD' hlp
      have a1 := Finset.inf'_le (setWeight u) hB
      have a2 := Finset.le_sup' (setWeight u) hD'
      linarith
    exact le_antisymm hge hle
  · intro e he
    have hxe := hD.1.2.2 e he
    obtain ⟨hz, hone, hmid⟩ := hpt e he
    have hu := hP.1.1 e he
    apply le_antisymm
    · rcases hu.1.eq_or_lt with h0 | h0
      · rw [hz h0.symm]; exact le_max_left _ _
      · rcases hu.2.eq_or_lt with h1 | h1
        · rw [hone h1, ]; exact le_max_right _ _
        · rw [(hmid h0 h1).1]; exact le_max_left _ _
    · exact max_le hxe.1 hxe.2
  · intro e he
    have hxe := hD.1.2.2 e he
    obtain ⟨hz, hone, hmid⟩ := hpt e he
    refine ⟨fun h0 => ?_, fun hp hq => ?_, fun h1 => ?_⟩
    · have := hz h0; linarith [hxe.2]
    · exact ((hmid hp hq).2.symm.trans (hmid hp hq).1)
    · have := hone h1; linarith [hxe.1]

end MatroidEquitability
end

theorem solution : type_of% @MatroidEquitability.chk_proof_theorem_2_eq_5 := @MatroidEquitability.chk_proof_theorem_2_eq_5
