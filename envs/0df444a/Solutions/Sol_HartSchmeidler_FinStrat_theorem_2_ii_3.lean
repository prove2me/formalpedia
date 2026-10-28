-- Prove2me | solution 3 for HartSchmeidler.FinStrat.theorem_2_ii
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T06:57:28.699757+00:00
-- url     : https://prove2.me/submissions/daa661a2-dd24-4597-bd7d-30a6f02bec3e

import Mathlib
import Definitions.Def_HartSchmeidler_FinStrat_Game
import Theorems.Thm_Brouwer_exists_fixedPoint_euclideanSpace

-- carved verbatim out of submission f073f57a-f3fe-4167-8a17-6160f40b6e6d, lines 1526-1534

section
open HartSchmeidler
open HartSchmeidler.FinStrat
open MeasureTheory
open Metric Set MeasureTheory

theorem brouwer_fp {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {K : Set E}
    (hKconv : Convex ℝ K) (hKcpt : IsCompact K) (hKne : K.Nonempty)
    (f : E → E) (hf : ContinuousOn f K) (hfK : Set.MapsTo f K K) :
    ∃ x ∈ K, f x = x := by
  classical
  let φ : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  have hconv' : Convex ℝ (φ '' K) :=
    hKconv.linear_image (φ : E →ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
  have hcont : ContinuousOn (φ ∘ f ∘ φ.symm) (φ '' K) := by
    refine φ.continuous.comp_continuousOn (hf.comp φ.symm.continuous.continuousOn ?_)
    rintro _ ⟨y, hy, rfl⟩
    simpa using hy
  have hmaps : MapsTo (φ ∘ f ∘ φ.symm) (φ '' K) (φ '' K) := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨f y, hfK hy, by simp⟩
  obtain ⟨x, ⟨y, hyK, rfl⟩, hx⟩ :=
    Brouwer.exists_fixedPoint_euclideanSpace hconv' (hKcpt.image φ.continuous) (hKne.image φ) _ hcont hmaps
  refine ⟨y, hyK, ?_⟩
  apply φ.injective
  simpa using hx

end

section
open HartSchmeidler
open HartSchmeidler.FinStrat
open MeasureTheory

theorem stat_dist {A : Type*} [Fintype A] [Nonempty A] [DecidableEq A] (y : A → A → ℝ)
    (hy : ∀ r t, 0 ≤ y r t) :
    ∃ x : A → ℝ, (∀ a, 0 ≤ x a) ∧ ∑ a, x a = 1 ∧ ∀ t, ∑ r, x r * y r t = x t * ∑ u, y t u := by
  have hrs0 : ∀ r, 0 ≤ ∑ t, y r t := fun r => Finset.sum_nonneg fun t _ => hy r t
  have htot0 : 0 ≤ ∑ r, ∑ t, y r t := Finset.sum_nonneg fun r _ => hrs0 r
  have hrs : ∀ r, ∑ t, y r t ≤ ∑ r, ∑ t, y r t :=
    fun r => Finset.single_le_sum (f := fun r => ∑ t, y r t) (fun r _ => hrs0 r) (Finset.mem_univ r)
  set c : ℝ := 1 + ∑ r, ∑ t, y r t with hcdef
  have hc : 0 < c := by linarith
  have hrsc : ∀ r, (∑ t, y r t) / c ≤ 1 := fun r => by
    rw [div_le_one hc]; linarith [hrs r]
  let Ψ : (A → ℝ) → (A → ℝ) := fun x t => x t * (1 - (∑ u, y t u) / c) + (∑ r, x r * y r t) / c
  have hcont : Continuous Ψ := by
    apply continuous_pi
    intro t
    have : Continuous fun x : A → ℝ => ∑ r, x r * y r t :=
      continuous_finset_sum _ fun r _ => (continuous_apply r).mul continuous_const
    exact ((continuous_apply t).mul continuous_const).add (this.div_const c)
  have hmaps : Set.MapsTo Ψ (stdSimplex ℝ A) (stdSimplex ℝ A) := by
    rintro x ⟨hx0, hx1⟩
    refine ⟨fun t => ?_, ?_⟩
    · have h1 := hx0 t
      have h2 : 0 ≤ 1 - (∑ u, y t u) / c := by linarith [hrsc t]
      have h3 : 0 ≤ (∑ r, x r * y r t) / c :=
        div_nonneg (Finset.sum_nonneg fun r _ => mul_nonneg (hx0 r) (hy r t)) hc.le
      simp only [Ψ]
      positivity
    · simp only [Ψ]
      rw [Finset.sum_add_distrib, ← Finset.sum_div]
      have : ∑ t, x t * (1 - (∑ u, y t u) / c) = 1 - (∑ t, x t * ∑ u, y t u) / c := by
        simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hx1]
        congr 1
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl; intro t _; ring
      rw [this]
      have h2 : ∑ t, ∑ r, x r * y r t = ∑ t, x t * ∑ u, y t u := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun r _ => (Finset.mul_sum _ _ _).symm
      rw [h2]
      ring
  obtain ⟨x, hxK, hfix⟩ := brouwer_fp (convex_stdSimplex ℝ A) (isCompact_stdSimplex ℝ A)
    ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary A)⟩ Ψ hcont.continuousOn hmaps
  refine ⟨x, hxK.1, hxK.2, fun t => ?_⟩
  have h := congrFun hfix t
  simp only [Ψ] at h
  have h2 : (∑ r, x r * y r t) / c = x t * (∑ u, y t u) / c := by
    have : x t * (1 - (∑ u, y t u) / c) + (∑ r, x r * y r t) / c = x t := h
    have e : x t * (1 - (∑ u, y t u) / c) = x t - x t * (∑ u, y t u) / c := by ring
    linarith
  exact (div_left_inj' hc.ne').1 h2

theorem stat_zero {A : Type*} [Fintype A] [DecidableEq A] (x : A → ℝ) (y : A → A → ℝ)
    (hst : ∀ t, ∑ r, x r * y r t = x t * ∑ u, y t u) (G : A → ℝ) :
    ∑ a, x a * ∑ t, y a t * (G a - G t) = 0 := by
  have h1 : ∑ a, x a * ∑ t, y a t * (G a - G t) =
      ∑ a, x a * (∑ t, y a t) * G a - ∑ a, ∑ t, x a * y a t * G t := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib, mul_assoc]
    congr 1
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t _
    ring
  have h2 : ∑ a, ∑ t, x a * y a t * G t = ∑ t, x t * (∑ u, y t u) * G t := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    rw [← Finset.sum_mul, hst t]
  rw [h1, h2]
  simp

end

section
open HartSchmeidler
open HartSchmeidler.FinStrat
open MeasureTheory
variable {P : Type*} [Fintype P] [DecidableEq P] {A : P → Type*} [∀ i, Fintype (A i)]
  [∀ i, DecidableEq (A i)] [∀ i, Nonempty (A i)]

def splitEquiv (i : P) (a₀ : A i) : (A i × {s : ∀ j, A j // s i = a₀}) ≃ (∀ j, A j) where
  toFun p := Function.update p.2.1 i p.1
  invFun s := (s i, ⟨Function.update s i a₀, by simp⟩)
  left_inv := by
    rintro ⟨a, z, hz⟩
    simp [hz]
  right_inv := by
    intro s
    simp

theorem key_ident (x : ∀ j, A j → ℝ) (i : P) (yi : A i → A i → ℝ)
    (hst : ∀ t, ∑ r, x i r * yi r t = x i t * ∑ u, yi t u) (g : (∀ j, A j) → ℝ) :
    ∑ s : (∀ j, A j), (∏ j, x j (s j)) * ∑ t, yi (s i) t * (g s - g (Function.update s i t)) = 0 := by
  classical
  let a₀ : A i := Classical.arbitrary _
  rw [← Equiv.sum_comp (splitEquiv i a₀), Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro z _
  have hprod : ∀ a : A i, (∏ j, x j ((splitEquiv i a₀ (a, z)) j)) = x i a * ∏ j ∈ Finset.univ.erase i, x j (z.1 j) := by
    intro a
    simp only [splitEquiv, Equiv.coe_fn_mk]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    simp only [Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  have hterm : ∀ a : A i, (∏ j, x j ((splitEquiv i a₀ (a, z)) j)) *
      ∑ t, yi ((splitEquiv i a₀ (a, z)) i) t * (g (splitEquiv i a₀ (a, z)) - g (Function.update (splitEquiv i a₀ (a, z)) i t))
      = (∏ j ∈ Finset.univ.erase i, x j (z.1 j)) *
        (x i a * ∑ t, yi a t * (g (Function.update z.1 i a) - g (Function.update z.1 i t))) := by
    intro a
    rw [hprod a]
    simp only [splitEquiv, Equiv.coe_fn_mk, Function.update_self, Function.update_idem]
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  have := stat_zero (x i) yi hst (fun a => g (Function.update z.1 i a))
  rw [this, mul_zero]

def ceV (u : P → (∀ i, A i) → ℝ) (s : ∀ i, A i) (k : (i : P) × A i × A i) : ℝ :=
  if s k.1 = k.2.1 then u k.1 s - u k.1 (Function.update s k.1 k.2.2) else 0

lemma sumV (u : P → (∀ i, A i) → ℝ) (y : ((i : P) × A i × A i) → ℝ) (s : ∀ i, A i) :
    ∑ k, y k * ceV u s k =
      ∑ i, ∑ t, y ⟨i, s i, t⟩ * (u i s - u i (Function.update s i t)) := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  simp only [ceV, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  simp

theorem fin_ce (u : P → (∀ i, A i) → ℝ) :
    ∃ w : (∀ i, A i) → ℝ, (∀ s, 0 ≤ w s) ∧ ∑ s, w s = 1 ∧
      ∀ k, 0 ≤ ∑ s, w s * ceV u s k := by
  by_contra hno
  push_neg at hno
  let Φ : ((∀ i, A i) → ℝ) →ₗ[ℝ] (((i : P) × A i × A i) → ℝ) :=
    { toFun := fun w k => ∑ s, w s * ceV u s k
      map_add' := by intro a b; ext k; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by intro c a; ext k; simp [Finset.mul_sum, mul_assoc] }
  let C := Φ '' stdSimplex ℝ (∀ i, A i)
  let Q : Set (((i : P) × A i × A i) → ℝ) := {x | ∀ k, 0 ≤ x k}
  have hCconv : Convex ℝ C := (convex_stdSimplex ℝ _).linear_image Φ
  have hCcpt : IsCompact C :=
    (isCompact_stdSimplex ℝ _).image (LinearMap.continuous_of_finiteDimensional Φ)
  have hQconv : Convex ℝ Q := by
    intro a ha b hb c d hc hd _ k
    have := ha k; have := hb k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    positivity
  have hQcl : IsClosed Q := by
    have : Q = ⋂ k, {x : ((i : P) × A i × A i) → ℝ | 0 ≤ x k} := by ext x; simp [Q]
    rw [this]
    exact isClosed_iInter fun k => isClosed_le continuous_const (continuous_apply k)
  have hdisj : Disjoint C Q := by
    rw [Set.disjoint_left]
    rintro x ⟨w, ⟨hw0, hw1⟩, rfl⟩ hQ
    obtain ⟨k, hk⟩ := hno w hw0 hw1
    have := hQ k
    simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk] at this
    linarith
  obtain ⟨f, u₀, v₀, hC, huv, hQf⟩ := geometric_hahn_banach_compact_closed hCconv hCcpt hQconv hQcl hdisj
  let e : ((i : P) × A i × A i) → (((i : P) × A i × A i) → ℝ) := fun k j => if k = j then 1 else 0
  let y : ((i : P) × A i × A i) → ℝ := fun k => f (e k)
  have hfx : ∀ x, f x = ∑ k, x k * y k := by
    intro x
    have := LinearMap.pi_apply_eq_sum_univ (f : (((i : P) × A i × A i) → ℝ) →ₗ[ℝ] ℝ) x
    simpa [smul_eq_mul, y, e] using this
  have hv0 : v₀ < 0 := by
    have := hQf 0 (fun k => le_rfl)
    simpa using this
  have hy : ∀ k, 0 ≤ y k := by
    intro k
    by_contra hneg
    push_neg at hneg
    have hpos : 0 < v₀ / y k := div_pos_of_neg_of_neg hv0 hneg
    have hb : (v₀ / y k + 1) • e k ∈ Q := by
      intro j
      simp only [Pi.smul_apply, smul_eq_mul, e]
      split_ifs <;> simp <;> linarith
    have h1 := hQf _ hb
    rw [map_smul, smul_eq_mul] at h1
    have h2 : (v₀ / y k + 1) * y k = v₀ + y k := by
      have : y k ≠ 0 := hneg.ne
      field_simp
    have h3 : f (e k) = y k := rfl
    rw [h3, h2] at h1
    linarith
  have hs : ∀ s, ∑ k, y k * ceV u s k < 0 := by
    intro s
    have hmem : (fun k => ceV u s k) ∈ C := by
      refine ⟨Pi.single s 1, ⟨fun s' => ?_, ?_⟩, ?_⟩
      · by_cases h : s' = s <;> simp [Pi.single_apply, h]
      · simp
      · ext k
        simp [Φ, Pi.single_apply]
    have := hC _ hmem
    rw [hfx] at this
    have h2 : ∑ k, y k * ceV u s k = ∑ k, ceV u s k * y k :=
      Finset.sum_congr rfl fun k _ => mul_comm _ _
    linarith
  -- stationary distributions
  have hstat : ∀ i : P, ∃ x : A i → ℝ, (∀ a, 0 ≤ x a) ∧ ∑ a, x a = 1 ∧
      ∀ t, ∑ r, x r * y ⟨i, r, t⟩ = x t * ∑ v, y ⟨i, t, v⟩ := fun i =>
    stat_dist (fun r t => y ⟨i, r, t⟩) (fun r t => hy _)
  choose x hx0 hx1 hxst using hstat
  let W : (∀ i, A i) → ℝ := fun s => ∏ i, x i (s i)
  have hW0 : ∀ s, 0 ≤ W s := fun s => Finset.prod_nonneg fun i _ => hx0 i (s i)
  have hW1 : ∑ s, W s = 1 := by
    have := Finset.prod_univ_sum (fun i => (Finset.univ : Finset (A i))) (fun i a => x i a)
    simp only [Fintype.piFinset_univ] at this
    rw [← this]
    exact Finset.prod_eq_one fun i _ => hx1 i
  have hzero : ∑ s, W s * ∑ k, y k * ceV u s k = 0 := by
    calc ∑ s, W s * ∑ k, y k * ceV u s k
        = ∑ s, ∑ i, W s * ∑ t, y ⟨i, s i, t⟩ * (u i s - u i (Function.update s i t)) := by
          apply Finset.sum_congr rfl
          intro s _
          rw [sumV, Finset.mul_sum]
      _ = ∑ i, ∑ s, W s * ∑ t, y ⟨i, s i, t⟩ * (u i s - u i (Function.update s i t)) :=
          Finset.sum_comm
      _ = 0 := by
          apply Finset.sum_eq_zero
          intro i _
          exact key_ident x i (fun r t => y ⟨i, r, t⟩) (hxst i) (u i)
  obtain ⟨s0, hs0⟩ : ∃ s0, 0 < W s0 := by
    by_contra h
    push_neg at h
    have : ∑ s, W s = 0 := Finset.sum_eq_zero fun s _ => le_antisymm (h s) (hW0 s)
    linarith
  have hlt : ∑ s, W s * ∑ k, y k * ceV u s k < 0 := by
    calc ∑ s, W s * ∑ k, y k * ceV u s k < ∑ s : (∀ i, A i), (0 : ℝ) := by
          apply Finset.sum_lt_sum
          · intro s _
            exact mul_nonpos_of_nonneg_of_nonpos (hW0 s) (hs s).le
          · exact ⟨s0, Finset.mem_univ _, mul_neg_of_pos_of_neg hs0 (hs s0)⟩
      _ = 0 := by simp
  linarith

end

section
open HartSchmeidler
open HartSchmeidler.FinStrat
open MeasureTheory

theorem fset_core {ι : Type*} [Nonempty ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    [∀ i, Nonempty (S i)]
    (h : ι → (∀ i, S i) → ℝ)
    (T : ∀ i, Finset (S i))
    (hT : IsFSet T) :
    ∃ (F : Finset (∀ i, S i)) (w : (∀ i, S i) → ℝ), IsFSetCE h T F w := by
  classical
  let N : Finset ι := hT.2.toFinset
  have hN : ∀ j, j ∉ N → ∃ c, T j = {c} := by
    intro j hj
    have : j ∉ {i | ¬ ∃ a : S i, T i = {a}} := by simpa [N] using hj
    simpa using this
  let P := {i // i ∈ N}
  let A : P → Type _ := fun i => {a : S i.1 // a ∈ T i.1}
  haveI : ∀ i, Nonempty (A i) := fun i => ⟨⟨(hT.1 i.1).choose, (hT.1 i.1).choose_spec⟩⟩
  let b : ∀ j, S j := fun j => (hT.1 j).choose
  have hb : ∀ j, b j ∈ T j := fun j => (hT.1 j).choose_spec
  let φ : (∀ i : P, A i) → (∀ j, S j) := fun a j => if hj : j ∈ N then (a ⟨j, hj⟩).1 else b j
  have hφT : ∀ a j, φ a j ∈ T j := by
    intro a j
    by_cases hj : j ∈ N
    · simp only [φ, hj, dite_true]; exact (a ⟨j, hj⟩).2
    · simp only [φ, hj, dite_false]; exact hb j
  have hφN : ∀ a (i : P), φ a i.1 = (a i).1 := by
    intro a i
    simp [φ, i.2]
  have hφupd : ∀ (a : ∀ i : P, A i) (i : P) (t : A i),
      φ (Function.update a i t) = Function.update (φ a) i.1 t.1 := by
    intro a i t
    funext j
    by_cases hj : j = i.1
    · subst hj
      rw [Function.update_self, hφN]
      simp
    · rw [Function.update_of_ne hj]
      by_cases hjN : j ∈ N
      · have : (⟨j, hjN⟩ : P) ≠ i := fun h => hj (congrArg Subtype.val h)
        simp [φ, hjN, Function.update_of_ne this]
      · simp [φ, hjN]
  let u : P → (∀ i : P, A i) → ℝ := fun i a => h i.1 (φ a)
  obtain ⟨w0, hw0, hw1, hw2⟩ := fin_ce u
  let F : Finset (∀ i, S i) := Finset.univ.image φ
  let w : (∀ i, S i) → ℝ := fun s => ∑ a, if φ a = s then w0 a else 0
  have hsum : ∀ g : (∀ i, S i) → ℝ, ∑ s ∈ F, w s * g s = ∑ a, w0 a * g (φ a) := by
    intro g
    simp only [w, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    simp [ite_mul, F]
  refine ⟨F, w, ?_, ?_, ?_, ?_⟩
  · intro s hs i
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hs
    exact hφT a i
  · intro s _
    exact Finset.sum_nonneg fun a _ => by split_ifs <;> simp [hw0 a]
  · have := hsum (fun _ => 1)
    simp only [mul_one] at this
    rw [this]; exact hw1
  · intro i r t hr ht
    rw [Finset.sum_filter]
    have h1 : ∑ s ∈ F, (if s i = r then w s * (h i s - h i (Function.update s i t)) else 0)
        = ∑ s ∈ F, w s * (if s i = r then (h i s - h i (Function.update s i t)) else 0) := by
      apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp
    rw [h1, hsum (fun s => if s i = r then (h i s - h i (Function.update s i t)) else 0)]
    by_cases hi : i ∈ N
    · have := hw2 ⟨⟨i, hi⟩, ⟨r, hr⟩, ⟨t, ht⟩⟩
      refine le_of_le_of_eq this (Finset.sum_congr rfl fun a _ => ?_)
      congr 1
      simp only [ceV, u]
      by_cases hc : a ⟨i, hi⟩ = ⟨r, hr⟩
      · have hc' : φ a i = r := by
          have e : φ a i = (a ⟨i, hi⟩).1 := hφN a ⟨i, hi⟩
          rw [e, hc]
        rw [if_pos hc, if_pos hc', hφupd]
      · have hc' : ¬ φ a i = r := by
          intro h2
          apply hc
          apply Subtype.ext
          simpa [φ, hi] using h2
        rw [if_neg hc, if_neg hc']
    · obtain ⟨c, hc⟩ := hN i hi
      have hrc : r = c := by rw [hc] at hr; simpa using hr
      have htc : t = c := by rw [hc] at ht; simpa using ht
      apply Finset.sum_nonneg
      intro a _
      by_cases hca : φ a i = r
      · have : Function.update (φ a) i t = φ a := by
          rw [show t = φ a i by rw [hca, hrc, htc]]
          exact Function.update_eq_self _ _
        simp [hca, this]
      · simp [hca]

end

section
open HartSchmeidler
open HartSchmeidler.FinStrat
open MeasureTheory
variable {ι : Type*} {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)]
    [∀ i, TopologicalSpace (S i)] [∀ i, DiscreteTopology (S i)]
    [∀ i, MeasurableSpace (S i)] [∀ i, DiscreteMeasurableSpace (S i)]

open Classical in
noncomputable def cylAlg : Subalgebra ℝ C(∀ i, S i, ℝ) where
  carrier := {f | ∃ J : Finset ι, ∀ x y : (∀ i, S i), (∀ j ∈ J, x j = y j) → f x = f y}
  mul_mem' := by
    rintro f g ⟨J, hJ⟩ ⟨K, hK⟩
    refine ⟨J ∪ K, fun x y hxy => ?_⟩
    simp only [ContinuousMap.mul_apply]
    rw [hJ x y (fun j hj => hxy j (Finset.mem_union_left _ hj)),
      hK x y (fun j hj => hxy j (Finset.mem_union_right _ hj))]
  add_mem' := by
    rintro f g ⟨J, hJ⟩ ⟨K, hK⟩
    refine ⟨J ∪ K, fun x y hxy => ?_⟩
    simp only [ContinuousMap.add_apply]
    rw [hJ x y (fun j hj => hxy j (Finset.mem_union_left _ hj)),
      hK x y (fun j hj => hxy j (Finset.mem_union_right _ hj))]
  algebraMap_mem' := by
    intro r
    exact ⟨∅, fun x y _ => rfl⟩

open Classical in
lemma cylAlg_measurable (f : C(∀ i, S i, ℝ)) (hf : f ∈ (cylAlg (S := S))) : Measurable f := by
  obtain ⟨J, hJ⟩ := hf
  let d : ∀ i, S i := fun i => Classical.arbitrary (S i)
  let ext : (∀ j : J, S j) → (∀ i, S i) := fun y j => if h : j ∈ J then y ⟨j, h⟩ else d j
  have hg : Measurable (fun y : (∀ j : J, S j) => f (ext y)) := measurable_of_countable _
  have hπ : Measurable (fun (x : ∀ i, S i) (j : J) => x j) :=
    measurable_pi_lambda _ fun j => measurable_pi_apply _
  have : (f : (∀ i, S i) → ℝ) = (fun y : (∀ j : J, S j) => f (ext y)) ∘ (fun (x : ∀ i, S i) (j : J) => x j) := by
    funext x
    simp only [Function.comp]
    apply hJ
    intro j hj
    simp [ext, hj]
  rw [this]
  exact hg.comp hπ

theorem meas_of_cont (f : C(∀ i, S i, ℝ)) : Measurable f := by
  classical
  have hsep : (cylAlg (S := S)).SeparatesPoints := by
    intro x y hxy
    have : ∃ j, x j ≠ y j := by
      by_contra h; push_neg at h; exact hxy (funext h)
    obtain ⟨j, hj⟩ := this
    let e : C(∀ i, S i, ℝ) :=
      ⟨fun z => if z j = x j then 1 else 0,
        (continuous_of_discreteTopology (f := fun a : S j => if a = x j then (1:ℝ) else 0)).comp
          (continuous_apply j)⟩
    refine ⟨e, ⟨e, ⟨{j}, fun a b hab => ?_⟩, rfl⟩, ?_⟩
    · have := hab j (by simp)
      simp [e, this]
    · simp [e, hj.symm]
  have htop := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints _ hsep
  have hf0 : f ∈ (cylAlg (S := S)).topologicalClosure := by rw [htop]; trivial
  have hf : f ∈ closure ((cylAlg (S := S) : Subalgebra ℝ C(∀ i, S i, ℝ)) : Set C(∀ i, S i, ℝ)) := by
    rw [← SetLike.mem_coe, Subalgebra.topologicalClosure_coe] at hf0; exact hf0
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 hf
  refine measurable_of_tendsto_metrizable (f := fun n => (u n : (∀ i, S i) → ℝ))
    (fun n => cylAlg_measurable _ (hu n)) ?_
  rw [tendsto_pi_nhds]
  intro x
  exact ((continuous_eval_const x).tendsto f).comp hlim

lemma cont_test [DecidableEq ι] [∀ i, DecidableEq (S i)] (h : ι → (∀ i, S i) → ℝ) (hh : ∀ i, Continuous (h i))
    (i : ι) (r t : S i) :
    Continuous (fun s : (∀ i, S i) => (if s i = r then (1:ℝ) else 0) * (h i s - h i (Function.update s i t))) := by
  have he : Continuous (fun s : (∀ i, S i) => if s i = r then (1:ℝ) else 0) :=
    (continuous_of_discreteTopology (f := fun a : S i => if a = r then (1:ℝ) else 0)).comp
          (continuous_apply i)
  exact he.mul ((hh i).sub ((hh i).comp (continuous_id.update i continuous_const)))

end

section
open HartSchmeidler
open HartSchmeidler.FinStrat
open MeasureTheory
variable {ι : Type*} [Nonempty ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    [∀ i, Nonempty (S i)]
    [∀ i, TopologicalSpace (S i)] [∀ i, DiscreteTopology (S i)]
    [∀ i, MeasurableSpace (S i)] [∀ i, DiscreteMeasurableSpace (S i)]

theorem cp_core
    (h : ι → (∀ i, S i) → ℝ) (hh : ∀ i, Continuous (h i))
    (anchor : ∀ i, S i)
    (F : (∀ i, Finset (S i)) → Finset (∀ i, S i))
    (w : (∀ i, Finset (S i)) → (∀ i, S i) → ℝ)
    (hFw : ∀ T, IsAnchoredFSet anchor T → IsFSetCE h T (F T) (w T))
    (p : Measure (∀ i, S i)) (hp : IsProbabilityMeasure p)
    (hcluster : ∀ (f : C(∀ i, S i, ℝ)) (ε : ℝ), 0 < ε →
      ∀ T₀, IsAnchoredFSet anchor T₀ →
        ∃ T, IsAnchoredFSet anchor T ∧ FSetLE T₀ T ∧
          |∫ s, f s ∂p - ∑ s ∈ F T, w T s * f s| < ε) :
    IsCorrelatedEq h p := by
  refine ⟨hp, fun i r t => ?_⟩
  let fC : C(∀ i, S i, ℝ) := ⟨_, cont_test h hh i r t⟩
  have hfC : ∀ s, fC s = ({s : ∀ i, S i | s i = r}.indicator (fun s => h i s - h i (Function.update s i t))) s := by
    intro s
    by_cases hs : s i = r <;> simp [fC, hs]
  have hmeasE : MeasurableSet {s : ∀ i, S i | s i = r} :=
    measurableSet_eq_fun (measurable_pi_apply i) measurable_const
  have hint : Integrable fC p := by
    obtain ⟨C, hC⟩ := (isCompact_range fC.continuous).isBounded.exists_norm_le
    exact Integrable.of_bound (meas_of_cont fC).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun s => hC _ ⟨s, rfl⟩)
  have hfeq : (fC : (∀ i, S i) → ℝ) = {s : ∀ i, S i | s i = r}.indicator (fun s => h i s - h i (Function.update s i t)) :=
    funext hfC
  have hI : IntegrableOn (fun s => h i s - h i (Function.update s i t)) {s | s i = r} p := by
    rw [← integrable_indicator_iff hmeasE, ← hfeq]; exact hint
  refine ⟨hI, ?_⟩
  have hsetint : ∫ s in {s : ∀ i, S i | s i = r}, (h i s - h i (Function.update s i t)) ∂p = ∫ s, fC s ∂p := by
    rw [hfeq, integral_indicator hmeasE]
  rw [hsetint]
  let T₀ : ∀ j, Finset (S j) := Function.update (fun j => {anchor j}) i {anchor i, r, t}
  have hT₀ : IsAnchoredFSet anchor T₀ := by
    refine ⟨⟨fun j => ?_, ?_⟩, fun j => ?_⟩
    · by_cases hj : j = i
      · subst hj; simp [T₀]
      · simp [T₀, Function.update_of_ne hj]
    · apply (Set.finite_singleton i).subset
      intro j hj
      by_contra hne
      have : j ≠ i := hne
      exact hj ⟨anchor j, by simp [T₀, Function.update_of_ne this]⟩
    · by_cases hj : j = i
      · subst hj; simp [T₀]
      · simp [T₀, Function.update_of_ne hj]
  apply le_of_forall_pos_lt_add
  intro ε hε
  obtain ⟨T, hT, hle, hab⟩ := hcluster fC ε hε T₀ hT₀
  have hr : r ∈ T i := hle i (by simp [T₀])
  have ht : t ∈ T i := hle i (by simp [T₀])
  have hnn := (hFw T hT).2.2.2 i r t hr ht
  have hsum : ∑ s ∈ F T, w T s * fC s =
      ∑ s ∈ (F T).filter (fun s => s i = r), w T s * (h i s - h i (Function.update s i t)) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro s _
    by_cases hs : s i = r <;> simp [fC, hs]
  rw [hsum] at hab
  have := (abs_lt.1 hab).1
  linarith

end

section
open HartSchmeidler
open HartSchmeidler.FinStrat
open MeasureTheory

open CompactlySupported in
lemma riesz_gen {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [m : MeasurableSpace X]
    [BorelSpace X] (L : C(X, ℝ) →ₗ[ℝ] ℝ) (hpos : ∀ f : C(X, ℝ), 0 ≤ f → 0 ≤ L f) (h1 : L 1 = 1) :
    ∃ ν : Measure X, IsProbabilityMeasure ν ∧ ∀ f : C(X, ℝ), ∫ x, f x ∂ν = L f := by
  let Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
    PositiveLinearMap.mk₀
      { toFun := fun g => L ⟨g, g.continuous⟩
        map_add' := fun g g' => by
          rw [← map_add]; congr 1
        map_smul' := fun c g => by
          simp only [RingHom.id_apply]
          rw [← map_smul]; congr 1 }
      (fun g hg => hpos _ (fun x => hg x))
  have hint : ∀ f : C(X, ℝ), ∫ x, f x ∂(RealRMK.rieszMeasure Λ) = L f := by
    intro f
    have := RealRMK.integral_rieszMeasure Λ ⟨f, HasCompactSupport.of_compactSpace f⟩
    exact this.trans rfl
  refine ⟨RealRMK.rieszMeasure Λ, ⟨?_⟩, hint⟩
  have h := hint 1
  rw [h1] at h
  simp at h
  have hf : IsFiniteMeasure (RealRMK.rieszMeasure Λ) := inferInstance
  have : (RealRMK.rieszMeasure Λ).real Set.univ = 1 := by simpa using h
  rw [measureReal_def] at this
  rwa [← ENNReal.toReal_eq_one_iff]

end

section
open HartSchmeidler
open HartSchmeidler.FinStrat
open MeasureTheory
variable {ι : Type*} [Nonempty ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)]
    [∀ i, TopologicalSpace (S i)] [∀ i, DiscreteTopology (S i)]
    [∀ i, MeasurableSpace (S i)] [∀ i, DiscreteMeasurableSpace (S i)]

lemma integrable_cont (μ : Measure (∀ i, S i)) [IsFiniteMeasure μ] (f : C(∀ i, S i, ℝ)) :
    Integrable f μ := by
  obtain ⟨C, hC⟩ := (isCompact_range f.continuous).isBounded.exists_norm_le
  exact Integrable.of_bound (meas_of_cont f).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun s => hC _ ⟨s, rfl⟩)

lemma pi_le_borel : (MeasurableSpace.pi : MeasurableSpace (∀ i, S i)) ≤ borel (∀ i, S i) := by
  refine iSup_le fun i => ?_
  have : @Measurable (∀ i, S i) (S i) (borel _) _ (fun b => b i) := by
    letI : MeasurableSpace (∀ i, S i) := borel _
    haveI : OpensMeasurableSpace (∀ i, S i) := ⟨le_rfl⟩
    intro s _
    exact ((isOpen_discrete s).preimage (continuous_apply i)).measurableSet
  exact this.comap_le

theorem ecp_core {D : Type*} [Preorder D] [IsDirected D (· ≤ ·)] [Nonempty D]
    (q : D → Measure (∀ i, S i)) (hq : ∀ d, IsProbabilityMeasure (q d)) :
    ∃ p : Measure (∀ i, S i), IsProbabilityMeasure p ∧
      ∀ (fs : Finset C(∀ i, S i, ℝ)) (ε : ℝ), 0 < ε → ∀ d₀ : D,
        ∃ d : D, d₀ ≤ d ∧ ∀ f ∈ fs, |∫ s, f s ∂p - ∫ s, f s ∂(q d)| < ε := by
  classical
  haveI : ∀ d, IsProbabilityMeasure (q d) := hq
  let 𝒰 : Ultrafilter D := Ultrafilter.of Filter.atTop
  have h𝒰 : (𝒰 : Filter D) ≤ Filter.atTop := Ultrafilter.of_le _
  have hbd : ∀ (f : C(∀ i, S i, ℝ)) d, ∫ s, f s ∂(q d) ∈ Set.Icc (-‖f‖) ‖f‖ := by
    intro f d
    have h := norm_integral_le_of_norm_le_const (μ := q d) (f := fun s => f s) (C := ‖f‖)
      (Filter.Eventually.of_forall fun s => ContinuousMap.norm_coe_le_norm f s)
    simp only [probReal_univ, mul_one] at h
    exact abs_le.1 (by simpa using h)
  have hlim : ∀ f : C(∀ i, S i, ℝ), ∃ x, Filter.Tendsto (fun d => ∫ s, f s ∂(q d)) (𝒰 : Filter D) (nhds x) := by
    intro f
    obtain ⟨x, -, hx⟩ := (isCompact_Icc (a := -‖f‖) (b := ‖f‖)).ultrafilter_le_nhds
      (𝒰.map (fun d => ∫ s, f s ∂(q d)))
      (by
        rw [Ultrafilter.coe_map, Filter.le_principal_iff]
        exact Filter.mem_map.2 (Filter.Eventually.of_forall (fun d => hbd f d)))
    exact ⟨x, hx⟩
  choose a ha using hlim
  have hadd : ∀ f g : C(∀ i, S i, ℝ), a (f + g) = a f + a g := by
    intro f g
    have h2 : (fun d => ∫ s, (f + g) s ∂(q d)) = fun d => ∫ s, f s ∂(q d) + ∫ s, g s ∂(q d) := by
      funext d
      simp only [ContinuousMap.add_apply]
      exact integral_add (integrable_cont _ f) (integrable_cont _ g)
    have h3 := (ha f).add (ha g)
    have h4 := ha (f + g)
    rw [h2] at h4
    exact tendsto_nhds_unique h4 h3
  have hsmul : ∀ (c : ℝ) (f : C(∀ i, S i, ℝ)), a (c • f) = c * a f := by
    intro c f
    have h2 : (fun d => ∫ s, (c • f) s ∂(q d)) = fun d => c * ∫ s, f s ∂(q d) := by
      funext d
      simp only [ContinuousMap.smul_apply, smul_eq_mul]
      exact integral_const_mul c _
    have h3 := (ha f).const_mul c
    have h4 := ha (c • f)
    rw [h2] at h4
    exact tendsto_nhds_unique h4 h3
  have hpos : ∀ f : C(∀ i, S i, ℝ), 0 ≤ f → 0 ≤ a f := fun f hf =>
    ge_of_tendsto' (ha f) fun d => integral_nonneg fun s => hf s
  have hone : a 1 = 1 := by
    have h4 := ha 1
    have h2 : (fun d => ∫ s, (1 : C(∀ i, S i, ℝ)) s ∂(q d)) = fun _ => (1:ℝ) := by
      funext d; simp
    rw [h2] at h4
    exact tendsto_nhds_unique h4 tendsto_const_nhds
  let L : C(∀ i, S i, ℝ) →ₗ[ℝ] ℝ :=
    { toFun := a, map_add' := hadd, map_smul' := fun c f => by simpa using hsmul c f }
  obtain ⟨ν, hν, hνint⟩ := @riesz_gen (∀ i, S i) _ _ _ (borel _) (@BorelSpace.mk _ _ (borel _) rfl) L hpos hone
  have hint : ∀ f : C(∀ i, S i, ℝ), ∫ s, f s ∂(ν.trim pi_le_borel) = a f := by
    intro f
    have h := integral_trim (μ := ν) pi_le_borel (meas_of_cont f).stronglyMeasurable
    exact h.symm.trans (hνint f)
  refine ⟨ν.trim pi_le_borel, ⟨?_⟩, ?_⟩
  · rw [trim_measurableSet_eq pi_le_borel MeasurableSet.univ]
    exact hν.measure_univ
  · intro fs ε hε d₀
    have hev : ∀ f : C(∀ i, S i, ℝ), ∀ᶠ d in (𝒰 : Filter D), |∫ s, f s ∂(ν.trim pi_le_borel) - ∫ s, f s ∂(q d)| < ε := by
      intro f
      have := Metric.tendsto_nhds.1 (ha f) ε hε
      refine this.mono fun d hd => ?_
      rw [Real.dist_eq, abs_sub_comm] at hd
      rw [hint f]
      exact hd
    have hall : ∀ᶠ d in (𝒰 : Filter D), ∀ f ∈ fs, |∫ s, f s ∂(ν.trim pi_le_borel) - ∫ s, f s ∂(q d)| < ε :=
      (Filter.eventually_all_finset fs).2 fun f _ => hev f
    have hge : ∀ᶠ d in (𝒰 : Filter D), d₀ ≤ d := h𝒰 (Filter.eventually_ge_atTop d₀)
    obtain ⟨d, hd1, hd2⟩ := (hall.and hge).exists
    exact ⟨d, hd2, hd1⟩

end

section
open HartSchmeidler
open HartSchmeidler.FinStrat
open MeasureTheory
variable {ι : Type*} [Nonempty ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]
    [∀ i, TopologicalSpace (S i)] [∀ i, DiscreteTopology (S i)]
    [∀ i, MeasurableSpace (S i)] [∀ i, DiscreteMeasurableSpace (S i)]

structure FDir (anchor : ∀ i, S i) where
  val : ∀ i, Finset (S i)
  prop : IsAnchoredFSet anchor val

instance (anchor : ∀ i, S i) : Preorder (FDir anchor) where
  le T U := FSetLE T.1 U.1
  le_refl T := fun i => Finset.Subset.refl _
  le_trans T U V h1 h2 := fun i => (h1 i).trans (h2 i)

instance (anchor : ∀ i, S i) : IsDirected (FDir anchor) (· ≤ ·) where
  directed T U := by
    refine ⟨⟨fun i => T.1 i ∪ U.1 i, ?_⟩, fun i => Finset.subset_union_left, fun i => Finset.subset_union_right⟩
    refine ⟨⟨fun i => ?_, ?_⟩, fun i => ?_⟩
    · exact (T.2.1.1 i).mono Finset.subset_union_left
    · apply (T.2.1.2.union U.2.1.2).subset
      intro i hi
      by_contra hn
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hn
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hn
      apply hi
      have h1 : anchor i ∈ T.1 i := T.2.2 i
      have h2 : anchor i ∈ U.1 i := U.2.2 i
      rw [ha] at h1; rw [hb] at h2
      simp only [Finset.mem_singleton] at h1 h2
      refine ⟨anchor i, ?_⟩
      show T.1 i ∪ U.1 i = {anchor i}
      rw [ha, hb, ← h1, ← h2]
      simp
    · exact Finset.mem_union_left _ (T.2.2 i)

instance (anchor : ∀ i, S i) : Nonempty (FDir anchor) := by
  refine ⟨⟨fun i => {anchor i}, ⟨fun i => ⟨anchor i, by simp⟩, ?_⟩, fun i => by simp⟩⟩
  apply (Set.finite_empty).subset
  intro i hi
  exact absurd ⟨anchor i, rfl⟩ hi

lemma fsetMeasure_prob (F : Finset (∀ i, S i)) (w : (∀ i, S i) → ℝ) (hw : ∀ s ∈ F, 0 ≤ w s)
    (h1 : ∑ s ∈ F, w s = 1) : IsProbabilityMeasure (fsetMeasure F w) := by
  refine ⟨?_⟩
  simp only [fsetMeasure, Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg hw, h1]
  simp

lemma fsetMeasure_integral (F : Finset (∀ i, S i)) (w : (∀ i, S i) → ℝ) (hw : ∀ s ∈ F, 0 ≤ w s)
    (f : C(∀ i, S i, ℝ)) : ∫ s, f s ∂(fsetMeasure F w) = ∑ s ∈ F, w s * f s := by
  unfold fsetMeasure
  rw [integral_finset_sum_measure]
  · apply Finset.sum_congr rfl
    intro s hs
    rw [integral_smul_measure, integral_dirac' _ _ (meas_of_cont f).stronglyMeasurable,
      ENNReal.toReal_ofReal (hw s hs), smul_eq_mul]
  · intro s _
    exact (integrable_cont _ f).smul_measure ENNReal.ofReal_ne_top

theorem goal_core (h : ι → (∀ i, S i) → ℝ) (hh : ∀ i, Continuous (h i)) :
    ∃ μ : Measure (∀ i, S i), IsCorrelatedEq h μ := by
  let anchor : ∀ i, S i := fun i => Classical.arbitrary (S i)
  have hex : ∀ T : (∀ i, Finset (S i)), ∃ (F : Finset (∀ i, S i)) (w : (∀ i, S i) → ℝ),
      IsFSet T → IsFSetCE h T F w := by
    intro T
    by_cases hT : IsFSet T
    · obtain ⟨F, w, hFw⟩ := fset_core h T hT
      exact ⟨F, w, fun _ => hFw⟩
    · exact ⟨∅, fun _ => 0, fun h' => absurd h' hT⟩
  choose F w hFw using hex
  let q : FDir anchor → Measure (∀ i, S i) := fun d => fsetMeasure (F d.1) (w d.1)
  have hq : ∀ d, IsProbabilityMeasure (q d) := fun d =>
    fsetMeasure_prob _ _ (hFw d.1 d.2.1).2.1 (hFw d.1 d.2.1).2.2.1
  obtain ⟨p, hp, hcl⟩ := ecp_core q hq
  refine ⟨p, cp_core h hh anchor F w (fun T hT => hFw T hT.1) p hp ?_⟩
  intro f ε hε T₀ hT₀
  obtain ⟨d, hd, hlt⟩ := hcl {f} ε hε ⟨T₀, hT₀⟩
  refine ⟨d.1, d.2, hd, ?_⟩
  have := hlt f (Finset.mem_singleton_self f)
  rwa [show ∫ s, f s ∂(q d) = ∑ s ∈ F d.1, w d.1 s * f s from
    fsetMeasure_integral _ _ (hFw d.1 d.2.1).2.1 f] at this

end

section
open HartSchmeidler.FinStrat
open MeasureTheory

theorem solution {ι : Type*} [Nonempty ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    [∀ i, Nonempty (S i)]
    [∀ i, TopologicalSpace (S i)] [∀ i, DiscreteTopology (S i)]
    [∀ i, MeasurableSpace (S i)] [∀ i, DiscreteMeasurableSpace (S i)]
    (h : ι → (∀ i, S i) → ℝ) (hh : ∀ i, Continuous (h i)) :
    ∃ μ : Measure (∀ i, S i), IsCorrelatedEq h μ := by
  exact goal_core h hh

end
