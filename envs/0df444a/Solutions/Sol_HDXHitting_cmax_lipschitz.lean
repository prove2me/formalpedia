-- Prove2me | solution 1 for HDXHitting.cmax_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:07:53.123987+00:00
-- url     : https://prove2.me/submissions/31f2f5d8-24ae-422b-801c-b2fcb6811f8e

import Mathlib
import Definitions.Def_HDXHitting_IsTopDist
import Definitions.Def_HDXHitting_vertexMeasure
import Definitions.Def_HDXHitting_mean
import Definitions.Def_HDXHitting_hit
import Definitions.Def_HDXHitting_cMax

section
set_option autoImplicit false
namespace HDXHitting.Dev.CL
open HDXHitting

theorem sum_vertex {V : Type*} [Fintype V] [DecidableEq V] (p : Finset V → ℝ) (x : V → ℝ) :
    ∑ σ : Finset V, p σ * ∑ v ∈ σ, x v =
      ∑ v : V, x v * ∑ σ ∈ Finset.univ.filter (fun σ : Finset V => v ∈ σ), p σ := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm' (s' := fun v => Finset.univ.filter (fun σ : Finset V => v ∈ σ))
    (t' := Finset.univ)]
  · apply Finset.sum_congr rfl; intro v _; apply Finset.sum_congr rfl; intros; ring
  · intro σ v; simp

theorem sum_pi {V : Type*} [Fintype V] [DecidableEq V] (d : ℕ) (hd : 1 ≤ d) (p : Finset V → ℝ)
    (hp : IsTopDist d p) : ∑ v, vertexMeasure d p v = 1 := by
  have h := sum_vertex p (fun _ => (1 : ℝ))
  simp only [one_mul, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  have h2 : ∑ σ : Finset V, p σ * (σ.card : ℝ) = d := by
    calc ∑ σ : Finset V, p σ * (σ.card : ℝ) = ∑ σ : Finset V, p σ * d := by
          apply Finset.sum_congr rfl; intro σ _
          by_cases h0 : p σ = 0
          · simp [h0]
          · rw [hp.2.1 σ h0]
      _ = d := by rw [← Finset.sum_mul, hp.2.2]; ring
  unfold vertexMeasure
  rw [← Finset.mul_sum, ← h, h2]
  have : (d : ℝ) ≠ 0 := by positivity
  field_simp

theorem prod_diff {V : Type*} [DecidableEq V] (a b : V → ℝ) (ha : ∀ v, 0 ≤ a v)
    (hab : ∀ v, a v ≤ b v) (hb : ∀ v, b v ≤ 1) (σ : Finset V) :
    ∏ v ∈ σ, b v - ∏ v ∈ σ, a v ≤ ∑ v ∈ σ, (b v - a v) := by
  induction σ using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.prod_insert hx, Finset.sum_insert hx]
    have hA : 0 ≤ ∏ v ∈ s, a v := Finset.prod_nonneg (fun v _ => ha v)
    have hA1 : ∏ v ∈ s, a v ≤ 1 := Finset.prod_le_one (fun v _ => ha v) (fun v _ => (hab v).trans (hb v))
    have hBA : ∏ v ∈ s, a v ≤ ∏ v ∈ s, b v := Finset.prod_le_prod (fun v _ => ha v) (fun v _ => hab v)
    have hb0 : 0 ≤ b x := (ha x).trans (hab x)
    nlinarith [mul_nonneg (sub_nonneg.2 (hb x)) (sub_nonneg.2 hBA),
      mul_nonneg (sub_nonneg.2 (hab x)) (sub_nonneg.2 hA1)]

theorem hit_mono {V : Type*} [Fintype V] [DecidableEq V] (d : ℕ) (p : Finset V → ℝ)
    (hp : IsTopDist d p) (a b : V → ℝ) (ha : ∀ v, 0 ≤ a v) (hab : ∀ v, a v ≤ b v) :
    hit p a ≤ hit p b := by
  unfold hit
  apply Finset.sum_le_sum; intro σ _
  exact mul_le_mul_of_nonneg_left
    (Finset.prod_le_prod (fun v _ => ha v) (fun v _ => hab v)) (hp.1 σ)

theorem hit_le_one {V : Type*} [Fintype V] [DecidableEq V] (d : ℕ) (p : Finset V → ℝ)
    (hp : IsTopDist d p) (a : V → ℝ) (ha : ∀ v, 0 ≤ a v ∧ a v ≤ 1) : hit p a ≤ 1 := by
  unfold hit
  calc ∑ σ : Finset V, p σ * ∏ v ∈ σ, a v ≤ ∑ σ : Finset V, p σ * 1 := by
        apply Finset.sum_le_sum; intro σ _
        exact mul_le_mul_of_nonneg_left (Finset.prod_le_one (fun v _ => (ha v).1)
          (fun v _ => (ha v).2)) (hp.1 σ)
    _ = 1 := by simp [hp.2.2]

theorem hit_diff {V : Type*} [Fintype V] [DecidableEq V] (d : ℕ) (hd : 1 ≤ d) (p : Finset V → ℝ)
    (hp : IsTopDist d p) (a b : V → ℝ) (ha : ∀ v, 0 ≤ a v) (hab : ∀ v, a v ≤ b v)
    (hb : ∀ v, b v ≤ 1) :
    hit p b - hit p a ≤ d * (mean d p b - mean d p a) := by
  have h1 : hit p b - hit p a = ∑ σ : Finset V, p σ * (∏ v ∈ σ, b v - ∏ v ∈ σ, a v) := by
    unfold hit; rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intros; ring
  have h2 : ∑ σ : Finset V, p σ * (∏ v ∈ σ, b v - ∏ v ∈ σ, a v) ≤
      ∑ σ : Finset V, p σ * ∑ v ∈ σ, (b v - a v) := by
    apply Finset.sum_le_sum; intro σ _
    exact mul_le_mul_of_nonneg_left (prod_diff a b ha hab hb σ) (hp.1 σ)
  rw [sum_vertex] at h2
  have h3 : (d : ℝ) * (mean d p b - mean d p a) =
      ∑ v : V, (b v - a v) * ∑ σ ∈ Finset.univ.filter (fun σ : Finset V => v ∈ σ), p σ := by
    unfold mean vertexMeasure
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro v _
    have : (d : ℝ) ≠ 0 := by positivity
    field_simp
  linarith

end HDXHitting.Dev.CL
namespace HDXHitting
open HDXHitting.Dev.CL in
theorem chk_cmax_lipschitz {V : Type*} [Fintype V] [DecidableEq V] (d : ℕ) (hd : 1 ≤ d)
    (p : Finset V → ℝ) (hp : IsTopDist d p) :
    (∀ μ : ℝ, 0 ≤ μ → μ ≤ 1 → ∃ f : V → ℝ, (∀ v, 0 ≤ f v ∧ f v ≤ 1) ∧ mean d p f = μ ∧
        hit p f = cMax d p μ) ∧
      (∀ μ μ' : ℝ, 0 ≤ μ → μ ≤ 1 → 0 ≤ μ' → μ' ≤ 1 →
        |cMax d p μ - cMax d p μ'| ≤ d * |μ - μ'|) := by
  have hcont_hit : Continuous (hit p) := by unfold hit; fun_prop
  have hcont_mean : Continuous (mean d p) := by unfold mean; fun_prop
  have hle : ∀ μ : ℝ, ∀ g : V → ℝ, (∀ v, 0 ≤ g v ∧ g v ≤ 1) → mean d p g = μ →
      hit p g ≤ cMax d p μ := by
    intro μ g hg hm
    unfold cMax
    apply le_csSup
    · refine ⟨1, ?_⟩
      rintro _ ⟨h, hh, rfl⟩
      exact hit_le_one d p hp h hh.1
    · exact ⟨g, ⟨hg, hm⟩, rfl⟩
  have hmean_const : ∀ μ : ℝ, mean d p (fun _ => μ) = μ := by
    intro μ
    unfold mean
    rw [← Finset.sum_mul, sum_pi d hd p hp, one_mul]
  have attain : ∀ μ : ℝ, 0 ≤ μ → μ ≤ 1 → ∃ f : V → ℝ, (∀ v, 0 ≤ f v ∧ f v ≤ 1) ∧
      mean d p f = μ ∧ hit p f = cMax d p μ := by
    intro μ h0 h1
    have hK : {f : V → ℝ | (∀ v, 0 ≤ f v ∧ f v ≤ 1) ∧ mean d p f = μ} =
        (Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1) ∩ {f | mean d p f = μ} := by
      ext f
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_pi, Set.mem_univ, Set.mem_Icc,
        forall_true_left]
    have hcomp : IsCompact {f : V → ℝ | (∀ v, 0 ≤ f v ∧ f v ≤ 1) ∧ mean d p f = μ} := by
      rw [hK]
      exact (isCompact_univ_pi (fun _ => isCompact_Icc)).inter_right
        (isClosed_eq hcont_mean continuous_const)
    have hne : {f : V → ℝ | (∀ v, 0 ≤ f v ∧ f v ≤ 1) ∧ mean d p f = μ}.Nonempty :=
      ⟨fun _ => μ, fun _ => ⟨h0, h1⟩, hmean_const μ⟩
    obtain ⟨f, hf, hmax⟩ := hcomp.exists_isMaxOn hne hcont_hit.continuousOn
    refine ⟨f, hf.1, hf.2, ?_⟩
    unfold cMax
    symm
    apply IsGreatest.csSup_eq
    refine ⟨⟨f, hf, rfl⟩, ?_⟩
    rintro _ ⟨g, hg, rfl⟩
    exact isMaxOn_iff.mp hmax g hg
  have key : ∀ μ μ' : ℝ, 0 ≤ μ → μ ≤ μ' → μ' ≤ 1 →
      cMax d p μ ≤ cMax d p μ' ∧ cMax d p μ' ≤ cMax d p μ + d * (μ' - μ) := by
    intro μ μ' h0 h1 h2
    obtain ⟨f, hf, hfm, hfe⟩ := attain μ h0 (h1.trans h2)
    obtain ⟨g, hg, hgm, hge⟩ := attain μ' (h0.trans h1) h2
    constructor
    · by_cases hμ : μ = 1
      · have : μ' = μ := by linarith
        rw [this]
      · have hμ1 : μ < 1 := lt_of_le_of_ne (h1.trans h2) hμ
        set t : ℝ := (μ' - μ) / (1 - μ) with ht
        have ht0 : 0 ≤ t := div_nonneg (by linarith) (by linarith)
        have ht1 : t ≤ 1 := by
          rw [ht, div_le_one (by linarith)]; linarith
        have hf' : ∀ v, 0 ≤ f v + t * (1 - f v) ∧ f v + t * (1 - f v) ≤ 1 := by
          intro v
          have := hf v
          constructor <;> nlinarith [this.1, this.2]
        have hm' : mean d p (fun v => f v + t * (1 - f v)) = μ' := by
          have e : mean d p (fun v => f v + t * (1 - f v)) =
              mean d p f + t * (1 - mean d p f) := by
            unfold mean
            have := sum_pi d hd p hp
            have h1' : (1 : ℝ) - ∑ v, vertexMeasure d p v * f v =
                ∑ v, vertexMeasure d p v - ∑ v, vertexMeasure d p v * f v := by rw [this]
            rw [h1', ← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl; intros; ring
          rw [e, hfm, ht]
          field_simp
          ring
        calc cMax d p μ = hit p f := hfe.symm
          _ ≤ hit p (fun v => f v + t * (1 - f v)) :=
            hit_mono d p hp _ _ (fun v => (hf v).1) (fun v => by nlinarith [(hf v).2])
          _ ≤ cMax d p μ' := hle μ' _ hf' hm'
    · by_cases hμ' : μ' = 0
      · have : μ = μ' := by linarith
        rw [this]; simp
      · have hpos : 0 < μ' := lt_of_le_of_ne (h0.trans h1) (Ne.symm hμ')
        set s : ℝ := μ / μ' with hs
        have hs0 : 0 ≤ s := div_nonneg h0 hpos.le
        have hs1 : s ≤ 1 := by rw [hs, div_le_one hpos]; exact h1
        have hg' : ∀ v, 0 ≤ s * g v ∧ s * g v ≤ 1 := by
          intro v
          have := hg v
          constructor <;> nlinarith [this.1, this.2]
        have hm' : mean d p (fun v => s * g v) = μ := by
          have e : mean d p (fun v => s * g v) = s * mean d p g := by
            unfold mean
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
          rw [e, hgm, hs]; field_simp
        have hd' := hit_diff d hd p hp (fun v => s * g v) g (fun v => (hg' v).1)
          (fun v => by nlinarith [(hg v).1]) (fun v => (hg v).2)
        have hh := hle μ _ hg' hm'
        have : mean d p (fun v => s * g v) = μ := hm'
        rw [this, hgm] at hd'
        linarith
  refine ⟨attain, ?_⟩
  intro μ μ' h0 h1 h0' h1'
  rcases le_total μ μ' with h | h
  · have := key μ μ' h0 h h1'
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    have hd0 : (0 : ℝ) ≤ d := by positivity
    nlinarith
  · have := key μ' μ h0' h h1
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    nlinarith
end HDXHitting
end

theorem solution : type_of% @HDXHitting.chk_cmax_lipschitz := @HDXHitting.chk_cmax_lipschitz
