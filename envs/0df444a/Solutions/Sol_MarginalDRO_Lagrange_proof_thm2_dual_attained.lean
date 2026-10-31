-- Prove2me | solution 1 for MarginalDRO.Lagrange.proof_thm2_dual_attained
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T10:03:45.01606+00:00
-- url     : https://prove2.me/submissions/1ff16b9f-69f4-4214-85c0-7da3d8e96c91

import Mathlib
import Definitions.Def_MarginalDRO_Lagrange_Model

open MeasureTheory ProbabilityTheory
open MarginalDRO.Lagrange

namespace MDROaux

variable {n : ℕ}

lemma proj_mem {𝒳 : Finset (Fin n → ℝ)} {x : Fin n → ℝ} (hx : x ∈ 𝒳) (i : Fin n) :
    x i ∈ proj 𝒳 i := Finset.mem_image_of_mem _ hx

lemma mem_proj {𝒳 : Finset (Fin n → ℝ)} {i : Fin n} {a : ℝ} (ha : a ∈ proj 𝒳 i) :
    ∃ x ∈ 𝒳, x i = a := by simpa [proj] using ha

lemma sup'_le_sup'_add {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (f g : ι → ℝ) (d : ℝ)
    (h : ∀ i ∈ s, f i ≤ g i + d) : s.sup' hs f ≤ s.sup' hs g + d :=
  Finset.sup'_le _ _ fun i hi => (h i hi).trans (by linarith [Finset.le_sup' g hi])

lemma sup'_sub_const {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (f : ι → ℝ) (k : ℝ) :
    s.sup' hs (fun i => f i - k) = s.sup' hs f - k := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun i hi => by linarith [Finset.le_sup' f hi]
  · have := sup'_le_sup'_add hs f (fun i => f i - k) k (fun i _ => by simp)
    linarith

lemma proj_nonempty {𝒳 : Finset (Fin n → ℝ)} (h𝒳 : 𝒳.Nonempty) (i : Fin n) :
    (proj 𝒳 i).Nonempty := h𝒳.image _

lemma conj_def (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty) (ψi : ℝ → ℝ) (i : Fin n) (c : ℝ) :
    conj 𝒳 h𝒳 ψi i c = (proj 𝒳 i).sup' (proj_nonempty h𝒳 i) (fun a => c * a - ψi a) := rfl

lemma conj_eq_fun (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty) (ψi : ℝ → ℝ) (i : Fin n) :
    conj 𝒳 h𝒳 ψi i = (proj 𝒳 i).sup' (proj_nonempty h𝒳 i) (fun a (c : ℝ) => c * a - ψi a) := by
  funext c; rw [Finset.sup'_apply]; rfl

lemma conj_measurable (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty) (ψi : ℝ → ℝ) (i : Fin n) :
    Measurable (conj 𝒳 h𝒳 ψi i) := by
  rw [conj_eq_fun]
  exact Finset.measurable_sup' _ fun a _ => by fun_prop

lemma conj_abs_le (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty) (ψi : ℝ → ℝ) (i : Fin n) (c : ℝ) :
    |conj 𝒳 h𝒳 ψi i c| ≤ |c| * (∑ a ∈ proj 𝒳 i, |a|) + ∑ a ∈ proj 𝒳 i, |ψi a| := by
  obtain ⟨a, ha, hca⟩ := Finset.exists_mem_eq_sup' (proj_nonempty h𝒳 i)
    (fun a => c * a - ψi a)
  rw [conj_def, hca]
  have h1 : |a| ≤ ∑ a ∈ proj 𝒳 i, |a| :=
    Finset.single_le_sum (f := fun a : ℝ => |a|) (fun _ _ => abs_nonneg _) ha
  have h2 : |ψi a| ≤ ∑ a ∈ proj 𝒳 i, |ψi a| :=
    Finset.single_le_sum (f := fun a : ℝ => |ψi a|) (fun _ _ => abs_nonneg _) ha
  calc |c * a - ψi a| ≤ |c * a| + |ψi a| := abs_sub _ _
    _ = |c| * |a| + |ψi a| := by rw [abs_mul]
    _ ≤ _ := by gcongr

lemma conj_integrable (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty) (ψi : ℝ → ℝ) (i : Fin n)
    (m : Measure ℝ) [IsFiniteMeasure m] (hm : Integrable id m) :
    Integrable (conj 𝒳 h𝒳 ψi i) m := by
  refine Integrable.mono' (g := fun c => |c| * (∑ a ∈ proj 𝒳 i, |a|) + ∑ a ∈ proj 𝒳 i, |ψi a|)
    ((hm.abs.mul_const _).add (integrable_const _))
    (conj_measurable 𝒳 h𝒳 ψi i).aestronglyMeasurable (Filter.Eventually.of_forall fun c => ?_)
  rw [Real.norm_eq_abs]; exact conj_abs_le 𝒳 h𝒳 ψi i c

lemma conj_le_add (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty) (ψ ψ' : ℝ → ℝ) (i : Fin n) (d : ℝ)
    (h : ∀ a ∈ proj 𝒳 i, ψ' a ≤ ψ a + d) (c : ℝ) :
    conj 𝒳 h𝒳 ψ i c ≤ conj 𝒳 h𝒳 ψ' i c + d :=
  sup'_le_sup'_add _ _ _ _ fun a ha => by linarith [h a ha]

lemma conj_congr (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty) (ψ ψ' : ℝ → ℝ) (i : Fin n)
    (h : ∀ a ∈ proj 𝒳 i, ψ a = ψ' a) : conj 𝒳 h𝒳 ψ i = conj 𝒳 h𝒳 ψ' i := by
  funext c
  apply le_antisymm
  · simpa using conj_le_add 𝒳 h𝒳 ψ ψ' i 0 (fun a ha => by rw [h a ha]; simp) c
  · simpa using conj_le_add 𝒳 h𝒳 ψ' ψ i 0 (fun a ha => by rw [h a ha]; simp) c

lemma conj_sub_const (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty) (ψ : ℝ → ℝ) (i : Fin n) (k : ℝ)
    (c : ℝ) : conj 𝒳 h𝒳 (fun a => ψ a - k) i c = conj 𝒳 h𝒳 ψ i c + k := by
  have := sup'_sub_const (proj_nonempty h𝒳 i) (fun a => c * a - ψ a) (-k)
  simp only [sub_neg_eq_add] at this
  rw [conj_def, conj_def, show (fun a => c * a - (ψ a - k)) = (fun a => c * a - ψ a + k) by funext a; ring, this]

/-- The dual objective `sup_ν L(ψ, ν)`. -/
noncomputable def D (μ : Fin n → Measure ℝ) (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty)
    (ψ : Fin n → ℝ → ℝ) : ℝ :=
  𝒳.sup' h𝒳 (fun x => ∑ i, ψ i (x i)) + ∑ i, ∫ c, conj 𝒳 h𝒳 (ψ i) i c ∂(μ i)

lemma lagrangian_eq (μ : Fin n → Measure ℝ) (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty)
    (ψ : Fin n → ℝ → ℝ) (ν : 𝒳 → ℝ) :
    lagrangian μ 𝒳 h𝒳 ψ ν = ∑ x : 𝒳, ν x * ∑ i, ψ i ((x : Fin n → ℝ) i) +
      ∑ i, ∫ c, conj 𝒳 h𝒳 (ψ i) i c ∂(μ i) := by
  simp only [lagrangian, Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma isGreatest_D (μ : Fin n → Measure ℝ) (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty)
    (ψ : Fin n → ℝ → ℝ) :
    IsGreatest ((fun ν => lagrangian μ 𝒳 h𝒳 ψ ν) '' stdSimplex ℝ 𝒳) (D μ 𝒳 h𝒳 ψ) := by
  classical
  obtain ⟨x0, hx0, hmax⟩ := Finset.exists_mem_eq_sup' h𝒳 (fun x => ∑ i, ψ i (x i))
  constructor
  · refine ⟨Pi.single ⟨x0, hx0⟩ 1, single_mem_stdSimplex ℝ _, ?_⟩
    simp only [lagrangian_eq, D, hmax]
    congr 1
    rw [Finset.sum_eq_single ⟨x0, hx0⟩]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  · rintro _ ⟨ν, hν, rfl⟩
    simp only [lagrangian_eq, D]
    gcongr
    calc ∑ x : 𝒳, ν x * ∑ i, ψ i ((x : Fin n → ℝ) i)
        ≤ ∑ x : 𝒳, ν x * 𝒳.sup' h𝒳 (fun x => ∑ i, ψ i (x i)) :=
          Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
            (Finset.le_sup' (fun x : Fin n → ℝ => ∑ i, ψ i (x i)) x.2) (hν.1 x)
      _ = _ := by rw [← Finset.sum_mul, hν.2, one_mul]

lemma D_congr (μ : Fin n → Measure ℝ) (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty)
    (ψ ψ' : Fin n → ℝ → ℝ) (h : ∀ i, ∀ a ∈ proj 𝒳 i, ψ i a = ψ' i a) :
    D μ 𝒳 h𝒳 ψ = D μ 𝒳 h𝒳 ψ' := by
  simp only [D]
  congr 1
  · exact Finset.sup'_congr _ rfl fun x hx =>
      Finset.sum_congr rfl fun i _ => h i (x i) (proj_mem hx i)
  · exact Finset.sum_congr rfl fun i _ => by rw [conj_congr 𝒳 h𝒳 (ψ i) (ψ' i) i (h i)]

lemma D_shift (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hint : ∀ i, Integrable id (μ i)) (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty)
    (ψ : Fin n → ℝ → ℝ) (k : Fin n → ℝ) :
    D μ 𝒳 h𝒳 (fun i a => ψ i a - k i) = D μ 𝒳 h𝒳 ψ := by
  simp only [D]
  have h1 : 𝒳.sup' h𝒳 (fun x => ∑ i, (ψ i (x i) - k i)) =
      𝒳.sup' h𝒳 (fun x => ∑ i, ψ i (x i)) - ∑ i, k i := by
    rw [← sup'_sub_const]
    exact Finset.sup'_congr _ rfl fun x _ => Finset.sum_sub_distrib _ _
  have h2 : ∀ i, ∫ c, conj 𝒳 h𝒳 (fun a => ψ i a - k i) i c ∂(μ i) =
      ∫ c, conj 𝒳 h𝒳 (ψ i) i c ∂(μ i) + k i := by
    intro i
    simp_rw [conj_sub_const]
    rw [integral_add (conj_integrable 𝒳 h𝒳 _ i _ (hint i)) (integrable_const _),
      integral_const]
    simp
  rw [h1, Finset.sum_congr rfl fun i _ => h2 i, Finset.sum_add_distrib]
  ring

lemma D_lower (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hint : ∀ i, Integrable id (μ i)) (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty)
    (ψ : Fin n → ℝ → ℝ) (hnn : ∀ i, ∀ a ∈ proj 𝒳 i, 0 ≤ ψ i a)
    (hz : ∀ i, ∃ a ∈ proj 𝒳 i, ψ i a = 0) (i0 : Fin n) (a : ℝ) (ha : a ∈ proj 𝒳 i0) :
    ψ i0 a ≤ D μ 𝒳 h𝒳 ψ + ∑ i, (∫ c, |c| ∂(μ i)) * ∑ b ∈ proj 𝒳 i, |b| := by
  obtain ⟨x, hx, rfl⟩ := mem_proj ha
  have h1 : ψ i0 (x i0) ≤ 𝒳.sup' h𝒳 (fun x => ∑ i, ψ i (x i)) :=
    (Finset.single_le_sum (f := fun i => ψ i (x i)) (fun i _ => hnn i _ (proj_mem hx i))
      (Finset.mem_univ i0)).trans (Finset.le_sup' (fun x : Fin n → ℝ => ∑ i, ψ i (x i)) hx)
  have h2 : ∀ i, -((∫ c, |c| ∂(μ i)) * ∑ b ∈ proj 𝒳 i, |b|) ≤
      ∫ c, conj 𝒳 h𝒳 (ψ i) i c ∂(μ i) := by
    intro i
    obtain ⟨a0, ha0, hz0⟩ := hz i
    rw [← neg_mul, ← integral_neg, ← integral_mul_const]
    refine integral_mono ((hint i).abs.neg.mul_const _) (conj_integrable 𝒳 h𝒳 _ i _ (hint i))
      fun c => ?_
    have h3 : c * a0 - ψ i a0 ≤ conj 𝒳 h𝒳 (ψ i) i c := by
      rw [conj_def]; exact Finset.le_sup' (fun a => c * a - ψ i a) ha0
    have h4 : |a0| ≤ ∑ b ∈ proj 𝒳 i, |b| :=
      Finset.single_le_sum (f := fun b : ℝ => |b|) (fun _ _ => abs_nonneg _) ha0
    have h5 : -(|c| * |a0|) ≤ c * a0 := by rw [← abs_mul]; exact neg_abs_le _
    have h6 : |c| * |a0| ≤ |c| * ∑ b ∈ proj 𝒳 i, |b| := mul_le_mul_of_nonneg_left h4 (abs_nonneg _)
    simp only [Pi.neg_apply, id]
    rw [hz0] at h3
    linarith
  have h7 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h2 i
  simp only [Finset.sum_neg_distrib] at h7
  simp only [D]
  linarith

end MDROaux

open MDROaux in
theorem solution {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hvar : ∀ i, MemLp id 2 (μ i)) (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty) :
    ∃ ψstar : Fin n → ℝ → ℝ, ∃ s : ℝ,
      IsLUB ((fun ν => lagrangian μ 𝒳 h𝒳 ψstar ν) '' stdSimplex ℝ 𝒳) s ∧
      ∀ (ψ : Fin n → ℝ → ℝ) (s' : ℝ),
        IsLUB ((fun ν => lagrangian μ 𝒳 h𝒳 ψ ν) '' stdSimplex ℝ 𝒳) s' → s ≤ s' := by
  classical
  have hint : ∀ i, Integrable id (μ i) := fun i => (hvar i).integrable (by norm_num)
  -- finite-dimensional parametrisation of the relevant values of ψ
  let ext : ((i : Fin n) × {a // a ∈ proj 𝒳 i} → ℝ) → Fin n → ℝ → ℝ :=
    fun φ i a => if h : a ∈ proj 𝒳 i then φ ⟨i, a, h⟩ else 0
  have hext : ∀ φ i a (h : a ∈ proj 𝒳 i), ext φ i a = φ ⟨i, a, h⟩ := fun φ i a h => dif_pos h
  let f : ((i : Fin n) × {a // a ∈ proj 𝒳 i} → ℝ) → ℝ := fun φ => D μ 𝒳 h𝒳 (ext φ)
  have hlip : ∀ φ φ', f φ ≤ f φ' + (2 * n) * dist φ φ' := by
    intro φ φ'
    have hd : ∀ i, ∀ a ∈ proj 𝒳 i, |ext φ i a - ext φ' i a| ≤ dist φ φ' := by
      intro i a ha
      rw [hext φ i a ha, hext φ' i a ha, ← Real.dist_eq]
      exact dist_le_pi_dist φ φ' _
    have h1 : 𝒳.sup' h𝒳 (fun x => ∑ i, ext φ i (x i)) ≤
        𝒳.sup' h𝒳 (fun x => ∑ i, ext φ' i (x i)) + n * dist φ φ' := by
      refine sup'_le_sup'_add _ _ _ _ fun x hx => ?_
      have : ∑ i, ext φ i (x i) ≤ ∑ i, (ext φ' i (x i) + dist φ φ') :=
        Finset.sum_le_sum fun i _ => by
          linarith [(abs_le.mp (hd i (x i) (proj_mem hx i))).2]
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul] at this
      exact this
    have h2 : ∀ i, ∫ c, conj 𝒳 h𝒳 (ext φ i) i c ∂(μ i) ≤
        ∫ c, conj 𝒳 h𝒳 (ext φ' i) i c ∂(μ i) + dist φ φ' := by
      intro i
      have hI := conj_integrable 𝒳 h𝒳 (ext φ i) i _ (hint i)
      have hI' := conj_integrable 𝒳 h𝒳 (ext φ' i) i _ (hint i)
      calc ∫ c, conj 𝒳 h𝒳 (ext φ i) i c ∂(μ i)
          ≤ ∫ c, (conj 𝒳 h𝒳 (ext φ' i) i c + dist φ φ') ∂(μ i) :=
            integral_mono hI (hI'.add (integrable_const (dist φ φ')))
              (conj_le_add 𝒳 h𝒳 (ext φ i) (ext φ' i) i (dist φ φ') (fun a ha => by
                linarith [(abs_le.mp (hd i a ha)).1]))
        _ = ∫ c, conj 𝒳 h𝒳 (ext φ' i) i c ∂(μ i) + dist φ φ' := by
            rw [integral_add hI' (integrable_const _), integral_const]; simp
    have h3 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h2 i
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at h3
    simp only [f, D]
    nlinarith
  have hfc : Continuous f := (LipschitzWith.of_le_add_mul' (2 * n) hlip).continuous
  set C : ℝ := ∑ i, (∫ c, |c| ∂(μ i)) * ∑ b ∈ proj 𝒳 i, |b| with hC
  set R : ℝ := max 0 (f 0 + C) with hR
  have h0K : (0 : (i : Fin n) × {a // a ∈ proj 𝒳 i} → ℝ) ∈ Set.Icc 0 (fun _ => R) :=
    ⟨le_rfl, fun _ => le_max_left _ _⟩
  obtain ⟨φs, hφsK, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨_, h0K⟩ hfc.continuousOn
  refine ⟨ext φs, D μ 𝒳 h𝒳 (ext φs), (isGreatest_D μ 𝒳 h𝒳 _).isLUB, fun ψ s' hs' => ?_⟩
  rw [hs'.unique (isGreatest_D μ 𝒳 h𝒳 ψ).isLUB]
  -- normalise ψ
  set k : Fin n → ℝ := fun i => (proj 𝒳 i).inf' (proj_nonempty h𝒳 i) (ψ i) with hk
  set ψt : Fin n → ℝ → ℝ := fun i a => ψ i a - k i with hψt
  have hDt : D μ 𝒳 h𝒳 ψt = D μ 𝒳 h𝒳 ψ := D_shift μ hint 𝒳 h𝒳 ψ k
  have hnn : ∀ i, ∀ a ∈ proj 𝒳 i, 0 ≤ ψt i a := fun i a ha => by
    simp only [ψt, k]; linarith [Finset.inf'_le (ψ i) ha]
  have hz : ∀ i, ∃ a ∈ proj 𝒳 i, ψt i a = 0 := fun i => by
    obtain ⟨a, ha, h⟩ := Finset.exists_mem_eq_inf' (proj_nonempty h𝒳 i) (ψ i)
    exact ⟨a, ha, by simp only [ψt, k]; rw [h]; ring⟩
  rw [← hDt]
  by_cases hbox : ∀ i, ∀ a ∈ proj 𝒳 i, ψt i a ≤ R
  · let φ : (i : Fin n) × {a // a ∈ proj 𝒳 i} → ℝ := fun e => ψt e.1 e.2.1
    have hφK : φ ∈ Set.Icc 0 (fun _ => R) :=
      ⟨fun e => hnn e.1 e.2.1 e.2.2, fun e => hbox e.1 e.2.1 e.2.2⟩
    have : f φ = D μ 𝒳 h𝒳 ψt := D_congr μ 𝒳 h𝒳 _ _ fun i a ha => hext φ i a ha
    rw [← this]
    exact hmin hφK
  · simp only [not_forall, not_le] at hbox
    obtain ⟨i, a, ha, hlt⟩ := hbox
    have h1 := D_lower μ hint 𝒳 h𝒳 ψt hnn hz i a ha
    have h2 : f φs ≤ f 0 := hmin h0K
    have h3 : f 0 + C ≤ R := le_max_right _ _
    show f φs ≤ _
    linarith
