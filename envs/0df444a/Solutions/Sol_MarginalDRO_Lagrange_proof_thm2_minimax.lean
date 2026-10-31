-- Prove2me | solution 1 for MarginalDRO.Lagrange.proof_thm2_minimax
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T10:06:00.767545+00:00
-- url     : https://prove2.me/submissions/decabf5e-ec73-421f-9123-05c1e266bfc3

import Mathlib
import Definitions.Def_MarginalDRO_Lagrange_Model
import Theorems.Thm_MarginalDRO_Lagrange_proof_thm2_dual_attained

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

lemma conj_convex (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty) (ψ₁ ψ₂ : ℝ → ℝ) (i : Fin n)
    (t s : ℝ) (ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t + s = 1) (c : ℝ) :
    conj 𝒳 h𝒳 (fun a => t * ψ₁ a + s * ψ₂ a) i c ≤
      t * conj 𝒳 h𝒳 ψ₁ i c + s * conj 𝒳 h𝒳 ψ₂ i c := by
  rw [conj_def]
  refine Finset.sup'_le _ _ fun a ha => ?_
  have h1 : c * a - ψ₁ a ≤ conj 𝒳 h𝒳 ψ₁ i c := by
    rw [conj_def]; exact Finset.le_sup' (fun a => c * a - ψ₁ a) ha
  have h2 : c * a - ψ₂ a ≤ conj 𝒳 h𝒳 ψ₂ i c := by
    rw [conj_def]; exact Finset.le_sup' (fun a => c * a - ψ₂ a) ha
  have e : c * a - (t * ψ₁ a + s * ψ₂ a) = t * (c * a - ψ₁ a) + s * (c * a - ψ₂ a) := by
    have : c * a = (t + s) * (c * a) := by rw [hts, one_mul]
    linarith [this]
  rw [e]
  exact add_le_add (mul_le_mul_of_nonneg_left h1 ht) (mul_le_mul_of_nonneg_left h2 hs)

end MDROaux

open MDROaux in
theorem solution {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hvar : ∀ i, MemLp id 2 (μ i)) (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty) :
    ∃ v : ℝ,
      IsGreatest {s | ∃ ν ∈ stdSimplex ℝ 𝒳,
        IsGLB (Set.range fun ψ : Fin n → ℝ → ℝ => lagrangian μ 𝒳 h𝒳 ψ ν) s} v ∧
      IsGLB {s | ∃ ψ : Fin n → ℝ → ℝ,
        IsLUB ((fun ν => lagrangian μ 𝒳 h𝒳 ψ ν) '' stdSimplex ℝ 𝒳) s} v := by
  classical
  have hint : ∀ i, Integrable id (μ i) := fun i => (hvar i).integrable (by norm_num)
  obtain ⟨ψs, s, hsLUB, hsmin⟩ := MarginalDRO.Lagrange.proof_thm2_dual_attained μ hvar 𝒳 h𝒳
  have hs : s = D μ 𝒳 h𝒳 ψs := hsLUB.unique (isGreatest_D μ 𝒳 h𝒳 ψs).isLUB
  have hαle : ∀ ψ, s ≤ D μ 𝒳 h𝒳 ψ := fun ψ => hsmin ψ _ (isGreatest_D μ 𝒳 h𝒳 ψ).isLUB
  -- values at the vertices
  let g : (Fin n → ℝ → ℝ) → 𝒳 → ℝ := fun ψ x =>
    ∑ i, ψ i ((x : Fin n → ℝ) i) + ∑ i, ∫ c, conj 𝒳 h𝒳 (ψ i) i c ∂(μ i)
  have hLg : ∀ ψ, ∀ ν ∈ stdSimplex ℝ 𝒳, lagrangian μ 𝒳 h𝒳 ψ ν = ∑ x, ν x * g ψ x := by
    intro ψ ν hν
    rw [lagrangian_eq]
    simp only [g, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hν.2, one_mul]
  have hgD : ∀ ψ, ∀ x : 𝒳, g ψ x ≤ D μ 𝒳 h𝒳 ψ := fun ψ x => by
    simp only [g, D]
    gcongr
    exact Finset.le_sup' (fun x : Fin n → ℝ => ∑ i, ψ i (x i)) x.2
  have hDg : ∀ ψ, ∃ x : 𝒳, D μ 𝒳 h𝒳 ψ = g ψ x := fun ψ => by
    obtain ⟨x, hx, h⟩ := Finset.exists_mem_eq_sup' h𝒳 (fun x : Fin n → ℝ => ∑ i, ψ i (x i))
    exact ⟨⟨x, hx⟩, by simp only [D, g, h]⟩
  -- the open convex set
  let U : Set (𝒳 → ℝ) := {y | ∃ ψ, ∀ x, g ψ x < y x}
  have hUopen : IsOpen U := by
    have : U = ⋃ ψ, Set.pi Set.univ (fun x => Set.Ioi (g ψ x)) := by
      ext y; simp [U]
    rw [this]
    exact isOpen_iUnion fun ψ => isOpen_set_pi Set.finite_univ fun x _ => isOpen_Ioi
  have hUconv : Convex ℝ U := by
    rintro y₁ ⟨ψ₁, h₁⟩ y₂ ⟨ψ₂, h₂⟩ t u ht hu htu
    refine ⟨fun i a => t * ψ₁ i a + u * ψ₂ i a, fun x => ?_⟩
    have hI : ∀ i, ∫ c, conj 𝒳 h𝒳 (fun a => t * ψ₁ i a + u * ψ₂ i a) i c ∂(μ i) ≤
        t * ∫ c, conj 𝒳 h𝒳 (ψ₁ i) i c ∂(μ i) + u * ∫ c, conj 𝒳 h𝒳 (ψ₂ i) i c ∂(μ i) := by
      intro i
      rw [← integral_const_mul, ← integral_const_mul, ← integral_add
        ((conj_integrable 𝒳 h𝒳 _ i _ (hint i)).const_mul t)
        ((conj_integrable 𝒳 h𝒳 _ i _ (hint i)).const_mul u)]
      exact integral_mono (conj_integrable 𝒳 h𝒳 _ i _ (hint i))
        (((conj_integrable 𝒳 h𝒳 _ i _ (hint i)).const_mul t).add
          ((conj_integrable 𝒳 h𝒳 _ i _ (hint i)).const_mul u))
        (fun c => conj_convex 𝒳 h𝒳 (ψ₁ i) (ψ₂ i) i t u ht hu htu c)
    have hle : g (fun i a => t * ψ₁ i a + u * ψ₂ i a) x ≤ t * g ψ₁ x + u * g ψ₂ x := by
      simp only [g]
      have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hI i
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at this
      have e : ∑ i, (t * ψ₁ i ((x : Fin n → ℝ) i) + u * ψ₂ i ((x : Fin n → ℝ) i)) =
          t * ∑ i, ψ₁ i ((x : Fin n → ℝ) i) + u * ∑ i, ψ₂ i ((x : Fin n → ℝ) i) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      rw [e]; nlinarith
    have hlt : t * g ψ₁ x + u * g ψ₂ x < t * y₁ x + u * y₂ x := by
      rcases ht.lt_or_eq with ht' | ht'
      · nlinarith [h₁ x, h₂ x]
      · subst ht'
        have : u = 1 := by linarith
        subst this
        simpa using h₂ x
    calc _ ≤ _ := hle
      _ < _ := hlt
      _ = (t • y₁ + u • y₂) x := by simp
  have hpU : (fun _ => s) ∉ U := by
    rintro ⟨ψ, hψ⟩
    obtain ⟨x, hx⟩ := hDg ψ
    have := hαle ψ
    have := hψ x
    linarith
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hUconv hUopen hpU
  set w : 𝒳 → ℝ := fun x => f (Pi.single x 1) with hw
  have hfw : ∀ y : 𝒳 → ℝ, f y = ∑ x, y x * w x := by
    intro y
    have : y = ∑ x, y x • (Pi.single x 1 : 𝒳 → ℝ) := by
      ext z; simp [Pi.single_apply]
    conv_lhs => rw [this]
    rw [map_sum]
    simp [w]
  have hgU : ∀ ψ, ∀ ε > 0, (fun x => g ψ x + ε) ∈ U := fun ψ ε hε =>
    ⟨ψ, fun x => by simp only; linarith⟩
  -- the normal vector is nonpositive
  have hw0 : ∀ x, w x ≤ 0 := by
    intro x0
    by_contra hpos
    have hpos : 0 < w x0 := lt_of_not_ge hpos
    set y0 : 𝒳 → ℝ := fun x => g ψs x + 1
    set T : ℝ := (f (fun _ => s) - f y0) / w x0 + 1
    have hT : 0 ≤ T := by
      have := hf y0 (hgU ψs 1 one_pos)
      have : 0 ≤ (f (fun _ => s) - f y0) / w x0 := div_nonneg (by linarith) hpos.le
      linarith
    have hmem : y0 + T • (Pi.single x0 1 : 𝒳 → ℝ) ∈ U := by
      refine ⟨ψs, fun x => ?_⟩
      have h1 : 0 ≤ (T • (Pi.single x0 1 : 𝒳 → ℝ)) x := by
        by_cases hx : x = x0
        · subst hx; simp [hT]
        · simp [hx]
      simp only [Pi.add_apply, y0] at h1 ⊢
      linarith
    have := hf _ hmem
    rw [map_add, map_smul, smul_eq_mul] at this
    have e : T * f (Pi.single x0 1) = T * w x0 := rfl
    rw [e] at this
    have : T * w x0 = (f (fun _ => s) - f y0) + w x0 := by
      simp only [T]; field_simp
    linarith
  set W : ℝ := ∑ x, -w x with hW
  have hWpos : 0 < W := by
    rcases (Finset.sum_nonneg fun x (_ : x ∈ Finset.univ) => neg_nonneg.mpr (hw0 x)).lt_or_eq
      with h | h
    · exact h
    · exfalso
      have hz : ∀ x, w x = 0 := by
        intro x
        have := (Finset.sum_eq_zero_iff_of_nonneg
          (fun x (_ : x ∈ Finset.univ) => neg_nonneg.mpr (hw0 x))).mp h.symm x (Finset.mem_univ x)
        linarith
      have := hf _ (hgU ψs 1 one_pos)
      rw [hfw, hfw] at this
      simp [hz] at this
  set ν : 𝒳 → ℝ := fun x => -w x / W with hν
  have hνΔ : ν ∈ stdSimplex ℝ 𝒳 := by
    refine ⟨fun x => div_nonneg (neg_nonneg.mpr (hw0 x)) hWpos.le, ?_⟩
    simp only [ν, ← Finset.sum_div]
    exact div_self hWpos.ne'
  -- every ψ gives L(ψ, ν) ≥ s
  have hLν : ∀ ψ, s ≤ lagrangian μ 𝒳 h𝒳 ψ ν := by
    intro ψ
    rw [hLg ψ ν hνΔ]
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    have h1 := hf _ (hgU ψ ε hε)
    rw [hfw, hfw] at h1
    have h2 : ∑ x, (g ψ x + ε) * w x = -W * (∑ x, ν x * g ψ x + ε) := by
      have hνw : ∀ x, -W * ν x = w x := by
        intro x; simp only [ν]; field_simp
      rw [mul_add, Finset.mul_sum]
      simp_rw [← mul_assoc, hνw]
      rw [hW, Finset.sum_neg_distrib, neg_neg, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      ring
    have h3 : ∑ x, s * w x = -W * s := by
      rw [← Finset.mul_sum, hW, Finset.sum_neg_distrib]; ring
    rw [h2, h3] at h1
    nlinarith
  have hLs : lagrangian μ 𝒳 h𝒳 ψs ν ≤ s := by
    rw [hs]; exact (isGreatest_D μ 𝒳 h𝒳 ψs).2 ⟨ν, hνΔ, rfl⟩
  have hglb : IsGLB (Set.range fun ψ : Fin n → ℝ → ℝ => lagrangian μ 𝒳 h𝒳 ψ ν) s := by
    refine ⟨?_, fun b hb => ?_⟩
    · rintro _ ⟨ψ, rfl⟩; exact hLν ψ
    · exact (hb ⟨ψs, rfl⟩).trans hLs
  refine ⟨s, ⟨⟨ν, hνΔ, hglb⟩, ?_⟩, ⟨?_, fun b hb => hb ⟨ψs, hsLUB⟩⟩⟩
  · rintro _ ⟨ν', hν', h'⟩
    refine (h'.1 ⟨ψs, rfl⟩).trans ?_
    rw [hs]; exact (isGreatest_D μ 𝒳 h𝒳 ψs).2 ⟨ν', hν', rfl⟩
  · rintro _ ⟨ψ, h⟩
    rw [h.unique (isGreatest_D μ 𝒳 h𝒳 ψ).isLUB]
    exact hαle ψ
