-- Prove2me | solution 1 for KallMayerSLP.RecourseBounds.lemma_2_8
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-05T06:24:02.408384+00:00
-- url     : https://prove2.me/submissions/cdf5f8da-c159-42f7-8f31-b67da022a23b

import Mathlib
import Definitions.Def_KallMayerSLP_RecourseBounds_genEMBound
import Definitions.Def_KallMayerSLP_RecourseBounds_IsBoxPartition

set_option autoImplicit false

open MeasureTheory

namespace KMSLP28

open KallMayerSLP.RecourseBounds NumStochOpt.Bounds

variable {r : ℕ}

noncomputable def fac (a b t : ℝ) (s : Bool) : ℝ :=
  if a < b then emProb a b t s else if s then 0 else 1

lemma vertexProb_eq (a b x : Fin r → ℝ) (v : Fin r → Bool) :
    vertexProb a b x v = ∏ i, fac (a i) (b i) (x i) (v i) := rfl

lemma fac_nonneg {a b t : ℝ} (h1 : a ≤ t) (h2 : t ≤ b) (s : Bool) : 0 ≤ fac a b t s := by
  unfold fac emProb
  split_ifs with h h'
  · exact div_nonneg (by linarith) (by linarith)
  · exact div_nonneg (by linarith) (by linarith)
  · exact le_rfl
  · exact zero_le_one

lemma fac_affine {a b t : ℝ} (h1 : a ≤ t) (h2 : t ≤ b) (c d : ℝ) :
    ∑ s : Bool, fac a b t s * (c + d * (if s then b else a)) = c + d * t := by
  rw [Fintype.sum_bool]
  by_cases h : a < b
  · have hne : b - a ≠ 0 := by linarith [sub_pos.2 h]
    simp only [fac, emProb, h, if_true, Bool.false_eq_true, if_false]
    field_simp
    ring
  · have hab : a = t := by linarith [not_lt.1 h]
    have hbt : t = b := by linarith [not_lt.1 h]
    simp only [fac, h, if_true, Bool.false_eq_true, if_false]
    subst hab; subst hbt; ring

lemma fac_affine_form (a b : ℝ) (w : Bool) : ∃ c d : ℝ, ∀ t, fac a b t w = c + d * t := by
  unfold fac emProb
  by_cases h : a < b
  · cases w
    · exact ⟨b / (b - a), -1 / (b - a), fun t => by simp only [h, if_true, Bool.false_eq_true, if_false]; ring⟩
    · exact ⟨-a / (b - a), 1 / (b - a), fun t => by simp only [h, if_true]; ring⟩
  · cases w
    · exact ⟨1, 0, fun t => by simp [h]⟩
    · exact ⟨0, 0, fun t => by simp [h]⟩

lemma reprod (a b x : Fin r → ℝ) (hx : x ∈ Set.Icc a b) (c d : Fin r → ℝ) :
    ∑ v : Fin r → Bool, vertexProb a b x v * ∏ i, (c i + d i * boxVertex a b v i) =
      ∏ i, (c i + d i * x i) := by
  have key : ∀ v : Fin r → Bool, vertexProb a b x v * ∏ i, (c i + d i * boxVertex a b v i) =
      ∏ i, (fac (a i) (b i) (x i) (v i) * (c i + d i * (if v i then b i else a i))) := by
    intro v; rw [vertexProb_eq, ← Finset.prod_mul_distrib]; rfl
  simp_rw [key]
  rw [← Fintype.prod_sum (fun i s => fac (a i) (b i) (x i) s * (c i + d i * (if s then b i else a i)))]
  exact Finset.prod_congr rfl fun i _ => fac_affine (hx.1 i) (hx.2 i) (c i) (d i)

lemma vertexProb_nonneg {a b x : Fin r → ℝ} (hx : x ∈ Set.Icc a b) (v : Fin r → Bool) :
    0 ≤ vertexProb a b x v := by
  rw [vertexProb_eq]
  exact Finset.prod_nonneg fun i _ => fac_nonneg (hx.1 i) (hx.2 i) (v i)

lemma vertexProb_sum_one {a b x : Fin r → ℝ} (hx : x ∈ Set.Icc a b) :
    ∑ v, vertexProb a b x v = 1 := by
  have := reprod a b x hx (fun _ => 1) (fun _ => 0)
  simpa using this

lemma vertexProb_bary {a b x : Fin r → ℝ} (hx : x ∈ Set.Icc a b) :
    ∑ v, vertexProb a b x v • boxVertex a b v = x := by
  funext j
  rw [Finset.sum_apply]
  have := reprod a b x hx (fun i => if i = j then 0 else 1) (fun i => if i = j then 1 else 0)
  have e : ∀ y : Fin r → ℝ, ∏ i, ((if i = j then (0:ℝ) else 1) + (if i = j then 1 else 0) * y i) = y j := by
    intro y
    have : ∀ i, ((if i = j then (0:ℝ) else 1) + (if i = j then 1 else 0) * y i) =
        if i = j then y i else 1 := by
      intro i; split_ifs <;> ring
    simp only [this]
    simp
  simp only [e] at this
  simpa [smul_eq_mul] using this

lemma vertexProb_refine {α β a b x : Fin r → ℝ} (hx : x ∈ Set.Icc a b) (w : Fin r → Bool) :
    ∑ v, vertexProb a b x v * vertexProb α β (boxVertex a b v) w = vertexProb α β x w := by
  choose c d hcd using fun i => fac_affine_form (α i) (β i) (w i)
  have e : ∀ y : Fin r → ℝ, vertexProb α β y w = ∏ i, (c i + d i * y i) := by
    intro y; rw [vertexProb_eq]; exact Finset.prod_congr rfl fun i _ => hcd i (y i)
  simp only [e]
  exact reprod a b x hx c d

lemma boxVertex_mem {a b : Fin r → ℝ} (hle : a ≤ b) (v : Fin r → Bool) :
    boxVertex a b v ∈ Set.Icc a b := by
  constructor <;> intro i <;> simp only [boxVertex] <;> split_ifs <;> linarith [hle i]

lemma em_pointwise {α β : Fin r → ℝ} {φ : (Fin r → ℝ) → ℝ} (hφ : ConvexOn ℝ (Set.Icc α β) φ)
    {a b x : Fin r → ℝ} (hab : Set.Icc a b ⊆ Set.Icc α β) (hx : x ∈ Set.Icc a b) :
    φ x ≤ ∑ v, vertexProb a b x v * φ (boxVertex a b v) := by
  have hle : a ≤ b := le_trans hx.1 hx.2
  have hw0 : ∀ v ∈ (Finset.univ : Finset (Fin r → Bool)), 0 ≤ vertexProb a b x v :=
    fun v _ => vertexProb_nonneg hx v
  have hw1 : ∑ v ∈ (Finset.univ : Finset (Fin r → Bool)), vertexProb a b x v = 1 :=
    vertexProb_sum_one hx
  have hmem : ∀ v ∈ (Finset.univ : Finset (Fin r → Bool)), boxVertex a b v ∈ Set.Icc α β :=
    fun v _ => hab (boxVertex_mem hle v)
  have := hφ.map_sum_le hw0 hw1 hmem
  rw [vertexProb_bary hx] at this
  simpa [smul_eq_mul] using this

lemma phi_bound {α β : Fin r → ℝ} {φ : (Fin r → ℝ) → ℝ} (hφ : ConvexOn ℝ (Set.Icc α β) φ) :
    ∃ C, ∀ x ∈ Set.Icc α β, |φ x| ≤ C := by
  set M := ∑ v, |φ (boxVertex α β v)|
  have hup : ∀ x ∈ Set.Icc α β, φ x ≤ M := by
    intro x hx
    refine le_trans (em_pointwise hφ subset_rfl hx) ?_
    refine Finset.sum_le_sum fun v _ => ?_
    have h0 := vertexProb_nonneg hx v
    have h1 : vertexProb α β x v ≤ 1 := by
      rw [← vertexProb_sum_one hx]
      exact Finset.single_le_sum (fun w _ => vertexProb_nonneg hx w) (Finset.mem_univ v)
    calc vertexProb α β x v * φ (boxVertex α β v) ≤ vertexProb α β x v * |φ (boxVertex α β v)| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) h0
      _ ≤ 1 * |φ (boxVertex α β v)| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ = |φ (boxVertex α β v)| := one_mul _
  refine ⟨M + 2 * |φ ((1/2 : ℝ) • (α + β))|, fun x hx => ?_⟩
  have hy : α + β - x ∈ Set.Icc α β := by
    constructor <;> intro i <;> simp only [Pi.add_apply, Pi.sub_apply] <;> linarith [hx.1 i, hx.2 i]
  have hc := hφ.2 hx hy (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  have he : (1/2 : ℝ) • x + (1/2 : ℝ) • (α + β - x) = (1/2 : ℝ) • (α + β) := by
    funext i; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [he, smul_eq_mul, smul_eq_mul] at hc
  have h1 := hup x hx
  have h2 := hup _ hy
  have h3 := neg_abs_le (φ ((1/2 : ℝ) • (α + β)))
  have h4 : 0 ≤ M := Finset.sum_nonneg fun v _ => abs_nonneg _
  have h5 := abs_nonneg (φ ((1/2 : ℝ) • (α + β)))
  rw [abs_le]; constructor <;> linarith

def emb (J : Finset (Fin r)) (c y : Fin r → ℝ) : Fin r → ℝ := fun i => if i ∈ J then y i else c i

def face (α β : Fin r → ℝ) (J : Finset (Fin r)) (c : Fin r → ℝ) : Set (Fin r → ℝ) :=
  Set.univ.pi (fun i => if i ∈ J then Set.Ioo (α i) (β i) else {c i})

lemma contOn_face {α β c : Fin r → ℝ} {φ : (Fin r → ℝ) → ℝ} (hφ : ConvexOn ℝ (Set.Icc α β) φ)
    (J : Finset (Fin r)) (hc : c ∈ Set.Icc α β) : ContinuousOn φ (face α β J c) := by
  set D : Set (Fin r → ℝ) := Set.univ.pi (fun i => if i ∈ J then Set.Icc (α i) (β i) else Set.univ)
  set U : Set (Fin r → ℝ) := Set.univ.pi (fun i => if i ∈ J then Set.Ioo (α i) (β i) else Set.univ)
  have hembD : ∀ y ∈ D, emb J c y ∈ Set.Icc α β := by
    intro y hy
    constructor <;> intro i <;> simp only [emb] <;> split_ifs with h
    · have := hy i (Set.mem_univ _); simp only [h, if_true] at this; exact this.1
    · exact hc.1 i
    · have := hy i (Set.mem_univ _); simp only [h, if_true] at this; exact this.2
    · exact hc.2 i
  have hconv : ConvexOn ℝ D (φ ∘ emb J c) := by
    refine ⟨convex_pi fun i _ => ?_, ?_⟩
    · split_ifs
      · exact convex_Icc _ _
      · exact convex_univ
    · intro x hx y hy a b ha hb hab
      have heq : emb J c (a • x + b • y) = a • emb J c x + b • emb J c y := by
        funext i; simp only [emb, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; split_ifs
        · rfl
        · rw [← add_mul, hab, one_mul]
      have := hφ.2 (hembD x hx) (hembD y hy) ha hb hab
      simpa only [Function.comp, heq] using this
  have hU : IsOpen U := isOpen_set_pi Set.finite_univ (fun i _ => by
    split_ifs
    · exact isOpen_Ioo
    · exact isOpen_univ)
  have hUD : U ⊆ D := Set.pi_mono (fun i _ => by
    split_ifs
    · exact Set.Ioo_subset_Icc_self
    · exact le_rfl)
  have hcont : ContinuousOn (φ ∘ emb J c) U :=
    hconv.continuousOn_interior.mono (interior_maximal hUD hU)
  have hFU : face α β J c ⊆ U := Set.pi_mono (fun i _ => by
    split_ifs
    · exact le_rfl
    · exact Set.subset_univ _)
  refine (hcont.mono hFU).congr ?_
  intro y hy
  have : emb J c y = y := by
    funext i; simp only [emb]; split_ifs with h
    · rfl
    · have := hy i (Set.mem_univ _); simp only [face, h, if_false] at this; exact this.symm
  simp only [Function.comp, this]

lemma aesm_phi {α β : Fin r → ℝ} {φ : (Fin r → ℝ) → ℝ} (hφ : ConvexOn ℝ (Set.Icc α β) φ)
    (hαβ : α ≤ β) (ν : Measure (Fin r → ℝ)) (hν : ν (Set.Icc α β)ᶜ = 0) :
    AEStronglyMeasurable φ ν := by
  have hae : ∀ᵐ x ∂ν, x ∈ Set.Icc α β := mem_ae_iff.2 hν
  have hcover : Set.Icc α β ⊆
      ⋃ p : Finset (Fin r) × (Fin r → Bool), face α β p.1 (boxVertex α β p.2) := by
    intro x hx
    refine Set.mem_iUnion.2 ⟨(Finset.univ.filter (fun i => α i < x i ∧ x i < β i),
      fun i => decide (x i = β i)), ?_⟩
    intro i _
    simp only [face]
    split_ifs with h
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h; exact h
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_lt] at h
      simp only [boxVertex, Set.mem_singleton_iff]
      by_cases hb : x i = β i
      · simp [hb]
      · simp only [hb, decide_false, Bool.false_eq_true, if_false]
        rcases (hx.1 i).lt_or_eq with h' | h'
        · exact absurd (le_antisymm (hx.2 i) (h h')) hb
        · exact h'.symm
  have hmeas : ∀ p : Finset (Fin r) × (Fin r → Bool),
      MeasurableSet (face α β p.1 (boxVertex α β p.2)) := fun p =>
    MeasurableSet.univ_pi (fun i => by
      split_ifs
      · exact measurableSet_Ioo
      · exact measurableSet_singleton _)
  have h2 : AEStronglyMeasurable φ
      (ν.restrict (⋃ p : Finset (Fin r) × (Fin r → Bool), face α β p.1 (boxVertex α β p.2))) := by
    rw [aestronglyMeasurable_iUnion_iff]
    intro p
    exact (contOn_face hφ p.1 (boxVertex_mem hαβ p.2)).aestronglyMeasurable (hmeas p)
  have h1 : ν.restrict (Set.Icc α β) = ν := Measure.restrict_eq_self_of_ae_mem hae
  rw [← h1]
  exact h2.mono_measure (Measure.restrict_mono hcover le_rfl)

lemma integrable_phi {α β : Fin r → ℝ} {φ : (Fin r → ℝ) → ℝ} (hφ : ConvexOn ℝ (Set.Icc α β) φ)
    (hαβ : α ≤ β) (ν : Measure (Fin r → ℝ)) [IsFiniteMeasure ν] (hν : ν (Set.Icc α β)ᶜ = 0) :
    Integrable φ ν := by
  have hae : ∀ᵐ x ∂ν, x ∈ Set.Icc α β := mem_ae_iff.2 hν
  obtain ⟨C, hC⟩ := phi_bound hφ
  refine Integrable.of_bound (aesm_phi hφ hαβ ν hν) C ?_
  filter_upwards [hae] with x hx
  simpa [Real.norm_eq_abs] using hC x hx

lemma integrable_of_cont {E : Type*} [NormedAddCommGroup E] {g : (Fin r → ℝ) → E}
    (hg : Continuous g) {a b : Fin r → ℝ} (ν : Measure (Fin r → ℝ)) [IsFiniteMeasure ν]
    (hae : ∀ᵐ x ∂ν, x ∈ Set.Icc a b) : Integrable g ν := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hg.continuousOn
    (s := Set.Icc a b)
  refine Integrable.of_bound hg.aestronglyMeasurable C ?_
  filter_upwards [hae] with x hx
  exact hC x hx

lemma continuous_vertexProb (a b : Fin r → ℝ) (v : Fin r → Bool) :
    Continuous fun x => vertexProb a b x v := by
  simp only [vertexProb_eq]
  refine continuous_finsetProd _ fun i _ => ?_
  unfold fac emProb
  split_ifs <;> fun_prop

lemma genEM_eq {μ : Measure (Fin r → ℝ)} [IsFiniteMeasure μ] {a b : Fin r → ℝ}
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (φ : (Fin r → ℝ) → ℝ) :
    genEMBound μ a b φ = ∫ x, ∑ v, vertexProb a b x v * φ (boxVertex a b v) ∂μ := by
  unfold genEMBound genEMWeight
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun v _ => ?_
    rw [integral_mul_const]
  · intro v _
    exact (integrable_of_cont (continuous_vertexProb a b v) μ hμ).mul_const _

set_option maxHeartbeats 1000000 in
lemma jensen_box {α β : Fin r → ℝ} {φ : (Fin r → ℝ) → ℝ} (hφ : ConvexOn ℝ (Set.Icc α β) φ)
    (ν : Measure (Fin r → ℝ)) [IsProbabilityMeasure ν] (hν : ν (Set.Icc α β)ᶜ = 0) :
    φ (∫ x, x ∂ν) ≤ ∫ x, φ x ∂ν := by
  have hae : ∀ᵐ x ∂ν, x ∈ Set.Icc α β := mem_ae_iff.2 hν
  have hne : (Set.Icc α β).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, Set.compl_empty] at hν
    simp at hν
  have hαβ : α ≤ β := Set.nonempty_Icc.1 hne
  have hint : Integrable (fun x : Fin r → ℝ => x) ν := integrable_of_cont continuous_id ν hae
  have hintφ : Integrable φ ν := integrable_phi hφ hαβ ν hν
  set m := ∫ x, x ∂ν with hm_def
  have hm : m ∈ Set.Icc α β := Convex.integral_mem (convex_Icc α β) isClosed_Icc hae hint
  set J := Finset.univ.filter (fun i => α i < m i ∧ m i < β i) with hJ
  have hcoord : ∀ i, ∫ x, x i ∂ν = m i := by
    intro i
    rw [hm_def, eval_integral (fun i => (integrable_of_cont (continuous_apply i) ν hae))]
  have hfix : ∀ᵐ x ∂ν, ∀ i, i ∉ J → x i = m i := by
    rw [ae_all_iff]
    intro i
    by_cases hi : i ∈ J
    · exact Filter.Eventually.of_forall (fun x h => absurd hi h)
    · have hi' : ¬ (α i < m i ∧ m i < β i) := by simpa [hJ] using hi
      have hint_i : Integrable (fun x : Fin r → ℝ => x i) ν :=
        integrable_of_cont (continuous_apply i) ν hae
      rcases (hm.1 i).lt_or_eq with h1 | h1
      · have h2 : m i = β i := le_antisymm (hm.2 i) (not_lt.1 fun h => hi' ⟨h1, h⟩)
        have hnn : 0 ≤ᵐ[ν] fun x => β i - x i := by
          filter_upwards [hae] with x hx; simp only [Pi.zero_apply]; linarith [hx.2 i]
        have hI : ∫ x, (β i - x i) ∂ν = 0 := by
          rw [integral_sub (integrable_const _) hint_i, integral_const, hcoord i, h2]; simp
        have := (integral_eq_zero_iff_of_nonneg_ae hnn ((integrable_const _).sub hint_i)).1 hI
        filter_upwards [this] with x hx _
        simp only [Pi.zero_apply] at hx
        linarith
      · have hnn : 0 ≤ᵐ[ν] fun x => x i - α i := by
          filter_upwards [hae] with x hx; simp only [Pi.zero_apply]; linarith [hx.1 i]
        have hI : ∫ x, (x i - α i) ∂ν = 0 := by
          rw [integral_sub hint_i (integrable_const _), integral_const, hcoord i, ← h1]; simp
        have := (integral_eq_zero_iff_of_nonneg_ae hnn (hint_i.sub (integrable_const _))).1 hI
        filter_upwards [this] with x hx _
        simp only [Pi.zero_apply] at hx
        linarith
  set f : (Fin r → ℝ) → (Fin r → ℝ) := fun x => (1/2 : ℝ) • m + (1/2 : ℝ) • x with hf_def
  have hfc : Continuous f := by rw [hf_def]; fun_prop
  have hfi : Integrable f ν := integrable_of_cont hfc ν hae
  have hfint : ∫ x, f x ∂ν = m := by
    have hint2 : Integrable (fun x : Fin r → ℝ => (1/2 : ℝ) • x) ν :=
      integrable_of_cont (by fun_prop) ν hae
    show ∫ x, ((1/2 : ℝ) • m + (1/2 : ℝ) • x) ∂ν = m
    rw [integral_add (integrable_const _) hint2, integral_const, integral_smul]
    rw [← hm_def]
    simp only [probReal_univ, one_smul]
    rw [← add_smul]; norm_num
  set s : Set (Fin r → ℝ) := Set.univ.pi
    (fun i => if i ∈ J then Set.Icc ((m i + α i) / 2) ((m i + β i) / 2) else {m i}) with hs_def
  have hsc : IsClosed s := isClosed_set_pi (fun i _ => by
    split_ifs
    · exact isClosed_Icc
    · exact isClosed_singleton)
  have hsF : s ⊆ face α β J m := Set.pi_mono (fun i _ => by
    split_ifs with h
    · simp only [hJ, Finset.mem_filter, Finset.mem_univ, true_and] at h
      intro t ht; constructor <;> linarith [ht.1, ht.2, h.1, h.2]
    · exact le_rfl)
  have hsB : s ⊆ Set.Icc α β := by
    intro y hy
    constructor <;> intro i <;> have := hy i (Set.mem_univ _) <;> simp only [hs_def] at this <;>
      split_ifs at this with h
    · simp only [hJ, Finset.mem_filter, Finset.mem_univ, true_and] at h; linarith [this.1, h.1]
    · rw [Set.mem_singleton_iff] at this; rw [this]; exact hm.1 i
    · simp only [hJ, Finset.mem_filter, Finset.mem_univ, true_and] at h; linarith [this.2, h.2]
    · rw [Set.mem_singleton_iff] at this; rw [this]; exact hm.2 i
  have hsconv : Convex ℝ s := convex_pi fun i _ => by
    split_ifs
    · exact convex_Icc _ _
    · exact convex_singleton _
  have hcont : ContinuousOn φ s := (contOn_face hφ J hm).mono hsF
  have hconv : ConvexOn ℝ s φ := hφ.subset hsB hsconv
  have hfs : ∀ᵐ x ∂ν, f x ∈ s := by
    filter_upwards [hae, hfix] with x hx hx2
    intro i _
    simp only [hf_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    split_ifs with h
    · constructor <;> linarith [hx.1 i, hx.2 i]
    · rw [hx2 i h, Set.mem_singleton_iff]; ring
  have hgi : Integrable (φ ∘ f) ν := by
    have hmapB : (ν.map f) (Set.Icc α β)ᶜ = 0 := by
      rw [Measure.map_apply hfc.measurable measurableSet_Icc.compl]
      have : ∀ᵐ x ∂ν, x ∈ f ⁻¹' (Set.Icc α β) := by
        filter_upwards [hfs] with x hx; exact hsB hx
      rw [Set.preimage_compl]; exact mem_ae_iff.1 this
    exact (integrable_phi hφ hαβ (ν.map f) hmapB).comp_measurable hfc.measurable
  have J1 := hconv.map_integral_le hcont hsc hfs hfi hgi
  rw [hfint] at J1
  have hrhs : Integrable (fun x => (1/2 : ℝ) * φ m + (1/2 : ℝ) * φ x) ν :=
    (integrable_const _).add (hintφ.const_mul _)
  have J2 : ∫ x, (φ ∘ f) x ∂ν ≤ ∫ x, ((1/2 : ℝ) * φ m + (1/2 : ℝ) * φ x) ∂ν := by
    refine integral_mono_ae hgi hrhs ?_
    filter_upwards [hae] with x hx
    have := hφ.2 hm hx (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
    simpa [hf_def, smul_eq_mul] using this
  rw [integral_add (integrable_const _) (hintφ.const_mul _), integral_const, integral_const_mul]
    at J2
  simp only [probReal_univ, one_smul] at J2
  have J2' : ∫ x, φ (f x) ∂ν ≤ 1 / 2 * φ m + 1 / 2 * ∫ x, φ x ∂ν := J2
  linarith

lemma cell_geom {α β lo hi : Fin r → ℝ} {C : Set (Fin r → ℝ)} (I : Fin r → Set ℝ)
    (hI : ∀ i, I i = Set.Icc (lo i) (hi i) ∨ I i = Set.Ico (lo i) (hi i) ∨
      I i = Set.Ioc (lo i) (hi i))
    (hC : C = Set.univ.pi I) (hne : C.Nonempty) (hsub : C ⊆ Set.Icc α β) :
    MeasurableSet C ∧ C ⊆ Set.Icc lo hi ∧ Set.Icc lo hi ⊆ Set.Icc α β := by
  subst hC
  obtain ⟨p, hp⟩ := hne
  have hIsub : ∀ i, I i ⊆ Set.Icc (lo i) (hi i) := fun i => by
    rcases hI i with h | h | h <;> rw [h] <;>
      first | exact Set.Subset.rfl | exact Set.Ico_subset_Icc_self | exact Set.Ioc_subset_Icc_self
  have hIab : ∀ i, I i ⊆ Set.Icc (α i) (β i) := by
    intro i t ht
    have hu : Function.update p i t ∈ Set.univ.pi I := by
      intro j _
      by_cases hj : j = i
      · subst hj; simpa using ht
      · rw [Function.update_of_ne hj]; exact hp j (Set.mem_univ _)
    have h2 := hsub hu
    have a1 := h2.1 i
    have a2 := h2.2 i
    simp only [Function.update_self] at a1 a2
    exact ⟨a1, a2⟩
  have hcl : ∀ i, Set.Icc (lo i) (hi i) ⊆ Set.Icc (α i) (β i) := by
    intro i
    have hpi : p i ∈ I i := hp i (Set.mem_univ _)
    have hclo : closure (I i) = Set.Icc (lo i) (hi i) := by
      rcases hI i with h | h | h <;> rw [h] <;> rw [h] at hpi
      · exact closure_Icc _ _
      · exact closure_Ico (ne_of_lt (Set.nonempty_Ico.1 ⟨_, hpi⟩))
      · exact closure_Ioc (ne_of_lt (Set.nonempty_Ioc.1 ⟨_, hpi⟩))
    rw [← hclo]
    exact closure_minimal (hIab i) isClosed_Icc
  refine ⟨?_, ?_, ?_⟩
  · exact MeasurableSet.univ_pi fun i => by
      rcases hI i with h | h | h <;> rw [h]
      · exact measurableSet_Icc
      · exact measurableSet_Ico
      · exact measurableSet_Ioc
  · intro x hx
    exact ⟨fun i => (hIsub i (hx i (Set.mem_univ _))).1, fun i => (hIsub i (hx i (Set.mem_univ _))).2⟩
  · intro x hx
    exact ⟨fun i => (hcl i ⟨hx.1 i, hx.2 i⟩).1, fun i => (hcl i ⟨hx.1 i, hx.2 i⟩).2⟩

lemma part_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : ℕ}
    (P : Measure (Fin r → ℝ)) (cell : Fin K → Set (Fin r → ℝ))
    (hm : ∀ k, MeasurableSet (cell k)) (hd : Pairwise (Function.onFun Disjoint cell))
    (hU : ∀ᵐ x ∂P, x ∈ ⋃ k, cell k) (h : (Fin r → ℝ) → E) (hi : Integrable h P) :
    ∑ k, ∫ x in cell k, h x ∂P = ∫ x, h x ∂P := by
  rw [← integral_iUnion_fintype hm hd (fun k => hi.integrableOn),
    Measure.restrict_eq_self_of_ae_mem hU]

set_option maxHeartbeats 1000000 in
theorem main {K : ℕ} (P : Measure (Fin r → ℝ)) [IsProbabilityMeasure P]
    (α β : Fin r → ℝ) (hsupp : P (Set.Icc α β)ᶜ = 0)
    (lo hi : Fin K → Fin r → ℝ) (cell : Fin K → Set (Fin r → ℝ))
    (hX : IsBoxPartition α β lo hi cell)
    (φ : (Fin r → ℝ) → ℝ) (hφ : ConvexOn ℝ (Set.Icc α β) φ) :
    φ (∫ x, x ∂P) ≤ ∑ k, P.real (cell k) * φ (⨍ x in cell k, x ∂P) ∧
    ∑ k, P.real (cell k) * φ (⨍ x in cell k, x ∂P) ≤ ∑ k, ∫ x in cell k, φ x ∂P ∧
    ∑ k, ∫ x in cell k, φ x ∂P = ∫ x, φ x ∂P ∧
    ∑ k, ∫ x in cell k, φ x ∂P ≤ ∑ k, genEMBound (P.restrict (cell k)) (lo k) (hi k) φ ∧
    ∑ k, genEMBound (P.restrict (cell k)) (lo k) (hi k) φ ≤ genEMBound P α β φ := by
  obtain ⟨hcellI, hne, hdisj, hunion⟩ := hX
  have hae : ∀ᵐ x ∂P, x ∈ Set.Icc α β := mem_ae_iff.2 hsupp
  have hBne : (Set.Icc α β).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, Set.compl_empty] at hsupp
    simp at hsupp
  have hαβ : α ≤ β := Set.nonempty_Icc.1 hBne
  have hgeom : ∀ k, MeasurableSet (cell k) ∧ cell k ⊆ Set.Icc (lo k) (hi k) ∧
      Set.Icc (lo k) (hi k) ⊆ Set.Icc α β := by
    intro k
    obtain ⟨I, hI, hc⟩ := hcellI k
    exact cell_geom I hI hc (hne k) (hunion ▸ Set.subset_iUnion cell k)
  have hmC : ∀ k, MeasurableSet (cell k) := fun k => (hgeom k).1
  have hU : ∀ᵐ x ∂P, x ∈ ⋃ k, cell k := by rw [hunion]; exact hae
  have hint_id : Integrable (fun x : Fin r → ℝ => x) P := integrable_of_cont continuous_id P hae
  have hintφ : Integrable φ P := integrable_phi hφ hαβ P hsupp
  have hrestr : ∀ k, ∀ᵐ x ∂P.restrict (cell k), x ∈ cell k := fun k => ae_restrict_mem (hmC k)
  -- per-cell Jensen
  have hcellJ : ∀ k, P.real (cell k) * φ (⨍ x in cell k, x ∂P) ≤ ∫ x in cell k, φ x ∂P := by
    intro k
    by_cases h0 : P (cell k) = 0
    · have hw : P.real (cell k) = 0 := by simp [measureReal_def, h0]
      rw [hw, zero_mul, Measure.restrict_eq_zero.2 h0, integral_zero_measure]
    · haveI : NeZero (P.restrict (cell k)) := ⟨by rwa [Ne, Measure.restrict_eq_zero]⟩
      set ν := (P.restrict (cell k) Set.univ)⁻¹ • P.restrict (cell k) with hν_def
      have hν : ν (Set.Icc α β)ᶜ = 0 := by
        rw [hν_def, Measure.smul_apply]
        have : P.restrict (cell k) (Set.Icc α β)ᶜ = 0 :=
          nonpos_iff_eq_zero.1 (le_trans (Measure.restrict_le_self _) hsupp.le)
        rw [this, smul_zero]
      have hJ := jensen_box hφ ν hν
      have e1 : ∫ x, x ∂ν = ⨍ x in cell k, x ∂P := rfl
      have e2 : ∫ x, φ x ∂ν = ⨍ x in cell k, φ x ∂P := rfl
      rw [e1, e2] at hJ
      calc P.real (cell k) * φ (⨍ x in cell k, x ∂P)
          ≤ P.real (cell k) * ⨍ x in cell k, φ x ∂P :=
            mul_le_mul_of_nonneg_left hJ measureReal_nonneg
        _ = ∫ x in cell k, φ x ∂P := by
            rw [← smul_eq_mul]; exact measure_smul_setAverage _ (measure_ne_top _ _)
  -- (1)
  have h1 : φ (∫ x, x ∂P) ≤ ∑ k, P.real (cell k) * φ (⨍ x in cell k, x ∂P) := by
    have hsum_m : ∑ k, P.real (cell k) • (⨍ x in cell k, x ∂P) = ∫ x, x ∂P := by
      rw [← part_integral P cell hmC hdisj hU (fun x => x) hint_id]
      exact Finset.sum_congr rfl fun k _ => measure_smul_setAverage _ (measure_ne_top _ _)
    have hw1 : ∑ k, P.real (cell k) = 1 := by
      have := part_integral P cell hmC hdisj hU (fun _ => (1:ℝ)) (integrable_const _)
      simpa [setIntegral_const] using this
    set t := Finset.univ.filter (fun k => P (cell k) ≠ 0)
    have hz : ∀ k, P (cell k) = 0 → P.real (cell k) = 0 := by
      intro k hk; simp [measureReal_def, hk]
    have ht1 : ∑ k ∈ t, P.real (cell k) • (⨍ x in cell k, x ∂P) =
        ∑ k, P.real (cell k) • (⨍ x in cell k, x ∂P) := by
      refine Finset.sum_filter_of_ne fun k _ hk => ?_
      by_contra hc; exact hk (by rw [hz k hc, zero_smul])
    have ht2 : ∑ k ∈ t, P.real (cell k) = ∑ k, P.real (cell k) := by
      refine Finset.sum_filter_of_ne fun k _ hk => ?_
      by_contra hc; exact hk (hz k hc)
    have ht3 : ∑ k ∈ t, P.real (cell k) • φ (⨍ x in cell k, x ∂P) =
        ∑ k, P.real (cell k) * φ (⨍ x in cell k, x ∂P) := by
      simp only [smul_eq_mul]
      refine Finset.sum_filter_of_ne fun k _ hk => ?_
      by_contra hc; exact hk (by rw [hz k hc, zero_mul])
    have hmem : ∀ k ∈ t, (⨍ x in cell k, x ∂P) ∈ Set.Icc α β := by
      intro k hk
      have hk' : P (cell k) ≠ 0 := (Finset.mem_filter.1 hk).2
      exact Convex.set_average_mem (convex_Icc α β) isClosed_Icc hk' (measure_ne_top _ _)
        (ae_restrict_of_ae hae) hint_id.integrableOn
    have := hφ.map_sum_le (t := t) (fun k _ => measureReal_nonneg) (by rw [ht2, hw1]) hmem
    rw [ht1, hsum_m, ht3] at this
    exact this
  have h3 : ∑ k, ∫ x in cell k, φ x ∂P = ∫ x, φ x ∂P := part_integral P cell hmC hdisj hU φ hintφ
  -- genEM as integrals
  have hG : ∀ k, genEMBound (P.restrict (cell k)) (lo k) (hi k) φ =
      ∫ x in cell k, ∑ v, vertexProb (lo k) (hi k) x v * φ (boxVertex (lo k) (hi k) v) ∂P := by
    intro k
    refine genEM_eq ?_ φ
    filter_upwards [hrestr k] with x hx using (hgeom k).2.1 hx
  have hintG : ∀ k, Integrable
      (fun x => ∑ v, vertexProb (lo k) (hi k) x v * φ (boxVertex (lo k) (hi k) v))
      (P.restrict (cell k)) := by
    intro k
    refine integrable_finsetSum _ fun v _ => ?_
    refine (integrable_of_cont (a := lo k) (b := hi k) (continuous_vertexProb (lo k) (hi k) v) _ ?_).mul_const _
    filter_upwards [hrestr k] with x hx using (hgeom k).2.1 hx
  have h4 : ∑ k, ∫ x in cell k, φ x ∂P ≤ ∑ k, genEMBound (P.restrict (cell k)) (lo k) (hi k) φ := by
    refine Finset.sum_le_sum fun k _ => ?_
    rw [hG k]
    refine integral_mono_ae hintφ.integrableOn (hintG k) ?_
    filter_upwards [hrestr k] with x hx
    exact em_pointwise hφ (hgeom k).2.2 ((hgeom k).2.1 hx)
  have h5 : ∑ k, genEMBound (P.restrict (cell k)) (lo k) (hi k) φ ≤ genEMBound P α β φ := by
    set H : (Fin r → ℝ) → ℝ := fun x => ∑ w, vertexProb α β x w * φ (boxVertex α β w) with hH
    have hHi : Integrable H P := by
      refine integrable_finsetSum _ fun w _ => ?_
      exact (integrable_of_cont (continuous_vertexProb α β w) P hae).mul_const _
    rw [genEM_eq hae φ, ← part_integral P cell hmC hdisj hU H hHi]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [hG k]
    refine integral_mono_ae (hintG k) hHi.integrableOn ?_
    filter_upwards [hrestr k] with x hx
    have hxk := (hgeom k).2.1 hx
    have hle : lo k ≤ hi k := le_trans hxk.1 hxk.2
    calc ∑ v, vertexProb (lo k) (hi k) x v * φ (boxVertex (lo k) (hi k) v)
        ≤ ∑ v, vertexProb (lo k) (hi k) x v *
            ∑ w, vertexProb α β (boxVertex (lo k) (hi k) v) w * φ (boxVertex α β w) := by
          refine Finset.sum_le_sum fun v _ => ?_
          refine mul_le_mul_of_nonneg_left ?_ (vertexProb_nonneg hxk v)
          exact em_pointwise hφ subset_rfl ((hgeom k).2.2 (boxVertex_mem hle v))
      _ = ∑ w, (∑ v, vertexProb (lo k) (hi k) x v * vertexProb α β (boxVertex (lo k) (hi k) v) w)
            * φ (boxVertex α β w) := by
          simp_rw [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun v _ => ?_
          ring
      _ = H x := by
          simp only [hH]
          refine Finset.sum_congr rfl fun w _ => ?_
          rw [vertexProb_refine hxk w]
  exact ⟨h1, Finset.sum_le_sum fun k _ => hcellJ k, h3, h4, h5⟩

end KMSLP28

open MeasureTheory KallMayerSLP.RecourseBounds in
theorem solution {r K : ℕ} (P : Measure (Fin r → ℝ)) [IsProbabilityMeasure P]
    (α β : Fin r → ℝ) (hsupp : P (Set.Icc α β)ᶜ = 0)
    (lo hi : Fin K → Fin r → ℝ) (cell : Fin K → Set (Fin r → ℝ))
    (hX : IsBoxPartition α β lo hi cell)
    (φ : (Fin r → ℝ) → ℝ) (hφ : ConvexOn ℝ (Set.Icc α β) φ) :
    -- (2.39)
    φ (∫ x, x ∂P) ≤ ∑ k, P.real (cell k) * φ (⨍ x in cell k, x ∂P) ∧
    ∑ k, P.real (cell k) * φ (⨍ x in cell k, x ∂P) ≤ ∑ k, ∫ x in cell k, φ x ∂P ∧
    ∑ k, ∫ x in cell k, φ x ∂P = ∫ x, φ x ∂P ∧
    -- (2.40)
    ∑ k, ∫ x in cell k, φ x ∂P ≤ ∑ k, genEMBound (P.restrict (cell k)) (lo k) (hi k) φ ∧
    ∑ k, genEMBound (P.restrict (cell k)) (lo k) (hi k) φ ≤ genEMBound P α β φ := by
  exact KMSLP28.main P α β hsupp lo hi cell hX φ hφ
