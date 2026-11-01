-- Prove2me | solution 1 for GradDOvS.Submod.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T11:48:14.731401+00:00
-- url     : https://prove2.me/submissions/e9956e85-251b-40bd-a409-4c74d16761b8

import Mathlib
import Definitions.Def_GradDOvS_Submod_Model
import Theorems.Thm_GradDOvS_Submod_eq_6


open MeasureTheory ProbabilityTheory GradDOvS.Submod

namespace GSSol

variable {d : ℕ}

lemma nbr_zero (α : Equiv.Perm (Fin d)) : nbr α 0 = ∅ := by
  ext j; simp [nbr]

lemma nbr_succ (α : Equiv.Perm (Fin d)) (k : Fin d) :
    nbr α ((k : ℕ) + 1) = insert (α k) (nbr α k) := by
  ext j
  simp only [nbr, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · intro h
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
    · exact Or.inr h
    · left
      have : α.symm j = k := Fin.ext h
      rw [← this]; simp
  · rintro (h | h)
    · subst h; simp
    · omega

lemma not_mem_nbr (α : Equiv.Perm (Fin d)) (k : Fin d) : α k ∉ nbr α k := by
  simp [nbr]

lemma chainGrad_apply (f : Finset (Fin d) → ℝ) (α : Equiv.Perm (Fin d)) (k : Fin d) :
    chainGrad f α (α k) = f (nbr α ((k : ℕ) + 1)) - f (nbr α k) := by
  simp [chainGrad]

/-- (2) rewritten: `f̃_α(x) = f(∅) + ⟨g^α, x⟩`. -/
lemma lovaszWith_eq (f : Finset (Fin d) → ℝ) (x : Fin d → ℝ) (α : Equiv.Perm (Fin d)) :
    lovaszWith f x α = f ∅ + ∑ j, chainGrad f α j * x j := by
  unfold lovaszWith
  rw [nbr_zero]
  congr 1
  rw [← Equiv.sum_comp α (fun j => chainGrad f α j * x j)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [chainGrad_apply]

/-- Base-polytope inequality: `∑_{j ∈ S} g^α_j ≤ f(S) - f(∅)` for submodular `f`. -/
lemma base_ineq (f : Finset (Fin d) → ℝ) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (α : Equiv.Perm (Fin d)) (S : Finset (Fin d)) :
    ∑ j ∈ S, chainGrad f α j ≤ f S - f ∅ := by
  induction S using Finset.induction_on_max_value (fun j => α.symm j) with
  | empty => simp
  | insert a s ha hmax ih =>
    rw [Finset.sum_insert ha]
    -- s ⊆ P_a
    have hsub : s ⊆ nbr α (α.symm a) := by
      intro x hx
      simp only [nbr, Finset.mem_filter, Finset.mem_univ, true_and]
      have h1 := hmax x hx
      have hne : x ≠ a := fun h => ha (h ▸ hx)
      have : α.symm x ≠ α.symm a := fun h => hne (α.symm.injective h)
      exact lt_of_le_of_ne (Fin.le_iff_val_le_val.1 h1) (fun h => this (Fin.ext h))
    have hcg : chainGrad f α a
        = f (insert a (nbr α (α.symm a))) - f (nbr α (α.symm a)) := by
      have := chainGrad_apply f α (α.symm a)
      simp only [Equiv.apply_symm_apply] at this
      rw [this, nbr_succ]; simp
    have hsm := hf (nbr α (α.symm a)) (insert a s)
    have hu : nbr α (α.symm a) ∪ insert a s = insert a (nbr α (α.symm a)) := by
      ext x; simp only [Finset.mem_union, Finset.mem_insert]
      constructor
      · rintro (h | h | h)
        · exact Or.inr h
        · exact Or.inl h
        · exact Or.inr (hsub h)
      · rintro (h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
    have hna : a ∉ nbr α (α.symm a) := by
      have := not_mem_nbr α (α.symm a); simpa using this
    have hi : nbr α (α.symm a) ∩ insert a s = s := by
      ext x; simp only [Finset.mem_inter, Finset.mem_insert]
      constructor
      · rintro ⟨h1, h | h⟩
        · exact absurd (h ▸ h1) hna
        · exact h
      · intro h; exact ⟨hsub h, Or.inr h⟩
    rw [hu, hi] at hsm
    rw [hcg]
    linarith

/-- The Lovász extension of a modular function. -/
lemma chainGrad_modular (c : Fin d → ℝ) (c0 : ℝ) (α : Equiv.Perm (Fin d)) :
    chainGrad (fun S => c0 + ∑ j ∈ S, c j) α = c := by
  funext j
  obtain ⟨k, rfl⟩ := α.surjective j
  rw [chainGrad_apply, nbr_succ, Finset.sum_insert (not_mem_nbr α k)]
  ring

lemma consistent_canon (x : Fin d → ℝ) : IsConsistentPerm x (canonPerm x) := by
  have h := Tuple.monotone_sort (fun i => -x i)
  intro a b hab
  have := h hab
  simp only [Function.comp, neg_le_neg_iff] at this
  exact this

/-- Lemma 2(iii)-type inequality: for `y ∈ [0,1]^d` and every permutation `α`,
`f(∅) + ⟨g^α, y⟩ ≤ f̃(y)`. -/
lemma lower_bound (f : Finset (Fin d) → ℝ) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (y : Fin d → ℝ) (hy : y ∈ box d) (α : Equiv.Perm (Fin d)) :
    f ∅ + ∑ j, chainGrad f α j * y j ≤ lovasz f y := by
  set β := canonPerm y
  have hβ : IsConsistentPerm y β := consistent_canon y
  set w : Finset (Fin d) → ℝ := fun S => f ∅ + ∑ j ∈ S, chainGrad f α j
  obtain ⟨h1, h2, -, -⟩ := eq_6 f y hy β hβ
  obtain ⟨k1, -, -, -⟩ := eq_6 w y hy β hβ
  have hw : lovaszWith w y β = f ∅ + ∑ j, chainGrad f α j * y j := by
    rw [lovaszWith_eq, chainGrad_modular]
    simp [w]
  rw [← hw, k1]
  unfold lovasz
  rw [h1]
  refine Finset.sum_le_sum fun i hi => ?_
  refine mul_le_mul_of_nonneg_left ?_ (h2 i hi)
  have := base_ineq f hf α (nbr β i)
  simp only [w]; linarith

lemma sum_ind (g : Fin d → ℝ) (A : Finset (Fin d)) :
    ∑ j, g j * ind A j = ∑ j ∈ A, g j := by
  simp [ind, mul_ite, Finset.sum_ite_mem]

/-- Subgradient inequality at a vertex: `f̃(x) - f(A) ≤ ⟨g^{α_x}, x - 1_A⟩`. -/
lemma subgrad_vertex (f : Finset (Fin d) → ℝ) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (x : Fin d → ℝ) (A : Finset (Fin d)) :
    lovasz f x - f A ≤ ∑ j, chainGrad f (canonPerm x) j * (x j - ind A j) := by
  unfold lovasz
  rw [lovaszWith_eq]
  have := base_ineq f hf (canonPerm x) A
  simp only [mul_sub, Finset.sum_sub_distrib, sum_ind]
  linarith

/-- Some neighbouring point beats the Lovász extension (from (6)). -/
lemma exists_nbr_le (f : Finset (Fin d) → ℝ) (x : Fin d → ℝ) (hx : x ∈ box d) :
    ∃ i : Fin (d + 1), f (nbr (canonPerm x) i) ≤ lovasz f x := by
  obtain ⟨-, -, -, i, hi, h⟩ := eq_6 f x hx (canonPerm x) (consistent_canon x)
  exact ⟨⟨i, by omega⟩, h⟩

/-- Projection onto `[0,1]` is nonexpansive towards points of `[0,1]`. -/
lemma proj_sq_le (y z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    (max 0 (min 1 y) - z) ^ 2 ≤ (y - z) ^ 2 := by
  rcases le_total y 0 with h | h
  · rw [min_eq_right (by linarith), max_eq_left h]; nlinarith
  · rcases le_total y 1 with h' | h'
    · rw [min_eq_right h', max_eq_right h]
    · rw [min_eq_left h', max_eq_right (by norm_num)]; nlinarith

lemma ind_mem_box (A : Finset (Fin d)) : ind A ∈ box d := by
  constructor <;> intro i <;> simp only [ind, Pi.zero_apply, Pi.one_apply] <;> split_ifs <;> norm_num

lemma proj_mem_box (x : Fin d → ℝ) : proj x ∈ box d := by
  constructor <;> intro i <;> simp only [proj, Pi.zero_apply, Pi.one_apply]
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

/-- Lemma EC.4 (pathwise regret of projected steps). -/
lemma regret (T : ℕ) (x G : ℕ → Fin d → ℝ) (xs : Fin d → ℝ) (η M : ℝ) (hη : 0 < η)
    (hx0 : x 0 ∈ box d) (hxs : xs ∈ box d)
    (hstep : ∀ t < T, x (t + 1) = proj (x t - η • G t))
    (hG : ∀ t < T, ∀ j, |G t j| ≤ M) :
    ∑ t ∈ Finset.range T, ∑ j, G t j * (x t j - xs j)
      ≤ d / (2 * η) + η * T * d * M ^ 2 / 2 := by
  -- potential
  set Φ : ℕ → ℝ := fun t => ∑ j, (x t j - xs j) ^ 2
  have key : ∀ t ≤ T, 2 * η * ∑ s ∈ Finset.range t, ∑ j, G s j * (x s j - xs j) + Φ t
      ≤ Φ 0 + t * (η ^ 2 * d * M ^ 2) := by
    intro t
    induction t with
    | zero => intro _; simp
    | succ t ih =>
      intro ht
      have ih := ih (by omega)
      have hst : Φ (t + 1) ≤ Φ t - 2 * η * ∑ j, G t j * (x t j - xs j)
          + η ^ 2 * ∑ j, G t j ^ 2 := by
        simp only [Φ]
        rw [hstep t (by omega)]
        have : ∀ j, (proj (x t - η • G t) j - xs j) ^ 2
            ≤ (x t j - xs j) ^ 2 - 2 * η * (G t j * (x t j - xs j)) + η ^ 2 * G t j ^ 2 := by
          intro j
          have := proj_sq_le (x t j - η * G t j) (xs j) (hxs.1 j) (hxs.2 j)
          simp only [proj, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          nlinarith
        calc ∑ j, (proj (x t - η • G t) j - xs j) ^ 2
            ≤ ∑ j, ((x t j - xs j) ^ 2 - 2 * η * (G t j * (x t j - xs j)) + η ^ 2 * G t j ^ 2) :=
              Finset.sum_le_sum fun j _ => this j
          _ = _ := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      have hG2 : ∑ j, G t j ^ 2 ≤ d * M ^ 2 := by
        calc ∑ j, G t j ^ 2 ≤ ∑ _j : Fin d, M ^ 2 := Finset.sum_le_sum fun j _ => by
                have := hG t (by omega) j
                have h0 : 0 ≤ M := le_trans (abs_nonneg _) this
                rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
          _ = d * M ^ 2 := by simp
      rw [Finset.sum_range_succ]
      push_cast
      nlinarith
  have h := key T le_rfl
  have hΦ0 : Φ 0 ≤ d := by
    calc Φ 0 ≤ ∑ _j : Fin d, (1 : ℝ) := Finset.sum_le_sum fun j _ => by
            have a1 := hx0.1 j; have a2 := hx0.2 j; have a3 := hxs.1 j; have a4 := hxs.2 j
            simp only [Pi.zero_apply, Pi.one_apply] at a1 a2 a3 a4
            nlinarith
      _ = d := by simp
  have hΦT : 0 ≤ Φ T := Finset.sum_nonneg fun j _ => sq_nonneg _
  have h2 : 2 * η * ∑ s ∈ Finset.range T, ∑ j, G s j * (x s j - xs j)
      ≤ d + T * (η ^ 2 * d * M ^ 2) := by linarith
  rw [div_add_div _ _ (by positivity) (by norm_num), le_div_iff₀ (by positivity)]
  nlinarith

end GSSol


open MeasureTheory ProbabilityTheory GradDOvS.Submod

namespace GSSol

variable {d : ℕ}

/-! ### Measurability of functions defined piecewise through the canonical permutation -/

lemma measurable_perm_piecewise {α γ : Type*} [MeasurableSpace α] [MeasurableSpace γ]
    (p : α → Equiv.Perm (Fin d)) (hp : ∀ σ, MeasurableSet {a | p a = σ})
    (F : Equiv.Perm (Fin d) → α → γ) (hF : ∀ σ, Measurable (F σ)) :
    Measurable (fun a => F (p a) a) := by
  intro s hs
  have : (fun a => F (p a) a) ⁻¹' s = ⋃ σ, ({a | p a = σ} ∩ F σ ⁻¹' s) := by
    ext a
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro h; exact ⟨p a, rfl, h⟩
    · rintro ⟨σ, rfl, h⟩; exact h
  rw [this]
  exact MeasurableSet.iUnion fun σ => (hp σ).inter (hF σ hs)

lemma measurableSet_canonPerm (σ : Equiv.Perm (Fin d)) :
    MeasurableSet {x : Fin d → ℝ | canonPerm x = σ} := by
  have : {x : Fin d → ℝ | canonPerm x = σ} = ⋂ i, ⋂ j,
      ({x : Fin d → ℝ | i ≤ j → -x (σ i) ≤ -x (σ j)} ∩
        {x | i < j → -x (σ i) = -x (σ j) → σ i < σ j}) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_inter_iff, canonPerm]
    rw [eq_comm, Tuple.eq_sort_iff]
    constructor
    · rintro ⟨h1, h2⟩ i j; exact ⟨fun h => h1 h, fun h h' => h2 i j h h'⟩
    · intro h; exact ⟨fun i j hij => (h i j).1 hij, fun i j hij h' => (h i j).2 hij h'⟩
  rw [this]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => MeasurableSet.inter ?_ ?_
  · by_cases hij : i ≤ j
    · simp only [hij, true_implies]
      exact measurableSet_le (by fun_prop) (by fun_prop)
    · simp [hij]
  · by_cases hij : i < j
    · by_cases hs : σ i < σ j
      · simp [hs]
      · simp only [hij, hs, true_implies, imp_false]
        exact (measurableSet_eq_fun (by fun_prop) (by fun_prop)).compl
    · simp [hij]

lemma measurableSet_canonPerm_comp {α : Type*} [MeasurableSpace α] {X : α → Fin d → ℝ}
    (hX : Measurable X) (σ : Equiv.Perm (Fin d)) :
    MeasurableSet {a | canonPerm (X a) = σ} :=
  hX (measurableSet_canonPerm σ)

/-! ### The deterministic trajectory -/

abbrev V (d : ℕ) := Finset (Fin d) → ℝ

/-- One coordinate of the estimator (4) for block `k` of the consistent permutation `σ`. -/
def est (σ : Equiv.Perm (Fin d)) (k : Fin d) (v : Fin 2 → V d) : ℝ :=
  v 0 (nbr σ ((k : ℕ) + 1)) - v 1 (nbr σ k)

noncomputable def gE (x : Fin d → ℝ) (w : Fin d → Fin 2 → V d) : Fin d → ℝ :=
  fun j => est (canonPerm x) ((canonPerm x).symm j) (w ((canonPerm x).symm j))

lemma gE_apply_perm (x : Fin d → ℝ) (w : Fin d → Fin 2 → V d) (k : Fin d) :
    gE x w (canonPerm x k) = est (canonPerm x) k (w k) := by
  simp [gE]

abbrev Hist (d T : ℕ) := Fin T → Fin d → Fin 2 → V d

def H {Ω : Type*} {T n : ℕ} (Z : Slot d T n → Ω → V d) (ω : Ω) : Hist d T :=
  fun t k b => Z (Sum.inl (t, k, b)) ω

lemma gradEst_eq {Ω : Type*} {T n : ℕ} (Z : Slot d T n → Ω → V d) (t : Fin T)
    (x : Fin d → ℝ) (ω : Ω) : gradEst Z t x ω = gE x (H Z ω t) := rfl

noncomputable def step (η M : ℝ) (x : Fin d → ℝ) (w : Fin d → Fin 2 → V d) : Fin d → ℝ :=
  proj (x - η • trunc M (gE x w))

noncomputable def iterDet {T : ℕ} (η M : ℝ) (A₀ : Finset (Fin d)) (h : Hist d T) :
    ℕ → Fin d → ℝ
  | 0 => ind A₀
  | t + 1 => if ht : t < T then step η M (iterDet η M A₀ h t) (h ⟨t, ht⟩)
      else iterDet η M A₀ h t

lemma ssgdIter_eq {Ω : Type*} {T n : ℕ} (Z : Slot d T n → Ω → V d) (η M : ℝ)
    (A₀ : Finset (Fin d)) (t : ℕ) (ω : Ω) :
    ssgdIter Z η M A₀ t ω = iterDet η M A₀ (H Z ω) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [ssgdIter, iterDet, ih]
    split_ifs <;> rfl

lemma iterDet_congr {T : ℕ} (η M : ℝ) (A₀ : Finset (Fin d)) (h h' : Hist d T) (t : ℕ)
    (hh : ∀ s : Fin T, (s : ℕ) < t → h s = h' s) :
    iterDet η M A₀ h t = iterDet η M A₀ h' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have ih := ih (fun s hs => hh s (by omega))
    simp only [iterDet]
    split_ifs with ht
    · rw [ih, hh ⟨t, ht⟩ (by simp)]
    · exact ih

lemma iterDet_mem_box {T : ℕ} (η M : ℝ) (A₀ : Finset (Fin d)) (h : Hist d T) (t : ℕ) :
    iterDet η M A₀ h t ∈ box d := by
  cases t with
  | zero => exact ind_mem_box A₀
  | succ t =>
    simp only [iterDet]
    split_ifs
    · exact proj_mem_box _
    · exact iterDet_mem_box η M A₀ h t

lemma iterDet_succ {T : ℕ} (η M : ℝ) (A₀ : Finset (Fin d)) (h : Hist d T) (t : ℕ)
    (ht : t < T) :
    iterDet η M A₀ h (t + 1) = proj (iterDet η M A₀ h t
      - η • trunc M (gE (iterDet η M A₀ h t) (h ⟨t, ht⟩))) := by
  simp [iterDet, ht, step]

lemma continuous_proj : Continuous (proj : (Fin d → ℝ) → Fin d → ℝ) :=
  continuous_pi fun i => by unfold proj; fun_prop

lemma continuous_trunc (M : ℝ) : Continuous (trunc M : (Fin d → ℝ) → Fin d → ℝ) :=
  continuous_pi fun i => by unfold trunc; fun_prop

lemma measurable_gE :
    Measurable (fun p : (Fin d → ℝ) × (Fin d → Fin 2 → V d) => gE p.1 p.2) := by
  have hF : ∀ σ : Equiv.Perm (Fin d), Measurable
      (fun p : (Fin d → ℝ) × (Fin d → Fin 2 → V d) => fun j => est σ (σ.symm j) (p.2 (σ.symm j))) := by
    intro σ; unfold est; fun_prop
  have := measurable_perm_piecewise (fun p : (Fin d → ℝ) × (Fin d → Fin 2 → V d) => canonPerm p.1)
    (fun σ => measurableSet_canonPerm_comp measurable_fst σ) _ hF
  exact this

lemma measurable_step (η M : ℝ) :
    Measurable (fun p : (Fin d → ℝ) × (Fin d → Fin 2 → V d) => step η M p.1 p.2) := by
  unfold step
  have h1 := (continuous_trunc (d := d) M).measurable.comp measurable_gE
  have h2 : Measurable (fun p : (Fin d → ℝ) × (Fin d → Fin 2 → V d) =>
      p.1 - η • trunc M (gE p.1 p.2)) :=
    measurable_fst.sub (h1.const_smul η)
  exact continuous_proj.measurable.comp h2

lemma measurable_iterDet {T : ℕ} (η M : ℝ) (A₀ : Finset (Fin d)) (t : ℕ) :
    Measurable (fun h : Hist d T => iterDet η M A₀ h t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    by_cases ht : t < T
    · have : (fun h : Hist d T => iterDet η M A₀ h (t + 1))
          = fun h => step η M (iterDet η M A₀ h t) (h ⟨t, ht⟩) := by
        funext h; simp [iterDet, ht]
      rw [this]
      exact (measurable_step η M).comp (ih.prodMk (measurable_pi_apply _))
    · have : (fun h : Hist d T => iterDet η M A₀ h (t + 1))
          = fun h => iterDet η M A₀ h t := by
        funext h; simp [iterDet, ht]
      rw [this]; exact ih

noncomputable def avgDet {T : ℕ} (η M : ℝ) (A₀ : Finset (Fin d)) (h : Hist d T) : Fin d → ℝ :=
  (1 / (T : ℝ)) • ∑ t ∈ Finset.range T, iterDet η M A₀ h t

lemma ssgdAvg_eq {Ω : Type*} {T n : ℕ} (Z : Slot d T n → Ω → V d) (η M : ℝ)
    (A₀ : Finset (Fin d)) (ω : Ω) :
    ssgdAvg Z η M A₀ ω = avgDet η M A₀ (H Z ω) := by
  simp only [ssgdAvg, avgDet, ssgdIter_eq]

lemma measurable_avgDet {T : ℕ} (η M : ℝ) (A₀ : Finset (Fin d)) :
    Measurable (fun h : Hist d T => avgDet η M A₀ h) := by
  unfold avgDet
  exact (Finset.measurable_sum (Finset.range T)
    (fun t _ => measurable_iterDet (T := T) η M A₀ t)).const_smul (1 / (T : ℝ))

lemma measurable_H {Ω : Type*} [MeasurableSpace Ω] {T n : ℕ} (Z : Slot d T n → Ω → V d)
    (hZ : ∀ s, Measurable (Z s)) : Measurable (H Z) := by
  unfold H
  exact measurable_pi_lambda _ fun t => measurable_pi_lambda _ fun k =>
    measurable_pi_lambda _ fun b => hZ _

/-! ### Freezing lemma -/

lemma freeze {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {U : Ω → α} {W : Ω → β} (hU : Measurable U) (hW : Measurable W) (hind : IndepFun U W P)
    {F : α × β → ENNReal} (hF : Measurable F) :
    ∫⁻ ω, F (U ω, W ω) ∂P = ∫⁻ ω, ∫⁻ ω', F (U ω, W ω') ∂P ∂P := by
  have h1 : P.map (fun ω => (U ω, W ω)) = (P.map U).prod (P.map W) :=
    (indepFun_iff_map_prod_eq_prod_map_map hU.aemeasurable hW.aemeasurable).1 hind
  rw [← lintegral_map hF (hU.prodMk hW), h1, lintegral_prod _ hF.aemeasurable,
    lintegral_map hF.lintegral_prod_right' hU]
  congr 1
  funext ω
  exact lintegral_map (hF.comp measurable_prodMk_left) hW

end GSSol


open MeasureTheory ProbabilityTheory GradDOvS.Submod

namespace GSSol

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Jensen for `exp`. -/
lemma exp_integral_le {X : Ω → ℝ} (hX : Integrable X P)
    (hE : Integrable (fun ω => Real.exp (X ω)) P) :
    Real.exp (∫ ω, X ω ∂P) ≤ ∫ ω, Real.exp (X ω) ∂P := by
  set m := ∫ ω, X ω ∂P
  have hpt : ∀ ω, Real.exp m * (1 + (X ω - m)) ≤ Real.exp (X ω) := by
    intro ω
    have h1 := Real.add_one_le_exp (X ω - m)
    have h2 : Real.exp m * Real.exp (X ω - m) = Real.exp (X ω) := by
      rw [← Real.exp_add]; ring_nf
    have hm := Real.exp_pos m
    nlinarith
  have hint : Integrable (fun ω => Real.exp m * (1 + (X ω - m))) P :=
    ((integrable_const 1).add (hX.sub (integrable_const m))).const_mul _
  have := integral_mono hint hE hpt
  have e : ∫ ω, (1 + (X ω - m)) ∂P = 1 := by
    rw [integral_add (integrable_const _)
      (by exact hX.sub (integrable_const m) : Integrable (fun ω => X ω - m) P),
      integral_sub hX (integrable_const _)]
    simp [m]
  rw [integral_const_mul, e, mul_one] at this
  exact this

/-- A sub-Gaussian variable is centred. -/
lemma integral_eq_zero_of_subG {X : Ω → ℝ} {c : NNReal} (h : HasSubgaussianMGF X c P) :
    ∫ ω, X ω ∂P = 0 := by
  set m := ∫ ω, X ω ∂P
  have key : ∀ t : ℝ, t * m ≤ c * t ^ 2 / 2 := by
    intro t
    have hX := h.integrable
    have h1 := exp_integral_le (hX.const_mul t) (h.integrable_exp_mul t)
    rw [integral_const_mul] at h1
    have h2 := h.mgf_le t
    have h3 : Real.exp (t * m) ≤ Real.exp (c * t ^ 2 / 2) := le_trans h1 h2
    exact Real.exp_le_exp.1 h3
  have hc : (0 : ℝ) ≤ c := c.2
  have k := key (m / (c + 1))
  have hc1 : (0 : ℝ) < c + 1 := by linarith
  have : m ^ 2 * ((c : ℝ) / 2 + 1) ≤ 0 := by
    have e1 : m / (c + 1) * m = m ^ 2 / (c + 1) := by ring
    have e2 : (c : ℝ) * (m / (c + 1)) ^ 2 / 2 = c * m ^ 2 / (2 * (c + 1) ^ 2) := by
      field_simp
    rw [e1, e2, div_le_div_iff₀ hc1 (by positivity)] at k
    nlinarith [sq_nonneg m]
  have : m ^ 2 = 0 := by
    have := sq_nonneg m
    nlinarith
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this

lemma exp_abs_le (x : ℝ) : Real.exp |x| ≤ Real.exp x + Real.exp (-x) := by
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h]; linarith [Real.exp_pos (-x)]
  · rw [abs_of_nonpos h]; linarith [Real.exp_pos x]

/-- Integrability of `exp (r * φ ∘ D)` for a 1-Lipschitz `φ` and sub-Gaussian `D`. -/
lemma integrable_exp_lip {D : Ω → ℝ} {s : NNReal} (hD : HasSubgaussianMGF D s P)
    (hDm : Measurable D) {φ : ℝ → ℝ} (hφm : Measurable φ)
    (hφ : ∀ a b, |φ a - φ b| ≤ |a - b|) (r : ℝ) :
    Integrable (fun ω => Real.exp (r * φ (D ω))) P := by
  have hb : Integrable (fun ω => Real.exp (|r| * |φ 0|) *
      (Real.exp (|r| * D ω) + Real.exp (-|r| * D ω))) P :=
    ((hD.integrable_exp_mul |r|).add (hD.integrable_exp_mul (-|r|))).const_mul _
  refine hb.mono' ?_ (ae_of_all _ fun ω => ?_)
  · exact (Real.measurable_exp.comp ((hφm.comp hDm).const_mul r)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have h1 : r * φ (D ω) ≤ |r| * |φ 0| + |r| * |D ω| := by
      have := hφ (D ω) 0
      have h2 : |φ (D ω)| ≤ |φ 0| + |D ω| := by
        have := abs_sub_abs_le_abs_sub (φ (D ω)) (φ 0)
        simp only [sub_zero] at *; linarith
      calc r * φ (D ω) ≤ |r * φ (D ω)| := le_abs_self _
        _ = |r| * |φ (D ω)| := abs_mul _ _
        _ ≤ |r| * (|φ 0| + |D ω|) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
        _ = _ := by ring
    calc Real.exp (r * φ (D ω)) ≤ Real.exp (|r| * |φ 0| + |r| * |D ω|) := Real.exp_le_exp.2 h1
      _ = Real.exp (|r| * |φ 0|) * Real.exp |(|r| * D ω)| := by
        rw [Real.exp_add, abs_mul, abs_abs]
      _ ≤ _ := by
        gcongr
        have := exp_abs_le (|r| * D ω)
        simpa [neg_mul] using this

lemma integrable_lip {D : Ω → ℝ} {s : NNReal} (hD : HasSubgaussianMGF D s P)
    (hDm : Measurable D) {φ : ℝ → ℝ} (hφm : Measurable φ)
    (hφ : ∀ a b, |φ a - φ b| ≤ |a - b|) :
    Integrable (fun ω => φ (D ω)) P := by
  refine ((integrable_const |φ 0|).add hD.integrable.abs).mono'
    (hφm.comp hDm).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs]
  show |φ (D ω)| ≤ |φ 0| + |D ω|
  have := abs_sub_abs_le_abs_sub (φ (D ω)) (φ 0)
  have h2 := hφ (D ω) 0
  simp only [sub_zero] at h2
  linarith

lemma ofReal_exp_lintegral {X : Ω → ℝ} (hX : Integrable (fun ω => Real.exp (X ω)) P) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (X ω)) ∂P = ENNReal.ofReal (∫ ω, Real.exp (X ω) ∂P) :=
  (ofReal_integral_eq_lintegral_ofReal hX (ae_of_all _ fun ω => (Real.exp_pos _).le)).symm

/-- Symmetrisation: a 1-Lipschitz image of a `s`-sub-Gaussian variable, once centred,
has moment generating function at most `exp (λ² s)`. -/
lemma lip_centered_mgf {D : Ω → ℝ} {s : NNReal} (hD : HasSubgaussianMGF D s P)
    (hDm : Measurable D) {φ : ℝ → ℝ} (hφm : Measurable φ)
    (hφ : ∀ a b, |φ a - φ b| ≤ |a - b|) (l : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (l * (φ (D ω) - ∫ ω', φ (D ω') ∂P))) ∂P
      ≤ ENNReal.ofReal (Real.exp (s * l ^ 2)) := by
  set m := ∫ ω', φ (D ω') ∂P
  have hAm : Measurable (fun ω => φ (D ω)) := hφm.comp hDm
  have hint := integrable_lip hD hDm hφm hφ
  -- Jensen
  have hJ : Real.exp (-l * m) ≤ ∫ ω, Real.exp (-l * φ (D ω)) ∂P := by
    have := exp_integral_le (hint.const_mul (-l)) (integrable_exp_lip hD hDm hφm hφ (-l))
    rwa [integral_const_mul] at this
  set a := ∫⁻ ω, ENNReal.ofReal (Real.exp (l * φ (D ω))) ∂P
  set b := ∫⁻ ω, ENNReal.ofReal (Real.exp (-l * φ (D ω))) ∂P
  set a' := ∫⁻ ω, ENNReal.ofReal (Real.exp (l * D ω)) ∂P
  set b' := ∫⁻ ω, ENNReal.ofReal (Real.exp (-l * D ω)) ∂P
  have hmeasE : ∀ r : ℝ, Measurable (fun ω => ENNReal.ofReal (Real.exp (r * φ (D ω)))) :=
    fun r => ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hAm.const_mul r))
  have hmeasD : ∀ r : ℝ, Measurable (fun ω => ENNReal.ofReal (Real.exp (r * D ω))) :=
    fun r => ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hDm.const_mul r))
  -- step 1
  have step1 : ∫⁻ ω, ENNReal.ofReal (Real.exp (l * (φ (D ω) - m))) ∂P
      = ENNReal.ofReal (Real.exp (-l * m)) * a := by
    rw [← lintegral_const_mul _ (hmeasE l)]
    refine lintegral_congr fun ω => ?_
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2; ring
  have hb : ENNReal.ofReal (Real.exp (-l * m)) ≤ b := by
    have : b = ENNReal.ofReal (∫ ω, Real.exp (-l * φ (D ω)) ∂P) :=
      ofReal_exp_lintegral (integrable_exp_lip hD hDm hφm hφ (-l))
    rw [this]
    exact ENNReal.ofReal_le_ofReal hJ
  -- step 2 : 2ab ≤ 2a'b'
  have hpt : ∀ ω ω',
      ENNReal.ofReal (Real.exp (l * φ (D ω))) * ENNReal.ofReal (Real.exp (-l * φ (D ω')))
      + ENNReal.ofReal (Real.exp (-l * φ (D ω))) * ENNReal.ofReal (Real.exp (l * φ (D ω')))
      ≤ ENNReal.ofReal (Real.exp (l * D ω)) * ENNReal.ofReal (Real.exp (-l * D ω'))
      + ENNReal.ofReal (Real.exp (-l * D ω)) * ENNReal.ofReal (Real.exp (l * D ω')) := by
    intro ω ω'
    simp only [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le,
      ← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
    apply ENNReal.ofReal_le_ofReal
    have hc : Real.cosh (l * (φ (D ω) - φ (D ω'))) ≤ Real.cosh (l * (D ω - D ω')) := by
      rw [Real.cosh_le_cosh, abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (hφ _ _) (abs_nonneg _)
    rw [Real.cosh_eq, Real.cosh_eq] at hc
    have e1 : l * φ (D ω) + -l * φ (D ω') = l * (φ (D ω) - φ (D ω')) := by ring
    have e2 : -l * φ (D ω) + l * φ (D ω') = -(l * (φ (D ω) - φ (D ω'))) := by ring
    have e3 : l * D ω + -l * D ω' = l * (D ω - D ω') := by ring
    have e4 : -l * D ω + l * D ω' = -(l * (D ω - D ω')) := by ring
    rw [e1, e2, e3, e4]
    linarith
  have L1 : ∀ (f g : Ω → ENNReal), Measurable f → Measurable g →
      ∫⁻ ω, ∫⁻ ω', f ω * g ω' ∂P ∂P = (∫⁻ ω, f ω ∂P) * ∫⁻ ω, g ω ∂P := by
    intro f g hf hg
    exact lintegral_lintegral_mul hf.aemeasurable hg.aemeasurable
  have M2 : ∀ (f g : Ω → ENNReal), Measurable f → Measurable g →
      Measurable (fun ω => ∫⁻ ω', f ω * g ω' ∂P) := by
    intro f g hf hg
    exact ((hf.comp measurable_fst).mul (hg.comp measurable_snd)).lintegral_prod_right'
  have hab : a * b + b * a ≤ a' * b' + b' * a' := by
    calc a * b + b * a
        = (∫⁻ ω, ∫⁻ ω', ENNReal.ofReal (Real.exp (l * φ (D ω)))
              * ENNReal.ofReal (Real.exp (-l * φ (D ω'))) ∂P ∂P)
          + ∫⁻ ω, ∫⁻ ω', ENNReal.ofReal (Real.exp (-l * φ (D ω)))
              * ENNReal.ofReal (Real.exp (l * φ (D ω'))) ∂P ∂P := by
          rw [L1 _ _ (hmeasE l) (hmeasE (-l)), L1 _ _ (hmeasE (-l)) (hmeasE l)]
      _ = ∫⁻ ω, ((∫⁻ ω', ENNReal.ofReal (Real.exp (l * φ (D ω)))
              * ENNReal.ofReal (Real.exp (-l * φ (D ω'))) ∂P)
          + ∫⁻ ω', ENNReal.ofReal (Real.exp (-l * φ (D ω)))
              * ENNReal.ofReal (Real.exp (l * φ (D ω'))) ∂P) ∂P :=
          (lintegral_add_left (M2 _ _ (hmeasE l) (hmeasE (-l))) _).symm
      _ = ∫⁻ ω, ∫⁻ ω', (ENNReal.ofReal (Real.exp (l * φ (D ω)))
              * ENNReal.ofReal (Real.exp (-l * φ (D ω')))
          + ENNReal.ofReal (Real.exp (-l * φ (D ω)))
              * ENNReal.ofReal (Real.exp (l * φ (D ω')))) ∂P ∂P := by
          refine lintegral_congr fun ω => ?_
          exact (lintegral_add_left (measurable_const.mul (hmeasE (-l))) _).symm
      _ ≤ ∫⁻ ω, ∫⁻ ω', (ENNReal.ofReal (Real.exp (l * D ω))
              * ENNReal.ofReal (Real.exp (-l * D ω'))
          + ENNReal.ofReal (Real.exp (-l * D ω))
              * ENNReal.ofReal (Real.exp (l * D ω'))) ∂P ∂P :=
          lintegral_mono fun ω => lintegral_mono fun ω' => hpt ω ω'
      _ = ∫⁻ ω, ((∫⁻ ω', ENNReal.ofReal (Real.exp (l * D ω))
              * ENNReal.ofReal (Real.exp (-l * D ω')) ∂P)
          + ∫⁻ ω', ENNReal.ofReal (Real.exp (-l * D ω))
              * ENNReal.ofReal (Real.exp (l * D ω')) ∂P) ∂P := by
          refine lintegral_congr fun ω => ?_
          exact lintegral_add_left (measurable_const.mul (hmeasD (-l))) _
      _ = (∫⁻ ω, ∫⁻ ω', ENNReal.ofReal (Real.exp (l * D ω))
              * ENNReal.ofReal (Real.exp (-l * D ω')) ∂P ∂P)
          + ∫⁻ ω, ∫⁻ ω', ENNReal.ofReal (Real.exp (-l * D ω))
              * ENNReal.ofReal (Real.exp (l * D ω')) ∂P ∂P :=
          lintegral_add_left (M2 _ _ (hmeasD l) (hmeasD (-l))) _
      _ = a' * b' + b' * a' := by
          rw [L1 _ _ (hmeasD l) (hmeasD (-l)), L1 _ _ (hmeasD (-l)) (hmeasD l)]
  have hab2 : a * b ≤ a' * b' := by
    rw [mul_comm b a, mul_comm b' a', ← two_mul, ← two_mul] at hab
    exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).1 hab
  have ha' : a' ≤ ENNReal.ofReal (Real.exp (s * l ^ 2 / 2)) := by
    have : a' = ENNReal.ofReal (∫ ω, Real.exp (l * D ω) ∂P) :=
      ofReal_exp_lintegral (hD.integrable_exp_mul l)
    rw [this]
    exact ENNReal.ofReal_le_ofReal (hD.mgf_le l)
  have hb' : b' ≤ ENNReal.ofReal (Real.exp (s * l ^ 2 / 2)) := by
    have e : b' = ENNReal.ofReal (∫ ω, Real.exp (-l * D ω) ∂P) :=
      ofReal_exp_lintegral (hD.integrable_exp_mul (-l))
    rw [e]
    have := hD.mgf_le (-l)
    rw [neg_sq] at this
    exact ENNReal.ofReal_le_ofReal this
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (l * (φ (D ω) - m))) ∂P
      = ENNReal.ofReal (Real.exp (-l * m)) * a := step1
    _ ≤ b * a := by gcongr
    _ = a * b := mul_comm _ _
    _ ≤ a' * b' := hab2
    _ ≤ ENNReal.ofReal (Real.exp (s * l ^ 2 / 2)) * ENNReal.ofReal (Real.exp (s * l ^ 2 / 2)) := by
        gcongr
    _ = ENNReal.ofReal (Real.exp (s * l ^ 2)) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        congr 2; ring

/-- `r ↦ clip_{[-M,M]}(g + r)` is 1-Lipschitz. -/
lemma clip_lip (M g : ℝ) (a b : ℝ) :
    |max (-M) (min M (g + a)) - max (-M) (min M (g + b))| ≤ |a - b| := by
  rw [max_comm (-M), max_comm (-M)]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  simp only [sub_self, abs_zero]
  rw [max_eq_right (abs_nonneg _)]
  ring_nf; exact le_rfl

lemma measurable_clip (M g : ℝ) : Measurable (fun r : ℝ => max (-M) (min M (g + r))) := by
  fun_prop

lemma clip_err (M g L r : ℝ) (hM : 0 ≤ M) (hg : |g| ≤ L) :
    |max (-M) (min M (g + r)) - (g + r)| ≤ max 0 (|r| - (M - L)) := by
  have hr : |g + r| ≤ L + |r| := (abs_add_le _ _).trans (by linarith)
  rcases le_total (g + r) M with h1 | h1
  · rw [min_eq_right h1]
    rcases le_total (-M) (g + r) with h2 | h2
    · rw [max_eq_right h2, sub_self, abs_zero]; exact le_max_left _ _
    · rw [max_eq_left h2]
      rw [abs_of_nonneg (by linarith)]
      refine le_trans ?_ (le_max_right _ _)
      have := neg_abs_le (g + r)
      linarith
  · rw [min_eq_left h1, max_eq_right (by linarith [abs_nonneg (g + r), neg_abs_le (g+r)])]
    rw [abs_of_nonpos (by linarith)]
    refine le_trans ?_ (le_max_right _ _)
    have := le_abs_self (g + r)
    linarith

lemma pos_part_le_exp (z l : ℝ) (hl : 0 < l) : max 0 z ≤ Real.exp (l * z) / l := by
  rw [le_div_iff₀ hl]
  rcases le_total z 0 with h | h
  · rw [max_eq_left h]; simp [(Real.exp_pos _).le]
  · rw [max_eq_right h]
    have := Real.add_one_le_exp (l * z)
    nlinarith

/-- Lemma EC.2-type bias bound for a single truncated coordinate. -/
lemma trunc_bias {D : Ω → ℝ} {s : NNReal} (hs : 0 < (s : ℝ)) (hD : HasSubgaussianMGF D s P)
    (hDm : Measurable D) (g L M : ℝ) (hg : |g| ≤ L) (hLM : L < M) :
    |∫ ω, max (-M) (min M (g + D ω)) ∂P - g|
      ≤ (2 * s / (M - L)) * Real.exp (-(M - L) ^ 2 / (2 * s)) := by
  set a := M - L with ha_def
  have ha : 0 < a := by linarith
  set l := a / s with hl_def
  have hl : 0 < l := div_pos ha hs
  have hY := integrable_lip hD hDm (measurable_clip M g) (fun x y => clip_lip M g x y)
  have hD0 := integral_eq_zero_of_subG hD
  have hInt := hD.integrable
  have e1 : ∫ ω, max (-M) (min M (g + D ω)) ∂P - g
      = ∫ ω, (max (-M) (min M (g + D ω)) - (g + D ω)) ∂P := by
    rw [integral_sub hY (by exact (integrable_const g).add hInt :
      Integrable (fun ω => g + D ω) P), integral_add (integrable_const g) hInt, hD0]
    simp
  rw [e1]
  have hB : Integrable (fun ω => (Real.exp (l * D ω) + Real.exp (-l * D ω))
      * (Real.exp (-(l * a)) / l)) P :=
    ((hD.integrable_exp_mul l).add (hD.integrable_exp_mul (-l))).mul_const _
  have hpt : ∀ ω, |max (-M) (min M (g + D ω)) - (g + D ω)|
      ≤ (Real.exp (l * D ω) + Real.exp (-l * D ω)) * (Real.exp (-(l * a)) / l) := by
    intro ω
    refine (clip_err M g L (D ω) (by linarith [abs_nonneg g]) hg).trans ?_
    refine (pos_part_le_exp _ l hl).trans ?_
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hl]
    have : Real.exp (l * (|D ω| - a)) = Real.exp |l * D ω| * Real.exp (-(l * a)) := by
      rw [← Real.exp_add, abs_mul, abs_of_pos hl]; ring_nf
    rw [this]
    gcongr
    have := exp_abs_le (l * D ω)
    simpa [neg_mul] using this
  calc |∫ ω, (max (-M) (min M (g + D ω)) - (g + D ω)) ∂P|
      ≤ ∫ ω, |max (-M) (min M (g + D ω)) - (g + D ω)| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ ω, (Real.exp (l * D ω) + Real.exp (-l * D ω)) * (Real.exp (-(l * a)) / l) ∂P :=
        integral_mono (hY.sub ((integrable_const g).add hInt)).abs hB hpt
    _ = (mgf D P l + mgf D P (-l)) * (Real.exp (-(l * a)) / l) := by
        rw [integral_mul_const, integral_add (hD.integrable_exp_mul l) (hD.integrable_exp_mul (-l))]
        rfl
    _ ≤ (Real.exp (s * l ^ 2 / 2) + Real.exp (s * (-l) ^ 2 / 2)) * (Real.exp (-(l * a)) / l) := by
        gcongr
        · exact hD.mgf_le l
        · exact hD.mgf_le (-l)
    _ = (2 * s / a) * Real.exp (-a ^ 2 / (2 * s)) := by
        rw [neg_sq, ← two_mul, mul_assoc, mul_div_assoc', ← Real.exp_add]
        have e2 : s * l ^ 2 / 2 + -(l * a) = -a ^ 2 / (2 * s) := by
          rw [hl_def]; field_simp; ring
        rw [e2, hl_def]
        field_simp

end GSSol


open MeasureTheory ProbabilityTheory GradDOvS.Submod

namespace GSSol

section Model

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d T n : ℕ}
  {f : Finset (Fin d) → ℝ} {σ0 : NNReal} {Z : Slot d T n → Ω → V d}

lemma measurable_est (σ : Equiv.Perm (Fin d)) (k : Fin d) :
    Measurable (fun v : Fin 2 → V d => est σ k v) := by
  unfold est; fun_prop

lemma est_subG (hZ : IsSimOracle P f σ0 Z) (t : Fin T) (σ : Equiv.Perm (Fin d)) (k : Fin d) :
    HasSubgaussianMGF (fun ω => est σ k (H Z ω t k) - (f (nbr σ ((k : ℕ) + 1)) - f (nbr σ k)))
      (σ0 ^ 2 + σ0 ^ 2) P := by
  have h0 := hZ.subgaussian (Sum.inl (t, k, 0)) (nbr σ ((k : ℕ) + 1))
  have h1 := hZ.subgaussian (Sum.inl (t, k, 1)) (nbr σ k)
  have hind : IndepFun (Z (Sum.inl (t, k, 0))) (Z (Sum.inl (t, k, 1))) P :=
    hZ.indep.indepFun (by simp)
  have hind2 := hind.comp
    ((measurable_pi_apply (nbr σ ((k : ℕ) + 1))).sub_const (f (nbr σ ((k : ℕ) + 1))))
    ((measurable_pi_apply (nbr σ k)).sub_const (f (nbr σ k)))
  have := h0.sub_of_indepFun h1 hind2
  refine this.congr (ae_of_all _ fun ω => ?_)
  simp only [est, H]
  ring

lemma measurable_est_H (hZ : IsSimOracle P f σ0 Z) (t : Fin T) (σ : Equiv.Perm (Fin d))
    (k : Fin d) : Measurable (fun ω => est σ k (H Z ω t k)) :=
  (measurable_est σ k).comp ((measurable_pi_apply k).comp
    ((measurable_pi_apply t).comp (measurable_H Z hZ.measurable)))

variable (P Z) in
/-- `E[T_M(ĝ)]` at block `k` of iteration `t` for the permutation `σ`. -/
noncomputable def mB (M : ℝ) (t : Fin T) (σ : Equiv.Perm (Fin d)) (k : Fin d) : ℝ :=
  ∫ ω, max (-M) (min M (est σ k (H Z ω t k))) ∂P

lemma mB_bias (hZ : IsSimOracle P f σ0 Z) {L M : ℝ} (hf : Standing L f) (hσ : 0 < σ0)
    (hLM : L < M) (t : Fin T) (σ : Equiv.Perm (Fin d)) (k : Fin d) :
    |mB P Z M t σ k - chainGrad f σ (σ k)|
      ≤ (2 * (σ0 ^ 2 + σ0 ^ 2 : NNReal) / (M - L))
        * Real.exp (-(M - L) ^ 2 / (2 * (σ0 ^ 2 + σ0 ^ 2 : NNReal))) := by
  set g := f (nbr σ ((k : ℕ) + 1)) - f (nbr σ k)
  have hcg : chainGrad f σ (σ k) = g := chainGrad_apply f σ k
  have hs : (0 : ℝ) < ((σ0 ^ 2 + σ0 ^ 2 : NNReal) : ℝ) := by
    push_cast; have : (0 : ℝ) < σ0 := hσ; positivity
  have key := trunc_bias hs (est_subG hZ t σ k) ((measurable_est_H hZ t σ k).sub_const _) g L M
    (hf.lipschitz _ _) hLM
  rw [hcg]
  convert key using 4
  unfold mB
  congr 1; funext ω; congr 2; ring

variable (P Z) in
/-- The martingale-difference term of block `(t,k)`. -/
noncomputable def Xi (η M : ℝ) (A₀ As : Finset (Fin d)) (t : Fin T) (k : Fin d)
    (u : Hist d T) (v : Fin 2 → V d) : ℝ :=
  (iterDet η M A₀ u t (canonPerm (iterDet η M A₀ u t) k)
      - ind As (canonPerm (iterDet η M A₀ u t) k))
    * (mB P Z M t (canonPerm (iterDet η M A₀ u t)) k
      - max (-M) (min M (est (canonPerm (iterDet η M A₀ u t)) k v)))

lemma measurable_Xi (η M : ℝ) (A₀ As : Finset (Fin d)) (t : Fin T) (k : Fin d) :
    Measurable (fun p : Hist d T × (Fin 2 → V d) => Xi P Z η M A₀ As t k p.1 p.2) := by
  have hit : Measurable (fun p : Hist d T × (Fin 2 → V d) => iterDet η M A₀ p.1 t) :=
    (measurable_iterDet η M A₀ t).comp measurable_fst
  have hF : ∀ σ : Equiv.Perm (Fin d), Measurable (fun p : Hist d T × (Fin 2 → V d) =>
      (iterDet η M A₀ p.1 t (σ k) - ind As (σ k))
        * (mB P Z M t σ k - max (-M) (min M (est σ k p.2)))) := by
    intro σ
    have h1 : Measurable (fun p : Hist d T × (Fin 2 → V d) => iterDet η M A₀ p.1 t (σ k)) :=
      (measurable_pi_apply _).comp hit
    have h2 : Measurable (fun p : Hist d T × (Fin 2 → V d) => est σ k p.2) :=
      (measurable_est σ k).comp measurable_snd
    exact (h1.sub_const _).mul (measurable_const.sub
      (measurable_const.max (measurable_const.min h2)))
  exact measurable_perm_piecewise (fun p : Hist d T × (Fin 2 → V d) =>
    canonPerm (iterDet η M A₀ p.1 t)) (fun σ => measurableSet_canonPerm_comp hit σ) _ hF

lemma measurable_Xi_diag (η M : ℝ) (A₀ As : Finset (Fin d)) (t : Fin T) (k : Fin d) :
    Measurable (fun u : Hist d T => Xi P Z η M A₀ As t k u (u t k)) :=
  (measurable_Xi η M A₀ As t k).comp (measurable_id.prodMk
    ((measurable_pi_apply k).comp (measurable_pi_apply t)))

lemma block_mgf (hZ : IsSimOracle P f σ0 Z) (η M : ℝ) (hM : 0 ≤ M) (A₀ As : Finset (Fin d))
    (t : Fin T) (k : Fin d) (u : Hist d T) (l : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (l * Xi P Z η M A₀ As t k u (H Z ω t k))) ∂P
      ≤ ENNReal.ofReal (Real.exp ((σ0 ^ 2 + σ0 ^ 2 : NNReal) * l ^ 2)) := by
  set x := iterDet η M A₀ u t
  set σ := canonPerm x
  set c := x (σ k) - ind As (σ k)
  have hx := iterDet_mem_box η M A₀ u (t : ℕ)
  have hi := ind_mem_box As
  have hc : c ^ 2 ≤ 1 := by
    have a1 := hx.1 (σ k); have a2 := hx.2 (σ k); have a3 := hi.1 (σ k); have a4 := hi.2 (σ k)
    simp only [Pi.zero_apply, Pi.one_apply] at a1 a2 a3 a4
    simp only [c]; nlinarith
  set g := f (nbr σ ((k : ℕ) + 1)) - f (nbr σ k)
  set D := fun ω => est σ k (H Z ω t k) - g
  have hD := est_subG hZ t σ k
  have hDm : Measurable D := (measurable_est_H hZ t σ k).sub_const _
  have key := lip_centered_mgf hD hDm (measurable_clip M g) (fun a b => clip_lip M g a b) (-l * c)
  have hm : mB P Z M t σ k = ∫ ω', max (-M) (min M (g + D ω')) ∂P := by
    unfold mB; congr 1; funext ω; simp only [D]; congr 2; ring
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (l * Xi P Z η M A₀ As t k u (H Z ω t k))) ∂P
      = ∫⁻ ω, ENNReal.ofReal (Real.exp (-l * c * (max (-M) (min M (g + D ω))
          - ∫ ω', max (-M) (min M (g + D ω')) ∂P))) ∂P := by
        refine lintegral_congr fun ω => ?_
        have e : g + D ω = est σ k (H Z ω t k) := by simp only [D]; ring
        have : l * Xi P Z η M A₀ As t k u (H Z ω t k) = -l * c * (max (-M) (min M (g + D ω))
            - ∫ ω', max (-M) (min M (g + D ω')) ∂P) := by
          rw [← hm, e]
          show l * ((x (σ k) - ind As (σ k))
            * (mB P Z M t σ k - max (-M) (min M (est σ k (H Z ω t k))))) = _
          simp only [c]; ring
        rw [this]
    _ ≤ ENNReal.ofReal (Real.exp ((σ0 ^ 2 + σ0 ^ 2 : NNReal) * (-l * c) ^ 2)) := key
    _ ≤ ENNReal.ofReal (Real.exp ((σ0 ^ 2 + σ0 ^ 2 : NNReal) * l ^ 2)) := by
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.2
        have : (0 : ℝ) ≤ ((σ0 ^ 2 + σ0 ^ 2 : NNReal) : ℝ) := NNReal.coe_nonneg _
        have : (-l * c) ^ 2 ≤ l ^ 2 := by
          rw [mul_pow, neg_sq]; nlinarith [sq_nonneg l]
        exact mul_le_mul_of_nonneg_left this (by assumption)

end Model

end GSSol


open MeasureTheory ProbabilityTheory GradDOvS.Submod

namespace GSSol

section Mart

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d T n : ℕ}
  {f : Finset (Fin d) → ℝ} {σ0 : NNReal} {Z : Slot d T n → Ω → V d}

def flat (t : Fin T) (k : Fin d) : ℕ := (t : ℕ) * d + k

def blk (d T N : ℕ) : Finset (Fin T × Fin d) := Finset.univ.filter (fun p => flat p.1 p.2 < N)

noncomputable def mask (N : ℕ) (u : Hist d T) : Hist d T :=
  fun t k b => if flat t k < N then u t k b else 0

variable (P Z) in
noncomputable def Qs (η M : ℝ) (A₀ As : Finset (Fin d)) (N : ℕ) (u : Hist d T) : ℝ :=
  ∑ p ∈ blk d T N, Xi P Z η M A₀ As p.1 p.2 u (u p.1 p.2)

lemma flat_lt_of_lt {t s : Fin T} (k j : Fin d) (h : (s : ℕ) < t) :
    flat s j < flat t k := by
  unfold flat
  have h1 : (s : ℕ) * d + j < ((s : ℕ) + 1) * d := by
    have := j.2; rw [add_mul, one_mul]; omega
  have h2 : ((s : ℕ) + 1) * d ≤ (t : ℕ) * d := Nat.mul_le_mul_right _ h
  omega

lemma iterDet_mask (η M : ℝ) (A₀ : Finset (Fin d)) (N : ℕ) (u : Hist d T) (t : Fin T)
    (k : Fin d) (h : flat t k ≤ N) :
    iterDet η M A₀ (mask N u) t = iterDet η M A₀ u t := by
  apply iterDet_congr
  intro s hs
  funext j b
  have : flat s j < N := lt_of_lt_of_le (flat_lt_of_lt k j hs) h
  simp [mask, this]

lemma Xi_mask (η M : ℝ) (A₀ As : Finset (Fin d)) (N : ℕ) (u : Hist d T) (t : Fin T)
    (k : Fin d) (h : flat t k ≤ N) (v : Fin 2 → V d) :
    Xi P Z η M A₀ As t k (mask N u) v = Xi P Z η M A₀ As t k u v := by
  unfold Xi; rw [iterDet_mask η M A₀ N u t k h]

lemma Qs_mask (η M : ℝ) (A₀ As : Finset (Fin d)) (N : ℕ) (u : Hist d T) :
    Qs P Z η M A₀ As N (mask N u) = Qs P Z η M A₀ As N u := by
  unfold Qs
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' : flat p.1 p.2 < N := (Finset.mem_filter.1 hp).2
  rw [Xi_mask η M A₀ As N u p.1 p.2 hp'.le]
  congr 1
  funext b; simp [mask, hp']

lemma measurable_mask (N : ℕ) : Measurable (mask (d := d) (T := T) N) := by
  refine measurable_pi_lambda _ fun t => measurable_pi_lambda _ fun k =>
    measurable_pi_lambda _ fun b => ?_
  unfold mask
  by_cases hc : flat t k < N
  · simp only [hc, if_true]
    exact (measurable_pi_apply b).comp ((measurable_pi_apply k).comp (measurable_pi_apply t))
  · simp only [hc, if_false]; exact measurable_const

lemma measurable_Qs (η M : ℝ) (A₀ As : Finset (Fin d)) (N : ℕ) :
    Measurable (Qs P Z η M A₀ As (T := T) N) := by
  show Measurable fun u : Hist d T => ∑ p ∈ blk d T N, Xi P Z η M A₀ As p.1 p.2 u (u p.1 p.2)
  exact Finset.measurable_sum _ fun p _ => measurable_Xi_diag η M A₀ As p.1 p.2

lemma blk_zero : blk d T 0 = ∅ := by
  ext p; simp [blk]

lemma blk_full : blk d T (T * d) = Finset.univ := by
  ext p
  simp only [blk, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  unfold flat
  have h1 : (p.1 : ℕ) * d + p.2 < ((p.1 : ℕ) + 1) * d := by
    rw [add_mul, one_mul]; have := p.2.2; omega
  have h2 : ((p.1 : ℕ) + 1) * d ≤ T * d := Nat.mul_le_mul_right _ p.1.2
  omega

lemma blk_succ (N : ℕ) (hN : N < T * d) :
    ∃ t : Fin T, ∃ k : Fin d, flat t k = N ∧ blk d T (N + 1) = insert (t, k) (blk d T N) ∧
      (t, k) ∉ blk d T N := by
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h; simp at hN
    · exact h
  have hNd : N / d < T := Nat.div_lt_of_lt_mul (by rwa [mul_comm])
  refine ⟨⟨N / d, hNd⟩, ⟨N % d, Nat.mod_lt _ hd⟩, ?_, ?_, ?_⟩
  · simp [flat, Nat.div_add_mod']
  · ext p
    simp only [blk, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h
      rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
      · exact Or.inr h
      · left
        have e1 : flat p.1 p.2 / d = p.1 := by
          unfold flat
          rw [add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt p.2.2, zero_add]
        have e2 : flat p.1 p.2 % d = p.2 := by
          unfold flat
          rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt p.2.2]
        rw [h] at e1 e2
        ext
        · simp [← e1]
        · simp [← e2]
    · rintro (h | h)
      · subst h; simp [flat, Nat.div_add_mod']
      · omega
  · intro h
    have h' := (Finset.mem_filter.1 h).2
    have hf : flat (⟨N / d, hNd⟩ : Fin T) (⟨N % d, Nat.mod_lt _ hd⟩ : Fin d) = N := by
      simp [flat, Nat.div_add_mod']
    rw [hf] at h'
    exact lt_irrefl _ h'

lemma indep_mask (hZ : IsSimOracle P f σ0 Z) (N : ℕ) (t : Fin T) (k : Fin d)
    (hN : flat t k = N) :
    IndepFun (fun ω => mask N (H Z ω)) (fun ω => H Z ω t k) P := by
  classical
  let S : Finset (Slot d T n) := Finset.univ.filter
    (fun s => Sum.elim (fun q : Fin T × Fin d × Fin 2 => flat q.1 q.2.1 < N) (fun _ => False) s)
  let R : Finset (Slot d T n) := Finset.univ.filter
    (fun s => Sum.elim (fun q : Fin T × Fin d × Fin 2 => q.1 = t ∧ q.2.1 = k) (fun _ => False) s)
  have hdisj : Disjoint S R := by
    rw [Finset.disjoint_filter]
    intro s _ h1 h2
    rcases s with q | q
    · simp only [Sum.elim_inl] at h1 h2
      obtain ⟨e1, e2⟩ := h2
      rw [e1, e2, hN] at h1
      exact lt_irrefl _ h1
    · simp at h1
  have h := hZ.indep.indepFun_finset S R hdisj hZ.measurable
  let φ : (S → V d) → Hist d T := fun r t' k' b =>
    if hc : flat t' k' < N then r ⟨Sum.inl (t', k', b), by simp [S, hc]⟩ else 0
  let ψ : (R → V d) → (Fin 2 → V d) := fun r b => r ⟨Sum.inl (t, k, b), by simp [R]⟩
  have hφ : Measurable φ := by
    refine measurable_pi_lambda _ fun t' => measurable_pi_lambda _ fun k' =>
      measurable_pi_lambda _ fun b => ?_
    by_cases hc : flat t' k' < N
    · simp only [φ, hc, dif_pos]; exact measurable_pi_apply _
    · simp only [φ, hc, dif_neg, not_false_eq_true]; exact measurable_const
  have hψ : Measurable ψ := measurable_pi_lambda _ fun b => measurable_pi_apply _
  have hc := h.comp hφ hψ
  convert hc using 1
  · funext ω t' k' b
    simp only [Function.comp, mask, φ, H]
    split_ifs <;> rfl
  · funext ω b; rfl

variable (P Z) in
lemma mgf_Q (hZ : IsSimOracle P f σ0 Z) (η M : ℝ) (hM : 0 ≤ M) (A₀ As : Finset (Fin d))
    (l : ℝ) (N : ℕ) (hN : N ≤ T * d) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (l * Qs P Z η M A₀ As N (H Z ω))) ∂P
      ≤ ENNReal.ofReal (Real.exp ((σ0 ^ 2 + σ0 ^ 2 : NNReal) * l ^ 2)) ^ N := by
  induction N with
  | zero => simp [Qs, blk_zero]
  | succ N ih =>
    obtain ⟨t, k, hflat, hblk, hnot⟩ := blk_succ (T := T) (d := d) N (by omega)
    set K := ENNReal.ofReal (Real.exp ((σ0 ^ 2 + σ0 ^ 2 : NNReal) * l ^ 2))
    have hU : ∀ ω, Qs P Z η M A₀ As (N + 1) (H Z ω)
        = Qs P Z η M A₀ As N (mask N (H Z ω))
          + Xi P Z η M A₀ As t k (mask N (H Z ω)) (H Z ω t k) := by
      intro ω
      rw [Qs_mask, Xi_mask η M A₀ As N _ t k hflat.le]
      unfold Qs
      rw [hblk, Finset.sum_insert hnot, add_comm]
    set F : Hist d T × (Fin 2 → V d) → ENNReal := fun p =>
      ENNReal.ofReal (Real.exp (l * Qs P Z η M A₀ As N p.1))
        * ENNReal.ofReal (Real.exp (l * Xi P Z η M A₀ As t k p.1 p.2))
    have hQm := measurable_Qs (P := P) (Z := Z) (T := T) η M A₀ As N
    have hF : Measurable F := by
      refine (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
        ((hQm.comp measurable_fst).const_mul l))).mul
        (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
          ((measurable_Xi η M A₀ As t k).const_mul l)))
    have hHm := measurable_H Z hZ.measurable
    have hUm : Measurable (fun ω => mask N (H Z ω)) := (measurable_mask N).comp hHm
    have hWm : Measurable (fun ω => H Z ω t k) :=
      (measurable_pi_apply k).comp ((measurable_pi_apply t).comp hHm)
    calc ∫⁻ ω, ENNReal.ofReal (Real.exp (l * Qs P Z η M A₀ As (N + 1) (H Z ω))) ∂P
        = ∫⁻ ω, F (mask N (H Z ω), H Z ω t k) ∂P := by
          refine lintegral_congr fun ω => ?_
          simp only [F]
          rw [hU, mul_add, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
      _ = ∫⁻ ω, ∫⁻ ω', F (mask N (H Z ω), H Z ω' t k) ∂P ∂P :=
          freeze hUm hWm (indep_mask hZ N t k hflat) hF
      _ = ∫⁻ ω, ENNReal.ofReal (Real.exp (l * Qs P Z η M A₀ As N (mask N (H Z ω))))
            * ∫⁻ ω', ENNReal.ofReal (Real.exp (l * Xi P Z η M A₀ As t k (mask N (H Z ω))
              (H Z ω' t k))) ∂P ∂P := by
          refine lintegral_congr fun ω => ?_
          simp only [F]
          refine lintegral_const_mul _ ?_
          exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
            (((measurable_Xi η M A₀ As t k).comp (measurable_const.prodMk hWm)).const_mul l))
      _ ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (l * Qs P Z η M A₀ As N (H Z ω))) * K ∂P := by
          refine lintegral_mono fun ω => ?_
          rw [Qs_mask]
          exact mul_le_mul_right (block_mgf hZ η M hM A₀ As t k _ l) _
      _ = (∫⁻ ω, ENNReal.ofReal (Real.exp (l * Qs P Z η M A₀ As N (H Z ω))) ∂P) * K :=
          lintegral_mul_const _ (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
            ((hQm.comp hHm).const_mul l)))
      _ ≤ K ^ N * K := mul_le_mul_left (ih (by omega)) _
      _ = K ^ (N + 1) := (pow_succ _ _).symm

variable (P Z) in
lemma chernoff_Q (hZ : IsSimOracle P f σ0 Z) (η M : ℝ) (hM : 0 ≤ M) (A₀ As : Finset (Fin d))
    (l : ℝ) (hl : 0 < l) (a : ℝ) :
    P {ω | a ≤ Qs P Z η M A₀ As (T * d) (H Z ω)}
      ≤ ENNReal.ofReal (Real.exp ((σ0 ^ 2 + σ0 ^ 2 : NNReal) * l ^ 2 * (T * d) - l * a)) := by
  have hHm := measurable_H Z hZ.measurable
  have hQm := (measurable_Qs (P := P) (Z := Z) (T := T) η M A₀ As (T * d)).comp hHm
  have hfm : Measurable (fun ω => ENNReal.ofReal (Real.exp (l * Qs P Z η M A₀ As (T * d)
      (H Z ω)))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hQm.const_mul l))
  have hmk := mul_meas_ge_le_lintegral₀ (μ := P) hfm.aemeasurable (ENNReal.ofReal (Real.exp (l * a)))
  have hsub : {ω | a ≤ Qs P Z η M A₀ As (T * d) (H Z ω)}
      ⊆ {ω | ENNReal.ofReal (Real.exp (l * a))
          ≤ ENNReal.ofReal (Real.exp (l * Qs P Z η M A₀ As (T * d) (H Z ω)))} := by
    intro ω hω
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hω hl.le))
  have h1 := (mul_le_mul_right (measure_mono (μ := P) hsub) _).trans
    (hmk.trans (mgf_Q P Z hZ η M hM A₀ As l (T * d) le_rfl))
  rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul] at h1
  have e : ENNReal.ofReal (Real.exp (-(l * a))) * ENNReal.ofReal (Real.exp (l * a)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]; simp
  calc P {ω | a ≤ Qs P Z η M A₀ As (T * d) (H Z ω)}
      = ENNReal.ofReal (Real.exp (-(l * a))) * (ENNReal.ofReal (Real.exp (l * a))
          * P {ω | a ≤ Qs P Z η M A₀ As (T * d) (H Z ω)}) := by
        rw [← mul_assoc, e, one_mul]
    _ ≤ ENNReal.ofReal (Real.exp (-(l * a))) * ENNReal.ofReal (Real.exp (((T * d : ℕ) : ℝ)
          * (((σ0 ^ 2 + σ0 ^ 2 : NNReal) : ℝ) * l ^ 2))) := by
        gcongr
    _ = _ := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        congr 2; push_cast; ring

end Mart

end GSSol


open MeasureTheory ProbabilityTheory GradDOvS.Submod

namespace GSSol

section Round

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d T n : ℕ}
  {f : Finset (Fin d) → ℝ} {σ0 : NNReal} {Z : Slot d T n → Ω → V d}

/-- Hoeffding for the sample mean at a fixed point `S`. -/
lemma hoeffding_fixed (hZ : IsSimOracle P f σ0 Z) (i : Fin (d + 1)) (S : Finset (Fin d))
    (r : ℝ) (hr : 0 ≤ r) (hn : 0 < n) :
    P {ω | r < |(1 / (n : ℝ)) * ∑ s : Fin n, Z (Sum.inr (i, s)) ω S - f S|}
      ≤ ENNReal.ofReal (2 * Real.exp (-(n * r ^ 2) / (2 * σ0 ^ 2))) := by
  have hinj : Function.Injective (fun s : Fin n => (Sum.inr (i, s) : Slot d T n)) := by
    intro a b h; simpa using h
  have hind0 := hZ.indep.precomp hinj
  set Y : Fin n → Ω → ℝ := fun s ω => Z (Sum.inr (i, s)) ω S - f S
  have hY : iIndepFun Y P := by
    have := hind0.comp (fun _ v => v S - f S) (fun _ => (measurable_pi_apply S).sub_const _)
    exact this
  have hYn : iIndepFun (fun s ω => -Y s ω) P := by
    have := hY.comp (fun _ x => -x) (fun _ => measurable_neg)
    exact this
  have hsub : ∀ s ∈ (Finset.univ : Finset (Fin n)), HasSubgaussianMGF (Y s) (σ0 ^ 2) P :=
    fun s _ => hZ.subgaussian _ S
  have hsubn : ∀ s ∈ (Finset.univ : Finset (Fin n)),
      HasSubgaussianMGF (fun ω => -Y s ω) (σ0 ^ 2) P :=
    fun s _ => (hZ.subgaussian _ S).neg
  have hnr : 0 ≤ (n : ℝ) * r := by positivity
  have h1 := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hY hsub hnr
  have h2 := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hYn hsubn hnr
  have hsum : ∑ s ∈ (Finset.univ : Finset (Fin n)), (σ0 ^ 2 : NNReal) = n * σ0 ^ 2 := by
    simp
  rw [hsum] at h1 h2
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have he : -((n : ℝ) * r) ^ 2 / (2 * ((n * σ0 ^ 2 : NNReal) : ℝ))
      = -(n * r ^ 2) / (2 * σ0 ^ 2) := by
    push_cast; field_simp
  rw [he] at h1 h2
  have hcover : {ω | r < |(1 / (n : ℝ)) * ∑ s : Fin n, Z (Sum.inr (i, s)) ω S - f S|}
      ⊆ {ω | (n : ℝ) * r ≤ ∑ s ∈ Finset.univ, Y s ω}
        ∪ {ω | (n : ℝ) * r ≤ ∑ s ∈ Finset.univ, -Y s ω} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    have e : (1 / (n : ℝ)) * ∑ s : Fin n, Z (Sum.inr (i, s)) ω S - f S
        = (1 / (n : ℝ)) * ∑ s, Y s ω := by
      simp only [Y, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      field_simp
    rw [e, abs_mul, abs_of_pos (by positivity)] at hω
    have h' : (n : ℝ) * r < |∑ s, Y s ω| := by
      rw [one_div, inv_mul_eq_div, lt_div_iff₀ hnpos] at hω; linarith
    rcases lt_abs.1 h' with h | h
    · left
      simp only [Set.mem_ofPred_eq]
      linarith
    · right
      simp only [Set.mem_ofPred_eq, Finset.sum_neg_distrib]
      linarith
  calc P {ω | r < |(1 / (n : ℝ)) * ∑ s : Fin n, Z (Sum.inr (i, s)) ω S - f S|}
      ≤ P ({ω | (n : ℝ) * r ≤ ∑ s ∈ Finset.univ, Y s ω}
        ∪ {ω | (n : ℝ) * r ≤ ∑ s ∈ Finset.univ, -Y s ω}) := measure_mono hcover
    _ ≤ P {ω | (n : ℝ) * r ≤ ∑ s ∈ Finset.univ, Y s ω}
        + P {ω | (n : ℝ) * r ≤ ∑ s ∈ Finset.univ, -Y s ω} := measure_union_le _ _
    _ = ENNReal.ofReal (P.real {ω | (n : ℝ) * r ≤ ∑ s ∈ Finset.univ, Y s ω})
        + ENNReal.ofReal (P.real {ω | (n : ℝ) * r ≤ ∑ s ∈ Finset.univ, -Y s ω}) := by
        rw [ofReal_measureReal, ofReal_measureReal]
    _ ≤ ENNReal.ofReal (Real.exp (-(n * r ^ 2) / (2 * σ0 ^ 2)))
        + ENNReal.ofReal (Real.exp (-(n * r ^ 2) / (2 * σ0 ^ 2))) := by
        gcongr
    _ = ENNReal.ofReal (2 * Real.exp (-(n * r ^ 2) / (2 * σ0 ^ 2))) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
        congr 1; ring

/-- The rounding block of neighbouring point `i`. -/
def Rblk (Z : Slot d T n → Ω → V d) (i : Fin (d + 1)) (ω : Ω) : Fin n → V d :=
  fun s => Z (Sum.inr (i, s)) ω

lemma indep_round (hZ : IsSimOracle P f σ0 Z) (i : Fin (d + 1)) :
    IndepFun (H Z) (Rblk Z i) P := by
  classical
  let S : Finset (Slot d T n) := Finset.univ.filter (fun s => s.isLeft)
  let R : Finset (Slot d T n) := Finset.univ.filter
    (fun s => Sum.elim (fun _ => False) (fun q : Fin (d + 1) × Fin n => q.1 = i) s)
  have hdisj : Disjoint S R := by
    rw [Finset.disjoint_filter]
    intro s _ h1 h2
    rcases s with q | q
    · simp at h2
    · simp at h1
  have h := hZ.indep.indepFun_finset S R hdisj hZ.measurable
  let φ : (S → V d) → Hist d T := fun r t k b => r ⟨Sum.inl (t, k, b), by simp [S]⟩
  let ψ : (R → V d) → (Fin n → V d) := fun r s => r ⟨Sum.inr (i, s), by simp [R]⟩
  have hφ : Measurable φ := measurable_pi_lambda _ fun t => measurable_pi_lambda _ fun k =>
    measurable_pi_lambda _ fun b => measurable_pi_apply _
  have hψ : Measurable ψ := measurable_pi_lambda _ fun s => measurable_pi_apply _
  have hc := h.comp hφ hψ
  convert hc using 1
  · funext ω t k b; rfl
  · funext ω s; rfl

lemma measurable_Rblk (hZ : IsSimOracle P f σ0 Z) (i : Fin (d + 1)) :
    Measurable (Rblk Z i) :=
  measurable_pi_lambda _ fun s => hZ.measurable _

lemma indicator_comp_eq {α β : Type*} (s : Set β) (k : α → β) (a : α) :
    s.indicator (1 : β → ENNReal) (k a) = (k ⁻¹' s).indicator 1 a := by
  by_cases hb : k a ∈ s
  · rw [Set.indicator_of_mem hb, Set.indicator_of_mem (show a ∈ k ⁻¹' s from hb)]; rfl
  · rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem (show a ∉ k ⁻¹' s from hb)]

/-- The bad rounding event for neighbouring point `i`, as a set of (history, rounding block). -/
def badSet (f : Finset (Fin d) → ℝ) (η M : ℝ) (A₀ : Finset (Fin d)) (r : ℝ)
    (i : Fin (d + 1)) : Set (Hist d T × (Fin n → V d)) :=
  {p | r < |(1 / (n : ℝ)) * ∑ s : Fin n, p.2 s (nbr (canonPerm (avgDet η M A₀ p.1)) i)
      - f (nbr (canonPerm (avgDet η M A₀ p.1)) i)|}

lemma measurableSet_badSet (η M : ℝ) (A₀ : Finset (Fin d)) (r : ℝ) (i : Fin (d + 1)) :
    MeasurableSet (badSet (T := T) (n := n) f η M A₀ r i) := by
  have ha : Measurable (fun p : Hist d T × (Fin n → V d) => avgDet η M A₀ p.1) :=
    (measurable_avgDet η M A₀).comp measurable_fst
  have hF : ∀ σ : Equiv.Perm (Fin d), Measurable (fun p : Hist d T × (Fin n → V d) =>
      |(1 / (n : ℝ)) * ∑ s : Fin n, p.2 s (nbr σ i) - f (nbr σ i)|) := by
    intro σ
    refine ((measurable_const.mul (Finset.measurable_sum _ fun s _ => ?_)).sub_const _).abs
    exact (measurable_pi_apply _).comp ((measurable_pi_apply s).comp measurable_snd)
  have hG := measurable_perm_piecewise (fun p : Hist d T × (Fin n → V d) =>
    canonPerm (avgDet η M A₀ p.1)) (fun σ => measurableSet_canonPerm_comp ha σ) _ hF
  exact measurableSet_lt measurable_const hG

lemma round_bad (hZ : IsSimOracle P f σ0 Z) (η M : ℝ) (A₀ : Finset (Fin d)) (r : ℝ)
    (hr : 0 ≤ r) (hn : 0 < n) (i : Fin (d + 1)) :
    P {ω | (H Z ω, Rblk Z i ω) ∈ badSet (T := T) (n := n) f η M A₀ r i}
      ≤ ENNReal.ofReal (2 * Real.exp (-(n * r ^ 2) / (2 * σ0 ^ 2))) := by
  have hB := measurableSet_badSet (T := T) (n := n) (f := f) η M A₀ r i
  have hHm := measurable_H Z hZ.measurable
  have hRm := measurable_Rblk hZ i
  set F : Hist d T × (Fin n → V d) → ENNReal := (badSet f η M A₀ r i).indicator 1
  have hF : Measurable F := measurable_one.indicator hB
  have e1 : ∀ (h : Hist d T) (g : Ω → Fin n → V d), Measurable g →
      ∫⁻ ω, F (h, g ω) ∂P = P {ω | (h, g ω) ∈ badSet (T := T) (n := n) f η M A₀ r i} := by
    intro h g hg
    have hms : MeasurableSet {ω | (h, g ω) ∈ badSet (T := T) (n := n) f η M A₀ r i} :=
      (measurable_const.prodMk hg) hB
    rw [← lintegral_indicator_one hms]
    refine lintegral_congr fun ω => ?_
    exact indicator_comp_eq (badSet (T := T) (n := n) f η M A₀ r i) (fun ω => (h, g ω)) ω
  have e2 : ∫⁻ ω, F (H Z ω, Rblk Z i ω) ∂P
      = P {ω | (H Z ω, Rblk Z i ω) ∈ badSet (T := T) (n := n) f η M A₀ r i} := by
    have hms : MeasurableSet {ω | (H Z ω, Rblk Z i ω) ∈ badSet (T := T) (n := n) f η M A₀ r i} :=
      (hHm.prodMk hRm) hB
    rw [← lintegral_indicator_one hms]
    refine lintegral_congr fun ω => ?_
    exact indicator_comp_eq (badSet (T := T) (n := n) f η M A₀ r i)
      (fun ω => (H Z ω, Rblk Z i ω)) ω
  rw [← e2, freeze hHm hRm (indep_round hZ i) hF]
  calc ∫⁻ ω, ∫⁻ ω', F (H Z ω, Rblk Z i ω') ∂P ∂P
      = ∫⁻ ω, P {ω' | (H Z ω, Rblk Z i ω') ∈ badSet (T := T) (n := n) f η M A₀ r i} ∂P :=
        lintegral_congr fun ω => e1 _ _ hRm
    _ ≤ ∫⁻ _ω, ENNReal.ofReal (2 * Real.exp (-(n * r ^ 2) / (2 * σ0 ^ 2))) ∂P := by
        refine lintegral_mono fun ω => ?_
        exact hoeffding_fixed (P := P) hZ i (nbr (canonPerm (avgDet η M A₀ (H Z ω))) i) r hr hn
    _ = _ := by simp

end Round

end GSSol


open MeasureTheory ProbabilityTheory GradDOvS.Submod

namespace GSSol

lemma abs_clip_le (M r : ℝ) (hM : 0 ≤ M) : |max (-M) (min M r)| ≤ M := by
  rw [abs_le]; constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

lemma avgDet_mem_box {d T : ℕ} (η M : ℝ) (A₀ : Finset (Fin d)) (u : Hist d T) (hT : 0 < T) :
    avgDet η M A₀ u ∈ box d := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  constructor <;> intro j <;>
    simp only [avgDet, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Pi.zero_apply, Pi.one_apply]
  · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun t _ =>
      (iterDet_mem_box η M A₀ u t).1 j)
  · rw [one_div, inv_mul_le_iff₀ hTr, mul_one]
    calc ∑ t ∈ Finset.range T, iterDet η M A₀ u t j ≤ ∑ _t ∈ Finset.range T, (1 : ℝ) :=
          Finset.sum_le_sum fun t _ => (iterDet_mem_box η M A₀ u t).2 j
      _ = T := by simp

section Path

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d T n : ℕ}
  {f : Finset (Fin d) → ℝ} {Z : Slot d T n → Ω → V d}

lemma per_step (L : ℝ) (hf : Standing L f) (η M : ℝ) (A₀ As : Finset (Fin d)) (β : ℝ)
    (hβ : ∀ (t : Fin T) (σ : Equiv.Perm (Fin d)) (k : Fin d),
      |mB P Z M t σ k - chainGrad f σ (σ k)| ≤ β)
    (u : Hist d T) (t : Fin T) :
    lovasz f (iterDet η M A₀ u t) - f As
      ≤ ∑ j, trunc M (gE (iterDet η M A₀ u t) (u t)) j
            * (iterDet η M A₀ u t j - ind As j)
        + ∑ k, Xi P Z η M A₀ As t k u (u t k) + d * β := by
  set x := iterDet η M A₀ u t
  set σ := canonPerm x
  set G := trunc M (gE x (u t))
  set c : Fin d → ℝ := fun j => x j - ind As j
  set m : Fin d → ℝ := fun j => mB P Z M t σ (σ.symm j)
  set g := chainGrad f σ
  have h1 := subgrad_vertex f hf.submodular x As
  have hsplit : ∑ j, g j * (x j - ind As j)
      = ∑ j, G j * c j + ∑ j, (m j - G j) * c j - ∑ j, (m j - g j) * c j := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [c]; ring
  have hX : ∑ j, (m j - G j) * c j = ∑ k, Xi P Z η M A₀ As t k u (u t k) := by
    rw [← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [m, G, c, Xi, Equiv.symm_apply_apply]
    rw [show trunc M (gE x (u t)) (σ k) = max (-M) (min M (gE x (u t) (σ k))) from rfl,
      gE_apply_perm]
    ring
  have hB : -∑ j, (m j - g j) * c j ≤ d * β := by
    have hc : ∀ j, |c j| ≤ 1 := by
      intro j
      have a1 := (iterDet_mem_box η M A₀ u t).1 j
      have a2 := (iterDet_mem_box η M A₀ u t).2 j
      have a3 := (ind_mem_box As).1 j
      have a4 := (ind_mem_box As).2 j
      simp only [Pi.zero_apply, Pi.one_apply] at a1 a2 a3 a4
      simp only [c]; rw [abs_le]; constructor <;> linarith
    calc -∑ j, (m j - g j) * c j ≤ ∑ j, |(m j - g j) * c j| := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_le_sum fun j _ => neg_le_abs _
      _ ≤ ∑ _j : Fin d, β := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul]
          have hb := hβ t σ (σ.symm j)
          simp only [Equiv.apply_symm_apply] at hb
          have hβ0 : 0 ≤ β := le_trans (abs_nonneg _) hb
          calc |m j - g j| * |c j| ≤ β * 1 :=
                mul_le_mul hb (hc j) (abs_nonneg _) hβ0
            _ = β := mul_one _
      _ = d * β := by simp
  rw [← hX]
  linarith

lemma pathwise (L : ℝ) (hf : Standing L f) (η M : ℝ) (hη : 0 < η) (hM : 0 ≤ M)
    (A₀ As : Finset (Fin d)) (β : ℝ)
    (hβ : ∀ (t : Fin T) (σ : Equiv.Perm (Fin d)) (k : Fin d),
      |mB P Z M t σ k - chainGrad f σ (σ k)| ≤ β)
    (hT : 0 < T) (u : Hist d T) :
    lovasz f (avgDet η M A₀ u) - f As
      ≤ d / (2 * η * T) + η * d * M ^ 2 / 2 + Qs P Z η M A₀ As (T * d) u / T + d * β := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  set x : ℕ → Fin d → ℝ := fun t => iterDet η M A₀ u t
  set G : ℕ → Fin d → ℝ := fun t =>
    if h : t < T then trunc M (gE (x t) (u ⟨t, h⟩)) else 0
  have hstep : ∀ t < T, x (t + 1) = proj (x t - η • G t) := by
    intro t ht
    simp only [x, G, ht, dif_pos]
    exact iterDet_succ η M A₀ u t ht
  have hG : ∀ t < T, ∀ j, |G t j| ≤ M := by
    intro t ht j
    simp only [G, ht, dif_pos]
    exact abs_clip_le M _ hM
  have hR := regret T x G (ind As) η M hη (iterDet_mem_box η M A₀ u 0) (ind_mem_box As)
    hstep hG
  -- sum of the per-step inequalities
  have hsum : ∑ t : Fin T, (lovasz f (x t) - f As)
      ≤ (d / (2 * η) + η * T * d * M ^ 2 / 2) + Qs P Z η M A₀ As (T * d) u + T * (d * β) := by
    have hps := Finset.sum_le_sum (s := Finset.univ) fun t (_ : t ∈ Finset.univ) =>
      per_step (P := P) (Z := Z) L hf η M A₀ As β hβ u t
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hps
    have e1 : ∑ t : Fin T, ∑ j, trunc M (gE (iterDet η M A₀ u t) (u t)) j
        * (iterDet η M A₀ u t j - ind As j)
        = ∑ t ∈ Finset.range T, ∑ j, G t j * (x t j - ind As j) := by
      rw [← Fin.sum_univ_eq_sum_range (fun t => ∑ j, G t j * (x t j - ind As j))]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [G, x, t.2, dif_pos, Fin.eta]
    have e2 : ∑ t : Fin T, ∑ k, Xi P Z η M A₀ As t k u (u t k)
        = Qs P Z η M A₀ As (T * d) u := by
      unfold Qs
      rw [blk_full, ← Finset.univ_product_univ, Finset.sum_product]
    have e3 : ∑ _t : Fin T, (d : ℝ) * β = T * (d * β) := by simp
    rw [e1, e2, e3] at hps
    linarith
  -- convexity
  set xb := avgDet η M A₀ u
  have hconv : lovasz f xb ≤ (1 / (T : ℝ)) * ∑ t : Fin T, lovasz f (x t) := by
    set α := canonPerm xb
    have hlb : ∀ t : Fin T, f ∅ + ∑ j, chainGrad f α j * x t j ≤ lovasz f (x t) :=
      fun t => lower_bound f hf.submodular (x t) (iterDet_mem_box η M A₀ u t) α
    have hxb : ∀ j, xb j = (1 / (T : ℝ)) * ∑ t : Fin T, x t j := by
      intro j
      simp only [xb, avgDet, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      rw [Fin.sum_univ_eq_sum_range (fun t => iterDet η M A₀ u t j)]
    have hl : lovasz f xb = f ∅ + ∑ j, chainGrad f α j * xb j := by
      unfold lovasz; rw [lovaszWith_eq]
    rw [hl]
    have := Finset.sum_le_sum (s := Finset.univ) fun t (_ : t ∈ Finset.univ) => hlb t
    rw [Finset.sum_add_distrib, Finset.sum_comm] at this
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    have e : ∑ j, chainGrad f α j * xb j
        = (1 / (T : ℝ)) * ∑ j, ∑ t : Fin T, chainGrad f α j * x t j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hxb j, ← Finset.mul_sum]; ring
    rw [e]
    rw [← sub_nonneg] at this ⊢
    have h2 : (1 / (T : ℝ)) * ∑ t : Fin T, lovasz f (x t) - (f ∅ + 1 / (T : ℝ)
        * ∑ j, ∑ t : Fin T, chainGrad f α j * x t j)
        = (1 / (T : ℝ)) * (∑ t : Fin T, lovasz f (x t)
          - ((T : ℝ) * f ∅ + ∑ j, ∑ t : Fin T, chainGrad f α j * x t j)) := by
      field_simp
    rw [h2]
    exact mul_nonneg (by positivity) this
  have hsum' : ∑ t : Fin T, lovasz f (x t) = ∑ t : Fin T, (lovasz f (x t) - f As) + T * f As := by
    rw [Finset.sum_sub_distrib]; simp
  rw [hsum'] at hconv
  have : lovasz f xb - f As ≤ (1 / (T : ℝ)) *
      ((d / (2 * η) + η * T * d * M ^ 2 / 2) + Qs P Z η M A₀ As (T * d) u + T * (d * β)) := by
    have h3 := mul_le_mul_of_nonneg_left hsum (show (0 : ℝ) ≤ 1 / T by positivity)
    have h4 : (1 / (T : ℝ)) * (∑ t : Fin T, (lovasz f (x t) - f As) + T * f As)
        = (1 / (T : ℝ)) * ∑ t : Fin T, (lovasz f (x t) - f As) + f As := by
      field_simp
    linarith
  calc lovasz f xb - f As ≤ _ := this
    _ = _ := by field_simp

end Path

end GSSol


open MeasureTheory ProbabilityTheory GradDOvS.Submod

namespace GSSol

lemma bias_numeric (s ε dd TT a : ℝ) (hs : 0 < s) (hε : 0 < ε) (hd : 1 ≤ dd) (hT : 4 ≤ TT)
    (hℓ : 1 ≤ Real.log (4 * s * dd * TT / ε))
    (ha : 2 * s * Real.sqrt (Real.log (4 * s * dd * TT / ε)) ≤ a) :
    dd * ((2 * (s ^ 2 + s ^ 2)) / a * Real.exp (-a ^ 2 / (2 * (s ^ 2 + s ^ 2)))) ≤ ε / 8 := by
  set ℓ := Real.log (4 * s * dd * TT / ε)
  have hsq : 1 ≤ Real.sqrt ℓ := by
    have := Real.sqrt_le_sqrt hℓ; rwa [Real.sqrt_one] at this
  have ha2 : 2 * s ≤ a := by nlinarith
  have hapos : 0 < a := by linarith
  have hsqℓ : Real.sqrt ℓ ^ 2 = ℓ := Real.sq_sqrt (by linarith)
  have ha_sq : 4 * s ^ 2 * ℓ ≤ a ^ 2 := by
    have h0 : 0 ≤ 2 * s * Real.sqrt ℓ := by positivity
    have := mul_self_le_mul_self h0 ha
    nlinarith [hsqℓ]
  have hpos : 0 < 4 * s * dd * TT / ε := by
    apply div_pos _ hε; have : (0 : ℝ) < TT := by linarith
    have : (0 : ℝ) < dd := by linarith
    positivity
  have hexp : Real.exp (-a ^ 2 / (2 * (s ^ 2 + s ^ 2))) ≤ Real.exp (-ℓ) := by
    apply Real.exp_le_exp.2
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hexpℓ : Real.exp (-ℓ) = ε / (4 * s * dd * TT) := by
    rw [Real.exp_neg, Real.exp_log hpos]; field_simp
  have hfrac : (2 * (s ^ 2 + s ^ 2)) / a ≤ 2 * s := by
    rw [div_le_iff₀ hapos]; nlinarith
  have hdd : 0 < dd := by linarith
  have hTT : 0 < TT := by linarith
  calc dd * ((2 * (s ^ 2 + s ^ 2)) / a * Real.exp (-a ^ 2 / (2 * (s ^ 2 + s ^ 2))))
      ≤ dd * (2 * s * (ε / (4 * s * dd * TT))) := by
        gcongr
        rw [← hexpℓ]; exact hexp
    _ = ε / (2 * TT) := by field_simp; ring
    _ ≤ ε / 8 := by
        apply div_le_div_of_nonneg_left hε.le (by norm_num); linarith

lemma chernoff_numeric (s ε dd TT δ : ℝ) (hs : 0 < s) (hε : 0 < ε) (hd : 1 ≤ dd) (hT : 0 < TT)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hT₁ : 3584 * dd * s ^ 2 / ε ^ 2 * Real.log (2 / δ) ≤ TT) :
    Real.exp ((s ^ 2 + s ^ 2) * (ε / (16 * s ^ 2 * dd)) ^ 2 * (TT * dd)
      - ε / (16 * s ^ 2 * dd) * (TT * ε / 4)) ≤ δ / 2 := by
  have hdd : 0 < dd := by linarith
  have e : (s ^ 2 + s ^ 2) * (ε / (16 * s ^ 2 * dd)) ^ 2 * (TT * dd)
      - ε / (16 * s ^ 2 * dd) * (TT * ε / 4) = -(TT * ε ^ 2 / (128 * s ^ 2 * dd)) := by
    field_simp; ring
  rw [e]
  have hl : 0 < Real.log (2 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ0]; linarith)
  have h1 : Real.log (2 / δ) ≤ TT * ε ^ 2 / (128 * s ^ 2 * dd) := by
    rw [le_div_iff₀ (by positivity)]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at hT₁
    nlinarith
  calc Real.exp (-(TT * ε ^ 2 / (128 * s ^ 2 * dd))) ≤ Real.exp (-Real.log (2 / δ)) :=
        Real.exp_le_exp.2 (by linarith)
    _ = δ / 2 := by
        rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp

lemma round_numeric (s ε dd δ nn : ℝ) (hs : 0 < s) (hε : 0 < ε) (hd : 1 ≤ dd)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hn : 32 * s ^ 2 / ε ^ 2 * Real.log (8 * dd / δ) ≤ nn) :
    2 * Real.exp (-(nn * (ε / 4) ^ 2) / (2 * s ^ 2)) ≤ δ / (4 * dd) := by
  have hdd : 0 < dd := by linarith
  have hpos : 0 < 8 * dd / δ := by positivity
  have h1 : Real.log (8 * dd / δ) ≤ nn * ε ^ 2 / (32 * s ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at hn
    nlinarith
  have e : -(nn * (ε / 4) ^ 2) / (2 * s ^ 2) = -(nn * ε ^ 2 / (32 * s ^ 2)) := by
    field_simp; ring
  rw [e]
  calc 2 * Real.exp (-(nn * ε ^ 2 / (32 * s ^ 2))) ≤ 2 * Real.exp (-Real.log (8 * dd / δ)) := by
        gcongr
    _ = δ / (4 * dd) := by
        rw [Real.exp_neg, Real.exp_log hpos]; field_simp; ring

end GSSol

open GSSol in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {d T n : ℕ} (P : Measure Ω)
    [IsProbabilityMeasure P] (f : Finset (Fin d) → ℝ) (L : ℝ) (σ : NNReal)
    (Z : Slot d T n → Ω → Finset (Fin d) → ℝ) (hZ : IsSimOracle P f σ Z)
    (hf : Standing L f) (hσ : 0 < σ) (ε δ M : ℝ) (hε : 0 < ε) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hT₁ : 3584 * d * (σ : ℝ) ^ 2 / ε ^ 2 * Real.log (2 / δ) ≤ T)
    (hT₂ : 2 * ε / (σ : ℝ) ≤ T) (hT₃ : 4 ≤ T)
    (hM : L + 2 * (σ : ℝ) * Real.sqrt (Real.log (4 * σ * d * T / ε)) ≤ M)
    (hMT : 64 * (d : ℝ) ^ 2 * M ^ 2 ≤ ε ^ 2 * T)
    (hn : 32 * (σ : ℝ) ^ 2 / ε ^ 2 * Real.log (8 * d / δ) ≤ n)
    (A₀ : Finset (Fin d)) :
    P (roundFail f ε Z (ssgdAvg Z (1 / (M * Real.sqrt T)) M A₀)) ≤ ENNReal.ofReal δ := by
  classical
  -- basic facts
  have hd1 : 1 ≤ d := hf.one_le_d
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hdpos : (0 : ℝ) < d := by linarith
  have hL0 : 0 ≤ L := le_trans (abs_nonneg _) (hf.lipschitz ∅ ∅)
  have hT4 : (4 : ℝ) ≤ T := by exact_mod_cast hT₃
  have hTpos : 0 < T := by omega
  have hTr : (0 : ℝ) < T := by linarith
  have hs : (0 : ℝ) < σ := hσ
  have hσT : 2 * ε ≤ σ * T := by
    rw [div_le_iff₀ hs] at hT₂; linarith
  have hℓ : 1 ≤ Real.log (4 * σ * d * T / ε) := by
    have h8 : 8 ≤ 4 * (σ : ℝ) * d * T / ε := by
      rw [le_div_iff₀ hε]; nlinarith
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hsqrt : 1 ≤ Real.sqrt (Real.log (4 * σ * d * T / ε)) := by
    have := Real.sqrt_le_sqrt hℓ; rwa [Real.sqrt_one] at this
  have hML : 2 * (σ : ℝ) ≤ M - L := by nlinarith
  have hMpos : 0 < M := by linarith
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.2 hTr
  set η := 1 / (M * Real.sqrt T) with hη_def
  have hη : 0 < η := by positivity
  obtain ⟨As, -, hAs⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty f
  have hminf : minf f = f As := hAs
  set β := (2 * ((σ ^ 2 + σ ^ 2 : NNReal) : ℝ) / (M - L))
      * Real.exp (-(M - L) ^ 2 / (2 * ((σ ^ 2 + σ ^ 2 : NNReal) : ℝ))) with hβ_def
  have hβ : ∀ (t : Fin T) (σ' : Equiv.Perm (Fin d)) (k : Fin d),
      |mB P Z M t σ' k - chainGrad f σ' (σ' k)| ≤ β :=
    fun t σ' k => mB_bias hZ hf hσ (by linarith) t σ' k
  have hdβ : (d : ℝ) * β ≤ ε / 8 := by
    have := bias_numeric σ ε d T (M - L) hs hε hdr hT4 hℓ (by linarith)
    simp only [hβ_def]; push_cast; exact this
  have hdm : (d : ℝ) / (2 * η * T) + η * d * M ^ 2 / 2 ≤ ε / 8 := by
    have hsq : Real.sqrt T ^ 2 = T := Real.sq_sqrt hTr.le
    have h8 : 8 * d * M ≤ ε * Real.sqrt T := by
      have h1 := Real.sqrt_le_sqrt hMT
      rw [show 64 * (d : ℝ) ^ 2 * M ^ 2 = (8 * d * M) ^ 2 by ring,
        Real.sqrt_sq (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq hε.le] at h1
      exact h1
    have e : (d : ℝ) / (2 * η * T) + η * d * M ^ 2 / 2 = d * M / Real.sqrt T := by
      rw [hη_def]; field_simp; rw [hsq]; ring
    rw [e, div_le_iff₀ hsT]
    linarith
  -- the deterministic inclusion
  set Q : Ω → ℝ := fun ω => Qs P Z η M A₀ As (T * d) (H Z ω)
  have hsub : roundFail f ε Z (ssgdAvg Z η M A₀)
      ⊆ {ω | T * ε / 4 ≤ Q ω}
        ∪ ⋃ i : Fin (d + 1), {ω | (H Z ω, Rblk Z i ω) ∈ badSet f η M A₀ (ε / 4) i} := by
    intro ω hω
    obtain ⟨i, hmin, hbad⟩ := hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists, Set.mem_ofPred_eq,
      not_le] at hcon
    obtain ⟨hQ, hround⟩ := hcon
    have hpath := pathwise (P := P) (Z := Z) L hf η M hη hMpos.le A₀ As β hβ hTpos (H Z ω)
    set xb := avgDet η M A₀ (H Z ω)
    obtain ⟨i₀, hi₀⟩ := exists_nbr_le f xb (avgDet_mem_box η M A₀ (H Z ω) hTpos)
    simp only [roundMean, roundPt, ssgdAvg_eq] at hmin hbad
    have hr : ∀ j, |(1 / (n : ℝ)) * ∑ s : Fin n,
        Z (Sum.inr (j, s)) ω (nbr (canonPerm xb) j) - f (nbr (canonPerm xb) j)| ≤ ε / 4 := by
      intro j
      have := hround j
      simp only [badSet, Rblk, Set.mem_ofPred_eq, not_lt] at this
      exact this
    have hQT : Q ω / T < ε / 4 := by
      rw [div_lt_iff₀ hTr]; linarith
    have r1 := abs_le.1 (hr i)
    have r2 := abs_le.1 (hr i₀)
    have hm := hmin i₀
    rw [hminf] at hbad
    simp only [Q] at hQT
    linarith
  -- probabilities
  have hA : P {ω | T * ε / 4 ≤ Q ω} ≤ ENNReal.ofReal (δ / 2) := by
    have hl : 0 < ε / (16 * (σ : ℝ) ^ 2 * d) := by positivity
    have := chernoff_Q P Z hZ η M hMpos.le A₀ As (ε / (16 * (σ : ℝ) ^ 2 * d)) hl (T * ε / 4)
    refine this.trans (ENNReal.ofReal_le_ofReal ?_)
    have h := chernoff_numeric σ ε d T δ hs hε hdr hTr hδ0 hδ1 hT₁
    push_cast
    exact h
  have hnpos : 0 < n := by
    have h1 : 0 < Real.log (8 * d / δ) := Real.log_pos (by
      rw [lt_div_iff₀ hδ0]; nlinarith)
    have : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hn
    exact_mod_cast this
  have hB : P (⋃ i : Fin (d + 1), {ω | (H Z ω, Rblk Z i ω) ∈ badSet f η M A₀ (ε / 4) i})
      ≤ ENNReal.ofReal (δ / 2) := by
    refine (measure_iUnion_fintype_le P _).trans ?_
    have hone : ∀ i : Fin (d + 1),
        P {ω | (H Z ω, Rblk Z i ω) ∈ badSet f η M A₀ (ε / 4) i}
          ≤ ENNReal.ofReal (δ / (4 * d)) := by
      intro i
      refine (round_bad hZ η M A₀ (ε / 4) (by positivity) hnpos i).trans
        (ENNReal.ofReal_le_ofReal ?_)
      exact round_numeric σ ε d δ n hs hε hdr hδ0 hδ1 hn
    calc ∑ i : Fin (d + 1), P {ω | (H Z ω, Rblk Z i ω) ∈ badSet f η M A₀ (ε / 4) i}
        ≤ ∑ _i : Fin (d + 1), ENNReal.ofReal (δ / (4 * d)) := Finset.sum_le_sum fun i _ => hone i
      _ = ENNReal.ofReal ((d + 1) * (δ / (4 * d))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ENNReal.ofReal_mul (by positivity)]
          norm_cast
      _ ≤ ENNReal.ofReal (δ / 2) := by
          apply ENNReal.ofReal_le_ofReal
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  calc P (roundFail f ε Z (ssgdAvg Z η M A₀))
      ≤ P ({ω | T * ε / 4 ≤ Q ω}
        ∪ ⋃ i : Fin (d + 1), {ω | (H Z ω, Rblk Z i ω) ∈ badSet f η M A₀ (ε / 4) i}) :=
        measure_mono hsub
    _ ≤ P {ω | T * ε / 4 ≤ Q ω}
        + P (⋃ i : Fin (d + 1), {ω | (H Z ω, Rblk Z i ω) ∈ badSet f η M A₀ (ε / 4) i}) :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) := add_le_add hA hB
    _ = ENNReal.ofReal δ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

