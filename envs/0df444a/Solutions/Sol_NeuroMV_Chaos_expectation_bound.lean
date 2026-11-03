-- Prove2me | solution 1 for NeuroMV.Chaos.expectation_bound
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-11-02T06:39:09.260096+00:00
-- url     : https://prove2.me/submissions/a7c4ba7f-8671-4657-8941-adbf55089c1d

import Mathlib
import Definitions.Def_NeuroMV_Chaos_Network

/-!
# Poisson point process, step 1: one cell.

A cell is `ℕ × (ℕ → Y)` with law `Po(lam) ⊗ p^ℕ`: a Poisson number `K` of iid `p`-points.
`cellSum f ω = Σ_{k < K} f (X_k)`.  Main result `cell_cf`:
`E exp(i · cellSum f) = exp(lam · (∫ exp(i f) dp - 1))`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false


namespace PPP

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal

variable {Y : Type*} [MeasurableSpace Y]

/-- iid product: `∫ Π_{k<n} g(x k) d p^ℕ = (∫ g dp)^n`. -/
lemma iid_prod_integral (p : Measure Y) [IsProbabilityMeasure p] (g : Y → ℂ)
    (hg : Measurable g) (n : ℕ) :
    ∫ x, ∏ k ∈ Finset.range n, g (x k) ∂(Measure.infinitePi (fun _ : ℕ => p)) =
      (∫ y, g y ∂p) ^ n := by
  have hind0 : iIndepFun (fun (k : ℕ) (x : ℕ → Y) => x k)
      (Measure.infinitePi (fun _ : ℕ => p)) :=
    iIndepFun_infinitePi (P := fun _ : ℕ => p) (X := fun _ y => y) (fun _ => measurable_id)
  have hind : iIndepFun (fun (k : Fin n) (x : ℕ → Y) => x k)
      (Measure.infinitePi (fun _ : ℕ => p)) :=
    hind0.precomp (g := fun k : Fin n => (k : ℕ)) Fin.val_injective
  have h1 : (fun x : ℕ → Y => ∏ k ∈ Finset.range n, g (x k)) =
      fun x => ∏ k : Fin n, g (x k) := by
    funext x; exact (Fin.prod_univ_eq_prod_range (fun k => g (x k)) n).symm
  rw [h1, hind.integral_fun_prod_comp (f := fun _ => g)
    (fun k => (measurable_pi_apply (k : ℕ)).aemeasurable)
    (fun _ => hg.aestronglyMeasurable)]
  have h2 : ∀ k : Fin n, ∫ x, g (x (k : ℕ)) ∂(Measure.infinitePi (fun _ : ℕ => p)) =
      ∫ y, g y ∂p := by
    intro k
    have hm := Measure.infinitePi_map_eval (μ := fun _ : ℕ => p) (k : ℕ)
    rw [← integral_map (measurable_pi_apply (k : ℕ)).aemeasurable hg.aestronglyMeasurable, hm]
  simp only [h2, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The law of one cell. -/
noncomputable def cellMeasure (lam : ℝ≥0) (p : Measure Y) [IsProbabilityMeasure p] :
    Measure (ℕ × (ℕ → Y)) :=
  (poissonMeasure lam).prod (Measure.infinitePi (fun _ : ℕ => p))

theorem cellMeasure_prob (lam : ℝ≥0) (p : Measure Y) [IsProbabilityMeasure p] :
    IsProbabilityMeasure (cellMeasure lam p) := by
  unfold cellMeasure; infer_instance
attribute [local instance] cellMeasure_prob

/-- `Σ_{k < K} f (X_k)`. -/
def cellSum (f : Y → ℝ) (ω : ℕ × (ℕ → Y)) : ℝ :=
  ∑ k ∈ Finset.range ω.1, f (ω.2 k)

lemma measurable_cellSum (f : Y → ℝ) (hf : Measurable f) :
    Measurable (cellSum f) := by
  apply measurable_from_prod_countable_right
  intro n
  simp only [cellSum]
  exact Finset.measurable_sum _ (fun k _ => hf.comp (measurable_pi_apply k))

/-- Poisson generating sum: `Σ e^{-lam} lam^n/n! φ^n = exp(lam (φ - 1))`. -/
lemma poisson_pow_integral (lam : ℝ≥0) (φ : ℂ) (hφ : ‖φ‖ ≤ 1) :
    ∫ n, φ ^ n ∂(poissonMeasure lam) = cexp (lam * (φ - 1)) := by
  have hint : Integrable (fun n : ℕ => φ ^ n) (poissonMeasure lam) := by
    refine Integrable.of_bound (Measurable.of_discrete).aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall (fun n => by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hφ)
  rw [integral_poissonMeasure' hint]
  calc ∑' n, (Real.exp (-(lam : ℝ)) * (lam : ℝ) ^ n / (n.factorial : ℝ)) • φ ^ n
      = ∑' n, (Real.exp (-(lam : ℝ)) : ℂ) * ((lam * φ) ^ n / (n.factorial : ℂ)) := by
        congr with n
        rw [Complex.real_smul]
        push_cast
        rw [mul_pow]
        ring
    _ = (Real.exp (-(lam : ℝ)) : ℂ) * ∑' n, ((lam * φ) ^ n / (n.factorial : ℂ)) := tsum_mul_left
    _ = (Real.exp (-(lam : ℝ)) : ℂ) * cexp (lam * φ) := by
        rw [(NormedSpace.expSeries_div_hasSum_exp ((lam : ℂ) * φ)).tsum_eq, exp_eq_exp_ℂ]
    _ = cexp (lam * (φ - 1)) := by
        rw [ofReal_exp, ← Complex.exp_add]
        push_cast
        ring_nf

/-- **Cell characteristic functional.** -/
lemma cell_cf (lam : ℝ≥0) (p : Measure Y) [IsProbabilityMeasure p] (f : Y → ℝ)
    (hf : Measurable f) :
    ∫ ω, cexp (cellSum f ω * I) ∂(cellMeasure lam p) =
      cexp (lam * ((∫ y, cexp (f y * I) ∂p) - 1)) := by
  set g : Y → ℂ := fun y => cexp (f y * I) with hg_def
  have hg : Measurable g := by
    simp only [hg_def]
    exact Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp hf).mul_const I)
  have hprod : ∀ ω : ℕ × (ℕ → Y), cexp (cellSum f ω * I) =
      ∏ k ∈ Finset.range ω.1, g (ω.2 k) := by
    intro ω
    simp only [cellSum, hg_def]
    push_cast
    rw [Finset.sum_mul, Complex.exp_sum]
  simp_rw [hprod]
  have hmeasF : Measurable (fun ω : ℕ × (ℕ → Y) => ∏ k ∈ Finset.range ω.1, g (ω.2 k)) := by
    apply measurable_from_prod_countable_right
    intro n
    show Measurable fun y : ℕ → Y => ∏ k ∈ Finset.range n, g (y k)
    exact Finset.measurable_prod (Finset.range n) (fun k _ => hg.comp (measurable_pi_apply k))
  have hgn : ∀ y, ‖g y‖ = 1 := fun y => by
    simp only [hg_def]; exact Complex.norm_exp_ofReal_mul_I (f y)
  have hint : Integrable (fun ω : ℕ × (ℕ → Y) => ∏ k ∈ Finset.range ω.1, g (ω.2 k))
      (cellMeasure lam p) := by
    refine Integrable.of_bound hmeasF.aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall (fun ω => by
      rw [norm_prod]; simp [hgn])
  unfold cellMeasure at hint ⊢
  rw [integral_prod _ hint]
  simp only [iid_prod_integral p g hg]
  apply poisson_pow_integral
  calc ‖∫ y, g y ∂p‖ ≤ ∫ y, ‖g y‖ ∂p := norm_integral_le_integral_norm _
    _ = 1 := by simp [hgn]

/-! ### Splitting a cell: restrictions to `D` and `Dᶜ` are independent -/

lemma cellSum_add (f g : Y → ℝ) (ω : ℕ × (ℕ → Y)) :
    cellSum (f + g) ω = cellSum f ω + cellSum g ω := by
  simp [cellSum, Finset.sum_add_distrib]

lemma integrable_cexp_mul_I (p : Measure Y) [IsFiniteMeasure p] (f : Y → ℝ)
    (hf : Measurable f) : Integrable (fun y => cexp (f y * I)) p := by
  refine Integrable.of_bound ?_ 1 (Filter.Eventually.of_forall (fun y => ?_))
  · exact (Complex.measurable_exp.comp
      ((Complex.measurable_ofReal.comp hf).mul_const I)).aestronglyMeasurable
  · exact le_of_eq (Complex.norm_exp_ofReal_mul_I (f y))

lemma integral_exp_split (p : Measure Y) [IsProbabilityMeasure p] (D : Set Y) (a b : Y → ℝ)
    (ha : Measurable a) (hb : Measurable b) (ha0 : ∀ y, y ∉ D → a y = 0)
    (hb0 : ∀ y, y ∈ D → b y = 0) :
    (∫ y, cexp (((a + b) y : ℝ) * I) ∂p) - 1 =
      ((∫ y, cexp (a y * I) ∂p) - 1) + ((∫ y, cexp (b y * I) ∂p) - 1) := by
  have hpt : ∀ y, cexp (((a + b) y : ℝ) * I) = cexp (a y * I) + cexp (b y * I) - 1 := by
    intro y
    by_cases hy : y ∈ D
    · simp [Pi.add_apply, hb0 y hy]
    · simp [Pi.add_apply, ha0 y hy]
  simp_rw [hpt]
  have hia := integrable_cexp_mul_I p a ha
  have hib := integrable_cexp_mul_I p b hb
  have hiab : Integrable (fun y => cexp (a y * I) + cexp (b y * I)) p := hia.add hib
  rw [integral_sub hiab (integrable_const (1 : ℂ)), integral_add hia hib, integral_const]
  simp only [probReal_univ, one_smul]
  ring

/-- Two vector statistics of a cell built from functions supported in `D` and in `Dᶜ` are
independent (Poisson splitting / colouring, characteristic-function proof). -/
lemma cell_indepFun {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    (lam : ℝ≥0) (p : Measure Y) [IsProbabilityMeasure p] (D : Set Y)
    (X : ℕ × (ℕ → Y) → E) (Z : ℕ × (ℕ → Y) → F) (hX : Measurable X) (hZ : Measurable Z)
    (a : E → Y → ℝ) (b : F → Y → ℝ) (ha : ∀ t, Measurable (a t)) (hb : ∀ t, Measurable (b t))
    (hXa : ∀ ω t, inner ℝ (X ω) t = cellSum (a t) ω)
    (hZb : ∀ ω t, inner ℝ (Z ω) t = cellSum (b t) ω)
    (ha0 : ∀ t y, y ∉ D → a t y = 0) (hb0 : ∀ t y, y ∈ D → b t y = 0) :
    IndepFun X Z (cellMeasure lam p) := by
  rw [indepFun_iff_charFun_prod hX.aemeasurable hZ.aemeasurable]
  intro t
  have hm : Measurable (fun ω => WithLp.toLp 2 (X ω, Z ω)) := by fun_prop
  rw [charFun_apply, charFun_apply, charFun_apply,
    integral_map hm.aemeasurable (by fun_prop), integral_map hX.aemeasurable (by fun_prop),
    integral_map hZ.aemeasurable (by fun_prop)]
  simp only [WithLp.prod_inner_apply, hXa, hZb]
  have e1 : ∀ ω, ((cellSum (a (WithLp.ofLp t).1) ω + cellSum (b (WithLp.ofLp t).2) ω : ℝ) : ℂ)
      = ((cellSum (a (WithLp.ofLp t).1 + b (WithLp.ofLp t).2) ω : ℝ) : ℂ) := by
    intro ω; rw [cellSum_add]
  simp_rw [e1]
  rw [cell_cf lam p _ ((ha _).add (hb _)), cell_cf lam p _ (ha _), cell_cf lam p _ (hb _),
    integral_exp_split p D _ _ (ha _) (hb _) (ha0 _) (hb0 _), mul_add, Complex.exp_add]

/-! ### From finite vector statistics to σ-algebras -/

section VecIndep

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {ι ι' : Type*}

/-- the vector of finitely many real statistics. -/
noncomputable def vecOf (f : ι → Ω → ℝ) (F : Finset ι) (ω : Ω) : EuclideanSpace ℝ F :=
  WithLp.toLp 2 (fun i : F => f i ω)

lemma comap_vecOf_mono (f : ι → Ω → ℝ) {F F' : Finset ι} (h : F ⊆ F') :
    MeasurableSpace.comap (vecOf f F) inferInstance ≤
      MeasurableSpace.comap (vecOf f F') inferInstance := by
  classical
  let g : EuclideanSpace ℝ F' → EuclideanSpace ℝ F :=
    fun x => WithLp.toLp 2 (fun i : F => (WithLp.ofLp x) ⟨i.1, h i.2⟩)
  have hg : Measurable g := by fun_prop
  have hcomp : vecOf f F = g ∘ vecOf f F' := by
    funext ω; rfl
  rw [hcomp]
  exact (hg.comp (comap_measurable (vecOf f F'))).comap_le

lemma comap_le_comap_vecOf (f : ι → Ω → ℝ) (i : ι) :
    MeasurableSpace.comap (f i) inferInstance ≤
      MeasurableSpace.comap (vecOf f {i}) inferInstance := by
  classical
  let g : EuclideanSpace ℝ ({i} : Finset ι) → ℝ :=
    fun x => (WithLp.ofLp x) ⟨i, Finset.mem_singleton_self i⟩
  have hg : Measurable g := by fun_prop
  have hcomp : f i = g ∘ vecOf f {i} := by
    funext ω; rfl
  rw [hcomp]
  exact (hg.comp (comap_measurable (vecOf f {i}))).comap_le

/-- If all finite vector statistics are independent, the generated σ-algebras are. -/
lemma indep_iSup_of_vec (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : ι → Ω → ℝ) (g : ι' → Ω → ℝ) (hf : ∀ i, Measurable (f i)) (hg : ∀ j, Measurable (g j))
    (h : ∀ (F : Finset ι) (G : Finset ι'), IndepFun (vecOf f F) (vecOf g G) μ) :
    Indep (⨆ i, MeasurableSpace.comap (f i) inferInstance)
      (⨆ j, MeasurableSpace.comap (g j) inferInstance) μ := by
  classical
  have hvf : ∀ F : Finset ι, Measurable (vecOf f F) := fun F => by
    unfold vecOf; fun_prop
  have hvg : ∀ G : Finset ι', Measurable (vecOf g G) := fun G => by
    unfold vecOf; fun_prop
  have hdf : Directed (· ≤ ·) (fun F : Finset ι =>
      MeasurableSpace.comap (vecOf f F) (inferInstance : MeasurableSpace (EuclideanSpace ℝ F))) :=
    Monotone.directed_le (fun F F' hFF' => comap_vecOf_mono f hFF')
  have hdg : Directed (· ≤ ·) (fun G : Finset ι' =>
      MeasurableSpace.comap (vecOf g G) (inferInstance : MeasurableSpace (EuclideanSpace ℝ G))) :=
    Monotone.directed_le (fun G G' hGG' => comap_vecOf_mono g hGG')
  have h1 : ∀ G : Finset ι', Indep (⨆ F : Finset ι, MeasurableSpace.comap (vecOf f F) inferInstance)
      (MeasurableSpace.comap (vecOf g G) inferInstance) μ := by
    intro G
    refine indep_iSup_of_directed_le (fun F => ?_) (fun F => (hvf F).comap_le)
      (hvg G).comap_le hdf
    exact (IndepFun_iff_Indep _ _ _).1 (h F G)
  have h2 : Indep (⨆ G : Finset ι', MeasurableSpace.comap (vecOf g G) inferInstance)
      (⨆ F : Finset ι, MeasurableSpace.comap (vecOf f F) inferInstance) μ :=
    indep_iSup_of_directed_le (fun G => (h1 G).symm) (fun G => (hvg G).comap_le)
      (iSup_le fun F => (hvf F).comap_le) hdg
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left h2.symm ?_) ?_
  · exact iSup_le fun i => (comap_le_comap_vecOf f i).trans (le_iSup (fun F : Finset ι =>
      MeasurableSpace.comap (vecOf f F) (inferInstance : MeasurableSpace (EuclideanSpace ℝ F))) {i})
  · exact iSup_le fun j => (comap_le_comap_vecOf g j).trans (le_iSup (fun G : Finset ι' =>
      MeasurableSpace.comap (vecOf g G) (inferInstance : MeasurableSpace (EuclideanSpace ℝ G))) {j})

end VecIndep

/-! ### Cell counts and the splitting theorem -/

/-- number of cell points in `A`, as a real. -/
noncomputable def cellCnt (A : Set Y) (ω : ℕ × (ℕ → Y)) : ℝ :=
  cellSum (A.indicator 1) ω

lemma measurable_cellCnt {A : Set Y} (hA : MeasurableSet A) : Measurable (cellCnt A) :=
  measurable_cellSum _ (measurable_one.indicator hA)

lemma cellSum_linear {κ : Type*} (s : Finset κ) (c : κ → ℝ) (h : κ → Y → ℝ)
    (ω : ℕ × (ℕ → Y)) :
    cellSum (fun y => ∑ i ∈ s, c i * h i y) ω = ∑ i ∈ s, c i * cellSum (h i) ω := by
  simp only [cellSum, Finset.mul_sum]
  exact Finset.sum_comm

/-- σ-algebra of the cell configuration restricted to `D`. -/
noncomputable def cellSigma (D : Set Y) : MeasurableSpace (ℕ × (ℕ → Y)) :=
  ⨆ A : {A : Set Y // MeasurableSet A ∧ A ⊆ D}, MeasurableSpace.comap (cellCnt A.1) inferInstance

lemma inner_vecOf {Ω ι : Type*} (f : ι → Ω → ℝ) (F : Finset ι) (ω : Ω)
    (t : EuclideanSpace ℝ F) :
    inner ℝ (vecOf f F ω) t = ∑ i : F, (WithLp.ofLp t) i * f i ω := by
  simp [vecOf, PiLp.inner_apply]

/-- **Poisson splitting in one cell**: the configurations in `D` and in `Dᶜ` are independent. -/
theorem cell_indep_split (lam : ℝ≥0) (p : Measure Y) [IsProbabilityMeasure p] (D : Set Y) :
    Indep (cellSigma D) (cellSigma Dᶜ) (cellMeasure lam p) := by
  classical
  unfold cellSigma
  refine indep_iSup_of_vec (cellMeasure lam p)
    (fun A : {A : Set Y // MeasurableSet A ∧ A ⊆ D} => cellCnt A.1)
    (fun A : {A : Set Y // MeasurableSet A ∧ A ⊆ Dᶜ} => cellCnt A.1)
    (fun A => measurable_cellCnt A.2.1) (fun A => measurable_cellCnt A.2.1) ?_
  intro F G
  refine cell_indepFun lam p D _ _ ?_ ?_
    (fun t y => ∑ i : F, (WithLp.ofLp t) i * (i.1.1.indicator 1 y))
    (fun t y => ∑ i : G, (WithLp.ofLp t) i * (i.1.1.indicator 1 y)) ?_ ?_ ?_ ?_ ?_ ?_
  · unfold vecOf
    have := fun i : F => measurable_cellCnt i.1.2.1
    fun_prop
  · unfold vecOf
    have := fun i : G => measurable_cellCnt i.1.2.1
    fun_prop
  · intro t
    exact Finset.measurable_sum _ (fun i _ => measurable_const.mul
      (measurable_one.indicator i.1.2.1))
  · intro t
    exact Finset.measurable_sum _ (fun i _ => measurable_const.mul
      (measurable_one.indicator i.1.2.1))
  · intro ω t
    rw [inner_vecOf, cellSum_linear]
    rfl
  · intro ω t
    rw [inner_vecOf, cellSum_linear]
    rfl
  · intro t y hy
    refine Finset.sum_eq_zero (fun i _ => ?_)
    have : y ∉ i.1.1 := fun h => hy (i.1.2.2 h)
    simp [this]
  · intro t y hy
    refine Finset.sum_eq_zero (fun i _ => ?_)
    have : y ∉ i.1.1 := fun h => (i.1.2.2 h) hy
    simp [this]

/-! ### Independent blocks, each split into two independent parts -/

lemma indep_iSup_blocks {Ω J : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (M A B : J → MeasurableSpace Ω) (hM : iIndep M μ)
    (hMle : ∀ j, M j ≤ mΩ) (hA : ∀ j, A j ≤ M j) (hB : ∀ j, B j ≤ M j)
    (hAB : ∀ j, Indep (A j) (B j) μ) :
    Indep (⨆ j, A j) (⨆ j, B j) μ := by
  classical
  have hgA := generateFrom_piiUnionInter_measurableSet A Set.univ
  have hgB := generateFrom_piiUnionInter_measurableSet B Set.univ
  simp only [Set.mem_univ, iSup_true] at hgA hgB
  refine IndepSets.indep (iSup_le fun j => (hA j).trans (hMle j))
    (iSup_le fun j => (hB j).trans (hMle j))
    (isPiSystem_piiUnionInter _ (fun j => @MeasurableSpace.isPiSystem_measurableSet Ω (A j)) _)
    (isPiSystem_piiUnionInter _ (fun j => @MeasurableSpace.isPiSystem_measurableSet Ω (B j)) _)
    hgA.symm hgB.symm ?_
  rw [IndepSets_iff]
  rintro s1 s2 ⟨t1, -, f1, hf1, rfl⟩ ⟨t2, -, f2, hf2, rfl⟩
  let F := t1 ∪ t2
  let g1 : J → Set Ω := fun x => if x ∈ t1 then f1 x else Set.univ
  let g2 : J → Set Ω := fun x => if x ∈ t2 then f2 x else Set.univ
  have hg1 : ∀ x, MeasurableSet[A x] (g1 x) := fun x => by
    by_cases h : x ∈ t1
    · simp only [g1, h, if_true]; exact hf1 x h
    · simp only [g1, h, if_false]; exact MeasurableSet.univ
  have hg2 : ∀ x, MeasurableSet[B x] (g2 x) := fun x => by
    by_cases h : x ∈ t2
    · simp only [g2, h, if_true]; exact hf2 x h
    · simp only [g2, h, if_false]; exact MeasurableSet.univ
  have e1 : (⋂ x ∈ t1, f1 x) = ⋂ x ∈ F, g1 x := by
    ext ω
    simp only [Set.mem_iInter, g1, F, Finset.mem_union]
    constructor
    · intro h x _
      split_ifs with h1
      · exact h x h1
      · trivial
    · intro h x hx
      have := h x (Or.inl hx)
      simpa [hx] using this
  have e2 : (⋂ x ∈ t2, f2 x) = ⋂ x ∈ F, g2 x := by
    ext ω
    simp only [Set.mem_iInter, g2, F, Finset.mem_union]
    constructor
    · intro h x _
      split_ifs with h1
      · exact h x h1
      · trivial
    · intro h x hx
      have := h x (Or.inr hx)
      simpa [hx] using this
  have e12 : (⋂ x ∈ F, g1 x) ∩ (⋂ x ∈ F, g2 x) = ⋂ x ∈ F, (g1 x ∩ g2 x) := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨h1, h2⟩ x hx
      exact ⟨h1 x hx, h2 x hx⟩
    · intro h
      exact ⟨fun x hx => (h x hx).1, fun x hx => (h x hx).2⟩
  rw [e1, e2, e12, hM.meas_biInter (fun x _ => (hA x _ (hg1 x)).inter (hB x _ (hg2 x))),
    hM.meas_biInter (fun x _ => hA x _ (hg1 x)), hM.meas_biInter (fun x _ => hB x _ (hg2 x)),
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun x _ => ?_)
  exact (Indep_iff _ _ _).1 (hAB x) _ _ (hg1 x) (hg2 x)

/-! ### Means -/

lemma poisson_mean (lam : ℝ≥0) : ∫⁻ n, (n : ℝ≥0∞) ∂(poissonMeasure lam) = lam := by
  let F : ℕ → ℝ := fun n => Real.exp (-(lam : ℝ)) * (lam : ℝ) ^ n / (n.factorial : ℝ) * n
  have hs : HasSum F (lam : ℝ) := by
    have h1 := (hasSum_one_poissonMeasure lam).mul_left (lam : ℝ)
    rw [mul_one] at h1
    have key : ∀ n : ℕ, (lam : ℝ) * (Real.exp (-(lam : ℝ)) * (lam : ℝ) ^ n / (n.factorial : ℝ))
        = F (n + 1) := by
      intro n
      simp only [F]
      rw [Nat.factorial_succ, pow_succ]
      push_cast
      have hf : (n.factorial : ℝ) ≠ 0 := by positivity
      field_simp
    simp_rw [key] at h1
    have h3 : HasSum (fun n => F (n + 1)) ((lam : ℝ) - ∑ i ∈ Finset.range 1, F i) := by
      simp only [Finset.sum_range_one, F, Nat.cast_zero, mul_zero, sub_zero]
      exact h1
    exact (hasSum_nat_add_iff' 1).mp h3
  unfold poissonMeasure
  rw [lintegral_sum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac]
  have hnn : ∀ n : ℕ, 0 ≤ Real.exp (-(lam : ℝ)) * (lam : ℝ) ^ n / (n.factorial : ℝ) :=
    fun n => by positivity
  have e : ∀ n : ℕ, ENNReal.ofReal (Real.exp (-(lam : ℝ)) * (lam : ℝ) ^ n / (n.factorial : ℝ)) *
      (n : ℝ≥0∞) = ENNReal.ofReal
        (Real.exp (-(lam : ℝ)) * (lam : ℝ) ^ n / (n.factorial : ℝ) * n) := by
    intro n
    rw [ENNReal.ofReal_mul (hnn n), ENNReal.ofReal_natCast]
  simp_rw [smul_eq_mul, e]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (hnn n) (Nat.cast_nonneg n))
    hs.summable, hs.tsum_eq, ENNReal.ofReal_coe_nnreal]

/-- number of cell points in `A`, in `ℝ≥0∞`. -/
noncomputable def cellCntE (A : Set Y) (ω : ℕ × (ℕ → Y)) : ℝ≥0∞ :=
  ∑ k ∈ Finset.range ω.1, A.indicator 1 (ω.2 k)

lemma measurable_cellCntE {A : Set Y} (hA : MeasurableSet A) : Measurable (cellCntE A) := by
  apply measurable_from_prod_countable_right
  intro n
  show Measurable fun y : ℕ → Y => ∑ k ∈ Finset.range n, A.indicator 1 (y k)
  exact Finset.measurable_sum _ (fun k _ =>
    (measurable_one.indicator hA).comp (measurable_pi_apply k))

lemma cell_mean (lam : ℝ≥0) (p : Measure Y) [IsProbabilityMeasure p] {A : Set Y}
    (hA : MeasurableSet A) :
    ∫⁻ ω, cellCntE A ω ∂(cellMeasure lam p) = lam * p A := by
  unfold cellMeasure
  rw [lintegral_prod _ (measurable_cellCntE hA).aemeasurable]
  have hin : ∀ n : ℕ, ∫⁻ x, cellCntE A (n, x) ∂(Measure.infinitePi (fun _ : ℕ => p)) =
      (n : ℝ≥0∞) * p A := by
    intro n
    simp only [cellCntE]
    rw [lintegral_finsetSum (f := fun k (x : ℕ → Y) => A.indicator 1 (x k)) _ (fun k _ =>
      (measurable_one.indicator hA).comp (measurable_pi_apply k))]
    have hk : ∀ k : ℕ, ∫⁻ x, A.indicator 1 (x k) ∂(Measure.infinitePi (fun _ : ℕ => p)) =
        p A := by
      intro k
      have hm := Measure.infinitePi_map_eval (μ := fun _ : ℕ => p) k
      rw [← lintegral_map (measurable_one.indicator hA) (measurable_pi_apply k), hm,
        lintegral_indicator_one hA]
    simp only [hk, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  simp only [hin]
  rw [lintegral_mul_const _ (Measurable.of_discrete), poisson_mean]

/-! ### Global atoms: cells `j = (n, c)` of `[0,∞) × κ × U` -/

section Global

open JacodTodorov10.LLN

variable {κ U : Type*} [MeasurableSpace κ] [MeasurableSpace U]

/-- configurations of all cells `j = (n, c)`: a count and a sequence of (time, mark) points. -/
abbrev Cfg (κ U : Type*) := ℕ × κ → ℕ × (ℕ → ℝ≥0 × U)

/-- atom map of cell `j = (n, c)`: time `t`, mark `ξ` ↦ `(t, (c, ξ))`. -/
def atomOf (j : ℕ × κ) (y : ℝ≥0 × U) : ℝ≥0 × (κ × U) := (y.1, (j.2, y.2))

/-- the raw atom set of a configuration of all cells. -/
def rawN (ω : Cfg κ U) : Set (ℝ≥0 × (κ × U)) :=
  {z | ∃ j k, k < (ω j).1 ∧ atomOf j ((ω j).2 k) = z}

/-- distinct labels give distinct atoms. -/
def AtomInj (ω : Cfg κ U) : Prop :=
  ∀ j k j' k', k < (ω j).1 → k' < (ω j').1 →
    atomOf j ((ω j).2 k) = atomOf j' ((ω j').2 k') → j = j' ∧ k = k'

lemma encard_rawN_inter [Countable κ] [MeasurableSingletonClass κ]
    (ω : Cfg κ U) (h : AtomInj ω)
    (B : Set (ℝ≥0 × (κ × U))) :
    (((rawN ω ∩ B).encard : ℕ∞) : ℝ≥0∞) = ∑' j, cellCntE (atomOf j ⁻¹' B) (ω j) := by
  classical
  let I : Set ((ℕ × κ) × ℕ) :=
    {x | x.2 < (ω x.1).1 ∧ atomOf x.1 ((ω x.1).2 x.2) ∈ B}
  let ψ : (ℕ × κ) × ℕ → ℝ≥0 × (κ × U) := fun x => atomOf x.1 ((ω x.1).2 x.2)
  have himg : rawN ω ∩ B = ψ '' I := by
    ext z
    constructor
    · rintro ⟨⟨j, k, hk, rfl⟩, hB⟩
      exact ⟨(j, k), ⟨hk, hB⟩, rfl⟩
    · rintro ⟨⟨j, k⟩, ⟨hk, hB⟩, rfl⟩
      exact ⟨⟨j, k, hk, rfl⟩, hB⟩
  have hinj : Set.InjOn ψ I := by
    rintro ⟨j, k⟩ ⟨hk, -⟩ ⟨j', k'⟩ ⟨hk', -⟩ he
    obtain ⟨h1, h2⟩ := h j k j' k' hk hk' he
    simp [h1, h2]
  rw [himg, hinj.encard_image, ← Measure.count_apply (MeasurableSet.of_discrete),
    ← lintegral_indicator_one (MeasurableSet.of_discrete), lintegral_count,
    show (∑' a : (ℕ × κ) × ℕ, I.indicator 1 a) = ∑' j, ∑' k, I.indicator 1 (j, k) from
      ENNReal.tsum_prod (f := fun j k => I.indicator (1 : (ℕ × κ) × ℕ → ℝ≥0∞) (j, k))]
  refine tsum_congr (fun j => ?_)
  rw [tsum_eq_sum (s := Finset.range (ω j).1)]
  · refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk' : k < (ω j).1 := Finset.mem_range.1 hk
    by_cases hB : atomOf j ((ω j).2 k) ∈ B
    · have hI : (j, k) ∈ I := ⟨hk', hB⟩
      have hB' : (ω j).2 k ∈ atomOf j ⁻¹' B := hB
      simp [Set.indicator_of_mem hI, Set.indicator_of_mem hB']
    · have hI : (j, k) ∉ I := fun hh => hB hh.2
      have hB' : (ω j).2 k ∉ atomOf j ⁻¹' B := hB
      simp [Set.indicator_of_notMem hI, Set.indicator_of_notMem hB']
  · intro k hk
    have hk' : ¬ k < (ω j).1 := fun h => hk (Finset.mem_range.2 h)
    have hI : (j, k) ∉ I := fun hh => hk' hh.1
    simp [Set.indicator_of_notMem hI]

lemma measurable_atomOf (j : ℕ × κ) : Measurable (atomOf (U := U) j) := by
  unfold atomOf
  exact measurable_fst.prodMk (measurable_const.prodMk measurable_snd)

/-- mean of the raw count: `E Σ_j cellCnt_j (φ_j⁻¹ B) = Σ_j lam · p_j (φ_j⁻¹ B)`. -/
lemma mean_rawCnt [Countable κ] (lam : ℝ≥0) (p : ℕ × κ → Measure (ℝ≥0 × U))
    [∀ j, IsProbabilityMeasure (p j)]
    {B : Set (ℝ≥0 × (κ × U))} (hB : MeasurableSet B) :
    ∫⁻ ω, ∑' j, cellCntE (atomOf j ⁻¹' B) (ω j)
        ∂(Measure.infinitePi (fun j : ℕ × κ => cellMeasure lam (p j))) =
      ∑' j, (lam : ℝ≥0∞) * p j (atomOf j ⁻¹' B) := by
  have hmj : ∀ j : ℕ × κ, MeasurableSet (atomOf (U := U) j ⁻¹' B) :=
    fun j => measurable_atomOf j hB
  rw [lintegral_tsum (f := fun j (ω : Cfg κ U) =>
    cellCntE (atomOf j ⁻¹' B) (ω j)) (fun j => ((measurable_cellCntE (hmj j)).comp
    (measurable_pi_apply j)).aemeasurable)]
  refine tsum_congr (fun j => ?_)
  have hm := Measure.infinitePi_map_eval (μ := fun j : ℕ × κ => cellMeasure lam (p j)) j
  rw [← lintegral_map (measurable_cellCntE (hmj j)) (measurable_pi_apply j), hm,
    cell_mean lam (p j) (hmj j)]

/-! #### The cell laws `Leb|(n,n+1] ⊗ ν` and the intensity -/

lemma lebPos_Ioc' (s t : ℝ≥0) : lebPos (Set.Ioc s t) = ENNReal.ofReal ((t : ℝ) - s) := by
  unfold lebPos
  rw [NNReal.isClosedEmbedding_coe.measurableEmbedding.comap_apply]
  have : ((↑) : ℝ≥0 → ℝ) '' Set.Ioc s t = Set.Ioc (s : ℝ) t := NNReal.image_coe_Ioc s t
  erw [this]
  rw [Real.volume_Ioc]

lemma lebPos_singleton' (c : ℝ≥0) : lebPos ({c} : Set ℝ≥0) = 0 := by
  unfold lebPos
  rw [NNReal.isClosedEmbedding_coe.measurableEmbedding.comap_apply, Set.image_singleton]
  simp

lemma lebPos_Icc_lt_top' (s : ℝ≥0) : lebPos (Set.Icc 0 s) < ⊤ := by
  unfold lebPos
  rw [NNReal.isClosedEmbedding_coe.measurableEmbedding.comap_apply]
  refine lt_of_le_of_lt (measure_mono (t := Set.Icc (0 : ℝ) s) ?_) measure_Icc_lt_top
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨by exact_mod_cast hx.1, by exact_mod_cast hx.2⟩

theorem lebPos_sigmaFinite' : SigmaFinite lebPos :=
  ⟨⟨{ set := fun n : ℕ => Set.Icc 0 (n : ℝ≥0)
      set_mem := fun _ => trivial
      finite := fun n => lebPos_Icc_lt_top' n
      spanning := Set.eq_univ_of_forall fun u => by
        obtain ⟨k, hk⟩ := exists_nat_ge u
        exact Set.mem_iUnion.2 ⟨k, zero_le, hk⟩ }⟩⟩
attribute [local instance] lebPos_sigmaFinite'

/-- time window `(n, n+1]` of cell `j = (n, c)`. -/
def win (j : ℕ × κ) : Set ℝ≥0 := Set.Ioc (j.1 : ℝ≥0) (j.1 + 1)

lemma measurableSet_win (j : ℕ × κ) : MeasurableSet (win j) := measurableSet_Ioc

lemma lebPos_win (j : ℕ × κ) : lebPos (win j) = 1 := by
  unfold win
  rw [lebPos_Ioc']
  have : (((j.1 : ℝ≥0) + 1 : ℝ≥0) : ℝ) - ((j.1 : ℝ≥0) : ℝ) = 1 := by push_cast; ring
  rw [this, ENNReal.ofReal_one]

theorem lebPos_win_prob (j : ℕ × κ) : IsProbabilityMeasure (lebPos.restrict (win j)) :=
  ⟨by rw [Measure.restrict_apply_univ, lebPos_win]⟩
attribute [local instance] lebPos_win_prob

/-- law of one point of cell `j`. -/
noncomputable def cellLaw (ν : Measure U) (j : ℕ × κ) : Measure (ℝ≥0 × U) :=
  (lebPos.restrict (win j)).prod ν

theorem cellLaw_prob (ν : Measure U) [IsProbabilityMeasure ν] (j : ℕ × κ) :
    IsProbabilityMeasure (cellLaw ν j) := by
  unfold cellLaw; infer_instance
attribute [local instance] cellLaw_prob

/-- the region `(n, n+1] × {c} × U` of cell `j`. -/
def region (j : ℕ × κ) : Set (ℝ≥0 × (κ × U)) := win j ×ˢ ({j.2} ×ˢ Set.univ)

lemma measurableSet_region [MeasurableSingletonClass κ] (j : ℕ × κ) :
    MeasurableSet (region (U := U) j) :=
  (measurableSet_win j).prod ((measurableSet_singleton _).prod MeasurableSet.univ)

lemma map_cellLaw [Countable κ] [MeasurableSingletonClass κ] (ν : Measure U)
    [IsProbabilityMeasure ν] (j : ℕ × κ) :
    (cellLaw ν j).map (atomOf j) =
      (lebPos.prod (Measure.count.prod ν)).restrict (region j) := by
  have hA : atomOf (U := U) j = Prod.map id (Prod.mk j.2) := rfl
  unfold cellLaw region
  rw [hA, ← Measure.map_prod_map _ _ measurable_id measurable_prodMk_left, Measure.map_id,
    ← Measure.prod_restrict, ← Measure.prod_restrict, Measure.restrict_univ,
    Measure.restrict_singleton, Measure.count_singleton, one_smul, Measure.dirac_prod]

lemma region_disj : Pairwise (Function.onFun Disjoint (region (κ := κ) (U := U))) := by
  intro i j hij
  rw [Function.onFun, Set.disjoint_left]
  rintro ⟨t, c0, ξ⟩ ⟨ht, hc, -⟩ ⟨ht', hc', -⟩
  apply hij
  have hc1 : c0 = i.2 := hc
  have hc2 : c0 = j.2 := hc'
  have h1 : (i.1 : ℝ≥0) < (j.1 : ℝ≥0) + 1 := lt_of_lt_of_le ht.1 ht'.2
  have h2 : (j.1 : ℝ≥0) < (i.1 : ℝ≥0) + 1 := lt_of_lt_of_le ht'.1 ht.2
  have a : i.1 < j.1 + 1 := by exact_mod_cast h1
  have b : j.1 < i.1 + 1 := by exact_mod_cast h2
  exact Prod.ext (by omega) (hc1.symm.trans hc2)

lemma mem_iUnion_region (z : ℝ≥0 × (κ × U)) (hz : z.1 ≠ 0) : z ∈ ⋃ j, region (U := U) j := by
  refine Set.mem_iUnion.2 ⟨(⌈z.1⌉₊ - 1, z.2.1), ⟨?_, rfl, trivial⟩⟩
  have hpos : 0 < z.1 := pos_iff_ne_zero.2 hz
  have h1 : 1 ≤ ⌈z.1⌉₊ := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hpos).ne'
  have e : ((⌈z.1⌉₊ - 1 : ℕ) : ℝ≥0) + 1 = (⌈z.1⌉₊ : ℝ≥0) := by
    rw [← Nat.cast_add_one, Nat.sub_add_cancel h1]
  have hlt := Nat.ceil_lt_add_one hpos.le
  show z.1 ∈ Set.Ioc _ _
  refine ⟨?_, ?_⟩
  · rw [← e] at hlt
    exact (add_lt_add_iff_right 1).1 hlt
  · show z.1 ≤ ((⌈z.1⌉₊ - 1 : ℕ) : ℝ≥0) + 1
    rw [e]; exact Nat.le_ceil z.1

/-- **intensity**: `Σ_j p_j(φ_j⁻¹ B) = (Leb ⊗ count ⊗ ν)(B)`. -/
lemma sum_cellLaw [Countable κ] [MeasurableSingletonClass κ] (ν : Measure U)
    [IsProbabilityMeasure ν] {B : Set (ℝ≥0 × (κ × U))} (hB : MeasurableSet B) :
    ∑' j, cellLaw ν j (atomOf j ⁻¹' B) = (lebPos.prod (Measure.count.prod ν)) B := by
  have h1 : ∀ j, cellLaw ν j (atomOf j ⁻¹' B) =
      (lebPos.prod (Measure.count.prod ν)) (B ∩ region j) := by
    intro j
    rw [← Measure.map_apply (measurable_atomOf j) hB, map_cellLaw, Measure.restrict_apply hB]
  simp_rw [h1]
  rw [← measure_iUnion (f := fun j => B ∩ region j)
    (fun i j hij => Disjoint.mono Set.inter_subset_right Set.inter_subset_right (region_disj hij))
    (fun j => hB.inter (measurableSet_region j)), ← Set.inter_iUnion]
  refine le_antisymm (measure_mono Set.inter_subset_left) ?_
  rw [← measure_inter_add_diff B (MeasurableSet.iUnion measurableSet_region)]
  have h0 : (lebPos.prod (Measure.count.prod ν)) (B \ ⋃ j, region j) = 0 := by
    refine measure_mono_null (t := ({0} : Set ℝ≥0) ×ˢ Set.univ) ?_ ?_
    · intro z hz
      by_contra hne
      exact hz.2 (mem_iUnion_region z (fun h0 => hne ⟨h0, trivial⟩))
    · rw [Measure.prod_prod, lebPos_singleton', zero_mul]
  rw [h0, add_zero]

/-! #### The good set: all points in their windows, all times distinct -/

/-- time of point `k` of cell `j`. -/
def tm (j : ℕ × κ) (k : ℕ) (ω : Cfg κ U) : ℝ≥0 := ((ω j).2 k).1

lemma measurable_tm (j : ℕ × κ) (k : ℕ) : Measurable (tm (U := U) j k) :=
  measurable_fst.comp ((measurable_pi_apply k).comp (measurable_snd.comp (measurable_pi_apply j)))

def Good (ω : Cfg κ U) : Prop :=
  (∀ j k, tm j k ω ∈ win j) ∧ (∀ j k j' k', (j, k) ≠ (j', k') → tm j k ω ≠ tm j' k' ω)

lemma good_inj {ω : Cfg κ U} (h : Good ω) : AtomInj ω := by
  intro j k j' k' _ _ he
  have ht : tm j k ω = tm j' k' ω := by
    have h' := congrArg Prod.fst he
    exact h'
  by_contra hne
  exact h.2 j k j' k' (fun hh => hne (Prod.mk.inj hh)) ht

lemma measurableSet_good [Countable κ] : MeasurableSet {ω : Cfg κ U | Good ω} := by
  have e : {ω : Cfg κ U | Good ω} = (⋂ j, ⋂ k, {ω | tm j k ω ∈ win j}) ∩
      ⋂ j, ⋂ k, ⋂ j', ⋂ k', {ω | (j, k) ≠ (j', k') → tm j k ω ≠ tm j' k' ω} := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Good]
  rw [e]
  refine MeasurableSet.inter (MeasurableSet.iInter fun j => MeasurableSet.iInter fun k =>
    measurable_tm j k (measurableSet_win j)) (MeasurableSet.iInter fun j =>
    MeasurableSet.iInter fun k => MeasurableSet.iInter fun j' => MeasurableSet.iInter fun k' => ?_)
  by_cases h : (j, k) = (j', k')
  · have : {ω : Cfg κ U | (j, k) ≠ (j', k') → tm j k ω ≠ tm j' k' ω} = Set.univ := by
      ext ω; simp [h]
    rw [this]; exact MeasurableSet.univ
  · have : {ω : Cfg κ U | (j, k) ≠ (j', k') → tm j k ω ≠ tm j' k' ω} =
        {ω | tm j k ω = tm j' k' ω}ᶜ := by
      ext ω; simp [h]
    rw [this]; exact (measurableSet_eq_fun (measurable_tm j k) (measurable_tm j' k')).compl

/-- the law of all cells. -/
noncomputable def mu0 (ν : Measure U) [IsProbabilityMeasure ν] : Measure (Cfg κ U) :=
  Measure.infinitePi (fun j : ℕ × κ => cellMeasure 1 (cellLaw ν j))

theorem mu0_prob (ν : Measure U) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (mu0 (κ := κ) ν) := by
  unfold mu0; infer_instance
attribute [local instance] mu0_prob

lemma map_tm_cell (ν : Measure U) [IsProbabilityMeasure ν] (j : ℕ × κ) (k : ℕ) :
    (cellMeasure 1 (cellLaw ν j)).map (fun c => (c.2 k).1) = lebPos.restrict (win j) := by
  have : (fun c : ℕ × (ℕ → ℝ≥0 × U) => (c.2 k).1) = Prod.fst ∘ (fun x => x k) ∘ Prod.snd := rfl
  rw [this, ← Measure.map_map measurable_fst ((measurable_pi_apply k).comp measurable_snd),
    ← Measure.map_map (measurable_pi_apply k) measurable_snd]
  unfold cellMeasure
  rw [Measure.map_snd_prod, measure_univ, one_smul, Measure.infinitePi_map_eval, cellLaw,
    Measure.map_fst_prod, measure_univ, one_smul]

lemma map_tm (ν : Measure U) [IsProbabilityMeasure ν] (j : ℕ × κ) (k : ℕ) :
    (mu0 ν).map (tm j k) = lebPos.restrict (win j) := by
  have : tm (U := U) j k = (fun c => (c.2 k).1) ∘ (fun ω => ω j) := rfl
  have hg : Measurable (fun c : ℕ × (ℕ → ℝ≥0 × U) => (c.2 k).1) :=
    measurable_fst.comp ((measurable_pi_apply k).comp measurable_snd)
  rw [this, ← Measure.map_map hg (measurable_pi_apply j), mu0, Measure.infinitePi_map_eval,
    map_tm_cell]

lemma tm_win_null (ν : Measure U) [IsProbabilityMeasure ν] (j : ℕ × κ) (k : ℕ) :
    (mu0 ν) {ω | tm j k ω ∉ win j} = 0 := by
  rw [show {ω | tm j k ω ∉ win j} = tm j k ⁻¹' (win j)ᶜ from rfl,
    ← Measure.map_apply (measurable_tm j k) (measurableSet_win j).compl, map_tm,
    Measure.restrict_apply (measurableSet_win j).compl, Set.compl_inter_self, measure_empty]

lemma indepFun_comp_map {Ω Ω' β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace β] [MeasurableSpace γ] {μ : Measure Ω} {h : Ω → Ω'} (hh : Measurable h)
    {f : Ω' → β} {g : Ω' → γ} (hf : Measurable f) (hg : Measurable g)
    (hfg : IndepFun f g (μ.map h)) : IndepFun (f ∘ h) (g ∘ h) μ := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at hfg ⊢
  intro A B hA hB
  have := hfg A B hA hB
  rw [Measure.map_apply hh ((hf hA).inter (hg hB)), Measure.map_apply hh (hf hA),
    Measure.map_apply hh (hg hB)] at this
  exact this

lemma diag_null {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ≥0} (hX : Measurable X) (hY : Measurable Y) (hi : IndepFun X Y μ)
    (hat : ∀ x, μ.map X {x} = 0) : μ {ω | X ω = Y ω} = 0 := by
  have hd : MeasurableSet {p : ℝ≥0 × ℝ≥0 | p.1 = p.2} :=
    measurableSet_eq_fun measurable_fst measurable_snd
  have e : {ω | X ω = Y ω} = (fun ω => (X ω, Y ω)) ⁻¹' {p | p.1 = p.2} := rfl
  rw [e, ← Measure.map_apply (hX.prodMk hY) hd,
    (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).1 hi,
    Measure.prod_apply_symm hd]
  simp only [Set.preimage_setOf_eq, Set.setOf_eq_eq_singleton, hat, lintegral_zero]

lemma indep_tm (ν : Measure U) [IsProbabilityMeasure ν] {j j' : ℕ × κ} {k k' : ℕ}
    (hne : (j, k) ≠ (j', k')) : IndepFun (tm j k) (tm j' k') (mu0 ν) := by
  by_cases hj : j = j'
  · subst hj
    have hk : k ≠ k' := fun h => hne (by rw [h])
    have h0 : IndepFun (fun x : ℕ → ℝ≥0 × U => (x k).1) (fun x => (x k').1)
        ((cellMeasure 1 (cellLaw ν j)).map Prod.snd) := by
      unfold cellMeasure
      rw [Measure.map_snd_prod, measure_univ, one_smul]
      have := (iIndepFun_infinitePi (P := fun _ : ℕ => cellLaw ν j) (X := fun _ y => y)
        (fun _ => measurable_id)).indepFun hk
      exact this.comp measurable_fst measurable_fst
    have hcell := indepFun_comp_map measurable_snd (measurable_fst.comp (measurable_pi_apply k))
      (measurable_fst.comp (measurable_pi_apply k')) h0
    have h1 : IndepFun (fun c : ℕ × (ℕ → ℝ≥0 × U) => (c.2 k).1) (fun c => (c.2 k').1)
        ((mu0 ν).map (fun ω => ω j)) := by
      rw [mu0, Measure.infinitePi_map_eval]; exact hcell
    have hg : Measurable (fun c : ℕ × (ℕ → ℝ≥0 × U) => (c.2 k).1) :=
      measurable_fst.comp ((measurable_pi_apply k).comp measurable_snd)
    have hg' : Measurable (fun c : ℕ × (ℕ → ℝ≥0 × U) => (c.2 k').1) :=
      measurable_fst.comp ((measurable_pi_apply k').comp measurable_snd)
    exact indepFun_comp_map (μ := mu0 ν) (h := fun ω : Cfg κ U => ω j)
      (f := fun c : ℕ × (ℕ → ℝ≥0 × U) => (c.2 k).1)
      (g := fun c : ℕ × (ℕ → ℝ≥0 × U) => (c.2 k').1) (measurable_pi_apply j) hg hg' h1
  · have h0 := (iIndepFun_infinitePi (P := fun j : ℕ × κ => cellMeasure 1 (cellLaw ν j))
      (X := fun _ y => y) (fun _ => measurable_id)).indepFun hj
    exact h0.comp (φ := fun c : ℕ × (ℕ → ℝ≥0 × U) => (c.2 k).1)
      (ψ := fun c : ℕ × (ℕ → ℝ≥0 × U) => (c.2 k').1)
      (measurable_fst.comp ((measurable_pi_apply k).comp measurable_snd))
      (measurable_fst.comp ((measurable_pi_apply k').comp measurable_snd))

lemma good_compl_null [Countable κ] (ν : Measure U) [IsProbabilityMeasure ν] :
    (mu0 ν) {ω : Cfg κ U | Good ω}ᶜ = 0 := by
  have e : {ω : Cfg κ U | Good ω}ᶜ ⊆ (⋃ j, ⋃ k, {ω | tm j k ω ∉ win j}) ∪
      ⋃ j, ⋃ k, ⋃ j', ⋃ k', {ω | (j, k) ≠ (j', k') ∧ tm j k ω = tm j' k' ω} := by
    intro ω hω
    by_cases h1 : ∀ j k, tm j k ω ∈ win j
    · have h2 : ¬ ∀ j k j' k', (j, k) ≠ (j', k') → tm j k ω ≠ tm j' k' ω :=
        fun h2 => hω ⟨h1, h2⟩
      push_neg at h2
      obtain ⟨j, k, j', k', hne, heq⟩ := h2
      refine Or.inr ?_
      simp only [Set.mem_iUnion]
      exact ⟨j, k, j', k', hne, heq⟩
    · push_neg at h1
      obtain ⟨j, k, h⟩ := h1
      exact Or.inl (Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨k, h⟩⟩)
  refine measure_mono_null e (measure_union_null (measure_iUnion_null fun j =>
    measure_iUnion_null fun k => tm_win_null ν j k) (measure_iUnion_null fun j =>
    measure_iUnion_null fun k => measure_iUnion_null fun j' => measure_iUnion_null fun k' => ?_))
  by_cases h : (j, k) = (j', k')
  · have : {ω : Cfg κ U | (j, k) ≠ (j', k') ∧ tm j k ω = tm j' k' ω} = ∅ := by
      ext ω; simp [h]
    rw [this, measure_empty]
  · refine measure_mono_null (fun ω hω => hω.2) ?_
    refine diag_null (measurable_tm j k) (measurable_tm j' k') (indep_tm ν h) (fun x => ?_)
    rw [map_tm, Measure.restrict_apply (measurableSet_singleton x)]
    exact measure_mono_null Set.inter_subset_left (lebPos_singleton' x)

/-! #### The atom set and the clauses that do not involve the filtration -/

open Classical in
/-- the atoms: `rawN` on the good set, empty off it. -/
noncomputable def Nset (ω : Cfg κ U) : Set (ℝ≥0 × (κ × U)) := if Good ω then rawN ω else ∅

/-- the count sum `Σ_j #{points of cell j in φ_j⁻¹ B}`. -/
noncomputable def cntSum (B : Set (ℝ≥0 × (κ × U))) (ω : Cfg κ U) : ℝ≥0∞ :=
  ∑' j, cellCntE (atomOf j ⁻¹' B) (ω j)

lemma measurable_cntSum [Countable κ] {B : Set (ℝ≥0 × (κ × U))} (hB : MeasurableSet B) :
    Measurable (cntSum B) :=
  Measurable.ennreal_tsum fun j =>
    (measurable_cellCntE (measurable_atomOf j hB)).comp (measurable_pi_apply j)

lemma cnt_Nset [Countable κ] [MeasurableSingletonClass κ] (B : Set (ℝ≥0 × (κ × U)))
    (ω : Cfg κ U) :
    cnt Nset ω B = {ω | Good ω}.indicator (cntSum B) ω := by
  classical
  unfold cnt Nset
  by_cases h : Good ω
  · rw [if_pos h, Set.indicator_of_mem (show ω ∈ {ω | Good ω} from h),
      encard_rawN_inter ω (good_inj h) B]
    rfl
  · rw [if_neg h, Set.indicator_of_notMem (show ω ∉ {ω | Good ω} from h)]
    simp

lemma measurable_cnt_Nset [Countable κ] [MeasurableSingletonClass κ]
    {B : Set (ℝ≥0 × (κ × U))} (hB : MeasurableSet B) :
    Measurable (fun ω : Cfg κ U => cnt Nset ω B) := by
  simp_rw [cnt_Nset]
  exact (measurable_cntSum hB).indicator measurableSet_good

lemma subsingleton_Nset (ω : Cfg κ U) (t : ℝ≥0) :
    {z | (t, z) ∈ (Nset ω : Set (ℝ≥0 × (κ × U)))}.Subsingleton := by
  classical
  unfold Nset
  by_cases h : Good ω
  · rw [if_pos h]
    rintro z ⟨j, k, hk, hz⟩ z' ⟨j', k', hk', hz'⟩
    have ht : tm j k ω = tm j' k' ω := (congrArg Prod.fst hz).trans (congrArg Prod.fst hz').symm
    obtain ⟨rfl, rfl⟩ : j = j' ∧ k = k' := by
      by_contra hne
      exact h.2 j k j' k' (fun hh => hne (Prod.mk.inj hh)) ht
    have := hz.symm.trans hz'
    exact congrArg Prod.snd this
  · rw [if_neg h]
    rintro z hz
    exact absurd hz (Set.notMem_empty _)

lemma mean_cnt_Nset [Countable κ] [MeasurableSingletonClass κ] (ν : Measure U)
    [IsProbabilityMeasure ν] {B : Set (ℝ≥0 × (κ × U))} (hB : MeasurableSet B) :
    ∫⁻ ω, cnt Nset ω B ∂(mu0 ν) = (lebPos.prod (Measure.count.prod ν)) B := by
  simp_rw [cnt_Nset]
  have hae : ∀ᵐ ω ∂(mu0 (κ := κ) ν), ω ∈ {ω : Cfg κ U | Good ω} :=
    ae_iff.2 (good_compl_null ν)
  rw [lintegral_congr_ae (hae.mono fun ω hω => Set.indicator_of_mem hω (cntSum B))]
  unfold cntSum mu0
  rw [mean_rawCnt 1 (cellLaw ν) hB, ← sum_cellLaw ν hB]
  simp

end Global

attribute [local instance] lebPos_sigmaFinite'
attribute [local instance] lebPos_win_prob
attribute [local instance] cellLaw_prob
attribute [local instance] mu0_prob

/-! ### P4: σ-algebras of the restricted configurations, completion, filtration -/

section Filt

open JacodTodorov10.LLN

lemma cellCntE_eq_ofReal (A : Set Y) (c : ℕ × (ℕ → Y)) :
    cellCntE A c = ENNReal.ofReal (cellCnt A c) := by
  unfold cellCntE cellCnt cellSum
  rw [ENNReal.ofReal_sum_of_nonneg]
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases h : c.2 k ∈ A
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  · intro k _
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

lemma cellSigma_le (D : Set Y) :
    cellSigma D ≤ (inferInstance : MeasurableSpace (ℕ × (ℕ → Y))) :=
  iSup_le fun A => (measurable_cellCnt A.2.1).comap_le

lemma cellSigma_mono {D D' : Set Y} (h : D ⊆ D') : cellSigma D ≤ cellSigma D' :=
  iSup_le fun A => le_iSup_of_le
    (⟨A.1, A.2.1, A.2.2.trans h⟩ : {A : Set Y // MeasurableSet A ∧ A ⊆ D'}) le_rfl

lemma measurable_cellCntE_sigma {A D : Set Y} (hA : MeasurableSet A) (hAD : A ⊆ D) :
    Measurable[cellSigma D] (cellCntE A) := by
  have h1 : Measurable[cellSigma D] (cellCnt A) :=
    (comap_measurable (cellCnt A)).mono (le_iSup (fun A : {A : Set Y // MeasurableSet A ∧ A ⊆ D} =>
      MeasurableSpace.comap (cellCnt A.1) inferInstance) ⟨A, hA, hAD⟩) le_rfl
  have : cellCntE A = fun c => ENNReal.ofReal (cellCnt A c) := funext (cellCntE_eq_ofReal A)
  rw [this]
  exact ENNReal.measurable_ofReal.comp h1

lemma cellCntE_iSup {A : Set Y} {E : ℕ → Set Y} (hE : Monotone E) (hAE : A ⊆ ⋃ m, E m)
    (c : ℕ × (ℕ → Y)) : cellCntE A c = ⨆ m, cellCntE (A ∩ E m) c := by
  refine le_antisymm ?_ (iSup_le fun m => ?_)
  · have hev : ∀ᶠ m in Filter.atTop, ∀ k ∈ Finset.range c.1,
        (A ∩ E m).indicator (1 : Y → ℝ≥0∞) (c.2 k) = A.indicator 1 (c.2 k) := by
      rw [Filter.eventually_all_finset]
      intro k _
      by_cases hk : c.2 k ∈ A
      · obtain ⟨m0, hm0⟩ := Set.mem_iUnion.1 (hAE hk)
        refine Filter.eventually_atTop.2 ⟨m0, fun m hm => ?_⟩
        rw [Set.indicator_of_mem hk, Set.indicator_of_mem (show c.2 k ∈ A ∩ E m from ⟨hk, hE hm hm0⟩)]
      · exact Filter.Eventually.of_forall fun m => by
          rw [Set.indicator_of_notMem hk, Set.indicator_of_notMem (fun h => hk h.1)]
    obtain ⟨m, hm⟩ := hev.exists
    refine le_iSup_of_le m (le_of_eq ?_)
    unfold cellCntE
    exact (Finset.sum_congr rfl hm).symm
  · unfold cellCntE
    exact Finset.sum_le_sum fun k _ =>
      Set.indicator_le_indicator_of_subset Set.inter_subset_left (fun _ => bot_le) _

lemma indep_comap_of_map {Ω Ω' : Type*} {m1 m2 : MeasurableSpace Ω'} [MeasurableSpace Ω]
    [mΩ' : MeasurableSpace Ω'] {μ : Measure Ω} {h : Ω → Ω'} (hh : Measurable h)
    (h1 : m1 ≤ mΩ') (h2 : m2 ≤ mΩ') (hi : Indep m1 m2 (μ.map h)) :
    Indep (m1.comap h) (m2.comap h) μ := by
  rw [Indep_iff] at hi ⊢
  rintro _ _ ⟨s1, hs1, rfl⟩ ⟨s2, hs2, rfl⟩
  have := hi s1 s2 hs1 hs2
  rwa [Measure.map_apply hh ((h1 _ hs1).inter (h2 _ hs2)), Measure.map_apply hh (h1 _ hs1),
    Measure.map_apply hh (h2 _ hs2)] at this

/-- the sets that are null or conull. -/
def nullsMS {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) : MeasurableSpace Ω where
  MeasurableSet' s := μ s = 0 ∨ μ sᶜ = 0
  measurableSet_empty := Or.inl measure_empty
  measurableSet_compl s hs := by rw [compl_compl]; exact hs.symm
  measurableSet_iUnion f hf := by
    by_cases h : ∀ i, μ (f i) = 0
    · exact Or.inl (measure_iUnion_null h)
    · push_neg at h
      obtain ⟨i, hi⟩ := h
      exact Or.inr (measure_mono_null (Set.compl_subset_compl.2 (Set.subset_iUnion f i))
        ((hf i).resolve_left hi))

lemma indep_sup_nulls {Ω : Type*} {m1 m2 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (h1 : m1 ≤ mΩ) (h2 : m2 ≤ mΩ)
    (hn : nullsMS μ ≤ mΩ) (h : Indep m1 m2 μ) : Indep m1 (m2 ⊔ nullsMS μ) μ := by
  let p2 : Set (Set Ω) :=
    {u | ∃ C D, MeasurableSet[m2] C ∧ MeasurableSet[nullsMS μ] D ∧ u = C ∩ D}
  have hp2 : IsPiSystem p2 := by
    rintro _ ⟨C, D, hC, hD, rfl⟩ _ ⟨C', D', hC', hD', rfl⟩ _
    refine ⟨C ∩ C', D ∩ D', hC.inter hC', hD.inter hD', ?_⟩
    rw [Set.inter_inter_inter_comm]
  have hgen : m2 ⊔ nullsMS μ = MeasurableSpace.generateFrom p2 := by
    refine le_antisymm (sup_le ?_ ?_) (MeasurableSpace.generateFrom_le ?_)
    · intro C hC
      exact MeasurableSpace.measurableSet_generateFrom ⟨C, Set.univ, hC, MeasurableSet.univ,
        (Set.inter_univ C).symm⟩
    · intro D hD
      exact MeasurableSpace.measurableSet_generateFrom ⟨Set.univ, D, MeasurableSet.univ, hD,
        (Set.univ_inter D).symm⟩
    · rintro _ ⟨C, D, hC, hD, rfl⟩
      exact ((le_sup_left : m2 ≤ m2 ⊔ nullsMS μ) _ hC).inter
        ((le_sup_right : nullsMS μ ≤ m2 ⊔ nullsMS μ) _ hD)
  refine IndepSets.indep h1 (sup_le h2 hn) (@MeasurableSpace.isPiSystem_measurableSet Ω m1)
    hp2 (@MeasurableSpace.generateFrom_measurableSet Ω m1).symm hgen ?_
  rw [IndepSets_iff]
  rintro t1 _ ht1 ⟨C, D, hC, hD, rfl⟩
  have hi := (Indep_iff _ _ _).1 h t1 C ht1 hC
  change μ D = 0 ∨ μ Dᶜ = 0 at hD
  rcases hD with h0 | h0
  · rw [measure_mono_null (Set.inter_subset_right.trans Set.inter_subset_right) h0,
      measure_mono_null Set.inter_subset_right h0, mul_zero]
  · rw [← Set.inter_assoc, measure_inter_conull h0, measure_inter_conull h0, hi]

variable {κ U : Type*} [MeasurableSpace κ] [MeasurableSpace U]

/-- `σ`-algebra of all cells restricted to `D`. -/
noncomputable def allSigma (D : Set (ℝ≥0 × U)) : MeasurableSpace (Cfg κ U) :=
  ⨆ j : ℕ × κ, (cellSigma D).comap (fun ω : Cfg κ U => ω j)

/-- points with time `≤ q`. -/
def Dle (q : ℝ≥0) : Set (ℝ≥0 × U) := {y | y.1 ≤ q}

lemma allSigma_le (D : Set (ℝ≥0 × U)) :
    allSigma (κ := κ) D ≤ (inferInstance : MeasurableSpace (Cfg κ U)) :=
  iSup_le fun j => (MeasurableSpace.comap_mono (cellSigma_le D)).trans
    (measurable_pi_apply j).comap_le

lemma allSigma_mono {D D' : Set (ℝ≥0 × U)} (h : D ⊆ D') : allSigma (κ := κ) D ≤ allSigma D' :=
  iSup_mono fun _ => MeasurableSpace.comap_mono (cellSigma_mono h)

lemma indep_allSigma (ν : Measure U) [IsProbabilityMeasure ν] (D : Set (ℝ≥0 × U)) :
    Indep (allSigma (κ := κ) D) (allSigma Dᶜ) (mu0 ν) := by
  unfold allSigma
  refine indep_iSup_blocks (mu0 ν) (fun j => (inferInstance : MeasurableSpace
    (ℕ × (ℕ → ℝ≥0 × U))).comap (fun ω : Cfg κ U => ω j)) _ _ ?_
    (fun j => (measurable_pi_apply j).comap_le)
    (fun j => MeasurableSpace.comap_mono (cellSigma_le D))
    (fun j => MeasurableSpace.comap_mono (cellSigma_le Dᶜ)) (fun j => ?_)
  · unfold mu0
    exact (iIndepFun_iff_iIndep _ _ _).1 (iIndepFun_infinitePi
      (P := fun j : ℕ × κ => cellMeasure 1 (cellLaw ν j)) (X := fun _ y => y)
      (fun _ => measurable_id))
  · refine indep_comap_of_map (measurable_pi_apply j) (cellSigma_le D) (cellSigma_le Dᶜ) ?_
    unfold mu0
    rw [Measure.infinitePi_map_eval]
    exact cell_indep_split 1 (cellLaw ν j) D

lemma measurable_cntSum_sigma [Countable κ] {B : Set (ℝ≥0 × (κ × U))} (hB : MeasurableSet B)
    {D : Set (ℝ≥0 × U)} (hBD : ∀ j, atomOf j ⁻¹' B ⊆ D) :
    Measurable[allSigma (κ := κ) D] (cntSum B) := by
  unfold cntSum
  refine Measurable.ennreal_tsum fun j => ?_
  have h1 := measurable_cellCntE_sigma (measurable_atomOf j hB) (hBD j)
  exact (h1.comp (comap_measurable (m := cellSigma D) (fun ω : Cfg κ U => ω j))).mono
    (le_iSup (fun j => (cellSigma D).comap (fun ω : Cfg κ U => ω j)) j) le_rfl

/-! #### The completed space -/

variable (κ U) in
/-- the completed sample space. -/
abbrev Om (ν : Measure U) [IsProbabilityMeasure ν] : Type _ :=
  NullMeasurableSpace (Cfg κ U) (mu0 (κ := κ) ν)

/-- the identity, viewed as a map to the uncompleted space. -/
def toCfg (ν : Measure U) [IsProbabilityMeasure ν] : Om κ U ν → Cfg κ U := fun ω => ω

/-- the completed law. -/
noncomputable def Pr (ν : Measure U) [IsProbabilityMeasure ν] : Measure (Om κ U ν) :=
  (mu0 ν).completion

theorem Pr_prob (ν : Measure U) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (Pr (κ := κ) ν) :=
  ⟨by show (mu0 (κ := κ) ν) Set.univ = 1; exact measure_univ⟩
attribute [local instance] Pr_prob

lemma m0_le (ν : Measure U) [IsProbabilityMeasure ν] :
    (inferInstance : MeasurableSpace (Cfg κ U)) ≤
      (inferInstance : MeasurableSpace (Om κ U ν)) :=
  fun _ hs => hs.nullMeasurableSet

lemma nulls_le (ν : Measure U) [IsProbabilityMeasure ν] :
    nullsMS (Pr (κ := κ) ν) ≤ (inferInstance : MeasurableSpace (Om κ U ν)) := by
  intro s hs
  change (mu0 ν) s = 0 ∨ (mu0 ν) sᶜ = 0 at hs
  rcases hs with h0 | h0
  · exact NullMeasurableSet.of_null h0
  · rw [← compl_compl s]
    exact MeasurableSet.compl (NullMeasurableSet.of_null h0)

lemma indep_completion (ν : Measure U) [IsProbabilityMeasure ν]
    {m1 m2 : MeasurableSpace (Cfg κ U)} (h : Indep m1 m2 (mu0 ν)) :
    Indep m1 m2 (Pr (κ := κ) ν) := by
  exact (Indep_iff m1 m2 (Pr (κ := κ) ν)).2
    (fun s t hs ht => (Indep_iff m1 m2 (mu0 ν)).1 h s t hs ht)

/-- `Past_q ∨ 𝒩`. -/
noncomputable def Gq (ν : Measure U) [IsProbabilityMeasure ν] (q : ℝ≥0) :
    MeasurableSpace (Om κ U ν) :=
  allSigma (κ := κ) (Dle q) ⊔ nullsMS (Pr (κ := κ) ν)

lemma Gq_le (ν : Measure U) [IsProbabilityMeasure ν] (q : ℝ≥0) :
    Gq (κ := κ) ν q ≤ (inferInstance : MeasurableSpace (Om κ U ν)) :=
  sup_le ((allSigma_le _).trans (m0_le ν)) (nulls_le ν)

/-- the filtration `𝓕_t = ⋂_{q > t} (Past_q ∨ 𝒩)`. -/
noncomputable def filt (ν : Measure U) [IsProbabilityMeasure ν] :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (Om κ U ν)) where
  seq t := ⨅ q > t, Gq (κ := κ) ν q
  mono' _ _ hst := le_iInf₂ fun q hq => iInf₂_le q (lt_of_le_of_lt hst hq)
  le' t := (iInf₂_le (t + 1) (lt_add_one t)).trans (Gq_le ν (t + 1))

lemma filt_apply (ν : Measure U) [IsProbabilityMeasure ν] (t : ℝ≥0) :
    filt (κ := κ) ν t = ⨅ q > t, Gq (κ := κ) ν q := rfl

lemma filt_null (ν : Measure U) [IsProbabilityMeasure ν] (A : Set (Om κ U ν))
    (hA : Pr (κ := κ) ν A = 0) (t : ℝ≥0) : MeasurableSet[filt (κ := κ) ν t] A := by
  rw [filt_apply]
  simp only [MeasurableSpace.measurableSet_iInf]
  intro q _
  exact (le_sup_right : nullsMS _ ≤ Gq (κ := κ) ν q) A (Or.inl hA)

lemma filt_rc (ν : Measure U) [IsProbabilityMeasure ν] (t : ℝ≥0) :
    filt (κ := κ) ν t = ⨅ s > t, filt (κ := κ) ν s := by
  apply le_antisymm
  · exact le_iInf₂ fun s hs => (filt ν).mono hs.le
  · rw [filt_apply]
    refine le_iInf₂ fun q hq => ?_
    obtain ⟨s, hts, hsq⟩ := exists_between hq
    refine (iInf₂_le s hts).trans ?_
    rw [filt_apply]
    exact iInf₂_le q hsq

lemma good_nulls [Countable κ] (ν : Measure U) [IsProbabilityMeasure ν] :
    MeasurableSet[nullsMS (Pr (κ := κ) ν)] {ω : Cfg κ U | Good ω} :=
  Or.inr (good_compl_null ν)

lemma filt_adapted [Countable κ] [MeasurableSingletonClass κ] (ν : Measure U)
    [IsProbabilityMeasure ν] (t : ℝ≥0) {A : Set (κ × U)} (hA : MeasurableSet A) :
    Measurable[filt (κ := κ) ν t] (fun ω : Om κ U ν => cnt Nset ω (Set.Icc 0 t ×ˢ A)) := by
  have hB : MeasurableSet (Set.Icc (0 : ℝ≥0) t ×ˢ A) := measurableSet_Icc.prod hA
  intro S hS
  rw [filt_apply]
  simp only [MeasurableSpace.measurableSet_iInf]
  intro q hq
  have h1 : Measurable[allSigma (κ := κ) (Dle q)] (cntSum (Set.Icc (0 : ℝ≥0) t ×ˢ A)) :=
    measurable_cntSum_sigma hB (fun j y hy => by
      show y.1 ≤ q
      exact hy.1.2.trans hq.le)
  have h2 : Measurable[Gq (κ := κ) ν q]
      ({ω : Cfg κ U | Good ω}.indicator (cntSum (Set.Icc (0 : ℝ≥0) t ×ˢ A))) :=
    (h1.mono (le_sup_left : allSigma (Dle q) ≤ Gq (κ := κ) ν q) le_rfl).indicator
      ((le_sup_right : nullsMS _ ≤ Gq (κ := κ) ν q) _ (good_nulls ν))
  have e : (fun ω : Om κ U ν => cnt Nset ω (Set.Icc 0 t ×ˢ A)) =
      {ω : Cfg κ U | Good ω}.indicator (cntSum (Set.Icc (0 : ℝ≥0) t ×ˢ A)) :=
    funext fun ω => cnt_Nset _ ω
  rw [e]
  exact h2 hS

lemma filt_indep [Countable κ] [MeasurableSingletonClass κ] (ν : Measure U)
    [IsProbabilityMeasure ν] (s : ℝ≥0) {B : Set (ℝ≥0 × (κ × U))} (hB : MeasurableSet B)
    (hBs : B ⊆ Set.Ioi s ×ˢ Set.univ) :
    Indep (MeasurableSpace.comap (fun ω : Om κ U ν => cnt Nset ω B) inferInstance)
      (filt (κ := κ) ν s) (Pr (κ := κ) ν) := by
  let q : ℕ → ℝ≥0 := fun m => s + 1 / ((m : ℝ≥0) + 1)
  have hqs : ∀ m, s < q m := fun m => lt_add_of_pos_right s (by positivity)
  have hqa : Antitone q := fun m m' hmm' => by
    simp only [q]
    gcongr
  let F : ℕ → MeasurableSpace (Om κ U ν) := fun m => allSigma (κ := κ) (Dle (q m))ᶜ
  have hFle : ∀ m, F m ≤ (inferInstance : MeasurableSpace (Om κ U ν)) :=
    fun m => (allSigma_le _).trans (m0_le ν)
  have hF : ∀ m, Indep (F m) (filt (κ := κ) ν s) (Pr (κ := κ) ν) := by
    intro m
    have h0 : Indep (F m) (allSigma (κ := κ) (Dle (q m))) (Pr (κ := κ) ν) :=
      indep_completion ν (indep_allSigma ν (Dle (q m))).symm
    have h1 := indep_sup_nulls (hFle m) ((allSigma_le _).trans (m0_le ν)) (nulls_le ν) h0
    refine indep_of_indep_of_le_right h1 ?_
    rw [filt_apply]
    exact iInf₂_le (q m) (hqs m)
  have hmono : Monotone F := fun m m' hmm' => allSigma_mono
    (Set.compl_subset_compl.2 (fun y (hy : y.1 ≤ q m') => (hy.trans (hqa hmm') : y.1 ≤ q m)))
  have hsup : Indep (⨆ m, F m) (filt (κ := κ) ν s) (Pr (κ := κ) ν) :=
    indep_iSup_of_directed_le hF hFle ((filt ν).le s) hmono.directed_le
  have hsup' : Indep ((⨆ m, F m) ⊔ nullsMS (Pr (κ := κ) ν)) (filt (κ := κ) ν s) (Pr (κ := κ) ν) :=
    (indep_sup_nulls ((filt ν).le s) (iSup_le hFle) (nulls_le ν) hsup.symm).symm
  refine indep_of_indep_of_le_left hsup' ?_
  have hterm : ∀ j : ℕ × κ, Measurable[⨆ m, F m]
      (fun ω : Cfg κ U => cellCntE (atomOf j ⁻¹' B) (ω j)) := by
    intro j
    have hAE : atomOf j ⁻¹' B ⊆ ⋃ m, (Dle (U := U) (q m))ᶜ := by
      intro y hy
      have hy1 : s < y.1 := (hBs hy).1
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt (tsub_pos_of_lt hy1)
      refine Set.mem_iUnion.2 ⟨m, fun (h : y.1 ≤ q m) => ?_⟩
      have : s + 1 / ((m : ℝ≥0) + 1) < y.1 := lt_tsub_iff_left.1 hm
      exact absurd h (not_le.2 this)
    have hEm : Monotone (fun m => (Dle (U := U) (q m))ᶜ) := fun m m' hmm' =>
      Set.compl_subset_compl.2 (fun y (hy : y.1 ≤ q m') => (hy.trans (hqa hmm') : y.1 ≤ q m))
    have e : (fun ω : Cfg κ U => cellCntE (atomOf j ⁻¹' B) (ω j)) =
        fun ω => ⨆ m, cellCntE (atomOf j ⁻¹' B ∩ (Dle (q m))ᶜ) (ω j) :=
      funext fun ω => cellCntE_iSup hEm hAE (ω j)
    rw [e]
    refine Measurable.iSup fun m => ?_
    have h1 := measurable_cellCntE_sigma ((measurable_atomOf j hB).inter
      (measurableSet_le measurable_fst measurable_const).compl)
      (Set.inter_subset_right : atomOf j ⁻¹' B ∩ (Dle (q m))ᶜ ⊆ (Dle (q m))ᶜ)
    refine (h1.comp (comap_measurable (m := cellSigma (Dle (q m))ᶜ)
      (fun ω : Cfg κ U => ω j))).mono ?_ le_rfl
    exact (le_iSup (fun j => (cellSigma (Dle (U := U) (q m))ᶜ).comap
      (fun ω : Cfg κ U => ω j)) j).trans (le_iSup F m)
  have hcs : Measurable[⨆ m, F m] (cntSum (κ := κ) B) := by
    unfold cntSum
    exact Measurable.ennreal_tsum hterm
  have hm : Measurable[(⨆ m, F m) ⊔ nullsMS (Pr (κ := κ) ν)]
      (fun ω : Om κ U ν => cnt Nset ω B) := by
    have e : (fun ω : Om κ U ν => cnt Nset ω B) = {ω : Cfg κ U | Good ω}.indicator (cntSum B) :=
      funext fun ω => cnt_Nset _ ω
    rw [e]
    exact (hcs.mono le_sup_left le_rfl).indicator (le_sup_right (a := ⨆ m, F m) _ (good_nulls ν))
  exact hm.comap_le

/-- **Existence of an `(𝓕_t)`-Poisson random measure** with intensity `Leb ⊗ count ⊗ ν`. -/
theorem isFPoisson_Nset [Countable κ] [MeasurableSingletonClass κ] (ν : Measure U)
    [IsProbabilityMeasure ν] :
    IsFPoisson (filt (κ := κ) ν) (Pr (κ := κ) ν) (Measure.count.prod ν)
      (fun ω : Om κ U ν => (Nset ω : Set (ℝ≥0 × (κ × U)))) := by
  refine ⟨fun ω t => subsingleton_Nset ω t, fun B hB => ?_, fun t A hA => filt_adapted ν t hA,
    fun B hB => ?_, fun s B hB hBs _ => filt_indep ν s hB hBs⟩
  · exact (measurable_cnt_Nset hB).mono (m0_le ν) le_rfl
  · have hid : Measurable (toCfg (κ := κ) ν) := fun s hs => m0_le ν s hs
    have hmap : (Pr (κ := κ) ν).map (toCfg ν) = mu0 ν := by
      ext S hS
      rw [Measure.map_apply hid hS]
      rfl
    have := lintegral_map (μ := Pr (κ := κ) ν) (measurable_cnt_Nset (U := U) hB) hid
    rw [hmap, mean_cnt_Nset ν hB] at this
    exact this.symm

/-- finitely many atoms of each mark slice up to any time (every `ω`). -/
lemma Nset_finite [Countable κ] (ω : Cfg κ U) (t : ℝ≥0) (c : κ) :
    {z : ℝ≥0 × (κ × U) | z ∈ Nset ω ∧ z.1 ≤ t ∧ z.2.1 = c}.Finite := by
  classical
  unfold Nset
  by_cases h : Good ω
  · simp only [if_pos h]
    refine Set.Finite.subset ((Finset.range (⌈t⌉₊ + 1)).finite_toSet.biUnion fun n _ =>
      (Finset.range (ω (n, c)).1).finite_toSet.biUnion fun k _ =>
        Set.finite_singleton (atomOf (n, c) ((ω (n, c)).2 k))) ?_
    rintro z ⟨⟨j, k, hk, rfl⟩, hzt, hzc⟩
    have hjc : j.2 = c := hzc
    have hw : tm j k ω ∈ win j := h.1 j k
    have htt : tm j k ω ≤ t := hzt
    have hj : j.1 < ⌈t⌉₊ + 1 := by
      have h1 : (j.1 : ℝ≥0) < t := lt_of_lt_of_le hw.1 htt
      have : (j.1 : ℝ≥0) < (⌈t⌉₊ : ℝ≥0) := lt_of_lt_of_le h1 (Nat.le_ceil t)
      exact Nat.lt_succ_of_lt (by exact_mod_cast this)
    obtain ⟨n, c'⟩ := j
    simp only at hjc hj
    subst hjc
    simp only [Set.mem_iUnion, Finset.coe_range, Set.mem_Iio, Set.mem_singleton_iff]
    exact ⟨n, hj, k, hk, rfl⟩
  · simp only [if_neg h]
    simp

/-- no atom at time `0` (every `ω`). -/
lemma Nset_pos (ω : Cfg κ U) {z : ℝ≥0 × (κ × U)} (hz : z ∈ Nset ω) : 0 < z.1 := by
  classical
  unfold Nset at hz
  by_cases h : Good ω
  · rw [if_pos h] at hz
    obtain ⟨j, k, _, rfl⟩ := hz
    have hw : tm j k ω ∈ win j := h.1 j k
    exact lt_of_le_of_lt (by positivity) hw.1
  · rw [if_neg h] at hz
    exact absurd hz (Set.notMem_empty _)

end Filt

end PPP


/-!
# Counterexample to NeuroMV.Chaos.theorem_1_8 (f046f7ad), Part I.

The Poisson random measures are abstract hypotheses here (`cex_main`); Part II instantiates them
with the PPP construction of `f046f7ad_lib/PPPCell.lean`.

Data: d = 1, m = n = 0, k = P = 1, τ = T = 1, U = ℝ with ν0 = Leb|[0,1], Ω' = Unit.
All coefficients are 0 except the look-ahead jump coefficient
`η0 t r r' x y ω' ξ = 1[r = r' = pos0 0 ∧ ξ = (y 1)₀] · (y 2)₀ · e0`,
which is nonzero only on a ν0-null set of marks (so (H4)/(H5) hold with zero rates), but which
reads the network path of neuron 0 beyond T.  Neuron 0 of the N-th network is the counting
process K of its own Poisson slice on [0,1]; on (1,2] it records the mark of the next atom and on
(2,∞) it equals N+1, so its netη integrand is exactly 1 at every atom.  Then
E|X^0_1 - Xbar^0_1|^2 = E K_1^2 ≥ E K_1 = 1 for every N ≥ 1.
-/

set_option autoImplicit false
set_option linter.all false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace NMVCex

open NeuroMV.Chaos

abbrev E1 := EthierKurtz.SDEState 1

theorem mscOpt : @MeasurableSingletonClass (Option (Fin 1)) (instMeasurableSpaceOptionFin 1) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

attribute [local instance] mscOpt

noncomputable def e0 : E1 := EuclideanSpace.single 0 1

lemma smul_e0_apply (c : ℝ) (i : Fin 1) : (c • e0) i = c := by
  fin_cases i; simp [e0]

lemma e0_apply (i : Fin 1) : e0 i = 1 := by
  fin_cases i; simp [e0]

@[simp] lemma e0_ofLp (i : Fin 1) : e0.ofLp i = 1 := by
  fin_cases i; simp [e0]

lemma enorm_smul_e0 (c : ℝ) : ‖c • e0‖ₑ = ‖c‖ₑ := by
  rw [enorm_smul]
  have : ‖e0‖ₑ = 1 := by
    rw [← ofReal_norm_eq_enorm, e0, EuclideanSpace.norm_single]; simp
  rw [this, mul_one]

noncomputable def ν0 : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

theorem ν0_prob : IsProbabilityMeasure ν0 := ⟨by simp [ν0]⟩

attribute [local instance] ν0_prob

lemma ν0_singleton (a : ℝ) : ν0 {a} = 0 := by
  unfold ν0; exact measure_singleton a

lemma ae_ne0 (a : ℝ) : ∀ᵐ ξ ∂ν0, ξ ≠ a := by
  rw [ae_iff]; simpa using ν0_singleton a

/-! ### Positions and geometry -/

noncomputable def pos0 (i : ℕ) : NeuroMV.WellPosed.Pos 1 :=
  (1 / ((i : ℝ) + 1)) • EuclideanSpace.single 0 1

lemma pos0_inj : Function.Injective pos0 := by
  intro i j h
  have := congrArg (fun v : NeuroMV.WellPosed.Pos 1 => v 0) h
  simp only [pos0] at this
  simp at this
  exact_mod_cast this

lemma pos0_mem (i : ℕ) : pos0 i ∈ Metric.ball (0 : NeuroMV.WellPosed.Pos 1) 2 := by
  rw [mem_ball_zero_iff, pos0, norm_smul, EuclideanSpace.norm_single, norm_one, mul_one,
    Real.norm_eq_abs, abs_of_pos (by positivity)]
  have : (1 : ℝ) / ((i : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
  linarith

noncomputable def G0 : Geometry 1 1 where
  τ := 1
  Γα := fun _ => Metric.ball 0 2
  𝓡 := Measure.dirac 0

lemma G0_Γ : G0.Γ = Metric.ball 0 2 := by
  show (⋃ _ : Fin 1, Metric.ball (0 : NeuroMV.WellPosed.Pos 1) 2) = _
  exact Set.iUnion_const _

lemma G0_valid : G0.Valid := by
  refine ⟨by show (0 : ℝ) < 1; norm_num, fun _ => Metric.isOpen_ball.measurableSet, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab; exact absurd (Subsingleton.elim a b) hab
  · rw [G0_Γ]; exact Metric.isBounded_ball
  · show IsFiniteMeasure (Measure.dirac _); infer_instance
  · rw [G0_Γ]
    show Measure.dirac (0 : NeuroMV.WellPosed.Pos 1) (Metric.ball 0 2)ᶜ = 0
    rw [Measure.dirac_apply' _ Metric.isOpen_ball.measurableSet.compl]
    simp
  · intro α
    show Measure.dirac (0 : NeuroMV.WellPosed.Pos 1) (Metric.ball 0 2) = 1
    exact Measure.dirac_apply_of_mem (Metric.mem_ball_self (by norm_num))

/-! ### Coefficients -/

open Classical in
noncomputable def η0 (_t : ℝ≥0) (r r' : NeuroMV.WellPosed.Pos 1) (_x : E1) (y : ℝ → E1)
    (_u : Unit) (ξ : ℝ) : E1 :=
  if r = pos0 0 ∧ r' = pos0 0 ∧ ξ = y 1 0 then (y 2 0) • e0 else 0

lemma η0_eq_zero_of_ne {t r r' x y u ξ} (h : ξ ≠ y 1 0) : η0 t r r' x y u ξ = 0 := by
  simp [η0, h]

lemma η0_eq_zero_of_r {t r r' x y u ξ} (h : r ≠ pos0 0) : η0 t r r' x y u ξ = 0 := by
  simp [η0, h]

lemma η0_eq_zero_of_r' {t r r' x y u ξ} (h : r' ≠ pos0 0) : η0 t r r' x y u ξ = 0 := by
  simp [η0, h]

lemma η0_zero_path {t r r' x u ξ} : η0 t r r' x 0 u ξ = 0 := by
  simp [η0]

lemma lint_η0_diff (t r r' x y u t2 r2 r2' x2 y2 u2) :
    ∫⁻ ξ, ‖η0 t r r' x y u ξ - η0 t2 r2 r2' x2 y2 u2 ξ‖ₑ ^ 2 ∂ν0 = 0 := by
  rw [lintegral_congr_ae (g := fun _ => 0) ?_, lintegral_zero]
  filter_upwards [ae_ne0 (y 1 0), ae_ne0 (y2 1 0)] with ξ h1 h2
  simp [η0_eq_zero_of_ne h1, η0_eq_zero_of_ne h2]

lemma lint_η0 (t r r' x y u) : ∫⁻ ξ, ‖η0 t r r' x y u ξ‖ₑ ^ 2 ∂ν0 = 0 := by
  rw [lintegral_congr_ae (g := fun _ => 0) ?_, lintegral_zero]
  filter_upwards [ae_ne0 (y 1 0)] with ξ h1
  simp [η0_eq_zero_of_ne h1]

lemma η0_meas : Measurable (fun p : ℝ≥0 × NeuroMV.WellPosed.Pos 1 × NeuroMV.WellPosed.Pos 1 × E1 ×
    (ℝ → E1) × Unit × ℝ =>
      η0 p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2) := by
  have hc : Measurable (fun v : E1 => v 0) := by fun_prop
  have hy : Measurable (fun p : ℝ≥0 × NeuroMV.WellPosed.Pos 1 × NeuroMV.WellPosed.Pos 1 × E1 ×
      (ℝ → E1) × Unit × ℝ => p.2.2.2.2.1) := measurable_snd.snd.snd.snd.fst
  have hy1 := hc.comp ((measurable_pi_apply (1 : ℝ)).comp hy)
  have hy2 := hc.comp ((measurable_pi_apply (2 : ℝ)).comp hy)
  unfold η0
  refine Measurable.ite ?_ (hy2.smul_const e0) measurable_const
  simp only [Set.setOf_and]
  refine (measurable_snd.fst (measurableSet_singleton _)).inter
    ((measurable_snd.snd.fst (measurableSet_singleton _)).inter ?_)
  exact measurableSet_eq_fun measurable_snd.snd.snd.snd.snd.snd hy1

noncomputable def C0 : Coeffs 1 0 0 1 1 ℝ Unit where
  f := fun _ _ _ _ => 0
  g := fun _ _ _ _ => 0
  h := fun _ _ _ _ _ => 0
  θ := fun _ _ _ _ _ _ => 0
  β := fun _ _ _ _ _ _ => 0
  η := η0

noncomputable def R0 : Rates Unit where
  lam := Measure.dirac 0
  K := fun _ _ => 0
  L := fun _ _ => 0
  Kb := fun _ _ => 0
  Lb := fun _ _ => 0
  Kt := fun _ _ _ => 0

def 𝒜0 (N : ℕ) : Finset ℕ := Finset.range N

def S0 (N : ℕ) (_ : Fin 1) : ℝ := (N : ℝ) + 1

def Q0 : Partitions 1 1 where
  M := fun _ _ => 1
  part := fun _ _ _ => Metric.ball 0 2

lemma nbr0 (N : ℕ) (α : Fin 1) : nbr pos0 𝒜0 N (G0.Γα α) = Finset.range N := by
  ext i
  unfold nbr
  simp only [Finset.mem_filter, 𝒜0, Finset.mem_range]
  exact ⟨fun h => h.1, fun h => ⟨h, pos0_mem i⟩⟩

lemma cnt0 (N : ℕ) (α : Fin 1) : cnt pos0 𝒜0 N (G0.Γα α) = N := by
  simp [cnt, nbr0]

lemma rate0 : NeuroMV.WellPosed.IsRate (fun (_ : ℝ≥0) (_ : Unit) => (0 : ℝ)) :=
  ⟨fun _ _ => le_rfl, measurable_const, fun _ _ => intervalIntegrable_const⟩

lemma C0_regular : C0.Regular :=
  ⟨measurable_const, fun _ _ => measurable_const, measurable_const, measurable_const,
    fun _ _ => measurable_const, η0_meas, fun _ _ _ => continuous_const,
    fun _ _ _ => continuous_const, fun _ _ _ _ => continuous_const,
    fun _ _ _ _ _ => continuous_const, fun _ _ _ _ _ => continuous_const,
    fun _ _ _ _ _ _ => continuous_const⟩

lemma hyp0 : Hyp G0 ν0 C0 R0 := by
  refine ⟨C0_regular, ?_, ?_, rate0, rate0, rate0, rate0, fun _ _ => rate0, ?_, ?_, ?_, ?_, ?_⟩
  · show IsProbabilityMeasure (Measure.dirac (0 : ℝ)); infer_instance
  · show Measure.dirac (0 : ℝ) (Set.Icc (-1) 0)ᶜ = 0
    rw [Measure.dirac_apply' _ measurableSet_Icc.compl]; simp
  · intro t r _ x x' ω'; simp [C0, R0, frob2]
  · intro t r _ x ω'; simp [C0, R0, frob2]
  · intro t r _ ω' Rr _ x _; simp [C0, R0, frob2]
  · intro t r _ r' _ x x' y y' ω' _ _; simp [C0, R0, frob2, lint_η0_diff]
  · intro t r _ r' _ x y ω' _; simp [C0, R0, frob2, lint_η0]

lemma h6 : H6 G0 R0 pos0 𝒜0 S0 (Measure.dirac ()) := by
  refine ⟨⟨1, ?_⟩, fun T _ => by simp [R0]⟩
  rintro _ ⟨N, rfl⟩
  simp only [sqSum, Fin.sum_univ_one, cnt0]
  show (N : ℝ) ^ 2 / ((N : ℝ) + 1) ^ 2 ≤ 1
  rw [div_le_one (by positivity)]
  nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]

lemma hyp16 : Hyp16 G0 ν0 C0 R0 pos0 𝒜0 S0 (Measure.dirac ()) Q0 := by
  refine ⟨⟨hyp0, h6⟩, fun α => tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop, ?_⟩
  intro ε _ α
  refine ⟨fun _ => Metric.isOpen_ball.measurableSet, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    exact absurd (Fin.ext (by have ha := a.isLt; have hb := b.isLt; simp only [Q0] at ha hb; omega)) hab
  · ext x; simp only [Set.mem_iUnion]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨⟨0, by simp [Q0]⟩, h⟩⟩
  · intro m
    have h1 : (G0.𝓡 (Q0.part ε α m)).toReal = 1 := by
      show (Measure.dirac (0 : NeuroMV.WellPosed.Pos 1) (Metric.ball 0 2)).toReal = 1
      rw [Measure.dirac_apply_of_mem (Metric.mem_ball_self (by norm_num))]; simp
    rw [h1]
    have h2 : (fun N => (cnt pos0 𝒜0 N (Q0.part ε α m) : ℝ) / S0 N α) =
        fun N : ℕ => (N : ℝ) / ((N : ℝ) + 1) := by
      funext N; rw [show Q0.part ε α m = G0.Γα α from rfl, cnt0]; rfl
    rw [h2]; exact tendsto_natCast_div_add_atTop 1
  · intro m r _ r' _ t x x' ω'; simp [C0, R0, frob2]
  · intro m r _ rt _ α' m' r' _ rt' _ t x xt y yt ω' _ _
    simp [C0, R0, frob2, lint_η0_diff]

/-! ### Generic helpers -/

lemma cadlag_const {E : Type*} [TopologicalSpace E] (c : E) (a b : ℝ) :
    NeuroMV.Chaos.IsCadlagOn a b (fun _ : ℝ => c) :=
  ⟨fun _ _ => continuousWithinAt_const, fun _ _ => ⟨c, tendsto_const_nhds⟩⟩

lemma tim_of_eventually {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) {l : Filter ι}
    (f : ι → Ω → ℝ) (g : Ω → ℝ) (h : ∀ᶠ k in l, ∀ ω, f k ω = g ω) : TendstoInMeasure P f l g := by
  intro ε hε
  apply tendsto_const_nhds.congr'
  filter_upwards [h] with k hk
  have : {x | ε ≤ edist (f k x) (g x)} = ∅ := by
    ext x
    simp only [hk x, edist_self, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
    exact hε
  rw [this, measure_empty]

lemma compInt_zero {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] (P : Measure Ω)
    (lam : Measure E) (N : Ω → Set (ℝ≥0 × E)) (H : Ω → ℝ≥0 → E → ℝ)
    (hH : ∀ ω s ξ, H ω s ξ = 0) :
    JacodTodorov10.LLN.HasCompInt P lam N H (fun _ _ => 0) := by
  intro t
  refine ⟨fun k => ae_of_all _ (fun ω => ?_), ?_⟩
  · have : ∀ p : ℝ≥0 × E, ¬ (1 / ((k : ℝ) + 1) < |H ω p.1 p.2|) := fun p => by
      rw [hH, abs_zero]; exact not_lt.mpr (by positivity)
    exact Set.Finite.subset Set.finite_empty (fun p hp => this p hp.2.2)
  · apply tim_of_eventually
    exact Eventually.of_forall fun k ω => by simp [JacodTodorov10.LLN.compSum, hH]

lemma indep_comap_subsingleton {Ω β : Type*} [MeasurableSpace Ω] [mβ : MeasurableSpace β]
    [Subsingleton β] (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → β)
    (m : MeasurableSpace Ω) : Indep (MeasurableSpace.comap f mβ) m μ := by
  refine indep_of_indep_of_le_left (indep_bot_left m) ?_
  rintro s ⟨t, -, rfl⟩
  rcases t.eq_empty_or_nonempty with rfl | ⟨y, hy⟩
  · simp
  · have : t = Set.univ := Set.eq_univ_of_forall (fun x => Subsingleton.elim y x ▸ hy)
    rw [this, Set.preimage_univ]; exact MeasurableSet.univ

lemma iIndepFun_const' {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {β : ι → Type*} [∀ i, MeasurableSpace (β i)] (c : ∀ i, β i) :
    iIndepFun (fun i (_ : Ω) => c i) μ := by
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets _
  by_cases h : ∀ i ∈ S, c i ∈ sets i
  · have h1 : (⋂ i ∈ S, (fun _ : Ω => c i) ⁻¹' sets i) = Set.univ := by
      ext ω; simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_univ, iff_true]; exact h
    have h2 : ∀ i ∈ S, μ ((fun _ : Ω => c i) ⁻¹' sets i) = 1 := by
      intro i hi
      have : (fun _ : Ω => c i) ⁻¹' sets i = Set.univ := by
        ext ω; simp only [Set.mem_preimage, Set.mem_univ, iff_true]; exact h i hi
      rw [this, measure_univ]
    rw [h1, Finset.prod_eq_one h2, measure_univ]
  · push_neg at h
    obtain ⟨i, hi, hc⟩ := h
    have h1 : (fun _ : Ω => c i) ⁻¹' sets i = ∅ := by
      ext ω; simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]; exact hc
    rw [Finset.prod_eq_zero hi (by rw [h1, measure_empty])]
    exact measure_mono_null (Set.biInter_subset_of_mem hi) (by rw [h1, measure_empty])

lemma identDistrib_const' {α α' β : Type*} [MeasurableSpace α] [MeasurableSpace α']
    [MeasurableSpace β] {μ : Measure α} {μ' : Measure α'} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ'] (c : β) :
    IdentDistrib (fun _ : α => c) (fun _ : α' => c) μ μ' :=
  ⟨aemeasurable_const, aemeasurable_const, by
    rw [Measure.map_const, Measure.map_const, measure_univ, measure_univ]⟩

lemma sb0 {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] :
    EthierKurtz.IsStandardBrownian Pr (fun _ _ => (0 : EthierKurtz.SDEState 0)) :=
  ⟨fun _ => measurable_const, fun _ => continuous_const, fun i => i.elim0,
    iIndepFun.of_subsingleton⟩

lemma seg_zero {Ω : Type*} (t : ℝ) (ω : Ω) :
    seg (fun (_ : ℝ) (_ : Ω) => (0 : E1)) t ω = 0 := by
  funext w; exact leftLim_eq_of_tendsto tendsto_const_nhds

lemma lebPos_Icc01 : 1 ≤ JacodTodorov10.LLN.lebPos (Set.Icc (0 : ℝ≥0) 1) := by
  have h : JacodTodorov10.LLN.lebPos (Set.Ioc (0 : ℝ≥0) 1) = 1 := by
    unfold JacodTodorov10.LLN.lebPos
    rw [NNReal.isClosedEmbedding_coe.measurableEmbedding.comap_apply]
    have : ((↑) : ℝ≥0 → ℝ) '' Set.Ioc 0 1 = Set.Ioc ((0 : ℝ≥0) : ℝ) ((1 : ℝ≥0) : ℝ) :=
      NNReal.image_coe_Ioc 0 1
    erw [this]
    rw [Real.volume_Ioc]; simp
  rw [← h]; exact measure_mono Set.Ioc_subset_Icc_self

/-- A zero solution of the jump Itô equation (all integrands vanish). -/
lemma jump_zero {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω)
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (W : ℝ≥0 → Ω → EthierKurtz.SDEState 0)
    (B : Fin 1 → ℝ≥0 → Ω → EthierKurtz.SDEState 0) (N0 : Ω → Set (ℝ≥0 × ℝ))
    (Nα : Fin 1 → Ω → Set (ℝ≥0 × ℝ)) (a : ℝ≥0 → Ω → E1)
    (G : ℝ≥0 → Ω → Matrix (Fin 1) (Fin 0) ℝ) (H : ℝ≥0 → Ω → ℝ → E1)
    (Gα : Fin 1 → ℝ≥0 → Ω → Matrix (Fin 1) (Fin 0) ℝ) (Hα : Fin 1 → ℝ≥0 → Ω → ℝ → E1)
    (ha : ∀ s ω, a s ω = 0) (hH : ∀ s ω ξ, H s ω ξ = 0) (hHα : ∀ α s ω ξ, Hα α s ω ξ = 0) :
    IsJumpItoSol Pr 𝓕 ν0 1 1 W B N0 Nα (fun _ _ => 0) a G H Gα Hα (fun _ _ => 0) := by
  refine ⟨fun _ _ _ => rfl, fun _ => cadlag_const _ _ _, fun _ _ => measurable_const,
    fun _ j => j.elim0, fun _ _ _ => 0, fun _ _ j => j.elim0, fun _ _ _ _ => 0,
    fun _ j => j.elim0, fun i => ?_, fun _ _ j => j.elim0, fun α i => ?_, fun ω i => ?_,
    fun t _ => ae_of_all _ fun ω i => ?_⟩
  · exact compInt_zero _ _ _ _ (fun ω s ξ => by simp [hH, cut])
  · exact compInt_zero _ _ _ _ (fun ω s ξ => by simp [hHα, cut])
  · have : (fun s : ℝ => a s.toNNReal ω i) = fun _ => 0 := funext fun s => by simp [ha]
    rw [this]; exact intervalIntegrable_const
  · simp [ha]

/-! ### The network path of neuron 0 -/

section Net

variable {Ω : Type} [MeasurableSpace Ω] (Nall : Ω → Set (ℝ≥0 × ((ℕ × Option (Fin 1)) × ℝ)))

def c0 : ℕ × Option (Fin 1) := (0, some 0)

def sl (ω : Ω) : Set (ℝ≥0 × ℝ) := markSlice Nall c0 ω

def A (ω : Ω) : Set (ℝ≥0 × ℝ) := {p | p ∈ sl Nall ω ∧ p.1 ≤ 1}

open Classical in
noncomputable def Fs (ω : Ω) : Finset (ℝ≥0 × ℝ) :=
  if h : (A Nall ω).Finite then h.toFinset else ∅

lemma mem_A_of_Fs {ω : Ω} {p : ℝ≥0 × ℝ} (h : p ∈ Fs Nall ω) : p ∈ A Nall ω := by
  unfold Fs at h
  split_ifs at h with hA
  · exact hA.mem_toFinset.1 h
  · simp at h

lemma mem_Fs {ω : Ω} {p : ℝ≥0 × ℝ} (hA : (A Nall ω).Finite) (h : p ∈ A Nall ω) :
    p ∈ Fs Nall ω := by
  unfold Fs; rw [dif_pos hA]; exact hA.mem_toFinset.2 h

noncomputable def K (ω : Ω) (v : ℝ) : ℝ :=
  ∑ p ∈ Fs Nall ω, if (p.1 : ℝ) ≤ v then (1 : ℝ) else 0

noncomputable def Ts (ω : Ω) : Set ℝ :=
  (fun p : ℝ≥0 × ℝ => (p.1 : ℝ)) '' (Fs Nall ω : Set (ℝ≥0 × ℝ))

noncomputable def nextT (ω : Ω) (u : ℝ) : ℝ := sInf {s | s ∈ Ts Nall ω ∧ u ≤ s}

open Classical in
noncomputable def mk (ω : Ω) (u : ℝ) : ℝ :=
  if h : ∃ p, p ∈ sl Nall ω ∧ (p.1 : ℝ) = u then (Classical.choose h).2 else 0

noncomputable def path (N : ℕ) (ω : Ω) (v : ℝ) : E1 :=
  if v ≤ 1 then K Nall ω v • e0
  else if v ≤ 2 then mk Nall ω (nextT Nall ω (v - 1)) • e0 else ((N : ℝ) + 1) • e0

noncomputable def XN0 (N : ℕ) (_ : Unit) (i : ℕ) (v : ℝ) (ω : Ω) : E1 :=
  if i = 0 then path Nall N ω v else 0

lemma XN0_zero (N : ℕ) (u : Unit) : XN0 Nall N u 0 = fun v ω => path Nall N ω v := by
  funext v ω; simp [XN0]

lemma XN0_ne (N : ℕ) (u : Unit) {i : ℕ} (hi : i ≠ 0) : XN0 Nall N u i = fun _ _ => 0 := by
  funext v ω; simp [XN0, hi]

variable {Nall}

lemma A_finite (hfin : ∀ ω t c, {z | z ∈ Nall ω ∧ z.1 ≤ t ∧ z.2.1 = c}.Finite) (ω : Ω) :
    (A Nall ω).Finite :=
  ((hfin ω 1 c0).image (fun z => (z.1, z.2.2))).subset (by
    rintro ⟨a, b⟩ ⟨hp, ha⟩
    exact ⟨(a, (c0, b)), ⟨hp, ha, rfl⟩, rfl⟩)

lemma slice_finite (hfin : ∀ ω t c, {z | z ∈ Nall ω ∧ z.1 ≤ t ∧ z.2.1 = c}.Finite) (ω : Ω)
    (t : ℝ≥0) (c : ℕ × Option (Fin 1)) :
    {p : ℝ≥0 × ℝ | p ∈ markSlice Nall c ω ∧ p.1 ≤ t}.Finite :=
  ((hfin ω t c).image (fun z => (z.1, z.2.2))).subset (by
    rintro ⟨a, b⟩ ⟨hp, ha⟩
    exact ⟨(a, (c, b)), ⟨hp, ha, rfl⟩, rfl⟩)

lemma K_nonpos (hpos : ∀ ω z, z ∈ Nall ω → 0 < z.1) (ω : Ω) {v : ℝ} (hv : v ≤ 0) :
    K Nall ω v = 0 := by
  refine Finset.sum_eq_zero (fun p hp => ?_)
  have h1 : 0 < p.1 := hpos ω _ (mem_A_of_Fs Nall hp).1
  have h2 : (0 : ℝ) < p.1 := by exact_mod_cast h1
  rw [if_neg (by linarith)]

lemma K_card (ω : Ω) (v : ℝ) :
    K Nall ω v = ((Fs Nall ω).filter (fun p => (p.1 : ℝ) ≤ v)).card := by
  unfold K; rw [Finset.sum_boole]

lemma cnt_card (hfin : ∀ ω t c, {z | z ∈ Nall ω ∧ z.1 ≤ t ∧ z.2.1 = c}.Finite) (ω : Ω)
    (t : ℝ≥0) (ht : t ≤ 1) :
    JacodTodorov10.LLN.cnt Nall ω (Set.Icc 0 t ×ˢ ({c0} ×ˢ Set.univ)) =
      (((Fs Nall ω).filter (fun p => (p.1 : ℝ) ≤ t)).card : ℝ≥0∞) := by
  have hA := A_finite hfin ω
  have hinj : Function.Injective (fun q : ℝ≥0 × ℝ => (q.1, (c0, q.2))) := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    simp only [Prod.mk.injEq] at h
    rw [h.1, h.2.2]
  have h2 : Nall ω ∩ (Set.Icc 0 t ×ˢ ({c0} ×ˢ Set.univ)) =
      (fun q : ℝ≥0 × ℝ => (q.1, (c0, q.2))) ''
        ↑((Fs Nall ω).filter (fun p => (p.1 : ℝ) ≤ t)) := by
    ext ⟨a, c, b⟩
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_Icc, Set.mem_singleton_iff,
      Set.mem_univ, and_true, Finset.coe_filter, Set.mem_image, Set.mem_setOf_eq,
      Prod.mk.injEq, NNReal.coe_le_coe]
    constructor
    · rintro ⟨hN, ⟨-, hat⟩, rfl⟩
      exact ⟨(a, b), ⟨mem_Fs Nall hA ⟨hN, hat.trans ht⟩, hat⟩, rfl, rfl, rfl⟩
    · rintro ⟨⟨a', b'⟩, ⟨hF, ha'⟩, rfl, rfl, rfl⟩
      exact ⟨(mem_A_of_Fs Nall hF).1, ⟨zero_le, ha'⟩, rfl⟩
  unfold JacodTodorov10.LLN.cnt
  rw [h2, hinj.encard_image, Set.encard_coe_eq_coe_finsetCard]
  simp

/-! #### càdlàg -/

lemma ind_rc (c t : ℝ) :
    ContinuousWithinAt (fun v : ℝ => if c ≤ v then (1 : ℝ) else 0) (Set.Ici t) t := by
  by_cases h : c ≤ t
  · have : ∀ᶠ v in 𝓝[Set.Ici t] t, (1 : ℝ) = (fun v : ℝ => if c ≤ v then (1 : ℝ) else 0) v := by
      filter_upwards [self_mem_nhdsWithin] with v hv
      simp [h.trans hv]
    show Tendsto _ _ (𝓝 (if c ≤ t then (1 : ℝ) else 0))
    rw [if_pos h]; exact tendsto_const_nhds.congr' this
  · push_neg at h
    have : ∀ᶠ v in 𝓝[Set.Ici t] t, (0 : ℝ) = (fun v : ℝ => if c ≤ v then (1 : ℝ) else 0) v := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds h)] with v hv
      simp [not_le.mpr (show v < c from hv)]
    show Tendsto _ _ (𝓝 (if c ≤ t then (1 : ℝ) else 0))
    rw [if_neg (not_le.mpr h)]; exact tendsto_const_nhds.congr' this

lemma ind_ll (c t : ℝ) :
    ∃ l, Tendsto (fun v : ℝ => if c ≤ v then (1 : ℝ) else 0) (𝓝[<] t) (𝓝 l) := by
  by_cases h : c < t
  · refine ⟨1, tendsto_const_nhds.congr' ?_⟩
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds h)] with v hv
    simp [le_of_lt (show c < v from hv)]
  · push_neg at h
    refine ⟨0, tendsto_const_nhds.congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin] with v hv
    simp [not_le.mpr (lt_of_lt_of_le (show v < t from hv) h)]

lemma K_rc (ω : Ω) (t : ℝ) : ContinuousWithinAt (K Nall ω) (Set.Ici t) t := by
  show Tendsto (fun v => ∑ p ∈ Fs Nall ω, if (p.1 : ℝ) ≤ v then (1 : ℝ) else 0) (𝓝[Set.Ici t] t)
    (𝓝 (∑ p ∈ Fs Nall ω, if (p.1 : ℝ) ≤ t then (1 : ℝ) else 0))
  exact tendsto_finset_sum _ fun p _ => ind_rc (p.1 : ℝ) t

lemma K_ll (ω : Ω) (t : ℝ) : ∃ l, Tendsto (K Nall ω) (𝓝[<] t) (𝓝 l) := by
  choose l hl using fun p : ℝ≥0 × ℝ => ind_ll (p.1 : ℝ) t
  exact ⟨∑ p ∈ Fs Nall ω, l p, tendsto_finset_sum _ fun p _ => hl p⟩

lemma path_cadlag (N : ℕ) (ω : Ω) :
    NeuroMV.Chaos.IsCadlagOn (-1) 1 (fun t => path Nall N ω t) := by
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · have h : ContinuousWithinAt (fun v => K Nall ω v • e0) (Set.Icc t 1) t :=
      ((K_rc (Nall := Nall) ω t).mono (fun v hv => hv.1 : Set.Icc t 1 ⊆ Set.Ici t)).smul
        (continuousWithinAt_const (b := e0))
    refine h.congr (fun v hv => ?_) ?_
    · simp [path, hv.2]
    · simp [path, ht.2.le]
  · obtain ⟨l, hl⟩ := K_ll (Nall := Nall) ω t
    refine ⟨l • e0, (hl.smul_const e0).congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin] with v hv
    simp [path, (le_of_lt (show v < t from hv)).trans ht.2]

/-! #### left limits beyond T -/

lemma mk_atom (hsub : ∀ ω t, {z | (t, z) ∈ Nall ω}.Subsingleton) {ω : Ω} {p : ℝ≥0 × ℝ}
    (hp : p ∈ sl Nall ω) : mk Nall ω p.1 = p.2 := by
  have h : ∃ q, q ∈ sl Nall ω ∧ (q.1 : ℝ) = p.1 := ⟨p, hp, rfl⟩
  unfold mk; rw [dif_pos h]
  have hs := Classical.choose_spec h
  generalize Classical.choose h = q at hs ⊢
  obtain ⟨hq, hqt⟩ := hs
  have ht : q.1 = p.1 := NNReal.coe_injective hqt
  have hq' : (p.1, (c0, q.2)) ∈ Nall ω := by rw [← ht]; exact hq
  have := hsub ω p.1 (show (c0, q.2) ∈ {z | (p.1, z) ∈ Nall ω} from hq')
    (show (c0, p.2) ∈ {z | (p.1, z) ∈ Nall ω} from hp)
  exact (Prod.mk.inj this).2

lemma ll_one (hsub : ∀ ω t, {z | (t, z) ∈ Nall ω}.Subsingleton)
    (hfin : ∀ ω t c, {z | z ∈ Nall ω ∧ z.1 ≤ t ∧ z.2.1 = c}.Finite) (N : ℕ) {ω : Ω}
    {p : ℝ≥0 × ℝ} (hp : p ∈ sl Nall ω) (hp0 : 0 < p.1) (hp1 : p.1 ≤ 1) :
    Function.leftLim (fun v => path Nall N ω v) ((p.1 : ℝ) + 1) = p.2 • e0 := by
  have hA := A_finite hfin ω
  have hpF : p ∈ Fs Nall ω := mem_Fs Nall hA ⟨hp, hp1⟩
  have hp0' : (0 : ℝ) < p.1 := by exact_mod_cast hp0
  have hp1' : (p.1 : ℝ) ≤ 1 := by exact_mod_cast hp1
  apply leftLim_eq_of_tendsto
  apply tendsto_const_nhds.congr'
  have E3 : ∀ᶠ v in 𝓝[<] ((p.1 : ℝ) + 1),
      ∀ q ∈ Fs Nall ω, (q.1 : ℝ) < p.1 → (q.1 : ℝ) + 1 < v := by
    rw [Filter.eventually_all_finset]
    intro q _
    by_cases hq : (q.1 : ℝ) < p.1
    · filter_upwards [mem_nhdsWithin_of_mem_nhds
        (Ioi_mem_nhds (show (q.1 : ℝ) + 1 < p.1 + 1 by linarith))] with v hv _ using hv
    · exact Filter.Eventually.of_forall (fun v h => absurd h hq)
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
    (Ioi_mem_nhds (show (1 : ℝ) < p.1 + 1 by linarith)), E3] with v hv1 hv2 hv3
  have hv1' : v < p.1 + 1 := hv1
  have hv2' : 1 < v := hv2
  have hnext : nextT Nall ω (v - 1) = p.1 := by
    apply IsLeast.csInf_eq
    refine ⟨⟨⟨p, hpF, rfl⟩, by linarith⟩, ?_⟩
    rintro s ⟨⟨q, hqF, rfl⟩, hqs⟩
    by_contra hlt
    push_neg at hlt
    have := hv3 q hqF hlt
    linarith
  have hmk : mk Nall ω p.1 = p.2 := mk_atom hsub hp
  simp only [path, if_neg (not_le.mpr hv2'), if_pos (show v ≤ 2 by linarith), hnext, hmk]

lemma ll_two (N : ℕ) (ω : Ω) {s : ℝ} (hs : 0 < s) :
    Function.leftLim (fun v => path Nall N ω v) (s + 2) = ((N : ℝ) + 1) • e0 := by
  apply leftLim_eq_of_tendsto
  apply tendsto_const_nhds.congr'
  filter_upwards [mem_nhdsWithin_of_mem_nhds
    (Ioi_mem_nhds (show (2 : ℝ) < s + 2 by linarith))] with v hv
  have h2 : (2 : ℝ) < v := hv
  simp [path, not_le.mpr h2, not_le.mpr (show (1 : ℝ) < v by linarith)]

/-! #### the jump integrand of neuron 0 -/

lemma netη_eq {Y : ℕ → ℝ → Ω → E1} {N : ℕ} (hN : 0 < N) (α : Fin 1) (s : ℝ≥0)
    (r : NeuroMV.WellPosed.Pos 1) (x : E1) (ω : Ω) (u : Unit) (ξ : ℝ) :
    netη G0 C0 pos0 𝒜0 S0 Y N α s r x ω u ξ =
      ((N : ℝ) + 1)⁻¹ • η0 s r (pos0 0) x (seg (Y 0) s ω) u ξ := by
  unfold netη
  rw [nbr0, Finset.sum_eq_single 0]
  · rfl
  · intro b _ hb
    show η0 s r (pos0 b) x (seg (Y b) s ω) u ξ = 0
    exact η0_eq_zero_of_r' (fun h => hb (pos0_inj h))
  · intro h; exact absurd (Finset.mem_range.2 hN) h

variable (Nall) in
noncomputable def H0 (N : ℕ) (u : Unit) (α i : Fin 1) (ω : Ω) (s : ℝ≥0) (ξ : ℝ) : ℝ :=
  cut 1 s ((netη G0 C0 pos0 𝒜0 S0 (XN0 Nall N u) N α s (pos0 0)
    (lft (XN0 Nall N u 0) s ω) ω u ξ) i)

lemma H0_zero {N : ℕ} (hN : 0 < N) (u : Unit) (α i : Fin 1) (ω : Ω) (s : ℝ≥0) {ξ : ℝ}
    (hξ : ξ ≠ seg (XN0 Nall N u 0) s ω 1 0) : H0 Nall N u α i ω s ξ = 0 := by
  unfold H0
  rw [netη_eq hN, η0_eq_zero_of_ne hξ, smul_zero]
  simp [cut]

lemma H0_atom (hsub : ∀ ω t, {z | (t, z) ∈ Nall ω}.Subsingleton)
    (hfin : ∀ ω t c, {z | z ∈ Nall ω ∧ z.1 ≤ t ∧ z.2.1 = c}.Finite) {N : ℕ} (hN : 0 < N)
    (u : Unit) (α i : Fin 1) {ω : Ω} {p : ℝ≥0 × ℝ} (hp : p ∈ sl Nall ω) (hp0 : 0 < p.1)
    (hp1 : p.1 ≤ 1) : H0 Nall N u α i ω p.1 p.2 = 1 := by
  unfold H0
  rw [netη_eq hN]
  have hp0' : (0 : ℝ) < p.1 := by exact_mod_cast hp0
  have h1 : seg (XN0 Nall N u 0) p.1 ω 1 = p.2 • e0 := by
    rw [XN0_zero]; exact ll_one hsub hfin N hp hp0 hp1
  have h2 : seg (XN0 Nall N u 0) p.1 ω 2 = ((N : ℝ) + 1) • e0 := by
    rw [XN0_zero]; exact ll_two N ω hp0'
  have h3 : η0 p.1 (pos0 0) (pos0 0) (lft (XN0 Nall N u 0) p.1 ω)
      (seg (XN0 Nall N u 0) p.1 ω) u p.2 = ((N : ℝ) + 1) • e0 := by
    simp only [η0, h1, h2, smul_e0_apply]; simp
  rw [h3, smul_smul, inv_mul_cancel₀ (by positivity), one_smul, e0_apply]
  have hp1' : (p.1 : ℝ) ≤ 1 := by exact_mod_cast hp1
  simp [cut, hp1']

lemma hasCompInt_n0 (hsub : ∀ ω t, {z | (t, z) ∈ Nall ω}.Subsingleton)
    (hfin : ∀ ω t c, {z | z ∈ Nall ω ∧ z.1 ≤ t ∧ z.2.1 = c}.Finite)
    (hpos : ∀ ω z, z ∈ Nall ω → 0 < z.1) (Pr : Measure Ω) {N : ℕ} (hN : 0 < N) (u : Unit)
    (α i : Fin 1) :
    JacodTodorov10.LLN.HasCompInt Pr ν0 (markSlice Nall (0, some α)) (H0 Nall N u α i)
      (fun t ω => K Nall ω (min (t : ℝ) 1)) := by
  obtain rfl : α = 0 := Subsingleton.elim _ _
  intro t
  refine ⟨fun k => ae_of_all _ (fun ω => ?_), ?_⟩
  · exact (slice_finite hfin ω t (0, some 0)).subset (fun p hp => ⟨hp.1, hp.2.1⟩)
  apply tim_of_eventually
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with k hk ω
  unfold JacodTodorov10.LLN.compSum
  have hcomp : ∀ s : ℝ, ∫ z, (if 1 / (k + 1) < |H0 Nall N u 0 i ω s.toNNReal z|
      then H0 Nall N u 0 i ω s.toNNReal z else 0) ∂ν0 = 0 := by
    intro s
    apply integral_eq_zero_of_ae
    filter_upwards [ae_ne0 (seg (XN0 Nall N u 0) s.toNNReal ω 1 0)] with z hz
    rw [H0_zero hN u 0 i ω s.toNNReal hz]; simp
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun s _ => hcomp s),
    intervalIntegral.integral_zero, sub_zero]
  have hkpos : (0 : ℝ) < 1 / (k + 1) := div_pos one_pos (by linarith)
  have hε : 1 / (k + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hA := A_finite hfin ω
  have hset : {p : ℝ≥0 × ℝ | p ∈ markSlice Nall (0, some 0) ω ∧ p.1 ≤ t ∧
      1 / (k + 1) < |H0 Nall N u 0 i ω p.1 p.2|} =
      ↑((Fs Nall ω).filter (fun p => (p.1 : ℝ) ≤ t)) := by
    ext p
    simp only [Set.mem_setOf_eq, Finset.coe_filter, NNReal.coe_le_coe]
    constructor
    · rintro ⟨hp, hpt, hH⟩
      have hp1 : p.1 ≤ 1 := by
        by_contra h
        push_neg at h
        have h0 : H0 Nall N u 0 i ω p.1 p.2 = 0 := by
          unfold H0 cut
          rw [if_neg (not_le.mpr (by exact_mod_cast h))]
        rw [h0, abs_zero] at hH
        linarith
      exact ⟨mem_Fs Nall hA ⟨hp, hp1⟩, hpt⟩
    · rintro ⟨hF, hpt⟩
      obtain ⟨hp, hp1⟩ := mem_A_of_Fs Nall hF
      refine ⟨hp, hpt, ?_⟩
      rw [H0_atom hsub hfin hN u 0 i hp (hpos ω _ hp) hp1, abs_one]
      exact hε
  rw [hset, finsum_mem_coe_finset]
  rw [Finset.sum_congr rfl (fun p hp => H0_atom hsub hfin hN u 0 i
    (mem_A_of_Fs Nall (Finset.mem_filter.1 hp).1).1
    (hpos ω _ (mem_A_of_Fs Nall (Finset.mem_filter.1 hp).1).1)
    (mem_A_of_Fs Nall (Finset.mem_filter.1 hp).1).2)]
  rw [K_card, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 2
  apply Finset.filter_congr
  intro p hp
  have hp1 : (p.1 : ℝ) ≤ 1 := by exact_mod_cast (mem_A_of_Fs Nall hp).2
  rw [le_min_iff]
  exact ⟨fun h => ⟨h, hp1⟩, fun h => h.1⟩

lemma path_meas (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (Pr : Measure Ω)
    (hP : JacodTodorov10.LLN.IsFPoisson 𝓕 Pr (Measure.count.prod ν0) Nall)
    (hfin : ∀ ω t c, {z | z ∈ Nall ω ∧ z.1 ≤ t ∧ z.2.1 = c}.Finite) (N : ℕ) (t : ℝ≥0)
    (ht : (t : ℝ) ≤ 1) : Measurable[𝓕 t] (fun ω => path Nall N ω t) := by
  have ht' : t ≤ 1 := by exact_mod_cast ht
  have : (fun ω => path Nall N ω t) = fun ω =>
      (JacodTodorov10.LLN.cnt Nall ω (Set.Icc 0 t ×ˢ ({c0} ×ˢ Set.univ))).toReal • e0 := by
    funext ω
    rw [path, if_pos ht, cnt_card hfin ω t ht', K_card]
    simp
  rw [this]
  exact ((hP.2.2.1 t _ ((measurableSet_singleton c0).prod MeasurableSet.univ)).ennreal_toReal).smul_const e0

lemma moment (Pr : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (hP : JacodTodorov10.LLN.IsFPoisson 𝓕 Pr (Measure.count.prod ν0) Nall)
    (hfin : ∀ ω t c, {z | z ∈ Nall ω ∧ z.1 ≤ t ∧ z.2.1 = c}.Finite) (N : ℕ) :
    1 ≤ ∫⁻ ω, ‖path Nall N ω 1‖ₑ ^ 2 ∂Pr := by
  have hB : MeasurableSet (Set.Icc (0 : ℝ≥0) 1 ×ˢ ({c0} ×ˢ (Set.univ : Set ℝ))) :=
    measurableSet_Icc.prod ((measurableSet_singleton c0).prod MeasurableSet.univ)
  have hpt : ∀ ω, JacodTodorov10.LLN.cnt Nall ω (Set.Icc 0 1 ×ˢ ({c0} ×ˢ Set.univ)) ≤
      ‖path Nall N ω 1‖ₑ ^ 2 := by
    intro ω
    have h1 := cnt_card hfin ω 1 le_rfl
    have h2 := K_card (Nall := Nall) ω 1
    rw [path, if_pos le_rfl, enorm_smul_e0, h1]
    simp only [NNReal.coe_one] at h2 ⊢
    rw [h2, Real.enorm_eq_ofReal (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    exact_mod_cast Nat.le_self_pow two_ne_zero _
  calc (1 : ℝ≥0∞) ≤ (JacodTodorov10.LLN.lebPos.prod (Measure.count.prod ν0))
        (Set.Icc 0 1 ×ˢ ({c0} ×ˢ Set.univ)) := by
        rw [Measure.prod_prod, Measure.prod_prod, Measure.count_singleton, measure_univ,
          mul_one, mul_one]
        exact lebPos_Icc01
    _ = ∫⁻ ω, JacodTodorov10.LLN.cnt Nall ω (Set.Icc 0 1 ×ˢ ({c0} ×ˢ Set.univ)) ∂Pr :=
        (hP.2.2.2.1 _ hB).symm
    _ ≤ _ := lintegral_mono hpt


lemma net_sol (hsub : ∀ ω t, {z | (t, z) ∈ Nall ω}.Subsingleton)
    (hfin : ∀ ω t c, {z | z ∈ Nall ω ∧ z.1 ≤ t ∧ z.2.1 = c}.Finite)
    (hpos : ∀ ω z, z ∈ Nall ω → 0 < z.1) (Pr : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (hP : JacodTodorov10.LLN.IsFPoisson 𝓕 Pr (Measure.count.prod ν0) Nall) (N : ℕ) (u : Unit) :
    IsNetSol G0 ν0 C0 pos0 𝒜0 S0 Pr 𝓕 (fun _ _ _ => 0) (fun _ _ _ _ => 0) Nall
      (fun _ _ _ => 0) N u 1 (XN0 Nall N u) := by
  intro i hi
  have hi' : i < N := by simpa [𝒜0] using hi
  by_cases h0 : i = 0
  · subst h0
    refine ⟨fun t ht ω => ?_, fun ω => ?_, fun t ht => ?_, fun _ j => j.elim0, fun _ _ _ => 0,
      fun _ _ j => j.elim0, fun _ _ t ω => K Nall ω (min (t : ℝ) 1), fun _ j => j.elim0,
      fun i => ?_, fun _ _ j => j.elim0, fun α i => hasCompInt_n0 hsub hfin hpos Pr hi' u α i,
      fun ω i => ?_, fun t ht => ae_of_all _ fun ω i => ?_⟩
    · rw [XN0_zero]
      simp [path, ht.trans zero_le_one, K_nonpos hpos ω ht]
    · rw [XN0_zero]; exact path_cadlag N ω
    · rw [XN0_zero]; exact path_meas 𝓕 Pr hP hfin N t ht
    · exact compInt_zero _ _ _ _ (fun ω s ξ => by simp [C0, cut])
    · simp [C0, netθ]
    · rw [XN0_zero]
      simp [C0, netθ, path, ht, min_eq_left ht]
  · rw [XN0_ne Nall N u h0]
    apply jump_zero
    · intro s ω; simp [C0, netθ]
    · intro s ω ξ; simp [C0]
    · intro α s ω ξ
      unfold netη
      rw [Finset.sum_eq_zero (fun i' _ => ?_), smul_zero]
      show η0 s (pos0 i) (pos0 i') (lft (fun (_ : ℝ) (_ : Ω) => (0 : E1)) s ω)
        (seg (XN0 Nall N u i') s ω) u ξ = 0
      exact η0_eq_zero_of_r (fun h => h0 (pos0_inj h))

end Net

section Zero

variable {Ω : Type} [MeasurableSpace Ω]

lemma solX (Pr : Measure Ω) [IsProbabilityMeasure Pr] (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (NX : Ω → Set (ℝ≥0 × (Option (Fin 1) × ℝ))) (u : Unit) :
    IsStrongSol6 G0 ν0 C0 Pr 𝓕 (fun _ _ => 0) (fun _ _ _ => 0) NX (fun _ _ _ => 0) u 1
      (fun _ _ _ => 0) ∧ InClass G0 Pr 1 (fun _ _ _ => (0 : E1)) := by
  refine ⟨⟨fun t => measurable_const, fun ζ r _ => ?_⟩, ⟨0, by simp, fun t _ => by simp⟩⟩
  apply jump_zero
  · intro s ω; simp [C0, meanθ]
  · intro s ω ξ; simp [C0]
  · intro α s ω ξ; simp [meanη, C0, seg_zero, η0_zero_path]

lemma solXbar {ΩX : Type} [MeasurableSpace ΩX] (Pr : Measure Ω)
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (Nall : Ω → Set (ℝ≥0 × ((ℕ × Option (Fin 1)) × ℝ))) (PrX : Measure ΩX) (u : Unit) (i : ℕ) :
    IsLimitSol G0 ν0 C0 pos0 Pr 𝓕 (fun _ _ _ => 0) (fun _ _ _ _ => 0) Nall (fun _ _ _ => 0) PrX
      (fun _ _ _ => 0) u 1 i (fun _ _ => 0) := by
  apply jump_zero
  · intro s ω; simp [C0, meanθ]
  · intro s ω ξ; simp [C0]
  · intro α s ω ξ; simp [meanη, C0, seg_zero, η0_zero_path]

lemma fam_net (Pr : Measure Ω) [IsProbabilityMeasure Pr] (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) :
    IsFBrownianFamily Pr 𝓕 (coordsNet (fun (_ : ℕ) (_ : ℝ≥0) (_ : Ω) => (0 : EthierKurtz.SDEState 0))
      (fun (_ : ℕ) (_ : Fin 1) (_ : ℝ≥0) (_ : Ω) => (0 : EthierKurtz.SDEState 0))) :=
  ⟨fun c => isEmptyElim c, iIndepFun.of_subsingleton,
    fun _ _ _ => indep_comap_subsingleton Pr _ _⟩

lemma fam_6 (Pr : Measure Ω) [IsProbabilityMeasure Pr] (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) :
    IsFBrownianFamily Pr 𝓕 (coords6 (fun (_ : ℝ≥0) (_ : Ω) => (0 : EthierKurtz.SDEState 0))
      (fun (_ : Fin 1) (_ : ℝ≥0) (_ : Ω) => (0 : EthierKurtz.SDEState 0))) :=
  ⟨fun c => isEmptyElim c, iIndepFun.of_subsingleton,
    fun _ _ _ => indep_comap_subsingleton Pr _ _⟩

lemma init0 {ι : Type*} (Pr : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) :
    IsInit Pr 𝓕 G0.τ (fun (_ : ι) (_ : ℝ) (_ : Ω) => (0 : E1)) :=
  ⟨fun _ _ => cadlag_const _ _ _, fun _ _ _ => measurable_const, fun _ => by simp⟩

end Zero

open NeuroMV.Chaos in
theorem cex_main {Ω0 ΩX0 : Type} [MeasurableSpace Ω0] [MeasurableSpace ΩX0] (Pr0 : Measure Ω0)
    [IsProbabilityMeasure Pr0] (𝓕0 : Filtration ℝ≥0 ‹MeasurableSpace Ω0›)
    (N0 : Ω0 → Set (ℝ≥0 × ((ℕ × Option (Fin 1)) × ℝ))) (hUC : UsualConditions Pr0 𝓕0)
    (hP : JacodTodorov10.LLN.IsFPoisson 𝓕0 Pr0 (Measure.count.prod ν0) N0)
    (hfin : ∀ ω t c, {z | z ∈ N0 ω ∧ z.1 ≤ t ∧ z.2.1 = c}.Finite)
    (hpos : ∀ ω z, z ∈ N0 ω → 0 < z.1)
    (PrX0 : Measure ΩX0) [IsProbabilityMeasure PrX0] (𝓕X0 : Filtration ℝ≥0 ‹MeasurableSpace ΩX0›)
    (NX0 : ΩX0 → Set (ℝ≥0 × (Option (Fin 1) × ℝ)))
    (hPX : JacodTodorov10.LLN.IsFPoisson 𝓕X0 PrX0 (Measure.count.prod ν0) NX0) :
    ¬ (∀ {d m n k P : ℕ} {U Ω' Ω ΩX : Type} [MeasurableSpace U] [MeasurableSpace Ω']
    [MeasurableSpace Ω] [MeasurableSpace ΩX]
    (G : Geometry k P) (ν : Measure U) [SigmaFinite ν] (Pr' : Measure Ω')
    [IsProbabilityMeasure Pr'] (C : Coeffs d m n k P U Ω') (R : Rates Ω')
    (pos : ℕ → NeuroMV.WellPosed.Pos k) (𝒜 : ℕ → Finset ℕ) (S : ℕ → Fin P → ℝ) (Q : Partitions k P)
    (Pr : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (W : ℕ → ℝ≥0 → Ω → EthierKurtz.SDEState m) (B : ℕ → Fin P → ℝ≥0 → Ω → EthierKurtz.SDEState n)
    (Nall : Ω → Set (ℝ≥0 × ((ℕ × Option (Fin P)) × U))) (z : ℕ → ℝ → Ω → EthierKurtz.SDEState d)
    (PrX : Measure ΩX) (𝓕X : Filtration ℝ≥0 ‹MeasurableSpace ΩX›)
    (WX : ℝ≥0 → ΩX → EthierKurtz.SDEState m) (BX : Fin P → ℝ≥0 → ΩX → EthierKurtz.SDEState n)
    (NX : ΩX → Set (ℝ≥0 × (Option (Fin P) × U))) (zh : Fin P → ℝ → ΩX → EthierKurtz.SDEState d)
    (hG : G.Valid) (hH : Hyp16 G ν C R pos 𝒜 S Pr' Q)
    (hnet : NetSetup G ν pos 𝒜 S Pr 𝓕 W B Nall z)
    (hnoise : IsNoise6 PrX 𝓕X ν WX BX NX) (hzh : IsInit PrX 𝓕X G.τ zh)
    (hchaos : ChaoticInit G pos 𝒜 Pr z PrX zh)
    (T : ℝ) (hT : 0 < T)
    (XN : ℕ → Ω' → ℕ → ℝ → Ω → EthierKurtz.SDEState d)
    (hXN : ∀ N, ∀ᵐ ω' ∂Pr', IsNetSol G ν C pos 𝒜 S Pr 𝓕 W B Nall z N ω' T (XN N ω'))
    (X : Ω' → NeuroMV.WellPosed.Pos k → ℝ → ΩX → EthierKurtz.SDEState d)
    (hX : ∀ᵐ ω' ∂Pr', IsStrongSol6 G ν C PrX 𝓕X WX BX NX zh ω' T (X ω') ∧
      InClass G PrX T (X ω'))
    (Xbar : Ω' → ℕ → ℝ → Ω → EthierKurtz.SDEState d)
    (hXbar : ∀ᵐ ω' ∂Pr', ∀ i : ℕ, (∃ N, i ∈ 𝒜 N) →
      IsLimitSol G ν C pos Pr 𝓕 W B Nall z PrX (X ω') ω' T i (Xbar ω' i)),
    Tendsto (fun N : ℕ => ∫⁻ ω', ⨆ t ∈ Set.Icc (-G.τ) T, ⨆ i ∈ 𝒜 N,
        ∫⁻ ω, ‖XN N ω' i t ω - Xbar ω' i t ω‖ₑ ^ 2 ∂Pr ∂Pr') atTop (𝓝 0)) := by
  intro h
  have hsub : ∀ ω t, {z | (t, z) ∈ N0 ω}.Subsingleton := hP.1
  have hnet : NetSetup G0 ν0 pos0 𝒜0 S0 Pr0 𝓕0 (fun _ _ _ => 0) (fun _ _ _ _ => 0) N0
      (fun _ _ _ => 0) :=
    ⟨pos0_inj, fun N i _ => by rw [G0_Γ]; exact pos0_mem i, fun N => Finset.card_range N,
      fun N α => by show (N : ℝ) + 1 ≠ 0; positivity, inferInstance, hUC, fun _ => sb0 Pr0,
      fun _ _ => sb0 Pr0, fam_net Pr0 𝓕0, hP, init0 Pr0 𝓕0⟩
  have hnoise : IsNoise6 PrX0 𝓕X0 ν0 (fun _ _ => (0 : EthierKurtz.SDEState 0))
      (fun _ _ _ => (0 : EthierKurtz.SDEState 0)) NX0 :=
    ⟨inferInstance, sb0 PrX0, fun _ => sb0 PrX0, fam_6 PrX0 𝓕X0, hPX⟩
  have hchaos : ChaoticInit G0 pos0 𝒜0 Pr0 (fun _ _ _ => (0 : E1)) PrX0
      (fun _ _ _ => (0 : E1)) :=
    ⟨iIndepFun_const' (Ω := Ω0) (β := fun _ : {i // ∃ N, i ∈ 𝒜0 N} => Set.Icc (-G0.τ) 0 → E1)
      (fun _ _ => 0), fun i _ α _ => identDistrib_const' (fun _ => (0 : E1))⟩
  have hlim := h (d := 1) (m := 0) (n := 0) (k := 1) (P := 1) (U := ℝ) (Ω' := Unit) (Ω := Ω0)
    (ΩX := ΩX0) G0 ν0 (Measure.dirac ()) C0 R0 pos0 𝒜0 S0 Q0 Pr0 𝓕0 (fun _ _ _ => 0)
    (fun _ _ _ _ => 0) N0 (fun _ _ _ => 0) PrX0 𝓕X0 (fun _ _ => 0) (fun _ _ _ => 0) NX0
    (fun _ _ _ => 0) G0_valid hyp16 hnet hnoise (init0 PrX0 𝓕X0) hchaos 1 one_pos (XN0 N0)
    (fun N => ae_of_all _ fun u => net_sol hsub hfin hpos Pr0 𝓕0 hP N u)
    (fun _ _ _ _ => 0) (ae_of_all _ fun u => solX PrX0 𝓕X0 NX0 u) (fun _ _ _ _ => 0)
    (ae_of_all _ fun u i _ => solXbar Pr0 𝓕0 N0 PrX0 u i)
  have hge : ∀ N : ℕ, 1 ≤ N → (1 : ℝ≥0∞) ≤ ∫⁻ ω', ⨆ t ∈ Set.Icc (-G0.τ) 1, ⨆ i ∈ 𝒜0 N,
      ∫⁻ ω, ‖XN0 N0 N ω' i t ω - (fun _ _ _ _ => (0 : E1)) ω' i t ω‖ₑ ^ 2 ∂Pr0 ∂(Measure.dirac ()) := by
    intro N hN
    rw [lintegral_dirac]
    refine le_trans ?_ (le_iSup₂_of_le (1 : ℝ) ⟨by show (-1 : ℝ) ≤ 1; norm_num, le_rfl⟩
      (le_iSup₂_of_le 0 (by simp [𝒜0]; omega) le_rfl))
    simpa [XN0] using moment Pr0 𝓕0 hP hfin N
  obtain ⟨N, hN1, hN2⟩ := (((tendsto_order.1 hlim).2 1 one_pos).and (eventually_ge_atTop 1)).exists
  exact absurd (hge N hN2) (not_le.mpr hN1)

end NMVCex


open NeuroMV.Chaos in
theorem not_thm18 : ¬ (∀ {d m n k P : ℕ} {U Ω' Ω ΩX : Type} [MeasurableSpace U] [MeasurableSpace Ω']
    [MeasurableSpace Ω] [MeasurableSpace ΩX]
    (G : Geometry k P) (ν : Measure U) [SigmaFinite ν] (Pr' : Measure Ω')
    [IsProbabilityMeasure Pr'] (C : Coeffs d m n k P U Ω') (R : Rates Ω')
    (pos : ℕ → NeuroMV.WellPosed.Pos k) (𝒜 : ℕ → Finset ℕ) (S : ℕ → Fin P → ℝ) (Q : Partitions k P)
    (Pr : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (W : ℕ → ℝ≥0 → Ω → EthierKurtz.SDEState m) (B : ℕ → Fin P → ℝ≥0 → Ω → EthierKurtz.SDEState n)
    (Nall : Ω → Set (ℝ≥0 × ((ℕ × Option (Fin P)) × U))) (z : ℕ → ℝ → Ω → EthierKurtz.SDEState d)
    (PrX : Measure ΩX) (𝓕X : Filtration ℝ≥0 ‹MeasurableSpace ΩX›)
    (WX : ℝ≥0 → ΩX → EthierKurtz.SDEState m) (BX : Fin P → ℝ≥0 → ΩX → EthierKurtz.SDEState n)
    (NX : ΩX → Set (ℝ≥0 × (Option (Fin P) × U))) (zh : Fin P → ℝ → ΩX → EthierKurtz.SDEState d)
    (hG : G.Valid) (hH : Hyp16 G ν C R pos 𝒜 S Pr' Q)
    (hnet : NetSetup G ν pos 𝒜 S Pr 𝓕 W B Nall z)
    (hnoise : IsNoise6 PrX 𝓕X ν WX BX NX) (hzh : IsInit PrX 𝓕X G.τ zh)
    (hchaos : ChaoticInit G pos 𝒜 Pr z PrX zh)
    (T : ℝ) (hT : 0 < T)
    (XN : ℕ → Ω' → ℕ → ℝ → Ω → EthierKurtz.SDEState d)
    (hXN : ∀ N, ∀ᵐ ω' ∂Pr', IsNetSol G ν C pos 𝒜 S Pr 𝓕 W B Nall z N ω' T (XN N ω'))
    (X : Ω' → NeuroMV.WellPosed.Pos k → ℝ → ΩX → EthierKurtz.SDEState d)
    (hX : ∀ᵐ ω' ∂Pr', IsStrongSol6 G ν C PrX 𝓕X WX BX NX zh ω' T (X ω') ∧
      InClass G PrX T (X ω'))
    (Xbar : Ω' → ℕ → ℝ → Ω → EthierKurtz.SDEState d)
    (hXbar : ∀ᵐ ω' ∂Pr', ∀ i : ℕ, (∃ N, i ∈ 𝒜 N) →
      IsLimitSol G ν C pos Pr 𝓕 W B Nall z PrX (X ω') ω' T i (Xbar ω' i)),
    Tendsto (fun N : ℕ => ∫⁻ ω', ⨆ t ∈ Set.Icc (-G.τ) T, ⨆ i ∈ 𝒜 N,
        ∫⁻ ω, ‖XN N ω' i t ω - Xbar ω' i t ω‖ₑ ^ 2 ∂Pr ∂Pr') atTop (𝓝 0)) := by
  haveI := NMVCex.ν0_prob
  haveI := NMVCex.mscOpt
  haveI : IsProbabilityMeasure (PPP.Pr (κ := ℕ × Option (Fin 1)) NMVCex.ν0) := PPP.Pr_prob _
  haveI : IsProbabilityMeasure (PPP.Pr (κ := Option (Fin 1)) NMVCex.ν0) := PPP.Pr_prob _
  exact NMVCex.cex_main (PPP.Pr (κ := ℕ × Option (Fin 1)) NMVCex.ν0) (PPP.filt NMVCex.ν0)
    (fun ω => PPP.Nset ω) ⟨fun A hA => PPP.filt_null _ A hA 0, PPP.filt_rc _⟩
    (PPP.isFPoisson_Nset _) (fun ω t c => PPP.Nset_finite ω t c) (fun ω z hz => PPP.Nset_pos ω hz)
    (PPP.Pr (κ := Option (Fin 1)) NMVCex.ν0) (PPP.filt NMVCex.ν0) (fun ω => PPP.Nset ω)
    (PPP.isFPoisson_Nset _)

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace NeuroMVChaosAux

open NeuroMV.Chaos

/-- For every `η > 0` there is `ε > 0` with `Σ_α bracket N ε α ≤ η` for all large `N`:
the first and third bracket terms tend to `0` (by `𝒮 → ∞`, (H6) and (10)), and the middle one
sums to `ε · sqSum N ≤ ε · sup_N sqSum`. -/
theorem bracket_small {k P : ℕ} (G : Geometry k P) (pos : ℕ → NeuroMV.WellPosed.Pos k)
    (𝒜 : ℕ → Finset ℕ) (S : ℕ → Fin P → ℝ) (Q : Partitions k P)
    (hBd : BddAbove (Set.range (sqSum G pos 𝒜 S)))
    (hS : ∀ α, Tendsto (fun N => S N α) atTop atTop)
    (h10 : ∀ ε : ℝ, 0 < ε → ∀ α : Fin P, ∀ m,
      Tendsto (fun N => (cnt pos 𝒜 N (Q.part ε α m) : ℝ) / S N α) atTop
        (𝓝 (G.𝓡 (Q.part ε α m)).toReal))
    (η : ℝ) (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ N in atTop, ∑ α, bracket G pos 𝒜 S Q N ε α ≤ η := by
  obtain ⟨Bd, hBd⟩ := hBd
  have hsq : ∀ N, sqSum G pos 𝒜 S N ≤ max Bd 0 := fun N => (hBd ⟨N, rfl⟩).trans (le_max_left _ _)
  obtain ⟨B', hB'⟩ : ∃ B', B' = max Bd 0 := ⟨_, rfl⟩
  rw [← hB'] at hsq
  have hB'0 : 0 ≤ B' := hB' ▸ le_max_right _ _
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = η / (2 * (B' + 1)) := ⟨_, rfl⟩
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  refine ⟨ε, hεpos, ?_⟩
  have hterm : ∀ N α, (cnt pos 𝒜 N (G.Γα α) : ℝ) ^ 2 / S N α ^ 2 ≤ B' := by
    intro N α
    have h1 : (cnt pos 𝒜 N (G.Γα α) : ℝ) ^ 2 / S N α ^ 2 ≤ sqSum G pos 𝒜 S N := by
      unfold sqSum
      exact Finset.single_le_sum (f := fun β => (cnt pos 𝒜 N (G.Γα β) : ℝ) ^ 2 / S N β ^ 2)
        (fun β _ => by positivity) (Finset.mem_univ α)
    exact h1.trans (hsq N)
  have ha : ∀ α, Tendsto (fun N => (cnt pos 𝒜 N (G.Γα α) : ℝ) / S N α ^ 2) atTop (𝓝 0) := by
    intro α
    have hinv : Tendsto (fun N => (S N α)⁻¹) atTop (𝓝 0) := (hS α).inv_tendsto_atTop
    have hbd : ∀ N, ‖(cnt pos 𝒜 N (G.Γα α) : ℝ) / S N α ^ 2‖ ≤ (B' + 1) * |(S N α)⁻¹| := by
      intro N
      rw [Real.norm_eq_abs]
      have e : (cnt pos 𝒜 N (G.Γα α) : ℝ) / S N α ^ 2 =
          ((cnt pos 𝒜 N (G.Γα α) : ℝ) / S N α) * (S N α)⁻¹ := by ring
      have hy : |(cnt pos 𝒜 N (G.Γα α) : ℝ) / S N α| ≤ B' + 1 := by
        have hsq2 : ((cnt pos 𝒜 N (G.Γα α) : ℝ) / S N α) ^ 2 ≤ B' := by
          rw [div_pow]; exact hterm N α
        have := sq_abs ((cnt pos 𝒜 N (G.Γα α) : ℝ) / S N α)
        nlinarith [sq_nonneg (|(cnt pos 𝒜 N (G.Γα α) : ℝ) / S N α| - 1),
          abs_nonneg ((cnt pos 𝒜 N (G.Γα α) : ℝ) / S N α)]
      rw [e, abs_mul]
      exact mul_le_mul_of_nonneg_right hy (abs_nonneg _)
    have hlim : Tendsto (fun N => (B' + 1) * |(S N α)⁻¹|) atTop (𝓝 0) := by
      have := ((continuous_abs.tendsto (0 : ℝ)).comp hinv).const_mul (B' + 1)
      simpa using this
    exact squeeze_zero_norm hbd hlim
  have hc : ∀ α, Tendsto (fun N => (Q.M ε α : ℝ) * ∑ mm, ((cnt pos 𝒜 N (Q.part ε α mm) : ℝ) /
      S N α - (G.𝓡 (Q.part ε α mm)).toReal) ^ 2) atTop (𝓝 0) := by
    intro α
    have hs : Tendsto (fun N => ∑ mm, ((cnt pos 𝒜 N (Q.part ε α mm) : ℝ) /
        S N α - (G.𝓡 (Q.part ε α mm)).toReal) ^ 2) atTop
        (𝓝 (∑ _mm : Fin (Q.M ε α), (0 : ℝ))) := by
      apply tendsto_finsetSum
      intro mm _
      have h := ((h10 ε hεpos α mm).sub_const ((G.𝓡 (Q.part ε α mm)).toReal)).pow 2
      rw [sub_self, zero_pow two_ne_zero] at h
      exact h
    rw [Finset.sum_const_zero] at hs
    simpa using hs.const_mul (Q.M ε α : ℝ)
  have hac : Tendsto (fun N => ∑ α, ((cnt pos 𝒜 N (G.Γα α) : ℝ) / S N α ^ 2 +
      (Q.M ε α : ℝ) * ∑ mm, ((cnt pos 𝒜 N (Q.part ε α mm) : ℝ) /
        S N α - (G.𝓡 (Q.part ε α mm)).toReal) ^ 2)) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset (Fin P)) (fun α _ => (ha α).add (hc α))
    simpa using this
  have hhalf : (0 : ℝ) < η / 2 := by positivity
  filter_upwards [hac.eventually (gt_mem_nhds hhalf)] with N hN
  have e1 : ∑ α, bracket G pos 𝒜 S Q N ε α = (∑ α, ((cnt pos 𝒜 N (G.Γα α) : ℝ) / S N α ^ 2 +
      (Q.M ε α : ℝ) * ∑ mm, ((cnt pos 𝒜 N (Q.part ε α mm) : ℝ) /
        S N α - (G.𝓡 (Q.part ε α mm)).toReal) ^ 2)) + ε * sqSum G pos 𝒜 S N := by
    unfold bracket sqSum
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    ring
  have h2 : ε * sqSum G pos 𝒜 S N ≤ ε * B' := mul_le_mul_of_nonneg_left (hsq N) hεpos.le
  have hne : B' + 1 ≠ 0 := by positivity
  have h3 : ε * B' + ε = η / 2 := by
    rw [hεdef]; field_simp
  rw [e1]
  linarith

end NeuroMVChaosAux

open NeuroMV.Chaos in
theorem eb_to_18
    (hChild : ∀ {d m n k P : ℕ} {U Ω' Ω ΩX : Type} [MeasurableSpace U] [MeasurableSpace Ω']
    [MeasurableSpace Ω] [MeasurableSpace ΩX]
    (G : Geometry k P) (ν : Measure U) [SigmaFinite ν] (Pr' : Measure Ω')
    [IsProbabilityMeasure Pr'] (C : Coeffs d m n k P U Ω') (R : Rates Ω')
    (pos : ℕ → NeuroMV.WellPosed.Pos k) (𝒜 : ℕ → Finset ℕ) (S : ℕ → Fin P → ℝ) (Q : Partitions k P)
    (Pr : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (W : ℕ → ℝ≥0 → Ω → EthierKurtz.SDEState m) (B : ℕ → Fin P → ℝ≥0 → Ω → EthierKurtz.SDEState n)
    (Nall : Ω → Set (ℝ≥0 × ((ℕ × Option (Fin P)) × U))) (z : ℕ → ℝ → Ω → EthierKurtz.SDEState d)
    (PrX : Measure ΩX) (𝓕X : Filtration ℝ≥0 ‹MeasurableSpace ΩX›)
    (WX : ℝ≥0 → ΩX → EthierKurtz.SDEState m) (BX : Fin P → ℝ≥0 → ΩX → EthierKurtz.SDEState n)
    (NX : ΩX → Set (ℝ≥0 × (Option (Fin P) × U))) (zh : Fin P → ℝ → ΩX → EthierKurtz.SDEState d)
    (hG : G.Valid) (hH : Hyp16 G ν C R pos 𝒜 S Pr' Q)
    (hnet : NetSetup G ν pos 𝒜 S Pr 𝓕 W B Nall z)
    (hnoise : IsNoise6 PrX 𝓕X ν WX BX NX) (hzh : IsInit PrX 𝓕X G.τ zh)
    (hchaos : ChaoticInit G pos 𝒜 Pr z PrX zh)
    (T : ℝ) (hT : 0 < T)
    (XN : ℕ → Ω' → ℕ → ℝ → Ω → EthierKurtz.SDEState d)
    (hXN : ∀ N, ∀ᵐ ω' ∂Pr', IsNetSol G ν C pos 𝒜 S Pr 𝓕 W B Nall z N ω' T (XN N ω'))
    (X : Ω' → NeuroMV.WellPosed.Pos k → ℝ → ΩX → EthierKurtz.SDEState d)
    (hX : ∀ᵐ ω' ∂Pr', IsStrongSol6 G ν C PrX 𝓕X WX BX NX zh ω' T (X ω') ∧
      InClass G PrX T (X ω'))
    (Xbar : Ω' → ℕ → ℝ → Ω → EthierKurtz.SDEState d)
    (hXbar : ∀ᵐ ω' ∂Pr', ∀ i : ℕ, (∃ N, i ∈ 𝒜 N) →
      IsLimitSol G ν C pos Pr 𝓕 W B Nall z PrX (X ω') ω' T i (Xbar ω' i)),
    ∃ CT : ℝ≥0∞, CT < ⊤ ∧ ∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
      ∫⁻ ω', (⨆ s ∈ Set.Icc (0 : ℝ) T, ⨆ i ∈ 𝒜 N,
          ∫⁻ ω, ‖XN N ω' i s ω - Xbar ω' i s ω‖ₑ ^ 2 ∂Pr) ∂Pr' ≤
        CT * ENNReal.ofReal (∑ α, bracket G pos 𝒜 S Q N ε α))
    {d m n k P : ℕ} {U Ω' Ω ΩX : Type} [MeasurableSpace U] [MeasurableSpace Ω']
    [MeasurableSpace Ω] [MeasurableSpace ΩX]
    (G : Geometry k P) (ν : Measure U) [SigmaFinite ν] (Pr' : Measure Ω')
    [IsProbabilityMeasure Pr'] (C : Coeffs d m n k P U Ω') (R : Rates Ω')
    (pos : ℕ → NeuroMV.WellPosed.Pos k) (𝒜 : ℕ → Finset ℕ) (S : ℕ → Fin P → ℝ) (Q : Partitions k P)
    (Pr : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (W : ℕ → ℝ≥0 → Ω → EthierKurtz.SDEState m) (B : ℕ → Fin P → ℝ≥0 → Ω → EthierKurtz.SDEState n)
    (Nall : Ω → Set (ℝ≥0 × ((ℕ × Option (Fin P)) × U))) (z : ℕ → ℝ → Ω → EthierKurtz.SDEState d)
    (PrX : Measure ΩX) (𝓕X : Filtration ℝ≥0 ‹MeasurableSpace ΩX›)
    (WX : ℝ≥0 → ΩX → EthierKurtz.SDEState m) (BX : Fin P → ℝ≥0 → ΩX → EthierKurtz.SDEState n)
    (NX : ΩX → Set (ℝ≥0 × (Option (Fin P) × U))) (zh : Fin P → ℝ → ΩX → EthierKurtz.SDEState d)
    (hG : G.Valid) (hH : Hyp16 G ν C R pos 𝒜 S Pr' Q)
    (hnet : NetSetup G ν pos 𝒜 S Pr 𝓕 W B Nall z)
    (hnoise : IsNoise6 PrX 𝓕X ν WX BX NX) (hzh : IsInit PrX 𝓕X G.τ zh)
    (hchaos : ChaoticInit G pos 𝒜 Pr z PrX zh)
    (T : ℝ) (hT : 0 < T)
    (XN : ℕ → Ω' → ℕ → ℝ → Ω → EthierKurtz.SDEState d)
    (hXN : ∀ N, ∀ᵐ ω' ∂Pr', IsNetSol G ν C pos 𝒜 S Pr 𝓕 W B Nall z N ω' T (XN N ω'))
    (X : Ω' → NeuroMV.WellPosed.Pos k → ℝ → ΩX → EthierKurtz.SDEState d)
    (hX : ∀ᵐ ω' ∂Pr', IsStrongSol6 G ν C PrX 𝓕X WX BX NX zh ω' T (X ω') ∧
      InClass G PrX T (X ω'))
    (Xbar : Ω' → ℕ → ℝ → Ω → EthierKurtz.SDEState d)
    (hXbar : ∀ᵐ ω' ∂Pr', ∀ i : ℕ, (∃ N, i ∈ 𝒜 N) →
      IsLimitSol G ν C pos Pr 𝓕 W B Nall z PrX (X ω') ω' T i (Xbar ω' i)) :
    Tendsto (fun N : ℕ => ∫⁻ ω', ⨆ t ∈ Set.Icc (-G.τ) T, ⨆ i ∈ 𝒜 N,
        ∫⁻ ω, ‖XN N ω' i t ω - Xbar ω' i t ω‖ₑ ^ 2 ∂Pr ∂Pr') atTop (𝓝 0) := by
  obtain ⟨CT, hCT, hbound⟩ := hChild G ν Pr' C R pos 𝒜 S Q Pr 𝓕 W B Nall z
    PrX 𝓕X WX BX NX zh hG hH hnet hnoise hzh hchaos T hT XN hXN X hX Xbar hXbar
  have hle : ∀ N, ∫⁻ ω', (⨆ t ∈ Set.Icc (-G.τ) T, ⨆ i ∈ 𝒜 N,
        ∫⁻ ω, ‖XN N ω' i t ω - Xbar ω' i t ω‖ₑ ^ 2 ∂Pr) ∂Pr' ≤
      ∫⁻ ω', (⨆ s ∈ Set.Icc (0 : ℝ) T, ⨆ i ∈ 𝒜 N,
        ∫⁻ ω, ‖XN N ω' i s ω - Xbar ω' i s ω‖ₑ ^ 2 ∂Pr) ∂Pr' := by
    intro N
    apply lintegral_mono_ae
    filter_upwards [hXN N, hXbar] with ω' hN hb
    apply iSup₂_le
    intro t ht
    by_cases ht0 : 0 ≤ t
    · exact le_iSup₂_of_le (f := fun s (_ : s ∈ Set.Icc (0 : ℝ) T) => ⨆ i ∈ 𝒜 N,
        ∫⁻ ω, ‖XN N ω' i s ω - Xbar ω' i s ω‖ₑ ^ 2 ∂Pr) t ⟨ht0, ht.2⟩ le_rfl
    · have htle : t ≤ 0 := le_of_lt (not_le.mp ht0)
      refine le_trans ?_ zero_le
      apply iSup₂_le
      intro i hi
      have h1 := (hN i hi).1 t htle
      have h2 := (hb i ⟨N, hi⟩).1 t htle
      have h0 : ∀ ω, XN N ω' i t ω - Xbar ω' i t ω = 0 := fun ω => by rw [h1 ω, h2 ω, sub_self]
      simp [h0]
  rw [ENNReal.tendsto_atTop_zero]
  intro δ hδ
  by_cases hδtop : δ = ⊤
  · exact ⟨0, fun _ _ => hδtop ▸ le_top⟩
  by_cases hC0 : CT = 0
  · refine ⟨0, fun N _ => ?_⟩
    have h := (hle N).trans (hbound 1 one_pos N)
    rw [hC0, zero_mul] at h
    exact h.trans zero_le
  have hdt : δ / CT ≠ ⊤ := ENNReal.div_ne_top hδtop hC0
  have hη : 0 < (δ / CT).toReal :=
    ENNReal.toReal_pos (ENNReal.div_pos_iff.2 ⟨hδ.ne', hCT.ne⟩).ne' hdt
  obtain ⟨ε, hε, hev⟩ := NeuroMVChaosAux.bracket_small G pos 𝒜 S Q hH.1.2.1 hH.2.1
    (fun ε hε α m => (hH.2.2 ε hε α).2.2.2.1 m) _ hη
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev
  refine ⟨N0, fun N hN => ?_⟩
  calc _ ≤ _ := hle N
    _ ≤ CT * ENNReal.ofReal (∑ α, bracket G pos 𝒜 S Q N ε α) := hbound ε hε N
    _ ≤ CT * ENNReal.ofReal (δ / CT).toReal := by
        gcongr
        exact hN0 N hN
    _ = δ := by rw [ENNReal.ofReal_toReal hdt, ENNReal.mul_div_cancel hC0 hCT.ne]

open NeuroMV.Chaos in
theorem solution : ¬ (∀ {d m n k P : ℕ} {U Ω' Ω ΩX : Type} [MeasurableSpace U] [MeasurableSpace Ω']
    [MeasurableSpace Ω] [MeasurableSpace ΩX]
    (G : Geometry k P) (ν : Measure U) [SigmaFinite ν] (Pr' : Measure Ω')
    [IsProbabilityMeasure Pr'] (C : Coeffs d m n k P U Ω') (R : Rates Ω')
    (pos : ℕ → NeuroMV.WellPosed.Pos k) (𝒜 : ℕ → Finset ℕ) (S : ℕ → Fin P → ℝ) (Q : Partitions k P)
    (Pr : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (W : ℕ → ℝ≥0 → Ω → EthierKurtz.SDEState m) (B : ℕ → Fin P → ℝ≥0 → Ω → EthierKurtz.SDEState n)
    (Nall : Ω → Set (ℝ≥0 × ((ℕ × Option (Fin P)) × U))) (z : ℕ → ℝ → Ω → EthierKurtz.SDEState d)
    (PrX : Measure ΩX) (𝓕X : Filtration ℝ≥0 ‹MeasurableSpace ΩX›)
    (WX : ℝ≥0 → ΩX → EthierKurtz.SDEState m) (BX : Fin P → ℝ≥0 → ΩX → EthierKurtz.SDEState n)
    (NX : ΩX → Set (ℝ≥0 × (Option (Fin P) × U))) (zh : Fin P → ℝ → ΩX → EthierKurtz.SDEState d)
    (hG : G.Valid) (hH : Hyp16 G ν C R pos 𝒜 S Pr' Q)
    (hnet : NetSetup G ν pos 𝒜 S Pr 𝓕 W B Nall z)
    (hnoise : IsNoise6 PrX 𝓕X ν WX BX NX) (hzh : IsInit PrX 𝓕X G.τ zh)
    (hchaos : ChaoticInit G pos 𝒜 Pr z PrX zh)
    (T : ℝ) (hT : 0 < T)
    (XN : ℕ → Ω' → ℕ → ℝ → Ω → EthierKurtz.SDEState d)
    (hXN : ∀ N, ∀ᵐ ω' ∂Pr', IsNetSol G ν C pos 𝒜 S Pr 𝓕 W B Nall z N ω' T (XN N ω'))
    (X : Ω' → NeuroMV.WellPosed.Pos k → ℝ → ΩX → EthierKurtz.SDEState d)
    (hX : ∀ᵐ ω' ∂Pr', IsStrongSol6 G ν C PrX 𝓕X WX BX NX zh ω' T (X ω') ∧
      InClass G PrX T (X ω'))
    (Xbar : Ω' → ℕ → ℝ → Ω → EthierKurtz.SDEState d)
    (hXbar : ∀ᵐ ω' ∂Pr', ∀ i : ℕ, (∃ N, i ∈ 𝒜 N) →
      IsLimitSol G ν C pos Pr 𝓕 W B Nall z PrX (X ω') ω' T i (Xbar ω' i)),
    ∃ CT : ℝ≥0∞, CT < ⊤ ∧ ∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
      ∫⁻ ω', (⨆ s ∈ Set.Icc (0 : ℝ) T, ⨆ i ∈ 𝒜 N,
          ∫⁻ ω, ‖XN N ω' i s ω - Xbar ω' i s ω‖ₑ ^ 2 ∂Pr) ∂Pr' ≤
        CT * ENNReal.ofReal (∑ α, bracket G pos 𝒜 S Q N ε α)) := by
  intro hChild
  exact not_thm18 (eb_to_18 hChild)
