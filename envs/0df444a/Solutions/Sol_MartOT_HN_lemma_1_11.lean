-- Prove2me | solution 1 for MartOT.HN.lemma_1_11
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-11T05:16:01.966654+00:00
-- url     : https://prove2.me/submissions/a50d2fab-9281-4716-9acf-3e18c4af713d

import Mathlib
import Definitions.Def_MartOT_Var_Setting

set_option autoImplicit false

/-! Lemma 1.11 (Beiglböck–Juillet, arXiv:1208.1509, p. 8): reduction skeleton.
Children (as `Prop`s, still OPEN) and the PROVED assembly `assemble`.
C1 KellererParam : Kellerer 1984 Lemma 1.8(a) / BGMS09 Prop 2.1, with a compact parameter coordinate.
C2 BadMeasurable : the parametrised bad set is Borel.
C3 GridReduce    : a cheaper competitor of a finitely supported alpha gives a point of the bad set.
C4 Improve       : a nonzero measure on the bad set with marginals <= pi improves pi. -/

namespace MartOT.HN.L111

open MeasureTheory MartOT.Var

/-- parameter space: weights `w` and grid masses `v`. -/
abbrev Qn (n : ℕ) := (Fin n → ℝ) × (Fin n → Fin n → ℝ)

/-- `∑ w_i δ_{z_i}`. -/
noncomputable def tupMeas (n : ℕ) (z : Fin n → ℝ × ℝ) (w : Fin n → ℝ) : Measure (ℝ × ℝ) :=
  ∑ i, ENNReal.ofReal (w i) • Measure.dirac (z i)

/-- `∑ v_ij δ_{(x_i, y_j)}`: every competitor of `tupMeas` lives on this grid. -/
noncomputable def gridMeas (n : ℕ) (z : Fin n → ℝ × ℝ) (v : Fin n → Fin n → ℝ) :
    Measure (ℝ × ℝ) :=
  ∑ i, ∑ j, ENNReal.ofReal (v i j) • Measure.dirac ((z i).1, (z j).2)

/-- normalised bad tuples with a strictly cheaper grid competitor. -/
def Bad (c : ℝ → ℝ → ℝ) (n : ℕ) : Set (Qn n × (Fin n → ℝ × ℝ)) :=
  {p | (∀ i, p.1.1 i ∈ Set.Icc (0:ℝ) 1) ∧ (∀ i j, p.1.2 i j ∈ Set.Icc (0:ℝ) 1) ∧
    ∑ i, p.1.1 i = 1 ∧ IsCompetitor (tupMeas n p.2 p.1.1) (gridMeas n p.2 p.1.2) ∧
    cost c (gridMeas n p.2 p.1.2) < cost c (tupMeas n p.2 p.1.1)}


open scoped ENNReal NNReal

/-- C2. -/
def BadMeasurable : Prop :=
  ∀ c : ℝ → ℝ → ℝ, Measurable (Function.uncurry c) → ∀ n, MeasurableSet (Bad c n)

lemma integralE_eq_coe' {X : Type*} [MeasurableSpace X] (m : Measure X) (f : X → ℝ)
    (hf : Integrable f m) : MartOT.Var.integralE m f = ((∫ x, f x ∂m : ℝ) : EReal) := by
  unfold MartOT.Var.integralE ModelRiskOT.Duality.extIntegral
  have e1 : ∀ x, ((f x : ℝ) : EReal).toENNReal = ENNReal.ofReal (max (f x) 0) := fun x => by
    rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
    rcases le_total 0 (f x) with h | h
    · rw [max_eq_left h]
    · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
  have e2 : ∀ x, (-((f x : ℝ) : EReal)).toENNReal = ENNReal.ofReal (max (-f x) 0) := fun x => by
    rw [← EReal.coe_neg, EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
    rcases le_total 0 (-f x) with h | h
    · rw [max_eq_left h]
    · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
  simp_rw [e1, e2]
  rw [← ofReal_integral_eq_lintegral_ofReal hf.pos_part (Filter.Eventually.of_forall
      (fun x => le_max_right _ _)),
    ← ofReal_integral_eq_lintegral_ofReal (show Integrable (fun x => max (-f x) 0) m from hf.neg.pos_part) (Filter.Eventually.of_forall
      (fun x => le_max_right _ _)),
    EReal.coe_ennreal_ofReal, EReal.coe_ennreal_ofReal,
    max_eq_left (integral_nonneg (fun x => le_max_right (f x) 0)),
    max_eq_left (integral_nonneg (fun x => le_max_right (-f x) 0)), ← EReal.coe_sub]
  congr 1
  rw [← integral_sub hf.pos_part (show Integrable (fun x => max (-f x) 0) m from hf.neg.pos_part)]
  congr 1
  ext x
  rcases le_total 0 (f x) with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring

lemma integrable_of_fin {m : Measure (ℝ × ℝ)} [IsFiniteMeasure m] (T : Finset (ℝ × ℝ))
    (hT : m (↑T)ᶜ = 0) {f : ℝ × ℝ → ℝ} (hf : Measurable f) : Integrable f m := by
  refine Integrable.of_bound hf.aestronglyMeasurable (∑ t ∈ T, ‖f t‖) ?_
  have hae : ∀ᵐ x ∂m, x ∈ (↑T : Set (ℝ × ℝ)) := by
    rw [ae_iff]; exact hT
  filter_upwards [hae] with x hx
  exact Finset.single_le_sum (f := fun t => ‖f t‖) (fun _ _ => norm_nonneg _) hx

lemma smul_fin {m : Measure (ℝ × ℝ)} [IsFiniteMeasure m] {s : ℝ≥0∞} (hs : s ≠ ⊤) :
    IsFiniteMeasure (s • m) :=
  ⟨by rw [Measure.smul_apply, smul_eq_mul]; exact ENNReal.mul_lt_top hs.lt_top (measure_lt_top _ _)⟩


lemma meas_eq_of_singletons' {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    {m1 m2 : Measure X} (T : Finset X)
    (h1 : m1 (↑T)ᶜ = 0) (h2 : m2 (↑T)ᶜ = 0) (h : ∀ t ∈ T, m1 {t} = m2 {t}) : m1 = m2 := by
  classical
  ext A hA
  have key : ∀ m : Measure X, m (↑T)ᶜ = 0 → m A = ∑ t ∈ T.filter (· ∈ A), m {t} := by
    intro m hm
    have e : (↑(T.filter (· ∈ A)) : Set X) = A ∩ ↑T := by ext x; simp [and_comm]
    rw [sum_measure_singleton, e, measure_inter_conull hm]
  rw [key m1 h1, key m2 h2]
  exact Finset.sum_congr rfl (fun t ht => h t (Finset.mem_filter.1 ht).1)

lemma single_fin (a : ℝ) (t : ℝ × ℝ) :
    IsFiniteMeasure (ENNReal.ofReal a • Measure.dirac t) := smul_fin ENNReal.ofReal_ne_top

lemma integrable_single (a : ℝ) (t : ℝ × ℝ) {f : ℝ × ℝ → ℝ} (hf : Measurable f) :
    Integrable f (ENNReal.ofReal a • Measure.dirac t) := by
  have := single_fin a t
  refine integrable_of_fin {t} ?_ hf
  rw [Measure.smul_apply, Measure.dirac_apply, Set.indicator_of_notMem (by simp), smul_zero]

lemma integrable_atom {ι : Type*} [Fintype ι] (a : ι → ℝ) (t : ι → ℝ × ℝ) {f : ℝ × ℝ → ℝ}
    (hf : Measurable f) : Integrable f (∑ i, ENNReal.ofReal (a i) • Measure.dirac (t i)) :=
  integrable_finsetSum_measure.2 (fun i _ => integrable_single (a i) (t i) hf)

lemma integral_atom {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (t : ι → ℝ × ℝ)
    {f : ℝ × ℝ → ℝ} (hf : Measurable f) :
    ∫ q, f q ∂(∑ i, ENNReal.ofReal (a i) • Measure.dirac (t i)) = ∑ i, a i * f (t i) := by
  rw [integral_finsetSum_measure (fun i _ => integrable_single (a i) (t i) hf)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (ha i), smul_eq_mul]

lemma cost_atom (c : ℝ → ℝ → ℝ) (hc : Measurable (Function.uncurry c)) {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (t : ι → ℝ × ℝ) :
    cost c (∑ i, ENNReal.ofReal (a i) • Measure.dirac (t i)) =
      ((∑ i, a i * c (t i).1 (t i).2 : ℝ) : EReal) := by
  unfold cost
  rw [integralE_eq_coe' _ _ (integrable_atom (f := fun p : ℝ × ℝ => c p.1 p.2) a t hc),
    integral_atom (f := fun p : ℝ × ℝ => c p.1 p.2) a ha t hc]

lemma map_atom_single {ι : Type*} [Fintype ι] (g : ℝ × ℝ → ℝ) (hg : Measurable g)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (t : ι → ℝ × ℝ) (r : ℝ) :
    ((∑ i, ENNReal.ofReal (a i) • Measure.dirac (t i)).map g) {r} =
      ENNReal.ofReal (∑ i, if g (t i) = r then a i else 0) := by
  rw [Measure.map_apply hg (measurableSet_singleton r), Measure.coe_finsetSum, Finset.sum_apply,
    ENNReal.ofReal_sum_of_nonneg (fun i _ => by split_ifs <;> simp [ha i])]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]
  by_cases h : g (t i) = r <;> simp [h]

lemma map_atom_conc {ι : Type*} [Fintype ι] (g : ℝ × ℝ → ℝ) (hg : Measurable g)
    (a : ι → ℝ) (t : ι → ℝ × ℝ) (T : Finset ℝ) (hT : ∀ i, g (t i) ∈ T) :
    ((∑ i, ENNReal.ofReal (a i) • Measure.dirac (t i)).map g) (↑T)ᶜ = 0 := by
  rw [Measure.map_apply hg (Finset.measurableSet _).compl, Measure.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Measure.smul_apply, Measure.dirac_apply, Set.indicator_of_notMem (by simpa using hT i),
    smul_zero]

lemma snn {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (P : ι → Prop)
    [DecidablePred P] : 0 ≤ ∑ i, if P i then a i else 0 :=
  Finset.sum_nonneg fun i _ => by split_ifs <;> simp [ha i]

lemma bary_split {ι : Type*} [Fintype ι] (a : ι → ℝ) (t : ι → ℝ × ℝ) (ρ : ℝ → ℝ) (T : Finset ℝ)
    (hT : ∀ i, (t i).1 ∈ T) :
    ∑ i, a i * (ρ (t i).1 * (t i).2) =
      ∑ r ∈ T, ρ r * ∑ i, (if (t i).1 = r then a i * (t i).2 else 0) := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun i => (t i).1) (t := T) (fun i _ => hT i)]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : (t i).1 = r
  · rw [if_pos h, if_pos h, h]; ring
  · rw [if_neg h, if_neg h, mul_zero]

lemma marg_eq {ι κ : Type*} [Fintype ι] [Fintype κ] (g : ℝ × ℝ → ℝ) (hg : Measurable g)
    (a : ι → ℝ) (b : κ → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (t : ι → ℝ × ℝ) (t' : κ → ℝ × ℝ) :
    (∑ i, ENNReal.ofReal (a i) • Measure.dirac (t i)).map g =
      (∑ j, ENNReal.ofReal (b j) • Measure.dirac (t' j)).map g ↔
    ∀ r, ∑ i, (if g (t i) = r then a i else 0) = ∑ j, (if g (t' j) = r then b j else 0) := by
  constructor
  · intro h r
    have e : ((∑ i, ENNReal.ofReal (a i) • Measure.dirac (t i)).map g) {r} =
        ((∑ j, ENNReal.ofReal (b j) • Measure.dirac (t' j)).map g) {r} := by rw [h]
    rw [map_atom_single g hg a ha t r, map_atom_single g hg b hb t' r,
      ENNReal.ofReal_eq_ofReal_iff (snn a ha _) (snn b hb _)] at e
    exact e
  · intro h
    classical
    let T : Finset ℝ := Finset.univ.image (fun i => g (t i)) ∪ Finset.univ.image (fun j => g (t' j))
    refine meas_eq_of_singletons' T ?_ ?_ ?_
    · exact map_atom_conc g hg a t T
        (fun i => Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
    · exact map_atom_conc g hg b t' T
        (fun j => Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
    · intro r _
      rw [map_atom_single g hg a ha t r, map_atom_single g hg b hb t' r, h r]

theorem comp_iff {ι κ : Type*} [Fintype ι] [Fintype κ] (a : ι → ℝ) (b : κ → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j) (t : ι → ℝ × ℝ) (t' : κ → ℝ × ℝ) :
    IsCompetitor (∑ i, ENNReal.ofReal (a i) • Measure.dirac (t i))
        (∑ j, ENNReal.ofReal (b j) • Measure.dirac (t' j)) ↔
      ((∀ r, ∑ i, (if (t i).1 = r then a i else 0) = ∑ j, (if (t' j).1 = r then b j else 0)) ∧
      (∀ r, ∑ i, (if (t i).2 = r then a i else 0) = ∑ j, (if (t' j).2 = r then b j else 0)) ∧
      (∀ r, ∑ i, (if (t i).1 = r then a i * (t i).2 else 0) =
        ∑ j, (if (t' j).1 = r then b j * (t' j).2 else 0))) := by
  constructor
  · rintro ⟨h1, h2, -, -, h5⟩
    refine ⟨(marg_eq Prod.fst measurable_fst a b ha hb t t').1 h1,
      (marg_eq Prod.snd measurable_snd a b ha hb t t').1 h2, fun r => ?_⟩
    have hρm : Measurable (fun u : ℝ => if u = r then (1:ℝ) else 0) :=
      Measurable.ite (measurableSet_singleton r) measurable_const measurable_const
    have e := h5 _ hρm ⟨1, fun u => by split_ifs <;> simp⟩
    rw [integral_atom (f := fun p : ℝ × ℝ => (if p.1 = r then (1:ℝ) else 0) * p.2) a ha t
      ((hρm.comp measurable_fst).mul measurable_snd),
      integral_atom (f := fun p : ℝ × ℝ => (if p.1 = r then (1:ℝ) else 0) * p.2) b hb t'
      ((hρm.comp measurable_fst).mul measurable_snd)] at e
    convert e using 2 <;> rename_i i _ <;> split_ifs <;> simp
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(marg_eq Prod.fst measurable_fst a b ha hb t t').2 h1,
      (marg_eq Prod.snd measurable_snd a b ha hb t t').2 h2, integrable_atom a t measurable_snd,
      integrable_atom b t' measurable_snd, fun ρ hρ _ => ?_⟩
    classical
    let T : Finset ℝ := Finset.univ.image (fun i => (t i).1) ∪ Finset.univ.image (fun j => (t' j).1)
    rw [integral_atom (f := fun p : ℝ × ℝ => ρ p.1 * p.2) a ha t
      ((hρ.comp measurable_fst).mul measurable_snd),
      integral_atom (f := fun p : ℝ × ℝ => ρ p.1 * p.2) b hb t'
      ((hρ.comp measurable_fst).mul measurable_snd),
      bary_split a t ρ T (fun i => Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))),
      bary_split b t' ρ T (fun j => Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j)))]
    exact Finset.sum_congr rfl fun r _ => by rw [h3 r]

lemma ar_iff {ι κ : Type*} [Fintype ι] [Fintype κ] {n : ℕ} (x : Fin n → ℝ) (g : ι → Fin n)
    (h : κ → Fin n) (F : ι → ℝ) (G : κ → ℝ) :
    (∀ r, ∑ i, (if x (g i) = r then F i else 0) = ∑ j, (if x (h j) = r then G j else 0)) ↔
      ∀ k, ∑ i, (if x (g i) = x k then F i else 0) = ∑ j, (if x (h j) = x k then G j else 0) := by
  constructor
  · intro H k; exact H _
  · intro H r
    by_cases hr : ∃ k, x k = r
    · obtain ⟨k, rfl⟩ := hr; exact H k
    · rw [Finset.sum_eq_zero (fun i _ => if_neg (fun e => hr ⟨_, e⟩)),
        Finset.sum_eq_zero (fun j _ => if_neg (fun e => hr ⟨_, e⟩))]

/-- the finite system equivalent to `IsCompetitor tup grid ∧ cost grid < cost tup`. -/
def Eqs (c : ℝ → ℝ → ℝ) (n : ℕ) (w : Fin n → ℝ) (v : Fin n → Fin n → ℝ)
    (z : Fin n → ℝ × ℝ) : Prop :=
  (∀ k, ∑ i, (if (z i).1 = (z k).1 then w i else 0) =
      ∑ q : Fin n × Fin n, (if (z q.1).1 = (z k).1 then v q.1 q.2 else 0)) ∧
  (∀ k, ∑ i, (if (z i).2 = (z k).2 then w i else 0) =
      ∑ q : Fin n × Fin n, (if (z q.2).2 = (z k).2 then v q.1 q.2 else 0)) ∧
  (∀ k, ∑ i, (if (z i).1 = (z k).1 then w i * (z i).2 else 0) =
      ∑ q : Fin n × Fin n, (if (z q.1).1 = (z k).1 then v q.1 q.2 * (z q.2).2 else 0)) ∧
  ∑ q : Fin n × Fin n, v q.1 q.2 * c (z q.1).1 (z q.2).2 < ∑ i, w i * c (z i).1 (z i).2

lemma grid_eq (n : ℕ) (z : Fin n → ℝ × ℝ) (v : Fin n → Fin n → ℝ) :
    gridMeas n z v = ∑ q : Fin n × Fin n,
      ENNReal.ofReal (v q.1 q.2) • Measure.dirac ((z q.1).1, (z q.2).2) := by
  unfold gridMeas; rw [Fintype.sum_prod_type]


lemma toENNReal_coe (r : ℝ) : ((r : EReal)).toENNReal = ENNReal.ofReal r := by
  rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]

lemma toENNReal_neg_coe (r : ℝ) : (-(r : EReal)).toENNReal = ENNReal.ofReal (-r) := by
  rw [← EReal.coe_neg, toENNReal_coe]

/-- Finite cost plus the sufficient integrability condition make the cost integrable. -/
lemma cost_integrable (μ ν : Measure ℝ) [IsFiniteMeasure μ] (π : Measure (ℝ × ℝ))
    (hplan : MartOT.Var.IsPlan μ ν π) (c : ℝ → ℝ → ℝ)
    (hc : Measurable (fun p : ℝ × ℝ => c p.1 p.2))
    (hint : MartOT.Var.SuffIntegrable μ ν c) (hfin : MartOT.Var.cost c π < ⊤) :
    Integrable (fun p : ℝ × ℝ => c p.1 p.2) π := by
  obtain ⟨a, b, ha, hb, hab⟩ := hint
  have hπa : Integrable (fun p : ℝ × ℝ => a p.1) π := by
    have h1 : Integrable a (π.map Prod.fst) := by rw [hplan.1]; exact ha
    exact (integrable_map_measure (hplan.1 ▸ ha.aestronglyMeasurable)
      measurable_fst.aemeasurable).1 h1
  have hπb : Integrable (fun p : ℝ × ℝ => b p.2) π := by
    have h1 : Integrable b (π.map Prod.snd) := by rw [hplan.2]; exact hb
    exact (integrable_map_measure (hplan.2 ▸ hb.aestronglyMeasurable)
      measurable_snd.aemeasurable).1 h1
  have hg := hπa.add hπb
  set f : ℝ × ℝ → ℝ := fun p => c p.1 p.2 with hf
  -- negative part finite
  have hneg : ∫⁻ p, ENNReal.ofReal (-f p) ∂π ≠ ⊤ := by
    have hle : ∀ p, ENNReal.ofReal (-f p) ≤ ‖a p.1 + b p.2‖ₑ := by
      intro p
      rw [← ofReal_norm_eq_enorm]
      apply ENNReal.ofReal_le_ofReal
      have := hab p.1 p.2
      rw [Real.norm_eq_abs]
      have := neg_abs_le (a p.1 + b p.2)
      simp only [hf]; linarith
    exact ne_top_of_le_ne_top hg.2.ne (lintegral_mono hle)
  have hpos : ∫⁻ p, ENNReal.ofReal (f p) ∂π ≠ ⊤ := by
    intro htop
    have : MartOT.Var.cost c π = ⊤ := by
      unfold MartOT.Var.cost MartOT.Var.integralE ModelRiskOT.Duality.extIntegral
      simp_rw [toENNReal_coe, toENNReal_neg_coe]
      change ((∫⁻ p, ENNReal.ofReal (f p) ∂π : ENNReal) : EReal) -
        ((∫⁻ p, ENNReal.ofReal (-f p) ∂π : ENNReal) : EReal) = ⊤
      rw [htop, EReal.coe_ennreal_top]
      apply EReal.top_sub
      exact fun h => hneg (EReal.coe_ennreal_eq_top_iff.1 h)
    rw [this] at hfin
    exact lt_irrefl _ hfin
  have i1 := integrable_toReal_of_lintegral_ne_top
    (hc.ennreal_ofReal.aemeasurable) hpos
  have i2 := integrable_toReal_of_lintegral_ne_top
    (hc.neg.ennreal_ofReal.aemeasurable) hneg
  refine (i1.sub i2).congr (Filter.Eventually.of_forall (fun p => ?_))
  simp only [Pi.sub_apply, ENNReal.toReal_ofReal', Pi.neg_apply]
  rcases le_total 0 (f p) with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring

/-- C4 (the improvement step of BJ's proof). -/
def Improve : Prop :=
  ∀ (μ ν : Measure ℝ), IsProbabilityMeasure μ → IsProbabilityMeasure ν →
    ∀ (c : ℝ → ℝ → ℝ), Measurable (Function.uncurry c) → SuffIntegrable μ ν c →
    ∀ (π : Measure (ℝ × ℝ)), IsMartingalePlan μ ν π → cost c π < ⊤ →
    ∀ (n : ℕ) (ξ : Measure (Qn n × (Fin n → ℝ × ℝ))), IsFiniteMeasure ξ →
      ξ (Bad c n)ᶜ = 0 → ξ ≠ 0 → (∀ i, ξ.map (fun p => p.2 i) ≤ π) →
      ∃ π', IsMartingalePlan μ ν π' ∧ cost c π' < cost c π

section avgsec
variable {P : Type*} [MeasurableSpace P] {ι : Type*} [Fintype ι]

/-- `∫ (∑ a_i(p) δ_{g_i(p)}) dξ(p)`. -/
noncomputable def avg (ξ : Measure P) (a : ι → P → ℝ) (g : ι → P → ℝ × ℝ) : Measure (ℝ × ℝ) :=
  ∑ i, (ξ.withDensity (fun p => ENNReal.ofReal (a i p))).map (g i)

lemma avg_apply (ξ : Measure P) {a : ι → P → ℝ} {g : ι → P → ℝ × ℝ} (ha : ∀ i, Measurable (a i))
    (hg : ∀ i, Measurable (g i)) {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) :
    avg ξ a g A = ∫⁻ p, (∑ i, ENNReal.ofReal (a i p) • Measure.dirac (g i p)) A ∂ξ := by
  unfold avg
  simp_rw [Measure.finset_sum_apply, Measure.smul_apply, Measure.dirac_apply' _ hA, smul_eq_mul]
  have hm : ∀ i, Measurable (fun p => ENNReal.ofReal (a i p) * A.indicator 1 (g i p)) :=
    fun i => (ha i).ennreal_ofReal.mul ((measurable_one.indicator hA).comp (hg i))
  rw [lintegral_finset_sum _ (fun i _ => hm i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.map_apply (hg i) hA, withDensity_apply _ ((hg i) hA),
    ← lintegral_indicator ((hg i) hA)]
  refine lintegral_congr fun p => ?_
  by_cases h : g i p ∈ A <;> simp [Set.indicator_apply, h]

lemma avg_map_eq {κ : Type*} [Fintype κ] (ξ : Measure P) {a : ι → P → ℝ} {g : ι → P → ℝ × ℝ}
    {b : κ → P → ℝ} {h : κ → P → ℝ × ℝ} (ha : ∀ i, Measurable (a i)) (hg : ∀ i, Measurable (g i))
    (hb : ∀ j, Measurable (b j)) (hh : ∀ j, Measurable (h j)) {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    (heq : ∀ᵐ p ∂ξ, (∑ i, ENNReal.ofReal (a i p) • Measure.dirac (g i p)).map f =
      (∑ j, ENNReal.ofReal (b j p) • Measure.dirac (h j p)).map f) :
    (avg ξ a g).map f = (avg ξ b h).map f := by
  ext S hS
  rw [Measure.map_apply hf hS, Measure.map_apply hf hS, avg_apply ξ ha hg (hf hS),
    avg_apply ξ hb hh (hf hS)]
  refine lintegral_congr_ae ?_
  filter_upwards [heq] with p hp
  rw [← Measure.map_apply hf hS, ← Measure.map_apply hf hS, hp]

lemma piece_int' (ξ : Measure P) [IsFiniteMeasure ξ] {a : P → ℝ} {g : P → ℝ × ℝ}
    (ha : Measurable a) (hg : Measurable g) {f : ℝ × ℝ → ℝ} (hf : Measurable f) {K : ℝ}
    (ha1 : ∀ᵐ p ∂ξ, a p ≤ 1) (hb : ∀ᵐ p ∂ξ, |f (g p)| ≤ K) :
    Integrable (fun p => (a p).toNNReal • f (g p)) ξ := by
  refine (integrable_const K).mono' (ha.real_toNNReal.smul (hf.comp hg)).aestronglyMeasurable ?_
  filter_upwards [ha1, hb] with p h1 h2
  rw [Real.norm_eq_abs, NNReal.smul_def, smul_eq_mul, abs_mul, Real.coe_toNNReal']
  have h0 : 0 ≤ max (a p) 0 := le_max_right _ _
  have h1' : max (a p) 0 ≤ 1 := max_le h1 zero_le_one
  rw [abs_of_nonneg h0]
  nlinarith [abs_nonneg (f (g p))]

lemma piece_int (ξ : Measure P) [IsFiniteMeasure ξ] {a : P → ℝ} {g : P → ℝ × ℝ}
    (ha : Measurable a) (hg : Measurable g) {f : ℝ × ℝ → ℝ} (hf : Measurable f) {K : ℝ}
    (ha1 : ∀ᵐ p ∂ξ, a p ≤ 1) (hb : ∀ᵐ p ∂ξ, |f (g p)| ≤ K) :
    Integrable f ((ξ.withDensity (fun p => ENNReal.ofReal (a p))).map g) := by
  rw [integrable_map_measure hf.aestronglyMeasurable hg.aemeasurable]
  exact (integrable_withDensity_iff_integrable_smul ha.real_toNNReal).2
    (piece_int' ξ ha hg hf ha1 hb)

lemma avg_integrable (ξ : Measure P) [IsFiniteMeasure ξ] {a : ι → P → ℝ} {g : ι → P → ℝ × ℝ}
    (ha : ∀ i, Measurable (a i)) (hg : ∀ i, Measurable (g i)) {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    {K : ℝ} (ha1 : ∀ i, ∀ᵐ p ∂ξ, a i p ≤ 1) (hb : ∀ i, ∀ᵐ p ∂ξ, |f (g i p)| ≤ K) :
    Integrable f (avg ξ a g) := by
  unfold avg
  exact integrable_finset_sum_measure.2 fun i _ => piece_int ξ (ha i) (hg i) hf (ha1 i) (hb i)

lemma avg_sum_int (ξ : Measure P) [IsFiniteMeasure ξ] {a : ι → P → ℝ} {g : ι → P → ℝ × ℝ}
    (ha : ∀ i, Measurable (a i)) (hg : ∀ i, Measurable (g i)) {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    {K : ℝ} (ha1 : ∀ i, ∀ᵐ p ∂ξ, a i p ≤ 1) (hb : ∀ i, ∀ᵐ p ∂ξ, |f (g i p)| ≤ K) :
    Integrable (fun p => ∑ i, max (a i p) 0 * f (g i p)) ξ :=
  integrable_finset_sum _ fun i _ => (piece_int' ξ (ha i) (hg i) hf (ha1 i) (hb i)).congr
    (Filter.Eventually.of_forall fun p => by
      simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal'])

lemma avg_integral (ξ : Measure P) [IsFiniteMeasure ξ] {a : ι → P → ℝ} {g : ι → P → ℝ × ℝ}
    (ha : ∀ i, Measurable (a i)) (hg : ∀ i, Measurable (g i)) {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    {K : ℝ} (ha1 : ∀ i, ∀ᵐ p ∂ξ, a i p ≤ 1) (hb : ∀ i, ∀ᵐ p ∂ξ, |f (g i p)| ≤ K) :
    ∫ q, f q ∂(avg ξ a g) = ∫ p, ∑ i, max (a i p) 0 * f (g i p) ∂ξ := by
  have hI : ∀ i, Integrable (fun p => max (a i p) 0 * f (g i p)) ξ := fun i =>
    (piece_int' ξ (ha i) (hg i) hf (ha1 i) (hb i)).congr (Filter.Eventually.of_forall fun p => by
      simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal'])
  unfold avg
  rw [integral_finset_sum_measure (fun i _ => piece_int ξ (ha i) (hg i) hf (ha1 i) (hb i)),
    integral_finset_sum _ (fun i _ => hI i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_map (hg i).aemeasurable hf.aestronglyMeasurable,
    show (fun p => ENNReal.ofReal (a i p)) = fun p => (((a i p).toNNReal : ℝ≥0) : ℝ≥0∞) from rfl,
    integral_withDensity_eq_integral_smul (ha i).real_toNNReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal']

lemma avg_integral_pt (ξ : Measure P) [IsFiniteMeasure ξ] {a : ι → P → ℝ} {g : ι → P → ℝ × ℝ}
    (ha : ∀ i, Measurable (a i)) (hg : ∀ i, Measurable (g i)) {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    {K : ℝ} (ha1 : ∀ i, ∀ᵐ p ∂ξ, a i p ≤ 1) (hb : ∀ i, ∀ᵐ p ∂ξ, |f (g i p)| ≤ K)
    (ha0 : ∀ i, ∀ᵐ p ∂ξ, 0 ≤ a i p) :
    ∫ q, f q ∂(avg ξ a g) =
      ∫ p, (∫ x, f x ∂(∑ i, ENNReal.ofReal (a i p) • Measure.dirac (g i p))) ∂ξ := by
  rw [avg_integral ξ ha hg hf ha1 hb]
  refine integral_congr_ae ?_
  have h0 : ∀ᵐ p ∂ξ, ∀ i, 0 ≤ a i p := ae_all_iff.2 ha0
  filter_upwards [h0] with p hp
  rw [show (∫ x, f x ∂(∑ i, ENNReal.ofReal (a i p) • Measure.dirac (g i p))) =
      ∑ i, a i p * f (g i p) from integral_atom (fun i => a i p) hp (fun i => g i p) hf]
  exact Finset.sum_congr rfl fun i _ => by rw [max_eq_left (hp i)]

end avgsec

lemma integral_lt_of_ae_lt {X : Type*} [MeasurableSpace X] (θ : Measure X) (hθ : θ ≠ 0)
    {f g : X → ℝ} (hf : Integrable f θ) (hg : Integrable g θ) (h : ∀ᵐ p ∂θ, f p < g p) :
    ∫ p, f p ∂θ < ∫ p, g p ∂θ := by
  have hd : 0 < ∫ p, (g p - f p) ∂θ := by
    rw [integral_pos_iff_support_of_nonneg_ae (h.mono fun p hp => (sub_pos.2 hp).le) (hg.sub hf)]
    have hs : θ (Function.support fun p => g p - f p)ᶜ = 0 := by
      rw [ae_iff] at h
      refine measure_mono_null ?_ h
      intro p hp hlt
      simp only [Set.mem_compl_iff, Function.mem_support, not_not] at hp
      linarith
    rw [pos_iff_ne_zero]
    intro h0
    apply hθ
    rw [← Measure.measure_univ_eq_zero]
    refine le_antisymm ?_ (by simp)
    calc θ Set.univ = θ ((Function.support fun p => g p - f p) ∪
          (Function.support fun p => g p - f p)ᶜ) := by rw [Set.union_compl_self]
      _ ≤ θ (Function.support fun p => g p - f p) + θ (Function.support fun p => g p - f p)ᶜ :=
          measure_union_le _ _
      _ = 0 := by rw [h0, hs, add_zero]
  rw [integral_sub hg hf] at hd
  linarith

lemma mart_atom {ι κ : Type*} [Fintype ι] [Fintype κ] (a : ι → ℝ) (b : κ → ℝ)
    (t : ι → ℝ × ℝ) (t' : κ → ℝ × ℝ)
    (h : IsCompetitor (∑ i, ENNReal.ofReal (a i) • Measure.dirac (t i))
      (∑ j, ENNReal.ofReal (b j) • Measure.dirac (t' j)))
    (ρ : ℝ → ℝ) (hρ : Measurable ρ) (hρb : ∃ C, ∀ x, |ρ x| ≤ C) :
    ∫ z, ρ z.1 * (z.2 - z.1) ∂(∑ i, ENNReal.ofReal (a i) • Measure.dirac (t i)) =
      ∫ z, ρ z.1 * (z.2 - z.1) ∂(∑ j, ENNReal.ofReal (b j) • Measure.dirac (t' j)) := by
  have e : ∀ m : Measure (ℝ × ℝ), Integrable (fun z : ℝ × ℝ => ρ z.1 * z.2) m →
      Integrable (fun z : ℝ × ℝ => ρ z.1 * z.1) m →
      ∫ z, ρ z.1 * (z.2 - z.1) ∂m = ∫ z, ρ z.1 * z.2 ∂m - ∫ z, ρ z.1 * z.1 ∂m :=
    fun m h1 h2 => by
      rw [← integral_sub h1 h2]; congr 1; ext z; ring
  have m1 : Measurable (fun z : ℝ × ℝ => ρ z.1 * z.2) := by fun_prop
  have m2 : Measurable (fun z : ℝ × ℝ => ρ z.1 * z.1) := by fun_prop
  have m3 : Measurable (fun x : ℝ => ρ x * x) := by fun_prop
  rw [e _ (integrable_atom a t m1) (integrable_atom a t m2),
    e _ (integrable_atom b t' m1) (integrable_atom b t' m2), h.2.2.2.2 ρ hρ hρb]
  congr 1
  have hm := congrArg (fun m : Measure ℝ => ∫ x, ρ x * x ∂m) h.1
  beta_reduce at hm
  rwa [integral_map measurable_fst.aemeasurable m3.aestronglyMeasurable,
    integral_map measurable_fst.aemeasurable m3.aestronglyMeasurable] at hm

lemma sub_bd {x y K : ℝ} (hx : |x| ≤ K) (hy : |y| ≤ K) : |y - x| ≤ K + K := by
  rw [abs_le] at *
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- bounded part of the tuple space. -/
def Ebd (c : ℝ → ℝ → ℝ) (n : ℕ) (K : ℝ) : Set (Qn n × (Fin n → ℝ × ℝ)) :=
  {p | ∀ i j, |c (p.2 i).1 (p.2 j).2| ≤ K ∧ |(p.2 i).1| ≤ K ∧ |(p.2 j).2| ≤ K}

lemma Ebd_meas (c : ℝ → ℝ → ℝ) (hc : Measurable (Function.uncurry c)) (n : ℕ) (K : ℝ) :
    MeasurableSet (Ebd c n K) := by
  unfold Ebd
  simp only [Set.setOf_forall, Set.setOf_and]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
  have h1 : Measurable fun p : Qn n × (Fin n → ℝ × ℝ) => c (p.2 i).1 (p.2 j).2 :=
    hc.comp (f := fun p : Qn n × (Fin n → ℝ × ℝ) => ((p.2 i).1, (p.2 j).2)) (by fun_prop)
  exact (measurableSet_le (continuous_abs.measurable.comp h1) measurable_const).inter
    ((measurableSet_le (by fun_prop) measurable_const).inter
      (measurableSet_le (by fun_prop) measurable_const))

lemma Ebd_union (c : ℝ → ℝ → ℝ) (n : ℕ) : ⋃ K : ℕ, Ebd c n K = Set.univ := by
  refine Set.eq_univ_of_forall fun p => ?_
  obtain ⟨K, hK⟩ := exists_nat_ge
    (∑ i, ∑ j, (|c (p.2 i).1 (p.2 j).2| + |(p.2 i).1| + |(p.2 j).2|))
  refine Set.mem_iUnion.2 ⟨K, ?_⟩
  intro i j
  have hij : |c (p.2 i).1 (p.2 j).2| + |(p.2 i).1| + |(p.2 j).2| ≤
      ∑ i, ∑ j, (|c (p.2 i).1 (p.2 j).2| + |(p.2 i).1| + |(p.2 j).2|) := by
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun i => ∑ j, (|c (p.2 i).1 (p.2 j).2| + |(p.2 i).1| + |(p.2 j).2|))
      (fun i _ => Finset.sum_nonneg fun j _ => by positivity) (Finset.mem_univ i))
    exact Finset.single_le_sum
      (f := fun j => |c (p.2 i).1 (p.2 j).2| + |(p.2 i).1| + |(p.2 j).2|)
      (fun j _ => by positivity) (Finset.mem_univ j)
  have a1 := abs_nonneg (c (p.2 i).1 (p.2 j).2)
  have a2 := abs_nonneg (p.2 i).1
  have a3 := abs_nonneg (p.2 j).2
  exact ⟨by linarith, by linarith, by linarith⟩

lemma bad_cost_lt (c : ℝ → ℝ → ℝ) (hc : Measurable (Function.uncurry c)) {n : ℕ}
    {p : Qn n × (Fin n → ℝ × ℝ)} (hp : p ∈ Bad c n) :
    ∑ q : Fin n × Fin n, p.1.2 q.1 q.2 * c (p.2 q.1).1 (p.2 q.2).2 <
      ∑ i, p.1.1 i * c (p.2 i).1 (p.2 i).2 := by
  have h := hp.2.2.2.2
  rw [grid_eq, show cost c (tupMeas n p.2 p.1.1) =
      ((∑ i, p.1.1 i * c (p.2 i).1 (p.2 i).2 : ℝ) : EReal) from
      cost_atom c hc (fun i => p.1.1 i) (fun i => (hp.1 i).1) (fun i => p.2 i),
    show cost c (∑ q : Fin n × Fin n, ENNReal.ofReal (p.1.2 q.1 q.2) •
        Measure.dirac ((p.2 q.1).1, (p.2 q.2).2)) =
      ((∑ q : Fin n × Fin n, p.1.2 q.1 q.2 * c (p.2 q.1).1 (p.2 q.2).2 : ℝ) : EReal) from
      cost_atom c hc (fun q : Fin n × Fin n => p.1.2 q.1 q.2) (fun q => (hp.2.1 q.1 q.2).1)
        (fun q => ((p.2 q.1).1, (p.2 q.2).2))] at h
  exact_mod_cast h

set_option maxHeartbeats 1000000 in
theorem improve4 : Improve := by
  intro μ ν hμ hν c hc hint π hπ hfin n ξ hξf hξB hξ0 hξm
  have hcm : Measurable (fun z : ℝ × ℝ => c z.1 z.2) := hc
  have hfinπ : IsFiniteMeasure π := by
    refine ⟨?_⟩
    have : π Set.univ = (π.map Prod.fst) Set.univ := by
      rw [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ]
    rw [this, hπ.1.1]; exact measure_lt_top μ _
  have hcI : Integrable (fun z : ℝ × ℝ => c z.1 z.2) π := cost_integrable μ ν π hπ.1 c hcm hint hfin
  have hBad : ∀ᵐ p ∂ξ, p ∈ Bad c n := by rw [ae_iff]; exact hξB
  have hn : n ≠ 0 := by
    rintro rfl
    apply hξ0
    rw [← Measure.measure_univ_eq_zero]
    have h : ∀ᵐ p ∂ξ, False := by
      filter_upwards [hBad] with p hp
      have := hp.2.2.1
      simp at this
    simpa [ae_iff] using h
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ξ (Ebd c n K) ≠ 0 := by
    by_contra h
    push_neg at h
    apply hξ0
    rw [← Measure.measure_univ_eq_zero, ← Ebd_union c n]
    exact measure_iUnion_null h
  set θ : Measure (Qn n × (Fin n → ℝ × ℝ)) := (n : ℝ≥0∞)⁻¹ • ξ.restrict (Ebd c n K) with hθdef
  have hninv : (n : ℝ≥0∞)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 (Nat.cast_ne_zero.2 hn)
  haveI : IsFiniteMeasure θ := by
    refine ⟨?_⟩
    rw [hθdef, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top hninv.lt_top (measure_lt_top _ _)
  have hθ0 : θ ≠ 0 := by
    intro h0
    have h1 := congrArg (fun m : Measure (Qn n × (Fin n → ℝ × ℝ)) => m (Ebd c n K)) h0
    simp only [hθdef, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_self,
      Measure.coe_zero, Pi.zero_apply] at h1
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top n) h2
    · exact hK h2
  have hθa : ∀ᵐ p ∂θ, p ∈ Bad c n ∧ p ∈ Ebd c n K := by
    rw [hθdef]
    exact Measure.ae_smul_measure
      ((ae_restrict_of_ae hBad).and (ae_restrict_mem (Ebd_meas c hc n K))) _
  have ham : ∀ i : Fin n, Measurable (fun p : Qn n × (Fin n → ℝ × ℝ) => p.1.1 i) :=
    fun i => by fun_prop
  have hgm : ∀ i : Fin n, Measurable (fun p : Qn n × (Fin n → ℝ × ℝ) => p.2 i) :=
    fun i => by fun_prop
  have hbm : ∀ q : Fin n × Fin n,
      Measurable (fun p : Qn n × (Fin n → ℝ × ℝ) => p.1.2 q.1 q.2) := fun q => by fun_prop
  have hhm : ∀ q : Fin n × Fin n,
      Measurable (fun p : Qn n × (Fin n → ℝ × ℝ) => ((p.2 q.1).1, (p.2 q.2).2)) :=
    fun q => by fun_prop
  have ha1 : ∀ i : Fin n, ∀ᵐ p ∂θ, p.1.1 i ≤ 1 := fun i => hθa.mono fun p hp => (hp.1.1 i).2
  have ha0 : ∀ i : Fin n, ∀ᵐ p ∂θ, 0 ≤ p.1.1 i := fun i => hθa.mono fun p hp => (hp.1.1 i).1
  have hb1 : ∀ q : Fin n × Fin n, ∀ᵐ p ∂θ, p.1.2 q.1 q.2 ≤ 1 :=
    fun q => hθa.mono fun p hp => (hp.1.2.1 q.1 q.2).2
  have hb0 : ∀ q : Fin n × Fin n, ∀ᵐ p ∂θ, 0 ≤ p.1.2 q.1 q.2 :=
    fun q => hθa.mono fun p hp => (hp.1.2.1 q.1 q.2).1
  set Wm := avg θ (fun i p => p.1.1 i) (fun i p => p.2 i) with hRdef
  set A := avg θ (fun (q : Fin n × Fin n) p => p.1.2 q.1 q.2)
    (fun q p => ((p.2 q.1).1, (p.2 q.2).2)) with hAdef
  have hR : Wm ≤ π := by
    refine Measure.le_iff.2 fun s hs => ?_
    rw [hRdef]; unfold avg
    beta_reduce
    rw [Measure.finset_sum_apply]
    calc ∑ i : Fin n, ((θ.withDensity fun p => ENNReal.ofReal (p.1.1 i)).map (fun p => p.2 i)) s
        ≤ ∑ _i : Fin n, (n : ℝ≥0∞)⁻¹ * π s := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [Measure.map_apply (hgm i) hs, withDensity_apply _ (hgm i hs)]
          calc ∫⁻ p in (fun p => p.2 i) ⁻¹' s, ENNReal.ofReal (p.1.1 i) ∂θ
              ≤ ∫⁻ _p in (fun p => p.2 i) ⁻¹' s, 1 ∂θ :=
                lintegral_mono_ae (ae_restrict_of_ae ((ha1 i).mono fun p hp =>
                  ENNReal.ofReal_le_one.2 hp))
            _ = θ ((fun p => p.2 i) ⁻¹' s) := by rw [setLIntegral_const, one_mul]
            _ ≤ (n : ℝ≥0∞)⁻¹ * π s := by
                rw [hθdef, Measure.smul_apply, smul_eq_mul]
                gcongr
                calc ξ.restrict (Ebd c n K) ((fun p => p.2 i) ⁻¹' s)
                    ≤ ξ ((fun p => p.2 i) ⁻¹' s) := Measure.le_iff'.1 Measure.restrict_le_self _
                  _ = ξ.map (fun p => p.2 i) s := (Measure.map_apply (hgm i) hs).symm
                  _ ≤ π s := Measure.le_iff'.1 (hξm i) s
      _ = π s := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
            ENNReal.mul_inv_cancel (Nat.cast_ne_zero.2 hn) (ENNReal.natCast_ne_top n), one_mul]
  haveI : IsFiniteMeasure Wm := isFiniteMeasure_of_le π hR
  have hfstA : A.map Prod.fst = Wm.map Prod.fst := by
    rw [hAdef, hRdef]
    refine avg_map_eq θ hbm hhm ham hgm measurable_fst (hθa.mono fun p hp => ?_)
    have h := hp.1.2.2.2.1.1
    rw [grid_eq] at h
    exact h.symm
  have hsndA : A.map Prod.snd = Wm.map Prod.snd := by
    rw [hAdef, hRdef]
    refine avg_map_eq θ hbm hhm ham hgm measurable_snd (hθa.mono fun p hp => ?_)
    have h := hp.1.2.2.2.1.2.1
    rw [grid_eq] at h
    exact h.symm
  refine ⟨π - Wm + A, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · rw [Measure.map_add _ _ measurable_fst, hfstA, ← Measure.map_add _ _ measurable_fst,
      Measure.sub_add_cancel_of_le hR]
    exact hπ.1.1
  · rw [Measure.map_add _ _ measurable_snd, hsndA, ← Measure.map_add _ _ measurable_snd,
      Measure.sub_add_cancel_of_le hR]
    exact hπ.1.2
  · refine (hπ.2.1.mono_measure Measure.sub_le).add_measure ?_
    rw [hAdef]
    exact avg_integrable θ hbm hhm (by fun_prop) hb1
      (fun q => hθa.mono fun p hp => sub_bd (hp.2 q.1 q.2).2.1 (hp.2 q.1 q.2).2.2)
  · intro ρ hρ hρb
    obtain ⟨C, hC⟩ := hρb
    have hfm : Measurable (fun z : ℝ × ℝ => ρ z.1 * (z.2 - z.1)) := by fun_prop
    have hbd : ∀ x y : ℝ, |x| ≤ K → |y| ≤ K → |ρ x * (y - x)| ≤ C * (K + K) :=
      fun x y hx hy => by
        rw [abs_mul]
        exact mul_le_mul (hC x) (sub_bd hx hy) (abs_nonneg _) ((abs_nonneg _).trans (hC x))
    have hiπ : Integrable (fun z : ℝ × ℝ => ρ z.1 * (z.2 - z.1)) π := by
      refine (hπ.2.1.norm.const_mul C).mono' hfm.aestronglyMeasurable
        (Filter.Eventually.of_forall fun z => ?_)
      rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hC _) (abs_nonneg _)
    have hiA : Integrable (fun z : ℝ × ℝ => ρ z.1 * (z.2 - z.1)) A := by
      rw [hAdef]
      exact avg_integrable θ hbm hhm hfm hb1
        (fun q => hθa.mono fun p hp => hbd _ _ (hp.2 q.1 q.2).2.1 (hp.2 q.1 q.2).2.2)
    have hiR : Integrable (fun z : ℝ × ℝ => ρ z.1 * (z.2 - z.1)) Wm := hiπ.mono_measure hR
    have heq : ∫ z : ℝ × ℝ, ρ z.1 * (z.2 - z.1) ∂A = ∫ z : ℝ × ℝ, ρ z.1 * (z.2 - z.1) ∂Wm := by
      rw [hAdef, hRdef, avg_integral_pt θ hbm hhm hfm hb1
          (fun q => hθa.mono fun p hp => hbd _ _ (hp.2 q.1 q.2).2.1 (hp.2 q.1 q.2).2.2) hb0,
        avg_integral_pt θ ham hgm hfm ha1
          (fun i => hθa.mono fun p hp => hbd _ _ (hp.2 i i).2.1 (hp.2 i i).2.2) ha0]
      refine integral_congr_ae (hθa.mono fun p hp => ?_)
      have h := hp.1.2.2.2.1
      rw [grid_eq] at h
      exact (mart_atom (fun i => p.1.1 i) (fun q : Fin n × Fin n => p.1.2 q.1 q.2)
        (fun i => p.2 i) (fun q => ((p.2 q.1).1, (p.2 q.2).2)) h ρ hρ ⟨C, hC⟩).symm
    rw [integral_add_measure (hiπ.mono_measure Measure.sub_le) hiA, heq,
      ← integral_add_measure (hiπ.mono_measure Measure.sub_le) hiR,
      Measure.sub_add_cancel_of_le hR]
    exact hπ.2.2 ρ hρ ⟨C, hC⟩
  · have hc1 : Integrable (fun z : ℝ × ℝ => c z.1 z.2) (π - Wm) := hcI.mono_measure Measure.sub_le
    have hcR : Integrable (fun z : ℝ × ℝ => c z.1 z.2) Wm := hcI.mono_measure hR
    have hbA : ∀ q : Fin n × Fin n, ∀ᵐ p ∂θ,
        |(fun z : ℝ × ℝ => c z.1 z.2) (((p.2 q.1).1, (p.2 q.2).2))| ≤ K :=
      fun q => hθa.mono fun p hp => (hp.2 q.1 q.2).1
    have hbR : ∀ i : Fin n, ∀ᵐ p ∂θ, |(fun z : ℝ × ℝ => c z.1 z.2) (p.2 i)| ≤ K :=
      fun i => hθa.mono fun p hp => (hp.2 i i).1
    have hcA : Integrable (fun z : ℝ × ℝ => c z.1 z.2) A := by
      rw [hAdef]
      exact avg_integrable θ hbm hhm hcm hb1 hbA
    have hlt : ∫ z : ℝ × ℝ, c z.1 z.2 ∂A < ∫ z : ℝ × ℝ, c z.1 z.2 ∂Wm := by
      rw [hAdef, hRdef, avg_integral θ hbm hhm hcm hb1 hbA, avg_integral θ ham hgm hcm ha1 hbR]
      refine integral_lt_of_ae_lt θ hθ0 (avg_sum_int θ hbm hhm hcm hb1 hbA)
        (avg_sum_int θ ham hgm hcm ha1 hbR) (hθa.mono fun p hp => ?_)
      have h := bad_cost_lt c hc hp.1
      have e1 : ∀ q : Fin n × Fin n, max (p.1.2 q.1 q.2) 0 = p.1.2 q.1 q.2 :=
        fun q => max_eq_left (hp.1.2.1 q.1 q.2).1
      have e2 : ∀ i, max (p.1.1 i) 0 = p.1.1 i := fun i => max_eq_left (hp.1.1 i).1
      simp only [e1, e2]
      exact h
    unfold MartOT.Var.cost
    rw [integralE_eq_coe' _ _ (hc1.add_measure hcA), integralE_eq_coe' _ _ hcI,
      EReal.coe_lt_coe_iff, integral_add_measure hc1 hcA]
    conv_rhs => rw [← Measure.sub_add_cancel_of_le hR]
    rw [integral_add_measure hc1 hcR]
    linarith

lemma key (c : ℝ → ℝ → ℝ) (hc : Measurable (Function.uncurry c)) (n : ℕ)
    (w : Fin n → ℝ) (v : Fin n → Fin n → ℝ) (z : Fin n → ℝ × ℝ)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i j, 0 ≤ v i j) :
    (IsCompetitor (tupMeas n z w) (gridMeas n z v) ∧
      cost c (gridMeas n z v) < cost c (tupMeas n z w)) ↔ Eqs c n w v z := by
  rw [grid_eq]
  unfold tupMeas
  rw [comp_iff w (fun q : Fin n × Fin n => v q.1 q.2) hw (fun q => hv q.1 q.2) z
      (fun q => ((z q.1).1, (z q.2).2)),
    cost_atom c hc (fun q : Fin n × Fin n => v q.1 q.2) (fun q => hv q.1 q.2)
      (fun q => ((z q.1).1, (z q.2).2)), cost_atom c hc w hw z, EReal.coe_lt_coe_iff]
  unfold Eqs
  simp only [and_assoc]
  exact and_congr (ar_iff (fun k => (z k).1) id Prod.fst _ _)
    (and_congr (ar_iff (fun k => (z k).2) id Prod.snd _ _)
      (and_congr (ar_iff (fun k => (z k).1) id Prod.fst _ _) Iff.rfl))

def Bad' (c : ℝ → ℝ → ℝ) (n : ℕ) : Set (Qn n × (Fin n → ℝ × ℝ)) :=
  {p | (∀ i, p.1.1 i ∈ Set.Icc (0:ℝ) 1) ∧ (∀ i j, p.1.2 i j ∈ Set.Icc (0:ℝ) 1) ∧
    ∑ i, p.1.1 i = 1 ∧ Eqs c n p.1.1 p.1.2 p.2}

lemma bad_eq (c : ℝ → ℝ → ℝ) (hc : Measurable (Function.uncurry c)) (n : ℕ) :
    Bad c n = Bad' c n := by
  ext p
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, h3, (key c hc n _ _ _ (fun i => (h1 i).1) (fun i j => (h2 i j).1)).1 h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, h3, (key c hc n _ _ _ (fun i => (h1 i).1) (fun i j => (h2 i j).1)).2 h4⟩

set_option maxHeartbeats 1000000 in
theorem badMeasurable : BadMeasurable := by
  intro c hc n
  rw [bad_eq c hc n]
  have mw : ∀ i, Measurable fun p : Qn n × (Fin n → ℝ × ℝ) => p.1.1 i := fun i => by fun_prop
  have mv : ∀ i j, Measurable fun p : Qn n × (Fin n → ℝ × ℝ) => p.1.2 i j := fun i j => by fun_prop
  have mx : ∀ i, Measurable fun p : Qn n × (Fin n → ℝ × ℝ) => (p.2 i).1 := fun i => by fun_prop
  have my : ∀ i, Measurable fun p : Qn n × (Fin n → ℝ × ℝ) => (p.2 i).2 := fun i => by fun_prop
  have mc : ∀ i j, Measurable fun p : Qn n × (Fin n → ℝ × ℝ) => c (p.2 i).1 (p.2 j).2 :=
    fun i j => hc.comp ((mx i).prodMk (my j))
  have meq : ∀ {f g : Qn n × (Fin n → ℝ × ℝ) → ℝ}, Measurable f → Measurable g →
      Measurable fun p => f p = g p := fun hf hg => measurableSet_setOfPred.1 (measurableSet_eq_fun hf hg)
  have mI : ∀ (f : Qn n × (Fin n → ℝ × ℝ) → ℝ), Measurable f →
      Measurable fun p => f p ∈ Set.Icc (0:ℝ) 1 := fun f hf => measurableSet_setOfPred.1 (hf measurableSet_Icc)
  refine measurableSet_setOfPred.2 ?_
  refine Measurable.and (Measurable.forall fun i => mI _ (mw i))
    (Measurable.and (Measurable.forall fun i => Measurable.forall fun j => mI _ (mv i j))
      (Measurable.and (meq (Finset.measurable_sum _ fun i _ => mw i) measurable_const) ?_))
  unfold Eqs
  refine Measurable.and (Measurable.forall fun k => meq ?_ ?_)
    (Measurable.and (Measurable.forall fun k => meq ?_ ?_)
      (Measurable.and (Measurable.forall fun k => meq ?_ ?_)
        (measurableSet_setOfPred.1 (measurableSet_lt ?_ ?_))))
  · exact Finset.measurable_sum _ fun i _ =>
      Measurable.ite (measurableSet_eq_fun (mx i) (mx k)) (mw i) measurable_const
  · exact Finset.measurable_sum _ fun q _ =>
      Measurable.ite (measurableSet_eq_fun (mx q.1) (mx k)) (mv q.1 q.2) measurable_const
  · exact Finset.measurable_sum _ fun i _ =>
      Measurable.ite (measurableSet_eq_fun (my i) (my k)) (mw i) measurable_const
  · exact Finset.measurable_sum _ fun q _ =>
      Measurable.ite (measurableSet_eq_fun (my q.2) (my k)) (mv q.1 q.2) measurable_const
  · exact Finset.measurable_sum _ fun i _ =>
      Measurable.ite (measurableSet_eq_fun (mx i) (mx k)) ((mw i).mul (my i)) measurable_const
  · exact Finset.measurable_sum _ fun q _ =>
      Measurable.ite (measurableSet_eq_fun (mx q.1) (mx k)) ((mv q.1 q.2).mul (my q.2))
        measurable_const
  · exact Finset.measurable_sum _ fun q _ => (mv q.1 q.2).mul (mc q.1 q.2)
  · exact Finset.measurable_sum _ fun i _ => (mw i).mul (mc i i)


/-- C3. -/
def GridReduce : Prop :=
  ∀ (c : ℝ → ℝ → ℝ), Measurable (Function.uncurry c) →
    ∀ (S : Finset (ℝ × ℝ)) (w : ℝ × ℝ → NNReal) (α' : Measure (ℝ × ℝ)),
      IsCompetitor (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) α' →
      cost c α' < cost c (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) →
      ∃ q : Qn S.card, (q, fun i => (S.equivFin.symm i : ℝ × ℝ)) ∈ Bad c S.card


lemma cost_smul_lt (c : ℝ → ℝ → ℝ) (hc : Measurable (Function.uncurry c))
    {m1 m2 : Measure (ℝ × ℝ)} [IsFiniteMeasure m1] [IsFiniteMeasure m2]
    (T1 T2 : Finset (ℝ × ℝ)) (h1 : m1 (↑T1)ᶜ = 0) (h2 : m2 (↑T2)ᶜ = 0)
    {s : ℝ≥0∞} (hs0 : s ≠ 0) (hs : s ≠ ⊤) (hlt : cost c m1 < cost c m2) :
    cost c (s • m1) < cost c (s • m2) := by
  have i1 : Integrable (fun p : ℝ × ℝ => c p.1 p.2) m1 := integrable_of_fin T1 h1 hc
  have i2 : Integrable (fun p : ℝ × ℝ => c p.1 p.2) m2 := integrable_of_fin T2 h2 hc
  unfold cost at *
  rw [integralE_eq_coe' _ _ i1, integralE_eq_coe' _ _ i2] at hlt
  rw [integralE_eq_coe' _ _ (i1.smul_measure hs), integralE_eq_coe' _ _ (i2.smul_measure hs),
    integral_smul_measure, integral_smul_measure, EReal.coe_lt_coe_iff]
  have hlt' := EReal.coe_lt_coe_iff.1 hlt
  have hpos : 0 < s.toReal := ENNReal.toReal_pos hs0 hs
  simp only [smul_eq_mul]
  exact mul_lt_mul_of_pos_left hlt' hpos

lemma meas_eq_of_singletons {m1 m2 : Measure (ℝ × ℝ)} (T : Finset (ℝ × ℝ))
    (h1 : m1 (↑T)ᶜ = 0) (h2 : m2 (↑T)ᶜ = 0) (h : ∀ t ∈ T, m1 {t} = m2 {t}) : m1 = m2 := by
  classical
  ext A hA
  have key : ∀ m : Measure (ℝ × ℝ), m (↑T)ᶜ = 0 → m A = ∑ t ∈ T.filter (· ∈ A), m {t} := by
    intro m hm
    have e : (↑(T.filter (· ∈ A)) : Set (ℝ × ℝ)) = A ∩ ↑T := by ext x; simp [and_comm]
    rw [sum_measure_singleton, e, measure_inter_conull hm]
  rw [key m1 h1, key m2 h2]
  exact Finset.sum_congr rfl (fun t ht => h t (Finset.mem_filter.1 ht).1)

lemma comp_smul {α α' : Measure (ℝ × ℝ)} (h : IsCompetitor α α') {s : ℝ≥0∞} (hs : s ≠ ⊤) :
    IsCompetitor (s • α) (s • α') := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨?_, ?_, h3.smul_measure hs, h4.smul_measure hs, ?_⟩
  · rw [Measure.map_smul, Measure.map_smul, h1]
  · rw [Measure.map_smul, Measure.map_smul, h2]
  · intro ρ hρ hb
    rw [integral_smul_measure, integral_smul_measure, h5 ρ hρ hb]

/-- first occurrence of a value of `f`. -/
lemma first_unique {n : ℕ} (f : Fin n → ℝ) (a : ℝ) (ha : ∃ i, f i = a) :
    ∃ i0, f i0 = a ∧ ∀ i, ((∀ i' < i, f i' ≠ f i) ∧ f i = a ↔ i = i0) := by
  classical
  have hne : (Finset.univ.filter (fun i => f i = a)).Nonempty := by
    obtain ⟨i, hi⟩ := ha; exact ⟨i, by simp [hi]⟩
  set i0 := (Finset.univ.filter (fun i => f i = a)).min' hne
  have hi0 : f i0 = a := (Finset.mem_filter.1 (Finset.min'_mem _ hne)).2
  have hle : ∀ i, f i = a → i0 ≤ i := fun i hi => Finset.min'_le _ _ (by simp [hi])
  refine ⟨i0, hi0, fun i => ⟨fun ⟨hP, hi⟩ => ?_, fun h => ?_⟩⟩
  · rcases (hle i hi).lt_or_eq with hlt | heq
    · exact absurd (hi0.trans hi.symm) (hP i0 hlt)
    · exact heq.symm
  · subst h
    refine ⟨fun i' hi' heq => ?_, hi0⟩
    exact absurd (hle i' (heq.trans hi0)) (not_le.2 hi')

set_option maxHeartbeats 1000000 in
theorem gridReduce : GridReduce := by
  classical
  intro c hc S w α' hα' hlt
  set α : Measure (ℝ × ℝ) := ∑ p ∈ S, (w p : ℝ≥0∞) • Measure.dirac p with hαdef
  set n := S.card
  set e := S.equivFin
  set z : Fin n → ℝ × ℝ := fun i => (e.symm i : ℝ × ℝ) with hz
  set Wn : ℝ≥0 := ∑ p ∈ S, w p with hWn
  have hαuniv : α Set.univ = (Wn : ℝ≥0∞) := by
    simp [α, Wn]
  have hα'univ : α' Set.univ = (Wn : ℝ≥0∞) := by
    rw [← hαuniv, ← Set.preimage_univ (f := Prod.fst), ← Measure.map_apply measurable_fst MeasurableSet.univ,
      ← Measure.map_apply measurable_fst MeasurableSet.univ, hα'.1]
  have : IsFiniteMeasure α := ⟨by rw [hαuniv]; exact ENNReal.coe_lt_top⟩
  have : IsFiniteMeasure α' := ⟨by rw [hα'univ]; exact ENNReal.coe_lt_top⟩
  -- the zero-mass case
  by_cases hW0 : Wn = 0
  · exfalso
    have h0 : α = 0 := Measure.measure_univ_eq_zero.1 (by rw [hαuniv, hW0]; rfl)
    have h0' : α' = 0 := Measure.measure_univ_eq_zero.1 (by rw [hα'univ, hW0]; rfl)
    rw [h0, h0'] at hlt
    exact lt_irrefl _ hlt
  have hWpos : (0 : ℝ) < (Wn : ℝ) := by
    have := pos_iff_ne_zero.2 hW0; exact_mod_cast this
  set W : ℝ := (Wn : ℝ) with hWdef
  set s : ℝ≥0∞ := (Wn : ℝ≥0∞)⁻¹ with hsdef
  have hs0 : s ≠ 0 := ENNReal.inv_ne_zero.2 ENNReal.coe_ne_top
  have hstop : s ≠ ⊤ := ENNReal.inv_ne_top.2 (by exact_mod_cast hW0)
  have hofW : ENNReal.ofReal W = (Wn : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal
  -- supports
  set X : Finset ℝ := S.image Prod.fst
  set Y : Finset ℝ := S.image Prod.snd
  set T : Finset (ℝ × ℝ) := X ×ˢ Y
  have hαS : α (↑S)ᶜ = 0 := by
    simp only [α, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
    refine Finset.sum_eq_zero (fun p hp => ?_)
    rw [Measure.dirac_apply, Set.indicator_of_notMem (by simpa using hp), mul_zero]
  have hST : (↑S : Set (ℝ × ℝ)) ⊆ ↑T := fun p hp => by
    simp only [T, X, Y, Finset.coe_product, Set.mem_prod, Finset.mem_coe]
    exact ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩
  have hαT : α (↑T)ᶜ = 0 := measure_mono_null (Set.compl_subset_compl.2 hST) hαS
  have hα'T : α' (↑T)ᶜ = 0 := by
    have hsub : (↑T : Set (ℝ × ℝ))ᶜ ⊆ Prod.fst ⁻¹' (↑X : Set ℝ)ᶜ ∪ Prod.snd ⁻¹' (↑Y : Set ℝ)ᶜ := by
      intro p hp
      simp only [T, Finset.coe_product, Set.mem_compl_iff, Set.mem_prod, not_and_or] at hp
      exact hp
    refine measure_mono_null hsub (measure_union_null ?_ ?_)
    · rw [← Measure.map_apply measurable_fst (Finset.measurableSet _).compl, ← hα'.1,
        Measure.map_apply measurable_fst (Finset.measurableSet _).compl]
      exact measure_mono_null (show Prod.fst ⁻¹' (↑X : Set ℝ)ᶜ ⊆ (↑S : Set (ℝ × ℝ))ᶜ from
        fun p hp hpS => hp (Finset.mem_image_of_mem _ hpS)) hαS
    · rw [← Measure.map_apply measurable_snd (Finset.measurableSet _).compl, ← hα'.2.1,
        Measure.map_apply measurable_snd (Finset.measurableSet _).compl]
      exact measure_mono_null (show Prod.snd ⁻¹' (↑Y : Set ℝ)ᶜ ⊆ (↑S : Set (ℝ × ℝ))ᶜ from
        fun p hp hpS => hp (Finset.mem_image_of_mem _ hpS)) hαS
  -- parameters
  set x : Fin n → ℝ := fun i => (z i).1
  set y : Fin n → ℝ := fun i => (z i).2
  let P : Fin n → Prop := fun i => ∀ i' < i, x i' ≠ x i
  let Q : Fin n → Prop := fun j => ∀ j' < j, y j' ≠ y j
  let w' : Fin n → ℝ := fun i => (w (z i) : ℝ) / W
  let v : Fin n → Fin n → ℝ := fun i j =>
    if P i ∧ Q j then (α' {(x i, y j)}).toReal / W else 0
  have hzS : ∀ i, z i ∈ S := fun i => (e.symm i).2
  have hzT : ∀ i j, (x i, y j) ∈ T := fun i j => by
    simp only [T, X, Y, Finset.mem_product]
    exact ⟨Finset.mem_image_of_mem _ (hzS i), Finset.mem_image_of_mem _ (hzS j)⟩
  have hsum : ∑ i, (w (z i) : ℝ) = W := by
    rw [hWdef, hWn, NNReal.coe_sum, ← Finset.sum_coe_sort S]
    exact Fintype.sum_equiv e.symm _ _ (fun i => rfl)
  have hofr : ∀ a : ℝ≥0∞, a ≠ ⊤ → ENNReal.ofReal (a.toReal / W) = a * s := fun a ha => by
    rw [ENNReal.ofReal_div_of_pos hWpos, ENNReal.ofReal_toReal ha, hofW, div_eq_mul_inv]
  have htup : tupMeas n z w' = s • α := by
    unfold tupMeas
    simp only [α, Finset.smul_sum, smul_smul]
    rw [← Finset.sum_coe_sort S]
    refine Fintype.sum_equiv e.symm _ _ (fun i => ?_)
    congr 1
    have := hofr (w (z i) : ℝ≥0∞) ENNReal.coe_ne_top
    simp only [ENNReal.coe_toReal] at this
    rw [this, mul_comm]
  have hgrid : gridMeas n z v = s • α' := by
    refine meas_eq_of_singletons T ?_ ?_ ?_
    · unfold gridMeas
      simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
      refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => ?_))
      rw [Measure.dirac_apply, Set.indicator_of_notMem (by simpa using hzT i j), mul_zero]
    · rw [Measure.smul_apply, hα'T, smul_zero]
    · intro t ht
      obtain ⟨a, b⟩ := t
      simp only [T, X, Y, Finset.mem_product, Finset.mem_image] at ht
      obtain ⟨⟨pa, hpa, hpa'⟩, ⟨pb, hpb, hpb'⟩⟩ := ht
      obtain ⟨i0, hi0, hiff⟩ := first_unique x a ⟨e ⟨pa, hpa⟩, by simp [x, z, hpa']⟩
      obtain ⟨j0, hj0, hjff⟩ := first_unique y b ⟨e ⟨pb, hpb⟩, by simp [y, z, hpb']⟩
      have term : ∀ i j, ENNReal.ofReal (v i j) * Measure.dirac (x i, y j) {(a, b)} =
          if i = i0 then (if j = j0 then s * α' {(a, b)} else 0) else 0 := by
        intro i j
        by_cases hij : (x i, y j) = (a, b)
        · rw [Measure.dirac_apply_of_mem (by simp [hij]), mul_one]
          simp only [Prod.mk.injEq] at hij
          by_cases hii : i = i0
          · by_cases hjj : j = j0
            · have hPQ : P i ∧ Q j := ⟨((hiff i).2 hii).1, ((hjff j).2 hjj).1⟩
              simp only [v, if_pos hPQ, if_pos hii, if_pos hjj]
              rw [hofr _ (measure_ne_top _ _), hij.1, hij.2, mul_comm]
            · have hQ : ¬ Q j := fun hq => hjj ((hjff j).1 ⟨hq, hij.2⟩)
              simp [v, hQ, hii, hjj]
          · have hP : ¬ P i := fun hp => hii ((hiff i).1 ⟨hp, hij.1⟩)
            simp [v, hP, hii]
        · rw [Measure.dirac_apply, Set.indicator_of_notMem (by simpa using hij), mul_zero]
          by_cases hii : i = i0
          · by_cases hjj : j = j0
            · exfalso; apply hij; rw [hii, hjj, hi0, hj0]
            · simp [hii, hjj]
          · simp [hii]
      unfold gridMeas
      simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
      exact (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => term i j).trans
        (by simp)
  refine ⟨(w', v), ?_⟩
  refine ⟨fun i => ⟨div_nonneg (w (z i)).2 hWpos.le, ?_⟩, fun i j => ?_, ?_, ?_, ?_⟩
  · rw [div_le_one hWpos, hWdef, hWn, NNReal.coe_sum]
    exact Finset.single_le_sum (f := fun p => (w p : ℝ)) (fun p _ => (w p).2) (hzS i)
  · show v i j ∈ Set.Icc (0:ℝ) 1
    simp only [v]
    split_ifs
    · refine ⟨div_nonneg ENNReal.toReal_nonneg hWpos.le, (div_le_one hWpos).2 ?_⟩
      have h1 : α' {(x i, y j)} ≤ (Wn : ℝ≥0∞) := hα'univ ▸ measure_mono (Set.subset_univ _)
      have h2 := ENNReal.toReal_mono ENNReal.coe_ne_top h1
      simpa using h2
    · exact ⟨le_refl 0, zero_le_one⟩
  · show ∑ i, w' i = 1
    simp only [w']
    rw [← Finset.sum_div, hsum, div_self hWpos.ne']
  · show IsCompetitor (tupMeas n z w') (gridMeas n z v)
    rw [htup, hgrid]; exact comp_smul hα' hstop
  · show cost c (gridMeas n z v) < cost c (tupMeas n z w')
    rw [htup, hgrid]
    exact cost_smul_lt c hc T T hα'T hαT hs0 hstop hlt

/-- C1 (Kellerer's lemma with a compact parameter). -/
def KellererParam : Prop :=
  ∀ (Q : Type) [TopologicalSpace Q] [PolishSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (n : ℕ) (π : Measure (ℝ × ℝ)), IsFiniteMeasure π →
    ∀ C : Set Q, IsCompact C → ∀ B : Set (Q × (Fin n → ℝ × ℝ)), MeasurableSet B →
      (∀ p ∈ B, p.1 ∈ C) →
      (∃ N : Set (ℝ × ℝ), MeasurableSet N ∧ π N = 0 ∧ ∀ p ∈ B, ∃ i, p.2 i ∈ N) ∨
      (∃ ξ : Measure (Q × (Fin n → ℝ × ℝ)), IsFiniteMeasure ξ ∧ ξ Bᶜ = 0 ∧ ξ ≠ 0 ∧
        ∀ i, ξ.map (fun p => p.2 i) ≤ π)

lemma cube_compact (n : ℕ) :
    IsCompact ((Set.univ.pi fun _ : Fin n => Set.Icc (0:ℝ) 1) ×ˢ
      (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => Set.Icc (0:ℝ) 1)) :=
  (isCompact_univ_pi fun _ => isCompact_Icc).prod
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc)

theorem assemble (h1 : KellererParam) (h2 : BadMeasurable) (h3 : GridReduce) (h4 : Improve)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (c : ℝ → ℝ → ℝ) (hc : Measurable (Function.uncurry c))
    (hint : SuffIntegrable μ ν c) (π : Measure (ℝ × ℝ)) (hπ : IsOptimal c μ ν π)
    (hfin : cost c π < ⊤) :
    ∃ Γ : Set (ℝ × ℝ), MeasurableSet Γ ∧ π Γᶜ = 0 ∧
      ∀ (S : Finset (ℝ × ℝ)) (w : ℝ × ℝ → NNReal), (↑S : Set (ℝ × ℝ)) ⊆ Γ →
        ∀ α' : Measure (ℝ × ℝ),
          IsCompetitor (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) α' →
          cost c (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) ≤ cost c α' := by
  have hfinπ : IsFiniteMeasure π := by
    have h := hπ.1.1.1
    refine ⟨?_⟩
    have : π Set.univ = (π.map Prod.fst) Set.univ := by
      rw [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ]
    rw [this, h]; exact measure_lt_top μ _
  have hN : ∀ n : ℕ, ∃ N : Set (ℝ × ℝ), MeasurableSet N ∧ π N = 0 ∧
      ∀ p ∈ Bad c n, ∃ i, p.2 i ∈ N := by
    intro n
    have hBC : ∀ p ∈ Bad c n, p.1 ∈ ((Set.univ.pi fun _ : Fin n => Set.Icc (0:ℝ) 1) ×ˢ
        (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => Set.Icc (0:ℝ) 1)) := by
      intro p hp
      exact ⟨Set.mem_univ_pi.2 hp.1, Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 (hp.2.1 i)⟩
    rcases h1 (Qn n) n π hfinπ _ (cube_compact n) (Bad c n) (h2 c hc n) hBC with h | ⟨ξ, hξf, hξB, hξ0, hξm⟩
    · exact h
    · exfalso
      obtain ⟨π', hπ', hlt⟩ := h4 μ ν inferInstance inferInstance c hc hint π hπ.1 hfin n ξ hξf
        hξB hξ0 hξm
      exact absurd (hπ.2 π' hπ') (not_le.2 hlt)
  choose N hNm hN0 hNc using hN
  refine ⟨(⋃ n, N n)ᶜ, (MeasurableSet.iUnion hNm).compl, ?_, ?_⟩
  · rw [compl_compl]; exact measure_iUnion_null hN0
  · intro S w hS α' hα'
    by_contra hlt
    obtain ⟨q, hq⟩ := h3 c hc S w α' hα' (not_le.1 hlt)
    obtain ⟨i, hi⟩ := hNc S.card _ hq
    have hmem : ((S.equivFin.symm i : ℝ × ℝ)) ∈ (↑S : Set (ℝ × ℝ)) := (S.equivFin.symm i).2
    exact hS hmem (Set.mem_iUnion.2 ⟨S.card, hi⟩)


/-- Lemma 1.11 from Kellerer's lemma (C1); C2, C3, C4 are proved above. -/
theorem of_kellerer (h1 : KellererParam)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (c : ℝ → ℝ → ℝ) (hc : Measurable (Function.uncurry c))
    (hint : SuffIntegrable μ ν c) (π : Measure (ℝ × ℝ)) (hπ : IsOptimal c μ ν π)
    (hfin : cost c π < ⊤) :
    ∃ Γ : Set (ℝ × ℝ), MeasurableSet Γ ∧ π Γᶜ = 0 ∧
      ∀ (S : Finset (ℝ × ℝ)) (w : ℝ × ℝ → NNReal), (↑S : Set (ℝ × ℝ)) ⊆ Γ →
        ∀ α' : Measure (ℝ × ℝ),
          IsCompetitor (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) α' →
          cost c (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) ≤ cost c α' :=
  assemble h1 badMeasurable gridReduce improve4 μ ν c hc hint π hπ hfin

/-- dual feasibility: `∑ f_i(x_i) ≥ 1` on `B`. -/
def DualFeas {Q : Type} {n : ℕ} (B : Set (Q × (Fin n → ℝ × ℝ)))
    (f : Fin n → ℝ × ℝ → ℝ≥0∞) : Prop :=
  (∀ i, Measurable (f i)) ∧ ∀ p ∈ B, 1 ≤ ∑ i, f i (p.2 i)

/-- C1-core (Kellerer 1984, duality for Borel sets): positive dual value gives a primal measure. -/
def KellererDual : Prop :=
  ∀ (Q : Type) [TopologicalSpace Q] [PolishSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (n : ℕ) (π : Measure (ℝ × ℝ)), IsFiniteMeasure π →
    ∀ C : Set Q, IsCompact C → ∀ B : Set (Q × (Fin n → ℝ × ℝ)), MeasurableSet B →
      (∀ p ∈ B, p.1 ∈ C) →
      (∃ ε : ℝ≥0∞, 0 < ε ∧ ∀ f, DualFeas B f → ε ≤ ∑ i, ∫⁻ x, f i x ∂π) →
      (∃ ξ : Measure (Q × (Fin n → ℝ × ℝ)), IsFiniteMeasure ξ ∧ ξ Bᶜ = 0 ∧ ξ ≠ 0 ∧
        ∀ i, ξ.map (fun p => p.2 i) ≤ π)

lemma null_cover {Q : Type} {n : ℕ} (π : Measure (ℝ × ℝ)) (B : Set (Q × (Fin n → ℝ × ℝ)))
    (h : ∀ ε : ℝ≥0∞, 0 < ε → ∃ f, DualFeas B f ∧ ∑ i, ∫⁻ x, f i x ∂π < ε) :
    ∃ N : Set (ℝ × ℝ), MeasurableSet N ∧ π N = 0 ∧ ∀ p ∈ B, ∃ i, p.2 i ∈ N := by
  have hk : ∀ k : ℕ, ∃ f, DualFeas B f ∧ ∑ i, ∫⁻ x, f i x ∂π < (2⁻¹ : ℝ≥0∞) ^ (k + 1) :=
    fun k => h _ (ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) _)
  choose f hfB hfs using hk
  have hFm : ∀ i, Measurable (fun x => ∑' k, f k i x) :=
    fun i => Measurable.ennreal_tsum fun k => (hfB k).1 i
  have hgeom : ∑' k : ℕ, (2⁻¹ : ℝ≥0∞) ^ (k + 1) ≠ ⊤ := by
    simp_rw [pow_succ, ENNReal.tsum_mul_right, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two,
      inv_inv]
    exact ENNReal.mul_ne_top (by simp) (by simp)
  have hFint : ∀ i, ∫⁻ x, (∑' k, f k i x) ∂π ≠ ⊤ := by
    intro i
    rw [lintegral_tsum fun k => ((hfB k).1 i).aemeasurable]
    refine ne_top_of_le_ne_top hgeom (ENNReal.tsum_le_tsum fun k => ?_)
    exact le_trans (Finset.single_le_sum (f := fun j => ∫⁻ x, f k j x ∂π)
      (fun _ _ => by positivity) (Finset.mem_univ i)) (hfs k).le
  refine ⟨⋃ i, {x | ∑' k, f k i x = ⊤}, MeasurableSet.iUnion fun i =>
    (hFm i) (measurableSet_singleton _), measure_iUnion_null fun i => ?_, ?_⟩
  · have h0 := ae_iff.1 (ae_lt_top (hFm i) (hFint i))
    simpa [lt_top_iff_ne_top] using h0
  · intro p hp
    have hsum : ∑ i, ∑' k, f k i (p.2 i) = ⊤ := by
      rw [← Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]
      refine eq_top_iff.2 (le_trans (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).ge
        (ENNReal.tsum_le_tsum fun k => (hfB k).2 p hp))
    obtain ⟨i, -, hi⟩ := ENNReal.sum_eq_top.1 hsum
    exact ⟨i, Set.mem_iUnion.2 ⟨i, hi⟩⟩

theorem kellerer_of_dual (hD : KellererDual) : KellererParam := by
  intro Q _ _ _ _ n π hπ C hC B hB hBC
  by_cases h : ∀ ε : ℝ≥0∞, 0 < ε → ∃ f, DualFeas B f ∧ ∑ i, ∫⁻ x, f i x ∂π < ε
  · exact Or.inl (null_cover π B h)
  · push_neg at h
    exact Or.inr (hD Q n π hπ C hC B hB hBC h)

open MeasureTheory Set Topology
open scoped ENNReal NNReal BoundedContinuousFunction CompactlySupported Pointwise

section Choquet

variable {α : Type*} [TopologicalSpace α]

/-- sequences bounded by `b` on the first `k` coordinates. -/
def pref (b : ℕ → ℕ) (k : ℕ) : Set (ℕ → ℕ) := {x | ∀ j < k, x j ≤ b j}

lemma pref_isClosed (b : ℕ → ℕ) (k : ℕ) : IsClosed (pref b k) := by
  have : pref b k = ⋂ j ∈ Finset.range k, (fun x : ℕ → ℕ => x j) ⁻¹' Iic (b j) := by
    ext x; simp [pref]
  rw [this]
  exact isClosed_biInter fun j _ => (isClosed_discrete _).preimage (continuous_apply j)

lemma pref_antitone (b : ℕ → ℕ) {k k' : ℕ} (h : k ≤ k') : pref b k' ⊆ pref b k :=
  fun _ hx j hj => hx j (lt_of_lt_of_le hj h)

lemma pref_succ_union (b : ℕ → ℕ) (k : ℕ) :
    pref b k = ⋃ m, pref (Function.update b k m) (k + 1) := by
  ext x; simp only [pref, mem_ofPred_eq, mem_iUnion]
  constructor
  · intro h
    refine ⟨x k, fun j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · simpa [Function.update_apply, hj.ne] using h j hj
    · simp
  · rintro ⟨m, h⟩ j hj
    simpa [Function.update_apply, hj.ne] using h j (Nat.lt_succ_of_lt hj)

/-- the recursively chosen bounds. -/
def bseq (step : (ℕ → ℕ) → ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0 => fun _ => 0
  | k + 1 => Function.update (bseq step k) k (step (bseq step k) k)

lemma bseq_stable (step : (ℕ → ℕ) → ℕ → ℕ) :
    ∀ k j, j < k → bseq step k j = bseq step (j + 1) j := by
  intro k
  induction k with
  | zero => intro j hj; omega
  | succ k ih =>
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · show Function.update (bseq step k) k (step (bseq step k) k) j = _
      rw [Function.update_apply, if_neg hj.ne]; exact ih j hj
    · rfl

lemma pref_bseq (step : (ℕ → ℕ) → ℕ → ℕ) (k : ℕ) :
    pref (bseq step k) k = pref (fun j => bseq step (j + 1) j) k := by
  ext x; simp only [pref, mem_ofPred_eq]
  exact forall₂_congr fun j hj => by rw [bseq_stable step k j hj]

set_option maxHeartbeats 1000000 in
/-- **Choquet's capacitability theorem** for analytic sets. -/
theorem choquet (I : Set α → ℝ≥0∞) (hmono : ∀ A B, A ⊆ B → I A ≤ I B)
    (hup : ∀ A : ℕ → Set α, Monotone A → I (⋃ m, A m) ≤ ⨆ m, I (A m))
    (hout : ∀ (A : Set α) (t : ℝ≥0∞), I A < t → ∃ U, IsOpen U ∧ A ⊆ U ∧ I U < t)
    (A : Set α) (hA : AnalyticSet A) (t : ℝ≥0∞) (ht : t < I A) :
    ∃ K, IsCompact K ∧ K ⊆ A ∧ t < I K := by
  rw [AnalyticSet] at hA
  rcases hA with rfl | ⟨f, hf, rfl⟩
  · exact ⟨∅, isCompact_empty, subset_rfl, ht⟩
  obtain ⟨t₁, htt₁, ht₁⟩ := exists_between ht
  have hstep : ∀ (b : ℕ → ℕ) (k : ℕ), ∃ m, t₁ < I (f '' pref b k) →
      t₁ < I (f '' pref (Function.update b k m) (k + 1)) := by
    intro b k
    by_contra hcon
    push Not at hcon
    have h0 := (hcon 0).1
    have hmonoA : Monotone fun m => f '' pref (Function.update b k m) (k + 1) := by
      intro m m' hmm x hx
      obtain ⟨y, hy, rfl⟩ := hx
      refine ⟨y, fun j hj => ?_, rfl⟩
      have := hy j hj
      by_cases hjk : j = k
      · subst hjk; simp only [Function.update_self] at this ⊢; omega
      · simpa [Function.update_apply, hjk] using this
    have hU := hup _ hmonoA
    rw [← image_iUnion, ← pref_succ_union] at hU
    exact lt_irrefl _ (lt_of_lt_of_le h0 (hU.trans (iSup_le fun m => (hcon m).2)))
  choose step hstep using hstep
  have hinv : ∀ k, t₁ < I (f '' pref (bseq step k) k) := by
    intro k
    induction k with
    | zero =>
      have : pref (bseq step 0) 0 = univ := by ext x; simp [pref]
      rw [this, image_univ]; exact ht₁
    | succ k ih => exact hstep (bseq step k) k ih
  set bs : ℕ → ℕ := fun j => bseq step (j + 1) j with hbs
  set P : Set (ℕ → ℕ) := univ.pi fun j => Iic (bs j) with hP
  have hPc : IsCompact P := isCompact_univ_pi fun j => (finite_Iic _).isCompact
  set K := f '' P with hK
  have hKc : IsCompact K := hPc.image hf
  refine ⟨K, hKc, image_subset_range _ _, lt_of_lt_of_le htt₁ (not_lt.1 fun hK1 => ?_)⟩
  obtain ⟨U, hUo, hKU, hIU⟩ := hout K t₁ hK1
  have hex : ∃ k, f '' pref bs k ⊆ U := by
    by_contra hno
    push Not at hno
    have hx : ∀ k, ∃ x ∈ pref bs k, f x ∉ U := by
      intro k
      obtain ⟨y, ⟨x, hx, rfl⟩, hy⟩ := not_subset.1 (hno k)
      exact ⟨x, hx, hy⟩
    choose x hxp hxU using hx
    set T : Set (ℕ → ℕ) := univ.pi fun j =>
      Iic (max (bs j) ((Finset.range (j + 1)).sup fun k => x k j)) with hT
    have hTc : IsCompact T := isCompact_univ_pi fun j => (finite_Iic _).isCompact
    have hxT : ∀ k, x k ∈ T := by
      intro k
      simp only [hT, mem_pi, mem_univ, mem_Iic, forall_true_left]
      intro j
      by_cases hkj : k ≤ j
      · exact le_max_of_le_right (Finset.le_sup (f := fun k => x k j)
          (Finset.mem_range.2 (by omega)))
      · exact le_max_of_le_left (hxp k j (by omega))
    have hF := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      (fun k => T ∩ (f ⁻¹' Uᶜ ∩ pref bs k))
      (fun a b => ⟨max a b,
        fun y hy => ⟨hy.1, hy.2.1, pref_antitone bs (le_max_left a b) hy.2.2⟩,
        fun y hy => ⟨hy.1, hy.2.1, pref_antitone bs (le_max_right a b) hy.2.2⟩⟩)
      (fun k => ⟨x k, hxT k, hxU k, hxp k⟩)
      (fun k => hTc.inter_right ((hUo.isClosed_compl.preimage hf).inter (pref_isClosed bs k)))
      (fun k => hTc.isClosed.inter ((hUo.isClosed_compl.preimage hf).inter (pref_isClosed bs k)))
    obtain ⟨y, hy⟩ := hF
    rw [mem_iInter] at hy
    have hyP : y ∈ P := by
      simp only [hP, mem_pi, mem_univ, mem_Iic, forall_true_left]
      intro j
      exact (hy (j + 1)).2.2 j (Nat.lt_succ_self j)
    exact (hy 0).2.1 (hKU ⟨y, hyP, rfl⟩)
  obtain ⟨k, hk⟩ := hex
  have h1 := hinv k
  rw [pref_bseq] at h1
  exact lt_irrefl _ (lt_of_lt_of_le h1 ((hmono _ _ hk).trans hIU.le))

end Choquet

/-- the dual capacity. -/
noncomputable def cap {Q : Type} {n : ℕ} (π : Measure (ℝ × ℝ))
    (A : Set (Q × (Fin n → ℝ × ℝ))) : ℝ≥0∞ :=
  ⨅ (f : Fin n → ℝ × ℝ → ℝ≥0∞) (_ : DualFeas A f), ∑ i, ∫⁻ x, f i x ∂π

lemma cap_mono {Q : Type} {n : ℕ} (π : Measure (ℝ × ℝ)) {A B : Set (Q × (Fin n → ℝ × ℝ))}
    (h : A ⊆ B) : cap π A ≤ cap π B :=
  iInf_mono fun _ => iInf_mono' fun hf => ⟨⟨hf.1, fun p hp => hf.2 p (h hp)⟩, le_rfl⟩

lemma cap_le {Q : Type} {n : ℕ} (π : Measure (ℝ × ℝ)) {A : Set (Q × (Fin n → ℝ × ℝ))}
    {f : Fin n → ℝ × ℝ → ℝ≥0∞} (hf : DualFeas A f) : cap π A ≤ ∑ i, ∫⁻ x, f i x ∂π :=
  iInf₂_le f hf

/-- outer regularity of the dual capacity (Vitali–Carathéodory). -/
lemma cap_outer {Q : Type} [TopologicalSpace Q] {n : ℕ} (π : Measure (ℝ × ℝ))
    [IsFiniteMeasure π] (A : Set (Q × (Fin n → ℝ × ℝ))) (t : ℝ≥0∞) (ht : cap π A < t) :
    ∃ U, IsOpen U ∧ A ⊆ U ∧ cap π U < t := by
  obtain ⟨f, hfA, hft⟩ : ∃ f, DualFeas A f ∧ ∑ i, ∫⁻ x, f i x ∂π < t := by
    simpa [cap, iInf_lt_iff] using ht
  obtain ⟨r, hr0, hr⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 hft
  set c : ℝ≥0∞ := π univ with hc
  have hcT : c ≠ ⊤ := measure_ne_top π univ
  set D : ℝ≥0∞ := (n : ℝ≥0∞) * (c + 1) + 1 with hD
  have hD0 : D ≠ 0 := by simp [hD]
  have hDT : D ≠ ⊤ := by
    simp only [hD]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by simp) (ENNReal.add_ne_top.2 ⟨hcT, by simp⟩),
      by simp⟩
  set η : ℝ≥0∞ := (r : ℝ≥0∞) / D with hη
  have hη0 : η ≠ 0 := ENNReal.div_ne_zero.2 ⟨by exact_mod_cast hr0.ne', hDT⟩
  have hηT : η ≠ ⊤ := ENNReal.div_ne_top (by simp) hD0
  have hsmall : (n : ℝ≥0∞) * (η * (c + 1)) ≤ r := by
    calc (n : ℝ≥0∞) * (η * (c + 1)) = η * ((n : ℝ≥0∞) * (c + 1)) := by ring
      _ ≤ η * D := by gcongr; simp [hD]
      _ = r := ENNReal.div_mul_cancel hD0 hDT
  have hg : ∀ i, ∃ g : ℝ × ℝ → ℝ≥0∞, (∀ x, f i x + η ≤ g x) ∧ LowerSemicontinuous g ∧
      ∫⁻ x, g x ∂π ≤ ∫⁻ x, f i x + η ∂π + η :=
    fun i => exists_le_lowerSemicontinuous_lintegral_ge π (fun x => f i x + η)
      ((hfA.1 i).add measurable_const) hη0
  choose g hfg hglsc hgint using hg
  have hsum_lsc : LowerSemicontinuous fun p : Q × (Fin n → ℝ × ℝ) => ∑ i, g i (p.2 i) :=
    lowerSemicontinuous_sum fun i _ =>
      (hglsc i).comp ((continuous_apply i).comp continuous_snd)
  refine ⟨(fun p : Q × (Fin n → ℝ × ℝ) => ∑ i, g i (p.2 i)) ⁻¹' Ioi 1,
    hsum_lsc.isOpen_preimage 1, ?_, ?_⟩
  · intro p hp
    have h1 := hfA.2 p hp
    have hn : n ≠ 0 := by
      rintro rfl
      simp at h1
    show 1 < ∑ i, g i (p.2 i)
    calc (1 : ℝ≥0∞) < 1 + (n : ℝ≥0∞) * η :=
          ENNReal.lt_add_right (by simp) (mul_ne_zero (by exact_mod_cast hn) hη0)
      _ ≤ ∑ i, f i (p.2 i) + (n : ℝ≥0∞) * η := by gcongr
      _ = ∑ i, (f i (p.2 i) + η) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
      _ ≤ ∑ i, g i (p.2 i) := Finset.sum_le_sum fun i _ => hfg i _
  · refine lt_of_le_of_lt (cap_le π ⟨fun i => (hglsc i).measurable, fun p hp => le_of_lt hp⟩) ?_
    refine lt_of_le_of_lt ?_ hr
    calc ∑ i, ∫⁻ x, g i x ∂π ≤ ∑ i, (∫⁻ x, f i x ∂π + η * (c + 1)) := by
          refine Finset.sum_le_sum fun i _ => (hgint i).trans (le_of_eq ?_)
          rw [lintegral_add_right _ measurable_const, lintegral_const, hc]
          ring
      _ = ∑ i, ∫⁻ x, f i x ∂π + (n : ℝ≥0∞) * (η * (c + 1)) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
      _ ≤ ∑ i, ∫⁻ x, f i x ∂π + r := by gcongr

section CompactDual

variable {Z : Type*} [TopologicalSpace Z] [CompactSpace Z] [T2Space Z]
  {n : ℕ} (π : Measure (ℝ × ℝ)) (e : Fin n → Z → ℝ × ℝ)

/-- costs of continuous dual-feasible families dominating `φ`. -/
def feasC (φ : Z → ℝ) : Set ℝ :=
  {a | ∃ f : Fin n → (ℝ × ℝ →ᵇ ℝ), (∀ i x, 0 ≤ f i x) ∧ (∀ z, φ z ≤ ∑ i, f i (e i z)) ∧
    a = ∑ i, ∫ x, f i x ∂π}

lemma feasC_nonneg {φ : Z → ℝ} {a : ℝ} (ha : a ∈ feasC π e φ) : 0 ≤ a := by
  obtain ⟨f, hf0, -, rfl⟩ := ha
  exact Finset.sum_nonneg fun i _ => integral_nonneg (hf0 i)

lemma feasC_bdd (φ : Z → ℝ) : BddBelow (feasC π e φ) := ⟨0, fun _ ha => feasC_nonneg π e ha⟩

lemma feasC_nonempty (hn : n ≠ 0) (φ : Z → ℝ) (hφ : Continuous φ) :
    (feasC π e φ).Nonempty := by
  obtain ⟨C, hC⟩ := (isCompact_range hφ).bddAbove
  let i0 : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
  refine ⟨_, ⟨fun i => BoundedContinuousFunction.const _ (if i = i0 then max C 0 else 0),
    fun i x => ?_, fun z => ?_, rfl⟩⟩
  · simp only [BoundedContinuousFunction.const_apply]
    split_ifs <;> simp
  · simp only [BoundedContinuousFunction.const_apply, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    exact (hC ⟨z, rfl⟩).trans (le_max_left _ _)

lemma N_smul {c : ℝ} (hc : 0 < c) (φ : Z → ℝ) :
    sInf (feasC π e (c • φ)) = c * sInf (feasC π e φ) := by
  have hset : feasC π e (c • φ) = c • feasC π e φ := by
    ext a
    simp only [Set.mem_smul_set, smul_eq_mul]
    constructor
    · rintro ⟨f, hf0, hfφ, rfl⟩
      refine ⟨∑ i, ∫ x, (c⁻¹ • f i) x ∂π,
        ⟨fun i => c⁻¹ • f i, fun i x => ?_, fun z => ?_, rfl⟩, ?_⟩
      · simp only [BoundedContinuousFunction.coe_smul, Pi.smul_apply, smul_eq_mul]
        exact mul_nonneg (inv_nonneg.2 hc.le) (hf0 i x)
      · have := hfφ z
        simp only [Pi.smul_apply, smul_eq_mul] at this
        simp only [BoundedContinuousFunction.coe_smul, Pi.smul_apply, smul_eq_mul,
          ← Finset.mul_sum]
        rw [le_inv_mul_iff₀ hc]; exact this
      · simp only [BoundedContinuousFunction.coe_smul, Pi.smul_apply, smul_eq_mul,
          integral_const_mul, ← Finset.mul_sum]
        field_simp
    · rintro ⟨a, ⟨f, hf0, hfφ, rfl⟩, rfl⟩
      refine ⟨fun i => c • f i, fun i x => ?_, fun z => ?_, ?_⟩
      · simp only [BoundedContinuousFunction.coe_smul, Pi.smul_apply, smul_eq_mul]
        exact mul_nonneg hc.le (hf0 i x)
      · simp only [Pi.smul_apply, smul_eq_mul, BoundedContinuousFunction.coe_smul,
          ← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (hfφ z) hc.le
      · simp only [BoundedContinuousFunction.coe_smul, Pi.smul_apply, smul_eq_mul,
          integral_const_mul, ← Finset.mul_sum]
  rw [hset, Real.sInf_smul_of_nonneg hc.le, smul_eq_mul]

lemma N_add [IsFiniteMeasure π] [MeasurableSpace Z] (hn : n ≠ 0) (φ ψ : Z → ℝ)
    (hφ : Continuous φ) (hψ : Continuous ψ) :
    sInf (feasC π e (φ + ψ)) ≤ sInf (feasC π e φ) + sInf (feasC π e ψ) := by
  refine le_of_forall_pos_lt_add fun δ hδ => ?_
  obtain ⟨a, ⟨f, hf0, hfφ, rfl⟩, ha⟩ := exists_lt_of_csInf_lt (feasC_nonempty π e hn φ hφ)
    (lt_add_of_pos_right (sInf (feasC π e φ)) (half_pos hδ))
  obtain ⟨b, ⟨g, hg0, hgψ, rfl⟩, hb⟩ := exists_lt_of_csInf_lt (feasC_nonempty π e hn ψ hψ)
    (lt_add_of_pos_right (sInf (feasC π e ψ)) (half_pos hδ))
  have hmem : ∑ i, ∫ x, (f i + g i) x ∂π ∈ feasC π e (φ + ψ) :=
    ⟨fun i => f i + g i, fun i x => by simpa using add_nonneg (hf0 i x) (hg0 i x),
      fun z => by simpa [Finset.sum_add_distrib] using add_le_add (hfφ z) (hgψ z), rfl⟩
  calc sInf (feasC π e (φ + ψ)) ≤ ∑ i, ∫ x, (f i + g i) x ∂π := csInf_le (feasC_bdd π e _) hmem
    _ = ∑ i, ∫ x, f i x ∂π + ∑ i, ∫ x, g i x ∂π := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [BoundedContinuousFunction.coe_add, Pi.add_apply]
        exact integral_add ((f i).integrable π) ((g i).integrable π)
    _ < _ := by linarith

set_option maxHeartbeats 1000000 in
/-- compact duality (Hahn–Banach + Riesz–Markov–Kakutani). -/
theorem compact_dual [MeasurableSpace Z] [BorelSpace Z] [IsFiniteMeasure π] (hn : n ≠ 0)
    (he : ∀ i, Continuous (e i)) (ε : ℝ) (hε : 0 < ε)
    (hfeas : ∀ f : Fin n → (ℝ × ℝ →ᵇ ℝ), (∀ i x, 0 ≤ f i x) → (∀ z, 1 ≤ ∑ i, f i (e i z)) →
      ε ≤ ∑ i, ∫ x, f i x ∂π) :
    ∃ ξ : Measure Z, IsFiniteMeasure ξ ∧ ξ ≠ 0 ∧
      ∀ i (h : ℝ × ℝ →ᵇ ℝ), (∀ x, 0 ≤ h x) → ∫ z, h (e i z) ∂ξ ≤ ∫ x, h x ∂π := by
  rcases isEmpty_or_nonempty Z with hZ | hZ
  · exfalso
    have := hfeas 0 (fun _ _ => by simp) (fun z => isEmptyElim z)
    simp at this; linarith
  let toCc : C(Z, ℝ) → C_c(Z, ℝ) := CompactlySupportedContinuousMap.continuousMapEquiv
  let N : C_c(Z, ℝ) → ℝ := fun φ => sInf (feasC π e ⇑φ)
  let one : C_c(Z, ℝ) := toCc (ContinuousMap.const Z 1)
  have hone : ∀ z, one z = 1 := fun z => rfl
  have hone0 : one ≠ 0 := by
    intro h
    have := congrArg (fun φ : C_c(Z, ℝ) => φ hZ.some) h
    simp [hone] at this
  have hNnonneg : ∀ φ, 0 ≤ N φ := fun φ => Real.sInf_nonneg fun a ha => feasC_nonneg π e ha
  have hNle : ∀ φ : C_c(Z, ℝ), (∀ z, φ z ≤ 0) → N φ ≤ 0 := by
    intro φ hφ
    refine csInf_le (feasC_bdd π e _) ⟨0, fun _ _ => by simp, fun z => by simpa using hφ z,
      by simp⟩
  have hN1 : ε ≤ N one := by
    refine le_csInf (feasC_nonempty π e hn _ one.continuous) ?_
    rintro a ⟨f, hf0, hf1, rfl⟩
    exact hfeas f hf0 fun z => by simpa [hone] using hf1 z
  have hN_smul : ∀ c : ℝ, 0 < c → ∀ φ, N (c • φ) = c * N φ := by
    intro c hc φ
    show sInf (feasC π e ⇑(c • φ)) = _
    rw [CompactlySupportedContinuousMap.coe_smul]
    exact N_smul π e hc _
  have hN_add : ∀ φ ψ, N (φ + ψ) ≤ N φ + N ψ := by
    intro φ ψ
    show sInf (feasC π e ⇑(φ + ψ)) ≤ _
    rw [CompactlySupportedContinuousMap.coe_add]
    exact N_add π e hn _ _ φ.continuous ψ.continuous
  let f0 : C_c(Z, ℝ) →ₗ.[ℝ] ℝ := LinearPMap.mkSpanSingleton one (N one) hone0
  have hdom : ∀ x : f0.domain, f0 x ≤ N x := by
    rintro ⟨x, hx⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    have h1 : f0 ⟨c • one, hx⟩ = c * N one := by
      have : (⟨c • one, hx⟩ : f0.domain) = c • ⟨one, Submodule.mem_span_singleton_self one⟩ :=
        rfl
      rw [this, LinearPMap.map_smul, LinearPMap.mkSpanSingleton_apply ℝ ℝ hone0, smul_eq_mul]
    rw [h1]
    rcases lt_trichotomy c 0 with hc | rfl | hc
    · nlinarith [hNnonneg one, hNnonneg (c • one)]
    · simpa using hNnonneg 0
    · exact (hN_smul c hc one).ge
  obtain ⟨g, hgf, hgN⟩ := exists_extension_of_le_sublinear f0 N hN_smul hN_add hdom
  have hg1 : g one = N one := by
    have := hgf ⟨one, Submodule.mem_span_singleton_self one⟩
    rw [LinearPMap.mkSpanSingleton_apply ℝ ℝ hone0] at this
    exact this
  have hpos : ∀ φ : C_c(Z, ℝ), 0 ≤ φ → 0 ≤ g φ := by
    intro φ hφ
    have h1 := hgN (-φ)
    have h2 : N (-φ) ≤ 0 := hNle (-φ) fun z => by
      have := CompactlySupportedContinuousMap.le_def.1 hφ z
      simp only [CompactlySupportedContinuousMap.coe_neg, Pi.neg_apply, neg_nonpos]
      simpa using this
    rw [map_neg] at h1
    linarith
  let Λ : C_c(Z, ℝ) →ₚ[ℝ] ℝ := PositiveLinearMap.mk₀ g hpos
  have hint : ∀ φ : C_c(Z, ℝ), ∫ z, φ z ∂(RealRMK.rieszMeasure Λ) = g φ :=
    fun φ => RealRMK.integral_rieszMeasure Λ φ
  refine ⟨RealRMK.rieszMeasure Λ, inferInstance, ?_, ?_⟩
  · intro h0
    have := hint one
    rw [h0, integral_zero_measure] at this
    linarith
  · intro i h hh0
    let φ : C_c(Z, ℝ) := toCc ⟨fun z => h (e i z), h.continuous.comp (he i)⟩
    calc ∫ z, h (e i z) ∂(RealRMK.rieszMeasure Λ) = g φ := hint φ
      _ ≤ N φ := hgN φ
      _ ≤ ∫ x, h x ∂π := by
        refine csInf_le (feasC_bdd π e _) ⟨fun j => (if j = i then (1:ℝ) else 0) • h,
          fun j x => ?_, fun z => ?_, ?_⟩
        · simp only [BoundedContinuousFunction.coe_smul, Pi.smul_apply, smul_eq_mul]
          split_ifs <;> simp [hh0]
        · simp only [BoundedContinuousFunction.coe_smul, Pi.smul_apply, smul_eq_mul, ite_mul,
            one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
          exact le_rfl
        · simp only [BoundedContinuousFunction.coe_smul, Pi.smul_apply, smul_eq_mul,
            integral_const_mul, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
            if_true]
          rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (by simp)]
          simp

end CompactDual

/-- comparison of finite measures through nonnegative bounded continuous tests. -/
lemma le_of_test {ν π : Measure (ℝ × ℝ)} [IsFiniteMeasure ν] [IsFiniteMeasure π]
    (h : ∀ g : ℝ × ℝ →ᵇ ℝ≥0, ∫⁻ x, (g x : ℝ≥0∞) ∂ν ≤ ∫⁻ x, (g x : ℝ≥0∞) ∂π) : ν ≤ π := by
  have hcl : ∀ F : Set (ℝ × ℝ), IsClosed F → ν F ≤ π F := by
    intro F hF
    exact le_of_tendsto_of_tendsto' (HasOuterApproxClosed.tendsto_lintegral_apprSeq hF ν)
      (HasOuterApproxClosed.tendsto_lintegral_apprSeq hF π) fun m => h _
  refine Measure.le_iff.2 fun s hs => ?_
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
  obtain ⟨F, hFs, hFc, hlt⟩ := hs.exists_isClosed_lt_add (μ := ν) (ε := (δ : ℝ≥0∞))
    (measure_ne_top ν s) (ENNReal.coe_ne_zero.2 hδ.ne')
  exact hlt.le.trans (add_le_add ((hcl F hFc).trans (measure_mono hFs)) le_rfl)

/-- the real-valued copy of a nonnegative bounded continuous function. -/
noncomputable def bcfReal {X : Type*} [TopologicalSpace X] (g : X →ᵇ ℝ≥0) : X →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨fun x => (g x : ℝ), NNReal.continuous_coe.comp g.continuous⟩
    (Classical.choose g.bounded) fun x y => Classical.choose_spec g.bounded x y

set_option maxHeartbeats 1000000 in
/-- compact case of Kellerer's duality: positive capacity gives a primal measure. -/
theorem cap_compact {Q : Type} [TopologicalSpace Q] [PolishSpace Q] [MeasurableSpace Q]
    [BorelSpace Q] {n : ℕ} (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (K : Set (Q × (Fin n → ℝ × ℝ))) (hK : IsCompact K) (hpos : 0 < cap π K) :
    ∃ ξ : Measure (Q × (Fin n → ℝ × ℝ)), IsFiniteMeasure ξ ∧ ξ Kᶜ = 0 ∧ ξ ≠ 0 ∧
      ∀ i, ξ.map (fun p => p.2 i) ≤ π := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hKne : K.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl
    have : cap π (∅ : Set (Q × (Fin n → ℝ × ℝ))) ≤ 0 := by
      refine (cap_le π (f := fun _ _ => 0) ⟨fun _ => measurable_const, fun p hp => hp.elim⟩).trans ?_
      simp
    exact absurd hpos (not_lt.2 this)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain ⟨k0, hk0⟩ := hKne
    refine ⟨Measure.dirac k0, inferInstance, ?_, Measure.dirac_ne_zero, fun i => i.elim0⟩
    rw [Measure.dirac_apply' _ hKm.compl]
    simp [hk0]
  obtain ⟨ε, -, hε0, hεc⟩ := ENNReal.lt_iff_exists_real_btwn.1 hpos
  have hε : 0 < ε := ENNReal.ofReal_pos.1 hε0
  let e : Fin n → K → ℝ × ℝ := fun i k => k.1.2 i
  have he : ∀ i, Continuous (e i) := fun i =>
    (continuous_apply i).comp (continuous_snd.comp continuous_subtype_val)
  obtain ⟨ξ0, hξf, hξ0, htest⟩ := compact_dual π e hn.ne' he ε hε (by
    intro f hf0 hf1
    have hF : DualFeas K fun i x => ENNReal.ofReal (f i x) := by
      refine ⟨fun i => (f i).continuous.measurable.ennreal_ofReal, fun p hp => ?_⟩
      rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => hf0 i _]
      exact ENNReal.one_le_ofReal.2 (hf1 ⟨p, hp⟩)
    have h1 := lt_of_lt_of_le hεc (cap_le π hF)
    rw [Finset.sum_congr rfl fun i _ => (ofReal_integral_eq_lintegral_ofReal
      ((f i).integrable π) (Filter.Eventually.of_forall (hf0 i))).symm,
      ← ENNReal.ofReal_sum_of_nonneg fun i _ => integral_nonneg (hf0 i)] at h1
    exact ((ENNReal.ofReal_lt_ofReal_iff'.1 h1).1).le)
  refine ⟨ξ0.map Subtype.val, inferInstance, ?_, ?_, fun i => ?_⟩
  · rw [Measure.map_apply measurable_subtype_coe hKm.compl]
    simp
  · rwa [Ne, Measure.map_eq_zero_iff measurable_subtype_coe.aemeasurable]
  · rw [Measure.map_map (by fun_prop) measurable_subtype_coe]
    refine le_of_test fun g => ?_
    change ∫⁻ x, (g x : ℝ≥0∞) ∂(ξ0.map (e i)) ≤ _
    rw [lintegral_map (f := fun x => ((g x : ℝ≥0) : ℝ≥0∞))
      (ENNReal.continuous_coe.comp g.continuous).measurable (he i).measurable]
    have hπi := BoundedContinuousFunction.integrable_of_nnreal (μ := π) g
    have hξi := BoundedContinuousFunction.integrable_of_nnreal (μ := ξ0)
      (g.compContinuous ⟨e i, he i⟩)
    rw [show (∫⁻ a, ((g (e i a) : ℝ≥0) : ℝ≥0∞) ∂ξ0) =
        ∫⁻ a, (((g.compContinuous ⟨e i, he i⟩) a : ℝ≥0) : ℝ≥0∞) ∂ξ0 from rfl,
      lintegral_coe_eq_integral _ hξi, lintegral_coe_eq_integral _ hπi]
    exact ENNReal.ofReal_le_ofReal (htest i (bcfReal g) fun x => (g x).2)

open Filter

/-- probability weights supported on `[m, ∞)`. -/
def Wt (m : ℕ) : Set (ℕ →₀ ℝ) :=
  {w | (∀ k, 0 ≤ w k) ∧ Finsupp.linearCombination ℝ (fun _ : ℕ => (1 : ℝ)) w = 1 ∧
    ∀ k < m, w k = 0}

lemma single_mem_Wt (m : ℕ) : Finsupp.single m (1 : ℝ) ∈ Wt m := by
  refine ⟨fun k => ?_, by simp, fun k hk => ?_⟩
  · by_cases h : m = k <;> simp [Finsupp.single_apply, h]
  · simp [Finsupp.single_apply, hk.ne']

lemma Wt_anti {m m' : ℕ} (h : m ≤ m') : Wt m' ⊆ Wt m :=
  fun _ hw => ⟨hw.1, hw.2.1, fun k hk => hw.2.2 k (lt_of_lt_of_le hk h)⟩

lemma mid_mem_Wt {m : ℕ} {a b : ℕ →₀ ℝ} (ha : a ∈ Wt m) (hb : b ∈ Wt m) :
    (1 / 2 : ℝ) • (a + b) ∈ Wt m := by
  refine ⟨fun k => ?_, ?_, fun k hk => ?_⟩
  · simp only [Finsupp.smul_apply, Finsupp.add_apply, smul_eq_mul]
    have := ha.1 k
    have := hb.1 k
    positivity
  · rw [map_smul, map_add, ha.2.1, hb.2.1]
    norm_num
  · simp [ha.2.2 k hk, hb.2.2 k hk]

set_option maxHeartbeats 1000000 in
/-- Mazur / minimal-norm argument: convex combinations of tails converge in a Hilbert space. -/
theorem mazur {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (v : ℕ → E) (R : ℝ) (hv : ∀ k, ‖v k‖ ≤ R) :
    ∃ (w : ℕ → ℕ →₀ ℝ) (g : E), (∀ m, w m ∈ Wt m) ∧
      Tendsto (fun m => Finsupp.linearCombination ℝ v (w m)) atTop (𝓝 g) := by
  set Φ := Finsupp.linearCombination ℝ v
  let d : ℕ → ℝ := fun m => sInf ((fun w => ‖Φ w‖) '' Wt m)
  have hne : ∀ m, ((fun w => ‖Φ w‖) '' Wt m).Nonempty :=
    fun m => ⟨_, mem_image_of_mem _ (single_mem_Wt m)⟩
  have hbdd : ∀ m, BddBelow ((fun w => ‖Φ w‖) '' Wt m) :=
    fun m => ⟨0, by rintro _ ⟨w, -, rfl⟩; exact norm_nonneg _⟩
  have hd_le : ∀ m w, w ∈ Wt m → d m ≤ ‖Φ w‖ :=
    fun m w hw => csInf_le (hbdd m) (mem_image_of_mem _ hw)
  have hd0 : ∀ m, 0 ≤ d m :=
    fun m => le_csInf (hne m) (by rintro _ ⟨w, -, rfl⟩; exact norm_nonneg _)
  have hdR : ∀ m, d m ≤ R := fun m =>
    (hd_le m _ (single_mem_Wt m)).trans (by simpa [Φ] using hv m)
  have hdmono : Monotone d := fun m m' h =>
    le_csInf (hne m') (by rintro _ ⟨w, hw, rfl⟩; exact hd_le m w (Wt_anti h hw))
  have hbddA : BddAbove (range d) := ⟨R, by rintro _ ⟨k, rfl⟩; exact hdR k⟩
  set D := ⨆ m, d m
  have hdD : ∀ m, d m ≤ D := fun m => le_ciSup hbddA m
  have hdT : Tendsto d atTop (𝓝 D) := tendsto_atTop_ciSup hdmono hbddA
  have hpick : ∀ m, ∃ w ∈ Wt m, ‖Φ w‖ < d m + 1 / ((m : ℝ) + 1) := fun m => by
    obtain ⟨_, ⟨w, hw, rfl⟩, h⟩ :=
      exists_lt_of_csInf_lt (hne m) (lt_add_of_pos_right (d m) (Nat.one_div_pos_of_nat (n := m)))
    exact ⟨w, hw, h⟩
  choose w hw hwlt using hpick
  set δ : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
  have hδanti : Antitone δ := fun m m' h => by
    simp only [δ]
    gcongr
  have hδ0 : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have key : ∀ N m m', N ≤ m → N ≤ m' →
      ‖Φ (w m) - Φ (w m')‖ ^ 2 ≤ 4 * (D + δ N) ^ 2 - 4 * d N ^ 2 := by
    intro N m m' hm hm'
    have hmid := hd_le N _ (mid_mem_Wt (Wt_anti hm (hw m)) (Wt_anti hm' (hw m')))
    rw [map_smul, map_add, norm_smul] at hmid
    have hn : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by norm_num
    rw [hn] at hmid
    have h1 : ‖Φ (w m)‖ ≤ D + δ N := (hwlt m).le.trans (add_le_add (hdD m) (hδanti hm))
    have h2 : ‖Φ (w m')‖ ≤ D + δ N := (hwlt m').le.trans (add_le_add (hdD m') (hδanti hm'))
    have hpar := parallelogram_law_with_norm ℝ (Φ (w m)) (Φ (w m'))
    have hsum : 2 * d N ≤ ‖Φ (w m) + Φ (w m')‖ := by linarith
    have e1 : ‖Φ (w m)‖ ^ 2 ≤ (D + δ N) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have e2 : ‖Φ (w m')‖ ^ 2 ≤ (D + δ N) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    have e3 : (2 * d N) ^ 2 ≤ ‖Φ (w m) + Φ (w m')‖ ^ 2 :=
      pow_le_pow_left₀ (by have := hd0 N; positivity) hsum 2
    nlinarith [hpar, e1, e2, e3]
  have hb : Tendsto (fun N => Real.sqrt (4 * (D + δ N) ^ 2 - 4 * d N ^ 2)) atTop (𝓝 0) := by
    have h : Tendsto (fun N => 4 * (D + δ N) ^ 2 - 4 * d N ^ 2) atTop
        (𝓝 (4 * (D + 0) ^ 2 - 4 * D ^ 2)) :=
      (((tendsto_const_nhds.add hδ0).pow 2).const_mul 4).sub ((hdT.pow 2).const_mul 4)
    simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto _).comp h
  have hC : CauchySeq (fun m => Φ (w m)) := cauchySeq_of_le_tendsto_0 _ (fun m m' N hm hm' => by
    rw [dist_eq_norm]
    exact (le_abs_self _).trans (Real.abs_le_sqrt (key N m m' hm hm'))) hb
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hC
  exact ⟨w, g, hw, hg⟩

/-- a capacity bound gives bounded real feasible functions. -/
lemma realFeas {Q : Type} {n : ℕ} (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (B : Set (Q × (Fin n → ℝ × ℝ))) (t : ℝ≥0∞) (ht : cap π B < t) (htT : t ≠ ⊤) :
    ∃ F : Fin n → ℝ × ℝ → ℝ, (∀ i, Measurable (F i)) ∧ (∀ i x, 0 ≤ F i x ∧ F i x ≤ 1) ∧
      (∀ p ∈ B, 1 ≤ ∑ i, F i (p.2 i)) ∧ ∑ i, ∫ x, F i x ∂π ≤ t.toReal := by
  obtain ⟨f, hfB, hft⟩ : ∃ f, DualFeas B f ∧ ∑ i, ∫⁻ x, f i x ∂π < t := by
    simpa [cap, iInf_lt_iff] using ht
  refine ⟨fun i x => (min (f i x) 1).toReal,
    fun i => ((hfB.1 i).min measurable_const).ennreal_toReal,
    fun i x => ⟨ENNReal.toReal_nonneg, ?_⟩, fun p hp => ?_, ?_⟩
  · exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using min_le_right (f i x) 1)
  · have h1 : (1 : ℝ≥0∞) ≤ ∑ i, min (f i (p.2 i)) 1 := by
      by_cases h : ∃ i, 1 ≤ f i (p.2 i)
      · obtain ⟨i, hi⟩ := h
        calc (1 : ℝ≥0∞) = min (f i (p.2 i)) 1 := (min_eq_right hi).symm
          _ ≤ ∑ j, min (f j (p.2 j)) 1 :=
            Finset.single_le_sum (f := fun j => min (f j (p.2 j)) 1) (fun _ _ => by simp)
              (Finset.mem_univ i)
      · push Not at h
        calc (1 : ℝ≥0∞) ≤ ∑ i, f i (p.2 i) := hfB.2 p hp
          _ = ∑ i, min (f i (p.2 i)) 1 :=
            Finset.sum_congr rfl fun i _ => (min_eq_left (h i).le).symm
    have hne : ∀ i ∈ (Finset.univ : Finset (Fin n)), min (f i (p.2 i)) 1 ≠ ⊤ :=
      fun i _ => ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
    rw [← ENNReal.toReal_sum hne]
    simpa using ENNReal.toReal_mono (ENNReal.sum_ne_top.2 hne) h1
  · have hint : ∀ i, ∫ x, (min (f i x) 1).toReal ∂π = (∫⁻ x, min (f i x) 1 ∂π).toReal :=
      fun i => integral_toReal ((hfB.1 i).min measurable_const).aemeasurable
        (ae_of_all _ fun x => lt_of_le_of_lt (min_le_right _ _) ENNReal.one_lt_top)
    simp_rw [hint]
    have hne : ∀ i ∈ (Finset.univ : Finset (Fin n)), ∫⁻ x, min (f i x) 1 ∂π ≠ ⊤ := fun i _ =>
      (lt_of_le_of_lt (lintegral_mono fun x => min_le_right (f i x) 1)
        (by simpa using measure_lt_top π univ)).ne
    rw [← ENNReal.toReal_sum hne]
    exact ENNReal.toReal_mono htT ((Finset.sum_le_sum fun i _ =>
      lintegral_mono fun x => min_le_left (f i x) 1).trans hft.le)

/-- a real feasible function, feasible off null sets of coordinates, bounds the capacity. -/
lemma cap_le_real {Q : Type} {n : ℕ} (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (B : Set (Q × (Fin n → ℝ × ℝ))) (G : Fin n → ℝ × ℝ → ℝ) (good : Fin n → Set (ℝ × ℝ))
    (hGm : ∀ i, Measurable (G i)) (hG0 : ∀ i x, 0 ≤ G i x) (hGi : ∀ i, Integrable (G i) π)
    (hgood : ∀ i, ∀ᵐ x ∂π, x ∈ good i)
    (hB : ∀ p ∈ B, (∀ i, p.2 i ∈ good i) → 1 ≤ ∑ i, G i (p.2 i)) :
    cap π B ≤ ENNReal.ofReal (∑ i, ∫ x, G i x ∂π) := by
  set N : Fin n → Set (ℝ × ℝ) := fun i => toMeasurable π (good i)ᶜ
  have hN0 : ∀ i, π (N i) = 0 := fun i => by
    simp only [N]
    rw [measure_toMeasurable]
    exact ae_iff.1 (hgood i)
  set f : Fin n → ℝ × ℝ → ℝ≥0∞ := fun i x => (N i).indicator (fun _ => ⊤) x + ENNReal.ofReal (G i x)
  refine (cap_le π (f := f) ⟨fun i => ?_, fun p hp => ?_⟩).trans ?_
  · exact (measurable_const.indicator (measurableSet_toMeasurable _ _)).add (hGm i).ennreal_ofReal
  · by_cases h : ∀ i, p.2 i ∈ good i
    · have h1 := hB p hp h
      calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := by simp
        _ ≤ ENNReal.ofReal (∑ i, G i (p.2 i)) := ENNReal.ofReal_le_ofReal h1
        _ = ∑ i, ENNReal.ofReal (G i (p.2 i)) := ENNReal.ofReal_sum_of_nonneg fun i _ => hG0 i _
        _ ≤ ∑ i, f i (p.2 i) := Finset.sum_le_sum fun i _ => le_add_self
    · push Not at h
      obtain ⟨i, hi⟩ := h
      have hfi : f i (p.2 i) = ⊤ := by
        have hm : p.2 i ∈ N i := subset_toMeasurable π _ hi
        simp [f, Set.indicator_of_mem hm]
      calc (1 : ℝ≥0∞) ≤ ⊤ := le_top
        _ = f i (p.2 i) := hfi.symm
        _ ≤ ∑ j, f j (p.2 j) :=
          Finset.single_le_sum (f := fun j => f j (p.2 j)) (fun _ _ => by simp)
            (Finset.mem_univ i)
  · have hfi : ∀ i, ∫⁻ x, f i x ∂π = ENNReal.ofReal (∫ x, G i x ∂π) := fun i => by
      rw [ofReal_integral_eq_lintegral_ofReal (hGi i) (ae_of_all _ (hG0 i))]
      apply lintegral_congr_ae
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hN0 i)] with x hx
      simp [f, Set.indicator_of_notMem hx]
    simp_rw [hfi]
    rw [ENNReal.ofReal_sum_of_nonneg fun i _ => integral_nonneg (hG0 i)]

lemma coeFn_lc {Z : Type*} [MeasurableSpace Z] {ν : Measure Z} (F : ℕ → Z → ℝ)
    (hF : ∀ k, MemLp (F k) 2 ν) (w : ℕ →₀ ℝ) :
    ⇑(Finsupp.linearCombination ℝ (fun k => (hF k).toLp (F k)) w) =ᵐ[ν]
      Finsupp.linearCombination ℝ F w := by
  induction w using Finsupp.induction_linear with
  | zero =>
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := ν)] with x hx
    simpa using hx
  | add a b ha hb =>
    rw [map_add, map_add]
    filter_upwards [Lp.coeFn_add (Finsupp.linearCombination ℝ (fun k => (hF k).toLp (F k)) a)
      (Finsupp.linearCombination ℝ (fun k => (hF k).toLp (F k)) b), ha, hb] with x h1 h2 h3
    rw [h1, Pi.add_apply, Pi.add_apply, h2, h3]
  | single k c =>
    rw [Finsupp.linearCombination_single, Finsupp.linearCombination_single]
    filter_upwards [Lp.coeFn_smul c ((hF k).toLp (F k)), (hF k).coeFn_toLp] with x h1 h2
    simp [h1, h2]

set_option maxHeartbeats 1000000 in
/-- the dual capacity is continuous along increasing sequences. -/
theorem cap_up {Q : Type} {n : ℕ} (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (A : ℕ → Set (Q × (Fin n → ℝ × ℝ))) (hA : Monotone A) :
    cap π (⋃ m, A m) ≤ ⨆ m, cap π (A m) := by
  set s := ⨆ m, cap π (A m)
  rcases eq_or_ne s ⊤ with hs | hs
  · rw [hs]; exact le_top
  have hcs : ∀ m, cap π (A m) ≤ s := fun m => le_iSup (fun m => cap π (A m)) m
  have hpick : ∀ k : ℕ, ∃ F : Fin n → ℝ × ℝ → ℝ, (∀ i, Measurable (F i)) ∧
      (∀ i x, 0 ≤ F i x ∧ F i x ≤ 1) ∧ (∀ p ∈ A k, 1 ≤ ∑ i, F i (p.2 i)) ∧
      ∑ i, ∫ x, F i x ∂π ≤ s.toReal + 1 / ((k : ℝ) + 1) := by
    intro k
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := Nat.one_div_pos_of_nat
    have hlt : cap π (A k) < s + ENNReal.ofReal (1 / ((k : ℝ) + 1)) :=
      lt_of_le_of_lt (hcs k) (ENNReal.lt_add_right hs (by simpa using hpos))
    obtain ⟨F, h1, h2, h3, h4⟩ :=
      realFeas π (A k) _ hlt (ENNReal.add_ne_top.2 ⟨hs, ENNReal.ofReal_ne_top⟩)
    refine ⟨F, h1, h2, h3, h4.trans (le_of_eq ?_)⟩
    rw [ENNReal.toReal_add hs ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hpos.le]
  choose F hFm hF01 hFfeas hFint using hpick
  set ν : Measure ((ℝ × ℝ) × Fin n) := π.prod Measure.count
  set Fz : ℕ → (ℝ × ℝ) × Fin n → ℝ := fun k z => F k z.2 z.1 with hFz
  have hFzm : ∀ k, Measurable (Fz k) := fun k =>
    measurable_from_prod_countable_left fun i => hFm k i
  have hFz01 : ∀ k z, 0 ≤ Fz k z ∧ Fz k z ≤ 1 := fun k z => hF01 k z.2 z.1
  have hFzL : ∀ k, MemLp (Fz k) 2 ν := fun k =>
    MemLp.of_bound (hFzm k).aestronglyMeasurable 1 (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hFz01 k z).1]; exact (hFz01 k z).2)
  set V : ℕ → Lp ℝ 2 ν := fun k => (hFzL k).toLp (Fz k)
  obtain ⟨w, g, hw, hg⟩ := mazur V _ (fun k => Lp.norm_le_of_ae_bound zero_le_one (by
      filter_upwards [(hFzL k).coeFn_toLp] with z hz
      rw [hz, Real.norm_eq_abs, abs_of_nonneg (hFz01 k z).1]; exact (hFz01 k z).2))
  set pt : ℕ → (ℝ × ℝ) × Fin n → ℝ := fun m => Finsupp.linearCombination ℝ Fz (w m)
  have hcoe : ∀ m, ⇑(Finsupp.linearCombination ℝ V (w m)) =ᵐ[ν] pt m :=
    fun m => coeFn_lc Fz hFzL (w m)
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hg).exists_seq_tendsto_ae
  have hae2 : ∀ᵐ z ∂ν, Tendsto (fun j => pt (ns j) z) atTop (𝓝 (g z)) := by
    have hall : ∀ᵐ z ∂ν, ∀ m, (Finsupp.linearCombination ℝ V (w m)) z = pt m z :=
      ae_all_iff.2 hcoe
    filter_upwards [hae, hall] with z h1 h2
    simpa [h2] using h1
  have hpt : ∀ m z, pt m z = ∑ k ∈ (w m).support, w m k * Fz k z := fun m z => by
    simp [pt, Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply]
  have htot : ∀ m, ∑ k ∈ (w m).support, w m k = 1 := fun m => by
    have := (hw m).2.1
    simpa [Finsupp.linearCombination_apply, Finsupp.sum] using this
  have hsupp : ∀ m, ∀ k ∈ (w m).support, m ≤ k := fun m k hk => by
    by_contra h
    push Not at h
    exact (Finsupp.mem_support_iff.1 hk) ((hw m).2.2 k h)
  have hpt01 : ∀ m z, 0 ≤ pt m z ∧ pt m z ≤ 1 := fun m z => by
    rw [hpt]
    constructor
    · exact Finset.sum_nonneg fun k _ => mul_nonneg ((hw m).1 k) (hFz01 k z).1
    · calc _ ≤ ∑ k ∈ (w m).support, w m k * 1 :=
            Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hFz01 k z).2 ((hw m).1 k)
        _ = 1 := by simpa using htot m
  have hptm : ∀ m, Measurable (pt m) := fun m => by
    have : pt m = fun z => ∑ k ∈ (w m).support, w m k * Fz k z := funext (hpt m)
    rw [this]
    exact Finset.measurable_sum _ fun k _ => (hFzm k).const_mul _
  have hptfeas : ∀ m, ∀ p ∈ A m, 1 ≤ ∑ i, pt m (p.2 i, i) := by
    intro m p hp
    simp_rw [hpt]
    rw [Finset.sum_comm]
    calc (1 : ℝ) = ∑ k ∈ (w m).support, w m k * 1 := by simpa using (htot m).symm
      _ ≤ ∑ k ∈ (w m).support, ∑ i, w m k * Fz k (p.2 i, i) :=
        Finset.sum_le_sum fun k hk => by
          rw [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left (hFfeas k p (hA (hsupp m k hk) hp)) ((hw m).1 k)
  have hFi : ∀ k i, Integrable (F k i) π := fun k i =>
    Integrable.mono' (integrable_const (1 : ℝ)) (hFm k i).aestronglyMeasurable
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hF01 k i x).1]; exact (hF01 k i x).2)
  have hptint : ∀ m, ∑ i, ∫ x, pt m (x, i) ∂π ≤ s.toReal + 1 / ((m : ℝ) + 1) := by
    intro m
    have h1 : ∀ i, ∫ x, pt m (x, i) ∂π = ∑ k ∈ (w m).support, w m k * ∫ x, F k i x ∂π :=
      fun i => by
        simp_rw [hpt, hFz]
        rw [integral_finset_sum]
        · exact Finset.sum_congr rfl fun k _ => integral_const_mul _ _
        · exact fun k _ => (hFi k i).const_mul _
    simp_rw [h1]
    rw [Finset.sum_comm]
    calc ∑ k ∈ (w m).support, ∑ i, w m k * ∫ x, F k i x ∂π
        = ∑ k ∈ (w m).support, w m k * ∑ i, ∫ x, F k i x ∂π :=
          Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
      _ ≤ ∑ k ∈ (w m).support, w m k * (s.toReal + 1 / ((m : ℝ) + 1)) :=
          Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left ((hFint k).trans (by
            have : (m : ℝ) ≤ k := by exact_mod_cast hsupp m k hk
            gcongr)) ((hw m).1 k)
      _ = s.toReal + 1 / ((m : ℝ) + 1) := by rw [← Finset.sum_mul, htot m, one_mul]
  set G : Fin n → ℝ × ℝ → ℝ := fun i x => max (g (x, i)) 0
  set good : Fin n → Set (ℝ × ℝ) :=
    fun i => {x | Tendsto (fun j => pt (ns j) (x, i)) atTop (𝓝 (g (x, i)))}
  have hgood : ∀ i, ∀ᵐ x ∂π, x ∈ good i := by
    have h := Measure.ae_ae_of_ae_prod hae2
    intro i
    filter_upwards [h] with x hx
    rw [ae_iff, Measure.count_eq_zero_iff] at hx
    by_contra hc
    have hmem : i ∈ {a : Fin n | ¬Tendsto (fun j => pt (ns j) (x, a)) atTop (𝓝 (g (x, a)))} := hc
    rw [hx] at hmem
    exact hmem
  have hGeq : ∀ i x, x ∈ good i → G i x = g (x, i) := fun i x hx =>
    max_eq_left (ge_of_tendsto' hx fun j => (hpt01 _ _).1)
  have hgm : Measurable (g : (ℝ × ℝ) × Fin n → ℝ) := (Lp.stronglyMeasurable g).measurable
  have hsec : ∀ i : Fin n, Measurable fun x : ℝ × ℝ => (x, i) :=
    fun i => measurable_id.prodMk measurable_const
  have hGm : ∀ i, Measurable (G i) := fun i => (hgm.comp (hsec i)).max measurable_const
  have hlim : ∀ i, Tendsto (fun j => ∫ x, pt (ns j) (x, i) ∂π) atTop (𝓝 (∫ x, G i x ∂π)) :=
    fun i => tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      (fun j => ((hptm (ns j)).comp (hsec i)).aestronglyMeasurable)
      (integrable_const 1)
      (fun j => ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hpt01 _ _).1]; exact (hpt01 _ _).2)
      (by
        filter_upwards [hgood i] with x hx
        rw [hGeq i x hx]
        exact hx)
  have hGint : ∀ i, Integrable (G i) π := fun i =>
    Integrable.mono' (integrable_const (1 : ℝ)) (hGm i).aestronglyMeasurable (by
      filter_upwards [hgood i] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _), hGeq i x hx]
      exact le_of_tendsto' hx fun j => (hpt01 _ _).2)
  have hsum : ∑ i, ∫ x, G i x ∂π ≤ s.toReal := by
    have hT : Tendsto (fun j => ∑ i, ∫ x, pt (ns j) (x, i) ∂π) atTop
        (𝓝 (∑ i, ∫ x, G i x ∂π)) := tendsto_finset_sum _ fun i _ => hlim i
    have hb : Tendsto (fun j => s.toReal + 1 / ((ns j : ℝ) + 1)) atTop (𝓝 (s.toReal + 0)) :=
      tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat.comp hns.tendsto_atTop)
    rw [add_zero] at hb
    exact le_of_tendsto_of_tendsto' hT hb fun j => hptint (ns j)
  have hfeas : ∀ p ∈ ⋃ m, A m, (∀ i, p.2 i ∈ good i) → 1 ≤ ∑ i, G i (p.2 i) := by
    intro p hp hgd
    obtain ⟨M, hM⟩ := mem_iUnion.1 hp
    have hT : Tendsto (fun j => ∑ i, pt (ns j) (p.2 i, i)) atTop (𝓝 (∑ i, G i (p.2 i))) := by
      refine tendsto_finset_sum _ fun i _ => ?_
      rw [hGeq i _ (hgd i)]
      exact hgd i
    refine ge_of_tendsto hT ?_
    filter_upwards [hns.tendsto_atTop.eventually_ge_atTop M] with j hj
    exact hptfeas (ns j) p (hA hj hM)
  calc cap π (⋃ m, A m) ≤ ENNReal.ofReal (∑ i, ∫ x, G i x ∂π) :=
        cap_le_real π _ G good hGm (fun i x => le_max_right _ _) hGint hgood hfeas
    _ ≤ ENNReal.ofReal s.toReal := ENNReal.ofReal_le_ofReal hsum
    _ = s := ENNReal.ofReal_toReal hs

/-- Kellerer's duality (C1-core), via Choquet capacitability of the dual capacity. -/
theorem kellererDual : KellererDual := by
  intro Q _ _ _ _ n π hπ C _ B hB _ hε
  haveI := hπ
  obtain ⟨ε, hε0, hεf⟩ := hε
  have hcap : ε ≤ cap π B := le_iInf₂ fun f hf => hεf f hf
  obtain ⟨K, hK, hKB, hKpos⟩ := choquet (cap π) (fun A B h => cap_mono π h)
    (fun A hA => cap_up π A hA) (fun A t ht => cap_outer π A t ht) B hB.analyticSet 0
    (lt_of_lt_of_le hε0 hcap)
  obtain ⟨ξ, hξf, hξK, hξ0, hξm⟩ := cap_compact π K hK hKpos
  exact ⟨ξ, hξf, measure_mono_null (compl_subset_compl.2 hKB) hξK, hξ0, hξm⟩

end MartOT.HN.L111

open MeasureTheory in
theorem solution (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : MartOT.Var.ConvexLE μ ν) (c : ℝ → ℝ → ℝ) (hc : Measurable (Function.uncurry c))
    (hint : MartOT.Var.SuffIntegrable μ ν c) (π : Measure (ℝ × ℝ)) (hπ : MartOT.Var.IsOptimal c μ ν π)
    (hfin : MartOT.Var.cost c π < ⊤) :
    ∃ Γ : Set (ℝ × ℝ), MeasurableSet Γ ∧ π Γᶜ = 0 ∧
      ∀ (S : Finset (ℝ × ℝ)) (w : ℝ × ℝ → NNReal), (↑S : Set (ℝ × ℝ)) ⊆ Γ →
        ∀ α' : Measure (ℝ × ℝ),
          MartOT.Var.IsCompetitor (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) α' →
          MartOT.Var.cost c (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) ≤ MartOT.Var.cost c α' := by
  exact MartOT.HN.L111.of_kellerer
    (MartOT.HN.L111.kellerer_of_dual MartOT.HN.L111.kellererDual) μ ν c hc hint π hπ hfin
