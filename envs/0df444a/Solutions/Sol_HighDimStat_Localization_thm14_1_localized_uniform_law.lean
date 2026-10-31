-- Prove2me | solution 1 for HighDimStat.Localization.thm14_1_localized_uniform_law
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-10-30T22:05:04.785587+00:00
-- url     : https://prove2.me/submissions/b2456ea4-9da6-4d45-a637-022e0a64aef1

import Mathlib
import Definitions.Def_HighDimStat_Localization_Core

set_option autoImplicit false

open MeasureTheory ProbabilityTheory HighDimStat.Localization

namespace HighDimStat.Localization.Disproof

theorem exists_n_exp_lt (c1 c2 : ℝ) (hc1 : 0 < c1) (hc2 : 0 < c2) :
    ∃ n : ℕ, 0 < n ∧ c1 * Real.exp (-c2 * (n : ℝ) * (1 / 2) ^ 2 / 1 ^ 2) < 1 := by
  have h_bound : ∃ m : ℕ, 4 * Real.log c1 / c2 < (m : ℝ) := exists_nat_gt (4 * Real.log c1 / c2)
  obtain ⟨m, hm⟩ := h_bound
  use m + 1
  constructor
  · omega
  · have hpos : (m : ℝ) < (m + 1 : ℝ) := lt_add_one (m : ℝ)
    have hmn : 4 * Real.log c1 / c2 < (m + 1 : ℝ) := hm.trans hpos
    have h1 : Real.log c1 < c2 * (m + 1 : ℝ) / 4 := by
      rw [div_lt_iff₀ hc2] at hmn
      linarith
    have h2 : - (c2 * (m + 1 : ℝ) / 4) < - Real.log c1 := by linarith
    have h3 : - Real.log c1 = Real.log (c1⁻¹) := (Real.log_inv c1).symm
    have h4 : - (c2 * (m + 1 : ℝ) / 4) < Real.log (c1⁻¹) := by rwa [← h3]
    have h5 : Real.exp (- (c2 * (m + 1 : ℝ) / 4)) < c1⁻¹ := by
      rw [← Real.exp_log (inv_pos.mpr hc1)]
      exact Real.exp_lt_exp.mpr h4
    have h6 : c1 * Real.exp (- (c2 * (m + 1 : ℝ) / 4)) < c1 * c1⁻¹ :=
      mul_lt_mul_of_pos_left h5 hc1
    rw [mul_inv_cancel₀ (ne_of_gt hc1)] at h6
    have heq : -c2 * ((m + 1 : ℕ) : ℝ) * (1 / 2) ^ 2 / 1 ^ 2 = - (c2 * (m + 1 : ℝ) / 4) := by
      push_cast
      ring
    rwa [heq]

/-- The reals with the countable–cocountable σ-algebra. -/
def CC0 : Type := ℝ

def toR0 : CC0 → ℝ := id
def ofR0 : ℝ → CC0 := id

instance instMS0 : MeasurableSpace CC0 where
  MeasurableSet' s := s.Countable ∨ sᶜ.Countable
  measurableSet_empty := Or.inl Set.countable_empty
  measurableSet_compl s h := by
    rcases h with h | h
    · exact Or.inr (by rwa [compl_compl])
    · exact Or.inl h
  measurableSet_iUnion f h := by
    by_cases hc : ∀ i, (f i).Countable
    · exact Or.inl (Set.countable_iUnion hc)
    · push Not at hc
      obtain ⟨i, hi⟩ := hc
      exact Or.inr (((h i).resolve_left hi).mono
        (Set.compl_subset_compl.mpr (Set.subset_iUnion f i)))

theorem ms0_iff (s : Set CC0) : MeasurableSet s ↔ s.Countable ∨ sᶜ.Countable := Iff.rfl

theorem univ_not_countable : ¬ (Set.univ : Set CC0).Countable := by
  intro h
  have h' : (Set.univ : Set ℝ).Countable := h
  have := h'.measure_zero (volume : Measure ℝ)
  simp at this

/-- The positive half-line, a set that is neither countable nor cocountable. -/
def A : Set CC0 := {x | 0 < toR0 x}

theorem A_not_countable : ¬ A.Countable := by
  intro h
  have h' : (Set.Ioi (0:ℝ)).Countable := h
  have := h'.measure_zero (volume : Measure ℝ)
  simp at this

theorem Ac_not_countable : ¬ Aᶜ.Countable := by
  intro h
  have h' : (Set.Iic (0:ℝ)).Countable := by
    refine Set.Countable.mono ?_ (show ({x : ℝ | ¬ 0 < x} : Set ℝ).Countable from h)
    intro x hx
    simp only [Set.mem_Iic] at hx
    simp only [Set.mem_setOf_eq, not_lt]
    exact hx
  have := h'.measure_zero (volume : Measure ℝ)
  simp at this

open Classical in
/-- The countable–cocountable probability measure on `CC0`. -/
noncomputable def ccM0 : Measure CC0 :=
  Measure.ofMeasurable (fun s _ => if s.Countable then 0 else 1) (by simp) (by
    intro f hf hd
    by_cases hc : ∀ i, (f i).Countable
    · simp [Set.countable_iUnion hc, hc]
    · push Not at hc
      obtain ⟨i, hi⟩ := hc
      have hU : ¬ (⋃ j, f j).Countable := fun h => hi (h.mono (Set.subset_iUnion f i))
      rw [if_neg hU, tsum_eq_single i]
      · simp [hi]
      · intro j hj
        have hcomp : (f i)ᶜ.Countable := (hf i).resolve_left hi
        have : (f j).Countable := hcomp.mono (hd hj).le_compl_right
        simp [this])

open Classical in
theorem ccM0_apply (s : Set CC0) (hs : MeasurableSet s) :
    ccM0 s = if s.Countable then 0 else 1 :=
  Measure.ofMeasurable_apply s hs

open Classical in
instance : IsProbabilityMeasure ccM0 :=
  ⟨by rw [ccM0_apply _ MeasurableSet.univ, if_neg univ_not_countable]⟩

open Classical in
theorem null_countable {N : Set CC0} (h : ccM0 N = 0) : N.Countable := by
  have hT := measurableSet_toMeasurable ccM0 N
  have h0 : ccM0 (toMeasurable ccM0 N) = 0 := by rwa [measure_toMeasurable]
  rw [ccM0_apply _ hT] at h0
  split_ifs at h0 with hc
  · exact hc.mono (subset_toMeasurable _ _)
  · simp at h0

open Classical in
/-- Non-measurable function `M0`. -/
noncomputable def M0 (x : CC0) : ℝ := if x ∈ A then 1 else 1 / 2

theorem M0_pos (x : CC0) : 0 < M0 x := by
  unfold M0
  split_ifs <;> norm_num

theorem M0_ge_half (x : CC0) : 1 / 2 ≤ M0 x := by
  unfold M0
  split_ifs <;> norm_num

theorem M0_le_one (x : CC0) : M0 x ≤ 1 := by
  unfold M0
  split_ifs <;> norm_num

open Classical in
theorem M0_not_aesm : ¬ AEStronglyMeasurable M0 ccM0 := by
  intro h
  have hm := h.aemeasurable
  have hM' : Measurable (hm.mk M0) := hm.measurable_mk
  have hN : ({x | ¬ M0 x = hm.mk M0 x} : Set CC0).Countable :=
    null_countable (ae_iff.1 hm.ae_eq_mk)
  have hE : MeasurableSet {x | (3 / 4 : ℝ) < hm.mk M0 x} := measurableSet_lt measurable_const hM'
  rcases (ms0_iff _).1 hE with hc | hc
  · apply A_not_countable
    refine (hc.union hN).mono ?_
    intro x hx
    by_cases hxN : M0 x = hm.mk M0 x
    · left
      simp only [Set.mem_setOf_eq]
      rw [← hxN]
      simp only [M0, hx, ↓reduceIte]
      norm_num
    · right; exact hxN
  · apply Ac_not_countable
    refine (hc.union hN).mono ?_
    intro x hx
    by_cases hxN : M0 x = hm.mk M0 x
    · left
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
      rw [← hxN]
      have hxA : x ∉ A := hx
      simp only [M0, hxA, ↓reduceIte]
      norm_num
    · right; exact hxN

/-- The Rademacher law on `Bool`. -/
noncomputable def radBool : Measure Bool := (2⁻¹ : ENNReal) • (Measure.dirac true + Measure.dirac false)

instance : IsProbabilityMeasure radBool := by
  constructor
  simp only [radBool, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
  rw [one_add_one_eq_two, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]

theorem radBool_true : radBool {true} = 2⁻¹ := by
  simp [radBool]

abbrev Ω0 (n : ℕ) : Type := (Fin n → CC0) × (Fin n → Bool)

noncomputable def μX0 (n : ℕ) : Measure (Fin n → CC0) := Measure.pi (fun _ : Fin n => ccM0)
noncomputable def μE0 (n : ℕ) : Measure (Fin n → Bool) := Measure.pi (fun _ : Fin n => radBool)
noncomputable def P0 (n : ℕ) : Measure (Ω0 n) := (μX0 n).prod (μE0 n)

instance (n : ℕ) : IsProbabilityMeasure (μX0 n) := by unfold μX0; infer_instance
instance (n : ℕ) : IsProbabilityMeasure (μE0 n) := by unfold μE0; infer_instance
instance (n : ℕ) : IsProbabilityMeasure (P0 n) := by unfold P0; infer_instance

universe u_1 u_2

abbrev CC : Type u_1 := ULift.{u_1} CC0
def ofCC (x : CC0) : CC.{u_1} := ULift.up x
def toCC (x : CC.{u_1}) : CC0 := ULift.down x

theorem measurable_ofCC : Measurable ofCC.{u_1} :=
  MeasurableEquiv.ulift.symm.measurable

theorem measurable_toCC : Measurable toCC.{u_1} :=
  MeasurableEquiv.ulift.measurable

noncomputable def ccM : Measure CC.{u_1} :=
  Measure.map ofCC ccM0

instance isProbabilityMeasure_ccM : IsProbabilityMeasure ccM.{u_1} := by
  constructor
  rw [ccM, Measure.map_apply measurable_ofCC MeasurableSet.univ]
  exact measure_univ

abbrev Ω (n : ℕ) : Type u_2 := ULift.{u_2} (Ω0 n)
def ofΩ {n : ℕ} (w : Ω0 n) : Ω.{u_2} n := ULift.up w
def toΩ {n : ℕ} (w : Ω.{u_2} n) : Ω0 n := ULift.down w

theorem measurable_ofΩ {n : ℕ} : Measurable (@ofΩ.{u_2} n) :=
  MeasurableEquiv.ulift.symm.measurable

theorem measurable_toΩ {n : ℕ} : Measurable (@toΩ.{u_2} n) :=
  MeasurableEquiv.ulift.measurable

noncomputable def P (n : ℕ) : Measure (Ω.{u_2} n) :=
  Measure.map ofΩ (P0 n)

instance isProbabilityMeasure_P (n : ℕ) : IsProbabilityMeasure (P.{u_2} n) := by
  constructor
  rw [P, Measure.map_apply measurable_ofΩ MeasurableSet.univ]
  exact measure_univ

theorem map_toΩ {n : ℕ} (E : Set (Ω0 n)) (hE : MeasurableSet E) :
    P.{u_2} n (toΩ ⁻¹' E) = P0 n E := by
  rw [P, Measure.map_apply measurable_ofΩ (measurable_toΩ hE)]
  change P0 n E = P0 n E
  rfl

theorem indepFun_toΩ {n : ℕ} {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {f : Ω0 n → α} {g : Ω0 n → β} (h : IndepFun f g (P0 n))
    (hf : Measurable f) (hg : Measurable g) :
    IndepFun (f ∘ toΩ) (g ∘ toΩ) (P.{u_2} n) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  have h1 : (f ∘ toΩ) ⁻¹' s ∩ (g ∘ toΩ) ⁻¹' t = toΩ ⁻¹' (f ⁻¹' s ∩ g ⁻¹' t) := rfl
  have hf_pre : (f ∘ toΩ) ⁻¹' s = toΩ ⁻¹' (f ⁻¹' s) := rfl
  have hg_pre : (g ∘ toΩ) ⁻¹' t = toΩ ⁻¹' (g ⁻¹' t) := rfl
  rw [h1, hf_pre, hg_pre, map_toΩ _ ((hf hs).inter (hg ht)), map_toΩ _ (hf hs), map_toΩ _ (hg ht)]
  exact indepFun_iff_measure_inter_preimage_eq_mul.mp h s t hs ht

theorem iIndepFun_toΩ {n : ℕ} {ι : Type*} {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    {f : ∀ i, Ω0 n → β i} (h : iIndepFun f (P0 n)) (hf : ∀ i, Measurable (f i)) :
    iIndepFun (fun i => f i ∘ toΩ) (P.{u_2} n) := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hsets
  have h1 : (⋂ i ∈ S, (f i ∘ toΩ) ⁻¹' sets i) = toΩ ⁻¹' (⋂ i ∈ S, f i ⁻¹' sets i) := by
    ext; simp
  rw [h1]
  have h_inter_meas : MeasurableSet (⋂ i ∈ S, f i ⁻¹' sets i) :=
    MeasurableSet.biInter S.countable_toSet (fun i hi => hf i (hsets i hi))
  rw [map_toΩ _ h_inter_meas]
  have h_orig := iIndepFun_iff_measure_inter_preimage_eq_mul.mp h S hsets
  rw [h_orig]
  refine Finset.prod_congr rfl ?_
  intro i hi
  have hi_pre : (f i ∘ toΩ) ⁻¹' sets i = toΩ ⁻¹' (f i ⁻¹' sets i) := rfl
  rw [hi_pre]
  exact (map_toΩ _ (hf i (hsets i hi))).symm

def xs {n : ℕ} (i : Fin n) (w : Ω.{u_2} n) : CC.{u_1} := ofCC ((toΩ w).1 i)
def eps {n : ℕ} (i : Fin n) (w : Ω.{u_2} n) : ℝ := if (toΩ w).2 i then 1 else -1

theorem measurable_xs {n : ℕ} (i : Fin n) : Measurable (xs.{u_1, u_2} (n := n) i) :=
  measurable_ofCC.comp (((measurable_pi_apply i).comp measurable_fst).comp measurable_toΩ)

theorem measurable_eps {n : ℕ} (i : Fin n) : Measurable (eps.{u_2} (n := n) i) := by
  have hm : Measurable (fun b : Bool => if b then (1:ℝ) else -1) := by
    intro s _; exact MeasurableSet.of_discrete
  exact hm.comp (((measurable_pi_apply i).comp measurable_snd).comp measurable_toΩ)

theorem map_xs {n : ℕ} (i : Fin n) :
    Measure.map (xs.{u_1, u_2} (n := n) i) (P n) = ccM := by
  have h1 : (xs.{u_1, u_2} (n := n) i) =
      (ofCC ∘ (fun p : Ω0 n => p.1 i)) ∘ toΩ := rfl
  have hm_inner : Measurable (ofCC ∘ (fun p : Ω0 n => p.1 i)) :=
    measurable_ofCC.comp ((measurable_pi_apply i).comp measurable_fst)
  rw [h1, ← Measure.map_map hm_inner measurable_toΩ]
  have h_map_toΩ_all : Measure.map (@toΩ.{u_2} n) (P n) = P0 n := by
    rw [P, Measure.map_map measurable_toΩ measurable_ofΩ]
    have : @toΩ.{u_2} n ∘ @ofΩ.{u_2} n = id := rfl
    rw [this, Measure.map_id]
  rw [h_map_toΩ_all]
  have h2 : (ofCC ∘ (fun p : Ω0 n => p.1 i)) =
      ofCC ∘ ((fun x : Fin n → CC0 => x i) ∘ Prod.fst) := rfl
  rw [h2, ← Measure.map_map measurable_ofCC ((measurable_pi_apply i).comp measurable_fst)]
  rw [← Measure.map_map (measurable_pi_apply i) measurable_fst, P0]
  simp only [Measure.map_fst_prod, measure_univ, one_smul]
  exact congrArg (Measure.map ofCC) ((measurePreserving_eval (fun _ : Fin n => ccM0) i).map_eq)

theorem indep_xs {n : ℕ} : iIndepFun (xs.{u_1, u_2} (n := n)) (P n) := by
  have hX : iIndepFun (fun i (x : Fin n → CC0) => x i) (μX0 n) :=
    iIndepFun_pi (fun i => aemeasurable_id)
  have hX_prod : iIndepFun (fun i (p : Ω0 n) => p.1 i) (P0 n) := by
    have hfm (i : Fin n) : Measurable (fun x : Fin n → CC0 => x i) := measurable_pi_apply i
    have hm_prod (i : Fin n) : Measurable (fun (p : Ω0 n) => p.1 i) := (hfm i).comp measurable_fst
    rw [iIndepFun_iff_map_fun_eq_pi_map (fun i => (hm_prod i).aemeasurable)]
    change Measure.map Prod.fst (P0 n) = Measure.pi fun i => Measure.map (fun p : Ω0 n => p.1 i) (P0 n)
    rw [P0, Measure.map_fst_prod, measure_univ, one_smul]
    have hf_pi := (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hfm i).aemeasurable)).mp hX
    change Measure.map id (μX0 n) = Measure.pi fun i => Measure.map (fun x : Fin n → CC0 => x i) (μX0 n) at hf_pi
    rw [Measure.map_id] at hf_pi
    refine hf_pi.trans ?_
    congr 1
    ext1 i
    symm
    have h2 : (fun (p : Ω0 n) => p.1 i) = (fun a : Fin n → CC0 => a i) ∘ Prod.fst := rfl
    rw [h2, ← Measure.map_map (hfm i) measurable_fst]
    simp only [Measure.map_fst_prod, measure_univ, one_smul]
  have hX_comp := iIndepFun.comp hX_prod (fun _ => ofCC) (fun _ => measurable_ofCC)
  exact iIndepFun_toΩ hX_comp (fun i => measurable_ofCC.comp ((measurable_pi_apply i).comp measurable_fst))

theorem indep_eps {n : ℕ} : iIndepFun (eps.{u_2} (n := n)) (P n) := by
  have hm_b : Measurable (fun b : Bool => if b then (1:ℝ) else -1) := by
    intro s _; exact MeasurableSet.of_discrete
  have hE : iIndepFun (fun i (e : Fin n → Bool) => e i) (μE0 n) :=
    iIndepFun_pi (fun i => aemeasurable_id)
  have hE_prod : iIndepFun (fun i (p : Ω0 n) => p.2 i) (P0 n) := by
    have hfm (i : Fin n) : Measurable (fun e : Fin n → Bool => e i) := measurable_pi_apply i
    have hm_prod (i : Fin n) : Measurable (fun (p : Ω0 n) => p.2 i) := (hfm i).comp measurable_snd
    rw [iIndepFun_iff_map_fun_eq_pi_map (fun i => (hm_prod i).aemeasurable)]
    change Measure.map Prod.snd (P0 n) = Measure.pi fun i => Measure.map (fun p : Ω0 n => p.2 i) (P0 n)
    rw [P0, Measure.map_snd_prod, measure_univ, one_smul]
    have hf_pi := (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hfm i).aemeasurable)).mp hE
    change Measure.map id (μE0 n) = Measure.pi fun i => Measure.map (fun e : Fin n → Bool => e i) (μE0 n) at hf_pi
    rw [Measure.map_id] at hf_pi
    refine hf_pi.trans ?_
    congr 1
    ext1 i
    symm
    have h2 : (fun (p : Ω0 n) => p.2 i) = (fun b : Fin n → Bool => b i) ∘ Prod.snd := rfl
    rw [h2, ← Measure.map_map (hfm i) measurable_snd]
    simp only [Measure.map_snd_prod, measure_univ, one_smul]
  have hE_comp := iIndepFun.comp hE_prod (fun _ => (fun b => if b then 1 else -1)) (fun _ => hm_b)
  exact iIndepFun_toΩ hE_comp (fun i => hm_b.comp ((measurable_pi_apply i).comp measurable_snd))

theorem indep_xs_eps {n : ℕ} :
    IndepFun (fun w i => xs.{u_1, u_2} (n := n) i w) (fun w i => eps.{u_2} (n := n) i w) (P n) := by
  have hm_b : Measurable (fun b : Bool => if b then (1:ℝ) else -1) := by
    intro s _; exact MeasurableSet.of_discrete
  have hX_meas : Measurable (fun x : Fin n → CC0 => fun i => ofCC (x i)) :=
    measurable_pi_lambda _ (fun i => measurable_ofCC.comp (measurable_pi_apply i))
  have hE_meas : Measurable (fun e : Fin n → Bool => fun i => if e i then (1:ℝ) else -1) :=
    measurable_pi_lambda _ (fun i => hm_b.comp (measurable_pi_apply i))
  have h_prod : IndepFun (fun p : Ω0 n => fun i => ofCC (p.1 i))
      (fun p : Ω0 n => fun i => if p.2 i then (1:ℝ) else -1) (P0 n) :=
    indepFun_prod hX_meas hE_meas (μ := μX0 n) (ν := μE0 n)
  have h_meas1 : Measurable (fun p : Ω0 n => fun i => ofCC (p.1 i)) :=
    hX_meas.comp measurable_fst
  have h_meas2 : Measurable (fun p : Ω0 n => fun i => if p.2 i then (1:ℝ) else -1) :=
    hE_meas.comp measurable_snd
  exact indepFun_toΩ h_prod h_meas1 h_meas2

theorem isIIDDesign {n : ℕ} :
    @IsIIDDesignWithRademacher CC.{u_1} (Ω.{u_2} n) _ _ n xs eps (P n) ccM := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; exact measurable_xs i
  · exact indep_xs
  · intro i; exact map_xs i
  · intro i; exact measurable_eps i
  · exact indep_eps
  · intro i
    constructor
    · intro w
      cases hw : (toΩ w).2 i <;> simp [eps, hw]
    · have hset : {w : Ω n | eps i w = 1} = toΩ ⁻¹' (Set.univ ×ˢ ((fun e : Fin n → Bool => e i) ⁻¹' ({true} : Set Bool))) := by
        ext w
        simp only [Set.mem_setOf_eq, eps, Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and,
          Set.mem_singleton_iff]
        constructor
        · intro h
          split_ifs at h with he
          · exact he
          · norm_num at h
        · intro he
          rw [if_pos he]
      rw [hset]
      have h_meas_e : MeasurableSet ((fun e : Fin n → Bool => e i) ⁻¹' ({true} : Set Bool)) :=
        measurable_pi_apply i (MeasurableSet.of_discrete)
      have h_meas_set : MeasurableSet ((Set.univ : Set (Fin n → CC0)) ×ˢ ((fun e : Fin n → Bool => e i) ⁻¹' ({true} : Set Bool))) :=
        MeasurableSet.univ.prod h_meas_e
      rw [measureReal_def, map_toΩ _ h_meas_set]
      rw [P0, Measure.prod_prod, measure_univ, one_mul]
      have hμE : μE0 n ((fun e : Fin n → Bool => e i) ⁻¹' ({true} : Set Bool)) = 2⁻¹ := by
        rw [← Measure.map_apply (measurable_pi_apply i) MeasurableSet.of_discrete]
        rw [μE0, (measurePreserving_eval (fun _ : Fin n => radBool) i).map_eq, radBool_true]
      rw [hμE]
      norm_num
  · exact indep_xs_eps

theorem section_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    {μ' : Measure β} [SFinite μ] [IsProbabilityMeasure μ'] {g : α × β → ℝ}
    (h : AEStronglyMeasurable g (μ.prod μ')) :
    ∀ᵐ b ∂μ', AEStronglyMeasurable (fun a => g (a, b)) μ := by
  have h2 := h.prod_swap.prodMk_left
  simpa using h2

noncomputable def M (x : CC.{u_1}) : ℝ := M0 x.down

def F : Set (CC.{u_1} → ℝ) := {f | (f ⁻¹' {0}ᶜ).Countable ∧ ∀ x, |f x| ≤ M x}

theorem isStarShaped : IsStarShapedAroundOrigin F.{u_1} := by
  intro f hf α hα
  rcases hf with ⟨hfc, hfb⟩
  refine ⟨?_, ?_⟩
  · refine hfc.mono ?_
    intro x hx
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] at hx ⊢
    intro h
    apply hx
    show α * f x = 0
    rw [h, mul_zero]
  · intro x
    have hα0 : 0 ≤ α := hα.1
    have hα1 : α ≤ 1 := hα.2
    rw [abs_mul, abs_of_nonneg hα0]
    have h1 := hfb x
    have hM_nonneg : 0 ≤ M x := le_of_lt (M0_pos x.down)
    nlinarith

theorem isUniformlyBounded : IsUniformlyBounded F.{u_1} 1 := by
  intro f hf x
  rcases hf with ⟨_, hfb⟩
  have h1 := hfb x
  have h2 : M x ≤ 1 := M0_le_one x.down
  linarith

theorem f_meas (f : CC.{u_1} → ℝ) (hf : f ∈ F.{u_1}) : Measurable f := by
  rcases hf with ⟨hfc, _⟩
  intro U hU
  by_cases h0 : (0 : ℝ) ∈ U
  · have hsub : (f ⁻¹' U)ᶜ ⊆ f ⁻¹' {0}ᶜ := by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_preimage] at hx
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hfx
      apply hx
      rw [hfx]
      exact h0
    have hc : ((f ⁻¹' U)ᶜ).Countable := hfc.mono hsub
    have hc_pre : (ofCC ⁻¹' (f ⁻¹' U)ᶜ).Countable := hc.preimage ULift.up_injective
    have hms0 : MeasurableSet (ofCC ⁻¹' (f ⁻¹' U)) := by
      rw [ms0_iff]
      right
      have : (ofCC ⁻¹' (f ⁻¹' U))ᶜ = ofCC ⁻¹' (f ⁻¹' U)ᶜ := rfl
      rwa [this]
    exact measurable_toCC hms0
  · have hsub : f ⁻¹' U ⊆ f ⁻¹' {0}ᶜ := by
      intro x hx
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hfx
      apply h0
      rw [← hfx]
      exact hx
    have hc : (f ⁻¹' U).Countable := hfc.mono hsub
    have hc_pre : (ofCC ⁻¹' (f ⁻¹' U)).Countable := hc.preimage ULift.up_injective
    have hms0 : MeasurableSet (ofCC ⁻¹' (f ⁻¹' U)) := by
      rw [ms0_iff]
      left
      exact hc_pre
    exact measurable_toCC hms0

open Classical in
theorem popNormSq_zero (f : CC.{u_1} → ℝ) (hf : f ∈ F.{u_1}) : popNormSq ccM f = 0 := by
  unfold popNormSq
  rcases hf with ⟨hfc, _⟩
  have hsub : {x | (f x) ^ 2 ≠ 0} ⊆ f ⁻¹' {0}ᶜ := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    apply hx
    rw [h, sq, mul_zero]
  have hc : {x : CC | (f x) ^ 2 ≠ 0}.Countable := hfc.mono hsub
  have hc_pre : (ofCC ⁻¹' {x : CC | (f x) ^ 2 ≠ 0}).Countable := hc.preimage ULift.up_injective
  have hms : MeasurableSet {x : CC | (f x) ^ 2 ≠ 0} := by
    have : MeasurableSet (ofCC ⁻¹' {x : CC | (f x) ^ 2 ≠ 0}) := ms0_iff _ |>.mpr (Or.inl hc_pre)
    exact measurable_toCC this
  have h_null : ccM {x : CC | (f x) ^ 2 ≠ 0} = 0 := by
    rw [ccM, Measure.map_apply measurable_ofCC hms]
    rw [ccM0_apply _ (Or.inl hc_pre), if_pos hc_pre]
  have hae : (fun x => (f x) ^ 2) =ᵐ[ccM] fun _ => 0 :=
    ae_iff.mpr h_null
  rw [integral_congr_ae hae]
  simp

open Classical in
theorem popNorm_zero (f : CC.{u_1} → ℝ) (hf : f ∈ F.{u_1}) : popNorm ccM f = 0 := by
  unfold popNorm
  rw [popNormSq_zero f hf, Real.sqrt_zero]

open Classical in
theorem satisfiesCritical {n : ℕ} (hn_pos : 0 < n) :
    SatisfiesCriticalInequality (xs.{u_1, u_2} (n := n)) (eps.{u_2} (n := n)) (P.{u_2} n) ccM.{u_1} F.{u_1} 1 (1 / 2) := by
  constructor
  · norm_num
  · have hR : popRademacherComplexity (xs.{u_1, u_2} (n := n)) (eps.{u_2} (n := n)) (P.{u_2} n) ccM.{u_1} F.{u_1} (1 / 2) = 0 := by
      unfold popRademacherComplexity
      refine integral_non_aestronglyMeasurable ?_
      intro hG
      have h_mp_ofΩ : MeasurePreserving (@ofΩ.{u_2} n) (P0 n) (P n) := ⟨measurable_ofΩ, rfl⟩
      have hG0 : AEStronglyMeasurable (fun w : Ω0 n =>
          ⨆ f : {f : CC → ℝ // f ∈ F ∧ popNorm ccM f ≤ 1 / 2},
            |(∑ i, eps i (ofΩ w) * f.1 (xs i (ofΩ w))) / (n : ℝ)|) (P0 n) :=
        hG.comp_measurePreserving h_mp_ofΩ
      have h_sec := section_fst (μ := μX0 n) (μ' := μE0 n) hG0
      have he0 : μE0 n ({fun _ : Fin n => true} : Set (Fin n → Bool)) ≠ 0 := by
        rw [μE0, Measure.pi_singleton]
        intro h_zero
        have : (∏ i : Fin n, radBool {true}) = (2⁻¹ : ENNReal) ^ n := by
          simp [radBool_true]
        rw [this] at h_zero
        exact (pow_ne_zero n (by norm_num)) h_zero
      have he0_ae : AEStronglyMeasurable (fun x : Fin n → CC0 =>
          ⨆ f : {f : CC → ℝ // f ∈ F ∧ popNorm ccM f ≤ 1 / 2},
            |(∑ i, eps i (ofΩ (x, fun _ => true)) * f.1 (xs i (ofΩ (x, fun _ => true)))) / (n : ℝ)|) (μX0 n) := by
        by_contra h_not
        have h_sub : ({fun _ : Fin n => true} : Set (Fin n → Bool)) ⊆ {e : Fin n → Bool | ¬ AEStronglyMeasurable (fun x =>
            ⨆ f : {f : CC → ℝ // f ∈ F ∧ popNorm ccM f ≤ 1 / 2},
              |(∑ i, eps i (ofΩ (x, e)) * f.1 (xs i (ofΩ (x, e)))) / (n : ℝ)|) (μX0 n)} := by
          intro e he
          simp only [Set.mem_singleton_iff] at he
          subst he
          exact h_not
        have h_le : μE0 n ({fun _ : Fin n => true} : Set (Fin n → Bool)) ≤
            μE0 n {e : Fin n → Bool | ¬ AEStronglyMeasurable (fun x =>
              ⨆ f : {f : CC → ℝ // f ∈ F ∧ popNorm ccM f ≤ 1 / 2},
                |(∑ i, eps i (ofΩ (x, e)) * f.1 (xs i (ofΩ (x, e)))) / (n : ℝ)|) (μX0 n)} :=
          measure_mono h_sub
        rw [ae_iff.mp h_sec] at h_le
        exact he0 (nonpos_iff_eq_zero.mp h_le)
      have h_sup_eq (x : Fin n → CC0) :
          (⨆ f : {f : CC → ℝ // f ∈ F ∧ popNorm ccM f ≤ 1 / 2},
            |(∑ i, eps i (ofΩ (x, fun _ => true)) * f.1 (xs i (ofΩ (x, fun _ => true)))) / (n : ℝ)|) =
            (∑ i, M0 (x i)) / (n : ℝ) := by
        change (⨆ f : {f : CC → ℝ // f ∈ F ∧ popNorm ccM f ≤ 1 / 2},
            |(∑ i, (1 : ℝ) * f.1 (ofCC (x i))) / (n : ℝ)|) =
            (∑ i, M0 (x i)) / (n : ℝ)
        simp only [one_mul]
        have hub (f : {f : CC → ℝ // f ∈ F ∧ popNorm ccM f ≤ 1 / 2}) :
            |(∑ i, f.1 (ofCC (x i))) / (n : ℝ)| ≤ (∑ i, M0 (x i)) / (n : ℝ) := by
          rcases f.2.1 with ⟨_, hfb⟩
          have hsum_le : |∑ i, f.1 (ofCC (x i))| ≤ ∑ i, M0 (x i) := by
            refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
            refine Finset.sum_le_sum ?_
            intro i _
            exact hfb (ofCC (x i))
          rw [abs_div, Nat.abs_cast]
          exact div_le_div_of_nonneg_right hsum_le (Nat.cast_nonneg n)
        let S := Set.range (fun i => ofCC (x i))
        let f_cand (z : CC) : ℝ := if z ∈ S then M z else 0
        have hf_cand_supp : {z | f_cand z ≠ 0} ⊆ S := by
          intro z hz
          simp only [Set.mem_setOf_eq, f_cand] at hz
          split_ifs at hz with hzs
          · exact hzs
          · contradiction
        have hS_fin : S.Finite := Set.finite_range _
        have hf_cand_count : (f_cand ⁻¹' {0}ᶜ).Countable :=
          (hS_fin.countable).mono hf_cand_supp
        have hf_cand_bdd (z : CC) : |f_cand z| ≤ M z := by
          simp only [f_cand]
          split_ifs with hzs
          · have hMp : 0 < M z := M0_pos z.down
            rw [abs_of_pos hMp]
          · rw [abs_zero]; exact le_of_lt (M0_pos z.down)
        have hf_cand_F : f_cand ∈ F := ⟨hf_cand_count, hf_cand_bdd⟩
        have hf_cand_norm : popNorm ccM f_cand ≤ 1 / 2 := by
          rw [popNorm_zero f_cand hf_cand_F]
          norm_num
        let f_sub : {f : CC → ℝ // f ∈ F ∧ popNorm ccM f ≤ 1 / 2} := ⟨f_cand, hf_cand_F, hf_cand_norm⟩
        haveI : Nonempty {f : CC → ℝ // f ∈ F ∧ popNorm ccM f ≤ 1 / 2} := ⟨f_sub⟩
        have hlb : (∑ i, M0 (x i)) / (n : ℝ) ≤
            ⨆ f : {f : CC → ℝ // f ∈ F ∧ popNorm ccM f ≤ 1 / 2}, |(∑ i, f.1 (ofCC (x i))) / (n : ℝ)| := by
          have hbdd : BddAbove (Set.range fun f : {f // f ∈ F ∧ popNorm ccM f ≤ 1 / 2} =>
              |(∑ i, f.1 (ofCC (x i))) / (n : ℝ)|) := by
            use (∑ i, M0 (x i)) / (n : ℝ)
            rintro _ ⟨f, rfl⟩
            exact hub f
          refine le_ciSup_of_le hbdd f_sub ?_
          show (∑ i, M0 (x i)) / (n : ℝ) ≤ |(∑ i, f_cand (ofCC (x i))) / (n : ℝ)|
          have heq_i (i : Fin n) : f_cand (ofCC (x i)) = M0 (x i) := by
            simp only [f_cand, S, Set.mem_range, exists_apply_eq_apply, ↓reduceIte]
            rfl
          simp_rw [heq_i]
          have hpos_sum : 0 ≤ ∑ i, M0 (x i) := Finset.sum_nonneg fun i _ => le_of_lt (M0_pos (x i))
          rw [abs_div, abs_of_nonneg hpos_sum, abs_of_pos (by positivity)]
        exact le_antisymm (ciSup_le hub) hlb
      have he0_ae' : AEStronglyMeasurable (fun x : Fin n → CC0 => (∑ i, M0 (x i)) / (n : ℝ)) (μX0 n) := by
        refine he0_ae.congr ?_
        filter_upwards with x
        exact h_sup_eq x
      have h_sum_aesm : AEStronglyMeasurable (fun x : Fin n → CC0 => ∑ i, M0 (x i)) (μX0 n) := by
        have : (fun x : Fin n → CC0 => ∑ i, M0 (x i)) =
            (fun y => (n : ℝ) * y) ∘ (fun x => (∑ i, M0 (x i)) / (n : ℝ)) := by
          ext x
          simp only [Function.comp_apply]
          rw [mul_div_cancel₀ _ (by positivity)]
        rw [this]
        exact (continuous_const_mul (n : ℝ)).measurable.comp_aemeasurable he0_ae'.aemeasurable |>.aestronglyMeasurable
      cases n with
      | zero => omega
      | succ m =>
        let eq := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => CC0) 0
        have mp := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => ccM0) 0
        have mp_symm := mp.symm
        have h_comp_aesm := h_sum_aesm.comp_measurePreserving mp_symm
        have h_sec_m := section_fst (μ := ccM0) (μ' := μX0 m) h_comp_aesm
        obtain ⟨y, hy⟩ := h_sec_m.exists
        have h_sum_split (z : CC0) : (∑ i : Fin (m + 1), M0 (eq.symm (z, y) i)) =
            M0 z + ∑ j : Fin m, M0 (y j) := by
          rw [Fin.sum_univ_succ]
          rfl
        have hy' : AEStronglyMeasurable (fun z : CC0 => M0 z + ∑ j : Fin m, M0 (y j)) ccM0 := by
          refine hy.congr ?_
          filter_upwards with z
          exact h_sum_split z
        have h_c : AEStronglyMeasurable (fun z : CC0 => (M0 z + ∑ j : Fin m, M0 (y j)) - ∑ j : Fin m, M0 (y j)) ccM0 :=
          (continuous_sub_right (∑ j : Fin m, M0 (y j))).measurable.comp_aemeasurable hy'.aemeasurable |>.aestronglyMeasurable
        simp only [add_sub_cancel_right] at h_c
        exact M0_not_aesm h_c
    rw [hR]
    norm_num

end HighDimStat.Localization.Disproof

open HighDimStat.Localization HighDimStat.Localization.Disproof in
theorem solution :
    ¬ (∃ c1 c2 c0 c1' c2' : ℝ, 0 < c1 ∧ 0 < c2 ∧ 0 < c0 ∧ 0 < c1' ∧ 0 < c2' ∧
      ∀ {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω] {n : ℕ}, 0 < n →
      ∀ (xs : Fin n → Ω → X) (eps : Fin n → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
        (μ : Measure X) [IsProbabilityMeasure μ],
        IsIIDDesignWithRademacher xs eps P μ →
      ∀ (F : Set (X → ℝ)), IsStarShapedAroundOrigin F →
      ∀ (b : ℝ), 0 < b → IsUniformlyBounded F b → (∀ f ∈ F, Measurable f) →
      ∀ (δn t : ℝ), SatisfiesCriticalInequality xs eps P μ F b δn → δn ≤ t →
        (1 - c1 * Real.exp (-c2 * (n : ℝ) * t ^ 2 / b ^ 2) ≤
            P.real {ω | ∀ f ∈ F,
              |empiricalNormSq (fun i => xs i ω) f - popNormSq μ f| ≤
                (1 / 2) * popNormSq μ f + t ^ 2 / 2}) ∧
        ((n : ℝ) * δn ^ 2 ≥ (2 / c2) * Real.log (4 * Real.log (1 / δn)) →
          1 - c1' * Real.exp (-c2' * (n : ℝ) * δn ^ 2 / b ^ 2) ≤
            P.real {ω | ∀ f ∈ F,
              |empiricalNorm (fun i => xs i ω) f - popNorm μ f| ≤ c0 * δn})) := by
  classical
  rintro ⟨c1, c2, c0, c1', c2', hc1, hc2, _, _, _, h_all⟩
  obtain ⟨n, hn_pos, h_exp_lt⟩ := exists_n_exp_lt c1 c2 hc1 hc2
  have h_spec := h_all (X := CC) (Ω := Ω n) hn_pos
    xs eps (P n) ccM isIIDDesign
    F isStarShaped 1 (by norm_num) isUniformlyBounded f_meas
    (1 / 2) (1 / 2) (satisfiesCritical hn_pos) (by rfl)
  have h_ineq := h_spec.1
  have h_empty : {ω : Ω n | ∀ f ∈ F,
      |empiricalNormSq (fun i => xs i ω) f - popNormSq ccM f| ≤
        (1 / 2) * popNormSq ccM f + (1 / 2) ^ 2 / 2} = (∅ : Set (Ω n)) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_forall]
    let S := Set.range (fun i => xs i ω)
    let g_cand (z : CC) : ℝ := if z ∈ S then (1 / 2 : ℝ) else 0
    have hS_fin : S.Finite := Set.finite_range _
    have hg_supp : {z | g_cand z ≠ 0} ⊆ S := by
      intro z hz
      simp only [Set.mem_setOf_eq, g_cand] at hz
      split_ifs at hz with hzs
      · exact hzs
      · contradiction
    have hg_count : (g_cand ⁻¹' {0}ᶜ).Countable := hS_fin.countable.mono hg_supp
    have hg_bdd (z : CC) : |g_cand z| ≤ M z := by
      simp only [g_cand]
      split_ifs
      · rw [abs_of_pos (by norm_num)]; exact M0_ge_half z.down
      · rw [abs_zero]; exact le_of_lt (M0_pos z.down)
    have hg_F : g_cand ∈ F := ⟨hg_count, hg_bdd⟩
    use g_cand, hg_F
    rw [popNormSq_zero g_cand hg_F]
    have hemp : empiricalNormSq (fun i => xs i ω) g_cand = 1 / 4 := by
      unfold empiricalNormSq
      have hval (i : Fin n) : g_cand (xs i ω) = 1 / 2 := by
        simp only [g_cand, S, Set.mem_range, exists_apply_eq_apply, ↓reduceIte]
      simp_rw [hval]
      have : (∑ i : Fin n, (1 / 2 : ℝ) ^ 2) = (n : ℝ) * (1 / 4) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      rw [this, mul_div_cancel_left₀ _ (by positivity)]
    rw [hemp]
    norm_num
  rw [h_empty, measureReal_empty] at h_ineq
  have heq : -c2 * (n : ℝ) * (1 / 2) ^ 2 / 1 ^ 2 = - (c2 * (n : ℝ) * (1 / 2) ^ 2 / 1 ^ 2) := by ring
  linarith
