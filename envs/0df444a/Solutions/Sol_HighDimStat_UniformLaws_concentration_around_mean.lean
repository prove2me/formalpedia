-- Prove2me | solution 1 for HighDimStat.UniformLaws.concentration_around_mean
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-10-31T01:18:06.506404+00:00
-- url     : https://prove2.me/submissions/493a7b74-074c-46b3-9f13-faca9f231091

import Mathlib
import Definitions.Def_HighDimStat_UniformLaws_empProcessDeviation
import Definitions.Def_HighDimStat_UniformLaws_IsUniformlyBounded

set_option autoImplicit false
set_option linter.deprecated false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory HighDimStat.UniformLaws

namespace Cex9bcc

/-- The reals with the countable–cocountable σ-algebra. -/
def CC : Type := ℝ

def toR : CC → ℝ := id
def ofR : ℝ → CC := id

instance instMS : MeasurableSpace CC where
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

theorem ms_iff (s : Set CC) : MeasurableSet s ↔ s.Countable ∨ sᶜ.Countable := Iff.rfl

theorem univ_not_countable : ¬ (Set.univ : Set CC).Countable := by
  intro h
  have h' : (Set.univ : Set ℝ).Countable := h
  have := h'.measure_zero (volume : Measure ℝ)
  simp at this

/-- The positive half-line, a set that is neither countable nor cocountable. -/
def A : Set CC := {x | 0 < toR x}

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
/-- The countable–cocountable probability measure. -/
noncomputable def ccM : Measure CC :=
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
theorem ccM_apply (s : Set CC) (hs : MeasurableSet s) :
    ccM s = if s.Countable then 0 else 1 := by
  unfold ccM
  exact Measure.ofMeasurable_apply s hs

open Classical in
instance : IsProbabilityMeasure ccM :=
  ⟨by rw [ccM_apply _ MeasurableSet.univ, if_neg univ_not_countable]⟩

open Classical in
theorem null_countable {N : Set CC} (h : ccM N = 0) : N.Countable := by
  have hT := measurableSet_toMeasurable ccM N
  have h0 : ccM (toMeasurable ccM N) = 0 := by rwa [measure_toMeasurable]
  rw [ccM_apply _ hT] at h0
  split_ifs at h0 with hc
  · exact hc.mono (subset_toMeasurable _ _)
  · simp at h0

open Classical in
theorem ccM_singleton (a : CC) : ccM {a} = 0 := by
  rw [ccM_apply _ (Or.inl (Set.countable_singleton a)), if_pos (Set.countable_singleton a)]

/-- The Rademacher law on `ℝ`. -/
noncomputable def rad : Measure ℝ := (2⁻¹ : ENNReal) • (Measure.dirac (1:ℝ) + Measure.dirac (-1))

instance : IsProbabilityMeasure rad := by
  constructor
  simp only [rad, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
  rw [one_add_one_eq_two, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]

theorem rad_ae : ∀ᵐ e ∂rad, |e| = 1 := by
  rw [ae_iff]
  simp [rad, Measure.dirac_apply]

noncomputable def ν : Measure (CC × ℝ) := ccM.prod rad
noncomputable def Q : Measure (ℕ → CC × ℝ) := Measure.infinitePi (fun _ => ν)

abbrev Ω0 : Type := (CC × ℝ) × (ℕ → CC × ℝ)
noncomputable def P0 : Measure Ω0 := ν.prod Q

instance : IsProbabilityMeasure ν := by unfold ν; infer_instance
instance : IsProbabilityMeasure Q := by unfold Q; infer_instance
instance : IsProbabilityMeasure P0 := by unfold P0; infer_instance

def Z0 : ℕ → Ω0 → CC × ℝ
  | 0, ω => ω.1
  | k + 1, ω => ω.2 k

def Xs : ℕ → Ω0 → CC := fun i ω => (Z0 i ω).1

def X00 : Ω0 → CC := fun ω => ω.1.1

theorem Z0_meas (i : ℕ) : Measurable (Z0 i) := by
  cases i with
  | zero => exact measurable_fst
  | succ k => exact (measurable_pi_apply k).comp measurable_snd

theorem mapZ (i : ℕ) : P0.map (Z0 i) = ν := by
  cases i with
  | zero =>
    show P0.map Prod.fst = ν
    simp [P0, Measure.map_fst_prod]
  | succ k =>
    have : Z0 (k + 1) = (fun w : ℕ → CC × ℝ => w k) ∘ Prod.snd := rfl
    rw [this, ← Measure.map_map (measurable_pi_apply k) measurable_snd]
    simp only [P0, Measure.map_snd_prod, measure_univ, one_smul]
    exact Measure.infinitePi_map_eval _ k

open Classical in
/-- The function class: a spike `1` at `a` for `a > 0`, a notch `1/2 - 1/2·[x = a]` for `a ≤ 0`. -/
noncomputable def f0 : CC → CC → ℝ := fun a x =>
  if a ∈ A then (if x = a then 1 else 0) else (if x = a then 0 else 1/2)

open Classical in
noncomputable def c0 (a : CC) : ℝ := if a ∈ A then 0 else 1/2

theorem f0_meas (a : CC) : Measurable (f0 a) := by
  classical
  have hs : MeasurableSet {x : CC | x = a} := Or.inl (by simp)
  unfold f0
  by_cases ha : a ∈ A
  · simp only [ha, ↓reduceIte]
    exact Measurable.ite hs measurable_const measurable_const
  · simp only [ha, ↓reduceIte]
    exact Measurable.ite hs measurable_const measurable_const

theorem f0_bound (a x : CC) : |f0 a x| ≤ 1 := by
  unfold f0
  split_ifs <;> norm_num

theorem mapX0 : P0.map X00 = ccM := by
  have : X00 = Prod.fst ∘ Z0 0 := rfl
  rw [this, ← Measure.map_map measurable_fst (Z0_meas 0), mapZ]
  simp [ν, Measure.map_fst_prod]

theorem f0_ae (a : CC) : f0 a =ᵐ[ccM] fun _ => c0 a := by
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (t := {a}) ?_ (ccM_singleton a)
  intro x hx
  simp only [Set.mem_setOf_eq] at hx
  simp only [Set.mem_singleton_iff]
  by_contra hxa
  apply hx
  unfold f0 c0
  split_ifs <;> simp_all

theorem int_eq (a : CC) : ∫ ω', f0 a (X00 ω') ∂P0 = c0 a := by
  have h1 : ∫ y, f0 a y ∂(P0.map X00) = ∫ ω', f0 a (X00 ω') ∂P0 :=
    integral_map (measurable_fst.comp measurable_fst).aemeasurable
      (f0_meas a).aestronglyMeasurable
  rw [← h1, mapX0, integral_congr_ae (f0_ae a)]
  simp

theorem succ_injOn (S : Set ℕ) : Set.InjOn Nat.succ S := fun _ _ _ _ h => Nat.succ.inj h

theorem box (s : Finset ℕ) (t : ℕ → Set (CC × ℝ)) :
    (fun ω : Ω0 => fun i => Z0 i ω) ⁻¹' (Set.pi ↑s t) =
      {y | 0 ∈ s → y ∈ t 0} ×ˢ
        Set.pi ↑(s.preimage Nat.succ (succ_injOn _)) (fun k => t (k+1)) := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod, Set.mem_setOf_eq,
    Finset.mem_preimage]
  constructor
  · intro h
    exact ⟨fun h0 => h 0 h0, fun k hk => h (k+1) hk⟩
  · rintro ⟨h0, h1⟩ i hi
    cases i with
    | zero => exact h0 hi
    | succ k => exact h1 k hi

theorem prod_split (s : Finset ℕ) (g : ℕ → ENNReal) :
    ∏ i ∈ s, g i = (if 0 ∈ s then g 0 else 1) *
      ∏ k ∈ s.preimage Nat.succ (succ_injOn _), g (k+1) := by
  classical
  rw [← Finset.prod_filter_mul_prod_filter_not s (fun i => i = 0)]
  congr 1
  · rw [Finset.filter_eq' s 0]
    split_ifs <;> simp
  · symm
    apply Finset.prod_nbij' (fun k => k + 1) (fun i => i - 1)
    · intro a ha
      rw [Finset.mem_filter]
      exact ⟨(Finset.mem_preimage (f := Nat.succ)).mp ha, by omega⟩
    · intro a ha
      rw [Finset.mem_filter] at ha
      rw [Finset.mem_preimage (f := Nat.succ)]
      have : Nat.succ (a - 1) = a := by omega
      rw [this]; exact ha.1
    · intro a _; simp
    · intro a ha
      rw [Finset.mem_filter] at ha
      show a - 1 + 1 = a
      omega
    · intro a _; rfl

theorem hInd : iIndepFun Z0 P0 := by
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map Z0_meas]
  have hfun : (fun i => P0.map (Z0 i)) = fun _ => ν := funext mapZ
  rw [hfun]
  refine Measure.eq_infinitePi _ ?_
  intro s t ht
  have hF : Measurable (fun ω : Ω0 => fun i => Z0 i ω) := measurable_pi_lambda _ Z0_meas
  rw [Measure.map_apply hF (MeasurableSet.pi s.countable_toSet (fun i _ => ht i)), box, P0,
    Measure.prod_prod, Q, Measure.infinitePi_pi (fun _ => ν) (fun k _ => ht (k+1)), prod_split s (fun i => ν (t i))]
  congr 1
  by_cases h0 : 0 ∈ s
  · simp [h0]
  · simp [h0]

theorem hIndep : iIndepFun Xs P0 :=
  hInd.comp (fun _ => Prod.fst) (fun _ => measurable_fst)

theorem mapX (i : ℕ) : P0.map (Xs i) = ccM := by
  have : Xs i = Prod.fst ∘ Z0 i := rfl
  rw [this, ← Measure.map_map measurable_fst (Z0_meas i), mapZ]
  simp [ν, Measure.map_fst_prod]

theorem hIdent (i : ℕ) : IdentDistrib (Xs i) X00 P0 P0 :=
  ⟨(measurable_fst.comp (Z0_meas i)).aemeasurable,
    (measurable_fst.comp measurable_fst).aemeasurable, by rw [mapX, mapX0]⟩

theorem section_fst {α β : Type} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    {μ' : Measure β} [SFinite μ] [IsProbabilityMeasure μ'] {g : α × β → ℝ}
    (h : AEStronglyMeasurable g (μ.prod μ')) :
    ∀ᵐ b ∂μ', AEStronglyMeasurable (fun a => g (a, b)) μ := by
  have h2 := h.prod_swap.prodMk_left
  simpa using h2

instance : Nonempty CC := ⟨ofR 0⟩

theorem bddM (x : CC) : BddAbove (Set.range fun a => |f0 a x|) :=
  ⟨1, by rintro _ ⟨a, rfl⟩; exact f0_bound a x⟩

theorem M_A {x : CC} (hx : x ∈ A) : (⨆ a, |f0 a x|) = 1 := by
  refine le_antisymm (ciSup_le fun a => f0_bound a x) (le_ciSup_of_le (bddM x) x ?_)
  simp [f0, hx]

theorem M_Ac {x : CC} (hx : x ∉ A) : (⨆ a, |f0 a x|) = 1/2 := by
  refine le_antisymm (ciSup_le ?_) (le_ciSup_of_le (bddM x) (ofR (toR x - 1)) ?_)
  · intro a
    unfold f0
    by_cases ha : a ∈ A
    · have : x ≠ a := fun h => hx (h ▸ ha)
      simp [ha, this]
    · simp only [ha, ↓reduceIte]
      split_ifs <;> norm_num
  · have hxA : ¬ (0 < toR x) := hx
    have ha : ofR (toR x - 1) ∉ A := by
      intro h
      have h' : 0 < toR x - 1 := h
      exact hxA (by linarith)
    have hne : x ≠ ofR (toR x - 1) := by
      intro h
      have : toR x = toR x - 1 := congrArg toR h
      linarith
    simp [f0, ha, hne]

theorem M_not_aesm : ¬ AEStronglyMeasurable (fun x => ⨆ a, |f0 a x|) ccM := by
  intro h
  have hm := h.aemeasurable
  have hM' : Measurable (hm.mk _) := hm.measurable_mk
  have hN : ({x | ¬ (⨆ a, |f0 a x|) = hm.mk _ x} : Set CC).Countable :=
    null_countable (ae_iff.1 hm.ae_eq_mk)
  have hE : MeasurableSet {x | (3/4 : ℝ) < hm.mk _ x} := measurableSet_lt measurable_const hM'
  rcases (ms_iff _).1 hE with hc | hc
  · apply A_not_countable
    refine (hc.union hN).mono ?_
    intro x hx
    by_cases hxN : (⨆ a, |f0 a x|) = hm.mk _ x
    · left
      simp only [Set.mem_setOf_eq]
      rw [← hxN, M_A hx]; norm_num
    · right; exact hxN
  · apply Ac_not_countable
    refine (hc.union hN).mono ?_
    intro x hx
    by_cases hxN : (⨆ a, |f0 a x|) = hm.mk _ x
    · left
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
      rw [← hxN, M_Ac hx]; norm_num
    · right; exact hxN

theorem dev0_bound (a x : CC) : |f0 a x - c0 a| ≤ 1 := by
  unfold f0 c0
  split_ifs <;> norm_num

theorem bddDev0 (x : CC) : BddAbove (Set.range fun a => |f0 a x - c0 a|) :=
  ⟨1, by rintro _ ⟨a, rfl⟩; exact dev0_bound a x⟩

theorem dev0_A {x : CC} (hx : x ∈ A) : (⨆ a, |f0 a x - c0 a|) = 1 := by
  refine le_antisymm (ciSup_le fun a => dev0_bound a x) (le_ciSup_of_le (bddDev0 x) x ?_)
  unfold f0 c0
  simp [hx]

theorem dev0_Ac {x : CC} (hx : x ∉ A) : (⨆ a, |f0 a x - c0 a|) = 1/2 := by
  refine le_antisymm (ciSup_le ?_) (le_ciSup_of_le (bddDev0 x) x ?_)
  · intro a
    unfold f0 c0
    by_cases ha : a ∈ A
    · have : x ≠ a := fun h => hx (h ▸ ha)
      simp [ha, this]
    · simp only [ha, ↓reduceIte]
      split_ifs <;> norm_num
  · unfold f0 c0
    simp [hx]

theorem dev0_eq_M (x : CC) : (⨆ a, |f0 a x - c0 a|) = (⨆ a, |f0 a x|) := by
  by_cases hx : x ∈ A
  · rw [dev0_A hx, M_A hx]
  · rw [dev0_Ac hx, M_Ac hx]

theorem dev_eq (ω : Ω0) :
    empProcessDeviation f0 Xs X00 P0 1 ω = ⨆ a, |f0 a ω.1.1| := by
  unfold empProcessDeviation Xs Z0
  simp only [int_eq, Finset.sum_range_one, Nat.cast_one, div_one, one_mul]
  exact dev0_eq_M ω.1.1

theorem dev_not_aesm :
    ¬ AEStronglyMeasurable (empProcessDeviation f0 Xs X00 P0 1) P0 := by
  have heq : empProcessDeviation f0 Xs X00 P0 1 = fun ω : Ω0 => ⨆ a, |f0 a ω.1.1| :=
    funext dev_eq
  rw [heq]
  intro h
  have h1 : AEStronglyMeasurable (fun y : CC × ℝ => ⨆ a, |f0 a y.1|) (ccM.prod rad) := by
    obtain ⟨q, hq⟩ := (section_fst (μ := ν) (μ' := Q)
      (g := fun ω : Ω0 => ⨆ a, |f0 a ω.1.1|) h).exists
    exact hq
  obtain ⟨e, he, -⟩ := ((section_fst h1).and rad_ae).exists
  apply M_not_aesm
  exact he

theorem int_dev_zero :
    ∫ ω', empProcessDeviation f0 Xs X00 P0 1 ω' ∂P0 = 0 :=
  integral_non_aestronglyMeasurable dev_not_aesm

theorem dev_ge (ω : Ω0) : (1:ℝ)/2 ≤ empProcessDeviation f0
    Xs X00 P0 1 ω := by
  rw [dev_eq]
  by_cases hx : ω.1.1 ∈ A
  · rw [M_A hx]; norm_num
  · rw [M_Ac hx]

end Cex9bcc

open MeasureTheory ProbabilityTheory HighDimStat.UniformLaws in
theorem solution : ¬ (∀ {D ι Ω : Type} [MeasurableSpace D] [MeasurableSpace Ω]
    {Prob : Measure Ω} [IsProbabilityMeasure Prob] (f : ι → D → ℝ) (hf : ∀ j, Measurable (f j))
    (b : ℝ) (hb : IsUniformlyBounded f b)
    (Xs : ℕ → Ω → D) (X0 : Ω → D) (hIndep : iIndepFun Xs Prob)
    (hIdent : ∀ i, IdentDistrib (Xs i) X0 Prob Prob) (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht : 0 ≤ t),
    Prob.real {ω | empProcessDeviation f Xs X0 Prob n ω -
      ∫ ω', empProcessDeviation f Xs X0 Prob n ω' ∂Prob ≤ t} ≥
      1 - Real.exp (-((n : ℝ) * t ^ 2) / (2 * b ^ 2))) := by
  intro h
  have key := h (Prob := Cex9bcc.P0) Cex9bcc.f0 Cex9bcc.f0_meas 1
    (fun j x => Cex9bcc.f0_bound j x) Cex9bcc.Xs Cex9bcc.X00 Cex9bcc.hIndep Cex9bcc.hIdent
    1 le_rfl (1/4) (by norm_num)
  rw [Cex9bcc.int_dev_zero] at key
  have hE : {ω | empProcessDeviation Cex9bcc.f0 Cex9bcc.Xs Cex9bcc.X00 Cex9bcc.P0 1 ω - 0 ≤ 1/4} =
      (∅ : Set Cex9bcc.Ω0) := by
    ext ω
    simp only [sub_zero, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
    linarith [Cex9bcc.dev_ge ω]
  rw [hE, measureReal_empty] at key
  have : Real.exp (-(((1:ℕ):ℝ) * (1/4:ℝ) ^ 2) / (2 * (1:ℝ) ^ 2)) < 1 :=
    Real.exp_lt_one_iff.mpr (by norm_num)
  linarith
