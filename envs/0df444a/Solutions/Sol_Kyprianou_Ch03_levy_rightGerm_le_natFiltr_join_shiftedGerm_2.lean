-- Prove2me | solution 2 for Kyprianou.Ch03.levy_rightGerm_le_natFiltr_join_shiftedGerm
-- status  : ACCEPTED   (disprove)
-- author  : @ytako6706
-- created : 2026-11-24T06:40:10.318563+00:00
-- url     : https://prove2.me/submissions/bcebf9f8-2afe-4daa-afcf-f88e1eef76bb

import Mathlib
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
import Definitions.Def_DurrettProbability_Brownian
open MeasureTheory ProbabilityTheory DurrettProbability Set
open scoped NNReal ENNReal
set_option autoImplicit false

namespace PiSystemJoinGermCounterexample

/-- Coin-tossing space. -/
abbrev Ω := ℕ → Bool

/-- the fair coin -/
noncomputable def ν : Measure Bool := (2⁻¹ : ℝ≥0∞) • (Measure.dirac true + Measure.dirac false)

instance : IsProbabilityMeasure ν := by
  constructor
  simp only [ν, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
  rw [one_add_one_eq_two, ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]

theorem ν_map_not : ν.map Bool.not = ν := by
  simp only [ν, Measure.map_smul, Measure.map_add _ _ (measurable_of_finite _),
    Measure.map_dirac' (measurable_of_finite Bool.not)]
  simp only [Bool.not_true, Bool.not_false]
  rw [add_comm]

/-- the product of fair coins -/
noncomputable def μ : Measure Ω := Measure.infinitePi (fun _ : ℕ => ν)

instance : IsProbabilityMeasure μ := by unfold μ; infer_instance

/-- flipping all coins -/
def Φ (ω : Ω) : Ω := fun i => !(ω i)

theorem measurable_Φ : Measurable Φ := measurable_pi_lambda _ fun i =>
  (measurable_of_finite Bool.not).comp (measurable_pi_apply i)

theorem μ_map_Φ : μ.map Φ = μ := by
  have := Measure.infinitePi_map_pi (μ := fun _ : ℕ => ν) (f := fun _ => Bool.not)
    (fun _ => measurable_of_finite _)
  simp only [ν_map_not] at this
  exact this

theorem μ_preimage_Φ {S : Set Ω} (hS : MeasurableSet S) : μ (Φ ⁻¹' S) = μ S := by
  conv_rhs => rw [← μ_map_Φ]
  rw [Measure.map_apply measurable_Φ hS]

theorem measurable_xor {m : MeasurableSpace Ω} {a b : Ω → Bool}
    (ha : Measurable[m] a) (hb : Measurable[m] b) : Measurable[m] (fun ω => xor (a ω) (b ω)) := by
  apply measurable_to_bool
  have : (fun ω => xor (a ω) (b ω)) ⁻¹' {true} =
      (a ⁻¹' {true} ∩ (b ⁻¹' {true})ᶜ) ∪ ((a ⁻¹' {true})ᶜ ∩ b ⁻¹' {true}) := by
    ext ω; cases h1 : a ω <;> cases h2 : b ω <;> simp [h1, h2]
  rw [this]
  have h1 := ha (measurableSet_singleton true)
  have h2 := hb (measurableSet_singleton true)
  exact (h1.inter h2.compl).union (h1.compl.inter h2)

/-- neighbouring xors -/
def D (j : ℕ) (ω : Ω) : Bool := xor (ω j) (ω (j + 1))

/-- the σ-algebra of the neighbouring xors -/
def G : MeasurableSpace Ω := ⨆ j, MeasurableSpace.comap (D j) inferInstance

/-- the process: `Y u` reveals the coin `⌈1/u⌉` for `u > 0` -/
noncomputable def Y (u : ℝ≥0) (ω : Ω) : ℝ :=
  if u = 0 then 0 else if ω ⌈(u : ℝ)⁻¹⌉₊ then 1 else 0

/-- parity of the first `k` xors -/
def par : ℕ → Ω → Bool
  | 0 => fun _ => false
  | k + 1 => fun ω => xor (par k ω) (D k ω)

theorem first_eq (ω : Ω) (k : ℕ) : ω 0 = xor (ω k) (par k ω) := by
  induction k with
  | zero => simp [par]
  | succ k ih =>
    rw [ih]
    simp only [par, D]
    cases ω k <;> cases ω (k + 1) <;> cases par k ω <;> rfl

theorem measurable_D (j : ℕ) : Measurable[G] (D j) :=
  (comap_measurable (D j)).mono
    (le_iSup (fun j => MeasurableSpace.comap (D j) (inferInstance : MeasurableSpace Bool)) j)
    le_rfl

theorem measurable_par (k : ℕ) : Measurable[G] (par k) := by
  induction k with
  | zero => exact @measurable_const _ _ _ G _
  | succ k ih => exact measurable_xor ih (measurable_D k)

theorem G_le : G ≤ MeasurableSpace.pi :=
  iSup_le fun j => (measurable_xor (measurable_pi_apply j) (measurable_pi_apply (j + 1))).comap_le

/-- `Φ` fixes every `G`-set -/
theorem Φ_preimage_of_G {A : Set Ω} (hA : MeasurableSet[G] A) : Φ ⁻¹' A = A := by
  let I : MeasurableSpace Ω :=
    { MeasurableSet' := fun S => Φ ⁻¹' S = S
      measurableSet_empty := rfl
      measurableSet_compl := fun S hS => by
        change Φ ⁻¹' Sᶜ = Sᶜ
        rw [Set.preimage_compl, hS]
      measurableSet_iUnion := fun f hf => by
        change Φ ⁻¹' (⋃ i, f i) = ⋃ i, f i
        rw [Set.preimage_iUnion]
        exact congrArg Set.iUnion (funext hf) }
  have hGI : G ≤ I := by
    refine iSup_le fun j => ?_
    rintro S ⟨T, _, rfl⟩
    change Φ ⁻¹' (D j ⁻¹' T) = D j ⁻¹' T
    rw [← Set.preimage_comp]
    congr 1
    funext ω
    simp only [Function.comp, D, Φ]
    cases ω j <;> cases ω (j + 1) <;> rfl
  exact hGI A hA

/-- the coordinate σ-algebras -/
def s (n : ℕ) : MeasurableSpace Ω := MeasurableSpace.comap (fun ω : Ω => ω n) inferInstance

theorem iIndep_s : iIndep s μ := by
  have h : iIndepFun (fun n (ω : Ω) => ω n) μ := by
    rw [iIndepFun_iff_map_fun_eq_infinitePi_map₀ (by fun_prop)]
    have hid : (fun (ω : Ω) (i : ℕ) => ω i) = id := rfl
    rw [hid, Measure.map_id]
    have hev : ∀ i, μ.map (fun ω : Ω => ω i) = ν := fun i =>
      (measurePreserving_eval_infinitePi (fun _ : ℕ => ν) i).map_eq
    simp only [hev]
    rfl
  exact (iIndepFun_iff_iIndep _ _ μ).mp h

theorem germ_le_limsup : germSigma Y ≤ Filter.limsup s Filter.atTop := by
  rw [Filter.limsup_eq_iInf_iSup_of_nat]
  refine le_iInf fun n => ?_
  have hpos : (0 : ℝ≥0) < 1 / ((n : ℝ≥0) + 1) := by positivity
  refine (iInf₂_le (1 / ((n : ℝ≥0) + 1)) hpos).trans ?_
  refine iSup₂_le fun u hu => ?_
  by_cases hu0 : u = 0
  · have : Y u = fun _ => 0 := by funext ω; simp [Y, hu0]
    rw [this, MeasurableSpace.comap_const]
    exact bot_le
  · have hk : n ≤ ⌈(u : ℝ)⁻¹⌉₊ := by
      have hu' : (u : ℝ) ≤ 1 / ((n : ℝ) + 1) := by exact_mod_cast (Set.mem_Iic.mp hu)
      have hupos : (0 : ℝ) < u := by
        exact_mod_cast (pos_iff_ne_zero.mpr hu0)
      have : (n : ℝ) + 1 ≤ (u : ℝ)⁻¹ := by
        rw [le_inv_comm₀ (by positivity) hupos]
        simpa using hu'
      have h2 := this.trans (Nat.le_ceil _)
      exact_mod_cast (by linarith : (n : ℝ) ≤ ⌈(u : ℝ)⁻¹⌉₊)
    refine le_trans ?_ (le_iSup₂ (f := fun i (_ : i ≥ n) => s i) _ hk)
    have hm : Measurable[s ⌈(u : ℝ)⁻¹⌉₊] (Y u) := by
      have : Y u = (fun b : Bool => if b then (1 : ℝ) else 0) ∘ (fun ω : Ω => ω ⌈(u : ℝ)⁻¹⌉₊) := by
        funext ω; simp [Y, hu0]
      rw [this]
      exact (measurable_of_finite _).comp (comap_measurable _)
    exact hm.comap_le

theorem germ_le_pi : germSigma Y ≤ MeasurableSpace.pi := by
  refine germ_le_limsup.trans ?_
  rw [Filter.limsup_eq_iInf_iSup_of_nat]
  refine (iInf_le _ 0).trans (iSup₂_le fun i _ => (measurable_pi_apply i).comap_le)

/-- `E` lies in every `G ⊔ pastSigma Y ε` -/
theorem E_mem (ε : ℝ≥0) (hε : 0 < ε) :
    MeasurableSet[G ⊔ pastSigma Y ε] {ω : Ω | ω 0 = true} := by
  set k := ⌈(ε : ℝ)⁻¹⌉₊
  have hY : Measurable[pastSigma Y ε] (Y ε) :=
    (comap_measurable (Y ε)).mono
      (le_iSup₂ (f := fun u (_ : u ∈ Set.Iic ε) =>
        MeasurableSpace.comap (Y u) (inferInstance : MeasurableSpace ℝ)) ε (Set.mem_Iic.mpr le_rfl)) le_rfl
  have hk : Measurable[pastSigma Y ε] (fun ω : Ω => ω k) := by
    have : (fun ω : Ω => ω k) = (fun r : ℝ => decide (r = 1)) ∘ Y ε := by
      funext ω
      simp only [Function.comp, Y, hε.ne', if_false]
      cases ω k <;> simp
    rw [this]
    have hdec : Measurable (fun r : ℝ => decide (r = 1)) := by
      apply measurable_to_bool
      have : (fun r : ℝ => decide (r = 1)) ⁻¹' {true} = {1} := by ext r; simp
      rw [this]; exact measurableSet_singleton 1
    exact hdec.comp hY
  have h0 : Measurable[G ⊔ pastSigma Y ε] (fun ω : Ω => ω 0) := by
    have : (fun ω : Ω => ω 0) = fun ω => xor (ω k) (par k ω) := funext fun ω => first_eq ω k
    rw [this]
    exact measurable_xor (hk.mono le_sup_right le_rfl) ((measurable_par k).mono le_sup_left le_rfl)
  exact h0 (measurableSet_singleton true)

/-- sets of `G ⊔ germ` are `G`-sets up to `μ`-null sets -/
@[instance_reducible]
def approx : MeasurableSpace Ω where
  MeasurableSet' S := MeasurableSet S ∧ ∃ A, MeasurableSet[G] A ∧ μ (symmDiff S A) = 0
  measurableSet_empty := ⟨MeasurableSet.empty, ∅, @MeasurableSet.empty _ G, by simp⟩
  measurableSet_compl S := by
    rintro ⟨hS, A, hA, h0⟩
    exact ⟨hS.compl, Aᶜ, hA.compl, by rwa [compl_symmDiff_compl]⟩
  measurableSet_iUnion f := by
    intro h
    choose hf A hA h0 using h
    refine ⟨MeasurableSet.iUnion hf, ⋃ i, A i, MeasurableSet.iUnion hA, ?_⟩
    refine measure_mono_null ?_ (measure_iUnion_null h0)
    intro x hx
    simp only [Set.mem_symmDiff, Set.mem_iUnion, not_exists] at hx ⊢
    rcases hx with ⟨⟨i, hi⟩, hn⟩ | ⟨⟨i, hi⟩, hn⟩
    · exact ⟨i, Or.inl ⟨hi, hn i⟩⟩
    · exact ⟨i, Or.inr ⟨hi, hn i⟩⟩

theorem le_approx : G ⊔ germSigma Y ≤ approx := by
  refine sup_le ?_ ?_
  · intro A hA
    exact ⟨G_le A hA, A, hA, by simp⟩
  · intro T hT
    have hTm : MeasurableSet T := germ_le_pi T hT
    rcases measure_zero_or_one_of_measurableSet_limsup_atTop
        (fun n => (measurable_pi_apply n).comap_le) iIndep_s (germ_le_limsup T hT) with h | h
    · exact ⟨hTm, ∅, @MeasurableSet.empty _ G, by simpa using h⟩
    · refine ⟨hTm, Set.univ, @MeasurableSet.univ _ G, ?_⟩
      have : symmDiff T Set.univ = Tᶜ := by ext; simp [Set.mem_symmDiff]
      rw [this, prob_compl_eq_zero_iff hTm]
      exact h

theorem not_mem : ¬ MeasurableSet[G ⊔ germSigma Y] {ω : Ω | ω 0 = true} := by
  intro hE
  obtain ⟨hEm, A, hA, h0⟩ := le_approx _ hE
  set E := {ω : Ω | ω 0 = true}
  have hAm : MeasurableSet A := G_le A hA
  have hΦE : Φ ⁻¹' E = Eᶜ := by
    ext ω; simp [E, Φ]
  -- flip symmetry
  have hsym : μ (E ∩ A) = μ (Eᶜ ∩ A) := by
    rw [← μ_preimage_Φ (hEm.inter hAm), Set.preimage_inter, hΦE, Φ_preimage_of_G hA]
  have h1 : μ (E \ A) = 0 := measure_mono_null (fun x hx => Or.inl hx) h0
  have h2 : μ (A \ E) = 0 := measure_mono_null (fun x hx => Or.inr hx) h0
  have h3 : μ (Eᶜ ∩ A) = 0 := by
    rw [Set.inter_comm, ← Set.diff_eq]; exact h2
  have hE0 : μ E = 0 := by
    have := measure_inter_add_diff E hAm (μ := μ)
    rw [hsym, h3, h1, add_zero] at this
    exact this.symm
  have hEc0 : μ Eᶜ = 0 := by
    rw [← hΦE, μ_preimage_Φ hEm, hE0]
  have : μ (E ∪ Eᶜ) = 0 := measure_union_null hE0 hEc0
  rw [Set.union_compl_self, measure_univ] at this
  exact one_ne_zero this


theorem measurable_par' {m : MeasurableSpace Ω} (hD : ∀ j, Measurable[m] (D j)) (k : ℕ) :
    Measurable[m] (par k) := by
  induction k with
  | zero => exact @measurable_const _ _ _ m _
  | succ k ih => exact measurable_xor ih (hD k)

/-- the process for the Lévy-germ statement -/
noncomputable def XX (u : ℝ≥0) (ω : Ω) : ℝ :=
  if u ≤ 1 then
    (if 0 < u ∧ u ≤ 1 / 2 then (if D (⌈(u : ℝ)⁻¹⌉₊ - 2) ω then 1 else 0) else 0)
  else (if ω ⌈((u : ℝ) - 1)⁻¹⌉₊ then 1 else 0)

theorem XX_one (ω : Ω) : XX 1 ω = 0 := by
  have : ¬ ((1 : ℝ≥0) ≤ 1 / 2) := by
    rw [not_le]; rw [← NNReal.coe_lt_coe]; push_cast; norm_num
  simp [XX, this]

theorem shifted_eq : (fun u : ℝ≥0 => fun ω : Ω => XX (1 + u) ω - XX 1 ω) = Y := by
  funext u ω
  rw [XX_one, sub_zero]
  by_cases hu : u = 0
  · subst hu
    simp only [add_zero, XX_one, Y, if_true]
  · have h1 : ¬ (1 + u ≤ 1) := by
      rw [not_le]; exact lt_add_of_pos_right _ (pos_iff_ne_zero.mpr hu)
    have h2 : ((((1 + u : ℝ≥0)) : ℝ) - 1) = (u : ℝ) := by push_cast; ring
    simp only [XX, h1, if_false, h2, Y, hu]

theorem XX_uj (j : ℕ) (ω : Ω) :
    XX (1 / ((j : ℝ≥0) + 2)) ω = if D j ω then 1 else 0 := by
  have hpos : (0 : ℝ≥0) < 1 / ((j : ℝ≥0) + 2) := by positivity
  have hle2 : 1 / ((j : ℝ≥0) + 2) ≤ 1 / 2 := by
    gcongr
    rw [← NNReal.coe_le_coe]; push_cast; linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]
  have hle1 : 1 / ((j : ℝ≥0) + 2) ≤ 1 := hle2.trans (by
    rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  have hceil : ⌈(((1 / ((j : ℝ≥0) + 2) : ℝ≥0)) : ℝ)⁻¹⌉₊ - 2 = j := by
    have : ((((1 / ((j : ℝ≥0) + 2) : ℝ≥0)) : ℝ))⁻¹ = ((j + 2 : ℕ) : ℝ) := by
      push_cast; rw [one_div, inv_inv]
    rw [this, Nat.ceil_natCast]; omega
  simp only [XX, hle1, hpos, hle2, and_self, if_true, hceil]

theorem natFiltr_one_le : PerfCorrMSQ.natFiltr XX 1 ≤ G := by
  refine iSup₂_le fun u hu => ?_
  refine Measurable.comap_le ?_
  have hm : Measurable[G] (XX u) := by
    unfold XX
    simp only [hu, if_true]
    split_ifs
    · exact (measurable_of_finite (fun b : Bool => if b then (1 : ℝ) else 0)).comp
        (measurable_D _)
    · exact @measurable_const _ _ _ G _
  exact hm

theorem E_mem_natFiltr (s : ℝ≥0) (hs : 1 < s) :
    MeasurableSet[PerfCorrMSQ.natFiltr XX s] {ω : Ω | ω 0 = true} := by
  have hX : ∀ u, u ≤ s → Measurable[PerfCorrMSQ.natFiltr XX s] (XX u) := fun u hu =>
    (comap_measurable (XX u)).mono
      (le_iSup₂ (f := fun v (_ : v ≤ s) =>
        MeasurableSpace.comap (XX v) (inferInstance : MeasurableSpace ℝ)) u hu) le_rfl
  have hdec : Measurable (fun r : ℝ => decide (r = 1)) := by
    apply measurable_to_bool
    have : (fun r : ℝ => decide (r = 1)) ⁻¹' {true} = {1} := by ext r; simp
    rw [this]; exact measurableSet_singleton 1
  have hD : ∀ j, Measurable[PerfCorrMSQ.natFiltr XX s] (D j) := by
    intro j
    have hle : 1 / ((j : ℝ≥0) + 2) ≤ s := by
      refine le_trans ?_ hs.le
      rw [div_le_one (by positivity), ← NNReal.coe_le_coe]
      push_cast; linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]
    have : D j = (fun r : ℝ => decide (r = 1)) ∘ XX (1 / ((j : ℝ≥0) + 2)) := by
      funext ω; simp only [Function.comp, XX_uj]; cases D j ω <;> simp
    rw [this]; exact hdec.comp (hX _ hle)
  set k := ⌈((s : ℝ) - 1)⁻¹⌉₊
  have hk : Measurable[PerfCorrMSQ.natFiltr XX s] (fun ω : Ω => ω k) := by
    have hns : ¬ (s ≤ 1) := not_le.mpr hs
    have : (fun ω : Ω => ω k) = (fun r : ℝ => decide (r = 1)) ∘ XX s := by
      funext ω; simp only [Function.comp, XX, hns, if_false]; cases ω k <;> simp
    rw [this]; exact hdec.comp (hX s le_rfl)
  have h0 : Measurable[PerfCorrMSQ.natFiltr XX s] (fun ω : Ω => ω 0) := by
    have : (fun ω : Ω => ω 0) = fun ω => xor (ω k) (par k ω) := funext fun ω => first_eq ω k
    rw [this]
    exact measurable_xor hk (measurable_par' hD k)
  exact h0 (measurableSet_singleton true)

end PiSystemJoinGermCounterexample

open PiSystemJoinGermCounterexample in
theorem solution :
    ¬ (∀ {Omega : Type} [MeasurableSpace Omega]
        (X : NNReal -> Omega -> Real)
        (t : NNReal),
        (⨅ s : NNReal, ⨅ (_ : t < s), PerfCorrMSQ.natFiltr X s) ≤
          PerfCorrMSQ.natFiltr X t ⊔
            germSigma (fun u : NNReal => fun omega : Omega => X (t + u) omega - X t omega)) := by
  intro h
  have hle := h (Omega := Ω) XX 1
  rw [shifted_eq] at hle
  apply not_mem
  refine sup_le_sup_right natFiltr_one_le _ _ (hle _ ?_)
  refine MeasurableSpace.measurableSet_iInf.mpr fun s => ?_
  refine MeasurableSpace.measurableSet_iInf.mpr fun hs => ?_
  exact E_mem_natFiltr s hs
