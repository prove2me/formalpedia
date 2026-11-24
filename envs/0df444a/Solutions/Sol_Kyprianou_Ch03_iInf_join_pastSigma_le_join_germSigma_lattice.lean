-- Prove2me | solution 1 for Kyprianou.Ch03.iInf_join_pastSigma_le_join_germSigma_lattice
-- status  : ACCEPTED   (disprove)
-- author  : @pageman
-- created : 2026-11-24T10:54:01.713684+00:00
-- url     : https://prove2.me/submissions/551fb507-b86b-4fb8-8719-fed65e29d9d4

import Mathlib
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

end PiSystemJoinGermCounterexample

open PiSystemJoinGermCounterexample in
theorem solution :
    ¬ (∀ {Omega : Type} [MeasurableSpace Omega]
        (G : MeasurableSpace Omega)
        (Y : NNReal → Omega → Real),
        (⨅ ε : NNReal, ⨅ (_ : 0 < ε), G ⊔ pastSigma Y ε) ≤ G ⊔ germSigma Y) := by
  intro h
  have hle := h (Omega := Ω) PiSystemJoinGermCounterexample.G PiSystemJoinGermCounterexample.Y
  apply not_mem
  refine hle _ ?_
  refine MeasurableSpace.measurableSet_iInf.mpr fun ε => ?_
  refine MeasurableSpace.measurableSet_iInf.mpr fun hε => ?_
  exact E_mem ε hε
