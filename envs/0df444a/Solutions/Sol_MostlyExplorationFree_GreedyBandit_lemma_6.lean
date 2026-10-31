-- Prove2me | solution 1 for MostlyExplorationFree.GreedyBandit.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T19:26:00.452348+00:00
-- url     : https://prove2.me/submissions/030d01d0-0f74-49ea-9f42-e39bf932d165

import Mathlib
import Definitions.Def_MostlyExplorationFree_GreedyBandit_Model
import Theorems.Thm_MostlyExplorationFree_GreedyBandit_lemma_5

open Matrix MeasureTheory ProbabilityTheory

namespace MEFLemma6Aux
open MostlyExplorationFree.GreedyBandit

theorem armSeq_eq {d : ℕ} (β : Fin 2 → Fin d → ℝ) (x : ℕ → Fin d → ℝ)
    (e : Fin 2 → ℕ → ℝ) (w : ℕ → Bool) (t : ℕ) :
    armSeq β x e w t = greedyChoice (x t)
      (estOf β x e (fun s => if s < t then armSeq β x e w s else 0) 0 (t - 1))
      (estOf β x e (fun s => if s < t then armSeq β x e w s else 0) 1 (t - 1)) (w t) := by
  rw [armSeq, Nat.strongRec]
  simp only [dite_eq_ite]
  rfl

theorem continuous_lambdaMin {d : ℕ} :
    Continuous (fun M : Matrix (Fin d) (Fin d) ℝ => lambdaMin M) := by
  have hS : IsCompact {v : Fin d → ℝ | v ⬝ᵥ v = 1} := by
    apply IsCompact.of_isClosed_subset
      (isCompact_univ_pi (fun _ : Fin d => isCompact_Icc (a := (-1:ℝ)) (b := 1)))
    · exact isClosed_eq (continuous_id.dotProduct continuous_id) continuous_const
    · intro v hv
      simp only [Set.mem_ofPred_eq] at hv
      simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies]
      intro i
      have h1 : v i ^ 2 ≤ v ⬝ᵥ v := by
        simp only [dotProduct]
        have := Finset.single_le_sum (f := fun j => v j * v j)
          (fun j _ => mul_self_nonneg (v j)) (Finset.mem_univ i)
        nlinarith [this]
      rw [hv] at h1
      have := (sq_le_one_iff_abs_le_one (v i)).mp h1
      exact abs_le.mp this
  have := hS.continuous_sInf
    (f := fun (M : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) => v ⬝ᵥ (M *ᵥ v))
    (continuous_snd.dotProduct (continuous_fst.matrix_mulVec continuous_snd))
  convert this using 2 with M
  rw [sInf_image']
  rfl

theorem meas_of_matrix_cont {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {Y : Type*}
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (F : Matrix (Fin d) (Fin d) ℝ → Y) (hF : Continuous F) (G : Ω → Matrix (Fin d) (Fin d) ℝ)
    (hG : ∀ p q, Measurable fun ω => G ω p q) : Measurable fun ω => F (G ω) := by
  have h1 : Measurable (fun ω => (fun p q => G ω p q : Fin d → Fin d → ℝ)) :=
    measurable_pi_lambda _ (fun p => measurable_pi_lambda _ (fun q => hG p q))
  have h2 : Continuous (fun f : Fin d → Fin d → ℝ => F f) := hF
  exact h2.measurable.comp h1


theorem condExp_indep_comp {Ω β γ : Type*} {m mΩ : MeasurableSpace Ω}
    (hm : m ≤ mΩ) (P : Measure Ω) [IsProbabilityMeasure P]
    [MeasurableSpace β] [MeasurableSpace γ] (B : Ω → β) (hB : Measurable[m] B)
    (Z : Ω → γ) (hZ : Measurable Z) (hind : Indep m (MeasurableSpace.comap Z inferInstance) P)
    (φ : β × γ → ℝ) (hφ : Measurable φ) (C : ℝ) (hC : ∀ p, |φ p| ≤ C) :
    condExp m P (fun ω => φ (B ω, Z ω)) =ᵐ[P] fun ω => ∫ ω', φ (B ω, Z ω') ∂P := by
  have hB' : Measurable B := hB.mono hm le_rfl
  set ν := P.map Z with hν
  have : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hZ.aemeasurable
  set ψ : β → ℝ := fun b => ∫ z, φ (b, z) ∂ν with hψ
  have hψm : StronglyMeasurable ψ := hφ.stronglyMeasurable.integral_prod_right'
  have hψeq : ∀ b, ∫ ω', φ (b, Z ω') ∂P = ψ b := by
    intro b
    show _ = ∫ z, φ (b, z) ∂(P.map Z)
    rw [integral_map hZ.aemeasurable]
    exact (hφ.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hψC : ∀ b, |ψ b| ≤ C := by
    intro b
    have := norm_integral_le_of_norm_le_const (μ := ν) (f := fun z => φ (b, z)) (C := C)
      (Filter.Eventually.of_forall (fun z => by rw [Real.norm_eq_abs]; exact hC _))
    simpa [Real.norm_eq_abs] using this
  have hfun : (fun ω => ∫ ω', φ (B ω, Z ω') ∂P) = fun ω => ψ (B ω) := funext fun ω => hψeq _
  rw [hfun]
  have hf : Integrable (fun ω => φ (B ω, Z ω)) P :=
    Integrable.of_bound (hφ.comp (hB'.prodMk hZ)).aestronglyMeasurable C
      (Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs]; exact hC _))
  have hg : Integrable (fun ω => ψ (B ω)) P :=
    Integrable.of_bound (hψm.measurable.comp hB').aestronglyMeasurable C
      (Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs]; exact hψC _))
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm hf (fun s _ _ => hg.integrableOn) ?_
    (hψm.comp_measurable hB).aestronglyMeasurable).symm
  intro s hs _
  classical
  -- encode s by a Bool-valued m-measurable variable
  set V : Ω → β × Bool := fun ω => (B ω, if ω ∈ s then true else false) with hV
  have hVm : Measurable[m] V :=
    hB.prodMk (Measurable.ite hs measurable_const measurable_const)
  have hVm' : Measurable V := hVm.mono hm le_rfl
  have hVZ : IndepFun V Z P := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_left hind (measurable_iff_comap_le.mp hVm)
  have hmap : P.map (fun ω => (V ω, Z ω)) = (P.map V).prod ν :=
    (indepFun_iff_map_prod_eq_prod_map_map hVm'.aemeasurable hZ.aemeasurable).mp hVZ
  set h : (β × Bool) × γ → ℝ := fun p => if p.1.2 then φ (p.1.1, p.2) else 0 with hh
  have hhm : Measurable h := by
    refine Measurable.ite ?_ (hφ.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
      measurable_const
    exact (measurable_snd.comp measurable_fst) (measurableSet_singleton true)
  have hhC : ∀ p, |h p| ≤ C := by
    intro p
    have : 0 ≤ C := (abs_nonneg _).trans (hC (p.1.1, p.2))
    simp only [hh]; split_ifs
    · exact hC _
    · simpa using this
  have : IsProbabilityMeasure (P.map V) := Measure.isProbabilityMeasure_map hVm'.aemeasurable
  have hhint : Integrable h ((P.map V).prod ν) :=
    Integrable.of_bound hhm.aestronglyMeasurable C
      (Filter.Eventually.of_forall (fun p => by rw [Real.norm_eq_abs]; exact hhC _))
  -- RHS
  have hR : ∫ ω in s, φ (B ω, Z ω) ∂P = ∫ ω, h (V ω, Z ω) ∂P := by
    rw [← integral_indicator (hm _ hs)]
    congr 1; funext ω
    by_cases hω : ω ∈ s <;> simp [hω, hh, hV]
  have hL : ∫ ω in s, ψ (B ω) ∂P = ∫ ω, (if (V ω).2 then ψ (V ω).1 else 0) ∂P := by
    rw [← integral_indicator (hm _ hs)]
    congr 1; funext ω
    by_cases hω : ω ∈ s <;> simp [hω, hV]
  rw [hR, hL]
  rw [← integral_map (f := h) (hVm'.prodMk hZ).aemeasurable hhm.aestronglyMeasurable, hmap,
    integral_prod h hhint]
  have hk : Measurable fun v : β × Bool => (if v.2 then ψ v.1 else 0) :=
    Measurable.ite (measurable_snd (measurableSet_singleton true))
      (hψm.measurable.comp measurable_fst) measurable_const
  rw [← integral_map (f := fun v : β × Bool => (if v.2 then ψ v.1 else 0)) hVm'.aemeasurable
    hk.aestronglyMeasurable]
  congr 1; funext v
  rcases v with ⟨b, c⟩
  cases c <;> simp [hh, hψ]


theorem estOf_congr {d : ℕ} (β : Fin 2 → Fin d → ℝ) (x : ℕ → Fin d → ℝ) (e : Fin 2 → ℕ → ℝ)
    (a a' : ℕ → Fin 2) (i : Fin 2) (t : ℕ) (h : ∀ s ∈ Finset.Icc 1 t, a s = a' s) :
    estOf β x e a i t = estOf β x e a' i t := by
  have hp : playedOf a i t = playedOf a' i t := by
    unfold playedOf
    exact Finset.filter_congr (fun s hs => by rw [h s hs])
  have hg : gramOf x a i t = gramOf x a' i t := by unfold gramOf; rw [hp]
  have hsum : ∑ s ∈ playedOf a' i t, rewardOf β x e a s • x s
      = ∑ s ∈ playedOf a' i t, rewardOf β x e a' s • x s :=
    Finset.sum_congr rfl (fun s hs => by
      simp only [rewardOf, h s (Finset.mem_filter.mp hs).1])
  unfold estOf
  rw [hg, hp, hsum]

section Meas
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {d : ℕ}

theorem measurable_gramOf_entry' (X : ℕ → Ω → Fin d → ℝ) (a : Ω → ℕ → Fin 2) (i : Fin 2)
    (t : ℕ) (hX : ∀ s ∈ Finset.Icc 1 t, Measurable (X s))
    (ha : ∀ s ∈ Finset.Icc 1 t, Measurable fun ω => a ω s) (p q : Fin d) :
    Measurable fun ω => gramOf (fun s => X s ω) (a ω) i t p q := by
  have : (fun ω => gramOf (fun s => X s ω) (a ω) i t p q) =
      fun ω => ∑ s ∈ Finset.Icc 1 t, if a ω s = i then X s ω p * X s ω q else 0 := by
    funext ω
    simp [gramOf, playedOf, Finset.sum_filter, Matrix.sum_apply, Matrix.vecMulVec_apply]
  rw [this]
  refine Finset.measurable_sum _ (fun s hs => ?_)
  exact Measurable.ite ((ha s hs) (measurableSet_singleton i))
    ((((measurable_pi_apply p).comp (hX s hs))).mul ((measurable_pi_apply q).comp (hX s hs)))
    measurable_const

theorem measurable_estOf' (β : Fin 2 → Fin d → ℝ) (X : ℕ → Ω → Fin d → ℝ)
    (ε : Fin 2 → ℕ → Ω → ℝ) (a : Ω → ℕ → Fin 2) (i : Fin 2) (t : ℕ)
    (hX : ∀ s ∈ Finset.Icc 1 t, Measurable (X s)) (hε : ∀ s ∈ Finset.Icc 1 t, Measurable (ε i s))
    (ha : ∀ s ∈ Finset.Icc 1 t, Measurable fun ω => a ω s) :
    Measurable fun ω => estOf β (fun s => X s ω) (fun j s => ε j s ω) (a ω) i t := by
  have hG := measurable_gramOf_entry' X a i t hX ha
  have hv : ∀ l, Measurable fun ω => (∑ s ∈ playedOf (a ω) i t,
      rewardOf β (fun s => X s ω) (fun j s => ε j s ω) (a ω) s • X s ω) l := by
    intro l
    have : (fun ω => (∑ s ∈ playedOf (a ω) i t,
        rewardOf β (fun s => X s ω) (fun j s => ε j s ω) (a ω) s • X s ω) l) =
        fun ω => ∑ s ∈ Finset.Icc 1 t,
          if a ω s = i then (X s ω ⬝ᵥ β i + ε i s ω) * X s ω l else 0 := by
      funext ω
      simp only [playedOf, Finset.sum_filter, Finset.sum_apply, rewardOf]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      split_ifs with h
      · simp [h]
      · simp
    rw [this]
    refine Finset.measurable_sum _ (fun s hs => ?_)
    have hXc : ∀ p, Measurable fun ω => X s ω p := fun p => (measurable_pi_apply p).comp (hX s hs)
    refine Measurable.ite ((ha s hs) (measurableSet_singleton i)) (Measurable.mul ?_ (hXc l))
      measurable_const
    refine Measurable.add ?_ (hε s hs)
    simp only [dotProduct]
    exact Finset.measurable_sum _ (fun k _ => (hXc k).mul measurable_const)
  have hdet : Measurable fun ω => (gramOf (fun s => X s ω) (a ω) i t).det :=
    meas_of_matrix_cont (fun M => M.det) (continuous_id.matrix_det) _ hG
  have hadj : ∀ k l, Measurable fun ω => (gramOf (fun s => X s ω) (a ω) i t).adjugate k l :=
    fun k l => meas_of_matrix_cont (fun M => M.adjugate k l)
      ((continuous_apply_apply k l).comp continuous_id.matrix_adjugate) _ hG
  unfold estOf
  refine Measurable.ite ?_ ?_ measurable_const
  · exact hdet (measurableSet_singleton 0).compl
  · refine measurable_pi_lambda _ (fun k => ?_)
    simp only [mulVec, dotProduct, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply,
      smul_eq_mul]
    exact Finset.measurable_sum _ (fun l _ => ((hdet.inv.mul (hadj k l)).mul (hv l)))

theorem measurable_greedyChoice (xt f0 f1 : Ω → Fin d → ℝ) (wt : Ω → Bool)
    (hx : Measurable xt) (h0 : Measurable f0) (h1 : Measurable f1) (hw : Measurable wt) :
    Measurable fun ω => greedyChoice (xt ω) (f0 ω) (f1 ω) (wt ω) := by
  have hdot : ∀ (f : Ω → Fin d → ℝ), Measurable f → Measurable fun ω => xt ω ⬝ᵥ f ω :=
    fun f hf => (continuous_fst.dotProduct continuous_snd).measurable.comp (hx.prodMk hf)
  unfold greedyChoice
  exact Measurable.ite (measurableSet_lt (hdot _ h1) (hdot _ h0)) measurable_const
    (Measurable.ite (measurableSet_lt (hdot _ h0) (hdot _ h1)) measurable_const
      (Measurable.ite (hw (measurableSet_singleton true)) measurable_const measurable_const))

theorem arm_eq_greedy (β : Fin 2 → Fin d → ℝ) (X : ℕ → Ω → Fin d → ℝ)
    (ε : Fin 2 → ℕ → Ω → ℝ) (W : ℕ → Ω → Bool) (t : ℕ) (ω : Ω) :
    arm β X ε W t ω = greedyChoice (X t ω)
      (estOf β (fun s => X s ω) (fun j s => ε j s ω)
        (fun s => if 1 ≤ s ∧ s < t then arm β X ε W s ω else 0) 0 (t - 1))
      (estOf β (fun s => X s ω) (fun j s => ε j s ω)
        (fun s => if 1 ≤ s ∧ s < t then arm β X ε W s ω else 0) 1 (t - 1)) (W t ω) := by
  unfold arm
  rw [armSeq_eq]
  have hc : ∀ j : Fin 2, estOf β (fun s => X s ω) (fun j s => ε j s ω)
      (fun s => if s < t then armSeq β (fun s => X s ω) (fun i s => ε i s ω)
        (fun s => W s ω) s else 0) j (t - 1)
      = estOf β (fun s => X s ω) (fun j s => ε j s ω)
      (fun s => if 1 ≤ s ∧ s < t then armSeq β (fun s => X s ω) (fun i s => ε i s ω)
        (fun s => W s ω) s else 0) j (t - 1) := by
    intro j
    refine estOf_congr _ _ _ _ _ _ _ (fun s hs => ?_)
    rw [Finset.mem_Icc] at hs
    have h1 : s < t := by omega
    simp [h1, hs.1]
  rw [hc 0, hc 1]

theorem measurable_arm_le (β : Fin 2 → Fin d → ℝ) (X : ℕ → Ω → Fin d → ℝ)
    (ε : Fin 2 → ℕ → Ω → ℝ) (W : ℕ → Ω → Bool) (N : ℕ)
    (hX : ∀ s ∈ Finset.Icc 1 N, Measurable (X s)) (hW : ∀ s ∈ Finset.Icc 1 N, Measurable (W s))
    (hε : ∀ j, ∀ s ∈ Finset.Icc 1 (N - 1), Measurable (ε j s)) :
    ∀ t ∈ Finset.Icc 1 N, Measurable (arm β X ε W t) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  intro ht
  have ht' := Finset.mem_Icc.mp ht
  have ha : ∀ s ∈ Finset.Icc 1 (t - 1),
      Measurable fun ω => (if 1 ≤ s ∧ s < t then arm β X ε W s ω else 0 : Fin 2) := by
    intro s hs
    have hs' := Finset.mem_Icc.mp hs
    have hc : 1 ≤ s ∧ s < t := ⟨hs'.1, by omega⟩
    simp only [hc, and_self, if_true]
    exact ih s hc.2 (Finset.mem_Icc.mpr ⟨hs'.1, by omega⟩)
  have hX' : ∀ s ∈ Finset.Icc 1 (t - 1), Measurable (X s) := fun s hs => hX s
    (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hs).1, by have := (Finset.mem_Icc.mp hs).2; omega⟩)
  have hε' : ∀ j, ∀ s ∈ Finset.Icc 1 (t - 1), Measurable (ε j s) := fun j s hs => hε j s
    (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hs).1, by have := (Finset.mem_Icc.mp hs).2; omega⟩)
  have e0 := measurable_estOf' β X ε
    (fun ω s => if 1 ≤ s ∧ s < t then arm β X ε W s ω else 0) 0 (t - 1) hX' (hε' 0) ha
  have e1 := measurable_estOf' β X ε
    (fun ω s => if 1 ≤ s ∧ s < t then arm β X ε W s ω else 0) 1 (t - 1) hX' (hε' 1) ha
  have : arm β X ε W t = fun ω => greedyChoice (X t ω)
      (estOf β (fun s => X s ω) (fun j s => ε j s ω)
        (fun s => if 1 ≤ s ∧ s < t then arm β X ε W s ω else 0) 0 (t - 1))
      (estOf β (fun s => X s ω) (fun j s => ε j s ω)
        (fun s => if 1 ≤ s ∧ s < t then arm β X ε W s ω else 0) 1 (t - 1)) (W t ω) :=
    funext fun ω => arm_eq_greedy β X ε W t ω
  rw [this]
  exact measurable_greedyChoice _ _ _ _ (hX t ht) e0 e1 (hW t ht)

theorem measurable_est_le (β : Fin 2 → Fin d → ℝ) (X : ℕ → Ω → Fin d → ℝ)
    (ε : Fin 2 → ℕ → Ω → ℝ) (W : ℕ → Ω → Bool) (N : ℕ)
    (hX : ∀ s ∈ Finset.Icc 1 N, Measurable (X s)) (hW : ∀ s ∈ Finset.Icc 1 N, Measurable (W s))
    (hε : ∀ j, ∀ s ∈ Finset.Icc 1 N, Measurable (ε j s)) (i : Fin 2) :
    Measurable fun ω => estOf β (fun s => X s ω) (fun j s => ε j s ω)
      (fun s => if 1 ≤ s ∧ s < N + 1 then arm β X ε W s ω else 0) i N := by
  have harm := measurable_arm_le β X ε W N hX hW (fun j s hs => hε j s
    (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hs).1, by have := (Finset.mem_Icc.mp hs).2; omega⟩))
  refine measurable_estOf' β X ε _ i N hX (hε i) (fun s hs => ?_)
  have hs' := Finset.mem_Icc.mp hs
  have hc : 1 ≤ s ∧ s < N + 1 := ⟨hs'.1, by omega⟩
  simp only [hc, and_self, if_true]
  exact harm s hs

end Meas


/-- The time `t ≥ 1` carried by each primitive variable of the model. -/
def idxTime : ModelIndex → ℕ :=
  Sum.elim (Sum.elim (fun t => t + 1) (fun p => p.2 + 1)) (fun t => t + 1)

section Filt
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}

/-- `H_k`: the σ-algebra generated by all contexts, noises and coins of times `≤ k`. -/
noncomputable def filt (X : ℕ → Ω → Fin d → ℝ) (ε : Fin 2 → ℕ → Ω → ℝ) (W : ℕ → Ω → Bool)
    (k : ℕ) : MeasurableSpace Ω :=
  ⨆ (j : ModelIndex) (_ : idxTime j ≤ k), modelSigma X ε W j

theorem filt_mono (X : ℕ → Ω → Fin d → ℝ) (ε : Fin 2 → ℕ → Ω → ℝ) (W : ℕ → Ω → Bool) :
    Monotone (filt X ε W) := by
  intro k l hkl
  unfold filt
  exact iSup₂_mono' (fun j hj => ⟨j, hj.trans hkl, le_rfl⟩)

theorem modelSigma_le (X : ℕ → Ω → Fin d → ℝ) (ε : Fin 2 → ℕ → Ω → ℝ) (W : ℕ → Ω → Bool)
    (hX : ∀ t, Measurable (X t)) (hε : ∀ i t, Measurable (ε i t)) (hW : ∀ t, Measurable (W t))
    (j : ModelIndex) : modelSigma X ε W j ≤ mΩ := by
  rcases j with (j | p) | j
  · exact (hX (j + 1)).comap_le
  · exact (hε p.1 (p.2 + 1)).comap_le
  · exact (hW (j + 1)).comap_le

theorem filt_le (X : ℕ → Ω → Fin d → ℝ) (ε : Fin 2 → ℕ → Ω → ℝ) (W : ℕ → Ω → Bool)
    (hX : ∀ t, Measurable (X t)) (hε : ∀ i t, Measurable (ε i t)) (hW : ∀ t, Measurable (W t))
    (k : ℕ) : filt X ε W k ≤ mΩ :=
  iSup₂_le (fun j _ => modelSigma_le X ε W hX hε hW j)

theorem measurable_X_filt (X : ℕ → Ω → Fin d → ℝ) (ε : Fin 2 → ℕ → Ω → ℝ) (W : ℕ → Ω → Bool)
    {k s : ℕ} (h1 : 1 ≤ s) (h2 : s ≤ k) : Measurable[filt X ε W k] (X s) := by
  have h := le_iSup₂ (f := fun (j : ModelIndex) (_ : idxTime j ≤ k) => modelSigma X ε W j)
    (Sum.inl (Sum.inl (s - 1))) (by simp only [idxTime, Sum.elim_inl]; omega)
  simp only [modelSigma, Sum.elim_inl] at h
  rw [show s - 1 + 1 = s by omega] at h
  exact measurable_iff_comap_le.mpr h

theorem measurable_ε_filt (X : ℕ → Ω → Fin d → ℝ) (ε : Fin 2 → ℕ → Ω → ℝ) (W : ℕ → Ω → Bool)
    (j : Fin 2) {k s : ℕ} (h1 : 1 ≤ s) (h2 : s ≤ k) : Measurable[filt X ε W k] (ε j s) := by
  have h := le_iSup₂ (f := fun (j : ModelIndex) (_ : idxTime j ≤ k) => modelSigma X ε W j)
    (Sum.inl (Sum.inr (j, s - 1))) (by simp only [idxTime, Sum.elim_inl, Sum.elim_inr]; omega)
  simp only [modelSigma, Sum.elim_inl, Sum.elim_inr] at h
  rw [show s - 1 + 1 = s by omega] at h
  exact measurable_iff_comap_le.mpr h

theorem measurable_W_filt (X : ℕ → Ω → Fin d → ℝ) (ε : Fin 2 → ℕ → Ω → ℝ) (W : ℕ → Ω → Bool)
    {k s : ℕ} (h1 : 1 ≤ s) (h2 : s ≤ k) : Measurable[filt X ε W k] (W s) := by
  have h := le_iSup₂ (f := fun (j : ModelIndex) (_ : idxTime j ≤ k) => modelSigma X ε W j)
    (Sum.inr (s - 1)) (by simp only [idxTime, Sum.elim_inr]; omega)
  simp only [modelSigma, Sum.elim_inr] at h
  rw [show s - 1 + 1 = s by omega] at h
  exact measurable_iff_comap_le.mpr h

theorem indep_filt (P : Measure Ω) (X : ℕ → Ω → Fin d → ℝ) (ε : Fin 2 → ℕ → Ω → ℝ)
    (W : ℕ → Ω → Bool)
    (hX : ∀ t, Measurable (X t)) (hε : ∀ i t, Measurable (ε i t)) (hW : ∀ t, Measurable (W t))
    (hind : iIndep (modelSigma X ε W) P) (k : ℕ) (hk : 1 ≤ k) :
    Indep (filt X ε W (k - 1))
      (MeasurableSpace.comap (fun ω => (X k ω, W k ω)) inferInstance) P := by
  set T : Set ModelIndex := {Sum.inl (Sum.inl (k - 1)), Sum.inr (k - 1)} with hT
  have hdisj : Disjoint {j : ModelIndex | idxTime j ≤ k - 1} T := by
    rw [Set.disjoint_left]
    intro j hj hjT
    simp only [Set.mem_ofPred_eq] at hj
    rcases hjT with h | h
    · subst h; simp only [idxTime, Sum.elim_inl] at hj; omega
    · rw [Set.mem_singleton_iff] at h; subst h; simp only [idxTime, Sum.elim_inr] at hj; omega
  have h := indep_iSup_of_disjoint (modelSigma_le X ε W hX hε hW) hind hdisj
  refine indep_of_indep_of_le_right h ?_
  apply measurable_iff_comap_le.mp
  refine Measurable.prodMk ?_ ?_
  · have h1 := le_iSup₂ (f := fun (j : ModelIndex) (_ : j ∈ T) => modelSigma X ε W j)
      (Sum.inl (Sum.inl (k - 1))) (by simp [hT])
    simp only [modelSigma, Sum.elim_inl] at h1
    rw [show k - 1 + 1 = k by omega] at h1
    exact measurable_iff_comap_le.mpr h1
  · have h1 := le_iSup₂ (f := fun (j : ModelIndex) (_ : j ∈ T) => modelSigma X ε W j)
      (Sum.inr (k - 1)) (by simp [hT])
    simp only [modelSigma, Sum.elim_inr] at h1
    rw [show k - 1 + 1 = k by omega] at h1
    exact measurable_iff_comap_le.mpr h1

end Filt


section LinAlg
variable {d : ℕ}

theorem dot_sq_le (v x : Fin d → ℝ) : (v ⬝ᵥ x) ^ 2 ≤ (v ⬝ᵥ v) * (x ⬝ᵥ x) := by
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v x
  simpa [dotProduct, sq] using this

theorem dot_self_le_of_l2norm {x : Fin d → ℝ} {xmax : ℝ} (h : l2norm x ≤ xmax) :
    x ⬝ᵥ x ≤ xmax ^ 2 := by
  unfold l2norm at h
  have hxx : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))
  rw [← Real.sq_sqrt hxx]
  exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2

theorem abs_mul_le_dot_self (x : Fin d → ℝ) (a b : Fin d) : |x a * x b| ≤ x ⬝ᵥ x := by
  have ha : x a * x a ≤ x ⬝ᵥ x := Finset.single_le_sum (f := fun j => x j * x j)
    (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ a)
  have hb : x b * x b ≤ x ⬝ᵥ x := Finset.single_le_sum (f := fun j => x j * x j)
    (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ b)
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (x a + x b), sq_nonneg (x a - x b)]

theorem quad_sum_eq (v x : Fin d → ℝ) :
    ∑ a, v a * ∑ b, x a * x b * v b = (v ⬝ᵥ x) ^ 2 := by
  rw [sq, dotProduct, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

theorem rayleigh_vecMulVec (v x : Fin d → ℝ) :
    v ⬝ᵥ (vecMulVec x x *ᵥ v) = (v ⬝ᵥ x) ^ 2 := by
  rw [← quad_sum_eq]
  simp only [dotProduct, mulVec, vecMulVec_apply]

theorem lambdaMax_le_of (hd : 1 ≤ d) (M : Matrix (Fin d) (Fin d) ℝ) (R : ℝ)
    (h : ∀ v : Fin d → ℝ, v ⬝ᵥ v = 1 → v ⬝ᵥ (M *ᵥ v) ≤ R) : lambdaMax M ≤ R := by
  have : Nonempty {v : Fin d → ℝ // v ⬝ᵥ v = 1} :=
    ⟨⟨Pi.single ⟨0, hd⟩ 1, by simp⟩⟩
  exact ciSup_le (fun v => h v.1 v.2)

theorem le_lambdaMin_of (hd : 1 ≤ d) (M : Matrix (Fin d) (Fin d) ℝ) (c : ℝ)
    (h : ∀ v : Fin d → ℝ, v ⬝ᵥ v = 1 → c ≤ v ⬝ᵥ (M *ᵥ v)) : c ≤ lambdaMin M := by
  have : Nonempty {v : Fin d → ℝ // v ⬝ᵥ v = 1} :=
    ⟨⟨Pi.single ⟨0, hd⟩ 1, by simp⟩⟩
  exact le_ciInf (fun v => h v.1 v.2)

theorem rayleigh_ge_of_lambdaMin (M : Matrix (Fin d) (Fin d) ℝ) (c : ℝ) (hc : 0 < c)
    (h : c ≤ lambdaMin M) (v : Fin d → ℝ) (hv : v ⬝ᵥ v = 1) : c ≤ v ⬝ᵥ (M *ᵥ v) := by
  unfold lambdaMin at h
  by_cases hb : BddBelow (Set.range fun w : {w : Fin d → ℝ // w ⬝ᵥ w = 1} => w.1 ⬝ᵥ (M *ᵥ w.1))
  · exact h.trans (ciInf_le hb ⟨v, hv⟩)
  · rw [Real.iInf_of_not_bddBelow hb] at h
    linarith

theorem quad_integral {α : Type*} [MeasurableSpace α] (ν : Measure α) (v : Fin d → ℝ)
    (g : Fin d → Fin d → α → ℝ) (hg : ∀ a b, Integrable (g a b) ν) :
    v ⬝ᵥ (Matrix.of (fun a b => ∫ y, g a b y ∂ν) *ᵥ v)
      = ∫ y, ∑ a, v a * ∑ b, g a b y * v b ∂ν := by
  simp only [dotProduct, mulVec, Matrix.of_apply]
  rw [integral_finsetSum _ (fun a _ => ((integrable_finsetSum _
    (fun b _ => (hg a b).mul_const (v b))).const_mul (v a)))]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [integral_const_mul, integral_finsetSum _ (fun b _ => (hg a b).mul_const (v b))]
  congr 1
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [integral_mul_const]

end LinAlg

theorem abs_dot_le' {d : ℕ} (x y : Fin d → ℝ) : |x ⬝ᵥ y| ≤ l2norm x * l2norm y := by
  unfold l2norm
  have h0 : (0:ℝ) ≤ x ⬝ᵥ x := Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))
  rw [← Real.sqrt_mul h0]
  apply Real.abs_le_sqrt
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y
  simpa [dotProduct, sq] using this

theorem meas_of_matrix_cont' {Ω : Type*} {mΩ : MeasurableSpace Ω} {d : ℕ}
    (F : Matrix (Fin d) (Fin d) ℝ → ℝ) (hF : Continuous F) (G : Ω → Matrix (Fin d) (Fin d) ℝ)
    (hG : ∀ p q, Measurable fun ω => G ω p q) : Measurable fun ω => F (G ω) := by
  have h1 : Measurable (fun ω => (fun p q => G ω p q : Fin d → Fin d → ℝ)) :=
    measurable_pi_lambda _ (fun p => measurable_pi_lambda _ (fun q => hG p q))
  have h2 : Continuous (fun f : Fin d → Fin d → ℝ => F f) := hF
  exact h2.measurable.comp h1

theorem greedy_one {d : ℕ} (x b0 b1 : Fin d → ℝ) (w : Bool) (h : greedyChoice x b0 b1 w = 1) :
    x ⬝ᵥ b0 ≤ x ⬝ᵥ b1 := by
  unfold greedyChoice at h
  split_ifs at h with h1 h2 <;> first | exact absurd h (by decide) | linarith

theorem greedy_zero {d : ℕ} (x b0 b1 : Fin d → ℝ) (w : Bool) (h : greedyChoice x b0 b1 w = 0) :
    x ⬝ᵥ b1 ≤ x ⬝ᵥ b0 := by
  unfold greedyChoice at h
  split_ifs at h with h1 h2 <;> first | exact absurd h (by decide) | linarith

theorem sum_sq_range (N : ℕ) :
    ∑ h ∈ Finset.range N, ((h : ℝ) + 1) ^ 2 = (N : ℝ) * (N + 1) * (2 * N + 1) / 6 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem succ_sq_le_four_pow (k : ℕ) : ((k : ℝ) + 1) ^ 2 ≤ 4 ^ k := by
  have h1 : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
  have h2 : ((k : ℝ) + 1) ≤ 2 ^ k := by exact_mod_cast h1
  calc ((k : ℝ) + 1) ^ 2 ≤ (2 ^ k) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
    _ = 4 ^ k := by rw [← pow_mul, mul_comm, pow_mul]; norm_num

theorem exp_four_ge : (54 : ℝ) ≤ Real.exp 4 := by
  have h := Real.exp_one_gt_d9
  have : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7182818283) h.le 4]

theorem front_decay (y : ℝ) (hy : 0 ≤ y) :
    (y + 4) ^ 2 * Real.exp (-(2 * (y + 2))) ≤ 16 * Real.exp (-4) := by
  have he : Real.exp (-(2 * (y + 2))) = Real.exp (-4) * (Real.exp y) ⁻¹ ^ 2 := by
    rw [inv_pow, ← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_add]; push_cast; ring_nf
  rw [he]
  have hey : 1 + y ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
  have hpos : 0 < Real.exp y := Real.exp_pos y
  have h4 : 0 < Real.exp (-4) := Real.exp_pos _
  have key : (y + 4) ^ 2 * ((Real.exp y)⁻¹) ^ 2 ≤ 16 := by
    rw [← mul_pow, ← div_eq_mul_inv, div_pow, div_le_iff₀ (by positivity)]
    nlinarith
  nlinarith

theorem cbar_expand (d : ℕ) (hd : 2 ≤ d) :
    Cbar d * Real.log d ^ (3 / 2 : ℝ)
      = Real.sqrt (Real.log d) ^ 3 / 3 + 7 / 2 * Real.sqrt (Real.log d) ^ 2
        + 38 / 3 * Real.sqrt (Real.log d) + 67 / 4 := by
  have hℓ : 0 < Real.log d := Real.log_pos (by exact_mod_cast (by omega : 1 < d))
  set ℓ := Real.log d with hℓdef
  set L := Real.sqrt ℓ with hLdef
  have hL : 0 < L := Real.sqrt_pos.mpr hℓ
  have hL2 : L ^ 2 = ℓ := Real.sq_sqrt hℓ.le
  have hhalf : ℓ ^ (1 / 2 : ℝ) = L := by rw [hLdef, Real.sqrt_eq_rpow]
  have h32 : ℓ ^ (3 / 2 : ℝ) = L ^ 3 := by
    rw [← hhalf, ← Real.rpow_natCast, ← Real.rpow_mul hℓ.le]; norm_num
  have hm12 : ℓ ^ (-(1 / 2) : ℝ) = L⁻¹ := by rw [Real.rpow_neg hℓ.le, hhalf]
  have hm32 : ℓ ^ (-(3 / 2) : ℝ) = (L ^ 3)⁻¹ := by rw [Real.rpow_neg hℓ.le, h32]
  unfold Cbar
  rw [← hℓdef, h32, hm12, hm32, ← hL2]
  field_simp

theorem sum_bound (d : ℕ) (hd : 2 ≤ d) (H : ℕ) :
    ∑ h ∈ Finset.range H, ((h : ℝ) + 1) ^ 2 * min 1 (4 * d * Real.exp (-((h : ℝ) ^ 2)))
      ≤ Cbar d * Real.log d ^ (3 / 2 : ℝ) := by
  rw [cbar_expand d hd]
  have hℓ : 0 < Real.log d := Real.log_pos (by exact_mod_cast (by omega : 1 < d))
  set ℓ := Real.log d with hℓdef
  set L := Real.sqrt ℓ with hLdef
  have hL2 : L ^ 2 = ℓ := Real.sq_sqrt hℓ.le
  have hL0 : 0 ≤ L := Real.sqrt_nonneg _
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hlog2 : Real.log 2 ≤ ℓ := Real.log_le_log (by norm_num) hdR
  have hl2a := Real.log_two_gt_d9
  have hl2b := Real.log_two_lt_d9
  have hLlo : (0.83 : ℝ) < L := by nlinarith
  set h0 : ℕ := ⌊L⌋₊ + 2 with hh0
  have hh0lo : L + 1 < (h0 : ℝ) := by
    have := Nat.lt_floor_add_one L; push_cast [hh0]; linarith
  have hh0hi : (h0 : ℝ) ≤ L + 2 := by
    have := Nat.floor_le hL0; push_cast [hh0]; linarith
  have hh02 : (2 : ℝ) ≤ h0 := by push_cast [hh0]; linarith [(Nat.cast_nonneg ⌊L⌋₊ : (0:ℝ) ≤ _)]
  -- 4 d e^{-h0²} ≤ 1
  have hdpos : (0 : ℝ) < d := by linarith
  have hkey : 4 * (d : ℝ) * Real.exp (-((h0 : ℝ) ^ 2)) ≤ 1 := by
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have hsq : ℓ + Real.log 4 ≤ (h0 : ℝ) ^ 2 := by nlinarith
    have : Real.exp (-((h0 : ℝ) ^ 2)) ≤ Real.exp (-(ℓ + Real.log 4)) :=
      Real.exp_le_exp.mpr (by linarith)
    have he : Real.exp (-(ℓ + Real.log 4)) = (d : ℝ)⁻¹ * 4⁻¹ := by
      rw [neg_add, Real.exp_add, Real.exp_neg, Real.exp_neg, hℓdef, Real.exp_log hdpos,
        Real.exp_log (by norm_num)]
    rw [he] at this
    have h4d : 0 < 4 * (d : ℝ) := by positivity
    calc 4 * (d : ℝ) * Real.exp (-((h0 : ℝ) ^ 2)) ≤ 4 * d * ((d : ℝ)⁻¹ * 4⁻¹) :=
          mul_le_mul_of_nonneg_left this h4d.le
      _ = 1 := by field_simp
  set a : ℕ → ℝ := fun h => ((h : ℝ) + 1) ^ 2 * min 1 (4 * d * Real.exp (-((h : ℝ) ^ 2)))
    with ha
  have ha0 : ∀ h, 0 ≤ a h := fun h => mul_nonneg (by positivity)
    (le_min zero_le_one (by positivity))
  set ρ : ℝ := 4 * Real.exp (-4) with hρ
  have he4 : Real.exp (-4) ≤ 1 / 54 := by
    rw [Real.exp_neg, ← one_div]; exact one_div_le_one_div_of_le (by norm_num) exp_four_ge
  have he4pos : 0 < Real.exp (-4) := Real.exp_pos _
  have hρ1 : ρ < 1 := by rw [hρ]; linarith
  -- tail terms
  have htail : ∀ k : ℕ, a (h0 + 1 + k) ≤ 16 * Real.exp (-4) * ρ ^ k := by
    intro k
    simp only [ha]
    push_cast
    have hm : min 1 (4 * (d : ℝ) * Real.exp (-(((h0 : ℝ) + 1 + k) ^ 2)))
        ≤ Real.exp (-(2 * (h0 : ℝ) + 4 * k)) := by
      refine (min_le_right _ _).trans ?_
      have : 4 * (d : ℝ) * Real.exp (-(((h0 : ℝ) + 1 + k) ^ 2))
          = (4 * d * Real.exp (-((h0 : ℝ) ^ 2)))
            * Real.exp (-(2 * (h0 : ℝ) * (k + 1) + ((k : ℝ) + 1) ^ 2)) := by
        have hx : Real.exp (-(((h0 : ℝ) + 1 + k) ^ 2)) = Real.exp (-((h0 : ℝ) ^ 2))
            * Real.exp (-(2 * (h0 : ℝ) * (k + 1) + ((k : ℝ) + 1) ^ 2)) := by
          rw [← Real.exp_add]; ring_nf
        rw [hx]; ring
      rw [this]
      calc (4 * (d : ℝ) * Real.exp (-((h0 : ℝ) ^ 2)))
            * Real.exp (-(2 * (h0 : ℝ) * (k + 1) + ((k : ℝ) + 1) ^ 2))
          ≤ 1 * Real.exp (-(2 * (h0 : ℝ) * (k + 1) + ((k : ℝ) + 1) ^ 2)) :=
            mul_le_mul_of_nonneg_right hkey (Real.exp_pos _).le
        _ ≤ Real.exp (-(2 * (h0 : ℝ) + 4 * k)) := by
            rw [one_mul]; apply Real.exp_le_exp.mpr
            have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
            nlinarith
    have hsq : ((h0 : ℝ) + 1 + k + 1) ^ 2 ≤ ((h0 : ℝ) + 2) ^ 2 * 4 ^ k := by
      have h1 := succ_sq_le_four_pow k
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have : (h0 : ℝ) + 1 + k + 1 ≤ ((h0 : ℝ) + 2) * ((k : ℝ) + 1) := by nlinarith
      calc ((h0 : ℝ) + 1 + k + 1) ^ 2 ≤ (((h0 : ℝ) + 2) * ((k : ℝ) + 1)) ^ 2 :=
            pow_le_pow_left₀ (by positivity) this 2
        _ = ((h0 : ℝ) + 2) ^ 2 * ((k : ℝ) + 1) ^ 2 := by ring
        _ ≤ ((h0 : ℝ) + 2) ^ 2 * 4 ^ k := mul_le_mul_of_nonneg_left h1 (by positivity)
    have hfront := front_decay ((h0 : ℝ) - 2) (by linarith)
    rw [show (h0 : ℝ) - 2 + 4 = (h0 : ℝ) + 2 by ring,
      show (h0 : ℝ) - 2 + 2 = (h0 : ℝ) by ring] at hfront
    have hsplit : Real.exp (-(2 * (h0 : ℝ) + 4 * k)) = Real.exp (-(2 * (h0 : ℝ)))
        * Real.exp (-4) ^ k := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; ring_nf
    rw [hsplit] at hm
    have hρk : ρ ^ k = 4 ^ k * Real.exp (-4) ^ k := by rw [hρ, mul_pow]
    rw [hρk]
    calc ((h0 : ℝ) + 1 + k + 1) ^ 2 * min 1 (4 * (d : ℝ) * Real.exp (-(((h0 : ℝ) + 1 + k) ^ 2)))
        ≤ (((h0 : ℝ) + 2) ^ 2 * 4 ^ k) * (Real.exp (-(2 * (h0 : ℝ))) * Real.exp (-4) ^ k) :=
          mul_le_mul hsq hm (le_min zero_le_one (by positivity)) (by positivity)
      _ = (((h0 : ℝ) + 2) ^ 2 * Real.exp (-(2 * (h0 : ℝ)))) * (4 ^ k * Real.exp (-4) ^ k) := by
          ring
      _ ≤ (16 * Real.exp (-4)) * (4 ^ k * Real.exp (-4) ^ k) :=
          mul_le_mul_of_nonneg_right hfront (by positivity)
  have hgeom : ∑ k ∈ Finset.range H, ρ ^ k ≤ 1 / (1 - ρ) := by
    rw [geom_sum_eq hρ1.ne]
    have h1ρ : 0 < 1 - ρ := by linarith
    have hρH : 0 ≤ ρ ^ H := by positivity
    rw [show (ρ ^ H - 1) / (ρ - 1) = (1 - ρ ^ H) / (1 - ρ) by
      rw [← neg_div_neg_eq]; ring_nf]
    exact div_le_div_of_nonneg_right (by linarith) h1ρ.le
  have hfirst : ∑ h ∈ Finset.range (h0 + 1), a h ≤ ((h0 : ℝ) + 1) * (h0 + 2) * (2 * h0 + 3) / 6 := by
    calc ∑ h ∈ Finset.range (h0 + 1), a h ≤ ∑ h ∈ Finset.range (h0 + 1), ((h : ℝ) + 1) ^ 2 :=
          Finset.sum_le_sum (fun h _ => by
            simp only [ha]
            exact mul_le_of_le_one_right (by positivity) (min_le_left _ _))
      _ = ((h0 : ℝ) + 1) * (h0 + 2) * (2 * h0 + 3) / 6 := by
          rw [sum_sq_range]; push_cast; ring
  calc ∑ h ∈ Finset.range H, a h ≤ ∑ h ∈ Finset.range (h0 + 1 + H), a h :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
          (fun h _ _ => ha0 h)
    _ = ∑ h ∈ Finset.range (h0 + 1), a h + ∑ k ∈ Finset.range H, a (h0 + 1 + k) :=
        Finset.sum_range_add _ _ _
    _ ≤ ((h0 : ℝ) + 1) * (h0 + 2) * (2 * h0 + 3) / 6
          + ∑ k ∈ Finset.range H, 16 * Real.exp (-4) * ρ ^ k :=
        add_le_add hfirst (Finset.sum_le_sum (fun k _ => htail k))
    _ ≤ (L + 3) * (L + 4) * (2 * L + 7) / 6 + 16 * Real.exp (-4) * (1 / (1 - ρ)) := by
        rw [← Finset.mul_sum]
        have hA : ((h0 : ℝ) + 1) * (h0 + 2) * (2 * h0 + 3) ≤ (L + 3) * (L + 4) * (2 * L + 7) := by
          have h1 : (0:ℝ) ≤ (h0 : ℝ) + 1 := by positivity
          apply mul_le_mul (mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity))
            (by linarith) (by positivity) (by positivity)
        have hB := mul_le_mul_of_nonneg_left hgeom (by positivity : (0:ℝ) ≤ 16 * Real.exp (-4))
        linarith
    _ ≤ L ^ 3 / 3 + 7 / 2 * L ^ 2 + 38 / 3 * L + 67 / 4 := by
        have h1ρ : 0 < 1 - ρ := by linarith
        have : 16 * Real.exp (-4) * (1 / (1 - ρ)) ≤ 1 := by
          rw [mul_one_div, div_le_one h1ρ, hρ]; linarith
        nlinarith


theorem measurable_l2norm {d : ℕ} : Measurable (fun x : Fin d → ℝ => l2norm x) :=
  (Real.continuous_sqrt.comp (continuous_id.dotProduct continuous_id)).measurable

theorem wrong_implies {d : ℕ} (x bl bi βl βi : Fin d → ℝ) (xmax η : ℝ)
    (hx : l2norm x ≤ xmax) (hxmax : 0 < xmax) (hZ : 2 * xmax * η < x ⬝ᵥ (βl - βi))
    (hW : 0 ≤ x ⬝ᵥ (bi - bl)) : η ≤ l2norm (bl - βl) ∨ η ≤ l2norm (bi - βi) := by
  by_contra hcon
  push Not at hcon
  have hn : ∀ v : Fin d → ℝ, l2norm v < η → |x ⬝ᵥ v| < xmax * η := by
    intro v hv
    have h0 : 0 ≤ l2norm v := Real.sqrt_nonneg _
    calc |x ⬝ᵥ v| ≤ l2norm x * l2norm v := abs_dot_le' x v
      _ ≤ xmax * l2norm v := mul_le_mul_of_nonneg_right hx h0
      _ < xmax * η := mul_lt_mul_of_pos_left hv hxmax
  have h1 := abs_lt.mp (hn _ hcon.1)
  have h2 := abs_lt.mp (hn _ hcon.2)
  simp only [dotProduct_sub] at h1 h2 hZ hW
  linarith

end MEFLemma6Aux

open MostlyExplorationFree.GreedyBandit MEFLemma6Aux

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d : ℕ} (hd : 2 ≤ d)
    (μ : Measure (Fin d → ℝ)) (X : ℕ → Ω → Fin d → ℝ) (ε : Fin 2 → ℕ → Ω → ℝ)
    (W : ℕ → Ω → Bool) (σ : ℝ) (hσ : 0 < σ) (β : Fin 2 → Fin d → ℝ)
    (xmax bmax C0 lam0 : ℝ) (hlam0 : 0 < lam0)
    (hmodel : IsGreedyModel P μ X ε W σ) (hA1 : ParameterSet μ β xmax bmax)
    (hA2 : MarginCondition μ β C0) (t : ℕ) (ht : 2 ≤ t) :
    instRegret β X ε W P t
      ≤ 4 * C0 * Cbar d * xmax ^ 2 * Real.log d ^ (3 / 2 : ℝ) / C3 lam0 d σ xmax
          * (1 / ((t : ℝ) - 1))
        + 4 * bmax * xmax *
          max (P {ω | lambdaMin (gram β X ε W 0 (t - 1) ω) < lam0 * ((t : ℝ) - 1) / 4}).toReal
              (P {ω | lambdaMin (gram β X ε W 1 (t - 1) ω) < lam0 * ((t : ℝ) - 1) / 4}).toReal := by
  have hP := hmodel.isProbability
  obtain ⟨m, rfl⟩ : ∃ m, t = m + 1 := ⟨t - 1, by omega⟩
  have hm1 : 1 ≤ m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm1
  rw [show ((m + 1 : ℕ) : ℝ) - 1 = m by push_cast; ring, Nat.add_sub_cancel]
  have hxmax : 0 < xmax := hA1.1
  have hXb0 := hA1.2.1
  have hβb := hA1.2.2
  have hC0 : 0 < C0 := hA2.1
  have hbmax : 0 ≤ bmax := le_trans (Real.sqrt_nonneg _) (hβb 0)
  have hXm := hmodel.measurable_X
  have hεm := hmodel.measurable_ε
  have hWm := hmodel.measurable_W
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hXae : ∀ᵐ ω ∂P, l2norm (X (m + 1) ω) ≤ xmax := by
    have h := hXb0
    rw [← hmodel.law_X (m + 1) (by omega)] at h
    exact ae_of_ae_map (hXm (m + 1)).aemeasurable h
  -- constants
  set c3 := C3 lam0 d σ xmax with hc3def
  have hc3 : 0 < c3 := by rw [hc3def]; unfold C3; positivity
  set δ := 1 / Real.sqrt (m * c3) with hδdef
  have hδ : 0 < δ := by rw [hδdef]; have := Real.sqrt_pos.mpr (mul_pos hmR hc3); positivity
  have hδsq : δ ^ 2 = 1 / (m * c3) := by
    rw [hδdef, div_pow, Real.sq_sqrt (mul_pos hmR hc3).le, one_pow]
  -- measurability of the run
  have hXFm : ∀ s ∈ Finset.Icc 1 m, Measurable[filt X ε W m] (X s) := fun s hs =>
    measurable_X_filt X ε W (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hs).2
  have hWFm : ∀ s ∈ Finset.Icc 1 m, Measurable[filt X ε W m] (W s) := fun s hs =>
    measurable_W_filt X ε W (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hs).2
  have hεFm : ∀ j, ∀ s ∈ Finset.Icc 1 m, Measurable[filt X ε W m] (ε j s) := fun j s hs =>
    measurable_ε_filt X ε W j (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hs).2
  have hFle : filt X ε W m ≤ ‹MeasurableSpace Ω› := filt_le X ε W hXm hεm hWm m
  have hest_eq : ∀ j ω, est β X ε W j m ω = estOf β (fun s => X s ω) (fun j s => ε j s ω)
      (fun s => if 1 ≤ s ∧ s < m + 1 then arm β X ε W s ω else 0) j m := by
    intro j ω
    refine estOf_congr _ _ _ _ _ _ _ (fun s hs => ?_)
    have hs' := Finset.mem_Icc.mp hs
    have hc : 1 ≤ s ∧ s < m + 1 := ⟨hs'.1, by omega⟩
    simp [hc]
  have hestF : ∀ j, Measurable[filt X ε W m] (est β X ε W j m) := by
    intro j
    have : est β X ε W j m = fun ω => estOf β (fun s => X s ω) (fun j s => ε j s ω)
        (fun s => if 1 ≤ s ∧ s < m + 1 then arm β X ε W s ω else 0) j m := funext (hest_eq j)
    rw [this]
    exact measurable_est_le (mΩ := filt X ε W m) β X ε W m hXFm hWFm hεFm j
  have harmF : ∀ s ∈ Finset.Icc 1 m, Measurable[filt X ε W m] (arm β X ε W s) :=
    measurable_arm_le (mΩ := filt X ε W m) β X ε W m hXFm hWFm
      (fun j s hs => hεFm j s (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hs).1,
        by have := (Finset.mem_Icc.mp hs).2; omega⟩))
  have hlamF : ∀ j, Measurable[filt X ε W m] (fun ω => lambdaMin (gram β X ε W j m ω)) := by
    intro j
    exact meas_of_matrix_cont' (mΩ := filt X ε W m) _ continuous_lambdaMin _
      (measurable_gramOf_entry' (mΩ := filt X ε W m) X (fun ω s => arm β X ε W s ω) j m hXFm
        harmF)
  have hestM : ∀ j, Measurable (est β X ε W j m) := fun j => (hestF j).mono hFle le_rfl
  have hlamM : ∀ j, Measurable (fun ω => lambdaMin (gram β X ε W j m ω)) :=
    fun j => (hlamF j).mono hFle le_rfl
  have harm_eq : ∀ ω, arm β X ε W (m + 1) ω
      = greedyChoice (X (m + 1) ω) (est β X ε W 0 m ω) (est β X ε W 1 m ω) (W (m + 1) ω) := by
    intro ω
    rw [arm_eq_greedy, Nat.add_sub_cancel, ← hest_eq 0 ω, ← hest_eq 1 ω]
  -- events
  set F : Fin 2 → Set Ω := fun j => {ω | lam0 / 4 * m ≤ lambdaMin (gram β X ε W j m ω)}
    with hFdef
  have hFm : ∀ j, MeasurableSet (F j) := fun j => measurableSet_le measurable_const (hlamM j)
  have hFbar : ∀ j, {ω | lambdaMin (gram β X ε W j m ω) < lam0 * m / 4} = (F j)ᶜ := by
    intro j; ext ω
    simp only [hFdef, Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]
    constructor <;> intro h <;> linarith
  rw [hFbar 0, hFbar 1]
  set Z : Fin 2 → Fin 2 → Ω → ℝ := fun l i ω => X (m + 1) ω ⬝ᵥ (β l - β i) with hZdef
  set κ : ℕ → ℝ := fun h => 2 * δ * xmax * ((h : ℝ) + 1) with hκdef
  set I : Fin 2 → Fin 2 → ℕ → Set Ω := fun l i h =>
    {ω | 2 * δ * xmax * h < Z l i ω ∧ Z l i ω ≤ κ h} with hIdef
  set Wr : Fin 2 → Fin 2 → Set Ω := fun l i =>
    {ω | 0 ≤ X (m + 1) ω ⬝ᵥ (est β X ε W i m ω - est β X ε W l m ω)} with hWrdef
  set A : Fin 2 → Fin 2 → ℕ → Set Ω := fun l i h => I l i h ∩ Wr l i ∩ (F 0 ∩ F 1) with hAdef
  set H : ℕ := ⌈bmax / δ⌉₊ + 1 with hHdef
  have hZm : ∀ l i, Measurable (Z l i) := fun l i =>
    (continuous_id.dotProduct continuous_const).measurable.comp (hXm _)
  have hIm : ∀ l i h, MeasurableSet (I l i h) := fun l i h =>
    (measurableSet_lt measurable_const (hZm l i)).inter (measurableSet_le (hZm l i) measurable_const)
  have hWrm : ∀ l i, MeasurableSet (Wr l i) := fun l i =>
    measurableSet_le measurable_const ((continuous_fst.dotProduct continuous_snd).measurable.comp
      ((hXm _).prodMk ((hestM i).sub (hestM l))))
  have hAm : ∀ l i h, MeasurableSet (A l i h) := fun l i h =>
    ((hIm l i h).inter (hWrm l i)).inter ((hFm 0).inter (hFm 1))
  -- the dominating function
  set RHS : Ω → ℝ := fun ω => ∑ h ∈ Finset.range H, κ h * ((A 0 1 h).indicator (1 : Ω → ℝ) ω
      + (A 1 0 h).indicator (1 : Ω → ℝ) ω)
      + 2 * bmax * xmax * ((F 0)ᶜ.indicator (1 : Ω → ℝ) ω + (F 1)ᶜ.indicator (1 : Ω → ℝ) ω)
    with hRHSdef
  have hκpos : ∀ h, 0 ≤ κ h := fun h => by simp only [hκdef]; positivity
  have hind01 : ∀ (s : Set Ω) ω, 0 ≤ s.indicator (1 : Ω → ℝ) ω := fun s ω =>
    Set.indicator_nonneg (fun _ _ => zero_le_one) ω
  have hsum_nn : ∀ ω, 0 ≤ ∑ h ∈ Finset.range H, κ h * ((A 0 1 h).indicator (1 : Ω → ℝ) ω
      + (A 1 0 h).indicator (1 : Ω → ℝ) ω) := fun ω =>
    Finset.sum_nonneg (fun h _ => mul_nonneg (hκpos h) (add_nonneg (hind01 _ _) (hind01 _ _)))
  have hbx : 0 ≤ 2 * bmax * xmax := by positivity
  have hpt : ∀ᵐ ω ∂P, max (X (m + 1) ω ⬝ᵥ β 0) (X (m + 1) ω ⬝ᵥ β 1)
      - X (m + 1) ω ⬝ᵥ β (arm β X ε W (m + 1) ω) ≤ RHS ω := by
    filter_upwards [hXae] with ω hω
    have hb : ∀ j, |X (m + 1) ω ⬝ᵥ β j| ≤ xmax * bmax := fun j =>
      (abs_dot_le' _ _).trans (mul_le_mul hω (hβb j) (Real.sqrt_nonneg _) hxmax.le)
    have hb0 := abs_le.mp (hb 0)
    have hb1 := abs_le.mp (hb 1)
    by_cases hF : ω ∈ F 0 ∧ ω ∈ F 1
    · -- the main case: locate the slice containing the gap
      have hslice : ∀ l i : Fin 2, arm β X ε W (m + 1) ω = i → ω ∈ Wr l i →
          max (X (m + 1) ω ⬝ᵥ β 0) (X (m + 1) ω ⬝ᵥ β 1) - X (m + 1) ω ⬝ᵥ β i
            ≤ max 0 (Z l i ω) →
          max (X (m + 1) ω ⬝ᵥ β 0) (X (m + 1) ω ⬝ᵥ β 1) - X (m + 1) ω ⬝ᵥ β i
            ≤ ∑ h ∈ Finset.range H, κ h * (A l i h).indicator (1 : Ω → ℝ) ω := by
        intro l i _ hWr hle
        by_cases hZ : Z l i ω ≤ 0
        · have : max 0 (Z l i ω) = 0 := max_eq_left hZ
          rw [this] at hle
          exact hle.trans (Finset.sum_nonneg (fun h _ => mul_nonneg (hκpos h) (hind01 _ _)))
        · push Not at hZ
          rw [max_eq_right hZ.le] at hle
          have hZle : Z l i ω ≤ 2 * xmax * bmax := by
            simp only [hZdef, dotProduct_sub]
            have := abs_le.mp (hb l); have := abs_le.mp (hb i); linarith
          set y := Z l i ω / (2 * δ * xmax) with hy
          have hy0 : 0 < y := by rw [hy]; positivity
          set h := ⌈y⌉₊ - 1 with hh
          have hc1 : 1 ≤ ⌈y⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp
            (Nat.ceil_pos.mpr hy0))
          have hhc : (h : ℝ) + 1 = ⌈y⌉₊ := by rw [hh]; push_cast [Nat.cast_sub hc1]; ring
          have hyle : y ≤ ⌈y⌉₊ := Nat.le_ceil y
          have hylt : (⌈y⌉₊ : ℝ) < y + 1 := Nat.ceil_lt_add_one hy0.le
          have hyb : y ≤ bmax / δ := by
            rw [hy, div_le_div_iff₀ (by positivity) hδ]
            nlinarith
          have hhH : h ∈ Finset.range H := by
            rw [Finset.mem_range, hHdef, hh]
            have := Nat.ceil_mono hyb
            omega
          have h2dx : 0 < 2 * δ * xmax := by positivity
          have hmemI : ω ∈ I l i h := by
            simp only [hIdef, hκdef, Set.mem_ofPred_eq]
            constructor
            · have : (h : ℝ) < y := by linarith
              have := mul_lt_mul_of_pos_left this h2dx
              rw [hy, mul_div_cancel₀ _ h2dx.ne'] at this
              exact this
            · rw [hhc]
              have := mul_le_mul_of_nonneg_left hyle h2dx.le
              rw [hy, mul_div_cancel₀ _ h2dx.ne'] at this
              exact this
          have hmemA : ω ∈ A l i h := ⟨⟨hmemI, hWr⟩, hF⟩
          calc max (X (m + 1) ω ⬝ᵥ β 0) (X (m + 1) ω ⬝ᵥ β 1) - X (m + 1) ω ⬝ᵥ β i
              ≤ κ h * (A l i h).indicator (1 : Ω → ℝ) ω := by
                rw [Set.indicator_of_mem hmemA, Pi.one_apply, mul_one]
                exact hle.trans hmemI.2
            _ ≤ ∑ h ∈ Finset.range H, κ h * (A l i h).indicator (1 : Ω → ℝ) ω :=
                Finset.single_le_sum (f := fun h => κ h * (A l i h).indicator (1 : Ω → ℝ) ω)
                  (fun h _ => mul_nonneg (hκpos h) (hind01 _ _)) hhH
      have hsplit : ∑ h ∈ Finset.range H, κ h * ((A 0 1 h).indicator (1 : Ω → ℝ) ω
          + (A 1 0 h).indicator (1 : Ω → ℝ) ω)
          = ∑ h ∈ Finset.range H, κ h * (A 0 1 h).indicator (1 : Ω → ℝ) ω
            + ∑ h ∈ Finset.range H, κ h * (A 1 0 h).indicator (1 : Ω → ℝ) ω := by
        rw [← Finset.sum_add_distrib]; congr 1; funext h; ring
      have hrest : 0 ≤ 2 * bmax * xmax * ((F 0)ᶜ.indicator (1 : Ω → ℝ) ω
          + (F 1)ᶜ.indicator (1 : Ω → ℝ) ω) := mul_nonneg hbx (add_nonneg (hind01 _ _) (hind01 _ _))
      have hS01 := Finset.sum_nonneg (fun h (_ : h ∈ Finset.range H) =>
        mul_nonneg (hκpos h) (hind01 (A 0 1 h) ω))
      have hS10 := Finset.sum_nonneg (fun h (_ : h ∈ Finset.range H) =>
        mul_nonneg (hκpos h) (hind01 (A 1 0 h) ω))
      simp only [hRHSdef]
      rw [hsplit]
      rcases Fin.exists_fin_two.mp ⟨arm β X ε W (m + 1) ω, rfl⟩ with ha | ha
      · -- arm 0 chosen: the gap is Z 1 0
        have hWr : ω ∈ Wr 1 0 := by
          simp only [hWrdef, Set.mem_ofPred_eq, dotProduct_sub, sub_nonneg]
          exact greedy_zero _ _ _ _ ((harm_eq ω).symm.trans ha)
        have := hslice 1 0 ha hWr (by
          simp only [hZdef, dotProduct_sub]
          rw [max_def]; split_ifs <;> [skip; skip] <;>
            first | (apply le_max_right) | (apply le_max_left) | skip
          all_goals (rw [le_max_iff]; first | (right; linarith) | (left; linarith)))
        rw [ha]; linarith
      · have hWr : ω ∈ Wr 0 1 := by
          simp only [hWrdef, Set.mem_ofPred_eq, dotProduct_sub, sub_nonneg]
          exact greedy_one _ _ _ _ ((harm_eq ω).symm.trans ha)
        have := hslice 0 1 ha hWr (by
          simp only [hZdef, dotProduct_sub]
          rw [max_def]; split_ifs <;> [skip; skip] <;>
            first | (apply le_max_right) | (apply le_max_left) | skip
          all_goals (rw [le_max_iff]; first | (right; linarith) | (left; linarith)))
        rw [ha]; linarith
    · -- outside the good event the regret is at most 2 x_max b_max
      have hRle : max (X (m + 1) ω ⬝ᵥ β 0) (X (m + 1) ω ⬝ᵥ β 1)
          - X (m + 1) ω ⬝ᵥ β (arm β X ε W (m + 1) ω) ≤ 2 * bmax * xmax := by
        rcases Fin.exists_fin_two.mp ⟨arm β X ε W (m + 1) ω, rfl⟩ with ha | ha <;>
          rw [ha] <;> (rw [max_def]; split_ifs <;> linarith)
      have hind : 1 ≤ (F 0)ᶜ.indicator (1 : Ω → ℝ) ω + (F 1)ᶜ.indicator (1 : Ω → ℝ) ω := by
        rw [not_and_or] at hF
        rcases hF with h | h
        · rw [Set.indicator_of_mem (show ω ∈ (F 0)ᶜ from h), Pi.one_apply]
          linarith [hind01 (F 1)ᶜ ω]
        · rw [Set.indicator_of_mem (show ω ∈ (F 1)ᶜ from h), Pi.one_apply]
          linarith [hind01 (F 0)ᶜ ω]
      simp only [hRHSdef]
      have := mul_le_mul_of_nonneg_left hind hbx
      linarith [hsum_nn ω]
  -- integrability and the value of the dominating integral
  have hI1 : ∀ s : Set Ω, MeasurableSet s → Integrable (s.indicator (1 : Ω → ℝ)) P :=
    fun s hs => (integrable_const (1 : ℝ)).indicator hs
  have hRHSint : Integrable RHS P :=
    (integrable_finsetSum _ (fun h _ => ((hI1 _ (hAm 0 1 h)).add (hI1 _ (hAm 1 0 h))).const_mul _)).add
      (((hI1 _ (hFm 0).compl).add (hI1 _ (hFm 1).compl)).const_mul _)
  have hR_le : instRegret β X ε W P (m + 1) ≤ ∫ ω, RHS ω ∂P := by
    unfold instRegret
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun ω => ?_)) hRHSint hpt
    rcases Fin.exists_fin_two.mp ⟨arm β X ε W (m + 1) ω, rfl⟩ with ha | ha <;>
      simp only [ha, Pi.zero_apply, sub_nonneg, le_max_left, le_max_right]
  have hf1 : Integrable (fun ω => ∑ h ∈ Finset.range H, κ h * ((A 0 1 h).indicator (1 : Ω → ℝ) ω
      + (A 1 0 h).indicator (1 : Ω → ℝ) ω)) P :=
    integrable_finsetSum _ (fun h _ => ((hI1 _ (hAm 0 1 h)).add (hI1 _ (hAm 1 0 h))).const_mul _)
  have hf2 : Integrable (fun ω => 2 * bmax * xmax * ((F 0)ᶜ.indicator (1 : Ω → ℝ) ω
      + (F 1)ᶜ.indicator (1 : Ω → ℝ) ω)) P :=
    ((hI1 _ (hFm 0).compl).add (hI1 _ (hFm 1).compl)).const_mul _
  have hRHSval : ∫ ω, RHS ω ∂P = ∑ h ∈ Finset.range H, κ h * (P.real (A 0 1 h) + P.real (A 1 0 h))
      + 2 * bmax * xmax * (P.real (F 0)ᶜ + P.real (F 1)ᶜ) := by
    calc ∫ ω, RHS ω ∂P
        = ∫ ω, ((∑ h ∈ Finset.range H, κ h * ((A 0 1 h).indicator (1 : Ω → ℝ) ω
            + (A 1 0 h).indicator (1 : Ω → ℝ) ω))
          + 2 * bmax * xmax * ((F 0)ᶜ.indicator (1 : Ω → ℝ) ω
            + (F 1)ᶜ.indicator (1 : Ω → ℝ) ω)) ∂P := rfl
      _ = ∫ ω, (∑ h ∈ Finset.range H, κ h * ((A 0 1 h).indicator (1 : Ω → ℝ) ω
            + (A 1 0 h).indicator (1 : Ω → ℝ) ω)) ∂P
          + ∫ ω, 2 * bmax * xmax * ((F 0)ᶜ.indicator (1 : Ω → ℝ) ω
            + (F 1)ᶜ.indicator (1 : Ω → ℝ) ω) ∂P := integral_add hf1 hf2
      _ = _ := by
          congr 1
          · rw [integral_finsetSum (f := fun h ω => κ h * ((A 0 1 h).indicator (1 : Ω → ℝ) ω
              + (A 1 0 h).indicator (1 : Ω → ℝ) ω)) _ (fun h _ =>
              ((hI1 _ (hAm 0 1 h)).add (hI1 _ (hAm 1 0 h))).const_mul _)]
            refine Finset.sum_congr rfl (fun h _ => ?_)
            rw [integral_const_mul, integral_add (hI1 _ (hAm 0 1 h)) (hI1 _ (hAm 1 0 h)),
              integral_indicator_one (hAm 0 1 h), integral_indicator_one (hAm 1 0 h)]
          · rw [integral_const_mul, integral_add (hI1 _ (hFm 0).compl) (hI1 _ (hFm 1).compl),
              integral_indicator_one (hFm 0).compl, integral_indicator_one (hFm 1).compl]
  -- independence of the fresh context from the past
  have hindX : Indep (filt X ε W m) (MeasurableSpace.comap (X (m + 1)) inferInstance) P := by
    have h := indep_filt P X ε W hXm hεm hWm hmodel.indep (m + 1) (by omega)
    rw [Nat.add_sub_cancel] at h
    refine indep_of_indep_of_le_right h ?_
    apply measurable_iff_comap_le.mp
    exact measurable_fst.comp (comap_measurable (fun ω => (X (m + 1) ω, W (m + 1) ω)))
  have hcard : ∀ j ω, (played β X ε W j m ω).card ≤ m := by
    intro j ω
    calc (played β X ε W j m ω).card ≤ (Finset.Icc 1 m).card := Finset.card_filter_le _ _
      _ = m := by simp
  -- the slice probabilities
  have hA_le : ∀ l i h, l ≠ i →
      P.real (A l i h) ≤ P.real (I l i h) * min 1 (4 * (d : ℝ) * Real.exp (-((h : ℝ) ^ 2))) := by
    intro l i h hli
    have hAI : P.real (A l i h) ≤ P.real (I l i h) :=
      measureReal_mono (fun ω hω => hω.1.1)
    rcases Nat.eq_zero_or_pos h with h0 | hpos
    · subst h0
      have : min 1 (4 * (d : ℝ) * Real.exp (-(((0 : ℕ) : ℝ) ^ 2))) = 1 := by
        simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
          neg_zero, Real.exp_zero, mul_one]
        exact min_eq_left (by linarith)
      rw [this, mul_one]; exact hAI
    · have hhR : (0 : ℝ) < h := by exact_mod_cast hpos
      set G : Fin 2 → Set Ω := fun j => {ω | δ * h ≤ l2norm (est β X ε W j m ω - β j)}
        with hGdef
      set B := (G 0 ∩ F 0) ∪ (G 1 ∩ F 1) with hBdef
      have hGF : ∀ j, MeasurableSet[filt X ε W m] (G j ∩ F j) := fun j =>
        (measurableSet_le measurable_const (measurable_l2norm.comp ((hestF j).sub_const _))).inter
          (measurableSet_le measurable_const (hlamF j))
      have hBF : MeasurableSet[filt X ε W m] B := (hGF 0).union (hGF 1)
      have hIX : MeasurableSet[MeasurableSpace.comap (X (m + 1)) inferInstance] (I l i h) :=
        ⟨{x | 2 * δ * xmax * h < x ⬝ᵥ (β l - β i) ∧ x ⬝ᵥ (β l - β i) ≤ κ h},
          (measurableSet_lt measurable_const
            (continuous_id.dotProduct continuous_const).measurable).inter
          (measurableSet_le (continuous_id.dotProduct continuous_const).measurable
            measurable_const), rfl⟩
      have hprod : P (B ∩ I l i h) = P B * P (I l i h) :=
        (Indep_iff _ _ _).mp hindX _ _ hBF hIX
      have hsub : A l i h ≤ᵐ[P] (B ∩ I l i h : Set Ω) := by
        filter_upwards [hXae] with ω hω hA
        refine ⟨?_, hA.1.1⟩
        have hw := wrong_implies (X (m + 1) ω) (est β X ε W l m ω) (est β X ε W i m ω)
          (β l) (β i) xmax (δ * h) hω hxmax (by
            have := hA.1.1.1
            simp only [hZdef] at this
            linarith) hA.1.2
        have hF0 := hA.2.1
        have hF1 := hA.2.2
        fin_cases l <;> fin_cases i
        · exact absurd rfl hli
        · rcases hw with hw | hw
          · exact Or.inl ⟨hw, hF0⟩
          · exact Or.inr ⟨hw, hF1⟩
        · rcases hw with hw | hw
          · exact Or.inr ⟨hw, hF1⟩
          · exact Or.inl ⟨hw, hF0⟩
        · exact absurd rfl hli
      have hAB : P.real (A l i h) ≤ P.real B * P.real (I l i h) := by
        have h1 := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
        rw [hprod, ENNReal.toReal_mul] at h1
        simpa [measureReal_def] using h1
      have hexp : C2 (lam0 / 4) d σ xmax * (m : ℝ) ^ 2 * (δ * h) ^ 2 / m = (h : ℝ) ^ 2 := by
        rw [mul_pow, hδsq, hc3def]
        unfold C2 C3
        field_simp
        ring
      have hG5 : ∀ j, P.real (G j ∩ F j) ≤ 2 * d * Real.exp (-((h : ℝ) ^ 2)) := by
        intro j
        have h5 := lemma_5 P (by omega : 1 ≤ d) μ X ε W σ hσ β xmax bmax hmodel hA1 j m hm1
          (lam0 / 4) (δ * h) (by positivity) (by positivity) m (hcard j)
        rw [hexp] at h5
        exact h5
      have hB1 : P.real B ≤ 1 := measureReal_le_one
      have hB2 : P.real B ≤ 4 * d * Real.exp (-((h : ℝ) ^ 2)) := by
        calc P.real B ≤ P.real (G 0 ∩ F 0) + P.real (G 1 ∩ F 1) := measureReal_union_le _ _
          _ ≤ _ := by linarith [hG5 0, hG5 1]
      calc P.real (A l i h) ≤ P.real B * P.real (I l i h) := hAB
        _ ≤ min 1 (4 * (d : ℝ) * Real.exp (-((h : ℝ) ^ 2))) * P.real (I l i h) :=
          mul_le_mul_of_nonneg_right (le_min hB1 hB2) measureReal_nonneg
        _ = _ := mul_comm _ _
  -- the margin condition
  have hI_sum : ∀ h, P.real (I 0 1 h) + P.real (I 1 0 h) ≤ C0 * κ h := by
    intro h
    have hκ : 0 < κ h := by simp only [hκdef]; positivity
    have h2dx : 0 ≤ 2 * δ * xmax * h := by positivity
    have hZneg : ∀ ω, Z 1 0 ω = -Z 0 1 ω := fun ω => by
      simp only [hZdef, dotProduct_sub]; ring
    have hdisj : Disjoint (I 0 1 h) (I 1 0 h) := by
      rw [Set.disjoint_left]
      intro ω h1 h2
      have a1 := h1.1; have a2 := h2.1
      rw [hZneg] at a2
      linarith
    set S : Set (Fin d → ℝ) := {x | 0 < |x ⬝ᵥ (β 0 - β 1)| ∧ |x ⬝ᵥ (β 0 - β 1)| ≤ κ h} with hS
    have hSm : MeasurableSet S := by
      have hc : Measurable fun x : Fin d → ℝ => |x ⬝ᵥ (β 0 - β 1)| :=
        (continuous_abs.comp (continuous_id.dotProduct continuous_const)).measurable
      exact (measurableSet_lt measurable_const hc).inter (measurableSet_le hc measurable_const)
    have hsubS : I 0 1 h ∪ I 1 0 h ⊆ X (m + 1) ⁻¹' S := by
      intro ω hω
      rcases hω with h1 | h2
      · have a1 := h1.1; have b1 := h1.2
        simp only [hZdef] at a1 b1
        refine ⟨?_, ?_⟩ <;> rw [abs_of_pos (by linarith)] <;> linarith
      · have a2 := h2.1; have b2 := h2.2
        rw [hZneg] at a2 b2
        simp only [hZdef] at a2 b2
        refine ⟨?_, ?_⟩ <;> rw [abs_of_neg (by linarith)] <;> linarith
    have hμS : μ S ≤ ENNReal.ofReal (C0 * κ h) := hA2.2 0 1 (by decide) (κ h) hκ
    have hPS : P (X (m + 1) ⁻¹' S) = μ S := by
      rw [← Measure.map_apply (hXm _) hSm, hmodel.law_X (m + 1) (by omega)]
    rw [← measureReal_union hdisj (hIm 1 0 h)]
    calc P.real (I 0 1 h ∪ I 1 0 h) ≤ P.real (X (m + 1) ⁻¹' S) := measureReal_mono hsubS
      _ = (μ S).toReal := by rw [measureReal_def, hPS]
      _ ≤ C0 * κ h := ENNReal.toReal_le_of_le_ofReal (by positivity) hμS
  -- assemble
  have hmain : ∑ h ∈ Finset.range H, κ h * (P.real (A 0 1 h) + P.real (A 1 0 h))
      ≤ 4 * C0 * δ ^ 2 * xmax ^ 2 * (Cbar d * Real.log d ^ (3 / 2 : ℝ)) := by
    calc ∑ h ∈ Finset.range H, κ h * (P.real (A 0 1 h) + P.real (A 1 0 h))
        ≤ ∑ h ∈ Finset.range H, κ h * (min 1 (4 * (d : ℝ) * Real.exp (-((h : ℝ) ^ 2)))
            * (C0 * κ h)) := by
          refine Finset.sum_le_sum (fun h _ => mul_le_mul_of_nonneg_left ?_ (hκpos h))
          have h1 := hA_le 0 1 h (by decide)
          have h2 := hA_le 1 0 h (by decide)
          have h3 := hI_sum h
          have hmin : 0 ≤ min 1 (4 * (d : ℝ) * Real.exp (-((h : ℝ) ^ 2))) :=
            le_min zero_le_one (by positivity)
          have := mul_le_mul_of_nonneg_left h3 hmin
          nlinarith
      _ = 4 * C0 * δ ^ 2 * xmax ^ 2 * ∑ h ∈ Finset.range H,
            ((h : ℝ) + 1) ^ 2 * min 1 (4 * d * Real.exp (-((h : ℝ) ^ 2))) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun h _ => ?_)
          simp only [hκdef]; ring
      _ ≤ 4 * C0 * δ ^ 2 * xmax ^ 2 * (Cbar d * Real.log d ^ (3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (sum_bound d hd H) (by positivity)
  have hF2 : P.real (F 0)ᶜ + P.real (F 1)ᶜ
      ≤ 2 * max (P (F 0)ᶜ).toReal (P (F 1)ᶜ).toReal := by
    simp only [measureReal_def]
    linarith [le_max_left (P (F 0)ᶜ).toReal (P (F 1)ᶜ).toReal,
      le_max_right (P (F 0)ᶜ).toReal (P (F 1)ᶜ).toReal]
  have hcoef : 4 * C0 * δ ^ 2 * xmax ^ 2 * (Cbar d * Real.log d ^ (3 / 2 : ℝ))
      = 4 * C0 * Cbar d * xmax ^ 2 * Real.log d ^ (3 / 2 : ℝ) / c3 * (1 / (m : ℝ)) := by
    rw [hδsq]; field_simp
  have := mul_le_mul_of_nonneg_left hF2 hbx
  calc instRegret β X ε W P (m + 1) ≤ _ := hR_le
    _ = _ := hRHSval
    _ ≤ _ := by rw [← hcoef]; linarith
