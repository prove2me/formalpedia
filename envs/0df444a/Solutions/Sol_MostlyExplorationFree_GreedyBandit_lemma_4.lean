-- Prove2me | solution 1 for MostlyExplorationFree.GreedyBandit.lemma_4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T19:00:51.123989+00:00
-- url     : https://prove2.me/submissions/07476e7f-3639-4a1f-af72-d004e5ac70a9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MostlyExplorationFree_GreedyBandit_Model
import Theorems.Thm_MostlyExplorationFree_GreedyBandit_lemma_9

open Matrix MeasureTheory ProbabilityTheory

namespace MEFLemma4Aux
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


section Half
variable {d : ℕ}

/-- The truncated integrand `𝕀{π = i, ‖x‖ ≤ x_max} x_a x_b` as a function of the estimates
`(b₀, b₁)` and the fresh context/coin `(x, w)`. -/
noncomputable def phiG (i : Fin 2) (xmax : ℝ) (a b : Fin d)
    (p : ((Fin d → ℝ) × (Fin d → ℝ)) × ((Fin d → ℝ) × Bool)) : ℝ :=
  if greedyChoice p.2.1 p.1.1 p.1.2 p.2.2 = i ∧ l2norm p.2.1 ≤ xmax then p.2.1 a * p.2.1 b else 0

theorem measurable_l2norm : Measurable (fun x : Fin d → ℝ => l2norm x) :=
  (Real.continuous_sqrt.comp (continuous_id.dotProduct continuous_id)).measurable

theorem measurable_phiG (i : Fin 2) (xmax : ℝ) (a b : Fin d) :
    Measurable (phiG (d := d) i xmax a b) := by
  unfold phiG
  refine Measurable.ite ?_ ?_ measurable_const
  · refine MeasurableSet.inter ?_ ?_
    · exact (measurable_greedyChoice _ _ _ _ (measurable_fst.comp measurable_snd)
        (measurable_fst.comp measurable_fst) (measurable_snd.comp measurable_fst)
        (measurable_snd.comp measurable_snd)) (measurableSet_singleton i)
    · exact measurableSet_le (measurable_l2norm.comp (measurable_fst.comp measurable_snd))
        measurable_const
  · exact ((measurable_pi_apply a).comp (measurable_fst.comp measurable_snd)).mul
      ((measurable_pi_apply b).comp (measurable_fst.comp measurable_snd))

theorem abs_phiG_le (i : Fin 2) (xmax : ℝ) (hxmax : 0 < xmax) (a b : Fin d) (p) :
    |phiG i xmax a b p| ≤ xmax ^ 2 := by
  unfold phiG
  split_ifs with h
  · exact (abs_mul_le_dot_self _ a b).trans (dot_self_le_of_l2norm h.2)
  · simp only [abs_zero]; positivity

theorem greedy_pt (i : Fin 2) (b0 b1 x : Fin d → ℝ) (w : Bool) (q : ℝ) (hq : 0 ≤ q)
    (N : Prop) [Decidable N] :
    (if 0 < x ⬝ᵥ (if i = 0 then b0 - b1 else b1 - b0) ∧ N then q else 0)
      + (if x ⬝ᵥ (if i = 0 then b0 - b1 else b1 - b0) = 0 ∧ N then q else 0)
        * (if w = decide (i = 0) then (1:ℝ) else 0)
      ≤ if greedyChoice x b0 b1 w = i ∧ N then q else 0 := by
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, if_true, dotProduct_sub, decide_true]
    unfold greedyChoice
    by_cases hN : N
    · by_cases h1 : x ⬝ᵥ b1 < x ⬝ᵥ b0
      · have : ¬ (x ⬝ᵥ b0 - x ⬝ᵥ b1 = 0) := by linarith
        simp [h1, hN, this]
      · by_cases h2 : x ⬝ᵥ b0 < x ⬝ᵥ b1
        · have : ¬ (0 < x ⬝ᵥ b0 - x ⬝ᵥ b1) := by linarith
          have h3 : ¬ (x ⬝ᵥ b0 - x ⬝ᵥ b1 = 0) := by linarith
          simp [h1, h2, hN, this, h3]
        · have h3 : x ⬝ᵥ b0 - x ⬝ᵥ b1 = 0 := by linarith
          cases w <;> simp [h1, h2, hN, h3]
    · simp [hN]
  · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, if_false, dotProduct_sub, decide_false]
    unfold greedyChoice
    by_cases hN : N
    · by_cases h1 : x ⬝ᵥ b1 < x ⬝ᵥ b0
      · have : ¬ (0 < x ⬝ᵥ b1 - x ⬝ᵥ b0) := by linarith
        have h3 : ¬ (x ⬝ᵥ b1 - x ⬝ᵥ b0 = 0) := by linarith
        simp [h1, hN, this, h3]
      · by_cases h2 : x ⬝ᵥ b0 < x ⬝ᵥ b1
        · have : ¬ (x ⬝ᵥ b1 - x ⬝ᵥ b0 = 0) := by linarith
          simp [h1, h2, hN, this]
        · have h3 : x ⬝ᵥ b1 - x ⬝ᵥ b0 = 0 := by linarith
          cases w <;> simp [h1, h2, hN, h3]
    · simp [hN]

end Half


theorem halfspace_lower {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    [IsProbabilityMeasure P] (μ : Measure (Fin d → ℝ))
    (Xk : Ω → Fin d → ℝ) (Wk : Ω → Bool) (hXm : Measurable Xk) (hWm : Measurable Wk)
    (hXW : IndepFun Xk Wk P) (hlaw : P.map Xk = μ) (hfair : P {ω | Wk ω = true} = 2⁻¹)
    (β : Fin 2 → Fin d → ℝ) (xmax bmax lam0 : ℝ)
    (hA1 : ParameterSet μ β xmax bmax) (hA3 : CovariateDiversity μ lam0) (i : Fin 2)
    (b0 b1 : Fin d → ℝ) (v : Fin d → ℝ) (hv : v ⬝ᵥ v = 1) :
    lam0 / 2 ≤ v ⬝ᵥ (Matrix.of (fun a b =>
      ∫ ω', phiG i xmax a b ((b0, b1), (Xk ω', Wk ω')) ∂P) *ᵥ v) := by
  obtain ⟨hxmax, hXb, -⟩ := hA1
  have hμ : IsProbabilityMeasure μ := hlaw ▸ Measure.isProbabilityMeasure_map hXm.aemeasurable
  set u : Fin d → ℝ := if i = 0 then b0 - b1 else b1 - b0 with hu
  set wi : Bool := decide (i = 0) with hwi
  have hphi_int : ∀ a b, Integrable
      (fun ω' => phiG i xmax a b ((b0, b1), (Xk ω', Wk ω'))) P := fun a b =>
    Integrable.of_bound ((measurable_phiG i xmax a b).comp
      (measurable_const.prodMk (hXm.prodMk hWm))).aestronglyMeasurable (xmax ^ 2)
      (Filter.Eventually.of_forall (fun ω' => by
        rw [Real.norm_eq_abs]; exact abs_phiG_le i xmax hxmax a b _))
  rw [quad_integral P v _ hphi_int]
  have hQ : ∀ ω', ∑ a, v a * ∑ b, phiG i xmax a b ((b0, b1), (Xk ω', Wk ω')) * v b
      = if greedyChoice (Xk ω') b0 b1 (Wk ω') = i ∧ l2norm (Xk ω') ≤ xmax
        then (v ⬝ᵥ Xk ω') ^ 2 else 0 := by
    intro ω'
    unfold phiG
    split_ifs with h
    · exact quad_sum_eq _ _
    · simp
  simp_rw [hQ]
  -- the comparison functions
  set R1 : (Fin d → ℝ) → ℝ := fun x =>
    if 0 < x ⬝ᵥ u ∧ l2norm x ≤ xmax then (v ⬝ᵥ x) ^ 2 else 0 with hR1
  set R2 : (Fin d → ℝ) → ℝ := fun x =>
    if x ⬝ᵥ u = 0 ∧ l2norm x ≤ xmax then (v ⬝ᵥ x) ^ 2 else 0 with hR2
  set Iw : Bool → ℝ := fun w => if w = wi then (1:ℝ) else 0 with hIw
  have hdotm : Measurable fun x : Fin d → ℝ => x ⬝ᵥ u :=
    (continuous_id.dotProduct continuous_const).measurable
  have hvxm : Measurable fun x : Fin d → ℝ => (v ⬝ᵥ x) ^ 2 :=
    ((continuous_const.dotProduct continuous_id).pow 2).measurable
  have hnormS : MeasurableSet {x : Fin d → ℝ | l2norm x ≤ xmax} :=
    measurableSet_le measurable_l2norm measurable_const
  have hR1m : Measurable R1 :=
    Measurable.ite ((measurableSet_lt measurable_const hdotm).inter hnormS) hvxm measurable_const
  have hR2m : Measurable R2 :=
    Measurable.ite (((measurableSet_singleton (0:ℝ)).preimage hdotm).inter hnormS) hvxm
      measurable_const
  have hIwm : Measurable Iw := measurable_of_countable _
  have hbd : ∀ x : Fin d → ℝ, l2norm x ≤ xmax → (v ⬝ᵥ x) ^ 2 ≤ xmax ^ 2 := by
    intro x hx
    have := dot_sq_le v x
    rw [hv, one_mul] at this
    exact this.trans (dot_self_le_of_l2norm hx)
  have hR1b : ∀ x, |R1 x| ≤ xmax ^ 2 := by
    intro x; simp only [hR1]; split_ifs with h
    · rw [abs_of_nonneg (sq_nonneg _)]; exact hbd x h.2
    · simp only [abs_zero]; positivity
  have hR2b : ∀ x, |R2 x| ≤ xmax ^ 2 := by
    intro x; simp only [hR2]; split_ifs with h
    · rw [abs_of_nonneg (sq_nonneg _)]; exact hbd x h.2
    · simp only [abs_zero]; positivity
  have hIwb : ∀ w, |Iw w| ≤ 1 := by intro w; simp only [hIw]; split_ifs <;> simp
  have bint : ∀ (f : Ω → ℝ) (C : ℝ), Measurable f → (∀ ω, |f ω| ≤ C) → Integrable f P :=
    fun f C hf hC => Integrable.of_bound hf.aestronglyMeasurable C
      (Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs]; exact hC ω))
  have hI1 : Integrable (fun ω => R1 (Xk ω)) P := bint _ _ (hR1m.comp hXm) (fun ω => hR1b _)
  have hI2 : Integrable (fun ω => R2 (Xk ω)) P := bint _ _ (hR2m.comp hXm) (fun ω => hR2b _)
  have hI2w : Integrable (fun ω => R2 (Xk ω) * Iw (Wk ω)) P :=
    bint _ (xmax ^ 2 * 1) ((hR2m.comp hXm).mul (hIwm.comp hWm))
      (fun ω => by rw [abs_mul]; exact mul_le_mul (hR2b _) (hIwb _) (abs_nonneg _) (by positivity))
  have hQm : Measurable fun ω => (if greedyChoice (Xk ω) b0 b1 (Wk ω) = i ∧ l2norm (Xk ω) ≤ xmax
      then (v ⬝ᵥ Xk ω) ^ 2 else 0) := by
    refine Measurable.ite ?_ (hvxm.comp hXm) measurable_const
    exact ((measurable_greedyChoice _ _ _ _ hXm measurable_const measurable_const hWm)
      (measurableSet_singleton i)).inter (hnormS.preimage hXm)
  have hQint : Integrable (fun ω => (if greedyChoice (Xk ω) b0 b1 (Wk ω) = i ∧
      l2norm (Xk ω) ≤ xmax then (v ⬝ᵥ Xk ω) ^ 2 else 0)) P := by
    refine bint _ (xmax ^ 2) hQm (fun ω => ?_)
    split_ifs with h
    · rw [abs_of_nonneg (sq_nonneg _)]; exact hbd _ h.2
    · simp only [abs_zero]; positivity
  -- Step 1: pointwise comparison.
  have hstep1 : ∫ ω, (R1 (Xk ω) + R2 (Xk ω) * Iw (Wk ω)) ∂P
      ≤ ∫ ω, (if greedyChoice (Xk ω) b0 b1 (Wk ω) = i ∧ l2norm (Xk ω) ≤ xmax
        then (v ⬝ᵥ Xk ω) ^ 2 else 0) ∂P := by
    refine integral_mono (hI1.add hI2w) hQint (fun ω => ?_)
    exact greedy_pt i b0 b1 (Xk ω) (Wk ω) _ (sq_nonneg _) _
  -- Step 2: independence of the coin.
  have hIwint : ∫ ω, Iw (Wk ω) ∂P = 1 / 2 := by
    have h1 : (fun ω => Iw (Wk ω)) = {ω | Wk ω = wi}.indicator (1 : Ω → ℝ) := by
      funext ω; simp only [hIw, Set.indicator, Set.mem_ofPred_eq, Pi.one_apply]
    have hm : MeasurableSet {ω | Wk ω = wi} := hWm (measurableSet_singleton wi)
    rw [h1, integral_indicator_one hm]
    have hprob : P {ω | Wk ω = wi} = 2⁻¹ := by
      cases hc : wi
      · have hm' : MeasurableSet {ω | Wk ω = true} := hWm (measurableSet_singleton true)
        have : {ω | Wk ω = false} = {ω | Wk ω = true}ᶜ := by
          ext ω; simp
        rw [this, prob_compl_eq_one_sub hm', hfair, ENNReal.one_sub_inv_two]
      · exact hfair
    rw [measureReal_def, hprob]
    simp
  have hstep2 : ∫ ω, (R1 (Xk ω) + R2 (Xk ω) * Iw (Wk ω)) ∂P
      = ∫ ω, R1 (Xk ω) ∂P + (∫ ω, R2 (Xk ω) ∂P) * (1 / 2) := by
    rw [integral_add hI1 hI2w, ← hIwint]
    congr 1
    exact (hXW.comp hR2m hIwm).integral_fun_mul_eq_mul_integral
      (hR2m.comp hXm).aestronglyMeasurable (hIwm.comp hWm).aestronglyMeasurable
  -- Step 3: back to the context law and the half-space second moment.
  set S : Set (Fin d → ℝ) := {y | 0 ≤ y ⬝ᵥ u} with hS
  have hSm : MeasurableSet S := measurableSet_le measurable_const hdotm
  have hsum12 : ∫ ω, R1 (Xk ω) ∂P + ∫ ω, R2 (Xk ω) ∂P
      = ∫ y, S.indicator (fun y => (v ⬝ᵥ y) ^ 2) y ∂μ := by
    rw [← integral_add hI1 hI2]
    have hmap : ∫ ω, (R1 (Xk ω) + R2 (Xk ω)) ∂P = ∫ y, (R1 y + R2 y) ∂μ := by
      rw [← hlaw, integral_map (f := fun y => R1 y + R2 y) hXm.aemeasurable
        (hR1m.add hR2m).aestronglyMeasurable]
    rw [hmap]
    refine integral_congr_ae ?_
    filter_upwards [hXb] with y hy
    simp only [hR1, hR2, hS, Set.indicator, Set.mem_ofPred_eq, Pi.add_apply]
    by_cases h1 : 0 < y ⬝ᵥ u
    · have h2 : ¬ y ⬝ᵥ u = 0 := by linarith
      simp [h1, h2, hy, h1.le]
    · by_cases h2 : y ⬝ᵥ u = 0
      · simp [h1, h2, hy]
      · have h3 : ¬ 0 ≤ y ⬝ᵥ u := by
          intro h; rcases h.lt_or_eq with h | h
          · exact h1 h
          · exact h2 h.symm
        simp [h1, h2, h3]
  have hgint : ∀ a b, Integrable (fun y => S.indicator (fun y : Fin d → ℝ => y a * y b) y) μ := by
    intro a b
    refine Integrable.of_bound ((((measurable_pi_apply a).mul
      (measurable_pi_apply b)).indicator hSm).aestronglyMeasurable) (xmax ^ 2) ?_
    filter_upwards [hXb] with y hy
    rw [Real.norm_eq_abs]
    by_cases hyS : y ∈ S
    · rw [Set.indicator_of_mem hyS]
      exact (abs_mul_le_dot_self y a b).trans (dot_self_le_of_l2norm hy)
    · rw [Set.indicator_of_notMem hyS, abs_zero]; positivity
  have hM : v ⬝ᵥ (halfSpaceSecondMoment μ u *ᵥ v)
      = ∫ y, S.indicator (fun y => (v ⬝ᵥ y) ^ 2) y ∂μ := by
    unfold halfSpaceSecondMoment
    rw [quad_integral μ v _ hgint]
    congr 1; funext y
    by_cases hyS : y ∈ S
    · simp only [Set.indicator_of_mem hyS]
      exact quad_sum_eq v y
    · simp [Set.indicator_of_notMem hyS]
  have hlam := rayleigh_ge_of_lambdaMin _ lam0 hA3.1 (hA3.2 u) v hv
  rw [hM, ← hsum12] at hlam
  have hR1nn : 0 ≤ ∫ ω, R1 (Xk ω) ∂P := integral_nonneg (fun ω => by
    simp only [hR1]; split_ifs <;> positivity)
  linarith

end MEFLemma4Aux

open MostlyExplorationFree.GreedyBandit MEFLemma4Aux

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d : ℕ} (hd : 1 ≤ d)
    (μ : Measure (Fin d → ℝ)) (X : ℕ → Ω → Fin d → ℝ) (ε : Fin 2 → ℕ → Ω → ℝ)
    (W : ℕ → Ω → Bool) (σ : ℝ) (β : Fin 2 → Fin d → ℝ) (xmax bmax lam0 : ℝ)
    (hmodel : IsGreedyModel P μ X ε W σ) (hA1 : ParameterSet μ β xmax bmax)
    (hA3 : CovariateDiversity μ lam0) (i : Fin 2) (t : ℕ) (ht : 1 ≤ t) :
    1 - Real.exp (Real.log d - C1 lam0 xmax * t)
      ≤ (P {ω | lam0 * t / 4 ≤ lambdaMin (gram β X ε W i t ω)}).toReal := by
  have hP := hmodel.isProbability
  have hxmax : 0 < xmax := hA1.1
  have hXb := hA1.2.1
  have hlam0 : 0 < lam0 := hA3.1
  have hXm := hmodel.measurable_X
  have hεm := hmodel.measurable_ε
  have hWm := hmodel.measurable_W
  -- The filtration `H_k` of contexts, noises and coins up to time `k`.
  let ℱ : Filtration ℕ ‹MeasurableSpace Ω› :=
    ⟨filt X ε W, filt_mono X ε W, filt_le X ε W hXm hεm hWm⟩
  have hℱ : ∀ k, ℱ k = filt X ε W k := fun k => rfl
  -- The summands `X_k X_kᵀ 𝕀{π_k = i}` of the sample covariance matrix.
  let Xk : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ := fun k ω =>
    if arm β X ε W k ω = i then vecMulVec (X k ω) (X k ω) else 0
  have hXkae : ∀ k, 1 ≤ k → ∀ᵐ ω ∂P, l2norm (X k ω) ≤ xmax := fun k hk => by
    have h := hXb
    rw [← hmodel.law_X k hk] at h
    exact ae_of_ae_map (hXm k).aemeasurable h
  have harmF : ∀ k, 1 ≤ k → Measurable[filt X ε W k] (arm β X ε W k) := by
    intro k hk
    exact measurable_arm_le (mΩ := filt X ε W k) β X ε W k
      (fun s hs => measurable_X_filt X ε W (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hs).2)
      (fun s hs => measurable_W_filt X ε W (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hs).2)
      (fun j s hs => measurable_ε_filt X ε W j (Finset.mem_Icc.mp hs).1
        (by have := (Finset.mem_Icc.mp hs).2; omega)) k (Finset.mem_Icc.mpr ⟨hk, le_rfl⟩)
  have hentry_eq : ∀ k ω a b, Xk k ω a b = if arm β X ε W k ω = i then X k ω a * X k ω b else 0 := by
    intro k ω a b
    simp only [Xk]
    split_ifs <;> simp [vecMulVec_apply]
  have hadapted : ∀ k ∈ Finset.Icc 1 t, ∀ a b,
      StronglyMeasurable[ℱ k] (fun ω => Xk k ω a b) := by
    intro k hk a b
    have hk1 := (Finset.mem_Icc.mp hk).1
    have hXk : Measurable[filt X ε W k] (X k) := measurable_X_filt X ε W hk1 le_rfl
    have hm : Measurable[filt X ε W k] (fun ω => Xk k ω a b) := by
      simp_rw [hentry_eq]
      exact Measurable.ite ((harmF k hk1) (measurableSet_singleton i))
        (((measurable_pi_apply a).comp hXk).mul ((measurable_pi_apply b).comp hXk))
        measurable_const
    exact hm.stronglyMeasurable
  have hpsd : ∀ k ∈ Finset.Icc 1 t, ∀ᵐ ω ∂P, (Xk k ω).PosSemidef := by
    intro k _
    refine Filter.Eventually.of_forall (fun ω => ?_)
    simp only [Xk]
    split_ifs
    · simpa using posSemidef_vecMulVec_self_star (X k ω)
    · exact PosSemidef.zero
  have hmax : ∀ k ∈ Finset.Icc 1 t, ∀ᵐ ω ∂P, lambdaMax (Xk k ω) ≤ xmax ^ 2 := by
    intro k hk
    filter_upwards [hXkae k (Finset.mem_Icc.mp hk).1] with ω hω
    refine lambdaMax_le_of hd _ _ (fun v hv => ?_)
    simp only [Xk]
    split_ifs
    · rw [rayleigh_vecMulVec]
      have := dot_sq_le v (X k ω)
      rw [hv, one_mul] at this
      exact this.trans (dot_self_le_of_l2norm hω)
    · simp only [zero_mulVec, dotProduct_zero]; positivity
  -- The conditional covariance of each summand dominates `λ₀/2` (covariate diversity + fair coin).
  have hcond : ∀ k ∈ Finset.Icc 1 t, ∀ᵐ ω ∂P, ∀ v : Fin d → ℝ, v ⬝ᵥ v = 1 →
      lam0 / 2 ≤ v ⬝ᵥ (condExpMatrix (filt X ε W (k - 1)) P (Xk k) ω *ᵥ v) := by
    intro k hk
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by have := (Finset.mem_Icc.mp hk).1; omega⟩
    rw [Nat.add_sub_cancel]
    have hXn : ∀ s ∈ Finset.Icc 1 n, Measurable[filt X ε W n] (X s) := fun s hs =>
      measurable_X_filt X ε W (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hs).2
    have hWn : ∀ s ∈ Finset.Icc 1 n, Measurable[filt X ε W n] (W s) := fun s hs =>
      measurable_W_filt X ε W (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hs).2
    have hεn : ∀ j, ∀ s ∈ Finset.Icc 1 n, Measurable[filt X ε W n] (ε j s) := fun j s hs =>
      measurable_ε_filt X ε W j (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hs).2
    set B : Ω → (Fin d → ℝ) × (Fin d → ℝ) := fun ω =>
      (estOf β (fun s => X s ω) (fun j s => ε j s ω)
        (fun s => if 1 ≤ s ∧ s < n + 1 then arm β X ε W s ω else 0) 0 n,
       estOf β (fun s => X s ω) (fun j s => ε j s ω)
        (fun s => if 1 ≤ s ∧ s < n + 1 then arm β X ε W s ω else 0) 1 n) with hB
    have hBm : Measurable[filt X ε W n] B :=
      (measurable_est_le (mΩ := filt X ε W n) β X ε W n hXn hWn hεn 0).prodMk
        (measurable_est_le (mΩ := filt X ε W n) β X ε W n hXn hWn hεn 1)
    set Z : Ω → (Fin d → ℝ) × Bool := fun ω => (X (n + 1) ω, W (n + 1) ω) with hZ
    have hZm : Measurable Z := (hXm _).prodMk (hWm _)
    have hind := indep_filt P X ε W hXm hεm hWm hmodel.indep (n + 1) (by omega)
    rw [Nat.add_sub_cancel] at hind
    have hentry : ∀ a b, condExp (filt X ε W n) P (fun ω => Xk (n + 1) ω a b)
        =ᵐ[P] fun ω => ∫ ω', phiG i xmax a b (B ω, Z ω') ∂P := by
      intro a b
      have hae : (fun ω => Xk (n + 1) ω a b) =ᵐ[P] fun ω => phiG i xmax a b (B ω, Z ω) := by
        filter_upwards [hXkae (n + 1) (by omega)] with ω hω
        rw [hentry_eq]
        simp only [phiG, hB, hZ, hω, and_true]
        rw [arm_eq_greedy β X ε W (n + 1) ω, Nat.add_sub_cancel]
      refine (condExp_congr_ae hae).trans ?_
      exact condExp_indep_comp (filt_le X ε W hXm hεm hWm n) P B hBm Z hZm hind
        (phiG i xmax a b) (measurable_phiG i xmax a b) (xmax ^ 2)
        (abs_phiG_le i xmax hxmax a b)
    have hall : ∀ᵐ ω ∂P, ∀ a b, condExpMatrix (filt X ε W n) P (Xk (n + 1)) ω a b
        = ∫ ω', phiG i xmax a b (B ω, Z ω') ∂P := by
      rw [ae_all_iff]; intro a
      rw [ae_all_iff]; intro b
      exact hentry a b
    have hXW : IndepFun (X (n + 1)) (W (n + 1)) P := by
      rw [IndepFun_iff_Indep]
      exact hmodel.indep.indep (i := Sum.inl (Sum.inl n)) (j := Sum.inr n) (by simp)
    filter_upwards [hall] with ω hω v hv
    have hmat : condExpMatrix (filt X ε W n) P (Xk (n + 1)) ω = Matrix.of (fun a b =>
        ∫ ω', phiG i xmax a b (((B ω).1, (B ω).2), (X (n + 1) ω', W (n + 1) ω')) ∂P) := by
      ext a b
      rw [hω a b]
      rfl
    rw [hmat]
    exact halfspace_lower P μ (X (n + 1)) (W (n + 1)) (hXm _) (hWm _) hXW
      (hmodel.law_X _ (by omega)) (hmodel.fair_W _ (by omega)) β xmax bmax lam0 hA1 hA3 i
      (B ω).1 (B ω).2 v hv
  -- Apply the matrix Chernoff bound (Lemma 9) with `μ = λ₀t/2`, `γ = 1/2`, `R = x_max²`.
  have h9 := lemma_9 P hd ℱ t Xk (xmax ^ 2) (by positivity) hadapted hpsd hmax
    (lam0 * t / 2) (1 / 2) (by positivity) (by norm_num) (by norm_num)
  have hsumX : ∀ ω, ∑ k ∈ Finset.Icc 1 t, Xk k ω = gram β X ε W i t ω := by
    intro ω
    simp only [Xk, MostlyExplorationFree.GreedyBandit.gram, gramOf, playedOf, Finset.sum_filter]
  have hWlow : ∀ᵐ ω ∂P, lam0 * t / 2
      ≤ lambdaMin (∑ k ∈ Finset.Icc 1 t, condExpMatrix (ℱ (k - 1)) P (Xk k) ω) := by
    filter_upwards [(Filter.eventually_all_finset _).mpr hcond] with ω hω
    refine le_lambdaMin_of hd _ _ (fun v hv => ?_)
    rw [sum_mulVec, dotProduct_sum]
    calc lam0 * t / 2 = ∑ k ∈ Finset.Icc 1 t, lam0 / 2 := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring
      _ ≤ _ := Finset.sum_le_sum (fun k hk => hω k hk v hv)
  have hsub : P {ω | lambdaMin (gram β X ε W i t ω) < lam0 * t / 4}
      ≤ P {ω | lambdaMin (∑ k ∈ Finset.Icc 1 t, Xk k ω) ≤ (1 - 1 / 2) * (lam0 * t / 2) ∧
        lam0 * t / 2 ≤ lambdaMin (∑ k ∈ Finset.Icc 1 t,
          condExpMatrix (ℱ (k - 1)) P (Xk k) ω)} := by
    refine measure_mono_ae ?_
    filter_upwards [hWlow] with ω hω
    intro (hlt : lambdaMin (gram β X ε W i t ω) < lam0 * t / 4)
    show _ ∧ _
    rw [hsumX]
    exact ⟨by linarith, hω⟩
  have hsubR := ENNReal.toReal_mono (measure_ne_top _ _) hsub
  -- Measurability of the event, to pass to the complement.
  have hlm : Measurable fun ω => lambdaMin (gram β X ε W i t ω) :=
    meas_of_matrix_cont _ continuous_lambdaMin _
      (measurable_gramOf_entry' X (fun ω s => arm β X ε W s ω) i t (fun s _ => hXm s)
        (fun s hs => measurable_arm_le β X ε W t (fun s _ => hXm s) (fun s _ => hWm s)
          (fun j s _ => hεm j s) s hs))
  set S := {ω | lam0 * t / 4 ≤ lambdaMin (gram β X ε W i t ω)} with hS
  have hSm : MeasurableSet S := measurableSet_le measurable_const hlm
  have hc := measure_add_measure_compl (μ := P) hSm
  rw [measure_univ] at hc
  have hcompl : Sᶜ = {ω | lambdaMin (gram β X ε W i t ω) < lam0 * t / 4} := by
    ext ω; simp [hS, not_le]
  have hsum : (P S).toReal + (P Sᶜ).toReal = 1 := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), hc]
    simp
  rw [hcompl] at hsum
  -- The Chernoff exponent.
  have hexp : (d : ℝ) * (Real.exp (-(1 / 2 : ℝ)) / (1 - 1 / 2 : ℝ) ^ (1 - 1 / 2 : ℝ))
      ^ (lam0 * t / 2 / xmax ^ 2) ≤ Real.exp (Real.log d - C1 lam0 xmax * t) := by
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
    have hhalf : (1 - 1 / 2 : ℝ) ^ (1 - 1 / 2 : ℝ) = Real.exp (-(Real.log 2) / 2) := by
      rw [Real.rpow_def_of_pos (by norm_num)]
      congr 1
      rw [show (1 - 1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.log_inv]
      ring
    rw [hhalf, ← Real.exp_sub, ← Real.exp_mul,
      show Real.log d - C1 lam0 xmax * t = Real.log d + (-(C1 lam0 xmax * t)) by ring,
      Real.exp_add, Real.exp_log hdpos]
    apply mul_le_mul_of_nonneg_left _ hdpos.le
    apply Real.exp_le_exp.mpr
    have hl2 := Real.log_two_lt_d9
    have hK : 0 ≤ lam0 * t / xmax ^ 2 := by positivity
    unfold C1
    have e1 : (-(1 / 2 : ℝ) - -Real.log 2 / 2) * (lam0 * t / 2 / xmax ^ 2)
        = (Real.log 2 - 1) / 4 * (lam0 * t / xmax ^ 2) := by
      field_simp; ring
    have e2 : -(lam0 / (40 * xmax ^ 2) * t) = -(1 / 40) * (lam0 * t / xmax ^ 2) := by
      field_simp
    rw [e1, e2]
    nlinarith
  have hfin := h9.trans hexp
  linarith
