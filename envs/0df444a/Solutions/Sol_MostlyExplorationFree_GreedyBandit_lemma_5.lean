-- Prove2me | solution 1 for MostlyExplorationFree.GreedyBandit.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T19:12:16.789019+00:00
-- url     : https://prove2.me/submissions/d180ab91-9f8c-4146-8597-dd1985c36e30

import Mathlib
import Definitions.Def_MostlyExplorationFree_GreedyBandit_Model

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MEFLemma5Aux
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

/-- A type synonym used to equip `Ω` with a sub-σ-algebra as a separate instance. -/
structure MWrap (Ω : Type*) where
  val : Ω

theorem lintegral_indep_comp {Ω γ : Type*} {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (P : Measure Ω) [IsFiniteMeasure P] [mγ : MeasurableSpace γ] (Y : Ω → γ) (hY : Measurable Y)
    (hind : Indep m (MeasurableSpace.comap Y mγ) P) (φ : Ω × γ → ℝ≥0∞)
    (hφ : Measurable[m.prod mγ] φ) :
    ∫⁻ ω, φ (ω, Y ω) ∂P = ∫⁻ ω, (∫⁻ ω', φ (ω, Y ω') ∂P) ∂P := by
  letI mW : MeasurableSpace (MWrap Ω) := m.comap MWrap.val
  set V : Ω → MWrap Ω := MWrap.mk with hVdef
  have hV : Measurable V := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := hs
    exact hm _ ht
  have hval : Measurable[mW, m] (MWrap.val : MWrap Ω → Ω) := comap_measurable _
  have hcomap : MeasurableSpace.comap V mW = m := by
    rw [MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_id
  have hVY : IndepFun V Y P := by
    rw [IndepFun_iff_Indep, hcomap]
    exact hind
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hV.aemeasurable hY.aemeasurable).mp hVY
  set ψ : MWrap Ω × γ → ℝ≥0∞ := fun p => φ (p.1.val, p.2) with hψ
  have hψm : Measurable ψ := hφ.comp (hval.prodMap measurable_id)
  calc ∫⁻ ω, φ (ω, Y ω) ∂P
      = ∫⁻ ω, ψ (V ω, Y ω) ∂P := rfl
    _ = ∫⁻ p, ψ p ∂(P.map (fun ω => (V ω, Y ω))) :=
        (lintegral_map hψm (hV.prodMk hY)).symm
    _ = ∫⁻ p, ψ p ∂((P.map V).prod (P.map Y)) := by rw [hmap]
    _ = ∫⁻ x, ∫⁻ y, ψ (x, y) ∂(P.map Y) ∂(P.map V) := lintegral_prod _ hψm.aemeasurable
    _ = ∫⁻ ω, ∫⁻ y, ψ (V ω, y) ∂(P.map Y) ∂P :=
        lintegral_map hψm.lintegral_prod_right' hV
    _ = ∫⁻ ω, ∫⁻ ω', φ (ω, Y ω') ∂P ∂P := by
        congr 1; funext ω
        exact lintegral_map (hψm.comp measurable_prodMk_left) hY


section Sig
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}

theorem modelSigma_le (X : ℕ → Ω → Fin d → ℝ) (ε : Fin 2 → ℕ → Ω → ℝ) (W : ℕ → Ω → Bool)
    (hX : ∀ t, Measurable (X t)) (hε : ∀ i t, Measurable (ε i t)) (hW : ∀ t, Measurable (W t))
    (j : ModelIndex) : modelSigma X ε W j ≤ mΩ := by
  rcases j with (j | p) | j
  · exact (hX (j + 1)).comap_le
  · exact (hε p.1 (p.2 + 1)).comap_le
  · exact (hW (j + 1)).comap_le

/-- The σ-algebra generated by the primitive variables whose index satisfies `p`. -/
noncomputable def sig (X : ℕ → Ω → Fin d → ℝ) (ε : Fin 2 → ℕ → Ω → ℝ) (W : ℕ → Ω → Bool)
    (p : ModelIndex → Prop) : MeasurableSpace Ω :=
  ⨆ (j : ModelIndex) (_ : p j), modelSigma X ε W j

theorem sig_le (X : ℕ → Ω → Fin d → ℝ) (ε : Fin 2 → ℕ → Ω → ℝ) (W : ℕ → Ω → Bool)
    (hX : ∀ t, Measurable (X t)) (hε : ∀ i t, Measurable (ε i t)) (hW : ∀ t, Measurable (W t))
    (p : ModelIndex → Prop) : sig X ε W p ≤ mΩ :=
  iSup₂_le (fun j _ => modelSigma_le X ε W hX hε hW j)

theorem measurable_X_sig (X : ℕ → Ω → Fin d → ℝ) (ε : Fin 2 → ℕ → Ω → ℝ) (W : ℕ → Ω → Bool)
    {p : ModelIndex → Prop} {s : ℕ} (h1 : 1 ≤ s) (hp : p (Sum.inl (Sum.inl (s - 1)))) :
    Measurable[sig X ε W p] (X s) := by
  have h := le_iSup₂ (f := fun (j : ModelIndex) (_ : p j) => modelSigma X ε W j) _ hp
  simp only [modelSigma, Sum.elim_inl] at h
  rw [show s - 1 + 1 = s by omega] at h
  exact measurable_iff_comap_le.mpr h

theorem measurable_W_sig (X : ℕ → Ω → Fin d → ℝ) (ε : Fin 2 → ℕ → Ω → ℝ) (W : ℕ → Ω → Bool)
    {p : ModelIndex → Prop} {s : ℕ} (h1 : 1 ≤ s) (hp : p (Sum.inr (s - 1))) :
    Measurable[sig X ε W p] (W s) := by
  have h := le_iSup₂ (f := fun (j : ModelIndex) (_ : p j) => modelSigma X ε W j) _ hp
  simp only [modelSigma, Sum.elim_inr] at h
  rw [show s - 1 + 1 = s by omega] at h
  exact measurable_iff_comap_le.mpr h

theorem measurable_ε_sig (X : ℕ → Ω → Fin d → ℝ) (ε : Fin 2 → ℕ → Ω → ℝ) (W : ℕ → Ω → Bool)
    {p : ModelIndex → Prop} (j : Fin 2) {s : ℕ} (h1 : 1 ≤ s)
    (hp : p (Sum.inl (Sum.inr (j, s - 1)))) : Measurable[sig X ε W p] (ε j s) := by
  have h := le_iSup₂ (f := fun (j : ModelIndex) (_ : p j) => modelSigma X ε W j) _ hp
  simp only [modelSigma, Sum.elim_inl, Sum.elim_inr] at h
  rw [show s - 1 + 1 = s by omega] at h
  exact measurable_iff_comap_le.mpr h

theorem indep_sig_ε (P : Measure Ω) (X : ℕ → Ω → Fin d → ℝ) (ε : Fin 2 → ℕ → Ω → ℝ)
    (W : ℕ → Ω → Bool)
    (hX : ∀ t, Measurable (X t)) (hε : ∀ i t, Measurable (ε i t)) (hW : ∀ t, Measurable (W t))
    (hind : iIndep (modelSigma X ε W) P) (p : ModelIndex → Prop) (j : Fin 2) (s : ℕ)
    (h1 : 1 ≤ s) (hp : ¬ p (Sum.inl (Sum.inr (j, s - 1)))) :
    Indep (sig X ε W p) (MeasurableSpace.comap (ε j s) inferInstance) P := by
  have hdisj : Disjoint {k : ModelIndex | p k} {Sum.inl (Sum.inr (j, s - 1))} := by
    rw [Set.disjoint_singleton_right]
    exact hp
  have h := indep_iSup_of_disjoint (modelSigma_le X ε W hX hε hW) hind hdisj
  rw [iSup_singleton] at h
  simp only [modelSigma, Sum.elim_inl, Sum.elim_inr] at h
  rw [show s - 1 + 1 = s by omega] at h
  exact h

end Sig

section OLS
variable {d : ℕ}

theorem ols_error_bound (hd : 1 ≤ d) (β : Fin 2 → Fin d → ℝ) (x : ℕ → Fin d → ℝ)
    (e : Fin 2 → ℕ → ℝ) (a : ℕ → Fin 2) (i : Fin 2) (t : ℕ) (L χ : ℝ) (hL : 0 < L)
    (hχ : 0 < χ) (hlam : L ≤ lambdaMin (gramOf x a i t))
    (hest : χ ≤ l2norm (estOf β x e a i t - β i)) :
    ∃ r : Fin d, L * χ / Real.sqrt d
      ≤ |∑ s ∈ Finset.Icc 1 t, (if a s = i then x s r else 0) * e i s| := by
  set G := gramOf x a i t with hG
  set y : Fin d → ℝ := ∑ s ∈ playedOf a i t, e i s • x s with hy
  -- quadratic form bound
  have hquad : ∀ v : Fin d → ℝ, L * (v ⬝ᵥ v) ≤ v ⬝ᵥ (G *ᵥ v) := by
    intro v
    by_cases hv0 : v = 0
    · subst hv0; simp
    have hvv : 0 < v ⬝ᵥ v := by
      rcases (Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i)) : (0:ℝ) ≤ v ⬝ᵥ v).lt_or_eq
        with h | h
      · exact h
      · exact absurd (dotProduct_self_eq_zero.mp h.symm) hv0
    set nv := Real.sqrt (v ⬝ᵥ v) with hnv
    have hnvpos : 0 < nv := Real.sqrt_pos.mpr hvv
    set w := nv⁻¹ • v with hw
    have hww : w ⬝ᵥ w = 1 := by
      rw [hw, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
        ← Real.sq_sqrt hvv.le, ← hnv]
      field_simp
    have h1 := rayleigh_ge_of_lambdaMin G L hL hlam w hww
    rw [hw, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at h1
    have h2 : v ⬝ᵥ v = nv ^ 2 := (Real.sq_sqrt hvv.le).symm
    rw [h2]
    have h3 : nv⁻¹ * (nv⁻¹ * (v ⬝ᵥ (G *ᵥ v))) = (v ⬝ᵥ (G *ᵥ v)) / nv ^ 2 := by
      field_simp
    rw [h3, le_div_iff₀ (by positivity)] at h1
    linarith
  -- invertibility
  have hdet : G.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hGv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have := hquad v
    rw [hGv, dotProduct_zero] at this
    have hvv : 0 < v ⬝ᵥ v := by
      rcases (Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i)) : (0:ℝ) ≤ v ⬝ᵥ v).lt_or_eq
        with h | h
      · exact h
      · exact absurd (dotProduct_self_eq_zero.mp h.symm) hv0
    nlinarith
  -- normal equations
  have hfull : ∑ s ∈ playedOf a i t, rewardOf β x e a s • x s = G *ᵥ β i + y := by
    rw [hG, hy, gramOf, sum_mulVec, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    have has : a s = i := (Finset.mem_filter.mp hs).2
    rw [vecMulVec_mulVec, op_smul_eq_smul, rewardOf, has, add_smul, dotProduct_comm]
  have hGw : G *ᵥ (estOf β x e a i t - β i) = y := by
    have hunit : IsUnit G.det := isUnit_iff_ne_zero.mpr hdet
    rw [mulVec_sub]
    unfold estOf
    rw [if_pos hdet, ← hG, hfull, mulVec_mulVec, Matrix.mul_nonsing_inv G hunit, one_mulVec]
    abel
  set w := estOf β x e a i t - β i with hw
  have hwpos : 0 < l2norm w := lt_of_lt_of_le hχ hest
  have hww : 0 ≤ w ⬝ᵥ w := Finset.sum_nonneg (fun i _ => mul_self_nonneg (w i))
  have hkey : L * l2norm w ≤ l2norm y := by
    have h1 := hquad w
    rw [hGw] at h1
    have h2 : w ⬝ᵥ y ≤ l2norm w * l2norm y := le_trans (le_abs_self _) (abs_dot_le' w y)
    have h3 : w ⬝ᵥ w = l2norm w ^ 2 := (Real.sq_sqrt hww).symm
    rw [h3] at h1
    have := le_trans h1 h2
    nlinarith
  have hy_big : L * χ ≤ l2norm y := le_trans (mul_le_mul_of_nonneg_left hest hL.le) hkey
  -- some coordinate is large
  have hyr : ∀ r, y r = ∑ s ∈ Finset.Icc 1 t, (if a s = i then x s r else 0) * e i s := by
    intro r
    rw [hy, Finset.sum_apply, playedOf, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    split_ifs <;> simp [mul_comm]
  by_contra hcon
  push Not at hcon
  have hdpos : (0:ℝ) < d := by exact_mod_cast hd
  have hlt : y ⬝ᵥ y < (L * χ) ^ 2 := by
    have hne : (Finset.univ : Finset (Fin d)).Nonempty := ⟨⟨0, hd⟩, Finset.mem_univ _⟩
    calc y ⬝ᵥ y = ∑ r, y r * y r := rfl
      _ < ∑ _r : Fin d, (L * χ / Real.sqrt d) ^ 2 := by
          apply Finset.sum_lt_sum_of_nonempty hne
          intro r _
          have h := hcon r
          rw [← hyr r] at h
          have h0 : |y r| ^ 2 < (L * χ / Real.sqrt d) ^ 2 :=
            pow_lt_pow_left₀ h (abs_nonneg _) (by norm_num)
          rw [sq_abs] at h0
          nlinarith
      _ = (L * χ) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, div_pow,
            Real.sq_sqrt hdpos.le]
          field_simp
  have hyy : 0 ≤ y ⬝ᵥ y := Finset.sum_nonneg (fun i _ => mul_self_nonneg (y i))
  have : l2norm y < L * χ := by
    unfold l2norm
    rw [← Real.sqrt_sq (by positivity : 0 ≤ L * χ)]
    exact Real.sqrt_lt_sqrt hyy hlt
  linarith

end OLS


section MGF
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}

/-- Indices of the variables observed by the end of the decision at time `k + 1`:
contexts and coins up to time `k + 1`, noises up to time `k`. -/
def predK (k : ℕ) : ModelIndex → Prop :=
  Sum.elim (Sum.elim (fun t => t + 1 ≤ k + 1) (fun q => q.2 + 1 ≤ k)) (fun t => t + 1 ≤ k + 1)

/-- `X_{s,r} 𝕀{π_s = i}`. -/
noncomputable def coefF (β : Fin 2 → Fin d → ℝ) (X : ℕ → Ω → Fin d → ℝ) (ε : Fin 2 → ℕ → Ω → ℝ)
    (W : ℕ → Ω → Bool) (i : Fin 2) (r : Fin d) (s : ℕ) (ω : Ω) : ℝ :=
  if arm β X ε W s ω = i then X s ω r else 0

/-- `𝕀{π_s = i}`. -/
noncomputable def indF (β : Fin 2 → Fin d → ℝ) (X : ℕ → Ω → Fin d → ℝ) (ε : Fin 2 → ℕ → Ω → ℝ)
    (W : ℕ → Ω → Bool) (i : Fin 2) (s : ℕ) (ω : Ω) : ℝ :=
  if arm β X ε W s ω = i then 1 else 0

/-- `∑_{s ≤ k} X_{s,r} 𝕀{π_s = i} ε_{i,s}`. -/
noncomputable def Ssum (β : Fin 2 → Fin d → ℝ) (X : ℕ → Ω → Fin d → ℝ) (ε : Fin 2 → ℕ → Ω → ℝ)
    (W : ℕ → Ω → Bool) (i : Fin 2) (r : Fin d) (k : ℕ) (ω : Ω) : ℝ :=
  ∑ s ∈ Finset.Icc 1 k, coefF β X ε W i r s ω * ε i s ω

/-- `∑_{s ≤ k} 𝕀{π_s = i} = |S_{i,k}|`. -/
noncomputable def Nsum (β : Fin 2 → Fin d → ℝ) (X : ℕ → Ω → Fin d → ℝ) (ε : Fin 2 → ℕ → Ω → ℝ)
    (W : ℕ → Ω → Bool) (i : Fin 2) (k : ℕ) (ω : Ω) : ℝ :=
  ∑ s ∈ Finset.Icc 1 k, indF β X ε W i s ω

theorem inner_bound (P : Measure Ω) (Y : Ω → ℝ) (hYm : Measurable Y) (σ : ℝ)
    (hY : HasSubgaussianMGF Y (σ ^ 2).toNNReal P) (A : ℝ≥0∞) (τ c ι cc : ℝ)
    (hc : σ ^ 2 * (τ * c) ^ 2 / 2 ≤ cc * ι) :
    ∫⁻ ω', A * ENNReal.ofReal (Real.exp (τ * c * Y ω' - cc * ι)) ∂P ≤ A := by
  have hmgf : ∫⁻ ω', ENNReal.ofReal (Real.exp ((τ * c) * Y ω')) ∂P
      ≤ ENNReal.ofReal (Real.exp (σ ^ 2 * (τ * c) ^ 2 / 2)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hY.integrable_exp_mul _)
      (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le))]
    apply ENNReal.ofReal_le_ofReal
    have := hY.mgf_le (τ * c)
    simpa [mgf, Real.coe_toNNReal _ (sq_nonneg σ)] using this
  calc ∫⁻ ω', A * ENNReal.ofReal (Real.exp (τ * c * Y ω' - cc * ι)) ∂P
      = ∫⁻ ω', (A * ENNReal.ofReal (Real.exp (-(cc * ι))))
          * ENNReal.ofReal (Real.exp ((τ * c) * Y ω')) ∂P := by
        congr 1; funext ω'
        have he : Real.exp (τ * c * Y ω' - cc * ι)
            = Real.exp (-(cc * ι)) * Real.exp ((τ * c) * Y ω') := by
          rw [← Real.exp_add]; ring_nf
        rw [he, ENNReal.ofReal_mul (Real.exp_pos _).le, ← mul_assoc]
    _ = (A * ENNReal.ofReal (Real.exp (-(cc * ι))))
          * ∫⁻ ω', ENNReal.ofReal (Real.exp ((τ * c) * Y ω')) ∂P :=
        lintegral_const_mul _ (((hYm.const_mul _).exp).ennreal_ofReal)
    _ ≤ (A * ENNReal.ofReal (Real.exp (-(cc * ι))))
          * ENNReal.ofReal (Real.exp (σ ^ 2 * (τ * c) ^ 2 / 2)) := by gcongr
    _ = A * ENNReal.ofReal (Real.exp (-(cc * ι) + σ ^ 2 * (τ * c) ^ 2 / 2)) := by
        rw [mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    _ ≤ A * 1 := by
        gcongr
        rw [ENNReal.ofReal_le_one]
        exact Real.exp_le_one_iff.mpr (by linarith)
    _ = A := mul_one A

theorem km (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure (Fin d → ℝ))
    (X : ℕ → Ω → Fin d → ℝ) (ε : Fin 2 → ℕ → Ω → ℝ) (W : ℕ → Ω → Bool) (σ : ℝ)
    (β : Fin 2 → Fin d → ℝ) (xmax : ℝ)
    (hmodel : IsGreedyModel P μ X ε W σ)
    (hXb : ∀ s, 1 ≤ s → ∀ᵐ ω ∂P, l2norm (X s ω) ≤ xmax) (i : Fin 2) (r : Fin d) (τ : ℝ) :
    ∀ k, ∫⁻ ω, ENNReal.ofReal (Real.exp (τ * Ssum β X ε W i r k ω
      - σ ^ 2 * xmax ^ 2 * τ ^ 2 / 2 * Nsum β X ε W i k ω)) ∂P ≤ 1 := by
  have hXm := hmodel.measurable_X
  have hεm := hmodel.measurable_ε
  have hWm := hmodel.measurable_W
  set cc := σ ^ 2 * xmax ^ 2 * τ ^ 2 / 2 with hcc
  intro k
  induction k with
  | zero => simp [Ssum, Nsum]
  | succ k ih =>
    have hGle : sig X ε W (predK k) ≤ mΩ := sig_le X ε W hXm hεm hWm _
    have hXG : ∀ s, 1 ≤ s → s ≤ k + 1 → Measurable[sig X ε W (predK k)] (X s) := fun s h1 h2 =>
      measurable_X_sig X ε W h1 (by simp only [predK, Sum.elim_inl]; omega)
    have hWG : ∀ s, 1 ≤ s → s ≤ k + 1 → Measurable[sig X ε W (predK k)] (W s) := fun s h1 h2 =>
      measurable_W_sig X ε W h1 (by simp only [predK, Sum.elim_inr]; omega)
    have hεG : ∀ j s, 1 ≤ s → s ≤ k → Measurable[sig X ε W (predK k)] (ε j s) := fun j s h1 h2 =>
      measurable_ε_sig X ε W j h1 (by simp only [predK, Sum.elim_inl, Sum.elim_inr]; omega)
    have harmG : ∀ s ∈ Finset.Icc 1 (k + 1), Measurable[sig X ε W (predK k)] (arm β X ε W s) :=
      measurable_arm_le (mΩ := sig X ε W (predK k)) β X ε W (k + 1)
        (fun s hs => hXG s (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hs).2)
        (fun s hs => hWG s (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hs).2)
        (fun j s hs => hεG j s (Finset.mem_Icc.mp hs).1
          (by have := (Finset.mem_Icc.mp hs).2; omega))
    have hcoefG : ∀ s ∈ Finset.Icc 1 (k + 1), Measurable[sig X ε W (predK k)] (coefF β X ε W i r s) := by
      intro s hs
      exact Measurable.ite ((harmG s hs) (measurableSet_singleton i))
        ((measurable_pi_apply r).comp (hXG s (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hs).2))
        measurable_const
    have hindG : ∀ s ∈ Finset.Icc 1 (k + 1), Measurable[sig X ε W (predK k)] (indF β X ε W i s) := by
      intro s hs
      exact Measurable.ite ((harmG s hs) (measurableSet_singleton i)) measurable_const
        measurable_const
    have hmemk : ∀ s ∈ Finset.Icc 1 k, s ∈ Finset.Icc 1 (k + 1) := fun s hs =>
      Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hs).1, by have := (Finset.mem_Icc.mp hs).2; omega⟩
    have hSG : Measurable[sig X ε W (predK k)] (Ssum β X ε W i r k) := by
      unfold Ssum
      exact Finset.measurable_sum _ (fun s hs => (hcoefG s (hmemk s hs)).mul
        (hεG i s (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hs).2))
    have hNG : Measurable[sig X ε W (predK k)] (Nsum β X ε W i k) := by
      unfold Nsum
      exact Finset.measurable_sum _ (fun s hs => hindG s (hmemk s hs))
    have hk1 : k + 1 ∈ Finset.Icc 1 (k + 1) := Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
    set φ : Ω × ℝ → ℝ≥0∞ := fun p =>
      ENNReal.ofReal (Real.exp (τ * Ssum β X ε W i r k p.1 - cc * Nsum β X ε W i k p.1))
        * ENNReal.ofReal (Real.exp (τ * coefF β X ε W i r (k + 1) p.1 * p.2
          - cc * indF β X ε W i (k + 1) p.1)) with hφdef
    have hφ : Measurable[(sig X ε W (predK k)).prod inferInstance] φ := by
      rw [hφdef]
      refine Measurable.mul (M := ℝ≥0∞) ?_ ?_
      · exact (((hSG.comp measurable_fst).const_mul τ).sub
          ((hNG.comp measurable_fst).const_mul cc)).exp.ennreal_ofReal
      · exact (((((hcoefG _ hk1).comp measurable_fst).const_mul τ).mul measurable_snd).sub
          (((hindG _ hk1).comp measurable_fst).const_mul cc)).exp.ennreal_ofReal
    have hind := indep_sig_ε P X ε W hXm hεm hWm hmodel.indep (predK k) i (k + 1) (by omega)
      (by simp only [predK, Sum.elim_inl, Sum.elim_inr]; omega)
    calc ∫⁻ ω, ENNReal.ofReal (Real.exp (τ * Ssum β X ε W i r (k + 1) ω
          - cc * Nsum β X ε W i (k + 1) ω)) ∂P
        = ∫⁻ ω, φ (ω, ε i (k + 1) ω) ∂P := by
          congr 1; funext ω
          simp only [hφdef, Ssum, Nsum]
          rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega),
            ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
          ring_nf
      _ = ∫⁻ ω, ∫⁻ ω', φ (ω, ε i (k + 1) ω') ∂P ∂P :=
          lintegral_indep_comp hGle P (ε i (k + 1)) (hεm i (k + 1)) hind φ hφ
      _ ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (τ * Ssum β X ε W i r k ω
          - cc * Nsum β X ε W i k ω)) ∂P := by
          refine lintegral_mono_ae ?_
          filter_upwards [hXb (k + 1) (by omega)] with ω hω
          simp only [hφdef]
          refine inner_bound P (ε i (k + 1)) (hεm i (k + 1)) σ
            (hmodel.subgaussian_ε i (k + 1) (by omega)) _ τ _ _ cc ?_
          simp only [coefF, indF, hcc]
          split_ifs
          · have h1 : X (k + 1) ω r ^ 2 ≤ xmax ^ 2 := by
              have h2 : X (k + 1) ω r * X (k + 1) ω r ≤ X (k + 1) ω ⬝ᵥ X (k + 1) ω :=
                Finset.single_le_sum (f := fun j => X (k + 1) ω j * X (k + 1) ω j)
                  (fun j _ => mul_self_nonneg _) (Finset.mem_univ r)
              have h3 := dot_self_le_of_l2norm hω
              nlinarith
            have : 0 ≤ σ ^ 2 * τ ^ 2 := by positivity
            nlinarith
          · simp
      _ ≤ 1 := ih

end MGF


theorem tail_bound {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    [IsProbabilityMeasure P] (μ : Measure (Fin d → ℝ))
    (X : ℕ → Ω → Fin d → ℝ) (ε : Fin 2 → ℕ → Ω → ℝ) (W : ℕ → Ω → Bool) (σ : ℝ) (hσ : 0 < σ)
    (β : Fin 2 → Fin d → ℝ) (xmax : ℝ) (hxmax : 0 < xmax)
    (hmodel : IsGreedyModel P μ X ε W σ)
    (hXb : ∀ s, 1 ≤ s → ∀ᵐ ω ∂P, l2norm (X s ω) ≤ xmax) (i : Fin 2) (r : Fin d) (t n : ℕ)
    (hn1 : 1 ≤ n) (hN : ∀ ω, Nsum β X ε W i t ω ≤ n) (a0 : ℝ) (ha0 : 0 < a0) :
    (P {ω | a0 ≤ |Ssum β X ε W i r t ω|}).toReal
      ≤ 2 * Real.exp (-(a0 ^ 2 / (2 * σ ^ 2 * xmax ^ 2 * n))) := by
  have hXm := hmodel.measurable_X
  have hεm := hmodel.measurable_ε
  have hWm := hmodel.measurable_W
  have harm : ∀ s ∈ Finset.Icc 1 t, Measurable (arm β X ε W s) :=
    measurable_arm_le β X ε W t (fun s _ => hXm s) (fun s _ => hWm s) (fun j s _ => hεm j s)
  have hcoef : ∀ s ∈ Finset.Icc 1 t, Measurable (coefF β X ε W i r s) := fun s hs =>
    Measurable.ite ((harm s hs) (measurableSet_singleton i))
      ((measurable_pi_apply r).comp (hXm s)) measurable_const
  have hSm : Measurable (Ssum β X ε W i r t) := by
    unfold Ssum
    exact Finset.measurable_sum _ (fun s hs => (hcoef s hs).mul (hεm i s))
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hmgf : ∀ τ : ℝ, ∫⁻ ω, ENNReal.ofReal (Real.exp (τ * Ssum β X ε W i r t ω)) ∂P
      ≤ ENNReal.ofReal (Real.exp (σ ^ 2 * xmax ^ 2 * τ ^ 2 / 2 * n)) := by
    intro τ
    have hcc : 0 ≤ σ ^ 2 * xmax ^ 2 * τ ^ 2 / 2 := by positivity
    calc ∫⁻ ω, ENNReal.ofReal (Real.exp (τ * Ssum β X ε W i r t ω)) ∂P
        ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (τ * Ssum β X ε W i r t ω
            - σ ^ 2 * xmax ^ 2 * τ ^ 2 / 2 * Nsum β X ε W i t ω))
            * ENNReal.ofReal (Real.exp (σ ^ 2 * xmax ^ 2 * τ ^ 2 / 2 * n)) ∂P := by
          refine lintegral_mono (fun ω => ?_)
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
          apply ENNReal.ofReal_le_ofReal
          apply Real.exp_le_exp.mpr
          have := mul_le_mul_of_nonneg_left (hN ω) hcc
          linarith
      _ = (∫⁻ ω, ENNReal.ofReal (Real.exp (τ * Ssum β X ε W i r t ω
            - σ ^ 2 * xmax ^ 2 * τ ^ 2 / 2 * Nsum β X ε W i t ω)) ∂P)
            * ENNReal.ofReal (Real.exp (σ ^ 2 * xmax ^ 2 * τ ^ 2 / 2 * n)) :=
          lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
      _ ≤ 1 * ENNReal.ofReal (Real.exp (σ ^ 2 * xmax ^ 2 * τ ^ 2 / 2 * n)) := by
          gcongr
          exact km P μ X ε W σ β xmax hmodel hXb i r τ t
      _ = ENNReal.ofReal (Real.exp (σ ^ 2 * xmax ^ 2 * τ ^ 2 / 2 * n)) := one_mul _
  have hside : ∀ (f : Ω → ℝ) (τ : ℝ), 0 < τ → Measurable f →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (τ * f ω)) ∂P
        ≤ ENNReal.ofReal (Real.exp (σ ^ 2 * xmax ^ 2 * τ ^ 2 / 2 * n)) →
      (P {ω | a0 ≤ f ω}).toReal ≤ Real.exp (σ ^ 2 * xmax ^ 2 * τ ^ 2 / 2 * n - τ * a0) := by
    intro f τ hτ hf hI
    have hM := mul_meas_ge_le_lintegral₀ (μ := P)
      (f := fun ω => ENNReal.ofReal (Real.exp (τ * f ω)))
      ((hf.const_mul τ).exp.ennreal_ofReal.aemeasurable) (ENNReal.ofReal (Real.exp (τ * a0)))
    have hsub : {ω | a0 ≤ f ω}
        ⊆ {ω | ENNReal.ofReal (Real.exp (τ * a0)) ≤ ENNReal.ofReal (Real.exp (τ * f ω))} :=
      fun ω hω => ENNReal.ofReal_le_ofReal
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω hτ.le))
    have h1 : ENNReal.ofReal (Real.exp (τ * a0)) * P {ω | a0 ≤ f ω}
        ≤ ENNReal.ofReal (Real.exp (σ ^ 2 * xmax ^ 2 * τ ^ 2 / 2 * n)) :=
      (mul_le_mul_right (measure_mono hsub) _).trans (hM.trans hI)
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le,
      ENNReal.toReal_ofReal (Real.exp_pos _).le] at h2
    rw [Real.exp_sub, le_div_iff₀ (Real.exp_pos _)]
    linarith
  set τ := a0 / (σ ^ 2 * xmax ^ 2 * n) with hτdef
  have hτ : 0 < τ := by positivity
  have hval : σ ^ 2 * xmax ^ 2 * τ ^ 2 / 2 * n - τ * a0
      = -(a0 ^ 2 / (2 * σ ^ 2 * xmax ^ 2 * n)) := by
    rw [hτdef]; field_simp; ring
  have hup := hside (Ssum β X ε W i r t) τ hτ hSm (hmgf τ)
  have hlo := hside (fun ω => -Ssum β X ε W i r t ω) τ hτ hSm.neg (by
    calc ∫⁻ ω, ENNReal.ofReal (Real.exp (τ * -Ssum β X ε W i r t ω)) ∂P
        = ∫⁻ ω, ENNReal.ofReal (Real.exp ((-τ) * Ssum β X ε W i r t ω)) ∂P := by
          congr 1; funext ω; ring_nf
      _ ≤ ENNReal.ofReal (Real.exp (σ ^ 2 * xmax ^ 2 * (-τ) ^ 2 / 2 * n)) := hmgf (-τ)
      _ = ENNReal.ofReal (Real.exp (σ ^ 2 * xmax ^ 2 * τ ^ 2 / 2 * n)) := by rw [neg_sq])
  rw [hval] at hup hlo
  have hsubset : {ω | a0 ≤ |Ssum β X ε W i r t ω|}
      ⊆ {ω | a0 ≤ Ssum β X ε W i r t ω} ∪ {ω | a0 ≤ -Ssum β X ε W i r t ω} := by
    intro ω hω
    simp only [Set.mem_union, Set.mem_ofPred_eq] at hω ⊢
    rcases le_abs'.mp hω with h | h
    · right; linarith
    · left; exact h
  calc (P {ω | a0 ≤ |Ssum β X ε W i r t ω|}).toReal
      ≤ (P {ω | a0 ≤ Ssum β X ε W i r t ω} + P {ω | a0 ≤ -Ssum β X ε W i r t ω}).toReal :=
        ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩)
          ((measure_mono hsubset).trans (measure_union_le _ _))
    _ = (P {ω | a0 ≤ Ssum β X ε W i r t ω}).toReal
          + (P {ω | a0 ≤ -Ssum β X ε W i r t ω}).toReal :=
        ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)
    _ ≤ 2 * Real.exp (-(a0 ^ 2 / (2 * σ ^ 2 * xmax ^ 2 * n))) := by linarith

end MEFLemma5Aux

open MostlyExplorationFree.GreedyBandit MEFLemma5Aux

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d : ℕ} (hd : 1 ≤ d)
    (μ : Measure (Fin d → ℝ)) (X : ℕ → Ω → Fin d → ℝ) (ε : Fin 2 → ℕ → Ω → ℝ)
    (W : ℕ → Ω → Bool) (σ : ℝ) (hσ : 0 < σ) (β : Fin 2 → Fin d → ℝ) (xmax bmax : ℝ)
    (hmodel : IsGreedyModel P μ X ε W σ) (hA1 : ParameterSet μ β xmax bmax)
    (i : Fin 2) (t : ℕ) (ht : 1 ≤ t) (lam χ : ℝ) (hlam : 0 < lam) (hχ : 0 < χ)
    (n : ℕ) (hn : ∀ ω, (played β X ε W i t ω).card ≤ n) :
    (P {ω | χ ≤ l2norm (est β X ε W i t ω - β i) ∧
        lam * t ≤ lambdaMin (gram β X ε W i t ω)}).toReal
      ≤ 2 * d * Real.exp (-(C2 lam d σ xmax * t ^ 2 * χ ^ 2 / n)) := by
  have hP := hmodel.isProbability
  have hxmax : 0 < xmax := hA1.1
  have hXb0 := hA1.2.1
  have hXb : ∀ s, 1 ≤ s → ∀ᵐ ω ∂P, l2norm (X s ω) ≤ xmax := fun s hs => by
    have h := hXb0
    rw [← hmodel.law_X s hs] at h
    exact ae_of_ae_map (hmodel.measurable_X s).aemeasurable h
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    simp only [Nat.cast_zero, div_zero, neg_zero, Real.exp_zero, mul_one]
    have h1 : (P {ω | χ ≤ l2norm (est β X ε W i t ω - β i) ∧
        lam * t ≤ lambdaMin (gram β X ε W i t ω)}).toReal ≤ 1 :=
      ENNReal.toReal_le_of_le_ofReal zero_le_one (prob_le_one.trans (by simp))
    linarith
  · have htR : (0 : ℝ) < t := by exact_mod_cast ht
    have hdpos : (0 : ℝ) < d := by linarith
    set a0 := lam * t * χ / Real.sqrt d with ha0def
    have ha0 : 0 < a0 := by
      rw [ha0def]; have := Real.sqrt_pos.mpr hdpos; positivity
    have hN : ∀ ω, Nsum β X ε W i t ω ≤ n := by
      intro ω
      unfold Nsum indF
      rw [← Finset.natCast_card_filter]
      exact_mod_cast hn ω
    have hsub : {ω | χ ≤ l2norm (est β X ε W i t ω - β i) ∧
        lam * t ≤ lambdaMin (gram β X ε W i t ω)}
        ⊆ ⋃ r : Fin d, {ω | a0 ≤ |Ssum β X ε W i r t ω|} := by
      intro ω hω
      obtain ⟨r, hr⟩ := ols_error_bound hd β (fun s => X s ω) (fun j s => ε j s ω)
        (fun s => arm β X ε W s ω) i t (lam * t) χ (by positivity) hχ hω.2 hω.1
      exact Set.mem_iUnion.mpr ⟨r, hr⟩
    have hexp : a0 ^ 2 / (2 * σ ^ 2 * xmax ^ 2 * n) = C2 lam d σ xmax * t ^ 2 * χ ^ 2 / n := by
      rw [ha0def, div_pow, Real.sq_sqrt hdpos.le]
      unfold C2
      field_simp
    calc (P {ω | χ ≤ l2norm (est β X ε W i t ω - β i) ∧
          lam * t ≤ lambdaMin (gram β X ε W i t ω)}).toReal
        ≤ (P (⋃ r : Fin d, {ω | a0 ≤ |Ssum β X ε W i r t ω|})).toReal :=
          ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
      _ ≤ (∑ r : Fin d, P {ω | a0 ≤ |Ssum β X ε W i r t ω|}).toReal :=
          ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr (fun r _ => measure_ne_top _ _))
            (measure_iUnion_fintype_le _ _)
      _ = ∑ r : Fin d, (P {ω | a0 ≤ |Ssum β X ε W i r t ω|}).toReal :=
          ENNReal.toReal_sum (fun r _ => measure_ne_top _ _)
      _ ≤ ∑ _r : Fin d, 2 * Real.exp (-(a0 ^ 2 / (2 * σ ^ 2 * xmax ^ 2 * n))) :=
          Finset.sum_le_sum (fun r _ => tail_bound P μ X ε W σ hσ β xmax hxmax hmodel hXb i r
            t n hnpos hN a0 ha0)
      _ = 2 * d * Real.exp (-(C2 lam d σ xmax * t ^ 2 * χ ^ 2 / n)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hexp]
          ring
