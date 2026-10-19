-- Prove2me | solution 1 for OAI.DirectionalZeroOne.directional_zero_one
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T17:54:16.297885+00:00
-- url     : https://prove2.me/submissions/20404e5e-2f8c-4144-bea5-c133ed833f12

import Mathlib
import Definitions.Def_DirectionalWalk

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h := dif_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
alias Finset.prod_le_prod₀ := Finset.prod_le_prod
alias Finset.prod_le_one₀ := Finset.prod_le_one
alias Finset.one_le_prod₀ := Finset.one_le_prod
alias List.Nodup.getElem?_inj := List.getElem?_inj
end OAICompat434

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

lemma probabilityMeasure_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} [IsProbabilityMeasure μ] {f : α → β}
    (hf : AEMeasurable f μ) : IsProbabilityMeasure (μ.map f) :=
  (Measure.isProbabilityMeasure_map_iff hf).2 inferInstance

instance {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (environmentLaw μ) := by
  unfold environmentLaw
  infer_instance

instance {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ] (x : Site d) :
    IsProbabilityMeasure (initialLaw μ x) := by
  apply probabilityMeasure_map
  exact (measurable_id.prodMk measurable_const).aemeasurable

instance {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ] (x : Site d) :
    IsProbabilityMeasure (annealed μ x) := by
  apply probabilityMeasure_map
  exact (Measurable.of_eval (fun n => measurable_snd.comp (measurable_pi_apply n))).aemeasurable

lemma measurableSet_escape {d : ℕ} (ℓ : Fin d → ℝ) : MeasurableSet (escape ℓ) := by
  apply measurableSet_tendsto
  intro n
  exact (measurable_of_countable (fun x : Site d => ∑ i, (x i : ℝ) * ℓ i)).comp
    (measurable_pi_apply n)

lemma all_rows_strictly_positive {d : ℕ} (μ : Measure (Row d))
    [IsProbabilityMeasure μ] (hμ : StrictEllipticity μ) :
    ∀ᵐ ω ∂environmentLaw μ, ∀ x e, 0 < (ω x).val e := by
  rw [ae_all_iff]
  intro x
  apply ae_of_ae_map (μ := environmentLaw μ) (f := fun ω : Environment d => ω x)
    (p := fun p : Row d => ∀ e, 0 < p.val e) (measurable_pi_apply x).aemeasurable
  simpa only [environmentLaw, Measure.infinitePi_map_eval, StrictEllipticity] using hμ

abbrev rowSigma {d : ℕ} (s : Set (Site d)) : MeasurableSpace (Environment d) :=
  ⨆ x ∈ s, MeasurableSpace.comap (fun ω : Environment d => ω x) inferInstance

lemma rowSigma_le {d : ℕ} (s : Set (Site d)) : rowSigma s ≤ (inferInstance : MeasurableSpace (Environment d)) := by
  exact iSup₂_le (fun x _ => (measurable_pi_apply x).comap_le)

lemma measurable_row {d : ℕ} {s : Set (Site d)} {x : Site d} (hx : x ∈ s) :
    @Measurable (Environment d) (Row d) (rowSigma s) _ (fun ω => ω x) := by
  exact measurable_iff_comap_le.mpr (le_iSup₂_of_le x hx le_rfl)

lemma independent_rowSigma {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    {s t : Set (Site d)} (hst : Disjoint s t) :
    Indep (rowSigma s) (rowSigma t) (environmentLaw μ) := by
  apply indep_iSup_of_disjoint (fun x => (measurable_pi_apply x).comap_le) _ hst
  exact iIndepFun_infinitePi (X := fun _ (p : Row d) => p) (fun _ => measurable_id)

noncomputable def quenchedWeight {d n : ℕ} (x : Fin n → Site d) (e : Fin n → Step d)
    (ω : Environment d) : ℝ≥0∞ := ∏ j, ENNReal.ofReal ((ω (x j)).val (e j))

noncomputable def wordWeight {d n : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x : Fin n → Site d) (e : Fin n → Step d) : ℝ≥0∞ :=
  ∫⁻ ω, quenchedWeight x e ω ∂environmentLaw μ

lemma measurable_quenchedWeight_on_rows {d n : ℕ} (x : Fin n → Site d)
    (e : Fin n → Step d) :
    @Measurable (Environment d) ℝ≥0∞ (rowSigma (Set.range x)) _
      (quenchedWeight x e) := by
  apply Finset.measurable_prod
  intro j hj
  exact ((measurable_pi_apply (e j)).comp
    (measurable_subtype_coe.comp (measurable_row (s := Set.range x) (x := x j) ⟨j, rfl⟩))).ennreal_ofReal

lemma measurable_quenchedWeight {d n : ℕ} (x : Fin n → Site d)
    (e : Fin n → Step d) : Measurable (quenchedWeight x e) :=
  (measurable_quenchedWeight_on_rows x e).mono (rowSigma_le _) le_rfl

lemma departure_transfer {d n : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x : Fin n → Site d) (e : Fin n → Step d) (f : Environment d → ℝ≥0∞)
    (hf : @Measurable (Environment d) ℝ≥0∞ (rowSigma ((Set.range x)ᶜ)) _ f) :
    (∫⁻ ω, quenchedWeight x e ω * f ω ∂environmentLaw μ) =
      wordWeight μ x e * ∫⁻ ω, f ω ∂environmentLaw μ := by
  exact lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    (rowSigma_le _) (rowSigma_le _)
    (independent_rowSigma μ disjoint_compl_right)
    (measurable_quenchedWeight_on_rows x e) hf

lemma quenchedWeight_le_one {d n : ℕ} (x : Fin n → Site d) (e : Fin n → Step d)
    (ω : Environment d) : quenchedWeight x e ω ≤ 1 := by
  apply Finset.prod_le_one'
  intro j hj
  exact ENNReal.ofReal_le_one.mpr ((ω (x j)).property.1 (e j)).2

lemma wordWeight_le_one {d n : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x : Fin n → Site d) (e : Fin n → Step d) : wordWeight μ x e ≤ 1 :=
  lintegral_le_const (ae_of_all _ (quenchedWeight_le_one x e))

lemma wordWeight_pos {d n : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hμ : StrictEllipticity μ) (x : Fin n → Site d) (e : Fin n → Step d) :
    0 < wordWeight μ x e := by
  apply pos_iff_ne_zero.mpr
  intro hz
  have hzero := (lintegral_eq_zero_iff (measurable_quenchedWeight x e)).mp hz
  obtain ⟨ω, hω, hωzero⟩ := ((all_rows_strictly_positive μ hμ).and hzero).exists
  have hp : 0 < quenchedWeight x e ω := by
    apply pos_iff_ne_zero.mpr
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (hω (x j) (e j)))
  exact (ne_of_gt hp) hωzero

noncomputable def meanStep {d : ℕ} (μ : Measure (Row d)) (e : Step d) : ℝ≥0∞ :=
  ∫⁻ p, ENNReal.ofReal (p.val e) ∂μ

lemma meanStep_pos {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hμ : StrictEllipticity μ) (e : Step d) : 0 < meanStep μ e := by
  apply pos_iff_ne_zero.mpr
  intro hz
  have hm : Measurable (fun p : Row d => ENNReal.ofReal (p.val e)) :=
    ((measurable_pi_apply e).comp measurable_subtype_coe).ennreal_ofReal
  have hzero := (lintegral_eq_zero_iff hm).mp hz
  obtain ⟨p, hp, hpzero⟩ := (hμ.and hzero).exists
  exact (ne_of_gt (ENNReal.ofReal_pos.mpr (hp e))) hpzero

lemma meanStep_le_one {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (e : Step d) : meanStep μ e ≤ 1 := by
  apply lintegral_le_const
  exact ae_of_all _ (fun p => ENNReal.ofReal_le_one.mpr (p.property.1 e).2)

lemma meanStep_at_site {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x : Site d) (e : Step d) :
    (∫⁻ ω, ENNReal.ofReal ((ω x).val e) ∂environmentLaw μ) = meanStep μ e := by
  have hm : Measurable (fun p : Row d => ENNReal.ofReal (p.val e)) :=
    ((measurable_pi_apply e).comp measurable_subtype_coe).ennreal_ofReal
  rw [← lintegral_map hm (measurable_pi_apply x)]
  simp only [environmentLaw, Measure.infinitePi_map_eval, meanStep]

lemma fresh_word_weight {d n : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x : Fin n → Site d) (e : Fin n → Step d) (hx : Function.Injective x) :
    wordWeight μ x e = ∏ j, meanStep μ (e j) := by
  have hi : iIndepFun (fun j : Fin n => fun ω : Environment d => ω (x j))
      (environmentLaw μ) :=
    iIndepFun.precomp hx
      (iIndepFun_infinitePi (X := fun _ (p : Row d) => p) (fun _ => measurable_id))
  let f : Fin n → Row d → ℝ≥0∞ := fun j p => ENNReal.ofReal (p.val (e j))
  have hf : ∀ j, Measurable (f j) := fun j =>
    ((measurable_pi_apply (e j)).comp measurable_subtype_coe).ennreal_ofReal
  have hid := hi.comp f hf
  unfold wordWeight quenchedWeight
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun]
  · exact Finset.prod_congr rfl (fun j hj => meanStep_at_site μ (x j) (e j))
  · exact hid
  · intro j
    exact (hf j).comp (measurable_pi_apply (x j))

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

noncomputable def walkInitialLaw {d : ℕ} (μ : Measure (Environment d)) (x : Site d) :
    Measure (State d) := μ.map (fun ω => (ω, x))

instance {d : ℕ} (μ : Measure (Environment d)) [IsProbabilityMeasure μ] (x : Site d) :
    IsProbabilityMeasure (walkInitialLaw μ x) := by
  apply probabilityMeasure_map
  exact (measurable_id.prodMk measurable_const).aemeasurable

noncomputable def walkStateLaw {d : ℕ} (μ : Measure (Environment d)) [IsProbabilityMeasure μ]
    (x : Site d) : Measure (ℕ → State d) :=
  Kernel.trajMeasure (X := fun _ => State d) (walkInitialLaw μ x) (historyKernel d)

instance {d : ℕ} (μ : Measure (Environment d)) [IsProbabilityMeasure μ] (x : Site d) :
    IsProbabilityMeasure (walkStateLaw μ x) := by
  unfold walkStateLaw
  infer_instance

lemma lintegral_transition {d : ℕ} (s : State d) (f : State d → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ t, f t ∂transition d s) =
      ∑ e, ENNReal.ofReal ((s.1 s.2).val e) * f (s.1, s.2 + stepVector e) := by
  change (∫⁻ t, f t ∂∑ e : Step d,
    ENNReal.ofReal ((s.1 s.2).val e) • Measure.dirac (s.1, s.2 + stepVector e)) = _
  rw [lintegral_finsetSum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac' _ hf, smul_eq_mul]

lemma walkStateLaw_initial_history {d : ℕ} (μ : Measure (Environment d)) [IsProbabilityMeasure μ]
    (x : Site d) :
    (walkStateLaw μ x).map (Preorder.frestrictLe 0) =
      (walkInitialLaw μ x).map (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => State d)).symm := by
  rw [walkStateLaw, Kernel.trajMeasure, Measure.map_comp _ _ (measurable_frestrictLe _),
    Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp]

lemma walkStateLaw_initial {d : ℕ} (μ : Measure (Environment d)) [IsProbabilityMeasure μ]
    (x : Site d) : (walkStateLaw μ x).map (fun z => z 0) = walkInitialLaw μ x := by
  let e := MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => State d)
  have h : (fun z : ℕ → State d => z 0) = e ∘ Preorder.frestrictLe 0 := by
    funext z
    rfl
  rw [h, ← Measure.map_map e.measurable (measurable_frestrictLe 0), walkStateLaw_initial_history]
  exact e.symm.map_symm_map

lemma walkStateLaw_one_step {d : ℕ} (μ : Measure (Environment d)) [IsProbabilityMeasure μ]
    (x : Site d) (n : ℕ)
    (f : ((i : Finset.Iic n) → State d) × State d → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f (Preorder.frestrictLe n z, z (n + 1)) ∂walkStateLaw μ x) =
      ∫⁻ z, ∫⁻ t, f (Preorder.frestrictLe n z, t) ∂transition d (z n) ∂walkStateLaw μ x := by
  have hm : Measurable (fun z : ℕ → State d => (Preorder.frestrictLe n z, z (n+1))) :=
    (measurable_frestrictLe n).prodMk (measurable_pi_apply _)
  rw [← lintegral_map hf hm]
  unfold walkStateLaw
  rw [← Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure,
    Measure.lintegral_compProd hf]
  rw [lintegral_map]
  · rfl
  · exact hf.lintegral_kernel_prod_right'
  · exact measurable_frestrictLe n

noncomputable def entryWeight {d : ℕ} (ω : Environment d) (x y : Site d) : ℝ≥0∞ :=
  ∑ e : Step d, if x + stepVector e = y then ENNReal.ofReal ((ω x).val e) else 0

lemma measurable_entryWeight {d : ℕ} (x y : Site d) :
    Measurable (fun ω : Environment d => entryWeight ω x y) := by
  apply Finset.measurable_sum
  intro e he
  split_ifs
  · exact ((measurable_pi_apply e).comp
      (measurable_subtype_coe.comp (measurable_pi_apply x))).ennreal_ofReal
  · exact measurable_const

def prefixMatches {d : ℕ} (n : ℕ) (γ : ℕ → Site d) (z : ℕ → State d) : Prop :=
  ∀ i ≤ n, (z i).2 = γ i

noncomputable def prefixObservable {d : ℕ} (n : ℕ) (γ : ℕ → Site d)
    (f : Environment d → ℝ≥0∞) (z : ℕ → State d) : ℝ≥0∞ := by
  classical
  exact if prefixMatches n γ z then f (z n).1 else 0

lemma measurableSet_prefixMatches {d : ℕ} (n : ℕ) (γ : ℕ → Site d) :
    MeasurableSet {z : ℕ → State d | prefixMatches n γ z} := by
  simp only [prefixMatches, Set.ofPred_forall]
  exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun _ =>
    measurableSet_eq_fun (measurable_snd.comp (measurable_pi_apply i)) measurable_const))

lemma measurable_prefixObservable {d : ℕ} (n : ℕ) (γ : ℕ → Site d)
    (f : Environment d → ℝ≥0∞) (hf : Measurable f) :
    Measurable (prefixObservable n γ f) := by
  exact (hf.comp (measurable_fst.comp (measurable_pi_apply n))).ite
    (measurableSet_prefixMatches n γ) measurable_const

lemma prefixMatches_succ {d : ℕ} (n : ℕ) (γ : ℕ → Site d) (z : ℕ → State d) :
    prefixMatches (n+1) γ z ↔ prefixMatches n γ z ∧ (z (n+1)).2 = γ (n+1) := by
  constructor
  · intro h
    exact ⟨fun i hi => h i (by omega), h _ le_rfl⟩
  · rintro ⟨h, hn⟩ i hi
    by_cases hin : i ≤ n
    · exact h i hin
    · have hie : i = n+1 := by omega
      simpa only [hie] using hn

noncomputable def pathWeight {d : ℕ} (n : ℕ) (γ : ℕ → Site d)
    (ω : Environment d) : ℝ≥0∞ :=
  ∏ i ∈ Finset.range n, entryWeight ω (γ i) (γ (i+1))

lemma measurable_pathWeight {d : ℕ} (n : ℕ) (γ : ℕ → Site d) :
    Measurable (pathWeight n γ) := by
  exact Finset.measurable_prod _ (fun i _ => measurable_entryWeight (γ i) (γ (i+1)))

lemma pathWeight_succ {d : ℕ} (n : ℕ) (γ : ℕ → Site d) (ω : Environment d) :
    pathWeight (n+1) γ ω = pathWeight n γ ω * entryWeight ω (γ n) (γ (n+1)) :=
  Finset.prod_range_succ _ n

lemma history_matches_iff {d : ℕ} (n : ℕ) (γ : ℕ → Site d) (z : ℕ → State d) :
    (∀ i : Finset.Iic n, (frestrictLe n z i).2 = γ i) ↔ prefixMatches n γ z := by
  constructor
  · intro h i hi
    exact h ⟨i, Finset.mem_Iic.mpr hi⟩
  · intro h i
    exact h i (Finset.mem_Iic.mp i.property)

lemma prefix_lintegral_succ {d : ℕ} (μ : Measure (Environment d)) [IsProbabilityMeasure μ]
    (x : Site d) (n : ℕ) (γ : ℕ → Site d) (f : Environment d → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ z, prefixObservable (n+1) γ f z ∂walkStateLaw μ x) =
      ∫⁻ z, prefixObservable n γ (fun ω => entryWeight ω (γ n) (γ (n+1)) * f ω) z
        ∂walkStateLaw μ x := by
  classical
  let F : ((i : Finset.Iic n) → State d) × State d → ℝ≥0∞ := fun q =>
    if (∀ i, (q.1 i).2 = γ i) then
      if q.2.2 = γ (n+1) then f q.2.1 else 0
    else 0
  have hm : MeasurableSet {q : ((i : Finset.Iic n) → State d) × State d |
      ∀ i, (q.1 i).2 = γ i} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i => measurableSet_eq_fun
      (measurable_snd.comp ((measurable_pi_apply i).comp measurable_fst)) measurable_const)
  have hn : MeasurableSet {q : ((i : Finset.Iic n) → State d) × State d |
      q.2.2 = γ (n+1)} :=
    measurableSet_eq_fun (measurable_snd.comp measurable_snd) measurable_const
  have hF : Measurable F :=
    Measurable.ite hm (Measurable.ite hn
      (hf.comp (measurable_fst.comp measurable_snd)) measurable_const) measurable_const
  have hFeq (z : ℕ → State d) :
      F (frestrictLe n z, z (n+1)) = prefixObservable (n+1) γ f z := by
    simp only [F, history_matches_iff, prefixObservable, prefixMatches_succ]
    split_ifs <;> simp_all
  calc
    (∫⁻ z, prefixObservable (n+1) γ f z ∂walkStateLaw μ x) =
        ∫⁻ z, F (frestrictLe n z, z (n+1)) ∂walkStateLaw μ x :=
      lintegral_congr (fun z => (hFeq z).symm)
    _ = ∫⁻ z, ∫⁻ t, F (frestrictLe n z, t) ∂transition d (z n) ∂walkStateLaw μ x :=
      walkStateLaw_one_step μ x n F hF
    _ = _ := by
      apply lintegral_congr
      intro z
      rw [lintegral_transition (z n) (fun t => F (frestrictLe n z, t))
        (hF.comp (measurable_const.prodMk measurable_id))]
      by_cases hz : prefixMatches n γ z
      · have hzn := hz n le_rfl
        simp only [F, history_matches_iff, hz, ite_true, prefixObservable]
        rw [hzn, entryWeight, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro e he
        split_ifs <;> simp_all
      · simp only [F, history_matches_iff, hz, ite_false, prefixObservable, mul_zero,
          Finset.sum_const_zero]

lemma prefix_lintegral_zero {d : ℕ} (μ : Measure (Environment d)) [IsProbabilityMeasure μ]
    (x : Site d) (γ : ℕ → Site d) (f : Environment d → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, prefixObservable 0 γ f z ∂walkStateLaw μ x) =
      if x = γ 0 then ∫⁻ ω, f ω ∂μ else 0 := by
  classical
  let g : State d → ℝ≥0∞ := fun s => if s.2 = γ 0 then f s.1 else 0
  have hg : Measurable g := Measurable.ite
    (measurableSet_eq_fun measurable_snd measurable_const) (hf.comp measurable_fst) measurable_const
  have heq : prefixObservable 0 γ f = fun z => g (z 0) := by
    funext z
    simp [prefixObservable, prefixMatches, g]
  rw [heq, ← lintegral_map hg (measurable_pi_apply 0), walkStateLaw_initial,
    walkInitialLaw, lintegral_map (g := fun ω : Environment d => (ω, x)) hg
      (measurable_id.prodMk measurable_const)]
  by_cases hx : x = γ 0 <;> simp [g, hx]

lemma prefix_lintegral {d : ℕ} (μ : Measure (Environment d)) [IsProbabilityMeasure μ]
    (x : Site d) (n : ℕ) (γ : ℕ → Site d) (f : Environment d → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ z, prefixObservable n γ f z ∂walkStateLaw μ x) =
      if x = γ 0 then ∫⁻ ω, pathWeight n γ ω * f ω ∂μ else 0 := by
  induction n generalizing f with
  | zero => simpa [pathWeight] using prefix_lintegral_zero μ x γ f hf
  | succ n ih =>
    rw [prefix_lintegral_succ μ x n γ f hf,
      ih (fun ω => entryWeight ω (γ n) (γ (n+1)) * f ω)
        ((measurable_entryWeight (γ n) (γ (n+1))).mul hf)]
    simp only [pathWeight_succ, mul_assoc]

noncomputable def stateLaw {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x : Site d) : Measure (ℕ → State d) := walkStateLaw (environmentLaw μ) x

lemma annealed_eq_map_stateLaw {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x : Site d) : annealed μ x = (stateLaw μ x).map (fun z n => (z n).2) := rfl

noncomputable def walkLaw {d : ℕ} (μ : Measure (Environment d)) [IsProbabilityMeasure μ]
    (x : Site d) : Measure (Path d) := (walkStateLaw μ x).map (fun z n => (z n).2)

instance {d : ℕ} (μ : Measure (Environment d)) [IsProbabilityMeasure μ] (x : Site d) :
    IsProbabilityMeasure (walkLaw μ x) := by
  apply probabilityMeasure_map
  exact (Measurable.of_eval (fun n => measurable_snd.comp (measurable_pi_apply n))).aemeasurable

def pathCylinder {d : ℕ} (n : ℕ) (γ : ℕ → Site d) : Set (Path d) :=
  {X | ∀ i ≤ n, X i = γ i}

lemma measurableSet_pathCylinder {d : ℕ} (n : ℕ) (γ : ℕ → Site d) :
    MeasurableSet (pathCylinder n γ) := by
  simp only [pathCylinder, Set.ofPred_forall]
  exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun _ =>
    measurableSet_eq_fun (measurable_pi_apply i) measurable_const))

lemma walkLaw_cylinder {d : ℕ} (μ : Measure (Environment d)) [IsProbabilityMeasure μ]
    (x : Site d) (n : ℕ) (γ : ℕ → Site d) :
    walkLaw μ x (pathCylinder n γ) =
      if x = γ 0 then ∫⁻ ω, pathWeight n γ ω ∂μ else 0 := by
  classical
  have hp := prefix_lintegral μ x n γ (fun _ => 1) measurable_const
  have hobs : prefixObservable n γ (fun _ => 1) =
      {z : ℕ → State d | prefixMatches n γ z}.indicator (fun _ => 1) := by
    funext z
    simp [prefixObservable, Set.indicator]
  rw [hobs] at hp
  change (∫⁻ z, {z' : ℕ → State d | prefixMatches n γ z'}.indicator 1 z
    ∂walkStateLaw μ x) = _ at hp
  rw [lintegral_indicator_one (measurableSet_prefixMatches n γ)] at hp
  rw [walkLaw, Measure.map_apply (f := fun z : ℕ → State d => fun n => (z n).2)
    (Measurable.of_eval (fun n => measurable_snd.comp (measurable_pi_apply n)))
    (measurableSet_pathCylinder n γ)]
  simpa only [pathCylinder, prefixMatches, Set.preimage_ofPred_eq, mul_one] using hp

lemma annealed_cylinder {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x : Site d) (n : ℕ) (γ : ℕ → Site d) :
    annealed μ x (pathCylinder n γ) =
      if x = γ 0 then ∫⁻ ω, pathWeight n γ ω ∂environmentLaw μ else 0 :=
  walkLaw_cylinder (environmentLaw μ) x n γ

lemma stepVector_injective {d : ℕ} : Function.Injective (@stepVector d) := by
  rintro ⟨i, b⟩ ⟨j, c⟩ h
  have hij : i = j := by
    by_contra hn
    have hh := congr_fun h i
    cases b <;> simp [stepVector, hn] at hh
  subst j
  have hh := congr_fun h i
  cases b <;> cases c <;> simp_all [stepVector]

lemma entryWeight_step {d : ℕ} (ω : Environment d) (x : Site d) (e : Step d) :
    entryWeight ω x (x + stepVector e) = ENNReal.ofReal ((ω x).val e) := by
  simp [entryWeight, stepVector_injective.eq_iff]

noncomputable def quenchedKernel (d : ℕ) : Kernel (State d) (Path d) :=
  ((Kernel.traj (X := fun _ => State d) (historyKernel d) 0).comap
    (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => State d)).symm
    (MeasurableEquiv.measurable _)).map (fun z n => (z n).2)

instance (d : ℕ) : IsMarkovKernel (quenchedKernel d) := by
  unfold quenchedKernel
  apply Kernel.IsMarkovKernel.map
  exact Measurable.of_eval (fun n => measurable_snd.comp (measurable_pi_apply n))

lemma walkLaw_apply {d : ℕ} (μ : Measure (Environment d)) [IsProbabilityMeasure μ]
    (x : Site d) {s : Set (Path d)} (hs : MeasurableSet s) :
    walkLaw μ x s = ∫⁻ ω, quenchedKernel d (ω,x) s ∂μ := by
  let ψ : (ℕ → State d) → Path d := fun z n => (z n).2
  have hψ : Measurable ψ :=
    Measurable.of_eval (fun n => measurable_snd.comp (measurable_pi_apply n))
  let e := MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => State d)
  change ((Kernel.trajMeasure (X := fun _ => State d) (walkInitialLaw μ x) (historyKernel d)).map ψ) s = _
  rw [Kernel.trajMeasure, Measure.map_comp _ _ hψ,
    Measure.bind_apply hs (Kernel.measurable _).aemeasurable]
  rw [lintegral_map (Kernel.measurable_coe _ hs) e.symm.measurable]
  rw [walkInitialLaw, lintegral_map
    (f := fun a : State d => ((Kernel.traj (historyKernel d) 0).map ψ) (e.symm a) s)
    (g := fun ω : Environment d => (ω,x))
    ((Kernel.measurable_coe _ hs).comp e.symm.measurable)
    (measurable_id.prodMk measurable_const)]
  apply lintegral_congr
  intro ω
  change (((Kernel.traj (historyKernel d) 0).map ψ) (e.symm (ω,x))) s =
    (((Kernel.traj (historyKernel d) 0).comap e.symm e.symm.measurable).map ψ) (ω,x) s
  rw [Kernel.map_apply _ hψ, Kernel.map_apply _ hψ, Kernel.comap_apply]

lemma walkLaw_dirac {d : ℕ} (ω : Environment d) (x : Site d) :
    walkLaw (Measure.dirac ω) x = quenchedKernel d (ω,x) := by
  ext s hs
  rw [walkLaw_apply _ _ hs, lintegral_dirac' _]
  exact (Kernel.measurable_coe _ hs).comp (measurable_id.prodMk measurable_const)

lemma annealed_apply {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x : Site d) {s : Set (Path d)} (hs : MeasurableSet s) :
    annealed μ x s = ∫⁻ ω, quenchedKernel d (ω,x) s ∂environmentLaw μ :=
  walkLaw_apply (environmentLaw μ) x hs

lemma quenchedKernel_cylinder {d : ℕ} (ω : Environment d) (x : Site d)
    (n : ℕ) (γ : ℕ → Site d) :
    quenchedKernel d (ω,x) (pathCylinder n γ) =
      if x = γ 0 then pathWeight n γ ω else 0 := by
  rw [← walkLaw_dirac, walkLaw_cylinder, lintegral_dirac' _ (measurable_pathWeight n γ)]

lemma measure_eq_of_prefix {A : Type*} [MeasurableSpace A]
    (μ ν : Measure (ℕ → A)) [IsFiniteMeasure μ]
    (h : ∀ n, μ.map (frestrictLe n) = ν.map (frestrictLe n)) : μ = ν := by
  let P : ∀ I : Finset ℕ, Measure (I → A) := fun I => μ.map I.restrict
  have hP : IsProjectiveMeasureFamily (α := fun _ : ℕ => A) P := by
    intro I J hJI
    dsimp [P]
    have h1 : Measurable (Finset.restrict₂ (π := fun _ : ℕ => A) hJI) :=
      Measurable.of_eval (fun i => measurable_pi_apply (⟨i, hJI i.property⟩ : I))
    have h2 : Measurable (I.restrict : (ℕ → A) → (I → A)) :=
      Measurable.of_eval (fun i => measurable_pi_apply (i : ℕ))
    rw [Measure.map_map h1 h2]
    rfl
  have hμ : IsProjectiveLimit (α := fun _ : ℕ => A) μ P := fun I => rfl
  have hν : IsProjectiveLimit (α := fun _ : ℕ => A) ν P := (isProjectiveLimit_nat_iff hP ν).2 (fun n => (h n).symm)
  exact hμ.unique hν

lemma pathMeasure_ext {d : ℕ} (μ ν : Measure (Path d)) [IsFiniteMeasure μ]
    (h : ∀ n γ, μ (pathCylinder n γ) = ν (pathCylinder n γ)) : μ = ν := by
  classical
  apply measure_eq_of_prefix
  intro n
  apply Measure.ext_of_singleton
  intro a
  let γ : ℕ → Site d := fun i => if hi : i ∈ Finset.Iic n then a ⟨i,hi⟩ else 0
  have heq : (frestrictLe n : Path d → (Finset.Iic n → Site d)) ⁻¹' {a} = pathCylinder n γ := by
    ext X
    simp only [Set.mem_preimage, Set.mem_singleton_iff, pathCylinder, Set.mem_ofPred_eq]
    constructor
    · intro hh i hi
      have hh' := congr_fun hh ⟨i, Finset.mem_Iic.mpr hi⟩
      simpa [γ, hi, frestrictLe] using hh'
    · intro hh
      funext i
      have hi := Finset.mem_Iic.mp i.property
      simpa [γ, hi, frestrictLe] using hh i hi
  rw [Measure.map_apply (measurable_frestrictLe n) (measurableSet_singleton a),
    Measure.map_apply (measurable_frestrictLe n) (measurableSet_singleton a), heq]
  exact h n γ

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

def shiftEnvironment {d : ℕ} (z : Site d) (ω : Environment d) : Environment d :=
  fun x => ω (x+z)

def shiftPath {d : ℕ} (z : Site d) (X : Path d) : Path d := fun n => X n + z

lemma measurable_shiftEnvironment {d : ℕ} (z : Site d) :
    Measurable (shiftEnvironment z) := Measurable.of_eval (fun x => measurable_pi_apply (x+z))

lemma measurable_shiftPath {d : ℕ} (z : Site d) : Measurable (shiftPath z) := by
  apply Measurable.of_eval
  intro n
  exact (show Measurable (fun X : Path d => X n) from measurable_pi_apply n).add_const z

lemma environmentLaw_shift {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (z : Site d) : (environmentLaw μ).map (shiftEnvironment z) = environmentLaw μ := by
  let e := MeasurableEquiv.piCongrLeft (fun _ : Site d => Row d) (Equiv.addRight z)
  have h : (environmentLaw μ).map e = environmentLaw μ :=
    Measure.infinitePi_map_piCongrLeft (fun _ : Site d => μ) (Equiv.addRight z)
  have hh := congrArg (fun ξ : Measure (Environment d) => ξ.map e.symm) h
  have heq : (e.symm : Environment d → Environment d) = shiftEnvironment z := by
    funext ω x
    rfl
  rw [e.map_symm_map, heq] at hh
  exact hh.symm

lemma entryWeight_shift {d : ℕ} (z : Site d) (ω : Environment d) (x y : Site d) :
    entryWeight (shiftEnvironment z ω) x y = entryWeight ω (x+z) (y+z) := by
  simp only [entryWeight, shiftEnvironment]
  apply Finset.sum_congr rfl
  intro e he
  have h : x + z + stepVector e = y + z ↔ x + stepVector e = y := by
    rw [add_right_comm, add_left_inj]
  simp only [h]

lemma pathWeight_shift {d : ℕ} (z : Site d) (ω : Environment d) (n : ℕ) (γ : Path d) :
    pathWeight n γ (shiftEnvironment z ω) = pathWeight n (shiftPath z γ) ω := by
  simp only [pathWeight, shiftPath, entryWeight_shift]

lemma pathWeight_integral_shift {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (z : Site d) (n : ℕ) (γ : Path d) :
    (∫⁻ ω, pathWeight n (shiftPath z γ) ω ∂environmentLaw μ) =
      ∫⁻ ω, pathWeight n γ ω ∂environmentLaw μ := by
  calc
    _ = ∫⁻ ω, pathWeight n γ (shiftEnvironment z ω) ∂environmentLaw μ :=
      lintegral_congr (fun ω => (pathWeight_shift z ω n γ).symm)
    _ = ∫⁻ ω, pathWeight n γ ω ∂(environmentLaw μ).map (shiftEnvironment z) :=
      (lintegral_map (measurable_pathWeight n γ) (measurable_shiftEnvironment z)).symm
    _ = _ := by rw [environmentLaw_shift]

lemma shiftPath_preimage_cylinder {d : ℕ} (z : Site d) (n : ℕ) (γ : Path d) :
    shiftPath z ⁻¹' pathCylinder n γ = pathCylinder n (shiftPath (-z) γ) := by
  ext X
  simp only [Set.mem_preimage, pathCylinder, shiftPath, Set.mem_ofPred_eq]
  simp only [eq_add_neg_iff_add_eq]

lemma annealed_shift {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x z : Site d) : (annealed μ x).map (shiftPath z) = annealed μ (x+z) := by
  apply pathMeasure_ext
  intro n γ
  rw [Measure.map_apply (measurable_shiftPath z) (measurableSet_pathCylinder n γ),
    shiftPath_preimage_cylinder, annealed_cylinder, annealed_cylinder,
    pathWeight_integral_shift]
  simp only [shiftPath, eq_add_neg_iff_add_eq]

def tailPath {d : ℕ} (n : ℕ) (X : Path d) : Path d := fun k => X (n+k)

lemma measurable_tailPath {d : ℕ} (n : ℕ) : Measurable (@tailPath d n) :=
  Measurable.of_eval (fun k => measurable_pi_apply (n+k))

def concatPath {d : ℕ} (n : ℕ) (γ δ : Path d) : Path d :=
  fun k => if k < n then γ k else δ (k-n)

lemma concatPath_before {d : ℕ} (n : ℕ) (γ δ : Path d) (h : γ n = δ 0)
    {i : ℕ} (hi : i ≤ n) : concatPath n γ δ i = γ i := by
  rcases hi.eq_or_lt with rfl | hi
  · simp [concatPath, h]
  · simp [concatPath, hi]

lemma concatPath_after {d : ℕ} (n : ℕ) (γ δ : Path d) (i : ℕ) :
    concatPath n γ δ (n+i) = δ i := by simp [concatPath]

lemma pathWeight_concat {d : ℕ} (n m : ℕ) (γ δ : Path d) (h : γ n = δ 0)
    (ω : Environment d) :
    pathWeight (n+m) (concatPath n γ δ) ω = pathWeight n γ ω * pathWeight m δ ω := by
  unfold pathWeight
  rw [Finset.prod_range_add]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    rw [concatPath_before n γ δ h (Nat.le_of_lt (Finset.mem_range.mp hi)),
      concatPath_before n γ δ h (Finset.mem_range.mp hi)]
  · apply Finset.prod_congr rfl
    intro i hi
    simp only [concatPath_after, Nat.add_assoc]

lemma prefix_tail_inter {d : ℕ} (n m : ℕ) (γ δ : Path d) :
    pathCylinder n γ ∩ tailPath n ⁻¹' pathCylinder m δ =
      if γ n = δ 0 then pathCylinder (n+m) (concatPath n γ δ) else ∅ := by
  classical
  by_cases h : γ n = δ 0
  · rw [ite_eq_left h]
    ext X
    constructor
    · rintro ⟨hγ,hδ⟩ i hi
      by_cases hin : i < n
      · simpa [concatPath, hin] using hγ i (le_of_lt hin)
      · have hh := hδ (i-n) (by omega)
        simpa [tailPath, concatPath, hin, Nat.add_sub_of_le (Nat.le_of_not_gt hin)] using hh
    · intro hh
      constructor
      · intro i hi
        rw [hh i (by omega), concatPath_before n γ δ h hi]
      · intro i hi
        change X (n+i) = δ i
        rw [hh (n+i) (by omega), concatPath_after]
  · rw [ite_eq_right h]
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro X ⟨hγ,hδ⟩
    have h1 := hγ n le_rfl
    have h2 := hδ 0 (Nat.zero_le m)
    exact h (h1.symm.trans (by simpa [tailPath] using h2))

lemma quenched_prefix_tail {d : ℕ} (ω : Environment d) (x : Site d) (n : ℕ) (γ : Path d) :
    ((quenchedKernel d (ω,x)).restrict (pathCylinder n γ)).map (tailPath n) =
      (if x = γ 0 then pathWeight n γ ω else 0) • quenchedKernel d (ω,γ n) := by
  classical
  apply pathMeasure_ext
  intro m δ
  rw [Measure.map_apply (measurable_tailPath n) (measurableSet_pathCylinder m δ),
    Measure.restrict_apply ((measurable_tailPath n) (measurableSet_pathCylinder m δ)),
    Set.inter_comm, prefix_tail_inter, Measure.smul_apply, smul_eq_mul]
  by_cases h : γ n = δ 0
  · rw [ite_eq_left h, quenchedKernel_cylinder, quenchedKernel_cylinder, ite_eq_left h,
      concatPath_before n γ δ h (Nat.zero_le n), pathWeight_concat n m γ δ h]
    split_ifs <;> simp
  · rw [ite_eq_right h, measure_empty, quenchedKernel_cylinder, ite_eq_right h, mul_zero]

lemma prefix_preimage_singleton {d : ℕ} (n : ℕ) (γ : Path d) :
    (frestrictLe n : Path d → (Finset.Iic n → Site d)) ⁻¹' {frestrictLe n γ} =
      pathCylinder n γ := by
  ext X
  simp only [Set.mem_preimage, Set.mem_singleton_iff, pathCylinder, Set.mem_ofPred_eq]
  constructor
  · intro h i hi
    exact congr_fun h ⟨i, Finset.mem_Iic.mpr hi⟩
  · intro h
    funext i
    exact h i (Finset.mem_Iic.mp i.property)

lemma cylinder_measure_eq_of_prefixMap {d : ℕ} {μ ν : Measure (Path d)} (n : ℕ)
    (h : μ.map (frestrictLe n) = ν.map (frestrictLe n)) (γ : Path d) :
    μ (pathCylinder n γ) = ν (pathCylinder n γ) := by
  have hh := congrArg (fun ξ : Measure (Finset.Iic n → Site d) => ξ {frestrictLe n γ}) h
  simpa only [Measure.map_apply (measurable_frestrictLe n) (measurableSet_singleton _),
    prefix_preimage_singleton] using hh

lemma prefixMap_mono {d : ℕ} {μ ν : Measure (Path d)} {n m : ℕ} (hnm : n ≤ m)
    (h : μ.map (frestrictLe m) = ν.map (frestrictLe m)) :
    μ.map (frestrictLe n) = ν.map (frestrictLe n) := by
  have hh := congrArg (fun ξ : Measure (Finset.Iic m → Site d) =>
    ξ.map (frestrictLe₂ (π := fun _ : ℕ => Site d) hnm)) h
  simpa only [Measure.map_map (measurable_frestrictLe₂ hnm) (measurable_frestrictLe m),
    frestrictLe₂_comp_frestrictLe] using hh

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

def avoidsThrough {d : ℕ} (K : Set (Site d)) (n : ℕ) : Set (Path d) :=
  {X | ∀ i ≤ n, X i ∉ K}

def avoids {d : ℕ} (K : Set (Site d)) : Set (Path d) := {X | ∀ i, X i ∉ K}

lemma measurableSet_avoidsThrough {d : ℕ} (K : Set (Site d)) (n : ℕ) :
    MeasurableSet (avoidsThrough K n) := by
  simp only [avoidsThrough, Set.ofPred_forall]
  exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun _ =>
    (show Measurable (fun X : Path d => X i) from measurable_pi_apply i)
      (Set.to_countable K).measurableSet.compl))

lemma measurableSet_avoids {d : ℕ} (K : Set (Site d)) : MeasurableSet (avoids K) := by
  simp only [avoids, Set.ofPred_forall]
  exact MeasurableSet.iInter (fun i =>
    (show Measurable (fun X : Path d => X i) from measurable_pi_apply i)
      (Set.to_countable K).measurableSet.compl)

lemma avoidsThrough_antitone {d : ℕ} (K : Set (Site d)) : Antitone (avoidsThrough K) := by
  intro n m hnm X hX i hi
  exact hX i (hi.trans hnm)

open Classical in
lemma cylinder_inter_avoidsThrough {d : ℕ} (K : Set (Site d)) (n : ℕ) (γ : Path d) :
    pathCylinder n γ ∩ avoidsThrough K n =
      if ∀ i ≤ n, γ i ∉ K then pathCylinder n γ else ∅ := by
  classical
  by_cases h : ∀ i ≤ n, γ i ∉ K
  · rw [ite_eq_left h]
    apply Set.inter_eq_left.mpr
    intro X hX i hi
    rw [hX i hi]
    exact h i hi
  · rw [ite_eq_right h]
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro X ⟨hX,hK⟩
    apply h
    intro i hi
    rw [← hX i hi]
    exact hK i hi

lemma pathWeight_congr_rows {d : ℕ} (ω ω' : Environment d) (n : ℕ) (γ : Path d)
    (h : ∀ i < n, ω (γ i) = ω' (γ i)) : pathWeight n γ ω = pathWeight n γ ω' := by
  apply Finset.prod_congr rfl
  intro i hi
  simp only [entryWeight, h i (Finset.mem_range.mp hi)]

lemma quenched_avoid_prefixMap {d : ℕ} (K : Set (Site d)) (ω ω' : Environment d)
    (h : ∀ y ∉ K, ω y = ω' y) (x : Site d) (n : ℕ) :
    ((quenchedKernel d (ω,x)).restrict (avoidsThrough K n)).map (frestrictLe n) =
      ((quenchedKernel d (ω',x)).restrict (avoidsThrough K n)).map (frestrictLe n) := by
  classical
  apply Measure.ext_of_singleton
  intro a
  let γ : Path d := fun i => if hi : i ∈ Finset.Iic n then a ⟨i,hi⟩ else 0
  have hγ : frestrictLe n γ = a := by
    funext i
    change (if hi : (i : ℕ) ∈ Finset.Iic n then a ⟨i,hi⟩ else 0) = a i
    rw [dite_eq_left i.property]
  rw [← hγ, Measure.map_apply (measurable_frestrictLe n) (measurableSet_singleton _),
    Measure.map_apply (measurable_frestrictLe n) (measurableSet_singleton _),
    prefix_preimage_singleton, Measure.restrict_apply (measurableSet_pathCylinder n γ),
    Measure.restrict_apply (measurableSet_pathCylinder n γ), cylinder_inter_avoidsThrough]
  by_cases hK : ∀ i ≤ n, γ i ∉ K
  · rw [ite_eq_left hK, quenchedKernel_cylinder, quenchedKernel_cylinder,
      pathWeight_congr_rows ω ω' n γ (fun i hi => h _ (hK i (le_of_lt hi)))]
  · rw [ite_eq_right hK]
    simp only [measure_empty]

lemma quenched_restrict_avoids_eq {d : ℕ} (K : Set (Site d)) (ω ω' : Environment d)
    (h : ∀ y ∉ K, ω y = ω' y) (x : Site d) :
    (quenchedKernel d (ω,x)).restrict (avoids K) =
      (quenchedKernel d (ω',x)).restrict (avoids K) := by
  apply pathMeasure_ext
  intro n γ
  rw [Measure.restrict_apply (measurableSet_pathCylinder n γ),
    Measure.restrict_apply (measurableSet_pathCylinder n γ)]
  let s : ℕ → Set (Path d) := fun m => pathCylinder n γ ∩ avoidsThrough K (n+m)
  have hsm : ∀ m, MeasurableSet (s m) := fun m =>
    (measurableSet_pathCylinder n γ).inter (measurableSet_avoidsThrough K (n+m))
  have hsa : Antitone s := by
    intro i j hij
    exact Set.inter_subset_inter_right _ (avoidsThrough_antitone K (Nat.add_le_add_left hij n))
  have hs : (⋂ m, s m) = pathCylinder n γ ∩ avoids K := by
    ext X
    simp only [Set.mem_iInter, Set.mem_inter_iff, s]
    constructor
    · intro hX
      refine ⟨(hX 0).1, fun i => ?_⟩
      exact (hX i).2 i (Nat.le_add_left i n)
    · rintro ⟨hX,hK⟩ m
      exact ⟨hX, fun i _ => hK i⟩
  have he : ∀ m, quenchedKernel d (ω,x) (s m) = quenchedKernel d (ω',x) (s m) := by
    intro m
    have hh := cylinder_measure_eq_of_prefixMap n
      (prefixMap_mono (Nat.le_add_right n m) (quenched_avoid_prefixMap K ω ω' h x (n+m))) γ
    simpa only [Measure.restrict_apply (measurableSet_pathCylinder n γ)] using hh
  have hω := tendsto_measure_iInter_atTop
    (fun m => (hsm m).nullMeasurableSet (μ := quenchedKernel d (ω,x))) hsa
    ⟨0, measure_ne_top _ _⟩
  have hω' := tendsto_measure_iInter_atTop
    (fun m => (hsm m).nullMeasurableSet (μ := quenchedKernel d (ω',x))) hsa
    ⟨0, measure_ne_top _ _⟩
  rw [hs] at hω hω'
  have heq : (quenchedKernel d (ω,x) ∘ s) = (quenchedKernel d (ω',x) ∘ s) := funext he
  rw [heq] at hω
  exact tendsto_nhds_unique hω hω'

noncomputable def maskEnvironment {d : ℕ} (K : Set (Site d)) (r : Row d)
    (ω : Environment d) : Environment d := by
  classical
  exact fun y => if y ∈ K then r else ω y

lemma measurable_maskEnvironment {d : ℕ} (K : Set (Site d)) (r : Row d) :
    @Measurable (Environment d) (Environment d) (rowSigma Kᶜ) _ (maskEnvironment K r) := by
  classical
  apply @Measurable.of_eval (Environment d) (Site d) (fun _ => Row d) (rowSigma Kᶜ) _
  intro y
  by_cases hy : y ∈ K
  · simpa only [maskEnvironment, ite_eq_left hy] using
      (measurable_const : @Measurable (Environment d) (Row d) (rowSigma Kᶜ) _ (fun _ => r))
  · simpa only [maskEnvironment, ite_eq_right hy] using
      (measurable_row (s := Kᶜ) (x := y) hy)

lemma measurable_quenched_avoids_on_rows {d : ℕ} (K : Set (Site d)) (r : Row d)
    (x : Site d) {E : Set (Path d)} (hE : MeasurableSet E) :
    @Measurable (Environment d) ℝ≥0∞ (rowSigma Kᶜ) _
      (fun ω => quenchedKernel d (ω,x) (E ∩ avoids K)) := by
  have hmeas := (Kernel.measurable_coe (quenchedKernel d) (hE.inter (measurableSet_avoids K))).comp
    ((measurable_maskEnvironment K r).prodMk measurable_const (g := fun _ => x))
  suffices heq : (fun ω => quenchedKernel d (ω,x) (E ∩ avoids K)) =
      (fun ω => quenchedKernel d (maskEnvironment K r ω,x) (E ∩ avoids K)) by
    rw [heq]
    exact hmeas
  funext ω
  have he := congrArg (fun ξ : Measure (Path d) => ξ E)
    (quenched_restrict_avoids_eq K (maskEnvironment K r ω) ω
      (fun y hy => by simp [maskEnvironment, hy]) x)
  simpa only [Measure.restrict_apply hE] using he.symm

lemma measurable_entryWeight_on_rows {d : ℕ} (K : Set (Site d)) (x y : Site d) (hx : x ∈ K) :
    @Measurable (Environment d) ℝ≥0∞ (rowSigma K) _ (fun ω => entryWeight ω x y) := by
  apply Finset.measurable_sum
  intro e he
  split_ifs
  · exact ((measurable_pi_apply e).comp
      (measurable_subtype_coe.comp (measurable_row hx))).ennreal_ofReal
  · exact measurable_const

lemma measurable_pathWeight_on_rows {d : ℕ} (K : Set (Site d)) (n : ℕ) (γ : Path d)
    (hK : ∀ i < n, γ i ∈ K) :
    @Measurable (Environment d) ℝ≥0∞ (rowSigma K) _ (pathWeight n γ) := by
  apply Finset.measurable_prod
  intro i hi
  exact measurable_entryWeight_on_rows K _ _ (hK i (Finset.mem_range.mp hi))

lemma path_departure_transfer {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (K : Set (Site d)) (n : ℕ) (γ : Path d) (hK : ∀ i < n, γ i ∈ K)
    (f : Environment d → ℝ≥0∞)
    (hf : @Measurable (Environment d) ℝ≥0∞ (rowSigma Kᶜ) _ f) :
    (∫⁻ ω, pathWeight n γ ω * f ω ∂environmentLaw μ) =
      (∫⁻ ω, pathWeight n γ ω ∂environmentLaw μ) * ∫⁻ ω, f ω ∂environmentLaw μ := by
  exact lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    (rowSigma_le _) (rowSigma_le _)
    (independent_rowSigma μ disjoint_compl_right)
    (measurable_pathWeight_on_rows K n γ hK) hf

lemma quenched_prefix_tail_apply {d : ℕ} (ω : Environment d) (x : Site d) (n : ℕ)
    (γ : Path d) {E : Set (Path d)} (hE : MeasurableSet E) :
    quenchedKernel d (ω,x) (pathCylinder n γ ∩ tailPath n ⁻¹' E) =
      (if x = γ 0 then pathWeight n γ ω else 0) * quenchedKernel d (ω,γ n) E := by
  have h := congrArg (fun ξ : Measure (Path d) => ξ E) (quenched_prefix_tail ω x n γ)
  rw [Measure.map_apply (measurable_tailPath n) hE,
    Measure.restrict_apply ((measurable_tailPath n) hE), Set.inter_comm,
    Measure.smul_apply, smul_eq_mul] at h
  exact h

lemma annealed_fresh_prefix_tail {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (K : Set (Site d)) (x : Site d) (n : ℕ) (γ : Path d) (hK : ∀ i < n, γ i ∈ K)
    {E : Set (Path d)} (hE : MeasurableSet E) :
    annealed μ x (pathCylinder n γ ∩ tailPath n ⁻¹' (E ∩ avoids K)) =
      annealed μ x (pathCylinder n γ) * annealed μ (γ n) (E ∩ avoids K) := by
  classical
  have hF : MeasurableSet (E ∩ avoids K) := hE.inter (measurableSet_avoids K)
  rw [annealed_apply μ x ((measurableSet_pathCylinder n γ).inter ((measurable_tailPath n) hF))]
  simp_rw [quenched_prefix_tail_apply _ _ _ _ hF]
  rw [annealed_cylinder]
  by_cases hx : x = γ 0
  · simp only [ite_eq_left hx]
    let r : Row d := Classical.choice (nonempty_of_isProbabilityMeasure μ)
    rw [path_departure_transfer μ K n γ hK _ (measurable_quenched_avoids_on_rows K r _ hE),
      ← annealed_apply μ (γ n) hF]
  · simp only [ite_eq_right hx, zero_mul, lintegral_zero]

lemma path_weights_disjoint {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (n m : ℕ) (γ δ : Path d) (h : ∀ i < n, ∀ j < m, γ i ≠ δ j) :
    (∫⁻ ω, pathWeight n γ ω * pathWeight m δ ω ∂environmentLaw μ) =
      (∫⁻ ω, pathWeight n γ ω ∂environmentLaw μ) *
        (∫⁻ ω, pathWeight m δ ω ∂environmentLaw μ) := by
  let K : Set (Site d) := {y | ∃ i < n, γ i = y}
  apply path_departure_transfer μ K n γ (fun i hi => ⟨i,hi,rfl⟩)
  apply measurable_pathWeight_on_rows
  intro j hj
  rintro ⟨i,hi,hij⟩
  exact h i hi j hj hij

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

def height {d : ℕ} (v : Fin d → ℝ) (x : Site d) : ℝ := ∑ i, (x i : ℝ) * v i

lemma height_zero {d : ℕ} (v : Fin d → ℝ) : height v 0 = 0 := by simp [height]

lemma height_add {d : ℕ} (v : Fin d → ℝ) (x y : Site d) :
    height v (x+y) = height v x + height v y := by
  simp only [height, Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]

lemma height_neg {d : ℕ} (v : Fin d → ℝ) (x : Site d) :
    height v (-x) = -height v x := by simp [height, Finset.sum_neg_distrib]

def neverBelow {d : ℕ} (v : Fin d → ℝ) (a : ℝ) : Set (Path d) :=
  {X | ∀ n, a ≤ height v (X n)}

def nonBacktracking {d : ℕ} (v : Fin d → ℝ) : Set (Path d) := neverBelow v 0

lemma measurableSet_neverBelow {d : ℕ} (v : Fin d → ℝ) (a : ℝ) :
    MeasurableSet (neverBelow v a) := by
  simp only [neverBelow, Set.ofPred_forall]
  exact MeasurableSet.iInter (fun n => measurableSet_le measurable_const
    ((measurable_of_countable (height v)).comp (measurable_pi_apply n)))

lemma measurableSet_nonBacktracking {d : ℕ} (v : Fin d → ℝ) :
    MeasurableSet (nonBacktracking v) := measurableSet_neverBelow v 0

lemma shiftPath_preimage_neverBelow {d : ℕ} (v : Fin d → ℝ) (z : Site d) :
    shiftPath z ⁻¹' neverBelow v (height v z) = nonBacktracking v := by
  ext X
  simp only [Set.mem_preimage, neverBelow, nonBacktracking, Set.mem_ofPred_eq,
    shiftPath, height_add, le_add_iff_nonneg_left]

lemma annealed_neverBelow_start {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (v : Fin d → ℝ) (x : Site d) :
    annealed μ x (neverBelow v (height v x)) = annealed μ 0 (nonBacktracking v) := by
  have h := congrArg (fun ξ : Measure (Path d) => ξ (neverBelow v (height v x)))
    (annealed_shift μ 0 x)
  rw [Measure.map_apply (measurable_shiftPath x) (measurableSet_neverBelow v _),
    shiftPath_preimage_neverBelow, zero_add] at h
  exact h.symm

lemma annealed_prefix_tail_null {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x : Site d) (n : ℕ) (γ : Path d) {E : Set (Path d)} (hE : MeasurableSet E)
    (hzero : annealed μ (γ n) E = 0) :
    annealed μ x (pathCylinder n γ ∩ tailPath n ⁻¹' E) = 0 := by
  have hae : ∀ᵐ ω ∂environmentLaw μ, quenchedKernel d (ω,γ n) E = 0 := by
    apply (lintegral_eq_zero_iff
      ((Kernel.measurable_coe _ hE).comp (measurable_id.prodMk measurable_const))).mp
    change (∫⁻ ω, quenchedKernel d (ω,γ n) E ∂environmentLaw μ) = 0
    rw [← annealed_apply μ (γ n) hE]
    exact hzero
  rw [annealed_apply μ x ((measurableSet_pathCylinder n γ).inter ((measurable_tailPath n) hE))]
  calc
    _ = ∫⁻ _ : Environment d, (0 : ℝ≥0∞) ∂environmentLaw μ := by
      apply lintegral_congr_ae
      filter_upwards [hae] with ω hω
      rw [quenched_prefix_tail_apply _ _ _ _ hE, hω, mul_zero]
    _ = 0 := lintegral_zero

def extendPrefix {d : ℕ} (n : ℕ) (a : Finset.Iic n → Site d) : Path d :=
  fun i => if hi : i ∈ Finset.Iic n then a ⟨i,hi⟩ else 0

lemma extendPrefix_apply {d : ℕ} (n : ℕ) (a : Finset.Iic n → Site d) {i : ℕ} (hi : i ≤ n) :
    extendPrefix n a i = a ⟨i, Finset.mem_Iic.mpr hi⟩ := by
  simp only [extendPrefix, dite_eq_left (Finset.mem_Iic.mpr hi)]

lemma restrict_extendPrefix {d : ℕ} (n : ℕ) (a : Finset.Iic n → Site d) :
    frestrictLe n (extendPrefix n a) = a := by
  funext i
  exact extendPrefix_apply n a (Finset.mem_Iic.mp i.property)

lemma set_eq_iUnion_prefix_inter {d : ℕ} (E : Set (Path d)) (n : ℕ) :
    E = ⋃ a : Finset.Iic n → Site d, E ∩ pathCylinder n (extendPrefix n a) := by
  ext X
  simp only [Set.mem_iUnion, Set.mem_inter_iff]
  constructor
  · intro hX
    refine ⟨frestrictLe n X, hX, fun i hi => ?_⟩
    rw [extendPrefix_apply n _ hi]
    rfl
  · rintro ⟨a,hX,_⟩
    exact hX

lemma measure_zero_of_prefix_inter {d : ℕ} (μ : Measure (Path d)) (n : ℕ)
    (E : Set (Path d)) (h : ∀ a : Finset.Iic n → Site d,
      μ (E ∩ pathCylinder n (extendPrefix n a)) = 0) : μ E = 0 := by
  rw [set_eq_iUnion_prefix_inter E n]
  exact measure_iUnion_null h

lemma annealed_tail_start_null {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (y x : Site d) (n : ℕ) {E : Set (Path d)} (hE : MeasurableSet E)
    (hzero : annealed μ x E = 0) :
    annealed μ y ({X | X n = x} ∩ tailPath n ⁻¹' E) = 0 := by
  classical
  apply measure_zero_of_prefix_inter _ n
  intro a
  let γ := extendPrefix n a
  by_cases hx : γ n = x
  · apply measure_mono_null _ (annealed_prefix_tail_null μ y n γ hE (by simpa [hx] using hzero))
    rintro X ⟨⟨_,hX⟩,hC⟩
    exact ⟨hC,hX⟩
  · have he : ({X : Path d | X n = x} ∩ tailPath n ⁻¹' E) ∩ pathCylinder n γ = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro X ⟨⟨hX,_⟩,hC⟩
      exact hx ((hC n le_rfl).symm.trans hX)
    rw [he, measure_empty]

lemma escape_subset_globalMinimum_suffix {d : ℕ} (v : Fin d → ℝ) :
    escape v ⊆ ⋃ n : ℕ, ⋃ x : Site d,
      {X | X n = x} ∩ tailPath n ⁻¹' neverBelow v (height v x) := by
  intro X hX
  have ht : Tendsto (fun n => height v (X n)) cofinite atTop := by
    simpa only [Nat.cofinite_eq_atTop, height] using (show Tendsto (fun n => ∑ i, (X n i : ℝ) * v i) atTop atTop from hX)
  obtain ⟨n,hn⟩ := ht.exists_forall_le
  apply Set.mem_iUnion.mpr
  refine ⟨n, Set.mem_iUnion.mpr ⟨X n, rfl, ?_⟩⟩
  intro k
  exact hn (n+k)

lemma positive_nonBacktracking {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (v : Fin d → ℝ) (hescape : 0 < annealed μ 0 (escape v)) :
    0 < annealed μ 0 (nonBacktracking v) := by
  by_contra h
  have hz : annealed μ 0 (nonBacktracking v) = 0 :=
    le_antisymm (le_of_not_gt h) (zero_le)
  have hnull : annealed μ 0 (⋃ n : ℕ, ⋃ x : Site d,
      {X | X n = x} ∩ tailPath n ⁻¹' neverBelow v (height v x)) = 0 := by
    apply measure_iUnion_null
    intro n
    apply measure_iUnion_null
    intro x
    apply annealed_tail_start_null μ 0 x n (measurableSet_neverBelow v _)
    rw [annealed_neverBelow_start, hz]
  exact (ne_of_gt hescape) (measure_mono_null (escape_subset_globalMinimum_suffix v) hnull)

lemma annealed_record_tail {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (v : Fin d → ℝ) (x : Site d) (n : ℕ) (γ : Path d)
    (hrec : ∀ i < n, height v (γ i) < height v (γ n))
    {E : Set (Path d)} (hE : MeasurableSet E)
    (hD : E ⊆ neverBelow v (height v (γ n))) :
    annealed μ x (pathCylinder n γ ∩ tailPath n ⁻¹' E) =
      annealed μ x (pathCylinder n γ) * annealed μ (γ n) E := by
  let K : Set (Site d) := {y | height v y < height v (γ n)}
  have hav : E ⊆ avoids K := by
    intro X hX i hi
    exact (not_lt_of_ge (hD hX i)) hi
  have hEq : E ∩ avoids K = E := Set.inter_eq_left.mpr hav
  simpa only [hEq] using annealed_fresh_prefix_tail μ K x n γ hrec hE

lemma annealed_record_relative_tail {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (v : Fin d → ℝ) (x : Site d) (n : ℕ) (γ : Path d)
    (hrec : ∀ i < n, height v (γ i) < height v (γ n))
    {E : Set (Path d)} (hE : MeasurableSet E) :
    annealed μ x (pathCylinder n γ ∩
      tailPath n ⁻¹' (shiftPath (-(γ n)) ⁻¹' (E ∩ nonBacktracking v))) =
      annealed μ x (pathCylinder n γ) * annealed μ 0 (E ∩ nonBacktracking v) := by
  have hF := hE.inter (measurableSet_nonBacktracking v)
  rw [annealed_record_tail μ v x n γ hrec ((measurable_shiftPath _) hF)]
  · congr 1
    have h := congrArg (fun ξ : Measure (Path d) =>
      ξ (shiftPath (-(γ n)) ⁻¹' (E ∩ nonBacktracking v))) (annealed_shift μ 0 (γ n))
    rw [Measure.map_apply (measurable_shiftPath _) ((measurable_shiftPath _) hF), zero_add] at h
    have heq : shiftPath (γ n) ⁻¹' (shiftPath (-(γ n)) ⁻¹' (E ∩ nonBacktracking v)) =
        E ∩ nonBacktracking v := by
      ext X
      simp only [Set.mem_preimage]
      have hs : shiftPath (-(γ n)) (shiftPath (γ n) X) = X := by
        funext i
        simp [shiftPath]
      rw [hs]
    rw [heq] at h
    exact h.symm
  · intro X hX i
    have hi := hX.2 i
    change 0 ≤ height v (X i + -(γ n)) at hi
    rw [height_add, height_neg] at hi
    linarith

def pathFiltration (d : ℕ) : Filtration ℕ (inferInstance : MeasurableSpace (Path d)) :=
  Filtration.piLE

lemma pathFiltration_eq {d : ℕ} (n : ℕ) : pathFiltration d n =
    MeasurableSpace.comap (frestrictLe n : Path d → _) inferInstance :=
  Filtration.piLE_eq_comap_frestrictLe n

lemma pathCylinder_eq_fiber {d : ℕ} (n : ℕ) (X : Path d) :
    pathCylinder n X = (frestrictLe n : Path d → (Finset.Iic n → Site d)) ⁻¹' {frestrictLe n X} := by
  ext Y
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro h
    funext i
    exact h i (Finset.mem_Iic.mp i.property)
  · intro h i hi
    exact congr_fun h ⟨i,Finset.mem_Iic.mpr hi⟩

lemma measurableSet_pathCylinder_filtration {d : ℕ} (n : ℕ) (X : Path d) :
    MeasurableSet[pathFiltration d n] (pathCylinder n X) := by
  rw [pathFiltration_eq, pathCylinder_eq_fiber]
  exact ⟨_, measurableSet_singleton _, rfl⟩

lemma pathFiltration_iSup (d : ℕ) : (⨆ n, pathFiltration d n) =
    (inferInstance : MeasurableSpace (Path d)) := by
  apply le_antisymm (iSup_le (pathFiltration d).le)
  have hi : @Measurable (Path d) (Path d) (⨆ n, pathFiltration d n) _ id := by
    apply @Measurable.of_eval (Path d) ℕ (fun _ => Site d) (⨆ n, pathFiltration d n) _
    intro n
    have hn : Measurable[pathFiltration d n] (fun X : Path d => X n) := by
      rw [pathFiltration_eq]
      exact (show Measurable (fun a : Finset.Iic n → Site d => a ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
        from measurable_pi_apply _).comp (Measurable.of_comap_le
          (f := (frestrictLe n : Path d → (Finset.Iic n → Site d))) le_rfl)
    exact hn.mono (le_iSup _ n) le_rfl
  simpa using hi.comap_le

lemma ae_pathCylinder_ne_zero {d : ℕ} (μ : Measure (Path d)) :
    ∀ᵐ X ∂μ, ∀ n, μ (pathCylinder n X) ≠ 0 := by
  have ha (n : ℕ) (a : Finset.Iic n → Site d) :
      ∀ᵐ X ∂μ, X ∈ pathCylinder n (extendPrefix n a) →
        μ (pathCylinder n (extendPrefix n a)) ≠ 0 := by
    by_cases hz : μ (pathCylinder n (extendPrefix n a)) = 0
    · have hh : ∀ᵐ X ∂μ, X ∉ pathCylinder n (extendPrefix n a) := by
        rw [ae_iff]
        simpa using hz
      filter_upwards [hh] with X hX using fun hx => (hX hx).elim
    · exact ae_of_all _ (fun _ _ => hz)
  filter_upwards [ae_all_iff.mpr (fun n => ae_all_iff.mpr (ha n))] with X hX
  intro n
  have heq : pathCylinder n (extendPrefix n (frestrictLe n X)) = pathCylinder n X := by
    rw [pathCylinder_eq_fiber, restrict_extendPrefix, ← pathCylinder_eq_fiber]
  have hmem : X ∈ pathCylinder n X := fun _ _ => rfl
  simpa only [heq] using hX n (frestrictLe n X) (heq.symm ▸ hmem)

lemma condExp_indicator_cylinder {d : ℕ} (μ : Measure (Path d)) [IsFiniteMeasure μ]
    {E : Set (Path d)} (hE : MeasurableSet E) (n : ℕ) (X : Path d) :
    μ.real (pathCylinder n X) * (μ[E.indicator (fun _ => (1 : ℝ)) | pathFiltration d n]) X =
      μ.real (E ∩ pathCylinder n X) := by
  let f := μ[E.indicator (fun _ => (1 : ℝ)) | pathFiltration d n]
  have hf : StronglyMeasurable[MeasurableSpace.comap (frestrictLe n) inferInstance] f := by
    rw [← pathFiltration_eq]
    exact stronglyMeasurable_condExp
  have hconst : ∫ Y in pathCylinder n X, f Y ∂μ =
      μ.real (pathCylinder n X) * f X := by
    calc
      _ = ∫ _ in pathCylinder n X, f X ∂μ := by
        apply setIntegral_congr_fun (measurableSet_pathCylinder n X)
        intro Y hY
        apply hf.factorsThrough
        simpa only [pathCylinder_eq_fiber, Set.mem_preimage, Set.mem_singleton_iff] using hY
      _ = _ := by rw [setIntegral_const, smul_eq_mul]
  rw [← hconst, setIntegral_condExp ((pathFiltration d).le n) (integrable_const 1 |>.indicator hE)
    (measurableSet_pathCylinder_filtration n X)]
  rw [setIntegral_indicator hE, setIntegral_const, smul_eq_mul, mul_one, Set.inter_comm]

lemma null_of_prefix_contraction {d : ℕ} (μ : Measure (Path d)) [IsFiniteMeasure μ]
    {E : Set (Path d)} (hE : MeasurableSet E) (c : ℝ) (hc : c < 1)
    (hcontract : ∀ X ∈ E, ∃ᶠ n in atTop,
      μ.real (E ∩ pathCylinder n X) ≤ c * μ.real (pathCylinder n X)) : μ E = 0 := by
  have hint : Integrable (E.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hE
  have hmeas : StronglyMeasurable[⨆ n, pathFiltration d n]
      (E.indicator (fun _ => (1 : ℝ))) := by
    rw [pathFiltration_iSup]
    exact stronglyMeasurable_const.indicator hE
  have ht := hint.tendsto_ae_condExp (ℱ := pathFiltration d) hmeas
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [ht, ae_pathCylinder_ne_zero μ] with X hX hpos
  intro hXE
  have htX : Tendsto (fun n => (μ[E.indicator (fun _ => (1 : ℝ)) | pathFiltration d n]) X)
      atTop (𝓝 (1 : ℝ)) := by simpa [hXE] using hX
  have hlow : ∃ᶠ n in atTop,
      (μ[E.indicator (fun _ => (1 : ℝ)) | pathFiltration d n]) X ≤ c := by
    apply (hcontract X hXE).mono
    intro n hn
    rw [← condExp_indicator_cylinder μ hE n X, mul_comm c] at hn
    exact (mul_le_mul_iff_right₀ (ENNReal.toReal_pos (hpos n) (measure_ne_top _ _))).mp hn
  have hhigh : ∀ᶠ n in atTop,
      c < (μ[E.indicator (fun _ => (1 : ℝ)) | pathFiltration d n]) X :=
    htX.eventually (lt_mem_nhds hc)
  exact (hlow.and_eventually hhigh).exists.elim (fun _ hh => (not_lt_of_ge hh.1) hh.2)

lemma real_contraction_of_disjoint_success {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {E C S : Set Ω}
    (hC : MeasurableSet C) (hS : MeasurableSet S)
    (hd : Disjoint (E ∩ C) (C ∩ S)) (q : ℝ)
    (hq : μ.real (C ∩ S) = q * μ.real C) :
    μ.real (E ∩ C) ≤ (1-q) * μ.real C := by
  have hu : (E ∩ C) ∪ (C ∩ S) ⊆ C := by
    rintro x (hx | hx)
    · exact hx.2
    · exact hx.1
  have hh := measureReal_mono (μ := μ) hu
  rw [measureReal_union hd (hC.inter hS), hq] at hh
  linarith

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

def axialRay {d : ℕ} (x : Site d) (e : Step d) : Path d :=
  fun n => x + n • stepVector e

lemma axialRay_zero {d : ℕ} (x : Site d) (e : Step d) : axialRay x e 0 = x := by
  simp [axialRay]

lemma axialRay_succ {d : ℕ} (x : Site d) (e : Step d) (n : ℕ) :
    axialRay x e (n+1) = axialRay x e n + stepVector e := by
  simp only [axialRay, succ_nsmul, add_assoc]

lemma axialRay_injective {d : ℕ} (x : Site d) (e : Step d) :
    Function.Injective (axialRay x e) := by
  intro n m h
  have hh := congr_fun h e.1
  cases hb : e.2 <;> simpa [axialRay, stepVector, hb] using hh

lemma height_nsmul {d : ℕ} (v : Fin d → ℝ) (x : Site d) (n : ℕ) :
    height v (n • x) = n * height v x := by
  induction n with
  | zero => simp [height_zero]
  | succ n hn => rw [succ_nsmul, height_add, hn, Nat.cast_add, Nat.cast_one]; ring

lemma height_axialRay {d : ℕ} (v : Fin d → ℝ) (x : Site d) (e : Step d) (n : ℕ) :
    height v (axialRay x e n) = height v x + n * height v (stepVector e) := by
  rw [axialRay, height_add, height_nsmul]

lemma pathWeight_axialRay {d : ℕ} (x : Site d) (e : Step d) (n : ℕ) (ω : Environment d) :
    pathWeight n (axialRay x e) ω =
      quenchedWeight (fun j : Fin n => axialRay x e j) (fun _ => e) ω := by
  simp only [pathWeight, axialRay_succ, entryWeight_step, quenchedWeight]
  exact (Fin.prod_univ_eq_prod_range (fun j => ENNReal.ofReal ((ω (axialRay x e j)).val e)) n).symm

lemma quenched_axialRay_pos {d : ℕ} (ω : Environment d)
    (hω : ∀ x e, 0 < (ω x).val e) (x : Site d) (e : Step d) (m : ℕ) :
    0 < quenchedKernel d (ω,x) (pathCylinder m (axialRay x e)) := by
  rw [quenchedKernel_cylinder, axialRay_zero, ite_eq_left rfl, pathWeight_axialRay]
  apply pos_iff_ne_zero.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (hω _ _))

lemma annealed_axialRay {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x : Site d) (e : Step d) (m : ℕ) :
    annealed μ x (pathCylinder m (axialRay x e)) = meanStep μ e ^ m := by
  rw [annealed_cylinder, axialRay_zero, ite_eq_left rfl]
  simp_rw [pathWeight_axialRay]
  change wordWeight μ (fun j : Fin m => axialRay x e j) (fun _ => e) = _
  rw [fresh_word_weight μ (fun j : Fin m => axialRay x e j) (fun _ => e)
    ((axialRay_injective x e).comp Fin.val_injective)]
  simp

lemma quenched_prefix_tail_factor {d : ℕ} (ω : Environment d) (x : Site d)
    (n : ℕ) (γ : Path d) {E : Set (Path d)} (hE : MeasurableSet E) :
    quenchedKernel d (ω,x) (pathCylinder n γ ∩ tailPath n ⁻¹' E) =
      quenchedKernel d (ω,x) (pathCylinder n γ) * quenchedKernel d (ω,γ n) E := by
  rw [quenched_prefix_tail_apply _ _ _ _ hE, quenchedKernel_cylinder]

lemma annealed_disjoint_prefix_tail {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x : Site d) (n m : ℕ) (γ δ : Path d) (hjoin : γ n = δ 0)
    (hdis : ∀ i < n, ∀ j < m, γ i ≠ δ j) :
    annealed μ x (pathCylinder n γ ∩ tailPath n ⁻¹' pathCylinder m δ) =
      annealed μ x (pathCylinder n γ) * annealed μ (γ n) (pathCylinder m δ) := by
  classical
  rw [annealed_apply μ x ((measurableSet_pathCylinder n γ).inter
    ((measurable_tailPath n) (measurableSet_pathCylinder m δ)))]
  simp_rw [quenched_prefix_tail_apply _ _ _ _ (measurableSet_pathCylinder m δ),
    quenchedKernel_cylinder, ite_eq_left hjoin]
  rw [annealed_cylinder, annealed_cylinder, ite_eq_left hjoin]
  by_cases hx : x = γ 0
  · simp only [ite_eq_left hx]
    exact path_weights_disjoint μ n m γ δ hdis
  · simp only [ite_eq_right hx, zero_mul, lintegral_zero]

def alwaysBelow {d : ℕ} (v : Fin d → ℝ) (b : ℝ) : Set (Path d) :=
  {X | ∀ n, height v (X n) ≤ b}

lemma measurableSet_alwaysBelow {d : ℕ} (v : Fin d → ℝ) (b : ℝ) :
    MeasurableSet (alwaysBelow v b) := by
  simp only [alwaysBelow, Set.ofPred_forall]
  exact MeasurableSet.iInter (fun n => measurableSet_le
    ((measurable_of_countable (height v)).comp (measurable_pi_apply n)) measurable_const)

def infiniteVisits {d : ℕ} (x : Site d) : Set (Path d) :=
  {X | ∀ N, ∃ n, N ≤ n ∧ X n = x}

lemma measurableSet_infiniteVisits {d : ℕ} (x : Site d) : MeasurableSet (infiniteVisits x) := by
  simp only [infiniteVisits, Set.ofPred_forall, Set.ofPred_exists, Set.ofPred_and]
  exact MeasurableSet.iInter (fun N => MeasurableSet.iUnion (fun n =>
    (MeasurableSet.const _).inter (measurableSet_eq_fun (measurable_pi_apply n) measurable_const)))

lemma quenched_bounded_infiniteVisits_null {d : ℕ} (ω : Environment d)
    (hω : ∀ x e, 0 < (ω x).val e) (y x : Site d) (v : Fin d → ℝ)
    (e : Step d) (he : 0 < height v (stepVector e)) (b : ℝ) :
    quenchedKernel d (ω,y) (alwaysBelow v b ∩ infiniteVisits x) = 0 := by
  obtain ⟨m,hm⟩ := exists_nat_gt ((b-height v x) / height v (stepVector e))
  have hcross : b < height v (axialRay x e m) := by
    rw [height_axialRay]
    have ht := (div_lt_iff₀ he).mp hm
    linarith
  let ν := quenchedKernel d (ω,y)
  let S := pathCylinder m (axialRay x e)
  let q := (quenchedKernel d (ω,x) S).toReal
  have hq : 0 < q := ENNReal.toReal_pos
    (ne_of_gt (quenched_axialRay_pos ω hω x e m)) (measure_ne_top _ _)
  apply null_of_prefix_contraction ν
    ((measurableSet_alwaysBelow v b).inter (measurableSet_infiniteVisits x)) (1-q) (by linarith)
  intro X hX
  apply (frequently_atTop.mpr hX.2).mono
  intro n hn
  refine real_contraction_of_disjoint_success ν (measurableSet_pathCylinder n X)
    ((measurable_tailPath n) (measurableSet_pathCylinder m (axialRay x e))) ?_ q ?_
  · apply Set.disjoint_left.mpr
    rintro Y ⟨hY,_⟩ ⟨_,hS⟩
    have hs := hS m le_rfl
    have hbound := hY.1 (n+m)
    change Y (n+m) = axialRay x e m at hs
    rw [hs] at hbound
    exact (not_le_of_gt hcross) hbound
  · change (ν (pathCylinder n X ∩ tailPath n ⁻¹' S)).toReal = _
    rw [quenched_prefix_tail_factor _ _ _ _ (measurableSet_pathCylinder m (axialRay x e)), hn,
      ENNReal.toReal_mul, mul_comm]
    rfl

lemma annealed_bounded_infiniteVisits_null {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (y x : Site d) (v : Fin d → ℝ)
    (e : Step d) (he : 0 < height v (stepVector e)) (b : ℝ) :
    annealed μ y (alwaysBelow v b ∩ infiniteVisits x) = 0 := by
  rw [annealed_apply μ y ((measurableSet_alwaysBelow v b).inter (measurableSet_infiniteVisits x))]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [all_rows_strictly_positive μ hell] with ω hω
  exact quenched_bounded_infiniteVisits_null ω hω y x v e he b

def column {d : ℕ} (c : Fin d) (x : Site d) : Site d := Function.update x c 0

lemma column_axialRay {d : ℕ} (x : Site d) (e : Step d) (n : ℕ) :
    column e.1 (axialRay x e n) = column e.1 x := by
  funext j
  by_cases hj : j = e.1
  · subst j; simp [column]
  · simp [column, hj, axialRay, stepVector]

lemma height_eq_column {d : ℕ} (v : Fin d → ℝ) (c : Fin d) (x : Site d) :
    height v x = height v (column c x) + (x c : ℝ) * v c := by
  have h : height v x - height v (column c x) = (x c : ℝ) * v c := by
    unfold height
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single c]
    · simp [column]
    · intro j _ hj; simp [column, hj]
    · simp
  linarith

lemma finite_column_band {d : ℕ} (v : Fin d → ℝ) (c : Fin d) (hv : v c ≠ 0)
    (y : Site d) (a b : ℝ) :
    {x : Site d | column c x = column c y ∧ a ≤ height v x ∧ height v x ≤ b}.Finite := by
  let S := {x : Site d | column c x = column c y ∧ a ≤ height v x ∧ height v x ≤ b}
  have hi : Set.InjOn (fun x : Site d => x c) S := by
    intro x hx z hz h
    funext j
    by_cases hj : j = c
    · simpa [hj] using h
    · have hh := congr_fun (hx.1.trans hz.1.symm) j
      simpa [column, hj] using hh
  apply Set.Finite.of_finite_image (hi := hi)
  rcases lt_or_gt_of_ne hv with hneg | hpos
  · apply (Set.finite_Icc ⌈(b-height v (column c y))/v c⌉ ⌊(a-height v (column c y))/v c⌋).subset
    rintro _ ⟨x,hx,rfl⟩
    have hh := height_eq_column v c x
    rw [hx.1] at hh
    constructor
    · apply Int.ceil_le.mpr
      apply (div_le_iff_of_neg hneg).mpr
      linarith [hx.2.2]
    · apply Int.le_floor.mpr
      apply (le_div_iff_of_neg hneg).mpr
      linarith [hx.2.1]
  · apply (Set.finite_Icc ⌈(a-height v (column c y))/v c⌉ ⌊(b-height v (column c y))/v c⌋).subset
    rintro _ ⟨x,hx,rfl⟩
    have hh := height_eq_column v c x
    rw [hx.1] at hh
    constructor
    · apply Int.ceil_le.mpr
      apply (div_le_iff₀ hpos).mpr
      linarith [hx.2.1]
    · apply Int.le_floor.mpr
      apply (le_div_iff₀ hpos).mpr
      linarith [hx.2.2]

def freshColumnTime {d : ℕ} (v : Fin d → ℝ) (e : Step d) (a : ℝ) (X : Path d) (n : ℕ) : Prop :=
  a ≤ height v (X n) ∧ ∀ i < n, column e.1 (X i) = column e.1 (X n) → height v (X i) < a

lemma measurableSet_freshColumnTime {d : ℕ} (v : Fin d → ℝ) (e : Step d) (a : ℝ) (n : ℕ) :
    MeasurableSet {X : Path d | freshColumnTime v e a X n} := by
  unfold freshColumnTime
  simp only [Set.ofPred_and, Set.ofPred_forall]
  refine (measurableSet_le measurable_const
    ((measurable_of_countable (height v)).comp (measurable_pi_apply n))).inter ?_
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro _
  simp only [imp_iff_not_or, Set.ofPred_or]
  exact ((measurableSet_eq_fun
    ((measurable_of_countable (column e.1)).comp (measurable_pi_apply i))
    ((measurable_of_countable (column e.1)).comp (measurable_pi_apply n))).compl).union
    (measurableSet_lt ((measurable_of_countable (height v)).comp (measurable_pi_apply i)) measurable_const)

lemma measurableSet_frequently_nat {Ω : Type*} [MeasurableSpace Ω] (P : ℕ → Ω → Prop)
    (hP : ∀ n, MeasurableSet {x | P n x}) :
    MeasurableSet {x | ∃ᶠ n in atTop, P n x} := by
  simp only [frequently_atTop, Set.ofPred_forall, Set.ofPred_exists, Set.ofPred_and]
  exact MeasurableSet.iInter (fun N => MeasurableSet.iUnion (fun n =>
    (MeasurableSet.const _).inter (hP n)))

lemma annealed_bounded_freshColumns_null {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (y : Site d) (v : Fin d → ℝ)
    (e : Step d) (he : 0 < height v (stepVector e)) (a b : ℝ) :
    annealed μ y (alwaysBelow v b ∩ {X | ∃ᶠ n in atTop, freshColumnTime v e a X n}) = 0 := by
  obtain ⟨m,hm⟩ := exists_nat_gt ((b-a) / height v (stepVector e))
  let q := (meanStep μ e ^ m).toReal
  have hq : 0 < q := ENNReal.toReal_pos
    (pow_ne_zero _ (ne_of_gt (meanStep_pos μ hell e)))
    (ne_of_lt (lt_of_le_of_lt (pow_le_one₀ zero_le (meanStep_le_one μ e)) ENNReal.one_lt_top))
  apply null_of_prefix_contraction (annealed μ y)
    ((measurableSet_alwaysBelow v b).inter (measurableSet_frequently_nat _
      (measurableSet_freshColumnTime v e a))) (1-q) (by linarith)
  intro X hX
  apply hX.2.mono
  intro n hn
  have hcross : b < height v (axialRay (X n) e m) := by
    rw [height_axialRay]
    have ht := (div_lt_iff₀ he).mp hm
    linarith [hn.1]
  have hdis : ∀ i < n, ∀ j < m, X i ≠ axialRay (X n) e j := by
    intro i hi j _ hij
    have hcol : column e.1 (X i) = column e.1 (X n) := by rw [hij, column_axialRay]
    have hlow := hn.2 i hi hcol
    rw [hij, height_axialRay] at hlow
    have hnonneg : 0 ≤ (j : ℝ) * height v (stepVector e) := mul_nonneg (Nat.cast_nonneg _) he.le
    linarith [hn.1]
  refine real_contraction_of_disjoint_success (annealed μ y) (measurableSet_pathCylinder n X)
    ((measurable_tailPath n) (measurableSet_pathCylinder m (axialRay (X n) e))) ?_ q ?_
  · apply Set.disjoint_left.mpr
    rintro Y ⟨hY,_⟩ ⟨_,hS⟩
    have hs := hS m le_rfl
    have hbound := hY.1 (n+m)
    change Y (n+m) = axialRay (X n) e m at hs
    rw [hs] at hbound
    exact (not_le_of_gt hcross) hbound
  · change (annealed μ y (pathCylinder n X ∩ tailPath n ⁻¹'
        pathCylinder m (axialRay (X n) e))).toReal = _
    rw [annealed_disjoint_prefix_tail μ y n m X (axialRay (X n) e)
      (axialRay_zero (X n) e).symm hdis, annealed_axialRay, ENNReal.toReal_mul, mul_comm]
    rfl

lemma recurrent_or_freshColumns {d : ℕ} (v : Fin d → ℝ) (e : Step d) (hv : v e.1 ≠ 0)
    (a b : ℝ) (X : Path d) (hb : X ∈ alwaysBelow v b)
    (ha : ∃ᶠ n in atTop, a ≤ height v (X n)) :
    (∃ x, X ∈ infiniteVisits x) ∨ ∃ᶠ n in atTop, freshColumnTime v e a X n := by
  classical
  by_cases hf : ∃ᶠ n in atTop, freshColumnTime v e a X n
  · exact Or.inr hf
  left
  obtain ⟨N,hN⟩ := eventually_atTop.mp (not_frequently.mp hf)
  let F : Set (Site d) := ⋃ i ∈ Finset.range N,
    {x | column e.1 x = column e.1 (X i) ∧ a ≤ height v x ∧ height v x ≤ b}
  have hF : F.Finite := (Finset.finite_toSet (Finset.range N)).biUnion
    (fun i _ => finite_column_band v e.1 hv (X i) a b)
  have hmem (n : ℕ) (hn : a ≤ height v (X n)) : X n ∈ F := by
    have hex : ∃ i, a ≤ height v (X i) ∧ column e.1 (X i) = column e.1 (X n) := ⟨n,hn,rfl⟩
    let k := Nat.find hex
    have hk := Nat.find_spec hex
    have helig : freshColumnTime v e a X k := by
      refine ⟨hk.1, fun i hi hcol => ?_⟩
      by_contra h
      exact Nat.find_min hex hi ⟨le_of_not_gt h, hcol.trans hk.2⟩
    have hkN : k < N := lt_of_not_ge (fun h => hN k h helig)
    exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr
      ⟨Finset.mem_range.mpr hkN, hk.2.symm, hn, hb n⟩⟩
  have hfreq : ∃ᶠ n in atTop, ∃ x ∈ F, X n = x := ha.mono (fun n hn => ⟨X n,hmem n hn,rfl⟩)
  obtain ⟨x,_,hx⟩ := hF.frequently_exists.mp hfreq
  exact ⟨x, frequently_atTop.mp hx⟩

lemma height_stepVector {d : ℕ} (v : Fin d → ℝ) (e : Step d) :
    height v (stepVector e) = if e.2 then v e.1 else -v e.1 := by
  classical
  simp [height, stepVector, ite_mul]

lemma annealed_bounded_band_null {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (y : Site d) (v : Fin d → ℝ)
    (e : Step d) (he : 0 < height v (stepVector e)) (a b : ℝ) :
    annealed μ y (alwaysBelow v b ∩ {X | ∃ᶠ n in atTop, a ≤ height v (X n)}) = 0 := by
  have hv : v e.1 ≠ 0 := by
    intro hz
    rw [height_stepVector, hz] at he
    split_ifs at he <;> simp_all
  apply measure_mono_null (t := (⋃ x, alwaysBelow v b ∩ infiniteVisits x) ∪
    (alwaysBelow v b ∩ {X | ∃ᶠ n in atTop, freshColumnTime v e a X n}))
  · rintro X ⟨hX,hfreq⟩
    rcases recurrent_or_freshColumns v e hv a b X hX hfreq with ⟨x,hx⟩ | hf
    · exact Or.inl (Set.mem_iUnion.mpr ⟨x,hX,hx⟩)
    · exact Or.inr ⟨hX,hf⟩
  · rw [measure_union_null_iff]
    exact ⟨measure_iUnion_null (fun x => annealed_bounded_infiniteVisits_null μ hell y x v e he b),
      annealed_bounded_freshColumns_null μ hell y v e he a b⟩

lemma exists_positive_step {d : ℕ} (v : Fin d → ℝ) (hv : v ≠ 0) :
    ∃ e : Step d, 0 < height v (stepVector e) := by
  have hex : ∃ c, v c ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  obtain ⟨c,hc⟩ := hex
  rcases lt_or_gt_of_ne hc with hneg | hpos
  · exact ⟨(c,false), by simpa [height_stepVector] using neg_pos.mpr hneg⟩
  · exact ⟨(c,true), by simpa [height_stepVector] using hpos⟩

lemma finite_supremum {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (y : Site d) (v : Fin d → ℝ) (hv : v ≠ 0) :
    ∀ᵐ X ∂annealed μ y, (∃ b : ℝ, ∀ n, height v (X n) ≤ b) →
      Tendsto (fun n => height v (X n)) atTop atBot := by
  obtain ⟨e,he⟩ := exists_positive_step v hv
  have hnull (b a : ℤ) : ∀ᵐ X ∂annealed μ y,
      ¬(X ∈ alwaysBelow v (b : ℝ) ∧ ∃ᶠ n in atTop, (a : ℝ) ≤ height v (X n)) := by
    exact (measure_eq_zero_iff_ae_notMem).mp (annealed_bounded_band_null μ hell y v e he a b)
  filter_upwards [ae_all_iff.mpr (fun b => ae_all_iff.mpr (hnull b))] with X hX
  rintro ⟨b,hb⟩
  have hb' : X ∈ alwaysBelow v (⌈b⌉ : ℝ) := fun n => (hb n).trans (Int.le_ceil b)
  apply tendsto_atBot.mpr
  intro a
  have hnf : ¬∃ᶠ n in atTop, (⌊a⌋ : ℝ) ≤ height v (X n) := fun h => hX ⌈b⌉ ⌊a⌋ ⟨hb',h⟩
  filter_upwards [not_frequently.mp hnf] with n hn
  exact (lt_of_not_ge hn).le.trans (Int.floor_le a)

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

def strictRecord {d : ℕ} (v : Fin d → ℝ) (X : Path d) (n : ℕ) : Prop :=
  0 < n ∧ ∀ i < n, height v (X i) < height v (X n)

def trueCut {d : ℕ} (v : Fin d → ℝ) (X : Path d) (n : ℕ) : Prop :=
  strictRecord v X n ∧ ∀ j, height v (X n) ≤ height v (X (n+j))

lemma measurableSet_strictRecord {d : ℕ} (v : Fin d → ℝ) (n : ℕ) :
    MeasurableSet {X : Path d | strictRecord v X n} := by
  simp only [strictRecord, Set.ofPred_and, Set.ofPred_forall]
  exact (MeasurableSet.const _).inter (MeasurableSet.iInter (fun i =>
    MeasurableSet.iInter (fun _ => measurableSet_lt
      ((measurable_of_countable (height v)).comp (measurable_pi_apply i))
      ((measurable_of_countable (height v)).comp (measurable_pi_apply n)))))

lemma measurableSet_trueCut {d : ℕ} (v : Fin d → ℝ) (n : ℕ) :
    MeasurableSet {X : Path d | trueCut v X n} := by
  simp only [trueCut, Set.ofPred_and, Set.ofPred_forall]
  exact (measurableSet_strictRecord v n).inter (MeasurableSet.iInter (fun j =>
    measurableSet_le ((measurable_of_countable (height v)).comp (measurable_pi_apply n))
      ((measurable_of_countable (height v)).comp (measurable_pi_apply (n+j)))))

lemma strictRecord_prefix {d : ℕ} (v : Fin d → ℝ) {X Y : Path d} {n : ℕ}
    (hX : strictRecord v X n) (hY : Y ∈ pathCylinder n X) : strictRecord v Y n := by
  refine ⟨hX.1,fun i hi => ?_⟩
  rw [hY i hi.le, hY n le_rfl]
  exact hX.2 i hi

lemma unbounded_has_later_strictRecord {d : ℕ} (v : Fin d → ℝ) (X : Path d)
    (hX : ¬∃ b : ℝ, ∀ n, height v (X n) ≤ b) (N : ℕ) :
    ∃ n, N < n ∧ strictRecord v X n := by
  classical
  let b := (Finset.range (N+1)).sup' (by simp) (fun n => height v (X n))
  have hex : ∃ n, b < height v (X n) := by
    by_contra h
    push Not at h
    exact hX ⟨b,h⟩
  refine ⟨Nat.find hex, ?_, ?_⟩
  · by_contra h
    have hn : Nat.find hex ∈ Finset.range (N+1) := Finset.mem_range.mpr (by omega)
    exact (not_le_of_gt (Nat.find_spec hex)) (Finset.le_sup' (fun n => height v (X n)) hn)
  · refine ⟨?_,fun i hi => ?_⟩
    · have hzero : height v (X 0) ≤ b := Finset.le_sup' (fun n => height v (X n)) (Finset.mem_range.mpr (Nat.succ_pos N))
      by_contra h
      have hn : Nat.find hex = 0 := by omega
      have hh := Nat.find_spec hex
      rw [hn] at hh
      linarith
    · exact (le_of_not_gt (Nat.find_min hex hi)).trans_lt (Nat.find_spec hex)

lemma measurableSet_boundedHeight {d : ℕ} (v : Fin d → ℝ) :
    MeasurableSet {X : Path d | ∃ b : ℝ, ∀ n, height v (X n) ≤ b} := by
  have heq : {X : Path d | ∃ b : ℝ, ∀ n, height v (X n) ≤ b} =
      ⋃ b : ℤ, alwaysBelow v (b : ℝ) := by
    ext X
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨b,hb⟩
      exact ⟨⌈b⌉,fun n => (hb n).trans (Int.le_ceil b)⟩
    · rintro ⟨b,hb⟩; exact ⟨b,hb⟩
  rw [heq]
  exact MeasurableSet.iUnion (fun b => measurableSet_alwaysBelow v b)

lemma no_later_trueCut_null {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (y : Site d) (v : Fin d → ℝ) (hp : 0 < annealed μ 0 (nonBacktracking v)) (N : ℕ) :
    annealed μ y {X | (¬∃ b : ℝ, ∀ n, height v (X n) ≤ b) ∧
      ∀ n, N < n → ¬trueCut v X n} = 0 := by
  let p := (annealed μ 0 (nonBacktracking v)).toReal
  have hp' : 0 < p := ENNReal.toReal_pos (ne_of_gt hp) (measure_ne_top _ _)
  have hE : MeasurableSet {X : Path d | (¬∃ b : ℝ, ∀ n, height v (X n) ≤ b) ∧
      ∀ n, N < n → ¬trueCut v X n} := by
    simp only [Set.ofPred_and, Set.ofPred_forall]
    exact (measurableSet_boundedHeight v).compl.inter (MeasurableSet.iInter (fun n =>
      MeasurableSet.iInter (fun _ => (measurableSet_trueCut v n).compl)))
  apply null_of_prefix_contraction (annealed μ y) hE (1-p) (by linarith)
  intro X hX
  have hf : ∃ᶠ n in atTop, N < n ∧ strictRecord v X n := by
    apply frequently_atTop.mpr
    intro k
    obtain ⟨n,hn,hr⟩ := unbounded_has_later_strictRecord v X hX.1 (max k N)
    exact ⟨n,(le_max_left k N).trans hn.le,(le_max_right k N).trans_lt hn,hr⟩
  apply hf.mono
  rintro n ⟨hn,hr⟩
  refine real_contraction_of_disjoint_success (annealed μ y) (measurableSet_pathCylinder n X)
    ((measurable_tailPath n) (measurableSet_neverBelow v (height v (X n)))) ?_ p ?_
  · apply Set.disjoint_left.mpr
    rintro Y ⟨hY,hYC⟩ ⟨_,hS⟩
    apply hY.2 n hn
    refine ⟨strictRecord_prefix v hr hYC,fun j => ?_⟩
    rw [hYC n le_rfl]
    exact hS j
  · change (annealed μ y (pathCylinder n X ∩ tailPath n ⁻¹'
        neverBelow v (height v (X n)))).toReal = _
    rw [annealed_record_tail μ v y n X hr.2 (measurableSet_neverBelow v (height v (X n)))
      (fun _ h => h), annealed_neverBelow_start, ENNReal.toReal_mul, mul_comm]
    rfl

lemma ae_infinitely_trueCuts {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (y : Site d) (v : Fin d → ℝ) (hp : 0 < annealed μ 0 (nonBacktracking v)) :
    ∀ᵐ X ∂annealed μ y, (¬∃ b : ℝ, ∀ n, height v (X n) ≤ b) →
      ∀ N, ∃ n, N < n ∧ trueCut v X n := by
  have hN (N : ℕ) : ∀ᵐ X ∂annealed μ y,
      ¬((¬∃ b : ℝ, ∀ n, height v (X n) ≤ b) ∧ ∀ n, N < n → ¬trueCut v X n) :=
    (measure_eq_zero_iff_ae_notMem).mp (no_later_trueCut_null μ y v hp N)
  filter_upwards [ae_all_iff.mpr hN] with X hX
  intro hu N
  by_contra h
  push Not at h
  exact hX N ⟨hu,h⟩

lemma escape_of_infinitely_trueCuts {d : ℕ} (v : Fin d → ℝ) (X : Path d)
    (hu : ¬∃ b : ℝ, ∀ n, height v (X n) ≤ b)
    (hcuts : ∀ N, ∃ n, N < n ∧ trueCut v X n) : X ∈ escape v := by
  apply tendsto_atTop.mpr
  intro b
  have hex : ∃ k, b < height v (X k) := by
    by_contra h; push Not at h; exact hu ⟨b,h⟩
  obtain ⟨k,hk⟩ := hex
  obtain ⟨n,hn,hr,ht⟩ := hcuts k
  apply eventually_atTop.mpr
  refine ⟨n,fun m hm => ?_⟩
  have ht' := ht (m-n)
  rw [Nat.add_sub_of_le hm] at ht'
  exact (hk.trans (hr.2 k hn)).le.trans ht'

lemma height_neg_direction {d : ℕ} (v : Fin d → ℝ) (x : Site d) :
    height (-v) x = -height v x := by simp [height, Finset.sum_neg_distrib]

lemma ae_escape_or_opposite {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (y : Site d) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) :
    ∀ᵐ X ∂annealed μ y, X ∈ escape v ∨ X ∈ escape (-v) := by
  filter_upwards [finite_supremum μ hell y v hv, ae_infinitely_trueCuts μ y v hp] with X hfin hcut
  by_cases hb : ∃ b : ℝ, ∀ n, height v (X n) ≤ b
  · right
    have ht := tendsto_neg_atBot_atTop.comp (hfin hb)
    change Tendsto (fun n => height (-v) (X n)) atTop atTop
    simpa only [height_neg_direction, Function.comp_def] using ht
  · exact Or.inl (escape_of_infinitely_trueCuts v X hb (hcut hb))

def nearestNeighbour {d : ℕ} (X : Path d) : Prop :=
  ∀ n, ∃ e : Step d, X (n+1) = X n + stepVector e

lemma ae_start_and_nearestNeighbour {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (y : Site d) : ∀ᵐ X ∂annealed μ y, X 0 = y ∧ nearestNeighbour X := by
  classical
  filter_upwards [ae_pathCylinder_ne_zero (annealed μ y)] with X hX
  constructor
  · by_contra h
    have hh := hX 0
    rw [annealed_cylinder, ite_eq_right (Ne.symm h)] at hh
    exact hh rfl
  · intro n
    by_contra h
    have hw (ω : Environment d) : entryWeight ω (X n) (X (n+1)) = 0 := by
      unfold entryWeight
      apply Finset.sum_eq_zero
      intro e _
      have he : X (n+1) ≠ X n + stepVector e := fun he => h ⟨e,he⟩
      simp [Ne.symm he]
    have hh := hX (n+1)
    rw [annealed_cylinder] at hh
    split_ifs at hh
    · simp only [pathWeight_succ, hw, mul_zero, lintegral_zero] at hh
      exact hh rfl
    · exact hh rfl

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

abbrev Word (d : ℕ) := Σ n : ℕ, (Finset.Iic n → Site d)

instance (d : ℕ) : MeasurableSpace (Word d) := ⊤
instance (d : ℕ) : MeasurableSingletonClass (Word d) := ⟨fun _ => trivial⟩

def wordPath {d : ℕ} (γ : Word d) : Path d := extendPrefix γ.1 γ.2

def prefixWord {d : ℕ} (n : ℕ) (X : Path d) : Word d := ⟨n,frestrictLe n X⟩

lemma wordPath_prefixWord {d : ℕ} (n : ℕ) (X : Path d) {i : ℕ} (hi : i ≤ n) :
    wordPath (prefixWord n X) i = X i := by
  exact extendPrefix_apply n (frestrictLe n X) hi

lemma prefixWord_eq_iff {d : ℕ} (n : ℕ) (X : Path d) (γ : Word d) :
    prefixWord n X = γ ↔ n = γ.1 ∧ X ∈ pathCylinder γ.1 (wordPath γ) := by
  rcases γ with ⟨m,a⟩
  constructor
  · intro h
    have hm := congrArg Sigma.fst h
    change n = m at hm
    subst m
    have ha : frestrictLe n X = a := by simpa [prefixWord] using h
    refine ⟨rfl,fun i hi => ?_⟩
    rw [wordPath, extendPrefix_apply n a hi, ← ha]
    rfl
  · rintro ⟨rfl,h⟩
    change (⟨n, frestrictLe n X⟩ : Word d) = ⟨n,a⟩
    congr 1
    funext i
    simpa [wordPath, extendPrefix_apply n a (Finset.mem_Iic.mp i.property)] using
      h i (Finset.mem_Iic.mp i.property)

lemma measurable_prefixWord {d : ℕ} (n : ℕ) : Measurable (prefixWord (d := d) n) := by
  apply measurable_to_countable'
  intro γ
  have heq : (prefixWord n) ⁻¹' {γ} =
      {X : Path d | n = γ.1} ∩ pathCylinder γ.1 (wordPath γ) := by
    ext X; exact prefixWord_eq_iff n X γ
  rw [heq]
  exact (MeasurableSet.const _).inter (measurableSet_pathCylinder _ _)

def RegenerationWord {d : ℕ} (v : Fin d → ℝ) (γ : Word d) : Prop :=
  0 < γ.1 ∧ wordPath γ 0 = 0 ∧
  (∀ i < γ.1, ∃ e : Step d, wordPath γ (i+1) = wordPath γ i + stepVector e) ∧
  (∀ i < γ.1, 0 ≤ height v (wordPath γ i) ∧ height v (wordPath γ i) < height v (wordPath γ γ.1)) ∧
  (∀ j < γ.1, strictRecord v (wordPath γ) j →
    ∃ k, j < k ∧ k < γ.1 ∧ height v (wordPath γ k) < height v (wordPath γ j))

noncomputable def annealedWordWeight {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (γ : Word d) : ℝ≥0∞ := ∫⁻ ω, pathWeight γ.1 (wordPath γ) ω ∂environmentLaw μ

noncomputable def firstCutTime {d : ℕ} (v : Fin d → ℝ) (X : Path d) : ℕ :=
  by
    classical
    exact if h : ∃ n, trueCut v X n then Nat.find h else 0

lemma firstCutTime_spec {d : ℕ} (v : Fin d → ℝ) (X : Path d)
    (h : ∃ n, trueCut v X n) : trueCut v X (firstCutTime v X) ∧
      ∀ i < firstCutTime v X, ¬trueCut v X i := by
  classical
  simp only [firstCutTime, dite_eq_left h]
  exact ⟨Nat.find_spec h,fun i hi => Nat.find_min h hi⟩

lemma firstCutTime_eq_pos_iff {d : ℕ} (v : Fin d → ℝ) (X : Path d) {n : ℕ} (hn : 0 < n) :
    firstCutTime v X = n ↔ trueCut v X n ∧ ∀ i < n, ¬trueCut v X i := by
  classical
  constructor
  · intro h
    have hex : ∃ n, trueCut v X n := by
      by_contra hh
      simp only [firstCutTime, dite_eq_right hh] at h
      omega
    have hs := firstCutTime_spec v X hex
    simpa [h] using hs
  · rintro ⟨ht,hm⟩
    have hex : ∃ n, trueCut v X n := ⟨n,ht⟩
    simp only [firstCutTime, dite_eq_left hex]
    exact (Nat.find_eq_iff hex).mpr ⟨ht,hm⟩

lemma firstCutTime_eq_zero_iff {d : ℕ} (v : Fin d → ℝ) (X : Path d) :
    firstCutTime v X = 0 ↔ ¬∃ n, trueCut v X n := by
  constructor
  · intro hz hex
    have hs := (firstCutTime_spec v X hex).1.1.1
    omega
  · intro h; simp [firstCutTime,h]

lemma measurable_firstCutTime {d : ℕ} (v : Fin d → ℝ) : Measurable (firstCutTime v) := by
  apply measurable_to_countable'
  intro n
  by_cases hn : n = 0
  · subst n
    have heq : (firstCutTime v) ⁻¹' {0} = (⋃ n, {X : Path d | trueCut v X n})ᶜ := by
      ext X
      simp only [Set.mem_preimage, Set.mem_singleton_iff, firstCutTime_eq_zero_iff,
        Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq]
    rw [heq]
    exact (MeasurableSet.iUnion (fun n => measurableSet_trueCut v n)).compl
  · have hp : 0 < n := Nat.pos_of_ne_zero hn
    have heq : (firstCutTime v) ⁻¹' {n} = {X : Path d | trueCut v X n} ∩
        ⋂ i, ⋂ (_ : i < n), {X : Path d | ¬trueCut v X i} := by
      ext X
      simp only [Set.mem_preimage, Set.mem_singleton_iff, firstCutTime_eq_pos_iff v X hp,
        Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    rw [heq]
    exact (measurableSet_trueCut v n).inter (MeasurableSet.iInter (fun i =>
      MeasurableSet.iInter (fun _ => (measurableSet_trueCut v i).compl)))

noncomputable def firstWord {d : ℕ} (v : Fin d → ℝ) (X : Path d) : Word d :=
  prefixWord (firstCutTime v X) X

noncomputable def cutSuffix {d : ℕ} (v : Fin d → ℝ) (X : Path d) : Path d :=
  shiftPath (-(X (firstCutTime v X))) (tailPath (firstCutTime v X) X)

lemma measurable_firstWord {d : ℕ} (v : Fin d → ℝ) : Measurable (firstWord v) := by
  exact (measurable_from_prod_countable_right (f := fun (p : ℕ × Path d) =>
    prefixWord p.1 p.2) (fun n => measurable_prefixWord n)).comp
    ((measurable_firstCutTime v).prodMk measurable_id)

lemma measurable_cutSuffix {d : ℕ} (v : Fin d → ℝ) : Measurable (cutSuffix v) := by
  apply Measurable.comp (measurable_from_prod_countable_right
    (f := fun (p : ℕ × Path d) => shiftPath (-(p.2 p.1)) (tailPath p.1 p.2))
    (fun n => ?_))
    ((measurable_firstCutTime v).prodMk measurable_id)
  apply Measurable.of_eval
  intro j
  change Measurable (fun X : Path d => X (n+j) + -(X n))
  exact (measurable_pi_apply (n+j)).add (measurable_pi_apply n).neg

lemma firstWord_regeneration {d : ℕ} (v : Fin d → ℝ) (X : Path d)
    (h0 : X 0 = 0) (hNN : nearestNeighbour X) (hD : X ∈ nonBacktracking v)
    (hc : ∃ n, trueCut v X n) : RegenerationWord v (firstWord v X) := by
  let m := firstCutTime v X
  change RegenerationWord v (prefixWord m X)
  have hs := firstCutTime_spec v X hc
  have hwp : ∀ i ≤ m, wordPath (firstWord v X) i = X i :=
    fun i hi => wordPath_prefixWord m X hi
  change 0 < m ∧ wordPath (firstWord v X) 0 = 0 ∧
    (∀ i < m, ∃ e : Step d, wordPath (firstWord v X) (i+1) =
      wordPath (firstWord v X) i + stepVector e) ∧
    (∀ i < m, 0 ≤ height v (wordPath (firstWord v X) i) ∧
      height v (wordPath (firstWord v X) i) < height v (wordPath (firstWord v X) m)) ∧
    (∀ j < m, strictRecord v (wordPath (firstWord v X)) j →
      ∃ k, j < k ∧ k < m ∧ height v (wordPath (firstWord v X) k) <
        height v (wordPath (firstWord v X) j))
  refine ⟨hs.1.1.1,?_,?_,?_,?_⟩
  · rw [hwp 0 (Nat.zero_le _)]; exact h0
  · intro i hi
    rw [hwp (i+1) (by omega),hwp i hi.le]
    exact hNN i
  · intro i hi
    rw [hwp i hi.le,hwp m le_rfl]
    exact ⟨hD i,hs.1.1.2 i hi⟩
  · intro j hj hrec
    have hrecX : strictRecord v X j := by
      refine ⟨hrec.1,fun i hi => ?_⟩
      have hh := hrec.2 i hi
      rw [hwp i (by omega),hwp j hj.le] at hh
      exact hh
    have hex : ∃ k, j < k ∧ k < m ∧ height v (X k) < height v (X j) := by
      by_contra h
      push Not at h
      apply hs.2 j hj
      refine ⟨hrecX,fun t => ?_⟩
      by_cases htm : j+t < m
      · by_cases ht0 : t = 0
        · simp [ht0]
        · exact h (j+t) (by omega) htm
      · have hh := hs.1.2 (j+t-m)
        rw [Nat.add_sub_of_le (by omega : m ≤ j+t)] at hh
        exact (hs.1.1.2 j hj).le.trans hh
    obtain ⟨k,hjk,hkm,hk⟩ := hex
    refine ⟨k,hjk,hkm,?_⟩
    rw [hwp k hkm.le,hwp j hj.le]
    exact hk

lemma firstWord_eq_iff {d : ℕ} (v : Fin d → ℝ) (X : Path d) (γ : Word d)
    (hγ : RegenerationWord v γ) : firstWord v X = γ ↔
      X ∈ pathCylinder γ.1 (wordPath γ) ∧
      shiftPath (-(wordPath γ γ.1)) (tailPath γ.1 X) ∈ nonBacktracking v := by
  constructor
  · intro h
    have hpre := (prefixWord_eq_iff (firstCutTime v X) X γ).mp h
    have hc := ((firstCutTime_eq_pos_iff v X hγ.1).mp hpre.1).1
    refine ⟨hpre.2,fun k => ?_⟩
    have hk := hc.2 k
    rw [hpre.2 γ.1 le_rfl] at hk
    change 0 ≤ height v (X (γ.1+k) + -(wordPath γ γ.1))
    rw [height_add, height_neg]
    linarith
  · rintro ⟨hpre,hD⟩
    have hrec : strictRecord v X γ.1 := by
      refine ⟨hγ.1,fun i hi => ?_⟩
      rw [hpre i hi.le,hpre γ.1 le_rfl]
      exact (hγ.2.2.2.1 i hi).2
    have hc : trueCut v X γ.1 := by
      refine ⟨hrec,fun k => ?_⟩
      have hk := hD k
      change 0 ≤ height v (X (γ.1+k) + -(wordPath γ γ.1)) at hk
      rw [height_add,height_neg] at hk
      rw [hpre γ.1 le_rfl]
      linarith
    have hmin : ∀ j < γ.1, ¬trueCut v X j := by
      intro j hj ht
      have hr : strictRecord v (wordPath γ) j := by
        refine ⟨ht.1.1,fun i hi => ?_⟩
        rw [← hpre i (by omega),← hpre j hj.le]
        exact ht.1.2 i hi
      obtain ⟨k,hjk,hkm,hk⟩ := hγ.2.2.2.2 j hj hr
      have hk' := ht.2 (k-j)
      rw [Nat.add_sub_of_le hjk.le,hpre k hkm.le,hpre j hj.le] at hk'
      exact (not_lt_of_ge hk') hk
    have hm := (firstCutTime_eq_pos_iff v X hγ.1).mpr ⟨hc,hmin⟩
    exact (prefixWord_eq_iff (firstCutTime v X) X γ).mpr ⟨hm,hpre⟩

lemma firstWord_event {d : ℕ} (v : Fin d → ℝ) (γ : Word d)
    (hγ : RegenerationWord v γ) (E : Set (Path d)) :
    {X | firstWord v X = γ ∧ cutSuffix v X ∈ E} =
      pathCylinder γ.1 (wordPath γ) ∩ tailPath γ.1 ⁻¹'
        (shiftPath (-(wordPath γ γ.1)) ⁻¹' (E ∩ nonBacktracking v)) := by
  ext X
  constructor
  · rintro ⟨h,hE⟩
    obtain ⟨hpre,hD⟩ := (firstWord_eq_iff v X γ hγ).mp h
    have hm : firstCutTime v X = γ.1 := congrArg Sigma.fst h
    refine ⟨hpre,?_,hD⟩
    simpa only [cutSuffix,hm,hpre γ.1 le_rfl] using hE
  · rintro ⟨hpre,hE,hD⟩
    have h := (firstWord_eq_iff v X γ hγ).mpr ⟨hpre,hD⟩
    have hm : firstCutTime v X = γ.1 := congrArg Sigma.fst h
    refine ⟨h,?_⟩
    simpa only [cutSuffix,hm,hpre γ.1 le_rfl] using hE

lemma firstWord_event_subset_nonBacktracking {d : ℕ} (v : Fin d → ℝ) (γ : Word d)
    (hγ : RegenerationWord v γ) : {X | firstWord v X = γ} ⊆ nonBacktracking v := by
  intro X hX n
  obtain ⟨hpre,hD⟩ := (firstWord_eq_iff v X γ hγ).mp hX
  by_cases hn : n < γ.1
  · rw [hpre n hn.le]; exact (hγ.2.2.2.1 n hn).1
  · have hk := hD (n-γ.1)
    change 0 ≤ height v (X (γ.1+(n-γ.1)) + -(wordPath γ γ.1)) at hk
    rw [Nat.add_sub_of_le (by omega),height_add,height_neg] at hk
    have hh := hγ.2.2.2.1 0 hγ.1
    rw [hγ.2.1,height_zero] at hh
    change 0 ≤ height v (X n)
    linarith

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

noncomputable def conditioned {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (v : Fin d → ℝ) : Measure (Path d) := (annealed μ 0)[|nonBacktracking v]

lemma conditioned_probability {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (v : Fin d → ℝ) (hp : 0 < annealed μ 0 (nonBacktracking v)) :
    IsProbabilityMeasure (conditioned μ v) := cond_isProbabilityMeasure hp.ne'

lemma ae_conditioned_firstWord {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) :
    ∀ᵐ X ∂conditioned μ v, RegenerationWord v (firstWord v X) := by
  have hac : conditioned μ v ≪ annealed μ 0 := cond_absolutelyContinuous
  have hfin := hac.ae_le (finite_supremum μ hell 0 v hv)
  have hcut := hac.ae_le (ae_infinitely_trueCuts μ 0 v hp)
  have hNN := hac.ae_le (ae_start_and_nearestNeighbour μ 0)
  filter_upwards [ae_cond_mem (μ := annealed μ 0) (measurableSet_nonBacktracking v),
    hfin,hcut,hNN] with X hD hf hc hs
  apply firstWord_regeneration v X hs.1 hs.2 hD
  have hu : ¬∃ b : ℝ, ∀ n, height v (X n) ≤ b := by
    intro hb
    obtain ⟨n,hn⟩ := eventually_atTop.mp ((hf hb).eventually (eventually_lt_atBot (-1)))
    have hh := hD n
    have := hn n le_rfl
    linarith
  obtain ⟨n,_,hn⟩ := hc hu 0
  exact ⟨n,hn⟩

lemma conditioned_firstWord_suffix {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (v : Fin d → ℝ) (γ : Word d) (hγ : RegenerationWord v γ)
    {E : Set (Path d)} (hE : MeasurableSet E) :
    conditioned μ v {X | firstWord v X = γ ∧ cutSuffix v X ∈ E} =
      annealedWordWeight μ γ * conditioned μ v E := by
  change (annealed μ 0)[{X | firstWord v X = γ ∧ cutSuffix v X ∈ E}|nonBacktracking v] = _
  rw [cond_apply (measurableSet_nonBacktracking v)]
  have hsub : {X | firstWord v X = γ ∧ cutSuffix v X ∈ E} ⊆ nonBacktracking v :=
    fun _ h => firstWord_event_subset_nonBacktracking v γ hγ h.1
  rw [Set.inter_eq_right.mpr hsub,firstWord_event v γ hγ E,
    annealed_record_relative_tail μ v 0 γ.1 (wordPath γ)
      (fun i hi => (hγ.2.2.2.1 i hi).2) hE,
    annealed_cylinder,ite_eq_left hγ.2.1.symm]
  unfold conditioned
  rw [cond_apply (measurableSet_nonBacktracking v),Set.inter_comm (nonBacktracking v) E]
  unfold annealedWordWeight
  ac_rfl

lemma measure_eq_tsum_fibres {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [Countable A] [MeasurableSingletonClass A] (P : Measure Ω) (f : Ω → A)
    (hf : Measurable f) {E : Set Ω} (hE : MeasurableSet E) :
    P E = ∑' a, P ({X | f X = a} ∩ E) := by
  have heq : E = ⋃ a, {X | f X = a} ∩ E := by
    ext X; simp
  calc
    P E = P (⋃ a, {X | f X = a} ∩ E) := congrArg P heq
    _ = _ := measure_iUnion (fun a b hab => ?_) (fun a => ?_)
  · apply Set.disjoint_left.mpr
    rintro X ⟨ha,_⟩ ⟨hb,_⟩
    exact hab (ha.symm.trans hb)
  · exact ((measurableSet_singleton a).preimage hf).inter hE

noncomputable def slabLaw {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (v : Fin d → ℝ) : Measure (Word d) := (conditioned μ v).map (firstWord v)

lemma slabLaw_probability {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (v : Fin d → ℝ) (hp : 0 < annealed μ 0 (nonBacktracking v)) :
    IsProbabilityMeasure (slabLaw μ v) := by
  let := conditioned_probability μ v hp
  exact probabilityMeasure_map (measurable_firstWord v).aemeasurable

lemma slabLaw_atom {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (v : Fin d → ℝ) (hp : 0 < annealed μ 0 (nonBacktracking v))
    (γ : Word d) (hγ : RegenerationWord v γ) :
    slabLaw μ v {γ} = annealedWordWeight μ γ := by
  let := conditioned_probability μ v hp
  have h := conditioned_firstWord_suffix μ v γ hγ MeasurableSet.univ
  rw [slabLaw, Measure.map_apply (measurable_firstWord v) (measurableSet_singleton γ)]
  change conditioned μ v {X | firstWord v X = γ} = _
  simpa only [Set.mem_univ, and_true, measure_univ, mul_one] using h

lemma ae_slabLaw_regeneration {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) :
    ∀ᵐ γ ∂slabLaw μ v, RegenerationWord v γ := by
  exact (ae_map_iff (measurable_firstWord v).aemeasurable
    (Set.to_countable {γ : Word d | RegenerationWord v γ}).measurableSet).mpr
      (ae_conditioned_firstWord μ hell v hv hp)

lemma firstWord_suffix_factorization {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) (γ : Word d)
    {E : Set (Path d)} (hE : MeasurableSet E) :
    conditioned μ v {X | firstWord v X = γ ∧ cutSuffix v X ∈ E} =
      slabLaw μ v {γ} * conditioned μ v E := by
  by_cases hγ : RegenerationWord v γ
  · rw [conditioned_firstWord_suffix μ v γ hγ hE,slabLaw_atom μ v hp γ hγ]
  · have hz : conditioned μ v {X | firstWord v X = γ} = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [ae_conditioned_firstWord μ hell v hv hp] with X hX hEq
      exact hγ (hEq ▸ hX)
    have hν : slabLaw μ v {γ} = 0 := by
      rw [slabLaw,Measure.map_apply (measurable_firstWord v) (measurableSet_singleton γ)]
      exact hz
    rw [hν,zero_mul]
    exact measure_mono_null (fun _ h => h.1) hz

lemma cutSuffix_measurePreserving {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) :
    MeasurePreserving (cutSuffix v) (conditioned μ v) (conditioned μ v) := by
  let := conditioned_probability μ v hp
  let := slabLaw_probability μ v hp
  refine ⟨measurable_cutSuffix v,?_⟩
  apply Measure.ext
  intro E hE
  rw [Measure.map_apply (measurable_cutSuffix v) hE,
    measure_eq_tsum_fibres (conditioned μ v) (firstWord v) (measurable_firstWord v)
      ((measurable_cutSuffix v) hE)]
  simp_rw [show ∀ γ, {X | firstWord v X = γ} ∩ cutSuffix v ⁻¹' E =
    {X | firstWord v X = γ ∧ cutSuffix v X ∈ E} from fun _ => rfl,
    firstWord_suffix_factorization μ hell v hv hp _ hE, ENNReal.tsum_mul_right]
  have hsum := measure_eq_tsum_fibres (slabLaw μ v) id measurable_id MeasurableSet.univ
  simp only [id_eq,Set.inter_univ,Set.ofPred_eq_eq_singleton,measure_univ] at hsum
  rw [← hsum,one_mul]

noncomputable def slabs {d : ℕ} (v : Fin d → ℝ) (X : Path d) (k : ℕ) : Word d :=
  firstWord v ((cutSuffix v)^[k] X)

lemma measurable_slabs {d : ℕ} (v : Fin d → ℝ) : Measurable (slabs v) :=
  Measurable.of_eval (fun k => (measurable_firstWord v).comp ((measurable_cutSuffix v).iterate k))

lemma slabs_prefix_mass {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) (n : ℕ) (γ : ℕ → Word d) :
    conditioned μ v {X | ∀ i < n, slabs v X i = γ i} =
      ∏ i ∈ Finset.range n, slabLaw μ v {γ i} := by
  let := conditioned_probability μ v hp
  induction n generalizing γ with
  | zero => simp
  | succ n ih =>
    have heq : {X | ∀ i < n+1, slabs v X i = γ i} =
        {X | firstWord v X = γ 0 ∧ cutSuffix v X ∈
          {Y | ∀ i < n, slabs v Y i = γ (i+1)}} := by
      ext X
      simp only [Set.mem_ofPred_eq]
      constructor
      · intro h
        refine ⟨h 0 (Nat.succ_pos _),fun i hi => ?_⟩
        simpa only [slabs,Function.iterate_succ_apply] using h (i+1) (by omega)
      · rintro ⟨h0,h⟩ i hi
        cases i with
        | zero => exact h0
        | succ i => simpa only [slabs,Function.iterate_succ_apply] using h i (by omega)
    have hE : MeasurableSet {Y | ∀ i < n, slabs v Y i = γ (i+1)} := by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun _ =>
        (measurableSet_singleton (γ (i+1))).preimage ((measurable_pi_apply i).comp (measurable_slabs v))))
    rw [heq,firstWord_suffix_factorization μ hell v hv hp _ hE,ih]
    rw [Finset.prod_range_succ']
    exact mul_comm _ _

lemma slabs_map_eq_infinitePi {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) :
    (conditioned μ v).map (slabs v) = Measure.infinitePi (fun _ : ℕ => slabLaw μ v) := by
  classical
  let := conditioned_probability μ v hp
  let := slabLaw_probability μ v hp
  apply measure_eq_of_prefix
  intro n
  apply Measure.ext_of_singleton
  intro a
  let γ : ℕ → Word d := fun i => if hi : i ≤ n then a ⟨i,Finset.mem_Iic.mpr hi⟩ else
    a ⟨0,Finset.mem_Iic.mpr (Nat.zero_le n)⟩
  have heq : (frestrictLe n : (ℕ → Word d) → (Finset.Iic n → Word d)) ⁻¹' {a} = (↑(Finset.range (n+1)) : Set ℕ).pi (fun i => {γ i}) := by
    ext b
    simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_pi,Finset.mem_coe,Finset.mem_range]
    constructor
    · intro h i hi
      have hh := congr_fun h ⟨i,Finset.mem_Iic.mpr (by omega)⟩
      simpa [γ,show i ≤ n by omega] using hh
    · intro h
      funext i
      have hi := Finset.mem_Iic.mp i.property
      simpa [γ,hi] using h i (by omega)
  rw [Measure.map_apply (measurable_frestrictLe n) (measurableSet_singleton a),
    Measure.map_apply (measurable_frestrictLe n) (measurableSet_singleton a),heq,
    Measure.map_apply (measurable_slabs v) (MeasurableSet.pi (Finset.countable_toSet _) (fun _ _ => measurableSet_singleton _)),
    Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
  have hpre : slabs v ⁻¹' (↑(Finset.range (n+1)) : Set ℕ).pi (fun i => {γ i}) =
      {X | ∀ i < n+1, slabs v X i = γ i} := by
    ext X
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_singleton_iff,
      Finset.mem_coe, Finset.mem_range, Set.mem_ofPred_eq]
  rw [hpre]
  exact slabs_prefix_mass μ hell v hv hp (n+1) γ

lemma slabs_marginal {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) (k : ℕ) :
    (conditioned μ v).map (fun X => slabs v X k) = slabLaw μ v := by
  rw [show (fun X => slabs v X k) = firstWord v ∘ (cutSuffix v)^[k] from rfl,
    ← Measure.map_map (measurable_firstWord v) ((measurable_cutSuffix v).iterate k),
    ((cutSuffix_measurePreserving μ hell v hv hp).iterate k).map_eq]
  rfl

lemma slabs_iid {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) :
    iIndepFun (fun k X => slabs v X k) (conditioned μ v) := by
  let := conditioned_probability μ v hp
  apply (iIndepFun_iff_map_fun_eq_infinitePi_map (fun k =>
    (measurable_pi_apply k).comp (measurable_slabs v))).mpr
  change (conditioned μ v).map (slabs v) = Measure.infinitePi
    (fun k => (conditioned μ v).map (fun X => slabs v X k))
  rw [slabs_map_eq_infinitePi μ hell v hv hp]
  congr 1
  funext k
  exact (slabs_marginal μ hell v hv hp k).symm

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

lemma height_sub {d : ℕ} (v : Fin d → ℝ) (x y : Site d) :
    height v (x-y) = height v x - height v y := by
  rw [sub_eq_add_neg,height_add,height_neg,sub_eq_add_neg]

noncomputable def recordCount {d : ℕ} (v : Fin d → ℝ) (X : Path d) (n : ℕ) : ℕ :=
  (Finset.range (n+1)).filter (strictRecord v X) |>.card

lemma recordCount_zero {d : ℕ} (v : Fin d → ℝ) (X : Path d) : recordCount v X 0 = 0 := by
  classical
  simp [recordCount,strictRecord]

lemma recordCount_succ {d : ℕ} (v : Fin d → ℝ) (X : Path d) (n : ℕ) :
    recordCount v X (n+1) = recordCount v X n + if strictRecord v X (n+1) then 1 else 0 := by
  classical
  rw [recordCount,Finset.range_add_one,Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem]
    · rfl
    · simp
  · rfl

lemma recordCount_mono {d : ℕ} (v : Fin d → ℝ) (X : Path d) : Monotone (recordCount v X) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [recordCount_succ]
  exact Nat.le_add_right _ _

lemma recordCount_prefix {d : ℕ} (v : Fin d → ℝ) {X Y : Path d} {n : ℕ}
    (h : Y ∈ pathCylinder n X) : recordCount v Y n = recordCount v X n := by
  classical
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro i hi
  have hin : i ≤ n := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hi
  constructor <;> intro hr
  · exact strictRecord_prefix v hr (fun j hj => (h j (hj.trans hin)).symm)
  · exact strictRecord_prefix v hr (fun j hj => h j (hj.trans hin))

lemma measurable_recordCount {d : ℕ} (v : Fin d → ℝ) (n : ℕ) :
    Measurable (fun X : Path d => recordCount v X n) := by
  classical
  induction n with
  | zero => simpa only [recordCount_zero] using (measurable_const : Measurable (fun _ : Path d => (0 : ℕ)))
  | succ n ih =>
    simp_rw [recordCount_succ]
    exact ih.add (Measurable.ite (measurableSet_strictRecord v (n+1)) measurable_const measurable_const)

lemma recordCount_strict {d : ℕ} (v : Fin d → ℝ) (X : Path d) {m n : ℕ}
    (hmn : m < n) (hn : strictRecord v X n) : recordCount v X m < recordCount v X n := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn.1)
  rw [recordCount_succ,ite_eq_left hn]
  exact Nat.lt_succ_of_le (recordCount_mono v X (by omega))

lemma recordCount_boundary_unique {d : ℕ} (v : Fin d → ℝ) (X : Path d) {m n : ℕ}
    (hm : m = 0 ∨ strictRecord v X m) (hn : n = 0 ∨ strictRecord v X n)
    (he : recordCount v X m = recordCount v X n) : m = n := by
  rcases lt_trichotomy m n with h|h|h
  · have hnr : strictRecord v X n := hn.resolve_left (by omega)
    exact False.elim ((ne_of_lt (recordCount_strict v X h hnr)) he)
  · exact h
  · have hmr : strictRecord v X m := hm.resolve_left (by omega)
    exact False.elim ((ne_of_lt (recordCount_strict v X h hmr)) he.symm)

lemma unbounded_recordCount {d : ℕ} (v : Fin d → ℝ) (X : Path d)
    (hu : ¬∃ b : ℝ, ∀ n, height v (X n) ≤ b) : ∀ j, ∃ n, j ≤ recordCount v X n := by
  intro j
  induction j with
  | zero => exact ⟨0,Nat.zero_le _⟩
  | succ j ih =>
    obtain ⟨m,hm⟩ := ih
    obtain ⟨n,hmn,hn⟩ := unbounded_has_later_strictRecord v X hu m
    exact ⟨n,Nat.succ_le_of_lt (hm.trans_lt (recordCount_strict v X hmn hn))⟩

lemma exists_record_index {d : ℕ} (v : Fin d → ℝ) (X : Path d)
    (hu : ¬∃ b : ℝ, ∀ n, height v (X n) ≤ b) (j : ℕ) :
    ∃ n, (n = 0 ∨ strictRecord v X n) ∧ recordCount v X n = j := by
  classical
  by_cases hj : j = 0
  · exact ⟨0,Or.inl rfl,by rw [recordCount_zero,hj]⟩
  have hex := unbounded_recordCount v X hu j
  let n := Nat.find hex
  have hn : j ≤ recordCount v X n := Nat.find_spec hex
  have hn0 : 0 < n := by
    by_contra h
    have he : n = 0 := by omega
    rw [he,recordCount_zero] at hn
    omega
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn0)
  have hprev : recordCount v X k < j := Nat.lt_of_not_ge (Nat.find_min hex (by omega : k < n))
  rw [hk,recordCount_succ] at hn
  split_ifs at hn with hr
  · exact ⟨n,Or.inr (by simpa only [hk] using hr),by rw [hk,recordCount_succ,ite_eq_left hr]; omega⟩
  · omega

def relativeTail {d : ℕ} (n : ℕ) (X : Path d) : Path d :=
  shiftPath (-(X n)) (tailPath n X)

lemma relativeTail_apply {d : ℕ} (n : ℕ) (X : Path d) (k : ℕ) :
    relativeTail n X k = X (n+k) - X n := rfl

lemma relativeTail_zero {d : ℕ} (n : ℕ) (X : Path d) : relativeTail n X 0 = 0 := by
  simp [relativeTail_apply]

lemma measurable_relativeTail {d : ℕ} (n : ℕ) : Measurable (relativeTail (d := d) n) := by
  apply Measurable.of_eval
  intro k
  change Measurable (fun X : Path d => X (n+k) - X n)
  exact (measurable_pi_apply (n+k)).sub (measurable_pi_apply n)

lemma strictRecord_relativeTail {d : ℕ} (v : Fin d → ℝ) (X : Path d) {n : ℕ}
    (hn : n = 0 ∨ strictRecord v X n) {k : ℕ} (hk : 0 < k) :
    strictRecord v (relativeTail n X) k ↔ strictRecord v X (n+k) := by
  change (0 < k ∧ ∀ i < k, height v (X (n+i) - X n) < height v (X (n+k) - X n)) ↔ _
  simp_rw [height_sub]
  constructor
  · rintro ⟨_,hr⟩
    refine ⟨by omega,fun i hi => ?_⟩
    by_cases hin : n ≤ i
    · have hh := hr (i-n) (by omega)
      rw [Nat.add_sub_of_le hin] at hh
      linarith
    · have hh := hr 0 hk
      rw [Nat.add_zero] at hh
      have hi' : i < n := by omega
      have hnr := hn.resolve_left (by omega)
      exact (hnr.2 i hi').trans (by linarith)
  · intro hr
    refine ⟨hk,fun i hi => ?_⟩
    have hh := hr.2 (n+i) (by omega)
    linarith

lemma trueCut_relativeTail {d : ℕ} (v : Fin d → ℝ) (X : Path d) {n : ℕ}
    (hn : n = 0 ∨ strictRecord v X n) {k : ℕ} (hk : 0 < k) :
    trueCut v (relativeTail n X) k ↔ trueCut v X (n+k) := by
  rw [trueCut,trueCut,strictRecord_relativeTail v X hn hk]
  simp only [relativeTail_apply,height_sub,Nat.add_assoc,sub_le_sub_iff_right]

lemma recordCount_relativeTail {d : ℕ} (v : Fin d → ℝ) (X : Path d) {n : ℕ}
    (hn : n = 0 ∨ strictRecord v X n) (k : ℕ) :
    recordCount v X (n+k) = recordCount v X n + recordCount v (relativeTail n X) k := by
  classical
  induction k with
  | zero => simp [recordCount_zero]
  | succ k ih =>
    rw [Nat.add_succ,recordCount_succ,recordCount_succ,ih,
      strictRecord_relativeTail v X hn (Nat.succ_pos k),Nat.add_assoc]
    simp only [Nat.succ_eq_add_one,Nat.add_assoc]

def noCutBeforeRecord {d : ℕ} (v : Fin d → ℝ) (r : ℕ) : Set (Path d) :=
  {X | ∀ n, trueCut v X n → r < recordCount v X n}

lemma measurableSet_noCutBeforeRecord {d : ℕ} (v : Fin d → ℝ) (r : ℕ) :
    MeasurableSet (noCutBeforeRecord v r) := by
  simp only [noCutBeforeRecord,Set.ofPred_forall,imp_iff_not_or,Set.ofPred_or]
  exact MeasurableSet.iInter (fun n => (measurableSet_trueCut v n).compl.union
    (measurableSet_lt measurable_const (measurable_recordCount v n)))

lemma noCutBeforeRecord_iff {d : ℕ} (v : Fin d → ℝ) (X : Path d)
    (hc : ∃ n, trueCut v X n) (r : ℕ) : X ∈ noCutBeforeRecord v r ↔
      r < recordCount v X (firstCutTime v X) := by
  obtain ⟨hcut,hmin⟩ := firstCutTime_spec v X hc
  constructor
  · intro h; exact h _ hcut
  · intro h n hn
    have ht : firstCutTime v X ≤ n := by
      by_contra hx
      exact hmin n (by omega) hn
    exact h.trans_le (recordCount_mono v X ht)

def recordPrefix {d : ℕ} (v : Fin d → ℝ) (j : ℕ) (X : Path d) (n : ℕ) : Prop :=
  (n = 0 ∨ strictRecord v X n) ∧ recordCount v X n = j ∧
    ∀ i ≤ n, 0 ≤ height v (X i)

lemma recordPrefix_prefix {d : ℕ} (v : Fin d → ℝ) (j : ℕ) {X Y : Path d} {n : ℕ}
    (hX : recordPrefix v j X n) (hY : Y ∈ pathCylinder n X) : recordPrefix v j Y n := by
  refine ⟨hX.1.imp id (fun hr => strictRecord_prefix v hr hY),?_,fun i hi => ?_⟩
  · rw [recordCount_prefix v hY];exact hX.2.1
  · rw [hY i hi];exact hX.2.2 i hi

lemma recordPrefix_unique {d : ℕ} (v : Fin d → ℝ) (j : ℕ) (X : Path d) {m n : ℕ}
    (hm : recordPrefix v j X m) (hn : recordPrefix v j X n) : m = n :=
  recordCount_boundary_unique v X hm.1 hn.1 (hm.2.1.trans hn.2.1.symm)

lemma measurableSet_recordPrefix {d : ℕ} (v : Fin d → ℝ) (j n : ℕ) :
    MeasurableSet {X : Path d | recordPrefix v j X n} := by
  simp only [recordPrefix,Set.ofPred_and,Set.ofPred_or,Set.ofPred_forall]
  refine ((MeasurableSet.const _).union (measurableSet_strictRecord v n)).inter
    (((measurableSet_singleton j).preimage (measurable_recordCount v n)).inter ?_)
  exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun _ =>
    measurableSet_le measurable_const ((measurable_of_countable (height v)).comp (measurable_pi_apply i))))

lemma relativeTail_nonBacktracking_iff {d : ℕ} (v : Fin d → ℝ) (X : Path d) (n : ℕ) :
    relativeTail n X ∈ nonBacktracking v ↔ ∀ k, height v (X n) ≤ height v (X (n+k)) := by
  simp only [nonBacktracking,neverBelow,Set.mem_ofPred_eq,relativeTail_apply,height_sub,sub_nonneg]

lemma recordPrefix_tail_subset_nonBacktracking {d : ℕ} (v : Fin d → ℝ) (j n : ℕ)
    (X : Path d) (hpre : recordPrefix v j X n) (hD : relativeTail n X ∈ nonBacktracking v) :
    X ∈ nonBacktracking v := by
  intro k
  by_cases hk : k ≤ n
  · exact hpre.2.2 k hk
  · have hh := (relativeTail_nonBacktracking_iff v X n).mp hD (k-n)
    rw [Nat.add_sub_of_le (by omega : n ≤ k)] at hh
    exact (hpre.2.2 n le_rfl).trans hh

lemma relativeTail_cylinder {d : ℕ} (n : ℕ) (X γ : Path d)
    (h : X ∈ pathCylinder n γ) : relativeTail n X = shiftPath (-(γ n)) (tailPath n X) := by
  rw [relativeTail,h n le_rfl]

lemma conditioned_recordCylinder {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (v : Fin d → ℝ) (j n : ℕ) (γ : Path d) (hγ : recordPrefix v j γ n)
    {E : Set (Path d)} (hE : MeasurableSet E) :
    conditioned μ v (pathCylinder n γ ∩ relativeTail n ⁻¹' (E ∩ nonBacktracking v)) =
      annealed μ 0 (pathCylinder n γ) * conditioned μ v E := by
  have hsub : pathCylinder n γ ∩ relativeTail n ⁻¹' (E ∩ nonBacktracking v) ⊆ nonBacktracking v := by
    rintro X ⟨hX,hY⟩
    exact recordPrefix_tail_subset_nonBacktracking v j n X (recordPrefix_prefix v j hγ hX) hY.2
  have heq : pathCylinder n γ ∩ relativeTail n ⁻¹' (E ∩ nonBacktracking v) =
      pathCylinder n γ ∩ tailPath n ⁻¹' (shiftPath (-(γ n)) ⁻¹' (E ∩ nonBacktracking v)) := by
    ext X
    constructor <;> rintro ⟨hX,hY⟩ <;> refine ⟨hX,?_⟩
    · simpa only [Set.mem_preimage,relativeTail_cylinder n X γ hX] using hY
    · simpa only [Set.mem_preimage,relativeTail_cylinder n X γ hX] using hY
  change (annealed μ 0)[_|nonBacktracking v] = _
  rw [cond_apply (measurableSet_nonBacktracking v),Set.inter_eq_right.mpr hsub,heq,
    annealed_record_relative_tail μ v 0 n γ (fun i hi => ?_) hE]
  · unfold conditioned
    rw [cond_apply (measurableSet_nonBacktracking v),Set.inter_comm (nonBacktracking v) E]
    ac_rfl
  · exact (hγ.1.resolve_left (by omega)).2 i hi

lemma conditioned_recordPrefix {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (v : Fin d → ℝ) (j n : ℕ) {E : Set (Path d)} (hE : MeasurableSet E) :
    conditioned μ v ({X | recordPrefix v j X n} ∩ relativeTail n ⁻¹' (E ∩ nonBacktracking v)) =
      annealed μ 0 {X | recordPrefix v j X n} * conditioned μ v E := by
  let B : Set (Path d) := {X | recordPrefix v j X n}
  have hB := measurableSet_recordPrefix v j n
  have hF := (measurable_relativeTail n) (hE.inter (measurableSet_nonBacktracking v))
  rw [measure_eq_tsum_fibres (conditioned μ v) (frestrictLe n) (measurable_frestrictLe n) (hB.inter hF),
    measure_eq_tsum_fibres (annealed μ 0) (frestrictLe n) (measurable_frestrictLe n) hB,
    ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro a
  let γ := extendPrefix n a
  have hcyl : {X : Path d | frestrictLe n X = a} = pathCylinder n γ := by
    rw [pathCylinder_eq_fiber,restrict_extendPrefix]
    rfl
  rw [hcyl]
  by_cases hγ : recordPrefix v j γ n
  · have hsub : pathCylinder n γ ⊆ B := fun _ h => recordPrefix_prefix v j hγ h
    have heq : pathCylinder n γ ∩ ({X | recordPrefix v j X n} ∩ relativeTail n ⁻¹' (E ∩ nonBacktracking v)) =
        pathCylinder n γ ∩ relativeTail n ⁻¹' (E ∩ nonBacktracking v) := by
      rw [← Set.inter_assoc,Set.inter_eq_left.mpr hsub]
    rw [heq,Set.inter_eq_left.mpr hsub]
    exact conditioned_recordCylinder μ v j n γ hγ hE
  · have hdis : pathCylinder n γ ∩ B = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro X ⟨hX,hB'⟩
      exact hγ (recordPrefix_prefix v j hB' (fun i hi => (hX i hi).symm))
    rw [← Set.inter_assoc,hdis,Set.empty_inter,measure_empty,measure_empty,zero_mul]

def reachRecord {d : ℕ} (v : Fin d → ℝ) (j : ℕ) : Set (Path d) :=
  ⋃ n, {X | recordPrefix v j X n}

def recordTailEvent {d : ℕ} (v : Fin d → ℝ) (j : ℕ) (E : Set (Path d)) : Set (Path d) :=
  ⋃ n, {X | recordPrefix v j X n} ∩ relativeTail n ⁻¹' (E ∩ nonBacktracking v)

lemma measurableSet_reachRecord {d : ℕ} (v : Fin d → ℝ) (j : ℕ) :
    MeasurableSet (reachRecord v j) := MeasurableSet.iUnion (fun n => measurableSet_recordPrefix v j n)

lemma measurableSet_recordTailEvent {d : ℕ} (v : Fin d → ℝ) (j : ℕ)
    {E : Set (Path d)} (hE : MeasurableSet E) : MeasurableSet (recordTailEvent v j E) :=
  MeasurableSet.iUnion (fun n => (measurableSet_recordPrefix v j n).inter
    ((measurable_relativeTail n) (hE.inter (measurableSet_nonBacktracking v))))

lemma recordPrefix_disjoint {d : ℕ} (v : Fin d → ℝ) (j : ℕ) :
    Pairwise (fun m n => Disjoint {X : Path d | recordPrefix v j X m}
      {X : Path d | recordPrefix v j X n}) := by
  intro m n hmn
  apply Set.disjoint_left.mpr
  intro X hm hn
  exact hmn (recordPrefix_unique v j X hm hn)

lemma recordTail_factorization {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (v : Fin d → ℝ) (j : ℕ) {E : Set (Path d)} (hE : MeasurableSet E) :
    conditioned μ v (recordTailEvent v j E) = annealed μ 0 (reachRecord v j) * conditioned μ v E := by
  rw [recordTailEvent,measure_iUnion (fun m n hmn =>
    (recordPrefix_disjoint v j hmn).mono Set.inter_subset_left Set.inter_subset_left)
      (fun n => (measurableSet_recordPrefix v j n).inter
        ((measurable_relativeTail n) (hE.inter (measurableSet_nonBacktracking v))))]
  simp_rw [conditioned_recordPrefix μ v j _ hE,ENNReal.tsum_mul_right]
  rw [reachRecord,measure_iUnion (recordPrefix_disjoint v j) (measurableSet_recordPrefix v j)]

lemma reachRecord_mass_ge {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0) (j : ℕ) :
    annealed μ 0 (nonBacktracking v) ≤ annealed μ 0 (reachRecord v j) := by
  apply measure_mono_ae
  filter_upwards [finite_supremum μ hell 0 v hv] with X hfin hD
  have hu : ¬∃ b : ℝ, ∀ n, height v (X n) ≤ b := by
    intro hb
    obtain ⟨n,hn⟩ := eventually_atTop.mp ((hfin hb).eventually (eventually_lt_atBot (-1)))
    have hh := hD n
    have := hn n le_rfl
    linarith
  obtain ⟨n,hn,hj⟩ := exists_record_index v X hu j
  exact Set.mem_iUnion.mpr ⟨n,hn,hj,fun i _ => hD i⟩

lemma recordTailEvent_disjoint {d : ℕ} (v : Fin d → ℝ) (N : ℕ) :
    (Finset.range (N+1) : Set ℕ).Pairwise (fun j k =>
      Disjoint (recordTailEvent v j (noCutBeforeRecord v (N-j)))
        (recordTailEvent v k (noCutBeforeRecord v (N-k)))) := by
  intro j hj k hk hjk
  simp only [Finset.mem_coe,Finset.mem_range] at hj hk
  wlog hlt : j < k generalizing j k
  · exact (this hjk.symm hk hj (by omega)).symm
  apply Set.disjoint_left.mpr
  intro X hX hY
  obtain ⟨m,hm,hM⟩ := Set.mem_iUnion.mp hX
  obtain ⟨n,hn,hN⟩ := Set.mem_iUnion.mp hY
  have hmn : m < n := by
    by_contra h
    have hcount := recordCount_mono v X (show n ≤ m by omega)
    rw [hm.2.1,hn.2.1] at hcount
    omega
  have hnpos : 0 < n := by omega
  have hncut : trueCut v X n := ⟨hn.1.resolve_left (Nat.ne_of_gt hnpos),
    (relativeTail_nonBacktracking_iff v X n).mp hN.2⟩
  have hsuf : trueCut v (relativeTail m X) (n-m) := by
    apply (trueCut_relativeTail v X hm.1 (by omega)).mpr
    simpa only [Nat.add_sub_of_le hmn.le] using hncut
  have hcontra := hM.1 (n-m) hsuf
  have hcount := recordCount_relativeTail v X hm.1 (n-m)
  rw [Nat.add_sub_of_le hmn.le,hm.2.1,hn.2.1] at hcount
  omega

lemma record_tail_sum_bound {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) (N : ℕ) :
    annealed μ 0 (nonBacktracking v) *
      ∑ j ∈ Finset.range (N+1), conditioned μ v (noCutBeforeRecord v (N-j)) ≤ 1 := by
  let := conditioned_probability μ v hp
  calc
    _ = ∑ j ∈ Finset.range (N+1), annealed μ 0 (nonBacktracking v) *
        conditioned μ v (noCutBeforeRecord v (N-j)) := Finset.mul_sum ..
    _ ≤ ∑ j ∈ Finset.range (N+1), conditioned μ v
        (recordTailEvent v j (noCutBeforeRecord v (N-j))) := by
      apply Finset.sum_le_sum
      intro j _
      rw [recordTail_factorization μ v j (measurableSet_noCutBeforeRecord v (N-j))]
      exact mul_le_mul' (reachRecord_mass_ge μ hell v hv j) le_rfl
    _ = conditioned μ v (⋃ j ∈ Finset.range (N+1),
        recordTailEvent v j (noCutBeforeRecord v (N-j))) := by
      symm
      exact measure_biUnion_finset (recordTailEvent_disjoint v N)
        (fun j _ => measurableSet_recordTailEvent v j (measurableSet_noCutBeforeRecord v (N-j)))
    _ ≤ 1 := prob_le_one

lemma lintegral_nat_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : Ω → ℕ) (hf : Measurable f) :
    (∫⁻ x, (f x : ℝ≥0∞) ∂P) = ∑' j : ℕ, P {x | j < f x} := by
  classical
  have hA (j : ℕ) : MeasurableSet {x | j < f x} := measurableSet_lt measurable_const hf
  have hexp (x : Ω) : (f x : ℝ≥0∞) = ∑' j : ℕ, ({x | j < f x}.indicator (fun _ => (1 : ℝ≥0∞))) x := by
    rw [tsum_eq_sum (s := Finset.range (f x))]
    · symm
      calc
        _ = ∑ _j ∈ Finset.range (f x), (1 : ℝ≥0∞) := by
          apply Finset.sum_congr rfl
          intro j hj
          simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_left (Finset.mem_range.mp hj)]
        _ = _ := by simp
    · intro j hj
      simp only [Finset.mem_range, not_lt] at hj
      simp [Set.indicator_of_notMem, not_lt.mpr hj]
  simp_rw [hexp,lintegral_tsum (fun j => (measurable_const.indicator (hA j)).aemeasurable)]
  apply tsum_congr
  intro j
  simp [lintegral_indicator (hA j)]

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

noncomputable def slabRecords {d : ℕ} (v : Fin d → ℝ) (γ : Word d) : ℕ :=
  recordCount v (wordPath γ) γ.1

def slabWidth {d : ℕ} (v : Fin d → ℝ) (γ : Word d) : ℝ :=
  height v (wordPath γ γ.1)

lemma slabRecords_firstWord {d : ℕ} (v : Fin d → ℝ) (X : Path d) :
    slabRecords v (firstWord v X) = recordCount v X (firstCutTime v X) := by
  apply recordCount_prefix
  intro i hi
  exact wordPath_prefixWord _ X hi

lemma slabRecords_tail {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) (j : ℕ) :
    slabLaw μ v {γ | j < slabRecords v γ} = conditioned μ v (noCutBeforeRecord v j) := by
  rw [slabLaw, Measure.map_apply (measurable_firstWord v)
    (measurableSet_lt measurable_const (measurable_of_countable (slabRecords v)))]
  apply measure_congr
  filter_upwards [ae_conditioned_firstWord μ hell v hv hp] with X hX
  apply propext
  change (j < slabRecords v (firstWord v X)) ↔ X ∈ noCutBeforeRecord v j
  rw [slabRecords_firstWord]
  have hc : ∃ n, trueCut v X n := by
    by_contra hh
    have hz := (firstCutTime_eq_zero_iff v X).mpr hh
    have hpos : 0 < firstCutTime v X := hX.1
    omega
  exact (noCutBeforeRecord_iff v X hc j).symm

lemma lintegral_slabRecords_le {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) :
    (∫⁻ γ, (slabRecords v γ : ℝ≥0∞) ∂slabLaw μ v) ≤
      (annealed μ 0 (nonBacktracking v))⁻¹ := by
  rw [lintegral_nat_tail _ _ (measurable_of_countable _)]
  simp_rw [slabRecords_tail μ hell v hv hp]
  apply ENNReal.tsum_le_of_sum_range_le
  intro n
  cases n with
  | zero => simp
  | succ N =>
    have h := record_tail_sum_bound μ hell v hv hp N
    have hreflect := Finset.sum_range_reflect
      (fun j => conditioned μ v (noCutBeforeRecord v j)) (N+1)
    simp only [Nat.add_sub_cancel] at hreflect
    rw [hreflect] at h
    have hb := (ENNReal.mul_le_iff_le_inv hp.ne' (measure_ne_top _ _)).mp h
    simpa only [mul_one] using hb

lemma integrable_slabRecords {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) :
    Integrable (fun γ => (slabRecords v γ : ℝ)) (slabLaw μ v) := by
  refine ⟨(measurable_of_countable _).aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall
    (fun γ => Nat.cast_nonneg (slabRecords v γ)))).mpr
  simp_rw [ENNReal.ofReal_natCast]
  exact (lintegral_slabRecords_le μ hell v hv hp).trans_lt
    (ENNReal.inv_lt_top.mpr hp)

lemma height_stepVector_le_one {d : ℕ} (v : Fin d → ℝ)
    (hv : ∀ i, |v i| ≤ 1) (e : Step d) : height v (stepVector e) ≤ 1 := by
  rw [height_stepVector]
  have hi := abs_le.mp (hv e.1)
  split <;> linarith [hi.1,hi.2]

lemma height_le_recordCount {d : ℕ} (v : Fin d → ℝ) (X : Path d) (n : ℕ)
    (h0 : height v (X 0) = 0)
    (hs : ∀ i < n, height v (X (i+1)) ≤ height v (X i) + 1) :
    ∀ i ≤ n, height v (X i) ≤ (recordCount v X n : ℝ) := by
  classical
  induction n with
  | zero =>
    intro i hi
    have hi0 : i = 0 := by omega
    simp [hi0,h0,recordCount_zero]
  | succ n ih =>
    have ih' := ih (fun i hi => hs i (by omega))
    intro i hi
    by_cases hin : i ≤ n
    · exact (ih' i hin).trans (Nat.cast_le.mpr (recordCount_mono v X (by omega)))
    · have hin : i = n+1 := by omega
      subst i
      by_cases hr : strictRecord v X (n+1)
      · rw [recordCount_succ,ite_eq_left hr,Nat.cast_add,Nat.cast_one]
        linarith [hs n (by omega),ih' n le_rfl]
      · have hex : ∃ j < n+1, height v (X (n+1)) ≤ height v (X j) := by
          have hn : ¬∀ j < n+1, height v (X j) < height v (X (n+1)) :=
            fun hh => hr ⟨by omega,hh⟩
          push Not at hn
          exact hn
        obtain ⟨j,hj,hbound⟩ := hex
        exact hbound.trans ((ih' j (by omega)).trans
          (Nat.cast_le.mpr (recordCount_mono v X (by omega))))

lemma slabWidth_bounds {d : ℕ} (v : Fin d → ℝ) (hv : ∀ i, |v i| ≤ 1)
    (γ : Word d) (hγ : RegenerationWord v γ) :
    0 < slabWidth v γ ∧ slabWidth v γ ≤ (slabRecords v γ : ℝ) := by
  have hz : height v (wordPath γ 0) = 0 := by rw [hγ.2.1,height_zero]
  refine ⟨?_,height_le_recordCount v (wordPath γ) γ.1 hz ?_ γ.1 le_rfl⟩
  · have h := (hγ.2.2.2.1 0 hγ.1).2
    rwa [hz] at h
  · intro i hi
    obtain ⟨e,he⟩ := hγ.2.2.1 i hi
    rw [he,height_add]
    linarith [height_stepVector_le_one v hv e]

lemma integrable_slabWidth {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hvnorm : ∀ i, |v i| ≤ 1) (hp : 0 < annealed μ 0 (nonBacktracking v)) :
    Integrable (slabWidth v) (slabLaw μ v) := by
  apply (integrable_slabRecords μ hell v hv hp).mono'
    (measurable_of_countable _).aestronglyMeasurable
  filter_upwards [ae_slabLaw_regeneration μ hell v hv hp] with γ hγ
  have hb := slabWidth_bounds v hvnorm γ hγ
  simpa only [Real.norm_eq_abs,abs_of_pos hb.1] using hb.2

lemma lintegral_slabWidth_le {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hvnorm : ∀ i, |v i| ≤ 1) (hp : 0 < annealed μ 0 (nonBacktracking v)) :
    (∫⁻ γ, ENNReal.ofReal (slabWidth v γ) ∂slabLaw μ v) ≤
      (annealed μ 0 (nonBacktracking v))⁻¹ := by
  apply le_trans (lintegral_mono_ae ?_) (lintegral_slabRecords_le μ hell v hv hp)
  filter_upwards [ae_slabLaw_regeneration μ hell v hv hp] with γ hγ
  simpa only [ENNReal.ofReal_natCast] using
    ENNReal.ofReal_le_ofReal (slabWidth_bounds v hvnorm γ hγ).2

lemma integral_slabWidth_pos {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hvnorm : ∀ i, |v i| ≤ 1) (hp : 0 < annealed μ 0 (nonBacktracking v)) :
    0 < ∫ γ, slabWidth v γ ∂slabLaw μ v := by
  let := slabLaw_probability μ v hp
  have hpos : ∀ᵐ γ ∂slabLaw μ v, 0 < slabWidth v γ :=
    (ae_slabLaw_regeneration μ hell v hv hp).mono (fun γ hγ =>
      (slabWidth_bounds v hvnorm γ hγ).1)
  apply (integral_pos_iff_support_of_nonneg_ae (hpos.mono (fun _ h => h.le))
    (integrable_slabWidth μ hell v hv hvnorm hp)).mpr
  have hfull : slabLaw μ v (Function.support (slabWidth v)) = 1 := by
    apply (mem_ae_iff_prob_eq_one (measurableSet_support (measurable_of_countable _))).mp
    exact hpos.mono (fun _ h => h.ne')
  rw [hfull]
  exact zero_lt_one

lemma nonneg_sum_range_mono (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j) {m n : ℕ}
    (h : m ≤ n) : ∑ j ∈ Finset.range m, f j ≤ ∑ j ∈ Finset.range n, f j := by
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) (fun j _ _ => hf j)

lemma greedy_interval_bound (f b : ℕ → ℝ) (n : ℕ) (a : ℝ) (ha : 0 ≤ a)
    (hf : ∀ j, 0 ≤ f j) (hb : ∀ j, b j ≤ 1)
    (hw : ∀ s, b s ≠ 0 → ∃ k : ℕ, 0 < k ∧ k ≤ n ∧
      a * (k : ℝ) ≤ ∑ j ∈ Finset.range k, f (s+j)) (M : ℕ) :
    a * ∑ s ∈ Finset.range M, b s ≤ ∑ j ∈ Finset.range (M+n), f j := by
  induction M using Nat.strong_induction_on generalizing f b with
  | h M ih =>
    by_cases hM : M = 0
    · subst M
      simpa using Finset.sum_nonneg (fun j _ => hf j)
    by_cases hb0 : b 0 = 0
    · obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hM
      have hh := ih m (by omega) (fun j => f (j+1)) (fun j => b (j+1))
        (fun j => hf (j+1)) (fun j => hb (j+1)) (by
          intro s hs
          obtain ⟨k,hk,hkn,hkw⟩ := hw (s+1) hs
          refine ⟨k,hk,hkn,?_⟩
          simpa only [Nat.add_right_comm] using hkw)
      rw [Finset.sum_range_succ',hb0,add_zero]
      have hsum : ∑ j ∈ Finset.range (m+1+n), f j =
          (∑ j ∈ Finset.range (m+n), f (j+1)) + f 0 := by
        rw [show m+1+n = m+n+1 by omega,Finset.sum_range_succ']
      rw [hsum]
      linarith [hf 0]
    · obtain ⟨k,hk,hkn,hkw⟩ := hw 0 hb0
      simp only [Nat.zero_add] at hkw
      have hbfirst (r : ℕ) : ∑ j ∈ Finset.range r, b j ≤ (r : ℝ) := by
        have hh := Finset.sum_le_sum (s := Finset.range r) (fun j _ => hb j)
        simpa using hh
      by_cases hMk : M ≤ k
      · calc
          _ ≤ a * (M : ℝ) := mul_le_mul_of_nonneg_left (hbfirst M) ha
          _ ≤ a * (k : ℝ) := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hMk) ha
          _ ≤ ∑ j ∈ Finset.range k, f j := hkw
          _ ≤ _ := nonneg_sum_range_mono f hf (by omega)
      · have hkm : k < M := by omega
        have hh := ih (M-k) (by omega) (fun j => f (k+j)) (fun j => b (k+j))
          (fun j => hf (k+j)) (fun j => hb (k+j)) (by
            intro s hs
            obtain ⟨r,hr,hrn,hrw⟩ := hw (k+s) hs
            exact ⟨r,hr,hrn,by simpa only [Nat.add_assoc] using hrw⟩)
        have hsplit : ∑ j ∈ Finset.range M, b j =
            (∑ j ∈ Finset.range k, b j) + ∑ j ∈ Finset.range (M-k), b (k+j) := by
          rw [← Finset.sum_range_add, Nat.add_sub_of_le hkm.le]
        have hsplitf : ∑ j ∈ Finset.range (M+n), f j =
            (∑ j ∈ Finset.range k, f j) + ∑ j ∈ Finset.range (M-k+n), f (k+j) := by
          rw [← Finset.sum_range_add]
          exact congrArg (fun r => ∑ j ∈ Finset.range r, f j) (by omega)
        rw [hsplit,hsplitf,mul_add]
        exact add_le_add ((mul_le_mul_of_nonneg_left (hbfirst k) ha).trans hkw) hh

def initialAverageBad {Ω : Type*} (T : Ω → Ω) (f : Ω → ℝ) (a : ℝ) (n : ℕ) : Set Ω :=
  {x | ∃ k : ℕ, 0 < k ∧ k ≤ n ∧ a * (k : ℝ) < ∑ j ∈ Finset.range k, f (T^[j] x)}

lemma measurableSet_initialAverageBad {Ω : Type*} [MeasurableSpace Ω]
    (T : Ω → Ω) (hT : Measurable T) (f : Ω → ℝ) (hf : Measurable f)
    (a : ℝ) (n : ℕ) : MeasurableSet (initialAverageBad T f a n) := by
  unfold initialAverageBad
  simp only [Set.ofPred_exists, Set.ofPred_and]
  apply MeasurableSet.iUnion
  intro k
  exact (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
    (measurableSet_lt measurable_const (Finset.measurable_sum _ (fun j _ => hf.comp (hT.iterate j)))))

lemma integral_comp_preserving {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (T : Ω → Ω) (hT : MeasurePreserving T P P) (f : Ω → ℝ)
    (hf : AEStronglyMeasurable f P) : (∫ x, f (T x) ∂P) = ∫ x, f x ∂P := by
  have hh := integral_map hT.measurable.aemeasurable (hT.map_eq.symm ▸ hf)
  rw [hT.map_eq] at hh
  exact hh.symm

lemma stationary_initial_average_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : Ω → Ω)
    (hT : MeasurePreserving T P P) (f : Ω → ℝ) (hfm : Measurable f)
    (hfi : Integrable f P) (hf : ∀ x, 0 ≤ f x) (a : ℝ) (ha : 0 < a) (n : ℕ) :
    P.real (initialAverageBad T f a n) ≤ (∫ x, f x ∂P) / a := by
  classical
  let B := initialAverageBad T f a n
  have hB : MeasurableSet B := measurableSet_initialAverageBad T hT.measurable f hfm a n
  let b : Ω → ℝ := B.indicator (fun _ => 1)
  have hbi : Integrable b P := (integrable_const (1 : ℝ)).indicator hB
  have hbe : (∫ x, b x ∂P) = P.real B := integral_indicator_one hB
  have hshiftf (j : ℕ) : Integrable (fun x => f (T^[j] x)) P :=
    (hT.iterate j).integrable_comp_of_integrable hfi
  have hshiftb (j : ℕ) : Integrable (fun x => b (T^[j] x)) P :=
    (hT.iterate j).integrable_comp_of_integrable hbi
  have hM (M : ℕ) : a * ((M : ℝ) * P.real B) ≤ ((M+n : ℕ) : ℝ) * (∫ x, f x ∂P) := by
    have hpoint (x : Ω) :
        a * ∑ s ∈ Finset.range M, b (T^[s] x) ≤
          ∑ j ∈ Finset.range (M+n), f (T^[j] x) := by
      apply greedy_interval_bound (fun j => f (T^[j] x)) (fun j => b (T^[j] x)) n a ha.le
        (fun j => hf _) (fun j => ?_) (fun s hs => ?_) M
      · simp only [b, Set.indicator_apply]
        split_ifs <;> norm_num
      · have hx : T^[s] x ∈ B := by
          by_contra hnot
          exact hs (Set.indicator_of_notMem hnot _)
        obtain ⟨k,hk,hkn,hkw⟩ := hx
        refine ⟨k,hk,hkn,hkw.le.trans_eq ?_⟩
        apply Finset.sum_congr rfl
        intro j hj
        rw [← Function.iterate_add_apply, Nat.add_comm j s]
    have hle := integral_mono
      ((integrable_finsetSum _ (fun j _ => hshiftb j)).const_mul a)
      (integrable_finsetSum _ (fun j _ => hshiftf j)) hpoint
    rw [integral_const_mul,integral_finsetSum _ (fun j _ => hshiftb j),
      integral_finsetSum _ (fun j _ => hshiftf j)] at hle
    simp_rw [integral_comp_preserving P _ (hT.iterate _) b hbi.aestronglyMeasurable,
      integral_comp_preserving P _ (hT.iterate _) f hfi.aestronglyMeasurable,hbe] at hle
    simpa using hle
  apply (le_div_iff₀ ha).mpr
  by_contra hnot
  have hpos : 0 < a * P.real B - (∫ x, f x ∂P) := by linarith
  obtain ⟨M,hMbig⟩ := exists_nat_gt (((n : ℝ) * (∫ x, f x ∂P)) /
    (a * P.real B - (∫ x, f x ∂P)))
  have hh := (div_lt_iff₀ hpos).mp hMbig
  have hh' := hM M
  push_cast at hh'
  nlinarith

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

def euclideanSite {d : ℕ} (x : Site d) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => (x i : ℝ))

lemma euclideanSite_add {d : ℕ} (x y : Site d) :
    euclideanSite (x+y) = euclideanSite x + euclideanSite y := by
  ext i
  simp [euclideanSite]

lemma euclideanSite_zero {d : ℕ} : euclideanSite (0 : Site d) = 0 := by
  ext i
  simp [euclideanSite]

lemma euclideanSite_sub {d : ℕ} (x y : Site d) :
    euclideanSite (x-y) = euclideanSite x - euclideanSite y := by
  ext i
  simp [euclideanSite]

noncomputable def slabRadius {d : ℕ} (γ : Word d) : ℝ :=
  (Finset.range (γ.1+1)).sup' ⟨0,Finset.mem_range.mpr (Nat.succ_pos _)⟩
    (fun j => ‖euclideanSite (wordPath γ j - wordPath γ 0)‖)

lemma norm_wordPath_le_radius {d : ℕ} (γ : Word d) {j : ℕ} (hj : j ≤ γ.1) :
    ‖euclideanSite (wordPath γ j - wordPath γ 0)‖ ≤ slabRadius γ :=
  Finset.le_sup' (fun k => ‖euclideanSite (wordPath γ k - wordPath γ 0)‖)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

lemma slabRadius_nonneg {d : ℕ} (γ : Word d) : 0 ≤ slabRadius γ := by
  exact (norm_nonneg _).trans (norm_wordPath_le_radius γ (j := 0) (Nat.zero_le _))

lemma slabs_identDistrib {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) (k : ℕ) :
    IdentDistrib (fun X => slabs v X k) id (conditioned μ v) (slabLaw μ v) := by
  refine ⟨((measurable_pi_apply k).comp (measurable_slabs v)).aemeasurable,
    measurable_id.aemeasurable,?_⟩
  rw [Measure.map_id]
  exact slabs_marginal μ hell v hv hp k

lemma slabObservable_strongLaw {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) (f : Word d → ℝ)
    (hf : Integrable f (slabLaw μ v)) :
    ∀ᵐ X ∂conditioned μ v,
      Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, f (slabs v X i)) / n)
        atTop (𝓝 (∫ γ, f γ ∂slabLaw μ v)) := by
  have hind := (slabs_iid μ hell v hv hp).comp (fun _ => f)
    (fun _ => measurable_of_countable _)
  have hid (k : ℕ) := (slabs_identDistrib μ hell v hv hp k).comp
    (measurable_of_countable f)
  have hfi : Integrable (fun X => f (slabs v X 0)) (conditioned μ v) :=
    (hid 0).integrable_iff.mpr hf
  have heq : (∫ X, f (slabs v X 0) ∂conditioned μ v) = ∫ γ, f γ ∂slabLaw μ v :=
    (hid 0).integral_eq
  simpa only [Function.comp_apply, id_eq,heq] using strong_law_ae_real
    (fun k X => f (slabs v X k)) hfi (fun i j hij => hind.indepFun hij)
    (fun k => (hid k).trans (hid 0).symm)

lemma slabWidth_strongLaw {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hvnorm : ∀ i, |v i| ≤ 1) (hp : 0 < annealed μ 0 (nonBacktracking v)) :
    ∀ᵐ X ∂conditioned μ v,
      Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, slabWidth v (slabs v X i)) / n)
        atTop (𝓝 (∫ γ, slabWidth v γ ∂slabLaw μ v)) :=
  slabObservable_strongLaw μ hell v hv hp _ (integrable_slabWidth μ hell v hv hvnorm hp)

lemma slab_initial_average_bound {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) (f : Word d → ℝ)
    (hf : Integrable f (slabLaw μ v)) (hf0 : ∀ γ, 0 ≤ f γ)
    (a : ℝ) (ha : 0 < a) (n : ℕ) :
    (conditioned μ v).real {X | ∃ k : ℕ, 0 < k ∧ k ≤ n ∧
      a * (k : ℝ) < ∑ j ∈ Finset.range k, f (slabs v X j)} ≤
      (∫ γ, f γ ∂slabLaw μ v) / a := by
  let := conditioned_probability μ v hp
  have hid := (slabs_identDistrib μ hell v hv hp 0).comp (measurable_of_countable f)
  have hfi : Integrable (fun X => f (firstWord v X)) (conditioned μ v) :=
    hid.integrable_iff.mpr hf
  have hfe : (∫ X, f (firstWord v X) ∂conditioned μ v) = ∫ γ, f γ ∂slabLaw μ v :=
    hid.integral_eq
  have hh := stationary_initial_average_bound (conditioned μ v) (cutSuffix v)
    (cutSuffix_measurePreserving μ hell v hv hp) (fun X => f (firstWord v X))
    ((measurable_of_countable f).comp (measurable_firstWord v)) hfi (fun X => hf0 _) a ha n
  simpa only [initialAverageBad,slabs,hfe] using hh

noncomputable def slabTime {d : ℕ} (v : Fin d → ℝ) (X : Path d) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, (slabs v X i).1

lemma slabTime_zero {d : ℕ} (v : Fin d → ℝ) (X : Path d) : slabTime v X 0 = 0 := by
  simp [slabTime]

lemma slabTime_succ {d : ℕ} (v : Fin d → ℝ) (X : Path d) (k : ℕ) :
    slabTime v X (k+1) = slabTime v X k + (slabs v X k).1 := by
  exact Finset.sum_range_succ _ _

lemma iterated_cutSuffix {d : ℕ} (v : Fin d → ℝ) (X : Path d) (h0 : X 0 = 0)
    (k n : ℕ) : (cutSuffix v)^[k] X n = X (slabTime v X k + n) - X (slabTime v X k) := by
  induction k generalizing n with
  | zero => simp [slabTime_zero,h0]
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    change ((cutSuffix v)^[k] X) (firstCutTime v ((cutSuffix v)^[k] X) + n) +
      -((cutSuffix v)^[k] X (firstCutTime v ((cutSuffix v)^[k] X))) = _
    rw [ih,ih,slabTime_succ]
    change X (slabTime v X k + ((slabs v X k).1+n)) - X (slabTime v X k) +
      -(X (slabTime v X k + (slabs v X k).1) - X (slabTime v X k)) = _
    rw [← Nat.add_assoc]
    abel

lemma slab_word_path {d : ℕ} (v : Fin d → ℝ) (X : Path d) (k : ℕ)
    {j : ℕ} (hj : j ≤ (slabs v X k).1) :
    wordPath (slabs v X k) j = (cutSuffix v)^[k] X j :=
  wordPath_prefixWord _ _ hj

def GoodSlabPath {d : ℕ} (v : Fin d → ℝ) (X : Path d) : Prop :=
  X 0 = 0 ∧ ∀ k, RegenerationWord v (slabs v X k)

lemma ae_goodSlabPath {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) :
    ∀ᵐ X ∂conditioned μ v, GoodSlabPath v X := by
  have h0 := (cond_absolutelyContinuous (s := nonBacktracking v) (μ := annealed μ 0)).ae_le
    (ae_start_and_nearestNeighbour μ 0)
  have hs : ∀ᵐ X ∂conditioned μ v, ∀ k, RegenerationWord v (slabs v X k) := by
    rw [ae_all_iff]
    intro k
    exact ((cutSuffix_measurePreserving μ hell v hv hp).iterate k).quasiMeasurePreserving.ae
      (ae_conditioned_firstWord μ hell v hv hp)
  filter_upwards [h0,hs] with X hX hW
  exact ⟨hX.1,hW⟩

lemma slabTime_strictMono {d : ℕ} (v : Fin d → ℝ) (X : Path d) (hX : GoodSlabPath v X) :
    StrictMono (slabTime v X) := by
  apply strictMono_nat_of_lt_succ
  intro k
  rw [slabTime_succ]
  exact Nat.lt_add_of_pos_right (hX.2 k).1

lemma slab_location {d : ℕ} (v : Fin d → ℝ) (X : Path d) (hX : GoodSlabPath v X)
    (n : ℕ) : ∃ k, slabTime v X k ≤ n ∧ n < slabTime v X (k+1) := by
  have hex : ∃ k, n < slabTime v X (k+1) :=
    ⟨n,(Nat.lt_succ_self n).trans_le ((slabTime_strictMono v X hX).id_le (n+1))⟩
  refine ⟨Nat.find hex,?_,Nat.find_spec hex⟩
  by_cases hz : Nat.find hex = 0
  · rw [hz,slabTime_zero]
    exact Nat.zero_le _
  · obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero hz
    have hh := Nat.find_min hex (show j < Nat.find hex by omega)
    rw [hj]
    exact not_lt.mp hh

noncomputable def slabHeightSum {d : ℕ} (v : Fin d → ℝ) (X : Path d) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, slabWidth v (slabs v X i)

noncomputable def slabRadiusSum {d : ℕ} (v : Fin d → ℝ) (X : Path d) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, slabRadius (slabs v X i)

lemma height_at_slabTime {d : ℕ} (v : Fin d → ℝ) (X : Path d) (h0 : X 0 = 0)
    (k : ℕ) : height v (X (slabTime v X k)) = slabHeightSum v X k := by
  induction k with
  | zero => simp [slabTime_zero,slabHeightSum,h0,height_zero]
  | succ k ih =>
    have hh := iterated_cutSuffix v X h0 k (slabs v X k).1
    rw [← slab_word_path v X k le_rfl,← slabTime_succ] at hh
    have hh' := congrArg (height v) hh
    rw [height_sub,ih] at hh'
    change slabWidth v (slabs v X k) = height v (X (slabTime v X (k+1))) - _ at hh'
    rw [slabHeightSum,Finset.sum_range_succ]
    change height v (X (slabTime v X (k+1))) = slabHeightSum v X k + _
    linarith

lemma norm_at_slabTime_le {d : ℕ} (v : Fin d → ℝ) (X : Path d) (hX : GoodSlabPath v X)
    (k : ℕ) : ‖euclideanSite (X (slabTime v X k))‖ ≤ slabRadiusSum v X k := by
  induction k with
  | zero => simp [slabTime_zero,slabRadiusSum,hX.1,euclideanSite_zero]
  | succ k ih =>
    have hh := iterated_cutSuffix v X hX.1 k (slabs v X k).1
    rw [← slab_word_path v X k le_rfl,← slabTime_succ] at hh
    have heq : X (slabTime v X (k+1)) = X (slabTime v X k) + wordPath (slabs v X k) (slabs v X k).1 := by
      rw [hh]
      abel
    rw [heq,euclideanSite_add]
    have hb := norm_wordPath_le_radius (slabs v X k) (j := (slabs v X k).1) le_rfl
    rw [(hX.2 k).2.1,sub_zero] at hb
    rw [slabRadiusSum,Finset.sum_range_succ]
    exact (norm_add_le _ _).trans (add_le_add ih hb)

lemma norm_in_slab_le {d : ℕ} (v : Fin d → ℝ) (X : Path d) (hX : GoodSlabPath v X)
    (k j : ℕ) (hj : j ≤ (slabs v X k).1) :
    ‖euclideanSite (X (slabTime v X k + j))‖ ≤ slabRadiusSum v X (k+1) := by
  have hh := iterated_cutSuffix v X hX.1 k j
  rw [← slab_word_path v X k hj] at hh
  have heq : X (slabTime v X k+j) = X (slabTime v X k) + wordPath (slabs v X k) j := by
    rw [hh]
    abel
  rw [heq,euclideanSite_add]
  have hb := norm_wordPath_le_radius (slabs v X k) hj
  rw [(hX.2 k).2.1,sub_zero] at hb
  rw [slabRadiusSum,Finset.sum_range_succ]
  exact (norm_add_le _ _).trans (add_le_add (norm_at_slabTime_le v X hX k) hb)

lemma height_in_slab {d : ℕ} (v : Fin d → ℝ) (X : Path d) (hX : GoodSlabPath v X)
    (k j : ℕ) (hj : j < (slabs v X k).1) :
    slabHeightSum v X k ≤ height v (X (slabTime v X k+j)) ∧
    height v (X (slabTime v X k+j)) < slabHeightSum v X (k+1) := by
  have hh := congrArg (height v) (iterated_cutSuffix v X hX.1 k j)
  rw [← slab_word_path v X k hj.le,height_sub,height_at_slabTime v X hX.1] at hh
  have hb := (hX.2 k).2.2.2.1 j hj
  have heq : slabHeightSum v X (k+1) = slabHeightSum v X k + slabWidth v (slabs v X k) :=
    Finset.sum_range_succ _ _
  rw [heq]
  change 0 ≤ height v (wordPath (slabs v X k) j) ∧
    height v (wordPath (slabs v X k) j) < slabWidth v (slabs v X k) at hb
  constructor <;> linarith [hb.1,hb.2]

noncomputable def truncatedMoment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ℝ) (t : ℝ) : ℝ := ∫ x, min (f x) t ∂P

lemma integrable_min_const {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → ℝ) (hfm : Measurable f)
    (hf : ∀ x, 0 ≤ f x) (t : ℝ) (ht : 0 ≤ t) : Integrable (fun x => min (f x) t) P := by
  apply (integrable_const t).mono' (hfm.min measurable_const).aestronglyMeasurable
  exact Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hf x) ht)]
    exact min_le_right _ _)

lemma truncatedMoment_nonneg {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ℝ) (hf : ∀ x, 0 ≤ f x) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ truncatedMoment P f t := integral_nonneg (fun x => le_min (hf x) ht)

lemma truncatedMoment_mono {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → ℝ) (hfm : Measurable f)
    (hf : ∀ x, 0 ≤ f x) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    truncatedMoment P f s ≤ truncatedMoment P f t :=
  integral_mono (integrable_min_const P f hfm hf s hs)
    (integrable_min_const P f hfm hf t (hs.trans hst)) (fun _ => min_le_min_left _ hst)

lemma min_mul_le_mul_min {r t C : ℝ} (hr : 0 ≤ r) (hC : 1 ≤ C) :
    min r (C*t) ≤ C * min r t := by
  by_cases hrt : r ≤ t
  · rw [min_eq_left hrt]
    exact (min_le_left _ _).trans (by nlinarith)
  · rw [min_eq_right (le_of_not_ge hrt)]
    exact min_le_right _ _

lemma truncatedMoment_mul_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → ℝ) (hfm : Measurable f)
    (hf : ∀ x, 0 ≤ f x) {t C : ℝ} (ht : 0 ≤ t) (hC : 1 ≤ C) :
    truncatedMoment P f (C*t) ≤ C * truncatedMoment P f t := by
  unfold truncatedMoment
  rw [← integral_const_mul]
  exact integral_mono (integrable_min_const P f hfm hf _ (mul_nonneg (by linarith) ht))
    ((integrable_min_const P f hfm hf t ht).const_mul C)
    (fun x => min_mul_le_mul_min (hf x) hC)

lemma truncatedMoment_sublinear {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → ℝ) (hfm : Measurable f)
    (hf : ∀ x, 0 ≤ f x) :
    Tendsto (fun t : ℝ => truncatedMoment P f t / t) atTop (𝓝 0) := by
  have hlim := tendsto_integral_filter_of_dominated_convergence (μ := P)
    (F := fun t : ℝ => fun x => min (f x) t / t) (f := fun _ => (0 : ℝ))
    (fun _ => (1 : ℝ))
    (Eventually.of_forall (fun t => ((hfm.min measurable_const).div_const t).aestronglyMeasurable))
    (show ∀ᶠ t : ℝ in atTop, ∀ᵐ x ∂P, ‖min (f x) t / t‖ ≤ (1 : ℝ) from by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      exact Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (le_min (hf x) ht.le) ht.le)]
        exact (div_le_one ht).mpr (min_le_right _ _)))
    (integrable_const (1 : ℝ))
    (Eventually.of_forall (fun x => by
      apply Tendsto.congr' (f₁ := fun t : ℝ => f x / t) ?_
        (tendsto_const_nhds.div_atTop tendsto_id)
      filter_upwards [eventually_ge_atTop (f x)] with t ht
      rw [min_eq_left ht]))
  simpa only [integral_div,integral_zero,truncatedMoment] using hlim

lemma integrable_of_truncatedMoment_bounded {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → ℝ) (hfm : Measurable f)
    (hf : ∀ x, 0 ≤ f x) (B : ℝ)
    (hb : ∀ n : ℕ, truncatedMoment P f n ≤ B) : Integrable f P := by
  have hlim : Tendsto (fun n : ℕ => ∫⁻ x, ENNReal.ofReal (min (f x) (n : ℝ)) ∂P)
      atTop (𝓝 (∫⁻ x, ENNReal.ofReal (f x) ∂P)) := by
    apply lintegral_tendsto_of_tendsto_of_monotone
    · intro n
      exact (hfm.min measurable_const).ennreal_ofReal.aemeasurable
    · exact Eventually.of_forall (fun x n m hnm =>
        ENNReal.ofReal_le_ofReal (min_le_min_left _ (Nat.cast_le.mpr hnm)))
    · exact Eventually.of_forall (fun x => by
        apply tendsto_const_nhds.congr'
        filter_upwards [(tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
          (eventually_ge_atTop (f x))] with n hn
        rw [min_eq_left hn])
  have hbound : (∫⁻ x, ENNReal.ofReal (f x) ∂P) ≤ ENNReal.ofReal B := by
    apply le_of_tendsto hlim
    exact Eventually.of_forall (fun n => by
      rw [← ofReal_integral_eq_lintegral_ofReal
        (integrable_min_const P f hfm hf (n : ℝ) (Nat.cast_nonneg _))
        (Eventually.of_forall (fun x => le_min (hf x) (Nat.cast_nonneg _)))]
      exact ENNReal.ofReal_le_ofReal (hb n))
  refine ⟨hfm.aestronglyMeasurable, ?_⟩
  exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hf)).mpr
    (hbound.trans_lt ENNReal.ofReal_lt_top)

lemma exists_truncatedMoment_gt {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → ℝ) (hfm : Measurable f)
    (hf : ∀ x, 0 ≤ f x) (hnot : ¬Integrable f P) (B : ℝ) :
    ∃ n : ℕ, B < truncatedMoment P f n := by
  by_contra h
  push Not at h
  exact hnot (integrable_of_truncatedMoment_bounded P f hfm hf B h)

lemma truncatedMoment_scaled_sublinear {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → ℝ) (hfm : Measurable f)
    (hf : ∀ x, 0 ≤ f x) {C : ℝ} (hC : 0 < C) :
    Tendsto (fun a : ℝ => truncatedMoment P f (C*a) / a) atTop (𝓝 0) := by
  have ht : Tendsto (fun a : ℝ => C*a) atTop atTop := tendsto_id.const_mul_atTop hC
  have hh := ((truncatedMoment_sublinear P f hfm hf).comp ht).const_mul C
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  dsimp
  field_simp

lemma exists_truncation_multiple {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → ℝ) (hfm : Measurable f)
    (hf : ∀ x, 0 ≤ f x) (hnot : ¬Integrable f P) {a b : ℝ} (ha : 0 < a) :
    ∃ n : ℕ, 0 < n ∧ b ≤ truncatedMoment P f (a*n) := by
  obtain ⟨j,hj⟩ := exists_truncatedMoment_gt P f hfm hf hnot b
  obtain ⟨n,hn⟩ := exists_nat_gt ((j : ℝ)/a)
  refine ⟨n+1,Nat.succ_pos _,hj.le.trans ?_⟩
  apply truncatedMoment_mono P f hfm hf (Nat.cast_nonneg _)
  have hh : (j : ℝ) < (n : ℝ)*a := (div_lt_iff₀ ha).mp hn
  push_cast
  nlinarith

lemma radius_scales {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → ℝ) (hfm : Measurable f)
    (hf : ∀ x, 0 ≤ f x) (hnot : ¬Integrable f P) {η : ℝ} (hη : 0 < η)
    (M : ℕ) {D : ℝ} (hD : 0 < D) :
    ∀ᶠ a : ℝ in atTop, 0 < a ∧ ∃ N : ℕ, max 2 M ≤ N ∧
      η*a ≤ truncatedMoment P f (a*N) ∧ truncatedMoment P f (a*N) < 2*η*a ∧
      truncatedMoment P f (D*a) < η*a/4 ∧
      ∀ m : ℕ, 0 < m → m < N → truncatedMoment P f (a*m) < η*a := by
  let K := max 2 M
  have hK : (0 : ℝ) < K := by dsimp [K]; exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) (le_max_left 2 M))
  have hs := (truncatedMoment_scaled_sublinear P f hfm hf hK).eventually
    (gt_mem_nhds hη)
  have hsmall := (truncatedMoment_scaled_sublinear P f hfm hf hD).eventually
    (gt_mem_nhds (show (0 : ℝ) < η/4 by positivity))
  filter_upwards [eventually_gt_atTop (0 : ℝ),hs,hsmall] with a ha hs hsmall
  obtain hex := exists_truncation_multiple P f hfm hf hnot (b := η*a) ha
  let N := Nat.find hex
  have hN := Nat.find_spec hex
  have hmin : ∀ m : ℕ, 0 < m → m < N → truncatedMoment P f (a*m) < η*a := by
    intro m hm hmN
    have hh := Nat.find_min hex hmN
    exact lt_of_not_ge (fun h => hh ⟨hm,h⟩)
  have hKN : K < N := by
    by_contra hh
    have hNK : N ≤ K := le_of_not_gt hh
    have hhN := truncatedMoment_mono P f hfm hf (mul_nonneg ha.le (Nat.cast_nonneg N))
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hNK) ha.le)
    have hhK : truncatedMoment P f (a*K) < η*a := by
      rw [mul_comm a]
      exact (div_lt_iff₀ ha).mp hs
    exact (not_lt_of_ge hN.2) (hhN.trans_lt hhK)
  have hN2 : 2 ≤ N := (le_max_left 2 M).trans hKN.le
  have hNm : 0 < N-1 := by omega
  have hm := hmin (N-1) hNm (by omega)
  have hstep : truncatedMoment P f (a*N) ≤ 2*truncatedMoment P f (a*((N-1 : ℕ) : ℝ)) := by
    apply (truncatedMoment_mono P f hfm hf (mul_nonneg ha.le (Nat.cast_nonneg N)) ?_).trans
      (truncatedMoment_mul_le P f hfm hf (mul_nonneg ha.le (by positivity)) (by norm_num : (1 : ℝ) ≤ 2))
    have hNN : (N : ℝ) ≤ 2*((N-1 : ℕ) : ℝ) := by exact_mod_cast (show N ≤ 2*(N-1) by omega)
    nlinarith
  refine ⟨ha,N,hKN.le,hN.2,?_,?_,hmin⟩
  · nlinarith
  · exact (div_lt_iff₀ ha).mp hsmall |>.trans_le (by ring_nf; exact le_rfl)

lemma stationary_truncated_average_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : Ω → Ω)
    (hT : MeasurePreserving T P P) (f : Ω → ℝ) (hfm : Measurable f)
    (hf : ∀ x, 0 ≤ f x) (a : ℝ) (ha : 0 < a) (n : ℕ) (hn : 0 < n) :
    P.real (initialAverageBad T f a n) ≤ 2*truncatedMoment P f (a*n)/a := by
  classical
  let A : ℝ := a*n
  have hA : 0 < A := mul_pos ha (Nat.cast_pos.mpr hn)
  let g : Ω → ℝ := fun x => min (f x) A
  have hgm : Measurable g := hfm.min measurable_const
  have hgi : Integrable g P := integrable_min_const P f hfm hf A hA.le
  have hg0 : ∀ x, 0 ≤ g x := fun x => le_min (hf x) hA.le
  have htail : P.real {x | A < f x} ≤ truncatedMoment P f A / A := by
    have hb := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall hg0) hgi A
    have hm : P.real {x | A < f x} ≤ P.real {x | A ≤ g x} := by
      refine measureReal_mono ?_ (measure_ne_top _ _)
      intro x hx
      change A < f x at hx
      exact le_min hx.le le_rfl
    apply (le_div_iff₀ hA).mpr
    calc
      P.real {x | A < f x} * A ≤ A * P.real {x | A ≤ g x} := by nlinarith
      _ ≤ _ := hb
  let B : Set Ω := ⋃ j ∈ Finset.range n, {x | A < f (T^[j] x)}
  have hB : P.real B ≤ (n : ℝ)*truncatedMoment P f A/A := by
    apply (measureReal_biUnion_finset_le (Finset.range n) _).trans
    have heq (j : ℕ) : P.real {x | A < f (T^[j] x)} = P.real {x | A < f x} := by
      apply congrArg ENNReal.toReal
      exact (hT.iterate j).measure_preimage (measurableSet_lt measurable_const hfm).nullMeasurableSet
    simp_rw [heq]
    simpa [mul_div_assoc] using mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg n)
  have hsub : initialAverageBad T f a n ⊆ initialAverageBad T g a n ∪ B := by
    intro x hx
    by_cases hb : x ∈ B
    · exact Or.inr hb
    · left
      obtain ⟨k,hk,hkn,hkw⟩ := hx
      refine ⟨k,hk,hkn,?_⟩
      have heq : ∑ j ∈ Finset.range k, g (T^[j] x) = ∑ j ∈ Finset.range k, f (T^[j] x) := by
        apply Finset.sum_congr rfl
        intro j hj
        apply min_eq_left
        by_contra hbad
        exact hb (Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr
          ((Finset.mem_range.mp hj).trans_le hkn),lt_of_not_ge hbad⟩⟩)
      rwa [heq]
  have havg := stationary_initial_average_bound P T hT g hgm hgi hg0 a ha n
  calc
    P.real (initialAverageBad T f a n) ≤
        P.real (initialAverageBad T g a n) + P.real B :=
      (measureReal_mono hsub).trans (measureReal_union_le _ _)
    _ ≤ truncatedMoment P f A/a + (n : ℝ)*truncatedMoment P f A/A := add_le_add havg hB
    _ = 2*truncatedMoment P f (a*n)/a := by dsimp [A]; field_simp; ring

lemma linear_envelope_of_tendsto (s : ℕ → ℝ) {m c C : ℝ}
    (hm : Tendsto (fun n : ℕ => s n / n) atTop (𝓝 m)) (hc : c < m) (hC : m < C) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ k : ℕ, c*k-b ≤ s k ∧ s k ≤ C*k+b := by
  have hh : ∀ᶠ k : ℕ in atTop, 0 < k ∧ c*k ≤ s k ∧ s k ≤ C*k := by
    filter_upwards [eventually_gt_atTop (0 : ℕ),hm (Ioo_mem_nhds hc hC)] with k hk hkm
    have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
    exact ⟨hk,(le_div_iff₀ hk').mp hkm.1.le,(div_le_iff₀ hk').mp hkm.2.le⟩
  obtain ⟨K,hK⟩ := eventually_atTop.mp hh
  let b : ℝ := ∑ k ∈ Finset.range K, (|c*k-s k|+|s k-C*k|)
  have hb : 0 ≤ b := Finset.sum_nonneg (fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
  refine ⟨b,hb,?_⟩
  intro k
  by_cases hk : K ≤ k
  · obtain ⟨_,hl,hu⟩ := hK k hk
    constructor <;> linarith
  · have hkb : |c*k-s k|+|s k-C*k| ≤ b := by
      dsimp [b]
      exact Finset.single_le_sum (fun j _ => add_nonneg (abs_nonneg (c*j-s j))
        (abs_nonneg (s j-C*j))) (Finset.mem_range.mpr (Nat.lt_of_not_ge hk))
    constructor <;> linarith [le_abs_self (c*k-s k),le_abs_self (s k-C*k),
      abs_nonneg (c*k-s k),abs_nonneg (s k-C*k)]

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

def heightEnvelope {Ω : Type*} (s : ℕ → Ω → ℝ) (c C b : ℝ) : Set Ω :=
  {x | ∀ k : ℕ, c*k-b ≤ s k x ∧ s k x ≤ C*k+b}

lemma measurableSet_heightEnvelope {Ω : Type*} [MeasurableSpace Ω]
    (s : ℕ → Ω → ℝ) (hs : ∀ k, Measurable (s k)) (c C b : ℝ) :
    MeasurableSet (heightEnvelope s c C b) := by
  unfold heightEnvelope
  simp only [Set.ofPred_forall,Set.ofPred_and]
  exact MeasurableSet.iInter (fun k => (measurableSet_le measurable_const (hs k)).inter
    (measurableSet_le (hs k) measurable_const))

lemma heightEnvelope_mono {Ω : Type*} (s : ℕ → Ω → ℝ) (c C : ℝ) :
    Monotone (heightEnvelope s c C) := by
  intro a b hab x hx k
  obtain ⟨hl,hu⟩ := hx k
  constructor <;> linarith

lemma exists_heightEnvelope_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (s : ℕ → Ω → ℝ)
    (hs : ∀ k, Measurable (s k)) {m c C : ℝ}
    (hm : ∀ᵐ x ∂P, Tendsto (fun n : ℕ => s n x / n) atTop (𝓝 m))
    (hc : c < m) (hC : m < C) {q : ℝ} (hq : q < 1) :
    ∃ b : ℝ, 0 ≤ b ∧ q < P.real (heightEnvelope s c C b) := by
  have hcover : P (⋃ b : ℕ, heightEnvelope s c C b) = 1 := by
    apply (mem_ae_iff_prob_eq_one (MeasurableSet.iUnion (fun b : ℕ =>
      measurableSet_heightEnvelope s hs c C b))).mp
    filter_upwards [hm] with x hx
    obtain ⟨b,_,hb⟩ := linear_envelope_of_tendsto (fun n => s n x) hx hc hC
    obtain ⟨k,hk⟩ := exists_nat_ge b
    exact Set.mem_iUnion.mpr ⟨k,heightEnvelope_mono s c C hk hb⟩
  have ht := tendsto_measure_iUnion_atTop (μ := P)
    (show Monotone (fun b : ℕ => heightEnvelope s c C b) from
      fun i j hij => heightEnvelope_mono s c C (Nat.cast_le.mpr hij))
  rw [hcover] at ht
  have htr : Tendsto (fun b : ℕ => P.real (heightEnvelope s c C b)) atTop (𝓝 1) := by
    simpa only [ENNReal.toReal_one,Function.comp_def,Measure.real] using (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp ht
  have hev : ∀ᶠ b : ℕ in atTop, q < P.real (heightEnvelope s c C b) :=
    htr.eventually (eventually_gt_nhds hq)
  obtain ⟨b,hb⟩ := hev.exists
  exact ⟨b,Nat.cast_nonneg _,hb⟩

lemma indepFun_initial_block {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (P : Measure Ω) (f : ℕ → Ω → α) (hf : ∀ i, Measurable (f i))
    (hind : iIndepFun f P) (n : ℕ) :
    IndepFun (fun x (i : Fin n) => f i x) (f n) P := by
  have hd : Disjoint (Finset.range n) {n} := by simp
  have hh := hind.indepFun_finset (Finset.range n) {n} hd hf
  exact hh.comp (Measurable.of_eval (f := fun v (i : Fin n) =>
    v ⟨i,Finset.mem_range.mpr i.isLt⟩) (fun _ => measurable_pi_apply _))
    (measurable_pi_apply ⟨n,by simp⟩)

noncomputable def prefixSum {α : Type*} {n : ℕ} (f : α → ℝ) (v : Fin n → α) (k : ℕ) : ℝ :=
  ∑ j : Fin n, if (j : ℕ) < k then f (v j) else 0

lemma prefixSum_eq {α : Type*} (f : α → ℝ) (v : ℕ → α) {k n : ℕ} (hk : k ≤ n) :
    prefixSum f (fun i : Fin n => v i) k = ∑ j ∈ Finset.range k, f (v j) := by
  classical
  unfold prefixSum
  rw [Fin.sum_univ_eq_sum_range (fun j => if j < k then f (v j) else 0),← Finset.sum_filter]
  have he : (Finset.range n).filter (fun j => j < k) = Finset.range k := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_range]
    omega
  rw [he]

lemma initial_block_factorization {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (P : Measure Ω) (f : ℕ → Ω → α) (hf : ∀ i, Measurable (f i))
    (hind : iIndepFun f P) (n : ℕ) (A : Set (Fin n → α)) (B : Set α)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    P.real ({x | (fun i : Fin n => f i x) ∈ A} ∩ {x | f n x ∈ B}) =
      P.real {x | (fun i : Fin n => f i x) ∈ A} * P.real {x | f n x ∈ B} := by
  have hh := (indepFun_initial_block P f hf hind n).measure_inter_preimage_eq_mul A B hA hB
  exact congrArg ENNReal.toReal hh |>.trans ENNReal.toReal_mul

def goodRadiusTuple {d m : ℕ} (v : Fin d → ℝ) (a c C b : ℝ) :
    Set (Fin m → Word d) :=
  {γ | ∀ k : ℕ, k ≤ m → c*k-b ≤ prefixSum (slabWidth v) γ k ∧
    prefixSum (slabWidth v) γ k ≤ C*k+b ∧ prefixSum slabRadius γ k ≤ a*k}

def goodRadiusPrefix {d : ℕ} (v : Fin d → ℝ) (a c C b : ℝ) (m : ℕ) : Set (Path d) :=
  {X | (fun i : Fin m => slabs v X i) ∈ goodRadiusTuple v a c C b}

lemma goodRadiusPrefix_iff {d : ℕ} (v : Fin d → ℝ) (a c C b : ℝ) (m : ℕ) (X : Path d) :
    X ∈ goodRadiusPrefix v a c C b m ↔ ∀ k : ℕ, k ≤ m →
      c*k-b ≤ slabHeightSum v X k ∧ slabHeightSum v X k ≤ C*k+b ∧
      slabRadiusSum v X k ≤ a*k := by
  simp only [goodRadiusPrefix,goodRadiusTuple,Set.mem_ofPred_eq]
  apply forall_congr'
  intro k
  apply forall_congr'
  intro hk
  rw [prefixSum_eq _ _ hk,prefixSum_eq _ _ hk]
  rfl

lemma measurableSet_goodRadiusPrefix {d : ℕ} (v : Fin d → ℝ) (a c C b : ℝ) (m : ℕ) :
    MeasurableSet (goodRadiusPrefix v a c C b m) :=
  (Set.to_countable _).measurableSet.preimage (Measurable.of_eval (fun i =>
    (measurable_pi_apply (i : ℕ)).comp (measurable_slabs v)))

lemma goodRadiusPrefix_mono {d : ℕ} (v : Fin d → ℝ) (a c C b : ℝ) {m n : ℕ}
    (hmn : m ≤ n) : goodRadiusPrefix v a c C b n ⊆ goodRadiusPrefix v a c C b m := by
  intro X hX
  rw [goodRadiusPrefix_iff] at hX ⊢
  exact fun k hk => hX k (hk.trans hmn)

lemma slab_truncated_average_bound {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) (a : ℝ) (ha : 0 < a)
    (n : ℕ) (hn : 0 < n) :
    (conditioned μ v).real {X | ∃ k : ℕ, 0 < k ∧ k ≤ n ∧ a*k < slabRadiusSum v X k} ≤
      2*truncatedMoment (slabLaw μ v) slabRadius (a*n)/a := by
  let := conditioned_probability μ v hp
  have hh := stationary_truncated_average_bound (conditioned μ v) (cutSuffix v)
    (cutSuffix_measurePreserving μ hell v hv hp) (fun X => slabRadius (firstWord v X))
    ((measurable_of_countable slabRadius).comp (measurable_firstWord v))
    (fun _ => slabRadius_nonneg _) a ha n hn
  have hi := (slabs_identDistrib μ hell v hv hp 0).comp
    (measurable_of_countable (fun γ => min (slabRadius γ) (a*n)))
  have he : truncatedMoment (conditioned μ v) (fun X => slabRadius (firstWord v X)) (a*n) =
      truncatedMoment (slabLaw μ v) slabRadius (a*n) := hi.integral_eq
  simpa only [initialAverageBad,slabs,slabRadiusSum,he] using hh

lemma goodRadiusPrefix_probability {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) (a c C b : ℝ) (ha : 0 < a)
    (n : ℕ) (hn : 0 < n) :
    (conditioned μ v).real (heightEnvelope (fun k X => slabHeightSum v X k) c C b) -
      2*truncatedMoment (slabLaw μ v) slabRadius (a*n)/a ≤
      (conditioned μ v).real (goodRadiusPrefix v a c C b n) := by
  let := conditioned_probability μ v hp
  let B : Set (Path d) := {X | ∃ k : ℕ, 0 < k ∧ k ≤ n ∧ a*k < slabRadiusSum v X k}
  have hsub : heightEnvelope (fun k X => slabHeightSum v X k) c C b ⊆
      goodRadiusPrefix v a c C b n ∪ B := by
    intro X hX
    by_cases hB : X ∈ B
    · exact Or.inr hB
    · left
      rw [goodRadiusPrefix_iff]
      intro k hk
      refine ⟨(hX k).1,(hX k).2,?_⟩
      by_cases hk0 : k = 0
      · simp [hk0,slabRadiusSum]
      · exact le_of_not_gt (fun h => hB ⟨k,Nat.pos_of_ne_zero hk0,hk,h⟩)
  have hu := (measureReal_mono (μ := conditioned μ v) hsub (measure_ne_top _ _)).trans
    (measureReal_union_le (μ := conditioned μ v) _ _)
  have hb := slab_truncated_average_bound μ hell v hv hp a ha n hn
  change (conditioned μ v).real B ≤ _ at hb
  linarith

lemma goodRadiusPrefix_current_factorization {d : ℕ} (μ : Measure (Row d))
    [IsProbabilityMeasure μ] (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) (a c C b : ℝ) (n : ℕ)
    (G : Set (Word d)) :
    (conditioned μ v).real (goodRadiusPrefix v a c C b n ∩ {X | slabs v X n ∈ G}) =
      (conditioned μ v).real (goodRadiusPrefix v a c C b n) * (slabLaw μ v).real G := by
  have hh := initial_block_factorization (conditioned μ v) (fun i X => slabs v X i)
    (fun i => (measurable_pi_apply i).comp (measurable_slabs v))
    (slabs_iid μ hell v hv hp) n (goodRadiusTuple v a c C b) G
    (Set.to_countable _).measurableSet (Set.to_countable _).measurableSet
  have he : (conditioned μ v).real {X | slabs v X n ∈ G} = (slabLaw μ v).real G := by
    apply congrArg ENNReal.toReal
    rw [← slabs_marginal μ hell v hv hp n]
    exact (Measure.map_apply ((measurable_pi_apply n).comp (measurable_slabs v))
      (Set.to_countable G).measurableSet).symm
  simpa only [goodRadiusPrefix,he] using hh

lemma truncatedMoment_sub_le_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → ℝ) (hfm : Measurable f)
    (hf : ∀ x, 0 ≤ f x) {t D : ℝ} (ht : 0 ≤ t) (hD : 0 ≤ D) :
    truncatedMoment P f (t+D)-truncatedMoment P f t ≤ D*P.real {x | t < f x} := by
  have hS : MeasurableSet {x | t < f x} := measurableSet_lt measurable_const hfm
  have hi := (integrable_min_const P f hfm hf (t+D) (add_nonneg ht hD)).sub
    (integrable_min_const P f hfm hf t ht)
  have hb : ∀ x, min (f x) (t+D)-min (f x) t ≤
      Set.indicator {x | t < f x} (fun _ => D) x := by
    intro x
    by_cases h : t < f x
    · rw [Set.indicator_of_mem (s := {x | t < f x}) h,min_eq_right h.le]
      linarith [min_le_right (f x) (t+D)]
    · have he : f x ≤ t := le_of_not_gt h
      rw [Set.indicator_of_notMem (s := {x | t < f x}) h,min_eq_left he,
        min_eq_left (he.trans (le_add_of_nonneg_right hD))]
      linarith
  have hh := integral_mono hi ((integrable_const D).indicator hS) hb
  simp only [Pi.sub_apply] at hh
  rw [integral_sub (integrable_min_const P f hfm hf (t+D) (add_nonneg ht hD))
      (integrable_min_const P f hfm hf t ht),integral_indicator_const D hS,
    smul_eq_mul,mul_comm (P.real _) D] at hh
  exact hh

lemma mul_tail_le_truncatedMoment_sub {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → ℝ) (hfm : Measurable f)
    (hf : ∀ x, 0 ≤ f x) {t D : ℝ} (ht : 0 ≤ t) (hD : 0 ≤ D) :
    D*P.real {x | t+D < f x} ≤ truncatedMoment P f (t+D)-truncatedMoment P f t := by
  have hS : MeasurableSet {x | t+D < f x} := measurableSet_lt measurable_const hfm
  have hi := (integrable_min_const P f hfm hf (t+D) (add_nonneg ht hD)).sub
    (integrable_min_const P f hfm hf t ht)
  have hb : ∀ x, Set.indicator {x | t+D < f x} (fun _ => D) x ≤
      min (f x) (t+D)-min (f x) t := by
    intro x
    by_cases h : t+D < f x
    · rw [Set.indicator_of_mem (s := {x | t+D < f x}) h,min_eq_right h.le,
        min_eq_right ((le_add_of_nonneg_right hD).trans h.le)]
      linarith
    · rw [Set.indicator_of_notMem (s := {x | t+D < f x}) h]
      exact sub_nonneg.mpr (min_le_min_left _ (le_add_of_nonneg_right hD))
  have hh := integral_mono ((integrable_const D).indicator hS) hi hb
  simp only [Pi.sub_apply] at hh
  rw [integral_sub (integrable_min_const P f hfm hf (t+D) (add_nonneg ht hD))
      (integrable_min_const P f hfm hf t ht),integral_indicator_const D hS,
    smul_eq_mul,mul_comm (P.real _) D] at hh
  exact hh

lemma truncatedMoment_zero {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ℝ) (hf : ∀ x, 0 ≤ f x) :
    truncatedMoment P f 0 = 0 := by
  simp [truncatedMoment, min_eq_right (hf _)]

lemma tail_sum_lower {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → ℝ) (hfm : Measurable f)
    (hf : ∀ x, 0 ≤ f x) {a : ℝ} (ha : 0 < a) (l n : ℕ) :
    truncatedMoment P f (a*(l+n))-truncatedMoment P f (a*l) ≤
      a*∑ i ∈ Finset.range n, P.real {x | a*(l+i) < f x} := by
  have hi (i : ℕ) := truncatedMoment_sub_le_tail P f hfm hf
    (t := a*(l+i)) (D := a) (mul_nonneg ha.le (by positivity)) ha.le
  have hsum := Finset.sum_le_sum (s := Finset.range n) (fun i _ => hi i)
  have he (i : ℕ) : a*(l+i)+a = a*((l+(i+1) : ℕ) : ℝ) := by push_cast; ring
  simp_rw [he] at hsum
  rw [← Finset.mul_sum] at hsum
  have htel := Finset.sum_range_sub (fun i : ℕ => truncatedMoment P f (a*(l+i))) n
  simp only [Nat.cast_add,Nat.cast_one,Nat.cast_zero,add_zero] at htel hsum
  rw [htel] at hsum
  exact hsum

lemma tail_sum_upper {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → ℝ) (hfm : Measurable f)
    (hf : ∀ x, 0 ≤ f x) {a : ℝ} (ha : 0 < a) (n : ℕ) :
    a*∑ i ∈ Finset.range n, P.real {x | a*(i+1) < f x} ≤
      truncatedMoment P f (a*n) := by
  have hi (i : ℕ) := mul_tail_le_truncatedMoment_sub P f hfm hf
    (t := a*i) (D := a) (mul_nonneg ha.le (Nat.cast_nonneg _)) ha.le
  have hsum := Finset.sum_le_sum (s := Finset.range n) (fun i _ => hi i)
  have he (i : ℕ) : a*i+a = a*((i+1 : ℕ) : ℝ) := by push_cast; ring
  simp_rw [he] at hsum
  rw [← Finset.mul_sum,Finset.sum_range_sub (fun i : ℕ => truncatedMoment P f (a*i)) n] at hsum
  simpa [truncatedMoment_zero P f hf] using hsum

lemma summable_real_tail_of_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → ℝ) (hfm : Measurable f)
    (hf : ∀ x, 0 ≤ f x) (hfi : Integrable f P) :
    Summable (fun n : ℕ => P.real {x | (n+1 : ℝ) < f x}) := by
  apply summable_of_sum_range_le (fun _ => measureReal_nonneg) (c := ∫ x, f x ∂P)
  intro n
  have hb := tail_sum_upper P f hfm hf (a := 1) zero_lt_one n
  simp only [one_mul] at hb
  apply hb.trans
  exact integral_mono (integrable_min_const P f hfm hf n (Nat.cast_nonneg _)) hfi
    (fun x => min_le_left _ _)

lemma union_lower_of_pair_bounds {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (A G : ι → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (hAG : ∀ i, A i ⊆ G i)
    (hpair : ∀ i j, i ≠ j → P.real (G i ∩ G j) ≤ P.real (G i)*P.real (G j))
    (s : Finset ι) :
    (∑ i ∈ s, P.real (A i)) ≤ P.real (⋃ i ∈ s, A i) + (∑ i ∈ s, P.real (G i))^2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    let U := ⋃ j ∈ s, A j
    let L := ∑ j ∈ s, P.real (G j)
    have hL : 0 ≤ L := Finset.sum_nonneg (fun _ _ => measureReal_nonneg)
    have hp : 0 ≤ P.real (G i) := measureReal_nonneg
    have hU : MeasurableSet U := MeasurableSet.biUnion (Finset.countable_toSet s) (fun j _ => hA j)
    have hu : P.real (A i ∪ U) + P.real (A i ∩ U) = P.real (A i)+P.real U :=
      measureReal_union_add_inter₀ hU.nullMeasurableSet (measure_ne_top _ _) (measure_ne_top _ _)
    have hsub : A i ∩ U ⊆ ⋃ j ∈ s, G i ∩ G j := by
      rintro x ⟨hx,hy⟩
      obtain ⟨j,hj,hxj⟩ := Set.mem_iUnion₂.mp hy
      exact Set.mem_iUnion₂.mpr ⟨j,hj,hAG i hx,hAG j hxj⟩
    have hint : P.real (A i ∩ U) ≤ P.real (G i)*L := by
      apply (measureReal_mono hsub (measure_ne_top _ _)).trans
      apply (measureReal_biUnion_finset_le s _).trans
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun j hj => hpair i j (fun hij => hi (hij ▸ hj)))
    simp only [Finset.sum_insert hi,Finset.set_biUnion_insert]
    change P.real (A i) + ∑ j ∈ s, P.real (A j) ≤ P.real (A i ∪ U) + (P.real (G i)+L)^2
    change (∑ j ∈ s, P.real (A j)) ≤ P.real U + L^2 at ih
    nlinarith

lemma controlled_occurrence_lower {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (R G : ι → Set Ω)
    (hR : ∀ i, MeasurableSet (R i)) (hG : ∀ i, MeasurableSet (G i))
    (hind : ∀ i, P.real (R i ∩ G i) = P.real (R i)*P.real (G i))
    (hpair : ∀ i j, i ≠ j → P.real (G i ∩ G j) ≤ P.real (G i)*P.real (G j))
    (s : Finset ι) (q : ℝ) (hq : ∀ i ∈ s, q ≤ P.real (R i)) :
    q*(∑ i ∈ s, P.real (G i)) - (∑ i ∈ s, P.real (G i))^2 ≤
      P.real (⋃ i ∈ s, R i ∩ G i) := by
  have hu := union_lower_of_pair_bounds P (fun i => R i ∩ G i) G
    (fun i => (hR i).inter (hG i)) (fun _ => Set.inter_subset_right) hpair s
  have hl : q*(∑ i ∈ s, P.real (G i)) ≤ ∑ i ∈ s, P.real (R i ∩ G i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [hind]
    exact mul_le_mul_of_nonneg_right (hq i hi) measureReal_nonneg
  linarith

lemma truncatedMoment_add_measure {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure Q] (f : Ω → ℝ)
    (hfm : Measurable f) (hf : ∀ x, 0 ≤ f x) {t : ℝ} (ht : 0 ≤ t) :
    truncatedMoment (P+Q) f t = truncatedMoment P f t + truncatedMoment Q f t :=
  integral_add_measure (integrable_min_const P f hfm hf t ht)
    (integrable_min_const Q f hfm hf t ht)

lemma tail_sum_Ico_lower {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → ℝ) (hfm : Measurable f)
    (hf : ∀ x, 0 ≤ f x) {a : ℝ} (ha : 0 < a) {l n : ℕ} (hln : l ≤ n) :
    truncatedMoment P f (a*(n+1))-truncatedMoment P f (a*(l+1)) ≤
      a*∑ i ∈ Finset.Ico l n, P.real {x | a*(i+1) < f x} := by
  have hi (i : ℕ) := truncatedMoment_sub_le_tail P f hfm hf
    (t := a*(i+1)) (D := a) (mul_nonneg ha.le (by positivity)) ha.le
  have hsum := Finset.sum_le_sum (s := Finset.Ico l n) (fun i _ => hi i)
  have he (i : ℕ) : a*(i+1)+a = a*((i+1 : ℕ)+1) := by push_cast; ring
  simp_rw [he] at hsum
  rw [← Finset.mul_sum,Finset.sum_Ico_sub (fun i : ℕ => truncatedMoment P f (a*(i+1))) hln] at hsum
  exact hsum

def largeRadiusWord {Ω : Type*} (R L : Ω → ℝ) (a : ℝ) (i : ℕ) : Set Ω :=
  {x | a*(i+1) < R x ∧ L x ≤ i+1}

lemma largeRadius_mass_bounds {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (R L : Ω → ℝ) (hR : Measurable R)
    (hRn : ∀ x, 0 ≤ R x) {a : ℝ} (ha : 0 < a) {l n : ℕ} (hln : l ≤ n) :
    (truncatedMoment P R (a*(n+1))-truncatedMoment P R (a*(l+1)))/a -
        (∑ i ∈ Finset.Ico l n, P.real {x | (i+1 : ℝ) < L x}) ≤
        ∑ i ∈ Finset.Ico l n, P.real (largeRadiusWord R L a i) ∧
      (∑ i ∈ Finset.Ico l n, P.real (largeRadiusWord R L a i)) ≤
        truncatedMoment P R (a*n)/a := by
  have hu (i : ℕ) : P.real (largeRadiusWord R L a i) ≤ P.real {x | a*(i+1) < R x} :=
    measureReal_mono (fun _ h => h.1) (measure_ne_top _ _)
  have hl (i : ℕ) : P.real {x | a*(i+1) < R x} ≤
      P.real (largeRadiusWord R L a i) + P.real {x | (i+1 : ℝ) < L x} := by
    have hs : {x | a*(i+1) < R x} ⊆ largeRadiusWord R L a i ∪ {x | (i+1 : ℝ) < L x} := by
      intro x hx
      by_cases h : L x ≤ i+1
      · exact Or.inl ⟨hx,h⟩
      · exact Or.inr (lt_of_not_ge h)
    exact (measureReal_mono hs (measure_ne_top _ _)).trans (measureReal_union_le _ _)
  constructor
  · have hsum := Finset.sum_le_sum (s := Finset.Ico l n) (fun i _ => hl i)
    rw [Finset.sum_add_distrib] at hsum
    have hh := tail_sum_Ico_lower P R hR hRn ha hln
    have hh' : (truncatedMoment P R (a*(n+1))-truncatedMoment P R (a*(l+1)))/a ≤
        ∑ i ∈ Finset.Ico l n, P.real {x | a*(i+1) < R x} :=
      (div_le_iff₀ ha).mpr (by nlinarith only [hh])
    linarith
  · apply (Finset.sum_le_sum (fun i _ => hu i)).trans
    have hs : Finset.Ico l n ⊆ Finset.range n := fun i hi => Finset.mem_range.mpr (Finset.mem_Ico.mp hi).2
    apply (Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => measureReal_nonneg)).trans
    apply (le_div_iff₀ ha).mpr
    nlinarith only [tail_sum_upper P R hR hRn ha n]

lemma largeRadius_mass_pair_lower {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (R L K : Ω → ℝ) (hR : Measurable R) (hRn : ∀ x, 0 ≤ R x)
    {a B η : ℝ} (ha : 0 < a) (hB : 1 ≤ B) (hη : 0 < η) {l n : ℕ} (hln : l ≤ n)
    (hscale : η*a ≤ truncatedMoment (P+Q) R (a*n))
    (hsmall : truncatedMoment (P+Q) R (B*a*(l+1)) < η*a/4)
    (hwidth : (∑ i ∈ Finset.Ico l n, P.real {x | (i+1 : ℝ) < L x}) +
      (∑ i ∈ Finset.Ico l n, Q.real {x | (i+1 : ℝ) < K x}) < η/(4*B)) :
    η/(2*B) ≤ (∑ i ∈ Finset.Ico l n, P.real (largeRadiusWord R L (B*a) i)) +
      (∑ i ∈ Finset.Ico l n, Q.real (largeRadiusWord R K (B*a) i)) := by
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hBa : 0 < B*a := mul_pos hB0 ha
  have hp := (largeRadius_mass_bounds P R L hR hRn hBa hln).1
  have hq := (largeRadius_mass_bounds Q R K hR hRn hBa hln).1
  have hadd1 := truncatedMoment_add_measure P Q R hR hRn
    (t := B*a*(n+1)) (by positivity)
  have hadd2 := truncatedMoment_add_measure P Q R hR hRn
    (t := B*a*(l+1)) (by positivity)
  have hmono : truncatedMoment (P+Q) R (a*n) ≤ truncatedMoment (P+Q) R (B*a*(n+1)) := by
    apply truncatedMoment_mono _ _ hR hRn (by positivity)
    have hh := mul_le_mul_of_nonneg_right hB (show 0 ≤ a*((n : ℝ)+1) by positivity)
    nlinarith only [hh,ha]
  have hlow : η*a ≤ truncatedMoment (P+Q) R (B*a*(n+1)) := hscale.trans hmono
  have hd : η/(2*B) + η/(4*B) = (η*a-η*a/4)/(B*a) := by field_simp; ring
  rw [hadd1] at hlow
  rw [hadd2] at hsmall
  have htot : (η*a-η*a/4)/(B*a) ≤
      (truncatedMoment P R (B*a*(n+1))-truncatedMoment P R (B*a*(l+1)))/(B*a) +
      (truncatedMoment Q R (B*a*(n+1))-truncatedMoment Q R (B*a*(l+1)))/(B*a) := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by linarith) hBa.le
  linarith

lemma largeRadius_mass_pair_upper {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (R L K : Ω → ℝ) (hR : Measurable R) (hRn : ∀ x, 0 ≤ R x)
    {a B η : ℝ} (ha : 0 < a) (hB : 1 ≤ B) {l n : ℕ} (hln : l ≤ n)
    (hscale : truncatedMoment (P+Q) R (a*n) < 2*η*a) :
    (∑ i ∈ Finset.Ico l n, P.real (largeRadiusWord R L (B*a) i)) +
      (∑ i ∈ Finset.Ico l n, Q.real (largeRadiusWord R K (B*a) i)) < 2*η := by
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hBa : 0 < B*a := mul_pos hB0 ha
  have hp := (largeRadius_mass_bounds P R L hR hRn hBa hln).2
  have hq := (largeRadius_mass_bounds Q R K hR hRn hBa hln).2
  have hadd := truncatedMoment_add_measure P Q R hR hRn (t := B*a*n) (by positivity)
  have hmul := truncatedMoment_mul_le (P+Q) R hR hRn (t := a*n) (by positivity) hB
  rw [← mul_assoc] at hmul
  have hh : truncatedMoment (P+Q) R (B*a*n)/(B*a) < 2*η := by
    apply (div_lt_iff₀ hBa).mpr
    have hs := mul_lt_mul_of_pos_left hscale hB0
    nlinarith only [hmul,hs]
  rw [hadd,add_div] at hh
  linarith

lemma slabs_event_measureReal {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) (i : ℕ) (G : Set (Word d)) :
    (conditioned μ v).real {X | slabs v X i ∈ G} = (slabLaw μ v).real G := by
  apply congrArg ENNReal.toReal
  rw [← slabs_marginal μ hell v hv hp i]
  exact (Measure.map_apply ((measurable_pi_apply i).comp (measurable_slabs v))
    (Set.to_countable G).measurableSet).symm

lemma slabs_pair_event_factorization {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) {i j : ℕ} (hij : i ≠ j)
    (G H : Set (Word d)) :
    (conditioned μ v).real ({X | slabs v X i ∈ G} ∩ {X | slabs v X j ∈ H}) =
      (slabLaw μ v).real G * (slabLaw μ v).real H := by
  have hh := ((slabs_iid μ hell v hv hp).indepFun hij).measure_inter_preimage_eq_mul
    G H (Set.to_countable G).measurableSet (Set.to_countable H).measurableSet
  have hh' := congrArg ENNReal.toReal hh
  rw [ENNReal.toReal_mul] at hh'
  change (conditioned μ v).real ({X | slabs v X i ∈ G} ∩ {X | slabs v X j ∈ H}) =
    (conditioned μ v).real {X | slabs v X i ∈ G} * (conditioned μ v).real {X | slabs v X j ∈ H} at hh'
  rwa [slabs_event_measureReal μ hell v hv hp i G,slabs_event_measureReal μ hell v hv hp j H] at hh'

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

def controlledSlabOccurrence {d : ℕ} (v : Fin d → ℝ) (a c C b : ℝ)
    (G : ℕ → Set (Word d)) (s : Finset ℕ) : Set (Path d) :=
  ⋃ i ∈ s, goodRadiusPrefix v a c C b i ∩ {X | slabs v X i ∈ G i}

lemma measurableSet_controlledSlabOccurrence {d : ℕ} (v : Fin d → ℝ) (a c C b : ℝ)
    (G : ℕ → Set (Word d)) (s : Finset ℕ) :
    MeasurableSet (controlledSlabOccurrence v a c C b G s) := by
  apply MeasurableSet.biUnion (Finset.countable_toSet s)
  intro i hi
  exact (measurableSet_goodRadiusPrefix v a c C b i).inter
    ((Set.to_countable (G i)).measurableSet.preimage
      ((measurable_pi_apply i).comp (measurable_slabs v)))

lemma controlledSlabOccurrence_probability {d : ℕ} (μ : Measure (Row d))
    [IsProbabilityMeasure μ] (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) (a c C b : ℝ)
    (G : ℕ → Set (Word d)) (s : Finset ℕ) (q : ℝ)
    (hq : ∀ i ∈ s, q ≤ (conditioned μ v).real (goodRadiusPrefix v a c C b i)) :
    q*(∑ i ∈ s, (slabLaw μ v).real (G i)) - (∑ i ∈ s, (slabLaw μ v).real (G i))^2 ≤
      (conditioned μ v).real (controlledSlabOccurrence v a c C b G s) := by
  let := conditioned_probability μ v hp
  have hG (i : ℕ) : MeasurableSet {X | slabs v X i ∈ G i} :=
    (Set.to_countable (G i)).measurableSet.preimage
      ((measurable_pi_apply i).comp (measurable_slabs v))
  have hind (i : ℕ) :
      (conditioned μ v).real (goodRadiusPrefix v a c C b i ∩ {X | slabs v X i ∈ G i}) =
        (conditioned μ v).real (goodRadiusPrefix v a c C b i) *
          (conditioned μ v).real {X | slabs v X i ∈ G i} := by
    rw [goodRadiusPrefix_current_factorization μ hell v hv hp,
      slabs_event_measureReal μ hell v hv hp]
  have hpair (i j : ℕ) (hij : i ≠ j) :
      (conditioned μ v).real ({X | slabs v X i ∈ G i} ∩ {X | slabs v X j ∈ G j}) ≤
        (conditioned μ v).real {X | slabs v X i ∈ G i} *
          (conditioned μ v).real {X | slabs v X j ∈ G j} := by
    rw [slabs_pair_event_factorization μ hell v hv hp hij,
      slabs_event_measureReal μ hell v hv hp,slabs_event_measureReal μ hell v hv hp]
  have hh := controlled_occurrence_lower (conditioned μ v) (goodRadiusPrefix v a c C b)
    (fun i => {X | slabs v X i ∈ G i}) (measurableSet_goodRadiusPrefix v a c C b)
    hG hind hpair s q hq
  simpa only [slabs_event_measureReal μ hell v hv hp,controlledSlabOccurrence] using hh

lemma controlledSlabOccurrence_probability_half {d : ℕ} (μ : Measure (Row d))
    [IsProbabilityMeasure μ] (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) (a c C b : ℝ)
    (G : ℕ → Set (Word d)) (s : Finset ℕ)
    (hq : ∀ i ∈ s, (3:ℝ)/4 ≤ (conditioned μ v).real (goodRadiusPrefix v a c C b i))
    (hsmall : (∑ i ∈ s, (slabLaw μ v).real (G i)) ≤ 1/4) :
    (∑ i ∈ s, (slabLaw μ v).real (G i))/2 ≤
      (conditioned μ v).real (controlledSlabOccurrence v a c C b G s) := by
  have hh := controlledSlabOccurrence_probability μ hell v hv hp a c C b G s (3/4) hq
  have hn : 0 ≤ ∑ i ∈ s, (slabLaw μ v).real (G i) :=
    Finset.sum_nonneg (fun _ _ => measureReal_nonneg)
  nlinarith

lemma slabWidth_pos_of_regeneration {d : ℕ} (v : Fin d → ℝ) (γ : Word d)
    (hγ : RegenerationWord v γ) : 0 < slabWidth v γ := by
  have hh := (hγ.2.2.2.1 0 hγ.1).2
  simpa only [hγ.2.1,height_zero,slabWidth] using hh

lemma slabHeightSum_strictMono {d : ℕ} (v : Fin d → ℝ) (X : Path d)
    (hX : GoodSlabPath v X) : StrictMono (slabHeightSum v X) := by
  apply strictMono_nat_of_lt_succ
  intro k
  change slabHeightSum v X k < ∑ i ∈ Finset.range (k+1), slabWidth v (slabs v X i)
  rw [Finset.sum_range_succ]
  exact lt_add_of_pos_right _ (slabWidth_pos_of_regeneration v _ (hX.2 k))

lemma slabHeightSum_nonneg {d : ℕ} (v : Fin d → ℝ) (X : Path d)
    (hX : GoodSlabPath v X) (k : ℕ) : 0 ≤ slabHeightSum v X k :=
  Finset.sum_nonneg (fun i _ => (slabWidth_pos_of_regeneration v _ (hX.2 i)).le)

lemma slabRadiusSum_mono {d : ℕ} (v : Fin d → ℝ) (X : Path d) :
    Monotone (slabRadiusSum v X) := by
  intro m n hmn
  exact nonneg_sum_range_mono (fun i => slabRadius (slabs v X i)) (fun _ => slabRadius_nonneg _) hmn

lemma goodSlabPath_height_nonneg {d : ℕ} (v : Fin d → ℝ) (X : Path d)
    (hX : GoodSlabPath v X) (t : ℕ) : 0 ≤ height v (X t) := by
  obtain ⟨k,hkt,htk⟩ := slab_location v X hX t
  have hj : t-slabTime v X k < (slabs v X k).1 := by rw [slabTime_succ] at htk; omega
  have hh := (height_in_slab v X hX k (t-slabTime v X k) hj).1
  rw [Nat.add_sub_of_le hkt] at hh
  exact (slabHeightSum_nonneg v X hX k).trans hh

lemma height_before_slabTime_le {d : ℕ} (v : Fin d → ℝ) (X : Path d)
    (hX : GoodSlabPath v X) {k t : ℕ} (ht : t ≤ slabTime v X k) :
    height v (X t) ≤ slabHeightSum v X k := by
  rcases ht.eq_or_lt with ht | ht
  · rw [ht,height_at_slabTime v X hX.1]
  · obtain ⟨j,hjt,htj⟩ := slab_location v X hX t
    have hjk : j < k := (slabTime_strictMono v X hX).lt_iff_lt.mp (hjt.trans_lt ht)
    have hj : t-slabTime v X j < (slabs v X j).1 := by rw [slabTime_succ] at htj; omega
    have hh := (height_in_slab v X hX j (t-slabTime v X j) hj).2
    rw [Nat.add_sub_of_le hjt] at hh
    exact hh.le.trans ((slabHeightSum_strictMono v X hX).monotone (by omega))

lemma height_after_slabTime_le {d : ℕ} (v : Fin d → ℝ) (X : Path d)
    (hX : GoodSlabPath v X) {k t : ℕ} (ht : slabTime v X k ≤ t) :
    slabHeightSum v X k ≤ height v (X t) := by
  obtain ⟨j,hjt,htj⟩ := slab_location v X hX t
  have hkj : k ≤ j := by
    have := (slabTime_strictMono v X hX).lt_iff_lt.mp (ht.trans_lt htj)
    omega
  have hj : t-slabTime v X j < (slabs v X j).1 := by rw [slabTime_succ] at htj; omega
  have hh := (height_in_slab v X hX j (t-slabTime v X j) hj).1
  rw [Nat.add_sub_of_le hjt] at hh
  exact ((slabHeightSum_strictMono v X hX).monotone hkj).trans hh

lemma norm_before_slabTime_le {d : ℕ} (v : Fin d → ℝ) (X : Path d)
    (hX : GoodSlabPath v X) {k t : ℕ} (ht : t ≤ slabTime v X k) :
    ‖euclideanSite (X t)‖ ≤ slabRadiusSum v X k := by
  rcases ht.eq_or_lt with ht | ht
  · rw [ht]
    exact norm_at_slabTime_le v X hX k
  · obtain ⟨j,hjt,htj⟩ := slab_location v X hX t
    have hjk : j < k := (slabTime_strictMono v X hX).lt_iff_lt.mp (hjt.trans_lt ht)
    have hj : t-slabTime v X j ≤ (slabs v X j).1 := by rw [slabTime_succ] at htj; omega
    have hh := norm_in_slab_le v X hX j (t-slabTime v X j) hj
    rw [Nat.add_sub_of_le hjt] at hh
    exact hh.trans (slabRadiusSum_mono v X (by omega))

def stepDirection {d : ℕ} (e : Step d) : Fin d → ℝ := fun i => (stepVector e i : ℝ)

lemma height_stepDirection {d : ℕ} (e : Step d) (x : Site d) :
    height (stepDirection e) x = if e.2 then (x e.1 : ℝ) else -(x e.1 : ℝ) := by
  simp only [height,stepDirection,stepVector]
  simp only [Int.cast_ite,Int.cast_zero,Int.cast_one,Int.cast_neg,mul_ite,mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ e.1,ite_eq_left (Finset.mem_univ _)]
  cases e.2 <;> simp

lemma height_stepDirection_le_norm {d : ℕ} (e : Step d) (x : Site d) :
    |height (stepDirection e) x| ≤ ‖euclideanSite x‖ := by
  have hh := PiLp.norm_apply_le (euclideanSite x) e.1
  rw [height_stepDirection]
  cases e.2 <;> simpa [euclideanSite] using hh

lemma exists_large_signedCoordinate {d : ℕ} (x : Site d) {A : ℝ} (hA : 0 ≤ A)
    (hx : Real.sqrt d*A < ‖euclideanSite x‖) :
    ∃ e : Step d, A < height (stepDirection e) x := by
  by_contra h
  push Not at h
  have hb (i : Fin d) : |(x i : ℝ)| ≤ A := by
    have hp := h (i,true)
    have hm := h (i,false)
    rw [height_stepDirection] at hp hm
    simp only [Bool.false_eq_true,ite_false,ite_true] at hp hm
    exact abs_le.mpr ⟨by linarith, hp⟩
  have hs : ∑ i : Fin d, (x i : ℝ)^2 ≤ (d : ℝ)*A^2 := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => sq_le_sq₀ (abs_nonneg (x i : ℝ)) hA |>.mpr (hb i))
    simpa only [sq_abs,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hh
  have he := EuclideanSpace.real_norm_sq_eq (euclideanSite x)
  simp only [euclideanSite,WithLp.ofLp_toLp] at he
  have hd := Real.sq_sqrt (show (0 : ℝ) ≤ d by positivity)
  have hprod : (Real.sqrt (d : ℝ)*A)^2 = (d : ℝ)*A^2 := by rw [mul_pow,hd]
  have hp : 0 ≤ Real.sqrt (d : ℝ)*A := mul_nonneg (Real.sqrt_nonneg _) hA
  change ‖euclideanSite x‖^2 = ∑ i : Fin d, (x i : ℝ)^2 at he
  have hx2 := (sq_lt_sq₀ hp (norm_nonneg (euclideanSite x))).mpr hx
  rw [hprod,he] at hx2
  exact (not_lt_of_ge hs) hx2

def tiltDirection {d : ℕ} (v : Fin d → ℝ) (e : Step d) (t : ℝ) : Fin d → ℝ :=
  fun i => stepDirection e i - t*v i

lemma height_tiltDirection {d : ℕ} (v : Fin d → ℝ) (e : Step d) (t : ℝ) (x : Site d) :
    height (tiltDirection v e t) x = height (stepDirection e) x - t*height v x := by
  simp only [height,tiltDirection,mul_sub,Finset.sum_sub_distrib,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma largeRadius_point {d : ℕ} (v : Fin d → ℝ) (X : Path d) (hX : GoodSlabPath v X)
    (a B : ℝ) (ha : 0 ≤ a) {k : ℕ} (hr : B*a*(k+1) < slabRadius (slabs v X k))
    (hp : slabRadiusSum v X k ≤ a*k) :
    ∃ j : ℕ, j ≤ (slabs v X k).1 ∧ (B-1)*a*(k+1) <
      ‖euclideanSite (X (slabTime v X k+j))‖ := by
  obtain ⟨j,hj,he⟩ := Finset.exists_mem_eq_sup'
    (show (Finset.range ((slabs v X k).1+1)).Nonempty from ⟨0,Finset.mem_range.mpr (Nat.succ_pos _)⟩)
    (fun j => ‖euclideanSite (wordPath (slabs v X k) j - wordPath (slabs v X k) 0)‖)
  have hj' : j ≤ (slabs v X k).1 := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hj
  change slabRadius (slabs v X k) = _ at he
  have hh := iterated_cutSuffix v X hX.1 k j
  rw [← slab_word_path v X k hj'] at hh
  have he' : ‖euclideanSite (wordPath (slabs v X k) j - wordPath (slabs v X k) 0)‖ ≤
      ‖euclideanSite (X (slabTime v X k+j))‖ + ‖euclideanSite (X (slabTime v X k))‖ := by
    rw [(hX.2 k).2.1,sub_zero,hh,euclideanSite_sub]
    exact norm_sub_le _ _
  have hb := (norm_at_slabTime_le v X hX k).trans hp
  refine ⟨j,hj',?_⟩
  rw [he] at hr
  nlinarith

def radiusLaunch {d : ℕ} (v : Fin d → ℝ) (e : Step d) (t L U : ℝ)
    (X : Path d) (n : ℕ) : Prop :=
  strictRecord (tiltDirection v e t) X n ∧
  (∀ j ≤ n, 0 ≤ height v (X j)) ∧
  (∃ j ≤ n, L ≤ height v (X j)) ∧
  (∀ j ≤ n, height v (X j) ≤ U)

lemma measurableSet_radiusLaunch {d : ℕ} (v : Fin d → ℝ) (e : Step d)
    (t L U : ℝ) (n : ℕ) : MeasurableSet {X : Path d | radiusLaunch v e t L U X n} := by
  unfold radiusLaunch
  simp only [Set.ofPred_and, Set.ofPred_forall, Set.ofPred_exists]
  apply (measurableSet_strictRecord _ _).inter
  apply MeasurableSet.inter
  · exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      measurableSet_le measurable_const ((measurable_of_countable (height v)).comp (measurable_pi_apply j))
  apply MeasurableSet.inter
  · exact MeasurableSet.iUnion fun j => MeasurableSet.inter (MeasurableSet.const _) <|
      measurableSet_le measurable_const ((measurable_of_countable (height v)).comp (measurable_pi_apply j))
  · exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      measurableSet_le ((measurable_of_countable (height v)).comp (measurable_pi_apply j)) measurable_const

lemma radiusLaunch_prefix {d : ℕ} (v : Fin d → ℝ) (e : Step d) (t L U : ℝ)
    {X Y : Path d} {n : ℕ} (hX : radiusLaunch v e t L U X n)
    (hY : Y ∈ pathCylinder n X) : radiusLaunch v e t L U Y n := by
  rcases hX with ⟨hr,hp,⟨j,hj,hL⟩,hu⟩
  exact ⟨strictRecord_prefix _ hr hY, fun i hi => (hY i hi).symm ▸ hp i hi,
    ⟨j,hj,(hY j hj).symm ▸ hL⟩,fun i hi => (hY i hi).symm ▸ hu i hi⟩

lemma first_crossing_strictRecord {d : ℕ} (w : Fin d → ℝ) (X : Path d)
    (A : ℝ) {m t : ℕ} (hm : ∀ j ≤ m, height w (X j) ≤ A)
    (ht : A < height w (X t)) :
    ∃ n, m < n ∧ n ≤ t ∧ strictRecord w X n := by
  let n := Nat.find (show ∃ j, A < height w (X j) from ⟨t,ht⟩)
  have hn : A < height w (X n) := Nat.find_spec (show ∃ j, A < height w (X j) from ⟨t,ht⟩)
  have hmn : m < n := by
    by_contra h
    exact (not_lt_of_ge (hm n (by omega))) hn
  refine ⟨n,hmn,Nat.find_min' _ ht,?_,?_⟩
  · omega
  · intro j hj
    exact (le_of_not_gt (Nat.find_min (show ∃ j, A < height w (X j) from ⟨t,ht⟩) hj)).trans_lt hn

lemma largeRadius_launch {d : ℕ} (v : Fin d → ℝ) (X : Path d)
    (hX : GoodSlabPath v X) (a B β K L U : ℝ) (ha : 0 < a) (hβ : 0 ≤ β)
    (hK : 0 ≤ K) (hB : Real.sqrt d*(2+β*K) < B-1) {k : ℕ}
    (hr : B*a*(k+1) < slabRadius (slabs v X k))
    (hp : slabRadiusSum v X k ≤ a*k)
    (hH : slabHeightSum v X (k+1) ≤ K*(k+1))
    (hL : L ≤ slabHeightSum v X k) (hU : K*(k+1) ≤ U) :
    ∃ e : Step d, ∃ n, radiusLaunch v e (β*a) L U X n := by
  obtain ⟨j,hj,hbig⟩ := largeRadius_point v X hX a B ha.le hr hp
  let t := slabTime v X k+j
  have ht : t ≤ slabTime v X (k+1) := by rw [slabTime_succ]; omega
  have hk : (0 : ℝ) < k+1 := by positivity
  have hb : Real.sqrt d*((2+β*K)*a*(k+1)) < ‖euclideanSite (X t)‖ := by
    have h := mul_lt_mul_of_pos_right hB (mul_pos ha hk)
    calc
      _ = (Real.sqrt d*(2+β*K))*(a*(k+1)) := by ring
      _ < (B-1)*(a*(k+1)) := h
      _ < _ := by simpa only [mul_assoc] using hbig
  obtain ⟨e,he⟩ := exists_large_signedCoordinate (X t) (by positivity) hb
  have hy : a*k < height (tiltDirection v e (β*a)) (X t) := by
    rw [height_tiltDirection]
    have hheight := (height_before_slabTime_le v X hX ht).trans hH
    have hmul := mul_le_mul_of_nonneg_left hheight (mul_nonneg hβ ha.le)
    have hak : a*(k:ℝ) < 2*a*(k+1) := by nlinarith
    nlinarith
  have hold (l : ℕ) (hl : l ≤ slabTime v X k) :
      height (tiltDirection v e (β*a)) (X l) ≤ a*k := by
    rw [height_tiltDirection]
    have hc := (le_abs_self (height (stepDirection e) (X l))).trans
      ((height_stepDirection_le_norm e _).trans ((norm_before_slabTime_le v X hX hl).trans hp))
    have hm := mul_nonneg (mul_nonneg hβ ha.le) (goodSlabPath_height_nonneg v X hX l)
    linarith
  obtain ⟨n,hn,hnt,hrec⟩ := first_crossing_strictRecord _ X (a*k) hold hy
  refine ⟨e,n,hrec,fun i _ => goodSlabPath_height_nonneg v X hX i,?_,?_⟩
  · exact ⟨slabTime v X k,hn.le,by rw [height_at_slabTime v X hX.1]; exact hL⟩
  · intro i hi
    exact (height_before_slabTime_le v X hX (hi.trans (hnt.trans ht))).trans (hH.trans hU)

lemma height_signed_step_abs_le_one {d : ℕ} (u e : Step d) :
    |height (stepDirection u) (stepVector e)| ≤ 1 := by
  rw [height_stepDirection]
  cases u.2 <;> simp [stepVector] <;> split_ifs <;> norm_num

lemma tilt_down_step_lower {d : ℕ} (v : Fin d → ℝ) (u e : Step d)
    (t : ℝ) (he : height v (stepVector e) = -1) :
    t-1 ≤ height (tiltDirection v u t) (stepVector e) := by
  rw [height_tiltDirection,he]
  have hh := (abs_le.mp (height_signed_step_abs_le_one u e)).1
  linarith

lemma radius_script_fresh {d : ℕ} (v : Fin d → ℝ) (u e : Step d)
    (t : ℝ) (ht : 1 < t) (he : height v (stepVector e) = -1)
    (γ : Path d) {n : ℕ} (hr : strictRecord (tiltDirection v u t) γ n) :
    ∀ i < n, ∀ j : ℕ, γ i ≠ axialRay (γ n) e j := by
  intro i hi j hj
  have h := hr.2 i hi
  rw [hj,height_axialRay] at h
  have hs := tilt_down_step_lower v u e t he
  have hp : 0 ≤ (j : ℝ)*height (tiltDirection v u t) (stepVector e) :=
    mul_nonneg (Nat.cast_nonneg _) (by linarith)
  linarith

lemma opposite_template_height {d : ℕ} (v : Fin d → ℝ) (Z : Path d)
    (hZ : GoodSlabPath (-v) Z) (t : ℕ) : height v (Z t) ≤ 0 := by
  have hh := goodSlabPath_height_nonneg (-v) Z hZ t
  rw [height_neg_direction] at hh
  linarith

lemma radius_template_before {d : ℕ} (v : Fin d → ℝ) (u e : Step d)
    (a β c C b : ℝ) (ha : 0 ≤ a) (hβ : 0 ≤ β) (hbc : 1 ≤ β*c)
    (he : height v (stepVector e) = -1) (M q : ℕ)
    (hM : (M : ℝ) < a*(M*β-1-β*b)) (x : Site d) (Z : Path d)
    (hZ : GoodSlabPath (-v) Z) (hgood : Z ∈ goodRadiusPrefix (-v) a c C b q)
    {t : ℕ} (ht : t < slabTime (-v) Z q) :
    height (tiltDirection v u (β*a)) x <
      height (tiltDirection v u (β*a)) (Z t + axialRay x e M) := by
  obtain ⟨k,hkt,htk⟩ := slab_location (-v) Z hZ t
  have hkq : k < q := (slabTime_strictMono (-v) Z hZ).lt_iff_lt.mp (hkt.trans_lt ht)
  have hnorm := norm_before_slabTime_le (-v) Z hZ htk.le
  have hgood' := (goodRadiusPrefix_iff (-v) a c C b q Z).mp hgood
  have hnorm' := hnorm.trans (hgood' (k+1) (by omega)).2.2
  have hlow := (hgood' k hkq.le).1.trans (height_after_slabTime_le (-v) Z hZ hkt)
  rw [height_neg_direction] at hlow
  have hu := (abs_le.mp (height_stepDirection_le_norm u (Z t))).1
  have hdown := tilt_down_step_lower v u e (β*a) he
  rw [height_add,height_axialRay,height_tiltDirection v u (β*a) (Z t)]
  simp only [Nat.cast_add,Nat.cast_one] at hnorm'
  have hmm := mul_le_mul_of_nonneg_left hdown (Nat.cast_nonneg M : (0:ℝ) ≤ M)
  have hhh := mul_le_mul_of_nonneg_left hlow (mul_nonneg hβ ha)
  have hkk := mul_nonneg (show (0:ℝ) ≤ k by positivity) (sub_nonneg.mpr hbc)
  have hkk' := mul_nonneg ha hkk
  nlinarith

lemma radius_template_avoids {d : ℕ} (v : Fin d → ℝ) (u e : Step d)
    (a β c C b U : ℝ) (ha : 0 ≤ a) (hβ : 0 ≤ β) (hbc : 1 ≤ β*c)
    (he : height v (stepVector e) = -1) (M q : ℕ)
    (hM : (M : ℝ) < a*(M*β-1-β*b)) (hq : U-M-c*q+b < 0)
    (γ : Path d) {n : ℕ} (hr : strictRecord (tiltDirection v u (β*a)) γ n)
    (hnonneg : ∀ i ≤ n, 0 ≤ height v (γ i)) (hU : height v (γ n) ≤ U)
    (Z : Path d) (hZ : GoodSlabPath (-v) Z)
    (hgood : Z ∈ goodRadiusPrefix (-v) a c C b q) :
    ∀ i < n+M, ∀ t, Z t + axialRay (γ n) e M ≠
      concatPath n γ (axialRay (γ n) e) i := by
  intro i hi t heq
  by_cases hin : i < n
  · rw [concatPath_before n γ (axialRay (γ n) e) (axialRay_zero _ _).symm hin.le] at heq
    by_cases ht : t < slabTime (-v) Z q
    · have hh := radius_template_before v u e a β c C b ha hβ hbc he M q hM (γ n) Z hZ hgood ht
      rw [heq] at hh
      exact (not_lt_of_ge (hr.2 i hin).le) hh
    · have hh := height_after_slabTime_le (-v) Z hZ (le_of_not_gt ht)
      have hl := ((goodRadiusPrefix_iff (-v) a c C b q Z).mp hgood q le_rfl).1.trans hh
      rw [height_neg_direction] at hl
      have hheight := congrArg (height v) heq
      rw [height_add,height_axialRay,he] at hheight
      have hn := hnonneg i hin.le
      nlinarith
  · have hscript : concatPath n γ (axialRay (γ n) e) i = axialRay (γ n) e (i-n) := by
      simpa only [Nat.add_sub_of_le (le_of_not_gt hin)] using
        concatPath_after n γ (axialRay (γ n) e) (i-n)
    rw [hscript] at heq
    have hh := congrArg (height v) heq
    rw [height_add,height_axialRay,height_axialRay,he] at hh
    have hn := opposite_template_height v Z hZ t
    have hj : ((i-n : ℕ) : ℝ) < M := by exact_mod_cast (show i-n < M by omega)
    nlinarith

lemma radius_continuation_maximum {d : ℕ} (v : Fin d → ℝ) (e : Step d)
    (he : height v (stepVector e) = -1) (γ Y Z : Path d) (n M : ℕ)
    (hprefix : Y ∈ pathCylinder (n+M) (concatPath n γ (axialRay (γ n) e)))
    (htail : tailPath (n+M) Y = shiftPath (axialRay (γ n) e M) Z)
    (hZ : GoodSlabPath (-v) Z) (U : ℝ) (hU : ∀ i ≤ n, height v (γ i) ≤ U) :
    Y ∈ alwaysBelow v U := by
  intro t
  by_cases ht : t < n
  · rw [hprefix t (by omega),concatPath_before n γ (axialRay (γ n) e)
      (axialRay_zero _ _).symm ht.le]
    exact hU t ht.le
  · by_cases htM : t < n+M
    · rw [hprefix t htM.le]
      have hscript : concatPath n γ (axialRay (γ n) e) t = axialRay (γ n) e (t-n) := by
        simpa only [Nat.add_sub_of_le (le_of_not_gt ht)] using
          concatPath_after n γ (axialRay (γ n) e) (t-n)
      rw [hscript,height_axialRay,he]
      have hn := hU n le_rfl
      have hj : (0:ℝ) ≤ (t-n:ℕ) := by positivity
      linarith
    · have hh := congr_fun htail (t-(n+M))
      change Y ((n+M)+(t-(n+M))) = Z (t-(n+M))+axialRay (γ n) e M at hh
      rw [Nat.add_sub_of_le (le_of_not_gt htM)] at hh
      rw [hh,height_add,height_axialRay,he]
      have hz := opposite_template_height v Z hZ (t-(n+M))
      have hn := hU n le_rfl
      have hm : (0:ℝ) ≤ M := by positivity
      linarith

lemma measure_prefix_lower {d : ℕ} (P : Measure (Path d)) (n : ℕ)
    {Q E : Set (Path d)} (hQ : MeasurableSet Q) (hE : MeasurableSet E)
    (hpre : ∀ X ∈ Q, pathCylinder n X ⊆ Q) (q : ℝ≥0∞)
    (hbound : ∀ X ∈ Q, q*P (pathCylinder n X) ≤ P (pathCylinder n X ∩ E)) :
    q*P Q ≤ P (Q ∩ E) := by
  rw [measure_eq_tsum_fibres P (frestrictLe n) (measurable_frestrictLe n) hQ,
    measure_eq_tsum_fibres P (frestrictLe n) (measurable_frestrictLe n) (hQ.inter hE),
    ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro a
  let γ := extendPrefix n a
  have hcyl : {X : Path d | frestrictLe n X = a} = pathCylinder n γ := by
    rw [pathCylinder_eq_fiber,restrict_extendPrefix]
    rfl
  rw [hcyl,← Set.inter_assoc]
  by_cases hg : γ ∈ Q
  · rw [Set.inter_eq_left.mpr (hpre γ hg)]
    exact hbound γ hg
  · have hempty : pathCylinder n γ ∩ Q = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro X ⟨hX,hXQ⟩
      exact hg (hpre X hXQ (fun i hi => (hX i hi).symm))
    rw [hempty,measure_empty,Set.empty_inter,measure_empty,mul_zero]

lemma measure_first_prefix_lower {d : ℕ} (P : Measure (Path d))
    (F : Path d → ℕ → Prop) (hF : ∀ n, MeasurableSet {X | F X n})
    (hpre : ∀ X n, F X n → ∀ Y ∈ pathCylinder n X, F Y n)
    {E : Set (Path d)} (hE : MeasurableSet E) (q : ℝ≥0∞)
    (hbound : ∀ X n, F X n → q*P (pathCylinder n X) ≤ P (pathCylinder n X ∩ E)) :
    q*P {X | ∃ n, F X n} ≤ P E := by
  let Q (n : ℕ) : Set (Path d) := {X | F X n ∧ ∀ j < n, ¬F X j}
  have hQ (n : ℕ) : MeasurableSet (Q n) := by
    simp only [Q,Set.ofPred_and,Set.ofPred_forall]
    exact (hF n).inter (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => (hF j).compl)
  have hQpre (n : ℕ) (X : Path d) (hX : X ∈ Q n) : pathCylinder n X ⊆ Q n := by
    intro Y hY
    refine ⟨hpre X n hX.1 Y hY,fun j hj hfj => hX.2 j hj ?_⟩
    exact hpre Y j hfj X (fun i hi => (hY i (hi.trans hj.le)).symm)
  have hQD : Pairwise (fun m n => Disjoint (Q m) (Q n)) := by
    intro m n hmn
    apply Set.disjoint_left.mpr
    intro X hm hn
    rcases lt_or_gt_of_ne hmn with h | h
    · exact hn.2 m h hm.1
    · exact hm.2 n h hn.1
  have heq : {X | ∃ n, F X n} = ⋃ n, Q n := by
    ext X
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion]
    constructor
    · intro h
      exact ⟨Nat.find h,Nat.find_spec h,fun j hj => Nat.find_min h hj⟩
    · rintro ⟨n,h⟩;exact ⟨n,h.1⟩
  rw [heq,measure_iUnion hQD hQ,← ENNReal.tsum_mul_left]
  calc
    _ ≤ ∑' n, P (Q n ∩ E) := ENNReal.tsum_le_tsum fun n =>
      measure_prefix_lower P n (hQ n) hE (hQpre n) q (fun X hX => hbound X n hX.1)
    _ = P (⋃ n, Q n ∩ E) := (measure_iUnion
      (fun m n hmn => (hQD hmn).mono Set.inter_subset_left Set.inter_subset_left)
      (fun n => (hQ n).inter hE)).symm
    _ ≤ P E := measure_mono (Set.iUnion_subset fun _ => Set.inter_subset_right)

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

def finiteHighMaximum {d : ℕ} (v : Fin d → ℝ) (L : ℝ) : Set (Path d) :=
  {X | (∃ b : ℕ, ∀ n, height v (X n) ≤ b) ∧ ∃ j, L ≤ height v (X j)}

lemma measurableSet_finiteHighMaximum {d : ℕ} (v : Fin d → ℝ) (L : ℝ) :
    MeasurableSet (finiteHighMaximum v L) := by
  simp only [finiteHighMaximum,Set.ofPred_and,Set.ofPred_exists]
  exact (MeasurableSet.iUnion fun b : ℕ => measurableSet_alwaysBelow v b).inter
    (MeasurableSet.iUnion fun j => measurableSet_le measurable_const
      ((measurable_of_countable (height v)).comp (measurable_pi_apply j)))

lemma finiteHighMaximum_mono {d : ℕ} (v : Fin d → ℝ) {L U : ℝ} (h : L ≤ U) :
    finiteHighMaximum v U ⊆ finiteHighMaximum v L := by
  rintro X ⟨hb,j,hj⟩
  exact ⟨hb,j,h.trans hj⟩

lemma tendsto_measure_finiteHighMaximum {d : ℕ} (P : Measure (Path d)) [IsFiniteMeasure P]
    (v : Fin d → ℝ) : Tendsto (fun n : ℕ => P (finiteHighMaximum v n)) atTop (𝓝 0) := by
  have hh : (⋂ n : ℕ, finiteHighMaximum v n) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro X hX
    have h := Set.mem_iInter.mp hX
    obtain ⟨b,hb⟩ := (h 0).1
    obtain ⟨j,hj⟩ := (h (b+1)).2
    have hb' := hb j
    have : (b:ℝ)+1 ≤ b := by simpa only [Nat.cast_add,Nat.cast_one] using hj.trans hb'
    linarith
  have hm := tendsto_measure_iInter_atTop
    (fun n : ℕ => (measurableSet_finiteHighMaximum v n).nullMeasurableSet (μ := P))
    (fun m n hmn => finiteHighMaximum_mono v (by exact_mod_cast hmn))
    (show ∃ i : ℕ, P (finiteHighMaximum v i) ≠ ⊤ from ⟨0,measure_ne_top _ _⟩)
  simpa only [hh,measure_empty,Function.comp_def] using hm

lemma measurableSet_goodSlabPath {d : ℕ} (v : Fin d → ℝ) :
    MeasurableSet {X : Path d | GoodSlabPath v X} := by
  simp only [GoodSlabPath,Set.ofPred_and,Set.ofPred_forall]
  exact (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const).inter
    (MeasurableSet.iInter fun k => (Set.to_countable {γ | RegenerationWord v γ}).measurableSet.preimage
      ((measurable_pi_apply k).comp (measurable_slabs v)))

def radiusTemplate {d : ℕ} (v : Fin d → ℝ) (a c C b : ℝ) (q : ℕ) : Set (Path d) :=
  {Z | GoodSlabPath v Z} ∩ goodRadiusPrefix v a c C b q

lemma measurableSet_radiusTemplate {d : ℕ} (v : Fin d → ℝ) (a c C b : ℝ) (q : ℕ) :
    MeasurableSet (radiusTemplate v a c C b q) :=
  (measurableSet_goodSlabPath v).inter (measurableSet_goodRadiusPrefix v a c C b q)

lemma annealed_radiusTemplate {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) (a c C b : ℝ) (q : ℕ) :
    annealed μ 0 (radiusTemplate v a c C b q) = annealed μ 0 (nonBacktracking v) *
      conditioned μ v (goodRadiusPrefix v a c C b q) := by
  have hsub : radiusTemplate v a c C b q ⊆ nonBacktracking v :=
    fun Z hZ t => goodSlabPath_height_nonneg v Z hZ.1 t
  have he : conditioned μ v (radiusTemplate v a c C b q) =
      conditioned μ v (goodRadiusPrefix v a c C b q) := by
    apply measure_congr
    filter_upwards [ae_goodSlabPath μ hell v hv hp] with Z hZ
    exact propext ⟨fun h => h.2, fun h => ⟨hZ, h⟩⟩
  have hh := cond_mul_eq_inter (measurableSet_nonBacktracking v) (radiusTemplate v a c C b q) (annealed μ 0)
  rw [Set.inter_eq_right.mpr hsub] at hh
  change conditioned μ v (radiusTemplate v a c C b q) * _ = _ at hh
  rw [he,mul_comm] at hh
  exact hh.symm

lemma shiftPath_add_neg_cancel {d : ℕ} (x : Site d) (Z : Path d) :
    shiftPath (-x) (shiftPath x Z) = Z := by
  funext t
  simp [shiftPath]

lemma shiftPath_neg_add_cancel {d : ℕ} (x : Site d) (Z : Path d) :
    shiftPath x (shiftPath (-x) Z) = Z := by
  funext t
  simp [shiftPath]

lemma annealed_translated_event {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x : Site d) {E : Set (Path d)} (hE : MeasurableSet E) :
    annealed μ x (shiftPath (-x) ⁻¹' E) = annealed μ 0 E := by
  have hh := congrArg (fun P : Measure (Path d) => P (shiftPath (-x) ⁻¹' E)) (annealed_shift μ 0 x)
  rw [zero_add,Measure.map_apply (measurable_shiftPath x) ((measurable_shiftPath (-x)) hE)] at hh
  have he : shiftPath x ⁻¹' (shiftPath (-x) ⁻¹' E) = E := by
    ext Z
    simp only [Set.mem_preimage,shiftPath_add_neg_cancel]
  rw [he] at hh
  exact hh.symm

lemma radius_launch_cylinder_lower {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (v : Fin d → ℝ) (u e : Step d) (a β c C b L U : ℝ)
    (ha : 0 ≤ a) (hβ : 0 ≤ β) (hbc : 1 ≤ β*c) (hta : 1 < β*a)
    (he : height v (stepVector e) = -1) (M q : ℕ)
    (hM : (M : ℝ) < a*(M*β-1-β*b)) (hq : U-M-c*q+b < 0)
    (γ : Path d) (n : ℕ) (hr : radiusLaunch v u (β*a) L U γ n) :
    (meanStep μ e ^ M * annealed μ 0 (radiusTemplate (-v) a c C b q)) *
      annealed μ 0 (pathCylinder n γ) ≤
      annealed μ 0 (pathCylinder n γ ∩ finiteHighMaximum v L) := by
  let δ := concatPath n γ (axialRay (γ n) e)
  let x := axialRay (γ n) e M
  let F := shiftPath (-x) ⁻¹' radiusTemplate (-v) a c C b q
  let K : Set (Site d) := {y | ∃ i < n+M, δ i = y}
  have hF : MeasurableSet F :=
    (measurable_shiftPath (-x)) (measurableSet_radiusTemplate (-v) a c C b q)
  have hx : δ (n+M) = x := concatPath_after _ _ _ _
  have hFK : F ⊆ avoids K := by
    intro W hW t
    rintro ⟨i,hi,hii⟩
    let Z := shiftPath (-x) W
    have hz : W = shiftPath x Z := (shiftPath_neg_add_cancel x W).symm
    have hZ : Z ∈ radiusTemplate (-v) a c C b q := hW
    have hsep := radius_template_avoids v u e a β c C b U ha hβ hbc he M q hM hq
      γ hr.1 hr.2.1 (hr.2.2.2 n le_rfl) Z hZ.1 hZ.2 i hi t
    apply hsep
    have hwt : W t = Z t+x := congr_fun hz t
    exact hwt.symm.trans hii.symm
  have hraw : annealed μ x F = annealed μ 0 (radiusTemplate (-v) a c C b q) :=
    annealed_translated_event μ x (measurableSet_radiusTemplate (-v) a c C b q)
  have hfac := annealed_fresh_prefix_tail μ K 0 (n+M) δ (fun i hi => ⟨i,hi,rfl⟩) hF
  rw [Set.inter_eq_left.mpr hFK,hx,hraw] at hfac
  have hscript : annealed μ 0 (pathCylinder (n+M) δ) =
      annealed μ 0 (pathCylinder n γ) * meanStep μ e ^ M := by
    have hh := annealed_disjoint_prefix_tail μ 0 n M γ (axialRay (γ n) e)
      (axialRay_zero _ _).symm (fun i hi j _ => radius_script_fresh v u e (β*a) hta he γ hr.1 i hi j)
    rw [prefix_tail_inter,ite_eq_left (axialRay_zero _ _).symm,annealed_axialRay] at hh
    exact hh
  have hsub : pathCylinder (n+M) δ ∩ tailPath (n+M) ⁻¹' F ⊆
      pathCylinder n γ ∩ finiteHighMaximum v L := by
    rintro Y ⟨hY,hT⟩
    let Z := shiftPath (-x) (tailPath (n+M) Y)
    have hZ : Z ∈ radiusTemplate (-v) a c C b q := hT
    have ht : tailPath (n+M) Y = shiftPath x Z :=
      (shiftPath_neg_add_cancel x (tailPath (n+M) Y)).symm
    have hy : Y ∈ pathCylinder n γ := by
      intro i hi
      rw [hY i (by omega)]
      exact concatPath_before _ _ _ (axialRay_zero _ _).symm hi
    refine ⟨hy,?_,?_⟩
    · obtain ⟨b',hb'⟩ := exists_nat_ge U
      exact ⟨b',fun i => (radius_continuation_maximum v e he γ Y Z n M hY ht hZ.1 U hr.2.2.2 i).trans hb'⟩
    · obtain ⟨j,hj,hjl⟩ := hr.2.2.1
      exact ⟨j,by rw [hy j hj];exact hjl⟩
  have hm := measure_mono (μ := annealed μ 0) hsub
  rw [hfac,hscript] at hm
  convert hm using 1; ac_rfl

lemma radius_launch_probability_lower {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (v : Fin d → ℝ) (u e : Step d) (a β c C b L U : ℝ)
    (ha : 0 ≤ a) (hβ : 0 ≤ β) (hbc : 1 ≤ β*c) (hta : 1 < β*a)
    (he : height v (stepVector e) = -1) (M q : ℕ)
    (hM : (M : ℝ) < a*(M*β-1-β*b)) (hq : U-M-c*q+b < 0) :
    (meanStep μ e ^ M * annealed μ 0 (radiusTemplate (-v) a c C b q)) *
      annealed μ 0 {X | ∃ n, radiusLaunch v u (β*a) L U X n} ≤
      annealed μ 0 (finiteHighMaximum v L) :=
  measure_first_prefix_lower (annealed μ 0) (radiusLaunch v u (β*a) L U)
    (measurableSet_radiusLaunch v u (β*a) L U)
    (fun _ _ h _ hY => radiusLaunch_prefix v u (β*a) L U h hY)
    (measurableSet_finiteHighMaximum v L) _
    (radius_launch_cylinder_lower μ v u e a β c C b L U ha hβ hbc hta he M q hM hq)

lemma controlledSlabOccurrence_launch {d : ℕ} (v : Fin d → ℝ) (X : Path d)
    (hX : GoodSlabPath v X) (a B β c C b L : ℝ) (ha : 0 < a) (hβ : 0 ≤ β)
    (hc : 0 ≤ c) (hC : 0 ≤ C) (hB : Real.sqrt d*(2+β*(C+2)) < B-1)
    (l N : ℕ) (hl : b ≤ l+1) (hL : L ≤ c*l-b)
    (hocc : X ∈ controlledSlabOccurrence v a c C b
      (largeRadiusWord slabRadius (slabWidth v) (B*a)) (Finset.Ico l N)) :
    ∃ e : Step d, ∃ n, radiusLaunch v e (β*a) L ((C+2)*N) X n := by
  obtain ⟨k,hk,hgp,hbig⟩ := Set.mem_iUnion₂.mp hocc
  have hki := Finset.mem_Ico.mp hk
  have hg := (goodRadiusPrefix_iff v a c C b k X).mp hgp k le_rfl
  have hwidth : slabWidth v (slabs v X k) ≤ k+1 := hbig.2
  apply largeRadius_launch v X hX a B β (C+2) L ((C+2)*N) ha hβ (by linarith) hB hbig.1 hg.2.2
  · have hb : b ≤ (k : ℝ)+1 := hl.trans (by exact_mod_cast Nat.add_le_add_right hki.1 1)
    rw [slabHeightSum,Finset.sum_range_succ]
    change slabHeightSum v X k + slabWidth v (slabs v X k) ≤ _
    nlinarith [hg.2.1]
  · exact hL.trans ((sub_le_sub_right (mul_le_mul_of_nonneg_left
      (Nat.cast_le.mpr hki.1) hc) b).trans hg.1)
  · exact mul_le_mul_of_nonneg_left (by exact_mod_cast (show k+1 ≤ N by omega)) (by linarith)

lemma annealed_goodSlabPath_event {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) (E : Set (Path d)) :
    annealed μ 0 ({X | GoodSlabPath v X} ∩ E) =
      annealed μ 0 (nonBacktracking v) * conditioned μ v E := by
  have hsub : {X | GoodSlabPath v X} ∩ E ⊆ nonBacktracking v :=
    fun X hX t => goodSlabPath_height_nonneg v X hX.1 t
  have he : conditioned μ v ({X | GoodSlabPath v X} ∩ E) = conditioned μ v E := by
    apply measure_congr
    filter_upwards [ae_goodSlabPath μ hell v hv hp] with X hX
    exact propext ⟨fun h => h.2,fun h => ⟨hX,h⟩⟩
  have hh := cond_mul_eq_inter (measurableSet_nonBacktracking v)
    ({X | GoodSlabPath v X} ∩ E) (annealed μ 0)
  rw [Set.inter_eq_right.mpr hsub] at hh
  change conditioned μ v ({X | GoodSlabPath v X} ∩ E) * _ = _ at hh
  rw [he,mul_comm] at hh
  exact hh.symm

lemma radius_occurrence_probability_upper {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) (e : Step d)
    (a B β c C b L : ℝ) (ha : 0 < a) (hβ : 0 ≤ β) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hB : Real.sqrt d*(2+β*(C+2)) < B-1)
    (hbc : 1 ≤ β*c) (hta : 1 < β*a) (he : height v (stepVector e) = -1)
    (M q l N : ℕ) (hM : (M : ℝ) < a*(M*β-1-β*b))
    (hq : (C+2)*N-M-c*q+b < 0) (hl : b ≤ l+1) (hL : L ≤ c*l-b) :
    ((meanStep μ e ^ M * annealed μ 0 (radiusTemplate (-v) a c C b q)).toReal *
      (annealed μ 0).real (nonBacktracking v)) *
      (conditioned μ v).real (controlledSlabOccurrence v a c C b
        (largeRadiusWord slabRadius (slabWidth v) (B*a)) (Finset.Ico l N)) ≤
      (Fintype.card (Step d) : ℝ) * (annealed μ 0).real (finiteHighMaximum v L) := by
  let A := controlledSlabOccurrence v a c C b
    (largeRadiusWord slabRadius (slabWidth v) (B*a)) (Finset.Ico l N)
  let E (u : Step d) : Set (Path d) := {X | ∃ n, radiusLaunch v u (β*a) L ((C+2)*N) X n}
  let κ := meanStep μ e ^ M * annealed μ 0 (radiusTemplate (-v) a c C b q)
  have hsub : {X | GoodSlabPath v X} ∩ A ⊆ ⋃ u : Step d, E u := by
    intro X hX
    obtain ⟨u,n,hn⟩ := controlledSlabOccurrence_launch v X hX.1 a B β c C b L ha hβ hc hC hB l N hl hL hX.2
    exact Set.mem_iUnion.mpr ⟨u,n,hn⟩
  have hmass := (measureReal_mono (μ := annealed μ 0) hsub (measure_ne_top _ _)).trans
    (measureReal_iUnion_fintype_le (μ := annealed μ 0) E)
  have heq : (annealed μ 0).real ({X | GoodSlabPath v X} ∩ A) =
      (annealed μ 0).real (nonBacktracking v) * (conditioned μ v).real A := by
    exact (congrArg ENNReal.toReal (annealed_goodSlabPath_event μ hell v hv hp A)).trans ENNReal.toReal_mul
  rw [heq] at hmass
  have hu (u : Step d) : κ.toReal * (annealed μ 0).real (E u) ≤
      (annealed μ 0).real (finiteHighMaximum v L) := by
    have hh := radius_launch_probability_lower μ v u e a β c C b L ((C+2)*N)
      ha.le hβ hbc hta he M q hM hq
    have hh' := ENNReal.toReal_mono (measure_ne_top (annealed μ 0) _) hh
    simpa only [κ,E,Measure.real,ENNReal.toReal_mul] using hh'
  calc
    _ = κ.toReal*((annealed μ 0).real (nonBacktracking v)*(conditioned μ v).real A) := by ring
    _ ≤ κ.toReal * ∑ u : Step d, (annealed μ 0).real (E u) := mul_le_mul_of_nonneg_left hmass ENNReal.toReal_nonneg
    _ = ∑ u : Step d, κ.toReal * (annealed μ 0).real (E u) := Finset.mul_sum _ _ _
    _ ≤ ∑ _u : Step d, (annealed μ 0).real (finiteHighMaximum v L) := Finset.sum_le_sum (fun u _ => hu u)
    _ = _ := by simp

lemma radius_occurrence_mass_le {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v))
    (hp' : 0 < annealed μ 0 (nonBacktracking (-v))) (e : Step d)
    (a B β c C b L : ℝ) (ha : 0 < a) (hβ : 0 ≤ β) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hB : Real.sqrt d*(2+β*(C+2)) < B-1)
    (hbc : 1 ≤ β*c) (hta : 1 < β*a) (he : height v (stepVector e) = -1)
    (M q l N : ℕ) (hM : (M : ℝ) < a*(M*β-1-β*b))
    (hq : (C+2)*N-M-c*q+b < 0) (hl : b ≤ l+1) (hL : L ≤ c*l-b)
    (hgp : ∀ i ∈ Finset.Ico l N, (3:ℝ)/4 ≤
      (conditioned μ v).real (goodRadiusPrefix v a c C b i))
    (htp : (3:ℝ)/4 ≤ (conditioned μ (-v)).real (goodRadiusPrefix (-v) a c C b q))
    (hs : (∑ i ∈ Finset.Ico l N, (slabLaw μ v).real
      (largeRadiusWord slabRadius (slabWidth v) (B*a) i)) ≤ 1/4) :
    ((meanStep μ e ^ M).toReal * (annealed μ 0).real (nonBacktracking v) *
      (annealed μ 0).real (nonBacktracking (-v)) * (3/8)) *
      (∑ i ∈ Finset.Ico l N, (slabLaw μ v).real
        (largeRadiusWord slabRadius (slabWidth v) (B*a) i)) ≤
      (Fintype.card (Step d) : ℝ) * (annealed μ 0).real (finiteHighMaximum v L) := by
  have hh := radius_occurrence_probability_upper μ hell v hv hp e a B β c C b L
    ha hβ hc hC hB hbc hta he M q l N hM hq hl hL
  have ht := congrArg ENNReal.toReal (annealed_radiusTemplate μ hell (-v) (neg_ne_zero.mpr hv) hp' a c C b q)
  rw [ENNReal.toReal_mul] at ht
  have ho := controlledSlabOccurrence_probability_half μ hell v hv hp a c C b
    (largeRadiusWord slabRadius (slabWidth v) (B*a)) (Finset.Ico l N) hgp hs
  rw [ENNReal.toReal_mul,ht] at hh
  have hn : 0 ≤ ∑ i ∈ Finset.Ico l N, (slabLaw μ v).real
      (largeRadiusWord slabRadius (slabWidth v) (B*a) i) :=
    Finset.sum_nonneg (fun _ _ => measureReal_nonneg)
  have hcoef : 0 ≤ (meanStep μ e ^ M).toReal * (annealed μ 0).real (nonBacktracking (-v)) *
      (annealed μ 0).real (nonBacktracking v) := by positivity
  have hmul := mul_le_mul_of_nonneg_left (mul_le_mul htp ho (by positivity) measureReal_nonneg) hcoef
  calc
    _ = ((meanStep μ e ^ M).toReal * (annealed μ 0).real (nonBacktracking (-v)) *
      (annealed μ 0).real (nonBacktracking v)) * ((3/4)*
      ((∑ i ∈ Finset.Ico l N, (slabLaw μ v).real
        (largeRadiusWord slabRadius (slabWidth v) (B*a) i))/2)) := by ring
    _ ≤ _ := hmul
    _ = _ := by unfold Measure.real; ring
    _ ≤ _ := hh

lemma goodRadiusPrefix_uniform_probability {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) (a c C b : ℝ) (ha : 0 < a)
    (n : ℕ) (hn : 0 < n)
    (hheight : (15:ℝ)/16 ≤ (conditioned μ v).real
      (heightEnvelope (fun k X => slabHeightSum v X k) c C b))
    (htrunc : truncatedMoment (slabLaw μ v) slabRadius (a*n) ≤ 3*a/32) :
    ∀ i ≤ n, (3:ℝ)/4 ≤ (conditioned μ v).real (goodRadiusPrefix v a c C b i) := by
  let := conditioned_probability μ v hp
  have hh := goodRadiusPrefix_probability μ hell v hv hp a c C b ha n hn
  have hb : 2*truncatedMoment (slabLaw μ v) slabRadius (a*n)/a ≤ 3/16 := by
    apply (div_le_iff₀ ha).mpr
    linarith
  intro i hi
  exact (show (3:ℝ)/4 ≤ (conditioned μ v).real (goodRadiusPrefix v a c C b n) by linarith).trans
    (measureReal_mono (goodRadiusPrefix_mono v a c C b hi) (measure_ne_top _ _))

lemma summable_real_upper_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → ℝ) (hfm : Measurable f)
    (hfi : Integrable f P) : Summable (fun n : ℕ => P.real {x | (n+1 : ℝ) < f x}) := by
  apply Summable.of_nonneg_of_le (fun _ => measureReal_nonneg) (fun n =>
    measureReal_mono (fun x hx => hx.trans_le (le_abs_self (f x))) (measure_ne_top _ _))
  exact summable_real_tail_of_integrable P (fun x => |f x|) hfm.abs (fun _ => abs_nonneg _) hfi.abs

lemma summable_small_Ico (f : ℕ → ℝ) (hf : Summable f) (hn : ∀ i, 0 ≤ f i)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ l : ℕ in atTop, ∀ n, l ≤ n → ∑ i ∈ Finset.Ico l n, f i < ε := by
  have ht : Tendsto (fun l : ℕ => (∑' i, f i) - ∑ i ∈ Finset.range l, f i) atTop (𝓝 0) := by
    have hh : Tendsto (fun _ : ℕ => ∑' i, f i) atTop (𝓝 (∑' i, f i)) := tendsto_const_nhds
    simpa only [sub_self] using hh.sub hf.hasSum.tendsto_sum_nat
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with l hl n hln
  rw [Finset.sum_Ico_eq_sub f hln]
  exact (sub_le_sub_right (hf.sum_le_tsum (Finset.range n) (fun _ _ => hn _)) _).trans_lt hl

lemma measurable_slabHeightSum {d : ℕ} (v : Fin d → ℝ) (k : ℕ) :
    Measurable (fun X : Path d => slabHeightSum v X k) := by
  apply Finset.measurable_sum
  intro i hi
  exact (measurable_of_countable (slabWidth v)).comp
    ((measurable_pi_apply i).comp (measurable_slabs v))

lemma exists_common_heightEnvelope {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hvnorm : ∀ i, |v i| ≤ 1) (hp : 0 < annealed μ 0 (nonBacktracking v))
    (hp' : 0 < annealed μ 0 (nonBacktracking (-v))) :
    ∃ c C b : ℝ, 0 < c ∧ 0 ≤ C ∧ 0 ≤ b ∧
      (15:ℝ)/16 ≤ (conditioned μ v).real
        (heightEnvelope (fun k X => slabHeightSum v X k) c C b) ∧
      (15:ℝ)/16 ≤ (conditioned μ (-v)).real
        (heightEnvelope (fun k X => slabHeightSum (-v) X k) c C b) := by
  let := conditioned_probability μ v hp
  let := conditioned_probability μ (-v) hp'
  have hv' : -v ≠ 0 := neg_ne_zero.mpr hv
  have hvnorm' : ∀ i, |(-v) i| ≤ 1 := by simpa only [Pi.neg_apply,abs_neg] using hvnorm
  let m := ∫ γ, slabWidth v γ ∂slabLaw μ v
  let m' := ∫ γ, slabWidth (-v) γ ∂slabLaw μ (-v)
  have hm : 0 < m := integral_slabWidth_pos μ hell v hv hvnorm hp
  have hm' : 0 < m' := integral_slabWidth_pos μ hell (-v) hv' hvnorm' hp'
  let c := min m m'/2
  let C := m+m'+1
  have hc : 0 < c := half_pos (lt_min hm hm')
  have hcm : c < m := (half_lt_self (lt_min hm hm')).trans_le (min_le_left _ _)
  have hcm' : c < m' := (half_lt_self (lt_min hm hm')).trans_le (min_le_right _ _)
  obtain ⟨b,hb,hbe⟩ := exists_heightEnvelope_probability (conditioned μ v)
    (fun k X => slabHeightSum v X k) (measurable_slabHeightSum v)
    (slabWidth_strongLaw μ hell v hv hvnorm hp) hcm (show m < C by dsimp [C]; linarith)
    (by norm_num : (15:ℝ)/16 < 1)
  obtain ⟨b',hb',hbe'⟩ := exists_heightEnvelope_probability (conditioned μ (-v))
    (fun k X => slabHeightSum (-v) X k) (measurable_slabHeightSum (-v))
    (slabWidth_strongLaw μ hell (-v) hv' hvnorm' hp') hcm' (show m' < C by dsimp [C]; linarith)
    (by norm_num : (15:ℝ)/16 < 1)
  refine ⟨c,C,max b b',hc,by dsimp [C]; linarith,hb.trans (le_max_left _ _),?_,?_⟩
  · exact hbe.le.trans (measureReal_mono (heightEnvelope_mono _ c C (le_max_left _ _)) (measure_ne_top _ _))
  · exact hbe'.le.trans (measureReal_mono (heightEnvelope_mono _ c C (le_max_right _ _)) (measure_ne_top _ _))

lemma truncatedMoment_component_scale {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (f : Ω → ℝ) (hfm : Measurable f) (hf : ∀ x, 0 ≤ f x)
    {a : ℝ} (ha : 0 < a) (r n : ℕ) (hr : 1 ≤ r)
    (hs : truncatedMoment (P+Q) f (a*n) < a/(32*r)) :
    truncatedMoment P f (a*(r*n)) ≤ 3*a/32 := by
  have hnon := truncatedMoment_nonneg Q f (fun x => hf x) (t := a*(r*n)) (by positivity)
  have hadd := truncatedMoment_add_measure P Q f hfm hf (t := a*(r*n)) (by positivity)
  have ht := truncatedMoment_mul_le (P+Q) f hfm hf (t := a*n) (by positivity)
    (show (1:ℝ) ≤ r by exact_mod_cast hr)
  have hmul := mul_lt_mul_of_pos_left hs (show (0:ℝ) < r by exact_mod_cast (by omega : 0 < r))
  have he : (r : ℝ)*(a/(32*r)) = a/32 := by
    have hr0 : (r:ℝ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
    field_simp
  rw [he] at hmul
  have he' : (r:ℝ)*(a*n) = a*(r*n) := by ring
  rw [he'] at ht
  linarith

lemma tendsto_real_finiteHighMaximum {d : ℕ} (P : Measure (Path d)) [IsFiniteMeasure P]
    (v : Fin d → ℝ) : Tendsto (fun n : ℕ => P.real (finiteHighMaximum v n)) atTop (𝓝 0) := by
  simpa only [Function.comp_def,Measure.real,ENNReal.toReal_zero] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (tendsto_measure_finiteHighMaximum P v)

lemma meanStep_power_real_pos {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d) (M : ℕ) : 0 < (meanStep μ e ^ M).toReal :=
  ENNReal.toReal_pos (pow_ne_zero _ (ne_of_gt (meanStep_pos μ hell e)))
    (ne_of_lt (lt_of_le_of_lt (pow_le_one₀ zero_le (meanStep_le_one μ e)) ENNReal.one_lt_top))

lemma integrable_radius_from_parameters {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hvnorm : ∀ i, |v i| ≤ 1) (hp : 0 < annealed μ 0 (nonBacktracking v))
    (hp' : 0 < annealed μ 0 (nonBacktracking (-v))) (e e' : Step d)
    (he : height v (stepVector e) = -1) (he' : height (-v) (stepVector e') = -1)
    (c C b β B : ℝ) (hc : 0 < c) (hC : 0 ≤ C) (hb : 0 ≤ b)
    (hβ : 0 < β) (hβc : 1 ≤ β*c) (hB : 1 ≤ B)
    (htilt : Real.sqrt d*(2+β*(C+2)) < B-1)
    (r : ℕ) (hr : 1 ≤ r) (hrc : C+3 < c*r)
    (hheight : (15:ℝ)/16 ≤ (conditioned μ v).real
      (heightEnvelope (fun k X => slabHeightSum v X k) c C b))
    (hheight' : (15:ℝ)/16 ≤ (conditioned μ (-v)).real
      (heightEnvelope (fun k X => slabHeightSum (-v) X k) c C b)) :
    Integrable slabRadius (slabLaw μ v + slabLaw μ (-v)) := by
  let := slabLaw_probability μ v hp
  let := slabLaw_probability μ (-v) hp'
  let := conditioned_probability μ v hp
  let := conditioned_probability μ (-v) hp'
  by_contra hnot
  have hv' : -v ≠ 0 := neg_ne_zero.mpr hv
  have hvnorm' : ∀ i, |(-v) i| ≤ 1 := by simpa only [Pi.neg_apply,abs_neg] using hvnorm
  have hr0 : (0:ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  let η : ℝ := 1/(64*r)
  have hη : 0 < η := by dsimp [η]; positivity
  have hηsmall : 2*η ≤ 1/4 := by
    dsimp [η]
    rw [mul_one_div]
    have hr1 : (1:ℝ) ≤ r := by exact_mod_cast hr
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 64*r)).mpr
    linarith
  obtain ⟨M,hM⟩ := exists_nat_gt ((2+β*b)/β)
  have hMcoef : 1 < (M:ℝ)*β-1-β*b := by
    have hm := (div_lt_iff₀ hβ).mp hM
    nlinarith only [hm]
  let p := (annealed μ 0).real (nonBacktracking v)
  let p' := (annealed μ 0).real (nonBacktracking (-v))
  have hp0 : 0 < p := ENNReal.toReal_pos hp.ne' (measure_ne_top _ _)
  have hp0' : 0 < p' := ENNReal.toReal_pos hp'.ne' (measure_ne_top _ _)
  let A := (meanStep μ e ^ M).toReal*p*p'*(3/8)
  let A' := (meanStep μ e' ^ M).toReal*p'*p*(3/8)
  have hA : 0 < A := by
    have := meanStep_power_real_pos μ hell e M
    dsimp [A]; positivity
  have hA' : 0 < A' := by
    have := meanStep_power_real_pos μ hell e' M
    dsimp [A']; positivity
  let Γ := min A A'
  have hΓ : 0 < Γ := lt_min hA hA'
  let K : ℝ := Fintype.card (Step d)
  have hlim : Tendsto (fun L : ℕ => K*((annealed μ 0).real (finiteHighMaximum v L)+
      (annealed μ 0).real (finiteHighMaximum (-v) L))) atTop (𝓝 0) := by
    simpa only [zero_add,mul_zero] using tendsto_const_nhds.mul
      ((tendsto_real_finiteHighMaximum (annealed μ 0) v).add
        (tendsto_real_finiteHighMaximum (annealed μ 0) (-v)))
  obtain ⟨L,hLsmall⟩ := (hlim.eventually (gt_mem_nhds (show (0:ℝ) < Γ*(η/(2*B)) by positivity))).exists
  have hsum := (summable_real_upper_tail (slabLaw μ v) (slabWidth v) (measurable_of_countable _)
    (integrable_slabWidth μ hell v hv hvnorm hp)).add
    (summable_real_upper_tail (slabLaw μ (-v)) (slabWidth (-v)) (measurable_of_countable _)
      (integrable_slabWidth μ hell (-v) hv' hvnorm' hp'))
  have hsmall := summable_small_Ico _ hsum (fun _ => add_nonneg measureReal_nonneg measureReal_nonneg)
    (show 0 < η/(4*B) by positivity)
  obtain ⟨l₁,hl₁⟩ := eventually_atTop.mp hsmall
  obtain ⟨l₀,hl₀⟩ := exists_nat_gt (max (b+1) (((L:ℝ)+b)/c))
  let l := max l₀ l₁
  have hlb : b+1 < (l:ℝ) := (lt_of_le_of_lt (le_max_left _ _) hl₀).trans_le
    (Nat.cast_le.mpr (le_max_left _ _))
  have hlL : (L:ℝ) ≤ c*l-b := by
    have hll : ((L:ℝ)+b)/c < (l:ℝ) := (lt_of_le_of_lt (le_max_right _ _) hl₀).trans_le
      (Nat.cast_le.mpr (le_max_left _ _))
    have hh := (div_lt_iff₀ hc).mp hll
    nlinarith only [hh]
  have hl0 : 0 < l := by
    have hh : (0:ℝ) < l := by linarith
    exact_mod_cast hh
  have hscales := radius_scales (slabLaw μ v + slabLaw μ (-v)) slabRadius
    (measurable_of_countable _) slabRadius_nonneg hnot hη l
    (show 0 < B*((l:ℝ)+1) by positivity)
  obtain ⟨a,ha,hlarge⟩ := ((eventually_gt_atTop (max ((M:ℝ)+1) (1/β+1))).and hscales).exists
  obtain ⟨ha0,N,hN,hsc,hscu,hscs,_⟩ := hlarge
  have hNl : l ≤ N := (le_max_right _ _).trans hN
  have hN0 : 0 < N := hl0.trans_le hNl
  have hβa : 1 < β*a := by
    have haa : 1/β+1 < a := lt_of_le_of_lt (le_max_right _ _) ha
    have hh := mul_lt_mul_of_pos_left haa hβ
    rw [mul_add,mul_one_div_cancel hβ.ne',mul_one] at hh
    linarith
  have hMa : (M:ℝ) < a*((M:ℝ)*β-1-β*b) := by
    have haa : (M:ℝ)+1 < a := lt_of_le_of_lt (le_max_left _ _) ha
    nlinarith only [mul_lt_mul_of_pos_left hMcoef ha0,haa]
  have hq : (C+2)*(N:ℝ)-(M:ℝ)-c*(r*N:ℕ)+b < 0 := by
    have hbn : b+1 < (N:ℝ) := hlb.trans_le (Nat.cast_le.mpr hNl)
    have hh := mul_lt_mul_of_pos_right hrc (Nat.cast_pos.mpr hN0)
    push_cast
    nlinarith only [hh,hbn,show (0:ℝ) ≤ M from Nat.cast_nonneg M]
  have hwidth := hl₁ l (le_max_right _ _) N hNl
  rw [Finset.sum_add_distrib] at hwidth
  have hsmallscale : truncatedMoment (slabLaw μ v + slabLaw μ (-v)) slabRadius
      (B*a*(l+1)) < η*a/4 := by
    convert hscs using 1; ring_nf
  have hlo := largeRadius_mass_pair_lower (slabLaw μ v) (slabLaw μ (-v))
    slabRadius (slabWidth v) (slabWidth (-v)) (measurable_of_countable _) slabRadius_nonneg
    ha0 hB hη hNl hsc hsmallscale hwidth
  have hup := largeRadius_mass_pair_upper (slabLaw μ v) (slabLaw μ (-v))
    slabRadius (slabWidth v) (slabWidth (-v)) (measurable_of_countable _) slabRadius_nonneg
    ha0 hB hNl hscu
  let lam := ∑ i ∈ Finset.Ico l N, (slabLaw μ v).real (largeRadiusWord slabRadius (slabWidth v) (B*a) i)
  let lam' := ∑ i ∈ Finset.Ico l N, (slabLaw μ (-v)).real (largeRadiusWord slabRadius (slabWidth (-v)) (B*a) i)
  have hlam : 0 ≤ lam := Finset.sum_nonneg (fun _ _ => measureReal_nonneg)
  have hlam' : 0 ≤ lam' := Finset.sum_nonneg (fun _ _ => measureReal_nonneg)
  change η/(2*B) ≤ lam+lam' at hlo
  change lam+lam' < 2*η at hup
  have hlams : lam ≤ 1/4 := by linarith
  have hlams' : lam' ≤ 1/4 := by linarith
  have hscsimple : truncatedMoment (slabLaw μ v + slabLaw μ (-v)) slabRadius (a*N) < a/(32*r) := by
    convert hscu using 1
    dsimp [η]
    field_simp [ne_of_gt hr0]
    ring
  have htr := truncatedMoment_component_scale (slabLaw μ v) (slabLaw μ (-v)) slabRadius
    (measurable_of_countable _) slabRadius_nonneg ha0 r N hr hscsimple
  have htr' := truncatedMoment_component_scale (slabLaw μ (-v)) (slabLaw μ v) slabRadius
    (measurable_of_countable _) slabRadius_nonneg ha0 r N hr (by simpa only [add_comm] using hscsimple)
  have hq0 : 0 < r*N := Nat.mul_pos (by omega) hN0
  have hNq : N ≤ r*N := Nat.le_mul_of_pos_left N (by omega)
  have hgood := goodRadiusPrefix_uniform_probability μ hell v hv hp a c C b ha0 (r*N) hq0 hheight (by simpa only [Nat.cast_mul] using htr)
  have hgood' := goodRadiusPrefix_uniform_probability μ hell (-v) hv' hp' a c C b ha0 (r*N) hq0 hheight' (by simpa only [Nat.cast_mul] using htr')
  have hpos := radius_occurrence_mass_le μ hell v hv hp hp' e a B β c C b L ha0 hβ.le hc.le hC
    htilt hβc hβa he M (r*N) l N hMa hq (by linarith) hlL
    (fun i hi => hgood i ((Finset.mem_Ico.mp hi).2.le.trans hNq)) (hgood' _ le_rfl) hlams
  have hneg := radius_occurrence_mass_le μ hell (-v) hv' hp' (by simpa only [neg_neg] using hp) e' a B β c C b L ha0 hβ.le hc.le hC
    htilt hβc hβa he' M (r*N) l N hMa hq (by linarith) hlL
    (fun i hi => hgood' i ((Finset.mem_Ico.mp hi).2.le.trans hNq)) (by simpa only [neg_neg] using hgood (r*N) le_rfl) hlams'
  change A*lam ≤ K*(annealed μ 0).real (finiteHighMaximum v L) at hpos
  simp only [neg_neg] at hneg
  change A'*lam' ≤ K*(annealed μ 0).real (finiteHighMaximum (-v) L) at hneg
  have hbound : Γ*(lam+lam') ≤ K*((annealed μ 0).real (finiteHighMaximum v L)+
      (annealed μ 0).real (finiteHighMaximum (-v) L)) := by
    have hh := add_le_add (mul_le_mul_of_nonneg_right (min_le_left A A') hlam)
      (mul_le_mul_of_nonneg_right (min_le_right A A') hlam')
    dsimp [Γ]
    nlinarith only [hh,hpos,hneg]
  have hh := mul_le_mul_of_nonneg_left hlo hΓ.le
  exact (not_lt_of_ge (hh.trans hbound)) hLsmall

lemma exists_down_unit_step {d : ℕ} (v : Fin d → ℝ) (hv : ∃ i, |v i| = 1) :
    ∃ e : Step d, height v (stepVector e) = -1 := by
  obtain ⟨i,hi⟩ := hv
  rcases le_total 0 (v i) with h | h
  · rw [abs_of_nonneg h] at hi
    exact ⟨(i,false),by simp [height_stepVector,hi]⟩
  · rw [abs_of_nonpos h] at hi
    exact ⟨(i,true),by simp [height_stepVector]; linarith⟩

lemma integrable_slabRadius_normalized {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hvnorm : ∀ i, |v i| ≤ 1) (hvunit : ∃ i, |v i| = 1)
    (hp : 0 < annealed μ 0 (nonBacktracking v))
    (hp' : 0 < annealed μ 0 (nonBacktracking (-v))) :
    Integrable slabRadius (slabLaw μ v) ∧ Integrable slabRadius (slabLaw μ (-v)) := by
  obtain ⟨c,C,b,hc,hC,hb,hh,hh'⟩ := exists_common_heightEnvelope μ hell v hv hvnorm hp hp'
  let β := 2/c
  have hβ : 0 < β := div_pos (by norm_num) hc
  have hβc : 1 ≤ β*c := by dsimp [β]; rw [div_mul_cancel₀ _ hc.ne']; norm_num
  let B := Real.sqrt d*(2+β*(C+2))+2
  have hB : 1 ≤ B := by
    have ht : 0 ≤ Real.sqrt d*(2+β*(C+2)) := by positivity
    dsimp [B]; linarith
  have htilt : Real.sqrt d*(2+β*(C+2)) < B-1 := by dsimp [B]; linarith
  obtain ⟨r,hr⟩ := exists_nat_gt (max 1 ((C+3)/c))
  have hr1 : 1 ≤ r := by
    have hh : (1:ℝ) < r := lt_of_le_of_lt (le_max_left _ _) hr
    have : 1 < r := by exact_mod_cast hh
    omega
  have hrc : C+3 < c*r := by
    have hh := (div_lt_iff₀ hc).mp (lt_of_le_of_lt (le_max_right _ _) hr)
    nlinarith only [hh]
  obtain ⟨e,he⟩ := exists_down_unit_step v hvunit
  obtain ⟨e',he'⟩ := exists_down_unit_step (-v) (by simpa only [Pi.neg_apply,abs_neg] using hvunit)
  exact integrable_add_measure.mp (integrable_radius_from_parameters μ hell v hv hvnorm hp hp'
    e e' he he' c C b β B hc hC hb hβ hβc hB htilt r hr1 hrc hh hh')

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

noncomputable def wordOffset {α : Type*} (D : α → ℝ) (Z : ℕ → α) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, D (Z i)

def wordSequenceEscape {α : Type*} (D F : α → ℝ) : Set (ℕ → α) :=
  {Z | Tendsto (fun k => wordOffset D Z k + F (Z k)) atTop atTop}

lemma wordOffset_add {α : Type*} (D : α → ℝ) (Z : ℕ → α) (n k : ℕ) :
    wordOffset D Z (n+k) = wordOffset D Z n + wordOffset D (fun i => Z (n+i)) k := by
  simp only [wordOffset,Finset.sum_range_add]

lemma wordSequenceEscape_shift {α : Type*} (D F : α → ℝ) (Z : ℕ → α) (n : ℕ) :
    (fun i => Z (n+i)) ∈ wordSequenceEscape D F ↔ Z ∈ wordSequenceEscape D F := by
  change Tendsto _ atTop atTop ↔ Tendsto _ atTop atTop
  have heq : (fun k => wordOffset D Z (n+k)+F (Z (n+k))) =
      fun k => wordOffset D Z n + (wordOffset D (fun i => Z (n+i)) k + F (Z (n+k))) := by
    funext k; rw [wordOffset_add]; ring
  have hh := tendsto_add_atTop_iff_nat (f := fun k => wordOffset D Z k + F (Z k)) (l := atTop) n
  simp only [Nat.add_comm] at hh
  rw [heq] at hh
  have hc : Tendsto (fun k => wordOffset D Z n +
      (wordOffset D (fun i => Z (n+i)) k + F (Z (n+k)))) atTop atTop ↔
      Tendsto (fun k => wordOffset D (fun i => Z (n+i)) k + F (Z (n+k))) atTop atTop := by
    constructor <;> intro ht <;> apply tendsto_atTop.mpr <;> intro b
    · filter_upwards [(tendsto_atTop.mp ht) (wordOffset D Z n+b)] with k hk
      linarith
    · filter_upwards [(tendsto_atTop.mp ht) (b-wordOffset D Z n)] with k hk
      linarith
  exact hc.symm.trans hh

lemma measurableSet_wordSequenceEscape {α : Type*} [MeasurableSpace α]
    (D F : α → ℝ) (hD : Measurable D) (hF : Measurable F) :
    MeasurableSet (wordSequenceEscape D F) := by
  apply measurableSet_tendsto
  intro k
  exact (Finset.measurable_sum _ (fun i _ => hD.comp (measurable_pi_apply i))).add
    (hF.comp (measurable_pi_apply k))

lemma wordSequenceEscape_zero_one {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (P : Measure Ω) (Z : ℕ → Ω → α) (hZ : ∀ i, Measurable (Z i))
    (hind : iIndepFun Z P) (D F : α → ℝ) (hD : Measurable D) (hF : Measurable F) :
    P {x | (fun i => Z i x) ∈ wordSequenceEscape D F} = 0 ∨
      P {x | (fun i => Z i x) ∈ wordSequenceEscape D F} = 1 := by
  apply measure_zero_or_one_of_measurableSet_limsup_atTop
    (fun n => (hZ n).comap_le) hind
  rw [limsup_eq_iInf_iSup_of_nat,MeasurableSpace.measurableSet_iInf]
  intro n
  have hm : @Measurable Ω (ℕ → α) (⨆ i ≥ n, MeasurableSpace.comap (Z i) inferInstance)
      inferInstance (fun x k => Z (n+k) x) := by
    exact @Measurable.of_eval Ω ℕ (fun _ => α)
      (⨆ i ≥ n, MeasurableSpace.comap (Z i) inferInstance) (fun _ => inferInstance)
      (fun x k => Z (n+k) x) (fun k => (comap_measurable (Z (n+k))).mono
      (le_iSup_of_le (n+k) (le_iSup_of_le (by omega : n ≤ n+k) le_rfl)) le_rfl)
  have hh := hm (measurableSet_wordSequenceEscape D F hD hF)
  convert hh using 1
  ext x
  exact (wordSequenceEscape_shift D F (fun i => Z i x) n).symm

noncomputable def heightBound {d : ℕ} (w : Fin d → ℝ) : ℝ := ∑ i, |w i|

lemma heightBound_nonneg {d : ℕ} (w : Fin d → ℝ) : 0 ≤ heightBound w :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

lemma abs_height_le_norm {d : ℕ} (w : Fin d → ℝ) (x : Site d) :
    |height w x| ≤ heightBound w * ‖euclideanSite x‖ := by
  calc
    _ ≤ ∑ i, |(x i : ℝ)*w i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |w i| *‖euclideanSite x‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul,mul_comm]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa [euclideanSite] using PiLp.norm_apply_le (euclideanSite x) i
    _ = _ := by rw [← Finset.sum_mul]; rfl

noncomputable def slabFloor {d : ℕ} (w : Fin d → ℝ) (γ : Word d) : ℝ :=
  (Finset.range (γ.1+1)).inf' ⟨0,Finset.mem_range.mpr (Nat.succ_pos _)⟩
    (fun j => height w (wordPath γ j))

lemma slabFloor_le {d : ℕ} (w : Fin d → ℝ) (γ : Word d) {j : ℕ} (hj : j ≤ γ.1) :
    slabFloor w γ ≤ height w (wordPath γ j) :=
  Finset.inf'_le _ (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

lemma abs_word_height_le_radius {d : ℕ} (w : Fin d → ℝ) (γ : Word d)
    (h0 : wordPath γ 0 = 0) {j : ℕ} (hj : j ≤ γ.1) :
    |height w (wordPath γ j)| ≤ heightBound w * slabRadius γ := by
  have hh := norm_wordPath_le_radius γ hj
  rw [h0,sub_zero] at hh
  exact (abs_height_le_norm w _).trans (mul_le_mul_of_nonneg_left hh (heightBound_nonneg w))

lemma abs_slabFloor_le_radius {d : ℕ} (w : Fin d → ℝ) (γ : Word d)
    (h0 : wordPath γ 0 = 0) : |slabFloor w γ| ≤ heightBound w * slabRadius γ := by
  apply abs_le.mpr
  constructor
  · apply Finset.le_inf'
    intro j hj
    exact (abs_le.mp (abs_word_height_le_radius w γ h0 (by simpa using hj))).1
  · have hh := slabFloor_le w γ (j := 0) (Nat.zero_le _)
    rw [h0,height_zero] at hh
    exact hh.trans (mul_nonneg (heightBound_nonneg w) (slabRadius_nonneg γ))

lemma height_at_slabTime_projection {d : ℕ} (v w : Fin d → ℝ) (X : Path d)
    (h0 : X 0 = 0) (k : ℕ) :
    height w (X (slabTime v X k)) = wordOffset (slabWidth w) (slabs v X) k := by
  induction k with
  | zero => simp [slabTime_zero,wordOffset,h0,height_zero]
  | succ k ih =>
    have hh := iterated_cutSuffix v X h0 k (slabs v X k).1
    rw [← slab_word_path v X k le_rfl,← slabTime_succ] at hh
    have hh' := congrArg (height w) hh
    rw [height_sub,ih] at hh'
    change slabWidth w (slabs v X k) = height w (X (slabTime v X (k+1))) - _ at hh'
    rw [wordOffset,Finset.sum_range_succ]
    change height w (X (slabTime v X (k+1))) = wordOffset (slabWidth w) (slabs v X) k + _
    linarith

lemma height_in_slab_projection {d : ℕ} (v w : Fin d → ℝ) (X : Path d)
    (h0 : X 0 = 0) (k j : ℕ) (hj : j ≤ (slabs v X k).1) :
    height w (X (slabTime v X k+j)) = wordOffset (slabWidth w) (slabs v X) k +
      height w (wordPath (slabs v X k) j) := by
  have hh := congrArg (height w) (iterated_cutSuffix v X h0 k j)
  rw [← slab_word_path v X k hj,height_sub,height_at_slabTime_projection v w X h0] at hh
  linarith

lemma escape_iff_wordSequenceEscape {d : ℕ} (v w : Fin d → ℝ) (X : Path d)
    (hX : GoodSlabPath v X) :
    X ∈ escape w ↔ slabs v X ∈ wordSequenceEscape (slabWidth w) (slabFloor w) := by
  constructor
  · intro ht
    apply tendsto_atTop.mpr
    intro b
    obtain ⟨N,hN⟩ := eventually_atTop.mp ((tendsto_atTop.mp ht) b)
    refine eventually_atTop.mpr ⟨N,fun k hk => ?_⟩
    have hf : b-wordOffset (slabWidth w) (slabs v X) k ≤ slabFloor w (slabs v X k) := by
      apply Finset.le_inf'
      intro j hj
      have hn : N ≤ slabTime v X k+j := (hk.trans ((slabTime_strictMono v X hX).id_le k)).trans (Nat.le_add_right _ _)
      have hh := hN _ hn
      change b ≤ height w (X _) at hh
      rw [height_in_slab_projection v w X hX.1 k j (by simpa using hj)] at hh
      linarith
    linarith
  · intro ht
    apply tendsto_atTop.mpr
    intro b
    obtain ⟨K,hK⟩ := eventually_atTop.mp ((tendsto_atTop.mp ht) b)
    refine eventually_atTop.mpr ⟨slabTime v X K,fun n hn => ?_⟩
    obtain ⟨k,hkn,hnk⟩ := slab_location v X hX n
    have hk : K ≤ k := by
      by_contra hh
      have hh' : k+1 ≤ K := by omega
      have hh'' := (slabTime_strictMono v X hX).monotone hh'
      omega
    have hj : n-slabTime v X k ≤ (slabs v X k).1 := by
      rw [slabTime_succ] at hnk
      omega
    have hp := height_in_slab_projection v w X hX.1 k (n-slabTime v X k) hj
    rw [Nat.add_sub_of_le hkn] at hp
    change b ≤ height w (X n)
    rw [hp]
    exact (hK k hk).trans (add_le_add le_rfl (slabFloor_le w _ hj))

lemma conditioned_escape_zero_one {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) (w : Fin d → ℝ) :
    conditioned μ v (escape w) = 0 ∨ conditioned μ v (escape w) = 1 := by
  have heq : conditioned μ v (escape w) = conditioned μ v
      {X | slabs v X ∈ wordSequenceEscape (slabWidth w) (slabFloor w)} := by
    apply measure_congr
    filter_upwards [ae_goodSlabPath μ hell v hv hp] with X hX
    exact propext (escape_iff_wordSequenceEscape v w X hX)
  rw [heq]
  exact wordSequenceEscape_zero_one (conditioned μ v) (fun k X => slabs v X k)
    (fun k => (measurable_pi_apply k).comp (measurable_slabs v))
    (slabs_iid μ hell v hv hp) _ _ (measurable_of_countable _) (measurable_of_countable _)

lemma tendsto_term_div_nat_of_average (f : ℕ → ℝ) {m : ℝ}
    (h : Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, f i) / n) atTop (𝓝 m)) :
    Tendsto (fun n : ℕ => f n/n) atTop (𝓝 0) := by
  have hs := h.comp (tendsto_add_atTop_nat 1)
  have hr : Tendsto (fun n : ℕ => ((n:ℝ)+1)/n) atTop (𝓝 1) := by
    simpa only [inv_div,inv_one] using (tendsto_natCast_div_add_atTop (1:ℝ)).inv₀ (by norm_num)
  have ht := (hs.mul hr).sub h
  simp only [mul_one,sub_self] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  dsimp [Function.comp_def]
  rw [Finset.sum_range_succ]
  push_cast
  have hn0 : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hn1 : (n:ℝ)+1 ≠ 0 := by positivity
  field_simp
  ring

lemma tendsto_atTop_of_positive_slope (f : ℕ → ℝ) {m : ℝ} (hm : 0 < m)
    (h : Tendsto (fun n : ℕ => f n/n) atTop (𝓝 m)) : Tendsto f atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  obtain ⟨N,hN⟩ := exists_nat_gt (max 1 (b/(m/2)))
  have hn1 : (1:ℝ) < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hNb : b < (m/2)*N := by
    have hh := (div_lt_iff₀ (half_pos hm)).mp (lt_of_le_of_lt (le_max_right _ _) hN)
    nlinarith only [hh]
  filter_upwards [h.eventually (lt_mem_nhds (half_lt_self hm)),eventually_ge_atTop N] with n hn hnN
  have hn0 : (0:ℝ) < n := by
    have hh : (N:ℝ) ≤ n := Nat.cast_le.mpr hnN
    linarith
  have hh := (lt_div_iff₀ hn0).mp hn
  have hhN := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hnN) (half_pos hm).le
  exact (hNb.trans_le hhN).le.trans hh.le

lemma relativeTail_escape_iff {d : ℕ} (w : Fin d → ℝ) (X : Path d) (n : ℕ) :
    relativeTail n X ∈ escape w ↔ X ∈ escape w := by
  change Tendsto (fun k => height w (relativeTail n X k)) atTop atTop ↔
    Tendsto (fun k => height w (X k)) atTop atTop
  simp only [relativeTail_apply,height_sub]
  have hh := tendsto_add_atTop_iff_nat (f := fun k => height w (X k)) (l := atTop) n
  simp only [Nat.add_comm] at hh
  have hc : Tendsto (fun k => height w (X (n+k))-height w (X n)) atTop atTop ↔
      Tendsto (fun k => height w (X (n+k))) atTop atTop := by
    constructor <;> intro ht <;> apply tendsto_atTop.mpr <;> intro b
    · filter_upwards [(tendsto_atTop.mp ht) (b-height w (X n))] with k hk
      linarith
    · filter_upwards [(tendsto_atTop.mp ht) (b+height w (X n))] with k hk
      linarith
  exact hc.trans hh

lemma annealed_shift_back {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x : Site d) {E : Set (Path d)} (hE : MeasurableSet E) :
    annealed μ x (shiftPath (-x) ⁻¹' E) = annealed μ 0 E := by
  have hh := congrArg (fun P : Measure (Path d) => P (shiftPath (-x) ⁻¹' E))
    (annealed_shift μ 0 x)
  rw [Measure.map_apply (measurable_shiftPath _) ((measurable_shiftPath _) hE),zero_add] at hh
  have he : shiftPath x ⁻¹' (shiftPath (-x) ⁻¹' E) = E := by
    ext X
    simp only [Set.mem_preimage]
    have hX : shiftPath (-x) (shiftPath x X) = X := by
      funext n
      simp [shiftPath]
    rw [hX]
  rw [he] at hh
  exact hh.symm

lemma annealed_relativeTail_null {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (y : Site d) (n : ℕ) {E : Set (Path d)} (hE : MeasurableSet E)
    (hzero : annealed μ 0 E = 0) : annealed μ y (relativeTail n ⁻¹' E) = 0 := by
  have hsub : relativeTail n ⁻¹' E ⊆ ⋃ x : Site d,
      {X | X n = x} ∩ tailPath n ⁻¹' (shiftPath (-x) ⁻¹' E) := by
    intro X hX
    exact Set.mem_iUnion.mpr ⟨X n,rfl,hX⟩
  apply measure_mono_null hsub
  apply measure_iUnion_null
  intro x
  apply annealed_tail_start_null μ y x n ((measurable_shiftPath _) hE)
  rw [annealed_shift_back μ x hE,hzero]

lemma conditioned_null_transfer {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (v : Fin d → ℝ) (hp : 0 < annealed μ 0 (nonBacktracking v))
    {E : Set (Path d)} (hE : MeasurableSet E)
    (hinv : ∀ X n, relativeTail n X ∈ E ↔ X ∈ E)
    (hz : conditioned μ v E = 0) : annealed μ 0 (escape v ∩ E) = 0 := by
  have hDE : annealed μ 0 (E ∩ nonBacktracking v) = 0 := by
    unfold conditioned at hz
    rw [cond_apply (measurableSet_nonBacktracking v)] at hz
    have hh := (mul_eq_zero.mp hz).resolve_left (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))
    simpa only [Set.inter_comm] using hh
  have ht (n : ℕ) := annealed_relativeTail_null μ 0 n
    (hE.inter (measurableSet_nonBacktracking v)) hDE
  have halls : ∀ᵐ X ∂annealed μ 0, ∀ n, relativeTail n X ∉ E ∩ nonBacktracking v :=
    ae_all_iff.mpr (fun n => (measure_eq_zero_iff_ae_notMem).mp (ht n))
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [halls,ae_infinitely_trueCuts μ 0 v hp] with X hX hc hXE
  have hu : ¬∃ b : ℝ, ∀ n, height v (X n) ≤ b := by
    rintro ⟨b,hb⟩
    obtain ⟨n,hn⟩ := ((tendsto_atTop.mp hXE.1) (b+1)).exists
    change b+1 ≤ height v (X n) at hn
    have hh := hb n
    linarith
  obtain ⟨n,_,hn⟩ := hc hu 0
  exact hX n ⟨(hinv X n).mpr hXE.2,(relativeTail_nonBacktracking_iff v X n).mpr hn.2⟩

lemma conditioned_ae_transfer {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (v : Fin d → ℝ) (hp : 0 < annealed μ 0 (nonBacktracking v))
    {E : Set (Path d)} (hE : MeasurableSet E)
    (hinv : ∀ X n, relativeTail n X ∈ E ↔ X ∈ E)
    (h : ∀ᵐ X ∂conditioned μ v, X ∈ E) :
    ∀ᵐ X ∂annealed μ 0, X ∈ escape v → X ∈ E := by
  have hz : conditioned μ v Eᶜ = 0 := by
    exact ae_iff.mp h
  have hh := conditioned_null_transfer μ v hp hE.compl
    (fun X n => not_congr (hinv X n)) hz
  filter_upwards [(measure_eq_zero_iff_ae_notMem).mp hh] with X hX hAv
  by_contra hn
  exact hX ⟨hAv,hn⟩

lemma integrable_slabProjection {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v))
    (hR : Integrable slabRadius (slabLaw μ v)) (w : Fin d → ℝ) :
    Integrable (slabWidth w) (slabLaw μ v) := by
  apply (hR.const_mul (heightBound w)).mono' (measurable_of_countable _).aestronglyMeasurable
  filter_upwards [ae_slabLaw_regeneration μ hell v hv hp] with γ hγ
  exact abs_word_height_le_radius w γ hγ.2.1 le_rfl

lemma ae_slabRadius_sublinear {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v))
    (hR : Integrable slabRadius (slabLaw μ v)) :
    ∀ᵐ X ∂conditioned μ v,
      Tendsto (fun n : ℕ => slabRadius (slabs v X n)/n) atTop (𝓝 0) := by
  filter_upwards [slabObservable_strongLaw μ hell v hv hp _ hR] with X hX
  exact tendsto_term_div_nat_of_average _ hX

lemma conditioned_escape_of_positive_mean {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v))
    (hR : Integrable slabRadius (slabLaw μ v)) (w : Fin d → ℝ)
    (hw : 0 < ∫ γ, slabWidth w γ ∂slabLaw μ v) :
    ∀ᵐ X ∂conditioned μ v, X ∈ escape w := by
  filter_upwards [ae_goodSlabPath μ hell v hv hp,ae_slabRadius_sublinear μ hell v hv hp hR,
    slabObservable_strongLaw μ hell v hv hp _ (integrable_slabProjection μ hell v hv hp hR w)]
    with X hX hsub hsum
  apply (escape_iff_wordSequenceEscape v w X hX).mpr
  change Tendsto (fun n => wordOffset (slabWidth w) (slabs v X) n + slabFloor w (slabs v X n)) atTop atTop
  apply tendsto_atTop_of_positive_slope _ hw
  have hfloor : Tendsto (fun n : ℕ => slabFloor w (slabs v X n)/n) atTop (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    have ht := hsub.const_mul (heightBound w)
    rw [mul_zero] at ht
    apply squeeze_zero (fun n => abs_nonneg _) (fun n => ?_) ht
    rw [abs_div,show |(n:ℝ)| = (n:ℝ) from abs_of_nonneg (Nat.cast_nonneg n),← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    exact abs_slabFloor_le_radius w _ (hX.2 n).2.1
  simpa only [add_div,add_zero,wordOffset] using hsum.add hfloor

noncomputable def slabMean {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (v : Fin d → ℝ) : Fin d → ℝ :=
  fun i => ∫ γ, (wordPath γ γ.1 i : ℝ) ∂slabLaw μ v

noncomputable def directionDot {d : ℕ} (v w : Fin d → ℝ) : ℝ := ∑ i, v i*w i

lemma integral_slabProjection {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v))
    (hR : Integrable slabRadius (slabLaw μ v)) (w : Fin d → ℝ) :
    (∫ γ, slabWidth w γ ∂slabLaw μ v) = directionDot (slabMean μ v) w := by
  have hi (i : Fin d) : Integrable (fun γ : Word d => (wordPath γ γ.1 i : ℝ)) (slabLaw μ v) := by
    have hh := integrable_slabProjection μ hell v hv hp hR (Pi.single i 1)
    have he : slabWidth (Pi.single i 1) = (fun γ : Word d => (wordPath γ γ.1 i : ℝ)) := by
      funext γ
      simp [slabWidth,height,Pi.single_apply]
    rwa [he] at hh
  unfold slabWidth height directionDot slabMean
  rw [integral_finsetSum _ (fun i _ => (hi i).mul_const (w i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_mul_const]

lemma directionDot_add_right {d : ℕ} (a b c : Fin d → ℝ) :
    directionDot a (b+c) = directionDot a b + directionDot a c := by
  simp [directionDot,mul_add,Finset.sum_add_distrib]

lemma directionDot_self_pos {d : ℕ} (a : Fin d → ℝ) (ha : a ≠ 0) :
    0 < directionDot a a := by
  obtain ⟨i,hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra hh
    push Not at hh
    exact ha (funext hh)
  apply Finset.sum_pos'
  · intro j _
    exact mul_self_nonneg _
  · exact ⟨i,Finset.mem_univ _,mul_self_pos.mpr hi⟩

lemma escape_not_opposite {d : ℕ} (v : Fin d → ℝ) (X : Path d)
    (h : X ∈ escape v) : X ∉ escape (-v) := by
  intro hn
  have hh := ((tendsto_atTop.mp h) 1).and ((tendsto_atTop.mp hn) 1)
  obtain ⟨n,hp,hm⟩ := hh.exists
  change 1 ≤ height v (X n) at hp
  change 1 ≤ height (-v) (X n) at hm
  rw [height_neg_direction] at hm
  linarith

lemma escape_zero_one_of_full_direction {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (w : Fin d → ℝ) (hw : w ≠ 0)
    (hfull : annealed μ 0 (escape w) = 1) (v : Fin d → ℝ) :
    annealed μ 0 (escape v) = 0 ∨ annealed μ 0 (escape v) = 1 := by
  have hp := positive_nonBacktracking μ w (hfull ▸ zero_lt_one)
  have hwfull := (mem_ae_iff_prob_eq_one (measurableSet_escape w)).mpr hfull
  let := conditioned_probability μ w hp
  rcases conditioned_escape_zero_one μ hell w hw hp v with hz | ho
  · left
    have he := conditioned_null_transfer μ w hp (measurableSet_escape v)
      (relativeTail_escape_iff v) hz
    calc
      _ = annealed μ 0 (escape w ∩ escape v) := by
        apply measure_congr
        filter_upwards [hwfull] with X hX
        exact propext ⟨fun hv => ⟨hX,hv⟩,fun hh => hh.2⟩
      _ = 0 := he
  · right
    have he := conditioned_ae_transfer μ w hp (measurableSet_escape v)
      (relativeTail_escape_iff v)
      ((mem_ae_iff_prob_eq_one (measurableSet_escape v)).mpr ho)
    apply (mem_ae_iff_prob_eq_one (measurableSet_escape v)).mp
    filter_upwards [he,hwfull] with X hX hWX
    exact hX hWX

lemma not_zero_one_of_opposite_positive {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (v : Fin d → ℝ) (hp : 0 < annealed μ 0 (escape v))
    (hm : 0 < annealed μ 0 (escape (-v))) :
    ¬(annealed μ 0 (escape v) = 0 ∨ annealed μ 0 (escape v) = 1) := by
  rintro (hz|ho)
  · exact hp.ne' hz
  · have he := (mem_ae_iff_prob_eq_one (measurableSet_escape v)).mpr ho
    have hz : annealed μ 0 (escape (-v)) = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [he] with X hX
      exact escape_not_opposite v X hX
    exact hm.ne' hz

lemma positive_raw_of_conditioned_ae {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (v : Fin d → ℝ) (hp : 0 < annealed μ 0 (nonBacktracking v))
    {E : Set (Path d)} (hE : MeasurableSet E) (he : ∀ᵐ X ∂conditioned μ v, X ∈ E) :
    0 < annealed μ 0 E := by
  let := conditioned_probability μ v hp
  by_contra hh
  have hz : annealed μ 0 E = 0 := le_antisymm (le_of_not_gt hh) (zero_le)
  have hac : conditioned μ v ≪ annealed μ 0 := cond_absolutelyContinuous
  have hh' := hac hz
  have ho := (mem_ae_iff_prob_eq_one hE).mp he
  rw [hh'] at ho
  exact zero_ne_one ho

lemma coordinate_direction_ne_zero {d : ℕ} (i : Fin d) :
    (Pi.single i (1:ℝ) : Fin d → ℝ) ≠ 0 := by
  intro hh
  have hh' := congr_fun hh i
  simp at hh'

lemma exists_mixed_coordinate {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hvnorm : ∀ i, |v i| ≤ 1) (hvunit : ∃ i, |v i| = 1)
    (hp : 0 < annealed μ 0 (escape v)) (hm : 0 < annealed μ 0 (escape (-v))) :
    ∃ i : Fin d, 0 < annealed μ 0 (escape (Pi.single i 1)) ∧
      0 < annealed μ 0 (escape (-Pi.single i 1)) := by
  have hpD := positive_nonBacktracking μ v hp
  have hmD := positive_nonBacktracking μ (-v) hm
  have hvn : -v ≠ 0 := neg_ne_zero.mpr hv
  have hvnn : ∀ i, |(-v) i| ≤ 1 := by simpa only [Pi.neg_apply,abs_neg] using hvnorm
  obtain ⟨hR,hR'⟩ := integrable_slabRadius_normalized μ hell v hv hvnorm hvunit hpD hmD
  let a := slabMean μ v
  let b := slabMean μ (-v)
  have ha : a ≠ 0 := by
    have hh := integral_slabWidth_pos μ hell v hv hvnorm hpD
    rw [integral_slabProjection μ hell v hv hpD hR] at hh
    intro hz
    change 0 < directionDot a v at hh
    simp [hz,directionDot] at hh
  have hb : b ≠ 0 := by
    have hh := integral_slabWidth_pos μ hell (-v) hvn hvnn hmD
    rw [integral_slabProjection μ hell (-v) hvn hmD hR'] at hh
    intro hz
    change 0 < directionDot b (-v) at hh
    simp [hz,directionDot] at hh
  have hex : ∃ i, a i*b i < 0 := by
    by_contra hh
    push Not at hh
    let w := a+b
    have hacross : 0 ≤ directionDot a b := Finset.sum_nonneg (fun i _ => hh i)
    have hbcross : 0 ≤ directionDot b a := by
      simpa only [directionDot,mul_comm] using hacross
    have hwa : 0 < directionDot a w := by
      rw [directionDot_add_right]
      exact add_pos_of_pos_of_nonneg (directionDot_self_pos a ha) hacross
    have hwb : 0 < directionDot b w := by
      rw [directionDot_add_right]
      exact add_pos_of_nonneg_of_pos hbcross (directionDot_self_pos b hb)
    have hwn : w ≠ 0 := by
      intro hz
      simp [hz,directionDot] at hwa
    have hwA : ∀ᵐ X ∂conditioned μ v, X ∈ escape w := by
      apply conditioned_escape_of_positive_mean μ hell v hv hpD hR w
      rwa [integral_slabProjection μ hell v hv hpD hR]
    have hwB : ∀ᵐ X ∂conditioned μ (-v), X ∈ escape w := by
      apply conditioned_escape_of_positive_mean μ hell (-v) hvn hmD hR' w
      rwa [integral_slabProjection μ hell (-v) hvn hmD hR']
    have hfull : annealed μ 0 (escape w) = 1 := by
      apply (mem_ae_iff_prob_eq_one (measurableSet_escape w)).mp
      filter_upwards [ae_escape_or_opposite μ hell 0 v hv hpD,
        conditioned_ae_transfer μ v hpD (measurableSet_escape w) (relativeTail_escape_iff w) hwA,
        conditioned_ae_transfer μ (-v) hmD (measurableSet_escape w) (relativeTail_escape_iff w) hwB]
        with X hXC hXA hXB
      exact hXC.elim hXA hXB
    exact not_zero_one_of_opposite_positive μ v hp hm
      (escape_zero_one_of_full_direction μ hell w hwn hfull v)
  obtain ⟨i,hi⟩ := hex
  have hproj (u : Fin d → ℝ) (hun : u ≠ 0)
      (huD : 0 < annealed μ 0 (nonBacktracking u))
      (huR : Integrable slabRadius (slabLaw μ u)) (w : Fin d → ℝ)
      (huw : 0 < directionDot (slabMean μ u) w) : 0 < annealed μ 0 (escape w) := by
    apply positive_raw_of_conditioned_ae μ u huD (measurableSet_escape w)
    apply conditioned_escape_of_positive_mean μ hell u hun huD huR w
    rwa [integral_slabProjection μ hell u hun huD huR]
  have hdoti (c : Fin d → ℝ) : directionDot c (Pi.single i 1) = c i := by
    simp [directionDot,Pi.single_apply]
  have hdotni (c : Fin d → ℝ) : directionDot c (-Pi.single i 1) = -c i := by
    simp [directionDot,Pi.single_apply,Finset.sum_neg_distrib]
  refine ⟨i,?_⟩
  rcases mul_neg_iff.mp hi with ⟨hia,hib⟩|⟨hia,hib⟩
  · exact ⟨hproj v hv hpD hR _ (by rw [hdoti]; exact hia),
      hproj (-v) hvn hmD hR' _ (by rw [hdotni]; exact neg_pos.mpr hib)⟩
  · exact ⟨hproj (-v) hvn hmD hR' _ (by rw [hdoti]; exact hib),
      hproj v hv hpD hR _ (by rw [hdotni]; exact neg_pos.mpr hia)⟩

lemma height_scale_direction {d : ℕ} (v : Fin d → ℝ) (c : ℝ) (x : Site d) :
    height (c • v) x = c * height v x := by
  simp only [height, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma escape_scale_direction {d : ℕ} (v : Fin d → ℝ) {c : ℝ} (hc : 0 < c) :
    escape (c • v) = escape v := by
  ext X
  change Tendsto (fun n => height (c • v) (X n)) atTop atTop ↔ _
  simp only [height_scale_direction]
  exact tendsto_const_mul_atTop_of_pos hc

lemma direction_normalization {d : ℕ} (v : Fin d → ℝ) (hv : v ≠ 0) :
    ∃ (c : ℝ), 0 < c ∧ (∀ i, |(c • v) i| ≤ 1) ∧ ∃ i, |(c • v) i| = 1 := by
  classical
  obtain ⟨j,hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hv (funext hh)
  obtain ⟨i,_,hmax⟩ := Finset.exists_max_image Finset.univ (fun i => |v i|)
    (show (Finset.univ : Finset (Fin d)).Nonempty from ⟨j,Finset.mem_univ _⟩)
  have hi : 0 < |v i| := (abs_pos.mpr hj).trans_le (hmax j (Finset.mem_univ _))
  refine ⟨|v i|⁻¹, inv_pos.mpr hi, ?_, i, ?_⟩
  · intro k
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_abs]
    rw [inv_mul_le_iff₀ hi, mul_one]
    exact hmax k (Finset.mem_univ _)
  · simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_abs]
    exact inv_mul_cancel₀ hi.ne'

lemma mixed_direction_has_mixed_coordinate {d : ℕ} (μ : Measure (Row d))
    [IsProbabilityMeasure μ] (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (h0 : 0 < annealed μ 0 (escape v)) (h1 : annealed μ 0 (escape v) < 1) :
    ∃ i : Fin d, 0 < annealed μ 0 (escape (Pi.single i 1)) ∧
      0 < annealed μ 0 (escape (-Pi.single i 1)) := by
  obtain ⟨c,hc,hcn,hcu⟩ := direction_normalization v hv
  have hcv : c • v ≠ 0 := smul_ne_zero hc.ne' hv
  have hp : 0 < annealed μ 0 (escape (c • v)) := by
    rwa [escape_scale_direction v hc]
  have hm : 0 < annealed μ 0 (escape (-(c • v))) := by
    have hpD := positive_nonBacktracking μ (c • v) hp
    have hu : annealed μ 0 (escape (c • v) ∪ escape (-(c • v))) = 1 :=
      (mem_ae_iff_prob_eq_one ((measurableSet_escape _).union (measurableSet_escape _))).mp
        (ae_escape_or_opposite μ hell 0 (c • v) hcv hpD)
    by_contra hh
    have hz : annealed μ 0 (escape (-(c • v))) = 0 := le_antisymm (not_lt.mp hh) bot_le
    have hle := measure_union_le (escape (c • v)) (escape (-(c • v))) (μ := annealed μ 0)
    rw [hu,hz,add_zero,escape_scale_direction v hc] at hle
    exact not_le_of_gt h1 hle
  exact exists_mixed_coordinate μ hell (c • v) hcv hcn hcu hp hm

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

def axisDirection {d : ℕ} (e : Step d) : Fin d → ℝ :=
  Pi.single e.1 (if e.2 then 1 else -1)

def axisHeight {d : ℕ} (e : Step d) (x : Site d) : ℤ :=
  if e.2 then x e.1 else -(x e.1)

lemma height_axisDirection {d : ℕ} (e : Step d) (x : Site d) :
    height (axisDirection e) x = (axisHeight e x : ℝ) := by
  rcases e with ⟨i,b⟩
  cases b <;> simp [height,axisDirection,axisHeight,Pi.single_apply]

lemma axisHeight_zero {d : ℕ} (e : Step d) : axisHeight e 0 = 0 := by
  simp [axisHeight]

lemma axisDirection_ne_zero {d : ℕ} (e : Step d) : axisDirection e ≠ 0 := by
  intro hh
  have h := congr_fun hh e.1
  rcases e with ⟨i,b⟩
  cases b <;> simp [axisDirection] at h

lemma axisDirection_normalized {d : ℕ} (e : Step d) :
    (∀ i, |axisDirection e i| ≤ 1) ∧ ∃ i, |axisDirection e i| = 1 := by
  classical
  constructor
  · intro i
    simp only [axisDirection, Pi.single_apply]
    split_ifs <;> norm_num
  · refine ⟨e.1, ?_⟩
    simp only [axisDirection, Pi.single_eq_same]
    cases e.2 <;> norm_num

lemma axisHeight_add {d : ℕ} (e : Step d) (x y : Site d) :
    axisHeight e (x+y) = axisHeight e x + axisHeight e y := by
  rcases e with ⟨i,b⟩
  cases b <;> simp [axisHeight,add_comm]

lemma axisHeight_step_le {d : ℕ} (e f : Step d) : axisHeight e (stepVector f) ≤ 1 := by
  rcases e with ⟨i,b⟩
  rcases f with ⟨j,c⟩
  cases b <;> cases c <;> simp [axisHeight,stepVector] <;> split_ifs <;> omega

lemma axisHeight_step_ge {d : ℕ} (e f : Step d) : -1 ≤ axisHeight e (stepVector f) := by
  rcases e with ⟨i,b⟩
  rcases f with ⟨j,c⟩
  cases b <;> cases c <;> simp [axisHeight,stepVector] <;> split_ifs <;> omega

lemma axisHeight_nn_le {d : ℕ} (e : Step d) (X : Path d) (hX : nearestNeighbour X) (n : ℕ) :
    axisHeight e (X (n+1)) ≤ axisHeight e (X n) + 1 := by
  obtain ⟨f,hf⟩ := hX n
  rw [hf,axisHeight_add]
  exact add_le_add le_rfl (axisHeight_step_le e f)

lemma axis_recordCount_witness {d : ℕ} (e : Step d) (X : Path d)
    (h0 : axisHeight e (X 0) = 0) (n : ℕ) :
    ∃ j ≤ n, (recordCount (axisDirection e) X n : ℤ) ≤ axisHeight e (X j) := by
  classical
  induction n with
  | zero => exact ⟨0,le_rfl,by simp [recordCount_zero,h0]⟩
  | succ n ih =>
    obtain ⟨j,hj,hcount⟩ := ih
    rw [recordCount_succ]
    by_cases hr : strictRecord (axisDirection e) X (n+1)
    · rw [ite_eq_left hr, Nat.cast_add, Nat.cast_one]
      refine ⟨n+1,le_rfl,?_⟩
      have hh := hr.2 j (by omega)
      simp only [height_axisDirection,Int.cast_lt] at hh
      omega
    · rw [ite_eq_right hr,add_zero]
      exact ⟨j,by omega,hcount⟩

lemma axis_record_height {d : ℕ} (e : Step d) (X : Path d) (n : ℕ)
    (h0 : X 0 = 0) (hX : ∀ i < n, axisHeight e (X (i+1)) ≤ axisHeight e (X i)+1)
    (hr : n = 0 ∨ strictRecord (axisDirection e) X n) :
    axisHeight e (X n) = (recordCount (axisDirection e) X n : ℤ) := by
  have hz : axisHeight e (X 0) = 0 := by rw [h0,axisHeight_zero]
  apply le_antisymm
  · have hs : ∀ i < n, height (axisDirection e) (X (i+1)) ≤ height (axisDirection e) (X i)+1 := by
      intro i hi
      simp only [height_axisDirection]
      exact_mod_cast hX i hi
    have hh := height_le_recordCount (axisDirection e) X n (by rw [h0,height_zero]) hs n le_rfl
    rw [height_axisDirection] at hh
    exact_mod_cast hh
  · obtain ⟨j,hj,hjc⟩ := axis_recordCount_witness e X hz n
    apply hjc.trans
    rcases hr with rfl | hr
    · have : j = 0 := by omega
      simp [this]
    · by_cases he : j = n
      · rw [he]
      · have hh := hr.2 j (by omega)
        simp only [height_axisDirection,Int.cast_lt] at hh
        exact hh.le

lemma integer_first_crossing (f : ℕ → ℤ) (n : ℕ) (a : ℤ)
    (hf : ∀ i < n, f (i+1) ≤ f i+1) (h0 : f 0 ≤ a) (hn : a ≤ f n) :
    ∃ j ≤ n, f j = a ∧ ∀ i < j, f i < a := by
  have hex : ∃ k, a ≤ f k := ⟨n,hn⟩
  let j := Nat.find hex
  have hj : a ≤ f j := Nat.find_spec hex
  have hjn : j ≤ n := Nat.find_min' hex hn
  have hmin : ∀ i < j, f i < a := by
    intro i hi
    exact lt_of_not_ge (Nat.find_min hex hi)
  refine ⟨j,hjn,?_,hmin⟩
  apply le_antisymm _ hj
  by_cases hz : j = 0
  · simpa [hz] using h0
  · have hbelow := hmin (j-1) (by omega)
    have hstep := hf (j-1) (by omega)
    have he : j-1+1 = j := by omega
    rw [he] at hstep
    omega

def reachAxis {d : ℕ} (e : Step d) (H : ℕ) : Set (Path d) :=
  {X | ∃ n, axisHeight e (X n) = H ∧ ∀ i ≤ n, 0 ≤ axisHeight e (X i)}

lemma measurableSet_reachAxis {d : ℕ} (e : Step d) (H : ℕ) : MeasurableSet (reachAxis e H) := by
  simp only [reachAxis,Set.ofPred_exists,Set.ofPred_and,Set.ofPred_forall]
  refine MeasurableSet.iUnion (fun n => (measurableSet_eq_fun
    ((measurable_of_countable (axisHeight e)).comp (measurable_pi_apply n)) measurable_const).inter ?_)
  exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun _ =>
    measurableSet_le measurable_const ((measurable_of_countable (axisHeight e)).comp (measurable_pi_apply i))))

lemma reachRecord_eq_reachAxis {d : ℕ} (e : Step d) (X : Path d)
    (h0 : X 0 = 0) (hX : nearestNeighbour X) (H : ℕ) :
    X ∈ reachRecord (axisDirection e) H ↔ X ∈ reachAxis e H := by
  constructor
  · intro hh
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hh
    refine ⟨n,?_,?_⟩
    · rw [axis_record_height e X n h0 (fun i _ => axisHeight_nn_le e X hX i) hn.1,hn.2.1]
    · intro i hi
      have hh := hn.2.2 i hi
      rw [height_axisDirection] at hh
      exact_mod_cast hh
  · rintro ⟨n,hn,hbelow⟩
    obtain ⟨j,hjn,hj,hmin⟩ := integer_first_crossing (fun i => axisHeight e (X i)) n H
      (fun i _ => axisHeight_nn_le e X hX i) (by simp [h0,axisHeight_zero]) hn.ge
    have hr : j = 0 ∨ strictRecord (axisDirection e) X j := by
      by_cases hz : j = 0
      · exact Or.inl hz
      · refine Or.inr ⟨by omega,fun i hi => ?_⟩
        simp only [height_axisDirection]
        exact_mod_cast (show axisHeight e (X i) < axisHeight e (X j) by rw [hj];exact hmin i hi)
    refine Set.mem_iUnion.mpr ⟨j,hr,?_,?_⟩
    · have hc := axis_record_height e X j h0 (fun i _ => axisHeight_nn_le e X hX i) hr
      rw [hj] at hc
      exact_mod_cast hc.symm
    · intro i hi
      rw [height_axisDirection]
      exact_mod_cast hbelow i (hi.trans hjn)

lemma reachAxis_antitone {d : ℕ} (e : Step d) (X : Path d)
    (h0 : X 0 = 0) (hX : nearestNeighbour X) {m n : ℕ} (hmn : m ≤ n) :
    X ∈ reachAxis e n → X ∈ reachAxis e m := by
  rintro ⟨k,hk,hbelow⟩
  obtain ⟨j,hjk,hj,_⟩ := integer_first_crossing (fun i => axisHeight e (X i)) k m
    (fun i _ => axisHeight_nn_le e X hX i) (by simp [h0,axisHeight_zero])
    (by rw [hk];exact_mod_cast hmn)
  exact ⟨j,hj,fun i hi => hbelow i (hi.trans hjk)⟩

lemma last_record_cut_partition {d : ℕ} (v : Fin d → ℝ) (X : Path d)
    (h0 : X 0 = 0) (hD : X ∈ nonBacktracking v) (N : ℕ) :
    X ∈ ⋃ j ∈ Finset.range (N+1), recordTailEvent v j (noCutBeforeRecord v (N-j)) := by
  classical
  let s := (Finset.range (N+1)).filter (fun j => ∃ n, recordPrefix v j X n ∧
    relativeTail n X ∈ nonBacktracking v)
  have h0s : 0 ∈ s := by
    refine Finset.mem_filter.mpr ⟨by simp,0,⟨Or.inl rfl, recordCount_zero v X,?_⟩,?_⟩
    · intro i hi
      have : i = 0 := by omega
      rw [this,h0,height_zero]
    · intro k
      simpa [relativeTail_apply,height_sub,h0,height_zero] using hD k
  let j := s.max' ⟨0,h0s⟩
  have hjs := s.max'_mem ⟨0,h0s⟩
  obtain ⟨hj, n, hpre, htail⟩ := Finset.mem_filter.mp hjs
  have hjN : j ≤ N := by have := Finset.mem_range.mp hj; omega
  refine Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨hj,Set.mem_iUnion.mpr ⟨n,hpre,?_,htail⟩⟩⟩
  intro m hm
  have hmpos := hm.1.1
  have hcut : trueCut v X (n+m) := (trueCut_relativeTail v X hpre.1 hm.1.1).mp hm
  have hcount := recordCount_relativeTail v X hpre.1 m
  rw [hpre.2.1] at hcount
  by_contra hlt
  have hk : recordCount v X (n+m) ≤ N := by omega
  have hk_mem : recordCount v X (n+m) ∈ s := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),n+m,?_,?_⟩
    · exact ⟨Or.inr hcut.1,rfl,fun i _ => hD i⟩
    · exact (relativeTail_nonBacktracking_iff v X (n+m)).mpr hcut.2
  have hle := s.le_max' (recordCount v X (n+m)) hk_mem
  have hgt := recordCount_strict v X (show n < n+m by omega) hcut.1
  rw [hpre.2.1] at hgt
  exact (not_lt_of_ge hle) hgt

lemma record_tail_sum_eq_one {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (v : Fin d → ℝ) (hp : 0 < annealed μ 0 (nonBacktracking v)) (N : ℕ) :
    ∑ j ∈ Finset.range (N+1), annealed μ 0 (reachRecord v j) *
      conditioned μ v (noCutBeforeRecord v (N-j)) = 1 := by
  let := conditioned_probability μ v hp
  calc
    _ = ∑ j ∈ Finset.range (N+1), conditioned μ v
        (recordTailEvent v j (noCutBeforeRecord v (N-j))) := by
      apply Finset.sum_congr rfl
      intro j _
      exact (recordTail_factorization μ v j (measurableSet_noCutBeforeRecord v (N-j))).symm
    _ = conditioned μ v (⋃ j ∈ Finset.range (N+1),
        recordTailEvent v j (noCutBeforeRecord v (N-j))) := by
      symm
      exact measure_biUnion_finset (recordTailEvent_disjoint v N)
        (fun j _ => measurableSet_recordTailEvent v j (measurableSet_noCutBeforeRecord v (N-j)))
    _ = 1 := by
      apply (mem_ae_iff_prob_eq_one (MeasurableSet.biUnion (Finset.countable_toSet _)
        (fun j _ => measurableSet_recordTailEvent v j (measurableSet_noCutBeforeRecord v (N-j))))).mp
      have h0 := (cond_absolutelyContinuous (s := nonBacktracking v) (μ := annealed μ 0)).ae_le
        (ae_start_and_nearestNeighbour μ 0)
      have hD : ∀ᵐ X ∂conditioned μ v, X ∈ nonBacktracking v :=
        ae_cond_mem (measurableSet_nonBacktracking v)
      filter_upwards [h0,hD] with X hX hXD
      exact last_record_cut_partition v X hX.1 hXD N

noncomputable def axisReachProb {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (e : Step d) (H : ℕ) : ℝ≥0∞ := annealed μ 0 (reachAxis e H)

lemma axisReachProb_eq_record {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (e : Step d) (H : ℕ) : axisReachProb μ e H = annealed μ 0 (reachRecord (axisDirection e) H) := by
  apply measure_congr
  filter_upwards [ae_start_and_nearestNeighbour μ 0] with X hX
  exact propext (reachRecord_eq_reachAxis e X hX.1 hX.2 H).symm

lemma axisReachProb_antitone {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (e : Step d) : Antitone (axisReachProb μ e) := by
  intro m n hmn
  apply measure_mono_ae
  filter_upwards [ae_start_and_nearestNeighbour μ 0] with X hX
  exact reachAxis_antitone e X hX.1 hX.2 hmn

lemma axisReachProb_lower {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d) (H : ℕ) :
    annealed μ 0 (nonBacktracking (axisDirection e)) ≤ axisReachProb μ e H := by
  rw [axisReachProb_eq_record]
  exact reachRecord_mass_ge μ hell (axisDirection e) (axisDirection_ne_zero e) H

lemma axisReachProb_zero {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (e : Step d) : axisReachProb μ e 0 = 1 := by
  apply (mem_ae_iff_prob_eq_one (measurableSet_reachAxis e 0)).mp
  filter_upwards [ae_start_and_nearestNeighbour μ 0] with X hX
  refine ⟨0,by rw [hX.1,axisHeight_zero]; rfl,?_⟩
  intro i hi
  have : i = 0 := by omega
  simp [this,hX.1,axisHeight_zero]

noncomputable def axisWidthTail {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (e : Step d) (H : ℕ) : ℝ≥0∞ :=
  slabLaw μ (axisDirection e) {γ | H < slabRecords (axisDirection e) γ}

lemma axis_renewal_tail_identity {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : 0 < annealed μ 0 (nonBacktracking (axisDirection e))) (N : ℕ) :
    ∑ j ∈ Finset.range (N+1), axisReachProb μ e j * axisWidthTail μ e (N-j) = 1 := by
  simp_rw [axisReachProb_eq_record,axisWidthTail,
    slabRecords_tail μ hell (axisDirection e) (axisDirection_ne_zero e) hp]
  exact record_tail_sum_eq_one μ (axisDirection e) hp N

lemma slabRecords_pos {d : ℕ} (v : Fin d → ℝ) (γ : Word d) (hγ : RegenerationWord v γ) :
    0 < slabRecords v γ := by
  have hr : strictRecord v (wordPath γ) γ.1 :=
    ⟨hγ.1,fun j hj => (hγ.2.2.2.1 j hj).2⟩
  have hh := recordCount_strict v (wordPath γ) hγ.1 hr
  simpa only [recordCount_zero, slabRecords] using hh

lemma axis_slabWidth_eq_records {d : ℕ} (e : Step d) (γ : Word d)
    (hγ : RegenerationWord (axisDirection e) γ) :
    slabWidth (axisDirection e) γ = (slabRecords (axisDirection e) γ : ℝ) := by
  have hh := axis_record_height e (wordPath γ) γ.1 hγ.2.1 (fun j hj => by
    obtain ⟨f,hf⟩ := hγ.2.2.1 j hj
    rw [hf,axisHeight_add]
    exact add_le_add le_rfl (axisHeight_step_le e f))
    (Or.inr ⟨hγ.1,fun j hj => (hγ.2.2.2.1 j hj).2⟩)
  change height (axisDirection e) (wordPath γ γ.1) = _
  rw [height_axisDirection]
  exact_mod_cast hh

lemma axisWidthTail_zero {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : 0 < annealed μ 0 (nonBacktracking (axisDirection e))) : axisWidthTail μ e 0 = 1 := by
  let := slabLaw_probability μ (axisDirection e) hp
  apply (mem_ae_iff_prob_eq_one (measurableSet_lt measurable_const (measurable_of_countable _))).mp
  filter_upwards [ae_slabLaw_regeneration μ hell (axisDirection e) (axisDirection_ne_zero e) hp] with γ hγ
  exact slabRecords_pos (axisDirection e) γ hγ

lemma axisWidthTail_antitone {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (e : Step d) : Antitone (axisWidthTail μ e) := by
  intro m n hmn
  exact measure_mono (fun _ hn => hmn.trans_lt hn)

lemma renewal_step_bound (u F : ℕ → ℝ) (hu : Antitone u) (hF : ∀ n, 0 ≤ F n)
    (hu0 : u 0 = 1) (hF0 : F 0 = 1)
    (hid : ∀ n, ∑ j ∈ Finset.range (n+1), u j * F (n-j) = 1) (n : ℕ) :
    u n - u (n+1) ≤ F (n+1) := by
  have hid' := hid (n+1)
  rw [Finset.sum_range_succ'] at hid'
  simp only [Nat.succ_sub_succ_eq_sub,hu0,one_mul,Nat.sub_zero] at hid'
  have heq : ∑ j ∈ Finset.range (n+1), (u j-u (j+1))*F (n-j) = F (n+1) := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib,hid n]
    linarith
  have hle := Finset.single_le_sum (s := Finset.range (n+1))
    (f := fun j => (u j-u (j+1))*F (n-j))
    (fun j _ => mul_nonneg (sub_nonneg.mpr (hu (Nat.le_succ j))) (hF (n-j)))
    (show n ∈ Finset.range (n+1) by simp)
  simpa only [Nat.sub_self,hF0,mul_one,heq] using hle

lemma renewal_interval_bound (u F : ℕ → ℝ) (hu : Antitone u) (hF : Antitone F)
    (hstep : ∀ n, u n-u (n+1) ≤ F (n+1)) {n m : ℕ} (hnm : n ≤ m) :
    0 ≤ u n-u m ∧ u n-u m ≤ (m-n)*F n := by
  refine ⟨sub_nonneg.mpr (hu hnm),?_⟩
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hnm
  simp only [Nat.cast_add, add_sub_cancel_left]
  induction k with
  | zero => simp
  | succ k ih =>
    have ih := ih (by omega)
    have hs := (hstep (n+k)).trans (hF (show n ≤ n+k+1 by omega))
    have he : n+(k+1) = n+k+1 := by omega
    rw [he,Nat.cast_add,Nat.cast_one]
    nlinarith

lemma axis_renewal_identity_real {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : 0 < annealed μ 0 (nonBacktracking (axisDirection e))) (N : ℕ) :
    ∑ j ∈ Finset.range (N+1), (axisReachProb μ e j).toReal *
      (axisWidthTail μ e (N-j)).toReal = 1 := by
  let := slabLaw_probability μ (axisDirection e) hp
  have h := congrArg ENNReal.toReal (axis_renewal_tail_identity μ hell e hp N)
  rw [ENNReal.toReal_sum (f := fun j => axisReachProb μ e j * axisWidthTail μ e (N-j))
    (fun j _ => ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))] at h
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_one] using h

lemma axis_renewal_tail_bound {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : 0 < annealed μ 0 (nonBacktracking (axisDirection e))) {n m : ℕ} (hnm : n ≤ m) :
    0 ≤ (axisReachProb μ e n).toReal-(axisReachProb μ e m).toReal ∧
      (axisReachProb μ e n).toReal-(axisReachProb μ e m).toReal ≤
        (m-n)*(axisWidthTail μ e n).toReal := by
  let := slabLaw_probability μ (axisDirection e) hp
  have hu : Antitone (fun n => (axisReachProb μ e n).toReal) :=
    fun _ _ h => ENNReal.toReal_mono (measure_ne_top _ _) (axisReachProb_antitone μ e h)
  have hF : Antitone (fun n => (axisWidthTail μ e n).toReal) :=
    fun _ _ h => ENNReal.toReal_mono (measure_ne_top _ _) (axisWidthTail_antitone μ e h)
  apply renewal_interval_bound _ _ hu hF _ hnm
  intro k
  apply renewal_step_bound _ _ hu (fun _ => ENNReal.toReal_nonneg) _ _
    (axis_renewal_identity_real μ hell e hp) k
  · rw [axisReachProb_zero,ENNReal.toReal_one]
  · rw [axisWidthTail_zero μ hell e hp,ENNReal.toReal_one]

lemma summable_axisWidthTail {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : 0 < annealed μ 0 (nonBacktracking (axisDirection e))) :
    Summable (fun n => (axisWidthTail μ e n).toReal) := by
  apply ENNReal.summable_toReal
  change (∑' n, slabLaw μ (axisDirection e) {γ | n < slabRecords (axisDirection e) γ}) ≠ ⊤
  rw [← lintegral_nat_tail _ _ (measurable_of_countable _)]
  exact ((lintegral_slabRecords_le μ hell (axisDirection e) (axisDirection_ne_zero e) hp).trans_lt
    (ENNReal.inv_lt_top.mpr hp)).ne

lemma summable_dyadic_axisWidthTail {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : 0 < annealed μ 0 (nonBacktracking (axisDirection e))) :
    Summable (fun l => (2:ℝ)^l*(axisWidthTail μ e (2^l)).toReal) := by
  let := slabLaw_probability μ (axisDirection e) hp
  apply (summable_condensed_iff_of_nonneg (fun _ => ENNReal.toReal_nonneg) (fun _ _ _ h =>
    ENNReal.toReal_mono (measure_ne_top _ _) (axisWidthTail_antitone μ e h))).mpr
  exact summable_axisWidthTail μ hell e hp

lemma iterated_cutSuffix_eq_relativeTail {d : ℕ} (v : Fin d → ℝ) (X : Path d)
    (h0 : X 0 = 0) (k : ℕ) : (cutSuffix v)^[k] X = relativeTail (slabTime v X k) X := by
  funext n
  exact iterated_cutSuffix v X h0 k n

lemma slabTime_boundary {d : ℕ} (v : Fin d → ℝ) (X : Path d) (hX : GoodSlabPath v X)
    (k : ℕ) : slabTime v X k = 0 ∨ trueCut v X (slabTime v X k) := by
  induction k with
  | zero => exact Or.inl (slabTime_zero v X)
  | succ k ih =>
    right
    have hp : 0 < firstCutTime v ((cutSuffix v)^[k] X) := (hX.2 k).1
    have hc := ((firstCutTime_eq_pos_iff v ((cutSuffix v)^[k] X) hp).mp rfl).1
    have hc' : trueCut v (relativeTail (slabTime v X k) X) (slabs v X k).1 := by
      rw [← iterated_cutSuffix_eq_relativeTail v X hX.1 k]
      exact hc
    rw [slabTime_succ]
    exact (trueCut_relativeTail v X (ih.imp_right And.left) hp).mp hc'

lemma trueCut_eq_slabTime {d : ℕ} (v : Fin d → ℝ) (X : Path d) (hX : GoodSlabPath v X)
    {n : ℕ} (hn : trueCut v X n) : ∃ k, slabTime v X k = n := by
  obtain ⟨k,hkn,hnk⟩ := slab_location v X hX n
  refine ⟨k,?_⟩
  by_contra hne
  have hlt : slabTime v X k < n := lt_of_le_of_ne hkn hne
  have hc : trueCut v (relativeTail (slabTime v X k) X) (n-slabTime v X k) := by
    apply (trueCut_relativeTail v X ((slabTime_boundary v X hX k).imp_right And.left)
      (Nat.sub_pos_of_lt hlt)).mpr
    simpa only [Nat.add_sub_of_le hkn] using hn
  rw [← iterated_cutSuffix_eq_relativeTail v X hX.1 k] at hc
  have hp : 0 < firstCutTime v ((cutSuffix v)^[k] X) := (hX.2 k).1
  have hm := ((firstCutTime_eq_pos_iff v ((cutSuffix v)^[k] X) hp).mp rfl).2
  apply hm (n-slabTime v X k) _ hc
  rw [slabTime_succ] at hnk
  change n-slabTime v X k < (slabs v X k).1
  omega

lemma recordCount_slabTime {d : ℕ} (v : Fin d → ℝ) (X : Path d) (hX : GoodSlabPath v X)
    (k : ℕ) : recordCount v X (slabTime v X k) =
      ∑ i ∈ Finset.range k, slabRecords v (slabs v X i) := by
  induction k with
  | zero => simp [slabTime_zero,recordCount_zero]
  | succ k ih =>
    rw [slabTime_succ,recordCount_relativeTail v X
      ((slabTime_boundary v X hX k).imp_right And.left),ih,Finset.sum_range_succ]
    congr 1
    rw [← iterated_cutSuffix_eq_relativeTail v X hX.1 k]
    exact (slabRecords_firstWord v ((cutSuffix v)^[k] X)).symm

def tapeCut {d : ℕ} (v : Fin d → ℝ) (H : ℕ) : Set (ℕ → Word d) :=
  {Z | ∃ k, ∑ i ∈ Finset.range k, slabRecords v (Z i) = H}

lemma measurableSet_tapeCut {d : ℕ} (v : Fin d → ℝ) (H : ℕ) :
    MeasurableSet (tapeCut v H) := by
  simp only [tapeCut,Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro k
  exact measurableSet_eq_fun (Finset.measurable_sum _ (fun i _ =>
    (measurable_of_countable (slabRecords v)).comp (measurable_pi_apply i))) measurable_const

lemma tapeCut_iff_recordTailEvent {d : ℕ} (v : Fin d → ℝ) (X : Path d)
    (hX : GoodSlabPath v X) (H : ℕ) :
    slabs v X ∈ tapeCut v H ↔ X ∈ recordTailEvent v H Set.univ := by
  have hD : X ∈ nonBacktracking v := fun t => goodSlabPath_height_nonneg v X hX t
  constructor
  · rintro ⟨k,hk⟩
    have hb := slabTime_boundary v X hX k
    refine Set.mem_iUnion.mpr ⟨slabTime v X k,⟨hb.imp_right And.left,?_,fun i _ => hD i⟩,
      Set.mem_univ _,?_⟩
    · rw [recordCount_slabTime v X hX k,hk]
    · rcases hb with hz | hc
      · intro i
        simpa [relativeTail_apply,hz,hX.1,height_sub,height_zero] using hD i
      · exact (relativeTail_nonBacktracking_iff v X _).mpr hc.2
  · intro ht
    obtain ⟨n,hn,_,hD'⟩ := Set.mem_iUnion.mp ht
    have hncut : n = 0 ∨ trueCut v X n := hn.1.imp_right
      (fun hr => ⟨hr,(relativeTail_nonBacktracking_iff v X n).mp hD'⟩)
    have hk : ∃ k, slabTime v X k = n := by
      rcases hncut with hz | hc
      · exact ⟨0,(slabTime_zero v X).trans hz.symm⟩
      · exact trueCut_eq_slabTime v X hX hc
    obtain ⟨k,rfl⟩ := hk
    refine ⟨k,?_⟩
    rw [← recordCount_slabTime v X hX k]
    exact hn.2.1

lemma tapeCut_mass {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) (H : ℕ) :
    Measure.infinitePi (fun _ : ℕ => slabLaw μ v) (tapeCut v H) =
      annealed μ 0 (reachRecord v H) := by
  let := conditioned_probability μ v hp
  rw [← slabs_map_eq_infinitePi μ hell v hv hp,
    Measure.map_apply (measurable_slabs v) (measurableSet_tapeCut v H)]
  have he : conditioned μ v (slabs v ⁻¹' tapeCut v H) =
      conditioned μ v (recordTailEvent v H Set.univ) := by
    apply measure_congr
    filter_upwards [ae_goodSlabPath μ hell v hv hp] with X hX
    exact propext (tapeCut_iff_recordTailEvent v X hX H)
  rw [he,recordTail_factorization μ v H MeasurableSet.univ,measure_univ,mul_one]

lemma axis_tapeCut_mass {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : 0 < annealed μ 0 (nonBacktracking (axisDirection e))) (H : ℕ) :
    Measure.infinitePi (fun _ : ℕ => slabLaw μ (axisDirection e)) (tapeCut (axisDirection e) H) =
      axisReachProb μ e H := by
  rw [tapeCut_mass μ hell _ (axisDirection_ne_zero e) hp,axisReachProb_eq_record]

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

abbrev TapeList (α : Type*) := Σ n : ℕ, Fin n → α

instance tapeListMeasurableSpace (α : Type*) : MeasurableSpace (TapeList α) := ⊤
instance tapeListMeasurableSingletonClass (α : Type*) : MeasurableSingletonClass (TapeList α) :=
  ⟨fun _ => trivial⟩

def tapePrefix {α : Type*} (n : ℕ) (Z : ℕ → α) : TapeList α := ⟨n,fun i => Z i⟩

def tapeCylinder {α : Type*} (a : TapeList α) : Set (ℕ → α) :=
  {Z | ∀ i : Fin a.1, Z i = a.2 i}

lemma measurableSet_tapeCylinder {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (a : TapeList α) : MeasurableSet (tapeCylinder a) := by
  simp only [tapeCylinder,Set.ofPred_forall]
  exact MeasurableSet.iInter (fun i => (measurableSet_singleton (a.2 i)).preimage (measurable_pi_apply (i : ℕ)))

lemma tapePrefix_eq_iff {α : Type*} (n : ℕ) (Z : ℕ → α) (a : TapeList α) :
    tapePrefix n Z = a ↔ n = a.1 ∧ Z ∈ tapeCylinder a := by
  rcases a with ⟨m,a⟩
  constructor
  · intro h
    have hn := congrArg Sigma.fst h
    change n = m at hn
    subst m
    have ha : (fun i : Fin n => Z i) = a := by simpa [tapePrefix] using h
    exact ⟨rfl,fun i => congrFun ha i⟩
  · rintro ⟨rfl,ha⟩
    exact congrArg (Sigma.mk n) (funext ha)

lemma measurable_tapePrefix {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (n : ℕ) : Measurable (tapePrefix (α := α) n) := by
  apply measurable_to_countable'
  intro a
  have he : tapePrefix n ⁻¹' {a} = {Z : ℕ → α | n = a.1} ∩ tapeCylinder a := by
    ext Z; exact tapePrefix_eq_iff n Z a
  rw [he]
  exact (MeasurableSet.const _).inter (measurableSet_tapeCylinder a)

lemma tapeCylinder_mass {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (ν : Measure α) [IsProbabilityMeasure ν] (a : TapeList α) :
    Measure.infinitePi (fun _ : ℕ => ν) (tapeCylinder a) = ∏ i : Fin a.1, ν {a.2 i} := by
  have hm := Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => ν)
    (f := fun i : Fin a.1 => (i : ℕ)) Fin.val_injective
  have he : tapeCylinder a = (fun Z (i : Fin a.1) => Z i) ⁻¹' {a.2} := by
    ext Z
    simp only [tapeCylinder,Set.mem_ofPred_eq,Set.mem_preimage,Set.mem_singleton_iff,funext_iff]
  rw [he,← Measure.map_apply (by fun_prop) (measurableSet_singleton _),hm,
    Measure.infinitePi_singleton_of_fintype]

def tapeHeight {α : Type*} (L : α → ℕ) (Z : ℕ → α) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, L (Z i)

def listHeight {α : Type*} (L : α → ℕ) (a : TapeList α) : ℕ :=
  ∑ i : Fin a.1, L (a.2 i)

lemma listHeight_prefix {α : Type*} (L : α → ℕ) (Z : ℕ → α) (n : ℕ) :
    listHeight L (tapePrefix n Z) = tapeHeight L Z n := by
  exact Fin.sum_univ_eq_sum_range (fun i => L (Z i)) n

lemma tapeHeight_mono {α : Type*} (L : α → ℕ) (Z : ℕ → α) : Monotone (tapeHeight L Z) := by
  apply monotone_nat_of_le_succ
  intro n
  simp only [tapeHeight,Finset.sum_range_succ]
  omega

lemma tapeHeight_strictMono {α : Type*} (L : α → ℕ) (Z : ℕ → α)
    (hZ : ∀ i, 0 < L (Z i)) : StrictMono (tapeHeight L Z) := by
  apply strictMono_nat_of_lt_succ
  intro n
  simp only [tapeHeight,Finset.sum_range_succ]
  have := hZ n
  omega

lemma le_tapeHeight {α : Type*} (L : α → ℕ) (Z : ℕ → α)
    (hZ : ∀ i, 0 < L (Z i)) (n : ℕ) : n ≤ tapeHeight L Z n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    simp only [tapeHeight,Finset.sum_range_succ] at *
    have := hZ n
    omega

lemma measurable_tapeHeight {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (L : α → ℕ) (n : ℕ) : Measurable (fun Z => tapeHeight L Z n) := by
  exact Finset.measurable_sum _ (fun i _ => (measurable_of_countable L).comp (measurable_pi_apply (i : ℕ)))

noncomputable def cutListIndex {α : Type*} (L : α → ℕ) (H : ℕ) (Z : ℕ → α) : ℕ := by
  classical
  exact Nat.findGreatest (fun n => tapeHeight L Z n = H) H

lemma measurable_cutListIndex {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (L : α → ℕ) (H : ℕ) : Measurable (cutListIndex L H) := by
  classical
  apply measurable_findGreatest
  intro n _
  exact measurableSet_eq_fun (measurable_tapeHeight L n) measurable_const

lemma cutListIndex_eq {α : Type*} (L : α → ℕ) (H : ℕ) (Z : ℕ → α)
    (hZ : ∀ i, 0 < L (Z i)) {n : ℕ} (hn : tapeHeight L Z n = H) : cutListIndex L H Z = n := by
  classical
  have hnH : n ≤ H := hn ▸ le_tapeHeight L Z hZ n
  have he : tapeHeight L Z (cutListIndex L H Z) = H :=
    Nat.findGreatest_spec (P := fun n => tapeHeight L Z n = H) hnH hn
  exact (tapeHeight_strictMono L Z hZ).injective (he.trans hn.symm)

noncomputable def cutList {α : Type*} (L : α → ℕ) (H : ℕ) (Z : ℕ → α) : TapeList α :=
  tapePrefix (cutListIndex L H Z) Z

lemma measurable_cutList {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (L : α → ℕ) (H : ℕ) : Measurable (cutList L H) := by
  apply measurable_to_countable'
  intro a
  have he : cutList L H ⁻¹' {a} = {Z | cutListIndex L H Z = a.1} ∩ tapeCylinder a := by
    ext Z; exact tapePrefix_eq_iff (cutListIndex L H Z) Z a
  rw [he]
  exact (measurableSet_eq_fun (measurable_cutListIndex L H) measurable_const).inter
    (measurableSet_tapeCylinder a)

def renewalCut {α : Type*} (L : α → ℕ) (H : ℕ) : Set (ℕ → α) :=
  {Z | ∃ n, tapeHeight L Z n = H}

lemma measurableSet_renewalCut {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (L : α → ℕ) (H : ℕ) : MeasurableSet (renewalCut L H) := by
  simp only [renewalCut,Set.ofPred_exists]
  exact MeasurableSet.iUnion (fun n => measurableSet_eq_fun (measurable_tapeHeight L n) measurable_const)

lemma cutList_atom_iff {α : Type*} (L : α → ℕ) (H : ℕ) (Z : ℕ → α)
    (hZ : ∀ i, 0 < L (Z i)) (a : TapeList α) :
    (Z ∈ renewalCut L H ∧ cutList L H Z = a) ↔
      (listHeight L a = H ∧ Z ∈ tapeCylinder a) := by
  constructor
  · rintro ⟨⟨n,hn⟩,ha⟩
    have hi := cutListIndex_eq L H Z hZ hn
    have ha' : tapePrefix n Z = a := by simpa only [cutList,hi] using ha
    refine ⟨?_,((tapePrefix_eq_iff n Z a).mp ha').2⟩
    rw [← ha',listHeight_prefix,hn]
  · rintro ⟨hH,ha⟩
    have he : tapePrefix a.1 Z = a := (tapePrefix_eq_iff _ _ _).mpr ⟨rfl,ha⟩
    have hh : tapeHeight L Z a.1 = H := by rw [← listHeight_prefix,he,hH]
    exact ⟨⟨a.1,hh⟩,by rw [cutList,cutListIndex_eq L H Z hZ hh,he]⟩

lemma ae_tape_prop {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
    (p : α → Prop) (hp : MeasurableSet {a | p a}) (h : ∀ᵐ a ∂ν, p a) :
    ∀ᵐ Z ∂Measure.infinitePi (fun _ : ℕ => ν), ∀ i, p (Z i) := by
  rw [ae_all_iff]
  intro i
  apply (ae_map_iff (measurable_pi_apply i).aemeasurable hp).mp
  rw [Measure.infinitePi_map_eval]
  exact h

noncomputable def bridgeListMeasure {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (L : α → ℕ) (H : ℕ) : Measure (TapeList α) :=
  ((Measure.infinitePi (fun _ : ℕ => ν)).restrict (renewalCut L H)).map (cutList L H)

lemma bridgeListMeasure_mass {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Measure α) [IsProbabilityMeasure ν]
    (L : α → ℕ) (H : ℕ) :
    bridgeListMeasure ν L H Set.univ = Measure.infinitePi (fun _ : ℕ => ν) (renewalCut L H) := by
  rw [bridgeListMeasure,Measure.map_apply (measurable_cutList L H) MeasurableSet.univ]
  simp

lemma bridgeListMeasure_atom {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Measure α) [IsProbabilityMeasure ν]
    (L : α → ℕ) (hL : ∀ᵐ a ∂ν, 0 < L a) (H : ℕ) (a : TapeList α) :
    bridgeListMeasure ν L H {a} =
      if listHeight L a = H then ∏ i : Fin a.1, ν {a.2 i} else 0 := by
  classical
  rw [bridgeListMeasure,Measure.map_apply (measurable_cutList L H) (measurableSet_singleton _),
    Measure.restrict_apply ((measurable_cutList L H) (measurableSet_singleton _))]
  have hZ := ae_tape_prop ν (fun x => 0 < L x)
    (measurableSet_lt measurable_const (measurable_of_countable L)) hL
  by_cases hH : listHeight L a = H
  · rw [ite_eq_left hH,← tapeCylinder_mass ν a]
    apply measure_congr
    filter_upwards [hZ] with Z hZ
    apply propext
    constructor
    · intro h
      exact ((cutList_atom_iff L H Z hZ a).mp ⟨h.2,h.1⟩).2
    · intro h
      have hh := (cutList_atom_iff L H Z hZ a).mpr ⟨hH,h⟩
      exact ⟨hh.2,hh.1⟩
  · rw [ite_eq_right hH]
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hZ] with Z hZ hm
    exact hH ((cutList_atom_iff L H Z hZ a).mp ⟨hm.2,hm.1⟩).1

def reverseTapeList {α : Type*} (a : TapeList α) : TapeList α := ⟨a.1,fun i => a.2 i.rev⟩

lemma reverseTapeList_involutive {α : Type*} : Function.Involutive (reverseTapeList (α := α)) := by
  rintro ⟨n,a⟩
  simp only [reverseTapeList,Fin.rev_rev]

lemma listHeight_reverse {α : Type*} (L : α → ℕ) (a : TapeList α) :
    listHeight L (reverseTapeList a) = listHeight L a := by
  exact Equiv.sum_comp Fin.revPerm (fun i => L (a.2 i))

lemma listProduct_reverse {α M : Type*} [CommMonoid M] (f : α → M) (a : TapeList α) :
    (∏ i : Fin (reverseTapeList a).1, f ((reverseTapeList a).2 i)) = ∏ i : Fin a.1, f (a.2 i) := by
  exact Equiv.prod_comp Fin.revPerm (fun i => f (a.2 i))

lemma bridgeListMeasure_reverse {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Measure α) [IsProbabilityMeasure ν]
    (L : α → ℕ) (hL : ∀ᵐ a ∂ν, 0 < L a) (H : ℕ) :
    (bridgeListMeasure ν L H).map reverseTapeList = bridgeListMeasure ν L H := by
  apply Measure.ext_of_singleton
  intro a
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have he : reverseTapeList ⁻¹' {a} = {reverseTapeList a} := by
    ext b
    exact reverseTapeList_involutive.eq_iff
  rw [he,bridgeListMeasure_atom ν L hL H _,bridgeListMeasure_atom ν L hL H _,
    listHeight_reverse,listProduct_reverse (fun x => ν {x}) a]

noncomputable def bridgeListLaw {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (L : α → ℕ) (H : ℕ) : Measure (TapeList α) :=
  (Measure.infinitePi (fun _ : ℕ => ν) (renewalCut L H))⁻¹ • bridgeListMeasure ν L H

lemma bridgeListLaw_probability {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Measure α) [IsProbabilityMeasure ν]
    (L : α → ℕ) (H : ℕ)
    (hH : Measure.infinitePi (fun _ : ℕ => ν) (renewalCut L H) ≠ 0) :
    IsProbabilityMeasure (bridgeListLaw ν L H) := by
  constructor
  rw [bridgeListLaw,Measure.smul_apply,smul_eq_mul,bridgeListMeasure_mass,
    ENNReal.inv_mul_cancel hH (measure_ne_top _ _)]

lemma bridgeListLaw_atom {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Measure α) [IsProbabilityMeasure ν]
    (L : α → ℕ) (hL : ∀ᵐ a ∂ν, 0 < L a) (H : ℕ) (a : TapeList α)
    (ha : listHeight L a = H) : bridgeListLaw ν L H {a} =
      (Measure.infinitePi (fun _ : ℕ => ν) (renewalCut L H))⁻¹ * ∏ i : Fin a.1, ν {a.2 i} := by
  rw [bridgeListLaw,Measure.smul_apply,smul_eq_mul,bridgeListMeasure_atom ν L hL H a,ite_eq_left ha]

lemma bridgeListLaw_reverse {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Measure α) [IsProbabilityMeasure ν]
    (L : α → ℕ) (hL : ∀ᵐ a ∂ν, 0 < L a) (H : ℕ) :
    (bridgeListLaw ν L H).map reverseTapeList = bridgeListLaw ν L H := by
  rw [bridgeListLaw,Measure.map_smul,
    bridgeListMeasure_reverse ν L hL H]

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

abbrev TwoTape (α : Type*) := (Bool × ℕ) → α
abbrev TwoTapeList (α : Type*) := Bool → TapeList α

noncomputable def twoTapeLaw {α : Type*} [MeasurableSpace α]
    (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)] : Measure (TwoTape α) :=
  Measure.infinitePi (fun i => ν i.1)

def twoPrefix {α : Type*} (n : Bool → ℕ) (Z : TwoTape α) : TwoTapeList α :=
  fun b => tapePrefix (n b) (fun i => Z (b,i))

def twoCylinder {α : Type*} (a : TwoTapeList α) : Set (TwoTape α) :=
  {Z | ∀ b, ∀ i : Fin (a b).1, Z (b,i) = (a b).2 i}

lemma measurableSet_twoCylinder {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (a : TwoTapeList α) : MeasurableSet (twoCylinder a) := by
  simp only [twoCylinder,Set.ofPred_forall]
  exact MeasurableSet.iInter (fun b => MeasurableSet.iInter (fun i =>
    (measurableSet_singleton ((a b).2 i)).preimage (measurable_pi_apply (b,(i : ℕ)))))

lemma measurable_twoPrefix {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (n : Bool → ℕ) : Measurable (twoPrefix (α := α) n) := by
  exact Measurable.of_eval (fun b => (measurable_tapePrefix (n b)).comp (by fun_prop))

def twoShift {α : Type*} (n : Bool → ℕ) (Z : TwoTape α) : TwoTape α :=
  fun i => Z (i.1,n i.1+i.2)

lemma measurable_twoShift {α : Type*} [MeasurableSpace α] (n : Bool → ℕ) :
    Measurable (twoShift (α := α) n) := by
  exact Measurable.of_eval (fun i => measurable_pi_apply _)

lemma twoShift_law {α : Type*} [MeasurableSpace α] (ν : Bool → Measure α)
    [∀ b, IsProbabilityMeasure (ν b)] (n : Bool → ℕ) :
    (twoTapeLaw ν).map (twoShift n) = twoTapeLaw ν := by
  apply Measure.map_infinitePi_infinitePi_of_inj
  intro i j h
  have hb := congrArg Prod.fst h
  have hn := congrArg Prod.snd h
  cases i with | mk b i =>
    cases j with | mk c j =>
      simp only [Prod.mk.injEq] at hb hn ⊢
      subst c
      exact ⟨rfl,Nat.add_left_cancel hn⟩

lemma twoExtract_law {α : Type*} [MeasurableSpace α] (ν : Bool → Measure α)
    [∀ b, IsProbabilityMeasure (ν b)] (b : Bool) :
    (twoTapeLaw ν).map (fun Z i => Z (b,i)) = Measure.infinitePi (fun _ : ℕ => ν b) := by
  exact Measure.map_infinitePi_infinitePi_of_inj (fun _ _ h => congrArg Prod.snd h)

lemma ae_twoTape_prop {α : Type*} [MeasurableSpace α] (ν : Bool → Measure α)
    [∀ b, IsProbabilityMeasure (ν b)] (p : Bool → α → Prop)
    (hp : ∀ b, MeasurableSet {a | p b a}) (h : ∀ b, ∀ᵐ a ∂ν b, p b a) :
    ∀ᵐ Z ∂twoTapeLaw ν, ∀ b i, p b (Z (b,i)) := by
  rw [ae_all_iff]
  intro b
  apply ae_of_ae_map (μ := twoTapeLaw ν) (f := fun Z i => Z (b,i))
    (p := fun Z => ∀ i, p b (Z i))
    ((Measurable.of_eval (fun i => measurable_pi_apply (b,i))).aemeasurable)
  rw [twoExtract_law]
  exact ae_tape_prop (ν b) (p b) (hp b) (h b)

abbrev coordSigma {ι α : Type*} [MeasurableSpace α] (s : Set ι) : MeasurableSpace (ι → α) :=
  ⨆ i ∈ s, MeasurableSpace.comap (fun Z : ι → α => Z i) inferInstance

lemma measurable_coordEval {ι α : Type*} [MeasurableSpace α] {s : Set ι} {i : ι} (hi : i ∈ s) :
    @Measurable (ι → α) α (coordSigma s) _ (fun Z => Z i) :=
  measurable_iff_comap_le.mpr (le_iSup₂_of_le i hi le_rfl)

lemma two_prefix_suffix_independent {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (n : Bool → ℕ) :
    IndepFun (fun Z (i : Σ b : Bool, Fin (n b)) => Z (i.1,i.2)) (twoShift n) (twoTapeLaw ν) := by
  have hS : @Measurable (TwoTape α) ((Σ b : Bool, Fin (n b)) → α)
      (coordSigma {i | i.2 < n i.1}) _ (fun Z i => Z (i.1,i.2)) := by
    let : MeasurableSpace (TwoTape α) := coordSigma {i | i.2 < n i.1}
    exact Measurable.of_eval (fun i => measurable_coordEval i.2.isLt)
  have hT : @Measurable (TwoTape α) (TwoTape α)
      (coordSigma {i | n i.1 ≤ i.2}) _ (twoShift n) := by
    let : MeasurableSpace (TwoTape α) := coordSigma {i | n i.1 ≤ i.2}
    exact Measurable.of_eval (fun i => measurable_coordEval (Nat.le_add_right (n i.1) i.2))
  have hd : Disjoint {i : Bool × ℕ | i.2 < n i.1} {i | n i.1 ≤ i.2} := by
    apply Set.disjoint_left.mpr
    intro i hi hj
    exact (not_lt_of_ge (show n i.1 ≤ i.2 from hj)) (show i.2 < n i.1 from hi)
  have hind := indep_iSup_of_disjoint (fun i : Bool × ℕ => (measurable_pi_apply (X := fun _ => α) i).comap_le)
    (iIndepFun_infinitePi (P := fun i : Bool × ℕ => ν i.1) (X := fun _ x => x) (fun _ => measurable_id)) hd
  exact (IndepFun_iff_Indep _ _ _).mpr (indep_of_indep_of_le hind hS.comap_le hT.comap_le)

lemma twoCylinder_mass {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)] (a : TwoTapeList α) :
    twoTapeLaw ν (twoCylinder a) = ∏ b : Bool, ∏ i : Fin (a b).1, ν b {(a b).2 i} := by
  classical
  let f : (Σ b : Bool, Fin (a b).1) → Bool × ℕ := fun i => (i.1,i.2)
  have hf : Function.Injective f := by
    rintro ⟨b,i⟩ ⟨c,j⟩ h
    have hb := congrArg Prod.fst h
    change b = c at hb
    subst c
    have hi := congrArg Prod.snd h
    simp only [f] at hi
    exact congrArg (Sigma.mk b) (Fin.ext hi)
  have hm := Measure.map_infinitePi_infinitePi_of_inj (P := fun i : Bool × ℕ => ν i.1) hf
  have he : (fun Z i => Z (f i)) ⁻¹' {fun i : Σ b : Bool, Fin (a b).1 => (a i.1).2 i.2} = twoCylinder a := by
    ext Z
    simp only [Set.mem_preimage,Set.mem_singleton_iff,funext_iff, twoCylinder, Set.mem_ofPred_eq,
      Sigma.forall,f]
  rw [← he,← Measure.map_apply (by fun_prop) (measurableSet_singleton _),twoTapeLaw,hm]
  rw [Measure.infinitePi_singleton_of_fintype]
  exact Fintype.prod_sigma _

lemma twoCylinder_suffix_factorization {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (a : TwoTapeList α) (E : Set (TwoTape α)) (hE : MeasurableSet E) :
    twoTapeLaw ν {Z | Z ∈ twoCylinder a ∧ twoShift (fun b => (a b).1) Z ∈ E} =
      (∏ b : Bool, ∏ i : Fin (a b).1, ν b {(a b).2 i}) * twoTapeLaw ν E := by
  have hh := (two_prefix_suffix_independent ν (fun b => (a b).1)).measure_inter_preimage_eq_mul
    {fun i : Σ b : Bool, Fin (a b).1 => (a i.1).2 i.2} E (measurableSet_singleton _) hE
  have hc : (fun Z (i : Σ b : Bool, Fin (a b).1) => Z (i.1,i.2)) ⁻¹'
      {fun i : Σ b : Bool, Fin (a b).1 => (a i.1).2 i.2} = twoCylinder a := by
    ext Z
    simp only [Set.mem_preimage,Set.mem_singleton_iff,funext_iff,twoCylinder,Set.mem_ofPred_eq,Sigma.forall]
  rw [hc,twoCylinder_mass ν a,← Measure.map_apply (measurable_twoShift _) hE,twoShift_law] at hh
  exact hh

lemma tapeHeight_add {α : Type*} (L : α → ℕ) (Z : ℕ → α) (n m : ℕ) :
    tapeHeight L Z (n+m) = tapeHeight L Z n + tapeHeight L (fun i => Z (n+i)) m := by
  exact Finset.sum_range_add (fun i => L (Z i)) n m

lemma renewalCut_add_iff {α : Type*} (L : α → ℕ) (Z : ℕ → α)
    (hZ : ∀ i, 0 < L (Z i)) {n H : ℕ} (hn : tapeHeight L Z n = H) (J : ℕ) :
    Z ∈ renewalCut L (H+J) ↔ (fun i => Z (n+i)) ∈ renewalCut L J := by
  constructor
  · rintro ⟨k,hk⟩
    have hnk : n ≤ k := (tapeHeight_strictMono L Z hZ).le_iff_le.mp (by omega)
    obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hnk
    refine ⟨j,?_⟩
    rw [tapeHeight_add,hn] at hk
    omega
  · rintro ⟨j,hj⟩
    exact ⟨n+j,by rw [tapeHeight_add,hn,hj]⟩

def commonCut {α : Type*} (L : Bool → α → ℕ) (H : ℕ) : Set (TwoTape α) :=
  {Z | ∀ b, (fun i => Z (b,i)) ∈ renewalCut (L b) H}

lemma measurableSet_commonCut {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (L : Bool → α → ℕ) (H : ℕ) : MeasurableSet (commonCut L H) := by
  simp only [commonCut,Set.ofPred_forall]
  exact MeasurableSet.iInter (fun b => (measurableSet_renewalCut (L b) H).preimage (by fun_prop))

lemma commonCut_zero {α : Type*} (L : Bool → α → ℕ) : commonCut L 0 = Set.univ := by
  ext Z; simp only [commonCut,Set.mem_ofPred_eq,Set.mem_univ,iff_true]
  intro b
  exact ⟨0,rfl⟩

noncomputable def commonCutIndices {α : Type*} (L : Bool → α → ℕ) (H : ℕ) (Z : TwoTape α) : Bool → ℕ :=
  fun b => cutListIndex (L b) H (fun i => Z (b,i))

noncomputable def commonCutList {α : Type*} (L : Bool → α → ℕ) (H : ℕ) (Z : TwoTape α) : TwoTapeList α :=
  fun b => cutList (L b) H (fun i => Z (b,i))

noncomputable def afterCommonCut {α : Type*} (L : Bool → α → ℕ) (H : ℕ) (Z : TwoTape α) : TwoTape α :=
  twoShift (commonCutIndices L H Z) Z

lemma measurable_commonCutIndices {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (L : Bool → α → ℕ) (H : ℕ) : Measurable (commonCutIndices L H) := by
  exact Measurable.of_eval (fun b => (measurable_cutListIndex (L b) H).comp (by fun_prop))

lemma measurable_commonCutList {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (L : Bool → α → ℕ) (H : ℕ) : Measurable (commonCutList L H) := by
  exact Measurable.of_eval (fun b => (measurable_cutList (L b) H).comp (by fun_prop))

lemma measurable_afterCommonCut {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (L : Bool → α → ℕ) (H : ℕ) : Measurable (afterCommonCut L H) := by
  have hm : Measurable (fun p : TwoTape α × (Bool → ℕ) => twoShift p.2 p.1) :=
    measurable_from_prod_countable_left (measurable_twoShift (α := α))
  exact hm.comp (measurable_id.prodMk (measurable_commonCutIndices L H))

lemma commonCutList_atom_iff {α : Type*} (L : Bool → α → ℕ) (H : ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i))) (a : TwoTapeList α) :
    (Z ∈ commonCut L H ∧ commonCutList L H Z = a) ↔
      ((∀ b, listHeight (L b) (a b) = H) ∧ Z ∈ twoCylinder a) := by
  constructor
  · rintro ⟨hc,ha⟩
    have hh : ∀ b, listHeight (L b) (a b) = H ∧
        (fun i => Z (b,i)) ∈ tapeCylinder (a b) := fun b =>
      (cutList_atom_iff (L b) H _ (hZ b) (a b)).mp ⟨hc b,congrFun ha b⟩
    exact ⟨fun b => (hh b).1,fun b => (hh b).2⟩
  · rintro ⟨hh,ha⟩
    have hb := fun b => (cutList_atom_iff (L b) H (fun i => Z (b,i)) (hZ b) (a b)).mpr ⟨hh b,ha b⟩
    exact ⟨fun b => (hb b).1,funext (fun b => (hb b).2)⟩

lemma commonCutIndices_eq_lengths {α : Type*} (L : Bool → α → ℕ) (H : ℕ) (Z : TwoTape α)
    (a : TwoTapeList α) (ha : commonCutList L H Z = a) :
    commonCutIndices L H Z = fun b => (a b).1 := by
  funext b
  exact congrArg Sigma.fst (congrFun ha b)

lemma commonCut_add_iff {α : Type*} (L : Bool → α → ℕ) (H : ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i))) (hc : Z ∈ commonCut L H) (J : ℕ) :
    Z ∈ commonCut L (H+J) ↔ afterCommonCut L H Z ∈ commonCut L J := by
  apply forall_congr'
  intro b
  obtain ⟨n,hn⟩ := hc b
  have hi := cutListIndex_eq (L b) H (fun i => Z (b,i)) (hZ b) hn
  change _ ↔ (fun i => Z (b,cutListIndex (L b) H (fun i => Z (b,i))+i)) ∈ renewalCut (L b) J
  rw [hi]
  exact renewalCut_add_iff (L b) _ (hZ b) hn J

lemma commonCut_fibre_tail {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a) (H : ℕ)
    (a : TwoTapeList α) (E : Set (TwoTape α)) (hE : MeasurableSet E) :
    twoTapeLaw ν ({Z | commonCutList L H Z = a} ∩
      (commonCut L H ∩ afterCommonCut L H ⁻¹' E)) =
    twoTapeLaw ν ({Z | commonCutList L H Z = a} ∩ commonCut L H) * twoTapeLaw ν E := by
  classical
  have hZ := ae_twoTape_prop ν (fun b a => 0 < L b a)
    (fun b => measurableSet_lt measurable_const (measurable_of_countable (L b))) hL
  by_cases ha : ∀ b, listHeight (L b) (a b) = H
  · have h1 : twoTapeLaw ν ({Z | commonCutList L H Z = a} ∩
        (commonCut L H ∩ afterCommonCut L H ⁻¹' E)) =
      twoTapeLaw ν {Z | Z ∈ twoCylinder a ∧ twoShift (fun b => (a b).1) Z ∈ E} := by
      apply measure_congr
      filter_upwards [hZ] with Z hZ
      apply propext
      constructor
      · rintro ⟨hlist,hc,hE⟩
        refine ⟨((commonCutList_atom_iff L H Z hZ a).mp ⟨hc,hlist⟩).2,?_⟩
        simpa only [Set.mem_preimage,afterCommonCut,commonCutIndices_eq_lengths L H Z a hlist] using hE
      · rintro ⟨hpre,hE⟩
        have hh := (commonCutList_atom_iff L H Z hZ a).mpr ⟨ha,hpre⟩
        refine ⟨hh.2,hh.1,?_⟩
        simpa only [Set.mem_preimage,afterCommonCut,commonCutIndices_eq_lengths L H Z a hh.2] using hE
    have h2 : twoTapeLaw ν ({Z | commonCutList L H Z = a} ∩ commonCut L H) =
        twoTapeLaw ν (twoCylinder a) := by
      apply measure_congr
      filter_upwards [hZ] with Z hZ
      apply propext
      constructor
      · rintro ⟨hb,hc⟩; exact ((commonCutList_atom_iff L H Z hZ a).mp ⟨hc,hb⟩).2
      · intro h; have hh := (commonCutList_atom_iff L H Z hZ a).mpr ⟨ha,h⟩; exact ⟨hh.2,hh.1⟩
    rw [h1,h2,twoCylinder_suffix_factorization ν a E hE,twoCylinder_mass]
  · have h0 : twoTapeLaw ν ({Z | commonCutList L H Z = a} ∩ commonCut L H) = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [hZ] with Z hZ hm
      exact ha ((commonCutList_atom_iff L H Z hZ a).mp ⟨hm.2,hm.1⟩).1
    rw [h0,zero_mul]
    apply measure_mono_null _ h0
    exact fun Z h => ⟨h.1,h.2.1⟩

lemma commonCut_tail_factorization {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a) (H : ℕ)
    (E : Set (TwoTape α)) (hE : MeasurableSet E) :
    twoTapeLaw ν (commonCut L H ∩ afterCommonCut L H ⁻¹' E) =
      twoTapeLaw ν (commonCut L H) * twoTapeLaw ν E := by
  rw [measure_eq_tsum_fibres (twoTapeLaw ν) (commonCutList L H) (measurable_commonCutList L H)
      ((measurableSet_commonCut L H).inter (hE.preimage (measurable_afterCommonCut L H)))]
  simp_rw [commonCut_fibre_tail ν L hL H _ E hE]
  rw [ENNReal.tsum_mul_right,← measure_eq_tsum_fibres (twoTapeLaw ν) (commonCutList L H)
    (measurable_commonCutList L H) (measurableSet_commonCut L H)]

instance twoTapeLaw_probability {α : Type*} [MeasurableSpace α] (ν : Bool → Measure α)
    [∀ b, IsProbabilityMeasure (ν b)] : IsProbabilityMeasure (twoTapeLaw ν) := by
  unfold twoTapeLaw
  infer_instance

lemma twoExtract_independent {α : Type*} [MeasurableSpace α] (ν : Bool → Measure α)
    [∀ b, IsProbabilityMeasure (ν b)] :
    IndepFun (fun Z i => Z (false,i)) (fun Z i => Z (true,i)) (twoTapeLaw ν) := by
  have hS : @Measurable (TwoTape α) (ℕ → α)
      (coordSigma {i | i.1 = false}) _ (fun Z i => Z (false,i)) := by
    let : MeasurableSpace (TwoTape α) := coordSigma {i | i.1 = false}
    exact Measurable.of_eval (fun _ => measurable_coordEval rfl)
  have hT : @Measurable (TwoTape α) (ℕ → α)
      (coordSigma {i | i.1 = true}) _ (fun Z i => Z (true,i)) := by
    let : MeasurableSpace (TwoTape α) := coordSigma {i | i.1 = true}
    exact Measurable.of_eval (fun _ => measurable_coordEval rfl)
  have hd : Disjoint {i : Bool × ℕ | i.1 = false} {i | i.1 = true} := by
    apply Set.disjoint_left.mpr
    intro i hi hj
    exact Bool.false_ne_true (hi.symm.trans hj)
  have hind := indep_iSup_of_disjoint (fun i : Bool × ℕ => (measurable_pi_apply (X := fun _ => α) i).comap_le)
    (iIndepFun_infinitePi (P := fun i : Bool × ℕ => ν i.1) (X := fun _ x => x) (fun _ => measurable_id)) hd
  exact (IndepFun_iff_Indep _ _ _).mpr (indep_of_indep_of_le hind hS.comap_le hT.comap_le)

lemma commonCut_mass {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (H : ℕ) :
    twoTapeLaw ν (commonCut L H) =
      Measure.infinitePi (fun _ : ℕ => ν false) (renewalCut (L false) H) *
      Measure.infinitePi (fun _ : ℕ => ν true) (renewalCut (L true) H) := by
  have hh := (twoExtract_independent ν).measure_inter_preimage_eq_mul
    (renewalCut (L false) H) (renewalCut (L true) H)
    (measurableSet_renewalCut _ _) (measurableSet_renewalCut _ _)
  have he : commonCut L H =
      (fun Z i => Z (false,i)) ⁻¹' renewalCut (L false) H ∩
      (fun Z i => Z (true,i)) ⁻¹' renewalCut (L true) H := by
    ext Z
    exact Bool.forall_bool
  rw [he,hh,← Measure.map_apply (by fun_prop) (measurableSet_renewalCut (L false) H),
    ← Measure.map_apply (by fun_prop) (measurableSet_renewalCut (L true) H),twoExtract_law,twoExtract_law]

def noCommonThrough {α : Type*} (L : Bool → α → ℕ) (N : ℕ) : Set (TwoTape α) :=
  {Z | ∀ i, 0 < i → i ≤ N → Z ∉ commonCut L i}

lemma measurableSet_noCommonThrough {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (L : Bool → α → ℕ) (N : ℕ) : MeasurableSet (noCommonThrough L N) := by
  simp only [noCommonThrough,Set.ofPred_forall]
  exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun _ =>
    MeasurableSet.iInter (fun _ => (measurableSet_commonCut L i).compl)))

def lastCommonEvent {α : Type*} (L : Bool → α → ℕ) (N j : ℕ) : Set (TwoTape α) :=
  {Z | Z ∈ commonCut L j ∧ ∀ k, j < k → k ≤ N → Z ∉ commonCut L k}

lemma measurableSet_lastCommonEvent {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (L : Bool → α → ℕ) (N j : ℕ) : MeasurableSet (lastCommonEvent L N j) := by
  change MeasurableSet (commonCut L j ∩ {Z | ∀ k, j < k → k ≤ N → Z ∉ commonCut L k})
  apply (measurableSet_commonCut L j).inter
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter (fun k => MeasurableSet.iInter (fun _ =>
    MeasurableSet.iInter (fun _ => (measurableSet_commonCut L k).compl)))

lemma lastCommonEvent_disjoint {α : Type*} (L : Bool → α → ℕ) (N : ℕ) :
    (Finset.range (N+1) : Set ℕ).PairwiseDisjoint (lastCommonEvent L N) := by
  intro i hi j hj hij
  apply Set.disjoint_left.mpr
  rintro Z ⟨hci,hli⟩ ⟨hcj,hlj⟩
  have hiN : i ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hjN : j ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rcases lt_or_gt_of_ne hij with h | h
  · exact hli j h hjN hcj
  · exact hlj i h hiN hci

lemma lastCommonEvent_partition {α : Type*} (L : Bool → α → ℕ) (N : ℕ) :
    (⋃ j ∈ Finset.range (N+1), lastCommonEvent L N j) = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro Z
  let s := (Finset.range (N+1)).filter (fun j => Z ∈ commonCut L j)
  have h0 : 0 ∈ s := by simp [s,commonCut_zero]
  let j := s.max' ⟨0,h0⟩
  have hj := s.max'_mem ⟨0,h0⟩
  obtain ⟨hjN,hcut⟩ := Finset.mem_filter.mp hj
  refine Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨hjN,hcut,?_⟩⟩
  intro k hjk hkN hk
  have hks : k ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hk⟩
  exact (not_le_of_gt hjk) (s.le_max' k hks)

lemma lastCommonEvent_tail {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i))) (N j : ℕ) (hj : j ≤ N) :
    Z ∈ lastCommonEvent L N j ↔
      Z ∈ commonCut L j ∩ afterCommonCut L j ⁻¹' noCommonThrough L (N-j) := by
  constructor
  · rintro ⟨hc,hl⟩
    refine ⟨hc,fun i hi hiN hcut => ?_⟩
    exact hl (j+i) (by omega) (by omega) ((commonCut_add_iff L j Z hZ hc i).mpr hcut)
  · rintro ⟨hc,hl⟩
    refine ⟨hc,fun k hjk hkN hcut => ?_⟩
    apply hl (k-j) (by omega) (by omega)
    apply (commonCut_add_iff L j Z hZ hc (k-j)).mp
    simpa only [Nat.add_sub_of_le hjk.le] using hcut

lemma lastCommonEvent_mass {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a) (N j : ℕ) (hj : j ≤ N) :
    twoTapeLaw ν (lastCommonEvent L N j) =
      twoTapeLaw ν (commonCut L j) * twoTapeLaw ν (noCommonThrough L (N-j)) := by
  rw [← commonCut_tail_factorization ν L hL j _ (measurableSet_noCommonThrough L _)]
  apply measure_congr
  filter_upwards [ae_twoTape_prop ν (fun b a => 0 < L b a)
    (fun b => measurableSet_lt measurable_const (measurable_of_countable (L b))) hL] with Z hZ
  exact propext (lastCommonEvent_tail L Z hZ N j hj)

lemma common_renewal_tail_identity {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a) (N : ℕ) :
    ∑ j ∈ Finset.range (N+1), twoTapeLaw ν (commonCut L j) *
      twoTapeLaw ν (noCommonThrough L (N-j)) = 1 := by
  calc
    _ = ∑ j ∈ Finset.range (N+1), twoTapeLaw ν (lastCommonEvent L N j) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (lastCommonEvent_mass ν L hL N j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).symm
    _ = twoTapeLaw ν (⋃ j ∈ Finset.range (N+1), lastCommonEvent L N j) := by
      exact (measure_biUnion_finset (lastCommonEvent_disjoint L N)
        (fun j _ => measurableSet_lastCommonEvent L N j)).symm
    _ = 1 := by rw [lastCommonEvent_partition,measure_univ]

lemma common_renewal_tail_sum_bound {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a) (c : ℝ≥0∞)
    (hc : ∀ H, c ≤ twoTapeLaw ν (commonCut L H)) :
    c * ∑' N, twoTapeLaw ν (noCommonThrough L N) ≤ 1 := by
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_of_sum_range_le
  intro n
  cases n with
  | zero => simp
  | succ N =>
    have h := common_renewal_tail_identity ν L hL N
    calc
      _ = ∑ j ∈ Finset.range (N+1), c * twoTapeLaw ν (noCommonThrough L (N-j)) := by
        exact (Finset.sum_range_reflect (fun j => c * twoTapeLaw ν (noCommonThrough L j)) (N+1)).symm
      _ ≤ ∑ j ∈ Finset.range (N+1), twoTapeLaw ν (commonCut L j) *
          twoTapeLaw ν (noCommonThrough L (N-j)) :=
        Finset.sum_le_sum (fun j _ => mul_le_mul' (hc j) le_rfl)
      _ = 1 := h

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

noncomputable def firstCommonWidth {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α) : ℕ := by
  classical
  exact if h : ∃ H, 0 < H ∧ Z ∈ commonCut L H then Nat.find h else 0

lemma firstCommonWidth_spec {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    (h : ∃ H, 0 < H ∧ Z ∈ commonCut L H) :
    0 < firstCommonWidth L Z ∧ Z ∈ commonCut L (firstCommonWidth L Z) ∧
      ∀ j < firstCommonWidth L Z, 0 < j → Z ∉ commonCut L j := by
  classical
  simp only [firstCommonWidth,dite_eq_left h]
  exact ⟨(Nat.find_spec h).1,(Nat.find_spec h).2,fun j hj hjpos hc => Nat.find_min h hj ⟨hjpos,hc⟩⟩

lemma firstCommonWidth_zero_iff {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α) :
    firstCommonWidth L Z = 0 ↔ ¬∃ H, 0 < H ∧ Z ∈ commonCut L H := by
  constructor
  · intro hz h
    have hh := (firstCommonWidth_spec L Z h).1
    omega
  · intro h; simp [firstCommonWidth,h]

lemma firstCommonWidth_eq_pos_iff {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    {H : ℕ} (hH : 0 < H) :
    firstCommonWidth L Z = H ↔ Z ∈ commonCut L H ∧ Z ∈ noCommonThrough L (H-1) := by
  classical
  constructor
  · intro he
    have hex : ∃ n, 0 < n ∧ Z ∈ commonCut L n := by
      by_contra hn
      have := (firstCommonWidth_zero_iff L Z).mpr hn
      omega
    have hh := firstCommonWidth_spec L Z hex
    rw [he] at hh
    exact ⟨hh.2.1,fun j hj hjH => hh.2.2 j (by omega) hj⟩
  · rintro ⟨hc,hl⟩
    have he : ∃ n, 0 < n ∧ Z ∈ commonCut L n := ⟨H,hH,hc⟩
    simp only [firstCommonWidth,dite_eq_left he]
    apply (Nat.find_eq_iff he).mpr
    exact ⟨⟨hH,hc⟩,fun j hj hm => hl j hm.1 (by omega) hm.2⟩

lemma measurable_firstCommonWidth {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (L : Bool → α → ℕ) : Measurable (firstCommonWidth L) := by
  apply measurable_to_countable'
  intro H
  by_cases hH : H = 0
  · subst H
    have he : firstCommonWidth L ⁻¹' {0} = (⋃ n, ⋃ (_ : 0 < n), commonCut L n)ᶜ := by
      ext Z
      simp only [Set.mem_preimage,Set.mem_singleton_iff,firstCommonWidth_zero_iff,
        Set.mem_compl_iff,Set.mem_iUnion,not_exists,not_and]
    rw [he]
    exact (MeasurableSet.iUnion (fun n => MeasurableSet.iUnion (fun _ => measurableSet_commonCut L n))).compl
  · have he : firstCommonWidth L ⁻¹' {H} = commonCut L H ∩ noCommonThrough L (H-1) := by
      ext Z;exact firstCommonWidth_eq_pos_iff L Z (Nat.pos_of_ne_zero hH)
    rw [he]
    exact (measurableSet_commonCut L H).inter (measurableSet_noCommonThrough L _)

lemma firstCommonWidth_tail_subset {α : Type*} (L : Bool → α → ℕ) (N : ℕ) :
    {Z | N < firstCommonWidth L Z} ⊆ noCommonThrough L N := by
  intro Z hZ j hj hjN hc
  have he := firstCommonWidth_spec L Z ⟨j,hj,hc⟩
  exact he.2.2 j (lt_of_le_of_lt hjN hZ) hj hc

lemma ae_exists_commonCut {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a) (c : ℝ≥0∞) (hcpos : c ≠ 0)
    (hc : ∀ H, c ≤ twoTapeLaw ν (commonCut L H)) :
    ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H := by
  have hb := common_renewal_tail_sum_bound ν L hL c hc
  have hn : (∑' N, twoTapeLaw ν (noCommonThrough L N)) ≠ ∞ :=
    (ENNReal.lt_top_of_mul_ne_top_right (ne_top_of_le_ne_top ENNReal.one_ne_top hb) hcpos).ne
  filter_upwards [ae_eventually_notMem hn] with Z hZ
  obtain ⟨N,hN⟩ := hZ.exists
  by_contra h
  apply hN
  intro j hj _ hc
  exact h ⟨j,hj,hc⟩

lemma lintegral_firstCommonWidth_le {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a) (c : ℝ≥0∞) (hcpos : c ≠ 0)
    (hc : ∀ H, c ≤ twoTapeLaw ν (commonCut L H)) :
    (∫⁻ Z, (firstCommonWidth L Z : ℝ≥0∞) ∂twoTapeLaw ν) ≤ c⁻¹ := by
  have hctop : c ≠ ∞ := ne_top_of_le_ne_top (measure_ne_top _ _) (hc 0)
  have hb := (ENNReal.mul_le_iff_le_inv hcpos hctop).mp (common_renewal_tail_sum_bound ν L hL c hc)
  rw [lintegral_nat_tail _ _ (measurable_firstCommonWidth L)]
  exact (ENNReal.tsum_le_tsum (fun N => measure_mono (firstCommonWidth_tail_subset L N))).trans (by simpa using hb)

lemma integrable_firstCommonWidth {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a) (c : ℝ≥0∞) (hcpos : c ≠ 0)
    (hc : ∀ H, c ≤ twoTapeLaw ν (commonCut L H)) :
    Integrable (fun Z => (firstCommonWidth L Z : ℝ)) (twoTapeLaw ν) := by
  have hm : Measurable (fun Z => (firstCommonWidth L Z : ℝ)) :=
    (measurable_of_countable Nat.cast).comp (measurable_firstCommonWidth L)
  refine ⟨hm.aestronglyMeasurable,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun Z => Nat.cast_nonneg (firstCommonWidth L Z)))).mpr
  simp_rw [ENNReal.ofReal_natCast]
  exact (lintegral_firstCommonWidth_le ν L hL c hcpos hc).trans_lt (ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr hcpos))

def listHasCut {α : Type*} (L : α → ℕ) (a : TapeList α) (H : ℕ) : Prop :=
  ∃ n, ∃ hn : n ≤ a.1, (∑ i : Fin n, L (a.2 (i.castLE hn))) = H

lemma listHasCut_prefix {α : Type*} (L : α → ℕ) (Z : ℕ → α) (n H : ℕ) :
    listHasCut L (tapePrefix n Z) H ↔ ∃ j ≤ n, tapeHeight L Z j = H := by
  change (∃ j, ∃ hj : j ≤ n, (∑ i : Fin j, L (Z (i : ℕ))) = H) ↔ _
  simp only [Fin.sum_univ_eq_sum_range (fun i => L (Z i)),tapeHeight,exists_prop]

lemma renewalCut_iff_listHasCut {α : Type*} (L : α → ℕ) (Z : ℕ → α)
    (hZ : ∀ i, 0 < L (Z i)) (H j : ℕ) (hH : Z ∈ renewalCut L H) (hj : j ≤ H) :
    Z ∈ renewalCut L j ↔ listHasCut L (cutList L H Z) j := by
  obtain ⟨n,hn⟩ := hH
  rw [cutList,cutListIndex_eq L H Z hZ hn,listHasCut_prefix]
  constructor
  · rintro ⟨k,hk⟩
    refine ⟨k,?_,hk⟩
    exact (tapeHeight_strictMono L Z hZ).le_iff_le.mp (by omega)
  · rintro ⟨k,_,hk⟩;exact ⟨k,hk⟩

lemma commonCut_iff_listHasCut {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i))) (H j : ℕ) (hH : Z ∈ commonCut L H) (hj : j ≤ H) :
    Z ∈ commonCut L j ↔ ∀ b, listHasCut (L b) (commonCutList L H Z b) j := by
  exact forall_congr' (fun b => renewalCut_iff_listHasCut (L b) _ (hZ b) H j (hH b) hj)

noncomputable def firstCommonBlock {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α) : TwoTapeList α :=
  commonCutList L (firstCommonWidth L Z) Z

noncomputable def commonRestart {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α) : TwoTape α :=
  afterCommonCut L (firstCommonWidth L Z) Z

lemma measurable_firstCommonBlock {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (L : Bool → α → ℕ) : Measurable (firstCommonBlock L) := by
  have hm : Measurable (fun p : TwoTape α × ℕ => commonCutList L p.2 p.1) :=
    measurable_from_prod_countable_left (measurable_commonCutList L)
  exact hm.comp (measurable_id.prodMk (measurable_firstCommonWidth L))

lemma measurable_commonRestart {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (L : Bool → α → ℕ) : Measurable (commonRestart L) := by
  have hm : Measurable (fun p : TwoTape α × ℕ => afterCommonCut L p.2 p.1) :=
    measurable_from_prod_countable_left (measurable_afterCommonCut L)
  exact hm.comp (measurable_id.prodMk (measurable_firstCommonWidth L))

def IsFirstCommonList {α : Type*} (L : Bool → α → ℕ) (a : TwoTapeList α) : Prop :=
  0 < listHeight (L false) (a false) ∧
    (∀ b, listHeight (L b) (a b) = listHeight (L false) (a false)) ∧
    ∀ j, 0 < j → j < listHeight (L false) (a false) → ¬∀ b, listHasCut (L b) (a b) j

lemma firstCommonBlock_spec {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i))) (he : ∃ H, 0 < H ∧ Z ∈ commonCut L H) :
    IsFirstCommonList L (firstCommonBlock L Z) ∧
      listHeight (L false) (firstCommonBlock L Z false) = firstCommonWidth L Z := by
  have hK := firstCommonWidth_spec L Z he
  have hh := (commonCutList_atom_iff L (firstCommonWidth L Z) Z hZ
    (firstCommonBlock L Z)).mp ⟨hK.2.1,rfl⟩
  refine ⟨⟨by rw [hh.1 false];exact hK.1,fun b => (hh.1 b).trans (hh.1 false).symm,?_⟩,hh.1 false⟩
  intro j hj hjK hc
  rw [hh.1 false] at hjK
  exact hK.2.2 j hjK hj ((commonCut_iff_listHasCut L Z hZ _ j hK.2.1 hjK.le).mpr hc)

lemma firstCommonBlock_atom_iff {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i))) (he : ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (a : TwoTapeList α) (ha : IsFirstCommonList L a) :
    firstCommonBlock L Z = a ↔ Z ∈ twoCylinder a := by
  let H := listHeight (L false) (a false)
  constructor
  · intro h
    have hK := firstCommonWidth_spec L Z he
    exact ((commonCutList_atom_iff L _ Z hZ a).mp ⟨hK.2.1,h⟩).2
  · intro hcyl
    have hc := (commonCutList_atom_iff L H Z hZ a).mpr ⟨ha.2.1,hcyl⟩
    have heq : firstCommonWidth L Z = H := by
      apply (firstCommonWidth_eq_pos_iff L Z ha.1).mpr
      refine ⟨hc.1,fun j hj hjH hcut => ?_⟩
      apply ha.2.2 j hj (by change j < H;omega)
      rw [← hc.2]
      exact (commonCut_iff_listHasCut L Z hZ H j hc.1 (by omega)).mp hcut
    simp only [firstCommonBlock,heq,hc.2]

lemma commonRestart_eq_shift {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    (a : TwoTapeList α) (ha : firstCommonBlock L Z = a) :
    commonRestart L Z = twoShift (fun b => (a b).1) Z := by
  unfold commonRestart afterCommonCut
  rw [commonCutIndices_eq_lengths L _ Z a ha]

noncomputable def commonBlockLaw {α : Type*} [MeasurableSpace α]
    (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) : Measure (TwoTapeList α) :=
  (twoTapeLaw ν).map (firstCommonBlock L)

lemma firstCommonBlock_suffix_factorization {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (a : TwoTapeList α) (E : Set (TwoTape α)) (hE : MeasurableSet E) :
    twoTapeLaw ν {Z | firstCommonBlock L Z = a ∧ commonRestart L Z ∈ E} =
      commonBlockLaw ν L {a} * twoTapeLaw ν E := by
  classical
  have hZ := ae_twoTape_prop ν (fun b a => 0 < L b a)
    (fun b => measurableSet_lt measurable_const (measurable_of_countable (L b))) hL
  rw [commonBlockLaw,Measure.map_apply (measurable_firstCommonBlock L) (measurableSet_singleton a)]
  by_cases ha : IsFirstCommonList L a
  · have hmass : twoTapeLaw ν (firstCommonBlock L ⁻¹' {a}) = twoTapeLaw ν (twoCylinder a) := by
      apply measure_congr
      filter_upwards [hZ,he] with Z hZ he
      exact propext (firstCommonBlock_atom_iff L Z hZ he a ha)
    have hevent : twoTapeLaw ν {Z | firstCommonBlock L Z = a ∧ commonRestart L Z ∈ E} =
        twoTapeLaw ν {Z | Z ∈ twoCylinder a ∧ twoShift (fun b => (a b).1) Z ∈ E} := by
      apply measure_congr
      filter_upwards [hZ,he] with Z hZ he
      apply propext
      constructor
      · rintro ⟨h,ht⟩
        exact ⟨(firstCommonBlock_atom_iff L Z hZ he a ha).mp h,
          by simpa only [commonRestart_eq_shift L Z a h] using ht⟩
      · rintro ⟨h,ht⟩
        have hb := (firstCommonBlock_atom_iff L Z hZ he a ha).mpr h
        exact ⟨hb,by simpa only [commonRestart_eq_shift L Z a hb] using ht⟩
    rw [hmass,hevent,twoCylinder_suffix_factorization ν a E hE,twoCylinder_mass]
  · have hzero : twoTapeLaw ν (firstCommonBlock L ⁻¹' {a}) = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [hZ,he] with Z hZ he h
      exact ha (h ▸ (firstCommonBlock_spec L Z hZ he).1)
    rw [hzero,zero_mul]
    exact measure_mono_null (fun _ h => h.1) hzero

lemma commonRestart_measurePreserving {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H) :
    MeasurePreserving (commonRestart L) (twoTapeLaw ν) (twoTapeLaw ν) := by
  refine ⟨measurable_commonRestart L,Measure.ext (fun E hE => ?_)⟩
  rw [Measure.map_apply (measurable_commonRestart L) hE,
    measure_eq_tsum_fibres (twoTapeLaw ν) (firstCommonBlock L) (measurable_firstCommonBlock L)
      (hE.preimage (measurable_commonRestart L))]
  simp_rw [show ∀ a, {Z | firstCommonBlock L Z = a} ∩ commonRestart L ⁻¹' E =
      {Z | firstCommonBlock L Z = a ∧ commonRestart L Z ∈ E} from fun _ => rfl,
    firstCommonBlock_suffix_factorization ν L hL he _ E hE,ENNReal.tsum_mul_right]
  have hp : IsProbabilityMeasure (commonBlockLaw ν L) :=
    probabilityMeasure_map (μ := twoTapeLaw ν) (measurable_firstCommonBlock L).aemeasurable
  have hsum := measure_eq_tsum_fibres (commonBlockLaw ν L) id measurable_id MeasurableSet.univ
  simp only [id_eq,Set.inter_univ,Set.ofPred_eq_eq_singleton,measure_univ] at hsum
  rw [← hsum,one_mul]

def commonNeeds {α : Type*} (L : Bool → α → ℕ) (b : Bool) (i : ℕ) : Set (TwoTape α) :=
  {Z | ∀ j, 0 < j → j ≤ i → ¬∃ n,
    tapeHeight (L (!b)) (fun k => Z (!b,k)) n = tapeHeight (L b) (fun k => Z (b,k)) j}

lemma commonNeeds_iff {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i))) (he : ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (b : Bool) (i : ℕ) :
    Z ∈ commonNeeds L b i ↔ i < (firstCommonBlock L Z b).1 := by
  have hK := firstCommonWidth_spec L Z he
  obtain ⟨n,hn⟩ := hK.2.1 b
  have hnblock : (firstCommonBlock L Z b).1 = n := by
    exact cutListIndex_eq (L b) _ _ (hZ b) hn
  rw [hnblock]
  have hnpos : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    rw [hn0] at hn
    have hz : firstCommonWidth L Z = 0 := hn.symm
    omega
  have h0 (j : ℕ) (hj : 0 < j) : 0 < tapeHeight (L b) (fun k => Z (b,k)) j :=
    lt_of_lt_of_le hj (le_tapeHeight (L b) _ (hZ b) j)
  constructor
  · intro hc
    by_contra hin
    obtain ⟨m,hm⟩ := hK.2.1 (!b)
    exact hc n hnpos (by omega) ⟨m,hm.trans hn.symm⟩
  · intro hin j hj hji ⟨m,hm⟩
    have hjn : j < n := lt_of_le_of_lt hji hin
    have hcut : Z ∈ commonCut L (tapeHeight (L b) (fun k => Z (b,k)) j) := by
      intro c
      by_cases hcb : c = b
      · subst c;exact ⟨j,rfl⟩
      · have hco : c = !b := by cases b <;> cases c <;> simp_all
        subst c;exact ⟨m,hm⟩
    apply hK.2.2 _ _ (h0 j hj) hcut
    rw [← hn]
    exact (tapeHeight_strictMono (L b) _ (hZ b)) hjn

lemma coordSigma_le {ι α : Type*} [MeasurableSpace α] (s : Set ι) :
    coordSigma (α := α) s ≤ inferInstanceAs (MeasurableSpace (ι → α)) :=
  iSup₂_le (fun i _ => (measurable_pi_apply (X := fun _ => α) i).comap_le)

lemma measurableSet_commonNeeds_rest {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (L : Bool → α → ℕ) (b : Bool) (i : ℕ) :
    @MeasurableSet (TwoTape α) (coordSigma {p | p ≠ (b,i)}) (commonNeeds L b i) := by
  let : MeasurableSpace (TwoTape α) := coordSigma {p | p ≠ (b,i)}
  have hother (n : ℕ) : Measurable (fun Z : TwoTape α => tapeHeight (L (!b)) (fun k => Z (!b,k)) n) := by
    apply Finset.measurable_sum
    intro k _
    apply (measurable_of_countable (L (!b))).comp
    apply measurable_coordEval
    intro hp
    have hb := congrArg Prod.fst hp
    cases b <;> simp at hb
  have hprev (j : ℕ) (hj : j ≤ i) : Measurable (fun Z : TwoTape α => tapeHeight (L b) (fun k => Z (b,k)) j) := by
    apply Finset.measurable_sum
    intro k hk
    apply (measurable_of_countable (L b)).comp
    apply measurable_coordEval
    intro hp
    have hi := congrArg Prod.snd hp
    have hk := Finset.mem_range.mp hk
    change k = i at hi
    omega
  simp only [commonNeeds,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro _
  apply MeasurableSet.iInter
  intro hj
  change MeasurableSet ({Z : TwoTape α | ∃ n, tapeHeight (L (!b)) (fun k => Z (!b,k)) n =
      tapeHeight (L b) (fun k => Z (b,k)) j}ᶜ)
  apply MeasurableSet.compl
  simp only [Set.ofPred_exists]
  exact MeasurableSet.iUnion (fun n => measurableSet_eq_fun (hother n) (hprev j hj))

lemma measurableSet_commonNeeds {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (L : Bool → α → ℕ) (b : Bool) (i : ℕ) :
    MeasurableSet (commonNeeds L b i) :=
  coordSigma_le _ _ (measurableSet_commonNeeds_rest L b i)

lemma commonNeeds_next_independent {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (b : Bool) (i : ℕ) (R : α → ℝ≥0∞) :
    IndepFun ((commonNeeds L b i).indicator (fun _ => (1 : ℝ≥0∞)))
      (fun Z : TwoTape α => R (Z (b,i))) (twoTapeLaw ν) := by
  classical
  have hS : @Measurable (TwoTape α) ℝ≥0∞ (coordSigma {p | p ≠ (b,i)}) _
      ((commonNeeds L b i).indicator (fun _ => (1 : ℝ≥0∞))) := by
    let : MeasurableSpace (TwoTape α) := coordSigma {p | p ≠ (b,i)}
    exact measurable_const.indicator (measurableSet_commonNeeds_rest L b i)
  have hT : @Measurable (TwoTape α) ℝ≥0∞ (coordSigma {(b,i)}) _
      (fun Z => R (Z (b,i))) := by
    let : MeasurableSpace (TwoTape α) := coordSigma {(b,i)}
    exact (measurable_of_countable R).comp (measurable_coordEval rfl)
  have hd : Disjoint {p : Bool × ℕ | p ≠ (b,i)} {(b,i)} := by
    apply Set.disjoint_left.mpr
    exact fun p hp hq => hp hq
  have hind := indep_iSup_of_disjoint (fun i : Bool × ℕ =>
    (measurable_pi_apply (X := fun _ => α) i).comap_le)
    (iIndepFun_infinitePi (P := fun i : Bool × ℕ => ν i.1) (X := fun _ x => x) (fun _ => measurable_id)) hd
  exact (IndepFun_iff_Indep _ _ _).mpr (indep_of_indep_of_le hind hS.comap_le hT.comap_le)

lemma commonNeeds_radius_factorization {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (b : Bool) (i : ℕ) (R : α → ℝ≥0∞) :
    (∫⁻ Z, (commonNeeds L b i).indicator (fun Z => R (Z (b,i))) Z ∂twoTapeLaw ν) =
      twoTapeLaw ν (commonNeeds L b i) * ∫⁻ a, R a ∂ν b := by
  classical
  have he : (commonNeeds L b i).indicator (fun Z => R (Z (b,i))) =
      fun Z => (commonNeeds L b i).indicator (fun _ => (1 : ℝ≥0∞)) Z * R (Z (b,i)) := by
    funext Z
    by_cases h : Z ∈ commonNeeds L b i <;> simp [h]
  rw [he]
  have hx := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
    (measurable_const.indicator (measurableSet_commonNeeds L b i))
    ((measurable_of_countable R).comp (measurable_pi_apply (b,i)))
    (commonNeeds_next_independent ν L b i R)
  simp only [Pi.mul_apply,Function.comp_apply] at hx
  rw [hx]
  have hm : (twoTapeLaw ν).map (fun Z => Z (b,i)) = ν b := by
    exact Measure.infinitePi_map_eval (fun p : Bool × ℕ => ν p.1) (b,i)
  rw [lintegral_indicator (measurableSet_commonNeeds L b i)]
  simp only [lintegral_const,Measure.restrict_apply_univ,one_mul]
  rw [← lintegral_map (measurable_of_countable R) (measurable_pi_apply (b,i)),hm]

noncomputable def listCost {α : Type*} (R : α → ℝ≥0∞) (a : TapeList α) : ℝ≥0∞ :=
  ∑ i : Fin a.1, R (a.2 i)

lemma firstCommonBlock_length_le {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i))) (he : ∃ H, 0 < H ∧ Z ∈ commonCut L H) (b : Bool) :
    (firstCommonBlock L Z b).1 ≤ firstCommonWidth L Z := by
  obtain ⟨n,hn⟩ := (firstCommonWidth_spec L Z he).2.1 b
  have hindex := cutListIndex_eq (L b) _ _ (hZ b) hn
  change cutListIndex (L b) (firstCommonWidth L Z) (fun i => Z (b,i)) ≤ _
  rw [hindex,← hn]
  exact le_tapeHeight (L b) _ (hZ b) n

lemma firstCommonBlock_cost_eq {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i))) (he : ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (b : Bool) (R : α → ℝ≥0∞) :
    listCost R (firstCommonBlock L Z b) =
      ∑' i, (commonNeeds L b i).indicator (fun Z => R (Z (b,i))) Z := by
  classical
  have hsum (i : ℕ) : (commonNeeds L b i).indicator (fun Z => R (Z (b,i))) Z =
      if i < (firstCommonBlock L Z b).1 then R (Z (b,i)) else 0 := by
    simp only [Set.indicator_apply,commonNeeds_iff L Z hZ he b i]
  simp_rw [hsum]
  rw [tsum_eq_sum (s := Finset.range (firstCommonBlock L Z b).1)]
  · change (∑ i : Fin (firstCommonBlock L Z b).1, R (Z (b,i))) = _
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => R (Z (b,i)))]
    apply Finset.sum_congr rfl
    intro i hi
    rw [ite_eq_left (Finset.mem_range.mp hi)]
  · intro i hi
    simp only [Finset.mem_range] at hi
    exact ite_eq_right hi

lemma commonBlock_Wald {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (b : Bool) (R : α → ℝ≥0∞) :
    (∫⁻ Z, listCost R (firstCommonBlock L Z b) ∂twoTapeLaw ν) =
      (∫⁻ Z, ((firstCommonBlock L Z b).1 : ℝ≥0∞) ∂twoTapeLaw ν) * ∫⁻ a, R a ∂ν b := by
  classical
  have hZ := ae_twoTape_prop ν (fun b a => 0 < L b a)
    (fun b => measurableSet_lt measurable_const (measurable_of_countable (L b))) hL
  have hN : Measurable (fun Z => (firstCommonBlock L Z b).1) :=
    (measurable_of_countable (fun a : TwoTapeList α => (a b).1)).comp (measurable_firstCommonBlock L)
  have hcost : (∫⁻ Z, listCost R (firstCommonBlock L Z b) ∂twoTapeLaw ν) =
      ∫⁻ Z, ∑' i, (commonNeeds L b i).indicator (fun Z => R (Z (b,i))) Z ∂twoTapeLaw ν := by
    apply lintegral_congr_ae
    filter_upwards [hZ,he] with Z hZ he
    exact firstCommonBlock_cost_eq L Z hZ he b R
  have ht : (∫⁻ Z, ∑' i, (commonNeeds L b i).indicator (fun Z => R (Z (b,i))) Z ∂twoTapeLaw ν) =
      ∑' i, ∫⁻ Z, (commonNeeds L b i).indicator (fun Z => R (Z (b,i))) Z ∂twoTapeLaw ν :=
    lintegral_tsum (fun i => (((measurable_of_countable R).comp (measurable_pi_apply (b,i))).indicator
      (measurableSet_commonNeeds L b i)).aemeasurable)
  rw [hcost,ht]
  simp_rw [commonNeeds_radius_factorization ν L b _ R]
  rw [ENNReal.tsum_mul_right,lintegral_nat_tail _ _ hN]
  congr 1
  apply tsum_congr
  intro i
  apply measure_congr
  filter_upwards [hZ,he] with Z hZ he
  exact propext (commonNeeds_iff L Z hZ he b i)

lemma commonBlock_cost_bound {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (b : Bool) (R : α → ℝ≥0∞) :
    (∫⁻ Z, listCost R (firstCommonBlock L Z b) ∂twoTapeLaw ν) ≤
      (∫⁻ Z, (firstCommonWidth L Z : ℝ≥0∞) ∂twoTapeLaw ν) * ∫⁻ a, R a ∂ν b := by
  rw [commonBlock_Wald ν L hL he b R]
  apply mul_le_mul' _ le_rfl
  apply lintegral_mono_ae
  filter_upwards [ae_twoTape_prop ν (fun b a => 0 < L b a)
    (fun b => measurableSet_lt measurable_const (measurable_of_countable (L b))) hL,he] with Z hZ he
  exact_mod_cast firstCommonBlock_length_le L Z hZ he b

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

abbrev tapeSigma {α : Type*} [MeasurableSpace α] (s : Set ℕ) : MeasurableSpace (ℕ → α) :=
  ⨆ i ∈ s, MeasurableSpace.comap (fun Z : ℕ → α => Z i) inferInstance

lemma measurable_tapeEval {α : Type*} [MeasurableSpace α] {s : Set ℕ} {i : ℕ} (hi : i ∈ s) :
    @Measurable (ℕ → α) α (tapeSigma s) _ (fun Z => Z i) :=
  measurable_iff_comap_le.mpr (le_iSup₂_of_le i hi le_rfl)

lemma iid_prefix_suffix_independent {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (n : ℕ) :
    IndepFun (fun Z (i : Fin n) => Z i) (fun (Z : ℕ → α) j => Z (n+j))
      (Measure.infinitePi (fun _ : ℕ => ν)) := by
  have hS : @Measurable (ℕ → α) (Fin n → α) (tapeSigma {i | i < n}) _
      (fun Z i => Z i) := by
    let : MeasurableSpace (ℕ → α) := tapeSigma {i | i < n}
    exact Measurable.of_eval (fun i => measurable_tapeEval i.isLt)
  have hT : @Measurable (ℕ → α) (ℕ → α) (tapeSigma {i | n ≤ i}) _
      (fun Z j => Z (n+j)) := by
    let : MeasurableSpace (ℕ → α) := tapeSigma {i | n ≤ i}
    exact Measurable.of_eval (fun j => measurable_tapeEval (Nat.le_add_right n j))
  have hd : Disjoint {i : ℕ | i < n} {i | n ≤ i} := by
    apply Set.disjoint_left.mpr
    intro i hi hj
    exact (not_lt_of_ge (show n ≤ i from hj)) (show i < n from hi)
  have hind := indep_iSup_of_disjoint (fun i : ℕ => (measurable_pi_apply (X := fun _ => α) i).comap_le)
    (iIndepFun_infinitePi (P := fun _ : ℕ => ν) (X := fun _ x => x) (fun _ => measurable_id)) hd
  exact (IndepFun_iff_Indep _ _ _).mpr (indep_of_indep_of_le hind hS.comap_le hT.comap_le)

lemma iid_suffix_law {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (n : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => ν)).map (fun Z j => Z (n+j)) =
      Measure.infinitePi (fun _ : ℕ => ν) := by
  exact Measure.map_infinitePi_infinitePi_of_inj (fun _ _ h => Nat.add_left_cancel h)

lemma tapeCylinder_suffix_factorization {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (ν : Measure α) [IsProbabilityMeasure ν] (a : TapeList α) (E : Set (ℕ → α)) (hE : MeasurableSet E) :
    Measure.infinitePi (fun _ : ℕ => ν) {Z | Z ∈ tapeCylinder a ∧ (fun j => Z (a.1+j)) ∈ E} =
      (∏ i : Fin a.1, ν {a.2 i}) * Measure.infinitePi (fun _ : ℕ => ν) E := by
  have hh := (iid_prefix_suffix_independent ν a.1).measure_inter_preimage_eq_mul {a.2} E
    (measurableSet_singleton _) hE
  have hc : (fun Z (i : Fin a.1) => Z i) ⁻¹' {a.2} = tapeCylinder a := by
    ext Z; simp only [Set.mem_preimage,Set.mem_singleton_iff,tapeCylinder,Set.mem_ofPred_eq,funext_iff]
  rw [hc,tapeCylinder_mass ν a,← Measure.map_apply (by fun_prop) hE,iid_suffix_law] at hh
  exact hh

noncomputable def regenerativeSequence {Ω β : Type*} (f : Ω → β) (T : Ω → Ω) (x : Ω) (k : ℕ) : β :=
  f (T^[k] x)

lemma measurable_regenerativeSequence {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (f : Ω → β) (T : Ω → Ω) (hf : Measurable f) (hT : Measurable T) :
    Measurable (regenerativeSequence f T) :=
  Measurable.of_eval (fun k => hf.comp (hT.iterate k))

lemma regenerativeSequence_prefix_mass {Ω β : Type*} [MeasurableSpace Ω] [Countable β]
    [MeasurableSpace β] [MeasurableSingletonClass β] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure β) (f : Ω → β) (T : Ω → Ω) (hf : Measurable f) (hT : Measurable T)
    (hfac : ∀ a E, MeasurableSet E → P {x | f x = a ∧ T x ∈ E} = ν {a} * P E)
    (n : ℕ) (a : ℕ → β) :
    P {x | ∀ i < n, regenerativeSequence f T x i = a i} = ∏ i ∈ Finset.range n, ν {a i} := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    have heq : {x | ∀ i < n+1, regenerativeSequence f T x i = a i} =
        {x | f x = a 0 ∧ T x ∈ {y | ∀ i < n, regenerativeSequence f T y i = a (i+1)}} := by
      ext x
      simp only [Set.mem_ofPred_eq]
      constructor
      · intro h
        refine ⟨h 0 (Nat.succ_pos _),fun i hi => ?_⟩
        simpa only [regenerativeSequence,Function.iterate_succ_apply] using h (i+1) (by omega)
      · rintro ⟨h0,h⟩ i hi
        cases i with
        | zero => exact h0
        | succ i => simpa only [regenerativeSequence,Function.iterate_succ_apply] using h i (by omega)
    have hE : MeasurableSet {y | ∀ i < n, regenerativeSequence f T y i = a (i+1)} := by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun _ =>
        (measurableSet_singleton (a (i+1))).preimage ((measurable_pi_apply i).comp
          (measurable_regenerativeSequence f T hf hT))))
    rw [heq,hfac _ _ hE,ih,Finset.prod_range_succ']
    exact mul_comm _ _

lemma regenerativeSequence_map {Ω β : Type*} [MeasurableSpace Ω] [Countable β]
    [MeasurableSpace β] [MeasurableSingletonClass β] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure β) [IsProbabilityMeasure ν] (f : Ω → β) (T : Ω → Ω) (hf : Measurable f) (hT : Measurable T)
    (hfac : ∀ a E, MeasurableSet E → P {x | f x = a ∧ T x ∈ E} = ν {a} * P E) :
    P.map (regenerativeSequence f T) = Measure.infinitePi (fun _ : ℕ => ν) := by
  classical
  apply measure_eq_of_prefix
  intro n
  apply Measure.ext_of_singleton
  intro a
  let γ : ℕ → β := fun i => if hi : i ≤ n then a ⟨i,Finset.mem_Iic.mpr hi⟩ else
    a ⟨0,Finset.mem_Iic.mpr (Nat.zero_le n)⟩
  have heq : (frestrictLe n : (ℕ → β) → (Finset.Iic n → β)) ⁻¹' {a} =
      (↑(Finset.range (n+1)) : Set ℕ).pi (fun i => {γ i}) := by
    ext b
    simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_pi,Finset.mem_coe,Finset.mem_range]
    constructor
    · intro h i hi
      have hh := congr_fun h ⟨i,Finset.mem_Iic.mpr (by omega)⟩
      simpa [γ,show i ≤ n by omega] using hh
    · intro h
      funext i
      have hi := Finset.mem_Iic.mp i.property
      simpa [γ,hi] using h i (by omega)
  rw [Measure.map_apply (measurable_frestrictLe n) (measurableSet_singleton a),
    Measure.map_apply (measurable_frestrictLe n) (measurableSet_singleton a),heq,
    Measure.map_apply (measurable_regenerativeSequence f T hf hT)
      (MeasurableSet.pi (Finset.countable_toSet _) (fun _ _ => measurableSet_singleton _)),
    Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
  have hpre : regenerativeSequence f T ⁻¹' (↑(Finset.range (n+1)) : Set ℕ).pi (fun i => {γ i}) =
      {x | ∀ i < n+1, regenerativeSequence f T x i = γ i} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_singleton_iff,Finset.mem_coe, Finset.mem_range, Set.mem_ofPred_eq]
  rw [hpre]
  exact regenerativeSequence_prefix_mass P ν f T hf hT hfac (n+1) γ

noncomputable def commonBlocks {α : Type*} (L : Bool → α → ℕ) : TwoTape α → ℕ → TwoTapeList α :=
  regenerativeSequence (firstCommonBlock L) (commonRestart L)

lemma commonBlocks_map {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H) :
    (twoTapeLaw ν).map (commonBlocks L) = Measure.infinitePi (fun _ : ℕ => commonBlockLaw ν L) := by
  let : IsProbabilityMeasure (commonBlockLaw ν L) :=
    probabilityMeasure_map (μ := twoTapeLaw ν) (measurable_firstCommonBlock L).aemeasurable
  exact regenerativeSequence_map (twoTapeLaw ν) (commonBlockLaw ν L) _ _
    (measurable_firstCommonBlock L) (measurable_commonRestart L)
    (firstCommonBlock_suffix_factorization ν L hL he)

lemma commonBlockLaw_atom {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (a : TwoTapeList α) (ha : IsFirstCommonList L a) :
    commonBlockLaw ν L {a} = ∏ b : Bool, ∏ i : Fin (a b).1, ν b {(a b).2 i} := by
  rw [commonBlockLaw,Measure.map_apply (measurable_firstCommonBlock L) (measurableSet_singleton a),← twoCylinder_mass ν a]
  apply measure_congr
  filter_upwards [ae_twoTape_prop ν (fun b a => 0 < L b a)
    (fun b => measurableSet_lt measurable_const (measurable_of_countable (L b))) hL,he] with Z hZ he
  exact propext (firstCommonBlock_atom_iff L Z hZ he a ha)

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

noncomputable def runningMax {Ω : Type*} (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (Finset.range (n+1)).sup' Finset.nonempty_range_add_one (fun i => f i ω)

lemma runningMax_nonneg {Ω : Type*} (f : ℕ → Ω → ℝ) (hf : ∀ n ω, 0 ≤ f n ω)
    (n : ℕ) (ω : Ω) : 0 ≤ runningMax f n ω := by
  exact (hf 0 ω).trans (Finset.le_sup' (fun i => f i ω) (Finset.mem_range.mpr (Nat.succ_pos _)))

lemma runningMax_le {Ω : Type*} (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (B : ℝ)
    (hf : ∀ i ≤ n, f i ω ≤ B) : runningMax f n ω ≤ B := by
  exact Finset.sup'_le _ _ (fun i hi => hf i (by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hi))

lemma measurable_runningMax {Ω : Type*} [MeasurableSpace Ω] (f : ℕ → Ω → ℝ)
    (hf : ∀ i, Measurable (f i)) (n : ℕ) : Measurable (runningMax f n) :=
  Finset.measurable_range_sup'' (fun i _ => hf i)

lemma dyadic_cover (x : ℝ) (hx : x ≤ 1) (L : ℕ) :
    x ≤ (1/2 : ℝ)^L + ∑ j ∈ Finset.range L, if (1/2 : ℝ)^(j+1) ≤ x then (1/2 : ℝ)^(j+1) else 0 := by
  induction L with
  | zero => simpa using hx
  | succ L ih =>
    rw [Finset.sum_range_succ]
    by_cases h : (1/2 : ℝ)^(L+1) ≤ x
    · rw [ite_eq_left h]
      have hh : (1/2 : ℝ)^(L+1) + (1/2 : ℝ)^(L+1) = (1/2 : ℝ)^L := by rw [pow_succ]; ring
      linarith
    · rw [ite_eq_right h,add_zero]
      exact (le_of_lt (lt_of_not_ge h)).trans (le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => by positivity)))

lemma martingale_maximal_real {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (f : ℕ → Ω → ℝ) (hf : Martingale f ℱ μ)
    (hpos : ∀ i ω, 0 ≤ f i ω) (n : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    a * μ.real {ω | a ≤ runningMax f n ω} ≤ ∫ ω, f 0 ω ∂μ := by
  have hc := maximal_ineq hf.submartingale hpos (ε := ⟨a,ha⟩) n
  have hle : (∫ ω in {ω | a ≤ runningMax f n ω}, f n ω ∂μ) ≤ ∫ ω, f n ω ∂μ :=
    setIntegral_le_integral (hf.integrable n) (Filter.Eventually.of_forall (hpos n))
  have hnon : 0 ≤ ∫ ω in {ω | a ≤ runningMax f n ω}, f n ω ∂μ := integral_nonneg (hpos n)
  have hh := ENNReal.toReal_mono (ENNReal.ofReal_ne_top : ENNReal.ofReal
    (∫ ω in {ω | a ≤ runningMax f n ω}, f n ω ∂μ) ≠ ⊤) hc
  have he := hf.setIntegral_eq (Nat.zero_le n) (s := Set.univ) MeasurableSet.univ
  simp only [setIntegral_univ] at he
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hnon] at hh
  exact hh.trans (hle.trans_eq he.symm)

lemma integrable_runningMax {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : ℕ → Ω → ℝ) (hf : ∀ i, Measurable (f i)) (hpos : ∀ i ω, 0 ≤ f i ω)
    (hle : ∀ i ω, f i ω ≤ 1) (n : ℕ) : Integrable (runningMax f n) μ := by
  apply (integrable_const (1 : ℝ)).mono' (measurable_runningMax f hf n).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ω => by
    rw [Real.norm_eq_abs,abs_of_nonneg (runningMax_nonneg f hpos n ω)]
    exact runningMax_le f n ω 1 (fun i _ => hle i ω))

lemma integral_runningMax_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (f : ℕ → Ω → ℝ) (hf : Martingale f ℱ μ)
    (hpos : ∀ i ω, 0 ≤ f i ω) (hle : ∀ i ω, f i ω ≤ 1)
    (E : Set Ω) (hE : MeasurableSet E) (hzero : ∀ i ω, ω ∉ E → f i ω = 0)
    (n L : ℕ) :
    (∫ ω, runningMax f n ω ∂μ) ≤ (1/2 : ℝ)^L * μ.real E + L * ∫ ω, f 0 ω ∂μ := by
  classical
  let A (j : ℕ) : Set Ω := {ω | (1/2 : ℝ)^(j+1) ≤ runningMax f n ω}
  have hfm (i : ℕ) : Measurable (f i) := (hf.stronglyMeasurable i).measurable.mono (ℱ.le i) le_rfl
  have hA (j : ℕ) : MeasurableSet (A j) := measurableSet_le measurable_const (measurable_runningMax f hfm n)
  have hI (j : ℕ) : Integrable ((A j).indicator (fun _ => (1/2 : ℝ)^(j+1))) μ :=
    (integrable_const _).indicator (hA j)
  have hB : Integrable (E.indicator (fun _ => (1/2 : ℝ)^L)) μ := (integrable_const _).indicator hE
  have hCv := integral_mono (integrable_runningMax μ f hfm hpos hle n)
    (hB.add (integrable_finsetSum _ (fun j _ => hI j)))
    (show ∀ ω, runningMax f n ω ≤ E.indicator (fun _ => (1/2 : ℝ)^L) ω +
      ∑ j ∈ Finset.range L, (A j).indicator (fun _ => (1/2 : ℝ)^(j+1)) ω from by
      intro ω
      by_cases hω : ω ∈ E
      · simp only [Set.indicator_of_mem hω]
        simpa only [Set.indicator_apply,Set.mem_ofPred_eq,A] using dyadic_cover
          (runningMax f n ω) (runningMax_le f n ω 1 (fun i _ => hle i ω)) L
      · have hz : runningMax f n ω = 0 := le_antisymm
          (runningMax_le f n ω 0 (fun i _ => le_of_eq (hzero i ω hω))) (runningMax_nonneg f hpos n ω)
        rw [hz,Set.indicator_of_notMem hω,zero_add]
        exact Finset.sum_nonneg (fun j _ => Set.indicator_nonneg (fun _ _ => by positivity) _))
  simp only [Pi.add_apply] at hCv
  rw [integral_add hB (integrable_finsetSum _ (fun j _ => hI j)),integral_finsetSum _ (fun j _ => hI j),
    integral_indicator_const _ hE,smul_eq_mul,mul_comm (μ.real E)] at hCv
  refine hCv.trans (add_le_add le_rfl ?_)
  calc
    (∑ j ∈ Finset.range L, ∫ ω, (A j).indicator (fun _ => (1/2 : ℝ)^(j+1)) ω ∂μ) ≤
        ∑ _j ∈ Finset.range L, ∫ ω, f 0 ω ∂μ := by
      apply Finset.sum_le_sum
      intro j _
      rw [integral_indicator_const _ (hA j),smul_eq_mul,mul_comm]
      exact martingale_maximal_real μ ℱ f hf hpos n _ (by positivity)
    _ = L * ∫ ω, f 0 ω ∂μ := by simp

noncomputable def posteriorMax {Ω ι : Type*} [Fintype ι] (w : ι → ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) : ℝ := ∑ e, runningMax (w e) n ω

lemma posterior_coord_le_one {Ω ι : Type*} [Fintype ι] (w : ι → ℕ → Ω → ℝ)
    (hpos : ∀ e i ω, 0 ≤ w e i ω) (hsum : ∀ i ω, ∑ e, w e i ω ≤ 1)
    (e : ι) (i : ℕ) (ω : Ω) : w e i ω ≤ 1 := by
  classical
  exact (Finset.single_le_sum (fun e _ => hpos e i ω) (Finset.mem_univ e)).trans (hsum i ω)

lemma integral_posteriorMax_bound {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (w : ι → ℕ → Ω → ℝ) (hw : ∀ e, Martingale (w e) ℱ μ)
    (hpos : ∀ e i ω, 0 ≤ w e i ω) (hsum : ∀ i ω, ∑ e, w e i ω ≤ 1)
    (E : Set Ω) (hE : MeasurableSet E) (hzero : ∀ e i ω, ω ∉ E → w e i ω = 0)
    (n L : ℕ) :
    (∫ ω, posteriorMax w n ω ∂μ) ≤ ((Fintype.card ι : ℝ) * (1/2 : ℝ)^L + L) * μ.real E := by
  classical
  have hfm (e : ι) (i : ℕ) : Measurable (w e i) :=
    ((hw e).stronglyMeasurable i).measurable.mono (ℱ.le i) le_rfl
  have hInt (e : ι) := integrable_runningMax μ (w e) (hfm e) (hpos e) (posterior_coord_le_one w hpos hsum e) n
  have hs : (∑ e, ∫ ω, w e 0 ω ∂μ) ≤ μ.real E := by
    rw [← integral_finsetSum _ (fun e _ => (hw e).integrable 0)]
    have hi := integral_mono (integrable_finsetSum _ (fun e _ => (hw e).integrable 0))
      ((integrable_const (1 : ℝ)).indicator hE) (show ∀ ω, (∑ e, w e 0 ω) ≤ E.indicator (fun _ => (1 : ℝ)) ω from by
        intro ω
        by_cases hω : ω ∈ E
        · simpa only [Set.indicator_of_mem hω] using hsum 0 ω
        · simp [Set.indicator_of_notMem hω,hzero _ _ _ hω])
    simpa only [integral_indicator_const _ hE,smul_eq_mul,mul_one] using hi
  calc
    (∫ ω, posteriorMax w n ω ∂μ) = ∑ e, ∫ ω, runningMax (w e) n ω ∂μ :=
      integral_finsetSum _ (fun e _ => hInt e)
    _ ≤ ∑ e, ((1/2 : ℝ)^L * μ.real E + L * ∫ ω, w e 0 ω ∂μ) :=
      Finset.sum_le_sum (fun e _ => integral_runningMax_bound μ ℱ (w e) (hw e) (hpos e)
        (posterior_coord_le_one w hpos hsum e) E hE (hzero e) n L)
    _ = (Fintype.card ι : ℝ) * (1/2 : ℝ)^L * μ.real E + L * ∑ e, ∫ ω, w e 0 ω ∂μ := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum]
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      rw [← Finset.mul_sum]
      ring
    _ ≤ (Fintype.card ι : ℝ) * (1/2 : ℝ)^L * μ.real E + L * μ.real E :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _))
    _ = _ := by ring

noncomputable def shiftedFiltration {Ω : Type*} [m : MeasurableSpace Ω]
    (ℱ : Filtration ℕ m) (s : ℕ) : Filtration ℕ m where
  seq i := ℱ (s+i)
  mono' _i _j hij := ℱ.mono (Nat.add_le_add_left hij s)
  le' i := ℱ.le (s+i)

lemma martingale_shift_indicator {Ω : Type*} [m : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ℱ : Filtration ℕ m)
    (f : ℕ → Ω → ℝ) (hf : Martingale f ℱ μ) (s : ℕ)
    (E : Set Ω) (hE : MeasurableSet[ℱ s] E) :
    Martingale (fun i => E.indicator (f (s+i))) (shiftedFiltration ℱ s) μ := by
  have hE' (i : ℕ) : MeasurableSet[ℱ (s+i)] E := ℱ.mono (Nat.le_add_right s i) E hE
  refine ⟨fun i => (hf.stronglyMeasurable (s+i)).indicator (hE' i),fun i j hij => ?_⟩
  refine (condExp_indicator (hf.integrable (s+j)) (hE' i)).trans ?_
  filter_upwards [hf.condExp_ae_eq (Nat.add_le_add_left hij s)] with ω hω
  by_cases h : ω ∈ E
  · simp only [Set.indicator_of_mem h,hω]
  · simp only [Set.indicator_of_notMem h]

lemma runningMax_future_bound {Ω : Type*} (f : ℕ → Ω → ℝ) (hpos : ∀ i ω, 0 ≤ f i ω)
    (n N : ℕ) (ω : Ω) :
    runningMax f N ω - runningMax f n ω ≤ runningMax (fun i => f (n+i)) N ω := by
  apply sub_le_iff_le_add.mpr
  apply runningMax_le
  intro i hi
  by_cases hin : i ≤ n
  · exact (Finset.le_sup' (fun j => f j ω) (Finset.mem_range.mpr (by omega))).trans
      (le_add_of_nonneg_left (runningMax_nonneg (fun j => f (n+j)) (fun j => hpos (n+j)) N ω))
  · have hi' : i-n < N+1 := by omega
    have hh := Finset.le_sup' (fun j => f (n+j) ω) (Finset.mem_range.mpr hi')
    have he : n+(i-n) = i := by omega
    rw [he] at hh
    exact hh.trans (le_add_of_nonneg_right (runningMax_nonneg f hpos n ω))

lemma posterior_future_energy {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (w : ι → ℕ → Ω → ℝ) (hw : ∀ e, Martingale (w e) ℱ μ)
    (hpos : ∀ e i ω, 0 ≤ w e i ω) (hsum : ∀ i ω, ∑ e, w e i ω ≤ 1)
    (L : ℕ) (hL : (Fintype.card ι : ℝ) * (1/2 : ℝ)^L ≤ 1)
    (n N : ℕ) (E : Set Ω) (hE : MeasurableSet[ℱ n] E) :
    (∫ ω in E, (posteriorMax w N ω - posteriorMax w n ω) ∂μ) ≤ (L+1 : ℝ) * μ.real E := by
  classical
  let g : ι → ℕ → Ω → ℝ := fun e i => E.indicator (w e (n+i))
  have hg (e : ι) := martingale_shift_indicator μ ℱ (w e) (hw e) n E hE
  have hgp (e : ι) (i : ℕ) (ω : Ω) : 0 ≤ g e i ω :=
    Set.indicator_nonneg (fun ω _ => hpos e (n+i) ω) ω
  have hgs (i : ℕ) (ω : Ω) : ∑ e, g e i ω ≤ 1 := by
    by_cases hω : ω ∈ E
    · simpa only [g,Set.indicator_of_mem hω] using hsum (n+i) ω
    · simp only [g,Set.indicator_of_notMem hω,Finset.sum_const_zero]; norm_num
  have hgz (e : ι) (i : ℕ) (ω : Ω) (hω : ω ∉ E) : g e i ω = 0 := Set.indicator_of_notMem hω _
  have hE0 := ℱ.le n E hE
  have hb := integral_posteriorMax_bound μ (shiftedFiltration ℱ n) g hg hgp hgs E hE0 hgz N L
  have hfm (e : ι) (i : ℕ) : Measurable (w e i) := ((hw e).stronglyMeasurable i).measurable.mono (ℱ.le i) le_rfl
  have hpm (i : ℕ) : Integrable (posteriorMax w i) μ :=
    integrable_finsetSum _ (fun e _ => integrable_runningMax μ (w e) (hfm e) (hpos e)
      (posterior_coord_le_one w hpos hsum e) i)
  have hgfm (e : ι) (i : ℕ) : Measurable (g e i) :=
    ((hg e).stronglyMeasurable i).measurable.mono ((shiftedFiltration ℱ n).le i) le_rfl
  have hpg : Integrable (posteriorMax g N) μ := integrable_finsetSum _ (fun e _ =>
    integrable_runningMax μ (g e) (hgfm e) (hgp e) (posterior_coord_le_one g hgp hgs e) N)
  have hi := integral_mono (((hpm N).sub (hpm n)).indicator hE0) hpg
    (show ∀ ω, E.indicator (fun ω => posteriorMax w N ω - posteriorMax w n ω) ω ≤ posteriorMax g N ω from by
      intro ω
      by_cases hω : ω ∈ E
      · rw [Set.indicator_of_mem hω]
        simp only [posteriorMax,← Finset.sum_sub_distrib]
        apply Finset.sum_le_sum
        intro e _

        have hr : runningMax (g e) N ω = runningMax (fun i => w e (n+i)) N ω := by
          unfold runningMax
          congr 1
          funext i
          exact Set.indicator_of_mem hω _
        rw [hr]
        exact runningMax_future_bound (w e) (hpos e) n N ω
      · rw [Set.indicator_of_notMem hω]
        exact Finset.sum_nonneg (fun e _ => runningMax_nonneg (g e) (hgp e) N ω))
  rw [integral_indicator hE0] at hi
  exact hi.trans (hb.trans (mul_le_mul_of_nonneg_right (by linarith : (Fintype.card ι : ℝ) * (1/2 : ℝ)^L + L ≤ L+1) measureReal_nonneg))

def crossingEvent {Ω : Type*} (A : ℕ → Ω → ℝ) (x : ℝ) (i : ℕ) : Set Ω :=
  {ω | x < A i ω ∧ ∀ j < i, A j ω ≤ x}

lemma crossingEvent_measurable {Ω : Type*} [m : MeasurableSpace Ω] (ℱ : Filtration ℕ m)
    (A : ℕ → Ω → ℝ) (hA : ∀ i, Measurable[ℱ i] (A i)) (x : ℝ) (i : ℕ) :
    MeasurableSet[ℱ i] (crossingEvent A x i) := by
  apply MeasurableSet.inter (measurableSet_lt measurable_const (hA i))
  change MeasurableSet[ℱ i] {ω | ∀ j < i, A j ω ≤ x}
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter (fun j => MeasurableSet.iInter (fun hj =>
    measurableSet_le ((hA j).mono (ℱ.mono (Nat.le_of_lt hj)) le_rfl) measurable_const))

lemma crossingEvent_disjoint {Ω : Type*} (A : ℕ → Ω → ℝ) (x : ℝ) :
    Pairwise (fun i j => Disjoint (crossingEvent A x i) (crossingEvent A x j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro ω ⟨hi,hi'⟩ ⟨hj,hj'⟩
  rcases lt_or_gt_of_ne hij with h | h
  · exact (not_lt_of_ge (hj' i h)) hi
  · exact (not_lt_of_ge (hi' j h)) hj

lemma union_crossingEvent {Ω : Type*} (A : ℕ → Ω → ℝ) (hmono : ∀ ω, Monotone (fun i => A i ω))
    (x : ℝ) (N : ℕ) : (⋃ i ∈ Finset.range (N+1), crossingEvent A x i) = {ω | x < A N ω} := by
  ext ω
  simp only [Set.mem_iUnion,Finset.mem_range,Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i,hi,hai⟩
    exact hai.1.trans_le (hmono ω (by omega))
  · intro hN
    have he : ∃ i, x < A i ω := ⟨N,hN⟩
    refine ⟨Nat.find he,by have h := Nat.find_min' he hN; omega,Nat.find_spec he,?_⟩
    intro j hj
    exact le_of_not_gt (Nat.find_min he hj)

lemma crossingEvent_overshoot {Ω : Type*} (A : ℕ → Ω → ℝ)
    (h0 : ∀ ω, A 0 ω ≤ 1) (hj : ∀ i ω, A (i+1) ω ≤ A i ω + 1)
    (x : ℝ) (hx : 1 ≤ x) (i : ℕ) (ω : Ω) (hω : ω ∈ crossingEvent A x i) :
    A i ω ≤ x+1 := by
  cases i with
  | zero => exact ((hω.1.not_ge ((h0 ω).trans hx))).elim
  | succ i => exact (hj i ω).trans (add_le_add (hω.2 i (Nat.lt_succ_self i)) le_rfl)

lemma increasing_energy_tail_step {Ω : Type*} [m : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ℱ : Filtration ℕ m)
    (A : ℕ → Ω → ℝ) (hA : ∀ i, Measurable[ℱ i] (A i)) (hI : ∀ i, Integrable (A i) μ)
    (hmono : ∀ ω, Monotone (fun i => A i ω)) (h0 : ∀ ω, A 0 ω ≤ 1)
    (hj : ∀ i ω, A (i+1) ω ≤ A i ω + 1) (C : ℝ) (hC : 0 < C)
    (henergy : ∀ i N E, MeasurableSet[ℱ i] E →
      (∫ ω in E, (A N ω - A i ω) ∂μ) ≤ C * μ.real E)
    (N : ℕ) (x : ℝ) (hx : 1 ≤ x) :
    μ.real {ω | x+(2*C+1) < A N ω} ≤ (1/2 : ℝ) * μ.real {ω | x < A N ω} := by
  classical
  let V : Set Ω := {ω | x+(2*C+1) < A N ω}
  have hV : MeasurableSet V := measurableSet_lt measurable_const ((hA N).mono (ℱ.le N) le_rfl)
  have hEm (i : ℕ) := crossingEvent_measurable ℱ A hA x i
  have hEm0 (i : ℕ) : MeasurableSet (crossingEvent A x i) := ℱ.le i _ (hEm i)
  have hEi (i : ℕ) (hi : i ∈ Finset.range (N+1)) :
      μ.real (crossingEvent A x i ∩ V) ≤ (1/2 : ℝ) * μ.real (crossingEvent A x i) := by
    have hiN : i ≤ N := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hi
    have hbound := integral_mono ((integrable_const (2*C)).indicator ((hEm0 i).inter hV))
      (((hI N).sub (hI i)).indicator (hEm0 i))
      (show ∀ ω, (crossingEvent A x i ∩ V).indicator (fun _ => 2*C) ω ≤
          (crossingEvent A x i).indicator (fun ω => A N ω - A i ω) ω from by
        intro ω
        by_cases hω : ω ∈ crossingEvent A x i
        · rw [Set.indicator_of_mem hω]
          by_cases hωV : ω ∈ V
          · rw [Set.indicator_of_mem (show ω ∈ crossingEvent A x i ∩ V from ⟨hω,hωV⟩)]
            have hov := crossingEvent_overshoot A h0 hj x hx i ω hω
            change x+(2*C+1) < A N ω at hωV
            linarith
          · rw [Set.indicator_of_notMem (show ω ∉ crossingEvent A x i ∩ V from fun h => hωV h.2)]
            exact sub_nonneg.mpr (hmono ω hiN)
        · rw [Set.indicator_of_notMem hω,Set.indicator_of_notMem
            (show ω ∉ crossingEvent A x i ∩ V from fun h => hω h.1)])
    rw [integral_indicator_const _ ((hEm0 i).inter hV),smul_eq_mul,
      integral_indicator (hEm0 i)] at hbound
    have he := hbound.trans (henergy i N _ (hEm i))
    nlinarith
  have hsub : V ⊆ {ω | x < A N ω} := by intro ω hω; change x+(2*C+1) < A N ω at hω; dsimp; linarith
  have heV : V = ⋃ i ∈ Finset.range (N+1), crossingEvent A x i ∩ V := by
    ext ω
    simp only [Set.mem_iUnion,Set.mem_inter_iff]
    constructor
    · intro hω
      have hm : ω ∈ ⋃ i ∈ Finset.range (N+1), crossingEvent A x i := by
        rw [union_crossingEvent A hmono x N]
        exact hsub hω
      obtain ⟨i,hi,hh⟩ := Set.mem_iUnion₂.mp hm
      exact ⟨i,hi,hh,hω⟩
    · rintro ⟨i,hi,hh,hω⟩
      exact hω
  have hd : (↑(Finset.range (N+1)) : Set ℕ).PairwiseDisjoint (crossingEvent A x) :=
    fun _ _ _ _ hij => crossingEvent_disjoint A x hij
  calc
    μ.real V = ∑ i ∈ Finset.range (N+1), μ.real (crossingEvent A x i ∩ V) := by
      calc
        μ.real V = μ.real (⋃ i ∈ Finset.range (N+1), crossingEvent A x i ∩ V) := congrArg μ.real heV
        _ = _ := measureReal_biUnion_finset (μ := μ)
          (fun _ hi _ hj hij => (hd hi hj hij).mono inf_le_left inf_le_left)
          (fun i _ => (hEm0 i).inter hV) (fun i _ => measure_ne_top μ _)
    _ ≤ ∑ i ∈ Finset.range (N+1), (1/2 : ℝ) * μ.real (crossingEvent A x i) := Finset.sum_le_sum hEi
    _ = (1/2 : ℝ) * μ.real {ω | x < A N ω} := by
      rw [← Finset.mul_sum,← measureReal_biUnion_finset (μ := μ) hd (fun i _ => hEm0 i),union_crossingEvent A hmono]

lemma increasing_energy_geometric_tail {Ω : Type*} [m : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m)
    (A : ℕ → Ω → ℝ) (hA : ∀ i, Measurable[ℱ i] (A i)) (hI : ∀ i, Integrable (A i) μ)
    (hmono : ∀ ω, Monotone (fun i => A i ω)) (h0 : ∀ ω, A 0 ω ≤ 1)
    (hj : ∀ i ω, A (i+1) ω ≤ A i ω + 1) (C : ℝ) (hC : 0 < C)
    (henergy : ∀ i N E, MeasurableSet[ℱ i] E →
      (∫ ω in E, (A N ω - A i ω) ∂μ) ≤ C * μ.real E)
    (N k : ℕ) : μ.real {ω | 1+k*(2*C+1) < A N ω} ≤ (1/2 : ℝ)^k := by
  induction k with
  | zero => simpa only [Nat.cast_zero,zero_mul,add_zero,pow_zero] using measureReal_le_one (μ := μ) (s := {ω | 1 < A N ω})
  | succ k ih =>
    have hEq : (1 + (k+1 : ℕ)*(2*C+1) : ℝ) = 1 + k*(2*C+1) + (2*C+1) := by push_cast; ring
    rw [hEq]
    have ht := increasing_energy_tail_step μ ℱ A hA hI hmono h0 hj C hC henergy N
      (1+k*(2*C+1)) (by
        have h : 0 ≤ (k : ℝ)*(2*C+1) := by positivity
        linarith)
    exact ht.trans (by rw [pow_succ]; nlinarith)

lemma runningMax_mono {Ω : Type*} (f : ℕ → Ω → ℝ) (ω : Ω) : Monotone (fun n => runningMax f n ω) := by
  intro n N hnN
  apply runningMax_le
  intro i hi
  exact Finset.le_sup' (fun j => f j ω) (Finset.mem_range.mpr (by omega))

lemma runningMax_step {Ω : Type*} (f : ℕ → Ω → ℝ) (hpos : ∀ i ω, 0 ≤ f i ω)
    (n : ℕ) (ω : Ω) : runningMax f (n+1) ω ≤ runningMax f n ω + f (n+1) ω := by
  apply runningMax_le
  intro i hi
  by_cases hin : i ≤ n
  · have hh := Finset.le_sup' (fun j => f j ω) (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hin))
    exact hh.trans (le_add_of_nonneg_right (hpos (n+1) ω))
  · have he : i = n+1 := by omega
    rw [he]
    exact le_add_of_nonneg_left (runningMax_nonneg f hpos n ω)

lemma posteriorMax_mono {Ω ι : Type*} [Fintype ι] (w : ι → ℕ → Ω → ℝ) (ω : Ω) :
    Monotone (fun n => posteriorMax w n ω) := by
  intro n N hnN
  exact Finset.sum_le_sum (fun e _ => runningMax_mono (w e) ω hnN)

lemma posteriorMax_step {Ω ι : Type*} [Fintype ι] (w : ι → ℕ → Ω → ℝ)
    (hpos : ∀ e i ω, 0 ≤ w e i ω) (hsum : ∀ i ω, ∑ e, w e i ω ≤ 1) (n : ℕ) (ω : Ω) :
    posteriorMax w (n+1) ω ≤ posteriorMax w n ω + 1 := by
  calc
    _ ≤ ∑ e, (runningMax (w e) n ω + w e (n+1) ω) :=
      Finset.sum_le_sum (fun e _ => runningMax_step (w e) (hpos e) n ω)
    _ = posteriorMax w n ω + ∑ e, w e (n+1) ω := Finset.sum_add_distrib
    _ ≤ _ := add_le_add le_rfl (hsum (n+1) ω)

lemma posteriorMax_adapted {Ω ι : Type*} [m : MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (ℱ : Filtration ℕ m) (w : ι → ℕ → Ω → ℝ)
    (hw : ∀ e, Martingale (w e) ℱ μ) (n : ℕ) : Measurable[ℱ n] (posteriorMax w n) := by
  let : MeasurableSpace Ω := ℱ n
  apply Finset.measurable_sum
  intro e _
  exact Finset.measurable_range_sup'' (fun i hi =>
    ((hw e).stronglyMeasurable i).measurable.mono (ℱ.mono hi) le_rfl)

lemma posteriorMax_integrable {Ω ι : Type*} [m : MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ℱ : Filtration ℕ m) (w : ι → ℕ → Ω → ℝ)
    (hw : ∀ e, Martingale (w e) ℱ μ) (hpos : ∀ e i ω, 0 ≤ w e i ω)
    (hsum : ∀ i ω, ∑ e, w e i ω ≤ 1) (n : ℕ) : Integrable (posteriorMax w n) μ := by
  apply integrable_finsetSum
  intro e _
  exact integrable_runningMax μ (w e)
    (fun i => ((hw e).stronglyMeasurable i).measurable.mono (ℱ.le i) le_rfl)
    (hpos e) (posterior_coord_le_one w hpos hsum e) n

lemma posteriorMax_geometric_tail {Ω ι : Type*} [m : MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m)
    (w : ι → ℕ → Ω → ℝ) (hw : ∀ e, Martingale (w e) ℱ μ)
    (hpos : ∀ e i ω, 0 ≤ w e i ω) (hsum : ∀ i ω, ∑ e, w e i ω ≤ 1)
    (L : ℕ) (hL : (Fintype.card ι : ℝ) * (1/2 : ℝ)^L ≤ 1) (N k : ℕ) :
    μ.real {ω | 1+k*(2*(L+1)+1) < posteriorMax w N ω} ≤ (1/2 : ℝ)^k := by
  apply increasing_energy_geometric_tail μ ℱ (posteriorMax w)
    (posteriorMax_adapted μ ℱ w hw) (posteriorMax_integrable μ ℱ w hw hpos hsum)
    (posteriorMax_mono w) _ (posteriorMax_step w hpos hsum) (L+1) (by positivity)
    (posterior_future_energy μ ℱ w hw hpos hsum L hL) N k
  intro ω
  apply (Finset.sum_le_sum (fun e _ => runningMax_le (w e) 0 ω (w e 0 ω) (by
    intro i hi
    have : i = 0 := by omega
    subst i
    exact le_rfl))).trans
  exact hsum 0 ω

lemma energy_exp_cover (b x : ℝ) (hb : 0 < b) (M : ℕ) (hx : x ≤ 1+M*b) :
    Real.exp (Real.log (3/2) * (x-1) / b) ≤
      1 + ∑ k ∈ Finset.range M, if 1+k*b < x then (3/2 : ℝ)^(k+1) else 0 := by
  have hl : 0 < Real.log (3/2) := Real.log_pos (by norm_num)
  induction M with
  | zero =>
    simp only [Nat.cast_zero,zero_mul,add_zero] at hx
    simp only [Finset.range_zero,Finset.sum_empty,add_zero]
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hl.le (by linarith)) hb.le
  | succ M ih =>
    rw [Finset.sum_range_succ]
    by_cases h : x ≤ 1+M*b
    · exact (ih h).trans (by
        have hh : 0 ≤ if 1+(M : ℝ)*b < x then (3/2 : ℝ)^(M+1) else 0 := by positivity
        linarith)
    · rw [ite_eq_left (lt_of_not_ge h)]
      have hv : Real.log (3/2) * (x-1) / b ≤ (M+1 : ℕ)*Real.log (3/2) := by
        apply (div_le_iff₀ hb).mpr
        have := mul_le_mul_of_nonneg_left (show x-1 ≤ (M+1 : ℕ)*b by linarith) hl.le
        nlinarith
      have he := Real.exp_le_exp.mpr hv
      rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0 : ℝ) < 3/2)] at he
      exact he.trans (by
        have hs : 0 ≤ ∑ k ∈ Finset.range M, if 1+(k : ℝ)*b < x then (3/2 : ℝ)^(k+1) else 0 :=
          Finset.sum_nonneg (fun k _ => by positivity)
        linarith)

lemma geometric_three_quarter_sum (M : ℕ) : ∑ k ∈ Finset.range M, (3/4 : ℝ)^k ≤ 4 := by
  have he : (∑ k ∈ Finset.range M, (3/4 : ℝ)^k) + 4*(3/4 : ℝ)^M = 4 := by
    induction M with
    | zero => simp
    | succ M ih => rw [Finset.sum_range_succ,pow_succ]; nlinarith
  have hp : 0 ≤ (3/4 : ℝ)^M := by positivity
  linarith

lemma geometric_tail_exponential {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X) (M : ℕ)
    (hbound : ∀ ω, X ω ≤ M)
    (b : ℝ) (hb : 1 ≤ b)
    (htail : ∀ k : ℕ, μ.real {ω | 1+k*b < X ω} ≤ (1/2 : ℝ)^k) :
    (∫ ω, Real.exp (Real.log (3/2) / b * X ω) ∂μ) ≤ 12 := by
  classical
  have hb0 : 0 < b := by linarith
  have hl : 0 < Real.log (3/2) := Real.log_pos (by norm_num)
  let c := Real.log (3/2) / b
  have hc : 0 < c := div_pos hl hb0
  have hEint : Integrable (fun ω => Real.exp (c * (X ω-1))) μ := by
    apply (integrable_const (Real.exp (c*(M : ℝ)))).mono' ((hX.sub measurable_const).const_mul c).exp.aestronglyMeasurable
    filter_upwards [] with ω
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    change c * (X ω-1) ≤ c * (M : ℝ)
    exact mul_le_mul_of_nonneg_left (by have := hbound ω; linarith) hc.le
  let A (k : ℕ) : Set Ω := {ω | 1+k*b < X ω}
  have hA (k : ℕ) : MeasurableSet (A k) := measurableSet_lt measurable_const hX
  have hI (k : ℕ) : Integrable ((A k).indicator (fun _ => (3/2 : ℝ)^(k+1))) μ :=
    (integrable_const _).indicator (hA k)
  have hi := integral_mono hEint ((integrable_const (1 : ℝ)).add
    (integrable_finsetSum _ (fun k _ => hI k))) (show ∀ ω, Real.exp (c*(X ω-1)) ≤
        1 + ∑ k ∈ Finset.range M, (A k).indicator (fun _ => (3/2 : ℝ)^(k+1)) ω from by
      intro ω
      have hB : X ω ≤ 1 + (M : ℝ)*b := by
        have hh : (M : ℝ) ≤ M*b := by nlinarith [Nat.cast_nonneg (α := ℝ) M]
        linarith [hbound ω]
      have hh := energy_exp_cover b (X ω) hb0 M hB
      simpa only [c,div_mul_eq_mul_div,Set.indicator_apply,Set.mem_ofPred_eq,A] using hh)
  simp only [Pi.add_apply] at hi
  rw [integral_add (integrable_const _) (integrable_finsetSum _ (fun k _ => hI k)),
    integral_const,probReal_univ,one_smul,integral_finsetSum _ (fun k _ => hI k)] at hi
  have hb7 : (∫ ω, Real.exp (c*(X ω-1)) ∂μ) ≤ 7 := by
    apply hi.trans
    have hh : (∑ k ∈ Finset.range M, ∫ ω, (A k).indicator (fun _ => (3/2 : ℝ)^(k+1)) ω ∂μ) ≤ 6 := by
      calc
        _ ≤ ∑ k ∈ Finset.range M, (3/2 : ℝ)^(k+1) * (1/2 : ℝ)^k := by
          apply Finset.sum_le_sum
          intro k _
          rw [integral_indicator_const _ (hA k),smul_eq_mul,mul_comm]
          exact mul_le_mul_of_nonneg_left (htail k) (by positivity)
        _ = (3/2 : ℝ) * ∑ k ∈ Finset.range M, (3/4 : ℝ)^k := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          rw [pow_succ]
          calc (3/2 : ℝ)^k * (3/2) * (1/2)^k = (3/2) * ((3/2)^k*(1/2)^k) := by ring
               _ = _ := by rw [← mul_pow]; norm_num
        _ ≤ 6 := by nlinarith [geometric_three_quarter_sum M]
    linarith
  have hc_bound : Real.exp c ≤ 3/2 := by
    apply (Real.exp_le_exp.mpr (show c ≤ Real.log (3/2) from (div_le_iff₀ hb0).mpr (by nlinarith))) |>.trans_eq
    exact Real.exp_log (by norm_num)
  have hfun : (fun ω => Real.exp (c * X ω)) = fun ω => Real.exp c * Real.exp (c*(X ω-1)) := by
    funext ω
    rw [← Real.exp_add]
    congr 1
    ring
  rw [show (fun ω => Real.exp (Real.log (3/2) / b * X ω)) = (fun ω => Real.exp (c * X ω)) from rfl,hfun,integral_const_mul]
  have hmul := mul_le_mul_of_nonneg_left hb7 (Real.exp_nonneg c)
  nlinarith

lemma integrable_exp_of_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (X : Ω → ℝ) (hX : Measurable X) (B c : ℝ)
    (hbound : ∀ ω, X ω ≤ B) (hc : 0 ≤ c) : Integrable (fun ω => Real.exp (c*X ω)) μ := by
  apply (integrable_const (Real.exp (c*B))).mono' (hX.const_mul c).exp.aestronglyMeasurable
  filter_upwards [] with ω
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hbound ω) hc)

lemma posteriorMax_nonneg {Ω ι : Type*} [Fintype ι] (w : ι → ℕ → Ω → ℝ)
    (hpos : ∀ e i ω, 0 ≤ w e i ω) (n : ℕ) (ω : Ω) : 0 ≤ posteriorMax w n ω :=
  Finset.sum_nonneg (fun e _ => runningMax_nonneg (w e) (hpos e) n ω)

lemma posteriorMax_le_card {Ω ι : Type*} [Fintype ι] (w : ι → ℕ → Ω → ℝ)
    (hpos : ∀ e i ω, 0 ≤ w e i ω) (hsum : ∀ i ω, ∑ e, w e i ω ≤ 1) (n : ℕ) (ω : Ω) :
    posteriorMax w n ω ≤ Fintype.card ι := by
  calc
    _ ≤ ∑ _e : ι, (1 : ℝ) := Finset.sum_le_sum (fun e _ =>
      runningMax_le (w e) n ω 1 (fun i _ => posterior_coord_le_one w hpos hsum e i ω))
    _ = _ := by simp

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

noncomputable def posteriorSup {Ω ι : Type*} [Fintype ι] (w : ι → ℕ → Ω → ℝ)
    (ω : Ω) : ℝ := ⨆ n : ℕ, posteriorMax w n ω

lemma posteriorSup_bounds {Ω ι : Type*} [Fintype ι] (w : ι → ℕ → Ω → ℝ)
    (hpos : ∀ e i ω, 0 ≤ w e i ω) (hsum : ∀ i ω, ∑ e, w e i ω ≤ 1) (ω : Ω) :
    0 ≤ posteriorSup w ω ∧ posteriorSup w ω ≤ Fintype.card ι := by
  have hb : BddAbove (Set.range (fun n => posteriorMax w n ω)) :=
    ⟨Fintype.card ι,by rintro _ ⟨n,rfl⟩; exact posteriorMax_le_card w hpos hsum n ω⟩
  exact ⟨(posteriorMax_nonneg w hpos 0 ω).trans (le_ciSup hb 0),
    ciSup_le (fun n => posteriorMax_le_card w hpos hsum n ω)⟩

lemma posteriorMax_tendsto {Ω ι : Type*} [Fintype ι] (w : ι → ℕ → Ω → ℝ)
    (hpos : ∀ e i ω, 0 ≤ w e i ω) (hsum : ∀ i ω, ∑ e, w e i ω ≤ 1) (ω : Ω) :
    Tendsto (fun n => posteriorMax w n ω) atTop (𝓝 (posteriorSup w ω)) := by
  exact tendsto_atTop_ciSup (posteriorMax_mono w ω)
    ⟨Fintype.card ι,by rintro _ ⟨n,rfl⟩; exact posteriorMax_le_card w hpos hsum n ω⟩

lemma measurable_posteriorSup {Ω ι : Type*} [m : MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (ℱ : Filtration ℕ m) (w : ι → ℕ → Ω → ℝ)
    (hw : ∀ e, Martingale (w e) ℱ μ) : Measurable (posteriorSup w) :=
  Measurable.iSup (fun n => (posteriorMax_adapted μ ℱ w hw n).mono (ℱ.le n) le_rfl)

lemma posteriorSup_exponential {Ω ι : Type*} [m : MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m)
    (w : ι → ℕ → Ω → ℝ) (hw : ∀ e, Martingale (w e) ℱ μ)
    (hpos : ∀ e i ω, 0 ≤ w e i ω) (hsum : ∀ i ω, ∑ e, w e i ω ≤ 1)
    (L : ℕ) (hL : (Fintype.card ι : ℝ)*(1/2 : ℝ)^L ≤ 1) :
    (∫ ω, Real.exp (Real.log (3/2) / (2*(L+1)+1) * posteriorSup w ω) ∂μ) ≤ 12 := by
  let c : ℝ := Real.log (3/2) / (2*(L+1)+1)
  have hc : 0 ≤ c := div_nonneg (Real.log_nonneg (by norm_num)) (by positivity)
  have hM (n : ℕ) : Measurable (posteriorMax w n) := (posteriorMax_adapted μ ℱ w hw n).mono (ℱ.le n) le_rfl
  have hI (n : ℕ) : Integrable (fun ω => Real.exp (c*posteriorMax w n ω)) μ :=
    integrable_exp_of_bound μ _ (hM n) (Fintype.card ι) c (posteriorMax_le_card w hpos hsum n) hc
  have hS : Integrable (fun ω => Real.exp (c*posteriorSup w ω)) μ :=
    integrable_exp_of_bound μ _ (measurable_posteriorSup μ ℱ w hw) (Fintype.card ι) c
      (fun ω => (posteriorSup_bounds w hpos hsum ω).2) hc
  have ht := integral_tendsto_of_tendsto_of_monotone hI hS
    (Filter.Eventually.of_forall (fun ω n N hnN => Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (posteriorMax_mono w ω hnN) hc)))
    (Filter.Eventually.of_forall (fun ω => Real.continuous_exp.continuousAt.tendsto.comp
      ((posteriorMax_tendsto w hpos hsum ω).const_mul c)))
  apply le_of_tendsto ht
  filter_upwards [] with n
  exact geometric_tail_exponential μ (posteriorMax w n) (hM n) (Fintype.card ι)
    (posteriorMax_le_card w hpos hsum n) (2*(L+1)+1) (by have := Nat.cast_nonneg (α := ℝ) L; linarith)
    (posteriorMax_geometric_tail μ ℱ w hw hpos hsum L hL n)

noncomputable def goodPosteriorSet {Ω ι : Type*} [Fintype ι]
    (w : ι → ℕ → Ω → ℝ) (n : ℕ) : Set Ω := {ω | (∀ e, 0 ≤ w e n ω) ∧ ∑ e, w e n ω ≤ 1}

noncomputable def clippedPosterior {Ω ι : Type*} [Fintype ι]
    (w : ι → ℕ → Ω → ℝ) (e : ι) (n : ℕ) : Ω → ℝ := (goodPosteriorSet w n).indicator (w e n)

lemma measurableSet_goodPosterior {Ω ι : Type*} [m : MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (ℱ : Filtration ℕ m) (w : ι → ℕ → Ω → ℝ)
    (hw : ∀ e, Martingale (w e) ℱ μ) (n : ℕ) : MeasurableSet[ℱ n] (goodPosteriorSet w n) := by
  let : MeasurableSpace Ω := ℱ n
  unfold goodPosteriorSet
  rw [Set.ofPred_and,Set.ofPred_forall]
  apply MeasurableSet.inter
  ·
    exact MeasurableSet.iInter (fun e => measurableSet_le measurable_const ((hw e).stronglyMeasurable n).measurable)
  · exact measurableSet_le (Finset.measurable_sum _ (fun e _ => ((hw e).stronglyMeasurable n).measurable)) measurable_const

lemma clippedPosterior_bounds {Ω ι : Type*} [Fintype ι] (w : ι → ℕ → Ω → ℝ) :
    (∀ e n ω, 0 ≤ clippedPosterior w e n ω) ∧ (∀ n ω, ∑ e, clippedPosterior w e n ω ≤ 1) := by
  constructor
  · intro e n ω
    by_cases hω : ω ∈ goodPosteriorSet w n
    · simpa only [clippedPosterior,Set.indicator_of_mem hω] using hω.1 e
    · simp only [clippedPosterior,Set.indicator_of_notMem hω,le_refl]
  · intro n ω
    by_cases hω : ω ∈ goodPosteriorSet w n
    · simpa only [clippedPosterior,Set.indicator_of_mem hω] using hω.2
    · simp only [clippedPosterior,Set.indicator_of_notMem hω,Finset.sum_const_zero]; norm_num

lemma clippedPosterior_ae_eq {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (w : ι → ℕ → Ω → ℝ)
    (hpos : ∀ e n, ∀ᵐ ω ∂μ, 0 ≤ w e n ω) (hsum : ∀ n, ∀ᵐ ω ∂μ, ∑ e, w e n ω ≤ 1)
    (e : ι) (n : ℕ) : w e n =ᵐ[μ] clippedPosterior w e n := by
  filter_upwards [(ae_all_iff.mpr (fun e => hpos e n)),hsum n] with ω hω hsumω
  exact (Set.indicator_of_mem (show ω ∈ goodPosteriorSet w n from ⟨hω,hsumω⟩) _).symm

lemma clippedPosterior_martingale {Ω ι : Type*} [m : MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (ℱ : Filtration ℕ m) (w : ι → ℕ → Ω → ℝ)
    (hw : ∀ e, Martingale (w e) ℱ μ)
    (hpos : ∀ e n, ∀ᵐ ω ∂μ, 0 ≤ w e n ω) (hsum : ∀ n, ∀ᵐ ω ∂μ, ∑ e, w e n ω ≤ 1) (e : ι) :
    Martingale (clippedPosterior w e) ℱ μ := by
  apply (hw e).congr
  · intro n
    exact ((hw e).stronglyMeasurable n).indicator (measurableSet_goodPosterior μ ℱ w hw n)
  · exact clippedPosterior_ae_eq μ w hpos hsum e

lemma posteriorSup_congr_ae {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (w v : ι → ℕ → Ω → ℝ) (h : ∀ e n, w e n =ᵐ[μ] v e n) :
    posteriorSup w =ᵐ[μ] posteriorSup v := by
  filter_upwards [ae_all_iff.mpr (fun e => ae_all_iff.mpr (h e))] with ω hω
  unfold posteriorSup
  congr 1
  funext n
  apply Finset.sum_congr rfl
  intro e _
  unfold runningMax
  congr 1
  funext i
  exact hω e i

noncomputable def posteriorLevel (m : ℕ) : ℕ := ⌈Real.log (m+1) / Real.log 2⌉₊

lemma posteriorLevel_dyadic (m : ℕ) : (m : ℝ) * (1/2 : ℝ)^(posteriorLevel m) ≤ 1 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hceil := Nat.le_ceil (Real.log (m+1) / Real.log 2)
  have hlog : Real.log (m+1) ≤ (posteriorLevel m : ℝ) * Real.log 2 :=
    (div_le_iff₀ h2).mp hceil
  have he := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (by positivity),Real.exp_nat_mul,Real.exp_log (by norm_num)] at he
  have hpow : (2 : ℝ)^posteriorLevel m * (1/2 : ℝ)^posteriorLevel m = 1 := by
    rw [← mul_pow]; norm_num
  have hh := mul_le_mul_of_nonneg_right he (by positivity : 0 ≤ (1/2 : ℝ)^posteriorLevel m)
  rw [hpow] at hh
  have hp : 0 ≤ (1/2 : ℝ)^posteriorLevel m := by positivity
  nlinarith

lemma posteriorLevel_scale (m : ℕ) (hm : 1 ≤ m) :
    2*((posteriorLevel m : ℝ)+1)+1 ≤ 7 * Real.log (m+1) / Real.log 2 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hB : Real.log 2 ≤ Real.log (m+1) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ m+1 by omega))
  have hq : 0 ≤ Real.log (m+1) / Real.log 2 := div_nonneg (h2.le.trans hB) h2.le
  have hceil : (posteriorLevel m : ℝ) < Real.log (m+1)/Real.log 2 + 1 := Nat.ceil_lt_add_one hq
  have hh : 1 ≤ Real.log (m+1)/Real.log 2 := (le_div_iff₀ h2).mpr (by simpa using hB)
  have he : 7*Real.log (m+1)/Real.log 2 = 7*(Real.log (m+1)/Real.log 2) := by ring
  rw [he]
  linarith

noncomputable def posteriorExponent : ℝ := Real.log (3/2) * Real.log 2 / 7

lemma posteriorExponent_pos : 0 < posteriorExponent := by
  exact div_pos (mul_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))) (by norm_num)

lemma posteriorExponent_le (m : ℕ) (hm : 1 ≤ m) :
    posteriorExponent / Real.log (m+1) ≤ Real.log (3/2) / (2*((posteriorLevel m : ℝ)+1)+1) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hB : 0 < Real.log (m+1) := Real.log_pos (by exact_mod_cast (show 1 < m+1 by omega))
  have hb : 0 < 2*((posteriorLevel m : ℝ)+1)+1 := by positivity
  have hscale := (le_div_iff₀ h2).mp (posteriorLevel_scale m hm)
  apply (div_le_div_iff₀ hB hb).mpr
  unfold posteriorExponent
  have hl : 0 ≤ Real.log (3/2) := Real.log_nonneg (by norm_num)
  have hh := mul_le_mul_of_nonneg_left hscale hl
  nlinarith

lemma setIntegral_entropy_of_exp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Integrable X μ) (c : ℝ) (hc : 0 < c)
    (hE : Integrable (fun ω => Real.exp (c*X ω)) μ)
    (hbound : (∫ ω, Real.exp (c*X ω) ∂μ) ≤ 12) (V : Set Ω) :
    (∫ ω in V, X ω ∂μ) ≤ (12/c) * μ.real V * (1-Real.log (μ.real V)) := by
  let p := μ.real V
  by_cases hp : p = 0
  · change μ.real V = 0 at hp
    have hz : μ V = 0 := (measureReal_eq_zero_iff (by finiteness)).mp hp
    simp only [Measure.restrict_eq_zero.mpr hz,integral_zero_measure,hp,mul_zero,zero_mul,le_refl]
  · have hp0 : 0 < p := lt_of_le_of_ne measureReal_nonneg (Ne.symm hp)
    have hp1 : p ≤ 1 := measureReal_le_one
    have hlog : Real.log p ≤ 0 := Real.log_nonpos hp0.le hp1
    have hpoint (ω : Ω) : c*X ω ≤ p*Real.exp (c*X ω) - Real.log p := by
      have h := Real.add_one_le_exp (c*X ω + Real.log p)
      rw [Real.exp_add,Real.exp_log hp0] at h
      nlinarith
    have hi : (∫ ω in V, c*X ω ∂μ) ≤ ∫ ω in V, (p*Real.exp (c*X ω)-Real.log p) ∂μ :=
      integral_mono (hX.restrict.const_mul c)
      ((hE.restrict.const_mul p).sub (integrable_const (Real.log p))) hpoint
    rw [integral_const_mul,integral_sub (hE.restrict.const_mul p) (integrable_const _),
      integral_const_mul,integral_const,measureReal_restrict_apply_univ,smul_eq_mul] at hi
    have he : (∫ ω in V, Real.exp (c*X ω) ∂μ) ≤ 12 :=
      (setIntegral_le_integral hE (Filter.Eventually.of_forall (fun ω => Real.exp_nonneg _))).trans hbound
    have hcore : c * (∫ ω in V, X ω ∂μ) ≤ 12*p*(1-Real.log p) := by
      change c * (∫ ω in V, X ω ∂μ) ≤ _ at hi
      have hh := mul_le_mul_of_nonneg_left he hp0.le
      have hl := mul_nonpos_of_nonneg_of_nonpos hp0.le hlog
      dsimp [p] at hi ⊢
      dsimp [p] at hh hl
      nlinarith
    calc
      _ ≤ 12*p*(1-Real.log p)/c := (le_div_iff₀ hc).mpr (by simpa [mul_comm] using hcore)
      _ = _ := by dsimp [p]; ring

lemma posteriorSup_exponential_log {Ω ι : Type*} [m : MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m)
    (w : ι → ℕ → Ω → ℝ) (hw : ∀ e, Martingale (w e) ℱ μ)
    (hpos : ∀ e i ω, 0 ≤ w e i ω) (hsum : ∀ i ω, ∑ e, w e i ω ≤ 1) :
    (∫ ω, Real.exp (posteriorExponent / Real.log (Fintype.card ι+1) * posteriorSup w ω) ∂μ) ≤ 12 := by
  have hm : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ‹Nonempty ι›
  have hB : 0 < Real.log (Fintype.card ι+1) := Real.log_pos (by exact_mod_cast (show 1 < Fintype.card ι+1 by omega))
  let c := posteriorExponent / Real.log (Fintype.card ι+1)
  let c' := Real.log (3/2) / (2*((posteriorLevel (Fintype.card ι) : ℝ)+1)+1)
  have hle : c ≤ c' := posteriorExponent_le _ hm
  have hc : 0 ≤ c := (div_pos posteriorExponent_pos hB).le
  have hc' : 0 ≤ c' := hc.trans hle
  have hmeas := measurable_posteriorSup μ ℱ w hw
  have hb := fun ω => (posteriorSup_bounds w hpos hsum ω).2
  have hi := integral_mono (integrable_exp_of_bound μ _ hmeas _ c hb hc)
    (integrable_exp_of_bound μ _ hmeas _ c' hb hc') (show ∀ ω, Real.exp (c*posteriorSup w ω) ≤ Real.exp (c'*posteriorSup w ω) from by
      intro ω
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hle (posteriorSup_bounds w hpos hsum ω).1))
  exact hi.trans (posteriorSup_exponential μ ℱ w hw hpos hsum _ (posteriorLevel_dyadic _))

lemma posteriorSup_exponential_log_ae {Ω ι : Type*} [m : MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m)
    (w : ι → ℕ → Ω → ℝ) (hw : ∀ e, Martingale (w e) ℱ μ)
    (hpos : ∀ e i, ∀ᵐ ω ∂μ, 0 ≤ w e i ω) (hsum : ∀ i, ∀ᵐ ω ∂μ, ∑ e, w e i ω ≤ 1) :
    (∫ ω, Real.exp (posteriorExponent / Real.log (Fintype.card ι+1) * posteriorSup w ω) ∂μ) ≤ 12 := by
  have he := posteriorSup_congr_ae μ w (clippedPosterior w) (clippedPosterior_ae_eq μ w hpos hsum)
  have hi : (∫ ω, Real.exp (posteriorExponent / Real.log (Fintype.card ι+1) * posteriorSup w ω) ∂μ) =
      ∫ ω, Real.exp (posteriorExponent / Real.log (Fintype.card ι+1) * posteriorSup (clippedPosterior w) ω) ∂μ := by
    apply integral_congr_ae
    filter_upwards [he] with ω hω
    rw [hω]
  rw [hi]
  exact posteriorSup_exponential_log μ ℱ (clippedPosterior w)
    (clippedPosterior_martingale μ ℱ w hw hpos hsum)
    (clippedPosterior_bounds w).1 (clippedPosterior_bounds w).2

lemma integrable_posteriorSup_ae {Ω ι : Type*} [m : MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ℱ : Filtration ℕ m)
    (w : ι → ℕ → Ω → ℝ) (hw : ∀ e, Martingale (w e) ℱ μ)
    (hpos : ∀ e i, ∀ᵐ ω ∂μ, 0 ≤ w e i ω) (hsum : ∀ i, ∀ᵐ ω ∂μ, ∑ e, w e i ω ≤ 1) :
    Integrable (posteriorSup w) μ := by
  have he := posteriorSup_congr_ae μ w (clippedPosterior w) (clippedPosterior_ae_eq μ w hpos hsum)
  apply (integrable_const (Fintype.card ι : ℝ)).mono' (measurable_posteriorSup μ ℱ w hw).aestronglyMeasurable
  filter_upwards [he] with ω hω
  rw [hω,Real.norm_eq_abs,abs_of_nonneg (posteriorSup_bounds _ (clippedPosterior_bounds w).1 (clippedPosterior_bounds w).2 ω).1]
  exact (posteriorSup_bounds _ (clippedPosterior_bounds w).1 (clippedPosterior_bounds w).2 ω).2

lemma integrable_posteriorSup_exp_ae {Ω ι : Type*} [m : MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ℱ : Filtration ℕ m)
    (w : ι → ℕ → Ω → ℝ) (hw : ∀ e, Martingale (w e) ℱ μ)
    (hpos : ∀ e i, ∀ᵐ ω ∂μ, 0 ≤ w e i ω) (hsum : ∀ i, ∀ᵐ ω ∂μ, ∑ e, w e i ω ≤ 1)
    (c : ℝ) (hc : 0 ≤ c) : Integrable (fun ω => Real.exp (c * posteriorSup w ω)) μ := by
  have he := posteriorSup_congr_ae μ w (clippedPosterior w) (clippedPosterior_ae_eq μ w hpos hsum)
  have hm := measurable_posteriorSup μ ℱ w hw
  apply (integrable_const (Real.exp (c*Fintype.card ι))).mono' (hm.const_mul c).exp.aestronglyMeasurable
  filter_upwards [he] with ω hω
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),hω]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
    (posteriorSup_bounds _ (clippedPosterior_bounds w).1 (clippedPosterior_bounds w).2 ω).2 hc)

lemma posteriorSup_joint_event_weight {Ω Ξ ι : Type*} [m : MeasurableSpace Ω] [MeasurableSpace Ξ]
    [Fintype ι] [Nonempty ι] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Ξ) [IsProbabilityMeasure ν] (π : Ξ → Ω) (hπ : MeasurePreserving π ν μ)
    (ℱ : Filtration ℕ m) (w : ι → ℕ → Ω → ℝ) (hw : ∀ e, Martingale (w e) ℱ μ)
    (hpos : ∀ e i, ∀ᵐ ω ∂μ, 0 ≤ w e i ω) (hsum : ∀ i, ∀ᵐ ω ∂μ, ∑ e, w e i ω ≤ 1)
    (V : Set Ξ) :
    (∫ ξ in V, posteriorSup w (π ξ) ∂ν) ≤
      (12/posteriorExponent) * Real.log (Fintype.card ι+1) * ν.real V * (1-Real.log (ν.real V)) := by
  let c := posteriorExponent / Real.log (Fintype.card ι+1)
  have hm : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ‹Nonempty ι›
  have hB : 0 < Real.log (Fintype.card ι+1) := Real.log_pos (by exact_mod_cast (show 1 < Fintype.card ι+1 by omega))
  have hc : 0 < c := div_pos posteriorExponent_pos hB
  have hXe := integrable_posteriorSup_exp_ae μ ℱ w hw hpos hsum c hc.le
  have hXI := integrable_posteriorSup_ae μ ℱ w hw hpos hsum
  have hExp : (∫ ξ, Real.exp (c * posteriorSup w (π ξ)) ∂ν) ≤ 12 := by
    have hi : (∫ ξ, Real.exp (c * posteriorSup w (π ξ)) ∂ν) =
        ∫ ω, Real.exp (c * posteriorSup w ω) ∂μ := by
      rw [← hπ.map_eq]
      exact (integral_map_of_stronglyMeasurable hπ.measurable
        (((measurable_posteriorSup μ ℱ w hw).const_mul c).exp.stronglyMeasurable)).symm
    rw [hi]
    exact posteriorSup_exponential_log_ae μ ℱ w hw hpos hsum
  have hi := setIntegral_entropy_of_exp ν (fun ξ => posteriorSup w (π ξ))
    (hπ.integrable_comp_of_integrable hXI) c hc (hπ.integrable_comp_of_integrable hXe) hExp V
  have hscale : 12/c = (12/posteriorExponent) * Real.log (Fintype.card ι+1) := by
    dsimp [c]
    field_simp
  simpa only [hscale] using hi

lemma ae_atom_pos {α : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) : ∀ᵐ x ∂μ, μ {x} ≠ 0 := by
  simp only [ae_iff]
  have h : {x | ¬ μ {x} ≠ 0} = ⋃ x : {x // μ {x} = 0}, ({x.val} : Set α) := by
    ext x
    simp
  rw [h]
  exact measure_iUnion_null fun x => x.property

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

noncomputable def atomInfo {α : Type*} [MeasurableSpace α] (μ : Measure α) (x : α) : ℝ :=
  -Real.log (μ.real {x})

noncomputable def discreteEntropy {α : Type*} [MeasurableSpace α] (μ : Measure α) : ℝ :=
  ∫ x, atomInfo μ x ∂μ

lemma atomInfo_nonneg {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (x : α) : 0 ≤ atomInfo μ x := by
  exact neg_nonneg.mpr (Real.log_nonpos measureReal_nonneg measureReal_le_one)

lemma discreteEntropy_nonneg {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] : 0 ≤ discreteEntropy μ :=
  integral_nonneg (atomInfo_nonneg μ)

lemma ae_atom_real_pos {α : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) [IsFiniteMeasure μ] : ∀ᵐ x ∂μ, 0 < μ.real {x} := by
  filter_upwards [ae_atom_pos μ] with x hx
  exact ENNReal.toReal_pos hx (by finiteness)

lemma summable_integral_ratio {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsFiniteMeasure μ]
    (q : α → ℝ≥0∞) (_hq : (∑' x, q x) ≠ ∞) :
    (∫⁻ x, q x / μ {x} ∂μ) ≤ ∑' x, q x := by
  rw [lintegral_countable']
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : μ {x} = 0
  · simp [hx]
  · rw [ENNReal.div_mul_cancel hx (by finiteness)]

lemma integrable_atom_ratio {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsFiniteMeasure μ]
    (q : α → ℝ≥0∞) (hq : (∑' x, q x) ≠ ∞) :
    Integrable (fun x => (q x / μ {x}).toReal) μ := by
  apply integrable_toReal_of_lintegral_ne_top (measurable_of_countable _).aemeasurable
  exact ne_of_lt ((summable_integral_ratio μ q hq).trans_lt (lt_top_iff_ne_top.mpr hq))

lemma integral_atom_ratio_le {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsFiniteMeasure μ]
    (q : α → ℝ≥0∞) (hq : (∑' x, q x) ≠ ∞) :
    (∫ x, (q x / μ {x}).toReal ∂μ) ≤ (∑' x, q x).toReal := by
  rw [integral_toReal]
  · exact ENNReal.toReal_mono hq (summable_integral_ratio μ q hq)
  · exact (measurable_of_countable _).aemeasurable
  · filter_upwards [ae_atom_pos μ] with x hx
    exact lt_top_iff_ne_top.mpr (ENNReal.div_ne_top (ne_of_lt ((ENNReal.le_tsum x).trans_lt (lt_top_iff_ne_top.mpr hq))) hx)

lemma atomInfo_le_comparison {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsProbabilityMeasure μ]
    (q : α → ℝ≥0∞) (hq : ∀ x, q x ≠ 0 ∧ q x ≠ ∞) :
    ∀ᵐ x ∂μ, atomInfo μ x ≤ -Real.log (q x).toReal + (q x / μ {x}).toReal - 1 := by
  filter_upwards [ae_atom_real_pos μ] with x hx
  have hqx : 0 < (q x).toReal := ENNReal.toReal_pos (hq x).1 (hq x).2
  have hh := Real.log_le_sub_one_of_pos (div_pos hqx hx)
  rw [Real.log_div (ne_of_gt hqx) (ne_of_gt hx)] at hh
  simp only [atomInfo,ENNReal.toReal_div,measureReal_def] at *
  linarith

lemma integrable_atomInfo_of_comparison {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsProbabilityMeasure μ]
    (q : α → ℝ≥0∞) (hq0 : ∀ x, q x ≠ 0) (hq : (∑' x, q x) ≠ ∞)
    (hcost : Integrable (fun x => -Real.log (q x).toReal) μ) : Integrable (atomInfo μ) μ := by
  have hqx x : q x ≠ 0 ∧ q x ≠ ∞ := ⟨hq0 x,
    ne_of_lt ((ENNReal.le_tsum x).trans_lt (lt_top_iff_ne_top.mpr hq))⟩
  apply ((hcost.add (integrable_atom_ratio μ q hq)).sub (integrable_const 1)).mono'
    (measurable_of_countable _).aestronglyMeasurable
  filter_upwards [atomInfo_le_comparison μ q hqx] with x hx
  simpa only [Pi.sub_apply,Pi.add_apply,Real.norm_eq_abs,abs_of_nonneg (atomInfo_nonneg μ x)] using hx

lemma discreteEntropy_le_comparison {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsProbabilityMeasure μ]
    (q : α → ℝ≥0∞) (hq0 : ∀ x, q x ≠ 0) (hq : (∑' x, q x) ≠ ∞)
    (hcost : Integrable (fun x => -Real.log (q x).toReal) μ) :
    discreteEntropy μ ≤ (∫ x, -Real.log (q x).toReal ∂μ) + (∑' x, q x).toReal - 1 := by
  have hqx x : q x ≠ 0 ∧ q x ≠ ∞ := ⟨hq0 x,
    ne_of_lt ((ENNReal.le_tsum x).trans_lt (lt_top_iff_ne_top.mpr hq))⟩
  have hi := integral_mono_ae (integrable_atomInfo_of_comparison μ q hq0 hq hcost)
    ((hcost.add (integrable_atom_ratio μ q hq)).sub (integrable_const 1))
    (atomInfo_le_comparison μ q hqx)
  simp only [Pi.sub_apply,Pi.add_apply] at hi
  have hsum : Integrable (fun x => -Real.log (q x).toReal + (q x / μ {x}).toReal) μ :=
    hcost.add (integrable_atom_ratio μ q hq)
  rw [integral_sub hsum (integrable_const 1),
    integral_add hcost (integrable_atom_ratio μ q hq)] at hi
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at hi
  exact hi.trans (by linarith [integral_atom_ratio_le μ q hq])

lemma rnDeriv_atom {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν)
    (x : α) (hx : ν {x} ≠ 0) : μ.rnDeriv ν x = μ {x} / ν {x} := by
  have h := Measure.setLIntegral_rnDeriv hμν ({x} : Set α)
  rw [lintegral_singleton] at h
  exact (ENNReal.eq_div_iff hx (by finiteness)).mpr (by simpa only [mul_comm] using h)

lemma llr_atom {α : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν) :
    llr μ ν =ᵐ[μ] fun x => Real.log (μ.real {x}) - Real.log (ν.real {x}) := by
  filter_upwards [ae_atom_pos μ,hμν (ae_atom_pos ν)] with x hx hy
  rw [llr,rnDeriv_atom μ ν hμν x hy,ENNReal.toReal_div,Real.log_div]
  · rfl
  · exact (ENNReal.toReal_pos hx (by finiteness)).ne'
  · exact (ENNReal.toReal_pos hy (by finiteness)).ne'

lemma absolutelyContinuous_of_atoms {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ ν : Measure α)
    (h : ∀ x, ν {x} = 0 → μ {x} = 0) : μ ≪ ν := by
  intro s hs
  rw [← Set.biUnion_of_singleton s]
  exact (measure_biUnion_null_iff (Set.to_countable s)).mpr fun x hx => h x
    (measure_mono_null (Set.singleton_subset_iff.mpr hx) hs)

lemma atom_logRatio_nonneg {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hμν : μ ≪ ν)
    (hi : Integrable (fun x => Real.log (μ.real {x}) - Real.log (ν.real {x})) μ) :
    0 ≤ ∫ x, Real.log (μ.real {x}) - Real.log (ν.real {x}) ∂μ := by
  have hllr := llr_atom μ ν hμν
  have h := InformationTheory.integral_llr_add_sub_measure_univ_nonneg hμν
    (hi.congr hllr.symm)
  simpa only [integral_congr_ae hllr,probReal_univ,add_sub_cancel_right] using h

lemma atom_klDiv_formula {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hμν : μ ≪ ν)
    (hi : Integrable (fun x => Real.log (μ.real {x}) - Real.log (ν.real {x})) μ) :
    InformationTheory.klDiv μ ν = ENNReal.ofReal
      (∫ x, Real.log (μ.real {x}) - Real.log (ν.real {x}) ∂μ) := by
  have hllr := llr_atom μ ν hμν
  rw [InformationTheory.klDiv_of_ac_of_integrable hμν (hi.congr hllr.symm),
    integral_congr_ae hllr,probReal_univ,probReal_univ,add_sub_cancel_right]

noncomputable def conditionalInfo {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ρ : Measure (α × β)) (p : α × β) : ℝ :=
  -Real.log (ρ.real {p} / ρ.fst.real {p.1})

noncomputable def conditionalEntropy {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ρ : Measure (α × β)) : ℝ := ∫ p, conditionalInfo ρ p ∂ρ

lemma atom_le_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] (ρ : Measure (α × β)) (p : α × β) :
    ρ {p} ≤ ρ.fst {p.1} := by
  rw [Measure.fst_apply (measurableSet_singleton _)]
  exact measure_mono (by intro x hx; obtain rfl := Set.mem_singleton_iff.mp hx; rfl)

lemma conditionalInfo_nonneg {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] (ρ : Measure (α × β)) [IsFiniteMeasure ρ] (p : α × β) :
    0 ≤ conditionalInfo ρ p := by
  apply neg_nonneg.mpr
  apply Real.log_nonpos (div_nonneg measureReal_nonneg measureReal_nonneg)
  by_cases h : ρ.fst.real {p.1} = 0
  · simp [h]
  · apply (div_le_one (lt_of_le_of_ne measureReal_nonneg (Ne.symm h))).mpr
    exact ENNReal.toReal_mono (by finiteness) (atom_le_fst ρ p)

lemma conditionalInfo_log {α β : Type*} [Countable α] [Countable β]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (ρ : Measure (α × β)) [IsFiniteMeasure ρ] :
    conditionalInfo ρ =ᵐ[ρ] fun p => -Real.log (ρ.real {p}) + Real.log (ρ.fst.real {p.1}) := by
  filter_upwards [ae_atom_real_pos ρ] with p hp
  have hfst : 0 < ρ.fst.real {p.1} := hp.trans_le (ENNReal.toReal_mono (by finiteness) (atom_le_fst ρ p))
  dsimp [conditionalInfo]
  rw [Real.log_div hp.ne' hfst.ne']
  ring

lemma compProd_atom {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ] (p : α × β) :
    (μ ⊗ₘ κ) {p} = μ {p.1} * κ p.1 {p.2} := by
  have hset : ({p} : Set (α × β)) = {p.1} ×ˢ {p.2} := by ext x; simp [Prod.ext_iff]
  rw [hset,Measure.compProd_apply_prod (measurableSet_singleton _) (measurableSet_singleton _),
    lintegral_singleton,mul_comm]

lemma integrable_conditionalInfo {α β : Type*} [Countable α] [Countable β]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (ρ : Measure (α × β)) [IsProbabilityMeasure ρ] (κ : Kernel α β) [IsMarkovKernel κ]
    (hac : ρ ≪ ρ.fst ⊗ₘ κ)
    (hi : Integrable (fun p : α × β => atomInfo (κ p.1) p.2) ρ) :
    Integrable (conditionalInfo ρ) ρ := by
  let ν := ρ.fst ⊗ₘ κ
  have hsum : (∑' p, ν {p}) = 1 := by
    have hh := lintegral_countable' (μ := ν) (fun _ => (1 : ℝ≥0∞))
    simpa using hh.symm
  have hr := integrable_atom_ratio ρ (fun p => ν {p}) (by rw [hsum]; exact ENNReal.one_ne_top)
  apply ((hi.add hr).sub (integrable_const 1)).mono' (measurable_of_countable _).aestronglyMeasurable
  filter_upwards [ae_atom_real_pos ρ,hac (ae_atom_real_pos ν),conditionalInfo_log ρ] with p hp hν he
  have hfst : 0 < ρ.fst.real {p.1} := hp.trans_le (ENNReal.toReal_mono (by finiteness) (atom_le_fst ρ p))
  have hn : ν.real {p} = ρ.fst.real {p.1} * (κ p.1).real {p.2} := by
    simp only [ν,measureReal_def,compProd_atom,ENNReal.toReal_mul]
  have hk : 0 < (κ p.1).real {p.2} := (mul_pos_iff_of_pos_left hfst).mp (hn ▸ hν)
  have hh := Real.log_le_sub_one_of_pos (div_pos hν hp)
  rw [Real.log_div hν.ne' hp.ne',hn,Real.log_mul hfst.ne' hk.ne'] at hh
  rw [Real.norm_eq_abs,abs_of_nonneg (conditionalInfo_nonneg ρ p)]
  simp only [Pi.sub_apply,Pi.add_apply,he,atomInfo,ENNReal.toReal_div,← measureReal_def,hn]
  linarith

lemma conditionalEntropy_le_crossEntropy {α β : Type*} [Countable α] [Countable β]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (ρ : Measure (α × β)) [IsProbabilityMeasure ρ] (κ : Kernel α β) [IsMarkovKernel κ]
    (hac : ρ ≪ ρ.fst ⊗ₘ κ)
    (hi : Integrable (fun p : α × β => atomInfo (κ p.1) p.2) ρ) :
    conditionalEntropy ρ ≤ ∫ p, atomInfo (κ p.1) p.2 ∂ρ := by
  have hc := integrable_conditionalInfo ρ κ hac hi
  have he : (fun p : α × β => atomInfo (κ p.1) p.2 - conditionalInfo ρ p) =ᵐ[ρ]
      fun p => Real.log (ρ.real {p}) - Real.log ((ρ.fst ⊗ₘ κ).real {p}) := by
    filter_upwards [ae_atom_real_pos ρ,hac (ae_atom_real_pos (ρ.fst ⊗ₘ κ)),conditionalInfo_log ρ] with p hp hν he
    have hfst : 0 < ρ.fst.real {p.1} := hp.trans_le (ENNReal.toReal_mono (by finiteness) (atom_le_fst ρ p))
    have hn : (ρ.fst ⊗ₘ κ).real {p} = ρ.fst.real {p.1} * (κ p.1).real {p.2} := by
      simp only [measureReal_def,compProd_atom,ENNReal.toReal_mul]
    have hk : 0 < (κ p.1).real {p.2} := (mul_pos_iff_of_pos_left hfst).mp (hn ▸ hν)
    rw [hn,Real.log_mul hfst.ne' hk.ne',he]
    dsimp [atomInfo]
    ring
  have hh := atom_logRatio_nonneg ρ (ρ.fst ⊗ₘ κ) hac ((hi.sub hc).congr he)
  rw [← integral_congr_ae he,integral_sub hi hc] at hh
  exact sub_nonneg.mp hh

lemma joint_ac_marginal_product {α β : Type*} [Countable α] [Countable β]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (ρ : Measure (α × β)) [IsProbabilityMeasure ρ] : ρ ≪ ρ.fst.prod ρ.snd := by
  apply absolutelyContinuous_of_atoms
  intro p hp
  have he : (ρ.fst.prod ρ.snd) {p} = ρ.fst {p.1} * ρ.snd {p.2} := by
    rw [← Set.singleton_prod_singleton,Measure.prod_prod]
  rw [he,mul_eq_zero] at hp
  rcases hp with hp | hp
  · exact le_antisymm ((atom_le_fst ρ p).trans hp.le) bot_le
  · have hh : ρ {p} ≤ ρ.snd {p.2} := by
      rw [Measure.snd_apply (measurableSet_singleton _)]
      exact measure_mono (by intro x hx; obtain rfl := Set.mem_singleton_iff.mp hx; rfl)
    exact le_antisymm (hh.trans hp.le) bot_le

lemma conditionalEntropy_le_entropy_snd {α β : Type*} [Countable α] [Countable β]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (ρ : Measure (α × β)) [IsProbabilityMeasure ρ]
    (hi : Integrable (atomInfo ρ.snd) ρ.snd) : conditionalEntropy ρ ≤ discreteEntropy ρ.snd := by
  have hmap : MeasurePreserving Prod.snd ρ ρ.snd := ⟨measurable_snd,rfl⟩
  have hc : Integrable (fun p : α × β => atomInfo ρ.snd p.2) ρ := hmap.integrable_comp_of_integrable hi
  have hh := conditionalEntropy_le_crossEntropy ρ (Kernel.const α ρ.snd)
    (by simpa only [Measure.compProd_const] using joint_ac_marginal_product ρ) hc
  have he : (∫ p, atomInfo ρ.snd p.2 ∂ρ) = discreteEntropy ρ.snd := by
    dsimp [discreteEntropy,Measure.snd]
    rw [integral_map_of_stronglyMeasurable measurable_snd (measurable_of_countable _).stronglyMeasurable]
  exact hh.trans_eq he

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

noncomputable def informationOf {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (μ : Measure Ω) (X : Ω → α) (ω : Ω) : ℝ := atomInfo (μ.map X) (X ω)

noncomputable def entropyOf {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (μ : Measure Ω) (X : Ω → α) : ℝ := ∫ ω, informationOf μ X ω ∂μ

noncomputable def conditionedInformation {Ω α β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure Ω) (X : Ω → α) (Y : Ω → β) : Ω → ℝ :=
  fun ω => informationOf μ (fun ξ => (Y ξ,X ξ)) ω - informationOf μ Y ω

noncomputable def conditionedEntropy {Ω α β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure Ω) (X : Ω → α) (Y : Ω → β) : ℝ :=
  ∫ ω, conditionedInformation μ X Y ω ∂μ

section DiscreteEntropyVariables
variable {Ω α β γ : Type*} [Countable Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Countable β] [MeasurableSpace β] [MeasurableSingletonClass β]
  [Countable γ] [MeasurableSpace γ] [MeasurableSingletonClass γ]

omit [Countable α] in
lemma informationOf_fiber (μ : Measure Ω) (X : Ω → α) (ω : Ω) :
    informationOf μ X ω = -Real.log (μ.real {ξ | X ξ = X ω}) := by
  simp only [informationOf,atomInfo,measureReal_def,
    Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  rfl

omit [Countable α] [Countable β] in
lemma informationOf_pair_comm (μ : Measure Ω) (X : Ω → α) (Y : Ω → β) :
    informationOf μ (fun ω => (X ω,Y ω)) = informationOf μ (fun ω => (Y ω,X ω)) := by
  funext ω
  rw [informationOf_fiber,informationOf_fiber]
  congr 3
  ext ξ
  simp [and_comm]

omit [Countable α] [Countable β] [Countable γ] in
lemma informationOf_pair_assoc (μ : Measure Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    informationOf μ (fun ω => ((X ω,Y ω),Z ω)) = informationOf μ (fun ω => (X ω,Y ω,Z ω)) := by
  funext ω
  rw [informationOf_fiber,informationOf_fiber]
  congr 3
  ext ξ
  simp [and_assoc]

omit [Countable α] [Countable β] in
lemma informationOf_function (μ : Measure Ω) (X : Ω → α) (f : α → β) (hf : Function.Injective f) :
    informationOf μ (f ∘ X) = informationOf μ X := by
  funext ω
  rw [informationOf_fiber,informationOf_fiber]
  congr 3
  ext ξ
  simp [hf.eq_iff]

lemma entropyOf_eq_discreteEntropy (μ : Measure Ω) (X : Ω → α) :
    entropyOf μ X = discreteEntropy (μ.map X) := by
  dsimp [entropyOf,discreteEntropy,informationOf]
  rw [integral_map_of_stronglyMeasurable (measurable_of_countable _) (measurable_of_countable _).stronglyMeasurable]

lemma integrable_informationOf_iff (μ : Measure Ω) (X : Ω → α) :
    Integrable (informationOf μ X) μ ↔ Integrable (atomInfo (μ.map X)) (μ.map X) := by
  exact (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
    (measurable_of_countable _).aemeasurable).symm

lemma conditionedInformation_eq (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → α) (Y : Ω → β) :
    conditionedInformation μ X Y =ᵐ[μ] fun ω => conditionalInfo (μ.map (fun ξ => (Y ξ,X ξ))) (Y ω,X ω) := by
  let F := fun ξ => (Y ξ,X ξ)
  have hmap : MeasurePreserving F μ (μ.map F) := ⟨measurable_of_countable _,rfl⟩
  have hmarg : (μ.map F).fst = μ.map Y := by
    simp only [Measure.fst,Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
    rfl
  filter_upwards [hmap.quasiMeasurePreserving.ae (conditionalInfo_log (μ.map F))] with ω hω
  rw [hω,hmarg]
  simp only [conditionedInformation,informationOf,atomInfo,F]
  ring

lemma conditionedInformation_nonneg (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → α) (Y : Ω → β) :
    ∀ᵐ ω ∂μ, 0 ≤ conditionedInformation μ X Y ω := by
  filter_upwards [conditionedInformation_eq μ X Y] with ω hω
  rw [hω]
  exact conditionalInfo_nonneg _ _

lemma integrable_conditionedInformation (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (Y : Ω → β) (hi : Integrable (informationOf μ X) μ) :
    Integrable (conditionedInformation μ X Y) μ := by
  let F := fun ξ => (Y ξ,X ξ)
  let ρ := μ.map F
  have : IsProbabilityMeasure ρ := probabilityMeasure_map (measurable_of_countable _).aemeasurable
  have hsnd : ρ.snd = μ.map X := by
    dsimp [ρ,Measure.snd]
    rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
    rfl
  have hmap : MeasurePreserving Prod.snd ρ ρ.snd := ⟨measurable_snd,rfl⟩
  have hi' : Integrable (atomInfo ρ.snd) ρ.snd := by
    rw [hsnd]
    exact (integrable_informationOf_iff μ X).mp hi
  have hc : Integrable (conditionalInfo ρ) ρ := integrable_conditionalInfo ρ (Kernel.const β ρ.snd)
    (by simpa only [Measure.compProd_const] using joint_ac_marginal_product ρ)
    (hmap.integrable_comp_of_integrable hi')
  have hF : MeasurePreserving F μ ρ := ⟨measurable_of_countable _,rfl⟩
  exact (hF.integrable_comp_of_integrable hc).congr (conditionedInformation_eq μ X Y).symm

lemma conditionedEntropy_le_entropyOf (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (Y : Ω → β) (hi : Integrable (informationOf μ X) μ) :
    conditionedEntropy μ X Y ≤ entropyOf μ X := by
  let F := fun ξ => (Y ξ,X ξ)
  let ρ := μ.map F
  have : IsProbabilityMeasure ρ := probabilityMeasure_map (measurable_of_countable _).aemeasurable
  have hsnd : ρ.snd = μ.map X := by
    dsimp [ρ,Measure.snd]
    rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
    rfl
  have he : conditionedEntropy μ X Y = conditionalEntropy ρ := by
    dsimp [conditionedEntropy,conditionalEntropy,ρ]
    rw [integral_congr_ae (conditionedInformation_eq μ X Y),
      integral_map_of_stronglyMeasurable (measurable_of_countable _) (measurable_of_countable _).stronglyMeasurable]
  rw [he,entropyOf_eq_discreteEntropy,← hsnd]
  apply conditionalEntropy_le_entropy_snd
  rw [hsnd]
  exact (integrable_informationOf_iff μ X).mp hi

omit [Countable α] [Countable β] [Countable γ] in
lemma conditionedInformation_chain (μ : Measure Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    conditionedInformation μ (fun ω => (X ω,Y ω)) Z =
      fun ω => conditionedInformation μ X Z ω + conditionedInformation μ Y (fun ξ => (Z ξ,X ξ)) ω := by
  funext ω
  simp only [conditionedInformation,informationOf_pair_assoc]
  ring

omit [Countable α] [Countable β] [Countable γ] in
lemma conditionedEntropy_chain (μ : Measure Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ)
    (hX : Integrable (conditionedInformation μ X Z) μ)
    (hY : Integrable (conditionedInformation μ Y (fun ξ => (Z ξ,X ξ))) μ) :
    conditionedEntropy μ (fun ω => (X ω,Y ω)) Z =
      conditionedEntropy μ X Z + conditionedEntropy μ Y (fun ξ => (Z ξ,X ξ)) := by
  simp only [conditionedEntropy,conditionedInformation_chain]
  exact integral_add hX hY

omit [Countable Ω] [MeasurableSingletonClass Ω] [Countable α] [MeasurableSingletonClass α]
  [Countable β] [MeasurableSingletonClass β] in
lemma informationOf_pair_chain (μ : Measure Ω) (X : Ω → α) (Y : Ω → β) :
    informationOf μ (fun ω => (X ω,Y ω)) = fun ω => informationOf μ X ω + conditionedInformation μ Y X ω := by
  funext ω
  simp only [conditionedInformation]
  ring

lemma integrable_informationOf_pair (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (Y : Ω → β) (hX : Integrable (informationOf μ X) μ)
    (hY : Integrable (informationOf μ Y) μ) :
    Integrable (informationOf μ (fun ω => (X ω,Y ω))) μ := by
  rw [informationOf_pair_chain]
  exact hX.add (integrable_conditionedInformation μ Y X hY)

omit [Countable Ω] [MeasurableSingletonClass Ω] [Countable α] [MeasurableSingletonClass α]
  [Countable β] [MeasurableSingletonClass β] in
lemma entropyOf_pair_chain (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (Y : Ω → β) (hX : Integrable (informationOf μ X) μ)
    (hY : Integrable (conditionedInformation μ Y X) μ) :
    entropyOf μ (fun ω => (X ω,Y ω)) = entropyOf μ X + conditionedEntropy μ Y X := by
  dsimp [entropyOf,conditionedEntropy]
  rw [informationOf_pair_chain,integral_add hX hY]

end DiscreteEntropyVariables

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

lemma atom_le_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] (μ : Measure α) (f : α → β) (hf : Measurable f) (x : α) :
    μ {x} ≤ μ.map f {f x} := by
  rw [Measure.map_apply hf (measurableSet_singleton _)]
  exact measure_mono (by intro y hy; obtain rfl := Set.mem_singleton_iff.mp hy; rfl)

lemma conditionalInfo_eq_kernel {α β : Type*} [Countable α] [Countable β] [Nonempty β]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (ρ : Measure (α × β)) [IsFiniteMeasure ρ] (p : α × β) (hp : ρ.fst {p.1} ≠ 0) :
    atomInfo (ρ.condKernel p.1) p.2 = conditionalInfo ρ p := by
  dsimp [atomInfo,conditionalInfo,measureReal_def]
  rw [Measure.condKernel_apply_of_ne_zero hp,Set.singleton_prod_singleton,ENNReal.toReal_mul,
    ENNReal.toReal_inv]
  congr 1
  ring_nf

lemma ac_conditioning_projection {α β γ : Type*} [Countable α] [Countable β] [Countable γ]
    [Nonempty γ] [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
    (ρ : Measure (α × γ)) [IsProbabilityMeasure ρ] (f : α → β) :
    ρ ≪ ρ.fst ⊗ₘ (ρ.map (fun p => (f p.1,p.2))).condKernel.comap f (measurable_of_countable _) := by
  let ν := ρ.map (fun p => (f p.1,p.2))
  apply absolutelyContinuous_of_atoms
  intro p hp
  by_contra hn
  have hfst : ρ.fst {p.1} ≠ 0 := ne_of_gt ((pos_iff_ne_zero.mpr hn).trans_le (atom_le_fst ρ p))
  have hold : ν {(f p.1,p.2)} ≠ 0 := ne_of_gt ((pos_iff_ne_zero.mpr hn).trans_le
    (atom_le_map ρ (fun p => (f p.1,p.2)) (measurable_of_countable _) p))
  have hmarg : ν.fst {f p.1} ≠ 0 := ne_of_gt ((pos_iff_ne_zero.mpr hold).trans_le (atom_le_fst ν (f p.1,p.2)))
  rw [compProd_atom,Kernel.comap_apply] at hp
  have hk : ν.condKernel (f p.1) {p.2} ≠ 0 := by
    rw [Measure.condKernel_apply_of_ne_zero hmarg,Set.singleton_prod_singleton]
    exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (by finiteness)) hold
  exact (mul_ne_zero hfst hk) hp

lemma conditionedEntropy_monotone_projection {α β γ : Type*} [Countable α] [Countable β]
    [Countable γ] [Nonempty γ] [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
    (ρ : Measure (α × γ)) [IsProbabilityMeasure ρ] (f : α → β)
    (hi : Integrable (conditionalInfo (ρ.map (fun p => (f p.1,p.2)))) (ρ.map (fun p => (f p.1,p.2)))) :
    conditionalEntropy ρ ≤ conditionalEntropy (ρ.map (fun p => (f p.1,p.2))) := by
  let F := fun p : α × γ => (f p.1,p.2)
  let ν := ρ.map F
  let κ := ν.condKernel.comap f (measurable_of_countable _)
  have hF : MeasurePreserving F ρ ν := ⟨measurable_of_countable _,rfl⟩
  have he : (fun p : α × γ => atomInfo (κ p.1) p.2) =ᵐ[ρ] fun p => conditionalInfo ν (F p) := by
    filter_upwards [hF.quasiMeasurePreserving.ae (ae_atom_pos ν)] with p hp
    have hm : ν.fst {(F p).1} ≠ 0 := ne_of_gt ((pos_iff_ne_zero.mpr hp).trans_le (atom_le_fst ν (F p)))
    exact conditionalInfo_eq_kernel ν (F p) hm
  have hc := (hF.integrable_comp_of_integrable hi).congr he.symm
  have hh := conditionalEntropy_le_crossEntropy ρ κ (ac_conditioning_projection ρ f) hc
  rw [integral_congr_ae he] at hh
  have hi' : (∫ p, conditionalInfo ν (F p) ∂ρ) = conditionalEntropy ν := by
    dsimp [conditionalEntropy,ν]
    rw [integral_map_of_stronglyMeasurable (measurable_of_countable _) (measurable_of_countable _).stronglyMeasurable]
  exact hh.trans_eq hi'

lemma conditionedEntropy_eq_conditionalEntropy {Ω α β : Type*} [Countable Ω] [Countable α]
    [Countable β] [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass Ω] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → α) (Y : Ω → β) :
    conditionedEntropy μ X Y = conditionalEntropy (μ.map (fun ω => (Y ω,X ω))) := by
  dsimp [conditionedEntropy,conditionalEntropy]
  rw [integral_congr_ae (conditionedInformation_eq μ X Y),
    integral_map_of_stronglyMeasurable (measurable_of_countable _) (measurable_of_countable _).stronglyMeasurable]

lemma conditionedEntropy_le_conditionedEntropy {Ω α β γ : Type*} [Countable Ω] [Countable α]
    [Countable β] [Countable γ] [Nonempty α] [MeasurableSpace Ω] [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSingletonClass Ω]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → α) (Y : Ω → β) (Z : Ω → γ)
    (hi : Integrable (informationOf μ X) μ) :
    conditionedEntropy μ X (fun ω => (Y ω,Z ω)) ≤ conditionedEntropy μ X Y := by
  rw [conditionedEntropy_eq_conditionalEntropy,conditionedEntropy_eq_conditionalEntropy]
  let ρ := μ.map (fun ω => ((Y ω,Z ω),X ω))
  have : IsProbabilityMeasure ρ := probabilityMeasure_map (measurable_of_countable _).aemeasurable
  have he : ρ.map (fun p => (p.1.1,p.2)) = μ.map (fun ω => (Y ω,X ω)) := by
    dsimp [ρ]
    rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
    rfl
  have hI : Integrable (conditionalInfo (μ.map (fun ω => (Y ω,X ω)))) (μ.map (fun ω => (Y ω,X ω))) := by
    rw [integrable_map_measure (measurable_of_countable _).aestronglyMeasurable (measurable_of_countable _).aemeasurable]
    exact (integrable_conditionedInformation μ X Y hi).congr (conditionedInformation_eq μ X Y)
  have hh := conditionedEntropy_monotone_projection ρ Prod.fst (by rw [he]; exact hI)
  simpa only [he] using hh

section EntropyTransforms
variable {Ω α β γ : Type*} [Countable Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Countable β] [MeasurableSpace β] [MeasurableSingletonClass β]
  [Countable γ] [MeasurableSpace γ] [MeasurableSingletonClass γ]

omit [Countable α] [MeasurableSingletonClass α] in
lemma informationOf_nonneg (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → α) (ω : Ω) :
    0 ≤ informationOf μ X ω := by
  have : IsProbabilityMeasure (μ.map X) := probabilityMeasure_map (measurable_of_countable _).aemeasurable
  exact atomInfo_nonneg _ _

omit [Countable β] in
lemma informationOf_comp_le (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → α) (f : α → β) :
    ∀ᵐ ω ∂μ, informationOf μ (f ∘ X) ω ≤ informationOf μ X ω := by
  have : IsProbabilityMeasure (μ.map X) := probabilityMeasure_map (measurable_of_countable _).aemeasurable
  have hX : MeasurePreserving X μ (μ.map X) := ⟨measurable_of_countable _,rfl⟩
  filter_upwards [hX.quasiMeasurePreserving.ae (ae_atom_real_pos (μ.map X))] with ω hω
  have hm := atom_le_map (μ.map X) f (measurable_of_countable _) (X ω)
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)] at hm
  have hm' : (μ.map X).real {X ω} ≤ (μ.map (f ∘ X)).real {(f ∘ X) ω} :=
    ENNReal.toReal_mono (by finiteness) hm
  dsimp [informationOf,atomInfo]
  exact neg_le_neg (Real.log_le_log hω hm')

omit [Countable β] in
lemma integrable_informationOf_comp (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (f : α → β) (hi : Integrable (informationOf μ X) μ) :
    Integrable (informationOf μ (f ∘ X)) μ := by
  apply hi.mono' (measurable_of_countable _).aestronglyMeasurable
  filter_upwards [informationOf_comp_le μ X f] with ω hω
  simpa only [Real.norm_eq_abs,abs_of_nonneg (informationOf_nonneg μ (f ∘ X) ω)] using hω

omit [Countable β] in
lemma entropyOf_comp_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (f : α → β) (hi : Integrable (informationOf μ X) μ) :
    entropyOf μ (f ∘ X) ≤ entropyOf μ X := by
  exact integral_mono_ae (integrable_informationOf_comp μ X f hi) hi (informationOf_comp_le μ X f)

omit [Countable α] [Countable β] [Countable γ] in
lemma conditionedInformation_fiberwise_injective (μ : Measure Ω) (X : Ω → α) (Y : Ω → β)
    (f : β → α → γ) (hf : ∀ y, Function.Injective (f y)) :
    conditionedInformation μ (fun ω => f (Y ω) (X ω)) Y = conditionedInformation μ X Y := by
  have he : informationOf μ (fun ω => (Y ω,f (Y ω) (X ω))) =
      informationOf μ (fun ω => (Y ω,X ω)) := by
    funext ω
    rw [informationOf_fiber,informationOf_fiber]
    congr 3
    ext ξ
    simp only [Set.mem_ofPred_eq,Prod.mk.injEq]
    constructor
    · rintro ⟨hy,hf'⟩
      exact ⟨hy,hf (Y ω) (by simpa only [hy] using hf')⟩
    · rintro ⟨hy,hx⟩
      simp [hy,hx]
  funext ω
  change informationOf μ (fun ξ => (Y ξ,f (Y ξ) (X ξ))) ω - informationOf μ Y ω =
    informationOf μ (fun ξ => (Y ξ,X ξ)) ω - informationOf μ Y ω
  rw [he]

lemma informationOf_pair_indep (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (Y : Ω → β) (hXY : X ⟂ᵢ[μ] Y) :
    informationOf μ (fun ω => (X ω,Y ω)) =ᵐ[μ] fun ω => informationOf μ X ω + informationOf μ Y ω := by
  have hX : MeasurePreserving X μ (μ.map X) := ⟨measurable_of_countable _,rfl⟩
  have hY : MeasurePreserving Y μ (μ.map Y) := ⟨measurable_of_countable _,rfl⟩
  filter_upwards [hX.quasiMeasurePreserving.ae (ae_atom_real_pos (μ.map X)),
    hY.quasiMeasurePreserving.ae (ae_atom_real_pos (μ.map Y))] with ω hx hy
  simp only [informationOf,atomInfo]
  rw [hXY.map_prod_eq_prod_map_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aemeasurable,measureReal_def,← Set.singleton_prod_singleton,
    Measure.prod_prod,ENNReal.toReal_mul,← measureReal_def,← measureReal_def,
    Real.log_mul hx.ne' hy.ne']
  ring

lemma conditionedInformation_indep (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (Y : Ω → β) (hXY : X ⟂ᵢ[μ] Y) :
    conditionedInformation μ X Y =ᵐ[μ] informationOf μ X := by
  filter_upwards [informationOf_pair_indep μ Y X hXY.symm] with ω hω
  simp only [conditionedInformation,hω,add_sub_cancel_left]

lemma conditionedEntropy_indep (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (Y : Ω → β) (hXY : X ⟂ᵢ[μ] Y) :
    conditionedEntropy μ X Y = entropyOf μ X := integral_congr_ae (conditionedInformation_indep μ X Y hXY)

lemma conditionedInformation_indep_pair (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) (hXYZ : (fun ω => (Y ω,X ω)) ⟂ᵢ[μ] Z) :
    conditionedInformation μ X (fun ω => (Y ω,Z ω)) =ᵐ[μ] conditionedInformation μ X Y := by
  have hYZ : Y ⟂ᵢ[μ] Z := by
    simpa only [Function.comp_def,id_eq] using hXYZ.comp measurable_fst measurable_id
  filter_upwards [informationOf_pair_indep μ (fun ω => (Y ω,X ω)) Z hXYZ,
    informationOf_pair_indep μ Y Z hYZ] with ω hω hω'
  have hswap : informationOf μ (fun ω => ((Y ω,Z ω),X ω)) =
      informationOf μ (fun ω => ((Y ω,X ω),Z ω)) := by
    funext ξ
    rw [informationOf_fiber,informationOf_fiber]
    congr 3
    ext ζ
    simp [and_assoc,and_comm]
  simp only [conditionedInformation,hswap,hω,hω']
  ring

lemma conditionedEntropy_indep_pair (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) (hXYZ : (fun ω => (Y ω,X ω)) ⟂ᵢ[μ] Z) :
    conditionedEntropy μ X (fun ω => (Y ω,Z ω)) = conditionedEntropy μ X Y :=
  integral_congr_ae (conditionedInformation_indep_pair μ X Y Z hXYZ)

end EntropyTransforms

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

lemma geometric_comparison_sum (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    (∑' n : ℕ, ENNReal.ofReal ((1-r)*r^n)) = 1 := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (sub_nonneg.mpr hr1.le) (pow_nonneg hr0.le n))
    ((summable_geometric_of_lt_one hr0.le hr1).mul_left (1-r)),tsum_mul_left,
    tsum_geometric_of_lt_one hr0.le hr1]
  simp [ne_of_gt (sub_pos.mpr hr1)]

lemma geometric_comparison_cost (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (n : ℕ) :
    -Real.log (ENNReal.ofReal ((1-r)*r^n)).toReal = -Real.log (1-r) - n*Real.log r := by
  rw [ENNReal.toReal_ofReal (by positivity),Real.log_mul (by linarith) (pow_ne_zero _ hr0.ne'),Real.log_pow]
  ring

lemma entropy_nat_moment (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hi : Integrable (fun k : ℕ => (k : ℝ)) μ) (a : ℝ) (ha : 0 < a)
    (hmean : (∫ k : ℕ, (k : ℝ) ∂μ) ≤ a) :
    Integrable (atomInfo μ) μ ∧ discreteEntropy μ ≤ 1 + Real.log (a+1) := by
  let r := a/(a+1)
  have ha1 : 0 < a+1 := by linarith
  have hr0 : 0 < r := div_pos ha ha1
  have hr1 : r < 1 := (div_lt_one ha1).mpr (by linarith)
  let q := fun n : ℕ => ENNReal.ofReal ((1-r)*r^n)
  have hq : (∑' n, q n) = 1 := geometric_comparison_sum r hr0 hr1
  have hq0 : ∀ n, q n ≠ 0 := by intro n; exact ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
  have hcost : Integrable (fun n => -Real.log (q n).toReal) μ := by
    simp only [q,geometric_comparison_cost r hr0 hr1]
    exact (integrable_const _).sub (hi.mul_const _)
  refine ⟨integrable_atomInfo_of_comparison μ q hq0 (by rw [hq]; simp) hcost, ?_⟩
  have hb := discreteEntropy_le_comparison μ q hq0 (by rw [hq]; simp) hcost
  rw [hq,ENNReal.toReal_one,add_sub_cancel_right] at hb
  simp only [q,geometric_comparison_cost r hr0 hr1] at hb
  rw [integral_sub (integrable_const _) (hi.mul_const _),integral_const,probReal_univ,
    smul_eq_mul,one_mul,integral_mul_const] at hb
  have he : 1-r = (a+1)⁻¹ := by dsimp [r]; field_simp; ring
  have hl : -Real.log r = Real.log (1+1/a) := by
    rw [← Real.log_inv]
    congr 1
    dsimp [r]
    field_simp
  have hlog : 0 ≤ Real.log (1+1/a) := Real.log_nonneg (by
    have hh : 0 ≤ 1/a := by positivity
    linarith)
  have hlog' : Real.log (1+1/a) ≤ 1/a := by
    have hh := Real.log_le_sub_one_of_pos (show 0 < 1+1/a by positivity)
    linarith
  rw [he,Real.log_inv] at hb
  have hh : (∫ k : ℕ, (k : ℝ) ∂μ) * Real.log (1+1/a) ≤ 1 := by
    calc
      _ ≤ a * Real.log (1+1/a) := mul_le_mul_of_nonneg_right hmean hlog
      _ ≤ a * (1/a) := mul_le_mul_of_nonneg_left hlog' ha.le
      _ = 1 := by field_simp
  have heq : -(∫ k : ℕ, (k : ℝ) ∂μ) * Real.log r =
      (∫ k : ℕ, (k : ℝ) ∂μ) * Real.log (1+1/a) := by rw [← hl]; ring
  linarith

lemma entropy_finite (α : Type*) [Fintype α] [Nonempty α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsProbabilityMeasure μ] :
    Integrable (atomInfo μ) μ ∧ discreteEntropy μ ≤ Real.log (Fintype.card α) := by
  let q := fun _ : α => (Fintype.card α : ℝ≥0∞)⁻¹
  have hc : Fintype.card α ≠ 0 := (Fintype.card_pos).ne'
  have hq : (∑' x, q x) = 1 := by
    simp only [q,tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by exact_mod_cast hc) (by finiteness)
  have hq0 : ∀ x, q x ≠ 0 := by intro x; simp [q]
  have hcost : (fun x => -Real.log (q x).toReal) = fun _ => Real.log (Fintype.card α) := by
    funext x
    simp [q,ENNReal.toReal_inv,Real.log_inv]
  refine ⟨integrable_atomInfo_of_comparison μ q hq0 (by rw [hq]; simp)
    (by rw [hcost]; exact integrable_const _), ?_⟩
  have hh := discreteEntropy_le_comparison μ q hq0 (by rw [hq]; simp)
    (by rw [hcost]; exact integrable_const _)
  simpa only [hcost,hq,integral_const,probReal_univ,smul_eq_mul,one_mul,ENNReal.toReal_one,
    add_sub_cancel_right] using hh

lemma entropyOf_pair_le {Ω α β : Type*} [Countable Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [Countable β] [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → α) (Y : Ω → β)
    (hX : Integrable (informationOf μ X) μ) (hY : Integrable (informationOf μ Y) μ) :
    entropyOf μ (fun ω => (X ω,Y ω)) ≤ entropyOf μ X + entropyOf μ Y := by
  rw [entropyOf_pair_chain μ X Y hX (integrable_conditionedInformation μ Y X hY)]
  exact add_le_add le_rfl (conditionedEntropy_le_entropyOf μ Y X hY)

lemma entropyOf_nat_moment {Ω : Type*} [Countable Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℕ)
    (hi : Integrable (fun ω => (X ω : ℝ)) μ) (a : ℝ) (ha : 0 < a)
    (hmean : (∫ ω, (X ω : ℝ) ∂μ) ≤ a) :
    Integrable (informationOf μ X) μ ∧ entropyOf μ X ≤ 1+Real.log (a+1) := by
  have : IsProbabilityMeasure (μ.map X) := probabilityMeasure_map (measurable_of_countable _).aemeasurable
  have hi' : Integrable (fun n : ℕ => (n : ℝ)) (μ.map X) :=
    (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
      (measurable_of_countable _).aemeasurable).mpr hi
  have hmean' : (∫ n : ℕ, (n : ℝ) ∂μ.map X) ≤ a := by
    rwa [integral_map_of_stronglyMeasurable (measurable_of_countable _) (measurable_of_countable _).stronglyMeasurable]
  have hh := entropy_nat_moment (μ.map X) hi' a ha hmean'
  exact ⟨(integrable_informationOf_iff μ X).mpr hh.1, (entropyOf_eq_discreteEntropy μ X) ▸ hh.2⟩

lemma entropyOf_finite {Ω α : Type*} [Countable Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → α) :
    Integrable (informationOf μ X) μ ∧ entropyOf μ X ≤ Real.log (Fintype.card α) := by
  have : IsProbabilityMeasure (μ.map X) := probabilityMeasure_map (measurable_of_countable _).aemeasurable
  have hh := entropy_finite α (μ.map X)
  exact ⟨(integrable_informationOf_iff μ X).mpr hh.1, (entropyOf_eq_discreteEntropy μ X) ▸ hh.2⟩

lemma entropyOf_int_moment {Ω : Type*} [Countable Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℤ)
    (hi : Integrable (fun ω => |(X ω : ℝ)|) μ) (a : ℝ) (ha : 0 < a)
    (hmean : (∫ ω, |(X ω : ℝ)| ∂μ) ≤ a) :
    Integrable (informationOf μ X) μ ∧ entropyOf μ X ≤ 1+Real.log 2+Real.log (a+1) := by
  let f : ℤ → ℕ × Bool := fun z => (z.natAbs,decide (z < 0))
  have hf : Function.Injective f := by
    intro x y h
    have h0 := (Prod.mk.inj h).1
    have h1 := (Prod.mk.inj h).2
    have hs : (x < 0) ↔ (y < 0) := by simpa using h1
    rcases Int.natAbs_eq_natAbs_iff.mp h0 with h0 | h0
    · exact h0
    · omega
  have habs : (fun ω => ((X ω).natAbs : ℝ)) = fun ω => |(X ω : ℝ)| := by
    funext ω
    simp
  have hN := entropyOf_nat_moment μ (fun ω => (X ω).natAbs) (habs ▸ hi) a ha (habs ▸ hmean)
  have hB := entropyOf_finite μ (fun ω => decide (X ω < 0))
  have he := informationOf_function μ X f hf
  have he' : entropyOf μ (f ∘ X) = entropyOf μ X := by simp only [entropyOf,he]
  refine ⟨?_, ?_⟩
  · rw [← he]
    exact integrable_informationOf_pair μ _ _ hN.1 hB.1
  · have hh := entropyOf_pair_le μ _ _ hN.1 hB.1
    change entropyOf μ (f ∘ X) ≤ _ at hh
    rw [he'] at hh
    have hb : entropyOf μ (fun ω => decide (X ω < 0)) ≤ Real.log 2 := by simpa using hB.2
    linarith [hN.2]

lemma entropyOf_lattice_moment {Ω : Type*} [Countable Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (q : ℕ) (X : Ω → Fin q → ℤ)
    (hi : ∀ i, Integrable (fun ω => |(X ω i : ℝ)|) μ) (a : ℝ) (ha : 0 < a)
    (hmean : ∀ i, (∫ ω, |(X ω i : ℝ)| ∂μ) ≤ a) :
    Integrable (informationOf μ X) μ ∧ entropyOf μ X ≤ q*(1+Real.log 2+Real.log (a+1)) := by
  induction q with
  | zero =>
    have he : informationOf μ X = 0 := by
      funext ω
      rw [informationOf_fiber]
      have hset : {ξ | X ξ = X ω} = Set.univ := by
        ext ξ
        simp only [Set.mem_ofPred_eq,Set.mem_univ,iff_true]
        funext i
        exact Fin.elim0 i
      simp [hset]
    constructor
    · rw [he]
      exact integrable_zero _ _ _
    · simp [entropyOf,he]
  | succ q ih =>
    let f : (Fin (q+1) → ℤ) → ℤ × (Fin q → ℤ) := fun v => (v 0,fun i => v i.succ)
    have hf : Function.Injective f := by
      intro v w h
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact (Prod.mk.inj h).1
      · exact congrFun (Prod.mk.inj h).2 j
    have hh := entropyOf_int_moment μ (fun ω => X ω 0) (hi 0) a ha (hmean 0)
    have ht := ih (fun ω i => X ω i.succ) (fun i => hi i.succ) (fun i => hmean i.succ)
    have he := informationOf_function μ X f hf
    have he' : entropyOf μ (f ∘ X) = entropyOf μ X := by simp only [entropyOf,he]
    refine ⟨?_, ?_⟩
    · rw [← he]
      exact integrable_informationOf_pair μ _ _ hh.1 ht.1
    · have hb := entropyOf_pair_le μ _ _ hh.1 ht.1
      change entropyOf μ (f ∘ X) ≤ _ at hb
      rw [he'] at hb
      push_cast
      nlinarith [hh.2,ht.2]

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

lemma llr_conditional_reference {α β : Type*} [Countable α] [Countable β]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (ρ : Measure (α × β)) [IsProbabilityMeasure ρ] (κ : Kernel α β) [IsMarkovKernel κ]
    (hac : ρ ≪ ρ.fst ⊗ₘ κ) :
    llr ρ (ρ.fst ⊗ₘ κ) =ᵐ[ρ] fun p => atomInfo (κ p.1) p.2 - conditionalInfo ρ p := by
  filter_upwards [llr_atom ρ (ρ.fst ⊗ₘ κ) hac,ae_atom_real_pos ρ,
    hac (ae_atom_real_pos (ρ.fst ⊗ₘ κ)),conditionalInfo_log ρ] with p hllr hp hν he
  have hfst : 0 < ρ.fst.real {p.1} := hp.trans_le (ENNReal.toReal_mono (by finiteness) (atom_le_fst ρ p))
  have hn : (ρ.fst ⊗ₘ κ).real {p} = ρ.fst.real {p.1} * (κ p.1).real {p.2} := by
    simp only [measureReal_def,compProd_atom,ENNReal.toReal_mul]
  have hk : 0 < (κ p.1).real {p.2} := (mul_pos_iff_of_pos_left hfst).mp (hn ▸ hν)
  rw [hllr,hn,Real.log_mul hfst.ne' hk.ne',he]
  dsimp [atomInfo]
  ring

lemma llr_reference_pullback {Ω α β : Type*} [Countable Ω] [Countable α] [Countable β]
    [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass Ω] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → β) (Y : Ω → α)
    (κ : Kernel α β) [IsMarkovKernel κ]
    (hac : μ.map (fun ω => (Y ω,X ω)) ≪ (μ.map (fun ω => (Y ω,X ω))).fst ⊗ₘ κ) :
    (fun ω => llr (μ.map (fun ω => (Y ω,X ω)))
      ((μ.map (fun ω => (Y ω,X ω))).fst ⊗ₘ κ) (Y ω,X ω)) =ᵐ[μ]
      fun ω => atomInfo (κ (Y ω)) (X ω) - conditionedInformation μ X Y ω := by
  let F := fun ω => (Y ω,X ω)
  have : IsProbabilityMeasure (μ.map F) := probabilityMeasure_map (measurable_of_countable _).aemeasurable
  have hF : MeasurePreserving F μ (μ.map F) := ⟨measurable_of_countable _,rfl⟩
  filter_upwards [hF.quasiMeasurePreserving.ae (llr_conditional_reference (μ.map F) κ hac),
    conditionedInformation_eq μ X Y] with ω hω hω'
  rw [hω,hω']

lemma reference_ac_lift {α β γ : Type*} [Countable α] [Countable β] [Countable γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
    (ρ : Measure ((α × γ) × β)) [IsProbabilityMeasure ρ]
    (κ : Kernel α β) [IsMarkovKernel κ]
    (hac : ρ.map (fun p => (p.1.1,p.2)) ≪ (ρ.map (fun p => (p.1.1,p.2))).fst ⊗ₘ κ) :
    ρ ≪ ρ.fst ⊗ₘ κ.comap Prod.fst measurable_fst := by
  apply absolutelyContinuous_of_atoms
  intro p hp
  by_contra hn
  have hfst : ρ.fst {p.1} ≠ 0 := ne_of_gt ((pos_iff_ne_zero.mpr hn).trans_le (atom_le_fst ρ p))
  have hm : ρ.map (fun p => (p.1.1,p.2)) {(p.1.1,p.2)} ≠ 0 :=
    ne_of_gt ((pos_iff_ne_zero.mpr hn).trans_le (atom_le_map ρ _ (measurable_of_countable _) p))
  have hq : ((ρ.map (fun p => (p.1.1,p.2))).fst ⊗ₘ κ) {(p.1.1,p.2)} ≠ 0 := fun h => hm (hac h)
  rw [compProd_atom] at hq
  rw [compProd_atom,Kernel.comap_apply] at hp
  exact (mul_ne_zero hfst (mul_ne_zero_iff.mp hq).2) hp

lemma conditionedInformation_swap_chain {Ω α β γ : Type*} [Countable Ω]
    [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass Ω] [MeasurableSingletonClass α]
    [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
    (μ : Measure Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    (fun ω => conditionedInformation μ X Y ω - conditionedInformation μ X (fun ξ => (Y ξ,Z ξ)) ω) =
      fun ω => conditionedInformation μ Z Y ω - conditionedInformation μ Z (fun ξ => (Y ξ,X ξ)) ω := by
  have hswap : informationOf μ (fun ω => ((Y ω,Z ω),X ω)) =
      informationOf μ (fun ω => ((Y ω,X ω),Z ω)) := by
    funext ξ
    rw [informationOf_fiber,informationOf_fiber]
    congr 3
    ext ζ
    simp [and_assoc,and_comm]
  funext ω
  simp only [conditionedInformation,hswap]
  ring

lemma klDiv_reference_augment {Ω α β γ : Type*} [Countable Ω] [Countable α] [Countable β]
    [Countable γ] [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass Ω] [MeasurableSingletonClass α]
    [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → β) (H : Ω → α) (Z : Ω → γ)
    (κ : Kernel α β) [IsMarkovKernel κ]
    (hac : μ.map (fun ω => (H ω,X ω)) ≪ (μ.map (fun ω => (H ω,X ω))).fst ⊗ₘ κ)
    (hi : Integrable (llr (μ.map (fun ω => (H ω,X ω)))
      ((μ.map (fun ω => (H ω,X ω))).fst ⊗ₘ κ)) (μ.map (fun ω => (H ω,X ω))))
    (hZ : Integrable (informationOf μ Z) μ) :
    let P := μ.map (fun ω => ((H ω,Z ω),X ω))
    let Q := P.fst ⊗ₘ κ.comap Prod.fst measurable_fst
    InformationTheory.klDiv P Q ≠ ∞ ∧
      (InformationTheory.klDiv P Q).toReal =
        (InformationTheory.klDiv (μ.map (fun ω => (H ω,X ω)))
          ((μ.map (fun ω => (H ω,X ω))).fst ⊗ₘ κ)).toReal +
        conditionedEntropy μ Z H - conditionedEntropy μ Z (fun ω => (H ω,X ω)) := by
  dsimp only
  let F := fun ω => (H ω,X ω)
  let G := fun ω => ((H ω,Z ω),X ω)
  let P := μ.map G
  let P₀ := μ.map F
  let Q := P.fst ⊗ₘ κ.comap Prod.fst measurable_fst
  let Q₀ := P₀.fst ⊗ₘ κ
  have : IsProbabilityMeasure P := probabilityMeasure_map (measurable_of_countable _).aemeasurable
  have : IsProbabilityMeasure P₀ := probabilityMeasure_map (measurable_of_countable _).aemeasurable
  have hac' : P ≪ Q := by
    apply reference_ac_lift
    simpa only [P,G,Measure.map_map (measurable_of_countable _) (measurable_of_countable _),Function.comp_def] using hac
  have hF : MeasurePreserving F μ P₀ := ⟨measurable_of_countable _,rfl⟩
  have hG : MeasurePreserving G μ P := ⟨measurable_of_countable _,rfl⟩
  have he : (fun ω => llr P Q (G ω)) =ᵐ[μ]
      fun ω => llr P₀ Q₀ (F ω) + conditionedInformation μ Z H ω -
        conditionedInformation μ Z (fun ξ => (H ξ,X ξ)) ω := by
    filter_upwards [llr_reference_pullback μ X H κ hac,
      llr_reference_pullback μ X (fun ω => (H ω,Z ω)) (κ.comap Prod.fst measurable_fst) hac'] with ω h0 h1
    have hs := congrFun (conditionedInformation_swap_chain μ X H Z) ω
    simp only [Kernel.comap_apply] at h1
    change llr P₀ Q₀ (F ω) = _ at h0
    change llr P Q (G ω) = _ at h1
    linarith
  have hiF : Integrable (fun ω => llr P₀ Q₀ (F ω)) μ := hF.integrable_comp_of_integrable hi
  have hiZH := integrable_conditionedInformation μ Z H hZ
  have hiZX := integrable_conditionedInformation μ Z (fun ω => (H ω,X ω)) hZ
  have hiG : Integrable (fun ω => llr P Q (G ω)) μ := ((hiF.add hiZH).sub hiZX).congr he.symm
  have hiP : Integrable (llr P Q) P :=
    (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
      (measurable_of_countable _).aemeasurable).mpr hiG
  refine ⟨InformationTheory.klDiv_ne_top hac' hiP, ?_⟩
  have hq := InformationTheory.toReal_klDiv hac' hiP
  have hq0 := InformationTheory.toReal_klDiv hac hi
  simp only [probReal_univ,add_sub_cancel_right] at hq hq0
  change (InformationTheory.klDiv P Q).toReal = (InformationTheory.klDiv P₀ Q₀).toReal + _ - _
  rw [hq,hq0]
  have hInt : (∫ p, llr P Q p ∂P) = ∫ ω, llr P Q (G ω) ∂μ :=
    integral_map_of_stronglyMeasurable (measurable_of_countable _) (measurable_of_countable _).stronglyMeasurable
  have hInt0 : (∫ p, llr P₀ Q₀ p ∂P₀) = ∫ ω, llr P₀ Q₀ (F ω) ∂μ :=
    integral_map_of_stronglyMeasurable (measurable_of_countable _) (measurable_of_countable _).stronglyMeasurable
  rw [hInt,hInt0,integral_congr_ae he]
  calc
    _ = (∫ ω, llr P₀ Q₀ (F ω) + conditionedInformation μ Z H ω ∂μ) -
        ∫ ω, conditionedInformation μ Z (fun ξ => (H ξ,X ξ)) ω ∂μ :=
      integral_sub (hiF.add hiZH) hiZX
    _ = _ := by
      congr 1
      exact integral_add hiF hiZH

lemma reference_ac_projection {α β γ : Type*} [Countable α] [Countable β] [Countable γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
    (ρ : Measure (α × γ)) [IsProbabilityMeasure ρ] (f : α → β)
    (κ : Kernel β γ) [IsMarkovKernel κ]
    (hac : ρ ≪ ρ.fst ⊗ₘ κ.comap f (measurable_of_countable _)) :
    ρ.map (fun p => (f p.1,p.2)) ≪ (ρ.map (fun p => (f p.1,p.2))).fst ⊗ₘ κ := by
  let F := fun p : α × γ => (f p.1,p.2)
  let ν := ρ.map F
  apply absolutelyContinuous_of_atoms
  intro p hp
  by_contra hn
  have hm : ν.fst {p.1} ≠ 0 := ne_of_gt ((pos_iff_ne_zero.mpr hn).trans_le (atom_le_fst ν p))
  rw [compProd_atom] at hp
  have hk : κ p.1 {p.2} = 0 := (mul_eq_zero.mp hp).resolve_left hm
  apply hn
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
    ← Set.biUnion_of_singleton (F ⁻¹' {p})]
  apply (measure_biUnion_null_iff (Set.to_countable _)).mpr
  intro x hx
  have he : F x = p := hx
  apply hac
  rw [compProd_atom,Kernel.comap_apply]
  have he1 := congrArg Prod.fst he
  have he2 := congrArg Prod.snd he
  dsimp [F] at he1 he2
  rw [he1,he2,hk,mul_zero]

lemma conditional_mutualInformation_le_reference {α β γ : Type*}
    [Countable α] [Countable β] [Countable γ] [Nonempty γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
    (ρ : Measure (α × γ)) [IsProbabilityMeasure ρ] (ν : Measure α) [IsProbabilityMeasure ν]
    (f : α → β) (κ : Kernel β γ) [IsMarkovKernel κ]
    (hfin : InformationTheory.klDiv ρ (ν ⊗ₘ κ.comap f (measurable_of_countable _)) ≠ ∞)
    (hZ : Integrable (informationOf ρ Prod.snd) ρ) :
    conditionedEntropy ρ Prod.snd (f ∘ Prod.fst) - conditionedEntropy ρ Prod.snd Prod.fst ≤
      (InformationTheory.klDiv ρ (ν ⊗ₘ κ.comap f (measurable_of_countable _))).toReal := by
  let η := κ.comap f (measurable_of_countable _)
  have hchain := InformationTheory.klDiv_compProd_eq_add ρ.fst ν ρ.condKernel η
  rw [Measure.disintegrate] at hchain
  have hle : InformationTheory.klDiv ρ (ρ.fst ⊗ₘ η) ≤ InformationTheory.klDiv ρ (ν ⊗ₘ η) := by
    rw [hchain]
    exact le_add_self
  have hfin' : InformationTheory.klDiv ρ (ρ.fst ⊗ₘ η) ≠ ∞ := ne_top_of_le_ne_top hfin hle
  obtain ⟨hac,hi⟩ := InformationTheory.klDiv_ne_top_iff.mp hfin'
  have hid : ρ.map (fun p : α × γ => (p.1,p.2)) = ρ := by
    change ρ.map id = ρ
    exact Measure.map_id
  have hce : conditionedInformation ρ Prod.snd Prod.fst =ᵐ[ρ] conditionalInfo ρ := by
    simpa only [hid,Prod.mk.eta] using conditionedInformation_eq ρ Prod.snd Prod.fst
  have hci : Integrable (conditionalInfo ρ) ρ :=
    (integrable_conditionedInformation ρ Prod.snd Prod.fst hZ).congr hce
  have hc : Integrable (fun p : α × γ => atomInfo (κ (f p.1)) p.2) ρ := by
    apply (hi.add hci).congr
    filter_upwards [llr_conditional_reference ρ η hac] with p hp
    simpa only [Pi.add_apply,η,Kernel.comap_apply,sub_add_cancel] using congrArg (fun x => x + conditionalInfo ρ p) hp
  let F := fun p : α × γ => (f p.1,p.2)
  let P := ρ.map F
  have : IsProbabilityMeasure P := probabilityMeasure_map (measurable_of_countable _).aemeasurable
  have hcP : Integrable (fun p : β × γ => atomInfo (κ p.1) p.2) P := by
    exact (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
      (measurable_of_countable _).aemeasurable).mpr hc
  have hg := conditionalEntropy_le_crossEntropy P κ (reference_ac_projection ρ f κ hac) hcP
  have heP : conditionedEntropy ρ Prod.snd (f ∘ Prod.fst) = conditionalEntropy P := by
    exact conditionedEntropy_eq_conditionalEntropy ρ Prod.snd (f ∘ Prod.fst)
  have heρ : conditionedEntropy ρ Prod.snd Prod.fst = conditionalEntropy ρ := by
    rw [conditionedEntropy_eq_conditionalEntropy,hid]
  have heI : (∫ p, atomInfo (κ p.1) p.2 ∂P) = ∫ p : α × γ, atomInfo (κ (f p.1)) p.2 ∂ρ :=
    integral_map_of_stronglyMeasurable (measurable_of_countable _) (measurable_of_countable _).stronglyMeasurable
  have hkl := InformationTheory.toReal_klDiv hac hi
  simp only [probReal_univ,add_sub_cancel_right] at hkl
  have hint : (∫ p, llr ρ (ρ.fst ⊗ₘ η) p ∂ρ) =
      (∫ p : α × γ, atomInfo (κ (f p.1)) p.2 ∂ρ) - conditionalEntropy ρ := by
    rw [integral_congr_ae (llr_conditional_reference ρ η hac)]
    exact integral_sub hc hci
  rw [heI] at hg
  rw [heP,heρ]
  calc
    _ ≤ (InformationTheory.klDiv ρ (ρ.fst ⊗ₘ η)).toReal := by rw [hkl,hint]; linarith
    _ ≤ _ := ENNReal.toReal_mono hfin hle

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

def appendWord {d : ℕ} (a b : Word d) : Word d :=
  prefixWord (a.1+b.1) (concatPath a.1 (wordPath a)
    (shiftPath (wordPath a a.1) (wordPath b)))

lemma appendWord_length {d : ℕ} (a b : Word d) : (appendWord a b).1 = a.1+b.1 := rfl

lemma appendWord_before {d : ℕ} (a b : Word d) (hb : wordPath b 0 = 0)
    {i : ℕ} (hi : i ≤ a.1) : wordPath (appendWord a b) i = wordPath a i := by
  rw [appendWord,wordPath_prefixWord (a.1+b.1) _ (by omega)]
  apply concatPath_before _ _ _ _ hi
  simp [shiftPath,hb]

lemma appendWord_after {d : ℕ} (a b : Word d) {i : ℕ} (hi : i ≤ b.1) :
    wordPath (appendWord a b) (a.1+i) = wordPath a a.1 + wordPath b i := by
  rw [appendWord,wordPath_prefixWord (a.1+b.1) _ (Nat.add_le_add_left hi _),concatPath_after]
  exact add_comm _ _

lemma appendWord_prefixWord {d : ℕ} (X : Path d) (n m : ℕ) :
    appendWord (prefixWord n X) (prefixWord m (relativeTail n X)) = prefixWord (n+m) X := by
  apply (prefixWord_eq_iff _ _ _).mpr
  refine ⟨rfl,?_⟩
  intro i hi
  change i ≤ n+m at hi
  rw [wordPath_prefixWord (n+m) X hi]
  change concatPath n (wordPath (prefixWord n X))
    (shiftPath (wordPath (prefixWord n X) n) (wordPath (prefixWord m (relativeTail n X)))) i = X i
  by_cases hin : i ≤ n
  · rw [concatPath_before _ _ _ _ hin,wordPath_prefixWord _ _ hin]
    simp only [wordPath_prefixWord _ _ (le_refl _),wordPath_prefixWord _ _ (Nat.zero_le _),
      shiftPath,relativeTail_apply,Nat.add_zero,sub_self,zero_add]
  · have hn : n ≤ i := by omega
    obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [concatPath_after,shiftPath,wordPath_prefixWord _ _ (le_refl _),
      wordPath_prefixWord _ _ (by omega),relativeTail_apply]
    abel

def concatenateWords {d : ℕ} : (n : ℕ) → (Fin n → Word d) → Word d
  | 0, _ => prefixWord 0 (fun _ => 0)
  | n+1, a => appendWord (concatenateWords n (fun i => a i.castSucc)) (a (Fin.last n))

def concatenateList {d : ℕ} (a : TapeList (Word d)) : Word d := concatenateWords a.1 a.2

lemma concatenateWords_length {d : ℕ} (n : ℕ) (a : Fin n → Word d) :
    (concatenateWords n a).1 = ∑ i : Fin n, (a i).1 := by
  induction n with
  | zero => simp [concatenateWords,prefixWord]
  | succ n ih => simp only [concatenateWords,appendWord_length,ih,Fin.sum_univ_castSucc]

lemma concatenateList_prefix_slabs {d : ℕ} (v : Fin d → ℝ) (X : Path d) (h0 : X 0 = 0) (k : ℕ) :
    concatenateList (tapePrefix k (slabs v X)) = prefixWord (slabTime v X k) X := by
  induction k with
  | zero =>
    apply (prefixWord_eq_iff _ _ _).mpr
    refine ⟨rfl,?_⟩
    intro i hi
    change i ≤ 0 at hi
    have hi0 : i = 0 := Nat.eq_zero_of_le_zero hi
    subst i
    simp [wordPath_prefixWord,h0]
  | succ k ih =>
    change appendWord (concatenateList (tapePrefix k (slabs v X))) (slabs v X k) = _
    rw [ih,slabTime_succ]
    have he : slabs v X k = prefixWord (slabs v X k).1 (relativeTail (slabTime v X k) X) := by
      change prefixWord (slabs v X k).1 ((cutSuffix v)^[k] X) = _
      rw [iterated_cutSuffix_eq_relativeTail v X h0 k]
    rw [he]
    exact appendWord_prefixWord X _ _

lemma concatenateList_length {d : ℕ} (a : TapeList (Word d)) :
    (concatenateList a).1 = listHeight (fun w => w.1) a := concatenateWords_length a.1 a.2

noncomputable def recordWord {d : ℕ} (v : Fin d → ℝ) (H : ℕ) (X : Path d) : Word d := by
  classical
  exact if h : ∃ n, recordPrefix v H X n then prefixWord (Nat.find h) X else prefixWord 0 X

lemma recordWord_eq {d : ℕ} (v : Fin d → ℝ) (H : ℕ) (X : Path d) {n : ℕ}
    (hn : recordPrefix v H X n) : recordWord v H X = prefixWord n X := by
  classical
  have hex : ∃ n, recordPrefix v H X n := ⟨n,hn⟩
  rw [recordWord,dite_eq_left hex]
  rw [recordPrefix_unique v H X (Nat.find_spec hex) hn]

lemma recordWord_atom {d : ℕ} (v : Fin d → ℝ) (H : ℕ) (X : Path d) (a : Word d) :
    (X ∈ reachRecord v H ∧ recordWord v H X = a) ↔
      recordPrefix v H (wordPath a) a.1 ∧ X ∈ pathCylinder a.1 (wordPath a) := by
  constructor
  · rintro ⟨hX,ha⟩
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hX
    rw [recordWord_eq v H X hn] at ha
    obtain ⟨rfl,hpre⟩ := (prefixWord_eq_iff n X a).mp ha
    exact ⟨recordPrefix_prefix v H hn (fun i hi => (hpre i hi).symm),hpre⟩
  · rintro ⟨ha,hX⟩
    have hr := recordPrefix_prefix v H ha hX
    exact ⟨Set.mem_iUnion.mpr ⟨a.1,hr⟩,
      (recordWord_eq v H X hr).trans ((prefixWord_eq_iff _ _ _).mpr ⟨rfl,hX⟩)⟩

lemma measurable_recordWord {d : ℕ} (v : Fin d → ℝ) (H : ℕ) : Measurable (recordWord v H) := by
  apply measurable_to_countable'
  intro a
  have he : recordWord v H ⁻¹' {a} =
      (if recordPrefix v H (wordPath a) a.1 then pathCylinder a.1 (wordPath a) else ∅) ∪
      ((reachRecord v H)ᶜ ∩ prefixWord 0 ⁻¹' {a}) := by
    classical
    ext X
    by_cases hX : X ∈ reachRecord v H
    · have hh := recordWord_atom v H X a
      simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_union,Set.mem_inter_iff,
        Set.mem_compl_iff,hX,not_true_eq_false,false_and,or_false,true_and] at hh ⊢
      split_ifs <;> simp_all
    · have hn : ¬∃ n, recordPrefix v H X n := by simpa only [reachRecord,Set.mem_iUnion,Set.mem_ofPred_eq] using hX
      have hrw : recordWord v H X = prefixWord 0 X := by simp only [recordWord,dite_eq_right hn]
      have hnot : recordPrefix v H (wordPath a) a.1 → X ∉ pathCylinder a.1 (wordPath a) := by
        intro ha hc
        exact hX ((recordWord_atom v H X a).mpr ⟨ha,hc⟩).1
      split_ifs <;> simp_all
  rw [he]
  apply MeasurableSet.union
  · split_ifs
    · exact measurableSet_pathCylinder _ _
    · exact MeasurableSet.empty
  · exact (measurableSet_reachRecord v H).compl.inter ((measurable_prefixWord 0) (measurableSet_singleton _))

lemma conditioned_recordWord_atom {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (v : Fin d → ℝ) (hp : 0 < annealed μ 0 (nonBacktracking v)) (H : ℕ) (a : Word d) :
    conditioned μ v (recordTailEvent v H Set.univ ∩ recordWord v H ⁻¹' {a}) =
      annealed μ 0 (reachRecord v H ∩ recordWord v H ⁻¹' {a}) := by
  let := conditioned_probability μ v hp
  classical
  have he0 : reachRecord v H ∩ recordWord v H ⁻¹' {a} =
      if recordPrefix v H (wordPath a) a.1 then pathCylinder a.1 (wordPath a) else ∅ := by
    ext X
    simp only [Set.mem_inter_iff,Set.mem_preimage,Set.mem_singleton_iff,recordWord_atom]
    split_ifs <;> simp_all
  have he1 : recordTailEvent v H Set.univ ∩ recordWord v H ⁻¹' {a} =
      if recordPrefix v H (wordPath a) a.1 then
        pathCylinder a.1 (wordPath a) ∩ relativeTail a.1 ⁻¹' (Set.univ ∩ nonBacktracking v) else ∅ := by
    ext X
    simp only [Set.mem_inter_iff,Set.mem_preimage,Set.mem_singleton_iff]
    split_ifs with ha
    · constructor
      · rintro ⟨hX,hw⟩
        obtain ⟨n,hn,hD⟩ := Set.mem_iUnion.mp hX
        have hpre := ((recordWord_atom v H X a).mp ⟨Set.mem_iUnion.mpr ⟨n,hn⟩,hw⟩).2
        have hnn := recordPrefix_unique v H X hn (recordPrefix_prefix v H ha hpre)
        subst n
        exact ⟨hpre,hD⟩
      · rintro ⟨hpre,ht⟩
        have hr := recordPrefix_prefix v H ha hpre
        refine ⟨Set.mem_iUnion.mpr ⟨a.1,hr,ht⟩,?_⟩
        exact ((recordWord_atom v H X a).mpr ⟨ha,hpre⟩).2
    · constructor
      · rintro ⟨hX,hw⟩
        obtain ⟨n,hn,_⟩ := Set.mem_iUnion.mp hX
        exact ha ((recordWord_atom v H X a).mp ⟨Set.mem_iUnion.mpr ⟨n,hn⟩,hw⟩).1
      · exact False.elim
  rw [he0,he1]
  split_ifs with ha
  · rw [conditioned_recordCylinder μ v H a.1 (wordPath a) ha MeasurableSet.univ,measure_univ,mul_one]
  · simp only [measure_empty]

noncomputable def rawBridgeMeasure {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (v : Fin d → ℝ) (H : ℕ) : Measure (Word d) :=
  ((annealed μ 0).restrict (reachRecord v H)).map (recordWord v H)

lemma rawBridgeMeasure_conditioned {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (v : Fin d → ℝ) (hp : 0 < annealed μ 0 (nonBacktracking v)) (H : ℕ) :
    ((conditioned μ v).restrict (recordTailEvent v H Set.univ)).map (recordWord v H) =
      rawBridgeMeasure μ v H := by
  apply Measure.ext_of_singleton
  intro a
  simp only [rawBridgeMeasure,Measure.map_apply (measurable_recordWord v H) (measurableSet_singleton _),
    Measure.restrict_apply ((measurable_recordWord v H) (measurableSet_singleton _))]
  simpa only [Set.inter_comm] using conditioned_recordWord_atom μ v hp H a

lemma concatenate_cutList_slabs {d : ℕ} (v : Fin d → ℝ) (H : ℕ) (X : Path d)
    (hX : GoodSlabPath v X) (hH : slabs v X ∈ tapeCut v H) :
    concatenateList (cutList (slabRecords v) H (slabs v X)) = recordWord v H X := by
  obtain ⟨k,hk⟩ := hH
  have hpos : ∀ i, 0 < slabRecords v (slabs v X i) := fun i => slabRecords_pos v _ (hX.2 i)
  rw [cutList,cutListIndex_eq (slabRecords v) H (slabs v X) hpos hk,
    concatenateList_prefix_slabs v X hX.1 k]
  symm
  apply recordWord_eq
  refine ⟨(slabTime_boundary v X hX k).imp_right And.left,?_,fun i _ => ?_⟩
  · rw [recordCount_slabTime v X hX k]
    exact hk
  · exact goodSlabPath_height_nonneg v X hX i

lemma bridgeListMeasure_concatenate {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) (H : ℕ) :
    letI := slabLaw_probability μ v hp
    (bridgeListMeasure (slabLaw μ v) (slabRecords v) H).map concatenateList =
      rawBridgeMeasure μ v H := by
  let := slabLaw_probability μ v hp
  let := conditioned_probability μ v hp
  rw [← rawBridgeMeasure_conditioned μ v hp H]
  apply Measure.ext_of_singleton
  intro a
  rw [Measure.map_apply (measurable_of_countable concatenateList) (measurableSet_singleton _),
    bridgeListMeasure,Measure.map_apply (measurable_cutList (slabRecords v) H)
      ((measurable_of_countable concatenateList) (measurableSet_singleton _)),
    Measure.restrict_apply ((measurable_cutList (slabRecords v) H)
      ((measurable_of_countable concatenateList) (measurableSet_singleton _))),
    ← slabs_map_eq_infinitePi μ hell v hv hp,
    Measure.map_apply (measurable_slabs v)
      (((measurable_cutList (slabRecords v) H)
        ((measurable_of_countable concatenateList) (measurableSet_singleton _))).inter
        (measurableSet_renewalCut (slabRecords v) H)),
    Measure.map_apply (measurable_recordWord v H) (measurableSet_singleton _),
    Measure.restrict_apply ((measurable_recordWord v H) (measurableSet_singleton _))]
  apply measure_congr
  filter_upwards [ae_goodSlabPath μ hell v hv hp] with X hX
  apply propext
  change (concatenateList (cutList (slabRecords v) H (slabs v X)) = a ∧
    slabs v X ∈ tapeCut v H) ↔ (recordWord v H X = a ∧ X ∈ recordTailEvent v H Set.univ)
  constructor
  · rintro ⟨ha,hH⟩
    exact ⟨(concatenate_cutList_slabs v H X hX hH).symm.trans ha,
      (tapeCut_iff_recordTailEvent v X hX H).mp hH⟩
  · rintro ⟨ha,hH⟩
    have hc := (tapeCut_iff_recordTailEvent v X hX H).mpr hH
    exact ⟨(concatenate_cutList_slabs v H X hX hc).trans ha,hc⟩

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

def wordCylinder {d : ℕ} (a : Word d) : Set (Path d) := pathCylinder a.1 (wordPath a)

def wordEnd {d : ℕ} (a : Word d) : Site d := wordPath a a.1

def wordDepartures {d : ℕ} (a : Word d) : Set (Site d) :=
  {y | ∃ i < a.1, wordPath a i = y}

def PrefixFreeWords {d : ℕ} (A : Set (Word d)) : Prop :=
  Pairwise (fun (a b : A) => Disjoint (wordCylinder a.val) (wordCylinder b.val))

def firstHitWord {d : ℕ} (K : Set (Site d)) (a : Word d) : Prop :=
  wordEnd a ∈ K ∧ ∀ i < a.1, wordPath a i ∉ K

lemma firstHitWords_prefixFree {d : ℕ} (K : Set (Site d)) :
    PrefixFreeWords {a | firstHitWord K a} := by
  intro a b hab
  apply Set.disjoint_left.mpr
  intro X hXa hXb
  have hn : a.val.1 = b.val.1 := by
    apply le_antisymm
    · by_contra h
      have hlt : b.val.1 < a.val.1 := by omega
      apply a.property.2 _ hlt
      rw [← hXa _ hlt.le,hXb _ (le_refl _)]
      exact b.property.1
    · by_contra h
      have hlt : a.val.1 < b.val.1 := by omega
      apply b.property.2 _ hlt
      rw [← hXb _ hlt.le,hXa _ (le_refl _)]
      exact a.property.1
  apply hab
  apply Subtype.ext
  have ha := (prefixWord_eq_iff a.val.1 X a.val).mpr ⟨rfl,hXa⟩
  have hb := (prefixWord_eq_iff a.val.1 X b.val).mpr ⟨hn,hXb⟩
  exact ha.symm.trans hb

lemma PrefixFreeWords.mono {d : ℕ} {A B : Set (Word d)} (hA : PrefixFreeWords A)
    (hBA : B ⊆ A) : PrefixFreeWords B := by
  intro a b hab
  exact hA (i := ⟨a.val,hBA a.property⟩) (j := ⟨b.val,hBA b.property⟩)
    (fun he => hab (Subtype.ext (congrArg (fun u : A => u.val) he)))

lemma quenched_restart_word {d : ℕ} (ω : Environment d) (x : Site d) (a : Word d)
    {E : Set (Path d)} (hE : MeasurableSet E) :
    quenchedKernel d (ω,x) (wordCylinder a ∩ tailPath a.1 ⁻¹' E) =
      quenchedKernel d (ω,x) (wordCylinder a) * quenchedKernel d (ω,wordEnd a) E := by
  rw [wordCylinder,quenched_prefix_tail_apply ω x a.1 (wordPath a) hE,quenchedKernel_cylinder]
  rfl

lemma quenched_prefix_family {d : ℕ} (ω : Environment d) (x : Site d) (A : Set (Word d))
    (hA : PrefixFreeWords A) (E : Word d → Set (Path d)) (hE : ∀ a ∈ A, MeasurableSet (E a)) :
    quenchedKernel d (ω,x) (⋃ a : A, wordCylinder a ∩ tailPath a.val.1 ⁻¹' E a) =
      ∑' a : A, quenchedKernel d (ω,x) (wordCylinder a) *
        quenchedKernel d (ω,wordEnd a) (E a) := by
  rw [measure_iUnion (fun a b hab => (hA hab).mono Set.inter_subset_left Set.inter_subset_left)
    (fun a : A => (measurableSet_pathCylinder a.val.1 (wordPath a.val)).inter ((measurable_tailPath _) (hE a.val a.property)))]
  apply tsum_congr
  intro a
  exact quenched_restart_word ω x a (hE a a.property)

lemma quenched_prefix_family_bound {d : ℕ} (ω : Environment d) (x : Site d)
    (A : Set (Word d)) (hA : PrefixFreeWords A) (E : Word d → Set (Path d))
    (hE : ∀ a ∈ A, MeasurableSet (E a)) (B : Set (Path d)) (c : ℝ≥0∞)
    (hc : ∀ a ∈ A, c ≤ quenchedKernel d (ω,wordEnd a) (E a))
    (hsub : ∀ a ∈ A, wordCylinder a ∩ tailPath a.1 ⁻¹' E a ⊆ B) :
    c * quenchedKernel d (ω,x) (⋃ a : A, wordCylinder a) ≤ quenchedKernel d (ω,x) B := by
  rw [measure_iUnion (f := fun a : A => wordCylinder a.val) hA
    (fun _ => measurableSet_pathCylinder _ _),← ENNReal.tsum_mul_left]
  calc
    ∑' a : A, c * quenchedKernel d (ω,x) (wordCylinder a) ≤
        ∑' a : A, quenchedKernel d (ω,x) (wordCylinder a) *
          quenchedKernel d (ω,wordEnd a) (E a) := by
      apply ENNReal.tsum_le_tsum
      intro a
      rw [mul_comm c]
      exact mul_le_mul_right (hc a a.property) _
    _ = quenchedKernel d (ω,x) (⋃ a : A, wordCylinder a ∩ tailPath a.val.1 ⁻¹' E a) :=
      (quenched_prefix_family ω x A hA E hE).symm
    _ ≤ _ := measure_mono (Set.iUnion_subset (fun a => hsub a a.property))

lemma word_contact_transfer {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (a : Word d) (x : Site d) {E : Set (Path d)} (hE : MeasurableSet E) :
    (∫⁻ ω, pathWeight a.1 (wordPath a) ω *
      quenchedKernel d (ω,x) (E ∩ avoids (wordDepartures a)) ∂environmentLaw μ) =
    (∫⁻ ω, pathWeight a.1 (wordPath a) ω ∂environmentLaw μ) *
      annealed μ x (E ∩ avoids (wordDepartures a)) := by
  let r : Row d := Classical.choice (nonempty_of_isProbabilityMeasure μ)
  rw [path_departure_transfer μ (wordDepartures a) a.1 (wordPath a)
    (fun i hi => ⟨i,hi,rfl⟩) _ (measurable_quenched_avoids_on_rows _ r _ hE),
    annealed_apply μ x (hE.inter (measurableSet_avoids _))]

lemma annealed_ae_quenched {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x : Site d) {E : Set (Path d)} (hE : MeasurableSet E)
    (h : ∀ᵐ X ∂annealed μ x, X ∈ E) :
    ∀ᵐ ω ∂environmentLaw μ, ∀ᵐ X ∂quenchedKernel d (ω,x), X ∈ E := by
  have hz : annealed μ x Eᶜ = 0 := by
    rw [ae_iff] at h
    exact h
  rw [annealed_apply μ x hE.compl] at hz
  have hm : Measurable (fun ω : Environment d => quenchedKernel d (ω,x) Eᶜ) :=
    ((quenchedKernel d).measurable_coe hE.compl).comp (measurable_id.prodMk measurable_const)
  filter_upwards [(lintegral_eq_zero_iff hm).mp hz] with ω hω
  rw [ae_iff]
  exact hω

lemma annealed_exit_band {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (x : Site d) (v : Fin d → ℝ) (hv : v ≠ 0) (a b : ℝ) :
    ∀ᵐ X ∂annealed μ x, ∃ n, height v (X n) ∉ Set.Icc a b := by
  filter_upwards [finite_supremum μ hell x v hv] with X hX
  by_contra h
  have hb : ∀ n, height v (X n) ∈ Set.Icc a b := by simpa only [not_exists,not_not] using h
  have ht := tendsto_atBot.mp (hX ⟨b,fun n => (hb n).2⟩) (a-1)
  obtain ⟨n,hn⟩ := ht.exists
  have ha := (hb n).1
  linarith

lemma measurableSet_exit_band {d : ℕ} (v : Fin d → ℝ) (a b : ℝ) :
    MeasurableSet {X : Path d | ∃ n, height v (X n) ∉ Set.Icc a b} := by
  simp only [Set.ofPred_exists]
  exact MeasurableSet.iUnion (fun n =>
    (((measurable_of_countable (height v)).comp (measurable_pi_apply n)) measurableSet_Icc).compl)

lemma quenched_exit_all_integer_bands {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0) :
    ∀ᵐ ω ∂environmentLaw μ, ∀ (x : Site d) (a b : ℤ),
      ∀ᵐ X ∂quenchedKernel d (ω,x), ∃ n, height v (X n) ∉ Set.Icc (a : ℝ) (b : ℝ) := by
  simp only [ae_all_iff]
  intro x a b
  exact annealed_ae_quenched μ x (measurableSet_exit_band v a b)
    (annealed_exit_band μ hell x v hv a b)

def hitBefore {d : ℕ} (A B : Set (Site d)) : Set (Path d) :=
  {X | ∃ n, X n ∈ A ∧ ∀ i ≤ n, X i ∉ B}

lemma measurableSet_hitBefore {d : ℕ} (A B : Set (Site d)) : MeasurableSet (hitBefore A B) := by
  simp only [hitBefore,Set.ofPred_exists,Set.ofPred_and,Set.ofPred_forall]
  apply MeasurableSet.iUnion
  intro n
  exact (((Set.to_countable A).measurableSet).preimage (measurable_pi_apply n)).inter
    (MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun _ =>
      (((Set.to_countable B).measurableSet).preimage (measurable_pi_apply i)).compl)))

lemma hitBefore_disjoint {d : ℕ} (A B : Set (Site d)) : Disjoint (hitBefore A B) (hitBefore B A) := by
  apply Set.disjoint_left.mpr
  rintro X ⟨n,hn,hB⟩ ⟨m,hm,hA⟩
  rcases le_total n m with h | h
  · exact hA n h hn
  · exact hB m h hm

lemma hitBefore_union_eq_eventual {d : ℕ} (A B : Set (Site d)) (hAB : Disjoint A B) :
    hitBefore A B ∪ hitBefore B A = {X | ∃ n, X n ∈ A ∪ B} := by
  ext X
  constructor
  · rintro (⟨n,hn,_⟩ | ⟨n,hn,_⟩)
    · exact ⟨n,Or.inl hn⟩
    · exact ⟨n,Or.inr hn⟩
  · intro h
    let n := Nat.find h
    have hn := Nat.find_spec h
    have hp (i : ℕ) (hi : i < n) : X i ∉ A ∪ B := Nat.find_min h hi
    rcases hn with ha | hb
    · left
      refine ⟨n,ha,fun i hi hm => ?_⟩
      rcases lt_or_eq_of_le hi with hir | rfl
      · exact hp i hir (Or.inr hm)
      · exact Set.disjoint_left.mp hAB ha hm
    · right
      refine ⟨n,hb,fun i hi hm => ?_⟩
      rcases lt_or_eq_of_le hi with hir | rfl
      · exact hp i hir (Or.inl hm)
      · exact Set.disjoint_left.mp hAB hm hb

lemma hitBefore_tail_subset {d : ℕ} (A B : Set (Site d)) (n : ℕ) (γ : Path d)
    (hB : ∀ i < n, γ i ∉ B) :
    pathCylinder n γ ∩ tailPath n ⁻¹' hitBefore A B ⊆ hitBefore A B := by
  rintro X ⟨hX,m,hm,hbm⟩
  refine ⟨n+m,hm,fun i hi hbi => ?_⟩
  by_cases hin : i < n
  · exact hB i hin (by rwa [hX i hin.le] at hbi)
  · have hn : n ≤ i := by omega
    obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hn
    exact hbm j (by omega) hbi

lemma prefixWord_of_wordCylinder {d : ℕ} (a : Word d) (X : Path d)
    (hX : X ∈ wordCylinder a) (j : ℕ) (hj : j ≤ a.1) :
    prefixWord j X = prefixWord j (wordPath a) := by
  apply (prefixWord_eq_iff j X _).mpr
  refine ⟨rfl,fun i hi => ?_⟩
  rw [wordPath_prefixWord j _ hi]
  exact hX i (hi.trans hj)

def firstPrefixWord {d : ℕ} (P : Word d → Prop) (a : Word d) : Prop :=
  P a ∧ ∀ j < a.1, ¬ P (prefixWord j (wordPath a))

lemma firstPrefixWords_prefixFree {d : ℕ} (P : Word d → Prop) :
    PrefixFreeWords {a | firstPrefixWord P a} := by
  intro a b hab
  apply Set.disjoint_left.mpr
  intro X ha hb
  have hea : prefixWord a.val.1 X = a.val := (prefixWord_eq_iff _ _ _).mpr ⟨rfl,ha⟩
  have heb : prefixWord b.val.1 X = b.val := (prefixWord_eq_iff _ _ _).mpr ⟨rfl,hb⟩
  have hn : a.val.1 = b.val.1 := by
    apply le_antisymm
    · by_contra h
      have hlt : b.val.1 < a.val.1 := by omega
      apply a.property.2 _ hlt
      rw [← prefixWord_of_wordCylinder a.val X ha _ hlt.le,heb]
      exact b.property.1
    · by_contra h
      have hlt : a.val.1 < b.val.1 := by omega
      apply b.property.2 _ hlt
      rw [← prefixWord_of_wordCylinder b.val X hb _ hlt.le,hea]
      exact a.property.1
  apply hab
  apply Subtype.ext
  rw [← hea,← heb,hn]

lemma firstPrefixWords_union {d : ℕ} (P : Word d → Prop) :
    (⋃ a : {a | firstPrefixWord P a}, wordCylinder a.val) =
      {X : Path d | ∃ n, P (prefixWord n X)} := by
  ext X
  constructor
  · rintro ⟨_,⟨a,rfl⟩,ha⟩
    refine ⟨a.val.1,?_⟩
    rw [(prefixWord_eq_iff _ _ _).mpr ⟨rfl,ha⟩]
    exact a.property.1
  · intro h
    let n := Nat.find h
    have hn : P (prefixWord n X) := Nat.find_spec h
    have ha : firstPrefixWord P (prefixWord n X) := by
      refine ⟨hn,fun j hj hh => ?_⟩
      have hX : X ∈ wordCylinder (prefixWord n X) := by
        intro i hi
        exact (wordPath_prefixWord n X hi).symm
      rw [← prefixWord_of_wordCylinder _ X hX j hj.le] at hh
      exact Nat.find_min h hj hh
    apply Set.mem_iUnion.mpr
    refine ⟨⟨prefixWord n X,ha⟩,?_⟩
    intro i hi
    exact (wordPath_prefixWord n X hi).symm

def visitAfterWord {d : ℕ} (R A K : Set (Site d)) (a : Word d) : Prop :=
  wordEnd a ∈ A ∧ (∃ j ≤ a.1, wordPath a j ∈ R) ∧ ∀ j ≤ a.1, wordPath a j ∉ K

def visitAfter {d : ℕ} (R A K : Set (Site d)) : Set (Path d) :=
  {X | ∃ n, X n ∈ A ∧ (∃ j ≤ n, X j ∈ R) ∧ ∀ j ≤ n, X j ∉ K}

lemma visitAfter_eq_firstPrefix {d : ℕ} (R A K : Set (Site d)) :
    visitAfter R A K = ⋃ a : {a | firstPrefixWord (visitAfterWord R A K) a}, wordCylinder a.val := by
  rw [firstPrefixWords_union]
  ext X
  change (∃ n, X n ∈ A ∧ (∃ j ≤ n, X j ∈ R) ∧ ∀ j ≤ n, X j ∉ K) ↔
    ∃ n, wordPath (prefixWord n X) n ∈ A ∧
      (∃ j ≤ n, wordPath (prefixWord n X) j ∈ R) ∧ ∀ j ≤ n, wordPath (prefixWord n X) j ∉ K
  apply exists_congr
  intro n
  rw [wordPath_prefixWord n X le_rfl]
  constructor
  · rintro ⟨ha,⟨j,hj,hr⟩,hk⟩
    refine ⟨ha,⟨j,hj,?_⟩,fun j hj => ?_⟩
    · rwa [wordPath_prefixWord n X hj]
    · rw [wordPath_prefixWord n X hj]
      exact hk j hj
  · rintro ⟨ha,⟨j,hj,hr⟩,hk⟩
    refine ⟨ha,⟨j,hj,?_⟩,fun j hj => ?_⟩
    · rwa [wordPath_prefixWord n X hj] at hr
    · have hh := hk j hj
      rwa [wordPath_prefixWord n X hj] at hh

lemma measurableSet_visitAfter {d : ℕ} (R A K : Set (Site d)) : MeasurableSet (visitAfter R A K) := by
  rw [visitAfter_eq_firstPrefix]
  exact MeasurableSet.iUnion (fun _ => measurableSet_pathCylinder _ _)

lemma quenched_visitAfter_bound {d : ℕ} (ω : Environment d) (x : Site d)
    (R A B C : Set (Site d)) (c : ℝ≥0∞)
    (hc : ∀ y ∈ A, c ≤ quenchedKernel d (ω,y) (hitBefore B C)) :
    c * quenchedKernel d (ω,x) (visitAfter R A (B ∪ C)) ≤
      quenchedKernel d (ω,x) (hitBefore R B ∩ hitBefore B C) := by
  rw [visitAfter_eq_firstPrefix]
  apply quenched_prefix_family_bound ω x _ (firstPrefixWords_prefixFree _) (fun _ => hitBefore B C)
    (fun _ _ => measurableSet_hitBefore B C) _ c
  · intro a ha
    exact hc (wordEnd a) ha.1.1
  · intro a ha X hX
    have hp := ha.1
    constructor
    · obtain ⟨j,hj,hr⟩ := hp.2.1
      refine ⟨j,?_,fun i hi hbi => ?_⟩
      · rwa [hX.1 j hj]
      · exact hp.2.2 i (hi.trans hj) (Or.inl (by rwa [← hX.1 i (hi.trans hj)]))
    · exact hitBefore_tail_subset B C a.1 (wordPath a)
        (fun i hi hci => hp.2.2 i hi.le (Or.inr hci)) hX

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

def oppositeStep {d : ℕ} (e : Step d) : Step d := (e.1,!e.2)

lemma axisDirection_opposite {d : ℕ} (e : Step d) :
    axisDirection (oppositeStep e) = -axisDirection e := by
  ext i
  rcases e with ⟨j,b⟩
  cases b <;> simp [axisDirection,oppositeStep,Pi.single_apply] <;> split_ifs <;> norm_num

lemma axisHeight_opposite {d : ℕ} (e : Step d) (x : Site d) :
    axisHeight (oppositeStep e) x = -axisHeight e x := by
  rcases e with ⟨i,b⟩
  cases b <;> simp [axisHeight,oppositeStep]

lemma axisHeight_neg {d : ℕ} (e : Step d) (x : Site d) :
    axisHeight e (-x) = -axisHeight e x := by
  rcases e with ⟨i,b⟩
  cases b <;> simp [axisHeight]

lemma axisHeight_sum {d : ℕ} {ι : Type*} (e : Step d) (s : Finset ι) (f : ι → Site d) :
    axisHeight e (∑ i ∈ s, f i) = ∑ i ∈ s, axisHeight e (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [axisHeight_zero]
  | @insert i s hi ih => simp [Finset.sum_insert hi,axisHeight_add,ih]

lemma axisHeight_step_self {d : ℕ} (e : Step d) : axisHeight e (stepVector e) = 1 := by
  rcases e with ⟨i,b⟩
  cases b <;> simp [axisHeight,stepVector]

lemma axisHeight_wordEnd {d : ℕ} (e : Step d) (a : Word d)
    (ha : RegenerationWord (axisDirection e) a) :
    axisHeight e (wordEnd a) = (slabRecords (axisDirection e) a : ℤ) := by
  have h := axis_slabWidth_eq_records e a ha
  change height (axisDirection e) (wordEnd a) = _ at h
  rw [height_axisDirection] at h
  exact_mod_cast h

lemma axisHeight_word_interior {d : ℕ} (e : Step d) (a : Word d)
    (ha : RegenerationWord (axisDirection e) a) (i : ℕ) (hi : i < a.1) :
    0 ≤ axisHeight e (wordPath a i) ∧
      axisHeight e (wordPath a i) < (slabRecords (axisDirection e) a : ℤ) := by
  have h := ha.2.2.2.1 i hi
  have hh := axisHeight_wordEnd e a ha
  change axisHeight e (wordPath a a.1) = _ at hh
  rw [height_axisDirection,height_axisDirection,hh] at h
  exact ⟨by exact_mod_cast h.1,by exact_mod_cast h.2⟩

def placedAxis {d : ℕ} (e : Step d) (b : Bool) : Step d := if b then oppositeStep e else e

noncomputable def placedWidth {d : ℕ} (e : Step d) (b : Bool) : Word d → ℕ :=
  slabRecords (axisDirection (placedAxis e b))

def opposedAnchor {d : ℕ} (e : Step d) (Z : TwoTape (Word d)) (b : Bool) (i : ℕ) : Site d :=
  if b then -stepVector e + ∑ j ∈ Finset.range i, wordEnd (Z (true,j))
  else -(∑ j ∈ Finset.range (i+1), wordEnd (Z (false,j)))

def opposedSite {d : ℕ} (e : Step d) (Z : TwoTape (Word d)) (b : Bool) (i t : ℕ) : Site d :=
  opposedAnchor e Z b i + wordPath (Z (b,i)) t

def opposedDeparture {d : ℕ} (e : Step d) (Z : TwoTape (Word d)) (b : Bool) (y : Site d) : Prop :=
  ∃ i, ∃ t < (Z (b,i)).1, opposedSite e Z b i t = y

def contactAt {d : ℕ} (e : Step d) (Z : TwoTape (Word d)) (y : Site d) : Prop :=
  opposedDeparture e Z false y ∧ opposedDeparture e Z true y

def contactDepth {d : ℕ} (e : Step d) (Z : TwoTape (Word d)) (h : ℕ) : Prop :=
  ∃ y, contactAt e Z y ∧ -axisHeight e y = (h : ℤ)

lemma opposedAnchor_height {d : ℕ} (e : Step d) (Z : TwoTape (Word d))
    (hZ : ∀ b i, RegenerationWord (axisDirection (placedAxis e b)) (Z (b,i)))
    (b : Bool) (i : ℕ) :
    -axisHeight e (opposedAnchor e Z b i) =
      if b then 1 + (tapeHeight (placedWidth e true) (fun j => Z (true,j)) i : ℤ)
      else (tapeHeight (placedWidth e false) (fun j => Z (false,j)) (i+1) : ℤ) := by
  have hp (j : ℕ) : axisHeight e (wordEnd (Z (false,j))) = (placedWidth e false (Z (false,j)) : ℤ) :=
    axisHeight_wordEnd e _ (hZ false j)
  have hm (j : ℕ) : axisHeight e (wordEnd (Z (true,j))) = -(placedWidth e true (Z (true,j)) : ℤ) := by
    have hh := axisHeight_wordEnd (oppositeStep e) _ (hZ true j)
    rw [axisHeight_opposite] at hh
    exact neg_eq_iff_eq_neg.mp hh
  cases b <;> simp [opposedAnchor,axisHeight_neg,axisHeight_add,axisHeight_sum,
    axisHeight_step_self,hp,hm,tapeHeight,Finset.sum_neg_distrib,add_comm]

lemma opposed_departure_band {d : ℕ} (e : Step d) (Z : TwoTape (Word d))
    (hZ : ∀ b i, RegenerationWord (axisDirection (placedAxis e b)) (Z (b,i)))
    (b : Bool) (i t : ℕ) (ht : t < (Z (b,i)).1) :
    let s := tapeHeight (placedWidth e b) (fun j => Z (b,j)) i
    let L := placedWidth e b (Z (b,i))
    (s : ℤ) < -axisHeight e (opposedSite e Z b i t) ∧
      -axisHeight e (opposedSite e Z b i t) ≤ (s+L : ℕ) := by
  have hc := axisHeight_word_interior (placedAxis e b) (Z (b,i)) (hZ b i) t ht
  have ha := opposedAnchor_height e Z hZ b i
  dsimp only
  unfold opposedSite
  rw [axisHeight_add]
  cases b
  · simp only [placedAxis,Bool.false_eq_true,↓reduceIte] at hc ha
    simp only [tapeHeight,Finset.sum_range_succ,Nat.cast_add] at ha ⊢
    simp only [placedWidth,placedAxis,Bool.false_eq_true,↓reduceIte] at *
    omega
  · simp only [placedAxis,↓reduceIte,axisHeight_opposite] at hc ha
    simp only [placedWidth,placedAxis,↓reduceIte] at *
    push_cast
    omega

lemma axial_step_unique {d : ℕ} (e f : Step d) (h : axisHeight e (stepVector f) = 1) :
    f = e := by
  rcases e with ⟨i,b⟩
  rcases f with ⟨j,c⟩
  by_cases hij : i = j
  · subst j
    cases b <;> cases c <;> simp_all [axisHeight,stepVector]
  · cases b <;> cases c <;> simp [axisHeight,stepVector,hij] at h

lemma axis_word_last_step {d : ℕ} (e : Step d) (a : Word d)
    (ha : RegenerationWord (axisDirection e) a) :
    wordEnd a = wordPath a (a.1-1) + stepVector e := by
  have hp : a.1-1 < a.1 := by have := ha.1; omega
  have hh := axisHeight_word_interior e a ha (a.1-1) hp
  obtain ⟨f,hf⟩ := ha.2.2.1 (a.1-1) hp
  rw [Nat.sub_add_cancel (by omega : 1 ≤ a.1)] at hf
  have he : axisHeight e (stepVector f) = 1 := by
    have htt := axisHeight_wordEnd e a ha
    change axisHeight e (wordPath a a.1) = _ at htt
    rw [hf,axisHeight_add] at htt
    have hle := axisHeight_step_le e f
    omega
  rw [axial_step_unique e f he] at hf
  exact hf

lemma opposed_forced_contact {d : ℕ} (e : Step d) (Z : TwoTape (Word d))
    (hZ : ∀ b i, RegenerationWord (axisDirection (placedAxis e b)) (Z (b,i))) :
    contactAt e Z (-stepVector e) ∧ contactDepth e Z 1 := by
  have hc : contactAt e Z (-stepVector e) := by
    constructor
    · refine ⟨0,(Z (false,0)).1-1,by have := (hZ false 0).1; omega,?_⟩
      have ht := axis_word_last_step e (Z (false,0)) (hZ false 0)
      simp only [opposedSite,opposedAnchor,Bool.false_eq_true,↓reduceIte,
        zero_add,Finset.sum_range_one,ht]
      abel
    · refine ⟨0,0,(hZ true 0).1,?_⟩
      simp only [opposedSite,opposedAnchor,↓reduceIte,Finset.sum_range_zero,add_zero,
        (hZ true 0).2.1]
  refine ⟨hc,⟨-stepVector e,hc,?_⟩⟩
  rw [axisHeight_neg,axisHeight_step_self]
  norm_num

def axisLower {d : ℕ} (e : Step d) (k : ℤ) : Set (Site d) := {y | axisHeight e y < k}
def axisUpper {d : ℕ} (e : Step d) (k : ℤ) : Set (Site d) := {y | k ≤ axisHeight e y}

lemma axis_barriers_disjoint {d : ℕ} (e : Step d) {k N : ℤ} (hkN : k ≤ N) :
    Disjoint (axisLower e k) (axisUpper e N) := by
  apply Set.disjoint_left.mpr
  intro y hy hz
  exact (not_lt_of_ge (hkN.trans hz)) hy

lemma hitBefore_axis_eq_reach {d : ℕ} (e : Step d) (H : ℕ) (X : Path d)
    (h0 : X 0 = 0) (hX : nearestNeighbour X) :
    X ∈ hitBefore (axisUpper e H) (axisLower e 0) ↔ X ∈ reachAxis e H := by
  constructor
  · rintro ⟨n,hn,hb⟩
    obtain ⟨j,hjn,hj,_⟩ := integer_first_crossing (fun i => axisHeight e (X i)) n H
      (fun i _ => axisHeight_nn_le e X hX i) (by simp [h0,axisHeight_zero]) hn
    exact ⟨j,hj,fun i hi => le_of_not_gt (hb i (hi.trans hjn))⟩
  · rintro ⟨n,hn,hb⟩
    exact ⟨n,hn.ge,fun i hi => not_lt_of_ge (hb i hi)⟩

lemma annealed_axis_exit {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d) (x : Site d) (k N : ℤ) :
    ∀ᵐ X ∂annealed μ x, ∃ n, X n ∈ axisLower e k ∪ axisUpper e N := by
  filter_upwards [annealed_exit_band μ hell x (axisDirection e) (axisDirection_ne_zero e)
    (k : ℝ) (N-1 : ℤ)] with X hX
  obtain ⟨n,hn⟩ := hX
  refine ⟨n,?_⟩
  simp only [height_axisDirection,Set.mem_Icc,not_and,not_le] at hn
  change axisHeight e (X n) < k ∨ N ≤ axisHeight e (X n)
  by_cases h : axisHeight e (X n) < k
  · exact Or.inl h
  · right
    have hh := hn (by exact_mod_cast le_of_not_gt h)
    have : N-1 < axisHeight e (X n) := by exact_mod_cast hh
    omega

lemma annealed_axis_return_probability {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d) {r N : ℕ} (hrN : r ≤ N) :
    annealed μ 0 (hitBefore (axisUpper e r) (axisLower e 0) ∩
      hitBefore (axisLower e 0) (axisUpper e N)) = axisReachProb μ e r - axisReachProb μ e N := by
  have hAE := annealed_axis_exit μ hell e 0 0 N
  have hd := hitBefore_disjoint (axisLower e 0) (axisUpper e N)
  have he : (hitBefore (axisUpper e r) (axisLower e 0) ∩
      hitBefore (axisLower e 0) (axisUpper e N) : Set (Path d)) =ᵐ[annealed μ 0]
      (reachAxis e r \ reachAxis e N : Set (Path d)) := by
    filter_upwards [ae_start_and_nearestNeighbour μ 0,hAE] with X hX hx
    have hb : X ∈ hitBefore (axisLower e 0) (axisUpper e N) ∪
        hitBefore (axisUpper e N) (axisLower e 0) := by
      rw [hitBefore_union_eq_eventual _ _ (axis_barriers_disjoint e (by positivity))]
      exact hx
    have h1 := hitBefore_axis_eq_reach e r X hX.1 hX.2
    have h2 := hitBefore_axis_eq_reach e N X hX.1 hX.2
    apply propext
    constructor
    · rintro ⟨ha,hb⟩
      exact ⟨h1.mp ha,fun hc => Set.disjoint_left.mp hd hb (h2.mpr hc)⟩
    · rintro ⟨ha,hc⟩
      exact ⟨h1.mpr ha,hb.resolve_right (fun hh => hc (h2.mp hh))⟩
  have he' : (reachAxis e r ∪ reachAxis e N : Set (Path d)) =ᵐ[annealed μ 0] reachAxis e r := by
    filter_upwards [ae_start_and_nearestNeighbour μ 0] with X hX
    apply propext
    exact ⟨fun h => h.elim id (reachAxis_antitone e X hX.1 hX.2 hrN),Or.inl⟩
  rw [measure_congr he,measure_sdiff' _ (measurableSet_reachAxis e N).nullMeasurableSet
    (measure_ne_top _ _),measure_congr he']
  rfl

lemma annealed_axis_visitAfter_bound {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d) {r N : ℕ} (hrN : r ≤ N)
    (a : ℝ≥0∞) (A : Environment d → Set (Site d))
    (hA : ∀ᵐ ω ∂environmentLaw μ, ∀ y ∈ A ω,
      a ≤ quenchedKernel d (ω,y) (hitBefore (axisLower e 0) (axisUpper e N))) :
    a * (∫⁻ ω, quenchedKernel d (ω,0)
      (visitAfter (axisUpper e r) (A ω) (axisLower e 0 ∪ axisUpper e N)) ∂environmentLaw μ) ≤
      axisReachProb μ e r - axisReachProb μ e N := by
  rw [← annealed_axis_return_probability μ hell e hrN,
    annealed_apply μ 0 ((measurableSet_hitBefore _ _).inter (measurableSet_hitBefore _ _))]
  apply (lintegral_const_mul_le _ _).trans
  apply lintegral_mono_ae
  filter_upwards [hA] with ω hω
  exact quenched_visitAfter_bound ω 0 _ _ _ _ a hω

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

def visits {d : ℕ} (y : Site d) : Set (Path d) := {X | ∃ n, X n = y}

lemma measurableSet_visits {d : ℕ} (y : Site d) : MeasurableSet (visits y) := by
  simp only [visits,Set.ofPred_exists]
  exact MeasurableSet.iUnion (fun n => measurableSet_eq_fun (measurable_pi_apply n) measurable_const)

def contactAvoid {d : ℕ} (a : Word d) : Set (Path d) :=
  visits (wordEnd a) ∩ avoids (wordDepartures a)

lemma measurableSet_contactAvoid {d : ℕ} (a : Word d) : MeasurableSet (contactAvoid a) :=
  (measurableSet_visits _).inter (measurableSet_avoids _)

lemma contactAvoid_iff_firstHit {d : ℕ} (a : Word d) (B : Path d) :
    B ∈ contactAvoid a ↔ firstHitWord (Set.range B) a := by
  constructor
  · rintro ⟨⟨n,hn⟩,hb⟩
    refine ⟨⟨n,hn⟩,fun i hi ⟨j,hj⟩ => ?_⟩
    exact hb j ⟨i,hi,hj.symm⟩
  · rintro ⟨⟨n,hn⟩,hb⟩
    refine ⟨⟨n,hn⟩,fun j ⟨i,hi,he⟩ => ?_⟩
    exact hb i hi ⟨j,he.symm⟩

def contactRectangle {d : ℕ} (a : Word d) : Set (Path d × Path d) :=
  wordCylinder a ×ˢ contactAvoid a

lemma measurableSet_contactRectangle {d : ℕ} (a : Word d) : MeasurableSet (contactRectangle a) :=
  (measurableSet_pathCylinder _ _).prod (measurableSet_contactAvoid a)

lemma contactRectangles_disjoint {d : ℕ} :
    Pairwise (fun a b : Word d => Disjoint (contactRectangle a) (contactRectangle b)) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  rintro ⟨X,B⟩ ⟨ha,hBa⟩ ⟨hb,hBb⟩
  have h1 := (contactAvoid_iff_firstHit a B).mp hBa
  have h2 := (contactAvoid_iff_firstHit b B).mp hBb
  have hd := firstHitWords_prefixFree (Set.range B) (i := ⟨a,h1⟩) (j := ⟨b,h2⟩)
    (fun h => hab (congrArg Subtype.val h))
  exact Set.disjoint_left.mp hd ha hb

lemma annealed_contactRectangle_transfer {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x z : Site d) (a : Word d) (ha : wordPath a 0 = x) {D : Set (Path d)}
    (hD : MeasurableSet D) :
    annealed μ x (wordCylinder a) * annealed μ z (D ∩ contactAvoid a) =
      ∫⁻ ω, ((quenchedKernel d (ω,x)).prod (quenchedKernel d (ω,z)))
        (wordCylinder a ×ˢ (D ∩ contactAvoid a)) ∂environmentLaw μ := by
  have he : D ∩ contactAvoid a = (D ∩ visits (wordEnd a)) ∩ avoids (wordDepartures a) := by
    ext X
    exact and_assoc.symm
  rw [he,wordCylinder,annealed_cylinder,ite_eq_left ha.symm,
    ← word_contact_transfer μ a z (hD.inter (measurableSet_visits _))]
  apply lintegral_congr
  intro ω
  rw [Measure.prod_prod,quenchedKernel_cylinder,ite_eq_left ha.symm]

lemma weighted_contact_transfer {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x z : Site d) (A : Set (Word d)) (hA : ∀ a ∈ A, wordPath a 0 = x)
    (w : Word d → ℝ≥0∞) {D : Set (Path d)} (hD : MeasurableSet D) :
    ∑' a : A, w a * (annealed μ x (wordCylinder a) * annealed μ z (D ∩ contactAvoid a)) =
      ∫⁻ ω, ∑' a : A, w a * (((quenchedKernel d (ω,x)).prod (quenchedKernel d (ω,z)))
        (wordCylinder a ×ˢ (D ∩ contactAvoid a))) ∂environmentLaw μ := by
  simp_rw [annealed_contactRectangle_transfer μ x z _ (hA _ (Subtype.mem _)) hD,
    Measure.prod_prod]
  have hm (a : A) : Measurable (fun ω : Environment d =>
      quenchedKernel d (ω,x) (wordCylinder a) *
        quenchedKernel d (ω,z) (D ∩ contactAvoid a)) :=
    (((quenchedKernel d).measurable_coe (measurableSet_pathCylinder _ _)).comp
      (measurable_id.prodMk measurable_const)).mul
      (((quenchedKernel d).measurable_coe (hD.inter (measurableSet_contactAvoid _))).comp
      (measurable_id.prodMk measurable_const))
  have hwm (a : A) : Measurable (fun ω : Environment d => w a *
      (quenchedKernel d (ω,x) (wordCylinder a) *
        quenchedKernel d (ω,z) (D ∩ contactAvoid a))) := measurable_const.mul (hm a)
  rw [lintegral_tsum (fun a => (hwm a).aemeasurable)]
  apply tsum_congr
  intro a
  exact (lintegral_const_mul (w a) (hm a)).symm

lemma hits_eq_firstHitWords {d : ℕ} (A : Set (Site d)) :
    {X : Path d | ∃ n, X n ∈ A} = ⋃ a : {a | firstHitWord A a}, wordCylinder a.val := by
  classical
  ext X
  constructor
  · intro h
    let n := Nat.find h
    have ha : firstHitWord A (prefixWord n X) := by
      refine ⟨?_,fun i hi => ?_⟩
      · change wordPath (prefixWord n X) n ∈ A
        rw [wordPath_prefixWord n X le_rfl]
        exact Nat.find_spec h
      · rw [wordPath_prefixWord n X hi.le]
        exact Nat.find_min h (show i < Nat.find h from hi)
    exact Set.mem_iUnion.mpr ⟨⟨prefixWord n X,ha⟩,fun i hi => (wordPath_prefixWord n X hi).symm⟩
  · intro h
    obtain ⟨a,ha⟩ := Set.mem_iUnion.mp h
    exact ⟨a.val.1,by rw [ha a.val.1 le_rfl];exact a.property.1⟩

lemma negative_visit_firstWord_subset {d : ℕ} (A B C : Set (Site d)) :
    {X : Path d | (∃ n, X n ∈ A) ∧ (∀ n, ∃ m, n ≤ m ∧ X m ∈ B) ∧ X ∈ avoids C} ⊆
      ⋃ a : {a | firstHitWord A a}, wordCylinder a.val ∩ tailPath a.val.1 ⁻¹' hitBefore B C := by
  rintro X ⟨hA,hB,hC⟩
  obtain ⟨a,ha⟩ := Set.mem_iUnion.mp ((Set.ext_iff.mp (hits_eq_firstHitWords A) X).mp hA)
  obtain ⟨m,hm,hbm⟩ := hB a.val.1
  obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le hm
  refine Set.mem_iUnion.mpr ⟨a,ha,j,?_,fun i _ => ?_⟩
  · simpa only [tailPath,← hj] using hbm
  · exact hC (a.val.1+i)

lemma quenched_negative_visit_bound {d : ℕ} (ω : Environment d) (x : Site d)
    (A B C : Set (Site d)) (c : ℝ≥0∞)
    (hc : ∀ y ∈ A, quenchedKernel d (ω,y) (hitBefore B C) ≤ c) :
    quenchedKernel d (ω,x)
      {X | (∃ n, X n ∈ A) ∧ (∀ n, ∃ m, n ≤ m ∧ X m ∈ B) ∧ X ∈ avoids C} ≤ c := by
  apply (measure_mono (negative_visit_firstWord_subset A B C)).trans
  rw [quenched_prefix_family ω x _ (firstHitWords_prefixFree _) (fun _ => hitBefore B C)
    (fun _ _ => measurableSet_hitBefore _ _)]
  calc
    ∑' a : {a | firstHitWord A a}, quenchedKernel d (ω,x) (wordCylinder a) *
        quenchedKernel d (ω,wordEnd a) (hitBefore B C) ≤
      ∑' a : {a | firstHitWord A a}, c * quenchedKernel d (ω,x) (wordCylinder a) := by
        apply ENNReal.tsum_le_tsum
        intro a
        rw [mul_comm c]
        exact mul_le_mul_right (hc _ a.property.1) _
    _ = c * quenchedKernel d (ω,x) (⋃ a : {a | firstHitWord A a}, wordCylinder a.val) := by
      rw [ENNReal.tsum_mul_left,measure_iUnion (firstHitWords_prefixFree A)
        (fun _ => measurableSet_pathCylinder _ _)]
    _ ≤ c := by
      simpa only [mul_one] using mul_le_mul_right (prob_le_one
        (μ := quenchedKernel d (ω,x))) c

def lateVisits {d : ℕ} (A : Set (Site d)) : Set (Path d) :=
  {X | ∀ n, ∃ m, n ≤ m ∧ X m ∈ A}

lemma measurableSet_lateVisits {d : ℕ} (A : Set (Site d)) : MeasurableSet (lateVisits A) := by
  simp only [lateVisits,Set.ofPred_forall,Set.ofPred_exists,Set.ofPred_and]
  apply MeasurableSet.iInter
  intro n
  apply MeasurableSet.iUnion
  intro m
  exact (MeasurableSet.const _).inter ((Set.to_countable A).measurableSet.preimage (measurable_pi_apply m))

lemma annealed_avoidsUpper_lateLower {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d) (x : Site d) (k N : ℤ) :
    ∀ᵐ X ∂annealed μ x, X ∈ avoids (axisUpper e N) → X ∈ lateVisits (axisLower e k) := by
  filter_upwards [finite_supremum μ hell x (axisDirection e) (axisDirection_ne_zero e)] with X hX
  intro hD
  have hbound : ∃ b, ∀ n, height (axisDirection e) (X n) ≤ b := by
    refine ⟨(N : ℝ),fun n => ?_⟩
    have hn : axisHeight e (X n) < N := lt_of_not_ge (hD n)
    rw [height_axisDirection]
    exact_mod_cast hn.le
  have ht := tendsto_atBot.mp (hX hbound) ((k-1 : ℤ) : ℝ)
  obtain ⟨m,hm⟩ := eventually_atTop.mp ht
  intro n
  refine ⟨max m n,le_max_right _ _,?_⟩
  have he := hm (max m n) (le_max_left _ _)
  rw [height_axisDirection] at he
  have hh : axisHeight e (X (max m n)) ≤ k-1 := by exact_mod_cast he
  change axisHeight e (X (max m n)) < k
  omega

lemma quenched_negative_bins {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d) :
    ∀ᵐ ω ∂environmentLaw μ, ∀ (x : Site d) (k N : ℤ) (K : Set (Site d)) (c : ℝ≥0∞),
      (∀ y ∈ K, quenchedKernel d (ω,y) (hitBefore (axisLower e k) (axisUpper e N)) ≤ c) →
      quenchedKernel d (ω,x) (avoids (axisUpper e N) ∩ {B | ∃ n, B n ∈ K}) ≤ c := by
  have hAE : ∀ᵐ ω ∂environmentLaw μ, ∀ (x : Site d) (k N : ℤ),
      ∀ᵐ X ∂quenchedKernel d (ω,x),
        X ∈ avoids (axisUpper e N) → X ∈ lateVisits (axisLower e k) := by
    simp only [ae_all_iff]
    intro x k N
    apply annealed_ae_quenched μ x
    · simp only [imp_iff_not_or]
      exact (measurableSet_avoids _).compl.union (measurableSet_lateVisits _)
    · exact annealed_avoidsUpper_lateLower μ hell e x k N
  filter_upwards [hAE] with ω hω
  intro x k N K c hc
  apply (measure_mono_ae (show (avoids (axisUpper e N) ∩ {B | ∃ n, B n ∈ K} : Set (Path d)) ≤ᵐ[quenchedKernel d (ω,x)]
    {X | (∃ n, X n ∈ K) ∧ (∀ n, ∃ m, n ≤ m ∧ X m ∈ axisLower e k) ∧ X ∈ avoids (axisUpper e N)} from ?_)).trans
    (quenched_negative_visit_bound ω x K (axisLower e k) (axisUpper e N) c hc)
  filter_upwards [hω x k N] with X hX
  exact fun h => ⟨h.2,hX h.1,h.1⟩

lemma weighted_disjoint_measure_bound {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (μ : Measure Ω) (s : ι → Set Ω) (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (fun i j => Disjoint (s i) (s j))) (w : ι → ℝ≥0∞) (F : Ω → ℝ≥0∞)
    (E : Set Ω) (hsub : ∀ i, s i ⊆ E) (hbound : ∀ i, ∀ ω ∈ s i, w i ≤ F ω) :
    ∑' i, w i * μ (s i) ≤ ∫⁻ ω in E, F ω ∂μ := by
  calc
    ∑' i, w i * μ (s i) ≤ ∑' i, ∫⁻ ω in s i, F ω ∂μ := by
      apply ENNReal.tsum_le_tsum
      intro i
      rw [← setLIntegral_const]
      apply setLIntegral_mono' (hs i)
      exact hbound i
    _ = ∫⁻ ω in ⋃ i, s i, F ω ∂μ := (lintegral_iUnion hs hd F).symm
    _ ≤ _ := lintegral_mono_set (Set.iUnion_subset hsub)

lemma weighted_contact_bin_bound {d : ℕ} (P Q : Measure (Path d)) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (A : Set (Word d)) (D V : Set (Path d)) (K : Set (Site d))
    (hD : MeasurableSet D) (w : Word d → ℝ≥0∞) (M : Path d → ℝ≥0∞)
    (hM : Measurable M) (hA : ∀ a ∈ A, wordEnd a ∈ K)
    (hAV : ∀ a ∈ A, wordCylinder a ⊆ V)
    (hw : ∀ a ∈ A, ∀ X ∈ wordCylinder a, w a ≤ M X) (c : ℝ≥0∞)
    (hc : Q (D ∩ {B | ∃ n, B n ∈ K}) ≤ c) :
    ∑' a : A, w a * (P (wordCylinder a) * Q (D ∩ contactAvoid a)) ≤
      c * ∫⁻ X in V, M X ∂P := by
  let R : Set (Path d) := D ∩ {B | ∃ n, B n ∈ K}
  have hR : MeasurableSet R := hD.inter (by
    simp only [Set.ofPred_exists]
    exact MeasurableSet.iUnion (fun n => (Set.to_countable K).measurableSet.preimage (measurable_pi_apply n)))
  have hs (a : A) : MeasurableSet (wordCylinder a.val ×ˢ (D ∩ contactAvoid a.val)) :=
    (measurableSet_pathCylinder _ _).prod (hD.inter (measurableSet_contactAvoid _))
  have hd : Pairwise (fun a b : A => Disjoint
      (wordCylinder a.val ×ˢ (D ∩ contactAvoid a.val))
      (wordCylinder b.val ×ˢ (D ∩ contactAvoid b.val))) := by
    intro a b hab
    apply (contactRectangles_disjoint (i := a.val) (j := b.val) (fun h => hab (Subtype.ext h))).mono
    · exact fun _ h => ⟨h.1,h.2.2⟩
    · exact fun _ h => ⟨h.1,h.2.2⟩
  have hsub (a : A) : wordCylinder a.val ×ˢ (D ∩ contactAvoid a.val) ⊆ V ×ˢ R := by
    rintro ⟨X,B⟩ ⟨hX,hB⟩
    obtain ⟨n,hn⟩ := hB.2.1
    exact ⟨hAV _ a.property hX,hB.1,n,hn ▸ hA _ a.property⟩
  have h := weighted_disjoint_measure_bound (P.prod Q)
    (fun a : A => wordCylinder a.val ×ˢ (D ∩ contactAvoid a.val)) hs hd
    (fun a => w a) (fun p => M p.1) (V ×ˢ R) hsub
    (fun a _ h => hw a a.property _ h.1)
  simp only [Measure.prod_prod] at h
  apply h.trans
  rw [setLIntegral_prod (fun p : Path d × Path d => M p.1) (hM.comp measurable_fst).aemeasurable.restrict]
  simp only [setLIntegral_const]
  rw [lintegral_mul_const _ hM]
  rw [mul_comm]
  exact mul_le_mul_left hc _

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

open scoped Classical

noncomputable def firstVisitIndex {d : ℕ} (K : Set (Site d)) (X : Path d) : ℕ :=
  if h : ∃ n, X n ∈ K then Nat.find h else 0

lemma firstVisitIndex_eq {d : ℕ} (K : Set (Site d)) (X : Path d) (h : ∃ n, X n ∈ K) :
    firstVisitIndex K X = Nat.find h := by simp only [firstVisitIndex,dite_eq_left h]

lemma firstVisitIndex_fiber {d : ℕ} (K : Set (Site d)) (n : ℕ) :
    {X : Path d | firstVisitIndex K X = n} =
      {X | X n ∈ K ∧ ∀ i < n, X i ∉ K} ∪ {X | n = 0 ∧ ¬∃ i, X i ∈ K} := by
  classical
  ext X
  change firstVisitIndex K X = n ↔ (X n ∈ K ∧ ∀ i < n, X i ∉ K) ∨ (n = 0 ∧ ¬∃ i, X i ∈ K)
  by_cases h : ∃ i, X i ∈ K
  · rw [firstVisitIndex,dite_eq_left h]
    simp only [h,not_true_eq_false,and_false,or_false]
    exact Nat.find_eq_iff h
  · have hn : X n ∉ K := fun hn => h ⟨n,hn⟩
    rw [firstVisitIndex,dite_eq_right h]
    simp only [hn,h,false_and,
      not_false_eq_true,and_true,false_or,eq_comm]

lemma measurable_firstVisitIndex {d : ℕ} (K : Set (Site d)) : Measurable (firstVisitIndex K) := by
  apply measurable_to_countable'
  intro n
  change MeasurableSet {X : Path d | firstVisitIndex K X = n}
  rw [firstVisitIndex_fiber]
  have hi (i : ℕ) : MeasurableSet {X : Path d | X i ∈ K} :=
    (Set.to_countable K).measurableSet.preimage (measurable_pi_apply i)
  have hp : MeasurableSet {X : Path d | ∀ i < n, X i ∉ K} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun _ => (hi i).compl))
  have hno : MeasurableSet {X : Path d | ¬∃ i, X i ∈ K} := by
    change MeasurableSet ({X : Path d | ∃ i, X i ∈ K}ᶜ)
    simp only [Set.ofPred_exists]
    exact (MeasurableSet.iUnion hi).compl
  exact ((hi n).inter hp).union ((MeasurableSet.const _).inter hno)

noncomputable def firstVisitWord {d : ℕ} (K : Set (Site d)) (X : Path d) : Word d :=
  prefixWord (firstVisitIndex K X) X

lemma measurable_firstVisitWord {d : ℕ} (K : Set (Site d)) : Measurable (firstVisitWord K) := by
  exact (measurable_from_prod_countable_right (f := fun (p : ℕ × Path d) => prefixWord p.1 p.2) (fun n => measurable_prefixWord n)).comp
    ((measurable_firstVisitIndex K).prodMk measurable_id)

lemma firstVisitWord_spec {d : ℕ} (K : Set (Site d)) (X : Path d) (h : ∃ n, X n ∈ K) :
    firstHitWord K (firstVisitWord K X) ∧ X ∈ wordCylinder (firstVisitWord K X) := by
  classical
  have he := firstVisitIndex_eq K X h
  refine ⟨⟨?_,fun i hi => ?_⟩,fun i hi => ?_⟩
  · change wordPath (prefixWord (firstVisitIndex K X) X) (firstVisitIndex K X) ∈ K
    rw [wordPath_prefixWord _ _ le_rfl,he]
    exact Nat.find_spec h
  · change wordPath (prefixWord (firstVisitIndex K X) X) i ∉ K
    rw [wordPath_prefixWord _ _ (show i ≤ firstVisitIndex K X from hi.le)]
    exact Nat.find_min h (he ▸ (show i < firstVisitIndex K X from hi))
  · exact (wordPath_prefixWord _ _ hi).symm

lemma firstVisitWord_eq_of_cylinder {d : ℕ} (K : Set (Site d)) (a : Word d)
    (ha : firstHitWord K a) (X : Path d) (hX : X ∈ wordCylinder a) :
    firstVisitWord K X = a := by
  have hex : ∃ n, X n ∈ K := ⟨a.1,by rw [hX _ le_rfl];exact ha.1⟩
  have hs := firstVisitWord_spec K X hex
  by_contra hne
  exact Set.disjoint_left.mp (firstHitWords_prefixFree K
    (i := ⟨firstVisitWord K X,hs.1⟩) (j := ⟨a,ha⟩) (fun h => hne (congrArg Subtype.val h))) hs.2 hX

lemma firstVisitWord_fiber_ae {d : ℕ} (P : Measure (Path d)) (K : Set (Site d))
    (hP : ∀ᵐ X ∂P, ∃ n, X n ∈ K) (a : Word d) :
    (firstVisitWord K ⁻¹' {a} : Set (Path d)) =ᵐ[P]
      (if firstHitWord K a then wordCylinder a else ∅ : Set (Path d)) := by
  classical
  filter_upwards [hP] with X hX
  have hs := firstVisitWord_spec K X hX
  by_cases ha : firstHitWord K a
  · rw [ite_eq_left ha]
    apply propext
    change firstVisitWord K X = a ↔ X ∈ wordCylinder a
    exact ⟨fun he => he ▸ hs.2,firstVisitWord_eq_of_cylinder K a ha X⟩
  · rw [ite_eq_right ha]
    apply propext
    change firstVisitWord K X = a ↔ False
    exact ⟨fun he => ha (he ▸ hs.1),False.elim⟩

lemma firstVisitWord_map_eq {d : ℕ} (P Q : Measure (Path d)) (K : Set (Site d))
    (hP : ∀ᵐ X ∂P, ∃ n, X n ∈ K) (hQ : ∀ᵐ X ∂Q, ∃ n, X n ∈ K)
    (h : ∀ a, firstHitWord K a → P (wordCylinder a) = Q (wordCylinder a)) :
    P.map (firstVisitWord K) = Q.map (firstVisitWord K) := by
  classical
  apply Measure.ext_of_singleton
  intro a
  rw [Measure.map_apply (measurable_firstVisitWord K) (measurableSet_singleton a),
    Measure.map_apply (measurable_firstVisitWord K) (measurableSet_singleton a),
    measure_congr (firstVisitWord_fiber_ae P K hP a),measure_congr (firstVisitWord_fiber_ae Q K hQ a)]
  by_cases ha : firstHitWord K a
  · simp only [ite_eq_left ha];exact h a ha
  · simp only [ite_eq_right ha,measure_empty]

noncomputable def continuationLaw {d : ℕ} (P : Measure (Path d)) (a : Word d) : Measure (Path d) :=
  (ProbabilityTheory.cond P (wordCylinder a)).map (tailPath a.1)

lemma continuationLaw_probability {d : ℕ} (P : Measure (Path d)) [IsProbabilityMeasure P]
    (a : Word d) (ha : P (wordCylinder a) ≠ 0) : IsProbabilityMeasure (continuationLaw P a) := by
  let := ProbabilityTheory.cond_isProbabilityMeasure (μ := P) ha
  exact probabilityMeasure_map (measurable_tailPath a.1).aemeasurable

lemma annealed_disjoint_prefix_tail' {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x : Site d) (n m : ℕ) (γ δ : Path d)
    (hdis : ∀ i < n, ∀ j < m, γ i ≠ δ j) :
    annealed μ x (pathCylinder n γ ∩ tailPath n ⁻¹' pathCylinder m δ) =
      annealed μ x (pathCylinder n γ) * annealed μ (γ n) (pathCylinder m δ) := by
  classical
  by_cases hjoin : γ n = δ 0
  · exact annealed_disjoint_prefix_tail μ x n m γ δ hjoin hdis
  · have he : pathCylinder n γ ∩ tailPath n ⁻¹' pathCylinder m δ = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro X ⟨hX,hY⟩
      exact hjoin ((hX n le_rfl).symm.trans (by simpa only [tailPath,Nat.add_zero] using hY 0 (Nat.zero_le m)))
    rw [he,measure_empty,annealed_cylinder μ (γ n) m δ,ite_eq_right hjoin,mul_zero]

lemma continuationLaw_fresh_cylinder {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x : Site d) (a b : Word d) (ha : annealed μ x (wordCylinder a) ≠ 0)
    (hdis : Disjoint (wordDepartures a) (wordDepartures b)) :
    continuationLaw (annealed μ x) a (wordCylinder b) = annealed μ (wordEnd a) (wordCylinder b) := by
  dsimp only [continuationLaw,wordCylinder]
  rw [Measure.map_apply (measurable_tailPath a.1) (measurableSet_pathCylinder _ _),
    ProbabilityTheory.cond_apply (measurableSet_pathCylinder _ _) _ _]
  rw [annealed_disjoint_prefix_tail' μ x a.1 b.1 (wordPath a) (wordPath b) (by
    intro i hi j hj he
    exact Set.disjoint_left.mp hdis ⟨i,hi,rfl⟩ ⟨j,hj,he.symm⟩)]
  change (annealed μ x (wordCylinder a))⁻¹ * (annealed μ x (wordCylinder a) *
    annealed μ (wordEnd a) (wordCylinder b)) = _
  rw [← mul_assoc,ENNReal.inv_mul_cancel ha (measure_ne_top _ _),one_mul]
  rfl

lemma firstHitWords_full_of_cylinder_eq {d : ℕ} (P Q : Measure (Path d))
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (K : Set (Site d))
    (hQ : ∀ᵐ X ∂Q, ∃ n, X n ∈ K)
    (h : ∀ a, firstHitWord K a → P (wordCylinder a) = Q (wordCylinder a)) :
    ∀ᵐ X ∂P, ∃ n, X n ∈ K := by
  have hm : MeasurableSet {X : Path d | ∃ n, X n ∈ K} := by
    rw [hits_eq_firstHitWords]
    exact MeasurableSet.iUnion (fun _ => measurableSet_pathCylinder _ _)
  have he : P {X | ∃ n, X n ∈ K} = Q {X | ∃ n, X n ∈ K} := by
    rw [hits_eq_firstHitWords,measure_iUnion (firstHitWords_prefixFree K)
      (fun _ => measurableSet_pathCylinder _ _),measure_iUnion (firstHitWords_prefixFree K)
      (fun _ => measurableSet_pathCylinder _ _)]
    exact tsum_congr (fun a => h a a.property)
  have hq : Q {X | ∃ n, X n ∈ K} = 1 := by
    rw [← measure_univ (μ := Q)]
    exact measure_congr (by filter_upwards [hQ] with X hX;exact propext ⟨fun _ => trivial,fun _ => hX⟩)
  rw [ae_iff]
  change P ({X | ∃ n, X n ∈ K}ᶜ) = 0
  rw [measure_compl hm (measure_ne_top _ _),he,hq,measure_univ,tsub_self]

lemma continuationLaw_fresh_stopped {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x : Site d) (a : Word d) (K : Set (Site d)) (ha : annealed μ x (wordCylinder a) ≠ 0)
    (hdep : wordDepartures a ⊆ K)
    (hex : ∀ᵐ X ∂annealed μ (wordEnd a), ∃ n, X n ∈ K) :
    (continuationLaw (annealed μ x) a).map (firstVisitWord K) =
      (annealed μ (wordEnd a)).map (firstVisitWord K) := by
  have := continuationLaw_probability (annealed μ x) a ha
  have he (b : Word d) (hb : firstHitWord K b) :
      continuationLaw (annealed μ x) a (wordCylinder b) = annealed μ (wordEnd a) (wordCylinder b) := by
    apply continuationLaw_fresh_cylinder μ x a b ha
    apply Set.disjoint_left.mpr
    rintro y hy ⟨j,hj,rfl⟩
    exact hb.2 j hj (hdep hy)
  exact firstVisitWord_map_eq _ _ K (firstHitWords_full_of_cylinder_eq _ _ K hex he) hex he

noncomputable def wordPosterior {d ι : ℕ} (P : Measure (Path d))
    (E : Fin ι → Set (Path d)) (e : Fin ι) (a : Word d) : ℝ :=
  P.real (E e ∩ wordCylinder a) / P.real (wordCylinder a)

noncomputable def endpointPosterior {d ι : ℕ} (P : Measure (Path d))
    (E : Fin ι → Set (Path d)) (e : Fin ι) (n : ℕ) (X : Path d) : ℝ :=
  wordPosterior P E e (prefixWord n X)

lemma wordCylinder_prefixWord {d : ℕ} (n : ℕ) (X : Path d) :
    wordCylinder (prefixWord n X) = pathCylinder n X := by
  ext Y
  constructor
  · intro h i hi
    exact (h i hi).trans (wordPath_prefixWord n X hi)
  · intro h i hi
    exact (h i hi).trans (wordPath_prefixWord n X hi).symm

lemma endpointPosterior_eq_ratio {d ι : ℕ} (P : Measure (Path d))
    (E : Fin ι → Set (Path d)) (e : Fin ι) (n : ℕ) (X : Path d) :
    endpointPosterior P E e n X = P.real (E e ∩ pathCylinder n X) / P.real (pathCylinder n X) := by
  simp only [endpointPosterior,wordPosterior,wordCylinder_prefixWord]

lemma measurable_prefixWord_filtration {d : ℕ} (n : ℕ) :
    Measurable[pathFiltration d n] (prefixWord (d := d) n) := by
  rw [pathFiltration_eq]
  exact (measurable_of_countable (fun a : Finset.Iic n → Site d => (⟨n,a⟩ : Word d))).comp
    (Measurable.of_comap_le le_rfl)

lemma endpointPosterior_adapted {d ι : ℕ} (P : Measure (Path d)) (E : Fin ι → Set (Path d))
    (e : Fin ι) (n : ℕ) : StronglyMeasurable[pathFiltration d n] (endpointPosterior P E e n) :=
  ((measurable_of_countable (wordPosterior P E e)).comp (measurable_prefixWord_filtration n)).stronglyMeasurable

lemma endpointPosterior_condExp {d ι : ℕ} (P : Measure (Path d)) [IsFiniteMeasure P]
    (E : Fin ι → Set (Path d)) (hE : ∀ e, MeasurableSet (E e)) (e : Fin ι) (n : ℕ) :
    P[(E e).indicator (fun _ => (1 : ℝ)) | pathFiltration d n] =ᵐ[P] endpointPosterior P E e n := by
  filter_upwards [ae_pathCylinder_ne_zero P] with X hX
  rw [endpointPosterior_eq_ratio]
  have hp : P.real (pathCylinder n X) ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨hX n,measure_ne_top _ _⟩
  apply (eq_div_iff hp).mpr
  simpa only [mul_comm] using condExp_indicator_cylinder P (hE e) n X

lemma endpointPosterior_martingale {d ι : ℕ} (P : Measure (Path d)) [IsFiniteMeasure P]
    (E : Fin ι → Set (Path d)) (hE : ∀ e, MeasurableSet (E e)) (e : Fin ι) :
    Martingale (endpointPosterior P E e) (pathFiltration d) P := by
  apply (martingale_condExp ((E e).indicator (fun _ => (1 : ℝ))) (pathFiltration d) P).congr
  · exact endpointPosterior_adapted P E e
  · exact endpointPosterior_condExp P E hE e

lemma wordPosterior_bounds {d ι : ℕ} (P : Measure (Path d)) [IsFiniteMeasure P]
    (E : Fin ι → Set (Path d)) (hE : ∀ e, MeasurableSet (E e))
    (hdis : Pairwise (fun i j => Disjoint (E i) (E j))) (a : Word d) :
    (∀ e, 0 ≤ wordPosterior P E e a) ∧ ∑ e, wordPosterior P E e a ≤ 1 := by
  constructor
  · exact fun _ => div_nonneg measureReal_nonneg measureReal_nonneg
  · unfold wordPosterior
    rw [← Finset.sum_div]
    by_cases hp : P.real (wordCylinder a) = 0
    · simp only [hp,div_zero];norm_num
    · have hp0 : 0 < P.real (wordCylinder a) := lt_of_le_of_ne measureReal_nonneg (Ne.symm hp)
      apply (div_le_one hp0).mpr
      rw [← measureReal_iUnion_fintype (μ := P) (f := fun i => E i ∩ wordCylinder a) (fun i j hij => (hdis hij).mono Set.inter_subset_left Set.inter_subset_left)
        (fun i => (hE i).inter (measurableSet_pathCylinder _ _)) (fun _ => measure_ne_top _ _)]
      exact measureReal_mono (Set.iUnion_subset (fun _ => Set.inter_subset_right)) (measure_ne_top _ _)

lemma endpointPosterior_bounds {d ι : ℕ} (P : Measure (Path d)) [IsFiniteMeasure P]
    (E : Fin ι → Set (Path d)) (hE : ∀ e, MeasurableSet (E e))
    (hdis : Pairwise (fun i j => Disjoint (E i) (E j))) :
    (∀ e n X, 0 ≤ endpointPosterior P E e n X) ∧
    (∀ n X, ∑ e, endpointPosterior P E e n X ≤ 1) :=
  ⟨fun e n X => (wordPosterior_bounds P E hE hdis (prefixWord n X)).1 e,
    fun n X => (wordPosterior_bounds P E hE hdis (prefixWord n X)).2⟩

lemma endpointPosterior_prefix {d ι : ℕ} (P : Measure (Path d))
    (E : Fin ι → Set (Path d)) (e : Fin ι) (a : Word d) (X : Path d)
    (hX : X ∈ wordCylinder a) {j : ℕ} (hj : j ≤ a.1) :
    endpointPosterior P E e j X = endpointPosterior P E e j (wordPath a) := by
  unfold endpointPosterior
  rw [prefixWord_of_wordCylinder a X hX j hj]

noncomputable def wordEndpointMax {d ι : ℕ} (P : Measure (Path d))
    (E : Fin ι → Set (Path d)) (a : Word d) : ℝ :=
  posteriorMax (endpointPosterior P E) a.1 (wordPath a)

lemma wordEndpointMax_prefixWord {d ι : ℕ} (P : Measure (Path d))
    (E : Fin ι → Set (Path d)) (n : ℕ) (X : Path d) :
    wordEndpointMax P E (prefixWord n X) = posteriorMax (endpointPosterior P E) n X := by
  classical
  unfold wordEndpointMax posteriorMax
  apply Finset.sum_congr rfl
  intro e _
  unfold runningMax
  apply Finset.sup'_congr _ rfl
  intro j hj
  exact (endpointPosterior_prefix P E e (prefixWord n X) X
    (by intro i hi;exact (wordPath_prefixWord n X hi).symm)
    (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).symm

lemma wordEndpointMax_bounds {d ι : ℕ} (P : Measure (Path d)) [IsFiniteMeasure P]
    (E : Fin ι → Set (Path d)) (hE : ∀ e, MeasurableSet (E e))
    (hdis : Pairwise (fun i j => Disjoint (E i) (E j))) (a : Word d) :
    0 ≤ wordEndpointMax P E a ∧ wordEndpointMax P E a ≤ ι := by
  have hb := endpointPosterior_bounds P E hE hdis
  exact ⟨posteriorMax_nonneg _ hb.1 _ _,by simpa only [wordEndpointMax,Fintype.card_fin] using posteriorMax_le_card _ hb.1 hb.2 a.1 (wordPath a)⟩

lemma stoppedEndpointMax_le {d ι : ℕ} (P : Measure (Path d)) [IsFiniteMeasure P]
    (E : Fin ι → Set (Path d)) (hE : ∀ e, MeasurableSet (E e))
    (hdis : Pairwise (fun i j => Disjoint (E i) (E j))) (K : Set (Site d)) (X : Path d) :
    wordEndpointMax P E (firstVisitWord K X) ≤ posteriorSup (endpointPosterior P E) X := by
  rw [firstVisitWord,wordEndpointMax_prefixWord]
  have hb := endpointPosterior_bounds P E hE hdis
  have hba : BddAbove (Set.range (fun n => posteriorMax (endpointPosterior P E) n X)) :=
    ⟨(ι : ℝ),by rintro _ ⟨n,rfl⟩;simpa only [Fintype.card_fin] using posteriorMax_le_card _ hb.1 hb.2 n X⟩
  exact le_ciSup hba _

lemma stoppedEndpointMax_exponential {d ι : ℕ} [NeZero ι]
    (P Q : Measure (Path d)) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (E : Fin ι → Set (Path d)) (hE : ∀ e, MeasurableSet (E e))
    (hdis : Pairwise (fun i j => Disjoint (E i) (E j))) (K : Set (Site d))
    (he : P.map (firstVisitWord K) = Q.map (firstVisitWord K)) :
    (∫ X, Real.exp (posteriorExponent / Real.log (ι+1) * wordEndpointMax P E (firstVisitWord K X)) ∂Q) ≤ 12 := by
  let c := posteriorExponent / Real.log (ι+1)
  have hc : 0 ≤ c := (div_pos posteriorExponent_pos
    (Real.log_pos (by exact_mod_cast (show 1 < ι+1 by have := NeZero.pos ι;omega)))).le
  have hf : Measurable (fun X => wordEndpointMax P E (firstVisitWord K X)) :=
    (measurable_of_countable (wordEndpointMax P E)).comp (measurable_firstVisitWord K)
  have hi : (∫ X, Real.exp (c * wordEndpointMax P E (firstVisitWord K X)) ∂Q) =
      ∫ X, Real.exp (c * wordEndpointMax P E (firstVisitWord K X)) ∂P := by
    have hsm := (measurable_of_countable (fun a : Word d => Real.exp (c*wordEndpointMax P E a))).stronglyMeasurable
    rw [← integral_map_of_stronglyMeasurable (measurable_firstVisitWord K) hsm,
      ← integral_map_of_stronglyMeasurable (measurable_firstVisitWord K) hsm,he]
  rw [show posteriorExponent / Real.log (↑ι+1) = c from rfl,hi]
  have hw := endpointPosterior_martingale P E hE
  have hb := endpointPosterior_bounds P E hE hdis
  apply (integral_mono (integrable_exp_of_bound P _ hf ι c (fun X => (wordEndpointMax_bounds P E hE hdis _).2) hc)
    (integrable_exp_of_bound P _ (measurable_posteriorSup P (pathFiltration d) _ hw) ι c
      (fun X => by simpa using (posteriorSup_bounds _ hb.1 hb.2 X).2) hc)
    (fun X => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (stoppedEndpointMax_le P E hE hdis K X) hc))).trans
  simpa only [Fintype.card_fin] using posteriorSup_exponential_log P (pathFiltration d) _ hw hb.1 hb.2

lemma stoppedEndpointMax_joint_weight {d ι : ℕ} [NeZero ι]
    {Ξ : Type*} [MeasurableSpace Ξ] (P Q : Measure (Path d))
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (E : Fin ι → Set (Path d)) (hE : ∀ e, MeasurableSet (E e))
    (hdis : Pairwise (fun i j => Disjoint (E i) (E j))) (K : Set (Site d))
    (he : P.map (firstVisitWord K) = Q.map (firstVisitWord K))
    (ν : Measure Ξ) [IsProbabilityMeasure ν] (π : Ξ → Path d) (hπ : MeasurePreserving π ν Q)
    (V : Set Ξ) :
    (∫ ξ in V, wordEndpointMax P E (firstVisitWord K (π ξ)) ∂ν) ≤
      (12/posteriorExponent) * Real.log (ι+1) * ν.real V * (1-Real.log (ν.real V)) := by
  let c := posteriorExponent / Real.log (ι+1)
  let f := fun X => wordEndpointMax P E (firstVisitWord K X)
  have hc : 0 < c := div_pos posteriorExponent_pos
    (Real.log_pos (by exact_mod_cast (show 1 < ι+1 by have := NeZero.pos ι;omega)))
  have hm : Measurable f := (measurable_of_countable (wordEndpointMax P E)).comp (measurable_firstVisitWord K)
  have hib : Integrable f Q := (integrable_const (ι : ℝ)).mono' hm.aestronglyMeasurable (by
    filter_upwards [] with X
    rw [Real.norm_eq_abs,abs_of_nonneg (wordEndpointMax_bounds P E hE hdis _).1]
    exact (wordEndpointMax_bounds P E hE hdis _).2)
  have hie := integrable_exp_of_bound Q f hm ι c (fun X => (wordEndpointMax_bounds P E hE hdis _).2) hc.le
  have hex : (∫ ξ, Real.exp (c*f (π ξ)) ∂ν) ≤ 12 := by
    have hi : (∫ ξ, Real.exp (c*f (π ξ)) ∂ν) = ∫ X, Real.exp (c*f X) ∂Q := by
      rw [← hπ.map_eq]
      exact (integral_map_of_stronglyMeasurable hπ.measurable (hm.const_mul c).exp.stronglyMeasurable).symm
    rw [hi]
    exact stoppedEndpointMax_exponential P Q E hE hdis K he
  have hi := setIntegral_entropy_of_exp ν (fun ξ => f (π ξ))
    (hπ.integrable_comp_of_integrable hib) c hc (hπ.integrable_comp_of_integrable hie) hex V
  have hs : 12/c = (12/posteriorExponent)*Real.log (ι+1) := by dsimp [c];field_simp
  simpa only [hs] using hi

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

noncomputable def freshPathKernel {d : ℕ} (x : Site d) : Kernel (Environment d) (Path d) :=
  (quenchedKernel d).comap (fun ω => (ω,x)) (measurable_id.prodMk measurable_const)

instance {d : ℕ} (x : Site d) : IsMarkovKernel (freshPathKernel x) := by
  unfold freshPathKernel
  infer_instance

noncomputable def freshJoint {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x : Site d) : Measure (Environment d × Path d) :=
  environmentLaw μ ⊗ₘ freshPathKernel x

instance {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ] (x : Site d) :
    IsProbabilityMeasure (freshJoint μ x) := by
  unfold freshJoint
  infer_instance

lemma freshJoint_apply {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ] (x : Site d)
    {A : Set (Environment d × Path d)} (hA : MeasurableSet A) :
    freshJoint μ x A = ∫⁻ ω, quenchedKernel d (ω,x) (Prod.mk ω ⁻¹' A) ∂environmentLaw μ := by
  rw [freshJoint,Measure.compProd_apply hA]
  rfl

lemma freshJoint_path_marginal {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ] (x : Site d) :
    MeasurePreserving Prod.snd (freshJoint μ x) (annealed μ x) := by
  refine ⟨measurable_snd,?_⟩
  ext A hA
  rw [Measure.map_apply measurable_snd hA,freshJoint_apply μ x (hA.preimage measurable_snd),annealed_apply μ x hA]
  rfl

lemma freshJoint_lintegral {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ] (x : Site d)
    (f : Environment d × Path d → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ξ, f ξ ∂freshJoint μ x) =
      ∫⁻ ω, ∫⁻ X, f (ω,X) ∂quenchedKernel d (ω,x) ∂environmentLaw μ := by
  rw [freshJoint,Measure.lintegral_compProd hf]
  rfl

lemma measurable_random_visitAfter {d : ℕ} (R K : Set (Site d)) (A : Environment d → Set (Site d))
    (hA : ∀ y, MeasurableSet {ω | y ∈ A ω}) :
    MeasurableSet {ξ : Environment d × Path d | ξ.2 ∈ visitAfter R (A ξ.1) K} := by
  have he : {ξ : Environment d × Path d | ξ.2 ∈ visitAfter R (A ξ.1) K} =
      ⋃ y : Site d, {ξ | y ∈ A ξ.1} ∩ {ξ | ξ.2 ∈ visitAfter R {y} K} := by
    ext ⟨ω,X⟩
    simp only [Set.mem_iUnion,Set.mem_inter_iff,Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n,hAn,hR,hK⟩
      exact ⟨X n,hAn,n,rfl,hR,hK⟩
    · rintro ⟨y,hy,n,hAn,hR,hK⟩
      exact ⟨n,hAn ▸ hy,hR,hK⟩
  rw [he]
  exact MeasurableSet.iUnion (fun y => ((hA y).preimage measurable_fst).inter
    ((measurableSet_visitAfter R {y} K).preimage measurable_snd))

noncomputable def quenchedReturn {d : ℕ} (e : Step d) (k N : ℤ)
    (ω : Environment d) (y : Site d) : ℝ≥0∞ :=
  quenchedKernel d (ω,y) (hitBefore (axisLower e k) (axisUpper e N))

lemma measurable_quenchedReturn {d : ℕ} (e : Step d) (k N : ℤ) (y : Site d) :
    Measurable (fun ω => quenchedReturn e k N ω y) :=
  ((quenchedKernel d).measurable_coe (measurableSet_hitBefore _ _)).comp
    (measurable_id.prodMk measurable_const)

def returnAtLeast {d : ℕ} (e : Step d) (k N : ℤ) (a : ℝ≥0∞)
    (ω : Environment d) : Set (Site d) :=
  {y | k ≤ axisHeight e y ∧ axisHeight e y < N ∧ a ≤ quenchedReturn e k N ω y}

def returnBin {d : ℕ} (e : Step d) (k N : ℤ) (a : ℝ≥0∞)
    (ω : Environment d) : Set (Site d) :=
  {y | y ∈ returnAtLeast e k N a ω ∧ quenchedReturn e k N ω y < 2*a}

lemma measurableSet_returnAtLeast {d : ℕ} (e : Step d) (k N : ℤ) (a : ℝ≥0∞) (y : Site d) :
    MeasurableSet {ω | y ∈ returnAtLeast e k N a ω} :=
  (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
    (measurableSet_le measurable_const (measurable_quenchedReturn e k N y)))

lemma measurableSet_returnBin {d : ℕ} (e : Step d) (k N : ℤ) (a : ℝ≥0∞) (y : Site d) :
    MeasurableSet {ω | y ∈ returnBin e k N a ω} :=
  (measurableSet_returnAtLeast e k N a y).inter
    (measurableSet_lt (measurable_quenchedReturn e k N y) measurable_const)

lemma freshJoint_return_visit_bound {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d) {r N : ℕ} (hrN : r ≤ N) (a : ℝ≥0∞) :
    a * freshJoint μ 0 {ξ | ξ.2 ∈ visitAfter (axisUpper e r) (returnAtLeast e 0 N a ξ.1)
      (axisLower e 0 ∪ axisUpper e N)} ≤ axisReachProb μ e r - axisReachProb μ e N := by
  rw [freshJoint_apply μ 0 (measurable_random_visitAfter _ _ _ (measurableSet_returnAtLeast e 0 N a))]
  exact annealed_axis_visitAfter_bound μ hell e hrN a _ (by
    filter_upwards [] with ω
    exact fun y hy => hy.2.2)

lemma weighted_disjoint_measure_bound_ae {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (μ : Measure Ω) (s : ι → Set Ω) (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (fun i j => Disjoint (s i) (s j))) (w : ι → ℝ≥0∞) (F : Ω → ℝ≥0∞)
    (E : Set Ω) (hsub : ∀ i, s i ⊆ E) (hbound : ∀ i, ∀ᵐ ω ∂μ, ω ∈ s i → w i ≤ F ω) :
    ∑' i, w i * μ (s i) ≤ ∫⁻ ω in E, F ω ∂μ := by
  calc
    ∑' i, w i * μ (s i) ≤ ∑' i, ∫⁻ ω in s i, F ω ∂μ := by
      apply ENNReal.tsum_le_tsum
      intro i
      rw [← setLIntegral_const]
      exact lintegral_mono_ae ((ae_restrict_iff' (hs i)).mpr (hbound i))
    _ = ∫⁻ ω in ⋃ i, s i, F ω ∂μ := (lintegral_iUnion hs hd F).symm
    _ ≤ _ := lintegral_mono_set (Set.iUnion_subset hsub)

lemma weighted_contact_bin_bound_ae {d : ℕ} (P Q : Measure (Path d)) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (A : Set (Word d)) (D V : Set (Path d)) (K : Set (Site d))
    (hD : MeasurableSet D) (w : Word d → ℝ≥0∞) (M : Path d → ℝ≥0∞)
    (hM : Measurable M) (hA : ∀ a ∈ A, wordEnd a ∈ K)
    (hAV : ∀ a ∈ A, wordCylinder a ⊆ V)
    (hw : ∀ a ∈ A, ∀ᵐ X ∂P, X ∈ wordCylinder a → w a ≤ M X) (c : ℝ≥0∞)
    (hc : Q (D ∩ {B | ∃ n, B n ∈ K}) ≤ c) :
    ∑' a : A, w a * (P (wordCylinder a) * Q (D ∩ contactAvoid a)) ≤
      c * ∫⁻ X in V, M X ∂P := by
  let R : Set (Path d) := D ∩ {B | ∃ n, B n ∈ K}
  have hR : MeasurableSet R := hD.inter (by
    simp only [Set.ofPred_exists]
    exact MeasurableSet.iUnion (fun n => (Set.to_countable K).measurableSet.preimage (measurable_pi_apply n)))
  have hs (a : A) : MeasurableSet (wordCylinder a.val ×ˢ (D ∩ contactAvoid a.val)) :=
    (measurableSet_pathCylinder _ _).prod (hD.inter (measurableSet_contactAvoid _))
  have hd : Pairwise (fun a b : A => Disjoint
      (wordCylinder a.val ×ˢ (D ∩ contactAvoid a.val))
      (wordCylinder b.val ×ˢ (D ∩ contactAvoid b.val))) := by
    intro a b hab
    apply (contactRectangles_disjoint (i := a.val) (j := b.val) (fun h => hab (Subtype.ext h))).mono
    · exact fun _ h => ⟨h.1,h.2.2⟩
    · exact fun _ h => ⟨h.1,h.2.2⟩
  have hsub (a : A) : wordCylinder a.val ×ˢ (D ∩ contactAvoid a.val) ⊆ V ×ˢ R := by
    rintro ⟨X,B⟩ ⟨hX,hB⟩
    obtain ⟨n,hn⟩ := hB.2.1
    exact ⟨hAV _ a.property hX,hB.1,n,hn ▸ hA _ a.property⟩
  have hb (a : A) : ∀ᵐ p ∂P.prod Q, p ∈ wordCylinder a.val ×ˢ (D ∩ contactAvoid a.val) → w a.val ≤ M p.1 := by
    have hfst : ∀ᵐ p ∂P.prod Q, p.1 ∈ wordCylinder a.val → w a.val ≤ M p.1 :=
      (measurePreserving_fst (μ := P) (ν := Q)).quasiMeasurePreserving.ae (hw a a.property)
    filter_upwards [hfst] with p hp
    exact fun h => hp h.1
  have h := weighted_disjoint_measure_bound_ae (P.prod Q)
    (fun a : A => wordCylinder a.val ×ˢ (D ∩ contactAvoid a.val)) hs hd
    (fun a => w a) (fun p => M p.1) (V ×ˢ R) hsub hb
  simp only [Measure.prod_prod] at h
  apply h.trans
  rw [setLIntegral_prod (fun p : Path d × Path d => M p.1) (hM.comp measurable_fst).aemeasurable.restrict]
  simp only [setLIntegral_const]
  rw [lintegral_mul_const _ hM,mul_comm]
  exact mul_le_mul_left hc _

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

noncomputable def wordEndpointCoordinate {d ι : ℕ} (P : Measure (Path d))
    (E : Fin ι → Set (Path d)) (q : Fin ι) (a : Word d) : ℝ :=
  runningMax (endpointPosterior P E q) a.1 (wordPath a)

lemma sum_wordEndpointCoordinate {d ι : ℕ} (P : Measure (Path d))
    (E : Fin ι → Set (Path d)) (a : Word d) :
    ∑ q, wordEndpointCoordinate P E q a = wordEndpointMax P E a := rfl

lemma wordPosterior_le_stoppedCoordinate {d ι : ℕ} (P : Measure (Path d))
    (E : Fin ι → Set (Path d)) (q : Fin ι) (K : Set (Site d)) (a : Word d)
    (ha : ∀ j < a.1, wordPath a j ∉ K) (X : Path d) (hX : X ∈ wordCylinder a)
    (hex : ∃ n, X n ∈ K) :
    wordPosterior P E q a ≤ wordEndpointCoordinate P E q (firstVisitWord K X) := by
  classical
  have hle : a.1 ≤ firstVisitIndex K X := by
    by_contra h
    have hj : firstVisitIndex K X < a.1 := by omega
    apply ha _ hj
    rw [← hX _ hj.le,firstVisitIndex_eq K X hex]
    exact Nat.find_spec hex
  have hc : X ∈ wordCylinder (firstVisitWord K X) := (firstVisitWord_spec K X hex).2
  have he : endpointPosterior P E q a.1 X = wordPosterior P E q a := by
    unfold endpointPosterior
    rw [(prefixWord_eq_iff a.1 X a).mpr ⟨rfl,hX⟩]
  rw [← he,endpointPosterior_prefix P E q (firstVisitWord K X) X hc hle]
  exact Finset.le_sup' (fun i => endpointPosterior P E q i (wordPath (firstVisitWord K X)))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))

def upperContactWord {d : ℕ} (z : Site d) (R K : Set (Site d)) (a : Word d) : Prop :=
  wordPath a 0 = z ∧ (∃ j ≤ a.1, wordPath a j ∈ R) ∧ ∀ j ≤ a.1, wordPath a j ∉ K

def contactBinWords {d : ℕ} (e : Step d) (z : Site d) (r N : ℕ) (a : ℝ≥0∞)
    (ω : Environment d) : Set (Word d) :=
  {b | upperContactWord z (axisUpper e r) (axisLower e 0 ∪ axisUpper e N) b ∧
    wordEnd b ∈ returnBin e 0 N a ω}

lemma upperContactWord_visit {d : ℕ} (z : Site d) (R K A : Set (Site d)) (b : Word d)
    (hb : upperContactWord z R K b) (hA : wordEnd b ∈ A) :
    wordCylinder b ⊆ visitAfter R A K := by
  intro X hX
  refine ⟨b.1,?_,?_,?_⟩
  · rw [hX _ le_rfl];exact hA
  · obtain ⟨j,hj,hR⟩ := hb.2.1
    exact ⟨j,hj,by rw [hX _ hj];exact hR⟩
  · intro j hj
    rw [hX _ hj]
    exact hb.2.2 j hj

lemma posterior_contact_bin_quenched {d ι : ℕ} (P : Measure (Path d)) [IsProbabilityMeasure P]
    (E : Fin ι → Set (Path d)) (hE : ∀ q, MeasurableSet (E q))
    (hdis : Pairwise (fun i j => Disjoint (E i) (E j))) (e : Step d)
    (ω : Environment d) (z : Site d) (start : Fin ι → Site d) (r N : ℕ) (a : ℝ≥0∞)
    (hex : ∀ᵐ X ∂quenchedKernel d (ω,z), ∃ n, X n ∈ axisLower e 0 ∪ axisUpper e N)
    (hneg : ∀ x : Site d, quenchedKernel d (ω,x)
      (avoids (axisUpper e N) ∩ {B | ∃ n, B n ∈ returnBin e 0 N a ω}) ≤ 2*a) :
    (∑ q, ∑' b : contactBinWords e z r N a ω,
      ENNReal.ofReal (wordPosterior P E q b) *
        (quenchedKernel d (ω,z) (wordCylinder b) *
          quenchedKernel d (ω,start q) (avoids (axisUpper e N) ∩ contactAvoid b))) ≤
      (2*a) * ∫⁻ X in visitAfter (axisUpper e r) (returnAtLeast e 0 N a ω)
        (axisLower e 0 ∪ axisUpper e N),
        ENNReal.ofReal (wordEndpointMax P E (firstVisitWord (axisLower e 0 ∪ axisUpper e N) X))
        ∂quenchedKernel d (ω,z) := by
  classical
  let K := axisLower e 0 ∪ axisUpper e N
  let V := visitAfter (axisUpper e r) (returnAtLeast e 0 N a ω) K
  let M := fun q X => ENNReal.ofReal (wordEndpointCoordinate P E q (firstVisitWord K X))
  have hM (q : Fin ι) : Measurable (M q) :=
    ((measurable_of_countable (wordEndpointCoordinate P E q)).comp (measurable_firstVisitWord K)).ennreal_ofReal
  have hq (q : Fin ι) : (∑' b : contactBinWords e z r N a ω,
      ENNReal.ofReal (wordPosterior P E q b) *
        (quenchedKernel d (ω,z) (wordCylinder b) *
          quenchedKernel d (ω,start q) (avoids (axisUpper e N) ∩ contactAvoid b))) ≤
        (2*a) * ∫⁻ X in V, M q X ∂quenchedKernel d (ω,z) := by
    apply weighted_contact_bin_bound_ae _ _ (contactBinWords e z r N a ω)
      (avoids (axisUpper e N)) V (returnBin e 0 N a ω) (measurableSet_avoids _)
      (fun b => ENNReal.ofReal (wordPosterior P E q b)) (M q) (hM q)
      (fun _ hb => hb.2)
    · intro b hb
      exact upperContactWord_visit z _ _ _ b hb.1 hb.2.1
    · intro b hb
      filter_upwards [hex] with X hx
      exact fun hX => ENNReal.ofReal_le_ofReal (wordPosterior_le_stoppedCoordinate P E q K b
        (fun j hj => hb.1.2.2 j hj.le) X hX hx)
    · exact hneg _
  calc
    _ ≤ ∑ q, (2*a) * ∫⁻ X in V, M q X ∂quenchedKernel d (ω,z) := Finset.sum_le_sum (fun q _ => hq q)
    _ = (2*a) * ∫⁻ X in V, (∑ q, M q X) ∂quenchedKernel d (ω,z) := by
      rw [lintegral_finsetSum _ (fun q _ => hM q),Finset.mul_sum]
    _ = _ := by
      congr 1
      apply lintegral_congr
      intro X
      change (∑ q, ENNReal.ofReal (wordEndpointCoordinate P E q (firstVisitWord K X))) = _
      rw [← ENNReal.ofReal_sum_of_nonneg (fun q _ => show 0 ≤ wordEndpointCoordinate P E q (firstVisitWord K X) from
        runningMax_nonneg _ ((endpointPosterior_bounds P E hE hdis).1 q) _ _),sum_wordEndpointCoordinate]

lemma posterior_contact_bin_joint {d ι : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (P : Measure (Path d)) [IsProbabilityMeasure P]
    (E : Fin ι → Set (Path d)) (hE : ∀ q, MeasurableSet (E q))
    (hdis : Pairwise (fun i j => Disjoint (E i) (E j))) (e : Step d)
    (z : Site d) (start : Fin ι → Site d) (r N : ℕ) (a : ℝ≥0∞) (ha : a ≠ ∞) :
    (∫⁻ ω, ∑ q, ∑' b : contactBinWords e z r N a ω,
      ENNReal.ofReal (wordPosterior P E q b) *
        (quenchedKernel d (ω,z) (wordCylinder b) *
          quenchedKernel d (ω,start q) (avoids (axisUpper e N) ∩ contactAvoid b)) ∂environmentLaw μ) ≤
    (2*a) * ∫⁻ ξ in {ξ | ξ.2 ∈ visitAfter (axisUpper e r) (returnAtLeast e 0 N a ξ.1)
      (axisLower e 0 ∪ axisUpper e N)},
      ENNReal.ofReal (wordEndpointMax P E (firstVisitWord (axisLower e 0 ∪ axisUpper e N) ξ.2))
      ∂freshJoint μ z := by
  let K := axisLower e 0 ∪ axisUpper e N
  let V : Set (Environment d × Path d) := {ξ | ξ.2 ∈ visitAfter (axisUpper e r) (returnAtLeast e 0 N a ξ.1) K}
  let f : Environment d × Path d → ℝ≥0∞ := fun ξ => ENNReal.ofReal (wordEndpointMax P E (firstVisitWord K ξ.2))
  have hf : Measurable f := ((measurable_of_countable (wordEndpointMax P E)).comp
    ((measurable_firstVisitWord K).comp measurable_snd)).ennreal_ofReal
  have hV : MeasurableSet V := measurable_random_visitAfter _ _ _ (measurableSet_returnAtLeast e 0 N a)
  have hex : ∀ᵐ ω ∂environmentLaw μ, ∀ᵐ X ∂quenchedKernel d (ω,z), ∃ n, X n ∈ K := by
    apply annealed_ae_quenched μ z
    · have hh : (fun X : Path d => ∃ n, X n ∈ K) = ⋃ n : ℕ, {X : Path d | X n ∈ K} := by
        funext X
        apply propext
        change (∃ n, X n ∈ K) ↔ X ∈ ⋃ n : ℕ, {X : Path d | X n ∈ K}
        constructor
        · rintro ⟨n, hn⟩
          exact Set.mem_iUnion.mpr ⟨n, hn⟩
        · intro h
          exact Set.mem_iUnion.mp h
      rw [hh]
      exact MeasurableSet.iUnion (fun n => (Set.to_countable K).measurableSet.preimage (measurable_pi_apply n))
    · exact annealed_axis_exit μ hell e z 0 N
  have hinner : (∫⁻ ξ in V, f ξ ∂freshJoint μ z) =
      ∫⁻ ω, ∫⁻ X in visitAfter (axisUpper e r) (returnAtLeast e 0 N a ω) K,
        ENNReal.ofReal (wordEndpointMax P E (firstVisitWord K X)) ∂quenchedKernel d (ω,z) ∂environmentLaw μ := by
    rw [← lintegral_indicator hV,freshJoint_lintegral μ z _ (hf.indicator hV)]
    apply lintegral_congr
    intro ω
    rw [← lintegral_indicator (measurableSet_visitAfter _ _ _)]
    rfl
  change _ ≤ (2*a) * ∫⁻ ξ in V, f ξ ∂freshJoint μ z
  rw [hinner,← lintegral_const_mul' _ _ (ENNReal.mul_ne_top (by norm_num) ha)]
  apply lintegral_mono_ae
  filter_upwards [hex,quenched_negative_bins μ hell e] with ω hω hn
  apply posterior_contact_bin_quenched P E hE hdis e ω z start r N a hω
  intro x
  exact hn x 0 N (returnBin e 0 N a ω) (2*a) (fun y hy => hy.2.le)

lemma axisHeight_axialRay {d : ℕ} (e f : Step d) (x : Site d) (n : ℕ) :
    axisHeight e (axialRay x f n) = axisHeight e x + n * axisHeight e (stepVector f) := by
  induction n with
  | zero => simp [axialRay_zero]
  | succ n ih => rw [axialRay_succ,axisHeight_add,ih,Nat.cast_add,Nat.cast_one];ring

lemma axisHeight_step_opposite {d : ℕ} (e : Step d) :
    axisHeight e (stepVector (oppositeStep e)) = -1 := by
  have h := axisHeight_step_self (oppositeStep e)
  rw [axisHeight_opposite] at h
  omega

lemma quenchedReturn_pos_lt_one {d : ℕ} (e : Step d) (k N : ℤ)
    (ω : Environment d) (hω : ∀ x f, 0 < (ω x).val f) (y : Site d)
    (hy : k ≤ axisHeight e y ∧ axisHeight e y < N) :
    0 < quenchedReturn e k N ω y ∧ quenchedReturn e k N ω y < 1 := by
  let down := (axisHeight e y-k+1).toNat
  let up := (N-axisHeight e y).toNat
  have hd : (down : ℤ) = axisHeight e y-k+1 := Int.toNat_of_nonneg (by omega)
  have hu : (up : ℤ) = N-axisHeight e y := Int.toNat_of_nonneg (by omega)
  have hdown : pathCylinder down (axialRay y (oppositeStep e)) ⊆ hitBefore (axisLower e k) (axisUpper e N) := by
    intro X hX
    refine ⟨down,?_,?_⟩
    · rw [hX _ le_rfl]
      change axisHeight e (axialRay y (oppositeStep e) down) < k
      rw [axisHeight_axialRay,axisHeight_step_opposite,hd]
      omega
    · intro i hi
      rw [hX _ hi]
      change ¬N ≤ axisHeight e (axialRay y (oppositeStep e) i)
      rw [axisHeight_axialRay,axisHeight_step_opposite]
      omega
  have hup : pathCylinder up (axialRay y e) ⊆ hitBefore (axisUpper e N) (axisLower e k) := by
    intro X hX
    refine ⟨up,?_,?_⟩
    · rw [hX _ le_rfl]
      change N ≤ axisHeight e (axialRay y e up)
      rw [axisHeight_axialRay,axisHeight_step_self,hu]
      omega
    · intro i hi
      rw [hX _ hi]
      change ¬axisHeight e (axialRay y e i) < k
      rw [axisHeight_axialRay,axisHeight_step_self]
      omega
  have hdp : 0 < quenchedReturn e k N ω y :=
    (quenched_axialRay_pos ω hω y (oppositeStep e) down).trans_le (measure_mono hdown)
  have hup' : 0 < quenchedKernel d (ω,y) (hitBefore (axisUpper e N) (axisLower e k)) :=
    (quenched_axialRay_pos ω hω y e up).trans_le (measure_mono hup)
  refine ⟨hdp,lt_of_le_of_ne prob_le_one ?_⟩
  intro he
  have hb : quenchedReturn e k N ω y + quenchedKernel d (ω,y) (hitBefore (axisUpper e N) (axisLower e k)) ≤ 1 := by
    rw [quenchedReturn,← measure_union (hitBefore_disjoint _ _) (measurableSet_hitBefore _ _)]
    exact prob_le_one
  rw [he] at hb
  have hz : quenchedKernel d (ω,y) (hitBefore (axisUpper e N) (axisLower e k)) ≤ 0 := by
    apply (ENNReal.add_le_add_iff_left (by norm_num : (1 : ℝ≥0∞) ≠ ∞)).mp
    simpa using hb
  exact (not_le_of_gt hup') hz

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

noncomputable def dyad (j : ℕ) : ℝ≥0∞ := ENNReal.ofReal ((1/2 : ℝ)^(j+1))

lemma dyad_pos (j : ℕ) : 0 < dyad j := ENNReal.ofReal_pos.mpr (pow_pos (by norm_num) _)
lemma dyad_ne_top (j : ℕ) : dyad j ≠ ∞ := ENNReal.ofReal_ne_top

lemma exists_dyad_bin {q : ℝ≥0∞} (hq : 0 < q) (h1 : q < 1) :
    ∃ j : ℕ, dyad j ≤ q ∧ q < 2*dyad j := by
  have hqf : q ≠ ∞ := ne_of_lt (h1.trans (by norm_num))
  have hqr : 0 < q.toReal := ENNReal.toReal_pos (ne_of_gt hq) hqf
  have hqr1 : q.toReal < 1 := by exact_mod_cast (ENNReal.toReal_lt_toReal hqf (by norm_num)).mpr h1
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (1/2 : ℝ)) (by norm_num : (1/2 : ℝ) < 1)
  have hex : ∃ n : ℕ, (1/2 : ℝ)^n ≤ q.toReal := by
    obtain ⟨n,hn⟩ := (ht.eventually (eventually_lt_nhds hqr)).exists
    exact ⟨n,hn.le⟩
  let n := Nat.find hex
  have hn : (1/2 : ℝ)^n ≤ q.toReal := Nat.find_spec hex
  have hn0 : 0 < n := by
    by_contra h
    have he : n = 0 := by omega
    rw [he,pow_zero] at hn
    linarith
  refine ⟨n-1,?_,?_⟩
  · unfold dyad
    rw [Nat.sub_add_cancel hn0]
    exact (ENNReal.ofReal_le_iff_le_toReal hqf).mpr hn
  · have hp : q.toReal < (1/2 : ℝ)^(n-1) := lt_of_not_ge (Nat.find_min hex (by omega))
    have he : (2 : ℝ) * (1/2 : ℝ)^n = (1/2 : ℝ)^(n-1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hn0,pow_succ]
      ring
    rw [dyad,Nat.sub_add_cancel hn0,← ENNReal.ofReal_ofNat,← ENNReal.ofReal_mul (by norm_num),he]
    exact (ENNReal.lt_ofReal_iff_toReal_lt hqf).mpr hp

lemma return_bins_cover {d : ℕ} (e : Step d) (k N : ℤ) (ω : Environment d)
    (hω : ∀ x f, 0 < (ω x).val f) (y : Site d)
    (hy : k ≤ axisHeight e y ∧ axisHeight e y < N) :
    ∃ j, y ∈ returnBin e k N (dyad j) ω := by
  obtain ⟨j,hj,hj'⟩ := exists_dyad_bin (quenchedReturn_pos_lt_one e k N ω hω y hy).1
    (quenchedReturn_pos_lt_one e k N ω hω y hy).2
  exact ⟨j,⟨hy.1,hy.2,hj⟩,hj'⟩

lemma tsum_subtype_cover {α : Type*} [Countable α] (A : Set α) (B : ℕ → Set α)
    (h : A ⊆ ⋃ n, B n) (f : α → ℝ≥0∞) :
    (∑' a : A, f a) ≤ ∑' n, ∑' a : B n, f a := by
  classical
  have hex (a : A) : ∃ n, a.val ∈ B n := Set.mem_iUnion.mp (h a.property)
  let g : A → (Σ n, B n) := fun a => ⟨(hex a).choose,⟨a.val,(hex a).choose_spec⟩⟩
  have hg : Function.Injective g := by
    intro a b hab
    have hv : ((g a).2 : α) = ((g b).2 : α) := congrArg (fun i : Σ n, B n => i.2.val) hab
    exact Subtype.ext hv
  calc
    _ ≤ ∑' i : Σ n, B n, f i.2 := Summable.tsum_le_tsum_of_inj g hg (fun _ _ => zero_le) (fun _ => le_rfl) ENNReal.summable ENNReal.summable
    _ = _ := ENNReal.tsum_sigma (fun n (a : B n) => f a)

lemma half_geometric_sum_le (s : Finset ℕ) : (∑ j ∈ s, (1/2 : ℝ)^(j+1)) ≤ 1 := by
  have hs : HasSum (fun j : ℕ => (1/2 : ℝ)^(j+1)) 1 := by
    have hh := (hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1/2 : ℝ)‖ < 1)).mul_right (1/2)
    norm_num [pow_succ] at hh ⊢
    exact hh
  exact (hs.summable.sum_le_tsum s (fun j _ => by positivity)).trans_eq hs.tsum_eq

lemma half_geometric_tail_sum_le (s : Finset ℕ) (m : ℕ) :
    (∑ j ∈ s.filter (m ≤ ·), (1/2 : ℝ)^(j+1)) ≤ (1/2 : ℝ)^m := by
  classical
  let t := (s.filter (m ≤ ·)).image (fun j => j-m)
  have he : (∑ j ∈ s.filter (m ≤ ·), (1/2 : ℝ)^(j+1)) =
      (1/2 : ℝ)^m * ∑ j ∈ t, (1/2 : ℝ)^(j+1) := by
    rw [Finset.mul_sum,Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [← pow_add]
      congr 1
      have := (Finset.mem_filter.mp hj).2
      omega
    · intro a ha b hb hab
      have := (Finset.mem_filter.mp ha).2
      have := (Finset.mem_filter.mp hb).2
      change a-m=b-m at hab
      omega
  rw [he]
  exact (mul_le_mul_of_nonneg_left (half_geometric_sum_le t) (by positivity)).trans_eq (mul_one _)

lemma dyadic_weighted_mass_sum {v : ℕ → ℝ} (_hv0 : ∀ j, 0 ≤ v j) (hv1 : ∀ j, v j ≤ 1)
    (m : ℕ) (hv : ∀ j, (1/2 : ℝ)^(j+1)*v j ≤ (1/2 : ℝ)^m) (s : Finset ℕ) :
    (∑ j ∈ s, (1/2 : ℝ)^(j+1)*v j) ≤ (m+1)*(1/2 : ℝ)^m := by
  classical
  have hsmall : (∑ j ∈ s.filter (· < m), (1/2 : ℝ)^(j+1)*v j) ≤ m*(1/2 : ℝ)^m := by
    calc
      _ ≤ ∑ _ ∈ s.filter (· < m), (1/2 : ℝ)^m := Finset.sum_le_sum (fun j _ => hv j)
      _ = ((s.filter (· < m)).card : ℝ)*(1/2 : ℝ)^m := by simp
      _ ≤ m*(1/2 : ℝ)^m := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hh : (s.filter (· < m)).card ≤ m := by
          simpa using (Finset.card_le_card (show s.filter (· < m) ⊆ Finset.range m by
            intro j hj;exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2))
        exact_mod_cast hh
  have hlarge : (∑ j ∈ s.filter (m ≤ ·), (1/2 : ℝ)^(j+1)*v j) ≤ (1/2 : ℝ)^m := by
    apply (Finset.sum_le_sum (s := s.filter (m ≤ ·)) (fun j _ =>
      mul_le_of_le_one_right (by positivity) (hv1 j))).trans
    exact half_geometric_tail_sum_le s m
  have he : (∑ j ∈ s.filter (· < m), (1/2 : ℝ)^(j+1)*v j) +
      (∑ j ∈ s.filter (m ≤ ·), (1/2 : ℝ)^(j+1)*v j) = ∑ j ∈ s, (1/2 : ℝ)^(j+1)*v j := by
    simpa only [not_lt] using Finset.sum_filter_add_sum_filter_not s (fun j => j < m)
      (fun j => (1/2 : ℝ)^(j+1)*v j)
  linarith

lemma dyadic_event_weight_bound {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (S : Ω → ℝ) (hS : Integrable S ν)
    (hS0 : ∀ ξ, 0 ≤ S ξ) (c : ℝ) (hc : 0 < c)
    (hExp : Integrable (fun ξ => Real.exp (c*S ξ)) ν)
    (hExp12 : (∫ ξ, Real.exp (c*S ξ) ∂ν) ≤ 12)
    (V : ℕ → Set Ω) (m : ℕ)
    (hV : ∀ j, dyad j * ν (V j) ≤ ENNReal.ofReal ((1/2 : ℝ)^m)) :
    (∑' j, 2*dyad j * ∫⁻ ξ in V j, ENNReal.ofReal (S ξ) ∂ν) ≤
      ENNReal.ofReal ((24/c)*(m+1)^2*(1/2 : ℝ)^m) := by
  classical
  let t := (1/2 : ℝ)^m
  have ht : 0 < t := pow_pos (by norm_num) _
  have ht1 : t ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hl : Real.log t ≤ 0 := Real.log_nonpos ht.le ht1
  have hv (j : ℕ) : (1/2 : ℝ)^(j+1)*ν.real (V j) ≤ t := by
    have hh := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) (hV j)
    simpa only [ENNReal.toReal_mul,dyad,ENNReal.toReal_ofReal (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) _),Measure.real,t] using hh
  have hlog : -Real.log t ≤ m := by
    dsimp [t]
    rw [Real.log_pow,Real.log_div (by norm_num) (by norm_num),Real.log_one]
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    nlinarith [mul_le_mul_of_nonneg_left h (Nat.cast_nonneg m)]
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro s
  have hI (j : ℕ) : c*(∫ ξ in V j, S ξ ∂ν) ≤ 12*t - ν.real (V j)*Real.log t := by
    have hp (ξ : Ω) : c*S ξ ≤ t*Real.exp (c*S ξ)-Real.log t := by
      have h := Real.add_one_le_exp (c*S ξ + Real.log t)
      rw [Real.exp_add,Real.exp_log ht] at h
      nlinarith
    have hi := integral_mono (hS.restrict (s := V j) |>.const_mul c)
      ((hExp.restrict.const_mul t).sub (integrable_const (Real.log t))) hp
    simp only [Pi.sub_apply] at hi
    rw [integral_const_mul,integral_sub (hExp.restrict (s := V j) |>.const_mul t) (integrable_const _),
      integral_const_mul,integral_const,measureReal_restrict_apply_univ,smul_eq_mul] at hi
    have he : (∫ ξ in V j, Real.exp (c*S ξ) ∂ν) ≤ 12 :=
      (setIntegral_le_integral hExp (Filter.Eventually.of_forall (fun ξ => Real.exp_nonneg _))).trans hExp12
    nlinarith [mul_le_mul_of_nonneg_left he ht.le]
  let B := ∑ j ∈ s, (1/2 : ℝ)^(j+1)*(∫ ξ in V j, S ξ ∂ν)
  have hB : c*B ≤ 12*t + m*((m+1)*t) := by
    have hsum := Finset.sum_le_sum (s := s) (fun j _ => mul_le_mul_of_nonneg_left (hI j)
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) (j+1)))
    have he1 : (∑ j ∈ s, (1/2 : ℝ)^(j+1)*(c*(∫ ξ in V j, S ξ ∂ν))) = c*B := by
      dsimp [B];rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro j _;ring
    have he2 : (∑ j ∈ s, (1/2 : ℝ)^(j+1)*(12*t-ν.real (V j)*Real.log t)) =
        12*t*(∑ j ∈ s, (1/2 : ℝ)^(j+1)) + (-Real.log t)*(∑ j ∈ s, (1/2 : ℝ)^(j+1)*ν.real (V j)) := by
      rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl;intro j _;ring
    rw [he1,he2] at hsum
    have hmass := dyadic_weighted_mass_sum (fun j => measureReal_nonneg) (fun j => measureReal_le_one) m hv s
    have hh := mul_le_mul_of_nonneg_left (half_geometric_sum_le s) (show 0 ≤ 12*t by positivity)
    have hh' := mul_le_mul hlog hmass (Finset.sum_nonneg (fun j _ => mul_nonneg (by positivity) measureReal_nonneg)) (Nat.cast_nonneg m)
    dsimp [t] at *
    nlinarith
  have hbound : 2*B ≤ (24/c)*(m+1)^2*t := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hpoly : 12*t + m*((m+1)*t) ≤ 12*(m+1)^2*t := by
      nlinarith [sq_nonneg (m : ℝ)]
    have hcc : c*(2*B) ≤ c*((24/c)*(m+1)^2*t) := by
      field_simp
      nlinarith [hB.trans hpoly]
    exact (mul_le_mul_iff_right₀ hc).mp hcc
  have he (j : ℕ) : 2*dyad j * (∫⁻ ξ in V j, ENNReal.ofReal (S ξ) ∂ν) =
      ENNReal.ofReal (2*(1/2 : ℝ)^(j+1)*(∫ ξ in V j, S ξ ∂ν)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hS.restrict (Filter.Eventually.of_forall hS0),dyad]
    rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_mul (by norm_num)]
    norm_num
  simp_rw [he]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (by positivity)
    (integral_nonneg hS0))]
  apply ENNReal.ofReal_le_ofReal
  convert hbound using 1
  dsimp [B,t]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

lemma measurable_dependent_subtype_tsum {Ω α : Type*} [MeasurableSpace Ω] [Countable α]
    (A : Ω → Set α) (hA : ∀ a, MeasurableSet {ω | a ∈ A ω})
    (f : α → Ω → ℝ≥0∞) (hf : ∀ a, Measurable (f a)) :
    Measurable (fun ω => ∑' a : A ω, f a ω) := by
  classical
  have he : (fun ω => ∑' a : A ω, f a ω) =
      fun ω => ∑' a : α, if a ∈ A ω then f a ω else 0 := by
    funext ω
    simpa only [Set.indicator_apply] using tsum_subtype (A ω) (fun a => f a ω)
  rw [he]
  exact Measurable.tsum (fun a => Measurable.ite (hA a) (hf a) measurable_const)

lemma measurable_contactBinMass {d ι : ℕ} (P : Measure (Path d))
    (E : Fin ι → Set (Path d)) (e : Step d) (z : Site d) (start : Fin ι → Site d)
    (r N : ℕ) (a : ℝ≥0∞) :
    Measurable (fun ω => ∑ q, ∑' b : contactBinWords e z r N a ω,
      ENNReal.ofReal (wordPosterior P E q b) *
        (quenchedKernel d (ω,z) (wordCylinder b) *
          quenchedKernel d (ω,start q) (avoids (axisUpper e N) ∩ contactAvoid b))) := by
  apply Finset.measurable_sum
  intro q _
  refine measurable_dependent_subtype_tsum (contactBinWords e z r N a) ?_
    (fun b ω => ENNReal.ofReal (wordPosterior P E q b) *
      (quenchedKernel d (ω,z) (wordCylinder b) *
        quenchedKernel d (ω,start q) (avoids (axisUpper e N) ∩ contactAvoid b))) ?_
  · intro b
    exact (MeasurableSet.const _).inter (measurableSet_returnBin e 0 N a (wordEnd b))
  · intro b
    apply measurable_const.mul
    exact (((quenchedKernel d).measurable_coe (measurableSet_pathCylinder _ _)).comp
      (measurable_id.prodMk measurable_const)).mul
      (((quenchedKernel d).measurable_coe ((measurableSet_avoids _).inter
        (measurableSet_contactAvoid b))).comp (measurable_id.prodMk measurable_const))

lemma measurable_quenched_apply {d : ℕ} (z : Site d) (E : Set (Path d)) (hE : MeasurableSet E) :
    Measurable (fun ω => quenchedKernel d (ω,z) E) :=
  ((quenchedKernel d).measurable_coe hE).comp (measurable_id.prodMk measurable_const)

lemma measurable_kernel_weighted_sum {Ω ξ β α : Type*} [MeasurableSpace Ω] [MeasurableSpace ξ]
    [MeasurableSpace β] [Countable α] (κ : Kernel (Ω × ξ) β) (z y : ξ)
    (A B : α → Set β) (hA : ∀ a, MeasurableSet (A a)) (hB : ∀ a, MeasurableSet (B a)) (f : α → ℝ≥0∞) :
    Measurable (fun ω => ∑' a, f a * (κ (ω,z) (A a) * κ (ω,y) (B a))) := by
  apply Measurable.tsum
  intro a
  exact measurable_const.mul (((κ.measurable_coe (hA a)).comp (measurable_id.prodMk measurable_const)).mul
    ((κ.measurable_coe (hB a)).comp (measurable_id.prodMk measurable_const)))

lemma measurable_weighted_contact_tsum {d : ℕ} (A : Set (Word d)) (f : Word d → ℝ≥0∞)
    (z y : Site d) (K : Set (Site d)) :
    Measurable (fun ω => ∑' a : A, f a * (quenchedKernel d (ω,z) (wordCylinder a) *
      quenchedKernel d (ω,y) (avoids K ∩ contactAvoid a))) := by
  exact measurable_kernel_weighted_sum (quenchedKernel d) z y
    (fun a : A => wordCylinder a) (fun a : A => avoids K ∩ contactAvoid a)
    (fun a => measurableSet_pathCylinder a.val.1 (wordPath a.val))
    (fun a => (measurableSet_avoids K).inter (measurableSet_contactAvoid a.val)) (fun a => f a.val)

lemma totalPosterior_le_bins {d ι : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (P : Measure (Path d)) (E : Fin ι → Set (Path d))
    (e : Step d) (z : Site d) (start : Fin ι → Site d) (r N : ℕ) :
    (∑ q, ∑' b : {b | upperContactWord z (axisUpper e r) (axisLower e 0 ∪ axisUpper e N) b},
      ENNReal.ofReal (wordPosterior P E q b) *
        (annealed μ z (wordCylinder b) *
          annealed μ (start q) (avoids (axisUpper e N) ∩ contactAvoid b))) ≤
    ∑' j, ∫⁻ ω, ∑ q, ∑' b : contactBinWords e z r N (dyad j) ω,
      ENNReal.ofReal (wordPosterior P E q b) *
        (quenchedKernel d (ω,z) (wordCylinder b) *
          quenchedKernel d (ω,start q) (avoids (axisUpper e N) ∩ contactAvoid b)) ∂environmentLaw μ := by
  classical
  let A := {b | upperContactWord z (axisUpper e r) (axisLower e 0 ∪ axisUpper e N) b}
  have he (q : Fin ι) := weighted_contact_transfer μ z (start q) A (fun _ hb => hb.1)
    (fun b => ENNReal.ofReal (wordPosterior P E q b)) (measurableSet_avoids (axisUpper e N))
  simp only [Measure.prod_prod] at he
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun q _ => he q)
  rw [hsum]
  have hme (q : Fin ι) : Measurable (fun ω => ∑' a : A,
      ENNReal.ofReal (wordPosterior P E q a) *
        (quenchedKernel d (ω,z) (wordCylinder a) *
          quenchedKernel d (ω,start q) (avoids (axisUpper e N) ∩ contactAvoid a))) :=
    measurable_weighted_contact_tsum A (fun a => ENNReal.ofReal (wordPosterior P E q a)) z (start q) (axisUpper e N)
  rw [← lintegral_finsetSum _ (fun q _ => hme q)]
  rw [← lintegral_tsum (fun j => (measurable_contactBinMass P E e z start r N (dyad j)).aemeasurable)]
  apply lintegral_mono_ae
  filter_upwards [all_rows_strictly_positive μ hell] with ω hω
  calc
    _ ≤ ∑ q, ∑' j, ∑' b : contactBinWords e z r N (dyad j) ω,
        ENNReal.ofReal (wordPosterior P E q b) *
          (quenchedKernel d (ω,z) (wordCylinder b) *
            quenchedKernel d (ω,start q) (avoids (axisUpper e N) ∩ contactAvoid b)) := by
      apply Finset.sum_le_sum
      intro q _
      refine tsum_subtype_cover A (fun j => contactBinWords e z r N (dyad j) ω) ?_
        (fun b => ENNReal.ofReal (wordPosterior P E q b) *
          (quenchedKernel d (ω,z) (wordCylinder b) *
            quenchedKernel d (ω,start q) (avoids (axisUpper e N) ∩ contactAvoid b)))
      intro b hb
      obtain ⟨j,hj⟩ := return_bins_cover e 0 N ω hω (wordEnd b) (by
        have hh := hb.2.2 b.1 le_rfl
        simp only [Set.mem_union,not_or,axisLower,axisUpper,Set.mem_ofPred_eq,not_lt,not_le] at hh
        exact hh)
      exact Set.mem_iUnion.mpr ⟨j,hb,hj⟩
    _ = _ := by
      simpa only [tsum_fintype] using (ENNReal.tsum_comm (f := fun q j => ∑' b : contactBinWords e z r N (dyad j) ω,
        ENNReal.ofReal (wordPosterior P E q b) *
          (quenchedKernel d (ω,z) (wordCylinder b) *
            quenchedKernel d (ω,start q) (avoids (axisUpper e N) ∩ contactAvoid b))))

lemma posterior_contact_raw_bound {d ι : ℕ} [NeZero ι]
    (μ : Measure (Row d)) [IsProbabilityMeasure μ] (hell : StrictEllipticity μ)
    (P : Measure (Path d)) [IsProbabilityMeasure P]
    (E : Fin ι → Set (Path d)) (hE : ∀ q, MeasurableSet (E q))
    (hdis : Pairwise (fun i j => Disjoint (E i) (E j))) (e : Step d)
    (start : Fin ι → Site d) (r N m : ℕ) (hrN : r ≤ N)
    (he : P.map (firstVisitWord (axisLower e 0 ∪ axisUpper e N)) =
      (annealed μ 0).map (firstVisitWord (axisLower e 0 ∪ axisUpper e N)))
    (hΔ : axisReachProb μ e r - axisReachProb μ e N ≤ ENNReal.ofReal ((1/2 : ℝ)^m)) :
    (∑ q, ∑' b : {b | upperContactWord 0 (axisUpper e r) (axisLower e 0 ∪ axisUpper e N) b},
      ENNReal.ofReal (wordPosterior P E q b) *
        (annealed μ 0 (wordCylinder b) *
          annealed μ (start q) (avoids (axisUpper e N) ∩ contactAvoid b))) ≤
      ENNReal.ofReal ((24 / posteriorExponent)*Real.log (ι+1)*(m+1)^2*(1/2 : ℝ)^m) := by
  let K := axisLower e 0 ∪ axisUpper e N
  let V := fun j => {ξ : Environment d × Path d | ξ.2 ∈ visitAfter (axisUpper e r)
    (returnAtLeast e 0 N (dyad j) ξ.1) K}
  let f := fun X : Path d => wordEndpointMax P E (firstVisitWord K X)
  let ν := freshJoint μ 0
  let c := posteriorExponent/Real.log (ι+1)
  have hc : 0 < c := div_pos posteriorExponent_pos
    (Real.log_pos (by exact_mod_cast (show 1 < ι+1 by have := NeZero.pos ι;omega)))
  have hm : Measurable f := (measurable_of_countable (wordEndpointMax P E)).comp (measurable_firstVisitWord K)
  have hmf : Measurable (fun ξ : Environment d × Path d => f ξ.2) := hm.comp measurable_snd
  have hb (X : Path d) : 0 ≤ f X ∧ f X ≤ ι := wordEndpointMax_bounds P E hE hdis _
  have hi : Integrable (fun ξ : Environment d × Path d => f ξ.2) ν :=
    (integrable_const (ι : ℝ)).mono' hmf.aestronglyMeasurable (by
      filter_upwards [] with ξ
      rw [Real.norm_eq_abs,abs_of_nonneg (hb ξ.2).1]
      exact (hb ξ.2).2)
  have hie := integrable_exp_of_bound ν (fun ξ => f ξ.2) hmf ι c (fun ξ => (hb ξ.2).2) hc.le
  have hex : (∫ ξ, Real.exp (c*f ξ.2) ∂ν) ≤ 12 := by
    have hπ := freshJoint_path_marginal μ 0
    have hi' : (∫ ξ, Real.exp (c*f ξ.2) ∂ν) = ∫ X, Real.exp (c*f X) ∂annealed μ 0 := by
      rw [← hπ.map_eq]
      exact (integral_map_of_stronglyMeasurable hπ.measurable (hm.const_mul c).exp.stronglyMeasurable).symm
    rw [hi']
    exact stoppedEndpointMax_exponential P (annealed μ 0) E hE hdis K he
  have hv (j : ℕ) : dyad j * ν (V j) ≤ ENNReal.ofReal ((1/2 : ℝ)^m) :=
    (freshJoint_return_visit_bound μ hell e hrN (dyad j)).trans hΔ
  have hn := dyadic_event_weight_bound ν (fun ξ => f ξ.2) hi (fun ξ => (hb ξ.2).1)
    c hc hie hex V m hv
  have hs : 24/c = (24/posteriorExponent)*Real.log (ι+1) := by dsimp [c];field_simp
  rw [hs] at hn
  apply (totalPosterior_le_bins μ hell P E e 0 start r N).trans
  apply le_trans (ENNReal.tsum_le_tsum (fun j => posterior_contact_bin_joint μ hell P E hE hdis e 0 start r N
    (dyad j) ENNReal.ofReal_ne_top)) hn

noncomputable def commonCount {α : Type*} (L : Bool → α → ℕ) (H : ℕ) (Z : TwoTape α) : ℕ := by
  classical
  exact ∑ j ∈ Finset.range H, if Z ∈ commonCut L (j+1) then 1 else 0

noncomputable def listCommonCount {α : Type*} (L : Bool → α → ℕ) (a : TwoTapeList α) : ℕ := by
  classical
  exact ∑ j ∈ Finset.range (listHeight (L false) (a false)),
    if ∀ b, listHasCut (L b) (a b) (j+1) then 1 else 0

lemma commonCount_cutList {α : Type*} (L : Bool → α → ℕ) (H : ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i))) (hc : Z ∈ commonCut L H) :
    listCommonCount L (commonCutList L H Z) = commonCount L H Z := by
  classical
  have hh := ((commonCutList_atom_iff L H Z hZ (commonCutList L H Z)).mp ⟨hc,rfl⟩).1 false
  unfold listCommonCount commonCount
  rw [hh]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [← commonCut_iff_listHasCut L Z hZ H (j+1) hc (by have := Finset.mem_range.mp hj;omega)]

lemma commonCount_zero {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α) :
    commonCount L 0 Z = 0 := by simp [commonCount]

lemma commonCount_succ {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α) (H : ℕ) :
    commonCount L (H+1) Z = commonCount L H Z + (by classical exact if Z ∈ commonCut L (H+1) then 1 else 0) := by
  classical
  exact Finset.sum_range_succ _ _

lemma commonCount_mono {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α) :
    Monotone (fun H => commonCount L H Z) := by
  classical
  intro H J hHJ
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hHJ) (fun _ _ _ => Nat.zero_le _)

lemma commonCount_lt_at_cut {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    {H J : ℕ} (hHJ : H < J) (hJ : Z ∈ commonCut L J) :
    commonCount L H Z < commonCount L J Z := by
  classical
  have hm : commonCount L H Z ≤ commonCount L (J-1) Z := commonCount_mono L Z (by omega)
  have hh : commonCount L J Z = commonCount L (J-1) Z + 1 := by
    have hs := commonCount_succ L Z (J-1)
    simpa only [show J-1+1=J by omega,ite_eq_left hJ] using hs
  omega

lemma commonCut_count_injective {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    {H J : ℕ} (hH : Z ∈ commonCut L H) (hJ : Z ∈ commonCut L J)
    (he : commonCount L H Z = commonCount L J Z) : H = J := by
  rcases lt_trichotomy H J with h | h | h
  · exact False.elim ((ne_of_lt (commonCount_lt_at_cut L Z h hJ)) he)
  · exact h
  · exact False.elim ((ne_of_lt (commonCount_lt_at_cut L Z h hH)) he.symm)

lemma commonCount_add {α : Type*} (L : Bool → α → ℕ) (H J : ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i))) (hc : Z ∈ commonCut L H) :
    commonCount L (H+J) Z = commonCount L H Z + commonCount L J (afterCommonCut L H Z) := by
  classical
  unfold commonCount
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [Nat.add_assoc,commonCut_add_iff L H Z hZ hc (j+1)]

lemma commonCount_first {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    (he : ∃ H, 0 < H ∧ Z ∈ commonCut L H) :
    commonCount L (firstCommonWidth L Z) Z = 1 := by
  classical
  obtain ⟨hpos,hcut,hmin⟩ := firstCommonWidth_spec L Z he
  have hzero : commonCount L (firstCommonWidth L Z-1) Z = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hj' := Finset.mem_range.mp hj
    exact ite_eq_right (hmin (j+1) (by omega) (by omega))
  have heq : firstCommonWidth L Z = (firstCommonWidth L Z-1)+1 := by omega
  have hs := commonCount_succ L Z (firstCommonWidth L Z-1)
  simpa only [← heq,ite_eq_left hcut,hzero,zero_add] using hs

lemma twoShift_comp {α : Type*} (n m : Bool → ℕ) (Z : TwoTape α) :
    twoShift m (twoShift n Z) = twoShift (fun b => n b + m b) Z := by
  funext i
  simp only [twoShift,Nat.add_assoc]

lemma cutListIndex_spec {α : Type*} (L : α → ℕ) (H : ℕ) (Z : ℕ → α)
    (hZ : ∀ i, 0 < L (Z i)) (hc : Z ∈ renewalCut L H) :
    tapeHeight L Z (cutListIndex L H Z) = H := by
  obtain ⟨n,hn⟩ := hc
  rw [cutListIndex_eq L H Z hZ hn,hn]

lemma afterCommonCut_add {α : Type*} (L : Bool → α → ℕ) (H J : ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i))) (hH : Z ∈ commonCut L H)
    (hJ : afterCommonCut L H Z ∈ commonCut L J) :
    afterCommonCut L (H+J) Z = afterCommonCut L J (afterCommonCut L H Z) := by
  have hie (b : Bool) : commonCutIndices L (H+J) Z b =
      commonCutIndices L H Z b + commonCutIndices L J (afterCommonCut L H Z) b := by
    apply cutListIndex_eq (L b) (H+J) _ (hZ b)
    rw [tapeHeight_add]
    have h1 : tapeHeight (L b) (fun i => Z (b,i)) (commonCutIndices L H Z b) = H := by
      exact cutListIndex_spec (L b) H _ (hZ b) (hH b)
    have h2 : tapeHeight (L b) (fun i => Z (b,commonCutIndices L H Z b+i))
        (commonCutIndices L J (afterCommonCut L H Z) b) = J := by
      exact cutListIndex_spec (L b) J _ (fun i => hZ b _) (hJ b)
    rw [h1,h2]
  unfold afterCommonCut
  rw [twoShift_comp]
  congr 1
  exact funext hie

noncomputable def commonDepth {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α) (r : ℕ) : ℕ :=
  ∑ i ∈ Finset.range r, firstCommonWidth L ((commonRestart L)^[i] Z)

lemma commonDepth_zero {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α) :
    commonDepth L Z 0 = 0 := by simp [commonDepth]

lemma commonDepth_succ {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α) (r : ℕ) :
    commonDepth L Z (r+1) = commonDepth L Z r + firstCommonWidth L ((commonRestart L)^[r] Z) := by
  exact Finset.sum_range_succ _ _

lemma commonDepth_spec {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i)))
    (he : ∀ r, ∃ H, 0 < H ∧ ((commonRestart L)^[r] Z) ∈ commonCut L H) (r : ℕ) :
    Z ∈ commonCut L (commonDepth L Z r) ∧
    afterCommonCut L (commonDepth L Z r) Z = (commonRestart L)^[r] Z ∧
    commonCount L (commonDepth L Z r) Z = r := by
  induction r with
  | zero =>
    have h0 : commonCutIndices L 0 Z = fun _ => 0 := by
      funext b
      exact cutListIndex_eq (L b) 0 _ (hZ b) rfl
    refine ⟨by rw [commonDepth_zero,commonCut_zero];trivial,?_,by rw [commonDepth_zero,commonCount_zero]⟩
    simp only [commonDepth_zero,afterCommonCut,h0,Function.iterate_zero, id_eq]
    funext i
    exact congrArg Z (by cases i;simp only [Nat.zero_add])
  | succ r ih =>
    obtain ⟨_,hc,_⟩ := firstCommonWidth_spec L ((commonRestart L)^[r] Z) (he r)
    have hc' : afterCommonCut L (commonDepth L Z r) Z ∈
        commonCut L (firstCommonWidth L ((commonRestart L)^[r] Z)) := by rw [ih.2.1];exact hc
    rw [commonDepth_succ]
    refine ⟨(commonCut_add_iff L _ Z hZ ih.1 _).mpr hc',?_,?_⟩
    · rw [afterCommonCut_add L _ _ Z hZ ih.1 hc',ih.2.1,Function.iterate_succ_apply']
      rfl
    · rw [commonCount_add L _ _ Z hZ ih.1,ih.2.1,ih.2.2,commonCount_first L _ (he r)]

lemma ae_common_iterates {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H) :
    ∀ᵐ Z ∂twoTapeLaw ν, ∀ r, ∃ H, 0 < H ∧ ((commonRestart L)^[r] Z) ∈ commonCut L H := by
  rw [ae_all_iff]
  intro r
  exact ((commonRestart_measurePreserving ν L hL he).iterate r).quasiMeasurePreserving.ae he

lemma measurable_commonDepth {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (L : Bool → α → ℕ) (r : ℕ) : Measurable (fun Z => commonDepth L Z r) := by
  exact Finset.measurable_sum _ (fun i _ => (measurable_firstCommonWidth L).comp
    ((measurable_commonRestart L).iterate i))

noncomputable def nthCommonList {α : Type*} (L : Bool → α → ℕ) (r : ℕ) (Z : TwoTape α) : TwoTapeList α :=
  commonCutList L (commonDepth L Z r) Z

lemma measurable_nthCommonList {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (L : Bool → α → ℕ) (r : ℕ) : Measurable (nthCommonList L r) := by
  have hm : Measurable (fun p : TwoTape α × ℕ => commonCutList L p.2 p.1) :=
    measurable_from_prod_countable_left (measurable_commonCutList L)
  exact hm.comp (measurable_id.prodMk (measurable_commonDepth L r))

def BalancedList {α : Type*} (L : Bool → α → ℕ) (a : TwoTapeList α) : Prop :=
  ∀ b, listHeight (L b) (a b) = listHeight (L false) (a false)

lemma nthCommonList_atom_iff {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i)))
    (he : ∀ r, ∃ H, 0 < H ∧ ((commonRestart L)^[r] Z) ∈ commonCut L H)
    (r : ℕ) (a : TwoTapeList α) :
    nthCommonList L r Z = a ↔ (BalancedList L a ∧ listCommonCount L a = r ∧ Z ∈ twoCylinder a) := by
  obtain ⟨hc,_,hr⟩ := commonDepth_spec L Z hZ he r
  constructor
  · intro ha
    have hh := (commonCutList_atom_iff L (commonDepth L Z r) Z hZ a).mp ⟨hc,ha⟩
    refine ⟨fun b => (hh.1 b).trans (hh.1 false).symm,?_,hh.2⟩
    rw [← ha]
    exact (commonCount_cutList L _ Z hZ hc).trans hr
  · rintro ⟨hb,hr',hpre⟩
    obtain ⟨hc',hh⟩ := (commonCutList_atom_iff L _ Z hZ a).mpr ⟨hb,hpre⟩
    have hn : commonDepth L Z r = listHeight (L false) (a false) := by
      apply commonCut_count_injective L Z hc hc'
      rw [hr,← commonCount_cutList L _ Z hZ hc',hh,hr']
    unfold nthCommonList
    rw [hn,hh]

noncomputable def nthCommonLaw {α : Type*} [MeasurableSpace α]
    (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (r : ℕ) : Measure (TwoTapeList α) :=
  (twoTapeLaw ν).map (nthCommonList L r)

instance nthCommonLaw_probability {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (r : ℕ) : IsProbabilityMeasure (nthCommonLaw ν L r) :=
  probabilityMeasure_map (μ := twoTapeLaw ν) (measurable_nthCommonList L r).aemeasurable

lemma nthCommonLaw_atom {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (r : ℕ) (a : TwoTapeList α) :
    nthCommonLaw ν L r {a} = (by classical exact if BalancedList L a ∧ listCommonCount L a = r
      then (∏ b : Bool, ∏ i : Fin (a b).1, ν b {(a b).2 i}) else 0) := by
  classical
  have hZ := ae_twoTape_prop ν (fun b a => 0 < L b a)
    (fun b => measurableSet_lt measurable_const (measurable_of_countable (L b))) hL
  have hiter := ae_common_iterates ν L hL he
  rw [nthCommonLaw,Measure.map_apply (measurable_nthCommonList L r) (measurableSet_singleton a)]
  by_cases ha : BalancedList L a ∧ listCommonCount L a = r
  · rw [ite_eq_left ha,← twoCylinder_mass ν a]
    apply measure_congr
    filter_upwards [hZ,hiter] with Z hZ hiter
    apply propext
    exact ⟨fun h => ((nthCommonList_atom_iff L Z hZ hiter r a).mp h).2.2,
      fun h => (nthCommonList_atom_iff L Z hZ hiter r a).mpr ⟨ha.1,ha.2,h⟩⟩
  · rw [ite_eq_right ha]
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hZ,hiter] with Z hZ hiter h
    have hh := (nthCommonList_atom_iff L Z hZ hiter r a).mp h
    exact ha ⟨hh.1,hh.2.1⟩

lemma nthCommon_suffix_factorization {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (r : ℕ) (a : TwoTapeList α) (E : Set (TwoTape α)) (hE : MeasurableSet E) :
    twoTapeLaw ν {Z | nthCommonList L r Z = a ∧ (commonRestart L)^[r] Z ∈ E} =
      nthCommonLaw ν L r {a} * twoTapeLaw ν E := by
  classical
  have hZ := ae_twoTape_prop ν (fun b a => 0 < L b a)
    (fun b => measurableSet_lt measurable_const (measurable_of_countable (L b))) hL
  have hiter := ae_common_iterates ν L hL he
  by_cases ha : BalancedList L a ∧ listCommonCount L a = r
  · rw [nthCommonLaw_atom ν L hL he r a,ite_eq_left ha]
    rw [← twoCylinder_suffix_factorization ν a E hE]
    apply measure_congr
    filter_upwards [hZ,hiter] with Z hZ hiter
    have hs (hh : nthCommonList L r Z = a) :
        (commonRestart L)^[r] Z = twoShift (fun b => (a b).1) Z := by
      rw [← (commonDepth_spec L Z hZ hiter r).2.1]
      unfold afterCommonCut
      rw [commonCutIndices_eq_lengths L _ Z a hh]
    apply propext
    constructor
    · rintro ⟨hb,hE⟩
      exact ⟨((nthCommonList_atom_iff L Z hZ hiter r a).mp hb).2.2,by rwa [← hs hb]⟩
    · rintro ⟨hb,hE⟩
      have hh := (nthCommonList_atom_iff L Z hZ hiter r a).mpr ⟨ha.1,ha.2,hb⟩
      exact ⟨hh,by rwa [hs hh]⟩
  · rw [nthCommonLaw_atom ν L hL he r a,ite_eq_right ha,zero_mul]
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hZ,hiter] with Z hZ hiter h
    have hh := (nthCommonList_atom_iff L Z hZ hiter r a).mp h.1
    exact ha ⟨hh.1,hh.2.1⟩

noncomputable def windowCommonLaw {α : Type*} [MeasurableSpace α]
    (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (k n : ℕ) : Measure (TwoTapeList α) :=
  (n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, nthCommonLaw ν L (k+i)

instance windowCommonLaw_probability {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (k n : ℕ) [NeZero n] : IsProbabilityMeasure (windowCommonLaw ν L k n) := by
  constructor
  simp only [windowCommonLaw,Measure.smul_apply,smul_eq_mul,Measure.finsetSum_apply,measure_univ,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast NeZero.ne n) (by finiteness)

noncomputable def twoListWeight {α : Type*} [MeasurableSpace α]
    (ν : Bool → Measure α) (a : TwoTapeList α) : ℝ≥0∞ :=
  ∏ b : Bool, ∏ i : Fin (a b).1, ν b {(a b).2 i}

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

def InCountWindow {α : Type*} (L : Bool → α → ℕ) (k n : ℕ) (a : TwoTapeList α) : Prop :=
  BalancedList L a ∧ k ≤ listCommonCount L a ∧ listCommonCount L a < k+n

lemma windowCommonLaw_atom {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (k n : ℕ) (a : TwoTapeList α) :
    windowCommonLaw ν L k n {a} =
      (by classical exact if InCountWindow L k n a then (n : ℝ≥0∞)⁻¹ * twoListWeight ν a else 0) := by
  classical
  rw [windowCommonLaw,Measure.smul_apply,smul_eq_mul,Measure.finsetSum_apply]
  simp_rw [nthCommonLaw_atom ν L hL he]
  by_cases ha : InCountWindow L k n a
  · rw [ite_eq_left ha]
    congr 1
    let i : Fin n := ⟨listCommonCount L a-k,by obtain ⟨_,_,_⟩ := ha;omega⟩
    rw [Finset.sum_eq_single i]
    · exact ite_eq_left ⟨ha.1,by dsimp [i];obtain ⟨_,_,_⟩ := ha;omega⟩
    · intro j _ hji
      apply ite_eq_right
      rintro ⟨_,hj⟩
      apply hji
      apply Fin.ext
      dsimp [i]
      omega
    · simp
  · rw [ite_eq_right ha]
    have hh : ∑ i : Fin n, (if BalancedList L a ∧ listCommonCount L a = k+↑i then
        (∏ b : Bool, ∏ j : Fin (a b).1, ν b {(a b).2 j}) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      apply ite_eq_right
      rintro ⟨hb,hc⟩
      exact ha ⟨hb,by omega,by omega⟩
    rw [hh,mul_zero]

lemma windowCommonLaw_ae_window {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (k n : ℕ) : ∀ᵐ a ∂windowCommonLaw ν L k n, InCountWindow L k n a := by
  classical
  filter_upwards [ae_atom_pos (windowCommonLaw ν L k n)] with a ha
  by_contra hn
  rw [windowCommonLaw_atom ν L hL he,ite_eq_right hn] at ha
  exact ha rfl

noncomputable def pairBridgeLaw {α : Type*} [MeasurableSpace α]
    (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (H : ℕ) : Measure (TwoTapeList α) :=
  Measure.pi (fun b => bridgeListLaw (ν b) (L b) H)

lemma pairBridgeLaw_probability {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (H : ℕ)
    (hH : ∀ b, Measure.infinitePi (fun _ : ℕ => ν b) (renewalCut (L b) H) ≠ 0) :
    IsProbabilityMeasure (pairBridgeLaw ν L H) := by
  let : ∀ b, IsProbabilityMeasure (bridgeListLaw (ν b) (L b) H) :=
    fun b => bridgeListLaw_probability (ν b) (L b) H (hH b)
  unfold pairBridgeLaw
  infer_instance

instance bridgeListLaw_finite {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Measure α) [IsProbabilityMeasure ν]
    (L : α → ℕ) (H : ℕ) : IsFiniteMeasure (bridgeListLaw ν L H) := by
  constructor
  rw [bridgeListLaw,Measure.smul_apply,smul_eq_mul,bridgeListMeasure_mass]
  exact (ENNReal.inv_mul_le_one _).trans_lt (by simp)

lemma pairBridgeLaw_atom {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a) (H : ℕ) (a : TwoTapeList α)
    (ha : ∀ b, listHeight (L b) (a b) = H) :
    pairBridgeLaw ν L H {a} =
      (∏ b : Bool, Measure.infinitePi (fun _ : ℕ => ν b) (renewalCut (L b) H))⁻¹ * twoListWeight ν a := by
  classical
  have hs : ({a} : Set (TwoTapeList α)) = Set.univ.pi (fun b => {a b}) := by
    ext x
    simp only [Set.mem_singleton_iff,Set.mem_pi,Set.mem_univ,true_implies]
    exact funext_iff
  rw [pairBridgeLaw,hs,Measure.pi_pi]
  simp_rw [bridgeListLaw_atom (ν _) (L _) (hL _) H _ (ha _)]
  rw [Finset.prod_mul_distrib]
  change _ * twoListWeight ν a = _ * twoListWeight ν a
  congr 1
  simp only [Fintype.prod_bool]
  exact (ENNReal.mul_inv (Or.inr (measure_ne_top _ _)) (Or.inl (measure_ne_top _ _))).symm

noncomputable def chunkHeight {α : Type*} (L : Bool → α → ℕ) (a : TwoTapeList α) : ℕ :=
  listHeight (L false) (a false)

noncomputable def pairBridgeKernel {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) : Kernel ℕ (TwoTapeList α) where
  toFun := pairBridgeLaw ν L
  measurable' := measurable_of_countable _

lemma pairBridgeKernel_markov {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ)
    (hu : ∀ H b, Measure.infinitePi (fun _ : ℕ => ν b) (renewalCut (L b) H) ≠ 0) :
    IsMarkovKernel (pairBridgeKernel ν L) :=
  ⟨fun H => pairBridgeLaw_probability ν L H (hu H)⟩

lemma map_graph_atom {α β : Type*} [Countable α] [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (μ : Measure α) (f : α → β) (x : α) : μ.map (fun a => (f a,a)) {(f x,x)} = μ {x} := by
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  congr 1
  ext a
  simp only [Set.mem_preimage,Set.mem_singleton_iff,Prod.mk.injEq,and_iff_right_iff_imp]
  rintro rfl
  rfl

lemma map_graph_fst {α β : Type*} [Countable α] [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (μ : Measure α) (f : α → β) : (μ.map (fun a => (f a,a))).fst = μ.map f := by
  rw [Measure.fst,Measure.map_map measurable_fst (measurable_of_countable _)]
  rfl

lemma window_reference_ac {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (k n : ℕ) [NeZero n]
    (hu : ∀ H b, Measure.infinitePi (fun _ : ℕ => ν b) (renewalCut (L b) H) ≠ 0) :
    (windowCommonLaw ν L k n).map (fun a => (chunkHeight L a,a)) ≪
      (windowCommonLaw ν L k n).map (chunkHeight L) ⊗ₘ pairBridgeKernel ν L := by
  classical
  let P := windowCommonLaw ν L k n
  let H := chunkHeight L
  let κ := pairBridgeKernel ν L
  let : IsMarkovKernel κ := pairBridgeKernel_markov ν L hu
  have hP : IsProbabilityMeasure P := inferInstance
  apply absolutelyContinuous_of_atoms
  rintro ⟨h,a⟩ hz
  by_contra hap
  have hg : h = H a := by
    by_contra hne
    apply hap
    rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
    have hh : (fun a => (H a,a)) ⁻¹' {(h,a)} = ∅ := by
      ext b
      simp only [Set.mem_preimage,Set.mem_singleton_iff,Prod.mk.injEq,Set.mem_empty_iff_false,iff_false,not_and]
      intro hh hb
      exact hne (hb ▸ hh.symm)
    rw [hh,measure_empty]
  subst h
  rw [map_graph_atom] at hap
  have hw : InCountWindow L k n a := by
    by_contra hn
    exact hap (by rw [windowCommonLaw_atom ν L hL he,ite_eq_right hn])
  have hwa : twoListWeight ν a ≠ 0 := by
    intro hz
    apply hap
    rw [windowCommonLaw_atom ν L hL he,ite_eq_left hw,hz,mul_zero]
  have hx : (P.map H) {H a} ≠ 0 := fun hh => hap (le_antisymm ((atom_le_map P H (measurable_of_countable _) a).trans hh.le) bot_le)
  have hκ : κ (H a) {a} ≠ 0 := by
    change pairBridgeLaw ν L (H a) {a} ≠ 0
    rw [pairBridgeLaw_atom ν L hL (H a) a hw.1]
    exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (ENNReal.prod_ne_top (fun _ _ => measure_ne_top _ _))) hwa
  exact (mul_ne_zero hx hκ) (by simpa only [compProd_atom] using hz)

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

noncomputable def renewalPairMass {α : Type*} [MeasurableSpace α]
    (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)] (L : Bool → α → ℕ) (H : ℕ) : ℝ≥0∞ :=
  ∏ b : Bool, Measure.infinitePi (fun _ : ℕ => ν b) (renewalCut (L b) H)

lemma renewalPairMass_le_one {α : Type*} [MeasurableSpace α]
    (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)] (L : Bool → α → ℕ) (H : ℕ) :
    renewalPairMass ν L H ≤ 1 := Finset.prod_le_one' (fun _ _ => prob_le_one)

lemma window_reference_llr {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (k n : ℕ) [NeZero n]
    (hu : ∀ H b, Measure.infinitePi (fun _ : ℕ => ν b) (renewalCut (L b) H) ≠ 0) :
    let P := windowCommonLaw ν L k n
    let H := chunkHeight L
    let ρ := P.map (fun a => (H a,a))
    let Q := P.map H ⊗ₘ pairBridgeKernel ν L
    (fun a => llr ρ Q (H a,a)) =ᵐ[P] fun a =>
      Real.log (renewalPairMass ν L (H a)).toReal - Real.log (n : ℝ) + informationOf P H a := by
  dsimp only
  let P := windowCommonLaw ν L k n
  let H := chunkHeight L
  let ρ := P.map (fun a => (H a,a))
  let κ := pairBridgeKernel ν L
  let : IsMarkovKernel κ := pairBridgeKernel_markov ν L hu
  let : IsProbabilityMeasure ρ := probabilityMeasure_map (measurable_of_countable _).aemeasurable
  have hmap : MeasurePreserving (fun a => (H a,a)) P ρ := ⟨measurable_of_countable _,rfl⟩
  have hl := hmap.quasiMeasurePreserving.ae (llr_atom ρ (P.map H ⊗ₘ κ)
    (window_reference_ac ν L hL he k n hu))
  filter_upwards [hl,ae_atom_pos P,windowCommonLaw_ae_window ν L hL he k n] with a hl ha hw
  have hw0 : twoListWeight ν a ≠ 0 := by
    intro hz
    apply ha
    change windowCommonLaw ν L k n {a} = 0
    rw [windowCommonLaw_atom ν L hL he,ite_eq_left hw,hz,mul_zero]
  have hwfin : twoListWeight ν a ≠ ∞ := ENNReal.prod_ne_top (fun _ _ =>
    ENNReal.prod_ne_top (fun _ _ => measure_ne_top _ _))
  have hwp : 0 < (twoListWeight ν a).toReal := ENNReal.toReal_pos hw0 hwfin
  have hr0 : renewalPairMass ν L (H a) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun b _ => hu _ b)
  have hrfin : renewalPairMass ν L (H a) ≠ ∞ := ne_of_lt ((renewalPairMass_le_one ν L _).trans_lt (by simp))
  have hrp : 0 < (renewalPairMass ν L (H a)).toReal := ENNReal.toReal_pos hr0 hrfin
  have hpH : 0 < (P.map H).real {H a} := ENNReal.toReal_pos
    (ne_zero_of_lt ((pos_iff_ne_zero.mpr ha).trans_le (atom_le_map P H (measurable_of_countable _) a))) (by finiteness)
  have hρ : ρ.real {(H a,a)} = (1/(n : ℝ))*(twoListWeight ν a).toReal := by
    rw [measureReal_def,map_graph_atom]
    change (windowCommonLaw ν L k n {a}).toReal = _
    rw [windowCommonLaw_atom ν L hL he,ite_eq_left hw,ENNReal.toReal_mul,ENNReal.toReal_inv]
    simp
  have hQ : (P.map H ⊗ₘ κ).real {(H a,a)} =
      (P.map H).real {H a} * ((renewalPairMass ν L (H a)).toReal)⁻¹ * (twoListWeight ν a).toReal := by
    rw [measureReal_def,compProd_atom]
    change (_ * pairBridgeLaw ν L (H a) {a}).toReal = _
    rw [pairBridgeLaw_atom ν L hL (H a) a hw.1]
    simp only [ENNReal.toReal_mul,ENNReal.toReal_inv,measureReal_def,renewalPairMass,mul_assoc]
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  rw [hl,hρ,hQ,Real.log_mul (one_div_ne_zero hn) hwp.ne',
    Real.log_mul (mul_ne_zero hpH.ne' (inv_ne_zero hrp.ne')) hwp.ne',
    Real.log_mul hpH.ne' (inv_ne_zero hrp.ne'),Real.log_inv,Real.log_div one_ne_zero hn,Real.log_one]
  change _ = _ + (-Real.log ((P.map H).real {H a}))
  ring

lemma window_reference_entropy_bound {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (k n : ℕ) [NeZero n]
    (hu : ∀ H b, Measure.infinitePi (fun _ : ℕ => ν b) (renewalCut (L b) H) ≠ 0)
    (c : ℝ) (hc : 0 < c) (hlo : ∀ H, ENNReal.ofReal c ≤ renewalPairMass ν L H)
    (hH : Integrable (informationOf (windowCommonLaw ν L k n) (chunkHeight L)) (windowCommonLaw ν L k n)) :
    let P := windowCommonLaw ν L k n
    let H := chunkHeight L
    let ρ := P.map (fun a => (H a,a))
    let Q := P.map H ⊗ₘ pairBridgeKernel ν L
    InformationTheory.klDiv ρ Q ≠ ∞ ∧
      (InformationTheory.klDiv ρ Q).toReal ≤ entropyOf P H - Real.log (n : ℝ) := by
  dsimp only
  let P := windowCommonLaw ν L k n
  let H := chunkHeight L
  let ρ := P.map (fun a => (H a,a))
  let κ := pairBridgeKernel ν L
  let : IsMarkovKernel κ := pairBridgeKernel_markov ν L hu
  let : IsProbabilityMeasure ρ := probabilityMeasure_map (measurable_of_countable _).aemeasurable
  let Q := P.map H ⊗ₘ κ
  let : IsProbabilityMeasure (P.map H) := probabilityMeasure_map (measurable_of_countable _).aemeasurable
  let : IsProbabilityMeasure Q := inferInstance
  have hlow (h : ℕ) : c ≤ (renewalPairMass ν L h).toReal := by
    simpa only [ENNReal.toReal_ofReal (le_of_lt hc)] using
      ENNReal.toReal_mono (ne_of_lt ((renewalPairMass_le_one ν L h).trans_lt (by simp))) (hlo h)
  have hupp (h : ℕ) : (renewalPairMass ν L h).toReal ≤ 1 := by
    exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using renewalPairMass_le_one ν L h)
  have hlog (h : ℕ) : Real.log c ≤ Real.log (renewalPairMass ν L h).toReal ∧
      Real.log (renewalPairMass ν L h).toReal ≤ 0 :=
    ⟨Real.log_le_log hc (hlow h),Real.log_nonpos ENNReal.toReal_nonneg (hupp h)⟩
  have hi : Integrable (fun a => Real.log (renewalPairMass ν L (H a)).toReal) P := by
    apply (integrable_const |Real.log c|).mono' (measurable_of_countable _).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun a => by
      rw [Real.norm_eq_abs,abs_of_nonpos (hlog _).2]
      exact (neg_le_neg (hlog _).1).trans (neg_le_abs _))
  have hid : (fun a => llr ρ Q (H a,a)) =ᵐ[P] fun a =>
      Real.log (renewalPairMass ν L (H a)).toReal - Real.log (n : ℝ) + informationOf P H a :=
    window_reference_llr ν L hL he k n hu
  have hii : Integrable (fun a => llr ρ Q (H a,a)) P :=
    ((hi.sub (integrable_const _)).add hH).congr hid.symm
  have hiρ : Integrable (llr ρ Q) ρ :=
    (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
      (measurable_of_countable _).aemeasurable).mpr hii
  have hac : ρ ≪ Q := window_reference_ac ν L hL he k n hu
  refine ⟨InformationTheory.klDiv_ne_top_iff.mpr ⟨hac,hiρ⟩,?_⟩
  have hkl := InformationTheory.toReal_klDiv hac hiρ
  simp only [probReal_univ,add_sub_cancel_right] at hkl
  rw [hkl,show (∫ x, llr ρ Q x ∂ρ) = ∫ a, llr ρ Q (H a,a) ∂P from
    integral_map_of_stronglyMeasurable (measurable_of_countable _) (measurable_of_countable _).stronglyMeasurable,
    integral_congr_ae hid]
  have hbound := integral_mono_ae ((hi.sub (integrable_const (Real.log (n : ℝ)))).add hH)
    (hH.sub (integrable_const (Real.log (n : ℝ))))
    (Filter.Eventually.of_forall (fun a => by
      dsimp only [Pi.add_apply,Pi.sub_apply]
      linarith [(hlog (H a)).2]))
  change (∫ a, Real.log (renewalPairMass ν L (H a)).toReal - Real.log (n : ℝ) + informationOf P H a ∂P) ≤
    ∫ a, informationOf P H a - Real.log (n : ℝ) ∂P at hbound
  rw [integral_sub hH (integrable_const (Real.log (n : ℝ)))] at hbound
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul,entropyOf] using hbound

lemma commonDepth_integrable {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (hi : Integrable (fun Z => (firstCommonWidth L Z : ℝ)) (twoTapeLaw ν)) (r : ℕ) :
    Integrable (fun Z => (commonDepth L Z r : ℝ)) (twoTapeLaw ν) := by
  simp only [commonDepth,Nat.cast_sum]
  apply integrable_finsetSum
  intro i _
  exact ((commonRestart_measurePreserving ν L hL he).iterate i).integrable_comp_of_integrable hi

lemma commonDepth_integral {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (hi : Integrable (fun Z => (firstCommonWidth L Z : ℝ)) (twoTapeLaw ν)) (r : ℕ) :
    (∫ Z, (commonDepth L Z r : ℝ) ∂twoTapeLaw ν) =
      (r : ℝ) * ∫ Z, (firstCommonWidth L Z : ℝ) ∂twoTapeLaw ν := by
  simp only [commonDepth,Nat.cast_sum]
  have hii (i : ℕ) : Integrable (fun Z => (firstCommonWidth L ((commonRestart L)^[i] Z) : ℝ)) (twoTapeLaw ν) :=
    ((commonRestart_measurePreserving ν L hL he).iterate i).integrable_comp_of_integrable hi
  rw [integral_finsetSum (Finset.range r) (fun i _ => hii i)]
  have heq (i : ℕ) : (∫ Z, (firstCommonWidth L ((commonRestart L)^[i] Z) : ℝ) ∂twoTapeLaw ν) =
      ∫ Z, (firstCommonWidth L Z : ℝ) ∂twoTapeLaw ν := by
    have hp := (commonRestart_measurePreserving ν L hL he).iterate i
    have hm : Measurable (fun Z : TwoTape α => (firstCommonWidth L Z : ℝ)) :=
      (measurable_of_countable Nat.cast).comp (measurable_firstCommonWidth L)
    conv_rhs => rw [← hp.map_eq]
    exact (integral_map_of_stronglyMeasurable hp.measurable hm.stronglyMeasurable).symm
  simp_rw [heq]
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]

lemma nthCommonList_height {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i)))
    (he : ∀ r, ∃ H, 0 < H ∧ ((commonRestart L)^[r] Z) ∈ commonCut L H)
    (r : ℕ) : chunkHeight L (nthCommonList L r Z) = commonDepth L Z r := by
  have hc := (commonDepth_spec L Z hZ he r).1
  exact ((commonCutList_atom_iff L _ Z hZ (nthCommonList L r Z)).mp ⟨hc,rfl⟩).1 false

lemma nthCommonList_height_ae {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H) (r : ℕ) :
    (fun Z => chunkHeight L (nthCommonList L r Z)) =ᵐ[twoTapeLaw ν] fun Z => commonDepth L Z r := by
  filter_upwards [ae_twoTape_prop ν (fun b a => 0 < L b a)
    (fun b => measurableSet_lt measurable_const (measurable_of_countable (L b))) hL,
    ae_common_iterates ν L hL he] with Z hZ hiter
  exact nthCommonList_height L Z hZ hiter r

lemma nthCommonLaw_height_integrable {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (hi : Integrable (fun Z => (firstCommonWidth L Z : ℝ)) (twoTapeLaw ν)) (r : ℕ) :
    Integrable (fun a => (chunkHeight L a : ℝ)) (nthCommonLaw ν L r) := by
  apply (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
    (measurable_nthCommonList L r).aemeasurable).mpr
  apply (commonDepth_integrable ν L hL he hi r).congr
  filter_upwards [nthCommonList_height_ae ν L hL he r] with Z hZ
  change (commonDepth L Z r : ℝ) = (chunkHeight L (nthCommonList L r Z) : ℝ)
  exact_mod_cast hZ.symm

lemma nthCommonLaw_height_integral {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (hi : Integrable (fun Z => (firstCommonWidth L Z : ℝ)) (twoTapeLaw ν)) (r : ℕ) :
    (∫ a, (chunkHeight L a : ℝ) ∂nthCommonLaw ν L r) =
      (r : ℝ) * ∫ Z, (firstCommonWidth L Z : ℝ) ∂twoTapeLaw ν := by
  rw [nthCommonLaw,integral_map_of_stronglyMeasurable (measurable_nthCommonList L r)
    (measurable_of_countable _).stronglyMeasurable,← commonDepth_integral ν L hL he hi r]
  apply integral_congr_ae
  filter_upwards [nthCommonList_height_ae ν L hL he r] with Z hZ
  exact_mod_cast hZ

lemma windowCommonLaw_height_integrable {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (hi : Integrable (fun Z => (firstCommonWidth L Z : ℝ)) (twoTapeLaw ν)) (k n : ℕ) [NeZero n] :
    Integrable (fun a => (chunkHeight L a : ℝ)) (windowCommonLaw ν L k n) := by
  apply Integrable.smul_measure _ (ENNReal.inv_ne_top.mpr (by exact_mod_cast NeZero.ne n))
  apply integrable_finsetSum_measure.mpr
  intro i _
  exact nthCommonLaw_height_integrable ν L hL he hi (k+i)

lemma windowCommonLaw_height_mean {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (hi : Integrable (fun Z => (firstCommonWidth L Z : ℝ)) (twoTapeLaw ν)) (k n : ℕ) [NeZero n] :
    (∫ a, (chunkHeight L a : ℝ) ∂windowCommonLaw ν L k n) ≤
      ((k+n : ℕ) : ℝ) * ∫ Z, (firstCommonWidth L Z : ℝ) ∂twoTapeLaw ν := by
  rw [windowCommonLaw,integral_smul_measure,integral_finsetSum_measure
    (μ := fun i : Fin n => nthCommonLaw ν L (k+i)) (s := Finset.univ)
    (fun i _ => nthCommonLaw_height_integrable ν L hL he hi (k+i))]
  simp only [ENNReal.toReal_inv,ENNReal.toReal_natCast,smul_eq_mul]
  simp_rw [nthCommonLaw_height_integral ν L hL he hi]
  have hm : 0 ≤ ∫ Z, (firstCommonWidth L Z : ℝ) ∂twoTapeLaw ν := integral_nonneg (fun _ => Nat.cast_nonneg _)
  have hn : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  calc
    _ ≤ (n : ℝ)⁻¹ * ∑ _ : Fin n,
        ((k+n : ℕ) : ℝ) * ∫ Z, (firstCommonWidth L Z : ℝ) ∂twoTapeLaw ν := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt (inv_pos.mpr hn))
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.add_le_add_left (le_of_lt i.isLt) k) hm
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];field_simp

lemma window_entropy_uniform {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (hi : Integrable (fun Z => (firstCommonWidth L Z : ℝ)) (twoTapeLaw ν)) (k n : ℕ) [NeZero n]
    (hk : k ≤ 7*n) :
    Integrable (informationOf (windowCommonLaw ν L k n) (chunkHeight L)) (windowCommonLaw ν L k n) ∧
      entropyOf (windowCommonLaw ν L k n) (chunkHeight L) - Real.log (n : ℝ) ≤
        1 + Real.log (8 * ((∫ Z, (firstCommonWidth L Z : ℝ) ∂twoTapeLaw ν)+1)+1) := by
  let m := ∫ Z, (firstCommonWidth L Z : ℝ) ∂twoTapeLaw ν
  have hm : 0 ≤ m := integral_nonneg (fun _ => Nat.cast_nonneg _)
  have hn : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  let A := 8*(m+1)
  have hA : 0 < A := by dsimp [A];positivity
  have hmean : (∫ a, (chunkHeight L a : ℝ) ∂windowCommonLaw ν L k n) ≤ A*n := by
    calc
      _ ≤ ((k+n : ℕ) : ℝ)*m := windowCommonLaw_height_mean ν L hL he hi k n
      _ ≤ (8*(n:ℝ))*m := mul_le_mul_of_nonneg_right (by exact_mod_cast (show k+n ≤ 8*n by omega)) hm
      _ ≤ A*n := by dsimp [A];nlinarith
  have hh := entropyOf_nat_moment (windowCommonLaw ν L k n) (chunkHeight L)
    (windowCommonLaw_height_integrable ν L hL he hi k n) (A*n) (mul_pos hA hn) hmean
  refine ⟨hh.1,?_⟩
  have hlog : Real.log (A*(n:ℝ)+1) ≤ Real.log (A+1) + Real.log (n:ℝ) := by
    rw [← Real.log_mul (by positivity : A+1 ≠ 0) (ne_of_gt hn)]
    exact Real.log_le_log (by positivity) (by nlinarith)
  change _ ≤ 1+Real.log (A+1)
  linarith [hh.2]

lemma window_kl_uniform {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (hi : Integrable (fun Z => (firstCommonWidth L Z : ℝ)) (twoTapeLaw ν))
    (hu : ∀ H b, Measure.infinitePi (fun _ : ℕ => ν b) (renewalCut (L b) H) ≠ 0)
    (c : ℝ) (hc : 0 < c) (hlo : ∀ H, ENNReal.ofReal c ≤ renewalPairMass ν L H)
    (k n : ℕ) [NeZero n] (hk : k ≤ 7*n) :
    let P := windowCommonLaw ν L k n
    let H := chunkHeight L
    let ρ := P.map (fun a => (H a,a))
    let Q := P.map H ⊗ₘ pairBridgeKernel ν L
    InformationTheory.klDiv ρ Q ≠ ∞ ∧
      (InformationTheory.klDiv ρ Q).toReal ≤
        1 + Real.log (8 * ((∫ Z, (firstCommonWidth L Z : ℝ) ∂twoTapeLaw ν)+1)+1) := by
  have hh := window_entropy_uniform ν L hL he hi k n hk
  have hd := window_reference_entropy_bound ν L hL he k n hu c hc hlo hh.1
  exact ⟨hd.1, hd.2.trans hh.2⟩

lemma klDiv_map_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (e : α ≃ᵐ β) :
    InformationTheory.klDiv (μ.map e) (ν.map e) = InformationTheory.klDiv μ ν := by
  apply le_antisymm (InformationTheory.klDiv_map_le μ ν e.measurable)
  have h := InformationTheory.klDiv_map_le (μ.map e) (ν.map e) e.symm.measurable
  simpa only [Measure.map_map e.symm.measurable e.measurable,
    show e.symm ∘ e = id from funext e.symm_apply_apply,Measure.map_id] using h

lemma klDiv_product {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ ν : Measure α) (ρ η : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure η] :
    InformationTheory.klDiv (μ.prod ρ) (ν.prod η) =
      InformationTheory.klDiv μ ν + InformationTheory.klDiv ρ η := by
  have h := InformationTheory.klDiv_compProd_eq_add μ ν (Kernel.const α ρ) (Kernel.const α η)
  simp only [Measure.compProd_const] at h
  rw [h]
  congr 1
  have hs := klDiv_map_equiv (μ.prod ρ) (μ.prod η) MeasurableEquiv.prodComm
  change InformationTheory.klDiv ((μ.prod ρ).map Prod.swap) ((μ.prod η).map Prod.swap) = _ at hs
  rw [Measure.prod_swap,Measure.prod_swap] at hs
  rw [← hs,← Measure.compProd_const,← Measure.compProd_const]
  exact InformationTheory.klDiv_compProd_left ρ η (Kernel.const β μ)

lemma product_graph {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (f : α → γ) (g : β → δ) (hf : Measurable f) (hg : Measurable g) :
    (μ.prod ν).map (fun a => ((f a.1,g a.2),a)) =
      ((μ.map (fun a => (f a,a))).prod (ν.map (fun b => (g b,b)))).map
        (fun p => ((p.1.1,p.2.1),(p.1.2,p.2.2))) := by
  rw [Measure.map_prod_map μ ν (show Measurable (fun a => (f a,a)) from hf.prodMk measurable_id)
    (show Measurable (fun b => (g b,b)) from hg.prodMk measurable_id),
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

def interlace {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ] : (α × β) × (γ × δ) ≃ᵐ (α × γ) × (β × δ) where
  toEquiv := Equiv.prodProdProdComm α β γ δ
  measurable_toFun := by dsimp [Equiv.prodProdProdComm];fun_prop
  measurable_invFun := by dsimp [Equiv.prodProdProdComm];fun_prop

lemma compProd_product {α β γ δ : Type*} [Countable α] [Countable β] [Countable γ] [Countable δ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [MeasurableSingletonClass γ] [MeasurableSingletonClass δ]
    (μ : Measure α) (ν : Measure γ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (κ : Kernel α β) (η : Kernel γ δ) [IsMarkovKernel κ] [IsMarkovKernel η] :
    (μ.prod ν) ⊗ₘ (κ ∥ₖ η) = ((μ ⊗ₘ κ).prod (ν ⊗ₘ η)).map interlace := by
  apply Measure.ext_of_singleton
  rintro ⟨⟨a,c⟩,⟨b,d⟩⟩
  rw [compProd_atom,Kernel.parallelComp_apply,Measure.map_apply interlace.measurable (measurableSet_singleton _)]
  have hh : interlace ⁻¹' {((a,c),(b,d))} = {((a,b),(c,d))} := by
    ext p
    simp only [Set.mem_preimage,Set.mem_singleton_iff,interlace,MeasurableEquiv.coe_mk,
      Equiv.prodProdProdComm_apply,Prod.ext_iff]
    tauto
  rw [hh]
  simp only [← Set.singleton_prod_singleton,Measure.prod_prod]
  rw [Set.singleton_prod_singleton,Set.singleton_prod_singleton,compProd_atom,compProd_atom]
  ring

lemma graph_product_kl {α β γ δ : Type*} [Countable α] [Countable β] [Countable γ] [Countable δ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [MeasurableSingletonClass γ] [MeasurableSingletonClass δ]
    (μ : Measure α) (ν : Measure γ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : α → β) (g : γ → δ)
    (κ : Kernel β α) (η : Kernel δ γ) [IsMarkovKernel κ] [IsMarkovKernel η] :
    InformationTheory.klDiv ((μ.prod ν).map (fun a => ((f a.1,g a.2),a)))
      (((μ.prod ν).map (fun a => (f a.1,g a.2))) ⊗ₘ (κ ∥ₖ η)) =
    InformationTheory.klDiv (μ.map (fun a => (f a,a))) ((μ.map f) ⊗ₘ κ) +
      InformationTheory.klDiv (ν.map (fun a => (g a,a))) ((ν.map g) ⊗ₘ η) := by
  have : IsProbabilityMeasure (μ.map f) := probabilityMeasure_map (measurable_of_countable _).aemeasurable
  have : IsProbabilityMeasure (ν.map g) := probabilityMeasure_map (measurable_of_countable _).aemeasurable
  have : IsProbabilityMeasure (μ.map (fun a => (f a,a))) := probabilityMeasure_map (measurable_of_countable _).aemeasurable
  have : IsProbabilityMeasure (ν.map (fun a => (g a,a))) := probabilityMeasure_map (measurable_of_countable _).aemeasurable
  have hm : (μ.prod ν).map (fun a => (f a.1,g a.2)) = (μ.map f).prod (ν.map g) :=
    (Measure.map_prod_map μ ν (measurable_of_countable _) (measurable_of_countable _)).symm
  rw [hm,compProd_product,product_graph μ ν f g (measurable_of_countable _) (measurable_of_countable _)]
  change InformationTheory.klDiv (Measure.map interlace _) (Measure.map interlace _) = _
  rw [klDiv_map_equiv,klDiv_product]

abbrev ThreeChunk (α : Type*) := TwoTapeList α × (TwoTapeList α × TwoTapeList α)

noncomputable def threeChunkLaw {α : Type*} [MeasurableSpace α]
    (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)] (L : Bool → α → ℕ) (n : ℕ) :
    Measure (ThreeChunk α) :=
  (windowCommonLaw ν L n n).prod ((windowCommonLaw ν L (7*n) n).prod (windowCommonLaw ν L n n))

instance threeChunkLaw_probability {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (n : ℕ) [NeZero n] : IsProbabilityMeasure (threeChunkLaw ν L n) :=
  inferInstanceAs (IsProbabilityMeasure ((windowCommonLaw ν L n n).prod
    ((windowCommonLaw ν L (7*n) n).prod (windowCommonLaw ν L n n))))

noncomputable def threeHeight {α : Type*} (L : Bool → α → ℕ) (a : ThreeChunk α) : ℕ × (ℕ × ℕ) :=
  (chunkHeight L a.1,chunkHeight L a.2.1,chunkHeight L a.2.2)

noncomputable def threeBridgeKernel {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) : Kernel (ℕ × (ℕ × ℕ)) (ThreeChunk α) :=
  pairBridgeKernel ν L ∥ₖ (pairBridgeKernel ν L ∥ₖ pairBridgeKernel ν L)

lemma threeBridgeKernel_markov {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ)
    (hu : ∀ H b, Measure.infinitePi (fun _ : ℕ => ν b) (renewalCut (L b) H) ≠ 0) :
    IsMarkovKernel (threeBridgeKernel ν L) := by
  let : IsMarkovKernel (pairBridgeKernel ν L) := pairBridgeKernel_markov ν L hu
  unfold threeBridgeKernel
  infer_instance

lemma threeChunk_kl_uniform {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (hi : Integrable (fun Z => (firstCommonWidth L Z : ℝ)) (twoTapeLaw ν))
    (hu : ∀ H b, Measure.infinitePi (fun _ : ℕ => ν b) (renewalCut (L b) H) ≠ 0)
    (c : ℝ) (hc : 0 < c) (hlo : ∀ H, ENNReal.ofReal c ≤ renewalPairMass ν L H)
    (n : ℕ) [NeZero n] :
    let P := threeChunkLaw ν L n
    let H := threeHeight L
    let ρ := P.map (fun a => (H a,a))
    let Q := P.map H ⊗ₘ threeBridgeKernel ν L
    InformationTheory.klDiv ρ Q ≠ ∞ ∧
      (InformationTheory.klDiv ρ Q).toReal ≤
        3 * (1+Real.log (8*((∫ Z, (firstCommonWidth L Z : ℝ) ∂twoTapeLaw ν)+1)+1)) := by
  dsimp only
  let : IsMarkovKernel (pairBridgeKernel ν L) := pairBridgeKernel_markov ν L hu
  have hl := window_kl_uniform ν L hL he hi hu c hc hlo n n (by omega)
  have hm := window_kl_uniform ν L hL he hi hu c hc hlo (7*n) n le_rfl
  have hid : InformationTheory.klDiv
      ((threeChunkLaw ν L n).map (fun a => (threeHeight L a,a)))
      ((threeChunkLaw ν L n).map (threeHeight L) ⊗ₘ threeBridgeKernel ν L) =
      InformationTheory.klDiv
        ((windowCommonLaw ν L n n).map (fun a => (chunkHeight L a,a)))
        ((windowCommonLaw ν L n n).map (chunkHeight L) ⊗ₘ pairBridgeKernel ν L) +
      (InformationTheory.klDiv
        ((windowCommonLaw ν L (7*n) n).map (fun a => (chunkHeight L a,a)))
        ((windowCommonLaw ν L (7*n) n).map (chunkHeight L) ⊗ₘ pairBridgeKernel ν L) +
      InformationTheory.klDiv
        ((windowCommonLaw ν L n n).map (fun a => (chunkHeight L a,a)))
        ((windowCommonLaw ν L n n).map (chunkHeight L) ⊗ₘ pairBridgeKernel ν L)) := by
    unfold threeChunkLaw threeHeight threeBridgeKernel
    rw [graph_product_kl (windowCommonLaw ν L n n)
      ((windowCommonLaw ν L (7*n) n).prod (windowCommonLaw ν L n n))
      (chunkHeight L) (fun p : TwoTapeList α × TwoTapeList α =>
        (chunkHeight L p.1,chunkHeight L p.2))
      (pairBridgeKernel ν L) (pairBridgeKernel ν L ∥ₖ pairBridgeKernel ν L),
      graph_product_kl (windowCommonLaw ν L (7*n) n) (windowCommonLaw ν L n n)
      (chunkHeight L) (chunkHeight L) (pairBridgeKernel ν L) (pairBridgeKernel ν L)]
  rw [hid]
  exact ⟨ENNReal.add_ne_top.mpr ⟨hl.1,ENNReal.add_ne_top.mpr ⟨hm.1,hl.1⟩⟩,by
    rw [ENNReal.toReal_add hl.1 (ENNReal.add_ne_top.mpr ⟨hm.1,hl.1⟩),
      ENNReal.toReal_add hm.1 hl.1]
    linarith [hl.2,hm.2]⟩

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

section EntropyLawTransforms
variable {Ω Ξ α β γ : Type*} [Countable Ω] [Countable Ξ] [Countable α] [Countable β]
  [Countable γ] [MeasurableSpace Ω] [MeasurableSpace Ξ] [MeasurableSpace α]
  [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSingletonClass Ω]
  [MeasurableSingletonClass Ξ] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
  [MeasurableSingletonClass γ]

omit [Countable α] [MeasurableSingletonClass α] in
lemma informationOf_map (μ : Measure Ω) (F : Ω → Ξ) (X : Ξ → α) :
    informationOf (μ.map F) X ∘ F = informationOf μ (X ∘ F) := by
  funext ω
  simp only [informationOf,Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
    Function.comp_apply]

omit [Countable α] [MeasurableSingletonClass α] in
lemma entropyOf_map (μ : Measure Ω) (F : Ω → Ξ) (X : Ξ → α) :
    entropyOf (μ.map F) X = entropyOf μ (X ∘ F) := by
  unfold entropyOf
  rw [integral_map_of_stronglyMeasurable (measurable_of_countable _)
    (measurable_of_countable _).stronglyMeasurable]
  exact congrArg (fun f => ∫ ω, f ω ∂μ) (informationOf_map μ F X)

omit [Countable α] [Countable β] [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
lemma conditionedEntropy_map (μ : Measure Ω) (F : Ω → Ξ) (X : Ξ → α) (Y : Ξ → β) :
    conditionedEntropy (μ.map F) X Y = conditionedEntropy μ (X ∘ F) (Y ∘ F) := by
  unfold conditionedEntropy conditionedInformation
  rw [integral_map_of_stronglyMeasurable (measurable_of_countable _)
    (measurable_of_countable _).stronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [] with ω
  change (informationOf (μ.map F) (fun ξ => (Y ξ,X ξ)) ∘ F) ω -
    (informationOf (μ.map F) Y ∘ F) ω = _
  rw [informationOf_map,informationOf_map]
  rfl

omit [Countable α] [Countable β] in
lemma informationOf_same_fibers (μ : Measure Ω) (X : Ω → α) (Y : Ω → β)
    (h : ∀ ω ξ, X ω = X ξ ↔ Y ω = Y ξ) : informationOf μ X = informationOf μ Y := by
  funext ω
  rw [informationOf_fiber,informationOf_fiber]
  congr 3
  ext ξ
  exact h ξ ω

omit [Countable α] [Countable β] [Countable γ] in
lemma conditionedInformation_same_conditioner (μ : Measure Ω) (X : Ω → α) (Y : Ω → β)
    (Z : Ω → γ) (h : ∀ ω ξ, Y ω = Y ξ ↔ Z ω = Z ξ) :
    conditionedInformation μ X Y = conditionedInformation μ X Z := by
  have hp := informationOf_same_fibers μ (fun ω => (Y ω,X ω)) (fun ω => (Z ω,X ω))
    (fun ω ξ => by simp only [Prod.mk.injEq,h ω ξ])
  funext ω
  simp only [conditionedInformation,hp,informationOf_same_fibers μ Y Z h]

lemma conditionedEntropy_monotone_function (μ : Measure Ω) [IsProbabilityMeasure μ]
    [Nonempty α] (X : Ω → α) (Y : Ω → β) (f : β → γ)
    (hi : Integrable (informationOf μ X) μ) :
    conditionedEntropy μ X Y ≤ conditionedEntropy μ X (f ∘ Y) := by
  have hh := conditionedEntropy_le_conditionedEntropy μ X (f ∘ Y) Y hi
  have he : conditionedInformation μ X (fun ω => ((f ∘ Y) ω,Y ω)) =
      conditionedInformation μ X Y := by
    apply conditionedInformation_same_conditioner
    intro ω ξ
    simp only [Function.comp_apply,Prod.mk.injEq]
    exact ⟨And.right,fun h => ⟨congrArg f h,h⟩⟩
  simpa only [conditionedEntropy,he] using hh

omit [Countable α] [MeasurableSingletonClass α] in
lemma entropyOf_prod_fst (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (X : Ω → α) : entropyOf (μ.prod ν) (X ∘ Prod.fst) = entropyOf μ X := by
  rw [← entropyOf_map,Measure.map_fst_prod,measure_univ,one_smul]

omit [Countable α] [Countable β] [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
lemma conditionedEntropy_prod_fst (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (X : Ω → α) (Y : Ω → β) :
    conditionedEntropy (μ.prod ν) (X ∘ Prod.fst) (Y ∘ Prod.fst) = conditionedEntropy μ X Y := by
  rw [← conditionedEntropy_map,Measure.map_fst_prod,measure_univ,one_smul]
end EntropyLawTransforms

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

section BufferEntropy
variable {Λ Θ B G : Type*} [Countable Λ] [Countable Θ] [Countable B] [Countable G]
  [MeasurableSpace Λ] [MeasurableSpace Θ] [MeasurableSpace B] [MeasurableSpace G]
  [MeasurableSingletonClass Λ] [MeasurableSingletonClass Θ] [MeasurableSingletonClass B]
  [MeasurableSingletonClass G] [AddCommGroup G]

omit [Countable Θ] in

lemma buffer_remaining_count_entropy (π : Measure (ℕ × G)) (ρ : Measure Λ)
    [IsProbabilityMeasure π] [IsProbabilityMeasure ρ]
    (H : Λ → Θ) (D : Λ → G) (C : Λ → ℕ) :
    conditionedEntropy (π.prod ρ) (fun ω => ω.1.1+C ω.2)
      (fun ω => ((H ω.2,ω.2),ω.1.2+D ω.2)) =
      conditionedEntropy π Prod.fst Prod.snd := by
  let μ := π.prod ρ
  have he : conditionedInformation μ (fun ω => ω.1.1+C ω.2)
      (fun ω => ((H ω.2,ω.2),ω.1.2+D ω.2)) =
      conditionedInformation μ (fun ω => ω.1.1) (fun ω => (ω.1.2,ω.2)) := by
    rw [conditionedInformation_same_conditioner μ (fun ω => ω.1.1+C ω.2)
      (fun ω => ((H ω.2,ω.2),ω.1.2+D ω.2)) (fun ω => (ω.1.2,ω.2)) (by
        intro ω ξ
        simp only [Prod.mk.injEq]
        constructor
        · rintro ⟨⟨_,h⟩,hd⟩
          exact ⟨add_right_cancel (by simpa only [h] using hd),h⟩
        · rintro ⟨hd,h⟩
          simp only [hd,h,and_self])]
    exact conditionedInformation_fiberwise_injective μ (fun ω => ω.1.1)
      (fun ω => (ω.1.2,ω.2)) (fun y x => x+C y.2) (fun _ _ _ h => Nat.add_right_cancel h)
  change (∫ ω, _ ∂μ) = _
  rw [he]
  change conditionedEntropy μ (fun ω => ω.1.1) (fun ω => (ω.1.2,ω.2)) = _
  rw [conditionedEntropy_indep_pair μ (fun ω => ω.1.1) (fun ω => ω.1.2) Prod.snd
    (indepFun_prod (measurable_of_countable (fun p : ℕ × G => (p.2,p.1))) measurable_id)]
  exact conditionedEntropy_prod_fst π ρ Prod.fst Prod.snd

lemma buffer_displacement_entropy (π : Measure (ℕ × G)) (ρ : Measure Λ)
    [IsProbabilityMeasure π] [IsProbabilityMeasure ρ] (H : Λ → Θ) (D : Λ → G) :
    conditionedEntropy (π.prod ρ) (fun ω => ω.1.2+D ω.2) (fun ω => (H ω.2,ω.2)) =
      entropyOf π Prod.snd := by
  have he := conditionedInformation_fiberwise_injective (π.prod ρ) (fun ω => ω.1.2)
    (fun ω => (H ω.2,ω.2)) (fun y x => x+D y.2) (fun _ _ _ h => add_right_cancel h)
  change (∫ ω, _ ∂π.prod ρ) = _
  rw [he]
  change conditionedEntropy (π.prod ρ) (fun ω => ω.1.2) (fun ω => (H ω.2,ω.2)) = _
  rw [conditionedEntropy_indep _ _ _ (indepFun_prod measurable_snd
    (measurable_of_countable (fun x => (H x,x))))]
  exact entropyOf_prod_fst π ρ Prod.snd

lemma buffer_entropy_chain (π : Measure (ℕ × G)) (ρ : Measure Λ)
    [IsProbabilityMeasure π] [IsProbabilityMeasure ρ]
    (H : Λ → Θ) (Bfun : Λ → B) (DA : Λ → G) (DB : B → G) (C : Λ → ℕ)
    (hT : Integrable (informationOf (π.prod ρ) (fun ω => ω.1.1+C ω.2)) (π.prod ρ))
    (hS : Integrable (informationOf (π.prod ρ) (fun ω => ω.1.2+DA ω.2+DB (Bfun ω.2))) (π.prod ρ))
    (D₀ : ℝ)
    (hI : conditionedEntropy (π.prod ρ) (fun ω => ω.1.2+DA ω.2) (fun ω => H ω.2) -
      conditionedEntropy (π.prod ρ) (fun ω => ω.1.2+DA ω.2) (fun ω => (H ω.2,Bfun ω.2)) ≤ D₀) :
    conditionedEntropy (π.prod ρ) (fun ω => ω.1.2+DA ω.2) (fun ω => H ω.2) +
      conditionedEntropy π Prod.fst Prod.snd ≤ D₀ +
      entropyOf (π.prod ρ) (fun ω => (ω.1.2+DA ω.2+DB (Bfun ω.2),ω.1.1+C ω.2)) := by
  let μ := π.prod ρ
  let Z := fun ω : (ℕ × G) × Λ => ω.1.2+DA ω.2
  let T := fun ω : (ℕ × G) × Λ => ω.1.1+C ω.2
  let S := fun ω : (ℕ × G) × Λ => Z ω+DB (Bfun ω.2)
  let F := fun ω : (ℕ × G) × Λ => (H ω.2,Bfun ω.2)
  let K := fun ω : (ℕ × G) × Λ => ((H ω.2,ω.2),Z ω)
  have hpair := integrable_informationOf_pair μ S T hS hT
  have hup := conditionedEntropy_le_entropyOf μ (fun ω => (S ω,T ω)) F hpair
  rw [conditionedEntropy_chain μ S T F (integrable_conditionedInformation μ S F hS)
    (integrable_conditionedInformation μ T (fun ω => (F ω,S ω)) hT)] at hup
  have hs : conditionedEntropy μ S F = conditionedEntropy μ Z F := by
    apply congrArg (fun f => ∫ ω, f ω ∂μ)
      (conditionedInformation_fiberwise_injective μ Z F
        (fun y x => x+DB y.2) (fun _ _ _ h => add_right_cancel h))
  have ht : conditionedEntropy μ T K ≤ conditionedEntropy μ T (fun ω => (F ω,S ω)) := by
    exact conditionedEntropy_monotone_function μ T K
      (fun k => ((k.1.1,Bfun k.1.2),k.2+DB (Bfun k.1.2))) hT
  have hk : conditionedEntropy μ T K = conditionedEntropy π Prod.fst Prod.snd :=
    buffer_remaining_count_entropy π ρ H DA C
  rw [hs] at hup
  rw [hk] at ht
  change conditionedEntropy μ Z (fun ω => H ω.2) - conditionedEntropy μ Z F ≤ D₀ at hI
  change conditionedEntropy μ Z (fun ω => H ω.2) + _ ≤ D₀ + entropyOf μ (fun ω => (S ω,T ω))
  linarith
end BufferEntropy

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

section BufferKernelTransforms
variable {Θ A B Δ G : Type*} [Countable Θ] [Countable A] [Countable B] [Countable Δ] [Countable G]
  [MeasurableSpace Θ] [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace Δ] [MeasurableSpace G]
  [MeasurableSingletonClass Θ] [MeasurableSingletonClass A] [MeasurableSingletonClass B]
  [MeasurableSingletonClass Δ] [MeasurableSingletonClass G]

lemma compProd_swap_inner (η : Measure Θ) [IsProbabilityMeasure η]
    (κA : Kernel Θ A) (κB : Kernel Θ B) [IsMarkovKernel κA] [IsMarkovKernel κB] :
    (η ⊗ₘ (κA ×ₖ κB)).map (fun p => ((p.1,p.2.2),p.2.1)) =
      (η ⊗ₘ κB) ⊗ₘ κA.comap Prod.fst measurable_fst := by
  apply Measure.ext_of_singleton
  rintro ⟨⟨h,b⟩,a⟩
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have hs : (fun p : Θ × (A × B) => ((p.1,p.2.2),p.2.1)) ⁻¹' {((h,b),a)} = {(h,(a,b))} := by
    ext p
    simp only [Set.mem_preimage,Set.mem_singleton_iff,Prod.ext_iff]
    tauto
  rw [hs,compProd_atom,compProd_atom,compProd_atom,Kernel.comap_apply,Kernel.prod_apply,
    ← Set.singleton_prod_singleton,Measure.prod_prod]
  ring

lemma compProd_prod_buffer (η : Measure Θ) [IsProbabilityMeasure η]
    (κ : Kernel Θ A) [IsMarkovKernel κ] (π : Measure Δ) [IsProbabilityMeasure π] :
    ((η ⊗ₘ κ).prod π).map (fun p => (p.1.1,(p.2,p.1.2))) =
      η ⊗ₘ ((Kernel.const Θ π) ×ₖ κ) := by
  apply Measure.ext_of_singleton
  rintro ⟨h,d,a⟩
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have hs : (fun p : (Θ × A) × Δ => (p.1.1,(p.2,p.1.2))) ⁻¹' {(h,(d,a))} = {((h,a),d)} := by
    ext p
    simp only [Set.mem_preimage,Set.mem_singleton_iff,Prod.ext_iff]
    tauto
  rw [hs,← Set.singleton_prod_singleton,Measure.prod_prod,compProd_atom,compProd_atom,
    Kernel.prod_apply,Kernel.const_apply,← Set.singleton_prod_singleton,Measure.prod_prod]
  ring

omit [Countable G] [MeasurableSingletonClass G] in
lemma buffer_reference_map (η : Measure Θ) [IsProbabilityMeasure η]
    (κA : Kernel Θ A) (κB : Kernel Θ B) [IsMarkovKernel κA] [IsMarkovKernel κB]
    (π : Measure Δ) [IsProbabilityMeasure π] (F : Δ × A → G) :
    ((η ⊗ₘ (κA ×ₖ κB)).prod π).map (fun p => ((p.1.1,p.1.2.2),F (p.2,p.1.2.1))) =
      (η ⊗ₘ κB) ⊗ₘ (((Kernel.const Θ π ×ₖ κA).map F).comap Prod.fst measurable_fst) := by
  let f := fun p : Θ × (A × B) => ((p.1,p.2.2),p.2.1)
  let g := fun p : ((Θ × B) × A) × Δ => (p.1.1,(p.2,p.1.2))
  have h1 : ((η ⊗ₘ (κA ×ₖ κB)).prod π).map (Prod.map f id) =
      (((η ⊗ₘ κB) ⊗ₘ κA.comap Prod.fst measurable_fst).prod π) := by
    rw [← Measure.map_prod_map _ _ (measurable_of_countable _) measurable_id,Measure.map_id,
      compProd_swap_inner]
  have h2 := compProd_prod_buffer (η ⊗ₘ κB) (κA.comap Prod.fst measurable_fst) π
  have hk : ((Kernel.const (Θ × B) π) ×ₖ κA.comap Prod.fst measurable_fst).map F =
      ((Kernel.const Θ π ×ₖ κA).map F).comap Prod.fst measurable_fst := by
    ext p s hs
    simp only [Kernel.map_apply _ (measurable_of_countable F),Kernel.comap_apply,
      Kernel.prod_apply,Kernel.const_apply]
  rw [← hk,Measure.compProd_map (measurable_of_countable F),← h2,← h1,
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  rfl

omit [Countable G] [MeasurableSingletonClass G] in
lemma buffer_data_processing (ρ : Measure (Θ × (A × B))) [IsProbabilityMeasure ρ]
    (η : Measure Θ) [IsProbabilityMeasure η] (κA : Kernel Θ A) (κB : Kernel Θ B)
    [IsMarkovKernel κA] [IsMarkovKernel κB]
    (π : Measure Δ) [IsProbabilityMeasure π] (F : Δ × A → G) :
    InformationTheory.klDiv
      ((ρ.prod π).map (fun p => ((p.1.1,p.1.2.2),F (p.2,p.1.2.1))))
      ((η ⊗ₘ κB) ⊗ₘ (((Kernel.const Θ π ×ₖ κA).map F).comap Prod.fst measurable_fst)) ≤
      InformationTheory.klDiv ρ (η ⊗ₘ (κA ×ₖ κB)) := by
  rw [← buffer_reference_map]
  apply (InformationTheory.klDiv_map_le _ _ (measurable_of_countable _)).trans
  rw [klDiv_product,InformationTheory.klDiv_self,add_zero]

lemma conditional_buffer_information (ρ : Measure (Θ × (A × B))) [IsProbabilityMeasure ρ]
    (η : Measure Θ) [IsProbabilityMeasure η] (κA : Kernel Θ A) (κB : Kernel Θ B)
    [IsMarkovKernel κA] [IsMarkovKernel κB] [Nonempty G]
    (π : Measure Δ) [IsProbabilityMeasure π] (F : Δ × A → G)
    (hfin : InformationTheory.klDiv ρ (η ⊗ₘ (κA ×ₖ κB)) ≠ ∞)
    (hZ : Integrable (informationOf (ρ.prod π) (fun p => F (p.2,p.1.2.1))) (ρ.prod π)) :
    conditionedEntropy (ρ.prod π) (fun p => F (p.2,p.1.2.1)) (fun p => p.1.1) -
      conditionedEntropy (ρ.prod π) (fun p => F (p.2,p.1.2.1)) (fun p => (p.1.1,p.1.2.2)) ≤
      (InformationTheory.klDiv ρ (η ⊗ₘ (κA ×ₖ κB))).toReal := by
  let K := ((Kernel.const Θ π ×ₖ κA).map F)
  let : IsMarkovKernel K := Kernel.IsMarkovKernel.map _ (measurable_of_countable F)
  let f := fun p : (Θ × (A × B)) × Δ => ((p.1.1,p.1.2.2),F (p.2,p.1.2.1))
  let P := (ρ.prod π).map f
  have : IsProbabilityMeasure P := probabilityMeasure_map (measurable_of_countable _).aemeasurable
  have hle := buffer_data_processing ρ η κA κB π F
  have hn : InformationTheory.klDiv P ((η ⊗ₘ κB) ⊗ₘ K.comap Prod.fst measurable_fst) ≠ ∞ :=
    ne_top_of_le_ne_top hfin hle
  have hi : Integrable (informationOf P Prod.snd) P := by
    rw [integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
      (measurable_of_countable _).aemeasurable]
    change Integrable (informationOf ((ρ.prod π).map f) Prod.snd ∘ f) (ρ.prod π)
    rw [informationOf_map]
    exact hZ
  have hh := conditional_mutualInformation_le_reference P (η ⊗ₘ κB) Prod.fst K hn hi
  rw [conditionedEntropy_map,conditionedEntropy_map] at hh
  exact hh.trans (ENNReal.toReal_mono hfin hle)
end BufferKernelTransforms

section BufferedComparison
variable {Θ A B G : Type*} [Countable Θ] [Countable A] [Countable B] [Countable G]
  [MeasurableSpace Θ] [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace G]
  [MeasurableSingletonClass Θ] [MeasurableSingletonClass A] [MeasurableSingletonClass B]
  [MeasurableSingletonClass G] [AddCommGroup G]

omit [Countable A] [Countable G] [MeasurableSingletonClass A]
  [MeasurableSingletonClass G] [AddCommGroup G] in
lemma map_prod_snd_function (π : Measure A) (ρ : Measure B) [IsProbabilityMeasure π]
    [IsProbabilityMeasure ρ] (f : B → G) : (π.prod ρ).map (f ∘ Prod.snd) = ρ.map f := by
  rw [← Measure.map_map (measurable_of_countable _) measurable_snd,Measure.map_snd_prod,
    measure_univ,one_smul]

lemma buffered_reference_comparison (π : Measure (ℕ × G)) (ρ : Measure (A × B))
    [IsProbabilityMeasure π] [IsProbabilityMeasure ρ]
    (H : A × B → Θ) (DA : A → G) (DB : B → G) (C : A × B → ℕ)
    (κA : Kernel Θ A) (κB : Kernel Θ B) [IsMarkovKernel κA] [IsMarkovKernel κB]
    (hfin : InformationTheory.klDiv (ρ.map (fun a => (H a,a))) (ρ.map H ⊗ₘ (κA ×ₖ κB)) ≠ ∞)
    (hU : Integrable (informationOf π Prod.fst) π)
    (hd : Integrable (informationOf π Prod.snd) π)
    (hZ : Integrable (informationOf (π.prod ρ) (fun ω => ω.1.2+DA ω.2.1)) (π.prod ρ))
    (hT : Integrable (informationOf (π.prod ρ) (fun ω => ω.1.1+C ω.2)) (π.prod ρ))
    (hS : Integrable (informationOf (π.prod ρ) (fun ω => ω.1.2+DA ω.2.1+DB ω.2.2)) (π.prod ρ)) :
    let P := (π.prod ρ).map (fun ω => ((H ω.2,ω.1.2+DA ω.2.1),ω.2))
    let Q := P.fst ⊗ₘ (κA ×ₖ κB).comap Prod.fst measurable_fst
    InformationTheory.klDiv P Q ≠ ∞ ∧
      (InformationTheory.klDiv P Q).toReal ≤
        2*(InformationTheory.klDiv (ρ.map (fun a => (H a,a))) (ρ.map H ⊗ₘ (κA ×ₖ κB))).toReal +
        entropyOf (π.prod ρ) (fun ω => (ω.1.2+DA ω.2.1+DB ω.2.2,ω.1.1+C ω.2)) -
        entropyOf π (fun p => (p.2,p.1)) := by
  dsimp only
  let R := ρ.map (fun a => (H a,a))
  let η := ρ.map H
  have : IsProbabilityMeasure R := probabilityMeasure_map (measurable_of_countable _).aemeasurable
  have : IsProbabilityMeasure η := probabilityMeasure_map (measurable_of_countable _).aemeasurable
  have hb : (π.prod ρ).map (fun ω => (H ω.2,ω.2)) = R :=
    map_prod_snd_function π ρ (fun a => (H a,a))
  have hf : R.fst = η := map_graph_fst ρ H
  have he : R.prod π = (π.prod ρ).map (fun p => ((H p.2,p.2),p.1)) := by
    calc
      R.prod π = (ρ.map (fun a => (H a,a))).prod (π.map id) := by rw [Measure.map_id]
      _ = (ρ.prod π).map (Prod.map (fun a => (H a,a)) id) :=
        Measure.map_prod_map ρ π (measurable_of_countable _) measurable_id
      _ = _ := by
        rw [← Measure.prod_swap (μ := π) (ν := ρ),Measure.map_map (measurable_of_countable _) measurable_swap]
        rfl
  have hz' : Integrable (informationOf (R.prod π) (fun p => p.2.2+DA p.1.2.1)) (R.prod π) := by
    rw [he,integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
      (measurable_of_countable _).aemeasurable]
    rw [informationOf_map]
    exact hZ
  have hI := conditional_buffer_information R η κA κB π (fun p => p.1.2+DA p.2) hfin hz'
  rw [he,conditionedEntropy_map,conditionedEntropy_map] at hI
  have hc := buffer_entropy_chain π ρ H Prod.snd (fun a => DA a.1) DB C hT hS
    (InformationTheory.klDiv R (η ⊗ₘ (κA ×ₖ κB))).toReal hI
  have hbase : InformationTheory.klDiv ((π.prod ρ).map (fun ω => (H ω.2,ω.2)))
      (((π.prod ρ).map (fun ω => (H ω.2,ω.2))).fst ⊗ₘ (κA ×ₖ κB)) ≠ ∞ := by
    rwa [hb,hf]
  have haug := klDiv_reference_augment (π.prod ρ) Prod.snd (H ∘ Prod.snd)
    (fun ω => ω.1.2+DA ω.2.1) (κA ×ₖ κB)
    (InformationTheory.klDiv_ne_top_iff.mp hbase).1
    (InformationTheory.klDiv_ne_top_iff.mp hbase).2 hZ
  dsimp only [Function.comp_apply] at haug
  rw [hb,hf,buffer_displacement_entropy π ρ H (fun a => DA a.1)] at haug
  rw [entropyOf_pair_chain π Prod.snd Prod.fst hd
    (integrable_conditionedInformation π Prod.fst Prod.snd hU)]
  refine ⟨haug.1,?_⟩
  rw [haug.2]
  dsimp only [R,η,Function.comp_def] at hc ⊢
  linarith
end BufferedComparison

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

abbrev ThreeLists (α : Type*) := TapeList α × (TapeList α × TapeList α)

def splitThree {α : Type*} (a : ThreeChunk α) : ThreeLists α × ThreeLists α :=
  ((a.1 false,a.2.1 false,a.2.2 false),(a.1 true,a.2.1 true,a.2.2 true))

def joinThree {α : Type*} (p : ThreeLists α × ThreeLists α) : ThreeChunk α :=
  ((fun b => if b then p.2.1 else p.1.1),
    (fun b => if b then p.2.2.1 else p.1.2.1),
    (fun b => if b then p.2.2.2 else p.1.2.2))

lemma split_joinThree {α : Type*} (p : ThreeLists α × ThreeLists α) :
    splitThree (joinThree p) = p := by
  rcases p with ⟨⟨a,b,c⟩,⟨d,e,f⟩⟩
  rfl

lemma join_splitThree {α : Type*} (a : ThreeChunk α) : joinThree (splitThree a) = a := by
  apply Prod.ext
  · funext b;cases b <;> rfl
  · apply Prod.ext <;> (funext b;cases b <;> rfl)

def splitThreeEquiv {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] : ThreeChunk α ≃ᵐ ThreeLists α × ThreeLists α where
  toFun := splitThree
  invFun := joinThree
  left_inv := join_splitThree
  right_inv := split_joinThree
  measurable_toFun := measurable_of_countable _
  measurable_invFun := measurable_of_countable _

noncomputable def oneBridgeKernel {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Measure α) [IsProbabilityMeasure ν] (L : α → ℕ) :
    Kernel ℕ (TapeList α) where
  toFun := bridgeListLaw ν L
  measurable' := measurable_of_countable _

noncomputable def signedThreeKernel {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Measure α) [IsProbabilityMeasure ν] (L : α → ℕ) :
    Kernel (ℕ × (ℕ × ℕ)) (ThreeLists α) :=
  oneBridgeKernel ν L ∥ₖ (oneBridgeKernel ν L ∥ₖ oneBridgeKernel ν L)

lemma signedThreeKernel_markov {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Measure α) [IsProbabilityMeasure ν] (L : α → ℕ)
    (hu : ∀ H, Measure.infinitePi (fun _ : ℕ => ν) (renewalCut L H) ≠ 0) :
    IsMarkovKernel (signedThreeKernel ν L) := by
  let : IsMarkovKernel (oneBridgeKernel ν L) := ⟨fun H => bridgeListLaw_probability ν L H (hu H)⟩
  unfold signedThreeKernel
  infer_instance

lemma pairBridgeLaw_atom_general {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (H : ℕ) (a : TwoTapeList α) :
    pairBridgeLaw ν L H {a} =
      bridgeListLaw (ν false) (L false) H {a false} * bridgeListLaw (ν true) (L true) H {a true} := by
  have hs : ({a} : Set (TwoTapeList α)) = Set.univ.pi (fun b => {a b}) := by
    ext x
    simp only [Set.mem_singleton_iff,Set.mem_pi,Set.mem_univ,true_implies]
    exact funext_iff
  rw [pairBridgeLaw,hs,Measure.pi_pi,Fintype.prod_bool]
  exact mul_comm _ _

lemma threeBridgeKernel_split {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ)
    (hu : ∀ H b, Measure.infinitePi (fun _ : ℕ => ν b) (renewalCut (L b) H) ≠ 0) :
    (threeBridgeKernel ν L).map splitThree =
      signedThreeKernel (ν false) (L false) ×ₖ signedThreeKernel (ν true) (L true) := by
  let : IsMarkovKernel (pairBridgeKernel ν L) := pairBridgeKernel_markov ν L hu
  let : ∀ b, IsMarkovKernel (oneBridgeKernel (ν b) (L b)) :=
    fun b => ⟨fun H => bridgeListLaw_probability (ν b) (L b) H (hu H b)⟩
  apply Kernel.ext
  intro h
  apply Measure.ext_of_singleton
  intro p
  rw [Kernel.map_apply _ (measurable_of_countable _),Measure.map_apply
    (measurable_of_countable _) (measurableSet_singleton _)]
  have hs : splitThree ⁻¹' {p} = {joinThree p} := by
    ext a
    change splitThree a = p ↔ a = joinThree p
    exact ⟨fun h => by rw [← h,join_splitThree],fun h => by rw [h,split_joinThree]⟩
  rw [hs]
  rcases p with ⟨⟨a,b,c⟩,⟨d,e,f⟩⟩
  simp only [joinThree]
  simp only [threeBridgeKernel,signedThreeKernel,Kernel.parallelComp_apply,Kernel.prod_apply,
    ← Set.singleton_prod_singleton,Measure.prod_prod]
  change (pairBridgeLaw ν L h.1 {fun b => if b then d else a}) *
    ((pairBridgeLaw ν L h.2.1 {fun u => if u then e else b}) *
    (pairBridgeLaw ν L h.2.2 {fun b => if b then f else c})) = _
  simp only [pairBridgeLaw_atom_general,Bool.false_eq_true,↓reduceIte]
  simp only [oneBridgeKernel,Kernel.coe_mk]
  ring

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

section SumLaws
variable {G : Type*} [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [AddCommGroup G]

noncomputable def sumLaw (ν : Measure G) : ℕ → Measure G
  | 0 => Measure.dirac 0
  | n+1 => ν.conv (sumLaw ν n)

instance conv_probability (μ ν : Measure G) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (μ.conv ν) :=
  probabilityMeasure_map (measurable_of_countable _).aemeasurable

instance sumLaw_probability (ν : Measure G) [IsProbabilityMeasure ν] (n : ℕ) :
    IsProbabilityMeasure (sumLaw ν n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac (0 : G)))
  | succ n ih =>
    let := ih
    exact inferInstanceAs (IsProbabilityMeasure (ν.conv (sumLaw ν n)))

lemma sumLaw_add (ν : Measure G) [IsProbabilityMeasure ν] (m n : ℕ) :
    sumLaw ν (m+n) = (sumLaw ν m).conv (sumLaw ν n) := by
  induction m with
  | zero => simp only [Nat.zero_add,sumLaw,Measure.dirac_zero_conv]
  | succ m ih =>
    rw [Nat.succ_add,sumLaw,ih,sumLaw,Measure.conv_assoc]

lemma entropy_conv_ge_left (μ ν : Measure G) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hi : Integrable (informationOf (μ.conv ν) id) (μ.conv ν)) :
    entropyOf μ id ≤ entropyOf (μ.conv ν) id := by
  have hs : Integrable (informationOf (μ.prod ν) (fun p => p.1+p.2)) (μ.prod ν) := by
    rw [Measure.conv,integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
      (measurable_of_countable _).aemeasurable] at hi
    rw [informationOf_map] at hi
    exact hi
  have hh := conditionedEntropy_le_entropyOf (μ.prod ν) (fun p => p.1+p.2) Prod.snd hs
  have he := conditionedInformation_fiberwise_injective (μ.prod ν) Prod.fst Prod.snd
    (fun y x => x+y) (fun _ _ _ h => add_right_cancel h)
  have hce : conditionedEntropy (μ.prod ν) (fun p => p.1+p.2) Prod.snd = entropyOf μ id := by
    change (∫ p, conditionedInformation (μ.prod ν) (fun p => p.1+p.2) Prod.snd p ∂μ.prod ν) = _
    rw [he]
    change conditionedEntropy (μ.prod ν) Prod.fst Prod.snd = _
    have hind : IndepFun (Prod.fst : G × G → G) Prod.snd (μ.prod ν) :=
      indepFun_prod measurable_id measurable_id
    rw [conditionedEntropy_indep _ _ _ hind]
    exact entropyOf_prod_fst μ ν id
  rw [hce] at hh
  simpa only [Measure.conv,entropyOf_map,Function.id_comp] using hh

lemma sumLaw_entropy_monotone (ν : Measure G) [IsProbabilityMeasure ν]
    (hi : ∀ n, Integrable (informationOf (sumLaw ν n) id) (sumLaw ν n)) :
    Monotone (fun n => entropyOf (sumLaw ν n) id) := by
  intro m n hmn
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hmn
  dsimp only
  rw [sumLaw_add]
  apply entropy_conv_ge_left
  rw [← sumLaw_add]
  exact hi _
end SumLaws

lemma sumLaw_lattice_moment {q : ℕ} (ν : Measure (Fin q → ℤ)) [IsProbabilityMeasure ν]
    (hi : ∀ i, Integrable (fun x => |(x i : ℝ)|) ν) (a : ℝ)
    (hm : ∀ i, (∫ x, |(x i : ℝ)| ∂ν) ≤ a) (n : ℕ) :
    ∀ i, Integrable (fun x => |(x i : ℝ)|) (sumLaw ν n) ∧
      (∫ x, |(x i : ℝ)| ∂sumLaw ν n) ≤ n*a := by
  induction n with
  | zero =>
    intro i
    refine ⟨integrable_dirac (by simp),?_⟩
    simp only [sumLaw,integral_dirac,Pi.zero_apply,Int.cast_zero,abs_zero,Nat.cast_zero,zero_mul,le_refl]
  | succ n ih =>
    intro i
    have ha : Integrable (fun p : (Fin q → ℤ) × (Fin q → ℤ) => |(p.1 i : ℝ)|+|(p.2 i : ℝ)|)
        (ν.prod (sumLaw ν n)) := (hi i).comp_fst _ |>.add ((ih i).1.comp_snd _)
    have hb : Integrable (fun p : (Fin q → ℤ) × (Fin q → ℤ) => |((p.1 i+p.2 i : ℤ) : ℝ)|)
        (ν.prod (sumLaw ν n)) := by
      apply ha.mono' (measurable_of_countable _).aestronglyMeasurable
      filter_upwards [] with p
      simpa only [Real.norm_eq_abs,abs_abs,Int.cast_add] using abs_add_le (p.1 i : ℝ) (p.2 i : ℝ)
    constructor
    · rw [sumLaw,Measure.conv,integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
        (measurable_of_countable _).aemeasurable]
      exact hb
    · rw [sumLaw,Measure.conv,integral_map_of_stronglyMeasurable (measurable_of_countable _)
        (measurable_of_countable _).stronglyMeasurable]
      calc
        _ ≤ ∫ p : (Fin q → ℤ) × (Fin q → ℤ), |(p.1 i : ℝ)|+|(p.2 i : ℝ)| ∂ν.prod (sumLaw ν n) :=
          integral_mono hb ha (fun p => by simpa only [Pi.add_apply,Int.cast_add] using abs_add_le (p.1 i : ℝ) (p.2 i : ℝ))
        _ = (∫ x, |(x i : ℝ)| ∂ν) + ∫ x, |(x i : ℝ)| ∂sumLaw ν n := by
          rw [integral_add ((hi i).comp_fst _) ((ih i).1.comp_snd _),integral_fun_fst (fun x : Fin q → ℤ => |(x i : ℝ)|),
            integral_fun_snd (fun x : Fin q → ℤ => |(x i : ℝ)|)]
          simp only [measureReal_def,measure_univ,ENNReal.toReal_one,one_smul]
        _ ≤ _ := by have := hm i;have := (ih i).2;push_cast; nlinarith

lemma sumLaw_lattice_entropy {q : ℕ} (ν : Measure (Fin q → ℤ)) [IsProbabilityMeasure ν]
    (hi : ∀ i, Integrable (fun x => |(x i : ℝ)|) ν) (a : ℝ) (ha : 0 < a)
    (hm : ∀ i, (∫ x, |(x i : ℝ)| ∂ν) ≤ a) (n : ℕ) :
    Integrable (informationOf (sumLaw ν n) id) (sumLaw ν n) ∧
      entropyOf (sumLaw ν n) id ≤ q*(1+Real.log 2+Real.log (a+1)+Real.log (n+1)) := by
  have h := sumLaw_lattice_moment ν hi a hm n
  have hb := entropyOf_lattice_moment (sumLaw ν n) q id (fun i => (h i).1)
    ((n+1)*a) (mul_pos (by positivity) ha) (fun i => (h i).2.trans (by nlinarith))
  refine ⟨hb.1,hb.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg q)
  have hl : Real.log ((n+1)*a+1) ≤ Real.log ((a+1)*(n+1)) := by
    apply Real.log_le_log (by positivity)
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  rw [Real.log_mul (by positivity) (by positivity)] at hl
  linarith
section ListTotals
variable {α G : Type*} [AddCommMonoid G]

noncomputable def listTotal (D : α → G) (a : TapeList α) : G := ∑ i, D (a.2 i)
noncomputable def pairTotal (D : Bool → α → G) (a : TwoTapeList α) : G :=
  listTotal (D false) (a false) + listTotal (D true) (a true)

lemma listTotal_prefix (D : α → G) (Z : ℕ → α) (n : ℕ) :
    listTotal D (tapePrefix n Z) = ∑ i ∈ Finset.range n, D (Z i) := by
  exact Fin.sum_univ_eq_sum_range (fun i => D (Z i)) n

lemma commonCutIndices_add (L : Bool → α → ℕ) (H J : ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i))) (hH : Z ∈ commonCut L H)
    (hJ : afterCommonCut L H Z ∈ commonCut L J) (b : Bool) :
    commonCutIndices L (H+J) Z b =
      commonCutIndices L H Z b + commonCutIndices L J (afterCommonCut L H Z) b := by
  apply cutListIndex_eq (L b) (H+J) _ (hZ b)
  rw [tapeHeight_add]
  have h1 : tapeHeight (L b) (fun i => Z (b,i)) (commonCutIndices L H Z b) = H :=
    cutListIndex_spec (L b) H _ (hZ b) (hH b)
  have h2 : tapeHeight (L b) (fun i => Z (b,commonCutIndices L H Z b+i))
      (commonCutIndices L J (afterCommonCut L H Z) b) = J :=
    cutListIndex_spec (L b) J _ (fun i => hZ b _) (hJ b)
  rw [h1,h2]

lemma listTotal_commonCut_add (L : Bool → α → ℕ) (D : α → G) (H J : ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i))) (hH : Z ∈ commonCut L H)
    (hJ : afterCommonCut L H Z ∈ commonCut L J) (b : Bool) :
    listTotal D (commonCutList L (H+J) Z b) = listTotal D (commonCutList L H Z b) +
      listTotal D (commonCutList L J (afterCommonCut L H Z) b) := by
  change listTotal D (tapePrefix (commonCutIndices L (H+J) Z b) (fun i => Z (b,i))) =
    listTotal D (tapePrefix (commonCutIndices L H Z b) (fun i => Z (b,i))) +
    listTotal D (tapePrefix (commonCutIndices L J (afterCommonCut L H Z) b) (fun i => afterCommonCut L H Z (b,i)))
  simp only [listTotal_prefix]
  rw [commonCutIndices_add L H J Z hZ hH hJ b,Finset.sum_range_add]
  rfl

lemma nthCommonList_total (L : Bool → α → ℕ) (D : α → G) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i)))
    (he : ∀ r, ∃ H, 0 < H ∧ ((commonRestart L)^[r] Z) ∈ commonCut L H) (r : ℕ) (b : Bool) :
    listTotal D (nthCommonList L r Z b) =
      ∑ i ∈ Finset.range r, listTotal D (commonBlocks L Z i b) := by
  induction r with
  | zero =>
    have hi : commonCutIndices L 0 Z b = 0 := cutListIndex_eq (L b) 0 _ (hZ b) rfl
    change listTotal D (tapePrefix (commonCutIndices L (commonDepth L Z 0) Z b) (fun i => Z (b,i))) = _
    simp only [commonDepth_zero,hi,listTotal_prefix,Finset.range_zero,Finset.sum_empty]
  | succ r ih =>
    obtain ⟨_,hc,_⟩ := firstCommonWidth_spec L ((commonRestart L)^[r] Z) (he r)
    have hspec := commonDepth_spec L Z hZ he r
    have hc' : afterCommonCut L (commonDepth L Z r) Z ∈
        commonCut L (firstCommonWidth L ((commonRestart L)^[r] Z)) := by rw [hspec.2.1];exact hc
    rw [Finset.sum_range_succ,← ih]
    unfold nthCommonList
    rw [commonDepth_succ,listTotal_commonCut_add L D _ _ Z hZ hspec.1 hc' b,hspec.2.1]
    rfl

lemma nthCommonList_pairTotal (L : Bool → α → ℕ) (D : Bool → α → G) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i)))
    (he : ∀ r, ∃ H, 0 < H ∧ ((commonRestart L)^[r] Z) ∈ commonCut L H) (r : ℕ) :
    pairTotal D (nthCommonList L r Z) = ∑ i ∈ Finset.range r, pairTotal D (commonBlocks L Z i) := by
  simp only [pairTotal,nthCommonList_total L _ Z hZ he,Finset.sum_add_distrib]
end ListTotals
section SumCommon
variable {G : Type*} [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [AddCommGroup G]

lemma iid_sum_law (ν : Measure G) [IsProbabilityMeasure ν] (n : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => ν)).map (fun Z => ∑ i ∈ Finset.range n, Z i) = sumLaw ν n := by
  induction n with
  | zero => simp only [Finset.range_zero,Finset.sum_empty,sumLaw,Measure.map_const,measure_univ,one_smul]
  | succ n ih =>
    have hind := (iid_prefix_suffix_independent ν n).comp
      (measurable_of_countable (fun Z : Fin n → G => ∑ i, Z i)) (measurable_pi_apply 0)
    have heq : (fun Z : ℕ → G => ∑ i : Fin n, Z i) = (fun Z => ∑ i ∈ Finset.range n, Z i) := by
      funext Z
      exact Fin.sum_univ_eq_sum_range Z n
    simp only [Function.comp_def,Nat.add_zero] at hind
    rw [heq] at hind
    have hm := hind.map_add_eq_map_conv_map (by fun_prop) (by fun_prop)
    change (Measure.infinitePi (fun _ : ℕ => ν)).map
      (fun Z => (∑ i ∈ Finset.range n, Z i)+Z n) = _ at hm
    simp only [Finset.sum_range_succ]
    rw [hm,ih,Measure.infinitePi_map_eval,Measure.conv_comm]
    rfl

variable {α : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]

noncomputable def commonGapLaw (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (D : Bool → α → G) : Measure G :=
  (commonBlockLaw ν L).map (pairTotal D)

instance commonBlockLaw_probability (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) : IsProbabilityMeasure (commonBlockLaw ν L) :=
  probabilityMeasure_map (μ := twoTapeLaw ν) (measurable_firstCommonBlock L).aemeasurable

instance commonGapLaw_probability (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (D : Bool → α → G) : IsProbabilityMeasure (commonGapLaw ν L D) :=
  probabilityMeasure_map (measurable_of_countable _).aemeasurable

lemma nthCommonLaw_pairTotal (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (D : Bool → α → G) (r : ℕ) :
    (nthCommonLaw ν L r).map (pairTotal D) = sumLaw (commonGapLaw ν L D) r := by
  rw [nthCommonLaw,Measure.map_map (measurable_of_countable _) (measurable_nthCommonList L r)]
  have hae : (fun Z => pairTotal D (nthCommonList L r Z)) =ᵐ[twoTapeLaw ν]
      (fun Z => ∑ i ∈ Finset.range r, pairTotal D (commonBlocks L Z i)) := by
    filter_upwards [ae_twoTape_prop ν (fun b a => 0 < L b a)
      (fun b => measurableSet_lt measurable_const (measurable_of_countable (L b))) hL,
      ae_common_iterates ν L hL he] with Z hZ hiter
    exact nthCommonList_pairTotal L D Z hZ hiter r
  change (twoTapeLaw ν).map (fun Z => pairTotal D (nthCommonList L r Z)) = _
  rw [Measure.map_congr hae]
  have hm := Measure.infinitePi_map_pi (μ := fun _ : ℕ => commonBlockLaw ν L)
    (f := fun _ => pairTotal D) (fun _ => measurable_of_countable _)
  have hb := commonBlocks_map ν L hL he
  have hmb : Measurable (commonBlocks L) := measurable_regenerativeSequence _ _
    (measurable_firstCommonBlock L) (measurable_commonRestart L)
  let : IsProbabilityMeasure ((commonBlockLaw ν L).map (pairTotal D)) :=
    probabilityMeasure_map (measurable_of_countable _).aemeasurable
  calc
    _ = ((twoTapeLaw ν).map (commonBlocks L)).map
        (fun Z => ∑ i ∈ Finset.range r, pairTotal D (Z i)) := by
      rw [Measure.map_map (by fun_prop) hmb]
      rfl
    _ = _ := by
      rw [hb]
      have hh := congrArg (fun μ : Measure (ℕ → G) => μ.map (fun Z => ∑ i ∈ Finset.range r, Z i)) hm
      rw [Measure.map_map (by fun_prop) (by fun_prop),iid_sum_law] at hh
      exact hh
end SumCommon

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

section MarkedSums
variable {G : Type*} [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [AddCommGroup G]

noncomputable def sumKernel (ν : Measure G) : Kernel ℕ G where
  toFun := sumLaw ν
  measurable' := measurable_of_countable _

instance sumKernel_markov (ν : Measure G) [IsProbabilityMeasure ν] : IsMarkovKernel (sumKernel ν) :=
  ⟨fun n => sumLaw_probability ν n⟩

noncomputable def markedSumLaw (ν : Measure G) (θ : Measure ℕ) : Measure (ℕ × G) :=
  θ ⊗ₘ sumKernel ν

instance markedSumLaw_probability (ν : Measure G) [IsProbabilityMeasure ν]
    (θ : Measure ℕ) [IsProbabilityMeasure θ] : IsProbabilityMeasure (markedSumLaw ν θ) :=
  inferInstanceAs (IsProbabilityMeasure (θ ⊗ₘ sumKernel ν))

lemma markedSumLaw_atom (ν : Measure G) [IsProbabilityMeasure ν]
    (θ : Measure ℕ) [IsProbabilityMeasure θ] (n : ℕ) (x : G) :
    markedSumLaw ν θ {(n,x)} = θ {n} * sumLaw ν n {x} := compProd_atom θ (sumKernel ν) (n,x)

lemma markedSumLaw_fst (ν : Measure G) [IsProbabilityMeasure ν]
    (θ : Measure ℕ) [IsProbabilityMeasure θ] : (markedSumLaw ν θ).fst = θ :=
  Measure.fst_compProd θ (sumKernel ν)

lemma markedSumLaw_conv (ν : Measure G) [IsProbabilityMeasure ν]
    (θ η : Measure ℕ) [IsProbabilityMeasure θ] [IsProbabilityMeasure η] :
    (markedSumLaw ν θ).conv (markedSumLaw ν η) = markedSumLaw ν (θ.conv η) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Measure.lintegral_conv hf]
  change (∫⁻ x, ∫⁻ y, f (x+y) ∂η ⊗ₘ sumKernel ν ∂θ ⊗ₘ sumKernel ν) =
    ∫⁻ x, f x ∂(θ.conv η) ⊗ₘ sumKernel ν
  rw [Measure.lintegral_compProd (measurable_of_countable _),
    Measure.lintegral_compProd hf]
  change (∫⁻ n, ∫⁻ x, ∫⁻ y, f ((n,x)+y) ∂η ⊗ₘ sumKernel ν ∂sumLaw ν n ∂θ) =
    ∫⁻ n, ∫⁻ x, f (n,x) ∂sumLaw ν n ∂θ.conv η
  rw [Measure.lintegral_conv (measurable_of_countable _)]
  apply lintegral_congr
  intro n
  simp_rw [Measure.lintegral_compProd (measurable_of_countable _)]
  rw [lintegral_lintegral_swap (measurable_of_countable _).aemeasurable]
  apply lintegral_congr
  intro m
  change (∫⁻ x, ∫⁻ y, f (n+m,x+y) ∂sumLaw ν m ∂sumLaw ν n) =
    ∫⁻ x, f (n+m,x) ∂sumLaw ν (n+m)
  rw [sumLaw_add,Measure.lintegral_conv (measurable_of_countable _)]

lemma conditionalInfo_markedSum (ν : Measure G) [IsProbabilityMeasure ν]
    (θ : Measure ℕ) [IsProbabilityMeasure θ] :
    conditionalInfo (markedSumLaw ν θ) =ᵐ[markedSumLaw ν θ]
      fun p => atomInfo (sumLaw ν p.1) p.2 := by
  filter_upwards [ae_atom_real_pos (markedSumLaw ν θ)] with p hp
  have hf : 0 < θ.real {p.1} := by
    have hh := atom_le_fst (markedSumLaw ν θ) p
    rw [markedSumLaw_fst] at hh
    exact hp.trans_le (ENNReal.toReal_mono (by finiteness) hh)
  dsimp [conditionalInfo]
  rw [markedSumLaw_fst]
  have hx : (markedSumLaw ν θ).real {p} = θ.real {p.1} * (sumLaw ν p.1).real {p.2} := by
    rw [measureReal_def,show p = (p.1,p.2) from rfl,markedSumLaw_atom,ENNReal.toReal_mul]
    rfl
  rw [hx,mul_div_cancel_left₀ _ hf.ne']
  rfl

lemma markedSumLaw_conditional_entropy (ν : Measure G) [IsProbabilityMeasure ν]
    (θ : Measure ℕ) [IsProbabilityMeasure θ]
    (hi : ∀ n, Integrable (informationOf (sumLaw ν n) id) (sumLaw ν n))
    (hh : Integrable (fun n => entropyOf (sumLaw ν n) id) θ) :
    Integrable (conditionalInfo (markedSumLaw ν θ)) (markedSumLaw ν θ) ∧
      conditionalEntropy (markedSumLaw ν θ) = ∫ n, entropyOf (sumLaw ν n) id ∂θ := by
  have hin (n : ℕ) : Integrable (atomInfo (sumLaw ν n)) (sumLaw ν n) := by
    simpa only [Measure.map_id] using (integrable_informationOf_iff _ id).mp (hi n)
  have ha : Integrable (fun p : ℕ × G => atomInfo (sumLaw ν p.1) p.2) (markedSumLaw ν θ) := by
    apply (Measure.integrable_compProd_iff (measurable_of_countable _).aestronglyMeasurable).mpr
    constructor
    · exact Eventually.of_forall hin
    · change Integrable (fun n => ∫ y, ‖atomInfo (sumLaw ν n) y‖ ∂sumLaw ν n) θ
      simpa only [Real.norm_eq_abs,abs_of_nonneg (atomInfo_nonneg _ _),
        entropyOf_eq_discreteEntropy,Measure.map_id,discreteEntropy] using hh
  refine ⟨ha.congr (conditionalInfo_markedSum ν θ).symm,?_⟩
  change (∫ p, conditionalInfo (markedSumLaw ν θ) p ∂markedSumLaw ν θ) = _
  rw [integral_congr_ae (conditionalInfo_markedSum ν θ)]
  change (∫ p, atomInfo (sumLaw ν p.1) p.2 ∂θ ⊗ₘ sumKernel ν) = _
  rw [Measure.integral_compProd ha]
  change (∫ n, discreteEntropy (sumLaw ν n) ∂θ) = _
  simp only [entropyOf_eq_discreteEntropy,Measure.map_id]
end MarkedSums
section CommonMoments
variable {α : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]

lemma commonBlock_integrable_total (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (hW : Integrable (fun Z => (firstCommonWidth L Z : ℝ)) (twoTapeLaw ν))
    (b : Bool) (D : α → ℝ) (hi : Integrable D (ν b)) :
    Integrable (fun a => listTotal D (a b)) (commonBlockLaw ν L) := by
  rw [commonBlockLaw,integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
    (measurable_firstCommonBlock L).aemeasurable]
  refine ⟨((measurable_of_countable _).comp (measurable_firstCommonBlock L)).aestronglyMeasurable,?_⟩
  apply lt_of_le_of_lt _ ((commonBlock_cost_bound ν L hL he b (fun a => ‖D a‖ₑ)).trans_lt ?_)
  · apply lintegral_mono
    intro Z
    exact enorm_sum_le Finset.univ (fun i => D ((firstCommonBlock L Z b).2 i))
  · apply ENNReal.mul_lt_top
    · have hw := (hasFiniteIntegral_iff_ofReal (Eventually.of_forall
        (fun Z => Nat.cast_nonneg (α := ℝ) (firstCommonWidth L Z)))).mp hW.hasFiniteIntegral
      simpa only [ENNReal.ofReal_natCast] using hw
    · exact hi.hasFiniteIntegral

lemma commonGapLaw_lattice_integrable {q : ℕ}
    (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (hW : Integrable (fun Z => (firstCommonWidth L Z : ℝ)) (twoTapeLaw ν))
    (D : Bool → α → (Fin q → ℤ))
    (hi : ∀ b i, Integrable (fun a => (D b a i : ℝ)) (ν b)) (i : Fin q) :
    Integrable (fun x => |(x i : ℝ)|) (commonGapLaw ν L D) := by
  rw [commonGapLaw,integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
    (measurable_of_countable _).aemeasurable]
  have h0 := commonBlock_integrable_total ν L hL he hW false (fun a => (D false a i : ℝ)) (hi false i)
  have h1 := commonBlock_integrable_total ν L hL he hW true (fun a => (D true a i : ℝ)) (hi true i)
  simpa only [Function.comp_def,pairTotal,listTotal,Pi.add_apply,Finset.sum_apply,Int.cast_add,Int.cast_sum] using (h0.add h1).abs
end CommonMoments

section MarkedEntropy
variable {G : Type*} [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [AddCommGroup G]

lemma markedSumLaw_entropy (ν : Measure G) [IsProbabilityMeasure ν]
    (θ : Measure ℕ) [IsProbabilityMeasure θ]
    (hi : ∀ n, Integrable (informationOf (sumLaw ν n) id) (sumLaw ν n))
    (hθ : Integrable (atomInfo θ) θ)
    (hh : Integrable (fun n => entropyOf (sumLaw ν n) id) θ) :
    Integrable (informationOf (markedSumLaw ν θ) id) (markedSumLaw ν θ) ∧
      entropyOf (markedSumLaw ν θ) id = discreteEntropy θ + ∫ n, entropyOf (sumLaw ν n) id ∂θ := by
  have hc := markedSumLaw_conditional_entropy ν θ hi hh
  have hfst : Integrable (informationOf (markedSumLaw ν θ) Prod.fst) (markedSumLaw ν θ) := by
    rw [integrable_informationOf_iff]
    change Integrable (atomInfo (markedSumLaw ν θ).fst) (markedSumLaw ν θ).fst
    rwa [markedSumLaw_fst]
  have he : conditionedInformation (markedSumLaw ν θ) Prod.snd Prod.fst =ᵐ[markedSumLaw ν θ]
      conditionalInfo (markedSumLaw ν θ) := by
    have h := conditionedInformation_eq (markedSumLaw ν θ) Prod.snd Prod.fst
    simpa only [show (fun p : ℕ × G => (p.1,p.2)) = id from rfl,Measure.map_id] using h
  have hcond : Integrable (conditionedInformation (markedSumLaw ν θ) Prod.snd Prod.fst) (markedSumLaw ν θ) :=
    hc.1.congr he.symm
  constructor
  · change Integrable (informationOf (markedSumLaw ν θ) (fun p => (p.1,p.2))) (markedSumLaw ν θ)
    rw [informationOf_pair_chain]
    exact hfst.add hcond
  · change entropyOf (markedSumLaw ν θ) (fun p => (p.1,p.2)) = _
    rw [entropyOf_pair_chain _ _ _ hfst hcond,entropyOf_eq_discreteEntropy]
    change discreteEntropy (markedSumLaw ν θ).fst + _ = _
    rw [markedSumLaw_fst]
    congr 1
    change (∫ p, conditionedInformation (markedSumLaw ν θ) Prod.snd Prod.fst p ∂markedSumLaw ν θ) = _
    rw [integral_congr_ae he]
    exact hc.2

lemma entropyOf_nonneg {Ω : Type*} [Countable Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    {A : Type*} [Countable A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → A) : 0 ≤ entropyOf μ X :=
  integral_nonneg (informationOf_nonneg μ X)

lemma sum_entropy_integrable_bounded (ν : Measure G) [IsProbabilityMeasure ν]
    (θ : Measure ℕ) [IsProbabilityMeasure θ]
    (hi : ∀ n, Integrable (informationOf (sumLaw ν n) id) (sumLaw ν n))
    (M : ℕ) (hM : ∀ᵐ n ∂θ, n ≤ M) :
    Integrable (fun n => entropyOf (sumLaw ν n) id) θ := by
  apply (integrable_const (entropyOf (sumLaw ν M) id)).mono' (measurable_of_countable _).aestronglyMeasurable
  filter_upwards [hM] with n hn
  rw [Real.norm_eq_abs,abs_of_nonneg (entropyOf_nonneg _ _)]
  exact sumLaw_entropy_monotone ν hi hn

lemma markedSumLaw_entropy_bounds (ν : Measure G) [IsProbabilityMeasure ν]
    (θ : Measure ℕ) [IsProbabilityMeasure θ]
    (hi : ∀ n, Integrable (informationOf (sumLaw ν n) id) (sumLaw ν n))
    (hθ : Integrable (atomInfo θ) θ)
    (m M : ℕ) (hM : ∀ᵐ n ∂θ, m ≤ n ∧ n ≤ M) :
    Integrable (informationOf (markedSumLaw ν θ) id) (markedSumLaw ν θ) ∧
      discreteEntropy θ + entropyOf (sumLaw ν m) id ≤ entropyOf (markedSumLaw ν θ) id ∧
      entropyOf (markedSumLaw ν θ) id ≤ discreteEntropy θ + entropyOf (sumLaw ν M) id := by
  have hb := sum_entropy_integrable_bounded ν θ hi M (hM.mono (fun _ h => h.2))
  have hh := markedSumLaw_entropy ν θ hi hθ hb
  refine ⟨hh.1,?_,?_⟩
  · rw [hh.2]
    apply add_le_add le_rfl
    calc
      _ = ∫ _ : ℕ, entropyOf (sumLaw ν m) id ∂θ := by simp
      _ ≤ _ := integral_mono_ae (integrable_const _) hb (hM.mono (fun _ h => sumLaw_entropy_monotone ν hi h.1))
  · rw [hh.2]
    apply add_le_add le_rfl
    calc
      _ ≤ ∫ _ : ℕ, entropyOf (sumLaw ν M) id ∂θ :=
        integral_mono_ae hb (integrable_const _) (hM.mono (fun _ h => sumLaw_entropy_monotone ν hi h.2))
      _ = _ := by simp
end MarkedEntropy

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

noncomputable def countWindowLaw (k n : ℕ) : Measure ℕ :=
  (n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, Measure.dirac (k+i)

instance countWindowLaw_probability (k n : ℕ) [NeZero n] : IsProbabilityMeasure (countWindowLaw k n) := by
  constructor
  simp only [countWindowLaw,Measure.smul_apply,smul_eq_mul,Measure.finsetSum_apply,measure_univ,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast NeZero.ne n) (by finiteness)

lemma countWindowLaw_atom (k n r : ℕ) : countWindowLaw k n {r} =
    (if k ≤ r ∧ r < k+n then (n : ℝ≥0∞)⁻¹ else 0) := by
  classical
  simp only [countWindowLaw,Measure.smul_apply,smul_eq_mul,Measure.finsetSum_apply,
    Measure.dirac_apply' _ (measurableSet_singleton _),Set.indicator_apply,Set.mem_singleton_iff,Pi.one_apply]
  by_cases h : k ≤ r ∧ r < k+n
  · rw [ite_eq_left h]
    let i : Fin n := ⟨r-k,by omega⟩
    rw [Finset.sum_eq_single i]
    · simp only [show k+(i : ℕ) = r by dsimp [i];omega,ite_eq_left,mul_one]
    · intro j _ hji
      apply ite_eq_right
      intro hj
      apply hji
      apply Fin.ext
      change (j : ℕ) = r-k
      omega
    · simp
  · rw [ite_eq_right h]
    have hz : ∑ i : Fin n, (if k+(i : ℕ) = r then (1 : ℝ≥0∞) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      apply ite_eq_right
      intro hi
      exact h ⟨by omega,by omega⟩
    rw [hz,mul_zero]

lemma countWindowLaw_ae (k n : ℕ) : ∀ᵐ r ∂countWindowLaw k n, k ≤ r ∧ r < k+n := by
  filter_upwards [ae_atom_pos (countWindowLaw k n)] with r hr
  by_contra hn
  rw [countWindowLaw_atom,ite_eq_right hn] at hr
  exact hr rfl

lemma countWindowLaw_info (k n : ℕ) : atomInfo (countWindowLaw k n) =ᵐ[countWindowLaw k n]
    fun _ => Real.log n := by
  filter_upwards [countWindowLaw_ae k n] with r hr
  simp only [atomInfo,measureReal_def,countWindowLaw_atom,ite_eq_left hr,ENNReal.toReal_inv,
    ENNReal.toReal_natCast,Real.log_inv,neg_neg]

lemma countWindowLaw_entropy (k n : ℕ) [NeZero n] :
    Integrable (atomInfo (countWindowLaw k n)) (countWindowLaw k n) ∧
      discreteEntropy (countWindowLaw k n) = Real.log n := by
  constructor
  · exact (integrable_const _).congr (countWindowLaw_info k n).symm
  · change (∫ r, atomInfo (countWindowLaw k n) r ∂countWindowLaw k n) = _
    rw [integral_congr_ae (countWindowLaw_info k n)]
    simp

lemma convolution_ae_bounds (μ ν : Measure ℕ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (a b c d : ℕ) (hμ : ∀ᵐ x ∂μ, a ≤ x ∧ x ≤ b) (hν : ∀ᵐ y ∂ν, c ≤ y ∧ y ≤ d) :
    ∀ᵐ z ∂μ.conv ν, a+c ≤ z ∧ z ≤ b+d := by
  rw [Measure.conv,ae_map_iff (measurable_of_countable _).aemeasurable (Set.to_countable _).measurableSet]
  apply (Measure.ae_prod_iff_ae_ae (Set.to_countable _).measurableSet).mpr
  filter_upwards [hμ] with x hx
  filter_upwards [hν] with y hy
  exact ⟨Nat.add_le_add hx.1 hy.1,Nat.add_le_add hx.2 hy.2⟩
section MarkedWindows
variable {G : Type*} [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [AddCommGroup G]
  {α : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]

lemma nthCommonLaw_marked (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (D : Bool → α → G) (r : ℕ) :
    (nthCommonLaw ν L r).map (fun a => (listCommonCount L a,pairTotal D a)) =
      (sumLaw (commonGapLaw ν L D) r).map (fun x => (r,x)) := by
  have hc : ∀ᵐ a ∂nthCommonLaw ν L r, listCommonCount L a = r := by
    classical
    filter_upwards [ae_atom_pos (nthCommonLaw ν L r)] with a ha
    by_contra hn
    rw [nthCommonLaw_atom ν L hL he,ite_eq_right (fun h => hn h.2)] at ha
    exact ha rfl
  rw [← nthCommonLaw_pairTotal ν L hL he D r,Measure.map_map (measurable_of_countable _)
    (measurable_of_countable _)]
  apply Measure.map_congr
  filter_upwards [hc] with a ha
  exact Prod.ext ha rfl

lemma windowCommonLaw_marked (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (D : Bool → α → G) (k n : ℕ) :
    (windowCommonLaw ν L k n).map (fun a => (listCommonCount L a,pairTotal D a)) =
      markedSumLaw (commonGapLaw ν L D) (countWindowLaw k n) := by
  simp only [windowCommonLaw,Measure.map_smul]
  rw [Measure.map_finset_sum' (measurable_of_countable _).aemeasurable]
  simp_rw [nthCommonLaw_marked ν L hL he D]
  conv_rhs => unfold markedSumLaw countWindowLaw
  rw [Measure.compProd_smul_left]
  congr 1
  conv_rhs => rw [← Measure.sum_fintype,Measure.compProd_sum_left,Measure.sum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  apply Measure.ext
  intro s hs
  rw [Measure.dirac_compProd_apply hs,Measure.map_apply (measurable_of_countable _) hs]
  rfl
end MarkedWindows

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

section ChunkSums
variable {G : Type*} [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [AddCommGroup G]
  {α : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]

lemma map_add_product {E F M : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [Countable E] [Countable F] [MeasurableSingletonClass E] [MeasurableSingletonClass F]
    [AddCommMonoid M] [Countable M] [MeasurableSpace M] [MeasurableSingletonClass M]
    (μ : Measure E) (ν : Measure F) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : E → M) (g : F → M) :
    (μ.prod ν).map (fun p => f p.1+g p.2) = (μ.map f).conv (ν.map g) := by
  rw [Measure.conv,Measure.map_prod_map μ ν (measurable_of_countable _) (measurable_of_countable _),
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  rfl

noncomputable def threeCount {α : Type*} (L : Bool → α → ℕ) (a : ThreeChunk α) : ℕ :=
  listCommonCount L a.1 + (listCommonCount L a.2.1 + listCommonCount L a.2.2)

noncomputable def threeTotal (D : Bool → α → G) (a : ThreeChunk α) : G :=
  pairTotal D a.1 + (pairTotal D a.2.1 + pairTotal D a.2.2)

noncomputable def threeCountLaw (n : ℕ) : Measure ℕ :=
  (countWindowLaw n n).conv ((countWindowLaw (7*n) n).conv (countWindowLaw n n))

noncomputable def totalCountLaw (n : ℕ) : Measure ℕ :=
  (countWindowLaw n n).conv (threeCountLaw n)

instance threeCountLaw_probability (n : ℕ) [NeZero n] : IsProbabilityMeasure (threeCountLaw n) := by
  unfold threeCountLaw
  infer_instance

instance totalCountLaw_probability (n : ℕ) [NeZero n] : IsProbabilityMeasure (totalCountLaw n) := by
  unfold totalCountLaw
  infer_instance

lemma threeChunkLaw_marked (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (D : Bool → α → G) (n : ℕ) [NeZero n] :
    (threeChunkLaw ν L n).map (fun a => (threeCount L a,threeTotal D a)) =
      markedSumLaw (commonGapLaw ν L D) (threeCountLaw n) := by
  change ((windowCommonLaw ν L n n).prod
    ((windowCommonLaw ν L (7*n) n).prod (windowCommonLaw ν L n n))).map
      (fun a => (listCommonCount L a.1,pairTotal D a.1)+
        ((listCommonCount L a.2.1,pairTotal D a.2.1)+(listCommonCount L a.2.2,pairTotal D a.2.2))) = _
  rw [map_add_product (windowCommonLaw ν L n n)
    ((windowCommonLaw ν L (7*n) n).prod (windowCommonLaw ν L n n))
    (fun a => (listCommonCount L a,pairTotal D a))
    (fun a => (listCommonCount L a.1,pairTotal D a.1)+(listCommonCount L a.2,pairTotal D a.2)),
    map_add_product (windowCommonLaw ν L (7*n) n) (windowCommonLaw ν L n n)
    (fun a => (listCommonCount L a,pairTotal D a)) (fun a => (listCommonCount L a,pairTotal D a))]
  simp_rw [windowCommonLaw_marked ν L hL he D,markedSumLaw_conv]
  rfl

lemma bufferedChunkLaw_marked (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (D : Bool → α → G) (n : ℕ) [NeZero n] :
    ((markedSumLaw (commonGapLaw ν L D) (countWindowLaw n n)).prod (threeChunkLaw ν L n)).map
      (fun p => (p.1.1+threeCount L p.2,p.1.2+threeTotal D p.2)) =
      markedSumLaw (commonGapLaw ν L D) (totalCountLaw n) := by
  change ((markedSumLaw (commonGapLaw ν L D) (countWindowLaw n n)).prod (threeChunkLaw ν L n)).map
      (fun p => id p.1+(threeCount L p.2,threeTotal D p.2)) = _
  rw [map_add_product (markedSumLaw (commonGapLaw ν L D) (countWindowLaw n n))
    (threeChunkLaw ν L n) id (fun a => (threeCount L a,threeTotal D a)),Measure.map_id,threeChunkLaw_marked ν L hL he D,markedSumLaw_conv]
  rfl

lemma totalCountLaw_bounds (n : ℕ) [NeZero n] :
    ∀ᵐ r ∂totalCountLaw n, 10*n ≤ r ∧ r ≤ 14*n := by
  have h (k : ℕ) : ∀ᵐ r ∂countWindowLaw k n, k ≤ r ∧ r ≤ k+n :=
    (countWindowLaw_ae k n).mono (fun _ h => ⟨h.1,h.2.le⟩)
  have h3 := convolution_ae_bounds (countWindowLaw (7*n) n) (countWindowLaw n n)
    (7*n) (7*n+n) n (n+n) (h (7*n)) (h n)
  have h2 := convolution_ae_bounds (countWindowLaw n n)
    ((countWindowLaw (7*n) n).conv (countWindowLaw n n))
    n (n+n) (7*n+n) ((7*n+n)+(n+n)) (h n) h3
  have h1 := convolution_ae_bounds (countWindowLaw n n) (threeCountLaw n)
    n (n+n) (n+(7*n+n)) ((n+n)+((7*n+n)+(n+n))) (h n) h2
  have hlow : n+(n+(7*n+n)) = 10*n := by omega
  have hhi : (n+n)+((n+n)+((7*n+n)+(n+n))) = 14*n := by omega
  simpa only [hlow,hhi,totalCountLaw] using h1
end ChunkSums
lemma atomInfo_integrable_nat_bounded (θ : Measure ℕ) [IsProbabilityMeasure θ]
    (M : ℕ) (hM : ∀ᵐ n ∂θ, n ≤ M) :
    Integrable (atomInfo θ) θ ∧ discreteEntropy θ ≤ 1+Real.log (M+2) := by
  have hi : Integrable (fun n : ℕ => (n : ℝ)) θ := by
    apply (integrable_const (M : ℝ)).mono' (measurable_of_countable _).aestronglyMeasurable
    filter_upwards [hM] with n hn
    simpa only [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)] using (Nat.cast_le.mpr hn : (n : ℝ) ≤ M)
  have hm : (∫ n : ℕ, (n : ℝ) ∂θ) ≤ M+1 := by
    calc
      _ ≤ ∫ _ : ℕ, (M : ℝ) ∂θ := integral_mono_ae hi (integrable_const _) (hM.mono (fun _ h => Nat.cast_le.mpr h))
      _ ≤ M+1 := by simp
  simpa only [add_assoc,show (1 : ℝ)+1=2 by norm_num] using entropy_nat_moment θ hi (M+1) (by positivity) hm

section TotalEntropy
variable {G : Type*} [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [AddCommGroup G]

lemma marked_count_entropy_difference (ν : Measure G) [IsProbabilityMeasure ν]
    (hi : ∀ r, Integrable (informationOf (sumLaw ν r) id) (sumLaw ν r))
    (n : ℕ) [NeZero n] :
    Integrable (informationOf (markedSumLaw ν (countWindowLaw n n)) id) (markedSumLaw ν (countWindowLaw n n)) ∧
    Integrable (informationOf (markedSumLaw ν (totalCountLaw n)) id) (markedSumLaw ν (totalCountLaw n)) ∧
    entropyOf (markedSumLaw ν (totalCountLaw n)) id - entropyOf (markedSumLaw ν (countWindowLaw n n)) id ≤
      1+Real.log 16+entropyOf (sumLaw ν (14*n)) id-entropyOf (sumLaw ν n) id := by
  have hc : ∀ᵐ r ∂countWindowLaw n n, n ≤ r ∧ r ≤ 2*n := (countWindowLaw_ae n n).mono (fun _ h => by omega)
  have hT := totalCountLaw_bounds n
  have he := atomInfo_integrable_nat_bounded (totalCountLaw n) (14*n) (hT.mono (fun _ h => h.2))
  have hb := markedSumLaw_entropy_bounds ν (countWindowLaw n n) hi (countWindowLaw_entropy n n).1 n (2*n) hc
  have ht := markedSumLaw_entropy_bounds ν (totalCountLaw n) hi he.1 (10*n) (14*n) hT
  refine ⟨hb.1,ht.1,?_⟩
  rw [(countWindowLaw_entropy n n).2] at hb
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))
  have hl : Real.log ((14*n : ℕ)+2 : ℝ) ≤ Real.log 16+Real.log n := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    apply Real.log_le_log (by positivity)
    push_cast
    linarith
  linarith [ht.2.2,hb.2.1,he.2]
end TotalEntropy
lemma integrable_informationOf_lattice {Ω : Type*} [Countable Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {q : ℕ} (X : Ω → Fin q → ℤ) (hi : ∀ i, Integrable (fun ω => (X ω i : ℝ)) μ) :
    Integrable (informationOf μ X) μ := by
  have hn : ∀ i : Fin q, 0 ≤ ∫ ω, |(X ω i : ℝ)| ∂μ := fun i => integral_nonneg (fun ω => abs_nonneg _)
  have hs : 0 ≤ ∑ i : Fin q, ∫ ω, |(X ω i : ℝ)| ∂μ := Finset.sum_nonneg (fun i _ => hn i)
  exact (entropyOf_lattice_moment μ q X (fun i => (hi i).abs)
    (1+∑ i : Fin q, ∫ ω, |(X ω i : ℝ)| ∂μ) (by linarith) (fun i => by
      have h := Finset.single_le_sum (fun j _ => hn j) (Finset.mem_univ i)
      linarith)).1

lemma listTotal_nth_integrable {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (hW : Integrable (fun Z => (firstCommonWidth L Z : ℝ)) (twoTapeLaw ν))
    (b : Bool) (D : α → ℝ) (hi : Integrable D (ν b)) (r : ℕ) :
    Integrable (fun a => listTotal D (a b)) (nthCommonLaw ν L r) := by
  rw [nthCommonLaw,integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
    (measurable_nthCommonList L r).aemeasurable]
  have hb := commonBlock_integrable_total ν L hL he hW b D hi
  rw [commonBlockLaw,integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
    (measurable_firstCommonBlock L).aemeasurable] at hb
  have hi' (i : ℕ) : Integrable (fun Z => listTotal D (commonBlocks L Z i b)) (twoTapeLaw ν) := by
    exact ((commonRestart_measurePreserving ν L hL he).iterate i).integrable_comp_of_integrable hb
  have hs := integrable_finsetSum (Finset.range r) (fun i _ => hi' i)
  apply hs.congr
  have hZ := ae_twoTape_prop ν (fun b a => 0 < L b a)
    (fun b => measurableSet_lt measurable_const (measurable_of_countable (L b))) hL
  filter_upwards [hZ,ae_common_iterates ν L hL he] with Z hZ hiter
  exact (nthCommonList_total L D Z hZ hiter r b).symm

lemma listTotal_window_integrable {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (hW : Integrable (fun Z => (firstCommonWidth L Z : ℝ)) (twoTapeLaw ν))
    (b : Bool) (D : α → ℝ) (hi : Integrable D (ν b)) (k n : ℕ) [NeZero n] :
    Integrable (fun a => listTotal D (a b)) (windowCommonLaw ν L k n) := by
  unfold windowCommonLaw
  apply Integrable.smul_measure _ (ENNReal.inv_ne_top.mpr (by exact_mod_cast NeZero.ne n))
  rw [integrable_finsetSum_measure]
  intro i _
  exact listTotal_nth_integrable ν L hL he hW b D hi (k+i)

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

section SignedKL
variable {α : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]

noncomputable def signedChunkLaw (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (n : ℕ) : Measure (ThreeLists α × ThreeLists α) :=
  (threeChunkLaw ν L n).map splitThree

instance signedChunkLaw_probability (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (n : ℕ) [NeZero n] : IsProbabilityMeasure (signedChunkLaw ν L n) :=
  probabilityMeasure_map (measurable_of_countable _).aemeasurable

lemma signedChunk_kl (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ)
    (hu : ∀ H b, Measure.infinitePi (fun _ : ℕ => ν b) (renewalCut (L b) H) ≠ 0)
    (n : ℕ) [NeZero n] :
    InformationTheory.klDiv
      ((signedChunkLaw ν L n).map (fun a => (threeHeight L (joinThree a),a)))
      ((signedChunkLaw ν L n).map (threeHeight L ∘ joinThree) ⊗ₘ
        (signedThreeKernel (ν false) (L false) ×ₖ signedThreeKernel (ν true) (L true))) =
    InformationTheory.klDiv ((threeChunkLaw ν L n).map (fun a => (threeHeight L a,a)))
      ((threeChunkLaw ν L n).map (threeHeight L) ⊗ₘ threeBridgeKernel ν L) := by
  let : IsMarkovKernel (threeBridgeKernel ν L) := threeBridgeKernel_markov ν L hu
  have hf : (signedChunkLaw ν L n).map (threeHeight L ∘ joinThree) =
      (threeChunkLaw ν L n).map (threeHeight L) := by
    rw [signedChunkLaw,Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
    congr 1
  rw [hf,← threeBridgeKernel_split ν L hu,Measure.compProd_map (measurable_of_countable _)]
  have hg : (signedChunkLaw ν L n).map (fun a => (threeHeight L (joinThree a),a)) =
      ((threeChunkLaw ν L n).map (fun a => (threeHeight L a,a))).map
        (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (ℕ × (ℕ × ℕ))) splitThreeEquiv) := by
    rw [signedChunkLaw,Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
      Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
    congr 1
  rw [hg]
  exact klDiv_map_equiv _ _ (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) splitThreeEquiv)
end SignedKL

section SignedTotals
variable {α : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
  {G : Type*} [AddCommGroup G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

noncomputable def signedTotal (D : α → G) (a : ThreeLists α) : G :=
  listTotal D a.1 + (listTotal D a.2.1 + listTotal D a.2.2)

omit [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] in
lemma threeTotal_split (D : Bool → α → G) (a : ThreeChunk α) :
    signedTotal (D false) (splitThree a).1 + signedTotal (D true) (splitThree a).2 = threeTotal D a := by
  dsimp [signedTotal,splitThree,threeTotal,pairTotal]
  abel

lemma signed_buffer_marked (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (D : Bool → α → G) (n : ℕ) [NeZero n] :
    ((markedSumLaw (commonGapLaw ν L D) (countWindowLaw n n)).prod (signedChunkLaw ν L n)).map
      (fun p => (p.1.1+threeCount L (joinThree p.2),
        p.1.2+signedTotal (D false) p.2.1+signedTotal (D true) p.2.2)) =
      markedSumLaw (commonGapLaw ν L D) (totalCountLaw n) := by
  have hp := Measure.map_prod_map (markedSumLaw (commonGapLaw ν L D) (countWindowLaw n n))
    (threeChunkLaw ν L n) measurable_id (measurable_of_countable splitThree)
  simp only [Measure.map_id] at hp
  rw [signedChunkLaw,hp,
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  have hf : (fun p : (ℕ × G) × ThreeChunk α =>
      (p.1.1+threeCount L (joinThree (splitThree p.2)),
        p.1.2+signedTotal (D false) (splitThree p.2).1+signedTotal (D true) (splitThree p.2).2)) =
      (fun p => (p.1.1+threeCount L p.2,p.1.2+threeTotal D p.2)) := by
    funext p
    rw [join_splitThree,add_assoc,threeTotal_split]
  change Measure.map (fun p : (ℕ × G) × ThreeChunk α =>
    (p.1.1+threeCount L (joinThree (splitThree p.2)),
      p.1.2+signedTotal (D false) (splitThree p.2).1+signedTotal (D true) (splitThree p.2).2)) _ = _
  rw [hf,bufferedChunkLaw_marked ν L hL he D]
end SignedTotals
section InformationTransport
variable {Ω Ξ A : Type*} [Countable Ω] [Countable Ξ] [Countable A]
  [MeasurableSpace Ω] [MeasurableSpace Ξ] [MeasurableSpace A]
  [MeasurableSingletonClass Ω] [MeasurableSingletonClass Ξ] [MeasurableSingletonClass A]

omit [Countable A] [MeasurableSingletonClass A] in
lemma integrable_informationOf_map_iff (μ : Measure Ω) (F : Ω → Ξ) (X : Ξ → A) :
    Integrable (informationOf (μ.map F) X) (μ.map F) ↔
      Integrable (informationOf μ (X ∘ F)) μ := by
  rw [integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
    (measurable_of_countable _).aemeasurable,informationOf_map]

omit [Countable A] [MeasurableSingletonClass A] in
lemma integrable_informationOf_prod_fst (μ : Measure Ω) (ν : Measure Ξ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (X : Ω → A)
    (hi : Integrable (informationOf μ X) μ) :
    Integrable (informationOf (μ.prod ν) (X ∘ Prod.fst)) (μ.prod ν) := by
  rw [← integrable_informationOf_map_iff,Measure.map_fst_prod,measure_univ,one_smul]
  exact hi

omit [Countable A] [MeasurableSingletonClass A] in
lemma integrable_informationOf_prod_snd (μ : Measure Ω) (ν : Measure Ξ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (X : Ξ → A)
    (hi : Integrable (informationOf ν X) ν) :
    Integrable (informationOf (μ.prod ν) (X ∘ Prod.snd)) (μ.prod ν) := by
  rw [← integrable_informationOf_map_iff,Measure.map_snd_prod,measure_univ,one_smul]
  exact hi
end InformationTransport

lemma entropyOf_pair_comm {Ω A B : Type*} [Countable Ω] [Countable A] [Countable B]
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass Ω] [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (μ : Measure Ω) (X : Ω → A) (Y : Ω → B) :
    entropyOf μ (fun ω => (X ω,Y ω)) = entropyOf μ (fun ω => (Y ω,X ω)) := by
  unfold entropyOf
  rw [informationOf_pair_comm]

section ExperimentInformation
variable {α : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]

lemma signed_chunk_positive_integrable (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (hW : Integrable (fun Z => (firstCommonWidth L Z : ℝ)) (twoTapeLaw ν))
    (D : α → ℝ) (hi : Integrable D (ν false)) (n : ℕ) [NeZero n] :
    Integrable (fun a => signedTotal D a.1) (signedChunkLaw ν L n) := by
  rw [signedChunkLaw,integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
    (measurable_of_countable _).aemeasurable]
  have h0 := listTotal_window_integrable ν L hL he hW false D hi n n
  have h1 := listTotal_window_integrable ν L hL he hW false D hi (7*n) n
  exact (h0.comp_fst _).add (((h1.comp_fst _).add (h0.comp_snd _)).comp_snd _)

lemma signed_chunk_positive_info {q : ℕ}
    (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (hW : Integrable (fun Z => (firstCommonWidth L Z : ℝ)) (twoTapeLaw ν))
    (D : α → Fin q → ℤ) (hi : ∀ i, Integrable (fun a => (D a i : ℝ)) (ν false))
    (n : ℕ) [NeZero n] :
    Integrable (informationOf (signedChunkLaw ν L n) (fun a => signedTotal D a.1)) (signedChunkLaw ν L n) := by
  apply integrable_informationOf_lattice
  intro i
  have h := signed_chunk_positive_integrable ν L hL he hW (fun a => (D a i : ℝ)) (hi i) n
  simpa only [signedTotal,listTotal,Pi.add_apply,Finset.sum_apply,Int.cast_add,Int.cast_sum] using h
end ExperimentInformation

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

section ActualComparison
variable {α G : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [AddCommGroup G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

noncomputable def experimentLaw (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (D : Bool → α → G) (n : ℕ) :
    Measure (((ℕ × (ℕ × ℕ)) × G) × (ThreeLists α × ThreeLists α)) :=
  ((markedSumLaw (commonGapLaw ν L D) (countWindowLaw n n)).prod (signedChunkLaw ν L n)).map
    (fun p => ((threeHeight L (joinThree p.2),p.1.2+signedTotal (D false) p.2.1),p.2))

noncomputable def experimentReference (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (D : Bool → α → G) (n : ℕ) :
    Measure (((ℕ × (ℕ × ℕ)) × G) × (ThreeLists α × ThreeLists α)) :=
  (experimentLaw ν L D n).fst ⊗ₘ
    (signedThreeKernel (ν false) (L false) ×ₖ signedThreeKernel (ν true) (L true)).comap Prod.fst measurable_fst

lemma experiment_kl_comparison (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (hW : Integrable (fun Z => (firstCommonWidth L Z : ℝ)) (twoTapeLaw ν))
    (hu : ∀ H b, Measure.infinitePi (fun _ : ℕ => ν b) (renewalCut (L b) H) ≠ 0)
    (c : ℝ) (hc : 0 < c) (hlo : ∀ H, ENNReal.ofReal c ≤ renewalPairMass ν L H)
    (D : Bool → α → G)
    (hgap : ∀ r, Integrable (informationOf (sumLaw (commonGapLaw ν L D) r) id) (sumLaw (commonGapLaw ν L D) r))
    (n : ℕ) [NeZero n]
    (hD : Integrable (informationOf (signedChunkLaw ν L n) (fun a => signedTotal (D false) a.1)) (signedChunkLaw ν L n)) :
    InformationTheory.klDiv (experimentLaw ν L D n) (experimentReference ν L D n) ≠ ∞ ∧
      (InformationTheory.klDiv (experimentLaw ν L D n) (experimentReference ν L D n)).toReal ≤
        6*(1+Real.log (8*((∫ Z, (firstCommonWidth L Z : ℝ) ∂twoTapeLaw ν)+1)+1)) +
        1+Real.log 16 + entropyOf (sumLaw (commonGapLaw ν L D) (14*n)) id -
        entropyOf (sumLaw (commonGapLaw ν L D) n) id := by
  let π := markedSumLaw (commonGapLaw ν L D) (countWindowLaw n n)
  let ρ := signedChunkLaw ν L n
  let T : (ℕ × G) × (ThreeLists α × ThreeLists α) → ℕ × G :=
    fun p => (p.1.1+threeCount L (joinThree p.2),
      p.1.2+signedTotal (D false) p.2.1+signedTotal (D true) p.2.2)
  let : IsMarkovKernel (signedThreeKernel (ν false) (L false)) := signedThreeKernel_markov _ _ (fun H => hu H false)
  let : IsMarkovKernel (signedThreeKernel (ν true) (L true)) := signedThreeKernel_markov _ _ (fun H => hu H true)
  have hmark : (π.prod ρ).map T = markedSumLaw (commonGapLaw ν L D) (totalCountLaw n) :=
    signed_buffer_marked ν L hL he D n
  have hent := marked_count_entropy_difference (commonGapLaw ν L D) hgap n
  have hpair : Integrable (informationOf (π.prod ρ) T) (π.prod ρ) := by
    have ht := hent.2.1
    rw [← hmark,integrable_informationOf_map_iff] at ht
    exact ht
  have hT := integrable_informationOf_comp (π.prod ρ) T Prod.fst hpair
  have hS := integrable_informationOf_comp (π.prod ρ) T Prod.snd hpair
  have hU := integrable_informationOf_comp π id Prod.fst hent.1
  have hd := integrable_informationOf_comp π id Prod.snd hent.1
  have hzpair := integrable_informationOf_pair (π.prod ρ) (fun p => p.1.2)
    (fun p => signedTotal (D false) p.2.1)
    (integrable_informationOf_prod_fst π ρ Prod.snd hd)
    (integrable_informationOf_prod_snd π ρ (fun a => signedTotal (D false) a.1) hD)
  have hZ := integrable_informationOf_comp (π.prod ρ) _ (fun p : G × G => p.1+p.2) hzpair
  have hkl := threeChunk_kl_uniform ν L hL he hW hu c hc hlo n
  dsimp only at hkl
  rw [← signedChunk_kl ν L hu n] at hkl
  have hb := buffered_reference_comparison π ρ (threeHeight L ∘ joinThree)
    (signedTotal (D false)) (signedTotal (D true)) (threeCount L ∘ joinThree)
    (signedThreeKernel (ν false) (L false)) (signedThreeKernel (ν true) (L true))
    hkl.1 hU hd hZ hT hS
  have ht : entropyOf (π.prod ρ) (fun p =>
      (p.1.2+signedTotal (D false) p.2.1+signedTotal (D true) p.2.2,
        p.1.1+threeCount L (joinThree p.2))) =
      entropyOf (markedSumLaw (commonGapLaw ν L D) (totalCountLaw n)) id := by
    rw [entropyOf_pair_comm]
    change entropyOf (π.prod ρ) T = _
    rw [← hmark,entropyOf_map]
    rfl
  have hπ : entropyOf π (fun p => (p.2,p.1)) = entropyOf π id := by
    rw [entropyOf_pair_comm]
    rfl
  change InformationTheory.klDiv (experimentLaw ν L D n) (experimentReference ν L D n) ≠ ∞ ∧ _
  refine ⟨hb.1,?_⟩
  dsimp only [Function.comp_apply] at hb
  rw [ht,hπ] at hb
  have hh := hent.2.2
  dsimp only [π,ρ] at hb hh ⊢
  dsimp only [experimentLaw,experimentReference]
  linarith only [hb.2,hkl.2,hh]
end ActualComparison

lemma sumLaw_lattice_information {q : ℕ} (ν : Measure (Fin q → ℤ)) [IsProbabilityMeasure ν]
    (hi : ∀ i, Integrable (fun x => |(x i : ℝ)|) ν) (n : ℕ) :
    Integrable (informationOf (sumLaw ν n) id) (sumLaw ν n) := by
  let a := 1+∑ i, ∫ x, |(x i : ℝ)| ∂ν
  have hm (i : Fin q) : (∫ x, |(x i : ℝ)| ∂ν) ≤ a := by
    have h : (∫ x, |(x i : ℝ)| ∂ν) ≤ ∑ j : Fin q, ∫ x, |(x j : ℝ)| ∂ν :=
      Finset.single_le_sum (f := fun j : Fin q => ∫ x, |(x j : ℝ)| ∂ν) (fun j _ => integral_nonneg (fun x : Fin q → ℤ => abs_nonneg (x j : ℝ))) (Finset.mem_univ i)
    dsimp [a]
    linarith
  exact (sumLaw_lattice_entropy ν hi a (by
    dsimp [a]
    have h : 0 ≤ ∑ i : Fin q, ∫ x, |(x i : ℝ)| ∂ν := Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => abs_nonneg _))
    linarith) hm n).1

lemma lattice_experiment_kl_comparison {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] {q : ℕ}
    (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (hW : Integrable (fun Z => (firstCommonWidth L Z : ℝ)) (twoTapeLaw ν))
    (hu : ∀ H b, Measure.infinitePi (fun _ : ℕ => ν b) (renewalCut (L b) H) ≠ 0)
    (c : ℝ) (hc : 0 < c) (hlo : ∀ H, ENNReal.ofReal c ≤ renewalPairMass ν L H)
    (D : Bool → α → Fin q → ℤ) (hi : ∀ b i, Integrable (fun a => (D b a i : ℝ)) (ν b))
    (n : ℕ) [NeZero n] :
    InformationTheory.klDiv (experimentLaw ν L D n) (experimentReference ν L D n) ≠ ∞ ∧
      (InformationTheory.klDiv (experimentLaw ν L D n) (experimentReference ν L D n)).toReal ≤
        6*(1+Real.log (8*((∫ Z, (firstCommonWidth L Z : ℝ) ∂twoTapeLaw ν)+1)+1)) +
        1+Real.log 16 + entropyOf (sumLaw (commonGapLaw ν L D) (14*n)) id -
        entropyOf (sumLaw (commonGapLaw ν L D) n) id := by
  exact experiment_kl_comparison ν L hL he hW hu c hc hlo D
    (sumLaw_lattice_information _ (commonGapLaw_lattice_integrable ν L hL he hW D hi)) n
    (signed_chunk_positive_info ν L hL he hW (D false) (hi false) n)

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

def wordPairCylinder {d : ℕ} (p : Word d × Word d) : Set (Path d × Path d) :=
  wordCylinder p.1 ×ˢ wordCylinder p.2

lemma measurableSet_wordPairCylinder {d : ℕ} (p : Word d × Word d) :
    MeasurableSet (wordPairCylinder p) :=
  (measurableSet_pathCylinder _ _).prod (measurableSet_pathCylinder _ _)

lemma wordPair_transfer {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x z : Site d) (a b : Word d) (h : Disjoint (wordDepartures a) (wordDepartures b)) :
    annealed μ x (wordCylinder a) * annealed μ z (wordCylinder b) =
      ∫⁻ ω, quenchedKernel d (ω,x) (wordCylinder a) * quenchedKernel d (ω,z) (wordCylinder b)
        ∂environmentLaw μ := by
  simp only [wordCylinder,annealed_cylinder,quenchedKernel_cylinder]
  split_ifs <;> try simp only [zero_mul,mul_zero,lintegral_zero]
  exact (path_weights_disjoint μ a.1 b.1 (wordPath a) (wordPath b) (by
    intro i hi j hj hij
    exact Set.disjoint_left.mp h ⟨i,hi,rfl⟩ ⟨j,hj,hij.symm⟩)).symm

noncomputable def freshPair {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x z : Site d) : Measure (Environment d × (Path d × Path d)) :=
  environmentLaw μ ⊗ₘ (freshPathKernel x ×ₖ freshPathKernel z)

instance {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ] (x z : Site d) :
    IsProbabilityMeasure (freshPair μ x z) := by
  unfold freshPair
  infer_instance

lemma freshPair_apply {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ] (x z : Site d)
    {E : Set (Environment d × (Path d × Path d))} (hE : MeasurableSet E) :
    freshPair μ x z E = ∫⁻ ω, ((quenchedKernel d (ω,x)).prod (quenchedKernel d (ω,z)))
      (Prod.mk ω ⁻¹' E) ∂environmentLaw μ := by
  rw [freshPair,Measure.compProd_apply hE]
  simp only [Kernel.prod_apply,freshPathKernel,Kernel.comap_apply]

lemma freshPair_first {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ] (x z : Site d)
    {E : Set (Environment d × Path d)} (hE : MeasurableSet E) :
    freshPair μ x z {ξ | (ξ.1,ξ.2.1) ∈ E} = freshJoint μ x E := by
  change freshPair μ x z ((fun ξ => (ξ.1,ξ.2.1)) ⁻¹' E) = _
  rw [freshPair_apply μ x z (hE.preimage (measurable_fst.prodMk measurable_snd.fst)),
    freshJoint_apply μ x hE]
  apply lintegral_congr
  intro ω
  rw [show (Prod.mk ω ⁻¹' (fun ξ : Environment d × (Path d × Path d) => (ξ.1,ξ.2.1)) ⁻¹' E) =
    (Prod.mk ω ⁻¹' E) ×ˢ Set.univ by ext p; simp]
  rw [Measure.prod_prod,measure_univ,mul_one]

lemma freshPair_second {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ] (x z : Site d)
    {E : Set (Environment d × Path d)} (hE : MeasurableSet E) :
    freshPair μ x z {ξ | (ξ.1,ξ.2.2) ∈ E} = freshJoint μ z E := by
  change freshPair μ x z ((fun ξ => (ξ.1,ξ.2.2)) ⁻¹' E) = _
  rw [freshPair_apply μ x z (hE.preimage (measurable_fst.prodMk measurable_snd.snd)),
    freshJoint_apply μ z hE]
  apply lintegral_congr
  intro ω
  rw [show (Prod.mk ω ⁻¹' (fun ξ : Environment d × (Path d × Path d) => (ξ.1,ξ.2.2)) ⁻¹' E) =
    Set.univ ×ˢ (Prod.mk ω ⁻¹' E) by ext p; simp]
  rw [Measure.prod_prod,measure_univ,one_mul]

lemma wordPairFamily_transfer {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x z : Site d) (A : Set (Word d × Word d))
    (hdis : Pairwise (fun a b : A => Disjoint (wordPairCylinder a.val) (wordPairCylinder b.val)))
    (hrows : ∀ p ∈ A, Disjoint (wordDepartures p.1) (wordDepartures p.2)) :
    ((annealed μ x).prod (annealed μ z)) (⋃ p : A, wordPairCylinder p.val) =
      freshPair μ x z {ξ | ξ.2 ∈ ⋃ p : A, wordPairCylinder p.val} := by
  have hm := MeasurableSet.iUnion (fun p : A => measurableSet_wordPairCylinder p.val)
  change ((annealed μ x).prod (annealed μ z)) (⋃ p : A, wordPairCylinder p.val) =
    freshPair μ x z (Prod.snd ⁻¹' (⋃ p : A, wordPairCylinder p.val))
  rw [freshPair_apply μ x z (hm.preimage measurable_snd),
    measure_iUnion hdis (fun p => measurableSet_wordPairCylinder p.val)]
  simp only [wordPairCylinder,Measure.prod_prod]
  simp_rw [wordPair_transfer μ x z _ _ (hrows _ (Subtype.property _))]
  rw [← lintegral_tsum]
  · apply lintegral_congr
    intro ω
    change (∑' p : A, quenchedKernel d (ω,x) (wordCylinder p.val.1) *
      quenchedKernel d (ω,z) (wordCylinder p.val.2)) =
        ((quenchedKernel d (ω,x)).prod (quenchedKernel d (ω,z))) (⋃ p : A, wordPairCylinder p.val)
    rw [measure_iUnion hdis (fun p => measurableSet_wordPairCylinder p.val)]
    apply tsum_congr
    intro p
    rw [wordPairCylinder,Measure.prod_prod]
  · intro p
    exact ((((quenchedKernel d).measurable_coe (measurableSet_pathCylinder _ _)).comp
      (measurable_id.prodMk measurable_const)).mul
      (((quenchedKernel d).measurable_coe (measurableSet_pathCylinder _ _)).comp
        (measurable_id.prodMk measurable_const))).aemeasurable

lemma wordPairFamily_visit_bound {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x z : Site d) (A : Set (Word d × Word d))
    (hdis : Pairwise (fun a b : A => Disjoint (wordPairCylinder a.val) (wordPairCylinder b.val)))
    (hrows : ∀ p ∈ A, Disjoint (wordDepartures p.1) (wordDepartures p.2))
    (V W : Set (Environment d × Path d)) (hV : MeasurableSet V) (hW : MeasurableSet W)
    (hcover : ∀ ξ : Environment d × (Path d × Path d),
      (∃ p : A, ξ.2 ∈ wordPairCylinder p.val) → (ξ.1,ξ.2.1) ∈ V ∨ (ξ.1,ξ.2.2) ∈ W) :
    ((annealed μ x).prod (annealed μ z)) (⋃ p : A, wordPairCylinder p.val) ≤
      freshJoint μ x V + freshJoint μ z W := by
  rw [wordPairFamily_transfer μ x z A hdis hrows]
  calc
    _ ≤ freshPair μ x z ({ξ | (ξ.1,ξ.2.1) ∈ V} ∪ {ξ | (ξ.1,ξ.2.2) ∈ W}) :=
      measure_mono (fun ξ hξ => hcover ξ (Set.mem_iUnion.mp hξ))
    _ ≤ _ := (measure_union_le _ _).trans_eq (by rw [freshPair_first μ x z hV,freshPair_second μ x z hW])

def firstContactPairs {d : ℕ} (T R S K : Set (Site d)) : Set (Word d × Word d) :=
  {p | firstHitWord T p.1 ∧ firstHitWord (wordDepartures p.1) p.2 ∧
    (∃ i < p.1.1, wordPath p.1 i = wordEnd p.2 ∧
      (∃ j ≤ i, wordPath p.1 j ∈ R) ∧ ∀ j ≤ i, wordPath p.1 j ∉ K) ∧
    (∃ j ≤ p.2.1, wordPath p.2 j ∈ S) ∧ ∀ j ≤ p.2.1, wordPath p.2 j ∉ K}

lemma firstContactPairs_rows {d : ℕ} (T R S K : Set (Site d)) (p : Word d × Word d)
    (hp : p ∈ firstContactPairs T R S K) :
    Disjoint (wordDepartures p.1) (wordDepartures p.2) := by
  apply Set.disjoint_left.mpr
  rintro y hy ⟨j,hj,hjy⟩
  exact hp.2.1.2 j hj (hjy ▸ hy)

lemma firstContactPairs_disjoint {d : ℕ} (T R S K : Set (Site d)) :
    Pairwise (fun p q : firstContactPairs T R S K =>
      Disjoint (wordPairCylinder p.val) (wordPairCylinder q.val)) := by
  intro p q hpq
  apply Set.disjoint_left.mpr
  rintro ⟨X,Y⟩ ⟨hp1,hp2⟩ ⟨hq1,hq2⟩
  by_cases h1 : p.val.1 = q.val.1
  · have h2 : p.val.2 ≠ q.val.2 := by
      intro h2
      apply hpq
      exact Subtype.ext (Prod.ext h1 h2)
    have ha := p.property.2.1
    have hb := q.property.2.1
    rw [← h1] at hb
    exact Set.disjoint_left.mp (firstHitWords_prefixFree (wordDepartures p.val.1)
      (i := ⟨p.val.2,ha⟩) (j := ⟨q.val.2,hb⟩)
      (fun h => h2 (congrArg Subtype.val h))) hp2 hq2
  · exact Set.disjoint_left.mp (firstHitWords_prefixFree T
      (i := ⟨p.val.1,p.property.1⟩) (j := ⟨q.val.1,q.property.1⟩)
      (fun h => h1 (congrArg Subtype.val h))) hp1 hq1

lemma firstContactPairs_classify {d : ℕ} (T R S K : Set (Site d))
    (A : Set (Site d)) (p : firstContactPairs T R S K) (X Y : Path d)
    (h : (X,Y) ∈ wordPairCylinder p.val) :
    X ∈ visitAfter R (A \ K) K ∨ Y ∈ visitAfter S (Aᶜ \ K) K := by
  change (X ∈ wordCylinder p.val.1 ∧ Y ∈ wordCylinder p.val.2) at h
  obtain ⟨i,hi,he,⟨j,hji,hR⟩,hK⟩ := p.property.2.2.1
  have hyK : wordEnd p.val.2 ∉ K := by rw [← he];exact hK i le_rfl
  by_cases hy : wordEnd p.val.2 ∈ A
  · left
    refine ⟨i,?_,⟨j,hji,?_⟩,fun k hk => ?_⟩
    · rw [h.1 i hi.le,he]
      exact ⟨hy,hyK⟩
    · rw [h.1 j (hji.trans hi.le)]
      exact hR
    · rw [h.1 k (hk.trans hi.le)]
      exact hK k hk
  · right
    obtain ⟨j,hj,hS⟩ := p.property.2.2.2.1
    refine ⟨p.val.2.1,?_,⟨j,hj,?_⟩,fun k hk => ?_⟩
    · rw [h.2 _ le_rfl]
      exact ⟨hy,hyK⟩
    · rw [h.2 j hj]
      exact hS
    · rw [h.2 k hk]
      exact p.property.2.2.2.2 k hk

lemma firstContactPairs_visit_bound {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x z : Site d) (T R S K : Set (Site d)) (A : Environment d → Set (Site d))
    (hA : ∀ y, MeasurableSet {ω | y ∈ A ω}) :
    ((annealed μ x).prod (annealed μ z))
      (⋃ p : firstContactPairs T R S K, wordPairCylinder p.val) ≤
      freshJoint μ x {ξ | ξ.2 ∈ visitAfter R (A ξ.1 \ K) K} +
      freshJoint μ z {ξ | ξ.2 ∈ visitAfter S ((A ξ.1)ᶜ \ K) K} := by
  apply wordPairFamily_visit_bound μ x z _ (firstContactPairs_disjoint T R S K)
    (firstContactPairs_rows T R S K) _ _
    (measurable_random_visitAfter _ _ _ (fun y => (hA y).diff (MeasurableSet.const _)))
    (measurable_random_visitAfter _ _ _ (fun y => (hA y).compl.diff (MeasurableSet.const _)))
  rintro ⟨ω,X,Y⟩ ⟨p,hp⟩
  exact firstContactPairs_classify T R S K (A ω) p X Y hp

lemma freshJoint_visitAfter_bound {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x : Site d) (R B C : Set (Site d)) (A : Environment d → Set (Site d))
    (hA : ∀ y, MeasurableSet {ω | y ∈ A ω}) (c : ℝ≥0∞)
    (hc : ∀ᵐ ω ∂environmentLaw μ, ∀ y ∈ A ω,
      c ≤ quenchedKernel d (ω,y) (hitBefore B C)) :
    c * freshJoint μ x {ξ | ξ.2 ∈ visitAfter R (A ξ.1) (B ∪ C)} ≤
      annealed μ x (hitBefore R B ∩ hitBefore B C) := by
  rw [freshJoint_apply μ x (measurable_random_visitAfter _ _ _ hA),
    annealed_apply μ x ((measurableSet_hitBefore _ _).inter (measurableSet_hitBefore _ _))]
  apply (lintegral_const_mul_le _ _).trans
  apply lintegral_mono_ae
  filter_upwards [hc] with ω hω
  exact quenched_visitAfter_bound ω x R (A ω) B C c hω

lemma firstContactPairs_raw_bound {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x z : Site d) (T R S B C : Set (Site d))
    (hex : ∀ᵐ ω ∂environmentLaw μ, ∀ y,
      quenchedKernel d (ω,y) (hitBefore B C) + quenchedKernel d (ω,y) (hitBefore C B) = 1) :
    ((annealed μ x).prod (annealed μ z))
      (⋃ p : firstContactPairs T R S (B ∪ C), wordPairCylinder p.val) ≤
      2*(annealed μ x (hitBefore R B ∩ hitBefore B C) +
        annealed μ z (hitBefore S C ∩ hitBefore C B)) := by
  let A : Environment d → Set (Site d) := fun ω =>
    {y | (2 : ℝ≥0∞)⁻¹ ≤ quenchedKernel d (ω,y) (hitBefore B C)}
  have hA (y : Site d) : MeasurableSet {ω | y ∈ A ω} :=
    measurableSet_le measurable_const (((quenchedKernel d).measurable_coe (measurableSet_hitBefore _ _)).comp
      (measurable_id.prodMk measurable_const))
  have hv := firstContactPairs_visit_bound μ x z T R S (B ∪ C) A hA
  have h1 := freshJoint_visitAfter_bound μ x R B C (fun ω => A ω \ (B ∪ C))
    (fun y => (hA y).diff (MeasurableSet.const _)) (2 : ℝ≥0∞)⁻¹ (by
      filter_upwards [] with ω
      exact fun y hy => hy.1)
  have h2 := freshJoint_visitAfter_bound μ z S C B (fun ω => (A ω)ᶜ \ (B ∪ C))
    (fun y => (hA y).compl.diff (MeasurableSet.const _)) (2 : ℝ≥0∞)⁻¹ (by
      filter_upwards [hex] with ω hω
      intro y hy
      have hy' : quenchedKernel d (ω,y) (hitBefore B C) ≤ (2 : ℝ≥0∞)⁻¹ := le_of_lt (lt_of_not_ge hy.1)
      apply (ENNReal.add_le_add_iff_left (by norm_num : (2 : ℝ≥0∞)⁻¹ ≠ ∞)).mp
      calc
        (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ = 1 := ENNReal.inv_two_add_inv_two
        _ = _ := (hω y).symm
        _ ≤ _ := add_le_add hy' le_rfl)
  rw [Set.union_comm C B] at h2
  have h : (2 : ℝ≥0∞)⁻¹ * ((annealed μ x).prod (annealed μ z))
      (⋃ p : firstContactPairs T R S (B ∪ C), wordPairCylinder p.val) ≤
      annealed μ x (hitBefore R B ∩ hitBefore B C) +
        annealed μ z (hitBefore S C ∩ hitBefore C B) := by
    calc
      _ ≤ (2 : ℝ≥0∞)⁻¹ * (freshJoint μ x {ξ | ξ.2 ∈ visitAfter R (A ξ.1 \ (B ∪ C)) (B ∪ C)} +
        freshJoint μ z {ξ | ξ.2 ∈ visitAfter S ((A ξ.1)ᶜ \ (B ∪ C)) (B ∪ C)}) := by gcongr
      _ ≤ _ := by rw [mul_add]; exact add_le_add h1 h2
  have h' := mul_le_mul (show (2 : ℝ≥0∞) ≤ 2 from le_rfl) h zero_le zero_le
  simpa only [← mul_assoc,ENNReal.mul_inv_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞),one_mul] using h'

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

lemma quenched_axis_exit_sum {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d) (k N : ℤ) (hkN : k ≤ N) :
    ∀ᵐ ω ∂environmentLaw μ, ∀ y,
      quenchedKernel d (ω,y) (hitBefore (axisLower e k) (axisUpper e N)) +
        quenchedKernel d (ω,y) (hitBefore (axisUpper e N) (axisLower e k)) = 1 := by
  have hAE : ∀ᵐ ω ∂environmentLaw μ, ∀ y, ∀ᵐ X ∂quenchedKernel d (ω,y),
      ∃ n, X n ∈ axisLower e k ∪ axisUpper e N := by
    rw [ae_all_iff]
    intro y
    apply annealed_ae_quenched μ y
    · change MeasurableSet {X : Path d | ∃ n, X n ∈ axisLower e k ∪ axisUpper e N}
      simp only [Set.ofPred_exists]
      exact MeasurableSet.iUnion (fun n : ℕ =>
        (Set.to_countable (axisLower e k ∪ axisUpper e N)).measurableSet.preimage
          (measurable_pi_apply (X := fun _ : ℕ => Site d) n))
    · exact annealed_axis_exit μ hell e y k N
  filter_upwards [hAE] with ω hω
  intro y
  rw [← measure_union (hitBefore_disjoint _ _) (measurableSet_hitBefore _ _),
    hitBefore_union_eq_eventual _ _ (axis_barriers_disjoint e hkN)]
  have hm : MeasurableSet {X : Path d | ∃ n, X n ∈ axisLower e k ∪ axisUpper e N} := by
    simp only [Set.ofPred_exists]
    exact MeasurableSet.iUnion (fun n : ℕ =>
      (Set.to_countable (axisLower e k ∪ axisUpper e N)).measurableSet.preimage
        (measurable_pi_apply (X := fun _ : ℕ => Site d) n))
  exact (mem_ae_iff_prob_eq_one hm).mp (hω y)

lemma shiftPath_preimage_hitBefore {d : ℕ} (z : Site d) (A B : Set (Site d)) :
    shiftPath z ⁻¹' hitBefore A B = hitBefore ((fun x => x+z) ⁻¹' A) ((fun x => x+z) ⁻¹' B) := by
  rfl

lemma axis_barriers_from_top {d : ℕ} (e : Step d) (z : Site d) (N n : ℕ)
    (hz : axisHeight e z = (N : ℤ)-1) :
    (fun x => x+z) ⁻¹' axisUpper e N = axisLower (oppositeStep e) 0 ∧
    (fun x => x+z) ⁻¹' axisLower e 0 = axisUpper (oppositeStep e) N ∧
    (fun x => x+z) ⁻¹' axisLower e ((N : ℤ)-n) = axisUpper (oppositeStep e) n := by
  refine ⟨?_,?_,?_⟩ <;> ext x <;>
    simp only [axisLower,axisUpper,Set.mem_preimage,Set.mem_ofPred_eq,axisHeight_add,
      axisHeight_opposite,hz] <;> omega

lemma annealed_axis_return_from_top {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d) (z : Site d) {n N : ℕ} (hnN : n ≤ N)
    (hz : axisHeight e z = (N : ℤ)-1) :
    annealed μ z (hitBefore (axisLower e ((N : ℤ)-n)) (axisUpper e N) ∩
      hitBefore (axisUpper e N) (axisLower e 0)) =
      axisReachProb μ (oppositeStep e) n - axisReachProb μ (oppositeStep e) N := by
  have hs := annealed_shift μ 0 z
  rw [zero_add] at hs
  rw [← hs,Measure.map_apply (measurable_shiftPath z)
    ((measurableSet_hitBefore _ _).inter (measurableSet_hitBefore _ _)),
    Set.preimage_inter,shiftPath_preimage_hitBefore,shiftPath_preimage_hitBefore,
    (axis_barriers_from_top e z N n hz).1,(axis_barriers_from_top e z N n hz).2.1,
    (axis_barriers_from_top e z N n hz).2.2]
  exact annealed_axis_return_probability μ hell (oppositeStep e) hnN

lemma firstContactPairs_axis_bound {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d) (z : Site d) (T : Set (Site d))
    {n N : ℕ} (hnN : n ≤ N) (hz : axisHeight e z = (N : ℤ)-1) :
    ((annealed μ 0).prod (annealed μ z))
      (⋃ p : firstContactPairs T (axisUpper e n) (axisLower e ((N : ℤ)-n))
        (axisLower e 0 ∪ axisUpper e N), wordPairCylinder p.val) ≤
      2*((axisReachProb μ e n-axisReachProb μ e N) +
        (axisReachProb μ (oppositeStep e) n-axisReachProb μ (oppositeStep e) N)) := by
  have h := firstContactPairs_raw_bound μ 0 z T (axisUpper e n) (axisLower e ((N : ℤ)-n))
    (axisLower e 0) (axisUpper e N) (quenched_axis_exit_sum μ hell e 0 N (by positivity))
  rw [annealed_axis_return_probability μ hell e hnN,
    annealed_axis_return_from_top μ hell e z hnN hz] at h
  exact h

def translateWord {d : ℕ} (z : Site d) (a : Word d) : Word d :=
  ⟨a.1,fun i => a.2 i + z⟩

lemma wordPath_translate {d : ℕ} (z : Site d) (a : Word d) (i : ℕ) (hi : i ≤ a.1) :
    wordPath (translateWord z a) i = wordPath a i + z := by
  simp [wordPath,translateWord,extendPrefix,Finset.mem_Iic,hi]

lemma wordEnd_translate {d : ℕ} (z : Site d) (a : Word d) :
    wordEnd (translateWord z a) = wordEnd a + z := wordPath_translate z a a.1 le_rfl

def AxisBridgeWord {d : ℕ} (e : Step d) (H : ℕ) (a : Word d) : Prop :=
  axisHeight e (wordEnd a) = (H : ℤ) ∧
    ∀ i < a.1, 0 ≤ axisHeight e (wordPath a i) ∧ axisHeight e (wordPath a i) < (H : ℤ)

lemma axisBridgeWord_recordWord {d : ℕ} (e : Step d) (H : ℕ) (X : Path d)
    (h0 : X 0 = 0) (hX : nearestNeighbour X) (hH : X ∈ reachRecord (axisDirection e) H) :
    AxisBridgeWord e H (recordWord (axisDirection e) H X) := by
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hH
  have hh := axis_record_height e X n h0 (fun i _ => axisHeight_nn_le e X hX i) hn.1
  rw [hn.2.1] at hh
  rw [recordWord_eq (axisDirection e) H X hn]
  dsimp only [AxisBridgeWord]
  constructor
  · change axisHeight e (wordPath (prefixWord n X) n) = _
    rw [wordPath_prefixWord n X le_rfl,hh]
  · intro i hi
    change i < n at hi
    rw [wordPath_prefixWord n X hi.le]
    constructor
    · have h := hn.2.2 i hi.le
      rw [height_axisDirection] at h
      exact_mod_cast h
    · rcases hn.1 with rfl | hr
      · omega
      · have h := hr.2 i hi
        rw [height_axisDirection,height_axisDirection,hh] at h
        exact_mod_cast h

lemma rawBridgeMeasure_axis_supported {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (e : Step d) (H : ℕ) :
    ∀ᵐ a ∂rawBridgeMeasure μ (axisDirection e) H, AxisBridgeWord e H a := by
  rw [rawBridgeMeasure,ae_map_iff (measurable_recordWord _ _).aemeasurable
    (Set.to_countable _).measurableSet]
  filter_upwards [ae_restrict_of_ae (ae_start_and_nearestNeighbour μ 0),
    ae_restrict_mem (measurableSet_reachRecord (axisDirection e) H)] with X hX hH
  exact axisBridgeWord_recordWord e H X hX.1 hX.2 hH

lemma AxisBridgeWord.firstHit {d : ℕ} {e : Step d} {H : ℕ} {a : Word d}
    (ha : AxisBridgeWord e H a) : firstHitWord (axisUpper e H) a := by
  exact ⟨ha.1.ge,fun i hi => not_le_of_gt (ha.2 i hi).2⟩

lemma firstContactPairs_of_bridge_contact {d : ℕ} (e : Step d) (z : Site d)
    (n N H J : ℕ) (hH : H ≤ N) (hJ : J ≤ N) (hn : n+J ≤ N) (hn' : n+H ≤ N)
    (hz : axisHeight e z = (N : ℤ)-1) (a b : Word d)
    (ha : AxisBridgeWord e H a) (hb : AxisBridgeWord (oppositeStep e) J b)
    (hc : ∃ i < a.1, ∃ j < b.1, wordPath a i = wordPath b j + z)
    (X Y : Path d) (hX : X ∈ wordCylinder a) (hY : Y ∈ wordCylinder (translateWord z b)) :
    (X,Y) ∈ ⋃ p : firstContactPairs (axisUpper e H) (axisUpper e n)
      (axisLower e ((N : ℤ)-n)) (axisLower e 0 ∪ axisUpper e N), wordPairCylinder p.val := by
  classical
  have hex : ∃ j, Y j ∈ wordDepartures a := by
    obtain ⟨i,hi,j,hj,hij⟩ := hc
    refine ⟨j,i,hi,?_⟩
    rw [hY j hj.le,wordPath_translate z b j hj.le,hij]
  let j := Nat.find hex
  have hj : Y j ∈ wordDepartures a := Nat.find_spec hex
  have hjb : j < b.1 := by
    obtain ⟨i,hi,k,hk,hik⟩ := hc
    have hYk : Y k ∈ wordDepartures a := ⟨i,hi,by rw [hY k hk.le,wordPath_translate z b k hk.le,hik]⟩
    exact (Nat.find_min' hex hYk).trans_lt hk
  have hjmin : ∀ k < j, Y k ∉ wordDepartures a := fun k hk => Nat.find_min hex hk
  let c := prefixWord j Y
  have hcend : wordEnd c = Y j := wordPath_prefixWord j Y le_rfl
  have hcf : firstHitWord (wordDepartures a) c := by
    refine ⟨?_,fun k hk => ?_⟩
    · rw [hcend]; exact hj
    · rw [wordPath_prefixWord j Y hk.le]
      exact hjmin k hk
  have hYband : ∀ k ≤ j, (N : ℤ)-J ≤ axisHeight e (Y k) ∧ axisHeight e (Y k) < N := by
    intro k hk
    have hb' := hb.2 k (hk.trans_lt hjb)
    rw [axisHeight_opposite] at hb'
    rw [hY k (hk.trans hjb.le),wordPath_translate z b k (hk.trans hjb.le),axisHeight_add,hz]
    omega
  obtain ⟨i,hi,hij⟩ := hj
  have hR : wordPath a i ∈ axisUpper e n := by
    have hband := (hYband j le_rfl).1
    change (n : ℤ) ≤ _
    rw [hij]
    omega
  have hS : wordEnd c ∈ axisLower e ((N : ℤ)-n) := by
    rw [hcend,← hij]
    have hu := (ha.2 i hi).2
    change axisHeight e (wordPath a i) < (N : ℤ)-n
    omega
  have hp : (a,c) ∈ firstContactPairs (axisUpper e H) (axisUpper e n)
      (axisLower e ((N : ℤ)-n)) (axisLower e 0 ∪ axisUpper e N) := by
    refine ⟨ha.firstHit,hcf,⟨i,hi,hij.trans hcend.symm,⟨i,le_rfl,hR⟩,?_⟩,
      ⟨j,le_rfl,hS⟩,?_⟩
    · intro k hk hK
      have hb := ha.2 k (hk.trans_lt hi)
      rcases hK with hK | hK
      · change axisHeight e (wordPath a k) < 0 at hK; omega
      · change (N : ℤ) ≤ axisHeight e (wordPath a k) at hK; omega
    · intro k hk hK
      rw [wordPath_prefixWord j Y hk] at hK
      have hb := hYband k hk
      rcases hK with hK | hK
      · change axisHeight e (Y k) < 0 at hK; omega
      · change (N : ℤ) ≤ axisHeight e (Y k) at hK; omega
  refine Set.mem_iUnion.mpr ⟨⟨(a,c),hp⟩,hX,?_⟩
  rw [wordCylinder_prefixWord]
  exact fun _ _ => rfl

def bridgeWordContact {d : ℕ} (z : Site d) : Set (Word d × Word d) :=
  {p | ∃ i < p.1.1, ∃ j < p.2.1, wordPath p.1 i = wordPath p.2 j + z}

lemma translate_wordCylinder {d : ℕ} (z : Site d) (a : Word d) (X : Path d)
    (hX : X ∈ wordCylinder a) : shiftPath z X ∈ wordCylinder (translateWord z a) := by
  intro i hi
  change X i + z = _
  rw [wordPath_translate z a i hi,hX i hi]

lemma rawBridgeMeasure_contact_le {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d) (z : Site d) (n N H J : ℕ)
    (hH : H ≤ N) (hJ : J ≤ N) (hn : n+J ≤ N) (hn' : n+H ≤ N)
    (hz : axisHeight e z = (N : ℤ)-1) :
    ((rawBridgeMeasure μ (axisDirection e) H).prod
      (rawBridgeMeasure μ (axisDirection (oppositeStep e)) J)) (bridgeWordContact z) ≤
      2*((axisReachProb μ e n-axisReachProb μ e N) +
        (axisReachProb μ (oppositeStep e) n-axisReachProb μ (oppositeStep e) N)) := by
  let A := ⋃ p : firstContactPairs (axisUpper e H) (axisUpper e n)
    (axisLower e ((N : ℤ)-n)) (axisLower e 0 ∪ axisUpper e N), wordPairCylinder p.val
  have hA : MeasurableSet A := MeasurableSet.iUnion (fun p => measurableSet_wordPairCylinder p.val)
  have hs : ((annealed μ 0).prod (annealed μ 0)).map (Prod.map id (shiftPath z)) =
      (annealed μ 0).prod (annealed μ z) := by
    rw [← Measure.map_prod_map _ _ measurable_id (measurable_shiftPath z),Measure.map_id]
    have hh := annealed_shift μ 0 z
    rw [zero_add] at hh
    rw [hh]
  have hp : ((rawBridgeMeasure μ (axisDirection e) H).prod
      (rawBridgeMeasure μ (axisDirection (oppositeStep e)) J)) (bridgeWordContact z) ≤
      ((annealed μ 0).prod (annealed μ z)) A := by
    rw [rawBridgeMeasure,rawBridgeMeasure,Measure.map_prod_map _ _ (measurable_recordWord _ _)
      (measurable_recordWord _ _),Measure.map_apply
      ((measurable_recordWord _ _).prodMap (measurable_recordWord _ _)) (Set.to_countable _).measurableSet,
      Measure.prod_restrict,Measure.restrict_apply
      (((measurable_recordWord _ _).prodMap (measurable_recordWord _ _)) (Set.to_countable _).measurableSet),
      ← hs,Measure.map_apply (measurable_id.prodMap (measurable_shiftPath z)) hA]
    apply measure_mono_ae
    have hgood : ∀ᵐ p ∂(annealed μ 0).prod (annealed μ 0),
        (p.1 0 = 0 ∧ nearestNeighbour p.1) ∧ (p.2 0 = 0 ∧ nearestNeighbour p.2) :=
      (Measure.quasiMeasurePreserving_fst.ae (ae_start_and_nearestNeighbour μ 0)).and
        (Measure.quasiMeasurePreserving_snd.ae (ae_start_and_nearestNeighbour μ 0))
    filter_upwards [hgood] with p hp
    rintro ⟨hc,hpH,hpJ⟩
    have h1 := axisBridgeWord_recordWord e H p.1 hp.1.1 hp.1.2 hpH
    have h2 := axisBridgeWord_recordWord (oppositeStep e) J p.2 hp.2.1 hp.2.2 hpJ
    have hC1 := ((recordWord_atom (axisDirection e) H p.1 _).mp ⟨hpH,rfl⟩).2
    have hC2 := ((recordWord_atom (axisDirection (oppositeStep e)) J p.2 _).mp ⟨hpJ,rfl⟩).2
    exact firstContactPairs_of_bridge_contact e z n N H J hH hJ hn hn' hz _ _ h1 h2 hc _ _
      hC1 (translate_wordCylinder z _ _ hC2)
  exact hp.trans (firstContactPairs_axis_bound μ hell e z (axisUpper e H) (by omega) hz)

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

def appendTapeList {α : Type*} (a b : TapeList α) : TapeList α :=
  ⟨a.1+b.1,Fin.append a.2 b.2⟩

lemma listHeight_append {α : Type*} (L : α → ℕ) (a b : TapeList α) :
    listHeight L (appendTapeList a b) = listHeight L a + listHeight L b := by
  change (∑ i : Fin (a.1+b.1), L (Fin.append a.2 b.2 i)) = _
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left,Fin.append_right]
  rfl

lemma listProduct_append {α M : Type*} [CommMonoid M] (f : α → M) (a b : TapeList α) :
    (∏ i : Fin (appendTapeList a b).1, f ((appendTapeList a b).2 i)) =
      (∏ i : Fin a.1, f (a.2 i)) * ∏ i : Fin b.1, f (b.2 i) := by
  change (∏ i : Fin (a.1+b.1), f (Fin.append a.2 b.2 i)) = _
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left,Fin.append_right]

lemma tapeCylinder_append {α : Type*} (a b : TapeList α) (Z : ℕ → α) :
    Z ∈ tapeCylinder (appendTapeList a b) ↔
      Z ∈ tapeCylinder a ∧ (fun j => Z (a.1+j)) ∈ tapeCylinder b := by
  constructor
  · intro h
    refine ⟨fun i => ?_,fun i => ?_⟩
    · simpa [appendTapeList] using h (i.castAdd b.1)
    · simpa [appendTapeList] using h (i.natAdd a.1)
  · rintro ⟨ha,hb⟩ i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa [appendTapeList] using ha j
    · simpa [appendTapeList] using hb j

lemma appendTapeList_cut_recover {α : Type*} (L : α → ℕ) (H J : ℕ)
    (Z : ℕ → α) (hZ : ∀ i, 0 < L (Z i)) (a b : TapeList α)
    (ha : listHeight L a = H) (hb : listHeight L b = J)
    (h : Z ∈ tapeCylinder (appendTapeList a b)) :
    cutList L H Z = a ∧ cutList L J (fun j => Z (a.1+j)) = b := by
  have hh := (tapeCylinder_append a b Z).mp h
  exact ⟨((cutList_atom_iff L H Z hZ a).mpr ⟨ha,hh.1⟩).2,
    ((cutList_atom_iff L J _ (fun i => hZ _) b).mpr ⟨hb,hh.2⟩).2⟩

lemma bridgeList_pair_atom {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Measure α) [IsProbabilityMeasure ν]
    (L : α → ℕ) (hL : ∀ᵐ a ∂ν, 0 < L a) (H J : ℕ) (a b : TapeList α) :
    ((bridgeListMeasure ν L H).prod (bridgeListMeasure ν L J)) {(a,b)} =
      if listHeight L a = H ∧ listHeight L b = J then
        Measure.infinitePi (fun _ : ℕ => ν) (tapeCylinder (appendTapeList a b)) else 0 := by
  classical
  have ht : ({(a,b)} : Set (TapeList α × TapeList α)) = {a} ×ˢ {b} := by ext p; simp
  rw [ht,Measure.prod_prod,bridgeListMeasure_atom ν L hL,bridgeListMeasure_atom ν L hL,
    tapeCylinder_mass,listProduct_append (fun x => ν {x}) a b]
  split_ifs <;> simp_all

lemma measure_le_of_singleton_le {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (P Q : Measure α) (h : ∀ a, P {a} ≤ Q {a}) : P ≤ Q := by
  classical
  apply Measure.le_iff.mpr
  intro s hs
  rw [← Measure.tsum_indicator_apply_singleton P s hs,← Measure.tsum_indicator_apply_singleton Q s hs]
  apply ENNReal.tsum_le_tsum
  intro a
  by_cases ha : a ∈ s <;> simp only [Set.indicator_apply,ha,ite_true,ite_false]
  · exact h a
  · exact le_rfl

lemma bridgeListMeasure_append_le {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Measure α) [IsProbabilityMeasure ν]
    (L : α → ℕ) (hL : ∀ᵐ a ∂ν, 0 < L a) (H J : ℕ) :
    (((bridgeListMeasure ν L H).prod (bridgeListMeasure ν L J)).map
      (fun p => appendTapeList p.1 p.2)) ≤ bridgeListMeasure ν L (H+J) := by
  classical
  apply measure_le_of_singleton_le
  intro c
  let P := (bridgeListMeasure ν L H).prod (bridgeListMeasure ν L J)
  let f : TapeList α × TapeList α → ℝ≥0∞ := fun p =>
    if appendTapeList p.1 p.2 = c then P {p} else 0
  have he : (P.map (fun p => appendTapeList p.1 p.2)) {c} = ∑' p, f p := by
    rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
      ← Measure.tsum_indicator_apply_singleton P _ ((measurable_of_countable _) (measurableSet_singleton _))]
    apply tsum_congr
    intro p
    simp only [Set.indicator_apply,Set.mem_preimage,Set.mem_singleton_iff]
    rfl
  change (P.map (fun p => appendTapeList p.1 p.2)) {c} ≤ _
  rw [he]
  by_cases hf : ∃ p, f p ≠ 0
  · obtain ⟨p,hp⟩ := hf
    have hac : appendTapeList p.1 p.2 = c := by
      by_contra h
      exact hp (by simp [f,h])
    have hab : listHeight L p.1 = H ∧ listHeight L p.2 = J := by
      by_contra h
      exact hp (by simp [f,hac,P,bridgeList_pair_atom ν L hL,h])
    have hpc : P {p} = Measure.infinitePi (fun _ : ℕ => ν) (tapeCylinder c) := by
      dsimp only [P]
      rw [bridgeList_pair_atom ν L hL,ite_eq_left hab,hac]
    have hpos : Measure.infinitePi (fun _ : ℕ => ν) (tapeCylinder c) ≠ 0 := by
      simpa only [f,ite_eq_left hac,hpc] using hp
    obtain ⟨Z,hZc,hZ⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos
      (ae_restrict_of_ae (ae_tape_prop ν (fun a => 0 < L a)
        (measurableSet_lt measurable_const (measurable_of_countable L)) hL))
    have hpR := appendTapeList_cut_recover L H J Z hZ p.1 p.2 hab.1 hab.2 (hac.symm ▸ hZc)
    have hzero : ∀ q ≠ p, f q = 0 := by
      intro q hqp
      by_contra hq
      have hqc : appendTapeList q.1 q.2 = c := by
        by_contra h
        exact hq (by simp [f,h])
      have hqH : listHeight L q.1 = H ∧ listHeight L q.2 = J := by
        by_contra h
        exact hq (by simp [f,hqc,P,bridgeList_pair_atom ν L hL,h])
      have hqR := appendTapeList_cut_recover L H J Z hZ q.1 q.2 hqH.1 hqH.2 (hqc.symm ▸ hZc)
      have h1 : q.1 = p.1 := hqR.1.symm.trans hpR.1
      have h2 : q.2 = p.2 := by rw [h1] at hqR; exact hqR.2.symm.trans hpR.2
      exact hqp (Prod.ext h1 h2)
    rw [tsum_eq_single p hzero]
    have hc : listHeight L c = H+J := by rw [← hac,listHeight_append,hab.1,hab.2]
    rw [bridgeListMeasure_atom ν L hL,ite_eq_left hc]
    rw [show f p = P {p} by simp [f,hac],hpc,tapeCylinder_mass]
  · push Not at hf
    simp only [hf,tsum_zero,zero_le]

lemma bridgeListLaw_append_le {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Measure α) [IsProbabilityMeasure ν]
    (L : α → ℕ) (hL : ∀ᵐ a ∂ν, 0 < L a) (H J : ℕ) :
    (((bridgeListLaw ν L H).prod (bridgeListLaw ν L J)).map
      (fun p => appendTapeList p.1 p.2)) ≤
      ((Measure.infinitePi (fun _ : ℕ => ν) (renewalCut L H))⁻¹ *
       (Measure.infinitePi (fun _ : ℕ => ν) (renewalCut L J))⁻¹) •
        bridgeListMeasure ν L (H+J) := by
  let : IsFiniteMeasure (bridgeListMeasure ν L H) := by unfold bridgeListMeasure; infer_instance
  let : IsFiniteMeasure (bridgeListMeasure ν L J) := by unfold bridgeListMeasure; infer_instance
  rw [bridgeListLaw,bridgeListLaw,Measure.prod_smul_left,Measure.prod_smul_right,
    smul_smul,Measure.map_smul]
  apply Measure.le_iff.mpr
  intro s hs
  simp only [Measure.smul_apply,smul_eq_mul]
  simpa only [mul_comm] using
    mul_le_mul_left ((Measure.le_iff.mp (bridgeListMeasure_append_le ν L hL H J)) s hs)
      ((Measure.infinitePi (fun _ : ℕ => ν) (renewalCut L H))⁻¹ *
       (Measure.infinitePi (fun _ : ℕ => ν) (renewalCut L J))⁻¹)

lemma bridgeListLaw_join_raw_le {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) (H J : ℕ) :
    letI := slabLaw_probability μ v hp
    (((bridgeListLaw (slabLaw μ v) (slabRecords v) H).prod
      (bridgeListLaw (slabLaw μ v) (slabRecords v) J)).map
      (fun p => concatenateList (appendTapeList p.1 p.2))) ≤
      ((Measure.infinitePi (fun _ : ℕ => slabLaw μ v) (renewalCut (slabRecords v) H))⁻¹ *
       (Measure.infinitePi (fun _ : ℕ => slabLaw μ v) (renewalCut (slabRecords v) J))⁻¹) •
        rawBridgeMeasure μ v (H+J) := by
  let := slabLaw_probability μ v hp
  have hL : ∀ᵐ a ∂slabLaw μ v, 0 < slabRecords v a := by
    filter_upwards [ae_slabLaw_regeneration μ hell v hv hp] with a ha
    exact slabRecords_pos v a ha
  have h := Measure.map_mono (bridgeListLaw_append_le (slabLaw μ v) (slabRecords v) hL H J)
    (measurable_of_countable concatenateList)
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
    Measure.map_smul,
    bridgeListMeasure_concatenate μ hell v hv hp] at h
  exact h

lemma product_contact_domination {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d) (z : Site d) (n N H J : ℕ)
    (hH : H ≤ N) (hJ : J ≤ N) (hn : n+J ≤ N) (hn' : n+H ≤ N)
    (hz : axisHeight e z = (N : ℤ)-1)
    (P Q : Measure (Word d)) (a b : ℝ≥0∞) (hb : b ≠ ∞)
    (hP : P ≤ a • rawBridgeMeasure μ (axisDirection e) H)
    (hQ : Q ≤ b • rawBridgeMeasure μ (axisDirection (oppositeStep e)) J) :
    P.prod Q (bridgeWordContact z) ≤ a*b *
      (2*((axisReachProb μ e n-axisReachProb μ e N) +
        (axisReachProb μ (oppositeStep e) n-axisReachProb μ (oppositeStep e) N))) := by
  let : IsFiniteMeasure (rawBridgeMeasure μ (axisDirection e) H) := by
    unfold rawBridgeMeasure; infer_instance
  let : IsFiniteMeasure (rawBridgeMeasure μ (axisDirection (oppositeStep e)) J) := by
    unfold rawBridgeMeasure; infer_instance
  have : Fact (b < ∞) := ⟨hb.lt_top⟩
  have hh := Measure.le_iff.mp (Measure.prod_mono hP hQ) (bridgeWordContact z)
    (Set.to_countable _).measurableSet
  rw [Measure.prod_smul_left,Measure.prod_smul_right,smul_smul,Measure.smul_apply,smul_eq_mul] at hh
  refine hh.trans ?_
  simpa only [mul_comm] using mul_le_mul_left
    (rawBridgeMeasure_contact_le μ hell e z n N H J hH hJ hn hn' hz) (a*b)

lemma bridgeListLaw_reverse_pair {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Measure α) [IsProbabilityMeasure ν]
    (L : α → ℕ) (hL : ∀ᵐ a ∂ν, 0 < L a) (H J : ℕ) :
    ((bridgeListLaw ν L H).prod (bridgeListLaw ν L J)).map
      (Prod.map reverseTapeList reverseTapeList) =
        (bridgeListLaw ν L H).prod (bridgeListLaw ν L J) := by
  rw [← Measure.map_prod_map _ _ (measurable_of_countable _) (measurable_of_countable _),
    bridgeListLaw_reverse ν L hL,bridgeListLaw_reverse ν L hL]

lemma bridgeListLaw_join_reversed_raw_le {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) (H J : ℕ) :
    letI := slabLaw_probability μ v hp
    (((bridgeListLaw (slabLaw μ v) (slabRecords v) H).prod
      (bridgeListLaw (slabLaw μ v) (slabRecords v) J)).map
      (fun p => concatenateList (appendTapeList (reverseTapeList p.1) (reverseTapeList p.2)))) ≤
      ((Measure.infinitePi (fun _ : ℕ => slabLaw μ v) (renewalCut (slabRecords v) H))⁻¹ *
       (Measure.infinitePi (fun _ : ℕ => slabLaw μ v) (renewalCut (slabRecords v) J))⁻¹) •
        rawBridgeMeasure μ v (H+J) := by
  let := slabLaw_probability μ v hp
  have hL : ∀ᵐ a ∂slabLaw μ v, 0 < slabRecords v a := by
    filter_upwards [ae_slabLaw_regeneration μ hell v hv hp] with a ha
    exact slabRecords_pos v a ha
  have he := congrArg (fun M : Measure (TapeList (Word d) × TapeList (Word d)) =>
    M.map (fun p => concatenateList (appendTapeList p.1 p.2)))
    (bridgeListLaw_reverse_pair (slabLaw μ v) (slabRecords v) hL H J)
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)] at he
  exact he.le.trans (bridgeListLaw_join_raw_le μ hell v hv hp H J)

lemma signedThreeKernel_proj12 {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Measure α) [IsProbabilityMeasure ν]
    (L : α → ℕ) (hu : ∀ H, Measure.infinitePi (fun _ : ℕ => ν) (renewalCut L H) ≠ 0)
    (H : ℕ × (ℕ × ℕ)) :
    (signedThreeKernel ν L H).map (fun a => (a.1,a.2.1)) =
      (bridgeListLaw ν L H.1).prod (bridgeListLaw ν L H.2.1) := by
  let : ∀ h, IsProbabilityMeasure (bridgeListLaw ν L h) := fun h => bridgeListLaw_probability ν L h (hu h)
  let : IsMarkovKernel (oneBridgeKernel ν L) := ⟨fun h => bridgeListLaw_probability ν L h (hu h)⟩
  simp only [signedThreeKernel,Kernel.parallelComp_apply]
  change _ = (bridgeListLaw ν L H.1).prod (bridgeListLaw ν L H.2.1)
  change ((bridgeListLaw ν L H.1).prod
    ((bridgeListLaw ν L H.2.1).prod (bridgeListLaw ν L H.2.2))).map (Prod.map id Prod.fst) = _
  rw [← Measure.map_prod_map _ _ measurable_id measurable_fst,Measure.map_id,
    Measure.map_fst_prod,measure_univ,one_smul]

lemma signedThreeKernel_proj32 {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Measure α) [IsProbabilityMeasure ν]
    (L : α → ℕ) (hu : ∀ H, Measure.infinitePi (fun _ : ℕ => ν) (renewalCut L H) ≠ 0)
    (H : ℕ × (ℕ × ℕ)) :
    (signedThreeKernel ν L H).map (fun a => (a.2.2,a.2.1)) =
      (bridgeListLaw ν L H.2.2).prod (bridgeListLaw ν L H.2.1) := by
  let : ∀ h, IsProbabilityMeasure (bridgeListLaw ν L h) := fun h => bridgeListLaw_probability ν L h (hu h)
  let : IsMarkovKernel (oneBridgeKernel ν L) := ⟨fun h => bridgeListLaw_probability ν L h (hu h)⟩
  simp only [signedThreeKernel,Kernel.parallelComp_apply]
  change ((bridgeListLaw ν L H.1).prod
    ((bridgeListLaw ν L H.2.1).prod (bridgeListLaw ν L H.2.2))).map (Prod.swap ∘ Prod.snd) = _
  rw [← Measure.map_map measurable_swap measurable_snd,Measure.map_snd_prod,
    measure_univ,one_smul,Measure.prod_swap]

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

noncomputable def positiveJoin {d : ℕ} (a : ThreeLists (Word d)) : Word d :=
  concatenateList (appendTapeList (reverseTapeList a.2.2) (reverseTapeList a.2.1))
noncomputable def negativeJoin {d : ℕ} (a : ThreeLists (Word d)) : Word d :=
  concatenateList (appendTapeList a.1 a.2.1)

def middleContact {d : ℕ} (z : Site d) : Set (ThreeLists (Word d) × ThreeLists (Word d)) :=
  (Prod.map positiveJoin negativeJoin) ⁻¹' bridgeWordContact z

lemma signedThreeKernel_join_le {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) (H : ℕ × (ℕ × ℕ)) :
    letI := slabLaw_probability μ v hp
    let U := fun h => Measure.infinitePi (fun _ : ℕ => slabLaw μ v) (renewalCut (slabRecords v) h)
    ((signedThreeKernel (slabLaw μ v) (slabRecords v) H).map positiveJoin ≤
      ((U H.2.2)⁻¹*(U H.2.1)⁻¹) • rawBridgeMeasure μ v (H.2.2+H.2.1)) ∧
    ((signedThreeKernel (slabLaw μ v) (slabRecords v) H).map negativeJoin ≤
      ((U H.1)⁻¹*(U H.2.1)⁻¹) • rawBridgeMeasure μ v (H.1+H.2.1)) := by
  let := slabLaw_probability μ v hp
  have hu (h : ℕ) : Measure.infinitePi (fun _ : ℕ => slabLaw μ v) (renewalCut (slabRecords v) h) ≠ 0 := by
    change Measure.infinitePi (fun _ : ℕ => slabLaw μ v) (tapeCut v h) ≠ 0
    rw [tapeCut_mass μ hell v hv hp]
    exact ne_of_gt (hp.trans_le (reachRecord_mass_ge μ hell v hv h))
  dsimp only
  constructor
  · have hh := congrArg (fun M : Measure (TapeList (Word d) × TapeList (Word d)) =>
      M.map (fun p => concatenateList (appendTapeList (reverseTapeList p.1) (reverseTapeList p.2))))
      (signedThreeKernel_proj32 (slabLaw μ v) (slabRecords v) hu H)
    rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)] at hh
    exact hh.le.trans (bridgeListLaw_join_reversed_raw_le μ hell v hv hp H.2.2 H.2.1)
  · have hh := congrArg (fun M : Measure (TapeList (Word d) × TapeList (Word d)) =>
      M.map (fun p => concatenateList (appendTapeList p.1 p.2)))
      (signedThreeKernel_proj12 (slabLaw μ v) (slabRecords v) hu H)
    rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)] at hh
    exact hh.le.trans (bridgeListLaw_join_raw_le μ hell v hv hp H.1 H.2.1)

lemma four_bridge_contact_le {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : 0 < annealed μ 0 (nonBacktracking (axisDirection e)))
    (hm : 0 < annealed μ 0 (nonBacktracking (axisDirection (oppositeStep e))))
    (H : ℕ × (ℕ × ℕ)) (z : Site d) (n : ℕ)
    (h1 : n ≤ H.1) (h3 : n ≤ H.2.2)
    (hz : axisHeight e z = ((H.1+H.2.1+H.2.2 : ℕ) : ℤ)-1) :
    letI := slabLaw_probability μ (axisDirection e) hp
    letI := slabLaw_probability μ (axisDirection (oppositeStep e)) hm
    ((signedThreeKernel (slabLaw μ (axisDirection e)) (slabRecords (axisDirection e)) H).prod
      (signedThreeKernel (slabLaw μ (axisDirection (oppositeStep e)))
        (slabRecords (axisDirection (oppositeStep e))) H)) (middleContact z) ≤
      ((annealed μ 0 (nonBacktracking (axisDirection e)))⁻¹)^2 *
      ((annealed μ 0 (nonBacktracking (axisDirection (oppositeStep e))))⁻¹)^2 *
      (2*((axisReachProb μ e n-axisReachProb μ e (H.1+H.2.1+H.2.2)) +
        (axisReachProb μ (oppositeStep e) n-axisReachProb μ (oppositeStep e) (H.1+H.2.1+H.2.2)))) := by
  let := slabLaw_probability μ (axisDirection e) hp
  let := slabLaw_probability μ (axisDirection (oppositeStep e)) hm
  have hU (f : Step d) (hf : 0 < annealed μ 0 (nonBacktracking (axisDirection f))) (h : ℕ) :
      letI := slabLaw_probability μ (axisDirection f) hf
      Measure.infinitePi (fun _ : ℕ => slabLaw μ (axisDirection f))
        (renewalCut (slabRecords (axisDirection f)) h) = axisReachProb μ f h :=
    axis_tapeCut_mass μ hell f hf h
  have hA := (signedThreeKernel_join_le μ hell (axisDirection e) (axisDirection_ne_zero e) hp H).1
  have hB := (signedThreeKernel_join_le μ hell (axisDirection (oppositeStep e))
    (axisDirection_ne_zero (oppositeStep e)) hm H).2
  simp only [hU e hp] at hA
  simp only [hU (oppositeStep e) hm] at hB
  have hpos (f : Step d) (hf : 0 < annealed μ 0 (nonBacktracking (axisDirection f))) (h : ℕ) :
      axisReachProb μ f h ≠ 0 := ne_of_gt (hf.trans_le (axisReachProb_lower μ hell f h))
  have hb : (axisReachProb μ (oppositeStep e) H.1)⁻¹ * (axisReachProb μ (oppositeStep e) H.2.1)⁻¹ ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (hpos _ hm _)) (ENNReal.inv_ne_top.mpr (hpos _ hm _))
  have hh := product_contact_domination μ hell e z n (H.1+H.2.1+H.2.2) (H.2.2+H.2.1) (H.1+H.2.1)
    (by omega) (by omega) (by omega) (by omega) hz _ _ _ _ hb hA hB
  rw [Measure.map_prod_map _ _ (measurable_of_countable _) (measurable_of_countable _),
    Measure.map_apply ((measurable_of_countable positiveJoin).prodMap (measurable_of_countable negativeJoin))
      (Set.to_countable _).measurableSet] at hh
  refine hh.trans ?_
  calc
    _ ≤ (((annealed μ 0 (nonBacktracking (axisDirection e)))⁻¹)*
        ((annealed μ 0 (nonBacktracking (axisDirection e)))⁻¹)) *
      (((annealed μ 0 (nonBacktracking (axisDirection (oppositeStep e))))⁻¹)*
        ((annealed μ 0 (nonBacktracking (axisDirection (oppositeStep e))))⁻¹)) * _ := by
          gcongr <;> exact axisReachProb_lower μ hell _ _
    _ = _ := by simp only [pow_two]

lemma shiftPath_preimage_wordCylinder {d : ℕ} (z : Site d) (a : Word d) :
    shiftPath (-z) ⁻¹' wordCylinder a = wordCylinder (translateWord z a) := by
  ext X
  constructor
  · intro h i hi
    rw [wordPath_translate z a i hi]
    have hh := h i hi
    dsimp only [shiftPath] at hh
    rw [← hh]
    abel
  · intro h i hi
    have hh := h i hi
    rw [wordPath_translate z a i hi] at hh
    change X i + -z = wordPath a i
    rw [hh]
    abel

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

noncomputable def relativeContinuationLaw {d : ℕ} (P : Measure (Path d)) (a : Word d) : Measure (Path d) :=
  (continuationLaw P a).map (shiftPath (-wordEnd a))

lemma relativeContinuationLaw_probability {d : ℕ} (P : Measure (Path d)) [IsProbabilityMeasure P]
    (a : Word d) (ha : P (wordCylinder a) ≠ 0) : IsProbabilityMeasure (relativeContinuationLaw P a) := by
  let := continuationLaw_probability P a ha
  exact probabilityMeasure_map (measurable_shiftPath _).aemeasurable

lemma relativeContinuation_fresh_stopped {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d) (a : Word d) (ha : annealed μ 0 (wordCylinder a) ≠ 0)
    (hdep : ∀ i < a.1, axisHeight e (wordPath a i) < axisHeight e (wordEnd a)) (N : ℕ) :
    (relativeContinuationLaw (annealed μ 0) a).map (firstVisitWord (axisLower e 0 ∪ axisUpper e N)) =
      (annealed μ 0).map (firstVisitWord (axisLower e 0 ∪ axisUpper e N)) := by
  let := relativeContinuationLaw_probability (annealed μ 0) a ha
  let K := axisLower e 0 ∪ axisUpper e N
  have hex : ∀ᵐ X ∂annealed μ 0, ∃ n, X n ∈ K := annealed_axis_exit μ hell e 0 0 N
  have he (b : Word d) (hb : firstHitWord K b) :
      relativeContinuationLaw (annealed μ 0) a (wordCylinder b) = annealed μ 0 (wordCylinder b) := by
    rw [relativeContinuationLaw,Measure.map_apply (measurable_shiftPath _) (show MeasurableSet (wordCylinder b) from measurableSet_pathCylinder _ _),
      shiftPath_preimage_wordCylinder,continuationLaw_fresh_cylinder μ 0 a _ ha]
    · have hs := congrArg (fun M : Measure (Path d) => M (wordCylinder b))
        (annealed_shift μ (wordEnd a) (-wordEnd a))
      rw [add_neg_cancel,Measure.map_apply (measurable_shiftPath _) (show MeasurableSet (wordCylinder b) from measurableSet_pathCylinder _ _),
        shiftPath_preimage_wordCylinder] at hs
      exact hs
    · apply Set.disjoint_left.mpr
      rintro y ⟨i,hi,rfl⟩ ⟨j,hj,heq⟩
      have hj' := hb.2 j hj
      have hnonneg : 0 ≤ axisHeight e (wordPath b j) := by
        by_contra h
        exact hj' (Or.inl (by exact lt_of_not_ge h))
      rw [wordPath_translate (wordEnd a) b j hj.le] at heq
      have ha' := hdep i hi
      have heq' := congrArg (axisHeight e) heq
      rw [axisHeight_add] at heq'
      omega
  exact firstVisitWord_map_eq _ _ K (firstHitWords_full_of_cylinder_eq _ _ K hex he) hex he

lemma posterior_old_prefix_contact_bound {d ι : ℕ} [NeZero ι]
    (μ : Measure (Row d)) [IsProbabilityMeasure μ] (hell : StrictEllipticity μ)
    (e : Step d) (a : Word d) (ha : annealed μ 0 (wordCylinder a) ≠ 0)
    (hdep : ∀ i < a.1, axisHeight e (wordPath a i) < axisHeight e (wordEnd a))
    (E : Fin ι → Set (Path d)) (hE : ∀ q, MeasurableSet (E q))
    (hdis : Pairwise (fun i j => Disjoint (E i) (E j)))
    (start : Fin ι → Site d) (r N m : ℕ) (hrN : r ≤ N)
    (hΔ : axisReachProb μ e r - axisReachProb μ e N ≤ ENNReal.ofReal ((1/2 : ℝ)^m)) :
    letI := relativeContinuationLaw_probability (annealed μ 0) a ha
    (∑ q, ∑' b : {b | upperContactWord 0 (axisUpper e r) (axisLower e 0 ∪ axisUpper e N) b},
      ENNReal.ofReal (wordPosterior (relativeContinuationLaw (annealed μ 0) a) E q b) *
        (annealed μ 0 (wordCylinder b) *
          annealed μ (start q) (avoids (axisUpper e N) ∩ contactAvoid b))) ≤
      ENNReal.ofReal ((24 / posteriorExponent)*Real.log (ι+1)*(m+1)^2*(1/2 : ℝ)^m) := by
  let := relativeContinuationLaw_probability (annealed μ 0) a ha
  exact posterior_contact_raw_bound μ hell (relativeContinuationLaw (annealed μ 0) a) E hE hdis e
    start r N m hrN (relativeContinuation_fresh_stopped μ hell e a ha hdep N) hΔ

lemma binary_cross_entropy_bound (P Q : Measure Bool) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPQ : P ≪ Q) :
    P.real {true} * (-Real.log (Q.real {true})) ≤
      (InformationTheory.klDiv P Q).toReal + Real.log 2 := by
  have hi : Integrable (fun x => Real.log (P.real {x}) - Real.log (Q.real {x})) P := Integrable.of_finite
  have hkl := atom_klDiv_formula P Q hPQ hi
  have hnonneg := atom_logRatio_nonneg P Q hPQ hi
  rw [hkl,ENNReal.toReal_ofReal hnonneg]
  have hs : (∫ x, Real.log (P.real {x}) - Real.log (Q.real {x}) ∂P) =
      (∫ x, atomInfo Q x ∂P) - discreteEntropy P := by
    rw [discreteEntropy,← integral_sub Integrable.of_finite Integrable.of_finite]
    congr 1
    funext x
    simp only [atomInfo]
    ring
  rw [hs]
  have hent := (entropy_finite Bool P).2
  simp only [Fintype.card_bool,Nat.cast_ofNat] at hent
  have hcross : P.real {true} * (-Real.log (Q.real {true})) ≤ ∫ x, atomInfo Q x ∂P := by
    rw [integral_fintype Integrable.of_finite]
    simp only [Fintype.sum_bool,smul_eq_mul,atomInfo]
    have hpos : 0 ≤ P.real {false} * (-Real.log (Q.real {false})) :=
      mul_nonneg measureReal_nonneg (atomInfo_nonneg Q false)
    linarith
  linarith

lemma kl_event_bound {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hfin : InformationTheory.klDiv P Q ≠ ∞)
    (E : Set Ω) (hE : MeasurableSet E) :
    P.real E * (-Real.log (Q.real E)) ≤ (InformationTheory.klDiv P Q).toReal + Real.log 2 := by
  classical
  let f : Ω → Bool := fun x => decide (x ∈ E)
  have hf : Measurable f := by
    intro s hs
    by_cases ht : true ∈ s <;> by_cases hf : false ∈ s
    · have he : f ⁻¹' s = Set.univ := by ext x;simp only [Set.mem_preimage,Set.mem_univ,iff_true];cases h : f x <;> simp_all
      rw [he];exact MeasurableSet.univ
    · have he : f ⁻¹' s = E := by ext x;simp only [Set.mem_preimage,f];by_cases hx : x ∈ E <;> simp_all
      rw [he];exact hE
    · have he : f ⁻¹' s = Eᶜ := by ext x;simp only [Set.mem_preimage,f,Set.mem_compl_iff];by_cases hx : x ∈ E <;> simp_all
      rw [he];exact hE.compl
    · have he : f ⁻¹' s = ∅ := by ext x;simp only [Set.mem_preimage,Set.mem_empty_iff_false,iff_false];cases h : f x <;> simp_all
      rw [he];exact MeasurableSet.empty
  let := probabilityMeasure_map hf.aemeasurable (μ := P)
  let := probabilityMeasure_map hf.aemeasurable (μ := Q)
  have hac := (InformationTheory.klDiv_ne_top_iff.mp hfin).1
  have hh := binary_cross_entropy_bound (P.map f) (Q.map f) (hac.map hf)
  have hmass (M : Measure Ω) : (M.map f).real {true} = M.real E := by
    rw [measureReal_def,Measure.map_apply hf (measurableSet_singleton _)]
    have he : f ⁻¹' {true} = E := by ext x;simp [f]
    rw [he]
    rfl
  rw [hmass P,hmass Q] at hh
  have hm := ENNReal.toReal_mono hfin (InformationTheory.klDiv_map_le P Q hf)
  linarith

lemma posterior_cylinder_mass {d ι : ℕ} (P : Measure (Path d)) [IsFiniteMeasure P]
    (E : Fin ι → Set (Path d)) (q : Fin ι) (b : Word d) :
    ENNReal.ofReal (wordPosterior P E q b) * P (wordCylinder b) = P (E q ∩ wordCylinder b) := by
  by_cases hb : P (wordCylinder b) = 0
  · have he : P (E q ∩ wordCylinder b) = 0 := measure_mono_null Set.inter_subset_right hb
    simp only [hb,mul_zero,he]
  · have hp : 0 < P.real (wordCylinder b) := ENNReal.toReal_pos hb (measure_ne_top _ _)
    rw [wordPosterior,ENNReal.ofReal_div_of_pos hp,measureReal_def,measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top _ _),ENNReal.ofReal_toReal (measure_ne_top _ _),
      ENNReal.div_mul_cancel hb (measure_ne_top _ _)]

lemma relativeContinuation_fresh_cylinder {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (e : Step d) (a b : Word d) (ha : annealed μ 0 (wordCylinder a) ≠ 0)
    (hdep : ∀ i < a.1, axisHeight e (wordPath a i) < axisHeight e (wordEnd a))
    (hb : ∀ j < b.1, 0 ≤ axisHeight e (wordPath b j)) :
    relativeContinuationLaw (annealed μ 0) a (wordCylinder b) = annealed μ 0 (wordCylinder b) := by
  rw [relativeContinuationLaw,Measure.map_apply (measurable_shiftPath _)
    (show MeasurableSet (wordCylinder b) from measurableSet_pathCylinder _ _),
    shiftPath_preimage_wordCylinder,continuationLaw_fresh_cylinder μ 0 a _ ha]
  · have hs := congrArg (fun M : Measure (Path d) => M (wordCylinder b))
      (annealed_shift μ (wordEnd a) (-wordEnd a))
    rw [add_neg_cancel,Measure.map_apply (measurable_shiftPath _)
      (show MeasurableSet (wordCylinder b) from measurableSet_pathCylinder _ _),
      shiftPath_preimage_wordCylinder] at hs
    exact hs
  · apply Set.disjoint_left.mpr
    rintro y ⟨i,hi,rfl⟩ ⟨j,hj,heq⟩
    rw [wordPath_translate (wordEnd a) b j hj.le] at heq
    have heq' := congrArg (axisHeight e) heq
    rw [axisHeight_add] at heq'
    have := hdep i hi
    have := hb j hj
    omega

lemma prefix_relative_completion_mass {d : ℕ} (P : Measure (Path d)) [IsProbabilityMeasure P]
    (a : Word d) (ha : P (wordCylinder a) ≠ 0) (E : Set (Path d)) (hE : MeasurableSet E) :
    P (wordCylinder a ∩ (shiftPath (-wordEnd a) ∘ tailPath a.1) ⁻¹' E) =
      P (wordCylinder a) * relativeContinuationLaw P a E := by
  rw [relativeContinuationLaw,Measure.map_apply (measurable_shiftPath _) hE,
    continuationLaw,Measure.map_apply (measurable_tailPath _) (hE.preimage (measurable_shiftPath _)),
    ProbabilityTheory.cond_apply (show MeasurableSet (wordCylinder a) from measurableSet_pathCylinder _ _) _ _]
  rw [← mul_assoc,ENNReal.mul_inv_cancel ha (measure_ne_top _ _),one_mul]
  rfl

lemma posterior_old_prefix_weighted_bound {d ι : ℕ} [NeZero ι]
    (μ : Measure (Row d)) [IsProbabilityMeasure μ] (hell : StrictEllipticity μ)
    (e : Step d) (a : Word d) (ha : annealed μ 0 (wordCylinder a) ≠ 0)
    (hdep : ∀ i < a.1, axisHeight e (wordPath a i) < axisHeight e (wordEnd a))
    (E : Fin ι → Set (Path d)) (hE : ∀ q, MeasurableSet (E q))
    (hdis : Pairwise (fun i j => Disjoint (E i) (E j)))
    (start : Fin ι → Site d) (r N m : ℕ) (hrN : r ≤ N)
    (hΔ : axisReachProb μ e r - axisReachProb μ e N ≤ ENNReal.ofReal ((1/2 : ℝ)^m)) :
    (∑ q, ∑' b : {b | upperContactWord 0 (axisUpper e r) (axisLower e 0 ∪ axisUpper e N) b},
      annealed μ 0 (wordCylinder a ∩ (shiftPath (-wordEnd a) ∘ tailPath a.1) ⁻¹' (E q ∩ wordCylinder b)) *
        annealed μ (start q) (avoids (axisUpper e N) ∩ contactAvoid b)) ≤
      annealed μ 0 (wordCylinder a) *
        ENNReal.ofReal ((24 / posteriorExponent)*Real.log (ι+1)*(m+1)^2*(1/2 : ℝ)^m) := by
  let P := relativeContinuationLaw (annealed μ 0) a
  let := relativeContinuationLaw_probability (annealed μ 0) a ha
  have hmass (q : Fin ι) (b : {b | upperContactWord 0 (axisUpper e r) (axisLower e 0 ∪ axisUpper e N) b}) :
      annealed μ 0 (wordCylinder a ∩ (shiftPath (-wordEnd a) ∘ tailPath a.1) ⁻¹' (E q ∩ wordCylinder b)) =
        annealed μ 0 (wordCylinder a) * (ENNReal.ofReal (wordPosterior P E q b) * annealed μ 0 (wordCylinder b)) := by
    rw [prefix_relative_completion_mass _ a ha _ ((hE q).inter (show MeasurableSet (wordCylinder (b : Word d)) from measurableSet_pathCylinder _ _)),
      ← posterior_cylinder_mass P E q b]
    rw [relativeContinuation_fresh_cylinder μ e a b ha hdep]
    intro j hj
    have hh := b.property.2.2 j hj.le
    exact le_of_not_gt (fun h => hh (Or.inl h))
  simp_rw [hmass,mul_assoc]
  simp_rw [ENNReal.tsum_mul_left]
  rw [← Finset.mul_sum]
  simpa only [mul_assoc] using mul_le_mul_right (posterior_old_prefix_contact_bound μ hell e a ha hdep E hE hdis start r N m hrN hΔ) (annealed μ 0 (wordCylinder a))

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

lemma property_of_atom {α : Type*} [MeasurableSpace α] (ν : Measure α)
    (P : α → Prop) (hP : ∀ᵐ a ∂ν, P a) (a : α) (ha : ν {a} ≠ 0) : P a := by
  by_contra h
  apply ha
  exact measure_mono_null (Set.singleton_subset_iff.mpr h) (ae_iff.mp hP)

lemma windowCommonLaw_support {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (P : Bool → α → Prop) (hP : ∀ b, ∀ᵐ a ∂ν b, P b a) (k n : ℕ) :
    ∀ᵐ a ∂windowCommonLaw ν L k n, InCountWindow L k n a ∧ ∀ b i, P b ((a b).2 i) := by
  classical
  filter_upwards [ae_atom_pos (windowCommonLaw ν L k n),windowCommonLaw_ae_window ν L hL he k n] with a ha hw
  rw [windowCommonLaw_atom ν L hL he,ite_eq_left hw] at ha
  have hp : twoListWeight ν a ≠ 0 := right_ne_zero_of_mul ha
  refine ⟨hw,fun b i => property_of_atom (ν b) (P b) (hP b) _ ?_⟩
  exact (Finset.prod_ne_zero_iff.mp (Finset.prod_ne_zero_iff.mp hp b (Finset.mem_univ b))) i (Finset.mem_univ i)

lemma listCommonCount_le_height {α : Type*} (L : Bool → α → ℕ) (a : TwoTapeList α) :
    listCommonCount L a ≤ chunkHeight L a := by
  classical
  unfold listCommonCount chunkHeight
  calc
    _ ≤ ∑ _j ∈ Finset.range (listHeight (L false) (a false)), 1 := by
      apply Finset.sum_le_sum
      intro j hj
      split_ifs <;> omega
    _ = _ := by simp

lemma experimentLaw_fourWindows {α G : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [AddCommGroup G] [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (D : Bool → α → G) (n : ℕ) :
    experimentLaw ν L D n = ((windowCommonLaw ν L n n).prod (threeChunkLaw ν L n)).map
      (fun p => ((threeHeight L p.2,pairTotal D p.1+signedTotal (D false) (splitThree p.2).1),splitThree p.2)) := by
  rw [experimentLaw,← windowCommonLaw_marked ν L hL he D n n,signedChunkLaw,
    Measure.map_prod_map _ _ (measurable_of_countable _) (measurable_of_countable _),
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  congr 1

lemma axisHeight_listTotal {d : ℕ} (e : Step d) (b : Bool) (a : TapeList (Word d))
    (ha : ∀ i, RegenerationWord (axisDirection (placedAxis e b)) (a.2 i)) :
    axisHeight e (listTotal wordEnd a) = if b then -(listHeight (placedWidth e b) a : ℤ)
      else (listHeight (placedWidth e b) a : ℤ) := by
  rw [listTotal,axisHeight_sum]
  cases b with
  | false =>
    simp only [Bool.false_eq_true,↓reduceIte,listHeight,Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact axisHeight_wordEnd e _ (ha i)
  | true =>
    simp only [↓reduceIte,listHeight,Nat.cast_sum,← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have h := axisHeight_wordEnd (oppositeStep e) _ (ha i)
    rw [axisHeight_opposite] at h
    exact neg_eq_iff_eq_neg.mp h

lemma axisHeight_pairTotal {d : ℕ} (e : Step d) (a : TwoTapeList (Word d))
    (hb : BalancedList (placedWidth e) a)
    (ha : ∀ b i, RegenerationWord (axisDirection (placedAxis e b)) ((a b).2 i)) :
    axisHeight e (pairTotal (fun _ => wordEnd) a) = 0 := by
  rw [pairTotal,axisHeight_add,axisHeight_listTotal e false _ (ha false),
    axisHeight_listTotal e true _ (ha true)]
  simp only [Bool.false_eq_true,↓reduceIte,hb true,add_neg_cancel]

lemma axisHeight_signedTotal {d : ℕ} (e : Step d) (a : ThreeChunk (Word d))
    (ha : ∀ i, RegenerationWord (axisDirection e) ((a.1 false).2 i))
    (hb : ∀ i, RegenerationWord (axisDirection e) ((a.2.1 false).2 i))
    (hc : ∀ i, RegenerationWord (axisDirection e) ((a.2.2 false).2 i)) :
    axisHeight e (signedTotal wordEnd (splitThree a).1) =
      ((threeHeight (placedWidth e) a).1+(threeHeight (placedWidth e) a).2.1+
        (threeHeight (placedWidth e) a).2.2 : ℕ) := by
  simp only [signedTotal,splitThree,axisHeight_add,axisHeight_listTotal e false _ ha,
    axisHeight_listTotal e false _ hb,axisHeight_listTotal e false _ hc,Bool.false_eq_true,↓reduceIte]
  simp only [threeHeight,chunkHeight,Nat.cast_add,add_assoc]

lemma experimentLaw_axis_support {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : ∀ b, 0 < annealed μ 0 (nonBacktracking (axisDirection (placedAxis e b))))
    (he : letI : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) :=
      fun b => slabLaw_probability μ _ (hp b)
      ∀ᵐ Z ∂twoTapeLaw (fun b => slabLaw μ (axisDirection (placedAxis e b))),
        ∃ H, 0 < H ∧ Z ∈ commonCut (placedWidth e) H)
    (n : ℕ) [NeZero n] :
    let : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) :=
      fun b => slabLaw_probability μ _ (hp b)
    ∀ᵐ x ∂experimentLaw (fun b => slabLaw μ (axisDirection (placedAxis e b))) (placedWidth e)
      (fun _ => wordEnd) n,
      n ≤ x.1.1.1 ∧ n ≤ x.1.1.2.2 ∧
        axisHeight e x.1.2 = ((x.1.1.1+x.1.1.2.1+x.1.1.2.2 : ℕ) : ℤ) := by
  dsimp only
  let : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) :=
      fun b => slabLaw_probability μ _ (hp b)
  have : Countable (Word d) := inferInstance
  have : Countable (TapeList (Word d)) := inferInstance
  have : Countable (TwoTapeList (Word d)) := inferInstance
  have : Countable (ThreeChunk (Word d)) := inferInstance
  have : Countable (ThreeLists (Word d)) := inferInstance
  let ν := fun b => slabLaw μ (axisDirection (placedAxis e b))
  have hs (b : Bool) : ∀ᵐ a ∂ν b, RegenerationWord (axisDirection (placedAxis e b)) a :=
    ae_slabLaw_regeneration μ hell _ (axisDirection_ne_zero (placedAxis e b)) (hp b)
  have hL (b : Bool) : ∀ᵐ a ∂ν b, 0 < placedWidth e b a := by
    filter_upwards [hs b] with a ha
    exact slabRecords_pos _ _ ha
  have hw (k : ℕ) := windowCommonLaw_support ν (placedWidth e) hL he _ hs k n
  rw [experimentLaw_fourWindows ν (placedWidth e) hL he,
    ae_map_iff (measurable_of_countable _).aemeasurable (Set.to_countable _).measurableSet]
  apply (Measure.ae_prod_iff_ae_ae (Set.to_countable _).measurableSet).mpr
  filter_upwards [hw n] with a ha
  change ∀ᵐ c ∂(windowCommonLaw ν (placedWidth e) n n).prod
    ((windowCommonLaw ν (placedWidth e) (7*n) n).prod (windowCommonLaw ν (placedWidth e) n n)), _
  apply (Measure.ae_prod_iff_ae_ae (Set.to_countable _).measurableSet).mpr
  filter_upwards [hw n] with b hb
  apply (Measure.ae_prod_iff_ae_ae (Set.to_countable _).measurableSet).mpr
  filter_upwards [hw (7*n)] with c hc
  filter_upwards [hw n] with f hf
  refine ⟨hb.1.2.1.trans (listCommonCount_le_height _ b),
    hf.1.2.1.trans (listCommonCount_le_height _ f),?_⟩
  rw [axisHeight_add,axisHeight_pairTotal e a ha.1.1 ha.2,zero_add]
  exact axisHeight_signedTotal e (b,c,f) (hb.2 false) (hc.2 false) (hf.2 false)

lemma experiment_height_moment {α G : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [AddCommGroup G] [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (hi : Integrable (fun Z => (firstCommonWidth L Z : ℝ)) (twoTapeLaw ν))
    (D : Bool → α → G) (n : ℕ) [NeZero n] :
    Integrable (fun x => ((x.1.1.1+x.1.1.2.1+x.1.1.2.2 : ℕ) : ℝ)) (experimentLaw ν L D n) ∧
      (∫ x, ((x.1.1.1+x.1.1.2.1+x.1.1.2.2 : ℕ) : ℝ) ∂experimentLaw ν L D n) ≤
        12*n*(∫ Z, (firstCommonWidth L Z : ℝ) ∂twoTapeLaw ν) := by
  have h0 := windowCommonLaw_height_integrable ν L hL he hi n n
  have h1 := windowCommonLaw_height_integrable ν L hL he hi (7*n) n
  have hv : Integrable (fun a : ThreeChunk α =>
      (chunkHeight L a.1 : ℝ)+(chunkHeight L a.2.1 : ℝ)+(chunkHeight L a.2.2 : ℝ))
      (threeChunkLaw ν L n) :=
    ((h0.comp_fst _).add ((h1.comp_fst _).comp_snd _)).add ((h0.comp_snd _).comp_snd _)
  rw [experimentLaw_fourWindows ν L hL he]
  constructor
  · rw [integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
      (measurable_of_countable _).aemeasurable]
    simpa only [Function.comp_def,threeHeight,Nat.cast_add] using hv.comp_snd (windowCommonLaw ν L n n)
  · rw [integral_map (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aestronglyMeasurable]
    simp only [threeHeight,Nat.cast_add]
    rw [integral_prod _ (hv.comp_snd _)]
    simp only [integral_const,probReal_univ,one_smul]
    have hs : (∫ a : ThreeChunk α, (chunkHeight L a.1 : ℝ)+(chunkHeight L a.2.1 : ℝ)+(chunkHeight L a.2.2 : ℝ) ∂threeChunkLaw ν L n) =
        (∫ a : ThreeChunk α, (chunkHeight L a.1 : ℝ) ∂threeChunkLaw ν L n) +
        (∫ a : ThreeChunk α, (chunkHeight L a.2.1 : ℝ) ∂threeChunkLaw ν L n) +
        (∫ a : ThreeChunk α, (chunkHeight L a.2.2 : ℝ) ∂threeChunkLaw ν L n) := by
      calc
        _ = (∫ a : ThreeChunk α, (chunkHeight L a.1 : ℝ)+(chunkHeight L a.2.1 : ℝ) ∂threeChunkLaw ν L n) + _ :=
          integral_add ((h0.comp_fst _).add ((h1.comp_fst _).comp_snd _)) ((h0.comp_snd _).comp_snd _)
        _ = _ := congrArg (fun t : ℝ => t+(∫ a : ThreeChunk α, (chunkHeight L a.2.2 : ℝ) ∂threeChunkLaw ν L n))
          (integral_add (h0.comp_fst _) ((h1.comp_fst _).comp_snd _))
    rw [hs]
    simp only [threeChunkLaw]
    rw [integral_prod _ (h0.comp_fst _),integral_prod _ ((h1.comp_fst _).comp_snd _),
      integral_prod _ ((h0.comp_snd _).comp_snd _)]
    simp only [integral_const,probReal_univ,one_smul]
    rw [integral_prod _ (h1.comp_fst _),integral_prod _ (h0.comp_snd _)]
    simp only [integral_const,probReal_univ,one_smul]
    have hm0 := windowCommonLaw_height_mean ν L hL he hi n n
    have hm1 := windowCommonLaw_height_mean ν L hL he hi (7*n) n
    push_cast at hm0 hm1
    linarith

lemma axis_renewal_tail_bound_ennreal {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : 0 < annealed μ 0 (nonBacktracking (axisDirection e))) {n N : ℕ} (hnN : n ≤ N) :
    axisReachProb μ e n-axisReachProb μ e N ≤ (N : ℝ≥0∞)*axisWidthTail μ e n := by
  have := slabLaw_probability μ (axisDirection e) hp
  apply (ENNReal.toReal_le_toReal (lt_of_le_of_lt tsub_le_self (measure_lt_top _ _)).ne
    (ENNReal.mul_ne_top (by simp) (measure_ne_top _ _))).mp
  change (axisReachProb μ e n-axisReachProb μ e N).toReal ≤ ((N : ℝ≥0∞)*axisWidthTail μ e n).toReal
  rw [ENNReal.toReal_sub_of_le (axisReachProb_antitone μ e hnN) (measure_ne_top _ _),
    ENNReal.toReal_mul,ENNReal.toReal_natCast]
  refine (axis_renewal_tail_bound μ hell e hp hnN).2.trans ?_
  exact mul_le_mul_of_nonneg_right (sub_le_self _ (Nat.cast_nonneg _)) ENNReal.toReal_nonneg

def experimentContact {d : ℕ} (e : Step d) :
    Set (((ℕ × (ℕ × ℕ)) × Site d) × (ThreeLists (Word d) × ThreeLists (Word d))) :=
  {x | x.2 ∈ middleContact (x.1.2-stepVector e)}

lemma experimentReference_contact_bound {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : ∀ b, 0 < annealed μ 0 (nonBacktracking (axisDirection (placedAxis e b))))
    (he : letI : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) :=
      fun b => slabLaw_probability μ _ (hp b)
      ∀ᵐ Z ∂twoTapeLaw (fun b => slabLaw μ (axisDirection (placedAxis e b))),
      ∃ H, 0 < H ∧ Z ∈ commonCut (placedWidth e) H)
    (hi : letI : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) :=
      fun b => slabLaw_probability μ _ (hp b)
      Integrable (fun Z => (firstCommonWidth (placedWidth e) Z : ℝ))
      (twoTapeLaw (fun b => slabLaw μ (axisDirection (placedAxis e b)))))
    (n : ℕ) [NeZero n] :
    letI : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) :=
      fun b => slabLaw_probability μ _ (hp b)
    experimentReference (fun b => slabLaw μ (axisDirection (placedAxis e b))) (placedWidth e)
      (fun _ => wordEnd) n (experimentContact e) ≤
      ((annealed μ 0 (nonBacktracking (axisDirection e)))⁻¹)^2 *
      ((annealed μ 0 (nonBacktracking (axisDirection (oppositeStep e))))⁻¹)^2 * 2 *
      ENNReal.ofReal (12*n*(∫ Z, (firstCommonWidth (placedWidth e) Z : ℝ)
        ∂twoTapeLaw (fun b => slabLaw μ (axisDirection (placedAxis e b))))) *
      (axisWidthTail μ e n+axisWidthTail μ (oppositeStep e) n) := by
  let : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) :=
    fun b => slabLaw_probability μ _ (hp b)
  have : Countable (Word d) := inferInstance
  have : Countable (TapeList (Word d)) := inferInstance
  have : Countable (ThreeLists (Word d)) := inferInstance
  let ν := fun b => slabLaw μ (axisDirection (placedAxis e b))
  let P := experimentLaw ν (placedWidth e) (fun _ => wordEnd) n
  let C : ℝ≥0∞ := ((annealed μ 0 (nonBacktracking (axisDirection e)))⁻¹)^2 *
      ((annealed μ 0 (nonBacktracking (axisDirection (oppositeStep e))))⁻¹)^2 * 2
  let F := axisWidthTail μ e n+axisWidthTail μ (oppositeStep e) n
  have hL (b : Bool) : ∀ᵐ a ∂ν b, 0 < placedWidth e b a := by
    filter_upwards [ae_slabLaw_regeneration μ hell _ (axisDirection_ne_zero _) (hp b)] with a ha
    exact slabRecords_pos _ _ ha
  have hu (b : Bool) (H : ℕ) : Measure.infinitePi (fun _ : ℕ => ν b)
      (renewalCut (placedWidth e b) H) ≠ 0 := by
    rw [show Measure.infinitePi (fun _ : ℕ => ν b) (renewalCut (placedWidth e b) H) =
      axisReachProb μ (placedAxis e b) H from axis_tapeCut_mass μ hell _ (hp b) H]
    exact ne_of_gt ((hp b).trans_le (axisReachProb_lower μ hell _ _))
  let : IsMarkovKernel (signedThreeKernel (ν false) (placedWidth e false)) :=
    signedThreeKernel_markov _ _ (hu false)
  let : IsMarkovKernel (signedThreeKernel (ν true) (placedWidth e true)) :=
    signedThreeKernel_markov _ _ (hu true)
  have hs : ∀ᵐ x ∂P.fst, n ≤ x.1.1 ∧ n ≤ x.1.2.2 ∧
      axisHeight e x.2 = ((x.1.1+x.1.2.1+x.1.2.2 : ℕ) : ℤ) := by
    rw [Measure.fst,ae_map_iff measurable_fst.aemeasurable (Set.to_countable _).measurableSet]
    exact experimentLaw_axis_support μ hell e hp he n
  have hm := experiment_height_moment ν (placedWidth e) hL he hi (fun _ => wordEnd) n
  have hm' : Integrable (fun x : (ℕ × (ℕ × ℕ)) × Site d =>
      ((x.1.1+x.1.2.1+x.1.2.2 : ℕ) : ℝ)) P.fst := by
    rw [Measure.fst,integrable_map_measure (measurable_of_countable _).aestronglyMeasurable measurable_fst.aemeasurable]
    exact hm.1
  have hmean : (∫⁻ x : (ℕ × (ℕ × ℕ)) × Site d,
      (x.1.1+x.1.2.1+x.1.2.2 : ℝ≥0∞) ∂P.fst) ≤
      ENNReal.ofReal (12*n*(∫ Z, (firstCommonWidth (placedWidth e) Z : ℝ) ∂twoTapeLaw ν)) := by
    have heq (x : (ℕ × (ℕ × ℕ)) × Site d) :
        (x.1.1+x.1.2.1+x.1.2.2 : ℝ≥0∞) = ENNReal.ofReal ((x.1.1+x.1.2.1+x.1.2.2 : ℕ) : ℝ) := by
      norm_cast
    simp_rw [heq]
    rw [← ofReal_integral_eq_lintegral_ofReal hm' (Filter.Eventually.of_forall (by intro x; positivity)),
      Measure.fst,integral_map measurable_fst.aemeasurable (measurable_of_countable _).aestronglyMeasurable]
    exact ENNReal.ofReal_le_ofReal hm.2
  unfold experimentReference
  rw [Measure.compProd_apply (Set.to_countable _).measurableSet]
  change (∫⁻ x, _ ∂P.fst) ≤ _
  calc
    _ ≤ ∫⁻ x : (ℕ × (ℕ × ℕ)) × Site d, C*(x.1.1+x.1.2.1+x.1.2.2 : ℝ≥0∞)*F ∂P.fst := by
      apply lintegral_mono_ae
      filter_upwards [hs] with x hx
      have hz : axisHeight e (x.2-stepVector e) = ((x.1.1+x.1.2.1+x.1.2.2 : ℕ) : ℤ)-1 := by
        rw [sub_eq_add_neg,axisHeight_add,axisHeight_neg,axisHeight_step_self,hx.2.2]; rfl
      have hh := four_bridge_contact_le μ hell e (hp false) (hp true) x.1 (x.2-stepVector e) n hx.1 hx.2.1 hz
      rw [Kernel.comap_apply,Kernel.prod_apply]
      change ((signedThreeKernel (ν false) (placedWidth e false) x.1).prod
        (signedThreeKernel (ν true) (placedWidth e true) x.1)) (middleContact (x.2-stepVector e)) ≤ _
      refine hh.trans ?_
      have hp' := axis_renewal_tail_bound_ennreal μ hell e (hp false)
        (show n ≤ x.1.1+x.1.2.1+x.1.2.2 by omega)
      have hm' := axis_renewal_tail_bound_ennreal μ hell (oppositeStep e) (hp true)
        (show n ≤ x.1.1+x.1.2.1+x.1.2.2 by omega)
      calc
        _ ≤ _ * _ * (2*((x.1.1+x.1.2.1+x.1.2.2 : ℝ≥0∞)*axisWidthTail μ e n+
            (x.1.1+x.1.2.1+x.1.2.2 : ℝ≥0∞)*axisWidthTail μ (oppositeStep e) n)) := by
              gcongr
              · simpa only [Nat.cast_add] using hp'
              · simpa only [Nat.cast_add] using hm'
        _ = _ := by dsimp only [C,F];ring
    _ = C*(∫⁻ x : (ℕ × (ℕ × ℕ)) × Site d, (x.1.1+x.1.2.1+x.1.2.2 : ℝ≥0∞) ∂P.fst)*F := by
      rw [lintegral_mul_const _ (measurable_of_countable _),lintegral_const_mul _ (measurable_of_countable _)]
    _ ≤ _ := by
      change C*_ *F ≤ C*_ *F
      exact mul_le_mul_left (mul_le_mul_right hmean C) F

lemma axisBridgeWords_prefixFree {d : ℕ} (e : Step d) (k : ℕ) :
    PrefixFreeWords {a : Word d | AxisBridgeWord e k a} := by
  intro a b hab
  exact (firstHitWords_prefixFree (axisUpper e k))
    (i := ⟨a,a.property.firstHit⟩) (j := ⟨b,b.property.firstHit⟩)
    (fun h => hab (Subtype.ext (congrArg (fun x : {a | firstHitWord (axisUpper e k) a} => x.val) h)))

lemma prefix_contact_total_bound {d ι : ℕ} [NeZero ι]
    (μ : Measure (Row d)) [IsProbabilityMeasure μ] (hell : StrictEllipticity μ)
    (e : Step d) (k r N m : ℕ) (hrN : r ≤ N)
    (E : Word d → Fin ι → Set (Path d)) (hE : ∀ a q, MeasurableSet (E a q))
    (hdis : ∀ a, Pairwise (fun i j => Disjoint (E a i) (E a j)))
    (start : Word d → Fin ι → Site d)
    (hΔ : axisReachProb μ e r-axisReachProb μ e N ≤ ENNReal.ofReal ((1/2 : ℝ)^m)) :
    (∑' a : {a : Word d | AxisBridgeWord e k a}, ∑ q,
      ∑' b : {b | upperContactWord 0 (axisUpper e r) (axisLower e 0 ∪ axisUpper e N) b},
        annealed μ 0 (wordCylinder a ∩ (shiftPath (-wordEnd a) ∘ tailPath a.val.1) ⁻¹'
          (E a q ∩ wordCylinder b)) *
        annealed μ (start a q) (avoids (axisUpper e N) ∩ contactAvoid b)) ≤
      ENNReal.ofReal ((24 / posteriorExponent)*Real.log (ι+1)*(m+1)^2*(1/2 : ℝ)^m) := by
  let C := ENNReal.ofReal ((24 / posteriorExponent)*Real.log (ι+1)*(m+1)^2*(1/2 : ℝ)^m)
  calc
    _ ≤ ∑' a : {a : Word d | AxisBridgeWord e k a}, annealed μ 0 (wordCylinder a)*C := by
      apply ENNReal.tsum_le_tsum
      intro a
      by_cases ha : annealed μ 0 (wordCylinder a) = 0
      · have hz (q : Fin ι) (b : {b | upperContactWord 0 (axisUpper e r) (axisLower e 0 ∪ axisUpper e N) b}) :
          annealed μ 0 (wordCylinder a ∩ (shiftPath (-wordEnd a) ∘ tailPath a.val.1) ⁻¹'
            (E a q ∩ wordCylinder b)) = 0 := measure_mono_null Set.inter_subset_left ha
        simp only [hz,zero_mul,tsum_zero,Finset.sum_const_zero,ha,le_refl]
      · exact posterior_old_prefix_weighted_bound μ hell e a ha
          (fun i hi => (a.property.2 i hi).2.trans_eq a.property.1.symm)
          (E a) (hE a) (hdis a) (start a) r N m hrN hΔ
    _ = annealed μ 0 (⋃ a : {a : Word d | AxisBridgeWord e k a}, wordCylinder a)*C := by
      rw [ENNReal.tsum_mul_right,measure_iUnion (axisBridgeWords_prefixFree e k)
        (fun _ => measurableSet_pathCylinder _ _)]
    _ ≤ C := by simpa only [one_mul] using mul_le_mul_left (prob_le_one (μ := annealed μ 0)) C

lemma conditioned_negative_shift {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (e : Step d) (z : Site d) (N : ℕ) (hz : axisHeight e z = (N : ℤ)-1)
    (E : Set (Path d)) (hE : MeasurableSet E) :
    conditioned μ (axisDirection (oppositeStep e)) (shiftPath z ⁻¹' E) =
      (annealed μ 0 (nonBacktracking (axisDirection (oppositeStep e))))⁻¹ *
        annealed μ z (avoids (axisUpper e N) ∩ E) := by
  have hb : shiftPath z ⁻¹' avoids (axisUpper e N) = nonBacktracking (axisDirection (oppositeStep e)) := by
    ext X
    change (∀ j, ¬(N : ℤ) ≤ axisHeight e (X j+z)) ↔
      ∀ j, 0 ≤ height (axisDirection (oppositeStep e)) (X j)
    simp only [axisHeight_add,hz,height_axisDirection,axisHeight_opposite]
    constructor
    · intro h j
      have hj := h j
      have hx : axisHeight e (X j) ≤ 0 := by omega
      exact_mod_cast (neg_nonneg.mpr hx)
    · intro h j
      have hx : -(axisHeight e (X j)) ≥ 0 := by exact_mod_cast h j
      omega
  rw [conditioned,cond_apply (measurableSet_nonBacktracking _)]
  have hh := congrArg (fun M : Measure (Path d) => M (avoids (axisUpper e N) ∩ E)) (annealed_shift μ 0 z)
  rw [zero_add,Measure.map_apply (measurable_shiftPath z) ((measurableSet_avoids _).inter hE),
    Set.preimage_inter,hb] at hh
  rw [hh]

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

def latePrefixEvent {d ι : ℕ} (e : Step d) (k r N : ℕ)
    (E : Word d → Fin ι → Set (Path d)) (start : Word d → Fin ι → Site d) :
    Set (Path d × Path d) :=
  ⋃ a : {a : Word d | AxisBridgeWord e k a}, ⋃ q : Fin ι,
    ⋃ b : {b | upperContactWord 0 (axisUpper e r) (axisLower e 0 ∪ axisUpper e N) b},
      (wordCylinder a ∩ (shiftPath (-wordEnd a) ∘ tailPath a.val.1) ⁻¹' (E a q ∩ wordCylinder b)) ×ˢ
        (shiftPath (start a q) ⁻¹' contactAvoid b)

lemma latePrefixEvent_bound {d ι : ℕ} [NeZero ι]
    (μ : Measure (Row d)) [IsProbabilityMeasure μ] (hell : StrictEllipticity μ)
    (e : Step d) (k r N m : ℕ) (hrN : r ≤ N)
    (E : Word d → Fin ι → Set (Path d)) (hE : ∀ a q, MeasurableSet (E a q))
    (hdis : ∀ a, Pairwise (fun i j => Disjoint (E a i) (E a j)))
    (start : Word d → Fin ι → Site d)
    (hstart : ∀ a, AxisBridgeWord e k a → ∀ q, axisHeight e (start a q) = (N : ℤ)-1)
    (hΔ : axisReachProb μ e r-axisReachProb μ e N ≤ ENNReal.ofReal ((1/2 : ℝ)^m)) :
    ((annealed μ 0).prod (conditioned μ (axisDirection (oppositeStep e))))
      (latePrefixEvent e k r N E start) ≤
      (annealed μ 0 (nonBacktracking (axisDirection (oppositeStep e))))⁻¹ *
        ENNReal.ofReal ((24 / posteriorExponent)*Real.log (ι+1)*(m+1)^2*(1/2 : ℝ)^m) := by
  have : IsFiniteMeasure (conditioned μ (axisDirection (oppositeStep e))) := by
    unfold conditioned
    infer_instance
  unfold latePrefixEvent
  calc
    _ ≤ ∑' a : {a : Word d | AxisBridgeWord e k a}, ∑' q : Fin ι,
      ∑' b : {b | upperContactWord 0 (axisUpper e r) (axisLower e 0 ∪ axisUpper e N) b},
        ((annealed μ 0).prod (conditioned μ (axisDirection (oppositeStep e))))
          ((wordCylinder a ∩ (shiftPath (-wordEnd a) ∘ tailPath a.val.1) ⁻¹' (E a q ∩ wordCylinder b)) ×ˢ
            (shiftPath (start a q) ⁻¹' contactAvoid b)) := by
        apply (measure_iUnion_le _).trans
        apply ENNReal.tsum_le_tsum
        intro a
        apply (measure_iUnion_le _).trans
        exact ENNReal.tsum_le_tsum (fun q => measure_iUnion_le _)
    _ = (annealed μ 0 (nonBacktracking (axisDirection (oppositeStep e))))⁻¹ *
      (∑' a : {a : Word d | AxisBridgeWord e k a}, ∑ q,
        ∑' b : {b | upperContactWord 0 (axisUpper e r) (axisLower e 0 ∪ axisUpper e N) b},
          annealed μ 0 (wordCylinder a ∩ (shiftPath (-wordEnd a) ∘ tailPath a.val.1) ⁻¹' (E a q ∩ wordCylinder b)) *
          annealed μ (start a q) (avoids (axisUpper e N) ∩ contactAvoid b)) := by
        rw [← ENNReal.tsum_mul_left]
        apply tsum_congr
        intro a
        rw [tsum_fintype,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q _
        rw [← ENNReal.tsum_mul_left]
        apply tsum_congr
        intro b
        rw [Measure.prod_prod,conditioned_negative_shift μ e _ N (hstart _ a.property _) _ (measurableSet_contactAvoid _)]
        ac_rfl
    _ ≤ _ := mul_le_mul_right (prefix_contact_total_bound μ hell e k r N m hrN E hE hdis start hΔ) _

def prependRelative {d : ℕ} (a : Word d) (R : Path d) : Path d :=
  concatPath a.1 (wordPath a) (shiftPath (wordEnd a) R)

lemma measurable_prependRelative {d : ℕ} (a : Word d) : Measurable (prependRelative a) := by
  apply Measurable.of_eval
  intro j
  by_cases hj : j < a.1
  · simpa only [prependRelative,concatPath,ite_eq_left hj] using
      (measurable_const : Measurable (fun _ : Path d => wordPath a j))
  · have hm : Measurable (fun R : Path d => R (j-a.1)) := measurable_pi_apply _
    simpa only [prependRelative,concatPath,ite_eq_right hj,shiftPath] using hm.add_const (wordEnd a)

lemma prependRelative_recover {d : ℕ} (a : Word d) (X : Path d) (hX : X ∈ wordCylinder a) :
    prependRelative a (shiftPath (-wordEnd a) (tailPath a.1 X)) = X := by
  funext j
  by_cases hj : j < a.1
  · simpa only [prependRelative,concatPath,ite_eq_left hj] using (hX j hj.le).symm
  · simp only [prependRelative,concatPath,ite_eq_right hj,shiftPath,tailPath,
      Nat.add_sub_of_le (Nat.le_of_not_gt hj),neg_add_cancel_right]

lemma latePrefixEvent_of_contact {d ι : ℕ} (e : Step d)
    (k r N : ℕ) (hr : k ≤ r) (hN : k ≤ N)
    (E : Fin ι → Set (Path d)) (z : Fin ι → Site d)
    (X Y : Path d) (q : Fin ι) (hE : X ∈ E q)
    (t τ : ℕ) (htτ : t ≤ τ)
    (hold : AxisBridgeWord e k (prefixWord t X))
    (hband : ∀ j, t ≤ j → j ≤ τ → (k : ℤ) ≤ axisHeight e (X j) ∧ axisHeight e (X j) < (N : ℤ))
    (hreached : ∃ j, t ≤ j ∧ j ≤ τ ∧ (r : ℤ) ≤ axisHeight e (X j))
    (hhit : ∃ j, Y j+z q = X τ)
    (hbefore : ∀ i, t ≤ i → i < τ → ∀ j, Y j+z q ≠ X i) :
    (X,Y) ∈ latePrefixEvent e k (r-k) (N-k)
      (fun a q => prependRelative a ⁻¹' E q) (fun a q => z q-wordEnd a) := by
  let a := prefixWord t X
  let R := shiftPath (-wordEnd a) (tailPath t X)
  let b := prefixWord (τ-t) R
  have ha : X ∈ wordCylinder a := fun j hj => (wordPath_prefixWord t X hj).symm
  have hend : wordEnd a = X t := wordPath_prefixWord t X le_rfl
  have hbpath (j : ℕ) (hj : j ≤ τ-t) : wordPath b j = X (t+j)-X t := by
    rw [wordPath_prefixWord (τ-t) R hj]
    change X (t+j)+(-wordEnd a) = _
    rw [hend,sub_eq_add_neg]
  have hb : upperContactWord 0 (axisUpper e ((r-k : ℕ) : ℤ))
      (axisLower e 0 ∪ axisUpper e ((N-k : ℕ) : ℤ)) b := by
    refine ⟨?_,?_,?_⟩
    · rw [hbpath 0 (Nat.zero_le _),Nat.add_zero,sub_self]
    · obtain ⟨j,htj,hjτ,hjr⟩ := hreached
      refine ⟨j-t,by change j-t ≤ τ-t;omega,?_⟩
      rw [hbpath (j-t) (by omega),Nat.add_sub_of_le htj]
      change ((r-k : ℕ) : ℤ) ≤ axisHeight e (X j-X t)
      rw [sub_eq_add_neg,axisHeight_add,axisHeight_neg,← hend,hold.1,Nat.cast_sub hr]
      omega
    · intro j hj
      rw [hbpath j hj]
      have hjτ : t+j ≤ τ := by change j ≤ τ-t at hj;omega
      obtain ⟨hlo,hhi⟩ := hband (t+j) (by omega) hjτ
      change ¬(axisHeight e (X (t+j)-X t) < (0 : ℤ) ∨
        ((N-k : ℕ) : ℤ) ≤ axisHeight e (X (t+j)-X t))
      rw [sub_eq_add_neg,axisHeight_add,axisHeight_neg,← hend,hold.1,Nat.cast_sub hN]
      omega
  have hca : shiftPath (z q-wordEnd a) Y ∈ contactAvoid b := by
    rw [contactAvoid_iff_firstHit]
    constructor
    · obtain ⟨j,hj⟩ := hhit
      refine ⟨j,?_⟩
      change Y j+(z q-wordEnd a) = wordPath b (τ-t)
      rw [hbpath (τ-t) le_rfl,Nat.add_sub_of_le htτ,hend]
      rw [sub_eq_add_neg,← add_assoc,hj,sub_eq_add_neg]
    · intro i hi
      rintro ⟨j,hj⟩
      apply hbefore (t+i) (by omega) (by change i < τ-t at hi;omega) j
      rw [hbpath i hi.le] at hj
      change Y j+(z q-wordEnd a) = X (t+i)-X t at hj
      rw [hend,sub_eq_add_neg,sub_eq_add_neg,← add_assoc] at hj
      exact add_right_cancel hj
  refine Set.mem_iUnion.mpr ⟨⟨a,hold⟩,Set.mem_iUnion.mpr ⟨q,Set.mem_iUnion.mpr ⟨⟨b,hb⟩,?_⟩⟩⟩
  refine ⟨⟨ha,?_,?_⟩,hca⟩
  · change prependRelative a R ∈ E q
    exact (prependRelative_recover a X ha).symm ▸ hE
  · exact fun j hj => (wordPath_prefixWord (τ-t) R hj).symm

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

def lateContactEvent {d ι : ℕ} (e : Step d) (k r N : ℕ)
    (E : Fin ι → Set (Path d)) (z : Fin ι → Site d) : Set (Path d × Path d) :=
  {p | ∃ q, p.1 ∈ E q ∧ ∃ t τ, t ≤ τ ∧
    AxisBridgeWord e k (prefixWord t p.1) ∧
    (∀ j, t ≤ j → j ≤ τ → (k : ℤ) ≤ axisHeight e (p.1 j) ∧ axisHeight e (p.1 j) < (N : ℤ)) ∧
    (∃ j, t ≤ j ∧ j ≤ τ ∧ (r : ℤ) ≤ axisHeight e (p.1 j)) ∧
    (∃ j, p.2 j+z q = p.1 τ) ∧
    (∀ i, t ≤ i → i < τ → ∀ j, p.2 j+z q ≠ p.1 i)}

lemma lateContactEvent_bound {d ι : ℕ} [NeZero ι]
    (μ : Measure (Row d)) [IsProbabilityMeasure μ] (hell : StrictEllipticity μ)
    (e : Step d) (k r N m : ℕ) (hkr : k ≤ r) (hrN : r ≤ N)
    (E : Fin ι → Set (Path d)) (hE : ∀ q, MeasurableSet (E q))
    (hdis : Pairwise (fun i j => Disjoint (E i) (E j)))
    (z : Fin ι → Site d) (hz : ∀ q, axisHeight e (z q) = (N : ℤ)-1)
    (hΔ : axisReachProb μ e (r-k)-axisReachProb μ e (N-k) ≤ ENNReal.ofReal ((1/2 : ℝ)^m)) :
    ((annealed μ 0).prod (conditioned μ (axisDirection (oppositeStep e))))
      (lateContactEvent e k r N E z) ≤
      (annealed μ 0 (nonBacktracking (axisDirection (oppositeStep e))))⁻¹ *
        ENNReal.ofReal ((24 / posteriorExponent)*Real.log (ι+1)*(m+1)^2*(1/2 : ℝ)^m) := by
  refine (measure_mono (t := latePrefixEvent e k (r-k) (N-k)
      (fun a q => prependRelative a ⁻¹' E q) (fun a q => z q-wordEnd a)) ?_).trans ?_
  · rintro ⟨X,Y⟩ ⟨q,hq,t,τ,htτ,ha,hband,hr,hh,hbefore⟩
    exact latePrefixEvent_of_contact e k r N hkr (hkr.trans hrN) E z X Y q hq t τ htτ ha hband hr hh hbefore
  · apply latePrefixEvent_bound μ hell e k (r-k) (N-k) m (Nat.sub_le_sub_right hrN k)
      _ (fun a q => measurable_prependRelative a (hE q))
      (fun a i j hij => (hdis hij).preimage _) _ _ hΔ
    intro a ha q
    rw [sub_eq_add_neg,axisHeight_add,axisHeight_neg,hz q,ha.1,Nat.cast_sub (hkr.trans hrN)]
    omega

lemma conditioned_bridge_late_bound {d ι : ℕ} [NeZero ι]
    (μ : Measure (Row d)) [IsProbabilityMeasure μ] (hell : StrictEllipticity μ)
    (e : Step d) (k r N m : ℕ) (hkr : k ≤ r) (hrN : r ≤ N)
    (E : Fin ι → Set (Path d)) (hE : ∀ q, MeasurableSet (E q))
    (hdis : Pairwise (fun i j => Disjoint (E i) (E j)))
    (z : Fin ι → Site d) (hz : ∀ q, axisHeight e (z q) = (N : ℤ)-1)
    (hΔ : axisReachProb μ e (r-k)-axisReachProb μ e (N-k) ≤ ENNReal.ofReal ((1/2 : ℝ)^m)) :
    ((ProbabilityTheory.cond (annealed μ 0) (reachRecord (axisDirection e) N)).prod
      (conditioned μ (axisDirection (oppositeStep e)))) (lateContactEvent e k r N E z) ≤
      (axisReachProb μ e N)⁻¹ *
      (annealed μ 0 (nonBacktracking (axisDirection (oppositeStep e))))⁻¹ *
        ENNReal.ofReal ((24 / posteriorExponent)*Real.log (ι+1)*(m+1)^2*(1/2 : ℝ)^m) := by
  have : IsFiniteMeasure (conditioned μ (axisDirection (oppositeStep e))) := by
    unfold conditioned
    infer_instance
  rw [ProbabilityTheory.cond,Measure.prod_smul_left,Measure.smul_apply,← axisReachProb_eq_record]
  change (axisReachProb μ e N)⁻¹ * _ ≤ _
  rw [mul_assoc]
  apply mul_le_mul_right
  refine (Measure.prod_mono Measure.restrict_le_self le_rfl _).trans ?_
  exact lateContactEvent_bound μ hell e k r N m hkr hrN E hE hdis z hz hΔ

lemma iid_tape_strongLaw {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (f : α → ℝ)
    (hf : Measurable f) (hi : Integrable f ν) :
    ∀ᵐ Z ∂Measure.infinitePi (fun _ : ℕ => ν),
      Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, f (Z i))/n) atTop (𝓝 (∫ a, f a ∂ν)) := by
  let P := Measure.infinitePi (fun _ : ℕ => ν)
  have hid (k : ℕ) : IdentDistrib (fun Z : ℕ → α => f (Z k)) f P ν := by
    refine ⟨(hf.comp (measurable_pi_apply k)).aemeasurable,hf.aemeasurable,?_⟩
    rw [show P.map (fun Z => f (Z k)) = (P.map (fun Z => Z k)).map f from
      (Measure.map_map hf (measurable_pi_apply k)).symm,Measure.infinitePi_map_eval]
  have hind := iIndepFun_infinitePi (P := fun _ : ℕ => ν) (X := fun _ => f) (fun _ => hf)
  have hx := strong_law_ae_real (fun k (Z : ℕ → α) => f (Z k))
    ((hid 0).integrable_iff.mpr hi) (fun i j hij => hind.indepFun hij)
    (fun k => (hid k).trans (hid 0).symm)
  rwa [(hid 0).integral_eq] at hx

lemma tapeHeight_strongLaw {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Measure α) [IsProbabilityMeasure ν]
    (L : α → ℕ) (hi : Integrable (fun a => (L a : ℝ)) ν) :
    ∀ᵐ Z ∂Measure.infinitePi (fun _ : ℕ => ν),
      Tendsto (fun n : ℕ => (tapeHeight L Z n : ℝ)/n) atTop (𝓝 (∫ a, (L a : ℝ) ∂ν)) := by
  simpa only [tapeHeight,Nat.cast_sum] using iid_tape_strongLaw ν _ (measurable_of_countable _) hi

lemma firstCommonBlock_height {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i))) (he : ∃ H, 0 < H ∧ Z ∈ commonCut L H) :
    chunkHeight L (firstCommonBlock L Z) = firstCommonWidth L Z := by
  exact ((commonCutList_atom_iff L _ Z hZ (firstCommonBlock L Z)).mp
    ⟨(firstCommonWidth_spec L Z he).2.1,rfl⟩).1 false

lemma commonDepth_strongLaw {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (hi : Integrable (fun Z => (firstCommonWidth L Z : ℝ)) (twoTapeLaw ν)) :
    ∀ᵐ Z ∂twoTapeLaw ν,
      Tendsto (fun n : ℕ => (commonDepth L Z n : ℝ)/n) atTop
        (𝓝 (∫ Z, (firstCommonWidth L Z : ℝ) ∂twoTapeLaw ν)) := by
  have ha : (fun Z => (chunkHeight L (firstCommonBlock L Z) : ℝ)) =ᵐ[twoTapeLaw ν]
      fun Z => (firstCommonWidth L Z : ℝ) := by
    filter_upwards [ae_twoTape_prop ν (fun b a => 0 < L b a)
      (fun b => measurableSet_lt measurable_const (measurable_of_countable (L b))) hL,he] with Z hZ he
    exact_mod_cast firstCommonBlock_height L Z hZ he
  have hii : Integrable (fun a => (chunkHeight L a : ℝ)) (commonBlockLaw ν L) := by
    rw [commonBlockLaw,integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
      (measurable_firstCommonBlock L).aemeasurable]
    exact hi.congr ha.symm
  have hei : (∫ a, (chunkHeight L a : ℝ) ∂commonBlockLaw ν L) =
      ∫ Z, (firstCommonWidth L Z : ℝ) ∂twoTapeLaw ν := by
    rw [commonBlockLaw,integral_map (measurable_firstCommonBlock L).aemeasurable
      (measurable_of_countable _).aestronglyMeasurable]
    exact integral_congr_ae ha
  let : IsProbabilityMeasure (commonBlockLaw ν L) :=
    probabilityMeasure_map (measurable_firstCommonBlock L).aemeasurable
  have hh := iid_tape_strongLaw (commonBlockLaw ν L) (fun a => (chunkHeight L a : ℝ))
    (measurable_of_countable _) hii
  rw [← commonBlocks_map ν L hL he] at hh
  have hm : Measurable (commonBlocks L) := by
    apply Measurable.of_eval
    intro k
    exact (measurable_firstCommonBlock L).comp ((measurable_commonRestart L).iterate k)
  have ht := ae_of_ae_map hm.aemeasurable hh
  rw [hei] at ht
  filter_upwards [ht,ae_twoTape_prop ν (fun b a => 0 < L b a)
    (fun b => measurableSet_lt measurable_const (measurable_of_countable (L b))) hL,
    ae_common_iterates ν L hL he] with Z hZ hpos hiter
  have hsum (n : ℕ) : (∑ i ∈ Finset.range n, (chunkHeight L (commonBlocks L Z i) : ℝ)) =
      (commonDepth L Z n : ℝ) := by
    simp only [commonDepth,Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hposi : ∀ b j, 0 < L b (((commonRestart L)^[i] Z) (b,j)) := by
      rw [← (commonDepth_spec L Z hpos hiter i).2.1]
      exact fun b j => hpos b _
    exact_mod_cast firstCommonBlock_height L _ hposi (hiter i)
  simpa only [hsum] using hZ

lemma placed_slab_positive {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : ∀ b, 0 < annealed μ 0 (nonBacktracking (axisDirection (placedAxis e b)))) (b : Bool) :
    ∀ᵐ a ∂slabLaw μ (axisDirection (placedAxis e b)), 0 < placedWidth e b a := by
  filter_upwards [ae_slabLaw_regeneration μ hell _ (axisDirection_ne_zero _) (hp b)] with a ha
  exact slabRecords_pos _ _ ha

lemma placed_common_lower {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : ∀ b, 0 < annealed μ 0 (nonBacktracking (axisDirection (placedAxis e b)))) (H : ℕ) :
    letI : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) :=
      fun b => slabLaw_probability μ _ (hp b)
    annealed μ 0 (nonBacktracking (axisDirection e)) *
      annealed μ 0 (nonBacktracking (axisDirection (oppositeStep e))) ≤
      twoTapeLaw (fun b => slabLaw μ (axisDirection (placedAxis e b))) (commonCut (placedWidth e) H) := by
  let : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) :=
    fun b => slabLaw_probability μ _ (hp b)
  rw [commonCut_mass,show Measure.infinitePi (fun _ : ℕ => slabLaw μ (axisDirection (placedAxis e false)))
      (renewalCut (placedWidth e false) H) = axisReachProb μ e H from axis_tapeCut_mass μ hell _ (hp false) H,
    show Measure.infinitePi (fun _ : ℕ => slabLaw μ (axisDirection (placedAxis e true)))
      (renewalCut (placedWidth e true) H) = axisReachProb μ (oppositeStep e) H from axis_tapeCut_mass μ hell _ (hp true) H]
  exact mul_le_mul' (axisReachProb_lower μ hell e H) (axisReachProb_lower μ hell (oppositeStep e) H)

lemma placed_common_data {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : ∀ b, 0 < annealed μ 0 (nonBacktracking (axisDirection (placedAxis e b)))) :
    letI : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) :=
      fun b => slabLaw_probability μ _ (hp b)
    (∀ᵐ Z ∂twoTapeLaw (fun b => slabLaw μ (axisDirection (placedAxis e b))),
      ∃ H, 0 < H ∧ Z ∈ commonCut (placedWidth e) H) ∧
    Integrable (fun Z => (firstCommonWidth (placedWidth e) Z : ℝ))
      (twoTapeLaw (fun b => slabLaw μ (axisDirection (placedAxis e b)))) := by
  let : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) :=
    fun b => slabLaw_probability μ _ (hp b)
  have hc := mul_ne_zero (ne_of_gt (hp false)) (ne_of_gt (hp true))
  exact ⟨ae_exists_commonCut _ _ (placed_slab_positive μ hell e hp) _ hc (placed_common_lower μ hell e hp),
    integrable_firstCommonWidth _ _ (placed_slab_positive μ hell e hp) _ hc (placed_common_lower μ hell e hp)⟩

lemma placed_slabRadius_integrable {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : ∀ b, 0 < annealed μ 0 (nonBacktracking (axisDirection (placedAxis e b)))) (b : Bool) :
    Integrable slabRadius (slabLaw μ (axisDirection (placedAxis e b))) := by
  have hn : annealed μ 0 (nonBacktracking (-axisDirection e)) > 0 := by
    rw [← axisDirection_opposite]
    exact hp true
  have hh := integrable_slabRadius_normalized μ hell _ (axisDirection_ne_zero e)
    (axisDirection_normalized e).1 (axisDirection_normalized e).2 (hp false) hn
  cases b
  · exact hh.1
  · simpa only [placedAxis,↓reduceIte,axisDirection_opposite] using hh.2

lemma placed_wordEnd_integrable {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : ∀ b, 0 < annealed μ 0 (nonBacktracking (axisDirection (placedAxis e b)))) (b : Bool) (i : Fin d) :
    Integrable (fun a => (wordEnd a i : ℝ)) (slabLaw μ (axisDirection (placedAxis e b))) := by
  have hh := integrable_slabProjection μ hell _ (axisDirection_ne_zero _) (hp b)
    (placed_slabRadius_integrable μ hell e hp b) (Pi.single i 1)
  change Integrable (fun a => height (Pi.single i 1) (wordEnd a)) _ at hh
  simpa [height,Pi.single_apply] using hh

lemma concatenateWords_end {d : ℕ} (n : ℕ) (a : Fin n → Word d) :
    wordEnd (concatenateWords n a) = ∑ i, wordEnd (a i) := by
  induction n with
  | zero => simp [concatenateWords,wordEnd,prefixWord,wordPath,extendPrefix]
  | succ n ih =>
    change wordPath (appendWord (concatenateWords n (fun i => a i.castSucc)) (a (Fin.last n)))
      ((concatenateWords n (fun i => a i.castSucc)).1+(a (Fin.last n)).1) = _
    rw [appendWord_after _ _ le_rfl]
    change wordEnd (concatenateWords n _) + wordEnd (a (Fin.last n)) = _
    rw [ih,Fin.sum_univ_castSucc]

lemma concatenateList_end {d : ℕ} (a : TapeList (Word d)) :
    wordEnd (concatenateList a) = listTotal wordEnd a := concatenateWords_end a.1 a.2

lemma fin_prefix_sum_castSucc {G : Type*} [AddCommMonoid G] {n : ℕ}
    (f : Fin (n+1) → G) (i : Fin n) :
    (∑ j : Fin (n+1) with j < i.castSucc, f j) = ∑ j : Fin n with j < i, f j.castSucc := by
  classical
  simp only [Finset.sum_filter]
  rw [Fin.sum_univ_castSucc]
  simp [show ¬Fin.last n < i.castSucc by simp only [Fin.lt_def,Fin.val_last,Fin.val_castSucc];omega]

lemma fin_prefix_sum_last {G : Type*} [AddCommMonoid G] {n : ℕ}
    (f : Fin (n+1) → G) :
    (∑ j : Fin (n+1) with j < Fin.last n, f j) = ∑ j : Fin n, f j.castSucc := by
  classical
  simp only [Finset.sum_filter]
  rw [Fin.sum_univ_castSucc]
  simp

lemma concatenateWords_site {d n : ℕ} (a : Fin n → Word d)
    (h0 : ∀ i, wordPath (a i) 0 = 0) (i : Fin n) (t : ℕ) (ht : t ≤ (a i).1) :
    wordPath (concatenateWords n a) ((∑ j : Fin n with j < i, (a j).1)+t) =
      (∑ j : Fin n with j < i, wordEnd (a j)) + wordPath (a i) t := by
  classical
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    revert ht
    refine Fin.lastCases ?_ (fun i => ?_) i
    · intro ht
      rw [fin_prefix_sum_last,fin_prefix_sum_last]
      change wordPath (appendWord (concatenateWords n (fun j => a j.castSucc)) (a (Fin.last n)))
        ((∑ j : Fin n, (a j.castSucc).1)+t) = _
      rw [← concatenateWords_length,appendWord_after _ _ ht,← concatenateWords_end]
      rfl
    · intro ht
      rw [fin_prefix_sum_castSucc,fin_prefix_sum_castSucc]
      change wordPath (appendWord (concatenateWords n (fun j => a j.castSucc)) (a (Fin.last n))) _ = _
      rw [appendWord_before _ _ (h0 _) ?_]
      · exact ih (fun j => a j.castSucc) (fun j => h0 _) i ht
      · rw [concatenateWords_length]
        have hs : (∑ j : Fin n with j < i, (a j.castSucc).1)+(a i.castSucc).1 ≤
            ∑ j : Fin n, (a j.castSucc).1 := by
          rw [add_comm,← Finset.sum_insert (f := fun j : Fin n => (a j.castSucc).1) (a := i) (s := Finset.univ.filter (fun j : Fin n => j < i))
            (by simp)]
          exact Finset.sum_le_sum_of_subset (by intro j hj;simp)
        omega

lemma fin_reverse_prefix_sum {G : Type*} [AddCommMonoid G] {n : ℕ}
    (f : Fin n → G) (i : Fin n) :
    (∑ j : Fin n with j < i.rev, f j.rev) + (∑ j : Fin n with j ≤ i, f j) = ∑ j, f j := by
  classical
  have he : (∑ j : Fin n with j < i.rev, f j.rev) = ∑ j : Fin n with ¬j ≤ i, f j := by
    simp only [Finset.sum_filter]
    have hh := Equiv.sum_comp Fin.revPerm (fun j : Fin n => if ¬j ≤ i then f j else 0)
    simpa only [Fin.revPerm_apply,not_le,Fin.lt_rev_iff] using hh
  rw [he,add_comm]
  exact Finset.sum_filter_add_sum_filter_not _ _ _

lemma fin_prefix_sum_range {G : Type*} [AddCommMonoid G] {n : ℕ}
    (f : ℕ → G) (k : ℕ) (hk : k ≤ n) :
    (∑ j : Fin n with j.val < k, f j) = ∑ j ∈ Finset.range k, f j := by
  classical
  simp only [Finset.sum_filter]
  rw [Fin.sum_univ_eq_sum_range (fun j => if j < k then f j else 0)]
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter,Finset.mem_range]
  omega

lemma reversePrefix_site {d n : ℕ} (Z : ℕ → Word d)
    (h0 : ∀ j < n, wordPath (Z j) 0 = 0) (i : Fin n) (t : ℕ) (ht : t ≤ (Z i).1) :
    wordPath (concatenateList (reverseTapeList (tapePrefix n Z)))
      ((∑ j : Fin n with j < i.rev, (Z j.rev).1)+t) =
      (∑ j ∈ Finset.range n, wordEnd (Z j)) - (∑ j ∈ Finset.range (i.val+1), wordEnd (Z j)) +
        wordPath (Z i) t := by
  have hs := concatenateWords_site (fun j : Fin n => Z j.rev)
    (fun j => h0 _ j.rev.isLt) i.rev t (by simpa using ht)
  simp only [Fin.rev_rev] at hs
  change wordPath (concatenateList (reverseTapeList (tapePrefix n Z))) _ = _ at hs
  rw [hs]
  congr 1
  have hh := fin_reverse_prefix_sum (fun j : Fin n => wordEnd (Z j)) i
  have he : (∑ j : Fin n with j ≤ i, wordEnd (Z j)) = ∑ j ∈ Finset.range (i.val+1), wordEnd (Z j) := by
    have heq : Finset.univ.filter (fun j : Fin n => j ≤ i) =
        Finset.univ.filter (fun j : Fin n => j.val < i.val+1) := by
      ext j
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Fin.le_def]
      omega
    rw [heq]
    exact fin_prefix_sum_range (fun j => wordEnd (Z j)) (i.val+1) (by omega)
  rw [he,Fin.sum_univ_eq_sum_range (fun j => wordEnd (Z j))] at hh
  exact eq_sub_of_add_eq hh

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

lemma reversePrefix_opposedSite {d n : ℕ} (e : Step d) (Z : TwoTape (Word d))
    (h0 : ∀ j < n, wordPath (Z (false,j)) 0 = 0) (i : Fin n) (t : ℕ) (ht : t ≤ (Z (false,i)).1) :
    wordPath (concatenateList (reverseTapeList (tapePrefix n (fun j => Z (false,j)))))
      ((∑ j : Fin n with j < i.rev, (Z (false,j.rev)).1)+t) -
      (∑ j ∈ Finset.range n, wordEnd (Z (false,j))) = opposedSite e Z false i t := by
  rw [reversePrefix_site _ h0 i t ht]
  simp only [opposedSite,opposedAnchor,Bool.false_eq_true,↓reduceIte]
  abel

lemma concatenateWords_departure {d n : ℕ} (a : Fin n → Word d)
    (i : Fin n) (t : ℕ) (ht : t < (a i).1) :
    (∑ j : Fin n with j < i, (a j).1)+t < (concatenateWords n a).1 := by
  classical
  rw [concatenateWords_length]
  have hs : (∑ j : Fin n with j < i, (a j).1)+(a i).1 ≤ ∑ j : Fin n, (a j).1 := by
    rw [add_comm,← Finset.sum_insert (f := fun j : Fin n => (a j).1) (a := i)
      (s := Finset.univ.filter (fun j : Fin n => j < i)) (by simp)]
    exact Finset.sum_le_sum_of_subset (by intro j hj;simp)
  omega

lemma opposed_positive_in_finite_bridge {d : ℕ} (e : Step d) (Z : TwoTape (Word d))
    (hZ : ∀ b i, RegenerationWord (axisDirection (placedAxis e b)) (Z (b,i)))
    (n h : ℕ) (hn : h ≤ tapeHeight (placedWidth e false) (fun j => Z (false,j)) n)
    (y : Site d) (hy : opposedDeparture e Z false y) (hh : -axisHeight e y = (h : ℤ)) :
    ∃ t < (concatenateList (reverseTapeList (tapePrefix n (fun j => Z (false,j))))).1,
      wordPath (concatenateList (reverseTapeList (tapePrefix n (fun j => Z (false,j))))) t -
        (∑ j ∈ Finset.range n, wordEnd (Z (false,j))) = y := by
  obtain ⟨i,t,ht,hy⟩ := hy
  have hb := (opposed_departure_band e Z hZ false i t ht).1
  rw [hy,hh] at hb
  have hin : i < n := by
    by_contra hi
    have hm := (tapeHeight_strictMono (placedWidth e false) (fun j => Z (false,j))
      (fun j => slabRecords_pos _ _ (hZ false j))).monotone (Nat.le_of_not_gt hi)
    have hh' : tapeHeight (placedWidth e false) (fun j => Z (false,j)) i < h := by exact_mod_cast hb
    omega
  refine ⟨(∑ j : Fin n with j < (⟨i,hin⟩ : Fin n).rev, (Z (false,j.rev)).1)+t,?_,?_⟩
  · exact concatenateWords_departure (fun j : Fin n => Z (false,j.rev))
      (⟨i,hin⟩ : Fin n).rev t (by simpa using ht)
  · exact (reversePrefix_opposedSite e Z (fun j _ => (hZ false j).2.1) ⟨i,hin⟩ t ht.le).trans hy

lemma concatenateWords_departure_exists {d n : ℕ} (a : Fin n → Word d)
    (t : ℕ) (ht : t < (concatenateWords n a).1) :
    ∃ i : Fin n, ∃ u < (a i).1, t = (∑ j : Fin n with j < i, (a j).1)+u := by
  classical
  induction n with
  | zero => simp [concatenateWords,prefixWord] at ht
  | succ n ih =>
    let b := concatenateWords n (fun j => a j.castSucc)
    change t < b.1+(a (Fin.last n)).1 at ht
    by_cases htb : t < b.1
    · obtain ⟨i,u,hu,he⟩ := ih (fun j => a j.castSucc) htb
      refine ⟨i.castSucc,u,hu,?_⟩
      rw [fin_prefix_sum_castSucc]
      exact he
    · refine ⟨Fin.last n,t-b.1,by omega,?_⟩
      rw [fin_prefix_sum_last,← concatenateWords_length]
      exact (Nat.add_sub_of_le (Nat.le_of_not_gt htb)).symm

lemma concatenateWords_axis_bridge {d n : ℕ} (e : Step d) (a : Fin n → Word d)
    (ha : ∀ i, RegenerationWord (axisDirection e) (a i)) :
    AxisBridgeWord e (∑ i, slabRecords (axisDirection e) (a i)) (concatenateWords n a) := by
  classical
  constructor
  · rw [concatenateWords_end,axisHeight_sum]
    simp only [axisHeight_wordEnd e _ (ha _),Nat.cast_sum]
  · intro t ht
    obtain ⟨i,u,hu,rfl⟩ := concatenateWords_departure_exists a t ht
    rw [concatenateWords_site a (fun i => (ha i).2.1) i u hu.le,axisHeight_add,axisHeight_sum]
    have hw := axisHeight_word_interior e (a i) (ha i) u hu
    have hh : (∑ j : Fin n with j < i, axisHeight e (wordEnd (a j))) =
        ((∑ j : Fin n with j < i, slabRecords (axisDirection e) (a j)) : ℕ) := by
      simp only [axisHeight_wordEnd e _ (ha _),Nat.cast_sum]
    rw [hh]
    constructor
    · exact add_nonneg (Nat.cast_nonneg _) hw.1
    · have hs : (∑ j : Fin n with j < i, slabRecords (axisDirection e) (a j))+
          slabRecords (axisDirection e) (a i) ≤ ∑ j, slabRecords (axisDirection e) (a j) := by
        rw [add_comm,← Finset.sum_insert (f := fun j : Fin n => slabRecords (axisDirection e) (a j))
          (a := i) (s := Finset.univ.filter (fun j : Fin n => j < i)) (by simp)]
        exact Finset.sum_le_sum_of_subset (by intro j hj;simp)
      have hs' : ((∑ j : Fin n with j < i, slabRecords (axisDirection e) (a j)) : ℕ) +
          (slabRecords (axisDirection e) (a i) : ℤ) ≤ ((∑ j, slabRecords (axisDirection e) (a j)) : ℕ) := by exact_mod_cast hs
      omega

lemma wordEnd_slabs_sum {d : ℕ} (v : Fin d → ℝ) (Y : Path d) (h0 : Y 0 = 0) (n : ℕ) :
    (∑ i ∈ Finset.range n, wordEnd (slabs v Y i)) = Y (slabTime v Y n) := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => wordEnd (slabs v Y i)),← concatenateWords_end]
  change wordEnd (concatenateList (tapePrefix n (slabs v Y))) = _
  rw [concatenateList_prefix_slabs v Y h0]
  exact wordPath_prefixWord _ _ le_rfl

lemma opposed_negative_slabs {d : ℕ} (e : Step d) (Z : TwoTape (Word d))
    (Y : Path d) (hY : GoodSlabPath (axisDirection (oppositeStep e)) Y)
    (hZ : ∀ i, Z (true,i) = slabs (axisDirection (oppositeStep e)) Y i)
    (y : Site d) : opposedDeparture e Z true y ↔ ∃ t, Y t-stepVector e = y := by
  constructor
  · rintro ⟨i,j,hj,hij⟩
    refine ⟨slabTime (axisDirection (oppositeStep e)) Y i+j,?_⟩
    simp only [opposedSite,opposedAnchor,↓reduceIte,hZ,wordEnd_slabs_sum _ _ hY.1] at hij
    have hp := slab_word_path (axisDirection (oppositeStep e)) Y i (show j ≤ (slabs (axisDirection (oppositeStep e)) Y i).1 by simpa only [hZ] using hj.le)
    rw [iterated_cutSuffix _ Y hY.1] at hp
    rw [hp] at hij
    convert hij using 1; abel
  · rintro ⟨t,ht⟩
    obtain ⟨i,hi,hi'⟩ := slab_location _ Y hY t
    refine ⟨i,t-slabTime (axisDirection (oppositeStep e)) Y i,?_,?_⟩
    · rw [slabTime_succ] at hi'
      rw [hZ]
      omega
    · simp only [opposedSite,opposedAnchor,↓reduceIte,hZ,wordEnd_slabs_sum _ _ hY.1]
      have hj : t-slabTime (axisDirection (oppositeStep e)) Y i ≤
          (slabs (axisDirection (oppositeStep e)) Y i).1 := by rw [slabTime_succ] at hi';omega
      rw [slab_word_path _ _ _ hj,iterated_cutSuffix _ Y hY.1,Nat.add_sub_of_le hi]
      convert ht using 1; abel

lemma fin_prefix_length_mono {α : Type*} {n : ℕ} (L : α → ℕ) (a : Fin n → α)
    {i j : Fin n} (hij : i ≤ j) :
    (∑ k : Fin n with k < i, L (a k)) ≤ ∑ k : Fin n with k < j, L (a k) := by
  classical
  apply Finset.sum_le_sum_of_subset
  intro k hk
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hk ⊢
  exact hk.trans_le hij

lemma fin_prefix_length_separated {α : Type*} {n : ℕ} (L : α → ℕ) (a : Fin n → α)
    {i j : Fin n} (hij : i < j) :
    (∑ k : Fin n with k < i, L (a k))+L (a i) ≤ ∑ k : Fin n with k < j, L (a k) := by
  classical
  rw [add_comm,← Finset.sum_insert (f := fun k : Fin n => L (a k)) (a := i)
    (s := Finset.univ.filter (fun k : Fin n => k < i)) (by simp)]
  apply Finset.sum_le_sum_of_subset
  intro k hk
  simp only [Finset.mem_insert,Finset.mem_filter,Finset.mem_univ,true_and] at hk ⊢
  rcases hk with rfl | hk
  · exact hij
  · exact hk.trans hij

lemma axisHeight_tapeTotal {d : ℕ} (e : Step d) (Z : ℕ → Word d)
    (hZ : ∀ i, RegenerationWord (axisDirection e) (Z i)) (n : ℕ) :
    axisHeight e (∑ j ∈ Finset.range n, wordEnd (Z j)) =
      (tapeHeight (slabRecords (axisDirection e)) Z n : ℤ) := by
  rw [axisHeight_sum]
  simp only [axisHeight_wordEnd e _ (hZ _),tapeHeight,Nat.cast_sum]

lemma reversePrefix_departure_in_opposed {d n : ℕ} (e : Step d) (Z : TwoTape (Word d))
    (hZ : ∀ i, wordPath (Z (false,i)) 0 = 0) (t : ℕ)
    (ht : t < (concatenateList (reverseTapeList (tapePrefix n (fun j => Z (false,j))))).1) :
    opposedDeparture e Z false
      (wordPath (concatenateList (reverseTapeList (tapePrefix n (fun j => Z (false,j))))) t -
        (∑ j ∈ Finset.range n, wordEnd (Z (false,j)))) := by
  obtain ⟨i,u,hu,rfl⟩ := concatenateWords_departure_exists (fun i : Fin n => Z (false,i.rev)) t ht
  refine ⟨i.rev,u,hu,?_⟩
  simpa only [Fin.rev_rev] using (reversePrefix_opposedSite e Z (fun j _ => hZ j) i.rev u hu.le).symm

lemma reversePrefix_cut_geometry {d : ℕ} (e : Step d) (Z : TwoTape (Word d))
    (hZ : ∀ b i, RegenerationWord (axisDirection (placedAxis e b)) (Z (b,i)))
    (m n : ℕ) (hm : 0 < m) (hmn : m ≤ n) :
    let L := placedWidth e false
    let H := tapeHeight L (fun j => Z (false,j)) n
    let s := tapeHeight L (fun j => Z (false,j)) m
    let a := concatenateList (reverseTapeList (tapePrefix n (fun j => Z (false,j))))
    ∃ t < a.1, AxisBridgeWord e (H-s) (prefixWord t (wordPath a)) ∧
      ∀ u, t ≤ u → u < a.1 → (H-s : ℕ) ≤ axisHeight e (wordPath a u) := by
  classical
  dsimp only
  let i : Fin n := ⟨m-1,by omega⟩
  let a : Fin n → Word d := fun j => Z (false,j.rev)
  let t := ∑ j : Fin n with j < i.rev, (a j).1
  let H := tapeHeight (placedWidth e false) (fun j => Z (false,j)) n
  let s := tapeHeight (placedWidth e false) (fun j => Z (false,j)) m
  have hl : ∀ j, 0 < placedWidth e false (Z (false,j)) := fun j => slabRecords_pos _ _ (hZ false j)
  have hsH : s ≤ H := (tapeHeight_strictMono _ _ hl).monotone hmn
  have htotal := axisHeight_tapeTotal e (fun j => Z (false,j)) (hZ false) n
  have htlen : t < (concatenateWords n a).1 := by
    have hh := concatenateWords_departure a i.rev 0 (by simpa only [a,Fin.rev_rev] using (hZ false i).1)
    simpa only [Nat.add_zero] using hh
  have hend : axisHeight e (wordPath (concatenateWords n a) t) = ((H-s : ℕ) : ℤ) := by
    have hh := reversePrefix_opposedSite e Z (fun j _ => (hZ false j).2.1) i 0 (Nat.zero_le _)
    simp only [Nat.add_zero] at hh
    have he := congrArg (axisHeight e) hh
    rw [sub_eq_add_neg,axisHeight_add,axisHeight_neg,htotal] at he
    have hi : i.val+1 = m := by dsimp [i];omega
    have ho := opposedAnchor_height e Z hZ false i
    simp only [Bool.false_eq_true,↓reduceIte,hi] at ho
    simp only [opposedSite,(hZ false i).2.1,add_zero] at he
    change axisHeight e (wordPath (concatenateWords n a) t)-(H : ℤ) = _ at he
    rw [Nat.cast_sub hsH]
    change -axisHeight e (opposedAnchor e Z false i) = (s : ℤ) at ho
    omega
  have hheight (j : Fin n) (u : ℕ) (hu : u < (a j).1) :
      let y := wordPath (concatenateWords n a) ((∑ q : Fin n with q < j, (a q).1)+u)
      (tapeHeight (placedWidth e false) (fun q => Z (false,q)) j.rev.val : ℤ) < (H : ℤ)-axisHeight e y ∧
      (H : ℤ)-axisHeight e y ≤ (tapeHeight (placedWidth e false) (fun q => Z (false,q)) (j.rev.val+1) : ℤ) := by
    have hh := reversePrefix_opposedSite e Z (fun q _ => (hZ false q).2.1) j.rev u hu.le
    simp only [Fin.rev_rev] at hh
    have he := congrArg (axisHeight e) hh
    rw [sub_eq_add_neg,axisHeight_add,axisHeight_neg,htotal] at he
    have hb := opposed_departure_band e Z hZ false j.rev u hu
    have hsucc : tapeHeight (placedWidth e false) (fun q => Z (false,q)) (j.rev.val+1) =
        tapeHeight (placedWidth e false) (fun q => Z (false,q)) j.rev.val + placedWidth e false (Z (false,j.rev)) := by
      simp only [tapeHeight,Finset.sum_range_succ]
    dsimp only at hb
    rw [← hsucc] at hb
    dsimp only
    change axisHeight e (wordPath (concatenateWords n a) ((∑ q : Fin n with q < j, (a q).1)+u)) - (H : ℤ) = _ at he
    omega
  refine ⟨t,htlen,⟨?_,?_⟩,?_⟩
  · change axisHeight e (wordPath (prefixWord t (wordPath (concatenateWords n a))) t) = _
    rw [wordPath_prefixWord t _ le_rfl]
    exact hend
  · intro u hu
    change u < t at hu
    rw [wordPath_prefixWord t _ hu.le]
    obtain ⟨j,v,hv,rfl⟩ := concatenateWords_departure_exists a u (hu.trans htlen)
    have hji : j < i.rev := by
      by_contra h
      have hh := fin_prefix_length_mono (fun w : Word d => w.1) a (le_of_not_gt h)
      dsimp [t] at hu
      omega
    have hij : m ≤ j.rev.val := by
      have hh := Fin.lt_rev_iff.mp hji
      change m-1 < j.rev.val at hh
      omega
    have hmj := (tapeHeight_strictMono _ _ hl).monotone hij
    have hh := hheight j v hv
    dsimp only at hh
    have hab := concatenateWords_axis_bridge e a (fun q => hZ false q.rev)
    have hnon := (hab.2 _ (by have := concatenateWords_departure a j v hv;exact this)).1
    change 0 ≤ axisHeight e (wordPath (concatenateWords n a) _) ∧
      axisHeight e (wordPath (concatenateWords n a) _) < _
    constructor
    · exact hnon
    · rw [Nat.cast_sub hsH]
      have hmj' : (s : ℤ) ≤ (tapeHeight (placedWidth e false) (fun q => Z (false,q)) j.rev.val : ℤ) := by exact_mod_cast hmj
      omega
  · intro u htu hu
    obtain ⟨j,v,hv,rfl⟩ := concatenateWords_departure_exists a u hu
    have hij : i.rev ≤ j := by
      by_contra h
      have hh := fin_prefix_length_separated (fun w : Word d => w.1) a (lt_of_not_ge h)
      dsimp [t] at htu
      omega
    have hjm : j.rev.val+1 ≤ m := by
      have hh := Fin.rev_le_rev.mpr hij
      simp only [Fin.rev_rev,Fin.le_def] at hh
      change j.rev.val ≤ m-1 at hh
      omega
    have hjs := (tapeHeight_strictMono _ _ hl).monotone hjm
    have hh := hheight j v hv
    dsimp only at hh
    change ((H-s : ℕ) : ℤ) ≤ axisHeight e (wordPath (concatenateWords n a) _)
    rw [Nat.cast_sub hsH]
    have hjs' : (tapeHeight (placedWidth e false) (fun q => Z (false,q)) (j.rev.val+1) : ℤ) ≤ (s : ℤ) := by exact_mod_cast hjs
    omega

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

def finiteLateContact {d : ℕ} (e : Step d) (k r N : ℕ) (a : Word d) (Y : Path d) : Prop :=
  ∃ t τ, t ≤ τ ∧ τ < a.1 ∧ AxisBridgeWord e k (prefixWord t (wordPath a)) ∧
    (∀ j, t ≤ j → j ≤ τ → (k : ℤ) ≤ axisHeight e (wordPath a j) ∧ axisHeight e (wordPath a j) < (N : ℤ)) ∧
    (r : ℤ) ≤ axisHeight e (wordPath a τ) ∧
    (∃ j, Y j+(wordEnd a-stepVector e) = wordPath a τ) ∧
    (∀ i, t ≤ i → i < τ → ∀ j, Y j+(wordEnd a-stepVector e) ≠ wordPath a i)

lemma uncovered_bridge_late {d : ℕ} (e : Step d) (Z : TwoTape (Word d))
    (hZ : ∀ b i, RegenerationWord (axisDirection (placedAxis e b)) (Z (b,i)))
    (Y : Path d) (hY : GoodSlabPath (axisDirection (oppositeStep e)) Y)
    (hZY : ∀ i, Z (true,i) = slabs (axisDirection (oppositeStep e)) Y i)
    (m n low high : ℕ) (hm : 0 < m) (hmn : m ≤ n)
    (hslo : low ≤ tapeHeight (placedWidth e false) (fun j => Z (false,j)) m)
    (hshi : tapeHeight (placedWidth e false) (fun j => Z (false,j)) m < high)
    (hno : ∀ h, low ≤ h → h < high → ¬contactDepth e Z h) :
    let H := tapeHeight (placedWidth e false) (fun j => Z (false,j)) n
    let s := tapeHeight (placedWidth e false) (fun j => Z (false,j)) m
    finiteLateContact e (H-s) (H-low) H
      (concatenateList (reverseTapeList (tapePrefix n (fun j => Z (false,j))))) Y := by
  classical
  let H := tapeHeight (placedWidth e false) (fun j => Z (false,j)) n
  let s := tapeHeight (placedWidth e false) (fun j => Z (false,j)) m
  let a := concatenateList (reverseTapeList (tapePrefix n (fun j => Z (false,j))))
  let D := ∑ j ∈ Finset.range n, wordEnd (Z (false,j))
  have hl : ∀ j, 0 < placedWidth e false (Z (false,j)) := fun j => slabRecords_pos _ _ (hZ false j)
  have hsH : s ≤ H := (tapeHeight_strictMono _ _ hl).monotone hmn
  have hsp : 0 < s := hm.trans_le (le_tapeHeight _ _ hl m)
  have hH : 1 ≤ H := (Nat.succ_le_of_lt hsp).trans hsH
  have hD : wordEnd a = D := by
    rw [concatenateList_end]
    change (∑ j : Fin n, wordEnd (Z (false,j.rev))) = _
    have hh := Equiv.sum_comp Fin.revPerm (fun j : Fin n => wordEnd (Z (false,j)))
    apply (show (∑ j : Fin n, wordEnd (Z (false,j.rev))) = ∑ j : Fin n, wordEnd (Z (false,j)) by
      simpa only [Fin.revPerm_apply] using hh).trans
    rw [Fin.sum_univ_eq_sum_range (fun j => wordEnd (Z (false,j)))]
  have hDh : axisHeight e D = (H : ℤ) := axisHeight_tapeTotal e (fun j => Z (false,j)) (hZ false) n
  have ha : AxisBridgeWord e H a := by
    have hh := concatenateWords_axis_bridge e (fun j : Fin n => Z (false,j.rev)) (fun j => hZ false j.rev)
    have he : (∑ j : Fin n, slabRecords (axisDirection e) (Z (false,j.rev))) = H := by
      have hh := Equiv.sum_comp Fin.revPerm (fun j : Fin n => slabRecords (axisDirection e) (Z (false,j)))
      apply (show (∑ j : Fin n, slabRecords (axisDirection e) (Z (false,j.rev))) =
          ∑ j : Fin n, slabRecords (axisDirection e) (Z (false,j)) by
        simpa only [Fin.revPerm_apply] using hh).trans
      rw [Fin.sum_univ_eq_sum_range (fun j => slabRecords (axisDirection e) (Z (false,j)))]
      rfl
    exact he ▸ hh
  obtain ⟨t,ht,htbridge,htband⟩ := reversePrefix_cut_geometry e Z hZ m n hm hmn
  change t < a.1 at ht
  have hforce := (opposed_forced_contact e Z hZ).1.1
  obtain ⟨v,hv,hvsite⟩ := opposed_positive_in_finite_bridge e Z hZ n 1 hH (-stepVector e) hforce
    (by rw [axisHeight_neg,axisHeight_step_self];norm_num)
  change v < a.1 at hv
  change wordPath a v-D = -stepVector e at hvsite
  have hvheight : axisHeight e (wordPath a v) = (H : ℤ)-1 := by
    have hh := congrArg (axisHeight e) hvsite
    rw [sub_eq_add_neg,axisHeight_add,axisHeight_neg,hDh,axisHeight_neg,axisHeight_step_self] at hh
    omega
  have htv : t ≤ v := by
    by_contra h
    have hvt : v < t := Nat.lt_of_not_ge h
    have hh := (htbridge.2 v hvt).2
    rw [wordPath_prefixWord t _ hvt.le,hvheight,Nat.cast_sub hsH] at hh
    omega
  have hex : ∃ τ, t ≤ τ ∧ τ < a.1 ∧ ∃ j, Y j+(wordEnd a-stepVector e) = wordPath a τ := by
    refine ⟨v,htv,hv,0,?_⟩
    rw [hY.1,zero_add,hD]
    calc
      D-stepVector e = -stepVector e+D := by abel
      _ = wordPath a v := (sub_eq_iff_eq_add.mp hvsite).symm
  let τ := Nat.find hex
  have hτ := Nat.find_spec hex
  have hcontact : contactAt e Z (wordPath a τ-D) := by
    constructor
    · exact reversePrefix_departure_in_opposed e Z (fun i => (hZ false i).2.1) τ hτ.2.1
    · rw [opposed_negative_slabs e Z Y hY hZY]
      obtain ⟨j,hj⟩ := hτ.2.2
      refine ⟨j,?_⟩
      change Y j+(wordEnd a-stepVector e) = wordPath a τ at hj
      rw [hD] at hj
      rw [← hj]
      abel
  have hτband : ((H-s : ℕ) : ℤ) ≤ axisHeight e (wordPath a τ) ∧ axisHeight e (wordPath a τ) < (H : ℤ) :=
    ⟨htband τ hτ.1 hτ.2.1,(ha.2 τ hτ.2.1).2⟩
  let δ : ℤ := (H : ℤ)-axisHeight e (wordPath a τ)
  have hδ0 : 0 < δ := sub_pos.mpr hτband.2
  have hδs : δ ≤ (s : ℤ) := by dsimp [δ];rw [Nat.cast_sub hsH] at hτband;omega
  have hδ : (Int.toNat δ : ℤ) = δ := Int.toNat_of_nonneg hδ0.le
  have hdep : contactDepth e Z (Int.toNat δ) := by
    refine ⟨wordPath a τ-D,hcontact,?_⟩
    rw [sub_eq_add_neg,axisHeight_add,axisHeight_neg,hDh,hδ]
    dsimp [δ]
    omega
  have hsmall : Int.toNat δ < low := by
    by_contra h
    apply hno _ (Nat.le_of_not_gt h) ?_ hdep
    have hh : Int.toNat δ ≤ s := by
      rw [← hδ] at hδs
      exact_mod_cast hδs
    exact hh.trans_lt hshi
  have hr : ((H-low : ℕ) : ℤ) ≤ axisHeight e (wordPath a τ) := by
    rw [Nat.cast_sub (hslo.trans hsH)]
    have hh : δ < (low : ℤ) := by
      rw [← hδ]
      exact_mod_cast hsmall
    dsimp [δ] at hh
    omega
  refine ⟨t,τ,hτ.1,hτ.2.1,htbridge,?_,hr,hτ.2.2,?_⟩
  · intro j htj hjτ
    exact ⟨htband j htj (hjτ.trans_lt hτ.2.1),(ha.2 j (hjτ.trans_lt hτ.2.1)).2⟩
  · intro i hti hiτ j hj
    exact Nat.find_min hex hiτ ⟨hti,hiτ.trans hτ.2.1,j,hj⟩

lemma measurableSet_finiteLateContact {d : ℕ} (e : Step d) (k r N : ℕ) :
    MeasurableSet {p : Word d × Path d | finiteLateContact e k r N p.1 p.2} := by
  classical
  have hword (P : Word d → Prop) : MeasurableSet {p : Word d × Path d | P p.1} :=
    measurable_fst (Set.to_countable _).measurableSet
  have heq (i j : ℕ) : MeasurableSet {p : Word d × Path d |
      p.2 j + (wordEnd p.1-stepVector e) = wordPath p.1 i} := by
    apply measurableSet_eq_fun
    · exact ((measurable_pi_apply j).comp measurable_snd).add
        ((measurable_of_countable (fun a : Word d => wordEnd a-stepVector e)).comp measurable_fst)
    · exact (measurable_of_countable (fun a : Word d => wordPath a i)).comp measurable_fst
  simp only [finiteLateContact,Set.ofPred_exists]
  apply MeasurableSet.iUnion;intro t
  apply MeasurableSet.iUnion;intro τ
  refine (hword (fun _ => t ≤ τ)).inter ((hword (fun a => τ < a.1)).inter
    ((hword (fun a => AxisBridgeWord e k (prefixWord t (wordPath a)))).inter
    ((hword (fun a => ∀ j, t ≤ j → j ≤ τ → (k : ℤ) ≤ axisHeight e (wordPath a j) ∧
      axisHeight e (wordPath a j) < (N : ℤ))).inter
    ((hword (fun a => (r : ℤ) ≤ axisHeight e (wordPath a τ))).inter ?_))))
  apply MeasurableSet.inter
  · change MeasurableSet {p : Word d × Path d | ∃ j, p.2 j+(wordEnd p.1-stepVector e) = wordPath p.1 τ}
    simpa only [Set.ofPred_exists] using MeasurableSet.iUnion (fun j => heq τ j)
  · change MeasurableSet {p : Word d × Path d | ∀ i, t ≤ i → i < τ → ∀ j,
      p.2 j+(wordEnd p.1-stepVector e) ≠ wordPath p.1 i}
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun _ =>
      MeasurableSet.iInter (fun _ => MeasurableSet.iInter (fun j => (heq i j).compl))))

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

def finiteLateEndpointEvent {d ι : ℕ} (e : Step d) (k r N : ℕ) (z : Fin ι → Site d) :
    Set (Word d × Path d) :=
  {p | (∃ q, wordEnd p.1-stepVector e = z q) ∧ finiteLateContact e k r N p.1 p.2}

lemma measurableSet_finiteLateEndpointEvent {d ι : ℕ} (e : Step d) (k r N : ℕ)
    (z : Fin ι → Site d) : MeasurableSet (finiteLateEndpointEvent e k r N z) :=
  (measurable_fst (Set.to_countable {a : Word d | ∃ q, wordEnd a-stepVector e = z q}).measurableSet).inter
    (measurableSet_finiteLateContact e k r N)

lemma finiteLateContact_prefix {d : ℕ} (e : Step d) (k r N n : ℕ)
    (X Y : Path d) (h : finiteLateContact e k r N (prefixWord n X) Y) :
    ∃ t τ, t ≤ τ ∧ AxisBridgeWord e k (prefixWord t X) ∧
      (∀ j, t ≤ j → j ≤ τ → (k : ℤ) ≤ axisHeight e (X j) ∧ axisHeight e (X j) < (N : ℤ)) ∧
      (r : ℤ) ≤ axisHeight e (X τ) ∧
      (∃ j, Y j+(X n-stepVector e) = X τ) ∧
      (∀ i, t ≤ i → i < τ → ∀ j, Y j+(X n-stepVector e) ≠ X i) := by
  obtain ⟨t,τ,htτ,hτ,ha,hband,hr,hc,hb⟩ := h
  change τ < n at hτ
  have hpre : prefixWord t (wordPath (prefixWord n X)) = prefixWord t X := by
    apply (prefixWord_eq_iff t _ _).mpr
    refine ⟨rfl,fun i hi => ?_⟩
    rw [wordPath_prefixWord t X hi,wordPath_prefixWord n X (hi.trans (htτ.trans hτ.le))]
  rw [hpre] at ha
  have hend : wordEnd (prefixWord n X) = X n := wordPath_prefixWord n X le_rfl
  refine ⟨t,τ,htτ,ha,?_,?_,?_,?_⟩
  · intro j htj hjτ
    simpa only [wordPath_prefixWord n X (hjτ.trans hτ.le)] using hband j htj hjτ
  · simpa only [wordPath_prefixWord n X hτ.le] using hr
  · simpa only [hend,wordPath_prefixWord n X hτ.le] using hc
  · intro i hti hiτ j
    simpa only [hend,wordPath_prefixWord n X (hiτ.le.trans hτ.le)] using hb i hti hiτ j

lemma finite_bridge_late_bound {d ι : ℕ} [NeZero ι]
    (μ : Measure (Row d)) [IsProbabilityMeasure μ] (hell : StrictEllipticity μ)
    (e : Step d) (k r N m : ℕ) (hkr : k ≤ r) (hrN : r ≤ N)
    (z : Fin ι → Site d) (hz : ∀ q, axisHeight e (z q) = (N : ℤ)-1)
    (hzi : Function.Injective z)
    (hΔ : axisReachProb μ e (r-k)-axisReachProb μ e (N-k) ≤ ENNReal.ofReal ((1/2 : ℝ)^m)) :
    (((axisReachProb μ e N)⁻¹ • rawBridgeMeasure μ (axisDirection e) N).prod
      (conditioned μ (axisDirection (oppositeStep e)))) (finiteLateEndpointEvent e k r N z) ≤
      (axisReachProb μ e N)⁻¹ *
      (annealed μ 0 (nonBacktracking (axisDirection (oppositeStep e))))⁻¹ *
        ENNReal.ofReal ((24 / posteriorExponent)*Real.log (ι+1)*(m+1)^2*(1/2 : ℝ)^m) := by
  let A := ProbabilityTheory.cond (annealed μ 0) (reachRecord (axisDirection e) N)
  let B := conditioned μ (axisDirection (oppositeStep e))
  have : IsFiniteMeasure B := by dsimp [B,conditioned];infer_instance
  let E : Fin ι → Set (Path d) := fun q =>
    {X | wordEnd (recordWord (axisDirection e) N X)-stepVector e = z q}
  have hE (q) : MeasurableSet (E q) :=
    measurable_recordWord (axisDirection e) N
      (Set.to_countable {a : Word d | wordEnd a-stepVector e = z q}).measurableSet
  have hdis : Pairwise (fun i j => Disjoint (E i) (E j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro X hi hj
    exact hij (hzi (hi.symm.trans hj))
  have hmap : A.map (recordWord (axisDirection e) N) =
      (axisReachProb μ e N)⁻¹ • rawBridgeMeasure μ (axisDirection e) N := by
    dsimp only [A]
    rw [ProbabilityTheory.cond,
      Measure.map_smul,
      ← axisReachProb_eq_record]
    rfl
  rw [← hmap,show (A.map (recordWord (axisDirection e) N)).prod B =
      (A.prod B).map (fun p => (recordWord (axisDirection e) N p.1,p.2)) from by
        simpa only [Measure.map_id,Measure.map_id',Prod.map_def,Function.id_def] using (Measure.map_prod_map A B
          (measurable_recordWord (axisDirection e) N) measurable_id),
    Measure.map_apply (show Measurable (fun p : Path d × Path d => (recordWord (axisDirection e) N p.1,p.2)) from
      ((measurable_recordWord (axisDirection e) N).comp measurable_fst).prodMk measurable_snd)
      (measurableSet_finiteLateEndpointEvent e k r N z)]
  refine (measure_mono_ae ?_).trans (conditioned_bridge_late_bound μ hell e k r N m hkr hrN E hE hdis z hz hΔ)
  have hreach : ∀ᵐ p ∂A.prod B, p.1 ∈ reachRecord (axisDirection e) N :=
    Measure.quasiMeasurePreserving_fst.ae (ProbabilityTheory.ae_cond_mem (measurableSet_reachRecord _ _))
  filter_upwards [hreach] with p hp hf
  obtain ⟨q,hq⟩ := hf.1
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hp
  have hword := recordWord_eq (axisDirection e) N p.1 hn
  have hfinite : finiteLateContact e k r N (prefixWord n p.1) p.2 := hword ▸ hf.2
  obtain ⟨t,τ,htτ,ha,hband,hr,hc,hb⟩ := finiteLateContact_prefix e k r N n p.1 p.2 hfinite
  have heq : p.1 n-stepVector e = z q := by
    change wordEnd (recordWord (axisDirection e) N p.1)-stepVector e = z q at hq
    rw [hword] at hq
    exact (wordPath_prefixWord n p.1 le_rfl ▸ hq)
  refine ⟨q,hq,t,τ,htτ,ha,hband,⟨τ,htτ,le_rfl,hr⟩,?_,?_⟩
  · simpa only [heq] using hc
  · simpa only [heq] using hb

lemma renewalCut_two_mass {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Measure α) [IsProbabilityMeasure ν]
    (L : α → ℕ) (hL : ∀ᵐ a ∂ν, 0 < L a) (H J : ℕ) :
    Measure.infinitePi (fun _ : ℕ => ν) (renewalCut L H ∩ renewalCut L (H+J)) =
      Measure.infinitePi (fun _ : ℕ => ν) (renewalCut L H) *
        Measure.infinitePi (fun _ : ℕ => ν) (renewalCut L J) := by
  classical
  let P := Measure.infinitePi (fun _ : ℕ => ν)
  have hZ := ae_tape_prop ν (fun a => 0 < L a)
    (measurableSet_lt measurable_const (measurable_of_countable L)) hL
  have hf (a : TapeList α) :
      P ({Z | cutList L H Z = a} ∩ (renewalCut L H ∩ renewalCut L (H+J))) =
        P ({Z | cutList L H Z = a} ∩ renewalCut L H) * P (renewalCut L J) := by
    by_cases ha : listHeight L a = H
    · have h1 : P ({Z | cutList L H Z = a} ∩ (renewalCut L H ∩ renewalCut L (H+J))) =
          P {Z | Z ∈ tapeCylinder a ∧ (fun j => Z (a.1+j)) ∈ renewalCut L J} := by
        apply measure_congr
        filter_upwards [hZ] with Z hZ
        apply propext
        constructor
        · rintro ⟨hc,hs,ht⟩
          have hp := ((cutList_atom_iff L H Z hZ a).mp ⟨hs,hc⟩).2
          have hn : tapeHeight L Z a.1 = H := by
            rw [← listHeight_prefix,(tapePrefix_eq_iff _ _ _).mpr ⟨rfl,hp⟩,ha]
          exact ⟨hp,(renewalCut_add_iff L Z hZ hn J).mp ht⟩
        · rintro ⟨hp,ht⟩
          have hc := (cutList_atom_iff L H Z hZ a).mpr ⟨ha,hp⟩
          have hn : tapeHeight L Z a.1 = H := by
            rw [← listHeight_prefix,(tapePrefix_eq_iff _ _ _).mpr ⟨rfl,hp⟩,ha]
          exact ⟨hc.2,hc.1,(renewalCut_add_iff L Z hZ hn J).mpr ht⟩
      have h2 : P ({Z | cutList L H Z = a} ∩ renewalCut L H) = P (tapeCylinder a) := by
        apply measure_congr
        filter_upwards [hZ] with Z hZ
        apply propext
        constructor
        · rintro ⟨hc,hs⟩;exact ((cutList_atom_iff L H Z hZ a).mp ⟨hs,hc⟩).2
        · intro hp;have hc := (cutList_atom_iff L H Z hZ a).mpr ⟨ha,hp⟩;exact ⟨hc.2,hc.1⟩
      rw [h1,h2]
      exact (tapeCylinder_suffix_factorization ν a _ (measurableSet_renewalCut L J)).trans
        (by rw [tapeCylinder_mass])
    · have h0 : P ({Z | cutList L H Z = a} ∩ renewalCut L H) = 0 := by
        apply measure_eq_zero_iff_ae_notMem.mpr
        filter_upwards [hZ] with Z hZ hm
        exact ha ((cutList_atom_iff L H Z hZ a).mp ⟨hm.2,hm.1⟩).1
      rw [h0,zero_mul]
      apply measure_mono_null _ h0
      exact fun _ h => ⟨h.1,h.2.1⟩
  rw [measure_eq_tsum_fibres P (cutList L H) (measurable_cutList L H)
    ((measurableSet_renewalCut L H).inter (measurableSet_renewalCut L (H+J)))]
  simp_rw [hf]
  rw [ENNReal.tsum_mul_right,← measure_eq_tsum_fibres P (cutList L H)
    (measurable_cutList L H) (measurableSet_renewalCut L H)]

lemma axis_two_cuts_lower {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : 0 < annealed μ 0 (nonBacktracking (axisDirection e))) (s N : ℕ) (hsN : s ≤ N) :
    letI := slabLaw_probability μ (axisDirection e) hp
    (annealed μ 0 (nonBacktracking (axisDirection e)))^2 ≤
      Measure.infinitePi (fun _ : ℕ => slabLaw μ (axisDirection e))
        (tapeCut (axisDirection e) s ∩ tapeCut (axisDirection e) N) := by
  let := slabLaw_probability μ (axisDirection e) hp
  have hL : ∀ᵐ a ∂slabLaw μ (axisDirection e), 0 < slabRecords (axisDirection e) a := by
    filter_upwards [ae_slabLaw_regeneration μ hell _ (axisDirection_ne_zero e) hp] with a ha
    exact slabRecords_pos _ _ ha
  have hh := renewalCut_two_mass (slabLaw μ (axisDirection e)) (slabRecords (axisDirection e)) hL s (N-s)
  rw [Nat.add_sub_of_le hsN] at hh
  change (annealed μ 0 (nonBacktracking (axisDirection e)))^2 ≤
    Measure.infinitePi (fun _ : ℕ => slabLaw μ (axisDirection e))
      (renewalCut (slabRecords (axisDirection e)) s ∩ renewalCut (slabRecords (axisDirection e)) N)
  rw [hh,show Measure.infinitePi (fun _ : ℕ => slabLaw μ (axisDirection e))
      (renewalCut (slabRecords (axisDirection e)) s) = axisReachProb μ e s from axis_tapeCut_mass μ hell e hp s,
    show Measure.infinitePi (fun _ : ℕ => slabLaw μ (axisDirection e))
      (renewalCut (slabRecords (axisDirection e)) (N-s)) = axisReachProb μ e (N-s) from axis_tapeCut_mass μ hell e hp (N-s),pow_two]
  exact mul_le_mul' (axisReachProb_lower μ hell e s) (axisReachProb_lower μ hell e (N-s))

lemma reversed_cut_bridge_law {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : 0 < annealed μ 0 (nonBacktracking (axisDirection e))) (N : ℕ) :
    letI := slabLaw_probability μ (axisDirection e) hp
    ((Measure.infinitePi (fun _ : ℕ => slabLaw μ (axisDirection e))).restrict
      (tapeCut (axisDirection e) N)).map
      (fun Z => concatenateList (reverseTapeList (cutList (slabRecords (axisDirection e)) N Z))) =
        rawBridgeMeasure μ (axisDirection e) N := by
  let := slabLaw_probability μ (axisDirection e) hp
  have hL : ∀ᵐ a ∂slabLaw μ (axisDirection e), 0 < slabRecords (axisDirection e) a := by
    filter_upwards [ae_slabLaw_regeneration μ hell _ (axisDirection_ne_zero e) hp] with a ha
    exact slabRecords_pos _ _ ha
  change (((Measure.infinitePi (fun _ : ℕ => slabLaw μ (axisDirection e))).restrict
    (tapeCut (axisDirection e) N)).map
    (concatenateList ∘ (reverseTapeList ∘ cutList (slabRecords (axisDirection e)) N))) = _
  rw [← Measure.map_map (measurable_of_countable concatenateList)
    ((measurable_of_countable reverseTapeList).comp (measurable_cutList _ N)),
    ← Measure.map_map (measurable_of_countable reverseTapeList) (measurable_cutList _ N)]
  change ((bridgeListMeasure (slabLaw μ (axisDirection e)) (slabRecords (axisDirection e)) N).map
    reverseTapeList).map concatenateList = _
  rw [bridgeListMeasure_reverse _ _ hL,
    bridgeListMeasure_concatenate μ hell _ (axisDirection_ne_zero e) hp]

lemma mixed_bridge_late_bound {d ι : ℕ} [NeZero ι]
    (μ : Measure (Row d)) [IsProbabilityMeasure μ] (hell : StrictEllipticity μ)
    (e : Step d) (hp : 0 < annealed μ 0 (nonBacktracking (axisDirection e)))
    (k r N m : ℕ) (hkr : k ≤ r) (hrN : r ≤ N)
    (z : Fin ι → Site d) (hz : ∀ q, axisHeight e (z q) = (N : ℤ)-1)
    (hzi : Function.Injective z)
    (hΔ : axisReachProb μ e (r-k)-axisReachProb μ e (N-k) ≤ ENNReal.ofReal ((1/2 : ℝ)^m)) :
    letI := slabLaw_probability μ (axisDirection e) hp
    ((Measure.infinitePi (fun _ : ℕ => slabLaw μ (axisDirection e))).prod
      (conditioned μ (axisDirection (oppositeStep e))))
        {p | p.1 ∈ tapeCut (axisDirection e) N ∧
          (concatenateList (reverseTapeList (cutList (slabRecords (axisDirection e)) N p.1)),p.2) ∈
            finiteLateEndpointEvent e k r N z} ≤
      (annealed μ 0 (nonBacktracking (axisDirection e)))⁻¹ *
      (annealed μ 0 (nonBacktracking (axisDirection (oppositeStep e))))⁻¹ *
        ENNReal.ofReal ((24 / posteriorExponent)*Real.log (ι+1)*(m+1)^2*(1/2 : ℝ)^m) := by
  let := slabLaw_probability μ (axisDirection e) hp
  let A := Measure.infinitePi (fun _ : ℕ => slabLaw μ (axisDirection e))
  let B := conditioned μ (axisDirection (oppositeStep e))
  have : IsFiniteMeasure B := by dsimp [B,conditioned];infer_instance
  let C := tapeCut (axisDirection e) N
  let F := fun Z => concatenateList (reverseTapeList (cutList (slabRecords (axisDirection e)) N Z))
  have hF : Measurable F := (measurable_of_countable concatenateList).comp
    ((measurable_of_countable reverseTapeList).comp (measurable_cutList _ N))
  let E := finiteLateEndpointEvent e k r N z
  have hE : MeasurableSet E := measurableSet_finiteLateEndpointEvent e k r N z
  have hCu : A C ≤ 1 := prob_le_one
  have hCu0 : A C ≠ 0 := by
    rw [show A C = axisReachProb μ e N from axis_tapeCut_mass μ hell e hp N]
    exact ne_of_gt (hp.trans_le (axisReachProb_lower μ hell e N))
  have hcond : (ProbabilityTheory.cond A C).map F =
      (axisReachProb μ e N)⁻¹ • rawBridgeMeasure μ (axisDirection e) N := by
    rw [ProbabilityTheory.cond,Measure.map_smul]
    rw [show A C = axisReachProb μ e N from axis_tapeCut_mass μ hell e hp N]
    congr 1
    exact reversed_cut_bridge_law μ hell e hp N
  have hmap : ((ProbabilityTheory.cond A C).prod B).map (fun p => (F p.1,p.2)) =
      (((ProbabilityTheory.cond A C).map F).prod B) := by
    simpa only [Measure.map_id',Prod.map_def,Function.id_def] using
      (Measure.map_prod_map (ProbabilityTheory.cond A C) B hF measurable_id).symm
  have hh := finite_bridge_late_bound μ hell e k r N m hkr hrN z hz hzi hΔ
  rw [← hcond,← hmap] at hh
  rw [Measure.map_apply (show Measurable (fun p : (ℕ → Word d) × Path d => (F p.1,p.2)) from
    (hF.comp measurable_fst).prodMk measurable_snd) hE] at hh
  have hsub : A.restrict C ≤ ProbabilityTheory.cond A C := by
    rw [ProbabilityTheory.cond]
    intro S
    rw [Measure.smul_apply,smul_eq_mul]
    exact le_mul_of_one_le_left' (ENNReal.one_le_inv.mpr hCu)
  have hle := Measure.prod_mono hsub (le_refl B)
  have heq : (A.prod B) {p | p.1 ∈ C ∧ (F p.1,p.2) ∈ E} =
      ((A.restrict C).prod B) ((fun p => (F p.1,p.2)) ⁻¹' E) := by
    rw [Measure.restrict_prod_eq_prod_univ C,
      Measure.restrict_apply (hE.preimage (show Measurable (fun p : (ℕ → Word d) × Path d => (F p.1,p.2)) from (hF.comp measurable_fst).prodMk measurable_snd))]
    congr 1
    ext p
    simp only [Set.mem_inter_iff,Set.mem_preimage,Set.mem_prod,Set.mem_univ,and_true]
    exact and_comm
  change (A.prod B) {p | p.1 ∈ C ∧ (F p.1,p.2) ∈ E} ≤ _
  rw [heq]
  refine ((hle _).trans hh).trans ?_
  gcongr
  exact axisReachProb_lower μ hell e N

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

def combineTapes {α : Type*} (p : (ℕ → α) × (ℕ → α)) : TwoTape α :=
  fun i => if i.1 then p.2 i.2 else p.1 i.2

lemma measurable_combineTapes {α : Type*} [MeasurableSpace α] :
    Measurable (combineTapes (α := α)) := by
  apply Measurable.of_eval
  intro i
  cases i with | mk b n =>
    cases b <;> simp only [combineTapes,↓reduceIte,Bool.false_eq_true] <;> fun_prop

lemma combineTapes_law {α : Type*} [MeasurableSpace α]
    (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)] :
    ((Measure.infinitePi (fun _ : ℕ => ν false)).prod
      (Measure.infinitePi (fun _ : ℕ => ν true))).map combineTapes = twoTapeLaw ν := by
  have hpair := (twoExtract_independent ν).map_prod_eq_prod_map_map
    (Measurable.of_eval (fun i => measurable_pi_apply (false,i))).aemeasurable
    (Measurable.of_eval (fun i => measurable_pi_apply (true,i))).aemeasurable
  rw [twoExtract_law,twoExtract_law] at hpair
  rw [← hpair,Measure.map_map measurable_combineTapes
    ((Measurable.of_eval (fun i => measurable_pi_apply (false,i))).prodMk
      (Measurable.of_eval (fun i => measurable_pi_apply (true,i))))]
  have he : combineTapes ∘ (fun Z : TwoTape α => ((fun i => Z (false,i)),(fun i => Z (true,i)))) = id := by
    funext Z
    funext i
    cases i with | mk b n => cases b <;> rfl
  rw [he,Measure.map_id]

noncomputable def mixedTapes {d : ℕ} (e : Step d) (p : (ℕ → Word d) × Path d) : TwoTape (Word d) :=
  combineTapes (p.1,slabs (axisDirection (oppositeStep e)) p.2)

lemma measurable_mixedTapes {d : ℕ} (e : Step d) : Measurable (mixedTapes e) :=
  measurable_combineTapes.comp
    (measurable_fst.prodMk ((measurable_slabs (axisDirection (oppositeStep e))).comp measurable_snd))

lemma mixedTapes_law {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : ∀ b, 0 < annealed μ 0 (nonBacktracking (axisDirection (placedAxis e b)))) :
    letI : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) :=
      fun b => slabLaw_probability μ _ (hp b)
    ((Measure.infinitePi (fun _ : ℕ => slabLaw μ (axisDirection e))).prod
      (conditioned μ (axisDirection (oppositeStep e)))).map (mixedTapes e) =
      twoTapeLaw (fun b => slabLaw μ (axisDirection (placedAxis e b))) := by
  let : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) :=
    fun b => slabLaw_probability μ _ (hp b)
  let := slabLaw_probability μ (axisDirection e) (hp false)
  let := conditioned_probability μ (axisDirection (oppositeStep e)) (hp true)
  have hpminus : 0 < annealed μ 0 (nonBacktracking (axisDirection (oppositeStep e))) := hp true
  change (((Measure.infinitePi (fun _ : ℕ => slabLaw μ (axisDirection e))).prod
      (conditioned μ (axisDirection (oppositeStep e)))).map
    (combineTapes ∘ (fun p => (p.1,slabs (axisDirection (oppositeStep e)) p.2)))) = _
  have hf : Measurable (fun p : (ℕ → Word d) × Path d =>
      (p.1,slabs (axisDirection (oppositeStep e)) p.2)) :=
    measurable_fst.prodMk ((measurable_slabs (axisDirection (oppositeStep e))).comp measurable_snd)
  rw [← Measure.map_map measurable_combineTapes hf]
  have hmap := Measure.map_prod_map
    (Measure.infinitePi (fun _ : ℕ => slabLaw μ (axisDirection e)))
    (conditioned μ (axisDirection (oppositeStep e))) measurable_id
    (measurable_slabs (axisDirection (oppositeStep e)))
  simp only [Measure.map_id',Prod.map_def,Function.id_def] at hmap
  rw [← hmap,slabs_map_eq_infinitePi μ hell _ (axisDirection_ne_zero (oppositeStep e)) hpminus]
  exact combineTapes_law (fun b => slabLaw μ (axisDirection (placedAxis e b)))

lemma measurableSet_contactDepth {d : ℕ} (e : Step d) (h : ℕ) :
    MeasurableSet {Z : TwoTape (Word d) | contactDepth e Z h} := by
  have hsite (b : Bool) (i t : ℕ) : Measurable (fun Z : TwoTape (Word d) => opposedSite e Z b i t) := by
    unfold opposedSite opposedAnchor
    cases b <;> simp only [Bool.false_eq_true,↓reduceIte]
    · exact (Finset.measurable_sum _ (fun j _ => (measurable_of_countable wordEnd).comp
        (measurable_pi_apply (X := fun _ : Bool × ℕ => Word d) (false,j)))).neg.add ((measurable_of_countable (fun a : Word d => wordPath a t)).comp
          (measurable_pi_apply (X := fun _ : Bool × ℕ => Word d) (false,i)))
    · exact (measurable_const.add (Finset.measurable_sum _ (fun j _ =>
        (measurable_of_countable wordEnd).comp (measurable_pi_apply (X := fun _ : Bool × ℕ => Word d) (true,j))))).add
          ((measurable_of_countable (fun a : Word d => wordPath a t)).comp (measurable_pi_apply (X := fun _ : Bool × ℕ => Word d) (true,i)))
  have hdep (b : Bool) (y : Site d) : MeasurableSet {Z : TwoTape (Word d) | opposedDeparture e Z b y} := by
    simp only [opposedDeparture,Set.ofPred_exists]
    apply MeasurableSet.iUnion;intro i
    apply MeasurableSet.iUnion;intro t
    apply MeasurableSet.inter
    · exact (measurable_pi_apply (X := fun _ : Bool × ℕ => Word d) (b,i)) (Set.to_countable {a : Word d | t < a.1}).measurableSet
    · exact (hsite b i t) (measurableSet_singleton y)
  unfold contactDepth contactAt
  simp only [Set.ofPred_exists]
  exact MeasurableSet.iUnion (fun y => ((hdep false y).inter (hdep true y)).inter (MeasurableSet.const _))

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

def coveredDepthBand {d : ℕ} (e : Step d) (low high : ℕ) : Set (TwoTape (Word d)) :=
  {Z | ∃ h, low ≤ h ∧ h < high ∧ contactDepth e Z h}

lemma measurableSet_coveredDepthBand {d : ℕ} (e : Step d) (low high : ℕ) :
    MeasurableSet (coveredDepthBand e low high) := by
  simp only [coveredDepthBand,Set.ofPred_exists]
  exact MeasurableSet.iUnion (fun h => (MeasurableSet.const _).inter
    ((MeasurableSet.const _).inter (measurableSet_contactDepth e h)))

lemma two_cuts_uncovered_mixed {d : ℕ} (e : Step d) (p : (ℕ → Word d) × Path d)
    (hpos : ∀ i, RegenerationWord (axisDirection e) (p.1 i))
    (hneg : GoodSlabPath (axisDirection (oppositeStep e)) p.2)
    (s N low high : ℕ) (hs : 0 < s) (hsN : s ≤ N) (hls : low ≤ s) (hsh : s < high)
    (hcs : p.1 ∈ tapeCut (axisDirection e) s) (hcN : p.1 ∈ tapeCut (axisDirection e) N)
    (hno : mixedTapes e p ∉ coveredDepthBand e low high) :
    finiteLateContact e (N-s) (N-low) N
      (concatenateList (reverseTapeList (cutList (slabRecords (axisDirection e)) N p.1))) p.2 := by
  obtain ⟨m,hm⟩ := hcs
  obtain ⟨n,hn⟩ := hcN
  change tapeHeight (slabRecords (axisDirection e)) p.1 m = s at hm
  change tapeHeight (slabRecords (axisDirection e)) p.1 n = N at hn
  have hL : ∀ i, 0 < slabRecords (axisDirection e) (p.1 i) := fun i => slabRecords_pos _ _ (hpos i)
  have hm0 : 0 < m := by
    by_contra hh
    have hmz : m = 0 := by omega
    rw [hmz] at hm
    change 0 = s at hm
    omega
  have hmn : m ≤ n := (tapeHeight_strictMono _ _ hL).le_iff_le.mp (by rw [hm,hn];exact hsN)
  have hgood : ∀ b i, RegenerationWord (axisDirection (placedAxis e b)) (mixedTapes e p (b,i)) := by
    intro b i
    cases b
    · exact hpos i
    · exact hneg.2 i
  have hh := uncovered_bridge_late e (mixedTapes e p) hgood p.2 hneg (fun _ => rfl)
    m n low high hm0 hmn (by change low ≤ tapeHeight (slabRecords (axisDirection e)) p.1 m;rw [hm];exact hls)
    (by change tapeHeight (slabRecords (axisDirection e)) p.1 m < high;rw [hm];exact hsh)
    (fun h hl hh hc => hno ⟨h,hl,hh,hc⟩)
  change finiteLateContact e (tapeHeight (slabRecords (axisDirection e)) p.1 n-tapeHeight (slabRecords (axisDirection e)) p.1 m)
    (tapeHeight (slabRecords (axisDirection e)) p.1 n-low) (tapeHeight (slabRecords (axisDirection e)) p.1 n)
      (concatenateList (reverseTapeList (tapePrefix n p.1))) p.2 at hh
  rw [hm,hn] at hh
  rw [cutList,cutListIndex_eq _ N p.1 hL hn]
  exact hh

lemma nthCommon_suffix_map {α β : Type*} [Countable α] [Countable β]
    [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β] [MeasurableSingletonClass β]
    (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (r : ℕ) (f : TwoTape α → β) (hf : Measurable f) :
    (twoTapeLaw ν).map (fun Z => (nthCommonList L r Z,f ((commonRestart L)^[r] Z))) =
      (nthCommonLaw ν L r).prod ((twoTapeLaw ν).map f) := by
  apply Measure.ext_of_singleton
  intro a
  have hpair : Measurable (fun Z => (nthCommonList L r Z,f ((commonRestart L)^[r] Z))) :=
    (measurable_nthCommonList L r).prodMk (hf.comp ((measurable_commonRestart L).iterate r))
  have hprod : ((nthCommonLaw ν L r).prod ((twoTapeLaw ν).map f)) {a} =
      nthCommonLaw ν L r {a.1} * ((twoTapeLaw ν).map f) {a.2} := by
    rw [show {a} = {a.1} ×ˢ {a.2} from (Set.singleton_prod_singleton).symm,Measure.prod_prod]
  rw [Measure.map_apply hpair (measurableSet_singleton a),hprod,
    Measure.map_apply hf (measurableSet_singleton _)]
  have heq : (fun Z => (nthCommonList L r Z,f ((commonRestart L)^[r] Z))) ⁻¹' {a} =
      {Z | nthCommonList L r Z = a.1 ∧ (commonRestart L)^[r] Z ∈ f ⁻¹' {a.2}} := by
    rcases a with ⟨a,b⟩
    ext Z;simp only [Set.mem_preimage,Set.mem_singleton_iff,Prod.mk.injEq,Set.mem_ofPred_eq]
  rw [heq]
  exact nthCommon_suffix_factorization ν L hL he r a.1 _ (hf (measurableSet_singleton _))

noncomputable def consecutiveThree {α : Type*} (L : Bool → α → ℕ)
    (r s t : ℕ) (Z : TwoTape α) : ThreeChunk α :=
  (nthCommonList L r Z,nthCommonList L s ((commonRestart L)^[r] Z),
    nthCommonList L t ((commonRestart L)^[r+s] Z))

lemma measurable_consecutiveThree {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (L : Bool → α → ℕ) (r s t : ℕ) :
    Measurable (consecutiveThree L r s t) :=
  (measurable_nthCommonList L r).prodMk
    (((measurable_nthCommonList L s).comp ((measurable_commonRestart L).iterate r)).prodMk
      ((measurable_nthCommonList L t).comp ((measurable_commonRestart L).iterate (r+s))))

lemma consecutiveThree_law {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (r s t : ℕ) :
    (twoTapeLaw ν).map (consecutiveThree L r s t) =
      (nthCommonLaw ν L r).prod ((nthCommonLaw ν L s).prod (nthCommonLaw ν L t)) := by
  have hm := nthCommon_suffix_map ν L hL he s (nthCommonList L t) (measurable_nthCommonList L t)
  have hr := nthCommon_suffix_map ν L hL he r
    (fun Z => (nthCommonList L s Z,nthCommonList L t ((commonRestart L)^[s] Z)))
    ((measurable_nthCommonList L s).prodMk
      ((measurable_nthCommonList L t).comp ((measurable_commonRestart L).iterate s)))
  rw [hm] at hr
  have heq : consecutiveThree L r s t = (fun Z =>
      (nthCommonList L r Z,nthCommonList L s ((commonRestart L)^[r] Z),
        nthCommonList L t ((commonRestart L)^[s] ((commonRestart L)^[r] Z)))) := by
    funext Z
    simp only [consecutiveThree]
    rw [Nat.add_comm r s,Function.iterate_add_apply]
  rw [heq]
  exact hr

noncomputable def consecutiveFour {α : Type*} (L : Bool → α → ℕ)
    (u r s t : ℕ) (Z : TwoTape α) : TwoTapeList α × ThreeChunk α :=
  (nthCommonList L u Z,consecutiveThree L r s t ((commonRestart L)^[u] Z))

lemma measurable_consecutiveFour {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (L : Bool → α → ℕ) (u r s t : ℕ) :
    Measurable (consecutiveFour L u r s t) :=
  (measurable_nthCommonList L u).prodMk
    ((measurable_consecutiveThree L r s t).comp ((measurable_commonRestart L).iterate u))

lemma consecutiveFour_law {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (u r s t : ℕ) :
    (twoTapeLaw ν).map (consecutiveFour L u r s t) =
      (nthCommonLaw ν L u).prod ((nthCommonLaw ν L r).prod
        ((nthCommonLaw ν L s).prod (nthCommonLaw ν L t))) := by
  change (twoTapeLaw ν).map (fun Z => (nthCommonList L u Z,
    consecutiveThree L r s t ((commonRestart L)^[u] Z))) = _
  rw [nthCommon_suffix_map ν L hL he u _ (measurable_consecutiveThree L r s t),
    consecutiveThree_law ν L hL he]

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

abbrev CubeSite (d R : ℕ) := Fin d → Set.Icc (-(R : ℤ)) (R : ℤ)

abbrev AxisCubeSite {d : ℕ} (e : Step d) (N R : ℕ) :=
  {z : CubeSite d R // axisHeight e (fun i => z i) = (N : ℤ)-1}

lemma card_cubeSite (d R : ℕ) : Fintype.card (CubeSite d R) = (2*R+1)^d := by
  simp only [CubeSite,Fintype.card_fun,Fintype.card_fin]
  congr 1
  rw [Fintype.card_ofFinset (Finset.Icc (-(R : ℤ)) R) (by simp),Int.card_Icc]
  omega

lemma card_axisCubeSite_le {d : ℕ} (e : Step d) (N R : ℕ) :
    Fintype.card (AxisCubeSite e N R) ≤ (2*R+1)^d := by
  rw [← card_cubeSite d R]
  exact Fintype.card_subtype_le _

lemma axisCubeSite_nonempty {d : ℕ} (e : Step d) (N R : ℕ) (hN : 0 < N) (hR : N ≤ R) :
    Nonempty (AxisCubeSite e N R) := by
  let z : Site d := (N-1 : ℕ) • stepVector e
  have hbd (i : Fin d) : z i ∈ Set.Icc (-(R : ℤ)) (R : ℤ) := by
    dsimp [z,stepVector]
    simp only [Int.natCast_sub hN]
    split_ifs <;> constructor <;> omega
  exact ⟨⟨(fun i => ⟨z i,hbd i⟩),by
    change axisHeight e z = _
    dsimp [z,axisHeight,stepVector]
    cases e.2 <;> simp only [Bool.false_eq_true,↓reduceIte] <;>
      omega⟩⟩

noncomputable def axisCubeEnumeration {d : ℕ} (e : Step d) (N R : ℕ) :
    Fin (Fintype.card (AxisCubeSite e N R)) → Site d :=
  fun q i => ((Fintype.equivFin (AxisCubeSite e N R)).symm q).val i

lemma axisCubeEnumeration_injective {d : ℕ} (e : Step d) (N R : ℕ) :
    Function.Injective (axisCubeEnumeration e N R) := by
  intro q r h
  apply (Fintype.equivFin (AxisCubeSite e N R)).symm.injective
  apply Subtype.ext
  funext i
  exact Subtype.ext (congr_fun h i)

lemma axisCubeEnumeration_height {d : ℕ} (e : Step d) (N R : ℕ)
    (q : Fin (Fintype.card (AxisCubeSite e N R))) :
    axisHeight e (axisCubeEnumeration e N R q) = (N : ℤ)-1 :=
  ((Fintype.equivFin (AxisCubeSite e N R)).symm q).property

lemma axisCubeEnumeration_surjective {d : ℕ} (e : Step d) (N R : ℕ) (z : Site d)
    (hz : axisHeight e z = (N : ℤ)-1) (hbd : ∀ i, |z i| ≤ (R : ℤ)) :
    ∃ q, axisCubeEnumeration e N R q = z := by
  let a : AxisCubeSite e N R := ⟨fun i => ⟨z i,abs_le.mp (hbd i)⟩,hz⟩
  refine ⟨Fintype.equivFin _ a,?_⟩
  change (fun i => (((Fintype.equivFin (AxisCubeSite e N R)).symm
    ((Fintype.equivFin (AxisCubeSite e N R)) a)).val i : ℤ)) = z
  rw [Equiv.symm_apply_apply]

lemma abs_wordEnd_coord_le_radius {d : ℕ} (a : Word d) (h0 : wordPath a 0 = 0) (i : Fin d) :
    |(wordEnd a i : ℝ)| ≤ slabRadius a := by
  have hh := norm_wordPath_le_radius a (j := a.1) le_rfl
  rw [h0,sub_zero] at hh
  have hc : |(wordEnd a i : ℝ)| ≤ ‖euclideanSite (wordPath a a.1)‖ := by
    simpa [euclideanSite,wordEnd] using PiLp.norm_apply_le (euclideanSite (wordPath a a.1)) i
  exact hc.trans hh

lemma reversePrefix_endpoint_coord {d n : ℕ} (Z : ℕ → Word d)
    (h0 : ∀ j < n, wordPath (Z j) 0 = 0) (i : Fin d) :
    |(wordEnd (concatenateList (reverseTapeList (tapePrefix n Z))) i : ℝ)| ≤
      ∑ j ∈ Finset.range n, slabRadius (Z j) := by
  have he : wordEnd (concatenateList (reverseTapeList (tapePrefix n Z))) =
      ∑ j ∈ Finset.range n, wordEnd (Z j) := by
    change wordEnd (concatenateWords n (fun j : Fin n => Z j.rev)) = _
    rw [concatenateWords_end]
    exact (Equiv.sum_comp Fin.revPerm (fun j : Fin n => wordEnd (Z j))).trans
      (Fin.sum_univ_eq_sum_range (fun j => wordEnd (Z j)) n)
  rw [he]
  simp only [Finset.sum_apply,Int.cast_sum]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum
    (fun j hj => abs_wordEnd_coord_le_radius _ (h0 j (Finset.mem_range.mp hj)) i))

lemma cutIndex_le_height {α : Type*} (L : α → ℕ) (Z : ℕ → α)
    (hL : ∀ i, 0 < L (Z i)) (N : ℕ) (hC : Z ∈ renewalCut L N) :
    cutListIndex L N Z ≤ N := by
  have he := cutListIndex_spec L N Z hL hC
  have hh := (tapeHeight_strictMono L Z hL).id_le (cutListIndex L N Z)
  rwa [he] at hh

lemma reversed_cut_endpoint_radius {d : ℕ} (e : Step d) (Z : ℕ → Word d)
    (hZ : ∀ i, RegenerationWord (axisDirection e) (Z i)) (N : ℕ)
    (hC : Z ∈ tapeCut (axisDirection e) N) (i : Fin d) :
    |((wordEnd (concatenateList (reverseTapeList (cutList (slabRecords (axisDirection e)) N Z))) i : ℤ) : ℝ)| ≤
      ∑ j ∈ Finset.range N, slabRadius (Z j) := by
  have hh := reversePrefix_endpoint_coord Z (n := cutListIndex (slabRecords (axisDirection e)) N Z)
    (fun j _ => (hZ j).2.1) i
  refine hh.trans ?_
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono (cutIndex_le_height _ Z (fun j => slabRecords_pos _ _ (hZ j)) N hC)
  · intro j _ _
    exact slabRadius_nonneg _

lemma commonDepth_add {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α) (r s : ℕ) :
    commonDepth L Z (r+s) = commonDepth L Z r +
      commonDepth L ((commonRestart L)^[r] Z) s := by
  rw [commonDepth,Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.add_comm r i,Function.iterate_add_apply]

lemma commonDepth_strictMono {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    (he : ∀ r, ∃ H, 0 < H ∧ ((commonRestart L)^[r] Z) ∈ commonCut L H) :
    StrictMono (commonDepth L Z) := by
  apply strictMono_nat_of_lt_succ
  intro r
  rw [commonDepth_succ]
  have hh := (firstCommonWidth_spec L _ (he r)).1
  omega

lemma common_iterates_shift {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i)))
    (he : ∀ r, ∃ H, 0 < H ∧ ((commonRestart L)^[r] Z) ∈ commonCut L H) (r : ℕ) :
    (commonRestart L)^[r] Z = twoShift (fun b => (nthCommonList L r Z b).1) Z := by
  rw [← (commonDepth_spec L Z hZ he r).2.1]
  rfl

lemma nthCommonList_data {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i)))
    (he : ∀ r, ∃ H, 0 < H ∧ ((commonRestart L)^[r] Z) ∈ commonCut L H) (r : ℕ) :
    (∀ b, listHeight (L b) (nthCommonList L r Z b) = commonDepth L Z r) ∧
      Z ∈ twoCylinder (nthCommonList L r Z) := by
  exact (commonCutList_atom_iff L _ Z hZ _).mp ⟨(commonDepth_spec L Z hZ he r).1,rfl⟩

lemma nthCommonList_append {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i)))
    (he : ∀ r, ∃ H, 0 < H ∧ ((commonRestart L)^[r] Z) ∈ commonCut L H) (r s : ℕ) (b : Bool) :
    nthCommonList L (r+s) Z b = appendTapeList (nthCommonList L r Z b)
      (nthCommonList L s ((commonRestart L)^[r] Z) b) := by
  have hr := nthCommonList_data L Z hZ he r
  let Y := (commonRestart L)^[r] Z
  have hYZ : ∀ b i, 0 < L b (Y (b,i)) := by
    dsimp only [Y]
    rw [common_iterates_shift L Z hZ he r]
    exact fun b i => hZ b _
  have hYe : ∀ s, ∃ H, 0 < H ∧ ((commonRestart L)^[s] Y) ∈ commonCut L H := by
    intro s
    dsimp only [Y]
    rw [← Function.iterate_add_apply]
    exact he (s+r)
  have hs := nthCommonList_data L Y hYZ hYe s
  have hshift : Y = twoShift (fun b => (nthCommonList L r Z b).1) Z := common_iterates_shift L Z hZ he r
  have hl : listHeight (L b) (appendTapeList (nthCommonList L r Z b) (nthCommonList L s Y b)) =
      commonDepth L Z (r+s) := by
    rw [listHeight_append,hr.1 b,hs.1 b,commonDepth_add]
  have hc : (fun i => Z (b,i)) ∈ tapeCylinder
      (appendTapeList (nthCommonList L r Z b) (nthCommonList L s Y b)) := by
    rw [tapeCylinder_append]
    refine ⟨hr.2 b,?_⟩
    intro i
    exact (congr_fun hshift (b,i)).symm.trans (hs.2 b i)
  exact ((cutList_atom_iff (L b) _ _ (hZ b) _).mpr ⟨hl,hc⟩).2

lemma appendTapeList_prefix {α : Type*} (Z : ℕ → α) (m n : ℕ) :
    appendTapeList (tapePrefix m Z) (tapePrefix n (fun i => Z (m+i))) = tapePrefix (m+n) Z := by
  change (⟨m+n,Fin.append (fun i : Fin m => Z i) (fun i : Fin n => Z (m+i))⟩ : TapeList α) =
    ⟨m+n,fun i => Z i⟩
  congr 1
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

lemma listTotal_append {α G : Type*} [AddCommMonoid G] (D : α → G) (a b : TapeList α) :
    listTotal D (appendTapeList a b) = listTotal D a + listTotal D b := by
  change (∑ i : Fin (a.1+b.1), D (Fin.append a.2 b.2 i)) = _
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left,Fin.append_right]
  rfl

lemma listTotal_reverse {α G : Type*} [AddCommMonoid G] (D : α → G) (a : TapeList α) :
    listTotal D (reverseTapeList a) = listTotal D a := by
  exact Equiv.sum_comp Fin.revPerm (fun i => D (a.2 i))

lemma iid_lintegral_sum {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] (f : α → ℝ≥0∞) (hf : Measurable f) (n : ℕ) :
    (∫⁻ Z, ∑ j ∈ Finset.range n, f (Z j) ∂Measure.infinitePi (fun _ : ℕ => ν)) =
      (n : ℝ≥0∞) * ∫⁻ a, f a ∂ν := by
  rw [lintegral_finsetSum (Finset.range n) (f := fun (j : ℕ) (Z : ℕ → α) => f (Z j)) (fun j _ => hf.comp (measurable_pi_apply j))]
  have he (j : ℕ) : (∫⁻ Z, f (Z j) ∂Measure.infinitePi (fun _ : ℕ => ν)) = ∫⁻ a, f a ∂ν := by
    rw [← lintegral_map' hf.aemeasurable (measurable_pi_apply j).aemeasurable,Measure.infinitePi_map_eval]
  simp only [he,Finset.sum_const,Finset.card_range,nsmul_eq_mul]

lemma iid_radius_large {d : ℕ} (ν : Measure (Word d)) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 0 < n) :
    Measure.infinitePi (fun _ : ℕ => ν)
      {Z | (n : ℝ)^2 ≤ ∑ j ∈ Finset.range n, slabRadius (Z j)} ≤
      (∫⁻ a, ENNReal.ofReal (slabRadius a) ∂ν) / (n : ℝ≥0∞) := by
  let f : (ℕ → Word d) → ℝ≥0∞ := fun Z => ∑ j ∈ Finset.range n, ENNReal.ofReal (slabRadius (Z j))
  have hf : Measurable f := Finset.measurable_sum _ (fun j _ =>
    (measurable_of_countable (fun a : Word d => ENNReal.ofReal (slabRadius a))).comp (measurable_pi_apply j))
  have hne : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast Nat.ne_zero_of_lt hn
  have htop : (n : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top n
  have hset : {Z | (n : ℝ)^2 ≤ ∑ j ∈ Finset.range n, slabRadius (Z j)} =
      {Z | (n : ℝ≥0∞)^2 ≤ f Z} := by
    ext Z
    dsimp only [Set.mem_ofPred_eq,f]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => slabRadius_nonneg (Z j))]
    have he : ENNReal.ofReal ((n : ℝ)^2) = (n : ℝ≥0∞)^2 := by
      rw [ENNReal.ofReal_pow (Nat.cast_nonneg n),ENNReal.ofReal_natCast]
    rw [← he,ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg (fun j _ => slabRadius_nonneg (Z j)))]
  rw [hset]
  have hh := meas_ge_le_lintegral_div (μ := Measure.infinitePi (fun _ : ℕ => ν)) hf.aemeasurable (pow_ne_zero _ hne) (by finiteness : (n : ℝ≥0∞)^2 ≠ ∞)
  refine hh.trans_eq ?_
  change ((∫⁻ Z, ∑ j ∈ Finset.range n, ENNReal.ofReal (slabRadius (Z j)) ∂Measure.infinitePi (fun _ : ℕ => ν)) / (n : ℝ≥0∞)^2) = _
  rw [iid_lintegral_sum ν (fun a => ENNReal.ofReal (slabRadius a)) (measurable_of_countable _) n,pow_two,ENNReal.mul_div_mul_left _ _ hne htop]

lemma tapeList_ext {α : Type*} {a b : TapeList α} (hl : a.1 = b.1)
    (h : ∀ i hi hj, a.2 ⟨i,hi⟩ = b.2 ⟨i,hj⟩) : a = b := by
  rcases a with ⟨m,a⟩
  rcases b with ⟨n,b⟩
  dsimp only at hl
  subst n
  exact congrArg (Sigma.mk m) (funext (fun i => h i i.isLt i.isLt))

lemma reverseTapeList_append {α : Type*} (a b : TapeList α) :
    reverseTapeList (appendTapeList a b) = appendTapeList (reverseTapeList b) (reverseTapeList a) := by
  apply tapeList_ext (Nat.add_comm a.1 b.1)
  intro i hi hj
  exact Fin.append_rev a.2 b.2 ⟨i,hi⟩

lemma slice_sum {G : Type*} [AddCommGroup G] (f : ℕ → G) (a n : ℕ) :
    (∑ j ∈ Finset.range n, f (a+j)) =
      (∑ j ∈ Finset.range (a+n), f j) - (∑ j ∈ Finset.range a, f j) := by
  rw [Finset.sum_range_add]
  abel

lemma reverseSlice_departure {d : ℕ} (Z : ℕ → Word d) (a n i t : ℕ)
    (h0 : ∀ j, wordPath (Z j) 0 = 0) (hai : a ≤ i) (hin : i < a+n) (ht : t < (Z i).1) :
    ∃ u < (concatenateList (reverseTapeList (tapePrefix n (fun j => Z (a+j))))).1,
      wordPath (concatenateList (reverseTapeList (tapePrefix n (fun j => Z (a+j))))) u =
        (∑ j ∈ Finset.range (a+n), wordEnd (Z j)) -
        (∑ j ∈ Finset.range (i+1), wordEnd (Z j)) + wordPath (Z i) t := by
  let q : Fin n := ⟨i-a,by omega⟩
  have hq : a+q.val = i := by dsimp [q];omega
  let u := (∑ j : Fin n with j < q.rev, (Z (a+j.rev)).1)+t
  have hu := concatenateWords_departure (fun j : Fin n => Z (a+j.rev)) q.rev t
    (by simpa only [Fin.rev_rev,hq] using ht)
  refine ⟨u,hu,?_⟩
  have he := reversePrefix_site (fun j => Z (a+j)) (fun j _ => h0 _) q t
    (by simpa only [hq] using ht.le)
  change wordPath (concatenateList (reverseTapeList (tapePrefix n (fun j => Z (a+j))))) u = _ at he
  rw [he,slice_sum (fun j => wordEnd (Z j)) a n,slice_sum (fun j => wordEnd (Z j)) a (q.val+1),hq]
  have hh : a+(q.val+1) = i+1 := by omega
  rw [hh]
  abel

lemma forwardSlice_departure {d : ℕ} (Z : ℕ → Word d) (a n i t : ℕ)
    (h0 : ∀ j, wordPath (Z j) 0 = 0) (hai : a ≤ i) (hin : i < a+n) (ht : t < (Z i).1) :
    ∃ u < (concatenateList (tapePrefix n (fun j => Z (a+j)))).1,
      wordPath (concatenateList (tapePrefix n (fun j => Z (a+j)))) u =
        (∑ j ∈ Finset.range i, wordEnd (Z j)) -
        (∑ j ∈ Finset.range a, wordEnd (Z j)) + wordPath (Z i) t := by
  let q : Fin n := ⟨i-a,by omega⟩
  have hq : a+q.val = i := by dsimp [q];omega
  let u := (∑ j : Fin n with j < q, (Z (a+j)).1)+t
  have hu := concatenateWords_departure (fun j : Fin n => Z (a+j)) q t (by simpa only [hq] using ht)
  refine ⟨u,hu,?_⟩
  have he := concatenateWords_site (fun j : Fin n => Z (a+j)) (fun j => h0 _) q t
    (by simpa only [hq] using ht.le)
  change wordPath (concatenateList (tapePrefix n (fun j => Z (a+j)))) u = _ at he
  rw [he,hq]
  have hsum : (∑ j : Fin n with j < q, wordEnd (Z (a+j))) =
      ∑ j ∈ Finset.range q.val, wordEnd (Z (a+j)) :=
    fin_prefix_sum_range (fun j => wordEnd (Z (a+j))) q.val (by omega)
  rw [hsum,slice_sum (fun j => wordEnd (Z j)) a q.val,hq]

lemma common_iterate_positive {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i)))
    (he : ∀ r, ∃ H, 0 < H ∧ ((commonRestart L)^[r] Z) ∈ commonCut L H) (r : ℕ) :
    ∀ b i, 0 < L b (((commonRestart L)^[r] Z) (b,i)) := by
  rw [common_iterates_shift L Z hZ he r]
  exact fun b i => hZ b _

lemma common_iterate_exists {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    (he : ∀ r, ∃ H, 0 < H ∧ ((commonRestart L)^[r] Z) ∈ commonCut L H) (r : ℕ) :
    ∀ s, ∃ H, 0 < H ∧ ((commonRestart L)^[s] ((commonRestart L)^[r] Z)) ∈ commonCut L H := by
  intro s
  rw [← Function.iterate_add_apply]
  exact he (s+r)

lemma nthCommon_length_add {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i)))
    (he : ∀ r, ∃ H, 0 < H ∧ ((commonRestart L)^[r] Z) ∈ commonCut L H) (r s : ℕ) (b : Bool) :
    (nthCommonList L (r+s) Z b).1 = (nthCommonList L r Z b).1 +
      (nthCommonList L s ((commonRestart L)^[r] Z) b).1 := by
  rw [nthCommonList_append L Z hZ he r s b]
  rfl

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

lemma nthCommon_shift_prefix {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i)))
    (he : ∀ r, ∃ H, 0 < H ∧ ((commonRestart L)^[r] Z) ∈ commonCut L H) (r s : ℕ) (b : Bool) :
    nthCommonList L s ((commonRestart L)^[r] Z) b =
      tapePrefix (nthCommonList L s ((commonRestart L)^[r] Z) b).1
        (fun j => Z (b,(nthCommonList L r Z b).1+j)) := by
  symm
  apply (tapePrefix_eq_iff _ _ _).mpr
  refine ⟨rfl,?_⟩
  have hh := (nthCommonList_data L _ (common_iterate_positive L Z hZ he r)
    (common_iterate_exists L Z he r) s).2 b
  have hz := common_iterates_shift L Z hZ he r
  intro i
  exact (congr_fun hz (b,i)).symm.trans (hh i)

lemma consecutiveThree_joins {d : ℕ} (L : Bool → Word d → ℕ) (Z : TwoTape (Word d))
    (hZ : ∀ b i, 0 < L b (Z (b,i)))
    (he : ∀ r, ∃ H, 0 < H ∧ ((commonRestart L)^[r] Z) ∈ commonCut L H) (r s t : ℕ) :
    positiveJoin (splitThree (consecutiveThree L r s t Z)).1 =
      concatenateList (reverseTapeList (nthCommonList L (s+t) ((commonRestart L)^[r] Z) false)) ∧
    negativeJoin (splitThree (consecutiveThree L r s t Z)).2 =
      concatenateList (nthCommonList L (r+s) Z true) := by
  have hs := nthCommonList_append L ((commonRestart L)^[r] Z)
    (common_iterate_positive L Z hZ he r) (common_iterate_exists L Z he r) s t false
  have hit : (commonRestart L)^[s] ((commonRestart L)^[r] Z) = (commonRestart L)^[r+s] Z := by
    rw [Nat.add_comm r s,Function.iterate_add_apply]
  rw [hit] at hs
  constructor
  · dsimp only [positiveJoin,splitThree,consecutiveThree]
    rw [← reverseTapeList_append,← hs]
  · dsimp only [negativeJoin,splitThree,consecutiveThree]
    rw [← nthCommonList_append L Z hZ he r s true]

lemma signedTotal_consecutiveThree {α G : Type*} [AddCommGroup G]
    (L : Bool → α → ℕ) (D : α → G) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i)))
    (he : ∀ r, ∃ H, 0 < H ∧ ((commonRestart L)^[r] Z) ∈ commonCut L H) (r s t : ℕ) :
    signedTotal D (splitThree (consecutiveThree L r s t Z)).1 =
      listTotal D (nthCommonList L (r+s+t) Z false) := by
  rw [nthCommonList_append L Z hZ he (r+s) t false,listTotal_append,
    nthCommonList_append L Z hZ he r s false,listTotal_append]
  simp only [signedTotal,splitThree,consecutiveThree]
  abel

lemma consecutiveFour_total {α G : Type*} [AddCommGroup G]
    (L : Bool → α → ℕ) (D : Bool → α → G) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i)))
    (he : ∀ r, ∃ H, 0 < H ∧ ((commonRestart L)^[r] Z) ∈ commonCut L H) (u r s t : ℕ) :
    pairTotal D (consecutiveFour L u r s t Z).1 +
      signedTotal (D false) (splitThree (consecutiveFour L u r s t Z).2).1 =
      listTotal (D false) (nthCommonList L (u+(r+s+t)) Z false) +
      listTotal (D true) (nthCommonList L u Z true) := by
  dsimp only [consecutiveFour]
  rw [signedTotal_consecutiveThree L (D false) _ (common_iterate_positive L Z hZ he u)
    (common_iterate_exists L Z he u),nthCommonList_append L Z hZ he u (r+s+t) false,
    listTotal_append,pairTotal]
  ac_rfl

lemma nthCommon_index_height {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i)))
    (he : ∀ r, ∃ H, 0 < H ∧ ((commonRestart L)^[r] Z) ∈ commonCut L H) (r : ℕ) (b : Bool) :
    tapeHeight (L b) (fun j => Z (b,j)) (nthCommonList L r Z b).1 = commonDepth L Z r :=
  cutListIndex_spec (L b) (commonDepth L Z r) _ (hZ b) ((commonDepth_spec L Z hZ he r).1 b)

lemma listTotal_nthCommon {α G : Type*} [AddCommGroup G]
    (L : Bool → α → ℕ) (D : α → G) (Z : TwoTape α) (r : ℕ) (b : Bool) :
    listTotal D (nthCommonList L r Z b) =
      ∑ j ∈ Finset.range (nthCommonList L r Z b).1, D (Z (b,j)) := by
  exact listTotal_prefix D _ _

lemma departure_between_common {d : ℕ} (e : Step d) (Z : TwoTape (Word d))
    (hZ : ∀ b i, RegenerationWord (axisDirection (placedAxis e b)) (Z (b,i)))
    (he : ∀ r, ∃ H, 0 < H ∧ ((commonRestart (placedWidth e))^[r] Z) ∈ commonCut (placedWidth e) H)
    (a c h : ℕ) (ha : commonDepth (placedWidth e) Z a < h)
    (hc : h ≤ commonDepth (placedWidth e) Z c)
    (b : Bool) (i t : ℕ) (ht : t < (Z (b,i)).1)
    (hd : -axisHeight e (opposedSite e Z b i t) = (h : ℤ)) :
    (nthCommonList (placedWidth e) a Z b).1 ≤ i ∧
      i < (nthCommonList (placedWidth e) c Z b).1 := by
  have hpos : ∀ b i, 0 < placedWidth e b (Z (b,i)) := fun b i => slabRecords_pos _ _ (hZ b i)
  have hs := opposed_departure_band e Z hZ b i t ht
  dsimp only at hs
  rw [hd] at hs
  have hm := (tapeHeight_strictMono (placedWidth e b) (fun j => Z (b,j)) (hpos b)).monotone
  have hea := nthCommon_index_height (placedWidth e) Z hpos he a b
  have hec := nthCommon_index_height (placedWidth e) Z hpos he c b
  have hi : tapeHeight (placedWidth e b) (fun j => Z (b,j)) (i+1) =
      tapeHeight (placedWidth e b) (fun j => Z (b,j)) i + placedWidth e b (Z (b,i)) := by
    exact Finset.sum_range_succ _ _
  constructor
  · by_contra hn
    have hh := hm (show i+1 ≤ (nthCommonList (placedWidth e) a Z b).1 by omega)
    rw [hea,hi] at hh
    omega
  · by_contra hn
    have hh := hm (show (nthCommonList (placedWidth e) c Z b).1 ≤ i by omega)
    rw [hec] at hh
    omega

lemma commonBand_experiment_contact {d : ℕ} (e : Step d) (Z : TwoTape (Word d))
    (hZ : ∀ b i, RegenerationWord (axisDirection (placedAxis e b)) (Z (b,i)))
    (he : ∀ r, ∃ H, 0 < H ∧ ((commonRestart (placedWidth e))^[r] Z) ∈ commonCut (placedWidth e) H)
    (u r s t h : ℕ) (ha : commonDepth (placedWidth e) Z (u+r) < h)
    (hc : h ≤ commonDepth (placedWidth e) Z (u+r+s)) (hcon : contactDepth e Z h) :
    let p := consecutiveFour (placedWidth e) u r s t Z
    ((threeHeight (placedWidth e) p.2,pairTotal (fun _ => wordEnd) p.1+
      signedTotal wordEnd (splitThree p.2).1),splitThree p.2) ∈ experimentContact e := by
  let L := placedWidth e
  have hpos : ∀ b i, 0 < L b (Z (b,i)) := fun b i => slabRecords_pos _ _ (hZ b i)
  have hmono := (commonDepth_strictMono L Z he).monotone
  obtain ⟨y,⟨⟨i,ti,hti,hyi⟩,⟨j,tj,htj,hyj⟩⟩,hy⟩ := hcon
  have hi := departure_between_common e Z hZ he (u+r) (u+r+(s+t)) h ha
    (hc.trans (hmono (by omega))) false i ti hti (by rwa [hyi])
  have hj := departure_between_common e Z hZ he u (u+(r+s)) h
    ((hmono (by omega : u ≤ u+r)).trans_lt ha) (by simpa [Nat.add_assoc] using hc)
    true j tj htj (by rwa [hyj])
  let Y := (commonRestart L)^[u] Z
  have hYY : (commonRestart L)^[r] Y = (commonRestart L)^[u+r] Z := by
    dsimp [Y]
    rw [Nat.add_comm u r,Function.iterate_add_apply]
  have hjoin := consecutiveThree_joins L Y (common_iterate_positive L Z hpos he u)
    (common_iterate_exists L Z he u) r s t
  rw [hYY] at hjoin
  have hip := reverseSlice_departure (fun j => Z (false,j))
    (nthCommonList L (u+r) Z false).1
    (nthCommonList L (s+t) ((commonRestart L)^[u+r] Z) false).1 i ti
    (fun j => (hZ false j).2.1) hi.1
    (by rw [← nthCommon_length_add L Z hpos he (u+r) (s+t) false];exact hi.2) hti
  have hjp := forwardSlice_departure (fun j => Z (true,j))
    (nthCommonList L u Z true).1 (nthCommonList L (r+s) Y true).1 j tj
    (fun j => (hZ true j).2.1) hj.1
    (by rw [← nthCommon_length_add L Z hpos he u (r+s) true];exact hj.2) htj
  rw [← nthCommon_shift_prefix L Z hpos he (u+r) (s+t) false,
    ← nthCommon_length_add L Z hpos he (u+r) (s+t) false] at hip
  rw [← nthCommon_shift_prefix L Z hpos he u (r+s) true] at hjp
  obtain ⟨v,hv,hev⟩ := hip
  obtain ⟨w,hw,hew⟩ := hjp
  dsimp only
  change ∃ v < (positiveJoin (splitThree (consecutiveThree L r s t Y)).1).1,
    ∃ w < (negativeJoin (splitThree (consecutiveThree L r s t Y)).2).1,
      wordPath (positiveJoin (splitThree (consecutiveThree L r s t Y)).1) v =
      wordPath (negativeJoin (splitThree (consecutiveThree L r s t Y)).2) w +
        (pairTotal (fun _ => wordEnd) (nthCommonList L u Z) +
          signedTotal wordEnd (splitThree (consecutiveThree L r s t Y)).1-stepVector e)
  rw [hjoin.1,hjoin.2]
  refine ⟨v,hv,w,hw,?_⟩
  have htot := consecutiveFour_total L (fun _ => wordEnd) Z hpos he u r s t
  change pairTotal (fun _ => wordEnd) (nthCommonList L u Z) +
      signedTotal wordEnd (splitThree (consecutiveThree L r s t Y)).1 = _ at htot
  rw [htot,listTotal_nthCommon,listTotal_nthCommon,hev,hew]
  have hadd : u+r+(s+t) = u+(r+s+t) := by omega
  rw [hadd]
  simp only [opposedSite,opposedAnchor,Bool.false_eq_true,↓reduceIte] at hyi hyj
  have heq := hyi.trans hyj.symm
  abel_nf at heq ⊢
  simpa only [add_assoc] using congrArg (fun x => x + ∑ j ∈ Finset.range (nthCommonList L (u+(r+s+t)) Z false).1, wordEnd (Z (false,j))) heq

lemma averageProd_left {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (n : ℕ) (M : Fin n → Measure α) (P : Measure β) [SFinite P] :
    (((n : ℝ≥0∞)⁻¹ • ∑ i, M i).prod P) =
      (n : ℝ≥0∞)⁻¹ • ∑ i, (M i).prod P := by
  rw [Measure.prod_smul_left]
  congr 1
  rw [← Measure.sum_fintype,Measure.prod_sum_left,Measure.sum_fintype]

lemma averageProd_right {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (n : ℕ) (P : Measure α) (M : Fin n → Measure β) [∀ i, SFinite (M i)] :
    P.prod ((n : ℝ≥0∞)⁻¹ • ∑ i, M i) =
      (n : ℝ≥0∞)⁻¹ • ∑ i, P.prod (M i) := by
  have : SFinite (∑ i, M i) := by
    rw [← Measure.sum_fintype]
    infer_instance
  rw [Measure.prod_smul_right]
  congr 1
  rw [← Measure.sum_fintype,Measure.prod_sum_right,Measure.sum_fintype]

lemma average_ge (n : ℕ) (hn : 0 < n) (c : ℝ≥0∞) (f : Fin n → ℝ≥0∞)
    (h : ∀ i, c ≤ f i) : c ≤ (n : ℝ≥0∞)⁻¹ * ∑ i, f i := by
  have hne : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast Nat.ne_zero_of_lt hn
  calc
    c = (n : ℝ≥0∞)⁻¹ * ∑ _i : Fin n, c := by
      rw [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        ← mul_assoc,ENNReal.inv_mul_cancel hne (by finiteness),one_mul]
    _ ≤ _ := by
      gcongr
      exact h _

lemma fourWindow_average {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (n : ℕ) [NeZero n] (E : Set (TwoTapeList α × ThreeChunk α)) :
    ((windowCommonLaw ν L n n).prod (threeChunkLaw ν L n)) E =
      (n : ℝ≥0∞)⁻¹ * ∑ u : Fin n, (n : ℝ≥0∞)⁻¹ * ∑ r : Fin n,
        (n : ℝ≥0∞)⁻¹ * ∑ s : Fin n, (n : ℝ≥0∞)⁻¹ * ∑ t : Fin n,
          ((nthCommonLaw ν L (n+u)).prod ((nthCommonLaw ν L (n+r)).prod
            ((nthCommonLaw ν L (7*n+s)).prod (nthCommonLaw ν L (n+t))))) E := by
  simp only [windowCommonLaw,threeChunkLaw]
  simp_rw [averageProd_left,averageProd_right]
  simp only [Measure.smul_apply,smul_eq_mul,Measure.finsetSum_apply]

lemma fourWindow_ge {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (n : ℕ) [NeZero n] (E : Set (TwoTapeList α × ThreeChunk α))
    (c : ℝ≥0∞) (h : ∀ u r s t : Fin n,
      c ≤ ((nthCommonLaw ν L (n+u)).prod ((nthCommonLaw ν L (n+r)).prod
        ((nthCommonLaw ν L (7*n+s)).prod (nthCommonLaw ν L (n+t))))) E) :
    c ≤ ((windowCommonLaw ν L n n).prod (threeChunkLaw ν L n)) E := by
  rw [fourWindow_average]
  exact average_ge n (Nat.pos_of_ne_zero (NeZero.ne n)) c _ (fun u =>
    average_ge n (Nat.pos_of_ne_zero (NeZero.ne n)) c _ (fun r =>
      average_ge n (Nat.pos_of_ne_zero (NeZero.ne n)) c _ (fun s =>
        average_ge n (Nat.pos_of_ne_zero (NeZero.ne n)) c _ (fun t => h u r s t))))

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

def commonBandContact {d : ℕ} (e : Step d) (n : ℕ) : Set (TwoTape (Word d)) :=
  {Z | ∃ h : ℕ, commonDepth (placedWidth e) Z (4*n) < h ∧
    h ≤ commonDepth (placedWidth e) Z (8*n) ∧ contactDepth e Z h}

lemma measurableSet_commonBandContact {d : ℕ} (e : Step d) (n : ℕ) :
    MeasurableSet (commonBandContact e n) := by
  simp only [commonBandContact,Set.ofPred_exists]
  exact MeasurableSet.iUnion (fun h =>
    (measurableSet_lt (measurable_commonDepth (placedWidth e) (4*n)) measurable_const).inter
      ((measurableSet_le measurable_const (measurable_commonDepth (placedWidth e) (8*n))).inter
        (measurableSet_contactDepth e h)))

lemma commonBand_probability_le_experiment {d : ℕ} (e : Step d)
    (ν : Bool → Measure (Word d)) [∀ b, IsProbabilityMeasure (ν b)]
    (hreg : ∀ b, ∀ᵐ a ∂ν b, RegenerationWord (axisDirection (placedAxis e b)) a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut (placedWidth e) H)
    (n : ℕ) [NeZero n] :
    twoTapeLaw ν (commonBandContact e n) ≤
      experimentLaw ν (placedWidth e) (fun _ => wordEnd) n (experimentContact e) := by
  have : Countable (Word d) := inferInstance
  have : Countable (TapeList (Word d)) := inferInstance
  have : Countable (ThreeLists (Word d)) := inferInstance
  have : Countable (TwoTapeList (Word d)) := inferInstance
  let L := placedWidth e
  have hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a := by
    intro b
    filter_upwards [hreg b] with a ha
    exact slabRecords_pos _ _ ha
  rw [experimentLaw_fourWindows ν L hL he,Measure.map_apply (measurable_of_countable _)
    (Set.to_countable _).measurableSet]
  apply fourWindow_ge
  intro u r s t
  rw [← consecutiveFour_law ν L hL he,Measure.map_apply
    (measurable_consecutiveFour L _ _ _ _) (Set.to_countable _).measurableSet]
  apply measure_mono_ae
  filter_upwards [ae_twoTape_prop ν _ (fun b => (Set.to_countable _).measurableSet) hreg,
    ae_common_iterates ν L hL he] with Z hZ hi
  intro hc
  obtain ⟨h,ha,hb,hc⟩ := hc
  have hm := (commonDepth_strictMono L Z hi).monotone
  apply commonBand_experiment_contact e Z hZ hi (n+u) (n+r) (7*n+s) (n+t) h
  · exact (hm (by have := u.isLt; have := r.isLt; omega)).trans_lt ha
  · exact hb.trans (hm (by omega))
  · exact hc

lemma reversed_cut_endpoint_height {d : ℕ} (e : Step d) (Z : ℕ → Word d)
    (hZ : ∀ i, RegenerationWord (axisDirection e) (Z i)) (N : ℕ)
    (hC : Z ∈ tapeCut (axisDirection e) N) :
    axisHeight e (wordEnd (concatenateList (reverseTapeList
      (cutList (slabRecords (axisDirection e)) N Z)))-stepVector e) = (N : ℤ)-1 := by
  rw [sub_eq_add_neg,axisHeight_add,axisHeight_neg,axisHeight_step_self,
    concatenateList_end,listTotal_reverse,axisHeight_listTotal e false (cutList (slabRecords (axisDirection e)) N Z) (fun i => hZ i)]
  change (listHeight (slabRecords (axisDirection e)) (cutList (slabRecords (axisDirection e)) N Z) : ℤ)+ -1 = _
  have hh : listHeight (slabRecords (axisDirection e)) (cutList (slabRecords (axisDirection e)) N Z) = N := by
    rw [cutList,listHeight_prefix]
    exact cutListIndex_spec _ _ Z (fun i => slabRecords_pos _ _ (hZ i)) hC
  rw [hh]
  rfl

lemma reversed_cut_endpoint_cube {d : ℕ} (e : Step d) (Z : ℕ → Word d)
    (hZ : ∀ i, RegenerationWord (axisDirection e) (Z i)) (N : ℕ)
    (hC : Z ∈ tapeCut (axisDirection e) N)
    (hR : ∑ j ∈ Finset.range N, slabRadius (Z j) < (N : ℝ)^2) :
    ∃ q, wordEnd (concatenateList (reverseTapeList (cutList (slabRecords (axisDirection e)) N Z))) -
      stepVector e = axisCubeEnumeration e N (N^2+1) q := by
  have hbd (i : Fin d) : |(wordEnd (concatenateList (reverseTapeList (cutList (slabRecords (axisDirection e)) N Z)))-stepVector e) i| ≤ ((N^2+1 : ℕ) : ℤ) := by
    have hh := (reversed_cut_endpoint_radius e Z hZ N hC i).trans hR.le
    have hv : |((stepVector e i : ℤ) : ℝ)| ≤ 1 := by
      dsimp [stepVector]
      split_ifs <;> norm_num
    have habs : |((wordEnd (concatenateList (reverseTapeList (cutList (slabRecords (axisDirection e)) N Z))) i : ℝ)) - (stepVector e i : ℝ)| ≤ |((wordEnd (concatenateList (reverseTapeList (cutList (slabRecords (axisDirection e)) N Z))) i : ℝ))| + |(stepVector e i : ℝ)| := by
      simpa only [sub_eq_add_neg,abs_neg] using abs_add_le ((wordEnd (concatenateList (reverseTapeList (cutList (slabRecords (axisDirection e)) N Z))) i : ℝ)) (-(stepVector e i : ℝ))
    have ht := habs.trans (add_le_add hh hv)
    exact_mod_cast ht
  obtain ⟨q,hq⟩ := axisCubeEnumeration_surjective e N (N^2+1)
    (wordEnd (concatenateList (reverseTapeList (cutList (slabRecords (axisDirection e)) N Z)))-stepVector e)
    (reversed_cut_endpoint_height e Z hZ N hC) hbd
  exact ⟨q,hq.symm⟩

lemma coveredDepthBand_lower {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : ∀ b, 0 < annealed μ 0 (nonBacktracking (axisDirection (placedAxis e b))))
    (s N low high m : ℕ) (hs : 0 < s) (hsN : s ≤ N) (hls : low ≤ s) (hsh : s < high)
    (hΔ : axisReachProb μ e (s-low)-axisReachProb μ e s ≤ ENNReal.ofReal ((1/2 : ℝ)^m)) :
    letI : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) :=
      fun b => slabLaw_probability μ _ (hp b)
    (annealed μ 0 (nonBacktracking (axisDirection e)))^2 ≤
      twoTapeLaw (fun b => slabLaw μ (axisDirection (placedAxis e b))) (coveredDepthBand e low high) +
      (∫⁻ a, ENNReal.ofReal (slabRadius a) ∂slabLaw μ (axisDirection e)) / (N : ℝ≥0∞) +
      (annealed μ 0 (nonBacktracking (axisDirection e)))⁻¹ *
      (annealed μ 0 (nonBacktracking (axisDirection (oppositeStep e))))⁻¹ *
        ENNReal.ofReal ((24 / posteriorExponent)*Real.log (Fintype.card (AxisCubeSite e N (N^2+1))+1)*(m+1)^2*(1/2 : ℝ)^m) := by
  let : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) :=
    fun b => slabLaw_probability μ _ (hp b)
  let := slabLaw_probability μ (axisDirection e) (hp false)
  let := conditioned_probability μ (axisDirection (oppositeStep e)) (hp true)
  have hN : 0 < N := lt_of_lt_of_le hs hsN
  have : Nonempty (AxisCubeSite e N (N^2+1)) := axisCubeSite_nonempty e N (N^2+1) hN (by nlinarith)
  have : NeZero (Fintype.card (AxisCubeSite e N (N^2+1))) := ⟨Fintype.card_ne_zero⟩
  let A := Measure.infinitePi (fun _ : ℕ => slabLaw μ (axisDirection e))
  let B := conditioned μ (axisDirection (oppositeStep e))
  let M := A.prod B
  let R : Set ((ℕ → Word d) × Path d) := {p | (N : ℝ)^2 ≤ ∑ j ∈ Finset.range N, slabRadius (p.1 j)}
  let C := mixedTapes e ⁻¹' coveredDepthBand e low high
  let F : Set ((ℕ → Word d) × Path d) := {p | p.1 ∈ tapeCut (axisDirection e) N ∧
    (concatenateList (reverseTapeList (cutList (slabRecords (axisDirection e)) N p.1)),p.2) ∈
      finiteLateEndpointEvent e (N-s) (N-low) N (axisCubeEnumeration e N (N^2+1))}
  have hM : M (Prod.fst ⁻¹' (tapeCut (axisDirection e) s ∩ tapeCut (axisDirection e) N)) ≤ M C+M R+M F := by
    refine (measure_mono_ae (t := C ∪ R ∪ F) ?_).trans ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl))
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae
      (ae_tape_prop (slabLaw μ (axisDirection e)) (RegenerationWord (axisDirection e))
        (Set.to_countable _).measurableSet (ae_slabLaw_regeneration μ hell _ (axisDirection_ne_zero e) (hp false))),
      Measure.quasiMeasurePreserving_snd.ae
        (ae_goodSlabPath μ hell _ (axisDirection_ne_zero _) (hp true))] with p hpos hneg
    intro hcuts
    by_cases hc : p ∈ C
    · exact Or.inl (Or.inl hc)
    by_cases hr : p ∈ R
    · exact Or.inl (Or.inr hr)
    apply Or.inr
    refine ⟨hcuts.2,?_,two_cuts_uncovered_mixed e p hpos hneg s N low high hs hsN hls hsh hcuts.1 hcuts.2 hc⟩
    exact reversed_cut_endpoint_cube e p.1 hpos N hcuts.2 (lt_of_not_ge hr)
  have hC : M C = twoTapeLaw (fun b => slabLaw μ (axisDirection (placedAxis e b))) (coveredDepthBand e low high) := by
    rw [← mixedTapes_law μ hell e hp,Measure.map_apply (measurable_mixedTapes e) (measurableSet_coveredDepthBand e low high)]
  have hR : M R ≤ (∫⁻ a, ENNReal.ofReal (slabRadius a) ∂slabLaw μ (axisDirection e)) / (N : ℝ≥0∞) := by
    change (A.prod B) (Prod.fst ⁻¹' {Z : ℕ → Word d | (N : ℝ)^2 ≤ ∑ j ∈ Finset.range N, slabRadius (Z j)}) ≤ _
    have hm : MeasurableSet {Z : ℕ → Word d | (N : ℝ)^2 ≤ ∑ j ∈ Finset.range N, slabRadius (Z j)} :=
      measurableSet_le measurable_const (Finset.measurable_sum _ (fun j _ =>
        (measurable_of_countable slabRadius).comp (measurable_pi_apply j)))
    rw [(measurePreserving_fst (μ := A) (ν := B)).measure_preimage hm.nullMeasurableSet]
    exact iid_radius_large _ N (lt_of_lt_of_le hs hsN)
  have hF := mixed_bridge_late_bound μ hell e (hp false) (N-s) (N-low) N m
    (by omega) (by omega) (axisCubeEnumeration e N (N^2+1))
    (axisCubeEnumeration_height e N (N^2+1)) (axisCubeEnumeration_injective e N (N^2+1))
    (by simpa only [show N-low-(N-s) = s-low by omega,show N-(N-s) = s by omega] using hΔ)
  have hcuts := axis_two_cuts_lower μ hell e (hp false) s N hsN
  have hfrom : M (Prod.fst ⁻¹' (tapeCut (axisDirection e) s ∩ tapeCut (axisDirection e) N)) =
      A (tapeCut (axisDirection e) s ∩ tapeCut (axisDirection e) N) := by
    exact measurePreserving_fst.measure_preimage ((measurableSet_tapeCut _ _).inter (measurableSet_tapeCut _ _)).nullMeasurableSet
  rw [hfrom,hC] at hM
  exact hcuts.trans (hM.trans (add_le_add (add_le_add le_rfl hR) hF))

lemma commonDepth_markov {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (hi : Integrable (fun Z => (firstCommonWidth L Z : ℝ)) (twoTapeLaw ν))
    (r low : ℕ) (hlow : 0 < low) :
    twoTapeLaw ν {Z | low ≤ commonDepth L Z r} ≤
      (r : ℝ≥0∞) * ENNReal.ofReal (∫ Z, (firstCommonWidth L Z : ℝ) ∂twoTapeLaw ν) / (low : ℝ≥0∞) := by
  have hh := meas_ge_le_lintegral_div (μ := twoTapeLaw ν)
    (((measurable_of_countable (fun n : ℕ => (n : ℝ≥0∞))).comp (measurable_commonDepth L r)).aemeasurable)
    (ε := (low : ℝ≥0∞)) (by exact_mod_cast Nat.ne_zero_of_lt hlow) (by finiteness)
  have hs : {Z : TwoTape α | (low : ℝ≥0∞) ≤ (commonDepth L Z r : ℝ≥0∞)} =
      {Z | low ≤ commonDepth L Z r} := by ext Z;simp
  simp only [Function.comp_def] at hh
  rw [hs] at hh
  have heq : (∫⁻ Z, (commonDepth L Z r : ℝ≥0∞) ∂twoTapeLaw ν) =
      (r : ℝ≥0∞)*ENNReal.ofReal (∫ Z, (firstCommonWidth L Z : ℝ) ∂twoTapeLaw ν) := by
    have hv := ofReal_integral_eq_lintegral_ofReal (commonDepth_integrable ν L hL he hi r)
      (Filter.Eventually.of_forall (fun Z => Nat.cast_nonneg (commonDepth L Z r)))
    simp only [ENNReal.ofReal_natCast] at hv
    rw [← hv,commonDepth_integral ν L hL he hi,ENNReal.ofReal_mul (Nat.cast_nonneg r),ENNReal.ofReal_natCast]
  exact hh.trans_eq (congrArg (fun x => x/(low : ℝ≥0∞)) heq)

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

lemma dyadic_band_cover (H : ℕ → ℕ) (a b h : ℕ) (hab : a ≤ b)
    (ha : H (4*2^a) < h) (hb : h ≤ H (8*2^b)) :
    ∃ j ∈ Finset.Icc a b, H (4*2^j) < h ∧ h ≤ H (8*2^j) := by
  induction b,hab using Nat.le_induction with
  | base => exact ⟨a,Finset.mem_Icc.mpr ⟨le_rfl,le_rfl⟩,ha,hb⟩
  | succ b hab ih =>
    by_cases hh : h ≤ H (8*2^b)
    · obtain ⟨j,hj,hjlo,hjhi⟩ := ih hh
      exact ⟨j,Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1,(Finset.mem_Icc.mp hj).2.trans (Nat.le_succ b)⟩,hjlo,hjhi⟩
    · refine ⟨b+1,Finset.mem_Icc.mpr ⟨by omega,le_rfl⟩,?_,hb⟩
      have hp : 4*2^(b+1) = 8*2^b := by rw [pow_succ];omega
      rw [hp]
      exact lt_of_not_ge hh

lemma coveredDepthBand_le_index_sum {d : ℕ} (e : Step d)
    (ν : Bool → Measure (Word d)) [∀ b, IsProbabilityMeasure (ν b)]
    (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < placedWidth e b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut (placedWidth e) H)
    (hi : Integrable (fun Z => (firstCommonWidth (placedWidth e) Z : ℝ)) (twoTapeLaw ν))
    (a b low high : ℕ) (hab : a ≤ b) (hlow : 0 < low) (hhigh : high ≤ 8*2^b) :
    twoTapeLaw ν (coveredDepthBand e low high) ≤
      ((4*2^a : ℕ) : ℝ≥0∞) * ENNReal.ofReal (∫ Z, (firstCommonWidth (placedWidth e) Z : ℝ) ∂twoTapeLaw ν) / (low : ℝ≥0∞) +
      ∑ j ∈ Finset.Icc a b, twoTapeLaw ν (commonBandContact e (2^j)) := by
  let B := {Z | low ≤ commonDepth (placedWidth e) Z (4*2^a)}
  have hh : twoTapeLaw ν (coveredDepthBand e low high) ≤
      twoTapeLaw ν B + twoTapeLaw ν (⋃ j ∈ Finset.Icc a b, commonBandContact e (2^j)) := by
    refine (measure_mono_ae (t := B ∪ ⋃ j ∈ Finset.Icc a b, commonBandContact e (2^j)) ?_).trans (measure_union_le _ _)
    filter_upwards [ae_common_iterates ν (placedWidth e) hL he] with Z hZ
    intro hcov
    by_cases hbad : Z ∈ B
    · exact Or.inl hbad
    apply Or.inr
    obtain ⟨h,hlo,hhi,hcon⟩ := hcov
    have hmon := commonDepth_strictMono (placedWidth e) Z hZ
    obtain ⟨j,hj,hja,hjb⟩ := dyadic_band_cover (commonDepth (placedWidth e) Z) a b h hab
      ((lt_of_not_ge hbad).trans_le hlo) (hhi.le.trans (hhigh.trans (hmon.id_le _)))
    exact Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨hj,h,hja,hjb,hcon⟩⟩
  exact hh.trans (add_le_add (commonDepth_markov ν (placedWidth e) hL he hi (4*2^a) low hlow)
    (measure_biUnion_finset_le _ _))

lemma sum_shift_four_sub (h : ℕ → ℝ) (J : ℕ) :
    (∑ j ∈ Finset.range J, (h (j+4)-h j)) =
      h J+h (J+1)+h (J+2)+h (J+3)-h 0-h 1-h 2-h 3 := by
  induction J with
  | zero => simp;ring
  | succ J ih =>
    rw [Finset.sum_range_succ,ih]
    have h1 : J+1+1 = J+2 := by omega
    have h2 : J+1+2 = J+3 := by omega
    have h3 : J+1+3 = J+4 := by omega
    simp only [h1,h2,h3]
    ring

lemma sum_shift_four_le (h : ℕ → ℝ) (h0 : ∀ j, 0 ≤ h j) (hm : Monotone h) (J : ℕ) :
    (∑ j ∈ Finset.range J, (h (j+4)-h j)) ≤ 4*h (J+3) := by
  rw [sum_shift_four_sub]
  have ha := hm (show J ≤ J+3 by omega)
  have hb := hm (show J+1 ≤ J+3 by omega)
  have hc := hm (show J+2 ≤ J+3 by omega)
  linarith [h0 0,h0 1,h0 2,h0 3]

lemma log_nat_pow_two_add_one (j : ℕ) :
    Real.log (((2:ℕ)^j : ℝ)+1) ≤ (j+1)*Real.log 2 := by
  have hp : (1:ℝ) ≤ 2^j := one_le_pow₀ (by norm_num)
  have hh : ((2:ℕ)^j : ℝ)+1 ≤ (2:ℝ)^(j+1) := by
    push_cast
    rw [pow_succ]
    linarith
  have ht := Real.log_le_log (by positivity : (0:ℝ) < ((2:ℕ)^j : ℝ)+1) hh
  rw [Real.log_pow] at ht
  simpa only [Nat.cast_add,Nat.cast_one] using ht

lemma entropy_dyadic_telescope {q : ℕ} (ν : Measure (Fin q → ℤ)) [IsProbabilityMeasure ν]
    (hi : ∀ i, Integrable (fun x => |(x i : ℝ)|) ν) (a : ℝ) (ha : 0 < a)
    (hb : ∀ i, (∫ x, |(x i : ℝ)| ∂ν) ≤ a) (J : ℕ) :
    (∑ j ∈ Finset.range J, (entropyOf (sumLaw ν (14*2^j)) id-entropyOf (sumLaw ν (2^j)) id)) ≤
      4*q*(1+Real.log 2+Real.log (a+1)+(J+4)*Real.log 2) := by
  let h := fun j => entropyOf (sumLaw ν (2^j)) id
  have hall (n : ℕ) := (sumLaw_lattice_entropy ν hi a ha hb n).1
  have hm := sumLaw_entropy_monotone ν hall
  have hmono : Monotone h := by
    intro m n hmn
    apply hm
    exact Nat.pow_le_pow_right (by norm_num) hmn
  have hsum : (∑ j ∈ Finset.range J, (entropyOf (sumLaw ν (14*2^j)) id-entropyOf (sumLaw ν (2^j)) id)) ≤
      ∑ j ∈ Finset.range J, (h (j+4)-h j) := by
    apply Finset.sum_le_sum
    intro j hj
    apply sub_le_sub_right
    apply hm
    rw [pow_add]
    omega
  refine hsum.trans ((sum_shift_four_le h (fun _ => entropyOf_nonneg _ _) hmono J).trans ?_)
  have hh := (sumLaw_lattice_entropy ν hi a ha hb (2^(J+3))).2
  have hl := log_nat_pow_two_add_one (J+3)
  have hq : (0:ℝ) ≤ q := Nat.cast_nonneg _
  have hb' : h (J+3) ≤ q*(1+Real.log 2+Real.log (a+1)+(J+4)*Real.log 2) := by
    refine hh.trans (mul_le_mul_of_nonneg_left ?_ hq)
    have he : ((J+3 : ℕ) : ℝ)+1 = (J:ℝ)+4 := by push_cast;ring
    rw [he] at hl
    push_cast at *
    linarith
  nlinarith

lemma kl_event_scale_bound {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hfin : InformationTheory.klDiv P Q ≠ ∞) (E : Set Ω) (hE : MeasurableSet E)
    (B : ℝ) (hB : 1 ≤ B) :
    Real.log B * P.real E ≤ (InformationTheory.klDiv P Q).toReal + Real.log 2 +
      Real.log B * B * Q.real E := by
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hlog : 0 ≤ Real.log B := Real.log_nonneg hB
  have hkl : 0 ≤ (InformationTheory.klDiv P Q).toReal := ENNReal.toReal_nonneg
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  by_cases hq : Q.real E = 0
  · have hq' : Q E = 0 := (ENNReal.toReal_eq_zero_iff _).mp hq |>.resolve_right (measure_ne_top Q E)
    have hp := (InformationTheory.klDiv_ne_top_iff.mp hfin).1 hq'
    simp only [measureReal_def,hp,hq',ENNReal.toReal_zero,mul_zero]
    linarith
  by_cases hsmall : Q.real E ≤ B⁻¹
  · have hq0 : 0 < Q.real E := lt_of_le_of_ne measureReal_nonneg (Ne.symm hq)
    have hh := Real.log_le_log hq0 hsmall
    rw [Real.log_inv] at hh
    have hb := kl_event_bound P Q hfin E hE
    have hp := mul_le_mul_of_nonneg_left (neg_le_neg hh) (measureReal_nonneg (μ := P) (s := E))
    have ht : 0 ≤ Real.log B*B*Q.real E := mul_nonneg (mul_nonneg hlog hB0.le) measureReal_nonneg
    nlinarith
  · have ht : 1 ≤ B*Q.real E := by
      have hh := mul_le_mul_of_nonneg_left (le_of_not_ge hsmall) hB0.le
      simpa only [mul_inv_cancel₀ hB0.ne'] using hh
    have hp := measureReal_le_one (μ := P) (s := E)
    nlinarith [mul_le_mul_of_nonneg_left ht hlog]

lemma placed_cut_positive {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : ∀ b, 0 < annealed μ 0 (nonBacktracking (axisDirection (placedAxis e b)))) (H : ℕ) (b : Bool) :
    Measure.infinitePi (fun _ : ℕ => slabLaw μ (axisDirection (placedAxis e b)))
      (renewalCut (placedWidth e b) H) ≠ 0 := by
  rw [show Measure.infinitePi (fun _ : ℕ => slabLaw μ (axisDirection (placedAxis e b)))
      (renewalCut (placedWidth e b) H) = axisReachProb μ (placedAxis e b) H from
      axis_tapeCut_mass μ hell _ (hp b) H]
  exact ne_of_gt ((hp b).trans_le (axisReachProb_lower μ hell _ _))

lemma experiment_probability {α G : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
    [AddCommGroup G] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (D : Bool → α → G) (n : ℕ) [NeZero n] :
    IsProbabilityMeasure (experimentLaw ν L D n) :=
  probabilityMeasure_map (measurable_of_countable _).aemeasurable

lemma reference_probability {α G : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
    [AddCommGroup G] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (D : Bool → α → G)
    (hu : ∀ H b, Measure.infinitePi (fun _ : ℕ => ν b) (renewalCut (L b) H) ≠ 0)
    (n : ℕ) [NeZero n] : IsProbabilityMeasure (experimentReference ν L D n) := by
  let := experiment_probability ν L D n
  let : IsMarkovKernel (signedThreeKernel (ν false) (L false)) := signedThreeKernel_markov _ _ (fun H => hu H false)
  let : IsMarkovKernel (signedThreeKernel (ν true) (L true)) := signedThreeKernel_markov _ _ (fun H => hu H true)
  unfold experimentReference
  infer_instance

lemma placed_reference_summable {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : ∀ b, 0 < annealed μ 0 (nonBacktracking (axisDirection (placedAxis e b)))) :
    letI : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) :=
      fun b => slabLaw_probability μ _ (hp b)
    Summable (fun j => (experimentReference (fun b => slabLaw μ (axisDirection (placedAxis e b)))
      (placedWidth e) (fun _ => wordEnd) (2^j)).real (experimentContact e)) := by
  let : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) := fun b => slabLaw_probability μ _ (hp b)
  let := slabLaw_probability μ (axisDirection e) (hp false)
  let := slabLaw_probability μ (axisDirection (oppositeStep e)) (hp true)
  let ν := fun b => slabLaw μ (axisDirection (placedAxis e b))
  obtain ⟨he,hi⟩ := placed_common_data μ hell e hp
  let W := ∫ Z, (firstCommonWidth (placedWidth e) Z : ℝ) ∂twoTapeLaw ν
  let C := ((annealed μ 0 (nonBacktracking (axisDirection e))).toReal)⁻¹^2 *
    ((annealed μ 0 (nonBacktracking (axisDirection (oppositeStep e)))).toReal)⁻¹^2 * 24 * W
  have hc : Summable (fun j => C*((2:ℝ)^j*(axisWidthTail μ e (2^j)).toReal+
      (2:ℝ)^j*(axisWidthTail μ (oppositeStep e) (2^j)).toReal)) :=
    ((summable_dyadic_axisWidthTail μ hell e (hp false)).add
      (summable_dyadic_axisWidthTail μ hell (oppositeStep e) (hp true))).mul_left C
  apply Summable.of_nonneg_of_le (fun _ => measureReal_nonneg) _ hc
  intro j
  let : NeZero ((2:ℕ)^j) := ⟨pow_ne_zero _ (by norm_num)⟩
  let := reference_probability ν (placedWidth e) (fun _ => wordEnd) (placed_cut_positive μ hell e hp) (2^j)
  have hb := experimentReference_contact_bound μ hell e hp he hi (2^j)
  have hW : 0 ≤ W := integral_nonneg (fun Z => Nat.cast_nonneg _)
  have ht := ENNReal.toReal_mono (show
      ((annealed μ 0 (nonBacktracking (axisDirection e)))⁻¹)^2 *
      ((annealed μ 0 (nonBacktracking (axisDirection (oppositeStep e))))⁻¹)^2 * 2 *
      ENNReal.ofReal (12*(2^j : ℕ)*W) *
      (axisWidthTail μ e (2^j)+axisWidthTail μ (oppositeStep e) (2^j)) ≠ ∞ by
        apply ENNReal.mul_ne_top
        · apply ENNReal.mul_ne_top
          · apply ENNReal.mul_ne_top
            · exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (ne_of_gt (hp false))))
                (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (ne_of_gt (hp true))))
            · norm_num
          · exact ENNReal.ofReal_ne_top
        · exact ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _,measure_ne_top _ _⟩) hb
  have hFa : axisWidthTail μ e (2^j) ≠ ∞ := measure_ne_top _ _
  have hFb : axisWidthTail μ (oppositeStep e) (2^j) ≠ ∞ := measure_ne_top _ _
  simp only [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_inv,ENNReal.toReal_ofNat,
    ENNReal.toReal_add hFa hFb] at ht
  rw [ENNReal.toReal_ofReal (by positivity)] at ht
  push_cast at ht
  change _ ≤ C*((2:ℝ)^j*(axisWidthTail μ e (2^j)).toReal+
      (2:ℝ)^j*(axisWidthTail μ (oppositeStep e) (2^j)).toReal)
  calc
    _ ≤ _ := ht
    _ = _ := by dsimp only [C];ring

lemma placed_kl_bounds {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : ∀ b, 0 < annealed μ 0 (nonBacktracking (axisDirection (placedAxis e b)))) :
    letI : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) :=
      fun b => slabLaw_probability μ _ (hp b)
    let ν := fun b => slabLaw μ (axisDirection (placedAxis e b))
    (∀ j, InformationTheory.klDiv (experimentLaw ν (placedWidth e) (fun _ => wordEnd) (2^j))
      (experimentReference ν (placedWidth e) (fun _ => wordEnd) (2^j)) ≠ ∞) ∧
    ∃ A : ℝ, 0 ≤ A ∧ ∀ J,
      (∑ j ∈ Finset.range J, (InformationTheory.klDiv
        (experimentLaw ν (placedWidth e) (fun _ => wordEnd) (2^j))
        (experimentReference ν (placedWidth e) (fun _ => wordEnd) (2^j))).toReal) ≤ A*J := by
  let : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) := fun b => slabLaw_probability μ _ (hp b)
  let ν := fun b => slabLaw μ (axisDirection (placedAxis e b))
  obtain ⟨he,hW⟩ := placed_common_data μ hell e hp
  let ρ := commonGapLaw ν (placedWidth e) (fun _ => wordEnd)
  have hi : ∀ i, Integrable (fun x : Site d => |(x i : ℝ)|) ρ :=
    commonGapLaw_lattice_integrable ν (placedWidth e) (placed_slab_positive μ hell e hp)
      he hW (fun _ => wordEnd) (placed_wordEnd_integrable μ hell e hp)
  let c := ((annealed μ 0 (nonBacktracking (axisDirection e))) *
    (annealed μ 0 (nonBacktracking (axisDirection (oppositeStep e))))).toReal
  have hc : 0 < c := ENNReal.toReal_pos (mul_ne_zero (ne_of_gt (hp false)) (ne_of_gt (hp true)))
    (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))
  have hlo (H : ℕ) : ENNReal.ofReal c ≤ renewalPairMass ν (placedWidth e) H := by
    rw [show ENNReal.ofReal c = annealed μ 0 (nonBacktracking (axisDirection e))*
      annealed μ 0 (nonBacktracking (axisDirection (oppositeStep e))) from
      ENNReal.ofReal_toReal (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))]
    simpa only [commonCut_mass,renewalPairMass,Fintype.prod_bool,ν,mul_comm] using placed_common_lower μ hell e hp H
  let C := 6*(1+Real.log (8*((∫ Z, (firstCommonWidth (placedWidth e) Z : ℝ) ∂twoTapeLaw ν)+1)+1))+1+Real.log 16
  have hb (j : ℕ) : InformationTheory.klDiv (experimentLaw ν (placedWidth e) (fun _ => wordEnd) (2^j))
      (experimentReference ν (placedWidth e) (fun _ => wordEnd) (2^j)) ≠ ∞ ∧
      (InformationTheory.klDiv (experimentLaw ν (placedWidth e) (fun _ => wordEnd) (2^j))
      (experimentReference ν (placedWidth e) (fun _ => wordEnd) (2^j))).toReal ≤
      C+(entropyOf (sumLaw ρ (14*2^j)) id-entropyOf (sumLaw ρ (2^j)) id) := by
    let : NeZero ((2:ℕ)^j) := ⟨pow_ne_zero _ (by norm_num)⟩
    have hh := lattice_experiment_kl_comparison ν (placedWidth e) (placed_slab_positive μ hell e hp)
      he hW (placed_cut_positive μ hell e hp) c hc hlo (fun _ => wordEnd)
      (placed_wordEnd_integrable μ hell e hp) (2^j)
    exact ⟨hh.1,by dsimp [C,ρ];linarith [hh.2]⟩
  refine ⟨fun j => (hb j).1,?_⟩
  let a := 1+∑ i : Fin d, ∫ x, |(x i : ℝ)| ∂ρ
  have ha : 0 < a := by
    have hh : 0 ≤ ∑ i : Fin d, ∫ x, |(x i : ℝ)| ∂ρ := Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => abs_nonneg _))
    dsimp [a];linarith
  have hia (i : Fin d) : (∫ x, |(x i : ℝ)| ∂ρ) ≤ a := by
    have hh := Finset.single_le_sum (s := Finset.univ) (f := fun i : Fin d => ∫ x, |(x i : ℝ)| ∂ρ)
      (fun i _ => integral_nonneg (fun x => abs_nonneg _)) (Finset.mem_univ i)
    dsimp [a];linarith
  let B := 1+Real.log 2+Real.log (a+1)+4*Real.log 2
  refine ⟨|C|+4*d*(|B|+Real.log 2),by have := Real.log_nonneg (by norm_num : (1:ℝ)≤2);positivity,?_⟩
  intro J
  by_cases hJ : J = 0
  · subst J;simp
  have hJ1 : (1:ℝ) ≤ J := by exact_mod_cast Nat.pos_of_ne_zero hJ
  have hh := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range J) => (hb j).2)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hh
  have ht := entropy_dyadic_telescope ρ hi a ha hia J
  have hC := le_abs_self C
  have hB := le_abs_self B
  have hBB : |B| ≤ |B| * J := le_mul_of_one_le_right (abs_nonneg _) hJ1
  have hd : (0:ℝ) ≤ d := Nat.cast_nonneg _
  have hcJ := mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg J)
  have hbJ := mul_le_mul_of_nonneg_left (hB.trans hBB) (by positivity : (0:ℝ)≤4*d)
  dsimp only [B] at hbJ
  nlinarith

lemma commonBand_entropy_upper {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : ∀ b, 0 < annealed μ 0 (nonBacktracking (axisDirection (placedAxis e b)))) :
    letI : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) :=
      fun b => slabLaw_probability μ _ (hp b)
    let ν := fun b => slabLaw μ (axisDirection (placedAxis e b))
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ (J L : ℕ),
      (L*Real.log 2)*(∑ j ∈ Finset.range J, (twoTapeLaw ν).real (commonBandContact e (2^j))) ≤
        A*J+(L*Real.log 2)*(2:ℝ)^L*B := by
  let : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) := fun b => slabLaw_probability μ _ (hp b)
  let ν := fun b => slabLaw μ (axisDirection (placedAxis e b))
  have : Countable (Word d) := inferInstance
  have : Countable (TapeList (Word d)) := inferInstance
  have : Countable (ThreeLists (Word d)) := inferInstance
  let Q (j : ℕ) := experimentReference ν (placedWidth e) (fun _ => wordEnd) (2^j)
  let P (j : ℕ) := experimentLaw ν (placedWidth e) (fun _ => wordEnd) (2^j)
  have hne (j : ℕ) : NeZero ((2:ℕ)^j) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hP (j : ℕ) : IsProbabilityMeasure (P j) := by let := hne j;exact experiment_probability ν (placedWidth e) (fun _ => wordEnd) _
  have hQ (j : ℕ) : IsProbabilityMeasure (Q j) := by let := hne j;exact reference_probability ν (placedWidth e) (fun _ => wordEnd) (placed_cut_positive μ hell e hp) _
  obtain ⟨hfin,A,hA,hbound⟩ := placed_kl_bounds μ hell e hp
  have hsum := placed_reference_summable μ hell e hp
  let B := ∑' j, (Q j).real (experimentContact e)
  have hB : 0 ≤ B := tsum_nonneg (fun _ => measureReal_nonneg)
  refine ⟨A+Real.log 2,B,add_nonneg hA (Real.log_nonneg (by norm_num)),hB,?_⟩
  intro J L
  have hlog : 0 ≤ (L:ℝ)*Real.log 2 := mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
  have he := (placed_common_data μ hell e hp).1
  have hpoint (j : ℕ) : (L*Real.log 2)*(twoTapeLaw ν).real (commonBandContact e (2^j)) ≤
      (InformationTheory.klDiv (P j) (Q j)).toReal+Real.log 2+(L*Real.log 2)*(2:ℝ)^L*(Q j).real (experimentContact e) := by
    let := hne j
    let := hP j
    let := hQ j
    have hdom := commonBand_probability_le_experiment e ν
      (fun b => ae_slabLaw_regeneration μ hell _ (axisDirection_ne_zero _) (hp b)) he (2^j)
    have hdr := ENNReal.toReal_mono (measure_ne_top (P j) _) hdom
    have hkl := kl_event_scale_bound (P j) (Q j) (hfin j) (experimentContact e)
      (Set.to_countable _).measurableSet ((2:ℝ)^L) (one_le_pow₀ (by norm_num))
    rw [Real.log_pow] at hkl
    exact (mul_le_mul_of_nonneg_left hdr hlog).trans hkl
  have hh := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range J) => hpoint j)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,
    ← Finset.mul_sum] at hh
  have hqs : (∑ j ∈ Finset.range J, (Q j).real (experimentContact e)) ≤ B :=
    Summable.sum_le_tsum (Finset.range J) (fun _ _ => measureReal_nonneg) hsum
  have ht := mul_le_mul_of_nonneg_left hqs (mul_nonneg hlog (by positivity : (0:ℝ) ≤ (2:ℝ)^L))
  have hk := hbound J
  dsimp only [P,Q] at hh ht
  nlinarith

lemma commonBand_lower_real {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : ∀ b, 0 < annealed μ 0 (nonBacktracking (axisDirection (placedAxis e b))))
    (s N low high m a b : ℕ) (hs : 0 < s) (hsN : s ≤ N) (hls : low ≤ s) (hsh : s < high)
    (hab : a ≤ b) (hlow : 0 < low) (hhigh : high ≤ 8*2^b)
    (hΔ : axisReachProb μ e (s-low)-axisReachProb μ e s ≤ ENNReal.ofReal ((1/2 : ℝ)^m)) :
    letI : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) :=
      fun b => slabLaw_probability μ _ (hp b)
    let ν := fun b => slabLaw μ (axisDirection (placedAxis e b))
    (annealed μ 0).real (nonBacktracking (axisDirection e))^2 ≤
      (4*2^a : ℕ) * (∫ Z, (firstCommonWidth (placedWidth e) Z : ℝ) ∂twoTapeLaw ν) / low +
      (∑ j ∈ Finset.Icc a b, (twoTapeLaw ν).real (commonBandContact e (2^j))) +
      (∫ a, slabRadius a ∂ν false) / N +
      ((annealed μ 0).real (nonBacktracking (axisDirection e)))⁻¹ *
      ((annealed μ 0).real (nonBacktracking (axisDirection (oppositeStep e))))⁻¹ *
        ((24 / posteriorExponent)*Real.log (Fintype.card (AxisCubeSite e N (N^2+1))+1)*(m+1)^2*(1/2 : ℝ)^m) := by
  let : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) := fun b => slabLaw_probability μ _ (hp b)
  let ν := fun b => slabLaw μ (axisDirection (placedAxis e b))
  obtain ⟨he,hi⟩ := placed_common_data μ hell e hp
  have hbnd := coveredDepthBand_lower μ hell e hp s N low high m hs hsN hls hsh hΔ
  have hidx := coveredDepthBand_le_index_sum e ν (placed_slab_positive μ hell e hp) he hi a b low high hab hlow hhigh
  have hh := hbnd.trans (add_le_add (add_le_add hidx le_rfl) le_rfl)
  have hR := ofReal_integral_eq_lintegral_ofReal (placed_slabRadius_integrable μ hell e hp false)
    (Filter.Eventually.of_forall (fun a => slabRadius_nonneg a))
  change ENNReal.ofReal (∫ x, slabRadius x ∂slabLaw μ (axisDirection e)) =
    ∫⁻ x, ENNReal.ofReal (slabRadius x) ∂slabLaw μ (axisDirection e) at hR
  rw [← hR] at hh
  have hfin : ((4*2^a : ℕ) : ℝ≥0∞) * ENNReal.ofReal (∫ Z, (firstCommonWidth (placedWidth e) Z : ℝ) ∂twoTapeLaw ν) / (low : ℝ≥0∞) +
      (∑ j ∈ Finset.Icc a b, twoTapeLaw ν (commonBandContact e (2^j))) +
      ENNReal.ofReal (∫ a, slabRadius a ∂ν false) / (N : ℝ≥0∞) +
      (annealed μ 0 (nonBacktracking (axisDirection e)))⁻¹ *
      (annealed μ 0 (nonBacktracking (axisDirection (oppositeStep e))))⁻¹ *
        ENNReal.ofReal ((24 / posteriorExponent)*Real.log (Fintype.card (AxisCubeSite e N (N^2+1))+1)*(m+1)^2*(1/2 : ℝ)^m) ≠ ∞ := by
    have hN : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast (lt_of_lt_of_le hs hsN).ne'
    have hl : (low : ℝ≥0∞) ≠ 0 := by exact_mod_cast hlow.ne'
    have hp0 : annealed μ 0 (nonBacktracking (axisDirection e)) ≠ 0 := ne_of_gt (hp false)
    have hp1 : annealed μ 0 (nonBacktracking (axisDirection (oppositeStep e))) ≠ 0 := ne_of_gt (hp true)
    refine ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨?_,?_⟩,?_⟩,?_⟩
    · exact ENNReal.div_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top) hl
    · exact ENNReal.sum_ne_top.mpr (fun j _ => measure_ne_top _ _)
    · exact ENNReal.div_ne_top ENNReal.ofReal_ne_top hN
    · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hp0)
        (ENNReal.inv_ne_top.mpr hp1)) ENNReal.ofReal_ne_top
  have ht := ENNReal.toReal_mono hfin hh
  have hW : 0 ≤ ∫ Z, (firstCommonWidth (placedWidth e) Z : ℝ) ∂twoTapeLaw ν := integral_nonneg (fun Z => Nat.cast_nonneg _)
  have hr : 0 ≤ ∫ a, slabRadius a ∂ν false := integral_nonneg slabRadius_nonneg
  have hlog : 0 ≤ Real.log (Fintype.card (AxisCubeSite e N (N^2+1))+1) := Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg _))
  have hE : 0 ≤ (24/posteriorExponent)*Real.log (Fintype.card (AxisCubeSite e N (N^2+1))+1)*(m+1)^2*(1/2 : ℝ)^m := by
    have := posteriorExponent_pos
    positivity
  have hadd (x y : ℝ≥0∞) (h : x+y ≠ ∞) : (x+y).toReal = x.toReal+y.toReal :=
    ENNReal.toReal_add (ENNReal.add_ne_top.mp h).1 (ENNReal.add_ne_top.mp h).2
  rw [hadd _ _ hfin] at ht
  rw [hadd _ _ (ENNReal.add_ne_top.mp hfin).1] at ht
  rw [hadd _ _ (ENNReal.add_ne_top.mp (ENNReal.add_ne_top.mp hfin).1).1] at ht
  simp only [ENNReal.toReal_mul,
    ENNReal.toReal_div,ENNReal.toReal_natCast,ENNReal.toReal_sum (fun j _ => measure_ne_top _ _),
    ENNReal.toReal_inv,ENNReal.toReal_pow,ENNReal.toReal_ofReal hW,ENNReal.toReal_ofReal hr,
    ENNReal.toReal_ofReal hE] at ht
  exact ht

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

lemma axisCube_log_bound {d : ℕ} (e : Step d) (J : ℕ) (hJ : 0 < J) :
    Real.log (Fintype.card (AxisCubeSite e (2^J) ((2^J)^2+1))+1) ≤
      (d+1)*6*J := by
  have hc := card_axisCubeSite_le e (2^J) ((2^J)^2+1)
  have hpow : (2:ℕ)^(2*J) = ((2:ℕ)^J)^2 := by rw [Nat.mul_comm 2 J,pow_mul]
  have hb : 2*((2:ℕ)^J)^2+3 ≤ 2^(2*J+3) := by
    rw [pow_add,hpow]
    have hh : 1 ≤ ((2:ℕ)^J)^2 := one_le_pow₀ (one_le_pow₀ (by norm_num))
    norm_num at *
    omega
  have hbase : 2*((2:ℕ)^J)^2+3 = 2*(((2:ℕ)^J)^2+1)+1 := by ring
  rw [hbase] at hb
  have hp : (2*(((2:ℕ)^J)^2+1)+1)^d ≤ 2^((2*J+3)*d) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left hb d
  have hc' : Fintype.card (AxisCubeSite e (2^J) ((2^J)^2+1))+1 ≤ 2^((2*J+3)*d+1) := by
    have hh := hc.trans hp
    have h1 : 1 ≤ (2:ℕ)^((2*J+3)*d) := one_le_pow₀ (by norm_num)
    rw [pow_succ (2:ℕ) ((2*J+3)*d)]
    omega
  have hh := Real.log_le_log (by positivity : 0 < (Fintype.card (AxisCubeSite e (2^J) ((2^J)^2+1)) : ℝ)+1)
    (show (Fintype.card (AxisCubeSite e (2^J) ((2^J)^2+1)) : ℝ)+1 ≤ (2:ℝ)^((2*J+3)*d+1) by exact_mod_cast hc')
  rw [Real.log_pow] at hh
  have hl : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hm : 0 ≤ (((2*J+3)*d+1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hv := mul_le_mul_of_nonneg_left hl hm
  push_cast at hh hv
  have hj : (1:ℝ) ≤ J := by exact_mod_cast hJ
  have hd : (0:ℝ) ≤ d := Nat.cast_nonneg _
  nlinarith

lemma summable_shifted_axisTail {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : 0 < annealed μ 0 (nonBacktracking (axisDirection e))) :
    Summable (fun l => (2:ℝ)^l*(axisWidthTail μ e (2^(l-1))).toReal) := by
  apply (summable_nat_add_iff 1).mp
  simpa only [Nat.add_sub_cancel,pow_succ,mul_assoc,mul_comm,mul_left_comm] using
    (summable_dyadic_axisWidthTail μ hell e hp).mul_left 2

lemma axis_delta_dyadic {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : 0 < annealed μ 0 (nonBacktracking (axisDirection e)))
    (l G : ℕ) (hG : 1 ≤ G) (hGl : G ≤ l) :
    axisReachProb μ e (2^l-2^(l-G))-axisReachProb μ e (2^l) ≤
      ENNReal.ofReal ((1/2 : ℝ)^G*((2:ℝ)^l*(axisWidthTail μ e (2^(l-1))).toReal)) := by
  let := slabLaw_probability μ (axisDirection e) hp
  have hlow : (2:ℕ)^(l-G) ≤ 2^l := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
  have hhalf : (2:ℕ)^(l-1) ≤ 2^l-2^(l-G) := by
    have hh : (2:ℕ)^(l-G) ≤ 2^(l-1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpow : (2:ℕ)^l = 2^(l-1)*2 := by
      conv_lhs => rw [show l = (l-1)+1 by omega,pow_succ]
    omega
  have hr := (axis_renewal_tail_bound μ hell e hp (Nat.sub_le ((2:ℕ)^l) ((2:ℕ)^(l-G)))).2
  have ht := ENNReal.toReal_mono (measure_ne_top _ _) (axisWidthTail_antitone μ e hhalf)
  change (axisWidthTail μ e (2^l-2^(l-G))).toReal ≤ (axisWidthTail μ e (2^(l-1))).toReal at ht
  have hpow : (2:ℝ)^(l-G) = (1/2 : ℝ)^G*(2:ℝ)^l := by
    have he : l = (l-G)+G := by omega
    rw [show (2:ℝ)^l = (2:ℝ)^(l-G)*(2:ℝ)^G from by rw [← pow_add, ← he]]
    rw [div_pow,one_pow]
    field_simp
  have hreal : (axisReachProb μ e (2^l-2^(l-G))).toReal-(axisReachProb μ e (2^l)).toReal ≤
      (1/2 : ℝ)^G*((2:ℝ)^l*(axisWidthTail μ e (2^(l-1))).toReal) := by
    have hrr : ((2^l : ℕ) : ℝ)-((2^l-2^(l-G) : ℕ) : ℝ) = (2:ℝ)^(l-G) := by
      rw [Nat.cast_sub hlow];push_cast;ring
    rw [hrr] at hr
    exact hr.trans (by simpa only [hpow,mul_assoc] using mul_le_mul_of_nonneg_left ht (by positivity : (0:ℝ)≤(2:ℝ)^(l-G)))
  apply (ENNReal.toReal_le_toReal (lt_of_le_of_lt tsub_le_self (measure_lt_top _ _)).ne ENNReal.ofReal_ne_top).mp
  change (axisReachProb μ e (2^l-2^(l-G))-axisReachProb μ e (2^l)).toReal ≤ (ENNReal.ofReal _).toReal
  rw [ENNReal.toReal_sub_of_le (axisReachProb_antitone μ e (Nat.sub_le _ _)) (measure_ne_top _ _),
    ENNReal.toReal_ofReal (by positivity)]
  exact hreal

lemma dyadic_markov_ratio (l G c : ℕ) (h : G+c ≤ l) (W : ℝ) :
    ((4*2^(l-G-c) : ℕ) : ℝ)*W/((2^(l-G) : ℕ) : ℝ) = 4*W*(1/2 : ℝ)^c := by
  have he : l-G = (l-G-c)+c := by omega
  push_cast
  rw [show (2:ℝ)^(l-G) = (2:ℝ)^(l-G-c)*(2:ℝ)^c from by rw [← pow_add, ← he]]
  rw [div_pow,one_pow]
  field_simp

lemma commonBand_good_label {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : ∀ b, 0 < annealed μ 0 (nonBacktracking (axisDirection (placedAxis e b))))
    (J G c l m : ℕ) (hG : 0 < G) (hl : G+c ≤ l) (hlJ : l < J)
    (hΔ : (1/2 : ℝ)^G*((2:ℝ)^l*(axisWidthTail μ e (2^(l-1))).toReal) ≤ (1/2 : ℝ)^m) :
    letI : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) :=
      fun b => slabLaw_probability μ _ (hp b)
    let ν := fun b => slabLaw μ (axisDirection (placedAxis e b))
    (annealed μ 0).real (nonBacktracking (axisDirection e))^2 ≤
      4*(∫ Z, (firstCommonWidth (placedWidth e) Z : ℝ) ∂twoTapeLaw ν)*(1/2 : ℝ)^c +
      (∑ j ∈ Finset.Icc (l-(G+c)) l, (twoTapeLaw ν).real (commonBandContact e (2^j))) +
      (∫ a, slabRadius a ∂ν false)*(1/2 : ℝ)^J +
      ((annealed μ 0).real (nonBacktracking (axisDirection e)))⁻¹ *
      ((annealed μ 0).real (nonBacktracking (axisDirection (oppositeStep e))))⁻¹ *
        ((24 / posteriorExponent)*((d+1)*6*J)*(m+1)^2*(1/2 : ℝ)^m) := by
  let : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) := fun b => slabLaw_probability μ _ (hp b)
  let ν := fun b => slabLaw μ (axisDirection (placedAxis e b))
  have hlpos : 0 < (2:ℕ)^l := by positivity
  have hh := commonBand_lower_real μ hell e hp (2^l) (2^J) (2^(l-G)) (2^(l+1)) m
    (l-G-c) l (by positivity) (Nat.pow_le_pow_right (by norm_num) hlJ.le)
    (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)) (by rw [pow_succ];omega)
    (by omega) (by positivity) (by rw [pow_succ];omega)
    ((axis_delta_dyadic μ hell e (hp false) l G hG (by omega)).trans (ENNReal.ofReal_le_ofReal hΔ))
  dsimp only at hh
  rw [dyadic_markov_ratio l G c hl,show l-G-c = l-(G+c) by omega] at hh
  have hrad : (∫ a, slabRadius a ∂ν false)/((2^J : ℕ) : ℝ) =
      (∫ a, slabRadius a ∂ν false)*(1/2 : ℝ)^J := by push_cast;rw [div_pow,one_pow];ring
  rw [hrad] at hh
  have hlog := axisCube_log_bound e J (by omega)
  have hc : 0 ≤ ((annealed μ 0).real (nonBacktracking (axisDirection e)))⁻¹ *
      ((annealed μ 0).real (nonBacktracking (axisDirection (oppositeStep e))))⁻¹ := by positivity
  have hm : 0 ≤ (24/posteriorExponent)*(m+1)^2*(1/2 : ℝ)^m := by have := posteriorExponent_pos;positivity
  have hb := mul_le_mul_of_nonneg_left hlog (mul_nonneg hc hm)
  nlinarith

lemma sum_trailing_windows (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j) (J w : ℕ) :
    (∑ l ∈ Finset.range J, ∑ j ∈ Finset.Icc (l-w) l, p j) ≤
      (w+1)*∑ j ∈ Finset.range J, p j := by
  classical
  have hid (l : ℕ) (hl : l ∈ Finset.range J) :
      (∑ j ∈ Finset.Icc (l-w) l, p j) =
        ∑ j ∈ Finset.range J, if j ≤ l ∧ l ≤ j+w then p j else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Icc]
    have hl' := Finset.mem_range.mp hl
    omega
  rw [Finset.sum_congr rfl hid,Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  rw [← Finset.sum_filter,Finset.sum_const, nsmul_eq_mul]
  have hc : ((Finset.range J).filter (fun l => j ≤ l ∧ l ≤ j+w)).card ≤ w+1 := by
    have hs : (Finset.range J).filter (fun l => j ≤ l ∧ l ≤ j+w) ⊆ Finset.Icc j (j+w) := by
      intro l hl
      exact Finset.mem_Icc.mpr (Finset.mem_filter.mp hl).2
    have hh := Finset.card_le_card hs
    simp only [Nat.card_Icc] at hh
    omega
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (hp j)

lemma sum_early_labels (J w : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    (∑ l ∈ Finset.range J, if l < w then c else 0) ≤ w*c := by
  classical
  rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
  have hs : ((Finset.range J).filter (fun l => l < w)) ⊆ Finset.range w := by
    intro l hl
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hl).2
  have hh := Finset.card_le_card hs
  simp only [Finset.card_range] at hh
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hh) hc

lemma window_count_lower (p a : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j) (ha : ∀ j, 0 ≤ a j)
    (S C c : ℝ) (hS : ∀ J, ∑ l ∈ Finset.range J, a l ≤ S)
    (hC : 0 < C) (hc : 0 < c) (hSC : 4*S ≤ C)
    (J w : ℕ) (hwJ : 4*w ≤ J)
    (hgood : ∀ l, w ≤ l → l < J → a l ≤ C/J → c ≤ ∑ j ∈ Finset.Icc (l-w) l, p j) :
    c*J/2 ≤ (w+1)*∑ j ∈ Finset.range J, p j := by
  classical
  by_cases hJ : J = 0
  · subst J
    simp
  have hJ0 : (0:ℝ) < J := by exact_mod_cast Nat.pos_of_ne_zero hJ
  have hpoint (l : ℕ) (hl : l ∈ Finset.range J) :
      c ≤ (if l < w then c else 0)+(∑ j ∈ Finset.Icc (l-w) l, p j)+(c*J/C)*a l := by
    have hs : 0 ≤ ∑ j ∈ Finset.Icc (l-w) l, p j := Finset.sum_nonneg (fun j _ => hp j)
    have he : 0 ≤ (c*J/C)*a l := mul_nonneg (by positivity) (ha l)
    by_cases hlw : l < w
    · simp only [hlw,↓reduceIte]
      linarith
    simp only [hlw,↓reduceIte,zero_add]
    by_cases hg : a l ≤ C/J
    · linarith [hgood l (by omega) (Finset.mem_range.mp hl) hg]
    · have hh : C/J ≤ a l := le_of_not_ge hg
      have hm := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ c*J/C)
      have hid : (c*J/C)*(C/J) = c := by field_simp
      rw [hid] at hm
      linarith
  have hh := Finset.sum_le_sum hpoint
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,
    ← Finset.mul_sum] at hh
  have hearly := sum_early_labels J w c hc.le
  have hwindows := sum_trailing_windows p hp J w
  have htail := mul_le_mul_of_nonneg_left (hS J) (by positivity : 0 ≤ c*J/C)
  have htail' : (c*J/C)*S ≤ c*J/4 := by
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<4)).mpr
    have hh := mul_le_mul_of_nonneg_left hSC (by positivity : 0 ≤ c*J/C)
    have hid : (c*J/C)*C = c*J := by field_simp
    rw [hid] at hh
    nlinarith
  have hearly' : w*c ≤ c*J/4 := by
    have hw : (4:ℝ)*w ≤ J := by exact_mod_cast hwJ
    nlinarith
  linarith

lemma tendsto_dyadic_quadratic :
    Tendsto (fun t : ℕ => ((t:ℝ)+1)^2*(1/2 : ℝ)^t) atTop (𝓝 0) := by
  have h0 := tendsto_pow_const_mul_const_pow_of_lt_one 0 (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)
  have h1 := tendsto_pow_const_mul_const_pow_of_lt_one 1 (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)
  have h2 := tendsto_pow_const_mul_const_pow_of_lt_one 2 (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)
  have hh := (h2.add (h1.const_mul 2)).add h0
  convert hh using 1 <;> simp only [pow_zero,pow_one,mul_zero,add_zero]
  ext t
  ring

lemma eventually_dyadic_quadratic_lt (D ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℕ in atTop, D*(((t:ℝ)+1)^2*(1/2 : ℝ)^t) < ε := by
  have hh := tendsto_dyadic_quadratic.const_mul D
  simp only [mul_zero] at hh
  exact hh.eventually (gt_mem_nhds hε)

lemma dyadic_decay_le_quadratic (t : ℕ) :
    (1/2 : ℝ)^t ≤ ((t:ℝ)+1)^2*(1/2 : ℝ)^t := by
  have ht : (0:ℝ) ≤ t := Nat.cast_nonneg _
  have hp : (0:ℝ) ≤ (1/2:ℝ)^t := by positivity
  nlinarith [mul_le_mul_of_nonneg_right (show (1:ℝ) ≤ ((t:ℝ)+1)^2 by nlinarith) hp]

lemma self_dyadic_decay_le_quadratic (t : ℕ) :
    t*(1/2 : ℝ)^t ≤ ((t:ℝ)+1)^2*(1/2 : ℝ)^t := by
  have ht : (0:ℝ) ≤ t := Nat.cast_nonneg _
  exact mul_le_mul_of_nonneg_right (by nlinarith : (t:ℝ) ≤ ((t:ℝ)+1)^2) (by positivity)

lemma dyadic_decay_antitone : Antitone (fun t : ℕ => (1/2 : ℝ)^t) := by
  intro a b hab
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hab

lemma dyadic_power_cancel (a b : ℕ) :
    (2:ℝ)^a*(1/2 : ℝ)^(a+b) = (1/2 : ℝ)^b := by
  simp only [pow_add,div_pow,one_pow]
  field_simp

lemma dyadic_delta_identity (a t : ℕ) :
    (1/2 : ℝ)^(2*t)*((2:ℝ)^t/(2:ℝ)^a) = (1/2 : ℝ)^(a+t) := by
  simp only [show 2*t=t+t by omega,pow_add,div_pow,one_pow]
  field_simp

lemma dyadic_large_parameters (K c : ℕ) (hK : 0 < K)
    (C R E B P : ℝ) (hC : 0 < C) (hR : 0 ≤ R) (hE : 0 ≤ E)
    (hB : 0 ≤ B) (hP : 0 < P) :
    ∃ t : ℕ, c+1 ≤ t ∧ 0 < t ∧
      C ≤ (2:ℝ)^t ∧
      4*(2*t+c) ≤ (2:ℕ)^(2*K*t) ∧
      R*(1/2 : ℝ)^((2:ℕ)^(2*K*t)) ≤ P/8 ∧
      E*((2:ℕ)^(2*K*t) : ℝ)*(((2*K+1)*t : ℕ)+1 : ℝ)^2*(1/2 : ℝ)^((2*K+1)*t) ≤ P/8 ∧
      ((K*t : ℕ):ℝ)*Real.log 2*(2:ℝ)^(K*t)*B ≤ ((2:ℕ)^(2*K*t) : ℝ) := by
  have hP8 : (0:ℝ) < P/8 := by positivity
  obtain ⟨t,ht,htC,htwin,htR,htE,htB⟩ := ((eventually_ge_atTop (c+1)).and
    ((eventually_dyadic_quadratic_lt C 1 (by norm_num)).and
    ((eventually_dyadic_quadratic_lt (8+4*c) 1 (by norm_num)).and
    ((eventually_dyadic_quadratic_lt R (P/8) hP8).and
    ((eventually_dyadic_quadratic_lt (E*(2*K+2)^2) (P/8) hP8).and
    (eventually_dyadic_quadratic_lt (K*Real.log 2*B) 1 (by norm_num))))))).exists
  have htpos : 0 < t := by omega
  have ht0 : (0:ℝ) ≤ t := Nat.cast_nonneg _
  have hK0 : (0:ℝ) ≤ K := Nat.cast_nonneg _
  have hc0 : (0:ℝ) ≤ c := Nat.cast_nonneg _
  have htKt : t ≤ K*t := by nlinarith only [hK]
  have ht2Kt : t ≤ 2*K*t := by nlinarith only [htKt]
  have hpow : (2:ℕ)^t ≤ 2^(2*K*t) := Nat.pow_le_pow_right (by norm_num) ht2Kt
  have htJ : t ≤ (2:ℕ)^(2*K*t) := (Nat.lt_two_pow_self (n := t)).le.trans hpow
  have hCpow : C ≤ (2:ℝ)^t := by
    have hh := (mul_le_mul_of_nonneg_left (dyadic_decay_le_quadratic t) hC.le).trans htC.le
    simpa only [div_pow,one_pow,← div_eq_mul_one_div,div_le_one (by positivity : (0:ℝ)<(2:ℝ)^t)] using hh
  have hw : 4*(2*t+c) ≤ (2:ℕ)^t := by
    have hpol : (4:ℝ)*(2*t+c) ≤ (8+4*c)*((t:ℝ)+1)^2 := by
      have hx : (0:ℝ) ≤ (8+4*c)*(t:ℝ)^2+(8+8*c)*t+8 := by positivity
      nlinarith only [hx]
    have hh := (mul_le_mul_of_nonneg_right hpol (by positivity : (0:ℝ)≤(1/2:ℝ)^t)).trans (by nlinarith only [htwin] : (8+4*c)*((t:ℝ)+1)^2*(1/2:ℝ)^t ≤ 1)
    have hh' : (4:ℝ)*(2*t+c) ≤ (2:ℝ)^t := by
      simpa only [div_pow,one_pow,← div_eq_mul_one_div,div_le_one (by positivity : (0:ℝ)<(2:ℝ)^t)] using hh
    exact_mod_cast hh'
  have hr : R*(1/2 : ℝ)^((2:ℕ)^(2*K*t)) ≤ P/8 :=
    (mul_le_mul_of_nonneg_left ((dyadic_decay_antitone htJ).trans (dyadic_decay_le_quadratic t)) hR).trans htR.le
  have hm : ((2*K+1)*t : ℕ) = 2*K*t+t := by ring
  have hrealM : ((((2*K+1)*t : ℕ):ℝ)+1)^2 ≤ (2*K+2)^2*((t:ℝ)+1)^2 := by
    have hcmp : (((2*K+1)*t : ℕ):ℝ)+1 ≤ (2*K+2)*((t:ℝ)+1) := by
      push_cast
      nlinarith only [hK0,ht0]
    simpa only [mul_pow] using (sq_le_sq₀ (by positivity) (by positivity)).mpr hcmp
  have herror : E*((2:ℕ)^(2*K*t) : ℝ)*(((2*K+1)*t : ℕ)+1 : ℝ)^2*(1/2 : ℝ)^((2*K+1)*t) ≤ P/8 := by
    have hi : (2:ℝ)^(2*K*t)*(1/2 : ℝ)^((2*K+1)*t) = (1/2 : ℝ)^t := by
      rw [hm]
      exact dyadic_power_cancel (2*K*t) t
    have heq : E*((2:ℕ)^(2*K*t) : ℝ)*(((2*K+1)*t : ℕ)+1 : ℝ)^2*(1/2 : ℝ)^((2*K+1)*t) =
        E*((((2*K+1)*t : ℕ):ℝ)+1)^2*(1/2 : ℝ)^t := by
      calc
        _ = (E*((((2*K+1)*t : ℕ):ℝ)+1)^2)*((2:ℝ)^(2*K*t)*(1/2 : ℝ)^((2*K+1)*t)) := by push_cast;ring
        _ = _ := by rw [hi]
    rw [heq]
    have hm' := mul_le_mul_of_nonneg_left hrealM (mul_nonneg hE (by positivity : (0:ℝ)≤(1/2:ℝ)^t))
    have he' : E*(↑((2*K+1)*t)+1)^2*(1/2:ℝ)^t ≤ E*(2*K+2)^2*(((t:ℝ)+1)^2*(1/2:ℝ)^t) := by
      nlinarith only [hm']
    exact he'.trans htE.le
  have hcor : ((K*t : ℕ):ℝ)*Real.log 2*(2:ℝ)^(K*t)*B ≤ ((2:ℕ)^(2*K*t) : ℝ) := by
    have hcoef : 0 ≤ (K:ℝ)*Real.log 2*B := by positivity
    have hh := (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (dyadic_decay_antitone htKt) ht0 |>.trans (self_dyadic_decay_le_quadratic t)) hcoef).trans htB.le
    have hp2 : (2:ℝ)^(2*K*t) = (2:ℝ)^(K*t)*(2:ℝ)^(K*t) := by rw [← pow_add];congr 1;ring
    push_cast
    rw [hp2]
    have hh' : (K:ℝ)*Real.log 2*B*t ≤ (2:ℝ)^(K*t) := by
      have hx : ((K:ℝ)*Real.log 2*B*t)*(1/2:ℝ)^(K*t) ≤ 1 := by nlinarith only [hh]
      simpa only [div_pow,one_pow,← div_eq_mul_one_div,div_le_one (by positivity : (0:ℝ)<(2:ℝ)^(K*t))] using hx
    nlinarith only [mul_le_mul_of_nonneg_right hh' (by positivity : (0:ℝ)≤(2:ℝ)^(K*t))]
  exact ⟨t,ht,htpos,hCpow,hw.trans hpow,hr,herror,hcor⟩

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

lemma dyadic_entropy_contradiction (p a : ℕ → ℝ)
    (hp : ∀ j, 0 ≤ p j) (ha : ∀ j, 0 ≤ a j) (hs : Summable a)
    (P W R E A B : ℝ) (hP : 0 < P) (hW : 0 ≤ W) (hR : 0 ≤ R)
    (hE : 0 ≤ E) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hlower : ∀ (J G c l m : ℕ), 0 < G → G+c ≤ l → l < J →
      (1/2 : ℝ)^G*a l ≤ (1/2 : ℝ)^m →
      P ≤ W*(1/2 : ℝ)^c + (∑ j ∈ Finset.Icc (l-(G+c)) l, p j) +
        R*(1/2 : ℝ)^J + E*J*(m+1)^2*(1/2 : ℝ)^m)
    (hupper : ∀ J L : ℕ, (L*Real.log 2)*(∑ j ∈ Finset.range J, p j) ≤
      A*J+(L*Real.log 2)*(2:ℝ)^L*B) : False := by
  let S := ∑' j, a j
  let C := 4*S+1
  have hS0 : 0 ≤ S := tsum_nonneg ha
  have hC : 0 < C := by dsimp [C];linarith
  have hSC : 4*S ≤ C := by dsimp [C];linarith
  have hS (J : ℕ) : ∑ j ∈ Finset.range J, a j ≤ S :=
    Summable.sum_le_tsum _ (fun j _ => ha j) hs
  obtain ⟨c,hc⟩ := (eventually_dyadic_quadratic_lt W (P/4) (by positivity)).exists
  have hcsmall : W*(1/2 : ℝ)^c < P/4 :=
    (mul_le_mul_of_nonneg_left (dyadic_decay_le_quadratic c) hW).trans_lt hc
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨K,hK⟩ := exists_nat_gt (12*(A+1)/(P*Real.log 2))
  have hk0 : (0:ℝ) ≤ 12*(A+1)/(P*Real.log 2) := by positivity
  have hKpos : 0 < K := by exact_mod_cast (lt_of_le_of_lt hk0 hK)
  have hKbig : 3*(A+1) < P*K*Real.log 2/4 := by
    have hh := (div_lt_iff₀ (mul_pos hP hlog)).mp hK
    nlinarith only [hh]
  obtain ⟨t,htc,ht,hCt,hwJ,hr,herr,hcorr⟩ :=
    dyadic_large_parameters K c hKpos C R E B P hC hR hE hB hP
  let J := (2:ℕ)^(2*K*t)
  let w := 2*t+c
  have hJpos : (0:ℝ) < J := by dsimp [J];positivity
  have htpos : (0:ℝ) < t := by exact_mod_cast ht
  have hw : (w:ℝ)+1 ≤ 3*t := by
    have hh : (c:ℝ)+1 ≤ t := by exact_mod_cast htc
    dsimp [w]
    push_cast
    linarith only [hh]
  have hlabel (l : ℕ) (hwl : w ≤ l) (hlJ : l < J) (hgood : a l ≤ C/J) :
      P/2 ≤ ∑ j ∈ Finset.Icc (l-w) l, p j := by
    have hdelta : (1/2 : ℝ)^(2*t)*a l ≤ (1/2 : ℝ)^((2*K+1)*t) := by
      calc
        _ ≤ (1/2 : ℝ)^(2*t)*(C/J) := mul_le_mul_of_nonneg_left hgood (by positivity)
        _ ≤ (1/2 : ℝ)^(2*t)*((2:ℝ)^t/J) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hCt hJpos.le) (by positivity)
        _ = _ := by
          dsimp [J]
          push_cast
          rw [dyadic_delta_identity]
          congr 1
          ring
    have hh := hlower J (2*t) c l ((2*K+1)*t) (by omega) hwl hlJ hdelta
    change P ≤ W*(1/2:ℝ)^c + (∑ j ∈ Finset.Icc (l-w) l, p j) + R*(1/2:ℝ)^J +
      E*J*((((2*K+1)*t : ℕ):ℝ)+1)^2*(1/2:ℝ)^((2*K+1)*t) at hh
    change R*(1/2:ℝ)^J ≤ P/8 at hr
    have herr' : E*J*((((2*K+1)*t : ℕ):ℝ)+1)^2*(1/2:ℝ)^((2*K+1)*t) ≤ P/8 := by
      simpa only [J,Nat.cast_pow,Nat.cast_ofNat] using herr
    linarith only [hh,hcsmall,hr,herr']
  have hc2 : 0 < P/2 := by positivity
  have hcount := window_count_lower p a hp ha S C (P/2) hS hC hc2 hSC J w hwJ hlabel
  have hu := hupper J (K*t)
  have hu' : (((K*t : ℕ):ℝ)*Real.log 2)*(∑ j ∈ Finset.range J,p j) ≤ (A+1)*J := by
    have hcorr' : ((K*t : ℕ):ℝ)*Real.log 2*(2:ℝ)^(K*t)*B ≤ (J:ℝ) := by
      simpa only [J,Nat.cast_pow,Nat.cast_ofNat] using hcorr
    linarith only [hu,hcorr']
  have hcoef : 0 ≤ ((K*t : ℕ):ℝ)*Real.log 2 := by positivity
  have hAJ : 0 ≤ (A+1)*(J:ℝ) := by positivity
  have hfinal : (P*K*Real.log 2/4)*(t:ℝ)*(J:ℝ) ≤ (3*(A+1))*(t:ℝ)*(J:ℝ) := by
    calc
      _ = (((K*t : ℕ):ℝ)*Real.log 2)*((P/2)*J/2) := by push_cast;ring
      _ ≤ (((K*t : ℕ):ℝ)*Real.log 2)*((w+1)*(∑ j ∈ Finset.range J,p j)) :=
        mul_le_mul_of_nonneg_left hcount hcoef
      _ = (w+1)*((((K*t : ℕ):ℝ)*Real.log 2)*(∑ j ∈ Finset.range J,p j)) := by ring
      _ ≤ (w+1)*((A+1)*J) := mul_le_mul_of_nonneg_left hu' (by positivity)
      _ ≤ (3*t)*((A+1)*J) := mul_le_mul_of_nonneg_right hw hAJ
      _ = _ := by ring
  have hf := le_of_mul_le_mul_right (le_of_mul_le_mul_right hfinal hJpos) htpos
  exact not_le_of_gt hKbig hf

lemma not_both_axis_nonBacktracking {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : ∀ b, 0 < annealed μ 0 (nonBacktracking (axisDirection (placedAxis e b)))) : False := by
  let : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) :=
    fun b => slabLaw_probability μ _ (hp b)
  let ν := fun b => slabLaw μ (axisDirection (placedAxis e b))
  let p (j : ℕ) := (twoTapeLaw ν).real (commonBandContact e (2^j))
  let a (l : ℕ) := (2:ℝ)^l*(axisWidthTail μ e (2^(l-1))).toReal
  let P := (annealed μ 0).real (nonBacktracking (axisDirection e))^2
  let W := 4*(∫ Z, (firstCommonWidth (placedWidth e) Z : ℝ) ∂twoTapeLaw ν)
  let R := ∫ a, slabRadius a ∂ν false
  let E := ((annealed μ 0).real (nonBacktracking (axisDirection e)))⁻¹ *
      ((annealed μ 0).real (nonBacktracking (axisDirection (oppositeStep e))))⁻¹ *
      (24/posteriorExponent)*((d+1)*6)
  have hpos : 0 < (annealed μ 0).real (nonBacktracking (axisDirection e)) :=
    ENNReal.toReal_pos (ne_of_gt (hp false)) (measure_ne_top _ _)
  have hP : 0 < P := by dsimp [P];positivity
  have hW : 0 ≤ W := mul_nonneg (by norm_num) (integral_nonneg (fun _ => Nat.cast_nonneg _))
  have hR : 0 ≤ R := integral_nonneg slabRadius_nonneg
  have hE : 0 ≤ E := by dsimp [E];have := posteriorExponent_pos;positivity
  obtain ⟨A,B,hA,hB,hupper⟩ := commonBand_entropy_upper μ hell e hp
  apply dyadic_entropy_contradiction p a (fun _ => measureReal_nonneg)
    (fun _ => mul_nonneg (by positivity) ENNReal.toReal_nonneg)
    (summable_shifted_axisTail μ hell e (hp false)) P W R E A B hP hW hR hE hA hB _ hupper
  intro J G c l m hG hl hlJ hΔ
  have hh := commonBand_good_label μ hell e hp J G c l m hG hl hlJ hΔ
  dsimp only at hh
  dsimp only [P,W,R,E,p,ν]
  nlinarith only [hh]

theorem directional_zero_one_oai (d : ℕ) (hd : 3 ≤ d)
    (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (ℓ : Fin d → ℝ) (hℓ : ℓ ≠ 0) :
    annealed μ 0 (escape ℓ) = 0 ∨ annealed μ 0 (escape ℓ) = 1 := by
  cases d with
  | zero => omega
  | succ d =>
    by_contra hh
    have hne0 : annealed μ 0 (escape ℓ) ≠ 0 := fun h => hh (Or.inl h)
    have hne1 : annealed μ 0 (escape ℓ) ≠ 1 := fun h => hh (Or.inr h)
    have h0 : 0 < annealed μ 0 (escape ℓ) := bot_lt_iff_ne_bot.mpr hne0
    have h1 : annealed μ 0 (escape ℓ) < 1 := lt_of_le_of_ne (prob_le_one) hne1
    obtain ⟨i,hi,hi'⟩ := mixed_direction_has_mixed_coordinate μ hell ℓ hℓ h0 h1
    apply not_both_axis_nonBacktracking μ hell (i,true)
    intro b
    cases b
    · simpa only [placedAxis, Bool.false_eq_true,↓reduceIte,axisDirection] using
        positive_nonBacktracking μ (Pi.single i 1) hi
    · change 0 < annealed μ 0 (nonBacktracking (axisDirection (oppositeStep (i,true))))
      rw [axisDirection_opposite]
      simpa only [axisDirection,↓reduceIte] using positive_nonBacktracking μ (-Pi.single i 1) hi'

end DirectionalZeroOne

end OAI
end
end

theorem solution : type_of% @OAI.DirectionalZeroOne.directional_zero_one_oai := @OAI.DirectionalZeroOne.directional_zero_one_oai
