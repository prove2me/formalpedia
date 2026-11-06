-- Prove2me | solution 1 for LinParamBandits.UEGeneral.regret_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T20:50:21.865329+00:00
-- url     : https://prove2.me/submissions/5829f5a7-351b-4079-bed1-151870dcb89d

import Mathlib
import Definitions.Def_LinParamBandits_UEGeneral_Model
import Definitions.Def_LinParamBandits_UEGeneral_UEPolicy
import Theorems.Thm_LinParamBandits_UEGeneral_inst_regret_bound
import Theorems.Thm_LinParamBandits_UEGeneral_potential_recursion

open MeasureTheory ProbabilityTheory

namespace UEGenB8Aux

open LinParamBandits.UEGeneral

variable {r : ℕ}

lemma measurable_stepZ (ψ : Policy r) (n : ℕ) :
    Measurable (fun q : LinParamBandits.LowerBound.Vec r × (LinParamBandits.LowerBound.History r n × ℝ) =>
      Fin.snoc (α := fun _ => LinParamBandits.LowerBound.Vec r × ℝ) q.2.1
        (ψ.act n q.2.1, inner ℝ (ψ.act n q.2.1) q.1 + q.2.2)) := by
  rw [measurable_pi_iff]
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
    have ha : Measurable (fun q : LinParamBandits.LowerBound.Vec r ×
        (LinParamBandits.LowerBound.History r n × ℝ) => ψ.act n q.2.1) :=
      (ψ.measurable_act n).comp (measurable_fst.comp measurable_snd)
    refine ha.prodMk ?_
    exact (Measurable.inner ha measurable_fst).add (measurable_snd.comp measurable_snd)
  · simp only [Fin.snoc_castSucc]
    exact (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)

lemma measurable_step (ψ : Policy r) (z : LinParamBandits.LowerBound.Vec r) (n : ℕ) :
    Measurable (fun p : LinParamBandits.LowerBound.History r n × ℝ =>
      Fin.snoc (α := fun _ => LinParamBandits.LowerBound.Vec r × ℝ) p.1
        (ψ.act n p.1, inner ℝ (ψ.act n p.1) z + p.2)) :=
  (measurable_stepZ ψ n).comp (measurable_const.prodMk measurable_id)

lemma isProb_histMeasure (ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ) [IsMarkovKernel ν]
    (z : LinParamBandits.LowerBound.Vec r) (ψ : Policy r) :
    ∀ n, IsProbabilityMeasure (histMeasure ν z ψ n)
  | 0 => by
      simp only [histMeasure]; infer_instance
  | n + 1 => by
      have := isProb_histMeasure ν z ψ n
      simp only [histMeasure]
      exact Measure.isProbabilityMeasure_map (measurable_step ψ z n).aemeasurable

lemma exists_kernel (ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ) [IsMarkovKernel ν]
    (ψ : Policy r) :
    ∀ n, ∃ K : Kernel (LinParamBandits.LowerBound.Vec r) (LinParamBandits.LowerBound.History r n),
      IsMarkovKernel K ∧ ∀ z, K z = histMeasure ν z ψ n
  | 0 => ⟨Kernel.const _ (Measure.dirac (Fin.elim0 : LinParamBandits.LowerBound.History r 0)),
      inferInstance, fun z => by simp [histMeasure]⟩
  | n + 1 => by
      obtain ⟨K, hK, hKz⟩ := exists_kernel ν ψ n
      let η : Kernel (LinParamBandits.LowerBound.Vec r × LinParamBandits.LowerBound.History r n) ℝ :=
        ν.comap (fun p => ψ.act n p.2) ((ψ.measurable_act n).comp measurable_snd)
      let C := K ⊗ₖ η
      let D := (Kernel.deterministic (fun z : LinParamBandits.LowerBound.Vec r => z) measurable_id) ×ₖ C
      refine ⟨D.map (fun q : LinParamBandits.LowerBound.Vec r × (LinParamBandits.LowerBound.History r n × ℝ) =>
          Fin.snoc (α := fun _ => LinParamBandits.LowerBound.Vec r × ℝ) q.2.1
            (ψ.act n q.2.1, inner ℝ (ψ.act n q.2.1) q.1 + q.2.2)),
        Kernel.IsMarkovKernel.map _ (measurable_stepZ ψ n), fun z => ?_⟩
      rw [Kernel.map_apply _ (measurable_stepZ ψ n), Kernel.prod_apply, Kernel.deterministic_apply,
        Measure.dirac_prod, Measure.map_map (measurable_stepZ ψ n) measurable_prodMk_left]
      have hC : C z = (histMeasure ν z ψ n) ⊗ₘ (ν.comap (ψ.act n) (ψ.measurable_act n)) := by
        simp only [C]
        rw [Kernel.compProd_apply_eq_compProd_sectR, hKz]
        congr 1
      rw [hC]
      simp only [histMeasure]
      rfl

/-- The admissible arm set of period `s + 1`: arms of `𝒰`, equal to `b_{s+1}` if `s < r`. -/
def admissible (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (b : Fin r → LinParamBandits.LowerBound.Vec r)
    (s : ℕ) : Set (LinParamBandits.LowerBound.Vec r) :=
  {v | v ∈ 𝒰 ∧ ∀ hs : s < r, v = b ⟨s, hs⟩}

lemma measurableSet_admissible (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰 : MeasurableSet 𝒰)
    (b : Fin r → LinParamBandits.LowerBound.Vec r) (s : ℕ) : MeasurableSet (admissible 𝒰 b s) := by
  by_cases hs : s < r
  · have : admissible 𝒰 b s = 𝒰 ∩ {b ⟨s, hs⟩} := by
      ext v; simp only [admissible, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_singleton_iff]
      exact ⟨fun h => ⟨h.1, h.2 hs⟩, fun h => ⟨h.1, fun _ => h.2⟩⟩
    rw [this]; exact h𝒰.inter (measurableSet_singleton _)
  · have : admissible 𝒰 b s = 𝒰 := by
      ext v; simp only [admissible, Set.mem_setOf_eq]
      exact ⟨fun h => h.1, fun h => ⟨h, fun h' => absurd h' hs⟩⟩
    rw [this]; exact h𝒰

lemma measurableSet_good (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰 : MeasurableSet 𝒰)
    (b : Fin r → LinParamBandits.LowerBound.Vec r) (n : ℕ) :
    MeasurableSet {h : LinParamBandits.LowerBound.History r n | ∀ s : Fin n, (h s).1 ∈ admissible 𝒰 b s} := by
  have : {h : LinParamBandits.LowerBound.History r n | ∀ s : Fin n, (h s).1 ∈ admissible 𝒰 b s} =
      ⋂ s : Fin n, (fun h : LinParamBandits.LowerBound.History r n => (h s).1) ⁻¹' admissible 𝒰 b s := by
    ext h; simp
  rw [this]
  exact MeasurableSet.iInter fun s =>
    (measurable_fst.comp (measurable_pi_apply s)) (measurableSet_admissible 𝒰 h𝒰 b s)

lemma ae_good (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰 : MeasurableSet 𝒰)
    (b : Fin r → LinParamBandits.LowerBound.Vec r)
    (ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ)
    (z : LinParamBandits.LowerBound.Vec r) (ψ : Policy r)
    (hact : ∀ t h, ψ.act t h ∈ 𝒰)
    (hinit : ∀ (t : ℕ) (h : LinParamBandits.LowerBound.History r t) (ht : t < r), ψ.act t h = b ⟨t, ht⟩) :
    ∀ n, ∀ᵐ h ∂(histMeasure ν z ψ n), ∀ s : Fin n, (h s).1 ∈ admissible 𝒰 b s
  | 0 => Filter.Eventually.of_forall (fun h s => Fin.elim0 s)
  | n + 1 => by
      have ih := ae_good 𝒰 h𝒰 b ν z ψ hact hinit n
      simp only [histMeasure]
      rw [ae_map_iff (measurable_step ψ z n).aemeasurable (measurableSet_good 𝒰 h𝒰 b (n + 1))]
      have hms : MeasurableSet {p : LinParamBandits.LowerBound.History r n × ℝ |
          ∀ s : Fin n, (p.1 s).1 ∈ admissible 𝒰 b s} :=
        measurable_fst (measurableSet_good 𝒰 h𝒰 b n)
      have h2 : ∀ᵐ p ∂((histMeasure ν z ψ n) ⊗ₘ (ν.comap (ψ.act n) (ψ.measurable_act n))),
          ∀ s : Fin n, (p.1 s).1 ∈ admissible 𝒰 b s := by
        apply Measure.ae_compProd_of_ae_ae hms
        filter_upwards [ih] with h hh
        exact Filter.Eventually.of_forall (fun _ => hh)
      filter_upwards [h2] with p hp
      intro s
      refine Fin.lastCases ?_ (fun j => ?_) s
      · simp only [Fin.snoc_last, Fin.val_last]
        exact ⟨hact n p.1, fun hs => hinit n p.1 hs⟩
      · simp only [Fin.snoc_castSucc, Fin.coe_castSucc]
        exact hp j

lemma bddAbove_image (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰c : IsCompact 𝒰)
    (z : LinParamBandits.LowerBound.Vec r) : BddAbove ((fun v => inner ℝ v z) '' 𝒰) :=
  (h𝒰c.image (by fun_prop : Continuous fun v : LinParamBandits.LowerBound.Vec r => inner ℝ v z)).bddAbove

lemma le_bestValue (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰c : IsCompact 𝒰)
    (u : LinParamBandits.LowerBound.Vec r) (hu : u ∈ 𝒰) (z : LinParamBandits.LowerBound.Vec r) :
    inner ℝ u z ≤ bestValue 𝒰 z :=
  le_csSup (bddAbove_image 𝒰 h𝒰c z) ⟨u, hu, rfl⟩

lemma bestValue_le_add (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰c : IsCompact 𝒰)
    (h𝒰ne : 𝒰.Nonempty) (ū : ℝ) (hnorm : ∀ u ∈ 𝒰, ‖u‖ ≤ ū) (z w : LinParamBandits.LowerBound.Vec r) :
    bestValue 𝒰 z ≤ bestValue 𝒰 w + ū * ‖z - w‖ := by
  unfold bestValue
  apply csSup_le (h𝒰ne.image _)
  rintro _ ⟨v, hv, rfl⟩
  have h1 : inner ℝ v z = inner ℝ v w + inner ℝ v (z - w) := by
    rw [inner_sub_right]; ring
  have h2 : inner ℝ v (z - w) ≤ ū * ‖z - w‖ :=
    (real_inner_le_norm v (z - w)).trans (by gcongr; exact hnorm v hv)
  have h3 : inner ℝ v w ≤ sSup ((fun v => inner ℝ v w) '' 𝒰) := le_bestValue 𝒰 h𝒰c v hv w
  linarith

lemma continuous_bestValue (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰c : IsCompact 𝒰)
    (h𝒰ne : 𝒰.Nonempty) (ū : ℝ) (hū : 0 ≤ ū) (hnorm : ∀ u ∈ 𝒰, ‖u‖ ≤ ū) :
    Continuous (fun z => bestValue 𝒰 z) := by
  have : LipschitzWith (Real.toNNReal ū) (fun z => bestValue 𝒰 z) := by
    apply LipschitzWith.of_le_add_mul
    intro z w
    rw [Real.coe_toNNReal _ hū, dist_eq_norm]
    exact bestValue_le_add 𝒰 h𝒰c h𝒰ne ū hnorm z w
  exact this.continuous

lemma abs_bestValue_le (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰c : IsCompact 𝒰)
    (h𝒰ne : 𝒰.Nonempty) (ū : ℝ) (hnorm : ∀ u ∈ 𝒰, ‖u‖ ≤ ū) (z : LinParamBandits.LowerBound.Vec r) :
    |bestValue 𝒰 z| ≤ ū * ‖z‖ := by
  rw [abs_le]
  obtain ⟨u, hu⟩ := h𝒰ne
  constructor
  · have h1 := le_bestValue 𝒰 h𝒰c u hu z
    have h2 : -inner ℝ u z ≤ ū * ‖z‖ :=
      (neg_le_abs _).trans ((abs_real_inner_le_norm u z).trans (by gcongr; exact hnorm u hu))
    linarith
  · have := bestValue_le_add 𝒰 h𝒰c ⟨u, hu⟩ ū hnorm z 0
    unfold bestValue at this ⊢
    simp only [inner_zero_right, sub_zero] at this
    have h0 : sSup ((fun v : LinParamBandits.LowerBound.Vec r => (0 : ℝ)) '' 𝒰) = 0 := by
      rw [Set.Nonempty.image_const ⟨u, hu⟩, csSup_singleton]
    linarith


/-- Restriction of a history of `T` periods to its first `t` periods. -/
def restr {t T : ℕ} (hle : t ≤ T) (h : LinParamBandits.LowerBound.History r T) :
    LinParamBandits.LowerBound.History r t :=
  fun s => h (Fin.castLE hle s)

lemma measurable_restr {t T : ℕ} (hle : t ≤ T) :
    Measurable (restr (r := r) hle) :=
  measurable_pi_lambda _ (fun s => measurable_pi_apply _)

lemma restr_snoc {t T : ℕ} (hle : t ≤ T) (p : LinParamBandits.LowerBound.History r T)
    (x : LinParamBandits.LowerBound.Vec r × ℝ) :
    restr (hle.trans (Nat.le_succ T)) (Fin.snoc (α := fun _ => LinParamBandits.LowerBound.Vec r × ℝ) p x) =
      restr hle p := by
  funext s
  simp only [restr]
  have : (Fin.castLE (hle.trans (Nat.le_succ T)) s : Fin (T + 1)) = Fin.castSucc (Fin.castLE hle s) :=
    Fin.ext rfl
  rw [this, Fin.snoc_castSucc]

lemma restr_snoc_self {T : ℕ} (p : LinParamBandits.LowerBound.History r T)
    (x : LinParamBandits.LowerBound.Vec r × ℝ) :
    restr (Nat.le_succ T) (Fin.snoc (α := fun _ => LinParamBandits.LowerBound.Vec r × ℝ) p x) = p := by
  funext s
  simp only [restr]
  have : (Fin.castLE (Nat.le_succ T) s : Fin (T + 1)) = Fin.castSucc s := Fin.ext rfl
  rw [this, Fin.snoc_castSucc]

lemma map_restr (ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ) [IsMarkovKernel ν]
    (z : LinParamBandits.LowerBound.Vec r) (ψ : Policy r) (t : ℕ) :
    ∀ T (hle : t ≤ T), (histMeasure ν z ψ T).map (restr hle) = histMeasure ν z ψ t := by
  intro T hle
  induction T, hle using Nat.le_induction with
  | base =>
      have : (restr (r := r) (le_refl t)) = id := by
        funext h s; simp [restr]
      rw [this, Measure.map_id]
  | succ T hle ih =>
      have := isProb_histMeasure ν z ψ T
      simp only [histMeasure]
      rw [Measure.map_map (measurable_restr _) (measurable_step ψ z T)]
      have hc : (restr (hle.trans (Nat.le_succ T))) ∘ (fun p : LinParamBandits.LowerBound.History r T × ℝ =>
          Fin.snoc (α := fun _ => LinParamBandits.LowerBound.Vec r × ℝ) p.1
            (ψ.act T p.1, inner ℝ (ψ.act T p.1) z + p.2)) = (restr hle) ∘ Prod.fst := by
        funext p
        simp only [Function.comp_apply]
        exact restr_snoc hle p.1 _
      rw [hc, ← Measure.map_map (measurable_restr _) measurable_fst]
      have hf := Measure.fst_compProd (histMeasure ν z ψ T) (ν.comap (ψ.act T) (ψ.measurable_act T))
      rw [Measure.fst] at hf
      rw [hf, ih]

lemma measurableSet_actRel (ψ : Policy r) (T : ℕ) :
    MeasurableSet {h : LinParamBandits.LowerBound.History r T |
      ∀ t (ht : t < T), (h ⟨t, ht⟩).1 = ψ.act t (restr ht.le h)} := by
  have : {h : LinParamBandits.LowerBound.History r T |
      ∀ t (ht : t < T), (h ⟨t, ht⟩).1 = ψ.act t (restr ht.le h)} =
      ⋂ s : Fin T, {h | (h ⟨s, s.isLt⟩).1 = ψ.act s (restr s.isLt.le h)} := by
    ext h; simp only [Set.mem_setOf_eq, Set.mem_iInter]
    exact ⟨fun H s => H s s.isLt, fun H t ht => H ⟨t, ht⟩⟩
  rw [this]
  refine MeasurableSet.iInter fun s => measurableSet_eq_fun ?_ ?_
  · exact measurable_fst.comp (measurable_pi_apply _)
  · exact (ψ.measurable_act s).comp (measurable_restr _)

lemma ae_actRel (ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ)
    (z : LinParamBandits.LowerBound.Vec r) (ψ : Policy r) :
    ∀ T, ∀ᵐ h ∂(histMeasure ν z ψ T), ∀ t (ht : t < T), (h ⟨t, ht⟩).1 = ψ.act t (restr ht.le h)
  | 0 => Filter.Eventually.of_forall (fun h t ht => absurd ht (Nat.not_lt_zero t))
  | T + 1 => by
      have ih := ae_actRel ν z ψ T
      simp only [histMeasure]
      rw [ae_map_iff (measurable_step ψ z T).aemeasurable (measurableSet_actRel ψ (T + 1))]
      have hms : MeasurableSet {p : LinParamBandits.LowerBound.History r T × ℝ |
          ∀ t (ht : t < T), (p.1 ⟨t, ht⟩).1 = ψ.act t (restr ht.le p.1)} :=
        measurable_fst (measurableSet_actRel ψ T)
      have h2 : ∀ᵐ p ∂((histMeasure ν z ψ T) ⊗ₘ (ν.comap (ψ.act T) (ψ.measurable_act T))),
          ∀ t (ht : t < T), (p.1 ⟨t, ht⟩).1 = ψ.act t (restr ht.le p.1) := by
        apply Measure.ae_compProd_of_ae_ae hms
        filter_upwards [ih] with h hh
        exact Filter.Eventually.of_forall (fun _ => hh)
      filter_upwards [h2] with p hp
      intro t ht
      rcases Nat.lt_succ_iff_lt_or_eq.mp ht with htT | rfl
      · have e : (⟨t, ht⟩ : Fin (T + 1)) = Fin.castSucc ⟨t, htT⟩ := rfl
        rw [e, Fin.snoc_castSucc, restr_snoc htT.le]
        exact hp t htT
      · have e : (⟨t, ht⟩ : Fin (t + 1)) = Fin.last t := rfl
        rw [e, Fin.snoc_last, restr_snoc_self]

lemma measurable_armSeq {T : ℕ} (t : ℕ) :
    Continuous (fun h : LinParamBandits.LowerBound.History r T => armSeq h t) := by
  by_cases ht : t < T
  · simp only [armSeq, dif_pos ht]
    exact continuous_fst.comp (continuous_apply _)
  · simp only [armSeq, dif_neg ht]
    exact continuous_const

lemma measurable_potential {T : ℕ} (t : ℕ) :
    Measurable (fun h : LinParamBandits.LowerBound.History r T => potential (armSeq h) t) := by
  have hg : ∀ s : Fin t, Continuous fun h : LinParamBandits.LowerBound.History r T => armSeq h s :=
    fun s => measurable_armSeq s
  have hf := measurable_armSeq (r := r) (T := T) t
  have hD : Continuous fun h : LinParamBandits.LowerBound.History r T =>
      design (fun s : Fin t => armSeq h s) := by
    unfold design
    fun_prop
  simp only [potential, quadForm, Cmat, Matrix.inv_def, Ring.inverse_eq_inv']
  have h1 : Measurable fun h : LinParamBandits.LowerBound.History r T =>
      ((design (fun s : Fin t => armSeq h s)).det)⁻¹ := (hD.matrix_det).measurable.inv
  have h2 := hD.matrix_adjugate
  simp only [dotProduct, Matrix.mulVec, Matrix.smul_apply, smul_eq_mul]
  refine Finset.measurable_sum _ (fun i _ => ?_)
  refine Measurable.mul ?_ (Finset.measurable_sum _ (fun j _ => ?_))
  · exact (continuous_apply i |>.comp (PiLp.continuous_ofLp 2 _ |>.comp hf)).measurable
  · refine (h1.mul ?_).mul ?_
    · exact ((continuous_apply j).comp ((continuous_apply i).comp h2)).measurable
    · exact (continuous_apply j |>.comp (PiLp.continuous_ofLp 2 _ |>.comp hf)).measurable

lemma sum_inv_sq_le (r : ℕ) (hr : 1 ≤ r) :
    ∀ T, r ≤ T → ∑ t ∈ Finset.Ico r T, (1 / (t : ℝ) ^ 2) ≤ 2 - 2 / (T : ℝ) := by
  intro T hT
  induction T, hT using Nat.le_induction with
  | base =>
      simp only [Finset.Ico_self, Finset.sum_empty]
      have : (1 : ℝ) ≤ r := by exact_mod_cast hr
      have : 2 / (r : ℝ) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
      linarith
  | succ T hle ih =>
      rw [Finset.sum_Ico_succ_top hle]
      have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast (hr.trans hle)
      have key : 1 / (T : ℝ) ^ 2 ≤ 2 / T - 2 / ((T + 1 : ℕ) : ℝ) := by
        push_cast
        rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      linarith

lemma instRegret_le (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰c : IsCompact 𝒰)
    (h𝒰ne : 𝒰.Nonempty) (ū : ℝ) (hnorm : ∀ u ∈ 𝒰, ‖u‖ ≤ ū) (z u : LinParamBandits.LowerBound.Vec r)
    (hu : u ∈ 𝒰) : |instRegret 𝒰 z u| ≤ 2 * ū * ‖z‖ := by
  have h1 := abs_bestValue_le 𝒰 h𝒰c h𝒰ne ū hnorm z
  have h2 : |inner ℝ u z| ≤ ū * ‖z‖ :=
    (abs_real_inner_le_norm u z).trans (by gcongr; exact hnorm u hu)
  unfold instRegret
  calc |bestValue 𝒰 z - inner ℝ u z| ≤ |bestValue 𝒰 z| + |inner ℝ u z| := abs_sub _ _
    _ ≤ _ := by linarith

lemma radiusFactor_le (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (σ₀ ubar lam0 : ℝ) (hσ₀ : 0 < σ₀)
    (t : ℕ) (ht : 1 ≤ t) :
    radiusFactor 𝒰 σ₀ ubar lam0 t ≤ alpha σ₀ ubar lam0 * Real.sqrt r * Real.log t := by
  have hL : 0 ≤ Real.log t := Real.log_natCast_nonneg t
  have hα : 0 ≤ alpha σ₀ ubar lam0 := by unfold alpha; positivity
  have hw : width 𝒰 t ≤ (r : ℝ) * Real.log t := by
    unfold width
    split_ifs
    · exact min_le_left _ _
    · exact le_rfl
  unfold radiusFactor
  rw [mul_assoc, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hα
  calc Real.sqrt (Real.log t) * Real.sqrt (width 𝒰 t) ≤
      Real.sqrt (Real.log t) * Real.sqrt ((r : ℝ) * Real.log t) := by
        gcongr
    _ = Real.sqrt r * Real.log t := by
        rw [Real.sqrt_mul (by positivity), mul_comm (Real.sqrt (r : ℝ)), ← mul_assoc,
          Real.mul_self_sqrt hL]
        ring

lemma cs_step (r T : ℕ) (hr : 1 ≤ r) (P : ℕ → ℝ) (hP : ∀ t ∈ Finset.Ico r T, 0 ≤ P t) :
    ∑ t ∈ Finset.Ico r T, Real.log t * Real.sqrt (P t) ≤
      Real.log T * Real.sqrt T * Real.sqrt (∑ t ∈ Finset.Ico r T, P t) := by
  have h1 := Real.sum_mul_le_sqrt_mul_sqrt (Finset.Ico r T) (fun t => Real.log t) (fun t => Real.sqrt (P t))
  have h2 : ∑ t ∈ Finset.Ico r T, Real.sqrt (P t) ^ 2 = ∑ t ∈ Finset.Ico r T, P t :=
    Finset.sum_congr rfl (fun t ht => Real.sq_sqrt (hP t ht))
  rw [h2] at h1
  refine h1.trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
  have hLT : 0 ≤ Real.log T := Real.log_natCast_nonneg T
  have h3 : ∑ t ∈ Finset.Ico r T, Real.log t ^ 2 ≤ T * Real.log T ^ 2 := by
    calc ∑ t ∈ Finset.Ico r T, Real.log t ^ 2 ≤ ∑ t ∈ Finset.Ico r T, Real.log T ^ 2 := by
          apply Finset.sum_le_sum
          intro t ht
          rw [Finset.mem_Ico] at ht
          have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast (hr.trans ht.1)
          have hl0 : 0 ≤ Real.log t := Real.log_nonneg ht1
          have hl : Real.log t ≤ Real.log T :=
            Real.log_le_log (by linarith) (by exact_mod_cast ht.2.le)
          exact pow_le_pow_left₀ hl0 hl 2
      _ = (T - r : ℕ) * Real.log T ^ 2 := by rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      _ ≤ T * Real.log T ^ 2 := by
          gcongr
          exact_mod_cast Nat.sub_le T r
  calc Real.sqrt (∑ t ∈ Finset.Ico r T, Real.log t ^ 2) ≤ Real.sqrt (T * Real.log T ^ 2) :=
        Real.sqrt_le_sqrt h3
    _ = Real.log T * Real.sqrt T := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hLT, mul_comm]

end UEGenB8Aux

open UEGenB8Aux LinParamBandits.UEGeneral in
theorem solution {r : ℕ} (hr : 2 ≤ r) {𝒰 : Set (LinParamBandits.LowerBound.Vec r)} (h𝒰c : IsCompact 𝒰) (h𝒰n : 𝒰.Nonempty)
    {ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ} [IsMarkovKernel ν] {b : Fin r → LinParamBandits.LowerBound.Vec r} {σ₀ ubar lam0 : ℝ}
    (hA : Assumption1 𝒰 ν b σ₀ ubar lam0) {ψ : Policy r} (hψ : IsUE 𝒰 b σ₀ ubar lam0 ψ)
    (T : ℕ) (hT : r + 1 ≤ T) (z : LinParamBandits.LowerBound.Vec r) :
    regret ν 𝒰 ψ z T ≤
      2 * ubar * ((r : ℝ) + 2) * ‖z‖ +
        2 * alpha σ₀ ubar lam0 * Real.sqrt r * Real.log T * Real.sqrt T *
          ∫ h, Real.sqrt (∑ t ∈ Finset.Ico r T, potential (armSeq h) t)
            ∂(histMeasure ν z ψ T) := by
  have hprob := isProb_histMeasure ν z ψ T
  set μ := histMeasure ν z ψ T with hμ
  have h𝒰m : MeasurableSet 𝒰 := h𝒰c.isClosed.measurableSet
  have hσ₀ := hA.σ₀_pos
  have hubar := hA.ubar_pos
  have hlam0 := hA.lam0_pos
  set α := alpha σ₀ ubar lam0 with hαdef
  have hα : 0 ≤ α := by simp only [hαdef, alpha]; positivity
  have hrT : r ≤ T := by omega
  have hnz := norm_nonneg z
  -- consequences of the a.s. structure of the history
  have hgood := ae_good 𝒰 h𝒰m b ν z ψ hψ.act_mem hψ.act_init T
  have hrel := ae_actRel ν z ψ T
  have hinit : ∀ h : LinParamBandits.LowerBound.History r T,
      (∀ s : Fin T, (h s).1 ∈ admissible 𝒰 b s) → ∀ (k : ℕ) (hk : k < r), armSeq h k = b ⟨k, hk⟩ := by
    intro h hg k hk
    have hkT : k < T := by omega
    simp only [armSeq, dif_pos hkT]
    exact (hg ⟨k, hkT⟩).2 hk
  have hmem : ∀ h : LinParamBandits.LowerBound.History r T,
      (∀ s : Fin T, (h s).1 ∈ admissible 𝒰 b s) → ∀ t, t < T → armSeq h t ∈ 𝒰 := by
    intro h hg t ht
    simp only [armSeq, dif_pos ht]
    exact (hg ⟨t, ht⟩).1
  have hnormU : ∀ h : LinParamBandits.LowerBound.History r T,
      (∀ s : Fin T, (h s).1 ∈ admissible 𝒰 b s) → ∀ s, ‖armSeq h s‖ ≤ ubar := by
    intro h hg s
    by_cases hs : s < T
    · exact hA.norm_le _ (hmem h hg s hs)
    · simp only [armSeq, dif_neg hs, norm_zero]; exact hubar.le
  have hrec : ∀ h : LinParamBandits.LowerBound.History r T,
      (∀ s : Fin T, (h s).1 ∈ admissible 𝒰 b s) → ∀ t, r ≤ t →
        0 ≤ potential (armSeq h) t ∧ potential (armSeq h) t ≤ ubar ^ 2 / lam0 := by
    intro h hg t ht
    have := potential_recursion hr hubar hlam0 hA.b_minEig (armSeq h) (hinit h hg) (hnormU h hg) t ht
    exact ⟨this.1, this.2.1⟩
  -- the bad events of Lemma B.7
  let B : (t : ℕ) → Set (LinParamBandits.LowerBound.History r t) := fun t =>
    {h | 2 * radiusFactor 𝒰 σ₀ ubar lam0 t * wnorm (Cmat (armsOf h)) (ψ.act t h) <
          instRegret 𝒰 z (ψ.act t h)}
  let S : ℕ → Set (LinParamBandits.LowerBound.History r T) := fun t =>
    toMeasurable μ {h | ∃ ht : t ≤ T, restr ht h ∈ B t}
  have hSm : ∀ t, MeasurableSet (S t) := fun t => measurableSet_toMeasurable _ _
  have hSle : ∀ t ∈ Finset.Ico r T, μ.real (S t) ≤ 1 / (t : ℝ) ^ 2 := by
    intro t ht
    rw [Finset.mem_Ico] at ht
    have hle : t ≤ T := ht.2.le
    have hset : {h : LinParamBandits.LowerBound.History r T | ∃ ht : t ≤ T, restr ht h ∈ B t} =
        restr hle ⁻¹' B t := by
      ext h; simp only [Set.mem_setOf_eq, Set.mem_preimage]
      exact ⟨fun ⟨_, h'⟩ => h', fun h' => ⟨hle, h'⟩⟩
    have h1 : μ (S t) ≤ ENNReal.ofReal (1 / (t : ℝ) ^ 2) := by
      simp only [S]
      rw [measure_toMeasurable, hset]
      calc μ (restr hle ⁻¹' B t) ≤ (μ.map (restr hle)) (B t) :=
            Measure.le_map_apply (measurable_restr hle).aemeasurable _
        _ = histMeasure ν z ψ t (B t) := by rw [hμ, map_restr ν z ψ t T hle]
        _ ≤ _ := inst_regret_bound hr h𝒰c h𝒰n hA hψ t ht.1 z
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) h1
  -- the dominating function
  set P : LinParamBandits.LowerBound.History r T → ℝ := fun h =>
    Real.sqrt (∑ t ∈ Finset.Ico r T, potential (armSeq h) t) with hPdef
  set cc := 2 * α * Real.sqrt r * Real.log T * Real.sqrt T with hcc
  set G : LinParamBandits.LowerBound.History r T → ℝ := fun h =>
    (2 * ubar * ‖z‖ * r + 2 * ubar * ‖z‖ * ∑ t ∈ Finset.Ico r T, (S t).indicator 1 h) + cc * P h
    with hGdef
  set q : LinParamBandits.LowerBound.History r T → ℝ := fun h =>
    ∑ t ∈ Finset.range T, instRegret 𝒰 z (armSeq h t) with hqdef
  -- pathwise bound
  have hpath : ∀ᵐ h ∂μ, q h ≤ G h := by
    filter_upwards [hgood, hrel] with h hg hr'
    simp only [hqdef, hGdef]
    rw [← Finset.sum_range_add_sum_Ico _ hrT]
    have e1 : ∑ t ∈ Finset.range r, instRegret 𝒰 z (armSeq h t) ≤ 2 * ubar * ‖z‖ * r := by
      calc ∑ t ∈ Finset.range r, instRegret 𝒰 z (armSeq h t) ≤
          ∑ t ∈ Finset.range r, 2 * ubar * ‖z‖ := by
            apply Finset.sum_le_sum
            intro t ht
            rw [Finset.mem_range] at ht
            exact (le_abs_self _).trans
              (instRegret_le 𝒰 h𝒰c h𝒰n ubar hA.norm_le z _ (hmem h hg t (by omega)))
        _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    have e2 : ∀ t ∈ Finset.Ico r T, instRegret 𝒰 z (armSeq h t) ≤
        2 * ubar * ‖z‖ * (S t).indicator 1 h +
          2 * α * Real.sqrt r * (Real.log t * Real.sqrt (potential (armSeq h) t)) := by
      intro t ht
      rw [Finset.mem_Ico] at ht
      have htT := ht.2
      have harm : armSeq h t = ψ.act t (restr htT.le h) := by
        simp only [armSeq, dif_pos htT]; exact hr' t htT
      have hnn : 0 ≤ 2 * α * Real.sqrt r * (Real.log t * Real.sqrt (potential (armSeq h) t)) := by
        have := Real.log_natCast_nonneg t
        positivity
      by_cases hB : restr htT.le h ∈ B t
      · have hS : h ∈ S t := subset_toMeasurable _ _ ⟨htT.le, hB⟩
        rw [Set.indicator_of_mem hS, Pi.one_apply, mul_one]
        have := (le_abs_self _).trans
          (instRegret_le 𝒰 h𝒰c h𝒰n ubar hA.norm_le z _ (hmem h hg t htT))
        linarith
      · have hind : 0 ≤ (S t).indicator (1 : LinParamBandits.LowerBound.History r T → ℝ) h :=
          Set.indicator_nonneg (fun _ _ => zero_le_one) _
        simp only [B, Set.mem_setOf_eq, not_lt] at hB
        have hw : wnorm (Cmat (armsOf (restr htT.le h))) (ψ.act t (restr htT.le h)) =
            Real.sqrt (potential (armSeq h) t) := by
          have ha : armsOf (restr htT.le h) = fun s : Fin t => armSeq h s := by
            funext s
            have hs : (s : ℕ) < T := s.isLt.trans htT
            simp only [armsOf, restr, armSeq, dif_pos hs]
            rfl
          rw [ha, ← harm]
          rfl
        rw [hw, ← harm] at hB
        have hrf := radiusFactor_le 𝒰 σ₀ ubar lam0 hσ₀ t (by omega)
        have hsq := Real.sqrt_nonneg (potential (armSeq h) t)
        have : 2 * radiusFactor 𝒰 σ₀ ubar lam0 t * Real.sqrt (potential (armSeq h) t) ≤
            2 * α * Real.sqrt r * (Real.log t * Real.sqrt (potential (armSeq h) t)) := by
          have := mul_le_mul_of_nonneg_right hrf hsq
          nlinarith
        have h0 : 0 ≤ 2 * ubar * ‖z‖ * (S t).indicator 1 h := mul_nonneg (by positivity) hind
        linarith
    have e3 := Finset.sum_le_sum e2
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at e3
    have e4 := cs_step r T (by omega) (fun t => potential (armSeq h) t)
      (fun t ht => (hrec h hg t (Finset.mem_Ico.mp ht).1).1)
    have hc0 : 0 ≤ 2 * α * Real.sqrt r := by positivity
    have e5 := mul_le_mul_of_nonneg_left e4 hc0
    simp only [hPdef, hcc]
    nlinarith
  -- integrability
  have hPmeas : Measurable P := by
    simp only [hPdef]
    exact (Finset.measurable_sum _ (fun t _ => measurable_potential t)).sqrt
  have hPint : Integrable P μ := by
    refine Integrable.of_bound hPmeas.aestronglyMeasurable (Real.sqrt (T * (ubar ^ 2 / lam0))) ?_
    filter_upwards [hgood] with h hg
    simp only [hPdef]
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    apply Real.sqrt_le_sqrt
    calc ∑ t ∈ Finset.Ico r T, potential (armSeq h) t ≤ ∑ t ∈ Finset.Ico r T, ubar ^ 2 / lam0 :=
          Finset.sum_le_sum (fun t ht => (hrec h hg t (Finset.mem_Ico.mp ht).1).2)
      _ = (T - r : ℕ) * (ubar ^ 2 / lam0) := by rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      _ ≤ T * (ubar ^ 2 / lam0) := by
          gcongr
          exact_mod_cast Nat.sub_le T r
  have hIint : ∀ t, Integrable ((S t).indicator (1 : LinParamBandits.LowerBound.History r T → ℝ)) μ :=
    fun t => (integrable_const (1 : ℝ)).indicator (hSm t)
  have hGint : Integrable G μ := by
    simp only [hGdef]
    exact ((integrable_const _).add ((integrable_finsetSum _ (fun t _ => hIint t)).const_mul _)).add
      (hPint.const_mul _)
  set f : LinParamBandits.LowerBound.History r T → ℝ := fun h =>
    ∑ t ∈ Finset.range T, inner ℝ (armSeq h t) z with hfdef
  have hfint : Integrable f μ := by
    have hc : Continuous f := by
      simp only [hfdef]
      exact continuous_finset_sum _ (fun t _ => (measurable_armSeq t).inner continuous_const)
    refine Integrable.of_bound hc.aestronglyMeasurable (T * (ubar * ‖z‖)) ?_
    filter_upwards [hgood] with h hg
    simp only [hfdef]
    calc ‖∑ t ∈ Finset.range T, inner ℝ (armSeq h t) z‖ ≤
        ∑ t ∈ Finset.range T, ‖inner ℝ (armSeq h t) z‖ := norm_sum_le _ _
      _ ≤ ∑ t ∈ Finset.range T, ubar * ‖z‖ := by
          apply Finset.sum_le_sum
          intro t _
          rw [Real.norm_eq_abs]
          exact (abs_real_inner_le_norm _ _).trans (by gcongr; exact hnormU h hg t)
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hqf : q = fun h => (T : ℝ) * bestValue 𝒰 z - f h := by
    funext h
    simp only [hqdef, hfdef, instRegret, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
  have hqint : Integrable q μ := by
    rw [hqf]; exact (integrable_const _).sub hfint
  have hreg : regret ν 𝒰 ψ z T = ∫ h, q h ∂μ := by
    rw [hqf, integral_sub (integrable_const _) hfint, integral_const, probReal_univ, one_smul]
    unfold regret
    congr 1
    apply integral_congr_ae
    filter_upwards with h
    simp only [hfdef]
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro s _
    simp only [armSeq, dif_pos s.isLt]
  -- integrate
  have hInt : ∫ h, G h ∂μ = (2 * ubar * ‖z‖ * r + 2 * ubar * ‖z‖ * ∑ t ∈ Finset.Ico r T, μ.real (S t)) +
      cc * ∫ h, P h ∂μ := by
    simp only [hGdef]
    have hB1 : Integrable (fun h => 2 * ubar * ‖z‖ * ∑ t ∈ Finset.Ico r T,
        (S t).indicator (1 : LinParamBandits.LowerBound.History r T → ℝ) h) μ :=
      (integrable_finsetSum _ (fun t _ => hIint t)).const_mul _
    rw [integral_add (μ := μ) (f := fun h => 2 * ubar * ‖z‖ * r + 2 * ubar * ‖z‖ * ∑ t ∈ Finset.Ico r T,
        (S t).indicator (1 : LinParamBandits.LowerBound.History r T → ℝ) h) (g := fun h => cc * P h)
        ((integrable_const _).add hB1) (hPint.const_mul _)]
    rw [integral_add (μ := μ) (f := fun _ => 2 * ubar * ‖z‖ * r) (integrable_const _) hB1]
    rw [integral_const, probReal_univ, one_smul, integral_const_mul, integral_const_mul,
      integral_finsetSum _ (fun t _ => hIint t)]
    congr 3
    apply Finset.sum_congr rfl
    intro t _
    exact integral_indicator_one (hSm t)
  have hsumS : ∑ t ∈ Finset.Ico r T, μ.real (S t) ≤ 2 := by
    calc ∑ t ∈ Finset.Ico r T, μ.real (S t) ≤ ∑ t ∈ Finset.Ico r T, 1 / (t : ℝ) ^ 2 :=
          Finset.sum_le_sum hSle
      _ ≤ 2 - 2 / (T : ℝ) := sum_inv_sq_le r (by omega) T hrT
      _ ≤ 2 := by have : (0 : ℝ) ≤ 2 / T := by positivity
                  linarith
  rw [hreg]
  calc ∫ h, q h ∂μ ≤ ∫ h, G h ∂μ := integral_mono_ae hqint hGint hpath
    _ = _ := hInt
    _ ≤ (2 * ubar * ‖z‖ * r + 2 * ubar * ‖z‖ * 2) + cc * ∫ h, P h ∂μ := by
        have : 0 ≤ 2 * ubar * ‖z‖ := by positivity
        nlinarith
    _ = _ := by simp only [hcc, hPdef]; ring
