-- Prove2me | solution 1 for MartOT.Product.theorem_6_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T05:20:41.170547+00:00
-- url     : https://prove2.me/submissions/75bfbc6f-2db0-4fe2-9ea1-f7429de940ee
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MartOT_Var_Setting
import Theorems.Thm_MartOT_Product_theorem_4_18
import Theorems.Thm_MartOT_Product_curtain_target_least
import Theorems.Thm_MartOT_Product_eq_16
import Theorems.Thm_MartOT_Product_strict_convex_integral_eq_iff
import Theorems.Thm_MartOT_Product_plan_determined_by_targets

open MeasureTheory

namespace LC5Aux

/-- `ν^π_A = proj^y_# π|_{A×ℝ}`. -/
noncomputable def tgt (π : Measure (ℝ × ℝ)) (A : Set ℝ) : Measure ℝ :=
  (π.restrict (A ×ˢ Set.univ)).map Prod.snd

lemma integralE_of_nonneg {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    MartOT.Var.integralE μ f = ((∫⁻ x, ENNReal.ofReal (f x) ∂μ : ENNReal) : EReal) := by
  unfold MartOT.Var.integralE ModelRiskOT.Duality.extIntegral
  have h0 : ∀ x, (-(f x : EReal)).toENNReal = 0 := fun x =>
    EReal.toENNReal_of_nonpos (by rw [← EReal.coe_neg]; exact_mod_cast neg_nonpos.mpr (hf x))
  simp only [h0, lintegral_zero, EReal.real_coe_toENNReal, EReal.coe_ennreal_zero, sub_zero]

lemma integralE_eq {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ) :
    MartOT.Var.integralE μ f = ((∫⁻ x, ENNReal.ofReal (f x) ∂μ : ENNReal) : EReal) -
      ((∫⁻ x, ENNReal.ofReal (-f x) ∂μ : ENNReal) : EReal) := by
  unfold MartOT.Var.integralE ModelRiskOT.Duality.extIntegral
  simp only [← EReal.coe_neg, EReal.real_coe_toENNReal]

lemma tgt_apply (π : Measure (ℝ × ℝ)) (A : Set ℝ) {B : Set ℝ} (hB : MeasurableSet B) :
    tgt π A B = π (Prod.snd ⁻¹' B ∩ A ×ˢ Set.univ) := by
  unfold tgt
  rw [Measure.map_apply measurable_snd hB, Measure.restrict_apply (measurable_snd hB)]

lemma tgt_mono (π : Measure (ℝ × ℝ)) {A A' : Set ℝ} (h : A ⊆ A') : tgt π A ≤ tgt π A' := by
  unfold tgt
  exact Measure.map_mono (Measure.restrict_mono (Set.prod_mono h le_rfl) le_rfl) measurable_snd

lemma tgt_le_of_plan {μ ν : Measure ℝ} {π : Measure (ℝ × ℝ)} (h : MartOT.Var.IsPlan μ ν π)
    (A : Set ℝ) : tgt π A ≤ ν := by
  rw [← h.2]; unfold tgt
  exact Measure.map_mono Measure.restrict_le_self measurable_snd

lemma isFinite_of_plan {μ ν : Measure ℝ} [IsFiniteMeasure μ] {π : Measure (ℝ × ℝ)}
    (h : MartOT.Var.IsPlan μ ν π) : IsFiniteMeasure π := by
  refine ⟨?_⟩
  have : π Set.univ = μ Set.univ := by
    rw [← h.1, Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ]
  rw [this]; exact measure_lt_top μ _

lemma inM_of_le {η ν : Measure ℝ} (h : η ≤ ν) (hν : MartOT.Var.InM ν) : MartOT.Var.InM η := by
  have := hν.1
  have : IsFiniteMeasure η := isFiniteMeasure_of_le ν h
  exact ⟨inferInstance, hν.2.mono_measure h⟩

lemma lintegral_tgt (π : Measure (ℝ × ℝ)) (A : Set ℝ) {g : ℝ → ENNReal} (hg : Measurable g) :
    ∫⁻ y, g y ∂(tgt π A) = ∫⁻ p in A ×ˢ Set.univ, g p.2 ∂π := by
  unfold tgt; rw [lintegral_map hg measurable_snd]

lemma lintegral_tgt_iUnion (π : Measure (ℝ × ℝ)) (u : ℕ → ℝ) (hu : Monotone u)
    {g : ℝ → ENNReal} (hg : Measurable g) :
    Monotone (fun n => ∫⁻ y, g y ∂(tgt π (Set.Iic (u n)))) ∧
    ∫⁻ y, g y ∂(tgt π (⋃ n, Set.Iic (u n))) = ⨆ n, ∫⁻ y, g y ∂(tgt π (Set.Iic (u n))) := by
  refine ⟨fun m n h => lintegral_mono' (tgt_mono π (Set.Iic_subset_Iic.mpr (hu h))) le_rfl, ?_⟩
  simp only [lintegral_tgt π _ hg]
  rw [Set.iUnion_prod_const]
  apply setLIntegral_iUnion_of_directed
  intro i j
  exact ⟨max i j, Set.prod_mono (Set.Iic_subset_Iic.mpr (hu (le_max_left i j))) le_rfl,
    Set.prod_mono (Set.Iic_subset_Iic.mpr (hu (le_max_right i j))) le_rfl⟩

lemma convex_lower_bound {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ) :
    ∃ C K : ℝ, ∀ x, -φ x ≤ C + K * |x| := by
  refine ⟨|φ 0|, |φ 0 - φ (-1)| + |φ 1 - φ 0|, fun x => ?_⟩
  have h0 := neg_abs_le (φ 0)
  have ha1 := abs_nonneg (φ 0 - φ (-1))
  have ha2 := abs_nonneg (φ 1 - φ 0)
  have hx0 := abs_nonneg x
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have h := hφ.secant_mono (a := 0) (x := x) (y := 1) trivial trivial trivial hx.ne
      (by norm_num) (by linarith)
    simp only [sub_zero, div_one] at h
    rw [div_le_iff_of_neg hx] at h
    have h1 : -(φ 1 - φ 0) * x ≤ |φ 1 - φ 0| * |x| := by
      rw [abs_of_neg hx, neg_mul, ← mul_neg]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) (neg_pos.mpr hx).le
    nlinarith
  · subst hx; simp only [abs_zero, mul_zero, add_zero]; exact neg_le_abs _
  · have h := hφ.secant_mono (a := 0) (x := -1) (y := x) trivial trivial trivial (by norm_num)
      hx.ne' (by linarith)
    have e : (φ (-1) - φ 0) / (-1 - 0) = φ 0 - φ (-1) := by ring
    rw [e, sub_zero, le_div_iff₀ hx] at h
    have h1 : -(φ 0 - φ (-1)) * x ≤ |φ 0 - φ (-1)| * |x| := by
      rw [abs_of_pos hx]
      exact mul_le_mul_of_nonneg_right (by linarith [neg_abs_le (φ 0 - φ (-1))]) hx.le
    nlinarith

lemma lintegral_neg_ne_top {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ) {η : Measure ℝ}
    (hη : MartOT.Var.InM η) : ∫⁻ x, ENNReal.ofReal (-φ x) ∂η ≠ ⊤ := by
  obtain ⟨C, K, hCK⟩ := convex_lower_bound hφ
  have := hη.1
  have hint : Integrable (fun x : ℝ => C + K * |x|) η :=
    (integrable_const C).add ((hη.2.abs).const_mul K)
  refine ne_top_of_le_ne_top hint.lintegral_lt_top.ne ?_
  exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hCK x)

lemma ereal_sub_le_iff (a b c d : ENNReal) (hb : b ≠ ⊤) (hd : d ≠ ⊤) :
    ((a : EReal) - b ≤ (c : EReal) - d) ↔ a + d ≤ c + b := by
  lift b to NNReal using hb
  lift d to NNReal using hd
  induction a using ENNReal.recTopCoe <;> induction c using ENNReal.recTopCoe
  · simp
  · rename_i c
    simp only [EReal.coe_nnreal_eq_coe_real, EReal.coe_ennreal_top]
    simp
    rw [← EReal.coe_sub]; exact EReal.coe_ne_top _
  · simp
  · rename_i a c
    rw [← ENNReal.coe_add, ← ENNReal.coe_add, ENNReal.coe_le_coe]
    simp only [EReal.coe_nnreal_eq_coe_real]
    rw [← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_le_coe_iff, ← NNReal.coe_le_coe,
      NNReal.coe_add, NNReal.coe_add]
    constructor <;> intro h <;> linarith

lemma convexLE_of_limit (η η' : Measure ℝ) (s s' : ℕ → Measure ℝ)
    (hs : ∀ g : ℝ → ENNReal, Measurable g → Monotone (fun n => ∫⁻ y, g y ∂(s n)) ∧
        ∫⁻ y, g y ∂η = ⨆ n, ∫⁻ y, g y ∂(s n))
    (hs' : ∀ g : ℝ → ENNReal, Measurable g → Monotone (fun n => ∫⁻ y, g y ∂(s' n)) ∧
        ∫⁻ y, g y ∂η' = ⨆ n, ∫⁻ y, g y ∂(s' n))
    (hn : ∀ n, MartOT.Var.ConvexLE (s n) (s' n)) (hη : MartOT.Var.InM η)
    (hη' : MartOT.Var.InM η') : MartOT.Var.ConvexLE η η' := by
  refine ⟨hη, hη', fun φ hφ => ?_⟩
  have hφc : Continuous φ := continuousOn_univ.mp (hφ.continuousOn isOpen_univ)
  have hm1 : Measurable (fun x => ENNReal.ofReal (φ x)) :=
    ENNReal.measurable_ofReal.comp hφc.measurable
  have hm2 : Measurable (fun x => ENNReal.ofReal (-φ x)) :=
    ENNReal.measurable_ofReal.comp hφc.measurable.neg
  rw [integralE_eq, integralE_eq,
    ereal_sub_le_iff _ _ _ _ (lintegral_neg_ne_top hφ hη) (lintegral_neg_ne_top hφ hη')]
  have hstep : ∀ n, (∫⁻ x, ENNReal.ofReal (φ x) ∂(s n)) + (∫⁻ x, ENNReal.ofReal (-φ x) ∂(s' n)) ≤
      (∫⁻ x, ENNReal.ofReal (φ x) ∂(s' n)) + (∫⁻ x, ENNReal.ofReal (-φ x) ∂(s n)) := fun n => by
    have h := (hn n).2.2 φ hφ
    rwa [integralE_eq, integralE_eq, ereal_sub_le_iff _ _ _ _
      (lintegral_neg_ne_top hφ (hn n).1) (lintegral_neg_ne_top hφ (hn n).2.1)] at h
  rw [(hs _ hm1).2, (hs _ hm2).2, (hs' _ hm1).2, (hs' _ hm2).2,
    ENNReal.iSup_add_iSup_of_monotone (hs _ hm1).1 (hs' _ hm2).1,
    ENNReal.iSup_add_iSup_of_monotone (hs' _ hm1).1 (hs _ hm2).1]
  exact iSup_mono hstep

lemma lower_classify (A : Set ℝ) (hA : IsLowerSet A) :
    A = ∅ ∨ (∃ u, A = Set.Iic u) ∨ ∃ u : ℕ → ℝ, Monotone u ∧ A = ⋃ n, Set.Iic (u n) := by
  rcases A.eq_empty_or_nonempty with h | hne
  · exact Or.inl h
  right
  by_cases hb : BddAbove A
  · by_cases ha : sSup A ∈ A
    · left
      exact ⟨sSup A, Set.ext fun x => ⟨fun hx => le_csSup hb hx, fun hx => hA hx ha⟩⟩
    · right
      refine ⟨fun n => sSup A - 1 / ((n:ℝ) + 1), fun m n hmn => ?_,
        Set.ext fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
      · have : (m:ℝ) ≤ n := by exact_mod_cast hmn
        show sSup A - 1 / ((m:ℝ) + 1) ≤ sSup A - 1 / ((n:ℝ) + 1)
        gcongr
      · have hle := le_csSup hb hx
        have hlt : x < sSup A := lt_of_le_of_ne hle (fun h => ha (h ▸ hx))
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
        exact Set.mem_iUnion.mpr ⟨n, by simp only [Set.mem_Iic]; linarith⟩
      · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
        simp only [Set.mem_Iic] at hn
        have : x < sSup A := by
          have : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
          linarith
        obtain ⟨z, hz, hxz⟩ := exists_lt_of_lt_csSup hne this
        exact hA hxz.le hz
  · right
    refine ⟨fun n => (n:ℝ), Nat.mono_cast,
      Set.ext fun x => ⟨fun _ => ?_, fun _ => ?_⟩⟩
    · obtain ⟨n, hn⟩ := exists_nat_ge x
      exact Set.mem_iUnion.mpr ⟨n, hn⟩
    · rw [not_bddAbove_iff] at hb
      obtain ⟨z, hz, hxz⟩ := hb x
      exact hA hxz.le hz

lemma convexLE_tgt {μ ν : Measure ℝ} (πlc π : Measure (ℝ × ℝ))
    (hplc : MartOT.Var.IsPlan μ ν πlc) (hpπ : MartOT.Var.IsPlan μ ν π) (hν : MartOT.Var.InM ν)
    (hIic : ∀ s, MartOT.Var.ConvexLE (tgt πlc (Set.Iic s)) (tgt π (Set.Iic s)))
    (A : Set ℝ) (hA : IsLowerSet A) : MartOT.Var.ConvexLE (tgt πlc A) (tgt π A) := by
  have hi1 := inM_of_le (tgt_le_of_plan hplc A) hν
  have hi2 := inM_of_le (tgt_le_of_plan hpπ A) hν
  rcases lower_classify A hA with h | ⟨u, h⟩ | ⟨u, hu, h⟩
  · refine ⟨hi1, hi2, fun φ _ => ?_⟩
    have e1 : tgt πlc A = 0 := by subst h; unfold tgt; simp
    have e2 : tgt π A = 0 := by subst h; unfold tgt; simp
    rw [e1, e2]
  · subst h; exact hIic u
  · subst h
    exact convexLE_of_limit _ _ (fun n => tgt πlc (Set.Iic (u n))) (fun n => tgt π (Set.Iic (u n)))
      (fun g hg => lintegral_tgt_iUnion πlc u hu hg) (fun g hg => lintegral_tgt_iUnion π u hu hg)
      (fun n => hIic (u n)) hi1 hi2

end LC5Aux

open LC5Aux in
theorem solution (μ ν : Measure ℝ) (hμν : MartOT.Var.ConvexLE μ ν) (ψ ϕ : ℝ → ℝ)
    (hψ0 : ∀ y, 0 ≤ ψ y) (hψ : StrictConvexOn ℝ Set.univ ψ)
    (hϕ0 : ∀ x, 0 ≤ ϕ x) (hϕ : StrictAnti ϕ)
    (hfin : MartOT.Var.CM (fun x y => ϕ x * ψ y) μ ν < ⊤) :
    ∃ π : Measure (ℝ × ℝ), MartOT.Var.IsLeftCurtain μ ν π ∧ MartOT.Var.IsOptimal (fun x y => ϕ x * ψ y) μ ν π ∧
      ∀ π' : Measure (ℝ × ℝ), MartOT.Var.IsOptimal (fun x y => ϕ x * ψ y) μ ν π' → π' = π := by
  obtain ⟨⟨πlc, hlc, -⟩, hmart⟩ := MartOT.Product.theorem_4_18 μ ν hμν
  have hlcM := hmart πlc hlc
  have : IsFiniteMeasure μ := hμν.1.1
  have hν : MartOT.Var.InM ν := hμν.2.1
  have hψc : Continuous ψ := continuousOn_univ.mp (hψ.convexOn.continuousOn isOpen_univ)
  have hψm : Measurable ψ := hψc.measurable
  have hψm' : Measurable (fun y => ENNReal.ofReal (ψ y)) := ENNReal.measurable_ofReal.comp hψm
  have hϕa : Antitone ϕ := hϕ.antitone
  -- the layer function
  let F : Measure (ℝ × ℝ) → ℝ → ENNReal := fun π t =>
    ∫⁻ y, ENNReal.ofReal (ψ y) ∂(tgt π {x | t ≤ ϕ x})
  have hlow : ∀ t : ℝ, IsLowerSet {x | t ≤ ϕ x} := fun t a b hba ha => le_trans ha (hϕa hba)
  have hcost : ∀ π, MartOT.Var.IsPlan μ ν π →
      MartOT.Var.cost (fun x y => ϕ x * ψ y) π = ((∫⁻ t in Set.Ioi (0:ℝ), F π t : ENNReal) : EReal) := by
    intro π hπ
    unfold MartOT.Var.cost
    rw [integralE_of_nonneg π _ (fun p => mul_nonneg (hϕ0 p.1) (hψ0 p.2))]
    rw [MartOT.Product.eq_16 μ ν π hπ ψ ϕ hψ0 hψm hϕ0 hϕa]
    rfl
  have hconv : ∀ π, MartOT.Var.IsMartingalePlan μ ν π → ∀ t : ℝ,
      MartOT.Var.ConvexLE (tgt πlc {x | t ≤ ϕ x}) (tgt π {x | t ≤ ϕ x}) := by
    intro π hπ t
    exact convexLE_tgt πlc π hlcM.1 hπ.1 hν
      (fun s => (MartOT.Product.curtain_target_least μ ν hμν πlc π hlc hπ s).2.2) _ (hlow t)
  have hle : ∀ π, MartOT.Var.IsMartingalePlan μ ν π → ∀ t : ℝ, F πlc t ≤ F π t := by
    intro π hπ t
    have h := (MartOT.Product.strict_convex_integral_eq_iff _ _ (hconv π hπ t) ψ hψ).1
    rw [integralE_of_nonneg _ _ hψ0, integralE_of_nonneg _ _ hψ0] at h
    exact EReal.coe_ennreal_le_coe_ennreal_iff.mp h
  have hopt : MartOT.Var.IsOptimal (fun x y => ϕ x * ψ y) μ ν πlc := by
    refine ⟨hlcM, fun π' hπ' => ?_⟩
    rw [hcost _ hlcM.1, hcost _ hπ'.1, EReal.coe_ennreal_le_coe_ennreal_iff]
    exact lintegral_mono fun t => hle π' hπ' t
  refine ⟨πlc, hlc, hopt, fun π' hπ' => ?_⟩
  -- finiteness of the optimal value
  obtain ⟨π0, hπ0⟩ := iInf_lt_iff.mp hfin
  obtain ⟨hπ0M, hπ0c⟩ := iInf_lt_iff.mp hπ0
  have hlcfin : ∫⁻ t in Set.Ioi (0:ℝ), F πlc t ∂volume ≠ ⊤ := by
    have h1 := lt_of_le_of_lt (hopt.2 π0 hπ0M) hπ0c
    rw [hcost _ hlcM.1] at h1
    intro htop; rw [htop] at h1; simp at h1
  have hπ'le : ∫⁻ t in Set.Ioi (0:ℝ), F π' t ≤ ∫⁻ t in Set.Ioi (0:ℝ), F πlc t := by
    have h1 := hπ'.2 πlc hlcM
    rwa [hcost _ hπ'.1.1, hcost _ hlcM.1, EReal.coe_ennreal_le_coe_ennreal_iff] at h1
  have hπ'fin : ∫⁻ t in Set.Ioi (0:ℝ), F π' t ≠ ⊤ := ne_top_of_le_ne_top hlcfin hπ'le
  have hFanti : ∀ π : Measure (ℝ × ℝ), Antitone (F π) := by
    intro π t t' htt'
    exact lintegral_mono' (tgt_mono π (fun x (hx : t' ≤ ϕ x) => le_trans htt' hx)) le_rfl
  have hFm : ∀ π : Measure (ℝ × ℝ), Measurable (F π) := fun π => (hFanti π).measurable
  have hae : F πlc =ᵐ[volume.restrict (Set.Ioi (0:ℝ))] F π' :=
    ae_eq_of_ae_le_of_lintegral_le (Filter.Eventually.of_forall fun t => hle π' hπ'.1 t)
      hlcfin (hFm π').aemeasurable hπ'le
  have hlt : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0:ℝ))), F π' t < ⊤ := ae_lt_top (hFm π') hπ'fin
  have hgood : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0:ℝ))),
      tgt πlc {x | t ≤ ϕ x} = tgt π' {x | t ≤ ϕ x} := by
    filter_upwards [hae, hlt] with t h1 h2
    have h := (MartOT.Product.strict_convex_integral_eq_iff _ _ (hconv π' hπ'.1 t) ψ hψ).2
    rw [integralE_of_nonneg _ _ hψ0, integralE_of_nonneg _ _ hψ0] at h
    refine (h ?_).mp ?_
    · exact lt_of_le_of_ne le_top (fun h => h2.ne (EReal.coe_ennreal_eq_top_iff.mp h))
    · show ((F πlc t : ENNReal) : EReal) = ((F π' t : ENNReal) : EReal)
      rw [h1]
  -- every `ν^π_s` agrees
  have hfinlc : IsFiniteMeasure πlc := isFinite_of_plan hlcM.1
  have hfin' : IsFiniteMeasure π' := isFinite_of_plan hπ'.1.1
  have hexist : ∀ s : ℝ, ∀ n : ℕ, ∃ t : ℝ, ϕ (s + 1 / ((n:ℝ) + 1)) < t ∧ t ≤ ϕ s ∧
      tgt πlc {x | t ≤ ϕ x} = tgt π' {x | t ≤ ϕ x} := by
    intro s n
    by_contra hcon
    push Not at hcon
    have hsub : Set.Ioc (ϕ (s + 1 / ((n:ℝ) + 1))) (ϕ s) ⊆
        {t | ¬ tgt πlc {x | t ≤ ϕ x} = tgt π' {x | t ≤ ϕ x}} := fun t ht => hcon t ht.1 ht.2
    have hnull := measure_mono_null hsub (ae_iff.mp hgood)
    rw [Measure.restrict_apply measurableSet_Ioc] at hnull
    have hpos : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
    have hlt' : ϕ (s + 1 / ((n:ℝ) + 1)) < ϕ s := hϕ (by linarith)
    have hsub2 : Set.Ioc (ϕ (s + 1 / ((n:ℝ) + 1))) (ϕ s) ∩ Set.Ioi 0 =
        Set.Ioc (ϕ (s + 1 / ((n:ℝ) + 1))) (ϕ s) :=
      Set.inter_eq_left.mpr fun t ht => lt_of_le_of_lt (hϕ0 _) ht.1
    rw [hsub2, Real.volume_Ioc, ENNReal.ofReal_eq_zero] at hnull
    linarith
  choose T hT1 hT2 hT3 using hexist
  have htarget : ∀ s, MartOT.Var.targetUpTo π' s = MartOT.Var.targetUpTo πlc s := by
    intro s
    show tgt π' (Set.Iic s) = tgt πlc (Set.Iic s)
    ext B hB
    rw [tgt_apply _ _ hB, tgt_apply _ _ hB]
    -- the sets `A_n = {ϕ ≥ T s n}` squeeze to `Iic s`
    have hin : ∀ n, Set.Iic s ⊆ {x | T s n ≤ ϕ x} := fun n x hx => le_trans (hT2 s n) (hϕa hx)
    have hout : ∀ n, {x | T s n ≤ ϕ x} ⊆ Set.Iio (s + 1 / ((n:ℝ) + 1)) := by
      intro n x hx
      by_contra hc
      simp only [Set.mem_Iio, not_lt] at hc
      have := hϕa hc
      simp only [Set.mem_ofPred_eq] at hx
      linarith [hT1 s n]
    have hlim : ∀ ρ : Measure (ℝ × ℝ), IsFiniteMeasure ρ →
        Filter.Tendsto (fun n => ρ (Prod.snd ⁻¹' B ∩ {x | T s n ≤ ϕ x} ×ˢ Set.univ))
          Filter.atTop (nhds (ρ (Prod.snd ⁻¹' B ∩ Set.Iic s ×ˢ Set.univ))) := by
      intro ρ hρ
      have hdec : Filter.Tendsto
          (fun n : ℕ => ρ (Prod.snd ⁻¹' B ∩ Set.Iio (s + 1 / ((n:ℝ) + 1)) ×ˢ Set.univ))
          Filter.atTop (nhds (ρ (Prod.snd ⁻¹' B ∩ Set.Iic s ×ˢ Set.univ))) := by
        have hI : (⋂ n : ℕ, Prod.snd ⁻¹' B ∩ Set.Iio (s + 1 / ((n:ℝ) + 1)) ×ˢ Set.univ) =
            Prod.snd ⁻¹' B ∩ Set.Iic s ×ˢ Set.univ := by
          ext ⟨x, y⟩
          simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod,
            Set.mem_Iio, Set.mem_Iic, Set.mem_univ, and_true]
          constructor
          · intro h
            refine ⟨(h 0).1, ?_⟩
            by_contra hc
            push Not at hc
            obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hc)
            have := (h n).2
            linarith
          · rintro ⟨h1, h2⟩ n
            have : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
            exact ⟨h1, by linarith⟩
        rw [← hI]
        refine tendsto_measure_iInter_atTop (fun n => ?_) (fun m n hmn => ?_) ⟨0, measure_ne_top _ _⟩
        · exact ((measurable_snd hB).inter (measurableSet_Iio.prod MeasurableSet.univ)).nullMeasurableSet
        · refine Set.inter_subset_inter_right _ (Set.prod_mono (Set.Iio_subset_Iio ?_) le_rfl)
          have : (m:ℝ) ≤ n := by exact_mod_cast hmn
          gcongr
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdec (fun n => ?_) (fun n => ?_)
      · exact measure_mono (Set.inter_subset_inter_right _ (Set.prod_mono (hin n) le_rfl))
      · exact measure_mono (Set.inter_subset_inter_right _ (Set.prod_mono (hout n) le_rfl))
    have heq : (fun n => π' (Prod.snd ⁻¹' B ∩ {x | T s n ≤ ϕ x} ×ˢ Set.univ)) =
        (fun n => πlc (Prod.snd ⁻¹' B ∩ {x | T s n ≤ ϕ x} ×ˢ Set.univ)) := by
      funext n
      rw [← tgt_apply _ _ hB, ← tgt_apply _ _ hB, hT3 s n]
    have h1 := hlim π' hfin'
    rw [heq] at h1
    exact tendsto_nhds_unique h1 (hlim πlc hfinlc)
  exact MartOT.Product.plan_determined_by_targets μ ν π' πlc hπ'.1.1 hlcM.1 htarget
