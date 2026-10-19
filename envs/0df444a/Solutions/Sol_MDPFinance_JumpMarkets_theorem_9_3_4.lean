-- Prove2me | solution 1 for MDPFinance.JumpMarkets.theorem_9_3_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-17T21:14:04.808189+00:00
-- url     : https://prove2.me/submissions/b754eb67-36ac-4834-9f1f-54eeacd6509b

import Mathlib
import Definitions.Def_MDPFinance_JumpMarkets_JumpMarket

open MeasureTheory Filter Topology
open scoped ENNReal Pointwise

namespace P51V

def rel (x y : ℝ) : Prop := ∃ a : ℚ, ∃ b : ℤ, x - y = (a : ℝ) + (b : ℝ) * Real.sqrt 2

lemma rel_equiv : Equivalence rel where
  refl x := ⟨0, 0, by simp⟩
  symm := by
    rintro x y ⟨a, b, h⟩
    exact ⟨-a, -b, by push_cast; linarith⟩
  trans := by
    rintro x y z ⟨a, b, h⟩ ⟨a', b', h'⟩
    exact ⟨a + a', b + b', by push_cast; linarith⟩

def st : Setoid ℝ := ⟨rel, rel_equiv⟩

noncomputable def rep (x : ℝ) : ℝ := (Quotient.mk st x).out

lemma rel_rep (x : ℝ) : rel x (rep x) := by
  have : st.r (rep x) x := Quotient.mk_out (s := st) x
  exact rel_equiv.symm this

lemma rep_eq (x y : ℝ) (h : rel x y) : rep x = rep y := by
  unfold rep
  congr 1
  exact Quotient.sound h

lemma uniq (a a' : ℚ) (b b' : ℤ)
    (h : (a : ℝ) + (b : ℝ) * Real.sqrt 2 = (a' : ℝ) + (b' : ℝ) * Real.sqrt 2) : b = b' := by
  by_contra hne
  have hb : ((b : ℝ) - b') ≠ 0 := by
    have : (b : ℝ) ≠ b' := by exact_mod_cast hne
    exact sub_ne_zero.mpr this
  have hs : Real.sqrt 2 = (((a' - a) / (b - b') : ℚ) : ℝ) := by
    push_cast
    field_simp
    linarith
  exact irrational_sqrt_two ⟨_, hs.symm⟩

def Sv : Set ℝ := {x | ∃ a : ℚ, ∃ b : ℤ, x - rep x = (a : ℝ) + ((2 * b : ℤ) : ℝ) * Real.sqrt 2}

lemma mem_Sv_iff (x : ℝ) (a : ℚ) (b : ℤ) (h : x - rep x = (a : ℝ) + (b : ℝ) * Real.sqrt 2) :
    x ∈ Sv ↔ Even b := by
  constructor
  · rintro ⟨a', b', h'⟩
    have := uniq a a' b (2 * b') (h.symm.trans h')
    exact ⟨b', by omega⟩
  · rintro ⟨b', hb'⟩
    exact ⟨a, b', by rw [h, hb']; push_cast; ring⟩

lemma flip (x : ℝ) (q : ℚ) : x + ((q : ℝ) + Real.sqrt 2) ∈ Sv ↔ x ∉ Sv := by
  obtain ⟨a, b, h⟩ := rel_rep x
  have hr : rep (x + ((q : ℝ) + Real.sqrt 2)) = rep x :=
    rep_eq _ _ ⟨q, 1, by push_cast; ring⟩
  have h2 : x + ((q : ℝ) + Real.sqrt 2) - rep (x + ((q : ℝ) + Real.sqrt 2))
      = ((a + q : ℚ) : ℝ) + ((b + 1 : ℤ) : ℝ) * Real.sqrt 2 := by
    rw [hr]; push_cast; linarith
  rw [mem_Sv_iff _ _ _ h2, mem_Sv_iff _ _ _ h, Int.even_add_one]

lemma null_of_sub (K : Set ℝ) (hK : MeasurableSet K)
    (hsub : K ⊆ Sv ∨ K ⊆ Svᶜ) : volume K = 0 := by
  by_contra hne
  have hpos : 0 < volume K := pos_iff_ne_zero.mpr hne
  have hn : K - K ∈ 𝓝 (0 : ℝ) := Measure.sub_mem_nhds_zero_of_addHaar_pos volume K hK hpos
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hn
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show -Real.sqrt 2 - ε < -Real.sqrt 2 by linarith)
  have hmem : ((q : ℝ) + Real.sqrt 2) ∈ K - K := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith
  obtain ⟨k1, hk1, k2, hk2, hk⟩ := hmem
  have hk1' : k1 = k2 + ((q : ℝ) + Real.sqrt 2) := by simp only at hk; linarith
  have hfl := flip k2 q
  rw [← hk1'] at hfl
  rcases hsub with h | h
  · exact (hfl.mp (h hk1)) (h hk2)
  · exact (h hk1) (hfl.mpr (h hk2))

end P51V

namespace P51
open MDPFinance.JumpMarkets
variable {d : ℕ}

noncomputable def nuInf (M : JumpMarket d) : Measure ℝ :=
  (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
    (fun s => ENNReal.ofReal (M.lam * Real.exp (-M.lam * s)))

lemma lint_Ioi (M : JumpMarket d) (c : ℝ) :
    ∫⁻ s in Set.Ioi c, ENNReal.ofReal (M.lam * Real.exp (-M.lam * s))
      = ENNReal.ofReal (Real.exp (-M.lam * c)) := by
  have hl := M.lam_pos
  have hint : IntegrableOn (fun s => M.lam * Real.exp (-M.lam * s)) (Set.Ioi c) :=
    (integrableOn_exp_mul_Ioi (by linarith) c).const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun s => by positivity)]
  congr 1
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith)]
  field_simp

lemma nuInf_apply (M : JumpMarket d) (A : Set ℝ) (hA : MeasurableSet A) :
    nuInf M A = ∫⁻ s in A ∩ Set.Ioi 0, ENNReal.ofReal (M.lam * Real.exp (-M.lam * s)) := by
  rw [nuInf, withDensity_apply _ hA, Measure.restrict_restrict hA]

lemma nuInf_Ioi (M : JumpMarket d) (c : ℝ) (hc : 0 ≤ c) :
    nuInf M (Set.Ioi c) = ENNReal.ofReal (Real.exp (-M.lam * c)) := by
  rw [nuInf_apply M _ measurableSet_Ioi, Set.Ioi_inter_Ioi, sup_eq_left.mpr hc, lint_Ioi]

lemma nuInf_univ (M : JumpMarket d) : nuInf M Set.univ = 1 := by
  rw [nuInf_apply M _ MeasurableSet.univ, Set.univ_inter, lint_Ioi]; simp

instance (M : JumpMarket d) : IsProbabilityMeasure (nuInf M) := ⟨nuInf_univ M⟩

lemma nuInf_null (M : JumpMarket d) (A : Set ℝ) (hA : volume A = 0) : nuInf M A = 0 :=
  ((withDensity_absolutelyContinuous _ _).trans
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)) hA

lemma nuInf_Iic (M : JumpMarket d) : nuInf M (Set.Iic 0) = 0 := by
  rw [nuInf_apply M _ measurableSet_Iic]
  have : Set.Iic (0 : ℝ) ∩ Set.Ioi 0 = ∅ := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioi, Set.mem_empty_iff_false,
      iff_false, not_and, not_lt]; intro h; exact h
  rw [this, Measure.restrict_empty, lintegral_zero_measure]

lemma ae_pos (M : JumpMarket d) : ∀ᵐ s ∂(nuInf M), 0 < s := by
  rw [ae_iff]
  have : {a : ℝ | ¬ 0 < a} = Set.Iic 0 := by ext; simp
  rw [this]; exact nuInf_Iic M

lemma kernel_meas {F : ℝ → (Fin d → ℝ) → ℝ × ℝ} (hF : Measurable (Function.uncurry F))
    (Q : Measure (Fin d → ℝ)) [SFinite Q] : Measurable (fun s => Q.map (F s)) := by
  have : (fun s => Q.map (F s)) = fun s => (Q.map (Prod.mk s)).map (Function.uncurry F) := by
    funext s; rw [Measure.map_map hF measurable_prodMk_left]; rfl
  rw [this]; exact (Measure.measurable_map _ hF).comp Measurable.map_prodMk_left

lemma bind_apply' (M : JumpMarket d) {F : ℝ → (Fin d → ℝ) → ℝ × ℝ}
    (hF : Measurable (Function.uncurry F))
    (Q : Measure (Fin d → ℝ)) [SFinite Q] (B : Set (ℝ × ℝ)) (hB : MeasurableSet B) :
    ((nuInf M).bind (fun s => Q.map (F s))) B = ∫⁻ s, Q ((F s) ⁻¹' B) ∂(nuInf M) := by
  rw [Measure.bind_apply hB (kernel_meas hF Q).aemeasurable]
  congr 1; funext s
  exact Measure.map_apply (hF.comp measurable_prodMk_left) hB

lemma phi_of_const (M : JumpMarket d) (a : Control d) (c : ℝ)
    (h : ∀ s, M.rho + ∑ i, a.val s i * (M.mu i - M.rho) = c) (s x : ℝ) :
    M.phi a s x = x * Real.exp (c * max s 0) := by
  unfold JumpMarket.phi
  simp only [h]
  rw [setIntegral_const]
  simp [mul_comm]

def a0 (d : ℕ) : Control d := ⟨fun _ => 0, measurable_const, fun _ => by simp [Ucal]⟩

def ai (i : Fin d) : Control d := ⟨fun _ => Pi.single i 1, measurable_const, fun _ => by
  refine ⟨fun j => ?_, ?_⟩
  · by_cases h : j = i
    · subst h; simp
    · simp [Pi.single_apply, h]
  · simp⟩

lemma phi_a0 (M : JumpMarket d) (s x : ℝ) :
    M.phi (a0 d) s x = x * Real.exp (M.rho * max s 0) :=
  phi_of_const M _ _ (fun s => by simp [a0]) s x

lemma phi_ai (M : JumpMarket d) (i : Fin d) (s x : ℝ) :
    M.phi (ai i) s x = x * Real.exp (M.mu i * max s 0) :=
  phi_of_const M _ _ (fun s => by simp [ai, Pi.single_apply]) s x


lemma step_a0 (M : JumpMarket d) (q : ℝ × ℝ) :
    M.step (a0 d) q = (nuInf M).map (fun s => (q.1 + s, q.2 * Real.exp (M.rho * max s 0))) := by
  haveI := M.QY_prob
  have h : ∀ s, M.QY.map (fun y => (q.1 + s, M.phi (a0 d) s q.2 * (1 + ∑ i, (a0 d).val s i * y i)))
      = Measure.dirac (q.1 + s, q.2 * Real.exp (M.rho * max s 0)) := by
    intro s; simp only [phi_a0]; simp [a0, Measure.map_const]
  change (nuInf M).bind _ = _
  simp_rw [h]
  exact Measure.bind_dirac_eq_map _ (by fun_prop)

lemma step_ai_apply (M : JumpMarket d) (i : Fin d) (q : ℝ × ℝ) (B : Set (ℝ × ℝ))
    (hB : MeasurableSet B) :
    M.step (ai i) q B = ∫⁻ s, M.QY ((fun y : Fin d → ℝ =>
      (q.1 + s, q.2 * Real.exp (M.mu i * max s 0) * (1 + y i))) ⁻¹' B) ∂(nuInf M) := by
  haveI := M.QY_prob
  have h : M.step (ai i) q = (nuInf M).bind (fun s => M.QY.map (fun y : Fin d → ℝ =>
      (q.1 + s, q.2 * Real.exp (M.mu i * max s 0) * (1 + y i)))) := by
    change (nuInf M).bind _ = _
    congr 1; funext s; congr 1; funext y
    simp only [phi_ai]; simp [ai, Pi.single_apply]
  rw [h]
  exact bind_apply' M (F := fun s (y : Fin d → ℝ) =>
    (q.1 + s, q.2 * Real.exp (M.mu i * max s 0) * (1 + y i))) (by fun_prop) M.QY B hB

theorem nondeg_false (M : JumpMarket d) (Pr : HistPolicy d → ℝ × ℝ → Measure (ℕ → ℝ × ℝ))
    (hPr : ∀ g, M.IsChainLaw g (Pr g)) (i : Fin d)
    (hi : M.mu i ≠ M.rho ∨ M.QY {y | y i ≠ 0} ≠ 0) : False := by
  classical
  haveI := M.QY_prob
  let S : Set (ℝ × ℝ) := {q | q.1 ∈ P51V.Sv}
  let G : ℝ × ℝ → Control d := fun q => if q.1 ∉ P51V.Sv then ai i else a0 d
  let g : HistPolicy d := fun n h => if n = 1 then G (h (Fin.last n)) else a0 d
  let Bs : Set (ℝ × ℝ) := {q | q.2 ≠ Real.exp (M.rho * q.1)}
  have hBs : MeasurableSet Bs := (measurableSet_eq_fun measurable_snd (by fun_prop)).compl
  let μ := M.step (a0 d) ((0:ℝ), (1:ℝ))
  have hcyl : ∀ C : Set (ℝ × ℝ), MeasurableSet C →
      Pr g ((0:ℝ), (1:ℝ)) {w | w 2 ∈ C} = ∫⁻ q, M.step (G q) q C ∂μ := by
    intro C hC
    have hset : {w : ℕ → ℝ × ℝ | w 2 ∈ C}
        = {w | ∀ j ≤ 2, w j ∈ (fun j => if j = 2 then C else Set.univ) j} := by
      ext w; constructor
      · intro h j _
        by_cases hj2 : j = 2
        · subst hj2; simpa using h
        · simp [hj2]
      · intro h; simpa using h 2 le_rfl
    rw [hset, (hPr g).2 _ 2 _ (fun j => by by_cases hj : j = 2 <;> simp [hj, hC])]
    simp [JumpMarket.chainCyl, g, μ]
    rfl
  have hγm : Measurable (fun s : ℝ => ((0:ℝ) + s, (1:ℝ) * Real.exp (M.rho * max s 0))) := by
    fun_prop
  have hμ : μ = (nuInf M).map (fun s => ((0:ℝ) + s, (1:ℝ) * Real.exp (M.rho * max s 0))) :=
    step_a0 M _
  have hμuniv : μ Set.univ = 1 := by
    rw [hμ, Measure.map_apply hγm MeasurableSet.univ, Set.preimage_univ, nuInf_univ]
  have hμBs : μ Bs = 0 := by
    rw [hμ, Measure.map_apply hγm hBs]
    apply measure_mono_null _ (nuInf_Iic M)
    intro s hs
    simp only [Set.mem_preimage, Bs, Set.mem_setOf_eq] at hs
    simp only [Set.mem_Iic]
    by_contra h; push_neg at h
    apply hs; rw [max_eq_left h.le]; simp
  have hμS : ∀ K, MeasurableSet K → (K ⊆ S ∨ K ⊆ Sᶜ) → μ K = 0 := by
    intro K hK hsub
    rw [hμ, Measure.map_apply hγm hK]
    apply nuInf_null
    apply P51V.null_of_sub _ (hγm hK)
    rcases hsub with h | h
    · left; intro s hs; have := h hs; simpa [S] using this
    · right; intro s hs; have := h hs; simpa [S] using this
  have hc0 : ∀ q, q ∉ Bs → M.step (a0 d) q Bs = 0 := by
    intro q hq
    rw [step_a0, Measure.map_apply (by fun_prop) hBs]
    apply measure_mono_null _ (nuInf_Iic M)
    intro s hs
    simp only [Set.mem_preimage, Bs, Set.mem_setOf_eq, not_not] at hs hq
    simp only [Set.mem_Iic]
    by_contra h; push_neg at h
    apply hs; rw [max_eq_left h.le, hq, ← Real.exp_add]; ring_nf
  let κ := ∫⁻ s, M.QY {y : Fin d → ℝ | Real.exp (M.mu i * max s 0) * (1 + y i)
      ≠ Real.exp (M.rho * s)} ∂(nuInf M)
  have hc1 : ∀ q, q ∉ Bs → M.step (ai i) q Bs = κ := by
    intro q hq
    rw [step_ai_apply M i q Bs hBs]
    congr 1; funext s; congr 1; ext y
    simp only [Set.mem_preimage, Bs, Set.mem_setOf_eq, not_not] at hq ⊢
    rw [hq, mul_assoc, show M.rho * (q.1 + s) = M.rho * q.1 + M.rho * s by ring, Real.exp_add,
      ne_eq, ne_eq, mul_right_inj' (Real.exp_pos _).ne']
  have hc1u : ∀ q, M.step (ai i) q Set.univ = 1 := by
    intro q
    rw [step_ai_apply M i q _ MeasurableSet.univ]
    simp [nuInf_univ]
  have hκ : κ ≠ 0 := by
    intro h0
    have hDm : MeasurableSet {p : ℝ × (Fin d → ℝ) |
        Real.exp (M.mu i * max p.1 0) * (1 + p.2 i) ≠ Real.exp (M.rho * p.1)} :=
      (measurableSet_eq_fun (by fun_prop) (by fun_prop)).compl
    have hmeas : Measurable (fun s => M.QY {y : Fin d → ℝ |
        Real.exp (M.mu i * max s 0) * (1 + y i) ≠ Real.exp (M.rho * s)}) :=
      measurable_measure_prodMk_left hDm
    rw [lintegral_eq_zero_iff hmeas] at h0
    have hae : ∀ᵐ s ∂ nuInf M, M.QY {y : Fin d → ℝ |
        Real.exp (M.mu i * max s 0) * (1 + y i) ≠ Real.exp (M.rho * s)} = 0 ∧ 0 < s :=
      h0.and (ae_pos M)
    obtain ⟨s1, -, hs1, hs1pos⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (s := Set.univ) (by rw [nuInf_univ]; exact one_ne_zero) (ae_restrict_of_ae hae)
    rw [max_eq_left hs1pos.le] at hs1
    by_cases hmu : M.mu i = M.rho
    · have hq : M.QY {y | y i ≠ 0} ≠ 0 := hi.resolve_left (by simpa using hmu)
      apply hq; rw [← hs1]; congr 1; ext y
      simp only [Set.mem_setOf_eq, hmu, ne_eq]
      have key : (Real.exp (M.rho * s1) * (1 + y i) = Real.exp (M.rho * s1)) ↔ y i = 0 := by
        constructor
        · intro h
          have := mul_left_cancel₀ (Real.exp_pos (M.rho * s1)).ne' (h.trans (mul_one _).symm)
          linarith
        · intro h; rw [h]; ring
      rw [key]
    · have hne : nuInf M {s1}ᶜ ≠ 0 := by
        rw [measure_compl (measurableSet_singleton _) (measure_ne_top _ _), nuInf_univ,
          nuInf_null M _ (Real.volume_singleton)]
        simp
      obtain ⟨s2, hs2mem, hs2, hs2pos⟩ :=
        Measure.exists_mem_of_measure_ne_zero_of_ae hne (ae_restrict_of_ae hae)
      rw [max_eq_left hs2pos.le] at hs2
      have hsub : (Set.univ : Set (Fin d → ℝ)) ⊆
          {y : Fin d → ℝ | Real.exp (M.mu i * s1) * (1 + y i) ≠ Real.exp (M.rho * s1)} ∪
          {y : Fin d → ℝ | Real.exp (M.mu i * s2) * (1 + y i) ≠ Real.exp (M.rho * s2)} := by
        intro y _
        by_contra hy
        simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hy
        obtain ⟨h1, h2⟩ := hy
        apply hs2mem
        have e1 : 1 + y i = Real.exp ((M.rho - M.mu i) * s1) := by
          rw [sub_mul, Real.exp_sub, eq_div_iff (Real.exp_pos _).ne']; linarith
        have e2 : 1 + y i = Real.exp ((M.rho - M.mu i) * s2) := by
          rw [sub_mul, Real.exp_sub, eq_div_iff (Real.exp_pos _).ne']; linarith
        have e3 := Real.exp_injective (e1.symm.trans e2)
        have hsub0 : M.rho - M.mu i ≠ 0 := sub_ne_zero.mpr (Ne.symm hmu)
        exact (mul_left_cancel₀ hsub0 e3).symm
      have := (measure_mono hsub).trans (measure_union_le (μ := M.QY) _ _)
      rw [hs1, hs2, add_zero, measure_univ] at this
      exact absurd this (by simp)
  have hE1 : Pr g ((0:ℝ), (1:ℝ)) {w | w 2 ∈ Bs} = 0 := by
    rw [hcyl Bs hBs]
    obtain ⟨f1, hf1m, hf1le, hf1eq⟩ :=
      exists_measurable_le_lintegral_eq μ (fun q => M.step (G q) q Bs)
    rw [hf1eq, lintegral_eq_zero_iff hf1m]
    have hK : μ ({q | f1 q ≠ 0} ∩ Bsᶜ) = 0 := by
      apply hμS _ ((hf1m (measurableSet_singleton 0).compl).inter hBs.compl)
      right
      rintro q ⟨hq1, hq2⟩ hqS
      have h := hf1le q
      have hqS' : q.1 ∈ P51V.Sv := hqS
      have hG : G q = a0 d := if_neg (not_not.mpr hqS')
      simp only [hG, hc0 q hq2] at h
      exact hq1 (le_antisymm h bot_le)
    rw [Filter.EventuallyEq, ae_iff]
    apply measure_mono_null _ (measure_union_null hK hμBs)
    intro q hq
    by_cases hqB : q ∈ Bs
    · right; exact hqB
    · left; exact ⟨hq, hqB⟩
  have hE2 : Pr g ((0:ℝ), (1:ℝ)) {w | w 2 ∈ Bsᶜ} ≤ 1 - κ := by
    rw [hcyl _ hBs.compl]
    obtain ⟨f2, hf2m, hf2le, hf2eq⟩ :=
      exists_measurable_le_lintegral_eq μ (fun q => M.step (G q) q Bsᶜ)
    rw [hf2eq]
    have hK : μ ({q | 1 - κ < f2 q} ∩ Bsᶜ) = 0 := by
      apply hμS _ ((measurableSet_lt measurable_const hf2m).inter hBs.compl)
      left
      rintro q ⟨hq1, hq2⟩
      by_contra hqS
      have h := hf2le q
      have hqS' : q.1 ∉ P51V.Sv := hqS
      have hG : G q = ai i := if_pos hqS'
      have hfin : M.step (ai i) q Bs ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.one_ne_top ((hc1u q) ▸ measure_mono (Set.subset_univ _))
      simp only [hG] at h
      rw [measure_compl hBs hfin, hc1u, hc1 q hq2] at h
      exact absurd h (not_le.mpr hq1)
    have hae : ∀ᵐ q ∂μ, f2 q ≤ 1 - κ := by
      rw [ae_iff]
      apply measure_mono_null _ (measure_union_null hK hμBs)
      intro q hq
      simp only [Set.mem_setOf_eq, not_le] at hq
      by_cases hqB : q ∈ Bs
      · right; exact hqB
      · left; exact ⟨hq, hqB⟩
    calc ∫⁻ q, f2 q ∂μ ≤ ∫⁻ _, (1 - κ) ∂μ := lintegral_mono_ae hae
      _ = 1 - κ := by rw [lintegral_const, hμuniv, mul_one]
  have htot : Pr g ((0:ℝ), (1:ℝ)) {w | w 2 ∈ Bs} + Pr g ((0:ℝ), (1:ℝ)) {w | w 2 ∈ Bsᶜ} = 1 := by
    haveI := (hPr g).1 ((0:ℝ), (1:ℝ))
    have hm : MeasurableSet {w : ℕ → ℝ × ℝ | w 2 ∈ Bs} := measurable_pi_apply 2 hBs
    have : {w : ℕ → ℝ × ℝ | w 2 ∈ Bsᶜ} = {w | w 2 ∈ Bs}ᶜ := rfl
    rw [this, measure_add_measure_compl hm, measure_univ]
  rw [hE1, zero_add] at htot
  have hlt : (1 : ℝ≥0∞) - κ < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hκ
  rw [htot] at hE2
  exact absurd hE2 (not_le.mpr hlt)


section Deg
variable (M : JumpMarket d)

def IsDeg : Prop := ∀ i, M.mu i = M.rho ∧ M.QY {y | y i ≠ 0} = 0

noncomputable def Γ (p : ℝ × ℝ) (s : ℝ) : ℝ × ℝ := (p.1 + s, p.2 * Real.exp (M.rho * max s 0))

noncomputable def nuP (p : ℝ × ℝ) : Measure ℝ :=
  (volume.restrict (Set.Ioo (0 : ℝ) (M.T - p.1))).withDensity
    (fun s => ENNReal.ofReal (M.lam * Real.exp (-M.lam * s)))

noncomputable def Φ (p : ℝ × ℝ) : ℝ := p.2 * Real.exp (M.rho * (M.T - p.1))

noncomputable def vv (p : ℝ × ℝ) : ℝ := M.U (Φ M p)

variable {M}

lemma QY_dirac (hdeg : IsDeg M) : M.QY = Measure.dirac 0 := by
  haveI := M.QY_prob
  have hnull : M.QY {y | y ≠ 0} = 0 := by
    have : {y : Fin d → ℝ | y ≠ 0} = ⋃ i, {y | y i ≠ 0} := by
      ext y; simp [funext_iff]
    rw [this]; exact measure_iUnion_null (fun i => (hdeg i).2)
  ext A hA
  rw [Measure.dirac_apply' _ hA]
  by_cases h0 : (0 : Fin d → ℝ) ∈ A
  · rw [Set.indicator_of_mem h0]
    have hc : M.QY Aᶜ = 0 := measure_mono_null (fun y hy => by
      intro h; rw [h] at hy; exact hy h0) hnull
    rw [prob_compl_eq_zero_iff hA] at hc
    simpa using hc
  · rw [Set.indicator_of_notMem h0]
    exact measure_mono_null (fun y hy => by intro h; rw [h] at hy; exact h0 hy) hnull

lemma phi_deg (hdeg : IsDeg M) (a : Control d) (s x : ℝ) :
    M.phi a s x = x * Real.exp (M.rho * max s 0) :=
  phi_of_const M a M.rho (fun s => by simp [(hdeg _).1]) s x

lemma Γ_meas (p : ℝ × ℝ) : Measurable (Γ M p) := by unfold Γ; fun_prop

lemma Γ_meas2 : Measurable (fun ps : (ℝ × ℝ) × ℝ => Γ M ps.1 ps.2) := by unfold Γ; fun_prop

lemma step_deg (hdeg : IsDeg M) (a : Control d) (p : ℝ × ℝ) :
    M.step a p = (nuInf M).map (Γ M p) := by
  have h : ∀ s, M.QY.map (fun y => (p.1 + s, M.phi a s p.2 * (1 + ∑ i, a.val s i * y i)))
      = Measure.dirac (Γ M p s) := by
    intro s
    rw [QY_dirac hdeg, Measure.map_dirac' (by fun_prop : Measurable (fun y : Fin d → ℝ =>
      (p.1 + s, M.phi a s p.2 * (1 + ∑ i, a.val s i * y i))))]
    simp [Γ, phi_deg hdeg]
  change (nuInf M).bind _ = _
  simp_rw [h]
  exact Measure.bind_dirac_eq_map _ (Γ_meas p)

lemma Q_deg (hdeg : IsDeg M) (a : Control d) (p : ℝ × ℝ) :
    M.Q a p = (nuP M p).map (Γ M p) := by
  have h : ∀ s, M.QY.map (fun y => (p.1 + s, M.phi a s p.2 * (1 + ∑ i, a.val s i * y i)))
      = Measure.dirac (Γ M p s) := by
    intro s
    rw [QY_dirac hdeg, Measure.map_dirac' (by fun_prop : Measurable (fun y : Fin d → ℝ =>
      (p.1 + s, M.phi a s p.2 * (1 + ∑ i, a.val s i * y i))))]
    simp [Γ, phi_deg hdeg]
  change (nuP M p).bind _ = _
  simp_rw [h]
  exact Measure.bind_dirac_eq_map _ (Γ_meas p)

lemma r_deg (hdeg : IsDeg M) (a : Control d) (p : ℝ × ℝ) :
    M.r a p = Real.exp (-M.lam * (M.T - p.1)) * M.U (p.2 * Real.exp (M.rho * max (M.T - p.1) 0)) := by
  simp [JumpMarket.r, phi_deg hdeg]

lemma Φ_Γ (p : ℝ × ℝ) (s : ℝ) (hs : 0 ≤ s) : Φ M (Γ M p s) = Φ M p := by
  simp only [Φ, Γ, max_eq_left hs]
  rw [mul_assoc, ← Real.exp_add]; congr 2; ring

lemma Φ_meas : Measurable (Φ M) := by unfold Φ; fun_prop

lemma Γ_mem (p : ℝ × ℝ) (hp : p ∈ M.E) (s : ℝ) (hs : s ∈ Set.Icc 0 (M.T - p.1)) :
    Γ M p s ∈ M.E := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := hp
  simp only [Set.mem_Ici] at h3
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [Γ]; linarith [hs.1]
  · simp only [Γ]; linarith [hs.2]
  · simp only [Γ, Set.mem_Ici]; positivity

lemma Φ_nonneg (p : ℝ × ℝ) (hp : p ∈ M.E) : 0 ≤ Φ M p := by
  have := hp.2; simp only [Set.mem_Ici] at this; unfold Φ; positivity

lemma r_E (hdeg : IsDeg M) (a : Control d) (p : ℝ × ℝ) (hp : p ∈ M.E) :
    M.r a p = Real.exp (-M.lam * (M.T - p.1)) * vv M p := by
  rw [r_deg hdeg, max_eq_left (by linarith [hp.1.2])]; rfl

lemma Γ_emb (p : ℝ × ℝ) : MeasurableEmbedding (Γ M p) := by
  apply MeasurableEmbedding.of_measurable_inverse (Γ_meas p) _ (g := fun q => q.1 - p.1)
    (by fun_prop)
  · intro s; simp [Γ]
  · have : Set.range (Γ M p) = {q | q.2 = p.2 * Real.exp (M.rho * max (q.1 - p.1) 0)} := by
      ext q; constructor
      · rintro ⟨s, rfl⟩; simp [Γ]
      · intro hq; refine ⟨q.1 - p.1, ?_⟩; simp only [Γ]; ext
        · simp
        · simp only [Set.mem_setOf_eq] at hq; rw [hq]
    rw [this]; exact measurableSet_eq_fun measurable_snd (by fun_prop)

lemma lint_Ioc (τ : ℝ) (hτ : 0 ≤ τ) :
    ∫⁻ s in Set.Ioc 0 τ, ENNReal.ofReal (M.lam * Real.exp (-M.lam * s))
      = ENNReal.ofReal (1 - Real.exp (-M.lam * τ)) := by
  have hu := lintegral_union (μ := volume) (f := fun s => ENNReal.ofReal (M.lam * Real.exp (-M.lam * s)))
    (A := Set.Ioc 0 τ) (measurableSet_Ioi (a := τ)) (Set.Ioc_disjoint_Ioi (a := 0) le_rfl)
  rw [Set.Ioc_union_Ioi_eq_Ioi hτ, lint_Ioi, lint_Ioi] at hu
  simp only [mul_zero, Real.exp_zero, ENNReal.ofReal_one] at hu
  have hfin : ENNReal.ofReal (Real.exp (-M.lam * τ)) ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [ENNReal.ofReal_sub _ (Real.exp_pos _).le, ENNReal.ofReal_one, hu, ENNReal.add_sub_cancel_right hfin]

lemma nuP_univ (p : ℝ × ℝ) (hp : p.1 ≤ M.T) :
    nuP M p Set.univ = ENNReal.ofReal (1 - Real.exp (-M.lam * (M.T - p.1))) := by
  rw [nuP, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    setLIntegral_congr Ioo_ae_eq_Ioc, lint_Ioc _ (by linarith)]

instance (p : ℝ × ℝ) : IsFiniteMeasure (nuP M p) := by
  refine ⟨?_⟩
  rw [nuP, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    setLIntegral_congr Ioo_ae_eq_Ioc]
  by_cases h : 0 ≤ M.T - p.1
  · rw [lint_Ioc _ h]; exact ENNReal.ofReal_lt_top
  · rw [Set.Ioc_eq_empty (by linarith)]; simp

lemma nuP_ac (p : ℝ × ℝ) : nuP M p ≪ volume.restrict (Set.Ioo (0 : ℝ) (M.T - p.1)) :=
  withDensity_absolutelyContinuous _ _

lemma nuP_ae (p : ℝ × ℝ) : ∀ᵐ s ∂(nuP M p), s ∈ Set.Ioo (0 : ℝ) (M.T - p.1) :=
  nuP_ac p (ae_restrict_mem measurableSet_Ioo)

lemma vv_Γ (p : ℝ × ℝ) (s : ℝ) (hs : 0 ≤ s) : vv M (Γ M p s) = vv M p := by
  simp only [vv, Φ_Γ p s hs]

lemma vv_nonneg (p : ℝ × ℝ) (hp : p ∈ M.E) : 0 ≤ vv M p := M.U_nonneg _ (Φ_nonneg p hp)

lemma integral_Q (hdeg : IsDeg M) (a : Control d) (p : ℝ × ℝ) (f : ℝ × ℝ → ℝ) :
    ∫ q, f q ∂(M.Q a p) = ∫ s, f (Γ M p s) ∂(nuP M p) := by
  rw [Q_deg hdeg, (Γ_emb p).integral_map]

lemma lintegral_Q (hdeg : IsDeg M) (a : Control d) (p : ℝ × ℝ) (f : ℝ × ℝ → ℝ≥0∞) :
    ∫⁻ q, f q ∂(M.Q a p) = ∫⁻ s, f (Γ M p s) ∂(nuP M p) := by
  rw [Q_deg hdeg, (Γ_emb p).lintegral_map]

lemma vv_TOf_val (hdeg : IsDeg M) (a : Control d) (p : ℝ × ℝ) (hp : p ∈ M.E) :
    M.r a p + ∫ q, vv M q ∂(M.Q a p) = vv M p := by
  rw [integral_Q hdeg, r_E hdeg a p hp]
  have hae : ∀ᵐ s ∂(nuP M p), vv M (Γ M p s) = vv M p :=
    (nuP_ae p).mono fun s hs => vv_Γ p s hs.1.le
  rw [integral_congr_ae hae, integral_const, smul_eq_mul, measureReal_def,
    nuP_univ p hp.1.2, ENNReal.toReal_ofReal]
  · ring
  · have : Real.exp (-M.lam * (M.T - p.1)) ≤ 1 := Real.exp_le_one_iff.mpr (by
      have := M.lam_pos; have := hp.1.2; nlinarith)
    linarith

lemma vv_L (hdeg : IsDeg M) (a : Control d) (p : ℝ × ℝ) (hp : p ∈ M.E) (F : ℝ × ℝ → ℝ≥0∞)
    (hF : ∀ q ∈ M.E, F q = ENNReal.ofReal (vv M q)) :
    M.L F a p = ENNReal.ofReal (vv M p) := by
  unfold JumpMarket.L
  rw [lintegral_Q hdeg]
  have hae : ∀ᵐ s ∂(nuP M p), F (Γ M p s) = ENNReal.ofReal (vv M p) :=
    (nuP_ae p).mono fun s hs => by
      rw [hF _ (Γ_mem p hp s ⟨hs.1.le, hs.2.le⟩), vv_Γ p s hs.1.le]
  rw [lintegral_congr_ae hae, lintegral_const, nuP_univ p hp.1.2, r_E hdeg a p hp]
  have he0 : 0 ≤ Real.exp (-M.lam * (M.T - p.1)) := (Real.exp_pos _).le
  have he1 : Real.exp (-M.lam * (M.T - p.1)) ≤ 1 := Real.exp_le_one_iff.mpr (by
      have := M.lam_pos; have := hp.1.2; nlinarith)
  have hv := vv_nonneg p hp
  rw [← ENNReal.ofReal_mul hv, ← ENNReal.ofReal_add (mul_nonneg he0 hv)
    (mul_nonneg hv (by linarith))]
  congr 1; ring

end Deg
end P51

namespace P51
open MDPFinance.JumpMarkets ProbabilityTheory
variable {d : ℕ} {M : JumpMarket d}

noncomputable def Kk (M : JumpMarket d) : Kernel (ℝ × ℝ) (ℝ × ℝ) where
  toFun p := (nuInf M).map (Γ M p)
  measurable' := by
    have : (fun p => (nuInf M).map (Γ M p)) = fun p => ((nuInf M).map (Prod.mk p)).map
        (fun ps : (ℝ × ℝ) × ℝ => Γ M ps.1 ps.2) := by
      funext p; rw [Measure.map_map Γ_meas2 measurable_prodMk_left]; rfl
    rw [this]; exact (Measure.measurable_map _ Γ_meas2).comp Measurable.map_prodMk_left

lemma Kk_apply (p : ℝ × ℝ) : Kk M p = (nuInf M).map (Γ M p) := rfl

instance : IsMarkovKernel (Kk M) :=
  ⟨fun p => by rw [Kk_apply]; exact Measure.isProbabilityMeasure_map (Γ_meas p).aemeasurable⟩

lemma Kk_set (p : ℝ × ℝ) (A : Set (ℝ × ℝ)) (hA : MeasurableSet A) :
    Kk M p A = nuInf M (Γ M p ⁻¹' A) := by
  rw [Kk_apply, Measure.map_apply (Γ_meas p) hA]

noncomputable def Cy (M : JumpMarket d) : ℕ → ℝ × ℝ → (ℕ → Set (ℝ × ℝ)) → ℝ≥0∞
  | 0, _, _ => 1
  | m + 1, x, B => ∫⁻ q in B 0, Cy M m q (fun i => B (i + 1)) ∂(Kk M x)

lemma Cy_zero (x : ℝ × ℝ) (B : ℕ → Set (ℝ × ℝ)) : Cy M 0 x B = 1 := rfl

lemma Cy_succ (m : ℕ) (x : ℝ × ℝ) (B : ℕ → Set (ℝ × ℝ)) :
    Cy M (m + 1) x B = ∫⁻ q in B 0, Cy M m q (fun i => B (i + 1)) ∂(Kk M x) := rfl

lemma chainCyl_deg (hdeg : IsDeg M) (g : HistPolicy d) :
    ∀ m n (h : Fin (n + 1) → ℝ × ℝ) B, M.chainCyl g n h m B = Cy M m (h (Fin.last n)) B := by
  intro m
  induction m with
  | zero => intro n h B; rfl
  | succ m ih =>
    intro n h B
    rw [Cy_succ]
    simp only [JumpMarket.chainCyl]
    rw [step_deg hdeg, ← Kk_apply]
    congr 1; funext q
    rw [ih]; simp [Fin.snoc_last]

lemma Cy_marg : ∀ j (x : ℝ × ℝ) (A : Set (ℝ × ℝ)), MeasurableSet A →
    Cy M (j + 1) x (fun i => if i = j then A else Set.univ) = (Kk M ^ (j + 1)) x A := by
  intro j
  induction j with
  | zero =>
    intro x A hA
    rw [Cy_succ]; simp [Cy_zero, hA]
  | succ j ih =>
    intro x A hA
    rw [Cy_succ]
    have hshift : (fun i : ℕ => (fun i => if i = j + 1 then A else Set.univ) (i + 1))
        = (fun i => if i = j then A else Set.univ) := by funext i; simp
    rw [hshift]
    simp only [show ((0:ℕ) = j + 1) = False from by simp, if_false, Measure.restrict_univ]
    simp_rw [ih _ A hA]
    rw [show j + 1 + 1 = 1 + (j + 1) by ring, Kernel.pow_add_apply_eq_lintegral _ 1 (j + 1) x hA,
      pow_one]

lemma law (hdeg : IsDeg M) (g : HistPolicy d) (Pr' : ℝ × ℝ → Measure (ℕ → ℝ × ℝ))
    (hc : M.IsChainLaw g Pr') (p : ℝ × ℝ) (k : ℕ) (A : Set (ℝ × ℝ)) (hA : MeasurableSet A) :
    Pr' p {w | w k ∈ A} = (Kk M ^ k) p A := by
  have hset : {w : ℕ → ℝ × ℝ | w k ∈ A}
      = {w | ∀ i ≤ k, w i ∈ (fun i => if i = k then A else Set.univ) i} := by
    ext w; constructor
    · intro h i _
      by_cases hik : i = k
      · subst hik; simpa using h
      · simp [hik]
    · intro h; simpa using h k le_rfl
  rw [hset, hc.2 p k _ (fun i => by by_cases h : i = k <;> simp [h, hA])]
  cases k with
  | zero =>
    rw [pow_zero]
    change _ = (Kernel.id p) A
    rw [Kernel.id_apply, Measure.dirac_apply' _ hA]
    simp [JumpMarket.chainCyl]
    rfl
  | succ j =>
    simp only [show ((0:ℕ) = j + 1) = False from by simp, if_false, Set.indicator_univ]
    rw [chainCyl_deg hdeg]
    have : (fun i : ℕ => (fun i => if i = j + 1 then A else Set.univ) (i + 1))
        = fun i => if i = j then A else Set.univ := by funext i; simp
    rw [this, Cy_marg j _ A hA]

lemma law_map (hdeg : IsDeg M) (g : HistPolicy d) (Pr' : ℝ × ℝ → Measure (ℕ → ℝ × ℝ))
    (hc : M.IsChainLaw g Pr') (p : ℝ × ℝ) (k : ℕ) :
    (Pr' p).map (fun w => w k) = (Kk M ^ k) p := by
  ext A hA
  rw [Measure.map_apply (measurable_pi_apply k) hA]
  exact law hdeg g Pr' hc p k A hA

lemma pow_zero_apply (p : ℝ × ℝ) : (Kk M ^ 0) p = Measure.dirac p := by
  rw [pow_zero]; exact Kernel.id_apply p

lemma margΦ (p : ℝ × ℝ) : ∀ k, (Kk M ^ k) p {q | Φ M q ≠ Φ M p} = 0 := by
  have hm : MeasurableSet {q : ℝ × ℝ | Φ M q ≠ Φ M p} :=
    (measurableSet_eq_fun Φ_meas measurable_const).compl
  intro k
  induction k with
  | zero => rw [pow_zero_apply, Measure.dirac_apply' _ hm]; simp
  | succ k ih =>
    rw [Kernel.pow_succ_apply_eq_lintegral _ _ _ hm]
    have hae : ∀ᵐ q ∂((Kk M ^ k) p), Kk M q {q' | Φ M q' ≠ Φ M p} = 0 := by
      have := (measure_eq_zero_iff_ae_notMem).mp ih
      filter_upwards [this] with q hq
      simp only [Set.mem_setOf_eq, not_not] at hq
      rw [Kk_set _ _ hm]
      apply measure_mono_null _ (nuInf_Iic M)
      intro s hs
      simp only [Set.mem_preimage, Set.mem_setOf_eq] at hs
      simp only [Set.mem_Iic]
      by_contra h; push_neg at h
      exact hs (by rw [Φ_Γ q s h.le, hq])
    rw [lintegral_congr_ae hae, lintegral_zero]

lemma Kle (q : ℝ × ℝ) (hq : M.T < q.1) : Kk M q {q' | q'.1 ≤ M.T} = 0 := by
  rw [Kk_set _ _ (measurableSet_le measurable_fst measurable_const)]
  apply measure_mono_null _ (nuInf_Iic M)
  intro s hs
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Γ] at hs
  simp only [Set.mem_Iic]; linarith

lemma Kgt (q : ℝ × ℝ) (hq : q.1 ≤ M.T) :
    Kk M q {q' | M.T < q'.1} = ENNReal.ofReal (Real.exp (-M.lam * (M.T - q.1))) := by
  rw [Kk_set _ _ (measurableSet_lt measurable_const measurable_fst)]
  have : Γ M q ⁻¹' {q' | M.T < q'.1} = Set.Ioi (M.T - q.1) := by
    ext s; simp only [Set.mem_preimage, Set.mem_setOf_eq, Γ, Set.mem_Ioi]; constructor <;>
      intro h <;> linarith
  rw [this, nuInf_Ioi M _ (by linarith)]

lemma Kexp (q : ℝ × ℝ) :
    ∫⁻ q', ENNReal.ofReal (Real.exp (-q'.1)) ∂(Kk M q)
      = ENNReal.ofReal (Real.exp (-q.1)) * ENNReal.ofReal (M.lam / (M.lam + 1)) := by
  have hl := M.lam_pos
  rw [Kk_apply, lintegral_map (by fun_prop) (Γ_meas q), nuInf,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  have h : ∀ s : ℝ, ((fun s => ENNReal.ofReal (M.lam * Real.exp (-M.lam * s))) *
      (fun s => ENNReal.ofReal (Real.exp (-(Γ M q s).1)))) s
      = ENNReal.ofReal (Real.exp (-q.1)) *
        ENNReal.ofReal (M.lam * Real.exp ((-(M.lam + 1)) * s)) := by
    intro s
    simp only [Pi.mul_apply, Γ]
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [show -(q.1 + s) = -q.1 + -s by ring, Real.exp_add,
      show -(M.lam + 1) * s = -M.lam * s + -s by ring, Real.exp_add]
    ring
  simp_rw [h]
  rw [lintegral_const_mul _ (by fun_prop)]
  congr 1
  have hint : IntegrableOn (fun s => M.lam * Real.exp (-(M.lam + 1) * s)) (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun s => by positivity)]
  congr 1
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith)]
  simp only [mul_zero, Real.exp_zero]
  field_simp

lemma margExp (p : ℝ × ℝ) : ∀ k, ∫⁻ q, ENNReal.ofReal (Real.exp (-q.1)) ∂((Kk M ^ k) p)
    = ENNReal.ofReal (Real.exp (-p.1)) * ENNReal.ofReal (M.lam / (M.lam + 1)) ^ k := by
  intro k
  induction k with
  | zero => rw [pow_zero_apply, lintegral_dirac' _ (by fun_prop)]; simp
  | succ k ih =>
    rw [pow_succ']
    change ∫⁻ q, _ ∂((Kk M ∘ₖ (Kk M ^ k)) p) = _
    rw [Kernel.lintegral_comp _ _ _ (by fun_prop)]
    simp_rw [Kexp]
    rw [lintegral_mul_const _ (by fun_prop), ih, pow_succ, mul_assoc]

lemma margLe_tendsto (p : ℝ × ℝ) :
    Tendsto (fun k => (Kk M ^ k) p {q | q.1 ≤ M.T}) atTop (𝓝 0) := by
  have hl := M.lam_pos
  set c := ENNReal.ofReal (M.lam / (M.lam + 1))
  have hc : c < 1 := by
    rw [ENNReal.ofReal_lt_one, div_lt_one (by linarith)]; linarith
  have hbound : ∀ k, (Kk M ^ k) p {q | q.1 ≤ M.T}
      ≤ ENNReal.ofReal (Real.exp M.T) * (ENNReal.ofReal (Real.exp (-p.1)) * c ^ k) := by
    intro k
    rw [← margExp p k, ← lintegral_const_mul _ (by fun_prop),
      ← lintegral_indicator_one (measurableSet_le measurable_fst measurable_const)]
    apply lintegral_mono
    intro q
    by_cases hq : q.1 ≤ M.T
    · rw [Set.indicator_of_mem (by exact hq)]
      show (1:ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp M.T) * ENNReal.ofReal (Real.exp (-q.1))
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      rw [Real.one_le_exp_iff]; linarith
    · rw [Set.indicator_of_notMem (by exact hq)]; exact zero_le'
  have hlim : Tendsto (fun k => ENNReal.ofReal (Real.exp M.T) *
      (ENNReal.ofReal (Real.exp (-p.1)) * c ^ k)) atTop (𝓝 0) := by
    have h1 := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hc
    have h2 := ENNReal.Tendsto.const_mul h1 (Or.inr (ENNReal.ofReal_ne_top (r := Real.exp (-p.1))))
    have h3 := ENNReal.Tendsto.const_mul h2 (Or.inr (ENNReal.ofReal_ne_top (r := Real.exp M.T)))
    simpa using h3
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun k => zero_le') hbound

end P51

namespace P51
open MDPFinance.JumpMarkets ProbabilityTheory
variable {d : ℕ} {M : JumpMarket d}

lemma tele (p : ℝ × ℝ) (hp : p.1 ≤ M.T) :
    ∑' k, ∫⁻ q in {q : ℝ × ℝ | q.1 ≤ M.T},
      ENNReal.ofReal (Real.exp (-M.lam * (M.T - q.1))) ∂((Kk M ^ k) p) = 1 := by
  have hS : MeasurableSet {q : ℝ × ℝ | q.1 ≤ M.T} := measurableSet_le measurable_fst measurable_const
  have hSc : {q : ℝ × ℝ | q.1 ≤ M.T}ᶜ = {q | M.T < q.1} := by ext q; simp
  set a : ℕ → ℝ≥0∞ := fun k => (Kk M ^ k) p {q | q.1 ≤ M.T}
  set t : ℕ → ℝ≥0∞ := fun k => ∫⁻ q in {q : ℝ × ℝ | q.1 ≤ M.T},
      ENNReal.ofReal (Real.exp (-M.lam * (M.T - q.1))) ∂((Kk M ^ k) p)
  have hrec : ∀ k, t k + a (k + 1) = a k := by
    intro k
    have h1 : a (k + 1) = ∫⁻ b in {q : ℝ × ℝ | q.1 ≤ M.T}, Kk M b {q | q.1 ≤ M.T} ∂((Kk M ^ k) p) := by
      simp only [a]
      rw [Kernel.pow_succ_apply_eq_lintegral _ _ _ hS, ← lintegral_add_compl _ hS]
      have h0 : ∫⁻ b in {q : ℝ × ℝ | q.1 ≤ M.T}ᶜ, Kk M b {q | q.1 ≤ M.T} ∂((Kk M ^ k) p) = 0 := by
        rw [setLIntegral_congr_fun hS.compl (g := fun _ => 0) (fun b hb => by
          rw [hSc] at hb; exact Kle b hb)]
        simp
      rw [h0, add_zero]
    have h2 : t k = ∫⁻ b in {q : ℝ × ℝ | q.1 ≤ M.T}, Kk M b {q | M.T < q.1} ∂((Kk M ^ k) p) := by
      simp only [t]
      exact setLIntegral_congr_fun hS (fun b hb => (Kgt b hb).symm)
    rw [h1, h2, ← lintegral_add_left (Kernel.measurable_coe _
      (measurableSet_lt measurable_const measurable_fst))]
    have h3 : ∀ b, Kk M b {q | M.T < q.1} + Kk M b {q | q.1 ≤ M.T} = 1 := by
      intro b
      rw [← hSc, add_comm, measure_add_measure_compl hS, measure_univ]
    simp_rw [h3]
    simp [a, Measure.restrict_apply_univ]
  have hsum : ∀ n, (∑ k ∈ Finset.range n, t k) + a n = 1 := by
    intro n
    induction n with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, zero_add, a]
      rw [pow_zero_apply, Measure.dirac_apply' _ hS, Set.indicator_of_mem (by exact hp)]
      rfl
    | succ n ih => rw [Finset.sum_range_succ, add_assoc, hrec, ih]
  apply le_antisymm
  · apply ENNReal.tsum_le_of_sum_range_le
    intro n; rw [← hsum n]; exact le_self_add
  · have hlim : Tendsto (fun n => (∑' k, t k) + a n) atTop (𝓝 ((∑' k, t k) + 0)) :=
      tendsto_const_nhds.add (margLe_tendsto p)
    rw [add_zero] at hlim
    apply ge_of_tendsto' hlim
    intro n; rw [← hsum n]
    gcongr
    exact ENNReal.sum_le_tsum _

lemma ae_Φ (hdeg : IsDeg M) (g : HistPolicy d) (Pr' : ℝ × ℝ → Measure (ℕ → ℝ × ℝ))
    (hc : M.IsChainLaw g Pr') (p : ℝ × ℝ) : ∀ᵐ w ∂Pr' p, ∀ k, Φ M (w k) = Φ M p := by
  rw [ae_all_iff]; intro k
  have hm : MeasurableSet {q : ℝ × ℝ | Φ M q ≠ Φ M p} :=
    (measurableSet_eq_fun Φ_meas measurable_const).compl
  rw [ae_iff]
  have : {w : ℕ → ℝ × ℝ | ¬ Φ M (w k) = Φ M p} = {w | w k ∈ {q | Φ M q ≠ Φ M p}} := rfl
  rw [this, law hdeg g Pr' hc p k _ hm]; exact margΦ p k

theorem Vpi_deg (hdeg : IsDeg M) (g : HistPolicy d) (Pr' : ℝ × ℝ → Measure (ℕ → ℝ × ℝ))
    (hc : M.IsChainLaw g Pr') (p : ℝ × ℝ) (hp : p ∈ M.E) :
    M.Vpi g Pr' p = ENNReal.ofReal (vv M p) := by
  haveI := hc.1 p
  have hpT : p.1 ≤ M.T := hp.1.2
  have hΦ := ae_Φ hdeg g Pr' hc p
  have hex : ∀ᵐ w ∂Pr' p, ∃ k, (w k).1 ≤ M.T ∧ M.T < (w (k + 1)).1 := by
    rw [ae_iff]
    have hsub : {w : ℕ → ℝ × ℝ | ¬ ∃ k, (w k).1 ≤ M.T ∧ M.T < (w (k + 1)).1} ⊆
        {w | w 0 ∈ {q : ℝ × ℝ | M.T < q.1}} ∪ ⋂ k, {w | w k ∈ {q : ℝ × ℝ | q.1 ≤ M.T}} := by
      intro w hw
      by_cases h0 : M.T < (w 0).1
      · left; exact h0
      · right
        simp only [Set.mem_iInter, Set.mem_setOf_eq]
        intro k
        induction k with
        | zero => exact not_lt.mp h0
        | succ k ih => by_contra hk; exact hw ⟨k, ih, not_le.mp hk⟩
    apply measure_mono_null hsub (measure_union_null ?_ ?_)
    · rw [law hdeg g Pr' hc p 0 _ (measurableSet_lt measurable_const measurable_fst),
        pow_zero_apply, Measure.dirac_apply' _ (measurableSet_lt measurable_const measurable_fst),
        Set.indicator_of_notMem (by simp only [Set.mem_setOf_eq, not_lt]; exact hpT)]
    · refine le_antisymm (ge_of_tendsto' (margLe_tendsto (M := M) p) ?_) bot_le
      intro n
      rw [← law hdeg g Pr' hc p n _ (measurableSet_le measurable_fst measurable_const)]
      exact measure_mono (Set.iInter_subset _ n)
  unfold JumpMarket.Vpi
  have hae : ∀ᵐ w ∂Pr' p, ENNReal.ofReal (M.U (M.terminalWealth g w))
      = ENNReal.ofReal (vv M p) := by
    filter_upwards [hΦ, hex] with w hw1 hw2
    unfold JumpMarket.terminalWealth
    rw [dif_pos hw2]
    have hk := hw2.choose_spec
    rw [phi_deg hdeg, max_eq_left (by linarith [hk.1]), vv, ← hw1 hw2.choose]
    rfl
  rw [lintegral_congr_ae hae, lintegral_const, measure_univ, mul_one]

theorem Jinfpi_deg (hdeg : IsDeg M) (f : ℕ → ℝ × ℝ → Control d)
    (Pr' : ℝ × ℝ → Measure (ℕ → ℝ × ℝ)) (hc : M.IsChainLaw (ofMarkov f) Pr')
    (p : ℝ × ℝ) (hp : p ∈ M.E) :
    M.Jinfpi f Pr' p = ENNReal.ofReal (vv M p) := by
  have hS : MeasurableSet {q : ℝ × ℝ | q.1 ≤ M.T} := measurableSet_le measurable_fst measurable_const
  have hΦ := ae_Φ hdeg _ Pr' hc p
  unfold JumpMarket.Jinfpi
  let F : ℝ × ℝ → ℝ≥0∞ := fun q => if q.1 ≤ M.T then
    ENNReal.ofReal (Real.exp (-M.lam * (M.T - q.1))) * ENNReal.ofReal (vv M p) else 0
  have hF : Measurable F := Measurable.ite hS (by fun_prop) measurable_const
  have hae : ∀ᵐ w ∂Pr' p, (∑' k, if (w k).1 ≤ M.T then ENNReal.ofReal (M.r (f k (w k)) (w k))
      else 0) = ∑' k, F (w k) := by
    filter_upwards [hΦ] with w hw
    congr 1; funext k
    simp only [F]
    split_ifs with h
    · rw [r_deg hdeg, max_eq_left (by linarith), ← ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 2
      rw [vv, ← hw k]; rfl
    · rfl
  rw [lintegral_congr_ae hae, lintegral_tsum (f := fun k (w : ℕ → ℝ × ℝ) => F (w k))
    (fun k => (hF.comp (measurable_pi_apply k)).aemeasurable)]
  have hk : ∀ k, ∫⁻ w, F (w k) ∂Pr' p = ENNReal.ofReal (vv M p) *
      ∫⁻ q in {q : ℝ × ℝ | q.1 ≤ M.T}, ENNReal.ofReal (Real.exp (-M.lam * (M.T - q.1)))
        ∂((Kk M ^ k) p) := by
    intro k
    rw [← lintegral_map hF (measurable_pi_apply k), law_map hdeg _ Pr' hc p k,
      ← lintegral_indicator hS, ← lintegral_const_mul _ ((by fun_prop :
        Measurable (fun q : ℝ × ℝ => ENNReal.ofReal (Real.exp (-M.lam * (M.T - q.1))))).indicator hS)]
    congr 1; funext q
    simp only [F, Set.indicator, Set.mem_setOf_eq]
    split_ifs <;> simp [mul_comm]
  simp_rw [hk]
  rw [ENNReal.tsum_mul_left, tele p hp.1.2, mul_one]

end P51

namespace P51
open MDPFinance.JumpMarkets
variable {d : ℕ} {M : JumpMarket d}

lemma r_indep (hdeg : IsDeg M) (a a' : Control d) (p : ℝ × ℝ) : M.r a p = M.r a' p := by
  rw [r_deg hdeg, r_deg hdeg]

lemma Q_indep (hdeg : IsDeg M) (a a' : Control d) (p : ℝ × ℝ) : M.Q a p = M.Q a' p := by
  rw [Q_deg hdeg, Q_deg hdeg]

lemma TOf_val (hdeg : IsDeg M) {f f' : ℝ × ℝ → ℝ} (h : M.IsTOf f f') (p : ℝ × ℝ)
    (hp : p ∈ M.E) : f' p = M.r (a0 d) p + ∫ q, f q ∂(M.Q (a0 d) p) := by
  have hset : {y : ℝ | ∃ a : Control d, y = M.r a p + ∫ q, f q ∂(M.Q a p)}
      = {M.r (a0 d) p + ∫ q, f q ∂(M.Q (a0 d) p)} := by
    ext y; constructor
    · rintro ⟨a, rfl⟩; rw [r_indep hdeg a (a0 d), Q_indep hdeg a (a0 d)]; rfl
    · intro hy; exact ⟨a0 d, hy⟩
  have := h p hp
  rw [hset] at this
  exact this.unique isLUB_singleton

def FC (M : JumpMarket d) (f : ℝ × ℝ → ℝ) : Prop :=
  ∀ p ∈ M.E, ContinuousOn (fun s => f (Γ M p s)) (Set.Icc 0 (M.T - p.1))

lemma Γ_cont (p : ℝ × ℝ) : Continuous (Γ M p) := by unfold Γ; fun_prop

lemma FC_of_cont {f : ℝ × ℝ → ℝ} (hf : ContinuousOn f M.E) : FC M f := by
  intro p hp
  exact hf.comp (Γ_cont p).continuousOn (fun s hs => Γ_mem p hp s hs)

lemma integrable_of_FC {f : ℝ × ℝ → ℝ} (p : ℝ × ℝ)
    (hc : ContinuousOn (fun s => f (Γ M p s)) (Set.Icc 0 (M.T - p.1))) :
    Integrable (fun s => f (Γ M p s)) (nuP M p) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine Integrable.of_bound ?_ C ?_
  · exact ((hc.mono Set.Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo).mono_ac
      (nuP_ac p)
  · filter_upwards [nuP_ae p] with s hs
    exact hC s (Set.Ioo_subset_Icc_self hs)

lemma bfun_cont (gamma : ℝ) : Continuous (M.bfun gamma) := by
  unfold JumpMarket.bfun; fun_prop

lemma b_bound (hdeg : IsDeg M) {gamma alpha : ℝ} (hb : M.IsBoundingFunction (M.bfun gamma) alpha)
    (halpha0 : 0 ≤ alpha) (p : ℝ × ℝ) (hp : p ∈ M.E) :
    ∫ s, M.bfun gamma (Γ M p s) ∂(nuP M p) ≤ alpha * M.bfun gamma p := by
  have h := hb.2.2 p hp (a0 d)
  rw [lintegral_Q hdeg] at h
  have hnn : ∀ s, 0 ≤ M.bfun gamma (Γ M p s) := by
    intro s
    have := hp.2; simp only [Set.mem_Ici] at this
    unfold JumpMarket.bfun Γ; positivity
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnn)
    ((bfun_cont gamma).comp (Γ_cont p)).aestronglyMeasurable]
  have hbp : 0 ≤ alpha * M.bfun gamma p := mul_nonneg halpha0 (hb.1 p hp).le
  calc (∫⁻ s, ENNReal.ofReal (M.bfun gamma (Γ M p s)) ∂(nuP M p)).toReal
      ≤ (ENNReal.ofReal (alpha * M.bfun gamma p)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    _ = alpha * M.bfun gamma p := ENNReal.toReal_ofReal hbp

lemma contract (hdeg : IsDeg M) {gamma alpha : ℝ} (hb : M.IsBoundingFunction (M.bfun gamma) alpha)
    (halpha0 : 0 ≤ alpha) (f1 f2 : ℝ × ℝ → ℝ) (p : ℝ × ℝ) (hp : p ∈ M.E) (K : ℝ) (hK : 0 ≤ K)
    (hc1 : FC M f1) (hc2 : FC M f2)
    (hbd : ∀ q ∈ M.E, |f1 q - f2 q| ≤ K * M.bfun gamma q) :
    |∫ q, f1 q ∂(M.Q (a0 d) p) - ∫ q, f2 q ∂(M.Q (a0 d) p)| ≤ K * (alpha * M.bfun gamma p) := by
  have i1 := integrable_of_FC p (hc1 p hp)
  have i2 := integrable_of_FC p (hc2 p hp)
  have ib := integrable_of_FC (M := M) (f := M.bfun gamma) p
    ((bfun_cont gamma).comp (Γ_cont (M := M) p)).continuousOn
  rw [integral_Q hdeg, integral_Q hdeg, ← integral_sub i1 i2]
  calc |∫ s, (f1 (Γ M p s) - f2 (Γ M p s)) ∂(nuP M p)|
      ≤ ∫ s, |f1 (Γ M p s) - f2 (Γ M p s)| ∂(nuP M p) := abs_integral_le_integral_abs
    _ ≤ ∫ s, K * M.bfun gamma (Γ M p s) ∂(nuP M p) := by
        apply integral_mono_ae (i1.sub i2).abs (ib.const_mul K)
        filter_upwards [nuP_ae p] with s hs
        exact hbd _ (Γ_mem p hp s ⟨hs.1.le, hs.2.le⟩)
    _ = K * ∫ s, M.bfun gamma (Γ M p s) ∂(nuP M p) := integral_const_mul _ _
    _ ≤ K * (alpha * M.bfun gamma p) :=
        mul_le_mul_of_nonneg_left (b_bound hdeg hb halpha0 p hp) hK

lemma step_bound (hdeg : IsDeg M) {gamma alpha : ℝ}
    (hb : M.IsBoundingFunction (M.bfun gamma) alpha) (halpha0 : 0 ≤ alpha)
    {f1 f1' f2 f2' : ℝ × ℝ → ℝ} (h1 : M.IsTOf f1 f1') (h2 : M.IsTOf f2 f2')
    (hc1 : FC M f1) (hc2 : FC M f2) (K : ℝ) (hK : 0 ≤ K)
    (hbd : ∀ q ∈ M.E, |f1 q - f2 q| ≤ K * M.bfun gamma q) :
    ∀ p ∈ M.E, |f1' p - f2' p| ≤ (K * alpha) * M.bfun gamma p := by
  intro p hp
  rw [TOf_val hdeg h1 p hp, TOf_val hdeg h2 p hp,
    show ∀ x y z : ℝ, x + y - (x + z) = y - z from fun x y z => by ring, mul_assoc]
  exact contract hdeg hb halpha0 f1 f2 p hp K hK hc1 hc2 hbd

lemma nuP_integral (p : ℝ × ℝ) (g : ℝ → ℝ) :
    ∫ u, g u ∂(nuP M p) = ∫ u in Set.Ioo 0 (M.T - p.1), M.lam * Real.exp (-M.lam * u) * g u := by
  have h : nuP M p = (volume.restrict (Set.Ioo 0 (M.T - p.1))).withDensity
      (fun u => ((M.lam * Real.exp (-M.lam * u)).toNNReal : ℝ≥0∞)) := rfl
  rw [h, integral_withDensity_eq_integral_smul (by fun_prop)]
  congr 1; funext u
  rw [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (by have := M.lam_pos; positivity)]

lemma Γ_Γ (p : ℝ × ℝ) (s u : ℝ) (hs : 0 ≤ s) (hu : 0 ≤ u) :
    Γ M (Γ M p s) u = Γ M p (s + u) := by
  simp only [Γ, max_eq_left hs, max_eq_left hu, max_eq_left (add_nonneg hs hu)]
  ext
  · simp; ring
  · simp only; rw [mul_add, Real.exp_add]; ring

lemma FC_T (hdeg : IsDeg M) {f f' : ℝ × ℝ → ℝ} (h : M.IsTOf f f') (hc : FC M f) : FC M f' := by
  intro p hp
  have hτ : 0 ≤ M.T - p.1 := by linarith [hp.1.2]
  set τ := M.T - p.1 with hτdef
  let G : ℝ → ℝ := fun w => M.lam * Real.exp (-M.lam * w) * f (Γ M p w)
  have hG : ContinuousOn G (Set.Icc 0 τ) :=
    (by fun_prop : Continuous (fun w : ℝ => M.lam * Real.exp (-M.lam * w))).continuousOn.mul
      (hc p hp)
  have hGi : IntegrableOn G (Set.uIcc 0 τ) := by
    rw [Set.uIcc_of_le hτ]; exact hG.integrableOn_Icc
  have hprim := intervalIntegral.continuousOn_primitive_interval_left hGi
  rw [Set.uIcc_of_le hτ] at hprim
  have heq : ∀ s ∈ Set.Icc 0 τ, f' (Γ M p s) = Real.exp (-M.lam * (τ - s)) * vv M p
      + Real.exp (M.lam * s) * ∫ w in s..τ, G w := by
    intro s hs
    have hmem := Γ_mem p hp s hs
    rw [TOf_val hdeg h _ hmem, r_E hdeg _ _ hmem, vv_Γ p s hs.1, integral_Q hdeg, nuP_integral]
    have h1 : M.T - (Γ M p s).1 = τ - s := by simp only [Γ, hτdef]; ring
    rw [h1]
    congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [hs.2])]
    have hcongr : Set.EqOn (fun u => M.lam * Real.exp (-M.lam * u) * f (Γ M (Γ M p s) u))
        (fun u => Real.exp (M.lam * s) * G (s + u)) (Set.uIcc 0 (τ - s)) := by
      intro u hu
      rw [Set.uIcc_of_le (by linarith [hs.2])] at hu
      simp only [G]
      rw [Γ_Γ p s u hs.1 hu.1]
      rw [show -M.lam * (s + u) = -(M.lam * s) + -M.lam * u by ring, Real.exp_add, Real.exp_neg]
      field_simp
    rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_add_left (fun w => G w) s]
    simp
  have hcont : ContinuousOn (fun s => Real.exp (-M.lam * (τ - s)) * vv M p
      + Real.exp (M.lam * s) * ∫ w in s..τ, G w) (Set.Icc 0 τ) :=
    ((by fun_prop : Continuous (fun s : ℝ => Real.exp (-M.lam * (τ - s)) * vv M p)).continuousOn).add
      ((by fun_prop : Continuous (fun s : ℝ => Real.exp (M.lam * s))).continuousOn.mul hprim)
  exact hcont.congr heq

lemma vv_FC : FC M (vv M) := by
  intro p hp
  exact continuousOn_const.congr (fun s hs => vv_Γ p s hs.1)

lemma vv_TOf (hdeg : IsDeg M) : M.IsTOf (vv M) (vv M) := by
  intro p hp
  have hset : {y : ℝ | ∃ a : Control d, y = M.r a p + ∫ q, vv M q ∂(M.Q a p)} = {vv M p} := by
    ext y; constructor
    · rintro ⟨a, rfl⟩; exact vv_TOf_val hdeg a p hp
    · intro hy; exact ⟨a0 d, by rw [hy, vv_TOf_val hdeg (a0 d) p hp]⟩
  rw [hset]; exact isLUB_singleton

lemma iter (hdeg : IsDeg M) {gamma alpha : ℝ} (hb : M.IsBoundingFunction (M.bfun gamma) alpha)
    (halpha0 : 0 ≤ alpha) (h : ℕ → ℝ × ℝ → ℝ) (hT : ∀ n, M.IsTOf (h n) (h (n + 1)))
    (hc0 : FC M (h 0)) (K0 : ℝ) (hK0 : 0 ≤ K0)
    (hbd : ∀ q ∈ M.E, |h 0 q - vv M q| ≤ K0 * M.bfun gamma q) :
    ∀ n, ∀ q ∈ M.E, |h n q - vv M q| ≤ K0 * alpha ^ n * M.bfun gamma q := by
  have hFC : ∀ n, FC M (h n) := by
    intro n
    induction n with
    | zero => exact hc0
    | succ n ih => exact FC_T hdeg (hT n) ih
  intro n
  induction n with
  | zero => simpa using hbd
  | succ n ih =>
    have := step_bound hdeg hb halpha0 (hT n) (vv_TOf hdeg) (hFC n) vv_FC (K0 * alpha ^ n)
      (mul_nonneg hK0 (pow_nonneg halpha0 n)) ih
    intro q hq
    have := this q hq
    rw [pow_succ]; linarith [show K0 * alpha ^ n * alpha * M.bfun gamma q
      = K0 * (alpha ^ n * alpha) * M.bfun gamma q by ring]

lemma zero_of_geom {x K y alpha : ℝ} (halpha0 : 0 ≤ alpha) (halpha : alpha < 1)
    (h : ∀ n : ℕ, |x| ≤ K * alpha ^ n * y) : x = 0 := by
  have hlim : Tendsto (fun n : ℕ => K * alpha ^ n * y) atTop (𝓝 (K * 0 * y)) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one halpha0 halpha).const_mul K).mul_const y
  rw [mul_zero, zero_mul] at hlim
  have := ge_of_tendsto' hlim h
  exact abs_nonpos_iff.mp this

end P51

namespace P51
open MDPFinance.JumpMarkets
variable {d : ℕ} {M : JumpMarket d}

lemma vv_bound (hdeg : IsDeg M) {gamma alpha : ℝ}
    (hb : M.IsBoundingFunction (M.bfun gamma) alpha) :
    ∃ C, 0 ≤ C ∧ ∀ p ∈ M.E, |vv M p| ≤ C * M.bfun gamma p := by
  obtain ⟨cr, hcr⟩ := hb.2.1
  refine ⟨Real.exp (M.lam * M.T) * |cr|, by positivity, fun p hp => ?_⟩
  have h := hcr p hp (a0 d)
  rw [r_E hdeg _ p hp, abs_mul, abs_of_pos (Real.exp_pos _)] at h
  have hbp := hb.1 p hp
  have h1 : |vv M p| = Real.exp (M.lam * (M.T - p.1)) *
      (Real.exp (-M.lam * (M.T - p.1)) * |vv M p|) := by
    rw [← mul_assoc, ← Real.exp_add]; simp
  rw [h1]
  have h2 : Real.exp (M.lam * (M.T - p.1)) ≤ Real.exp (M.lam * M.T) :=
    Real.exp_le_exp.mpr (by have := M.lam_pos; have := hp.1.1; nlinarith)
  have h3 : Real.exp (-M.lam * (M.T - p.1)) * |vv M p| ≤ |cr| * M.bfun gamma p :=
    h.trans (mul_le_mul_of_nonneg_right (le_abs_self cr) hbp.le)
  calc _ ≤ Real.exp (M.lam * M.T) * (|cr| * M.bfun gamma p) :=
        mul_le_mul h2 h3 (by positivity) (by positivity)
    _ = _ := by ring

lemma vv_IMcv (hdeg : IsDeg M) {gamma alpha : ℝ}
    (hb : M.IsBoundingFunction (M.bfun gamma) alpha) : M.IMcv (M.bfun gamma) (vv M) := by
  obtain ⟨C, -, hC⟩ := vv_bound hdeg hb
  have hρ := M.rho_nonneg
  refine ⟨⟨C, hC⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact M.U_cont.comp (by unfold Φ; fun_prop : Continuous (Φ M)).continuousOn
      (fun p hp => Φ_nonneg p hp)
  · intro t _
    refine ⟨convex_Ici 0, fun x hx y hy a b ha hb' hab => ?_⟩
    simp only [vv, Φ, smul_eq_mul]
    have hc : 0 < Real.exp (M.rho * (M.T - t)) := Real.exp_pos _
    have hx' : x * Real.exp (M.rho * (M.T - t)) ∈ Set.Ici (0:ℝ) := mul_nonneg hx hc.le
    have hy' : y * Real.exp (M.rho * (M.T - t)) ∈ Set.Ici (0:ℝ) := mul_nonneg hy hc.le
    have := M.U_concave.concaveOn.2 hx' hy' ha hb' hab
    simp only [smul_eq_mul] at this
    convert this using 2
    ring
  · intro t _ x hx y hy hxy
    simp only [vv, Φ]
    exact M.U_mono.monotoneOn (mul_nonneg hx (Real.exp_pos _).le)
      (mul_nonneg hy (Real.exp_pos _).le) (mul_le_mul_of_nonneg_right hxy (Real.exp_pos _).le)
  · intro x hx t _ t' _ htt
    simp only [vv, Φ]
    apply M.U_mono.monotoneOn (mul_nonneg hx (Real.exp_pos _).le)
      (mul_nonneg hx (Real.exp_pos _).le)
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hx
  · intro p hp
    simp only [vv, Φ]
    have hx : 0 ≤ p.2 := hp.2
    apply M.U_mono.monotoneOn hx (mul_nonneg hx (Real.exp_pos _).le)
    exact le_mul_of_one_le_right hx (Real.one_le_exp (by nlinarith [hp.1.2]))

lemma phiRel_indep (hdeg : IsDeg M) (α α' : RelaxedControl d) (t x : ℝ) :
    M.phiRel α t x = M.phiRel α' t x := by
  simp [JumpMarket.phiRel, (hdeg _).1]

lemma rRel_indep (hdeg : IsDeg M) (α α' : RelaxedControl d) (p : ℝ × ℝ) :
    M.rRel α p = M.rRel α' p := by
  simp only [JumpMarket.rRel, phiRel_indep hdeg α α']

lemma QRel_eq (hdeg : IsDeg M) (α : RelaxedControl d) (p : ℝ × ℝ) :
    M.QRel α p = ((volume.restrict (Set.Ioo (0 : ℝ) (M.T - p.1))).withDensity
      (fun s => ENNReal.ofReal (M.lam * Real.exp (-M.lam * s)))).bind
      (fun s => Measure.dirac (p.1 + s, M.phiRel α s p.2)) := by
  unfold JumpMarket.QRel
  congr 1; funext s
  have hGm : Measurable (fun uy : Ucal d × (Fin d → ℝ) => (p.1 + s, M.phiRel α s p.2 *
      (1 + ∑ i, (uy.1 : Fin d → ℝ) i * uy.2 i))) :=
    measurable_const.prodMk (measurable_const.mul (measurable_const.add
      (Finset.measurable_sum _ (fun i _ =>
        ((measurable_pi_apply i).comp (measurable_subtype_coe.comp measurable_fst)).mul
          ((measurable_pi_apply i).comp measurable_snd)))))
  rw [QY_dirac hdeg, Measure.prod_dirac, Measure.map_map hGm measurable_prodMk_right]
  have : ((fun uy : Ucal d × (Fin d → ℝ) => (p.1 + s, M.phiRel α s p.2 *
      (1 + ∑ i, (uy.1 : Fin d → ℝ) i * uy.2 i))) ∘ fun x => (x, (0 : Fin d → ℝ)))
      = fun _ => (p.1 + s, M.phiRel α s p.2) := by
    funext u; simp
  rw [this, Measure.map_const, measure_univ, one_smul]

lemma QRel_indep (hdeg : IsDeg M) (α α' : RelaxedControl d) (p : ℝ × ℝ) :
    M.QRel α p = M.QRel α' p := by
  rw [QRel_eq hdeg, QRel_eq hdeg]; simp_rw [phiRel_indep hdeg α α']

lemma AstarRel_univ (hdeg : IsDeg M) (F : ℝ × ℝ → ℝ≥0∞) (p : ℝ × ℝ) :
    M.AstarRel F p = Set.univ := by
  ext α
  simp only [JumpMarket.AstarRel, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  intro α'
  unfold JumpMarket.LRel
  rw [rRel_indep hdeg α' α, QRel_indep hdeg α' α]

lemma Jstat_deg (hdeg : IsDeg M) (Pr : HistPolicy d → ℝ × ℝ → Measure (ℕ → ℝ × ℝ))
    (hPr : ∀ g, M.IsChainLaw g (Pr g)) (f : ℝ × ℝ → Control d) (p : ℝ × ℝ) (hp : p ∈ M.E) :
    M.Jstat Pr f p = ENNReal.ofReal (vv M p) := by
  unfold JumpMarket.Jstat
  exact Jinfpi_deg hdeg (fun _ => f) _ (hPr _) p hp

end P51

open MeasureTheory Filter Topology MDPFinance.JumpMarkets in
theorem solution {d : ℕ} (M : JumpMarket d) (gamma alpha : ℝ)
    (hb : M.IsBoundingFunction (M.bfun gamma) alpha) (halpha0 : 0 ≤ alpha) (halpha : alpha < 1)
    (Pr : HistPolicy d → ℝ × ℝ → Measure (ℕ → ℝ × ℝ))
    (hPr : ∀ g, M.IsChainLaw g (Pr g)) :
    ∃ v : ℝ × ℝ → ℝ, M.IMcv (M.bfun gamma) v ∧
      (∀ p ∈ M.E, M.V Pr p = ENNReal.ofReal (v p)) ∧
      (∀ p ∈ M.E, M.Jinf Pr p = ENNReal.ofReal (v p)) ∧
      (∀ h : ℕ → ℝ × ℝ → ℝ, M.IsTChain (fun p => M.U p.2) h →
        ∀ p ∈ M.E, Tendsto (fun n => h n p) atTop (𝓝 (v p))) ∧
      (M.IsTOf v v ∧
        ∀ w : ℝ × ℝ → ℝ, M.IMcv (M.bfun gamma) w → M.IsTOf w w → ∀ p ∈ M.E, w p = v p) ∧
      (∀ (g : ℝ × ℝ → ℝ) (h : ℕ → ℝ × ℝ → ℝ) (C : ℝ),
        M.IMcv (M.bfun gamma) g → M.IsTChain g h →
        (∀ p ∈ M.E, |h 1 p - g p| ≤ C * M.bfun gamma p) →
        ∀ (n : ℕ), ∀ p ∈ M.E,
          |v p - h n p| ≤ (alpha ^ n / (1 - alpha)) * C * M.bfun gamma p) ∧
      (∃ fstar : ℝ × ℝ → Control d, Measurable fstar ∧
        (∀ p ∈ M.E, fstar p ∈ M.Astar (fun q => ENNReal.ofReal (v q)) p) ∧
        ∀ p ∈ M.E, M.Jstat Pr fstar p = M.V Pr p) ∧
      (∀ h : ℕ → ℝ × ℝ → ℝ, M.IsTChain (fun p => M.U p.2) h →
        ∀ p ∈ M.E,
          (LsSeq (fun n => M.AstarRel (fun q => ENNReal.ofReal (h n q)) p)).Nonempty ∧
          LsSeq (fun n => M.AstarRel (fun q => ENNReal.ofReal (h n q)) p) ⊆
            M.AstarRel (fun q => ENNReal.ofReal (v q)) p) ∧
      (∀ f h : ℝ × ℝ → Control d, Measurable f → Measurable h →
        ∀ E0 : Set (ℝ × ℝ), MeasurableSet E0 →
          (∀ p ∈ M.E, p ∈ E0 → M.Jstat Pr f p < M.L (M.Jstat Pr f) (h p) p) →
          (∀ p ∈ M.E, p ∉ E0 → h p = f p) →
          (∀ p ∈ M.E, M.Jstat Pr f p ≤ M.Jstat Pr h p) ∧
            ∀ p ∈ M.E, p ∈ E0 → M.Jstat Pr f p < M.Jstat Pr h p) ∧
      (∀ f : ℝ × ℝ → Control d, Measurable f →
        (∀ p ∈ M.E, ∀ a : Control d, M.L (M.Jstat Pr f) a p ≤ M.Jstat Pr f p) →
        ∀ p ∈ M.E, M.Jstat Pr f p = M.Jinf Pr p) := by
  classical
  by_cases hdeg : P51.IsDeg M
  swap
  · exfalso
    simp only [P51.IsDeg, not_forall, not_and] at hdeg
    obtain ⟨i, hi⟩ := hdeg
    refine P51.nondeg_false M Pr hPr i ?_
    by_cases h : M.mu i = M.rho
    · exact Or.inr (hi h)
    · exact Or.inl h
  have hV : ∀ p ∈ M.E, M.V Pr p = ENNReal.ofReal (P51.vv M p) := by
    intro p hp
    unfold JumpMarket.V
    apply le_antisymm
    · exact iSup₂_le fun g _ => (P51.Vpi_deg hdeg g (Pr g) (hPr g) p hp).le
    · exact le_iSup₂_of_le (fun _ _ => P51.a0 d) (fun _ => measurable_const)
        (P51.Vpi_deg hdeg _ (Pr _) (hPr _) p hp).ge
  have hJ : ∀ p ∈ M.E, M.Jinf Pr p = ENNReal.ofReal (P51.vv M p) := by
    intro p hp
    unfold JumpMarket.Jinf
    apply le_antisymm
    · exact iSup₂_le fun f _ => (P51.Jinfpi_deg hdeg f _ (hPr _) p hp).le
    · exact le_iSup₂_of_le (fun _ _ => P51.a0 d) (fun _ => measurable_const)
        (P51.Jinfpi_deg hdeg _ _ (hPr _) p hp).ge
  obtain ⟨Cv, hCv0, hCv⟩ := P51.vv_bound hdeg hb
  have hbpos := hb.1
  have hdiff : ∀ w : ℝ × ℝ → ℝ, M.IMcv (M.bfun gamma) w →
      ∃ K, 0 ≤ K ∧ ∀ q ∈ M.E, |w q - P51.vv M q| ≤ K * M.bfun gamma q := by
    intro w hw
    obtain ⟨Cw, hCw⟩ := hw.1
    refine ⟨max Cw 0 + Cv, add_nonneg (le_max_right _ _) hCv0, fun q hq => ?_⟩
    have h1 := hCw q hq
    have h2 := hCv q hq
    have hbq := (hbpos q hq).le
    have h3 : Cw * M.bfun gamma q ≤ max Cw 0 * M.bfun gamma q :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hbq
    calc |w q - P51.vv M q| ≤ |w q| + |P51.vv M q| := abs_sub _ _
      _ ≤ max Cw 0 * M.bfun gamma q + Cv * M.bfun gamma q := by linarith
      _ = _ := by ring
  refine ⟨P51.vv M, P51.vv_IMcv hdeg hb, hV, hJ, ?_, ⟨P51.vv_TOf hdeg, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro h hch p hp
    have hFC0 : P51.FC M (h 0) := by
      rw [hch.1]
      intro q hq
      exact M.U_cont.comp ((P51.Γ_cont (M := M) q).snd.continuousOn)
        (fun s hs => (P51.Γ_mem q hq s hs).2)
    have hbd0 : ∀ q ∈ M.E, |h 0 q - P51.vv M q| ≤ Cv * M.bfun gamma q := by
      intro q hq
      rw [hch.1]
      have hU0 : 0 ≤ M.U q.2 := M.U_nonneg _ hq.2
      have hUv : M.U q.2 ≤ P51.vv M q := (P51.vv_IMcv hdeg hb).2.2.2.2.2 q hq
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      have := hCv q hq
      rw [abs_of_nonneg (P51.vv_nonneg q hq)] at this
      linarith
    have hit := P51.iter hdeg hb halpha0 h hch.2 hFC0 Cv hCv0 hbd0
    have hlim : Tendsto (fun n : ℕ => Cv * alpha ^ n * M.bfun gamma p) atTop (𝓝 0) := by
      have := ((tendsto_pow_atTop_nhds_zero_of_lt_one halpha0 halpha).const_mul Cv).mul_const
        (M.bfun gamma p)
      simpa using this
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _)
      (fun n => by rw [Real.norm_eq_abs]; exact hit n p hp) hlim
  · intro w hw hwT p hp
    obtain ⟨K, hK0, hK⟩ := hdiff w hw
    have hit := P51.iter hdeg hb halpha0 (fun _ => w) (fun _ => hwT) (P51.FC_of_cont hw.2.1)
      K hK0 hK
    have := P51.zero_of_geom halpha0 halpha (fun n => hit n p hp)
    linarith
  · intro g h C hg hch hC1 n p hp
    have hC : 0 ≤ C := by
      by_contra hC
      push_neg at hC
      have h1 := hC1 p hp
      have h2 := mul_neg_of_neg_of_pos hC (hbpos p hp)
      linarith [abs_nonneg (h 1 p - g p)]
    obtain ⟨K0, hK00, hK0⟩ := hdiff g hg
    have h1α : 0 < 1 - alpha := by linarith
    have hFCg : P51.FC M g := P51.FC_of_cont hg.2.1
    have hT0 : M.IsTOf g (h 1) := by have := hch.2 0; rwa [hch.1] at this
    have hA : ∀ j : ℕ, ∀ q ∈ M.E, |g q - P51.vv M q|
        ≤ (C / (1 - alpha) + alpha ^ j * K0) * M.bfun gamma q := by
      intro j
      induction j with
      | zero =>
        intro q hq
        have h1 := hK0 q hq
        have h2 : 0 ≤ C / (1 - alpha) * M.bfun gamma q :=
          mul_nonneg (div_nonneg hC h1α.le) (hbpos q hq).le
        rw [pow_zero, one_mul, add_mul]
        linarith
      | succ j ih =>
        intro q hq
        have hKn : 0 ≤ C / (1 - alpha) + alpha ^ j * K0 :=
          add_nonneg (div_nonneg hC h1α.le) (mul_nonneg (pow_nonneg halpha0 j) hK00)
        have hsb := P51.step_bound hdeg hb halpha0 hT0 (P51.vv_TOf hdeg) hFCg P51.vv_FC
          (C / (1 - alpha) + alpha ^ j * K0) hKn ih q hq
        have hg1 := hC1 q hq
        have htri : |g q - P51.vv M q| ≤ |h 1 q - g q| + |h 1 q - P51.vv M q| := by
          calc |g q - P51.vv M q| = |(g q - h 1 q) + (h 1 q - P51.vv M q)| := by ring_nf
            _ ≤ |g q - h 1 q| + |h 1 q - P51.vv M q| := abs_add_le _ _
            _ = _ := by rw [abs_sub_comm (g q)]
        have heq : C + (C / (1 - alpha) + alpha ^ j * K0) * alpha
            = C / (1 - alpha) + alpha ^ (j + 1) * K0 := by
          field_simp
          ring
        have hfin : |g q - P51.vv M q| ≤ (C + (C / (1 - alpha) + alpha ^ j * K0) * alpha)
            * M.bfun gamma q := by
          have e : (C + (C / (1 - alpha) + alpha ^ j * K0) * alpha) * M.bfun gamma q
              = C * M.bfun gamma q + (C / (1 - alpha) + alpha ^ j * K0) * alpha
                * M.bfun gamma q := by ring
          rw [e]; linarith
        rw [heq] at hfin
        exact hfin
    have hB : ∀ q ∈ M.E, |g q - P51.vv M q| ≤ C / (1 - alpha) * M.bfun gamma q := by
      intro q hq
      have hlim : Tendsto (fun j : ℕ => (C / (1 - alpha) + alpha ^ j * K0) * M.bfun gamma q)
          atTop (𝓝 ((C / (1 - alpha) + 0 * K0) * M.bfun gamma q)) :=
        ((tendsto_const_nhds.add ((tendsto_pow_atTop_nhds_zero_of_lt_one halpha0
          halpha).mul_const K0)).mul_const _)
      simp only [zero_mul, add_zero] at hlim
      exact ge_of_tendsto' hlim (fun j => hA j q hq)
    have hFCh0 : P51.FC M (h 0) := by rw [hch.1]; exact hFCg
    have hbd0 : ∀ q ∈ M.E, |h 0 q - P51.vv M q| ≤ C / (1 - alpha) * M.bfun gamma q := by
      rw [hch.1]; exact hB
    have hit := P51.iter hdeg hb halpha0 h hch.2 hFCh0 (C / (1 - alpha))
      (div_nonneg hC h1α.le) hbd0 n p hp
    rw [abs_sub_comm]
    calc |h n p - P51.vv M p| ≤ C / (1 - alpha) * alpha ^ n * M.bfun gamma p := hit
      _ = alpha ^ n / (1 - alpha) * C * M.bfun gamma p := by ring
  · refine ⟨fun _ => P51.a0 d, measurable_const, fun p hp => ?_, fun p hp => ?_⟩
    · intro a'
      rw [P51.vv_L hdeg a' p hp _ (fun q _ => rfl), P51.vv_L hdeg (P51.a0 d) p hp _ (fun q _ => rfl)]
    · rw [P51.Jstat_deg hdeg Pr hPr _ p hp, hV p hp]
  · intro h _ p _
    simp only [P51.AstarRel_univ hdeg]
    refine ⟨⟨(P51.a0 d).toRelaxed, fun _ => (P51.a0 d).toRelaxed, fun _ => Set.mem_univ _, ?_⟩,
      Set.subset_univ _⟩
    rw [MapClusterPt, Filter.map_const]
    exact ClusterPt.of_le_nhds (pure_le_nhds _)
  · intro f h _ _ E0 _ himp _
    refine ⟨fun p hp => le_of_eq ((P51.Jstat_deg hdeg Pr hPr f p hp).trans
      (P51.Jstat_deg hdeg Pr hPr h p hp).symm), fun p hp hpE0 => ?_⟩
    have := himp p hp hpE0
    rw [P51.vv_L hdeg _ p hp _ (fun q hq => P51.Jstat_deg hdeg Pr hPr f q hq),
      P51.Jstat_deg hdeg Pr hPr f p hp] at this
    exact absurd this (lt_irrefl _)
  · intro f _ _ p hp
    rw [P51.Jstat_deg hdeg Pr hPr f p hp, hJ p hp]
