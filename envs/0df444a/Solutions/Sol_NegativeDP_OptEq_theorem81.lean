-- Prove2me | solution 1 for NegativeDP.OptEq.theorem81
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T01:25:28.703322+00:00
-- url     : https://prove2.me/submissions/6f7594e2-cee9-40a9-bab6-f9d865078c08

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return
import Definitions.Def_NegativeDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Operators
import Definitions.Def_NegativeDP_OptEq_Model


/-! Child P4 of the f42af937 plan (Strauch Thm 8.1, negative case): measurable selection from a
Borel set whose sections have positive kernel measure, `p`-a.e. Elementary (Fubini + exhaustion);
no analytic-set theory needed. Used to derandomise the first decision of a near-optimal plan. -/

namespace NegativeDP.OptEq.Sel
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- Exhaustion: if `p`-a.e. section of `D` has positive `ν`-measure, then countably many
`u`-slices of `D` cover `S` up to a `p`-null set. -/
theorem exists_countable_ae_cover {S U : Type*} [MeasurableSpace S] [MeasurableSpace U]
    (p : Measure S) [IsFiniteMeasure p] (ν : Measure U) [SFinite ν]
    (D : Set (S × U)) (hD : MeasurableSet D)
    (h : ∀ᵐ s ∂p, ν (Prod.mk s ⁻¹' D) ≠ 0) :
    ∃ C : Set U, C.Countable ∧ ∀ᵐ s ∂p, ∃ u ∈ C, (s, u) ∈ D := by
  classical
  let G : U → Set S := fun u => (fun s => (s, u)) ⁻¹' D
  have hGm : ∀ u, MeasurableSet (G u) := fun u => measurable_prodMk_right hD
  let φ : Set U → ℝ≥0∞ := fun C => p (⋃ u ∈ C, G u)
  let c : ℝ≥0∞ := ⨆ C : {C : Set U // C.Countable}, φ C.1
  have hc_fin : c ≠ ∞ :=
    ne_top_of_le_ne_top (measure_ne_top p univ) (iSup_le fun C => measure_mono (subset_univ _))
  have hstep : ∀ n : ℕ, ∃ C : {C : Set U // C.Countable}, c - (n : ℝ≥0∞)⁻¹ ≤ φ C.1 := by
    intro n
    by_cases hc0 : c = 0
    · exact ⟨⟨∅, countable_empty⟩, by simp [hc0]⟩
    · have hlt : c - (n : ℝ≥0∞)⁻¹ < c :=
        ENNReal.sub_lt_self hc_fin hc0 (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top n))
      obtain ⟨C, hC⟩ := lt_iSup_iff.1 hlt
      exact ⟨C, hC.le⟩
  choose Cs hCs using hstep
  let C : Set U := ⋃ n, (Cs n).1
  have hCc : C.Countable := countable_iUnion fun n => (Cs n).2
  have hφmono : ∀ n, φ (Cs n).1 ≤ φ C := fun n =>
    measure_mono (biUnion_subset_biUnion_left (subset_iUnion (fun n => (Cs n).1) n))
  have hcle : c ≤ φ C := by
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (a := (ε : ℝ≥0∞)) (by simpa using hε.ne')
    calc c ≤ c - (n : ℝ≥0∞)⁻¹ + (n : ℝ≥0∞)⁻¹ := le_tsub_add
      _ ≤ φ C + ε := add_le_add ((hCs n).trans (hφmono n)) hn.le
  let E : Set S := (⋃ u ∈ C, G u)ᶜ
  have hEm : MeasurableSet E := (MeasurableSet.biUnion hCc fun u _ => hGm u).compl
  have hE : p E = 0 := by
    by_contra hE0
    -- the product measure of `D` under `(p|E) × ν` is positive
    have hpos : ((p.restrict E).prod ν) D ≠ 0 := by
      rw [Measure.prod_apply hD]
      intro h0
      rw [lintegral_eq_zero_iff (measurable_measure_prodMk_left hD)] at h0
      have hae : ∀ᵐ s ∂(p.restrict E), False := by
        filter_upwards [h0, ae_restrict_of_ae h] with s hs1 hs2
        exact hs2 hs1
      have : p.restrict E = 0 := by
        rw [← Measure.measure_univ_eq_zero]
        simpa using (ae_iff.1 hae)
      exact hE0 (by rw [← Measure.restrict_apply_univ, this]; rfl)
    rw [Measure.prod_apply_symm hD] at hpos
    obtain ⟨u, hu⟩ : ∃ u, (p.restrict E) ((fun x => (x, u)) ⁻¹' D) ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hpos (by simp [hall])
    rw [Measure.restrict_apply (measurable_prodMk_right hD)] at hu
    -- adding `u` to `C` strictly increases `φ`
    have hins : (insert u C).Countable := hCc.insert u
    have hunion : (⋃ v ∈ insert u C, G v) = (⋃ v ∈ C, G v) ∪ (G u ∩ E) := by
      ext s
      simp only [mem_iUnion, mem_insert_iff, exists_prop, mem_union, mem_inter_iff, E,
        mem_compl_iff, G]
      constructor
      · rintro ⟨v, hv | hv, hs⟩
        · subst hv
          by_cases h' : ∃ i, i ∈ C ∧ s ∈ (fun s => (s, i)) ⁻¹' D
          · exact Or.inl h'
          · exact Or.inr ⟨hs, h'⟩
        · exact Or.inl ⟨v, hv, hs⟩
      · rintro (⟨v, hv, hs⟩ | ⟨hs, _⟩)
        · exact ⟨v, Or.inr hv, hs⟩
        · exact ⟨u, Or.inl rfl, hs⟩
    have hdisj : Disjoint (⋃ v ∈ C, G v) (G u ∩ E) :=
      disjoint_compl_right.mono_right inter_subset_right
    have hφins : φ (insert u C) = φ C + p (G u ∩ E) := by
      simp only [φ]
      rw [hunion, measure_union hdisj ((hGm u).inter hEm)]
    have hle : φ (insert u C) ≤ c := le_iSup (fun C : {C : Set U // C.Countable} => φ C.1)
      ⟨insert u C, hins⟩
    have hfin : φ C ≠ ∞ := ne_top_of_le_ne_top (measure_ne_top p univ) (measure_mono (subset_univ _))
    have : φ C < φ C + p (G u ∩ E) := ENNReal.lt_add_right hfin (by simpa [G] using hu)
    exact absurd (hφins ▸ hle) (not_le.2 (lt_of_le_of_lt hcle this))
  refine ⟨C, hCc, ?_⟩
  rw [ae_iff]
  convert hE using 2
  ext s
  simp [E, G]

/-- Measurable selection a.e. from a Borel set whose sections have positive measure under a
Markov kernel (derandomisation of a single decision). -/
theorem exists_measurable_selector_of_kernel {S A : Type*} [MeasurableSpace S]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    (p : Measure S) [IsFiniteMeasure p] (κ : Kernel S A) [IsMarkovKernel κ]
    (B : Set (S × A)) (hB : MeasurableSet B) (h : ∀ᵐ s ∂p, κ s (Prod.mk s ⁻¹' B) ≠ 0) :
    ∃ f : S → A, Measurable f ∧ ∀ᵐ s ∂p, (s, f s) ∈ B := by
  classical
  obtain ⟨ψ, hψ, hψκ⟩ := Kernel.exists_measurable_map_eq_unitInterval κ
  let D : Set (S × unitInterval) := {x | (x.1, ψ x.1 x.2) ∈ B}
  have hD : MeasurableSet D := (measurable_fst.prodMk hψ) hB
  have hψs : ∀ s, Measurable (ψ s) := fun s => hψ.comp measurable_prodMk_left
  have h' : ∀ᵐ s ∂p, (volume : Measure unitInterval) (Prod.mk s ⁻¹' D) ≠ 0 := by
    filter_upwards [h] with s hs
    rw [← hψκ s, Measure.map_apply (hψs s) (measurable_prodMk_left hB)] at hs
    exact hs
  obtain ⟨C, hCc, hC⟩ := exists_countable_ae_cover p volume D hD h'
  rcases C.eq_empty_or_nonempty with hCe | hCne
  · refine ⟨fun _ => Classical.arbitrary A, measurable_const, ?_⟩
    filter_upwards [hC] with s ⟨u, hu, _⟩
    simp [hCe] at hu
  obtain ⟨e, he⟩ := hCc.exists_eq_range hCne
  let P : S → ℕ → Prop := fun s k => (s, e k) ∈ D ∨ ∀ m, (s, e m) ∉ D
  have hex : ∀ s, ∃ k, P s k := by
    intro s
    by_cases hs : ∃ m, (s, e m) ∈ D
    · obtain ⟨m, hm⟩ := hs
      exact ⟨m, Or.inl hm⟩
    · push Not at hs
      exact ⟨0, Or.inr hs⟩
  have hPm : ∀ k, MeasurableSet {s | P s k} := by
    intro k
    have h1 : MeasurableSet {s | (s, e k) ∈ D} := measurable_prodMk_right hD
    have h2 : MeasurableSet {s | ∀ m, (s, e m) ∉ D} := by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun m => (measurable_prodMk_right hD).compl
    exact h1.union h2
  have hk : Measurable fun s => Nat.find (hex s) := measurable_find hex hPm
  refine ⟨fun s => ψ s (e (Nat.find (hex s))), ?_, ?_⟩
  · exact hψ.comp (measurable_id.prodMk (measurable_from_nat.comp hk))
  · filter_upwards [hC] with s ⟨u, hu, hsu⟩
    rw [he] at hu
    obtain ⟨j, rfl⟩ := hu
    rcases Nat.find_spec (hex s) with h1 | h2
    · exact h1
    · exact absurd hsu (h2 j)

end NegativeDP.OptEq.Sel



set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open DiscountedDP.Stationary (Hist Plan MarkovPlan MarkovPlan.toPlan stationary)

namespace NegativeDP.Stationary.F42P6

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

/-- Append `(a, t)` to a history (the map used in `historyLaw`). -/
def snoc {n : ℕ} (h : Hist S A n) (a : A) (t : S) : Hist S A (n + 1) :=
  ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => S × A) (Fin.last n)).symm
    ((h.2, a), h.1), t)

/-- Prepend the pair `(s, a)` to a history. -/
def consH (s : S) (a : A) {k : ℕ} (h : Hist S A k) : Hist S A (k + 1) :=
  ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => S × A) 0).symm
    ((s, a), h.1), h.2)

/-- The empty history at state `s`. -/
def start (s : S) : Hist S A 0 := ((fun i : Fin 0 => Fin.elim0 i), s)

lemma measurable_snoc (n : ℕ) :
    Measurable (fun x : (Hist S A n × A) × S => snoc x.1.1 x.1.2 x.2) := by
  unfold snoc; fun_prop

lemma measurable_consH (s : S) (a : A) (k : ℕ) :
    Measurable (fun h : Hist S A k => consH s a h) := by
  unfold consH; fun_prop

lemma measurable_start : Measurable (fun s : S => (start s : Hist S A 0)) := by
  unfold start; fun_prop

lemma snoc_eq {n : ℕ} (h : Hist S A n) (a : A) (t : S) :
    snoc h a t = (Fin.snoc (α := fun _ => S × A) h.1 (h.2, a), t) := by
  show (Fin.insertNth (α := fun _ => S × A) (Fin.last n) (h.2, a) h.1, t) = _
  rw [Fin.insertNth_last']

lemma consH_eq (s : S) (a : A) {k : ℕ} (h : Hist S A k) :
    consH s a h = (Fin.cons (α := fun _ => S × A) (s, a) h.1, h.2) := by
  show (Fin.insertNth (α := fun _ => S × A) 0 (s, a) h.1, h.2) = _
  rw [Fin.insertNth_zero']

lemma snoc_consH (s : S) (a : A) {k : ℕ} (h : Hist S A k) (b : A) (t : S) :
    snoc (consH s a h) b t = consH s a (snoc h b t) := by
  rw [snoc_eq, consH_eq, consH_eq, snoc_eq]
  simp only [Fin.cons_snoc_eq_snoc_cons]
  rfl

lemma consH_start (s : S) (a : A) (t : S) :
    consH s a (start t : Hist S A 0) = snoc (start s) a t := by
  rw [snoc_eq, consH_eq]
  refine Prod.ext ?_ rfl
  funext i
  fin_cases i
  rfl

lemma historyLaw_succ (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) (n : ℕ) :
    historyLaw P π s (n + 1) = (stageLaw P π s n).map (fun x => snoc x.1.1 x.1.2 x.2) := rfl

lemma historyLaw_zero (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) :
    historyLaw P π s 0 = Measure.dirac (start s) := rfl

lemma isProb_historyLaw (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) :
    ∀ n, IsProbabilityMeasure (historyLaw P π s n)
  | 0 => by rw [historyLaw_zero]; infer_instance
  | n + 1 => by
    haveI := isProb_historyLaw P π s n
    haveI := π.κ_markov n
    haveI := P.q_markov
    haveI : IsMarkovKernel (nextKernel P n) := by unfold nextKernel; infer_instance
    haveI : IsProbabilityMeasure (stageLaw P π s n) := by
      show IsProbabilityMeasure ((historyLaw P π s n ⊗ₘ π.κ n) ⊗ₘ nextKernel P n)
      infer_instance
    rw [historyLaw_succ]
    exact Measure.isProbabilityMeasure_map (measurable_snoc n).aemeasurable

lemma lintegral_stageLaw (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) (n : ℕ)
    (G : (Hist S A n × A) × S → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ x, G x ∂stageLaw P π s n =
      ∫⁻ h, ∫⁻ a, ∫⁻ t, G ((h, a), t) ∂P.q (h.2, a) ∂π.κ n h ∂historyLaw P π s n := by
  haveI := π.κ_markov n
  haveI := P.q_markov
  haveI : IsMarkovKernel (nextKernel P n) := by unfold nextKernel; infer_instance
  haveI := isProb_historyLaw P π s n
  have hnk : ∀ ha : Hist S A n × A, nextKernel P n ha = P.q (ha.1.2, ha.2) := fun ha => by
    simp [nextKernel, Kernel.comp_deterministic_eq_comap, Kernel.comap_apply]
  show ∫⁻ x, G x ∂((historyLaw P π s n ⊗ₘ π.κ n) ⊗ₘ nextKernel P n) = _
  rw [Measure.lintegral_compProd hG,
    Measure.lintegral_compProd (f := fun ha => ∫⁻ t, G (ha, t) ∂nextKernel P n ha)
      hG.lintegral_kernel_prod_right']
  simp only [hnk]

lemma lintegral_historyLaw_succ (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S)
    (n : ℕ) (g : Hist S A (n + 1) → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ h', g h' ∂historyLaw P π s (n + 1) =
      ∫⁻ h, ∫⁻ a, ∫⁻ t, g (snoc h a t) ∂P.q (h.2, a) ∂π.κ n h ∂historyLaw P π s n := by
  rw [historyLaw_succ, lintegral_map hg (measurable_snoc n)]
  exact lintegral_stageLaw P π s n _ (hg.comp (measurable_snoc n))

lemma measurable_loss (P : Problem S A) :
    Measurable (fun x : S × A × S => ENNReal.ofReal (-P.r x)) :=
  ENNReal.measurable_ofReal.comp P.r_measurable.neg

lemma stageLoss_eq (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) (n : ℕ) :
    stageLoss P π s n = ∫⁻ h, ∫⁻ a, ∫⁻ t, ENNReal.ofReal (-P.r (h.2, a, t))
      ∂P.q (h.2, a) ∂π.κ n h ∂historyLaw P π s n :=
  lintegral_stageLaw P π s n (fun x => ENNReal.ofReal (-P.r (x.1.1.2, x.1.2, x.2)))
    ((measurable_loss P).comp (by fun_prop))

lemma meas_inner (P : Problem S A) {n : ℕ} (X : (Hist S A n × A) × S → ℝ≥0∞)
    (hX : Measurable X) :
    Measurable (fun ha : Hist S A n × A => ∫⁻ t, X (ha, t) ∂P.q (ha.1.2, ha.2)) := by
  haveI := P.q_markov
  have hm : Measurable (fun ha : Hist S A n × A => (ha.1.2, ha.2)) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  haveI : IsMarkovKernel (P.q.comap _ hm) := Kernel.IsMarkovKernel.comap _ hm
  exact hX.lintegral_kernel_prod_right' (κ := P.q.comap _ hm)


theorem coe_ennreal_real (x : ℝ≥0∞) (hx : x ≠ ⊤) : (x : EReal) = ((x.toReal : ℝ) : EReal) := by
  lift x to NNReal using hx
  rfl

/-- From `-W - ε ≤ -L` get `L ≤ W + ε`. -/
theorem key_le (L W : ℝ≥0∞) (ε : ℝ) (hε : 0 < ε)
    (h : -(W : EReal) - (ε : EReal) ≤ -(L : EReal)) : L ≤ W + ENNReal.ofReal ε := by
  by_cases hW : W = ⊤
  · simp [hW]
  by_cases hL : L = ⊤
  · exfalso
    rw [hL, coe_ennreal_real W hW] at h
    have e : (-((W.toReal : ℝ) : EReal) - (ε : EReal)) = ((-W.toReal - ε : ℝ) : EReal) := by
      norm_cast
    have hne : (-((W.toReal : ℝ) : EReal) - (ε : EReal)) ≠ ⊥ := by
      rw [e]; exact EReal.coe_ne_bot _
    exact hne (by simpa using h)
  rw [coe_ennreal_real W hW, coe_ennreal_real L hL] at h
  have e1 : (-((W.toReal : ℝ) : EReal) - (ε : EReal)) = ((-W.toReal - ε : ℝ) : EReal) := by
    norm_cast
  have e2 : (-((L.toReal : ℝ) : EReal)) = ((-L.toReal : ℝ) : EReal) := by norm_cast
  rw [e1, e2, EReal.coe_le_coe_iff] at h
  rw [← ENNReal.ofReal_toReal hL, ← ENNReal.ofReal_toReal hW,
    ← ENNReal.ofReal_add ENNReal.toReal_nonneg hε.le]
  exact ENNReal.ofReal_le_ofReal (by linarith)

theorem key_ge (L W : ℝ≥0∞) (ε : ℝ) (hε : 0 < ε) (h : L ≤ W + ENNReal.ofReal ε) :
    -(W : EReal) - (ε : EReal) ≤ -(L : EReal) := by
  by_cases hW : W = ⊤
  · simp [hW]
  have hL : L ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hW, ENNReal.ofReal_ne_top⟩) h
  have hr : L.toReal ≤ W.toReal + ε := by
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hW, ENNReal.ofReal_ne_top⟩) h
    rwa [ENNReal.toReal_add hW ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hε.le] at this
  rw [coe_ennreal_real W hW, coe_ennreal_real L hL]
  have e1 : (-((W.toReal : ℝ) : EReal) - (ε : EReal)) = ((-W.toReal - ε : ℝ) : EReal) := by
    norm_cast
  have e2 : (-((L.toReal : ℝ) : EReal)) = ((-L.toReal : ℝ) : EReal) := by norm_cast
  rw [e1, e2, EReal.coe_le_coe_iff]
  linarith

lemma I_nonpos (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) : I P π s ≤ 0 := by
  unfold I
  rw [EReal.neg_le, neg_zero]
  exact EReal.coe_ennreal_nonneg _

lemma vstar_nonpos (P : Problem S A) (s : S) : vstar P s ≤ 0 :=
  iSup_le fun π => I_nonpos P π s

lemma vstar_eq (P : Problem S A) (s : S) :
    vstar P s = -(((-(vstar P s)).toENNReal : ℝ≥0∞) : EReal) := by
  have h0 : 0 ≤ -(vstar P s) := by rw [EReal.le_neg, neg_zero]; exact vstar_nonpos P s
  rw [EReal.coe_toENNReal h0, neg_neg]

noncomputable def epsK (ε : ℝ) (k : ℕ) : ℝ := ε / 2 ^ (k + 1)

lemma epsK_pos {ε : ℝ} (hε : 0 < ε) (k : ℕ) : 0 < epsK ε k := by unfold epsK; positivity

lemma sum_epsK_le {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    ∑ j ∈ Finset.range n, ENNReal.ofReal (epsK ε j) ≤ ENNReal.ofReal ε := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => (epsK_pos hε j).le)]
  refine ENNReal.ofReal_le_ofReal ?_
  have e : ∀ j, epsK ε j = ε / 2 * (1 / 2 : ℝ) ^ j := fun j => by
    unfold epsK; rw [pow_succ, one_div_pow]; field_simp
  simp_rw [e, ← Finset.mul_sum]
  have := sum_geometric_two_le n
  nlinarith


lemma triple_add (P : Problem S A) (π : Plan (S := S) (A := A)) {n : ℕ}
    (μ : Measure (Hist S A n)) (X Y : (Hist S A n × A) × S → ℝ≥0∞) (hX : Measurable X) :
    ∫⁻ h, ∫⁻ a, ∫⁻ t, X ((h, a), t) + Y ((h, a), t) ∂P.q (h.2, a) ∂π.κ n h ∂μ =
      (∫⁻ h, ∫⁻ a, ∫⁻ t, X ((h, a), t) ∂P.q (h.2, a) ∂π.κ n h ∂μ) +
      ∫⁻ h, ∫⁻ a, ∫⁻ t, Y ((h, a), t) ∂P.q (h.2, a) ∂π.κ n h ∂μ := by
  haveI := P.q_markov
  haveI := π.κ_markov n
  have h1 := meas_inner P X hX
  have h2 : Measurable (fun h => ∫⁻ a, ∫⁻ t, X ((h, a), t) ∂P.q (h.2, a) ∂π.κ n h) :=
    h1.lintegral_kernel_prod_right'
  have e3 : ∀ h a, ∫⁻ t, X ((h, a), t) + Y ((h, a), t) ∂P.q (h.2, a) =
      ∫⁻ t, X ((h, a), t) ∂P.q (h.2, a) + ∫⁻ t, Y ((h, a), t) ∂P.q (h.2, a) := fun h a =>
    lintegral_add_left (f := fun t => X ((h, a), t)) (hX.comp (by fun_prop)) _
  have e2 : ∀ h, ∫⁻ a, (∫⁻ t, X ((h, a), t) ∂P.q (h.2, a) + ∫⁻ t, Y ((h, a), t) ∂P.q (h.2, a))
      ∂π.κ n h = ∫⁻ a, ∫⁻ t, X ((h, a), t) ∂P.q (h.2, a) ∂π.κ n h +
        ∫⁻ a, ∫⁻ t, Y ((h, a), t) ∂P.q (h.2, a) ∂π.κ n h := fun h =>
    lintegral_add_left (f := fun a => ∫⁻ t, X ((h, a), t) ∂P.q (h.2, a))
      (h1.comp (measurable_const.prodMk measurable_id)) _
  simp_rw [e3, e2]
  exact lintegral_add_left h2 _

/-- Finite-horizon continuation loss: `N` more stages from a history at Lean stage `n`. -/
noncomputable def V (P : Problem S A) (π : Plan (S := S) (A := A)) :
    (N : ℕ) → (n : ℕ) → Hist S A n → ℝ≥0∞
  | 0, _, _ => 0
  | N + 1, n, h => ∫⁻ a, ∫⁻ t, ENNReal.ofReal (-P.r (h.2, a, t)) + V P π N (n + 1) (snoc h a t)
      ∂P.q (h.2, a) ∂π.κ n h

lemma measurable_V (P : Problem S A) (π : Plan (S := S) (A := A)) :
    ∀ N n, Measurable (V P π N n)
  | 0, n => measurable_const
  | N + 1, n => by
    haveI := π.κ_markov n
    have hX : Measurable (fun x : (Hist S A n × A) × S =>
        ENNReal.ofReal (-P.r (x.1.1.2, x.1.2, x.2)) + V P π N (n + 1) (snoc x.1.1 x.1.2 x.2)) :=
      ((measurable_loss P).comp (by fun_prop)).add
        ((measurable_V P π N (n + 1)).comp (measurable_snoc n))
    exact (meas_inner P _ hX).lintegral_kernel_prod_right'

lemma V_le_succ (P : Problem S A) (π : Plan (S := S) (A := A)) :
    ∀ N n h, V P π N n h ≤ V P π (N + 1) n h
  | 0, n, h => by simp only [V]; exact bot_le
  | N + 1, n, h => by
    show ∫⁻ a, ∫⁻ t, ENNReal.ofReal (-P.r (h.2, a, t)) + V P π N (n + 1) (snoc h a t)
      ∂P.q (h.2, a) ∂π.κ n h ≤ ∫⁻ a, ∫⁻ t, ENNReal.ofReal (-P.r (h.2, a, t)) +
        V P π (N + 1) (n + 1) (snoc h a t) ∂P.q (h.2, a) ∂π.κ n h
    exact lintegral_mono fun a => lintegral_mono fun t =>
      add_le_add le_rfl (V_le_succ P π N (n + 1) (snoc h a t))

lemma V_mono (P : Problem S A) (π : Plan (S := S) (A := A)) (n : ℕ) (h : Hist S A n) :
    Monotone (fun N => V P π N n h) :=
  monotone_nat_of_le_succ fun N => V_le_succ P π N n h

lemma V_sum (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) :
    ∀ N n, ∫⁻ h, V P π N n h ∂historyLaw P π s n =
      ∑ j ∈ Finset.range N, stageLoss P π s (n + j)
  | 0, n => by simp [V]
  | N + 1, n => by
    have hX : Measurable (fun x : (Hist S A n × A) × S =>
        ENNReal.ofReal (-P.r (x.1.1.2, x.1.2, x.2))) := (measurable_loss P).comp (by fun_prop)
    simp only [V]
    rw [triple_add P π _ (fun x => ENNReal.ofReal (-P.r (x.1.1.2, x.1.2, x.2)))
      (fun x => V P π N (n + 1) (snoc x.1.1 x.1.2 x.2)) hX,
      ← stageLoss_eq, ← lintegral_historyLaw_succ P π s n _ (measurable_V P π N (n + 1)),
      V_sum P π s N (n + 1), Finset.sum_range_succ', add_comm]
    simp only [add_zero]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show n + 1 + j = n + (j + 1) by omega]

/-- The total expected loss of a plan, so that `I P π s = -(L P π s)`. -/
noncomputable def L (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) : ℝ≥0∞ :=
  ∑' n, stageLoss P π s n

lemma I_eq (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) :
    I P π s = -((L P π s : ℝ≥0∞) : EReal) := rfl

lemma L_eq_iSup (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) :
    L P π s = ⨆ N, V P π N 0 (start s) := by
  rw [L, ENNReal.tsum_eq_iSup_nat]
  refine iSup_congr fun N => ?_
  have := V_sum P π s N 0
  rw [historyLaw_zero, lintegral_dirac' _ (measurable_V P π N 0)] at this
  rw [this]
  simp

lemma measurable_L (P : Problem S A) (π : Plan (S := S) (A := A)) : Measurable (L P π) := by
  have : L P π = fun s => ⨆ N, V P π N 0 (start s) := funext (L_eq_iSup P π)
  rw [this]
  exact Measurable.iSup fun N => (measurable_V P π N 0).comp measurable_start

/-- The plan `π` seen after the first pair `(s, a)`. -/
noncomputable def shiftPlan (π : Plan (S := S) (A := A)) (s : S) (a : A) :
    Plan (S := S) (A := A) where
  κ k := (π.κ (k + 1)).comap (fun h => consH s a h) (measurable_consH s a k)
  κ_markov k := by
    haveI := π.κ_markov (k + 1)
    exact Kernel.IsMarkovKernel.comap _ _

lemma V_shift (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) (a : A) :
    ∀ N k (h : Hist S A k), V P π N (k + 1) (consH s a h) = V P (shiftPlan π s a) N k h
  | 0, k, h => rfl
  | N + 1, k, h => by
    simp only [V, snoc_consH, V_shift P π s a N (k + 1)]
    rfl

lemma L_shift (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) (a : A) (t : S) :
    L P (shiftPlan π s a) t = ⨆ N, V P π N 1 (snoc (start s) a t) := by
  rw [L_eq_iSup]
  refine iSup_congr fun N => ?_
  rw [← V_shift P π s a N 0, consH_start]

lemma V_succ (P : Problem S A) (π : Plan (S := S) (A := A)) (N n : ℕ) (h : Hist S A n) :
    V P π (N + 1) n h = ∫⁻ a, ∫⁻ t, ENNReal.ofReal (-P.r (h.2, a, t)) +
      V P π N (n + 1) (snoc h a t) ∂P.q (h.2, a) ∂π.κ n h := rfl


/-! ## P6: Markov assembly from one-step selectors (negative case) -/

lemma lintegral_compProd_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ] (F : α × β → ℝ≥0∞) :
    ∫⁻ x, F x ∂(μ ⊗ₘ κ) ≤ ∫⁻ a, ∫⁻ b, F (a, b) ∂κ a ∂μ := by
  obtain ⟨g, hg, hgF, heq⟩ := exists_measurable_le_lintegral_eq (μ := μ ⊗ₘ κ) F
  rw [heq, Measure.lintegral_compProd hg]
  exact lintegral_mono fun a => lintegral_mono fun b => hgF (a, b)

lemma toPlan_kappa (m : MarkovPlan S A) (k : ℕ) (h : Hist S A k) :
    (MarkovPlan.toPlan m).κ k h = Measure.dirac ((m k).1 h.2) := by
  simp [MarkovPlan.toPlan, Kernel.deterministic_apply]

lemma step (P : Problem S A) (m : MarkovPlan S A) (s : S) (k : ℕ) (W : S → ℝ≥0∞)
    (c : ℝ≥0∞)
    (hstep : ∀ᵐ h ∂historyLaw P (MarkovPlan.toPlan m) s k,
      ∫⁻ t, ENNReal.ofReal (-P.r (h.2, (m k).1 h.2, t)) + W t ∂P.q (h.2, (m k).1 h.2)
        ≤ W h.2 + c) :
    stageLoss P (MarkovPlan.toPlan m) s k + ∫⁻ h, W h.2 ∂historyLaw P (MarkovPlan.toPlan m) s (k+1)
      ≤ ∫⁻ h, W h.2 ∂historyLaw P (MarkovPlan.toPlan m) s k + c := by
  set π := MarkovPlan.toPlan m with hπ
  haveI := isProb_historyLaw P π s k
  haveI := π.κ_markov k
  haveI := P.q_markov
  haveI : IsMarkovKernel (nextKernel P k) := by unfold nextKernel; infer_instance
  have hnk : ∀ ha : Hist S A k × A, nextKernel P k ha = P.q (ha.1.2, ha.2) := fun ha => by
    simp [nextKernel, Kernel.comp_deterministic_eq_comap, Kernel.comap_apply]
  have hl : Measurable (fun x : (Hist S A k × A) × S =>
      ENNReal.ofReal (-P.r (x.1.1.2, x.1.2, x.2))) := (measurable_loss P).comp (by fun_prop)
  calc stageLoss P π s k + ∫⁻ h, W h.2 ∂historyLaw P π s (k+1)
      ≤ ∫⁻ x, ENNReal.ofReal (-P.r (x.1.1.2, x.1.2, x.2)) ∂stageLaw P π s k
        + ∫⁻ x, W x.2 ∂stageLaw P π s k := by
        refine add_le_add le_rfl ?_
        rw [historyLaw_succ]
        exact lintegral_map_le (fun h : Hist S A (k+1) => W h.2) _
    _ = ∫⁻ x, ENNReal.ofReal (-P.r (x.1.1.2, x.1.2, x.2)) + W x.2 ∂stageLaw P π s k :=
        (lintegral_add_left hl _).symm
    _ ≤ ∫⁻ h, ∫⁻ a, ∫⁻ t, ENNReal.ofReal (-P.r (h.2, a, t)) + W t ∂P.q (h.2, a) ∂π.κ k h
          ∂historyLaw P π s k := by
        show ∫⁻ x, _ ∂((historyLaw P π s k ⊗ₘ π.κ k) ⊗ₘ nextKernel P k) ≤ _
        refine (lintegral_compProd_le _ _ _).trans ?_
        refine (lintegral_compProd_le _ _ _).trans ?_
        simp only [hnk]
        exact le_rfl
    _ = ∫⁻ h, ∫⁻ t, ENNReal.ofReal (-P.r (h.2, (m k).1 h.2, t)) + W t
          ∂P.q (h.2, (m k).1 h.2) ∂historyLaw P π s k := by
        refine lintegral_congr fun h => ?_
        rw [hπ, toPlan_kappa, lintegral_dirac]
    _ ≤ ∫⁻ h, W h.2 + c ∂historyLaw P π s k := lintegral_mono_ae hstep
    _ = ∫⁻ h, W h.2 ∂historyLaw P π s k + c := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]

lemma measurable_histInt (P : Problem S A) (π : Plan (S := S) (A := A)) :
    ∀ k (g : Hist S A k → ℝ≥0∞), Measurable g →
      Measurable (fun s => ∫⁻ h, g h ∂historyLaw P π s k)
  | 0, g, hg => by
    simp only [historyLaw_zero]
    simp_rw [lintegral_dirac' _ hg]
    exact hg.comp measurable_start
  | k + 1, g, hg => by
    haveI := π.κ_markov k
    simp_rw [fun s => lintegral_historyLaw_succ P π s k g hg]
    refine measurable_histInt P π k _ ?_
    have h1 := meas_inner P (n := k) (fun x => g (snoc x.1.1 x.1.2 x.2))
      (hg.comp (measurable_snoc k))
    exact h1.lintegral_kernel_prod_right'

lemma lintegral_law (P : Problem S A) (m : MarkovPlan S A) (μ : ℕ → Measure S)
    (hμ : ∀ k, μ (k + 1) = (μ k).bind (fun x => P.q (x, (m k).1 x))) :
    ∀ k (φ : S → ℝ≥0∞), Measurable φ →
      ∫⁻ s, ∫⁻ h, φ h.2 ∂historyLaw P (MarkovPlan.toPlan m) s k ∂μ 0 = ∫⁻ x, φ x ∂μ k
  | 0, φ, hφ => by
    congr 1
    funext s
    have hm : Measurable (fun h : Hist S A 0 => φ h.2) := hφ.comp measurable_snd
    rw [historyLaw_zero, lintegral_dirac' _ hm]
    rfl
  | k + 1, φ, hφ => by
    haveI := P.q_markov
    have hg : Measurable (fun x : S => (x, (m k).1 x)) := measurable_id.prodMk (m k).2
    have hψ : Measurable (fun x : S => ∫⁻ t, φ t ∂P.q (x, (m k).1 x)) := by
      have := hφ.lintegral_kernel (κ := P.q.comap _ hg)
      simpa [Kernel.comap_apply] using this
    have e : ∀ s, ∫⁻ h, φ h.2 ∂historyLaw P (MarkovPlan.toPlan m) s (k + 1)
        = ∫⁻ h, (fun x => ∫⁻ t, φ t ∂P.q (x, (m k).1 x)) h.2
            ∂historyLaw P (MarkovPlan.toPlan m) s k := by
      intro s
      have hm : Measurable (fun h : Hist S A (k + 1) => φ h.2) := hφ.comp measurable_snd
      rw [lintegral_historyLaw_succ P _ s k _ hm]
      refine lintegral_congr fun h => ?_
      simp only [toPlan_kappa]
      rw [lintegral_dirac]
      rfl
    simp_rw [e]
    rw [lintegral_law P m μ hμ k _ hψ, hμ k,
      Measure.lintegral_bind (μ := fun x => P.q (x, (m k).1 x))
        ((P.q.measurable.comp hg).aemeasurable) hφ.aemeasurable]

section Assembly

variable (P : Problem S A)
  (H : ∀ μ : Measure S, IsProbabilityMeasure μ → ∀ ε : ℝ, 0 < ε →
    ∃ f : {g : S → A // Measurable g}, ∀ᵐ s ∂μ, vstar P s - (ε : EReal) ≤ T P f (vstar P) s)

include H

noncomputable def chooseF (ε : ℝ) (hε : 0 < ε) (μ : {μ : Measure S // IsProbabilityMeasure μ})
    (k : ℕ) : {g : S → A // Measurable g} :=
  Classical.choose (H μ.1 μ.2 (epsK ε k) (epsK_pos hε k))

lemma chooseF_spec (ε : ℝ) (hε : 0 < ε) (μ : {μ : Measure S // IsProbabilityMeasure μ})
    (k : ℕ) : ∀ᵐ s ∂μ.1, vstar P s - (epsK ε k : EReal) ≤
      T P (chooseF P H ε hε μ k) (vstar P) s :=
  Classical.choose_spec (H μ.1 μ.2 (epsK ε k) (epsK_pos hε k))

noncomputable def lawSeq (ε : ℝ) (hε : 0 < ε) (p : {μ : Measure S // IsProbabilityMeasure μ}) :
    ℕ → {μ : Measure S // IsProbabilityMeasure μ}
  | 0 => p
  | k + 1 =>
    ⟨(lawSeq ε hε p k).1.bind (fun x => P.q (x, (chooseF P H ε hε (lawSeq ε hε p k) k).1 x)), by
      haveI := P.q_markov
      have hg : Measurable (fun x : S =>
          (x, (chooseF P H ε hε (lawSeq ε hε p k) k).1 x)) :=
        measurable_id.prodMk (chooseF P H ε hε (lawSeq ε hε p k) k).2
      haveI := (lawSeq ε hε p k).2
      constructor
      rw [Measure.bind_apply (f := fun x => P.q (x, (chooseF P H ε hε (lawSeq ε hε p k) k).1 x))
        MeasurableSet.univ (P.q.measurable.comp hg).aemeasurable]
      simp⟩

theorem p6_assembly : ∀ p : Measure S, IsProbabilityMeasure p → ∀ ε : ℝ, 0 < ε →
    ∃ πstar : MarkovPlan S A, NegativeDP.OptEq.IsPEOptimal P p ε (MarkovPlan.toPlan πstar) := by
  intro p hp ε hε
  set μs := lawSeq P H ε hε ⟨p, hp⟩ with hμs
  set m : MarkovPlan S A := fun k => chooseF P H ε hε (μs k) k with hm
  refine ⟨m, hp, ?_⟩
  set W : S → ℝ≥0∞ := fun s => (-(vstar P s)).toENNReal with hW
  have hgood : ∀ k, ∀ᵐ x ∂(μs k).1,
      ∫⁻ t, ENNReal.ofReal (-P.r (x, (m k).1 x, t)) + W t ∂P.q (x, (m k).1 x)
        ≤ W x + ENNReal.ofReal (epsK ε k) := by
    intro k
    filter_upwards [chooseF_spec P H ε hε (μs k) k] with x hx
    rw [vstar_eq P x] at hx
    exact key_le _ (W x) _ (epsK_pos hε k) hx
  have hae : ∀ k, ∀ᵐ s ∂p, ∀ᵐ h ∂historyLaw P (MarkovPlan.toPlan m) s k,
      ∫⁻ t, ENNReal.ofReal (-P.r (h.2, (m k).1 h.2, t)) + W t ∂P.q (h.2, (m k).1 h.2)
        ≤ W h.2 + ENNReal.ofReal (epsK ε k) := by
    intro k
    obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 (hgood k))
    have hind : Measurable (N.indicator (1 : S → ℝ≥0∞)) := measurable_one.indicator hNm
    have hint := lintegral_law P m (fun k => (μs k).1) (fun k => rfl) k _ hind
    have hmeas := measurable_histInt P (MarkovPlan.toPlan m) k
      (fun h => N.indicator (1 : S → ℝ≥0∞) h.2) (hind.comp measurable_snd)
    rw [lintegral_indicator_one hNm, hN0] at hint
    have h0 : ∀ᵐ s ∂p, ∫⁻ h, N.indicator (1 : S → ℝ≥0∞) h.2
        ∂historyLaw P (MarkovPlan.toPlan m) s k = 0 :=
      (lintegral_eq_zero_iff hmeas).1 hint
    filter_upwards [h0] with s hs
    have hpre : MeasurableSet (Prod.snd ⁻¹' N : Set (Hist S A k)) := measurable_snd hNm
    have e : (fun h : Hist S A k => N.indicator (1 : S → ℝ≥0∞) h.2) =
        (Prod.snd ⁻¹' N : Set (Hist S A k)).indicator 1 := by
      funext h; simp only [Set.indicator, Set.mem_preimage]; rfl
    rw [e, lintegral_indicator_one hpre] at hs
    rw [ae_iff]
    refine measure_mono_null (fun h hh => ?_) hs
    exact hNsub hh
  filter_upwards [ae_all_iff.2 hae] with s hs
  haveI : MeasurableSingletonClass (Hist S A 0) :=
    inferInstanceAs (MeasurableSingletonClass ((Fin 0 → S × A) × S))
  have tele : ∀ n, (∑ j ∈ Finset.range n, stageLoss P (MarkovPlan.toPlan m) s j)
      + ∫⁻ h, W h.2 ∂historyLaw P (MarkovPlan.toPlan m) s n
        ≤ W s + ∑ j ∈ Finset.range n, ENNReal.ofReal (epsK ε j) := by
    intro n
    induction n with
    | zero =>
      rw [historyLaw_zero, lintegral_dirac]
      simp [start]
    | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      calc (∑ j ∈ Finset.range n, stageLoss P (MarkovPlan.toPlan m) s j)
            + stageLoss P (MarkovPlan.toPlan m) s n
            + ∫⁻ h, W h.2 ∂historyLaw P (MarkovPlan.toPlan m) s (n + 1)
          = (∑ j ∈ Finset.range n, stageLoss P (MarkovPlan.toPlan m) s j)
            + (stageLoss P (MarkovPlan.toPlan m) s n
            + ∫⁻ h, W h.2 ∂historyLaw P (MarkovPlan.toPlan m) s (n + 1)) := by
            rw [add_assoc]
        _ ≤ (∑ j ∈ Finset.range n, stageLoss P (MarkovPlan.toPlan m) s j)
            + (∫⁻ h, W h.2 ∂historyLaw P (MarkovPlan.toPlan m) s n
              + ENNReal.ofReal (epsK ε n)) := by
            exact add_le_add le_rfl (step P m s n W _ (hs n))
        _ = ((∑ j ∈ Finset.range n, stageLoss P (MarkovPlan.toPlan m) s j)
            + ∫⁻ h, W h.2 ∂historyLaw P (MarkovPlan.toPlan m) s n)
              + ENNReal.ofReal (epsK ε n) := by rw [add_assoc]
        _ ≤ (W s + ∑ j ∈ Finset.range n, ENNReal.ofReal (epsK ε j))
              + ENNReal.ofReal (epsK ε n) := by gcongr
        _ = _ := by rw [add_assoc]
  have htsum : ∑' n, stageLoss P (MarkovPlan.toPlan m) s n ≤ W s + ENNReal.ofReal ε := by
    refine ENNReal.tsum_le_of_sum_range_le fun n => ?_
    calc ∑ j ∈ Finset.range n, stageLoss P (MarkovPlan.toPlan m) s j
        ≤ (∑ j ∈ Finset.range n, stageLoss P (MarkovPlan.toPlan m) s j)
          + ∫⁻ h, W h.2 ∂historyLaw P (MarkovPlan.toPlan m) s n := le_self_add
      _ ≤ W s + ∑ j ∈ Finset.range n, ENNReal.ofReal (epsK ε j) := tele n
      _ ≤ W s + ENNReal.ofReal ε := by gcongr; exact sum_epsK_le hε n
  rw [vstar_eq P s]
  exact key_ge _ _ ε hε htsum

end Assembly

/-! ## P1 + P5: first-step decomposition and one-step selector from a (p, ε)-optimal plan -/

lemma iSup_V_succ (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) :
    (⨆ N, V P π (N + 1) 0 (start s)) = ⨆ N, V P π N 0 (start s) := by
  refine le_antisymm (iSup_le fun N => le_iSup (fun N => V P π N 0 (start s)) (N + 1))
    (iSup_le fun N => (V_mono P π 0 (start s) (Nat.le_succ N)).trans
      (le_iSup (fun N => V P π (N + 1) 0 (start s)) N))

lemma measurable_inner_V (P : Problem S A) (π : Plan (S := S) (A := A)) (N : ℕ) :
    Measurable (fun y : (S × A) × S =>
      ENNReal.ofReal (-P.r (y.1.1, y.1.2, y.2)) + V P π N 1 (snoc (start y.1.1) y.1.2 y.2)) := by
  have hg : Measurable (fun y : (S × A) × S => (((start y.1.1 : Hist S A 0), y.1.2), y.2)) :=
    ((measurable_start.comp (measurable_fst.comp measurable_fst)).prodMk
      (measurable_snd.comp measurable_fst)).prodMk measurable_snd
  exact ((measurable_loss P).comp (by fun_prop)).add ((measurable_V P π N 1).comp
    ((measurable_snoc 0).comp hg))

/-- `G(s, a)`: expected loss of taking `a` at `s` and then following `π` shifted. -/
noncomputable def G (P : Problem S A) (π : Plan (S := S) (A := A)) (x : S × A) : ℝ≥0∞ :=
  ∫⁻ t, ENNReal.ofReal (-P.r (x.1, x.2, t)) + L P (shiftPlan π x.1 x.2) t ∂P.q x

lemma G_eq_iSup (P : Problem S A) (π : Plan (S := S) (A := A)) (x : S × A) :
    G P π x = ⨆ N, ∫⁻ t, ENNReal.ofReal (-P.r (x.1, x.2, t)) +
      V P π N 1 (snoc (start x.1) x.2 t) ∂P.q x := by
  unfold G
  simp_rw [L_shift, ENNReal.add_iSup]
  exact lintegral_iSup
    (f := fun N t => ENNReal.ofReal (-P.r (x.1, x.2, t)) + V P π N 1 (snoc (start x.1) x.2 t))
    (fun N => (measurable_inner_V P π N).comp (measurable_const.prodMk measurable_id))
    (fun N M hNM t => add_le_add le_rfl (V_mono P π 1 _ hNM))

lemma measurable_G (P : Problem S A) (π : Plan (S := S) (A := A)) : Measurable (G P π) := by
  haveI := P.q_markov
  have : G P π = fun x => ⨆ N, ∫⁻ t, ENNReal.ofReal (-P.r (x.1, x.2, t)) +
      V P π N 1 (snoc (start x.1) x.2 t) ∂P.q x := funext (G_eq_iSup P π)
  rw [this]
  exact Measurable.iSup fun N => (measurable_inner_V P π N).lintegral_kernel_prod_right'

lemma L_first (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) :
    L P π s = ∫⁻ a, G P π (s, a) ∂π.κ 0 (start s) := by
  haveI := P.q_markov
  haveI := π.κ_markov 0
  have hin : ∀ N, Measurable (fun a => ∫⁻ t, ENNReal.ofReal (-P.r (s, a, t)) +
      V P π N 1 (snoc (start s) a t) ∂P.q (s, a)) := fun N =>
    ((measurable_inner_V P π N).lintegral_kernel_prod_right' (κ := P.q)).comp
      (measurable_const.prodMk measurable_id)
  simp_rw [G_eq_iSup]
  rw [lintegral_iSup hin (fun N M hNM a =>
      lintegral_mono fun t => add_le_add le_rfl (V_mono P π 1 _ hNM)), L_eq_iSup,
    ← iSup_V_succ]
  exact iSup_congr fun N => (V_succ P π N 0 (start s))

lemma W_le_L (P : Problem S A) (σ : Plan (S := S) (A := A)) (t : S) :
    (-(vstar P t)).toENNReal ≤ L P σ t := by
  have h : I P σ t ≤ vstar P t := le_iSup (fun σ => I P σ t) σ
  rw [vstar_eq P t, I_eq, EReal.neg_le_neg_iff] at h
  exact_mod_cast h

theorem p5_of_p2 (P : Problem S A)
    (H2 : ∀ p : Measure S, IsProbabilityMeasure p → ∀ ε : ℝ, 0 < ε →
      ∃ π : Plan (S := S) (A := A), ∀ᵐ s ∂p, vstar P s - (ε : EReal) ≤ I P π s) :
    ∀ μ : Measure S, IsProbabilityMeasure μ → ∀ ε : ℝ, 0 < ε →
      ∃ f : {g : S → A // Measurable g},
        ∀ᵐ s ∂μ, vstar P s - (ε : EReal) ≤ T P f (vstar P) s := by
  intro μ hμ ε hε
  obtain ⟨π, hπ⟩ := H2 μ hμ (ε / 2) (half_pos hε)
  set W : S → ℝ≥0∞ := fun s => (-(vstar P s)).toENNReal with hW
  haveI := π.κ_markov 0
  set κ0 : Kernel S A := (π.κ 0).comap (fun s => start s) measurable_start with hκ0
  haveI : IsMarkovKernel κ0 := Kernel.IsMarkovKernel.comap _ _
  set B : Set (S × A) := {x | G P π x ≤ L P π x.1 + ENNReal.ofReal (ε / 2)} with hBdef
  have hB : MeasurableSet B :=
    measurableSet_le (measurable_G P π) (((measurable_L P π).comp measurable_fst).add_const _)
  have hpos : ∀ s, κ0 s (Prod.mk s ⁻¹' B) ≠ 0 := by
    intro s hzero
    have hfin : L P π s ≠ ⊤ := by
      intro htop
      have : Prod.mk s ⁻¹' B = Set.univ := by
        ext a; simp [hBdef, htop]
      rw [this, measure_univ] at hzero
      exact one_ne_zero hzero
    have hae : ∀ᵐ a ∂κ0 s, L P π s + ENNReal.ofReal (ε / 2) ≤ G P π (s, a) := by
      rw [ae_iff]
      refine measure_mono_null (fun a ha => ?_) hzero
      simp only [Set.mem_setOf_eq, not_le] at ha
      exact ha.le
    have h1 : L P π s + ENNReal.ofReal (ε / 2) ≤ L P π s := by
      calc L P π s + ENNReal.ofReal (ε / 2) = ∫⁻ a, L P π s + ENNReal.ofReal (ε / 2) ∂κ0 s := by
            rw [lintegral_const, measure_univ, mul_one]
        _ ≤ ∫⁻ a, G P π (s, a) ∂κ0 s := lintegral_mono_ae hae
        _ = L P π s := by rw [L_first P π s, hκ0, Kernel.comap_apply]
    exact absurd h1 (not_le.2 (ENNReal.lt_add_right hfin
      (ENNReal.ofReal_pos.2 (half_pos hε)).ne'))
  obtain ⟨f, hf, hfB⟩ := NegativeDP.OptEq.Sel.exists_measurable_selector_of_kernel μ κ0 B hB
    (Filter.Eventually.of_forall hpos)
  refine ⟨⟨f, hf⟩, ?_⟩
  filter_upwards [hfB, hπ] with s hsB hsπ
  have h1 : L P π s ≤ W s + ENNReal.ofReal (ε / 2) := by
    rw [vstar_eq P s, I_eq] at hsπ
    exact key_le _ _ _ (half_pos hε) hsπ
  have h2 : ∫⁻ t, ENNReal.ofReal (-P.r (s, f s, t)) + W t ∂P.q (s, f s) ≤ G P π (s, f s) :=
    lintegral_mono fun t => add_le_add le_rfl (W_le_L P _ t)
  have h3 : G P π (s, f s) ≤ W s + ENNReal.ofReal ε := by
    calc G P π (s, f s) ≤ L P π s + ENNReal.ofReal (ε / 2) := hsB
      _ ≤ W s + ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by gcongr
      _ = W s + ENNReal.ofReal ε := by
          rw [add_assoc, ← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le, add_halves]
  rw [vstar_eq P s]
  exact key_ge _ _ ε hε (h2.trans h3)

/-- Reduction core: a `(p, ε)`-optimal history-dependent plan for every `p` gives Theorem 8.1. -/
theorem theorem81_of_p2 (P : Problem S A)
    (H2 : ∀ p : Measure S, IsProbabilityMeasure p → ∀ ε : ℝ, 0 < ε →
      ∃ π : Plan (S := S) (A := A), ∀ᵐ s ∂p, vstar P s - (ε : EReal) ≤ I P π s) :
    ∀ p : Measure S, IsProbabilityMeasure p → ∀ ε : ℝ, 0 < ε →
      ∃ πstar : MarkovPlan S A, NegativeDP.OptEq.IsPEOptimal P p ε (MarkovPlan.toPlan πstar) :=
  p6_assembly P (p5_of_p2 P H2)

end NegativeDP.Stationary.F42P6


/-! Child C1a of the f42af937 plan: analytic sets are null-measurable for finite measures
(capacitability; Kechris, Classical Descriptive Set Theory, Thm 29.7 / Bertsekas-Shreve Cor. 7.42.1).
Proof: for `A = range f`, `f : ℕ^ℕ → X` continuous, choose bounds `m` coordinatewise so that
`μ (f '' Σ(m,k))` stays within `ε` of `μ A`; then `⋂ₖ closure (f '' Σ(m,k)) ⊆ f '' ∏ [0, mᵢ]`, compact. -/

set_option autoImplicit false

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace NegativeDP.OptEq.C1a

/-- `Σ(m, k)`: sequences bounded by `m` in the first `k` coordinates. -/
def Sig (m : ℕ → ℕ) (k : ℕ) : Set (ℕ → ℕ) := {z | ∀ i < k, z i ≤ m i}

lemma Sig_antitone (m : ℕ → ℕ) : Antitone (Sig m) :=
  antitone_nat_of_succ_le fun _ _ hz i hi => hz i (by omega)

lemma Sig_update_mono (g : ℕ → ℕ) (k : ℕ) :
    Monotone (fun j => Sig (Function.update g k j) (k + 1)) := by
  intro j j' hjj' z hz i hi
  have h := hz i hi
  simp only [Function.update_apply] at h ⊢
  split_ifs at h ⊢ with hik
  · omega
  · exact h

lemma iUnion_Sig_update (g : ℕ → ℕ) (k : ℕ) :
    ⋃ j, Sig (Function.update g k j) (k + 1) = Sig g k := by
  ext z
  simp only [mem_iUnion]
  constructor
  · rintro ⟨j, hz⟩ i hi
    have h := hz i (by omega)
    simpa [Function.update_apply, show i ≠ k by omega] using h
  · intro hz
    refine ⟨z k, fun i hi => ?_⟩
    simp only [Function.update_apply]
    split_ifs with hik
    · subst hik; exact le_rfl
    · exact hz i (by omega)

lemma Sig_zero (m : ℕ → ℕ) : Sig m 0 = univ := by
  ext z; simp [Sig]

/-- The closure lemma: a point in every `closure (f '' Σ(m,k))` is an image of a point of
`∏ [0, mᵢ]`. -/
lemma mem_image_of_forall_mem_closure {X : Type*} [TopologicalSpace X] [T2Space X]
    {f : (ℕ → ℕ) → X} (hf : Continuous f) (m : ℕ → ℕ) (x : X)
    (hx : ∀ k, x ∈ closure (f '' Sig m k)) : x ∈ f '' {z | ∀ i, z i ≤ m i} := by
  have hd : Directed (· ≥ ·) (Sig m) := (Sig_antitone m).directed_ge
  have hB := Filter.hasBasis_iInf_principal hd
  let G : Filter (ℕ → ℕ) := (⨅ k, 𝓟 (Sig m k)) ⊓ comap f (𝓝 x)
  haveI hG : G.NeBot := by
    refine Filter.inf_neBot_iff.2 fun s hs t ht => ?_
    obtain ⟨k, -, hk⟩ := hB.mem_iff.1 hs
    obtain ⟨U, hU, hUt⟩ := Filter.mem_comap.1 ht
    obtain ⟨y, hyU, z, hz, rfl⟩ := mem_closure_iff_nhds.1 (hx k) U hU
    exact ⟨z, hk hz, hUt hyU⟩
  let u : Ultrafilter (ℕ → ℕ) := Ultrafilter.of G
  have hu : (u : Filter (ℕ → ℕ)) ≤ G := Ultrafilter.of_le G
  have hcoord : ∀ i, ∃ v, Ultrafilter.map (fun z : ℕ → ℕ => z i) u = pure v ∧ v ≤ m i := by
    intro i
    have hmem : Iic (m i) ∈ Ultrafilter.map (fun z : ℕ → ℕ => z i) u := by
      rw [Ultrafilter.mem_map]
      have : Sig m (i + 1) ∈ (u : Filter (ℕ → ℕ)) :=
        hu (mem_inf_of_left (mem_iInf_of_mem (i + 1) (mem_principal_self _)))
      exact Filter.mem_of_superset this fun z hz => hz i (Nat.lt_succ_self i)
    obtain ⟨v, hv, he⟩ := Ultrafilter.eq_pure_of_finite_mem (finite_Iic (m i)) hmem
    exact ⟨v, he, hv⟩
  choose v hv hvm using hcoord
  have hconv : Tendsto id (u : Filter (ℕ → ℕ)) (𝓝 v) := by
    rw [tendsto_pi_nhds]
    intro i
    have e := congrArg (fun w : Ultrafilter ℕ => (w : Filter ℕ)) (hv i)
    simp only [Ultrafilter.coe_map, Ultrafilter.coe_pure] at e
    have : Tendsto (fun z : ℕ → ℕ => z i) u (pure (v i)) := e.le
    exact this.mono_right (pure_le_nhds _)
  refine ⟨v, hvm, ?_⟩
  have h1 : Tendsto f u (𝓝 (f v)) := (hf.tendsto v).comp hconv
  have h2 : Tendsto f u (𝓝 x) := tendsto_iff_comap.2 (hu.trans inf_le_right)
  exact tendsto_nhds_unique h1 h2

section Measure

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] (μ : Measure X)
  (f : (ℕ → ℕ) → X)

/-- One coordinate choice keeps the outer measure within `η`. -/
lemma exists_step [IsFiniteMeasure μ] (g : ℕ → ℕ) (k : ℕ) (η : ℝ≥0∞) (hη : η ≠ 0) :
    ∃ j, μ (f '' Sig g k) ≤ μ (f '' Sig (Function.update g k j) (k + 1)) + η := by
  have hmono : Monotone (fun j => f '' Sig (Function.update g k j) (k + 1)) :=
    fun j j' h => image_mono (Sig_update_mono g k h)
  have hsup : μ (f '' Sig g k) = ⨆ j, μ (f '' Sig (Function.update g k j) (k + 1)) := by
    rw [← iUnion_Sig_update g k, image_iUnion]
    exact hmono.measure_iUnion
  by_contra hcon
  push_neg at hcon
  have hle : μ (f '' Sig g k) + η ≤ μ (f '' Sig g k) := by
    calc μ (f '' Sig g k) + η = ⨆ j, (μ (f '' Sig (Function.update g k j) (k + 1)) + η) := by
          rw [hsup, ENNReal.iSup_add]
      _ ≤ μ (f '' Sig g k) := iSup_le fun j => (hcon j).le
  exact absurd hle (not_le.2 (ENNReal.lt_add_right (measure_ne_top _ _) hη))

/-- The coordinatewise choice of bounds. -/
noncomputable def nextJ (ε : ℝ≥0∞) (g : ℕ → ℕ) (k : ℕ) : ℕ := by
  classical
  exact if h : ∃ j, μ (f '' Sig g k) ≤ μ (f '' Sig (Function.update g k j) (k + 1)) +
      ε * 2⁻¹ ^ (k + 1) then h.choose else 0

noncomputable def Mseq (ε : ℝ≥0∞) : ℕ → (ℕ → ℕ)
  | 0 => fun _ => 0
  | k + 1 => Function.update (Mseq ε k) k (nextJ μ f ε (Mseq ε k) k)

lemma Mseq_stable (ε : ℝ≥0∞) : ∀ k i, i < k → Mseq μ f ε k i = Mseq μ f ε (i + 1) i
  | 0, i, h => absurd h (Nat.not_lt_zero i)
  | k + 1, i, h => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · rw [Mseq, Function.update_of_ne (by omega)]
      exact Mseq_stable ε k i h
    · rfl

lemma Mseq_inv [IsFiniteMeasure μ] (ε : ℝ≥0∞) (hε : ε ≠ 0) : ∀ k,
    μ (range f) ≤ μ (f '' Sig (Mseq μ f ε k) k) +
      ∑ i ∈ Finset.range k, ε * 2⁻¹ ^ (i + 1)
  | 0 => by simp [Sig_zero, image_univ]
  | k + 1 => by
    have hη : ε * 2⁻¹ ^ (k + 1) ≠ 0 := mul_ne_zero hε (pow_ne_zero _ (by simp))
    have hex := exists_step μ f (Mseq μ f ε k) k _ hη
    have hstep : μ (f '' Sig (Mseq μ f ε k) k) ≤
        μ (f '' Sig (Mseq μ f ε (k + 1)) (k + 1)) + ε * 2⁻¹ ^ (k + 1) := by
      classical
      have e : Mseq μ f ε (k + 1) = Function.update (Mseq μ f ε k) k hex.choose := by
        rw [Mseq, nextJ, dif_pos hex]
      rw [e]
      exact hex.choose_spec
    calc μ (range f) ≤ μ (f '' Sig (Mseq μ f ε k) k) +
          ∑ i ∈ Finset.range k, ε * 2⁻¹ ^ (i + 1) := Mseq_inv ε hε k
      _ ≤ μ (f '' Sig (Mseq μ f ε (k + 1)) (k + 1)) + ε * 2⁻¹ ^ (k + 1) +
          ∑ i ∈ Finset.range k, ε * 2⁻¹ ^ (i + 1) := by gcongr
      _ = _ := by rw [Finset.sum_range_succ, add_assoc, add_comm (ε * 2⁻¹ ^ (k + 1))]

lemma sum_le_eps (ε : ℝ≥0∞) (k : ℕ) : ∑ i ∈ Finset.range k, ε * 2⁻¹ ^ (i + 1) ≤ ε := by
  calc ∑ i ∈ Finset.range k, ε * 2⁻¹ ^ (i + 1) ≤ ∑' i, ε * 2⁻¹ ^ (i + 1) :=
        ENNReal.sum_le_tsum _
    _ = ε := by
        rw [ENNReal.tsum_mul_left]
        have : ∑' i : ℕ, (2⁻¹ : ℝ≥0∞) ^ (i + 1) = 1 := by
          simp_rw [pow_succ]
          rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv,
            ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
        rw [this, mul_one]

/-- Capacitability: the range of a continuous `f : ℕ^ℕ → X` is approximated from inside by
compact sets, in outer measure. -/
theorem exists_compact_subset [T2Space X] [OpensMeasurableSpace X] [IsFiniteMeasure μ]
    (hf : Continuous f) (ε : ℝ≥0∞) (hε : ε ≠ 0) :
    ∃ K, IsCompact K ∧ K ⊆ range f ∧ μ (range f) ≤ μ K + ε := by
  set m : ℕ → ℕ := fun i => Mseq μ f ε (i + 1) i with hm
  have hSig : ∀ k, Sig (Mseq μ f ε k) k = Sig m k := by
    intro k; ext z
    simp only [Sig, mem_setOf_eq]
    exact forall₂_congr fun i hi => by rw [Mseq_stable μ f ε k i hi]
  set C : Set (ℕ → ℕ) := {z | ∀ i, z i ≤ m i} with hC
  have hCc : IsCompact C := by
    have : C = Set.pi univ (fun i => Iic (m i)) := by
      ext z; simp only [hC, Set.mem_pi, mem_univ, true_implies, mem_Iic, mem_setOf_eq]
    rw [this]
    exact isCompact_univ_pi fun i => (finite_Iic (m i)).isCompact
  refine ⟨f '' C, hCc.image hf, image_subset_range _ _, ?_⟩
  have hk : ∀ k, μ (range f) ≤ μ (closure (f '' Sig m k)) + ε := fun k =>
    (Mseq_inv μ f ε hε k).trans (by
      rw [hSig]
      exact add_le_add (measure_mono subset_closure) (sum_le_eps ε k))
  have hanti : Antitone (fun k => closure (f '' Sig m k)) :=
    fun a b hab => closure_mono (image_mono (Sig_antitone m hab))
  have hInter : μ (⋂ k, closure (f '' Sig m k)) = ⨅ k, μ (closure (f '' Sig m k)) :=
    hanti.measure_iInter (fun k => isClosed_closure.measurableSet.nullMeasurableSet)
      ⟨0, measure_ne_top _ _⟩
  have hsub : (⋂ k, closure (f '' Sig m k)) ⊆ f '' C := fun x hx =>
    mem_image_of_forall_mem_closure hf m x (mem_iInter.1 hx)
  calc μ (range f) ≤ (⨅ k, μ (closure (f '' Sig m k))) + ε := by
        rw [ENNReal.iInf_add]; exact le_iInf hk
    _ = μ (⋂ k, closure (f '' Sig m k)) + ε := by rw [hInter]
    _ ≤ μ (f '' C) + ε := by gcongr

/-- Analytic sets are null-measurable for finite measures. -/
theorem nullMeasurableSet_of_analytic [T2Space X] [OpensMeasurableSpace X] [IsFiniteMeasure μ]
    {A : Set X} (hA : AnalyticSet A) : NullMeasurableSet A μ := by
  rw [AnalyticSet] at hA
  rcases hA with rfl | ⟨f, hf, rfl⟩
  · exact nullMeasurableSet_empty
  have hK : ∀ n : ℕ, ∃ K, IsCompact K ∧ K ⊆ range f ∧
      μ (range f) ≤ μ K + (n + 1 : ℝ≥0∞)⁻¹ := fun n =>
    exists_compact_subset μ f hf _ (by simp)
  choose K hKc hKs hKμ using hK
  set F := ⋃ n, K n with hF
  have hFm : MeasurableSet F := MeasurableSet.iUnion fun n => (hKc n).isClosed.measurableSet
  have hFs : F ⊆ range f := iUnion_subset hKs
  have hle : μ (range f) ≤ μ F := by
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (ENNReal.coe_ne_zero.2 hε.ne')
    calc μ (range f) ≤ μ (K n) + (n + 1 : ℝ≥0∞)⁻¹ := hKμ n
      _ ≤ μ F + ε := by
          gcongr
          · exact subset_iUnion K n
          · refine le_trans ?_ hn.le
            gcongr
            exact le_self_add
  have hnull : μ (range f \ F) = 0 := by
    refine measure_mono_null (sdiff_subset_sdiff_left (subset_toMeasurable μ (range f))) ?_
    rw [measure_sdiff (hFs.trans (subset_toMeasurable μ _)) hFm.nullMeasurableSet
      (measure_ne_top _ _), measure_toMeasurable]
    exact tsub_eq_zero_of_le hle
  refine hFm.nullMeasurableSet.congr ?_
  refine ae_eq_set.2 ⟨by simp [sdiff_eq_empty.2 hFs], hnull⟩

end Measure

end NegativeDP.OptEq.C1a

/-! ## C1b: a.e. measurable selection for Borel sets (Jankov-von Neumann, a.e. form).
For `B = range φ`, `φ : ℕ^ℕ → X × Y` continuous, capacitability gives compacts `C n ⊆ ℕ^ℕ`
whose `fst ∘ φ`-images exhaust `proj B` up to a null set; on each compact the greedy
(lexicographically least) point of the fibre is a Borel selector. -/

namespace NegativeDP.OptEq.C1b

open NegativeDP.OptEq.C1a
open Classical

section Domain

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] (μ : Measure X)
  (f : (ℕ → ℕ) → X)

theorem exists_compact_domain [T2Space X] [OpensMeasurableSpace X] [IsFiniteMeasure μ]
    (hf : Continuous f) (ε : ℝ≥0∞) (hε : ε ≠ 0) :
    ∃ C : Set (ℕ → ℕ), IsCompact C ∧ μ (range f) ≤ μ (f '' C) + ε := by
  set m : ℕ → ℕ := fun i => Mseq μ f ε (i + 1) i with hm
  have hSig : ∀ k, Sig (Mseq μ f ε k) k = Sig m k := by
    intro k; ext z
    simp only [Sig, mem_setOf_eq]
    exact forall₂_congr fun i hi => by rw [Mseq_stable μ f ε k i hi]
  set C : Set (ℕ → ℕ) := {z | ∀ i, z i ≤ m i} with hC
  have hCc : IsCompact C := by
    have : C = Set.pi univ (fun i => Iic (m i)) := by
      ext z; simp only [hC, Set.mem_pi, mem_univ, true_implies, mem_Iic, mem_setOf_eq]
    rw [this]
    exact isCompact_univ_pi fun i => (finite_Iic (m i)).isCompact
  refine ⟨C, hCc, ?_⟩
  have hk : ∀ k, μ (range f) ≤ μ (closure (f '' Sig m k)) + ε := fun k =>
    (Mseq_inv μ f ε hε k).trans (by
      rw [hSig]
      exact add_le_add (measure_mono subset_closure) (sum_le_eps ε k))
  have hanti : Antitone (fun k => closure (f '' Sig m k)) :=
    fun a b hab => closure_mono (image_mono (Sig_antitone m hab))
  have hInter : μ (⋂ k, closure (f '' Sig m k)) = ⨅ k, μ (closure (f '' Sig m k)) :=
    hanti.measure_iInter (fun k => isClosed_closure.measurableSet.nullMeasurableSet)
      ⟨0, measure_ne_top _ _⟩
  have hsub : (⋂ k, closure (f '' Sig m k)) ⊆ f '' C := fun x hx =>
    mem_image_of_forall_mem_closure hf m x (mem_iInter.1 hx)
  calc μ (range f) ≤ (⨅ k, μ (closure (f '' Sig m k))) + ε := by
        rw [ENNReal.iInf_add]; exact le_iInf hk
    _ = μ (⋂ k, closure (f '' Sig m k)) + ε := by rw [hInter]
    _ ≤ μ (f '' C) + ε := by gcongr

end Domain

section Select

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  (g : (ℕ → ℕ) → X) (C : Set (ℕ → ℕ))

/-- Points of `C` with prescribed prefix `l`. -/
def Cyl (l : List ℕ) : Set (ℕ → ℕ) := {w | w ∈ C ∧ ∀ i < l.length, w i = l.getD i 0}

/-- Image of a cylinder. -/
def E (l : List ℕ) : Set X := g '' Cyl C l

/-- Greedy predicate: `n` extends `l`, or no extension exists. -/
def Pr (l : List ℕ) (x : X) (n : ℕ) : Prop :=
  x ∈ E g C (l ++ [n]) ∨ ∀ m, x ∉ E g C (l ++ [m])

lemma Pr_exists (l : List ℕ) (x : X) : ∃ n, Pr g C l x n := by
  by_cases h : ∃ n, x ∈ E g C (l ++ [n])
  · obtain ⟨n, hn⟩ := h; exact ⟨n, Or.inl hn⟩
  · push_neg at h; exact ⟨0, Or.inr h⟩

noncomputable def step (l : List ℕ) (x : X) : List ℕ := l ++ [Nat.find (Pr_exists g C l x)]

noncomputable def pre (x : X) : ℕ → List ℕ
  | 0 => []
  | k + 1 => step g C (pre x k) x

/-- The greedy selector. -/
noncomputable def sel (x : X) : ℕ → ℕ := fun i => (pre g C x (i + 1)).getD i 0

lemma pre_succ (x : X) (k : ℕ) :
    pre g C x (k + 1) = pre g C x k ++ [Nat.find (Pr_exists g C (pre g C x k) x)] := rfl

lemma length_pre (x : X) (k : ℕ) : (pre g C x k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pre_succ]; simp [ih]

lemma prefix_pre (x : X) {k k' : ℕ} (h : k ≤ k') : pre g C x k <+: pre g C x k' := by
  induction k', h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ k' _ ih => rw [pre_succ]; exact ih.trans (List.prefix_append _ _)

lemma getD_pre (x : X) {i k : ℕ} (h : i < k) : (pre g C x k).getD i 0 = sel g C x i := by
  obtain ⟨t, ht⟩ := prefix_pre g C x (Nat.succ_le_of_lt h)
  rw [sel, ← ht, List.getD_append _ _ _ _ (by rw [length_pre]; omega)]

lemma Cyl_nil : Cyl C [] = C := by ext w; simp [Cyl]

lemma mem_E_pre {x : X} (hx : x ∈ g '' C) : ∀ k, x ∈ E g C (pre g C x k) := by
  intro k
  induction k with
  | zero => simpa [E, pre, Cyl_nil] using hx
  | succ k ih =>
    rw [pre_succ]
    have hex : ∃ n, x ∈ E g C (pre g C x k ++ [n]) := by
      obtain ⟨w, ⟨hwC, hwl⟩, hwx⟩ := ih
      refine ⟨w (pre g C x k).length, w, ⟨hwC, fun i hi => ?_⟩, hwx⟩
      simp only [List.length_append, List.length_singleton] at hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
      · rw [List.getD_append _ _ _ _ hi]; exact hwl i hi
      · subst hi; rw [List.getD_append_right _ _ _ _ le_rfl]; simp
    rcases Nat.find_spec (Pr_exists g C (pre g C x k) x) with hs | hs
    · exact hs
    · obtain ⟨n, hn⟩ := hex; exact absurd hn (hs n)

lemma sel_mem [T2Space X] (hg : Continuous g) (hC : IsCompact C) {x : X} (hx : x ∈ g '' C) :
    sel g C x ∈ C ∧ g (sel g C x) = x := by
  have h : ∀ k, ∃ w, w ∈ Cyl C (pre g C x k) ∧ g w = x := fun k => mem_E_pre g C hx k
  choose w hw hwx using h
  have hT : Tendsto w atTop (𝓝 (sel g C x)) := by
    refine tendsto_pi_nhds.2 fun i => ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop i] with k hk
    rw [(hw k).2 i (by rw [length_pre]; exact hk), getD_pre g C x hk]
  refine ⟨hC.isClosed.mem_of_tendsto hT (Eventually.of_forall fun k => (hw k).1), ?_⟩
  have h2 : Tendsto (fun k => g (w k)) atTop (𝓝 (g (sel g C x))) :=
    (hg.tendsto _).comp hT
  simp only [hwx] at h2
  exact tendsto_nhds_unique h2 tendsto_const_nhds

lemma isCompact_Cyl (hC : IsCompact C) (l : List ℕ) : IsCompact (Cyl C l) := by
  have : Cyl C l = C ∩ ⋂ i ∈ Finset.range l.length, {w : ℕ → ℕ | w i = l.getD i 0} := by
    ext w; simp [Cyl]
  rw [this]
  exact hC.inter_right (isClosed_biInter fun i _ =>
    isClosed_eq (continuous_apply i) continuous_const)

lemma measurableSet_E [T2Space X] [OpensMeasurableSpace X] (hg : Continuous g)
    (hC : IsCompact C) (l : List ℕ) : MeasurableSet (E g C l) :=
  ((isCompact_Cyl C hC l).image hg).isClosed.measurableSet

lemma measurableSet_pre_eq [T2Space X] [OpensMeasurableSpace X] (hg : Continuous g)
    (hC : IsCompact C) : ∀ k (l : List ℕ), MeasurableSet {x | pre g C x k = l} := by
  intro k
  induction k with
  | zero =>
    intro l
    show MeasurableSet {_x : X | ([] : List ℕ) = l}
    exact MeasurableSet.const _
  | succ k ih =>
    intro l
    have hfind : ∀ l' : List ℕ, Measurable fun x => Nat.find (Pr_exists g C l' x) := by
      intro l'
      refine measurable_find (p := fun x n => Pr g C l' x n) (Pr_exists g C l') fun n => ?_
      have : {x | Pr g C l' x n} = E g C (l' ++ [n]) ∪ (⋃ m, E g C (l' ++ [m]))ᶜ := by
        ext x; simp [Pr]
      rw [this]
      exact (measurableSet_E g C hg hC _).union
        (MeasurableSet.iUnion fun m => measurableSet_E g C hg hC _).compl
    have : {x | pre g C x (k + 1) = l} = ⋃ l' : List ℕ, {x | pre g C x k = l'} ∩
        (fun x => Nat.find (Pr_exists g C l' x)) ⁻¹' {n | l' ++ [n] = l} := by
      ext x; simp [pre_succ]
    rw [this]
    exact MeasurableSet.iUnion fun l' => (ih l').inter (hfind l' (MeasurableSet.of_discrete))

lemma measurable_sel [T2Space X] [OpensMeasurableSpace X] (hg : Continuous g)
    (hC : IsCompact C) : Measurable (sel g C) := by
  refine measurable_pi_lambda _ fun i => measurable_to_countable' fun n => ?_
  have : (fun x => sel g C x i) ⁻¹' {n} =
      ⋃ l : List ℕ, {x | pre g C x (i + 1) = l} ∩ {_x | l.getD i 0 = n} := by
    ext x; simp [sel]
  rw [this]
  exact MeasurableSet.iUnion fun l =>
    (measurableSet_pre_eq g C hg hC (i + 1) l).inter (MeasurableSet.const _)

end Select

/-- C1: a.e. measurable selection for Borel subsets of a product of standard Borel spaces. -/
theorem C1_selection {X : Type*} {Y : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure X) [IsFiniteMeasure μ] (B : Set (X × Y)) (hB : MeasurableSet B) :
    ∃ f : X → Y, Measurable f ∧ ∀ᵐ x ∂μ, (∃ y, (x, y) ∈ B) → (x, f x) ∈ B := by
  letI := upgradeStandardBorel X
  letI := upgradeStandardBorel Y
  have hBa : AnalyticSet B := hB.analyticSet
  rw [AnalyticSet] at hBa
  rcases hBa with rfl | ⟨φ, hφ, rfl⟩
  · exact ⟨fun _ => Classical.arbitrary Y, measurable_const,
      Eventually.of_forall fun x ⟨y, hy⟩ => hy.elim⟩
  set ψ : (ℕ → ℕ) → X := fun z => (φ z).1 with hψ
  have hψc : Continuous ψ := continuous_fst.comp hφ
  have hC : ∀ n : ℕ, ∃ C : Set (ℕ → ℕ), IsCompact C ∧
      μ (range ψ) ≤ μ (ψ '' C) + (n + 1 : ℝ≥0∞)⁻¹ :=
    fun n => exists_compact_domain μ ψ hψc _ (by simp)
  choose C hCc hCμ using hC
  set G : ℕ → Set X := fun n => ψ '' C n with hG
  have hGm : ∀ n, MeasurableSet (G n) := fun n => ((hCc n).image hψc).isClosed.measurableSet
  let p : ℕ → X → Prop := fun n x => x ∈ G n ∨ x ∉ ⋃ m, G m
  have hp : ∀ x, ∃ n, p n x := fun x => by
    by_cases hx : x ∈ ⋃ m, G m
    · obtain ⟨m, hm⟩ := mem_iUnion.1 hx; exact ⟨m, Or.inl hm⟩
    · exact ⟨0, Or.inr hx⟩
  have hpm : ∀ n, MeasurableSet {x | p n x} := fun n =>
    (hGm n).union (MeasurableSet.iUnion hGm).compl
  let F : ℕ → X → Y := fun n x => (φ (sel ψ (C n) x)).2
  have hF : ∀ n, Measurable (F n) := fun n =>
    (continuous_snd.comp hφ).measurable.comp (measurable_sel ψ (C n) hψc (hCc n))
  refine ⟨fun x => F (Nat.find (hp x)) x, Measurable.find hF hpm hp, ?_⟩
  set U := ⋃ m, G m with hU
  have hUm : MeasurableSet U := MeasurableSet.iUnion hGm
  have hUs : U ⊆ range ψ := iUnion_subset fun n => image_subset_range _ _
  have hle : μ (range ψ) ≤ μ U := by
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (ENNReal.coe_ne_zero.2 hε.ne')
    calc μ (range ψ) ≤ μ (G n) + (n + 1 : ℝ≥0∞)⁻¹ := hCμ n
      _ ≤ μ U + ε := by
          gcongr
          · exact subset_iUnion G n
          · refine le_trans ?_ hn.le
            gcongr
            exact le_self_add
  have hnull : μ (range ψ \ U) = 0 := by
    refine measure_mono_null (sdiff_subset_sdiff_left (subset_toMeasurable μ (range ψ))) ?_
    rw [measure_sdiff (hUs.trans (subset_toMeasurable μ _)) hUm.nullMeasurableSet
      (measure_ne_top _ _), measure_toMeasurable]
    exact tsub_eq_zero_of_le hle
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) hnull
  simp only [mem_setOf_eq, _root_.not_imp] at hx
  obtain ⟨⟨y, z, hz⟩, hxB⟩ := hx
  have hxr : x ∈ range ψ := ⟨z, by simp [hψ, hz]⟩
  refine ⟨hxr, fun hxU => hxB ?_⟩
  have hs := Nat.find_spec (hp x)
  have hxG : x ∈ G (Nat.find (hp x)) := by
    rcases hs with hs | hs
    · exact hs
    · exact absurd hxU hs
  obtain ⟨-, hsel⟩ := sel_mem ψ (C (Nat.find (hp x))) hψc (hCc _) hxG
  refine ⟨sel ψ (C (Nat.find (hp x))) x, ?_⟩
  exact Prod.ext hsel rfl

end NegativeDP.OptEq.C1b


/-! ## P2a: a standard Borel parametrisation of the strategic laws (codes of stage laws). -/

namespace NegativeDP.OptEq.P2a

open Set NegativeDP.Stationary NegativeDP.Stationary.F42P6

/-! ### Universal codes for probability measures on a standard Borel space -/

/-- Codes: rational-point values of a distribution function. -/
abbrev Code := ℚ → ℝ

/-- The decoding kernel on `ℝ`. -/
noncomputable def codeR : Kernel Code ℝ where
  toFun y := (stieltjesOfMeasurableRat (fun y : Code => y) measurable_id y).measure
  measurable' := measurable_measure_stieltjesOfMeasurableRat measurable_id

theorem isMarkovKernel_codeR : IsMarkovKernel codeR :=
  ⟨fun y => by
    show IsProbabilityMeasure (stieltjesOfMeasurableRat (fun y : Code => y) measurable_id y).measure
    infer_instance⟩

attribute [local instance] isMarkovKernel_codeR

theorem codeR_surj (ν : Measure ℝ) [IsProbabilityMeasure ν] : ∃ y, codeR y = ν := by
  have hpt : IsRatStieltjesPoint (fun y : Code => y) (fun q : ℚ => cdf ν q) :=
    { mono := fun a b h => monotone_cdf ν (Rat.cast_le.2 h)
      tendsto_atTop_one := (tendsto_cdf_atTop ν).comp (tendsto_ratCast_atTop_iff.2 tendsto_id)
      tendsto_atBot_zero := (tendsto_cdf_atBot ν).comp (tendsto_ratCast_atBot_iff.2 tendsto_id)
      iInf_rat_gt_eq := fun t => by
        beta_reduce
        rw [← (cdf ν).iInf_rat_gt_eq (t : ℝ)]
        exact (Equiv.subtypeEquivRight (fun r : ℚ => by
          simp only [Set.mem_Ioi, Rat.cast_lt])).iInf_congr (fun r => rfl) }
  refine ⟨fun q : ℚ => cdf ν q, ?_⟩
  have hF : stieltjesOfMeasurableRat (fun y : Code => y) measurable_id (fun q : ℚ => cdf ν q)
      = cdf ν := by
    ext x
    rw [← StieltjesFunction.iInf_rat_gt_eq, ← StieltjesFunction.iInf_rat_gt_eq (cdf ν) x]
    refine iInf_congr fun r => ?_
    rw [stieltjesOfMeasurableRat_eq, toRatCDF_of_isRatStieltjesPoint hpt]
  show (stieltjesOfMeasurableRat (fun y : Code => y) measurable_id _).measure = ν
  rw [hF, measure_cdf]

theorem exists_code (Z : Type*) [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z] :
    ∃ Λ : Kernel Code Z, IsMarkovKernel Λ ∧
      ∀ ν : Measure Z, IsProbabilityMeasure ν → ∃ y, Λ y = ν := by
  obtain ⟨e, he⟩ := exists_measurableEmbedding_real Z
  obtain ⟨ρ, hρ, hρe⟩ := he.exists_measurable_extend (g := id) measurable_id
    (fun _ => inferInstance)
  refine ⟨codeR.map ρ, Kernel.IsMarkovKernel.map _ hρ, fun ν hν => ?_⟩
  haveI : IsProbabilityMeasure (ν.map e) := Measure.isProbabilityMeasure_map he.measurable.aemeasurable
  obtain ⟨y, hy⟩ := codeR_surj (ν.map e)
  refine ⟨y, ?_⟩
  rw [Kernel.map_apply _ hρ, hy, Measure.map_map hρ he.measurable, hρe, Measure.map_id]

/-- Equality of two Markov kernels into a standard Borel space is a measurable condition. -/
theorem measurableSet_kernel_eq {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    [StandardBorelSpace W] (κ η : Kernel Z W) [IsMarkovKernel κ] [IsMarkovKernel η] :
    MeasurableSet {z | κ z = η z} := by
  obtain ⟨e, he⟩ := exists_measurableEmbedding_real W
  have hset : {z | κ z = η z} =
      ⋂ q : ℚ, {z | κ z (e ⁻¹' Iic (q : ℝ)) = η z (e ⁻¹' Iic (q : ℝ))} := by
    ext z
    simp only [mem_setOf_eq, mem_iInter]
    refine ⟨fun h q => by rw [h], fun h => ?_⟩
    have hmap : (κ z).map e = (η z).map e := by
      refine ext_of_generate_finite _ (BorelSpace.measurable_eq.trans
        Real.borel_eq_generateFrom_Iic_rat) Real.isPiSystem_Iic_rat (fun s hs => ?_) ?_
      · simp only [mem_iUnion, mem_singleton_iff] at hs
        obtain ⟨q, rfl⟩ := hs
        rw [Measure.map_apply he.measurable measurableSet_Iic,
          Measure.map_apply he.measurable measurableSet_Iic]
        exact h q
      · rw [Measure.map_apply he.measurable MeasurableSet.univ,
          Measure.map_apply he.measurable MeasurableSet.univ]
        simp
    rw [← he.comap_map (κ z), hmap, he.comap_map]
  rw [hset]
  exact MeasurableSet.iInter fun q => measurableSet_eq_fun
    (Kernel.measurable_coe _ (he.measurable measurableSet_Iic))
    (Kernel.measurable_coe _ (he.measurable measurableSet_Iic))

/-! ### The model -/

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

theorem stdBorel_hist (n : ℕ) : StandardBorelSpace (Hist S A n) :=
  inferInstanceAs (StandardBorelSpace ((Fin n → S × A) × S))

theorem nonempty_hist (n : ℕ) : Nonempty (Hist S A n) :=
  inferInstanceAs (Nonempty ((Fin n → S × A) × S))

attribute [local instance] stdBorel_hist nonempty_hist

/-- Decoding kernel for stage laws. -/
noncomputable def Λ (S A : Type*) [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A] (n : ℕ) :
    Kernel Code ((Hist S A n × A) × S) :=
  Classical.choose (exists_code ((Hist S A n × A) × S))

theorem isMarkovKernel_Λ (n : ℕ) : IsMarkovKernel (Λ S A n) :=
  (Classical.choose_spec (exists_code ((Hist S A n × A) × S))).1

attribute [local instance] isMarkovKernel_Λ

theorem Λ_surj (n : ℕ) (ν : Measure ((Hist S A n × A) × S)) [IsProbabilityMeasure ν] :
    ∃ y, Λ S A n y = ν :=
  (Classical.choose_spec (exists_code ((Hist S A n × A) × S))).2 ν inferInstance

theorem isMarkovKernel_next (P : Problem S A) (n : ℕ) : IsMarkovKernel (nextKernel P n) := by
  haveI := P.q_markov; unfold nextKernel; infer_instance

attribute [local instance] isMarkovKernel_next

variable (P : Problem S A)

/-- The codes `y` that encode the stage laws of some plan started at `s`. -/
def Γ : Set (S × (ℕ → Code)) :=
  {sy | (Λ S A 0 (sy.2 0)).map (fun x => x.1.1) = Measure.dirac (start sy.1) ∧
    ∀ n, Λ S A n (sy.2 n) = ((Λ S A n (sy.2 n)).map Prod.fst) ⊗ₘ nextKernel P n ∧
      (Λ S A (n + 1) (sy.2 (n + 1))).map (fun x => x.1.1) =
        (Λ S A n (sy.2 n)).map (fun x => snoc x.1.1 x.1.2 x.2)}

lemma meas11 (n : ℕ) : Measurable (fun x : (Hist S A n × A) × S => x.1.1) :=
  measurable_fst.comp measurable_fst

lemma measurable_ev (n : ℕ) : Measurable (fun sy : S × (ℕ → Code) => sy.2 n) :=
  (measurable_pi_apply n).comp measurable_snd

theorem measurableSet_Γ : MeasurableSet (Γ P) := by
  have h0 : MeasurableSet {sy : S × (ℕ → Code) |
      (Λ S A 0 (sy.2 0)).map (fun x => x.1.1) = Measure.dirac (start sy.1)} := by
    haveI : IsMarkovKernel (((Λ S A 0).comap _ (measurable_ev (S := S) 0)).map
        (fun x => x.1.1)) := Kernel.IsMarkovKernel.map _ (meas11 _)
    have := measurableSet_kernel_eq
      (((Λ S A 0).comap _ (measurable_ev (S := S) 0)).map (fun x => x.1.1))
      (Kernel.deterministic (fun sy : S × (ℕ → Code) => (start sy.1 : Hist S A 0))
        (measurable_start.comp measurable_fst))
    convert this using 1
    ext sy
    simp only [mem_setOf_eq]
    rw [Kernel.map_apply _ (meas11 _), Kernel.comap_apply,
      Kernel.deterministic_apply]
  have h1 : ∀ n, MeasurableSet {sy : S × (ℕ → Code) |
      Λ S A n (sy.2 n) = ((Λ S A n (sy.2 n)).map Prod.fst) ⊗ₘ nextKernel P n} := by
    intro n
    haveI : IsMarkovKernel (((Λ S A n).comap _ (measurable_ev (S := S) n)).map Prod.fst) :=
      Kernel.IsMarkovKernel.map _ measurable_fst
    have := measurableSet_kernel_eq ((Λ S A n).comap _ (measurable_ev (S := S) n))
      ((((Λ S A n).comap _ (measurable_ev (S := S) n)).map Prod.fst) ⊗ₖ
        (nextKernel P n).prodMkLeft (S × (ℕ → Code)))
    convert this using 1
    ext sy
    simp only [mem_setOf_eq]
    rw [Kernel.compProd_apply_eq_compProd_sectR, Kernel.comap_apply,
      Kernel.map_apply _ measurable_fst, Kernel.comap_apply]
    rfl
  have h2 : ∀ n, MeasurableSet {sy : S × (ℕ → Code) |
      (Λ S A (n + 1) (sy.2 (n + 1))).map (fun x => x.1.1) =
        (Λ S A n (sy.2 n)).map (fun x => snoc x.1.1 x.1.2 x.2)} := by
    intro n
    haveI : IsMarkovKernel (((Λ S A (n + 1)).comap _ (measurable_ev (S := S) (n + 1))).map
        (fun x => x.1.1)) := Kernel.IsMarkovKernel.map _ (meas11 _)
    haveI : IsMarkovKernel (((Λ S A n).comap _ (measurable_ev (S := S) n)).map
        (fun x => snoc x.1.1 x.1.2 x.2)) := Kernel.IsMarkovKernel.map _ (measurable_snoc n)
    have := measurableSet_kernel_eq
      (((Λ S A (n + 1)).comap _ (measurable_ev (S := S) (n + 1))).map (fun x => x.1.1))
      (((Λ S A n).comap _ (measurable_ev (S := S) n)).map (fun x => snoc x.1.1 x.1.2 x.2))
    convert this using 1
    ext sy
    simp only [mem_setOf_eq]
    rw [Kernel.map_apply _ (meas11 _), Kernel.comap_apply,
      Kernel.map_apply _ (measurable_snoc n), Kernel.comap_apply]
  have : Γ P = {sy : S × (ℕ → Code) |
      (Λ S A 0 (sy.2 0)).map (fun x => x.1.1) = Measure.dirac (start sy.1)} ∩
      ⋂ n, ({sy : S × (ℕ → Code) |
        Λ S A n (sy.2 n) = ((Λ S A n (sy.2 n)).map Prod.fst) ⊗ₘ nextKernel P n} ∩
        {sy : S × (ℕ → Code) | (Λ S A (n + 1) (sy.2 (n + 1))).map (fun x => x.1.1) =
          (Λ S A n (sy.2 n)).map (fun x => snoc x.1.1 x.1.2 x.2)}) := by
    ext sy
    simp only [Γ, mem_setOf_eq, mem_inter_iff, mem_iInter, forall_and]
  rw [this]
  exact h0.inter (MeasurableSet.iInter fun n => (h1 n).inter (h2 n))

/-- Total expected loss encoded by `y`. -/
noncomputable def R (y : ℕ → Code) : ℝ≥0∞ :=
  ∑' n, ∫⁻ x, ENNReal.ofReal (-P.r (x.1.1.2, x.1.2, x.2)) ∂(Λ S A n (y n))

open Classical in
/-- The parametrised return. -/
noncomputable def PhiC (sy : S × (ℕ → Code)) : EReal :=
  if sy ∈ Γ P then -((R P sy.2 : ℝ≥0∞) : EReal) else ⊥

theorem measurable_PhiC : Measurable (PhiC P) := by
  refine Measurable.ite (measurableSet_Γ P) ?_ measurable_const
  refine continuous_neg.measurable.comp (measurable_coe_ennreal_ereal.comp ?_)
  refine Measurable.ennreal_tsum fun n => ?_
  have hl : Measurable (fun x : (Hist S A n × A) × S => ENNReal.ofReal (-P.r (x.1.1.2, x.1.2, x.2))) :=
    (measurable_loss P).comp
      (by fun_prop : Measurable (fun x : (Hist S A n × A) × S => (x.1.1.2, x.1.2, x.2)))
  exact (hl.lintegral_kernel (κ := Λ S A n)).comp ((measurable_pi_apply n).comp measurable_snd)

/-! ### Gluing -/

/-- Conditional action kernels decoded from the codes. -/
noncomputable def cK (n : ℕ) : Kernel (Code × Hist S A n) A :=
  Kernel.condKernel ((Λ S A n).map Prod.fst)

/-- The plan that reads the initial state `s` and follows the code `g s`. -/
noncomputable def gluePlan (g : S → (ℕ → Code)) (hg : Measurable g) : Plan (S := S) (A := A) where
  κ n := (cK n).comap (fun h => (g (Hist.init h) n, h))
    (((measurable_pi_apply n).comp (hg.comp (Hist.measurable_init n))).prodMk measurable_id)
  κ_markov n := by unfold cK; infer_instance

lemma init_snoc {n : ℕ} (h : Hist S A n) (a : A) (t : S) :
    Hist.init (snoc h a t) = Hist.init h := by
  rw [snoc_eq]
  cases n with
  | zero =>
    show (Fin.snoc (α := fun _ => S × A) h.1 (h.2, a) (Fin.last 0)).1 = h.2
    rw [Fin.snoc_last]
  | succ n =>
    show (Fin.snoc (α := fun _ => S × A) h.1 (h.2, a) (Fin.castSucc 0)).1 = (h.1 0).1
    rw [Fin.snoc_castSucc]

theorem init_ae (π : Plan (S := S) (A := A)) (s : S) :
    ∀ n, ∀ᵐ h ∂(historyLaw P π s n), Hist.init h = s := by
  intro n
  have hm : ∀ k, MeasurableSet {h : Hist S A k | Hist.init h = s} := fun k =>
    Hist.measurable_init k (measurableSet_singleton s)
  induction n with
  | zero =>
    rw [historyLaw_zero]
    exact (ae_dirac_iff (hm 0)).2 rfl
  | succ n ih =>
    rw [historyLaw_succ, ae_map_iff (measurable_snoc n).aemeasurable (hm _)]
    haveI := π.κ_markov n
    have hm' : MeasurableSet {x : (Hist S A n × A) × S | Hist.init x.1.1 = s} :=
      (measurable_fst.comp measurable_fst) (hm n)
    have h1 : ∀ᵐ x ∂(historyLaw P π s n ⊗ₘ π.κ n), Hist.init x.1 = s :=
      Measure.ae_compProd_of_ae_ae (measurable_fst (hm n))
        (by filter_upwards [ih] with h hh; exact Eventually.of_forall fun _ => hh)
    have h2 : ∀ᵐ x ∂stageLaw P π s n, Hist.init x.1.1 = s :=
      Measure.ae_compProd_of_ae_ae hm'
        (by filter_upwards [h1] with h hh; exact Eventually.of_forall fun _ => hh)
    filter_upwards [h2] with x hx
    rw [init_snoc]; exact hx

theorem laws_glue (g : S → (ℕ → Code)) (hg : Measurable g) (s : S) (hΓ : (s, g s) ∈ Γ P) :
    ∀ n, historyLaw P (gluePlan (A := A) g hg) s n = (Λ S A n (g s n)).map (fun x => x.1.1) ∧
      stageLaw P (gluePlan (A := A) g hg) s n = Λ S A n (g s n) := by
  have hstage : ∀ n, historyLaw P (gluePlan (A := A) g hg) s n = (Λ S A n (g s n)).map (fun x => x.1.1) →
      stageLaw P (gluePlan (A := A) g hg) s n = Λ S A n (g s n) := by
    intro n hn
    set K := (Λ S A n).map Prod.fst with hK
    set ρ := (Λ S A n (g s n)).map Prod.fst with hρ
    have hKc : K (g s n) = ρ := Kernel.map_apply _ measurable_fst _
    have hdis : ρ = ρ.map Prod.fst ⊗ₘ Kernel.sectR (Kernel.condKernel K) (g s n) := by
      have := congrArg (fun κ => κ (g s n)) (Kernel.disintegrate (κ := K) (κCond := Kernel.condKernel K))
      rw [Kernel.compProd_apply_eq_compProd_sectR, Kernel.fst_apply, hKc] at this
      exact this.symm
    have hhist : historyLaw P (gluePlan (A := A) g hg) s n = ρ.map Prod.fst := by
      rw [hn, hρ, Measure.map_map measurable_fst measurable_fst]; rfl
    have hcongr : (gluePlan (A := A) g hg).κ n =ᵐ[historyLaw P (gluePlan (A := A) g hg) s n]
        Kernel.sectR (Kernel.condKernel K) (g s n) := by
      filter_upwards [init_ae P (gluePlan (A := A) g hg) s n] with h hh
      show (cK (S := S) (A := A) n) (g (Hist.init h) n, h) = _
      rw [Kernel.sectR_apply, hh]
      rfl
    haveI := (gluePlan (A := A) g hg).κ_markov n
    have h1 : historyLaw P (gluePlan (A := A) g hg) s n ⊗ₘ (gluePlan (A := A) g hg).κ n = ρ := by
      rw [Measure.compProd_congr hcongr, hhist, ← hdis]
    show (historyLaw P (gluePlan (A := A) g hg) s n ⊗ₘ (gluePlan (A := A) g hg).κ n) ⊗ₘ nextKernel P n = _
    rw [h1, hρ, ← (hΓ.2 n).1]
  intro n
  induction n with
  | zero =>
    have h0 : historyLaw P (gluePlan (A := A) g hg) s 0 = (Λ S A 0 (g s 0)).map (fun x => x.1.1) := by
      rw [historyLaw_zero, hΓ.1]
    exact ⟨h0, hstage 0 h0⟩
  | succ n ih =>
    have h0 : historyLaw P (gluePlan (A := A) g hg) s (n + 1) =
        (Λ S A (n + 1) (g s (n + 1))).map (fun x => x.1.1) := by
      rw [historyLaw_succ, ih.2, (hΓ.2 n).2]
    exact ⟨h0, hstage (n + 1) h0⟩

theorem PhiC_le_glue (g : S → (ℕ → Code)) (hg : Measurable g) (s : S) :
    PhiC P (s, g s) ≤ I P (gluePlan (A := A) g hg) s := by
  unfold PhiC
  split_ifs with hΓ
  · have hl := laws_glue P g hg s hΓ
    unfold I R stageLoss
    simp only [(hl _).2]
    rfl
  · exact bot_le

/-! ### Completeness -/

theorem stageLaw_map_fst (π : Plan (S := S) (A := A)) (s : S) (n : ℕ) :
    (stageLaw P π s n).map Prod.fst = historyLaw P π s n ⊗ₘ π.κ n := by
  haveI := π.κ_markov n
  haveI := isProb_historyLaw P π s n
  exact Measure.fst_compProd _ _

theorem isProb_stageLaw (π : Plan (S := S) (A := A)) (s : S) (n : ℕ) :
    IsProbabilityMeasure (stageLaw P π s n) := by
  haveI := π.κ_markov n
  haveI := isProb_historyLaw P π s n
  show IsProbabilityMeasure ((historyLaw P π s n ⊗ₘ π.κ n) ⊗ₘ nextKernel P n)
  infer_instance

theorem stageLaw_map_fst_fst (π : Plan (S := S) (A := A)) (s : S) (n : ℕ) :
    (stageLaw P π s n).map (fun x => x.1.1) = historyLaw P π s n := by
  haveI := π.κ_markov n
  haveI := isProb_historyLaw P π s n
  rw [show (fun x : (Hist S A n × A) × S => x.1.1) = Prod.fst ∘ Prod.fst from rfl,
    ← Measure.map_map measurable_fst measurable_fst, stageLaw_map_fst]
  exact Measure.fst_compProd _ _

theorem exists_code_of_plan (π : Plan (S := S) (A := A)) (s : S) :
    ∃ y : ℕ → Code, PhiC P (s, y) = I P π s := by
  have hy : ∀ n, ∃ c, Λ S A n c = stageLaw P π s n := fun n => by
    haveI := isProb_stageLaw P π s n
    exact Λ_surj n _
  choose y hy using hy
  have hΓ : (s, y) ∈ Γ P := by
    refine ⟨?_, fun n => ⟨?_, ?_⟩⟩
    · simp only [hy, stageLaw_map_fst_fst, historyLaw_zero]
    · simp only [hy, stageLaw_map_fst]; rfl
    · simp only [hy, stageLaw_map_fst_fst, historyLaw_succ]
  refine ⟨y, ?_⟩
  simp only [PhiC, if_pos hΓ, R, hy]
  rfl

end NegativeDP.OptEq.P2a

/-! ## P2: (p, ε)-optimal history-dependent plans, from C1 and P2a by rational levels. -/

namespace NegativeDP.OptEq.P2

open Set NegativeDP.Stationary NegativeDP.Stationary.F42P6 NegativeDP.OptEq.P2a

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

theorem p2 (P : Problem S A) : ∀ p : Measure S, IsProbabilityMeasure p → ∀ ε : ℝ, 0 < ε →
    ∃ π : Plan (S := S) (A := A), ∀ᵐ s ∂p, vstar P s - (ε : EReal) ≤ I P π s := by
  intro p hp ε hε
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ε / 2 := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδ]; positivity
  obtain ⟨c, hc⟩ : ∃ c : ℕ → EReal, c = fun j : ℕ => ((-((j : ℝ) * δ) : ℝ) : EReal) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℕ → Set (S × (ℕ → Code)), B = fun j => {sy | c j < PhiC P sy} :=
    ⟨_, rfl⟩
  have hBm : ∀ j, MeasurableSet (B j) := fun j => by
    rw [hB]; exact measurableSet_lt measurable_const (measurable_PhiC P)
  have hsel : ∀ j, ∃ g : S → (ℕ → Code), Measurable g ∧
      ∀ᵐ s ∂p, (∃ y, (s, y) ∈ B j) → (s, g s) ∈ B j :=
    fun j => NegativeDP.OptEq.C1b.C1_selection p (B j) (hBm j)
  choose g hgm hgae using hsel
  classical
  let q : ℕ → S → Prop := fun j s => (s, g j s) ∈ B j ∨ ∀ k, (s, g k s) ∉ B k
  have hq : ∀ s, ∃ j, q j s := fun s => by
    by_cases h : ∃ k, (s, g k s) ∈ B k
    · obtain ⟨k, hk⟩ := h; exact ⟨k, Or.inl hk⟩
    · push_neg at h; exact ⟨0, Or.inr h⟩
  have hmem : ∀ j, MeasurableSet {s | (s, g j s) ∈ B j} := fun j =>
    (Measurable.prodMk measurable_id (hgm j)) (hBm j)
  have hqm : ∀ j, MeasurableSet {s | q j s} := fun j => by
    have : {s | q j s} = {s | (s, g j s) ∈ B j} ∪ (⋃ k, {s | (s, g k s) ∈ B k})ᶜ := by
      ext s; simp [q]
    rw [this]; exact (hmem j).union (MeasurableSet.iUnion hmem).compl
  let G : S → (ℕ → Code) := fun s => g (Nat.find (hq s)) s
  have hG : Measurable G := Measurable.find hgm hqm hq
  refine ⟨gluePlan (A := A) G hG, ?_⟩
  filter_upwards [ae_all_iff.2 hgae] with s hs
  have hvle : vstar P s ≤ 0 := vstar_nonpos P s
  rcases eq_bot_or_bot_lt (vstar P s) with hbot | hpos
  · rw [hbot, EReal.bot_sub]; exact bot_le
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (vstar P s).toReal := ⟨_, rfl⟩
  have hvx : vstar P s = (x : EReal) := by
    rw [hx]; exact (EReal.coe_toReal (hvle.trans_lt EReal.zero_lt_top).ne hpos.ne').symm
  have hx0 : x ≤ 0 := by rw [hvx] at hvle; exact_mod_cast hvle
  obtain ⟨j, hj⟩ : ∃ j : ℕ, j = ⌊-x / δ⌋₊ + 1 := ⟨_, rfl⟩
  have hj1 : -x < (j : ℝ) * δ := by
    have h1 : -x / δ < (j : ℝ) := by rw [hj]; push_cast; exact Nat.lt_floor_add_one _
    rwa [div_lt_iff₀ hδpos] at h1
  have hj2 : (j : ℝ) * δ ≤ -x + δ := by
    have h1 : ((⌊-x / δ⌋₊ : ℕ) : ℝ) ≤ -x / δ := Nat.floor_le (div_nonneg (by linarith) hδpos.le)
    have h2 : (j : ℝ) ≤ -x / δ + 1 := by rw [hj]; push_cast; linarith
    have h3 := mul_le_mul_of_nonneg_right h2 hδpos.le
    rw [add_mul, div_mul_cancel₀ _ hδpos.ne', one_mul] at h3
    exact h3
  have hcj : c j < vstar P s := by
    rw [hvx, hc]; exact EReal.coe_lt_coe_iff.2 (by linarith)
  have hcj' : vstar P s - (ε : EReal) ≤ c j := by
    rw [hvx, hc, ← EReal.coe_sub]; exact EReal.coe_le_coe_iff.2 (by rw [hδ] at hj2 ⊢; linarith)
  obtain ⟨π', hπ'⟩ : ∃ π' : Plan (S := S) (A := A), c j < I P π' s :=
    lt_iSup_iff.1 (show c j < ⨆ π : Plan (S := S) (A := A), I P π s from hcj)
  obtain ⟨y, hy⟩ := exists_code_of_plan P π' s
  have hBj : (s, g j s) ∈ B j := hs j ⟨y, by
    rw [hB]; show c j < PhiC P (s, y); rw [hy]; exact hπ'⟩
  have hN : Nat.find (hq s) ≤ j := Nat.find_min' (hq s) (Or.inl hBj)
  have hBN : (s, G s) ∈ B (Nat.find (hq s)) := by
    rcases Nat.find_spec (hq s) with h | h
    · exact h
    · exact absurd hBj (h j)
  have hcN : c j ≤ c (Nat.find (hq s)) := by
    rw [hc]
    refine EReal.coe_le_coe_iff.2 (neg_le_neg (mul_le_mul_of_nonneg_right ?_ hδpos.le))
    exact_mod_cast hN
  have hBc : ∀ k, (s, g k s) ∈ B k → c k < PhiC P (s, g k s) := fun k hk => by
    rw [hB] at hk; exact hk
  have hBN' : c (Nat.find (hq s)) < PhiC P (s, G s) := hBc _ hBN
  calc vstar P s - (ε : EReal) ≤ c j := hcj'
    _ ≤ c (Nat.find (hq s)) := hcN
    _ ≤ PhiC P (s, G s) := hBN'.le
    _ ≤ I P (gluePlan (A := A) G hG) s := PhiC_le_glue P G hG s

end NegativeDP.OptEq.P2

open MeasureTheory ProbabilityTheory Filter Topology in open DiscountedDP.Stationary (Hist Plan MarkovPlan stationary IsGenerated IsGeneratedPlan) in open NegativeDP.OptEq in
theorem solution {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A] (P : NegativeDP.Stationary.Problem S A) :
    ∀ p : Measure S, IsProbabilityMeasure p → ∀ ε : ℝ, 0 < ε →
      ∃ πstar : MarkovPlan S A, IsPEOptimal P p ε πstar.toPlan := by
  exact NegativeDP.Stationary.F42P6.theorem81_of_p2 P (NegativeDP.OptEq.P2.p2 P)
