-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result8_2_v2_atoms_c1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T20:35:27.088159+00:00
-- url     : https://prove2.me/submissions/40b9c328-d853-4470-8af9-0cbaceffdefc

/-
Worker solution for Prove2Me target d5e9acf8-5f4c-4200-afa7-dba2c6f70f07
(Kyprianou.Ch08.StageB.source_result8_2_v2_atoms_c1),
mission 774734e3-04f0-4425-85f7-4e268610a046, rev 0df444a360eaa60ab8c11dca51a86af692955474.
Integrates handoff 0217c297dc26420592010565 (atoms_c1_v2.lean SHA 0c9853f4...).
Compact revision to meet 100-line / 2500-token budget: dropped Set. prefixes,
factored 1/(k+1) monotonicity, replaced calc with trans lemmas, joined lines.
Unique path: candidates/work_on/kyprianou82_fragments/atoms_c1_solution_muse_20261122_v9.lean
Repair of 46061 CE (E01-E02 at L50): bare _ in refine asks the elaborator to synthesize (fails); only ?-holes become goals (tactic.constructor: refine <witness, ?_>). Restore v6 ?lo/?hi; L27 saving funds the mu-pin.
-/
import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
private lemma ts (n : Measure ℝ) (x : ℝ) : n (Ici x) = n (Ioi x) + n {x} := by
  have hdisj : Disjoint (Ioi x) ({x} : Set ℝ) := disjoint_left.mpr (fun y hy hx => ne_of_gt hy (mem_singleton_iff.mp hx))
  have hu : Ioi x ∪ ({x} : Set ℝ) = Ici x := by ext y; simp [mem_union, mem_Ioi, mem_Ici, mem_singleton_iff, le_iff_lt_or_eq, eq_comm]
  rw [← hu]; exact measure_union hdisj (measurableSet_singleton x)
private lemma tsR (n : Measure ℝ) {x : ℝ} (hIci : n (Ici x) < ⊤) : (n (Ici x)).toReal = (n (Ioi x)).toReal + (n {x}).toReal := by
  have hIoi : n (Ioi x) < ⊤ := lt_of_le_of_lt (measure_mono Ioi_subset_Ici_self) hIci
  have hx : n ({x} : Set ℝ) < ⊤ := lt_of_le_of_lt (measure_mono (singleton_subset_iff.mpr (mem_Ici.mpr le_rfl))) hIci
  rw [ts n x]; exact ENNReal.toReal_add hIoi.ne hx.ne
private lemma aiff {ψ : ℝ → ℝ} {q : ℝ} (n : Measure ℝ) (W : ℝ → ℝ) {x dL dR : ℝ} (hW : 0 < W x) (hIci : n (Ici x) < ⊤) (hL : dL = (Phi ψ q + (n (Ici x)).toReal) * W x) (hR : dR = (Phi ψ q + (n (Ioi x)).toReal) * W x) : dL = dR ↔ n {x} = 0 := by
  constructor
  · intro hEq; rw [hL, hR] at hEq; have hc := mul_right_cancel₀ (ne_of_gt hW) hEq; have hs := tsR n hIci; have hsing : (n ({x} : Set ℝ)).toReal = 0 := by linarith
    have hx : n ({x} : Set ℝ) < ⊤ := lt_of_le_of_lt (measure_mono (singleton_subset_iff.mpr (mem_Ici.mpr le_rfl))) hIci
    exact ((ENNReal.toReal_eq_zero_iff _).mp hsing).resolve_right hx.ne
  · intro ha; rw [hL, hR, tsR n hIci, ha, ENNReal.toReal_zero, add_zero]
private lemma cT (n : Measure ℝ) (hfin : ∀ x : ℝ, 0 < x → n (Ici x) < ⊤) (ha : ∀ x : ℝ, 0 < x → n {x} = 0) : ContinuousOn (fun x => (n (Ici x)).toReal) (Ioi 0) := by
  intro x hx
  have hIoi : n (Ioi x) = n (Ici x) := by simpa [ha x hx] using (ts n x).symm
  suffices hAt : ContinuousAt (fun t => (n (Ici t)).toReal) x by exact hAt.continuousWithinAt
  have hENN : Tendsto (fun t => n (Ici t)) (𝓝 x) (𝓝 (n (Ici x))) := by
    have hmono : Antitone fun t : ℝ => n (Ici t) := fun a b hab => measure_mono (Ici_subset_Ici.mpr hab)
    have hInter : (⋂ k : ℕ, Ici (x - 1 / ((k : ℝ) + 1))) = Ici x := by
      ext y; constructor
      · intro hy; by_contra hnge; have hlt : y < x := lt_of_not_ge hnge; obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt); have hyk := mem_iInter.mp hy k; simp only [mem_Ici] at hyk; linarith
      · intro hy; simp only [mem_iInter, mem_Ici] at hy ⊢; intro k; have hp : 0 < 1 / ((k : ℝ) + 1) := (by positivity); linarith
    have hUnion : (⋃ k : ℕ, Ici (x + 1 / ((k : ℝ) + 1))) = Ioi x := by
      ext y; constructor
      · intro hy; obtain ⟨k, hk⟩ := mem_iUnion.mp hy; simp only [mem_Ici] at hk; have hp : 0 < 1 / ((k : ℝ) + 1) := (by positivity); simp [mem_Ioi]; linarith
      · intro hy; simp [mem_Ioi] at hy; obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr hy); exact mem_iUnion.mpr ⟨k, by simp only [mem_Ici]; linarith⟩
    have hLA : Antitone fun k : ℕ => Ici (x - 1 / ((k : ℝ) + 1)) := fun a b hab => Ici_subset_Ici.mpr (sub_le_sub_left (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hab 1)) x)
    have hLM (k : ℕ) : NullMeasurableSet (Ici (x - 1 / ((k : ℝ) + 1))) n := measurableSet_Ici.nullMeasurableSet
    have hLF : ∃ k : ℕ, n (Ici (x - 1 / ((k : ℝ) + 1))) ≠ ∞ := by obtain ⟨k0, hk0⟩ := exists_nat_one_div_lt (mem_Ioi.mp hx); exact ⟨k0, (hfin _ (by linarith)).ne⟩
    have hLT := tendsto_measure_iInter_atTop hLM hLA hLF; rw [hInter] at hLT
    have hRM : Monotone fun k : ℕ => Ici (x + 1 / ((k : ℝ) + 1)) := fun a b hab => Ici_subset_Ici.mpr (add_le_add_right (one_div_le_one_div_of_le (by positivity) (show (a : ℝ) + 1 ≤ (b : ℝ) + 1 by exact_mod_cast Nat.add_le_add_right hab 1)) x)
    have hRT := tendsto_measure_iUnion_atTop (μ := n) hRM; rw [hUnion, hIoi] at hRT; refine tendsto_order.2 ⟨?lo, ?hi⟩
    · intro z hz; obtain ⟨k, hk⟩ := eventually_atTop.1 ((tendsto_order.1 hRT).1 z hz); have hmem : Ioo (x - 1) (x + 1 / ((k : ℝ) + 1)) ∈ 𝓝 x := Ioo_mem_nhds (by linarith) (by have : 0 < 1 / ((k : ℝ) + 1) := (by positivity); linarith); filter_upwards [hmem] with t ht; by_cases hle : t ≤ x
      · exact lt_of_lt_of_le hz (hmono hle)
      · push_neg at hle; exact lt_of_lt_of_le (hk k le_rfl) (measure_mono (Ici_subset_Ici.mpr (le_of_lt ht.2)))
    · intro z hz; obtain ⟨k, hk⟩ := eventually_atTop.1 ((tendsto_order.1 hLT).2 z hz); have hmem : Ioo (x - 1 / ((k : ℝ) + 1)) (x + 1) ∈ 𝓝 x := Ioo_mem_nhds (by have : 0 < 1 / ((k : ℝ) + 1) := (by positivity); linarith) (by linarith); filter_upwards [hmem] with t ht; by_cases hle : x ≤ t
      · exact lt_of_le_of_lt (hmono hle) hz
      · push_neg at hle; exact lt_of_le_of_lt (measure_mono (Ici_subset_Ici.mpr (le_of_lt ht.1))) (hk k le_rfl)
  exact (ENNReal.tendsto_toReal (hfin x hx).ne).comp hENN
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ) (q : ℝ) (n : Measure ℝ)
    (hn : HasActualQExcursionHeightLaw P D ψ q n)
    (hRep : HasQExcursionScaleRepresentation ψ q (W q) n)
    (hDeriv : ∀ x : ℝ, 0 < x →
      ∃ dLeft dRight : ℝ,
        HasDerivWithinAt (W q) dLeft (Iic x) x ∧
        HasDerivWithinAt (W q) dRight (Ici x) x ∧
        dLeft = (Phi ψ q + (n (Ici x)).toReal) * W q x ∧
        dRight = (Phi ψ q + (n (Ioi x)).toReal) * W q x) :
    (∀ x : ℝ, 0 < x →
      ∃ dLeft dRight : ℝ,
        HasDerivWithinAt (W q) dLeft (Iic x) x ∧
        HasDerivWithinAt (W q) dRight (Ici x) x ∧
        dLeft = (Phi ψ q + (n (Ici x)).toReal) * W q x ∧
        dRight = (Phi ψ q + (n (Ioi x)).toReal) * W q x ∧
        (dLeft = dRight ↔ n {x} = 0)) ∧
    (ContDiffOn ℝ 1 (W q) (Ioi (0 : ℝ)) ↔
      ∀ x : ℝ, 0 < x → n {x} = 0) := by
  have hfin := fun x hx => (hn.2 x x hx hx).1; refine ⟨?p1, ?p2⟩
  · intro x hx; rcases hDeriv x hx with ⟨dL, dR, hdL, hdR, hLd, hRd⟩; exact ⟨dL, dR, hdL, hdR, hLd, hRd, aiff n (W q) (hRep.1 x hx) (hfin x hx) hLd hRd⟩
  · constructor
    · intro hC1 x hx; have hDO : DifferentiableOn ℝ (W q) (Ioi 0) := hC1.differentiableOn one_ne_zero
      have hAt : HasDerivAt (W q) (deriv (W q) x) x := (hDO.differentiableAt (Ioi_mem_nhds hx)).hasDerivAt
      have hL0 : HasDerivWithinAt (W q) (deriv (W q) x) (Iic x) x := hAt.hasDerivWithinAt
      have hR0 : HasDerivWithinAt (W q) (deriv (W q) x) (Ici x) x := hAt.hasDerivWithinAt
      rcases hDeriv x hx with ⟨dL, dR, hdL, hdR, hLd, hRd⟩
      have huL : UniqueDiffWithinAt ℝ (Iic x) x := (uniqueDiffOn_Iic x).uniqueDiffWithinAt (mem_Iic.mpr le_rfl)
      have huR : UniqueDiffWithinAt ℝ (Ici x) x := (uniqueDiffOn_Ici x).uniqueDiffWithinAt (mem_Ici.mpr le_rfl)
      have hDL : dL = deriv (W q) x := (hdL.derivWithin huL).symm.trans (hL0.derivWithin huL)
      have hDR : dR = deriv (W q) x := (hdR.derivWithin huR).symm.trans (hR0.derivWithin huR)
      exact (aiff n (W q) (hRep.1 x hx) (hfin x hx) hLd hRd).mp (hDL.trans hDR.symm)
    · intro ha; have hDA : ∀ x ∈ Ioi 0, HasDerivAt (W q) ((Phi ψ q + (n (Ioi x)).toReal) * W q x) x := by intro x hx; rcases hDeriv x hx with ⟨dL, dR, hdL, hdR, hLd, hRd⟩; have hEq := (aiff n (W q) (hRep.1 x hx) (hfin x hx) hLd hRd).mpr (ha x hx); have hdL' := hEq ▸ hdL; have hAt := (by simpa [Iic_union_Ici, hasDerivWithinAt_univ] using (hdL'.union hdR)); simpa [hRd] using hAt
      have hTI := cT n hfin ha
      have hTO : ContinuousOn (fun x => (n (Ioi x)).toReal) (Ioi 0) := by refine hTI.congr ?_; intro y hy; simpa [ha y hy] using (tsR n (hfin y hy)).symm
      have hDF : ContinuousOn (fun x => (Phi ψ q + (n (Ioi x)).toReal) * W q x) (Ioi 0) := (continuousOn_const.add hTO).mul (fun x hx => (hDA x hx).continuousAt.continuousWithinAt)
      have hDW : ContinuousOn (derivWithin (W q) (Ioi 0)) (Ioi 0) := by refine hDF.congr ?_; intro x hx; rw [derivWithin_of_mem_nhds (Ioi_mem_nhds hx)]; exact (hDA x hx).deriv
      exact (contDiffOn_one_iff_derivWithin isOpen_Ioi.uniqueDiffOn).mpr ⟨(fun x hx => (hDA x hx).differentiableAt.differentiableWithinAt), hDW⟩
