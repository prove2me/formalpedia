-- Prove2me | solution 1 for MultiStageAlloc.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-23T10:03:33.793482+00:00
-- url     : https://prove2.me/submissions/8e6f00ec-b159-408e-8af9-161632d3626d

import Mathlib
import Definitions.Def_MultiStageAlloc_OfflineLP
import Definitions.Def_MultiStageAlloc_Run
import Theorems.Thm_MultiStageAlloc_certificate
import Theorems.Thm_MultiStageAlloc_step_i
import Theorems.Thm_MultiStageAlloc_inequality_1
import Theorems.Thm_MultiStageAlloc_run_feasible
import Theorems.Thm_MultiStageAlloc_proposition_1
import Theorems.Thm_MultiStageAlloc_proposition_2

namespace NCMSA
open MultiStageAlloc

variable {U V : Type*} [Fintype U] [Fintype V] {K : ℕ}

/-- `regPoly K k` is interval integrable everywhere. -/
lemma regPoly_intervalIntegrable (K k : ℕ) (a b : ℝ) :
    IntervalIntegrable (regPoly K k) MeasureTheory.volume a b := by
  by_cases hk : k < K
  · have : Continuous (regPoly K k) := by
      have h : regPoly K k = fun x => (1 - (1 - x) / ((K - k : ℕ) : ℝ)) ^ (K - k) := by
        funext x; simp [regPoly, hk]
      rw [h]; fun_prop
    exact this.intervalIntegrable a b
  · have h : regPoly K k = Set.indicator {(1 : ℝ)} (fun _ => 1) := by
      funext x; simp [regPoly, hk, Set.indicator]
    rw [h]
    have h0 : (Set.indicator {(1 : ℝ)} (fun _ => (1 : ℝ))) =ᵐ[MeasureTheory.volume] 0 := by
      have : MeasureTheory.volume ({(1 : ℝ)} : Set ℝ) = 0 := Real.volume_singleton
      filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp this] with x hx
      simp [Set.indicator, hx]
    exact (intervalIntegrable_const (c := (0 : ℝ))).congr_ae
      (MeasureTheory.ae_restrict_of_ae h0.symm)

lemma regF_continuous (K k : ℕ) : Continuous (regF K k) := by
  unfold regF
  exact intervalIntegral.continuous_primitive (regPoly_intervalIntegrable K k) 0

lemma stageObj_continuous (I : Instance U V K) (k : ℕ) (y : V → ℝ) :
    Continuous (stageObj I k y) := by
  unfold stageObj level
  have hF := regF_continuous K k
  fun_prop

lemma stageFeasible_compact (I : Instance U V K) (k : ℕ) (y : V → ℝ) :
    IsCompact {z | StageFeasible I k y z} := by
  have hsub : {z | StageFeasible I k y z} ⊆
      Set.pi Set.univ (fun _ : U => Set.pi Set.univ (fun _ : V => Set.Icc (0 : ℝ) 1)) := by
    intro z hz i _ j _
    refine ⟨hz.1 i j, ?_⟩
    calc z i j ≤ ∑ j', z i j' :=
          Finset.single_le_sum (f := fun j' => z i j') (fun j' _ => hz.1 i j') (Finset.mem_univ j)
      _ ≤ 1 := hz.2.2.1 i
  have hcpt : IsCompact
      (Set.pi Set.univ (fun _ : U => Set.pi Set.univ (fun _ : V => Set.Icc (0 : ℝ) 1))) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  refine hcpt.of_isClosed_subset ?_ hsub
  have hsupp : ∀ i j, IsClosed {z : U → V → ℝ | z i j ≠ 0 → I.edge i j ∧ I.batch i = k} := by
    intro i j
    by_cases hP : I.edge i j ∧ I.batch i = k
    · simp only [hP, imp_true_iff, and_self]; exact isClosed_univ
    · have : {z : U → V → ℝ | z i j ≠ 0 → I.edge i j ∧ I.batch i = k} = {z | z i j = 0} := by
        ext z; simp only [Set.mem_setOf_eq]; tauto
      rw [this]; exact isClosed_eq (by fun_prop) continuous_const
  have e : {z | StageFeasible I k y z} =
      {z : U → V → ℝ | ∀ i j, 0 ≤ z i j} ∩ ({z | StageSupported I k z} ∩
        ({z | ∀ i, ∑ j, z i j ≤ 1} ∩ {z | ∀ j, ∑ i, z i j ≤ I.cap j * (1 - y j)})) :=
    Set.ext fun z => Iff.rfl
  have hA : IsClosed {z : U → V → ℝ | ∀ i j, 0 ≤ z i j} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_le continuous_const (by fun_prop)
  have hB : IsClosed {z | StageSupported I k z} := by
    simp only [StageSupported, Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => hsupp i j
  have hC : IsClosed {z : U → V → ℝ | ∀ i, ∑ j, z i j ≤ 1} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const
  have hD : IsClosed {z : U → V → ℝ | ∀ j, ∑ i, z i j ≤ I.cap j * (1 - y j)} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun j => isClosed_le (by fun_prop) continuous_const
  rw [e]; exact hA.inter (hB.inter (hC.inter hD))

lemma exists_stageOptimal (I : Instance U V K) (k : ℕ) (y : V → ℝ) (hy : ∀ j, y j ≤ 1) :
    ∃ x, IsStageOptimal I k y x := by
  have hne : (0 : U → V → ℝ) ∈ {z | StageFeasible I k y z} := by
    refine ⟨fun _ _ => le_rfl, fun i j h => (h rfl).elim, fun i => by simp, fun j => ?_⟩
    simp only [Pi.zero_apply, Finset.sum_const_zero]
    exact mul_nonneg (I.cap_pos j).le (by linarith [hy j])
  obtain ⟨x, hx, hmax⟩ := (stageFeasible_compact I k y).exists_isMaxOn ⟨_, hne⟩
    (stageObj_continuous I k y).continuousOn
  exact ⟨x, hx, hmax⟩

open Classical in
noncomputable def xsel (I : Instance U V K) (k : ℕ) (y : V → ℝ) : U → V → ℝ :=
  if h : ∃ x, IsStageOptimal I k y x then h.choose else 0

noncomputable def ySeq (I : Instance U V K) : ℕ → V → ℝ
  | 0 => 0
  | n + 1 => level I (ySeq I n) (xsel I (n + 1) (ySeq I n))

noncomputable def xSeq (I : Instance U V K) (k : ℕ) : U → V → ℝ :=
  xsel I k (ySeq I (k - 1))

lemma ySeq_le_one (I : Instance U V K) : ∀ n j, ySeq I n j ≤ 1 := by
  intro n
  induction n with
  | zero => intro j; simp [ySeq]
  | succ n ih =>
    intro j
    have hex := exists_stageOptimal I (n + 1) (ySeq I n) ih
    have hopt : IsStageOptimal I (n + 1) (ySeq I n) (xsel I (n + 1) (ySeq I n)) := by
      simp only [xsel, dif_pos hex]; exact hex.choose_spec
    have h4 := hopt.1.2.2.2 j
    have hc := I.cap_pos j
    show level I (ySeq I n) (xsel I (n + 1) (ySeq I n)) j ≤ 1
    unfold level
    have : (∑ i, xsel I (n + 1) (ySeq I n) i j) / I.cap j ≤ 1 - ySeq I n j := by
      rw [div_le_iff₀ hc]; linarith
    rw [← Finset.sum_div]; linarith

lemma run_exists (I : Instance U V K) : IsRun I (xSeq I) (ySeq I) := by
  refine ⟨rfl, fun k hk1 hkK => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hex := exists_stageOptimal I (n + 1) (ySeq I n) (ySeq_le_one I n)
  refine ⟨?_, fun j => rfl⟩
  show IsStageOptimal I (n + 1) (ySeq I n) (xsel I (n + 1) (ySeq I n))
  simp only [xsel, dif_pos hex]
  exact hex.choose_spec

lemma bound (hK : 1 ≤ K) (I : Instance U V K) (x : ℕ → U → V → ℝ) (y : ℕ → V → ℝ)
    (hrun : IsRun I x y) : gammaK K * OPT I ≤ ALG I x := by
  obtain ⟨⟨a, b, hab⟩, hobj⟩ := step_i hK I x y hrun
  have hy := (run_feasible I x y hrun).2.2
  have hΔ : ∀ s ∈ Finset.Icc 1 K, ∀ j, 0 ≤ deltaBeta I x y b s j := by
    intro s hs j
    obtain ⟨hs1, hsK⟩ := Finset.mem_Icc.mp hs
    unfold deltaBeta
    split_ifs with hlt
    · have hst := hrun.2 s hs1 hsK
      refine mul_nonneg (Finset.sum_nonneg fun i _ =>
        div_nonneg (hst.1.1.1 i j) (I.cap_pos j).le) (sub_nonneg.mpr ?_)
      have hP := (proposition_2 I s hs1 hlt (y (s - 1)) (hy (s - 1) (by omega)) (x s) hst.1).1
        (offlinePair I s (y (s - 1)) (x s) j) j (by simp [pairV])
      rw [← hP]
      unfold levelPrice
      have hmem : level I (y (s - 1)) (x s) j ∈ Set.Icc (0 : ℝ) 1 := by
        rw [← hst.2 j]; exact hy s hsK j
      have hr := (proposition_1 K hK).2.2.1 s hs1 hsK _ hmem
      have hw := I.w_nonneg j
      nlinarith [hr.1]
    · exact mul_nonneg (sub_nonneg.mpr (hy (K - 1) (by omega) j).2) (hab.1.2.1 j)
  refine certificate hK I x y hrun (dualAlpha I x y a) (dualBeta I x y b) ?_ ?_ (hobj a b hab) ?_
  · intro i
    have hb := Finset.mem_Icc.mp (I.batch_mem i)
    unfold dualAlpha
    split_ifs with hlt
    · exact (proposition_2 I _ hb.1 hlt _ (hy _ (by omega)) _ (hrun.2 _ hb.1 hb.2).1).2.2.2.2 _
    · exact hab.1.1 i (by omega)
  · intro j; exact Finset.sum_nonneg fun s hs => hΔ s hs j
  · intro i j hij
    have hb := Finset.mem_Icc.mp (I.batch_mem i)
    have h1 := inequality_1 hK I x y hrun a b hab (I.batch i) hb.1 hb.2 i j hij rfl
    have h2 : ∑ s ∈ Finset.Icc 1 (I.batch i), deltaBeta I x y b s j ≤ dualBeta I x y b j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hb.2)
        (fun s hs _ => hΔ s hs j)
    unfold gammaK
    linarith

end NCMSA

open MultiStageAlloc in
theorem solution {U V : Type*} [Fintype U] [Fintype V] (K : ℕ) (hK : 1 ≤ K)
    (I : Instance U V K) :
    (∃ x y, IsRun I x y) ∧ ∀ x y, IsRun I x y → gammaK K * OPT I ≤ ALG I x :=
  ⟨⟨_, _, NCMSA.run_exists I⟩, fun x y h => NCMSA.bound hK I x y h⟩
