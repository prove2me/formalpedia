-- Prove2me | solution 1 for KallMayerSLP.Multistage.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T10:17:59.235555+00:00
-- url     : https://prove2.me/submissions/71998bc7-7c33-45c7-a778-91b82f9fa86d

import Definitions.Def_KallMayerSLP_Multistage_Assumption32
import Definitions.Def_KallMayerSLP_Multistage_aggValue
import Mathlib.Tactic.FunProp
import Mathlib.Tactic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Data.ENNReal.BigOperators
import Definitions.Def_KallMayerSLP_Multistage_IsFeasiblePolicy
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_KallMayerSLP_Multistage_zeta
import Mathlib.Probability.Independence.Integration
import Definitions.Def_KallMayerSLP_Multistage_objective
import Definitions.Def_KallMayerSLP_Multistage_value

/-!
Complete proof of the exact published Kall–Mayer multistage aggregation lower bound.
All session-local helpers are inlined. The original scenario tree, probabilities,
null-node constraints, and extended-real optimal values are retained.
-/

set_option autoImplicit false

/- Inlined from Solutions.P082Null. -/
namespace S04P082

open MeasureTheory KallMayerSLP.Multistage
open scoped Matrix

variable {D : MSLP} {Ξ : ∀ t, Set (Fin (D.r t) → ℝ)}
    (𝒯 : ScenarioTree D Ξ)

@[simp] theorem anc_self {t : ℕ} (n : 𝒯.Node t) :
    𝒯.anc (le_refl t) n = n := by
  simp [ScenarioTree.anc]

theorem anc_succ {s t : ℕ} (h : s ≤ t) (n : 𝒯.Node (t + 1)) :
    𝒯.anc (Nat.le_succ_of_le h) n = 𝒯.anc h (𝒯.parent t n) := by
  simp [ScenarioTree.anc, Nat.leRec_succ, h]

theorem anc_trans {r s t : ℕ} (hrs : r ≤ s) (hst : s ≤ t) (n : 𝒯.Node t) :
    𝒯.anc hrs (𝒯.anc hst n) = 𝒯.anc (hrs.trans hst) n := by
  induction hst with
  | refl => simp
  | @step t hst ih =>
      rw [anc_succ 𝒯 hst, anc_succ 𝒯 (hrs.trans hst)]
      exact ih _

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ξ : ∀ t, Ω → Fin (D.r t) → ℝ)

@[simp] theorem nodeProb_one (n : 𝒯.Node 1) : nodeProb 𝒯 P ξ n = 1 := by
  simp [nodeProb]

theorem nodeProb_ancestor_ne_zero {s t : ℕ} (hst : s ≤ t) (n : 𝒯.Node t)
    (hn : nodeProb 𝒯 P ξ n ≠ 0) : nodeProb 𝒯 P ξ (𝒯.anc hst n) ≠ 0 := by
  classical
  rw [nodeProb, Finset.prod_ne_zero_iff] at hn ⊢
  intro u hu
  let v : Set.Icc 2 t := ⟨u.1, u.2.1, u.2.2.trans hst⟩
  have hv := hn v (Finset.mem_univ _)
  simpa only [anc_trans] using hv

variable (Y : ∀ t, 𝒯.Node t → Fin (D.n t) → ℝ)
    (hcomplete : ∀ t, 2 ≤ t → t ≤ D.T → IsCompleteRecourse (D.A t t))

noncomputable def nullFill (t : ℕ) (n : 𝒯.Node t) : Fin (D.n t) → ℝ :=
  if hgood : nodeProb 𝒯 P ξ n ≠ 0 then Y t n
  else if ht : 2 ≤ t ∧ t ≤ D.T then
    Classical.choose (hcomplete t ht.1 ht.2
      (D.b t (zetaHat 𝒯 P ξ n) -
        ∑ s : Set.Icc 1 t, if hs : (s : ℕ) < t then
          D.A t s *ᵥ nullFill s (𝒯.anc s.2.2 n) else 0))
  else 0
termination_by t

theorem nullFill_eq_of_ne_zero {t : ℕ} (n : 𝒯.Node t)
    (hn : nodeProb 𝒯 P ξ n ≠ 0) : nullFill 𝒯 P ξ Y hcomplete t n = Y t n := by
  rw [nullFill, dif_pos hn]

theorem history_sum_split (X : ∀ t, 𝒯.Node t → Fin (D.n t) → ℝ)
    {t : ℕ} (ht : 1 ≤ t) (n : 𝒯.Node t) :
    ∑ s : Set.Icc 1 t, D.A t s *ᵥ X s (𝒯.anc s.2.2 n) =
      (∑ s : Set.Icc 1 t, if (s : ℕ) < t then
        D.A t s *ᵥ X s (𝒯.anc s.2.2 n) else 0) + D.A t t *ᵥ X t n := by
  classical
  let last : Set.Icc 1 t := ⟨t, ht, le_rfl⟩
  have hterm (s : Set.Icc 1 t) :
      D.A t s *ᵥ X s (𝒯.anc s.2.2 n) =
        (if (s : ℕ) < t then D.A t s *ᵥ X s (𝒯.anc s.2.2 n) else 0) +
        (if s = last then D.A t t *ᵥ X t n else 0) := by
    by_cases hs : (s : ℕ) < t
    · have hne : s ≠ last := by
        intro heq
        have := congrArg Subtype.val heq
        dsimp [last] at this
        omega
      simp [hs, hne]
    · have heq : s = last := Subtype.ext (Nat.le_antisymm s.2.2 (Nat.le_of_not_gt hs))
      subst s
      simp [last]
  calc
    _ = ∑ s : Set.Icc 1 t,
        ((if (s : ℕ) < t then D.A t s *ᵥ X s (𝒯.anc s.2.2 n) else 0) +
        (if s = last then D.A t t *ᵥ X t n else 0)) := by
      exact Finset.sum_congr rfl (fun s _ => hterm s)
    _ = _ := by
      rw [Finset.sum_add_distrib]
      congr 1
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem nullFill_isAggFeasible
    (hY : ∀ t, 1 ≤ t → t ≤ D.T → ∀ n : 𝒯.Node t, nodeProb 𝒯 P ξ n ≠ 0 →
      (∑ s : Set.Icc 1 t, D.A t s *ᵥ Y s (𝒯.anc s.2.2 n) =
        D.b t (zetaHat 𝒯 P ξ n)) ∧ 0 ≤ Y t n) :
    IsAggFeasible 𝒯 P ξ (nullFill 𝒯 P ξ Y hcomplete) := by
  classical
  intro t ht hT n
  by_cases hn : nodeProb 𝒯 P ξ n ≠ 0
  · constructor
    · calc
        _ = ∑ s : Set.Icc 1 t, D.A t s *ᵥ Y s (𝒯.anc s.2.2 n) := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [nullFill_eq_of_ne_zero 𝒯 P ξ Y hcomplete _
            (nodeProb_ancestor_ne_zero 𝒯 P ξ s.2.2 n hn)]
        _ = _ := (hY t ht hT n hn).1
    · rw [nullFill_eq_of_ne_zero 𝒯 P ξ Y hcomplete _ hn]
      exact (hY t ht hT n hn).2
  · have ht2 : 2 ≤ t := by
      by_contra h
      have heq : t = 1 := by omega
      subst t
      exact hn (by simp)
    let z := D.b t (zetaHat 𝒯 P ξ n) -
      ∑ s : Set.Icc 1 t, if (s : ℕ) < t then
        D.A t s *ᵥ nullFill 𝒯 P ξ Y hcomplete s (𝒯.anc s.2.2 n) else 0
    have heq : nullFill 𝒯 P ξ Y hcomplete t n =
        Classical.choose (hcomplete t ht2 hT z) := by
      rw [nullFill, dif_neg hn, dif_pos ⟨ht2, hT⟩]
    have hspec := Classical.choose_spec (hcomplete t ht2 hT z)
    constructor
    · rw [history_sum_split 𝒯 _ ht n, heq, hspec.2]
      dsimp [z]
      abel
    · rw [heq]
      exact hspec.1

theorem nullFill_aggObjective :
    aggObjective 𝒯 P ξ (nullFill 𝒯 P ξ Y hcomplete) = aggObjective 𝒯 P ξ Y := by
  classical
  unfold aggObjective
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : nodeProb 𝒯 P ξ n ≠ 0
  · rw [nullFill_eq_of_ne_zero 𝒯 P ξ Y hcomplete _ hp]
  · simp [not_not.mp hp]

include hcomplete in
theorem aggValue_le_of_positive_feasible
    (hY : ∀ t, 1 ≤ t → t ≤ D.T → ∀ n : 𝒯.Node t, nodeProb 𝒯 P ξ n ≠ 0 →
      (∑ s : Set.Icc 1 t, D.A t s *ᵥ Y s (𝒯.anc s.2.2 n) =
        D.b t (zetaHat 𝒯 P ξ n)) ∧ 0 ≤ Y t n) :
    aggValue 𝒯 P ξ ≤ ((aggObjective 𝒯 P ξ Y : ℝ) : EReal) := by
  calc
    _ ≤ ((aggObjective 𝒯 P ξ (nullFill 𝒯 P ξ Y hcomplete) : ℝ) : EReal) :=
      iInf_le_of_le (nullFill 𝒯 P ξ Y hcomplete)
        (iInf_le_of_le (nullFill_isAggFeasible 𝒯 P ξ Y hcomplete hY) le_rfl)
    _ = _ := congrArg (fun z : ℝ => (z : EReal)) (nullFill_aggObjective 𝒯 P ξ Y hcomplete)


end S04P082

/- Inlined from Solutions.P082Events. -/
namespace S04P082

open MeasureTheory ProbabilityTheory KallMayerSLP.Multistage

variable {D : MSLP} {Ξ : ∀ t, Set (Fin (D.r t) → ℝ)}
    (𝒯 : ScenarioTree D Ξ)
    {Ω : Type*} [MeasurableSpace Ω]
    (ξ : ∀ t, Ω → Fin (D.r t) → ℝ)

def nodeEvent {t : ℕ} (n : 𝒯.Node t) : Set Ω :=
  {ω | ∀ s : Set.Icc 2 t, ξ s ω ∈ 𝒯.cell s (𝒯.anc s.2.2 n)}

theorem nodeEvent_eq_iInter {t : ℕ} (n : 𝒯.Node t) :
    nodeEvent 𝒯 ξ n = ⋂ s : Set.Icc 2 t, ξ s ⁻¹' 𝒯.cell s (𝒯.anc s.2.2 n) := by
  ext ω
  simp only [nodeEvent, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]

theorem interval_measurable {k : ℕ} {S : Set (Fin k → ℝ)}
    (hS : IsInterval S) : MeasurableSet S := by
  obtain ⟨I, hI, rfl⟩ := hS
  exact MeasurableSet.univ_pi (fun i => (hI i).measurableSet)

@[simp] theorem nodeEvent_one (n : 𝒯.Node 1) : nodeEvent 𝒯 ξ n = Set.univ := by
  ext ω
  simp [nodeEvent]

theorem nodeEvent_succ {t : ℕ} (ht : 1 ≤ t) (n : 𝒯.Node (t + 1)) :
    nodeEvent 𝒯 ξ n = nodeEvent 𝒯 ξ (𝒯.parent t n) ∩
      (ξ (t + 1) ⁻¹' 𝒯.cell (t + 1) n) := by
  ext ω
  constructor
  · intro hω
    constructor
    · intro s
      have h := hω ⟨s.1, s.2.1, Nat.le_succ_of_le s.2.2⟩
      change ξ s.1 ω ∈ 𝒯.cell s.1 (𝒯.anc (Nat.le_succ_of_le s.2.2) n) at h
      rw [anc_succ] at h
      exact h
    · have h := hω ⟨t + 1, by omega, le_rfl⟩
      simpa using h
  · rintro ⟨hparent, hlast⟩ ⟨s, hslo, hshi⟩
    by_cases hst : s = t + 1
    · subst s
      simpa using hlast
    · have hle : s ≤ t := by omega
      have h := hparent ⟨s, hslo, hle⟩
      change ξ s ω ∈ 𝒯.cell s (𝒯.anc (Nat.le_succ_of_le hle) n)
      rw [anc_succ]
      exact h


theorem pairwiseDisjoint_nodeEvent {t : ℕ} (hlo : 1 ≤ t) (ht : t ≤ D.T) :
    Pairwise (fun n m : 𝒯.Node t => Disjoint (nodeEvent 𝒯 ξ n) (nodeEvent 𝒯 ξ m)) := by
  induction hlo with
  | refl =>
      letI := 𝒯.uniqueRoot
      intro n m hnm
      exact (hnm (Subsingleton.elim n m)).elim
  | @step t hlo ih =>
      intro n m hnm
      rw [nodeEvent_succ 𝒯 ξ hlo n, nodeEvent_succ 𝒯 ξ hlo m]
      by_cases hp : 𝒯.parent t n = 𝒯.parent t m
      · have hd := (𝒯.disjoint_cell t hlo (by omega) n m hp hnm).preimage (ξ (t + 1))
        exact hd.mono Set.inter_subset_right Set.inter_subset_right
      · have hd := ih (by omega) hp
        exact hd.mono Set.inter_subset_left Set.inter_subset_left

variable (P : Measure Ω) (hA : Assumption32 D P ξ Ξ)

include hA

theorem measurableSet_nodeEvent {t : ℕ} (ht : t ≤ D.T) (n : 𝒯.Node t) :
    MeasurableSet (nodeEvent 𝒯 ξ n) := by
  rw [nodeEvent_eq_iInter]
  exact MeasurableSet.iInter (fun s =>
    (interval_measurable (𝒯.isInterval_cell s s.2.1 (s.2.2.trans ht) _)).preimage
      (hA.measurable_xi s s.2.1 (s.2.2.trans ht)))

theorem measure_nodeEvent {t : ℕ} (ht : t ≤ D.T) (n : 𝒯.Node t) :
    P (nodeEvent 𝒯 ξ n) =
      ∏ s : Set.Icc 2 t, P (ξ s ⁻¹' 𝒯.cell s (𝒯.anc s.2.2 n)) := by
  classical
  let emb : Set.Icc 2 t → Set.Icc 2 D.T :=
    fun s => ⟨s.1, s.2.1, s.2.2.trans ht⟩
  have hemb : Function.Injective emb := by
    intro s u h
    exact Subtype.ext (congrArg (fun x : Set.Icc 2 D.T => x.1) h)
  have hind : iIndepFun (fun s : Set.Icc 2 t => ξ s) P :=
    hA.indep.precomp hemb
  have h := hind.measure_inter_preimage_eq_mul Finset.univ
    (sets := fun s => 𝒯.cell s (𝒯.anc s.2.2 n))
    (fun s _ => interval_measurable (𝒯.isInterval_cell s s.2.1 (s.2.2.trans ht) _))
  simpa only [Finset.mem_univ, Set.iInter_true, nodeEvent_eq_iInter] using h

theorem real_nodeEvent {t : ℕ} (ht : t ≤ D.T) (n : 𝒯.Node t) :
    P.real (nodeEvent 𝒯 ξ n) = nodeProb 𝒯 P ξ n := by
  simp only [Measure.real, measure_nodeEvent 𝒯 ξ P hA ht n, ENNReal.toReal_prod, nodeProb]


theorem ae_mem_iUnion_nodeEvent {t : ℕ} (hlo : 1 ≤ t) (ht : t ≤ D.T) :
    ∀ᵐ ω ∂P, ω ∈ ⋃ n : 𝒯.Node t, nodeEvent 𝒯 ξ n := by
  induction hlo with
  | refl =>
      letI := 𝒯.uniqueRoot
      filter_upwards [] with ω
      simp
  | @step t hlo ih =>
      have hprev := ih (by omega)
      have hxi := hA.ae_mem (t + 1) (Nat.succ_le_succ hlo) ht
      filter_upwards [hprev, hxi] with ω hω hx
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hω
      rw [← 𝒯.iUnion_cell t hlo (by omega) n] at hx
      obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hp, hv⟩ := Set.mem_iUnion.mp hv
      apply Set.mem_iUnion.mpr
      refine ⟨v, ?_⟩
      rw [nodeEvent_succ 𝒯 ξ hlo, hp]
      exact ⟨hn, hv⟩

theorem integral_partition_nodeEvent {t : ℕ} (hlo : 1 ≤ t) (ht : t ≤ D.T)
    {f : Ω → ℝ} (hf : Integrable f P) :
    ∑ n : 𝒯.Node t, ∫ ω in nodeEvent 𝒯 ξ n, f ω ∂P = ∫ ω, f ω ∂P := by
  classical
  rw [← integral_iUnion_fintype
    (fun n => measurableSet_nodeEvent 𝒯 ξ P hA ht n)
    (pairwiseDisjoint_nodeEvent 𝒯 ξ hlo ht)
    (fun _ => hf.integrableOn)]
  exact (integral_eq_setIntegral (ae_mem_iUnion_nodeEvent 𝒯 ξ P hA hlo ht) f).symm

end S04P082

/- Inlined from Solutions.P082Average. -/
namespace S04P082

open MeasureTheory KallMayerSLP.Multistage
open scoped Matrix

variable {Ω E F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def avgOn (P : Measure Ω) (s : Set Ω) (f : Ω → E) : E :=
  (P.real s)⁻¹ • ∫ ω in s, f ω ∂P

theorem avgOn_congr_ae {P : Measure Ω} {s : Set Ω} {f g : Ω → E}
    (h : f =ᵐ[P.restrict s] g) : avgOn P s f = avgOn P s g := by
  unfold avgOn
  rw [integral_congr_ae h]

theorem avgOn_of_scaling {P : Measure Ω} {s t : Set Ω} {f : Ω → E} {r : ℝ}
    (hm : P.real t = r * P.real s)
    (hi : (∫ ω in t, f ω ∂P) = r • ∫ ω in s, f ω ∂P)
    (ht : P.real t ≠ 0) : avgOn P t f = avgOn P s f := by
  have hr : r ≠ 0 := by
    intro h
    exact ht (by simp [hm, h])
  simp only [avgOn, hm, hi, smul_smul, mul_inv_rev, mul_assoc, inv_mul_cancel₀ hr,
    mul_one]

theorem avgOn_linear [CompleteSpace E] [CompleteSpace F] (L : E →L[ℝ] F)
    {P : Measure Ω} {s : Set Ω} {f : Ω → E} (hf : Integrable f P) :
    avgOn P s (fun ω => L (f ω)) = L (avgOn P s f) := by
  unfold avgOn
  rw [L.integral_comp_comm hf.integrableOn, L.map_smul]

theorem avgOn_sum {ι : Type*} (a : Finset ι) {P : Measure Ω} {s : Set Ω}
    {f : ι → Ω → E} (hf : ∀ i ∈ a, Integrable (f i) P) :
    avgOn P s (fun ω => ∑ i ∈ a, f i ω) = ∑ i ∈ a, avgOn P s (f i) := by
  unfold avgOn
  rw [integral_finsetSum a (fun i hi => (hf i hi).integrableOn), Finset.smul_sum]

theorem avgOn_eval {ι : Type*} [Fintype ι] {G : ι → Type*}
    [∀ i, NormedAddCommGroup (G i)] [∀ i, NormedSpace ℝ (G i)]
    [∀ i, CompleteSpace (G i)] {P : Measure Ω} {s : Set Ω}
    {f : Ω → ∀ i, G i} (hf : Integrable f P) (i : ι) :
    (avgOn P s f) i = avgOn P s (fun ω => f ω i) := by
  unfold avgOn
  rw [Pi.smul_apply, eval_integral (fun j => (hf.eval j).integrableOn)]

theorem avgOn_const [CompleteSpace E] {P : Measure Ω} [IsFiniteMeasure P]
    {s : Set Ω} (hs : P.real s ≠ 0) (v : E) :
    avgOn P s (fun _ => v) = v := by
  simp [avgOn, integral_const, smul_smul, hs]

theorem integral_affine [CompleteSpace E] [CompleteSpace F] [FiniteDimensional ℝ E]
    {P : Measure Ω} [IsFiniteMeasure P] {s : Set Ω} (b : E →ᵃ[ℝ] F)
    {f : Ω → E} (hf : Integrable f P) :
    (∫ ω in s, b (f ω) ∂P) =
      b.linear (∫ ω in s, f ω ∂P) + (P.real s) • b 0 := by
  let L : E →L[ℝ] F := ⟨b.linear, b.linear.continuous_of_finiteDimensional⟩
  have hb (v : E) : b v = L v + b 0 := by
    simpa [L] using congrFun b.decomp v
  calc
    _ = ∫ ω in s, L (f ω) + b 0 ∂P :=
      integral_congr_ae (Filter.Eventually.of_forall (fun ω => hb (f ω)))
    _ = L (∫ ω in s, f ω ∂P) + (P.real s) • b 0 := by
      rw [integral_add (L.integrable_comp hf.integrableOn) (integrable_const _),
        L.integral_comp_comm hf.integrableOn]
      simp [integral_const, measureReal_def]
    _ = _ := rfl

theorem avgOn_affine [CompleteSpace E] [CompleteSpace F] [FiniteDimensional ℝ E]
    {P : Measure Ω} [IsFiniteMeasure P] {s : Set Ω} (b : E →ᵃ[ℝ] F)
    {f : Ω → E} (hf : Integrable f P) (hs : P.real s ≠ 0) :
    avgOn P s (fun ω => b (f ω)) = b (avgOn P s f) := by
  rw [avgOn, integral_affine b hf, smul_add, smul_smul, inv_mul_cancel₀ hs, one_smul]
  have hb (v : E) : b v = b.linear v + b 0 := by
    simpa using congrFun b.decomp v
  rw [← b.linear.map_smul]
  exact (hb _).symm

theorem integrable_mulVec {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    {P : Measure Ω} {f : Ω → Fin n → ℝ} (hf : Integrable f P) :
    Integrable (fun ω => A *ᵥ f ω) P := by
  let L : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ) :=
    ⟨A.mulVecLin, A.mulVecLin.continuous_of_finiteDimensional⟩
  exact L.integrable_comp hf

theorem avgOn_mulVec {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    {P : Measure Ω} {s : Set Ω} {f : Ω → Fin n → ℝ} (hf : Integrable f P) :
    avgOn P s (fun ω => A *ᵥ f ω) = A *ᵥ avgOn P s f := by
  let L : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ) :=
    ⟨A.mulVecLin, A.mulVecLin.continuous_of_finiteDimensional⟩
  exact avgOn_linear L hf

theorem integrable_dotProduct {n : ℕ} (c : Fin n → ℝ)
    {P : Measure Ω} {f : Ω → Fin n → ℝ} (hf : Integrable f P) :
    Integrable (fun ω => c ⬝ᵥ f ω) P := by
  unfold dotProduct
  exact integrable_finsetSum _ (fun i _ => (hf.eval i).const_mul (c i))

theorem avgOn_dotProduct {n : ℕ} (c : Fin n → ℝ)
    {P : Measure Ω} {s : Set Ω} {f : Ω → Fin n → ℝ} (hf : Integrable f P) :
    avgOn P s (fun ω => c ⬝ᵥ f ω) = c ⬝ᵥ avgOn P s f := by
  unfold dotProduct avgOn
  rw [integral_finsetSum _ (fun i _ => ((hf.eval i).const_mul (c i)).integrableOn)]
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_const_mul, eval_integral (fun i => (hf.eval i).integrableOn)]
  ring

theorem mass_mul_avgOn_dotProduct {n : ℕ} (c : Fin n → ℝ)
    {P : Measure Ω} [IsFiniteMeasure P] {s : Set Ω} {f : Ω → Fin n → ℝ}
    (hf : Integrable f P) :
    P.real s * (c ⬝ᵥ avgOn P s f) = ∫ ω in s, c ⬝ᵥ f ω ∂P := by
  by_cases hs : P.real s = 0
  · have hs0 : P s = 0 := (measureReal_eq_zero_iff (by finiteness)).mp hs
    simp [hs, Measure.restrict_eq_zero.mpr hs0]
  · rw [← avgOn_dotProduct c hf, avgOn, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hs,
      one_mul]

theorem avgOn_nonneg {n : ℕ} {P : Measure Ω} {s : Set Ω}
    {f : Ω → Fin n → ℝ} (hf : Integrable f P) (hn : ∀ᵐ ω ∂P, 0 ≤ f ω) :
    0 ≤ avgOn P s f := by
  intro i
  change 0 ≤ (P.real s)⁻¹ * (∫ ω in s, f ω ∂P) i
  rw [eval_integral (fun j => (hf.eval j).integrableOn)]
  exact mul_nonneg (inv_nonneg.mpr (measureReal_nonneg))
    (integral_nonneg_of_ae ((ae_restrict_of_ae hn).mono (fun ω h => h i)))

variable {D : MSLP} {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ∀ t, Ω → Fin (D.r t) → ℝ} {Ξ : ∀ t, Set (Fin (D.r t) → ℝ)}
    {x : ∀ t, Hist D.r t → Fin (D.n t) → ℝ}

theorem policy_integrable (hx : IsFeasiblePolicy D P ξ x) {t : ℕ}
    (ht1 : 1 ≤ t) (htT : t ≤ D.T) :
    Integrable (fun ω => x t (zeta ξ t ω)) P :=
  MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2) (hx.memLp t ht1 htT)

theorem xi_integrable (hA : Assumption32 D P ξ Ξ) {t : ℕ}
    (ht2 : 2 ≤ t) (htT : t ≤ D.T) : Integrable (ξ t) P := by
  obtain ⟨C, hC⟩ := (hA.isBounded t ht2 htT).exists_norm_le
  exact Integrable.of_bound (hA.measurable_xi t ht2 htT).aestronglyMeasurable C
    ((hA.ae_mem t ht2 htT).mono (fun ω hω => hC _ hω))

theorem zeta_integrable (hA : Assumption32 D P ξ Ξ) {t : ℕ}
    (htT : t ≤ D.T) : Integrable (zeta ξ t) P := by
  exact Integrable.of_eval (fun s : Set.Icc 2 t =>
    xi_integrable hA s.2.1 (s.2.2.trans htT))

theorem averaged_constraint (hA : Assumption32 D P ξ Ξ)
    (hx : IsFeasiblePolicy D P ξ x) {t : ℕ} (ht1 : 1 ≤ t) (htT : t ≤ D.T)
    {s : Set Ω} (hs : P.real s ≠ 0)
    (v : ∀ τ : Set.Icc 1 t, Fin (D.n τ) → ℝ) (z : Hist D.r t)
    (hv : ∀ τ : Set.Icc 1 t,
      avgOn P s (fun ω => x τ (zeta ξ τ ω)) = v τ)
    (hz : avgOn P s (zeta ξ t) = z) :
    ∑ τ : Set.Icc 1 t, D.A t τ *ᵥ v τ = D.b t z := by
  have hsum : ∀ ω, (∑ τ ∈ Finset.Icc 1 t, D.A t τ *ᵥ x τ (zeta ξ τ ω)) =
      ∑ τ : Set.Icc 1 t, D.A t τ *ᵥ x τ (zeta ξ τ ω) := by
    intro ω
    exact Finset.sum_subtype (Finset.Icc 1 t) (fun i => Finset.mem_Icc) _
  have hc : (fun ω => ∑ τ : Set.Icc 1 t, D.A t τ *ᵥ x τ (zeta ξ τ ω))
      =ᵐ[P.restrict s] (fun ω => D.b t (zeta ξ t ω)) := by
    filter_upwards [ae_restrict_of_ae (hx.constraint t ht1 htT)] with ω hω
    rwa [hsum ω] at hω
  have hi (τ : Set.Icc 1 t) := policy_integrable hx τ.2.1 (τ.2.2.trans htT)
  have ha := avgOn_congr_ae hc
  rw [avgOn_sum (Finset.univ : Finset (Set.Icc 1 t))
      (fun (τ : Set.Icc 1 t) _ => integrable_mulVec (D.A t τ) (hi τ)),
    avgOn_affine (D.b t) (zeta_integrable hA htT) hs, hz] at ha
  simpa only [avgOn_mulVec _ (hi _), hv] using ha

end S04P082

/- Inlined from Solutions.P082History. -/
namespace S04P082

open MeasureTheory ProbabilityTheory KallMayerSLP.Multistage

variable {D : MSLP} {Ξ : ∀ t, Set (Fin (D.r t) → ℝ)}
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ξ : ∀ t, Ω → Fin (D.r t) → ℝ)
    (hA : Assumption32 D P ξ Ξ)

include hA

theorem measurable_zeta {t : ℕ} (ht : t ≤ D.T) : Measurable (zeta ξ t) := by
  exact measurable_pi_lambda _ (fun s => hA.measurable_xi s s.2.1 (s.2.2.trans ht))

/-- Any two finite subfamilies with disjoint stage ranges are independent.
The maps need not be injective within either subfamily. -/
theorem indep_finite_subfamilies {I J : Type*} [Fintype I] [Fintype J]
    (e : I → Set.Icc 2 D.T) (f : J → Set.Icc 2 D.T)
    (hdisj : ∀ i j, e i ≠ f j) :
    IndepFun (fun ω i => ξ (e i) ω) (fun ω j => ξ (f j) ω) P := by
  classical
  let S : Finset (Set.Icc 2 D.T) := Finset.univ.image e
  let T : Finset (Set.Icc 2 D.T) := Finset.univ.image f
  have hd : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro k hkS hkT
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hkS
    obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hkT
    exact hdisj i j heq.symm
  have h := hA.indep.indepFun_finset S T hd
    (fun k => hA.measurable_xi k k.2.1 k.2.2)
  let ei (i : I) : S := ⟨e i, Finset.mem_image_of_mem e (Finset.mem_univ i)⟩
  let fj (j : J) : T := ⟨f j, Finset.mem_image_of_mem f (Finset.mem_univ j)⟩
  have he : Measurable (fun x : (∀ k : S, Fin (D.r k) → ℝ) => fun i => x (ei i)) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply (ei i))
  have hf : Measurable (fun x : (∀ k : T, Fin (D.r k) → ℝ) => fun j => x (fj j)) :=
    measurable_pi_lambda _ (fun j => measurable_pi_apply (fj j))
  exact h.comp he hf

theorem indep_zeta_next {t : ℕ} (hlo : 1 ≤ t) (ht : t + 1 ≤ D.T) :
    IndepFun (zeta ξ t) (ξ (t + 1)) P := by
  classical
  let e : Set.Icc 2 t → Set.Icc 2 D.T :=
    fun s => ⟨s.1, s.2.1, s.2.2.trans (Nat.le_succ t) |>.trans ht⟩
  let f : Unit → Set.Icc 2 D.T := fun _ => ⟨t + 1, by omega, ht⟩
  have h := indep_finite_subfamilies P ξ hA e f (by
    intro s u heq
    have hv := congrArg Subtype.val heq
    have hs := s.2.2
    dsimp [e, f] at hv
    omega)
  exact h.comp measurable_id (measurable_pi_apply ())

abbrev SuffixHist (r : ℕ → ℕ) (s t : ℕ) : Type := ∀ u : Set.Ioc s t, Fin (r u) → ℝ

def suffixZeta (s t : ℕ) (ω : Ω) : SuffixHist D.r s t := fun u => ξ u ω

theorem measurable_suffixZeta {s t : ℕ} (hs : 1 ≤ s) (ht : t ≤ D.T) :
    Measurable (suffixZeta ξ s t) := by
  exact measurable_pi_lambda _ (fun u => hA.measurable_xi u (by have := u.2.1; omega)
    (u.2.2.trans ht))

theorem indep_zeta_suffix {s t : ℕ} (hs : 1 ≤ s) (hst : s ≤ t) (ht : t ≤ D.T) :
    IndepFun (zeta ξ s) (suffixZeta ξ s t) P := by
  let e : Set.Icc 2 s → Set.Icc 2 D.T :=
    fun u => ⟨u.1, u.2.1, u.2.2.trans (hst.trans ht)⟩
  let f : Set.Ioc s t → Set.Icc 2 D.T :=
    fun u => ⟨u.1, by have := u.2.1; omega, u.2.2.trans ht⟩
  exact indep_finite_subfamilies P ξ hA e f (by
    intro u v heq
    have hv := congrArg Subtype.val heq
    have hu := u.2.2
    have hvs := v.2.1
    dsimp [e, f] at hv
    omega)

abbrev OtherHist (r : ℕ → ℕ) (s t : ℕ) : Type :=
  ∀ u : {u : Set.Icc 2 t // (u : ℕ) ≠ s}, Fin (r u.1) → ℝ

def otherZeta (s t : ℕ) (ω : Ω) : OtherHist D.r s t := fun u => ξ u.1 ω

theorem measurable_otherZeta {s t : ℕ} (ht : t ≤ D.T) :
    Measurable (otherZeta ξ s t) := by
  exact measurable_pi_lambda _ (fun u => hA.measurable_xi u.1 u.1.2.1 (u.1.2.2.trans ht))

theorem indep_xi_other {s t : ℕ} (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ D.T) :
    IndepFun (ξ s) (otherZeta ξ s t) P := by
  classical
  let e : Unit → Set.Icc 2 D.T := fun _ => ⟨s, hs, hst.trans ht⟩
  let f : {u : Set.Icc 2 t // (u : ℕ) ≠ s} → Set.Icc 2 D.T :=
    fun u => ⟨u.1.1, u.1.2.1, u.1.2.2.trans ht⟩
  have h := indep_finite_subfamilies P ξ hA e f (by
    intro u v heq
    exact v.2 (congrArg Subtype.val heq).symm)
  exact h.comp (measurable_pi_apply ()) measurable_id

omit hA

variable (𝒯 : ScenarioTree D Ξ)

def historyCell {t : ℕ} (n : 𝒯.Node t) : Set (Hist D.r t) :=
  {x | ∀ u : Set.Icc 2 t, x u ∈ 𝒯.cell u (𝒯.anc u.2.2 n)}

theorem measurableSet_historyCell {t : ℕ} (ht : t ≤ D.T) (n : 𝒯.Node t) :
    MeasurableSet (historyCell 𝒯 n) := by
  simp only [historyCell, Set.setOf_forall]
  exact MeasurableSet.iInter (fun u =>
    (interval_measurable (𝒯.isInterval_cell u u.2.1 (u.2.2.trans ht) _)).preimage
      (measurable_pi_apply u))

theorem nodeEvent_eq_preimage_historyCell {t : ℕ} (n : 𝒯.Node t) :
    nodeEvent 𝒯 ξ n = zeta ξ t ⁻¹' historyCell 𝒯 n := rfl

def suffixCell {s t : ℕ} (n : 𝒯.Node t) : Set (SuffixHist D.r s t) :=
  {x | ∀ u : Set.Ioc s t, x u ∈ 𝒯.cell u (𝒯.anc u.2.2 n)}

theorem measurableSet_suffixCell {s t : ℕ} (hs : 1 ≤ s) (ht : t ≤ D.T)
    (n : 𝒯.Node t) : MeasurableSet (suffixCell (s := s) 𝒯 n) := by
  simp only [suffixCell, Set.setOf_forall]
  exact MeasurableSet.iInter (fun u =>
    (interval_measurable (𝒯.isInterval_cell u (by have := u.2.1; omega)
      (u.2.2.trans ht) _)).preimage (measurable_pi_apply u))

theorem nodeEvent_eq_prefix_inter_suffix {s t : ℕ} (hs : 1 ≤ s) (hst : s ≤ t)
    (n : 𝒯.Node t) :
    nodeEvent 𝒯 ξ n = nodeEvent 𝒯 ξ (𝒯.anc hst n) ∩
      (suffixZeta ξ s t ⁻¹' suffixCell 𝒯 n) := by
  ext ω
  constructor
  · intro hω
    constructor
    · intro u
      have h := hω ⟨u.1, u.2.1, u.2.2.trans hst⟩
      change ξ u.1 ω ∈ 𝒯.cell u.1 (𝒯.anc u.2.2 (𝒯.anc hst n))
      rw [anc_trans]
      exact h
    · intro u
      exact hω ⟨u.1, by have := u.2.1; omega, u.2.2⟩
  · rintro ⟨hpre, hsuf⟩ u
    by_cases hu : (u : ℕ) ≤ s
    · have h := hpre ⟨u.1, u.2.1, hu⟩
      change ξ u.1 ω ∈ 𝒯.cell u.1 (𝒯.anc hu (𝒯.anc hst n)) at h
      rwa [anc_trans] at h
    · exact hsuf ⟨u.1, Nat.lt_of_not_ge hu, u.2.2⟩

def otherCell {s t : ℕ} (n : 𝒯.Node t) : Set (OtherHist D.r s t) :=
  {x | ∀ u : {u : Set.Icc 2 t // (u : ℕ) ≠ s},
    x u ∈ 𝒯.cell u.1 (𝒯.anc u.1.2.2 n)}

theorem measurableSet_otherCell {s t : ℕ} (ht : t ≤ D.T) (n : 𝒯.Node t) :
    MeasurableSet (otherCell (s := s) 𝒯 n) := by
  simp only [otherCell, Set.setOf_forall]
  exact MeasurableSet.iInter (fun u =>
    (interval_measurable (𝒯.isInterval_cell u.1 u.1.2.1 (u.1.2.2.trans ht) _)).preimage
      (measurable_pi_apply u))

theorem nodeEvent_eq_coordinate_inter_other {s t : ℕ} (hs : 2 ≤ s) (hst : s ≤ t)
    (n : 𝒯.Node t) :
    nodeEvent 𝒯 ξ n = (ξ s ⁻¹' 𝒯.cell s (𝒯.anc hst n)) ∩
      (otherZeta ξ s t ⁻¹' otherCell 𝒯 n) := by
  ext ω
  constructor
  · intro hω
    exact ⟨hω ⟨s, hs, hst⟩, fun u => hω u.1⟩
  · rintro ⟨hcoord, hother⟩ u
    by_cases hu : (u : ℕ) = s
    · obtain rfl := hu
      exact hcoord
    · exact hother ⟨u, hu⟩

end S04P082

/- Inlined from Solutions.P082Indep. -/
namespace S04P082

open MeasureTheory ProbabilityTheory

variable {Ω A B E : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → A} {Y : Ω → B}

theorem independent_setIntegral (hi : IndepFun X Y P)
    (hX : Measurable X) (hY : Measurable Y)
    {U : Set A} {V : Set B} (hU : MeasurableSet U) (hV : MeasurableSet V)
    {f : A → E} (hf : Measurable f) :
    (∫ ω in X ⁻¹' U ∩ Y ⁻¹' V, f (X ω) ∂P) =
      P.real (Y ⁻¹' V) • ∫ ω in X ⁻¹' U, f (X ω) ∂P := by
  have h := hi.symm.integral_fun_comp_smul_comp hY.aemeasurable hX.aemeasurable
    ((measurable_const.indicator hV).aestronglyMeasurable :
      AEStronglyMeasurable (V.indicator (fun _ => (1 : ℝ))) (P.map Y))
    ((hf.indicator hU).aestronglyMeasurable :
      AEStronglyMeasurable (U.indicator f) (P.map X))
  have hv : (fun ω => V.indicator (fun _ => (1 : ℝ)) (Y ω)) =
      (Y ⁻¹' V).indicator (fun _ => (1 : ℝ)) := by
    ext ω
    rfl
  have hu : (fun ω => U.indicator f (X ω)) =
      (X ⁻¹' U).indicator (fun ω => f (X ω)) := by
    ext ω
    rfl
  have huv : (fun ω => V.indicator (fun _ => (1 : ℝ)) (Y ω) • U.indicator f (X ω)) =
      (X ⁻¹' U ∩ Y ⁻¹' V).indicator (fun ω => f (X ω)) := by
    ext ω
    by_cases hu : X ω ∈ U <;> by_cases hv : Y ω ∈ V <;>
      simp [Set.indicator_apply, hu, hv]
  rw [huv, hv, hu, integral_indicator ((hU.preimage hX).inter (hV.preimage hY)),
    integral_indicator (hV.preimage hY), setIntegral_const,
    integral_indicator (hU.preimage hX)] at h
  simpa only [smul_eq_mul, mul_one] using h

theorem independent_avgOn (hi : IndepFun X Y P)
    (hX : Measurable X) (hY : Measurable Y)
    {U : Set A} {V : Set B} (hU : MeasurableSet U) (hV : MeasurableSet V)
    {f : A → E} (hf : Measurable f)
    (hn : P.real (X ⁻¹' U ∩ Y ⁻¹' V) ≠ 0) :
    avgOn P (X ⁻¹' U ∩ Y ⁻¹' V) (fun ω => f (X ω)) =
      avgOn P (X ⁻¹' U) (fun ω => f (X ω)) := by
  have hm : P.real (X ⁻¹' U ∩ Y ⁻¹' V) =
      P.real (X ⁻¹' U) * P.real (Y ⁻¹' V) := by
    simpa only [Measure.real, ENNReal.toReal_mul] using
      congrArg ENNReal.toReal (hi.measure_inter_preimage_eq_mul U V hU hV)
  have hb : P.real (Y ⁻¹' V) ≠ 0 := by
    intro hb
    exact hn (by rw [hm, hb, mul_zero])
  unfold avgOn
  rw [independent_setIntegral hi hX hY hU hV hf, hm, smul_smul]
  congr 1
  simp [mul_inv_rev, mul_assoc, mul_left_comm, mul_comm, hb]

end S04P082

/- Inlined from Solutions.P082Objective. -/
namespace S04P082

open MeasureTheory KallMayerSLP.Multistage
open scoped Matrix

variable {D : MSLP} {Ξ : ∀ t, Set (Fin (D.r t) → ℝ)}
    (𝒯 : ScenarioTree D Ξ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ξ : ∀ t, Ω → Fin (D.r t) → ℝ)

noncomputable def nodeAveragePolicy
    (x : ∀ t, Hist D.r t → Fin (D.n t) → ℝ) (t : ℕ) (n : 𝒯.Node t) :
    Fin (D.n t) → ℝ :=
  avgOn P (nodeEvent 𝒯 ξ n) (fun ω => x t (zeta ξ t ω))

theorem aggObjective_nodeAveragePolicy [IsProbabilityMeasure P]
    (hA : Assumption32 D P ξ Ξ)
    {x : ∀ t, Hist D.r t → Fin (D.n t) → ℝ} (hx : IsFeasiblePolicy D P ξ x) :
    aggObjective 𝒯 P ξ (nodeAveragePolicy 𝒯 P ξ x) = objective D P ξ x := by
  classical
  unfold aggObjective objective
  apply Finset.sum_congr rfl
  intro t ht
  have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
  have htT : t ≤ D.T := (Finset.mem_Icc.mp ht).2
  have hxt := policy_integrable hx ht1 htT
  calc
    ∑ n : 𝒯.Node t, nodeProb 𝒯 P ξ n *
        (D.c t ⬝ᵥ nodeAveragePolicy 𝒯 P ξ x t n) =
        ∑ n : 𝒯.Node t, ∫ ω in nodeEvent 𝒯 ξ n, D.c t ⬝ᵥ x t (zeta ξ t ω) ∂P := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [← real_nodeEvent 𝒯 ξ P hA htT n]
      exact mass_mul_avgOn_dotProduct (D.c t) hxt
    _ = _ := integral_partition_nodeEvent 𝒯 ξ P hA ht1 htT
      (integrable_dotProduct (D.c t) hxt)


theorem aggValue_le_objective_of_averages [IsProbabilityMeasure P]
    (hA : Assumption32 D P ξ Ξ)
    {x : ∀ t, Hist D.r t → Fin (D.n t) → ℝ} (hx : IsFeasiblePolicy D P ξ x)
    (hanc : ∀ t, 1 ≤ t → t ≤ D.T → ∀ n : 𝒯.Node t, nodeProb 𝒯 P ξ n ≠ 0 →
      ∀ τ : Set.Icc 1 t,
        avgOn P (nodeEvent 𝒯 ξ n) (fun ω => x τ (zeta ξ τ ω)) =
          nodeAveragePolicy 𝒯 P ξ x τ (𝒯.anc τ.2.2 n))
    (hz : ∀ t, 1 ≤ t → t ≤ D.T → ∀ n : 𝒯.Node t, nodeProb 𝒯 P ξ n ≠ 0 →
      avgOn P (nodeEvent 𝒯 ξ n) (zeta ξ t) = zetaHat 𝒯 P ξ n) :
    aggValue 𝒯 P ξ ≤ ((objective D P ξ x : ℝ) : EReal) := by
  classical
  let Y := nodeAveragePolicy 𝒯 P ξ x
  have hY : ∀ t, 1 ≤ t → t ≤ D.T → ∀ n : 𝒯.Node t, nodeProb 𝒯 P ξ n ≠ 0 →
      (∑ τ : Set.Icc 1 t, D.A t τ *ᵥ Y τ (𝒯.anc τ.2.2 n) =
        D.b t (zetaHat 𝒯 P ξ n)) ∧ 0 ≤ Y t n := by
    intro t ht1 htT n hn
    constructor
    · exact averaged_constraint hA hx ht1 htT
        (by rwa [real_nodeEvent 𝒯 ξ P hA htT n])
        (fun τ => Y τ (𝒯.anc τ.2.2 n)) (zetaHat 𝒯 P ξ n)
        (hanc t ht1 htT n hn) (hz t ht1 htT n hn)
    · exact avgOn_nonneg (policy_integrable hx ht1 htT) (hx.nonneg t ht1 htT)
  let X := nullFill 𝒯 P ξ Y hA.complete
  have hX : IsAggFeasible 𝒯 P ξ X := nullFill_isAggFeasible 𝒯 P ξ Y hA.complete hY
  have ho : aggObjective 𝒯 P ξ X = objective D P ξ x := by
    exact (nullFill_aggObjective 𝒯 P ξ Y hA.complete).trans
      (aggObjective_nodeAveragePolicy 𝒯 P ξ hA hx)
  unfold aggValue
  exact iInf_le_of_le X (iInf_le_of_le hX (by rw [ho]))

theorem aggValue_le_value_of_averages [IsProbabilityMeasure P]
    (hA : Assumption32 D P ξ Ξ)
    (hanc : ∀ (x : ∀ t, Hist D.r t → Fin (D.n t) → ℝ), IsFeasiblePolicy D P ξ x →
      ∀ t, 1 ≤ t → t ≤ D.T → ∀ n : 𝒯.Node t, nodeProb 𝒯 P ξ n ≠ 0 →
      ∀ τ : Set.Icc 1 t,
        avgOn P (nodeEvent 𝒯 ξ n) (fun ω => x τ (zeta ξ τ ω)) =
          nodeAveragePolicy 𝒯 P ξ x τ (𝒯.anc τ.2.2 n))
    (hz : ∀ t, 1 ≤ t → t ≤ D.T → ∀ n : 𝒯.Node t, nodeProb 𝒯 P ξ n ≠ 0 →
      avgOn P (nodeEvent 𝒯 ξ n) (zeta ξ t) = zetaHat 𝒯 P ξ n) :
    aggValue 𝒯 P ξ ≤ value D P ξ := by
  unfold value
  exact le_iInf (fun x => le_iInf (fun hx =>
    aggValue_le_objective_of_averages 𝒯 P ξ hA hx (hanc x hx) hz))

end S04P082

/- Inlined from Solutions.P082Ancestor. -/
namespace S04P082

open MeasureTheory ProbabilityTheory KallMayerSLP.Multistage

variable {D : MSLP} {Ξ : ∀ t, Set (Fin (D.r t) → ℝ)}
    (𝒯 : ScenarioTree D Ξ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ∀ t, Ω → Fin (D.r t) → ℝ) (hA : Assumption32 D P ξ Ξ)

include hA

/-- Conditioning a measurable function of a prefix history on any positive descendant
event gives the same average as conditioning on that prefix node event. -/
theorem avgOn_nodeEvent_ancestor
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {s t : ℕ} (hs : 1 ≤ s) (hst : s ≤ t) (ht : t ≤ D.T) (n : 𝒯.Node t)
    (hn : nodeProb 𝒯 P ξ n ≠ 0)
    {f : Hist D.r s → E} (hf : Measurable f) :
    avgOn P (nodeEvent 𝒯 ξ n) (fun ω => f (zeta ξ s ω)) =
      avgOn P (nodeEvent 𝒯 ξ (𝒯.anc hst n)) (fun ω => f (zeta ξ s ω)) := by
  have hsplit : nodeEvent 𝒯 ξ n =
      (zeta ξ s ⁻¹' historyCell 𝒯 (𝒯.anc hst n)) ∩
      (suffixZeta ξ s t ⁻¹' suffixCell 𝒯 n) := by
    rw [nodeEvent_eq_prefix_inter_suffix (𝒯 := 𝒯) (ξ := ξ) hs hst n,
      nodeEvent_eq_preimage_historyCell]
  rw [hsplit, nodeEvent_eq_preimage_historyCell]
  exact independent_avgOn (indep_zeta_suffix P ξ hA hs hst ht)
    (measurable_zeta P ξ hA (hst.trans ht))
    (measurable_suffixZeta P ξ hA hs ht)
    (measurableSet_historyCell 𝒯 (hst.trans ht) _)
    (measurableSet_suffixCell 𝒯 hs ht n) hf
    (by rw [← hsplit, real_nodeEvent 𝒯 ξ P hA ht n]; exact hn)

theorem avgOn_policy_ancestor
    {x : ∀ t, Hist D.r t → Fin (D.n t) → ℝ} (hx : IsFeasiblePolicy D P ξ x)
    {s t : ℕ} (hs : 1 ≤ s) (hst : s ≤ t) (ht : t ≤ D.T) (n : 𝒯.Node t)
    (hn : nodeProb 𝒯 P ξ n ≠ 0) :
    avgOn P (nodeEvent 𝒯 ξ n) (fun ω => x s (zeta ξ s ω)) =
      avgOn P (nodeEvent 𝒯 ξ (𝒯.anc hst n)) (fun ω => x s (zeta ξ s ω)) :=
  avgOn_nodeEvent_ancestor 𝒯 P ξ hA hs hst ht n hn (hx.measurable s hs (hst.trans ht))

end S04P082

/- Inlined from Solutions.P082Means. -/
namespace S04P082

open MeasureTheory ProbabilityTheory KallMayerSLP.Multistage

variable {D : MSLP} {Ξ : ∀ t, Set (Fin (D.r t) → ℝ)}
    (𝒯 : ScenarioTree D Ξ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ∀ t, Ω → Fin (D.r t) → ℝ) (hA : Assumption32 D P ξ Ξ)

include hA

theorem avgOn_xi_nodeEvent {t : ℕ} (ht : t ≤ D.T) (n : 𝒯.Node t)
    (hn : nodeProb 𝒯 P ξ n ≠ 0) (s : Set.Icc 2 t) :
    avgOn P (nodeEvent 𝒯 ξ n) (ξ s) = xiBar 𝒯 P ξ s (𝒯.anc s.2.2 n) := by
  have he := nodeEvent_eq_coordinate_inter_other (ξ := ξ) (𝒯 := 𝒯) s.2.1 s.2.2 n
  have hp : P.real (nodeEvent 𝒯 ξ n) ≠ 0 := by
    rwa [real_nodeEvent 𝒯 ξ P hA ht n]
  have h := independent_avgOn (indep_xi_other P ξ hA s.2.1 s.2.2 ht)
    (hA.measurable_xi s s.2.1 (s.2.2.trans ht))
    (measurable_otherZeta P ξ hA ht)
    (interval_measurable (𝒯.isInterval_cell s s.2.1 (s.2.2.trans ht) _))
    (measurableSet_otherCell (𝒯 := 𝒯) ht n)
    (measurable_id : Measurable (fun v : Fin (D.r s) → ℝ => v))
    (by rw [← he]; exact hp)
  change avgOn P (nodeEvent 𝒯 ξ n) (ξ s) =
    avgOn P (ξ s ⁻¹' 𝒯.cell s (𝒯.anc s.2.2 n)) (ξ s)
  rw [he]
  exact h

theorem averaged_zeta {t : ℕ} (ht : t ≤ D.T) (n : 𝒯.Node t)
    (hn : nodeProb 𝒯 P ξ n ≠ 0) :
    avgOn P (nodeEvent 𝒯 ξ n) (zeta ξ t) = zetaHat 𝒯 P ξ n := by
  funext s
  rw [avgOn_eval (zeta_integrable hA ht) s]
  exact avgOn_xi_nodeEvent 𝒯 P ξ hA ht n hn s

end S04P082

/- Inlined from Solutions.P082. -/
open KallMayerSLP.Multistage

open MeasureTheory

theorem solution {D : MSLP} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ξ : ∀ t, Ω → Fin (D.r t) → ℝ} {Ξ : ∀ t, Set (Fin (D.r t) → ℝ)}
    (hA : Assumption32 D P ξ Ξ) (𝒯 : ScenarioTree D Ξ) :
    aggValue 𝒯 P ξ ≤ value D P ξ := by
  apply S04P082.aggValue_le_value_of_averages 𝒯 P ξ hA
  · intro x hx t ht1 htT n hn τ
    exact S04P082.avgOn_policy_ancestor 𝒯 P ξ hA hx τ.2.1 τ.2.2 htT n hn
  · intro t ht1 htT n hn
    exact S04P082.averaged_zeta 𝒯 P ξ hA htT n hn

#print axioms solution
