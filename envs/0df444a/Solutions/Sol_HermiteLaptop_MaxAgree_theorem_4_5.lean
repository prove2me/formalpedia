-- Prove2me | solution 1 for HermiteLaptop.MaxAgree.theorem_4_5
-- status  : ACCEPTED   (prove)
-- author  : @hypercube
-- created : 2026-11-18T14:14:18.743197+00:00
-- url     : https://prove2.me/submissions/3332077c-0c00-49ba-aba9-dd8ee2497aef

import Theorems.Thm_HermiteLaptop_MaxAgree_lemma_4_1
import Theorems.Thm_HermiteLaptop_MaxAgree_proposition_2_4
import Theorems.Thm_HermiteLaptop_MaxAgree_proposition_4_4
import Theorems.Thm_HermiteLaptop_MaxAgree_negative_edge_equality


open scoped RealInnerProductSpace
namespace HermiteLaptop.MaxAgree

private theorem sdpRelaxationBridge {n : ℕ} (I : Instance n)
    (v : Fin n → EuclideanSpace ℝ (Fin n)) (hv : I.SDPOptimal 0 v) (C : Fin n → ℕ) :
    I.val C ≤ I.sdpObj 0 v := by
  classical
  let rep (c : Set.range C) : Fin n := c.property.choose
  let r (i : Fin n) := rep ⟨C i, i, rfl⟩
  have hr (i j : Fin n) : r i = r j ↔ C i = C j := by
    constructor
    · intro h
      have hrep (k : Fin n) : C (r k) = C k :=
        (show ∃ t, C t = C k from ⟨k, rfl⟩).choose_spec
      exact (hrep i).symm.trans ((congrArg C h).trans (hrep j))
    · intro h
      exact congrArg rep (Subtype.ext h)
  let u (i : Fin n) : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single (r i) 1
  have hu (i j : Fin n) : ⟪u i, u j⟫ = if C i = C j then 1 else 0 := by
    simp [u, EuclideanSpace.inner_single_left, PiLp.single_apply, hr]
  have hf : SDPFeasible 0 u := by
    refine ⟨fun i => by exact (hu i i).trans (if_pos rfl), fun i j => ?_⟩
    rw [hu]
    split <;> norm_num
  have hEdge : edgeInner u = sameInd C := by
    funext e
    induction e using Sym2.inductionOn with
    | _ i j => exact hu i j
  simpa [Instance.sdpObj, Instance.val, sPlus, sMinus, hEdge] using hv.2 u hf

end HermiteLaptop.MaxAgree

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace HermiteLaptop.MaxAgree

private theorem spokeIndex_measurable {k : ℕ} : Measurable (spokeIndex (k := k)) := by
  classical
  unfold spokeIndex
  generalize List.finRange k = l
  induction l with
  | nil => exact measurable_const
  | cons p l ih =>
    have h : MeasurableSet {x : Fin k → ℝ | ∀ q, x q ≤ x p} := by
      rw [Set.ofPred_forall]
      exact MeasurableSet.iInter (fun q => measurableSet_le (measurable_pi_apply q) (measurable_pi_apply p))
    simp only [List.find?_cons]
    convert Measurable.ite h (measurable_const (a := p.val)) ih using 1
    ext x
    by_cases hmax : ∀ q, x q ≤ x p <;> simp [hmax]
    all_goals exact fun _ => Classical.propDecidable _

private theorem kSpokes_measurable {n k : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    Measurable (fun g : Fin k → EuclideanSpace ℝ (Fin n) => kSpokes v g i) := by
  apply spokeIndex_measurable.comp
  apply measurable_pi_lambda
  intro q
  exact (continuous_const.inner (continuous_apply q)).measurable

private theorem integrable_spokes_val {n k : ℕ} (I : Instance n) (v : Fin n → EuclideanSpace ℝ (Fin n)) :
    Integrable (fun g : Fin k → EuclideanSpace ℝ (Fin n) => I.val (kSpokes v g)) (spokeMeasure n k) := by
  let : IsProbabilityMeasure (spokeMeasure n k) := by unfold spokeMeasure; infer_instance
  have h (e : Sym2 (Fin n)) : Integrable (fun g : Fin k → EuclideanSpace ℝ (Fin n) =>
      sameInd (kSpokes v g) e) (spokeMeasure n k) := by
    induction e using Sym2.inductionOn with
    | _ i j =>
      have hm := measurableSet_eq_fun (kSpokes_measurable (k := k) v i) (kSpokes_measurable v j)
      have heq : (fun g : Fin k → EuclideanSpace ℝ (Fin n) => sameInd (kSpokes v g) s(i, j)) =
          ({g | kSpokes v g i = kSpokes v g j} : Set (Fin k → EuclideanSpace ℝ (Fin n))).indicator (fun _ => (1 : ℝ)) := by
        funext g
        by_cases hsame : kSpokes v g i = kSpokes v g j <;> simp [sameInd, Set.indicator_apply, hsame]
      rw [heq]
      exact (integrable_const (μ := spokeMeasure n k) (1 : ℝ)).indicator hm
  unfold Instance.val
  apply Integrable.add
  · exact integrable_finsetSum I.Epos (fun e _ => (h e).const_mul (I.w e))
  · exact integrable_finsetSum I.Eneg (fun e _ => ((integrable_const (1 : ℝ)).sub (h e)).const_mul (I.w e))

private theorem weighted_spokesValue_le_algorithm2Value {n : ℕ} (I : Instance n)
    (v : Fin n → EuclideanSpace ℝ (Fin n)) :
    0.364 * I.spokesValue 4 v + 0.636 * I.spokesValue 5 v ≤ I.algorithm2Value v := by
  let : IsProbabilityMeasure (spokeMeasure n 4) := by unfold spokeMeasure; infer_instance
  let : IsProbabilityMeasure (spokeMeasure n 5) := by unfold spokeMeasure; infer_instance
  let f (g : Fin 4 → EuclideanSpace ℝ (Fin n)) := I.val (kSpokes v g)
  let h (g : Fin 5 → EuclideanSpace ℝ (Fin n)) := I.val (kSpokes v g)
  have h4 := (integrable_spokes_val (k := 4) I v).comp_fst (spokeMeasure n 5)
  have h5 := (integrable_spokes_val (k := 5) I v).comp_snd (spokeMeasure n 4)
  have h4' : I.spokesValue 4 v ≤ I.algorithm2Value v := by
    unfold Instance.spokesValue Instance.algorithm2Value
    calc
      _ = ∫ g, f g.1 ∂(spokeMeasure n 4).prod (spokeMeasure n 5) := by
        rw [integral_fun_fst]; simp [f]
      _ ≤ _ := integral_mono h4 (h4.sup h5) (fun z => le_max_left _ _)
  have h5' : I.spokesValue 5 v ≤ I.algorithm2Value v := by
    unfold Instance.spokesValue Instance.algorithm2Value
    calc
      _ = ∫ g, h g.2 ∂(spokeMeasure n 4).prod (spokeMeasure n 5) := by
        rw [integral_fun_snd]; simp [h]
      _ ≤ _ := integral_mono h5 (h4.sup h5) (fun z => le_max_right _ _)
  linarith

end HermiteLaptop.MaxAgree

open HermiteLaptop.MaxAgree

private lemma sum_four_five (μ : Mixture) (h4 : μ.lam 4 = 0.364)
    (h5 : μ.lam 5 = 0.636) (f : ℕ → ℝ) :
    (∑' k, μ.lam k * f k) = 0.364 * f 4 + 0.636 * f 5 := by
  classical
  have hoff (k : ℕ) (hk : k ∉ ({4, 5} : Finset ℕ)) : μ.lam k = 0 := by
    have h := sum_le_hasSum (insert k ({4, 5} : Finset ℕ)) (fun i _ => μ.lam_nonneg i) μ.lam_sum
    rw [Finset.sum_insert hk] at h
    norm_num [Finset.sum_insert, h4, h5] at h
    linarith [μ.lam_nonneg k]
  rw [tsum_eq_sum (s := ({4, 5} : Finset ℕ)) (fun k hk => by simp [hoff k hk])]
  norm_num [Finset.sum_insert, h4, h5]

private noncomputable def fourFiveMix : Mixture where
  K := {4, 5}
  lam := fun k => if k = 4 then 0.364 else if k = 5 then 0.636 else 0
  K_pos := by intro k hk; rcases hk with h | h <;> simp_all
  lam_nonneg := by intro k; split_ifs <;> norm_num
  lam_zero_off := by intro k hk; split_ifs <;> simp_all
  lam_sum := by
    convert hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ) (s := ({4, 5} : Finset ℕ))
      (f := fun k : ℕ => if k = 4 then (0.364 : ℝ) else if k = 5 then 0.636 else 0)
      (fun k hk => by split_ifs <;> simp_all) using 1 <;> norm_num [Finset.sum_insert]

private lemma positive_edge (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    0.7818 * sPlus 0 ρ ≤ fourFiveMix.collision ρ := by
  obtain ⟨cl, hcl, hcert⟩ := proposition_4_4
  have htr (k : ℕ) (hk : k ∈ ({4, 5} : Finset ℕ)) :
      (∑ m ∈ Finset.range 25, (cl k m : ℝ) * ρ ^ m) ≤ collisionProb k ρ := by
    have hk' : 1 ≤ k := by simp only [Finset.mem_insert, Finset.mem_singleton] at hk; omega
    have hρ' : ρ ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [hρ.1], hρ.2⟩
    have h := (proposition_2_4 k hk' 24 (fun m => (cl k m : ℝ)) (coeffC k)
        (hcl k hk) (fun _ _ => le_rfl) ρ hρ').1
    simpa [truncLower, hρ.1] using h
  have h4 := htr 4 (by simp)
  have h5 := htr 5 (by simp)
  rw [Mixture.collision, sum_four_five fourFiveMix (by norm_num [fourFiveMix]) (by norm_num [fourFiveMix])]
  simp only [sPlus, sub_zero, div_one]
  linarith [hcert ρ hρ]

private lemma negative_edge : (0.7818 : ℝ) ≤ 1 - fourFiveMix.collision 0 := by
  obtain ⟨h, h', h''⟩ := negative_edge_equality fourFiveMix
    (by norm_num [fourFiveMix]) (by norm_num [fourFiveMix])
  linarith


theorem solution {n : ℕ} (I : Instance n) (v : Fin n → EuclideanSpace ℝ (Fin n))
    (hv : I.SDPOptimal 0 v) (C : Fin n → ℕ) :
    (0.7818 : ℝ) * I.val C ≤ I.algorithm2Value v := by
  have hmix := lemma_4_1 I Set.univ 0 (by constructor <;> norm_num) v hv
    (fun D _ => sdpRelaxationBridge I v hv D) fourFiveMix
    (fun _ _ _ => Set.mem_univ _) 0.7818 (by norm_num) positive_edge negative_edge C (Set.mem_univ _)
  rw [Mixture.value, sum_four_five fourFiveMix (by norm_num [fourFiveMix]) (by norm_num [fourFiveMix])] at hmix
  exact hmix.trans (weighted_spokesValue_le_algorithm2Value I v)
