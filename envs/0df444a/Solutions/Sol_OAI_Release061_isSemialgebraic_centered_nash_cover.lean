-- Prove2me | solution 1 for OAI.Release061.isSemialgebraic_centered_nash_cover
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:04:24.922989+00:00
-- url     : https://prove2.me/submissions/16408009-31dc-48b2-84cd-58ec06667d4f

import Mathlib
import Definitions.Def_SymmetricDomains
import Definitions.Def_OAIQ025S003

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_IntegralPrimitive
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology


open Polynomial

theorem resultant_derivative_ne_zero_of_generic_separable
    {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (p : R[X])
    (hp : (p.map (algebraMap R K)).Separable) :
    p.resultant p.derivative ≠ 0 := by
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have h := Polynomial.resultant_ne_zero (p.map (algebraMap R K))
    ((p.map (algebraMap R K)).derivative) hp
  rw [Polynomial.derivative_map,
    Polynomial.natDegree_map_eq_of_injective hinj,
    Polynomial.natDegree_map_eq_of_injective hinj,
    Polynomial.resultant_map_map] at h
  exact fun hz => h (by rw [hz, map_zero])

open Polynomial Algebra
open scoped nonZeroDivisors

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_PolynomialEmptyInterior
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology

theorem PolynomialSignSet.exists_regular_polynomial {X ι : Type*}
    [TopologicalSpace X] {c : X → ι → ℝ} (hc : Continuous c)
    {S : Set X} (hS : PolynomialSignSet c S) :
    ∃ P : MvPolynomial ι ℝ, P ≠ 0 ∧ ∀ x,
      MvPolynomial.eval (c x) P ≠ 0 → S ∈ 𝓝 x ∨ Sᶜ ∈ 𝓝 x := by
  classical
  induction hS with
  | zero p =>
    by_cases hp : p = 0
    · subst p
      refine ⟨1,one_ne_zero,fun x _ => Or.inl ?_⟩
      simp
    · refine ⟨p,hp,fun x hx => Or.inr ?_⟩
      exact ((MvPolynomial.continuous_eval p).comp hc).continuousAt.eventually_ne hx
  | positive p =>
    by_cases hp : p = 0
    · subst p
      refine ⟨1,one_ne_zero,fun x _ => Or.inr ?_⟩
      simp
    · refine ⟨p,hp,fun x hx => ?_⟩
      rcases lt_or_gt_of_ne hx with hneg | hpos
      · right
        filter_upwards [((MvPolynomial.continuous_eval p).comp hc).continuousAt.tendsto.eventually_lt_const hneg]
          with y hy
        exact not_lt_of_ge hy.le
      · exact Or.inl (((MvPolynomial.continuous_eval p).comp hc).continuousAt.tendsto.eventually_const_lt hpos)
  | @compl _ _ ih =>
    obtain ⟨P,hP,hreg⟩ := ih
    refine ⟨P,hP,fun x hx => ?_⟩
    simpa only [compl_compl] using (hreg x hx).symm
  | @union _ _ _ _ ihS ihT =>
    obtain ⟨P,hP,hregP⟩ := ihS
    obtain ⟨Q,hQ,hregQ⟩ := ihT
    refine ⟨P*Q,mul_ne_zero hP hQ,fun x hx => ?_⟩
    have hPQ : MvPolynomial.eval (c x) P ≠ 0 ∧ MvPolynomial.eval (c x) Q ≠ 0 := by
      simpa only [map_mul,mul_ne_zero_iff] using hx
    rcases hregP x hPQ.1 with hs | hs
    · exact Or.inl (Filter.mem_of_superset hs subset_union_left)
    rcases hregQ x hPQ.2 with ht | ht
    · exact Or.inl (Filter.mem_of_superset ht subset_union_right)
    · exact Or.inr (by simpa only [compl_union] using inter_mem hs ht)

theorem PolynomialSignSet.frontier_polynomial {X ι : Type*}
    [TopologicalSpace X] {c : X → ι → ℝ} (hc : Continuous c)
    {S : Set X} (hS : PolynomialSignSet c S) :
    ∃ P : MvPolynomial ι ℝ, P ≠ 0 ∧
      ∀ x ∈ frontier S, MvPolynomial.eval (c x) P = 0 := by
  obtain ⟨P,hP,hreg⟩ := hS.exists_regular_polynomial hc
  refine ⟨P,hP,fun x hx => ?_⟩
  by_contra hne
  rcases hreg x hne with hs | hs
  · exact hx.2 (mem_interior_iff_mem_nhds.mpr hs)
  · have hx' : x ∈ frontier Sᶜ := by simpa only [frontier_compl] using hx
    exact hx'.2 (mem_interior_iff_mem_nhds.mpr hs)

theorem PolynomialSignSet.polynomial_of_empty_interior {X ι : Type*}
    [TopologicalSpace X] {c : X → ι → ℝ} (hc : Continuous c)
    {S : Set X} (hS : PolynomialSignSet c S) (hempty : interior S = ∅) :
    ∃ P : MvPolynomial ι ℝ, P ≠ 0 ∧ ∀ x ∈ S, MvPolynomial.eval (c x) P = 0 := by
  obtain ⟨P,hP,hzero⟩ := hS.frontier_polynomial hc
  refine ⟨P,hP,fun x hx => hzero x ?_⟩
  exact ⟨subset_closure hx,by simp only [hempty,mem_empty_iff_false,not_false_eq_true]⟩

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AlgebraicGraphPolynomial
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology

theorem real_graph_empty_interior {ι : Type*} [Fintype ι]
    (B : Set (ι → ℝ)) (f : (ι → ℝ) → ℝ) :
    interior {x : Option ι → ℝ | (fun i => x (some i)) ∈ B ∧
      x none = f (fun i => x (some i))} = ∅ := by
  classical
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hxS := interior_subset hx
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  let y : Option ι → ℝ := x + Pi.single none (r/2)
  have hdist : dist y x < r := by
    rw [dist_eq_norm]
    change ‖x + Pi.single none (r/2) - x‖ < r
    rw [add_sub_cancel_left,Pi.norm_single]
    rw [Real.norm_eq_abs,abs_of_pos (by positivity : 0 < r/2)]
    linarith
  have hyS := hball hdist
  have hyeq := hyS.2
  change y none = _ at hyeq
  simp only [y,Pi.add_apply,Pi.single_eq_same,Pi.single_eq_of_ne (Option.some_ne_none _),add_zero] at hyeq
  linarith [hxS.2,hyeq]

theorem semialgebraic_graph_polynomial {ι : Type*} [Fintype ι]
    (B : Set (ι → ℝ)) (f : (ι → ℝ) → ℝ)
    (hgraph : PolynomialSignSet (id : (Option ι → ℝ) → (Option ι → ℝ))
      {x | (fun i => x (some i)) ∈ B ∧ x none = f (fun i => x (some i))}) :
    ∃ P : MvPolynomial (Option ι) ℝ, P ≠ 0 ∧
      ∀ s ∈ B, MvPolynomial.eval (fun a => a.elim (f s) s) P = 0 := by
  obtain ⟨P,hP,hzero⟩ := hgraph.polynomial_of_empty_interior continuous_id
    (real_graph_empty_interior B f)
  exact ⟨P,hP,fun s hs => hzero _ ⟨hs,rfl⟩⟩

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_PolynomialSignSetFinite
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

namespace SignElimination
open MvPolynomial Set
open scoped Classical BigOperators

namespace RationalOn
variable {X ι : Type*} {c : X → ι → ℝ} {S T : Set X} {f g : X → ℝ}

lemma pow (hf : RationalOn c S f) (n : ℕ) : RationalOn c S (fun x => f x ^ n) := by
  induction n with
  | zero => simpa using (const (c := c) (S := S) 1)
  | succ n ih => simpa only [pow_succ] using ih.mul hf

end RationalOn

end SignElimination
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_PolynomialSignSetRoot
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.SignElimination

open Polynomial Set Finset
open scoped Classical BigOperators

lemma zero_stratum_signSet {X ι : Type*} {c : X → ι → ℝ} {S : Set X}
    (hS : PolynomialSignSet c S) (P : X → ℝ[X]) (N : ℕ)
    (hP : ∀ k, RationalOn c S (fun x => (P x).coeff k))
    (hd : ∀ x ∈ S, (P x).natDegree ≤ N) :
    PolynomialSignSet c (S ∩ {x | P x = 0}) := by
  apply polynomialSignSet_of_sign_invariant hS
    (fun k : Fin (N+1) => fun x => (P x).coeff k) (fun k => hP k)
  intro x hx y hy he
  exact (degree_data_of_coeff_sign_eq (coeff_sign_ext_of_bound (hd x hx) (hd y hy) he)).1

end Release061.SignElimination

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_PolynomialSignSetFinite2
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.SignElimination
open Set Polynomial
open scoped Classical BigOperators

lemma RationalOn.polynomial_preimage {X Y ι κ : Type*} {c : X → ι → ℝ} {d : Y → κ → ℝ}
    {S : Set X} {g : X → ℝ} (hg : RationalOn c S g) (f : Y → X)
    (q : ι → MvPolynomial κ ℝ)
    (hc : ∀ y i, c (f y) i = MvPolynomial.eval (d y) (q i)) :
    RationalOn d (f ⁻¹' S) (g ∘ f) := by
  obtain ⟨p,r,hr⟩ := hg
  refine ⟨MvPolynomial.eval₂Hom MvPolynomial.C q p,
    MvPolynomial.eval₂Hom MvPolynomial.C q r,fun y hy => ?_⟩
  have hv (p : MvPolynomial ι ℝ) :
      MvPolynomial.eval (d y) (MvPolynomial.eval₂Hom MvPolynomial.C q p) =
        MvPolynomial.eval (c (f y)) p := by
    rw [PolynomialSignSet.eval_substitution]
    exact congrArg (fun v => MvPolynomial.eval v p) (funext (fun i => (hc y i).symm))
  simpa only [hv,Function.comp_apply] using hr (f y) hy

lemma RationalOn.coordinate_preimage {X Y ι κ : Type*} {c : X → ι → ℝ} {d : Y → κ → ℝ}
    {S : Set X} {g : X → ℝ} (hg : RationalOn c S g) (f : Y → X)
    (r : ι → κ) (hc : ∀ y i, c (f y) i = d y (r i)) :
    RationalOn d (f ⁻¹' S) (g ∘ f) :=
  hg.polynomial_preimage f (fun i => MvPolynomial.X (r i)) (by simpa using hc)

lemma eval_eq_sum_range_of_natDegree_le (P : ℝ[X]) (N : ℕ) (hN : P.natDegree ≤ N) (y : ℝ) :
    P.eval y = ∑ k ∈ Finset.range (N+1), P.coeff k * y^k := by
  rw [eval_eq_sum_range]
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hN 1))
  intro k hk hkn
  simp only [Finset.mem_range,not_lt] at hkn
  rw [coeff_eq_zero_of_natDegree_lt (by omega),zero_mul]

lemma polynomialSignSet_root_relation {X ι : Type*} {c : X → ι → ℝ}
    {S : Set X} (hS : PolynomialSignSet c S) (P : X → ℝ[X]) (N : ℕ)
    (hP : RationalPolynomialOn c S P) (hd : ∀ x ∈ S, (P x).natDegree ≤ N) :
    PolynomialSignSet (fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1))
      {z | z.1 ∈ S ∧ (P z.1).eval z.2 = 0} := by
  let d := fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1)
  have hT : PolynomialSignSet d (Prod.fst ⁻¹' S) :=
    hS.coordinate_preimage Prod.fst some (by intros; rfl)
  have hy : RationalOn d (Prod.fst ⁻¹' S) (fun z => z.2) := by
    simpa only [MvPolynomial.eval_X, d, Option.elim_none] using
      (RationalOn.polynomial (c := d) (S := Prod.fst ⁻¹' S) (MvPolynomial.X none))
  have hr (k : ℕ) : RationalOn d (Prod.fst ⁻¹' S) (fun z : X × ℝ => (P z.1).coeff k) :=
    (hP k).coordinate_preimage Prod.fst some (by intros; rfl)
  have he : RationalOn d (Prod.fst ⁻¹' S) (fun z : X × ℝ => (P z.1).eval z.2) := by
    apply (RationalOn.sum (Finset.range (N+1)) _ (fun k _ => (hr k).mul (hy.pow k))).congr
    intro z hz
    exact (eval_eq_sum_range_of_natDegree_le (P z.1) N (hd z.1 hz) z.2).symm
  convert he.sign_set hT 0 using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  simp only [mem_ofPred_eq,mem_inter_iff,mem_preimage,sign_eq_zero_iff]

theorem polynomialSignSet_finite_subrelation {X ι : Type*} {c : X → ι → ℝ}
    {A : Set (X × ℝ)}
    (hA : PolynomialSignSet (fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1)) A) :
    ∃ B : Set (X × ℝ),
      PolynomialSignSet (fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1)) B ∧
      B ⊆ A ∧ (∀ x, {y : ℝ | (x,y) ∈ B}.Finite) ∧
      ∀ x, (∃ y : ℝ, (x,y) ∈ B) ↔ ∃ y : ℝ, (x,y) ∈ A := by
  classical
  obtain ⟨s,W,hW⟩ := hA.finite_sign_description
  let Q : s → X → ℝ[X] := fun p x =>
    ((MvPolynomial.optionEquivLeft ℝ ι) p.val).map (MvPolynomial.eval (c x))
  let d : s → ℕ := fun p => ((MvPolynomial.optionEquivLeft ℝ ι) p.val).natDegree
  have hQ (p : s) : RationalPolynomialOn c univ (Q p) := by
    intro k
    simpa only [Q,coeff_map] using RationalOn.polynomial
      (((MvPolynomial.optionEquivLeft ℝ ι) p.val).coeff k)
  have hd (p : s) (x : X) (_hx : x ∈ (univ : Set X)) : (Q p x).natDegree ≤ d p := natDegree_map_le
  let T := fun J : Finset s => (univ : Set X) ∩ {x | ∀ a, Q a x ≠ 0 ↔ a ∈ J}
  have hT (J : Finset s) : PolynomialSignSet c (T J) :=
    polynomialSignSet_nonzero_mask PolynomialSignSet.univ d Q hQ hd J
  let P := fun (J : Finset s) x => ∏ a : J, Q a.val x
  let N := fun J : Finset s => ∑ a : J, d a.val
  have hp (J : Finset s) : RationalPolynomialOn c (T J) (P J) :=
    RationalPolynomialOn.prod Finset.univ _ (fun a _ => (hQ a.val).mono inter_subset_left)
  have hpn (J : Finset s) (x : X) (hx : x ∈ T J) : P J x ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun a _ => (hx.2 a.val).mpr a.property)
  have hpd (J : Finset s) (x : X) (hx : x ∈ T J) : (P J x).natDegree ≤ N J :=
    (natDegree_prod_le _ _).trans (Finset.sum_le_sum (fun a _ => hd a.val x hx.1))
  let U := fun (J : Finset s) (n : Fin (N J+1)) => T J ∩
    {x | P J x ≠ 0 ∧ (P J x).natDegree = n.val}
  have hU (J : Finset s) (n : Fin (N J+1)) : PolynomialSignSet c (U J n) :=
    degree_stratum_signSet (hT J) (P J) (N J) n (hp J) (hpd J)
  let R := fun (J : Finset s) x => P J x * criticalSampler (P J x)
  have hrs (J : Finset s) (x : X) (hx : x ∈ T J) : R J x ≠ 0 ∧
      ∀ y : ℝ, ∃ z : ℝ, (R J x).eval z = 0 ∧
        ∀ a, SignType.sign ((Q a x).eval z) = SignType.sign ((Q a x).eval y) := by
    have hs := sample_all_chambers (fun a : J => Q a.val x)
      (fun a => (hx.2 a.val).mpr a.property)
    refine ⟨hs.1,fun y => ?_⟩
    obtain ⟨z,hz,hsg⟩ := hs.2 y
    refine ⟨z,hz,fun a => ?_⟩
    by_cases ha : a ∈ J
    · exact hsg ⟨a,ha⟩
    · have ha0 : Q a x = 0 := by simpa only [not_ne_iff] using mt (hx.2 a).mp ha
      simp only [ha0,eval_zero]
  let B := fun (J : Finset s) (n : Fin (N J+1)) =>
    {z : X × ℝ | z.1 ∈ U J n ∧ (R J z.1).eval z.2 = 0} ∩ A
  have hB (J : Finset s) (n : Fin (N J+1)) :
      PolynomialSignSet (fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1)) (B J n) := by
    apply PolynomialSignSet.inter _ hA
    apply polynomialSignSet_root_relation (hU J n) (R J) (2*n.val+2)
    · have hrp := (hp J).mono (show U J n ⊆ T J from inter_subset_left)
      exact hrp.mul (hrp.criticalSampler n (fun x hx => hx.2.2))
    · intro x hx
      have hb := natDegree_mul_le (p := P J x) (q := criticalSampler (P J x))
      have hc := criticalSampler_natDegree_le (P J x)
      rw [hx.2.2] at hb hc
      change (P J x * criticalSampler (P J x)).natDegree ≤ _
      omega
  refine ⟨{z | ∃ J, ∃ n, z ∈ B J n},?_,?_,?_,?_⟩
  · exact PolynomialSignSet.exists_finite _ (fun J =>
      PolynomialSignSet.exists_finite _ (hB J))
  · rintro z ⟨J,n,hz⟩
    exact hz.2
  · intro x
    have hf (J : Finset s) (n : Fin (N J+1)) : {y : ℝ | (x,y) ∈ B J n}.Finite := by
      by_cases hx : x ∈ U J n
      · apply (Polynomial.finite_setOfPred_isRoot (hrs J x hx.1).1).subset
        intro y hy
        exact hy.1.2
      · have he : {y : ℝ | (x,y) ∈ B J n} = ∅ := by
          ext y
          simp only [B,mem_inter_iff,mem_ofPred_eq,mem_empty_iff_false,iff_false,not_and]
          exact fun h _ => hx h.1
        rw [he]
        exact finite_empty
    convert Set.finite_iUnion (fun J => Set.finite_iUnion (hf J)) using 1
    all_goals try with_reducible_and_instances rfl
    ext y
    simp only [mem_iUnion,mem_ofPred_eq]
  · intro x
    constructor
    · rintro ⟨y,J,n,hy⟩
      exact ⟨y,hy.2⟩
    · rintro ⟨y,hy⟩
      let J := Finset.univ.filter (fun a : s => Q a x ≠ 0)
      have hx : x ∈ T J := ⟨mem_univ _,fun a => by simp [J]⟩
      let n : Fin (N J+1) := ⟨(P J x).natDegree,Nat.lt_succ_of_le (hpd J x hx)⟩
      obtain ⟨z,hz,hsg⟩ := (hrs J x hx).2 y
      refine ⟨z,J,n,⟨⟨⟨hx,hpn J x hx,rfl⟩,hz⟩,?_⟩⟩
      apply (hW (x,z)).mpr
      have hsg' : (fun p : s => SignType.sign (MvPolynomial.eval
          (fun o => Option.elim o z (c x)) p.val)) =
          fun p : s => SignType.sign (MvPolynomial.eval (fun o => Option.elim o y (c x)) p.val) := by
        funext p
        simpa only [Q,eval_optionEquivLeft] using hsg p
      rw [hsg']
      exact (hW (x,y)).mp hy

end Release061.SignElimination

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_PolynomialSignSetInf
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter

namespace Release061.SignElimination
open Set Metric
open scoped Classical

lemma polynomialSignSet_forall_one {X ι : Type*} {c : X → ι → ℝ}
    {P : X × ℝ → Prop}
    (h : PolynomialSignSet (fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1))
      {z | P z}) : PolynomialSignSet c {x | ∀ t : ℝ, P (x,t)} := by
  convert (polynomialSignSet_projection_one h.compl).compl using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp

end Release061.SignElimination

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_Pair
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set
open SignElimination
open scoped Classical

namespace SemialgebraicOn
variable {ι κ δ : Type*}
variable {B C : Set (ι → ℝ)} {f : (ι → ℝ) → (κ → ℝ)}

lemma domain [Finite κ] (h : SemialgebraicOn B f) : PolynomialSignSet id B := by
  simpa only [mem_ofPred_eq, exists_and_left, exists_eq, and_true, ofPred_mem_eq] using
    polynomialSignSet_projection_finite (c := id) h

lemma restrict (hf : SemialgebraicOn B f) (hC : PolynomialSignSet id C) :
    SemialgebraicOn (B ∩ C) f := by
  have hc := hC.coordinate_preimage (fun z : (ι → ℝ) × (κ → ℝ) => z.1) Sum.inl
    (d := fun z => Sum.elim z.1 z.2) (by intro z i; rfl)
  unfold SemialgebraicOn at hf ⊢
  convert hf.inter hc using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  simp only [mem_inter_iff,mem_ofPred_eq,mem_preimage]
  tauto

lemma mono (hf : SemialgebraicOn B f) (hC : PolynomialSignSet id C) (hCB : C ⊆ B) :
    SemialgebraicOn C f := by
  simpa only [inter_eq_right.mpr hCB] using hf.restrict hC

lemma constant [Finite κ] (hB : PolynomialSignSet id B) (v : κ → ℝ) :
    SemialgebraicOn B (fun _ => v) := by
  simpa only [MvPolynomial.eval_C] using polynomial hB (fun j => MvPolynomial.C (v j))

end SemialgebraicOn
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_FiniteUnion
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology MeasureTheory
open scoped Classical

namespace NashPatch
variable {n : ℕ}

lemma dim_le (p : NashPatch n) : p.dim ≤ n := by
  obtain ⟨x,hx⟩ := p.isConnected_domain.nonempty
  simpa using (fderiv ℝ p.toFun x).toLinearMap.finrank_le_finrank_of_injective (p.injective_fderiv x hx)

lemma image_mem_nhds_of_dim_eq (p : NashPatch n) (hdim : p.dim = n)
    {x : Fin p.dim → ℝ} (hx : x ∈ p.domain) : p.image ∈ 𝓝 (p.toFun x) := by
  let L := fderiv ℝ p.toFun x
  have hdim' : Module.finrank ℝ (Fin p.dim → ℝ) = Module.finrank ℝ (Fin n → ℝ) := by
    simpa using hdim
  let e := (L.toLinearMap.linearEquivOfInjective (p.injective_fderiv x hx) hdim').toContinuousLinearEquiv
  have he : (e : (Fin p.dim → ℝ) →L[ℝ] (Fin n → ℝ)) = L := by
    ext v
    rfl
  have hder : HasStrictFDerivAt p.toFun (e : (Fin p.dim → ℝ) →L[ℝ] (Fin n → ℝ)) x := by
    rw [he]
    exact (p.analytic_toFun x hx).hasStrictFDerivAt
  rw [← hder.map_nhds_eq_of_equiv]
  exact Filter.image_mem_map (p.isOpen_domain.mem_nhds hx)

lemma dim_lt_of_empty_interior (p : NashPatch n) {S : Set (Fin n → ℝ)}
    (hS : interior S = ∅) (hsub : p.image ⊆ S) : p.dim < n := by
  apply lt_of_le_of_ne p.dim_le
  intro he
  obtain ⟨x,hx⟩ := p.isConnected_domain.nonempty
  have hm : p.toFun x ∈ interior S := mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset (p.image_mem_nhds_of_dim_eq he hx) hsub)
  simp only [hS,mem_empty_iff_false] at hm

end NashPatch

namespace HasFiniteNashCover
variable {n : ℕ}

lemma empty : HasFiniteNashCover (∅ : Set (Fin n → ℝ)) := by
  exact ⟨∅,by simp⟩

lemma patch (p : NashPatch n) : HasFiniteNashCover p.image := by
  refine ⟨{p},?_⟩
  simp

lemma union {S T : Set (Fin n → ℝ)} (hS : HasFiniteNashCover S) (hT : HasFiniteNashCover T) :
    HasFiniteNashCover (S ∪ T) := by
  obtain ⟨P,hP⟩ := hS
  obtain ⟨Q,hQ⟩ := hT
  refine ⟨P ∪ Q,fun x => ?_⟩
  simp only [mem_union,hP,hQ,Finset.mem_union]
  aesop

lemma finite_union {α : Type*} (s : Finset α) {S : α → Set (Fin n → ℝ)}
    (hS : ∀ i ∈ s, HasFiniteNashCover (S i)) : HasFiniteNashCover (⋃ i ∈ s, S i) := by
  induction s using Finset.induction_on with
  | empty => simpa using (empty (n := n))
  | @insert i s hi ih =>
    simpa only [Finset.mem_insert,ofPred_or,iUnion_iUnion_eq_or_left] using
      (hS i (Finset.mem_insert_self _ _)).union
        (ih (fun j hj => hS j (Finset.mem_insert_of_mem hj)))

end HasFiniteNashCover
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_PolynomialSignSetChoice
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.SignElimination
open Set
open scoped Classical

theorem polynomialSignSet_choice_relation_one {X ι : Type*} {c : X → ι → ℝ}
    {A : Set (X × ℝ)}
    (hA : PolynomialSignSet (fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1)) A) :
    ∃ C : Set (X × ℝ),
      PolynomialSignSet (fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1)) C ∧
      C ⊆ A ∧ (∀ x y z, (x,y) ∈ C → (x,z) ∈ C → y = z) ∧
      ∀ x, (∃ y : ℝ, (x,y) ∈ C) ↔ ∃ y : ℝ, (x,y) ∈ A := by
  classical
  obtain ⟨B,hB,hBA,hfin,hdom⟩ := polynomialSignSet_finite_subrelation hA
  let d := fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1)
  let C : Set (X × ℝ) := {z | z ∈ B ∧ ∀ t, (z.1,t) ∈ B → z.2 ≤ t}
  have hlt : PolynomialSignSet (fun z : (X × ℝ) × ℝ =>
      fun o => Option.elim o z.2 (d z.1))
      {z | (z.1.1,z.2) ∈ B ∧ z.2 < z.1.2} := by
    have hb := hB.coordinate_preimage (fun z : (X × ℝ) × ℝ => (z.1.1,z.2))
      (fun o => Option.elim o none (fun i => some (some i)))
      (d := fun z : (X × ℝ) × ℝ => fun o => Option.elim o z.2 (d z.1))
      (by intro z i; cases i <;> rfl)
    have hh : PolynomialSignSet (fun z : (X × ℝ) × ℝ =>
        fun o => Option.elim o z.2 (d z.1)) {z | z.2 < z.1.2} := by
      convert PolynomialSignSet.positive (c := fun z : (X × ℝ) × ℝ =>
          fun o => Option.elim o z.2 (d z.1))
          (MvPolynomial.X (some none) - MvPolynomial.X none) using 1
      all_goals try with_reducible_and_instances rfl
      ext z
      simp [d]
    exact hb.inter hh
  have hC : PolynomialSignSet d C := by
    have hh := hB.inter (polynomialSignSet_projection_one hlt).compl
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    simp only [C,mem_ofPred_eq,mem_inter_iff,mem_compl_iff,not_exists,not_and,not_lt]
  have huniq : ∀ x y z, (x,y) ∈ C → (x,z) ∈ C → y = z := by
    intro x y z hy hz
    exact le_antisymm (hy.2 z hz.1) (hz.2 y hy.1)
  refine ⟨C,hC,fun z hz => hBA hz.1,huniq,fun x => ?_⟩
  constructor
  · rintro ⟨y,hy⟩
    exact ⟨y,hBA hy.1⟩
  · intro hx
    obtain ⟨y,hy⟩ := (hdom x).mpr hx
    let s := (hfin x).toFinset
    have hs : s.Nonempty := ⟨y,by simpa only [s,Set.Finite.mem_toFinset,mem_ofPred_eq] using hy⟩
    refine ⟨s.min' hs,?_,?_⟩
    · exact (hfin x).mem_toFinset.mp (s.min'_mem hs)
    · intro t ht
      exact s.min'_le t ((hfin x).mem_toFinset.mpr ht)

end Release061.SignElimination

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_PolynomialSignSetChoice2
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.SignElimination
open Set
open scoped Classical

universe uX uI uK

theorem polynomialSignSet_choice_relation_finite {X : Type uX} {ι : Type uI} {κ : Type uK}
    [Finite κ] {c : X → ι → ℝ} {A : Set (X × (κ → ℝ))}
    (hA : PolynomialSignSet (fun z : X × (κ → ℝ) => Sum.elim (c z.1) z.2) A) :
    ∃ B : Set (X × (κ → ℝ)),
      PolynomialSignSet (fun z : X × (κ → ℝ) => Sum.elim (c z.1) z.2) B ∧
      B ⊆ A ∧ (∀ x y z, (x,y) ∈ B → (x,z) ∈ B → y = z) ∧
      ∀ x, (∃ y : κ → ℝ, (x,y) ∈ B) ↔ ∃ y : κ → ℝ, (x,y) ∈ A := by
  classical
  suffices hh : ∀ (κ : Type uK) [Finite κ], ∀ {X : Type uX} {ι : Type uI} (c : X → ι → ℝ)
      (A : Set (X × (κ → ℝ))),
      PolynomialSignSet (fun z : X × (κ → ℝ) => Sum.elim (c z.1) z.2) A →
      ∃ B : Set (X × (κ → ℝ)),
        PolynomialSignSet (fun z : X × (κ → ℝ) => Sum.elim (c z.1) z.2) B ∧
        B ⊆ A ∧ (∀ x y z, (x,y) ∈ B → (x,z) ∈ B → y = z) ∧
        ∀ x, (∃ y : κ → ℝ, (x,y) ∈ B) ↔ ∃ y : κ → ℝ, (x,y) ∈ A from hh κ c A hA
  intro κ _
  induction κ using Finite.induction_empty_option with
  | @of_equiv α β e ih =>
    intro X ι c A hA
    let f : (X × (α → ℝ)) → X × (β → ℝ) := fun z => (z.1,z.2 ∘ e.symm)
    let g : (X × (β → ℝ)) → X × (α → ℝ) := fun z => (z.1,z.2 ∘ e)
    have hf := hA.coordinate_preimage f (Sum.map id e.symm)
      (d := fun z => Sum.elim (c z.1) z.2) (by intro z i; cases i <;> rfl)
    obtain ⟨B,hB,hBA,huniq,hdom⟩ := ih c (f ⁻¹' A) hf
    have hg := hB.coordinate_preimage g (Sum.map id e)
      (d := fun z => Sum.elim (c z.1) z.2) (by intro z i; cases i <;> rfl)
    have hfg (z : X × (β → ℝ)) : f (g z) = z := by
      simp [f,g,Function.comp_def]
    have hgf (z : X × (α → ℝ)) : g (f z) = z := by
      simp [f,g,Function.comp_def]
    refine ⟨g ⁻¹' B,hg,fun z hz => ?_,?_,fun x => ?_⟩
    · simpa only [mem_preimage,hfg] using hBA hz
    · intro x y z hy hz
      have hh := huniq x (y ∘ e) (z ∘ e) hy hz
      funext j
      simpa only [Function.comp_apply,e.apply_symm_apply] using congrFun hh (e.symm j)
    · constructor
      · rintro ⟨y,hy⟩
        exact ⟨y,by simpa only [mem_preimage,hfg] using hBA hy⟩
      · rintro ⟨y,hy⟩
        have hx : ∃ u : α → ℝ, (x,u) ∈ f ⁻¹' A :=
          ⟨y ∘ e,by change f (g (x,y)) ∈ A; rwa [hfg]⟩
        obtain ⟨u,hu⟩ := (hdom x).mpr hx
        refine ⟨u ∘ e.symm,?_⟩
        change g (f (x,u)) ∈ B
        rwa [hgf]
  | h_empty =>
    intro X ι c A hA
    exact ⟨A,hA,Subset.rfl,fun _ _ _ _ _ => Subsingleton.elim _ _,fun _ => Iff.rfl⟩
  | @h_option κ _ ih =>
    intro X ι c A hA
    let f : ((X × (κ → ℝ)) × ℝ) → X × (Option κ → ℝ) :=
      fun z => (z.1.1,fun o => Option.elim o z.2 z.1.2)
    let g : (X × (Option κ → ℝ)) → (X × (κ → ℝ)) × ℝ :=
      fun z => ((z.1,z.2 ∘ some),z.2 none)
    let d := fun z : X × (κ → ℝ) => Sum.elim (c z.1) z.2
    have hfg (z : X × (Option κ → ℝ)) : f (g z) = z := by
      apply Prod.ext
      · rfl
      · funext o
        cases o <;> rfl
    have hgf (z : (X × (κ → ℝ)) × ℝ) : g (f z) = z := rfl
    have ha := hA.coordinate_preimage f
      (Sum.elim (fun i => some (Sum.inl i)) (Option.map Sum.inr))
      (d := fun z : (X × (κ → ℝ)) × ℝ => fun o => Option.elim o z.2 (d z.1)) (by
        intro z i
        cases i with
        | inl i => rfl
        | inr o => cases o <;> rfl)
    obtain ⟨B,hB,hBA,huniqB,hdomB⟩ := polynomialSignSet_choice_relation_one ha
    let C : Set (X × (κ → ℝ)) := {z | ∃ t : ℝ, (z,t) ∈ B}
    have hC : PolynomialSignSet d C := polynomialSignSet_projection_one hB
    obtain ⟨E,hE,hEC,huniqE,hdomE⟩ := ih c C hC
    let p : X × (Option κ → ℝ) → X × (κ → ℝ) := fun z => (z.1,z.2 ∘ some)
    have hbg := hB.coordinate_preimage g
      (fun o => Option.elim o (Sum.inr none) (Sum.elim Sum.inl (fun k => Sum.inr (some k))))
      (d := fun z : X × (Option κ → ℝ) => Sum.elim (c z.1) z.2) (by
        intro z o
        cases o with
        | none => rfl
        | some i => cases i <;> rfl)
    have hep := hE.coordinate_preimage p (Sum.map id some)
      (d := fun z : X × (Option κ → ℝ) => Sum.elim (c z.1) z.2)
      (by intro z i; cases i <;> rfl)
    let D := (g ⁻¹' B) ∩ (p ⁻¹' E)
    have hDA : D ⊆ A := by
      intro z hz
      simpa only [mem_preimage,hfg] using hBA hz.1
    refine ⟨D,hbg.inter hep,hDA,?_,fun x => ?_⟩
    · intro x y z hy hz
      have he := huniqE x (y ∘ some) (z ∘ some) hy.2 hz.2
      have ht : y none = z none := by
        apply huniqB (x,y ∘ some) (y none) (z none) hy.1
        rw [he]
        exact hz.1
      funext o
      cases o with
      | none => exact ht
      | some i => exact congrFun he i
    · constructor
      · rintro ⟨y,hy⟩
        exact ⟨y,hDA hy⟩
      · rintro ⟨y,hy⟩
        have hxC : (x,y ∘ some) ∈ C := by
          apply (hdomB (x,y ∘ some)).mpr
          refine ⟨y none,?_⟩
          change f (g (x,y)) ∈ A
          rwa [hfg]
        obtain ⟨u,hu⟩ := (hdomE x).mpr ⟨y ∘ some,hxC⟩
        obtain ⟨t,ht⟩ := hEC hu
        refine ⟨fun o => Option.elim o t u,ht,hu⟩

theorem polynomialSignSet_choice_finite {X : Type uX} {ι : Type uI} {κ : Type uK}
    [Finite κ] {c : X → ι → ℝ} {A : Set (X × (κ → ℝ))}
    (hA : PolynomialSignSet (fun z : X × (κ → ℝ) => Sum.elim (c z.1) z.2) A) :
    ∃ f : X → κ → ℝ,
      (∀ x, (∃ y : κ → ℝ, (x,y) ∈ A) → (x,f x) ∈ A) ∧
      PolynomialSignSet (fun z : X × (κ → ℝ) => Sum.elim (c z.1) z.2)
        {z | (∃ y : κ → ℝ, (z.1,y) ∈ A) ∧ z.2 = f z.1} := by
  classical
  obtain ⟨B,hB,hBA,huniq,hdom⟩ := polynomialSignSet_choice_relation_finite hA
  let f := fun x => if hx : ∃ y : κ → ℝ, (x,y) ∈ A then ((hdom x).mpr hx).choose else 0
  have hf (x : X) (hx : ∃ y : κ → ℝ, (x,y) ∈ A) : (x,f x) ∈ B := by
    simpa only [f,dite_eq_left hx] using ((hdom x).mpr hx).choose_spec
  refine ⟨f,fun x hx => hBA (hf x hx),?_⟩
  convert hB using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  constructor
  · rintro ⟨hx,he⟩
    simpa only [← he] using hf z.1 hx
  · intro hz
    have hx := (hdom z.1).mp ⟨z.2,hz⟩
    exact ⟨hx,huniq z.1 z.2 (f z.1) hz (hf z.1 hx)⟩

end Release061.SignElimination

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AnalyticZeroNull
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

open Set Filter MeasureTheory
open scoped Topology

theorem analytic_real_zero_null {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set ℝ} (hU : MeasurableSet U) (hc : IsPreconnected U)
    {f : ℝ → F} (hf : AnalyticOnNhd ℝ f U) {p : ℝ} (hp : p ∈ U) (hne : f p ≠ 0) :
    volume {x | x ∈ U ∧ f x = 0} = 0 := by
  have ha := hf.eqOn_zero_or_eventually_ne_zero_of_preconnected hc
  rcases ha with ha | ha
  · exact (hne (ha hp)).elim
  · have hb := ae_restrict_le_codiscreteWithin (μ := volume) hU ha
    have hd := (ae_restrict_iff' hU).mp hb
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hd] with x hx
    exact fun h => hx h.1 h.2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem radialPlane_analytic (p : E × ℝ) (q : E × ℝ) : AnalyticAt ℝ (radialPlane p) q := by
  exact analyticAt_const.add ((analyticAt_snd.smul analyticAt_fst).prod analyticAt_snd)

theorem radialLine_analytic (p : E × ℝ) (y : E) (t : ℝ) : AnalyticAt ℝ (radialLine p y) t := by
  exact (radialPlane_analytic p (y,t)).comp (analyticAt_const.prod analyticAt_id)

theorem analytic_zero_null_convex [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    {U : Set (E × ℝ)} (hU : IsOpen U) (hc : Convex ℝ U)
    {f : E × ℝ → F} (hf : AnalyticOnNhd ℝ f U)
    {p : E × ℝ} (hp : p ∈ U) (hne : f p ≠ 0) :
    (μ.prod volume) {x | x ∈ U ∧ f x = 0} = 0 := by
  classical
  let Z : Set (E × ℝ) := {x | x ∈ U ∧ f x = 0}
  have hZ : MeasurableSet Z := by
    have hm : Measurable (U.piecewise f (fun _ => 0)) :=
      hf.continuousOn.measurable_piecewise continuousOn_const hU.measurableSet
    convert hU.measurableSet.inter ((measurableSet_singleton (0 : F)).preimage hm) using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    by_cases hx : x ∈ U <;> simp [Z,hx]
  have hr : Continuous (radialPlane p) := continuous_iff_continuousAt.mpr fun q => (radialPlane_analytic p q).continuousAt
  have hn : (μ.prod volume) (radialPlane p ⁻¹' Z) = 0 := by
    apply Measure.measure_prod_null_of_ae_null (hZ.preimage hr.measurable)
    apply Eventually.of_forall
    intro y
    let I : Set ℝ := radialLine p y ⁻¹' U
    have hI : IsOpen I := hU.preimage (continuous_iff_continuousAt.mpr fun t => (radialLine_analytic p y t).continuousAt)
    have hr0 : radialLine p y 0 = p := by
      change p + ((0 : ℝ) • y,(0 : ℝ)) = p
      rw [zero_smul]
      exact add_zero p
    have h0 : (0 : ℝ) ∈ I := by change radialLine p y 0 ∈ U; simpa only [hr0] using hp
    have hf0 : f (radialLine p y 0) ≠ 0 := by simpa only [hr0] using hne
    exact analytic_real_zero_null hI.measurableSet (hc.affine_preimage (radialLine p y)).isPreconnected
      (fun t ht => (hf _ ht).comp (radialLine_analytic p y t)) h0 hf0
  have himg := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
    (μ.prod volume) (s := radialPlane p ⁻¹' Z)
    (fun q _ => (radialPlane_analytic p q).differentiableAt.differentiableWithinAt) hn
  have hplane : (μ.prod volume) (Set.univ ×ˢ {p.2}) = 0 := by
    rw [Measure.prod_prod,measure_singleton,mul_zero]
  apply measure_mono_null (t := radialPlane p '' (radialPlane p ⁻¹' Z) ∪ (Set.univ ×ˢ {p.2}))
      _ (measure_union_null himg hplane)
  intro x hx
  by_cases ht : x.2 = p.2
  · exact Or.inr ⟨mem_univ _,ht⟩
  · left
    let q : E × ℝ := ((x.2-p.2)⁻¹ • (x.1-p.1),x.2-p.2)
    have hq : radialPlane p q = x := by
      ext
      · simp only [radialPlane,q,Prod.fst_add,smul_smul]
        rw [mul_inv_cancel₀ (sub_ne_zero.mpr ht),one_smul]
        abel
      · simp [radialPlane,q]
    exact ⟨q,by simpa only [mem_preimage,hq] using hx,hq⟩

theorem analytic_zero_null_connected [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    {U : Set (E × ℝ)} (hU : IsOpen U) (hc : IsPreconnected U)
    {f : E × ℝ → F} (hf : AnalyticOnNhd ℝ f U)
    {p : E × ℝ} (hp : p ∈ U) (hne : f p ≠ 0) :
    (μ.prod volume) {x | x ∈ U ∧ f x = 0} = 0 := by
  classical
  have hball : ∀ x ∈ U, ∃ r > 0, Metric.ball x r ⊆ U := fun x hx =>
    Metric.isOpen_iff.mp hU x hx
  choose! r hr hsub using hball
  obtain ⟨T,hTU,hTc,hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (s := U) (f := fun x => Metric.ball x (r x))
    (fun x hx => mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x (hr x hx)))
  have hn : ∀ x ∈ T, (μ.prod volume) {y | y ∈ Metric.ball x (r x) ∧ f y = 0} = 0 := by
    intro x hx
    have hxu := hTU hx
    have he : ∃ y ∈ Metric.ball x (r x), f y ≠ 0 := by
      by_contra! he
      have hz : f =ᶠ[𝓝 x] 0 := by
        filter_upwards [Metric.ball_mem_nhds x (hr x hxu)] with y hy
        exact he y hy
      exact hne (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hxu hz hp)
    obtain ⟨y,hy,hfy⟩ := he
    exact analytic_zero_null_convex μ Metric.isOpen_ball (convex_ball x (r x))
      (hf.mono (hsub x hxu)) hy hfy
  apply measure_mono_null (t := ⋃ x ∈ T, {y | y ∈ Metric.ball x (r x) ∧ f y = 0})
    _ ((measure_biUnion_null_iff hTc).mpr hn)
  intro y hy
  obtain ⟨x,hx,hyx⟩ := mem_iUnion₂.mp (hcov hy.1)
  exact mem_iUnion₂.mpr ⟨x,hx,hyx,hy.2⟩

theorem analytic_zero_null [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    {U : Set E} (hU : IsOpen U) (hc : IsPreconnected U)
    {f : E → F} (hf : AnalyticOnNhd ℝ f U)
    {p : E} (hp : p ∈ U) (hne : f p ≠ 0) : μ {x | x ∈ U ∧ f x = 0} = 0 := by
  classical
  rcases subsingleton_or_nontrivial E with hs | hnt
  · have hz : {x | x ∈ U ∧ f x = 0} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hne ((congrArg f (Subsingleton.elim p x)).trans hx.2)
    rw [hz,measure_empty]
  · obtain ⟨n,hd⟩ := Nat.exists_eq_succ_of_ne_zero (Module.finrank_pos (R := ℝ) (M := E)).ne'
    let e : E ≃L[ℝ] ((Fin n → ℝ) × ℝ) := ContinuousLinearEquiv.ofFinrankEq
      (by simpa [Module.finrank_prod,Module.finrank_pi_fintype,Nat.succ_eq_add_one] using hd)
    let U' := e.symm ⁻¹' U
    let f' := f ∘ e.symm
    have hf' : AnalyticOnNhd ℝ f' U' := fun x hx => (hf _ hx).comp (e.symm.analyticAt x)
    have hp' : e p ∈ U' := by simpa only [U',mem_preimage,e.symm_apply_apply] using hp
    have he : f' (e p) ≠ 0 := by simpa only [f',Function.comp_apply,e.symm_apply_apply] using hne
    have hU' : IsOpen U' := hU.preimage e.symm.continuous
    have hc' : IsPreconnected U' := e.symm.toHomeomorph.isPreconnected_preimage.mpr hc
    have hn := analytic_zero_null_connected (volume : Measure (Fin n → ℝ)) hU' hc' hf' hp' he
    let Z' := {x | x ∈ U' ∧ f' x = 0}
    have hZ' : MeasurableSet Z' := by
      have hm : Measurable (U'.piecewise f' (fun _ => 0)) :=
        hf'.continuousOn.measurable_piecewise continuousOn_const hU'.measurableSet
      convert hU'.measurableSet.inter ((measurableSet_singleton (0 : F)).preimage hm) using 1
      all_goals try with_reducible_and_instances rfl
      ext x
      by_cases hx : x ∈ U' <;> simp [Z',hx]
    have hae : ∀ᵐ q ∂(volume : Measure (Fin n → ℝ)).prod volume, q ∈ Z'ᶜ :=
      measure_eq_zero_iff_ae_notMem.mp hn
    have hat := (ae_comp_linearMap_mem_iff e.toLinearMap μ
      ((volume : Measure (Fin n → ℝ)).prod volume) e.surjective hZ'.compl).mpr hae
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hat] with x hx
    have hx' : e x ∈ Z'ᶜ := hx
    simpa [Z',U',f'] using hx'

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_GenericPolynomialParameterFactor
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology MeasureTheory

theorem complex_polynomial_real_witness {n : ℕ}
    (P : MvPolynomial (Fin n) ℂ) (hP : P ≠ 0) :
    ∃ x : Fin n → ℝ, MvPolynomial.eval (fun i => (x i : ℂ)) P ≠ 0 := by
  classical
  by_contra! hz
  apply hP
  apply MvPolynomial.funext_set (fun _ => Set.range (fun t : ℝ => (t : ℂ)))
    (fun _ => Set.infinite_range_of_injective Complex.ofReal_injective)
  intro z hz'
  have hc : ∀ i, ∃ t : ℝ, (t : ℂ) = z i := fun i => hz' i (mem_univ i)
  choose x hx using hc
  have he : z = fun i => (x i : ℂ) := (funext hx).symm
  simpa only [he,map_zero] using hz x

theorem complex_polynomial_real_zero_null {n : ℕ}
    (P : MvPolynomial (Fin n) ℂ) (hP : P ≠ 0) :
    volume {x : Fin n → ℝ | MvPolynomial.eval (fun i => (x i : ℂ)) P = 0} = 0 := by
  obtain ⟨x,hx⟩ := complex_polynomial_real_witness P hP
  have he (s : Fin n → ℝ) : AnalyticAt ℝ (fun y : Fin n → ℝ => fun i => (y i : ℂ)) s := by
    apply analyticAt_pi_iff.mpr
    intro i
    exact (Complex.ofRealCLM.analyticAt _).comp
      ((ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).analyticAt s)
  have ha : AnalyticOnNhd ℝ (fun x : Fin n → ℝ => MvPolynomial.eval (fun i => (x i : ℂ)) P) univ := by
    intro s _
    exact (((AnalyticOnNhd.eval_mvPolynomial P) _ (mem_univ _)).restrictScalars (𝕜 := ℝ)).comp (he s)
  simpa only [mem_univ,true_and] using analytic_zero_null volume isOpen_univ
    isPreconnected_univ ha (mem_univ x) hx

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_GenericFinParameterPolynomial
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology MeasureTheory Metric

theorem separable_map_of_leading_resultant_ne_zero
    {R K : Type*} [CommRing R] [Field K] (P : Polynomial R) (e : R →+* K)
    (hl : e P.leadingCoeff ≠ 0)
    (hd : e (P.resultant P.derivative) ≠ 0) : (P.map e).Separable := by
  by_cases hdeg : P.natDegree = 0
  · have hP : P = Polynomial.C P.leadingCoeff := by
      simpa only [Polynomial.leadingCoeff,hdeg] using Polynomial.eq_C_of_natDegree_eq_zero hdeg
    rw [hP,Polynomial.map_C]
    exact (Polynomial.separable_C _).mpr (isUnit_iff_ne_zero.mpr hl)
  · obtain ⟨a,b,_,_,hab⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant
      P P.derivative le_rfl le_rfl (Or.inl hdeg)
    have hh := congrArg (Polynomial.map e) hab
    simp only [Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C] at hh
    refine ⟨Polynomial.C ((e (P.resultant P.derivative))⁻¹) * a.map e,
      Polynomial.C ((e (P.resultant P.derivative))⁻¹) * b.map e,?_⟩
    rw [Polynomial.derivative_map]
    calc
      _ = Polynomial.C ((e (P.resultant P.derivative))⁻¹) *
          (P.map e * a.map e + P.derivative.map e * b.map e) := by ring
      _ = 1 := by rw [hh,← Polynomial.C_mul,inv_mul_cancel₀ hd,Polynomial.C_1]

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SquarefreeRelationOffDenominator
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Polynomial
open scoped nonZeroDivisors

theorem polynomial_clear_denominators
    {R K : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (p : K[X]) :
    ∃ a : R, a ≠ 0 ∧ ∃ q : R[X],
      q.map (algebraMap R K) = C (algebraMap R K a) * p := by
  obtain ⟨a,ha,hq⟩ := IsLocalization.integerNormalization_spec R⁰ p
  refine ⟨a,mem_nonZeroDivisors_iff_ne_zero.mp ha,
    IsLocalization.integerNormalization R⁰ p,?_⟩
  rw [hq,← algebraMap_smul K a p,Polynomial.smul_eq_C_mul]

theorem squarefree_relation_off_denominator
    {R K : Type*} [CommRing R] [IsDomain R] [Field K] [CharZero K]
    [Algebra R K] [IsFractionRing R K]
    (p : R[X]) (hp : p ≠ 0) :
    ∃ q : R[X], q ≠ 0 ∧ (q.map (algebraMap R K)).Separable ∧
      ∃ D : R, D ≠ 0 ∧
        ∀ {F : Type*} [Field F] (e : R →+* F), e D ≠ 0 →
          ∀ z : F, p.eval₂ e z = 0 ↔ q.eval₂ e z = 0 := by
  classical
  let e := algebraMap R K
  have hei : Function.Injective e := IsFractionRing.injective R K
  have hmap : Function.Injective (Polynomial.map e) := Polynomial.map_injective e hei
  have hp' : p.map e ≠ 0 := fun hz => hp (hmap (by simpa only [Polynomial.map_zero] using hz))
  obtain ⟨v,m,hv,hvp,hpv⟩ := exists_squarefree_dvd_pow_of_ne_zero hp'
  have hv0 : v ≠ 0 := by rintro rfl; exact hp' (by simpa using hvp)
  have hvsep : v.Separable := PerfectField.separable_iff_squarefree.mpr hv
  obtain ⟨w,hw⟩ := hvp
  obtain ⟨j,hj⟩ := hpv
  obtain ⟨a,ha,q,hq⟩ := polynomial_clear_denominators (R := R) v
  obtain ⟨b,hb,W,hW⟩ := polynomial_clear_denominators (R := R) w
  obtain ⟨c,hc,J,hJ⟩ := polynomial_clear_denominators (R := R) j
  have haK : e a ≠ 0 := by simpa only [map_zero] using hei.ne_iff.mpr ha
  have hq0 : q ≠ 0 := by
    intro hz
    rw [hz,Polynomial.map_zero] at hq
    exact (mul_ne_zero (Polynomial.C_ne_zero.mpr haK) hv0) hq.symm
  have hqs : (q.map e).Separable := by
    rw [hq]
    exact Polynomial.Separable.unit_mul (IsUnit.map C (isUnit_iff_ne_zero.mpr haK)) hvsep
  have h₁ : q*W = C (a*b)*p := by
    apply hmap
    simp only [Polynomial.map_mul,Polynomial.map_C,map_mul]
    rw [hq,hW,hw]
    dsimp only [e]
    ring
  have h₂ : C c*q^m = C (a^m)*p*J := by
    apply hmap
    simp only [Polynomial.map_mul,Polynomial.map_C,Polynomial.map_pow,map_pow]
    rw [hq,hJ,mul_pow,← Polynomial.C_pow,hj]
    dsimp only [e]
    ring
  refine ⟨q,hq0,hqs,a*b*c,mul_ne_zero (mul_ne_zero ha hb) hc,?_⟩
  intro F _ f hf z
  have hab : f (a*b) ≠ 0 := fun hz => hf (by simp only [map_mul,hz,zero_mul])
  have hc' : f c ≠ 0 := fun hz => hf (by simp only [map_mul,hz,mul_zero])
  constructor
  · intro hz
    have he := congrArg (Polynomial.eval₂ f z) h₂
    simp only [Polynomial.eval₂_mul,Polynomial.eval₂_C,Polynomial.eval₂_pow,hz,mul_zero,zero_mul] at he
    have hpw : (q.eval₂ f z)^m = 0 := (mul_eq_zero.mp he).resolve_left hc'
    by_contra hn
    exact pow_ne_zero m hn hpw
  · intro hz
    have he := congrArg (Polynomial.eval₂ f z) h₁
    simp only [Polynomial.eval₂_mul,Polynomial.eval₂_C,hz,zero_mul] at he
    exact (mul_eq_zero.mp he.symm).resolve_left hab

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_RealPolynomialAnalyticRoot
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Polynomial

theorem polynomial_gcd_specialization_data
    {R K : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (p q : R[X]) :
    ∃ a b c : R, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧
      ∃ A B C' U V : R[X],
        C a*p = A*B ∧ C b*q = A*C' ∧ C c*A = p*U+q*V := by
  classical
  let e := algebraMap R K
  have hi : Function.Injective (Polynomial.map e) :=
    Polynomial.map_injective e (IsFractionRing.injective R K)
  let g := EuclideanDomain.gcd (p.map e) (q.map e)
  obtain ⟨w,hw⟩ := EuclideanDomain.gcd_dvd_left (p.map e) (q.map e)
  obtain ⟨j,hj⟩ := EuclideanDomain.gcd_dvd_right (p.map e) (q.map e)
  change p.map e = g*w at hw
  change q.map e = g*j at hj
  obtain ⟨a,ha,A,hA⟩ := polynomial_clear_denominators (R := R) g
  obtain ⟨b,hb,B,hB⟩ := polynomial_clear_denominators (R := R) w
  obtain ⟨c,hc,C',hC⟩ := polynomial_clear_denominators (R := R) j
  obtain ⟨u,hu,U,hU⟩ := polynomial_clear_denominators (R := R)
    (EuclideanDomain.gcdA (p.map e) (q.map e))
  obtain ⟨v,hv,V,hV⟩ := polynomial_clear_denominators (R := R)
    (EuclideanDomain.gcdB (p.map e) (q.map e))
  refine ⟨a*b,a*c,u*v,mul_ne_zero ha hb,mul_ne_zero ha hc,mul_ne_zero hu hv,
    A,B,C',C (a*v)*U,C (a*u)*V,?_,?_,?_⟩
  · apply hi
    simp only [Polynomial.map_mul,Polynomial.map_C,map_mul]
    rw [hA,hB,hw]
    dsimp only [e]
    ring
  · apply hi
    simp only [Polynomial.map_mul,Polynomial.map_C,map_mul]
    rw [hA,hC,hj]
    dsimp only [e]
    ring
  · apply hi
    simp only [Polynomial.map_mul,Polynomial.map_C,map_mul,Polynomial.map_add]
    rw [hA,hU,hV]
    dsimp only [g,e]
    rw [EuclideanDomain.gcd_eq_gcd_ab]
    ring

end

theorem real_analytic_local_inverse
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E → F} {a : E} (hf : AnalyticAt ℝ f a)
    (i : E ≃L[ℝ] F) (hi : HasFDerivAt f (i : E →L[ℝ] F) a) :
    ∃ e : OpenPartialHomeomorph E F, (e : E → F) = f ∧ a ∈ e.source ∧
      AnalyticAt ℝ e.symm (f a) := by
  have hs : HasStrictFDerivAt f (i : E →L[ℝ] F) a := by
    simpa only [hi.fderiv] using hf.hasStrictFDerivAt
  let e := hs.toOpenPartialHomeomorph f
  refine ⟨e, hs.toOpenPartialHomeomorph_coe, hs.mem_toOpenPartialHomeomorph_source, ?_⟩
  obtain ⟨p, hp⟩ := hf
  have he : (e : E → F) = f := hs.toOpenPartialHomeomorph_coe
  have hpe : HasFPowerSeriesAt e p a := he ▸ hp
  have hcoeff : p 1 = (continuousMultilinearCurryFin1 ℝ E F).symm
      (i : E →L[ℝ] F) := by
    apply (continuousMultilinearCurryFin1 ℝ E F).injective
    simpa using hp.hasFDerivAt.unique hi
  simpa only [he] using
    (e.hasFPowerSeriesAt_symm hs.mem_toOpenPartialHomeomorph_source hpe hcoeff).analyticAt

theorem real_analytic_implicit_scalar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : E × ℝ → ℝ} {a : E} {b : ℝ}
    (hF : AnalyticAt ℝ F (a, b)) (hzero : F (a, b) = 0)
    (L : E × ℝ →L[ℝ] ℝ) (hL : HasFDerivAt F L (a, b))
    (hsimple : L (0, 1) ≠ 0) :
    ∃ g : E → ℝ, AnalyticAt ℝ g a ∧ g a = b ∧
      (∀ᶠ y in 𝓝 a, F (y, g y) = 0) ∧
      (∀ᶠ p in 𝓝 (a, b), F p = 0 → p.2 = g p.1) := by
  let G : E × ℝ → E × ℝ := fun p => (p.1, F p)
  have hG : AnalyticAt ℝ G (a, b) :=
    ((ContinuousLinearMap.fst ℝ E ℝ).analyticAt (a, b)).prod hF
  have hdG : HasFDerivAt G (real_triangularDifferentialEquiv L hsimple : _ →L[ℝ] _) (a, b) :=
    hasFDerivAt_fst.prodMk hL
  obtain ⟨e, he, hmem, hia⟩ := real_analytic_local_inverse hG
    (real_triangularDifferentialEquiv L hsimple) hdG
  have hGab : G (a, b) = (a, 0) := by simp [G, hzero]
  rw [hGab] at hia
  let g : E → ℝ := fun y => (e.symm (y, 0)).2
  have hiac : AnalyticAt ℝ (fun y : E => e.symm (y, 0)) a :=
    hia.comp (f := fun y : E => (y, 0))
      ((ContinuousLinearMap.inl ℝ E ℝ).analyticAt a)
  have hg : AnalyticAt ℝ g a :=
    ((ContinuousLinearMap.snd ℝ E ℝ).analyticAt _).comp hiac
  have hsource : e.symm (a, 0) = (a, b) := by
    rw [← hGab, ← he]
    exact e.left_inv hmem
  refine ⟨g, hg, congrArg Prod.snd hsource, ?_, ?_⟩
  · have hright := e.eventually_right_inverse' hmem
    rw [he, hGab] at hright
    have ht : Tendsto (fun y : E => (y, (0 : ℝ))) (𝓝 a) (𝓝 (a, 0)) :=
      (continuous_id.prodMk continuous_const).continuousAt.tendsto
    filter_upwards [ht.eventually hright] with y hy
    have hfst : (e.symm (y, 0)).1 = y := congrArg Prod.fst hy
    have hsnd : F (e.symm (y, 0)) = 0 := congrArg Prod.snd hy
    change F (y, (e.symm (y, 0)).2) = 0
    have hpair : (y, (e.symm (y, 0)).2) = e.symm (y, 0) :=
      Prod.ext hfst.symm rfl
    rw [hpair]
    exact hsnd
  · have hleft := e.eventually_left_inverse hmem
    rw [he] at hleft
    filter_upwards [hleft] with p hp hz
    have hGp : G p = (p.1, 0) := by simp [G, hz]
    rw [hGp] at hp
    exact (congrArg Prod.snd hp).symm

theorem real_polynomial_analytic_root {d : ℕ}
    (P : Polynomial (MvPolynomial (Fin d) ℝ)) (a : Fin d → ℝ) (b : ℝ)
    (hroot : Polynomial.eval₂ (MvPolynomial.eval a) b P = 0)
    (hsimple : Polynomial.eval₂ (MvPolynomial.eval a) b P.derivative ≠ 0) :
    ∃ g : (Fin d → ℝ) → ℝ, AnalyticAt ℝ g a ∧ g a = b ∧
      (∀ᶠ y in 𝓝 a, Polynomial.eval₂ (MvPolynomial.eval y) (g y) P = 0) ∧
      (∀ᶠ p in 𝓝 (a, b), Polynomial.eval₂ (MvPolynomial.eval p.1) p.2 P = 0 →
        p.2 = g p.1) := by
  let F : ((Fin d → ℝ) × ℝ) → ℝ := fun p =>
    Polynomial.eval₂ (MvPolynomial.eval p.1) p.2 P
  have hF : AnalyticAt ℝ F (a, b) := by
    have hpoly : ∀ j : ℕ, AnalyticAt ℝ
        (fun p : ((Fin d → ℝ) × ℝ) => MvPolynomial.eval p.1 (P.coeff j)) (a, b) := by
      intro j
      exact (AnalyticOnNhd.eval_mvPolynomial (P.coeff j) _ (Set.mem_univ _)).comp
        ((ContinuousLinearMap.fst ℝ (Fin d → ℝ) ℝ).analyticAt _)
    simp only [F, Polynomial.eval₂_eq_sum_range]
    exact
      Finset.analyticAt_fun_sum (Finset.range (P.natDegree + 1)) (fun j _ =>
        (hpoly j).mul (((ContinuousLinearMap.snd ℝ (Fin d → ℝ) ℝ).analyticAt _).pow j))
  let L := fderiv ℝ F (a,b)
  have hL : HasFDerivAt F L (a,b) := hF.differentiableAt.hasFDerivAt
  have hv : L (0,1) = Polynomial.eval₂ (MvPolynomial.eval a) b P.derivative := by
    have h1 : HasDerivAt (fun z => F (a,z)) (L (0,1)) b :=
      hL.comp_hasDerivAt b ((hasDerivAt_const b a).prodMk (hasDerivAt_id b))
    have h2 := (P.map (MvPolynomial.eval a)).hasDerivAt b
    simp only [Polynomial.derivative_map, Polynomial.eval_map] at h2
    exact h1.unique h2
  exact real_analytic_implicit_scalar hF hroot L hL (hv ▸ hsimple)

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_RegularSimpleSheet
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Polynomial Set Filter Topology

lemma continuousAt_real_parameter_eval {n : ℕ}
    (P : Polynomial (MvPolynomial (Fin n) ℝ))
    {g : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (hg : ContinuousAt g x) :
    ContinuousAt (fun y => P.eval₂ (MvPolynomial.eval y) (g y)) x := by
  simp only [Polynomial.eval₂_eq_sum_range]
  exact tendsto_finsetSum _ (fun j _ =>
    (MvPolynomial.continuous_eval (P.coeff j)).continuousAt.mul (hg.pow j))

theorem polynomial_zero_persists_on_simple_sheet {n : ℕ}
    (P Q : Polynomial (MvPolynomial (Fin n) ℝ)) :
    ∃ D : MvPolynomial (Fin n) ℝ, D ≠ 0 ∧
      ∀ (g : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ), ContinuousAt g x →
        (∀ᶠ y in 𝓝 x, P.eval₂ (MvPolynomial.eval y) (g y) = 0) →
        P.derivative.eval₂ (MvPolynomial.eval x) (g x) ≠ 0 →
        MvPolynomial.eval x D ≠ 0 → Q.eval₂ (MvPolynomial.eval x) (g x) = 0 →
        ∀ᶠ y in 𝓝 x, Q.eval₂ (MvPolynomial.eval y) (g y) = 0 := by
  obtain ⟨a,b,c,ha,hb,hc,A,B,C',U,V,h₁,h₂,h₃⟩ :=
    polynomial_gcd_specialization_data (K := FractionRing (MvPolynomial (Fin n) ℝ)) P Q
  refine ⟨a*b*c,mul_ne_zero (mul_ne_zero ha hb) hc,?_⟩
  intro g x hg hP hs hD hQ
  have ha' : MvPolynomial.eval x a ≠ 0 := by
    intro hz; apply hD; simp only [map_mul,hz,zero_mul]
  have hb' : MvPolynomial.eval x b ≠ 0 := by
    intro hz; apply hD; simp only [map_mul,hz,mul_zero,zero_mul]
  have hc' : MvPolynomial.eval x c ≠ 0 := by
    intro hz; apply hD; simp only [map_mul,hz,mul_zero]
  have hPx : P.eval₂ (MvPolynomial.eval x) (g x) = 0 := hP.self_of_nhds
  have hAx : A.eval₂ (MvPolynomial.eval x) (g x) = 0 := by
    have he := congrArg (Polynomial.eval₂ (MvPolynomial.eval x) (g x)) h₃
    simp only [eval₂_mul,eval₂_C,eval₂_add,hPx,hQ,zero_mul,zero_add] at he
    exact (mul_eq_zero.mp he).resolve_left hc'
  have hBx : B.eval₂ (MvPolynomial.eval x) (g x) ≠ 0 := by
    intro hz
    have hd := congrArg Polynomial.derivative h₁
    have he := congrArg (Polynomial.eval₂ (MvPolynomial.eval x) (g x)) hd
    simp only [derivative_mul,derivative_C,zero_mul,zero_add,eval₂_mul,eval₂_C,
      eval₂_add,hAx,hz,zero_mul,mul_zero,zero_add] at he
    exact hs ((mul_eq_zero.mp he).resolve_left ha')
  have hBn := (continuousAt_real_parameter_eval B hg).eventually_ne hBx
  have hbn := (MvPolynomial.continuous_eval b).continuousAt.eventually_ne hb'
  filter_upwards [hP,hBn,hbn] with y hPy hBy hby
  have hAy : A.eval₂ (MvPolynomial.eval y) (g y) = 0 := by
    have he := congrArg (Polynomial.eval₂ (MvPolynomial.eval y) (g y)) h₁
    simp only [eval₂_mul,eval₂_C,hPy,mul_zero] at he
    exact (mul_eq_zero.mp he.symm).resolve_right hBy
  have he := congrArg (Polynomial.eval₂ (MvPolynomial.eval y) (g y)) h₂
  simp only [eval₂_mul,eval₂_C,hAy,zero_mul] at he
  exact (mul_eq_zero.mp he).resolve_left hby

theorem PolynomialSignSet.regular_on_simple_sheet {n : ℕ}
    {S : Set (Option (Fin n) → ℝ)} (hS : PolynomialSignSet id S)
    (P : Polynomial (MvPolynomial (Fin n) ℝ)) :
    ∃ D : MvPolynomial (Fin n) ℝ, D ≠ 0 ∧
      ∀ (g : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ), ContinuousAt g x →
        (∀ᶠ y in 𝓝 x, P.eval₂ (MvPolynomial.eval y) (g y) = 0) →
        P.derivative.eval₂ (MvPolynomial.eval x) (g x) ≠ 0 →
        MvPolynomial.eval x D ≠ 0 →
        (∀ᶠ y in 𝓝 x, (fun o => Option.elim o (g y) y) ∈ S) ∨
        (∀ᶠ y in 𝓝 x, (fun o => Option.elim o (g y) y) ∉ S) := by
  induction hS with
  | zero q =>
    let Q := MvPolynomial.optionEquivLeft ℝ (Fin n) q
    obtain ⟨D,hD,hzero⟩ := polynomial_zero_persists_on_simple_sheet P Q
    refine ⟨D,hD,?_⟩
    intro g x hg hP hs hDx
    by_cases hz : Q.eval₂ (MvPolynomial.eval x) (g x) = 0
    · left
      simpa only [mem_ofPred,id_eq,MvPolynomial.optionEquivLeft_elim_eval,eval_map,Q] using
        hzero g x hg hP hs hDx hz
    · right
      simpa only [mem_ofPred,id_eq,MvPolynomial.optionEquivLeft_elim_eval,eval_map,Q] using
        (continuousAt_real_parameter_eval Q hg).eventually_ne hz
  | positive q =>
    let Q := MvPolynomial.optionEquivLeft ℝ (Fin n) q
    obtain ⟨D,hD,hzero⟩ := polynomial_zero_persists_on_simple_sheet P Q
    refine ⟨D,hD,?_⟩
    intro g x hg hP hs hDx
    by_cases hz : Q.eval₂ (MvPolynomial.eval x) (g x) = 0
    · right
      filter_upwards [hzero g x hg hP hs hDx hz] with y hy
      change ¬ 0 < MvPolynomial.eval (fun o => Option.elim o (g y) y) q
      rw [MvPolynomial.optionEquivLeft_elim_eval,eval_map]
      change ¬ 0 < Q.eval₂ (MvPolynomial.eval y) (g y)
      simp only [hy,lt_self_iff_false,not_false_eq_true]
    · rcases lt_or_gt_of_ne hz with hneg | hpos
      · right
        filter_upwards [(continuousAt_real_parameter_eval Q hg).eventually_lt_const hneg] with y hy
        change ¬ 0 < MvPolynomial.eval (fun o => Option.elim o (g y) y) q
        rw [MvPolynomial.optionEquivLeft_elim_eval,eval_map]
        exact not_lt_of_ge hy.le
      · left
        simpa only [mem_ofPred,id_eq,MvPolynomial.optionEquivLeft_elim_eval,eval_map,Q] using
          (continuousAt_real_parameter_eval Q hg).eventually_const_lt hpos
  | @compl S hS ih =>
    obtain ⟨D,hD,hreg⟩ := ih
    refine ⟨D,hD,?_⟩
    intro g x hg hP hs hDx
    simpa only [mem_compl_iff,not_not] using (hreg g x hg hP hs hDx).symm
  | @union S T hS hT ihS ihT =>
    obtain ⟨D,hD,hregD⟩ := ihS
    obtain ⟨E,hE,hregE⟩ := ihT
    refine ⟨D*E,mul_ne_zero hD hE,?_⟩
    intro g x hg hP hs hDE
    have hD' : MvPolynomial.eval x D ≠ 0 := fun hz => hDE (by simp only [map_mul,hz,zero_mul])
    have hE' : MvPolynomial.eval x E ≠ 0 := fun hz => hDE (by simp only [map_mul,hz,mul_zero])
    rcases hregD g x hg hP hs hD' with h | h
    · exact Or.inl (h.mono fun y hy => Or.inl hy)
    rcases hregE g x hg hP hs hE' with k | k
    · exact Or.inl (k.mono fun y hy => Or.inr hy)
    · right
      filter_upwards [h,k] with y hy ky
      exact fun h => h.elim hy ky

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_GenericAlgebraicRamificationUniform
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Polynomial Set Filter Topology

theorem semialgebraic_function_analytic_off_polynomial {n : ℕ}
    (B : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (hgraph : PolynomialSignSet id
      {x : Option (Fin n) → ℝ |
        (fun i => x (some i)) ∈ B ∧ x none = f (fun i => x (some i))}) :
    ∃ D : MvPolynomial (Fin n) ℝ, D ≠ 0 ∧
      ∀ a ∈ B, MvPolynomial.eval a D ≠ 0 → AnalyticAt ℝ f a := by
  obtain ⟨p,hp,hpr⟩ := semialgebraic_graph_polynomial B f hgraph
  let P := MvPolynomial.optionEquivLeft ℝ (Fin n) p
  have hP : P ≠ 0 := (MvPolynomial.optionEquivLeft ℝ (Fin n)).injective.ne hp
  obtain ⟨q,hq,hqs,D₀,hD₀,hqe⟩ :=
    squarefree_relation_off_denominator (K := FractionRing (MvPolynomial (Fin n) ℝ)) P hP
  have hres : q.resultant q.derivative ≠ 0 :=
    resultant_derivative_ne_zero_of_generic_separable q hqs
  obtain ⟨D₁,hD₁,hreg⟩ := hgraph.regular_on_simple_sheet q
  refine ⟨D₀*D₁*q.leadingCoeff*(q.resultant q.derivative),
    mul_ne_zero (mul_ne_zero (mul_ne_zero hD₀ hD₁)
      (Polynomial.leadingCoeff_ne_zero.mpr hq)) hres,?_⟩
  intro a ha hD
  have hD₀a : MvPolynomial.eval a D₀ ≠ 0 := by
    intro hz; apply hD; simp only [map_mul,hz,zero_mul]
  have hD₁a : MvPolynomial.eval a D₁ ≠ 0 := by
    intro hz; apply hD; simp only [map_mul,hz,mul_zero,zero_mul]
  have hl : MvPolynomial.eval a q.leadingCoeff ≠ 0 := by
    intro hz; apply hD; simp only [map_mul,hz,mul_zero,zero_mul]
  have hd : MvPolynomial.eval a (q.resultant q.derivative) ≠ 0 := by
    intro hz; apply hD; simp only [map_mul,hz,mul_zero]
  have hpr' : P.eval₂ (MvPolynomial.eval a) (f a) = 0 := by
    simpa only [MvPolynomial.optionEquivLeft_elim_eval,eval_map,P] using hpr a ha
  have hqr : q.eval₂ (MvPolynomial.eval a) (f a) = 0 :=
    (hqe (MvPolynomial.eval a) hD₀a (f a)).mp hpr'
  have hsep := separable_map_of_leading_resultant_ne_zero q (MvPolynomial.eval a) hl hd
  have hder : q.derivative.eval₂ (MvPolynomial.eval a) (f a) ≠ 0 := by
    have hh := Polynomial.Separable.eval₂_derivative_ne_zero (RingHom.id ℝ) hsep
      (x := f a) (by simpa only [Polynomial.eval₂_id,Polynomial.eval_map] using hqr)
    simpa only [Polynomial.eval₂_id,Polynomial.derivative_map,Polynomial.eval_map] using hh
  obtain ⟨g,hga,hgf,hgr,_⟩ := real_polynomial_analytic_root q a (f a) hqr hder
  have hder' : q.derivative.eval₂ (MvPolynomial.eval a) (g a) ≠ 0 := by
    simpa only [hgf] using hder
  rcases hreg g a hga.continuousAt hgr hder' hD₁a with hyes | hno
  · have he : g =ᶠ[𝓝 a] f := by
      filter_upwards [hyes] with y hy
      exact hy.2
    exact hga.congr he
  · have hn := hno.self_of_nhds
    exact (hn ⟨ha,hgf⟩).elim

end

open Set Filter Topology MeasureTheory Metric

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_GenericRealParameterPolynomial
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Polynomial Set Filter Topology Metric MeasureTheory

lemma complexify_mv_eval {n : ℕ} (D : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    MvPolynomial.eval (realParameter x) (MvPolynomial.map Complex.ofRealHom D) =
      (MvPolynomial.eval x D : ℂ) := by
  rw [MvPolynomial.eval_map]
  change _ = Complex.ofRealHom (MvPolynomial.eval x D)
  rw [MvPolynomial.eval₂_comp]
  rfl

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SemialgebraicOffsetLimitsFamily
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter

namespace Release061
open Set Filter Topology Metric MeasureTheory Classical
open SignElimination

theorem isSemialgebraic_iff_polynomialSignSet {n : ℕ} {S : Set (Affine n)} :
    IsSemialgebraic S ↔ PolynomialSignSet realCoordinates S := by
  constructor
  · intro h
    induction h with
    | zero p => exact .zero p
    | positive p => exact .positive p
    | compl _ ih => exact ih.compl
    | union _ _ ih ih' => exact ih.union ih'
  · intro h
    induction h with
    | zero p => exact .zero p
    | positive p => exact .positive p
    | compl _ ih => exact ih.compl
    | union _ _ ih ih' => exact ih.union ih'

lemma real_polynomial_zero_null {n : ℕ} (D : MvPolynomial (Fin n) ℝ) (hD : D ≠ 0) :
    volume {s : Fin n → ℝ | MvPolynomial.eval s D = 0} = 0 := by
  have hmap := (MvPolynomial.map_injective (σ := Fin n) Complex.ofRealHom
    Complex.ofReal_injective).ne hD
  have hn := complex_polynomial_real_zero_null
    (MvPolynomial.map Complex.ofRealHom D) (by simpa only [map_zero] using hmap)
  have he : {s : Fin n → ℝ |
      MvPolynomial.eval (fun i => (s i : ℂ)) (MvPolynomial.map Complex.ofRealHom D) = 0} =
      {s : Fin n → ℝ | MvPolynomial.eval s D = 0} := by
    ext s
    change MvPolynomial.eval (realParameter s) (MvPolynomial.map Complex.ofRealHom D) = 0 ↔
      MvPolynomial.eval s D = 0
    rw [complexify_mv_eval,Complex.ofReal_eq_zero]
  rwa [he] at hn

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AnalyticNashRefinement
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology MeasureTheory
open scoped Classical

namespace SemialgebraicOn
lemma analytic_off_polynomial {n k : ℕ} {B : Set (Fin n → ℝ)}
    {f : (Fin n → ℝ) → (Fin k → ℝ)} (hf : SemialgebraicOn B f) :
    ∃ D : MvPolynomial (Fin n) ℝ, D ≠ 0 ∧
      ∀ x ∈ B, MvPolynomial.eval x D ≠ 0 → AnalyticAt ℝ f x := by
  have hi (i : Fin k) : ∃ D : MvPolynomial (Fin n) ℝ, D ≠ 0 ∧
      ∀ x ∈ B, MvPolynomial.eval x D ≠ 0 → AnalyticAt ℝ (fun x => f x i) x := by
    have hp := (SemialgebraicOn.polynomial (B := (univ : Set (Fin k → ℝ)))
      PolynomialSignSet.univ (fun _ : Fin 1 => MvPolynomial.X i)).comp hf (fun _ _ => mem_univ _)
    have hs := hp.coordinate_preimage
      (fun x : Option (Fin n) → ℝ => ((fun i => x (some i)),fun _ => x none))
      (Sum.elim some (fun _ => none)) (d := id) (by intro x j; cases j <;> rfl)
    have he : PolynomialSignSet id
        {x : Option (Fin n) → ℝ | (fun i => x (some i)) ∈ B ∧
          x none = f (fun i => x (some i)) i} := by
      convert hs using 1
      all_goals try with_reducible_and_instances rfl
      ext x
      simp only [mem_preimage,mem_ofPred_eq,Function.comp_apply,MvPolynomial.eval_X,funext_iff,forall_const]
    exact semialgebraic_function_analytic_off_polynomial B (fun x => f x i) he
  choose D hD ha using hi
  refine ⟨∏ i, D i,Finset.prod_ne_zero_iff.mpr (fun i _ => hD i),?_⟩
  intro x hx hprod
  apply analyticAt_pi_iff.mpr
  intro i
  apply ha i x hx
  intro hz
  apply hprod
  rw [map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) hz
end SemialgebraicOn

namespace HasAnalyticNashCover
variable {n k : ℕ} {S T : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → (Fin k → ℝ)}

lemma empty : HasAnalyticNashCover (∅ : Set (Fin n → ℝ)) f := by
  exact ⟨∅,by simp,by simp⟩

lemma union (hS : HasAnalyticNashCover S f) (hT : HasAnalyticNashCover T f) :
    HasAnalyticNashCover (S ∪ T) f := by
  obtain ⟨P,hP,haP⟩ := hS
  obtain ⟨Q,hQ,haQ⟩ := hT
  refine ⟨P ∪ Q,fun x => ?_,?_⟩
  · simp only [mem_union,hP,hQ,Finset.mem_union]
    aesop
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact haP p hp
    · exact haQ p hp

lemma finite_union {α : Type*} (s : Finset α) {S : α → Set (Fin n → ℝ)}
    (hS : ∀ i ∈ s, HasAnalyticNashCover (S i) f) : HasAnalyticNashCover (⋃ i ∈ s, S i) f := by
  induction s using Finset.induction_on with
  | empty => simpa using (empty (n := n) (f := f))
  | @insert i s hi ih =>
    simpa only [Finset.mem_insert,ofPred_or,iUnion_iUnion_eq_or_left] using
      (hS i (Finset.mem_insert_self _ _)).union
        (ih (fun j hj => hS j (Finset.mem_insert_of_mem hj)))

lemma of_analytic (hS : HasFiniteNashCover S) (hf : AnalyticOnNhd ℝ f S) :
    HasAnalyticNashCover S f := by
  obtain ⟨P,hP⟩ := hS
  refine ⟨P,hP,?_⟩
  intro p hp x hx
  exact (hf _ ((hP _).mpr ⟨p,hp,x,hx,rfl⟩)).comp (p.analytic_toFun x hx)

lemma compose_patch (p : NashPatch n)
    (h : HasAnalyticNashCover p.domain (f ∘ p.toFun)) : HasAnalyticNashCover p.image f := by
  obtain ⟨P,hP,haP⟩ := h
  have hsub (q : {q // q ∈ P}) : q.val.image ⊆ p.domain := by
    intro y hy
    exact (hP y).mpr ⟨q,q.property,hy⟩
  let Q := P.attach.image (fun q => p.comp q.val (hsub q))
  refine ⟨Q,fun y => ?_,?_⟩
  · constructor
    · rintro ⟨x,hx,rfl⟩
      obtain ⟨q,hq,z,hz,he⟩ := (hP x).mp hx
      refine ⟨p.comp q (hsub ⟨q,hq⟩),Finset.mem_image.mpr ⟨⟨q,hq⟩,by simp,rfl⟩,z,hz,?_⟩
      change p.toFun (q.toFun z) = p.toFun x
      rw [he]
    · rintro ⟨r,hr,y,hy,hye⟩
      obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hr
      exact ⟨q.val.toFun y,hsub q ⟨y,hy,rfl⟩,hye⟩
  · intro r hr
    obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hr
    exact haP q.val q.property

end HasAnalyticNashCover

theorem analytic_nash_refinement (n : ℕ)
    (H : ∀ d ≤ n, ∀ S : Set (Fin d → ℝ), PolynomialSignSet id S → HasFiniteNashCover S) :
    ∀ d ≤ n, ∀ k (S : Set (Fin d → ℝ)) (f : (Fin d → ℝ) → (Fin k → ℝ)),
      SemialgebraicOn S f → HasAnalyticNashCover S f := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hdn k S f hf
    obtain ⟨D,hD,ha⟩ := hf.analytic_off_polynomial
    let G := S ∩ {x | MvPolynomial.eval x D ≠ 0}
    let E := S ∩ {x | MvPolynomial.eval x D = 0}
    have hGs : PolynomialSignSet id G := hf.domain.inter (PolynomialSignSet.zero D).compl
    have hEs : PolynomialSignSet id E := hf.domain.inter (PolynomialSignSet.zero D)
    have hG : HasAnalyticNashCover G f :=
      .of_analytic (H d hdn G hGs) (fun x hx => ha x hx.1 hx.2)
    have hE : HasAnalyticNashCover E f := by
      obtain ⟨P,hP⟩ := H d hdn E hEs
      have hpcover (p : NashPatch d) (hp : p ∈ P) : HasAnalyticNashCover p.image f := by
        have hsub : p.image ⊆ E := fun x hx => (hP x).mpr ⟨p,hp,hx⟩
        have hlt : p.dim < d := p.dim_lt_of_empty_interior
          ((volume : Measure (Fin d → ℝ)).interior_eq_empty_of_null (real_polynomial_zero_null D hD))
          (fun _ hx => (hsub hx).2)
        have hps : SemialgebraicOn p.domain (f ∘ p.toFun) := hf.comp p.semialgebraic_toFun
          (fun x hx => (hsub ⟨x,hx,rfl⟩).1)
        exact (ih p.dim hlt (p.dim_le.trans hdn) k p.domain _ hps).compose_patch p
      have he : E = ⋃ p ∈ P, p.image := by
        ext x
        simp only [mem_iUnion,hP]
        aesop
      rw [he]
      exact HasAnalyticNashCover.finite_union P hpcover
    have he : S = G ∪ E := by
      ext x
      simp only [G,E,mem_union,mem_inter_iff,mem_ofPred_eq]
      tauto
    rw [he]
    exact hG.union hE
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_Centered
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology
open scoped Classical

namespace NashPatch
variable {n : ℕ}

lemma recenter_zero (p : NashPatch n) {x : Fin p.dim → ℝ} (hx : x ∈ p.domain) :
    0 ∈ (p.recenter x).domain := by
  change (0 : Fin p.dim → ℝ)+x ∈ p.domain
  simpa only [zero_add] using hx

lemma recenter_image (p : NashPatch n) (x : Fin p.dim → ℝ) : (p.recenter x).image = p.image := by
  change (fun y : Fin p.dim → ℝ => p.toFun (y+x)) '' ((fun y => y+x) ⁻¹' p.domain) =
    p.toFun '' p.domain
  apply Set.Subset.antisymm
  · rintro _ ⟨y,hy,rfl⟩
    exact ⟨y+x,hy,rfl⟩
  · rintro _ ⟨y,hy,rfl⟩
    refine ⟨y-x,?_,?_⟩
    · change y-x+x ∈ p.domain
      simpa only [sub_add_cancel] using hy
    · change p.toFun (y-x+x) = p.toFun y
      rw [sub_add_cancel]

lemma centered_zero (p : NashPatch n) : 0 ∈ p.centered.domain :=
  p.recenter_zero p.isConnected_domain.nonempty.choose_spec

lemma centered_image (p : NashPatch n) : p.centered.image = p.image := p.recenter_image _

end NashPatch

lemma HasFiniteNashCover.centered {n : ℕ} {S : Set (Fin n → ℝ)} (hS : HasFiniteNashCover S) :
    ∃ C : Finset (NashPatch n), (∀ p ∈ C, 0 ∈ p.domain) ∧
      ∀ y, y ∈ S ↔ ∃ p ∈ C, y ∈ p.image := by
  obtain ⟨C,hC⟩ := hS
  refine ⟨C.image NashPatch.centered,?_,?_⟩
  · intro p hp
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hp
    exact p.centered_zero
  · intro y
    rw [hC y]
    constructor
    · rintro ⟨p,hp,hy⟩
      exact ⟨p.centered,Finset.mem_image.mpr ⟨p,hp,rfl⟩,p.centered_image ▸ hy⟩
    · rintro ⟨p,hp,hy⟩
      obtain ⟨a,ha,hap⟩ := Finset.mem_image.mp hp
      subst p
      exact ⟨a,ha,a.centered_image ▸ hy⟩

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_FiniteNashCoverAffine
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set
open scoped Classical

lemma hasFiniteNashCover_graph {n : ℕ} {B : Set (Fin n → ℝ)}
    {a : (Fin n → ℝ) → (Fin 1 → ℝ)} (hs : SemialgebraicOn B a)
    (hc : HasAnalyticNashCover B a) :
    HasFiniteNashCover {y : Fin (n+1) → ℝ | Fin.tail y ∈ B ∧ y 0 = a (Fin.tail y) 0} := by
  obtain ⟨P,hP,haP⟩ := hc
  have hsub (p : {p // p ∈ P}) : MapsTo p.val.toFun p.val.domain B := by
    intro x hx
    exact (hP _).mpr ⟨p,p.property,x,hx,rfl⟩
  let g (p : {p // p ∈ P}) := p.val.graph (a ∘ p.val.toFun)
    (hs.comp p.val.semialgebraic_toFun (hsub p)) (haP p p.property)
  refine ⟨P.attach.image g,fun y => ?_⟩
  constructor
  · rintro ⟨hy,he⟩
    obtain ⟨p,hp,x,hx,hxy⟩ := (hP _).mp hy
    refine ⟨g ⟨p,hp⟩,Finset.mem_image.mpr ⟨⟨p,hp⟩,by simp,rfl⟩,x,hx,?_⟩
    change Fin.cons (a (p.toFun x) 0) (p.toFun x) = y
    rw [hxy,← he,Fin.cons_self_tail]
  · rintro ⟨q,hq,x,hx,hxy⟩
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hq
    change Fin.cons (a (p.val.toFun x) 0) (p.val.toFun x) = y at hxy
    subst y
    exact ⟨hsub p hx,rfl⟩

lemma hasFiniteNashCover_affineBand {n : ℕ} {B : Set (Fin n → ℝ)}
    {f : (Fin n → ℝ) → (Fin 2 → ℝ)} (hs : SemialgebraicOn B f)
    (hc : HasAnalyticNashCover B f) (hb : ∀ x ∈ B, f x 1 ≠ 0)
    (I : Set ℝ) (hI : IsOpen I) (hcI : IsConnected I)
    (hsI : PolynomialSignSet (fun t : ℝ => fun _ : Fin 1 => t) I) :
    HasFiniteNashCover {y : Fin (n+1) → ℝ | Fin.tail y ∈ B ∧
      ∃ t ∈ I, y 0 = f (Fin.tail y) 0 + f (Fin.tail y) 1 * t} := by
  obtain ⟨P,hP,haP⟩ := hc
  have hsub (p : {p // p ∈ P}) : MapsTo p.val.toFun p.val.domain B := by
    intro x hx
    exact (hP _).mpr ⟨p,p.property,x,hx,rfl⟩
  let a (p : {p // p ∈ P}) := fun x : Fin p.val.dim → ℝ => fun _ : Fin 1 => f (p.val.toFun x) 0
  let b (p : {p // p ∈ P}) := fun x : Fin p.val.dim → ℝ => fun _ : Fin 1 => f (p.val.toFun x) 1
  have hsa (p : {p // p ∈ P}) : SemialgebraicOn p.val.domain (a p) :=
    (hs.comp p.val.semialgebraic_toFun (hsub p)).reindex (fun _ => 0)
  have hsb (p : {p // p ∈ P}) : SemialgebraicOn p.val.domain (b p) :=
    (hs.comp p.val.semialgebraic_toFun (hsub p)).reindex (fun _ => 1)
  have haa (p : {p // p ∈ P}) : AnalyticOnNhd ℝ (a p) p.val.domain := by
    intro x hx
    exact analyticAt_pi_iff.mpr (fun _ => analyticAt_pi_iff.mp (haP p p.property x hx) 0)
  have hab (p : {p // p ∈ P}) : AnalyticOnNhd ℝ (b p) p.val.domain := by
    intro x hx
    exact analyticAt_pi_iff.mpr (fun _ => analyticAt_pi_iff.mp (haP p p.property x hx) 1)
  let g (p : {p // p ∈ P}) := p.val.affineBand I hI hcI hsI (a p) (b p)
    (hsa p) (hsb p) (haa p) (hab p) (fun x hx => hb _ (hsub p hx))
  refine ⟨P.attach.image g,fun y => ?_⟩
  constructor
  · rintro ⟨hy,t,ht,he⟩
    obtain ⟨p,hp,x,hx,hxy⟩ := (hP _).mp hy
    refine ⟨g ⟨p,hp⟩,Finset.mem_image.mpr ⟨⟨p,hp⟩,by simp,rfl⟩,Fin.cons t x,⟨hx,ht⟩,?_⟩
    change Fin.cons (f (p.toFun x) 0 + f (p.toFun x) 1 * t) (p.toFun x) = y
    rw [hxy,← he,Fin.cons_self_tail]
  · rintro ⟨q,hq,x,hx,hxy⟩
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hq
    change Fin (p.val.dim+1) → ℝ at x
    change Fin.cons (f (p.val.toFun (Fin.tail x)) 0 + f (p.val.toFun (Fin.tail x)) 1 * x 0)
      (p.val.toFun (Fin.tail x)) = y at hxy
    subst y
    exact ⟨hsub p hx.1,x 0,hx.2,rfl⟩

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SortedFiberSelection
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set
open scoped Classical

namespace PolynomialSignSet
variable {X ι : Type*} {c : X → ι → ℝ} {P Q : X → Prop}
lemma iff (hP : PolynomialSignSet c {x | P x}) (hQ : PolynomialSignSet c {x | Q x}) :
    PolynomialSignSet c {x | P x ↔ Q x} := by
  convert (hP.inter hQ).union (hP.compl.inter hQ.compl) using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [mem_ofPred_eq,mem_union,mem_inter_iff,mem_compl_iff]
  tauto
lemma implies (hP : PolynomialSignSet c {x | P x}) (hQ : PolynomialSignSet c {x | Q x}) :
    PolynomialSignSet c {x | P x → Q x} := by
  convert hP.compl.union hQ using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [mem_ofPred_eq,mem_union,mem_compl_iff]
  tauto
end PolynomialSignSet

lemma sortedFiber_polynomialSignSet {X ι : Type*} {c : X → ι → ℝ}
    {R : Set (X × ℝ)}
    (hR : PolynomialSignSet (fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1)) R) (r : ℕ) :
    PolynomialSignSet (fun z : X × (Fin r → ℝ) => Sum.elim (c z.1) z.2) (SortedFiber R r) := by
  let d := fun z : X × (Fin r → ℝ) => Sum.elim (c z.1) z.2
  have hm : PolynomialSignSet d {z | StrictMono z.2} := by
    apply PolynomialSignSet.forall_finite
    intro i
    apply PolynomialSignSet.forall_finite
    intro j
    apply (PolynomialSignSet.const (c := d) (i < j)).implies
    convert PolynomialSignSet.positive (c := d)
      (MvPolynomial.X (Sum.inr j) - MvPolynomial.X (Sum.inr i)) using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    simp [d,sub_pos]
  let e := fun z : (X × (Fin r → ℝ)) × ℝ => fun o => Option.elim o z.2 (d z.1)
  have hr : PolynomialSignSet e {z | (z.1.1,z.2) ∈ R} :=
    hR.coordinate_preimage (fun z => (z.1.1,z.2)) (Option.map Sum.inl)
      (d := e) (by intro z o; cases o <;> rfl)
  have he : PolynomialSignSet e {z | ∃ i : Fin r, z.2 = z.1.2 i} := by
    apply PolynomialSignSet.exists_finite
    intro i
    convert PolynomialSignSet.zero (c := e)
      (MvPolynomial.X none - MvPolynomial.X (some (Sum.inr i))) using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    simp [e,d,sub_eq_zero]
  exact hm.inter (SignElimination.polynomialSignSet_forall_one (hr.iff he))

theorem sorted_fiber_selection {n : ℕ} {R : Set ((Fin n → ℝ) × ℝ)}
    (hR : PolynomialSignSet (fun z : (Fin n → ℝ) × ℝ => fun o => Option.elim o z.2 z.1) R)
    (r : ℕ) :
    ∃ B : Set (Fin n → ℝ), ∃ f : (Fin n → ℝ) → (Fin r → ℝ),
      PolynomialSignSet id B ∧ SemialgebraicOn B f ∧
      (∀ x, x ∈ B ↔ ∃ v, (x,v) ∈ SortedFiber R r) ∧
      ∀ x ∈ B, (x,f x) ∈ SortedFiber R r := by
  have hs := sortedFiber_polynomialSignSet (c := id) hR r
  obtain ⟨f,hf,hsf⟩ := SignElimination.polynomialSignSet_choice_finite hs
  refine ⟨{x | ∃ v, (x,v) ∈ SortedFiber R r},f,?_,hsf,fun _ => Iff.rfl,?_⟩
  · exact SignElimination.polynomialSignSet_projection_finite hs
  · exact hf
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_VerticalPieceBasePolynomial
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set
open scoped Classical

lemma verticalPiece_preconnected {r : ℕ} (v : Fin r → ℝ) (p : VerticalPiece r) :
    IsPreconnected (verticalPieceSet v p) := by
  rcases p with i | ⟨l,u⟩
  · exact isPreconnected_singleton
  · cases l <;> cases u
    · exact isPreconnected_univ
    · exact isPreconnected_Iio
    · exact isPreconnected_Ioi
    · exact isPreconnected_Ioo

lemma verticalPiece_lower {r : ℕ} (v : Fin r → ℝ) (i : Fin r) (u : Option (Fin r))
    {y : ℝ} (hy : y ∈ verticalPieceSet v (.inr (some i,u))) : v i < y := by
  cases u with
  | none => exact hy
  | some j => exact hy.1

lemma verticalPiece_upper {r : ℕ} (v : Fin r → ℝ) (j : Fin r) (l : Option (Fin r))
    {y : ℝ} (hy : y ∈ verticalPieceSet v (.inr (l,some j))) : y < v j := by
  cases l with
  | none => exact hy
  | some i => exact hy.2

lemma verticalPiece_polynomialSignSet {r : ℕ} (p : VerticalPiece r) :
    PolynomialSignSet (fun z : (Fin r → ℝ) × ℝ => fun o => Option.elim o z.2 z.1)
      {z | z.2 ∈ verticalPieceSet z.1 p} := by
  rcases p with i | ⟨l,u⟩
  · convert PolynomialSignSet.zero (c := fun z : (Fin r → ℝ) × ℝ => fun o =>
      Option.elim o z.2 z.1) (MvPolynomial.X none - MvPolynomial.X (some i)) using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    simp [verticalPieceSet,sub_eq_zero]
  · cases l with
    | none =>
      cases u with
      | none => simpa only [verticalPieceSet,mem_univ,ofPred_true] using
          (PolynomialSignSet.univ (c := fun z : (Fin r → ℝ) × ℝ => fun o => Option.elim o z.2 z.1))
      | some j =>
        convert PolynomialSignSet.positive (c := fun z : (Fin r → ℝ) × ℝ => fun o =>
          Option.elim o z.2 z.1) (MvPolynomial.X (some j) - MvPolynomial.X none) using 1
        all_goals try with_reducible_and_instances rfl
        ext z
        simp [verticalPieceSet,sub_pos]
    | some i =>
      have hl := PolynomialSignSet.positive (c := fun z : (Fin r → ℝ) × ℝ => fun o =>
          Option.elim o z.2 z.1) (MvPolynomial.X none - MvPolynomial.X (some i))
      cases u with
      | none =>
        convert hl using 1
        all_goals try with_reducible_and_instances rfl
        ext z
        simp [verticalPieceSet,sub_pos]
      | some j =>
        have hu := PolynomialSignSet.positive (c := fun z : (Fin r → ℝ) × ℝ => fun o =>
          Option.elim o z.2 z.1) (MvPolynomial.X (some j) - MvPolynomial.X none)
        convert hl.inter hu using 1
        all_goals try with_reducible_and_instances rfl
        ext z
        simp [verticalPieceSet,sub_pos]

lemma verticalPieces_cover {r : ℕ} (v : Fin r → ℝ) (S : Set ℝ)
    (H : ∀ I, IsPreconnected I → (∀ z ∈ I, ∀ i, z ≠ v i) →
      ∀ y ∈ I, ∀ z ∈ I, (y ∈ S ↔ z ∈ S)) :
    ∀ y ∈ S, ∃ p : VerticalPiece r, y ∈ verticalPieceSet v p ∧ verticalPieceSet v p ⊆ S := by
  intro y hyS
  by_cases he : ∃ i, y = v i
  · obtain ⟨i,rfl⟩ := he
    exact ⟨.inl i,mem_singleton _,by simpa only [verticalPieceSet,singleton_subset_iff] using hyS⟩
  have hleft : ∃ l : Option (Fin r),
      (∀ i, l = some i → v i < y) ∧
      (∀ j, v j < y → ∃ i, l = some i ∧ v j ≤ v i) := by
    let L := Finset.univ.filter (fun i : Fin r => v i < y)
    by_cases hL : L.Nonempty
    · obtain ⟨i,hi,him⟩ := L.exists_max_image v hL
      refine ⟨some i,?_,?_⟩
      · intro j hj
        cases Option.some.inj hj
        exact (Finset.mem_filter.mp hi).2
      · intro j hj
        exact ⟨i,rfl,him j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩)⟩
    · refine ⟨none,by simp,?_⟩
      intro j hj
      exact (hL ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩).elim
  have hright : ∃ u : Option (Fin r),
      (∀ i, u = some i → y < v i) ∧
      (∀ j, y < v j → ∃ i, u = some i ∧ v i ≤ v j) := by
    let U := Finset.univ.filter (fun i : Fin r => y < v i)
    by_cases hU : U.Nonempty
    · obtain ⟨i,hi,him⟩ := U.exists_min_image v hU
      refine ⟨some i,?_,?_⟩
      · intro j hj
        cases Option.some.inj hj
        exact (Finset.mem_filter.mp hi).2
      · intro j hj
        exact ⟨i,rfl,him j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩)⟩
    · refine ⟨none,by simp,?_⟩
      intro j hj
      exact (hU ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩).elim
  obtain ⟨l,hl,hlmax⟩ := hleft
  obtain ⟨u,hu,humin⟩ := hright
  have hy : y ∈ verticalPieceSet v (.inr (l,u)) := by
    cases l <;> cases u <;> simp only [verticalPieceSet,mem_univ,mem_Ioi,mem_Iio,mem_Ioo]
    · exact hu _ rfl
    · exact hl _ rfl
    · exact ⟨hl _ rfl,hu _ rfl⟩
  have hfree : ∀ z ∈ verticalPieceSet v (.inr (l,u)), ∀ i, z ≠ v i := by
    intro z hz i hzi
    rcases lt_or_gt_of_ne (show v i ≠ y from fun h => he ⟨i,h.symm⟩) with hi | hi
    · obtain ⟨j,hlj,hij⟩ := hlmax i hi
      subst l
      have hjz := verticalPiece_lower v j u hz
      exact (not_lt_of_ge hij) (hzi ▸ hjz)
    · obtain ⟨j,huj,hji⟩ := humin i hi
      subst u
      have hzj := verticalPiece_upper v j l hz
      exact (not_lt_of_ge hji) (hzi ▸ hzj)
  refine ⟨.inr (l,u),hy,fun z hz => ?_⟩
  exact (H _ (verticalPiece_preconnected v _) hfree y hy z hz).mp hyS

namespace SemialgebraicOn
lemma predicate {ι κ : Type*} [Finite κ] {B : Set (ι → ℝ)} {f : (ι → ℝ) → (κ → ℝ)}
    (hf : SemialgebraicOn B f) {P : Set ((ι → ℝ) × (κ → ℝ))}
    (hP : PolynomialSignSet (fun z : (ι → ℝ) × (κ → ℝ) => Sum.elim z.1 z.2) P) :
    PolynomialSignSet id {x | x ∈ B ∧ (x,f x) ∈ P} := by
  have hh := SignElimination.polynomialSignSet_projection_finite (c := id) (hf.inter hP)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [mem_ofPred_eq,mem_inter_iff]
  constructor
  · rintro ⟨hx,hp⟩
    exact ⟨f x,⟨hx,rfl⟩,hp⟩
  · rintro ⟨y,⟨hx,rfl⟩,hp⟩
    exact ⟨hx,hp⟩
end SemialgebraicOn

lemma verticalPiece_base_polynomialSignSet {n r : ℕ}
    {S : Set ((Fin n → ℝ) × ℝ)}
    (hS : PolynomialSignSet (fun z : (Fin n → ℝ) × ℝ => fun o => Option.elim o z.2 z.1) S)
    (p : VerticalPiece r) :
    PolynomialSignSet (fun z : (Fin n → ℝ) × (Fin r → ℝ) => Sum.elim z.1 z.2)
      {z | (verticalPieceSet z.2 p).Nonempty ∧ ∀ y ∈ verticalPieceSet z.2 p, (z.1,y) ∈ S} := by
  let c := fun z : (Fin n → ℝ) × (Fin r → ℝ) => Sum.elim z.1 z.2
  let d := fun z : ((Fin n → ℝ) × (Fin r → ℝ)) × ℝ => fun o => Option.elim o z.2 (c z.1)
  have hp := (verticalPiece_polynomialSignSet p).coordinate_preimage
    (fun z : ((Fin n → ℝ) × (Fin r → ℝ)) × ℝ => (z.1.2,z.2))
    (Option.map Sum.inr) (d := d) (by intro z o; cases o <;> rfl)
  have hs := hS.coordinate_preimage
    (fun z : ((Fin n → ℝ) × (Fin r → ℝ)) × ℝ => (z.1.1,z.2))
    (Option.map Sum.inl) (d := d) (by intro z o; cases o <;> rfl)
  exact (SignElimination.polynomialSignSet_projection_one hp).inter
    (SignElimination.polynomialSignSet_forall_one (hp.implies hs))

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_FiniteNashCoverVertical
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set
open scoped Classical

namespace SemialgebraicOn
lemma sub {ι κ : Type*} [Finite κ] {B : Set (ι → ℝ)} {f g : (ι → ℝ) → (κ → ℝ)}
    (hf : SemialgebraicOn B f) (hg : SemialgebraicOn B g) :
    SemialgebraicOn B (fun x => f x - g x) := by
  have hp := (polynomial (B := (univ : Set ((κ ⊕ κ) → ℝ))) PolynomialSignSet.univ
    (fun j => MvPolynomial.X (Sum.inl j) - MvPolynomial.X (Sum.inr j))).comp
      (hf.pair hg) (fun _ _ => mem_univ _)
  exact hp.congr (fun x _ => by ext j; simp)
end SemialgebraicOn

lemma hasFiniteNashCover_verticalPiece {n r : ℕ}
    (H : ∀ k (B : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → (Fin k → ℝ)),
      SemialgebraicOn B f → HasAnalyticNashCover B f)
    {B : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → (Fin r → ℝ)}
    (hs : SemialgebraicOn B f) (p : VerticalPiece r)
    (hne : ∀ x ∈ B, (verticalPieceSet (f x) p).Nonempty) :
    HasFiniteNashCover {y : Fin (n+1) → ℝ | Fin.tail y ∈ B ∧ y 0 ∈ verticalPieceSet (f (Fin.tail y)) p} := by
  have hB := hs.domain
  have hsIoi : PolynomialSignSet (fun t : ℝ => fun _ : Fin 1 => t) (Ioi 0) := by
    convert (PolynomialSignSet.positive (c := fun t : ℝ => fun _ : Fin 1 => t) (MvPolynomial.X 0)) using 1
    all_goals try with_reducible_and_instances rfl
    ext t
    simp
  have hsIoo : PolynomialSignSet (fun t : ℝ => fun _ : Fin 1 => t) (Ioo 0 1) := by
    have hu := PolynomialSignSet.positive (c := fun t : ℝ => fun _ : Fin 1 => t)
      (MvPolynomial.C 1 - MvPolynomial.X 0)
    convert hsIoi.inter hu using 1
    all_goals try with_reducible_and_instances rfl
    ext t
    simp [sub_pos]
  rcases p with i | ⟨l,u⟩
  · have ha := hs.reindex (fun _ : Fin 1 => i)
    simpa only [verticalPieceSet,mem_singleton_iff] using hasFiniteNashCover_graph ha (H 1 B _ ha)
  · cases l with
    | none =>
      cases u with
      | none =>
        let g : (Fin n → ℝ) → (Fin 2 → ℝ) := fun _ => Fin.cons 0 (fun _ => 1)
        have hg : SemialgebraicOn B g := SemialgebraicOn.constant hB _
        have hh := hasFiniteNashCover_affineBand hg (H 2 B g hg) (by intro x hx; norm_num [g])
          univ isOpen_univ isConnected_univ PolynomialSignSet.univ
        convert hh using 1
        all_goals try with_reducible_and_instances rfl
        ext y
        simp [verticalPieceSet,g]
      | some j =>
        let g : (Fin n → ℝ) → (Fin 2 → ℝ) := fun x => Fin.cons (f x j) (fun _ => -1)
        have hg : SemialgebraicOn B g := (hs.reindex (fun _ : Fin 1 => j)).finCons
          (SemialgebraicOn.constant hB (fun _ : Fin 1 => -1))
        have hh := hasFiniteNashCover_affineBand hg (H 2 B g hg) (by intro x hx; norm_num [g])
          (Ioi 0) isOpen_Ioi isConnected_Ioi hsIoi
        convert hh using 1
        all_goals try with_reducible_and_instances rfl
        ext y
        simp only [mem_ofPred_eq,verticalPieceSet,mem_Iio,mem_Ioi,g,Fin.cons_zero,Fin.cons_one,neg_mul,one_mul]
        constructor
        · rintro ⟨hy,hlt⟩
          exact ⟨hy,f (Fin.tail y) j-y 0,by linarith,by ring⟩
        · rintro ⟨hy,t,ht,he⟩
          exact ⟨hy,by linarith⟩
    | some i =>
      cases u with
      | none =>
        let g : (Fin n → ℝ) → (Fin 2 → ℝ) := fun x => Fin.cons (f x i) (fun _ => 1)
        have hg : SemialgebraicOn B g := (hs.reindex (fun _ : Fin 1 => i)).finCons
          (SemialgebraicOn.constant hB (fun _ : Fin 1 => 1))
        have hh := hasFiniteNashCover_affineBand hg (H 2 B g hg) (by intro x hx; norm_num [g])
          (Ioi 0) isOpen_Ioi isConnected_Ioi hsIoi
        convert hh using 1
        all_goals try with_reducible_and_instances rfl
        ext y
        simp only [mem_ofPred_eq,verticalPieceSet,mem_Ioi,g,Fin.cons_zero,Fin.cons_one,one_mul]
        constructor
        · rintro ⟨hy,hlt⟩
          exact ⟨hy,y 0-f (Fin.tail y) i,by linarith,by ring⟩
        · rintro ⟨hy,t,ht,he⟩
          exact ⟨hy,by linarith⟩
      | some j =>
        have hlt (x) (hx : x ∈ B) : f x i < f x j := nonempty_Ioo.mp (hne x hx)
        let g : (Fin n → ℝ) → (Fin 2 → ℝ) := fun x => Fin.cons (f x i) (fun _ => f x j-f x i)
        have hg : SemialgebraicOn B g := (hs.reindex (fun _ : Fin 1 => i)).finCons
          ((hs.reindex (fun _ : Fin 1 => j)).sub (hs.reindex (fun _ : Fin 1 => i)))
        have hh := hasFiniteNashCover_affineBand hg (H 2 B g hg)
          (by intro x hx; exact ne_of_gt (sub_pos.mpr (hlt x hx)))
          (Ioo 0 1) isOpen_Ioo (isConnected_Ioo (by norm_num)) hsIoo
        convert hh using 1
        all_goals try with_reducible_and_instances rfl
        ext y
        simp only [mem_ofPred_eq,verticalPieceSet,mem_Ioo,g,Fin.cons_zero,Fin.cons_one]
        constructor
        · rintro ⟨hy,hylo,hyhi⟩
          have hd : 0 < f (Fin.tail y) j-f (Fin.tail y) i := sub_pos.mpr (hlt _ hy)
          refine ⟨hy,(y 0-f (Fin.tail y) i)/(f (Fin.tail y) j-f (Fin.tail y) i),
            ⟨div_pos (sub_pos.mpr hylo) hd,(div_lt_one hd).mpr (by linarith)⟩,?_⟩
          field_simp
          ring
        · rintro ⟨hy,t,⟨ht0,ht1⟩,he⟩
          have hd : 0 < f (Fin.tail y) j-f (Fin.tail y) i := sub_pos.mpr (hlt _ hy)
          exact ⟨hy,by nlinarith,by nlinarith⟩

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_PolynomialSignSetFibre
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Polynomial
open scoped Classical BigOperators

theorem polynomialSignSet_fibre_roots {n : ℕ} {S : Set ((Fin n → ℝ) × ℝ)}
    (hS : PolynomialSignSet (fun z : (Fin n → ℝ) × ℝ => fun o => Option.elim o z.2 z.1) S) :
    ∃ R : Set ((Fin n → ℝ) × ℝ), ∃ N : ℕ,
      PolynomialSignSet (fun z : (Fin n → ℝ) × ℝ => fun o => Option.elim o z.2 z.1) R ∧
      (∀ x, ∃ r ≤ N, ∃ v : Fin r → ℝ, (x,v) ∈ SortedFiber R r) ∧
      ∀ x I, IsPreconnected I → (∀ y ∈ I, (x,y) ∉ R) →
        ∀ y ∈ I, ∀ z ∈ I, ((x,y) ∈ S ↔ (x,z) ∈ S) := by
  obtain ⟨s,W,hW⟩ := hS.finite_sign_description
  let Q : s → (Fin n → ℝ) → ℝ[X] := fun p x =>
    (((MvPolynomial.optionEquivLeft ℝ (Fin n)) p.val).map (MvPolynomial.eval x))
  let d : s → ℕ := fun p => ((MvPolynomial.optionEquivLeft ℝ (Fin n)) p.val).natDegree
  let R : Set ((Fin n → ℝ) × ℝ) := {z | ∃ p : s, Q p z.1 ≠ 0 ∧ (Q p z.1).eval z.2 = 0}
  have hd (p : s) (x : Fin n → ℝ) : (Q p x).natDegree ≤ d p := natDegree_map_le
  have hR : PolynomialSignSet (fun z : (Fin n → ℝ) × ℝ => fun o => Option.elim o z.2 z.1) R := by
    apply PolynomialSignSet.exists_finite
    intro p
    have hz : PolynomialSignSet id {x : Fin n → ℝ | Q p x = 0} := by
      simpa only [univ_inter] using SignElimination.zero_stratum_signSet
        (PolynomialSignSet.univ (c := id)) (Q p) (d p)
        (fun k => by
          simpa only [Q,coeff_map,id_eq] using (SignElimination.RationalOn.polynomial (c := id) (S := univ)
            (((MvPolynomial.optionEquivLeft ℝ (Fin n)) p.val).coeff k)))
        (fun x _ => hd p x)
    have hn := hz.compl.coordinate_preimage (fun z : (Fin n → ℝ) × ℝ => z.1)
      some (d := fun z o => Option.elim o z.2 z.1) (by intro z i; rfl)
    have he := PolynomialSignSet.zero (c := fun z : (Fin n → ℝ) × ℝ =>
      fun o => Option.elim o z.2 z.1) p.val
    convert hn.inter he using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    simp only [mem_preimage,mem_compl_iff,mem_inter_iff,mem_ofPred_eq,Q,SignElimination.eval_optionEquivLeft]
  refine ⟨R,∑ p, d p,hR,?_,?_⟩
  · intro x
    let F : Finset ℝ := Finset.univ.biUnion (fun p : s => (Q p x).roots.toFinset)
    have hF (y : ℝ) : y ∈ F ↔ (x,y) ∈ R := by
      simp only [F,Finset.mem_biUnion,Finset.mem_univ,true_and,Multiset.mem_toFinset,
        mem_roots',IsRoot.def,R,mem_ofPred_eq]
    have hcard : F.card ≤ ∑ p, d p := by
      calc
        F.card ≤ ∑ p : s, (Q p x).roots.toFinset.card := Finset.card_biUnion_le
        _ ≤ ∑ p : s, d p := Finset.sum_le_sum (fun p _ =>
          (Multiset.toFinset_card_le _).trans ((card_roots' _).trans (hd p x)))
    refine ⟨F.card,hcard,F.orderEmbOfFin rfl,(F.orderEmbOfFin rfl).strictMono,?_⟩
    intro y
    have he := Set.ext_iff.mp (Finset.range_orderEmbOfFin F rfl) y
    rw [← hF]
    simpa only [mem_range,Finset.mem_coe,eq_comm] using he.symm
  · intro x I hI hIR y hy z hz
    have hs (p : s) : SignType.sign ((Q p x).eval y) = SignType.sign ((Q p x).eval z) := by
      by_cases hp : Q p x = 0
      · simp only [hp,eval_zero]
      · apply hI.constant (f := fun t => SignType.sign ((Q p x).eval t)) ?_ hy hz
        intro t ht
        apply ContinuousAt.continuousWithinAt
        apply (continuousAt_sign_of_ne_zero ?_).comp (Q p x).continuous.continuousAt
        intro he
        exact hIR t ht ⟨p,hp,he⟩
    rw [hW,hW]
    have he : (fun p : s => SignType.sign (MvPolynomial.eval (fun o => Option.elim o y x) p.val)) =
        (fun p : s => SignType.sign (MvPolynomial.eval (fun o => Option.elim o z x) p.val)) := by
      funext p
      simpa only [Q,SignElimination.eval_optionEquivLeft] using hs p
    rw [he]
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SemialgebraicFiniteAnalyticNash
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set
open scoped Classical

theorem polynomialSignSet_finite_nash_cover (n : ℕ) (S : Set (Fin n → ℝ))
    (hS : PolynomialSignSet id S) : HasFiniteNashCover S := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      by_cases hne : S.Nonempty
      · have hSuniv : S = univ := by
          obtain ⟨x,hx⟩ := hne
          apply eq_univ_of_forall
          intro y
          rwa [Subsingleton.elim y x]
        rw [hSuniv]
        simpa only [NashPatch.image,NashPatch.identity,image_id] using
          HasFiniteNashCover.patch (NashPatch.identity (univ : Set (Fin 0 → ℝ))
            isOpen_univ isConnected_univ PolynomialSignSet.univ)
      · rw [not_nonempty_iff_eq_empty.mp hne]
        exact HasFiniteNashCover.empty
    | succ n =>
      have H (d : ℕ) (hd : d ≤ n) (T : Set (Fin d → ℝ)) (hT : PolynomialSignSet id T) :
          HasFiniteNashCover T := ih d (Nat.lt_succ_of_le hd) T hT
      have Ha := analytic_nash_refinement n H n le_rfl
      let S' : Set ((Fin n → ℝ) × ℝ) := {z | Fin.cons z.2 z.1 ∈ S}
      have hs : PolynomialSignSet (fun z : (Fin n → ℝ) × ℝ => fun o => Option.elim o z.2 z.1) S' := by
        exact hS.coordinate_preimage (fun z : (Fin n → ℝ) × ℝ => Fin.cons z.2 z.1)
          (Fin.cases none some) (d := fun z : (Fin n → ℝ) × ℝ => fun o => Option.elim o z.2 z.1) (by intro z i; exact Fin.cases rfl (fun _ => rfl) i)
      obtain ⟨R,N,hR,hroots,hconstant⟩ := polynomialSignSet_fibre_roots hs
      choose B f _hB hf hmem hsort using (fun r : Fin (N+1) => sorted_fiber_selection hR r.val)
      let C (r : Fin (N+1)) (p : VerticalPiece r.val) : Set (Fin n → ℝ) :=
        {x | x ∈ B r ∧ (verticalPieceSet (f r x) p).Nonempty ∧
          ∀ t ∈ verticalPieceSet (f r x) p, (x,t) ∈ S'}
      have hC (r : Fin (N+1)) (p : VerticalPiece r.val) : PolynomialSignSet id (C r p) :=
        (hf r).predicate (verticalPiece_base_polynomialSignSet hs p)
      let T (r : Fin (N+1)) (p : VerticalPiece r.val) : Set (Fin (n+1) → ℝ) :=
        {y | Fin.tail y ∈ C r p ∧ y 0 ∈ verticalPieceSet (f r (Fin.tail y)) p}
      have hT (r : Fin (N+1)) (p : VerticalPiece r.val) : HasFiniteNashCover (T r p) := by
        apply hasFiniteNashCover_verticalPiece Ha ((hf r).mono (hC r p) (fun _ hx => hx.1)) p
        exact fun _ hx => hx.2.1
      have he : S = ⋃ r ∈ (Finset.univ : Finset (Fin (N+1))),
          ⋃ p ∈ (Finset.univ : Finset (VerticalPiece r.val)), T r p := by
        ext y
        simp only [mem_iUnion,Finset.mem_univ,exists_prop,true_and]
        constructor
        · intro hy
          obtain ⟨r,hr,v,hv⟩ := hroots (Fin.tail y)
          let a : Fin (N+1) := ⟨r,Nat.lt_succ_of_le hr⟩
          have hxb : Fin.tail y ∈ B a := (hmem a _).mpr ⟨v,hv⟩
          have hyS : (Fin.tail y,y 0) ∈ S' := by
            change Fin.cons (y 0) (Fin.tail y) ∈ S
            rwa [Fin.cons_self_tail]
          have hc : ∀ I, IsPreconnected I → (∀ z ∈ I, ∀ i, z ≠ f a (Fin.tail y) i) →
              ∀ t ∈ I, ∀ z ∈ I, ((Fin.tail y,t) ∈ S' ↔ (Fin.tail y,z) ∈ S') := by
            intro I hI hfree
            apply hconstant (Fin.tail y) I hI
            intro z hz hzr
            obtain ⟨i,hei⟩ := (hsort a _ hxb).2 z |>.mp hzr
            exact hfree z hz i hei
          obtain ⟨p,hyp,hpS⟩ := verticalPieces_cover (f a (Fin.tail y))
            {t | (Fin.tail y,t) ∈ S'} hc (y 0) hyS
          exact ⟨a,p,⟨hxb,⟨y 0,hyp⟩,hpS⟩,hyp⟩
        · rintro ⟨r,p,hy,hyp⟩
          have hh := hy.2.2 (y 0) hyp
          change Fin.cons (y 0) (Fin.tail y) ∈ S at hh
          rwa [Fin.cons_self_tail] at hh
      rw [he]
      apply HasFiniteNashCover.finite_union
      intro r _
      exact HasFiniteNashCover.finite_union Finset.univ (fun p _ => hT r p)

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SemialgebraicBoundaryFiniteNash
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientAut_apply _root_.OAI.Release061.Biholomorph.ambientAut_iterate _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.derivativeAt_one _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_of_not_mem _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_one _root_.OAI.Release061.Biholomorph.inv_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.mul_apply _root_.OAI.Release061.Biholomorph.one_apply _root_.OAI.Release061.Biholomorph.pushForwardGenerator_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition _root_.OAI.Release061.ambientAction_subtype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric
open SignElimination
open scoped Classical

lemma isSemialgebraic_real_image {n : ℕ} {S : Set (Affine n)} (hS : IsSemialgebraic S) :
    PolynomialSignSet id (complexRealEquiv n '' S) := by
  have hh := (isSemialgebraic_iff_polynomialSignSet.mp hS).coordinate_preimage
    (complexRealEquiv n).symm finSumFinEquiv
    (d := id) (by intro x j; cases j <;> rfl)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [mem_image,mem_preimage]
  constructor
  · rintro ⟨z,hz,rfl⟩
    simpa using hz
  · intro hx
    exact ⟨_,hx,(complexRealEquiv n).apply_symm_apply x⟩

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SemialgebraicPolynomialNonzero
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Filter Topology MeasureTheory
open scoped Classical

theorem isSemialgebraic_centered_nash_cover_oai {n : ℕ} {S : Set (Affine n)} (hS : IsSemialgebraic S) :
    ∃ C : Finset (NashPatch (n+n)), (∀ p ∈ C, 0 ∈ p.domain) ∧
      ∀ z, z ∈ S ↔ ∃ p ∈ C, z ∈ p.complexMap '' p.domain := by
  obtain ⟨C,h0,hC⟩ := (polynomialSignSet_finite_nash_cover (n+n) _ (isSemialgebraic_real_image hS)).centered
  refine ⟨C,h0,fun z => ?_⟩
  rw [← (complexRealEquiv n).injective.mem_set_image,hC]
  apply exists_congr
  intro p
  apply and_congr_right
  intro _
  change (∃ x ∈ p.domain, p.toFun x = complexRealEquiv n z) ↔
    ∃ x ∈ p.domain, (complexRealEquiv n).symm (p.toFun x) = z
  apply exists_congr
  intro x
  apply and_congr_right
  intro _
  exact (complexRealEquiv n).symm_apply_eq.symm

end

open Set
open scoped Classical

end Release061

end

end OAI
end

theorem solution : type_of% @OAI.Release061.isSemialgebraic_centered_nash_cover_oai := @OAI.Release061.isSemialgebraic_centered_nash_cover_oai
