-- Prove2me | solution 1 for OAI.StructuralCrouzeix.optimal_metric_bundle
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T02:38:45.721666+00:00
-- url     : https://prove2.me/submissions/d780a16c-ea1e-4283-ac28-9a47067b17b2

import Mathlib
import Definitions.Def_StructuralCrouzeix
import Definitions.Def_OAIW2SC000
import Theorems.Thm_OAI_CompleteCrouzeix_AdmissibleDomain_extremal_condition_bound

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_HilbertSchmidt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_48 u_49 u_50 u_51 u_52 u_53

open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open MeasureTheory Set Complex
open scoped Topology Real
open MeasureTheory Set Metric Complex Filter
open scoped Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal InnerProductSpace
open scoped ComplexConjugate InnerProductSpace
open Set Metric Filter Complex
open scoped Topology
open MeasureTheory Set Complex
open scoped Topology
open MeasureTheory Set Complex Metric
open scoped Topology
open Set Filter Metric Complex
open scoped Topology

open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

section
open scoped InnerProductSpace
variable {m : Type u_51} [Fintype m] [instDecidableEqM : DecidableEq m]

lemma hs_inner
    {m : Type u_51} [Fintype m] [DecidableEq m] (A B : Matrix m m ℂ) :
    inner ℂ (toHS A) (toHS B) = Matrix.trace (Aᴴ * B) := by
  simp only [PiLp.inner_apply, Fintype.sum_prod_type, RCLike.inner_apply,
    Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    toHS]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

end

open MeasureTheory


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_HolomorphicEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix


universe u_61 u_62 u_63 u_64

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset
section

variable {A : Type u_61} [Ring A] [Algebra ℂ A]

lemma scalarJetEval_add {f g : ℂ → ℂ} {β : ℂ}
    (hf : AnalyticAt ℂ f β) (hg : AnalyticAt ℂ g β) (N : A) (s : ℕ) :
    scalarJetEval β N s (fun z => f z + g z) =
      scalarJetEval β N s f + scalarJetEval β N s g := by
  unfold scalarJetEval
  simp only [iteratedDeriv_fun_add hf.contDiffAt hg.contDiffAt,
    add_div, add_smul, Finset.sum_add_distrib]

lemma scalarJetEval_const {N : A} {s : ℕ} (hs : N^s = 0) (β c : ℂ) :
    scalarJetEval β N s (fun _ => c) = algebraMap ℂ A c := by
  simpa using scalarJetEval_polynomial hs β (C c)

lemma scalarJetEval_pow {f : ℂ → ℂ} {β : ℂ} (hf : AnalyticAt ℂ f β)
    {N : A} {s : ℕ} (hs : N^s = 0) (k : ℕ) :
    scalarJetEval β N s (fun z => f z ^ k) = (scalarJetEval β N s f) ^ k := by
  induction k with
  | zero => simpa using scalarJetEval_const hs β 1
  | succ k ih =>
    simp only [pow_succ]
    rw [scalarJetEval_mul (hf.fun_pow k) hf hs, ih]

lemma scalarJetEval_polynomial_comp {f : ℂ → ℂ} {β : ℂ}
    (hf : AnalyticAt ℂ f β) {N : A} {s : ℕ} (hs : N^s = 0) (p : ℂ[X]) :
    scalarJetEval β N s (fun z => p.eval (f z)) =
      Polynomial.aeval (scalarJetEval β N s f) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval_add, map_add]
    rw [scalarJetEval_add ((AnalyticOnNhd.eval_polynomial p (f β) (Set.mem_univ _)).fun_comp hf) ((AnalyticOnNhd.eval_polynomial q (f β) (Set.mem_univ _)).fun_comp hf), hp, hq]
  | monomial k c =>
    simp only [Polynomial.eval_monomial, Polynomial.aeval_monomial]
    rw [scalarJetEval_mul (analyticAt_const ..) (hf.fun_pow k) hs,
      scalarJetEval_const hs, scalarJetEval_pow hf hs]

lemma analytic_first_order_remainder {f : ℂ → ℂ} {β : ℂ}
    (hf : AnalyticAt ℂ f β) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R β ∧ ∀ᶠ z in nhds β,
      f z - f β = (z-β)*R z := by
  obtain ⟨R, hR, he⟩ := analytic_taylor_remainder hf 1
  refine ⟨R, hR, ?_⟩
  filter_upwards [he] with z hz
  simpa [jetPolynomial_eval, sub_eq_iff_eq_add, add_comm] using hz

lemma scalarJetEval_nilpotent_part {f : ℂ → ℂ} {β : ℂ}
    (hf : AnalyticAt ℂ f β) {N : A} {s : ℕ} (hs : N^s = 0) :
    (scalarJetEval β N s f - algebraMap ℂ A (f β)) ^ s = 0 := by
  obtain ⟨R, hR, he⟩ := analytic_first_order_remainder hf
  have hzero : scalarJetEval β N s (fun z => (f z - f β)^s) =
      scalarJetEval β N s (fun _ => (0 : ℂ)) := by
    apply scalarJetEval_eq_of_remainder (by fun_prop) (analyticAt_const ..) (hR.fun_pow s)
    filter_upwards [he] with z hz
    rw [sub_zero, hz, mul_pow]
  rw [scalarJetEval_pow (by fun_prop) hs,
    scalarJetEval_sub hf (analyticAt_const ..), scalarJetEval_const hs,
    scalarJetEval_const hs, map_zero] at hzero
  exact hzero

lemma scalarJetEval_comp {f g : ℂ → ℂ} {β : ℂ}
    (hf : AnalyticAt ℂ f β) (hg : AnalyticAt ℂ g (f β))
    {N : A} {s : ℕ} (hs : N^s = 0) :
    scalarJetEval β N s (fun z => g (f z)) =
      scalarJetEval (f β) (scalarJetEval β N s f - algebraMap ℂ A (f β)) s g := by
  let p := jetPolynomial (f β) s g
  obtain ⟨R, hR, he⟩ := analytic_taylor_remainder hg s
  obtain ⟨S, hS, hj⟩ := analytic_first_order_remainder hf
  have hRp : AnalyticAt ℂ (fun z => S z ^ s * R (f z)) β :=
    (hS.fun_pow s).fun_mul (hR.fun_comp hf)
  have hpoly : scalarJetEval β N s (fun z => g (f z)) =
      scalarJetEval β N s (fun z => p.eval (f z)) := by
    apply scalarJetEval_eq_of_remainder (hg.fun_comp hf) ((AnalyticOnNhd.eval_polynomial p (f β) (Set.mem_univ _)).fun_comp hf) hRp
    filter_upwards [hf.continuousAt.eventually he, hj] with z hz hw
    change g (f z) = p.eval (f z) + (f z-f β)^s * R (f z) at hz
    rw [hz, hw, mul_pow]
    ring
  rw [hpoly, scalarJetEval_polynomial_comp hf hs,
    scalarJetEval_taylor hg (scalarJetEval_nilpotent_part hf hs), sub_add_cancel]

end

open Module Set
open scoped DirectSum
variable {V : Type u_63} [AddCommGroup V] [Module ℂ V] [instFiniteDimensionalℂV : FiniteDimensional ℂ V]

lemma scalarJetEval_intertwine
    {V : Type u_63} [AddCommGroup V] [_root_.Module ℂ V] [FiniteDimensional ℂ V]
    {W : Type u_64} [AddCommGroup W] [Module ℂ W]
    (L : W →ₗ[ℂ] V) (S : Module.End ℂ W) (T : Module.End ℂ V)
    (h : ∀ x, T (L x) = L (S x)) (β : ℂ) (s : ℕ) (f : ℂ → ℂ) (x : W) :
    scalarJetEval β T s f (L x) = L (scalarJetEval β S s f x) := by
  have hp (k : ℕ) (x : W) : (T^k) (L x) = L ((S^k) x) := by
    induction k generalizing x with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, h,
        pow_succ', Module.End.mul_apply]
  simp only [scalarJetEval, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul, hp]

lemma primaryEval_on_generalized (T : Module.End ℂ V) (f : ℂ → ℂ)
    (β : ℂ) (x : T.maxGenEigenspace β) :
    primaryEval T f (x : V) =
      scalarJetEval β (T - algebraMap ℂ (Module.End ℂ V) β) (finrank ℂ V) f (x : V) := by
  rw [primaryEval_coe]
  exact (scalarJetEval_intertwine (T.maxGenEigenspace β).subtype
    (primaryNilpotent T β) (T - algebraMap ℂ (Module.End ℂ V) β)
    (fun _ => rfl) β (finrank ℂ V) f x).symm

lemma primaryEval_mapsTo_generalized (T : Module.End ℂ V) {f : ℂ → ℂ}
    (β : ℂ) (hf : AnalyticAt ℂ f β) :
    MapsTo (T.maxGenEigenspace β).subtype Set.univ
      ((primaryEval T f).maxGenEigenspace (f β)) := by
  intro x _
  change (x : V) ∈ (primaryEval T f).maxGenEigenspace (f β)
  rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank,
    Module.End.mem_genEigenspace_nat, LinearMap.mem_ker]
  have hp (k : ℕ) (x : T.maxGenEigenspace β) :
      ((primaryEval T f - algebraMap ℂ (Module.End ℂ V) (f β))^k) (x : V) =
        (((scalarJetEval β (primaryNilpotent T β) (finrank ℂ V) f -
          algebraMap ℂ (Module.End ℂ (T.maxGenEigenspace β)) (f β))^k) x : V) := by
    induction k generalizing x with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, LinearMap.sub_apply,
        primaryEval_coe, pow_succ', Module.End.mul_apply]
      rfl
  have he := hp (finrank ℂ V) x
  rw [scalarJetEval_nilpotent_part hf (primaryNilpotent_pow T β)] at he
  simpa only [Algebra.algebraMap_eq_smul_one,
    LinearMap.zero_apply, Submodule.coe_zero] using he

lemma primaryEval_comp (T : Module.End ℂ V) {f g : ℂ → ℂ}
    (hf : ∀ β ∈ spectrum ℂ T, AnalyticAt ℂ f β)
    (hg : ∀ β ∈ spectrum ℂ T, AnalyticAt ℂ g (f β)) :
    primaryEval T (fun z => g (f z)) = primaryEval (primaryEval T f) g := by
  apply primary_end_ext (T := T)
  intro β x
  by_cases hβ : β ∈ spectrum ℂ T
  · have hx : (x : V) ∈ (primaryEval T f).maxGenEigenspace (f β) :=
      primaryEval_mapsTo_generalized T β (hf β hβ) (by trivial : x ∈ Set.univ)
    rw [primaryEval_coe, primaryEval_on_generalized (primaryEval T f) g (f β) ⟨x, hx⟩]
    rw [scalarJetEval_comp (hf β hβ) (hg β hβ) (primaryNilpotent_pow T β)]
    symm
    apply scalarJetEval_intertwine (T.maxGenEigenspace β).subtype
    intro y
    change primaryEval T f (y : V) - (f β) • (y : V) = _
    rw [primaryEval_coe]
    rfl
  · have hspace : T.maxGenEigenspace β = ⊥ := by
      by_contra hn
      have he : T.HasGenEigenvalue β (finrank ℂ V) := by
        rwa [T.maxGenEigenspace_eq_genEigenspace_finrank β] at hn
      exact hβ (Module.End.hasEigenvalue_of_hasGenEigenvalue he).mem_spectrum
    have hx : x = 0 := by
      apply Subtype.ext
      simpa [hspace] using x.property
    simp [hx]

lemma primaryEval_intertwine (S T L : Module.End ℂ V)
    (h : ∀ x, T (L x) = L (S x)) (f : ℂ → ℂ) :
    primaryEval T f * L = L * primaryEval S f := by
  apply primary_end_ext (T := S)
  intro β x
  have hsub (y : V) :
      (T - algebraMap ℂ (Module.End ℂ V) β) (L y) =
        L ((S - algebraMap ℂ (Module.End ℂ V) β) y) := by
    simp only [LinearMap.sub_apply, algebraMap_end_apply, map_sub, map_smul, h]
  have hp (k : ℕ) (y : V) :
      ((T - algebraMap ℂ (Module.End ℂ V) β)^k) (L y) =
        L (((S - algebraMap ℂ (Module.End ℂ V) β)^k) y) := by
    induction k generalizing y with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, hsub, pow_succ', Module.End.mul_apply]
  have hx : L (x : V) ∈ T.maxGenEigenspace β := by
    have he := x.property
    simp only [Module.End.maxGenEigenspace_eq_genEigenspace_finrank,
      Module.End.mem_genEigenspace_nat, LinearMap.mem_ker] at he ⊢
    simpa only [Algebra.algebraMap_eq_smul_one, he, map_zero] using hp (finrank ℂ V) x
  change primaryEval T f (L x) = L (primaryEval S f x)
  rw [primaryEval_on_generalized T f β ⟨L x, hx⟩, primaryEval_on_generalized S f β x]
  exact scalarJetEval_intertwine L _ _ hsub β (finrank ℂ V) f x


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_DiskCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_65 u_66 u_67 u_68 u_69 u_70 u_71 u_72 u_73 u_74 u_75 u_76 u_77 u_78 u_79 u_80

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset

section
open Filter Topology Set Module
variable {n : Type u_67} [Fintype n] [DecidableEq n]

lemma matrixAnalyticEval_polynomial (A : Matrix n n ℂ) (p : ℂ[X]) :
    matrixAnalyticEval A (fun z => p.eval z) = Polynomial.aeval A p := by
  apply Matrix.toLinAlgEquiv'.injective
  simp only [matrixAnalyticEval, AlgEquiv.apply_symm_apply, primaryEval_polynomial,
    Polynomial.aeval_algHom_apply]

end

open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder

open MeasureTheory

open scoped Kronecker


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_CompleteResolvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_81 u_82 u_83 u_84 u_85 u_86 u_87 u_88 u_89 u_90

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset
open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder

section
open Filter Topology Set Metric Module
open scoped Matrix.Norms.L2Operator Kronecker

lemma primaryEval_add {V : Type u_85} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (T : Module.End ℂ V) {f g : ℂ → ℂ}
    (hf : ∀ z ∈ spectrum ℂ T, AnalyticAt ℂ f z)
    (hg : ∀ z ∈ spectrum ℂ T, AnalyticAt ℂ g z) :
    primaryEval T (fun z => f z + g z) = primaryEval T f + primaryEval T g := by
  apply primary_end_ext_spectrum (T := T)
  intro β hβ x
  simp only [LinearMap.add_apply, primaryEval_coe]
  rw [scalarJetEval_add (hf β hβ) (hg β hβ)]
  simp

variable {n : Type u_86} {m : Type u_87} [Fintype n] [DecidableEq n] [instFintypeM : Fintype m] [instDecidableEqM : DecidableEq m]

lemma matrixAnalyticEval_id (D : Matrix n n ℂ) :
    matrixAnalyticEval D (fun z => z) = D := by
  simpa using matrixAnalyticEval_polynomial D (Polynomial.X : ℂ[X])

lemma matrixAnalyticEval_add (D : Matrix n n ℂ) {f g : ℂ → ℂ}
    (hf : ∀ z ∈ spectrum ℂ D, AnalyticAt ℂ f z)
    (hg : ∀ z ∈ spectrum ℂ D, AnalyticAt ℂ g z) :
    matrixAnalyticEval D (fun z => f z + g z) = matrixAnalyticEval D f + matrixAnalyticEval D g := by
  apply Matrix.toLinAlgEquiv'.injective
  simp only [matrixAnalyticEval, map_add, AlgEquiv.apply_symm_apply]
  exact primaryEval_add _ (fun z hz => hf z (by simpa using hz))
    (fun z hz => hg z (by simpa using hz))

lemma matrixAnalyticEval_sum {ι : Type u_88} (s : Finset ι) (D : Matrix n n ℂ) {f : ι → ℂ → ℂ}
    (hf : ∀ i ∈ s, ∀ z ∈ spectrum ℂ D, AnalyticAt ℂ (f i) z) :
    matrixAnalyticEval D (fun z => ∑ i ∈ s, f i z) = ∑ i ∈ s, matrixAnalyticEval D (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [matrixAnalyticEval_const]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [matrixAnalyticEval_add D (hf i (Finset.mem_insert_self _ _))
      (fun z hz => Finset.analyticAt_fun_sum _ fun j hj => hf j (Finset.mem_insert_of_mem hj) z hz)]
    rw [ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

lemma completeAnalyticEval_const
    {n : Type u_86} {m : Type u_87} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (D : Matrix n n ℂ) (C : Matrix m m ℂ) :
    completeAnalyticEval D (fun _ => C) = (1 : Matrix n n ℂ) ⊗ₖ C := by
  ext i j
  simp only [completeAnalyticEval, matrixAnalyticEval_const, Algebra.algebraMap_eq_smul_one,
    Matrix.smul_apply, smul_eq_mul, Matrix.kroneckerMap_apply]
  ring

lemma completeAnalyticEval_add
    {n : Type u_86} {m : Type u_87} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (D : Matrix n n ℂ) {F G : ℂ → Matrix m m ℂ}
    (hF : ∀ i j, ∀ z ∈ spectrum ℂ D, AnalyticAt ℂ (fun z => F z i j) z)
    (hG : ∀ i j, ∀ z ∈ spectrum ℂ D, AnalyticAt ℂ (fun z => G z i j) z) :
    completeAnalyticEval D (fun z => F z + G z) =
      completeAnalyticEval D F + completeAnalyticEval D G := by
  ext i j
  simp only [completeAnalyticEval, Matrix.add_apply]
  rw [matrixAnalyticEval_add D (hF _ _) (hG _ _)]
  rfl

lemma completeAnalyticEval_mul
    {n : Type u_86} {m : Type u_87} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (D : Matrix n n ℂ) {F G : ℂ → Matrix m m ℂ}
    (hF : ∀ i j, ∀ z ∈ spectrum ℂ D, AnalyticAt ℂ (fun z => F z i j) z)
    (hG : ∀ i j, ∀ z ∈ spectrum ℂ D, AnalyticAt ℂ (fun z => G z i j) z) :
    completeAnalyticEval D (fun z => F z * G z) =
      completeAnalyticEval D F * completeAnalyticEval D G := by
  ext i j
  simp only [completeAnalyticEval, Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [matrixAnalyticEval_sum Finset.univ D (f := fun k z => F z i.2 k * G z k j.2)
    (fun k _ z hz => (hF i.2 k z hz).mul (hG k j.2 z hz))]
  simp only [Matrix.sum_apply]
  simp_rw [matrixAnalyticEval_mul D (hF _ _) (hG _ _), Matrix.mul_apply]
  rw [Finset.sum_comm]

lemma completeAnalyticEval_zsmul
    {n : Type u_86} {m : Type u_87} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (D : Matrix n n ℂ) (C : Matrix m m ℂ) :
    completeAnalyticEval D (fun z => z • C) = D ⊗ₖ C := by
  ext i j
  simp only [completeAnalyticEval, Matrix.smul_apply, smul_eq_mul]
  simp only [matrixAnalyticEval_mul D (f := fun z => z) (g := fun _ => C i.2 j.2)
    (fun _ _ => analyticAt_id) (fun _ _ => analyticAt_const),
    matrixAnalyticEval_id, matrixAnalyticEval_const, Algebra.algebraMap_eq_smul_one]
  simp [Matrix.kroneckerMap_apply, mul_comm]

end

open Filter Topology Set Metric Module
open scoped Matrix.Norms.L2Operator Kronecker
variable {n : Type u_89} {m : Type u_90} [Fintype n] [DecidableEq n] [instFintypeM : Fintype m] [instDecidableEqM : DecidableEq m]

lemma completeAnalyticEval_eqOn
    {n : Type u_89} {m : Type u_90} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (D : Matrix n n ℂ) {F G : ℂ → Matrix m m ℂ}
    {U : Set ℂ} (hU : IsOpen U) (hDU : spectrum ℂ D ⊆ U) (he : EqOn F G U) :
    completeAnalyticEval D F = completeAnalyticEval D G := by
  ext i j
  unfold completeAnalyticEval
  apply congrArg (fun M : Matrix n n ℂ => M i.1 j.1)
  apply matrixAnalyticEval_eventuallyEq
  intro z hz
  filter_upwards [hU.mem_nhds (hDU hz)] with w hw
  rw [he hw]

lemma completeAnalyticEval_sub
    {n : Type u_89} {m : Type u_90} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (D : Matrix n n ℂ) {F G : ℂ → Matrix m m ℂ}
    (hF : ∀ i j, ∀ z ∈ spectrum ℂ D, AnalyticAt ℂ (fun z => F z i j) z)
    (hG : ∀ i j, ∀ z ∈ spectrum ℂ D, AnalyticAt ℂ (fun z => G z i j) z) :
    completeAnalyticEval D (fun z => F z - G z) =
      completeAnalyticEval D F - completeAnalyticEval D G := by
  ext i j
  simp only [completeAnalyticEval, Matrix.sub_apply]
  rw [matrixAnalyticEval_sub D (hF _ _) (hG _ _)]
  rfl

lemma matrix_entry_analytic {f : ℂ → Matrix m m ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (i j : m) : AnalyticAt ℂ (fun w => f w i j) z := by
  let L : Matrix m m ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun M => M i j, map_add' := by intros; rfl, map_smul' := by intros; rfl }
  exact (L.toContinuousLinearMap.analyticAt (f z)).comp hf

lemma complete_resolvent_inverse_of_isUnit {D : Matrix n n ℂ} (hD : spectralRadius ℂ D < 1)
    {a : Matrix m m ℂ} (ha : ∀ z ∈ ball (0:ℂ) 1, IsUnit (1-z • a)) :
    completeAnalyticEval D (fun z => (1-z • a)⁻¹) * (1-D ⊗ₖ a) = 1 := by
  have hspec : spectrum ℂ D ⊆ ball (0:ℂ) 1 := fun z hz =>
    mem_ball_zero_iff.mpr (stable_spectrum_norm_lt_one hD hz)
  have hR i j z hz := matrix_entry_analytic (scalar_matrix_inverse_analytic (ha z (hspec hz))) i j
  have hM i j (z:ℂ) : AnalyticAt ℂ (fun w => (1-w • a) i j) z := by
    apply matrix_entry_analytic
    fun_prop
  have he : completeAnalyticEval D (fun z => (1-z • a)⁻¹*(1-z • a)) = 1 := by
    rw [completeAnalyticEval_eqOn D isOpen_ball hspec (G := fun _ => (1 : Matrix m m ℂ))]
    · rw [completeAnalyticEval_const, Matrix.one_kronecker_one]
    · intro z hz
      apply Matrix.nonsing_inv_mul
      apply (Matrix.isUnit_iff_isUnit_det _).mp
      exact ha z hz
  rw [completeAnalyticEval_mul D hR (fun i j z _ => hM i j z)] at he
  have hm : completeAnalyticEval D (fun z => (1 : Matrix m m ℂ)-z • a) = 1-D ⊗ₖ a := by
    rw [completeAnalyticEval_sub D (F := fun _ => (1 : Matrix m m ℂ)) (G := fun z => z • a)
      (fun _ _ _ _ => analyticAt_const)
      (fun i j z _ => matrix_entry_analytic (by fun_prop) i j),
      completeAnalyticEval_const, Matrix.one_kronecker_one, completeAnalyticEval_zsmul]
  rwa [hm] at he


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_PolynomialCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_91 u_92 u_93 u_94 u_95 u_96 u_97 u_98 u_99 u_100 u_101 u_102 u_103 u_104 u_105 u_106 u_107

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset
open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder

section
open Filter Topology Set Metric Module
open scoped Matrix.Norms.L2Operator Kronecker
variable {n : Type u_91} [Fintype n] [DecidableEq n]

lemma kronecker_vectorize {m : Type u_95} [Fintype m] [DecidableEq m]
    (A : Matrix n n ℂ) (B : Matrix m m ℂ) (X : Matrix n m ℂ) :
    Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) (A ⊗ₖ B) (vectorize X) =
      vectorize (A*X*Bᵀ) := by
  apply PiLp.ext
  rintro ⟨i,j⟩
  change (Matrix.kronecker A B *ᵥ (fun p => X p.1 p.2)) (i,j) = (A*X*Bᵀ) i j
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  change A i l * B j k * X l k = _
  ring

lemma transposed_resolvent_unit {a : Matrix n n ℂ} (ha : ‖a‖ ≤ 1) {z : ℂ}
    (hz : z ∈ ball (0:ℂ) 1) : IsUnit (1-z • aᵀ) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have hu : IsUnit (1-z • a) := isUnit_one_sub_of_norm_lt_one (by
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_left ha (norm_nonneg z)).trans_lt
      (by simpa only [mul_one] using mem_ball_zero_iff.mp hz))
  have he : (1-z • aᵀ) = (1-z • a)ᵀ := by simp
  rw [he, Matrix.det_transpose]
  exact (Matrix.isUnit_iff_isUnit_det _).mp hu

lemma evaluate_transposedTransfer {D a b c d : Matrix n n ℂ}
    (hD : spectralRadius ℂ D < 1) (ha : ‖a‖ ≤ 1) :
    completeAnalyticEval D (transposedTransfer a b c d) =
      (1 : Matrix n n ℂ) ⊗ₖ dᵀ + (D ⊗ₖ bᵀ) *
        completeAnalyticEval D (fun z => (1-z • aᵀ)⁻¹) * ((1 : Matrix n n ℂ) ⊗ₖ cᵀ) := by
  have hR (i j : n) (z : ℂ) (hz : z ∈ spectrum ℂ D) := matrix_entry_analytic
    (scalar_matrix_inverse_analytic (transposed_resolvent_unit ha
      (mem_ball_zero_iff.mpr (stable_spectrum_norm_lt_one hD hz)))) i j
  have hZ i j (z:ℂ) : AnalyticAt ℂ (fun w => (w • bᵀ) i j) z := by
    apply matrix_entry_analytic
    fun_prop
  have hP (i j : n) (z : ℂ) (hz : z ∈ spectrum ℂ D) : AnalyticAt ℂ (fun (w : ℂ) => ((w • bᵀ)*(1-w • aᵀ)⁻¹) i j) z := by
    simp only [Matrix.mul_apply]
    exact Finset.analyticAt_fun_sum _ fun k _ => (hZ i k z).mul (hR k j z hz)
  have hQ (i j : n) (z : ℂ) (hz : z ∈ spectrum ℂ D) : AnalyticAt ℂ (fun (w : ℂ) => (((w • bᵀ)*(1-w • aᵀ)⁻¹)*cᵀ) i j) z := by
    simp only [Matrix.mul_apply]
    exact Finset.analyticAt_fun_sum _ fun k _ => (hP i k z hz).mul analyticAt_const
  unfold transposedTransfer
  rw [completeAnalyticEval_add D (F := fun _ => dᵀ)
    (G := fun w => (w • bᵀ)*(1-w • aᵀ)⁻¹*cᵀ) (fun _ _ _ _ => analyticAt_const) hQ,
    completeAnalyticEval_mul D (F := fun w => (w • bᵀ)*(1-w • aᵀ)⁻¹)
      (G := fun _ => cᵀ) hP (fun _ _ _ _ => analyticAt_const),
    completeAnalyticEval_mul D (F := fun w => w • bᵀ) (G := fun w => (1-w • aᵀ)⁻¹)
      (fun i j z _ => hZ i j z) hR,
    completeAnalyticEval_const, completeAnalyticEval_const, completeAnalyticEval_zsmul]

lemma actual_transfer_extremal_evaluation {D a b c d L X Y : Matrix n n ℂ}
    (hD : spectralRadius ℂ D < 1) (ha : ‖a‖ ≤ 1)
    (hL : L = D*L*a+X*c) (hY : Y = D*L*b+X*d) :
    Matrix.toEuclideanCLM (n := n × n) (𝕜 := ℂ) (completeAnalyticEval D (transposedTransfer a b c d))
      (vectorize X) = vectorize Y := by
  let R := completeAnalyticEval D (fun z => (1-z • aᵀ)⁻¹)
  have hRQ : R * (1-D ⊗ₖ aᵀ) = 1 :=
    complete_resolvent_inverse_of_isUnit hD (fun _ hz => transposed_resolvent_unit ha hz)
  have hLsub : L-D*L*a = X*c := sub_eq_iff_eq_add.mpr (by simpa [add_comm] using hL)
  have hQ : Matrix.toEuclideanCLM (n := n × n) (𝕜 := ℂ) (1-D ⊗ₖ aᵀ) (vectorize L) = vectorize (X*c) := by
    rw [map_sub, map_one, sub_apply, one_apply_eq_self,
      kronecker_vectorize, Matrix.transpose_transpose]
    change vectorizeCLM L - vectorizeCLM (D*L*a) = vectorizeCLM (X*c)
    rw [← map_sub, hLsub]
  have hRX : Matrix.toEuclideanCLM (n := n × n) (𝕜 := ℂ) R (vectorize (X*c)) = vectorize L := by
    rw [← hQ, ← mul_apply_eq_comp, ← map_mul, hRQ,
      map_one, one_apply_eq_self]
  rw [evaluate_transposedTransfer hD ha, map_add, add_apply]
  simp only [map_mul, mul_apply_eq_comp]
  rw [kronecker_vectorize, kronecker_vectorize]
  simp only [Matrix.one_mul, Matrix.transpose_transpose]
  change vectorize (X*d) + Matrix.toEuclideanCLM (n := n × n) (𝕜 := ℂ) (D ⊗ₖ bᵀ)
    (Matrix.toEuclideanCLM (n := n × n) (𝕜 := ℂ) R (vectorize (X*c))) = vectorize Y
  rw [hRX, kronecker_vectorize, Matrix.transpose_transpose]
  change vectorizeCLM (X*d) + vectorizeCLM (D*L*b) = vectorizeCLM Y
  rw [← map_add]
  congr 1
  simpa [add_comm] using hY.symm

end

section
open Filter Topology Set Metric Module
open scoped Matrix.Norms.L2Operator Kronecker
variable {n : Type u_96} {m : Type u_97} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

lemma matrixAnalyticEval_comp (A : Matrix n n ℂ) {f g : ℂ → ℂ}
    (hf : ∀ z ∈ spectrum ℂ A, AnalyticAt ℂ f z)
    (hg : ∀ z ∈ spectrum ℂ A, AnalyticAt ℂ g (f z)) :
    matrixAnalyticEval A (fun z => g (f z)) = matrixAnalyticEval (matrixAnalyticEval A f) g := by
  apply Matrix.toLinAlgEquiv'.injective
  simp only [matrixAnalyticEval, AlgEquiv.apply_symm_apply]
  exact primaryEval_comp _ (fun z hz => hf z (by simpa using hz))
    (fun z hz => hg z (by simpa using hz))

lemma completeAnalyticEval_comp
    {n : Type u_96} {m : Type u_97} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (A : Matrix n n ℂ) {f : ℂ → ℂ} {F : ℂ → Matrix m m ℂ}
    (hf : ∀ z ∈ spectrum ℂ A, AnalyticAt ℂ f z)
    (hF : ∀ i j, ∀ z ∈ spectrum ℂ A, AnalyticAt ℂ (fun w => F w i j) (f z)) :
    completeAnalyticEval A (fun z => F (f z)) = completeAnalyticEval (matrixAnalyticEval A f) F := by
  ext i j
  simp only [completeAnalyticEval]
  rw [matrixAnalyticEval_comp A hf (hF _ _)]

lemma matrixAnalyticEval_intertwine (A B L : Matrix n n ℂ) (hL : A*L=L*B) (f : ℂ → ℂ) :
    matrixAnalyticEval A f * L = L * matrixAnalyticEval B f := by
  apply Matrix.toLinAlgEquiv'.injective
  simp only [map_mul, matrixAnalyticEval, AlgEquiv.apply_symm_apply]
  apply primaryEval_intertwine
  intro x
  have he := congrArg (Matrix.toLinAlgEquiv' : Matrix n n ℂ ≃ₐ[ℂ] Module.End ℂ (n → ℂ)) hL
  simp only [map_mul] at he
  exact LinearMap.congr_fun he x

lemma matrixAnalyticEval_similarity {S : Matrix n n ℂ} (hS : IsUnit S)
    (A : Matrix n n ℂ) (f : ℂ → ℂ) :
    matrixAnalyticEval (S*A*S⁻¹) f = S*matrixAnalyticEval A f*S⁻¹ := by
  have hi : S⁻¹*S=1 := Matrix.nonsing_inv_mul S ((Matrix.isUnit_iff_isUnit_det S).mp hS)
  have hi' : S*S⁻¹=1 := Matrix.mul_nonsing_inv S ((Matrix.isUnit_iff_isUnit_det S).mp hS)
  have he := matrixAnalyticEval_intertwine (S*A*S⁻¹) A S (by rw [mul_assoc, mul_assoc, hi, mul_one]) f
  have h := congrArg (fun M => M*S⁻¹) he
  simpa only [mul_assoc, hi', mul_one] using h

end

open Filter Topology Set Metric Module
open scoped Matrix.Norms.L2Operator Kronecker


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_UnitaryRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix


universe u_157 u_158 u_159 u_160 u_161 u_162 u_163 u_164 u_165 u_166 u_167 u_168 u_169 u_170 u_171 u_172 u_173 u_174 u_175 u_176

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset


open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder


section
open scoped InnerProductSpace
variable {E : Type u_173} {V : Type u_174} [NormedAddCommGroup E] [NormedAddCommGroup V]
  [InnerProductSpace ℂ E] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

theorem exists_unitary_intertwining (f g : E →ₗ[ℂ] V)
    (hn : ∀ x, ‖f x‖ = ‖g x‖) :
    ∃ U : V ≃ₗᵢ[ℂ] V, ∀ x, U (f x) = g x := by
  have hk : LinearMap.ker f ≤ LinearMap.ker g := by
    intro x hx
    change g x = 0
    apply norm_eq_zero.mp
    rw [← hn, LinearMap.mem_ker.mp hx, norm_zero]
  let L : LinearMap.range f →ₗ[ℂ] V :=
    ((LinearMap.ker f).liftQ g hk).comp f.quotKerEquivRange.symm.toLinearMap
  have hL (x : E) (hx : f x ∈ LinearMap.range f) : L ⟨f x,hx⟩ = g x := by
    simp only [L,LinearMap.comp_apply,LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image]
    exact Submodule.liftQ_apply _ _ x
  have hnL : ∀ v : LinearMap.range f, ‖L v‖ = ‖v‖ := by
    intro v
    obtain ⟨x,hx⟩ := v.property
    have he : v = ⟨f x,LinearMap.mem_range_self f x⟩ := Subtype.ext hx.symm
    rw [he,hL]
    exact (hn x).symm
  let I : LinearMap.range f →ₗᵢ[ℂ] V := { toLinearMap := L, norm_map' := hnL }
  let U : V →ₗᵢ[ℂ] V := I.extend
  have hs : Function.Surjective U :=
    LinearMap.surjective_of_injective (f := U.toLinearMap) U.injective
  refine ⟨LinearIsometryEquiv.ofSurjective U hs,?_⟩
  intro x
  change I.extend (f x) = g x
  rw [← show (⟨f x,LinearMap.mem_range_self f x⟩ : LinearMap.range f).val = f x from rfl,
    I.extend_apply]
  exact hL x _

variable [CompleteSpace E] [CompleteSpace V]

theorem exists_unitary_of_row_gram (R₁ R₂ : V →L[ℂ] E)
    (h : R₁.comp R₁.adjoint = R₂.comp R₂.adjoint) :
    ∃ U : V ≃ₗᵢ[ℂ] V, ∀ x, U (R₂.adjoint x) = R₁.adjoint x := by
  refine exists_unitary_intertwining R₂.adjoint.toLinearMap R₁.adjoint.toLinearMap ?_
  intro x
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hh : inner ℂ (R₂.adjoint x) (R₂.adjoint x) =
      inner ℂ (R₁.adjoint x) (R₁.adjoint x) := by
    rw [ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.adjoint_inner_left]
    exact congrArg (fun L : E →L[ℂ] E => inner ℂ x (L x)) h.symm
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),norm_sq_eq_re_inner (𝕜 := ℂ)]
  exact congrArg (RCLike.re (K := ℂ)) hh

end

open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder
section
variable {n : Type u_175} [Fintype n] [DecidableEq n]

theorem exists_unitary_matrix_of_gram (R₁ R₂ : Matrix n n ℂ)
    (h : R₁*R₁ᴴ = R₂*R₂ᴴ) :
    ∃ U : Matrix n n ℂ, Uᴴ*U = 1 ∧ U*Uᴴ = 1 ∧ R₁ = R₂*U := by
  let e := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)
  have he_mul (A B : Matrix n n ℂ) : e (A*B) = e A * e B := e.map_mul A B
  have he_star (A : Matrix n n ℂ) : e Aᴴ = (e A).adjoint := map_star e A
  have he_one : e (1 : Matrix n n ℂ) = 1 := map_one e
  have hh : (e R₁).comp (e R₁).adjoint = (e R₂).comp (e R₂).adjoint := by
    have := congrArg e h
    simpa only [he_mul,he_star,ContinuousLinearMap.mul_def] using this
  obtain ⟨u,hu⟩ := exists_unitary_of_row_gram (e R₁) (e R₂) hh
  let U := e.symm (u.symm : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
  have hU : e U = (u.symm : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) := e.apply_symm_apply _
  refine ⟨U,?_,?_,?_⟩
  · apply e.injective
    change e (Uᴴ*U) = e 1
    rw [he_mul,he_star,he_one,hU,LinearIsometryEquiv.adjoint_eq_symm]
    ext x
    simp
  · apply e.injective
    change e (U*Uᴴ) = e 1
    rw [he_mul,he_star,he_one,hU,LinearIsometryEquiv.adjoint_eq_symm]
    ext x
    simp
  · apply e.injective
    have hr : (u : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) * (e R₂).adjoint =
        (e R₁).adjoint := by apply ContinuousLinearMap.ext; intro x; exact hu x
    have hs := congrArg star hr
    simp only [star_mul, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_adjoint,
      LinearIsometryEquiv.adjoint_eq_symm] at hs
    change e R₁ = e (R₂*U)
    rw [he_mul,hU]
    exact hs.symm

theorem exists_unitary_row_realization (D X Y L : Matrix n n ℂ)
    (hb : X*Xᴴ-Y*Yᴴ = L*Lᴴ-D*(L*Lᴴ)*Dᴴ) :
    ∃ a b c d : Matrix n n ℂ,
      let U := Matrix.fromBlocks a b c d
      Uᴴ*U = 1 ∧ U*Uᴴ = 1 ∧ L = D*L*a+X*c ∧ Y = D*L*b+X*d := by
  let R₁ : Matrix (n ⊕ n) (n ⊕ n) ℂ := Matrix.fromBlocks L Y 0 0
  let R₂ : Matrix (n ⊕ n) (n ⊕ n) ℂ := Matrix.fromBlocks (D*L) X 0 0
  have hr : R₁*R₁ᴴ = R₂*R₂ᴴ := by
    simp only [R₁,R₂,Matrix.fromBlocks_conjTranspose,Matrix.conjTranspose_zero,
      Matrix.fromBlocks_multiply,Matrix.mul_zero,Matrix.zero_mul,add_zero]
    congr 1
    rw [Matrix.conjTranspose_mul]
    have he : D*L*(Lᴴ*Dᴴ) = D*(L*Lᴴ)*Dᴴ := by noncomm_ring
    rw [he]
    linear_combination (norm := abel) -hb
  obtain ⟨U,hu,hu',hrU⟩ := exists_unitary_matrix_of_gram R₁ R₂ hr
  refine ⟨U.toBlocks₁₁,U.toBlocks₁₂,U.toBlocks₂₁,U.toBlocks₂₂,?_⟩
  dsimp only
  rw [Matrix.fromBlocks_toBlocks]
  refine ⟨hu,hu',?_,?_⟩
  · have hh := congrArg Matrix.toBlocks₁₁ hrU
    rw [← Matrix.fromBlocks_toBlocks U] at hh
    simpa only [R₁,R₂,Matrix.fromBlocks_multiply,Matrix.toBlocks_fromBlocks₁₁] using hh
  · have hh := congrArg Matrix.toBlocks₁₂ hrU
    rw [← Matrix.fromBlocks_toBlocks U] at hh
    simpa only [R₁,R₂,Matrix.fromBlocks_multiply,Matrix.toBlocks_fromBlocks₁₂] using hh

lemma block_one₁₁
    {n : Type u_175} [Fintype n] [DecidableEq n] :
    (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ).toBlocks₁₁ = (1 : Matrix n n ℂ) := by
  ext i j
  simp [Matrix.toBlocks₁₁,Matrix.one_apply]

lemma block_one₂₂
    {n : Type u_175} [Fintype n] [DecidableEq n] :
    (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ).toBlocks₂₂ = (1 : Matrix n n ℂ) := by
  ext i j
  simp [Matrix.toBlocks₂₂,Matrix.one_apply]

lemma norm_le_one_of_star_mul_le {A : Matrix n n ℂ} (h : Aᴴ*A ≤ 1) : ‖A‖ ≤ 1 := by
  have hn := (CStarAlgebra.norm_le_one_iff_of_nonneg _
    (Matrix.posSemidef_conjTranspose_mul_self A).nonneg).mpr h
  rw [Matrix.l2_opNorm_conjTranspose_mul_self] at hn
  nlinarith [norm_nonneg A]

lemma block_unitary_contractions {a b c d : Matrix n n ℂ}
    (hU : (Matrix.fromBlocks a b c d)ᴴ * Matrix.fromBlocks a b c d = 1) :
    ‖a‖ ≤ 1 ∧ ‖b‖ ≤ 1 ∧ ‖c‖ ≤ 1 ∧ ‖d‖ ≤ 1 := by
  have h₁ := congrArg Matrix.toBlocks₁₁ hU
  have h₂ := congrArg Matrix.toBlocks₂₂ hU
  simp only [Matrix.fromBlocks_conjTranspose,Matrix.fromBlocks_multiply,
    Matrix.toBlocks_fromBlocks₁₁,block_one₁₁] at h₁
  simp only [Matrix.fromBlocks_conjTranspose,Matrix.fromBlocks_multiply,
    Matrix.toBlocks_fromBlocks₂₂,block_one₂₂] at h₂
  have hpos (A : Matrix n n ℂ) : 0 ≤ Aᴴ*A :=
    (Matrix.posSemidef_conjTranspose_mul_self A).nonneg
  refine ⟨norm_le_one_of_star_mul_le ?_,norm_le_one_of_star_mul_le ?_,
    norm_le_one_of_star_mul_le ?_,norm_le_one_of_star_mul_le ?_⟩
  · rw [← h₁]; exact le_add_of_nonneg_right (hpos c)
  · rw [← h₂]; exact le_add_of_nonneg_right (hpos d)
  · rw [← h₁]; exact le_add_of_nonneg_left (hpos a)
  · rw [← h₂]; exact le_add_of_nonneg_left (hpos b)

theorem transfer_contraction {a b c d : Matrix n n ℂ}
    (hU : (Matrix.fromBlocks a b c d)ᴴ * Matrix.fromBlocks a b c d = 1)
    {z : ℂ} (hz : ‖z‖ < 1) : ‖transfer a b c d z‖ ≤ 1 := by
  have ha := (block_unitary_contractions hU).1
  have hza : ‖z • a‖ < 1 := by
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_left ha (norm_nonneg z)).trans_lt (by simpa using hz)
  have he := isUnit_one_sub_of_norm_lt_one hza
  have hi := Matrix.mul_nonsing_inv (1-z • a) ((Matrix.isUnit_iff_isUnit_det _).mp he)
  let V := (1-z • a)⁻¹*b
  let R := transfer a b c d z
  have hV : a*(z • V)+b = V := by
    have hiV : (1-z • a)*V = b := by
      dsimp only [V]
      rw [← Matrix.mul_assoc,hi,Matrix.one_mul]
    rw [Matrix.sub_mul,Matrix.one_mul,Matrix.smul_mul] at hiV
    rw [Matrix.mul_smul]
    linear_combination (norm := module) -hiV
  have hR : c*(z • V)+d = R := by
    dsimp only [R,transfer,V]
    rw [Matrix.mul_smul,← Matrix.mul_assoc]
    exact add_comm _ _
  let W : Matrix (n ⊕ n) (n ⊕ n) ℂ := Matrix.fromBlocks (z • V) 0 1 0
  let UW : Matrix (n ⊕ n) (n ⊕ n) ℂ := Matrix.fromBlocks V 0 R 0
  have hw : Matrix.fromBlocks a b c d * W = UW := by
    simp only [W,UW,Matrix.fromBlocks_multiply,Matrix.mul_one,Matrix.mul_zero,zero_add,hV,hR]
  have hgram : UWᴴ*UW = Wᴴ*W := by
    rw [← hw,Matrix.conjTranspose_mul]
    calc
      _ = Wᴴ*((Matrix.fromBlocks a b c d)ᴴ*Matrix.fromBlocks a b c d)*W := by noncomm_ring
      _ = _ := by rw [hU,Matrix.mul_one]
  have hg := congrArg Matrix.toBlocks₁₁ hgram
  simp only [UW,W,Matrix.fromBlocks_conjTranspose,Matrix.fromBlocks_multiply,
    Matrix.toBlocks_fromBlocks₁₁,Matrix.conjTranspose_one,Matrix.one_mul,
    Matrix.conjTranspose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul] at hg
  have hsc : z*star z = (‖z‖^2 : ℝ) := by
    change z * (starRingEnd ℂ) z = _
    rw [mul_comm,← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
  rw [hsc] at hg
  have hg' : 1-Rᴴ*R = (1-‖z‖^2 : ℝ) • (Vᴴ*V) := by
    rw [sub_smul,one_smul]
    have hcast : ((‖z‖^2 : ℝ) : ℂ) • (Vᴴ*V) = (‖z‖^2 : ℝ) • (Vᴴ*V) := by
      ext i j; simp [Complex.real_smul]
    rw [hcast] at hg
    linear_combination (norm := module) -hg
  have hp : 0 ≤ (1-‖z‖^2 : ℝ) • (Vᴴ*V) := by
    apply smul_nonneg
    · nlinarith [norm_nonneg z]
    · exact (Matrix.posSemidef_conjTranspose_mul_self V).nonneg
  rw [← hg'] at hp
  exact norm_le_one_of_star_mul_le (sub_nonneg.mp hp)

end

open scoped BigOperators Matrix.Norms.L2Operator
open Set Filter Metric Topology
section
variable {n : Type u_176} [Fintype n] [DecidableEq n]

lemma meromorphic_matrix_det {M : ℂ → Matrix n n ℂ} {z : ℂ}
    (hM : ∀ i j, MeromorphicAt (fun w => M w i j) z) :
    MeromorphicAt (fun w => Matrix.det (M w)) z := by
  simp only [Matrix.det_apply']
  apply MeromorphicAt.fun_sum
  intro σ _
  exact (MeromorphicAt.const _ z).mul (MeromorphicAt.fun_prod (fun i _ => hM (σ i) i))

lemma meromorphic_matrix_adjugate {M : ℂ → Matrix n n ℂ} {z : ℂ}
    (hM : ∀ i j, MeromorphicAt (fun w => M w i j) z) (i j : n) :
    MeromorphicAt (fun w => (M w).adjugate i j) z := by
  simp only [Matrix.adjugate_apply]
  apply meromorphic_matrix_det
  intro k l
  by_cases hk : k = j
  · subst k
    simpa only [Matrix.updateRow_self] using MeromorphicAt.const ((Pi.single i (1:ℂ) : n → ℂ) l) z
  · simpa only [Matrix.updateRow_ne hk] using hM k l

lemma meromorphic_matrix_inverse {M : ℂ → Matrix n n ℂ} {z : ℂ}
    (hM : ∀ i j, MeromorphicAt (fun w => M w i j) z) (i j : n) :
    MeromorphicAt (fun w => (M w)⁻¹ i j) z := by
  simp only [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.smul_apply,smul_eq_mul]
  exact (meromorphic_matrix_det hM).inv.mul (meromorphic_matrix_adjugate hM i j)

end

open Set Filter Metric Topology

lemma meromorphic_order_nonneg_of_disk_bound {f : ℂ → ℂ} {C : ℝ}
    (_hf : MeromorphicOn f Set.univ) (ha : AnalyticOnNhd ℂ f (ball 0 1))
    (hb : ∀ z ∈ ball 0 1, ‖f z‖ ≤ C) {x : ℂ} (hx : x ∈ closedBall 0 1) :
    0 ≤ meromorphicOrderAt f x := by
  by_cases hxi : x ∈ ball 0 1
  · exact (ha x hxi).meromorphicOrderAt_nonneg
  have hxc : x ∈ closure (ball (0:ℂ) 1) := by
    simpa only [closure_ball (0:ℂ) (by norm_num : (1:ℝ) ≠ 0)] using hx
  have : NeBot (𝓝[ball (0:ℂ) 1] x) := mem_closure_iff_nhdsWithin_neBot.mp hxc
  have hsub : ball (0:ℂ) 1 ⊆ {x}ᶜ := by
    intro z hz he
    exact hxi ((mem_singleton_iff.mp he) ▸ hz)
  by_contra hneg
  have ht := (tendsto_norm_cobounded_atTop.comp
    (tendsto_cobounded_of_meromorphicOrderAt_neg (lt_of_not_ge hneg))).mono_left
      (nhdsWithin_mono x hsub)
  obtain ⟨z,hz,hgt⟩ := ((show ∀ᶠ z in 𝓝[ball (0:ℂ) 1] x, z ∈ ball 0 1 from self_mem_nhdsWithin).and
    (ht.eventually (eventually_gt_atTop C))).exists
  exact not_lt_of_ge (hb z hz) hgt

lemma bounded_meromorphic_disk_extension {f : ℂ → ℂ} {C : ℝ}
    (hf : MeromorphicOn f Set.univ) (ha : AnalyticOnNhd ℂ f (ball 0 1))
    (hb : ∀ z ∈ ball 0 1, ‖f z‖ ≤ C) :
    ∃ g, AnalyticOnNhd ℂ g (closedBall 0 1) ∧ EqOn g f (ball 0 1) := by
  let g := toMeromorphicNFOn f Set.univ
  refine ⟨g,?_,?_⟩
  · intro x hx
    have hn := (hf x (mem_univ x)).meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt.mp
      (meromorphic_order_nonneg_of_disk_bound hf ha hb hx)
    exact hn.congr (toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hf (mem_univ x)).symm
  · intro x hx
    rw [show g x = toMeromorphicNFAt f x x from
      toMeromorphicNFOn_eq_toMeromorphicNFAt hf (mem_univ x)]
    rw [toMeromorphicNFAt_eq_self.mpr (ha x hx).meromorphicNFAt]


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_MetricFeasibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_177 u_178 u_179 u_180 u_181 u_182 u_183

section
section
section
open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset
open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped BigOperators Matrix.Norms.L2Operator
open Set Filter Metric Topology
open Set Filter Metric Topology

section
open scoped BigOperators Matrix.Norms.L2Operator
open Set Filter Metric Topology
variable {n : Type u_177} [Fintype n] [DecidableEq n]

lemma transfer_meromorphic (a b c d : Matrix n n ℂ) (i j : n) :
    MeromorphicOn (fun z => transfer a b c d z i j) Set.univ := by
  intro z _
  have hM (i j : n) : MeromorphicAt (fun w : ℂ => (1-w • a : Matrix n n ℂ) i j) z := by
    simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
    fun_prop
  simp only [transfer,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.mul_apply]
  apply (MeromorphicAt.const _ z).add
  apply (MeromorphicAt.id z).mul
  apply MeromorphicAt.fun_sum
  intro k _
  apply MeromorphicAt.mul _ (MeromorphicAt.const _ z)
  apply MeromorphicAt.fun_sum
  intro l _
  exact (MeromorphicAt.const _ z).mul (meromorphic_matrix_inverse hM l k)

lemma transfer_analytic {a b c d : Matrix n n ℂ} (ha : ‖a‖ ≤ 1) :
    AnalyticOnNhd ℂ (transfer a b c d) (ball 0 1) := by
  intro z hz
  have hza : ‖z • a‖ < 1 := by
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_left ha (norm_nonneg z)).trans_lt
      (by simpa only [mul_one] using mem_ball_zero_iff.mp hz)
  have hi := scalar_matrix_inverse_analytic (isUnit_one_sub_of_norm_lt_one hza)
  unfold transfer
  fun_prop

theorem exists_transfer_extension {a b c d : Matrix n n ℂ}
    (hU : (Matrix.fromBlocks a b c d)ᴴ * Matrix.fromBlocks a b c d = 1) :
    ∃ R : ℂ → Matrix n n ℂ,
      AnalyticOnNhd ℂ R (closedBall 0 1) ∧ EqOn R (transfer a b c d) (ball 0 1) ∧
      ∀ z ∈ closedBall 0 1, ‖R z‖ ≤ 1 := by
  classical
  have ha := transfer_analytic (b := b) (c := c) (d := d) (block_unitary_contractions hU).1
  have hentries : ∀ i j : n, ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (closedBall 0 1) ∧
      EqOn g (fun z => transfer a b c d z i j) (ball 0 1) := by
    intro i j
    let L : Matrix n n ℂ →ₗ[ℂ] ℂ :=
      { toFun := fun M => M i j, map_add' := by intros; rfl, map_smul' := by intros; rfl }
    apply bounded_meromorphic_disk_extension (C := ‖L.toContinuousLinearMap‖)
      (transfer_meromorphic a b c d i j) (fun z hz => matrix_entry_analytic (ha z hz) i j)
    intro z hz
    exact (L.toContinuousLinearMap.le_opNorm (transfer a b c d z)).trans
      (mul_le_of_le_one_right (norm_nonneg _) (transfer_contraction hU (mem_ball_zero_iff.mp hz)))
  choose g hga hge using hentries
  let R : ℂ → Matrix n n ℂ := fun z i j => g i j z
  have hRa : AnalyticOnNhd ℂ R (closedBall 0 1) := by
    intro z hz
    have he : R = fun w => ∑ i : n, ∑ j : n, g i j w • Matrix.single i j (1:ℂ) := by
      funext w
      ext i j
      simp [R,Matrix.sum_apply,Matrix.single_apply, ite_and]
    rw [he]
    apply Finset.analyticAt_fun_sum
    intro i _
    apply Finset.analyticAt_fun_sum
    intro j _
    exact (hga i j z hz).smul analyticAt_const
  have hRe : EqOn R (transfer a b c d) (ball 0 1) := by
    intro z hz
    ext i j
    exact hge i j hz
  refine ⟨R,hRa,hRe,?_⟩
  intro z hz
  have hcl : closure (ball (0:ℂ) 1) = closedBall 0 1 := closure_ball 0 (by norm_num)
  apply le_on_closure (fun w hw => ?_) (hRa.continuousOn.norm.mono (by rw [hcl]))
    continuousOn_const (by rwa [hcl])
  rw [hRe hw]
  exact transfer_contraction hU (mem_ball_zero_iff.mp hw)

end

section
open Filter Topology Set Metric
open scoped Matrix.Norms.L2Operator Kronecker
variable {n : Type u_178} [Fintype n] [DecidableEq n]

theorem exists_analytic_extremal_from_balance {D X Y L : Matrix n n ℂ}
    (hD : spectralRadius ℂ D < 1)
    (hb : X*Xᴴ-Y*Yᴴ = L*Lᴴ-D*(L*Lᴴ)*Dᴴ) :
    ∃ F : ℂ → Matrix n n ℂ,
      AnalyticOnNhd ℂ F (closedBall 0 1) ∧
      (∀ z ∈ closedBall 0 1, ‖F z‖ ≤ 1) ∧
      Matrix.toEuclideanCLM (n := n × n) (𝕜 := ℂ) (completeAnalyticEval D F)
        (vectorize X) = vectorize Y := by
  obtain ⟨a,b,c,d,hU,hU',hL,hY⟩ := exists_unitary_row_realization D X Y L hb
  have hW : (Matrix.fromBlocks aᵀ cᵀ bᵀ dᵀ)ᴴ * Matrix.fromBlocks aᵀ cᵀ bᵀ dᵀ = 1 := by
    have ht := congrArg Matrix.transpose hU'
    simpa only [Matrix.transpose_mul, Matrix.transpose_one, Matrix.fromBlocks_transpose,
      Matrix.transpose_conjTranspose, Matrix.conjTranspose_transpose,
      Matrix.fromBlocks_conjTranspose] using ht
  obtain ⟨F,hFa,hFe,hFn⟩ := exists_transfer_extension hW
  refine ⟨F,hFa,hFn,?_⟩
  have he : EqOn F (transposedTransfer a b c d) (ball 0 1) := by
    intro z hz
    rw [hFe hz]
    simp only [transfer, transposedTransfer, smul_mul_assoc]
  rw [completeAnalyticEval_eqOn D isOpen_ball
    (fun z hz => mem_ball_zero_iff.mpr (stable_spectrum_norm_lt_one hD hz)) he]
  exact actual_transfer_extremal_evaluation hD (block_unitary_contractions hU).1 hL hY

end

section
open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder Pointwise
section

section Stability
variable {A : Type u_179} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

theorem summable_norm_powers_metricSupport {a : A} (ha : spectralRadius ℂ a < 1) :
    Summable (fun n : ℕ => ‖a ^ n‖) := by
  obtain ⟨r, har, hr1⟩ := exists_between ha
  have hrf : r ≠ ∞ := ne_of_lt (hr1.trans (by simp))
  have hrpos : 0 < r := lt_of_le_of_lt bot_le har
  have hr0 : 0 ≤ r.toReal := ENNReal.toReal_nonneg
  have hrr : ENNReal.ofReal r.toReal = r := ENNReal.ofReal_toReal hrf
  have hrt : r.toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hrf (by simp : (1 : ℝ≥0∞) ≠ ∞)).mpr hr1
  have hev := (spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius a).eventually
    (gt_mem_nhds har)
  have hbound : ∀ᶠ n : ℕ in atTop, ‖a ^ n‖ ≤ r.toReal ^ n := by
    filter_upwards [hev, eventually_gt_atTop 0] with n hn hn0
    have hroot : ‖a ^ n‖ ^ (1 / (n : ℝ)) < r.toReal := by
      rw [← hrr] at hn
      exact (ENNReal.ofReal_lt_ofReal_iff (ENNReal.toReal_pos hrpos.ne' hrf)).mp hn
    have hp := pow_le_pow_left₀ (Real.rpow_nonneg (norm_nonneg _) _) hroot.le n
    simpa only [one_div, Real.rpow_inv_natCast_pow (norm_nonneg _) (Nat.ne_of_gt hn0)] using hp
  apply (summable_geometric_of_lt_one hr0 hrt).of_norm_bounded_eventually
  simpa only [Nat.cofinite_eq_atTop, norm_norm] using hbound

end Stability

section Metric
variable {n : Type u_180} [Fintype n] [DecidableEq n]

lemma summable_steinTerm {T : Matrix n n ℂ} (hT : spectralRadius ℂ T < 1) :
    Summable (steinTerm T) := by
  have hs : Summable (fun j : ℕ => ‖T ^ j‖) := summable_norm_powers_metricSupport (a := T) hT
  have hp : Summable (fun ij : ℕ × ℕ => ‖T ^ ij.1‖ * ‖T ^ ij.2‖) :=
    @Summable.mul_of_nonneg ℕ ℕ (fun j => ‖T ^ j‖) (fun j => ‖T ^ j‖) hs hs
      (fun j => norm_nonneg (T ^ j)) (fun j => norm_nonneg (T ^ j))
  have hsq : Summable (fun j => ‖T ^ j‖ * ‖T ^ j‖) :=
    hp.comp_injective (i := fun j : ℕ => (j, j)) (fun a b h => congrArg Prod.fst h)
  apply Summable.of_norm
  apply hsq.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro j
  change ‖(T ^ j)ᴴ * T ^ j‖ ≤ ‖T ^ j‖ * ‖T ^ j‖
  exact (norm_mul_le (T ^ j)ᴴ (T ^ j)).trans_eq
    (congrArg (· * ‖T ^ j‖) (Matrix.l2_opNorm_conjTranspose (T ^ j)))

lemma steinMetric_nonneg (T : Matrix n n ℂ) : 0 ≤ steinMetric T := by
  apply tsum_nonneg
  intro j
  exact (Matrix.posSemidef_conjTranspose_mul_self (T ^ j)).nonneg

lemma steinMetric_ge_one {T : Matrix n n ℂ} (hT : spectralRadius ℂ T < 1) :
    1 ≤ steinMetric T := by
  have h := (summable_steinTerm hT).tsum_eq_zero_add
  change steinMetric T = _ at h
  rw [h]
  simpa [steinTerm] using add_le_add_left
    (tsum_nonneg (fun j : ℕ =>
      (Matrix.posSemidef_conjTranspose_mul_self (T ^ (j + 1))).nonneg)) (1 : Matrix n n ℂ)

lemma steinMetric_identity {T : Matrix n n ℂ} (hT : spectralRadius ℂ T < 1) :
    steinMetric T - Tᴴ * steinMetric T * T = 1 := by
  have hs := summable_steinTerm hT
  have hstep (j : ℕ) : Tᴴ * steinTerm T j * T = steinTerm T (j + 1) := by
    simp only [steinTerm, pow_succ, Matrix.conjTranspose_mul]
    noncomm_ring
  have hsum : Tᴴ * steinMetric T * T = ∑' j : ℕ, steinTerm T (j + 1) := by
    change (Tᴴ * ∑' j : ℕ, steinTerm T j) * T = _
    rw [← hs.tsum_mul_left Tᴴ, ← (hs.mul_left Tᴴ).tsum_mul_right T]
    exact tsum_congr hstep
  rw [hsum]
  have h := hs.tsum_eq_zero_add
  change steinMetric T = _ at h
  rw [h]
  simp [steinTerm]

end Metric

section Minimum
variable {n : Type u_181} [Fintype n] [DecidableEq n] [Nonempty n]

lemma scalarMatrix_le_iff (a b : ℝ) :
    algebraMap ℝ (Matrix n n ℂ) a ≤ algebraMap ℝ (Matrix n n ℂ) b ↔ a ≤ b := by
  constructor
  · intro h
    have hd := (h : ((algebraMap ℝ (Matrix n n ℂ)) b -
      (algebraMap ℝ (Matrix n n ℂ)) a).PosSemidef).diag_nonneg (i := Classical.arbitrary n)
    simpa [Matrix.sub_apply, Algebra.algebraMap_eq_smul_one, Matrix.smul_apply,
      Matrix.one_apply] using hd
  · intro h
    rw [Matrix.le_iff, ← map_sub]
    rw [Algebra.algebraMap_eq_smul_one]
    exact Matrix.nonneg_iff_posSemidef.mp
      (smul_nonneg (sub_nonneg.mpr h) (zero_le_one : 0 ≤ (1 : Matrix n n ℂ)))

lemma MetricFeasible.one_le {T H : Matrix n n ℂ} {τ : ℝ}
    (h : MetricFeasible T τ H) : 1 ≤ τ := by
  apply (scalarMatrix_le_iff (n := n) 1 τ).mp
  simpa using h.1.trans h.2.1

lemma MetricFeasible.norm_le {T H : Matrix n n ℂ} {τ : ℝ}
    (h : MetricFeasible T τ H) : ‖H‖ ≤ τ :=
  (CStarAlgebra.norm_le_iff_le_algebraMap H (zero_le_one.trans h.one_le)
    (zero_le_one.trans h.1)).mpr h.2.1

lemma steinMetric_feasible {n : Type u_181} [Fintype n] [DecidableEq n] [Nonempty n]
    {T : Matrix n n ℂ} (hT : spectralRadius ℂ T < 1) :
    MetricFeasible T ‖steinMetric T‖ (steinMetric T) := by
  refine ⟨steinMetric_ge_one hT,
    IsSelfAdjoint.le_algebraMap_norm_self (a := steinMetric T)
      (.of_nonneg (steinMetric_nonneg T)), ?_⟩
  rw [← sub_nonneg, steinMetric_identity hT]
  exact zero_le_one

lemma isClosed_metricFeasible {n : Type u_181} [Fintype n] [DecidableEq n] [Nonempty n]
    (T : Matrix n n ℂ) :
    IsClosed {x : ℝ × Matrix n n ℂ | MetricFeasible T x.1 x.2} := by
  unfold MetricFeasible
  exact (isClosed_le continuous_const continuous_snd).inter
    ((isClosed_le continuous_snd ((continuous_algebraMap ℝ _).comp continuous_fst)).inter
      (isClosed_le ((continuous_const.mul continuous_snd).mul continuous_const) continuous_snd))

theorem exists_optimal_metric {T : Matrix n n ℂ} (hT : spectralRadius ℂ T < 1) :
    ∃ (τ : ℝ) (H : Matrix n n ℂ), MetricFeasible T τ H ∧ H.PosDef ∧
      ∀ (σ : ℝ) (J : Matrix n n ℂ), MetricFeasible T σ J → τ ≤ σ := by
  let τ₀ := ‖steinMetric T‖
  let K : Set (ℝ × Matrix n n ℂ) :=
    {x | MetricFeasible T x.1 x.2 ∧ x.1 ≤ τ₀}
  have h₀ := steinMetric_feasible hT
  have hKclosed : IsClosed K := (isClosed_metricFeasible T).inter
    (isClosed_le continuous_fst continuous_const)
  have hKcompact : IsCompact K := by
    apply ((isCompact_Icc : IsCompact (Set.Icc (1 : ℝ) τ₀)).prod
      (isCompact_closedBall (0 : Matrix n n ℂ) τ₀)).of_isClosed_subset hKclosed
    intro x hx
    exact ⟨⟨hx.1.one_le, hx.2⟩, by simpa using hx.1.norm_le.trans hx.2⟩
  have hKne : K.Nonempty := ⟨(τ₀, steinMetric T), h₀, le_rfl⟩
  obtain ⟨x, hx, hmin⟩ := hKcompact.exists_isMinOn hKne continuous_fst.continuousOn
  refine ⟨x.1, x.2, hx.1, ?_, ?_⟩
  · have hp := (hx.1.1 : (x.2 - 1).PosSemidef)
    have hpositive := Matrix.PosDef.posSemidef_add hp Matrix.PosDef.one
    simpa only [sub_add_cancel] using hpositive
  · intro σ J hJ
    by_cases hσ : σ ≤ τ₀
    · exact hmin (show (σ, J) ∈ K from ⟨hJ, hσ⟩)
    · exact hx.2.trans (le_of_not_ge hσ)

end Minimum

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {n : Type u_182} [Fintype n] [DecidableEq n]

lemma hermTrace_realPart (B : Matrix n n ℂ) (A : HermitianMatrix n) :
    hermTrace (realPart B) A =
      (Matrix.trace (Bᴴ * (A : Matrix n n ℂ))).re := by
  have hA : (A : Matrix n n ℂ)ᴴ = A := A.property
  have hconj : (Matrix.trace (B * (A : Matrix n n ℂ))).re =
      (Matrix.trace (Bᴴ * (A : Matrix n n ℂ))).re := by
    have hc := congrArg Complex.re (Matrix.trace_conjTranspose (B * (A : Matrix n n ℂ)))
    rw [Matrix.conjTranspose_mul, hA, Matrix.trace_mul_comm] at hc
    simpa using hc.symm
  simp only [hermTrace, realPart_apply_coe, Matrix.star_eq_conjTranspose,
    Matrix.add_mul, Matrix.smul_mul, Matrix.trace_smul, Matrix.trace_add,
    Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.add_re]
  rw [hconj]
  ring

theorem exists_hermitian_trace_representative
    (φ : HermitianMatrix n →ₗ[ℝ] ℝ) :
    ∃ B : HermitianMatrix n, ∀ A, φ A = hermTrace B A := by
  let f : HSMatrix n →ₗ[ℝ] ℝ := φ.comp (realPart.comp fromHSL)
  let fc : HSMatrix n →L[ℝ] ℝ := f.toContinuousLinearMap
  obtain ⟨v, hv⟩ := (InnerProductSpace.toDual ℝ (HSMatrix n)).surjective fc
  refine ⟨realPart (fromHS v), ?_⟩
  intro A
  have h := congrArg (fun g : HSMatrix n →L[ℝ] ℝ => g (toHS (A : Matrix n n ℂ))) hv
  change inner ℝ v (toHS (A : Matrix n n ℂ)) = _ at h
  have hr : realPart (A : Matrix n n ℂ) = A := by
    exact Subtype.ext A.property.coe_realPart
  have hval : fc (toHS (A : Matrix n n ℂ)) = φ A := by
    change φ (realPart (fromHS (toHS (A : Matrix n n ℂ)))) = φ A
    rw [fromHS_toHS, hr]
  rw [hval] at h
  rw [hermTrace_realPart, ← hs_inner, toHS_fromHS]
  have hir (u w : HSMatrix n) : inner ℝ u w = (inner ℂ u w).re := by
    simp only [PiLp.inner_apply, Complex.re_sum]
    rfl
  simpa only [hir] using h.symm

lemma hermTrace_symm (A B : HermitianMatrix n) : hermTrace A B = hermTrace B A := by
  exact congrArg Complex.re (Matrix.trace_mul_comm _ _)

lemma hermTrace_nonneg_iff (B : HermitianMatrix n) :
    (0 ≤ (B : Matrix n n ℂ)) ↔
      ∀ A : HermitianMatrix n, 0 ≤ (A : Matrix n n ℂ) → 0 ≤ hermTrace B A := by
  constructor
  · intro hB A hA
    obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA
    have h := (Matrix.nonneg_iff_posSemidef.mp hB).mul_mul_conjTranspose_same C
    have hr := (Complex.nonneg_iff.mp h.trace_nonneg).1
    rw [Matrix.trace_mul_cycle] at hr
    rw [Matrix.trace_mul_comm] at hr
    simpa only [hermTrace, hC, Matrix.star_eq_conjTranspose] using hr
  · intro h
    apply Matrix.PosSemidef.nonneg
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg B.property
    intro x
    let A : HermitianMatrix n :=
      ⟨Matrix.vecMulVec x (star x), (Matrix.posSemidef_vecMulVec_self_star x).isHermitian⟩
    have hx := h A (Matrix.posSemidef_vecMulVec_self_star x).nonneg
    change 0 ≤ (Matrix.trace ((B : Matrix n n ℂ) * Matrix.vecMulVec x (star x))).re at hx
    rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm] at hx
    apply Complex.nonneg_iff.mpr
    refine ⟨hx, ?_⟩
    exact (Matrix.IsHermitian.im_star_dotProduct_mulVec_self B.property x).symm

end
end
end
end
end

end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_DualSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_184 u_185 u_186 u_187

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset
open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped BigOperators Matrix.Norms.L2Operator
open Set Filter Metric Topology
open Set Filter Metric Topology
open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder Pointwise
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {n : Type u_184} [Fintype n] [DecidableEq n] [Nonempty n]

local instance instZeroLEOneClassSubtypeMatrixComplexMemAddSubgroupHermitianMatrix : ZeroLEOneClass (HermitianMatrix n) where
  zero_le_one := (zero_le_one : (0 : Matrix n n ℂ) ≤ 1)

local instance instPosSMulMonoRealSubtypeMatrixComplexMemAddSubgroupHermitianMatrix : PosSMulMono ℝ (HermitianMatrix n) where
  smul_le_smul_of_nonneg_left a ha b c hbc :=
    show a • (b : Matrix n n ℂ) ≤ a • (c : Matrix n n ℂ) from
      smul_le_smul_of_nonneg_left hbc ha

lemma hermitian_smul_one_le_iff (a b : ℝ) :
    a • (1 : HermitianMatrix n) ≤ b • (1 : HermitianMatrix n) ↔ a ≤ b := by
  change a • (1 : Matrix n n ℂ) ≤ b • (1 : Matrix n n ℂ) ↔ a ≤ b
  simpa only [Algebra.algebraMap_eq_smul_one] using scalarMatrix_le_iff (n := n) a b

lemma hermitian_lower_norm
    {n : Type u_184} [Fintype n] [DecidableEq n] [Nonempty n] (H : HermitianMatrix n) :
    (-‖H‖) • (1 : HermitianMatrix n) ≤ H := by
  have h := IsSelfAdjoint.le_algebraMap_norm_self
    (a := -(H : Matrix n n ℂ)) H.property.neg
  rw [norm_neg] at h
  have hn := neg_le_neg h
  change (-‖(H : Matrix n n ℂ)‖) • (1 : Matrix n n ℂ) ≤ (H : Matrix n n ℂ)
  simpa only [map_neg, neg_neg, Algebra.algebraMap_eq_smul_one, neg_smul] using hn

lemma StrictPositive.nonneg
    {n : Type u_184} [Fintype n] [DecidableEq n] [Nonempty n] {H : HermitianMatrix n}
    (hH : StrictPositive H) : 0 ≤ H := by
  obtain ⟨r, hr, h⟩ := hH
  exact (smul_nonneg hr.le (zero_le_one : (0 : HermitianMatrix n) ≤ 1)).trans h

lemma strictPositive_one
    {n : Type u_184} [Fintype n] [DecidableEq n] [Nonempty n] :
    StrictPositive (1 : HermitianMatrix n) := by
  exact ⟨1, zero_lt_one, by simp⟩

lemma StrictPositive.add_nonneg
    {n : Type u_184} [Fintype n] [DecidableEq n] [Nonempty n] {H K : HermitianMatrix n}
    (hH : StrictPositive H) (hK : 0 ≤ K) : StrictPositive (H + K) := by
  obtain ⟨r, hr, h⟩ := hH
  exact ⟨r, hr, h.trans (le_add_of_nonneg_right hK)⟩

lemma StrictPositive.smul
    {n : Type u_184} [Fintype n] [DecidableEq n] [Nonempty n] {H : HermitianMatrix n}
    (hH : StrictPositive H)
    {a : ℝ} (ha : 0 < a) : StrictPositive (a • H) := by
  obtain ⟨r, hr, h⟩ := hH
  refine ⟨a*r, mul_pos ha hr, ?_⟩
  simpa only [mul_smul] using smul_le_smul_of_nonneg_left h ha.le

lemma strictPositive_isOpen : IsOpen {H : HermitianMatrix n | StrictPositive H} := by
  rw [Metric.isOpen_iff]
  intro H hH
  obtain ⟨r, hr, h⟩ := hH
  refine ⟨r/2, by positivity, ?_⟩
  intro J hJ
  have hδ : ‖J-H‖ < r/2 := by simpa only [Metric.mem_ball, dist_eq_norm] using hJ
  refine ⟨r/2, by positivity, ?_⟩
  have hb := add_le_add h (hermitian_lower_norm (J-H))
  have he : H + (J-H) = J := by abel
  rw [he, ← add_smul] at hb
  apply le_trans _ hb
  apply (hermitian_smul_one_le_iff _ _).mpr
  linarith

lemma strictPositive_convex
    {n : Type u_184} [Fintype n] [DecidableEq n] [Nonempty n] :
    Convex ℝ {H : HermitianMatrix n | StrictPositive H} := by
  intro H hH K hK a b ha hb hab
  obtain ⟨r, hr, hH⟩ := hH
  obtain ⟨s, hs, hK⟩ := hK
  refine ⟨a*r+b*s, ?_, ?_⟩
  · have h₁ : 0 ≤ a*r := mul_nonneg ha hr.le
    have h₂ : 0 ≤ b*s := mul_nonneg hb hs.le
    by_cases ha0 : a = 0
    · subst a
      have hb1 : b = 1 := by linarith
      simpa [hb1]
    · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      exact add_pos_of_pos_of_nonneg (mul_pos hap hr) h₂
  · simpa only [add_smul, mul_smul] using
      add_le_add (smul_le_smul_of_nonneg_left hH ha) (smul_le_smul_of_nonneg_left hK hb)

theorem exists_strict_metric {T : Matrix n n ℂ} (hT : spectralRadius ℂ T < 1) :
    ∃ (τ : ℝ) (H : HermitianMatrix n),
      StrictPositive (H-1) ∧ StrictPositive (τ • 1-H) ∧ StrictPositive (metricStein T H) := by
  let J : HermitianMatrix n := ⟨steinMetric T, IsSelfAdjoint.of_nonneg (steinMetric_nonneg T)⟩
  let H : HermitianMatrix n := (2 : ℝ) • J
  have hJ : (1 : HermitianMatrix n) ≤ J := steinMetric_ge_one hT
  have hJ2 : (2 : ℝ) • (1 : HermitianMatrix n) ≤ H :=
    smul_le_smul_of_nonneg_left hJ (by norm_num)
  have hH : 1 ≤ H-1 := by
    rw [le_sub_iff_add_le]
    simpa only [two_smul ℝ] using hJ2
  have hnorm : H ≤ ‖H‖ • (1 : HermitianMatrix n) := by
    change (H : Matrix n n ℂ) ≤ ‖(H : Matrix n n ℂ)‖ • (1 : Matrix n n ℂ)
    simpa [Algebra.algebraMap_eq_smul_one] using
      IsSelfAdjoint.le_algebraMap_norm_self (a := (H : Matrix n n ℂ)) H.property
  refine ⟨‖H‖+1, H, ⟨1, zero_lt_one, by simpa using hH⟩,
    ⟨1, zero_lt_one, ?_⟩, ?_⟩
  · rw [one_smul, le_sub_iff_add_le, add_smul, one_smul]
    simpa only [add_comm] using add_le_add_left hnorm 1
  · have hs : metricStein T H = (2 : ℝ) • (1 : HermitianMatrix n) := by
      rw [show H = (2:ℝ) • J from rfl, map_smul]
      congr 1
      apply Subtype.ext
      exact steinMetric_identity hT
    rw [hs]
    exact strictPositive_one.smul (by norm_num)

lemma metricOpen_isOpen (τ : ℝ) : IsOpen (metricOpen (n := n) τ) := by
  exact (isOpen_lt continuous_fst continuous_const).inter
    ((strictPositive_isOpen.preimage (continuous_fst.comp continuous_snd)).inter
      ((strictPositive_isOpen.preimage (continuous_fst.comp (continuous_snd.comp continuous_snd))).inter
        (strictPositive_isOpen.preimage (continuous_snd.comp (continuous_snd.comp continuous_snd)))))

lemma metricOpen_convex (τ : ℝ) : Convex ℝ (metricOpen (n := n) τ) := by
  exact (convex_Iio τ).prod (strictPositive_convex.prod
    (strictPositive_convex.prod strictPositive_convex))

lemma metricAffine_range_convex
    {n : Type u_184} [Fintype n] [DecidableEq n] [Nonempty n] (T : Matrix n n ℂ) :
    Convex ℝ (Set.range (metricAffine T)) := by
  have he : Set.range (metricAffine T) = (metricOffset (n := n)) +ᵥ
      ((metricLinear T).range : Set (MetricDualSpace n)) := by
    ext x
    simp only [Set.mem_range, Set.mem_vadd_set, metricAffine]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨metricLinear T y, ⟨y, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨y, rfl⟩, rfl⟩
      exact ⟨y, rfl⟩
  rw [he]
  exact (metricLinear T).range.convex.vadd _

lemma ray_slope_nonpos {a b c : ℝ} (h : ∀ t : ℝ, 0 ≤ t → a + t*b ≤ c) : b ≤ 0 := by
  by_contra hb
  have hb : 0 < b := lt_of_not_ge hb
  have ht : 0 ≤ (|c-a|+1)/b := div_nonneg (by positivity) hb.le
  have hh := h ((|c-a|+1)/b) ht
  rw [div_mul_cancel₀ _ hb.ne'] at hh
  have ha := le_abs_self (c-a)
  linarith

lemma affine_functional_constant {E : Type u_186} {F : Type u_187} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (L : E →ₗ[ℝ] F) (φ : F →ₗ[ℝ] ℝ)
    (b : F) (c : ℝ) (hc : ∀ x, c ≤ φ (b + L x)) :
    ∀ x, φ (L x) = 0 := by
  intro x
  have hn : -φ (L x) ≤ 0 := by
    apply ray_slope_nonpos (a := -φ b) (c := -c)
    intro t ht
    have hh := hc (t • x)
    simp only [map_add, map_smul, smul_eq_mul] at hh
    linarith
  have hp : φ (L x) ≤ 0 := by
    apply ray_slope_nonpos (a := -φ b) (c := -c)
    intro t ht
    have hh := hc (t • (-x))
    simp only [map_add, map_smul, map_neg, smul_eq_mul] at hh
    linarith
  linarith

lemma metricAffine_feasible
    {n : Type u_184} [Fintype n] [DecidableEq n] [Nonempty n] {T : Matrix n n ℂ} {s : ℝ}
    {J : HermitianMatrix n}
    (hu : 0 ≤ (metricAffine T (s,J)).2.1)
    (hv : 0 ≤ (metricAffine T (s,J)).2.2.1)
    (hw : 0 ≤ (metricAffine T (s,J)).2.2.2) : MetricFeasible T s J := by
  change 0 ≤ -1 + J at hu
  change 0 ≤ 0 + (s • 1 - J) at hv
  rw [zero_add] at hv
  change 0 ≤ 0 + metricStein T J at hw
  rw [zero_add] at hw
  have hu' : 1 ≤ J := by
    rw [← sub_nonneg]
    simpa only [sub_eq_add_neg, add_comm] using hu
  have hv' : J ≤ s • (1 : HermitianMatrix n) := sub_nonneg.mp hv
  refine ⟨hu', ?_, ?_⟩
  · change (J : Matrix n n ℂ) ≤ s • (1 : Matrix n n ℂ) at hv'
    simpa only [Algebra.algebraMap_eq_smul_one] using hv'
  · change 0 ≤ (J : Matrix n n ℂ) - Tᴴ * (J : Matrix n n ℂ) * T at hw
    exact sub_nonneg.mp hw

lemma metric_sets_disjoint {T : Matrix n n ℂ} {τ : ℝ}
    (hmin : ∀ s J, MetricFeasible T s J → τ ≤ s) :
    Disjoint (metricOpen (n := n) τ) (Set.range (metricAffine T)) := by
  rw [Set.disjoint_left]
  rintro a ha ⟨⟨s,J⟩, rfl⟩
  have hfeas := metricAffine_feasible ha.2.1.nonneg ha.2.2.1.nonneg ha.2.2.2.nonneg
  have hs : s < τ := by simpa [metricAffine, metricOffset, metricLinear] using ha.1
  exact (not_lt_of_ge (hmin s J hfeas)) hs

theorem metric_separator {T : Matrix n n ℂ} {τ : ℝ}
    (hmin : ∀ s J, MetricFeasible T s J → τ ≤ s) :
    ∃ φ : StrongDual ℝ (MetricDualSpace n),
      (∀ x, φ (metricLinear T x) = 0) ∧
      (∀ o ∈ metricOpen τ, φ o < φ metricOffset) := by
  obtain ⟨φ, c, ho, ha⟩ := geometric_hahn_banach_open
    (metricOpen_convex (n := n) τ) (metricOpen_isOpen (n := n) τ) (metricAffine_range_convex T)
    (metric_sets_disjoint hmin)
  have hconst : ∀ x, φ (metricLinear T x) = 0 :=
    affine_functional_constant (metricLinear T) φ.toLinearMap metricOffset c
      (fun x => ha _ ⟨x, rfl⟩)
  refine ⟨φ, hconst, ?_⟩
  have hc : c ≤ φ metricOffset := by
    simpa only [metricAffine, map_add, hconst, add_zero] using ha _ ⟨(0,0), rfl⟩
  exact fun o ho' => (ho o ho').trans_le hc

lemma metric_functional_decompose
    {n : Type u_184} [Fintype n] [DecidableEq n] [Nonempty n] (φ : StrongDual ℝ (MetricDualSpace n))
    (s : ℝ) (U V W : HermitianMatrix n) :
    φ (s,U,V,W) = s*φ (metricAxis0 1) + φ (metricAxis1 U) +
      φ (metricAxis2 V) + φ (metricAxis3 W) := by
  have he : (s,U,V,W) = s • metricAxis0 (n := n) 1 + metricAxis1 U +
      metricAxis2 V + metricAxis3 W := by
    simp [metricAxis0, metricAxis1, metricAxis2, metricAxis3]
  rw [he, map_add, map_add, map_add, map_smul, smul_eq_mul]

lemma metric_separator_nonpos {τ : ℝ} (φ : StrongDual ℝ (MetricDualSpace n))
    (ho : ∀ o ∈ metricOpen τ, φ o < φ metricOffset)
    {U V W : HermitianMatrix n} (hU : 0 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) :
    φ (0,U,V,W) ≤ 0 := by
  let b : MetricDualSpace n := (τ-1,1,1,1)
  apply ray_slope_nonpos (a := φ b) (c := φ metricOffset)
  intro t ht
  have hmem : b + t • (0,U,V,W) ∈ metricOpen τ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · change τ-1 + t*0 < τ
      linarith
    · exact strictPositive_one.add_nonneg (smul_nonneg ht hU)
    · exact strictPositive_one.add_nonneg (smul_nonneg ht hV)
    · exact strictPositive_one.add_nonneg (smul_nonneg ht hW)
  simpa only [map_add, map_smul, smul_eq_mul] using (ho _ hmem).le

lemma metric_separator_scalar_pos {T : Matrix n n ℂ} (hT : spectralRadius ℂ T < 1)
    {τ : ℝ} (hmin : ∀ s J, MetricFeasible T s J → τ ≤ s)
    (φ : StrongDual ℝ (MetricDualSpace n))
    (hc : ∀ x, φ (metricLinear T x) = 0)
    (ho : ∀ o ∈ metricOpen τ, φ o < φ metricOffset) :
    0 < φ (metricAxis0 1) := by
  obtain ⟨s,H,hU,hV,hW⟩ := exists_strict_metric hT
  let U := H-1
  let V := s • (1 : HermitianMatrix n)-H
  let W := metricStein T H
  have ha : metricAffine T (s,H) = (s,U,V,W) := by
    simp [metricAffine, metricOffset, metricLinear, U, V, W, sub_eq_add_neg, add_comm]
  have hfeas : MetricFeasible T s H := by
    apply metricAffine_feasible <;> rw [ha]
    · exact hU.nonneg
    · exact hV.nonneg
    · exact hW.nonneg
  have hs : τ ≤ s := hmin s H hfeas
  have hh := ho (τ-1,U,V,W) ⟨by linarith, hU,hV,hW⟩
  have hf : φ (s,U,V,W) = φ metricOffset := by
    rw [← ha, metricAffine, map_add, hc, add_zero]
  rw [metric_functional_decompose φ] at hf hh
  have hdiff : 0 < (s-(τ-1)) * φ (metricAxis0 1) := by linarith
  have hsq : 0 < s-(τ-1) := by linarith
  exact (mul_pos_iff.mp hdiff).elim (fun h => h.2)
    (fun h => False.elim ((not_lt_of_ge hsq.le) h.1))

lemma metric_separator_limit {τ : ℝ} (φ : StrongDual ℝ (MetricDualSpace n))
    (ho : ∀ o ∈ metricOpen τ, φ o < φ metricOffset) :
    φ (τ,0,0,0) ≤ φ metricOffset := by
  have hc : Continuous (fun ε : ℝ => φ (τ-ε, ε • (1 : HermitianMatrix n),
      ε • (1 : HermitianMatrix n), ε • (1 : HermitianMatrix n))) := by fun_prop
  have ht := hc.continuousAt.tendsto.mono_left
    (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  have he : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      φ (τ-ε, ε • (1 : HermitianMatrix n), ε • (1 : HermitianMatrix n),
        ε • (1 : HermitianMatrix n)) ≤ φ metricOffset := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    apply (ho _ ?_).le
    exact ⟨sub_lt_self _ hε, strictPositive_one.smul hε,
      strictPositive_one.smul hε, strictPositive_one.smul hε⟩
  simpa using le_of_tendsto ht he

theorem metric_normalized_separator {T : Matrix n n ℂ} (hT : spectralRadius ℂ T < 1)
    {τ : ℝ} {H : Matrix n n ℂ} (hfeas : MetricFeasible T τ H)
    (hmin : ∀ s J, MetricFeasible T s J → τ ≤ s) :
    ∃ φ : StrongDual ℝ (MetricDualSpace n),
      φ (metricAxis0 1) = 1 ∧
      (∀ x, φ (metricLinear T x) = 0) ∧
      φ metricOffset = τ ∧
      (∀ U V W : HermitianMatrix n, 0 ≤ U → 0 ≤ V → 0 ≤ W → φ (0,U,V,W) ≤ 0) := by
  obtain ⟨ψ, hcψ, hoψ⟩ := metric_separator hmin
  have hcoeff := metric_separator_scalar_pos hT hmin ψ hcψ hoψ
  let φ : StrongDual ℝ (MetricDualSpace n) := (ψ (metricAxis0 1))⁻¹ • ψ
  have hφ (x) : φ x = (ψ (metricAxis0 1))⁻¹ * ψ x := rfl
  have hs : φ (metricAxis0 1) = 1 := by rw [hφ, inv_mul_cancel₀ hcoeff.ne']
  have hc : ∀ x, φ (metricLinear T x) = 0 := by
    intro x
    rw [hφ, hcψ, mul_zero]
  have ho : ∀ o ∈ metricOpen τ, φ o < φ metricOffset := by
    intro o ho
    rw [hφ, hφ]
    exact mul_lt_mul_of_pos_left (hoψ o ho) (inv_pos.mpr hcoeff)
  have hn : ∀ {U V W : HermitianMatrix n},
      0 ≤ U → 0 ≤ V → 0 ≤ W → φ (0,U,V,W) ≤ 0 := metric_separator_nonpos φ ho
  have hl : τ ≤ φ metricOffset := by
    have hh := metric_separator_limit φ ho
    have he : (τ,0,0,0) = τ • metricAxis0 (n := n) 1 := by simp [metricAxis0]
    simpa only [he, map_smul, hs, smul_eq_mul, mul_one] using hh
  let J : HermitianMatrix n := ⟨H, IsSelfAdjoint.of_nonneg (zero_le_one.trans hfeas.1)⟩
  have hU : 0 ≤ J-1 := by
    change (0 : Matrix n n ℂ) ≤ H-1
    exact sub_nonneg.mpr hfeas.1
  have hV : 0 ≤ τ • (1 : HermitianMatrix n)-J := by
    change 0 ≤ τ • (1 : Matrix n n ℂ) - H
    simpa only [Algebra.algebraMap_eq_smul_one, sub_nonneg] using hfeas.2.1
  have hW : 0 ≤ metricStein T J := by
    change (0 : Matrix n n ℂ) ≤ H-Tᴴ*H*T
    exact sub_nonneg.mpr hfeas.2.2
  have hneg := hn hU hV hW
  have ha : metricAffine T (τ,J) = τ • metricAxis0 1 +
      (0,J-1,τ • (1 : HermitianMatrix n)-J,metricStein T J) := by
    simp [metricAffine, metricOffset, metricLinear, metricAxis0,
      sub_eq_add_neg, add_comm]
  have hu : φ metricOffset ≤ τ := by
    have he : φ metricOffset = φ (metricAffine T (τ,J)) := by
      rw [metricAffine, map_add, hc, add_zero]
    rw [he, ha, map_add, map_smul, hs, smul_eq_mul, mul_one]
    linarith
  exact ⟨φ, hs, hc, le_antisymm hu hl, fun _ _ _ hU hV hW => hn hU hV hW⟩

@[simp] lemma hermTrace_zero_left (B : HermitianMatrix n) : hermTrace 0 B = 0 := by
  rw [hermTrace_symm, hermTrace_zero_right]
lemma hermTrace_sub_right
    {n : Type u_184} [Fintype n] [DecidableEq n] [Nonempty n] (A B C : HermitianMatrix n) :
    hermTrace A (B-C) = hermTrace A B - hermTrace A C := by
  change (Matrix.trace ((A : Matrix n n ℂ) * ((B : Matrix n n ℂ)-(C : Matrix n n ℂ)))).re = _
  simp only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, hermTrace]
lemma hermTrace_sub_left (A B C : HermitianMatrix n) :
    hermTrace (A-B) C = hermTrace A C - hermTrace B C := by
  simpa only [hermTrace_symm] using hermTrace_sub_right C A B

lemma hermTrace_nondegenerate
    {n : Type u_184} [Fintype n] [DecidableEq n] [Nonempty n] {B : HermitianMatrix n}
    (h : ∀ A : HermitianMatrix n, hermTrace B A = 0) : B = 0 := by
  have hi : ‖toHS (B : Matrix n n ℂ)‖^2 = 0 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), hs_inner]
    rw [show (B : Matrix n n ℂ)ᴴ = B from B.property]
    exact h B
  have hz : toHS (B : Matrix n n ℂ) = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hi)
  apply Subtype.ext
  exact congrArg fromHS hz

lemma hermTrace_stein
    {n : Type u_184} [Fintype n] [DecidableEq n] [Nonempty n] (T : Matrix n n ℂ)
    (Z J : HermitianMatrix n) :
    hermTrace Z (metricStein T J) = hermTrace (Z-metricPush T Z) J := by
  have ht : Matrix.trace ((Z : Matrix n n ℂ) * (Tᴴ * (J : Matrix n n ℂ) * T)) =
      Matrix.trace ((T * (Z : Matrix n n ℂ) * Tᴴ) * (J : Matrix n n ℂ)) := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle]
    simp only [Matrix.mul_assoc]
  change (Matrix.trace ((Z : Matrix n n ℂ) *
    ((J : Matrix n n ℂ)-Tᴴ * (J : Matrix n n ℂ) * T))).re =
    (Matrix.trace (((Z : Matrix n n ℂ)-T*(Z : Matrix n n ℂ)*Tᴴ) * (J : Matrix n n ℂ))).re
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re, ht]

theorem metric_dual_certificate {T : Matrix n n ℂ} (hT : spectralRadius ℂ T < 1)
    {τ : ℝ} {H : HermitianMatrix n} (hfeas : MetricFeasible T τ H)
    (hmin : ∀ s J, MetricFeasible T s J → τ ≤ s) :
    ∃ X Y Z : HermitianMatrix n,
      0 ≤ (X : Matrix n n ℂ) ∧ 0 ≤ (Y : Matrix n n ℂ) ∧ 0 ≤ (Z : Matrix n n ℂ) ∧
      X-Y = Z-metricPush T Z ∧
      hermTrace X 1 = 1 ∧ hermTrace Y 1 = τ ∧
      hermTrace Y (H-1) = 0 ∧ hermTrace X (τ • 1-H) = 0 ∧
      hermTrace Z (metricStein T H) = 0 := by
  obtain ⟨φ, hs, hc, hval, hn⟩ := metric_normalized_separator hT hfeas hmin
  obtain ⟨Y,hY⟩ := exists_hermitian_trace_representative
    (-(φ.toLinearMap.comp metricAxis1))
  obtain ⟨X,hX⟩ := exists_hermitian_trace_representative
    (-(φ.toLinearMap.comp metricAxis2))
  obtain ⟨Z,hZ⟩ := exists_hermitian_trace_representative
    (-(φ.toLinearMap.comp metricAxis3))
  have hy (U) : φ (metricAxis1 U) = -hermTrace Y U := by
    have hh := hY U
    change -(φ (metricAxis1 U)) = _ at hh
    linarith
  have hx (V) : φ (metricAxis2 V) = -hermTrace X V := by
    have hh := hX V
    change -(φ (metricAxis2 V)) = _ at hh
    linarith
  have hz (W) : φ (metricAxis3 W) = -hermTrace Z W := by
    have hh := hZ W
    change -(φ (metricAxis3 W)) = _ at hh
    linarith
  have hYpos : 0 ≤ (Y : Matrix n n ℂ) := by
    apply (hermTrace_nonneg_iff Y).mpr
    intro U hU
    have hh := hn U 0 0 hU le_rfl le_rfl
    change φ (metricAxis1 U) ≤ 0 at hh
    rw [hy] at hh
    linarith
  have hXpos : 0 ≤ (X : Matrix n n ℂ) := by
    apply (hermTrace_nonneg_iff X).mpr
    intro V hV
    have hh := hn 0 V 0 le_rfl hV le_rfl
    change φ (metricAxis2 V) ≤ 0 at hh
    rw [hx] at hh
    linarith
  have hZpos : 0 ≤ (Z : Matrix n n ℂ) := by
    apply (hermTrace_nonneg_iff Z).mpr
    intro W hW
    have hh := hn 0 0 W le_rfl le_rfl hW
    change φ (metricAxis3 W) ≤ 0 at hh
    rw [hz] at hh
    linarith
  have hr (s : ℝ) (U V W : HermitianMatrix n) :
      φ (s,U,V,W) = s-hermTrace Y U-hermTrace X V-hermTrace Z W := by
    rw [metric_functional_decompose, hs, mul_one, hy, hx, hz]
    ring
  have hXone : hermTrace X 1 = 1 := by
    have hh := hc (1,0)
    change φ (1,0,(1:ℝ) • 1-0,metricStein T 0) = 0 at hh
    simp only [one_smul, sub_zero, map_zero] at hh
    rw [hr] at hh
    simp only [hermTrace_zero_right, sub_zero] at hh
    linarith
  have hYone : hermTrace Y 1 = τ := by
    change φ (0,-1,0,0) = τ at hval
    rw [hr] at hval
    have he : hermTrace Y (-1) = -hermTrace Y 1 := by
      simpa only [zero_sub, hermTrace_zero_right] using hermTrace_sub_right Y 0 1
    simp only [hermTrace_zero_right, sub_zero, he, zero_sub, neg_neg] at hval
    exact hval
  have hbalance : X-Y = Z-metricPush T Z := by
    apply sub_eq_zero.mp
    apply hermTrace_nondegenerate
    intro J
    have hh := hc (0,J)
    change φ (0,J,(0:ℝ) • 1-J,metricStein T J) = 0 at hh
    simp only [zero_smul, zero_sub] at hh
    rw [hr, hermTrace_stein] at hh
    have he : hermTrace X (-J) = -hermTrace X J := by
      simpa only [zero_sub, hermTrace_zero_right] using hermTrace_sub_right X 0 J
    rw [he] at hh
    simpa only [hermTrace_sub_left] using (show hermTrace X J-hermTrace Y J -
      (hermTrace Z J-hermTrace (metricPush T Z) J) = 0 by
        rw [hermTrace_sub_left] at hh
        linarith)
  have hU : 0 ≤ ((H-1 : HermitianMatrix n) : Matrix n n ℂ) := sub_nonneg.mpr hfeas.1
  have hV : 0 ≤ ((τ • 1-H : HermitianMatrix n) : Matrix n n ℂ) := by
    change (0 : Matrix n n ℂ) ≤ τ • 1 - (H : Matrix n n ℂ)
    simpa only [Algebra.algebraMap_eq_smul_one] using sub_nonneg.mpr hfeas.2.1
  have hW : 0 ≤ ((metricStein T H : HermitianMatrix n) : Matrix n n ℂ) :=
    sub_nonneg.mpr hfeas.2.2
  have hp := (hermTrace_nonneg_iff Y).mp hYpos (H-1) hU
  have hq := (hermTrace_nonneg_iff X).mp hXpos (τ • 1-H) hV
  have hrz := (hermTrace_nonneg_iff Z).mp hZpos (metricStein T H) hW
  have hh : φ (τ,H-1,τ • 1-H,metricStein T H) = τ := by
    have he : (τ,H-1,τ • 1-H,metricStein T H) = metricAffine T (τ,H) := by
      simp [metricAffine, metricOffset, metricLinear, sub_eq_add_neg, add_comm]
    rw [he, metricAffine, map_add, hc, add_zero, hval]
  rw [hr] at hh
  exact ⟨X,Y,Z,hXpos,hYpos,hZpos,hbalance,hXone,hYone,
    by linarith, by linarith, by linarith⟩


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_OptimalExtremal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_188 u_189 u_190

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset
open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped BigOperators Matrix.Norms.L2Operator
open Set Filter Metric Topology
open Set Filter Metric Topology
open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder Pointwise
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

section
variable {n : Type u_188} [Fintype n] [DecidableEq n]

lemma pos_trace_zero_mul {B C : Matrix n n ℂ}
    (hB : 0 ≤ B) (hC : 0 ≤ C) (h0 : (Matrix.trace (B*C)).re = 0) : B*C = 0 := by
  obtain ⟨R,hR⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB
  obtain ⟨S,hS⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hC
  change B = Rᴴ * R at hR
  change C = Sᴴ * S at hS
  have hp := (Matrix.nonneg_iff_posSemidef.mp hC).mul_mul_conjTranspose_same R
  have ht : Matrix.trace (R*C*Rᴴ) = 0 := by
    apply Complex.ext
    · rw [Matrix.trace_mul_cycle, ← hR]
      exact h0
    · exact (Complex.nonneg_iff.mp hp.trace_nonneg).2.symm
  have hz : R*C*Rᴴ = 0 := hp.trace_eq_zero_iff.mp ht
  have hrs : R*Sᴴ = 0 := by
    apply Matrix.self_mul_conjTranspose_eq_zero.mp
    simpa only [hS, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc] using hz
  rw [hR,hS]
  calc
    Rᴴ * R * (Sᴴ * S) = Rᴴ * (R*Sᴴ) * S := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hrs,Matrix.mul_zero,Matrix.zero_mul]

lemma pos_trace_zero_mul_reverse {B C : Matrix n n ℂ}
    (hB : 0 ≤ B) (hC : 0 ≤ C) (h0 : (Matrix.trace (B*C)).re = 0) : C*B = 0 := by
  apply pos_trace_zero_mul hC hB
  simpa only [Matrix.trace_mul_comm C B] using h0

lemma upper_slack_support {H X : Matrix n n ℂ} {τ : ℝ}
    (hX : 0 ≤ X) (hH : H ≤ τ • 1)
    (h0 : (Matrix.trace (X*(τ • 1-H))).re = 0) : H*X = τ • X := by
  have hz := pos_trace_zero_mul_reverse hX (sub_nonneg.mpr hH) h0
  have hh : τ • X = H*X := by
    simpa only [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, sub_eq_zero] using hz
  exact hh.symm

lemma lower_slack_support {H Y : Matrix n n ℂ}
    (hY : 0 ≤ Y) (hH : 1 ≤ H)
    (h0 : (Matrix.trace (Y*(H-1))).re = 0) : H*Y = Y := by
  have hz := pos_trace_zero_mul_reverse hY (sub_nonneg.mpr hH) h0
  simpa only [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] using hz

lemma endpoint_support_factor {H B X : Matrix n n ℂ} {τ : ℝ}
    (hX : X*Xᴴ = B) (hB : H*B = τ • B) : H*X = τ • X := by
  have hz : (H-τ • 1)*B = 0 := by
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul,hB,sub_self]
  rw [← hX] at hz
  have hh := (Matrix.mul_self_mul_conjTranspose_eq_zero X (H-τ • 1)).mp hz
  simpa only [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, sub_eq_zero] using hh

lemma sqrt_endpoint_support {H X : Matrix n n ℂ} {a : ℝ}
    (hH : 0 ≤ H) (ha : 0 < a) (hX : H*X = (a*a) • X) :
    CFC.sqrt H * X = a • X := by
  have hu : IsUnit (a • (1 : Matrix n n ℂ) + CFC.sqrt H) :=
    ((Matrix.PosDef.one.smul ha).add_posSemidef
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg H))).isUnit
  apply sub_eq_zero.mp
  apply hu.mul_left_cancel
  rw [Matrix.mul_zero]
  simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, ← Matrix.mul_assoc, CFC.sqrt_mul_sqrt_self H hH, hX]
  module

lemma separated_endpoint_orthogonal
    {n : Type u_188} [Fintype n] [DecidableEq n] {S X Y : Matrix n n ℂ} {a : ℝ}
    (hS : S.IsHermitian) (hX : S*X = a • X) (hY : S*Y = Y) (ha : a ≠ 1) :
    Xᴴ*Y = 0 := by
  have hx : Xᴴ*S = a • Xᴴ := by
    have hh := congrArg Matrix.conjTranspose hX
    simpa only [Matrix.conjTranspose_mul, hS.eq, Matrix.conjTranspose_smul,
      star_trivial] using hh
  have he : a • (Xᴴ*Y) = Xᴴ*Y := by
    rw [← Matrix.smul_mul, ← hx, Matrix.mul_assoc, hY]
  have hz : (a-1) • (Xᴴ*Y) = 0 := by rw [sub_smul,one_smul,he,sub_self]
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr ha)

end

section
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {n : Type u_189} [Fintype n] [DecidableEq n] [Nonempty n]

theorem exists_optimal_metric_and_dual {T : Matrix n n ℂ}
    (hT : spectralRadius ℂ T < 1) :
    ∃ (τ : ℝ) (H X Y Z : HermitianMatrix n),
      MetricFeasible T τ H ∧ (H : Matrix n n ℂ).PosDef ∧
      (∀ s J, MetricFeasible T s J → τ ≤ s) ∧
      0 ≤ (X : Matrix n n ℂ) ∧ 0 ≤ (Y : Matrix n n ℂ) ∧ 0 ≤ (Z : Matrix n n ℂ) ∧
      X-Y = Z-metricPush T Z ∧ hermTrace X 1 = 1 ∧ hermTrace Y 1 = τ ∧
      (H : Matrix n n ℂ)*(X : Matrix n n ℂ) = τ • (X : Matrix n n ℂ) ∧
      (H : Matrix n n ℂ)*(Y : Matrix n n ℂ) = (Y : Matrix n n ℂ) := by
  obtain ⟨τ,H,hf,hp,hm⟩ := exists_optimal_metric hT
  let HH : HermitianMatrix n := ⟨H,hp.isHermitian⟩
  obtain ⟨X,Y,Z,hX,hY,hZ,hb,htX,htY,hcY,hcX,_⟩ :=
    metric_dual_certificate (H := HH) hT hf (fun s J hJ => hm s J hJ)
  refine ⟨τ,HH,X,Y,Z,hf,hp,?_,hX,hY,hZ,hb,htX,htY,?_,?_⟩
  · exact hm
  · apply upper_slack_support hX
    · simpa only [Algebra.algebraMap_eq_smul_one] using hf.2.1
    · exact hcX
  · exact lower_slack_support hY hf.1 hcY

theorem endpoint_dual_factors
    {n : Type u_189} [Fintype n] [DecidableEq n] [Nonempty n]
    {H X₀ Y₀ : Matrix n n ℂ} {τ : ℝ}
    (hH : 0 ≤ H) (hX : 0 ≤ X₀) (hY : 0 ≤ Y₀) (hτ : 1 < τ)
    (hSX : H*X₀ = τ • X₀) (hSY : H*Y₀ = Y₀)
    (htrX : (Matrix.trace X₀).re = 1) (htrY : (Matrix.trace Y₀).re = τ) :
    ∃ X Y : Matrix n n ℂ,
      X*Xᴴ = X₀ ∧ Y*Yᴴ = τ⁻¹ • Y₀ ∧
      (Matrix.trace (X*Xᴴ)).re = 1 ∧ (Matrix.trace (Y*Yᴴ)).re = 1 ∧
      CFC.sqrt H * X = Real.sqrt τ • X ∧ CFC.sqrt H * Y = Y ∧ Xᴴ*Y = 0 := by
  let a := Real.sqrt τ
  have ha : 0 < a := Real.sqrt_pos.mpr (lt_trans zero_lt_one hτ)
  have ha2 : a*a = τ := Real.mul_self_sqrt (le_trans zero_le_one hτ.le)
  let X := CFC.sqrt X₀
  let Y := a⁻¹ • CFC.sqrt Y₀
  have hXh : Xᴴ = X := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg X₀)).isHermitian
  have hYh : (CFC.sqrt Y₀)ᴴ = CFC.sqrt Y₀ :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg Y₀)).isHermitian
  have hfX : X*Xᴴ = X₀ := by rw [hXh]; exact CFC.sqrt_mul_sqrt_self X₀ hX
  have hfY : Y*Yᴴ = τ⁻¹ • Y₀ := by
    change (a⁻¹ • CFC.sqrt Y₀)*(a⁻¹ • CFC.sqrt Y₀)ᴴ = _
    rw [Matrix.conjTranspose_smul,star_trivial,hYh,Matrix.smul_mul,Matrix.mul_smul,
      smul_smul,CFC.sqrt_mul_sqrt_self Y₀ hY,← mul_inv_rev,ha2]
  have hsX : H*X = τ • X := endpoint_support_factor hfX hSX
  have hsY : H*Y = Y := by
    have hs0 : H*CFC.sqrt Y₀ = CFC.sqrt Y₀ := by
      have hf : CFC.sqrt Y₀*(CFC.sqrt Y₀)ᴴ = Y₀ := by
        rw [hYh]; exact CFC.sqrt_mul_sqrt_self Y₀ hY
      simpa only [one_smul] using endpoint_support_factor (τ := 1) hf (by simpa using hSY)
    rw [Matrix.mul_smul,hs0]
  have hsX' : CFC.sqrt H*X = a • X :=
    sqrt_endpoint_support hH ha (by simpa only [ha2] using hsX)
  have hsY' : CFC.sqrt H*Y = Y := by
    simpa using sqrt_endpoint_support hH zero_lt_one (by simpa using hsY)
  refine ⟨X,Y,hfX,hfY,by rw [hfX]; exact htrX,?_,hsX',hsY',?_⟩
  · rw [hfY,Matrix.trace_smul]
    simp only [Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero,htrY,inv_mul_cancel₀ (ne_of_gt (lt_trans zero_lt_one hτ))]
  · apply separated_endpoint_orthogonal
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg H)).isHermitian hsX' hsY'
    intro hh
    rw [hh,mul_one] at ha2
    linarith

lemma metric_sqrt_isUnit
    {n : Type u_189} [Fintype n] [DecidableEq n] [Nonempty n]
    {H : Matrix n n ℂ} (hH : H.PosDef) : IsUnit (CFC.sqrt H) :=
  (CFC.isUnit_sqrt_iff H hH.posSemidef.nonneg).mpr hH.isUnit

theorem metric_similarity_contraction {T H : Matrix n n ℂ} {τ : ℝ}
    (hf : MetricFeasible T τ H) (hp : H.PosDef) :
    ‖CFC.sqrt H * T * (CFC.sqrt H)⁻¹‖ ≤ 1 := by
  let S := CFC.sqrt H
  have hS : S.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg H)).isHermitian
  have hs2 : S*S = H := CFC.sqrt_mul_sqrt_self H hp.posSemidef.nonneg
  have hu : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp (metric_sqrt_isUnit hp)
  have hi : S⁻¹*S = 1 := Matrix.nonsing_inv_mul S hu
  have hi' : S*S⁻¹ = 1 := Matrix.mul_nonsing_inv S hu
  have hp0 : (H-Tᴴ*H*T).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hf.2.2)
  have hpc := hp0.conjTranspose_mul_mul_same S⁻¹
  have hid : S⁻¹ᴴ*(H-Tᴴ*H*T)*S⁻¹ = 1-(S*T*S⁻¹)ᴴ*(S*T*S⁻¹) := by
    rw [hS.inv.eq,Matrix.mul_sub,Matrix.sub_mul]
    have h1 : S⁻¹*H*S⁻¹ = 1 := by
      rw [← hs2,← Matrix.mul_assoc,hi,Matrix.one_mul,hi']
    rw [h1,Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,hS.inv.eq,hS.eq]
    congr 1
    rw [← hs2]
    noncomm_ring
  rw [hid] at hpc
  have hle : (S*T*S⁻¹)ᴴ*(S*T*S⁻¹) ≤ 1 := hpc
  have hn := (CStarAlgebra.norm_le_one_iff_of_nonneg _
    (Matrix.posSemidef_conjTranspose_mul_self (S*T*S⁻¹)).nonneg).mpr hle
  rw [Matrix.l2_opNorm_conjTranspose_mul_self] at hn
  nlinarith [norm_nonneg (S*T*S⁻¹)]

lemma endpoint_congruence
    {n : Type u_189} [Fintype n] [DecidableEq n] [Nonempty n] {S B : Matrix n n ℂ} {a : ℝ}
    (hS : S.IsHermitian) (hB : B.IsHermitian) (hs : S*B = a • B) :
    S*B*S = (a*a) • B := by
  have hr : B*S = a • B := by
    simpa only [Matrix.conjTranspose_mul,hS.eq,hB.eq,Matrix.conjTranspose_smul,
      star_trivial] using congrArg Matrix.conjTranspose hs
  rw [hs,Matrix.smul_mul,hr,smul_smul]

lemma normalized_dual_balance {S T X₀ Y₀ Z₀ : Matrix n n ℂ} {a : ℝ}
    (hS : S.IsHermitian) (hSu : IsUnit S) (ha : a ≠ 0)
    (hX : X₀.IsHermitian) (hY : Y₀.IsHermitian)
    (hsX : S*X₀ = a • X₀) (hsY : S*Y₀ = Y₀)
    (hb : X₀-Y₀ = Z₀-T*Z₀*Tᴴ) :
    X₀-(a*a)⁻¹ • Y₀ =
      (a*a)⁻¹ • (S*Z₀*S) -
      (S*T*S⁻¹)*((a*a)⁻¹ • (S*Z₀*S))*(S*T*S⁻¹)ᴴ := by
  have hi : S⁻¹*S = 1 := Matrix.nonsing_inv_mul S ((Matrix.isUnit_iff_isUnit_det S).mp hSu)
  have hi' : S*S⁻¹ = 1 := Matrix.mul_nonsing_inv S ((Matrix.isUnit_iff_isUnit_det S).mp hSu)
  have he : (S*T*S⁻¹)*(S*Z₀*S)*(S*T*S⁻¹)ᴴ = S*(T*Z₀*Tᴴ)*S := by
    rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,hS.inv.eq,hS.eq]
    calc
      _ = S*T*(S⁻¹*S)*Z₀*(S*S⁻¹)*Tᴴ*S := by noncomm_ring
      _ = _ := by rw [hi,hi']; simp only [Matrix.mul_one]; noncomm_ring
  rw [Matrix.mul_smul,Matrix.smul_mul,he,← smul_sub,← Matrix.sub_mul,← Matrix.mul_sub,← hb]
  rw [Matrix.mul_sub,Matrix.sub_mul,endpoint_congruence hS hX hsX,
    endpoint_congruence (a := 1) hS hY (by simpa using hsY)]
  simp only [smul_sub,smul_smul,inv_mul_cancel₀ (mul_ne_zero ha ha),one_smul,one_mul]

end

open Filter Topology Set Metric
open scoped Matrix.Norms.L2Operator Kronecker MatrixOrder ComplexOrder
variable {n : Type u_190} [Fintype n] [DecidableEq n] [Nonempty n]

lemma spectrum_matrix_similarity
    {n : Type u_190} [Fintype n] [DecidableEq n] [Nonempty n]
    {S : Matrix n n ℂ} (hS : IsUnit S) (T : Matrix n n ℂ) :
    spectrum ℂ (S*T*S⁻¹) = spectrum ℂ T := by
  rw [← hS.unit_spec, ← Matrix.coe_units_inv]
  exact spectrum.units_conjugate

lemma vectorize_norm_one_of_trace
    {n : Type u_190} [Fintype n] [DecidableEq n] [Nonempty n] {X : Matrix n n ℂ}
    (hX : (Matrix.trace (X*Xᴴ)).re = 1) : ‖vectorize X‖ = 1 := by
  have hs : ‖vectorize X‖^2 = 1 := by
    calc
      _ = (inner ℂ (vectorize X) (vectorize X)).re := norm_sq_eq_re_inner (𝕜 := ℂ) (vectorize X)
      _ = (Matrix.trace (Xᴴ*X)).re := congrArg Complex.re (hs_inner X X)
      _ = 1 := by rw [Matrix.trace_mul_comm]; exact hX
  nlinarith [norm_nonneg (vectorize X)]

theorem exists_optimal_analytic_extremal {T : Matrix n n ℂ}
    (hT : spectralRadius ℂ T < 1) :
    ∃ (τ : ℝ) (H : Matrix n n ℂ),
      MetricFeasible T τ H ∧ H.PosDef ∧
      (∀ s J, MetricFeasible T s J → τ ≤ s) ∧
      (1 < τ → ∃ (X Y : Matrix n n ℂ) (F : ℂ → Matrix n n ℂ),
        ‖vectorize X‖ = 1 ∧ ‖vectorize Y‖ = 1 ∧
        CFC.sqrt H*X = Real.sqrt τ • X ∧ CFC.sqrt H*Y = Y ∧ Xᴴ*Y = 0 ∧
        AnalyticOnNhd ℂ F (closedBall 0 1) ∧
        (∀ z ∈ closedBall 0 1, ‖F z‖ ≤ 1) ∧
        Matrix.toEuclideanCLM (n := n × n) (𝕜 := ℂ)
          (completeAnalyticEval (CFC.sqrt H*T*(CFC.sqrt H)⁻¹) F)
          (vectorize X) = vectorize Y) := by
  obtain ⟨τ,H,X₀,Y₀,Z₀,hf,hp,hm,hX₀,hY₀,hZ₀,hb,htX,htY,hHX,hHY⟩ :=
    exists_optimal_metric_and_dual hT
  refine ⟨τ,H,hf,hp,hm,?_⟩
  intro hτ
  have hτ0 : 0 ≤ τ := le_trans zero_le_one hτ.le
  have ha : 0 < Real.sqrt τ := Real.sqrt_pos.mpr (lt_trans zero_lt_one hτ)
  have ha2 : Real.sqrt τ * Real.sqrt τ = τ := Real.mul_self_sqrt hτ0
  have htX' : (Matrix.trace (X₀ : Matrix n n ℂ)).re = 1 := by
    simpa only [hermTrace, selfAdjoint.val_one, Matrix.mul_one] using htX
  have htY' : (Matrix.trace (Y₀ : Matrix n n ℂ)).re = τ := by
    simpa only [hermTrace, selfAdjoint.val_one, Matrix.mul_one] using htY
  obtain ⟨X,Y,hXX,hYY,htrX,htrY,hSX,hSY,hXY⟩ :=
    endpoint_dual_factors hp.posSemidef.nonneg hX₀ hY₀ hτ hHX hHY htX' htY'
  let S := CFC.sqrt (H : Matrix n n ℂ)
  have hS : S.IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (H : Matrix n n ℂ))).isHermitian
  have hSu : IsUnit S := metric_sqrt_isUnit hp
  have hSX₀ : S*(X₀ : Matrix n n ℂ) = Real.sqrt τ • (X₀ : Matrix n n ℂ) :=
    sqrt_endpoint_support hp.posSemidef.nonneg ha (by rwa [ha2])
  have hSY₀ : S*(Y₀ : Matrix n n ℂ) = (Y₀ : Matrix n n ℂ) := by
    simpa only [one_mul, one_smul] using
      sqrt_endpoint_support (X := (Y₀ : Matrix n n ℂ)) hp.posSemidef.nonneg zero_lt_one
        (by simpa only [one_mul, one_smul] using hHY)
  have hb' : (X₀ : Matrix n n ℂ)-(Y₀ : Matrix n n ℂ) =
      (Z₀ : Matrix n n ℂ)-T*(Z₀ : Matrix n n ℂ)*Tᴴ := by
    exact congrArg (fun M : HermitianMatrix n => (M : Matrix n n ℂ)) hb
  let Z : Matrix n n ℂ := τ⁻¹ • (S*(Z₀ : Matrix n n ℂ)*S)
  have hZ : 0 ≤ Z := by
    have hz := (Matrix.nonneg_iff_posSemidef.mp hZ₀).conjTranspose_mul_mul_same S
    rw [hS.eq] at hz
    exact (hz.smul (inv_nonneg.mpr hτ0)).nonneg
  let L := CFC.sqrt Z
  have hLL : L*Lᴴ = Z := by
    rw [(Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg Z)).isHermitian.eq]
    exact CFC.sqrt_mul_sqrt_self Z hZ
  have hbal : X*Xᴴ-Y*Yᴴ = L*Lᴴ-(S*T*S⁻¹)*(L*Lᴴ)*(S*T*S⁻¹)ᴴ := by
    rw [hLL, hXX, hYY]
    simpa only [ha2] using normalized_dual_balance hS hSu ha.ne' X₀.property Y₀.property hSX₀ hSY₀ hb'
  have hD : spectralRadius ℂ (S*T*S⁻¹) < 1 := by
    simpa only [spectralRadius, spectrum_matrix_similarity hSu] using hT
  obtain ⟨F,hFa,hFn,hFe⟩ := exists_analytic_extremal_from_balance hD hbal
  exact ⟨X,Y,F,vectorize_norm_one_of_trace htrX,vectorize_norm_one_of_trace htrY,
    hSX,hSY,hXY,hFa,hFn,hFe⟩


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_ResolventPositivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexConjugate InnerProductSpace
namespace CompleteCrouzeix

lemma eigenvalue_mem_numericalRange {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    {z : ℂ} {x : EuclideanSpace ℂ (Fin n)} (hx : x ≠ 0)
    (he : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A x = z • x) :
    z ∈ numericalRange A := by
  let y := (‖x‖⁻¹ : ℝ) • x
  have hy : ‖y‖ = 1 := by simp [y, norm_smul, norm_ne_zero_iff.mpr hx]
  have he' : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A y = z • y := by
    simp [y, ContinuousLinearMap.map_smul_of_tower, he, smul_comm (‖x‖⁻¹ : ℝ) z]
  refine ⟨y, hy, ?_⟩
  rw [he', inner_smul_right, inner_self_eq_norm_sq_to_K, hy]
  simp

theorem spectrum_subset_numericalRange {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    spectrum ℂ A ⊆ numericalRange A := by
  intro z hz
  have hz' : z ∈ spectrum ℂ A.toLin' := by simpa using hz
  obtain ⟨v,hv⟩ := (Module.End.HasEigenvalue.of_mem_spectrum hz').exists_hasEigenvector
  let x : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 v
  apply eigenvalue_mem_numericalRange (x := x)
  · simpa [x] using hv.2
  · change WithLp.toLp 2 (A.toLin' v) = z • WithLp.toLp 2 v
    rw [hv.apply_eq_smul]
    rfl

end CompleteCrouzeix

end

end
end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_MetricNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_258

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
variable {n : Type u_258} [Fintype n] [DecidableEq n] [Nonempty n]
lemma matrix_contractivity_iff {n : Type u_258} [Fintype n] [DecidableEq n] [Nonempty n]
    (B : Matrix n n ℂ) : Bᴴ*B ≤ 1 ↔ ‖B‖ ≤ 1 := by
  have hn := CStarAlgebra.norm_le_one_iff_of_nonneg (Bᴴ*B)
    (Matrix.posSemidef_conjTranspose_mul_self B).nonneg
  rw [Matrix.l2_opNorm_conjTranspose_mul_self] at hn
  constructor
  · intro h
    have hh := hn.mpr h
    nlinarith [norm_nonneg B]
  · intro h
    apply hn.mp
    nlinarith [norm_nonneg B]
lemma metric_sqrt_inverse_contraction {H : Matrix n n ℂ} (hp : H.PosDef) (hH : 1 ≤ H) :
    ‖(CFC.sqrt H)⁻¹‖ ≤ 1 := by
  let S := CFC.sqrt H
  have hS : S.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg H)).isHermitian
  have hS2 : S*S = H := CFC.sqrt_mul_sqrt_self H hp.posSemidef.nonneg
  have hu : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp (metric_sqrt_isUnit hp)
  have hi : S⁻¹*S = 1 := Matrix.nonsing_inv_mul S hu
  have hi' : S*S⁻¹ = 1 := Matrix.mul_nonsing_inv S hu
  have hpos := (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hH)).conjTranspose_mul_mul_same S⁻¹
  have hid : S⁻¹ᴴ*(H-1)*S⁻¹ = 1-S⁻¹ᴴ*S⁻¹ := by
    rw [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,hS.inv.eq,← hS2]
    rw [← Matrix.mul_assoc,hi,Matrix.one_mul,hi']
  rw [hid] at hpos
  exact (matrix_contractivity_iff S⁻¹).mp hpos
lemma metric_sqrt_norm_le {T H : Matrix n n ℂ} {τ : ℝ}
    (hf : MetricFeasible T τ H) (hp : H.PosDef) : ‖CFC.sqrt H‖ ≤ Real.sqrt τ := by
  have hS : (CFC.sqrt H).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg H)).isHermitian
  have hsq := Matrix.l2_opNorm_conjTranspose_mul_self (CFC.sqrt H)
  rw [hS.eq,CFC.sqrt_mul_sqrt_self H hp.posSemidef.nonneg] at hsq
  have hτ : 0 ≤ τ := zero_le_one.trans hf.one_le
  have hs := Real.sq_sqrt hτ
  have hnorm := hf.norm_le
  nlinarith [Real.sqrt_nonneg τ,norm_nonneg (CFC.sqrt H)]
lemma metric_condition_estimate {T H : Matrix n n ℂ} {τ : ℝ}
    (hf : MetricFeasible T τ H) (hp : H.PosDef) :
    ‖CFC.sqrt H‖ * ‖(CFC.sqrt H)⁻¹‖ ≤ Real.sqrt τ := by
  calc
    _ ≤ ‖CFC.sqrt H‖*1 := mul_le_mul_of_nonneg_left (metric_sqrt_inverse_contraction hp hf.1) (norm_nonneg _)
    _ ≤ _ := by simpa only [mul_one] using metric_sqrt_norm_le hf hp
end CompleteCrouzeix

end

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_DomainBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_259

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
namespace AdmissibleDomain
variable (D : AdmissibleDomain)
variable {n m : ℕ} [Nonempty (Fin n)]

theorem exists_two_similarity (A : Matrix (Fin n) (Fin n) ℂ)
    (hW : numericalRange A ⊆ D.domain) :
    ∃ S : Matrix (Fin n) (Fin n) ℂ, IsUnit S ∧ ‖S‖ * ‖S⁻¹‖ ≤ 2 ∧
      (S*matrixAnalyticEval A D.interior.toDisk*S⁻¹)ᴴ *
        (S*matrixAnalyticEval A D.interior.toDisk*S⁻¹) ≤ 1 := by
  have hA : spectrum ℂ A ⊆ D.domain := (spectrum_subset_numericalRange A).trans hW
  let T := matrixAnalyticEval A D.interior.toDisk
  have hT : spectralRadius ℂ T < 1 := D.coordinate_stable A hA
  obtain ⟨τ,H,hf,hp,hm,hext⟩ := exists_optimal_analytic_extremal hT
  let S := CFC.sqrt H
  have hu : IsUnit S := metric_sqrt_isUnit hp
  have hS : S.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg H)).isHermitian
  have hc : (S*T*S⁻¹)ᴴ*(S*T*S⁻¹) ≤ 1 :=
    (matrix_contractivity_iff _).mpr (metric_similarity_contraction hf hp)
  have ha : Real.sqrt τ ≤ 2 := by
    by_cases hτ : τ ≤ 1
    · have hs : Real.sqrt τ ≤ 1 := by
        calc Real.sqrt τ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hτ
             _ = 1 := Real.sqrt_one
      exact hs.trans (by norm_num)
    · have ht : 1 < τ := lt_of_not_ge hτ
      have ha0 : 0 < Real.sqrt τ := Real.sqrt_pos.mpr (zero_lt_one.trans ht)
      obtain ⟨X,Y,F,hx,hy,hX,hY,hXY,hF,hn,he⟩ := hext ht
      have hX' : S*X = (Real.sqrt τ:ℂ) • X := by
        simpa only [Complex.coe_smul] using hX
      have hA' : spectrum ℂ (S*A*S⁻¹) ⊆ D.domain := by rwa [spectrum_matrix_similarity hu]
      have hc' : (matrixAnalyticEval (S*A*S⁻¹) D.interior.toDisk)ᴴ *
          matrixAnalyticEval (S*A*S⁻¹) D.interior.toDisk ≤ 1 := by
        rwa [matrixAnalyticEval_similarity hu]
      have hFa : AnalyticOnNhd ℂ (fun z => F (D.interior.toDisk z)) (closure D.domain) := by
        intro z hz
        exact (hF _ (D.interior.closure_maps hz)).comp
          (D.interior.analytic_to z (D.interior.closure_subset hz))
      have hFn : ∀ z ∈ closure D.domain, ‖F (D.interior.toDisk z)‖ ≤ 1 :=
        fun z hz => hn _ (D.interior.closure_maps hz)
      have hFe : Matrix.toEuclideanCLM (n := Fin n × Fin n) (𝕜 := ℂ)
          (completeAnalyticEval (S*A*S⁻¹) (fun z => F (D.interior.toDisk z)))
          (vectorize X) = vectorize Y := by
        rw [completeAnalyticEval_comp (S*A*S⁻¹) (D.coordinate_analytic_spectrum _ hA')
          (fun i j z hz => matrix_entry_analytic (hF _ (ball_subset_closedBall (D.toDisk_maps (hA' hz)))) i j),
          matrixAnalyticEval_similarity hu]
        exact he
      exact D.extremal_condition_bound A hW hS hu hc' ha0 hX' hY hx hy hXY hFa hFn hFe
  exact ⟨S,hu,(metric_condition_estimate hf hp).trans ha,hc⟩

end AdmissibleDomain
end CompleteCrouzeix

end

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.StructuralCrouzeix_SimilarityMinimum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Intrinsic domains, optimal similarities and matrix-valued boundary representations. -/

noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

omit [DecidableEq n] [Nonempty n] in
lemma metric_congruence_mono [DecidableEq n] [Nonempty n] {A B : Matrix n n ℂ} (h : A ≤ B)
    (R : Matrix n n ℂ) : Rᴴ*A*R ≤ Rᴴ*B*R := by
  have hp := (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr h)).conjTranspose_mul_mul_same R
  apply sub_nonneg.mp
  have he : Rᴴ*(B-A)*R = Rᴴ*B*R-Rᴴ*A*R := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
  rw [he] at hp
  exact hp.nonneg

omit [Nonempty n] in
lemma metric_gram_le_norm_sq [Nonempty n] (R : Matrix n n ℂ) :
    Rᴴ*R ≤ ‖R‖^2 • (1 : Matrix n n ℂ) := by
  simpa only [Matrix.star_eq_conjTranspose, Algebra.algebraMap_eq_smul_one] using
    (CStarAlgebra.star_mul_le_algebraMap_norm_sq (a := R))

theorem similarity_normalized_metric_feasible {T R : Matrix n n ℂ}
    (hR : IsUnit R) (hc : ‖R*T*R⁻¹‖ ≤ 1) :
    MetricFeasible T ((‖R‖*‖R⁻¹‖)^2) (‖R⁻¹‖^2 • (Rᴴ*R)) := by
  have hi : R⁻¹*R = 1 :=
    Matrix.nonsing_inv_mul R ((Matrix.isUnit_iff_isUnit_det R).mp hR)
  have hscale : 0 ≤ ‖R⁻¹‖^2 := sq_nonneg _
  have hlo := metric_congruence_mono (metric_gram_le_norm_sq R⁻¹) R
  have hgram : Rᴴ*(R⁻¹ᴴ*R⁻¹)*R = 1 := by
    calc
      _ = (R⁻¹*R)ᴴ*(R⁻¹*R) := by
        simp only [Matrix.conjTranspose_mul]
        noncomm_ring
      _ = 1 := by rw [hi]; simp
  have hlo' : 1 ≤ ‖R⁻¹‖^2 • (Rᴴ*R) := by
    simpa only [hgram, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one] using hlo
  have hupper := smul_le_smul_of_nonneg_left (metric_gram_le_norm_sq R) hscale
  have hupper' : ‖R⁻¹‖^2 • (Rᴴ*R) ≤
      algebraMap ℝ (Matrix n n ℂ) ((‖R‖*‖R⁻¹‖)^2) := by
    rw [Algebra.algebraMap_eq_smul_one]
    have he : ‖R⁻¹‖^2 • (‖R‖^2 • (1 : Matrix n n ℂ)) =
        (‖R‖*‖R⁻¹‖)^2 • (1 : Matrix n n ℂ) := by
      rw [smul_smul]
      congr 1
      ring
    rwa [he] at hupper
  let D := R*T*R⁻¹
  have hDR : D*R = R*T := by
    dsimp [D]
    rw [Matrix.mul_assoc, hi, Matrix.mul_one]
  have hstein := metric_congruence_mono ((matrix_contractivity_iff D).mpr hc) R
  have he : Rᴴ*(Dᴴ*D)*R = Tᴴ*(Rᴴ*R)*T := by
    calc
      _ = (D*R)ᴴ*(D*R) := by
        simp only [Matrix.conjTranspose_mul]
        noncomm_ring
      _ = (R*T)ᴴ*(R*T) := by rw [hDR]
      _ = _ := by simp only [Matrix.conjTranspose_mul]; noncomm_ring
  have hstein' : Tᴴ*(Rᴴ*R)*T ≤ Rᴴ*R := by
    simpa only [he, Matrix.mul_one] using hstein
  refine ⟨hlo', hupper', ?_⟩
  simpa only [Matrix.mul_smul, Matrix.smul_mul] using
    (smul_le_smul_of_nonneg_left hstein' hscale)

theorem optimal_metric_sqrt_le_similarity {T H : Matrix n n ℂ} {τ : ℝ}
    (hf : MetricFeasible T τ H)
    (hm : ∀ s J, MetricFeasible T s J → τ ≤ s)
    {R : Matrix n n ℂ} (hR : IsUnit R) (hc : ‖R*T*R⁻¹‖ ≤ 1) :
    Real.sqrt τ ≤ ‖R‖*‖R⁻¹‖ := by
  have hmin := hm _ _ (similarity_normalized_metric_feasible hR hc)
  have ht : 0 ≤ τ := zero_le_one.trans hf.one_le
  have hs := Real.sq_sqrt ht
  have hr : 0 ≤ ‖R‖*‖R⁻¹‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith [Real.sqrt_nonneg τ]

theorem optimal_metric_condition_eq_from_minimality
    {T H : Matrix n n ℂ} {τ : ℝ}
    (hf : MetricFeasible T τ H) (hp : H.PosDef)
    (hm : ∀ s J, MetricFeasible T s J → τ ≤ s) :
    ‖CFC.sqrt H‖*‖(CFC.sqrt H)⁻¹‖ = Real.sqrt τ := by
  exact le_antisymm (metric_condition_estimate hf hp)
    (optimal_metric_sqrt_le_similarity hf hm (metric_sqrt_isUnit hp)
      (metric_similarity_contraction hf hp))

end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.StructuralCrouzeix_OptimizerAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Intrinsic domains, optimal similarities and matrix-valued boundary representations. -/

noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator Kronecker
namespace StructuralCrouzeix
open CompleteCrouzeix

lemma strictPositive_posDef {n : Type*} [Fintype n] [DecidableEq n]
    {H : HermitianMatrix n} (hH : StrictPositive H) :
    (H : Matrix n n ℂ).PosDef := by
  obtain ⟨ε, hε, hle⟩ := hH
  have hp : ((H : Matrix n n ℂ) - ε • 1).PosSemidef := hle
  have hh := (Matrix.PosDef.one.smul hε).add_posSemidef hp
  simpa only [add_sub_cancel] using hh

lemma strictlyFeasible_of_stable {n : ℕ} [Nonempty (Fin n)]
    {T : Matrix (Fin n) (Fin n) ℂ} (hT : spectralRadius ℂ T < 1) :
    StrictlyFeasible T := by
  obtain ⟨τ,H,hlo,hhi,hstein⟩ := exists_strict_metric hT
  refine ⟨τ,H,H.property,strictPositive_posDef hlo,?_,?_⟩
  · simpa only [Algebra.algebraMap_eq_smul_one, AddSubgroup.coe_sub,
      selfAdjoint.val_smul, selfAdjoint.val_one] using strictPositive_posDef hhi
  · exact strictPositive_posDef hstein

lemma minimizing_posDef {n : ℕ} [Nonempty (Fin n)]
    {T H : Matrix (Fin n) (Fin n) ℂ} {τ : ℝ}
    (h : IsMinimizing T τ H) : H.PosDef := by
  have hp := (h.1.1 : (H-1).PosSemidef)
  have hh := Matrix.PosDef.one.add_posSemidef hp
  simpa only [add_sub_cancel] using hh

lemma minimizing_sqrt_le_two (D : AdmissibleDomain)
    {n : ℕ} [Nonempty (Fin n)] (A : Matrix (Fin n) (Fin n) ℂ)
    (hW : numericalRange A ⊆ D.domain)
    {τ : ℝ} {H : Matrix (Fin n) (Fin n) ℂ}
    (h : IsMinimizing (matrixAnalyticEval A D.interior.toDisk) τ H) :
    Real.sqrt τ ≤ 2 := by
  obtain ⟨R,hR,hr,hc⟩ := D.exists_two_similarity A hW
  exact (optimal_metric_sqrt_le_similarity h.1 h.2 hR
    ((matrix_contractivity_iff _).mp hc)).trans hr

theorem optimal_metric_bundle_oai (D : AdmissibleDomain)
    {n : ℕ} [Nonempty (Fin n)] (A : Matrix (Fin n) (Fin n) ℂ)
    (hW : numericalRange A ⊆ D.domain) :
    let T := matrixAnalyticEval A D.interior.toDisk
    StrictlyFeasible T ∧
    ∃ κ : ℝ, 1 ≤ κ ∧ κ ≤ 2 ∧
      (∃ H : Matrix (Fin n) (Fin n) ℂ, IsMinimizing T (κ^2) H) ∧
      ∀ H : Matrix (Fin n) (Fin n) ℂ, IsMinimizing T (κ^2) H →
        let S := CFC.sqrt H
        let A' := S*A*S⁻¹
        let B := S*T*S⁻¹
        H.PosDef ∧ IsUnit S ∧
        B = matrixAnalyticEval A' D.interior.toDisk ∧
        Bᴴ*B ≤ 1 ∧ spectralRadius ℂ B < 1 ∧
        ‖S‖*‖S⁻¹‖ = κ ∧
        (∀ R : Matrix (Fin n) (Fin n) ℂ, IsUnit R →
          (R*T*R⁻¹)ᴴ*(R*T*R⁻¹) ≤ 1 → κ ≤ ‖R‖*‖R⁻¹‖) := by
  let T := matrixAnalyticEval A D.interior.toDisk
  have hA : spectrum ℂ A ⊆ D.domain := (spectrum_subset_numericalRange A).trans hW
  have hT : spectralRadius ℂ T < 1 := D.coordinate_stable A hA
  refine ⟨strictlyFeasible_of_stable hT, ?_⟩
  obtain ⟨τ,H₀,hf,hp,hm⟩ := exists_optimal_metric hT
  have ht : 0 ≤ τ := zero_le_one.trans hf.one_le
  have hsq : (Real.sqrt τ)^2 = τ := Real.sq_sqrt ht
  have hk : 1 ≤ Real.sqrt τ := by
    have hh := Real.sqrt_le_sqrt hf.one_le
    simpa only [Real.sqrt_one] using hh
  refine ⟨Real.sqrt τ,hk,minimizing_sqrt_le_two D A hW ⟨hf,hm⟩,?_,?_⟩
  · exact ⟨H₀,by simpa only [hsq] using (show IsMinimizing T τ H₀ from ⟨hf,hm⟩)⟩
  intro H hH
  have hH' : IsMinimizing T τ H := by simpa only [hsq] using hH
  have hpos := minimizing_posDef hH'
  have hu := metric_sqrt_isUnit hpos
  refine ⟨hpos,hu,?_,?_,?_,?_,?_⟩
  · exact (matrixAnalyticEval_similarity hu A D.interior.toDisk).symm
  · exact (matrix_contractivity_iff _).mpr (metric_similarity_contraction hH'.1 hpos)
  · simpa only [spectralRadius,spectrum_matrix_similarity hu] using hT
  · exact optimal_metric_condition_eq_from_minimality hH'.1 hpos hH'.2
  · intro R hR hc
    exact optimal_metric_sqrt_le_similarity hH'.1 hH'.2 hR
      ((matrix_contractivity_iff _).mp hc)

end StructuralCrouzeix
end

end OAI
end

theorem solution : type_of% @OAI.StructuralCrouzeix.optimal_metric_bundle_oai := @OAI.StructuralCrouzeix.optimal_metric_bundle_oai
