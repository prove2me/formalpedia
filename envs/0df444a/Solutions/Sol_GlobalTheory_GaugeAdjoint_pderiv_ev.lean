-- Prove2me | solution 1 for GlobalTheory.GaugeAdjoint.pderiv_ev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:26:24.249109+00:00
-- url     : https://prove2.me/submissions/c9053d27-f759-4e1f-b5f2-a73069da9840

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_IntAASubstOfHasSubst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ConstantCoeffEv
import Theorems.Thm_GlobalTheory_FormalCalc_formalExp_zero
import Theorems.Thm_GlobalTheory_FormalCalc_formalLog_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FormalCalc.formalExp_zero
attribute [local simp] GlobalTheory.FormalCalc.formalLog_one


section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
namespace GlobalTheory.GaugeAdjoint
open GlobalTheory.FormalCalc GlobalTheory.IntSeries
section Ev
variable {k : Type} [CommRing k] {d m n p : ℕ}
private theorem coeff_subst_congr_lemma {σ τ : Type} [Finite σ] [Finite τ] {A : σ → MvPowerSeries τ k}
    (hA : ∀ q, constantCoeff (A q) = 0) {g g' : MvPowerSeries σ k} {x : τ →₀ ℕ}
    (hgg : ∀ y : σ →₀ ℕ, y.degree ≤ x.degree → coeff y g = coeff y g') :
    coeff x (subst A g) = coeff x (subst A g') := by
  have hT : truncTotal (x.degree + 1) g = truncTotal (x.degree + 1) g' := by
    ext y
    rw [coeff_truncTotal_eq_ite, coeff_truncTotal_eq_ite]
    split_ifs with hy
    · exact hgg y (Nat.lt_succ_iff.mp hy)
    · rfl
  have e1 := congrArg (MvPolynomial.coeff x)
    (truncTotal_subst_eq_truncTotal_truncTotal_subst (k := x.degree + 1) (f := g) hA)
  have e2 := congrArg (MvPolynomial.coeff x)
    (truncTotal_subst_eq_truncTotal_truncTotal_subst (k := x.degree + 1) (f := g') hA)
  rw [coeff_truncTotal _ (Nat.lt_succ_self _)] at e1 e2
  rw [e1, e2, hT]
private theorem pderiv_subst_coe_mvPolynomial_eq_sum {σ τ : Type} [Fintype σ] [DecidableEq σ]
    {A : σ → MvPowerSeries τ k} (hA : HasSubst A) (s : τ) (q : MvPolynomial σ k) :
    pderiv k s (subst A (q : MvPowerSeries σ k)) =
      ∑ r, subst A (pderiv k r (q : MvPowerSeries σ k)) * pderiv k s (A r) := by
  induction q using MvPolynomial.induction_on with
  | C c =>
    rw [MvPolynomial.coe_C, subst_C, pderiv_C]
    symm
    apply Finset.sum_eq_zero
    intro r _
    rw [pderiv_C, ← substAlgHom_apply hA, map_zero, zero_mul]
  | add f g hf hg =>
    simp only [MvPolynomial.coe_add, subst_add hA, map_add, hf, hg, add_mul, Finset.sum_add_distrib]
  | mul_X f r0 hf =>
    rw [MvPolynomial.coe_mul, MvPolynomial.coe_X]
    simp only [← substAlgHom_apply hA] at hf ⊢
    have hX : ∀ r, substAlgHom hA (pderiv k r (X r0 : MvPowerSeries σ k)) = if r = r0 then 1 else 0 := by
      intro r
      split_ifs with hr
      · subst hr
        rw [pderiv_X_self, map_one]
      · rw [pderiv_X_of_ne (Ne.symm hr), map_zero]
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, substAlgHom_X, hX, hf, mul_ite,
      mul_one, mul_zero, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Finset.mul_sum, mul_assoc]
private theorem pderiv_subst_eq_sum_of_constantCoeff_eq_zero {σ τ : Type} [Fintype σ] [DecidableEq σ] [Finite τ]
    {A : σ → MvPowerSeries τ k} (hA : ∀ r, constantCoeff (A r) = 0) (f : MvPowerSeries σ k) (s : τ) :
    pderiv k s (subst A f) = ∑ r, subst A (pderiv k r f) * pderiv k s (A r) := by
  classical
  have hS : HasSubst A := hasSubst_of_constantCoeff_zero hA
  ext x
  have h1 : coeff (x + Finsupp.single s 1) (subst A f) =
      coeff (x + Finsupp.single s 1)
        (subst A ((truncTotal (x.degree + 2) f : MvPolynomial σ k) : MvPowerSeries σ k)) := by
    apply coeff_subst_congr_lemma hA
    intro z hz
    rw [MvPolynomial.coeff_coe, coeff_truncTotal]
    rw [map_add, Finsupp.degree_single] at hz
    omega
  rw [coeff_pderiv, h1, ← coeff_pderiv, pderiv_subst_coe_mvPolynomial_eq_sum hS]
  simp only [map_sum, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun y hy => ?_
  congr 1
  apply coeff_subst_congr_lemma hA
  intro z hz
  have hxy := Finset.HasAntidiagonal.mem_antidiagonal.mp hy
  have h2 : y.1.degree ≤ x.degree := by
    rw [← hxy, map_add]
    omega
  rw [coeff_pderiv, coeff_pderiv, MvPolynomial.coeff_coe, coeff_truncTotal]
  rw [map_add, Finsupp.degree_single]
  omega
end Ev
end GlobalTheory.GaugeAdjoint
end

set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.GaugeAdjoint
open GlobalTheory.FormalCalc GlobalTheory.IntSeries
variable {k : Type} [CommRing k] {d m n p : ℕ}
namespace GlobalTheory.GaugeAdjoint
theorem _root_.solution {a : Fin m → Pt k n d} (ha : ∀ j i, constantCoeff (a j i) = 0)
    (f : PS k m d) (s : Fin n × Fin d) :
    pderiv k s (ev a f) = ∑ j, ∑ i, ev a (pderiv k (j, i) f) * pderiv k s (a j i) := by
  unfold ev
  rw [pderiv_subst_eq_sum_of_constantCoeff_eq_zero (A := fun q : Fin m × Fin d => a q.1 q.2) (fun q => ha q.1 q.2),
    Fintype.sum_prod_type]
end GlobalTheory.GaugeAdjoint
