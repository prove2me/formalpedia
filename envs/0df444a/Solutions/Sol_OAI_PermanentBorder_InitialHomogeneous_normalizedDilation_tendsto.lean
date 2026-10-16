-- Prove2me | solution 1 for OAI.PermanentBorder.InitialHomogeneous.normalizedDilation_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:44:18.303986+00:00
-- url     : https://prove2.me/submissions/38690ac1-d4c2-4902-ac2b-fcd5a8d4af46

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/InitialForm.lean:L70-L93
-- (upload_full_project.md Phase 4): solution for node OAI.PermanentBorder.InitialHomogeneous.normalizedDilation_tendsto. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts
import Definitions.Def_OAI_Algebra_Determinantal_KernelCharts
import Definitions.Def_OAI_Algebra_Determinantal_SchurDifferentials
import Definitions.Def_OAI_Algebra_Determinantal_SchurLifts
import Definitions.Def_OAI_Algebra_Determinantal_BilinearCounts
import Definitions.Def_OAI_Algebra_Determinantal_RegularSections
import Definitions.Def_OAI_Algebra_Determinantal_SmoothSlices
import Definitions.Def_OAI_Algebra_Determinantal_SliceCertificates
import Definitions.Def_OAI_Algebra_Determinantal_GenericPolars
import Definitions.Def_OAI_Algebra_Determinantal_RankTransfer
import Definitions.Def_OAI_Algebra_Determinantal_Model
import Definitions.Def_OAI_Algebra_Determinantal_BorderPolars
import Definitions.Def_OAI_Algebra_Determinantal_InitialForm

-- ---- from OAI.Algebra.Determinantal.SmoothSlices ----
namespace OAI

namespace PermanentBorder.SliceParameters

open MvPolynomial

lemma homogeneous_aeval_scale {K L σ : Type*} [CommSemiring K] [CommSemiring L]
    [Algebra K L] {f : MvPolynomial σ K} {r : ℕ} (hf : f.IsHomogeneous r)
    (a : L) (x : σ → L) :
    aeval (fun i => a * x i) f = a^r * aeval x f := by
  classical
  conv_lhs => rw [← f.support_sum_monomial_coeff]
  conv_rhs => rw [← f.support_sum_monomial_coeff]
  simp only [map_sum, aeval_monomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [hf.degree_eq_sum_deg_support hs]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

end PermanentBorder.SliceParameters

namespace PermanentBorder.CI
open MvPolynomial Topology
open scoped Topology Classical
variable {ι : Type*} [Fintype ι]

end PermanentBorder.CI

namespace PermanentBorder.SliceParameters
open MvPolynomial

end PermanentBorder.SliceParameters

namespace PermanentBorder.SliceParameters
open MvPolynomial

end PermanentBorder.SliceParameters

namespace PermanentBorder.SliceParameters
open MvPolynomial

section Matrix
variable {K σ ι : Type*} [CommRing K] [Finite σ] [Fintype ι]

end Matrix

section Surjectivity
variable {K σ ι : Type*} [Field K] [Finite σ] [Fintype ι]

end Surjectivity
end PermanentBorder.SliceParameters

end OAI

-- ---- from OAI.Algebra.Determinantal.InitialForm ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

namespace PermanentBorder
open MvPolynomial Filter
open scoped Topology

namespace InitialHomogeneous
variable {σ : Type*} [Fintype σ]

lemma dilation_eq_aeval (t : ℂ) :
    dilation (σ := σ) t = aeval (fun i => C t * X i) := by
  classical
  unfold dilation affineSubstitution
  congr 1
  funext i
  simp [apply_ite]

lemma dilation_monomial (t : ℂ) (e : σ →₀ ℕ) (c : ℂ) :
    dilation t (monomial e c) = t ^ e.degree • monomial e c := by
  rw [dilation_eq_aeval]
  have h := SliceParameters.homogeneous_aeval_scale
    (isHomogeneous_monomial c (n := e.degree) rfl) (C t) (fun i : σ => X i)
  simpa only [aeval_X_left_apply, ← map_pow, smul_eq_C_mul] using h

lemma coeff_dilation (t : ℂ) (q : Poly σ) (e : σ →₀ ℕ) :
    (dilation t q).coeff e = t ^ e.degree * q.coeff e := by
  classical
  induction q using MvPolynomial.induction_on' with
  | monomial s c =>
      rw [dilation_monomial, coeff_smul]
      by_cases h : s = e
      · subst s; rfl
      · simp [coeff_monomial, h]
  | add p q hp hq =>
      simp only [map_add, coeff_add, hp, hq, mul_add]

omit [Fintype σ] in
lemma coeff_eq_zero_of_lower_components {q : Poly σ} {r : ℕ}
    (hlow : ∀ j < r, homogeneousComponent j q = 0)
    (e : σ →₀ ℕ) (he : e.degree < r) : q.coeff e = 0 := by
  have h := congrArg (fun p : Poly σ => p.coeff e) (hlow e.degree he)
  simpa [coeff_homogeneousComponent] using h

lemma coeff_normalizedDilation {q : Poly σ} {r : ℕ}
    (hlow : ∀ j < r, homogeneousComponent j q = 0)
    {t : ℂ} (ht : t ≠ 0) (e : σ →₀ ℕ) :
    (normalizedDilation r q t).coeff e =
      if e.degree < r then 0 else t ^ (e.degree - r) * q.coeff e := by
  simp only [normalizedDilation, coeff_smul, smul_eq_mul, coeff_dilation]
  by_cases he : e.degree < r
  · simp [he, coeff_eq_zero_of_lower_components hlow e he]
  · rw [ite_eq_right he]
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt he)
    rw [hk, Nat.add_sub_cancel_left, pow_add]
    rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero r ht), one_mul]

/-- Cancellation of the pole gives coefficientwise convergence along any filter
approaching zero through nonzero complex values. -/
theorem normalizedDilation_tendsto {α : Type*} {l : Filter α}
    {q : Poly σ} {r : ℕ}
    (hlow : ∀ j < r, homogeneousComponent j q = 0)
    {t : α → ℂ} (ht : Tendsto t l (𝓝 0))
    (hne : ∀ᶠ j in l, t j ≠ 0) (e : σ →₀ ℕ) :
    Tendsto (fun j => (normalizedDilation r q (t j)).coeff e)
      l (𝓝 ((homogeneousComponent r q).coeff e)) := by
  have heq : (fun j => (normalizedDilation r q (t j)).coeff e) =ᶠ[l]
      (fun j => if e.degree < r then 0 else t j ^ (e.degree-r) * q.coeff e) :=
    hne.mono fun j hj => coeff_normalizedDilation hlow hj e
  apply Tendsto.congr' heq.symm
  rw [coeff_homogeneousComponent]
  by_cases hlo : e.degree < r
  · simp only [hlo, ite_true, ite_eq_right (Nat.ne_of_lt hlo)]
    exact tendsto_const_nhds
  · simp only [hlo, ite_false]
    by_cases he : e.degree = r
    · simp only [he, Nat.sub_self, pow_zero, one_mul, ite_true]
      exact tendsto_const_nhds
    · have hk : e.degree-r ≠ 0 := by omega
      simpa only [ite_eq_right he, zero_pow hk, zero_mul] using
        (ht.pow (e.degree-r)).mul_const (q.coeff e)

end InitialHomogeneous

end PermanentBorder

end OAI

-- ---- platform node ----
open OAI OAI.PermanentBorder OAI.PermanentBorder.InitialHomogeneous
open MvPolynomial Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.PermanentBorder.InitialHomogeneous.normalizedDilation_tendsto := @_root_.OAI.PermanentBorder.InitialHomogeneous.normalizedDilation_tendsto
