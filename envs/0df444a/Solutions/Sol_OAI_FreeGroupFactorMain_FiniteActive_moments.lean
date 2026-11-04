-- Prove2me | solution 1 for OAI.FreeGroupFactorMain.FiniteActive.moments
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T03:48:16.415197+00:00
-- url     : https://prove2.me/submissions/5a4b6983-b290-48b3-abe2-8bdbe37f6e0c

import Mathlib
import Definitions.Def_FreeGroupFactorProof18

set_option linter.all false

section
namespace OAI

noncomputable section

universe uA uι

open Set Metric
open scoped NNReal Topology BigOperators

open scoped BigOperators ContDiff
namespace FreeGroupFactorMain
namespace PolynomialFlow

section

variable {A : Type uA} [CStarAlgebra A]
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

 omit [DecidableEq ι] in
 theorem smooth_wordList (w : List (ι × Bool)) :
    ContDiff ℝ ∞ (wordList (A := A) w) := by
  induction w with
  | nil =>
    change ContDiff ℝ ∞ (fun _ : ι → A => (1 : A))
    exact contDiff_const
  | cons a w ih =>
    rcases a with ⟨i, b⟩
    cases b
    · change ContDiff ℝ ∞ (fun X : ι → A => star (X i) * wordList w X)
      exact ((starL ℝ (A := A)).contDiff.comp (contDiff_apply ℝ A i)).mul ih
    · change ContDiff ℝ ∞ (fun X : ι → A => X i * wordList w X)
      exact (contDiff_apply ℝ A i).mul ih

 theorem smooth_word (g : FreeGroup ι) : ContDiff ℝ ∞ (word (A := A) g) :=
  smooth_wordList _

 theorem smooth_hamiltonian (S : A) (h : FreeGroup ι →₀ ℝ) :
    ContDiff ℝ ∞ (hamiltonian S h) := by
  classical
  unfold hamiltonian Finsupp.sum
  apply ContDiff.sum
  intro g hg
  exact (contDiff_const (c := (h g : ℂ))).smul
    (((smooth_word (A := A) g).mul (contDiff_const (c := S))).mul
      ((starL ℝ (A := A)).contDiff.comp (smooth_word (A := A) g)))

 theorem smooth_field (S : A) (h : ι → FreeGroup ι →₀ ℝ) :
    ContDiff ℝ ∞ (field S h) := by
  apply contDiff_pi.mpr
  intro j
  exact (contDiff_const (c := Complex.I)).smul
    ((smooth_hamiltonian S (h j)).mul (contDiff_apply ℝ A j))

 omit [Fintype ι] in
 theorem selfAdjoint_hamiltonian (S : A) (hS : IsSelfAdjoint S)
    (h : FreeGroup ι →₀ ℝ) (X : ι → A) : IsSelfAdjoint (hamiltonian S h X) := by
  classical
  unfold hamiltonian Finsupp.sum
  change star (∑ g ∈ h.support, (h g : ℂ) • (word g X * S * star (word g X))) = _
  simp only [star_sum, star_smul, Complex.star_def, Complex.conj_ofReal, star_mul, star_star, hS.star_eq, mul_assoc]

end

section
open scoped NNReal BigOperators
variable {A : Type uA} [CStarAlgebra A]
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end

variable {A : Type uA} [CStarAlgebra A]
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

theorem smooth_solution (S : A) (h : ι → FreeGroup ι →₀ ℝ)
    (X : ℝ → ι → A) (hX : ∀ t, HasDerivAt X (field S h (X t)) t) :
    ContDiff ℝ ∞ X := by
  have hdiff : Differentiable ℝ X := fun t => (hX t).differentiableAt
  apply contDiff_infty.mpr
  intro n
  induction n with
  | zero => exact contDiff_zero.mpr hdiff.continuous
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_deriv]
    refine ⟨hdiff, by simp, ?_⟩
    have heq : deriv X = fun t => field S h (X t) := funext fun t => (hX t).deriv
    rw [heq]
    exact (contDiff_infty.mp (smooth_field S h) n).comp ih

end PolynomialFlow
end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

noncomputable section

universe uA uι

open Set Metric
open scoped NNReal Topology BigOperators ContDiff

open scoped BigOperators ContDiff
namespace FreeGroupFactorMain
namespace NCPolynomial

inductive Expr (ι : Type uι) where
  | scalar : ℂ → Expr ι
  | gen : ι → Expr ι
  | add : Expr ι → Expr ι → Expr ι
  | mul : Expr ι → Expr ι → Expr ι

def degree {ι : Type uι} : Expr ι → ℕ
  | .scalar _ => 0
  | .gen _ => 1
  | .add p q => max (degree p) (degree q)
  | .mul p q => degree p + degree q

def mass {ι : Type uι} : Expr ι → ℝ
  | .scalar c => ‖c‖
  | .gen _ => 1
  | .add p q => mass p + mass q
  | .mul p q => mass p * mass q

def eval {ι : Type uι} {A : Type uA} [Semiring A] [Algebra ℂ A] (X : ι → A) : Expr ι → A
  | .scalar c => algebraMap ℂ A c
  | .gen i => X i
  | .add p q => eval X p + eval X q
  | .mul p q => eval X p * eval X q

def delta {ι : Type uι} (V : ι → Expr ι) : Expr ι → Expr ι
  | .scalar _ => .scalar 0
  | .gen i => V i
  | .add p q => .add (delta V p) (delta V q)
  | .mul p q => .add (.mul (delta V p) q) (.mul p (delta V q))

 theorem mass_nonneg {ι : Type uι} (p : Expr ι) : 0 ≤ mass p := by
  induction p with
  | scalar c => exact norm_nonneg _
  | gen i => exact zero_le_one
  | add p q hp hq => exact add_nonneg hp hq
  | mul p q hp hq => exact mul_nonneg hp hq

 theorem degree_delta {ι : Type uι} (V : ι → Expr ι) (J : ℕ)
    (hV : ∀ i, degree (V i) ≤ J + 1) (p : Expr ι) :
    degree (delta V p) ≤ degree p + J := by
  induction p with
  | scalar c => simp [delta, degree]
  | gen i => simpa [delta, degree, Nat.add_comm] using hV i
  | add p q hp hq =>
    simp only [delta, degree]
    omega
  | mul p q hp hq =>
    simp only [delta, degree]
    omega

 theorem mass_delta {ι : Type uι} (V : ι → Expr ι) (B : ℝ) (hB : 0 ≤ B)
    (hV : ∀ i, mass (V i) ≤ B) (p : Expr ι) :
    mass (delta V p) ≤ mass p * (degree p : ℝ) * B := by
  induction p with
  | scalar c => simp [delta, mass, degree]
  | gen i => simpa [delta, mass, degree] using hV i
  | add p q hp hq =>
    simp only [delta, mass, degree]
    have hl : (degree p : ℝ) ≤ (max (degree p) (degree q) : ℕ) := by exact_mod_cast le_max_left _ _
    have hr : (degree q : ℝ) ≤ (max (degree p) (degree q) : ℕ) := by exact_mod_cast le_max_right _ _
    calc
      mass (delta V p) + mass (delta V q) ≤
          mass p * (degree p : ℝ) * B + mass q * (degree q : ℝ) * B := add_le_add hp hq
      _ ≤ mass p * (max (degree p) (degree q) : ℕ) * B +
          mass q * (max (degree p) (degree q) : ℕ) * B := by
        gcongr
        · exact mass_nonneg p
        · exact mass_nonneg q
      _ = _ := by ring
  | mul p q hp hq =>
    simp only [delta, mass, degree, Nat.cast_add]
    calc
      mass (delta V p) * mass q + mass p * mass (delta V q) ≤
          (mass p * (degree p : ℝ) * B) * mass q +
          mass p * (mass q * (degree q : ℝ) * B) := by
        exact add_le_add (mul_le_mul_of_nonneg_right hp (mass_nonneg q))
          (mul_le_mul_of_nonneg_left hq (mass_nonneg p))
      _ = _ := by ring

 theorem degree_iterate {ι : Type uι} (V : ι → Expr ι) (J : ℕ)
    (hV : ∀ i, degree (V i) ≤ J + 1) (p : Expr ι) (r : ℕ) :
    degree ((delta V)^[r] p) ≤ degree p + r * J := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    exact (degree_delta V J hV _).trans (by simpa [Nat.add_mul, Nat.add_assoc] using Nat.add_le_add_right ih J)

 theorem mass_iterate {ι : Type uι} (V : ι → Expr ι) (J : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hdeg : ∀ i, degree (V i) ≤ J + 1) (hmass : ∀ i, mass (V i) ≤ B)
    (p : Expr ι) (r : ℕ) :
    mass ((delta V)^[r] p) ≤
      mass p * (B * ((degree p : ℝ) + J)) ^ r * (r.factorial : ℝ) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    have hd : (degree ((delta V)^[r] p) : ℝ) ≤ ((degree p : ℝ) + J) * (r + 1) := by
      have := degree_iterate V J hdeg p r
      have hh : (degree ((delta V)^[r] p) : ℝ) ≤ (degree p : ℝ) + r * J := by exact_mod_cast this
      nlinarith [Nat.cast_nonneg (α := ℝ) (degree p)]
    calc
      mass (delta V ((delta V)^[r] p)) ≤
          mass ((delta V)^[r] p) * (degree ((delta V)^[r] p) : ℝ) * B :=
        mass_delta V B hB hmass _
      _ ≤ (mass p * (B * ((degree p : ℝ) + J)) ^ r * (r.factorial : ℝ)) *
          (((degree p : ℝ) + J) * (r + 1)) * B := by
        gcongr
        exact mul_nonneg (mul_nonneg (mass_nonneg p) (pow_nonneg (mul_nonneg hB (by positivity)) _)) (by positivity)
      _ = _ := by simp [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add]; ring

 theorem norm_eval {ι : Type uι} {A : Type uA} [NormedRing A] [NormedAlgebra ℂ A] [NormOneClass A]
    (X : ι → A) (R : ℝ) (hR : 1 ≤ R) (hX : ∀ i, ‖X i‖ ≤ R) (p : Expr ι) :
    ‖eval X p‖ ≤ mass p * R ^ degree p := by
  induction p with
  | scalar c => simp [eval, mass, degree, norm_algebraMap']
  | gen i => simpa [eval, mass, degree] using hX i
  | add p q hp hq =>
    simp only [eval, mass, degree]
    calc
      ‖eval X p + eval X q‖ ≤ ‖eval X p‖ + ‖eval X q‖ := norm_add_le _ _
      _ ≤ mass p * R ^ degree p + mass q * R ^ degree q := add_le_add hp hq
      _ ≤ mass p * R ^ max (degree p) (degree q) +
          mass q * R ^ max (degree p) (degree q) := by
        gcongr
        · exact mass_nonneg p
        · exact le_max_left _ _
        · exact mass_nonneg q
        · exact le_max_right _ _
      _ = _ := by ring
  | mul p q hp hq =>
    simp only [eval, mass, degree, pow_add]
    calc
      ‖eval X p * eval X q‖ ≤ ‖eval X p‖ * ‖eval X q‖ := norm_mul_le _ _
      _ ≤ (mass p * R ^ degree p) * (mass q * R ^ degree q) := by
        exact mul_le_mul hp hq (norm_nonneg _) (mul_nonneg (mass_nonneg _) (pow_nonneg (by linarith) _))
      _ = _ := by ring

 theorem hasDerivAt_eval {ι : Type uι} {A : Type uA} [NormedRing A] [NormedAlgebra ℂ A]
    (X : ℝ → ι → A) (V : ι → Expr ι) (t : ℝ)
    (hX : ∀ i, HasDerivAt (fun s => X s i) (eval (X t) (V i)) t) (p : Expr ι) :
    HasDerivAt (fun s => eval (X s) p) (eval (X t) (delta V p)) t := by
  induction p with
  | scalar c => simpa [eval, delta] using hasDerivAt_const t (algebraMap ℂ A c)
  | gen i => exact hX i
  | add p q hp hq => exact hp.add hq
  | mul p q hp hq => exact hp.mul hq

theorem norm_eval_iterate {ι : Type uι} {A : Type uA} [NormedRing A] [NormedAlgebra ℂ A]
    [NormOneClass A] (X : ι → A) (R : ℝ) (hR : 1 ≤ R) (hX : ∀ i, ‖X i‖ ≤ R)
    (V : ι → Expr ι) (J : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hdeg : ∀ i, degree (V i) ≤ J + 1) (hmass : ∀ i, mass (V i) ≤ B)
    (p : Expr ι) (r : ℕ) :
    ‖eval X ((delta V)^[r] p)‖ ≤
      (mass p * R ^ degree p) * (B * ((degree p : ℝ) + J) * R ^ J) ^ r *
        (r.factorial : ℝ) := by
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  calc
    ‖eval X ((delta V)^[r] p)‖ ≤ mass ((delta V)^[r] p) * R ^ degree ((delta V)^[r] p) :=
      norm_eval X R hR hX _
    _ ≤ (mass p * (B * ((degree p : ℝ) + J)) ^ r * (r.factorial : ℝ)) *
        R ^ (degree p + r * J) := by
      apply mul_le_mul (mass_iterate V J B hB hdeg hmass p r)
      · exact pow_le_pow_right₀ hR (degree_iterate V J hdeg p r)
      · exact pow_nonneg hR0 _
      · exact mul_nonneg (mul_nonneg (mass_nonneg p) (pow_nonneg (mul_nonneg hB (by positivity)) _)) (by positivity)
    _ = _ := by simp only [pow_add, mul_pow, ← pow_mul]; rw [Nat.mul_comm r J]; ring

theorem smooth_eval {ι : Type uι} {A : Type uA} [NormedRing A] [NormedAlgebra ℂ A]
    (X : ℝ → ι → A) (hX : ∀ i, ContDiff ℝ ∞ (fun t => X t i)) (p : Expr ι) :
    ContDiff ℝ ∞ (fun t => eval (X t) p) := by
  induction p with
  | scalar c => exact contDiff_const
  | gen i => exact hX i
  | add p q hp hq => exact hp.add hq
  | mul p q hp hq => exact hp.mul hq

end NCPolynomial
end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

noncomputable section

universe uA uB uG uι

open Set Metric
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain
namespace TraceCocycle

abbrev CF (G : Type uG) := G →₀ ℂ

def shift {G : Type uG} [Group G] (g : G) : CF G ≃+ CF G :=
  Finsupp.domCongr (MulAut.conj g).toEquiv

@[simp] theorem shift_apply {G : Type uG} [Group G] (g : G) (p : CF G) (b : G) :
    shift g p b = p (g⁻¹ * b * g) := rfl

@[simp] theorem shift_one {G : Type uG} [Group G] (p : CF G) : shift (1 : G) p = p := by
  ext b
  simp

@[simp] theorem shift_mul {G : Type uG} [Group G] (g b : G) (p : CF G) :
    shift (g * b) p = shift g (shift b p) := by
  ext c
  simp [mul_assoc]

def action (G : Type uG) [Group G] : G →* MulAut (Multiplicative (CF G)) where
  toFun g := AddEquiv.toMultiplicative (shift g)
  map_one' := by
    apply MulEquiv.ext
    intro p
    exact shift_one p.toAdd
  map_mul' g b := by
    apply MulEquiv.ext
    intro p
    exact shift_mul g b p.toAdd

def graph {ι : Type uι} (h : ι → CF (FreeGroup ι)) :
    FreeGroup ι →* (Multiplicative (CF (FreeGroup ι)) ⋊[action (FreeGroup ι)] FreeGroup ι) :=
  FreeGroup.lift (fun i => ⟨Multiplicative.ofAdd (h i), FreeGroup.of i⟩)

@[simp] theorem graph_right {ι : Type uι} (h : ι → CF (FreeGroup ι)) (g : FreeGroup ι) :
    (graph h g).right = g := by
  have hr : SemidirectProduct.rightHom.comp (graph h) = MonoidHom.id _ := by
    ext i
    simp [graph]
  exact DFunLike.congr_fun hr g

def cocycle {ι : Type uι} (h : ι → CF (FreeGroup ι)) (g : FreeGroup ι) : CF (FreeGroup ι) :=
  (graph h g).left.toAdd

@[simp] theorem cocycle_of {ι : Type uι} (h : ι → CF (FreeGroup ι)) (i : ι) :
    cocycle h (FreeGroup.of i) = h i := by
  simp [cocycle, graph]

@[simp] theorem cocycle_one {ι : Type uι} (h : ι → CF (FreeGroup ι)) : cocycle h 1 = 0 := by
  simp [cocycle]

theorem cocycle_mul {ι : Type uι} (h : ι → CF (FreeGroup ι)) (g b : FreeGroup ι) :
    cocycle h (g * b) = cocycle h g + shift g (cocycle h b) := by
  unfold cocycle
  rw [map_mul, SemidirectProduct.mul_left, graph_right]
  rfl

theorem cocycle_inv {ι : Type uι} (h : ι → CF (FreeGroup ι)) (g : FreeGroup ι) :
    cocycle h g⁻¹ = -shift g⁻¹ (cocycle h g) := by
  have he := cocycle_mul h g⁻¹ g
  simp only [inv_mul_cancel, cocycle_one] at he
  exact eq_neg_of_add_eq_zero_left he.symm

def traceDerivative {ι : Type uι} (h : ι → CF (FreeGroup ι)) (g : FreeGroup ι) : ℂ :=
  cocycle h g g⁻¹

theorem traceDerivative_conjugate {ι : Type uι} (h : ι → CF (FreeGroup ι))
    (a g : FreeGroup ι) :
    traceDerivative h (a * g * a⁻¹) = traceDerivative h g := by
  simp only [traceDerivative, cocycle_mul, cocycle_inv, shift_apply,
    Finsupp.add_apply, Finsupp.neg_apply, mul_inv_rev, inv_inv]
  simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  ring

def CyclicConjugate {G : Type uG} [Group G] (c b : G) : Prop :=
  ∃ (a : G) (k : ℤ), b = a * c ^ k * a⁻¹

theorem CyclicConjugate.conj {G : Type uG} [Group G] {c b : G}
    (hb : CyclicConjugate c b) (g : G) : CyclicConjugate c (g * b * g⁻¹) := by
  obtain ⟨a, k, rfl⟩ := hb
  exact ⟨g * a, k, by simp [mul_assoc]⟩

theorem CyclicConjugate.inv {G : Type uG} [Group G] {c b : G}
    (hb : CyclicConjugate c b) : CyclicConjugate c b⁻¹ := by
  obtain ⟨a, k, rfl⟩ := hb
  exact ⟨a, -k, by simp [mul_assoc]⟩

def SupportedOn {G : Type uG} (P : G → Prop) (p : CF G) : Prop :=
  ∀ b, ¬P b → p b = 0

@[simp] theorem supported_zero {G : Type uG} (P : G → Prop) : SupportedOn P (0 : CF G) := by
  intro b hb
  rfl

theorem supported_add {G : Type uG} {P : G → Prop} {p q : CF G}
    (hp : SupportedOn P p) (hq : SupportedOn P q) : SupportedOn P (p + q) := by
  intro b hb
  simp [hp b hb, hq b hb]

theorem supported_neg {G : Type uG} {P : G → Prop} {p : CF G}
    (hp : SupportedOn P p) : SupportedOn P (-p) := by
  intro b hb
  simp [hp b hb]

theorem supported_shift {G : Type uG} [Group G] {c : G} {p : CF G}
    (hp : SupportedOn (CyclicConjugate c) p) (g : G) :
    SupportedOn (CyclicConjugate c) (shift g p) := by
  intro b hb
  apply hp
  intro h
  have := h.conj g
  apply hb
  simpa [mul_assoc] using this

end TraceCocycle
end FreeGroupFactorMain

namespace FreeGroupFactorMain.TraceCocycle

 theorem cocycle_supported {ι : Type uι} (h : ι → CF (FreeGroup ι)) (c : FreeGroup ι)
    (hh : ∀ i, SupportedOn (CyclicConjugate c) (h i)) (g : FreeGroup ι) :
    SupportedOn (CyclicConjugate c) (cocycle h g) := by
  induction g using FreeGroup.induction_on with
  | C1 => simp
  | of i => simpa using hh i
  | inv_of g hg => rw [cocycle_inv]; exact supported_neg (supported_shift hg _)
  | mul g b hg hb => rw [cocycle_mul]; exact supported_add hg (supported_shift hb _)

 theorem cocycle_pow_zero {ι : Type uι} (h : ι → CF (FreeGroup ι)) (c : FreeGroup ι)
    (hc : cocycle h c = 0) (k : ℕ) : cocycle h (c ^ k) = 0 := by
  induction k with
  | zero => simp
  | succ k ih => simp [pow_succ, cocycle_mul, ih, hc]

 theorem cocycle_zpow_zero {ι : Type uι} (h : ι → CF (FreeGroup ι)) (c : FreeGroup ι)
    (hc : cocycle h c = 0) (k : ℤ) : cocycle h (c ^ k) = 0 := by
  cases k with
  | ofNat k => simpa using cocycle_pow_zero h c hc k
  | negSucc k => simp [zpow_negSucc, cocycle_inv, cocycle_pow_zero h c hc]

 theorem universalGroupTraceIdentity {ι : Type uι} (h : ι → CF (FreeGroup ι)) (c : ι)
    (hh : ∀ i, SupportedOn (CyclicConjugate (FreeGroup.of c)) (h i))
    (hc : h c = 0) (g : FreeGroup ι) : traceDerivative h g = 0 := by
  classical
  by_cases hg : CyclicConjugate (FreeGroup.of c) g
  · obtain ⟨a, k, rfl⟩ := hg
    rw [traceDerivative_conjugate, traceDerivative,
      cocycle_zpow_zero h _ (by simpa using hc)]
    rfl
  · apply cocycle_supported h (FreeGroup.of c) hh g
    intro hginv
    exact hg (by simpa using hginv.inv)

def rightShift {G : Type uG} [Group G] (g : G) : CF G ≃ₗ[ℂ] CF G :=
  Finsupp.domLCongr (Equiv.mulRight g)

@[simp] theorem rightShift_apply {G : Type uG} [Group G] (g : G) (p : CF G) (b : G) :
    rightShift g p b = p (b * g⁻¹) := rfl

def polynomialDerivative {ι : Type uι} (h : ι → CF (FreeGroup ι)) :
    CF (FreeGroup ι) →ₗ[ℂ] CF (FreeGroup ι) :=
  Finsupp.linearCombination ℂ (fun g => rightShift g (cocycle h g))

@[simp] theorem polynomialDerivative_single {ι : Type uι} (h : ι → CF (FreeGroup ι))
    (g : FreeGroup ι) (a : ℂ) :
    polynomialDerivative h (Finsupp.single g a) = a • rightShift g (cocycle h g) := by
  simp [polynomialDerivative]

 theorem polynomialDerivative_trace_zero {ι : Type uι} (h : ι → CF (FreeGroup ι)) (c : ι)
    (hh : ∀ i, SupportedOn (CyclicConjugate (FreeGroup.of c)) (h i))
    (hc : h c = 0) (p : CF (FreeGroup ι)) : (polynomialDerivative h p) 1 = 0 := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp [map_add, hp, hq]
  | single g a =>
    simp only [polynomialDerivative_single, Finsupp.smul_apply, smul_eq_mul,
      rightShift_apply, one_mul]
    change a * traceDerivative h g = 0
    rw [universalGroupTraceIdentity h c hh hc, mul_zero]

def algebraDerivative {ι : Type uι} (h : ι → CF (FreeGroup ι)) :
    MonoidAlgebra ℂ (FreeGroup ι) →ₗ[ℂ] MonoidAlgebra ℂ (FreeGroup ι) :=
  (MonoidAlgebra.coeffLinearEquiv ℂ).symm.toLinearMap ∘ₗ
    polynomialDerivative h ∘ₗ (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

@[simp] theorem algebraDerivative_coeff {ι : Type uι} (h : ι → CF (FreeGroup ι))
    (p : MonoidAlgebra ℂ (FreeGroup ι)) :
    (algebraDerivative h p).coeff = polynomialDerivative h p.coeff := rfl

@[simp] theorem algebraDerivative_of_coeff {ι : Type uι} (h : ι → CF (FreeGroup ι))
    (g : FreeGroup ι) (b : FreeGroup ι) :
    (algebraDerivative h (MonoidAlgebra.of ℂ (FreeGroup ι) g)).coeff b =
      cocycle h g (b * g⁻¹) := by
  simp [MonoidAlgebra.of_apply]

theorem algebraDerivative_mul_of {ι : Type uι} (h : ι → CF (FreeGroup ι))
    (g b : FreeGroup ι) :
    algebraDerivative h (MonoidAlgebra.of ℂ (FreeGroup ι) g *
      MonoidAlgebra.of ℂ (FreeGroup ι) b) =
      algebraDerivative h (MonoidAlgebra.of ℂ (FreeGroup ι) g) *
        MonoidAlgebra.of ℂ (FreeGroup ι) b +
      MonoidAlgebra.of ℂ (FreeGroup ι) g *
        algebraDerivative h (MonoidAlgebra.of ℂ (FreeGroup ι) b) := by
  rw [← map_mul]
  ext x
  simp [MonoidAlgebra.of_apply, cocycle_mul, mul_assoc]

theorem algebraDerivative_mul {ι : Type uι} (h : ι → CF (FreeGroup ι))
    (p q : MonoidAlgebra ℂ (FreeGroup ι)) :
    algebraDerivative h (p * q) = algebraDerivative h p * q + p * algebraDerivative h q := by
  induction p using MonoidAlgebra.induction_on with
  | of g =>
    induction q using MonoidAlgebra.induction_on with
    | of b => exact algebraDerivative_mul_of h g b
    | add q₁ q₂ ih₁ ih₂ => simp only [mul_add, map_add, ih₁, ih₂]; abel
    | smul r q ih => simp only [mul_smul_comm, map_smul, ih, smul_add]
  | add p₁ p₂ ih₁ ih₂ => simp only [add_mul, map_add, ih₁, ih₂]; abel
  | smul r p ih => simp only [smul_mul_assoc, map_smul, ih, smul_add]

def laurent {G : Type uG} [Group G] (c : G) (l : ℤ →₀ ℂ) : CF G :=
  Finsupp.linearCombination ℂ (fun k => Finsupp.single (c ^ k) 1) l

theorem supported_smul {G : Type uG} {P : G → Prop} {p : CF G}
    (hp : SupportedOn P p) (a : ℂ) : SupportedOn P (a • p) := by
  intro b hb
  simp [hp b hb]

theorem laurent_supported {G : Type uG} [Group G] (c : G) (l : ℤ →₀ ℂ) :
    SupportedOn (CyclicConjugate c) (laurent c l) := by
  classical
  induction l using Finsupp.induction_linear with
  | zero => simp [laurent]
  | add p q hp hq => simpa only [laurent, map_add] using supported_add hp hq
  | single k a =>
    simp only [laurent, Finsupp.linearCombination_single]
    apply supported_smul
    intro b hb
    apply Finsupp.single_eq_of_ne
    intro heq
    apply hb
    exact ⟨1, k, by simpa using heq⟩

def fieldCoefficients {ι : Type uι} (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ) :
    Option ι → CF (FreeGroup (Option ι))
  | none => 0
  | some i => (h i).sum fun g a => ((a : ℂ) * Complex.I) •
      shift (FreeGroup.map Option.some g) (laurent (FreeGroup.of none) l)

theorem fieldCoefficients_supported {ι : Type uι} (h : ι → FreeGroup ι →₀ ℝ)
    (l : ℤ →₀ ℂ) (i : Option ι) :
    SupportedOn (CyclicConjugate (FreeGroup.of none)) (fieldCoefficients h l i) := by
  classical
  cases i with
  | none => exact supported_zero _
  | some i =>
    intro b hb
    simp only [fieldCoefficients, Finsupp.sum, Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro g hg
    exact supported_smul (supported_shift (laurent_supported _ _) _) _ b hb

theorem sourceLaurentTraceIdentity {ι : Type uι} (h : ι → FreeGroup ι →₀ ℝ)
    (l : ℤ →₀ ℂ) (p : MonoidAlgebra ℂ (FreeGroup (Option ι))) (r : ℕ) :
    ((algebraDerivative (fieldCoefficients h l))^[r + 1] p).coeff 1 = 0 := by
  rw [Function.iterate_succ_apply', algebraDerivative_coeff]
  exact polynomialDerivative_trace_zero _ none (fieldCoefficients_supported h l) rfl _

end FreeGroupFactorMain.TraceCocycle

namespace FreeGroupFactorMain
namespace AlgebraPolynomial
open NCPolynomial

def signed {ι : Type uι} (ib : ι × Bool) : FreeGroup ι :=
  if ib.2 then FreeGroup.of ib.1 else (FreeGroup.of ib.1)⁻¹

def wordExpr {ι : Type uι} : List (ι × Bool) → Expr (ι × Bool)
  | [] => .scalar 1
  | a :: w => .mul (.gen a) (wordExpr w)

theorem eval_wordExpr {ι : Type uι} {A : Type uA} [Semiring A] [Algebra ℂ A]
    (ρ : FreeGroup ι →* A) (w : List (ι × Bool)) :
    eval (fun ib => ρ (signed ib)) (wordExpr w) = ρ (FreeGroup.mk w) := by
  induction w with
  | nil => simp [wordExpr, eval, ← FreeGroup.one_eq_mk]
  | cons a w ih =>
    rcases a with ⟨i, b⟩
    change ρ (signed (i, b)) * eval (fun ib => ρ (signed ib)) (wordExpr w) = _
    rw [ih, ← map_mul]
    cases b <;> rfl

def groupExpr {ι : Type uι} [DecidableEq ι] (g : FreeGroup ι) : Expr (ι × Bool) :=
  wordExpr g.toWord

theorem eval_groupExpr {ι : Type uι} {A : Type uA} [DecidableEq ι] [Semiring A] [Algebra ℂ A]
    (ρ : FreeGroup ι →* A) (g : FreeGroup ι) :
    eval (fun ib => ρ (signed ib)) (groupExpr g) = ρ g := by
  rw [groupExpr, eval_wordExpr, FreeGroup.mk_toWord]

def sumExpr {ι : Type uι} : List (Expr ι) → Expr ι
  | [] => .scalar 0
  | p :: ps => .add p (sumExpr ps)

theorem eval_sumExpr {ι : Type uι} {A : Type uA} [Semiring A] [Algebra ℂ A]
    (X : ι → A) (ps : List (Expr ι)) :
    eval X (sumExpr ps) = (ps.map (eval X)).sum := by
  induction ps with
  | nil => simp [sumExpr, eval]
  | cons p ps ih => simp [sumExpr, eval, ih]

def encode {ι : Type uι} [DecidableEq ι] (p : MonoidAlgebra ℂ (FreeGroup ι)) :
    Expr (ι × Bool) :=
  sumExpr (p.coeff.support.toList.map fun g => .mul (.scalar (p.coeff g)) (groupExpr g))

theorem eval_encode {ι : Type uι} [DecidableEq ι] (p : MonoidAlgebra ℂ (FreeGroup ι)) :
    eval (fun ib => MonoidAlgebra.of ℂ (FreeGroup ι) (signed ib)) (encode p) = p := by
  classical
  rw [encode, eval_sumExpr, List.map_map]
  simp only [Function.comp_def, eval]
  simp_rw [eval_groupExpr]
  simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
    MonoidAlgebra.of_apply, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
  rw [Finset.sum_map_toList]
  simpa only [Finsupp.sum] using (MonoidAlgebra.sum_coeff_single p)

def encodedField {ι : Type uι} [DecidableEq ι]
    (h : ι → TraceCocycle.CF (FreeGroup ι)) (ib : ι × Bool) : Expr (ι × Bool) :=
  encode (TraceCocycle.algebraDerivative h (MonoidAlgebra.of ℂ (FreeGroup ι) (signed ib)))

theorem algebraDerivative_one {ι : Type uι} (h : ι → TraceCocycle.CF (FreeGroup ι)) :
    TraceCocycle.algebraDerivative h 1 = 0 := by
  have he := TraceCocycle.algebraDerivative_mul h 1 1
  simp only [one_mul, mul_one] at he
  exact (add_eq_left.mp he.symm)

theorem eval_delta_encoded {ι : Type uι} [DecidableEq ι]
    (h : ι → TraceCocycle.CF (FreeGroup ι)) (p : Expr (ι × Bool)) :
    eval (fun ib => MonoidAlgebra.of ℂ (FreeGroup ι) (signed ib))
      (delta (encodedField h) p) =
    TraceCocycle.algebraDerivative h
      (eval (fun ib => MonoidAlgebra.of ℂ (FreeGroup ι) (signed ib)) p) := by
  induction p with
  | scalar c =>
    simp only [delta, eval, Algebra.algebraMap_eq_smul_one, map_smul,
      algebraDerivative_one, smul_zero, zero_smul]
  | gen ib => exact eval_encode _
  | add p q hp hq => simp only [delta, eval, hp, hq, map_add]
  | mul p q hp hq => simp only [delta, eval, hp, hq, TraceCocycle.algebraDerivative_mul]

theorem map_eval {ι : Type uι} {A : Type uA} {B : Type uB} [Semiring A] [Semiring B]
    [Algebra ℂ A] [Algebra ℂ B] (φ : A →ₐ[ℂ] B) (X : ι → A) (p : Expr ι) :
    φ (eval X p) = eval (fun i => φ (X i)) p := by
  induction p with
  | scalar c => exact φ.commutes c
  | gen i => rfl
  | add p q hp hq => simp only [eval, map_add, hp, hq]
  | mul p q hp hq => simp only [eval, map_mul, hp, hq]

theorem encoded_initial_trace {ι : Type uι} [DecidableEq ι]
    (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ) (p : Expr ((Option ι) × Bool)) :
    (eval (fun ib => MonoidAlgebra.of ℂ (FreeGroup (Option ι)) (signed ib))
      (delta (encodedField (TraceCocycle.fieldCoefficients h l)) p)).coeff 1 = 0 := by
  rw [eval_delta_encoded]
  exact TraceCocycle.sourceLaurentTraceIdentity h l _ 0

end AlgebraPolynomial
end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

noncomputable section

universe uA uG uι

open Set Metric
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain
namespace UnitaryEvaluation
variable {A : Type uA} [CStarAlgebra A]
variable {ι : Type uι}

theorem wordHom_word [DecidableEq ι]
    (U : ι → unitary A) (g : FreeGroup ι) :
    wordHom U g = PolynomialFlow.word g (fun i => (U i : A)) := by
  conv_lhs => rw [← FreeGroup.mk_toWord (x := g)]
  change ((FreeGroup.lift U (FreeGroup.mk g.toWord) : unitary A) : A) = _
  rw [FreeGroup.lift_mk]
  rw [Submonoid.coe_list_prod]
  simp only [List.map_map, Function.comp_def]
  unfold PolynomialFlow.word PolynomialFlow.wordList
  apply congrArg List.prod
  apply List.map_congr_left
  intro ib _
  rcases ib with ⟨i, b⟩
  cases b <;> rfl

def algebraHom (U : ι → unitary A) : MonoidAlgebra ℂ (FreeGroup ι) →ₐ[ℂ] A :=
  MonoidAlgebra.lift ℂ A (FreeGroup ι) (wordHom U)

@[simp] theorem algebraHom_of (U : ι → unitary A) (g : FreeGroup ι) :
    algebraHom U (MonoidAlgebra.of ℂ (FreeGroup ι) g) = wordHom U g := by
  simp [algebraHom]

@[simp] theorem eval_encode [DecidableEq ι]
    (U : ι → unitary A) (p : MonoidAlgebra ℂ (FreeGroup ι)) :
    NCPolynomial.eval (fun ib => wordHom U (AlgebraPolynomial.signed ib))
      (AlgebraPolynomial.encode p) = algebraHom U p := by
  calc
    _ = algebraHom U (NCPolynomial.eval
        (fun ib => MonoidAlgebra.of ℂ (FreeGroup ι) (AlgebraPolynomial.signed ib))
        (AlgebraPolynomial.encode p)) := by
      rw [AlgebraPolynomial.map_eval]
      congr 1
      funext ib
      exact (algebraHom_of U _).symm
    _ = algebraHom U p := by rw [AlgebraPolynomial.eval_encode]

theorem algebraHom_ofCoeff (U : ι → unitary A) (p : FreeGroup ι →₀ ℂ) :
    algebraHom U (MonoidAlgebra.ofCoeff p) = coefficientHom (wordHom U) p := by
  simp [algebraHom, MonoidAlgebra.lift_apply, coefficientHom, Finsupp.linearCombination_apply]

theorem coefficientHom_shift {G : Type uG} [Group G] (ρ : G →* A)
    (g : G) (p : G →₀ ℂ) :
    coefficientHom ρ (TraceCocycle.shift g p) =
      ρ g * coefficientHom ρ p * ρ g⁻¹ := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp [map_add, hp, hq, mul_add, add_mul]
  | single b c =>
    have hs : TraceCocycle.shift g (Finsupp.single b c) =
        Finsupp.single (g * b * g⁻¹) c := by
      simp only [TraceCocycle.shift, Finsupp.domCongr_apply,
        Finsupp.equivMapDomain_eq_mapDomain, Finsupp.mapDomain_single]
      rfl
    rw [hs, coefficientHom_single, coefficientHom_single]
    simp only [map_mul, smul_mul_assoc, mul_smul_comm]

theorem derivative_of (h : ι → TraceCocycle.CF (FreeGroup ι)) (g : FreeGroup ι) :
    TraceCocycle.algebraDerivative h (MonoidAlgebra.of ℂ (FreeGroup ι) g) =
      MonoidAlgebra.ofCoeff (TraceCocycle.cocycle h g) *
        MonoidAlgebra.of ℂ (FreeGroup ι) g := by
  ext b
  simp [MonoidAlgebra.of_apply]

theorem eval_derivative_of (U : ι → unitary A)
    (h : ι → TraceCocycle.CF (FreeGroup ι)) (g : FreeGroup ι) :
    algebraHom U (TraceCocycle.algebraDerivative h (MonoidAlgebra.of ℂ (FreeGroup ι) g)) =
      coefficientHom (wordHom U) (TraceCocycle.cocycle h g) * wordHom U g := by
  rw [derivative_of, map_mul, algebraHom_ofCoeff, algebraHom_of]

theorem eval_encodedField_pos [DecidableEq ι] (U : ι → unitary A)
    (h : ι → TraceCocycle.CF (FreeGroup ι)) (i : ι) :
    NCPolynomial.eval (fun ib => wordHom U (AlgebraPolynomial.signed ib))
      (AlgebraPolynomial.encodedField h (i, true)) =
      coefficientHom (wordHom U) (h i) * (U i : A) := by
  rw [AlgebraPolynomial.encodedField, eval_encode, eval_derivative_of]
  simp only [AlgebraPolynomial.signed, ↓reduceIte, TraceCocycle.cocycle_of, wordHom_of]

theorem eval_encodedField_neg [DecidableEq ι] (U : ι → unitary A)
    (h : ι → TraceCocycle.CF (FreeGroup ι)) (i : ι) :
    NCPolynomial.eval (fun ib => wordHom U (AlgebraPolynomial.signed ib))
      (AlgebraPolynomial.encodedField h (i, false)) =
      -(star (U i : A) * coefficientHom (wordHom U) (h i)) := by
  rw [AlgebraPolynomial.encodedField, eval_encode, eval_derivative_of]
  simp only [AlgebraPolynomial.signed, Bool.false_eq_true, ↓reduceIte,
    TraceCocycle.cocycle_inv, TraceCocycle.cocycle_of, map_neg, coefficientHom_shift,
    wordHom_inv, inv_inv, wordHom_of, neg_mul]
  rw [mul_assoc, mul_assoc, (U i).property.2, mul_one]

end UnitaryEvaluation
end FreeGroupFactorMain

namespace FreeGroupFactorMain.UnitaryEvaluation
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι}

@[simp] theorem coefficientHom_laurent (U : ι → unitary A) (C : unitary A) (l : ℤ →₀ ℂ) :
    coefficientHom (wordHom (extendUnitary U C))
      (TraceCocycle.laurent (FreeGroup.of none) l) = laurentValue C l := by
  induction l using Finsupp.induction_linear with
  | zero => simp [TraceCocycle.laurent, laurentValue]
  | add p q hp hq => simpa [TraceCocycle.laurent, laurentValue, map_add] using congrArg₂ (· + ·) hp hq
  | single k c =>
    simp only [TraceCocycle.laurent, Finsupp.linearCombination_single, map_smul,
      coefficientHom_single, one_smul, laurentValue]
    congr 1
    change ((FreeGroup.lift (extendUnitary U C) (FreeGroup.of none ^ k) : unitary A) : A) = _
    rw [map_zpow, FreeGroup.lift_apply_of]
    rfl

 theorem coefficientHom_fieldCoefficients [DecidableEq ι]
    (U : ι → unitary A) (C : unitary A) (h : ι → FreeGroup ι →₀ ℝ)
    (l : ℤ →₀ ℂ) (i : ι) :
    coefficientHom (wordHom (extendUnitary U C)) (TraceCocycle.fieldCoefficients h l (some i)) =
      Complex.I • PolynomialFlow.hamiltonian (laurentValue C l) (h i) (fun j => (U j : A)) := by
  classical
  simp only [TraceCocycle.fieldCoefficients, PolynomialFlow.hamiltonian, Finsupp.sum,
    map_sum, map_smul, coefficientHom_shift, coefficientHom_laurent,
    wordHom_inv, wordHom_extend, Finset.smul_sum]
  simp only [wordHom_word]
  apply Finset.sum_congr rfl
  intro g hg
  rw [smul_smul, mul_comm]

def signedTrajectory (X : ℝ → ι → A) (hU : ∀ t j, X t j ∈ unitary A)
    (C : unitary A) (t : ℝ) (ib : Option ι × Bool) : A :=
  wordHom (extendUnitary (fun j => ⟨X t j, hU t j⟩) C) (AlgebraPolynomial.signed ib)

 theorem signedTrajectory_some_pos (X : ℝ → ι → A) (hU : ∀ t j, X t j ∈ unitary A)
    (C : unitary A) (t : ℝ) (i : ι) :
    signedTrajectory X hU C t (some i, true) = X t i := by
  simp [signedTrajectory, AlgebraPolynomial.signed, extendUnitary]

 theorem signedTrajectory_some_neg (X : ℝ → ι → A) (hU : ∀ t j, X t j ∈ unitary A)
    (C : unitary A) (t : ℝ) (i : ι) :
    signedTrajectory X hU C t (some i, false) = star (X t i) := by
  simp [signedTrajectory, AlgebraPolynomial.signed, extendUnitary]

 theorem signedTrajectory_none_pos (X : ℝ → ι → A) (hU : ∀ t j, X t j ∈ unitary A)
    (C : unitary A) (t : ℝ) :
    signedTrajectory X hU C t (none, true) = C := by
  simp [signedTrajectory, AlgebraPolynomial.signed, extendUnitary]

 theorem signedTrajectory_none_neg (X : ℝ → ι → A) (hU : ∀ t j, X t j ∈ unitary A)
    (C : unitary A) (t : ℝ) :
    signedTrajectory X hU C t (none, false) = star (C : A) := by
  simp [signedTrajectory, AlgebraPolynomial.signed, extendUnitary]

end FreeGroupFactorMain.UnitaryEvaluation

end

end OAI
end

section
namespace OAI

noncomputable section

universe uA uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

open scoped Topology ContDiff
open Set Filter
namespace FreeGroupFactorMain

theorem flat_local_of_factorial_bound (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (B c : ℝ) (_hB : 0 ≤ B) (hc : 0 < c)
    (hbound : ∀ r t, |iteratedDeriv r f t| ≤ B * c ^ r * (r.factorial : ℝ))
    (a : ℝ) (ha : ∀ r, iteratedDeriv (r + 1) f a = 0)
    (x : ℝ) (hx : c * |x - a| < 1) : f x = f a := by
  by_cases hax : a = x
  · simp [hax]
  have htaylor (n : ℕ) : taylorWithinEval f n (uIcc a x) a x = f a := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [taylorWithinEval_succ, ih,
        iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hax)
          ((hf.of_le (by exact_mod_cast (le_top : ((n + 1 : ℕ) : ℕ∞) ≤ ⊤))).contDiffAt)
          (left_mem_uIcc), ha n]
      simp
  have hest (n : ℕ) : |f x - f a| ≤ B * (c * |x - a|) ^ (n + 1) := by
    obtain ⟨y, _, hy⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hax
      ((hf.of_le (by exact_mod_cast (le_top : ((n + 1 : ℕ) : ℕ∞) ≤ ⊤))).contDiffOn)
    rw [htaylor] at hy
    have hfpos : (0 : ℝ) < ((n + 1).factorial : ℝ) := by positivity
    calc
      |f x - f a| = |iteratedDeriv (n + 1) f y| * |x - a| ^ (n + 1) /
          ((n + 1).factorial : ℝ) := by rw [hy, abs_div, abs_mul, abs_pow, abs_of_pos hfpos]
      _ ≤ (B * c ^ (n + 1) * ((n + 1).factorial : ℝ)) * |x - a| ^ (n + 1) /
          ((n + 1).factorial : ℝ) := by gcongr; exact hbound _ _
      _ = B * (c * |x - a|) ^ (n + 1) := by rw [mul_pow]; field_simp
  have hlim : Tendsto (fun n : ℕ => B * (c * |x - a|) ^ (n + 1)) atTop (nhds 0) := by
    have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one (mul_nonneg hc.le (abs_nonneg _)) hx)
    simpa using (hp.comp (tendsto_add_atTop_nat 1)).const_mul B
  have hz : |f x - f a| ≤ 0 := ge_of_tendsto hlim (Eventually.of_forall hest)
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hz)

theorem flat_global_of_factorial_bound (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (B c : ℝ) (hB : 0 ≤ B) (hc : 0 < c)
    (hbound : ∀ r t, |iteratedDeriv r f t| ≤ B * c ^ r * (r.factorial : ℝ))
    (ha : ∀ r, iteratedDeriv (r + 1) f 0 = 0) (x : ℝ) : f x = f 0 := by
  let Z : Set ℝ := {a | ∀ r, iteratedDeriv (r + 1) f a = 0}
  have hclosed : IsClosed Z := by
    change IsClosed {a | ∀ r, iteratedDeriv (r + 1) f a = 0}
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro r
    exact isClosed_eq (hf.continuous_iteratedDeriv (r + 1) (by exact_mod_cast (le_top : ((r + 1 : ℕ) : ℕ∞) ≤ ⊤))) continuous_const
  have hopen : IsOpen Z := by
    apply isOpen_iff_mem_nhds.mpr
    intro a ha
    have hδ : 0 < c⁻¹ := inv_pos.mpr hc
    apply Filter.mem_of_superset (Metric.ball_mem_nhds a hδ)
    intro y hy
    have heq : f =ᶠ[nhds y] (fun _ => f a) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hy] with z hz
      apply flat_local_of_factorial_bound f hf B c hB hc hbound a ha z
      rw [Metric.mem_ball, Real.dist_eq] at hz
      have := mul_lt_mul_of_pos_left hz hc
      simpa [ne_of_gt hc] using this
    intro r
    rw [heq.iteratedDeriv_eq (r + 1)]
    simp [iteratedDeriv_const]
  have hall : Z = univ := (show IsClopen Z from ⟨hclosed, hopen⟩).eq_univ ⟨0, ha⟩
  have hderiv (a : ℝ) : deriv f a = 0 := by
    have hz : a ∈ Z := hall ▸ mem_univ a
    simpa using hz 0
  exact isOpen_univ.is_const_of_deriv_eq_zero isPreconnected_univ
    (fun a _ => ((hf.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).differentiable (by simp)).differentiableOn a (mem_univ a))
    (fun a _ => hderiv a) (mem_univ x) (mem_univ 0)

namespace NCPolynomial

theorem iteratedDeriv_moment {ι : Type uι} {A : Type uA} [NormedRing A] [NormedAlgebra ℂ A]
    (X : ℝ → ι → A) (V : ι → Expr ι) (L : A →L[ℝ] ℝ)
    (hX : ∀ t i, HasDerivAt (fun s => X s i) (eval (X t) (V i)) t)
    (p : Expr ι) (r : ℕ) :
    iteratedDeriv r (fun t => L (eval (X t) p)) =
      fun t => L (eval (X t) ((delta V)^[r] p)) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    rw [Function.iterate_succ_apply']
    convert! (L.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_eval X V t (hX t) ((delta V)^[r] p))).deriv using 1

theorem polynomial_moments {ι : Type uι} {A : Type uA} [NormedRing A] [NormedAlgebra ℂ A]
    [NormOneClass A] (X : ℝ → ι → A) (V : ι → Expr ι) (L : A →L[ℝ] ℝ)
    (hsmooth : ∀ i, ContDiff ℝ ∞ (fun t => X t i))
    (hX : ∀ t i, HasDerivAt (fun s => X s i) (eval (X t) (V i)) t)
    (R : ℝ) (hR : 1 ≤ R) (hbounded : ∀ t i, ‖X t i‖ ≤ R)
    (J : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hdeg : ∀ i, degree (V i) ≤ J + 1) (hmass : ∀ i, mass (V i) ≤ B)
    (htrace : ∀ p, L (eval (X 0) (delta V p)) = 0)
    (p : Expr ι) (t : ℝ) : L (eval (X t) p) = L (eval (X 0) p) := by
  let b := ‖L‖ * (mass p * R ^ degree p)
  let c := B * ((degree p : ℝ) + J) * R ^ J + 1
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  have hbase : 0 ≤ B * ((degree p : ℝ) + J) * R ^ J := by positivity
  have hb : 0 ≤ b := mul_nonneg (norm_nonneg _) (mul_nonneg (mass_nonneg _) (pow_nonneg hR0 _))
  have hc : 0 < c := by dsimp [c]; linarith
  apply flat_global_of_factorial_bound (fun t => L (eval (X t) p)) (L.contDiff.comp (smooth_eval X hsmooth p)) b c hb hc
  · intro r u
    rw [iteratedDeriv_moment X V L hX]
    calc
      |L (eval (X u) ((delta V)^[r] p))| ≤ ‖L‖ * ‖eval (X u) ((delta V)^[r] p)‖ :=
        L.le_opNorm _
      _ ≤ ‖L‖ * ((mass p * R ^ degree p) *
          (B * ((degree p : ℝ) + J) * R ^ J) ^ r * (r.factorial : ℝ)) := by
        gcongr
        exact norm_eval_iterate (X u) R hR (hbounded u) V J B hB hdeg hmass p r
      _ ≤ b * c ^ r * (r.factorial : ℝ) := by
        dsimp [b]
        calc
          _ = (‖L‖ * (mass p * R ^ degree p)) *
              (B * ((degree p : ℝ) + J) * R ^ J) ^ r * (r.factorial : ℝ) := by ring
          _ ≤ _ := by
            gcongr
            dsimp [c]; linarith
  · intro r
    rw [iteratedDeriv_moment X V L hX, Function.iterate_succ_apply']
    exact htrace _

end NCPolynomial
end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

noncomputable section

universe uG uH

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain

open scoped ENNReal

theorem canonicalTrace_eq_inner {G : Type uG} [Group G] [DecidableEq G]
    (T : groupVonNeumann G) :
    canonicalTrace T = inner ℂ (lp.single 2 (1 : G) (1 : ℂ))
      ((T : GroupOperator G) (lp.single 2 (1 : G) (1 : ℂ))) := by
  classical
  simp only [canonicalTrace, lp.inner_single_left, RCLike.inner_apply, map_one, mul_one]
  apply congrArg (fun v : GroupHilbert G => ((T : GroupOperator G) v) 1)
  ext b
  simp [lp.single_apply, Pi.single_apply]

def canonicalTraceLinear {G : Type uG} [Group G] : groupVonNeumann G →ₗ[ℂ] ℂ where
  toFun := canonicalTrace
  map_add' T U := by simp [canonicalTrace]
  map_smul' c T := by simp [canonicalTrace]

theorem norm_canonicalTrace_le {G : Type uG} [Group G] (T : groupVonNeumann G) :
    ‖canonicalTrace T‖ ≤ ‖T‖ := by
  classical
  rw [canonicalTrace_eq_inner]
  calc
    ‖inner ℂ (lp.single 2 (1 : G) (1 : ℂ))
        ((T : GroupOperator G) (lp.single 2 (1 : G) (1 : ℂ)))‖ ≤
        ‖lp.single (E := fun _ : G => ℂ) 2 (1 : G) (1 : ℂ)‖ *
        ‖(T : GroupOperator G) (lp.single 2 (1 : G) (1 : ℂ))‖ := norm_inner_le_norm _ _
    _ ≤ ‖lp.single (E := fun _ : G => ℂ) 2 (1 : G) (1 : ℂ)‖ *
        (‖(T : GroupOperator G)‖ * ‖lp.single (E := fun _ : G => ℂ) 2 (1 : G) (1 : ℂ)‖) := by
      gcongr
      exact (T : GroupOperator G).le_opNorm _
    _ = ‖T‖ := by simp

def canonicalTraceCLM {G : Type uG} [Group G] : groupVonNeumann G →L[ℂ] ℂ :=
  canonicalTraceLinear.mkContinuous 1 (fun T => by
    change ‖canonicalTrace T‖ ≤ 1 * ‖T‖
    simpa only [one_mul] using norm_canonicalTrace_le T)

@[simp] theorem canonicalTraceCLM_apply {G : Type uG} [Group G] (T : groupVonNeumann G) :
    canonicalTraceCLM T = canonicalTrace T := rfl

end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

noncomputable section

universe uA uG uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain

 def groupUnitaryHom (G : Type uG) [Group G] : G →* groupVonNeumann G where
  toFun := groupUnitary
  map_one' := Subtype.ext (leftRegular_one)
  map_mul' g b := Subtype.ext (leftRegular_mul g b)

 def groupAlgebraEvaluation (G : Type uG) [Group G] :
    MonoidAlgebra ℂ G →ₐ[ℂ] groupVonNeumann G :=
  MonoidAlgebra.lift ℂ (groupVonNeumann G) G (groupUnitaryHom G)

 @[simp] theorem groupAlgebraEvaluation_of {G : Type uG} [Group G] (g : G) :
    groupAlgebraEvaluation G (MonoidAlgebra.of ℂ G g) = groupUnitary g := by
  simp [groupAlgebraEvaluation, groupUnitaryHom]

 theorem canonicalTrace_groupAlgebraEvaluation {G : Type uG} [Group G] [DecidableEq G]
    (p : MonoidAlgebra ℂ G) : canonicalTrace (groupAlgebraEvaluation G p) = p.coeff 1 := by
  induction p using MonoidAlgebra.induction_on with
  | of g =>
    rw [groupAlgebraEvaluation_of, canonicalTrace_groupUnitary]
    simp only [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  | add p q hp hq =>
    change canonicalTraceCLM (groupAlgebraEvaluation G (p + q)) = _
    simp only [map_add, canonicalTraceCLM_apply, hp, hq, MonoidAlgebra.coeff_add,
      Finsupp.add_apply]
  | smul c p hp =>
    change canonicalTraceCLM (groupAlgebraEvaluation G (c • p)) = _
    simp only [map_smul, canonicalTraceCLM_apply, hp, MonoidAlgebra.coeff_smul,
      Finsupp.smul_apply]

 theorem canonicalTrace_eval {ι : Type uι} [DecidableEq ι]
    (p : NCPolynomial.Expr (ι × Bool)) :
    canonicalTrace (NCPolynomial.eval (fun ib => groupUnitary (AlgebraPolynomial.signed ib)) p) =
      (NCPolynomial.eval (fun ib => MonoidAlgebra.of ℂ (FreeGroup ι)
        (AlgebraPolynomial.signed ib)) p).coeff 1 := by
  rw [← canonicalTrace_groupAlgebraEvaluation]
  congr 1
  rw [AlgebraPolynomial.map_eval]
  congr 1
  funext ib
  exact (groupAlgebraEvaluation_of _).symm

end FreeGroupFactorMain

namespace FreeGroupFactorMain.UnitaryEvaluation
open scoped ContDiff
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι}
 theorem norm_signedTrajectory_le_one [Nontrivial A]
    (X : ℝ → ι → A) (hU : ∀ t j, X t j ∈ unitary A)
    (C : unitary A) (t : ℝ) (ib : Option ι × Bool) :
    ‖signedTrajectory X hU C t ib‖ ≤ 1 := by
  change ‖((FreeGroup.lift (extendUnitary (fun j => ⟨X t j, hU t j⟩) C)
    (AlgebraPolynomial.signed ib) : unitary A) : A)‖ ≤ 1
  exact (CStarRing.norm_of_mem_unitary (Subtype.property _)).le

end FreeGroupFactorMain.UnitaryEvaluation

namespace FreeGroupFactorMain
open scoped ContDiff

 theorem wordHom_generatorUnitary {ι : Type uι} (g : FreeGroup ι) :
    UnitaryEvaluation.wordHom generatorUnitary g = groupUnitary g := by
  have he : UnitaryEvaluation.wordHom (generatorUnitary (ι := ι)) =
      groupUnitaryHom (FreeGroup ι) := by
    apply FreeGroup.ext_hom
    intro i
    rfl
  exact DFunLike.congr_fun he g

end FreeGroupFactorMain

namespace FreeGroupFactorMain.PolynomialFlow
variable {A : Type uA} [CStarAlgebra A] [Nontrivial A]
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end FreeGroupFactorMain.PolynomialFlow

end

end OAI
end

section
namespace OAI

noncomputable section

universe uA uι uκ

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff ENNReal

attribute [local instance] Classical.propDecidable

open scoped ContDiff BigOperators ENNReal
namespace FreeGroupFactorMain
theorem source_laurent_moments_bounded {ι : Type uι} [DecidableEq ι]
    (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ)
    (Y : ℝ → (Option ι × Bool) → groupVonNeumann (FreeGroup (Option ι)))
    (hY₀ : ∀ ib, Y 0 ib = groupUnitary (AlgebraPolynomial.signed ib))
    (hsmooth : ∀ ib, ContDiff ℝ ∞ (fun t => Y t ib))
    (hbounded : ∀ t ib, ‖Y t ib‖ ≤ 1)
    (hODE : ∀ t ib, HasDerivAt (fun s => Y s ib)
      (NCPolynomial.eval (Y t)
        (AlgebraPolynomial.encodedField (TraceCocycle.fieldCoefficients h l) ib)) t)
    (J : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hdeg : ∀ ib, NCPolynomial.degree (AlgebraPolynomial.encodedField (TraceCocycle.fieldCoefficients h l) ib) ≤ J + 1)
    (hmass : ∀ ib, NCPolynomial.mass (AlgebraPolynomial.encodedField (TraceCocycle.fieldCoefficients h l) ib) ≤ B)
    (p : NCPolynomial.Expr (Option ι × Bool)) (t : ℝ) :
    canonicalTrace (NCPolynomial.eval (Y t) p) =
      canonicalTrace (NCPolynomial.eval (Y 0) p) := by
  classical
  let V := AlgebraPolynomial.encodedField (TraceCocycle.fieldCoefficients h l)
  have hinitial (q) : canonicalTrace (NCPolynomial.eval (Y 0) (NCPolynomial.delta V q)) = 0 := by
    have hinit : Y 0 = fun ib => groupUnitary (AlgebraPolynomial.signed ib) := funext hY₀
    rw [hinit, canonicalTrace_eval]
    exact AlgebraPolynomial.encoded_initial_trace h l q
  have hreal (L : ℂ →L[ℝ] ℝ) :
      L (canonicalTrace (NCPolynomial.eval (Y t) p)) =
      L (canonicalTrace (NCPolynomial.eval (Y 0) p)) := by
    let Lt := L.comp ((canonicalTraceCLM (G := FreeGroup (Option ι))).restrictScalars ℝ)
    apply NCPolynomial.polynomial_moments Y V Lt hsmooth hODE 1 le_rfl hbounded
      J B hB hdeg hmass
    intro q
    change L (canonicalTrace (NCPolynomial.eval (Y 0) (NCPolynomial.delta V q))) = 0
    rw [hinitial, map_zero]
  exact Complex.ext (hreal Complex.reCLM) (hreal Complex.imCLM)

end FreeGroupFactorMain
namespace FreeGroupFactorMain.UnitaryEvaluation
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι}
 theorem signedTrajectory_coordinate_ode [DecidableEq ι]
    (C : unitary A) (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ)
    (hS : IsSelfAdjoint (laurentValue C l))
    (X : ℝ → ι → A) (hU : ∀ t j, X t j ∈ unitary A)
    (hX : ∀ t i, HasDerivAt (fun s => X s i) (PolynomialFlow.field (laurentValue C l) h (X t) i) t)
    (t : ℝ) (ib : Option ι × Bool) :
    HasDerivAt (fun s => signedTrajectory X hU C s ib)
      (NCPolynomial.eval (signedTrajectory X hU C t)
        (AlgebraPolynomial.encodedField (TraceCocycle.fieldCoefficients h l) ib)) t := by
  have hpos (j : Option ι) : NCPolynomial.eval (signedTrajectory X hU C t)
      (AlgebraPolynomial.encodedField (TraceCocycle.fieldCoefficients h l) (j,true)) =
      coefficientHom (wordHom (extendUnitary (fun j => ⟨X t j, hU t j⟩) C))
        (TraceCocycle.fieldCoefficients h l j) *
        (extendUnitary (fun j => ⟨X t j,hU t j⟩) C j : A) :=
    eval_encodedField_pos _ _ _
  have hneg (j : Option ι) : NCPolynomial.eval (signedTrajectory X hU C t)
      (AlgebraPolynomial.encodedField (TraceCocycle.fieldCoefficients h l) (j,false)) =
      -(star (extendUnitary (fun j => ⟨X t j,hU t j⟩) C j : A) *
        coefficientHom (wordHom (extendUnitary (fun j => ⟨X t j, hU t j⟩) C))
          (TraceCocycle.fieldCoefficients h l j)) :=
    eval_encodedField_neg _ _ _
  rcases ib with ⟨i,b⟩
  cases i with
  | none =>
    cases b
    · rw [hneg]
      simp only [TraceCocycle.fieldCoefficients, map_zero, mul_zero, neg_zero]
      simpa only [signedTrajectory_none_neg] using hasDerivAt_const t (star (C : A))
    · rw [hpos]
      simp only [TraceCocycle.fieldCoefficients, map_zero, zero_mul]
      simpa only [signedTrajectory_none_pos] using hasDerivAt_const t (C : A)
  | some i =>
    have hi := hX t i
    cases b
    · rw [hneg, coefficientHom_fieldCoefficients]
      have hs := hi.star
      have he : star (PolynomialFlow.field (laurentValue C l) h (X t) i) =
          -(star (X t i) * (Complex.I • PolynomialFlow.hamiltonian (laurentValue C l) (h i) (X t))) := by
        simp only [PolynomialFlow.field, star_smul, star_mul, Complex.star_def,
          Complex.conj_I, (PolynomialFlow.selfAdjoint_hamiltonian _ hS _ _).star_eq,
          neg_smul, mul_smul_comm]
      rw [he] at hs
      simpa only [signedTrajectory_some_neg, extendUnitary, Option.elim_some] using hs
    · rw [hpos, coefficientHom_fieldCoefficients]
      simpa only [signedTrajectory_some_pos, extendUnitary, Option.elim_some,
        PolynomialFlow.field, smul_mul_assoc] using hi

end FreeGroupFactorMain.UnitaryEvaluation

namespace FreeGroupFactorMain
open scoped ContDiff
open UnitaryEvaluation

theorem encodedField_finite_range {ι : Type uι} [DecidableEq ι]
    (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ)
    (s : Finset ι) (hs : ∀ i, i ∉ s → h i = 0) :
    (Set.range (AlgebraPolynomial.encodedField (TraceCocycle.fieldCoefficients h l))).Finite := by
  classical
  let S : Finset (Option ι × Bool) := (insert none (s.image some)).product Finset.univ
  let V := AlgebraPolynomial.encodedField (TraceCocycle.fieldCoefficients h l)
  have hz (ib : Option ι × Bool) (hib : ib ∉ S) :
      V ib = AlgebraPolynomial.encode (0 : MonoidAlgebra ℂ (FreeGroup (Option ι))) := by
    have hi : ∃ i, ib.1 = some i ∧ i ∉ s := by
      rcases ib with ⟨i,b⟩
      cases i with
      | none => simp [S] at hib
      | some i => exact ⟨i,rfl,by simpa [S] using hib⟩
    obtain ⟨i,hi,his⟩ := hi
    have hf : TraceCocycle.fieldCoefficients h l (some i) = 0 := by
      simp [TraceCocycle.fieldCoefficients,hs i his]
    change AlgebraPolynomial.encode (TraceCocycle.algebraDerivative _
      (MonoidAlgebra.of ℂ _ (AlgebraPolynomial.signed ib))) = _
    congr 1
    ext b
    cases hb : ib.2 <;>
      simp [AlgebraPolynomial.signed,hi,hb,TraceCocycle.cocycle_inv,hf]
  apply (Set.Finite.insert (AlgebraPolynomial.encode (0 : MonoidAlgebra ℂ (FreeGroup (Option ι))))
    (S.finite_toSet.image V)).subset
  rintro q ⟨ib,rfl⟩
  by_cases hb : ib ∈ S
  · exact Set.mem_insert_of_mem _ ⟨ib,hb,rfl⟩
  · exact Set.mem_insert_iff.mpr (Or.inl (hz ib hb))

theorem source_laurent_moments_finite {ι : Type uι} [DecidableEq ι]
    (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ)
    (s : Finset ι) (hs : ∀ i, i ∉ s → h i = 0)
    (Y : ℝ → (Option ι × Bool) → groupVonNeumann (FreeGroup (Option ι)))
    (hY₀ : ∀ ib, Y 0 ib = groupUnitary (AlgebraPolynomial.signed ib))
    (hsmooth : ∀ ib, ContDiff ℝ ∞ (fun t => Y t ib))
    (hbounded : ∀ t ib, ‖Y t ib‖ ≤ 1)
    (hODE : ∀ t ib, HasDerivAt (fun s => Y s ib)
      (NCPolynomial.eval (Y t)
        (AlgebraPolynomial.encodedField (TraceCocycle.fieldCoefficients h l) ib)) t)
    (p : NCPolynomial.Expr (Option ι × Bool)) (t : ℝ) :
    canonicalTrace (NCPolynomial.eval (Y t) p) =
      canonicalTrace (NCPolynomial.eval (Y 0) p) := by
  classical
  let V := AlgebraPolynomial.encodedField (TraceCocycle.fieldCoefficients h l)
  let S := (encodedField_finite_range h l s hs).toFinset
  have hmem (ib) : V ib ∈ S := by simp [S,V]
  let J := S.sup NCPolynomial.degree
  let B := ∑ q ∈ S, NCPolynomial.mass q
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => NCPolynomial.mass_nonneg _
  apply source_laurent_moments_bounded h l Y hY₀ hsmooth hbounded hODE J B hB
  · intro ib
    exact (Finset.le_sup (f := NCPolynomial.degree) (hmem ib)).trans (Nat.le_succ _)
  · intro ib
    exact Finset.single_le_sum (fun q _ => NCPolynomial.mass_nonneg q) (hmem ib)

 theorem laurent_flow_coordinate_moments {ι : Type uι} [DecidableEq ι]
    (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ)
    (s : Finset ι) (hs : ∀ i, i ∉ s → h i = 0)
    (hS : IsSelfAdjoint (UnitaryEvaluation.laurentValue
      (generatorUnitary (none : Option ι)) l))
    (X : ℝ → ι → groupVonNeumann (FreeGroup (Option ι)))
    (hU : ∀ t j, X t j ∈ unitary (groupVonNeumann (FreeGroup (Option ι))))
    (hX₀ : X 0 = fun j => groupUnitary (FreeGroup.of (some j)))
    (hX : ∀ t i, HasDerivAt (fun s => X s i) (PolynomialFlow.field
      (UnitaryEvaluation.laurentValue (generatorUnitary (none : Option ι)) l) h (X t) i) t)
    (hsmoothX : ∀ i, ContDiff ℝ ∞ (fun t => X t i)) :
    ∀ t (g : FreeGroup (Option ι)),
      canonicalTrace (UnitaryEvaluation.wordHom
        (UnitaryEvaluation.extendUnitary (fun j => ⟨X t j, hU t j⟩)
          (generatorUnitary none)) g) = if g = 1 then 1 else 0 := by
  classical
  let C : unitary (groupVonNeumann (FreeGroup (Option ι))) := generatorUnitary none
  let S := UnitaryEvaluation.laurentValue C l
  let Y := UnitaryEvaluation.signedTrajectory X hU C
  have hu0 : UnitaryEvaluation.extendUnitary (fun j => ⟨X 0 j, hU 0 j⟩) C =
      generatorUnitary := by
    funext i
    cases i with
    | none => rfl
    | some j => apply Subtype.ext; exact congrFun hX₀ j
  have hY₀ (ib) : Y 0 ib = groupUnitary (AlgebraPolynomial.signed ib) := by
    dsimp [Y, UnitaryEvaluation.signedTrajectory]
    rw [hu0, wordHom_generatorUnitary]
  have hsmooth (ib) : ContDiff ℝ ∞ (fun t => Y t ib) := by
    rcases ib with ⟨i,b⟩
    cases i with
    | none => cases b <;>
        simp only [Y,signedTrajectory_none_pos,signedTrajectory_none_neg] <;>
        exact contDiff_const
    | some i => cases b
                · simp only [Y,signedTrajectory_some_neg]
                  exact (starL ℝ (A := groupVonNeumann (FreeGroup (Option ι)))).contDiff.comp (hsmoothX i)
                · simpa only [Y,signedTrajectory_some_pos] using hsmoothX i
  have hbounded (t ib) : ‖Y t ib‖ ≤ 1 :=
    UnitaryEvaluation.norm_signedTrajectory_le_one X hU C t ib
  intro t g
  let p := AlgebraPolynomial.encode (MonoidAlgebra.of ℂ (FreeGroup (Option ι)) g)
  have hmoment := source_laurent_moments_finite h l s hs Y hY₀ hsmooth hbounded
    (UnitaryEvaluation.signedTrajectory_coordinate_ode C h l hS X hU hX) p t
  have he (s) : NCPolynomial.eval (Y s) p =
      UnitaryEvaluation.wordHom
        (UnitaryEvaluation.extendUnitary (fun j => ⟨X s j, hU s j⟩) C) g := by
    change NCPolynomial.eval (fun ib => UnitaryEvaluation.wordHom
      (UnitaryEvaluation.extendUnitary (fun j => ⟨X s j, hU s j⟩) C)
        (AlgebraPolynomial.signed ib)) (AlgebraPolynomial.encode
          (MonoidAlgebra.of ℂ (FreeGroup (Option ι)) g)) = _
    rw [UnitaryEvaluation.eval_encode, UnitaryEvaluation.algebraHom_of]
  rw [he, he, hu0, wordHom_generatorUnitary, canonicalTrace_groupUnitary] at hmoment
  exact hmoment

end FreeGroupFactorMain

namespace FreeGroupFactorMain.UnitaryEvaluation
open scoped ContDiff
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι} {κ : Type uκ}

theorem hamiltonian_map [DecidableEq ι] [DecidableEq κ]
    (S : A) (h : FreeGroup ι →₀ ℝ) (f : ι → κ) (U : κ → unitary A) :
    PolynomialFlow.hamiltonian S (Finsupp.mapDomain (FreeGroup.map f) h) (fun j => (U j : A)) =
      PolynomialFlow.hamiltonian S h (fun i => (U (f i) : A)) := by
  classical
  simp only [PolynomialFlow.hamiltonian]
  rw [Finsupp.sum_mapDomain_index (fun g => by simp) (fun g a b => by simp [add_smul])]
  apply Finsupp.sum_congr
  intro g hg
  rw [← wordHom_word,wordHom_map,wordHom_word]
  rfl

theorem solution_coordinate_deriv [Fintype ι] [DecidableEq ι]
    (S : A) (h : ι → FreeGroup ι →₀ ℝ) (X : ℝ → ι → A)
    (hX : ∀ t, HasDerivAt X (PolynomialFlow.field S h (X t)) t) (t : ℝ) (i : ι) :
    HasDerivAt (fun s => X s i) (PolynomialFlow.field S h (X t) i) t :=
  hasDerivAt_pi.mp (hX t) i

theorem solution_coordinate_smooth [Fintype ι] [DecidableEq ι]
    (S : A) (h : ι → FreeGroup ι →₀ ℝ) (X : ℝ → ι → A)
    (hX : ∀ t, HasDerivAt X (PolynomialFlow.field S h (X t)) t) (i : ι) :
    ContDiff ℝ ∞ (fun t => X t i) :=
  (contDiff_apply ℝ A i).comp (PolynomialFlow.smooth_solution S h X hX)

end FreeGroupFactorMain.UnitaryEvaluation

namespace FreeGroupFactorMain.FiniteActive
open UnitaryEvaluation
open scoped ContDiff
variable {ι : Type uι} {κ : Type uκ}

def coefficients (h : ι → FreeGroup ι →₀ ℝ) : (ι ⊕ κ) → FreeGroup (ι ⊕ κ) →₀ ℝ :=
  Sum.elim (fun i => Finsupp.mapDomain (FreeGroup.map Sum.inl) (h i)) (fun _ => 0)

theorem field_inl [DecidableEq ι] [DecidableEq κ]
    (S : Ambient ι κ) (h : ι → FreeGroup ι →₀ ℝ)
    (X : ι → Ambient ι κ) (hX : ∀ i, X i ∈ unitary (Ambient ι κ)) (i : ι) :
    PolynomialFlow.field S (coefficients h) (tuple X) (Sum.inl i) =
      PolynomialFlow.field S h X i := by
  let U : (ι ⊕ κ) → unitary (Ambient ι κ) := fun j => ⟨tuple X j,tuple_unitary X hX j⟩
  change Complex.I • (PolynomialFlow.hamiltonian S
    (Finsupp.mapDomain (FreeGroup.map Sum.inl) (h i)) (fun j => (U j : Ambient ι κ)) * X i) = _
  rw [hamiltonian_map]
  rfl

@[simp] theorem field_inr [DecidableEq ι] [DecidableEq κ]
    (S : Ambient ι κ) (h : ι → FreeGroup ι →₀ ℝ)
    (X : ι → Ambient ι κ) (k : κ) :
    PolynomialFlow.field S (coefficients h) (tuple X) (Sum.inr k) = 0 := by
  change Complex.I • ((0 : Ambient ι κ) * tuple X (Sum.inr k)) = 0
  rw [zero_mul]
  apply Subtype.ext
  exact smul_zero Complex.I

theorem moments [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ)
    (hS : IsSelfAdjoint (laurentValue
      (generatorUnitary (none : Option (ι ⊕ κ))) l))
    (X : ℝ → ι → Ambient ι κ) (hU : ∀ t i, X t i ∈ unitary (Ambient ι κ))
    (hX₀ : X 0 = fun i => groupUnitary (FreeGroup.of (some (Sum.inl i))))
    (hX : ∀ t, HasDerivAt X (PolynomialFlow.field
      (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l) h (X t)) t) :
    ∀ t (g : FreeGroup (Option (ι ⊕ κ))), canonicalTrace (wordHom
      (extendUnitary (fun j => ⟨tuple (X t) j,tuple_unitary (X t) (hU t) j⟩)
        (generatorUnitary none)) g) = if g = 1 then 1 else 0 := by
  classical
  let s : Finset (ι ⊕ κ) := Finset.univ.image Sum.inl
  have hs (j) (hj : j ∉ s) : coefficients (κ := κ) h j = 0 := by
    cases j with
    | inl i => simp [s] at hj
    | inr k => rfl
  apply laurent_flow_coordinate_moments (coefficients h) l s hs hS
    (fun t => tuple (X t)) (fun t => tuple_unitary (X t) (hU t))
  · funext j
    cases j with
    | inl i => exact congrFun hX₀ i
    | inr k => rfl
  · intro t j
    cases j with
    | inl i =>
      rw [field_inl _ h (X t) (hU t)]
      exact solution_coordinate_deriv _ h X hX t i
    | inr k =>
      rw [field_inr]
      exact hasDerivAt_const t _
  · intro j
    cases j with
    | inl i =>
      change ContDiff ℝ _ (fun t => X t i)
      exact solution_coordinate_smooth _ h X hX i
    | inr k => exact contDiff_const

end FreeGroupFactorMain.FiniteActive

namespace FreeGroupFactorMain
open UnitaryEvaluation
open scoped ENNReal

end FreeGroupFactorMain

end

end OAI
end

theorem solution.{uι,uκ} : type_of% @OAI.FreeGroupFactorMain.FiniteActive.moments.{uι,uκ} := @OAI.FreeGroupFactorMain.FiniteActive.moments.{uι,uκ}
