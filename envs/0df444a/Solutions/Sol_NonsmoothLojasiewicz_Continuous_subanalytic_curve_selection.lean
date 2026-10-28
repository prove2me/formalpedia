-- Prove2me | solution 1 for NonsmoothLojasiewicz.Continuous.subanalytic_curve_selection
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T06:32:26.494328+00:00
-- url     : https://prove2.me/submissions/dffffdc2-3a97-40b4-b2a2-4aa37faa84c9

import Mathlib
import Definitions.Def_NonsmoothLojasiewicz_Continuous_IsSubanalytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! SubanalyticLib L6a: item C1 of c2c9aa25 (one-variable growth) from CURVE SELECTION.
If the graph of a positive `ψ` over `(0, η)` admits an analytic arc at `(0,0)` whenever `(0,0)` is
in its closure, then `ψ s ≥ c s^α` near `0`. Curve selection is the hub theorem (also needed for
C34 and the exponent `< 1`), so C1 no longer needs the planar curve lemma L4a. -/

open Filter Topology Set
open NonsmoothLojasiewicz.Continuous

set_option linter.unusedSectionVars false

namespace SubanalyticLib

/-- `A` admits an analytic arc at `x₀`: `γ` analytic at `0`, `γ 0 = x₀`, `γ (0, ε) ⊆ A`. -/
def HasArcAt {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (A : Set X) (x₀ : X) : Prop :=
  ∃ γ : ℝ → X, AnalyticAt ℝ γ 0 ∧ γ 0 = x₀ ∧ ∃ ε > 0, ∀ u ∈ Ioo (0 : ℝ) ε, γ u ∈ A

/-- Curve selection for subanalytic subsets of `X` (Bierstone–Milman 1988, Lojasiewicz). -/
def CurveSelection (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] :
    Prop :=
  ∀ A : Set X, IsSubanalytic A → ∀ x₀ ∈ closure A, HasArcAt A x₀

/-- Curve selection for semianalytic subsets of `Y` (the hub theorem, Lojasiewicz 1964). -/
def SemiCurveSelection (Y : Type*) [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [FiniteDimensional ℝ Y] : Prop :=
  ∀ B : Set Y, IsSemianalytic B → Bornology.IsBounded B → ∀ y₀ ∈ closure B, HasArcAt B y₀

/-- Curve selection passes from bounded semianalytic sets of `X × ℝ^m` to subanalytic sets of `X`. -/
theorem curveSelection_of_semi {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X]
    (hS : ∀ m : ℕ, SemiCurveSelection (X × EuclideanSpace ℝ (Fin m))) : CurveSelection X := by
  intro A hA x₀ hx₀
  obtain ⟨V, hV, m, -, B, hBs, hBb, hAV⟩ := hA x₀
  have hx₀' : x₀ ∈ closure (Prod.fst '' B) := by
    rw [← hAV, mem_closure_iff_nhds]
    intro t ht
    obtain ⟨y, hy⟩ := mem_closure_iff_nhds.mp hx₀ (t ∩ V) (Filter.inter_mem ht hV)
    exact ⟨y, hy.1.1, hy.2, hy.1.2⟩
  have hK : IsCompact (closure B) := hBb.isCompact_closure
  have hcl : closure (Prod.fst '' B) ⊆ Prod.fst '' closure B :=
    closure_minimal (Set.image_mono subset_closure) (hK.image continuous_fst).isClosed
  obtain ⟨b, hb, hbx⟩ := hcl hx₀'
  obtain ⟨γ, hγ, hγ0, ε, hε, hγB⟩ := hS m B hBs hBb b hb
  refine ⟨fun u => (γ u).1, (analyticAt_fst).comp hγ, by simp [hγ0, hbx], ε, hε, fun u hu => ?_⟩
  have h : (γ u).1 ∈ A ∩ V := by rw [hAV]; exact ⟨γ u, hγB u hu, rfl⟩
  exact h.1

end SubanalyticLib


/-! SubanalyticLib L1a: weighted ℓ¹ norms of multivariable power series.
`Conv w f` : the series `f` converges absolutely on the closed polydisc of polyradius `w`
(`∑ |a_α| w^α < ∞`); `wn w f` is that weighted norm.  These are the Banach-algebra estimates
behind convergent Weierstrass division (plan L2). -/


set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace SubanalyticLib

section Conv

open MvPowerSeries

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- weight of the monomial `X^α` for the polyradius `w`. -/
noncomputable def mw (w : σ → ℝ) (α : σ →₀ ℕ) : ℝ := ∏ i, w i ^ α i

theorem mw_zero (w : σ → ℝ) : mw w 0 = 1 := by simp [mw]

theorem mw_add (w : σ → ℝ) (α β : σ →₀ ℕ) : mw w (α + β) = mw w α * mw w β := by
  simp [mw, pow_add, Finset.prod_mul_distrib]

theorem mw_nonneg {w : σ → ℝ} (hw : ∀ i, 0 ≤ w i) (α : σ →₀ ℕ) : 0 ≤ mw w α :=
  Finset.prod_nonneg fun i _ => pow_nonneg (hw i) _

theorem mw_single (w : σ → ℝ) (i : σ) (k : ℕ) : mw w (Finsupp.single i k) = w i ^ k := by
  unfold mw
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem mw_mono {w w' : σ → ℝ} (hw' : ∀ i, 0 ≤ w' i) (hle : ∀ i, w' i ≤ w i) (α : σ →₀ ℕ) :
    mw w' α ≤ mw w α :=
  Finset.prod_le_prod (fun i _ => pow_nonneg (hw' i) _)
    (fun i _ => pow_le_pow_left₀ (hw' i) (hle i) _)

/-- the weighted absolute coefficient family. -/
noncomputable def wt (w : σ → ℝ) (f : MvPowerSeries σ ℝ) (α : σ →₀ ℕ) : ℝ :=
  |coeff α f| * mw w α

/-- `f` converges absolutely on the closed polydisc of polyradius `w`. -/
def Conv (w : σ → ℝ) (f : MvPowerSeries σ ℝ) : Prop := Summable (wt w f)

/-- the weighted ℓ¹ norm. -/
noncomputable def wn (w : σ → ℝ) (f : MvPowerSeries σ ℝ) : ℝ := ∑' α, wt w f α

variable {w : σ → ℝ}

theorem wt_nonneg (hw : ∀ i, 0 ≤ w i) (f : MvPowerSeries σ ℝ) (α : σ →₀ ℕ) : 0 ≤ wt w f α :=
  mul_nonneg (abs_nonneg _) (mw_nonneg hw α)

theorem wn_nonneg (hw : ∀ i, 0 ≤ w i) (f : MvPowerSeries σ ℝ) : 0 ≤ wn w f :=
  tsum_nonneg (wt_nonneg hw f)

theorem wt_zero (α : σ →₀ ℕ) : wt w 0 α = 0 := by simp [wt]

theorem conv_zero : Conv w (0 : MvPowerSeries σ ℝ) := by
  have : wt w (0 : MvPowerSeries σ ℝ) = fun _ => 0 := funext wt_zero
  rw [Conv, this]; exact summable_zero

theorem wn_zero : wn w (0 : MvPowerSeries σ ℝ) = 0 := by
  have : wt w (0 : MvPowerSeries σ ℝ) = fun _ => 0 := funext wt_zero
  rw [wn, this, tsum_zero]

theorem wt_neg (f : MvPowerSeries σ ℝ) (α : σ →₀ ℕ) : wt w (-f) α = wt w f α := by
  simp [wt]

theorem Conv.neg {f : MvPowerSeries σ ℝ} (hf : Conv w f) : Conv w (-f) := by
  have : wt w (-f) = wt w f := funext (wt_neg f)
  rw [Conv, this]; exact hf

theorem wn_neg (f : MvPowerSeries σ ℝ) : wn w (-f) = wn w f := by
  have : wt w (-f) = wt w f := funext (wt_neg f)
  rw [wn, wn, this]

theorem wt_smul (c : ℝ) (f : MvPowerSeries σ ℝ) (α : σ →₀ ℕ) : wt w (c • f) α = |c| * wt w f α := by
  simp only [wt, map_smul, smul_eq_mul, abs_mul]; ring

theorem Conv.smul {f : MvPowerSeries σ ℝ} (hf : Conv w f) (c : ℝ) : Conv w (c • f) := by
  have : wt w (c • f) = fun α => |c| * wt w f α := funext (wt_smul c f)
  rw [Conv, this]; exact hf.mul_left _

theorem wt_add_le (hw : ∀ i, 0 ≤ w i) (f g : MvPowerSeries σ ℝ) (α : σ →₀ ℕ) :
    wt w (f + g) α ≤ wt w f α + wt w g α := by
  unfold wt
  rw [map_add, ← add_mul]
  exact mul_le_mul_of_nonneg_right (abs_add_le _ _) (mw_nonneg hw α)

theorem Conv.add (hw : ∀ i, 0 ≤ w i) {f g : MvPowerSeries σ ℝ} (hf : Conv w f) (hg : Conv w g) :
    Conv w (f + g) :=
  Summable.of_nonneg_of_le (wt_nonneg hw _) (wt_add_le hw f g) (Summable.add hf hg)

theorem wn_add_le (hw : ∀ i, 0 ≤ w i) {f g : MvPowerSeries σ ℝ} (hf : Conv w f) (hg : Conv w g) :
    wn w (f + g) ≤ wn w f + wn w g :=
  hasSum_le (wt_add_le hw f g) (Conv.add hw hf hg).hasSum (hf.hasSum.add hg.hasSum)

theorem Conv.sub (hw : ∀ i, 0 ≤ w i) {f g : MvPowerSeries σ ℝ} (hf : Conv w f) (hg : Conv w g) :
    Conv w (f - g) := by
  rw [sub_eq_add_neg]; exact Conv.add hw hf (Conv.neg hg)

theorem wt_mul_le (hw : ∀ i, 0 ≤ w i) (f g : MvPowerSeries σ ℝ) (γ : σ →₀ ℕ) :
    wt w (f * g) γ ≤ ∑ p ∈ Finset.HasAntidiagonal.antidiagonal γ, wt w f p.1 * wt w g p.2 := by
  unfold wt
  rw [coeff_mul]
  calc |∑ p ∈ Finset.HasAntidiagonal.antidiagonal γ, coeff p.1 f * coeff p.2 g| * mw w γ
      ≤ (∑ p ∈ Finset.HasAntidiagonal.antidiagonal γ, |coeff p.1 f * coeff p.2 g|) * mw w γ :=
        mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (mw_nonneg hw γ)
    _ = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal γ, |coeff p.1 f| * mw w p.1 * (|coeff p.2 g| * mw w p.2) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
        rw [← hp, mw_add, abs_mul]; ring

theorem summable_wt_antidiag (hw : ∀ i, 0 ≤ w i) {f g : MvPowerSeries σ ℝ} (hf : Conv w f)
    (hg : Conv w g) :
    Summable fun x : (σ →₀ ℕ) × (σ →₀ ℕ) => wt w f x.1 * wt w g x.2 :=
  Summable.mul_of_nonneg hf hg (Pi.le_def.2 fun α => by simpa using wt_nonneg hw f α)
    (Pi.le_def.2 fun α => by simpa using wt_nonneg hw g α)

theorem Conv.mul (hw : ∀ i, 0 ≤ w i) {f g : MvPowerSeries σ ℝ} (hf : Conv w f) (hg : Conv w g) :
    Conv w (f * g) :=
  Summable.of_nonneg_of_le (wt_nonneg hw _) (wt_mul_le hw f g)
    (summable_sum_mul_antidiagonal_of_summable_mul (summable_wt_antidiag hw hf hg))

theorem wn_mul_le (hw : ∀ i, 0 ≤ w i) {f g : MvPowerSeries σ ℝ} (hf : Conv w f) (hg : Conv w g) :
    wn w (f * g) ≤ wn w f * wn w g := by
  have hS := summable_sum_mul_antidiagonal_of_summable_mul (summable_wt_antidiag hw hf hg)
  rw [wn, wn, wn, Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal hf hg
    (summable_wt_antidiag hw hf hg)]
  exact hasSum_le (wt_mul_le hw f g) (Conv.mul hw hf hg).hasSum hS.hasSum

theorem Conv.pow (hw : ∀ i, 0 ≤ w i) {f : MvPowerSeries σ ℝ} (hf : Conv w f) (n : ℕ) :
    Conv w (f ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    have : wt w (1 : MvPowerSeries σ ℝ) = fun α => if α = 0 then 1 else 0 := by
      funext α; by_cases h : α = 0 <;> simp [wt, coeff_one, h, mw_zero]
    rw [Conv, this]
    exact summable_of_ne_finset_zero (s := {0}) (fun α hα => by simp at hα; simp [hα])
  | succ n ih => rw [pow_succ]; exact Conv.mul hw ih hf

/-! ### constants, variables -/

theorem hasSum_wt_C (a : ℝ) : HasSum (wt w (C a : MvPowerSeries σ ℝ)) |a| := by
  have : |a| = wt w (C a : MvPowerSeries σ ℝ) 0 := by simp [wt, mw_zero]
  rw [this]
  exact hasSum_single 0 (fun β hβ => by simp [wt, coeff_C, hβ])

theorem conv_C (a : ℝ) : Conv w (C a : MvPowerSeries σ ℝ) := (hasSum_wt_C a).summable

theorem wn_C (a : ℝ) : wn w (C a : MvPowerSeries σ ℝ) = |a| := (hasSum_wt_C a).tsum_eq

theorem wn_one : wn w (1 : MvPowerSeries σ ℝ) = 1 := by
  simpa using wn_C (w := w) (σ := σ) 1

theorem hasSum_wt_X (hw : ∀ i, 0 ≤ w i) (i : σ) : HasSum (wt w (X i : MvPowerSeries σ ℝ)) (w i) := by
  have : w i = wt w (X i : MvPowerSeries σ ℝ) (Finsupp.single i 1) := by
    simp [wt, coeff_X, mw_single]
  rw [this]
  exact hasSum_single _ (fun β hβ => by simp [wt, coeff_X, hβ])

theorem conv_X (hw : ∀ i, 0 ≤ w i) (i : σ) : Conv w (X i : MvPowerSeries σ ℝ) :=
  (hasSum_wt_X hw i).summable

theorem wt_mono {w' : σ → ℝ} (hw' : ∀ i, 0 ≤ w' i) (hle : ∀ i, w' i ≤ w i)
    (f : MvPowerSeries σ ℝ) (α : σ →₀ ℕ) : wt w' f α ≤ wt w f α :=
  mul_le_mul_of_nonneg_left (mw_mono hw' hle α) (abs_nonneg _)

theorem Conv.mono {w' : σ → ℝ} (hw' : ∀ i, 0 ≤ w' i) (hle : ∀ i, w' i ≤ w i)
    {f : MvPowerSeries σ ℝ} (hf : Conv w f) : Conv w' f :=
  Summable.of_nonneg_of_le (wt_nonneg hw' f) (wt_mono hw' hle f) hf

theorem wn_mono {w' : σ → ℝ} (hw' : ∀ i, 0 ≤ w' i) (hle : ∀ i, w' i ≤ w i)
    {f : MvPowerSeries σ ℝ} (hf : Conv w f) : wn w' f ≤ wn w f :=
  hasSum_le (wt_mono hw' hle f) (Conv.mono hw' hle hf).hasSum hf.hasSum

/-- a finite family bound gives `Conv` (partial sums bounded). -/
theorem conv_of_sum_le (hw : ∀ i, 0 ≤ w i) {f : MvPowerSeries σ ℝ} {c : ℝ}
    (h : ∀ s : Finset (σ →₀ ℕ), ∑ α ∈ s, wt w f α ≤ c) : Conv w f :=
  summable_of_sum_le (Pi.le_def.2 fun α => by simpa using wt_nonneg hw f α) h

theorem wn_le_of_sum_le (hw : ∀ i, 0 ≤ w i) {f : MvPowerSeries σ ℝ} {c : ℝ}
    (h : ∀ s : Finset (σ →₀ ℕ), ∑ α ∈ s, wt w f α ≤ c) : wn w f ≤ c :=
  (conv_of_sum_le hw h).tsum_le_of_sum_le h

/-! ### approximation principle, finite sums, powers, inverses -/

/-- if `f` agrees coefficientwise with uniformly bounded convergent approximants, `f` converges. -/
theorem conv_of_approx (hw : ∀ i, 0 ≤ w i) {f : MvPowerSeries σ ℝ} (P : ℕ → MvPowerSeries σ ℝ)
    (D : (σ →₀ ℕ) → ℕ) {B : ℝ} (hP : ∀ N, Conv w (P N)) (hB : ∀ N, wn w (P N) ≤ B)
    (hc : ∀ α N, D α ≤ N → coeff α f = coeff α (P N)) : Conv w f ∧ wn w f ≤ B := by
  have key : ∀ s : Finset (σ →₀ ℕ), ∑ α ∈ s, wt w f α ≤ B := by
    intro s
    have h1 : ∑ α ∈ s, wt w f α = ∑ α ∈ s, wt w (P (s.sup D)) α := by
      refine Finset.sum_congr rfl fun α hα => ?_
      simp only [wt]; rw [hc α (s.sup D) (Finset.le_sup hα)]
    rw [h1]
    exact (sum_le_hasSum s (fun β _ => wt_nonneg hw _ β) (hP _).hasSum).trans (hB _)
  exact ⟨conv_of_sum_le hw key, wn_le_of_sum_le hw key⟩

theorem conv_finset_sum (hw : ∀ i, 0 ≤ w i) {ι : Type*} (s : Finset ι)
    (F : ι → MvPowerSeries σ ℝ) (hF : ∀ i ∈ s, Conv w (F i)) :
    Conv w (∑ i ∈ s, F i) ∧ wn w (∑ i ∈ s, F i) ≤ ∑ i ∈ s, wn w (F i) := by
  classical
  revert hF
  refine Finset.induction_on s ?_ ?_
  · intro _; simp [conv_zero, wn_zero]
  · intro a s ha ih hF
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hs := ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))
    have haF := hF a (Finset.mem_insert_self a s)
    exact ⟨Conv.add hw haF hs.1, (wn_add_le hw haF hs.1).trans (by linarith [hs.2])⟩

theorem wn_pow_le (hw : ∀ i, 0 ≤ w i) {h : MvPowerSeries σ ℝ} (hh : Conv w h) (k : ℕ) :
    wn w (h ^ k) ≤ wn w h ^ k := by
  induction k with
  | zero => simp [wn_one]
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact (wn_mul_le hw (Conv.pow hw hh k) hh).trans
      (mul_le_mul_of_nonneg_right ih (wn_nonneg hw h))

/-- **convergent inverse**: a series that is a small perturbation of its constant term is a unit
of the convergent algebra, with an explicit bound. -/
theorem conv_inv (hw : ∀ i, 0 ≤ w i) {u : MvPowerSeries σ ℝ} (hu : Conv w u) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hc : constantCoeff u ≠ 0)
    (hq : wn w (u - C (constantCoeff u)) ≤ q * |constantCoeff u|) :
    Conv w u⁻¹ ∧ wn w u⁻¹ ≤ |constantCoeff u|⁻¹ * (1 - q)⁻¹ := by
  set c := constantCoeff u with hcdef
  set h : MvPowerSeries σ ℝ := -(C c⁻¹ * (u - C c)) with hhdef
  have hcpos : 0 < |c| := abs_pos.2 hc
  have hd : Conv w (u - C c) := Conv.sub hw hu (conv_C c)
  have hh : Conv w h := Conv.neg (Conv.mul hw (conv_C _) hd)
  have hwh : wn w h ≤ q := by
    rw [hhdef, wn_neg]
    calc wn w (C c⁻¹ * (u - C c)) ≤ wn w (C c⁻¹ : MvPowerSeries σ ℝ) * wn w (u - C c) :=
          wn_mul_le hw (conv_C _) hd
      _ = |c|⁻¹ * wn w (u - C c) := by rw [wn_C, abs_inv]
      _ ≤ |c|⁻¹ * (q * |c|) := mul_le_mul_of_nonneg_left hq (inv_nonneg.2 (abs_nonneg c))
      _ = q := by field_simp
  have hh0 : constantCoeff h = 0 := by simp [hhdef, hcdef]
  have hu_eq : u = C c * (1 - h) := by
    rw [hhdef, sub_neg_eq_add, mul_add, mul_one, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hc,
      map_one, one_mul]
    ring
  have hPN : ∀ N : ℕ, u⁻¹ - C c⁻¹ * ∑ i ∈ Finset.range N, h ^ i = u⁻¹ * h ^ N := by
    intro N
    have h1 : u * (C c⁻¹ * ∑ i ∈ Finset.range N, h ^ i) = 1 - h ^ N := by
      calc u * (C c⁻¹ * ∑ i ∈ Finset.range N, h ^ i)
          = (C c * C c⁻¹) * ((1 - h) * ∑ i ∈ Finset.range N, h ^ i) := by
            rw [hu_eq]; ring
        _ = 1 - h ^ N := by rw [← map_mul, mul_inv_cancel₀ hc, map_one, one_mul, mul_neg_geom_sum]
    calc u⁻¹ - C c⁻¹ * ∑ i ∈ Finset.range N, h ^ i
        = u⁻¹ * (1 - u * (C c⁻¹ * ∑ i ∈ Finset.range N, h ^ i)) := by
          rw [mul_sub, mul_one, ← mul_assoc, MvPowerSeries.inv_mul_cancel u hc, one_mul]
      _ = u⁻¹ * h ^ N := by rw [h1]; ring
  have hcoeff : ∀ α N, Finsupp.degree α + 1 ≤ N →
      coeff α u⁻¹ = coeff α (C c⁻¹ * ∑ i ∈ Finset.range N, h ^ i) := by
    intro α N hN
    have hz : coeff α (u⁻¹ * h ^ N) = 0 := by
      apply coeff_of_lt_order
      calc ((Finsupp.degree α : ℕ) : ℕ∞) < N := by exact_mod_cast (Nat.lt_of_succ_le hN)
        _ ≤ (h ^ N).order := le_order_pow_of_constantCoeff_eq_zero N hh0
        _ ≤ u⁻¹.order + (h ^ N).order := le_add_self
        _ ≤ (u⁻¹ * h ^ N).order := le_order_mul
    have := congrArg (coeff α) (hPN N)
    rw [map_sub, hz, sub_eq_zero] at this
    exact this
  have hPc : ∀ N : ℕ, Conv w (C c⁻¹ * ∑ i ∈ Finset.range N, h ^ i) := fun N =>
    Conv.mul hw (conv_C _) (conv_finset_sum hw _ _ (fun i _ => Conv.pow hw hh i)).1
  have hPB : ∀ N : ℕ, wn w (C c⁻¹ * ∑ i ∈ Finset.range N, h ^ i) ≤ |c|⁻¹ * (1 - q)⁻¹ := by
    intro N
    have hS := conv_finset_sum hw (Finset.range N) (fun i => h ^ i) (fun i _ => Conv.pow hw hh i)
    have hsum : ∑ i ∈ Finset.range N, wn w (h ^ i) ≤ (1 - q)⁻¹ :=
      (Finset.sum_le_sum fun i _ => (wn_pow_le hw hh i).trans
        (pow_le_pow_left₀ (wn_nonneg hw h) hwh i)).trans
        (sum_le_hasSum _ (fun i _ => pow_nonneg hq0 i) (hasSum_geometric_of_lt_one hq0 hq1))
    calc wn w (C c⁻¹ * ∑ i ∈ Finset.range N, h ^ i)
        ≤ wn w (C c⁻¹ : MvPowerSeries σ ℝ) * wn w (∑ i ∈ Finset.range N, h ^ i) :=
          wn_mul_le hw (conv_C _) hS.1
      _ = |c|⁻¹ * wn w (∑ i ∈ Finset.range N, h ^ i) := by rw [wn_C, abs_inv]
      _ ≤ |c|⁻¹ * (1 - q)⁻¹ :=
          mul_le_mul_of_nonneg_left (hS.2.trans hsum) (inv_nonneg.2 (abs_nonneg c))
  exact conv_of_approx hw (fun N => C c⁻¹ * ∑ i ∈ Finset.range N, h ^ i)
    (fun α => Finsupp.degree α + 1) hPc hPB hcoeff

end Conv

end SubanalyticLib

/-! SubanalyticLib L2a (body; prepend L1_Conv.lean): a distinguished variable `y`, the operators
`lowPart d` (`y`-degree `< d`) and `hatPart d` (quotient by `y^d`), and the `x`-order `XOrd`. -/

namespace SubanalyticLib

section Split

open MvPowerSeries

variable {σ : Type*} [Fintype σ] [DecidableEq σ] (y : σ)

/-- the part of `f` of `y`-degree `< d`. -/
noncomputable def lowPart (d : ℕ) (f : MvPowerSeries σ ℝ) : MvPowerSeries σ ℝ :=
  fun α => if α y < d then coeff α f else 0

/-- the quotient of `f` by `y^d`, dropping the low part. -/
noncomputable def hatPart (d : ℕ) (f : MvPowerSeries σ ℝ) : MvPowerSeries σ ℝ :=
  fun α => coeff (α + Finsupp.single y d) f

theorem coeff_lowPart (d : ℕ) (f : MvPowerSeries σ ℝ) (α : σ →₀ ℕ) :
    coeff α (lowPart y d f) = if α y < d then coeff α f else 0 := rfl

theorem coeff_hatPart (d : ℕ) (f : MvPowerSeries σ ℝ) (α : σ →₀ ℕ) :
    coeff α (hatPart y d f) = coeff (α + Finsupp.single y d) f := rfl

theorem hatPart_add (d : ℕ) (f g : MvPowerSeries σ ℝ) :
    hatPart y d (f + g) = hatPart y d f + hatPart y d g := by
  ext α; simp only [coeff_hatPart, map_add]

theorem hatPart_sub (d : ℕ) (f g : MvPowerSeries σ ℝ) :
    hatPart y d (f - g) = hatPart y d f - hatPart y d g := by
  ext α; simp only [coeff_hatPart, map_sub]

theorem hatPart_finset_sum (d : ℕ) {ι : Type*} (s : Finset ι) (F : ι → MvPowerSeries σ ℝ) :
    hatPart y d (∑ i ∈ s, F i) = ∑ i ∈ s, hatPart y d (F i) := by
  ext α; simp only [coeff_hatPart, map_sum]

theorem single_le_iff' (d : ℕ) (α : σ →₀ ℕ) : Finsupp.single y d ≤ α ↔ d ≤ α y :=
  Finsupp.single_le_iff

/-- `f = lowPart + y^d * hatPart`. -/
theorem low_add_hat (d : ℕ) (f : MvPowerSeries σ ℝ) :
    f = lowPart y d f + X y ^ d * hatPart y d f := by
  ext α
  rw [map_add, X_pow_eq, coeff_monomial_mul, coeff_lowPart, coeff_hatPart]
  by_cases h : α y < d
  · have : ¬ Finsupp.single y d ≤ α := by rw [single_le_iff']; omega
    rw [if_pos h, if_neg this, add_zero]
  · have : Finsupp.single y d ≤ α := by rw [single_le_iff']; omega
    rw [if_neg h, if_pos this, zero_add, one_mul, tsub_add_cancel_of_le this]

theorem hatPart_X_pow_mul (d : ℕ) (g : MvPowerSeries σ ℝ) : hatPart y d (X y ^ d * g) = g := by
  ext α
  rw [coeff_hatPart, X_pow_eq, add_comm, coeff_add_monomial_mul, one_mul]

theorem hatPart_lowPart (d : ℕ) (f : MvPowerSeries σ ℝ) : hatPart y d (lowPart y d f) = 0 := by
  ext α
  rw [coeff_hatPart, coeff_lowPart, if_neg]
  · simp
  · simp

theorem lowPart_eq_self_iff (d : ℕ) (f : MvPowerSeries σ ℝ) :
    lowPart y d f = f ↔ hatPart y d f = 0 := by
  constructor
  · intro h; rw [← h, hatPart_lowPart]
  · intro h
    conv_rhs => rw [low_add_hat y d f, h, mul_zero, add_zero]

/-! ### weighted bounds -/

variable {w : σ → ℝ}

theorem wt_lowPart_le (d : ℕ) (f : MvPowerSeries σ ℝ) (α : σ →₀ ℕ) (hw : ∀ i, 0 ≤ w i) :
    wt w (lowPart y d f) α ≤ wt w f α := by
  unfold wt; rw [coeff_lowPart]; split_ifs
  · exact le_rfl
  · simp only [abs_zero, zero_mul]; exact mul_nonneg (abs_nonneg _) (mw_nonneg hw α)

theorem Conv.low (hw : ∀ i, 0 ≤ w i) (d : ℕ) {f : MvPowerSeries σ ℝ} (hf : Conv w f) :
    Conv w (lowPart y d f) :=
  Summable.of_nonneg_of_le (wt_nonneg hw _) (fun α => wt_lowPart_le y d f α hw) hf

theorem wt_hatPart (d : ℕ) (f : MvPowerSeries σ ℝ) (α : σ →₀ ℕ) (hy : 0 < w y) :
    wt w (hatPart y d f) α = wt w f (α + Finsupp.single y d) / w y ^ d := by
  unfold wt
  rw [coeff_hatPart, mw_add, mw_single]
  field_simp

theorem Conv.hat (hw : ∀ i, 0 ≤ w i) (hy : 0 < w y) (d : ℕ) {f : MvPowerSeries σ ℝ}
    (hf : Conv w f) : Conv w (hatPart y d f) := by
  have : wt w (hatPart y d f) = fun α => wt w f (α + Finsupp.single y d) / w y ^ d :=
    funext fun α => wt_hatPart y d f α hy
  rw [Conv, this]
  exact (hf.comp_injective (add_left_injective (Finsupp.single y d))).div_const _

theorem wn_hatPart_le (hw : ∀ i, 0 ≤ w i) (hy : 0 < w y) (d : ℕ) {f : MvPowerSeries σ ℝ}
    (hf : Conv w f) : wn w (hatPart y d f) ≤ wn w f / w y ^ d := by
  have : wt w (hatPart y d f) = fun α => wt w f (α + Finsupp.single y d) / w y ^ d :=
    funext fun α => wt_hatPart y d f α hy
  rw [wn, this, tsum_div_const]
  gcongr
  exact tsum_comp_le_tsum_of_inj hf (wt_nonneg hw f) (add_left_injective (Finsupp.single y d))

/-! ### the `x`-degree and `x`-order -/

/-- total degree in the variables other than `y`. -/
def xdeg (α : σ →₀ ℕ) : ℕ := ∑ i ∈ Finset.univ.erase y, α i

theorem xdeg_add (α β : σ →₀ ℕ) : xdeg y (α + β) = xdeg y α + xdeg y β := by
  simp [xdeg, Finset.sum_add_distrib]

theorem xdeg_single (d : ℕ) : xdeg y (Finsupp.single y d) = 0 := by
  unfold xdeg
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [Finsupp.single_apply, if_neg]
  exact fun h => (Finset.mem_erase.1 hi).1 h.symm

theorem eq_single_of_xdeg_eq_zero {α : σ →₀ ℕ} (h : xdeg y α = 0) :
    α = Finsupp.single y (α y) := by
  ext i
  by_cases hi : i = y
  · subst hi; simp
  · rw [Finsupp.single_apply, if_neg (Ne.symm hi)]
    exact (Finset.sum_eq_zero_iff.1 h) i (Finset.mem_erase.2 ⟨hi, Finset.mem_univ i⟩)

/-- all coefficients of `x`-degree `< m` vanish. -/
def XOrd (m : ℕ) (f : MvPowerSeries σ ℝ) : Prop := ∀ α, xdeg y α < m → coeff α f = 0

theorem XOrd.zero_ord (f : MvPowerSeries σ ℝ) : XOrd y 0 f := fun α h => absurd h (Nat.not_lt_zero _)

theorem XOrd.mono {m m' : ℕ} {f : MvPowerSeries σ ℝ} (hf : XOrd y m f) (h : m' ≤ m) :
    XOrd y m' f := fun α hα => hf α (lt_of_lt_of_le hα h)

theorem XOrd.add {m : ℕ} {f g : MvPowerSeries σ ℝ} (hf : XOrd y m f) (hg : XOrd y m g) :
    XOrd y m (f + g) := fun α hα => by rw [map_add, hf α hα, hg α hα, add_zero]

theorem XOrd.neg {m : ℕ} {f : MvPowerSeries σ ℝ} (hf : XOrd y m f) : XOrd y m (-f) :=
  fun α hα => by rw [map_neg, hf α hα, neg_zero]

theorem XOrd.sub {m : ℕ} {f g : MvPowerSeries σ ℝ} (hf : XOrd y m f) (hg : XOrd y m g) :
    XOrd y m (f - g) := fun α hα => by rw [map_sub, hf α hα, hg α hα, sub_zero]

theorem XOrd.zero (m : ℕ) : XOrd y m (0 : MvPowerSeries σ ℝ) := fun α _ => by simp

theorem XOrd.mul {m n : ℕ} {f g : MvPowerSeries σ ℝ} (hf : XOrd y m f) (hg : XOrd y n g) :
    XOrd y (m + n) (f * g) := fun α hα => by
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have : xdeg y p.1 + xdeg y p.2 < m + n := by rw [← xdeg_add, hp]; exact hα
  by_cases h1 : xdeg y p.1 < m
  · rw [hf _ h1, zero_mul]
  · rw [hg _ (by omega), mul_zero]

theorem XOrd.hat {m : ℕ} (d : ℕ) {f : MvPowerSeries σ ℝ} (hf : XOrd y m f) :
    XOrd y m (hatPart y d f) := fun α hα => by
  rw [coeff_hatPart]; exact hf _ (by rw [xdeg_add, xdeg_single, add_zero]; exact hα)

/-- the low part of a series regular of order `d` in `y` has positive `x`-order. -/
theorem XOrd.lowPart_of_regular (d : ℕ) {f : MvPowerSeries σ ℝ}
    (hreg : ∀ j < d, coeff (Finsupp.single y j) f = 0) : XOrd y 1 (lowPart y d f) := by
  intro α hα
  rw [coeff_lowPart]
  split_ifs with h
  · rw [eq_single_of_xdeg_eq_zero y (by omega : xdeg y α = 0)]
    exact hreg _ h
  · rfl

end Split

end SubanalyticLib

/-! SubanalyticLib L2b (body; prepend L12.lean): **convergent Weierstrass division**.
Neumann series `W = Σ_k (-T)^k ĝ`, `T v = hatPart d (v*h)`, `h = u⁻¹ * lowPart d f`; it is
coefficientwise finite because `T` raises the `x`-order, and converges by `conv_of_approx`. -/

namespace SubanalyticLib

section Div

open MvPowerSeries

variable {σ : Type*} [Fintype σ] [DecidableEq σ] (y : σ)

/-- `v ↦ -(hatPart d (v*h))`. -/
noncomputable def divOp (d : ℕ) (h v : MvPowerSeries σ ℝ) : MvPowerSeries σ ℝ :=
  -(hatPart y d (v * h))

/-- Neumann terms. -/
noncomputable def nterm (d : ℕ) (h g0 : MvPowerSeries σ ℝ) (k : ℕ) : MvPowerSeries σ ℝ :=
  (divOp y d h)^[k] g0

/-- Neumann partial sums. -/
noncomputable def npart (d : ℕ) (h g0 : MvPowerSeries σ ℝ) (N : ℕ) : MvPowerSeries σ ℝ :=
  ∑ k ∈ Finset.range N, nterm y d h g0 k

/-- the Neumann solution, read coefficientwise from a long enough partial sum. -/
noncomputable def nsol (d : ℕ) (h g0 : MvPowerSeries σ ℝ) : MvPowerSeries σ ℝ :=
  fun α => coeff α (npart y d h g0 (xdeg y α + 1))

theorem nterm_zero (d : ℕ) (h g0 : MvPowerSeries σ ℝ) : nterm y d h g0 0 = g0 := rfl

theorem nterm_succ (d : ℕ) (h g0 : MvPowerSeries σ ℝ) (k : ℕ) :
    nterm y d h g0 (k + 1) = divOp y d h (nterm y d h g0 k) :=
  Function.iterate_succ_apply' _ _ _

theorem divOp_sub (d : ℕ) (h a b : MvPowerSeries σ ℝ) :
    divOp y d h a - divOp y d h b = divOp y d h (a - b) := by
  simp only [divOp, sub_mul, hatPart_sub]; ring

theorem divOp_finset_sum (d : ℕ) (h : MvPowerSeries σ ℝ) {ι : Type*} (s : Finset ι)
    (F : ι → MvPowerSeries σ ℝ) : divOp y d h (∑ i ∈ s, F i) = ∑ i ∈ s, divOp y d h (F i) := by
  simp only [divOp, Finset.sum_mul, hatPart_finset_sum, Finset.sum_neg_distrib]

theorem XOrd.divOp {d m : ℕ} {h v : MvPowerSeries σ ℝ} (hh : XOrd y 1 h) (hv : XOrd y m v) :
    XOrd y (m + 1) (divOp y d h v) :=
  (XOrd.hat y d (XOrd.mul y hv hh)).neg y

theorem XOrd_nterm (d : ℕ) {h : MvPowerSeries σ ℝ} (hh : XOrd y 1 h) (g0 : MvPowerSeries σ ℝ) :
    ∀ k, XOrd y k (nterm y d h g0 k)
  | 0 => XOrd.zero_ord y _
  | k + 1 => by rw [nterm_succ]; exact XOrd.divOp y hh (XOrd_nterm d hh g0 k)

variable {w : σ → ℝ}

theorem conv_divOp (hw : ∀ i, 0 ≤ w i) (hy : 0 < w y) (d : ℕ) {h v : MvPowerSeries σ ℝ}
    (hh : Conv w h) (hv : Conv w v) :
    Conv w (divOp y d h v) ∧ wn w (divOp y d h v) ≤ wn w h / w y ^ d * wn w v := by
  have hvh : Conv w (v * h) := Conv.mul hw hv hh
  refine ⟨Conv.neg (Conv.hat y hw hy d hvh), ?_⟩
  rw [divOp, wn_neg]
  calc wn w (hatPart y d (v * h)) ≤ wn w (v * h) / w y ^ d := wn_hatPart_le y hw hy d hvh
    _ ≤ wn w v * wn w h / w y ^ d := by
        gcongr; exact wn_mul_le hw hv hh
    _ = wn w h / w y ^ d * wn w v := by ring

theorem conv_nterm (hw : ∀ i, 0 ≤ w i) (hy : 0 < w y) (d : ℕ) {h g0 : MvPowerSeries σ ℝ}
    (hh : Conv w h) (hg : Conv w g0) :
    ∀ k, Conv w (nterm y d h g0 k) ∧
      wn w (nterm y d h g0 k) ≤ (wn w h / w y ^ d) ^ k * wn w g0
  | 0 => by simp only [nterm_zero, pow_zero, one_mul]; exact ⟨hg, le_rfl⟩
  | k + 1 => by
    obtain ⟨hc, hb⟩ := conv_nterm hw hy d hh hg k
    obtain ⟨hc', hb'⟩ := conv_divOp y hw hy d hh hc
    rw [nterm_succ]
    refine ⟨hc', hb'.trans ?_⟩
    rw [pow_succ]
    have hθ : 0 ≤ wn w h / w y ^ d := div_nonneg (wn_nonneg hw h) (pow_nonneg hy.le d)
    calc wn w h / w y ^ d * wn w (nterm y d h g0 k)
        ≤ wn w h / w y ^ d * ((wn w h / w y ^ d) ^ k * wn w g0) :=
          mul_le_mul_of_nonneg_left hb hθ
      _ = (wn w h / w y ^ d) ^ k * (wn w h / w y ^ d) * wn w g0 := by ring

theorem coeff_npart_stable (d : ℕ) {h : MvPowerSeries σ ℝ} (hh : XOrd y 1 h)
    (g0 : MvPowerSeries σ ℝ) (α : σ →₀ ℕ) :
    ∀ N, xdeg y α + 1 ≤ N →
      coeff α (npart y d h g0 N) = coeff α (npart y d h g0 (xdeg y α + 1)) := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => rfl
  | succ N hN ih =>
    rw [npart, Finset.sum_range_succ, map_add, ← npart, ih,
      XOrd_nterm y d hh g0 N α (by omega), add_zero]

theorem coeff_nsol (d : ℕ) {h : MvPowerSeries σ ℝ} (hh : XOrd y 1 h) (g0 : MvPowerSeries σ ℝ)
    (α : σ →₀ ℕ) (N : ℕ) (hN : xdeg y α + 1 ≤ N) :
    coeff α (nsol y d h g0) = coeff α (npart y d h g0 N) :=
  (coeff_npart_stable y d hh g0 α N hN).symm

theorem conv_nsol (hw : ∀ i, 0 ≤ w i) (hy : 0 < w y) (d : ℕ) {h g0 : MvPowerSeries σ ℝ}
    (hh : Conv w h) (hhx : XOrd y 1 h) (hg : Conv w g0) (hθ : wn w h / w y ^ d < 1) :
    Conv w (nsol y d h g0) ∧ wn w (nsol y d h g0) ≤ wn w g0 * (1 - wn w h / w y ^ d)⁻¹ := by
  have hθ0 : 0 ≤ wn w h / w y ^ d := div_nonneg (wn_nonneg hw h) (pow_nonneg hy.le d)
  have hP : ∀ N, Conv w (npart y d h g0 N) ∧
      wn w (npart y d h g0 N) ≤ ∑ k ∈ Finset.range N, wn w (nterm y d h g0 k) := fun N =>
    conv_finset_sum hw _ _ (fun k _ => (conv_nterm y hw hy d hh hg k).1)
  refine conv_of_approx hw (npart y d h g0) (fun α => xdeg y α + 1) (fun N => (hP N).1)
    (fun N => ?_) (fun α N hN => coeff_nsol y d hhx g0 α N hN)
  refine (hP N).2.trans ?_
  calc ∑ k ∈ Finset.range N, wn w (nterm y d h g0 k)
      ≤ ∑ k ∈ Finset.range N, (wn w h / w y ^ d) ^ k * wn w g0 :=
        Finset.sum_le_sum fun k _ => (conv_nterm y hw hy d hh hg k).2
    _ = wn w g0 * ∑ k ∈ Finset.range N, (wn w h / w y ^ d) ^ k := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ wn w g0 * (1 - wn w h / w y ^ d)⁻¹ :=
        mul_le_mul_of_nonneg_left
          (sum_le_hasSum _ (fun i _ => pow_nonneg hθ0 i) (hasSum_geometric_of_lt_one hθ0 hθ))
          (wn_nonneg hw g0)

/-- the Neumann solution solves `W + hatPart d (W*h) = g0`. -/
theorem nsol_fixed (d : ℕ) {h : MvPowerSeries σ ℝ} (hh : XOrd y 1 h) (g0 : MvPowerSeries σ ℝ) :
    nsol y d h g0 + hatPart y d (nsol y d h g0 * h) = g0 := by
  ext α
  set N := xdeg y α + 1 with hNdef
  have hX : XOrd y N (nsol y d h g0 - npart y d h g0 N) := by
    intro β hβ
    rw [map_sub, coeff_nsol y d hh g0 β N (by omega), sub_self]
  have h1 : coeff α (divOp y d h (nsol y d h g0)) = coeff α (divOp y d h (npart y d h g0 N)) := by
    have := XOrd.divOp y (d := d) hh hX α (by omega)
    rw [← divOp_sub, map_sub, sub_eq_zero] at this
    exact this
  have h2 : npart y d h g0 N - divOp y d h (npart y d h g0 N) = g0 - nterm y d h g0 N := by
    rw [npart, divOp_finset_sum]
    simp_rw [← nterm_succ]
    rw [← Finset.sum_sub_distrib, Finset.sum_range_sub', nterm_zero]
  have h3 : coeff α (nterm y d h g0 N) = 0 := XOrd_nterm y d hh g0 N α (by omega)
  have key : coeff α (nsol y d h g0 - divOp y d h (nsol y d h g0)) = coeff α g0 := by
    rw [map_sub, h1, coeff_nsol y d hh g0 α N le_rfl, ← map_sub, h2, map_sub, h3, sub_zero]
  rw [divOp, sub_neg_eq_add] at key
  exact key

/-- **Convergent Weierstrass division** (polyradius form).  If `f` is regular of order `d` in `y`
and the polyradius `w` is small enough that `u = hatPart d f` has a convergent inverse and
`‖u⁻¹ * lowPart d f‖_w < w_y^d`, then every convergent `g` is `q*f + r` with `q, r`
convergent and `r` of `y`-degree `< d`. -/
theorem weierstrass_div_conv (hw : ∀ i, 0 ≤ w i) (hy : 0 < w y) (d : ℕ)
    {f g : MvPowerSeries σ ℝ} (hf : Conv w f) (hg : Conv w g)
    (hreg : ∀ j < d, coeff (Finsupp.single y j) f = 0)
    (hd : coeff (Finsupp.single y d) f ≠ 0) (hu : Conv w (hatPart y d f)⁻¹)
    (hθ : wn w ((hatPart y d f)⁻¹ * lowPart y d f) < w y ^ d) :
    ∃ q r : MvPowerSeries σ ℝ, Conv w q ∧ Conv w r ∧ hatPart y d r = 0 ∧ g = q * f + r := by
  set u := hatPart y d f with hudef
  set h := u⁻¹ * lowPart y d f with hhdef
  have hcu : constantCoeff u ≠ 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, hudef, coeff_hatPart, zero_add]; exact hd
  have hh : Conv w h := Conv.mul hw hu (Conv.low y hw d hf)
  have hhx : XOrd y 1 h := by
    have := XOrd.mul y (XOrd.zero_ord y u⁻¹) (XOrd.lowPart_of_regular y d hreg)
    rw [zero_add] at this; exact this
  have hθ' : wn w h / w y ^ d < 1 := by
    rw [div_lt_one (pow_pos hy d)]; exact hθ
  set W := nsol y d h (hatPart y d g) with hWdef
  have hW := conv_nsol y hw hy d hh hhx (Conv.hat y hw hy d hg) hθ'
  refine ⟨W * u⁻¹, g - W * u⁻¹ * f, Conv.mul hw hW.1 hu,
    Conv.sub hw hg (Conv.mul hw (Conv.mul hw hW.1 hu) hf), ?_, by ring⟩
  have hqf : W * u⁻¹ * f = W * h + X y ^ d * W := by
    conv_lhs => rw [low_add_hat y d f]
    rw [← hudef, hhdef]
    have : u⁻¹ * u = 1 := MvPowerSeries.inv_mul_cancel u hcu
    calc W * u⁻¹ * (lowPart y d f + X y ^ d * u)
        = W * (u⁻¹ * lowPart y d f) + X y ^ d * W * (u⁻¹ * u) := by ring
      _ = W * (u⁻¹ * lowPart y d f) + X y ^ d * W := by rw [this, mul_one]
  have hfix : W + hatPart y d (W * h) = hatPart y d g := nsol_fixed y d hhx _
  rw [hatPart_sub, hqf, hatPart_add, hatPart_X_pow_mul, ← hfix]
  ring

end Div

end SubanalyticLib

/-! SubanalyticLib L2c (body; prepend L2.lean): choosing the polyradius for Weierstrass division. -/

namespace SubanalyticLib

section Radius

open MvPowerSeries

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- scale the radii indexed by `S` by the factor `τ`. -/
noncomputable def scaleW (S : Finset σ) (τ : ℝ) (w : σ → ℝ) (i : σ) : ℝ :=
  if i ∈ S then τ * w i else w i

/-- partial degree in the variables of `S`. -/
def sdeg (S : Finset σ) (α : σ →₀ ℕ) : ℕ := ∑ i ∈ S, α i

theorem mw_scaleW (S : Finset σ) (τ : ℝ) (w : σ → ℝ) (α : σ →₀ ℕ) :
    mw (scaleW S τ w) α = τ ^ sdeg S α * mw w α := by
  unfold mw scaleW sdeg
  have : ∀ i ∈ (Finset.univ : Finset σ),
      (if i ∈ S then τ * w i else w i) ^ α i = (if i ∈ S then τ ^ α i else 1) * w i ^ α i := by
    intro i _; split_ifs <;> simp [mul_pow]
  rw [Finset.prod_congr rfl this, Finset.prod_mul_distrib, Finset.prod_ite_mem,
    Finset.univ_inter, Finset.prod_pow_eq_pow_sum]

theorem scaleW_le {S : Finset σ} {τ : ℝ} {w : σ → ℝ} (hw : ∀ i, 0 ≤ w i) (hτ : τ ≤ 1) (i : σ) :
    scaleW S τ w i ≤ w i := by
  unfold scaleW; split_ifs
  · exact mul_le_of_le_one_left (hw i) hτ
  · exact le_rfl

theorem conv_scale {w : σ → ℝ} (hw : ∀ i, 0 ≤ w i) (S : Finset σ) {τ : ℝ} (hτ0 : 0 ≤ τ)
    (hτ1 : τ ≤ 1) {f : MvPowerSeries σ ℝ} (hf : Conv w f)
    (hz : ∀ α, sdeg S α = 0 → coeff α f = 0) :
    Conv (scaleW S τ w) f ∧ wn (scaleW S τ w) f ≤ τ * wn w f := by
  have hnn : ∀ i, 0 ≤ scaleW S τ w i := fun i => by
    unfold scaleW; split_ifs
    · exact mul_nonneg hτ0 (hw i)
    · exact hw i
  have hle : ∀ α, wt (scaleW S τ w) f α ≤ τ * wt w f α := by
    intro α
    unfold wt; rw [mw_scaleW]
    by_cases h : sdeg S α = 0
    · rw [hz α h]; simp
    · calc |coeff α f| * (τ ^ sdeg S α * mw w α) ≤ |coeff α f| * (τ * mw w α) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (pow_le_of_le_one hτ0 hτ1 h) (mw_nonneg hw α))
              (abs_nonneg _)
        _ = τ * (|coeff α f| * mw w α) := by ring
  have hc : Conv (scaleW S τ w) f :=
    Summable.of_nonneg_of_le (wt_nonneg hnn f) hle (hf.mul_left τ)
  exact ⟨hc, hasSum_le hle hc.hasSum (hf.hasSum.mul_left τ)⟩

/-- **radius choice**: a series regular of order `d` in `y`, convergent on some polydisc, satisfies
the hypotheses of `weierstrass_div_conv` on a smaller polydisc. -/
theorem exists_radius_div (y : σ) {w0 : σ → ℝ} (hw0 : ∀ i, 0 < w0 i) (d : ℕ)
    {f : MvPowerSeries σ ℝ} (hf : Conv w0 f) (hreg : ∀ j < d, coeff (Finsupp.single y j) f = 0)
    (hd : coeff (Finsupp.single y d) f ≠ 0) :
    ∃ w : σ → ℝ, (∀ i, 0 < w i) ∧ (∀ i, w i ≤ w0 i) ∧ Conv w (hatPart y d f)⁻¹ ∧
      wn w ((hatPart y d f)⁻¹ * lowPart y d f) < w y ^ d := by
  have hw0' : ∀ i, 0 ≤ w0 i := fun i => (hw0 i).le
  set u := hatPart y d f with hudef
  have hu0 : Conv w0 u := Conv.hat y hw0' (hw0 y) d hf
  set c := constantCoeff u with hcdef
  have hc : c ≠ 0 := by
    rw [hcdef, ← coeff_zero_eq_constantCoeff_apply, hudef, coeff_hatPart, zero_add]; exact hd
  have hcpos : 0 < |c| := abs_pos.2 hc
  set A := wn w0 (u - C c) with hAdef
  have hA : 0 ≤ A := wn_nonneg hw0' _
  set t := min 1 (|c| / (2 * (A + 1))) with htdef
  have ht0 : 0 < t := lt_min one_pos (div_pos hcpos (by linarith))
  have ht1 : t ≤ 1 := min_le_left _ _
  have htA : t * A ≤ 1 / 2 * |c| := by
    have : t ≤ |c| / (2 * (A + 1)) := min_le_right _ _
    calc t * A ≤ |c| / (2 * (A + 1)) * A := mul_le_mul_of_nonneg_right this hA
      _ ≤ 1 / 2 * |c| := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]; nlinarith
  set w1 := scaleW Finset.univ t w0 with hw1def
  have hw1pos : ∀ i, 0 < w1 i := fun i => by
    simp only [hw1def, scaleW, Finset.mem_univ, if_true]; exact mul_pos ht0 (hw0 i)
  have hw1' : ∀ i, 0 ≤ w1 i := fun i => (hw1pos i).le
  have hw1le : ∀ i, w1 i ≤ w0 i := fun i => scaleW_le hw0' ht1 i
  have hv := conv_scale hw0' Finset.univ ht0.le ht1 (Conv.sub hw0' hu0 (conv_C c)) (by
    intro α hα
    have h0 : α = 0 := by
      ext i
      have := (Finset.sum_eq_zero_iff.1 hα) i (Finset.mem_univ i)
      simpa using this
    subst h0
    simp [coeff_zero_eq_constantCoeff_apply, hcdef])
  have hu1 : Conv w1 u := Conv.mono hw1' hw1le hu0
  obtain ⟨hinv, hinvB⟩ := conv_inv hw1' hu1 (q := 1 / 2) (by norm_num) (by norm_num) hc
    (hv.2.trans htA)
  set K := |c|⁻¹ * (1 - 1 / 2 : ℝ)⁻¹ with hKdef
  have hK : 0 ≤ K := by positivity
  have hlow1 : Conv w1 (lowPart y d f) := Conv.mono hw1' hw1le (Conv.low y hw0' d hf)
  set L := wn w1 (lowPart y d f) with hLdef
  have hL : 0 ≤ L := wn_nonneg hw1' _
  set s := w1 y with hsdef
  have hs : 0 < s := hw1pos y
  have hKL : 0 ≤ K * L := mul_nonneg hK hL
  set τ := min 1 (s ^ d / (2 * (K * L + 1))) with hτdef
  have hτ0 : 0 < τ := lt_min one_pos (div_pos (pow_pos hs d) (by linarith))
  have hτ1 : τ ≤ 1 := min_le_left _ _
  set w2 := scaleW (Finset.univ.erase y) τ w1 with hw2def
  have hw2pos : ∀ i, 0 < w2 i := fun i => by
    simp only [hw2def, scaleW]; split_ifs
    · exact mul_pos hτ0 (hw1pos i)
    · exact hw1pos i
  have hw2' : ∀ i, 0 ≤ w2 i := fun i => (hw2pos i).le
  have hw2le : ∀ i, w2 i ≤ w1 i := fun i => scaleW_le hw1' hτ1 i
  have hw2y : w2 y = s := by simp [hw2def, scaleW, hsdef]
  have hlow2 := conv_scale hw1' (Finset.univ.erase y) hτ0.le hτ1 hlow1
    (fun α hα => XOrd.lowPart_of_regular y d hreg α (by
      have : xdeg y α = 0 := hα
      omega))
  have hinv2 : Conv w2 u⁻¹ := Conv.mono hw2' hw2le hinv
  have hinv2B : wn w2 u⁻¹ ≤ K := (wn_mono hw2' hw2le hinv).trans hinvB
  refine ⟨w2, hw2pos, fun i => (hw2le i).trans (hw1le i), hinv2, ?_⟩
  rw [hw2y]
  have hsd : 0 < s ^ d := pow_pos hs d
  have h1 : τ ≤ s ^ d / (2 * (K * L + 1)) := min_le_right _ _
  have h2 : K * (τ * L) ≤ K * L * (s ^ d / (2 * (K * L + 1))) := by
    have := mul_le_mul_of_nonneg_left h1 hKL; nlinarith
  have h3 : K * L * (s ^ d / (2 * (K * L + 1))) < s ^ d := by
    rw [mul_div_assoc', div_lt_iff₀ (by linarith)]; nlinarith
  calc wn w2 (u⁻¹ * lowPart y d f) ≤ wn w2 u⁻¹ * wn w2 (lowPart y d f) :=
        wn_mul_le hw2' hinv2 hlow2.1
    _ ≤ K * (τ * L) := mul_le_mul hinv2B hlow2.2 (wn_nonneg hw2' _) hK
    _ < s ^ d := lt_of_le_of_lt h2 h3

end Radius

end SubanalyticLib

/-! SubanalyticLib L2d (body; prepend L2R.lean): convergent Weierstrass division (clean form) and
**convergent Weierstrass preparation** `X_y^d = q*f + r`, `q` a unit, `r` of `y`-degree `< d`
with `r(0,y) = 0`. -/

namespace SubanalyticLib

section Prep

open MvPowerSeries

variable {σ : Type*} [Fintype σ] [DecidableEq σ] (y : σ)

/-- **Weierstrass division, convergent form**. -/
theorem weierstrass_division (y : σ) {w0 : σ → ℝ} (hw0 : ∀ i, 0 < w0 i) (d : ℕ)
    {f : MvPowerSeries σ ℝ} (hf : Conv w0 f) (hreg : ∀ j < d, coeff (Finsupp.single y j) f = 0)
    (hd : coeff (Finsupp.single y d) f ≠ 0) :
    ∃ w : σ → ℝ, (∀ i, 0 < w i) ∧ (∀ i, w i ≤ w0 i) ∧
      ∀ g : MvPowerSeries σ ℝ, Conv w g →
        ∃ q r : MvPowerSeries σ ℝ, Conv w q ∧ Conv w r ∧ hatPart y d r = 0 ∧ g = q * f + r := by
  obtain ⟨w, hwpos, hwle, hu, hθ⟩ := exists_radius_div y hw0 d hf hreg hd
  have hw' : ∀ i, 0 ≤ w i := fun i => (hwpos i).le
  exact ⟨w, hwpos, hwle, fun g hg =>
    weierstrass_div_conv y hw' (hwpos y) d (Conv.mono hw' hwle hf) hg hreg hd hu hθ⟩

theorem eq_single_of_le_single {γ : σ →₀ ℕ} {j : ℕ} (h : γ ≤ Finsupp.single y j) :
    γ = Finsupp.single y (γ y) := by
  ext i
  by_cases hi : i = y
  · subst hi; simp
  · have := Finsupp.le_def.1 h i
    rw [Finsupp.single_apply, if_neg (Ne.symm hi)] at this ⊢
    omega

/-- pure-`y` coefficients of `q*f` for `f` regular of order `d` in `y`. -/
theorem coeff_single_mul_regular (d : ℕ) {q f : MvPowerSeries σ ℝ}
    (hreg : ∀ j < d, coeff (Finsupp.single y j) f = 0) (j : ℕ) (hj : j ≤ d) :
    coeff (Finsupp.single y j) (q * f) =
      if j = d then constantCoeff q * coeff (Finsupp.single y d) f else 0 := by
  rw [coeff_mul]
  have hterm : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal (Finsupp.single y j),
      p ≠ (0, Finsupp.single y j) → coeff p.1 q * coeff p.2 f = 0 := by
    intro p hp hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have hle : p.2 ≤ Finsupp.single y j := hp ▸ le_add_self
    have h2 := eq_single_of_le_single y hle
    have hk : p.2 y ≤ j := by have := Finsupp.le_def.1 hle y; simpa using this
    by_cases hk' : p.2 y < d
    · rw [h2, hreg _ hk', mul_zero]
    · exfalso; apply hne
      have hpj : p.2 = Finsupp.single y j := by rw [h2]; congr 1; omega
      have hp1 : p.1 = 0 := by
        rw [hpj] at hp; exact add_right_cancel (hp.trans (zero_add _).symm)
      exact Prod.ext hp1 hpj
  rw [Finset.sum_eq_single (0, Finsupp.single y j) hterm
    (fun h => absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (zero_add _)) h)]
  dsimp only
  rw [coeff_zero_eq_constantCoeff_apply]
  split_ifs with hjd
  · subst hjd; rfl
  · rw [hreg j (lt_of_le_of_ne hj hjd), mul_zero]

/-- **Weierstrass preparation, convergent form**: `X_y^d = q*f + r` with `q` a unit and
`r` a polynomial in `y` of degree `< d` whose coefficients vanish at `x = 0`. -/
theorem weierstrass_prep (y : σ) {w0 : σ → ℝ} (hw0 : ∀ i, 0 < w0 i) (d : ℕ)
    {f : MvPowerSeries σ ℝ} (hf : Conv w0 f) (hreg : ∀ j < d, coeff (Finsupp.single y j) f = 0)
    (hd : coeff (Finsupp.single y d) f ≠ 0) :
    ∃ w : σ → ℝ, (∀ i, 0 < w i) ∧ (∀ i, w i ≤ w0 i) ∧
      ∃ q r : MvPowerSeries σ ℝ, Conv w q ∧ Conv w r ∧ hatPart y d r = 0 ∧
        constantCoeff q ≠ 0 ∧ (∀ j < d, coeff (Finsupp.single y j) r = 0) ∧
        X y ^ d = q * f + r := by
  obtain ⟨w, hwpos, hwle, hdiv⟩ := weierstrass_division y hw0 d hf hreg hd
  have hw' : ∀ i, 0 ≤ w i := fun i => (hwpos i).le
  obtain ⟨q, r, hq, hr, hr0, heq⟩ := hdiv (X y ^ d) (Conv.pow hw' (conv_X hw' y) d)
  refine ⟨w, hwpos, hwle, q, r, hq, hr, hr0, ?_, ?_, heq⟩
  · have h := congrArg (coeff (Finsupp.single y d)) heq
    rw [map_add, coeff_single_mul_regular y d hreg d le_rfl, if_pos rfl] at h
    have hrd : coeff (Finsupp.single y d) r = 0 := by
      have := congrArg (coeff (Finsupp.single y d)) ((lowPart_eq_self_iff y d r).2 hr0)
      rw [coeff_lowPart, if_neg (by simp)] at this; exact this.symm
    rw [hrd, add_zero, X_pow_eq, coeff_monomial_same] at h
    intro hq0; rw [hq0, zero_mul] at h; exact one_ne_zero h
  · intro j hj
    have h := congrArg (coeff (Finsupp.single y j)) heq
    rw [map_add, coeff_single_mul_regular y d hreg j hj.le, if_neg hj.ne, zero_add, X_pow_eq,
      coeff_monomial, if_neg] at h
    · exact h.symm
    · intro he
      exact absurd (by simpa using congrArg (fun z => z y) he) hj.ne

end Prep

end SubanalyticLib

/-! SubanalyticLib L1b (body; prepend L2P.lean or L1_Conv.lean): evaluating convergent power series
on the closed polydisc; `ev` is a ring homomorphism there. -/

namespace SubanalyticLib

section Eval

open MvPowerSeries

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- the monomial `x^α`. -/
def mon (x : σ → ℝ) (α : σ →₀ ℕ) : ℝ := ∏ i, x i ^ α i

/-- evaluation of a power series (meaningful where it converges absolutely). -/
noncomputable def ev (f : MvPowerSeries σ ℝ) (x : σ → ℝ) : ℝ := ∑' α, coeff α f * mon x α

theorem mon_add (x : σ → ℝ) (α β : σ →₀ ℕ) : mon x (α + β) = mon x α * mon x β := by
  simp [mon, pow_add, Finset.prod_mul_distrib]

theorem mon_zero (x : σ → ℝ) : mon x 0 = 1 := by simp [mon]

theorem mon_single (x : σ → ℝ) (i : σ) (k : ℕ) : mon x (Finsupp.single i k) = x i ^ k := by
  unfold mon
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj; simp [Ne.symm hj]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem abs_mon_le {w x : σ → ℝ} (hx : ∀ i, |x i| ≤ w i) (α : σ →₀ ℕ) : |mon x α| ≤ mw w α := by
  unfold mon mw
  rw [Finset.abs_prod]
  exact Finset.prod_le_prod (fun i _ => abs_nonneg _)
    (fun i _ => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hx i) _)

variable {w : σ → ℝ}

theorem norm_term_le {x : σ → ℝ} (hx : ∀ i, |x i| ≤ w i) (f : MvPowerSeries σ ℝ) (α : σ →₀ ℕ) :
    ‖coeff α f * mon x α‖ ≤ wt w f α := by
  rw [Real.norm_eq_abs, abs_mul, wt]
  exact mul_le_mul_of_nonneg_left (abs_mon_le hx α) (abs_nonneg _)

theorem summable_norm_term {x : σ → ℝ} (hx : ∀ i, |x i| ≤ w i) {f : MvPowerSeries σ ℝ}
    (hf : Conv w f) : Summable fun α => ‖coeff α f * mon x α‖ :=
  Summable.of_nonneg_of_le (fun α => norm_nonneg _) (norm_term_le hx f) hf

theorem summable_term {x : σ → ℝ} (hx : ∀ i, |x i| ≤ w i) {f : MvPowerSeries σ ℝ}
    (hf : Conv w f) : Summable fun α => coeff α f * mon x α :=
  (summable_norm_term hx hf).of_norm

theorem abs_ev_le {x : σ → ℝ} (hx : ∀ i, |x i| ≤ w i) {f : MvPowerSeries σ ℝ} (hf : Conv w f) :
    |ev f x| ≤ wn w f := by
  rw [← Real.norm_eq_abs, ev, wn]
  exact (norm_tsum_le_tsum_norm (summable_norm_term hx hf)).trans
    (hasSum_le (norm_term_le hx f) (summable_norm_term hx hf).hasSum hf.hasSum)

theorem ev_add {x : σ → ℝ} (hx : ∀ i, |x i| ≤ w i) {f g : MvPowerSeries σ ℝ} (hf : Conv w f)
    (hg : Conv w g) : ev (f + g) x = ev f x + ev g x := by
  unfold ev
  rw [← ((summable_term hx hf).hasSum.add (summable_term hx hg).hasSum).tsum_eq]
  congr 1; funext α; rw [map_add, add_mul]

theorem ev_neg (f : MvPowerSeries σ ℝ) (x : σ → ℝ) : ev (-f) x = -ev f x := by
  unfold ev; rw [← tsum_neg]; congr 1; funext α; rw [map_neg, neg_mul]

theorem ev_sub {x : σ → ℝ} (hx : ∀ i, |x i| ≤ w i) {f g : MvPowerSeries σ ℝ} (hf : Conv w f)
    (hg : Conv w g) : ev (f - g) x = ev f x - ev g x := by
  rw [sub_eq_add_neg, ev_add hx hf (Conv.neg hg), ev_neg, ← sub_eq_add_neg]

theorem ev_C (a : ℝ) (x : σ → ℝ) : ev (C a : MvPowerSeries σ ℝ) x = a := by
  unfold ev
  rw [tsum_eq_single 0 (fun β hβ => by simp [coeff_C, hβ])]
  simp [coeff_C, mon_zero]

theorem ev_one (x : σ → ℝ) : ev (1 : MvPowerSeries σ ℝ) x = 1 := by
  simpa using ev_C (σ := σ) 1 x

theorem ev_X (i : σ) (x : σ → ℝ) : ev (X i : MvPowerSeries σ ℝ) x = x i := by
  unfold ev
  rw [tsum_eq_single (Finsupp.single i 1) (fun β hβ => by simp [coeff_X, hβ])]
  simp [coeff_X, mon_single]

theorem ev_mul {x : σ → ℝ} (hx : ∀ i, |x i| ≤ w i) (hw : ∀ i, 0 ≤ w i)
    {f g : MvPowerSeries σ ℝ} (hf : Conv w f) (hg : Conv w g) :
    ev (f * g) x = ev f x * ev g x := by
  have h1 : Summable (fun α => coeff α f * mon x α) := summable_term hx hf
  have h2 : Summable (fun α => coeff α g * mon x α) := summable_term hx hg
  have h12 : Summable (fun p : (σ →₀ ℕ) × (σ →₀ ℕ) =>
      (coeff p.1 f * mon x p.1) * (coeff p.2 g * mon x p.2)) :=
    summable_mul_of_summable_norm (f := fun α => coeff α f * mon x α)
      (g := fun α => coeff α g * mon x α) (summable_norm_term hx hf) (summable_norm_term hx hg)
  have key := Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal h1 h2 h12
  unfold ev
  rw [key]
  congr 1; funext γ
  rw [coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [← hp, mon_add]; ring

theorem ev_pow {x : σ → ℝ} (hx : ∀ i, |x i| ≤ w i) (hw : ∀ i, 0 ≤ w i)
    {f : MvPowerSeries σ ℝ} (hf : Conv w f) (n : ℕ) : ev (f ^ n) x = ev f x ^ n := by
  induction n with
  | zero => simp [ev_one]
  | succ n ih => rw [pow_succ, ev_mul hx hw (Conv.pow hw hf n) hf, ih, pow_succ]

theorem ev_zero_pt (f : MvPowerSeries σ ℝ) : ev f 0 = constantCoeff f := by
  unfold ev
  rw [tsum_eq_single 0]
  · simp [mon_zero, coeff_zero_eq_constantCoeff_apply]
  · intro β hβ
    obtain ⟨i, hi⟩ : ∃ i, β i ≠ 0 := by
      by_contra h; exact hβ (Finsupp.ext fun i => by simpa using not_exists.1 h i)
    have : mon (0 : σ → ℝ) β = 0 := by
      unfold mon
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
    rw [this, mul_zero]

end Eval

end SubanalyticLib
/-! SubanalyticLib L1c (body; prepend L2E.lean minus its last line, or L1_Conv + L1_Eval.body):
bridge A.  A power series converging absolutely on the closed polydisc of polyradius `w` defines,
through `ev`, a function with an explicit formal multilinear series on the sup-norm ball of any
radius `r ≤ min w`; hence `ev f` is analytic near `0`. -/

namespace SubanalyticLib

section BridgeA

open MvPowerSeries

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- the exponent of the monomial `∏_j X (ι j)`. -/
noncomputable def mult {n : ℕ} (ι : Fin n → σ) : σ →₀ ℕ := ∑ j, Finsupp.single (ι j) 1

theorem degree_mult {n : ℕ} (ι : Fin n → σ) : Finsupp.degree (mult ι) = n := by
  simp [mult, map_sum]

theorem mult_cons {n : ℕ} (i : σ) (ι : Fin n → σ) :
    mult (Fin.cons i ι : Fin (n + 1) → σ) = Finsupp.single i 1 + mult ι := by
  simp [mult, Fin.sum_univ_succ]

theorem exists_mult : ∀ (n : ℕ) (α : σ →₀ ℕ), Finsupp.degree α = n →
    ∃ ι : Fin n → σ, mult ι = α := by
  intro n
  induction n with
  | zero =>
    intro α hα
    refine ⟨Fin.elim0, ?_⟩
    rw [(Finsupp.degree_eq_zero_iff α).1 hα]; simp [mult]
  | succ n ih =>
    intro α hα
    have hα0 : α ≠ 0 := by
      intro h; rw [h] at hα; simp at hα
    obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
      by_contra h; exact hα0 (Finsupp.ext fun j => by simpa using not_exists.1 h j)
    have hle : Finsupp.single i 1 ≤ α := by
      rw [Finsupp.single_le_iff]; omega
    have hsplit : α = Finsupp.single i 1 + (α - Finsupp.single i 1) := by
      rw [add_tsub_cancel_of_le hle]
    have hdeg : Finsupp.degree (α - Finsupp.single i 1) = n := by
      have := congrArg Finsupp.degree hsplit
      rw [map_add, Finsupp.degree_single] at this; omega
    obtain ⟨ι, hι⟩ := ih _ hdeg
    exact ⟨Fin.cons i ι, by rw [mult_cons, hι, ← hsplit]⟩

theorem mon_sum (x : σ → ℝ) {ι : Type*} (s : Finset ι) (a : ι → σ →₀ ℕ) :
    mon x (∑ j ∈ s, a j) = ∏ j ∈ s, mon x (a j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mon_zero]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, mon_add, ih]

theorem mw_sum (w : σ → ℝ) {ι : Type*} (s : Finset ι) (a : ι → σ →₀ ℕ) :
    mw w (∑ j ∈ s, a j) = ∏ j ∈ s, mw w (a j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mw_zero]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, mw_add, ih]

theorem mon_mult (x : σ → ℝ) {n : ℕ} (ι : Fin n → σ) : mon x (mult ι) = ∏ j, x (ι j) := by
  rw [mult, mon_sum]; simp [mon_single]

theorem mw_mult (w : σ → ℝ) {n : ℕ} (ι : Fin n → σ) : mw w (mult ι) = ∏ j, w (ι j) := by
  rw [mult, mw_sum]; simp [mw_single]

/-- the exponents of total degree `n`. -/
noncomputable def degs (n : ℕ) : Finset (σ →₀ ℕ) := (Finset.univ : Finset (Fin n → σ)).image mult

theorem mem_degs {n : ℕ} {α : σ →₀ ℕ} : α ∈ degs n ↔ Finsupp.degree α = n := by
  constructor
  · intro h
    obtain ⟨ι, -, rfl⟩ := Finset.mem_image.1 h
    exact degree_mult ι
  · intro h
    obtain ⟨ι, hι⟩ := exists_mult n α h
    exact Finset.mem_image.2 ⟨ι, Finset.mem_univ _, hι⟩

/-- `ι` is the chosen representative of its exponent. -/
def Rep {n : ℕ} (ι : Fin n → σ) : Prop :=
  (⟨ι, rfl⟩ : ∃ ι' : Fin n → σ, mult ι' = mult ι).choose = ι

/-- the chosen representatives. -/
noncomputable def reps (n : ℕ) : Finset (Fin n → σ) := by
  classical exact (Finset.univ : Finset (Fin n → σ)).filter Rep

theorem choose_congr {n : ℕ} {a b : σ →₀ ℕ} (ha : ∃ ι' : Fin n → σ, mult ι' = a)
    (hb : ∃ ι' : Fin n → σ, mult ι' = b) (hab : a = b) : ha.choose = hb.choose := by
  subst hab; rfl

theorem mem_reps {n : ℕ} {ι : Fin n → σ} : ι ∈ reps n ↔ Rep ι := by
  classical
  unfold reps
  simp

theorem sum_reps {n : ℕ} (g : (σ →₀ ℕ) → ℝ) :
    ∑ ι ∈ reps n, g (mult ι) = ∑ α ∈ degs n, g α := by
  classical
  have himg : (reps n).image mult = degs (σ := σ) n := by
    apply Finset.Subset.antisymm
    · intro α hα
      obtain ⟨ι, -, rfl⟩ := Finset.mem_image.1 hα
      exact Finset.mem_image.2 ⟨ι, Finset.mem_univ _, rfl⟩
    · intro α hα
      obtain ⟨ι, -, rfl⟩ := Finset.mem_image.1 hα
      set h0 : ∃ ι' : Fin n → σ, mult ι' = mult ι := ⟨ι, rfl⟩
      have hspec : mult h0.choose = mult ι := h0.choose_spec
      refine Finset.mem_image.2 ⟨h0.choose, mem_reps.2 ?_, hspec⟩
      unfold Rep
      exact choose_congr _ h0 hspec
  rw [← himg, Finset.sum_image]
  intro ι1 h1 ι2 h2 h12
  have r1 := mem_reps.1 h1
  have r2 := mem_reps.1 h2
  unfold Rep at r1 r2
  rw [← r1, ← r2]
  exact choose_congr _ _ h12

/-- the monomial multilinear map `m ↦ ∏_j m_j (ι j)`. -/
noncomputable def pmono {n : ℕ} (ι : Fin n → σ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => σ → ℝ) ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compContinuousLinearMap
    (fun j => ContinuousLinearMap.proj (ι j))

theorem pmono_apply {n : ℕ} (ι : Fin n → σ) (m : Fin n → σ → ℝ) :
    pmono ι m = ∏ j, m j (ι j) := by
  simp [pmono]

theorem norm_pmono_le {n : ℕ} (ι : Fin n → σ) : ‖pmono ι‖ ≤ 1 := by
  refine ContinuousMultilinearMap.opNorm_le_bound zero_le_one fun m => ?_
  rw [pmono_apply, one_mul, norm_prod]
  exact Finset.prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => norm_le_pi_norm (m j) (ι j))

/-- the formal multilinear series of `ev f` at `0`. -/
noncomputable def ps (f : MvPowerSeries σ ℝ) : FormalMultilinearSeries ℝ (σ → ℝ) ℝ :=
  fun n => ∑ ι ∈ reps n, coeff (mult ι) f • pmono ι

theorem ps_diag (f : MvPowerSeries σ ℝ) (n : ℕ) (y : σ → ℝ) :
    ps f n (fun _ => y) = ∑ α ∈ degs n, coeff α f * mon y α := by
  rw [ps, ContinuousMultilinearMap.sum_apply]
  simp_rw [ContinuousMultilinearMap.smul_apply, pmono_apply, smul_eq_mul]
  rw [← sum_reps (fun α => coeff α f * mon y α)]
  refine Finset.sum_congr rfl fun ι _ => ?_
  rw [mon_mult]

theorem norm_ps_le (f : MvPowerSeries σ ℝ) (n : ℕ) :
    ‖ps f n‖ ≤ ∑ α ∈ degs n, |coeff α f| := by
  rw [← sum_reps (fun α => |coeff α f|)]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ι _ => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (norm_pmono_le ι) (abs_nonneg _)).trans (le_of_eq (mul_one _))

theorem pow_le_mw {w : σ → ℝ} {r : ℝ} (hr : 0 ≤ r) (hrw : ∀ i, r ≤ w i) {n : ℕ} {α : σ →₀ ℕ}
    (hα : α ∈ degs n) : r ^ n ≤ mw w α := by
  obtain ⟨ι, -, rfl⟩ := Finset.mem_image.1 hα
  rw [mw_mult]
  calc r ^ n = ∏ _j : Fin n, r := by simp
    _ ≤ ∏ j, w (ι j) := Finset.prod_le_prod (fun _ _ => hr) (fun j _ => hrw (ι j))

theorem ps_bound {w : σ → ℝ} (hw : ∀ i, 0 ≤ w i) {f : MvPowerSeries σ ℝ} (hf : Conv w f)
    {r : ℝ} (hr : 0 ≤ r) (hrw : ∀ i, r ≤ w i) (n : ℕ) : ‖ps f n‖ * r ^ n ≤ wn w f := by
  calc ‖ps f n‖ * r ^ n ≤ (∑ α ∈ degs n, |coeff α f|) * r ^ n :=
        mul_le_mul_of_nonneg_right (norm_ps_le f n) (pow_nonneg hr n)
    _ = ∑ α ∈ degs n, |coeff α f| * r ^ n := Finset.sum_mul _ _ _
    _ ≤ ∑ α ∈ degs n, wt w f α := Finset.sum_le_sum fun α hα =>
        mul_le_mul_of_nonneg_left (pow_le_mw hr hrw hα) (abs_nonneg _)
    _ ≤ wn w f := hf.sum_le_tsum _ (fun α _ => wt_nonneg hw f α)

/-- Bridge A. -/
theorem hasFPowerSeriesOnBall_ev {w : σ → ℝ} (hw : ∀ i, 0 ≤ w i) {f : MvPowerSeries σ ℝ}
    (hf : Conv w f) {r : NNReal} (hr : 0 < r) (hrw : ∀ i, (r : ℝ) ≤ w i) :
    HasFPowerSeriesOnBall (ev f) (ps f) 0 r where
  r_le := FormalMultilinearSeries.le_radius_of_bound _ (wn w f)
    (ps_bound hw hf r.coe_nonneg hrw)
  r_pos := by exact_mod_cast hr
  hasSum := by
    intro y hy
    rw [mem_eball_zero_iff] at hy
    have hy' : ‖y‖ < r := by exact_mod_cast hy
    have hx : ∀ i, |y i| ≤ w i := fun i =>
      ((norm_le_pi_norm y i).trans hy'.le).trans (hrw i)
    rw [zero_add]
    have h1 : HasSum (fun α => coeff α f * mon y α) (ev f y) := (summable_term hx hf).hasSum
    have h2 := (Equiv.sigmaFiberEquiv (Finsupp.degree : (σ →₀ ℕ) → ℕ)).hasSum_iff.2 h1
    refine h2.sigma fun n => ?_
    rw [ps_diag]
    classical
    have h3 : HasSum (fun c : {α : σ →₀ ℕ // Finsupp.degree α = n} => coeff c.1 f * mon y c.1)
        (∑ c ∈ (degs n).subtype (fun α => Finsupp.degree α = n), coeff c.1 f * mon y c.1) := by
      apply hasSum_sum_of_ne_finset_zero
      intro c hc
      exact absurd (Finset.mem_subtype.2 (mem_degs.2 c.2)) hc
    rw [Finset.sum_subtype_of_mem (fun α => coeff α f * mon y α)
      (fun α hα => mem_degs.1 hα)] at h3
    exact h3

theorem analyticAt_ev_zero {w : σ → ℝ} (hw : ∀ i, 0 < w i) {f : MvPowerSeries σ ℝ}
    (hf : Conv w f) : ∃ r : ℝ, 0 < r ∧ ∀ x : σ → ℝ, ‖x‖ < r → AnalyticAt ℝ (ev f) x := by
  classical
  by_cases hσ : Nonempty σ
  · obtain ⟨i0, -, hi0⟩ := Finset.exists_min_image Finset.univ w
      (Finset.univ_nonempty_iff.2 hσ)
    refine ⟨w i0, hw i0, fun x hx => ?_⟩
    let r0 : NNReal := ⟨w i0, (hw i0).le⟩
    have hpow := hasFPowerSeriesOnBall_ev (fun i => (hw i).le) hf
      (r := r0) (hw i0) (fun i => hi0 i (Finset.mem_univ _))
    refine hpow.analyticAt_of_mem ?_
    rw [mem_eball_zero_iff, enorm_eq_nnnorm]
    exact ENNReal.coe_lt_coe.2 (NNReal.coe_lt_coe.1 hx)
  · refine ⟨1, one_pos, fun x _ => ?_⟩
    have hpow := hasFPowerSeriesOnBall_ev (fun i => (hw i).le) hf (r := 1) one_pos
      (fun i => absurd ⟨i⟩ hσ)
    refine hpow.analyticAt_of_mem ?_
    have : x = 0 := funext fun i => absurd ⟨i⟩ hσ
    rw [this]; exact Metric.mem_eball_self (by simp)

end BridgeA

end SubanalyticLib
/-! SubanalyticLib L1d (body; after L1c_Bridge.body): bridge B.  A function with a power series
expansion at `x0` (on `σ → ℝ`, sup norm) agrees near `x0` with `ev a` for a power series `a`
converging absolutely on a small cube (`Conv (fun _ => ρ) a`). -/

namespace SubanalyticLib

section BridgeB

open MvPowerSeries

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem hasSum_fiber (g : (σ →₀ ℕ) → ℝ) (n : ℕ) :
    HasSum (fun c : {α : σ →₀ ℕ // Finsupp.degree α = n} => g c.1) (∑ α ∈ degs n, g α) := by
  classical
  have h3 : HasSum (fun c : {α : σ →₀ ℕ // Finsupp.degree α = n} => g c.1)
      (∑ c ∈ (degs n).subtype (fun α => Finsupp.degree α = n), g c.1) := by
    apply hasSum_sum_of_ne_finset_zero
    intro c hc
    exact absurd (Finset.mem_subtype.2 (mem_degs.2 c.2)) hc
  rwa [Finset.sum_subtype_of_mem g (fun α hα => mem_degs.1 hα)] at h3

/-- `ev` as the sum of its homogeneous parts. -/
theorem hasSum_ev_graded {w : σ → ℝ} {f : MvPowerSeries σ ℝ} (hf : Conv w f) {x : σ → ℝ}
    (hx : ∀ i, |x i| ≤ w i) :
    HasSum (fun n => ∑ α ∈ degs n, coeff α f * mon x α) (ev f x) := by
  have h1 : HasSum (fun α => coeff α f * mon x α) (ev f x) := (summable_term hx hf).hasSum
  have h2 := (Equiv.sigmaFiberEquiv (Finsupp.degree : (σ →₀ ℕ) → ℕ)).hasSum_iff.2 h1
  exact h2.sigma fun n => hasSum_fiber (fun α => coeff α f * mon x α) n

theorem cmm_diag_expand {n : ℕ} (q : ContinuousMultilinearMap ℝ (fun _ : Fin n => σ → ℝ) ℝ)
    (y : σ → ℝ) :
    q (fun _ => y) = ∑ ι : Fin n → σ, (∏ j, y (ι j)) * q (fun j => Pi.single (ι j) 1) := by
  have hy : y = ∑ i, y i • (Pi.single i (1 : ℝ) : σ → ℝ) := by
    ext k; simp [Pi.single_apply]
  have h := ContinuousMultilinearMap.map_sum q (fun (_ : Fin n) (i : σ) => y i • (Pi.single i (1 : ℝ) : σ → ℝ))
  rw [← hy] at h
  rw [h]
  refine Finset.sum_congr rfl fun ι _ => ?_
  rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul]

/-- the coefficient of `x^α` in the degree-`n` part of `p`. -/
noncomputable def ecA (p : FormalMultilinearSeries ℝ (σ → ℝ) ℝ) (n : ℕ) (α : σ →₀ ℕ) : ℝ :=
  ∑ ι ∈ (Finset.univ : Finset (Fin n → σ)) with mult ι = α, p n (fun j => Pi.single (ι j) 1)

/-- the power series of coefficients of `p`. -/
noncomputable def ecoef (p : FormalMultilinearSeries ℝ (σ → ℝ) ℝ) : MvPowerSeries σ ℝ :=
  fun α => ecA p (Finsupp.degree α) α

theorem coeff_ecoef (p : FormalMultilinearSeries ℝ (σ → ℝ) ℝ) (α : σ →₀ ℕ) :
    coeff α (ecoef p) = ecA p (Finsupp.degree α) α := rfl

theorem coeff_ecoef_of_mem (p : FormalMultilinearSeries ℝ (σ → ℝ) ℝ) {n : ℕ} {α : σ →₀ ℕ}
    (hα : α ∈ degs n) : coeff α (ecoef p) = ecA p n α := by
  rw [coeff_ecoef, mem_degs.1 hα]

theorem p_diag_eq (p : FormalMultilinearSeries ℝ (σ → ℝ) ℝ) (n : ℕ) (y : σ → ℝ) :
    p n (fun _ => y) = ∑ α ∈ degs n, coeff α (ecoef p) * mon y α := by
  rw [cmm_diag_expand]
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := degs n) (g := mult)
     (fun ι _ => Finset.mem_image.2 ⟨ι, Finset.mem_univ _, rfl⟩)]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [coeff_ecoef_of_mem p hα, ecA, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ι hι => ?_
  rw [Finset.mem_filter] at hι
  rw [← hι.2, mon_mult]; ring

theorem norm_single_one (i : σ) : ‖(Pi.single i (1 : ℝ) : σ → ℝ)‖ = 1 := by
  rw [Pi.norm_single]; simp

theorem abs_ecA_le (p : FormalMultilinearSeries ℝ (σ → ℝ) ℝ) (n : ℕ) (α : σ →₀ ℕ) :
    |ecA p n α| ≤ ∑ ι ∈ (Finset.univ : Finset (Fin n → σ)) with mult ι = α, ‖p n‖ := by
  unfold ecA
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ι _ => ?_)
  rw [← Real.norm_eq_abs]
  refine ((p n).le_opNorm _).trans (le_of_eq ?_)
  simp [norm_single_one]

theorem fiber_bound (p : FormalMultilinearSeries ℝ (σ → ℝ) ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) (n : ℕ) :
    ∑ α ∈ degs n, |coeff α (ecoef p)| * ρ ^ n ≤ ‖p n‖ * ((Fintype.card σ : ℝ) * ρ) ^ n := by
  calc ∑ α ∈ degs n, |coeff α (ecoef p)| * ρ ^ n
      ≤ ∑ α ∈ degs n,
          (∑ ι ∈ (Finset.univ : Finset (Fin n → σ)) with mult ι = α, ‖p n‖) * ρ ^ n :=
        Finset.sum_le_sum fun α hα => by
          rw [coeff_ecoef_of_mem p hα]
          exact mul_le_mul_of_nonneg_right (abs_ecA_le p n α) (pow_nonneg hρ n)
    _ = ∑ ι : Fin n → σ, ‖p n‖ * ρ ^ n := by
        simp_rw [Finset.sum_mul]
        exact Finset.sum_fiberwise_of_maps_to
          (fun ι _ => Finset.mem_image.2 ⟨ι, Finset.mem_univ _, rfl⟩) _
    _ = ‖p n‖ * ((Fintype.card σ : ℝ) * ρ) ^ n := by
        simp [Finset.sum_const, mul_pow]; ring

theorem mw_const (ρ : ℝ) (α : σ →₀ ℕ) : mw (fun _ => ρ) α = ρ ^ Finsupp.degree α := by
  rw [mw, Finsupp.degree_eq_sum, Finset.prod_pow_eq_pow_sum]

theorem conv_ecoef (p : FormalMultilinearSeries ℝ (σ → ℝ) ℝ) {ρ : NNReal}
    (h : (((Fintype.card σ : NNReal) * ρ : NNReal) : ENNReal) < p.radius) :
    Conv (fun _ => (ρ : ℝ)) (ecoef p) := by
  have hs := p.summable_norm_mul_pow h
  unfold Conv
  rw [← (Equiv.sigmaFiberEquiv (Finsupp.degree : (σ →₀ ℕ) → ℕ)).summable_iff]
  have hfib : ∀ n, HasSum
      (fun c : {α : σ →₀ ℕ // Finsupp.degree α = n} => wt (fun _ => (ρ : ℝ)) (ecoef p) c.1)
      (∑ α ∈ degs n, |coeff α (ecoef p)| * (ρ : ℝ) ^ n) := by
    intro n
    have := hasSum_fiber (fun α => wt (fun _ => (ρ : ℝ)) (ecoef p) α) n
    convert this using 1
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [wt, mw_const, mem_degs.1 hα]
  refine (summable_sigma_of_nonneg (f := wt (fun _ => (ρ : ℝ)) (ecoef p) ∘
    ⇑(Equiv.sigmaFiberEquiv (Finsupp.degree : (σ →₀ ℕ) → ℕ)))
    (fun c => wt_nonneg (fun _ => ρ.coe_nonneg) _ _)).2 ⟨fun n => (hfib n).summable, ?_⟩
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hs
  · exact tsum_nonneg fun c => wt_nonneg (fun _ => ρ.coe_nonneg) _ _
  · have hb : ∑ α ∈ degs n, |coeff α (ecoef p)| * (ρ : ℝ) ^ n ≤
        ‖p n‖ * (((Fintype.card σ : NNReal) * ρ : NNReal) : ℝ) ^ n := by
      have := fiber_bound p ρ.coe_nonneg n
      simpa using this
    exact (le_of_eq (hfib n).tsum_eq).trans hb

/-- Bridge B. -/
theorem exists_conv_of_hasFPowerSeriesOnBall {F : (σ → ℝ) → ℝ}
    {p : FormalMultilinearSeries ℝ (σ → ℝ) ℝ} {x0 : σ → ℝ} {R : ENNReal}
    (hF : HasFPowerSeriesOnBall F p x0 R) :
    ∃ ρ : ℝ, 0 < ρ ∧ Conv (fun _ => ρ) (ecoef p) ∧
      ∀ x : σ → ℝ, ‖x‖ ≤ ρ → F (x0 + x) = ev (ecoef p) x := by
  obtain ⟨r, hr0, hrR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hF.r_pos
  have hr0' : 0 < r := by exact_mod_cast hr0
  set c : NNReal := (Fintype.card σ : NNReal) + 1 with hc_def
  have hc1 : 1 ≤ c := le_add_of_nonneg_left zero_le
  have hc0 : c ≠ 0 := (lt_of_lt_of_le zero_lt_one hc1).ne'
  set ρ : NNReal := r / c with hρ_def
  have hcρ_eq : c * ρ = r := by rw [hρ_def]; field_simp
  have hcρ : (Fintype.card σ : NNReal) * ρ ≤ r := by
    rw [← hcρ_eq]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) zero_le
  have hρr : ρ ≤ r := by
    rw [← hcρ_eq]; exact le_mul_of_one_le_left zero_le hc1
  have hρ0 : 0 < ρ := by rw [hρ_def]; exact div_pos hr0' (lt_of_lt_of_le zero_lt_one hc1)
  have hconv : (((Fintype.card σ : NNReal) * ρ : NNReal) : ENNReal) < p.radius :=
    lt_of_lt_of_le (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hcρ) hrR) hF.r_le
  refine ⟨ρ, NNReal.coe_pos.2 hρ0, conv_ecoef p hconv, fun x hx => ?_⟩
  have hxb : x ∈ Metric.eball (0 : σ → ℝ) R := by
    rw [mem_eball_zero_iff, enorm_eq_nnnorm]
    have hx' : ‖x‖₊ ≤ ρ := NNReal.coe_le_coe.1 hx
    exact lt_of_le_of_lt (ENNReal.coe_le_coe.2 (hx'.trans hρr)) hrR
  have h1 := hF.hasSum hxb
  have hxi : ∀ i, |x i| ≤ (fun _ => (ρ : ℝ)) i := fun i => (norm_le_pi_norm x i).trans hx
  have h2 := hasSum_ev_graded (w := fun _ => (ρ : ℝ)) (conv_ecoef p hconv) hxi
  have h3 : (fun n => p n (fun _ => x)) = fun n => ∑ α ∈ degs n, coeff α (ecoef p) * mon x α :=
    funext fun n => p_diag_eq p n x
  rw [h3] at h1
  exact h1.unique h2

theorem exists_conv_of_analyticAt {F : (σ → ℝ) → ℝ} {x0 : σ → ℝ} (hF : AnalyticAt ℝ F x0) :
    ∃ a : MvPowerSeries σ ℝ, ∃ ρ : ℝ, 0 < ρ ∧ Conv (fun _ => ρ) a ∧
      ∀ x : σ → ℝ, ‖x‖ ≤ ρ → F (x0 + x) = ev a x := by
  obtain ⟨p, R, hp⟩ := hF
  obtain ⟨ρ, h1, h2, h3⟩ := exists_conv_of_hasFPowerSeriesOnBall hp
  exact ⟨_, ρ, h1, h2, h3⟩

end BridgeB

end SubanalyticLib
/-! SubanalyticLib L2e (body; after L2E.lean): Weierstrass preparation at the level of values.
On a small polydisc, `x_y^d = ev q x * ev f x + ev r x` with `ev q x ≠ 0`, and
`ev r x = Σ_{j<d} x_y^j * c_j(x)` where each `c_j` does not depend on `x_y`. -/

namespace SubanalyticLib

section EvPrep

open MvPowerSeries

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem ev_X_pow (i : σ) (d : ℕ) (x : σ → ℝ) {w : σ → ℝ} (hx : ∀ i, |x i| ≤ w i)
    (hw : ∀ i, 0 ≤ w i) : ev ((X i : MvPowerSeries σ ℝ) ^ d) x = x i ^ d := by
  rw [ev_pow hx hw (conv_X hw i) d, ev_X]

/-- the `j`-th coefficient of `r` as a series in the distinguished variable `y`. -/
noncomputable def yslice (y : σ) (j : ℕ) (r : MvPowerSeries σ ℝ) : MvPowerSeries σ ℝ :=
  lowPart y 1 (hatPart y j r)

theorem coeff_yslice (y : σ) (j : ℕ) (r : MvPowerSeries σ ℝ) (α : σ →₀ ℕ) :
    coeff α (yslice y j r) = if α y < 1 then coeff (α + Finsupp.single y j) r else 0 := by
  rw [yslice, coeff_lowPart, coeff_hatPart]

theorem eq_sum_yslice (y : σ) (d : ℕ) (r : MvPowerSeries σ ℝ) (hr : hatPart y d r = 0) :
    r = ∑ j ∈ Finset.range d, X y ^ j * yslice y j r := by
  have hlow : lowPart y d r = r := (lowPart_eq_self_iff y d r).2 hr
  ext α
  rw [map_sum]
  simp_rw [X_pow_eq, coeff_monomial_mul, one_mul, coeff_yslice]
  rw [Finset.sum_eq_single (α y)]
  · by_cases hαd : α y < d
    · have hle : Finsupp.single y (α y) ≤ α := by
        rw [Finsupp.single_le_iff]
      have hsub : (α - Finsupp.single y (α y)) y = 0 := by simp
      rw [if_pos hle, hsub, if_pos Nat.one_pos, tsub_add_cancel_of_le hle]
    · have h0 : coeff α r = 0 := by rw [← hlow, coeff_lowPart, if_neg hαd]
      have hle : Finsupp.single y (α y) ≤ α := by rw [Finsupp.single_le_iff]
      rw [if_pos hle, tsub_add_cancel_of_le hle, h0, ite_self]
  · intro j _ hj
    split_ifs with h1 h2
    · exfalso
      have e1 : (α - Finsupp.single y j) y = α y - j := by simp
      have e2 : j ≤ α y := by
        have := (Finsupp.single_le_iff).1 h1; simpa using this
      omega
    · rfl
    · rfl
  · intro hd
    rw [Finset.mem_range, not_lt] at hd
    have : coeff α r = 0 := by
      rw [← hlow, coeff_lowPart, if_neg (by omega)]
    split_ifs with h1 h2
    · rw [tsub_add_cancel_of_le h1, this]
    · rfl
    · rfl

/-- `y`-free series do not see the `y` coordinate. -/
theorem ev_yslice_update (y : σ) (j : ℕ) (r : MvPowerSeries σ ℝ) (x : σ → ℝ) (t : ℝ) :
    ev (yslice y j r) (Function.update x y t) = ev (yslice y j r) x := by
  unfold ev
  congr 1; funext α
  rw [coeff_yslice]
  split_ifs with h
  · congr 1
    unfold mon
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hi : i = y
    · subst hi; have : α i = 0 := by omega
      simp [this]
    · rw [Function.update_of_ne hi]
  · simp

theorem ev_sum_X_pow_mul (y : σ) {w : σ → ℝ} (hw : ∀ i, 0 ≤ w i) {x : σ → ℝ}
    (hx : ∀ i, |x i| ≤ w i) (s : Finset ℕ) (g : ℕ → MvPowerSeries σ ℝ) (hg : ∀ j, Conv w (g j)) :
    ev (∑ j ∈ s, X y ^ j * g j) x = ∑ j ∈ s, x y ^ j * ev (g j) x := by
  classical
  have hterm : ∀ j, Conv w ((X y : MvPowerSeries σ ℝ) ^ j * g j) := fun j =>
    Conv.mul hw (Conv.pow hw (conv_X hw y) j) (hg j)
  induction s using Finset.induction_on with
  | empty => simp [ev]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj,
      ev_add hx (hterm j) (conv_finset_sum hw s _ (fun k _ => hterm k)).1,
      ev_mul hx hw (Conv.pow hw (conv_X hw y) j) (hg j), ev_X_pow y j x hx hw, ih]

theorem ev_eq_sum_yslice (y : σ) (d : ℕ) {w : σ → ℝ} (hw : ∀ i, 0 ≤ w i) (hy : 0 < w y)
    {r : MvPowerSeries σ ℝ} (hrc : Conv w r) (hr : hatPart y d r = 0) {x : σ → ℝ}
    (hx : ∀ i, |x i| ≤ w i) :
    ev r x = ∑ j ∈ Finset.range d, x y ^ j * ev (yslice y j r) x := by
  have hs : ∀ j, Conv w (yslice y j r) := fun j => Conv.low y hw 1 (Conv.hat y hw hy j hrc)
  conv_lhs => rw [eq_sum_yslice y d r hr]
  exact ev_sum_X_pow_mul y hw hx _ _ hs

end EvPrep

end SubanalyticLib
/-! SubanalyticLib L3g (body; after L2F.lean): power-growth of positive zeros of a nonzero
convergent series in two variables.  If `G ≠ 0` converges on the polydisc `w` and `t = ψ(s) > 0`
solves `G(s,t) = 0` whenever `t ≤ w 1`, then `ψ(s) ≥ c s^m` near `0⁺`.  No Puiseux expansion
is needed: `G = t^k (g(s) + t H)` with `g(s) = s^m (b + o(1))`, `b ≠ 0`. -/

namespace SubanalyticLib

section Growth

open MvPowerSeries

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem ev_single_axis (v : σ) {h : MvPowerSeries σ ℝ}
    (hz : ∀ j, coeff (Finsupp.single v j) h = 0) (s : ℝ) : ev h (Pi.single v s) = 0 := by
  have key : ∀ α, coeff α h * mon (Pi.single v s) α = 0 := by
    intro α
    by_cases hα : ∃ i, i ≠ v ∧ α i ≠ 0
    · obtain ⟨i, hiv, hi⟩ := hα
      have : mon (Pi.single v s) α = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Pi.single_apply, hiv, hi])
      rw [this, mul_zero]
    · push_neg at hα
      have : α = Finsupp.single v (α v) := by
        ext i
        by_cases hi : i = v
        · subst hi; simp
        · rw [Finsupp.single_apply, if_neg (Ne.symm hi)]; exact hα i hi
      rw [this, hz, zero_mul]
  unfold ev
  simp only [key, tsum_zero]

theorem axis_lower_bound (v : σ) {w : σ → ℝ} (hw : ∀ i, 0 < w i) {g : MvPowerSeries σ ℝ}
    (hg : Conv w g) (m : ℕ) (hz : ∀ j < m, coeff (Finsupp.single v j) g = 0)
    (hb : coeff (Finsupp.single v m) g ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 ≤ s → s ≤ δ →
      |coeff (Finsupp.single v m) g| / 2 * s ^ m ≤ |ev g (Pi.single v s)| := by
  have hw' : ∀ i, 0 ≤ w i := fun i => (hw i).le
  set b := coeff (Finsupp.single v m) g with hb_def
  set K := hatPart v m g with hK_def
  have hK : Conv w K := Conv.hat v hw' (hw v) m hg
  set D := K - C b with hD_def
  have hD : Conv w D := Conv.sub hw' hK (conv_C b)
  have hDz : ∀ α, sdeg (Finset.univ : Finset σ) α = 0 → coeff α D = 0 := by
    intro α hα
    have : α = 0 := by
      ext i
      have := (Finset.sum_eq_zero_iff.1 hα) i (Finset.mem_univ _)
      simpa using this
    subst this
    rw [hD_def, map_sub, hK_def, coeff_hatPart, zero_add, coeff_zero_C, hb_def, sub_self]
  have hbpos : 0 < |b| := abs_pos.2 hb
  have hDn : 0 ≤ wn w D := wn_nonneg hw' D
  set τ : ℝ := min 1 (|b| / (2 * (wn w D + 1))) with hτ_def
  have hτ0 : 0 < τ := lt_min one_pos (div_pos hbpos (by linarith))
  have hτ1 : τ ≤ 1 := min_le_left _ _
  obtain ⟨hDw, hDwn⟩ := conv_scale hw' Finset.univ hτ0.le hτ1 hD hDz
  set w' := scaleW (Finset.univ : Finset σ) τ w with hw'_def
  have hw'v : ∀ i, w' i = τ * w i := fun i => by simp [hw'_def, scaleW]
  have hw'nn : ∀ i, 0 ≤ w' i := fun i => by rw [hw'v]; exact mul_nonneg hτ0.le (hw' i)
  have hw'le : ∀ i, w' i ≤ w i := scaleW_le hw' hτ1
  have hDsmall : wn w' D ≤ |b| / 2 := by
    refine hDwn.trans ?_
    have h1 : τ ≤ |b| / (2 * (wn w D + 1)) := min_le_right _ _
    have h2 : τ * wn w D ≤ |b| / (2 * (wn w D + 1)) * wn w D :=
      mul_le_mul_of_nonneg_right h1 hDn
    have h3 : |b| / (2 * (wn w D + 1)) * wn w D ≤ |b| / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by linarith) (by norm_num)]
      nlinarith
    linarith
  refine ⟨τ * w v, mul_pos hτ0 (hw v), fun s hs0 hsδ => ?_⟩
  set x : σ → ℝ := Pi.single v s with hx_def
  have hx : ∀ i, |x i| ≤ w' i := by
    intro i
    rw [hw'v]
    by_cases hi : i = v
    · subst hi; simp [hx_def, abs_of_nonneg hs0, hsδ]
    · simp [hx_def, Pi.single_apply, hi]; exact mul_nonneg hτ0.le (hw' i)
  have hgw : Conv w' g := Conv.mono hw'nn hw'le hg
  have hKw : Conv w' K := Conv.mono hw'nn hw'le hK
  have hlow : ev (lowPart v m g) x = 0 := by
    apply ev_single_axis
    intro j
    rw [coeff_lowPart]
    split_ifs with hj
    · simp only [Finsupp.single_eq_same] at hj; exact hz j hj
    · rfl
  have hsplit : ev g x = s ^ m * ev K x := by
    have e := congrArg (fun F => ev F x) (low_add_hat v m g)
    rw [ev_add hx (Conv.low v hw'nn m hgw) (Conv.mul hw'nn (Conv.pow hw'nn (conv_X hw'nn v) m) hKw),
      hlow, zero_add, ev_mul hx hw'nn (Conv.pow hw'nn (conv_X hw'nn v) m) hKw,
      ev_X_pow v m x hx hw'nn] at e
    rw [e, hx_def, Pi.single_eq_same]
  have hKx : ev K x = b + ev D x := by
    have : K = C b + D := by rw [hD_def]; ring
    rw [this, ev_add hx (conv_C b) hDw, ev_C]
  have hDx : |ev D x| ≤ |b| / 2 := (abs_ev_le hx hDw).trans hDsmall
  rw [hsplit, hKx, abs_mul, abs_of_nonneg (pow_nonneg hs0 m), mul_comm (s ^ m)]
  refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hs0 m)
  have := abs_sub_abs_le_abs_sub b (-ev D x)
  rw [sub_neg_eq_add, abs_neg] at this
  linarith

end Growth

end SubanalyticLib

/-! SubanalyticLib CS-5d prelude: `ev_weierstrass_prep` also exposing that the remainder has no pure-`y` terms
below degree `d` (copied from L2e with that extra conjunct). -/

namespace SubanalyticLib

section WP2

open MvPowerSeries

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem ev_weierstrass_prep2 (y : σ) {w0 : σ → ℝ} (hw0 : ∀ i, 0 < w0 i) (d : ℕ)
    {f : MvPowerSeries σ ℝ} (hf : Conv w0 f) (hreg : ∀ j < d, coeff (Finsupp.single y j) f = 0)
    (hd : coeff (Finsupp.single y d) f ≠ 0) :
    ∃ w : σ → ℝ, (∀ i, 0 < w i) ∧ (∀ i, w i ≤ w0 i) ∧
      ∃ q r : MvPowerSeries σ ℝ, Conv w q ∧ Conv w r ∧ hatPart y d r = 0 ∧
        (∀ j < d, coeff (Finsupp.single y j) r = 0) ∧
        ∀ x : σ → ℝ, (∀ i, |x i| ≤ w i) → ev q x ≠ 0 ∧ x y ^ d = ev q x * ev f x + ev r x := by
  obtain ⟨w1, hw1, hw10, q, r, hq, hr, hr0, hc, hrc0, heq⟩ := weierstrass_prep y hw0 d hf hreg hd
  have hw1' : ∀ i, 0 ≤ w1 i := fun i => (hw1 i).le
  set c := constantCoeff q with hc_def
  set g := q - C c with hg_def
  have hg : Conv w1 g := Conv.sub hw1' hq (conv_C c)
  have hgz : ∀ α, sdeg (Finset.univ : Finset σ) α = 0 → coeff α g = 0 := by
    intro α hα
    have : α = 0 := by
      ext i
      have := (Finset.sum_eq_zero_iff.1 hα) i (Finset.mem_univ _)
      simpa using this
    subst this
    rw [hg_def, map_sub, coeff_zero_eq_constantCoeff_apply, coeff_zero_C, hc_def, sub_self]
  have hcpos : 0 < |c| := abs_pos.2 hc
  have hgn : 0 ≤ wn w1 g := wn_nonneg hw1' g
  set τ : ℝ := min 1 (|c| / (2 * (wn w1 g + 1))) with hτ_def
  have hτ0 : 0 < τ := lt_min one_pos (div_pos hcpos (by linarith))
  have hτ1 : τ ≤ 1 := min_le_left _ _
  obtain ⟨hgw, hgwn⟩ := conv_scale hw1' Finset.univ hτ0.le hτ1 hg hgz
  set w := scaleW (Finset.univ : Finset σ) τ w1 with hw_def
  have hwpos : ∀ i, 0 < w i := fun i => by
    simp only [hw_def, scaleW, Finset.mem_univ, if_true]; exact mul_pos hτ0 (hw1 i)
  have hw' : ∀ i, 0 ≤ w i := fun i => (hwpos i).le
  have hwle : ∀ i, w i ≤ w1 i := scaleW_le hw1' hτ1
  have hgsmall : wn w g < |c| := by
    refine lt_of_le_of_lt hgwn ?_
    have h1 : τ ≤ |c| / (2 * (wn w1 g + 1)) := min_le_right _ _
    have h2 : τ * wn w1 g ≤ |c| / (2 * (wn w1 g + 1)) * wn w1 g :=
      mul_le_mul_of_nonneg_right h1 hgn
    have h3 : |c| / (2 * (wn w1 g + 1)) * wn w1 g < |c| := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
    linarith
  have hqw : Conv w q := Conv.mono hw' hwle hq
  have hrw : Conv w r := Conv.mono hw' hwle hr
  have hfw : Conv w f := Conv.mono hw' (fun i => (hwle i).trans (hw10 i)) hf
  refine ⟨w, hwpos, fun i => (hwle i).trans (hw10 i), q, r, hqw, hrw, hr0, hrc0, fun x hx => ⟨?_, ?_⟩⟩
  · have hqx : ev q x = c + ev g x := by
      have : q = C c + g := by rw [hg_def]; ring
      rw [this, ev_add hx (conv_C c) hgw, ev_C]
    rw [hqx]
    intro h0
    have h4 : |ev g x| ≤ wn w g := abs_ev_le hx hgw
    have h5 : ev g x = -c := by linarith
    rw [h5, abs_neg] at h4
    linarith
  · have : ev (X y ^ d) x = ev (q * f + r) x := by rw [heq]
    rw [ev_X_pow y d x hx hw', ev_add hx (Conv.mul hw' hqw hfw) hrw, ev_mul hx hw' hqw hfw] at this
    exact this

end WP2

end SubanalyticLib

/-! SubanalyticLib CS-5a: real Newton–Puiseux in one parameter, infrastructure.
`Ran` = functions analytic at `0`; `pv P v` = the real polynomial obtained by evaluating the
coefficients of `P : Ran[X]` at `v`; `BranchesAt P q` = the real roots of `pv P (v ^ q)` for
small `v > 0` are exactly the values `φ v` of finitely many analytic germs `φ`. -/

open Filter Topology Set Polynomial

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace SubanalyticLib
namespace Pui

noncomputable section

/-- Real functions analytic at `0`, as a subring of `ℝ → ℝ`. -/
def Ran : Subring (ℝ → ℝ) where
  carrier := {f | AnalyticAt ℝ f 0}
  mul_mem' {a b} ha hb := by
    show AnalyticAt ℝ (fun x => a x * b x) 0
    exact ha.mul hb
  one_mem' := by
    show AnalyticAt ℝ (fun _ => (1 : ℝ)) 0
    exact analyticAt_const
  add_mem' {a b} ha hb := by
    show AnalyticAt ℝ (fun x => a x + b x) 0
    exact ha.add hb
  zero_mem' := by
    show AnalyticAt ℝ (fun _ => (0 : ℝ)) 0
    exact analyticAt_const
  neg_mem' {a} ha := by
    show AnalyticAt ℝ (fun x => -a x) 0
    exact ha.neg

lemma analyticAt_coe (a : Ran) : AnalyticAt ℝ (a : ℝ → ℝ) 0 := a.2

/-- Constant germ. -/
def cst (c : ℝ) : Ran := ⟨fun _ => c, analyticAt_const⟩

@[simp] lemma cst_apply (c v : ℝ) : (cst c : ℝ → ℝ) v = c := rfl

/-- Evaluation at a point. -/
def evAt (v : ℝ) : Ran →+* ℝ := (Pi.evalRingHom (fun _ : ℝ => ℝ) v).comp Ran.subtype

@[simp] lemma evAt_apply (v : ℝ) (a : Ran) : evAt v a = (a : ℝ → ℝ) v := rfl

/-- The real polynomial at parameter `v`. -/
def pv (P : Ran[X]) (v : ℝ) : ℝ[X] := P.map (evAt v)

lemma coeff_pv (P : Ran[X]) (v : ℝ) (n : ℕ) : (pv P v).coeff n = (P.coeff n : ℝ → ℝ) v := by
  simp [pv]

lemma pv_monic {P : Ran[X]} (hP : P.Monic) (v : ℝ) : (pv P v).Monic := hP.map _

lemma natDegree_pv {P : Ran[X]} (hP : P.Monic) (v : ℝ) : (pv P v).natDegree = P.natDegree :=
  hP.natDegree_map _

lemma eval_monic_eq {p : ℝ[X]} (hp : p.Monic) (y : ℝ) :
    p.eval y = y ^ p.natDegree + ∑ j ∈ Finset.range p.natDegree, p.coeff j * y ^ j := by
  rw [eval_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, one_mul, add_comm]

lemma eval_pv {P : Ran[X]} (hP : P.Monic) (v y : ℝ) :
    (pv P v).eval y = y ^ P.natDegree + ∑ j ∈ Finset.range P.natDegree,
      (P.coeff j : ℝ → ℝ) v * y ^ j := by
  rw [eval_monic_eq (pv_monic hP v), natDegree_pv hP]
  simp only [coeff_pv]

/-- Cauchy's root bound for a monic real polynomial. -/
lemma root_bound {p : ℝ[X]} (hp : p.Monic) {y : ℝ} (hy : p.IsRoot y) :
    |y| ≤ max 1 (∑ j ∈ Finset.range p.natDegree, |p.coeff j|) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, hS⟩ := max_lt_iff.mp hcon
  set d := p.natDegree
  have h0 : y ^ d = -∑ j ∈ Finset.range d, p.coeff j * y ^ j := by
    have h := hy
    rw [IsRoot.def, eval_monic_eq hp] at h
    linarith
  have hyd : |y| ^ d ≤ ∑ j ∈ Finset.range d, |p.coeff j| * |y| ^ j := by
    rw [← abs_pow, h0, abs_neg]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [abs_mul, abs_pow]
  have hy1 : (1 : ℝ) ≤ |y| := h1.le
  have hstep : ∑ j ∈ Finset.range d, |p.coeff j| * |y| ^ j * |y| ≤
      (∑ j ∈ Finset.range d, |p.coeff j|) * |y| ^ d := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j hj => ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [← pow_succ]
    exact pow_le_pow_right₀ hy1 (Finset.mem_range.mp hj)
  have hpos : 0 < |y| ^ d := pow_pos (by linarith) _
  have h2 : |y| ^ d * |y| ≤ (∑ j ∈ Finset.range d, |p.coeff j|) * |y| ^ d := by
    calc |y| ^ d * |y| ≤ (∑ j ∈ Finset.range d, |p.coeff j| * |y| ^ j) * |y| :=
          mul_le_mul_of_nonneg_right hyd (abs_nonneg _)
      _ = ∑ j ∈ Finset.range d, |p.coeff j| * |y| ^ j * |y| := by rw [Finset.sum_mul]
      _ ≤ _ := hstep
  have h3 := mul_lt_mul_of_pos_right hS hpos
  have e : |y| ^ d * |y| = |y| * |y| ^ d := mul_comm _ _
  linarith

/-- Real roots move continuously: for `v` near `0`, every real root of `pv P v` is `δ`-close to a
real root of `pv P 0`. -/
lemma roots_near {P : Ran[X]} (hP : P.Monic) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ v in 𝓝 (0 : ℝ), ∀ y, (pv P v).IsRoot y → ∃ c, (pv P 0).IsRoot c ∧ |y - c| < δ := by
  have hc : ∀ j, ContinuousAt ((P.coeff j : ℝ → ℝ)) 0 := fun j => (analyticAt_coe (P.coeff j)).continuousAt
  set M : ℝ := max 1 (∑ j ∈ Finset.range P.natDegree, (|(P.coeff j : ℝ → ℝ) 0| + 1))
  -- eventually the coefficients are within 1 of their value at 0
  have hev1 : ∀ᶠ v in 𝓝 (0 : ℝ), ∀ j ∈ Finset.range P.natDegree, |(P.coeff j : ℝ → ℝ) v - (P.coeff j : ℝ → ℝ) 0| < 1 := by
    rw [Finset.eventually_all]
    intro j _
    have ht : Tendsto (fun v => (P.coeff j : ℝ → ℝ) v - (P.coeff j : ℝ → ℝ) 0) (𝓝 0) (𝓝 0) := by
      have := (hc j).tendsto.sub_const ((P.coeff j : ℝ → ℝ) 0)
      simpa using this
    have := ht.abs
    simp only [abs_zero] at this
    exact this.eventually (gt_mem_nhds one_pos)
  have hbound : ∀ᶠ v in 𝓝 (0 : ℝ), ∀ y, (pv P v).IsRoot y → |y| ≤ M := by
    filter_upwards [hev1] with v hv y hy
    have hb := root_bound (pv_monic hP v) hy
    rw [natDegree_pv hP] at hb
    refine hb.trans (max_le_max le_rfl (Finset.sum_le_sum fun j hj => ?_))
    rw [coeff_pv]
    have := hv j hj
    have h' : |(P.coeff j : ℝ → ℝ) v| ≤ |(P.coeff j : ℝ → ℝ) 0| + |(P.coeff j : ℝ → ℝ) v - (P.coeff j : ℝ → ℝ) 0| := by
      calc |(P.coeff j : ℝ → ℝ) v| = |(P.coeff j : ℝ → ℝ) 0 + ((P.coeff j : ℝ → ℝ) v - (P.coeff j : ℝ → ℝ) 0)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    show |(P.coeff j : ℝ → ℝ) v| ≤ |(P.coeff j : ℝ → ℝ) 0| + 1
    linarith
  set K : Set ℝ := {y | |y| ≤ M ∧ ∀ c, (pv P 0).IsRoot c → δ ≤ |y - c|}
  rcases K.eq_empty_or_nonempty with hK | hK
  · filter_upwards [hbound] with v hv y hy
    by_contra hno
    push Not at hno
    have hyK : y ∈ K := ⟨hv y hy, hno⟩
    rw [hK] at hyK
    exact hyK
  · have hKc : IsCompact K := by
      apply Metric.isCompact_of_isClosed_isBounded
      · have h1 : IsClosed {y : ℝ | |y| ≤ M} := isClosed_le continuous_abs continuous_const
        have h2 : IsClosed {y : ℝ | ∀ c, (pv P 0).IsRoot c → δ ≤ |y - c|} := by
          simp only [Set.ofPred_forall]
          exact isClosed_iInter fun c => isClosed_iInter fun _ =>
            isClosed_le continuous_const (continuous_abs.comp (continuous_id.sub continuous_const))
        exact h1.inter h2
      · refine (Metric.isBounded_Icc (-M) M).subset fun y hy => ?_
        exact ⟨by linarith [neg_abs_le y, hy.1], by linarith [le_abs_self y, hy.1]⟩
    obtain ⟨y0, hy0K, hmin⟩ := hKc.exists_isMinOn hK
      ((Polynomial.continuous _).abs.continuousOn (s := K))
    set η := |(pv P 0).eval y0|
    have hη : 0 < η := by
      rw [abs_pos]
      intro h0
      have := hy0K.2 y0 h0
      simp at this
      linarith
    have hT : Tendsto (fun v => ∑ j ∈ Finset.range P.natDegree, |(P.coeff j : ℝ → ℝ) v - (P.coeff j : ℝ → ℝ) 0| * M ^ j) (𝓝 0) (𝓝 0) := by
      have := tendsto_finsetSum (Finset.range P.natDegree) (fun j _ =>
        ((((hc j).sub (continuousAt_const (y := (P.coeff j : ℝ → ℝ) 0))).abs).mul
          (continuousAt_const (y := M ^ j))).tendsto)
      simpa using this
    filter_upwards [hbound, hT.eventually (gt_mem_nhds hη)] with v hv hsmall y hy
    by_contra hno
    push Not at hno
    have hyK : y ∈ K := ⟨hv y hy, hno⟩
    have hge : η ≤ |(pv P 0).eval y| := hmin hyK
    have hdiff' : (pv P 0).eval y = ∑ j ∈ Finset.range P.natDegree,
        ((P.coeff j : ℝ → ℝ) 0 - (P.coeff j : ℝ → ℝ) v) * y ^ j := by
      have h0 := hy.eq_zero
      rw [eval_pv hP] at h0 ⊢
      simp only [sub_mul, Finset.sum_sub_distrib]
      linarith
    have hyM : |y| ≤ M := hv y hy
    have hle : |(pv P 0).eval y| ≤ ∑ j ∈ Finset.range P.natDegree, |(P.coeff j : ℝ → ℝ) v - (P.coeff j : ℝ → ℝ) 0| * M ^ j := by
      rw [hdiff']
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [abs_mul, abs_sub_comm, abs_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hyM j) (abs_nonneg _)
    linarith

/-- The branch property with ramification index `q`. -/
def BranchesAt (P : Ran[X]) (q : ℕ) : Prop :=
  ∃ Φ : Set (ℝ → ℝ), Φ.Finite ∧ (∀ φ ∈ Φ, AnalyticAt ℝ φ 0) ∧
    ∀ᶠ v in 𝓝[>] (0 : ℝ), ∀ y : ℝ, (pv P (v ^ q)).IsRoot y ↔ ∃ φ ∈ Φ, φ v = y

lemma tendsto_pow_nhdsGT {k : ℕ} (hk : 0 < k) :
    Tendsto (fun w : ℝ => w ^ k) (𝓝[>] 0) (𝓝[>] 0) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, eventually_mem_nhdsWithin.mono fun w (hw : 0 < w) => show w ^ k ∈ Ioi 0 from pow_pos hw k⟩
  have : Tendsto (fun w : ℝ => w ^ k) (𝓝 0) (𝓝 (0 ^ k)) := (continuous_pow k).tendsto 0
  rw [zero_pow hk.ne'] at this
  exact this.mono_left nhdsWithin_le_nhds

lemma analyticAt_comp_pow {φ : ℝ → ℝ} (hφ : AnalyticAt ℝ φ 0) {k : ℕ} (hk : 0 < k) :
    AnalyticAt ℝ (fun w => φ (w ^ k)) 0 :=
  hφ.comp_of_eq ((analyticAt_id).pow k) (by simp [hk.ne'])

/-- Reparametrize `v = w ^ k`. -/
lemma BranchesAt.mul {P : Ran[X]} {q : ℕ} (h : BranchesAt P q) {k : ℕ} (hk : 0 < k) :
    BranchesAt P (q * k) := by
  obtain ⟨Φ, hfin, han, hev⟩ := h
  refine ⟨(fun φ => fun w => φ (w ^ k)) '' Φ, hfin.image _, ?_, ?_⟩
  · rintro _ ⟨φ, hφ, rfl⟩
    exact analyticAt_comp_pow (han φ hφ) hk
  · filter_upwards [(tendsto_pow_nhdsGT hk).eventually hev] with w hw y
    have e : w ^ (q * k) = (w ^ k) ^ q := by rw [← pow_mul, mul_comm]
    rw [e, hw y]
    constructor
    · rintro ⟨φ, hφ, rfl⟩
      exact ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩
      exact ⟨φ, hφ, rfl⟩

lemma BranchesAt.of_dvd {P : Ran[X]} {q L : ℕ} (h : BranchesAt P q) (hL : 0 < L) (hqL : q ∣ L) :
    BranchesAt P L := by
  obtain ⟨k, rfl⟩ := hqL
  exact h.mul (Nat.pos_of_mul_pos_left hL)

lemma pv_taylor (P : Ran[X]) (s : Ran) (v : ℝ) :
    pv (taylor s P) v = taylor ((s : ℝ → ℝ) v) (pv P v) := by
  simp [pv, taylor_apply, Polynomial.map_comp]

/-- Transfer the branch property through a coefficient shift `y ↦ y + s`. -/
lemma BranchesAt.of_taylor {P : Ran[X]} (s : Ran) {q : ℕ} (hq : 0 < q)
    (h : BranchesAt (taylor s P) q) : BranchesAt P q := by
  obtain ⟨Φ, hfin, han, hev⟩ := h
  refine ⟨(fun φ => fun w => φ w + (s : ℝ → ℝ) (w ^ q)) '' Φ, hfin.image _, ?_, ?_⟩
  · rintro _ ⟨φ, hφ, rfl⟩
    exact (han φ hφ).add (analyticAt_comp_pow (analyticAt_coe s) hq)
  · filter_upwards [hev] with w hw y
    have key : (pv P (w ^ q)).IsRoot y ↔
        (pv (taylor s P) (w ^ q)).IsRoot (y - (s : ℝ → ℝ) (w ^ q)) := by
      rw [pv_taylor, IsRoot.def, IsRoot.def, taylor_eval, sub_add_cancel]
    rw [key, hw]
    constructor
    · rintro ⟨φ, hφ, he⟩
      exact ⟨_, ⟨φ, hφ, rfl⟩, by simp only; linarith⟩
    · rintro ⟨_, ⟨φ, hφ, rfl⟩, he⟩
      exact ⟨φ, hφ, by simp only at he; linarith⟩

/-- Tschirnhaus: the `n`-th Taylor coefficient of a monic polynomial of degree `n + 1`. -/
lemma taylor_coeff_pred {R : Type*} [CommRing R] {p : R[X]} {n : ℕ} (hp : p.Monic)
    (hd : p.natDegree = n + 1) (r : R) :
    (taylor r p).coeff n = p.coeff n + (n + 1) * r := by
  rw [taylor_coeff]
  have hdeg : (hasseDeriv n p).natDegree < 2 := by
    have := natDegree_hasseDeriv_le p n
    omega
  rw [eval_eq_sum_range' hdeg, Finset.sum_range_succ, Finset.sum_range_one, hasseDeriv_coeff,
    hasseDeriv_coeff]
  have h1 : (1 + n) = p.natDegree := by omega
  rw [zero_add, Nat.choose_self, h1, hp.coeff_natDegree, hd, Nat.choose_succ_self_right]
  push_cast
  ring

/-- After the Tschirnhaus shift the coefficient of `X ^ n` vanishes. -/
lemma tschirnhaus {P : Ran[X]} {n : ℕ} (hP : P.Monic) (hd : P.natDegree = n + 1) :
    (taylor (cst (-((n : ℝ) + 1)⁻¹) * P.coeff n) P).coeff n = 0 := by
  rw [taylor_coeff_pred hP hd]
  apply Subtype.ext
  funext v
  simp only [Subring.coe_add, Subring.coe_mul, Pi.add_apply, Pi.mul_apply, cst_apply,
    ZeroMemClass.coe_zero, Pi.zero_apply]
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  have e1 : ((n : Ran) : ℝ → ℝ) v = n := by rw [← evAt_apply, map_natCast]
  have e2 : ((1 : Ran) : ℝ → ℝ) v = 1 := rfl
  rw [e1, e2]
  field_simp
  ring

lemma taylor_monic {R : Type*} [CommRing R] {p : R[X]} (hp : p.Monic) (r : R) :
    (taylor r p).Monic := by
  rw [Monic, leadingCoeff_taylor]
  exact hp

end

end Pui
end SubanalyticLib

/-! SubanalyticLib CS-5b: Newton-polygon rescaling for real Puiseux (appended to L5p_Pui). -/

namespace SubanalyticLib
namespace Pui

noncomputable section

/-- Monic polynomial with prescribed lower coefficients. -/
def mkMonic (d : ℕ) (b : Fin d → Ran) : Ran[X] := X ^ d + ∑ i : Fin d, C (b i) * X ^ (i : ℕ)

lemma mkMonic_monic (d : ℕ) (b : Fin d → Ran) : (mkMonic d b).Monic :=
  monic_X_pow_add (degree_sum_fin_lt b)

lemma mkMonic_natDegree (d : ℕ) (b : Fin d → Ran) : (mkMonic d b).natDegree = d := by
  unfold mkMonic
  rw [natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  rw [degree_X_pow]
  exact degree_sum_fin_lt b

lemma mkMonic_coeff (d : ℕ) (b : Fin d → Ran) {j : ℕ} (hj : j < d) :
    (mkMonic d b).coeff j = b ⟨j, hj⟩ := by
  unfold mkMonic
  rw [coeff_add, coeff_X_pow, if_neg hj.ne, zero_add, finset_sum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single ⟨j, hj⟩]
  · simp
  · intro i _ hi
    rw [if_neg]
    intro h
    exact hi (Fin.ext h.symm)
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma eval_pv_mkMonic (d : ℕ) (b : Fin d → Ran) (v z : ℝ) :
    (pv (mkMonic d b) v).eval z = z ^ d + ∑ i : Fin d, (b i : ℝ → ℝ) v * z ^ (i : ℕ) := by
  simp [pv, mkMonic, eval_map, eval₂_finset_sum]

/-- Order of vanishing of a non-flat analytic germ. -/
lemma exists_order {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) (hne : ¬ ∀ᶠ v in 𝓝 (0 : ℝ), f v = 0) :
    ∃ m : ℕ, ∃ h : ℝ → ℝ, AnalyticAt ℝ h 0 ∧ h 0 ≠ 0 ∧ ∀ᶠ u in 𝓝 (0 : ℝ), f u = u ^ m * h u := by
  have hne' : analyticOrderAt f 0 ≠ ⊤ := fun h => hne (analyticOrderAt_eq_top.mp h)
  obtain ⟨h, hh, h0, hev⟩ :=
    hf.analyticOrderAt_eq_natCast.mp (Nat.cast_analyticOrderNatAt hne').symm
  exact ⟨_, h, hh, h0, hev.mono fun u hu => by rw [hu, sub_zero, smul_eq_mul]⟩

/-- Newton rescaling: `a_j (v ^ N) = v ^ (p (d - j)) b_j v` with some `b_j (0) ≠ 0`. -/
lemma rescale {d : ℕ} (a : Fin d → Ran)
    (hnz : ∃ j, ¬ ∀ᶠ v in 𝓝 (0 : ℝ), (a j : ℝ → ℝ) v = 0) :
    ∃ N : ℕ, 0 < N ∧ ∃ p : ℕ, ∃ b : Fin d → Ran,
      (∀ j, a j = 0 → b j = 0) ∧ (∃ j, (b j : ℝ → ℝ) 0 ≠ 0) ∧
      ∀ᶠ v in 𝓝 (0 : ℝ), ∀ j : Fin d,
        (a j : ℝ → ℝ) (v ^ N) = v ^ (p * (d - j)) * (b j : ℝ → ℝ) v := by
  classical
  have hdat : ∀ j : Fin d, ∃ m : ℕ, ∃ h : ℝ → ℝ, AnalyticAt ℝ h 0 ∧
      (h 0 ≠ 0 ∨ h = fun _ => 0) ∧ (a j = 0 → h = fun _ => 0) ∧
      ((h = fun _ => 0) → ∀ᶠ u in 𝓝 (0 : ℝ), (a j : ℝ → ℝ) u = 0) ∧
      ∀ᶠ u in 𝓝 (0 : ℝ), (a j : ℝ → ℝ) u = u ^ m * h u := by
    intro j
    by_cases hz : ∀ᶠ u in 𝓝 (0 : ℝ), (a j : ℝ → ℝ) u = 0
    · exact ⟨0, fun _ => 0, analyticAt_const, Or.inr rfl, fun _ => rfl, fun _ => hz,
        hz.mono fun u hu => by simp [hu]⟩
    · obtain ⟨m, h, hh, h0, hev⟩ := exists_order (analyticAt_coe (a j)) hz
      refine ⟨m, h, hh, Or.inl h0, fun ha => ?_, fun hh0 => ?_, hev⟩
      · exact absurd (Filter.Eventually.of_forall fun u => by rw [ha]; rfl) hz
      · exact absurd (congrFun hh0 0) h0
  choose m h hh hor hzero hzev hev using hdat
  set S := Finset.univ.filter (fun j : Fin d => h j 0 ≠ 0) with hSdef
  have hS : S.Nonempty := by
    obtain ⟨j, hj⟩ := hnz
    refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun h0 => hj ?_⟩⟩
    rcases hor j with h1 | h1
    · exact absurd h0 h1
    · exact hzev j h1
  set N := d.factorial with hNdef
  have hN : 0 < N := Nat.factorial_pos d
  have hdvd : ∀ j : Fin d, (d - j) ∣ N := fun j => by
    have := j.isLt
    exact Nat.dvd_factorial (by omega) (by omega)
  set r : Fin d → ℕ := fun j => m j * (N / (d - j)) with hrdef
  set p := S.inf' hS r with hpdef
  have hr : ∀ j, r j * (d - j) = m j * N := fun j => by
    simp only [hrdef]
    rw [mul_assoc, Nat.div_mul_cancel (hdvd j)]
  have hp : ∀ j ∈ S, p * (d - j) ≤ m j * N := fun j hj => by
    rw [← hr j]
    exact Nat.mul_le_mul_right _ (Finset.inf'_le _ hj)
  obtain ⟨j0, hj0S, hj0⟩ := Finset.exists_mem_eq_inf' hS r
  obtain ⟨bf, hbfdef⟩ : ∃ bf : Fin d → ℝ → ℝ, bf = fun j => if j ∈ S then
      (fun v => v ^ (m j * N - p * (d - j)) * h j (v ^ N)) else fun _ => 0 := ⟨_, rfl⟩
  have hbf : ∀ j, AnalyticAt ℝ (bf j) 0 := by
    intro j
    rw [hbfdef]
    dsimp only
    split_ifs
    · exact ((analyticAt_id).pow _).mul (analyticAt_comp_pow (hh j) hN)
    · exact analyticAt_const
  refine ⟨N, hN, p, fun j => ⟨bf j, hbf j⟩, ?_, ⟨j0, ?_⟩, ?_⟩
  · intro j ha
    apply Subtype.ext
    have hjS : j ∉ S := by
      intro hjS
      have := (Finset.mem_filter.mp hjS).2
      rw [hzero j ha] at this
      exact this rfl
    show bf j = fun _ => 0
    rw [hbfdef]
    dsimp only
    rw [if_neg hjS]
  · show bf j0 0 ≠ 0
    rw [hbfdef]
    dsimp only
    rw [if_pos hj0S]
    have he : m j0 * N - p * (d - j0) = 0 := by
      rw [← hr j0, ← hj0]
      exact Nat.sub_self _
    rw [he, pow_zero, one_mul, zero_pow hN.ne']
    exact (Finset.mem_filter.mp hj0S).2
  · have hT : Tendsto (fun v : ℝ => v ^ N) (𝓝 0) (𝓝 0) := by
      have := (continuous_pow N).tendsto (0 : ℝ)
      rwa [zero_pow hN.ne'] at this
    have hall : ∀ᶠ v in 𝓝 (0 : ℝ), ∀ j, (a j : ℝ → ℝ) (v ^ N) = (v ^ N) ^ m j * h j (v ^ N) := by
      rw [Filter.eventually_all]
      intro j
      exact hT.eventually (hev j)
    filter_upwards [hall] with v hv j
    rw [hv j]
    show (v ^ N) ^ m j * h j (v ^ N) = v ^ (p * (d - j)) * bf j v
    rw [hbfdef]
    by_cases hjS : j ∈ S
    · dsimp only
      rw [if_pos hjS]
      rw [← pow_mul, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' (hp j hjS), mul_comm N (m j)]
    · dsimp only
      rw [if_neg hjS]
      have h0 : h j = fun _ => 0 := by
        rcases hor j with h1 | h1
        · exact absurd (show j ∈ S from Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩) hjS
        · exact h1
      rw [h0]
      simp

/-- The rescaled polynomial carries the branch property back. -/
lemma branches_of_rescale {P Q : Ran[X]} {N p L : ℕ} (hL : 0 < L)
    (hid : ∀ᶠ v in 𝓝 (0 : ℝ), ∀ z, (pv P (v ^ N)).eval (v ^ p * z) =
      v ^ (p * P.natDegree) * (pv Q v).eval z)
    (hB : BranchesAt Q L) : BranchesAt P (N * L) := by
  obtain ⟨Φ, hfin, han, hev⟩ := hB
  refine ⟨(fun φ => fun w => w ^ (L * p) * φ w) '' Φ, hfin.image _, ?_, ?_⟩
  · rintro _ ⟨φ, hφ, rfl⟩
    exact ((analyticAt_id).pow _).mul (han φ hφ)
  · filter_upwards [((tendsto_pow_nhdsGT hL).mono_right nhdsWithin_le_nhds).eventually hid, hev,
      self_mem_nhdsWithin] with w hw hwB hw0 y
    have hw0' : (0 : ℝ) < w := hw0
    have hv : (0 : ℝ) < w ^ L := pow_pos hw0' L
    have hvp : (w ^ L) ^ p ≠ 0 := pow_ne_zero _ hv.ne'
    have e1 : w ^ (N * L) = (w ^ L) ^ N := by rw [← pow_mul, mul_comm]
    have key : (pv P (w ^ (N * L))).IsRoot y ↔ (pv Q (w ^ L)).IsRoot (y / (w ^ L) ^ p) := by
      rw [e1, IsRoot.def, IsRoot.def]
      have h1 := hw (y / (w ^ L) ^ p)
      have hy' : (w ^ L) ^ p * (y / (w ^ L) ^ p) = y := by field_simp
      rw [hy'] at h1
      rw [h1, mul_eq_zero, or_iff_right (pow_ne_zero _ hv.ne')]
    rw [key, hwB]
    constructor
    · rintro ⟨φ, hφ, he⟩
      refine ⟨_, ⟨φ, hφ, rfl⟩, ?_⟩
      show w ^ (L * p) * φ w = y
      rw [he, pow_mul]
      field_simp
    · rintro ⟨_, ⟨φ, hφ, rfl⟩, he⟩
      refine ⟨φ, hφ, ?_⟩
      have he' : w ^ (L * p) * φ w = y := he
      rw [← he', pow_mul]
      field_simp

/-- If all lower coefficients are flat at `0`, the only real root is `0`. -/
lemma branches_of_eventually_zero {P : Ran[X]} (hP : P.Monic) (hd : 0 < P.natDegree)
    (hz : ∀ j < P.natDegree, ∀ᶠ v in 𝓝 (0 : ℝ), (P.coeff j : ℝ → ℝ) v = 0) : BranchesAt P 1 := by
  refine ⟨{fun _ => 0}, Set.finite_singleton _, ?_, ?_⟩
  · rintro φ rfl
    exact analyticAt_const
  · have hall : ∀ᶠ v in 𝓝 (0 : ℝ), ∀ j ∈ Finset.range P.natDegree,
        (P.coeff j : ℝ → ℝ) v = 0 :=
      (Finset.range P.natDegree).eventually_all.mpr fun j hj => hz j (Finset.mem_range.mp hj)
    filter_upwards [nhdsWithin_le_nhds hall] with v hv y
    rw [pow_one, IsRoot.def, eval_pv hP,
      Finset.sum_eq_zero (fun j hj => by rw [hv j hj, zero_mul]), add_zero,
      pow_eq_zero_iff hd.ne']
    constructor
    · rintro rfl
      exact ⟨_, rfl, rfl⟩
    · rintro ⟨φ, hφ, h⟩
      rw [Set.mem_singleton_iff] at hφ
      rw [← h, hφ]

/-- A monic polynomial of degree `n + 1` with vanishing `X ^ n` coefficient and some nonzero lower
coefficient has no real root of full multiplicity. -/
lemma rootMultiplicity_lt {q : ℝ[X]} {n : ℕ} (hq : q.Monic) (hd : q.natDegree = n + 1)
    (hn : q.coeff n = 0) (hj : ∃ j < n + 1, q.coeff j ≠ 0) (c : ℝ) :
    q.rootMultiplicity c < n + 1 := by
  by_contra hge
  push Not at hge
  have hdvd : (X - C c) ^ (n + 1) ∣ q := (le_rootMultiplicity_iff hq.ne_zero).mp hge
  have hm : ((X - C c) ^ (n + 1)).Monic := (monic_X_sub_C c).pow _
  have heq : q = (X - C c) ^ (n + 1) :=
    eq_of_monic_of_dvd_of_natDegree_le hm hq hdvd
      (by rw [hd, natDegree_pow, natDegree_X_sub_C, mul_one])
  have ht : taylor c q = X ^ (n + 1) := by
    rw [heq, taylor_apply, pow_comp, sub_comp, X_comp, C_comp, add_sub_cancel_right]
  have h1 := taylor_coeff_pred hq hd c
  rw [ht, coeff_X_pow, if_neg (by omega), hn, zero_add] at h1
  have hc : c = 0 := by
    have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
    exact (mul_eq_zero.mp h1.symm).resolve_left hne
  rw [hc, map_zero, sub_zero] at heq
  obtain ⟨j, hj, hne⟩ := hj
  rw [heq, coeff_X_pow, if_neg (by omega)] at hne
  exact hne rfl

end

end Pui
end SubanalyticLib

/-! SubanalyticLib CS-5c: real Newton–Puiseux, assembly by induction on the degree, from the local
Weierstrass factorization `LocalFactor` (proved separately from L3G's `ev_weierstrass_prep`). -/

namespace SubanalyticLib
namespace Pui

noncomputable section

/-- Local factorization at a real root `c` of multiplicity `m` of `pv Q 0`: near `(0, c)` the zeros
of `Q` are those of a monic `R` of degree `m` with `pv R 0 = X ^ m` (Weierstrass preparation). -/
def LocalFactor : Prop :=
  ∀ (Q : Ran[X]) (c : ℝ), Q.Monic → 0 < (pv Q 0).rootMultiplicity c →
    ∃ R : Ran[X], R.Monic ∧ R.natDegree = (pv Q 0).rootMultiplicity c ∧
      pv R 0 = X ^ R.natDegree ∧ ∃ δ > 0, ∀ᶠ v in 𝓝 (0 : ℝ), ∀ z, |z| < δ →
        ((pv Q v).IsRoot (c + z) ↔ (pv R v).IsRoot z)

lemma rescale_identity {d N p : ℕ} {P : Ran[X]} (hP : P.Monic) (hd : P.natDegree = d)
    (b : Fin d → Ran) (v : ℝ)
    (hv : ∀ j : Fin d, (P.coeff j : ℝ → ℝ) (v ^ N) = v ^ (p * (d - j)) * (b j : ℝ → ℝ) v)
    (z : ℝ) :
    (pv P (v ^ N)).eval (v ^ p * z) = v ^ (p * d) * (pv (mkMonic d b) v).eval z := by
  rw [eval_pv hP, eval_pv_mkMonic, hd,
    ← Fin.sum_univ_eq_sum_range (fun j => (P.coeff j : ℝ → ℝ) (v ^ N) * (v ^ p * z) ^ j) d,
    mul_add, Finset.mul_sum]
  congr 1
  · rw [mul_pow, ← pow_mul]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [hv j, mul_pow, ← pow_mul]
    have e : p * (d - j) + p * j = p * d := by rw [← mul_add, Nat.sub_add_cancel j.isLt.le]
    calc v ^ (p * (d - j)) * (b j : ℝ → ℝ) v * (v ^ (p * j) * z ^ (j : ℕ))
        = (v ^ (p * (d - j)) * v ^ (p * j)) * ((b j : ℝ → ℝ) v * z ^ (j : ℕ)) := by ring
      _ = _ := by rw [← pow_add, e]

/-- Gluing the local branches at the real roots of `pv Q 0`. -/
lemma branches_glue (hLF : LocalFactor) {Q : Ran[X]} (hQ : Q.Monic)
    (ih : ∀ R : Ran[X], R.Monic → R.natDegree < Q.natDegree → ∃ q, 0 < q ∧ BranchesAt R q)
    (hmult : ∀ c, (pv Q 0).rootMultiplicity c < Q.natDegree) : ∃ L, 0 < L ∧ BranchesAt Q L := by
  classical
  have hQ0 : pv Q 0 ≠ 0 := (pv_monic hQ 0).ne_zero
  set C := (pv Q 0).roots.toFinset with hC
  have hmemC : ∀ c, c ∈ C ↔ (pv Q 0).IsRoot c := fun c => by
    rw [hC, Multiset.mem_toFinset, mem_roots hQ0]
  have hdat : ∀ c ∈ C, ∃ R : Ran[X], ∃ δc : ℝ, 0 < δc ∧ ∃ qc : ℕ, 0 < qc ∧ BranchesAt R qc ∧
      (∀ᶠ v in 𝓝 (0 : ℝ), ∀ z, |z| < δc → ((pv Q v).IsRoot (c + z) ↔ (pv R v).IsRoot z)) ∧
      (∀ᶠ v in 𝓝 (0 : ℝ), ∀ z, (pv R v).IsRoot z → |z| < δc) := by
    intro c hc
    have hpos : 0 < (pv Q 0).rootMultiplicity c :=
      (rootMultiplicity_pos hQ0).mpr ((hmemC c).mp hc)
    obtain ⟨R, hRm, hRd, hR0, δc, hδc, hloc⟩ := hLF Q c hQ hpos
    obtain ⟨qc, hqc, hB⟩ := ih R hRm (by rw [hRd]; exact hmult c)
    refine ⟨R, δc, hδc, qc, hqc, hB, hloc, ?_⟩
    filter_upwards [roots_near hRm hδc] with v hv z hz
    obtain ⟨c', hc', hzc⟩ := hv z hz
    have hc'0 : c' = 0 := by
      rw [hR0, IsRoot.def, eval_pow, eval_X] at hc'
      exact (pow_eq_zero_iff (n := R.natDegree) (by omega)).mp hc'
    rw [hc'0, sub_zero] at hzc
    exact hzc
  choose! R δc hδc qc hqc hB hloc hsmall using hdat
  set L := ∏ c ∈ C, qc c with hLdef
  have hL : 0 < L := Finset.prod_pos fun c hc => hqc c hc
  have hBL : ∀ c ∈ C, BranchesAt (R c) L := fun c hc =>
    (hB c hc).of_dvd hL (Finset.dvd_prod_of_mem _ hc)
  choose! Φc hfin han hev using hBL
  obtain ⟨δ, hδ, hδle⟩ : ∃ δ > 0, ∀ c ∈ C, δ ≤ δc c := by
    by_cases hCn : C.Nonempty
    · exact ⟨C.inf' hCn δc, (Finset.lt_inf'_iff hCn).mpr fun c hc => hδc c hc,
        fun c hc => Finset.inf'_le _ hc⟩
    · exact ⟨1, one_pos, fun c hc => absurd ⟨c, hc⟩ hCn⟩
  refine ⟨L, hL, ⋃ c ∈ C, (fun φ => fun w => c + φ w) '' Φc c, ?_, ?_, ?_⟩
  · exact Set.Finite.biUnion C.finite_toSet fun c hc => (hfin c hc).image _
  · intro ψ hψ
    rw [Set.mem_iUnion₂] at hψ
    obtain ⟨c, hc, φ, hφ, rfl⟩ := hψ
    exact analyticAt_const.add (han c hc φ hφ)
  · have hTL : Tendsto (fun w : ℝ => w ^ L) (𝓝[>] 0) (𝓝 0) :=
      (tendsto_pow_nhdsGT hL).mono_right nhdsWithin_le_nhds
    filter_upwards [C.eventually_all.mpr hev, hTL.eventually (C.eventually_all.mpr hloc),
      hTL.eventually (C.eventually_all.mpr hsmall), hTL.eventually (roots_near hQ hδ)]
      with w h1 h2 h3 h4 y
    constructor
    · intro hy
      obtain ⟨c, hc0, hyc⟩ := h4 y hy
      have hc : c ∈ C := (hmemC c).mpr hc0
      have hz : |y - c| < δc c := lt_of_lt_of_le hyc (hδle c hc)
      have hR : (pv (R c) (w ^ L)).IsRoot (y - c) :=
        (h2 c hc (y - c) hz).mp (by rw [show c + (y - c) = y by ring]; exact hy)
      obtain ⟨φ, hφ, hφw⟩ := (h1 c hc (y - c)).mp hR
      refine ⟨fun w => c + φ w, Set.mem_iUnion₂.mpr ⟨c, hc, φ, hφ, rfl⟩, ?_⟩
      show c + φ w = y
      rw [hφw]
      ring
    · rintro ⟨ψ, hψ, rfl⟩
      rw [Set.mem_iUnion₂] at hψ
      obtain ⟨c, hc, φ, hφ, rfl⟩ := hψ
      have hR : (pv (R c) (w ^ L)).IsRoot (φ w) := (h1 c hc (φ w)).mpr ⟨φ, hφ, rfl⟩
      exact (h2 c hc (φ w) (h3 c hc (φ w) hR)).mpr hR

/-- **Real Newton–Puiseux in one parameter** (from `LocalFactor`): the real roots of a monic
polynomial with coefficients analytic at `0` are, for `u = v ^ q`, `v > 0` small, exactly the values
of finitely many analytic germs in `v`. -/
theorem puiseux_of_localFactor (hLF : LocalFactor) :
    ∀ (d : ℕ) (P : Ran[X]), P.Monic → P.natDegree = d → ∃ q, 0 < q ∧ BranchesAt P q := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro P hP hPd
  rcases d with _ | n
  · refine ⟨1, one_pos, ∅, Set.finite_empty, by simp, Filter.Eventually.of_forall fun v y => ?_⟩
    have h1 : P = 1 := eq_one_of_monic_natDegree_zero hP hPd
    simp [h1, pv]
  · set s : Ran := cst (-((n : ℝ) + 1)⁻¹) * P.coeff n with hs
    set P1 := taylor s P with hP1
    have hP1m : P1.Monic := taylor_monic hP s
    have hP1d : P1.natDegree = n + 1 := by rw [hP1, natDegree_taylor, hPd]
    have hP1n : P1.coeff n = 0 := tschirnhaus hP hPd
    suffices h : ∃ q, 0 < q ∧ BranchesAt P1 q by
      obtain ⟨q, hq, hB⟩ := h
      exact ⟨q, hq, hB.of_taylor s hq⟩
    by_cases hz : ∀ j < P1.natDegree, ∀ᶠ v in 𝓝 (0 : ℝ), (P1.coeff j : ℝ → ℝ) v = 0
    · exact ⟨1, one_pos, branches_of_eventually_zero hP1m (by omega) hz⟩
    obtain ⟨j1, hj1, hj1'⟩ : ∃ j, j < P1.natDegree ∧
        ¬ ∀ᶠ v in 𝓝 (0 : ℝ), (P1.coeff j : ℝ → ℝ) v = 0 := by
      by_contra hc
      push Not at hc
      exact hz hc
    obtain ⟨N, hN, p, b, hb0, ⟨j0, hj0⟩, hid⟩ :=
      rescale (d := n + 1) (fun j => P1.coeff j) ⟨⟨j1, by omega⟩, hj1'⟩
    set Q := mkMonic (n + 1) b with hQ
    have hQm : Q.Monic := mkMonic_monic _ _
    have hQd : Q.natDegree = n + 1 := mkMonic_natDegree _ _
    have hmult : ∀ c, (pv Q 0).rootMultiplicity c < Q.natDegree := by
      intro c
      rw [hQd]
      refine rootMultiplicity_lt (pv_monic hQm 0) (by rw [natDegree_pv hQm, hQd]) ?_
        ⟨j0, j0.isLt, ?_⟩ c
      · rw [coeff_pv, hQ, mkMonic_coeff _ _ (Nat.lt_succ_self n),
          hb0 ⟨n, Nat.lt_succ_self n⟩ hP1n]
        rfl
      · rw [coeff_pv, hQ, mkMonic_coeff _ _ j0.isLt]
        exact hj0
    have hid' : ∀ᶠ v in 𝓝 (0 : ℝ), ∀ z, (pv P1 (v ^ N)).eval (v ^ p * z) =
        v ^ (p * P1.natDegree) * (pv Q v).eval z := by
      filter_upwards [hid] with v hv z
      rw [hP1d]
      exact rescale_identity hP1m hP1d b v hv z
    obtain ⟨L, hL, hB⟩ := branches_glue hLF hQm
      (fun R hR hlt => ih _ (by rw [hQd] at hlt; exact hlt) R hR rfl) hmult
    exact ⟨N * L, Nat.mul_pos hN hL, branches_of_rescale hL hid' hB⟩

end

end Pui
end SubanalyticLib

/-! SubanalyticLib CS-5d: `LocalFactor` from convergent Weierstrass preparation (L3G), hence the
real Newton–Puiseux theorem `puiseux`. Appended after L3G + L5s_WP2 + L5R (MvPowerSeries names are
qualified here because `Polynomial` is open). -/

namespace SubanalyticLib
namespace Pui

noncomputable section

/-- The two-variable function `(v, z) ↦ (pv Q v)(c + z)`. -/
def F2 (Q : Ran[X]) (c : ℝ) (x : Fin 2 → ℝ) : ℝ := (pv Q (x 0)).eval (c + x 1)

lemma analyticAt_F2 (Q : Ran[X]) (c : ℝ) : AnalyticAt ℝ (F2 Q c) 0 := by
  set g : ℕ → (Fin 2 → ℝ) → ℝ := fun k x => (Q.coeff k : ℝ → ℝ) (x 0) * (c + x 1) ^ k with hg
  have h : F2 Q c = ∑ k ∈ Finset.range (Q.natDegree + 1), g k := by
    funext x
    rw [Finset.sum_apply]
    simp only [F2, hg]
    rw [eval_eq_sum_range' (n := Q.natDegree + 1)]
    · simp only [coeff_pv]
    · calc (pv Q (x 0)).natDegree ≤ Q.natDegree := natDegree_map_le
        _ < Q.natDegree + 1 := Nat.lt_succ_self _
  rw [h]
  refine Finset.analyticAt_sum _ fun k _ => ?_
  have h0 : AnalyticAt ℝ (fun x : Fin 2 → ℝ => x 0) 0 :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).analyticAt _
  have h1 : AnalyticAt ℝ (fun x : Fin 2 → ℝ => x 1) 0 :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).analyticAt _
  exact ((analyticAt_coe (Q.coeff k)).comp_of_eq h0 (by simp)).mul
    ((analyticAt_const.add h1).pow k)

lemma abs_single_le {ρ s : ℝ} (hρ : 0 ≤ ρ) (hs : |s| ≤ ρ) (i : Fin 2) :
    |(Pi.single 1 s : Fin 2 → ℝ) i| ≤ ρ := by
  by_cases hi : i = 1
  · subst hi
    simpa using hs
  · simp [Pi.single_apply, hi, hρ]

/-- On the `y`-axis the coefficients of a convergent series agree with those of the polynomial it
equals there. -/
lemma axis_coeff_eq {a : MvPowerSeries (Fin 2) ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (ha : Conv (fun _ => ρ) a) (T : ℝ[X])
    (hev : ∀ s : ℝ, |s| ≤ ρ → ev a (Pi.single 1 s) = T.eval s) (j : ℕ) :
    MvPowerSeries.coeff (Finsupp.single 1 j) a = T.coeff j := by
  classical
  have hw : ∀ i : Fin 2, 0 ≤ (fun _ => ρ) i := fun _ => hρ.le
  set G : MvPowerSeries (Fin 2) ℝ := ∑ k ∈ Finset.range (T.natDegree + 1),
    MvPowerSeries.X 1 ^ k * MvPowerSeries.C (T.coeff k) with hGdef
  have hG : Conv (fun _ => ρ) G := (conv_finset_sum hw _ _ (fun k _ =>
    Conv.mul hw (Conv.pow hw (conv_X hw 1) k) (conv_C _))).1
  have hcoeffG : ∀ j, MvPowerSeries.coeff (Finsupp.single 1 j) G = T.coeff j := by
    intro j
    rw [hGdef, map_sum]
    simp only [MvPowerSeries.coeff_mul_C, MvPowerSeries.coeff_X_pow,
      (Finsupp.single_injective (1 : Fin 2)).eq_iff, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_range]
    split_ifs with hj
    · rfl
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
  have hevG : ∀ s, |s| ≤ ρ → ev G (Pi.single 1 s) = T.eval s := by
    intro s hs
    rw [hGdef, ev_sum_X_pow_mul 1 hw (abs_single_le hρ.le hs) _ _ (fun j => conv_C _),
      eval_eq_sum_range]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ev_C]
    simp [mul_comm]
  set D := a - G with hDdef
  have hD : Conv (fun _ => ρ) D := Conv.sub hw ha hG
  have hDz : ∀ j, MvPowerSeries.coeff (Finsupp.single 1 j) D = 0 := by
    by_contra hne
    push Not at hne
    have hj0 := Nat.find_spec hne
    have hlt : ∀ j < Nat.find hne, MvPowerSeries.coeff (Finsupp.single 1 j) D = 0 := fun j hj => by
      by_contra h
      exact Nat.find_min hne hj h
    obtain ⟨δ, hδ, hb⟩ := axis_lower_bound 1 (fun _ => hρ) hD (Nat.find hne) hlt hj0
    have hs0 : 0 < min δ ρ := lt_min hδ hρ
    have h1 := hb (min δ ρ) hs0.le (min_le_left _ _)
    have hsρ : |min δ ρ| ≤ ρ := by rw [abs_of_pos hs0]; exact min_le_right _ _
    have hzero : ev D (Pi.single 1 (min δ ρ)) = 0 := by
      rw [hDdef, ev_sub (abs_single_le hρ.le hsρ) ha hG, hev _ hsρ, hevG _ hsρ, sub_self]
    rw [hzero, abs_zero] at h1
    have : 0 < |MvPowerSeries.coeff (Finsupp.single 1 (Nat.find hne)) D| / 2 *
        (min δ ρ) ^ (Nat.find hne) :=
      mul_pos (div_pos (abs_pos.mpr hj0) two_pos) (pow_pos hs0 _)
    linarith
  have h := hDz j
  rw [hDdef, map_sub, hcoeffG, sub_eq_zero] at h
  exact h

lemma fin2_update (v z : ℝ) : Function.update (![v, z] : Fin 2 → ℝ) 1 0 = Pi.single 0 v := by
  funext i
  fin_cases i <;> simp [Pi.single_apply]

/-- **Local factorization** at a real root (Weierstrass preparation in two variables). -/
theorem localFactor : LocalFactor := by
  intro Q c hQ hpos
  set m := (pv Q 0).rootMultiplicity c with hm
  set T := taylor c (pv Q 0) with hTdef
  have hQ0 : pv Q 0 ≠ 0 := (pv_monic hQ 0).ne_zero
  have hT0 : T ≠ 0 := by rw [Ne, hTdef, taylor_eq_zero]; exact hQ0
  have hmT : m = T.natTrailingDegree := by rw [hm, rootMultiplicity_eq_natTrailingDegree, hTdef, taylor_apply]
  obtain ⟨a, ρ, hρ, ha, hFa⟩ := exists_conv_of_analyticAt (analyticAt_F2 Q c)
  have hw0 : ∀ i : Fin 2, 0 < (fun _ => ρ) i := fun _ => hρ
  have hnorm : ∀ x : Fin 2 → ℝ, (∀ i, |x i| ≤ ρ) → ‖x‖ ≤ ρ := fun x hx =>
    (pi_norm_le_iff_of_nonneg hρ.le).mpr fun i => by rw [Real.norm_eq_abs]; exact hx i
  have hev : ∀ s : ℝ, |s| ≤ ρ → ev a (Pi.single 1 s) = T.eval s := by
    intro s hs
    rw [← hFa _ (hnorm _ (abs_single_le hρ.le hs)), zero_add, hTdef, taylor_eval]
    simp [F2, add_comm]
  have hax := axis_coeff_eq hρ ha T hev
  have hreg : ∀ j < m, MvPowerSeries.coeff (Finsupp.single 1 j) a = 0 := fun j hj => by
    rw [hax]
    exact coeff_eq_zero_of_lt_natTrailingDegree (by omega)
  have hd : MvPowerSeries.coeff (Finsupp.single 1 m) a ≠ 0 := by
    rw [hax, hmT]
    exact trailingCoeff_nonzero_iff_nonzero.mpr hT0
  obtain ⟨w, hw, hwle, q, r, hq, hr, hr0, hrc, hWP⟩ := ev_weierstrass_prep2 1 hw0 m ha hreg hd
  have hw' : ∀ i, 0 ≤ w i := fun i => (hw i).le
  have hsl : ∀ j, Conv w (yslice 1 j r) := fun j => Conv.low 1 hw' 1 (Conv.hat 1 hw' (hw 1) j hr)
  have hslA : ∀ j, AnalyticAt ℝ (fun v : ℝ => ev (yslice 1 j r) (Pi.single 0 v)) 0 := by
    intro j
    obtain ⟨r0, hr0pos, hA⟩ := analyticAt_ev_zero hw (hsl j)
    have hA0 : AnalyticAt ℝ (ev (yslice 1 j r)) 0 := hA 0 (by rw [norm_zero]; exact hr0pos)
    have hL : AnalyticAt ℝ (fun v : ℝ => (Pi.single 0 v : Fin 2 → ℝ)) 0 :=
      (ContinuousLinearMap.single ℝ (fun _ : Fin 2 => ℝ) 0).analyticAt _
    exact hA0.comp_of_eq hL (by simp)
  set rj : Fin m → Ran := fun j => ⟨fun v => -ev (yslice 1 j r) (Pi.single 0 v), (hslA j).neg⟩
    with hrj
  have hrj0 : ∀ j : Fin m, (rj j : ℝ → ℝ) 0 = 0 := by
    intro j
    show -ev (yslice 1 j r) (Pi.single 0 0) = 0
    rw [Pi.single_zero, ev_zero_pt, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      coeff_yslice]
    simp [hrc j j.isLt]
  set R := mkMonic m rj with hR
  have hRm : R.Monic := mkMonic_monic _ _
  have hRd : R.natDegree = m := mkMonic_natDegree _ _
  refine ⟨R, hRm, hRd, ?_, w 1, hw 1, ?_⟩
  · ext k
    rw [coeff_pv, hRd, coeff_X_pow]
    rcases lt_trichotomy k m with hk | hk | hk
    · rw [hR, mkMonic_coeff _ _ hk, if_neg hk.ne, hrj0]
    · subst hk
      rw [if_pos rfl, ← hRd, hRm.coeff_natDegree]
      rfl
    · rw [if_neg hk.ne', coeff_eq_zero_of_natDegree_lt (by omega)]
      rfl
  · filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (hw 0)] with v hv z hz
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hv
    have hx : ∀ i, |(![v, z] : Fin 2 → ℝ) i| ≤ w i := by
      intro i
      fin_cases i
      · simpa using hv.le
      · simpa using hz.le
    obtain ⟨hq0, heq⟩ := hWP _ hx
    have hxρ : ‖(![v, z] : Fin 2 → ℝ)‖ ≤ ρ := hnorm _ fun i => (hx i).trans (hwle i)
    have hFx : ev a ![v, z] = (pv Q v).eval (c + z) := by
      rw [← hFa _ hxρ, zero_add]
      simp [F2]
    have hrx : ev r ![v, z] = ∑ j ∈ Finset.range m, z ^ j * ev (yslice 1 j r) (Pi.single 0 v) := by
      rw [ev_eq_sum_yslice 1 m hw' (hw 1) hr hr0 hx]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← ev_yslice_update 1 j r ![v, z] 0, fin2_update]
      simp
    have hRv : (pv R v).eval z = ev q ![v, z] * (pv Q v).eval (c + z) := by
      rw [hR, eval_pv_mkMonic, ← hFx]
      have h2 : z ^ m = ev q ![v, z] * ev a ![v, z] + ev r ![v, z] := by simpa using heq
      rw [hrx] at h2
      have h3 : ∑ i : Fin m, (rj i : ℝ → ℝ) v * z ^ (i : ℕ) =
          -∑ j ∈ Finset.range m, z ^ j * ev (yslice 1 j r) (Pi.single 0 v) := by
        rw [← Fin.sum_univ_eq_sum_range (fun j => z ^ j * ev (yslice 1 j r) (Pi.single 0 v)) m,
          ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        show -ev (yslice 1 i r) (Pi.single 0 v) * z ^ (i : ℕ) = _
        ring
      rw [h3]
      linarith
    rw [IsRoot.def, IsRoot.def, hRv, mul_eq_zero, or_iff_right hq0]

/-- **Real Newton–Puiseux in one parameter.** -/
theorem puiseux (P : Ran[X]) (hP : P.Monic) : ∃ q, 0 < q ∧ BranchesAt P q :=
  puiseux_of_localFactor localFactor _ P hP rfl

end

end Pui
end SubanalyticLib


/-! SubanalyticLib CS-4: Thom's lemma (Bochnak–Coste–Roy, Real Algebraic Geometry, Prop. 2.5.4 /
Basu–Pollack–Roy Lemma 2.37). For a finite family of real polynomials closed under derivation,
every sign condition defines an order-connected set that is a point (subsingleton) or open,
i.e. empty, a point or an open interval. -/

open Polynomial Set

set_option linter.unusedSectionVars false

namespace SubanalyticLib

/-- The realization of the sign condition `ν` on the family `PP`. -/
def signSet (PP : Finset ℝ[X]) (ν : ℝ[X] → SignType) : Set ℝ :=
  {x : ℝ | ∀ p ∈ PP, SignType.sign (p.eval x) = ν p}

/-- Derivative-closed family. -/
def DerivClosed (PP : Finset ℝ[X]) : Prop := ∀ p ∈ PP, derivative p ∈ PP

theorem deriv_eval_poly (p : ℝ[X]) (x : ℝ) :
    deriv (fun y => p.eval y) x = (derivative p).eval x := Polynomial.deriv p

/-- A sign condition on a monotone function cuts an order-connected set to an order-connected set. -/
theorem ordConn_of_monotoneOn {A' : Set ℝ} (hA' : A'.OrdConnected) {f : ℝ → ℝ}
    (hm : MonotoneOn f A' ∨ AntitoneOn f A') (t : SignType) :
    (A' ∩ {x | SignType.sign (f x) = t}).OrdConnected := by
  constructor
  intro x hx z hz y hy
  have hyA : y ∈ A' := hA'.out hx.1 hz.1 hy
  refine ⟨hyA, ?_⟩
  have h1 : SignType.sign (f x) = t := hx.2
  have h2 : SignType.sign (f z) = t := hz.2
  show SignType.sign (f y) = t
  have hb : (f x ≤ f y ∧ f y ≤ f z) ∨ (f y ≤ f x ∧ f z ≤ f y) := by
    rcases hm with hm | hm
    · exact Or.inl ⟨hm hx.1 hyA hy.1, hm hyA hz.1 hy.2⟩
    · exact Or.inr ⟨hm hx.1 hyA hy.1, hm hyA hz.1 hy.2⟩
  rcases t with _ | _ | _
  · have e1 : f x = 0 := sign_eq_zero_iff.mp h1
    have e2 : f z = 0 := sign_eq_zero_iff.mp h2
    apply sign_eq_zero_iff.mpr
    rcases hb with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> exact le_antisymm (by linarith) (by linarith)
  · rw [SignType.neg_eq_neg_one, sign_eq_neg_one_iff] at h1 h2 ⊢
    rcases hb with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> linarith
  · rw [SignType.pos_eq_one, sign_eq_one_iff] at h1 h2 ⊢
    rcases hb with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> linarith

/-- One step: `A'` order-connected, `p` with `p'` of constant sign `s` on `A'`. -/
theorem thom_step {A' : Set ℝ} (hA' : A'.OrdConnected) (hA'o : A'.Subsingleton ∨ IsOpen A')
    (p : ℝ[X]) (s : SignType) (hs : ∀ x ∈ A', SignType.sign ((derivative p).eval x) = s)
    (t : SignType) :
    (A' ∩ {x | SignType.sign (p.eval x) = t}).OrdConnected ∧
      ((A' ∩ {x | SignType.sign (p.eval x) = t}).Subsingleton ∨
        IsOpen (A' ∩ {x | SignType.sign (p.eval x) = t})) := by
  have hconv : Convex ℝ A' := hA'.convex
  have hcont : ContinuousOn (fun y => p.eval y) A' := p.continuous.continuousOn
  have hint : ∀ x ∈ interior A', x ∈ A' := fun x hx => interior_subset hx
  have hdiff : DifferentiableOn ℝ (fun y => p.eval y) (interior A') :=
    p.differentiable.differentiableOn
  -- the subsingleton case is immediate
  have hsub : A'.Subsingleton → (A' ∩ {x | SignType.sign (p.eval x) = t}).Subsingleton :=
    fun h => h.anti inter_subset_left
  -- openness for strict signs
  have hopen : IsOpen A' → t ≠ 0 → IsOpen (A' ∩ {x | SignType.sign (p.eval x) = t}) := by
    intro ho ht
    rcases t with _ | _ | _
    · exact absurd rfl ht
    · have : {x : ℝ | SignType.sign (p.eval x) = SignType.neg} = (fun y => p.eval y) ⁻¹' Iio 0 := by
        ext x; simp [SignType.neg_eq_neg_one, sign_eq_neg_one_iff]
      rw [this]; exact ho.inter (isOpen_Iio.preimage p.continuous)
    · have : {x : ℝ | SignType.sign (p.eval x) = SignType.pos} = (fun y => p.eval y) ⁻¹' Ioi 0 := by
        ext x; simp [SignType.pos_eq_one, sign_eq_one_iff]
      rw [this]; exact ho.inter (isOpen_Ioi.preimage p.continuous)
  rcases s with _ | _ | _
  · -- p' = 0 on A': p constant on A'
    have hz : ∀ x ∈ A', (derivative p).eval x = 0 := by
      intro x hx; have := hs x hx; simpa [sign_eq_zero_iff] using this
    have hmono : MonotoneOn (fun y => p.eval y) A' :=
      monotoneOn_of_deriv_nonneg hconv hcont hdiff
        (fun x hx => by rw [deriv_eval_poly, hz x (hint x hx)])
    have hanti : AntitoneOn (fun y => p.eval y) A' :=
      antitoneOn_of_deriv_nonpos hconv hcont hdiff
        (fun x hx => by rw [deriv_eval_poly, hz x (hint x hx)])
    have hc : ∀ x ∈ A', ∀ y ∈ A', p.eval x = p.eval y := by
      intro x hx y hy
      rcases le_total x y with h | h
      · exact le_antisymm (hmono hx hy h) (hanti hx hy h)
      · exact le_antisymm (hanti hy hx h) (hmono hy hx h)
    by_cases hne : ∃ x₀ ∈ A', SignType.sign (p.eval x₀) = t
    · obtain ⟨x₀, hx₀, ht⟩ := hne
      have hA : A' ∩ {x | SignType.sign (p.eval x) = t} = A' := by
        ext x; constructor
        · exact fun h => h.1
        · intro hx; exact ⟨hx, by simp only [mem_setOf_eq]; rw [hc x hx x₀ hx₀]; exact ht⟩
      rw [hA]; exact ⟨hA', hA'o⟩
    · push Not at hne
      have hA : A' ∩ {x | SignType.sign (p.eval x) = t} = ∅ := by
        ext x; simp only [mem_empty_iff_false, iff_false]
        exact fun h => hne x h.1 h.2
      rw [hA]; exact ⟨ordConnected_empty, Or.inl subsingleton_empty⟩
  · -- p' < 0 on A': p strictly decreasing
    have hn : ∀ x ∈ A', (derivative p).eval x < 0 := by
      intro x hx; have := hs x hx; simpa [SignType.neg_eq_neg_one, sign_eq_neg_one_iff] using this
    have hsa : StrictAntiOn (fun y => p.eval y) A' :=
      strictAntiOn_of_deriv_neg hconv hcont (fun x hx => by rw [deriv_eval_poly]; exact hn x (hint x hx))
    refine ⟨ordConn_of_monotoneOn hA' (Or.inr hsa.antitoneOn) t, ?_⟩
    rcases hA'o with h | h
    · exact Or.inl (hsub h)
    · by_cases ht : t = 0
      · left; subst ht
        intro x hx y hy
        have e1 : p.eval x = 0 := by simpa [sign_eq_zero_iff] using hx.2
        have e2 : p.eval y = 0 := by simpa [sign_eq_zero_iff] using hy.2
        exact hsa.injOn hx.1 hy.1 (by simp only [e1, e2])
      · exact Or.inr (hopen h ht)
  · -- p' > 0 on A': p strictly increasing
    have hn : ∀ x ∈ A', 0 < (derivative p).eval x := by
      intro x hx; have := hs x hx; simpa [SignType.pos_eq_one, sign_eq_one_iff] using this
    have hsm : StrictMonoOn (fun y => p.eval y) A' :=
      strictMonoOn_of_deriv_pos hconv hcont (fun x hx => by rw [deriv_eval_poly]; exact hn x (hint x hx))
    refine ⟨ordConn_of_monotoneOn hA' (Or.inl hsm.monotoneOn) t, ?_⟩
    rcases hA'o with h | h
    · exact Or.inl (hsub h)
    · by_cases ht : t = 0
      · left; subst ht
        intro x hx y hy
        have e1 : p.eval x = 0 := by simpa [sign_eq_zero_iff] using hx.2
        have e2 : p.eval y = 0 := by simpa [sign_eq_zero_iff] using hy.2
        exact hsm.injOn hx.1 hy.1 (by simp only [e1, e2])
      · exact Or.inr (hopen h ht)

/-- **Thom's lemma.** -/
theorem eval_const {p : ℝ[X]} (h : p.natDegree = 0) (x : ℝ) : p.eval x = p.coeff 0 := by
  conv_lhs => rw [eq_C_of_natDegree_eq_zero h]
  simp

theorem thom : ∀ (n : ℕ) (PP : Finset ℝ[X]), PP.card ≤ n → DerivClosed PP → ∀ ν : ℝ[X] → SignType,
    (signSet PP ν).OrdConnected ∧ ((signSet PP ν).Subsingleton ∨ IsOpen (signSet PP ν)) := by
  intro n
  induction n with
  | zero =>
    intro PP hPP _ ν
    have : PP = ∅ := Finset.card_eq_zero.mp (by omega)
    subst this
    have : signSet ∅ ν = univ := by ext x; simp [signSet]
    rw [this]; exact ⟨ordConnected_univ, Or.inr isOpen_univ⟩
  | succ n ih =>
    intro PP hPP hcl ν
    by_cases hconst : ∀ p ∈ PP, p.natDegree = 0
    · -- all constant: the sign set is ∅ or univ
      by_cases hall : ∀ p ∈ PP, SignType.sign (p.coeff 0) = ν p
      · have : signSet PP ν = univ := by
          ext x; simp only [signSet, mem_setOf_eq, mem_univ, iff_true]
          intro p hp
          rw [eval_const (hconst p hp)]; exact hall p hp
        rw [this]; exact ⟨ordConnected_univ, Or.inr isOpen_univ⟩
      · push Not at hall
        obtain ⟨p, hp, hne⟩ := hall
        have : signSet PP ν = ∅ := by
          ext x; simp only [signSet, mem_setOf_eq, mem_empty_iff_false, iff_false]
          intro h; apply hne
          have := h p hp
          rwa [eval_const (hconst p hp)] at this
        rw [this]; exact ⟨ordConnected_empty, Or.inl subsingleton_empty⟩
    · push Not at hconst
      obtain ⟨q, hq, hqd⟩ := hconst
      have hne : PP.Nonempty := ⟨q, hq⟩
      obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image PP natDegree hne
      have hpd : p.natDegree ≠ 0 := by
        have := hmax q hq; omega
      set PP' := PP.erase p with hPP'
      have hcard : PP'.card ≤ n := by
        rw [Finset.card_erase_of_mem hp]; omega
      have hdp : derivative p ∈ PP' := by
        refine Finset.mem_erase.mpr ⟨?_, hcl p hp⟩
        intro h
        have := natDegree_derivative_lt hpd
        rw [h] at this; exact lt_irrefl _ this
      have hcl' : DerivClosed PP' := by
        intro r hr
        obtain ⟨hrp, hrPP⟩ := Finset.mem_erase.mp hr
        refine Finset.mem_erase.mpr ⟨?_, hcl r hrPP⟩
        intro h
        by_cases hr0 : r.natDegree = 0
        · rw [derivative_of_natDegree_zero hr0] at h
          apply hpd; rw [← h]; simp
        · have h1 := natDegree_derivative_lt hr0
          have h2 := hmax r hrPP
          rw [h] at h1; omega
      obtain ⟨hA', hA'o⟩ := ih PP' hcard hcl' ν
      have hsplit : signSet PP ν = signSet PP' ν ∩ {x | SignType.sign (p.eval x) = ν p} := by
        ext x
        simp only [signSet, mem_setOf_eq, mem_inter_iff]
        constructor
        · intro h
          exact ⟨fun r hr => h r (Finset.mem_of_mem_erase hr), h p hp⟩
        · rintro ⟨h, hpx⟩ r hr
          by_cases hrp : r = p
          · subst hrp; exact hpx
          · exact h r (Finset.mem_erase.mpr ⟨hrp, hr⟩)
      rw [hsplit]
      exact thom_step hA' hA'o p (ν (derivative p)) (fun x hx => hx _ hdp) (ν p)

/-- Relaxed sign: `t` is `s` or `0`. -/
def Relax (s t : SignType) : Prop := t = s ∨ t = 0

/-- Realization of the relaxed (closed) sign condition. -/
def relaxSet (PP : Finset ℝ[X]) (ν : ℝ[X] → SignType) : Set ℝ :=
  {x : ℝ | ∀ p ∈ PP, Relax (ν p) (SignType.sign (p.eval x))}

theorem relax_iff (s : SignType) (v : ℝ) :
    Relax s (SignType.sign v) ↔ (s = 0 ∧ v = 0) ∨ (s = 1 ∧ 0 ≤ v) ∨ (s = -1 ∧ v ≤ 0) := by
  rcases lt_trichotomy v 0 with h | h | h
  · rw [sign_neg h]
    have h1 : ¬ v = 0 := h.ne
    have h2 : ¬ 0 ≤ v := not_le.mpr h
    rcases s with _ | _ | _ <;> simp [Relax, h1, h2, h.le] <;> decide
  · subst h
    rw [sign_zero]
    rcases s with _ | _ | _ <;> simp [Relax] <;> decide
  · rw [sign_pos h]
    have h1 : ¬ v = 0 := h.ne'
    have h2 : ¬ v ≤ 0 := not_le.mpr h
    rcases s with _ | _ | _ <;> simp [Relax, h1, h2, h.le] <;> decide

theorem ordConn_relax_of_monotoneOn {A' : Set ℝ} (hA' : A'.OrdConnected) {f : ℝ → ℝ}
    (hm : MonotoneOn f A' ∨ AntitoneOn f A') (t : SignType) :
    (A' ∩ {x | Relax t (SignType.sign (f x))}).OrdConnected := by
  constructor
  intro x hx z hz y hy
  have hyA : y ∈ A' := hA'.out hx.1 hz.1 hy
  refine ⟨hyA, ?_⟩
  have h1 : Relax t (SignType.sign (f x)) := hx.2
  have h2 : Relax t (SignType.sign (f z)) := hz.2
  show Relax t (SignType.sign (f y))
  rw [relax_iff] at h1 h2 ⊢
  have hb : (f x ≤ f y ∧ f y ≤ f z) ∨ (f y ≤ f x ∧ f z ≤ f y) := by
    rcases hm with hm | hm
    · exact Or.inl ⟨hm hx.1 hyA hy.1, hm hyA hz.1 hy.2⟩
    · exact Or.inr ⟨hm hx.1 hyA hy.1, hm hyA hz.1 hy.2⟩
  rcases h1 with ⟨e1, f1⟩ | ⟨e1, f1⟩ | ⟨e1, f1⟩ <;>
  rcases h2 with ⟨e2, f2⟩ | ⟨e2, f2⟩ | ⟨e2, f2⟩ <;>
  first
  | (exact absurd (e1.symm.trans e2) (by decide))
  | (left; refine ⟨e1, ?_⟩; rcases hb with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
      exact le_antisymm (by linarith) (by linarith))
  | (right; left; refine ⟨e1, ?_⟩; rcases hb with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> linarith)
  | (right; right; refine ⟨e1, ?_⟩; rcases hb with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> linarith)

/-- **Relaxed Thom lemma**: closed sign conditions on a derivative-closed family are intervals. -/
theorem thom_relax : ∀ (n : ℕ) (PP : Finset ℝ[X]), PP.card ≤ n → DerivClosed PP →
    ∀ ν : ℝ[X] → SignType, (relaxSet PP ν).OrdConnected := by
  intro n
  induction n with
  | zero =>
    intro PP hPP _ ν
    have : PP = ∅ := Finset.card_eq_zero.mp (by omega)
    subst this
    have : relaxSet ∅ ν = univ := by ext x; simp [relaxSet]
    rw [this]; exact ordConnected_univ
  | succ n ih =>
    intro PP hPP hcl ν
    by_cases hconst : ∀ p ∈ PP, p.natDegree = 0
    · by_cases hall : ∀ p ∈ PP, Relax (ν p) (SignType.sign (p.coeff 0))
      · have : relaxSet PP ν = univ := by
          ext x; simp only [relaxSet, mem_setOf_eq, mem_univ, iff_true]
          intro p hp
          rw [eval_const (hconst p hp)]; exact hall p hp
        rw [this]; exact ordConnected_univ
      · push Not at hall
        obtain ⟨p, hp, hne⟩ := hall
        have : relaxSet PP ν = ∅ := by
          ext x; simp only [relaxSet, mem_setOf_eq, mem_empty_iff_false, iff_false]
          intro h; apply hne
          have := h p hp
          rwa [eval_const (hconst p hp)] at this
        rw [this]; exact ordConnected_empty
    · push Not at hconst
      obtain ⟨q, hq, hqd⟩ := hconst
      obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image PP natDegree ⟨q, hq⟩
      have hpd : p.natDegree ≠ 0 := by
        have := hmax q hq; omega
      set PP' := PP.erase p with hPP'
      have hcard : PP'.card ≤ n := by
        rw [Finset.card_erase_of_mem hp]; omega
      have hdp : derivative p ∈ PP' := by
        refine Finset.mem_erase.mpr ⟨?_, hcl p hp⟩
        intro h
        have := natDegree_derivative_lt hpd
        rw [h] at this; exact lt_irrefl _ this
      have hcl' : DerivClosed PP' := by
        intro r hr
        obtain ⟨hrp, hr𝒫⟩ := Finset.mem_erase.mp hr
        refine Finset.mem_erase.mpr ⟨?_, hcl r hr𝒫⟩
        intro h
        by_cases hr0 : r.natDegree = 0
        · rw [derivative_of_natDegree_zero hr0] at h
          apply hpd; rw [← h]; simp
        · have h1 := natDegree_derivative_lt hr0
          have h2 := hmax r hr𝒫
          rw [h] at h1; omega
      have hA' := ih PP' hcard hcl' ν
      have hsplit : relaxSet PP ν = relaxSet PP' ν ∩ {x | Relax (ν p) (SignType.sign (p.eval x))} := by
        ext x
        simp only [relaxSet, mem_setOf_eq, mem_inter_iff]
        constructor
        · intro h
          exact ⟨fun r hr => h r (Finset.mem_of_mem_erase hr), h p hp⟩
        · rintro ⟨h, hpx⟩ r hr
          by_cases hrp : r = p
          · subst hrp; exact hpx
          · exact h r (Finset.mem_erase.mpr ⟨hrp, hr⟩)
      rw [hsplit]
      -- p is monotone or antitone on the relaxed set of PP'
      have hconv : Convex ℝ (relaxSet PP' ν) := hA'.convex
      have hcont : ContinuousOn (fun y => p.eval y) (relaxSet PP' ν) := p.continuous.continuousOn
      have hdiff : DifferentiableOn ℝ (fun y => p.eval y) (interior (relaxSet PP' ν)) :=
        p.differentiable.differentiableOn
      have hder : ∀ x ∈ relaxSet PP' ν, Relax (ν (derivative p))
          (SignType.sign ((derivative p).eval x)) := fun x hx => hx _ hdp
      have hm : MonotoneOn (fun y => p.eval y) (relaxSet PP' ν) ∨
          AntitoneOn (fun y => p.eval y) (relaxSet PP' ν) := by
        rcases h : ν (derivative p) with _ | _ | _
        · left
          refine monotoneOn_of_deriv_nonneg hconv hcont hdiff (fun x hx => ?_)
          have := hder x (interior_subset hx)
          rw [h, relax_iff] at this
          rw [deriv_eval_poly]
          rcases this with ⟨_, e⟩ | ⟨e, _⟩ | ⟨e, _⟩
          · rw [e]
          · exact absurd e (by decide)
          · exact absurd e (by decide)
        · right
          refine antitoneOn_of_deriv_nonpos hconv hcont hdiff (fun x hx => ?_)
          have := hder x (interior_subset hx)
          rw [h, relax_iff] at this
          rw [deriv_eval_poly]
          rcases this with ⟨e, _⟩ | ⟨e, _⟩ | ⟨_, e⟩
          · exact absurd e (by decide)
          · exact absurd e (by decide)
          · exact e
        · left
          refine monotoneOn_of_deriv_nonneg hconv hcont hdiff (fun x hx => ?_)
          have := hder x (interior_subset hx)
          rw [h, relax_iff] at this
          rw [deriv_eval_poly]
          rcases this with ⟨e, _⟩ | ⟨_, e⟩ | ⟨e, _⟩
          · exact absurd e (by decide)
          · exact e
          · exact absurd e (by decide)
      exact ordConn_relax_of_monotoneOn hA' hm (ν p)

end SubanalyticLib

/-! SubanalyticLib CS-3 TS-b (part 2): ends of a sign-condition cell.
Appended to L4t_Thom.lean (uses `signSet`, `relaxSet`, `Relax`, `relax_iff`, `thom`, `thom_relax`).
* eventual signs of a real polynomial at `±∞` (`eventually_sign_atTop/atBot`);
* indexed sign sets `iSign Q ev μ` / `iRelax Q ev μ` and their transfer to `signSet`/`relaxSet`;
* `iSign` eventually contains `[c,∞)` iff every code is the sign at `+∞` (`eventually_mem_iSign_atTop_iff`);
* closure of a nonempty cell = its relaxed set (`mem_closure_of_iRelax`, `closure_iSign_subset`);
* realized signs of a strictly monotone continuous function on an open interval, read off at the
  finite endpoints and at the infinite ends (`realized_pos_iff`, `realized_zero_iff`). -/

open Polynomial Set Filter Topology

namespace SubanalyticLib

theorem eventually_sign_atTop (p : ℝ[X]) :
    ∀ᶠ x in atTop, SignType.sign (p.eval x) = SignType.sign p.leadingCoeff := by
  rcases le_or_gt p.degree 0 with h | h
  · have hp := eq_C_of_degree_le_zero h
    refine Eventually.of_forall fun x => ?_
    rw [hp]; simp
  · rcases lt_or_gt_of_ne (leadingCoeff_ne_zero.mpr (ne_zero_of_degree_gt h)) with hl | hl
    · have := Polynomial.tendsto_atBot_of_leadingCoeff_nonpos p h hl.le
      filter_upwards [this.eventually (eventually_lt_atBot 0)] with x hx
      rw [sign_neg hx, sign_neg hl]
    · have := Polynomial.tendsto_atTop_of_leadingCoeff_nonneg p h hl.le
      filter_upwards [this.eventually (eventually_gt_atTop 0)] with x hx
      rw [sign_pos hx, sign_pos hl]

/-- Sign at `-∞` of `p` is the sign at `+∞` of `p(-X)`. -/
theorem eventually_sign_atBot (p : ℝ[X]) :
    ∀ᶠ x in atBot, SignType.sign (p.eval x) = SignType.sign (p.comp (-X)).leadingCoeff := by
  have h := tendsto_neg_atBot_atTop.eventually (eventually_sign_atTop (p.comp (-X)))
  filter_upwards [h] with x hx
  simpa [eval_comp] using hx

theorem leadingCoeff_comp_neg_X (p : ℝ[X]) :
    (p.comp (-X)).leadingCoeff = (-1) ^ p.natDegree * p.leadingCoeff := by
  rw [leadingCoeff_comp (by rw [natDegree_neg, natDegree_X]; exact one_ne_zero)]
  rw [leadingCoeff_neg, leadingCoeff_X, mul_comm]

section Indexed

variable {ι : Type*}

/-- Realization of a sign condition on an indexed family of polynomials. -/
def iSign (Q : Finset ι) (ev : ι → ℝ[X]) (μ : ι → SignType) : Set ℝ :=
  {x : ℝ | ∀ i ∈ Q, SignType.sign ((ev i).eval x) = μ i}

/-- Realization of the relaxed sign condition on an indexed family. -/
def iRelax (Q : Finset ι) (ev : ι → ℝ[X]) (μ : ι → SignType) : Set ℝ :=
  {x : ℝ | ∀ i ∈ Q, Relax (μ i) (SignType.sign ((ev i).eval x))}

/-- Indexed derivative closure. -/
def IDerivClosed (Q : Finset ι) (ev : ι → ℝ[X]) : Prop :=
  ∀ i ∈ Q, ∃ j ∈ Q, ev j = derivative (ev i)

theorem iSign_subset_iRelax (Q : Finset ι) (ev : ι → ℝ[X]) (μ : ι → SignType) :
    iSign Q ev μ ⊆ iRelax Q ev μ := fun _ hx i hi => Or.inl (hx i hi)

theorem derivClosed_image {Q : Finset ι} {ev : ι → ℝ[X]} (h : IDerivClosed Q ev) :
    DerivClosed (Q.image ev) := by
  classical
  intro p hp
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨j, hj, e⟩ := h i hi
  exact Finset.mem_image.mpr ⟨j, hj, e⟩

/-- Transfer: a nonempty indexed cell is the cell of the image family with the code read at a point. -/
theorem iSign_eq_signSet [DecidableEq ℝ[X]] {Q : Finset ι} {ev : ι → ℝ[X]} {μ : ι → SignType} {x₀ : ℝ}
    (h₀ : x₀ ∈ iSign Q ev μ) :
    iSign Q ev μ = signSet (Q.image ev) (fun p => SignType.sign (p.eval x₀)) := by
  ext x
  simp only [iSign, signSet, mem_setOf_eq, Finset.mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  constructor
  · intro hx i hi; rw [hx i hi, h₀ i hi]
  · intro hx i hi; rw [hx i hi, h₀ i hi]

theorem iRelax_eq_relaxSet [DecidableEq ℝ[X]] {Q : Finset ι} {ev : ι → ℝ[X]} {μ : ι → SignType} {x₀ : ℝ}
    (h₀ : x₀ ∈ iSign Q ev μ) :
    iRelax Q ev μ = relaxSet (Q.image ev) (fun p => SignType.sign (p.eval x₀)) := by
  ext x
  simp only [iRelax, relaxSet, mem_setOf_eq, Finset.mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  constructor
  · intro hx i hi; rw [h₀ i hi]; exact hx i hi
  · intro hx i hi; rw [← h₀ i hi]; exact hx i hi

/-- Thom's lemma for indexed derivative-closed families. -/
theorem ithom {Q : Finset ι} {ev : ι → ℝ[X]} (hQ : IDerivClosed Q ev) (μ : ι → SignType) :
    (iSign Q ev μ).OrdConnected ∧ ((iSign Q ev μ).Subsingleton ∨ IsOpen (iSign Q ev μ)) := by
  classical
  rcases (iSign Q ev μ).eq_empty_or_nonempty with he | ⟨x₀, h₀⟩
  · rw [he]; exact ⟨ordConnected_empty, Or.inl subsingleton_empty⟩
  · rw [iSign_eq_signSet h₀]
    exact thom _ _ le_rfl (derivClosed_image hQ) _

theorem ithom_relax {Q : Finset ι} {ev : ι → ℝ[X]} (hQ : IDerivClosed Q ev) {μ : ι → SignType}
    (hne : (iSign Q ev μ).Nonempty) : (iRelax Q ev μ).OrdConnected := by
  classical
  obtain ⟨x₀, h₀⟩ := hne
  rw [iRelax_eq_relaxSet h₀]
  exact thom_relax _ _ le_rfl (derivClosed_image hQ) _

/-- `iSign` contains a neighbourhood of `+∞` iff every code is the sign at `+∞`. -/
theorem eventually_mem_iSign_atTop_iff (Q : Finset ι) (ev : ι → ℝ[X]) (μ : ι → SignType) :
    (∀ᶠ x in atTop, x ∈ iSign Q ev μ) ↔ ∀ i ∈ Q, μ i = SignType.sign (ev i).leadingCoeff := by
  have hall : ∀ᶠ x in atTop, ∀ i ∈ Q, SignType.sign ((ev i).eval x) =
      SignType.sign (ev i).leadingCoeff :=
    (Filter.eventually_all_finset Q).mpr fun i _ => eventually_sign_atTop (ev i)
  constructor
  · intro h
    obtain ⟨x, hx1, hx2⟩ := (h.and hall).exists
    intro i hi
    exact (hx1 i hi).symm.trans (hx2 i hi)
  · intro h
    filter_upwards [hall] with x hx
    exact fun i hi => (hx i hi).trans (h i hi).symm

theorem eventually_mem_iSign_atBot_iff (Q : Finset ι) (ev : ι → ℝ[X]) (μ : ι → SignType) :
    (∀ᶠ x in atBot, x ∈ iSign Q ev μ) ↔
      ∀ i ∈ Q, μ i = SignType.sign ((ev i).comp (-X)).leadingCoeff := by
  have hall : ∀ᶠ x in atBot, ∀ i ∈ Q, SignType.sign ((ev i).eval x) =
      SignType.sign ((ev i).comp (-X)).leadingCoeff :=
    (Filter.eventually_all_finset Q).mpr fun i _ => eventually_sign_atBot (ev i)
  constructor
  · intro h
    obtain ⟨x, hx1, hx2⟩ := (h.and hall).exists
    intro i hi
    exact (hx1 i hi).symm.trans (hx2 i hi)
  · intro h
    filter_upwards [hall] with x hx
    exact fun i hi => (hx i hi).trans (h i hi).symm

theorem isClosed_relax (q : ℝ[X]) (s : SignType) :
    IsClosed {x : ℝ | Relax s (SignType.sign (q.eval x))} := by
  have hc : Continuous fun x : ℝ => q.eval x := q.continuous
  rcases s with _ | _ | _
  · have : {x : ℝ | Relax SignType.zero (SignType.sign (q.eval x))} = {x | q.eval x = 0} := by
      ext x; simp only [mem_setOf_eq]
      rw [show SignType.zero = 0 from rfl, relax_iff]
      constructor
      · rintro (⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩)
        · exact h
        · exact absurd h (by decide)
        · exact absurd h (by decide)
      · intro h; exact Or.inl ⟨rfl, h⟩
    rw [this]; exact isClosed_eq hc continuous_const
  · have : {x : ℝ | Relax SignType.neg (SignType.sign (q.eval x))} = {x | q.eval x ≤ 0} := by
      ext x; simp only [mem_setOf_eq]
      rw [show SignType.neg = -1 from rfl, relax_iff]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩)
        · exact absurd h (by decide)
        · exact absurd h (by decide)
        · exact h
      · intro h; exact Or.inr (Or.inr ⟨rfl, h⟩)
    rw [this]; exact isClosed_le hc continuous_const
  · have : {x : ℝ | Relax SignType.pos (SignType.sign (q.eval x))} = {x | 0 ≤ q.eval x} := by
      ext x; simp only [mem_setOf_eq]
      rw [show SignType.pos = 1 from rfl, relax_iff]
      constructor
      · rintro (⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩)
        · exact absurd h (by decide)
        · exact h
        · exact absurd h (by decide)
      · intro h; exact Or.inr (Or.inl ⟨rfl, h⟩)
    rw [this]; exact isClosed_le continuous_const hc

theorem closure_iSign_subset (Q : Finset ι) (ev : ι → ℝ[X]) (μ : ι → SignType) :
    closure (iSign Q ev μ) ⊆ iRelax Q ev μ := by
  intro z hz
  show ∀ i ∈ Q, Relax (μ i) (SignType.sign ((ev i).eval z))
  intro i hi
  have hsub : iSign Q ev μ ⊆ {x | Relax (μ i) (SignType.sign ((ev i).eval x))} :=
    fun x hx => Or.inl (hx i hi)
  exact ((isClosed_relax (ev i) (μ i)).closure_subset_iff.mpr hsub) hz

/-- An infinite piece of the open segment from `z` towards `c`, within `ε` of `z`. -/
theorem exists_near_segment {c z ε : ℝ} (hcz : c ≠ z) (hε : 0 < ε) :
    ∃ I : Set ℝ, I.Infinite ∧ I ⊆ uIcc c z ∧ ∀ y ∈ I, dist y z < ε := by
  rcases lt_or_gt_of_ne hcz with h | h
  · refine ⟨Ioo (max c (z - ε)) z, Set.Ioo_infinite (max_lt h (by linarith)), ?_, ?_⟩
    · intro y hy
      rw [mem_uIcc]; left
      exact ⟨(le_max_left _ _).trans hy.1.le, hy.2.le⟩
    · intro y hy
      have h1 := (le_max_right c (z - ε)).trans_lt hy.1
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hy.2]
  · refine ⟨Ioo z (min c (z + ε)), Set.Ioo_infinite (lt_min h (by linarith)), ?_, ?_⟩
    · intro y hy
      rw [mem_uIcc]; right
      exact ⟨hy.1.le, hy.2.le.trans (min_le_left _ _)⟩
    · intro y hy
      have h1 := hy.2.trans_le (min_le_right c (z + ε))
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hy.1]

/-- A point of the relaxed set of a nonempty cell lies in the closure of the cell
(given the relaxed set is order-connected, e.g. by `ithom_relax`). -/
theorem mem_closure_of_iRelax {Q : Finset ι} {ev : ι → ℝ[X]} {μ : ι → SignType}
    (hR : (iRelax Q ev μ).OrdConnected) {c z : ℝ} (hc : c ∈ iSign Q ev μ)
    (hz : z ∈ iRelax Q ev μ) : z ∈ closure (iSign Q ev μ) := by
  classical
  rcases eq_or_ne c z with hcz | hcz
  · subst hcz; exact subset_closure hc
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨I, hIinf, hIsub, hIdist⟩ := exists_near_segment hcz hε
  set B : Finset ι := Q.filter (fun i => μ i ≠ 0)
  have hBne : ∀ i ∈ B, ev i ≠ 0 := by
    intro i hi h0
    obtain ⟨hiQ, hμ⟩ := Finset.mem_filter.mp hi
    have := hc i hiQ
    rw [h0, eval_zero, sign_zero] at this
    exact hμ this.symm
  have hfin : (⋃ i ∈ B, {x : ℝ | (ev i).IsRoot x}).Finite :=
    (B.finite_toSet).biUnion fun i hi => Polynomial.finite_setOfPred_isRoot (hBne i hi)
  obtain ⟨y, hyI, hyB⟩ := (hIinf.sdiff hfin).nonempty
  refine ⟨y, ?_, by rw [dist_comm]; exact hIdist y hyI⟩
  have hyR : y ∈ iRelax Q ev μ :=
    hR.uIcc_subset (iSign_subset_iRelax Q ev μ hc) hz (hIsub hyI)
  intro i hi
  rcases hyR i hi with h | h
  · exact h
  · by_cases hμ : μ i = 0
    · rw [h, hμ]
    · exfalso
      apply hyB
      refine mem_iUnion₂.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hμ⟩, ?_⟩
      show (ev i).eval y = 0
      exact sign_eq_zero_iff.mp h

end Indexed

section Realized

variable {C : Set ℝ} {f : ℝ → ℝ}

/-- Positive values of a strictly monotone continuous function on an open interval `C` are
realized iff it is positive at a finite endpoint or eventually positive at an infinite end. -/
theorem realized_pos_iff (hC : C.OrdConnected) (hCo : IsOpen C)
    (hm : StrictMonoOn f C ∨ StrictAntiOn f C) (hf : Continuous f) :
    (∃ y ∈ C, 0 < f y) ↔ (∃ z ∈ closure C, z ∉ C ∧ 0 < f z) ∨
      ((∀ᶠ x in atTop, x ∈ C) ∧ ∀ᶠ x in atTop, 0 < f x) ∨
      ((∀ᶠ x in atBot, x ∈ C) ∧ ∀ᶠ x in atBot, 0 < f x) := by
  constructor
  · rintro ⟨y, hy, hfy⟩
    rcases hm with hm | hm
    · by_cases htop : ∀ᶠ x in atTop, x ∈ C
      · right; left
        refine ⟨htop, ?_⟩
        filter_upwards [htop, eventually_ge_atTop y] with x hx hxy
        exact lt_of_lt_of_le hfy (hm.monotoneOn hy hx hxy)
      · left
        have hb : ∃ b, y ≤ b ∧ b ∉ C := by
          by_contra hcon
          push Not at hcon
          exact htop (eventually_atTop.mpr ⟨y, hcon⟩)
        obtain ⟨b, hyb, hbC⟩ := hb
        set S := C ∩ Ici y with hS
        have hSb : BddAbove S := by
          refine ⟨b, fun c hc => ?_⟩
          by_contra hbc
          push Not at hbc
          exact hbC (hC.out hy hc.1 ⟨hyb, hbc.le⟩)
        have hSne : S.Nonempty := ⟨y, hy, le_refl y⟩
        have hyβ : y ≤ sSup S := le_csSup hSb ⟨hy, le_refl y⟩
        have hβcl : sSup S ∈ closure S := csSup_mem_closure hSne hSb
        refine ⟨sSup S, closure_mono inter_subset_left hβcl, ?_, ?_⟩
        · intro hβ
          obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hCo _ hβ
          have hmem : sSup S + ε / 2 ∈ C :=
            hball (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
          have := le_csSup hSb ⟨hmem, by show y ≤ _; linarith⟩
          linarith
        · have hT : IsClosed {x | f y ≤ f x} := isClosed_le continuous_const hf
          have hST : S ⊆ {x | f y ≤ f x} := fun c hc => hm.monotoneOn hy hc.1 hc.2
          have := (hT.closure_subset_iff.mpr hST) hβcl
          exact lt_of_lt_of_le hfy this
    · by_cases hbot : ∀ᶠ x in atBot, x ∈ C
      · right; right
        refine ⟨hbot, ?_⟩
        filter_upwards [hbot, eventually_le_atBot y] with x hx hxy
        exact lt_of_lt_of_le hfy (hm.antitoneOn hx hy hxy)
      · left
        have hb : ∃ b, b ≤ y ∧ b ∉ C := by
          by_contra hcon
          push Not at hcon
          exact hbot (eventually_atBot.mpr ⟨y, hcon⟩)
        obtain ⟨b, hyb, hbC⟩ := hb
        set S := C ∩ Iic y with hS
        have hSb : BddBelow S := by
          refine ⟨b, fun c hc => ?_⟩
          by_contra hbc
          push Not at hbc
          exact hbC (hC.out hc.1 hy ⟨hbc.le, hyb⟩)
        have hSne : S.Nonempty := ⟨y, hy, le_refl y⟩
        have hyβ : sInf S ≤ y := csInf_le hSb ⟨hy, le_refl y⟩
        have hβcl : sInf S ∈ closure S := csInf_mem_closure hSne hSb
        refine ⟨sInf S, closure_mono inter_subset_left hβcl, ?_, ?_⟩
        · intro hβ
          obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hCo _ hβ
          have hmem : sInf S - ε / 2 ∈ C :=
            hball (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
          have := csInf_le hSb ⟨hmem, by show _ ≤ y; linarith⟩
          linarith
        · have hT : IsClosed {x | f y ≤ f x} := isClosed_le continuous_const hf
          have hST : S ⊆ {x | f y ≤ f x} := fun c hc => hm.antitoneOn hc.1 hy hc.2
          have := (hT.closure_subset_iff.mpr hST) hβcl
          exact lt_of_lt_of_le hfy this
  · rintro (⟨z, hzc, -, hz⟩ | ⟨htop, hpos⟩ | ⟨hbot, hpos⟩)
    · have hU : {x | 0 < f x} ∈ 𝓝 z := (isOpen_lt continuous_const hf).mem_nhds hz
      obtain ⟨y, hyU, hyC⟩ := mem_closure_iff_nhds.mp hzc _ hU
      exact ⟨y, hyC, hyU⟩
    · obtain ⟨x, h1, h2⟩ := (htop.and hpos).exists
      exact ⟨x, h1, h2⟩
    · obtain ⟨x, h1, h2⟩ := (hbot.and hpos).exists
      exact ⟨x, h1, h2⟩

/-- Negative version of `realized_pos_iff`. -/
theorem realized_neg_iff (hC : C.OrdConnected) (hCo : IsOpen C)
    (hm : StrictMonoOn f C ∨ StrictAntiOn f C) (hf : Continuous f) :
    (∃ y ∈ C, f y < 0) ↔ (∃ z ∈ closure C, z ∉ C ∧ f z < 0) ∨
      ((∀ᶠ x in atTop, x ∈ C) ∧ ∀ᶠ x in atTop, f x < 0) ∨
      ((∀ᶠ x in atBot, x ∈ C) ∧ ∀ᶠ x in atBot, f x < 0) := by
  have hm' : StrictMonoOn (fun x => -f x) C ∨ StrictAntiOn (fun x => -f x) C := by
    rcases hm with hm | hm
    · exact Or.inr fun a ha b hb hab => neg_lt_neg (hm ha hb hab)
    · exact Or.inl fun a ha b hb hab => neg_lt_neg (hm ha hb hab)
  have := realized_pos_iff hC hCo hm' hf.neg
  simp only [neg_pos] at this
  exact this

/-- A zero is realized iff both strict signs are realized. -/
theorem realized_zero_iff (hC : C.OrdConnected) (hCo : IsOpen C)
    (hm : StrictMonoOn f C ∨ StrictAntiOn f C) (hf : Continuous f) :
    (∃ y ∈ C, f y = 0) ↔ (∃ y ∈ C, 0 < f y) ∧ (∃ y ∈ C, f y < 0) := by
  constructor
  · rintro ⟨y, hy, h0⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hCo y hy
    have hl : y - ε / 2 ∈ C :=
      hball (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
    have hr : y + ε / 2 ∈ C :=
      hball (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
    rcases hm with hm | hm
    · have h1 := hm hl hy (by linarith)
      have h2 := hm hy hr (by linarith)
      exact ⟨⟨_, hr, by linarith⟩, ⟨_, hl, by linarith⟩⟩
    · have h1 := hm hl hy (by linarith)
      have h2 := hm hy hr (by linarith)
      exact ⟨⟨_, hl, by linarith⟩, ⟨_, hr, by linarith⟩⟩
  · rintro ⟨⟨a, ha, hfa⟩, ⟨b, hb, hfb⟩⟩
    have hsub : uIcc a b ⊆ C := hC.uIcc_subset ha hb
    obtain ⟨x, hx, hfx⟩ := intermediate_value_uIcc (hf.continuousOn : ContinuousOn f (uIcc a b))
      (show (0 : ℝ) ∈ uIcc (f a) (f b) from mem_uIcc.mpr (Or.inr ⟨hfb.le, hfa.le⟩))
    exact ⟨x, hsub hx, hfx⟩

end Realized

end SubanalyticLib

/-! SubanalyticLib CS-3 (Tarski–Seidenberg) infrastructure, part 1.
* `IsSA R S`: `S ⊆ A` lies in the Boolean algebra generated by `{f > 0}`, `{f = 0}` for `f` in a
  subring `R` of `A → ℝ` (polynomial functions give semialgebraic sets, analytic germs on a ball
  give semianalytic sets). Closure lemmas and finite-cover locality.
* Pseudo-division in `S[X]` over any commutative ring (with an even power of the leading
  coefficient, so that signs at the roots of the divisor are preserved). -/

open Polynomial Set

set_option linter.unusedSectionVars false

namespace SubanalyticLib

section SA

variable {A : Type*} (R : Subring (A → ℝ))

/-- Boolean algebra generated by the sign conditions of the functions in `R`. -/
inductive IsSA : Set A → Prop
  | pos {f : A → ℝ} (hf : f ∈ R) : IsSA {a | 0 < f a}
  | zero {f : A → ℝ} (hf : f ∈ R) : IsSA {a | f a = 0}
  | compl {S : Set A} : IsSA S → IsSA Sᶜ
  | inter {S T : Set A} : IsSA S → IsSA T → IsSA (S ∩ T)

variable {R}

theorem IsSA.univ : IsSA R (Set.univ : Set A) := by
  have h := IsSA.zero (R := R) (Subring.zero_mem R)
  have : {a : A | (0 : A → ℝ) a = 0} = Set.univ := by ext a; simp
  rwa [this] at h

theorem IsSA.empty : IsSA R (∅ : Set A) := by
  have h := (IsSA.univ (R := R)).compl
  rwa [Set.compl_univ] at h

theorem IsSA.union {S T : Set A} (hS : IsSA R S) (hT : IsSA R T) : IsSA R (S ∪ T) := by
  have h := (hS.compl.inter hT.compl).compl
  rwa [← Set.compl_union, compl_compl] at h

theorem IsSA.neg {f : A → ℝ} (hf : f ∈ R) : IsSA R {a | f a < 0} := by
  have h := IsSA.pos (R := R) (Subring.neg_mem R hf)
  have : {a : A | 0 < (-f) a} = {a | f a < 0} := by ext a; simp
  rwa [this] at h

theorem IsSA.ne {f : A → ℝ} (hf : f ∈ R) : IsSA R {a | f a ≠ 0} := by
  have h := (IsSA.zero (R := R) hf).compl
  exact h

theorem IsSA.sign {f : A → ℝ} (hf : f ∈ R) (s : SignType) :
    IsSA R {a | SignType.sign (f a) = s} := by
  rcases s with _ | _ | _
  · have : {a : A | SignType.sign (f a) = SignType.zero} = {a | f a = 0} := by
      ext a; simp only [mem_setOf_eq]; exact sign_eq_zero_iff
    rw [this]; exact IsSA.zero hf
  · have : {a : A | SignType.sign (f a) = SignType.neg} = {a | f a < 0} := by
      ext a; simp only [mem_setOf_eq]; exact sign_eq_neg_one_iff
    rw [this]; exact IsSA.neg hf
  · have : {a : A | SignType.sign (f a) = SignType.pos} = {a | 0 < f a} := by
      ext a; simp only [mem_setOf_eq]; exact sign_eq_one_iff
    rw [this]; exact IsSA.pos hf

theorem IsSA.biUnion {ι : Type*} (s : Finset ι) {S : ι → Set A} (h : ∀ i ∈ s, IsSA R (S i)) :
    IsSA R (⋃ i ∈ s, S i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty]; exact IsSA.empty
  | insert i s hi ih =>
    rw [Finset.set_biUnion_insert]
    exact (h i (Finset.mem_insert_self i s)).union
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem IsSA.biInter {ι : Type*} (s : Finset ι) {S : ι → Set A} (h : ∀ i ∈ s, IsSA R (S i)) :
    IsSA R (⋂ i ∈ s, S i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.notMem_empty, iInter_of_empty, iInter_univ]; exact IsSA.univ
  | insert i s hi ih =>
    rw [Finset.set_biInter_insert]
    exact (h i (Finset.mem_insert_self i s)).inter
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem IsSA.iUnion_fintype {ι : Type*} [Fintype ι] {S : ι → Set A} (h : ∀ i, IsSA R (S i)) :
    IsSA R (⋃ i, S i) := by
  have := IsSA.biUnion (R := R) Finset.univ (S := S) (fun i _ => h i)
  simpa using this

theorem IsSA.iInter_fintype {ι : Type*} [Fintype ι] {S : ι → Set A} (h : ∀ i, IsSA R (S i)) :
    IsSA R (⋂ i, S i) := by
  have := IsSA.biInter (R := R) Finset.univ (S := S) (fun i _ => h i)
  simpa using this

/-- Locality: `E` is SA if it is SA on each piece of a finite SA cover. -/
theorem IsSA.of_cover {ι : Type*} [Fintype ι] {C : ι → Set A} (hC : ∀ i, IsSA R (C i))
    (hcov : ∀ a, ∃ i, a ∈ C i) {E : Set A} (hE : ∀ i, IsSA R (E ∩ C i)) : IsSA R E := by
  have : E = ⋃ i, E ∩ C i := by
    ext a; constructor
    · intro ha; obtain ⟨i, hi⟩ := hcov a; exact mem_iUnion.mpr ⟨i, ha, hi⟩
    · intro ha; obtain ⟨i, hi⟩ := mem_iUnion.mp ha; exact hi.1
  rw [this]; exact IsSA.iUnion_fintype hE

/-- Evaluation of the coefficient functions at a parameter `a`. -/
def evR (a : A) : R →+* ℝ := (Pi.evalRingHom (fun _ : A => ℝ) a).comp R.subtype

theorem evR_apply (a : A) (f : R) : evR (R := R) a f = (f : A → ℝ) a := rfl

/-- A polynomial with coefficients in `R`, specialised at the parameter `a`. -/
noncomputable def pe (p : R[X]) (a : A) : ℝ[X] := p.map (evR (R := R) a)

/-- The function `a ↦ (p at a)(x₀)`-style coefficient functions lie in `R`. -/
theorem coeff_mem (p : R[X]) (i : ℕ) : ((p.coeff i : R) : A → ℝ) ∈ R := (p.coeff i).2

theorem pe_coeff (p : R[X]) (a : A) (i : ℕ) : (pe p a).coeff i = ((p.coeff i : R) : A → ℝ) a := by
  simp [pe, coeff_map, evR_apply]

end SA

section PseudoDiv

variable {S : Type*} [CommRing S]

/-- One elimination step of pseudo-division. -/
theorem pdiv_step (p q : S[X]) (hq : q.natDegree ≤ p.natDegree) (hp : 0 < p.natDegree) :
    (q.leadingCoeff • p - C p.leadingCoeff * X ^ (p.natDegree - q.natDegree) * q).natDegree <
      p.natDegree := by
  set p1 := q.leadingCoeff • p - C p.leadingCoeff * X ^ (p.natDegree - q.natDegree) * q with hp1
  have hc : ∀ i, p.natDegree ≤ i → p1.coeff i = 0 := by
    intro i hi
    rw [hp1, coeff_sub, coeff_smul, mul_assoc, coeff_C_mul, coeff_X_pow_mul', smul_eq_mul]
    rw [if_pos (le_trans (Nat.sub_le _ _) hi)]
    rcases eq_or_lt_of_le hi with h | h
    · subst h
      have : p.natDegree - (p.natDegree - q.natDegree) = q.natDegree := by omega
      rw [this]
      rw [coeff_natDegree, coeff_natDegree]
      ring
    · rw [coeff_eq_zero_of_natDegree_lt h]
      have : q.natDegree < i - (p.natDegree - q.natDegree) := by omega
      rw [coeff_eq_zero_of_natDegree_lt this]
      ring
  by_cases h0 : p1 = 0
  · rw [h0, natDegree_zero]; exact hp
  · rw [natDegree_lt_iff_degree_lt h0, degree_lt_iff_coeff_zero]
    intro m hm
    exact hc m (by exact_mod_cast hm)

/-- **Pseudo-division**: `lc(q)^k • p = s * q + r` with `deg r < deg q`. -/
theorem pseudo_div (q : S[X]) (hq : 0 < q.natDegree) (p : S[X]) :
    ∃ k : ℕ, ∃ s r : S[X], q.leadingCoeff ^ k • p = s * q + r ∧ r.natDegree < q.natDegree := by
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ n ih =>
    by_cases hlt : p.natDegree < q.natDegree
    · exact ⟨0, 0, p, by simp, hlt⟩
    · push Not at hlt
      have hp : 0 < p.natDegree := lt_of_lt_of_le hq hlt
      set m := p.natDegree - q.natDegree
      set p1 := q.leadingCoeff • p - C p.leadingCoeff * X ^ m * q with hp1
      have hdeg : p1.natDegree < n := hn ▸ pdiv_step p q hlt hp
      obtain ⟨k, s, r, hk, hr⟩ := ih p1.natDegree hdeg p1 rfl
      refine ⟨k + 1, s + C (q.leadingCoeff ^ k * p.leadingCoeff) * X ^ m, r, ?_, hr⟩
      have e1 : q.leadingCoeff • p = p1 + C p.leadingCoeff * X ^ m * q := by
        rw [hp1]; ring
      rw [pow_succ, mul_smul, e1, smul_add, hk]
      rw [smul_eq_C_mul]
      simp only [map_mul, map_pow]
      ring

/-- Pseudo-division with an even power of the leading coefficient. -/
theorem pseudo_div_even (q : S[X]) (hq : 0 < q.natDegree) (p : S[X]) :
    ∃ k : ℕ, ∃ s r : S[X], q.leadingCoeff ^ (2 * k) • p = s * q + r ∧
      r.natDegree < q.natDegree := by
  obtain ⟨k, s, r, h, hr⟩ := pseudo_div q hq p
  refine ⟨k, q.leadingCoeff ^ k • s, q.leadingCoeff ^ k • r, ?_, ?_⟩
  · rw [two_mul, pow_add, mul_smul, h, smul_add, smul_mul_assoc]
  · exact lt_of_le_of_lt (natDegree_smul_le _ _) hr

end PseudoDiv

end SubanalyticLib

/-! SubanalyticLib CS-3 TS-b (part 1): per-parameter cell lemmas for the Cohen–Hörmander step.
* `sign_at_root`: at a root of `q`, `P` has the sign of its pseudo-remainder by `q`.
* realized signs of a strictly increasing continuous function on an open order-connected set
  `C`, read off from its eventual signs at the two ends of `C` (filters `atBot`/`atTop` of the
  subtype `C`). -/

open Polynomial Set Filter

set_option linter.unusedSectionVars false

namespace SubanalyticLib

/-- At a root of `q`, `P` has the sign of the pseudo-remainder. -/
theorem sign_at_root {P q s r : ℝ[X]} {c : ℝ} {k : ℕ} (hc : c ≠ 0)
    (h : c ^ (2 * k) • P = s * q + r) {x : ℝ} (hx : q.eval x = 0) :
    SignType.sign (P.eval x) = SignType.sign (r.eval x) := by
  have e := congrArg (fun F : ℝ[X] => F.eval x) h
  simp only [eval_smul, smul_eq_mul, eval_add, eval_mul, hx, mul_zero, zero_add] at e
  rw [← e, sign_mul]
  have : SignType.sign (c ^ (2 * k)) = 1 := by
    rw [sign_eq_one_iff, pow_mul]
    exact pow_pos (by positivity) k
  rw [this, one_mul]

section Realized

variable {C : Set ℝ} {f : ℝ → ℝ}

end Realized

end SubanalyticLib

/-! SubanalyticLib CS-3 TS-c: parametric families, codes, the (max degree, count) measure and
normalisation by truncation (so that formal degree = effective degree on each branch).
Appended to L4TB.lean (= L4t_Thom + L4tc_Ends + L4s_SA + L4tb_Cells). -/

open Polynomial Set Filter

namespace SubanalyticLib

section TSc

open scoped Classical

variable {A : Type*} {R : Subring (A → ℝ)} {ι : Type*}

/-- Parameters at which the sign condition `ν` on the specialised family is realized. -/
def Rlz (F : Finset ι) (ev : ι → R[X]) (ν : ι → SignType) : Set A :=
  {a | (iSign F (fun i => pe (ev i) a) ν).Nonempty}

/-- Derivative-closed at every parameter of `B`. -/
def DCl (F : Finset ι) (ev : ι → R[X]) (B : Set A) : Prop :=
  ∀ a ∈ B, IDerivClosed F (fun i => pe (ev i) a)

/-- Formal degree = effective degree on `B` (or the polynomial is formally zero). -/
def Nrm (F : Finset ι) (ev : ι → R[X]) (B : Set A) : Prop :=
  ∀ i ∈ F, ∀ a ∈ B, (((ev i).leadingCoeff : R) : A → ℝ) a ≠ 0 ∨ ev i = 0

/-- Codes on `s`, extended by `0`. -/
noncomputable def codes (s : Finset ι) : Finset (ι → SignType) :=
  (Finset.univ : Finset (s → SignType)).image (fun c i => if h : i ∈ s then c ⟨i, h⟩ else 0)

theorem exists_code (s : Finset ι) (μ : ι → SignType) : ∃ c ∈ codes s, ∀ i ∈ s, c i = μ i :=
  ⟨_, Finset.mem_image.mpr ⟨fun i => μ i, Finset.mem_univ _, rfl⟩, fun i hi => by simp [hi]⟩

theorem Rlz_congr {F : Finset ι} {ev ev' : ι → R[X]} {ν ν' : ι → SignType} {a : A}
    (he : ∀ i ∈ F, pe (ev i) a = pe (ev' i) a) (hν : ∀ i ∈ F, ν i = ν' i) :
    a ∈ Rlz F ev ν ↔ a ∈ Rlz F ev' ν' := by
  simp only [Rlz, mem_setOf_eq, iSign]
  constructor
  · rintro ⟨y, hy⟩; exact ⟨y, fun i hi => by rw [← he i hi, ← hν i hi]; exact hy i hi⟩
  · rintro ⟨y, hy⟩; exact ⟨y, fun i hi => by rw [he i hi, hν i hi]; exact hy i hi⟩

/-! ### The measure -/

/-- Maximal formal degree. -/
noncomputable def mdeg (F : Finset ι) (ev : ι → R[X]) : ℕ := F.sup fun i => (ev i).natDegree

/-- Number of members of maximal formal degree. -/
noncomputable def mcnt (F : Finset ι) (ev : ι → R[X]) : ℕ :=
  (F.filter fun i => (ev i).natDegree = mdeg F ev).card

noncomputable def mord (F : Finset ι) (ev : ι → R[X]) : ℕ ×ₗ ℕ := toLex (mdeg F ev, mcnt F ev)

theorem natDegree_le_mdeg {F : Finset ι} {ev : ι → R[X]} {i : ι} (hi : i ∈ F) :
    (ev i).natDegree ≤ mdeg F ev :=
  Finset.le_sup (f := fun i => (ev i).natDegree) hi

theorem mdeg_le {F : Finset ι} {ev : ι → R[X]} {n : ℕ} (h : ∀ i ∈ F, (ev i).natDegree ≤ n) :
    mdeg F ev ≤ n := Finset.sup_le h

theorem mord_mono {F : Finset ι} {ev ev' : ι → R[X]}
    (h : ∀ i ∈ F, (ev' i).natDegree ≤ (ev i).natDegree) : mord F ev' ≤ mord F ev := by
  have hle : mdeg F ev' ≤ mdeg F ev := mdeg_le fun i hi => (h i hi).trans (natDegree_le_mdeg hi)
  rw [mord, mord, Prod.Lex.toLex_le_toLex]
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact Or.inl hlt
  · refine Or.inr ⟨heq, ?_⟩
    apply Finset.card_le_card
    intro i hi
    rw [Finset.mem_filter] at hi ⊢
    refine ⟨hi.1, le_antisymm (natDegree_le_mdeg hi.1) ?_⟩
    rw [← heq, ← hi.2]; exact h i hi.1

theorem mord_lt {ι' : Type*} {F : Finset ι} {ev : ι → R[X]} {F' : Finset ι'} {ev' : ι' → R[X]}
    (h1 : ∀ i ∈ F', (ev' i).natDegree ≤ mdeg F ev)
    (h2 : (F'.filter fun i => (ev' i).natDegree = mdeg F ev).card < mcnt F ev) :
    mord F' ev' < mord F ev := by
  have hle : mdeg F' ev' ≤ mdeg F ev := mdeg_le h1
  rw [mord, mord, Prod.Lex.toLex_lt_toLex]
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact Or.inl hlt
  · refine Or.inr ⟨heq, ?_⟩
    rw [mcnt, heq]; exact h2

/-! ### Truncation -/

/-- Keep the coefficients of index `< k`. -/
noncomputable def ptr (k : ℕ) (p : R[X]) : R[X] := ∑ j ∈ Finset.range k, monomial j (p.coeff j)

theorem coeff_ptr (k : ℕ) (p : R[X]) (n : ℕ) :
    (ptr k p).coeff n = if n < k then p.coeff n else 0 := by
  simp only [ptr, finset_sum_coeff, coeff_monomial, Finset.sum_ite_eq', Finset.mem_range]

theorem natDegree_ptr_le (k : ℕ) (p : R[X]) : (ptr k p).natDegree ≤ p.natDegree := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [coeff_ptr]
  split_ifs
  · exact coeff_eq_zero_of_natDegree_lt (by exact_mod_cast hn)
  · rfl

theorem ptr_zero (p : R[X]) : ptr 0 p = 0 := by simp [ptr]

theorem lc_ptr {m : ℕ} {p : R[X]} (h : p.coeff m ≠ 0) :
    (ptr (m + 1) p).natDegree = m ∧ (ptr (m + 1) p).leadingCoeff = p.coeff m := by
  have hc : (ptr (m + 1) p).coeff m = p.coeff m := by rw [coeff_ptr, if_pos (Nat.lt_succ_self m)]
  have hd : (ptr (m + 1) p).natDegree = m := by
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · rw [natDegree_le_iff_coeff_eq_zero]
      intro n hn
      rw [coeff_ptr, if_neg]
      have : m < n := by exact_mod_cast hn
      omega
    · rw [hc]; exact h
  exact ⟨hd, by rw [leadingCoeff, hd, hc]⟩

theorem pe_ptr {k : ℕ} {p : R[X]} {a : A}
    (h : ∀ j, k ≤ j → ((p.coeff j : R) : A → ℝ) a = 0) : pe (ptr k p) a = pe p a := by
  ext n
  rw [pe_coeff, pe_coeff, coeff_ptr]
  split_ifs with hn
  · rfl
  · rw [h n (not_lt.mp hn)]; rfl

/-! ### Branches by effective degree -/

/-- Branch where exactly the coefficients of index `< k` may be nonzero and (if `k > 0`)
coefficient `k - 1` is nonzero; `D` bounds the formal degree. -/
def Br (D : ℕ) (p : R[X]) (k : ℕ) : Set A :=
  {a | (∀ j ∈ Finset.range (D + 1), k ≤ j → ((p.coeff j : R) : A → ℝ) a = 0) ∧
    (k = 0 ∨ ((p.coeff (k - 1) : R) : A → ℝ) a ≠ 0)}

theorem isSA_Br (D : ℕ) (p : R[X]) (k : ℕ) : IsSA R (Br (A := A) D p k) := by
  have h1 : IsSA R {a : A | ∀ j ∈ Finset.range (D + 1), k ≤ j → ((p.coeff j : R) : A → ℝ) a = 0} := by
    have : {a : A | ∀ j ∈ Finset.range (D + 1), k ≤ j → ((p.coeff j : R) : A → ℝ) a = 0} =
        ⋂ j ∈ (Finset.range (D + 1)).filter (fun j => k ≤ j), {a | ((p.coeff j : R) : A → ℝ) a = 0} := by
      ext a; simp only [mem_setOf_eq, mem_iInter, Finset.mem_filter, and_imp]
    rw [this]
    exact IsSA.biInter _ fun j _ => IsSA.zero (coeff_mem p j)
  have h2 : IsSA R {a : A | k = 0 ∨ ((p.coeff (k - 1) : R) : A → ℝ) a ≠ 0} := by
    by_cases hk : k = 0
    · have : {a : A | k = 0 ∨ ((p.coeff (k - 1) : R) : A → ℝ) a ≠ 0} = univ := by
        ext a; simp [hk]
      rw [this]; exact IsSA.univ
    · have : {a : A | k = 0 ∨ ((p.coeff (k - 1) : R) : A → ℝ) a ≠ 0} =
          {a | ((p.coeff (k - 1) : R) : A → ℝ) a ≠ 0} := by
        ext a; simp [hk]
      rw [this]; exact IsSA.ne (coeff_mem p _)
  exact h1.inter h2

/-- The effective number of coefficients at `a`. -/
noncomputable def effk (D : ℕ) (p : R[X]) (a : A) : ℕ :=
  ((Finset.range (D + 1)).filter fun j => ((p.coeff j : R) : A → ℝ) a ≠ 0).sup (· + 1)

theorem effk_le (D : ℕ) (p : R[X]) (a : A) : effk D p a ≤ D + 1 := by
  apply Finset.sup_le
  intro j hj
  have := (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)
  omega

theorem mem_Br_effk {D : ℕ} {p : R[X]} (hD : p.natDegree ≤ D) (a : A) :
    a ∈ Br D p (effk D p a) := by
  refine ⟨fun j hj hkj => ?_, ?_⟩
  · by_contra hne
    have : j + 1 ≤ effk D p a :=
      Finset.le_sup (f := (· + 1)) (Finset.mem_filter.mpr ⟨hj, hne⟩)
    omega
  · rcases Nat.eq_zero_or_pos (effk D p a) with h0 | hpos
    · exact Or.inl h0
    · right
      have hne : ((Finset.range (D + 1)).filter fun j => ((p.coeff j : R) : A → ℝ) a ≠ 0).Nonempty := by
        by_contra hem
        rw [Finset.not_nonempty_iff_eq_empty] at hem
        have : effk D p a = 0 := by rw [effk, hem]; rfl
        omega
      obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup _ hne (· + 1)
      have : effk D p a - 1 = j := by rw [effk, hjeq]; omega
      rw [this]
      exact (Finset.mem_filter.mp hj).2

/-- On `Br D p k` all coefficients of index `≥ k` vanish (`D ≥ natDegree p`). -/
theorem coeff_vanish_of_Br {D : ℕ} {p : R[X]} (hD : p.natDegree ≤ D) {k : ℕ} {a : A}
    (ha : a ∈ Br D p k) (j : ℕ) (hj : k ≤ j) : ((p.coeff j : R) : A → ℝ) a = 0 := by
  by_cases hjD : j ≤ D
  · exact ha.1 j (Finset.mem_range.mpr (Nat.lt_succ_of_le hjD)) hj
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]; rfl

/-- Truncated family on the branch `e`. -/
noncomputable def evTr (F : Finset ι) (ev : ι → R[X]) (D : ℕ) (e : F → Fin (D + 2)) (i : ι) : R[X] :=
  if h : i ∈ F then ptr (e ⟨i, h⟩) (ev i) else ev i

/-- The branch `e`. -/
def BrE (F : Finset ι) (ev : ι → R[X]) (D : ℕ) (e : F → Fin (D + 2)) : Set A :=
  ⋂ i : F, Br D (ev i) (e i)

theorem isSA_BrE (F : Finset ι) (ev : ι → R[X]) (D : ℕ) (e : F → Fin (D + 2)) :
    IsSA R (BrE (A := A) F ev D e) :=
  IsSA.iInter_fintype fun i => isSA_Br D (ev i) (e i)

theorem pe_evTr {F : Finset ι} {ev : ι → R[X]} {D : ℕ} (hD : ∀ i ∈ F, (ev i).natDegree ≤ D)
    {e : F → Fin (D + 2)} {a : A} (ha : a ∈ BrE F ev D e) {i : ι} (hi : i ∈ F) :
    pe (evTr F ev D e i) a = pe (ev i) a := by
  rw [evTr, dif_pos hi]
  exact pe_ptr fun j hj => coeff_vanish_of_Br (hD i hi) (mem_iInter.mp ha ⟨i, hi⟩) j hj

theorem nrm_evTr {F : Finset ι} {ev : ι → R[X]} {D : ℕ} (e : F → Fin (D + 2)) :
    Nrm F (evTr F ev D e) (BrE F ev D e) := by
  intro i hi a ha
  have hb := mem_iInter.mp ha ⟨i, hi⟩
  rw [evTr, dif_pos hi]
  rcases Nat.eq_zero_or_pos (e ⟨i, hi⟩ : ℕ) with h0 | hpos
  · right; rw [h0]; exact ptr_zero _
  · left
    obtain ⟨m, hm⟩ : ∃ m, (e ⟨i, hi⟩ : ℕ) = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
    have hcm : (((ev i).coeff m : R) : A → ℝ) a ≠ 0 := by
      rcases hb.2 with h | h
      · omega
      · rw [hm] at h; simpa using h
    have hc : (ev i).coeff m ≠ 0 := by
      intro h0; apply hcm; rw [h0]; rfl
    rw [hm, (lc_ptr hc).2]
    exact hcm

theorem natDegree_evTr_le {F : Finset ι} {ev : ι → R[X]} {D : ℕ} (e : F → Fin (D + 2)) (i : ι) :
    (evTr F ev D e i).natDegree ≤ (ev i).natDegree := by
  rw [evTr]; split_ifs
  · exact natDegree_ptr_le _ _
  · exact le_rfl

theorem dcl_evTr {F : Finset ι} {ev : ι → R[X]} {D : ℕ} (hD : ∀ i ∈ F, (ev i).natDegree ≤ D)
    {B : Set A} (hB : DCl F ev B) (e : F → Fin (D + 2)) :
    DCl F (evTr F ev D e) (B ∩ BrE F ev D e) := by
  intro a ha i hi
  obtain ⟨j, hj, hje⟩ := hB a ha.1 i hi
  refine ⟨j, hj, ?_⟩
  show pe (evTr F ev D e j) a = derivative (pe (evTr F ev D e i) a)
  rw [pe_evTr hD ha.2 hj, pe_evTr hD ha.2 hi]
  exact hje

/-- **Normalisation**: to show `B ∩ Rlz F ev ν` is SA it suffices to treat every truncated,
normalised family on its branch. -/
theorem isSA_of_branches {F : Finset ι} {ev : ι → R[X]} {ν : ι → SignType} {B : Set A}
    (hBsa : IsSA R B) (D : ℕ) (hD : ∀ i ∈ F, (ev i).natDegree ≤ D)
    (h : ∀ e : F → Fin (D + 2),
      IsSA R ((B ∩ BrE F ev D e) ∩ Rlz F (evTr F ev D e) ν)) :
    IsSA R (B ∩ Rlz F ev ν) := by
  refine IsSA.of_cover (C := fun e : F → Fin (D + 2) => BrE F ev D e) (isSA_BrE F ev D) ?_ ?_
  · intro a
    refine ⟨fun i => ⟨effk D (ev i) a, Nat.lt_succ_of_le (effk_le D (ev i) a)⟩, ?_⟩
    exact mem_iInter.mpr fun i => mem_Br_effk (hD i i.2) a
  · intro e
    have : (B ∩ Rlz F ev ν) ∩ BrE F ev D e = (B ∩ BrE F ev D e) ∩ Rlz F (evTr F ev D e) ν := by
      ext a
      simp only [mem_inter_iff]
      constructor
      · rintro ⟨⟨hB, hR⟩, hE⟩
        exact ⟨⟨hB, hE⟩, (Rlz_congr (fun i hi => (pe_evTr hD hE hi).symm) fun _ _ => rfl).mp hR⟩
      · rintro ⟨⟨hB, hE⟩, hR⟩
        exact ⟨⟨hB, (Rlz_congr (fun i hi => (pe_evTr hD hE hi)) fun _ _ => rfl).mp hR⟩, hE⟩
    rw [this]
    exact h e

end TSc

end SubanalyticLib

/-! SubanalyticLib CS-3 TS-d (part 1): data of one Cohen–Hörmander elimination step.
A normalised derivative-closed family `F`, a member `iP` of maximal degree `d ≥ 1`,
`Q = F.erase iP`, pseudo-remainders `rem q` of `P` by each nonconstant `q ∈ Q`, and the new
family `F' = Q ⊕ {derivatives of the remainders}` (index type `ι ⊕ (ι × ℕ)`), which has
smaller (max degree, count) measure. Appended to L4TD.lean. -/

open Polynomial Set Filter

namespace SubanalyticLib

section TSd

open scoped Classical

variable {A : Type*} {R : Subring (A → ℝ)} {ι : Type*}

theorem pe_nrm {p : R[X]} {a : A} (h : ((p.leadingCoeff : R) : A → ℝ) a ≠ 0 ∨ p = 0) :
    (pe p a).natDegree = p.natDegree ∧
      (pe p a).leadingCoeff = ((p.leadingCoeff : R) : A → ℝ) a := by
  rcases h with h | h
  · have h' : evR (R := R) a p.leadingCoeff ≠ 0 := h
    exact ⟨natDegree_map_of_leadingCoeff_ne_zero _ h', leadingCoeff_map_of_leadingCoeff_ne_zero _ h'⟩
  · subst h
    rw [pe, Polynomial.map_zero, natDegree_zero, leadingCoeff_zero, leadingCoeff_zero]
    exact ⟨rfl, rfl⟩

theorem pe_iterate_derivative (p : R[X]) (a : A) (k : ℕ) :
    pe (derivative^[k] p) a = derivative^[k] (pe p a) :=
  (iterate_derivative_map p (evR a) k).symm

theorem pe_identity {P q s r : R[X]} {k : ℕ} (h : q.leadingCoeff ^ (2 * k) • P = s * q + r)
    (a : A) : (((q.leadingCoeff : R) : A → ℝ) a) ^ (2 * k) • pe P a = pe s a * pe q a + pe r a := by
  have := congrArg (Polynomial.map (evR (R := R) a)) h
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.smul_eq_C_mul, Polynomial.map_mul,
    Polynomial.map_C] at this
  rw [Polynomial.smul_eq_C_mul]
  simpa [pe, map_pow, evR_apply] using this

theorem pe_zero' (a : A) : pe (0 : R[X]) a = 0 := by simp [pe]

/-- Data of one elimination step on the branch `B`. -/
structure SD (F : Finset ι) (ev : ι → R[X]) (B : Set A) where
  iP : ι
  hiP : iP ∈ F
  hdeg : (ev iP).natDegree = mdeg F ev
  hpos : 0 < mdeg F ev
  rem : ι → R[X]
  kk : ι → ℕ
  ss : ι → R[X]
  hrem : ∀ i, 0 < (ev i).natDegree →
    (ev i).leadingCoeff ^ (2 * kk i) • ev iP = ss i * ev i + rem i ∧
      (rem i).natDegree < (ev i).natDegree
  hN : Nrm F ev B
  hD : DCl F ev B

theorem exists_rem (ev : ι → R[X]) (P : R[X]) :
    ∃ kk : ι → ℕ, ∃ ss rem : ι → R[X], ∀ i, 0 < (ev i).natDegree →
      (ev i).leadingCoeff ^ (2 * kk i) • P = ss i * ev i + rem i ∧
        (rem i).natDegree < (ev i).natDegree := by
  have : ∀ i, ∃ k : ℕ, ∃ s r : R[X], 0 < (ev i).natDegree →
      (ev i).leadingCoeff ^ (2 * k) • P = s * ev i + r ∧ r.natDegree < (ev i).natDegree := by
    intro i
    by_cases h : 0 < (ev i).natDegree
    · obtain ⟨k, s, r, h1, h2⟩ := pseudo_div_even (ev i) h P
      exact ⟨k, s, r, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, 0, 0, fun h' => absurd h' h⟩
  choose kk ss rem h using this
  exact ⟨kk, ss, rem, h⟩

/-- New index set. -/
noncomputable def Fp (Q : Finset ι) (ev : ι → R[X]) (d : ℕ) : Finset (ι ⊕ (ι × ℕ)) :=
  Q.disjSum ((Q.filter fun i => 0 < (ev i).natDegree) ×ˢ Finset.range (d + 1))

/-- New family. -/
noncomputable def evp (ev rem : ι → R[X]) : ι ⊕ (ι × ℕ) → R[X] :=
  Sum.elim ev (fun x => derivative^[x.2] (rem x.1))

theorem mem_Fp_inl {Q : Finset ι} {ev : ι → R[X]} {d : ℕ} {i : ι} :
    Sum.inl i ∈ Fp Q ev d ↔ i ∈ Q := by simp [Fp]

theorem mem_Fp_inr {Q : Finset ι} {ev : ι → R[X]} {d : ℕ} {i : ι} {j : ℕ} :
    Sum.inr (i, j) ∈ Fp Q ev d ↔ (i ∈ Q ∧ 0 < (ev i).natDegree) ∧ j < d + 1 := by
  simp [Fp]

variable {F : Finset ι} {ev : ι → R[X]} {B : Set A}

namespace SD

variable (S : SD F ev B)

/-- The rest of the family. -/
noncomputable def Q : Finset ι := F.erase S.iP

/-- The new family's index set. -/
noncomputable def F' : Finset (ι ⊕ (ι × ℕ)) := Fp S.Q ev (mdeg F ev)

/-- The new family. -/
noncomputable def ev' : ι ⊕ (ι × ℕ) → R[X] := evp ev S.rem

theorem mem_Q {i : ι} : i ∈ S.Q ↔ i ≠ S.iP ∧ i ∈ F := Finset.mem_erase

theorem mem_F_of_Q {i : ι} (h : i ∈ S.Q) : i ∈ F := (S.mem_Q.mp h).2

theorem card_Q_lt : (S.Q.filter fun i => (ev i).natDegree = mdeg F ev).card < mcnt F ev := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨S.iP, Finset.mem_filter.mpr ⟨S.hiP, S.hdeg⟩, fun h => ?_⟩
    exact (S.mem_Q.mp (Finset.mem_filter.mp h).1).1 rfl
  · intro i hi
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨S.mem_F_of_Q hi.1, hi.2⟩

theorem mord_Q_lt : mord S.Q ev < mord F ev :=
  mord_lt (fun i hi => natDegree_le_mdeg (S.mem_F_of_Q hi)) S.card_Q_lt

theorem natDegree_ev'_inr {i : ι} {j : ℕ} (hi : 0 < (ev i).natDegree) :
    (S.ev' (Sum.inr (i, j))).natDegree < (ev i).natDegree := by
  show (derivative^[j] (S.rem i)).natDegree < _
  exact lt_of_le_of_lt ((natDegree_iterate_derivative _ _).trans (Nat.sub_le _ _)) (S.hrem i hi).2

theorem mord_F'_lt : mord S.F' S.ev' < mord F ev := by
  apply mord_lt
  · rintro (i | ⟨i, j⟩) hx
    · exact natDegree_le_mdeg (S.mem_F_of_Q (mem_Fp_inl.mp hx))
    · have hx' := mem_Fp_inr.mp hx
      exact (S.natDegree_ev'_inr hx'.1.2).le.trans (natDegree_le_mdeg (S.mem_F_of_Q hx'.1.1))
  · refine lt_of_le_of_lt (le_trans (Finset.card_le_card ?_)
      (Finset.card_map (f := ⟨Sum.inl, Sum.inl_injective⟩) (s := S.Q.filter fun i => (ev i).natDegree = mdeg F ev)).le) S.card_Q_lt
    rintro (i | ⟨i, j⟩) hx
    · rw [Finset.mem_filter] at hx
      refine Finset.mem_map.mpr ⟨i, Finset.mem_filter.mpr ⟨mem_Fp_inl.mp hx.1, hx.2⟩, rfl⟩
    · exfalso
      rw [Finset.mem_filter] at hx
      have hx' := mem_Fp_inr.mp hx.1
      have h1 := S.natDegree_ev'_inr (j := j) hx'.1.2
      have h2 := natDegree_le_mdeg (ev := ev) (S.mem_F_of_Q hx'.1.1)
      rw [hx.2] at h1
      omega

theorem natDegree_peP {a : A} (ha : a ∈ B) : (pe (ev S.iP) a).natDegree = mdeg F ev := by
  rw [← S.hdeg]
  apply (pe_nrm (S.hN S.iP S.hiP a ha)).1

/-- The derivative witness of a member of `Q` is not `P`. -/
theorem dcl_Q : DCl S.Q ev B := by
  intro a ha i hi
  obtain ⟨j, hj, hje⟩ := S.hD a ha i (S.mem_F_of_Q hi)
  refine ⟨j, ?_, hje⟩
  refine S.mem_Q.mpr ⟨fun hjP => ?_, hj⟩
  subst hjP
  have h1 := S.natDegree_peP ha
  have h2 : (derivative (pe (ev i) a)).natDegree ≤ mdeg F ev - 1 :=
    (natDegree_derivative_le _).trans (Nat.sub_le_sub_right
      ((natDegree_map_le).trans (natDegree_le_mdeg (S.mem_F_of_Q hi))) 1)
  have h3 : (pe (ev S.iP) a).natDegree = (derivative (pe (ev i) a)).natDegree := by
    simp only at hje; rw [hje]
  have := S.hpos
  omega

theorem dcl_F' : DCl S.F' S.ev' B := by
  intro a ha x hx
  rcases x with i | ⟨i, j⟩
  · obtain ⟨j, hj, hje⟩ := S.dcl_Q a ha i (mem_Fp_inl.mp hx)
    exact ⟨Sum.inl j, mem_Fp_inl.mpr hj, hje⟩
  · have hx' := mem_Fp_inr.mp hx
    by_cases hjd : j < mdeg F ev
    · refine ⟨Sum.inr (i, j + 1), mem_Fp_inr.mpr ⟨hx'.1, by omega⟩, ?_⟩
      show pe (derivative^[j + 1] (S.rem i)) a = derivative (pe (derivative^[j] (S.rem i)) a)
      rw [pe_iterate_derivative, pe_iterate_derivative, Function.iterate_succ_apply']
    · refine ⟨Sum.inr (i, j), hx, ?_⟩
      have hz : derivative^[j] (S.rem i) = 0 := by
        apply iterate_derivative_eq_zero
        have := (S.hrem i hx'.1.2).2
        have := natDegree_le_mdeg (ev := ev) (S.mem_F_of_Q hx'.1.1)
        omega
      show pe (derivative^[j] (S.rem i)) a = derivative (pe (derivative^[j] (S.rem i)) a)
      rw [hz, pe_zero', derivative_zero]

/-- At a root of a nonconstant `q ∈ Q`, `P` has the sign of the remainder. -/
theorem sign_rem {a : A} (ha : a ∈ B) {q : ι} (hq : q ∈ S.Q) (hdq : 0 < (ev q).natDegree)
    {y : ℝ} (hy : (pe (ev q) a).eval y = 0) :
    SignType.sign ((pe (ev S.iP) a).eval y) = SignType.sign ((pe (S.rem q) a).eval y) := by
  have hne : ev q ≠ 0 := by
    intro h0; rw [h0, natDegree_zero] at hdq; exact lt_irrefl _ hdq
  have hc : (((ev q).leadingCoeff : R) : A → ℝ) a ≠ 0 := by
    rcases S.hN q (S.mem_F_of_Q hq) a ha with h | h
    · exact h
    · exact absurd h hne
  exact sign_at_root hc (pe_identity (S.hrem q hdq).1 a) hy

end SD

end TSd

end SubanalyticLib

/-! SubanalyticLib CS-3 TS-d (part 2): the per-parameter case analysis of one step.
Case A (some nonconstant `q ∈ Q` must vanish): replace `P` by its remainder.
Case B0 (a nonzero constant must vanish): empty.
Case C (only formally-zero members may vanish): the cell `C` of `Q` is an open interval on
which `P` is strictly monotone; realized signs of `P` are read off at the finite endpoints
(codes of `F'`, `T1`) and at `±∞` (leading coefficients, `T2`/`T3`). Appended to L4TE.lean. -/

open Polynomial Set Filter

namespace SubanalyticLib

section TSd2

open scoped Classical

variable {A : Type*} {R : Subring (A → ℝ)} {ι : Type*}

theorem iSign_erase_iff {κ : Type*} {F : Finset κ} {G : κ → ℝ[X]} {ν : κ → SignType} {k : κ}
    (hk : k ∈ F) {y : ℝ} :
    y ∈ iSign F G ν ↔ y ∈ iSign (F.erase k) G ν ∧ SignType.sign ((G k).eval y) = ν k := by
  constructor
  · intro h
    exact ⟨fun i hi => h i (Finset.mem_of_mem_erase hi), h k hk⟩
  · rintro ⟨h1, h2⟩ i hi
    by_cases hik : i = k
    · subst hik; exact h2
    · exact h1 i (Finset.mem_erase.mpr ⟨hik, hi⟩)

theorem code_of_point {κ : Type*} (F' : Finset κ) (ev' : κ → R[X]) (a : A) (y : ℝ) :
    ∃ c ∈ codes F', a ∈ Rlz F' ev' c ∧
      ∀ x ∈ F', c x = SignType.sign ((pe (ev' x) a).eval y) := by
  obtain ⟨c, hc, hce⟩ := exists_code F' (fun x => SignType.sign ((pe (ev' x) a).eval y))
  exact ⟨c, hc, ⟨y, fun x hx => (hce x hx).symm⟩, hce⟩

theorem isOpen_sign_eq {f : ℝ → ℝ} (hf : Continuous f) {s : SignType} (hs : s ≠ 0) :
    IsOpen {y | SignType.sign (f y) = s} := by
  rcases s with _ | _ | _
  · exact absurd rfl hs
  · have : {y | SignType.sign (f y) = SignType.neg} = {y | f y < 0} := by
      ext y; simp only [mem_setOf_eq]; exact sign_eq_neg_one_iff
    rw [this]; exact isOpen_lt hf continuous_const
  · have : {y | SignType.sign (f y) = SignType.pos} = {y | 0 < f y} := by
      ext y; simp only [mem_setOf_eq]; exact sign_eq_one_iff
    rw [this]; exact isOpen_lt continuous_const hf

theorem isOpen_iSign {κ : Type*} {Q : Finset κ} {G : κ → ℝ[X]} {ν : κ → SignType}
    (h : ∀ i ∈ Q, ν i = 0 → G i = 0) : IsOpen (iSign Q G ν) := by
  have : iSign Q G ν = ⋂ i ∈ Q, {y | SignType.sign ((G i).eval y) = ν i} := by
    ext y; simp [iSign]
  rw [this]
  apply isOpen_biInter_finset
  intro i hi
  by_cases h0 : ν i = 0
  · have : {y | SignType.sign ((G i).eval y) = ν i} = univ := by
      ext y; simp [h i hi h0, h0]
    rw [this]; exact isOpen_univ
  · exact isOpen_sign_eq (G i).continuous h0

theorem ev_sign_iff {l : Filter ℝ} [l.NeBot] {f : ℝ → ℝ} {c : ℝ}
    (h : ∀ᶠ x in l, SignType.sign (f x) = SignType.sign c) (s : SignType) :
    (∀ᶠ x in l, SignType.sign (f x) = s) ↔ SignType.sign c = s := by
  constructor
  · intro h1
    obtain ⟨x, hx1, hx2⟩ := (h1.and h).exists
    rw [← hx2, hx1]
  · intro hc
    filter_upwards [h] with x hx
    rw [hx, hc]

theorem coe_negpow_mul (n : ℕ) (r : R) (a : A) :
    ((((-1 : R) ^ n * r : R)) : A → ℝ) a = (-1) ^ n * (r : A → ℝ) a := by
  simp

variable {F : Finset ι} {ev : ι → R[X]} {B : Set A}

namespace SD

variable (S : SD F ev B)

/-- Endpoint codes: relax `ν` on `Q`, one nonconstant `q` with strict code drops to `0`, and the
remainder of `P` by `q` has sign `s`. -/
def good (ν : ι → SignType) (s : SignType) (c : ι ⊕ (ι × ℕ) → SignType) : Prop :=
  (∀ i ∈ S.Q, Relax (ν i) (c (Sum.inl i))) ∧
    ∃ q ∈ S.Q, 0 < (ev q).natDegree ∧ ν q ≠ 0 ∧ c (Sum.inl q) = 0 ∧ c (Sum.inr (q, 0)) = s

theorem mem_F'_inl {i : ι} (hi : i ∈ S.Q) : Sum.inl i ∈ S.F' := mem_Fp_inl.mpr hi

theorem mem_F'_inr0 {q : ι} (hq : q ∈ S.Q) (hdq : 0 < (ev q).natDegree) :
    Sum.inr (q, 0) ∈ S.F' := mem_Fp_inr.mpr ⟨⟨hq, hdq⟩, Nat.succ_pos _⟩

theorem caseA_iff {ν : ι → SignType} {q : ι} (hq : q ∈ S.Q) (hνq : ν q = 0)
    (hdq : 0 < (ev q).natDegree) {a : A} (ha : a ∈ B) :
    a ∈ Rlz F ev ν ↔ ∃ c ∈ codes S.F',
      ((∀ i ∈ S.Q, c (Sum.inl i) = ν i) ∧ c (Sum.inr (q, 0)) = ν S.iP) ∧ a ∈ Rlz S.F' S.ev' c := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨c, hc, hRl, hcy⟩ := code_of_point S.F' S.ev' a y
    refine ⟨c, hc, ⟨fun i hi => ?_, ?_⟩, hRl⟩
    · rw [hcy _ (S.mem_F'_inl hi)]; exact hy i (S.mem_F_of_Q hi)
    · rw [hcy _ (S.mem_F'_inr0 hq hdq)]
      have hroot : (pe (ev q) a).eval y = 0 :=
        sign_eq_zero_iff.mp ((hy q (S.mem_F_of_Q hq)).trans hνq)
      show SignType.sign ((pe (S.rem q) a).eval y) = ν S.iP
      rw [← S.sign_rem ha hq hdq hroot]
      exact hy S.iP S.hiP
  · rintro ⟨c, -, ⟨h1, h2⟩, ⟨y, hy⟩⟩
    refine ⟨y, fun i hi => ?_⟩
    have hq' : SignType.sign ((pe (ev q) a).eval y) = c (Sum.inl q) := hy _ (S.mem_F'_inl hq)
    by_cases hiP : i = S.iP
    · subst hiP
      have hroot : (pe (ev q) a).eval y = 0 := sign_eq_zero_iff.mp (by rw [hq', h1 q hq, hνq])
      have h3 : SignType.sign ((pe (S.rem q) a).eval y) = c (Sum.inr (q, 0)) :=
        hy _ (S.mem_F'_inr0 hq hdq)
      show SignType.sign ((pe (ev S.iP) a).eval y) = ν S.iP
      rw [S.sign_rem ha hq hdq hroot, h3, h2]
    · have hiQ : i ∈ S.Q := S.mem_Q.mpr ⟨hiP, hi⟩
      have : SignType.sign ((pe (ev i) a).eval y) = c (Sum.inl i) := hy _ (S.mem_F'_inl hiQ)
      show SignType.sign ((pe (ev i) a).eval y) = ν i
      rw [this, h1 i hiQ]

theorem eval_pe_const {p : R[X]} {a : A} (hl : ((p.leadingCoeff : R) : A → ℝ) a ≠ 0)
    (hd : p.natDegree = 0) (y : ℝ) : (pe p a).eval y = ((p.leadingCoeff : R) : A → ℝ) a := by
  have hpn := pe_nrm (Or.inl hl)
  rw [eval_const (hpn.1.trans hd), ← hpn.2, leadingCoeff, hpn.1, hd]

theorem caseB0 {ν : ι → SignType} {q : ι} (hq : q ∈ S.Q) (hνq : ν q = 0)
    (hdq : (ev q).natDegree = 0) (hne : ev q ≠ 0) {a : A} (ha : a ∈ B) : a ∉ Rlz F ev ν := by
  rintro ⟨y, hy⟩
  have h1 := hy q (S.mem_F_of_Q hq)
  rcases S.hN q (S.mem_F_of_Q hq) a ha with hl | h0
  · simp only at h1
    rw [eval_pe_const hl hdq, hνq] at h1
    exact hl (sign_eq_zero_iff.mp h1)
  · exact hne h0

/-- The cell of `Q` at the parameter `a`. -/
def cell (ν : ι → SignType) (a : A) : Set ℝ := iSign S.Q (fun i => pe (ev i) a) ν

theorem rlz_iff_cell {ν : ι → SignType} {a : A} :
    a ∈ Rlz F ev ν ↔ ∃ y ∈ S.cell ν a, SignType.sign ((pe (ev S.iP) a).eval y) = ν S.iP := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, ((iSign_erase_iff S.hiP).mp hy).1, ((iSign_erase_iff S.hiP).mp hy).2⟩
  · rintro ⟨y, hy, hs⟩
    exact ⟨y, (iSign_erase_iff S.hiP).mpr ⟨hy, hs⟩⟩

theorem cell_ordConnected (ν : ι → SignType) {a : A} (ha : a ∈ B) : (S.cell ν a).OrdConnected :=
  (ithom (S.dcl_Q a ha) ν).1

theorem cell_isOpen {ν : ι → SignType} (hC : ∀ i ∈ S.Q, ν i = 0 → ev i = 0) (a : A) :
    IsOpen (S.cell ν a) :=
  isOpen_iSign fun i hi h0 => by show pe (ev i) a = 0; rw [hC i hi h0, pe_zero']

theorem cell_mono {ν : ι → SignType} (hC : ∀ i ∈ S.Q, ν i = 0 → ev i = 0) {a : A} (ha : a ∈ B) :
    StrictMonoOn (fun y => (pe (ev S.iP) a).eval y) (S.cell ν a) ∨
      StrictAntiOn (fun y => (pe (ev S.iP) a).eval y) (S.cell ν a) := by
  obtain ⟨j, hj, hje⟩ := S.hD a ha S.iP S.hiP
  simp only at hje
  have hdP := S.natDegree_peP ha
  have hpos := S.hpos
  have hjQ : j ∈ S.Q := by
    refine S.mem_Q.mpr ⟨fun hjP => ?_, hj⟩
    subst hjP
    have h2 : (derivative (pe (ev S.iP) a)).natDegree ≤ (pe (ev S.iP) a).natDegree - 1 :=
      natDegree_derivative_le _
    rw [← hje] at h2
    omega
  have hνj : ν j ≠ 0 := by
    intro h0
    have h1 := hC j hjQ h0
    rw [h1, pe_zero'] at hje
    have := derivative_eq_zero.mp hje.symm
    omega
  have hconv : Convex ℝ (S.cell ν a) := convex_iff_ordConnected.mpr (S.cell_ordConnected ν ha)
  have hcont : ContinuousOn (fun y => (pe (ev S.iP) a).eval y) (S.cell ν a) :=
    (pe (ev S.iP) a).continuous.continuousOn
  have hsgn : ∀ y ∈ S.cell ν a,
      SignType.sign ((derivative (pe (ev S.iP) a)).eval y) = ν j := by
    intro y hy
    rw [← hje]; exact hy j hjQ
  rcases hv : ν j with _ | _ | _
  · exact absurd hv hνj
  · right
    apply strictAntiOn_of_deriv_neg hconv hcont
    intro y hy
    have := hsgn y (interior_subset hy)
    rw [hv] at this
    rw [Polynomial.deriv]
    exact sign_eq_neg_one_iff.mp this
  · left
    apply strictMonoOn_of_deriv_pos hconv hcont
    intro y hy
    have := hsgn y (interior_subset hy)
    rw [hv] at this
    rw [Polynomial.deriv]
    exact sign_eq_one_iff.mp this

/-- `T1`: a finite endpoint of the cell with `sign P = s` is detected by an endpoint code. -/
theorem T1 {ν : ι → SignType} {a : A} (ha : a ∈ B) (s : SignType) :
    (∃ z ∈ closure (S.cell ν a), z ∉ S.cell ν a ∧
        SignType.sign ((pe (ev S.iP) a).eval z) = s) ↔
      (a ∈ Rlz S.Q ev ν ∧ ∃ c ∈ codes S.F', S.good ν s c ∧ a ∈ Rlz S.F' S.ev' c) := by
  constructor
  · rintro ⟨z, hzcl, hzC, hzs⟩
    have hne : (S.cell ν a).Nonempty := closure_nonempty_iff.mp ⟨z, hzcl⟩
    refine ⟨hne, ?_⟩
    have hzR := closure_iSign_subset _ _ _ hzcl
    obtain ⟨q, hq, hqne⟩ : ∃ q ∈ S.Q, SignType.sign ((pe (ev q) a).eval z) ≠ ν q := by
      by_contra hcon
      push Not at hcon
      exact hzC hcon
    have hq0 : SignType.sign ((pe (ev q) a).eval z) = 0 := (hzR q hq).resolve_left hqne
    have hνq : ν q ≠ 0 := fun h => hqne (hq0.trans h.symm)
    obtain ⟨x, hx⟩ := hne
    have hdq : 0 < (ev q).natDegree := by
      by_contra hd
      have hd0 : (ev q).natDegree = 0 := by omega
      rcases S.hN q (S.mem_F_of_Q hq) a ha with hl | h0
      · rw [eval_pe_const hl hd0] at hq0
        exact hl (sign_eq_zero_iff.mp hq0)
      · have := hx q hq
        simp only at this
        rw [h0, pe_zero', eval_zero, sign_zero] at this
        exact hνq this.symm
    obtain ⟨c, hc, hRl, hcz⟩ := code_of_point S.F' S.ev' a z
    refine ⟨c, hc, ⟨fun i hi => ?_, q, hq, hdq, hνq, ?_, ?_⟩, hRl⟩
    · rw [hcz _ (S.mem_F'_inl hi)]; exact hzR i hi
    · rw [hcz _ (S.mem_F'_inl hq)]; exact hq0
    · rw [hcz _ (S.mem_F'_inr0 hq hdq)]
      show SignType.sign ((pe (S.rem q) a).eval z) = s
      rw [← S.sign_rem ha hq hdq (sign_eq_zero_iff.mp hq0)]
      exact hzs
  · rintro ⟨⟨x, hx⟩, c, -, ⟨hrel, q, hq, hdq, hνq, hcq, hcs⟩, ⟨z, hz⟩⟩
    have hzR : z ∈ iRelax S.Q (fun i => pe (ev i) a) ν := by
      intro i hi
      have : SignType.sign ((pe (ev i) a).eval z) = c (Sum.inl i) := hz _ (S.mem_F'_inl hi)
      show Relax (ν i) (SignType.sign ((pe (ev i) a).eval z))
      rw [this]; exact hrel i hi
    have h2 : SignType.sign ((pe (ev q) a).eval z) = c (Sum.inl q) := hz _ (S.mem_F'_inl hq)
    have hroot : (pe (ev q) a).eval z = 0 := sign_eq_zero_iff.mp (h2.trans hcq)
    refine ⟨z, mem_closure_of_iRelax (ithom_relax (S.dcl_Q a ha) ⟨x, hx⟩) hx hzR, ?_, ?_⟩
    · intro hzC
      have h1 : SignType.sign ((pe (ev q) a).eval z) = ν q := hzC q hq
      rw [h2, hcq] at h1
      exact hνq h1.symm
    · have h3 : SignType.sign ((pe (S.rem q) a).eval z) = c (Sum.inr (q, 0)) :=
        hz _ (S.mem_F'_inr0 hq hdq)
      rw [S.sign_rem ha hq hdq hroot, h3, hcs]

/-- `T2`: the cell contains a neighbourhood of `+∞`. -/
theorem T2 {ν : ι → SignType} {a : A} (ha : a ∈ B) :
    (∀ᶠ y in atTop, y ∈ S.cell ν a) ↔
      ∀ i ∈ S.Q, ν i = SignType.sign ((((ev i).leadingCoeff : R) : A → ℝ) a) := by
  rw [cell, eventually_mem_iSign_atTop_iff]
  have h : ∀ i ∈ S.Q, (pe (ev i) a).leadingCoeff = (((ev i).leadingCoeff : R) : A → ℝ) a :=
    fun i hi => (pe_nrm (S.hN i (S.mem_F_of_Q hi) a ha)).2
  constructor
  · intro h1 i hi; rw [h1 i hi, h i hi]
  · intro h1 i hi; rw [h1 i hi, h i hi]

theorem lcN_eq {p : R[X]} {a : A} (h : ((p.leadingCoeff : R) : A → ℝ) a ≠ 0 ∨ p = 0) :
    ((pe p a).comp (-X)).leadingCoeff =
      ((((-1 : R) ^ p.natDegree * p.leadingCoeff : R)) : A → ℝ) a := by
  rw [leadingCoeff_comp_neg_X, coe_negpow_mul, (pe_nrm h).1, (pe_nrm h).2]

/-- `T3`: the cell contains a neighbourhood of `-∞`. -/
theorem T3 {ν : ι → SignType} {a : A} (ha : a ∈ B) :
    (∀ᶠ y in atBot, y ∈ S.cell ν a) ↔
      ∀ i ∈ S.Q, ν i =
        SignType.sign (((((-1 : R) ^ (ev i).natDegree * (ev i).leadingCoeff : R)) : A → ℝ) a) := by
  rw [cell, eventually_mem_iSign_atBot_iff]
  have h := fun i (hi : i ∈ S.Q) => lcN_eq (S.hN i (S.mem_F_of_Q hi) a ha)
  constructor
  · intro h1 i hi; rw [h1 i hi, h i hi]
  · intro h1 i hi; rw [h1 i hi, h i hi]

theorem P_atTop {a : A} (ha : a ∈ B) (s : SignType) :
    (∀ᶠ y in atTop, SignType.sign ((pe (ev S.iP) a).eval y) = s) ↔
      SignType.sign ((((ev S.iP).leadingCoeff : R) : A → ℝ) a) = s := by
  rw [← (pe_nrm (S.hN S.iP S.hiP a ha)).2]
  exact ev_sign_iff (eventually_sign_atTop _) s

theorem P_atBot {a : A} (ha : a ∈ B) (s : SignType) :
    (∀ᶠ y in atBot, SignType.sign ((pe (ev S.iP) a).eval y) = s) ↔
      SignType.sign (((((-1 : R) ^ (ev S.iP).natDegree * (ev S.iP).leadingCoeff : R)) :
        A → ℝ) a) = s := by
  rw [← lcN_eq (S.hN S.iP S.hiP a ha)]
  exact ev_sign_iff (eventually_sign_atBot _) s

end SD

end TSd2

end SubanalyticLib

/-! SubanalyticLib CS-3 TS-d (part 3): assembly. One elimination step is SA given the
induction hypothesis on `Q` and `F'`; well-founded induction on `(max degree, count)` with
normalisation gives the **parametric one-variable Tarski–Seidenberg theorem** `ts`:
for a derivative-closed (at every parameter) finite family of polynomials in one variable with
coefficients in a subring `R` of `A → ℝ`, every realizable-sign-condition set
`{a | ∃ y, ∀ i ∈ F, sign ((pe (ev i) a).eval y) = ν i}` is in the Boolean algebra generated by
`{f > 0}`, `{f = 0}`, `f ∈ R`. Appended to L4TF.lean. -/

open Polynomial Set Filter

namespace SubanalyticLib

section TSd3

open scoped Classical

variable {A : Type*} {R : Subring (A → ℝ)} {ι : Type*}

theorem realized_sign_iff {C : Set ℝ} {f : ℝ → ℝ} (hC : C.OrdConnected) (hCo : IsOpen C)
    (hm : StrictMonoOn f C ∨ StrictAntiOn f C) (hf : Continuous f) {s : SignType} (hs : s ≠ 0) :
    (∃ y ∈ C, SignType.sign (f y) = s) ↔
      (∃ z ∈ closure C, z ∉ C ∧ SignType.sign (f z) = s) ∨
      ((∀ᶠ x in atTop, x ∈ C) ∧ ∀ᶠ x in atTop, SignType.sign (f x) = s) ∨
      ((∀ᶠ x in atBot, x ∈ C) ∧ ∀ᶠ x in atBot, SignType.sign (f x) = s) := by
  rcases s with _ | _ | _
  · exact absurd rfl hs
  · have := realized_neg_iff hC hCo hm hf
    simp only [show SignType.neg = -1 from rfl, sign_eq_neg_one_iff]
    exact this
  · have := realized_pos_iff hC hCo hm hf
    simp only [show SignType.pos = 1 from rfl, sign_eq_one_iff]
    exact this

theorem isSA_coe_sign (r : R) (s : SignType) : IsSA R {a : A | SignType.sign ((r : A → ℝ) a) = s} :=
  IsSA.sign r.2 s

variable {F : Finset ι} {ev : ι → R[X]} {B : Set A}

namespace SD

variable (S : SD F ev B)

/-- Parameters with a good endpoint code. -/
def U (ν : ι → SignType) (s : SignType) : Set A :=
  {a | ∃ c ∈ codes S.F', S.good ν s c ∧ a ∈ Rlz S.F' S.ev' c}

def TopS (ν : ι → SignType) : Set A :=
  {a | ∀ i ∈ S.Q, ν i = SignType.sign ((((ev i).leadingCoeff : R) : A → ℝ) a)}

def BotS (ν : ι → SignType) : Set A :=
  {a | ∀ i ∈ S.Q, ν i =
    SignType.sign (((((-1 : R) ^ (ev i).natDegree * (ev i).leadingCoeff : R)) : A → ℝ) a)}

def RealS (ν : ι → SignType) (s : SignType) : Set A :=
  (Rlz S.Q ev ν ∩ S.U ν s) ∪
    ((S.TopS ν ∩ {a | SignType.sign ((((ev S.iP).leadingCoeff : R) : A → ℝ) a) = s}) ∪
     (S.BotS ν ∩ {a | SignType.sign (((((-1 : R) ^ (ev S.iP).natDegree *
        (ev S.iP).leadingCoeff : R)) : A → ℝ) a) = s}))

theorem real_iff {ν : ι → SignType} (hC : ∀ i ∈ S.Q, ν i = 0 → ev i = 0) {a : A} (ha : a ∈ B)
    {s : SignType} (hs : s ≠ 0) :
    (∃ y ∈ S.cell ν a, SignType.sign ((pe (ev S.iP) a).eval y) = s) ↔ a ∈ S.RealS ν s := by
  refine (realized_sign_iff (S.cell_ordConnected ν ha) (S.cell_isOpen hC a) (S.cell_mono hC ha)
    (pe (ev S.iP) a).continuous hs).trans ?_
  beta_reduce
  rw [S.T1 ha s, S.T2 ha, S.P_atTop ha s, S.T3 ha, S.P_atBot ha s]
  exact Iff.rfl

theorem caseC_eq {ν : ι → SignType} (hC : ∀ i ∈ S.Q, ν i = 0 → ev i = 0) :
    B ∩ Rlz F ev ν = B ∩ (if ν S.iP = 0 then S.RealS ν 1 ∩ S.RealS ν (-1)
      else S.RealS ν (ν S.iP)) := by
  ext a
  simp only [mem_inter_iff]
  refine and_congr_right fun ha => ?_
  rw [S.rlz_iff_cell]
  split_ifs with h0
  · rw [h0, mem_inter_iff, ← S.real_iff hC ha one_ne_zero, ← S.real_iff hC ha (by decide)]
    simp only [sign_eq_zero_iff, sign_eq_one_iff, sign_eq_neg_one_iff]
    exact realized_zero_iff (S.cell_ordConnected ν ha) (S.cell_isOpen hC a) (S.cell_mono hC ha)
      (pe (ev S.iP) a).continuous
  · exact S.real_iff hC ha h0

theorem isSA_inter_union {X Y : Set A} (hX : IsSA R (B ∩ X)) (hY : IsSA R (B ∩ Y)) :
    IsSA R (B ∩ (X ∪ Y)) := by
  rw [inter_union_distrib_left]; exact hX.union hY

theorem isSA_inter_inter {X Y : Set A} (hX : IsSA R (B ∩ X)) (hY : IsSA R (B ∩ Y)) :
    IsSA R (B ∩ (X ∩ Y)) := by
  rw [inter_inter_distrib_left]; exact hX.inter hY

theorem isSA_RealS (hB : IsSA R B) (ν : ι → SignType) (hQ : IsSA R (B ∩ Rlz S.Q ev ν))
    (hF' : ∀ c, IsSA R (B ∩ Rlz S.F' S.ev' c)) (s : SignType) : IsSA R (B ∩ S.RealS ν s) := by
  have hU : IsSA R (B ∩ S.U ν s) := by
    have : B ∩ S.U ν s = ⋃ c ∈ (codes S.F').filter (S.good ν s), B ∩ Rlz S.F' S.ev' c := by
      ext a
      simp only [U, mem_inter_iff, mem_setOf_eq, mem_iUnion, Finset.mem_filter, exists_prop]
      constructor
      · rintro ⟨hB', c, hc, hg, hR⟩; exact ⟨c, ⟨hc, hg⟩, hB', hR⟩
      · rintro ⟨c, ⟨hc, hg⟩, hB', hR⟩; exact ⟨hB', c, hc, hg, hR⟩
    rw [this]
    exact IsSA.biUnion _ fun c _ => hF' c
  have hTop : IsSA R (S.TopS ν) := by
    have : S.TopS ν = ⋂ i ∈ S.Q,
        {a : A | SignType.sign ((((ev i).leadingCoeff : R) : A → ℝ) a) = ν i} := by
      ext a; simp only [TopS, mem_setOf_eq, mem_iInter]
      exact forall₂_congr fun i _ => eq_comm
    rw [this]; exact IsSA.biInter _ fun i _ => isSA_coe_sign _ _
  have hBot : IsSA R (S.BotS ν) := by
    have : S.BotS ν = ⋂ i ∈ S.Q, {a : A | SignType.sign (((((-1 : R) ^ (ev i).natDegree *
        (ev i).leadingCoeff : R)) : A → ℝ) a) = ν i} := by
      ext a; simp only [BotS, mem_setOf_eq, mem_iInter]
      exact forall₂_congr fun i _ => eq_comm
    rw [this]; exact IsSA.biInter _ fun i _ => isSA_coe_sign _ _
  unfold RealS
  refine isSA_inter_union (isSA_inter_inter hQ hU) (isSA_inter_union ?_ ?_)
  · exact hB.inter (hTop.inter (isSA_coe_sign _ _))
  · exact hB.inter (hBot.inter (isSA_coe_sign _ _))

/-- **One elimination step.** -/
theorem ts_step (hB : IsSA R B) (ν : ι → SignType) (hQ : IsSA R (B ∩ Rlz S.Q ev ν))
    (hF' : ∀ c, IsSA R (B ∩ Rlz S.F' S.ev' c)) : IsSA R (B ∩ Rlz F ev ν) := by
  by_cases hA : ∃ q ∈ S.Q, ν q = 0 ∧ 0 < (ev q).natDegree
  · obtain ⟨q, hq, hνq, hdq⟩ := hA
    have : B ∩ Rlz F ev ν = ⋃ c ∈ (codes S.F').filter
        (fun c => (∀ i ∈ S.Q, c (Sum.inl i) = ν i) ∧ c (Sum.inr (q, 0)) = ν S.iP),
        B ∩ Rlz S.F' S.ev' c := by
      ext a
      simp only [mem_inter_iff, mem_iUnion, Finset.mem_filter, exists_prop]
      constructor
      · rintro ⟨ha, hR⟩
        obtain ⟨c, hc, hcond, hR'⟩ := (S.caseA_iff hq hνq hdq ha).mp hR
        exact ⟨c, ⟨hc, hcond⟩, ha, hR'⟩
      · rintro ⟨c, ⟨hc, hcond⟩, ha, hR'⟩
        exact ⟨ha, (S.caseA_iff hq hνq hdq ha).mpr ⟨c, hc, hcond, hR'⟩⟩
    rw [this]
    exact IsSA.biUnion _ fun c _ => hF' c
  by_cases hB0 : ∃ q ∈ S.Q, ν q = 0 ∧ (ev q).natDegree = 0 ∧ ev q ≠ 0
  · obtain ⟨q, hq, hνq, hdq, hne⟩ := hB0
    have : B ∩ Rlz F ev ν = ∅ := by
      ext a
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
      exact fun ha => S.caseB0 hq hνq hdq hne ha
    rw [this]; exact IsSA.empty
  have hC : ∀ i ∈ S.Q, ν i = 0 → ev i = 0 := by
    intro i hi h0
    by_contra hne
    have hd : (ev i).natDegree = 0 := by
      by_contra hd
      exact hA ⟨i, hi, h0, Nat.pos_of_ne_zero hd⟩
    exact hB0 ⟨i, hi, h0, hd, hne⟩
  rw [S.caseC_eq hC]
  split_ifs
  · exact isSA_inter_inter (S.isSA_RealS hB ν hQ hF' 1) (S.isSA_RealS hB ν hQ hF' (-1))
  · exact S.isSA_RealS hB ν hQ hF' _

end SD

/-- Base case: all members constant. -/
theorem ts_base {F : Finset ι} {ev : ι → R[X]} (hd : mdeg F ev = 0) (ν : ι → SignType) :
    IsSA R (Rlz (A := A) F ev ν) := by
  have hc : ∀ i ∈ F, ∀ (a : A) (y : ℝ),
      (pe (ev i) a).eval y = ((((ev i).coeff 0) : R) : A → ℝ) a := by
    intro i hi a y
    have h0 : (pe (ev i) a).natDegree = 0 := by
      have := (natDegree_map_le (p := ev i) (f := evR a)).trans (natDegree_le_mdeg hi)
      unfold pe; omega
    rw [eval_const h0, pe_coeff]
  have : Rlz (A := A) F ev ν =
      ⋂ i ∈ F, {a : A | SignType.sign (((((ev i).coeff 0) : R) : A → ℝ) a) = ν i} := by
    ext a
    simp only [Rlz, mem_setOf_eq, mem_iInter]
    constructor
    · rintro ⟨y, hy⟩ i hi
      rw [← hc i hi a y]; exact hy i hi
    · intro h
      exact ⟨0, fun i hi => by simp only; rw [hc i hi a 0]; exact h i hi⟩
  rw [this]
  exact IsSA.biInter _ fun i _ => isSA_coe_sign _ _

theorem ts_main : ∀ (o : ℕ ×ₗ ℕ) {κ : Type} (F : Finset κ) (ev : κ → R[X]), mord F ev ≤ o →
    ∀ B : Set A, IsSA R B → DCl F ev B → ∀ ν : κ → SignType, IsSA R (B ∩ Rlz F ev ν) := by
  intro o
  induction o using WellFoundedLT.induction with
  | _ o IH =>
    intro κ F ev hle B hB hD ν
    refine isSA_of_branches hB (mdeg F ev) (fun i hi => natDegree_le_mdeg hi) fun e => ?_
    set ev1 := evTr F ev (mdeg F ev) e with hev1
    set B1 := B ∩ BrE F ev (mdeg F ev) e with hB1def
    have hB1 : IsSA R B1 := hB.inter (isSA_BrE F ev _ e)
    have hN1 : Nrm F ev1 B1 := fun i hi a ha => nrm_evTr e i hi a ha.2
    have hD1 : DCl F ev1 B1 := dcl_evTr (fun i hi => natDegree_le_mdeg hi) hD e
    have hle1 : mord F ev1 ≤ o := (mord_mono fun i _ => natDegree_evTr_le e i).trans hle
    by_cases hd0 : mdeg F ev1 = 0
    · exact hB1.inter (ts_base hd0 ν)
    have hFne : F.Nonempty := by
      by_contra hem
      rw [Finset.not_nonempty_iff_eq_empty] at hem
      apply hd0; rw [mdeg, hem]; rfl
    obtain ⟨iP, hiP, hiPeq⟩ := Finset.exists_mem_eq_sup F hFne fun i => (ev1 i).natDegree
    obtain ⟨kk, ss, rem, hrem⟩ := exists_rem ev1 (ev1 iP)
    let S : SD F ev1 B1 :=
      { iP := iP, hiP := hiP, hdeg := hiPeq.symm, hpos := Nat.pos_of_ne_zero hd0,
        rem := rem, kk := kk, ss := ss, hrem := hrem, hN := hN1, hD := hD1 }
    exact S.ts_step hB1 ν
      (IH _ (lt_of_lt_of_le S.mord_Q_lt hle1) S.Q ev1 le_rfl B1 hB1 S.dcl_Q ν)
      (fun c => IH _ (lt_of_lt_of_le S.mord_F'_lt hle1) S.F' S.ev' le_rfl B1 hB1 S.dcl_F' c)

/-- **Parametric Tarski–Seidenberg in one variable** (derivative-closed families). -/
theorem ts {κ : Type} (F : Finset κ) (ev : κ → R[X])
    (hD : ∀ a : A, IDerivClosed F (fun i => pe (ev i) a)) (ν : κ → SignType) :
    IsSA R (Rlz (A := A) F ev ν) := by
  have := ts_main _ F ev le_rfl univ IsSA.univ (fun a _ => hD a) ν
  rwa [univ_inter] at this

end TSd3

end SubanalyticLib

/-! SubanalyticLib CS-3 TS-e: Tarski–Seidenberg for an arbitrary finite family (close it under
derivatives first). Appended to L4TG.lean. -/

open Polynomial Set Filter

namespace SubanalyticLib

section TSe

open scoped Classical

variable {A : Type*} {R : Subring (A → ℝ)}

/-- **Parametric Tarski–Seidenberg in one variable**, any finite family. -/
theorem ts_any {κ : Type} (F : Finset κ) (ev : κ → R[X]) (ν : κ → SignType) :
    IsSA R (Rlz (A := A) F ev ν) := by
  set D := mdeg F ev
  set Ft : Finset (κ × ℕ) := F ×ˢ Finset.range (D + 2) with hFt
  set evt : κ × ℕ → R[X] := fun x => derivative^[x.2] (ev x.1) with hevt
  have hmem : ∀ i j, (i, j) ∈ Ft ↔ i ∈ F ∧ j < D + 2 := by
    intro i j; simp [hFt]
  have hDt : ∀ a : A, IDerivClosed Ft (fun x => pe (evt x) a) := by
    rintro a ⟨i, j⟩ hx
    have hx' := (hmem i j).mp hx
    by_cases hj : j < D + 1
    · refine ⟨(i, j + 1), (hmem i (j + 1)).mpr ⟨hx'.1, by omega⟩, ?_⟩
      show pe (derivative^[j + 1] (ev i)) a = derivative (pe (derivative^[j] (ev i)) a)
      rw [pe_iterate_derivative, pe_iterate_derivative, Function.iterate_succ_apply']
    · refine ⟨(i, j), hx, ?_⟩
      have hz : derivative^[j] (ev i) = 0 := by
        apply iterate_derivative_eq_zero
        have := natDegree_le_mdeg (ev := ev) hx'.1
        omega
      show pe (derivative^[j] (ev i)) a = derivative (pe (derivative^[j] (ev i)) a)
      rw [hz, pe_zero', derivative_zero]
  have h0mem : ∀ i ∈ F, (i, 0) ∈ Ft := fun i hi => (hmem i 0).mpr ⟨hi, by omega⟩
  have : Rlz (A := A) F ev ν =
      ⋃ c ∈ (codes Ft).filter (fun c => ∀ i ∈ F, c (i, 0) = ν i), Rlz Ft evt c := by
    ext a
    simp only [mem_iUnion, Finset.mem_filter, exists_prop]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨c, hc, hRl, hcy⟩ := code_of_point Ft evt a y
      refine ⟨c, ⟨hc, fun i hi => ?_⟩, hRl⟩
      rw [hcy _ (h0mem i hi)]
      exact hy i hi
    · rintro ⟨c, ⟨-, hc⟩, ⟨y, hy⟩⟩
      refine ⟨y, fun i hi => ?_⟩
      have := hy (i, 0) (h0mem i hi)
      show SignType.sign ((pe (ev i) a).eval y) = ν i
      rw [← hc i hi]
      exact this
  rw [this]
  exact IsSA.biUnion _ fun c _ => ts Ft evt hDt c

end TSe

end SubanalyticLib


/-! SubanalyticLib CS-6a: sign-code normal form of `IsSA` sets; monotonicity in the ring.
(Appended to L4s_SA.lean.) -/

namespace SubanalyticLib

section Code

variable {A : Type*}

/-- `S` is the set where the sign vector of finitely many functions of `R` lies in `N`. -/
def CodeForm (R : Subring (A → ℝ)) (S : Set A) : Prop :=
  ∃ (n : ℕ) (h : Fin n → A → ℝ), (∀ i, h i ∈ R) ∧
    ∃ N : Set (Fin n → SignType), S = {a | (fun i => SignType.sign (h i a)) ∈ N}

theorem IsSA.mono {R R' : Subring (A → ℝ)} (hRR : R ≤ R') {S : Set A} (hS : IsSA R S) :
    IsSA R' S := by
  induction hS with
  | pos hf => exact IsSA.pos (hRR hf)
  | zero hf => exact IsSA.zero (hRR hf)
  | compl _ ih => exact IsSA.compl ih
  | inter _ _ ih1 ih2 => exact IsSA.inter ih1 ih2

theorem IsSA.codeForm {R : Subring (A → ℝ)} {S : Set A} (hS : IsSA R S) : CodeForm R S := by
  induction hS with
  | @pos f hf =>
    refine ⟨1, ![f], fun i => by fin_cases i; exact hf, {c | c 0 = 1}, ?_⟩
    ext a
    simp [sign_eq_one_iff]
  | @zero f hf =>
    refine ⟨1, ![f], fun i => by fin_cases i; exact hf, {c | c 0 = 0}, ?_⟩
    ext a
    simp [sign_eq_zero_iff]
  | compl _ ih =>
    obtain ⟨n, h, hh, N, hN⟩ := ih
    refine ⟨n, h, hh, Nᶜ, ?_⟩
    rw [hN]
    rfl
  | inter _ _ ih1 ih2 =>
    obtain ⟨n, h, hh, N, hN⟩ := ih1
    obtain ⟨m, g, hg, M, hM⟩ := ih2
    refine ⟨n + m, Fin.append h g, fun i => ?_,
      {c | (fun i => c (Fin.castAdd m i)) ∈ N ∧ (fun j => c (Fin.natAdd n j)) ∈ M}, ?_⟩
    · refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · rw [Fin.append_left]; exact hh i
      · rw [Fin.append_right]; exact hg j
    · rw [hN, hM]
      ext a
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Fin.append_left, Fin.append_right]

end Code

end SubanalyticLib


/-! SubanalyticLib CS-1: a non-zero analytic germ becomes regular in a coordinate after a
linear change of coordinates (a shear), the first step of every Weierstrass-preparation induction. -/

open Filter Topology Set

set_option linter.unusedSectionVars false

namespace SubanalyticLib

/-- A germ that is not `≡ 0` near `0` is not `≡ 0` along some line through `0`. -/
theorem exists_dir_nonzero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    (hf : AnalyticAt ℝ f 0) (hnz : ¬ ∀ᶠ x in 𝓝 (0 : E), f x = 0) :
    ∃ v : E, ¬ ∀ᶠ t in 𝓝 (0 : ℝ), f (t • v) = 0 := by
  by_contra hall
  push Not at hall
  apply hnz
  obtain ⟨r, hr, hball⟩ := hf.exists_ball_analyticOnNhd
  filter_upwards [Metric.ball_mem_nhds (0 : E) hr] with x hx
  set U : Set ℝ := {t : ℝ | t • x ∈ Metric.ball (0 : E) r} with hU
  have hUo : IsOpen U :=
    Metric.isOpen_ball.preimage (continuous_id.smul continuous_const)
  have hUc : Convex ℝ U := by
    have hUeq : U = (LinearMap.toSpanSingleton ℝ E x) ⁻¹' Metric.ball 0 r := by
      ext t; simp [hU]
    rw [hUeq]
    exact (convex_ball (0 : E) r).linear_preimage (LinearMap.toSpanSingleton ℝ E x)
  have h0 : (0 : ℝ) ∈ U := by simp [hU, hr]
  have h1 : (1 : ℝ) ∈ U := by simpa [hU] using hx
  have han : AnalyticOnNhd ℝ (fun t : ℝ => f (t • x)) U := by
    intro t ht
    have hlin : AnalyticAt ℝ (fun t : ℝ => t • x) t :=
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) x).analyticAt t
    exact AnalyticAt.comp (g := f) (f := fun t : ℝ => t • x) (hball (t • x) ht) hlin
  have hev : (fun t : ℝ => f (t • x)) =ᶠ[𝓝 0] 0 := hall x
  have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc.isPreconnected h0 hev h1
  simpa using this

/-- The shear `x ↦ x + x k • w` (with `w k = 0`) as a continuous linear equivalence. -/
noncomputable def shear {σ : Type*} [Fintype σ] [DecidableEq σ] (k : σ) (w : σ → ℝ) (hw : w k = 0) :
    (σ → ℝ) ≃L[ℝ] (σ → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x => x + x k • w
      map_add' := by intro x y; simp only [Pi.add_apply, add_smul]; abel
      map_smul' := by intro c x; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
        smul_add, mul_smul]
      invFun := fun x => x - x k • w
      left_inv := by intro x; simp [hw]
      right_inv := by intro x; simp [hw] }

theorem shear_apply {σ : Type*} [Fintype σ] [DecidableEq σ] (k : σ) (w : σ → ℝ) (hw : w k = 0)
    (x : σ → ℝ) : shear k w hw x = x + x k • w := rfl

/-- **Generic regularity.** A non-zero analytic germ on `σ → ℝ` becomes regular in some coordinate
`k` (not `≡ 0` on the `k`-axis) after a linear change of coordinates. -/
theorem exists_regular_coord {σ : Type*} [Fintype σ] [DecidableEq σ] [Nonempty σ]
    {f : (σ → ℝ) → ℝ} (hf : AnalyticAt ℝ f 0) (hnz : ¬ ∀ᶠ x in 𝓝 (0 : σ → ℝ), f x = 0) :
    ∃ k : σ, ∃ L : (σ → ℝ) ≃L[ℝ] (σ → ℝ),
      ¬ ∀ᶠ t in 𝓝 (0 : ℝ), f (L (Pi.single k t)) = 0 := by
  obtain ⟨v, hv⟩ := exists_dir_nonzero hf hnz
  by_cases hv0 : v = 0
  · -- f 0 ≠ 0: any coordinate, identity map
    obtain ⟨k⟩ := ‹Nonempty σ›
    refine ⟨k, ContinuousLinearEquiv.refl ℝ _, ?_⟩
    intro h; apply hv
    have hf0 : f 0 = 0 := by
      have := h.self_of_nhds
      simpa using this
    filter_upwards with t
    simp [hv0, hf0]
  · obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
      by_contra hcon; push Not at hcon; exact hv0 (funext hcon)
    set w : σ → ℝ := (v k)⁻¹ • v - Pi.single k 1 with hw
    have hwk : w k = 0 := by simp [hw, hk]
    refine ⟨k, shear k w hwk, ?_⟩
    intro h
    apply hv
    have hL : ∀ t : ℝ, shear k w hwk (Pi.single k t) = (t * (v k)⁻¹) • v := by
      intro t
      rw [shear_apply]
      ext i
      by_cases hi : i = k
      · subst hi; simp [hw, hk]
      · simp [hw, hi]
        ring
    -- reparametrize t ↦ t * v k
    have hmap : Tendsto (fun t : ℝ => t * v k) (𝓝 0) (𝓝 0) := by
      have := (tendsto_id (x := 𝓝 (0:ℝ))).mul_const (v k)
      simpa using this
    filter_upwards [hmap.eventually h] with t ht
    rw [hL] at ht
    have : t * v k * (v k)⁻¹ = t := by field_simp
    rwa [this] at ht

end SubanalyticLib


/-! SubanalyticLib CS-6b: germs of real-analytic functions form an integral domain
(a product of two non-flat analytic germs is non-flat). Standalone. -/

open Filter Topology Set

set_option autoImplicit false

namespace SubanalyticLib

theorem nonflat_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {x₀ : E} (hf : AnalyticAt ℝ f x₀) (hg : AnalyticAt ℝ g x₀)
    (hf0 : ¬ ∀ᶠ x in 𝓝 x₀, f x = 0) (hg0 : ¬ ∀ᶠ x in 𝓝 x₀, g x = 0) :
    ¬ ∀ᶠ x in 𝓝 x₀, f x * g x = 0 := by
  intro hfg
  obtain ⟨r1, hr1, hfA⟩ := hf.exists_ball_analyticOnNhd
  obtain ⟨r2, hr2, hgA⟩ := hg.exists_ball_analyticOnNhd
  obtain ⟨r3, hr3, hball⟩ := Metric.eventually_nhds_iff_ball.mp hfg
  set r := min r1 (min r2 r3) with hr
  have hr0 : 0 < r := lt_min hr1 (lt_min hr2 hr3)
  have hrr1 : r ≤ r1 := min_le_left _ _
  have hrr3 : r ≤ r3 := (min_le_right _ _).trans (min_le_right _ _)
  -- a point of the ball where g ≠ 0
  have hx1 : ∃ x1 ∈ Metric.ball x₀ r, g x1 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hg0 (Filter.mem_of_superset (Metric.ball_mem_nhds x₀ hr0) fun x hx => hcon x hx)
  obtain ⟨x1, hx1B, hgx1⟩ := hx1
  -- near x1, g ≠ 0, so f = 0
  have hfz : f =ᶠ[𝓝 x1] 0 := by
    have hgc : ∀ᶠ x in 𝓝 x1, g x ≠ 0 :=
      (hgA x1 (Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hx1B)
        ).continuousAt.eventually_ne hgx1
    filter_upwards [hgc, Metric.isOpen_ball.mem_nhds hx1B] with x hgx hxB
    have := hball x (Metric.ball_subset_ball hrr3 hxB)
    exact (mul_eq_zero.mp this).resolve_right hgx
  have hEq : EqOn f 0 (Metric.ball x₀ r) :=
    (hfA.mono (Metric.ball_subset_ball hrr1)).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball x₀ r).isPreconnected hx1B hfz
  exact hf0 (Filter.mem_of_superset (Metric.ball_mem_nhds x₀ hr0) fun x hx => hEq hx)

/-- A finite product of non-flat analytic germs is non-flat. -/
theorem nonflat_prod {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}
    (s : Finset ι) {f : ι → E → ℝ} {x₀ : E} (hf : ∀ i ∈ s, AnalyticAt ℝ (f i) x₀)
    (hf0 : ∀ i ∈ s, ¬ ∀ᶠ x in 𝓝 x₀, f i x = 0) :
    AnalyticAt ℝ (fun x => ∏ i ∈ s, f i x) x₀ ∧ ¬ ∀ᶠ x in 𝓝 x₀, ∏ i ∈ s, f i x = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using analyticAt_const, ?_⟩
    simp only [Finset.prod_empty, one_ne_zero, Filter.eventually_false_iff_eq_bot]
    exact NeBot.ne inferInstance
  | insert a s ha ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (fun i hi => hf0 i (Finset.mem_insert_of_mem hi))
    have hA := hf a (Finset.mem_insert_self a s)
    simp only [Finset.prod_insert ha]
    exact ⟨hA.mul ih1, nonflat_mul hA ih1 (hf0 a (Finset.mem_insert_self a s)) ih2⟩

end SubanalyticLib


/-! SubanalyticLib CS-6 shared: the subring `An n` of germs analytic at `0` on `ℝ^n` (body; needs nothing). -/

namespace SubanalyticLib

/-- germs of functions on `ℝ^n` analytic at `0`. -/
def An (n : ℕ) : Subring ((Fin n → ℝ) → ℝ) where
  carrier := {f | AnalyticAt ℝ f 0}
  mul_mem' {a b} ha hb := by
    show AnalyticAt ℝ (fun x => a x * b x) 0
    exact ha.mul hb
  one_mem' := by
    show AnalyticAt ℝ (fun _ => (1 : ℝ)) 0
    exact analyticAt_const
  add_mem' {a b} ha hb := by
    show AnalyticAt ℝ (fun x => a x + b x) 0
    exact ha.add hb
  zero_mem' := by
    show AnalyticAt ℝ (fun _ => (0 : ℝ)) 0
    exact analyticAt_const
  neg_mem' {a} ha := by
    show AnalyticAt ℝ (fun x => -a x) 0
    exact ha.neg

theorem mem_An {n : ℕ} {f : (Fin n → ℝ) → ℝ} : f ∈ An n ↔ AnalyticAt ℝ f 0 := Iff.rfl

lemma snoc_zero_zero (n : ℕ) : (Fin.snoc (0 : Fin n → ℝ) (0 : ℝ) : Fin (n + 1) → ℝ) = 0 := by
  funext i
  induction i using Fin.lastCases with
  | last => simp
  | cast j => simp

end SubanalyticLib


/-! SubanalyticLib CS-6c (body; after L5S-prefix (L3G + WP2) + L6S + L5g + L6b): local polynomial normal form.
Finitely many analytic germs `h k` at `0 ∈ ℝ^(n+1)`: after one linear change of coordinates `L`, on a ball,
`sign (h k (L x)) = ε k * sign (P k (x', y))` with `P k` monic in `y = x (last n)`, coefficients analytic germs
in `x' = Fin.init x` vanishing at `0` (distinguished); flat germs get `ε k = 0`, `P k = 1`. -/

namespace SubanalyticLib

section Form

open Filter Topology Set Polynomial

set_option autoImplicit false

/-- monic polynomial `X^d + Σ_{i<d} b_i X^i` over any commutative ring. -/
noncomputable def mkMon {S : Type*} [CommRing S] (d : ℕ) (b : Fin d → S) : S[X] :=
  X ^ d + ∑ i : Fin d, C (b i) * X ^ (i : ℕ)

lemma mkMon_monic {S : Type*} [CommRing S] [Nontrivial S] (d : ℕ) (b : Fin d → S) :
    (mkMon d b).Monic :=
  monic_X_pow_add (degree_sum_fin_lt b)

lemma mkMon_natDegree {S : Type*} [CommRing S] [Nontrivial S] (d : ℕ) (b : Fin d → S) :
    (mkMon d b).natDegree = d := by
  unfold mkMon
  rw [natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  rw [degree_X_pow]
  exact degree_sum_fin_lt b

lemma mkMon_coeff {S : Type*} [CommRing S] (d : ℕ) (b : Fin d → S) {j : ℕ} (hj : j < d) :
    (mkMon d b).coeff j = b ⟨j, hj⟩ := by
  unfold mkMon
  rw [coeff_add, coeff_X_pow, if_neg hj.ne, zero_add, finset_sum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single ⟨j, hj⟩]
  · simp
  · intro i _ hi
    rw [if_neg]
    intro h; apply hi; ext; exact h.symm
  · intro h; exact absurd (Finset.mem_univ _) h

lemma eval_pe_mkMon {A : Type*} {R : Subring (A → ℝ)} (d : ℕ) (b : Fin d → R) (a : A) (z : ℝ) :
    (pe (mkMon d b) a).eval z = z ^ d + ∑ i : Fin d, (b i : A → ℝ) a * z ^ (i : ℕ) := by
  simp [pe, mkMon, eval_map, eval₂_finset_sum, evR_apply]

/-- a positive lower bound for finitely many positive numbers. -/
lemma exists_pos_le_all {ι : Type*} [Fintype ι] (ρ : ι → ℝ) (h : ∀ k, 0 < ρ k) :
    ∃ r > 0, ∀ k, r ≤ ρ k := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun k => (IsEmpty.false k).elim⟩
  · obtain ⟨k0, -, hk0⟩ := Finset.exists_min_image Finset.univ ρ Finset.univ_nonempty
    exact ⟨ρ k0, h k0, fun k => hk0 k (Finset.mem_univ _)⟩

/-- a continuous function without zeros on a ball has constant sign there. -/
lemma sign_const_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {ρ : ℝ}
    (hc : ContinuousOn f (Metric.ball 0 ρ)) (hne : ∀ x ∈ Metric.ball (0 : E) ρ, f x ≠ 0)
    {x : E} (hx : x ∈ Metric.ball (0 : E) ρ) : SignType.sign (f x) = SignType.sign (f 0) := by
  have h0 : (0 : E) ∈ Metric.ball (0 : E) ρ := by
    have : 0 < ρ := by
      have := Metric.mem_ball.1 hx
      exact lt_of_le_of_lt dist_nonneg this
    exact Metric.mem_ball_self this
  have hpc : IsPreconnected (Metric.ball (0 : E) ρ) := (convex_ball 0 ρ).isPreconnected
  have hx0 := hne x hx
  have h00 := hne 0 h0
  rcases lt_or_gt_of_ne hx0 with hxn | hxp <;> rcases lt_or_gt_of_ne h00 with h0n | h0p
  · rw [sign_neg hxn, sign_neg h0n]
  · exfalso
    obtain ⟨z, hz, hz0⟩ := hpc.intermediate_value hx h0 hc ⟨hxn.le, h0p.le⟩
    exact hne z hz hz0
  · exfalso
    obtain ⟨z, hz, hz0⟩ := hpc.intermediate_value h0 hx hc ⟨h0n.le, hxp.le⟩
    exact hne z hz hz0
  · rw [sign_pos hxp, sign_pos h0p]

lemma analyticAt_snoc0 (n : ℕ) :
    AnalyticAt ℝ (fun x' : Fin n → ℝ => (Fin.snoc x' (0 : ℝ) : Fin (n + 1) → ℝ)) 0 := by
  refine analyticAt_pi_iff.2 fun i => ?_
  induction i using Fin.lastCases with
  | last => simpa using (analyticAt_const : AnalyticAt ℝ (fun _ : Fin n → ℝ => (0 : ℝ)) 0)
  | cast j =>
    simp only [Fin.snoc_castSucc]
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j).analyticAt _

lemma sign_mul_cancel {ε s t : SignType} (hε : ε ≠ 0) (h : t = ε * s) : s = ε * t := by
  subst h
  rcases ε with _ | _ | _
  · exact absurd rfl hε
  · rcases s with _ | _ | _ <;> rfl
  · rcases s with _ | _ | _ <;> rfl

/-- **Local polynomial form of one regular germ.** -/
theorem local_form_one {n : ℕ} {g : (Fin (n + 1) → ℝ) → ℝ} (hg : AnalyticAt ℝ g 0)
    (hax : ¬ ∀ᶠ t in 𝓝 (0 : ℝ), g (Pi.single (Fin.last n) t) = 0) :
    ∃ ρ > 0, ∃ P : (An n)[X], P.Monic ∧
      (∀ i < P.natDegree, ((P.coeff i : An n) : (Fin n → ℝ) → ℝ) 0 = 0) ∧
      ∃ ε : SignType, ∀ x : Fin (n + 1) → ℝ, ‖x‖ < ρ →
        SignType.sign (g x) = ε * SignType.sign ((pe P (Fin.init x)).eval (x (Fin.last n))) := by
  classical
  set y : Fin (n + 1) := Fin.last n with hy
  obtain ⟨a, ρ0, hρ0, hconv, heq⟩ := exists_conv_of_analyticAt hg
  have hex : ∃ j, MvPowerSeries.coeff (Finsupp.single y j) a ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hax
    have hball : ∀ᶠ t in 𝓝 (0 : ℝ), |t| < ρ0 := by
      have := (continuous_abs.tendsto (0 : ℝ))
      simp only [abs_zero] at this
      exact this.eventually (gt_mem_nhds hρ0)
    filter_upwards [hball] with t ht
    have hn : ‖(Pi.single y t : Fin (n + 1) → ℝ)‖ ≤ ρ0 := by
      rw [Pi.norm_single, Real.norm_eq_abs]; exact ht.le
    have := heq _ hn
    rw [zero_add] at this
    rw [this]
    exact ev_single_axis y hcon t
  let d := Nat.find hex
  have hd : MvPowerSeries.coeff (Finsupp.single y d) a ≠ 0 := Nat.find_spec hex
  have hreg : ∀ j < d, MvPowerSeries.coeff (Finsupp.single y j) a = 0 := by
    intro j hj
    by_contra h
    exact Nat.find_min hex hj h
  obtain ⟨w, hw, hwle, q, r, hq, hr, hhat, hr0, hmain⟩ :=
    ev_weierstrass_prep2 y (fun _ => hρ0) d hconv hreg hd
  have hw' : ∀ i, 0 ≤ w i := fun i => (hw i).le
  -- coefficient germs
  have hsl : ∀ j, Conv w (yslice y j r) := fun j => Conv.low y hw' 1 (Conv.hat y hw' (hw y) j hr)
  let c : ℕ → (Fin n → ℝ) → ℝ := fun j x' => ev (yslice y j r) (Fin.snoc x' 0)
  have hcA : ∀ j, c j ∈ An n := by
    intro j
    obtain ⟨r1, hr1, hr1a⟩ := analyticAt_ev_zero hw (hsl j)
    have h0 : AnalyticAt ℝ (ev (yslice y j r)) 0 := hr1a 0 (by simpa using hr1)
    exact h0.comp_of_eq (analyticAt_snoc0 n) (snoc_zero_zero n)
  have hc0 : ∀ j < d, c j 0 = 0 := by
    intro j hj
    show ev (yslice y j r) (Fin.snoc 0 0) = 0
    rw [snoc_zero_zero, ev_zero_pt, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      coeff_yslice]
    simp [hr0 j hj]
  have hcx : ∀ j (x : Fin (n + 1) → ℝ), ev (yslice y j r) x = c j (Fin.init x) := by
    intro j x
    show _ = ev (yslice y j r) (Fin.snoc (Fin.init x) 0)
    have e1 : Function.update (Fin.snoc (Fin.init x) (0 : ℝ) : Fin (n + 1) → ℝ) (Fin.last n)
        (x (Fin.last n)) = x := by
      rw [Fin.update_snoc_last (α := fun _ => ℝ), Fin.snoc_init_self (α := fun _ => ℝ)]
    conv_lhs => rw [← e1]
    exact ev_yslice_update y j r _ _
  let b : Fin d → An n := fun i => ⟨fun x' => -c i x', (hcA i).neg⟩
  set P : (An n)[X] := mkMon d b with hP
  obtain ⟨r1, hr1, hr1a⟩ := analyticAt_ev_zero hw hq
  obtain ⟨wm, hwm, hwmle⟩ := exists_pos_le_all w hw
  have hq0 : ev q 0 ≠ 0 := (hmain 0 (fun i => by simpa using hw' i)).1
  refine ⟨min wm r1, lt_min hwm hr1, P, mkMon_monic d b, ?_, SignType.sign (ev q 0), ?_⟩
  · intro i hi
    rw [hP, mkMon_natDegree] at hi
    rw [hP, mkMon_coeff d b hi]
    show -c i 0 = 0
    rw [hc0 i hi, neg_zero]
  · have hbd : ∀ z : Fin (n + 1) → ℝ, ‖z‖ < min wm r1 → ∀ i, |z i| ≤ w i := fun z hz i => by
      have := norm_le_pi_norm z i
      rw [Real.norm_eq_abs] at this
      exact this.trans (hz.le.trans ((min_le_left _ _).trans (hwmle i)))
    intro x hx
    obtain ⟨hqx, hmx⟩ := hmain x (hbd x hx)
    have hgx : g x = ev a x := by
      have hn : ‖x‖ ≤ ρ0 := hx.le.trans ((min_le_left _ _).trans ((hwmle y).trans (hwle y)))
      simpa using heq x hn
    have hrx : ev r x = ∑ j ∈ Finset.range d, x y ^ j * ev (yslice y j r) x :=
      ev_eq_sum_yslice y d hw' (hw y) hr hhat (hbd x hx)
    have hPx : (pe P (Fin.init x)).eval (x y) = ev q x * g x := by
      rw [hP, eval_pe_mkMon, hgx]
      have hs : ∑ i : Fin d, ((b i : An n) : (Fin n → ℝ) → ℝ) (Fin.init x) * x y ^ (i : ℕ)
          = - ev r x := by
        rw [hrx, ← Finset.sum_neg_distrib,
          ← Fin.sum_univ_eq_sum_range (fun j => -(x y ^ j * ev (yslice y j r) x)) d]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hcx]
        show -c i (Fin.init x) * _ = _
        ring
      rw [hs]
      linarith
    have hsq : SignType.sign (ev q x) = SignType.sign (ev q 0) := by
      refine sign_const_ball (ρ := min wm r1) ?_ ?_ ?_
      · intro z hz
        rw [Metric.mem_ball, dist_zero_right] at hz
        exact (hr1a z (hz.trans_le (min_le_right _ _))).continuousAt.continuousWithinAt
      · intro z hz
        rw [Metric.mem_ball, dist_zero_right] at hz
        exact (hmain z (hbd z hz)).1
      · rw [Metric.mem_ball, dist_zero_right]; exact hx
    refine sign_mul_cancel (sign_ne_zero.2 hq0) ?_
    rw [hPx, sign_mul, hsq]

/-- swap of two coordinates as a continuous linear equivalence. -/
noncomputable def coordSwap {m : ℕ} (k l : Fin m) : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv (LinearEquiv.funCongrLeft ℝ ℝ (Equiv.swap k l))

lemma coordSwap_single {m : ℕ} (k l : Fin m) (t : ℝ) :
    coordSwap k l (Pi.single l t) = Pi.single k t := by
  funext i
  show (Pi.single l t : Fin m → ℝ) (Equiv.swap k l i) = _
  simp only [Pi.single_apply, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]

/-- **CS-6c: local polynomial normal form of finitely many analytic germs.** -/
theorem local_form {n K : ℕ} (h : Fin K → (Fin (n + 1) → ℝ) → ℝ) (hh : ∀ k, AnalyticAt ℝ (h k) 0) :
    ∃ L : (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ), ∃ ρ > 0, ∃ P : Fin K → (An n)[X],
      (∀ k, (P k).Monic ∧
        ∀ i < (P k).natDegree, (((P k).coeff i : An n) : (Fin n → ℝ) → ℝ) 0 = 0) ∧
      ∃ ε : Fin K → SignType, ∀ k, ∀ x : Fin (n + 1) → ℝ, ‖x‖ < ρ →
        SignType.sign (h k (L x)) =
          ε k * SignType.sign ((pe (P k) (Fin.init x)).eval (x (Fin.last n))) := by
  classical
  let s : Finset (Fin K) :=
    Finset.univ.filter (fun k => ¬ ∀ᶠ x in 𝓝 (0 : Fin (n + 1) → ℝ), h k x = 0)
  obtain ⟨hHa, hHn⟩ := nonflat_prod s (f := h) (x₀ := 0) (fun k _ => hh k)
    (fun k hk => (Finset.mem_filter.1 hk).2)
  obtain ⟨k0, L0, hL0⟩ := exists_regular_coord hHa hHn
  let L := (coordSwap k0 (Fin.last n)).trans L0
  have hLs : ∀ t, L (Pi.single (Fin.last n) t) = L0 (Pi.single k0 t) := fun t => by
    show L0 (coordSwap k0 (Fin.last n) _) = _
    rw [coordSwap_single]
  have hper : ∀ k, ∃ ρ > 0, ∃ P : (An n)[X],
      (P.Monic ∧ ∀ i < P.natDegree, ((P.coeff i : An n) : (Fin n → ℝ) → ℝ) 0 = 0) ∧
      ∃ ε : SignType, ∀ x : Fin (n + 1) → ℝ, ‖x‖ < ρ →
        SignType.sign (h k (L x)) = ε * SignType.sign ((pe P (Fin.init x)).eval (x (Fin.last n))) := by
    intro k
    have hgA : AnalyticAt ℝ (fun x => h k (L x)) 0 :=
      (hh k).comp_of_eq ((L : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)).analyticAt 0)
        (by simp)
    by_cases hk : k ∈ s
    · have hax : ¬ ∀ᶠ t in 𝓝 (0 : ℝ), h k (L (Pi.single (Fin.last n) t)) = 0 := by
        intro hev
        apply hL0
        filter_upwards [hev] with t ht
        rw [← hLs]
        exact Finset.prod_eq_zero hk ht
      obtain ⟨ρ, hρ, P, hPm, hPc, ε, hε⟩ := local_form_one hgA hax
      exact ⟨ρ, hρ, P, ⟨hPm, hPc⟩, ε, hε⟩
    · have hflat : ∀ᶠ x in 𝓝 (0 : Fin (n + 1) → ℝ), h k x = 0 := by
        by_contra hc
        exact hk (Finset.mem_filter.2 ⟨Finset.mem_univ _, hc⟩)
      have hflat' : ∀ᶠ x in 𝓝 (0 : Fin (n + 1) → ℝ), h k (L x) = 0 := by
        have ht : Tendsto L (𝓝 0) (𝓝 0) := by
          have := L.continuous.tendsto 0
          rwa [map_zero] at this
        exact ht.eventually hflat
      obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1 hflat'
      refine ⟨ρ, hρ, 1, ⟨monic_one, fun i hi => by simp at hi⟩, 0, fun x hx => ?_⟩
      rw [hball (by rw [dist_zero_right]; exact hx)]
      simp
  choose ρ hρ P hP ε hε using hper
  obtain ⟨r, hr, hrle⟩ := exists_pos_le_all ρ hρ
  exact ⟨L, r, hr, P, hP, ε, fun k x hx => hε k x (lt_of_lt_of_le hx (hrle k))⟩

end Form

end SubanalyticLib


/-! SubanalyticLib CS-6d/6e (body; after L5p_Pui (or L5S) + L6S + L6_An.body): curve selection for
`IsSA (An n)` germs at `0`, by induction on `n`, from three inputs stated as Props
(local polynomial form `LFStmt` = CS-6c `local_form`, one-variable Tarski–Seidenberg `TSStmt` = `ts_any`,
real Puiseux `PuiStmt` = `Pui.puiseux`). Lift along an arc: candidates = Puiseux branches, their
midpoints, branch ± v, and 0; each candidate's sign code is eventually constant. -/

namespace SubanalyticLib

section Lift

open Filter Topology Set Polynomial

set_option autoImplicit false

/-- curve selection at `0` for sets in the Boolean algebra of germs analytic at `0`. -/
def CSg (n : ℕ) : Prop := ∀ S : Set (Fin n → ℝ), IsSA (An n) S → (0 : Fin n → ℝ) ∈ closure S →
  ∃ γ : ℝ → (Fin n → ℝ), AnalyticAt ℝ γ 0 ∧ γ 0 = 0 ∧ ∃ ε > 0, ∀ u ∈ Ioo (0 : ℝ) ε, γ u ∈ S

/-- local polynomial normal form (proved as `local_form`). -/
def LFStmt (n : ℕ) : Prop := ∀ (K : ℕ) (h : Fin K → (Fin (n + 1) → ℝ) → ℝ), (∀ k, AnalyticAt ℝ (h k) 0) →
    ∃ L : (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ), ∃ ρ > 0, ∃ P : Fin K → (An n)[X],
      (∀ k, (P k).Monic ∧
        ∀ i < (P k).natDegree, (((P k).coeff i : An n) : (Fin n → ℝ) → ℝ) 0 = 0) ∧
      ∃ ε : Fin K → SignType, ∀ k, ∀ x : Fin (n + 1) → ℝ, ‖x‖ < ρ →
        SignType.sign (h k (L x)) =
          ε k * SignType.sign ((pe (P k) (Fin.init x)).eval (x (Fin.last n)))

/-- parametric one-variable Tarski–Seidenberg (proved as `ts_any`). -/
def TSStmt (n : ℕ) : Prop := ∀ (K : ℕ) (P : Fin K → (An n)[X]) (μ : Fin K → SignType),
  IsSA (An n) {x' | ∃ y : ℝ, ∀ i, SignType.sign ((pe (P i) x').eval y) = μ i}

/-- real Newton–Puiseux (proved as `Pui.puiseux`). -/
def PuiStmt : Prop := ∀ P : Pui.Ran[X], P.Monic → ∃ q, 0 < q ∧ Pui.BranchesAt P q

/-- a continuous function without zeros on a preconnected set has constant sign there. -/
lemma sign_eq_on_preconnected {E : Type*} [TopologicalSpace E] {f : E → ℝ} {s : Set E}
    (hs : IsPreconnected s) (hc : ContinuousOn f s) (hne : ∀ x ∈ s, f x ≠ 0)
    {x x' : E} (hx : x ∈ s) (hx' : x' ∈ s) : SignType.sign (f x) = SignType.sign (f x') := by
  have h1 := hne x hx
  have h2 := hne x' hx'
  rcases lt_or_gt_of_ne h1 with ha | ha <;> rcases lt_or_gt_of_ne h2 with hb | hb
  · rw [sign_neg ha, sign_neg hb]
  · exfalso
    obtain ⟨z, hz, hz0⟩ := hs.intermediate_value hx hx' hc ⟨ha.le, hb.le⟩
    exact hne z hz hz0
  · exfalso
    obtain ⟨z, hz, hz0⟩ := hs.intermediate_value hx' hx hc ⟨hb.le, ha.le⟩
    exact hne z hz hz0
  · rw [sign_pos ha, sign_pos hb]

/-- no root on the segment: same sign at both ends. -/
lemma sign_eq_of_no_root {p : ℝ[X]} {y y' : ℝ} (h : ∀ z ∈ uIcc y y', ¬ p.IsRoot z) :
    SignType.sign (p.eval y) = SignType.sign (p.eval y') :=
  sign_eq_on_preconnected isPreconnected_uIcc p.continuous.continuousOn
    (fun z hz => h z hz) left_mem_uIcc right_mem_uIcc

/-- **Candidates.** If every root of every `p i` lies in the finite set `Z`, every sign code
realized by some `y` is realized by `0`, a point of `Z`, `a ± t` or a midpoint of two points of `Z`. -/
lemma exists_cand {ι : Type*} (p : ι → ℝ[X]) (Z : Finset ℝ)
    (hZ : ∀ i z, (p i).IsRoot z → z ∈ Z) {t : ℝ} (ht : 0 < t) (y : ℝ) :
    ∃ y', (y' = 0 ∨ y' ∈ Z ∨ (∃ a ∈ Z, y' = a + t ∨ y' = a - t) ∨
        ∃ a ∈ Z, ∃ b ∈ Z, y' = (a + b) / 2) ∧
      ∀ i, SignType.sign ((p i).eval y') = SignType.sign ((p i).eval y) := by
  classical
  by_cases hyZ : y ∈ Z
  · exact ⟨y, Or.inr (Or.inl hyZ), fun i => rfl⟩
  -- a segment avoiding `Z` carries no root
  have key : ∀ y' : ℝ, (∀ z ∈ uIcc y' y, z ∉ Z) →
      ∀ i, SignType.sign ((p i).eval y') = SignType.sign ((p i).eval y) :=
    fun y' hseg i => sign_eq_of_no_root fun z hz hr => hseg z hz (hZ i z hr)
  rcases Z.eq_empty_or_nonempty with hZe | hne
  · refine ⟨0, Or.inl rfl, key 0 fun z _ => by simp [hZe]⟩
  set m := Z.max' hne
  set l := Z.min' hne
  by_cases hm : m < y
  · refine ⟨m + t, Or.inr (Or.inr (Or.inl ⟨m, Z.max'_mem hne, Or.inl rfl⟩)), key _ fun z hz hzZ => ?_⟩
    have h1 : z ≤ m := Z.le_max' z hzZ
    have h2 := (mem_uIcc.1 hz)
    rcases h2 with ⟨h3, _⟩ | ⟨h3, _⟩ <;> linarith
  by_cases hl : y < l
  · refine ⟨l - t, Or.inr (Or.inr (Or.inl ⟨l, Z.min'_mem hne, Or.inr rfl⟩)), key _ fun z hz hzZ => ?_⟩
    have h1 : l ≤ z := Z.min'_le z hzZ
    have h2 := (mem_uIcc.1 hz)
    rcases h2 with ⟨_, h3⟩ | ⟨_, h3⟩ <;> linarith
  push_neg at hm hl
  have hmy : y < m := lt_of_le_of_ne hm fun h => hyZ (h ▸ Z.max'_mem hne)
  have hly : l < y := lt_of_le_of_ne hl fun h => hyZ (h.symm ▸ Z.min'_mem hne)
  have hA : (Z.filter (· < y)).Nonempty := ⟨l, Finset.mem_filter.2 ⟨Z.min'_mem hne, hly⟩⟩
  have hB : (Z.filter (y < ·)).Nonempty := ⟨m, Finset.mem_filter.2 ⟨Z.max'_mem hne, hmy⟩⟩
  set a := (Z.filter (· < y)).max' hA
  set b := (Z.filter (y < ·)).min' hB
  have haZ : a ∈ Z ∧ a < y := Finset.mem_filter.1 ((Z.filter (· < y)).max'_mem hA)
  have hbZ : b ∈ Z ∧ y < b := Finset.mem_filter.1 ((Z.filter (y < ·)).min'_mem hB)
  refine ⟨(a + b) / 2, Or.inr (Or.inr (Or.inr ⟨a, haZ.1, b, hbZ.1, rfl⟩)), key _ fun z hz hzZ => ?_⟩
  have hz' : a < z ∧ z < b := by
    rcases mem_uIcc.1 hz with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith [haZ.2, hbZ.2]
  rcases lt_trichotomy z y with hzy | hzy | hzy
  · have : z ≤ a := (Z.filter (· < y)).le_max' z (Finset.mem_filter.2 ⟨hzZ, hzy⟩)
    linarith [hz'.1]
  · exact hyZ (hzy ▸ hzZ)
  · have : b ≤ z := (Z.filter (y < ·)).min'_le z (Finset.mem_filter.2 ⟨hzZ, hzy⟩)
    linarith [hz'.2]

/-- an analytic germ of one variable has eventually constant sign on the right of `0`. -/
lemma eventually_sign_const {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) :
    ∃ s : SignType, ∀ᶠ v in 𝓝[>] (0 : ℝ), SignType.sign (f v) = s := by
  rcases hf.eventually_eq_zero_or_eventually_ne_zero with h | h
  · refine ⟨0, ?_⟩
    filter_upwards [nhdsWithin_le_nhds h] with v hv
    rw [hv, sign_zero]
  · have h2 : ∀ᶠ v in 𝓝 (0 : ℝ), AnalyticAt ℝ f v := hf.eventually_analyticAt
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 h2
    obtain ⟨δ', hδ', hball'⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 h)
    set e := min δ δ'
    have he : 0 < e := lt_min hδ hδ'
    have hsub : ∀ v ∈ Ioo (0 : ℝ) e, AnalyticAt ℝ f v ∧ f v ≠ 0 := by
      intro v hv
      have hd : dist v 0 < e := by
        rw [Real.dist_eq, sub_zero, abs_of_pos hv.1]; exact hv.2
      exact ⟨hball (hd.trans_le (min_le_left _ _)),
        hball' (hd.trans_le (min_le_right _ _)) (ne_of_gt hv.1)⟩
    refine ⟨SignType.sign (f (e / 2)), ?_⟩
    filter_upwards [Ioo_mem_nhdsGT he] with v hv
    exact sign_eq_on_preconnected isPreconnected_Ioo
      (fun z hz => (hsub z hz).1.continuousAt.continuousWithinAt)
      (fun z hz => (hsub z hz).2) hv ⟨half_pos he, half_lt_self he⟩

/-- pull back germs along an analytic arc through `0`. -/
def compA {n : ℕ} (α : ℝ → (Fin n → ℝ)) (hα : AnalyticAt ℝ α 0) (h0 : α 0 = 0) :
    An n →+* Pui.Ran where
  toFun f := ⟨fun u => (f : (Fin n → ℝ) → ℝ) (α u),
    (show AnalyticAt ℝ (f : (Fin n → ℝ) → ℝ) 0 from f.2).comp_of_eq hα h0⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

lemma pv_compA {n : ℕ} (α : ℝ → (Fin n → ℝ)) (hα : AnalyticAt ℝ α 0) (h0 : α 0 = 0)
    (P : (An n)[X]) (u : ℝ) : Pui.pv (P.map (compA α hα h0)) u = pe P (α u) := by
  unfold Pui.pv pe
  rw [Polynomial.map_map]
  congr 1

lemma eval_pe_eq_pow {n : ℕ} {P : (An n)[X]} (hP : P.Monic)
    (h0 : ∀ i < P.natDegree, ((P.coeff i : An n) : (Fin n → ℝ) → ℝ) 0 = 0) (y : ℝ) :
    (pe P 0).eval y = y ^ P.natDegree := by
  have hm : (pe P 0).Monic := hP.map _
  have hd : (pe P 0).natDegree = P.natDegree := hP.natDegree_map _
  rw [Pui.eval_monic_eq hm, hd]
  rw [Finset.sum_eq_zero, add_zero]
  intro j hj
  rw [pe_coeff, h0 j (Finset.mem_range.1 hj), zero_mul]

lemma analyticAt_eval_pe {n : ℕ} (P : (An n)[X]) {β : ℝ → (Fin n → ℝ)} (hβ : AnalyticAt ℝ β 0)
    (hβ0 : β 0 = 0) {c : ℝ → ℝ} (hc : AnalyticAt ℝ c 0) :
    AnalyticAt ℝ (fun v => (pe P (β v)).eval (c v)) 0 := by
  have : (fun v => (pe P (β v)).eval (c v)) =
      fun v => ∑ j ∈ Finset.range (P.natDegree + 1),
        ((P.coeff j : An n) : (Fin n → ℝ) → ℝ) (β v) * c v ^ j := by
    funext v
    rw [eval_eq_sum_range' (n := P.natDegree + 1)]
    · simp only [pe_coeff]
    · have : (pe P (β v)).natDegree ≤ P.natDegree := natDegree_map_le
      omega
  rw [this]
  have hs := Finset.analyticAt_sum (𝕜 := ℝ) (c := (0 : ℝ)) (Finset.range (P.natDegree + 1))
    (f := fun j v => ((P.coeff j : An n) : (Fin n → ℝ) → ℝ) (β v) * c v ^ j) (fun j _ =>
      ((show AnalyticAt ℝ ((P.coeff j : An n) : (Fin n → ℝ) → ℝ) 0 from (P.coeff j).2).comp_of_eq
        hβ hβ0).mul (hc.pow j))
  convert hs using 1
  funext v
  rw [Finset.sum_apply]

/-- **Lifting an arc of the base to the graph-cylinder** (CS-6e). -/
theorem lift_arc {n K : ℕ} (P : Fin K → (An n)[X]) (hPm : ∀ k, (P k).Monic)
    (hP0 : ∀ k, ∀ i < (P k).natDegree, (((P k).coeff i : An n) : (Fin n → ℝ) → ℝ) 0 = 0)
    (hPui : PuiStmt) (μ : Fin K → SignType)
    (α : ℝ → (Fin n → ℝ)) (hα : AnalyticAt ℝ α 0) (h0 : α 0 = 0) {ε1 : ℝ} (hε1 : 0 < ε1)
    (hB : ∀ u ∈ Ioo (0 : ℝ) ε1, ∃ y : ℝ, ∀ i, SignType.sign ((pe (P i) (α u)).eval y) = μ i) :
    ∃ q : ℕ, 0 < q ∧ ∃ c : ℝ → ℝ, AnalyticAt ℝ c 0 ∧ c 0 = 0 ∧
      ∀ᶠ v in 𝓝[>] (0 : ℝ), ∀ i, SignType.sign ((pe (P i) (α (v ^ q))).eval (c v)) = μ i := by
  classical
  set φA := compA α hα h0
  set QQ : Pui.Ran[X] := ∏ i, (P i).map φA with hQQ
  have hQm : QQ.Monic := monic_prod_of_monic _ _ fun i _ => (hPm i).map _
  have hQe : ∀ u y, (Pui.pv QQ u).eval y = ∏ i, (pe (P i) (α u)).eval y := by
    intro u y
    rw [hQQ, Pui.pv, Polynomial.map_prod, eval_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    exact congrArg (Polynomial.eval y) (pv_compA α hα h0 (P i) u)
  obtain ⟨q, hq, Φ, hΦf, hΦa, hΦr⟩ := hPui QQ hQm
  have hroot0 : ∀ c, (Pui.pv QQ 0).IsRoot c → c = 0 := by
    intro c hc
    rw [IsRoot.def, hQe, h0] at hc
    obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.1 hc
    rw [eval_pe_eq_pow (hPm i) (hP0 i)] at hi
    by_contra hne
    exact pow_ne_zero _ hne hi
  have hpow : Tendsto (fun v : ℝ => v ^ q) (𝓝[>] 0) (𝓝[>] 0) := Pui.tendsto_pow_nhdsGT hq
  have hpow' : Tendsto (fun v : ℝ => v ^ q) (𝓝[>] 0) (𝓝 0) := hpow.mono_right nhdsWithin_le_nhds
  have hΦ0 : ∀ φ ∈ Φ, φ 0 = 0 := by
    intro φ hφ
    have ht : Tendsto φ (𝓝[>] 0) (𝓝 0) := by
      rw [Metric.tendsto_nhds]
      intro δ hδ
      have h1 := hpow'.eventually (Pui.roots_near hQm hδ)
      filter_upwards [h1, hΦr] with v hv1 hv2
      obtain ⟨c, hc, hcd⟩ := hv1 (φ v) ((hv2 (φ v)).2 ⟨φ, hφ, rfl⟩)
      rw [hroot0 c hc, sub_zero] at hcd
      rwa [Real.dist_eq, sub_zero]
    have ht' : Tendsto φ (𝓝[>] 0) (𝓝 (φ 0)) :=
      (hΦa φ hφ).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact tendsto_nhds_unique ht' ht
  set C : Set (ℝ → ℝ) := (((({fun _ => (0 : ℝ)} ∪ Φ) ∪ (fun φ => fun v => φ v + v) '' Φ) ∪
    (fun φ => fun v => φ v - v) '' Φ) ∪ Set.image2 (fun φ ψ => fun v => (φ v + ψ v) / 2) Φ Φ) with hC
  have hCf : C.Finite :=
    ((((Set.finite_singleton _).union hΦf).union (hΦf.image _)).union (hΦf.image _)).union
      (hΦf.image2 _ hΦf)
  have hCa : ∀ c ∈ C, AnalyticAt ℝ c 0 ∧ c 0 = 0 := by
    intro c hc
    rcases hc with (((hc | hc) | ⟨φ, hφ, rfl⟩) | ⟨φ, hφ, rfl⟩) | ⟨φ, hφ, ψ, hψ, rfl⟩
    · rw [Set.mem_singleton_iff] at hc
      subst hc
      exact ⟨analyticAt_const, rfl⟩
    · exact ⟨hΦa c hc, hΦ0 c hc⟩
    · exact ⟨(hΦa φ hφ).add analyticAt_id, by simp [hΦ0 φ hφ]⟩
    · exact ⟨(hΦa φ hφ).sub analyticAt_id, by simp [hΦ0 φ hφ]⟩
    · exact ⟨((hΦa φ hφ).add (hΦa ψ hψ)).div analyticAt_const (by norm_num),
        by simp [hΦ0 φ hφ, hΦ0 ψ hψ]⟩
  have hαq : AnalyticAt ℝ (fun v => α (v ^ q)) 0 :=
    hα.comp_of_eq ((analyticAt_id).pow q) (by simp [hq.ne'])
  have hαq0 : α (0 ^ q) = 0 := by rw [zero_pow hq.ne', h0]
  have hcode : ∀ c ∈ C, ∃ s : Fin K → SignType, ∀ᶠ v in 𝓝[>] (0 : ℝ),
      ∀ i, SignType.sign ((pe (P i) (α (v ^ q))).eval (c v)) = s i := by
    intro c hc
    have hi : ∀ i, ∃ s : SignType, ∀ᶠ v in 𝓝[>] (0 : ℝ),
        SignType.sign ((pe (P i) (α (v ^ q))).eval (c v)) = s := fun i =>
      eventually_sign_const (analyticAt_eval_pe (P i) hαq hαq0 (hCa c hc).1)
    choose s hs using hi
    exact ⟨s, Filter.eventually_all.2 hs⟩
  choose! s hs using hcode
  have hex : ∃ c ∈ C, s c = μ := by
    by_contra hne
    push_neg at hne
    have hall : ∀ᶠ v in 𝓝[>] (0 : ℝ), ∀ c ∈ C, ∀ i,
        SignType.sign ((pe (P i) (α (v ^ q))).eval (c v)) = s c i :=
      (Filter.eventually_all_finite hCf).2 hs
    have hev := (hall.and (hΦr.and (hpow.eventually (Ioo_mem_nhdsGT hε1)))).and
      (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))
    obtain ⟨v, ⟨hv1, hv2, hv3⟩, hv4⟩ := hev.exists
    obtain ⟨y, hy⟩ := hB (v ^ q) hv3
    set Z : Finset ℝ := hΦf.toFinset.image (fun φ => φ v)
    have hZ : ∀ i z, (pe (P i) (α (v ^ q))).IsRoot z → z ∈ Z := by
      intro i z hz
      have hz' : (Pui.pv QQ (v ^ q)).IsRoot z := by
        rw [IsRoot.def, hQe]
        exact Finset.prod_eq_zero (Finset.mem_univ i) hz
      obtain ⟨φ, hφ, rfl⟩ := (hv2 z).1 hz'
      exact Finset.mem_image.2 ⟨φ, hΦf.mem_toFinset.2 hφ, rfl⟩
    obtain ⟨y', hy'C, hy'⟩ := exists_cand (fun i => pe (P i) (α (v ^ q))) Z hZ hv4 y
    have hcv : ∃ c ∈ C, c v = y' := by
      rcases hy'C with h | h | ⟨a, ha, h | h⟩ | ⟨a, ha, b, hb, h⟩
      · exact ⟨fun _ => 0, Or.inl (Or.inl (Or.inl (Or.inl rfl))), h.symm⟩
      · obtain ⟨φ, hφ, rfl⟩ := Finset.mem_image.1 h
        exact ⟨φ, Or.inl (Or.inl (Or.inl (Or.inr (hΦf.mem_toFinset.1 hφ)))), rfl⟩
      · obtain ⟨φ, hφ, rfl⟩ := Finset.mem_image.1 ha
        exact ⟨_, Or.inl (Or.inl (Or.inr ⟨φ, hΦf.mem_toFinset.1 hφ, rfl⟩)), h.symm⟩
      · obtain ⟨φ, hφ, rfl⟩ := Finset.mem_image.1 ha
        exact ⟨_, Or.inl (Or.inr ⟨φ, hΦf.mem_toFinset.1 hφ, rfl⟩), h.symm⟩
      · obtain ⟨φ, hφ, rfl⟩ := Finset.mem_image.1 ha
        obtain ⟨ψ, hψ, rfl⟩ := Finset.mem_image.1 hb
        exact ⟨_, Or.inr ⟨φ, hΦf.mem_toFinset.1 hφ, ψ, hΦf.mem_toFinset.1 hψ, rfl⟩, h.symm⟩
    obtain ⟨c, hcC, hcy⟩ := hcv
    apply hne c hcC
    funext i
    rw [← hv1 c hcC i, hcy, hy' i, hy i]
  obtain ⟨c, hcC, hcμ⟩ := hex
  refine ⟨q, hq, c, (hCa c hcC).1, (hCa c hcC).2, ?_⟩
  filter_upwards [hs c hcC] with v hv i
  rw [hv i, hcμ]

lemma norm_init_le {n : ℕ} (x : Fin (n + 1) → ℝ) : ‖(Fin.init x : Fin n → ℝ)‖ ≤ ‖x‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 fun j => norm_le_pi_norm x _

lemma analyticAt_snoc {n : ℕ} {a : ℝ → (Fin n → ℝ)} {c : ℝ → ℝ} (ha : AnalyticAt ℝ a 0)
    (hc : AnalyticAt ℝ c 0) :
    AnalyticAt ℝ (fun v => (Fin.snoc (a v) (c v) : Fin (n + 1) → ℝ)) 0 := by
  refine analyticAt_pi_iff.2 fun i => ?_
  induction i using Fin.lastCases with
  | last => simpa using hc
  | cast j => simpa using analyticAt_pi_iff.1 ha j

/-- **CS-6 induction step.** -/
theorem cs_step {n : ℕ} (hLF : LFStmt n) (hTS : TSStmt n) (hPui : PuiStmt) (ih : CSg n) :
    CSg (n + 1) := by
  classical
  intro S hS hS0
  obtain ⟨K, h, hhR, N, rfl⟩ := hS.codeForm
  obtain ⟨L, ρ, hρ, P, hP, ε, hε⟩ := hLF K h (fun k => mem_An.1 (hhR k))
  set D : (Fin K → SignType) → Set (Fin n → ℝ) := fun μ =>
    {x' | (fun i => ε i * μ i) ∈ N ∧ ∃ y : ℝ, ∀ i, SignType.sign ((pe (P i) x').eval y) = μ i}
    with hD
  have hDSA : ∀ μ, IsSA (An n) (D μ) := by
    intro μ
    by_cases hμ : (fun i => ε i * μ i) ∈ N
    · have e : D μ = {x' | ∃ y : ℝ, ∀ i, SignType.sign ((pe (P i) x').eval y) = μ i} := by
        ext x'
        simp only [hD, Set.mem_setOf_eq]
        exact and_iff_right hμ
      rw [e]
      exact hTS K P μ
    · have e : D μ = ∅ := by
        ext x'
        simp only [hD, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hμ h.1
      rw [e]
      exact IsSA.empty
  have hcl : (0 : Fin n → ℝ) ∈ closure (⋃ μ, D μ) := by
    rw [Metric.mem_closure_iff]
    intro δ hδ
    have hLc : Tendsto L.symm (𝓝 0) (𝓝 0) := by
      have := L.symm.continuous.tendsto 0
      rwa [map_zero] at this
    have hev := hLc.eventually (Metric.ball_mem_nhds (0 : Fin (n + 1) → ℝ) (lt_min hδ hρ))
    obtain ⟨η, hη, hηb⟩ := Metric.eventually_nhds_iff.1 hev
    obtain ⟨s, hsS, hsd⟩ := Metric.mem_closure_iff.1 hS0 η hη
    have hx := hηb (by rwa [dist_comm] at hsd)
    rw [dist_zero_right] at hx
    set x := L.symm s with hxdef
    have hLx : L x = s := L.apply_symm_apply s
    refine ⟨Fin.init x, Set.mem_iUnion.2 ⟨fun i =>
      SignType.sign ((pe (P i) (Fin.init x)).eval (x (Fin.last n))), ?_, x (Fin.last n),
      fun i => rfl⟩, ?_⟩
    · have e : (fun i => ε i * SignType.sign ((pe (P i) (Fin.init x)).eval (x (Fin.last n)))) =
          fun i => SignType.sign (h i s) := by
        funext i
        rw [← hLx, hε i x (hx.trans_le (min_le_right _ _))]
      rw [e]
      exact hsS
    · rw [dist_zero_left]
      exact (norm_init_le x).trans_lt (hx.trans_le (min_le_left _ _))
  rw [closure_iUnion_of_finite] at hcl
  obtain ⟨μ, hμ⟩ := Set.mem_iUnion.1 hcl
  obtain ⟨α, hα, hα0, ε1, hε1, hαD⟩ := ih (D μ) (hDSA μ) hμ
  have hμN : (fun i => ε i * μ i) ∈ N := (hαD (ε1 / 2) ⟨half_pos hε1, half_lt_self hε1⟩).1
  obtain ⟨q, hq, c, hc, hc0, hev⟩ := lift_arc P (fun k => (hP k).1) (fun k => (hP k).2) hPui μ
    α hα hα0 hε1 (fun u hu => (hαD u hu).2)
  set β : ℝ → (Fin (n + 1) → ℝ) := fun v => Fin.snoc (α (v ^ q)) (c v) with hβ
  have hαq : AnalyticAt ℝ (fun v => α (v ^ q)) 0 :=
    hα.comp_of_eq ((analyticAt_id).pow q) (by simp [hq.ne'])
  have hβa : AnalyticAt ℝ β 0 := analyticAt_snoc hαq hc
  have hβ0 : β 0 = 0 := by
    simp only [hβ, zero_pow hq.ne', hα0, hc0]
    exact snoc_zero_zero n
  have hβn : ∀ᶠ v in 𝓝 (0 : ℝ), ‖β v‖ < ρ := by
    have ht := hβa.continuousAt.tendsto
    rw [hβ0] at ht
    exact (ht.eventually (Metric.ball_mem_nhds 0 hρ)).mono fun v hv => mem_ball_zero_iff.1 hv
  have hall := (Filter.Eventually.filter_mono nhdsWithin_le_nhds hβn).and hev
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hall
  refine ⟨fun v => L (β v), ((L : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)).analyticAt _).comp hβa,
    by simp [hβ0], δ, hδ, fun v hv => ?_⟩
  obtain ⟨hvn, hvc⟩ := hsub hv
  show (fun i => SignType.sign (h i (L (β v)))) ∈ N
  have e : (fun i => SignType.sign (h i (L (β v)))) = fun i => ε i * μ i := by
    funext i
    rw [hε i (β v) hvn]
    simp only [hβ, Fin.init_snoc, Fin.snoc_last]
    rw [hvc i]
  rw [e]
  exact hμN

theorem csg_zero : CSg 0 := by
  intro S _ hS0
  have hne : S.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, closure_empty] at hS0
    exact hS0
  obtain ⟨s, hs⟩ := hne
  have hs0 : s = 0 := Subsingleton.elim _ _
  refine ⟨fun _ => 0, analyticAt_const, rfl, 1, one_pos, fun u _ => ?_⟩
  rw [← hs0]
  exact hs

/-- **CS (germ form): curve selection for every `n`**, from the three inputs. -/
theorem csg_all (hLF : ∀ n, LFStmt n) (hTS : ∀ n, TSStmt n) (hPui : PuiStmt) : ∀ n, CSg n
  | 0 => csg_zero
  | n + 1 => cs_step (hLF n) (hTS n) hPui (csg_all hLF hTS hPui n)

end Lift

end SubanalyticLib


/-! SubanalyticLib CS-6f (body; last): the three inputs of `csg_all` discharged by `local_form`,
`ts_any`, `Pui.puiseux`: curve selection for `IsSA (An n)` sets at `0`, every `n`. -/

namespace SubanalyticLib

section CSfinal

open Filter Topology Set Polynomial

theorem lfStmt (n : ℕ) : LFStmt n := fun _ h hh => local_form h hh

theorem tsStmt (n : ℕ) : TSStmt n := by
  intro K P μ
  have e : {x' : Fin n → ℝ | ∃ y : ℝ, ∀ i, SignType.sign ((pe (P i) x').eval y) = μ i} =
      Rlz (A := Fin n → ℝ) (R := An n) Finset.univ P μ := by
    ext x'
    simp [Rlz, iSign, Set.Nonempty]
  rw [e]
  exact ts_any Finset.univ P μ

theorem puiStmt : PuiStmt := fun P hP => Pui.puiseux P hP

/-- **CS-6: curve selection at `0` for sets in the Boolean algebra of analytic germs, every `n`.** -/
theorem csg (n : ℕ) : CSg n := csg_all lfStmt tsStmt puiStmt n

end CSfinal

end SubanalyticLib


/-! SubanalyticLib CS-7 (body; after L6a_C1arc (imports) + L6F): curve selection for semianalytic sets
(`SemiCurveSelection Y`, every finite-dimensional `Y`) from the germ form `csg`, and hence
`CurveSelection X` and item C1 (`c1_growth`). -/

namespace SubanalyticLib

section Semi7

open Filter Topology Set

set_option autoImplicit false

/-- **Curve selection for semianalytic sets** (boundedness not needed). -/
theorem semiCurveSelection (Y : Type*) [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [FiniteDimensional ℝ Y] : SemiCurveSelection Y := by
  classical
  intro B hB _ y₀ hy₀
  obtain ⟨V, hVo, hy₀V, p, q, F, G, hFG, hEq⟩ := hB y₀
  set n := Module.finrank ℝ Y
  let e : Y ≃L[ℝ] (Fin n → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp [n])
  set T : (Fin n → ℝ) → Y := fun x => y₀ + e.symm x with hT
  have hTa : ∀ x, AnalyticAt ℝ T x := fun x =>
    analyticAt_const.add ((e.symm : (Fin n → ℝ) →L[ℝ] Y).analyticAt x)
  have hT0 : T 0 = y₀ := by simp [hT]
  have hTc : Continuous T := continuous_const.add e.symm.continuous
  set S : Set (Fin n → ℝ) :=
    ⋃ i : Fin p, ⋂ j : Fin q, ({x | F i j (T x) = 0} ∩ {x | 0 < G i j (T x)}) with hS
  have hSA : IsSA (An n) S := by
    refine IsSA.iUnion_fintype fun i => IsSA.iInter_fintype fun j => IsSA.inter ?_ ?_
    · exact IsSA.zero (mem_An.2 (((hFG i j).1 y₀ hy₀V).comp_of_eq (hTa 0) hT0))
    · exact IsSA.pos (mem_An.2 (((hFG i j).2 y₀ hy₀V).comp_of_eq (hTa 0) hT0))
  have hmemS : ∀ x, T x ∈ B ∩ V → x ∈ S := by
    intro x hx
    rw [hEq] at hx
    obtain ⟨-, hx2⟩ := hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx2
    exact Set.mem_iUnion.2 ⟨i, Set.mem_iInter.2 fun j => (Set.mem_iInter.1 hi j)⟩
  have hcl : (0 : Fin n → ℝ) ∈ closure S := by
    rw [mem_closure_iff_nhds]
    intro t ht
    -- T maps a neighbourhood of 0 onto a neighbourhood of y₀
    have hmap : T '' t ∈ 𝓝 y₀ := by
      have hom : IsOpenMap T := ((e.symm.toHomeomorph).trans (Homeomorph.addLeft y₀)).isOpenMap
      rw [← hT0]
      exact hom.image_mem_nhds ht
    obtain ⟨z, hz⟩ := mem_closure_iff_nhds.1 hy₀ _ (Filter.inter_mem hmap (hVo.mem_nhds hy₀V))
    obtain ⟨⟨⟨x, hxt, rfl⟩, hzV⟩, hzB⟩ := hz
    exact ⟨x, hxt, hmemS x ⟨hzB, hzV⟩⟩
  obtain ⟨γ, hγ, hγ0, ε, hε, hγS⟩ := csg n S hSA hcl
  have hTγ : ∀ᶠ u in 𝓝 (0 : ℝ), T (γ u) ∈ V := by
    have ht : Tendsto (fun u => T (γ u)) (𝓝 0) (𝓝 y₀) := by
      have := (hTc.tendsto _).comp hγ.continuousAt.tendsto
      rwa [Function.comp_def, hγ0, hT0] at this
    exact ht.eventually (hVo.mem_nhds hy₀V)
  obtain ⟨δ, hδ, hδV⟩ := Metric.eventually_nhds_iff.1 hTγ
  refine ⟨fun u => T (γ u), (hTa (γ 0)).comp hγ, by simp [hγ0, hT0], min ε δ, lt_min hε hδ,
    fun u hu => ?_⟩
  have huV : T (γ u) ∈ V := hδV (by
    rw [Real.dist_eq, sub_zero, abs_of_pos hu.1]; exact hu.2.trans_le (min_le_right _ _))
  have huS := hγS u ⟨hu.1, hu.2.trans_le (min_le_left _ _)⟩
  have : T (γ u) ∈ B ∩ V := by
    rw [hEq]
    refine ⟨huV, ?_⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 huS
    exact Set.mem_iUnion.2 ⟨i, Set.mem_iInter.2 fun j => (Set.mem_iInter.1 hi j)⟩
  exact this.1

/-- **Curve selection for subanalytic sets.** -/
theorem curveSelection (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] : CurveSelection X :=
  curveSelection_of_semi fun _ => semiCurveSelection _

end Semi7

end SubanalyticLib


open NonsmoothLojasiewicz.Continuous in
theorem solution {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    (A : Set X) (hA : IsSubanalytic A) (x₀ : X) (hx₀ : x₀ ∈ closure A) :
    ∃ γ : ℝ → X, AnalyticAt ℝ γ 0 ∧ γ 0 = x₀ ∧ ∃ ε > 0, ∀ u ∈ Set.Ioo (0 : ℝ) ε, γ u ∈ A := by
  exact SubanalyticLib.curveSelection X A hA x₀ hx₀
