-- Prove2me | solution 1 for KaimanovichVershik.hasNontrivialPoissonBoundary_iff_exists_isShiftInvariant_pathMeasure_pos_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-05T22:13:00.069758+00:00
-- url     : https://prove2.me/submissions/df8c269b-69cd-4688-997b-b0d395e39e81

import Mathlib
import Definitions.Def_ErschlerZheng_Walks

section
/-!
# Path space of a random walk (helpers for B7, B8)

Originally for B7: a shift-invariant event of intermediate probability gives a non-trivial Poisson boundary
(Kaimanovich–Vershik, pp. 9–10)

`F(y) = ℙ_y(A)` is `μ`-harmonic by the Markov property at the first step: under the product
measure, a path is its first increment followed by an independent path (`head_tail`), and
shift-invariance turns `W ∈ A` into `(path from y ξ_0) ∈ A`. If `F` were constant `= c` on the
points reachable from `x`, induction on the rank of a cylinder gives
`ℙ(S ∩ W_x⁻¹A) = c ℙ(S)` for every cylinder `S`; the cylinders generate the product σ-algebra,
so `ℙ(W_x⁻¹A) = c²` and `c ∈ {0, 1}`.
-/

open MeasureTheory

namespace ErschlerZheng

namespace B7Dev

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {Γ : Type*} [Group Γ] [Countable Γ] [MeasurableSpace Γ] [DiscreteMeasurableSpace Γ]

/-- `(z, ξ) ↦ z ξ_0 ξ_1 ⋯`. -/
def consMap (p : Γ × (ℕ → Γ)) : ℕ → Γ := fun n => match n with
  | 0 => p.1
  | n + 1 => p.2 n

theorem measurable_consMap : Measurable (consMap (Γ := Γ)) := by
  apply measurable_pi_lambda
  intro n
  cases n with
  | zero => exact measurable_fst
  | succ n => exact (measurable_pi_apply n).comp measurable_snd

theorem stepMeasure_apply (μ : Γ → ℝ) (s : Set Γ) :
    stepMeasure μ s = ∑' g, ENNReal.ofReal (μ g) * s.indicator 1 g := by
  unfold stepMeasure
  rw [Measure.sum_apply _ (DiscreteMeasurableSpace.forall_measurableSet s)]
  congr 1; funext g
  rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _
    (DiscreteMeasurableSpace.forall_measurableSet s)]

theorem isProbabilityMeasure_stepMeasure {μ : Γ → ℝ} (hμ : IsProbability μ) :
    IsProbabilityMeasure (stepMeasure μ) := by
  constructor
  rw [stepMeasure_apply]
  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg hμ.1 hμ.2.summable, hμ.2.tsum_eq, ENNReal.ofReal_one]

theorem lintegral_stepMeasure (μ : Γ → ℝ) (f : Γ → ENNReal) :
    ∫⁻ z, f z ∂stepMeasure μ = ∑' z, ENNReal.ofReal (μ z) * f z := by
  unfold stepMeasure
  rw [lintegral_sum_measure]
  congr 1; funext z
  rw [lintegral_smul_measure, lintegral_dirac]
  rfl

/-- The product measure is the first coordinate times an independent copy of itself. -/
theorem head_tail {μ : Γ → ℝ} (hμ : IsProbability μ) :
    haveI := isProbabilityMeasure_stepMeasure hμ
    ((stepMeasure μ).prod (Measure.infinitePi fun _ : ℕ => stepMeasure μ)).map consMap =
      Measure.infinitePi fun _ : ℕ => stepMeasure μ := by
  haveI := isProbabilityMeasure_stepMeasure hμ
  set ν := stepMeasure μ
  set P := Measure.infinitePi fun _ : ℕ => ν
  apply Measure.eq_infinitePi
  intro s t ht
  have hpi : MeasurableSet (Set.pi (↑s) t) := MeasurableSet.pi s.countable_toSet fun i _ => ht i
  rw [Measure.map_apply measurable_consMap hpi]
  set T₀ : Set Γ := if 0 ∈ s then t 0 else Set.univ
  set s' : Finset ℕ := s.preimage Nat.succ (Nat.succ_injective.injOn)
  have hset : consMap ⁻¹' Set.pi (↑s) t = T₀ ×ˢ Set.pi (↑s') (fun j => t (j + 1)) := by
    ext ⟨z, ξ⟩
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod, s', Finset.mem_preimage]
    constructor
    · intro h
      refine ⟨?_, fun j hj => h (j + 1) hj⟩
      simp only [T₀]
      split_ifs with h0
      · exact h 0 h0
      · trivial
    · rintro ⟨h0, h1⟩ i hi
      cases i with
      | zero => simp only [T₀, if_pos hi] at h0; exact h0
      | succ j => exact h1 j hi
  rw [hset, Measure.prod_prod, Measure.infinitePi_pi _ (fun i _ => ht (i + 1))]
  -- the product over `s` splits at `0`
  have hsplit : ∏ i ∈ s, ν (t i) =
      (∏ i ∈ s, if i = 0 then ν (t 0) else 1) * ∏ i ∈ s, if i = 0 then 1 else ν (t i) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    split_ifs with h
    · subst h; simp
    · simp
  rw [hsplit, Finset.prod_ite_eq' s 0 (fun _ => ν (t 0))]
  congr 1
  · simp only [T₀]; split_ifs <;> simp
  · rw [← Finset.prod_preimage Nat.succ s Nat.succ_injective.injOn
      (fun i => if i = 0 then 1 else ν (t i))]
    · rfl
    · intro x _ hx
      have : x = 0 := by
        by_contra h
        exact hx ⟨x - 1, by simp; omega⟩
      simp [this]

/-- The path from `y`: `W_n = y ξ_0 ⋯ ξ_{n-1}`. -/
def pathMap (y : Γ) (ξ : ℕ → Γ) : ℕ → Γ := fun n => y * (List.ofFn fun i : Fin n => ξ i).prod

theorem measurable_pathMap (y : Γ) : Measurable (pathMap (Γ := Γ) y) := by
  apply measurable_pi_lambda
  intro n
  have h1 : Measurable fun ξ : ℕ → Γ => fun i : Fin n => ξ i :=
    measurable_pi_lambda _ fun i => measurable_pi_apply _
  exact (measurable_of_countable (fun u : Fin n → Γ => y * (List.ofFn u).prod)).comp h1

theorem pathMap_cons_shift (y z : Γ) (ξ : ℕ → Γ) :
    (fun n => pathMap y (consMap (z, ξ)) (n + 1)) = pathMap (y * z) ξ := by
  funext n
  simp only [pathMap, List.ofFn_succ, List.prod_cons, mul_assoc]
  rfl


/-- `ℙ(E) = Σ_z μ(z) ℙ{ξ : z ξ ∈ E}`. -/
theorem measure_eq_tsum {μ : Γ → ℝ} (hμ : IsProbability μ) {E : Set (ℕ → Γ)} (hE : MeasurableSet E) :
    haveI := isProbabilityMeasure_stepMeasure hμ
    Measure.infinitePi (fun _ : ℕ => stepMeasure μ) E =
      ∑' z, ENNReal.ofReal (μ z) *
        Measure.infinitePi (fun _ : ℕ => stepMeasure μ) {ξ | consMap (z, ξ) ∈ E} := by
  haveI := isProbabilityMeasure_stepMeasure hμ
  conv_lhs => rw [← head_tail hμ]
  rw [Measure.map_apply measurable_consMap hE, Measure.prod_apply (measurable_consMap hE),
    lintegral_stepMeasure]
  rfl

/-- Rank-`n` cylinders. -/
def cyl (n : ℕ) (U : Set (Fin n → Γ)) : Set (ℕ → Γ) := {ξ | (fun i : Fin n => ξ i) ∈ U}

theorem measurableSet_cyl (n : ℕ) (U : Set (Fin n → Γ)) : MeasurableSet (cyl n U) := by
  have h1 : Measurable fun ξ : ℕ → Γ => fun i : Fin n => ξ i :=
    measurable_pi_lambda _ fun i => measurable_pi_apply _
  exact h1 (Set.to_countable U).measurableSet

theorem cons_mem_cyl (n : ℕ) (U : Set (Fin (n + 1) → Γ)) (z : Γ) (ξ : ℕ → Γ) :
    consMap (z, ξ) ∈ cyl (n + 1) U ↔ ξ ∈ cyl n {u | Fin.cons z u ∈ U} := by
  simp only [cyl, Set.mem_ofPred_eq]
  have : (fun i : Fin (n + 1) => consMap (z, ξ) i) = Fin.cons z (fun i : Fin n => ξ i) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp [consMap]
  rw [this]

theorem shift_mem {A : Set (ℕ → Γ)} (hAinv : IsShiftInvariant A) (w : ℕ → Γ) :
    w ∈ A ↔ (fun n => w (n + 1)) ∈ A := by
  constructor
  · intro h; rw [← hAinv] at h; exact h
  · intro h; rw [← hAinv]; exact h

theorem cons_mem_path {A : Set (ℕ → Γ)} (hAinv : IsShiftInvariant A) (y z : Γ) (ξ : ℕ → Γ) :
    consMap (z, ξ) ∈ pathMap y ⁻¹' A ↔ ξ ∈ pathMap (y * z) ⁻¹' A := by
  simp only [Set.mem_preimage]
  rw [shift_mem hAinv, pathMap_cons_shift]


end B7Dev

end ErschlerZheng
end

section
/-!
# B7: a shift-invariant event of intermediate probability gives a non-trivial Poisson boundary
(Kaimanovich–Vershik, pp. 9–10)

`F(y) = ℙ_y(A)` is `μ`-harmonic by the Markov property at the first step: under the product
measure, a path is its first increment followed by an independent path (`head_tail`), and
shift-invariance turns `W ∈ A` into `(path from y ξ_0) ∈ A`. If `F` were constant `= c` on the
points reachable from `x`, induction on the rank of a cylinder gives
`ℙ(S ∩ W_x⁻¹A) = c ℙ(S)` for every cylinder `S`; the cylinders generate the product σ-algebra,
so `ℙ(W_x⁻¹A) = c²` and `c ∈ {0, 1}`.
-/

open MeasureTheory

namespace ErschlerZheng

namespace B7Dev

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {Γ : Type*} [Group Γ] [Countable Γ] [MeasurableSpace Γ] [DiscreteMeasurableSpace Γ]

/-- If `ℙ_{x r}(A) = c` for every reachable `r`, then `ℙ(S ∩ W_{xr}⁻¹A) = c ℙ(S)` for cylinders. -/
theorem cyl_inter_eq {μ : Γ → ℝ} (hμ : IsProbability μ) {A : Set (ℕ → Γ)} (hA : MeasurableSet A)
    (hAinv : IsShiftInvariant A) (x : Γ) (c : ENNReal)
    (hconst : ∀ r ∈ Submonoid.closure (Function.support μ),
      haveI := isProbabilityMeasure_stepMeasure hμ
      Measure.infinitePi (fun _ : ℕ => stepMeasure μ) (pathMap (x * r) ⁻¹' A) = c) :
    haveI := isProbabilityMeasure_stepMeasure hμ
    ∀ (n : ℕ), ∀ r ∈ Submonoid.closure (Function.support μ), ∀ U : Set (Fin n → Γ),
      Measure.infinitePi (fun _ : ℕ => stepMeasure μ) (cyl n U ∩ pathMap (x * r) ⁻¹' A) =
        c * Measure.infinitePi (fun _ : ℕ => stepMeasure μ) (cyl n U) := by
  haveI := isProbabilityMeasure_stepMeasure hμ
  intro n
  induction n with
  | zero =>
    intro r hr U
    by_cases h : (fun i : Fin 0 => Fin.elim0 i : Fin 0 → Γ) ∈ U
    · have : cyl 0 U = Set.univ := by
        ext ξ
        simp only [cyl, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        convert h using 1
      rw [this, Set.univ_inter, hconst r hr, measure_univ, mul_one]
    · have : cyl 0 U = ∅ := by
        ext ξ
        simp only [cyl, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        convert h using 2
      rw [this, Set.empty_inter, measure_empty, mul_zero]
  | succ n ih =>
    intro r hr U
    have hE := (measurableSet_cyl _ U).inter ((measurable_pathMap (x * r)) hA)
    rw [measure_eq_tsum hμ hE, measure_eq_tsum hμ (measurableSet_cyl _ U),
      ← ENNReal.tsum_mul_left]
    congr 1
    funext z
    have hset : {ξ | consMap (z, ξ) ∈ cyl (n + 1) U ∩ pathMap (x * r) ⁻¹' A} =
        cyl n {u | Fin.cons z u ∈ U} ∩ pathMap (x * (r * z)) ⁻¹' A := by
      ext ξ
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      rw [cons_mem_cyl, cons_mem_path hAinv, mul_assoc]
    have hset2 : {ξ | consMap (z, ξ) ∈ cyl (n + 1) U} = cyl n {u | Fin.cons z u ∈ U} := by
      ext ξ; exact cons_mem_cyl n U z ξ
    rw [hset, hset2]
    by_cases hz : μ z = 0
    · simp [hz]
    · rw [ih (r * z) (Submonoid.mul_mem _ hr (Submonoid.subset_closure hz))]
      ring

/-- The 0–1 conclusion. -/
theorem sq_eq {μ : Γ → ℝ} (hμ : IsProbability μ) {A : Set (ℕ → Γ)} (hA : MeasurableSet A)
    (hAinv : IsShiftInvariant A) (x : Γ)
    (hconst : ∀ r ∈ Submonoid.closure (Function.support μ),
      haveI := isProbabilityMeasure_stepMeasure hμ
      Measure.infinitePi (fun _ : ℕ => stepMeasure μ) (pathMap (x * r) ⁻¹' A) =
        Measure.infinitePi (fun _ : ℕ => stepMeasure μ) (pathMap x ⁻¹' A)) :
    haveI := isProbabilityMeasure_stepMeasure hμ
    Measure.infinitePi (fun _ : ℕ => stepMeasure μ) (pathMap x ⁻¹' A) =
      Measure.infinitePi (fun _ : ℕ => stepMeasure μ) (pathMap x ⁻¹' A) *
        Measure.infinitePi (fun _ : ℕ => stepMeasure μ) (pathMap x ⁻¹' A) := by
  haveI := isProbabilityMeasure_stepMeasure hμ
  set P := Measure.infinitePi (fun _ : ℕ => stepMeasure μ)
  set W := pathMap x ⁻¹' A
  set c := P W
  have hW : MeasurableSet W := measurable_pathMap x hA
  have hclaim := cyl_inter_eq hμ hA hAinv x c hconst
  have hext : P.restrict W = c • P := by
    refine ext_of_generate_finite (measurableCylinders fun _ : ℕ => Γ)
      generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders ?_ ?_
    · intro t ht
      obtain ⟨s, S, hS, rfl⟩ := (mem_measurableCylinders t).mp ht
      set n := s.sup id + 1
      have hlt : ∀ i ∈ s, i < n := fun i hi => Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
      set U : Set (Fin n → Γ) := {u | (fun i : s => u ⟨i, hlt i i.2⟩) ∈ S}
      have hcyl : cylinder s S = cyl n U := by
        ext ξ
        simp only [mem_cylinder, cyl, U, Set.mem_ofPred_eq]
        rfl
      rw [hcyl, Measure.restrict_apply (measurableSet_cyl n U), Measure.smul_apply, smul_eq_mul]
      have := hclaim n 1 (Submonoid.one_mem _) U
      rwa [mul_one] at this
    · rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Measure.smul_apply,
        smul_eq_mul, measure_univ, mul_one]
  have := congrArg (fun m : Measure (ℕ → Γ) => m W) hext
  simp only [Measure.restrict_apply hW, Set.inter_self, Measure.smul_apply, smul_eq_mul] at this
  exact this

end B7Dev

end ErschlerZheng

namespace KaimanovichVershik

open ErschlerZheng ErschlerZheng.B7Dev MeasureTheory in
theorem hasNontrivialPoissonBoundary_of_isShiftInvariant_dev {Γ : Type*}
    [Group Γ] [Countable Γ] [MeasurableSpace Γ] [DiscreteMeasurableSpace Γ] (μ : Γ → ℝ)
    (hμ : IsProbability μ) (A : Set (ℕ → Γ)) (hA : MeasurableSet A) (hAinv : IsShiftInvariant A)
    (x : Γ) (hpos : 0 < pathMeasure μ x A) (hlt : pathMeasure μ x A < 1) :
    HasNontrivialPoissonBoundary μ := by
  have := isProbabilityMeasure_stepMeasure hμ
  set P := Measure.infinitePi (fun _ : ℕ => stepMeasure μ) with hP
  set F : Γ → ENNReal := fun y => P (pathMap y ⁻¹' A) with hF
  have hpath : ∀ y, pathMeasure μ y A = F y := by
    intro y
    show (Measure.map (pathMap y) P) A = F y
    rw [Measure.map_apply (measurable_pathMap y) hA]
  have hF1 : ∀ y, F y ≤ 1 := fun y => prob_le_one
  have hFtop : ∀ y, F y ≠ ⊤ := fun y => ne_top_of_le_ne_top ENNReal.one_ne_top (hF1 y)
  have hharm : ∀ y, F y = ∑' z, ENNReal.ofReal (μ z) * F (y * z) := by
    intro y
    show P (pathMap y ⁻¹' A) = _
    rw [measure_eq_tsum hμ (measurable_pathMap y hA)]
    congr 1; funext z
    congr 1
    show P _ = P _
    congr 1
    ext ξ
    exact cons_mem_path hAinv y z ξ
  set f : Γ → ℝ := fun g => (F (x * g)).toReal with hf
  refine ⟨f, ⟨1, fun g => ?_⟩, fun g => ?_, ?_⟩
  · rw [abs_of_nonneg ENNReal.toReal_nonneg]
    have := ENNReal.toReal_mono ENNReal.one_ne_top (hF1 (x * g))
    simpa using this
  · show (F (x * g)).toReal = ∑' y, (F (x * (g * y))).toReal * μ y
    rw [hharm (x * g), ENNReal.tsum_toReal_eq (fun z => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (hFtop _))]
    congr 1; funext z
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hμ.1 z), mul_comm, mul_assoc]
  · by_contra hcon
    push Not at hcon
    have hconst : ∀ r ∈ Submonoid.closure (Function.support μ),
        P (pathMap (x * r) ⁻¹' A) = P (pathMap x ⁻¹' A) := by
      intro r hr
      have := hcon r hr 1 (Submonoid.one_mem _)
      simp only [hf, mul_one] at this
      exact (ENNReal.toReal_eq_toReal_iff' (hFtop _) (hFtop _)).mp this
    have hsq := sq_eq hμ hA hAinv x hconst
    rw [hpath x] at hpos hlt
    have h0 : F x ≠ 0 := hpos.ne'
    change F x = F x * F x at hsq
    have h1 : F x = 1 := by
      have := (ENNReal.mul_right_inj h0 (hFtop x)).mp (hsq.symm.trans (mul_one (F x)).symm)
      exact this
    rw [h1] at hlt
    exact lt_irrefl _ hlt

end KaimanovichVershik
end

section
/-!
# The Kaimanovich–Vershik converse (pp. 9–10): a non-trivial Poisson boundary gives a
shift-invariant event of intermediate probability

Work on the increment space `Ω = ℕ → Γ` with the product measure `ν = ⊗ stepMeasure μ`; the walk
from `1` is `W_n = ξ_0 ⋯ ξ_{n-1}`, and `ℱ_n = σ(ξ_0, …, ξ_{n-1})`. For a bounded harmonic `f`,
`M_n = f(W_n)` is an `ℱ`-martingale (`ξ_n` is independent of `ℱ_n` and has law `μ`; harmonicity
averages it out). By the a.s. martingale convergence theorem `M_n → Z = limsup M_n` a.s. Put
`c = 𝔼 Z`. The events `{c < limsup f(w_n)}` and `{limsup f(w_n) < c}` of the path space are
shift-invariant. If neither had probability strictly between 0 and 1: probability 1 is impossible
(it would force `𝔼 Z ≠ c`), so `Z = c` a.s.; then for `s = {W_n = x}` (an `ℱ_n`-set), the martingale
property and dominated convergence give `f(x) ν(s) = ∫_s M_n = ∫_s Z = c ν(s)`, and `ν(s) > 0` for
every `x` in the submonoid generated by the support. So `f` would be constant there.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open ErschlerZheng

namespace KaimanovichVershik

namespace P3KVDev

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

variable {Γ : Type*} [Group Γ] [Countable Γ] [MeasurableSpace Γ] [DiscreteMeasurableSpace Γ]

/-- The first `n` increments. -/
def firstN (n : ℕ) (ξ : ℕ → Γ) : Fin n → Γ := fun i => ξ i

theorem measurable_firstN (n : ℕ) : Measurable (firstN (Γ := Γ) n) :=
  measurable_pi_lambda _ fun i => measurable_pi_apply _

/-- `W_n = ξ_0 ⋯ ξ_{n-1}`. -/
def walk (n : ℕ) (ξ : ℕ → Γ) : Γ := (List.ofFn (firstN n ξ)).prod

theorem measurable_walk (n : ℕ) : Measurable (walk (Γ := Γ) n) :=
  (measurable_of_countable (fun u : Fin n → Γ => (List.ofFn u).prod)).comp (measurable_firstN n)

theorem walk_succ (n : ℕ) (ξ : ℕ → Γ) : walk (n + 1) ξ = walk n ξ * ξ n := by
  simp only [walk, firstN, List.ofFn_succ', List.prod_concat]
  rfl

/-- `ℱ_n = σ(ξ_0, …, ξ_{n-1})`. -/
def filt : Filtration ℕ (MeasurableSpace.pi : MeasurableSpace (ℕ → Γ)) where
  seq n := MeasurableSpace.comap (firstN n) inferInstance
  mono' n m hnm := by
    have : firstN (Γ := Γ) n =
        (fun u : Fin m → Γ => fun i : Fin n => u (Fin.castLE hnm i)) ∘ firstN m := rfl
    simp only
    rw [this, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (Measurable.comap_le (measurable_of_countable _))
  le' n := (measurable_firstN n).comap_le

theorem measurable_filt {n : ℕ} (g : (Fin n → Γ) → ℝ) :
    Measurable[filt n] fun ξ : ℕ → Γ => g (firstN n ξ) :=
  (measurable_of_countable g).comp (comap_measurable (firstN n))

theorem stepMeasure_singleton {μ : Γ → ℝ} (hμ : IsProbability μ) (y : Γ) :
    (stepMeasure μ).real {y} = μ y := by
  rw [measureReal_def, B7Dev.stepMeasure_apply, tsum_eq_single y]
  · simp [ENNReal.toReal_ofReal (hμ.1 y)]
  · intro g hg; simp [hg]

theorem integral_stepMeasure {μ : Γ → ℝ} (hμ : IsProbability μ) {F : Γ → ℝ} {C : ℝ}
    (hF : ∀ y, |F y| ≤ C) : ∫ y, F y ∂stepMeasure μ = ∑' y, μ y * F y := by
  haveI := B7Dev.isProbabilityMeasure_stepMeasure hμ
  rw [integral_countable (Integrable.of_bound (measurable_of_countable F).aestronglyMeasurable C
    (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hF y))]
  congr 1; funext y
  rw [stepMeasure_singleton hμ, smul_eq_mul]

/-- The increment `ξ_n` is independent of the first `n` increments. -/
theorem indep_firstN {μ : Γ → ℝ} (hμ : IsProbability μ) (n : ℕ) :
    haveI := B7Dev.isProbabilityMeasure_stepMeasure hμ
    IndepFun (firstN n) (fun ξ : ℕ → Γ => ξ n) (Measure.infinitePi fun _ : ℕ => stepMeasure μ) := by
  haveI := B7Dev.isProbabilityMeasure_stepMeasure hμ
  have h := iIndepFun_infinitePi (P := fun _ : ℕ => stepMeasure μ) (X := fun _ (ω : Γ) => ω)
    (fun _ => measurable_id)
  have h2 := h.indepFun_finset (Finset.range n) {n} (by simp) (fun i => measurable_pi_apply i)
  have hφ : Measurable fun v : (Finset.range n) → Γ => fun i : Fin n => v ⟨i, by simp⟩ :=
    measurable_pi_lambda _ fun i => measurable_pi_apply _
  have hψ : Measurable fun v : ({n} : Finset ℕ) → Γ => v ⟨n, by simp⟩ := measurable_pi_apply _
  exact h2.comp hφ hψ

/-- The martingale step. -/
theorem setIntegral_succ {μ : Γ → ℝ} (hμ : IsProbability μ) {f : Γ → ℝ} (hf : IsHarmonic μ f)
    {C : ℝ} (hb : ∀ x, |f x| ≤ C) (n : ℕ) (s : Set (ℕ → Γ)) (hs : MeasurableSet[filt n] s) :
    ∫ ξ in s, f (walk n ξ) ∂(Measure.infinitePi fun _ : ℕ => stepMeasure μ) =
      ∫ ξ in s, f (walk (n + 1) ξ) ∂(Measure.infinitePi fun _ : ℕ => stepMeasure μ) := by
  classical
  haveI := B7Dev.isProbabilityMeasure_stepMeasure hμ
  set ν := Measure.infinitePi fun _ : ℕ => stepMeasure μ
  obtain ⟨U, -, rfl⟩ := hs
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hb 1)
  have hUm : MeasurableSet (firstN n ⁻¹' U : Set (ℕ → Γ)) :=
    measurable_firstN n (Set.to_countable U).measurableSet
  set h : (Fin n → Γ) × Γ → ℝ := fun p => if p.1 ∈ U then f ((List.ofFn p.1).prod * p.2) else 0
  have hh : ∀ p, |h p| ≤ C := by
    intro p; simp only [h]; split_ifs
    · exact hb _
    · simpa using hC
  have hX := measurable_firstN (Γ := Γ) n
  have hY : Measurable fun ξ : ℕ → Γ => ξ n := measurable_pi_apply n
  -- right-hand side as an integral against the joint law
  have hR : ∫ ξ in firstN n ⁻¹' U, f (walk (n + 1) ξ) ∂ν =
      ∫ p, h p ∂((ν.map (firstN n)).prod (ν.map fun ξ : ℕ → Γ => ξ n)) := by
    rw [← (indep_firstN hμ n).map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable,
      integral_map (hX.prodMk hY).aemeasurable
        (measurable_of_countable h).aestronglyMeasurable,
      ← integral_indicator hUm]
    congr 1; funext ξ
    simp only [Set.indicator, Set.mem_preimage, h, walk_succ]
    rfl
  have hint : Integrable h ((ν.map (firstN n)).prod (ν.map fun ξ : ℕ → Γ => ξ n)) :=
    Integrable.of_bound (measurable_of_countable h).aestronglyMeasurable C
      (ae_of_all _ fun p => by rw [Real.norm_eq_abs]; exact hh p)
  rw [hR, integral_prod h hint, Measure.infinitePi_map_eval]
  have hin : ∀ u : Fin n → Γ, ∫ y, h (u, y) ∂stepMeasure μ =
      if u ∈ U then f (List.ofFn u).prod else 0 := by
    intro u
    by_cases hu : u ∈ U
    · simp only [h, hu, if_true]
      rw [integral_stepMeasure hμ (fun y => hb _), hf]
      congr 1; funext y; ring
    · simp [h, hu]
  simp_rw [hin]
  rw [integral_map hX.aemeasurable (measurable_of_countable _).aestronglyMeasurable,
    ← integral_indicator hUm]
  congr 1

theorem martingale_walk {μ : Γ → ℝ} (hμ : IsProbability μ) {f : Γ → ℝ} (hf : IsHarmonic μ f)
    {C : ℝ} (hb : ∀ x, |f x| ≤ C) :
    haveI := B7Dev.isProbabilityMeasure_stepMeasure hμ
    Martingale (fun n ξ => f (walk n ξ)) filt (Measure.infinitePi fun _ : ℕ => stepMeasure μ) := by
  haveI := B7Dev.isProbabilityMeasure_stepMeasure hμ
  refine martingale_of_setIntegral_eq_succ (fun n => ?_) (fun n => ?_)
    (fun n s hs => setIntegral_succ hμ hf hb n s hs)
  · exact (measurable_filt (n := n) fun u => f (List.ofFn u).prod).stronglyMeasurable
  · exact Integrable.of_bound ((measurable_of_countable f).comp (measurable_walk n)).aestronglyMeasurable
      C (ae_of_all _ fun ξ => by rw [Real.norm_eq_abs]; exact hb _)

/-- Every product of elements of the support is reached with positive probability. -/
theorem reach {μ : Γ → ℝ} (hμ : IsProbability μ) {x : Γ}
    (hx : x ∈ Submonoid.closure (Function.support μ)) :
    ∃ n, (Measure.infinitePi fun _ : ℕ => stepMeasure μ) {ξ | walk n ξ = x} ≠ 0 := by
  haveI := B7Dev.isProbabilityMeasure_stepMeasure hμ
  obtain ⟨l, hl, rfl⟩ := Submonoid.exists_list_of_mem_closure hx
  refine ⟨l.length, ?_⟩
  set T : Set (ℕ → Γ) := Set.pi ↑(Finset.range l.length) fun i => {l.getD i 1}
  have hT : T ⊆ {ξ | walk l.length ξ = l.prod} := by
    intro ξ hξ
    simp only [T, Set.mem_pi, Finset.coe_range, Set.mem_Iio, Set.mem_singleton_iff] at hξ
    simp only [Set.mem_ofPred_eq, walk, firstN]
    congr 1
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.getElem_ofFn]
    show ξ i = l[i]
    rw [hξ i h2, List.getD_eq_getElem]
  have hνT : (Measure.infinitePi fun _ : ℕ => stepMeasure μ) T ≠ 0 := by
    show (Measure.infinitePi fun _ : ℕ => stepMeasure μ)
      (Set.pi ↑(Finset.range l.length) fun i => {l.getD i 1}) ≠ 0
    rw [Measure.infinitePi_pi _ (fun i _ => measurableSet_singleton _)]
    rw [Finset.prod_ne_zero_iff]
    intro i hi
    rw [Finset.mem_range] at hi
    have hmem : l.getD i 1 ∈ l := by
      rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
    have hpos : 0 < μ (l.getD i 1) := lt_of_le_of_ne (hμ.1 _) (Ne.symm (hl _ hmem))
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ _), ← measureReal_def,
      stepMeasure_singleton hμ]
    exact (ENNReal.ofReal_pos.mpr hpos).ne'
  exact fun h0 => hνT (measure_mono_null hT h0)

theorem not_ae_pos {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    {g : Ω → ℝ} (hg : Integrable g ν) (h0 : ∫ ω, g ω ∂ν = 0) : ¬ ∀ᵐ ω ∂ν, 0 < g ω := by
  intro h
  have h1 := (integral_eq_zero_iff_of_nonneg_ae (h.mono fun ω hω => hω.le) hg).mp h0
  have h2 : ∀ᵐ ω ∂ν, False := by
    filter_upwards [h, h1] with ω hω1 hω2
    simp only [Pi.zero_apply] at hω2
    linarith
  rw [Filter.eventually_false_iff_eq_bot, ae_eq_bot] at h2
  exact IsProbabilityMeasure.ne_zero ν h2

/-- The path-space event `{c ⋚ limsup f(w_n)}` is measurable and shift-invariant. -/
theorem measurable_limsup {f : Γ → ℝ} :
    Measurable fun w : ℕ → Γ => limsup (fun n => f (w n)) atTop :=
  Measurable.limsup fun n => (measurable_of_countable f).comp (measurable_pi_apply n)

theorem shift_limsup (f : Γ → ℝ) (w : ℕ → Γ) :
    limsup (fun n => f (w (n + 1))) atTop = limsup (fun n => f (w n)) atTop :=
  limsup_nat_add (fun n => f (w n)) 1

end P3KVDev

open P3KVDev in
theorem exists_isShiftInvariant_pathMeasure_pos_lt_one_dev
    {Γ : Type*} [Group Γ] [Countable Γ] [MeasurableSpace Γ] [DiscreteMeasurableSpace Γ]
    (μ : Γ → ℝ) (hμ : IsProbability μ) (hP : HasNontrivialPoissonBoundary μ) :
    ∃ A : Set (ℕ → Γ), MeasurableSet A ∧ IsShiftInvariant A ∧
      0 < pathMeasure μ 1 A ∧ pathMeasure μ 1 A < 1 := by
  haveI := B7Dev.isProbabilityMeasure_stepMeasure hμ
  obtain ⟨f, ⟨C, hb⟩, hf, x₀, hx₀, y₀, hy₀, hne⟩ := hP
  set ν := Measure.infinitePi fun _ : ℕ => stepMeasure μ with hν
  set M : ℕ → (ℕ → Γ) → ℝ := fun n ξ => f (walk n ξ) with hM
  have hmart : Martingale M filt ν := martingale_walk hμ hf hb
  have hMm : ∀ n, Measurable (M n) := fun n =>
    (measurable_of_countable f).comp (measurable_walk n)
  have hMb : ∀ n ξ, |M n ξ| ≤ C := fun n ξ => hb _
  have hconv := hmart.submartingale.ae_tendsto_limitProcess (R := C.toNNReal) fun n => by
    refine (eLpNorm_le_of_ae_bound (C := C) (ae_of_all _ fun ξ => ?_)).trans ?_
    · rw [Real.norm_eq_abs]; exact hMb n ξ
    · simp [ENNReal.ofReal]
  set Z : (ℕ → Γ) → ℝ := fun ξ => limsup (fun n => M n ξ) atTop with hZdef
  have hZ : ∀ᵐ ξ ∂ν, Tendsto (fun n => M n ξ) atTop (𝓝 (Z ξ)) := by
    filter_upwards [hconv] with ξ hξ
    rw [hZdef]; simp only
    rw [hξ.limsup_eq]; exact hξ
  have hZm : Measurable Z := Measurable.limsup hMm
  have hZb : ∀ᵐ ξ ∂ν, |Z ξ| ≤ C := by
    filter_upwards [hZ] with ξ hξ
    rw [abs_le]
    exact ⟨ge_of_tendsto' hξ fun n => (abs_le.mp (hMb n ξ)).1,
      le_of_tendsto' hξ fun n => (abs_le.mp (hMb n ξ)).2⟩
  have hZi : Integrable Z ν := Integrable.of_bound hZm.aestronglyMeasurable C
    (hZb.mono fun ξ h => by rwa [Real.norm_eq_abs])
  set c := ∫ ξ, Z ξ ∂ν with hc
  -- the two path-space events
  have hpath : ∀ (A : Set (ℕ → Γ)), MeasurableSet A →
      pathMeasure μ 1 A = ν (B7Dev.pathMap 1 ⁻¹' A) := fun A hA =>
    Measure.map_apply (B7Dev.measurable_pathMap 1) hA
  have hpre : ∀ ξ, limsup (fun n => f (B7Dev.pathMap 1 ξ n)) atTop = Z ξ := by
    intro ξ
    simp only [hZdef, hM, B7Dev.pathMap, one_mul, walk]
    rfl
  by_contra hcon
  push_neg at hcon
  have key : ∀ p : ℝ → Prop, (MeasurableSet {r | p r}) →
      ν {ξ | p (Z ξ)} = 0 ∨ 1 ≤ ν {ξ | p (Z ξ)} := by
    intro p hp
    set A : Set (ℕ → Γ) := {w | p (limsup (fun n => f (w n)) atTop)}
    have hA : MeasurableSet A := measurable_limsup hp
    have hAs : IsShiftInvariant A := by
      ext w
      simp only [A, Set.mem_preimage, Set.mem_ofPred_eq]
      rw [shift_limsup f w]
    have hνA : pathMeasure μ 1 A = ν {ξ | p (Z ξ)} := by
      rw [hpath A hA]
      congr 1
      ext ξ
      simp only [A, Set.mem_preimage, Set.mem_ofPred_eq, hpre]
    rw [← hνA]
    by_cases h0 : pathMeasure μ 1 A = 0
    · exact Or.inl h0
    · exact Or.inr (hcon A hA hAs (pos_iff_ne_zero.mpr h0))
  have hfull : ∀ p : ℝ → Prop, MeasurableSet {r | p r} → 1 ≤ ν {ξ | p (Z ξ)} →
      ∀ᵐ ξ ∂ν, p (Z ξ) := by
    intro p hp h1
    rw [ae_iff]
    have hmeas : MeasurableSet {ξ | p (Z ξ)} := hZm hp
    have := prob_compl_eq_one_sub (μ := ν) hmeas
    have hle : ν {ξ | p (Z ξ)} = 1 := le_antisymm prob_le_one h1
    rw [hle, tsub_self] at this
    simpa [Set.compl_def] using this
  have hgt : ν {ξ | c < Z ξ} = 0 := by
    rcases key (fun r => c < r) measurableSet_Ioi with h | h
    · exact h
    · exfalso
      refine not_ae_pos (hZi.sub (integrable_const c)) ?_ ((hfull _ measurableSet_Ioi h).mono
        fun ξ hξ => sub_pos.mpr hξ)
      simp only [Pi.sub_apply]
      rw [integral_sub hZi (integrable_const c), integral_const, probReal_univ, one_smul, sub_self]
  have hlt : ν {ξ | Z ξ < c} = 0 := by
    rcases key (fun r => r < c) measurableSet_Iio with h | h
    · exact h
    · exfalso
      refine not_ae_pos ((integrable_const c).sub hZi) ?_ ((hfull _ measurableSet_Iio h).mono
        fun ξ hξ => sub_pos.mpr hξ)
      simp only [Pi.sub_apply]
      rw [integral_sub (integrable_const c) hZi, integral_const, probReal_univ, one_smul,
        sub_self]
  have hZc : ∀ᵐ ξ ∂ν, Z ξ = c := by
    have h1 : ∀ᵐ ξ ∂ν, ¬ c < Z ξ := by rw [ae_iff]; simpa using hgt
    have h2 : ∀ᵐ ξ ∂ν, ¬ Z ξ < c := by rw [ae_iff]; simpa using hlt
    filter_upwards [h1, h2] with ξ h1 h2
    exact le_antisymm (not_lt.mp h1) (not_lt.mp h2)
  -- `f = c` on the submonoid generated by the support
  have hconst : ∀ x ∈ Submonoid.closure (Function.support μ), f x = c := by
    intro x hx
    obtain ⟨n, hn⟩ := reach hμ hx
    set s : Set (ℕ → Γ) := {ξ | walk n ξ = x}
    have hs : MeasurableSet[filt n] s :=
      ⟨{u | (List.ofFn u).prod = x}, (Set.to_countable _).measurableSet, rfl⟩
    have hsm : MeasurableSet s := (filt.le n) s hs
    have hlim : Tendsto (fun m => ∫ ξ in s, M m ξ ∂ν) atTop (𝓝 (∫ ξ in s, Z ξ ∂ν)) :=
      tendsto_integral_of_dominated_convergence (fun _ => C)
        (fun m => (hMm m).aestronglyMeasurable) (integrable_const C)
        (fun m => ae_of_all _ fun ξ => by rw [Real.norm_eq_abs]; exact hMb m ξ)
        (ae_restrict_of_ae hZ)
    have hev : Tendsto (fun m => ∫ ξ in s, M m ξ ∂ν) atTop (𝓝 (∫ ξ in s, M n ξ ∂ν)) :=
      tendsto_atTop_of_eventually_const (i₀ := n) fun m hm => (hmart.setIntegral_eq hm hs).symm
    have heq := tendsto_nhds_unique hev hlim
    have h1 : ∫ ξ in s, M n ξ ∂ν = ν.real s * f x := by
      rw [setIntegral_congr_fun hsm (g := fun _ => f x) (fun ξ hξ => by
        simp only [hM]; rw [show walk n ξ = x from hξ]), setIntegral_const, smul_eq_mul]
    have h2 : ∫ ξ in s, Z ξ ∂ν = ν.real s * c := by
      rw [setIntegral_congr_ae hsm (g := fun _ => c) (hZc.mono fun ξ h _ => h),
        setIntegral_const, smul_eq_mul]
    have hpos : 0 < ν.real s := ENNReal.toReal_pos hn (measure_ne_top _ _)
    rw [h1, h2] at heq
    exact mul_left_cancel₀ hpos.ne' heq
  exact hne ((hconst x₀ hx₀).trans (hconst y₀ hy₀).symm)

end KaimanovichVershik
end

section
/-!
# Kaimanovich–Vershik (pp. 9–10): the Poisson boundary is non-trivial iff some shift-invariant
event has probability strictly between 0 and 1

The two directions are `B7` (an invariant event gives a non-constant bounded harmonic function) and
`P3KV` (martingale convergence gives an invariant event, started at the identity).
-/

namespace KaimanovichVershik

end KaimanovichVershik
end

section
open KaimanovichVershik
open ErschlerZheng in
theorem solution
    {Γ : Type*} [Group Γ] [Countable Γ] [MeasurableSpace Γ] [DiscreteMeasurableSpace Γ]
    (μ : Γ → ℝ) (hμ : IsProbability μ) :
    HasNontrivialPoissonBoundary μ ↔
      ∃ A : Set (ℕ → Γ), MeasurableSet A ∧ IsShiftInvariant A ∧
        ∃ x : Γ, 0 < pathMeasure μ x A ∧ pathMeasure μ x A < 1 := by
  constructor
  · intro hP
    obtain ⟨A, hA, hAinv, hpos, hlt⟩ := exists_isShiftInvariant_pathMeasure_pos_lt_one_dev μ hμ hP
    exact ⟨A, hA, hAinv, 1, hpos, hlt⟩
  · rintro ⟨A, hA, hAinv, x, hpos, hlt⟩
    exact hasNontrivialPoissonBoundary_of_isShiftInvariant_dev μ hμ A hA hAinv x hpos hlt
end
