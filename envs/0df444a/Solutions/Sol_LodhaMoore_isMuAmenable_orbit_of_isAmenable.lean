-- Prove2me | solution 1 for LodhaMoore.isMuAmenable_orbit_of_isAmenable
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T11:34:29.137416+00:00
-- url     : https://prove2.me/submissions/eb6ec5d2-6ff6-4254-9319-57172b5d9f3b

import Mathlib
import Definitions.Def_LodhaMoore
import Definitions.Def_Monod_PiecewiseProjective
import Definitions.Def_Garrido_Amenability
import Theorems.Thm_Monod_isAmenableRel_orbit_of_isAmenable
import Theorems.Thm_LodhaMoore_isMuAmenable_of_isAmenableRel
section
/-! Development: `a`, `b`, `c` are the homeomorphisms the bundle names (`ofReal` returns the
extension of `aFun`, `bFun`, `cFun`), and their values on `ℝ`. -/

namespace LodhaMoore

end LodhaMoore
end

section
/-! Shared definitions for the Carrière–Ghys argument (Monod C9, `not_isAmenableRel_mob`). -/

namespace Monod.Dev.CG

open Matrix

variable {A : Subring ℝ}

end Monod.Dev.CG
end

section
/-! A4 of the Carrière–Ghys argument: for `|t| < 2`, the elliptic Möbius map `a_t : x ↦ t - 1/x`
preserves the finite measure `dx / (x² - t x + 1)` on `P¹`, which has the same null sets as
`volP1`; so `a_t` is conservative and every a.e. wandering set for `a_t` is null. -/

namespace Monod.Dev.CG.A4

open MeasureTheory Matrix OnePoint Set Filter

variable {A : Subring ℝ}

/-! ### The Möbius action of `ell t` -/

/-! ### The invariant weight `w(x) = 1 / (x² - τ x + 1)` -/

/-! ### Change of variables for `x ↦ τ - 1/x` -/

/-! ### Transport to `P¹` -/

end Monod.Dev.CG.A4

namespace Monod.Dev.CG

open MeasureTheory Matrix

end Monod.Dev.CG
end

section
namespace Monod.Dev.CG.A6

open Polynomial

end Monod.Dev.CG.A6

namespace Monod.Dev.CG

open Polynomial

end Monod.Dev.CG
end

section
/-! A5 + A7 of the Carrière–Ghys argument: the ping-pong partition of `SL(2, A)`. -/

namespace Monod.Dev.CG.A57

open Matrix

section PingPong

variable {K : Type} [NormedField K]

variable {E G : SpecialLinearGroup (Fin 2) K}

end PingPong

section Retraction

variable {A : Subring ℝ} (t : A)

end Retraction

end Monod.Dev.CG.A57

namespace Monod.Dev.CG

open Matrix

end Monod.Dev.CG
end

section
/-! # A8: the core of the Carrière–Ghys argument

A left invariant mean `P` on the orbit relation of `SL(2, A)` gives `u = P f_S`, where `f_S` is
the indicator of the pairs `(x, s x)` with `s ∈ S`.  Freeness off a countable set and the
ping-pong properties of `S` give `u + u ∘ b + u ∘ b² ≤ 1` and `1 ≤ u + u ∘ a^m` a.e.; the second
makes `{u < 1/2}` wandering for `a`, hence null, and the first is then contradictory. -/

namespace Monod.Dev.CG.A8

open Monod OnePoint Filter Topology Set MeasureTheory

variable {A : Subring ℝ}

/-! ### Möbius maps (copied from `DynBasic`) -/

/-! ### Measurability on `P¹ × P¹` -/

theorem secondCountable_P1 : SecondCountableTopology (OnePoint ℝ) :=
  (onePointEquivSphereOfFinrankEq (ι := Fin 2) (V := ℝ) (by simp)).isEmbedding.secondCountableTopology

attribute [local instance] secondCountable_P1

theorem countable_SL (A : Subring ℝ) [Countable A] :
    Countable (Matrix.SpecialLinearGroup (Fin 2) A) :=
  inferInstanceAs (Countable {M : Fin 2 → Fin 2 → A // Matrix.det M = 1})

attribute [local instance] countable_SL

section Bdd

variable {X : Type*} [MeasurableSpace X]

end Bdd

/-! ### The global partial transformations `φ_g` -/

/-! ### Null sets of `volP1` -/

/-! ### Freeness off a countable set -/

/-! ### The two pointwise inequalities -/

end Monod.Dev.CG.A8

namespace Monod.Dev.CG

open MeasureTheory Matrix

end Monod.Dev.CG
end

section
/-! # Group S2: statements 1, 3, 6, 7, 8, 10 of the Lodha–Moore development -/

namespace LodhaMoore.Dev.S2

open LodhaMoore Monod OnePoint Filter Topology Set

/-! ### Möbius maps over `⊤ : Subring ℝ` -/

/-- The real entries of a matrix of `SL(2, A)`. -/
noncomputable abbrev ent {A : Subring ℝ} (g : Matrix.SpecialLinearGroup (Fin 2) A) (i j : Fin 2) :
    ℝ := ((g i j : A) : ℝ)

/-- A matrix of `SL(2, ℝ)` (over `⊤ : Subring ℝ`) from its real entries. -/
noncomputable def mk2 (p q r s : ℝ) (h : p * s - q * r = 1) :
    Matrix.SpecialLinearGroup (Fin 2) (⊤ : Subring ℝ) :=
  ⟨!![⟨p, trivial⟩, ⟨q, trivial⟩; ⟨r, trivial⟩, ⟨s, trivial⟩], by
    rw [Matrix.det_fin_two_of]
    ext
    simpa using h⟩

@[simp] lemma ent_mk2_00 (p q r s : ℝ) (h) : ent (mk2 p q r s h) 0 0 = p := rfl
@[simp] lemma ent_mk2_01 (p q r s : ℝ) (h) : ent (mk2 p q r s h) 0 1 = q := rfl
@[simp] lemma ent_mk2_10 (p q r s : ℝ) (h) : ent (mk2 p q r s h) 1 0 = r := rfl
@[simp] lemma ent_mk2_11 (p q r s : ℝ) (h) : ent (mk2 p q r s h) 1 1 = s := rfl

/-! ### Statement 1: `G₀ ≤ H` -/

end LodhaMoore.Dev.S2

namespace LodhaMoore

open LodhaMoore.Dev.S2

end LodhaMoore

namespace LodhaMoore.Dev.S2

open LodhaMoore Filter Topology Set
open scoped ENNReal

/-! ### Statement 3: `φ` and `Φ` -/

end LodhaMoore.Dev.S2

namespace LodhaMoore

open LodhaMoore.Dev.S2

end LodhaMoore

namespace LodhaMoore.Dev.S2

open LodhaMoore MeasureTheory Set
open scoped ENNReal

section Orbit

variable {X : Type*} [MeasurableSpace X] (Γ : Type) [Group Γ] [MulAction Γ X]

/-- A measure dominating `ν` and quasi-invariant under `Γ`: `∑ 2⁻ⁿ (e n)_* ν`. -/
noncomputable def qiMeasure (ν : Measure X) (e : ℕ → Γ) : Measure X :=
  Measure.sum fun n => ((2 : ℝ≥0∞)⁻¹ ^ n) • ν.map (fun x => e n • x)

variable {Γ}

lemma qiMeasure_apply (ν : Measure X) (e : ℕ → Γ) (hmeas : ∀ g : Γ, Measurable fun x : X => g • x)
    {s : Set X} (hs : MeasurableSet s) :
    qiMeasure Γ ν e s = ∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * ν ((fun x => e n • x) ⁻¹' s) := by
  rw [qiMeasure, Measure.sum_apply _ hs]
  congr 1
  funext n
  rw [Measure.smul_apply, Measure.map_apply (hmeas _) hs, smul_eq_mul]

lemma qiMeasure_eq_zero_iff (ν : Measure X) (e : ℕ → Γ)
    (hmeas : ∀ g : Γ, Measurable fun x : X => g • x) {s : Set X} (hs : MeasurableSet s) :
    qiMeasure Γ ν e s = 0 ↔ ∀ n, ν ((fun x => e n • x) ⁻¹' s) = 0 := by
  rw [qiMeasure_apply ν e hmeas hs, ENNReal.tsum_eq_zero]
  refine forall_congr' fun n => ?_
  rw [mul_eq_zero]
  simp

lemma qiMeasure_quasiInv (ν : Measure X) (e : ℕ → Γ) (he : Function.Surjective e)
    (hmeas : ∀ g : Γ, Measurable fun x : X => g • x) (l : Γ) (s : Set X)
    (hs : qiMeasure Γ ν e s = 0) : qiMeasure Γ ν e ((fun x : X => l • x) ⁻¹' s) = 0 := by
  set t := toMeasurable (qiMeasure Γ ν e) s
  have ht : MeasurableSet t := measurableSet_toMeasurable _ _
  have ht0 : qiMeasure Γ ν e t = 0 := by rw [measure_toMeasurable]; exact hs
  refine measure_mono_null (preimage_mono (subset_toMeasurable (qiMeasure Γ ν e) s)) ?_
  rw [qiMeasure_eq_zero_iff ν e hmeas (hmeas l ht)]
  rw [qiMeasure_eq_zero_iff ν e hmeas ht] at ht0
  intro n
  obtain ⟨m, hm⟩ := he (l * e n)
  have : (fun x => e n • x) ⁻¹' ((fun x : X => l • x) ⁻¹' t) = (fun x => e m • x) ⁻¹' t := by
    ext x
    simp [hm, mul_smul]
  rw [this]
  exact ht0 m

lemma qiMeasure_isFinite (ν : Measure X) [IsFiniteMeasure ν] (e : ℕ → Γ)
    (hmeas : ∀ g : Γ, Measurable fun x : X => g • x) : IsFiniteMeasure (qiMeasure Γ ν e) := by
  constructor
  rw [qiMeasure_apply ν e hmeas MeasurableSet.univ]
  simp only [preimage_univ]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
  refine ENNReal.mul_lt_top ?_ (measure_lt_top ν univ)
  rw [ENNReal.inv_lt_top]
  exact tsub_pos_of_lt (ENNReal.inv_lt_one.2 (by norm_num))

lemma ac_qiMeasure (ν : Measure X) (e : ℕ → Γ) (he : Function.Surjective e)
    (hmeas : ∀ g : Γ, Measurable fun x : X => g • x) {s : Set X} (hs : MeasurableSet s)
    (h0 : qiMeasure Γ ν e s = 0) : ν s = 0 := by
  rw [qiMeasure_eq_zero_iff ν e hmeas hs] at h0
  obtain ⟨n, hn⟩ := he 1
  have := h0 n
  simpa [hn] using this

end Orbit

end LodhaMoore.Dev.S2

namespace LodhaMoore

open LodhaMoore.Dev.S2 MeasureTheory Set

end LodhaMoore

namespace LodhaMoore.Dev.S2

open LodhaMoore Monod OnePoint Filter Topology Set Matrix

@[simp] lemma ent_kTrans_00 : ent kTrans 0 0 = 1 := rfl
@[simp] lemma ent_kTrans_01 : ent kTrans 0 1 = 1 := rfl
@[simp] lemma ent_kTrans_10 : ent kTrans 1 0 = 0 := rfl
@[simp] lemma ent_kTrans_11 : ent kTrans 1 1 = 1 := rfl
@[simp] lemma ent_kInv_00 : ent kInv 0 0 = 0 := rfl
@[simp] lemma ent_kInv_01 : ent kInv 0 1 = 1 := rfl
@[simp] lemma ent_kInv_10 : ent kInv 1 0 = -1 := rfl
@[simp] lemma ent_kInv_11 : ent kInv 1 1 = 0 := rfl
@[simp] lemma ent_kDil_00 : ent kDil 0 0 = Real.sqrt 2 := rfl
@[simp] lemma ent_kDil_01 : ent kDil 0 1 = 0 := rfl
@[simp] lemma ent_kDil_10 : ent kDil 1 0 = 0 := rfl
@[simp] lemma ent_kDil_11 : ent kDil 1 1 = 1 / Real.sqrt 2 := rfl

/-! ### Möbius maps are continuous and preserve null sets (from the Monod development) -/

section Mob

variable {A : Subring ℝ}

theorem secondCountable_P1 : SecondCountableTopology (OnePoint ℝ) :=
  (onePointEquivSphereOfFinrankEq (ι := Fin 2) (V := ℝ) (by simp)).isEmbedding.secondCountableTopology

theorem polishSpace_P1 : PolishSpace (OnePoint ℝ) := by
  have e := onePointEquivSphereOfFinrankEq (ι := Fin 2) (V := ℝ) (by simp)
  have : PolishSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    Metric.isClosed_sphere.polishSpace
  exact e.isClosedEmbedding.polishSpace

theorem sigmaFinite_volP1 : MeasureTheory.SigmaFinite volP1 :=
  OnePoint.isOpenEmbedding_coe.measurableEmbedding.sigmaFinite_map

end Mob

attribute [local instance] secondCountable_P1 polishSpace_P1 sigmaFinite_volP1

end LodhaMoore.Dev.S2

namespace LodhaMoore

open LodhaMoore.Dev.S2

attribute [local instance] secondCountable_P1 polishSpace_P1 sigmaFinite_volP1

end LodhaMoore

namespace LodhaMoore.Dev.S2

open LodhaMoore Monod OnePoint Filter Topology Set Matrix

/-! ### Statement 10: `G₀`- and `K`-orbits of irrational points -/

end LodhaMoore.Dev.S2

namespace LodhaMoore

open LodhaMoore.Dev.S2

end LodhaMoore

namespace LodhaMoore.Dev.S2

open LodhaMoore Monod OnePoint Filter Topology Set MeasureTheory

/-! ### The Carrière–Ghys ping-pong argument for a countable subgroup `Λ` of `SL(2, ℝ)`

Monod's development (`Monod.Dev.CG.A8`) runs the argument for the orbit relation of `SL(2, A)`;
here it is run for the orbit relation of any countable subgroup `Λ` containing `a_t`, `b_t` and
a ping-pong set `S ⊆ Λ`. -/

section CGL

attribute [local instance] secondCountable_P1

variable {Λ}

end CGL


/-! ### The Carrière–Ghys argument for `K` -/

end LodhaMoore.Dev.S2

namespace LodhaMoore

open LodhaMoore.Dev.S2

attribute [local instance] secondCountable_P1 polishSpace_P1 sigmaFinite_volP1

end LodhaMoore

namespace LodhaMoore.Dev.S2

open LodhaMoore Monod MeasureTheory

end LodhaMoore.Dev.S2

namespace LodhaMoore

open LodhaMoore.Dev.S2

attribute [local instance] secondCountable_P1 polishSpace_P1 sigmaFinite_volP1

end LodhaMoore
end

section
open LodhaMoore
open LodhaMoore.Dev.S2 MeasureTheory Set
theorem solution {X : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : MeasureTheory.Measure X) [MeasureTheory.SigmaFinite μ]
    (Γ : Type) [Group Γ] [Countable Γ] [MulAction Γ X]
    (hmeas : ∀ g : Γ, Measurable fun x : X => g • x) (hΓ : Garrido.IsAmenable Γ) :
    IsMuAmenable μ {p : X × X | ∃ g : Γ, g • p.1 = p.2} := by
  obtain ⟨e, he⟩ := exists_surjective_nat Γ
  set ν := μ.toFinite
  set μ' := qiMeasure Γ ν e
  have : IsFiniteMeasure μ' := qiMeasure_isFinite ν e hmeas
  set E := {p : X × X | ∃ g : Γ, g • p.1 = p.2}
  have hqi : ∀ (l : Γ) (s : Set X), μ' s = 0 → μ' ((fun x : X => l • x) ⁻¹' s) = 0 :=
    fun l s hs => qiMeasure_quasiInv ν e he hmeas l s hs
  have hrel : Monod.IsAmenableRel μ' E :=
    Monod.isAmenableRel_orbit_of_isAmenable μ' Γ hmeas hqi hΓ
  have hE : MeasurableSet E := by
    have : E = ⋃ g : Γ, (fun p : X × X => (g • p.1, p.2)) ⁻¹' Set.diagonal X := by
      ext p
      simp [E, Set.mem_diagonal_iff]
    rw [this]
    exact MeasurableSet.iUnion fun g =>
      measurableSet_diagonal.preimage (((hmeas g).comp measurable_fst).prodMk measurable_snd)
  have hequiv : Equivalence fun x y => (x, y) ∈ E := by
    refine ⟨fun x => ⟨1, one_smul Γ x⟩, ?_, ?_⟩
    · rintro x y ⟨g, hg⟩
      exact ⟨g⁻¹, by simp only at hg ⊢; rw [← hg, inv_smul_smul]⟩
    · rintro x y z ⟨g, hg⟩ ⟨h, hh⟩
      exact ⟨h * g, by simp only at hg hh ⊢; rw [mul_smul, hg, hh]⟩
  have hcount : ∀ x, {y | (x, y) ∈ E}.Countable := fun x =>
    (Set.countable_range fun g : Γ => g • x).mono (by rintro y ⟨g, hg⟩; exact ⟨g, hg⟩)
  have hsat : ∀ A : Set X, μ' A = 0 → μ' {y | ∃ x ∈ A, (x, y) ∈ E} = 0 := by
    intro A hA
    have : {y | ∃ x ∈ A, (x, y) ∈ E} ⊆ ⋃ g : Γ, (fun y : X => g • y) ⁻¹' A := by
      rintro y ⟨x, hx, g, hg⟩
      refine Set.mem_iUnion.2 ⟨g⁻¹, ?_⟩
      simp only [Set.mem_preimage]
      simp only at hg
      rw [← hg, inv_smul_smul]
      exact hx
    exact measure_mono_null this (measure_iUnion_null fun g => hqi g A hA)
  obtain ⟨N, hN, hN0, T, hT⟩ :=
    isMuAmenable_of_isAmenableRel μ' E hE hequiv hcount hsat hrel
  refine ⟨N, hN, ?_, T, hT⟩
  have hν : ν N = 0 := ac_qiMeasure ν e he hmeas hN hN0
  exact toFinite_apply_eq_zero_iff.1 hν
end
