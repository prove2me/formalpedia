-- Prove2me | solution 1 for OAI.MarkovSuperreflexivity.hasNontrivialMarkovType_iff_hasEquivalentUCNorm
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T10:45:42.658621+00:00
-- url     : https://prove2.me/submissions/6d269ec7-d86a-456f-97a9-29d57a77e6da

import Mathlib
import Init.Data.List.Count
import Lean.Elab.Tactic.Omega
import Definitions.Def_MarkovType
import Definitions.Def_OAISMk002
import Theorems.Thm_OAI_MarkovSuperreflexivity_MarkovTypeWith_not_coordinatesRepresentable
import Theorems.Thm_OAI_MarkovSuperreflexivity_exists_power_smooth_equivalentNorm
import Theorems.Thm_OAI_MarkovSuperreflexivity_hasEquivalentUCNorm_of_finiteTriangularObstruction

section
-- module Solutions.OAIS_Markov.MarkovType_C00FiniteCoordinates
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.OrderedNorm.instCoeFunForallC00Real _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

namespace C00

theorem smul_basis (r : ℝ) (i : ℕ) : r • basis i = Finsupp.single i r := by
  simp [basis]

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem linearMap_ofArray (L : C00 →ₗ[ℝ] Y) {m : ℕ} (a : Fin m → ℝ) :
    L (ofArray a) = ∑ i, a i • L (basis i.val) := by
  simp only [ofArray, place, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← smul_basis, map_smul]

theorem norm_linearMap_ofArray_le (L : C00 →ₗ[ℝ] Y)
    (hunit : ∀ i, ‖L (basis i)‖ ≤ 1) {m : ℕ} (a : Fin m → ℝ) :
    ‖L (ofArray a)‖ ≤ ∑ i, |a i| := by
  rw [linearMap_ofArray]
  calc
    ‖∑ i, a i • L (basis i.val)‖ ≤ ∑ i, ‖a i • L (basis i.val)‖ :=
      norm_sum_le _ _
    _ = ∑ i, |a i| * ‖L (basis i.val)‖ := by
      simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ i, |a i| := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (hunit i.val) (abs_nonneg (a i))

theorem abs_norm_linearMap_ofArray_sub_le (L : C00 →ₗ[ℝ] Y)
    (hunit : ∀ i, ‖L (basis i)‖ ≤ 1) {m : ℕ} (a b : Fin m → ℝ) :
    |‖L (ofArray a)‖ - ‖L (ofArray b)‖| ≤ ∑ i, |a i - b i| := by
  calc
    |‖L (ofArray a)‖ - ‖L (ofArray b)‖| ≤ ‖L (ofArray a) - L (ofArray b)‖ :=
      abs_norm_sub_norm_le _ _
    _ = ‖L (ofArray (a - b))‖ := by
      rw [← map_sub]
      congr 2
      exact (map_sub (arrayLinear m) a b).symm
    _ ≤ ∑ i, |a i - b i| := norm_linearMap_ofArray_le L hunit (a - b)

end C00

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_CoefficientGrid
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

noncomputable section

theorem abs_coefficientGridValue_le (k : ℕ) (hk : 0 < k)
    (j : Fin (2 * k ^ 2 + 1)) : |coefficientGridValue k j| ≤ 1 := by
  have hq : 0 < (k : ℝ) ^ 2 := pow_pos (Nat.cast_pos.mpr hk) _
  have hj : j.val ≤ 2 * k ^ 2 := Nat.le_of_lt_succ j.isLt
  have hjR : (j.val : ℝ) ≤ 2 * (k : ℝ) ^ 2 := by exact_mod_cast hj
  have hlo : 0 ≤ (j.val : ℝ) / (k : ℝ) ^ 2 :=
    div_nonneg (Nat.cast_nonneg _) hq.le
  have hhi : (j.val : ℝ) / (k : ℝ) ^ 2 ≤ 2 :=
    (div_le_iff₀ hq).2 hjR
  unfold coefficientGridValue
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem exists_coefficientGrid_approx (k : ℕ) (hk : 0 < k)
    (a : ℝ) (ha : |a| ≤ 1) :
    ∃ j : Fin (2 * k ^ 2 + 1),
      |a - coefficientGridValue k j| ≤ 1 / (k : ℝ) ^ 2 := by
  have hq : 0 < (k : ℝ) ^ 2 := pow_pos (Nat.cast_pos.mpr hk) _
  obtain ⟨haLower, haUpper⟩ := abs_le.mp ha
  let x : ℝ := (a + 1) * (k : ℝ) ^ 2
  have hx0 : 0 ≤ x := by
    dsimp only [x]
    exact mul_nonneg (by linarith) hq.le
  have hxUpper : x ≤ ((2 * k ^ 2 : ℕ) : ℝ) := by
    dsimp only [x]
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      mul_le_mul_of_nonneg_right (show a + 1 ≤ (2 : ℝ) by linarith) hq.le
  let n : ℕ := ⌊x⌋₊
  have hn : n ≤ 2 * k ^ 2 := Nat.floor_le_of_le hxUpper
  let j : Fin (2 * k ^ 2 + 1) := ⟨n, Nat.lt_succ_of_le hn⟩
  have hnDiv : (n : ℝ) / (k : ℝ) ^ 2 ≤ a + 1 :=
    (div_le_iff₀ hq).2 (Nat.floor_le hx0)
  have hNear : a + 1 < ((n : ℝ) + 1) / (k : ℝ) ^ 2 :=
    (lt_div_iff₀ hq).2 (Nat.lt_floor_add_one x)
  rw [add_div] at hNear
  refine ⟨j, ?_⟩
  change |a - ((n : ℝ) / (k : ℝ) ^ 2 - 1)| ≤ 1 / (k : ℝ) ^ 2
  rw [abs_of_nonneg (show 0 ≤ a - ((n : ℝ) / (k : ℝ) ^ 2 - 1) by linarith)]
  linarith

end

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_CoordinateFactorization
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instFiniteDimensionalReal _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instModuleReal _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNorm _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem CoordinatesRepresentable.of_factorization (N : OrderedNorm)
    (p : Seminorm ℝ C00)
    (hNp : ∀ (m : ℕ) (η : ℝ), 0 < η →
      ∃ (k : ℕ) (A : (Fin m → ℝ) →ₗ[ℝ] (Fin k → ℝ)), ∀ a,
        N (C00.ofArray a) ≤ p (C00.ofArray (A a)) ∧
          p (C00.ofArray (A a)) ≤ (1 + η) * N (C00.ofArray a))
    (hpY : ∀ (k : ℕ) (η : ℝ), 0 < η →
      ∃ T : (Fin k → ℝ) →ₗ[ℝ] Y, ∀ b,
        p (C00.ofArray b) ≤ ‖T b‖ ∧
          ‖T b‖ ≤ (1 + η) * p (C00.ofArray b)) :
    CoordinatesRepresentable Y N := by
  intro m ε hε
  let δ : ℝ := min (ε / 3) 1
  have hδ : 0 < δ := lt_min (by linarith) zero_lt_one
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδε : δ ≤ ε / 3 := min_le_left _ _
  have hfactor : (1 + δ) * (1 + δ) ≤ 1 + ε := by
    have hsquare : δ * δ ≤ δ := by nlinarith
    nlinarith
  obtain ⟨k, A, hA⟩ := hNp m δ hδ
  obtain ⟨T, hT⟩ := hpY k δ hδ
  refine ⟨T.comp A, ?_⟩
  intro a
  constructor
  · exact (hA a).1.trans (hT (A a)).1
  · calc
      ‖(T.comp A) a‖ ≤ (1 + δ) * p (C00.ofArray (A a)) := (hT (A a)).2
      _ ≤ (1 + δ) * ((1 + δ) * N (C00.ofArray a)) :=
        mul_le_mul_of_nonneg_left (hA a).2 (by linarith)
      _ = ((1 + δ) * (1 + δ)) * N (C00.ofArray a) :=
        (mul_assoc _ _ _).symm
      _ ≤ (1 + ε) * N (C00.ofArray a) :=
        mul_le_mul_of_nonneg_right hfactor (N.nonneg _)

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_CoordinateRepresentability
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instFiniteDimensionalReal _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instModuleReal _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNorm _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

universe u v

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem CoordinatesRepresentable.transfer {N : OrderedNorm}
    (hNY : CoordinatesRepresentable Y N) (hYX : FinitelyRepresentable Y X) :
    CoordinatesRepresentable X N := by
  intro m ε hε
  let δ : ℝ := min (ε / 3) 1
  have hδ : 0 < δ := lt_min (by linarith) zero_lt_one
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδε : δ ≤ ε / 3 := min_le_left _ _
  have hfactor : (1 + δ) * (1 + δ) ≤ 1 + ε := by
    have hsquare : δ * δ ≤ δ := by nlinarith
    nlinarith
  obtain ⟨T, hT⟩ := hNY m δ hδ
  let E : Submodule ℝ Y := LinearMap.range T
  let : FiniteDimensional ℝ E := LinearMap.finiteDimensional_range T
  obtain ⟨S, hS⟩ := hYX E δ hδ
  refine ⟨S.comp T.rangeRestrict, ?_⟩
  intro a
  have hnorm : ‖T.rangeRestrict a‖ = ‖T a‖ := rfl
  constructor
  · exact (hT a).1.trans (by simpa only [LinearMap.comp_apply, hnorm] using (hS (T.rangeRestrict a)).1)
  · calc
      ‖(S.comp T.rangeRestrict) a‖ ≤ (1 + δ) * ‖T.rangeRestrict a‖ :=
        (hS (T.rangeRestrict a)).2
      _ = (1 + δ) * ‖T a‖ := by rw [hnorm]
      _ ≤ (1 + δ) * ((1 + δ) * N (C00.ofArray a)) :=
        mul_le_mul_of_nonneg_left (hT a).2 (by linarith)
      _ = ((1 + δ) * (1 + δ)) * N (C00.ofArray a) :=
        (mul_assoc _ _ _).symm
      _ ≤ (1 + ε) * N (C00.ofArray a) :=
        mul_le_mul_of_nonneg_right hfactor (N.nonneg _)

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_DenseFiniteApproximation
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

theorem exists_linearMap_approx_subtype
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ι : E →ₗᵢ[ℝ] F) (hι : DenseRange ι)
    (V : Submodule ℝ F) [FiniteDimensional ℝ V]
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ T : V →ₗ[ℝ] E, ∀ v : V, ‖ι (T v) - (v : F)‖ ≤ δ * ‖v‖ := by
  classical
  let b := Module.finBasis ℝ V
  obtain ⟨C : ℝ, hC : 0 < C,
      hbound : ∀ {L : V →L[ℝ] F} {M : ℝ},
        0 ≤ M → (∀ i, ‖L (b i)‖ ≤ M) → ‖L‖ ≤ C * M⟩ :=
    b.exists_opNorm_le (F := F)
  let ρ : ℝ := δ / C
  have hρ : 0 < ρ := div_pos hδ hC
  have happrox : ∀ i : Fin (Module.finrank ℝ V),
      ∃ x : E, ‖ι x - (b i : F)‖ < ρ := by
    intro i
    obtain ⟨x, hx⟩ := hι.exists_dist_lt (b i : F) hρ
    exact ⟨x, by simpa only [dist_eq_norm'] using hx⟩
  choose a ha using happrox
  let T : V →ₗ[ℝ] E := b.constr ℝ a
  let U : V →L[ℝ] F :=
    LinearMap.toContinuousLinearMap (ι.toLinearMap.comp T - V.subtype)
  have hUb : ∀ i, ‖U (b i)‖ ≤ ρ := by
    intro i
    change ‖ι (b.constr ℝ a (b i)) - (b i : F)‖ ≤ ρ
    rw [b.constr_basis]
    exact (ha i).le
  have hU : ‖U‖ ≤ δ := by
    calc
      ‖U‖ ≤ C * ρ := hbound hρ.le hUb
      _ = δ := by
        dsimp only [ρ]
        exact mul_div_cancel₀ δ (ne_of_gt hC)
  refine ⟨T, ?_⟩
  intro v
  change ‖U v‖ ≤ δ * ‖v‖
  exact (U.le_opNorm v).trans (mul_le_mul_of_nonneg_right hU (norm_nonneg v))

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteAnnihilator
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

open NormedSpace StrongDual

universe u

variable {Y : Type u} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem finite_double_annihilator
    (E : Submodule ℝ Y) [FiniteDimensional ℝ E]
    (w : StrongDual ℝ (StrongDual ℝ Y))
    (hw : ∀ f : polarSubmodule ℝ E, w (f : StrongDual ℝ Y) = 0) :
    ∃ e : E, w = inclusionInDoubleDual ℝ Y (e : Y) := by
  classical
  let R : StrongDual ℝ Y →ₗ[ℝ] StrongDual ℝ E :=
    { toFun := fun f => f.comp E.subtypeL
      map_add' := by intro f g; ext e; rfl
      map_smul' := by intro c f; ext e; rfl }
  have hR : Function.Surjective R := by
    intro g
    obtain ⟨G, hG, _⟩ := exists_extension_norm_eq E g
    refine ⟨G, ?_⟩
    ext e
    exact hG e
  obtain ⟨S, hS⟩ :=
    R.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hR)
  have hS_apply (g : StrongDual ℝ E) : R (S g) = g := by
    exact congrArg (fun L : StrongDual ℝ E →ₗ[ℝ] StrongDual ℝ E => L g) hS
  let C : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] StrongDual ℝ E := LinearMap.toContinuousLinearMap
  let L : (E →ₗ[ℝ] ℝ) →ₗ[ℝ] ℝ :=
    w.toLinearMap.comp (S.comp C.toLinearMap)
  have hEval : Function.Surjective (Module.Dual.eval ℝ E) :=
    LinearMap.range_eq_top.mp (Module.Basis.ofVectorSpace ℝ E).eval_range
  obtain ⟨e, he⟩ := hEval L
  refine ⟨e, ?_⟩
  ext f
  have hker : f - S (R f) ∈ polarSubmodule ℝ E := by
    apply (mem_polarSubmodule ℝ E (f - S (R f))).mpr
    intro y hy
    have hvalue := congrArg (fun g : StrongDual ℝ E => g ⟨y, hy⟩) (hS_apply (R f))
    change S (R f) y = f y at hvalue
    change f y - S (R f) y = 0
    exact sub_eq_zero.mpr hvalue.symm
  have hzero : w f - w (S (R f)) = 0 := by
    simpa only [map_sub] using hw ⟨f - S (R f), hker⟩
  have heval := congrArg
    (fun q : (E →ₗ[ℝ] ℝ) →ₗ[ℝ] ℝ => q (R f).toLinearMap) he
  change f (e : Y) = w (S (R f)) at heval
  change w f = f (e : Y)
  exact (sub_eq_zero.mp hzero).trans heval.symm

attribute [local instance] OAI.MarkovSuperreflexivity.normStrongDualSubmodule
theorem restriction_norm_eq_infDist_finite_image
    (E : Submodule ℝ Y) [FiniteDimensional ℝ E]
    (v : StrongDual ℝ (StrongDual ℝ Y)) :
    ‖(v.comp (polarSubmodule ℝ E).subtypeL : StrongDual ℝ (polarSubmodule ℝ E))‖ =
      Metric.infDist v
        (Set.range fun e : E => inclusionInDoubleDual ℝ Y (e : Y)) := by
  let A := polarSubmodule ℝ E
  let r : StrongDual ℝ A := v.comp A.subtypeL
  have hnonempty :
      (Set.range fun e : E => inclusionInDoubleDual ℝ Y (e : Y)).Nonempty :=
    ⟨inclusionInDoubleDual ℝ Y (0 : Y), ⟨0, rfl⟩⟩
  change ‖r‖ = _
  apply le_antisymm
  · apply (Metric.le_infDist hnonempty).mpr
    rintro z ⟨e, rfl⟩
    rw [dist_eq_norm v (inclusionInDoubleDual ℝ Y (e : Y))]
    change sInf {c : ℝ | 0 ≤ c ∧ ∀ f : A, ‖r f‖ ≤ c * ‖f‖} ≤
      ‖v - inclusionInDoubleDual ℝ Y (e : Y)‖
    refine csInf_le ⟨0, fun c hc => hc.1⟩
      ⟨ContinuousLinearMap.opNorm_nonneg
        (𝕜 := ℝ) (𝕜₂ := ℝ) (E := StrongDual ℝ Y) (F := ℝ)
        (σ₁₂ := RingHom.id ℝ) (v - inclusionInDoubleDual ℝ Y (e : Y)), ?_⟩
    intro f
    have hfe : (f : StrongDual ℝ Y) (e : Y) = 0 :=
      (mem_polarSubmodule ℝ E (f : StrongDual ℝ Y)).mp f.property (e : Y) e.property
    have hvalue : (v - inclusionInDoubleDual ℝ Y (e : Y)) (f : StrongDual ℝ Y) = r f := by
      change v (f : StrongDual ℝ Y) - (f : StrongDual ℝ Y) (e : Y) = v (f : StrongDual ℝ Y)
      rw [hfe, sub_zero]
    rw [← hvalue]
    exact (v - inclusionInDoubleDual ℝ Y (e : Y)).le_opNorm (f : StrongDual ℝ Y)
  · obtain ⟨V, hV, hnorm⟩ := exists_extension_norm_eq A r
    have hvanish : ∀ f : polarSubmodule ℝ E, (v - V) (f : StrongDual ℝ Y) = 0 := by
      intro f
      change v (f : StrongDual ℝ Y) - V (f : StrongDual ℝ Y) = 0
      exact sub_eq_zero.mpr (hV f).symm
    obtain ⟨e, he⟩ := finite_double_annihilator E (v - V) hvanish
    have hsub : v - inclusionInDoubleDual ℝ Y (e : Y) = V := by
      rw [← he]
      abel
    calc
      Metric.infDist v (Set.range fun e : E => inclusionInDoubleDual ℝ Y (e : Y))
          ≤ dist v (inclusionInDoubleDual ℝ Y (e : Y)) :=
        Metric.infDist_le_dist_of_mem ⟨e, rfl⟩
      _ = ‖V‖ := by rw [dist_eq_norm v (inclusionInDoubleDual ℝ Y (e : Y)), hsub]
      _ = ‖r‖ := hnorm

theorem exists_annihilating_functional
    (E : Submodule ℝ Y) [FiniteDimensional ℝ E]
    (v : StrongDual ℝ (StrongDual ℝ Y)) {d : ℝ} (hd : 0 < d)
    (hgap : d < Metric.infDist v (Set.range (inclusionInDoubleDual ℝ Y))) :
    ∃ f : StrongDual ℝ Y,
      ‖f‖ ≤ 1 ∧ (∀ e : E, f (e : Y) = 0) ∧ v f = d := by
  classical
  let A := polarSubmodule ℝ E
  let r : StrongDual ℝ A := v.comp A.subtypeL
  have hsubset :
      (Set.range fun e : E => inclusionInDoubleDual ℝ Y (e : Y)) ⊆
        Set.range (inclusionInDoubleDual ℝ Y) := by
    rintro z ⟨e, rfl⟩
    exact ⟨(e : Y), rfl⟩
  have hnonempty :
      (Set.range fun e : E => inclusionInDoubleDual ℝ Y (e : Y)).Nonempty :=
    ⟨inclusionInDoubleDual ℝ Y (0 : Y), ⟨0, rfl⟩⟩
  have hr : d < ‖r‖ := by
    calc
      d < Metric.infDist v (Set.range (inclusionInDoubleDual ℝ Y)) := hgap
      _ ≤ Metric.infDist v
          (Set.range fun e : E => inclusionInDoubleDual ℝ Y (e : Y)) :=
        Metric.infDist_le_infDist_of_subset hsubset hnonempty
      _ = ‖r‖ := (restriction_norm_eq_infDist_finite_image E v).symm
  have hex : ∃ g : A, ‖g‖ = 1 ∧ d < ‖r g‖ := by
    by_contra h
    have hbound : ‖r‖ ≤ d :=
      ContinuousLinearMap.opNorm_le_of_unit_norm hd.le fun g hg =>
        le_of_not_gt fun hgt => h ⟨g, hg, hgt⟩
    exact (not_le_of_gt hr) hbound
  obtain ⟨g, hg, hvalue⟩ := hex
  have habs : d < |v (g : StrongDual ℝ Y)| := by
    change d < ‖v (g : StrongDual ℝ Y)‖ at hvalue
    simpa only [Real.norm_eq_abs] using hvalue
  have hvg : v (g : StrongDual ℝ Y) ≠ 0 := by
    intro hzero
    rw [hzero, abs_zero] at habs
    exact (not_lt_of_ge hd.le) habs
  refine ⟨(d / v (g : StrongDual ℝ Y)) • (g : StrongDual ℝ Y), ?_, ?_, ?_⟩
  · have hg' : ‖(g : StrongDual ℝ Y)‖ = 1 := hg
    rw [norm_smul (d / v (g : StrongDual ℝ Y)) (g : StrongDual ℝ Y),
      Real.norm_eq_abs, abs_div, abs_of_pos hd, hg', mul_one]
    apply (div_le_iff₀ (hd.trans habs)).mpr
    simpa only [one_mul] using habs.le
  · intro e
    have hge : (g : StrongDual ℝ Y) (e : Y) = 0 :=
      (mem_polarSubmodule ℝ E (g : StrongDual ℝ Y)).mp g.property (e : Y) e.property
    change (d / v (g : StrongDual ℝ Y)) * (g : StrongDual ℝ Y) (e : Y) = 0
    rw [hge, mul_zero]
  · rw [map_smul, smul_eq_mul]
    exact div_mul_cancel₀ d hvg

theorem exists_bidual_gap [CompleteSpace Y]
    (hNR : ¬ Function.Surjective (inclusionInDoubleDual ℝ Y)) :
    ∃ (v : StrongDual ℝ (StrongDual ℝ Y)) (d : ℝ),
      ‖v‖ ≤ 1 ∧ 0 < d ∧
      d < Metric.infDist v (Set.range (inclusionInDoubleDual ℝ Y)) := by
  classical
  let J := inclusionInDoubleDual ℝ Y
  obtain ⟨w, hw⟩ := not_forall.mp hNR
  have hw_range : w ∉ Set.range J := hw
  have hw0 : w ≠ 0 := by
    intro hzero
    apply hw_range
    exact ⟨0, by simp [J, hzero]⟩
  let v : StrongDual ℝ (StrongDual ℝ Y) := ‖w‖⁻¹ • w
  have hvnorm : ‖v‖ = 1 := by
    simpa only [v, RCLike.ofReal_real_eq_id, id_eq] using
      (norm_smul_inv_norm (𝕜 := ℝ) (x := w) hw0)
  have hv_range : v ∉ Set.range J := by
    rintro ⟨y, hy⟩
    apply hw_range
    refine ⟨‖w‖ • y, ?_⟩
    rw [map_smul, hy]
    dsimp only [v]
    have hcancel : ‖w‖ * ‖w‖⁻¹ = (1 : ℝ) :=
      mul_inv_cancel₀ ((norm_ne_zero_iff (a := w)).mpr hw0)
    rw [smul_smul, hcancel, one_smul]
  have hJ : Isometry J := (inclusionInDoubleDualLi ℝ (E := Y)).isometry
  have hclosed : IsClosed (Set.range J) :=
    hJ.isClosedEmbedding.isClosed_range
  have hnonempty : (Set.range J).Nonempty := ⟨J 0, ⟨0, rfl⟩⟩
  have hdist : 0 < Metric.infDist v (Set.range J) :=
    (hclosed.notMem_iff_infDist_pos hnonempty).mp hv_range
  exact ⟨v, Metric.infDist v (Set.range J) / 2, hvnorm.le,
    half_pos hdist, half_lt_self hdist⟩

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteChains
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

theorem pathWeight_nonneg {S : Type*} [Fintype S]
    (C : FiniteReversibleChain S) (n : ℕ) (ω : StatePath S n) :
    0 ≤ pathWeight C n ω := by
  exact mul_nonneg (C.π_nonneg _) (Finset.prod_nonneg fun i _ => C.P_nonneg _ _)

theorem stateCost_nonneg {S X : Type*} [Fintype S] [NormedAddCommGroup X]
    (C : FiniteReversibleChain S) (f : S → X) (p : ℝ) (n : ℕ) :
    0 ≤ stateCost C f p n := by
  exact Finset.sum_nonneg fun ω _ =>
    mul_nonneg (pathWeight_nonneg C n ω) (Real.rpow_nonneg (norm_nonneg _) _)

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteCoordinateSupport
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.OrderedNorm.instCoeFunForallC00Real _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

theorem finite_coordinate_factorization
    {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (S : E →ₗ[ℝ] C00) :
    ∃ m : ℕ, ∃ R : E →ₗ[ℝ] (Fin m → ℝ),
      ∀ z : E, C00.ofArray (R z) = S z := by
  classical
  let b := Module.finBasis ℝ E
  let t : Finset ℕ := Finset.univ.biUnion (fun i => (S (b i)).support)
  let m := (t.sup id).succ
  have hbzero (i : Fin (Module.finrank ℝ E)) (n : ℕ) (hn : m ≤ n) :
      S (b i) n = 0 := by
    apply Finsupp.notMem_support_iff.mp
    intro hmem
    have hnt : n ∈ t :=
      Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hmem⟩
    have hlt : n < m :=
      Finset.mem_range.mp (Finset.subset_range_sup_succ t hnt)
    exact (Nat.not_lt_of_ge hn) hlt
  have hzero (z : E) (n : ℕ) (hn : m ≤ n) : S z n = 0 := by
    have hmap : (Finsupp.lapply n : C00 →ₗ[ℝ] ℝ).comp S = 0 := by
      apply b.ext
      intro i
      change S (b i) n = 0
      exact hbzero i n hn
    have hz := congrArg (fun L : E →ₗ[ℝ] ℝ => L z) hmap
    exact hz
  let R : E →ₗ[ℝ] (Fin m → ℝ) :=
    LinearMap.pi (fun i : Fin m => (Finsupp.lapply i.val : C00 →ₗ[ℝ] ℝ).comp S)
  refine ⟨m, R, ?_⟩
  intro z
  change C00.ofArray (fun i : Fin m => S z i.val) = S z
  exact C00.ofArray_of_vanishes (S z) m (hzero z)

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteL2IsometryTransport
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

universe u v w
variable {E : Type u} {G : Type v} {Ω : Type w}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup G] [NormedSpace ℝ G] [sectionFintypeΩ : Fintype Ω]

omit sectionFintypeΩ in
@[simp] theorem finiteDifference_map [Fintype Ω] (T : E →ₗ[ℝ] G) (M : ℕ → Ω → E)
    (j : ℕ) (ω : Ω) :
    finiteDifference (fun n ω => T (M n ω)) j ω = T (finiteDifference M j ω) := by
  by_cases hj : j = 0
  · subst j
    rfl
  · simp only [finiteDifference, ite_eq_right hj, map_sub]

@[simp] theorem finiteL2Norm_linearIsometry (T : E →ₗᵢ[ℝ] G)
    (μ : FiniteLaw Ω) (f : Ω → E) :
    finiteL2Norm μ (fun ω => T (f ω)) = finiteL2Norm μ f := by
  simp only [finiteL2Norm, T.norm_map]

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteNormApproximation
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace MarkovSuperreflexivity

universe u v

variable {E : Type u} {X : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem eventually_norm_sub_le_of_pointwise
    (U : Filter ℕ) [U.NeBot] (T : ℕ → E →ₗ[ℝ] X)
    (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ n x, ‖T n x‖ ≤ K * ‖x‖)
    (hlim : ∀ x, Tendsto (fun n => ‖T n x‖) U (𝓝 ‖x‖))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in U, ∀ x, |‖T n x‖ - ‖x‖| ≤ ε * ‖x‖ := by
  have hK1 : 0 < K + 1 := by linarith
  let δ : ℝ := (K + 1)⁻¹ * (ε / 2)
  have hδ : 0 < δ := mul_pos (inv_pos.mpr hK1) (half_pos hε)
  have hδeq : (K + 1) * δ = ε / 2 := by
    dsimp only [δ]
    rw [← mul_assoc, mul_inv_cancel₀ hK1.ne', one_mul]
  obtain ⟨t, _htsub, htfin, hcover⟩ :=
    (isCompact_closedBall (0 : E) 1).finite_cover_balls hδ
  have hnet : ∀ᶠ n in U, ∀ y ∈ t, |‖T n y‖ - ‖y‖| < ε / 2 := by
    apply htfin.eventually_all.2
    intro y _hy
    simpa only [Real.dist_eq] using
      (Metric.tendsto_nhds.1 (hlim y) (ε / 2) (half_pos hε))
  have hball : ∀ᶠ n in U, ∀ v ∈ Metric.closedBall (0 : E) 1,
      |‖T n v‖ - ‖v‖| ≤ ε := by
    refine hnet.mono fun n hn v hv => ?_
    obtain ⟨y, hyt, hvy⟩ := Set.mem_iUnion₂.mp (hcover hv)
    have hdist : ‖v - y‖ ≤ δ := by
      have hlt : ‖v - y‖ < δ := by
        simpa only [dist_eq_norm] using (Metric.mem_ball.mp hvy)
      exact hlt.le
    have hTdist : |‖T n v‖ - ‖T n y‖| ≤ K * ‖v - y‖ := by
      calc
        |‖T n v‖ - ‖T n y‖| ≤ ‖T n v - T n y‖ := abs_norm_sub_norm_le _ _
        _ = ‖T n (v - y)‖ := by rw [map_sub]
        _ ≤ K * ‖v - y‖ := hbound n (v - y)
    have hnormdist : |‖y‖ - ‖v‖| ≤ ‖v - y‖ := by
      calc
        |‖y‖ - ‖v‖| ≤ ‖y - v‖ := abs_norm_sub_norm_le _ _
        _ = ‖v - y‖ := norm_sub_rev _ _
    calc
      |‖T n v‖ - ‖v‖| =
          |(‖T n v‖ - ‖T n y‖) + (‖T n y‖ - ‖y‖) + (‖y‖ - ‖v‖)| := by
        congr 1
        ring
      _ ≤ |(‖T n v‖ - ‖T n y‖) + (‖T n y‖ - ‖y‖)| + |‖y‖ - ‖v‖| :=
        abs_add_le _ _
      _ ≤ (|‖T n v‖ - ‖T n y‖| + |‖T n y‖ - ‖y‖|) + |‖y‖ - ‖v‖| :=
        add_le_add_left (abs_add_le _ _) _
      _ ≤ (K * ‖v - y‖ + ε / 2) + ‖v - y‖ :=
        add_le_add (add_le_add hTdist (hn y hyt).le) hnormdist
      _ ≤ (K * δ + ε / 2) + δ :=
        add_le_add (add_le_add_left (mul_le_mul_of_nonneg_left hdist hK) _) hdist
      _ = ε := by nlinarith [hδeq]
  refine hball.mono fun n hn x => ?_
  by_cases hx0 : x = 0
  · simp [hx0]
  have hx : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  let v : E := ‖x‖⁻¹ • x
  have hv : ‖v‖ = 1 := by
    simp only [v, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx),
      inv_mul_cancel₀ hx.ne']
  have hxv : ‖x‖ • v = x := by
    simp only [v, smul_smul, mul_inv_cancel₀ hx.ne', one_smul]
  have hvball : v ∈ Metric.closedBall (0 : E) 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right, hv] using (le_refl (1 : ℝ))
  have hvbound : |‖T n v‖ - 1| ≤ ε := by
    simpa only [hv] using hn v hvball
  have hscale : ‖T n x‖ = ‖x‖ * ‖T n v‖ := by
    calc
      ‖T n x‖ = ‖T n (‖x‖ • v)‖ := congrArg (fun z => ‖T n z‖) hxv.symm
      _ = ‖x‖ * ‖T n v‖ := by
        rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)]
  calc
    |‖T n x‖ - ‖x‖| = |‖x‖ * (‖T n v‖ - 1)| := by
      rw [hscale]
      congr 1
      ring
    _ = ‖x‖ * |‖T n v‖ - 1| := by
      rw [abs_mul, abs_of_nonneg (norm_nonneg x)]
    _ ≤ ‖x‖ * ε := mul_le_mul_of_nonneg_left hvbound hx.le
    _ = ε * ‖x‖ := mul_comm _ _

theorem exists_scaled_norm_bounds_of_pointwise
    (U : Filter ℕ) [U.NeBot] (T : ℕ → E →ₗ[ℝ] X)
    (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ n x, ‖T n x‖ ≤ K * ‖x‖)
    (hlim : ∀ x, Tendsto (fun n => ‖T n x‖) U (𝓝 ‖x‖))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ S : E →ₗ[ℝ] X, ∀ x,
      ‖x‖ ≤ ‖S x‖ ∧ ‖S x‖ ≤ ((1 + ε) / (1 - ε)) * ‖x‖ := by
  obtain ⟨n, hn⟩ :=
    (eventually_norm_sub_le_of_pointwise U T K hK hbound hlim hε).exists
  have hden : 0 < 1 - ε := sub_pos.mpr hε1
  let S : E →ₗ[ℝ] X := (1 - ε)⁻¹ • T n
  have hS (x : E) : ‖S x‖ = ‖T n x‖ / (1 - ε) := by
    change ‖(1 - ε)⁻¹ • T n x‖ = _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hden), div_eq_mul_inv]
    exact mul_comm _ _
  refine ⟨S, fun x => ?_⟩
  have hlo := (abs_le.mp (hn x)).1
  have hhi := (abs_le.mp (hn x)).2
  rw [hS x]
  constructor
  · apply (le_div_iff₀ hden).2
    nlinarith
  · calc
      ‖T n x‖ / (1 - ε) ≤ ((1 + ε) * ‖x‖) / (1 - ε) := by
        apply (div_le_div_iff_of_pos_right hden).2
        nlinarith
      _ = ((1 + ε) / (1 - ε)) * ‖x‖ := by ring

theorem exists_near_isometric_map_of_pointwise
    (U : Filter ℕ) [U.NeBot] (T : ℕ → E →ₗ[ℝ] X)
    (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ n x, ‖T n x‖ ≤ K * ‖x‖)
    (hlim : ∀ x, Tendsto (fun n => ‖T n x‖) U (𝓝 ‖x‖))
    {η : ℝ} (hη : 0 < η) :
    ∃ S : E →ₗ[ℝ] X, ∀ x, ‖x‖ ≤ ‖S x‖ ∧ ‖S x‖ ≤ (1 + η) * ‖x‖ := by
  let ε : ℝ := min (η / 4) (1 / 2)
  have hε : 0 < ε := lt_min (by linarith) (by linarith)
  have hεη : ε ≤ η / 4 := min_le_left _ _
  have hεhalf : ε ≤ 1 / 2 := min_le_right _ _
  have hε1 : ε < 1 := lt_of_le_of_lt hεhalf (by linarith)
  obtain ⟨S, hS⟩ :=
    exists_scaled_norm_bounds_of_pointwise U T K hK hbound hlim hε hε1
  have hratio : (1 + ε) / (1 - ε) ≤ 1 + η := by
    apply (div_le_iff₀ (sub_pos.mpr hε1)).2
    have hprod := mul_le_mul_of_nonneg_left hεhalf hη.le
    nlinarith
  exact ⟨S, fun x => ⟨(hS x).1,
    (hS x).2.trans (mul_le_mul_of_nonneg_right hratio (norm_nonneg x))⟩⟩

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FinitePaths
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

variable {S : Type*} [sectionFintypeS : Fintype S]

theorem sum_π_mul_P (C : FiniteReversibleChain S) (t : S) :
    ∑ s, C.π s * C.P s t = C.π t := by
  simp_rw [C.balance]
  rw [← Finset.mul_sum, C.sum_P, mul_one]

theorem balance_product (n : ℕ) (m : Fin (n + 1) → ℝ) (a b : Fin n → ℝ)
    (h : ∀ i, m i.castSucc * a i = m i.succ * b i) :
    m 0 * ∏ i, a i = m (Fin.last n) * ∏ i, b i := by
  induction n with
  | zero => simp
  | succ n ih =>
      have ht := ih (fun i => m i.succ) (fun i => a i.succ)
        (fun i => b i.succ) (fun i => by
          simpa only [Fin.succ_castSucc] using h i.succ)
      simp only [Fin.succ_last] at ht
      have h0 : m 0 * a 0 = m (Fin.succ 0) * b 0 := by
        simpa only [Fin.castSucc_zero] using h 0
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
      calc
        m 0 * (a 0 * ∏ i : Fin n, a i.succ) =
            (m 0 * a 0) * ∏ i : Fin n, a i.succ := by ring
        _ = (m (Fin.succ 0) * b 0) * ∏ i : Fin n, a i.succ := by rw [h0]
        _ = b 0 * (m (Fin.succ 0) * ∏ i : Fin n, a i.succ) := by ring
        _ = b 0 * (m (Fin.last (n + 1)) * ∏ i : Fin n, b i.succ) := by rw [ht]
        _ = m (Fin.last (n + 1)) * (b 0 * ∏ i : Fin n, b i.succ) := by ring

theorem pathWeight_reverse (C : FiniteReversibleChain S) (n : ℕ)
    (ω : StatePath S n) : pathWeight C n (pathReverse ω) = pathWeight C n ω := by
  have hp := Fin.rev_involutive.bijective.prod_comp
    (fun i : Fin n => C.P (ω i.succ) (ω i.castSucc))
  change (∏ i : Fin n, C.P (ω i.rev.succ) (ω i.rev.castSucc)) =
    ∏ i : Fin n, C.P (ω i.succ) (ω i.castSucc) at hp
  simp only [pathWeight, pathReverse, Fin.rev_zero, Fin.rev_castSucc, Fin.rev_succ]
  rw [hp]
  exact (balance_product n (fun i => C.π (ω i))
    (fun i => C.P (ω i.castSucc) (ω i.succ))
    (fun i => C.P (ω i.succ) (ω i.castSucc))
    (fun i => C.balance _ _)).symm

theorem pathWeight_snoc (C : FiniteReversibleChain S) (n : ℕ)
    (ω : StatePath S n) (t : S) :
    pathWeight C (n + 1) (Fin.snoc ω t) =
      pathWeight C n ω * C.P (ω (Fin.last n)) t := by
  unfold pathWeight
  rw [Fin.prod_univ_castSucc]
  have hz : (0 : Fin (n + 1 + 1)) = (0 : Fin (n + 1)).castSucc := rfl
  simp only [hz, Fin.succ_castSucc, Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last]
  ring

section VectorExpectations

variable {V : Type*} [AddCommMonoid V] [Module ℝ V]

theorem sum_pathWeight_snoc_v (C : FiniteReversibleChain S) (n : ℕ)
    (F : StatePath S (n + 1) → V) :
    (∑ ω, pathWeight C (n + 1) ω • F ω) =
      ∑ η : StatePath S n, ∑ t : S,
        (pathWeight C n η * C.P (η (Fin.last n)) t) • F (Fin.snoc η t) := by
  classical
  rw [← (Fin.snocEquiv (fun _ : Fin (n + 1 + 1) => S)).sum_comp
    (fun ω => pathWeight C (n + 1) ω • F ω)]
  change (∑ z : S × StatePath S n,
    pathWeight C (n + 1) (Fin.snoc z.2 z.1) • F (Fin.snoc z.2 z.1)) = _
  simp only [Fintype.sum_prod_type, pathWeight_snoc]
  exact Finset.sum_comm

theorem sum_pathWeight_reverse_v (C : FiniteReversibleChain S) (n : ℕ)
    (F : StatePath S n → V) :
    (∑ ω, pathWeight C n ω • F (pathReverse ω)) =
      ∑ ω, pathWeight C n ω • F ω := by
  have h := (pathReverseEquiv (S := S) n).sum_comp
    (fun ω => pathWeight C n ω • F ω)
  change (∑ ω, pathWeight C n (pathReverse ω) • F (pathReverse ω)) = _ at h
  simpa only [pathWeight_reverse] using h

end VectorExpectations

theorem sum_pathWeight_snoc (C : FiniteReversibleChain S) (n : ℕ)
    (F : StatePath S (n + 1) → ℝ) :
    (∑ ω, pathWeight C (n + 1) ω * F ω) =
      ∑ η : StatePath S n, ∑ t : S,
        (pathWeight C n η * C.P (η (Fin.last n)) t) * F (Fin.snoc η t) :=
  sum_pathWeight_snoc_v C n F

section PrefixExpectations

variable {V : Type*} [AddCommMonoid V] [Module ℝ V]

theorem sum_pathWeight_take_v (C : FiniteReversibleChain S) {n : ℕ}
    (k : ℕ) (hk : k ≤ n) (H : StatePath S k → V) :
    (∑ ω : StatePath S n, pathWeight C n ω • H (pathTake k hk ω)) =
      ∑ η : StatePath S k, pathWeight C k η • H η := by
  classical
  induction n generalizing k with
  | zero =>
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      simp
  | succ n ih =>
      by_cases hkn : k ≤ n
      · rw [sum_pathWeight_snoc_v]
        simp only [pathTake_snoc k hkn, mul_smul]
        simp only [← Finset.smul_sum, ← Finset.sum_smul, C.sum_P, one_smul]
        exact ih k hkn H
      · have hnk : n + 1 ≤ k := Nat.succ_le_of_lt (Nat.lt_of_not_ge hkn)
        have hk' : k = n + 1 := Nat.le_antisymm hk hnk
        subst k
        simp

end PrefixExpectations

theorem sum_pathWeight_take (C : FiniteReversibleChain S) {n : ℕ}
    (k : ℕ) (hk : k ≤ n) (H : StatePath S k → ℝ) :
    (∑ ω : StatePath S n, pathWeight C n ω * H (pathTake k hk ω)) =
      ∑ η : StatePath S k, pathWeight C k η * H η :=
  sum_pathWeight_take_v C k hk H

theorem sum_pathWeight_last (C : FiniteReversibleChain S) (n : ℕ) (H : S → ℝ) :
    (∑ ω : StatePath S n, pathWeight C n ω * H (ω (Fin.last n))) =
      ∑ s, C.π s * H s := by
  classical
  induction n generalizing H with
  | zero =>
      let e : S ≃ StatePath S 0 :=
        { toFun := fun s _ => s
          invFun := fun ω => ω 0
          left_inv := fun _ => rfl
          right_inv := fun ω => funext fun i => congrArg ω (Fin.subsingleton_one.elim _ _) }
      rw [← e.sum_comp (fun ω => pathWeight C 0 ω * H (ω (Fin.last 0)))]
      simp [e, pathWeight]
  | succ n ih =>
      rw [sum_pathWeight_snoc]
      simp only [Fin.snoc_last, mul_assoc]
      simp_rw [← Finset.mul_sum]
      rw [ih (fun s => ∑ t, C.P s t * H t)]
      simp_rw [Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, sum_π_mul_P]

theorem sum_pathWeight_last_pair (C : FiniteReversibleChain S) (n : ℕ)
    (H : S → S → ℝ) :
    (∑ ω : StatePath S (n + 1), pathWeight C (n + 1) ω *
      H (ω (Fin.last n).castSucc) (ω (Fin.last (n + 1)))) =
      ∑ s, ∑ t, (C.π s * C.P s t) * H s t := by
  classical
  rw [sum_pathWeight_snoc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, mul_assoc]
  simp_rw [← Finset.mul_sum]
  exact sum_pathWeight_last C n (fun s => ∑ t, C.P s t * H s t)

theorem sum_pathWeight_pair (C : FiniteReversibleChain S) {n : ℕ}
    (r : ℕ) (hr : r < n) (H : S → S → ℝ) :
    (∑ ω : StatePath S n, pathWeight C n ω *
      H (ω (⟨r, hr⟩ : Fin n).castSucc) (ω (⟨r, hr⟩ : Fin n).succ)) =
      ∑ s, ∑ t, (C.π s * C.P s t) * H s t := by
  have hk : r + 1 ≤ n := Nat.succ_le_of_lt hr
  calc
    _ = ∑ ω : StatePath S n, pathWeight C n ω *
        (fun η : StatePath S (r + 1) =>
          H (η (Fin.last r).castSucc) (η (Fin.last (r + 1))))
          (pathTake (r + 1) hk ω) := by rfl
    _ = ∑ η : StatePath S (r + 1), pathWeight C (r + 1) η *
        H (η (Fin.last r).castSucc) (η (Fin.last (r + 1))) :=
      sum_pathWeight_take C (r + 1) hk
        (fun η : StatePath S (r + 1) => H (η (Fin.last r).castSucc) (η (Fin.last (r + 1))))
    _ = _ := sum_pathWeight_last_pair C r H

theorem stateCost_one {X : Type*} [NormedAddCommGroup X]
    (C : FiniteReversibleChain S) (f : S → X) (p : ℝ) :
    stateCost C f p 1 =
      ∑ s, ∑ t, (C.π s * C.P s t) * Real.rpow (‖f t - f s‖) p := by
  simpa only [stateCost, Fin.last_zero, Fin.castSucc_zero] using
    sum_pathWeight_last_pair C 0 (fun s t => Real.rpow (‖f t - f s‖) p)

theorem sum_pathWeight_take_next {V : Type*} [AddCommMonoid V] [Module ℝ V]
    (C : FiniteReversibleChain S) {n : ℕ} (k : ℕ) (hk : k < n)
    (η : StatePath S k) (H : S → V) :
    (∑ ω : StatePath S n,
      if pathTake k (Nat.le_of_lt hk) ω = η then
        pathWeight C n ω • H (ω ⟨k + 1, Nat.succ_lt_succ hk⟩)
      else 0) =
      pathWeight C k η • ∑ t, C.P (η (Fin.last k)) t • H t := by
  classical
  have hk1 : k + 1 ≤ n := Nat.succ_le_of_lt hk
  let F : StatePath S (k + 1) → V := fun ζ =>
    if Fin.init ζ = η then H (ζ (Fin.last (k + 1))) else 0
  calc
    _ = ∑ ω : StatePath S n, pathWeight C n ω • F (pathTake (k + 1) hk1 ω) := by
      apply Finset.sum_congr rfl
      intro ω _
      have hi : Fin.init (pathTake (k + 1) hk1 ω) =
          pathTake k (Nat.le_of_lt hk) ω := by funext i; rfl
      have hl : pathTake (k + 1) hk1 ω (Fin.last (k + 1)) =
          ω ⟨k + 1, Nat.succ_lt_succ hk⟩ := rfl
      simp only [F, hi, hl, smul_ite, smul_zero]
    _ = ∑ ζ : StatePath S (k + 1), pathWeight C (k + 1) ζ • F ζ :=
      sum_pathWeight_take_v C (k + 1) hk1 F
    _ = _ := by
      rw [sum_pathWeight_snoc_v]
      simp only [F, Fin.init_snoc, Fin.snoc_last]
      have hf (ζ : StatePath S k) :
          (∑ t, (pathWeight C k ζ * C.P (ζ (Fin.last k)) t) •
            (if ζ = η then H t else 0)) =
          if ζ = η then pathWeight C k ζ • ∑ t, C.P (ζ (Fin.last k)) t • H t
          else 0 := by
        by_cases hζη : ζ = η
        · simp only [hζη, ite_true, mul_smul, ← Finset.smul_sum]
        · simp only [hζη, ite_false, smul_zero, Finset.sum_const_zero]
      simp_rw [hf]
      simp

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteRamsey
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

open scoped BigOperators

theorem finite_ramsey_targets.{u, v} {κ : Type v} [Fintype κ] [Nonempty κ]
    (r : ℕ) (targets : κ → ℕ) :
    ∃ B : ℕ, FiniteRamseyBound.{u, v} r targets B := by
  classical
  induction r generalizing targets with
  | zero =>
      refine ⟨Finset.univ.sup targets, ?_⟩
      intro α _ S hS χ
      let i : κ := χ ∅
      have hi : targets i ≤ S.card :=
        (Finset.le_sup (Finset.mem_univ i)).trans hS
      obtain ⟨H, hHS, hHcard⟩ := Finset.exists_subset_card_eq hi
      refine ⟨i, H, hHS, hHcard, ?_⟩
      intro A _ hA
      have hAempty : A = ∅ := Finset.card_eq_zero.mp hA
      subst A
      rfl
  | succ r ih =>
      have by_sum : ∀ n : ℕ, ∀ w : κ → ℕ, (∑ i, w i) = n →
          ∃ B : ℕ, FiniteRamseyBound.{u, v} (r + 1) w B := by
        intro n
        induction n using Nat.strong_induction_on with
        | h n hn =>
            intro w hsum
            by_cases hz : ∃ i, w i = 0
            · obtain ⟨i, hi⟩ := hz
              refine ⟨0, ?_⟩
              intro α _ S _ χ
              refine ⟨i, ∅, Finset.empty_subset S, ?_, ?_⟩
              · simpa only [Finset.card_empty] using hi.symm
              · intro A hA hcard
                have hAempty : A = ∅ := Finset.subset_empty.mp hA
                subst A
                simp at hcard
            · have hpos : ∀ i, 0 < w i := by
                intro i
                exact Nat.pos_of_ne_zero (fun hi => hz ⟨i, hi⟩)
              have hsmall : ∀ i : κ,
                  ∃ B : ℕ, FiniteRamseyBound.{u, v} (r + 1)
                    (decreaseRamseyTarget w i) B := by
                intro i
                have hlt : (∑ j, decreaseRamseyTarget w i j) < n := by
                  rw [← hsum]
                  apply Finset.sum_lt_sum
                  · intro j _
                    by_cases hji : j = i
                    · simpa only [decreaseRamseyTarget, ite_eq_left hji] using
                        (Nat.sub_le (w j) 1)
                    · simpa only [decreaseRamseyTarget, ite_eq_right hji] using
                        (le_rfl : w j ≤ w j)
                  · refine ⟨i, Finset.mem_univ i, ?_⟩
                    simp only [decreaseRamseyTarget]
                    exact Nat.sub_lt (hpos i) (by decide)
                exact hn _ hlt _ rfl
              let N : κ → ℕ := fun i => Classical.choose (hsmall i)
              have hN : ∀ i : κ, FiniteRamseyBound.{u, v} (r + 1)
                  (decreaseRamseyTarget w i) (N i) := by
                intro i
                exact Classical.choose_spec (hsmall i)
              obtain ⟨D, hD⟩ := ih N
              refine ⟨D + 1, ?_⟩
              intro α _ S hS χ
              have hSnonempty : S.Nonempty := Finset.card_pos.mp (by omega)
              obtain ⟨x, hxS⟩ := hSnonempty
              have htail : D ≤ (S.erase x).card := by
                rw [Finset.card_erase_of_mem hxS]
                omega
              obtain ⟨i, H, hHS, hHcard, hHmono⟩ :=
                hD α (S.erase x) htail (fun A => χ (insert x A))
              obtain ⟨j, G, hGH, hGcard, hGmono⟩ :=
                hN i α H hHcard.ge χ
              by_cases hji : j = i
              · subst j
                have hxH : x ∉ H := by
                  intro hx
                  exact (Finset.mem_erase.mp (hHS hx)).1 rfl
                have hxG : x ∉ G := fun hx => hxH (hGH hx)
                refine ⟨i, insert x G, ?_, ?_, ?_⟩
                · apply Finset.insert_subset_iff.mpr
                  refine ⟨hxS, ?_⟩
                  exact hGH.trans (hHS.trans (Finset.erase_subset x S))
                · rw [Finset.card_insert_of_notMem hxG, hGcard]
                  simp only [decreaseRamseyTarget]
                  exact Nat.sub_add_cancel (hpos i)
                · intro A hA hcard
                  by_cases hxA : x ∈ A
                  · have herase : A.erase x ⊆ G := by
                      intro a ha
                      obtain ⟨hax, haA⟩ := Finset.mem_erase.mp ha
                      rcases Finset.mem_insert.mp (hA haA) with haeq | haG
                      · exact False.elim (hax haeq)
                      · exact haG
                    have heraseCard : (A.erase x).card = r := by
                      rw [Finset.card_erase_of_mem hxA, hcard]
                      exact Nat.add_sub_cancel r 1
                    have hcolor := hHmono (A.erase x) (herase.trans hGH) heraseCard
                    simpa only [Finset.insert_erase hxA] using hcolor
                  · apply hGmono A _ hcard
                    intro a ha
                    rcases Finset.mem_insert.mp (hA ha) with haeq | haG
                    · exact False.elim (hxA (haeq ▸ ha))
                    · exact haG
              · refine ⟨j, G, ?_, ?_, hGmono⟩
                · exact hGH.trans (hHS.trans (Finset.erase_subset x S))
                · simpa only [decreaseRamseyTarget, ite_eq_right hji] using hGcard
      exact by_sum (∑ i, targets i) targets rfl

theorem finite_ramsey_uniform_subsets.{u} (r colors target : ℕ) (hcolors : 0 < colors) :
    ∃ B : ℕ, target ≤ B ∧
      ∀ (α : Type u) [DecidableEq α] (S : Finset α), B ≤ S.card →
        ∀ χ : Finset α → Fin colors,
          ∃ H : Finset α, H ⊆ S ∧ H.card = target ∧
            ∀ A : Finset α, A ⊆ H → A.card = r →
              ∀ D : Finset α, D ⊆ H → D.card = r → χ A = χ D := by
  classical
  let : Nonempty (Fin colors) := ⟨⟨0, hcolors⟩⟩
  obtain ⟨B, hB⟩ := finite_ramsey_targets.{u, 0} r (fun _ : Fin colors => target)
  refine ⟨max target B, le_max_left _ _, ?_⟩
  intro α _ S hS χ
  obtain ⟨i, H, hHS, hHcard, hHmono⟩ :=
    hB α S ((le_max_right target B).trans hS) χ
  refine ⟨H, hHS, hHcard, ?_⟩
  intro A hA hAcard D hD hDcard
  exact (hHmono A hA hAcard).trans (hHmono D hD hDcard).symm

theorem finite_ramsey_simultaneous_subsets.{u}
    (q target : ℕ) (colors : Fin q → ℕ) (hcolors : ∀ m, 0 < colors m) :
    ∃ B : ℕ, target ≤ B ∧
      ∀ (α : Type u) [DecidableEq α] (S : Finset α), B ≤ S.card →
        ∀ χ : (m : Fin q) → Finset α → Fin (colors m),
          ∃ H : Finset α, H ⊆ S ∧ H.card = target ∧
            ∀ (m : Fin q) (A : Finset α), A ⊆ H → A.card = m.val →
              ∀ D : Finset α, D ⊆ H → D.card = m.val → χ m A = χ m D := by
  classical
  induction q generalizing target with
  | zero =>
      refine ⟨target, le_rfl, ?_⟩
      intro α _ S hS χ
      obtain ⟨H, hHS, hHcard⟩ := Finset.exists_subset_card_eq hS
      refine ⟨H, hHS, hHcard, ?_⟩
      intro m
      exact Fin.elim0 m
  | succ q ih =>
      obtain ⟨M, hMtarget, hM⟩ :=
        finite_ramsey_uniform_subsets.{u} q (colors (Fin.last q)) target
          (hcolors (Fin.last q))
      obtain ⟨B, hBM, hB⟩ :=
        ih M (fun m => colors m.castSucc) (fun m => hcolors m.castSucc)
      refine ⟨B, hMtarget.trans hBM, ?_⟩
      intro α _ S hS χ
      obtain ⟨H, hHS, hHcard, hHmono⟩ :=
        hB α S hS (fun m => χ m.castSucc)
      obtain ⟨G, hGH, hGcard, hGmono⟩ :=
        hM α H hHcard.ge (χ (Fin.last q))
      refine ⟨G, hGH.trans hHS, hGcard, ?_⟩
      intro m
      rcases Fin.eq_castSucc_or_eq_last m with ⟨m, rfl⟩ | rfl
      · intro A hA hAcard D hD hDcard
        exact hHmono m A (hA.trans hGH) hAcard D (hD.trans hGH) hDcard
      · intro A hA hAcard D hD hDcard
        exact hGmono A hA hAcard D hD hDcard

theorem finite_ordered_simultaneous_ramsey
    (k lower : ℕ)
    (colors : Fin (k + 1) → ℕ)
    (hcolors : ∀ m, 0 < colors m) :
    ∃ B : ℕ, max k lower ≤ B ∧
      ∀ χ : (m : Fin (k + 1)) →
          (Fin m.val ↪o Fin B) → Fin (colors m),
        ∃ e : Fin k ↪o Fin B,
          ∀ (m : Fin (k + 1))
            (s t : Fin m.val ↪o Fin k),
            χ m (s.trans e) = χ m (t.trans e) := by
  classical
  obtain ⟨B₀, hB₀k, hB₀⟩ :=
    finite_ramsey_simultaneous_subsets.{0} (k + 1) k colors hcolors
  let B := max B₀ lower
  have hBB₀ : B₀ ≤ B := le_max_left _ _
  have hBlower : lower ≤ B := le_max_right _ _
  refine ⟨B, max_le (hB₀k.trans hBB₀) hBlower, ?_⟩
  intro χ
  let χset : (m : Fin (k + 1)) → Finset (Fin B) → Fin (colors m) :=
    fun m A => if hA : A.card = m.val then χ m (A.orderEmbOfFin hA)
      else ⟨0, hcolors m⟩
  have hlarge : B₀ ≤ (Finset.univ : Finset (Fin B)).card := by
    simpa only [Finset.card_univ, Fintype.card_fin] using hBB₀
  obtain ⟨H, _, hHcard, hHmono⟩ := hB₀ (Fin B) Finset.univ hlarge χset
  let e : Fin k ↪o Fin B := H.orderEmbOfFin hHcard
  refine ⟨e, ?_⟩
  intro m s t
  let A : Finset (Fin B) := Finset.univ.map (s.trans e).toEmbedding
  let D : Finset (Fin B) := Finset.univ.map (t.trans e).toEmbedding
  have hAcard : A.card = m.val := by
    simp only [A, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have hDcard : D.card = m.val := by
    simp only [D, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have hAH : A ⊆ H := by
    intro x hx
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hx
    exact H.orderEmbOfFin_mem hHcard (s a)
  have hDH : D ⊆ H := by
    intro x hx
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hx
    exact H.orderEmbOfFin_mem hHcard (t a)
  have hAenum : A.orderEmbOfFin hAcard = s.trans e := by
    symm
    apply Finset.orderEmbOfFin_unique'
    intro a
    exact Finset.mem_map.mpr ⟨a, Finset.mem_univ a, rfl⟩
  have hDenum : D.orderEmbOfFin hDcard = t.trans e := by
    symm
    apply Finset.orderEmbOfFin_unique'
    intro a
    exact Finset.mem_map.mpr ⟨a, Finset.mem_univ a, rfl⟩
  have hcolor := hHmono m A hAH hAcard D hDH hDcard
  simpa only [χset, dite_eq_left hAcard, dite_eq_left hDcard, hAenum, hDenum] using hcolor

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteRepresentation
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

theorem finitelyRepresentable_completion_of_coordinates
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (p : Seminorm ℝ C00) (hp : ∀ a, p a = 0 → a = 0)
    (hcoord : ∀ (m : ℕ) (ε : ℝ), 0 < ε →
      ∃ T : (Fin m → ℝ) →ₗ[ℝ] X, ∀ a,
        p (C00.ofArray a) ≤ ‖T a‖ ∧
        ‖T a‖ ≤ (1 + ε) * p (C00.ofArray a)) :
    FinitelyRepresentable (UniformSpace.Completion (NormedC00 p hp)) X := by
  intro V hV η hη
  let δ : ℝ := min (η / 8) (1 / 2)
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hδhalf : δ ≤ 1 / 2 := min_le_right _ _
  have hδη : δ ≤ η / 8 := min_le_left _ _
  have hden : 0 < 1 - δ := by linarith
  have hinv : 0 < (1 - δ)⁻¹ := inv_pos.mpr hden
  have hraw : (1 + δ) * (1 + δ) ≤ (1 + η) * (1 - δ) := by
    have hsquare : δ * δ ≤ δ := by
      have := mul_le_mul_of_nonneg_left (show δ ≤ 1 by linarith) hδ.le
      nlinarith
    have hηδ := mul_le_mul_of_nonneg_left hδhalf hη.le
    nlinarith
  have hfactor : (1 - δ)⁻¹ * ((1 + δ) * (1 + δ)) ≤ 1 + η := by
    have h := (div_le_iff₀ hden).mpr hraw
    simpa only [div_eq_mul_inv, mul_comm] using h
  let ι : NormedC00 p hp →ₗᵢ[ℝ] UniformSpace.Completion (NormedC00 p hp) :=
    UniformSpace.Completion.toComplₗᵢ
  have hdense : DenseRange ι := UniformSpace.Completion.denseRange_coe
  obtain ⟨S, hS⟩ := exists_linearMap_approx_subtype ι hdense V δ hδ
  have hSnorm (z : V) :
      (1 - δ) * ‖z‖ ≤ ‖S z‖ ∧ ‖S z‖ ≤ (1 + δ) * ‖z‖ := by
    have habs : |‖S z‖ - ‖z‖| ≤ δ * ‖z‖ := by
      simpa only [ι.norm_map, Submodule.norm_coe] using
        (abs_norm_sub_norm_le (ι (S z))
          (z : UniformSpace.Completion (NormedC00 p hp))).trans (hS z)
    obtain ⟨hl, hu⟩ := abs_le.mp habs
    constructor <;> nlinarith
  obtain ⟨m, R, hR⟩ := finite_coordinate_factorization
    ((NormedC00.coefficients p hp).toLinearMap.comp S)
  have hRnorm (z : V) : p (C00.ofArray (R z)) = ‖S z‖ := by
    rw [hR z]
    rfl
  obtain ⟨T, hT⟩ := hcoord m δ hδ
  let U : V →ₗ[ℝ] X := T.comp R
  have hUnorm (z : V) : (1 - δ) * ‖z‖ ≤ ‖U z‖ ∧
      ‖U z‖ ≤ ((1 + δ) * (1 + δ)) * ‖z‖ := by
    constructor
    · calc
        (1 - δ) * ‖z‖ ≤ ‖S z‖ := (hSnorm z).1
        _ = p (C00.ofArray (R z)) := (hRnorm z).symm
        _ ≤ ‖U z‖ := (hT (R z)).1
    · calc
        ‖U z‖ ≤ (1 + δ) * p (C00.ofArray (R z)) := (hT (R z)).2
        _ = (1 + δ) * ‖S z‖ := by rw [hRnorm z]
        _ ≤ (1 + δ) * ((1 + δ) * ‖z‖) :=
          mul_le_mul_of_nonneg_left (hSnorm z).2 (by linarith)
        _ = ((1 + δ) * (1 + δ)) * ‖z‖ := (mul_assoc _ _ _).symm
  refine ⟨(1 - δ)⁻¹ • U, ?_⟩
  intro z
  have hscaled : ‖((1 - δ)⁻¹ • U) z‖ = (1 - δ)⁻¹ * ‖U z‖ := by
    simp only [LinearMap.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos hinv]
  constructor
  · rw [hscaled]
    calc
      ‖z‖ = (1 - δ)⁻¹ * ((1 - δ) * ‖z‖) := by
        rw [← mul_assoc, inv_mul_cancel₀ hden.ne', one_mul]
      _ ≤ (1 - δ)⁻¹ * ‖U z‖ :=
        mul_le_mul_of_nonneg_left (hUnorm z).1 hinv.le
  · rw [hscaled]
    calc
      (1 - δ)⁻¹ * ‖U z‖ ≤ (1 - δ)⁻¹ * (((1 + δ) * (1 + δ)) * ‖z‖) :=
        mul_le_mul_of_nonneg_left (hUnorm z).2 hinv.le
      _ = ((1 - δ)⁻¹ * ((1 + δ) * (1 + δ))) * ‖z‖ :=
        (mul_assoc _ _ _).symm
      _ ≤ (1 + η) * ‖z‖ := mul_le_mul_of_nonneg_right hfactor (norm_nonneg z)

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteSmoothMoments
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {X : Type*} [NormedAddCommGroup X] [sectionNormedSpaceℝX : NormedSpace ℝ X]
variable {q D : ℝ}

theorem norm_rpow_sum_smul_le {ι : Type*} (s : Finset ι)
    (p : ι → ℝ) (z : ι → X) (hp : ∀ i ∈ s, 0 ≤ p i)
    (hsum : ∑ i ∈ s, p i = 1) (hq : 1 ≤ q) :
    ‖∑ i ∈ s, p i • z i‖ ^ q ≤ ∑ i ∈ s, p i * ‖z i‖ ^ q := by
  have hn : ‖∑ i ∈ s, p i • z i‖ ≤ ∑ i ∈ s, p i * ‖z i‖ := by
    calc
      _ ≤ ∑ i ∈ s, ‖p i • z i‖ := norm_sum_le _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [norm_smul, Real.norm_of_nonneg (hp i hi)]
  exact (Real.rpow_le_rpow (norm_nonneg _) hn (by linarith)).trans
    (Real.rpow_arith_mean_le_arith_mean_rpow s p (fun i => ‖z i‖)
      hp hsum (fun i _ => norm_nonneg _) hq)

theorem finite_norm_rpow_jensen {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (z : ι → X) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (hq : 1 ≤ q) :
    ‖∑ i, p i • z i‖ ^ q ≤ ∑ i, p i * ‖z i‖ ^ q :=
  norm_rpow_sum_smul_le Finset.univ p z (fun i _ => hp i) hsum hq

omit sectionNormedSpaceℝX in
theorem norm_add_rpow_le_two [NormedSpace ℝ X] (hq : 1 ≤ q) (hq2 : q ≤ 2) (x y : X) :
    ‖x + y‖ ^ q ≤ 2 * (‖x‖ ^ q + ‖y‖ ^ q) := by
  have hm : ((1 / 2 : ℝ) * ‖x‖ + (1 / 2 : ℝ) * ‖y‖) ^ q ≤
      (1 / 2 : ℝ) * ‖x‖ ^ q + (1 / 2 : ℝ) * ‖y‖ ^ q := by
    exact (convexOn_rpow hq).2 (norm_nonneg x) (norm_nonneg y)
      (by norm_num) (by norm_num) (by norm_num)
  have hmid : 0 ≤ (1 / 2 : ℝ) * ‖x‖ + (1 / 2 : ℝ) * ‖y‖ := by positivity
  have htwo : (2 : ℝ) ^ q ≤ 4 := by
    calc
      _ ≤ (2 : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hq2
      _ = 4 := by norm_num [Real.rpow_two]
  calc
    _ ≤ (‖x‖ + ‖y‖) ^ q :=
      Real.rpow_le_rpow (norm_nonneg _) (norm_add_le _ _) (by linarith)
    _ = (2 : ℝ) ^ q * ((1 / 2 : ℝ) * ‖x‖ + (1 / 2 : ℝ) * ‖y‖) ^ q := by
      rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hmid]
      congr 1
      ring
    _ ≤ 4 * ((1 / 2 : ℝ) * ‖x‖ + (1 / 2 : ℝ) * ‖y‖) ^ q :=
      mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hmid _)
    _ ≤ 4 * ((1 / 2 : ℝ) * ‖x‖ ^ q + (1 / 2 : ℝ) * ‖y‖ ^ q) :=
      mul_le_mul_of_nonneg_left hm (by norm_num)
    _ = _ := by ring

theorem norm_sub_rpow_le_two (hq : 1 ≤ q) (hq2 : q ≤ 2) (x y : X) :
    ‖x - y‖ ^ q ≤ 2 * (‖x‖ ^ q + ‖y‖ ^ q) := by
  simpa only [sub_eq_add_neg, norm_neg] using norm_add_rpow_le_two hq hq2 x (-y)

private theorem double_weighted_left {ι : Type*} (s : Finset ι)
    (p f : ι → ℝ) (hsum : ∑ i ∈ s, p i = 1) :
    (∑ i ∈ s, ∑ j ∈ s, (p i * p j) * f i) = ∑ i ∈ s, p i * f i := by
  calc
    _ = ∑ i ∈ s, (p i * f i) * (∑ j ∈ s, p j) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by simp only [hsum, mul_one]

private theorem double_weighted_right {ι : Type*} (s : Finset ι)
    (p f : ι → ℝ) (hsum : ∑ i ∈ s, p i = 1) :
    (∑ i ∈ s, ∑ j ∈ s, (p i * p j) * f j) = ∑ i ∈ s, p i * f i := by
  rw [Finset.sum_comm]
  calc
    _ = ∑ i ∈ s, ∑ j ∈ s, (p i * p j) * f i := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := double_weighted_left s p f hsum

theorem centered_q_moment_four {ι : Type*} (s : Finset ι)
    (hq : 1 ≤ q) (hq2 : q ≤ 2) (hD : 0 ≤ D)
    (hsmooth : SymmetricPowerSmoothWith q D X)
    (p : ι → ℝ) (y : ι → X) (hp : ∀ i ∈ s, 0 ≤ p i)
    (hsum : ∑ i ∈ s, p i = 1) (hzero : ∑ i ∈ s, p i • y i = 0) (x : X) :
    (∑ i ∈ s, p i * ‖x + y i‖ ^ q) ≤
      ‖x‖ ^ q + (4 * D) * ∑ i ∈ s, p i * ‖y i‖ ^ q := by
  let A := ∑ i ∈ s, ∑ j ∈ s, (p i * p j) * ‖x + (y i - y j)‖ ^ q
  let B := ∑ i ∈ s, ∑ j ∈ s, (p i * p j) * ‖x - (y i - y j)‖ ^ q
  let R := ∑ i ∈ s, ∑ j ∈ s, (p i * p j) * ‖y i - y j‖ ^ q
  have hmean (i : ι) : (∑ j ∈ s, p j • (x + (y i - y j))) = x + y i := by
    simp_rw [smul_add, smul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [← Finset.sum_smul, ← Finset.sum_smul, hsum, hzero]
    simp
  have hHA : (∑ i ∈ s, p i * ‖x + y i‖ ^ q) ≤ A := by
    calc
      _ ≤ ∑ i ∈ s, p i * (∑ j ∈ s, p j * ‖x + (y i - y j)‖ ^ q) := by
        apply Finset.sum_le_sum
        intro i hi
        have h := norm_rpow_sum_smul_le s p (fun j => x + (y i - y j)) hp hsum hq
        rw [hmean i] at h
        exact mul_le_mul_of_nonneg_left h (hp i hi)
      _ = A := by simp only [A, Finset.mul_sum, mul_assoc]
  have hAB : A = B := by
    dsimp [A, B]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    have he : x + (y j - y i) = x - (y i - y j) := by abel
    rw [he, mul_comm (p j) (p i)]
  have htotal : (∑ i ∈ s, ∑ j ∈ s, p i * p j) = 1 := by
    calc
      _ = ∑ i ∈ s, p i := by
        simpa only [mul_one] using double_weighted_left s p (fun _ => 1) hsum
      _ = 1 := hsum
  have hsm : A + B ≤ 2 * ‖x‖ ^ q + (2 * D) * R := by
    calc
      A + B = ∑ i ∈ s, ∑ j ∈ s, (p i * p j) *
          (‖x + (y i - y j)‖ ^ q + ‖x - (y i - y j)‖ ^ q) := by
        simp only [A, B, mul_add, Finset.sum_add_distrib]
      _ ≤ ∑ i ∈ s, ∑ j ∈ s, (p i * p j) *
          (2 * ‖x‖ ^ q + 2 * D * ‖y i - y j‖ ^ q) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (hsmooth x (y i - y j))
          (mul_nonneg (hp i hi) (hp j hj))
      _ = (∑ i ∈ s, ∑ j ∈ s, p i * p j) * (2 * ‖x‖ ^ q) + (2 * D) * R := by
        simp only [R, mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by rw [htotal, one_mul]
  have hR : R ≤ 4 * ∑ i ∈ s, p i * ‖y i‖ ^ q := by
    calc
      R ≤ ∑ i ∈ s, ∑ j ∈ s, (p i * p j) * (2 * (‖y i‖ ^ q + ‖y j‖ ^ q)) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (norm_sub_rpow_le_two hq hq2 (y i) (y j))
          (mul_nonneg (hp i hi) (hp j hj))
      _ = 2 * ((∑ i ∈ s, ∑ j ∈ s, (p i * p j) * ‖y i‖ ^ q) +
          ∑ i ∈ s, ∑ j ∈ s, (p i * p j) * ‖y j‖ ^ q) := by
        rw [← Finset.sum_add_distrib]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [← Finset.sum_add_distrib]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by
        rw [double_weighted_left s p _ hsum, double_weighted_right s p _ hsum]
        ring
  have hDR := mul_le_mul_of_nonneg_left hR hD
  rw [← hAB] at hsm
  nlinarith

theorem finite_fiber_q_moment_step_four
    (hq : 1 ≤ q) (hq2 : q ≤ 2) (hD : 0 ≤ D)
    (hsmooth : SymmetricPowerSmoothWith q D X)
    {Ω κ : Type*} [Fintype Ω] [Fintype κ] [DecidableEq κ]
    (w : Ω → ℝ) (key : Ω → κ) (a b : Ω → X)
    (hw : ∀ i, 0 ≤ w i)
    (hadapt : ∀ i j, key i = key j → a i = a j)
    (hzero : ∀ c, ∑ i ∈ Finset.univ.filter (fun i => key i = c), w i • (b i - a i) = 0) :
    (∑ i, w i * ‖b i‖ ^ q) ≤ (∑ i, w i * ‖a i‖ ^ q) +
      (4 * D) * ∑ i, w i * ‖b i - a i‖ ^ q := by
  classical
  have hcell (c : κ) :
      (∑ i ∈ Finset.univ.filter (fun i => key i = c), w i * ‖b i‖ ^ q) ≤
      (∑ i ∈ Finset.univ.filter (fun i => key i = c), w i * ‖a i‖ ^ q) +
      (4 * D) * ∑ i ∈ Finset.univ.filter (fun i => key i = c), w i * ‖b i - a i‖ ^ q := by
    let s := Finset.univ.filter (fun i => key i = c)
    let μ := ∑ i ∈ s, w i
    have hμ0 : 0 ≤ μ := Finset.sum_nonneg (fun i _ => hw i)
    by_cases hμ : μ = 0
    · have hwzero : ∀ i ∈ s, w i = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hw i)).1 hμ
      change (∑ i ∈ s, w i * ‖b i‖ ^ q) ≤
        (∑ i ∈ s, w i * ‖a i‖ ^ q) + (4 * D) * ∑ i ∈ s, w i * ‖b i - a i‖ ^ q
      have hz (f : Ω → ℝ) : (∑ i ∈ s, w i * f i) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [hwzero i hi, zero_mul]
      rw [hz, hz, hz]
      simp
    · have hμpos : 0 < μ := lt_of_le_of_ne hμ0 (Ne.symm hμ)
      have hs : s.Nonempty := by
        by_contra hempty
        have hse : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
        exact hμ (by simp [μ, hse])
      obtain ⟨i₀, hi₀⟩ := hs
      have ha (i : Ω) (hi : i ∈ s) : a i = a i₀ :=
        hadapt i i₀ ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hi₀).2.symm)
      let p : Ω → ℝ := fun i => w i / μ
      have hp : ∀ i ∈ s, 0 ≤ p i := fun i _ => div_nonneg (hw i) hμ0
      have hp1 : (∑ i ∈ s, p i) = 1 := by
        dsimp [p]
        calc
          (∑ i ∈ s, w i / μ) = (∑ i ∈ s, w i) / μ := by
            simp only [div_eq_mul_inv, Finset.sum_mul]
          _ = 1 := div_self hμ
      have hz : (∑ i ∈ s, w i • (b i - a i₀)) = 0 := by
        calc
          _ = ∑ i ∈ s, w i • (b i - a i) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [ha i hi]
          _ = 0 := hzero c
      have hpz : (∑ i ∈ s, p i • (b i - a i₀)) = 0 := by
        calc
          _ = μ⁻¹ • ∑ i ∈ s, w i • (b i - a i₀) := by
            rw [Finset.smul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            rw [smul_smul]
            congr 1
            dsimp [p]
            ring
          _ = 0 := by rw [hz, smul_zero]
      have hc := centered_q_moment_four s hq hq2 hD hsmooth p
        (fun i => b i - a i₀) hp hp1 hpz (a i₀)
      have he (i : Ω) : a i₀ + (b i - a i₀) = b i := by abel
      simp_rw [he] at hc
      have hscale (f : Ω → ℝ) : μ * (∑ i ∈ s, p i * f i) = ∑ i ∈ s, w i * f i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [p]
        calc
          μ * ((w i / μ) * f i) = ((w i / μ) * μ) * f i := by ring
          _ = w i * f i := by rw [div_mul_cancel₀ _ hμ]
      have hconst : (∑ i ∈ s, w i * ‖a i‖ ^ q) = μ * ‖a i₀‖ ^ q := by
        calc
          _ = ∑ i ∈ s, w i * ‖a i₀‖ ^ q := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [ha i hi]
          _ = _ := (Finset.sum_mul ..).symm
      have hdiff : (∑ i ∈ s, w i * ‖b i - a i₀‖ ^ q) =
          ∑ i ∈ s, w i * ‖b i - a i‖ ^ q := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [ha i hi]
      change (∑ i ∈ s, w i * ‖b i‖ ^ q) ≤
        (∑ i ∈ s, w i * ‖a i‖ ^ q) + (4 * D) * ∑ i ∈ s, w i * ‖b i - a i‖ ^ q
      calc
        _ = μ * ∑ i ∈ s, p i * ‖b i‖ ^ q := (hscale _).symm
        _ ≤ μ * (‖a i₀‖ ^ q + (4 * D) * ∑ i ∈ s, p i * ‖b i - a i₀‖ ^ q) :=
          mul_le_mul_of_nonneg_left hc hμ0
        _ = μ * ‖a i₀‖ ^ q + (4 * D) *
            (μ * ∑ i ∈ s, p i * ‖b i - a i₀‖ ^ q) := by ring
        _ = _ := by rw [hscale, ← hconst, hdiff]
  have h := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset κ)) => hcell c)
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_fiberwise] using h

theorem finite_martingale_q_moment_four
    (hq : 1 ≤ q) (hq2 : q ≤ 2) (hD : 0 ≤ D)
    (hsmooth : SymmetricPowerSmoothWith q D X)
    {Ω : Type*} [Fintype Ω] (n : ℕ)
    (K : Fin n → Type*) [∀ k, Fintype (K k)] [∀ k, DecidableEq (K k)]
    (w : Ω → ℝ) (key : ∀ k, Ω → K k) (M : ℕ → Ω → X)
    (hw : ∀ i, 0 ≤ w i) (hstart : ∀ i, M 0 i = 0)
    (hadapt : ∀ k i j, key k i = key k j → M k.val i = M k.val j)
    (hzero : ∀ k c, ∑ i ∈ Finset.univ.filter (fun i => key k i = c),
      w i • (M (k.val + 1) i - M k.val i) = 0) :
    (∑ i, w i * ‖M n i‖ ^ q) ≤ (4 * D) * ∑ k : Fin n, ∑ i,
      w i * ‖M (k.val + 1) i - M k.val i‖ ^ q := by
  let Q (k : ℕ) := ∑ i, w i * ‖M k i‖ ^ q
  let E (k : ℕ) := ∑ i, w i * ‖M (k + 1) i - M k i‖ ^ q
  have hq0 : q ≠ 0 := by linarith
  have hQ0 : Q 0 = 0 := by simp [Q, hstart, Real.zero_rpow hq0]
  have hstep (k : ℕ) (hk : k < n) : Q (k + 1) ≤ Q k + (4 * D) * E k :=
    finite_fiber_q_moment_step_four hq hq2 hD hsmooth w (key ⟨k, hk⟩)
      (M k) (M (k + 1)) hw (hadapt ⟨k, hk⟩) (hzero ⟨k, hk⟩)
  have ht : ∀ j, j ≤ n → Q j ≤ (4 * D) * ∑ k ∈ Finset.range j, E k := by
    intro j
    induction j with
    | zero => intro hj; simp [hQ0]
    | succ j ih =>
      intro hj
      calc
        Q (j + 1) ≤ Q j + (4 * D) * E j := hstep j (by omega)
        _ ≤ (4 * D) * (∑ k ∈ Finset.range j, E k) + (4 * D) * E j :=
          add_le_add_left (ih (by omega)) _
        _ = (4 * D) * ∑ k ∈ Finset.range (j + 1), E k := by
          rw [Finset.sum_range_succ, mul_add]
  change Q n ≤ (4 * D) * ∑ k : Fin n, E k.val
  rw [Fin.sum_univ_eq_sum_range]
  exact ht n le_rfl

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_HomogeneousRows
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

open scoped BigOperators

noncomputable section

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem norm_row_sum_le_card {m : ℕ} (a : Fin m → ℝ) (y : Fin m → Y)
    (ha : ∀ i, |a i| ≤ 1) (hy : ∀ i, ‖y i‖ ≤ 1) :
    ‖∑ i, a i • y i‖ ≤ (m : ℝ) := by
  calc
    ‖∑ i, a i • y i‖ ≤ ∑ i, ‖a i • y i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin m, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs]
      calc
        |a i| * ‖y i‖ ≤ |a i| * 1 :=
          mul_le_mul_of_nonneg_left (hy i) (abs_nonneg _)
        _ ≤ 1 := by simpa only [mul_one] using ha i
    _ = (m : ℝ) := by simp

theorem abs_norm_row_sum_sub_le {m : ℕ} (a b : Fin m → ℝ)
    (y : Fin m → Y) (hy : ∀ i, ‖y i‖ ≤ 1) (ε : ℝ)
    (hab : ∀ i, |a i - b i| ≤ ε) :
    |‖∑ i, a i • y i‖ - ‖∑ i, b i • y i‖| ≤ (m : ℝ) * ε := by
  calc
    |‖∑ i, a i • y i‖ - ‖∑ i, b i • y i‖| ≤
        ‖(∑ i, a i • y i) - ∑ i, b i • y i‖ := abs_norm_sub_norm_le _ _
    _ = ‖∑ i, (a i - b i) • y i‖ := by
      simp only [sub_smul, Finset.sum_sub_distrib]
    _ ≤ ∑ i, ‖(a i - b i) • y i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin m, ε := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs]
      calc
        |a i - b i| * ‖y i‖ ≤ |a i - b i| * 1 :=
          mul_le_mul_of_nonneg_left (hy i) (abs_nonneg _)
        _ ≤ ε := by simpa only [mul_one] using hab i
    _ = (m : ℝ) * ε := by simp

private theorem boundedNormBin_close {k m : ℕ} (hk : 0 < k)
    {z w : ℝ} (hz0 : 0 ≤ z) (hw0 : 0 ≤ w)
    {hz : z ≤ (m : ℝ)} {hw : w ≤ (m : ℝ)}
    (h : boundedNormBin k m z hz = boundedNormBin k m w hw) :
    |z - w| ≤ 1 / (k : ℝ) := by
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have heq : ⌊(k : ℝ) * z⌋₊ = ⌊(k : ℝ) * w⌋₊ := congrArg Fin.val h
  have hzLower := Nat.floor_le (mul_nonneg hkR.le hz0)
  have hwLower := Nat.floor_le (mul_nonneg hkR.le hw0)
  have hzUpper := Nat.lt_floor_add_one ((k : ℝ) * z)
  have hwUpper := Nat.lt_floor_add_one ((k : ℝ) * w)
  rw [heq] at hzLower hzUpper
  have hzw : z - w ≤ 1 / (k : ℝ) := by
    apply (le_div_iff₀ hkR).2
    nlinarith
  have hwz : w - z ≤ 1 / (k : ℝ) := by
    apply (le_div_iff₀ hkR).2
    nlinarith
  exact abs_le.mpr ⟨by linarith, hzw⟩

theorem exists_homogeneous_rows (k : ℕ) (hk : 0 < k) :
    ∃ B : ℕ, k ≤ B ∧ k ^ 3 ≤ B ∧
      ∀ y : Fin B → Y, (∀ i, ‖y i‖ ≤ 1) →
        ∃ e : Fin k ↪o Fin B,
          ∀ (m : ℕ) (_hm : m ≤ k) (a : Fin m → ℝ), (∀ i, |a i| ≤ 1) →
            ∀ s t : Fin m ↪o Fin k,
              |‖∑ i, a i • y (e (s i))‖ - ‖∑ i, a i • y (e (t i))‖| ≤
                3 / (k : ℝ) := by
  classical
  let colors : Fin (k + 1) → ℕ := fun m => Fintype.card (RowPalette k m.val)
  have hcolors : ∀ m, 0 < colors m := by
    intro m
    change 0 < Fintype.card (RowPalette k m.val)
    let : Nonempty (RowPalette k m.val) :=
      ⟨fun _ => ⟨0, Nat.zero_lt_succ _⟩⟩
    exact Fintype.card_pos
  obtain ⟨B, hBbound, hB⟩ :=
    finite_ordered_simultaneous_ramsey k (k ^ 3) colors hcolors
  refine ⟨B, (le_max_left _ _).trans hBbound,
    (le_max_right _ _).trans hBbound, ?_⟩
  intro y hy
  let rawColor : (m : Fin (k + 1)) → (Fin m.val ↪o Fin B) → RowPalette k m.val :=
    fun m u g => boundedNormBin k m.val
      ‖∑ i, coefficientGridValue k (g i) • y (u i)‖
      (norm_row_sum_le_card (fun i => coefficientGridValue k (g i))
        (fun i => y (u i)) (fun i => abs_coefficientGridValue_le k hk (g i))
        (fun i => hy (u i)))
  let χ : (m : Fin (k + 1)) → (Fin m.val ↪o Fin B) → Fin (colors m) :=
    fun m u => Fintype.equivFin (RowPalette k m.val) (rawColor m u)
  obtain ⟨e, he⟩ := hB χ
  refine ⟨e, ?_⟩
  intro m hm a ha s t
  let arity : Fin (k + 1) := ⟨m, Nat.lt_succ_of_le hm⟩
  have hencoded :
      Fintype.equivFin (RowPalette k m) (rawColor arity (s.trans e)) =
        Fintype.equivFin (RowPalette k m) (rawColor arity (t.trans e)) :=
    he arity s t
  have hcolor : rawColor arity (s.trans e) = rawColor arity (t.trans e) :=
    (Fintype.equivFin (RowPalette k m)).injective hencoded
  let g : RowCoefficientGrid k m := fun i =>
    Classical.choose (exists_coefficientGrid_approx k hk (a i) (ha i))
  have hg : ∀ i, |a i - coefficientGridValue k (g i)| ≤ 1 / (k : ℝ) ^ 2 := by
    intro i
    exact Classical.choose_spec (exists_coefficientGrid_approx k hk (a i) (ha i))
  have hmiddle :
      |‖∑ i, coefficientGridValue k (g i) • y (e (s i))‖ -
        ‖∑ i, coefficientGridValue k (g i) • y (e (t i))‖| ≤ 1 / (k : ℝ) := by
    exact boundedNormBin_close (m := m) hk (norm_nonneg _) (norm_nonneg _)
      (congrFun hcolor g)
  have hleft := abs_norm_row_sum_sub_le a (fun i => coefficientGridValue k (g i))
    (fun i => y (e (s i))) (fun i => hy (e (s i))) (1 / (k : ℝ) ^ 2) hg
  have hright := abs_norm_row_sum_sub_le a (fun i => coefficientGridValue k (g i))
    (fun i => y (e (t i))) (fun i => hy (e (t i))) (1 / (k : ℝ) ^ 2) hg
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkR
  have hmR : (m : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hm
  have hbudget : (m : ℝ) * (1 / (k : ℝ) ^ 2) ≤ 1 / (k : ℝ) := by
    calc
      (m : ℝ) * (1 / (k : ℝ) ^ 2) ≤ (k : ℝ) * (1 / (k : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hmR (div_nonneg zero_le_one (sq_nonneg _))
      _ = 1 / (k : ℝ) := by field_simp [hkne]
  have hthree : (3 : ℝ) / (k : ℝ) = 3 * (1 / (k : ℝ)) := by ring
  rw [hthree]
  obtain ⟨hleftLower, hleftUpper⟩ := abs_le.mp hleft
  obtain ⟨hrightLower, hrightUpper⟩ := abs_le.mp hright
  obtain ⟨hmiddleLower, hmiddleUpper⟩ := abs_le.mp hmiddle
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SubdivisionOperators
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.OrderedNorm.instCoeFunForallC00Real _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity.C00

theorem uniformSubdivision_ofArray_apply_of_ge (q : ℕ) {m : ℕ} (a : Fin m → ℝ)
    (k : ℕ) (hk : q * m ≤ k) : uniformSubdivision q (ofArray a) k = 0 := by
  exact subdivide_ofArray_apply_of_ge (fun _ => q) a k
    (by simpa only [blockOffset_const] using hk)

end MarkovSuperreflexivity.C00

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_TriangularArrays
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

universe u

variable {Y : Type u} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

private theorem exists_triangular_array_with_value
    (v : StrongDual ℝ (StrongDual ℝ Y)) (hv : ‖v‖ ≤ 1)
    {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε)
    (hgap : d < Metric.infDist v
      (Set.range (NormedSpace.inclusionInDoubleDual ℝ Y))) (M : ℕ) :
    ∃ A : TriangularArray Y d ε M, ∀ i, v (A.f i) = d := by
  classical
  induction M with
  | zero =>
      refine ⟨{
        y := Fin.elim0
        f := Fin.elim0
        y_norm_le := fun i => Fin.elim0 i
        f_norm_le := fun i => Fin.elim0 i
        lower_zero := fun i => Fin.elim0 i
        upper_close := fun i => Fin.elim0 i }, ?_⟩
      intro i
      exact Fin.elim0 i
  | succ k ih =>
      obtain ⟨A, hA⟩ := ih
      let E : Submodule ℝ Y := Submodule.span ℝ (Set.range A.y)
      let : FiniteDimensional ℝ E :=
        FiniteDimensional.span_of_finite ℝ (Set.finite_range A.y)
      obtain ⟨g, hg, hg_zero, hg_value⟩ :=
        exists_annihilating_functional E v hd hgap
      have hg_y (j : Fin k) : g (A.y j) = 0 :=
        hg_zero ⟨A.y j, Submodule.subset_span ⟨j, rfl⟩⟩
      let f' : Fin (k + 1) → (Y →L[ℝ] ℝ) := Fin.snoc A.f g
      have hf_value (i : Fin (k + 1)) : v (f' i) = d := by
        refine Fin.lastCases ?_ (fun i => ?_) i
        · simpa only [f', Fin.snoc_last] using hg_value
        · simpa only [f', Fin.snoc_castSucc] using hA i
      have hf_norm (i : Fin (k + 1)) : ‖f' i‖ ≤ 1 := by
        refine Fin.lastCases ?_ (fun i => ?_) i
        · simpa only [f', Fin.snoc_last] using hg
        · simpa only [f', Fin.snoc_castSucc] using A.f_norm_le i
      obtain ⟨z, hz_norm, hz_close⟩ := finite_goldstine v hv f' hε
      have hz_d (i : Fin (k + 1)) : |f' i z - d| ≤ ε := by
        rw [← hf_value i]
        exact (hz_close i).le
      let B : TriangularArray Y d ε (k + 1) := {
        y := Fin.snoc A.y z
        f := f'
        y_norm_le := by
          intro j
          refine Fin.lastCases ?_ (fun j => ?_) j
          · simpa only [Fin.snoc_last] using hz_norm
          · simpa only [Fin.snoc_castSucc] using A.y_norm_le j
        f_norm_le := hf_norm
        lower_zero := by
          intro i j
          refine Fin.lastCases ?_ (fun j => ?_) j
          · intro h
            exact (not_lt_of_ge (Fin.le_last i) h).elim
          · refine Fin.lastCases ?_ (fun i => ?_) i
            · intro _
              simpa only [f', Fin.snoc_last, Fin.snoc_castSucc] using hg_y j
            · intro h
              simpa only [f', Fin.snoc_castSucc] using A.lower_zero i j h
        upper_close := by
          intro i j
          refine Fin.lastCases ?_ (fun j => ?_) j
          · intro _
            simpa only [Fin.snoc_last] using hz_d i
          · refine Fin.lastCases ?_ (fun i => ?_) i
            · intro h
              exact (not_le_of_gt (Fin.castSucc_lt_last j) h).elim
            · intro h
              simpa only [f', Fin.snoc_castSucc] using A.upper_close i j h }
      exact ⟨B, hf_value⟩

theorem exists_triangular_array_of_gap
    (v : StrongDual ℝ (StrongDual ℝ Y)) (hv : ‖v‖ ≤ 1)
    {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε)
    (hgap : d < Metric.infDist v
      (Set.range (NormedSpace.inclusionInDoubleDual ℝ Y))) (M : ℕ) :
    Nonempty (TriangularArray Y d ε M) := by
  obtain ⟨A, _⟩ := exists_triangular_array_with_value v hv hd hε hgap M
  exact ⟨A⟩

theorem exists_uniform_triangular_arrays [CompleteSpace Y]
    (hNR : ¬ Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ Y)) :
    ∃ d : ℝ, 0 < d ∧ ∀ M : ℕ, 0 < M →
      Nonempty (TriangularArray Y d (M : ℝ)⁻¹ M) := by
  obtain ⟨v, d, hv, hd, hgap⟩ := exists_bidual_gap hNR
  refine ⟨d, hd, ?_⟩
  intro M hM
  exact exists_triangular_array_of_gap v hv hd
    (inv_pos.mpr (Nat.cast_pos.mpr hM)) hgap M

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_TriangularPrefix
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.OrderedNorm.instCoeFunForallC00Real _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

universe u

variable {Y : Type u} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem coefficientL1_nonneg {m : ℕ} (a : Fin m → ℝ) : 0 ≤ coefficientL1 a :=
  Finset.sum_nonneg fun i _ => abs_nonneg (a i)

theorem prefixCut_ofArray {m : ℕ} (a : Fin m → ℝ) (k : ℕ) :
    prefixCut (C00.ofArray a) k = arrayPrefix a k := by
  classical
  simp only [prefixCut, C00.ofArray, C00.place, Finsupp.finsetSum_apply]
  rw [Finset.sum_comm]
  simp only [Finsupp.single_apply, Finset.sum_ite_eq, Finset.mem_range, arrayPrefix]

theorem triangular_prefix_lower {M m : ℕ} {d ε : ℝ}
    (A : TriangularArray Y d ε M) (hd : 0 ≤ d) (hε : 0 ≤ ε)
    (idx : Fin m → Fin M) (hidx : StrictAnti idx) (a : Fin m → ℝ) (k : ℕ) :
    d * |arrayPrefix a k| - ε * coefficientL1 a ≤
      ‖∑ i, a i • A.y (idx i)‖ := by
  classical
  by_cases hm : m = 0
  · subst m
    simp [arrayPrefix, coefficientL1]
  by_cases hk : k = 0
  · have hnonneg := mul_nonneg hε (coefficientL1_nonneg a)
    have hnorm := norm_nonneg (∑ i, a i • A.y (idx i))
    simp only [hk, arrayPrefix, Nat.not_lt_zero, ite_false, Finset.sum_const_zero,
      abs_zero, mul_zero]
    linarith
  have hmin_pos : 0 < min k m := by omega
  let j : Fin m := ⟨min k m - 1, by have := min_le_right k m; omega⟩
  let F : Y →L[ℝ] ℝ := A.f (idx j)
  let S : Y := ∑ i, a i • A.y (idx i)
  have herr (i : Fin m) :
      |F (A.y (idx i)) - (if i.val < k then d else 0)| ≤ ε := by
    by_cases hi : i.val < k
    · rw [ite_eq_left hi]
      have hij : i ≤ j := by
        change i.val ≤ min k m - 1
        have := i.isLt
        omega
      exact A.upper_close (idx j) (idx i) (hidx.antitone hij)
    · rw [ite_eq_right hi]
      have hji : j < i := by
        change min k m - 1 < i.val
        have := min_le_left k m
        omega
      have hzero : F (A.y (idx i)) = 0 := A.lower_zero (idx j) (idx i) (hidx hji)
      rw [hzero, sub_zero, abs_zero]
      exact hε
  have hidentity :
      F S - d * arrayPrefix a k =
        ∑ i, a i * (F (A.y (idx i)) - (if i.val < k then d else 0)) := by
    calc
      F S - d * arrayPrefix a k =
          (∑ i, a i * F (A.y (idx i))) -
            ∑ i, d * (if i.val < k then a i else 0) := by
        simp only [S, map_sum, map_smul, smul_eq_mul, arrayPrefix, Finset.mul_sum]
      _ = ∑ i, (a i * F (A.y (idx i)) - d * (if i.val < k then a i else 0)) := by
        rw [Finset.sum_sub_distrib]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> ring
  have herror : |F S - d * arrayPrefix a k| ≤ ε * coefficientL1 a := by
    rw [hidentity]
    calc
      |∑ i, a i * (F (A.y (idx i)) - (if i.val < k then d else 0))|
          ≤ ∑ i, |a i * (F (A.y (idx i)) - (if i.val < k then d else 0))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |a i| * ε := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (herr i) (abs_nonneg (a i))
      _ = ε * coefficientL1 a := by
        rw [← Finset.sum_mul]
        exact mul_comm _ _
  have hF : |F S| ≤ ‖S‖ := by
    simpa only [Real.norm_eq_abs, one_mul] using
      F.le_of_opNorm_le (A.f_norm_le (idx j)) S
  have htriangle : |d * arrayPrefix a k| ≤ |F S| + |F S - d * arrayPrefix a k| := by
    calc
      |d * arrayPrefix a k| = |F S - (F S - d * arrayPrefix a k)| := by congr 1; ring
      _ ≤ |F S| + |F S - d * arrayPrefix a k| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le (F S) (-(F S - d * arrayPrefix a k))
  rw [abs_mul, abs_of_nonneg hd] at htriangle
  change d * |arrayPrefix a k| - ε * coefficientL1 a ≤ ‖S‖
  linarith

theorem triangular_prefixCut_lower {M m : ℕ} {d ε : ℝ}
    (A : TriangularArray Y d ε M) (hd : 0 ≤ d) (hε : 0 ≤ ε)
    (idx : Fin m → Fin M) (hidx : StrictAnti idx) (a : Fin m → ℝ) (k : ℕ) :
    d * |prefixCut (C00.ofArray a) k| - ε * coefficientL1 a ≤
      ‖∑ i, a i • A.y (idx i)‖ := by
  rw [prefixCut_ofArray]
  exact triangular_prefix_lower A hd hε idx hidx a k

theorem reversed_triangular_prefixCut_lower {M m : ℕ} {d ε : ℝ}
    (A : TriangularArray Y d ε M) (hd : 0 ≤ d) (hε : 0 ≤ ε)
    (idx : Fin m → Fin M) (hidx : StrictMono idx) (a : Fin m → ℝ) (k : ℕ) :
    d * |prefixCut (C00.ofArray a) k| - ε * coefficientL1 a ≤
      ‖∑ i, a i • A.y (Fin.rev (idx i))‖ := by
  apply triangular_prefixCut_lower A hd hε (fun i => Fin.rev (idx i)) _ a k
  intro i j hij
  exact Fin.rev_lt_rev.mpr (hidx hij)

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SelectedRows
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.OrderedNorm.instCoeFunForallC00Real _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable (Y : Type*) [NormedAddCommGroup Y] [NormedSpace ℝ Y]

variable {Y}

theorem exists_selectedRow (d : ℝ)
    (hrows : ∀ M : ℕ, 0 < M → Nonempty (TriangularArray Y d (M : ℝ)⁻¹ M))
    (k : ℕ) (hk : 0 < k) : Nonempty (SelectedRow Y d k) := by
  obtain ⟨M, hkM, hcubic, hselect⟩ := exists_homogeneous_rows (Y := Y) k hk
  obtain ⟨A⟩ := hrows M (hk.trans_le hkM)
  obtain ⟨e, he⟩ := hselect (fun i => A.y (Fin.rev i))
    (fun i => A.y_norm_le (Fin.rev i))
  exact ⟨⟨M, hkM, hcubic, A, e, he⟩⟩

namespace SelectedRow

variable {d : ℝ} {k : ℕ}

theorem norm_vector_le (R : SelectedRow Y d k) (i : Fin k) : ‖R.vector i‖ ≤ 1 :=
  R.A.y_norm_le _

theorem synthesis_basis (R : SelectedRow Y d k) (j : ℕ) :
    R.synthesis (C00.basis j) = if h : j < k then R.vector ⟨j, h⟩ else 0 := by
  simp only [synthesis, C00.basis, Finsupp.linearCombination_single, one_smul]

theorem norm_synthesis_basis_le (R : SelectedRow Y d k) (j : ℕ) :
    ‖R.synthesis (C00.basis j)‖ ≤ 1 := by
  rw [synthesis_basis]
  split_ifs with h
  · exact R.norm_vector_le ⟨j, h⟩
  · simp

theorem synthesis_place (R : SelectedRow Y d k) {m : ℕ}
    (ι : Fin m → ℕ) (hι : ∀ i, ι i < k) (a : Fin m → ℝ) :
    R.synthesis (C00.place ι a) = ∑ i, a i • R.vector ⟨ι i, hι i⟩ := by
  simp only [C00.place, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [synthesis, Finsupp.linearCombination_single, dite_eq_left (hι i)]

theorem synthesis_ofArray (R : SelectedRow Y d k) {m : ℕ}
    (hm : m ≤ k) (a : Fin m → ℝ) :
    R.synthesis (C00.ofArray a) =
      ∑ i, a i • R.vector ⟨i.val, lt_of_lt_of_le i.isLt hm⟩ :=
  R.synthesis_place Fin.val (fun i => lt_of_lt_of_le i.isLt hm) a

theorem synthesis_prefix_lower (R : SelectedRow Y d k) (hd : 0 ≤ d)
    {m : ℕ} (hm : m ≤ k) (a : Fin m → ℝ) (r : ℕ) :
    d * |prefixCut (C00.ofArray a) r| - (R.M : ℝ)⁻¹ * coefficientL1 a ≤
      ‖R.synthesis (C00.ofArray a)‖ := by
  rw [R.synthesis_ofArray hm a]
  apply reversed_triangular_prefixCut_lower R.A hd
    (inv_nonneg.mpr (Nat.cast_nonneg _))
    (fun i => R.e ⟨i.val, lt_of_lt_of_le i.isLt hm⟩) _ a r
  intro i j hij
  exact R.e.strictMono hij

theorem synthesis_oscillation (R : SelectedRow Y d k) {m : ℕ} (hm : m ≤ k)
    (ι κ : Fin m → ℕ) (hι : StrictMono ι) (hκ : StrictMono κ)
    (hιk : ∀ i, ι i < k) (hκk : ∀ i, κ i < k)
    (a : Fin m → ℝ) (ha : ∀ i, |a i| ≤ 1) :
    |‖R.synthesis (C00.place ι a)‖ - ‖R.synthesis (C00.place κ a)‖| ≤
      3 / (k : ℝ) := by
  let s : Fin m ↪o Fin k := OrderEmbedding.ofStrictMono
    (fun i => ⟨ι i, hιk i⟩) (fun i j hij => hι hij)
  let t : Fin m ↪o Fin k := OrderEmbedding.ofStrictMono
    (fun i => ⟨κ i, hκk i⟩) (fun i j hij => hκ hij)
  rw [R.synthesis_place ι hιk a, R.synthesis_place κ hκk a]
  exact R.homogeneous m hm a ha s t

end SelectedRow

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SpreadingLimitEmbedding
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

variable {E Y : Type*}
variable [AddCommGroup E] [Module ℝ E]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem norm_spreadingRescale (δ : ℝ) (S : E →ₗ[ℝ] Y)
    (hδ : δ < 1) (x : E) :
    ‖spreadingRescale δ S x‖ = (1 - δ)⁻¹ * ‖S x‖ := by
  have hd : 0 < 1 - δ := sub_pos.mpr hδ
  rw [spreadingRescale_apply, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr hd.le)]

theorem spreadingRescale_bounds (p : Seminorm ℝ E) (S : E →ₗ[ℝ] Y)
    (δ : ℝ) (_hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (happrox : ∀ x, |‖S x‖ - p x| ≤ δ * p x) :
    ∀ x, p x ≤ ‖spreadingRescale δ S x‖ ∧
      ‖spreadingRescale δ S x‖ ≤ ((1 + δ) / (1 - δ)) * p x := by
  intro x
  have hd : 0 < 1 - δ := sub_pos.mpr hδ1
  have hdinv : 0 ≤ (1 - δ)⁻¹ := inv_nonneg.mpr hd.le
  obtain ⟨hl, hu⟩ := abs_le.mp (happrox x)
  have hlower : (1 - δ) * p x ≤ ‖S x‖ := by linarith
  have hupper : ‖S x‖ ≤ (1 + δ) * p x := by linarith
  rw [norm_spreadingRescale δ S hδ1 x]
  constructor
  · calc
      p x = (1 - δ)⁻¹ * ((1 - δ) * p x) := by
        rw [← mul_assoc, inv_mul_cancel₀ hd.ne', one_mul]
      _ ≤ (1 - δ)⁻¹ * ‖S x‖ := mul_le_mul_of_nonneg_left hlower hdinv
  · calc
      (1 - δ)⁻¹ * ‖S x‖ ≤ (1 - δ)⁻¹ * ((1 + δ) * p x) :=
        mul_le_mul_of_nonneg_left hupper hdinv
      _ = ((1 + δ) / (1 - δ)) * p x := by
        rw [div_eq_mul_inv]
        ring

theorem spreading_errorParameter (η : ℝ) (hη : 0 < η) :
    0 ≤ η / (2 + η) ∧ η / (2 + η) < 1 ∧
      (1 + η / (2 + η)) / (1 - η / (2 + η)) = 1 + η := by
  have hden : 0 < 2 + η := by linarith
  have hδ0 : 0 ≤ η / (2 + η) := div_nonneg hη.le hden.le
  have hδ1 : η / (2 + η) < 1 := (div_lt_one hden).mpr (by linarith)
  have hd : 0 < 1 - η / (2 + η) := sub_pos.mpr hδ1
  refine ⟨hδ0, hδ1, ?_⟩
  apply (div_eq_iff hd.ne').mpr
  have hcancel : η / (2 + η) * (2 + η) = η := div_mul_cancel₀ η hden.ne'
  nlinarith

theorem exists_spreading_normalizedMap (p : Seminorm ℝ E) (S : E →ₗ[ℝ] Y)
    (η : ℝ) (hη : 0 < η)
    (happrox : ∀ x, |‖S x‖ - p x| ≤ (η / (2 + η)) * p x) :
    ∃ T : E →ₗ[ℝ] Y, ∀ x, p x ≤ ‖T x‖ ∧ ‖T x‖ ≤ (1 + η) * p x := by
  obtain ⟨hδ0, hδ1, hratio⟩ := spreading_errorParameter η hη
  refine ⟨spreadingRescale (η / (2 + η)) S, ?_⟩
  intro x
  simpa only [hratio] using
    spreadingRescale_bounds p S (η / (2 + η)) hδ0 hδ1 happrox x

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SpreadingLimitUniform
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped BigOperators Topology

namespace MarkovSuperreflexivity

theorem coefficient_limit_lipschitz {m : ℕ}
    (v : ℕ → (Fin m → ℝ) → ℝ) (f : (Fin m → ℝ) → ℝ)
    (hlip : ∀ n a b, |v n a - v n b| ≤ ∑ i, |a i - b i|)
    (hlim : ∀ a, Tendsto (fun n => v n a) atTop (𝓝 (f a)))
    (a b : Fin m → ℝ) : |f a - f b| ≤ ∑ i, |a i - b i| := by
  apply abs_le.mpr
  constructor
  · exact le_of_tendsto_of_tendsto' tendsto_const_nhds ((hlim a).sub (hlim b))
      (fun n => (abs_le.mp (hlip n a b)).1)
  · exact le_of_tendsto' ((hlim a).sub (hlim b))
      (fun n => (abs_le.mp (hlip n a b)).2)

theorem uniform_coefficients_of_pointwise {m : ℕ}
    (v : ℕ → (Fin m → ℝ) → ℝ) (f : (Fin m → ℝ) → ℝ)
    (hlip : ∀ n a b, |v n a - v n b| ≤ ∑ i, |a i - b i|)
    (hlim : ∀ a, Tendsto (fun n => v n a) atTop (𝓝 (f a)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ a : Fin m → ℝ,
      (∀ i, |a i| ≤ 1) → |v n a - f a| < ε := by
  classical
  have hmpos : 0 < (m : ℝ) + 1 := by positivity
  have hethird : 0 < ε / 3 := by positivity
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt
    (show 0 < ε / (3 * ((m : ℝ) + 1)) by positivity)
  let k : ℕ := j + 1
  have hk : 0 < k := Nat.succ_pos j
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hsmall : 1 / (k : ℝ) < ε / (3 * ((m : ℝ) + 1)) := by
    simpa only [k, Nat.cast_add, Nat.cast_one] using hj
  have hmesh : 1 / (k : ℝ) ^ 2 ≤ 1 / (k : ℝ) := by
    apply (div_le_div_iff₀ (pow_pos hkR _) hkR).mpr
    nlinarith
  have hbudget : (m : ℝ) * (1 / (k : ℝ) ^ 2) < ε / 3 := by
    have hmul := mul_lt_mul_of_pos_left hsmall hmpos
    have hcancel : ((m : ℝ) + 1) * (ε / (3 * ((m : ℝ) + 1))) = ε / 3 := by
      field_simp [hmpos.ne']
    rw [hcancel] at hmul
    have hstep := mul_le_mul_of_nonneg_left hmesh (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    have hinv : 0 ≤ 1 / (k : ℝ) := by positivity
    nlinarith
  let Grid := Fin m → Fin (2 * k ^ 2 + 1)
  let coeff : Grid → Fin m → ℝ := fun g i => coefficientGridValue k (g i)
  have hpoint (g : Grid) :
      ∃ N : ℕ, ∀ n ≥ N, |v n (coeff g) - f (coeff g)| < ε / 3 := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hlim (coeff g)) (ε / 3) hethird
    exact ⟨N, fun n hn => by simpa only [Real.dist_eq] using hN n hn⟩
  choose cutoff hcutoff using hpoint
  let N : ℕ := Finset.univ.sup cutoff
  refine ⟨N, ?_⟩
  intro n hn a ha
  choose g hg using fun i : Fin m => exists_coefficientGrid_approx k hk (a i) (ha i)
  have hsum : (∑ i, |a i - coeff g i|) ≤ (m : ℝ) * (1 / (k : ℝ) ^ 2) := by
    calc
      (∑ i, |a i - coeff g i|) ≤ ∑ _i : Fin m, 1 / (k : ℝ) ^ 2 :=
        Finset.sum_le_sum (fun i _ => hg i)
      _ = (m : ℝ) * (1 / (k : ℝ) ^ 2) := by simp
  have hleft : |v n a - v n (coeff g)| < ε / 3 :=
    (hlip n a (coeff g)).trans_lt (hsum.trans_lt hbudget)
  have hright : |f a - f (coeff g)| < ε / 3 :=
    (coefficient_limit_lipschitz v f hlip hlim a (coeff g)).trans_lt
      (hsum.trans_lt hbudget)
  have hgN : cutoff g ≤ N := Finset.le_sup (Finset.mem_univ g)
  have hmiddle := hcutoff g n (hgN.trans hn)
  obtain ⟨hl0, hl1⟩ := abs_lt.mp hleft
  obtain ⟨hr0, hr1⟩ := abs_lt.mp hright
  obtain ⟨hm0, hm1⟩ := abs_lt.mp hmiddle
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SpreadingCoordinateEmbedding
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped BigOperators Topology

namespace MarkovSuperreflexivity

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem relative_error_of_cube_error {m : ℕ} (p : Seminorm ℝ (Fin m → ℝ))
    (S : (Fin m → ℝ) →ₗ[ℝ] Y) (d δ : ℝ) (_hd : 0 < d) (hδ : 0 ≤ δ)
    (hcoord : ∀ a i, (d / 2) * |a i| ≤ p a)
    (hcube : ∀ a, (∀ i, |a i| ≤ 1) →
      |‖S a‖ - p a| ≤ δ * (d / 2) / ((m : ℝ) + 1)) :
    ∀ a, |‖S a‖ - p a| ≤ δ * p a := by
  classical
  intro a
  let c : ℝ := ∑ i, |a i|
  have hc0 : 0 ≤ c := Finset.sum_nonneg (fun i _ => abs_nonneg (a i))
  have hsingle (i : Fin m) : |a i| ≤ c :=
    Finset.single_le_sum (fun j _ => abs_nonneg (a j)) (Finset.mem_univ i)
  by_cases hc : c = 0
  · have ha : a = 0 := by
      funext i
      have hi := hsingle i
      rw [hc] at hi
      exact abs_eq_zero.mp (le_antisymm hi (abs_nonneg _))
    simp [ha]
  have hcpos : 0 < c := lt_of_le_of_ne hc0 (Ne.symm hc)
  let b : Fin m → ℝ := c⁻¹ • a
  have hab : c • b = a := by
    simp only [b, smul_smul, mul_inv_cancel₀ hc, one_smul]
  have hb : ∀ i, |b i| ≤ 1 := by
    intro i
    change |c⁻¹ * a i| ≤ 1
    rw [abs_mul, abs_of_pos (inv_pos.mpr hcpos)]
    calc
      c⁻¹ * |a i| ≤ c⁻¹ * c :=
        mul_le_mul_of_nonneg_left (hsingle i) (inv_nonneg.mpr hc0)
      _ = 1 := inv_mul_cancel₀ hc
  have hscale : |‖S a‖ - p a| = c * |‖S b‖ - p b| := by
    conv_lhs => rw [← hab]
    rw [map_smul, norm_smul, map_smul_eq_mul p, Real.norm_of_nonneg hc0,
      ← mul_sub, abs_mul, abs_of_nonneg hc0]
  have hmass : (d / 2) * c ≤ (m : ℝ) * p a := by
    calc
      (d / 2) * c = ∑ i, (d / 2) * |a i| := Finset.mul_sum _ _ _
      _ ≤ ∑ _i : Fin m, p a := Finset.sum_le_sum (fun i _ => hcoord a i)
      _ = (m : ℝ) * p a := by simp
  have hmpos : 0 < (m : ℝ) + 1 := by positivity
  have hmass' : (d / 2) * c ≤ ((m : ℝ) + 1) * p a := by
    have hp := apply_nonneg p a
    nlinarith
  rw [hscale]
  calc
    c * |‖S b‖ - p b| ≤ c * (δ * (d / 2) / ((m : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left (hcube b hb) hc0
    _ = δ * ((d / 2) * c) / ((m : ℝ) + 1) := by ring
    _ ≤ δ * (((m : ℝ) + 1) * p a) / ((m : ℝ) + 1) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmass' hδ) hmpos.le
    _ = δ * p a := by field_simp [hmpos.ne']

theorem exists_coordinate_embedding_of_convergence {m : ℕ}
    (p : Seminorm ℝ (Fin m → ℝ)) (d : ℝ) (hd : 0 < d)
    (hcoord : ∀ a i, (d / 2) * |a i| ≤ p a)
    (L : ℕ → (Fin m → ℝ) →ₗ[ℝ] Y)
    (hlip : ∀ n a b, |‖L n a‖ - ‖L n b‖| ≤ ∑ i, |a i - b i|)
    (hlim : ∀ a, Tendsto (fun n => ‖L n a‖) atTop (𝓝 (p a)))
    (η : ℝ) (hη : 0 < η) :
    ∃ T : (Fin m → ℝ) →ₗ[ℝ] Y, ∀ a,
      p a ≤ ‖T a‖ ∧ ‖T a‖ ≤ (1 + η) * p a := by
  let δ : ℝ := η / (2 + η)
  have hδ : 0 < δ := div_pos hη (by linarith)
  let ε : ℝ := δ * (d / 2) / ((m : ℝ) + 1)
  have hε : 0 < ε := by dsimp only [ε]; positivity
  obtain ⟨N, hN⟩ := uniform_coefficients_of_pointwise
    (fun n a => ‖L n a‖) p hlip hlim ε hε
  apply exists_spreading_normalizedMap p (L N) η hη
  apply relative_error_of_cube_error p (L N) d δ hd hδ.le hcoord
  intro a ha
  exact (hN N le_rfl a ha).le

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SpreadingLimitCauchy
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology

noncomputable section

namespace MarkovSuperreflexivity

variable {E Q : Type*}

theorem cauchySeq_of_dense_lipschitz
    (v : ℕ → E → ℝ) (q : Q → E) (d : E → E → ℝ)
    (hlip : ∀ n x y, |v n x - v n y| ≤ d x y)
    (hdense : ∀ x ε, 0 < ε → ∃ a, d x (q a) < ε)
    (hcauchy : ∀ a, CauchySeq (fun n => v n (q a))) (x : E) :
    CauchySeq (fun n => v n x) := by
  apply Metric.cauchySeq_iff.2
  intro ε hε
  have hthird : 0 < ε / 3 := by linarith
  obtain ⟨a, ha⟩ := hdense x (ε / 3) hthird
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 (hcauchy a) (ε / 3) hthird
  refine ⟨N, ?_⟩
  intro m hm n hn

  have hleft : dist (v m x) (v m (q a)) < ε / 3 := by
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (hlip m x (q a)) ha
  have hright : dist (v n (q a)) (v n x) < ε / 3 := by
    rw [dist_comm, Real.dist_eq]
    exact lt_of_le_of_lt (hlip n x (q a)) ha
  have hmiddle : dist (v m (q a)) (v n (q a)) < ε / 3 := hN m hm n hn
  have htriangle := dist_triangle (v m x) (v m (q a)) (v n x)
  have htriangle' := dist_triangle (v m (q a)) (v n (q a)) (v n x)
  linarith

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SpreadingLimitDiagonal
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology

namespace MarkovSuperreflexivity

theorem exists_common_subsequence_of_bounded_with_bounds
    {Q : Type*} [Countable Q] (v : ℕ → Q → ℝ) (b : Q → ℝ)
    (hbound : ∀ n q, v n q ∈ Set.Icc 0 (b q)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ l : Q → ℝ,
      (∀ q, l q ∈ Set.Icc 0 (b q)) ∧
      ∀ q, Tendsto (fun n => v (σ n) q) atTop (𝓝 (l q)) := by
  let x : ℕ → (∀ q : Q, Set.Icc (0 : ℝ) (b q)) :=
    fun n q => ⟨v n q, hbound n q⟩
  obtain ⟨a, σ, hσ, ha⟩ := CompactSpace.tendsto_subseq x
  refine ⟨σ, hσ, (fun q => (a q : ℝ)), (fun q => (a q).property), ?_⟩
  intro q
  have hcoord : Continuous
      (fun z : (∀ r : Q, Set.Icc (0 : ℝ) (b r)) => (z q : ℝ)) :=
    continuous_subtype_val.comp (continuous_apply q)
  simpa only [Function.comp_def, x] using (hcoord.tendsto a).comp ha

theorem exists_common_subsequence_of_bounded
    {Q : Type*} [Countable Q] (v : ℕ → Q → ℝ) (b : Q → ℝ)
    (hbound : ∀ n q, v n q ∈ Set.Icc 0 (b q)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ q, ∃ l : ℝ, Tendsto (fun n => v (σ n) q) atTop (𝓝 l) := by
  obtain ⟨σ, hσ, l, _, hl⟩ :=
    exists_common_subsequence_of_bounded_with_bounds v b hbound
  exact ⟨σ, hσ, fun q => ⟨l q, hl q⟩⟩

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SpreadingLimitReal
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.OrderedNorm.instCoeFunForallC00Real _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped BigOperators Topology

namespace MarkovSuperreflexivity

theorem exists_rational_coefficients {m : ℕ} (a : Fin m → ℝ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ q : Fin m → ℚ, (∑ i, |a i - (q i : ℝ)|) < ε := by
  classical
  let δ : ℝ := ε / ((m : ℝ) + 1)
  have hden : 0 < (m : ℝ) + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hden
  choose q hq using fun i : Fin m => exists_rat_near (a i) hδ
  refine ⟨q, ?_⟩
  have hsum : (∑ i, |a i - (q i : ℝ)|) ≤ (m : ℝ) * δ := by
    calc
      (∑ i, |a i - (q i : ℝ)|) ≤ ∑ _i : Fin m, δ :=
        Finset.sum_le_sum (fun i _ => (hq i).le)
      _ = (m : ℝ) * δ := by simp
  have hcancel : δ * ((m : ℝ) + 1) = ε :=
    div_mul_cancel₀ ε hden.ne'
  nlinarith

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem exists_cauchy_subsequence
    (L : ℕ → C00 →ₗ[ℝ] Y)
    (hunit : ∀ n i, ‖L n (C00.basis i)‖ ≤ 1) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ x : C00, CauchySeq (fun n => ‖L (σ n) x‖) := by
  let v : ℕ → RationalCoefficients → ℝ :=
    fun n q => ‖L n (C00.ofArray (fun i => (q.2 i : ℝ)))‖
  let b : RationalCoefficients → ℝ := fun q => ∑ i, |(q.2 i : ℝ)|
  have hbound : ∀ n q, v n q ∈ Set.Icc 0 (b q) := by
    intro n q
    exact ⟨norm_nonneg _, C00.norm_linearMap_ofArray_le (L n) (hunit n) _⟩
  obtain ⟨σ, hσ, hlimit⟩ := exists_common_subsequence_of_bounded v b hbound
  have hrat (m : ℕ) (q : Fin m → ℚ) :
      CauchySeq (fun n => ‖L (σ n) (C00.ofArray (fun i => (q i : ℝ)))‖) := by
    obtain ⟨l, hl⟩ := hlimit ⟨m, q⟩
    exact hl.cauchySeq
  have hreal (m : ℕ) (a : Fin m → ℝ) :
      CauchySeq (fun n => ‖L (σ n) (C00.ofArray a)‖) := by
    apply cauchySeq_of_dense_lipschitz
      (fun n a => ‖L (σ n) (C00.ofArray a)‖)
      (fun q : Fin m → ℚ => fun i => (q i : ℝ))
      (fun a b : Fin m → ℝ => ∑ i, |a i - b i|)
      (fun n a b => C00.abs_norm_linearMap_ofArray_sub_le (L (σ n)) (hunit (σ n)) a b)
      (fun a ε hε => exists_rational_coefficients a ε hε)
      (hrat m) a
  refine ⟨σ, hσ, ?_⟩
  intro x
  obtain ⟨m, a, ha⟩ := C00.exists_ofArray x
  rw [← ha]
  exact hreal m a

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SpreadingLimit
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.OrderedNorm.instCoeFunForallC00Real _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace MarkovSuperreflexivity

namespace SpreadingLimit

section PointwiseLimit

variable {E Y : Type*} [AddCommGroup E] [Module ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

variable (L : ℕ → E →ₗ[ℝ] Y)
  (hCauchy : ∀ x, CauchySeq (fun n => ‖L n x‖))

theorem tendsto_limitSeminorm (x : E) :
    Tendsto (fun n => ‖L n x‖) atTop (𝓝 (limitSeminorm L hCauchy x)) :=
  tendsto_normLimit L hCauchy x

theorem limitSeminorm_le (x : E) (b : ℝ)
    (hb : ∀ᶠ n in atTop, ‖L n x‖ ≤ b) :
    limitSeminorm L hCauchy x ≤ b :=
  le_of_tendsto (tendsto_limitSeminorm L hCauchy x) hb

theorem le_limitSeminorm_of_error (x : E) (b : ℝ) (error : ℕ → ℝ)
    (herror : Tendsto error atTop (𝓝 0))
    (hb : ∀ᶠ n in atTop, b - error n ≤ ‖L n x‖) :
    b ≤ limitSeminorm L hCauchy x := by
  have h := le_of_tendsto_of_tendsto
    (tendsto_const_nhds.sub herror) (tendsto_limitSeminorm L hCauchy x) hb
  simpa only [sub_zero] using h

theorem limitSeminorm_le_limitSeminorm_of_error (x y : E) (error : ℕ → ℝ)
    (herror : Tendsto error atTop (𝓝 0))
    (hxy : ∀ᶠ n in atTop, ‖L n x‖ ≤ ‖L n y‖ + error n) :
    limitSeminorm L hCauchy x ≤ limitSeminorm L hCauchy y := by
  have h := le_of_tendsto_of_tendsto (tendsto_limitSeminorm L hCauchy x)
    ((tendsto_limitSeminorm L hCauchy y).add herror) hxy
  simpa only [add_zero] using h

theorem limitSeminorm_eq_of_error (x y : E) (error : ℕ → ℝ)
    (herror : Tendsto error atTop (𝓝 0))
    (hxy : ∀ᶠ n in atTop, |‖L n x‖ - ‖L n y‖| ≤ error n) :
    limitSeminorm L hCauchy x = limitSeminorm L hCauchy y := by
  apply le_antisymm
  · apply limitSeminorm_le_limitSeminorm_of_error L hCauchy x y error herror
    filter_upwards [hxy] with n hn
    have h := (abs_le.mp hn).2
    linarith
  · apply limitSeminorm_le_limitSeminorm_of_error L hCauchy y x error herror
    filter_upwards [hxy] with n hn
    have h := (abs_le.mp hn).1
    linarith

end PointwiseLimit

theorem coordinate_lower_of_prefix (p : Seminorm ℝ C00) (d : ℝ) (hd : 0 ≤ d)
    (hprefix : ∀ x r, d * |prefixCut x r| ≤ p x) (x : C00) (i : ℕ) :
    (d / 2) * |x i| ≤ p x := by
  have hcoord : |x i| ≤ |prefixCut x (i + 1)| + |prefixCut x i| := by
    calc
      |x i| = |prefixCut x (i + 1) + -(prefixCut x i)| := by
        rw [prefixCut_succ]
        congr 1
        ring
      _ ≤ |prefixCut x (i + 1)| + |-(prefixCut x i)| := abs_add_le _ _
      _ = |prefixCut x (i + 1)| + |prefixCut x i| := by rw [abs_neg]
  have hmul := mul_le_mul_of_nonneg_left hcoord hd
  have h0 := hprefix x i
  have h1 := hprefix x (i + 1)
  nlinarith

end SpreadingLimit

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SpreadingConstruction
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.OrderedNorm.instCoeFunForallC00Real _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped BigOperators Topology

namespace MarkovSuperreflexivity

private theorem nat_tendsto_atTop_of_id_le (f : ℕ → ℕ) (hf : ∀ n, n ≤ f n) :
    Tendsto f atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro b
  exact Filter.eventually_atTop.2 ⟨b, fun n hn => hn.trans (hf n)⟩

private theorem seminorm_spreading_of_cube (p : Seminorm ℝ C00)
    (hcube : ∀ {m : ℕ} (ι : Fin m → ℕ), StrictMono ι →
      ∀ a : Fin m → ℝ, (∀ i, |a i| ≤ 1) →
        p (C00.place ι a) = p (C00.ofArray a)) :
    ∀ {m : ℕ} (ι : Fin m → ℕ), StrictMono ι →
      ∀ a : Fin m → ℝ, p (C00.place ι a) = p (C00.ofArray a) := by
  intro m ι hι a
  let c : ℝ := (∑ i, |a i|) + 1
  have hc : 0 < c := by
    have hsum := Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) =>
      abs_nonneg (a i))
    dsimp only [c]
    linarith
  let b : Fin m → ℝ := c⁻¹ • a
  have hab : c • b = a := by simp only [b, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  have hb : ∀ i, |b i| ≤ 1 := by
    intro i
    have hi : |a i| ≤ c := by
      have hs := Finset.single_le_sum
        (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => abs_nonneg (a j))
        (Finset.mem_univ i)
      dsimp only [c]
      linarith
    change |c⁻¹ * a i| ≤ 1
    rw [abs_mul, abs_of_pos (inv_pos.mpr hc)]
    calc
      c⁻¹ * |a i| ≤ c⁻¹ * c :=
        mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hc.le)
      _ = 1 := inv_mul_cancel₀ hc.ne'
  have hplace : C00.place ι a = c • C00.place ι b := by
    simpa only [C00.placeLinear_apply, hab] using map_smul (C00.placeLinear ι) c b
  have harray : C00.ofArray a = c • C00.ofArray b := by
    simpa only [C00.arrayLinear_apply, hab] using map_smul (C00.arrayLinear m) c b
  rw [hplace, harray, map_smul_eq_mul p, map_smul_eq_mul p, hcube ι hι b hb]

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem exists_spreadingModel_of_triangular_arrays (d : ℝ) (hd : 0 < d)
    (hrows : ∀ M : ℕ, 0 < M → Nonempty (TriangularArray Y d (M : ℝ)⁻¹ M)) :
    Nonempty (SpreadingModel Y) := by
  classical
  let R : (n : ℕ) → SelectedRow Y d (n + 1) := fun n =>
    Classical.choice (exists_selectedRow d hrows (n + 1) (Nat.succ_pos n))
  let raw : ℕ → C00 →ₗ[ℝ] Y := fun n => (R n).synthesis
  have hraw : ∀ n i, ‖raw n (C00.basis i)‖ ≤ 1 :=
    fun n i => (R n).norm_synthesis_basis_le i
  obtain ⟨σ, hσ, hCauchy⟩ := exists_cauchy_subsequence raw hraw
  let L : ℕ → C00 →ₗ[ℝ] Y := fun n => raw (σ n)
  let p : Seminorm ℝ C00 := SpreadingLimit.limitSeminorm L hCauchy
  have hunit : ∀ n i, ‖L n (C00.basis i)‖ ≤ 1 := fun n i => hraw (σ n) i
  have hσle : ∀ n, n ≤ σ n := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih => exact Nat.succ_le_of_lt (ih.trans_lt (hσ (Nat.lt_succ_self n)))
  have hkTop : Tendsto (fun n => σ n + 1) atTop atTop :=
    nat_tendsto_atTop_of_id_le _ (fun n => (hσle n).trans (Nat.le_succ _))
  have hMTop : Tendsto (fun n => (R (σ n)).M) atTop atTop :=
    nat_tendsto_atTop_of_id_le _
      (fun n => (hσle n).trans ((Nat.le_succ _).trans (R (σ n)).le_M))
  have hprefix : ∀ x r, d * |prefixCut x r| ≤ p x := by
    intro x r
    obtain ⟨m, a, rfl⟩ := C00.exists_ofArray x
    let error : ℕ → ℝ := fun n => ((R (σ n)).M : ℝ)⁻¹ * coefficientL1 a
    have herror : Tendsto error atTop (𝓝 0) := by
      simpa only [error, Function.comp_apply, mul_zero, zero_mul] using
        ((tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hMTop).mul tendsto_const_nhds
    apply SpreadingLimit.le_limitSeminorm_of_error L hCauchy
      (C00.ofArray a) (d * |prefixCut (C00.ofArray a) r|) error herror
    apply Filter.eventually_atTop.2
    refine ⟨m, ?_⟩
    intro n hn
    have hm : m ≤ σ n + 1 := hn.trans ((hσle n).trans (Nat.le_succ _))
    exact (R (σ n)).synthesis_prefix_lower hd.le hm a r
  have hupper : ∀ {m : ℕ} (a : Fin m → ℝ), p (C00.ofArray a) ≤ ∑ i, |a i| := by
    intro m a
    exact SpreadingLimit.limitSeminorm_le L hCauchy (C00.ofArray a) (∑ i, |a i|)
      (Filter.Eventually.of_forall (fun n =>
        C00.norm_linearMap_ofArray_le (L n) (hunit n) a))
  have hspreadCube : ∀ {m : ℕ} (ι : Fin m → ℕ), StrictMono ι →
      ∀ a : Fin m → ℝ, (∀ i, |a i| ≤ 1) →
        p (C00.place ι a) = p (C00.ofArray a) := by
    intro m ι hι a ha
    let K : ℕ := max m ((Finset.univ.sup ι) + 1)
    let error : ℕ → ℝ := fun n => 3 / ((σ n + 1 : ℕ) : ℝ)
    have herror : Tendsto error atTop (𝓝 0) :=
      (tendsto_const_div_atTop_nhds_zero_nat 3).comp hkTop
    apply SpreadingLimit.limitSeminorm_eq_of_error L hCauchy
      (C00.place ι a) (C00.ofArray a) error herror
    apply Filter.eventually_atTop.2
    refine ⟨K, ?_⟩
    intro n hn
    have hK : K ≤ σ n + 1 := hn.trans ((hσle n).trans (Nat.le_succ _))
    have hm : m ≤ σ n + 1 := (le_max_left _ _).trans hK
    have hιk : ∀ i, ι i < σ n + 1 := by
      intro i
      exact (Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i))).trans_le
        ((le_max_right _ _).trans hK)
    exact (R (σ n)).synthesis_oscillation hm ι Fin.val hι
      (fun _ _ h => h) hιk (fun i => i.isLt.trans_le hm) a ha
  have hspread : ∀ {m : ℕ} (ι : Fin m → ℕ), StrictMono ι →
      ∀ a : Fin m → ℝ, p (C00.place ι a) = p (C00.ofArray a) := by
    intro m ι hι a
    exact seminorm_spreading_of_cube p hspreadCube ι hι a
  have hembed : ∀ (m : ℕ) (η : ℝ), 0 < η →
      ∃ T : (Fin m → ℝ) →ₗ[ℝ] Y, ∀ a,
        p (C00.ofArray a) ≤ ‖T a‖ ∧ ‖T a‖ ≤ (1 + η) * p (C00.ofArray a) := by
    intro m η hη
    let q : Seminorm ℝ (Fin m → ℝ) := p.comp (C00.arrayLinear m)
    let S : ℕ → (Fin m → ℝ) →ₗ[ℝ] Y := fun n => (L n).comp (C00.arrayLinear m)
    have hcoord : ∀ a i, (d / 2) * |a i| ≤ q a := by
      intro a i
      simpa only [q, Seminorm.comp_apply, C00.arrayLinear_apply, C00.ofArray_apply] using
        SpreadingLimit.coordinate_lower_of_prefix p d hd.le hprefix (C00.ofArray a) i.val
    have hlip : ∀ n a b, |‖S n a‖ - ‖S n b‖| ≤ ∑ i, |a i - b i| :=
      fun n a b => C00.abs_norm_linearMap_ofArray_sub_le (L n) (hunit n) a b
    have hlim : ∀ a, Tendsto (fun n => ‖S n a‖) atTop (𝓝 (q a)) :=
      fun a => SpreadingLimit.tendsto_limitSeminorm L hCauchy (C00.ofArray a)
    exact exists_coordinate_embedding_of_convergence q d hd hcoord S hlip hlim η hη
  exact ⟨⟨p, d, hd, hprefix, hupper, hspread, hembed⟩⟩

theorem exists_spreadingModel_of_nonreflexive [CompleteSpace Y]
    (hNR : ¬ Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ Y)) :
    Nonempty (SpreadingModel Y) := by
  obtain ⟨d, hd, hrows⟩ := exists_uniform_triangular_arrays hNR
  exact exists_spreadingModel_of_triangular_arrays d hd hrows

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SeminormUniformApproximation
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped NNReal Topology

namespace MarkovSuperreflexivity.SeminormApproximation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem continuous_of_norm_bound (p : Seminorm ℝ E) (C : ℝ≥0)
    (hp : ∀ x, p x ≤ (C : ℝ) * ‖x‖) : Continuous p := by
  have h : LipschitzWith C (fun x => p x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_eq_norm] using (p.norm_sub_map_le_sub x y).trans (hp (x - y))
  exact h.continuous

theorem exists_relative_approximation [ProperSpace E]
    (p : ℕ → Seminorm ℝ E) (q : Seminorm ℝ E)
    (ha : ∀ x, Antitone fun n => p n x)
    (ht : ∀ x, Tendsto (fun n => p n x) atTop (𝓝 (q x)))
    (C : ℝ≥0) (hC : ∀ n x, p n x ≤ (C : ℝ) * ‖x‖)
    {d : ℝ} (hd : 0 < d) (hcoerce : ∀ x, d * ‖x‖ ≤ q x)
    {η : ℝ} (hη : 0 < η) :
    ∃ n : ℕ, ∀ x, q x ≤ p n x ∧ p n x ≤ (1 + η) * q x := by
  have hqp (x : E) (n : ℕ) : q x ≤ p n x := by
    apply le_of_tendsto (ht x)
    filter_upwards [eventually_ge_atTop n] with k hnk
    exact ha x hnk
  have hqC (x : E) : q x ≤ (C : ℝ) * ‖x‖ :=
    (hqp x 0).trans (hC 0 x)
  have hu : TendstoUniformlyOn (fun n x => p n x) q atTop
      (Metric.closedBall (0 : E) 1) :=
    Antitone.tendstoUniformlyOn_of_forall_tendsto
      (isCompact_closedBall (0 : E) 1)
      (fun n => (continuous_of_norm_bound (p n) C (hC n)).continuousOn)
      (fun x _ => ha x)
      (continuous_of_norm_bound q C hqC).continuousOn
      (fun x _ => ht x)
  obtain ⟨n, hn⟩ :=
    (Metric.tendstoUniformlyOn_iff.mp hu (η * d) (mul_pos hη hd)).exists
  refine ⟨n, fun x => ⟨hqp x n, ?_⟩⟩
  by_cases hx0 : x = 0
  · simp only [hx0, map_zero, mul_zero, le_refl]
  have hx : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  let v : E := ‖x‖⁻¹ • x
  have hv : ‖v‖ = 1 := by
    simp only [v, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx),
      inv_mul_cancel₀ (ne_of_gt hx)]
  have hxv : ‖x‖ • v = x := by
    simp only [v, smul_smul, mul_inv_cancel₀ (ne_of_gt hx), one_smul]
  have hvball : v ∈ Metric.closedBall (0 : E) 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right, hv] using (le_refl (1 : ℝ))
  have herr : p n v - q v < η * d := by
    have hdist := hn v hvball
    have habs : |p n v - q v| < η * d := by
      simpa only [Real.dist_eq, abs_sub_comm] using hdist
    exact (le_abs_self _).trans_lt habs
  have hdv : d ≤ q v := by simpa only [hv, mul_one] using hcoerce v
  have hvbound : p n v ≤ (1 + η) * q v := by nlinarith
  have hscale (s : Seminorm ℝ E) : s x = ‖x‖ * s v := by
    calc
      s x = s (‖x‖ • v) := congrArg s hxv.symm
      _ = ‖x‖ * s v := by
        rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)]
  rw [hscale (p n), hscale q]
  calc
    ‖x‖ * p n v ≤ ‖x‖ * ((1 + η) * q v) :=
      mul_le_mul_of_nonneg_left hvbound hx.le
    _ = (1 + η) * (‖x‖ * q v) := by ring

end MarkovSuperreflexivity.SeminormApproximation

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SubdivisionLimit
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.OrderedNorm.instCoeFunForallC00Real _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped BigOperators Topology

namespace MarkovSuperreflexivity

namespace SpreadingModel

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem averaged_prefix_lower (S : SpreadingModel Y) (x : C00) (k : ℕ) :
    S.d * |prefixCut x k| ≤ S.averagedSeminorm x :=
  SeminormLimit.prefix_lower S.subdivisionFamily S.subdivisionFamily_antitone S.d
    S.subdivisionFamily_prefix_lower x k

theorem averaged_coordinate_lower (S : SpreadingModel Y) (x : C00) (i : ℕ) :
    (S.d / 2) * |x i| ≤ S.averagedSeminorm x :=
  SpreadingLimit.coordinate_lower_of_prefix S.averagedSeminorm S.d S.d_pos.le
    S.averaged_prefix_lower x i

end SpreadingModel

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SubdivisionNearIsometry
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.OrderedNorm.instCoeFunForallC00Real _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators NNReal

namespace MarkovSuperreflexivity

namespace C00

theorem ofArray_uniformArrayMap (q m : ℕ) (a : Fin m → ℝ) :
    ofArray (uniformArrayMap q m a) = uniformSubdivision q (ofArray a) :=
  ofArray_of_vanishes (uniformSubdivision q (ofArray a)) (q * m)
    (fun k hk => uniformSubdivision_ofArray_apply_of_ge q a k hk)

end C00

namespace SpreadingModel

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem averaged_array_norm_lower (S : SpreadingModel Y) {m : ℕ} (a : Fin m → ℝ) :
    (S.d / 2) * ‖a‖ ≤ S.averagedSeminorm (C00.ofArray a) := by
  have hd : 0 < S.d / 2 := half_pos S.d_pos
  have hn : ‖a‖ ≤ S.averagedSeminorm (C00.ofArray a) / (S.d / 2) := by
    apply (pi_norm_le_iff_of_nonneg
      (div_nonneg (apply_nonneg S.averagedSeminorm _) hd.le)).mpr
    intro i
    apply (le_div_iff₀ hd).mpr
    simpa only [Real.norm_eq_abs, C00.ofArray_apply, mul_comm] using
      S.averaged_coordinate_lower (C00.ofArray a) i.val
  simpa only [mul_comm] using (le_div_iff₀ hd).mp hn

theorem subdivisionFamily_array_norm_upper (S : SpreadingModel Y) (n : ℕ)
    {m : ℕ} (a : Fin m → ℝ) :
    S.subdivisionFamily n (C00.ofArray a) ≤ (m : ℝ) * ‖a‖ := by
  have hfirst := S.subdivisionFamily_upper n (C00.ofArray a)
  rw [C00.l1Mass_ofArray] at hfirst
  apply hfirst.trans
  simpa only [Real.norm_eq_abs, Fintype.card_fin, nsmul_eq_mul] using
    (Pi.sum_norm_apply_le_norm (f := a))

theorem exists_uniform_nearIsometry (S : SpreadingModel Y) (m : ℕ)
    {η : ℝ} (hη : 0 < η) :
    ∃ q : ℕ, 0 < q ∧ ∀ a : Fin m → ℝ,
      S.averagedSeminorm (C00.ofArray a) ≤
          S.p (C00.ofArray (C00.uniformArrayMap q m a)) ∧
        S.p (C00.ofArray (C00.uniformArrayMap q m a)) ≤
          (1 + η) * S.averagedSeminorm (C00.ofArray a) := by
  let p : ℕ → Seminorm ℝ (Fin m → ℝ) :=
    fun n => (S.subdivisionFamily n).comp (C00.arrayLinear m)
  let q : Seminorm ℝ (Fin m → ℝ) := S.averagedSeminorm.comp (C00.arrayLinear m)
  obtain ⟨n, hn⟩ := SeminormApproximation.exists_relative_approximation p q
    (fun a => S.subdivisionFamily_antitone (C00.ofArray a))
    (fun a => S.tendsto_averagedSeminorm (C00.ofArray a))
    (m : ℝ≥0) (fun n a => S.subdivisionFamily_array_norm_upper n a)
    (half_pos S.d_pos) (fun a => S.averaged_array_norm_lower a) hη
  refine ⟨n + 1, Nat.succ_pos n, ?_⟩
  intro a
  simp only [C00.ofArray_uniformArrayMap]
  change q a ≤ p n a ∧ p n a ≤ (1 + η) * q a
  exact hn a

end SpreadingModel

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SubdivisionOrderedNorm
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instFiniteDimensionalReal _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instModuleReal _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNorm _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

namespace SpreadingModel

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem orderedNorm_representable (S : SpreadingModel Y) :
    CoordinatesRepresentable Y S.orderedNorm := by
  apply CoordinatesRepresentable.of_factorization S.orderedNorm S.p
  · intro m η hη
    obtain ⟨q, hq, hqbound⟩ := S.exists_uniform_nearIsometry m hη
    exact ⟨q * m, C00.uniformArrayMap q m, hqbound⟩
  · exact S.embeddings

end SpreadingModel

theorem exists_orderedNorm_of_spreadingModel
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (S : SpreadingModel Y) :
    ∃ N : OrderedNorm, CoordinatesRepresentable Y N :=
  ⟨S.orderedNorm, S.orderedNorm_representable⟩

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_ScalarUltralimit
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace MarkovSuperreflexivity

variable {f g : ℕ → ℝ}

theorem tendsto_freeUltrafilter_of_tendsto_atTop {α : Type*} [TopologicalSpace α]
    {a : ℕ → α} {x : α} (h : Tendsto a atTop (𝓝 x)) :
    Tendsto a (freeUltrafilter : Filter ℕ) (𝓝 x) :=
  h.mono_left freeUltrafilter_le_atTop

theorem realULim_freeUltrafilter_eq_of_tendsto_atTop {a : ℝ}
    (h : Tendsto f atTop (𝓝 a)) : realULim freeUltrafilter f = a :=
  realULim_eq_of_tendsto freeUltrafilter (tendsto_freeUltrafilter_of_tendsto_atTop h)

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_TriangularLimitSeminorm
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.OrderedNorm.instCoeFunForallC00Real _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped BigOperators

namespace MarkovSuperreflexivity
namespace TriangularLimit

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {θ : ℝ}

theorem basis_bound (s : ∀ n : ℕ, TriangularSystem X n θ) (i : ℕ) :
    limitNorm s (C00.basis i) ≤ 1 := by
  apply realULim_le_of_eventually_le freeUltrafilter (bounded s (C00.basis i))
  apply Eventually.of_forall
  intro n
  simpa only [finiteSeminorm_apply, realize, C00.basis,
    Finsupp.linearCombination_single, one_smul] using vectorAt_bound s n i

end TriangularLimit
end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_TriangularCompletion
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity
namespace TriangularLimit

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {θ : ℝ}

theorem norm_basis_le (s : ∀ n : ℕ, TriangularSystem X n θ) (hθ : 0 < θ) (i : ℕ) :
    ‖basis s hθ i‖ ≤ 1 := by
  rw [basis, norm_ofC00]
  exact basis_bound s i

theorem norm_tail_le (s : ∀ n : ℕ, TriangularSystem X n θ) (hθ : 0 < θ) (j : ℕ) :
    ‖tail s hθ j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  refine UniformSpace.Completion.induction_on z
    (isClosed_le (tail s hθ j).continuous.norm (continuous_const.mul continuous_norm)) ?_
  intro a
  let b : C00 := (NormedC00.coefficients (limitNorm s) (definite s hθ)) a
  change ‖tail s hθ j (ofC00 s hθ b)‖ ≤ 1 * ‖ofC00 s hθ b‖
  rw [tail_ofC00, norm_ofC00, Real.norm_eq_abs, one_mul]
  exact tailForm_le s b j

private theorem linearCombination_basis (s : ∀ n : ℕ, TriangularSystem X n θ)
    (hθ : 0 < θ) : Finsupp.linearCombination ℝ (basis s hθ) = ofC00 s hθ := by
  apply Finsupp.lhom_ext
  intro i b
  rw [Finsupp.linearCombination_single]
  change b • ofC00 s hθ (C00.basis i) = ofC00 s hθ (Finsupp.single i b)
  rw [← map_smul]
  congr 1
  simp only [C00.basis, Finsupp.smul_single, smul_eq_mul, mul_one]

theorem dense_span_basis (s : ∀ n : ℕ, TriangularSystem X n θ) (hθ : 0 < θ) :
    Dense (Submodule.span ℝ (Set.range (basis s hθ)) : Set (Space s hθ)) := by
  have hd : Dense (Set.range ((↑) : PreSpace s hθ → Space s hθ)) :=
    UniformSpace.Completion.denseRange_coe
  apply hd.mono
  rintro z ⟨a, rfl⟩
  rw [← Finsupp.range_linearCombination, linearCombination_basis]
  refine ⟨(NormedC00.coefficients (limitNorm s) (definite s hθ)) a, ?_⟩
  rfl

end TriangularLimit
end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_TriangularCoordinateEmbeddings
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped BigOperators Topology

namespace MarkovSuperreflexivity
namespace TriangularLimit

universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {θ : ℝ}

private theorem realize_ofArray_bound (s : ∀ n : ℕ, TriangularSystem X n θ)
    (n : ℕ) {m : ℕ} (a : Fin m → ℝ) :
    ‖realize s n (C00.ofArray a)‖ ≤ ∑ i, |a i| := by
  classical
  change ‖realize s n (∑ i, Finsupp.single i.val (a i))‖ ≤ _
  rw [map_sum]
  apply norm_sum_le_of_le
  intro i hi
  rw [realize, Finsupp.linearCombination_single, norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (vectorAt_bound s n i.val) (abs_nonneg _)).trans_eq
    (mul_one _)

theorem coordinate_embeddings (s : ∀ n : ℕ, TriangularSystem X n θ) (hθ : 0 < θ)
    (m : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ T : (Fin m → ℝ) →ₗ[ℝ] X, ∀ a,
      limitNorm s (C00.ofArray a) ≤ ‖T a‖ ∧
        ‖T a‖ ≤ (1 + η) * limitNorm s (C00.ofArray a) := by
  classical
  let C := NormedC00.coefficients (limitNorm s) (definite s hθ)
  let F : (Fin m → ℝ) →ₗ[ℝ] PreSpace s hθ := C.symm.toLinearMap.comp (C00.arrayLinear m)
  let E : Submodule ℝ (PreSpace s hθ) := LinearMap.range F
  let : FiniteDimensional ℝ E := LinearMap.finiteDimensional_range F
  let read : E →ₗ[ℝ] (Fin m → ℝ) :=
    { toFun := fun x i => C (x : PreSpace s hθ) i.val
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let readL : E →L[ℝ] (Fin m → ℝ) := ⟨read, read.continuous_of_finiteDimensional⟩
  let A : ℕ → E →ₗ[ℝ] X := fun n =>
    (realize s n).comp (C.toLinearMap.comp E.subtype)
  let K : ℝ := (m : ℝ) * ‖readL‖
  have hK : 0 ≤ K := mul_nonneg (Nat.cast_nonneg m) (norm_nonneg readL)
  have hbound (n : ℕ) (x : E) : ‖A n x‖ ≤ K * ‖x‖ := by
    obtain ⟨a, ha⟩ := x.property
    have hc : C (x : PreSpace s hθ) = C00.ofArray a := by
      rw [← ha]
      rfl
    have hr : readL x = a := by
      funext i
      change C (x : PreSpace s hθ) i.val = a i
      rw [hc]
      exact C00.ofArray_apply a i
    calc
      ‖A n x‖ = ‖realize s n (C00.ofArray a)‖ := by
        change ‖realize s n (C (x : PreSpace s hθ))‖ = _
        rw [hc]
      _ ≤ ∑ i, |a i| := realize_ofArray_bound s n a
      _ ≤ ∑ _i : Fin m, ‖readL x‖ := by
        apply Finset.sum_le_sum
        intro i hi
        rw [hr, ← Real.norm_eq_abs]
        exact norm_le_pi_norm a i
      _ = (m : ℝ) * ‖readL x‖ := by simp
      _ ≤ (m : ℝ) * (‖readL‖ * ‖x‖) :=
        mul_le_mul_of_nonneg_left (readL.le_opNorm x) (Nat.cast_nonneg m)
      _ = K * ‖x‖ := (mul_assoc _ _ _).symm
  have hlim (x : E) :
      Tendsto (fun n => ‖A n x‖) (freeUltrafilter : Filter ℕ) (𝓝 ‖x‖) := by
    exact tendsto_realULim freeUltrafilter (bounded s (C (x : PreSpace s hθ)))
  obtain ⟨S, hS⟩ := exists_near_isometric_map_of_pointwise
    (freeUltrafilter : Filter ℕ) A K hK hbound hlim hη
  refine ⟨S.comp F.rangeRestrict, ?_⟩
  intro a
  have hnorm : ‖F.rangeRestrict a‖ = limitNorm s (C00.ofArray a) := rfl
  simpa only [LinearMap.comp_apply, hnorm] using hS (F.rangeRestrict a)

end TriangularLimit
end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_TriangularNonreflexivity
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace MarkovSuperreflexivity

universe u

variable {Z : Type u} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem unitSequenceBidual_eval_of_eventually_eq
    (e : ℕ → Z) (he : ∀ i, ‖e i‖ ≤ 1) (g : StrongDual ℝ Z) {a : ℝ}
    (h : ∀ᶠ i in atTop, g (e i) = a) : unitSequenceBidual e he g = a := by
  rw [unitSequenceBidual_apply]
  apply realULim_freeUltrafilter_eq_of_tendsto_atTop
  exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => a) atTop (𝓝 a)).congr' (h.mono fun _ hi => hi.symm)

theorem triangular_eventually_zero_on_span
    (e : ℕ → Z) (f : ℕ → StrongDual ℝ Z) {θ : ℝ}
    (hpair : ∀ i j, f j (e i) = if j ≤ i then θ else 0)
    {x : Z} (hx : x ∈ Submodule.span ℝ (Set.range e)) :
    ∀ᶠ j in atTop, f j x = 0 := by
  have hspan : Submodule.span ℝ (Set.range e) ≤ eventualKernelSubmodule f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change ∀ᶠ j in atTop, f j (e i) = 0
    refine Filter.eventually_atTop.mpr ⟨i + 1, ?_⟩
    intro j hji
    rw [hpair]
    exact ite_eq_right (Nat.not_le_of_lt ((Nat.lt_succ_self i).trans_le hji))
  exact hspan hx

theorem triangular_functionals_tendsto_zero
    (e : ℕ → Z) (f : ℕ → StrongDual ℝ Z)
    (hf : ∀ j, ‖f j‖ ≤ 1) {θ : ℝ}
    (hpair : ∀ i j, f j (e i) = if j ≤ i then θ else 0)
    (hdense : Dense (Submodule.span ℝ (Set.range e) : Set Z)) (x : Z) :
    Tendsto (fun j => f j x) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := hdense.exists_dist_lt x hε
  apply (triangular_eventually_zero_on_span e f hpair hy).mono
  intro j hj
  calc
    dist (f j x) 0 = ‖f j x‖ := dist_zero_right _
    _ = ‖f j (x - y)‖ := by rw [map_sub, hj, sub_zero]
    _ ≤ ‖f j‖ * ‖x - y‖ := (f j).le_opNorm (x - y)
    _ ≤ 1 * ‖x - y‖ := mul_le_mul_of_nonneg_right (hf j) (norm_nonneg _)
    _ = dist x y := by rw [one_mul, dist_eq_norm]
    _ < ε := hxy

theorem not_canonicallyReflexive_of_triangular_dense
    (e : ℕ → Z) (he : ∀ i, ‖e i‖ ≤ 1)
    (f : ℕ → StrongDual ℝ Z) (hf : ∀ j, ‖f j‖ ≤ 1)
    {θ : ℝ} (hθ : 0 < θ)
    (hpair : ∀ i j, f j (e i) = if j ≤ i then θ else 0)
    (hdense : Dense (Submodule.span ℝ (Set.range e) : Set Z)) :
    ¬ CanonicallyReflexive Z := by
  intro hR
  obtain ⟨x, hx⟩ := hR (unitSequenceBidual e he)
  have hvalue (j : ℕ) : f j x = θ := by
    have hulim : unitSequenceBidual e he (f j) = θ := by
      apply unitSequenceBidual_eval_of_eventually_eq
      refine Filter.eventually_atTop.mpr ⟨j, ?_⟩
      intro i hji
      rw [hpair, ite_eq_left hji]
    have hxj := congrArg (fun v : StrongDual ℝ (StrongDual ℝ Z) => v (f j)) hx
    change f j x = unitSequenceBidual e he (f j) at hxj
    exact hxj.trans hulim
  have hzero := triangular_functionals_tendsto_zero e f hf hpair hdense x
  have hconstant : (fun j => f j x) = (fun _ : ℕ => θ) := funext hvalue
  rw [hconstant] at hzero
  have hθ0 : θ = 0 := tendsto_nhds_unique tendsto_const_nhds hzero
  exact (ne_of_gt hθ) hθ0

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_TriangularCounterexample
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem triangular_family_of_not_obstruction (h : ¬ FiniteTriangularObstruction X) :
    ∃ (θ : ℝ), 0 < θ ∧ θ < 1 ∧ Nonempty (∀ n : ℕ, TriangularSystem X n θ) := by
  classical
  unfold FiniteTriangularObstruction at h
  push Not at h
  obtain ⟨θ, hθ, hθ1, hall⟩ := h
  let s : ∀ n : ℕ, TriangularSystem X n θ := fun n =>
    (Classical.choice (hall (n + 1) (Nat.zero_lt_succ n))).restrict (Nat.le_succ n)
  exact ⟨θ, hθ, hθ1, ⟨s⟩⟩

namespace TriangularLimit

theorem not_canonicallyReflexive {θ : ℝ}
    (s : ∀ n : ℕ, TriangularSystem X n θ) (hθ : 0 < θ) :
    ¬ CanonicallyReflexive (Space s hθ) :=
  not_canonicallyReflexive_of_triangular_dense
    (basis s hθ) (norm_basis_le s hθ) (tail s hθ) (norm_tail_le s hθ)
    hθ (pairing s hθ) (dense_span_basis s hθ)

end TriangularLimit
end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_TriangularRepresentability
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

namespace TriangularLimit

theorem finitelyRepresentable {θ : ℝ}
    (s : ∀ n : ℕ, TriangularSystem X n θ) (hθ : 0 < θ) :
    FinitelyRepresentable (Space s hθ) X :=
  finitelyRepresentable_completion_of_coordinates (limitNorm s) (definite s hθ)
    (coordinate_embeddings s hθ)

end TriangularLimit

theorem exists_nonreflexive_finitelyRepresentable_of_not_obstruction
    (h : ¬ FiniteTriangularObstruction X) :
    ∃ (θ : ℝ) (hθ : 0 < θ) (s : ∀ n : ℕ, TriangularSystem X n θ),
      FinitelyRepresentable (TriangularLimit.Space s hθ) X ∧
        ¬ CanonicallyReflexive (TriangularLimit.Space s hθ) := by
  obtain ⟨θ, hθ, _hθ1, ⟨s⟩⟩ := triangular_family_of_not_obstruction h
  exact ⟨θ, hθ, s, TriangularLimit.finitelyRepresentable s hθ,
    TriangularLimit.not_canonicallyReflexive s hθ⟩

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_RenormedGeometry
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

namespace Renormed

@[simp] theorem normSeminorm_comp_original (N : EquivalentNorm X) :
    (normSeminorm ℝ (Renormed N)).comp (linearEquiv N).toLinearMap = N.p := by
  ext x
  rfl

@[simp] theorem originalSeminorm_comp_inverse (N : EquivalentNorm X) :
    N.p.comp (linearEquiv N).symm.toLinearMap = normSeminorm ℝ (Renormed N) := by
  ext x
  rfl

end Renormed
end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_JamesEnflo
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

universe u v
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {Y : Type v} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem exists_nonreflexive_finitelyRepresentable_of_not_hasEquivalentUCNorm
    (h : ¬ HasEquivalentUCNorm X) :
    ∃ (θ : ℝ) (hθ : 0 < θ) (s : ∀ n, TriangularSystem X n θ),
      FinitelyRepresentable (TriangularLimit.Space s hθ) X ∧
        ¬ CanonicallyReflexive (TriangularLimit.Space s hθ) := by
  apply exists_nonreflexive_finitelyRepresentable_of_not_obstruction
  exact fun hObstruction => h (hasEquivalentUCNorm_of_finiteTriangularObstruction hObstruction)

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_MarkovTransport
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

theorem stateCost_reindex {S T X : Type*} [Fintype S] [Fintype T]
    [NormedAddCommGroup X] (C : FiniteReversibleChain S) (e : T ≃ S)
    (f : S → X) (p : ℝ) (n : ℕ) :
    stateCost (C.reindex e) (f ∘ e) p n = stateCost C f p n := by
  let ePath : StatePath T n ≃ StatePath S n := Equiv.piCongrRight (fun _ => e)
  let G : StatePath S n → ℝ := fun ω =>
    pathWeight C n ω * Real.rpow (‖f (ω (Fin.last n)) - f (ω 0)‖) p
  change (∑ ω : StatePath T n, G (ePath ω)) = ∑ ω : StatePath S n, G ω
  exact ePath.sum_comp G

theorem MarkovTypeWith.bound {X S : Type*} [NormedAddCommGroup X] [Fintype S]
    {p K : ℝ} (hX : MarkovTypeWith p K X) (C : FiniteReversibleChain S)
    (f : S → X) (n : ℕ) (hn : 1 ≤ n) :
    stateCost C f p n ≤ Real.rpow K p * (n : ℝ) * stateCost C f p 1 := by
  let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  have h := hX.2.2 (Fintype.card S) (C.reindex e) (f ∘ e) n hn
  simpa only [stateCost_reindex] using h

theorem stateCost_le_mul_of_norm_le {S X Y : Type*} [Fintype S]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    (C : FiniteReversibleChain S) (f : S → X) (g : S → Y)
    {p c : ℝ} (hp : 0 ≤ p) (hc : 0 ≤ c)
    (hfg : ∀ i j, ‖f j - f i‖ ≤ c * ‖g j - g i‖) (n : ℕ) :
    stateCost C f p n ≤ Real.rpow c p * stateCost C g p n := by
  calc
    stateCost C f p n ≤
        ∑ ω : StatePath S n, pathWeight C n ω *
          (Real.rpow c p * Real.rpow (‖g (ω (Fin.last n)) - g (ω 0)‖) p) := by
      apply Finset.sum_le_sum
      intro ω _
      apply mul_le_mul_of_nonneg_left _ (pathWeight_nonneg C n ω)
      calc
        Real.rpow (‖f (ω (Fin.last n)) - f (ω 0)‖) p ≤
            Real.rpow (c * ‖g (ω (Fin.last n)) - g (ω 0)‖) p :=
          Real.rpow_le_rpow (norm_nonneg _) (hfg _ _) hp
        _ = Real.rpow c p * Real.rpow (‖g (ω (Fin.last n)) - g (ω 0)‖) p :=
          Real.mul_rpow hc (norm_nonneg _)
    _ = Real.rpow c p * stateCost C g p n := by
      simp only [stateCost, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω _
      ring

theorem MarkovTypeWith.of_distortion_map {X Y : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup Y] {p K a b : ℝ}
    (hX : MarkovTypeWith p K X) (T : Y → X) (ha : 0 < a) (hb : 0 < b)
    (hlower : ∀ y z, a * ‖y - z‖ ≤ ‖T y - T z‖)
    (hupper : ∀ y z, ‖T y - T z‖ ≤ b * ‖y - z‖) :
    MarkovTypeWith p ((b / a) * K) Y := by
  refine ⟨hX.1, mul_pos (div_pos hb ha) hX.2.1, ?_⟩
  intro m C f n hn
  have hInv : 0 ≤ a⁻¹ := (inv_pos.mpr ha).le
  have hlo : ∀ i j, ‖f j - f i‖ ≤ a⁻¹ * ‖T (f j) - T (f i)‖ := by
    intro i j
    have h := mul_le_mul_of_nonneg_left (hlower (f j) (f i)) hInv
    simpa only [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul] using h
  have hhi : ∀ i j, ‖T (f j) - T (f i)‖ ≤ b * ‖f j - f i‖ :=
    fun i j => hupper (f j) (f i)
  have hkn : 0 ≤ Real.rpow K p * (n : ℝ) :=
    mul_nonneg (Real.rpow_nonneg hX.2.1.le _) (Nat.cast_nonneg _)
  calc
    stateCost C f p n ≤ Real.rpow (a⁻¹) p * stateCost C (T ∘ f) p n :=
      stateCost_le_mul_of_norm_le C f (T ∘ f) hX.1.le hInv hlo n
    _ ≤ Real.rpow (a⁻¹) p *
        (Real.rpow K p * (n : ℝ) * stateCost C (T ∘ f) p 1) :=
      mul_le_mul_of_nonneg_left (hX.bound C (T ∘ f) n hn)
        (Real.rpow_nonneg hInv _)
    _ ≤ Real.rpow (a⁻¹) p *
        (Real.rpow K p * (n : ℝ) * (Real.rpow b p * stateCost C f p 1)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hInv _)
      exact mul_le_mul_of_nonneg_left
        (stateCost_le_mul_of_norm_le C (T ∘ f) f hX.1.le hb.le hhi 1) hkn
    _ = Real.rpow ((b / a) * K) p * (n : ℝ) * stateCost C f p 1 := by
      simp only [Real.rpow_eq_pow]
      rw [Real.mul_rpow (div_pos hb ha).le hX.2.1.le,
        div_eq_mul_inv b a, Real.mul_rpow hb.le hInv]
      ring

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_OrderedNormConstruction
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instFiniteDimensionalReal _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instModuleReal _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNorm _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

universe u v

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

theorem exists_orderedNorm_of_nonreflexive_finitelyRepresentable
    (hNR : ¬ CanonicallyReflexive Y) (hYX : FinitelyRepresentable Y X) :
    ∃ N : OrderedNorm, CoordinatesRepresentable X N := by
  obtain ⟨S⟩ := exists_spreadingModel_of_nonreflexive hNR
  obtain ⟨N, hNY⟩ := exists_orderedNorm_of_spreadingModel S
  exact ⟨N, hNY.transfer hYX⟩

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_OrderedNormStructural
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instFiniteDimensionalReal _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instModuleReal _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNorm _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNormedSpaceReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem orderedNorm_of_not_hasEquivalentUCNorm
    (hnot : ¬ HasEquivalentUCNorm X) :
    ∃ N : OrderedNorm, CoordinatesRepresentable X N := by
  obtain ⟨θ, hθ, s, hrep, hNR⟩ :=
    exists_nonreflexive_finitelyRepresentable_of_not_hasEquivalentUCNorm hnot
  exact exists_orderedNorm_of_nonreflexive_finitelyRepresentable hNR hrep

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_MarkovRenorming
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {p K : ℝ}

theorem MarkovTypeWith.of_renormed (N : EquivalentNorm X)
    (hN : MarkovTypeWith p K (Renormed N)) :
    MarkovTypeWith p ((N.upper / N.lower) * K) X := by
  apply hN.of_distortion_map (Renormed.ofOriginal N) N.lower_pos N.upper_pos
  · intro x y
    change N.lower * ‖x - y‖ ≤ N.p (x - y)
    exact N.lower_bound (x - y)
  · intro x y
    change N.p (x - y) ≤ N.upper * ‖x - y‖
    exact N.upper_bound (x - y)

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_ReversibleMartingales
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {S X : Type*} [Fintype S]
variable [NormedAddCommGroup X] [sectionNormedSpaceℝX : NormedSpace ℝ X]

theorem chainDrift_eq_sum (C : FiniteReversibleChain S) (f : S → X) (i : S) :
    chainDrift C f i = ∑ j, C.P i j • (f j - f i) := by
  simp only [chainDrift, chainAverage, smul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_smul, C.sum_P, one_smul]

theorem chainAverage_centered_sum (C : FiniteReversibleChain S)
    (f : S → X) (i : S) :
    (∑ j, C.P i j • (f j - chainAverage C f i)) = 0 := by
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul,
    C.sum_P, one_smul]
  exact sub_self _

theorem sampledForward_step (C : FiniteReversibleChain S) (f : S → X)
    {m : ℕ} (k : Fin m) (ω : StatePath S (2 * m)) :
    sampledForward C f m (k.val + 1) ω - sampledForward C f m k.val ω =
      sampledDifference C f k ω := by
  classical
  unfold sampledForward
  rw [← Finset.sum_sub_distrib]
  have he (j : Fin m) :
      (if j.val < k.val + 1 then sampledDifference C f j ω else 0) -
        (if j.val < k.val then sampledDifference C f j ω else 0) =
      if j = k then sampledDifference C f k ω else 0 := by
    by_cases hjk : j = k
    · subst j
      simp
    · have hne : j.val ≠ k.val := fun h => hjk (Fin.ext h)
      by_cases hj : j.val < k.val
      · have hj' : j.val < k.val + 1 := by omega
        simp [hj, hj', hjk]
      · have hj' : ¬ j.val < k.val + 1 := by omega
        simp [hj, hj', hjk]
  simp_rw [he]
  simp

theorem sampledForward_end (C : FiniteReversibleChain S) (f : S → X)
    (m : ℕ) (ω : StatePath S (2 * m)) :
    sampledForward C f m m ω = ∑ j : Fin m, sampledDifference C f j ω := by
  apply Finset.sum_congr rfl
  intro j hj
  exact ite_eq_left j.isLt

theorem sampledForward_fiber_constant (C : FiniteReversibleChain S) (f : S → X)
    {m : ℕ} (k : Fin m) (ω ω' : StatePath S (2 * m))
    (hkey : sampledKey m k ω = sampledKey m k ω') :
    sampledForward C f m k.val ω = sampledForward C f m k.val ω' := by
  classical
  unfold sampledForward
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hjk : j.val < k.val
  · simp only [ite_eq_left hjk]
    have he := congrFun hkey (⟨2 * j.val + 2, by omega⟩ : Fin (2 * k.val + 1))
    have ho := congrFun hkey (⟨2 * j.val + 1, by omega⟩ : Fin (2 * k.val + 1))
    change ω ⟨2 * j.val + 2, _⟩ = ω' ⟨2 * j.val + 2, _⟩ at he
    change ω ⟨2 * j.val + 1, _⟩ = ω' ⟨2 * j.val + 1, _⟩ at ho
    unfold sampledDifference sampledEvenIndex sampledOddIndex
    dsimp only [Fin.val_succ]
    simpa only [Nat.mul_add, Nat.mul_one] using
      congrArg₂ (fun a b : S => f a - chainAverage C f b) he ho
  · simp only [ite_eq_right hjk]

omit sectionNormedSpaceℝX in
private theorem sum_fin_successive_sub [NormedSpace ℝ X] {m : ℕ} (g : Fin (m + 1) → X) :
    (∑ j : Fin m, (g j.succ - g j.castSucc)) = g (Fin.last m) - g 0 := by
  have he : g 0 + (∑ j : Fin m, g j.succ) =
      (∑ j : Fin m, g j.castSucc) + g (Fin.last m) :=
    (Fin.sum_univ_succ g).symm.trans (Fin.sum_univ_castSucc g)
  rw [Finset.sum_sub_distrib]
  calc
    _ = (g 0 + ∑ j : Fin m, g j.succ) -
        ((∑ j : Fin m, g j.castSucc) + g 0) := by abel
    _ = ((∑ j : Fin m, g j.castSucc) + g (Fin.last m)) -
        ((∑ j : Fin m, g j.castSucc) + g 0) := by rw [he]
    _ = g (Fin.last m) - g 0 := by abel

theorem sampledDifference_reverse (C : FiniteReversibleChain S) (f : S → X)
    {m : ℕ} (j : Fin m) (ω : StatePath S (2 * m)) :
    sampledDifference C f j ω - sampledDifference C f j.rev (pathReverse ω) =
      f (ω (sampledEvenIndex j.succ)) - f (ω (sampledEvenIndex j.castSucc)) := by
  have ho : (sampledOddIndex j.rev).rev = sampledOddIndex j := by
    apply Fin.ext
    simp only [sampledOddIndex, Fin.val_rev]
    omega
  have he : (sampledEvenIndex j.rev.succ).rev = sampledEvenIndex j.castSucc := by
    apply Fin.ext
    simp only [sampledEvenIndex, Fin.val_rev, Fin.val_succ, Fin.val_castSucc]
    omega
  simp only [sampledDifference, pathReverse, ho, he]
  abel

theorem even_displacement_decomposition (C : FiniteReversibleChain S) (f : S → X)
    (m : ℕ) (ω : StatePath S (2 * m)) :
    f (ω (Fin.last (2 * m))) - f (ω 0) =
      sampledForward C f m m ω - sampledBackward C f m m ω := by
  classical
  rw [sampledBackward, sampledForward_end, sampledForward_end]
  let e : Fin m ≃ Fin m := Fin.revPerm
  have hs := e.sum_comp (fun j => sampledDifference C f j (pathReverse ω))
  rw [← hs, ← Finset.sum_sub_distrib]
  change _ = ∑ j : Fin m,
    (sampledDifference C f j ω - sampledDifference C f j.rev (pathReverse ω))
  simp_rw [sampledDifference_reverse]
  have h := sum_fin_successive_sub (fun j : Fin (m + 1) => f (ω (sampledEvenIndex j)))
  have hlast : sampledEvenIndex (Fin.last m) = Fin.last (2 * m) := by
    apply Fin.ext
    simp only [sampledEvenIndex, Fin.val_last]
  have hzero : sampledEvenIndex (0 : Fin (m + 1)) = 0 := by
    apply Fin.ext
    simp only [sampledEvenIndex, Fin.val_zero, Nat.mul_zero]
  simpa only [hlast, hzero] using h.symm

private theorem sum_fiber_comp_zero {Ω ι κ V : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι] [DecidableEq κ] [AddCommMonoid V]
    (key : Ω → ι) (coarse : ι → κ) (F : Ω → V)
    (hz : ∀ a, ∑ ω ∈ Finset.univ.filter (fun ω => key ω = a), F ω = 0)
    (b : κ) :
    (∑ ω ∈ Finset.univ.filter (fun ω => coarse (key ω) = b), F ω) = 0 := by
  classical
  rw [← Finset.sum_fiberwise _ key F]
  apply Finset.sum_eq_zero
  intro a ha
  by_cases hb : coarse a = b
  · have he : (Finset.univ.filter (fun ω => coarse (key ω) = b)).filter
        (fun ω => key ω = a) = Finset.univ.filter (fun ω => key ω = a) := by
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨by simpa only [h] using hb, h⟩
    rw [he]
    exact hz a
  · have he : (Finset.univ.filter (fun ω => coarse (key ω) = b)).filter
        (fun ω => key ω = a) = ∅ := by
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false, not_and]
      intro h h'
      exact hb (h' ▸ h)
    rw [he, Finset.sum_empty]

attribute [local instance] OAI.MarkovSuperreflexivity.instDecidableEq_solutions
theorem sampledDifference_fine_cancel (C : FiniteReversibleChain S) (f : S → X)
    {m : ℕ} (k : Fin m) (η : StatePath S (2 * k.val + 1)) :
    (∑ ω ∈ Finset.univ.filter
        (fun ω : StatePath S (2 * m) => pathTake (2 * k.val + 1) (by omega) ω = η),
      pathWeight C (2 * m) ω • sampledDifference C f k ω) = 0 := by
  classical
  have h := sum_pathWeight_take_next C (2 * k.val + 1) (by omega : 2 * k.val + 1 < 2 * m)
    η (fun j => f j - chainAverage C f (η (Fin.last (2 * k.val + 1))))
  rw [chainAverage_centered_sum, smul_zero] at h
  rw [Finset.sum_filter]
  calc
    _ = ∑ ω : StatePath S (2 * m),
        if pathTake (2 * k.val + 1) (by omega) ω = η then
          pathWeight C (2 * m) ω •
            (f (ω ⟨2 * k.val + 1 + 1, by omega⟩) -
              chainAverage C f (η (Fin.last (2 * k.val + 1))))
        else 0 := by
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases he : pathTake (2 * k.val + 1) (by omega) ω = η
      · have hc := congrFun he (Fin.last (2 * k.val + 1))
        change ω (sampledOddIndex k) = η (Fin.last (2 * k.val + 1)) at hc
        simp only [ite_eq_left he, sampledDifference, hc, sampledEvenIndex,
          Fin.val_succ, Nat.mul_add, Nat.mul_one, Nat.add_assoc]
      · simp only [ite_eq_right he]
    _ = 0 := h

theorem sampledForward_fiber_cancel (C : FiniteReversibleChain S) (f : S → X)
    {m : ℕ} (k : Fin m) (η : StatePath S (2 * k.val)) :
    (∑ ω ∈ Finset.univ.filter (fun ω => sampledKey m k ω = η),
      pathWeight C (2 * m) ω •
        (sampledForward C f m (k.val + 1) ω - sampledForward C f m k.val ω)) = 0 := by
  classical
  simp_rw [sampledForward_step]
  exact sum_fiber_comp_zero
    (fun ω : StatePath S (2 * m) => pathTake (2 * k.val + 1) (by omega) ω)
    (pathTake (2 * k.val) (Nat.le_succ _))
    (fun ω => pathWeight C (2 * m) ω • sampledDifference C f k ω)
    (sampledDifference_fine_cancel C f k) η

private theorem sum_weighted_two {Ω : Type*} [Fintype Ω]
    (w a b : Ω → ℝ) :
    (∑ ω, w ω * (2 * (a ω + b ω))) =
      2 * ((∑ ω, w ω * a ω) + ∑ ω, w ω * b ω) := by
  calc
    _ = ∑ ω, (2 * (w ω * a ω) + 2 * (w ω * b ω)) := by
      apply Finset.sum_congr rfl
      intro ω hω
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      ring

theorem chainDrift_q_moment_le {q : ℝ} (hq : 1 ≤ q)
    (C : FiniteReversibleChain S) (f : S → X) :
    (∑ i, C.π i * ‖chainDrift C f i‖ ^ q) ≤ stateCost C f q 1 := by
  rw [stateCost_one]
  calc
    _ ≤ ∑ i, C.π i * ∑ j, C.P i j * ‖f j - f i‖ ^ q := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (C.π_nonneg i)
      rw [chainDrift_eq_sum]
      exact finite_norm_rpow_jensen (C.P i) (fun j => f j - f i)
        (C.P_nonneg i) (C.sum_P i) hq
    _ = _ := by simp only [Finset.mul_sum, mul_assoc, Real.rpow_eq_pow]

theorem centered_edge_q_moment_le_four {q : ℝ} (hq : 1 ≤ q) (hq2 : q ≤ 2)
    (C : FiniteReversibleChain S) (f : S → X) :
    (∑ i, ∑ j, (C.π i * C.P i j) * ‖f j - chainAverage C f i‖ ^ q) ≤
      4 * stateCost C f q 1 := by
  have htriangle (i j : S) : ‖f j - chainAverage C f i‖ ^ q ≤
      2 * (‖f j - f i‖ ^ q + ‖chainDrift C f i‖ ^ q) := by
    have he : (f j - f i) - chainDrift C f i = f j - chainAverage C f i := by
      unfold chainDrift
      abel
    simpa only [he] using norm_sub_rpow_le_two hq hq2 (f j - f i) (chainDrift C f i)
  have hrow : (∑ i, ∑ j, (C.π i * C.P i j) * ‖chainDrift C f i‖ ^ q) =
      ∑ i, C.π i * ‖chainDrift C f i‖ ^ q := by
    apply Finset.sum_congr rfl
    intro i hi
    calc
      _ = (C.π i * ∑ j, C.P i j) * ‖chainDrift C f i‖ ^ q := by
        rw [Finset.mul_sum, Finset.sum_mul]
      _ = _ := by rw [C.sum_P, mul_one]
  have he (i j : S) :
      (C.π i * C.P i j) *
          (2 * (‖f j - f i‖ ^ q + ‖chainDrift C f i‖ ^ q)) =
        2 * ((C.π i * C.P i j) * ‖f j - f i‖ ^ q) +
          2 * ((C.π i * C.P i j) * ‖chainDrift C f i‖ ^ q) := by ring
  calc
    _ ≤ ∑ i, ∑ j, (C.π i * C.P i j) *
        (2 * (‖f j - f i‖ ^ q + ‖chainDrift C f i‖ ^ q)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (htriangle i j)
        (mul_nonneg (C.π_nonneg i) (C.P_nonneg i j))
    _ = 2 * stateCost C f q 1 + 2 * ∑ i, C.π i * ‖chainDrift C f i‖ ^ q := by
      simp_rw [he, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [hrow, stateCost_one]
      simp only [Real.rpow_eq_pow]
    _ ≤ 4 * stateCost C f q 1 := by
      linarith only [chainDrift_q_moment_le hq C f]

theorem sampledDifference_q_moment_le_four {q : ℝ}
    (hq : 1 ≤ q) (hq2 : q ≤ 2) (C : FiniteReversibleChain S) (f : S → X)
    {m : ℕ} (k : Fin m) :
    (∑ ω : StatePath S (2 * m), pathWeight C (2 * m) ω *
      ‖sampledDifference C f k ω‖ ^ q) ≤ 4 * stateCost C f q 1 := by
  have hodd : (⟨2 * k.val + 1, by omega⟩ : Fin (2 * m)).castSucc =
      sampledOddIndex k := by
    apply Fin.ext
    rfl
  have heven : (⟨2 * k.val + 1, by omega⟩ : Fin (2 * m)).succ =
      sampledEvenIndex k.succ := by
    apply Fin.ext
    change 2 * k.val + 1 + 1 = 2 * (k.val + 1)
    omega
  have hp := sum_pathWeight_pair C (2 * k.val + 1)
    (by omega : 2 * k.val + 1 < 2 * m)
    (fun i j => ‖f j - chainAverage C f i‖ ^ q)
  have he : (∑ ω : StatePath S (2 * m), pathWeight C (2 * m) ω *
      ‖sampledDifference C f k ω‖ ^ q) =
      ∑ i, ∑ j, (C.π i * C.P i j) * ‖f j - chainAverage C f i‖ ^ q := by
    simpa only [sampledDifference, hodd, heven] using hp
  rw [he]
  exact centered_edge_q_moment_le_four hq hq2 C f

theorem sampledForward_q_moment_le {q D : ℝ}
    (hq : 1 ≤ q) (hq2 : q ≤ 2) (hD : 0 ≤ D)
    (hsmooth : SymmetricPowerSmoothWith q D X)
    (C : FiniteReversibleChain S) (f : S → X) (m : ℕ) :
    (∑ ω : StatePath S (2 * m), pathWeight C (2 * m) ω *
      ‖sampledForward C f m m ω‖ ^ q) ≤
      16 * D * (m : ℝ) * stateCost C f q 1 := by
  classical
  have h := finite_martingale_q_moment_four hq hq2 hD hsmooth m
    (fun k : Fin m => StatePath S (2 * k.val))
    (pathWeight C (2 * m)) (sampledKey m) (sampledForward C f m)
    (pathWeight_nonneg C (2 * m)) (sampledForward_zero C f m)
    (sampledForward_fiber_constant C f) (sampledForward_fiber_cancel C f)
  calc
    _ ≤ (4 * D) * ∑ k : Fin m, ∑ ω : StatePath S (2 * m),
        pathWeight C (2 * m) ω *
          ‖sampledForward C f m (k.val + 1) ω - sampledForward C f m k.val ω‖ ^ q := h
    _ = (4 * D) * ∑ k : Fin m, ∑ ω : StatePath S (2 * m),
        pathWeight C (2 * m) ω * ‖sampledDifference C f k ω‖ ^ q := by
      simp_rw [sampledForward_step]
    _ ≤ (4 * D) * ∑ _k : Fin m, 4 * stateCost C f q 1 := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hD)
      exact Finset.sum_le_sum fun k hk => sampledDifference_q_moment_le_four hq hq2 C f k
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

theorem sampledBackward_q_moment_le {q D : ℝ}
    (hq : 1 ≤ q) (hq2 : q ≤ 2) (hD : 0 ≤ D)
    (hsmooth : SymmetricPowerSmoothWith q D X)
    (C : FiniteReversibleChain S) (f : S → X) (m : ℕ) :
    (∑ ω : StatePath S (2 * m), pathWeight C (2 * m) ω *
      ‖sampledBackward C f m m ω‖ ^ q) ≤
      16 * D * (m : ℝ) * stateCost C f q 1 := by
  have h := sum_pathWeight_reverse_v C (2 * m)
    (fun ω => ‖sampledForward C f m m ω‖ ^ q)
  have he : (∑ ω : StatePath S (2 * m), pathWeight C (2 * m) ω *
      ‖sampledBackward C f m m ω‖ ^ q) =
      ∑ ω : StatePath S (2 * m), pathWeight C (2 * m) ω *
        ‖sampledForward C f m m ω‖ ^ q := by
    simpa only [sampledBackward, smul_eq_mul] using h
  rw [he]
  exact sampledForward_q_moment_le hq hq2 hD hsmooth C f m

theorem even_stateCost_le {q D : ℝ}
    (hq : 1 ≤ q) (hq2 : q ≤ 2) (hD : 0 ≤ D)
    (hsmooth : SymmetricPowerSmoothWith q D X)
    (C : FiniteReversibleChain S) (f : S → X) (m : ℕ) :
    stateCost C f q (2 * m) ≤
      32 * D * ((2 * m : ℕ) : ℝ) * stateCost C f q 1 := by
  have ha := sampledForward_q_moment_le hq hq2 hD hsmooth C f m
  have hb := sampledBackward_q_moment_le hq hq2 hD hsmooth C f m
  calc
    _ = ∑ ω : StatePath S (2 * m), pathWeight C (2 * m) ω *
        ‖sampledForward C f m m ω - sampledBackward C f m m ω‖ ^ q := by
      unfold stateCost
      simp_rw [even_displacement_decomposition C f m, Real.rpow_eq_pow]
    _ ≤ ∑ ω : StatePath S (2 * m), pathWeight C (2 * m) ω *
        (2 * (‖sampledForward C f m m ω‖ ^ q +
          ‖sampledBackward C f m m ω‖ ^ q)) := by
      exact Finset.sum_le_sum fun ω hω => mul_le_mul_of_nonneg_left
        (norm_sub_rpow_le_two hq hq2 _ _) (pathWeight_nonneg C (2 * m) ω)
    _ = 2 * ((∑ ω : StatePath S (2 * m), pathWeight C (2 * m) ω *
        ‖sampledForward C f m m ω‖ ^ q) +
        (∑ ω : StatePath S (2 * m), pathWeight C (2 * m) ω *
          ‖sampledBackward C f m m ω‖ ^ q)) := by
      exact sum_weighted_two _ _ _
    _ ≤ 32 * D * ((2 * m : ℕ) : ℝ) * stateCost C f q 1 := by
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      linarith only [ha, hb]

theorem stateCost_succ_le_two {q : ℝ} (hq : 1 ≤ q) (hq2 : q ≤ 2)
    (C : FiniteReversibleChain S) (f : S → X) (n : ℕ) :
    stateCost C f q (n + 1) ≤ 2 * (stateCost C f q n + stateCost C f q 1) := by
  let first : StatePath S (n + 1) → X := fun ω =>
    f (ω (Fin.last n).castSucc) - f (ω 0)
  let last : StatePath S (n + 1) → X := fun ω =>
    f (ω (Fin.last (n + 1))) - f (ω (Fin.last n).castSucc)
  have hsplit (ω : StatePath S (n + 1)) :
      f (ω (Fin.last (n + 1))) - f (ω 0) = first ω + last ω := by
    dsimp [first, last]
    abel
  have hfirst : (∑ ω : StatePath S (n + 1), pathWeight C (n + 1) ω * ‖first ω‖ ^ q) =
      stateCost C f q n := by
    have hcast (i : Fin (n + 1)) :
        Fin.castLE (Nat.add_le_add_right (Nat.le_succ n) 1) i = i.castSucc := by
      apply Fin.ext
      rfl
    have hzero : (0 : Fin (n + 1)).castSucc = 0 := by
      apply Fin.ext
      rfl
    simpa only [first, pathTake, stateCost, hcast, hzero, Real.rpow_eq_pow] using
      sum_pathWeight_take C n (Nat.le_succ n)
        (fun η => ‖f (η (Fin.last n)) - f (η 0)‖ ^ q)
  have hlast : (∑ ω : StatePath S (n + 1), pathWeight C (n + 1) ω * ‖last ω‖ ^ q) =
      stateCost C f q 1 := by
    rw [stateCost_one]
    exact sum_pathWeight_last_pair C n (fun i j => ‖f j - f i‖ ^ q)
  calc
    _ = ∑ ω : StatePath S (n + 1), pathWeight C (n + 1) ω * ‖first ω + last ω‖ ^ q := by
      unfold stateCost
      simp_rw [hsplit, Real.rpow_eq_pow]
    _ ≤ ∑ ω : StatePath S (n + 1), pathWeight C (n + 1) ω *
        (2 * (‖first ω‖ ^ q + ‖last ω‖ ^ q)) := by
      exact Finset.sum_le_sum fun ω hω => mul_le_mul_of_nonneg_left
        (norm_add_rpow_le_two hq hq2 _ _) (pathWeight_nonneg C (n + 1) ω)
    _ = 2 * ((∑ ω : StatePath S (n + 1), pathWeight C (n + 1) ω * ‖first ω‖ ^ q) +
        (∑ ω : StatePath S (n + 1), pathWeight C (n + 1) ω * ‖last ω‖ ^ q)) := by
      exact sum_weighted_two _ _ _
    _ = _ := by rw [hfirst, hlast]

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SmoothMarkovType
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem stateCost_le_of_symmetricPowerSmooth {q D : ℝ}
    (hq : 1 ≤ q) (hq₂ : q ≤ 2) (hD : 1 ≤ D)
    (hsmooth : SymmetricPowerSmoothWith q D X)
    {S : Type*} [Fintype S] (C : FiniteReversibleChain S)
    (f : S → X) (n : ℕ) :
    stateCost C f q n ≤ 64 * D * (n : ℝ) * stateCost C f q 1 := by
  have hD0 : 0 ≤ D := le_trans zero_le_one hD
  have hcost : 0 ≤ stateCost C f q 1 := stateCost_nonneg C f q 1
  rcases Nat.even_or_odd' n with ⟨m, hm | hm⟩
  · subst n
    have heven := even_stateCost_le hq hq₂ hD0 hsmooth C f m
    have hprod : 0 ≤ D * ((2 * m : ℕ) : ℝ) * stateCost C f q 1 :=
      mul_nonneg (mul_nonneg hD0 (Nat.cast_nonneg _)) hcost
    nlinarith only [heven, hprod]
  · subst n
    have hstep := stateCost_succ_le_two hq hq₂ C f (2 * m)
    have heven := even_stateCost_le hq hq₂ hD0 hsmooth C f m
    have hcostD : stateCost C f q 1 ≤ D * stateCost C f q 1 := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hD hcost
    have hcast : ((2 * m + 1 : ℕ) : ℝ) = ((2 * m : ℕ) : ℝ) + 1 := by
      simp only [Nat.cast_add, Nat.cast_one]
    rw [hcast]
    nlinarith only [hstep, heven, hcostD, hcost]

theorem markovTypeWith_of_symmetricPowerSmooth {q D : ℝ}
    (hq : 1 < q) (hq₂ : q ≤ 2) (hD : 1 ≤ D)
    (hsmooth : SymmetricPowerSmoothWith q D X) :
    MarkovTypeWith q (64 * D) X := by
  have hK : 1 ≤ 64 * D := by linarith
  refine ⟨lt_trans zero_lt_one hq, lt_of_lt_of_le zero_lt_one hK, ?_⟩
  intro m C f n _hn
  have hbound := stateCost_le_of_symmetricPowerSmooth hq.le hq₂ hD hsmooth C f n
  have hpower : 64 * D ≤ (64 * D) ^ q := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hK hq.le)
  calc
    stateCost C f q n ≤ 64 * D * (n : ℝ) * stateCost C f q 1 := hbound
    _ ≤ (64 * D) ^ q * (n : ℝ) * stateCost C f q 1 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpower (Nat.cast_nonneg n))
        (stateCost_nonneg C f q 1)

theorem markovTypeWith_of_symmetricPowerSmooth_nonneg {q D : ℝ}
    (hq : 1 < q) (hq₂ : q ≤ 2) (_hD : 0 ≤ D)
    (hsmooth : SymmetricPowerSmoothWith q D X) :
    MarkovTypeWith q (64 * max 1 D) X := by
  apply markovTypeWith_of_symmetricPowerSmooth hq hq₂ (le_max_left 1 D)
  intro x y
  have hmono := mul_le_mul_of_nonneg_right (le_max_right 1 D)
    (Real.rpow_nonneg (norm_nonneg y) q)
  have hbase := hsmooth x y
  nlinarith only [hmono, hbase]

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SmoothRenormed
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem symmetricPowerSmoothWith_renormed (N : EquivalentNorm X) {q D : ℝ}
    (h : SymmetricPowerSmooth N.p q D) :
    SymmetricPowerSmoothWith q D (Renormed N) := by
  intro x y
  change N.p (Renormed.toOriginal N x + Renormed.toOriginal N y) ^ q +
      N.p (Renormed.toOriginal N x - Renormed.toOriginal N y) ^ q ≤
    2 * N.p (Renormed.toOriginal N x) ^ q +
      2 * D * N.p (Renormed.toOriginal N y) ^ q
  have hxy := h (Renormed.toOriginal N x) (Renormed.toOriginal N y)
  linarith only [hxy]

theorem markovTypeWith_of_equivalent_symmetricPowerSmooth
    (N : EquivalentNorm X) {q D : ℝ}
    (hq : 1 < q) (hq₂ : q ≤ 2) (hD : 0 ≤ D)
    (h : SymmetricPowerSmooth N.p q D) :
    MarkovTypeWith q ((N.upper / N.lower) * (64 * max 1 D)) X := by
  exact (markovTypeWith_of_symmetricPowerSmooth_nonneg hq hq₂ hD
    (symmetricPowerSmoothWith_renormed N h)).of_renormed N

theorem hasNontrivialMarkovType_of_equivalent_symmetricPowerSmooth
    (N : EquivalentNorm X) {q D : ℝ}
    (hq : 1 < q) (hq₂ : q ≤ 2) (hD : 0 ≤ D)
    (h : SymmetricPowerSmooth N.p q D) : HasNontrivialMarkovType X := by
  exact ⟨q, hq, (N.upper / N.lower) * (64 * max 1 D),
    markovTypeWith_of_equivalent_symmetricPowerSmooth N hq hq₂ hD h⟩

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem MarkovTypeWith.hasEquivalentUCNorm {p K : ℝ}
    (hX : MarkovTypeWith p K X) (hp : 1 < p) : HasEquivalentUCNorm X := by
  classical
  by_contra hnot
  obtain ⟨N, hNX⟩ := orderedNorm_of_not_hasEquivalentUCNorm hnot
  exact hX.not_coordinatesRepresentable hp N hNX

theorem HasNontrivialMarkovType.hasEquivalentUCNorm
    (hX : HasNontrivialMarkovType X) : HasEquivalentUCNorm X := by
  obtain ⟨p, hp, K, hK⟩ := hX
  exact hK.hasEquivalentUCNorm hp

theorem HasEquivalentUCNorm.hasNontrivialMarkovType [CompleteSpace X]
    (hX : HasEquivalentUCNorm X) : HasNontrivialMarkovType X := by
  obtain ⟨N, q, hq, hq₂, C, hC, hSym, _, _, _⟩ :=
    exists_power_smooth_equivalentNorm hX
  exact hasNontrivialMarkovType_of_equivalent_symmetricPowerSmooth
    N hq hq₂ hC.le hSym

theorem hasNontrivialMarkovType_iff_hasEquivalentUCNorm_oai [CompleteSpace X] :
    HasNontrivialMarkovType X ↔ HasEquivalentUCNorm X :=
  ⟨HasNontrivialMarkovType.hasEquivalentUCNorm,
    HasEquivalentUCNorm.hasNontrivialMarkovType⟩

end MarkovSuperreflexivity

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MarkovSuperreflexivity.hasNontrivialMarkovType_iff_hasEquivalentUCNorm_oai.{u_1} := @OAI.MarkovSuperreflexivity.hasNontrivialMarkovType_iff_hasEquivalentUCNorm_oai.{u_1}
