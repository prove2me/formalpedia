-- Prove2me | solution 1 for OAI.Erdos3.RationalFilteredNilmanifold.exists_anchored_option_mode_factorization_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:33:59.265578+00:00
-- url     : https://prove2.me/submissions/8c205cfb-e06c-42ae-9444-a662f4859f62

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B215
import Definitions.Def_OAIE3v2B238

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeFixedVerticalPower
namespace OAI

section

namespace Erdos3

open CircleFourier
open scoped TensorProduct BigOperators

theorem exists_native_vertical_pair_on_finset
    {X σ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d e : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
    (D : RationalFilteredNilmanifold L s d) (D' : RationalFilteredNilmanifold M s e)
    {w : σ → ℕ} (Q : D.Niltest w) (R : D'.Niltest w)
    {p q delta rho eta : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hdelta : 0 < delta)
    (hrho : 0 < rho) (heta : 0 < eta) (hrhop : rho⁻¹ ≤ Real.exp p) (hetaq : eta⁻¹ ≤ Real.exp q)
    (hQc : Q.ComplexityLE p) (hRc : R.ComplexityLE q)
    (hQcap : (Q.normBound : ℝ) ≤ 1) (hRcap : (R.normBound : ℝ) ≤ 1)
    (hsmall : rho + Real.exp (verticalDecompositionBudget p) * eta ≤ delta / 2)
    (B : Finset X) (hB : B.Nonempty) (sample : X → σ → ℤ) (U : X → ℂ)
    (hU : ∀ x ∈ B, ‖U x‖ ≤ 1)
    (hcorr : delta ≤ ‖𝔼 x ∈ B, U x * Q.eval (sample x) * R.eval (sample x)‖) :
    ∃ (freq : L →ₗ[ℚ] ℚ) (freq' : M →ₗ[ℚ] ℚ) (V : D.Niltest w) (W : D'.Niltest w),
      V.ComplexityLE p ∧ V.orbit = Q.orbit ∧ V.normBound = Q.normBound ∧
      W.ComplexityLE q ∧ W.orbit = R.orbit ∧ W.normBound = R.normBound ∧
      (∀ i, rationalLogHeight (freq (D.basis i)) ≤ verticalDecompositionBudget p) ∧
      (∀ i, rationalLogHeight (freq' (D'.basis i)) ≤ verticalDecompositionBudget q) ∧
      (∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
        V.observable (z • x) = character ((realifyFunctional freq z.coord : ℝ) : CircleFourier.Circle) *
          V.observable x) ∧
      (∀ z, z ∈ D'.filtration.realification.subgroup s → ∀ x,
        W.observable (z • x) = character ((realifyFunctional freq' z.coord : ℝ) : CircleFourier.Circle) *
          W.observable x) ∧
      (delta / 2) / (Real.exp (verticalDecompositionBudget p) * Real.exp (verticalDecompositionBudget q)) ≤
        ‖𝔼 x ∈ B, U x * V.eval (sample x) * W.eval (sample x)‖ := by
  obtain ⟨I, instI, freqV, V, hI, hheightV, hcertV, hvertV, _, _, happroxV⟩ :=
    Q.exists_vertical_decomposition_preserving_bounds hp hQc hrho hrhop
  let := instI
  obtain ⟨J, instJ, freqW, W, hJ, hheightW, hcertW, hvertW, _, _, happroxW⟩ :=
    R.exists_vertical_decomposition_preserving_bounds hq hRc heta hetaq
  let := instJ
  obtain ⟨i, j, hbias⟩ := exists_correlating_components_on_finset B hB U
    (fun x => Q.eval (sample x)) (fun x => R.eval (sample x))
    (fun i x => (V i).eval (sample x)) (fun j x => (W j).eval (sample x))
    hdelta (Real.exp_pos _) (Real.exp_pos _) hrho.le heta.le hI hJ hU
    (fun x _ => (R.norm_eval_le (sample x)).trans hRcap)
    (fun i x _ => ((V i).norm_eval_le (sample x)).trans (by rw [(hcertV i).2.2.1]; exact hQcap))
    (fun x _ => by simpa only [norm_sub_rev] using happroxV (sample x))
    (fun x _ => by simpa only [norm_sub_rev] using happroxW (sample x)) hsmall hcorr
  exact ⟨freqV i, freqW j, V i, W j, (hcertV i).1, (hcertV i).2.1, (hcertV i).2.2.1,
    (hcertW j).1, (hcertW j).2.1, (hcertW j).2.2.1, hheightV i, hheightW j, hvertV i, hvertW j, hbias⟩

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped TensorProduct BigOperators

theorem exists_native_vertical_pair_power :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X σ L M : Type*}
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s d e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      (D : RationalFilteredNilmanifold L s d) (D' : RationalFilteredNilmanifold M s e)
      {w : σ → ℕ} (Q : D.Niltest w) (R : D'.Niltest w) (p : ℝ), 0 ≤ p →
      Q.ComplexityLE p → R.ComplexityLE p →
      (Q.normBound : ℝ) ≤ 1 → (R.normBound : ℝ) ≤ 1 →
      ∀ (B : Finset X), B.Nonempty → ∀ (sample : X → σ → ℤ) (U : X → ℂ),
      (∀ x ∈ B, ‖U x‖ ≤ 1) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ B, U x * Q.eval (sample x) * R.eval (sample x)‖ →
      ∃ (freq : L →ₗ[ℚ] ℚ) (freq' : M →ₗ[ℚ] ℚ) (V : D.Niltest w) (W : D'.Niltest w),
        V.ComplexityLE ((p + C) ^ C) ∧ V.orbit = Q.orbit ∧ V.normBound = Q.normBound ∧
        W.ComplexityLE ((p + C) ^ C) ∧ W.orbit = R.orbit ∧ W.normBound = R.normBound ∧
        (∀ i, rationalLogHeight (freq (D.basis i)) ≤ (p + C) ^ C) ∧
        (∀ i, rationalLogHeight (freq' (D'.basis i)) ≤ (p + C) ^ C) ∧
        (∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
          V.observable (z • x) = character ((realifyFunctional freq z.coord : ℝ) : CircleFourier.Circle) *
            V.observable x) ∧
        (∀ z, z ∈ D'.filtration.realification.subgroup s → ∀ x,
          W.observable (z • x) = character ((realifyFunctional freq' z.coord : ℝ) : CircleFourier.Circle) *
            W.observable x) ∧
        Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 x ∈ B, U x * V.eval (sample x) * W.eval (sample x)‖ := by
  obtain ⟨C, hC, hprecision⟩ := exists_vertical_pair_precision
  refine ⟨C, hC, ?_⟩
  intro X σ L M _ _ _ _ s d e _ _ _ _ _ _ _ _ D D' w Q R p hp hQ hR hQcap hRcap
    B hB sample U hU hcorr
  obtain ⟨q, r, rho, eta, hpq, hpr, hqC, hrC, hVq, hVr, hrho, heta, hrhoq, hetar, hsmall, hloss⟩ :=
    hprecision p hp
  obtain ⟨freq, freq', V, W, hVc, hVo, hVn, hWc, hWo, hWn, hVheight, hWheight, hvertV, hvertW, hbias⟩ :=
    exists_native_vertical_pair_on_finset D D' Q R (hp.trans hpq) (hp.trans hpr)
      (Real.exp_pos _) hrho heta hrhoq hetar (hQ.mono hpq) (hR.mono hpr)
      hQcap hRcap hsmall B hB sample U hU hcorr
  exact ⟨freq, freq', V, W, hVc.mono hqC, hVo, hVn, hWc.mono hrC, hWo, hWn,
    fun i => (hVheight i).trans hVq, fun i => (hWheight i).trans hVr, hvertV, hvertW, hloss.trans hbias⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestOrbitOne
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem oneOnOrbit_orbit (T : D.Niltest w) : T.oneOnOrbit.orbit = T.orbit := rfl

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSampleModelFamily
namespace OAI

section

open scoped TensorProduct BigOperators

namespace Erdos3.RationalFilteredNilmanifold

variable {ι σ : Type*} {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  {D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)} {w : σ → ℕ}

theorem selectedOrbitFactors_orbit (base T : ∀ i, (D i).Niltest w) (active : Finset ι)
    (horbit : ∀ i ∈ active, (T i).orbit = (base i).orbit) (i : ι) :
    (selectedOrbitFactors base T active i).orbit = (base i).orbit := by
  classical
  by_cases hi : i ∈ active
  · simpa only [selectedOrbitFactors, hi, ite_true] using horbit i hi
  · simp only [selectedOrbitFactors, hi, ite_false, Niltest.oneOnOrbit_orbit]

omit [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)] in
theorem selectedOrbitFrequencies_logHeight (eta : ∀ i, L i →ₗ[ℚ] ℚ)
    (active : Finset ι) {p : ℝ} (hp : 0 ≤ p)
    (hheight : ∀ i ∈ active, ∀ k, rationalLogHeight (eta i ((D i).basis k)) ≤ p)
    (i : ι) (k : Fin (d i)) :
    rationalLogHeight (selectedOrbitFrequencies eta active i ((D i).basis k)) ≤ p := by
  classical
  by_cases hi : i ∈ active
  · simpa only [selectedOrbitFrequencies, hi, ite_true] using hheight i hi k
  · simpa [selectedOrbitFrequencies, hi, rationalLogHeight] using hp

theorem selectedOrbitFactors_vertical (base T : ∀ i, (D i).Niltest w)
    (eta : ∀ i, L i →ₗ[ℚ] ℚ) (active : Finset ι)
    (hvert : ∀ i ∈ active, ∀ z, z ∈ (D i).filtration.realification.subgroup s → ∀ x,
      (T i).observable (z • x) =
        CircleFourier.character ((realifyFunctional (eta i) z.coord : ℝ) : CircleFourier.Circle) *
          (T i).observable x)
    (i : ι) (z : (D i).RealGroup) (hz : z ∈ (D i).filtration.realification.subgroup s)
    (x : (D i).Space) :
    (selectedOrbitFactors base T active i).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (selectedOrbitFrequencies eta active i) z.coord : ℝ) : CircleFourier.Circle) *
          (selectedOrbitFactors base T active i).observable x := by
  classical
  by_cases hi : i ∈ active
  · simpa only [selectedOrbitFactors, selectedOrbitFrequencies, hi, ite_true] using hvert i hi z hz x
  · simpa only [selectedOrbitFactors, selectedOrbitFrequencies, hi, ite_false] using
      (base i).oneOnOrbit_vertical z x

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.CommonProductNiltestFamily
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

variable {ι J σ : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]

theorem exists_common_product_niltest_family
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) {w : σ → ℕ}
    (base : ∀ i, (D i).Niltest w) (T : J → ∀ i, (D i).Niltest w)
    (active : J → Finset ι) (eta : J → ∀ i, L i →ₗ[ℚ] ℚ)
    {p : ℝ} (hp : 2 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hD : ∀ i, (D i).GeometryComplexityLE p)
    (horbit : ∀ j i, i ∈ active j → (T j i).orbit = (base i).orbit)
    (hcomp : ∀ j i, i ∈ active j → (T j i).ComplexityLE p)
    (hcap : ∀ j i, i ∈ active j → (T j i).normBound ≤ 1)
    (hheight : ∀ j i, i ∈ active j → ∀ k, rationalLogHeight (eta j i ((D i).basis k)) ≤ p)
    (hvert : ∀ j i, i ∈ active j → ∀ z, z ∈ (D i).filtration.realification.subgroup s → ∀ x,
      (T j i).observable (z • x) =
        CircleFourier.character ((realifyFunctional (eta j i) z.coord : ℝ) : CircleFourier.Circle) *
          (T j i).observable x) :
    ∃ (S0 : (pi D).Niltest w) (S : J → (pi D).Niltest w),
      S0.orbit = NilpotentLieFiltration.piRealOrbit (fun i => (D i).filtration) (fun i => (base i).orbit) ∧
      S0.ComplexityLE (productNiltestBudget p) ∧
      ∀ j, (S j).orbit = S0.orbit ∧
        (S j).normBound = 1 ∧ (S j).ComplexityLE (productNiltestBudget p) ∧
        (∀ x, (S j).eval x = ∏ i ∈ active j, (T j i).eval x) ∧
        (∀ k, rationalLogHeight
          (piFrequency (selectedOrbitFrequencies (eta j) (active j)) ((pi D).basis k)) ≤ p) ∧
        (∀ z, z ∈ (pi D).filtration.realification.subgroup s → ∀ x,
          (S j).observable (z • x) = CircleFourier.character
            ((realifyFunctional (piFrequency (selectedOrbitFrequencies (eta j) (active j))) z.coord : ℝ) :
              CircleFourier.Circle) * (S j).observable x) := by
  have hp0 : 0 ≤ p := by linarith
  let U := fun i => (base i).oneOnOrbit
  have hU : ∀ i, (U i).ComplexityLE p := fun i => (base i).oneOnOrbit_complexity hp (hD i)
  let S0 := piNiltest D U hp0 hι hU
  let factors := fun j => selectedOrbitFactors base (T j) (active j)
  have hfactorComp : ∀ j i, (factors j i).ComplexityLE p := fun j =>
    selectedOrbitFactors_complexity base (T j) (active j) hp hD (hcomp j)
  have hfactorCap : ∀ j i, (factors j i).normBound ≤ 1 := fun j =>
    selectedOrbitFactors_normBound base (T j) (active j) (hcap j)
  let S := fun j => unitBoundedPiNiltest D (factors j) hp0 hι (hfactorComp j) (hfactorCap j)
  refine ⟨S0, S, rfl, piNiltest_complexity D U hp0 hι hU, fun j => ?_⟩
  refine ⟨?_, rfl, unitBoundedPiNiltest_complexity D (factors j) hp0 hι (hfactorComp j) (hfactorCap j),
    ?_, ?_, ?_⟩
  · change NilpotentLieFiltration.piRealOrbit _ _ = NilpotentLieFiltration.piRealOrbit _ _
    apply congrArg (NilpotentLieFiltration.piRealOrbit (fun i => (D i).filtration))
    exact funext (selectedOrbitFactors_orbit base (T j) (active j) (horbit j))
  · intro x
    exact (unitBoundedPiNiltest_eval D (factors j) hp0 hι (hfactorComp j) (hfactorCap j) x).trans
      (selectedOrbitFactors_eval base (T j) (active j) x)
  · exact piFrequency_logHeight D _
      (selectedOrbitFrequencies_logHeight (eta j) (active j) hp0 (hheight j))
  · exact productObservable_vertical D (factors j) _
      (selectedOrbitFactors_vertical base (T j) (eta j) (active j) (hvert j))

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PositiveShiftProductData
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem anchoredOptionInputs_prod {J : Type*} (j : J) (f : Option (Option J ⊕ J) → ℂ) :
    (∏ i ∈ anchoredOptionInputs j, f i) =
      f none * f (some (.inl none)) * f (some (.inl (some j))) * f (some (.inr j)) := by
  classical
  simp [anchoredOptionInputs]; ring

namespace RationalFilteredNilmanifold

variable {J σ : Type*} {L : Option (Option J ⊕ J) → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : Option (Option J ⊕ J) → ℕ}
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  {D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)} {w : σ → ℕ}

theorem anchoredOptionObservableData_product
    (U : J → (D none).Niltest w) (V : J → (D (some (.inl none))).Niltest w)
    (A : ∀ j, (D (some (.inl (some j)))).Niltest w) (B : ∀ j, (D (some (.inr j))).Niltest w)
    (j : J) (x : σ → ℤ) :
    (∏ i ∈ anchoredOptionInputs j, (anchoredOptionObservableData U V A B j i).eval x) =
      (U j).eval x * star ((V j).eval x) * (A j).eval x * (B j).eval x := by
  rw [anchoredOptionInputs_prod]
  rfl

end RationalFilteredNilmanifold
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.SimultaneousNiltestFactorization
namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration
open scoped TensorProduct BigOperators

theorem exists_niltest_family_step_drop (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ J L : Type*} [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (w : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ w i}))
      (T0 : D.Niltest (fun _ : σ => 1)) (T : J → D.Niltest (fun _ : σ => 1))
      (_hOrbit : ∀ j, (T j).orbit = T0.orbit) (eta : J → L →ₗ[ℚ] ℚ)
      (p : ℝ), 0 ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (∀ j, (T j).ComplexityLE p) →
      (∀ j i, rationalLogHeight (eta j (D.basis i)) ≤ p) →
      (∀ j z, z ∈ D.filtration.realification.subgroup s → ∀ x,
        (T j).observable (z • x) =
          CircleFourier.character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) *
            (T j).observable x) →
      ∀ (origin : J → σ → ℤ) (lengths : J → σ → ℕ),
      (∀ j i, 0 < lengths j i) →
      (∀ j, Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox (origin j) (lengths j), (T j).eval x‖) →
      ∀ A : σ → ℝ, (∀ i, Real.exp ((p + C) ^ C) ≤ A i) →
      (∀ j i, Real.exp (-p) * A i ≤ lengths j i) →
      ∀ j, D.filtration.ControlledSymbolFactorization D.basis w hF (eta j) A
        (T0.symbol D.basis w hF) ((p + C) ^ C) := by
  obtain ⟨c, hc, hstep⟩ := exists_translated_step_drop s hs
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C c) ^ c +
    Polynomial.C s * Polynomial.X + Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget B
  refine ⟨C, hC, ?_⟩
  intro σ J L _ _ _ _ d _ _ _ _ D w hF T0 T hOrbit eta p hp hσ hT hη hvert
    origin lengths hlengths hbias A hA hrelative j
  have hbound : (p + c) ^ c + s * p + p ≤ (p + C) ^ C := by
    simpa [B, Polynomial.eval₂_pow] using hbudget p hp
  have hsp : 0 ≤ (s : ℝ) * p := mul_nonneg (Nat.cast_nonneg _) hp
  have hlength (i : σ) : Real.exp ((p + c) ^ c) ≤ (lengths j i : ℝ) := by
    calc
      _ = Real.exp (-p) * Real.exp ((p + c) ^ c + p) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-p) * A i := mul_le_mul_of_nonneg_left
        ((Real.exp_le_exp.mpr (by linarith : (p + c) ^ c + p ≤ (p + C) ^ C)).trans (hA i))
        (Real.exp_nonneg _)
      _ ≤ _ := hrelative j i
  have hsingle := hstep D w hF p hp hσ (T j) (hT j) (eta j) (hη j) (hvert j)
    (origin j) (lengths j) (hlengths j) hlength (hbias j)
  have hsymbol : (T j).symbol D.basis w hF = T0.symbol D.basis w hF := by
    unfold RationalFilteredNilmanifold.Niltest.symbol
    apply congrArg (D.filtration.realPolynomialSymbolHom D.basis w hF (fun _ => 1))
    apply NilpotentLieBCHGroup.ext
    apply Subtype.ext
    exact congrArg (fun q : D.filtration.realification.PolynomialOrbit (fun _ : σ => 1) => q.log)
      (hOrbit j)
  rw [hsymbol] at hsingle
  have hApos : ∀ i, 0 < A i := fun i => (Real.exp_pos _).trans_le (hA i)
  have hrescaled := ControlledSymbolFactorization.rescale D.filtration D.basis w hF hsingle
    (fun i => by exact_mod_cast hlengths j i) hApos hp (hrelative j)
  exact ControlledSymbolFactorization.mono D.filtration D.basis w hF hrescaled (by linarith) hApos

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration VectorPolynomial
open scoped TensorProduct BigOperators

theorem exists_lattice_normalized_niltest_factorization (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ J L : Type*} [Fintype σ] [DecidableEq σ] [Fintype J]
      [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (w : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ w i}))
      (T0 : D.Niltest (fun _ : σ => 1)) (T : J → D.Niltest (fun _ : σ => 1))
      (_hOrbit : ∀ j, (T j).orbit = T0.orbit) (eta : J → L →ₗ[ℚ] ℚ)
      (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      (Fintype.card σ : ℝ) ≤ p → (Fintype.card J : ℝ) ≤ p →
      (∀ j, (T j).ComplexityLE p) →
      (∀ j i, rationalLogHeight (eta j (D.basis i)) ≤ p) →
      (∀ j z, z ∈ D.filtration.realification.subgroup s → ∀ x,
        (T j).observable (z • x) =
          CircleFourier.character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) *
            (T j).observable x) →
      ∀ (origin : J → σ → ℤ) (lengths : J → σ → ℕ), (∀ j i, 0 < lengths j i) →
      (∀ j, Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox (origin j) (lengths j), (T j).eval x‖) →
      ∀ A : σ → ℝ, (∀ i, Real.exp ((p + C) ^ C) ≤ A i) →
      (∀ j i, Real.exp (-p) * A i ≤ lengths j i) →
      let g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group :=
        ⟨⟨T0.orbit.log, T0.orbit.property⟩⟩
      ∃ (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
        (v : Fin d → D.filtration.AssociatedGraded) (m : ℕ) (κ : D.RealGroup)
        (E b R : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group),
        Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
        BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis w hF) w W.toSubmodule ∧
        (∀ i k, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis w hF).repr (v i) k) ≤
          (p + C) ^ C) ∧
        (∀ j x, x ∈ D.filtration.realGradedRefiltrationLayer W s → realifyFunctional (eta j) x = 0) ∧
        0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ κ ∈ D.realLattice ∧
        E * b * R * D.filtration.realification.adaptedConstantGroupHom (fun _ => 1) κ = g ∧
        (∀ α i, |(D.basis.baseChange ℝ).repr
          (coefficients (E.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) i| ≤
            Real.exp ((p + C) ^ C) / monomialScale A α) ∧
        ((fun z : (σ →₀ ℕ) × Fin d => (D.basis.baseChange ℝ).repr
          (coefficients (R.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2) ∈ realDenominatorGrid m) ∧
        coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (R.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        (∀ α, coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈
          D.filtration.realGradedRefiltrationLayer W (Finsupp.weight (fun _ => 1) α)) ∧
        (∀ t : σ → ℝ, eval₂ t (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∈
          realificationLieSubalgebra (D.filtration.gradedRefiltrationSubalgebra W)) := by
  obtain ⟨c, hc, hfamily⟩ := exists_niltest_family_step_drop s hs
  obtain ⟨k, _, hnormalize⟩ := exists_lattice_normalized_refiltered_factorization s
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C c) ^ c
  let P : Polynomial ℕ := Q + (Q + Polynomial.C k) ^ k
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ J L _ _ _ _ _ d _ _ _ _ D w hF T0 T hOrbit eta p hp hD hσ hJ hT hη hvert
    origin lengths hlengths hbias A hA hrelative
  let q := (p + c) ^ c
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    have hc1 : 1 ≤ c := by omega
    have hcR : (2 : ℝ) ≤ c := by exact_mod_cast hc
    have hpbase : 1 ≤ p + c := by linarith
    exact (le_add_of_nonneg_right (Nat.cast_nonneg c)).trans
      (by simpa only [pow_one] using pow_le_pow_right₀ hpbase hc1)
  have hbound : q + (q + k) ^ k ≤ (p + C) ^ C := by
    simpa [P, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hk0 : 0 ≤ (q + k) ^ k := by positivity
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hkC : (q + k) ^ k ≤ (p + C) ^ C := by linarith
  let g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group :=
    ⟨⟨T0.orbit.log, T0.orbit.property⟩⟩
  have hfactor : ∀ j, D.filtration.ControlledSymbolFactorization D.basis w hF (eta j) A
      (D.filtration.realPolynomialSymbolHom D.basis w hF (fun _ => 1) g) q :=
    hfamily D w hF T0 T hOrbit eta p hp hσ hT hη hvert origin lengths hlengths hbias A
      (fun i => (Real.exp_le_exp.mpr hqC).trans (hA i)) hrelative
  obtain ⟨W, v, m, κ, E, b, R, hv, hW, hheight, hfreq, hm, hmp, hκ, hebr,
      hE, hR, hb0, hR0, hcoeff, hvalues⟩ :=
    hnormalize D w hF eta q hq (RationalFilteredNilmanifold.GeometryComplexityLE.mono D hD hpq)
      (hσ.trans hpq) (hJ.trans hpq) A
      (fun i => (Real.exp_le_exp.mpr hkC).trans (hA i)) g hfactor
  refine ⟨W, v, m, κ, E, b, R, hv, hW, (fun i j => (hheight i j).trans hkC), hfreq,
    hm, hmp.trans (Real.exp_le_exp.mpr hkC), hκ, hebr, ?_, hR, hb0, hR0, hcoeff, hvalues⟩
  intro α i
  exact (hE α i).trans (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hkC)
    (monomialScale_pos A (fun i => (Real.exp_pos _).trans_le (hA i)) α).le)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeDetectorContradiction
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial
open scoped TensorProduct BigOperators

theorem exists_selected_product_factorization (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {ι J σ : Type*} [Fintype ι] [Fintype J] [Fintype σ] [DecidableEq σ]
      {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d : ι → ℕ}
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
      (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
      (base : ∀ i, (D i).Niltest (fun _ : σ => 1))
      (rows : J → ∀ i, (D i).Niltest (fun _ : σ => 1))
      (active : J → Finset ι) (eta : J → ∀ i, L i →ₗ[ℚ] ℚ) {p : ℝ},
      2 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card J : ℝ) ≤ p →
      (Fintype.card σ : ℝ) ≤ p → (∀ i, (D i).GeometryComplexityLE p) →
      (∀ j i, i ∈ active j → (rows j i).orbit = (base i).orbit) →
      (∀ j i, i ∈ active j → (rows j i).ComplexityLE p) →
      (∀ j i, i ∈ active j → (rows j i).normBound ≤ 1) →
      (∀ j i, i ∈ active j → ∀ k, rationalLogHeight (eta j i ((D i).basis k)) ≤ p) →
      (∀ j i, i ∈ active j → ∀ z, z ∈ (D i).filtration.realification.subgroup s → ∀ x,
        (rows j i).observable (z • x) = CircleFourier.character
          ((realifyFunctional (eta j i) z.coord : ℝ) : CircleFourier.Circle) * (rows j i).observable x) →
      ∀ (weight : ∀ i, Fin (d i) → ℕ)
        (hFlayers : ∀ i j, (D i).filtration.layer j = Submodule.span ℚ ((D i).basis '' {k | j ≤ weight i k}))
        (origin : J → σ → ℤ) (lengths : J → σ → ℕ),
      (∀ j i, 0 < lengths j i) →
      (∀ j, Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox (origin j) (lengths j),
        ∏ i ∈ active j, (rows j i).eval x‖) →
      ∀ side : σ → ℝ, (∀ i, Real.exp ((p + C) ^ C) ≤ side i) →
      (∀ j i, Real.exp (-p) * side i ≤ lengths j i) →
    let omega := productBasisWeight weight
    let hTotal := pi_layer_span D weight hFlayers
    let orbit := NilpotentLieFiltration.piRealOrbit (fun i => (D i).filtration)
      (fun i => (base i).orbit)
    let g : ((pi D).filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group :=
      ⟨⟨orbit.log, orbit.property⟩⟩
    let freq := fun j => piFrequency
      (selectedOrbitFrequencies (eta j) (active j))
    ∃ (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded)
      (v : Fin (Fintype.card (Σ i, Fin (d i))) → (pi D).filtration.AssociatedGraded)
      (m : ℕ) (κ : (pi D).RealGroup)
      (E b R : ((pi D).filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group),
      Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
      BasisGradedSubmodule ((pi D).filtration.associatedGradedBasis (pi D).basis omega hTotal) omega W.toSubmodule ∧
      (∀ i k, rationalLogHeight (((pi D).filtration.associatedGradedBasis (pi D).basis omega hTotal).repr (v i) k) ≤
        (p + C) ^ C) ∧
      (∀ j x, x ∈ (pi D).filtration.realGradedRefiltrationLayer W s → realifyFunctional (freq j) x = 0) ∧
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ κ ∈ (pi D).realLattice ∧
      E * b * R * (pi D).filtration.realification.adaptedConstantGroupHom (fun _ => 1) κ = g ∧
      (∀ α i, |((pi D).basis.baseChange ℝ).repr
        (coefficients (E.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) α) i| ≤
          Real.exp ((p + C) ^ C) / monomialScale side α) ∧
      ((fun z : (σ →₀ ℕ) × Fin (Fintype.card (Σ i, Fin (d i))) => ((pi D).basis.baseChange ℝ).repr
        (coefficients (R.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) z.1) z.2) ∈ realDenominatorGrid m) ∧
      coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) 0 = 0 ∧
      coefficients (R.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) 0 = 0 ∧
      (∀ α, coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) α ∈
        (pi D).filtration.realGradedRefiltrationLayer W (Finsupp.weight (fun _ => 1) α)) ∧
      (∀ t : σ → ℝ, eval₂ t (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) ∈
        realificationLieSubalgebra ((pi D).filtration.gradedRefiltrationSubalgebra W)) := by
  obtain ⟨c, _, hfactor⟩ := exists_lattice_normalized_niltest_factorization s hs
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + 2) ^ 2 + X + (X + (X ^ 2 + X + 3) ^ 2) + X ^ 2 + 4
  let F := Q + (Q + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget F
  refine ⟨C, hC, ?_⟩
  intro ι J σ _ _ _ _ L _ _ d _ _ _ _ _ _ _ _ D base rows active eta p
    hp hι hJ hσ hD horbit hcomp hcap hheight hvert weight hFlayers
    origin lengths hlengths hbias side hside hrelative
  have hp0 : 0 ≤ p := by linarith
  let q := productNiltestBudget p
  have hpq : p ≤ q := by
    exact (by nlinarith [sq_nonneg p] : p ≤ (p + 2) ^ 2).trans (productNiltestBudget_geometry hp0)
  have hq : 0 ≤ q := hp0.trans hpq
  have hbudget' : q + (q + c) ^ c ≤ (p + C) ^ C := by
    simpa [F, Q, X, q, productNiltestBudget, productObservableLipBudget, Polynomial.eval₂_pow] using hbudget p hp0
  have hcC : (q + c) ^ c ≤ (p + C) ^ C := by linarith
  have hsidepos : ∀ i, 0 < side i := fun i => (Real.exp_pos _).trans_le (hside i)
  obtain ⟨S0, S, hS0, hS0c, hS⟩ := exists_common_product_niltest_family D base rows active eta
    hp hι hD horbit hcomp hcap hheight hvert
  let omega := productBasisWeight weight
  let hTotal := pi_layer_span D weight hFlayers
  let freq := fun j => piFrequency
    (selectedOrbitFrequencies (eta j) (active j))
  have hcorr : ∀ j, Real.exp (-q) ≤ ‖𝔼 x ∈ translatedIntegerBox (origin j) (lengths j), (S j).eval x‖ := by
    intro j
    apply (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans
    simpa only [(hS j).2.2.2.1] using hbias j
  have hrel : ∀ j i, Real.exp (-q) * side i ≤ lengths j i := fun j i =>
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hpq)) (hsidepos i).le).trans (hrelative j i)
  obtain ⟨W, v, m, κ, E, b, R, hv, hW, hheight, hfreq, hm, hmp, hκ, hebr,
      hE, hR, hb0, hR0, hcoeff, hvalues⟩ :=
    hfactor (pi D) omega hTotal S0 S (fun j => (hS j).1) freq q hq hS0c.1
      (by exact (show (Fintype.card σ : ℝ) ≤ p from hσ).trans hpq)
      (hJ.trans hpq) (fun j => (hS j).2.2.1)
      (fun j k => ((hS j).2.2.2.2.1 k).trans hpq) (fun j => (hS j).2.2.2.2.2)
      origin lengths hlengths hcorr side (fun i => (Real.exp_le_exp.mpr hcC).trans (hside i)) hrel
  let orbit := NilpotentLieFiltration.piRealOrbit (fun i => (D i).filtration)
    (fun i => (base i).orbit)
  let g : ((pi D).filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group :=
    ⟨⟨orbit.log, orbit.property⟩⟩
  have hg : (⟨⟨S0.orbit.log, S0.orbit.property⟩⟩ :
      ((pi D).filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group) = g := by
    apply NilpotentLieBCHGroup.ext
    apply Subtype.ext
    exact congrArg (fun o : (pi D).filtration.realification.PolynomialOrbit (fun _ : σ => 1) => o.log) hS0
  refine ⟨W, v, m, κ, E, b, R, hv, hW, (fun i k => (hheight i k).trans hcC), hfreq, hm,
    hmp.trans (Real.exp_le_exp.mpr hcC), hκ, hebr.trans hg, ?_, hR, hb0, hR0, hcoeff, hvalues⟩
  intro α i
  exact (hE α i).trans (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hcC)
    (monomialScale_pos side hsidepos α).le)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial
open scoped TensorProduct BigOperators

theorem exists_anchored_option_product_factorization (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {J σ : Type*} [Fintype J] [Fintype σ] [DecidableEq σ] {L : (Option (Option J ⊕ J)) → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d : (Option (Option J ⊕ J)) → ℕ}
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
    (P : (D none).Niltest (fun _ : σ => 1)) (P₀ : (D (some (.inl none))).Niltest (fun _ : σ => 1))
    (U : J → (D none).Niltest (fun _ : σ => 1)) (V : J → (D (some (.inl none))).Niltest (fun _ : σ => 1))
    (A : ∀ j, (D (some (.inl (some j)))).Niltest (fun _ : σ => 1)) (B : ∀ j, (D (some (.inr j))).Niltest (fun _ : σ => 1))
    (eta : J → L none →ₗ[ℚ] ℚ) (theta : J → L (some (.inl none)) →ₗ[ℚ] ℚ)
    (alpha : ∀ j, L (some (.inl (some j))) →ₗ[ℚ] ℚ) (beta : ∀ j, L (some (.inr j)) →ₗ[ℚ] ℚ)
    {p : ℝ} (_hp : 2 ≤ p) (_hcard : (Fintype.card (Option (Option J ⊕ J)) : ℝ) ≤ p)
    (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hD : ∀ i, (D i).GeometryComplexityLE p)
    (_hU : ∀ j, (U j).ComplexityLE p ∧ (U j).orbit = P.orbit ∧ (U j).normBound ≤ 1)
    (_hV : ∀ j, (V j).ComplexityLE p ∧ (V j).orbit = P₀.orbit ∧ (V j).normBound ≤ 1)
    (_hA : ∀ j, (A j).ComplexityLE p ∧ (A j).normBound ≤ 1)
    (_hB : ∀ j, (B j).ComplexityLE p ∧ (B j).normBound ≤ 1)
    (_heta : ∀ j k, rationalLogHeight (eta j ((D none).basis k)) ≤ p)
    (_htheta : ∀ j k, rationalLogHeight (theta j ((D (some (.inl none))).basis k)) ≤ p)
    (_halpha : ∀ j k, rationalLogHeight (alpha j ((D (some (.inl (some j)))).basis k)) ≤ p)
    (_hbeta : ∀ j k, rationalLogHeight (beta j ((D (some (.inr j))).basis k)) ≤ p)
    (_hvertU : ∀ j z, z ∈ (D none).filtration.realification.subgroup s → ∀ x,
      (U j).observable (z • x) = CircleFourier.character
        ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) * (U j).observable x)
    (_hvertV : ∀ j z, z ∈ (D (some (.inl none))).filtration.realification.subgroup s → ∀ x,
      (V j).observable (z • x) = CircleFourier.character
        ((realifyFunctional (theta j) z.coord : ℝ) : CircleFourier.Circle) * (V j).observable x)
    (_hvertA : ∀ j z, z ∈ (D (some (.inl (some j)))).filtration.realification.subgroup s → ∀ x,
      (A j).observable (z • x) = CircleFourier.character
        ((realifyFunctional (alpha j) z.coord : ℝ) : CircleFourier.Circle) * (A j).observable x)
    (_hvertB : ∀ j z, z ∈ (D (some (.inr j))).filtration.realification.subgroup s → ∀ x,
      (B j).observable (z • x) = CircleFourier.character
        ((realifyFunctional (beta j) z.coord : ℝ) : CircleFourier.Circle) * (B j).observable x)
    (weight : ∀ i, Fin (d i) → ℕ)
    (hFlayers : ∀ i j, (D i).filtration.layer j = Submodule.span ℚ ((D i).basis '' {k | j ≤ weight i k}))
    (origin : J → σ → ℤ) (lengths : J → σ → ℕ) (_hlengths : ∀ j i, 0 < lengths j i)
    (_hbias : ∀ j, Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox (origin j) (lengths j),
      (U j).eval x * star ((V j).eval x) * (A j).eval x * (B j).eval x‖)
    (side : σ → ℝ) (_hside : ∀ i, Real.exp ((p + C) ^ C) ≤ side i)
    (_hrelative : ∀ j i, Real.exp (-p) * side i ≤ lengths j i),
    let omega := productBasisWeight weight
    let hTotal := pi_layer_span D weight hFlayers
    let orbit := NilpotentLieFiltration.piRealOrbit (fun i => (D i).filtration)
      (fun i => (anchoredOptionReferenceData P P₀ A B i).orbit)
    let g : ((pi D).filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group :=
      ⟨⟨orbit.log, orbit.property⟩⟩
    let freq := fun j => piFrequency
      (selectedOrbitFrequencies (anchoredOptionFrequencyData eta theta alpha beta j) (anchoredOptionInputs j))
    ∃ (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded)
      (v : Fin (Fintype.card (Σ i, Fin (d i))) → (pi D).filtration.AssociatedGraded)
      (m : ℕ) (κ : (pi D).RealGroup)
      (E b R : ((pi D).filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group),
      Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
      BasisGradedSubmodule ((pi D).filtration.associatedGradedBasis (pi D).basis omega hTotal) omega W.toSubmodule ∧
      (∀ i k, rationalLogHeight (((pi D).filtration.associatedGradedBasis (pi D).basis omega hTotal).repr (v i) k) ≤
        (p + C) ^ C) ∧
      (∀ j x, x ∈ (pi D).filtration.realGradedRefiltrationLayer W s → realifyFunctional (freq j) x = 0) ∧
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ κ ∈ (pi D).realLattice ∧
      E * b * R * (pi D).filtration.realification.adaptedConstantGroupHom (fun _ => 1) κ = g ∧
      (∀ α i, |((pi D).basis.baseChange ℝ).repr
        (coefficients (E.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) α) i| ≤
          Real.exp ((p + C) ^ C) / monomialScale side α) ∧
      ((fun z : (σ →₀ ℕ) × Fin (Fintype.card (Σ i, Fin (d i))) => ((pi D).basis.baseChange ℝ).repr
        (coefficients (R.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) z.1) z.2) ∈ realDenominatorGrid m) ∧
      coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) 0 = 0 ∧
      coefficients (R.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) 0 = 0 ∧
      (∀ α, coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) α ∈
        (pi D).filtration.realGradedRefiltrationLayer W (Finsupp.weight (fun _ => 1) α)) ∧
      (∀ t : σ → ℝ, eval₂ t (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) ∈
        realificationLieSubalgebra ((pi D).filtration.gradedRefiltrationSubalgebra W)) := by
  obtain ⟨C, hC, hfactor⟩ := exists_selected_product_factorization s hs
  refine ⟨C, hC, ?_⟩
  intro J σ _ _ _ L _ _ d _ _ _ _ _ _ _ _ D P P₀ U V A B eta theta alpha beta p
    hp hcard hσ hD hU hV hA hB heta htheta halpha hbeta hvertU hvertV hvertA hvertB
    weight hFlayers origin lengths hlengths hbias side hside hrelative
  let base := anchoredOptionReferenceData P P₀ A B
  let rows := anchoredOptionObservableData U V A B
  let freq := anchoredOptionFrequencyData eta theta alpha beta
  have hJ : (Fintype.card J : ℝ) ≤ p := by
    have hh := hcard
    simp only [Fintype.card_option, Fintype.card_sum, Nat.cast_add, Nat.cast_one] at hh
    linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card J)]
  have horbit (j i) (_hi : i ∈ anchoredOptionInputs j) : (rows j i).orbit = (base i).orbit := by
    rcases i with _ | ((_ | k) | k)
    · exact (hU j).2.1
    · exact (hV j).2.1
    · rfl
    · rfl
  have hcomp (j i) (_hi : i ∈ anchoredOptionInputs j) : (rows j i).ComplexityLE p := by
    rcases i with _ | ((_ | k) | k)
    · exact (hU j).1
    · exact (hV j).1
    · exact (hA k).1
    · exact (hB k).1
  have hcap (j i) (_hi : i ∈ anchoredOptionInputs j) : (rows j i).normBound ≤ 1 := by
    rcases i with _ | ((_ | k) | k)
    · exact (hU j).2.2
    · exact (hV j).2.2
    · exact (hA k).2
    · exact (hB k).2
  have hheight (j i) (_hi : i ∈ anchoredOptionInputs j) (t) :
      rationalLogHeight (freq j i ((D i).basis t)) ≤ p := by
    rcases i with _ | ((_ | k) | k)
    · exact heta j t
    · change rationalLogHeight ((-theta j) ((D (some (.inl none))).basis t)) ≤ p
      simpa [rationalLogHeight] using htheta j t
    · exact halpha k t
    · exact hbeta k t
  have hvert (j i) (_hi : i ∈ anchoredOptionInputs j) (z)
      (hz : z ∈ (D i).filtration.realification.subgroup s) (x) :
      (rows j i).observable (z • x) = CircleFourier.character
        ((realifyFunctional (freq j i) z.coord : ℝ) : CircleFourier.Circle) * (rows j i).observable x := by
    rcases i with _ | ((_ | k) | k)
    · exact hvertU j z hz x
    · exact (V j).conjugate_vertical (theta j) (hvertV j) z hz x
    · exact hvertA k z hz x
    · exact hvertB k z hz x
  have hbias' (j) : Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox (origin j) (lengths j),
      ∏ i ∈ anchoredOptionInputs j, (rows j i).eval x‖ := by
    simpa only [rows, anchoredOptionObservableData_product] using hbias j
  exact hfactor D base rows anchoredOptionInputs freq hp hcard hJ hσ hD horbit hcomp hcap hheight hvert
    weight hFlayers origin lengths hlengths hbias' side hside hrelative

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial
open scoped TensorProduct BigOperators

theorem exists_anchored_option_mode_factorization_s2_oai (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {J σ : Type*} [Fintype J] [Fintype σ] [DecidableEq σ] {L : (Option (Option J ⊕ J)) → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d : (Option (Option J ⊕ J)) → ℕ}
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
    (P : (D none).Niltest (fun _ : σ => 1)) (P₀ : (D (some (.inl none))).Niltest (fun _ : σ => 1))
    (U : J → (D none).Niltest (fun _ : σ => 1)) (V : J → (D (some (.inl none))).Niltest (fun _ : σ => 1))
    (A : ∀ j, (D (some (.inl (some j)))).Niltest (fun _ : σ => 1)) (B : ∀ j, (D (some (.inr j))).Niltest (fun _ : σ => 1))
    (eta : J → L none →ₗ[ℚ] ℚ) (theta : J → L (some (.inl none)) →ₗ[ℚ] ℚ)
    {p : ℝ} (_hp : 2 ≤ p) (_hcard : (Fintype.card (Option (Option J ⊕ J)) : ℝ) ≤ p)
    (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hD : ∀ i, (D i).GeometryComplexityLE p)
    (_hU : ∀ j, (U j).ComplexityLE p ∧ (U j).orbit = P.orbit ∧ (U j).normBound ≤ 1)
    (_hV : ∀ j, (V j).ComplexityLE p ∧ (V j).orbit = P₀.orbit ∧ (V j).normBound ≤ 1)
    (_hA : ∀ j, (A j).ComplexityLE p ∧ (A j).normBound ≤ 1)
    (_hB : ∀ j, (B j).ComplexityLE p ∧ (B j).normBound ≤ 1)
    (_heta : ∀ j k, rationalLogHeight (eta j ((D none).basis k)) ≤ p)
    (_htheta : ∀ j k, rationalLogHeight (theta j ((D (some (.inl none))).basis k)) ≤ p)
    (_hvertU : ∀ j z, z ∈ (D none).filtration.realification.subgroup s → ∀ x,
      (U j).observable (z • x) = CircleFourier.character
        ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) * (U j).observable x)
    (_hvertV : ∀ j z, z ∈ (D (some (.inl none))).filtration.realification.subgroup s → ∀ x,
      (V j).observable (z • x) = CircleFourier.character
        ((realifyFunctional (theta j) z.coord : ℝ) : CircleFourier.Circle) * (V j).observable x)
    (weight : ∀ i, Fin (d i) → ℕ)
    (hFlayers : ∀ i j, (D i).filtration.layer j = Submodule.span ℚ ((D i).basis '' {k | j ≤ weight i k}))
    (origin : J → σ → ℤ) (lengths : J → σ → ℕ) (_hlengths : ∀ j i, 0 < lengths j i)
    (_hbias : ∀ j, Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox (origin j) (lengths j),
      (U j).eval x * star ((V j).eval x) * (A j).eval x * (B j).eval x‖)
    (side : σ → ℝ) (_hside : ∀ i, Real.exp ((p + C) ^ C) ≤ side i)
    (_hrelative : ∀ j i, Real.exp (-p) * side i ≤ lengths j i),
    let omega := productBasisWeight weight
    let hTotal := pi_layer_span D weight hFlayers
    ∃ (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded)
      (v : Fin (Fintype.card (Σ i, Fin (d i))) → (pi D).filtration.AssociatedGraded) (m : ℕ),
      Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
      BasisGradedSubmodule ((pi D).filtration.associatedGradedBasis (pi D).basis omega hTotal)
        omega W.toSubmodule ∧
      (∀ i k, rationalLogHeight
        (((pi D).filtration.associatedGradedBasis (pi D).basis omega hTotal).repr (v i) k) ≤
          (p + C) ^ C) ∧
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      HasFixedProductOrbitFactors D none
        (fun i => (anchoredOptionReferenceData P P₀ A B i).orbit) eta side ((p + C) ^ C) m W := by
  classical
  obtain ⟨c, _, hmodes⟩ := exists_native_vertical_pair_power
  obtain ⟨k, _, hfactor⟩ := exists_anchored_option_product_factorization s hs
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + (X + Polynomial.C c) ^ c + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + (Q + Polynomial.C k) ^ k)
  refine ⟨C, hC, ?_⟩
  intro J σ _ _ _ L _ _ d _ _ _ _ _ _ _ _ D P P₀ U V A B eta theta p
    hp hcard hσ hD hU hV hA hB heta htheta hvertU hvertV
    weight hFlayers origin lengths hlengths hbias side hside hrelative
  have hp0 : 0 ≤ p := by linarith
  let q := p + (p + c) ^ c + 2
  have hpow : 0 ≤ (p + c) ^ c := pow_nonneg (by positivity) _
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hq : 2 ≤ q := by dsimp [q]; linarith
  have hmodeq : (p + c) ^ c ≤ q := by dsimp [q]; linarith
  have hbud : q + (q + k) ^ k ≤ (p + C) ^ C := by
    simpa [Q, X, q, Polynomial.eval₂_pow] using hbudget p hp0
  have hkC : (q + k) ^ k ≤ (p + C) ^ C := by linarith
  have hsidepos (i) : 0 < side i := (Real.exp_pos _).trans_le (hside i)
  have hmodes' (j : J) := hmodes (D (some (.inl (some j)))) (D (some (.inr j)))
    (A j) (B j) p hp0 (hA j).1 (hB j).1
    (by exact_mod_cast (hA j).2) (by exact_mod_cast (hB j).2)
    (translatedIntegerBox (origin j) (lengths j))
    (by
      refine ⟨origin j, (mem_translatedIntegerBox _ _ _).mpr ?_⟩
      intro i
      have hi := hlengths j i
      constructor <;> omega)
    (fun x => x) (fun x => (U j).eval x * star ((V j).eval x))
    (by
      intro x _
      rw [norm_mul, norm_star]
      have hu : ‖(U j).eval x‖ ≤ 1 :=
        ((U j).norm_eval_le x).trans (by exact_mod_cast (hU j).2.2)
      have hv : ‖(V j).eval x‖ ≤ 1 :=
        ((V j).norm_eval_le x).trans (by exact_mod_cast (hV j).2.2)
      simpa only [one_mul] using mul_le_mul hu hv (norm_nonneg _) zero_le_one)
    (hbias j)
  choose alpha beta A' B' hAc hAo hAn hBc hBo hBn hAh hBh hAv hBv hcorr using hmodes'
  have hAcap (j) : (A' j).normBound ≤ 1 := by rw [hAn j]; exact (hA j).2
  have hBcap (j) : (B' j).normBound ≤ 1 := by rw [hBn j]; exact (hB j).2
  have hcorrq (j) : Real.exp (-q) ≤ ‖𝔼 x ∈ translatedIntegerBox (origin j) (lengths j),
      (U j).eval x * star ((V j).eval x) * (A' j).eval x * (B' j).eval x‖ :=
    (Real.exp_le_exp.mpr (neg_le_neg hmodeq)).trans (hcorr j)
  obtain ⟨W, v, m, κ, slow, middle, rat, hv, hW, hh, hf, hm, hmb, hκ, heq,
      hslow, hrat, hm0, hr0, hcoeff, hvalues⟩ :=
    hfactor D P P₀ U V A' B' eta theta alpha beta hq (hcard.trans hpq) (hσ.trans hpq)
      (fun i => (hD i).mono (D i) hpq)
      (fun j => ⟨(hU j).1.mono hpq, (hU j).2⟩)
      (fun j => ⟨(hV j).1.mono hpq, (hV j).2⟩)
      (fun j => ⟨(hAc j).mono hmodeq, hAcap j⟩)
      (fun j => ⟨(hBc j).mono hmodeq, hBcap j⟩)
      (fun j i => (heta j i).trans hpq) (fun j i => (htheta j i).trans hpq)
      (fun j i => (hAh j i).trans hmodeq) (fun j i => (hBh j i).trans hmodeq)
      hvertU hvertV hAv hBv weight hFlayers origin lengths hlengths hcorrq side
      (fun i => (Real.exp_le_exp.mpr hkC).trans (hside i))
      (fun j i => (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hpq))
        (hsidepos i).le).trans (hrelative j i))
  refine ⟨W, v, m, hv, hW, (fun i j => (hh i j).trans hkC), hm,
    hmb.trans (Real.exp_le_exp.mpr hkC), ?_⟩
  refine ⟨(fun j => selectedOrbitFrequencies
      (anchoredOptionFrequencyData eta theta alpha beta j) (anchoredOptionInputs j)), ?_, hf,
    κ, slow, middle, rat, hκ, ?_, ?_, hrat, hm0, hr0, hcoeff, hvalues⟩
  · intro j
    simp [selectedOrbitFrequencies, anchoredOptionFrequencyData, anchoredOptionInputs]
  · have hbase : (fun i => (anchoredOptionReferenceData P P₀ A' B' i).orbit) =
        (fun i => (anchoredOptionReferenceData P P₀ A B i).orbit) := by
      funext i
      rcases i with _ | ((_ | j) | j)
      · rfl
      · rfl
      · exact hAo j
      · exact hBo j
    simpa only [hbase] using heq
  · exact (pi D).filtration.polynomialSlowBound_mono (pi D).basis (fun _ => 1)
      side hsidepos (Real.exp_le_exp.mpr hkC) slow hslow

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Erdos3.RationalFilteredNilmanifold.exists_anchored_option_mode_factorization_s2_oai.{u_1, u_2, u_3} := @OAI.Erdos3.RationalFilteredNilmanifold.exists_anchored_option_mode_factorization_s2_oai.{u_1, u_2, u_3}
