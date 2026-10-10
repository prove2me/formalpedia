-- Prove2me | solution 1 for OAI.Erdos3.RationalFilteredNilmanifold.exists_controlled_refiltered_recovered_expansion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T08:52:28.007612+00:00
-- url     : https://prove2.me/submissions/7a819077-4c37-4d13-959c-dd74fe3ac59b

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B126
import Theorems.Thm_OAI_Erdos3_RationalFilteredNilmanifold_exists_controlled_lower_refiltered_reconstruction

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FrozenCosetVariation
namespace OAI

section

namespace Erdos3

open scoped NNReal ENNReal

variable {G : Type*} [Group G] [PseudoEMetricSpace G]

variable [IsIsometricSMul Gᵐᵒᵖ G]

end Erdos3

namespace Erdos3

open scoped NNReal

variable {G : Type*} [Group G] [MetricSpace G] [IsIsometricSMul Gᵐᵒᵖ G] [IsTopologicalGroup G]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal ENNReal

variable {G X : Type*} [Group G] [MetricSpace G]
  [IsIsometricSMul Gᵐᵒᵖ G] [IsTopologicalGroup G] [PseudoEMetricSpace X]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {G : Type*} [Group G]

variable [MetricSpace G] [IsIsometricSMul Gᵐᵒᵖ G] [IsTopologicalGroup G]

end Erdos3

end

section

namespace Erdos3

variable {G H : Type*} [Group G] [Group H]

open scoped NNReal

variable [MetricSpace G] [MetricSpace H]
  [IsIsometricSMul Gᵐᵒᵖ G] [IsIsometricSMul Hᵐᵒᵖ H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {G H : Type*} [Group G] [Group H] [MetricSpace G] [MetricSpace H]
  [IsIsometricSMul Gᵐᵒᵖ G] [IsIsometricSMul Hᵐᵒᵖ H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]
  (Γ : Subgroup G) (Λ : Subgroup H)
  (hΓ : IsClosed (Γ : Set G)) (hΛ : IsClosed (Λ : Set H))
  (φ : G →* H) (r : H) (h : ∀ γ ∈ Γ, r⁻¹ * φ γ * r ∈ Λ)

omit [MetricSpace G] [IsIsometricSMul Gᵐᵒᵖ G] [IsTopologicalGroup G] in
theorem frozenCosetMap_dist_left (a b : H) (x : G ⧸ Γ) :
    letI := rightCosetMetricSpace Λ hΛ
    dist (frozenCosetMap Γ Λ φ a r h x) (frozenCosetMap Γ Λ φ b r h x) ≤ dist a b := by
  let := rightCosetMetricSpace Λ hΛ
  induction x using Quotient.inductionOn with
  | h x =>
    have hLip := lipschitz_quotient_orbit Λ hΛ (QuotientGroup.mk (φ x * r))
    simpa only [NNReal.coe_one, one_mul, MulAction.Quotient.smul_mk, smul_eq_mul,
      mul_assoc, frozenCosetMap_mk] using hLip.dist_le_mul a b

theorem frozenCosetMap_dist_le (a b : H) {A C : ℝ≥0}
    (hφ : LipschitzWith C φ) (ha : LipschitzWith A (fun x => a * x)) (x y : G ⧸ Γ) :
    letI := rightCosetMetricSpace Γ hΓ
    letI := rightCosetMetricSpace Λ hΛ
    dist (frozenCosetMap Γ Λ φ a r h x) (frozenCosetMap Γ Λ φ b r h y) ≤
      (A * C : ℝ≥0) * dist x y + dist a b := by
  let := rightCosetMetricSpace Γ hΓ
  let := rightCosetMetricSpace Λ hΛ
  exact (dist_triangle _ (frozenCosetMap Γ Λ φ a r h y) _).trans
    (add_le_add ((lipschitz_frozenCosetMap Γ Λ hΓ hΛ φ a r h hφ ha).dist_le_mul x y)
      (frozenCosetMap_dist_left Γ Λ hΛ φ r h a b y))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InteriorIntervalCutoff
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem abs_sub_positive_sum_le {A : Type*} [Fintype A]
    (w c : A → ℝ) (t error : ℝ) (hw : ∀ a, 0 ≤ w a) (hsum : ∑ a, w a = 1)
    (herr : ∀ a, 0 < w a → |t - c a| ≤ error) :
    |t - ∑ a, w a * c a| ≤ error := by
  have hid : t - ∑ a, w a * c a = ∑ a, w a * (t - c a) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
  rw [hid]
  calc
    _ ≤ ∑ a, |w a * (t - c a)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, w a * error := by
      apply Finset.sum_le_sum
      intro a _
      rw [abs_mul, abs_of_nonneg (hw a)]
      rcases (hw a).eq_or_lt with ha | ha
      · rw [← ha, zero_mul, zero_mul]
      · exact mul_le_mul_of_nonneg_left (herr a ha) (hw a)
    _ = error := by rw [← Finset.sum_mul, hsum, one_mul]

theorem sum_pair_partition_weights {I J : Type*} [Fintype I] [Fintype J]
    (a : I → ℝ) (b : J → ℝ) (ha : ∑ i, a i = 1) (hb : ∑ j, b j = 1) :
    (∑ ij : I × J, a ij.1 * b ij.2) = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, hb, mul_one]
  exact ha

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem positiveCellParameter_of_empty {A X Ξ : Type*}
    (w : A → X → ℝ) (E : Set X) (xi : X → Ξ) (a : A)
    (h : ¬∃ x, x ∉ E ∧ 0 < w a x) : positiveCellParameter w E xi a = none := by
  simp [positiveCellParameter, h]

theorem positiveCellParameter_of_positive {A X Ξ : Type*}
    (w : A → X → ℝ) (E : Set X) (xi : X → Ξ) (a : A)
    {x : X} (hx : x ∉ E) (hpos : 0 < w a x) :
    ∃ y, y ∉ E ∧ 0 < w a y ∧ positiveCellParameter w E xi a = some (xi y) := by
  classical
  unfold positiveCellParameter
  split_ifs with h
  · exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2, rfl⟩
  · exact (h ⟨x, hx, hpos⟩).elim

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem positive_partition_sum_unit_interval {I : Type*} [Fintype I]
    (w c : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hc : ∀ i, 0 ≤ c i ∧ c i ≤ 1) :
    0 ≤ ∑ i, w i * c i ∧ ∑ i, w i * c i ≤ 1 := by
  refine ⟨Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (hc i).1), ?_⟩
  calc
    _ ≤ ∑ i, w i := Finset.sum_le_sum (fun i _ => mul_le_of_le_one_right (hw i) (hc i).2)
    _ = 1 := hsum

theorem positive_partition_approximation_mean_error {I X : Type*}
    [Fintype I] [Fintype X] [Nonempty X]
    (E : Finset X) (w c : I → X → ℝ) (T : X → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hw : ∀ i x, 0 ≤ w i x) (hsum : ∀ x, ∑ i, w i x = 1)
    (hc : ∀ i x, 0 ≤ c i x ∧ c i x ≤ 1) (hT : ∀ x, 0 ≤ T x ∧ T x ≤ 1)
    (hgood : ∀ x, x ∉ E → |T x - ∑ i, w i x * c i x| ≤ ε) :
    (𝔼 x, |T x - ∑ i, w i x * c i x|) ≤ ε + (E.card : ℝ) / Fintype.card X := by
  have hcap (x : X) : |T x - ∑ i, w i x * c i x| ≤ 1 := by
    have hc' := positive_partition_sum_unit_interval (fun i => w i x) (fun i => c i x)
      (fun i => hw i x) (hsum x) (fun i => hc i x)
    exact abs_le.mpr ⟨by linarith [(hT x).1], by linarith [(hT x).2]⟩
  simpa only [one_mul] using expect_abs_le_of_exceptional_set E _ hε hcap hgood

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem cellwise_positive_discretization_error {A X Z Ξ : Type*} [Fintype A] [PseudoMetricSpace Ξ]
    (w : A → X → ℝ) (E : Set X) (z : X → Z) (xi : X → Ξ)
    (F : A → Z → Ξ → ℝ) (T : X → ℝ) {L : ℝ≥0} {rho delta : ℝ}
    (hw : ∀ a x, 0 ≤ w a x) (hsum : ∀ x, ∑ a, w a x = 1)
    (hT : ∀ a x, x ∉ E → 0 < w a x → |T x - F a (z x) (xi x)| ≤ delta)
    (hLip : ∀ a q, LipschitzWith L (F a q))
    (hdiam : ∀ a x y, x ∉ E → y ∉ E → 0 < w a x → 0 < w a y →
      dist (xi x) (xi y) ≤ rho) (x : X) (hx : x ∉ E) :
    |T x - ∑ a, w a x * frozenRealSection (F a) (positiveCellParameter w E xi a) (z x)| ≤
      delta + L * rho := by
  apply abs_sub_positive_sum_le (fun a => w a x) _ _ _ (fun a => hw a x) (hsum x)
  intro a ha
  obtain ⟨y, hy, hwy, heq⟩ := positiveCellParameter_of_positive w E xi a hx ha
  rw [heq]
  change |T x - F a (z x) (xi y)| ≤ delta + (L : ℝ) * rho
  apply (abs_sub_le (T x) (F a (z x) (xi x)) (F a (z x) (xi y))).trans
  apply add_le_add (hT a x hx ha)
  simpa only [Real.dist_eq] using (hLip a (z x)).dist_le_mul_of_le (hdiam a x y hx hy ha hwy)

theorem exists_cellwise_positive_shift_discretization
    {I J G Ξ : Type*} [Fintype I] [Fintype J] [Add G] [PseudoMetricSpace Ξ]
    {Z : G → Type*} (A : I → G → ℝ) (B : J → G → ℝ) (E : G → Set G)
    (z : ∀ h, G → Z h) (xi : G → G → Ξ) (F : I → ∀ h, Z h → Ξ → ℝ) (T : G → G → ℝ)
    {L : ℝ≥0} {rho delta : ℝ}
    (hA : ∀ i n, 0 ≤ A i n) (hB : ∀ j n, 0 ≤ B j n)
    (hAsum : ∀ n, ∑ i, A i n = 1) (hBsum : ∀ n, ∑ j, B j n = 1)
    (hT : ∀ i h n, n ∉ E h → 0 < A i n → |T h n - F i h (z h n) (xi h n)| ≤ delta)
    (hLip : ∀ i h q, LipschitzWith L (F i h q))
    (hdiam : ∀ i j h n n', n ∉ E h → n' ∉ E h →
      0 < A i n * B j (n + h) → 0 < A i n' * B j (n' + h) →
      dist (xi h n) (xi h n') ≤ rho) :
    ∃ a : I → J → G → Option Ξ,
      (∀ i j h, (¬∃ n, n ∉ E h ∧ 0 < A i n * B j (n + h)) → a i j h = none) ∧
      ∀ h n, n ∉ E h →
        |T h n - ∑ i, ∑ j, A i n * B j (n + h) * frozenRealSection (F i h) (a i j h) (z h n)| ≤
          delta + L * rho := by
  classical
  let w : G → I × J → G → ℝ := fun h ij n => A ij.1 n * B ij.2 (n + h)
  let a : I → J → G → Option Ξ := fun i j h => positiveCellParameter (w h) (E h) (xi h) (i, j)
  refine ⟨a, ?_, ?_⟩
  · intro i j h hempty
    exact positiveCellParameter_of_empty (w h) (E h) (xi h) (i, j) hempty
  · intro h n hn
    have herror (ij : I × J) (x : G) (hx : x ∉ E h) (hpos : 0 < w h ij x) :
        |T h x - F ij.1 h (z h x) (xi h x)| ≤ delta := by
      apply hT ij.1 h x hx
      by_contra hnot
      exact not_le_of_gt hpos (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hnot) (hB ij.2 (x + h)))
    have he := cellwise_positive_discretization_error (w h) (E h) (z h) (xi h)
      (fun ij => F ij.1 h) (T h)
      (fun ij n => mul_nonneg (hA ij.1 n) (hB ij.2 (n + h)))
      (fun n => sum_pair_partition_weights (fun i => A i n) (fun j => B j (n + h))
        (hAsum n) (hBsum (n + h))) herror (fun ij => hLip ij.1 h)
      (fun ij n n' => hdiam ij.1 ij.2 h n n') n hn
    simpa only [Fintype.sum_prod_type, w, a] using he

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.IdealInvariantNiltestBudget
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

namespace RationalFilteredNilmanifold.Niltest

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

end RationalFilteredNilmanifold.Niltest

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s t d n : ℕ}
  (D : RationalFilteredNilmanifold L s d) (I : LieIdeal ℚ L)
  (hI : D.filtration.layer (t + 1) ≤ I.toSubmodule)
  (Q : RationalFilteredNilmanifold (L ⧸ I) t n)
  (hQF : Q.filtration = D.filtration.quotientLie I hI)

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ I))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ I))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ I))] [T2Space (ℝ ⊗[ℚ] (L ⧸ I))]

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

variable {σ K Ξ : Type*} [LieRing K] [LieAlgebra ℚ K] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)]
  (D : RationalFilteredNilmanifold K s d) {w : σ → ℕ}

theorem sectionNiltest_none_eval
    (g : D.filtration.realification.PolynomialOrbit w) (F : D.Space → Ξ → ℝ)
    (hF : ∀ z a, 0 ≤ F z a ∧ F z a ≤ 1) (M : ℝ≥0)
    (hLip : let := D.metricSpace; ∀ a, LipschitzWith M (fun z => F z a))
    (x : σ → ℤ) : (D.sectionNiltest g F hF M hLip none).eval x = 0 := rfl

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
  (T : D.Niltest w) (hT : T.UnitIntervalValued)
  (psi : D.Space → ℝ) (hpsi : ∀ z, 0 ≤ psi z ∧ psi z ≤ 1)
  (K : ℝ≥0) (hLip : letI := D.metricSpace; LipschitzWith K psi)

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.CellwiseNiltestDiscretization
namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct NNReal

theorem exists_cellwise_niltest_discretization
    {I J Ξ : Type*} [Fintype I] [Fintype J] [PseudoMetricSpace Ξ]
    (N : ℕ) [NeZero N] {K : ZMod N → Type*}
    [∀ h, LieRing (K h)] [∀ h, LieAlgebra ℚ (K h)] {s : ℕ} {d : ZMod N → ℕ}
    [∀ h, TopologicalSpace (ℝ ⊗[ℚ] K h)] [∀ h, IsTopologicalAddGroup (ℝ ⊗[ℚ] K h)]
    [∀ h, ContinuousSMul ℝ (ℝ ⊗[ℚ] K h)] [∀ h, T2Space (ℝ ⊗[ℚ] K h)]
    (D : ∀ h, RationalFilteredNilmanifold (K h) s (d h))
    (g : ∀ h, (D h).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (F : I → ∀ h, (D h).Space → Ξ → ℝ)
    (A : I → ZMod N → ℝ) (B : J → ZMod N → ℝ) (E : ZMod N → Set (ZMod N))
    (xi : ZMod N → ZMod N → Ξ) (T : ZMod N → ZMod N → ℝ)
    {L M : ℝ≥0} {rho delta p : ℝ}
    (hA : ∀ i n, 0 ≤ A i n) (hB : ∀ j n, 0 ≤ B j n)
    (hAsum : ∀ n, ∑ i, A i n = 1) (hBsum : ∀ n, ∑ j, B j n = 1)
    (hF : ∀ i h z a, 0 ≤ F i h z a ∧ F i h z a ≤ 1)
    (hFirstLip : ∀ i h, let := (D h).metricSpace; ∀ a, LipschitzWith M (fun z => F i h z a))
    (hSecondLip : ∀ i h z, LipschitzWith L (F i h z))
    (hGeometry : ∀ h, (D h).GeometryComplexityLE p)
    (hBudget : Real.log (3 + (M : ℝ)) ≤ p)
    (hT : ∀ i h n, n ∉ E h → 0 < A i n →
      |T h n - F i h ((D h).cyclicOrbitPoint (g h) N (fun _ : Unit => n)) (xi h n)| ≤ delta)
    (hdiam : ∀ i j h n n', n ∉ E h → n' ∉ E h →
      0 < A i n * B j (n + h) → 0 < A i n' * B j (n' + h) →
      dist (xi h n) (xi h n') ≤ rho) :
    ∃ U : I → J → (h : ZMod N) → (D h).Niltest (fun _ : Unit => 1),
      (∀ i j h, (U i j h).UnitIntervalValued) ∧
      (∀ i j h, (U i j h).ComplexityLE p) ∧
      (∀ i j h, (¬∃ n, n ∉ E h ∧ 0 < A i n * B j (n + h)) →
        ∀ x, (U i j h).eval x = 0) ∧
      ∀ h n, n ∉ E h →
        |T h n - ∑ i, ∑ j, A i n * B j (n + h) *
          ((U i j h).evalCyclic N (fun _ : Unit => n)).re| ≤ delta + L * rho := by
  let z : (h : ZMod N) → ZMod N → (D h).Space :=
    fun h n => (D h).cyclicOrbitPoint (g h) N (fun _ : Unit => n)
  obtain ⟨a, hempty, herr⟩ := exists_cellwise_positive_shift_discretization A B E z xi F T
    hA hB hAsum hBsum hT hSecondLip hdiam
  let U : I → J → (h : ZMod N) → (D h).Niltest (fun _ : Unit => 1) :=
    fun i j h => (D h).sectionNiltest (g h) (F i h) (hF i h) M (hFirstLip i h) (a i j h)
  refine ⟨U, ?_, ?_, ?_, ?_⟩
  · intro i j h
    exact (D h).sectionNiltest_unit_interval (g h) (F i h) (hF i h) M (hFirstLip i h) (a i j h)
  · intro i j h
    exact (D h).sectionNiltest_complexityLE (g h) (F i h) (hF i h) M (hFirstLip i h)
      (a i j h) (hGeometry h) hBudget
  · intro i j h hcell x
    dsimp only [U]
    rw [hempty i j h hcell]
    exact (D h).sectionNiltest_none_eval (g h) (F i h) (hF i h) M (hFirstLip i h) x
  · intro h n hn
    have heval (i : I) (j : J) : ((U i j h).evalCyclic N (fun _ : Unit => n)).re =
        frozenRealSection (F i h) (a i j h) (z h n) := rfl
    simpa only [heval] using herr h n hn

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.CyclicNiltestApproximation
namespace OAI

section

open scoped NNReal

namespace Erdos3

end Erdos3

end

section

open Module
open scoped BigOperators

namespace Erdos3.RationalFilteredNilmanifold

variable {ι : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

end Erdos3.RationalFilteredNilmanifold

end

section

open Module
open scoped TensorProduct BigOperators

namespace Erdos3.RationalFilteredNilmanifold

variable {ι : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

variable [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3

namespace RationalFilteredNilmanifold

open Module
open scoped TensorProduct

variable {ι : Type v} [Fintype ι] {L₀ : Type u} {L : ι → Type u}
  [LieRing L₀] [∀ i, LieRing (L i)] [LieAlgebra ℚ L₀] [∀ i, LieAlgebra ℚ (L i)]
  {s d₀ : ℕ} {d : ι → ℕ}
  (D₀ : RationalFilteredNilmanifold L₀ s d₀)
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

variable {H : Type u} [LieRing H] [LieAlgebra ℚ H]

end RationalFilteredNilmanifold
end Erdos3

end

section

open scoped TensorProduct BigOperators NNReal

namespace Erdos3.RationalFilteredNilmanifold

variable {ι σ : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) {w : σ → ℕ}

end Erdos3.RationalFilteredNilmanifold

end

section

open scoped TensorProduct BigOperators

namespace Erdos3.RationalFilteredNilmanifold

end Erdos3.RationalFilteredNilmanifold

end

section

open scoped TensorProduct BigOperators

namespace Erdos3.RationalFilteredNilmanifold

variable {ι σ : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

variable [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
  {w : σ → ℕ}

end Erdos3.RationalFilteredNilmanifold

end

section

open scoped TensorProduct BigOperators NNReal

namespace Erdos3.RationalFilteredNilmanifold

variable {ι σ : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) {w : σ → ℕ}

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

namespace RationalFilteredNilmanifold

namespace Niltest

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

end Niltest
end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem exists_cellwise_niltest_error
    {I J : Type*} [Fintype I] [Fintype J] (N : ℕ) [NeZero N]
    {K : ZMod N → Type*} [∀ h, LieRing (K h)] [∀ h, LieAlgebra ℚ (K h)]
    [∀ h, TopologicalSpace (ℝ ⊗[ℚ] K h)] [∀ h, IsTopologicalAddGroup (ℝ ⊗[ℚ] K h)]
    [∀ h, ContinuousSMul ℝ (ℝ ⊗[ℚ] K h)] [∀ h, T2Space (ℝ ⊗[ℚ] K h)]
    {s : ℕ} {d : ZMod N → ℕ} (D : ∀ h, RationalFilteredNilmanifold (K h) s (d h))
    (U : I → J → (h : ZMod N) → (D h).Niltest (fun _ : Unit => 1))
    (A : I → ZMod N → ℝ) (B : J → ZMod N → ℝ)
    (T : ZMod N → ZMod N → ℝ) (E : ZMod N → Finset (ZMod N))
    {ε : ℝ} (hε : 0 ≤ ε)
    (hA : ∀ i n, 0 ≤ A i n) (hB : ∀ j n, 0 ≤ B j n)
    (hAsum : ∀ n, ∑ i, A i n = 1) (hBsum : ∀ n, ∑ j, B j n = 1)
    (hT : ∀ h n, 0 ≤ T h n ∧ T h n ≤ 1)
    (hU : ∀ i j h, (U i j h).UnitIntervalValued)
    (hgood : ∀ h n, n ∉ E h →
      |T h n - ∑ i, ∑ j, A i n * B j (n + h) *
        ((U i j h).evalCyclic N (fun _ : Unit => n)).re| ≤ ε) :
    ∃ e : ZMod N → ZMod N → ℝ,
      (∀ h n, T h n = (∑ i, ∑ j, A i n * B j (n + h) *
        ((U i j h).evalCyclic N (fun _ : Unit => n)).re) + e h n) ∧
      ∀ h, (𝔼 n, |e h n|) ≤ ε + ((E h).card : ℝ) / N := by
  let e : ZMod N → ZMod N → ℝ := fun h n =>
    T h n - ∑ i, ∑ j, A i n * B j (n + h) * ((U i j h).evalCyclic N (fun _ : Unit => n)).re
  refine ⟨e, fun h n => by dsimp [e]; ring, ?_⟩
  intro h
  have hmean := positive_partition_approximation_mean_error (E h)
    (fun ij : I × J => fun n => A ij.1 n * B ij.2 (n + h))
    (fun ij : I × J => fun n => ((U ij.1 ij.2 h).evalCyclic N (fun _ : Unit => n)).re)
    (T h) hε
    (fun ij n => mul_nonneg (hA ij.1 n) (hB ij.2 (n + h)))
    (fun n => sum_pair_partition_weights (fun i => A i n) (fun j => B j (n + h))
      (hAsum n) (hBsum (n + h)))
    (fun ij n => ((U ij.1 ij.2 h).unit_interval_evalCyclic (hU ij.1 ij.2 h) N (fun _ : Unit => n)).2)
    (hT h) (fun n hn => by simpa only [Fintype.sum_prod_type] using hgood h n hn)
  simpa only [e, Fintype.sum_prod_type, ZMod.card] using hmean

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators NNReal

theorem exists_cyclic_cellwise_niltest_approximation
    {I J Ξ : Type*} [Fintype I] [Fintype J] [PseudoMetricSpace Ξ]
    (N : ℕ) [NeZero N] {K : ZMod N → Type*}
    [∀ h, LieRing (K h)] [∀ h, LieAlgebra ℚ (K h)] {s : ℕ} {d : ZMod N → ℕ}
    [∀ h, TopologicalSpace (ℝ ⊗[ℚ] K h)] [∀ h, IsTopologicalAddGroup (ℝ ⊗[ℚ] K h)]
    [∀ h, ContinuousSMul ℝ (ℝ ⊗[ℚ] K h)] [∀ h, T2Space (ℝ ⊗[ℚ] K h)]
    (D : ∀ h, RationalFilteredNilmanifold (K h) s (d h))
    (g : ∀ h, (D h).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (F : I → ∀ h, (D h).Space → Ξ → ℝ)
    (A : I → ZMod N → ℝ) (B : J → ZMod N → ℝ)
    (xi : ZMod N → ZMod N → Ξ) (T : ZMod N → ZMod N → ℝ)
    {L M : ℝ≥0} {ρ δ η p : ℝ} (hρ : 0 < ρ) (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hA : ∀ i n, 0 ≤ A i n) (hB : ∀ j n, 0 ≤ B j n)
    (hAsum : ∀ n, ∑ i, A i n = 1) (hBsum : ∀ n, ∑ j, B j n = 1)
    (hF : ∀ i h z a, 0 ≤ F i h z a ∧ F i h z a ≤ 1)
    (hFirstLip : ∀ i h, let := (D h).metricSpace; ∀ a, LipschitzWith M (fun z => F i h z a))
    (hSecondLip : ∀ i h z, LipschitzWith L (F i h z))
    (hGeometry : ∀ h, (D h).GeometryComplexityLE p)
    (hBudget : Real.log (3 + (M : ℝ)) ≤ p)
    (hT : ∀ h n, 0 ≤ T h n ∧ T h n ≤ 1)
    (happrox : ∀ i h n, n ∉ cyclicWrapExceptional h ρ → 0 < A i n →
      |T h n - F i h ((D h).cyclicOrbitPoint (g h) N (fun _ : Unit => n)) (xi h n)| ≤ δ)
    (hdiam : ∀ i j h n n', n ∉ cyclicWrapExceptional h ρ → n' ∉ cyclicWrapExceptional h ρ →
      0 < A i n * B j (n + h) → 0 < A i n' * B j (n' + h) → dist (xi h n) (xi h n') ≤ η) :
    ∃ U : I → J → (h : ZMod N) → (D h).Niltest (fun _ : Unit => 1),
      (∀ i j h, (U i j h).UnitIntervalValued) ∧
      (∀ i j h, (U i j h).ComplexityLE p) ∧
      (∀ i j h, (¬∃ n, n ∉ cyclicWrapExceptional h ρ ∧ 0 < A i n * B j (n + h)) →
        ∀ x, (U i j h).eval x = 0) ∧
      (∀ h n, n ∉ cyclicWrapExceptional h ρ →
        |T h n - ∑ i, ∑ j, A i n * B j (n + h) *
          ((U i j h).evalCyclic N (fun _ : Unit => n)).re| ≤ δ + L * η) ∧
      ∃ e : ZMod N → ZMod N → ℝ,
        (∀ h n, T h n = (∑ i, ∑ j, A i n * B j (n + h) *
          ((U i j h).evalCyclic N (fun _ : Unit => n)).re) + e h n) ∧
        ∀ h, (𝔼 n, |e h n|) ≤ δ + L * η + 6 * ρ + 3 / N := by
  obtain ⟨U, hU, hUcomplexity, hUempty, hgood⟩ := exists_cellwise_niltest_discretization
    N D g F A B (fun h => ↑(cyclicWrapExceptional h ρ)) xi T
    hA hB hAsum hBsum hF hFirstLip hSecondLip hGeometry hBudget happrox hdiam
  have herror : 0 ≤ δ + (L : ℝ) * η := add_nonneg hδ (mul_nonneg L.coe_nonneg hη)
  obtain ⟨e, heval, hmean⟩ := exists_cellwise_niltest_error N D U A B T
    (fun h => cyclicWrapExceptional h ρ) herror hA hB hAsum hBsum hT hU hgood
  refine ⟨U, hU, hUcomplexity, hUempty, hgood, e, heval, ?_⟩
  intro h
  calc
    _ ≤ δ + (L : ℝ) * η + ((cyclicWrapExceptional h ρ).card : ℝ) / N := hmean h
    _ ≤ δ + (L : ℝ) * η + (6 * ρ + 3 / N) := by
      linarith [cyclicWrapExceptional_density_le h hρ.le]
    _ = _ := by ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformControlledNativeExternalNetsOfRecovery
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {X Y : Type*} [Nonempty X] [PseudoMetricSpace Y]
  (φ : X → Y) (L : ℝ≥0)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {X Y Z : Type*} [Nonempty X] [PseudoMetricSpace Y] [PseudoMetricSpace Z]
  (φ : X → Y × Z) (L : ℝ≥0)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {X Y Z : Type*} [Nonempty X] [PseudoMetricSpace Y] [PseudoMetricSpace Z]
  (φ : X → Y × Z) (K : ℝ≥0) (f : X → ℂ)
  (hf : ∀ x, 0 ≤ (f x).re)
  (hrecovery : ∀ x, positiveImageSlice φ K f (φ x).2 (φ x).1 = f x)

include hf hrecovery

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped TensorProduct

namespace NilpotentLieFiltration

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

end NilpotentLieFiltration

namespace RationalFilteredNilmanifold

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d) (w : σ → ℕ)

namespace Niltest

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

end Niltest
end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem eval_freeze_of_lattice_factorization (T : D.Niltest w)
    (E b R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
    (κ : D.RealGroup) (hκ : κ ∈ D.realLattice)
    (hprod : E * b * R * D.filtration.realification.adaptedConstantGroupHom w κ =
      ⟨⟨T.orbit.log, T.orbit.property⟩⟩) (x : σ → ℤ) (a₀ r₀ : D.RealGroup)
    {p δ : ℝ} (hT : T.ComplexityLE p)
    (hr : (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) R) : D.Space) =
      QuotientGroup.mk r₀)
    (hE : letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
      dist (D.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) E) a₀ ≤ δ) :
    ‖T.eval x - T.observable (QuotientGroup.mk
      (a₀ * D.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) b * r₀))‖ ≤
      Real.exp p * δ := by
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  have hLip : (T.lipBound : ℝ) ≤ Real.exp p := by
    have hb := T.observable_budget hT
    linarith [T.normBound.coe_nonneg]
  rw [eval_of_lattice_factorization D w T E b R κ hκ hprod x]
  exact (T.observable_freeze_factors _ a₀ _ _ r₀ hr).trans
    ((mul_le_mul_of_nonneg_right hLip dist_nonneg).trans
      (mul_le_mul_of_nonneg_left hE (Real.exp_pos p).le))

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (D : RationalFilteredNilmanifold L s d)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeMarkedDiagramOrbitLift
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d n : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  (Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n)
  (hQ : Q.filtration = D.filtration.quotientTop) {w : σ → ℕ}

theorem topQuotientOrbit_cyclicOrbitPoint
    (g : D.filtration.realification.PolynomialOrbit w) (N : ℕ) [NeZero N] (x : σ → ZMod N) :
    Q.cyclicOrbitPoint (D.topQuotientOrbit Q hQ g) N x =
      (QuotientGroup.mk (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot)
        (lieQuotientMap (D.filtration.layerIdeal (s + 1)))
        (D.filtration.realification.polynomialOrbitEval w (fun i => ((x i).val : ℤ)) g)) : Q.Space) := by
  exact congrArg (QuotientGroup.mk : Q.RealGroup → Q.Space)
    (D.topQuotientOrbit_eval Q hQ g (fun i => ((x i).val : ℤ)))

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup NilpotentLieFiltration VectorPolynomial
open scoped TensorProduct

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d n : ℕ}
    (D : RationalFilteredNilmanifold L (s + 1) d)
    (Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n)
    (hQ : Q.filtration = D.filtration.quotientTop) {w : σ → ℕ}

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (G : NilpotentLieFiltration M (s + 1))
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.RationalFilteredNilmanifold

open VectorPolynomial NilpotentLieFiltration
open scoped TensorProduct

variable {L M σ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d n : ℕ}
    (D : RationalFilteredNilmanifold L (s + 1) d)
    (G : NilpotentLieFiltration M (s + 1))
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ G.layer j)
    (Q : RationalFilteredNilmanifold
      (L ⧸ D.filtration.layerIdeal (s + 1)) s n)
    (hQ : Q.filtration = D.filtration.quotientTop) {w : σ → ℕ}

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open VectorPolynomial NilpotentLieFiltration
open scoped TensorProduct

variable {L M σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s d e n m : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  (E : RationalFilteredNilmanifold M (s + 1) e)
  (φ : L →ₗ⁅ℚ⁆ M)
  (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ E.filtration.layer j)

variable (Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n)
  (hQ : Q.filtration = D.filtration.quotientTop)
  (QF : RationalFilteredNilmanifold (M ⧸ E.filtration.layerIdeal (s + 1)) s m)
  (hQF : QF.filtration = E.filtration.quotientTop) {w : σ → ℕ}

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration VectorPolynomial

variable {L M ι κ σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s d f nE nF : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  (Fmark : RationalFilteredNilmanifold M (s + 1) f)
  (φ : L →ₗ⁅ℚ⁆ M)
  (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
  (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
  (E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nE)
  (hE : E.filtration = D.filtration.gradedRefiltration W)
  (EF : RationalFilteredNilmanifold
    (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
  (hEF : EF.filtration = Fmark.filtration.gradedRefiltration
    (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))

include hE hEF

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d e n m : ℕ}
    (D : RationalFilteredNilmanifold L (s + 1) d)
    (E : RationalFilteredNilmanifold M (s + 1) e)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ E.filtration.layer j)
    (Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n)
    (QF : RationalFilteredNilmanifold (M ⧸ E.filtration.layerIdeal (s + 1)) s m)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s d e n m : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  (E : RationalFilteredNilmanifold M (s + 1) e)
  (φ : L →ₗ⁅ℚ⁆ M)
  (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ E.filtration.layer j)
  (Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n)
  (hQ : Q.filtration = D.filtration.quotientTop)
  (QF : RationalFilteredNilmanifold (M ⧸ E.filtration.layerIdeal (s + 1)) s m)
  (hQF : QF.filtration = E.filtration.quotientTop)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open VectorPolynomial NilpotentLieFiltration NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L M σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s d e n m : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  (E : RationalFilteredNilmanifold M (s + 1) e)
  (φ : L →ₗ⁅ℚ⁆ M)
  (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ E.filtration.layer j)
  (Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n)
  (hQ : Q.filtration = D.filtration.quotientTop)
  (QF : RationalFilteredNilmanifold (M ⧸ E.filtration.layerIdeal (s + 1)) s m)
  (hQF : QF.filtration = E.filtration.quotientTop) {w : σ → ℕ}

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeOrbitFreezing
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_slow_factor_freezing (s r : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (w : σ → ℕ),
      (∀ i, 0 < w i) → ∀ (p : ℝ), 0 ≤ p → (Fintype.card σ : ℝ) ≤ p →
      ∀ S : D.Niltest w, S.ComplexityLE p →
      ∀ (E b R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
        (κ : D.RealGroup), κ ∈ D.realLattice →
        E * b * R * D.filtration.realification.adaptedConstantGroupHom w κ =
          ⟨⟨S.orbit.log, S.orbit.property⟩⟩ →
        ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
          D.filtration.PolynomialSlowBound D.basis w T (Real.exp ((p + 2) ^ r)) E →
          ∀ (x : σ → ℤ) (z : σ → ℝ) (r₀ : D.RealGroup) (δ : ℝ), 0 ≤ δ →
            (∀ i, |(x i : ℝ)| ≤ T i) → (∀ i, |z i| ≤ T i) →
            (∀ i, |(x i : ℝ) - z i| ≤ T i * δ) →
            (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w
              (fun i => (x i : ℝ)) R) : D.Space) = QuotientGroup.mk r₀ →
            ‖S.eval x - S.observable (QuotientGroup.mk
              (D.filtration.adaptedPolynomialRealValueHom w z E *
                D.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) b * r₀))‖ ≤
              Real.exp ((p + C) ^ C) * δ := by
  obtain ⟨a, _, hmove⟩ := exists_polynomialSlowBound_dist_exp s r
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Polynomial.X + (Polynomial.X + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ _ d D w hw p hp hσ S hS E b R κ hκ hprod T hT hE x z r₀ δ hδ hx hz hxz hR
  have hdist := hmove D w hw p hp hS.1 hσ T hT E hE
    (fun i => (x i : ℝ)) z δ hδ hx hz hxz
  have hfreeze := S.eval_freeze_of_lattice_factorization E b R κ hκ hprod x
    (D.filtration.adaptedPolynomialRealValueHom w z E) r₀ hS hR hdist
  apply hfreeze.trans
  rw [← mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr _) hδ
  simpa [Polynomial.eval₂_pow] using hbudget p hp

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open NilpotentLieBCHGroup
open scoped TensorProduct

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3

open VectorPolynomial
open scoped TensorProduct

namespace NilpotentLieFiltration

end NilpotentLieFiltration

namespace RationalFilteredNilmanifold

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSharedFrozenCorrelations
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
  {s d e : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
  (φ : L →ₗ⁅ℚ⁆ M) (a r : E.RealGroup)
  (h : ∀ γ ∈ D.realLattice,
    r⁻¹ * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ γ * r ∈ E.realLattice)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem native_frozenCosetMap_dist_le {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)] {s d e : ℕ}
    (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
    (φ : L →ₗ⁅ℚ⁆ M) (r a b : E.RealGroup)
    (h : ∀ γ ∈ D.realLattice, r⁻¹ * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ γ * r ∈ E.realLattice)
    {A C : ℝ≥0}
    (hφ :
      letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
      letI := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
      LipschitzWith C (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ))
    (ha :
      letI := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
      LipschitzWith A (fun x => a * x)) (x y : D.RealGroup) :
    letI := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot)
      (E.basis.baseChange ℝ)
    letI := D.metricSpace
    letI := E.metricSpace
    let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ
    dist (QuotientGroup.mk (a * ψ x * r) : E.Space) (QuotientGroup.mk (b * ψ y * r)) ≤
      (A * C : ℝ≥0) * dist (QuotientGroup.mk x : D.Space) (QuotientGroup.mk y) + dist a b := by
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] L) := (D.basis.baseChange ℝ).finiteDimensional_of_finite
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] M) := (E.basis.baseChange ℝ).finiteDimensional_of_finite
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul (hnil := E.filtration.realification.lowerCentralSeries_eq_bot)
    (E.basis.baseChange ℝ)
  exact frozenCosetMap_dist_le D.realLattice E.realLattice D.realLattice_closed_discrete.1
    E.realLattice_closed_discrete.1 _ r h a b hφ ha (QuotientGroup.mk x) (QuotientGroup.mk y)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

theorem mapped_normal_conjugation_mem {G H : Type*} [Group G] [Group H]
    (Γ Λ : Subgroup G) (hle : Λ ≤ Γ) (hnormal : (Λ.subgroupOf Γ).Normal)
    (f : G →* H) {κ x : H} (hκ : κ ∈ Γ.map f) (hx : x ∈ Λ.map f) :
    κ * x * κ⁻¹ ∈ Λ.map f := by
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hκ
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  refine Subgroup.mem_map.mpr ⟨k * y * k⁻¹,
    (Subgroup.normal_subgroupOf_iff hle).mp hnormal y k hy hk, ?_⟩
  simp only [map_mul, map_inv]

namespace RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

theorem normalized_right_compatibility {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d e : ℕ}
    (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
    (φ : L →ₗ⁅ℚ⁆ M) (q : ℕ) (hq : 0 < q) (Λ : Subgroup D.filtration.Group)
    (hconj : Λ ≤ D.conjugationPullback E φ q) (hle : Λ ≤ D.lattice)
    (hnormal : (Λ.subgroupOf D.lattice).Normal)
    (κ : D.RealGroup) (hκ : κ ∈ D.realLattice) (r : E.RealGroup)
    (hr : (E.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q) :
    let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ
    ∀ x ∈ Λ.map realificationHom, (ψ κ⁻¹ * r)⁻¹ * ψ x * (ψ κ⁻¹ * r) ∈ E.realLattice := by
  let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
    (hM := E.filtration.lowerCentralSeries_eq_bot) φ
  have hright := D.real_conjugationPullback_property E φ q hq Λ hconj r hr
  dsimp only
  intro x hx
  have hmem := mapped_normal_conjugation_mem D.lattice Λ hle hnormal realificationHom hκ hx
  have heq : (ψ κ⁻¹ * r)⁻¹ * ψ x * (ψ κ⁻¹ * r) = r⁻¹ * ψ (κ * x * κ⁻¹) * r := by
    simp only [map_mul, map_inv]
    group
  rw [heq]
  exact hright _ hmem

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LowerRefilteredCyclicExpansion
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped NNReal TensorProduct

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped NNReal TensorProduct

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {L : ι → Type u}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
  (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
  (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
  (Q : RationalFilteredNilmanifold
    (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  [TopologicalSpace (ℝ ⊗[ℚ] L a)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L a)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L a)] [T2Space (ℝ ⊗[ℚ] L a)]

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {L : ι → Type u}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
  (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
  (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
  (Q : RationalFilteredNilmanifold
    (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  [TopologicalSpace (ℝ ⊗[ℚ] L a)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L a)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L a)] [T2Space (ℝ ⊗[ℚ] L a)]

theorem LowerRefilteredRecoveryFamily.mono_cost {p cost cost' : ℝ} {q k : ℕ}
    (h : LowerRefilteredRecoveryFamily D a W E Q p q k cost) (hc : cost ≤ cost') :
    LowerRefilteredRecoveryFamily D a W E Q p q k cost' := by
  obtain ⟨Q', hQF, hQb, hQle, hQ, Z, hZF, hZb, hZle, hZ, hrec⟩ := h
  refine ⟨Q', hQF, hQb, hQle, hQ.mono Q' hc, Z, hZF, hZb, hZle, hZ.mono Z hc, ?_⟩
  intro J eta hfreq l r hl hr S ℓ hℓ hS hpositive hinvariant
  obtain ⟨v, K, hK, hv, hpos, heval⟩ := hrec eta hfreq l r hl hr S ℓ hℓ hS hpositive hinvariant
  exact ⟨v, K, hK.trans (Real.exp_le_exp.mpr hc), hv, hpos, heval⟩

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {L : ι → Type u}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
  (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
  (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
  (Q : RationalFilteredNilmanifold
    (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  [TopologicalSpace (ℝ ⊗[ℚ] L a)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L a)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L a)] [T2Space (ℝ ⊗[ℚ] L a)]

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

theorem exists_lower_refiltered_cyclic_expansion (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] {L : ι → Type u}
      [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d : ι → ℕ}
      (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
      (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
      (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
      (Q : RationalFilteredNilmanifold
        (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
      [TopologicalSpace (ℝ ⊗[ℚ] L a)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L a)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L a)] [T2Space (ℝ ⊗[ℚ] L a)]
      {p cost : ℝ} {q : ℕ}, 1 ≤ p → 0 ≤ cost → Q.filtration = E.filtration.quotientTop →
      LowerRefilteredRecoveryFamily D a W E Q p q k cost →
      LowerRefilteredCyclicExpansionSpec D a W E Q p q k cost C := by
  obtain ⟨C, hC, hfreeze⟩ := Niltest.exists_slow_factor_freezing (s + 1) k
  refine ⟨C, hC, ?_⟩
  intro ι _ _ L _ _ d D a W e n E Q _ _ _ _ p cost q hp hcost hquot hrec
  classical
  let H := (pi D).filtration.gradedRefiltrationSubalgebra W
  let I₀ := {i : ι // i ≠ a}
  let Z₀ := pi (fun i : I₀ => D i.val)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  let := realification_moduleTopology_t2 Q.basis
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i : I₀, L i.val))
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i : I₀, L i.val))
  let := realification_moduleTopology_t2 Z₀.basis
  obtain ⟨Q', hQF, hQb, hQle, hQ, Z, hZF, hZb, hZle, hZ, hreconstruct⟩ := hrec
  refine ⟨Q', hQF, hQb, hQle, hQ, Z, hZF, hZb, hZle, hZ, ?_⟩
  let := Q'.metricSpace
  let := Z.metricSpace
  dsimp only
  intro J₀ freq hfreq N _ I J _ _ A B ρ η hρ hη hA hB hAsum hBsum
    S hS hpositive hinvariant slow middle rat κ g hκ hfactor hslow hmiddle
    anchor r₀ hanchor hleft hright hnear hrat hdiam
  let w := fun _ : Unit => 1
  let φ := realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
    (hM := (D a).filtration.lowerCentralSeries_eq_bot) (refilteredComponentMap D W a)
  let ψ := realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
    (hM := Z.filtration.lowerCentralSeries_eq_bot)
    (liePiMap (fun i : I₀ => refilteredComponentMap D W i.val))
  let qg := fun h => E.topQuotientOrbit Q' (hQF.trans hquot) (g h)
  let left := fun i h => (D a).filtration.adaptedPolynomialRealValueHom w
    (fun _ => anchor i h) (slow h)
  have hLip (h : ZMod N) : ((S h).lipBound : ℝ) ≤ Real.exp p := by
    have hb := Niltest.observable_budget (hS h)
    linarith [(S h).normBound.coe_nonneg]
  have hex (i : I) (h : ZMod N) := hreconstruct freq hfreq (left i h) (r₀ i h)
    (hleft i h) (hright i h) (S h).observable (S h).lipBound (hLip h)
    (S h).lipschitz (hpositive h) (hinvariant h)
  choose v K hK hv hpos heval using hex
  let bound : ℝ≥0 := ⟨Real.exp cost, (Real.exp_pos cost).le⟩
  let F := fun i h (z : Q'.Space) (a : Z.Space) => (v i h (z, a)).re
  have hF (i : I) (h : ZMod N) (z : Q'.Space) (a : Z.Space) :
      0 ≤ F i h z a ∧ F i h z a ≤ 1 := (hpos i h (z, a)).2
  have hvbound (i : I) (h : ZMod N) : LipschitzWith bound (v i h) :=
    (hv i h).weaken (hK i h)
  have hFirst (i : I) (h : ZMod N) (a : Z.Space) : LipschitzWith bound (fun z => F i h z a) := by
    simpa only [F, one_mul, mul_one, Function.comp_def, RCLike.re_eq_complex_re] using
      (RCLike.lipschitzWith_re (K := ℂ)).comp ((hvbound i h).comp (LipschitzWith.prodMk_right a))
  have hSecond (i : I) (h : ZMod N) (z : Q'.Space) : LipschitzWith bound (F i h z) := by
    simpa only [F, one_mul, mul_one, Function.comp_def, RCLike.re_eq_complex_re] using
      (RCLike.lipschitzWith_re (K := ℂ)).comp ((hvbound i h).comp (LipschitzWith.prodMk_left z))
  have hbudget : Real.log (3 + (bound : ℝ)) ≤ cost + 2 := by
    apply (Real.log_le_iff_le_exp (by positivity)).mpr
    have h1 : 1 ≤ Real.exp cost := Real.one_le_exp hcost
    have h2 : (4 : ℝ) ≤ Real.exp 2 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith [Real.add_one_le_exp (1 : ℝ)]
    change 3 + Real.exp cost ≤ Real.exp (cost + 2)
    rw [Real.exp_add]
    nlinarith [mul_le_mul_of_nonneg_left h2 (Real.exp_nonneg cost)]
  let xi : ZMod N → ZMod N → Z.Space := fun h x =>
    QuotientGroup.mk (ψ (E.filtration.realification.polynomialOrbitEval w (fun _ => (x.val : ℤ)) (g h)))
  let target := fun h x => ((S h).evalCyclic N (fun _ => x)).re
  have htarget (h x : ZMod N) : 0 ≤ target h x ∧ target h x ≤ 1 :=
    (hpositive h _).2
  have happrox (i : I) (h x : ZMod N) (hx : x ∉ cyclicWrapExceptional h ρ) (hAx : 0 < A i x) :
      |target h x - F i h (Q'.cyclicOrbitPoint (qg h) N (fun _ => x)) (xi h x)| ≤
        Real.exp ((p + C) ^ C) * ρ := by
    have hxN : |((x.val : ℤ) : ℝ)| ≤ (N : ℝ) := by
      rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast (Nat.le_of_lt (ZMod.val_lt x))
    have hfrozen := hfreeze (D a) w (fun _ => by decide) p (by linarith)
      (by simpa only [Fintype.card_unit, Nat.cast_one] using hp) (S h) (hS h)
      (slow h) (middle h) (rat h) (κ h) (hκ h) (hfactor h) (fun _ => (N : ℝ))
      (fun _ => Nat.cast_pos.mpr (NeZero.pos N)) (hslow h)
      (fun _ => (x.val : ℤ)) (fun _ => anchor i h) (r₀ i h) ρ hρ.le
      (fun _ => hxN) (fun _ => hanchor i h)
      (fun _ => by simpa only [Int.cast_natCast] using hnear i h x hx hAx)
      (by simpa only [Int.cast_natCast] using hrat i h x hx hAx)
    have hsection := heval i h
      (E.filtration.realification.polynomialOrbitEval w (fun _ => (x.val : ℤ)) (g h))
    have hreal : F i h (Q'.cyclicOrbitPoint (qg h) N (fun _ => x)) (xi h x) =
        ((S h).observable (QuotientGroup.mk (left i h *
          (D a).filtration.adaptedPolynomialRealValueHom w (fun _ => ((x.val : ℤ) : ℝ)) (middle h) * r₀ i h))).re := by
      dsimp only [F, qg, xi]
      rw [E.topQuotientOrbit_cyclicOrbitPoint]
      rw [hmiddle h (fun _ => (x.val : ℤ))]
      exact congrArg Complex.re hsection
    rw [hreal]
    exact (Complex.abs_re_le_norm _).trans hfrozen
  obtain ⟨U, hU, hUcomplexity, hUempty, _, err, herr, hmean⟩ :=
    exists_cyclic_cellwise_niltest_approximation N (fun _ => Q') qg F A B xi target
      hρ (by positivity) hη hA hB hAsum hBsum hF hFirst hSecond
      (fun _ => hQ.mono Q' (by linarith)) hbudget htarget happrox hdiam
  exact ⟨U, hU, hUcomplexity, hUempty, err, herr, hmean⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RefilteredResidueExpansionSpec
namespace OAI

section

namespace Erdos3

theorem exists_residue_class_lattice_factors {σ G : Type*} [Group G]
    (Γ : Subgroup G) (f : (σ → ℤ) → G) (M : ℕ) (P : G → Prop)
    (hperiod : ∀ x y : σ → ℤ, (∀ j, (M : ℤ) ∣ x j - y j) →
      ((QuotientGroup.mk (f x) : G ⧸ Γ) = QuotientGroup.mk (f y)) ∧
      ((QuotientGroup.mk (f x)⁻¹ : G ⧸ Γ) = QuotientGroup.mk (f y)⁻¹))
    (hrep : ∀ x : σ → ℤ,
      (∃ r : G, P r ∧ ∃ γ ∈ Γ, f x = r * γ) ∧
      (∃ r : G, P r ∧ ∃ γ ∈ Γ, f x = γ * r)) :
    ∃ rR rL : (σ → ZMod M) → G,
      (∀ c, P (rR c) ∧ P (rL c)) ∧
      ∀ x : σ → ℤ,
        (∃ γ ∈ Γ, f x = rR (fun j => (x j : ZMod M)) * γ) ∧
        (∃ γ ∈ Γ, f x = γ * rL (fun j => (x j : ZMod M))) := by
  classical
  let lift : (σ → ZMod M) → σ → ℤ := fun c j => Classical.choose (ZMod.intCast_surjective (c j))
  have hlift (c : σ → ZMod M) (j : σ) : (lift c j : ZMod M) = c j :=
    Classical.choose_spec (ZMod.intCast_surjective (c j))
  choose rR hrR γR hγR heqR using fun c => (hrep (lift c)).1
  choose rL hrL γL hγL heqL using fun c => (hrep (lift c)).2
  refine ⟨rR, rL, fun c => ⟨hrR c, hrL c⟩, ?_⟩
  intro x
  let c := fun j => (x j : ZMod M)
  have hxy (j : σ) : (M : ℤ) ∣ x j - lift c j :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (lift c j) (x j) M).mp (hlift c j)
  have h := hperiod x (lift c) hxy
  have hR : (QuotientGroup.mk (f x) : G ⧸ Γ) = QuotientGroup.mk (rR c) := by
    apply h.1.trans
    rw [heqR c]
    exact QuotientGroup.mk_mul_of_mem _ (hγR c)
  have hL : (QuotientGroup.mk (f x)⁻¹ : G ⧸ Γ) = QuotientGroup.mk (rL c)⁻¹ := by
    apply h.2.trans
    rw [heqL c, mul_inv_rev]
    exact QuotientGroup.mk_mul_of_mem _ (Γ.inv_mem (hγL c))
  constructor
  · refine ⟨(rR c)⁻¹ * f x, QuotientGroup.eq.mp hR.symm, ?_⟩
    change f x = rR c * ((rR c)⁻¹ * f x)
    group
  · have hmem : rL c * (f x)⁻¹ ∈ Γ := by
      simpa only [inv_inv] using QuotientGroup.eq.mp hL.symm
    refine ⟨f x * (rL c)⁻¹, ?_, ?_⟩
    · simpa only [mul_inv_rev, inv_inv] using Γ.inv_mem hmem
    · change f x = (f x * (rL c)⁻¹) * rL c
      group

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

theorem exists_native_residue_representatives (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (w : σ → ℕ),
      (∀ i, 0 < w i) → ∀ (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      (Fintype.card σ : ℝ) ≤ p → ∀ (q : ℕ), 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ M m : ℕ, 0 < M ∧ 0 < m ∧
        (M : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ g : (D.filtration.realification.adaptedPolynomialFiltration w).Group,
          D.filtration.PolynomialRationalGrid D.basis w q g →
          ∃ rR rL : (σ → ZMod M) → D.RealGroup,
            (∀ c, (∀ i, |(D.basis.baseChange ℝ).repr (rR c).coord i| ≤ Real.exp ((p + C) ^ C)) ∧
              (D.basis.baseChange ℝ).equivFun (rR c).coord ∈ realDenominatorGrid m ∧
              (∀ i, |(D.basis.baseChange ℝ).repr (rL c).coord i| ≤ Real.exp ((p + C) ^ C)) ∧
              (D.basis.baseChange ℝ).equivFun (rL c).coord ∈ realDenominatorGrid m) ∧
            ∀ x : σ → ℤ,
              (∃ γ ∈ D.realLattice,
                D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ)) g =
                  rR (fun j => (x j : ZMod M)) * γ) ∧
              (∃ γ ∈ D.realLattice,
                D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ)) g =
                  γ * rL (fun j => (x j : ZMod M))) := by
  obtain ⟨a, _, hperiod⟩ := exists_native_rational_period s
  obtain ⟨b, _, hrep⟩ := exists_native_rational_representatives s
  let P : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a + (Polynomial.X + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ _ d D w hw p hp hD hσ q hq hqp
  obtain ⟨M, hM, hMb, hper⟩ := hperiod D w hw p hp hD hσ q hq hqp
  obtain ⟨m, hm, hmb, hreps⟩ := hrep D p hp hD q hq hqp
  have hsum : (p + a) ^ a + (p + b) ^ b ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hbudget p hp
  have haC : (p + a) ^ a ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (add_nonneg hp (Nat.cast_nonneg b)) _)).trans hsum
  have hbC : (p + b) ^ b ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (pow_nonneg (add_nonneg hp (Nat.cast_nonneg a)) _)).trans hsum
  refine ⟨M, m, hM, hm, hMb.trans (Real.exp_le_exp.mpr haC), hmb.trans (Real.exp_le_exp.mpr hbC), ?_⟩
  intro g hg
  let f := fun x : σ → ℤ => D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ)) g
  let A := fun r : D.RealGroup =>
    (∀ i, |(D.basis.baseChange ℝ).repr r.coord i| ≤ Real.exp ((p + C) ^ C)) ∧
      (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid m
  have hf (x : σ → ℤ) :
      (∃ r : D.RealGroup, A r ∧ ∃ γ ∈ D.realLattice, f x = r * γ) ∧
      (∃ r : D.RealGroup, A r ∧ ∃ γ ∈ D.realLattice, f x = γ * r) := by
    obtain ⟨⟨rR, hR, hRgrid, γR, hγR, heqR⟩, ⟨rL, hL, hLgrid, γL, hγL, heqL⟩⟩ :=
      hreps (f x) (D.filtration.polynomialRationalGrid_value D.basis w q g hg x)
    exact ⟨⟨rR, ⟨fun i => (hR i).trans (Real.exp_le_exp.mpr hbC), hRgrid⟩, γR, hγR, heqR⟩,
      ⟨rL, ⟨fun i => (hL i).trans (Real.exp_le_exp.mpr hbC), hLgrid⟩, γL, hγL, heqL⟩⟩
  obtain ⟨rR, rL, hA, heq⟩ := exists_residue_class_lattice_factors D.realLattice f M A (hper g hg) hf
  exact ⟨rR, rL, fun c => ⟨(hA c).1.1, (hA c).1.2, (hA c).2.1, (hA c).2.2⟩, heq⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {L : ι → Type u}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
  (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
  (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
  (Q : RationalFilteredNilmanifold
    (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  [TopologicalSpace (ℝ ⊗[ℚ] L a)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L a)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L a)] [T2Space (ℝ ⊗[ℚ] L a)]

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSquareRecovery
namespace OAI

section

namespace Erdos3

theorem recover_middle_coset_of_left_class {G : Type*} [Group G] (Γ : Subgroup G)
    (e b r κ t z γ : G) (hfactor : e * b * r * κ = t)
    (hγ : γ ∈ Γ) (hr : r = γ * z) :
    (QuotientGroup.mk b : G ⧸ Γ) = QuotientGroup.mk (e⁻¹ * t * κ⁻¹ * z⁻¹) := by
  have heq : e⁻¹ * t * κ⁻¹ * z⁻¹ = b * γ := by
    rw [← hfactor, hr]
    group
  rw [heq]
  exact (QuotientGroup.mk_mul_of_mem b hγ).symm

theorem recover_mapped_middle_coset_of_left_class {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (Λ : Subgroup H) (e b r κ t : G) (z γ : H)
    (hfactor : e * b * r * κ = t) (hγ : γ ∈ Λ) (hr : φ r = γ * z) :
    (QuotientGroup.mk (φ b) : H ⧸ Λ) =
      QuotientGroup.mk ((φ e)⁻¹ * φ t * (φ κ)⁻¹ * z⁻¹) := by
  apply recover_middle_coset_of_left_class Λ (φ e) (φ b) (φ r) (φ κ) (φ t) z γ _ hγ hr
  simpa only [map_mul] using congrArg φ hfactor

end Erdos3

end

section

namespace Erdos3

open Module

namespace RationalFilteredNilmanifold

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_uniform_normalized_recovery (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      {d e : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (φ : L →ₗ⁅ℚ⁆ M) {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ Λ : Subgroup D.filtration.Group, Λ ≤ D.lattice ∧
        (Λ.subgroupOf D.lattice).Characteristic ∧ (Λ.subgroupOf D.lattice).Normal ∧
        (Λ.subgroupOf D.lattice).FiniteIndex ∧ (Λ.relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (N : ℕ) (hN : 0 < N)
          (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
          (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N),
          let Q := D.withLattice Λ N hN hin hout
          Q.GeometryComplexityLE ((p + C) ^ C) ∧
          letI := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot)
            (E.basis.baseChange ℝ)
          letI := Q.metricSpace
          letI := E.metricSpace
          let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := E.filtration.lowerCentralSeries_eq_bot) φ
          ∀ κ : D.RealGroup, κ ∈ D.realLattice → ∀ r : E.RealGroup,
            (E.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q →
            ∀ a b : E.RealGroup,
              (∀ i, |(E.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((p + 2) ^ k)) →
              ∀ x y : D.RealGroup,
                dist (QuotientGroup.mk (a * ψ x * (ψ κ⁻¹ * r)) : E.Space)
                    (QuotientGroup.mk (b * ψ y * (ψ κ⁻¹ * r))) ≤
                  Real.exp ((p + C) ^ C) * dist (QuotientGroup.mk x : Q.Space) (QuotientGroup.mk y) +
                    dist a b := by
  obtain ⟨c₀, _, hcover⟩ := exists_uniform_conjugated_source_cover s
  obtain ⟨c₁, _, hleft⟩ := exists_uniform_left_lipschitz_exp_bound s k
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C c₀) ^ c₀ + (X + 1 + Polynomial.C c₁) ^ c₁ + (X + 1 + 2) ^ 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ _ _ _ _ _ _ _ _ d e D E φ p hp hD hE hφ q hq hqp
  obtain ⟨Λ, htarget, hΛ, hchar, hnormal, hfinite, hindex, N, hN, hin, hout, hQ⟩ :=
    hcover D E φ p hp hD hE hφ q hq hqp
  let Q := D.withLattice Λ N hN hin hout
  let t := p + 1
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hpt : p ≤ t := by dsimp [t]; linarith
  have hsum : (p + c₀) ^ c₀ + (t + c₁) ^ c₁ + (t + 2) ^ 2 ≤ (p + C) ^ C := by
    simpa [P, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have hcoverC : (p + c₀) ^ c₀ ≤ (p + C) ^ C := by
    nlinarith [pow_nonneg (show 0 ≤ t + c₁ by positivity) c₁, sq_nonneg (t + 2)]
  have hmetricC : (t + c₁) ^ c₁ + (t + 2) ^ 2 ≤ (p + C) ^ C := by
    nlinarith [pow_nonneg (show 0 ≤ p + c₀ by positivity) c₀]
  let H := ⌈Real.exp p⌉₊
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
  obtain ⟨A, _, hA, hALip⟩ := hleft (E.basis.baseChange ℝ) (lieStructureConstants E.basis) H t
    E.filtration.realification.lowerCentralSeries_eq_bot
    (fun i j k => (realLieBasis_structure E.basis i j k).symm) ht
    (by simpa only [Fintype.card_fin] using hE.1.trans hpt) (ceil_exp_le_exp_add_one hp)
    (fun i j k => rationalHeightLE_ceil_exp (hE.2.2.1 i j k))
  obtain ⟨B, _, hB, hBLip⟩ := exists_realificationMap_lipschitz_exp_bound
    (hnil := D.filtration.lowerCentralSeries_eq_bot) (hM := E.filtration.lowerCentralSeries_eq_bot)
    D.basis E.basis φ H ht
    (by simpa only [Fintype.card_fin] using hD.1.trans hpt)
    (by simpa only [Fintype.card_fin] using hE.1.trans hpt) (ceil_exp_le_exp_add_one hp)
    (fun i j => rationalHeightLE_ceil_exp (hφ i j))
  have hAB : ((A * B : ℝ≥0) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    calc
      _ ≤ Real.exp ((t + c₁) ^ c₁) * Real.exp ((t + 2) ^ 2) := by push_cast; gcongr
      _ = Real.exp ((t + c₁) ^ c₁ + (t + 2) ^ 2) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hmetricC
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr hcoverC),
    N, hN, hin, hout, hQ.mono Q hcoverC, ?_⟩
  let := Q.metricSpace
  let := E.metricSpace
  dsimp only
  intro κ hκ r hr a b ha x y
  have ha' : LipschitzWith A (fun z => a * z) := hALip a (fun i =>
    (ha i).trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith) (by dsimp [t]; linarith) k)))
  have hcompat := D.normalized_right_compatibility E φ q hq Λ htarget hΛ hnormal κ hκ r hr
  have hdist := native_frozenCosetMap_dist_le Q E φ _ a b hcompat hBLip ha' x y
  exact hdist.trans (add_le_add (mul_le_mul_of_nonneg_right hAB dist_nonneg) le_rfl)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_uniform_left_class_recovery (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      {d e : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (φ : L →ₗ⁅ℚ⁆ M) {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ Λ : Subgroup D.filtration.Group, Λ ≤ D.lattice ∧
        (Λ.subgroupOf D.lattice).Characteristic ∧ (Λ.subgroupOf D.lattice).Normal ∧
        (Λ.subgroupOf D.lattice).FiniteIndex ∧ (Λ.relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (N : ℕ) (hN : 0 < N)
          (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
          (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N),
          let Q := D.withLattice Λ N hN hin hout
          Q.GeometryComplexityLE ((p + C) ^ C) ∧
          letI := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot)
            (E.basis.baseChange ℝ)
          letI := Q.metricSpace
          letI := E.metricSpace
          let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := E.filtration.lowerCentralSeries_eq_bot) φ
          ∀ κ : D.RealGroup, κ ∈ D.realLattice → ∀ z : E.RealGroup,
            (E.basis.baseChange ℝ).equivFun z.coord ∈ realDenominatorGrid q →
            ∀ a a' b b' r r' x x' : D.RealGroup,
              a * b * r * κ = x → a' * b' * r' * κ = x' →
              (∃ γ ∈ E.realLattice, ψ r = γ * z) → (∃ γ ∈ E.realLattice, ψ r' = γ * z) →
              (∀ i, |(E.basis.baseChange ℝ).repr ((ψ a)⁻¹).coord i| ≤ Real.exp ((p + 2) ^ k)) →
              dist (QuotientGroup.mk (ψ b) : E.Space) (QuotientGroup.mk (ψ b')) ≤
                Real.exp ((p + C) ^ C) * dist (QuotientGroup.mk x : Q.Space) (QuotientGroup.mk x') +
                  dist (ψ a)⁻¹ (ψ a')⁻¹ := by
  obtain ⟨C, hC, hrecovery⟩ := exists_uniform_normalized_recovery s k
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ _ _ _ _ _ _ _ _ d e D E φ p hp hD hE hφ q hq hqp
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, N, hN, hin, hout, hQ, hmetric⟩ :=
    hrecovery D E φ hp hD hE hφ q hq hqp
  let Q := D.withLattice Λ N hN hin hout
  let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
    (hM := E.filtration.lowerCentralSeries_eq_bot) φ
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, N, hN, hin, hout, hQ, ?_⟩
  let := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
  let := Q.metricSpace
  let := E.metricSpace
  dsimp only
  intro κ hκ z hz a a' b b' r r' x x' hfactor hfactor' hr hr' ha
  obtain ⟨γ, hγ, hr⟩ := hr
  obtain ⟨γ', hγ', hr'⟩ := hr'
  have hrecover := recover_mapped_middle_coset_of_left_class ψ E.realLattice a b r κ x z γ hfactor hγ hr
  have hrecover' := recover_mapped_middle_coset_of_left_class ψ E.realLattice a' b' r' κ x' z γ' hfactor' hγ' hr'
  have hzinv : (E.basis.baseChange ℝ).equivFun (z⁻¹).coord ∈ realDenominatorGrid q := by
    simpa only [coord_inv, map_neg] using realDenominatorGrid_neg q hz
  rw [hrecover, hrecover']
  simpa only [map_inv, mul_assoc] using hmetric κ hκ z⁻¹ hzinv (ψ a)⁻¹ (ψ a')⁻¹ ha x x'

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CyclicCellAnchors
namespace OAI

section

namespace Erdos3

theorem exists_cyclic_cell_anchors {I : Type*} (N : ℕ) [NeZero N]
    (A : I → ZMod N → ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hcircle : ∀ i x y, 0 < A i x → 0 < A i y →
      dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ) :
    ∃ anchor : I → ZMod N → ℝ,
      (∀ i h, |anchor i h| ≤ N) ∧
      ∀ i h x, x ∉ cyclicWrapExceptional h ρ → 0 < A i x →
        |(x.val : ℝ) - anchor i h| ≤ (N : ℝ) * ρ := by
  classical
  let pick (i : I) (h : ZMod N) : ZMod N :=
    if hx : ∃ x, x ∉ cyclicWrapExceptional h ρ ∧ 0 < A i x then hx.choose else 0
  have hpick (i : I) (h : ZMod N)
      (hx : ∃ x, x ∉ cyclicWrapExceptional h ρ ∧ 0 < A i x) :
      pick i h ∉ cyclicWrapExceptional h ρ ∧ 0 < A i (pick i h) := by
    simpa only [pick, dif_pos hx] using hx.choose_spec
  refine ⟨fun i h => ((pick i h).val : ℝ), ?_, ?_⟩
  · intro i h
    change |((pick i h).val : ℝ)| ≤ (N : ℝ)
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast (Nat.le_of_lt (ZMod.val_lt (pick i h)))
  · intro i h x hx hAx
    obtain ⟨hy, hAy⟩ := hpick i h ⟨x, hx, hAx⟩
    have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
    have hd := good_circle_observations_control_representatives h x (pick i h) hρ hx hy
      (hcircle i x (pick i h) hAx hAy)
    rw [← sub_div, abs_div, abs_of_pos hN] at hd
    simpa only [mul_comm ρ (N : ℝ)] using (div_le_iff₀ hN).mp hd

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SlowInverseControl
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_slow_inverse_control (s r : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (w : σ → ℕ),
      (∀ i, 0 < w i) → ∀ (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      (Fintype.card σ : ℝ) ≤ p → ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
      ∀ g : (D.filtration.realification.adaptedPolynomialFiltration w).Group,
        D.filtration.PolynomialSlowBound D.basis w T (Real.exp ((p + 2) ^ r)) g →
        (∀ (v : σ → ℝ), (∀ i, |v i| ≤ T i) → ∀ i,
          |(D.basis.baseChange ℝ).repr (D.filtration.adaptedPolynomialRealValueHom w v g)⁻¹.coord i| ≤
            Real.exp ((p + 2) ^ C)) ∧
        (∀ (v z : σ → ℝ) (δ : ℝ), 0 ≤ δ →
          (∀ i, |v i| ≤ T i) → (∀ i, |z i| ≤ T i) →
          (∀ i, |v i - z i| ≤ T i * δ) →
          letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
            (D.basis.baseChange ℝ)
          dist (D.filtration.adaptedPolynomialRealValueHom w v g)⁻¹
            (D.filtration.adaptedPolynomialRealValueHom w z g)⁻¹ ≤
              Real.exp ((p + 2) ^ C) * δ) := by
  obtain ⟨A, _, hmetric⟩ := exists_polynomialSlowBound_dist_exp s r
  let X : Polynomial ℕ := Polynomial.X
  let P := Polynomial.C s * (X + 1) + (X + 2) ^ r + (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget P
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ _ d D w hw p hp hD hσ T hT g hg
  have hinv := (D.filtration.polynomialSlowBound_inv_iff D.basis w T _ g).mpr hg
  have hsum : (s : ℝ) * (p + 1) + (p + 2) ^ r + (p + A) ^ A ≤ (p + 2) ^ C := by
    simpa [P, X, Polynomial.eval₂_pow] using hbudget p hp
  have hcoord : (s : ℝ) * (p + 1) + (p + 2) ^ r ≤ (p + 2) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (by positivity) _)).trans hsum
  have hdist : (p + A) ^ A ≤ (p + 2) ^ C :=
    (le_add_of_nonneg_left (by positivity)).trans hsum
  constructor
  · intro v hv i
    have hvbound := D.filtration.polynomialSlowBound_value D.basis w hw T hT
      (Real.exp_pos _).le g⁻¹ hinv v hv i
    rw [map_inv] at hvbound
    apply hvbound.trans
    have hn1 : (Fintype.card σ : ℝ) + 1 ≤ Real.exp p := by
      linarith [Real.add_one_le_exp p]
    calc
      _ ≤ Real.exp s * (Real.exp p) ^ s * Real.exp ((p + 2) ^ r) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul (Real.add_one_le_exp (s : ℝ))
            (pow_le_pow_left₀ (by positivity) hn1 _) (by positivity) (Real.exp_pos _).le)
          (Real.exp_pos _).le
      _ = Real.exp ((s : ℝ) * (p + 1) + (p + 2) ^ r) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr hcoord
  · intro v z δ hδ hv hz hvz
    have hm := hmetric D w hw p hp hD hσ T hT g⁻¹ hinv v z δ hδ hv hz hvz
    simp only [map_inv] at hm
    exact hm.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hdist) hδ)

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ControlledRefilteredResidueExpansion
namespace OAI

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

theorem exists_controlled_refiltered_residue_expansion (s r : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
      {L : ι → Type u} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {κ : Type*} [Fintype κ] {d : ι → ℕ}
      (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
      (w : ∀ i, Fin (d i) → ℕ)
      (hF : ∀ i j, (D i).filtration.layer j =
        Submodule.span ℚ ((D i).basis '' {b | j ≤ w i b}))
      (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded)
      (v₀ : κ → (pi D).filtration.AssociatedGraded)
      (_hspan : Submodule.span ℚ (Set.range v₀) = W.toSubmodule) {p : ℝ},
      1 ≤ p → (Fintype.card ι : ℝ) ≤ p → (∀ i, (D i).GeometryComplexityLE p) →
      (Fintype.card κ : ℝ) ≤ p →
      (∀ i b, rationalLogHeight (((pi D).filtration.associatedGradedBasis (pi D).basis
        (productBasisWeight w) (pi_layer_span D w hF)).repr (v₀ i) b) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W)
            (s + 1) (finrank ℚ ((pi D).filtration.gradedRefiltrationSubalgebra W)),
          E.filtration = (pi D).filtration.gradedRefiltration W ∧
          E.lattice = (pi D).lattice.comap
            (NilpotentLieBCHGroup.map
              (hnil := ((pi D).filtration.gradedRefiltration W).lowerCentralSeries_eq_bot)
              ((pi D).filtration.gradedRefiltrationSubalgebra W).incl) ∧
          E.GeometryComplexityLE ((p + C) ^ C) ∧
          ∃ n : ℕ, n ≤ finrank ℚ ((pi D).filtration.gradedRefiltrationSubalgebra W) ∧
            ∃ Q : RationalFilteredNilmanifold
                (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n,
              Q.filtration = E.filtration.quotientTop ∧
              Q.lattice = E.lattice.map
                (E.filtration.quotientStepHom (E.filtration.layerIdeal (s + 1)) le_rfl) ∧
              Q.GeometryComplexityLE ((p + C) ^ C) ∧
              (nativeRefilteredTarget D a W E Q).GeometryComplexityLE ((p + C) ^ C) ∧
              RefilteredResidueExpansionSpec D a W E Q p q r P ((p + C) ^ C) := by
  obtain ⟨k₀, _, hslowValues⟩ := exists_slow_inverse_control (s + 1) r
  let k := max r k₀
  obtain ⟨a₀, _, hreps⟩ := exists_native_residue_representatives (s + 1)
  obtain ⟨b₀, _, hmodels⟩ := exists_controlled_lower_refiltered_reconstruction s k
  obtain ⟨c₀, _, hexpand⟩ := exists_lower_refiltered_cyclic_expansion s k
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C a₀) ^ a₀
  let B := (T + Polynomial.C b₀) ^ b₀
  let F := (T + Polynomial.C c₀) ^ c₀
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + B + F)
  refine ⟨C, hC, ?_⟩
  intro ι _ _ L _ _ _ _ _ _ κ _ d D a w hF W v₀ hspan p hp hι hD hκ hv q hq hqp
  classical
  let w₁ := fun _ : Unit => 1
  have hp₀ : 0 ≤ p := by linarith
  obtain ⟨P, m, hP, hm, hPb, hmb, hperiod⟩ :=
    hreps (D a) w₁ (fun _ => by decide) p hp₀ (hD a)
      (by simpa only [Fintype.card_unit, Nat.cast_one] using hp) q hq hqp
  let t := p + (p + a₀) ^ a₀
  let cost := (p + C) ^ C
  have hpt : p ≤ t := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have ht : 0 ≤ t := hp₀.trans hpt
  have hat : (p + a₀) ^ a₀ ≤ t := le_add_of_nonneg_left hp₀
  have hsum : t + (t + b₀) ^ b₀ + (t + c₀) ^ c₀ ≤ cost := by
    simpa [T, B, F, X, t, cost, Polynomial.eval₂_pow] using hbudget p hp₀
  have hb₀ : 0 ≤ (t + b₀) ^ b₀ := pow_nonneg (by positivity) _
  have hc₀ : 0 ≤ (t + c₀) ^ c₀ := pow_nonneg (by positivity) _
  have htCost : t ≤ cost := by linarith
  have hmodelCost : (t + b₀) ^ b₀ ≤ cost := by linarith
  have hfreezeCost : (t + c₀) ^ c₀ ≤ cost := by linarith
  have hcost : 0 ≤ cost := ht.trans htCost
  obtain ⟨E, hEF, hEL, hE, n, hn, Q, hQF, hQL, hQ, htarget, hrec⟩ :=
    hmodels D a w hF W v₀ hspan ht (hι.trans hpt) (fun i => (hD i).mono (D i) hpt)
      (hκ.trans hpt) (fun i b => (hv i b).trans hpt) m hm
      (hmb.trans (Real.exp_le_exp.mpr hat))
  have hbase := hexpand D a W E Q (hp.trans hpt) hcost hQF
    (LowerRefilteredRecoveryFamily.mono_cost D a W E Q hrec hmodelCost)
  refine ⟨P, hP, hPb.trans (Real.exp_le_exp.mpr (hat.trans htCost)), E, hEF, hEL,
    hE.mono E hmodelCost, n, hn, Q, hQF, hQL, hQ.mono Q hmodelCost,
    htarget.mono _ hmodelCost, ?_⟩
  let H := (pi D).filtration.gradedRefiltrationSubalgebra W
  let I₀ := {i : ι // i ≠ a}
  let Z₀ := pi (fun i : I₀ => D i.val)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  let := realification_moduleTopology_t2 Q.basis
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i : I₀, L i.val))
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i : I₀, L i.val))
  let := realification_moduleTopology_t2 Z₀.basis
  obtain ⟨Q', hQ'F, hQ'b, hQ'le, hQ', Z, hZF, hZb, hZle, hZ, hbase⟩ := hbase
  refine ⟨Q', hQ'F, hQ'b, hQ'le, hQ', Z, hZF, hZb, hZle, hZ, ?_⟩
  let := Z.metricSpace
  dsimp only
  intro J₀ freq hfreq N _ I J _ _ A₁ B₁ label ρ η hρ hη hA hB hAsum hBsum hres hcircle
    S hS hpositive hinvariant slow middle rat κ₁ g hκ₁ hfactor hslow hrat hmiddle hdiam
  obtain ⟨anchor, hanchor, hnear⟩ := exists_cyclic_cell_anchors N A₁ hρ hcircle
  choose right left hright hvalue using fun h => hperiod (rat h) (hrat h)
  let r₀ := fun i h => right h (fun _ => label i)
  have hrightGrid (i : I) (h : ZMod N) :
      ((D a).basis.baseChange ℝ).equivFun (r₀ i h).coord ∈ realDenominatorGrid m :=
    (hright h _).2.1
  have hclass (i : I) (h x : ZMod N) (_hx : x ∉ cyclicWrapExceptional h ρ) (hAx : 0 < A₁ i x) :
      (QuotientGroup.mk ((D a).filtration.adaptedPolynomialRealValueHom w₁
        (fun _ => (x.val : ℝ)) (rat h)) : (D a).Space) = QuotientGroup.mk (r₀ i h) := by
    obtain ⟨γ, hγ, heq⟩ := (hvalue h (fun _ => (x.val : ℤ))).1
    have hclass' :
        (QuotientGroup.mk ((D a).filtration.adaptedPolynomialRealValueHom w₁
          (fun _ => ((x.val : ℤ) : ℝ)) (rat h)) : (D a).Space) =
          QuotientGroup.mk (right h (fun _ => ((x.val : ℤ) : ZMod P))) := by
      rw [heq]
      exact QuotientGroup.mk_mul_of_mem _ hγ
    simpa only [Int.cast_natCast, r₀, hres i x hAx] using hclass'
  have hpower {j : ℕ} (hj : j ≤ k) : (p + 2) ^ j ≤ (t + 2) ^ k :=
    (pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ p + 2)
      (by linarith : p + 2 ≤ t + 2) j).trans
        (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ t + 2) hj)
  have hslow' (h : ZMod N) : (D a).filtration.PolynomialSlowBound (D a).basis w₁
      (fun _ => (N : ℝ)) (Real.exp ((t + 2) ^ k)) (slow h) :=
    (D a).filtration.polynomialSlowBound_mono (D a).basis w₁
      (fun _ => (N : ℝ)) (fun _ => Nat.cast_pos.mpr (NeZero.pos N))
      (Real.exp_le_exp.mpr (hpower (le_max_left _ _))) (slow h) (hslow h)
  have hleft (i : I) (h : ZMod N) (b : Fin (d a)) :
      |((D a).basis.baseChange ℝ).repr
        ((D a).filtration.adaptedPolynomialRealValueHom w₁ (fun _ => anchor i h) (slow h)).coord b| ≤
          Real.exp ((t + 2) ^ k) := by
    have hinv := ((D a).filtration.polynomialSlowBound_inv_iff (D a).basis w₁
      (fun _ => (N : ℝ)) (Real.exp ((p + 2) ^ r)) (slow h)).mpr (hslow h)
    have hval := (hslowValues (D a) w₁ (fun _ => by decide) p hp₀ (hD a)
      (by simpa only [Fintype.card_unit, Nat.cast_one] using hp)
      (fun _ => (N : ℝ)) (fun _ => Nat.cast_pos.mpr (NeZero.pos N)) (slow h)⁻¹ hinv).1
        (fun _ => anchor i h) (fun _ => hanchor i h) b
    have hval' :
        |((D a).basis.baseChange ℝ).repr
          ((D a).filtration.adaptedPolynomialRealValueHom w₁ (fun _ => anchor i h) (slow h)).coord b| ≤
            Real.exp ((p + 2) ^ k₀) := by
      simpa only [map_inv, inv_inv] using hval
    exact hval'.trans (Real.exp_le_exp.mpr (hpower (le_max_right _ _)))
  obtain ⟨U, hU, hUcomplexity, hUempty, err, herr, hmean⟩ :=
    hbase freq hfreq N A₁ B₁ hρ hη hA hB hAsum hBsum S
      (fun h => (hS h).mono hpt) hpositive hinvariant slow middle rat κ₁ g
      hκ₁ hfactor hslow' hmiddle anchor r₀ hanchor hleft hrightGrid hnear hclass hdiam
  refine ⟨U, hU, hUcomplexity, hUempty, err, herr, ?_⟩
  intro h
  calc
    _ ≤ Real.exp ((t + c₀) ^ c₀) * ρ + Real.exp cost * η + 6 * ρ + 3 / N := hmean h
    _ ≤ Real.exp cost * (ρ + η) + 6 * ρ + 3 / N := by
      have hb := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hfreezeCost) hρ.le
      nlinarith

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SlowResidueRecovery
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_uniform_residue_recovery (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L M : Type*} [Fintype σ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)] {d e : ℕ}
      (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (φ : L →ₗ⁅ℚ⁆ M) (w : σ → ℕ), (∀ i, 0 < w i) → ∀ {p : ℝ},
      0 ≤ p → (Fintype.card σ : ℝ) ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ P m : ℕ, 0 < P ∧ 0 < m ∧
        (P : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ Λ : Subgroup D.filtration.Group, Λ ≤ D.lattice ∧
          (Λ.subgroupOf D.lattice).Characteristic ∧ (Λ.subgroupOf D.lattice).Normal ∧
          (Λ.subgroupOf D.lattice).FiniteIndex ∧ (Λ.relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ∃ (N : ℕ) (hN : 0 < N)
            (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
            (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N),
            let Q := D.withLattice Λ N hN hin hout
            Q.GeometryComplexityLE ((p + C) ^ C) ∧
            letI := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot)
              (E.basis.baseChange ℝ)
            letI := Q.metricSpace
            letI := E.metricSpace
            let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
              (hM := E.filtration.lowerCentralSeries_eq_bot) φ
            ∀ R : (E.filtration.realification.adaptedPolynomialFiltration w).Group,
              E.filtration.PolynomialRationalGrid E.basis w q R →
              ∃ z : (σ → ZMod P) → E.RealGroup,
                (∀ c, (∀ i, |(E.basis.baseChange ℝ).repr (z c).coord i| ≤ Real.exp ((p + C) ^ C)) ∧
                  (E.basis.baseChange ℝ).equivFun (z c).coord ∈ realDenominatorGrid m) ∧
                ∀ κ : D.RealGroup, κ ∈ D.realLattice →
                  ∀ a b r f : (σ → ℤ) → D.RealGroup,
                    (∀ x, a x * b x * r x * κ = f x) →
                    (∀ x, ψ (r x) = E.filtration.adaptedPolynomialRealValueHom w
                      (fun i => (x i : ℝ)) R) →
                    (∀ x, (QuotientGroup.mk (ψ (b x)) : E.Space) =
                      QuotientGroup.mk ((ψ (a x))⁻¹ * ψ (f x) * (ψ κ)⁻¹ *
                        (z (fun i => (x i : ZMod P)))⁻¹)) ∧
                    ∀ x y, (fun i => (x i : ZMod P)) = (fun i => (y i : ZMod P)) →
                      (∀ i, |(E.basis.baseChange ℝ).repr ((ψ (a x))⁻¹).coord i| ≤
                        Real.exp ((p + 2) ^ k)) →
                      dist (QuotientGroup.mk (ψ (b x)) : E.Space) (QuotientGroup.mk (ψ (b y))) ≤
                        Real.exp ((p + C) ^ C) * dist (QuotientGroup.mk (f x) : Q.Space)
                          (QuotientGroup.mk (f y)) + dist (ψ (a x))⁻¹ (ψ (a y))⁻¹ := by
  obtain ⟨A, _, hresidue⟩ := exists_native_residue_representatives s
  obtain ⟨B, _, hrecovery⟩ := exists_uniform_left_class_recovery s k
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C A) ^ A
  let U := T + (T + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget U
  refine ⟨C, hC, ?_⟩
  intro σ L M _ _ _ _ _ _ _ _ _ _ _ _ _ d e D E φ w hw p hp hσ hD hE hφ q hq hqp
  obtain ⟨P, m, hP, hm, hPb, hmb, hrepresentatives⟩ := hresidue E w hw p hp hE hσ q hq hqp
  let t := p + (p + A) ^ A
  have hpt : p ≤ t := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have ht : 0 ≤ t := hp.trans hpt
  have hAt : (p + A) ^ A ≤ t := le_add_of_nonneg_left hp
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, N, hN, hin, hout, hQ, hmetric⟩ :=
    hrecovery D E φ ht (hD.mono D hpt) (hE.mono E hpt) (fun i j => (hφ i j).trans hpt)
      m hm (hmb.trans (Real.exp_le_exp.mpr hAt))
  let Q := D.withLattice Λ N hN hin hout
  let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
    (hM := E.filtration.lowerCentralSeries_eq_bot) φ
  have hsum : t + (t + B) ^ B ≤ (p + C) ^ C := by
    simpa [U, T, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have htC : t ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (by positivity) _)).trans hsum
  have hcost : (t + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left ht).trans hsum
  refine ⟨P, m, hP, hm, hPb.trans (Real.exp_le_exp.mpr (hAt.trans htC)),
    hmb.trans (Real.exp_le_exp.mpr (hAt.trans htC)), Λ, hΛ, hchar, hnormal, hfinite,
    hindex.trans (Real.exp_le_exp.mpr hcost), N, hN, hin, hout, hQ.mono Q hcost, ?_⟩
  let := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
  let := Q.metricSpace
  let := E.metricSpace
  dsimp only
  intro R hR
  obtain ⟨_, z, hz, hclasses⟩ := hrepresentatives R hR
  refine ⟨z, fun c => ⟨fun i => ((hz c).2.2.1 i).trans
    (Real.exp_le_exp.mpr (hAt.trans htC)), (hz c).2.2.2⟩, ?_⟩
  intro κ hκ a b r f hfactor hvalue
  have hleft (x : σ → ℤ) : ∃ γ ∈ E.realLattice, ψ (r x) = γ * z (fun i => (x i : ZMod P)) := by
    obtain ⟨γ, hγ, heq⟩ := (hclasses x).2
    exact ⟨γ, hγ, (hvalue x).trans heq⟩
  refine ⟨?_, ?_⟩
  · intro x
    obtain ⟨γ, hγ, heq⟩ := hleft x
    exact recover_mapped_middle_coset_of_left_class ψ E.realLattice
      (a x) (b x) (r x) κ (f x) _ γ (hfactor x) hγ heq
  · intro x y hxy ha
    have hy : ∃ γ ∈ E.realLattice, ψ (r y) = γ * z (fun i => (x i : ZMod P)) := by
      rw [hxy]
      exact hleft y
    have ha' : ∀ i, |(E.basis.baseChange ℝ).repr ((ψ (a x))⁻¹).coord i| ≤ Real.exp ((t + 2) ^ k) :=
      fun i => (ha i).trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith) (by linarith) k))
    have hdist := hmetric κ hκ (z (fun i => (x i : ZMod P))) ((hz _).2.2.2)
      (a x) (a y) (b x) (b y) (r x) (r y) (f x) (f y) (hfactor x) (hfactor y) (hleft x) hy ha'
    exact hdist.trans (add_le_add
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hcost) dist_nonneg) le_rfl)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_slow_residue_recovery (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L M : Type*} [Fintype σ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)] {d e : ℕ}
      (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (φ : L →ₗ⁅ℚ⁆ M) (w : σ → ℕ), (∀ i, 0 < w i) → ∀ {p : ℝ},
      0 ≤ p → (Fintype.card σ : ℝ) ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ P m : ℕ, 0 < P ∧ 0 < m ∧
        (P : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ Λ : Subgroup D.filtration.Group, Λ ≤ D.lattice ∧
          (Λ.subgroupOf D.lattice).Characteristic ∧ (Λ.subgroupOf D.lattice).Normal ∧
          (Λ.subgroupOf D.lattice).FiniteIndex ∧ (Λ.relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ∃ (N : ℕ) (hN : 0 < N)
            (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
            (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N),
            let Q := D.withLattice Λ N hN hin hout
            Q.GeometryComplexityLE ((p + C) ^ C) ∧
            letI := Q.metricSpace
            letI := E.metricSpace
            let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
              (hM := E.filtration.lowerCentralSeries_eq_bot) φ
            ∀ R : (E.filtration.realification.adaptedPolynomialFiltration w).Group,
              E.filtration.PolynomialRationalGrid E.basis w q R →
              ∃ z : (σ → ZMod P) → E.RealGroup,
                (∀ c, (∀ i, |(E.basis.baseChange ℝ).repr (z c).coord i| ≤ Real.exp ((p + C) ^ C)) ∧
                  (E.basis.baseChange ℝ).equivFun (z c).coord ∈ realDenominatorGrid m) ∧
                ∀ κ : D.RealGroup, κ ∈ D.realLattice →
                  ∀ a b r f : (σ → ℤ) → D.RealGroup,
                    (∀ x, a x * b x * r x * κ = f x) →
                    (∀ x, ψ (r x) = E.filtration.adaptedPolynomialRealValueHom w
                      (fun i => (x i : ℝ)) R) →
                    (∀ x, (QuotientGroup.mk (ψ (b x)) : E.Space) =
                      QuotientGroup.mk ((ψ (a x))⁻¹ * ψ (f x) * (ψ κ)⁻¹ *
                        (z (fun i => (x i : ZMod P)))⁻¹)) ∧
                    ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
                      ∀ S : (E.filtration.realification.adaptedPolynomialFiltration w).Group,
                        E.filtration.PolynomialSlowBound E.basis w T (Real.exp ((p + 2) ^ k)) S →
                        (∀ x, ψ (a x) = E.filtration.adaptedPolynomialRealValueHom w
                          (fun i => (x i : ℝ)) S) →
                        ∀ x y, (fun i => (x i : ZMod P)) = (fun i => (y i : ZMod P)) →
                          ∀ δ : ℝ, 0 ≤ δ →
                            (∀ i, |(x i : ℝ)| ≤ T i) → (∀ i, |(y i : ℝ)| ≤ T i) →
                            (∀ i, |(x i : ℝ) - (y i : ℝ)| ≤ T i * δ) →
                            dist (QuotientGroup.mk (ψ (b x)) : E.Space) (QuotientGroup.mk (ψ (b y))) ≤
                              Real.exp ((p + C) ^ C) *
                                (dist (QuotientGroup.mk (f x) : Q.Space) (QuotientGroup.mk (f y)) + δ) := by
  obtain ⟨A, _, hslow⟩ := exists_slow_inverse_control s k
  obtain ⟨B, _, hresidue⟩ := exists_uniform_residue_recovery s A
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C B) ^ B + (X + 2) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget U
  refine ⟨C, hC, ?_⟩
  intro σ L M _ _ _ _ _ _ _ _ _ _ _ _ _ d e D E φ w hw p hp hσ hD hE hφ q hq hqp
  obtain ⟨P, m, hP, hm, hPb, hmb, Λ, hΛ, hchar, hnormal, hfinite, hindex,
    N, hN, hin, hout, hQ, hrecover⟩ := hresidue D E φ w hw hp hσ hD hE hφ q hq hqp
  let Q := D.withLattice Λ N hN hin hout
  let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
    (hM := E.filtration.lowerCentralSeries_eq_bot) φ
  have hsum : (p + B) ^ B + (p + 2) ^ A ≤ (p + C) ^ C := by
    simpa [U, X, Polynomial.eval₂_pow] using hbudget p hp
  have hBC : (p + B) ^ B ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (by positivity) _)).trans hsum
  have hAC : (p + 2) ^ A ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (pow_nonneg (by positivity) _)).trans hsum
  refine ⟨P, m, hP, hm, hPb.trans (Real.exp_le_exp.mpr hBC), hmb.trans (Real.exp_le_exp.mpr hBC),
    Λ, hΛ, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr hBC),
    N, hN, hin, hout, hQ.mono Q hBC, ?_⟩
  let := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
  let := Q.metricSpace
  let := E.metricSpace
  dsimp only
  intro R hR
  obtain ⟨z, hz, heval⟩ := hrecover R hR
  refine ⟨z, fun c => ⟨fun i => ((hz c).1 i).trans (Real.exp_le_exp.mpr hBC), (hz c).2⟩, ?_⟩
  intro κ hκ a b r f hfactor hvalue
  obtain ⟨hexact, hmove⟩ := heval κ hκ a b r f hfactor hvalue
  refine ⟨hexact, ?_⟩
  intro T hT S hS hslowvalue x y hxy δ hδ hx hy hdelta
  obtain ⟨hcoords, hdist⟩ := hslow E w hw p hp hE hσ T hT S hS
  have hleft : ∀ i, |(E.basis.baseChange ℝ).repr ((ψ (a x))⁻¹).coord i| ≤ Real.exp ((p + 2) ^ A) := by
    rw [hslowvalue x]
    exact hcoords (fun i => (x i : ℝ)) hx
  have hinverse : dist (ψ (a x))⁻¹ (ψ (a y))⁻¹ ≤ Real.exp ((p + 2) ^ A) * δ := by
    rw [hslowvalue x, hslowvalue y]
    exact hdist _ _ δ hδ hx hy hdelta
  apply (hmove x y hxy hleft).trans
  calc
    _ ≤ Real.exp ((p + B) ^ B) *
        dist (QuotientGroup.mk (f x) : Q.Space) (QuotientGroup.mk (f y)) +
          Real.exp ((p + 2) ^ A) * δ := add_le_add le_rfl hinverse
    _ ≤ Real.exp ((p + C) ^ C) *
        dist (QuotientGroup.mk (f x) : Q.Space) (QuotientGroup.mk (f y)) +
          Real.exp ((p + C) ^ C) * δ :=
      add_le_add (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hBC) dist_nonneg)
        (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hAC) hδ)
    _ = _ := (mul_add _ _ _).symm

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledRefilteredRecoveredExpansion
namespace OAI

section

namespace Erdos3

theorem positive_cell_residue_recovery
    {I J X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {P N : ℕ} [NeZero N] (A : I → ZMod N → ℝ) (B : J → ZMod N → ℝ)
    (label : I → ZMod P) (f : ℤ → X) (b : ℤ → Y) {R K ρ : ℝ}
    (hR : 0 ≤ R) (hρ : 0 < ρ)
    (hA : ∀ i x, 0 ≤ A i x)
    (hres : ∀ i x, 0 < A i x → (x.val : ZMod P) = label i)
    (hcircle : ∀ i x y, 0 < A i x → 0 < A i y →
      dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ)
    (hrecover : ∀ n m : ℤ, (n : ZMod P) = (m : ZMod P) →
      ∀ δ : ℝ, 0 ≤ δ → |(n : ℝ)| ≤ N → |(m : ℝ)| ≤ N →
        |(n : ℝ) - m| ≤ (N : ℝ) * δ →
        dist (b n) (b m) ≤ R * (dist (f n) (f m) + δ))
    (h : ZMod N) (i : I) (j : J) (x y : ZMod N)
    (hx : x ∉ cyclicWrapExceptional h ρ) (hy : y ∉ cyclicWrapExceptional h ρ)
    (hxy : 0 < A i x * B j (x + h)) (hyy : 0 < A i y * B j (y + h))
    (hinput : dist (f x.val) (f y.val) ≤ K * ρ) :
    dist (b x.val) (b y.val) ≤ R * (K + 1) * ρ := by
  have hpositive (z : ZMod N) (hz : 0 < A i z * B j (z + h)) : 0 < A i z := by
    rcases mul_pos_iff.mp hz with hz | hz
    · exact hz.1
    · linarith [hA i z]
  have hAx := hpositive x hxy
  have hAy := hpositive y hyy
  have hmod : ((x.val : ℤ) : ZMod P) = ((y.val : ℤ) : ZMod P) := by
    simpa only [Int.cast_natCast] using (hres i x hAx).trans (hres i y hAy).symm
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hbound (z : ZMod N) : |((z.val : ℤ) : ℝ)| ≤ (N : ℝ) := by
    rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast (Nat.le_of_lt (ZMod.val_lt z))
  have hdiff := good_circle_observations_control_representatives h x y hρ hx hy
    (hcircle i x y hAx hAy)
  rw [← sub_div, abs_div, abs_of_pos hN] at hdiff
  have hdiff' : |((x.val : ℤ) : ℝ) - ((y.val : ℤ) : ℝ)| ≤ (N : ℝ) * ρ := by
    simpa only [Int.cast_natCast, mul_comm ρ (N : ℝ)] using (div_le_iff₀ hN).mp hdiff
  calc
    _ ≤ R * (dist (f x.val) (f y.val) + ρ) :=
      hrecover x.val y.val hmod ρ hρ.le (hbound x) (hbound y) hdiff'
    _ ≤ R * (K * ρ + ρ) := mul_le_mul_of_nonneg_left
      (by linarith : dist (f x.val) (f y.val) + ρ ≤ K * ρ + ρ) hR
    _ = _ := by ring

end Erdos3

end

section

universe u v w

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_native_cyclic_recovery (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ NativeCyclicRecoverySpec.{u, v, w} s k C := by
  obtain ⟨C, hC, hrec⟩ := exists_slow_residue_recovery s k
  refine ⟨C, hC, ?_⟩
  dsimp only [NativeCyclicRecoverySpec]
  intro L M _ _ _ _ _ _ _ _ _ _ _ _ d e D E φ p hp hD hE hφ q hq hqp
  have hp0 : 0 ≤ p := by linarith
  obtain ⟨P, m, hP, hm, hPb, hmb, Λ, hΛ, hchar, hnormal, hfinite, hindex,
      l, hl, hin, hout, hQ, hrecover⟩ :=
    hrec D E φ (fun _ : Unit => 1) (fun _ => Nat.zero_lt_one) hp0
      (by simpa only [Fintype.card_unit, Nat.cast_one] using hp) hD hE hφ q hq hqp
  let Q := D.withLattice Λ l hl hin hout
  let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
    (hM := E.filtration.lowerCentralSeries_eq_bot) φ
  refine ⟨P, m, hP, hm, hPb, hmb, Λ, hΛ, hchar, hnormal, hfinite, hindex,
    l, hl, hin, hout, hQ, ?_⟩
  let := Q.metricSpace
  let := E.metricSpace
  intro R hR
  obtain ⟨z, hz, heval⟩ := hrecover R hR
  refine ⟨z, hz, ?_⟩
  intro κ hκ a b r f hfactor hvalue
  obtain ⟨hexact, hmove⟩ := heval κ hκ a b r f hfactor hvalue
  refine ⟨hexact, ?_⟩
  intro N _ S hS hSvalue I J A B label ρ K hρ hA hres hcircle h i j x y hx hy hxy hyy hinput
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  apply positive_cell_residue_recovery A B label
    (fun n => (QuotientGroup.mk (f (fun _ => n)) : Q.Space))
    (fun n => (QuotientGroup.mk (ψ (b (fun _ => n))) : E.Space))
    (Real.exp_pos _).le hρ hA hres hcircle ?_ h i j x y hx hy hxy hyy hinput
  intro n m hmod δ hδ hn hm hdiff
  exact hmove (fun _ : Unit => (N : ℝ)) (fun _ => hN) S hS hSvalue
    (fun _ => n) (fun _ => m) (funext (fun _ => hmod)) δ hδ
    (fun _ => hn) (fun _ => hm) (fun _ => hdiff)

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v w z

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v w z

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {L : ι → Type u}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
  (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
  (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
  (Q : RationalFilteredNilmanifold
    (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  [TopologicalSpace (ℝ ⊗[ℚ] L a)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L a)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L a)] [T2Space (ℝ ⊗[ℚ] L a)]

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {L : ι → Type u}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
  (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
  (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
  (Q : RationalFilteredNilmanifold
    (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  [TopologicalSpace (ℝ ⊗[ℚ] L a)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L a)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L a)] [T2Space (ℝ ⊗[ℚ] L a)]

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

theorem exists_refiltered_recovered_expansion (s r : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] {L : ι → Type u}
      [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d : ι → ℕ}
      (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
      (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
      (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
      (Q : RationalFilteredNilmanifold
        (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
      [TopologicalSpace (ℝ ⊗[ℚ] L a)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L a)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L a)] [T2Space (ℝ ⊗[ℚ] L a)]
      {p b : ℝ} {q P₀ : ℕ}, 1 ≤ p → p ≤ b → (Fintype.card ι : ℝ) ≤ b →
      (∀ i, (D i).GeometryComplexityLE b) → 0 < q → (q : ℝ) ≤ Real.exp b →
      0 < P₀ → (P₀ : ℝ) ≤ Real.exp b →
      RefilteredResidueExpansionSpec D a W E Q p q r P₀ b →
      RefilteredRecoveredExpansionSpec D a W E Q p q r ((b + C) ^ C) := by
  obtain ⟨a₀, _, hrecover⟩ := exists_native_cyclic_recovery.{u, u, u} (s + 1) r
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + 2) ^ 2 + X + 1
  let R := (T + Polynomial.C a₀) ^ a₀
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + X + R)
  refine ⟨C, hC, ?_⟩
  intro ι _ _ L _ _ d D a W e n E Q _ _ _ _ p b q P₀ hp hpb hι hD hq hqb hP₀ hP₀b hbase
  classical
  let H := (pi D).filtration.gradedRefiltrationSubalgebra W
  let I₀ := {i : ι // i ≠ a}
  let Z₀ := pi (fun i : I₀ => D i.val)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  let := realification_moduleTopology_t2 Q.basis
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i : I₀, L i.val))
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i : I₀, L i.val))
  let := realification_moduleTopology_t2 Z₀.basis
  obtain ⟨Q', hQF, hQb, hQle, hQ, Z, hZF, hZb, hZle, hZ, hbase⟩ := hbase
  let t := (b + 2) ^ 2 + b + 1
  let cost := (b + C) ^ C
  have hb : 0 ≤ b := by linarith
  have hbt : b ≤ t := by dsimp [t]; nlinarith [sq_nonneg (b + 2)]
  have ht : 0 ≤ t := hb.trans hbt
  have hsum : t + b + (t + a₀) ^ a₀ ≤ cost := by
    simpa [T, R, X, t, cost, Polynomial.eval₂_pow] using hbudget b hb
  have hrecpos : 0 ≤ (t + a₀) ^ a₀ := pow_nonneg (by positivity) _
  have hbCost : b ≤ cost := by linarith
  have hrecCost : (t + a₀) ^ a₀ ≤ cost := by linarith
  have hbothCost : b + (t + a₀) ^ a₀ ≤ cost := by linarith
  have hI₀ : (Fintype.card I₀ : ℝ) ≤ b :=
    (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans hι
  have hZ₀ : Z₀.GeometryComplexityLE t :=
    (pi_geometry (fun i : I₀ => D i.val) hb hI₀ (fun i => hD i.val)).mono Z₀
      (by dsimp [t]; linarith)
  let idLie : (∀ i : I₀, L i.val) →ₗ⁅ℚ⁆ (∀ i : I₀, L i.val) := LieHom.id
  have hheight (i j : Fin (Fintype.card (Σ i : I₀, Fin (d i.val)))) :
      rationalLogHeight (Z.basis.repr (idLie (Z₀.basis j)) i) ≤ t := by
    rw [hZb]
    change rationalLogHeight (Z₀.basis.repr (Z₀.basis j) i) ≤ t
    rw [Basis.repr_self]
    by_cases h : j = i <;> simp [h, rationalLogHeight, ht]
  obtain ⟨P₁, _, hP₁, _, hP₁b, _, Λ, hΛ, hchar, hnormal, hfinite, hindex,
      l, hl, hin, hout, hV, hrec⟩ := hrecover Z₀ Z idLie (hp.trans (hpb.trans hbt))
        hZ₀ (hZ.mono Z hbt) hheight q hq (hqb.trans (Real.exp_le_exp.mpr hbt))
  have hP : ((P₀ * P₁ : ℕ) : ℝ) ≤ Real.exp cost := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp b * Real.exp ((t + a₀) ^ a₀) :=
        mul_le_mul hP₀b hP₁b (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (b + (t + a₀) ^ a₀) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hbothCost
  refine ⟨P₀ * P₁, Nat.mul_pos hP₀ hP₁, hP, Q', hQF, hQb, hQle, hQ.mono Q' hbCost,
    Z, hZF, hZb, hZle, hZ.mono Z hbCost, Λ, hΛ, hchar, hnormal, hfinite,
    hindex.trans (Real.exp_le_exp.mpr hrecCost), l, hl, hin, hout, hV.mono _ hrecCost, ?_⟩
  let V := Z₀.withLattice Λ l hl hin hout
  let := V.metricSpace
  let := Z.metricSpace
  let Ψ := realificationMap (hnil := Z₀.filtration.lowerCentralSeries_eq_bot)
    (hM := Z.filtration.lowerCentralSeries_eq_bot) idLie
  have hΨ (x : Z₀.RealGroup) : Ψ x = x := by
    apply NilpotentLieBCHGroup.ext
    exact realificationLieHom_id_apply x.coord
  dsimp only [Ψ] at hΨ
  dsimp only
  intro J₀ freq hfreq N _ I J _ _ A B label ρ K hρ hK hA hB hAsum hBsum hres hcircle
    S hS hpositive hinvariant slow middle rat κ g hκ hfactor hslow hrat hmiddle
    slowZ ratZ κZ fZ hκZ hfactorZ hslowZ hratZ hinput
  let w := fun _ : Unit => 1
  let ψ := realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
    (hM := Z.filtration.lowerCentralSeries_eq_bot)
    (liePiMap (fun i : I₀ => refilteredComponentMap D W i.val))
  let π₀ := ZMod.castHom (dvd_mul_right P₀ P₁) (ZMod P₀)
  let π₁ := ZMod.castHom (dvd_mul_left P₁ P₀) (ZMod P₁)
  let label₀ := fun i => π₀ (label i)
  let label₁ := fun i => π₁ (label i)
  have hres₀ (i : I) (x : ZMod N) (hx : 0 < A i x) : (x.val : ZMod P₀) = label₀ i := by
    simpa only [map_natCast] using congrArg π₀ (hres i x hx)
  have hres₁ (i : I) (x : ZMod N) (hx : 0 < A i x) : (x.val : ZMod P₁) = label₁ i := by
    simpa only [map_natCast] using congrArg π₁ (hres i x hx)
  have hslowZ' (h : ZMod N) : Z.filtration.PolynomialSlowBound Z.basis w
      (fun _ => (N : ℝ)) (Real.exp ((t + 2) ^ r)) (slowZ h) :=
    Z.filtration.polynomialSlowBound_mono Z.basis w (fun _ => (N : ℝ))
      (fun _ => Nat.cast_pos.mpr (NeZero.pos N))
      (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ p + 2)
        (by linarith : p + 2 ≤ t + 2) r)) (slowZ h) (hslowZ h)
  let η := Real.exp ((t + a₀) ^ a₀) * (K + 1) * ρ
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hdiam (i : I) (j : J) (h x y : ZMod N)
      (hx : x ∉ cyclicWrapExceptional h ρ) (hy : y ∉ cyclicWrapExceptional h ρ)
      (hxy : 0 < A i x * B j (x + h)) (hyy : 0 < A i y * B j (y + h)) :
      dist (QuotientGroup.mk (ψ (E.filtration.realification.polynomialOrbitEval w
        (fun _ => (x.val : ℤ)) (g h))) : Z.Space)
        (QuotientGroup.mk (ψ (E.filtration.realification.polynomialOrbitEval w
          (fun _ => (y.val : ℤ)) (g h)))) ≤ η := by
    obtain ⟨_, _, hmove⟩ := hrec (ratZ h) (hratZ h)
    obtain ⟨_, hcell⟩ := hmove (κZ h) (hκZ h)
      (fun x => Z.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) (slowZ h))
      (fun x => ψ (E.filtration.realification.polynomialOrbitEval w x (g h)))
      (fun x => Z.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) (ratZ h))
      (fZ h) (hfactorZ h) (fun _ => hΨ _)
    have hd := hcell N (slowZ h) (hslowZ' h) (fun _ => hΨ _)
      A B label₁ hρ hA hres₁ hcircle h i j x y hx hy hxy hyy (hinput i j h x y hx hy hxy hyy)
    simpa only [hΨ] using hd
  obtain ⟨U, hU, hUcomplexity, hUempty, err, herr, hmean⟩ :=
    hbase freq hfreq N A B label₀ hρ hη hA hB hAsum hBsum hres₀ hcircle
      S hS hpositive hinvariant slow middle rat κ g hκ hfactor hslow hrat hmiddle hdiam
  refine ⟨U, hU, fun i j h => (hUcomplexity i j h).mono (by linarith), hUempty, err, herr, ?_⟩
  intro h
  have hρR : ρ ≤ Real.exp ((t + a₀) ^ a₀) * ρ := by
    nlinarith [Real.one_le_exp hrecpos]
  have hprod := mul_le_mul_of_nonneg_left
    (show ρ + η ≤ Real.exp ((t + a₀) ^ a₀) * ρ + η by linarith) (Real.exp_pos b).le
  calc
    _ ≤ Real.exp b * (ρ + η) + 6 * ρ + 3 / N := hmean h
    _ ≤ Real.exp b * (Real.exp ((t + a₀) ^ a₀) * ρ + η) + 6 * ρ + 3 / N := by linarith
    _ = Real.exp (b + (t + a₀) ^ a₀) * (K + 2) * ρ + 6 * ρ + 3 / N := by
      rw [Real.exp_add]
      dsimp [η]
      ring
    _ ≤ Real.exp cost * (K + 2) * ρ + 6 * ρ + 3 / N := by
      have hh := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hbothCost)
        (show 0 ≤ (K + 2) * ρ by positivity)
      nlinarith

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_controlled_refiltered_recovered_expansion (s r : ℕ) :
    ∃ A B : ℕ, 2 ≤ A ∧ 2 ≤ B ∧ ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
      {L : ι → Type u} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {κ : Type*} [Fintype κ] {d : ι → ℕ}
      (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
      (w : ∀ i, Fin (d i) → ℕ)
      (hF : ∀ i j, (D i).filtration.layer j =
        Submodule.span ℚ ((D i).basis '' {b | j ≤ w i b}))
      (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded)
      (v₀ : κ → (pi D).filtration.AssociatedGraded)
      (_hspan : Submodule.span ℚ (Set.range v₀) = W.toSubmodule) {p : ℝ},
      1 ≤ p → (Fintype.card ι : ℝ) ≤ p → (∀ i, (D i).GeometryComplexityLE p) →
      (Fintype.card κ : ℝ) ≤ p →
      (∀ i b, rationalLogHeight (((pi D).filtration.associatedGradedBasis (pi D).basis
        (productBasisWeight w) (pi_layer_span D w hF)).repr (v₀ i) b) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W)
          (s + 1) (finrank ℚ ((pi D).filtration.gradedRefiltrationSubalgebra W)),
        E.filtration = (pi D).filtration.gradedRefiltration W ∧
        E.lattice = (pi D).lattice.comap
          (NilpotentLieBCHGroup.map
            (hnil := ((pi D).filtration.gradedRefiltration W).lowerCentralSeries_eq_bot)
            ((pi D).filtration.gradedRefiltrationSubalgebra W).incl) ∧
        E.GeometryComplexityLE ((p + A) ^ A) ∧
        ∃ n : ℕ, n ≤ finrank ℚ ((pi D).filtration.gradedRefiltrationSubalgebra W) ∧
          ∃ Q : RationalFilteredNilmanifold
              (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n,
            Q.filtration = E.filtration.quotientTop ∧
            Q.lattice = E.lattice.map
              (E.filtration.quotientStepHom (E.filtration.layerIdeal (s + 1)) le_rfl) ∧
            Q.GeometryComplexityLE ((p + A) ^ A) ∧
            (nativeRefilteredTarget D a W E Q).GeometryComplexityLE ((p + A) ^ A) ∧
            RefilteredRecoveredExpansionSpec D a W E Q p q r (((p + A) ^ A + B) ^ B) := by
  obtain ⟨A, hA, hmodels⟩ := exists_controlled_refiltered_residue_expansion s r
  obtain ⟨B, hB, hrecover⟩ := exists_refiltered_recovered_expansion s r
  refine ⟨A, B, hA, hB, ?_⟩
  intro ι _ _ L _ _ _ _ _ _ κ _ d D a w hF W v₀ hspan p hp hι hD hκ hv q hq hqp
  obtain ⟨P, hP, hPb, E, hEF, hEL, hE, n, hn, Q, hQF, hQL, hQ, htarget, hbase⟩ :=
    hmodels D a w hF W v₀ hspan hp hι hD hκ hv q hq hqp
  have hAℝ : (2 : ℝ) ≤ A := by exact_mod_cast hA
  have hpA : p ≤ (p + A) ^ A :=
    (le_power_budget (by linarith) (by omega : 1 ≤ A)).trans
      (pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ p + 2) (by linarith) A)
  refine ⟨E, hEF, hEL, hE, n, hn, Q, hQF, hQL, hQ, htarget, ?_⟩
  exact hrecover D a W E Q hp hpA (hι.trans hpA) (fun i => (hD i).mono (D i) hpA)
    hq (hqp.trans (Real.exp_le_exp.mpr hpA)) hP hPb hbase

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

theorem solution.{u, u_1} : type_of% @OAI.Erdos3.RationalFilteredNilmanifold.exists_controlled_refiltered_recovered_expansion.{u, u_1} := @OAI.Erdos3.RationalFilteredNilmanifold.exists_controlled_refiltered_recovered_expansion.{u, u_1}
