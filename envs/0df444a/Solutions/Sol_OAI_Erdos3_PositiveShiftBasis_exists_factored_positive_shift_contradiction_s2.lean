-- Prove2me | solution 1 for OAI.Erdos3.PositiveShiftBasis.exists_factored_positive_shift_contradiction_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:17:58.646558+00:00
-- url     : https://prove2.me/submissions/8a3ae967-a3cc-4bbf-a0d3-77ff753a2400

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B230
import Theorems.Thm_OAI_Erdos3_PositiveShiftBasis_exists_common_refiltered_expansion_s2
import Theorems.Thm_OAI_Erdos3_RationalFilteredNilmanifold_exists_prescribed_complement_input_partition_s2
import Theorems.Thm_OAI_Erdos3_exists_native_partition_expansion_contradiction_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.RefilteredExpansionErrorBudget
namespace OAI

section

namespace Erdos3

theorem refiltered_expansion_error_budget {cost metric ε R : ℝ}
    (hc : 0 ≤ cost) (hm : 0 ≤ metric) (hε : 0 ≤ ε)
    (hbudget : cost + metric + 10 ≤ R) :
    Real.exp cost * (Real.exp metric + 2) * ε + 6 * ε ≤ Real.exp R * ε := by
  have hE : 1 ≤ Real.exp cost := Real.one_le_exp hc
  have hK : 1 ≤ Real.exp metric := Real.one_le_exp hm
  have hEK : 1 ≤ Real.exp cost * Real.exp metric := by nlinarith
  have hEE : Real.exp cost ≤ Real.exp cost * Real.exp metric := by nlinarith [Real.exp_pos cost]
  have hsmall : Real.exp cost * (Real.exp metric + 2) + 6 ≤
      9 * (Real.exp cost * Real.exp metric) := by nlinarith
  have h9 : (9 : ℝ) ≤ Real.exp 10 := by linarith [Real.add_one_le_exp (10 : ℝ)]
  have hlarge : Real.exp cost * (Real.exp metric + 2) + 6 ≤ Real.exp R := by
    calc
      _ ≤ 9 * (Real.exp cost * Real.exp metric) := hsmall
      _ ≤ Real.exp 10 * (Real.exp cost * Real.exp metric) :=
        mul_le_mul_of_nonneg_right h9 (by positivity)
      _ = Real.exp (cost + metric + 10) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp R := Real.exp_le_exp.mpr hbudget
  nlinarith [mul_le_mul_of_nonneg_right hlarge hε]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PositiveShiftRefilteredExpansionSpec
namespace OAI

section

universe u

namespace Erdos3.PositiveShiftBasis

open Module RationalFilteredNilmanifold NilpotentLieFiltration VectorPolynomial
open scoped TensorProduct

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff
attribute [local instance_reducible] optionLieSpace

variable {s N : ℕ} [NeZero N] {q : ℝ} {a J : ZMod N → ℝ}
  {B : PositiveShiftBasis.{u} s N q a J} {L M : Fin B.count → Type u}
  [∀ j, LieRing (L j)] [∀ j, LieAlgebra ℚ (L j)]
  [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)] {d e : Fin B.count → ℕ}
  [∀ j, TopologicalSpace (ℝ ⊗[ℚ] L j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] L j)]
  [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] L j)] [∀ j, T2Space (ℝ ⊗[ℚ] L j)]
  [∀ j, TopologicalSpace (ℝ ⊗[ℚ] M j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] M j)]
  [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] M j)] [∀ j, T2Space (ℝ ⊗[ℚ] M j)]
  {D : ∀ j, RationalFilteredNilmanifold (L j) s (d j)}
  {E : ∀ j, RationalFilteredNilmanifold (M j) s (e j)}
  {A : ∀ j, (D j).Niltest (fun _ : Unit => 1)}
  {R : ZMod N → ∀ j, (E j).Niltest (fun _ : Unit => 1)}
  {anchor : ZMod N} {H : Finset (ZMod N)} {p : ℝ}

theorem CommonFactorization.exists_test_extension
    (F : B.CommonFactorization D E A R anchor H p) (hH : H ⊆ B.shifts) (hqp : q ≤ p) :
    ∃ S : ZMod N → B.model.Niltest (fun _ : Unit => 1),
      (∀ h ∈ F.shifts, S h = B.test h) ∧
      (∀ h, (S h).ComplexityLE p) ∧ (∀ h, (S h).UnitIntervalValued) ∧
      (∀ h z, z ∈ B.model.filtration.realification.subgroup s →
        (∀ j, realifyFunctional (F.frequency j none) z.coord = 0) → ∀ x,
          (S h).observable (z • x) = (S h).observable x) := by
  classical
  obtain ⟨h₀, hh₀⟩ := F.shifts_nonempty
  let select (h : ZMod N) := if h ∈ F.shifts then h else h₀
  have hselect (h) : select h ∈ F.shifts := by
    by_cases hh : h ∈ F.shifts <;> simp [select, hh, hh₀]
  refine ⟨fun h => B.test (select h), ?_, ?_, ?_, ?_⟩
  · intro h hh
    simp only [select, if_pos hh]
  · intro h
    exact (B.test_complexity (select h) (hH (F.shifts_sub (hselect h)))).mono hqp
  · intro h
    exact B.test_positive (select h) (hH (F.shifts_sub (hselect h)))
  · intro h z hz hfreq x
    exact F.invariant (select h) (hselect h) z hz hfreq x

theorem CommonFactorization.exists_factor_family
    (F : B.CommonFactorization D E A R anchor H p) : F.FactorFamily := by
  classical
  dsimp only [CommonFactorization.FactorFamily]
  let T := B.anchoredFactors D E
  have hdata (h : ZMod N) (hh : h ∈ F.shifts) := F.factors h hh
  choose freq _ _ κ slow middle rat hκ hfactor hslow hrat hzero _ hcoeff _ using hdata
  let κ' (h : ZMod N) := if hh : h ∈ F.shifts then κ h hh else 1
  let slow' (h : ZMod N) := if hh : h ∈ F.shifts then slow h hh else 1
  let middle' (h : ZMod N) := if hh : h ∈ F.shifts then middle h hh else 1
  let rat' (h : ZMod N) := if hh : h ∈ F.shifts then rat h hh else 1
  refine ⟨κ', slow', middle', rat', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h hh
    simpa only [κ', dif_pos hh] using hκ h hh
  · intro h hh
    simpa only [κ', slow', middle', rat', dif_pos hh] using hfactor h hh
  · intro h hh
    simpa only [slow', dif_pos hh] using hslow h hh
  · intro h hh
    simpa only [rat', dif_pos hh] using hrat h hh
  · intro h hh
    simpa only [middle', dif_pos hh] using hzero h hh
  · intro h hh α
    simpa only [middle', dif_pos hh] using hcoeff h hh α

end Erdos3.PositiveShiftBasis

end

section

namespace Erdos3.PositiveShiftBasis

open Module RationalFilteredNilmanifold NilpotentLieFiltration
open scoped TensorProduct

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff
attribute [local instance_reducible] optionLieSpace

theorem productExpansionBudget_bounds {p : ℝ} (hp : 0 ≤ p) :
    2 ≤ productExpansionBudget p ∧ p ≤ productExpansionBudget p ∧
      (2 * p + 4) ^ 2 ≤ productExpansionBudget p := by
  dsimp [productExpansionBudget]
  constructor
  · nlinarith [sq_nonneg (2 * p + 4)]
  constructor
  · nlinarith [sq_nonneg (2 * p + 4)]
  · linarith

end Erdos3.PositiveShiftBasis

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.TrivialPolynomialData
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

namespace NilpotentLieFiltration

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : σ → ℕ)

theorem polynomialSlowBound_one (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M : ℝ} (hM : 0 ≤ M) : F.PolynomialSlowBound b w T M 1 := by
  intro α i
  change |(b.baseChange ℝ).repr (coefficients (0 : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) i| ≤ _
  simp only [map_zero, Finsupp.zero_apply, abs_zero]
  exact div_nonneg hM (monomialScale_pos T hT α).le

theorem polynomialRationalGrid_one (q : ℕ) : F.PolynomialRationalGrid b w q 1 := by
  refine ⟨fun _ => 0, ?_⟩
  funext z
  simp only [Pi.smul_apply, smul_eq_mul, Int.cast_zero]
  change (0 : ℝ) = (q : ℝ) * (b.baseChange ℝ).repr
    (coefficients (0 : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2
  simp only [map_zero, Finsupp.zero_apply, mul_zero]

theorem piRealOrbit_one {κ : Type*} [Fintype κ] {L : κ → Type*}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ}
    (F : ∀ i, NilpotentLieFiltration (L i) s) {σ : Type*} (w : σ → ℕ) :
    piRealOrbit F (fun _ => (1 : (F _).realification.PolynomialOrbit w)) = 1 := by
  apply Subtype.ext
  apply NilpotentLieBCHGroup.ext
  change (∑ i, VectorPolynomial.map ((realProductSingle i).restrictScalars ℚ)
    (0 : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L i))) = 0
  simp only [map_zero, Finset.sum_const_zero]

end NilpotentLieFiltration

namespace RationalFilteredNilmanifold.Niltest

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem const_zero_complexity_of {T : D.Niltest w} {p : ℝ} (hT : T.ComplexityLE p) :
    (const D w 0).ComplexityLE p := by
  refine ⟨hT.1, ?_⟩
  change Real.log (2 + (‖(0 : ℂ)‖₊ : ℝ) + (0 : ℝ)) ≤ p
  simp only [nnnorm_zero, NNReal.coe_zero, add_zero]
  exact (Real.log_le_log (by norm_num)
    (show (2 : ℝ) ≤ 2 + T.normBound + T.lipBound by
      linarith [T.normBound.coe_nonneg, T.lipBound.coe_nonneg])).trans hT.2

theorem const_zero_unit_interval (D : RationalFilteredNilmanifold L s d) (w : σ → ℕ) :
    (const D w 0).UnitIntervalValued := by
  intro x
  simp only [const, Complex.zero_im, Complex.zero_re, le_refl, zero_le_one, and_self]

end RationalFilteredNilmanifold.Niltest
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrescribedPartitionExpansionCore
namespace OAI

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial NilpotentLieFiltration NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {L : ι → Type u}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
  (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
  (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
  (Q : RationalFilteredNilmanifold
    (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  [TopologicalSpace (ℝ ⊗[ℚ] L a)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L a)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L a)] [T2Space (ℝ ⊗[ℚ] L a)]

theorem selected_refiltered_product_expansion
    {p cost : ℝ} {q r : ℕ} (hbase : RefilteredProductExpansionSpec D a W E Q p q r cost) :
    SelectedRefilteredProductExpansionSpec D a W E Q p q r cost := by
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
  obtain ⟨P, hP, hPb, Q', hQF, hQb, hQle, hQ, Λ, hΛ, hchar, hnormal,
    hfinite, hindex, l, hl, hin, hout, hV, hbase⟩ := hbase
  refine ⟨P, hP, hPb, Q', hQF, hQb, hQle, hQ, Λ, hΛ, hchar, hnormal,
    hfinite, hindex, l, hl, hin, hout, hV, ?_⟩
  let V := Z₀.withLattice Λ l hl hin hout
  let := V.metricSpace
  dsimp only
  intro J₀ freq hfreq N _ I J _ _ A B label ρ K hρ hK hA hB hAsum hBsum hres hcircle
    S hS hpositive hinvariant Hsh g horbit slow middle rat κ hκ hfactor hslow hrat hcoeff hzero hinput
  let w := fun _ : Unit => 1
  let S' := fun h => if h ∈ Hsh then S h else Niltest.const (D a) w 0
  let g' := fun h i => if h ∈ Hsh then g h i else (1 : (D i).filtration.realification.PolynomialOrbit w)
  let slow' := fun h => if h ∈ Hsh then slow h else 1
  let middle' := fun h => if h ∈ Hsh then middle h else 1
  let rat' := fun h => if h ∈ Hsh then rat h else 1
  let κ' := fun h => if h ∈ Hsh then κ h else 1
  have hS' (h) : (S' h).ComplexityLE p := by
    by_cases hh : h ∈ Hsh
    · simpa only [S', hh, ite_true] using hS h
    · simpa only [S', hh, ite_false] using Niltest.const_zero_complexity_of (hS h)
  have hpositive' (h) : (S' h).UnitIntervalValued := by
    by_cases hh : h ∈ Hsh
    · simpa only [S', hh, ite_true] using hpositive h
    · simpa only [S', hh, ite_false] using Niltest.const_zero_unit_interval (D a) w
  have hinvariant' (h : ZMod N) (z : (D a).RealGroup)
      (hz : z ∈ (D a).filtration.realification.subgroup (s + 1))
      (hfreqz : ∀ j, realifyFunctional (freq j a) z.coord = 0) (x : (D a).Space) :
      (S' h).observable (z • x) = (S' h).observable x := by
    by_cases hh : h ∈ Hsh
    · simpa only [S', hh, ite_true] using hinvariant h z hz hfreqz x
    · simp only [S', hh, ite_false, Niltest.const]
  have horbit' (h) : g' h a = (S' h).orbit := by
    by_cases hh : h ∈ Hsh
    · simpa only [g', S', hh, ite_true] using horbit h hh
    · simp only [g', S', hh, ite_false, Niltest.const]
  have hκ' (h) : κ' h ∈ (pi D).realLattice := by
    by_cases hh : h ∈ Hsh
    · simpa only [κ', hh, ite_true] using hκ h hh
    · simp only [κ', hh, ite_false, Subgroup.one_mem]
  have hfactor' (h) : slow' h * middle' h * rat' h *
      (pi D).filtration.realification.adaptedConstantGroupHom w (κ' h) =
        ⟨⟨(piRealOrbit (fun i => (D i).filtration) (g' h)).log,
          (piRealOrbit (fun i => (D i).filtration) (g' h)).property⟩⟩ := by
    by_cases hh : h ∈ Hsh
    · simpa only [slow', middle', rat', κ', g', hh, ite_true] using hfactor h hh
    · simp only [slow', middle', rat', κ', g', hh, ite_false, map_one, one_mul, piRealOrbit_one]
      rfl
  have hslow' (h) : (pi D).filtration.PolynomialSlowBound (pi D).basis w
      (fun _ => (N : ℝ)) (Real.exp ((p + 2) ^ r)) (slow' h) := by
    by_cases hh : h ∈ Hsh
    · simpa only [slow', hh, ite_true] using hslow h hh
    · simpa only [slow', hh, ite_false] using
        (pi D).filtration.polynomialSlowBound_one (pi D).basis w (fun _ => (N : ℝ))
          (fun _ => Nat.cast_pos.mpr (NeZero.pos N)) (Real.exp_pos _).le
  have hrat' (h) : (pi D).filtration.PolynomialRationalGrid (pi D).basis w q (rat' h) := by
    by_cases hh : h ∈ Hsh
    · simpa only [rat', hh, ite_true] using hrat h hh
    · simpa only [rat', hh, ite_false] using
        (pi D).filtration.polynomialRationalGrid_one (pi D).basis w q
  have hcoeff' (h α) : coefficients
      ((middle' h).coord : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] (∀ i, L i))) α ∈
        (pi D).filtration.realGradedRefiltrationLayer W (Finsupp.weight w α) := by
    by_cases hh : h ∈ Hsh
    · simpa only [middle', hh, ite_true] using hcoeff h hh α
    · simp only [middle', hh, ite_false]
      change coefficients (0 : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] (∀ i, L i))) α ∈ _
      simp only [map_zero, Finsupp.zero_apply, Submodule.zero_mem]
  have hzero' (h) : coefficients
      ((middle' h).coord : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] (∀ i, L i))) 0 = 0 := by
    by_cases hh : h ∈ Hsh
    · simpa only [middle', hh, ite_true] using hzero h hh
    · simp only [middle', hh, ite_false]
      change coefficients (0 : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] (∀ i, L i))) 0 = 0
      simp only [map_zero, Finsupp.zero_apply]
  have hinput' (i : I) (j : J) (h x y : ZMod N)
      (hx : x ∉ cyclicWrapExceptional h ρ) (hy : y ∉ cyclicWrapExceptional h ρ)
      (hAx : 0 < A i x * B j (x + h)) (hAy : 0 < A i y * B j (y + h)) :
      dist (V.cyclicOrbitPoint (piRealOrbit (fun i : I₀ => (D i.val).filtration)
        (fun i : I₀ => g' h i.val)) N (fun _ : Unit => x))
        (V.cyclicOrbitPoint (piRealOrbit (fun i : I₀ => (D i.val).filtration)
          (fun i : I₀ => g' h i.val)) N (fun _ : Unit => y)) ≤ K * ρ := by
    by_cases hh : h ∈ Hsh
    · simpa only [g', hh, ite_true] using hinput i j h hh x y hx hy hAx hAy
    · simp only [g', hh, ite_false, piRealOrbit_one]
      change dist (QuotientGroup.mk (V.filtration.realification.polynomialOrbitEval w
        (fun _ : Unit => (x.val : ℤ)) 1) : V.Space)
        (QuotientGroup.mk (V.filtration.realification.polynomialOrbitEval w
          (fun _ : Unit => (y.val : ℤ)) 1)) ≤ K * ρ
      rw [map_one, map_one, dist_self]
      exact mul_nonneg hK hρ.le
  obtain ⟨U, hU, hUc, hUempty, err, heval, hmean⟩ :=
    hbase freq hfreq N A B label hρ hK hA hB hAsum hBsum hres hcircle S' hS' hpositive'
      hinvariant' g' horbit' slow' middle' rat' κ' hκ' hfactor' hslow' hrat' hcoeff' hzero' hinput'
  refine ⟨U, hU, hUc, hUempty, err, ?_, hmean⟩
  intro h hh x
  simpa only [S', hh, ite_true] using heval h x

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct BigOperators

attribute [local instance_reducible] optionLieSpace

theorem prescribed_partition_expansion_from_partition (s r b₀ k₀ a B C B₀ J : ℕ)
    (hpartition : PrescribedComplementInputPartitionSpec (s + 1) k₀ a B₀ J)
    (hbudget : ∀ p : ℝ, 0 ≤ p →
      (p + (p + b₀) ^ b₀ + 2) + (p + (p + b₀) ^ b₀ + 2 + J) ^ J ≤ (p + C) ^ C)
    (hmetricBudget : ∀ p : ℝ, 0 ≤ p →
      (p + b₀) ^ b₀ + (p + (p + b₀) ^ b₀ + 2 + B₀) ^ B₀ + 10 ≤ (p + B) ^ B) :
    PrescribedPartitionExpansionSpec s r b₀ k₀ a B C := by
  dsimp only [PrescribedPartitionExpansionSpec]
  intro ι κ _ _ _ _ L _ _ d m _ _ _ _ K _ _ e _ _ _ _ D _ _ _ _ _ _ _ _
    b v hF M hM hin hout E L₀ _ _ d₀ D₀ W dR dQ R Q₀ _ _ _ _ p cost q
    hp hι hκ hD hV hb hE hcost hcostb hbase
  classical
  let Q := fun i => (D i).filtration.squareFiltration.topQuotientModel
    ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) (squareFinWeight (v i))
    ((D i).filtration.squareFinBasis_layers (b i) (v i) (hF i))
    ((D i).filtration.squareLattice (D i).lattice) (M i) (hM i) (hin i) (hout i)
  let Z := sumFactors E Q
  let T := optionFactors D₀ Z
  let H := (pi T).filtration.gradedRefiltrationSubalgebra W
  let KL := sumLieSpace K (fun i => (D i).filtration.squareLieSubalgebra ⧸
    (D i).filtration.squareFiltration.layerIdeal (s + 1 + 1))
  let I₀ := {i : Option (κ ⊕ ι) // i ≠ none}
  let Z₀ := pi (optionComplementFactors D₀ Z)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (H ⧸ R.filtration.layerIdeal (s + 1)))
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (H ⧸ R.filtration.layerIdeal (s + 1)))
  let := realification_moduleTopology_t2 Q₀.basis
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i : I₀, optionLieSpace L₀ KL i.val))
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i : I₀, optionLieSpace L₀ KL i.val))
  let := realification_moduleTopology_t2 Z₀.basis
  have hselected : SelectedRefilteredProductExpansionSpec T none W R Q₀ p q r cost :=
    selected_refiltered_product_expansion T none W R Q₀ hbase
  obtain ⟨P, hP, hPb, Q', hQF, hQb, hQle, hQ, Λ, hΛ, hchar, hnormal,
      hfinite, hindex, l, hl, hlin, hlout, hV₀, hbase⟩ :=
    hselected
  refine ⟨Q', hQF, hQb, hQle, hQ, ?_⟩
  intro g g₀ c N _ ε hε hε1 hεinv
  let V₀ := Z₀.withLattice Λ l hl hlin hlout
  let := V₀.metricSpace
  let : NeZero P := ⟨Nat.ne_of_gt hP⟩
  let t := p + (p + b₀) ^ b₀ + 2
  have hp0 : 0 ≤ p := by linarith
  have hpt : p ≤ t := by
    dsimp [t]
    have hh : 0 ≤ (p + b₀) ^ b₀ := by positivity
    linarith
  have ht : 0 ≤ t := hp0.trans hpt
  have hcostt : cost + 2 ≤ t := by dsimp [t]; linarith
  have hcostt' : cost ≤ t := by linarith
  have htotal : t + (t + J) ^ J ≤ (p + C) ^ C := by
    exact hbudget p hp0
  have hcomplex : (t + J) ^ J ≤ (p + C) ^ C := by linarith
  have htC : t ≤ (p + C) ^ C := by
    have hh : 0 ≤ (t + J) ^ J := by positivity
    linarith
  have hmetric : cost + (t + B₀) ^ B₀ + 10 ≤ (p + B) ^ B := by
    have hh : (p + b₀) ^ b₀ + (t + B₀) ^ B₀ + 10 ≤ (p + B) ^ B := by
      exact hmetricBudget p hp0
    linarith
  have hpart := hpartition D b v hF M hM hin hout E D₀ Λ l hl hlin hlout g g₀ c P N
      (hp.trans hpt) (hι.trans hpt) (hκ.trans hpt) (fun i => (hD i).mono _ hpt)
      (fun i => (hV i).mono _ hpt) (fun i j k => (hb i j k).trans hpt)
      (fun j => (hE j).mono _ hpt) (hV₀.mono V₀ hcostt')
      (hPb.trans (Real.exp_le_exp.mpr hcostt')) hε hε1
      (hεinv.trans (Real.exp_le_exp.mpr
        (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ p + 2) (by linarith) a)))
  let I : Type := Classical.choose hpart
  have hpartI := Classical.choose_spec hpart
  let inst : Fintype I := Classical.choose hpartI
  have hpartInst := Classical.choose_spec hpartI
  obtain ⟨hcount, A, label, hA, hsum, hres, hcircle, hshifts⟩ := hpartInst
  let := inst
  refine ⟨I, inst, hcount.trans (Real.exp_le_exp.mpr hcomplex), A,
    fun i => (hA i).mono le_rfl hcomplex, hsum, hcircle, ?_⟩
  intro J₀ freq hfreq S hS hpositive hinvariant Hsh gT branch η γ rSq qSq
    horbit hother hγ hη hnorm hqSq slow middle rat δ hδ hfactor hslow hrat hcoeff hzero
  have hinput (i j : I) (h : ZMod N) (hh : h ∈ Hsh) (x y : ZMod N)
      (hx : x ∉ cyclicWrapExceptional h ε) (hy : y ∉ cyclicWrapExceptional h ε)
      (hAx : 0 < A i x * A j (x + h)) (hAy : 0 < A i y * A j (y + h)) :
      dist (V₀.cyclicOrbitPoint (piRealOrbit (fun i : I₀ => (T i.val).filtration)
        (fun i : I₀ => gT h i.val)) N (fun _ : Unit => x))
        (V₀.cyclicOrbitPoint (piRealOrbit (fun i : I₀ => (T i.val).filtration)
          (fun i : I₀ => gT h i.val)) N (fun _ : Unit => y)) ≤ Real.exp ((t + B₀) ^ B₀) * ε := by
    have hgo : (fun i : I₀ => gT h i.val) = optionComplementOrbits D₀ Z (sumOrbits E Q g (qSq h)) := by
      funext i
      rcases i with ⟨i, hi⟩
      cases i with
      | none => exact False.elim (hi rfl)
      | some i => exact hother h hh i
    rw [hgo]
    apply hshifts h (branch h) (η h) (γ h) (rSq h) (qSq h) (hγ h hh) _
      (hnorm h hh) (hqSq h hh) i j x y hx hy hAx hAy
    intro i k
    exact (hη h hh i k).trans (Real.exp_le_exp.mpr
      (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ p + 2) (by linarith) k₀))
  have hAnonneg (i x) : 0 ≤ A i x := ((hA i).unit_interval x).1
  have hexp := hbase (J₀ := J₀) freq hfreq N (I := I) (J := I) A A label
    (ρ := ε) (K := Real.exp ((t + B₀) ^ B₀)) hε (Real.exp_pos _).le hAnonneg hAnonneg hsum hsum hres hcircle
      S hS hpositive hinvariant Hsh gT horbit slow middle rat δ hδ hfactor hslow hrat hcoeff hzero hinput
  let U := Classical.choose hexp
  have hUdata := Classical.choose_spec hexp
  obtain ⟨hU, hUc, hUempty, err, heval, hmean⟩ := hUdata
  refine ⟨U, hU, fun i j h => (hUc i j h).mono (hcostt.trans htC), hUempty, err, heval, ?_⟩
  intro h
  have herr := refiltered_expansion_error_budget hcost
    (by positivity : 0 ≤ (t + B₀) ^ B₀) hε.le hmetric
  linarith [hmean h]

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FactoredPositiveShiftContradiction
namespace OAI


namespace Erdos3

theorem partition_expansion_precision_properties {p : ℝ} (hp : 0 ≤ p) (a : ℕ) :
    0 < Real.exp (-((p + 2) ^ a)) ∧ Real.exp (-((p + 2) ^ a)) ≤ 1 ∧
      1 / Real.exp (-((p + 2) ^ a)) = Real.exp ((p + 2) ^ a) := by
  refine ⟨Real.exp_pos _, ?_, ?_⟩
  · exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (pow_nonneg (by linarith) _))
  · simp only [one_div, Real.exp_neg, inv_inv]

end Erdos3


namespace Erdos3.RationalFilteredNilmanifold

theorem exists_prescribed_partition_expansion (s r b₀ : ℕ) :
    ∃ B : ℕ, 2 ≤ B ∧ ∀ k₀ a : ℕ, ∃ C : ℕ, 2 ≤ C ∧
      PrescribedPartitionExpansionSpec s r b₀ k₀ a B C := by
  obtain ⟨B₀, _, hpartition⟩ := exists_prescribed_complement_input_partition_s2 (s + 1)
  let X : Polynomial ℕ := Polynomial.X
  let R₀ := (X + Polynomial.C b₀) ^ b₀
  let T₀ := X + R₀ + 2
  obtain ⟨B, hB, hmetricBudget⟩ :=
    exists_natPolynomial_eval_budget (R₀ + (T₀ + Polynomial.C B₀) ^ B₀ + 10)
  refine ⟨B, hB, ?_⟩
  intro k₀ a
  obtain ⟨J, _, hpartition⟩ := hpartition k₀ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T₀ + (T₀ + Polynomial.C J) ^ J)
  refine ⟨C, hC, prescribed_partition_expansion_from_partition s r b₀ k₀ a B C B₀ J hpartition ?_ ?_⟩
  · intro p hp
    simpa [R₀, T₀, X, Polynomial.eval₂_pow] using hbudget p hp
  · intro p hp
    simpa [R₀, T₀, X, Polynomial.eval₂_pow] using hmetricBudget p hp

end Erdos3.RationalFilteredNilmanifold


namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct BigOperators

attribute [local instance_reducible] optionLieSpace

theorem exists_prepared_higher_shift_contradiction (s r b₀ k₀ k c : ℕ) (hc : 2 ≤ c)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hshift : CyclicShiftComparison.{0} (s + 1) (epsilon / 2) c) :
    ∃ Dexp : ℕ, 2 ≤ Dexp ∧ PreparedHigherShiftContradictionSpec s r b₀ k₀ k Dexp epsilon := by
  obtain ⟨B, _, hpartition⟩ := exists_prescribed_partition_expansion s r b₀
  obtain ⟨a, _, hcontra⟩ := exists_native_partition_expansion_contradiction_s2.{0, 0}
    B k c s hc hepsilon hepsilon1 hshift
  obtain ⟨C, _, hpartition⟩ := hpartition k₀ a
  obtain ⟨Dexp, hDexp, _, hcontra⟩ := hcontra C
  refine ⟨Dexp, hDexp, ?_⟩
  dsimp only [PreparedHigherShiftContradictionSpec]
  intro ι κ _ _ _ _ L _ _ d m _ _ _ _ K _ _ e _ _ _ _ D _ _ _ _ _ _ _ _
    b v hF M hM hin hout E L₀ _ _ d₀ D₀ W dR dQ R Q₀ _ _ _ _ p cost q
    hp hι hκ hD hV hb hE hcost hcostb hbase g g₀ anchor N _ hodd hN
    f₁ f₂ weight sigma delta hsigma hdelta hf₁ hf₂ hweight J₀ freq hfreq S hS hpositive hinvariant
    Hsh gT branch η γ rSq qSq horbit hother hγ hη hnorm hqSq slow middle rat ζ
    hζ hfactor hslow hrat hcoeff hzero hH hcompare hviolate
  classical
  let Q := fun i => (D i).filtration.squareFiltration.topQuotientModel
    ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) (squareFinWeight (v i))
    ((D i).filtration.squareFinBasis_layers (b i) (v i) (hF i))
    ((D i).filtration.squareLattice (D i).lattice) (M i) (hM i) (hin i) (hout i)
  let Z := sumFactors E Q
  let T := optionFactors D₀ Z
  let H := (pi T).filtration.gradedRefiltrationSubalgebra W
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (H ⧸ R.filtration.layerIdeal (s + 1)))
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (H ⧸ R.filtration.layerIdeal (s + 1)))
  let := realification_moduleTopology_t2 Q₀.basis
  have hdata := hpartition D b v hF M hM hin hout E D₀ W R Q₀ q
    hp hι hκ hD hV hb hE hcost hcostb hbase
  let Q' := Classical.choose hdata
  have hQdata := Classical.choose_spec hdata
  obtain ⟨_, _, _, _, hpart⟩ := hQdata
  have hp0 : 0 ≤ p := by linarith
  obtain ⟨hρ, hρ1, hρinv⟩ := partition_expansion_precision_properties hp0 a
  have hpartData := hpart g g₀ anchor N hρ hρ1 (le_of_eq hρinv)
  let I : Type := Classical.choose hpartData
  have hpartI := Classical.choose_spec hpartData
  let inst : Fintype I := Classical.choose hpartI
  have hpartInst := Classical.choose_spec hpartI
  obtain ⟨hcount, A, hA, _, _, hexp⟩ := hpartInst
  let := inst
  have hexpData := hexp freq hfreq S hS hpositive hinvariant (↑Hsh : Set (ZMod N))
    gT branch η γ rSq qSq horbit hother hγ hη hnorm hqSq
    slow middle rat ζ hζ hfactor hslow hrat hcoeff hzero
  let U := Classical.choose hexpData
  have hUdata := Classical.choose_spec hexpData
  obtain ⟨hU, hUc, _, err, heval, hmean⟩ := hUdata
  exact hcontra (T none) Q' N p sigma delta f₁ f₂ weight A Hsh U S err
    hp hodd hN hcount hsigma hdelta hf₁ hf₂ hweight hA hU hUc hH
    (fun h _ => hpositive h) heval (fun h _ => hmean h) @hcompare hviolate

end Erdos3.RationalFilteredNilmanifold


namespace Erdos3.PositiveShiftBasis

open Module RationalFilteredNilmanifold NilpotentLieFiltration
open scoped TensorProduct BigOperators

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff
attribute [local instance_reducible] optionLieSpace

theorem exists_factored_positive_shift_contradiction_s2_oai (s c : ℕ) (hc : 2 ≤ c)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hshift : CyclicShiftComparison.{0} (s + 1) (epsilon / 2) c) :
    ∃ Dexp : ℕ, 2 ≤ Dexp ∧ FactoredPositiveShiftContradictionSpec s Dexp epsilon := by
  classical
  obtain ⟨C, _, hmodels⟩ := exists_common_refiltered_expansion_s2 s 1
  obtain ⟨Dexp, hDexp, hcontra⟩ :=
    exists_prepared_higher_shift_contradiction s 1 C 1 1 c hc hepsilon hepsilon1 hshift
  refine ⟨Dexp, hDexp, ?_⟩
  dsimp only [FactoredPositiveShiftContradictionSpec]
  intro N _ q f₁ f₂ weight B L M _ _ _ _ d e _ _ _ _ _ _ _ _ D E _ _ _ _ _ _ _ _ Y A R
    anchor H p F hH hp hqp hD hE hYfull hYquot hYheight g₀ branches η γ rSq hγ hη hnorm horbit
    hodd hN hf₁ hf₂ hweight hcompare
  let t := productExpansionBudget p
  let Q := fun j => (Y j).quotientModel
  let T := B.anchoredFactors D Q
  let fixed := optionFactors B.model D
  have hp0 : 0 ≤ p := by linarith
  obtain ⟨ht, hpt, _⟩ := productExpansionBudget_bounds hp0
  have hpt' : p ≤ t + 2 := by dsimp [t]; linarith
  obtain ⟨U, _, _, _, n, _, Q₀, _, _, _, _, cost, hcost, hcostb, hexp⟩ :=
    hmodels B D Q A R anchor H F hp hqp hD hYquot
  obtain ⟨S, hSsame, hS, hpositive, hinvariant⟩ := F.exists_test_extension hH hqp
  obtain ⟨κ, slow, middle, rat, hκ, hfactor, hslow, hrat, hzero, hcoeff⟩ := F.exists_factor_family
  let g : ∀ i, (fixed i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1)
    | none => (B.test anchor).orbit
    | some j => (A j).orbit
  let gT (h : ZMod N) : ∀ i, (T i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1) :=
    fun i => (anchoredOptionReferenceData (D := T) (B.test h) (B.test anchor) A (R h) i).orbit
  let branch (_h : ZMod N) (j : Fin B.count) : Fin 2 := if (branches j).1 then 1 else 0
  have hbranch (h : ZMod N) (j) :
      (h.val : ℤ) - ((branch h j).val : ℤ) * N = cyclicBranchOffset h (branches j).1 := by
    cases hb : (branches j).1 <;> simp [branch, cyclicBranchOffset, hb]
  have hcurrent (h) (hh : h ∈ F.shifts) : gT h none = (S h).orbit := by
    rw [hSsame h hh]
    rfl
  have hother (h) (_hh : h ∈ F.shifts) (i) :
      gT h (some i) = sumOrbits fixed Q g (fun j => (R h j).orbit) i := by
    rcases i with (_ | j) | j <;> rfl
  have hnormal (h) (hh : h ∈ F.shifts) (j) (x : Unit → ℤ) :
      (E j).filtration.realSquareFstHom
        ((E j).filtration.squareFiltration.realification.polynomialOrbitEval
          (fun _ => 1) x (rSq h j)) =
          (η h j)⁻¹ * (E j).filtration.realification.polynomialOrbitEval (fun _ => 1)
            (x + fun _ => (h.val : ℤ) - ((branch h j).val : ℤ) * N) (g₀ j) * (γ h j)⁻¹ ∧
      (E j).filtration.realSquareSndHom
        ((E j).filtration.squareFiltration.realification.polynomialOrbitEval
          (fun _ => 1) x (rSq h j)) =
          (E j).filtration.realification.polynomialOrbitEval (fun _ => 1)
            (x + fun _ => cyclicBranchOffset anchor (branches j).2) (g₀ j) := by
    simpa only [hbranch] using hnorm h hh j x
  have hslow' (h) (hh : h ∈ F.shifts) :
      (pi T).filtration.PolynomialSlowBound (pi T).basis (fun _ : Unit => 1)
        (fun _ => (N : ℝ)) (Real.exp ((t + 2) ^ 1)) (slow h) := by
    apply (pi T).filtration.polynomialSlowBound_mono (pi T).basis (fun _ : Unit => 1)
      (fun _ => (N : ℝ)) (fun _ => by exact_mod_cast NeZero.pos N)
      (Real.exp_le_exp.mpr (by simpa only [pow_one] using hpt')) (slow h)
    exact hslow h hh
  have hcount : (B.count : ℝ) ≤ p :=
    (Nat.cast_le.mpr B.count_le_dim).trans (B.geometry.1.trans hqp)
  have hcount' : (Fintype.card (Fin B.count) : ℝ) ≤ t := by
    simpa only [Fintype.card_fin] using hcount.trans hpt
  have hfixedCount : (Fintype.card (Option (Fin B.count)) : ℝ) ≤ t := by
    simp only [Fintype.card_option, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
    dsimp [t, productExpansionBudget]
    nlinarith [sq_nonneg (2 * p + 4)]
  have hfixed (i) : (fixed i).GeometryComplexityLE t := by
    rcases i with _ | j
    · exact B.geometry.mono B.model (hqp.trans hpt)
    · exact (hD j).mono (D j) hpt
  have hdensity : Real.exp (-((t + 2) ^ 1)) ≤ Real.exp (-p) := by
    exact Real.exp_le_exp.mpr (by simpa only [pow_one] using neg_le_neg hpt')
  have hdelta : Real.exp (-((t + 2) ^ 1)) ≤ Real.exp (-q) := by
    exact Real.exp_le_exp.mpr (by simpa only [pow_one] using neg_le_neg (hqp.trans hpt'))
  have hviolation (h) (hh : h ∈ F.shifts) : Real.exp (-q) <
      𝔼 n, (f₁ n - (1 + epsilon) * f₂ n) * weight (n + h) *
        ((S h).evalCyclic N (fun _ => n)).re := by
    rw [hSsame h hh]
    exact B.test_violation h (hH (F.shifts_sub hh))
  exact hcontra E (fun j => (Y j).basis) (fun j => (Y j).weight) (fun j => (Y j).layers)
    (fun j => (Y j).grid) (fun j => (Y j).grid_pos) (fun j => (Y j).inner) (fun j => (Y j).outer)
    fixed B.model F.subalgebra U Q₀ F.denominator ht hcount' hfixedCount
    (fun j => (hE j).mono (E j) hpt) (fun j => (hYfull j).mono (Y j).fullModel hpt)
    (fun j i k => (hYheight j i k).trans hpt) hfixed hcost hcostb hexp
    g g₀ (fun j => cyclicBranchOffset anchor (branches j).2) N hodd hN
    f₁ f₂ weight (Real.exp (-p)) (Real.exp (-q)) hdensity hdelta
    (fun n => ⟨(hf₁ n).1, (hf₁ n).2.trans (Real.exp_le_exp.mpr hpt)⟩)
    (fun n => ⟨(hf₂ n).1, (hf₂ n).2.trans (Real.exp_le_exp.mpr hpt)⟩)
    (fun n => ⟨(hweight n).1, (hweight n).2.trans (Real.exp_le_exp.mpr hpt)⟩)
    F.frequency F.frequency_zero S (fun h => (hS h).mono hpt) hpositive hinvariant
    F.shifts gT branch η γ rSq (fun h j => (R h j).orbit) hcurrent hother hγ
    (fun h hh j i => (hη h hh j i).trans (Real.exp_le_exp.mpr (by simpa only [pow_one] using hpt')))
    hnormal horbit slow middle rat κ hκ hfactor hslow' hrat hcoeff hzero
    F.shifts_large hcompare hviolation

end Erdos3.PositiveShiftBasis

end OAI
end

theorem solution : type_of% @OAI.Erdos3.PositiveShiftBasis.exists_factored_positive_shift_contradiction_s2_oai := @OAI.Erdos3.PositiveShiftBasis.exists_factored_positive_shift_contradiction_s2_oai
