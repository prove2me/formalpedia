-- Prove2me | solution 1 for OAI.BinaryCoordinateSweeps.constant_sweep_mixing
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T15:58:38.55049+00:00
-- url     : https://prove2.me/submissions/f34646c2-6499-4758-96b2-051b95f00d01

import Mathlib
import Definitions.Def_BinarySweep
import Definitions.Def_OAIB3Bs000
import Theorems.Thm_OAI_BinaryCoordinateSweeps_real_grid_bound

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Processes_Basic
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps

section FiniteProbability
variable {Ω G : Type*} [Fintype Ω] [Fintype G]

lemma finiteLaw_nonneg (f : Ω → G) (g : G) : 0 ≤ finiteLaw f g := by
  classical
  exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)

lemma finiteLaw_sum [Nonempty Ω] (f : Ω → G) : ∑ g, finiteLaw f g = 1 := by
  classical
  simp only [finiteLaw]
  rw [Finset.sum_comm]
  simp [Fintype.card_ne_zero]

lemma uniformLaw_sum [Nonempty G] : ∑ g, uniformLaw G g = 1 := by
  simp [uniformLaw, Fintype.card_ne_zero]

end FiniteProbability

end BinaryCoordinateSweeps
end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Processes_SupportTimeBoundBounds
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps

lemma sign_boolSwitch (c : Bool) :
    Equiv.Perm.sign (boolSwitch c) = if c then (-1 : ℤˣ) else 1 := by
  cases c
  · have : boolSwitch false = 1 := by ext x; cases x <;> rfl
    rw [this]; rfl
  · have : boolSwitch true = Equiv.swap false true := by
      ext x; cases x <;> simp [boolSwitch]
    rw [this, Equiv.Perm.sign_swap (by decide)]; rfl

lemma realSign_coordinateLayer (d : ℕ) (j : Fin d)
    (c : ({i : Fin d // i ≠ j} → Bool) → Bool) :
    realSign (coordinateLayer d j c) = ∏ y, (if c y then (-1 : ℝ) else 1) := by
  classical
  have he : coordinateLayer d j c =
      (Equiv.piSplitAt j (fun _ : Fin d => Bool)).trans
        ((Equiv.prodCongrLeft (fun y => boolSwitch (c y))).trans
          (Equiv.piSplitAt j (fun _ : Fin d => Bool)).symm) := rfl
  rw [he]
  simp [realSign, Equiv.Perm.sign_prodCongrLeft, sign_boolSwitch, apply_ite]

lemma sum_realSign_coordinateLayer (d : ℕ) (j : Fin d) :
    ∑ c : ({i : Fin d // i ≠ j} → Bool) → Bool,
      realSign (coordinateLayer d j c) = 0 := by
  classical
  simp_rw [realSign_coordinateLayer]
  rw [← Fintype.prod_sum (fun (_ : {i : Fin d // i ≠ j} → Bool) (b : Bool) =>
    if b then (-1 : ℝ) else 1)]
  simp

lemma realSign_binarySweep (d : ℕ) (c : SweepCoins d) :
    realSign (binarySweep d c) = ∏ j, realSign (coordinateLayer d j (c j)) := by
  classical
  simp [binarySweep, map_list_prod, List.map_reverse, List.prod_reverse,
    List.map_ofFn, List.prod_ofFn]

lemma sum_realSign_binarySweep (d : ℕ) (hd : 0 < d) :
    ∑ c : SweepCoins d, realSign (binarySweep d c) = 0 := by
  classical
  simp_rw [realSign_binarySweep]
  rw [← Fintype.prod_sum (fun (j : Fin d) (c : ({i : Fin d // i ≠ j} → Bool) → Bool) =>
    realSign (coordinateLayer d j c))]
  apply Finset.prod_eq_zero (i := ⟨0, hd⟩) (Finset.mem_univ _)
  exact sum_realSign_coordinateLayer d ⟨0, hd⟩

lemma finiteLaw_expectation {Ω G : Type*} [Fintype Ω] [Fintype G]
    (f : Ω → G) (a : G → ℝ) :
    ∑ g, finiteLaw f g * a g = (Fintype.card Ω : ℝ)⁻¹ * ∑ ω, a (f ω) := by
  classical
  simp only [finiteLaw, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [ite_mul, Finset.mul_sum]

theorem binary_sign_annihilated (d : ℕ) (hd : 0 < d) :
    ∑ g : Equiv.Perm (Slot d), binaryLaw d g * realSign g = 0 := by
  rw [binaryLaw, finiteLaw_expectation, sum_realSign_binarySweep d hd, mul_zero]

lemma coordinateLayer_zero (d : ℕ) (j : Fin d) :
    coordinateLayer d j (fun _ => false) = 1 := by
  ext x i
  simp [coordinateLayer, Equiv.piSplitAt_symm_apply]
  intro h
  rw [h]

lemma prod_reverse_ofFn_single {G : Type*} [Monoid G] (n : ℕ) (j : Fin n) (g : G) :
    (List.ofFn (fun i : Fin n => if i = j then g else 1)).reverse.prod = g := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [List.ofFn_succ, List.ofFn_const]
    · simpa [List.ofFn_succ, (Fin.succ_ne_zero j).symm] using ih j

lemma binarySweep_zero (d : ℕ) : binarySweep d (fun _ _ => false) = 1 := by
  simp [binarySweep, coordinateLayer_zero, List.ofFn_const]

lemma binarySweep_singleLayer (d : ℕ) (j : Fin d)
    (c : ({i : Fin d // i ≠ j} → Bool) → Bool) :
    binarySweep d (Function.update ((fun _ _ => false) : SweepCoins d) j c) = coordinateLayer d j c := by
  classical
  have h (i : Fin d) :
      coordinateLayer d i ((Function.update ((fun _ _ => false) : SweepCoins d) j c) i) =
      if i = j then coordinateLayer d j c else 1 := by
    by_cases hi : i = j
    · subst i; simp
    · simp [coordinateLayer_zero, hi]
  simp only [binarySweep, h]
  exact prod_reverse_ofFn_single d j _

lemma coordinateLayer_mem_reachable (d : ℕ) (j : Fin d)
    (c : ({i : Fin d // i ≠ j} → Bool) → Bool) :
    coordinateLayer d j c ∈ sweepReachable d := by
  refine ⟨[Function.update ((fun _ _ => false) : SweepCoins d) j c], ?_⟩
  simp [binarySweep_singleLayer]

lemma fiber_boolSwitch_eq_swap {Y : Type*} [DecidableEq Y] (y : Y) (a : Bool) :
    Equiv.prodCongrLeft (fun z => boolSwitch (decide (z = y))) =
      Equiv.swap (a, y) (!a, y) := by
  ext ⟨b, z⟩ <;> cases a <;> cases b <;> by_cases h : z = y <;>
    simp [boolSwitch, Equiv.swap_apply_def, h]

end BinaryCoordinateSweeps
end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Processes_CoordinateLayerEdgeSwap
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps

lemma coordinateLayer_edgeSwap (d : ℕ) (j : Fin d) (x : Slot d) :
    coordinateLayer d j (fun y => decide (y = fun i : {i : Fin d // i ≠ j} => x i)) =
      Equiv.swap x (Function.update x j (!x j)) := by
  classical
  let e := Equiv.piSplitAt j (fun _ : Fin d => Bool)
  let z : {i : Fin d // i ≠ j} → Bool := fun i => x i
  change (e.trans (Equiv.prodCongrLeft (fun y => boolSwitch (decide (y = z))))).trans e.symm = _
  rw [fiber_boolSwitch_eq_swap z (x j), Equiv.trans_swap_trans_symm]
  have hx : e.symm (x j, z) = x := by
    exact e.symm_apply_apply x
  have hy : e.symm (!x j, z) = Function.update x j (!x j) := by
    ext i
    by_cases h : i = j
    · subst i; simp [e, Equiv.piSplitAt_symm_apply]
    · simp [e, z, Equiv.piSplitAt_symm_apply, h]
  rw [hx, hy]

lemma swap_update_mem_reachable (d : ℕ) (j : Fin d) (x : Slot d) (b : Bool) :
    Equiv.swap x (Function.update x j b) ∈ sweepReachable d := by
  classical
  by_cases h : b = x j
  · subst b
    simp only [Function.update_eq_self, Equiv.swap_self]
    exact (sweepReachable d).one_mem
  · have hb : b = !x j := by cases b <;> cases hx : x j <;> simp_all
    rw [hb, ← coordinateLayer_edgeSwap]
    exact coordinateLayer_mem_reachable d j _

lemma swap_mem_sweepReachable (d : ℕ) (x y : Slot d) :
    Equiv.swap x y ∈ sweepReachable d := by
  classical
  have h (s : Finset (Fin d)) :
      Equiv.swap x (fun i => if i ∈ s then y i else x i) ∈ sweepReachable d := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.notMem_empty, ite_false, Equiv.swap_self]
      exact (sweepReachable d).one_mem
    | @insert j s hj ih =>
      have he : (fun i => if i ∈ insert j s then y i else x i) =
          Function.update (fun i => if i ∈ s then y i else x i) j (y j) := by
        ext i
        by_cases hi : i = j
        · subst i; simp
        · simp [hi]
      rw [he]
      exact SubmonoidClass.swap_mem_trans (sweepReachable d) ih
        (swap_update_mem_reachable d j _ _)
  simpa using h Finset.univ

theorem every_permutation_sweepReachable (d : ℕ) (g : Equiv.Perm (Slot d)) :
    g ∈ sweepReachable d := by
  classical
  induction g using Equiv.Perm.swap_induction_on with
  | one => exact (sweepReachable d).one_mem
  | swap_mul g x y h ih =>
    exact (sweepReachable d).mul_mem (swap_mem_sweepReachable d x y) ih

section FiniteRandomWalk
variable {G : Type*} [Fintype G] [Group G]

lemma sum_mulLeft (a : G) (f : G → ℝ) : ∑ g, f (a * g) = ∑ g, f g :=
  Equiv.sum_comp (Equiv.mulLeft a) f

lemma sum_inv_mulRight (a : G) (f : G → ℝ) : ∑ g, f (g⁻¹ * a) = ∑ g, f g :=
  ((Equiv.inv G).trans (Equiv.mulRight a)).sum_comp f

lemma convolution_sum (p q : G → ℝ) :
    ∑ g, convolution p q g = (∑ g, p g) * (∑ g, q g) := by
  simp only [convolution]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_mulLeft]
  rw [Finset.sum_mul]

lemma convolution_nonneg {p q : G → ℝ} (hp : ∀ g, 0 ≤ p g) (hq : ∀ g, 0 ≤ q g) :
    ∀ g, 0 ≤ convolution p q g := fun _ =>
  Finset.sum_nonneg (fun x _ => mul_nonneg (hp x) (hq _))

lemma convolution_probability {p q : G → ℝ} (hp : IsProbability p) (hq : IsProbability q) :
    IsProbability (convolution p q) := by
  exact ⟨convolution_nonneg hp.1 hq.1, by rw [convolution_sum, hp.2, hq.2, one_mul]⟩

lemma convolution_uniform_right {p : G → ℝ} (hp : ∑ g, p g = 1) :
    convolution p (uniformLaw G) = uniformLaw G := by
  funext g
  simp [convolution, uniformLaw, ← Finset.sum_mul, hp]

lemma convolution_uniform_left {p : G → ℝ} (hp : ∑ g, p g = 1) :
    convolution (uniformLaw G) p = uniformLaw G := by
  funext g
  simp [convolution, uniformLaw, ← Finset.mul_sum, sum_inv_mulRight, hp]

lemma convolution_assoc (p q r : G → ℝ) :
    convolution (convolution p q) r = convolution p (convolution q r) := by
  funext g
  simp only [convolution, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [← sum_mulLeft x (fun y => p x * q (x⁻¹ * y) * r (y⁻¹ * g))]
  simp [mul_assoc]

omit [Group G] in
lemma totalVariation_nonneg (p q : G → ℝ) : 0 ≤ totalVariation p q :=
  mul_nonneg (by norm_num) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))

omit [Group G] in
lemma totalVariation_le_one {p q : G → ℝ} (hp : IsProbability p) (hq : IsProbability q) :
    totalVariation p q ≤ 1 := by
  have h : ∑ g, |p g - q g| ≤ 2 := by
    calc
      _ ≤ ∑ g, (p g + q g) := Finset.sum_le_sum (fun g _ =>
        (abs_sub (p g) (q g)).trans_eq (by rw [abs_of_nonneg (hp.1 g), abs_of_nonneg (hq.1 g)]))
      _ = 2 := by rw [Finset.sum_add_distrib, hp.2, hq.2]; norm_num
  unfold totalVariation
  linarith

lemma convolution_tv_contract {p : G → ℝ} (hp : ∀ g, 0 ≤ p g) (q r : G → ℝ) :
    totalVariation (convolution p q) (convolution p r) ≤
      (∑ g, p g) * totalVariation q r := by
  have h : ∑ g, |convolution p q g - convolution p r g| ≤
      (∑ g, p g) * ∑ g, |q g - r g| := by
    calc
      _ = ∑ g, |∑ x, p x * (q (x⁻¹ * g) - r (x⁻¹ * g))| := by
        simp_rw [convolution, ← Finset.sum_sub_distrib, ← mul_sub]
      _ ≤ ∑ g, ∑ x, p x * |q (x⁻¹ * g) - r (x⁻¹ * g)| := by
        apply Finset.sum_le_sum
        intro g _
        simpa only [abs_mul, abs_of_nonneg (hp _)] using
          (Finset.abs_sum_le_sum_abs (s := Finset.univ)
            (f := fun x => p x * (q (x⁻¹ * g) - r (x⁻¹ * g))))
      _ = _ := by
        rw [Finset.sum_comm]
        have hs (x : G) : ∑ g, |q (x⁻¹ * g) - r (x⁻¹ * g)| = ∑ g, |q g - r g| :=
          sum_mulLeft x⁻¹ (fun g => |q g - r g|)
        simp_rw [← Finset.mul_sum, hs]
        rw [Finset.sum_mul]
  unfold totalVariation
  nlinarith

end FiniteRandomWalk

end BinaryCoordinateSweeps
end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Representations_MultiplicityBound
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators MonoidAlgebra Classical TensorProduct

namespace BinaryCoordinateSweeps.Irrep
open Representation

variable {G V W : Type*} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  (ρ : Representation ℂ G V) (σ : Representation ℂ G W)

omit [Fintype G] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
lemma isotypicSpan_stable (g : G) (w : W) (hw : w ∈ isotypicSpan ρ σ) :
    σ g w ∈ isotypicSpan ρ σ := by
  apply Submodule.iSup_induction (fun f : IntertwiningMap ρ σ => LinearMap.range f.toLinearMap)
    (motive := fun w => σ g w ∈ isotypicSpan ρ σ) hw
  · intro f x hx
    obtain ⟨v,rfl⟩ := hx
    change σ g (f v) ∈ isotypicSpan ρ σ
    rw [← IntertwiningMap.isIntertwining ρ σ f g v]
    exact (le_iSup (fun f : IntertwiningMap ρ σ => LinearMap.range f.toLinearMap) f)
      ⟨ρ g v,rfl⟩
  · simpa only [map_zero] using (isotypicSpan ρ σ).zero_mem
  · intro x y hx hy
    simpa only [map_add] using (isotypicSpan ρ σ).add_mem hx hy

omit [Fintype G] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
lemma isotypicSpan_map (g : G) : (isotypicSpan ρ σ).map (σ g) = isotypicSpan ρ σ := by
  apply le_antisymm
  · rintro _ ⟨w,hw,rfl⟩
    exact isotypicSpan_stable ρ σ g w hw
  · intro w hw
    refine ⟨σ g⁻¹ w, isotypicSpan_stable ρ σ g⁻¹ w hw, ?_⟩
    simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

end BinaryCoordinateSweeps.Irrep

end

open scoped BigOperators Classical TensorProduct

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Representations_IsotypicTrace
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical TensorProduct

namespace BinaryCoordinateSweeps.Irrep
open Representation

variable {G V W : Type*} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [ρ.IsIrreducible]

theorem isotypic_trace (A : V →ₗ[ℂ] V) (B : W →ₗ[ℂ] W)
    (hAB : ∀ f : IntertwiningMap ρ σ, ∀ v : V, B (f v) = f (A v)) :
    LinearMap.trace ℂ (isotypicSpan ρ σ)
      (B.restrict (isotypic_invariant_of_compatible ρ σ A B hAB)) =
    (Module.finrank ℂ (IntertwiningMap ρ σ) : ℂ) * LinearMap.trace ℂ V A := by
  let e := evaluationEquiv ρ σ
  let C := B.restrict (isotypic_invariant_of_compatible ρ σ A B hAB)
  have he : e.symm.conj C = TensorProduct.map A (LinearMap.id :
      IntertwiningMap ρ σ →ₗ[ℂ] IntertwiningMap ρ σ) := by
    apply TensorProduct.ext'
    intro v f
    apply e.injective
    change e (e.symm (C (e (v ⊗ₜ[ℂ] f)))) = e (A v ⊗ₜ[ℂ] f)
    rw [e.apply_symm_apply]
    apply Subtype.ext
    exact hAB f v
  have ht := LinearMap.trace_conj' C e.symm
  rw [he,LinearMap.trace_tensorProduct',LinearMap.trace_id] at ht
  exact ht.symm.trans (mul_comm _ _)

end BinaryCoordinateSweeps.Irrep

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Representations_IsotypicMoment
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical ComplexOrder

namespace BinaryCoordinateSweeps.Irrep
open Representation

variable {G V W : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  (ρ : Representation ℂ G V) (σ : Representation ℂ G W)

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
lemma average_compatible (p : G → ℂ) (f : IntertwiningMap ρ σ) (v : V) :
    groupAverage σ p (f v) = f (groupAverage ρ p v) := by
  simp only [groupAverage,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul,
    IntertwiningMap.isIntertwining]

lemma adjoint_average_compatible (p : G → ℂ)
    (hρ : ∀ g v, ‖ρ g v‖ = ‖v‖) (hσ : ∀ g w, ‖σ g w‖ = ‖w‖)
    (f : IntertwiningMap ρ σ) (v : V) :
    (groupAverage σ p).adjoint (f v) = f ((groupAverage ρ p).adjoint v) := by
  simp only [groupAverage,map_sum,map_smulₛₗ,unitary_rep_adjoint ρ hρ,
    unitary_rep_adjoint σ hσ,LinearMap.sum_apply,LinearMap.smul_apply,
    IntertwiningMap.isIntertwining, RingHom.id_apply]

lemma even_compatible (p : G → ℂ)
    (hρ : ∀ g v, ‖ρ g v‖ = ‖v‖) (hσ : ∀ g w, ‖σ g w‖ = ‖w‖)
    (q : ℕ) (f : IntertwiningMap ρ σ) (v : V) :
    (((groupAverage σ p).adjoint * groupAverage σ p)^q) (f v) =
      f ((((groupAverage ρ p).adjoint * groupAverage ρ p)^q) v) := by
  induction q generalizing v with
  | zero => simp
  | succ q ih =>
    rw [pow_succ',pow_succ',Module.End.mul_apply,Module.End.mul_apply,ih]
    rw [Module.End.mul_apply,average_compatible,adjoint_average_compatible ρ σ p hρ hσ]
    rfl

end BinaryCoordinateSweeps.Irrep

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Representations_FiniteUnitaryAverage
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
variable {G V : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

lemma complexAverage_apply (ρ : Representation ℂ G V) (p : G → ℂ) (v : V) :
    complexAverage ρ p v = ∑ g, p g • ρ g v := by
  simp [complexAverage,Irrep.groupAverage]

lemma complexAverage_norm_apply (ρ : Representation ℂ G V)
    (hρ : ∀ g v, ‖ρ g v‖=‖v‖) (p : G → ℂ) (v : V) :
    ‖complexAverage ρ p v‖ ≤ (∑g, ‖p g‖)*‖v‖ := by
  rw [complexAverage_apply,Finset.sum_mul]
  exact (norm_sum_le _ _).trans_eq (by simp [norm_smul,hρ])

lemma realAverage_contraction (ρ : Representation ℂ G V)
    (hρ : ∀ g v, ‖ρ g v‖=‖v‖) {p : G → ℝ} (hp : IsProbability p) (v : V) :
    ‖complexAverage ρ (fun g => (p g:ℂ)) v‖ ≤ ‖v‖ := by
  have he : (∑g, ‖(p g:ℂ)‖)=1 := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hp.1 _)] using hp.2
  simpa only [he,one_mul] using complexAverage_norm_apply ρ hρ (fun g => (p g:ℂ)) v

lemma complexAverage_sub (ρ : Representation ℂ G V) (p q : G → ℂ) :
    complexAverage ρ (fun g => p g-q g)=complexAverage ρ p-complexAverage ρ q := by
  ext v
  simp [complexAverage_apply,sub_smul,Finset.sum_sub_distrib]

lemma complexAverage_convolution (ρ : Representation ℂ G V) (p q : G → ℝ) :
    complexAverage ρ (fun g => (convolution p q g:ℂ)) =
      complexAverage ρ (fun g => (p g:ℂ))*complexAverage ρ (fun g => (q g:ℂ)) := by
  ext v
  calc
    _ = ∑ x, ∑ y, (p x:ℂ) • (q y:ℂ) • ρ (x*y) v := by
      rw [complexAverage_apply]
      simp only [convolution,Complex.ofReal_sum,Finset.sum_smul,
        Complex.ofReal_mul,mul_smul]
      conv_lhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      simpa only [Equiv.coe_mulLeft,inv_mul_cancel_left] using
        (Equiv.sum_comp (Equiv.mulLeft x)
          (fun y => (p x:ℂ) • (q (x⁻¹*y):ℂ) • ρ y v)).symm
    _ = _ := by
      rw [mul_apply_eq_comp,complexAverage_apply]
      apply Finset.sum_congr rfl
      intro x _
      rw [complexAverage_apply,map_sum,Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro y _
      rw [map_smul,map_mul,Module.End.mul_apply]

lemma complexAverage_pointMass (ρ : Representation ℂ G V) :
    complexAverage ρ (fun g => (pointMassOne g:ℂ))=1 := by
  ext v
  simp [complexAverage_apply,pointMassOne]

lemma complexAverage_power (ρ : Representation ℂ G V) (p : G → ℝ) (n : ℕ) :
    complexAverage ρ (fun g => (convolutionPower p n g:ℂ))=
      (complexAverage ρ (fun g => (p g:ℂ)))^n := by
  induction n with
  | zero => exact complexAverage_pointMass ρ
  | succ n ih => rw [convolutionPower,complexAverage_convolution,ih,pow_succ']

lemma complexAverage_uniform_left (ρ : Representation ℂ G V) (g : G) (v : V) :
    ρ g (complexAverage ρ (fun g => (uniformLaw G g:ℂ)) v)=
      complexAverage ρ (fun g => (uniformLaw G g:ℂ)) v := by
  simp only [complexAverage_apply,map_sum,map_smul,←Module.End.mul_apply,←map_mul,uniformLaw]
  simpa only [Equiv.coe_mulLeft,Complex.ofReal_inv] using
    Equiv.sum_comp (Equiv.mulLeft g) (fun x => ((Fintype.card G:ℝ)⁻¹:ℂ) • ρ x v)

lemma complexAverage_uniform_right (ρ : Representation ℂ G V) (g : G) (v : V) :
    complexAverage ρ (fun g => (uniformLaw G g:ℂ)) (ρ g v)=
      complexAverage ρ (fun g => (uniformLaw G g:ℂ)) v := by
  simp only [complexAverage_apply,←Module.End.mul_apply,←map_mul,uniformLaw]
  simpa only [Equiv.coe_mulRight,Complex.ofReal_inv] using
    Equiv.sum_comp (Equiv.mulRight g) (fun x => ((Fintype.card G:ℝ)⁻¹:ℂ) • ρ x v)

lemma complexAverage_uniform_idem (ρ : Representation ℂ G V) (v : V) :
    complexAverage ρ (fun g => (uniformLaw G g:ℂ))
      (complexAverage ρ (fun g => (uniformLaw G g:ℂ)) v) =
      complexAverage ρ (fun g => (uniformLaw G g:ℂ)) v := by
  rw [complexAverage_apply]
  simp only [complexAverage_uniform_left,←Finset.sum_smul,←Complex.ofReal_sum,uniformLaw_sum,
    Complex.ofReal_one,one_smul]

lemma complexAverage_uniform_inner (ρ : Representation ℂ G V)
    (hρ : ∀ g v, ‖ρ g v‖=‖v‖) (v w : V) :
    inner ℂ (complexAverage ρ (fun g => (uniformLaw G g:ℂ)) v) w =
      inner ℂ v (complexAverage ρ (fun g => (uniformLaw G g:ℂ)) w) := by
  simp only [complexAverage_apply,inner_sum,inner_smul_left, sum_inner,
    inner_smul_right,Complex.conj_ofReal]
  have he (g : G) : inner ℂ (ρ g v) w=inner ℂ v (ρ g⁻¹ w) := by
    rw [←LinearMap.adjoint_inner_right,Irrep.unitary_rep_adjoint ρ hρ]
  simp_rw [he]
  simpa only [uniformLaw,Equiv.inv_apply,Complex.ofReal_inv] using
    Equiv.sum_comp (Equiv.inv G) (fun g => ((Fintype.card G:ℝ)⁻¹:ℂ)*inner ℂ v (ρ g w))

lemma complexAverage_variance (ρ : Representation ℂ G V)
    (hρ : ∀ g v, ‖ρ g v‖=‖v‖) {p : G → ℝ} (hp : IsProbability p) (v : V) :
    ∑g, p g * ‖ρ g v-complexAverage ρ (fun g => (p g:ℂ)) v‖^2 =
      ‖v‖^2-‖complexAverage ρ (fun g => (p g:ℂ)) v‖^2 := by
  let B := complexAverage ρ (fun g => (p g:ℂ))
  have hi : ∑g, p g * (inner ℂ (ρ g v) (B v)).re=‖B v‖^2 := by
    have he : ∑g, (p g:ℂ)*inner ℂ (ρ g v) (B v)=inner ℂ (B v) (B v) := by
      rw [show B v=∑g, (p g:ℂ) • ρ g v from complexAverage_apply ρ _ v]
      rw [sum_inner]
      simp only [inner_smul_left,Complex.conj_ofReal]
    have hre := congrArg Complex.re he
    have hsq : (inner ℂ (B v) (B v)).re=‖B v‖^2 := inner_self_eq_norm_sq (𝕜:=ℂ) (B v)
    rw [hsq] at hre
    simpa only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero,inner_self_eq_norm_sq] using hre
  simp only [@norm_sub_sq ℂ V _ _,hρ,mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  rw [←Finset.sum_mul,hp.2,one_mul,←Finset.sum_mul,hp.2,one_mul]
  have hs : (∑g, p g*(2*(inner ℂ (ρ g v) (B v)).re))=2*‖B v‖^2 := by
    rw [←hi,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  change ‖v‖^2-(∑g, p g*(2*(inner ℂ (ρ g v) (B v)).re))+‖B v‖^2=_
  rw [hs]
  ring

lemma realAverage_identity_defect (ρ : Representation ℂ G V)
    (hρ : ∀ g v, ‖ρ g v‖=‖v‖) {p : G → ℝ} (hp : IsProbability p) (v : V) :
    p 1*‖v-complexAverage ρ (fun g => (p g:ℂ)) v‖^2 ≤
      ‖v‖^2-‖complexAverage ρ (fun g => (p g:ℂ)) v‖^2 := by
  rw [←complexAverage_variance ρ hρ hp]
  simpa only [map_one,Module.End.one_apply] using Finset.single_le_sum (fun g _ => mul_nonneg (hp.1 g)
    (sq_nonneg ‖ρ g v-complexAverage ρ (fun g => (p g:ℂ)) v‖))
    (Finset.mem_univ (1:G))

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_IndependentOperator
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

lemma independent_reverse_product {R : Type*} [Semiring R] {n : ℕ}
    {X : Fin n → Type*} [∀j, Fintype (X j)] (A : (j : Fin n) → X j → R) :
    (List.ofFn (fun j => ∑a, A j a)).reverse.prod=
      ∑f : ∀j, X j, (List.ofFn (fun j => A j (f j))).reverse.prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ,List.reverse_cons,List.prod_append,List.prod_singleton,ih]
    rw [←Equiv.sum_comp (Fin.consEquiv X),Fintype.sum_prod_type]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro f _
    simp only [Fin.consEquiv,Equiv.coe_fn_mk,List.ofFn_succ,List.reverse_cons,
      List.prod_append,List.prod_singleton,Fin.cons_zero,Fin.cons_succ]

lemma weighted_reverse_product {R : Type*} [Semiring R] [Algebra ℂ R] {n : ℕ}
    (w : Fin n → ℂ) (A : Fin n → R) :
    (List.ofFn (fun j => w j • A j)).reverse.prod=
      (∏j,w j) • (List.ofFn A).reverse.prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ,List.reverse_cons,List.prod_append,List.prod_singleton,
      Fin.prod_univ_succ]
    rw [ih,smul_mul_smul_comm,mul_comm (∏j : Fin n, w j.succ) (w 0)]

lemma independent_average_product {R : Type*} [Semiring R] [Algebra ℂ R] {n : ℕ}
    {X : Fin n → Type*} [∀j, Fintype (X j)]
    (w : (j : Fin n) → X j → ℂ) (A : (j : Fin n) → X j → R) :
    (∑f : ∀j, X j, (∏j,w j (f j)) •
      (List.ofFn (fun j => A j (f j))).reverse.prod)=
      (List.ofFn (fun j => ∑a, w j a • A j a)).reverse.prod := by
  rw [independent_reverse_product]
  exact Finset.sum_congr rfl (fun f _ => (weighted_reverse_product _ _).symm)

lemma reverse_product_norm_le_one {R : Type*} [NormedRing R] [NormOneClass R]
    {n : ℕ} (A : Fin n → R) (hA : ∀j, ‖A j‖≤1) :
    ‖(List.ofFn A).reverse.prod‖≤1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ,List.reverse_cons,List.prod_append,List.prod_singleton]
    exact (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _)
      (ih _ (fun index => hA index.succ))).trans (hA 0))

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

lemma pi_single_reverse {I G : Type*} [Fintype I] [DecidableEq I] [Group G]
    (f : I → G) (e : Fin (Fintype.card I) ≃ I) :
    (List.ofFn (fun j => Pi.mulSingle (e j) (f (e j)))).reverse.prod=f := by
  funext i
  have hh := List.prod_map_eq_pow_single (e.symm i)
    (fun j => (Pi.mulSingle (e j) (f (e j)) : I → G) i)
    (l := (List.ofFn (fun j : Fin (Fintype.card I) => j)).reverse) (by
      intro j hj _
      have hne : i ≠ e j := by
        intro he
        apply hj
        exact e.injective (he.symm.trans (e.apply_symm_apply i).symm)
      simp [Pi.mulSingle,hne])
  have hc : ((List.ofFn (fun j : Fin (Fintype.card I) => j)).reverse).count (e.symm i)=1 := by
    apply List.count_eq_one_of_mem
    · exact List.nodup_reverse.mpr (List.nodup_ofFn.mpr Function.injective_id)
    · simp
  rw [hc,pow_one,e.apply_symm_apply,Pi.mulSingle_eq_same] at hh
  simp only [List.map_reverse,List.map_ofFn,Function.comp_def] at hh
  change (Pi.evalMonoidHom (fun _ : I => G) i)
    ((List.ofFn (fun j => Pi.mulSingle (e j) (f (e j)))).reverse.prod)=f i
  rw [map_list_prod,List.map_reverse,List.map_ofFn]
  exact hh

variable {G V : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

lemma complexAverage_sum (ρ : Representation ℂ G V) (p : G → ℂ) :
    complexAverage ρ p=∑g,p g • continuousRep ρ g := by
  ext v
  simp [complexAverage_apply,continuousRep]

theorem pi_average_norm_le_one {I : Type*} [Fintype I] [DecidableEq I] [DecidableEq G] [Nontrivial V]
    (ρ : Representation ℂ (I → G) V) (p : I → G → ℂ)
    (h : ∀i, ‖complexAverage (ρ.comp (MonoidHom.mulSingle (fun _ : I => G) i)) (p i)‖≤1) :
    ‖complexAverage ρ (fun f => ∏i,p i (f i))‖≤1 := by
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let E : (Fin (Fintype.card I) → G) ≃ (I → G) := Equiv.piCongrLeft (fun _ => G) e
  have he (f : Fin (Fintype.card I) → G) : ∀j, E f (e j)=f j := by
    intro j; simp [E,Equiv.piCongrLeft]
  have hf : complexAverage ρ (fun f => ∏i,p i (f i))=
      (List.ofFn (fun j => complexAverage
        (ρ.comp (MonoidHom.mulSingle (fun _ : I => G) (e j))) (p (e j)))).reverse.prod := by
    rw [complexAverage_sum,←Equiv.sum_comp E]
    simp_rw [←e.prod_comp (fun i => p i (E _ i))]
    have ht (f : Fin (Fintype.card I) → G) : continuousRep ρ (E f)=
        (List.ofFn (fun j => continuousRep ρ (Pi.mulSingle (e j) (f j)))).reverse.prod := by
      rw [←pi_single_reverse (E f) e,map_list_prod,List.map_reverse,List.map_ofFn]
      simp only [Function.comp_def,he]
    simp_rw [ht,he]
    rw [independent_average_product (X := fun _ => G)
      (fun j a => p (e j) a) (fun j a => continuousRep ρ (Pi.mulSingle (e j) a))]
    congr 3
    funext j
    rw [complexAverage_sum]
    rfl
  rw [hf]
  exact reverse_product_norm_le_one _ (fun j => h (e j))

lemma pi_comp_average_norm_le_one {I H : Type*} [Fintype I] [DecidableEq I] [DecidableEq G] [Group H] [Fintype H]
    [Nontrivial V] (ρ : Representation ℂ H V) (φ : (I → G) →* H)
    (p : G → ℂ) (hρ : ∀g v, ‖ρ g v‖=‖v‖)
    (hp : ∀σ : Representation ℂ G V, (∀g v, ‖σ g v‖=‖v‖) →
      ‖complexAverage σ p‖≤1) :
    ‖complexAverage (ρ.comp φ) (fun f => ∏i,p (f i))‖≤1 := by
  apply pi_average_norm_le_one
  intro i
  apply hp
  exact fun g v => hρ _ v

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Analytic_FiniteAverageGap
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
variable {G V : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

lemma realAverage_uniform_commute (ρ : Representation ℂ G V) {p : G → ℝ}
    (hp : IsProbability p) (v : V) :
    complexAverage ρ (fun g => (p g:ℂ))
        (complexAverage ρ (fun g => (uniformLaw G g:ℂ)) v)=
      complexAverage ρ (fun g => (uniformLaw G g:ℂ)) v ∧
    complexAverage ρ (fun g => (uniformLaw G g:ℂ))
        (complexAverage ρ (fun g => (p g:ℂ)) v)=
      complexAverage ρ (fun g => (uniformLaw G g:ℂ)) v := by
  constructor
  · rw [complexAverage_apply]
    simp only [complexAverage_uniform_left,←Finset.sum_smul,←Complex.ofReal_sum,hp.2,
      Complex.ofReal_one,one_smul]
  · rw [complexAverage_apply ρ (fun g => (p g:ℂ)),map_sum]
    simp only [map_smul,complexAverage_uniform_right,←Finset.sum_smul,←Complex.ofReal_sum,
      hp.2,Complex.ofReal_one,one_smul]

lemma realAverage_TV_bound (ρ : Representation ℂ G V)
    (hρ : ∀ g v, ‖ρ g v‖=‖v‖) (p q : G → ℝ) (v : V) :
    ‖complexAverage ρ (fun g => (p g:ℂ)) v-
      complexAverage ρ (fun g => (q g:ℂ)) v‖ ≤ 2*totalVariation p q*‖v‖ := by
  have he : ∑g, ‖((p g:ℂ)-(q g:ℂ))‖=2*totalVariation p q := by
    simp only [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,totalVariation]
    ring
  simpa only [complexAverage_sub,sub_apply,he] using
    complexAverage_norm_apply ρ hρ (fun g => (p g:ℂ)-(q g:ℂ)) v

omit [FiniteDimensional ℂ V] in
lemma contraction_power_drift (B : V →L[ℂ] V) (hB : ∀v, ‖B v‖ ≤ ‖v‖) (n : ℕ) (v : V) :
    ‖v-(B^n) v‖ ≤ n*‖v-B v‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : v-(B^(n+1)) v=(v-B v)+B (v-(B^n) v) := by
      rw [pow_succ',mul_apply_eq_comp,map_sub]
      abel
    rw [he,Nat.cast_add,Nat.cast_one,add_mul]
    calc
      _ ≤ ‖v-B v‖ + ‖B (v-(B^n) v)‖ := norm_add_le _ _
      _ ≤ ‖v-B v‖ + n*‖v-B v‖ := by linarith [hB (v-(B^n) v)]
      _ = _ := by ring

theorem finite_average_gap (ρ : Representation ℂ G V)
    (hρ : ∀ g v, ‖ρ g v‖=‖v‖) {p : G → ℝ} (hp : IsProbability p)
    (hp1 : 0 < p 1) {L : ℕ} (hL : 0<L)
    (hTV : totalVariation (convolutionPower p L) (uniformLaw G) ≤ 1/4)
    (v : V) (hv : complexAverage ρ (fun g => (uniformLaw G g:ℂ)) v=0) :
    ‖complexAverage ρ (fun g => (p g:ℂ)) v‖^2 ≤
      (1-p 1/(4*(L:ℝ)^2))*‖v‖^2 := by
  let B := complexAverage ρ (fun g => (p g:ℂ))
  have hLp : (0:ℝ)<L := by exact_mod_cast hL
  have hpow : ‖(B^L) v‖ ≤ ‖v‖/2 := by
    have ht := realAverage_TV_bound ρ hρ (convolutionPower p L) (uniformLaw G) v
    rw [complexAverage_power,hv,sub_zero] at ht
    calc _ ≤ 2*totalVariation (convolutionPower p L) (uniformLaw G)*‖v‖ := ht
         _ ≤ ‖v‖/2 := by nlinarith [mul_le_mul_of_nonneg_right hTV (norm_nonneg v)]
  have hd := contraction_power_drift B (realAverage_contraction ρ hρ hp) L v
  have hn : ‖v‖ ≤ ‖v-(B^L) v‖+‖(B^L) v‖ := by simpa only [add_comm] using norm_le_insert' v ((B^L) v)
  have hc : ‖v‖/2 ≤ (L:ℝ)*‖v-B v‖ := by linarith
  have hcs : ‖v‖^2 ≤ 4*(L:ℝ)^2*‖v-B v‖^2 := by
    have hs := mul_self_le_mul_self (by positivity : 0≤‖v‖/2) hc
    nlinarith
  have hdef := realAverage_identity_defect ρ hρ hp v
  change p 1*‖v-B v‖^2 ≤ ‖v‖^2-‖B v‖^2 at hdef
  have hscale : p 1/(4*(L:ℝ)^2)*‖v‖^2 ≤ p 1*‖v-B v‖^2 := by
    rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hcs hp1.le]
  change ‖B v‖^2 ≤ _
  nlinarith

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
variable {G V : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

theorem finite_average_disk {p : G → ℝ} (hp : IsProbability p)
    (hp1 : 0<p 1) {L : ℕ} (hL : 0<L)
    (hTV : totalVariation (convolutionPower p L) (uniformLaw G) ≤ 1/4) :
    ∃ R : ℝ, 1<R ∧ ∀ (V : Type*) [NormedAddCommGroup V]
      [InnerProductSpace ℂ V] [FiniteDimensional ℂ V], ∀ (ρ : Representation ℂ G V),
      (∀g v, ‖ρ g v‖=‖v‖) → ∀z : ℂ, ‖z‖ ≤ R →
      ‖complexAverage ρ (fun g => (uniformLaw G g:ℂ))+
        z • (complexAverage ρ (fun g => (p g:ℂ))-
          complexAverage ρ (fun g => (uniformLaw G g:ℂ)))‖ ≤ 1 := by
  let c : ℝ := p 1/(4*(L:ℝ)^2)
  have hLp : (0:ℝ)<L := by exact_mod_cast hL
  have hL1 : (1:ℝ)≤L := by exact_mod_cast hL
  have hp1le : p 1≤1 := by
    rw [←hp.2]
    exact Finset.single_le_sum (fun g _ => hp.1 g) (Finset.mem_univ 1)
  have hc : 0<c := by dsimp [c]; positivity
  have hc1 : c≤1 := by
    dsimp [c]
    rw [div_le_one (by positivity)]
    nlinarith [sq_nonneg ((L:ℝ)-1)]
  let R : ℝ := 1+c/4
  have hR : 1<R := by dsimp [R]; linarith
  have hRq : R^2*(1-c) ≤ 1 := by
    dsimp [R]
    nlinarith [sq_nonneg c,mul_nonneg hc.le (sq_nonneg c)]
  refine ⟨R,hR,?_⟩
  intro V _ _ _ ρ hρ z hz
  let P := complexAverage ρ (fun g => (uniformLaw G g:ℂ))
  let B := complexAverage ρ (fun g => (p g:ℂ))
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  rw [one_mul]
  let u := P v
  let w := v-u
  have hPw : P w=0 := by
    change P (v-P v)=0
    rw [map_sub,complexAverage_uniform_idem,sub_self]
  have hPBw : P (B w)=0 := by
    rw [(realAverage_uniform_commute ρ hp w).2,hPw]
  have hiw : inner ℂ u w=0 := by
    change inner ℂ (P v) w=0
    rw [complexAverage_uniform_inner ρ hρ,hPw,inner_zero_right]
  have hiB : inner ℂ u (B w)=0 := by
    change inner ℂ (P v) (B w)=0
    rw [complexAverage_uniform_inner ρ hρ,hPBw,inner_zero_right]
  have hvsplit : v=u+w := by dsimp [w]; abel
  have hvsq : ‖v‖^2=‖u‖^2+‖w‖^2 := by
    calc ‖v‖^2=‖u+w‖^2 := congrArg (fun x : V => ‖x‖^2) hvsplit
         _ = _ := by simpa only [pow_two] using
           norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero u w hiw
  have hB : ‖B w‖^2 ≤ (1-c)*‖w‖^2 := finite_average_gap ρ hρ hp hp1 hL hTV w hPw
  have he : (P+z • (B-P)) v=u+z • B w := by
    simp only [add_apply,smul_apply,sub_apply]
    have hu : B u=u := (realAverage_uniform_commute ρ hp v).1
    have hb : B v=B u+B w := by rw [←map_add,←hvsplit]
    rw [hb,hu,show P v=u from rfl]
    abel_nf
  change ‖(P+z • (B-P)) v‖ ≤ ‖v‖
  rw [he]
  have hs : ‖u+z • B w‖^2=‖u‖^2+‖z‖^2*‖B w‖^2 := by
    have hi : inner ℂ u (z • B w)=0 := by rw [inner_smul_right,hiB,mul_zero]
    have hh := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero u (z • B w) hi
    simpa only [←pow_two,norm_smul,mul_pow] using hh
  have hzq : ‖z‖^2 ≤ R^2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
  have htot : ‖z‖^2*‖B w‖^2 ≤ ‖w‖^2 := by
    calc _ ≤ R^2*‖B w‖^2 := mul_le_mul_of_nonneg_right hzq (sq_nonneg _)
         _ ≤ R^2*((1-c)*‖w‖^2) := mul_le_mul_of_nonneg_left hB (sq_nonneg _)
         _ ≤ ‖w‖^2 := by nlinarith [mul_le_mul_of_nonneg_right hRq (sq_nonneg ‖w‖)]
  nlinarith [norm_nonneg (u+z • B w),norm_nonneg v]

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Processes_GridSweepPath
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps

variable {G : Type*} [Fintype G] [Group G]

lemma uniformLaw_probability : IsProbability (uniformLaw G) :=
  ⟨fun _ => by unfold uniformLaw; positivity, uniformLaw_sum⟩

lemma convolution_sub_left (p q r : G → ℝ) :
    convolution (fun g => p g - q g) r = fun g => convolution p r g - convolution q r g := by
  funext g
  simp [convolution, sub_mul, Finset.sum_sub_distrib]

lemma convolution_smul_left (a : ℝ) (p q : G → ℝ) :
    convolution (fun g => a * p g) q = fun g => a * convolution p q g := by
  funext g
  simp [convolution, mul_assoc, Finset.mul_sum]

lemma convolution_uniform_right_mass (p : G → ℝ) :
    convolution p (uniformLaw G) = fun g => (∑ x, p x) * uniformLaw G g := by
  funext g
  simp [convolution, uniformLaw, Finset.sum_mul]

lemma convolution_minorization {p q : G → ℝ} (hp : IsProbability p) (hq : IsProbability q)
    (δ : ℝ) (hδ : ∀ g, δ * uniformLaw G g ≤ p g) :
    totalVariation (convolution p q) (uniformLaw G) ≤
      (1 - δ) * totalVariation q (uniformLaw G) := by
  let r : G → ℝ := fun g => p g - δ * uniformLaw G g
  have hr : ∀ g, 0 ≤ r g := fun g => sub_nonneg.mpr (hδ g)
  have hmass : ∑ g, r g = 1 - δ := by
    simp [r, Finset.sum_sub_distrib, ← Finset.mul_sum, hp.2, uniformLaw_sum]
  have he : totalVariation (convolution p q) (uniformLaw G) =
      totalVariation (convolution r q) (convolution r (uniformLaw G)) := by
    have hdiff (g : G) : convolution r q g - convolution r (uniformLaw G) g =
        convolution p q g - uniformLaw G g := by
      rw [show r = (fun g => p g - δ * uniformLaw G g) from rfl,
        convolution_sub_left, convolution_smul_left, convolution_uniform_left hq.2]
      rw [← show r = (fun g => p g - δ * uniformLaw G g) from rfl,
        convolution_uniform_right_mass, hmass]
      ring
    simp only [totalVariation, hdiff]
  rw [he]
  simpa only [hmass] using convolution_tv_contract hr q (uniformLaw G)

end BinaryCoordinateSweeps
end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Processes_PointMassOne
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps
section FiniteRandomWalkConvergence
variable {G : Type*} [Fintype G] [Group G]

lemma pointMassOne_probability : IsProbability (pointMassOne : G → ℝ) := by
  classical
  constructor
  · intro g; unfold pointMassOne; split_ifs <;> norm_num
  · simp [pointMassOne]

lemma convolution_one_left (p : G → ℝ) : convolution pointMassOne p = p := by
  classical
  funext g
  simp [convolution, pointMassOne, ite_mul]

lemma convolutionPower_probability {p : G → ℝ} (hp : IsProbability p) (n : ℕ) :
    IsProbability (convolutionPower p n) := by
  induction n with
  | zero => exact pointMassOne_probability
  | succ n ih => exact convolution_probability hp ih

lemma convolutionPower_add (p : G → ℝ) (m n : ℕ) :
    convolutionPower p (m + n) = convolution (convolutionPower p m) (convolutionPower p n) := by
  induction m with
  | zero => simp [convolutionPower, convolution_one_left]
  | succ m ih =>
    simpa only [Nat.succ_add, convolutionPower, ih] using
      (convolution_assoc p (convolutionPower p m) (convolutionPower p n)).symm

lemma convolutionPower_block_bound {p : G → ℝ} (hp : IsProbability p) (L : ℕ)
    {δ : ℝ} (hδ0 : 0 ≤ 1 - δ)
    (hδ : ∀ g, δ * uniformLaw G g ≤ convolutionPower p L g) (k : ℕ) :
    totalVariation (convolutionPower p (L * k)) (uniformLaw G) ≤ (1 - δ) ^ k := by
  induction k with
  | zero =>
    simp only [mul_zero, pow_zero]
    exact totalVariation_le_one (convolutionPower_probability hp 0) uniformLaw_probability
  | succ k ih =>
    rw [Nat.mul_succ, Nat.add_comm, convolutionPower_add]
    calc
      _ ≤ (1 - δ) * totalVariation (convolutionPower p (L * k)) (uniformLaw G) :=
        convolution_minorization (convolutionPower_probability hp L)
          (convolutionPower_probability hp (L * k)) δ hδ
      _ ≤ (1 - δ) * (1 - δ) ^ k := mul_le_mul_of_nonneg_left ih hδ0
      _ = _ := by rw [pow_succ]; ring

lemma convolutionPower_all_time_bound {p : G → ℝ} (hp : IsProbability p) (L : ℕ)
    {δ : ℝ} (hδ0 : 0 ≤ 1 - δ)
    (hδ : ∀ g, δ * uniformLaw G g ≤ convolutionPower p L g) (t : ℕ) :
    totalVariation (convolutionPower p t) (uniformLaw G) ≤ (1 - δ) ^ (t / L) := by
  have he := convolutionPower_add p (t % L) (L * (t / L))
  rw [Nat.mod_add_div] at he
  rw [he, ← convolution_uniform_right (convolutionPower_probability hp (t % L)).2]
  have hc := convolution_tv_contract (convolutionPower_probability hp (t % L)).1
    (convolutionPower p (L * (t / L))) (uniformLaw G)
  rw [(convolutionPower_probability hp (t % L)).2, one_mul] at hc
  exact hc.trans (convolutionPower_block_bound hp L hδ0 hδ (t / L))

lemma uniformLaw_le_one (g : G) : uniformLaw G g ≤ 1 := by
  have hc : (1 : ℝ) ≤ Fintype.card G := by exact_mod_cast Fintype.card_pos (α := G)
  exact (inv_le_one₀ (by linarith)).mpr hc

theorem convolutionPower_tendsto_uniform {p : G → ℝ} (hp : IsProbability p)
    {L : ℕ} (hL : 0 < L) (hpos : ∀ g, 0 < convolutionPower p L g) :
    Filter.Tendsto (fun t => totalVariation (convolutionPower p t) (uniformLaw G))
      Filter.atTop (nhds 0) := by
  classical
  let ε := Finset.univ.inf' Finset.univ_nonempty (convolutionPower p L)
  have hε : 0 < ε := (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun g _ => hpos g)
  let δ : ℝ := min (1 / 2) ε
  have hδpos : 0 < δ := lt_min (by norm_num) hε
  have hδhalf : δ ≤ 1 / 2 := min_le_left _ _
  have hδ0 : 0 ≤ 1 - δ := by linarith
  have hδ : ∀ g, δ * uniformLaw G g ≤ convolutionPower p L g := by
    intro g
    calc
      _ ≤ δ * 1 := mul_le_mul_of_nonneg_left (uniformLaw_le_one g) hδpos.le
      _ = δ := mul_one _
      _ ≤ ε := min_le_right _ _
      _ ≤ _ := Finset.inf'_le _ (Finset.mem_univ g)
  apply squeeze_zero (fun _ => totalVariation_nonneg _ _)
    (convolutionPower_all_time_bound hp L hδ0 hδ)
  exact (tendsto_pow_atTop_nhds_zero_of_lt_one hδ0 (by linarith)).comp
    (Nat.tendsto_div_const_atTop hL.ne')

end FiniteRandomWalkConvergence

lemma finiteLaw_pos_of_mem {Ω G : Type*} [Fintype Ω] [Fintype G]
    (f : Ω → G) (ω : Ω) : 0 < finiteLaw f (f ω) := by
  classical
  have : Nonempty Ω := ⟨ω⟩
  apply Finset.sum_pos'
  · intro a _; split_ifs <;> positivity
  · exact ⟨ω, Finset.mem_univ _, by simp [Fintype.card_pos]⟩

section ReachableRandomWalk
variable {G Ω : Type*} [Fintype G] [Group G] [Fintype Ω] [Nonempty Ω]

lemma convolution_pos_at_mul {p q : G → ℝ} (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    {g h : G} (hg : 0 < p g) (hh : 0 < q h) : 0 < convolution p q (g * h) := by
  classical
  apply Finset.sum_pos'
  · intro x _; exact mul_nonneg (hp x) (hq _)
  · refine ⟨g, Finset.mem_univ _, ?_⟩
    simpa using mul_pos hg hh

lemma convolutionPower_pos_list (f : Ω → G) (l : List Ω) :
    0 < convolutionPower (finiteLaw f) l.length (l.map f).prod := by
  induction l with
  | nil => simp [convolutionPower, pointMassOne]
  | cons a l ih =>
    simpa only [List.length_cons, List.map_cons, List.prod_cons, convolutionPower] using
      convolution_pos_at_mul (finiteLaw_nonneg f)
        (convolutionPower_probability ⟨finiteLaw_nonneg f, finiteLaw_sum f⟩ l.length).1
        (finiteLaw_pos_of_mem f a) ih

lemma convolutionPower_pos_later {p : G → ℝ} (hp : IsProbability p) (h1 : 0 < p 1)
    {g : G} {n m : ℕ} (hn : 0 < convolutionPower p n g) (hnm : n ≤ m) :
    0 < convolutionPower p m g := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  clear hnm
  induction k with
  | zero => simpa using hn
  | succ k ih =>
    change 0 < convolution p (convolutionPower p (n + k)) g
    simpa only [one_mul] using
      convolution_pos_at_mul hp.1 (convolutionPower_probability hp (n + k)).1 h1 ih

lemma finiteLaw_fullSupport_power (f : Ω → G) (ω₀ : Ω) (hω₀ : f ω₀ = 1)
    (hgen : ∀ g : G, ∃ l : List Ω, (l.map f).prod = g) :
    ∃ L : ℕ, 0 < L ∧ ∀ g, 0 < convolutionPower (finiteLaw f) L g := by
  classical
  choose l hl using hgen
  let L := 1 + ∑ g : G, (l g).length
  refine ⟨L, by dsimp [L]; omega, ?_⟩
  intro g
  apply convolutionPower_pos_later ⟨finiteLaw_nonneg f, finiteLaw_sum f⟩
    (hω₀ ▸ finiteLaw_pos_of_mem f ω₀)
  · rw [← hl g]
    exact convolutionPower_pos_list f (l g)
  · exact (Finset.single_le_sum (fun i _ => Nat.zero_le ((l i).length))
      (Finset.mem_univ g)).trans (Nat.le_add_left _ _)

end ReachableRandomWalk

theorem fixed_dimension_sweep_convergence (d : ℕ) :
    Filter.Tendsto (fun t => totalVariation (sweepLaw d t)
      (uniformLaw (Equiv.Perm (Slot d)))) Filter.atTop (nhds 0) := by
  obtain ⟨L, hL, hpos⟩ := finiteLaw_fullSupport_power (binarySweep d)
    (fun _ _ => false) (binarySweep_zero d) (every_permutation_sweepReachable d)
  exact convolutionPower_tendsto_uniform
    ⟨finiteLaw_nonneg (binarySweep d), finiteLaw_sum (binarySweep d)⟩ hL hpos

end BinaryCoordinateSweeps
end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Mixing_BinaryLineDisk
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

lemma complexLineLaw_real (d : ℕ) (z : ℝ) (g : Equiv.Perm (Slot d)) :
    complexLineLaw d (z:ℂ) g=(lineLaw d z g:ℂ) := by
  simp [complexLineLaw,lineLaw]

lemma complexLine_average {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (d : ℕ) (ρ : Representation ℂ (Equiv.Perm (Slot d)) V)
    (z : ℂ) : complexAverage ρ (complexLineLaw d z)=
      complexAverage ρ (fun g => (uniformLaw (Equiv.Perm (Slot d)) g:ℂ))+
        z • (complexAverage ρ (fun g => (binaryLaw d g:ℂ))-
          complexAverage ρ (fun g => (uniformLaw (Equiv.Perm (Slot d)) g:ℂ))) := by
  ext v
  simp only [complexAverage_apply,complexLineLaw,add_smul,mul_smul,
    Finset.sum_add_distrib,←Finset.smul_sum,add_apply,
    smul_apply,sub_apply]
  module

theorem binary_line_disk (d : ℕ) : ∃ R : ℝ, 1<R ∧
    ∀ (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V],
    ∀ (ρ : Representation ℂ (Equiv.Perm (Slot d)) V),
      (∀g v, ‖ρ g v‖=‖v‖) → ∀z : ℂ, ‖z‖≤R →
        ‖complexAverage ρ (complexLineLaw d z)‖ ≤ 1 := by
  have he : ∀ᶠ n in Filter.atTop,
      totalVariation (sweepLaw d n) (uniformLaw (Equiv.Perm (Slot d)))<1/4 :=
    (fixed_dimension_sweep_convergence d).eventually (gt_mem_nhds (by norm_num))
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp he
  have ht := (hN (max N 1) (le_max_left _ _)).le
  have hp : IsProbability (binaryLaw d) :=
    ⟨finiteLaw_nonneg _,finiteLaw_sum _⟩
  have hp1 : 0<binaryLaw d 1 := by
    rw [binaryLaw,←binarySweep_zero d]
    exact finiteLaw_pos_of_mem _ _
  obtain ⟨R,hR,h⟩ := finite_average_disk hp hp1 (by omega : 0 < max N 1) ht
  refine ⟨R,hR,?_⟩
  intro V _ _ _ ρ hρ z hz
  rw [complexLine_average]
  exact h V ρ hρ z hz

theorem binary_lines_disk (m : ℕ) : ∃ R : ℝ, 1<R ∧ ∀ d, d ≤ m →
    ∀ (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V],
    ∀ (ρ : Representation ℂ (Equiv.Perm (Slot d)) V),
      (∀g v, ‖ρ g v‖=‖v‖) → ∀z : ℂ, ‖z‖≤R →
        ‖complexAverage ρ (complexLineLaw d z)‖ ≤ 1 := by
  induction m with
  | zero =>
    obtain ⟨R,hR,h⟩ := binary_line_disk 0
    refine ⟨R,hR,?_⟩
    intro d hd
    have : d=0 := by omega
    subst d
    exact h
  | succ m ih =>
    obtain ⟨R,hR,h⟩ := ih
    obtain ⟨S,hS,k⟩ := binary_line_disk (m+1)
    refine ⟨min R S,lt_min hR hS,?_⟩
    intro d hd V _ _ _ ρ hρ z hz
    by_cases he : d=m+1
    · subst d
      exact k V ρ hρ z (hz.trans (min_le_right _ _))
    · exact h d (by omega) V ρ hρ z (hz.trans (min_le_left _ _))

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Analytic_ComplexGrid
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

variable {b : ℕ} (bits : Fin b → ℕ)

lemma complexGridWeight_real (z : ℝ) (g : GridChoices bits) :
    complexGridWeight bits (z:ℂ) g=(gridWeight bits z g:ℂ) := by
  simp [complexGridWeight,gridWeight,complexLineLaw_real]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  (ρ : Representation ℂ (Equiv.Perm (GridSlot bits)) V)

lemma complexGridAverage_product (z : ℂ) :
    complexGridAverage bits ρ z=(List.ofFn (fun j =>
      complexAverage (ρ.comp (gridStageHom bits j))
        (fun f => ∏y,complexLineLaw (bits j) z (f y)))).reverse.prod := by
  unfold complexGridAverage complexGridWeight gridSweep
  simp_rw [map_list_prod,List.map_reverse,List.map_ofFn,Function.comp_def]
  change (∑g : GridChoices bits, (∏j, ∏y, complexLineLaw (bits j) z (g j y)) •
    (List.ofFn (fun j => continuousRep ρ (gridStageHom bits j (g j)))).reverse.prod)=_
  rw [independent_average_product (X := fun j => GridOutside bits j → Equiv.Perm (Slot (bits j)))
    (fun j f => ∏y,complexLineLaw (bits j) z (f y))
    (fun j f => continuousRep ρ (gridStageHom bits j f))]
  congr 3
  funext j
  rw [complexAverage_sum]
  rfl

lemma complexGridAverage_differentiable : Differentiable ℂ (complexGridAverage bits ρ) := by
  unfold complexGridAverage
  apply Differentiable.fun_sum
  intro g _
  apply Differentiable.fun_smul
  · unfold complexGridWeight
    apply Differentiable.fun_finsetProd
    intro j _
    apply Differentiable.fun_finsetProd
    intro y _
    unfold complexLineLaw
    fun_prop
  · fun_prop

lemma complexGridAverage_norm_le_one [Nontrivial V] (z : ℂ)
    (hρ : ∀g v, ‖ρ g v‖=‖v‖)
    (hline : ∀j : Fin b,
      ∀σ : Representation ℂ (Equiv.Perm (Slot (bits j))) V,
      (∀g v, ‖σ g v‖=‖v‖) → ‖complexAverage σ (complexLineLaw (bits j) z)‖ ≤ 1) :
    ‖complexGridAverage bits ρ z‖ ≤ 1 := by
  rw [complexGridAverage_product]
  apply reverse_product_norm_le_one
  intro j
  exact pi_comp_average_norm_le_one (I := GridOutside bits j)
    (G := Equiv.Perm (Slot (bits j))) (H := Equiv.Perm (GridSlot bits)) (V := V)
    ρ (gridStageHom bits j)
    (complexLineLaw (bits j) z) hρ (hline j)

theorem complex_grid_disk (m : ℕ) : ∃ R : ℝ, 1 < R ∧
    ∀ (b : ℕ) (bits : Fin b → ℕ), (∀ j, bits j ≤ m) →
    ∀ (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
      [FiniteDimensional ℂ V] [Nontrivial V],
    ∀ρ : Representation ℂ (Equiv.Perm (GridSlot bits)) V,
      (∀g v, ‖ρ g v‖=‖v‖) → ∀z : ℂ, ‖z‖ ≤ R →
        ‖complexGridAverage bits ρ z‖ ≤ 1 := by
  obtain ⟨R,hR,h⟩ := binary_lines_disk m
  refine ⟨R,hR,?_⟩
  intro b bits hm V _ _ _ _ ρ hρ z hz
  apply complexGridAverage_norm_le_one bits ρ z hρ
  intro j σ hσ
  exact h (bits j) (hm j) V σ hσ z hz

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Processes_IndependentHistory
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps

lemma totalVariation_fromInitial {G : Type*} [Fintype G] [Group G]
    (p : G → ℝ) (initial : G) :
    totalVariation (fromInitial p initial) (uniformLaw G) = totalVariation p (uniformLaw G) := by
  unfold totalVariation fromInitial uniformLaw
  congr 1
  exact Equiv.sum_comp (Equiv.mulRight initial⁻¹)
    (fun g => |p g - (Fintype.card G : ℝ)⁻¹|)

attribute [local instance] Classical.propDecidable

end BinaryCoordinateSweeps
end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungFactor
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.hilbertInner _root_.OAI.BinaryCoordinateSweeps.Young.hilbertNormed _root_.OAI.BinaryCoordinateSweeps.Young.instDecidableEqElemForallCellNatTabloid _root_.OAI.BinaryCoordinateSweeps.Young.instFiniteDimensionalComplexSubtypeAsModuleGForallElemForallCellNatTabloidTabloidRepresentationMemSubmoduleMonoidAlgebraSpecht _root_.OAI.BinaryCoordinateSweeps.Young.instFintypeElemForallCellNatTabloid _root_.OAI.BinaryCoordinateSweeps.Young.instFintypeSubtypePermCellMemSubgroupC _root_.OAI.BinaryCoordinateSweeps.Young.instMulActionGElemForallCellNatTabloid _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps.Young

lemma nat_le_strictMono {n : ℕ} (f : Fin n → ℕ) (hf : StrictMono f) (i : Fin n) :
    i.val ≤ f i := by
  obtain ⟨i, hi⟩ := i
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
    have hi' : i < n := by omega
    have hl := hf (show (⟨i, hi'⟩ : Fin n) < ⟨i+1, hi⟩ from by simp)
    have hp := ih hi'
    change i ≤ f ⟨i, hi'⟩ at hp
    change i + 1 ≤ f ⟨i+1, hi⟩
    omega

lemma sum_orderEmb (s : Finset ℕ) :
    ∑ i : Fin s.card, s.orderEmbOfFin rfl i = ∑ i ∈ s, i := by
  have h := Finset.sum_map (s := (Finset.univ : Finset (Fin s.card)))
    (s.orderEmbOfFin rfl).toEmbedding (fun i : ℕ => i)
  rw [s.map_orderEmbOfFin_univ rfl] at h
  exact h.symm

lemma range_sum_le (s : Finset ℕ) :
    ∑ i ∈ Finset.range s.card, i ≤ ∑ i ∈ s, i := by
  let e := s.orderEmbOfFin rfl
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => nat_le_strictMono e e.strictMono i)
  simpa only [← Fin.sum_univ_eq_sum_range, e, sum_orderEmb] using h

lemma eq_range_of_sum_eq (s : Finset ℕ)
    (h : ∑ i ∈ s, i = ∑ i ∈ Finset.range s.card, i) : s = Finset.range s.card := by
  let e := s.orderEmbOfFin rfl
  have he : ∀ i : Fin s.card, e i = i.val := by
    have hsum : ∑ i : Fin s.card, i.val = ∑ i : Fin s.card, e i := by
      dsimp only [e]
      rw [sum_orderEmb, Fin.sum_univ_eq_sum_range (fun i : ℕ => i)]
      exact h.symm
    have hh := (Finset.sum_eq_sum_iff_of_le
        (fun (i : Fin s.card) _ => nat_le_strictMono e e.strictMono i)).mp hsum
    exact fun i => (hh i (Finset.mem_univ i)).symm
  ext i
  constructor
  · intro hi
    obtain ⟨j, hj⟩ := (s.range_orderEmbOfFin rfl ▸ hi : i ∈ Set.range e)
    rw [← hj, he]
    exact Finset.mem_range.mpr j.isLt
  · intro hi
    let j : Fin s.card := ⟨i, Finset.mem_range.mp hi⟩
    rw [← show e j = i from he j]
    exact s.orderEmbOfFin_mem rfl j

lemma mem_columnCells {μ : YoungDiagram} {j : ℕ} {x : Cell μ} :
    x ∈ columnCells μ j ↔ col x = j := by simp [columnCells]

lemma row_injectiveOn_column (μ : YoungDiagram) (j : ℕ) :
    Set.InjOn (row (μ := μ)) (↑(columnCells μ j) : Set (Cell μ)) := by
  intro x hx y hy hxy
  apply Subtype.ext
  apply Prod.ext hxy
  exact (mem_columnCells.mp hx).trans (mem_columnCells.mp hy).symm

lemma image_row_columnCells (μ : YoungDiagram) (j : ℕ) :
    (columnCells μ j).image row = Finset.range (μ.colLen j) := by
  ext i
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hc := x.property
    have hj := mem_columnCells.mp hx
    change x.val.2 = j at hj
    rw [← hj]
    exact YoungDiagram.mem_iff_lt_colLen.mp hc
  · intro hi
    refine ⟨⟨(i,j), YoungDiagram.mem_iff_lt_colLen.mpr hi⟩, ?_, rfl⟩
    exact mem_columnCells.mpr rfl

lemma card_columnCells (μ : YoungDiagram) (j : ℕ) :
    (columnCells μ j).card = μ.colLen j := by
  rw [← Finset.card_image_of_injOn (row_injectiveOn_column μ j), image_row_columnCells]
  exact Finset.card_range _

lemma sum_row_columnCells (μ : YoungDiagram) (j : ℕ) :
    ∑ x ∈ columnCells μ j, row x = ∑ i ∈ Finset.range (μ.colLen j), i := by
  rw [← image_row_columnCells μ j]
  exact (Finset.sum_image (f := fun i : ℕ => i) (row_injectiveOn_column μ j)).symm

lemma sum_columnCells_le (μ : YoungDiagram) (f : Cell μ → ℕ) (j : ℕ)
    (hf : Set.InjOn f (columnCells μ j)) :
    ∑ x ∈ columnCells μ j, row x ≤ ∑ x ∈ columnCells μ j, f x := by
  have h := range_sum_le ((columnCells μ j).image f)
  rw [Finset.card_image_of_injOn hf, card_columnCells, Finset.sum_image hf] at h
  rwa [sum_row_columnCells]

lemma column_image_of_total_sum (μ : YoungDiagram) (f : Cell μ → ℕ)
    (hf : ∀ j, Set.InjOn f (columnCells μ j))
    (hsum : ∑ x, f x = ∑ x : Cell μ, row x) (j : ℕ) :
    (columnCells μ j).image f = Finset.range (μ.colLen j) := by
  classical
  let J := (Finset.univ : Finset (Cell μ)).image col
  have hmaps : ∀ x ∈ (Finset.univ : Finset (Cell μ)), col x ∈ J := by
    intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hfib (g : Cell μ → ℕ) :
      ∑ j ∈ J, ∑ x ∈ columnCells μ j, g x = ∑ x, g x :=
    Finset.sum_fiberwise_of_maps_to hmaps g
  have heq : ∑ j ∈ J, ∑ x ∈ columnCells μ j, row x =
      ∑ j ∈ J, ∑ x ∈ columnCells μ j, f x := by rw [hfib, hfib, hsum]
  have hone := (Finset.sum_eq_sum_iff_of_le
    (fun j (_ : j ∈ J) => sum_columnCells_le μ f j (hf j))).mp heq
  by_cases hj : j ∈ J
  · have hc : ((columnCells μ j).image f).card = μ.colLen j := by
      rw [Finset.card_image_of_injOn (hf j), card_columnCells]
    have h : ∑ i ∈ (columnCells μ j).image f, i =
        ∑ i ∈ Finset.range ((columnCells μ j).image f).card, i := by
      rw [hc, Finset.sum_image (hf j), ← sum_row_columnCells]
      exact (hone j hj).symm
    simpa only [hc] using eq_range_of_sum_eq _ h
  · have hc : columnCells μ j = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      apply hj
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, mem_columnCells.mp hx⟩
    have hz : μ.colLen j = 0 := by rw [← card_columnCells, hc]; rfl
    simp [hc, hz]

lemma rearranged_row_mem (μ : YoungDiagram) (π : Equiv.Perm (Cell μ))
    (hc : ∀ j, Set.InjOn (fun x => row (π x)) (columnCells μ j)) (x : Cell μ) :
    (row (π x), col x) ∈ μ := by
  have he := column_image_of_total_sum μ (fun x => row (π x)) hc
    (Equiv.sum_comp π row) (col x)
  have hm : row (π x) ∈ (columnCells μ (col x)).image (fun x => row (π x)) :=
    Finset.mem_image.mpr ⟨x, mem_columnCells.mpr rfl, rfl⟩
  rw [he, Finset.mem_range] at hm
  exact YoungDiagram.mem_iff_lt_colLen.mpr hm

lemma row_col_intersection (μ : YoungDiagram) :
    rowStabilizer μ ⊓ colStabilizer μ = ⊥ := by
  apply le_antisymm
  · intro π hπ
    change π = 1
    apply Equiv.ext
    intro x
    apply Subtype.ext
    exact Prod.ext (hπ.1 x) (hπ.2 x)
  · exact bot_le

theorem row_col_factorization (μ : YoungDiagram) (π : Equiv.Perm (Cell μ))
    (hc : ∀ j, Set.InjOn (fun x => row (π x)) (columnCells μ j)) :
    ∃ r ∈ rowStabilizer μ, ∃ c ∈ colStabilizer μ, π = r * c := by
  let t : Cell μ → Cell μ := fun x =>
    ⟨(row (π x), col x), rearranged_row_mem μ π hc x⟩
  have ht : Function.Injective t := by
    intro x y hxy
    have hcol := congrArg (fun z : Cell μ => col z) hxy
    change col x = col y at hcol
    have hrow := congrArg (fun z : Cell μ => row z) hxy
    change row (π x) = row (π y) at hrow
    exact hc (col x) (mem_columnCells.mpr rfl) (mem_columnCells.mpr hcol.symm) hrow
  let c : Equiv.Perm (Cell μ) := Equiv.ofBijective t
    ⟨ht, (Finite.injective_iff_surjective).mp ht⟩
  have cc : c ∈ colStabilizer μ := by intro x; rfl
  have cr : ∀ x, row (c x) = row (π x) := by intro x; rfl
  refine ⟨π * c⁻¹, ?_, c, cc, ?_⟩
  · intro x
    change row (π (c⁻¹ x)) = row x
    rw [← cr]
    simp
  · simp

theorem row_col_alternative (μ : YoungDiagram) (π : Equiv.Perm (Cell μ)) :
    (∃ x y : Cell μ, x ≠ y ∧ col x = col y ∧ row (π x) = row (π y)) ∨
    (∃ r ∈ rowStabilizer μ, ∃ c ∈ colStabilizer μ, π = r * c) := by
  by_cases hc : ∀ j, Set.InjOn (fun x => row (π x)) (columnCells μ j)
  · exact Or.inr (row_col_factorization μ π hc)
  · left
    simp only [Set.InjOn] at hc
    push Not at hc
    obtain ⟨j, x, hx, y, hy, hrow, hne⟩ := hc
    exact ⟨x, y, hne, (mem_columnCells.mp hx).trans (mem_columnCells.mp hy).symm, hrow⟩

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungTabloid
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.hilbertInner _root_.OAI.BinaryCoordinateSweeps.Young.hilbertNormed _root_.OAI.BinaryCoordinateSweeps.Young.instFiniteDimensionalComplexSubtypeAsModuleGForallElemForallCellNatTabloidTabloidRepresentationMemSubmoduleMonoidAlgebraSpecht _root_.OAI.BinaryCoordinateSweeps.Young.instFintypeSubtypePermCellMemSubgroupC _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps.Young
variable (μ : YoungDiagram)

lemma tabloidOfPerm_row_mul (π : G μ) (r : rowStabilizer μ) :
    tabloidOfPerm μ (π * r.val) = tabloidOfPerm μ π := by
  apply (tabloidOfPerm_eq_iff μ _ _).mpr
  simp

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungAnti
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.hilbertInner _root_.OAI.BinaryCoordinateSweeps.Young.hilbertNormed _root_.OAI.BinaryCoordinateSweeps.Young.instFiniteDimensionalComplexSubtypeAsModuleGForallElemForallCellNatTabloidTabloidRepresentationMemSubmoduleMonoidAlgebraSpecht _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps.Young
variable (μ : YoungDiagram)

lemma signC_swap {x y : Cell μ} (h : x ≠ y) : signC μ (Equiv.swap x y) = -1 := by
  simp [signC_eq, Equiv.Perm.sign_swap h]

lemma columnAnti_apply (v : Tabloid μ → ℂ) :
    columnAnti μ v = ∑ c : C μ, signC μ c.val • tabloidRepresentation μ c.val v := by
  simp [columnAnti, LinearMap.sum_apply]

lemma columnAnti_rep (c : C μ) (v : Tabloid μ → ℂ) :
    columnAnti μ (tabloidRepresentation μ c.val v) = signC μ c.val • columnAnti μ v := by
  rw [columnAnti_apply, columnAnti_apply, Finset.smul_sum]
  have h := Equiv.sum_comp (Equiv.mulRight c)
    (fun d : C μ => signC μ c.val • (signC μ d.val • tabloidRepresentation μ d.val v))
  rw [← h]
  apply Finset.sum_congr rfl
  intro d hd
  change signC μ d.val • tabloidRepresentation μ d.val (tabloidRepresentation μ c.val v) =
    signC μ c.val • (signC μ (d * c).val • tabloidRepresentation μ (d * c).val v)
  simp only [Subgroup.coe_mul, map_mul, Module.End.mul_apply, smul_smul]
  rw [show signC μ c.val * (signC μ d.val * signC μ c.val) = signC μ d.val from by
    calc
      _ = signC μ d.val * (signC μ c.val * signC μ c.val) := by ring
      _ = signC μ d.val := by rw [signC_sq, mul_one]]

lemma columnAnti_basis_column (c : C μ) :
    columnAnti μ (tabloidBasis μ (tabloidOfPerm μ c.val)) = signC μ c.val • polytabloid μ := by
  rw [← mul_one c.val, ← smul_tabloidOfPerm, ← rep_basis, columnAnti_rep]
  rfl

lemma col_fixes_base_iff (c : C μ) :
    c.val • tabloidOfPerm μ 1 = tabloidOfPerm μ 1 ↔ c = 1 := by
  rw [smul_tabloidOfPerm, mul_one, tabloidOfPerm_eq_iff]
  constructor
  · intro hc
    have hr : c.val ∈ rowStabilizer μ := by
      have h := (rowStabilizer μ).inv_mem hc
      simpa using h
    have hi : c.val ∈ rowStabilizer μ ⊓ colStabilizer μ := ⟨hr, c.property⟩
    rw [row_col_intersection] at hi
    exact Subtype.ext hi
  · intro hc
    subst c
    simp

lemma polytabloid_base : polytabloid μ (tabloidOfPerm μ 1) = 1 := by
  rw [polytabloid, columnAnti_apply]
  simp_rw [rep_basis, smul_tabloidOfPerm, mul_one]
  simp only [Finset.sum_apply, Pi.smul_apply, tabloidBasis, Pi.single_apply]
  have he (c : C μ) : tabloidOfPerm μ 1 = tabloidOfPerm μ c.val ↔ c = 1 := by
    simpa [smul_tabloidOfPerm, eq_comm] using (col_fixes_base_iff μ c)
  simp only [he]
  simp

lemma polytabloid_ne_zero : polytabloid μ ≠ 0 := by
  intro h
  have hh := congrFun h (tabloidOfPerm μ 1)
  rw [polytabloid_base] at hh
  exact one_ne_zero hh

lemma swap_mem_fiber {X Y : Type*} [DecidableEq X] (f : X → Y) {x y : X}
    (h : f x = f y) : Equiv.swap x y ∈ fiberStabilizer f := by
  intro z
  exact Equiv.apply_swap_eq_self h z

lemma swap_fixes_tabloid (t : Tabloid μ) {x y : Cell μ} (h : t.val x = t.val y) :
    (Equiv.swap x y : G μ) • t = t := by
  apply Subtype.ext
  funext z
  change t.val ((Equiv.swap x y)⁻¹ z) = t.val z
  simpa only [Equiv.swap_inv] using Equiv.apply_swap_eq_self h z

lemma columnAnti_basis_collision (π : G μ) {x y : Cell μ}
    (hne : x ≠ y) (hc : col x = col y) (hr : row (π⁻¹ x) = row (π⁻¹ y)) :
    columnAnti μ (tabloidBasis μ (tabloidOfPerm μ π)) = 0 := by
  let c : C μ := ⟨Equiv.swap x y, swap_mem_fiber _ hc⟩
  have hf : c.val • tabloidOfPerm μ π = tabloidOfPerm μ π :=
    swap_fixes_tabloid μ _ hr
  have h := columnAnti_rep μ c (tabloidBasis μ (tabloidOfPerm μ π))
  rw [rep_basis, hf] at h
  have hs : signC μ c.val = -1 := signC_swap μ hne
  rw [hs, neg_one_smul] at h
  ext t
  have ht := congrFun h t
  simp only [Pi.neg_apply] at ht
  change columnAnti μ (tabloidBasis μ (tabloidOfPerm μ π)) t = 0
  linear_combination (1 / 2 : ℂ) * ht

lemma columnAnti_basis_span (t : Tabloid μ) :
    ∃ a : ℂ, columnAnti μ (tabloidBasis μ t) = a • polytabloid μ := by
  obtain ⟨π, rfl⟩ := tabloidOfPerm_surjective μ t
  rcases row_col_alternative μ π⁻¹ with ⟨x, y, hne, hc, hr⟩ | ⟨r, hr, c, hc, he⟩
  · exact ⟨0, by rw [columnAnti_basis_collision μ π hne hc hr, zero_smul]⟩
  · have hp : π = c⁻¹ * r⁻¹ := by simpa using congrArg Inv.inv he
    rw [hp, tabloidOfPerm_row_mul μ c⁻¹ ⟨r⁻¹, (rowStabilizer μ).inv_mem hr⟩]
    exact ⟨signC μ c⁻¹, columnAnti_basis_column μ ⟨c⁻¹, (colStabilizer μ).inv_mem hc⟩⟩

theorem columnAnti_rank_one (v : Tabloid μ → ℂ) :
    columnAnti μ v = (columnAnti μ v (tabloidOfPerm μ 1)) • polytabloid μ := by
  have hv : ∃ a : ℂ, columnAnti μ v = a • polytabloid μ := by
    choose a ha using columnAnti_basis_span μ
    refine ⟨∑ t, v t * a t, ?_⟩
    conv_lhs => rw [← sum_tabloidBasis μ v]
    rw [map_sum, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro t ht
    rw [map_smul, ha, smul_smul]
  obtain ⟨a, ha⟩ := hv
  have he := congrFun ha (tabloidOfPerm μ 1)
  simp only [Pi.smul_apply, polytabloid_base, smul_eq_mul, mul_one] at he
  rw [he, ha]

lemma columnAnti_square (v : Tabloid μ → ℂ) :
    columnAnti μ (columnAnti μ v) = (Fintype.card (C μ) : ℂ) • columnAnti μ v := by
  rw [columnAnti_apply μ v]
  rw [map_sum]
  simp_rw [map_smul, columnAnti_rep, smul_smul, signC_sq, one_smul]
  rw [← columnAnti_apply]
  simp only [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ]

lemma columnAnti_polytabloid :
    columnAnti μ (polytabloid μ) = (Fintype.card (C μ) : ℂ) • polytabloid μ :=
  columnAnti_square μ _

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungSpecht
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.hilbertInner _root_.OAI.BinaryCoordinateSweeps.Young.hilbertNormed _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators MonoidAlgebra

namespace BinaryCoordinateSweeps.Young
variable (μ : YoungDiagram)

lemma antiModule_apply (v : (tabloidRepresentation μ).asModule) :
    antiModule μ v = (tabloidRepresentation μ).asModuleEquiv.symm
      (columnAnti μ ((tabloidRepresentation μ).asModuleEquiv v)) := rfl

lemma antiModule_rank_one (v : (tabloidRepresentation μ).asModule) :
    antiModule μ v =
      columnAnti μ ((tabloidRepresentation μ).asModuleEquiv v) (tabloidOfPerm μ 1) • polyModule μ := by
  rw [antiModule_apply, columnAnti_rank_one, map_smul]
  simp only [Pi.smul_apply, polytabloid_base, smul_eq_mul, mul_one]
  rfl

lemma polyModule_ne_zero : polyModule μ ≠ 0 := by
  intro h
  apply polytabloid_ne_zero μ
  have he := congrArg (tabloidRepresentation μ).asModuleEquiv h
  simpa only [polyModule, LinearEquiv.apply_symm_apply, map_zero] using he

lemma Specht_ne_bot : Specht μ ≠ ⊥ := by
  intro h
  have hm := polyModule_mem_Specht μ
  rw [h] at hm
  exact polyModule_ne_zero μ hm

lemma antiModule_mem (U : Submodule ℂ[G μ] (tabloidRepresentation μ).asModule)
    (v : (tabloidRepresentation μ).asModule) (hv : v ∈ U) : antiModule μ v ∈ U := by
  rw [antiModule_apply, columnAnti_apply, map_sum]
  apply U.sum_mem
  intro c hc
  have h := U.smul_mem (MonoidAlgebra.single c.val (signC μ c.val)) hv
  have he : (tabloidRepresentation μ).asModuleEquiv.symm
      (signC μ c.val • tabloidRepresentation μ c.val ((tabloidRepresentation μ).asModuleEquiv v)) =
      MonoidAlgebra.single c.val (signC μ c.val) • v := by
    apply (tabloidRepresentation μ).asModuleEquiv.injective
    rw [LinearEquiv.apply_symm_apply, Representation.asModuleEquiv_map_smul,
      Representation.asAlgebraHom_single, LinearMap.smul_apply]
  rw [he]
  exact h

lemma scalar_polyModule_mem_iff (U : Submodule ℂ[G μ] (tabloidRepresentation μ).asModule)
    {a : ℂ} (ha : a ≠ 0) : a • polyModule μ ∈ U ↔ polyModule μ ∈ U := by
  exact (U.restrictScalars ℂ).smul_mem_iff ha

lemma Specht_le_iff (U : Submodule ℂ[G μ] (tabloidRepresentation μ).asModule) :
    Specht μ ≤ U ↔ polyModule μ ∈ U := by
  rw [Specht, Submodule.span_le, Set.singleton_subset_iff]
  rfl

theorem Specht_isAtom : IsAtom (Specht μ) := by
  refine ⟨Specht_ne_bot μ, ?_⟩
  intro U hU
  obtain ⟨V, hUV⟩ := exists_isCompl U
  have ht : polyModule μ ∈ U ⊔ V := by
    rw [hUV.sup_eq_top]
    trivial
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp ht
  have hau := antiModule_mem μ U u hu
  have hav := antiModule_mem μ V v hv
  rw [antiModule_rank_one] at hau hav
  by_cases hc : columnAnti μ ((tabloidRepresentation μ).asModuleEquiv u) (tabloidOfPerm μ 1) = 0
  · have he : columnAnti μ ((tabloidRepresentation μ).asModuleEquiv v) (tabloidOfPerm μ 1) =
          (Fintype.card (C μ) : ℂ) := by
      have hh := congrArg (fun w : (tabloidRepresentation μ).asModule =>
        columnAnti μ ((tabloidRepresentation μ).asModuleEquiv w) (tabloidOfPerm μ 1)) huv
      simp only [map_add, Pi.add_apply, hc, zero_add, polyModule,
        LinearEquiv.apply_symm_apply, columnAnti_polytabloid,
        Pi.smul_apply, polytabloid_base, smul_eq_mul, mul_one] at hh
      exact hh
    have hne : (Fintype.card (C μ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hSV : Specht μ ≤ V := (Specht_le_iff μ V).mpr
      ((scalar_polyModule_mem_iff μ V (he.trans_ne hne)).mp hav)
    apply le_antisymm _ bot_le
    calc U ≤ U ⊓ V := le_inf le_rfl (hU.le.trans hSV)
         _ = ⊥ := hUV.inf_eq_bot
  · have hSU : Specht μ ≤ U := (Specht_le_iff μ U).mpr
      ((scalar_polyModule_mem_iff μ U hc).mp hau)
    exact (hU.not_ge hSU).elim

instance Specht_isSimpleModule : IsSimpleModule ℂ[G μ] (Specht μ) :=
  isSimpleModule_iff_isAtom.mpr (Specht_isAtom μ)

end BinaryCoordinateSweeps.Young

end

open scoped MonoidAlgebra BigOperators

namespace BinaryCoordinateSweeps.Young

variable {A V : Type*} [Ring A] [Algebra ℂ A] [AddCommGroup V]
  [Module A V] [Module ℂ V] [IsScalarTower ℂ A V]

variable (μ : YoungDiagram)

instance instIsIrreducibleGComplexSpechtSpaceSpechtRep : Representation.IsIrreducible (k := ℂ) (G := G μ) (V := SpechtSpace μ) (spechtRep μ) :=
  (Representation.isSimpleModule_iff_irreducible_ofModule (Specht μ)).mp inferInstance

lemma spechtInclude_poly : spechtInclude μ (spechtPoly μ) = polytabloid μ := by
  change (tabloidRepresentation μ).asModuleEquiv
    ((restrictLinearEquiv (A := ℂ[G μ]) (V := Specht μ)
      ((restrictLinearEquiv (A := ℂ[G μ]) (V := Specht μ)).symm
        (⟨polyModule μ, polyModule_mem_Specht μ⟩ : Specht μ))).val) = _
  rw [LinearEquiv.apply_symm_apply]
  exact (tabloidRepresentation μ).asModuleEquiv.apply_symm_apply _

lemma spechtPoly_ne_zero : spechtPoly μ ≠ 0 := by
  intro h
  have he := congrArg (spechtInclude μ) h
  rw [map_zero, spechtInclude_poly] at he
  exact polytabloid_ne_zero μ he

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_DiagonalRigidity
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.hilbertInner _root_.OAI.BinaryCoordinateSweeps.Young.hilbertNormed _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young

lemma diagonal_rigidity_aux {X : Type*} [Fintype X] (A B : X → ℝ)
    (r c : Equiv.Perm X) (hr : ∀ x, A (r x) = A x)
    (hc : ∀ x, B (c x) = B x)
    (hd : ∀ x, A ((r*c) x) + B ((r*c) x) = A x + B x) :
    ∀ x, A (c x) = A x := by
  have hq (x : X) : B ((r*c) x) = A x + B x - A (c x) := by
    have he := hd x
    change A (r (c x)) + _ = _ at he
    rw [hr] at he
    linarith
  have hxc : ∑ x, A (c x) * B x = ∑ x, A x * B x := by
    simpa only [hc] using Equiv.sum_comp c (fun x => A x * B x)
  have hxx : ∑ x, (A (c x))^2 = ∑ x, (A x)^2 :=
    Equiv.sum_comp c (fun x => (A x)^2)
  have hprod : ∑ x, (A (c x) * A x + A (c x) * B x - (A (c x))^2) =
      ∑ x, A x * B x := by
    calc
      _ = ∑ x, A ((r*c) x) * B ((r*c) x) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [hq]
        change _ = A (r (c x)) * _
        rw [hr]
        ring
      _ = _ := Equiv.sum_comp (r*c) (fun x => A x * B x)
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hxc] at hprod
  have hcross : ∑ x, A (c x) * A x = ∑ x, (A (c x))^2 := by linarith
  have hzero : ∑ x, (A (c x) - A x)^2 = 0 := by
    calc
      _ = (∑ x, (A (c x))^2) - 2 * (∑ x, A (c x)*A x) + ∑ x, (A x)^2 := by
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = 0 := by rw [hcross, hxx]; ring
  intro x
  have hx : (A (c x) - A x)^2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => sq_nonneg (A (c x) - A x))).mp hzero x
      (Finset.mem_univ x)
  nlinarith [sq_nonneg (A (c x) - A x)]

lemma diagonal_row_column (μ : YoungDiagram) (r : rowStabilizer μ) (c : C μ)
    (hd : r.val*c.val ∈ diagonalStabilizer μ) : r = 1 ∧ c = 1 := by
  have he := diagonal_rigidity_aux (fun x : Cell μ => (row x : ℝ))
    (fun x => (col x : ℝ)) r.val c.val
    (fun x => congrArg Nat.cast (r.property x)) (fun x => congrArg Nat.cast (c.property x))
    (fun x => by exact_mod_cast hd x)
  have hc : c.val ∈ rowStabilizer μ := fun x => by exact_mod_cast he x
  have hi : c.val ∈ rowStabilizer μ ⊓ colStabilizer μ := ⟨hc,c.property⟩
  rw [row_col_intersection] at hi
  have hc1 : c = 1 := Subtype.ext hi
  have hr1 : r = 1 := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    apply Subtype.ext
    apply Prod.ext (r.property x)
    have hh := hd x
    rw [hc1] at hh
    change row (r.val x) + col (r.val x) = row x + col x at hh
    rw [r.property] at hh
    exact Nat.add_left_cancel hh
  exact ⟨hr1,hc1⟩

lemma diagonal_column_row (μ : YoungDiagram) (c : C μ) (r : rowStabilizer μ)
    (hd : c.val*r.val ∈ diagonalStabilizer μ) : c = 1 ∧ r = 1 := by
  have hi := (diagonalStabilizer μ).inv_mem hd
  have he : (r⁻¹).val * (c⁻¹).val ∈ diagonalStabilizer μ := by simpa using hi
  obtain ⟨hr,hc⟩ := diagonal_row_column μ r⁻¹ c⁻¹ he
  exact ⟨inv_eq_one.mp hc, inv_eq_one.mp hr⟩

variable (μ : YoungDiagram)

lemma diagonal_tabloid_eq (g h : diagonalStabilizer μ) (c : C μ) :
    tabloidOfPerm μ (g.val*c.val) = tabloidOfPerm μ h.val ↔ g = h ∧ c = 1 := by
  constructor
  · intro he
    let r : rowStabilizer μ := ⟨(g.val*c.val)⁻¹*h.val,
      (tabloidOfPerm_eq_iff μ _ _).mp he⟩
    have hr : c.val*r.val = g.val⁻¹*h.val := by dsimp only [r]; group
    have hd : c.val*r.val ∈ diagonalStabilizer μ := by
      rw [hr]
      exact (diagonalStabilizer μ).mul_mem ((diagonalStabilizer μ).inv_mem g.property) h.property
    obtain ⟨hc,hr1⟩ := diagonal_column_row μ c r hd
    refine ⟨?_,hc⟩
    rw [hc,hr1] at hr
    have hg : g.val = h.val := inv_mul_eq_one.mp (by simpa using hr.symm)
    exact Subtype.ext hg
  · rintro ⟨rfl,rfl⟩
    simp

lemma diagonal_poly_coefficient (g h : diagonalStabilizer μ) :
    tabloidRepresentation μ g.val (polytabloid μ) (tabloidOfPerm μ h.val) =
      if g = h then (1 : ℂ) else 0 := by
  rw [polytabloid, columnAnti_apply]
  simp_rw [rep_basis, smul_tabloidOfPerm, mul_one]
  rw [map_sum]
  simp_rw [map_smul, rep_basis, smul_tabloidOfPerm]
  simp only [Finset.sum_apply, Pi.smul_apply, tabloidBasis, Pi.single_apply]
  have he (c : C μ) : tabloidOfPerm μ h.val = tabloidOfPerm μ (g.val*c.val) ↔
      g = h ∧ c = 1 := (eq_comm).trans (diagonal_tabloid_eq μ g h c)
  simp only [he]
  by_cases hgh : g = h
  · simp [hgh]
  · simp [hgh]

theorem diagonal_polytabloids_independent : LinearIndependent ℂ
    (fun g : diagonalStabilizer μ => spechtRep μ g.val (spechtPoly μ)) := by
  apply LinearIndependent.of_comp (f := spechtInclude μ)
  rw [Fintype.linearIndependent_iff]
  intro a ha g
  have he := congrFun ha (tabloidOfPerm μ g.val)
  simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, Pi.zero_apply] at he
  simp_rw [spechtInclude_rep, spechtInclude_poly, diagonal_poly_coefficient] at he
  simpa using he

theorem diagonal_card_le_dimension : Fintype.card (diagonalStabilizer μ) ≤
    Module.finrank ℂ (SpechtSpace μ) := by
  let : Module.Finite ℂ (SpechtSpace μ) :=
    inferInstanceAs (FiniteDimensional ℂ (SpechtSpace μ))
  exact (diagonal_polytabloids_independent μ).fintype_card_le_finrank

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_DiagonalDimension
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.hilbertInner _root_.OAI.BinaryCoordinateSweeps.Young.hilbertNormed _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
variable (μ : YoungDiagram)

lemma width_add_rectangle_le_card (x : Cell μ) :
    μ.rowLen 0 + row x * (col x+1) ≤ Fintype.card (Cell μ) := by
  let f : Fin (μ.rowLen 0) ⊕ (Fin (row x) × Fin (col x+1)) → Cell μ :=
    Sum.elim (fun a => ⟨(0,a.val), YoungDiagram.mem_iff_lt_rowLen.mpr a.isLt⟩)
      (fun a => ⟨(a.1.val+1,a.2.val), μ.up_left_mem
        (show a.1.val+1 ≤ row x from a.1.isLt)
        (show a.2.val ≤ col x from Nat.le_of_lt_succ a.2.isLt) x.property⟩)
  have hf : Function.Injective f := by
    intro a b he
    have he' := congrArg Subtype.val he
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        have hab : a = b := Fin.ext (congrArg Prod.snd he')
        exact congrArg Sum.inl hab
      | inr b =>
        have hh := congrArg Prod.fst he'
        change 0 = b.1.val+1 at hh
        omega
    | inr a =>
      cases b with
      | inl b =>
        have hh := congrArg Prod.fst he'
        change a.1.val+1 = 0 at hh
        omega
      | inr b =>
        congr 1
        apply Prod.ext
        · apply Fin.ext
          have hh := congrArg Prod.fst he'
          change a.1.val+1 = b.1.val+1 at hh
          omega
        · exact Fin.ext (congrArg Prod.snd he')
  simpa only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] using
    Fintype.card_le_of_injective f hf

lemma height_add_rectangle_le_card (x : Cell μ) :
    μ.colLen 0 + col x * (row x+1) ≤ Fintype.card (Cell μ) := by
  let y : Cell μ.transpose := ⟨x.val.swap, YoungDiagram.mem_transpose.mpr x.property⟩
  have hh := width_add_rectangle_le_card μ.transpose y
  have hc : Fintype.card (Cell μ.transpose) = Fintype.card (Cell μ) := by
    simpa only [Cell, Fintype.card_coe, YoungDiagram.card] using YoungDiagram.card_transpose μ
  simpa only [YoungDiagram.rowLen_transpose, hc, y, row, col, Prod.fst_swap, Prod.snd_swap] using hh

lemma height_width_le_card : max (μ.colLen 0) (μ.rowLen 0) ≤ Fintype.card (Cell μ) := by
  by_cases h : Nonempty (Cell μ)
  · obtain ⟨x⟩ := h
    exact max_le (by have := height_add_rectangle_le_card μ x; omega)
      (by have := width_add_rectangle_le_card μ x; omega)
  · have hempty : μ = ⊥ := by
      apply YoungDiagram.ext
      ext x
      simp only [YoungDiagram.cells_bot, Finset.notMem_empty, iff_false]
      intro hx
      exact h ⟨⟨x,hx⟩⟩
    subst μ
    simp [YoungDiagram.colLen, YoungDiagram.rowLen]

lemma diagonal_twice_le (x : Cell μ) :
    2*(diagonal μ x+1) ≤ Fintype.card (Cell μ) + max (μ.colLen 0) (μ.rowLen 0) := by
  have hr : row x < μ.colLen 0 :=
    (YoungDiagram.mem_iff_lt_colLen.mp x.property).trans_le (μ.colLen_anti 0 _ (Nat.zero_le _))
  have hc : col x < μ.rowLen 0 :=
    (YoungDiagram.mem_iff_lt_rowLen.mp x.property).trans_le (μ.rowLen_anti 0 _ (Nat.zero_le _))
  have hm := height_width_le_card μ
  unfold diagonal
  by_cases hrow : row x = 0
  · rw [hrow]
    omega
  by_cases hcol : col x = 0
  · rw [hcol]
    omega
  rcases le_total (μ.colLen 0) (μ.rowLen 0) with h | h
  · rw [max_eq_right h]
    have hh := width_add_rectangle_le_card μ x
    have hm2 : 2*row x ≤ row x*(col x+1) := by
      rw [mul_comm 2]
      exact Nat.mul_le_mul_left _ (by omega)
    omega
  · rw [max_eq_left h]
    have hh := height_add_rectangle_le_card μ x
    have hm2 : 2*col x ≤ col x*(row x+1) := by
      rw [mul_comm 2]
      exact Nat.mul_le_mul_left _ (by omega)
    omega

lemma diagonal_lt_half_card_add_max (x : Cell μ) :
    diagonal μ x < (Fintype.card (Cell μ) + max (μ.colLen 0) (μ.rowLen 0))/2 := by
  have hh := diagonal_twice_le μ x
  omega

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
variable {X Y : Type*} [Fintype X] [Fintype Y]

omit [Fintype X] [Fintype Y] in
lemma assembleFiberPerm_injective (f : X → Y) : Function.Injective (assembleFiberPerm f) := by
  intro p q he
  have hh := congrArg Subtype.val he
  have hh' : Equiv.sigmaCongrRight p = Equiv.sigmaCongrRight q :=
    (Equiv.sigmaFiberEquiv f).permCongr.injective hh
  exact Equiv.Perm.sigmaCongrRightHom_injective hh'

lemma product_factorial_le_stabilizer (f : X → Y) :
    (∏ y, (Fintype.card {x // f x = y}).factorial) ≤ Nat.card (fiberStabilizer f) := by
  have hi := Nat.card_le_card_of_injective (assembleFiberPerm f) (assembleFiberPerm_injective f)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_pi, Fintype.card_perm] using hi

lemma two_pow_sub_one_le_factorial (n : ℕ) : 2^(n-1) ≤ n.factorial := by
  cases n with
  | zero => simp
  | succ n =>
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.succ_sub_one, pow_succ, Nat.factorial_succ]
      have hp : 2 ≤ n+1+1 := by omega
      simpa only [Nat.succ_sub_one, mul_comm] using Nat.mul_le_mul ih hp

lemma two_pow_card_sub_colors_le_stabilizer (f : X → Y) :
    2^(Fintype.card X - Fintype.card Y) ≤ Nat.card (fiberStabilizer f) := by
  have hsum : ∑ y, Fintype.card {x // f x = y} = Fintype.card X := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.sigmaFiberEquiv f)
  have hexp : Fintype.card X - Fintype.card Y ≤
      ∑ y, (Fintype.card {x // f x = y} - 1) := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun (y : Y) _ =>
      show Fintype.card {x // f x = y} ≤ (Fintype.card {x // f x = y} - 1) + 1 from by omega)
    rw [hsum, Finset.sum_add_distrib] at hh
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hh
    omega
  calc
    _ ≤ 2^(∑ y, (Fintype.card {x // f x = y} - 1)) := Nat.pow_le_pow_right (by decide) hexp
    _ = ∏ y, 2^(Fintype.card {x // f x = y} - 1) := (Finset.prod_pow_eq_pow_sum _ _ _).symm
    _ ≤ ∏ y, (Fintype.card {x // f x = y}).factorial :=
      Finset.prod_le_prod' (fun y _ => two_pow_sub_one_le_factorial _)
    _ ≤ _ := product_factorial_le_stabilizer f

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Representations_UnitaryTransport
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep
open Representation

section Algebra
variable {G V W : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

lemma irreducible_equiv (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (e : ρ.Equiv σ) [ρ.IsIrreducible] : σ.IsIrreducible := by
  apply (irreducible_iff_isSimpleModule_asModule σ).mpr
  exact IsSimpleModule.congr (LinearEquiv.ofBijective
    (IntertwiningMap.equivLinearMapAsModule ρ σ e.toIntertwiningMap) e.toLinearEquiv.bijective).symm

end Algebra
variable {G V W : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  (ρ : Representation ℂ G V) (σ : Representation ℂ G W)

lemma equivalent_evenMoment (e : ρ.Equiv σ)
    (hρ : ∀ g v, ‖ρ g v‖ = ‖v‖) (hσ : ∀ g w, ‖σ g w‖ = ‖w‖)
    (p : G → ℂ) (q : ℕ) :
    evenMoment q (groupAverage ρ p) = evenMoment q (groupAverage σ p) := by
  have he : e.toLinearEquiv.conj (((groupAverage ρ p).adjoint * groupAverage ρ p)^q) =
      ((groupAverage σ p).adjoint * groupAverage σ p)^q := by
    ext w
    obtain ⟨v,rfl⟩ := e.toLinearEquiv.surjective w
    simp only [LinearEquiv.conj_apply,LinearMap.comp_apply,LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
    exact (even_compatible ρ σ p hρ hσ q e.toIntertwiningMap v).symm
  unfold evenMoment
  rw [← he,LinearMap.trace_conj']

end BinaryCoordinateSweeps.Irrep

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungHilbert
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
open Representation

variable (μ : YoungDiagram)

instance instIsIrreducibleGComplexSubtypeEuclideanSpaceElemForallCellNatTabloidMemSubmoduleSpechtHilbertHilbertSpecht : (hilbertSpecht μ).IsIrreducible :=
  letI : AddCommGroup (SpechtSpace μ) := Module.addCommMonoidToAddCommGroup ℂ
  Irrep.irreducible_equiv _ _ (Irrep.conjugateEquiv _ _)

lemma spechtHilbertEquiv_coeff (v : SpechtSpace μ) (t : Tabloid μ) :
    (spechtHilbertEquiv μ v).val t = spechtInclude μ v t := rfl

lemma hilbertSpecht_coeff (g : G μ) (v : SpechtHilbert μ) (t : Tabloid μ) :
    (hilbertSpecht μ g v).val t = v.val (g⁻¹ • t) := by
  obtain ⟨w,rfl⟩ := (spechtHilbertEquiv μ).surjective v
  change (spechtHilbertEquiv μ (spechtRep μ g ((spechtHilbertEquiv μ).symm
      (spechtHilbertEquiv μ w)))).val t = _
  rw [LinearEquiv.symm_apply_apply,spechtHilbertEquiv_coeff,spechtInclude_rep]
  rfl

lemma hilbertSpecht_inner (g : G μ) (v w : SpechtHilbert μ) :
    inner ℂ (hilbertSpecht μ g v) (hilbertSpecht μ g w) = inner ℂ v w := by
  change inner ℂ (hilbertSpecht μ g v).val (hilbertSpecht μ g w).val = inner ℂ v.val w.val
  simp only [PiLp.inner_apply,RCLike.inner_apply,hilbertSpecht_coeff]
  exact Equiv.sum_comp (MulAction.toPerm g⁻¹) (fun t => w.val t * star (v.val t))

lemma hilbertSpecht_unitary (g : G μ) (v : SpechtHilbert μ) :
    ‖hilbertSpecht μ g v‖ = ‖v‖ :=
  ((hilbertSpecht μ g).isometryOfInner (hilbertSpecht_inner μ g)).norm_map v

lemma hilbertSpecht_finrank : Module.finrank ℂ (SpechtHilbert μ) = Module.finrank ℂ (SpechtSpace μ) :=
  (spechtHilbertEquiv μ).finrank_eq.symm

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators Classical
open Equiv Equiv.Perm Finset

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Representations_MatrixIsotypicWhitening
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Classical MonoidAlgebra

namespace BinaryCoordinateSweeps.Irrep
open Representation

universe uG uW uV uI
variable {G : Type uG} [Group G] [Fintype G]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (σ : Representation ℂ G W)

omit [Fintype G] in
lemma algebraSubmoduleInclusion_injective (m : Submodule ℂ[G] σ.asModule) :
    Function.Injective (algebraSubmoduleInclusion σ m) := by
  intro x y h
  apply (RestrictScalars.addEquiv ℂ ℂ[G] m).injective
  apply Subtype.val_injective
  exact σ.asModuleEquiv.injective h

variable [FiniteDimensional ℂ W]
  {I : Type uI} {V : I → Type uV}
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, FiniteDimensional ℂ (V i)]
  (ρ : ∀ i, Representation ℂ G (V i))

omit [∀ i, FiniteDimensional ℂ (V i)] in
theorem iSup_isotypic_eq_top
    (complete : ∀ (U : Type uW) [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]
      (τ : Representation ℂ G U), τ.IsIrreducible → ∃ i, Nonempty (τ.Equiv (ρ i))) :
    (⨆ i, isotypicSpan (ρ i) σ) = ⊤ := by
  let T : Subrepresentation σ := {
    toSubmodule := ⨆ i, isotypicSpan (ρ i) σ
    apply_mem_toSubmodule := by
      intro g v hv
      apply Submodule.iSup_induction (fun i => isotypicSpan (ρ i) σ)
        (motive:=fun v => σ g v ∈ ⨆ i, isotypicSpan (ρ i) σ) hv
      · intro i v hv
        apply (le_iSup (fun i => isotypicSpan (ρ i) σ) i)
        rw [← isotypicSpan_map (ρ i) σ g]
        exact ⟨v,hv,rfl⟩
      · simp
      · intro x y hx hy; simpa only [map_add] using Submodule.add_mem _ hx hy }
  have htop : T.asSubmodule = ⊤ := by
    apply top_unique
    rw [← IsSemisimpleModule.sSup_simples_eq_top ℂ[G] σ.asModule]
    apply sSup_le
    intro m hm
    let group : AddCommGroup (RestrictScalars ℂ ℂ[G] m) :=
      Module.addCommMonoidToAddCommGroup ℂ
    let _ := group
    let _ : @Module ℂ (RestrictScalars ℂ ℂ[G] m) _ group.toAddCommMonoid :=
      RestrictScalars.module ℂ ℂ[G] m
    let τ := Representation.ofModule (k:=ℂ) (G:=G) m
    let f := algebraSubmoduleInclusion σ m
    have : FiniteDimensional ℂ (RestrictScalars ℂ ℂ[G] m) :=
      FiniteDimensional.of_injective f.toLinearMap (algebraSubmoduleInclusion_injective σ m)
    have : IsSimpleModule ℂ[G] m := hm
    have hτ : τ.IsIrreducible :=
      (Representation.isSimpleModule_iff_irreducible_ofModule m).mp hm
    obtain ⟨i,⟨e⟩⟩ := complete _ τ hτ
    intro x hx
    let v : RestrictScalars ℂ ℂ[G] m := (RestrictScalars.addEquiv ℂ ℂ[G] m).symm ⟨x,hx⟩
    change σ.asModuleEquiv x ∈ ⨆ i, isotypicSpan (ρ i) σ
    apply (le_iSup (fun i => isotypicSpan (ρ i) σ) i)
    apply (le_iSup (fun f : IntertwiningMap (ρ i) σ => LinearMap.range f.toLinearMap)
      (f.comp e.symm.toIntertwiningMap))
    refine ⟨e.toLinearEquiv.toFun v,?_⟩
    change f (e.toLinearEquiv.symm.toFun (e.toLinearEquiv.toFun v)) = σ.asModuleEquiv x
    exact congrArg f.toLinearMap.toFun (e.toLinearEquiv.symm_apply_apply v)
  have hT : T = ⊤ := Subrepresentation.subrepresentationSubmoduleOrderIso.injective
    (htop.trans (Subrepresentation.subrepresentationSubmoduleOrderIso.map_top).symm)
  exact congrArg Subrepresentation.toSubmodule hT

end BinaryCoordinateSweeps.Irrep

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Representations_IsotypicOrthogonal
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep
open Representation

variable {G V W Z : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [FiniteDimensional ℂ Z]
  (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (τ : Representation ℂ G Z)

omit [Fintype G] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
lemma intertwiner_zero_of_inequivalent [ρ.IsIrreducible] [σ.IsIrreducible]
    (h : ¬ Nonempty (ρ.Equiv σ)) (f : IntertwiningMap ρ σ) : f=0 := by
  exact (IsIrreducible.bijective_or_eq_zero f).resolve_left (fun hf => h ⟨f.ofBijective hf⟩)

omit [Fintype G] [FiniteDimensional ℂ W] in
theorem isotypic_orthogonal [ρ.IsIrreducible] [σ.IsIrreducible]
    (hρ : ∀ g v, ‖ρ g v‖=‖v‖) (_hσ : ∀ g w, ‖σ g w‖=‖w‖)
    (hτ : ∀ g z, ‖τ g z‖=‖z‖)
    (hne : ¬ Nonempty (ρ.Equiv σ)) :
    isotypicSpan σ τ ≤ (isotypicSpan ρ τ)ᗮ := by
  unfold isotypicSpan
  rw [← Submodule.iInf_orthogonal]
  apply iSup_le
  intro f
  rw [le_iInf_iff]
  intro g
  rintro _ ⟨w,rfl⟩
  rw [Submodule.mem_orthogonal]
  rintro _ ⟨v,rfl⟩
  have hn : ¬Nonempty (σ.Equiv ρ) := fun ⟨e⟩ => hne ⟨e.symm⟩
  have hz := intertwiner_zero_of_inequivalent σ ρ hn
    ((adjointIntertwiner ρ τ hρ hτ g).comp f)
  have he := congrArg (fun F : IntertwiningMap σ ρ => F w) hz
  change g.toLinearMap.adjoint (f.toLinearMap w) = 0 at he
  rw [← LinearMap.adjoint_inner_right,he]
  simp

end BinaryCoordinateSweeps.Irrep

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Representations_IrrepTransport
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators MonoidAlgebra Classical

namespace BinaryCoordinateSweeps.Irrep
variable {G H V : Type*} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]

lemma irreducible_comp_equiv (e : H ≃* G) (ρ : Representation ℂ G V) [ρ.IsIrreducible] :
    Representation.IsIrreducible (k := ℂ) (G := H) (V := V) (ρ.comp e.toMonoidHom) :=
  (subrepresentationCongr e ρ).isSimpleOrder_iff.mp inferInstance

variable [Fintype G] [FiniteDimensional ℂ V]

lemma classPair_character_self (ρ : Representation ℂ G V) [ρ.IsIrreducible] :
    classPairRight (classCharacter ρ) (classCharacter ρ) = 1 := by
  let : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr (Nat.card_pos.ne'))
  have he : Nonempty (Representation.Equiv ρ ρ) := ⟨Representation.Equiv.refl ρ⟩
  simpa [classPairRight, he] using Representation.char_orthonormal ρ ρ

lemma classPair_characters {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    [ρ.IsIrreducible] [σ.IsIrreducible] :
    classPairRight (classCharacter σ) (classCharacter ρ) =
      if Nonempty (Representation.Equiv σ ρ) then 1 else 0 := by
  let : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr (Nat.card_pos.ne'))
  exact Representation.char_orthonormal ρ σ

end BinaryCoordinateSweeps.Irrep

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Representations_CharacterComplete
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep
variable {G I : Type*} [Group G] [Fintype G] [Fintype I]
  {V : I → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, FiniteDimensional ℂ (V i)]
  (σ : ∀ i, Representation ℂ G (V i)) [∀ i, Representation.IsIrreducible (σ i)]

theorem linearIndependent_classCharacters
    (hdiff : ∀ i j, Nonempty (Representation.Equiv (σ i) (σ j)) → i = j) :
    LinearIndependent ℂ (fun i => classCharacter (σ i)) := by
  apply Fintype.linearIndependent_iff.mpr
  intro a ha i
  have h := congrArg (classPairRight (classCharacter (σ i))) ha
  simp only [map_sum, map_smul, map_zero, smul_eq_mul] at h
  have hi (j : I) : Nonempty (Representation.Equiv (σ i) (σ j)) ↔ i = j := by
    constructor
    · exact hdiff i j
    · rintro rfl
      exact ⟨Representation.Equiv.refl _⟩
  simp_rw [classPair_characters, hi] at h
  simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true] using h

theorem complete_of_card_ge [Nonempty I]
    (hdiff : ∀ i j, Nonempty (Representation.Equiv (σ i) (σ j)) → i = j)
    (hcard : Nat.card (ConjClasses G) ≤ Fintype.card I)
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G W) [ρ.IsIrreducible] :
    ∃ i, Nonempty (Representation.Equiv ρ (σ i)) := by
  let : Fintype (ConjClasses G) := Fintype.ofFinite _
  have hli := linearIndependent_classCharacters σ hdiff
  have hdim : Fintype.card I = Module.finrank ℂ (ConjClasses G → ℂ) := by
    apply le_antisymm hli.fintype_card_le_finrank
    simpa only [Module.finrank_pi, Nat.card_eq_fintype_card] using hcard
  have ht := hli.span_eq_top_of_card_eq_finrank hdim
  by_contra hn
  push Not at hn
  have hzero (i : I) : classPairRight (classCharacter ρ) (classCharacter (σ i)) = 0 := by
    have hi : ¬ Nonempty (Representation.Equiv ρ (σ i)) := fun ⟨f⟩ => (hn i).false f
    rw [classPair_characters, ite_eq_right hi]
  have hle : Submodule.span ℂ (Set.range (fun i => classCharacter (σ i))) ≤
      (classPairRight (classCharacter ρ)).ker := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hzero i
  rw [ht] at hle
  have he : classPairRight (classCharacter ρ) (classCharacter ρ) = 0 :=
    hle (Submodule.mem_top)
  rw [classPair_character_self] at he
  exact one_ne_zero he

end BinaryCoordinateSweeps.Irrep

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungDominance
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.hilbertInner _root_.OAI.BinaryCoordinateSweeps.Young.hilbertNormed _root_.OAI.BinaryCoordinateSweeps.Young.instIsIrreducibleGComplexSubtypeEuclideanSpaceElemForallCellNatTabloidMemSubmoduleSpechtHilbertHilbertSpecht _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators

namespace BinaryCoordinateSweeps.Young

lemma filter_column_card (μ : YoungDiagram) (j k : ℕ) :
    ((columnCells μ j).filter (fun x => row x < k)).card = min k (μ.colLen j) := by
  have hinj := row_injectiveOn_column μ j
  rw [← Finset.card_image_of_injOn (hinj.mono (by intro x hx; exact (Finset.mem_filter.mp hx).1))]
  have he : (((columnCells μ j).filter (fun x => row x < k)).image row) =
      Finset.range (min k (μ.colLen j)) := by
    ext i
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range, lt_min_iff]
    constructor
    · rintro ⟨x, ⟨hx, hk⟩, rfl⟩
      exact ⟨hk, Finset.mem_range.mp (image_row_columnCells μ j ▸
        Finset.mem_image.mpr ⟨x, hx, rfl⟩)⟩
    · rintro ⟨hk, hj⟩
      obtain ⟨x, hx, he⟩ := Finset.mem_image.mp
        ((image_row_columnCells μ j).symm ▸ Finset.mem_range.mpr hj)
      exact ⟨x, ⟨hx, he ▸ hk⟩, he⟩
  rw [he, Finset.card_range]

lemma filter_injective_column_le (μ : YoungDiagram) (f : Cell μ → ℕ) (j k : ℕ)
    (hf : Set.InjOn f (columnCells μ j)) :
    ((columnCells μ j).filter (fun x => f x < k)).card ≤ min k (μ.colLen j) := by
  apply le_min
  · calc
      _ ≤ (Finset.range k).card := by
        apply Finset.card_le_card_of_injOn f
        · intro x hx
          exact Finset.mem_range.mpr (Finset.mem_filter.mp hx).2
        · exact hf.mono (by intro x hx; exact (Finset.mem_filter.mp hx).1)
      _ = k := Finset.card_range k
  · rw [← card_columnCells μ j]
    exact Finset.card_le_card (Finset.filter_subset _ _)

lemma card_filter_eq_sum_columns (μ : YoungDiagram) (p : Cell μ → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card =
      ∑ j ∈ (Finset.univ : Finset (Cell μ)).image col, ((columnCells μ j).filter p).card := by
  simp only [Finset.card_filter]
  symm
  exact Finset.sum_fiberwise_of_maps_to
    (fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩) (fun x => if p x then 1 else 0)

theorem dominates_of_column_injective (μ ν : YoungDiagram) (e : Cell μ ≃ Cell ν)
    (he : ∀ j, Set.InjOn (fun x => row (e x)) (columnCells μ j)) : Dominates μ ν := by
  intro k
  have hc : rowPrefix ν k = (Finset.univ.filter (fun x : Cell μ => row (e x) < k)).card := by
    simp only [rowPrefix, Finset.card_filter]
    exact (Equiv.sum_comp e (fun x => if row x < k then 1 else 0)).symm
  rw [hc, card_filter_eq_sum_columns, rowPrefix, card_filter_eq_sum_columns]
  apply Finset.sum_le_sum
  intro j hj
  rw [filter_column_card]
  exact filter_injective_column_le μ _ j k (he j)

lemma rowPrefix_succ (μ : YoungDiagram) (k : ℕ) :
    rowPrefix μ (k+1) = rowPrefix μ k + μ.rowLen k := by
  have he : (Finset.univ.filter (fun x : Cell μ => row x < k+1)) =
      (Finset.univ.filter (fun x : Cell μ => row x < k)) ∪
      (Finset.univ.filter (fun x : Cell μ => row x = k)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    omega
  have hd : Disjoint (Finset.univ.filter (fun x : Cell μ => row x < k))
      (Finset.univ.filter (fun x : Cell μ => row x = k)) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    omega
  rw [rowPrefix, he, Finset.card_union_of_disjoint hd]
  congr 1
  rw [YoungDiagram.rowLen_eq_card]
  apply Finset.card_bij (fun (x : Cell μ) _ => x.val)
  · intro x hx
    rw [YoungDiagram.mem_row_iff]
    exact ⟨x.property, (Finset.mem_filter.mp hx).2⟩
  · intro x hx y hy he
    exact Subtype.ext he
  · intro x hx
    have h := YoungDiagram.mem_row_iff.mp hx
    exact ⟨⟨x, h.1⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h.2, rfl⟩

lemma dominates_antisymm {μ ν : YoungDiagram} (hμ : Dominates μ ν) (hν : Dominates ν μ) : μ = ν := by
  have hp (k : ℕ) : rowPrefix μ k = rowPrefix ν k := le_antisymm (hν k) (hμ k)
  have hr (k : ℕ) : μ.rowLen k = ν.rowLen k := by
    have h := hp (k+1)
    rw [rowPrefix_succ, rowPrefix_succ, hp k] at h
    exact Nat.add_left_cancel h
  apply SetLike.coe_injective
  ext x
  rcases x with ⟨i,j⟩
  simp only [SetLike.mem_coe, YoungDiagram.mem_iff_lt_rowLen, hr]

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators

namespace BinaryCoordinateSweeps.Young
variable {μ ν : YoungDiagram}

lemma crossAnti_apply (e : Cell μ ≃ Cell ν) (v : Tabloid ν → ℂ) :
    crossAnti e v = ∑ c : C μ, signC μ c.val •
      tabloidRepresentation ν (e.permCongr c.val) v := by
  simp [crossAnti, LinearMap.sum_apply]

lemma crossAnti_rep (e : Cell μ ≃ Cell ν) (c : C μ) (v : Tabloid ν → ℂ) :
    crossAnti e (tabloidRepresentation ν (e.permCongr c.val) v) =
      signC μ c.val • crossAnti e v := by
  rw [crossAnti_apply, crossAnti_apply, Finset.smul_sum]
  have h := Equiv.sum_comp (Equiv.mulRight c)
    (fun d : C μ => signC μ c.val •
      (signC μ d.val • tabloidRepresentation ν (e.permCongr d.val) v))
  rw [← h]
  apply Finset.sum_congr rfl
  intro d hd
  change signC μ d.val • tabloidRepresentation ν (e.permCongr d.val)
    (tabloidRepresentation ν (e.permCongr c.val) v) =
    signC μ c.val • (signC μ (d*c).val •
      tabloidRepresentation ν (e.permCongr (d*c).val) v)
  simp only [Subgroup.coe_mul, map_mul, Equiv.permCongr_mul, Module.End.mul_apply, smul_smul]
  rw [show signC μ c.val * (signC μ d.val * signC μ c.val) = signC μ d.val from by
    calc
      _ = signC μ d.val * (signC μ c.val * signC μ c.val) := by ring
      _ = signC μ d.val := by rw [signC_sq, mul_one]]

lemma crossAnti_basis_collision (e : Cell μ ≃ Cell ν) (t : Tabloid ν)
    {x y : Cell μ} (hne : x ≠ y) (hc : col x = col y) (ht : t.val (e x) = t.val (e y)) :
    crossAnti e (tabloidBasis ν t) = 0 := by
  let c : C μ := ⟨Equiv.swap x y, swap_mem_fiber _ hc⟩
  have he : e.permCongr c.val = Equiv.swap (e x) (e y) := by
    apply Equiv.ext
    intro z
    change e (Equiv.swap x y (e.symm z)) = _
    rw [Function.Injective.map_swap e.injective, e.apply_symm_apply]
  have hf : e.permCongr c.val • t = t := by
    rw [he]
    exact swap_fixes_tabloid ν _ ht
  have h := crossAnti_rep e c (tabloidBasis ν t)
  rw [rep_basis, hf, show signC μ c.val = -1 from signC_swap μ hne, neg_one_smul] at h
  ext u
  have hu := congrFun h u
  simp only [Pi.neg_apply] at hu
  change crossAnti e (tabloidBasis ν t) u = 0
  linear_combination (1/2 : ℂ) * hu

theorem crossAnti_eq_zero_of_not_dominates (e : Cell μ ≃ Cell ν) (h : ¬ Dominates μ ν) :
    crossAnti e = 0 := by
  have hb (t : Tabloid ν) : crossAnti e (tabloidBasis ν t) = 0 := by
    obtain ⟨π, rfl⟩ := tabloidOfPerm_surjective ν t
    by_contra hn
    apply h
    apply dominates_of_column_injective μ ν (e.trans π.symm)
    intro j x hx y hy hxy
    by_contra hne
    apply hn
    exact crossAnti_basis_collision e _ hne
      ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm) hxy
  apply LinearMap.ext
  intro v
  have hv : crossAnti e v = 0 := by
    conv_lhs => rw [← sum_tabloidBasis ν v]
    simp only [map_sum, map_smul, hb, smul_zero, Finset.sum_const_zero]
  exact hv

lemma spechtInclude_column_sum :
    (∑ c : C μ, signC μ c.val • spechtRep μ c.val (spechtPoly μ)) =
      (Fintype.card (C μ) : ℂ) • spechtPoly μ := by
  apply spechtInclude_injective μ
  simp only [map_sum, map_smul, spechtInclude_rep, spechtInclude_poly]
  simpa only [columnAnti_apply] using columnAnti_polytabloid μ

theorem intertwiner_dominance (e : Cell μ ≃ Cell ν)
    (f : SpechtSpace μ →ₗ[ℂ] (Tabloid ν → ℂ))
    (hf : ∀ g v, f (spechtRep μ g v) = tabloidRepresentation ν (e.permCongr g) (f v))
    (hne : f (spechtPoly μ) ≠ 0) : Dominates μ ν := by
  by_contra h
  have he : crossAnti e (f (spechtPoly μ)) = (Fintype.card (C μ) : ℂ) • f (spechtPoly μ) := by
    rw [crossAnti_apply]
    simp_rw [← hf]
    have hh := congrArg f (spechtInclude_column_sum (μ := μ))
    simpa only [map_sum, map_smul] using hh
  rw [crossAnti_eq_zero_of_not_dominates e h, LinearMap.zero_apply] at he
  exact hne ((smul_eq_zero.mp he.symm).resolve_left
    (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))

theorem equivalence_implies_diagram_eq (e : Cell μ ≃ Cell ν)
    (f : SpechtSpace μ ≃ₗ[ℂ] SpechtSpace ν)
    (hf : ∀ g v, f (spechtRep μ g v) = spechtRep ν (e.permCongr g) (f v)) : μ = ν := by
  apply dominates_antisymm
  · apply intertwiner_dominance e ((spechtInclude ν).comp f.toLinearMap)
    · intro g v
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hf, spechtInclude_rep]
    · intro hz
      apply spechtPoly_ne_zero μ
      apply f.injective
      apply spechtInclude_injective ν
      simpa using hz
  · apply intertwiner_dominance e.symm ((spechtInclude μ).comp f.symm.toLinearMap)
    · intro g v
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [show f.symm (spechtRep ν g v) =
        spechtRep μ (e.symm.permCongr g) (f.symm v) from by
          apply f.injective
          rw [LinearEquiv.apply_symm_apply, hf, LinearEquiv.apply_symm_apply]
          congr 2
          exact (e.permCongr.apply_symm_apply g).symm]
      exact spechtInclude_rep μ _ _
    · intro hz
      apply spechtPoly_ne_zero ν
      apply f.symm.injective
      apply spechtInclude_injective μ
      simpa using hz

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungPartition
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps.Young

lemma diagram_rowLens {n : ℕ} (p : n.Partition) :
    (diagram p).rowLens = p.parts.sort (· ≥ ·) := by
  apply YoungDiagram.rowLens_ofRowLens_eq_self
  intro x hx
  apply p.parts_pos
  simpa only [Multiset.mem_sort] using hx

lemma diagram_injective {n : ℕ} : Function.Injective (diagram (n := n)) := by
  intro p q h
  apply Nat.Partition.ext
  have hh := congrArg (fun μ => (μ.rowLens : Multiset ℕ)) h
  simpa only [diagram_rowLens, Multiset.sort_eq] using hh

lemma conjPartition_injective {X : Type*} [Fintype X] [DecidableEq X] :
    Function.Injective (conjPartition (X := X)) := by
  intro c d
  obtain ⟨c, rfl⟩ := ConjClasses.mk_surjective c
  obtain ⟨d, rfl⟩ := ConjClasses.mk_surjective d
  intro h
  exact ConjClasses.mk_eq_mk_iff_isConj.mpr (Equiv.Perm.partition_eq_of_isConj.mpr h)

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungFinite
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.hilbertInner _root_.OAI.BinaryCoordinateSweeps.Young.hilbertNormed _root_.OAI.BinaryCoordinateSweeps.Young.instIsIrreducibleGComplexSubtypeEuclideanSpaceElemForallCellNatTabloidMemSubmoduleSpechtHilbertHilbertSpecht _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps.Young

instance instIsIrreduciblePermFinComplexPartitionSpacePartitionRep {n : ℕ} (p : n.Partition) :
    Representation.IsIrreducible (k := ℂ) (G := Equiv.Perm (Fin n))
      (V := PartitionSpace p) (partitionRep p) :=
  Irrep.irreducible_comp_equiv _ _

lemma partitionRep_apply {n : ℕ} (p : n.Partition) (g : Equiv.Perm (Fin n))
    (v : PartitionSpace p) : partitionRep p g v =
      spechtRep (diagram p) ((cellsEquivFin p).symm.permCongr g) v := rfl

lemma partitionRep_equiv_injective {n : ℕ} (p q : n.Partition)
    (f : Representation.Equiv (partitionRep p) (partitionRep q)) : p = q := by
  apply diagram_injective
  let e := (cellsEquivFin p).trans (cellsEquivFin q).symm
  apply equivalence_implies_diagram_eq e f.toLinearEquiv
  intro g v
  have h := Representation.IntertwiningMap.isIntertwining
    (partitionRep p) (partitionRep q) f.toIntertwiningMap ((cellsEquivFin p).permCongr g) v
  simp only [partitionRep_apply] at h
  change f.toLinearEquiv _ = _ at h
  have hep : ((cellsEquivFin p).symm.permCongr ((cellsEquivFin p).permCongr g)) = g :=
    (cellsEquivFin p).permCongr.symm_apply_apply g
  rw [hep] at h
  rw [h]
  congr 2

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungClassification
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.hilbertInner _root_.OAI.BinaryCoordinateSweeps.Young.hilbertNormed _root_.OAI.BinaryCoordinateSweeps.Young.instIsIrreducibleGComplexSubtypeEuclideanSpaceElemForallCellNatTabloidMemSubmoduleSpechtHilbertHilbertSpecht _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps.Young

theorem partitionRep_complete {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) [ρ.IsIrreducible] :
    ∃ p : n.Partition, Nonempty (Representation.Equiv ρ (partitionRep p)) := by
  refine Irrep.complete_of_card_ge (G := Equiv.Perm (Fin n))
    (V := fun p : n.Partition => PartitionSpace p)
    (fun p : n.Partition => partitionRep p) ?_ ?_ ρ
  · intro p q ⟨f⟩
    exact partitionRep_equiv_injective p q f
  · let : Fintype (ConjClasses (Equiv.Perm (Fin n))) := Fintype.ofFinite _
    have h := Fintype.card_le_of_injective (conjPartition (X := Fin n)) conjPartition_injective
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using h

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungResolution
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
open Representation

instance instIsIrreduciblePermFinComplexSubtypeEuclideanSpaceElemForallCellDiagramNatTabloidMemSubmodulePartitionHilbertPartitionHilbertRep {n : ℕ} (p : n.Partition) : (partitionHilbertRep p).IsIrreducible :=
  Irrep.irreducible_comp_equiv _ _

lemma partitionHilbertRep_unitary {n : ℕ} (p : n.Partition)
    (g : Equiv.Perm (Fin n)) (v : PartitionHilbert p) :
    ‖partitionHilbertRep p g v‖=‖v‖ := hilbertSpecht_unitary _ _ _

lemma partitionHilbertRep_equiv_injective {n : ℕ} (p q : n.Partition)
    (e : (partitionHilbertRep p).Equiv (partitionHilbertRep q)) : p=q :=
  partitionRep_equiv_injective p q
    ((partitionHilbertEquiv p).trans (e.trans (partitionHilbertEquiv q).symm))

lemma partitionHilbertRep_complete {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (σ : Representation ℂ (Equiv.Perm (Fin n)) W)
    [σ.IsIrreducible] : ∃ p : n.Partition, Nonempty (σ.Equiv (partitionHilbertRep p)) := by
  obtain ⟨p,⟨e⟩⟩ := partitionRep_complete σ
  exact ⟨p,⟨e.trans (partitionHilbertEquiv p)⟩⟩

lemma partition_isotypic_top {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (σ : Representation ℂ (Equiv.Perm (Fin n)) W) :
    (⨆ p : n.Partition, Irrep.isotypicSpan (partitionHilbertRep p) σ)=⊤ := by
  apply Irrep.iSup_isotypic_eq_top σ (fun p => partitionHilbertRep p)
  intro U _ _ _ τ hτ
  have := hτ
  exact partitionHilbertRep_complete τ

lemma partition_isotypic_orthogonal {n : ℕ} {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ (Equiv.Perm (Fin n)) W)
    (hσ : ∀ g v, ‖σ g v‖=‖v‖) :
    OrthogonalFamily ℂ (fun p : n.Partition => Irrep.isotypicSpan (partitionHilbertRep p) σ)
      (fun p => (Irrep.isotypicSpan (partitionHilbertRep p) σ).subtypeₗᵢ) := by
  apply OrthogonalFamily.of_pairwise
  intro p q hpq
  apply Irrep.isotypic_orthogonal (partitionHilbertRep q) (partitionHilbertRep p) σ
    (partitionHilbertRep_unitary q) (partitionHilbertRep_unitary p) hσ
  rintro ⟨e⟩
  exact hpq (partitionHilbertRep_equiv_injective q p e).symm

theorem partition_projection_sum {n : ℕ} {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ (Equiv.Perm (Fin n)) W)
    (hσ : ∀ g v, ‖σ g v‖=‖v‖) (v : W) :
    (∑ p : n.Partition, (Irrep.isotypicSpan (partitionHilbertRep p) σ).starProjection v)=v := by
  apply (partition_isotypic_orthogonal σ hσ).sum_projection_of_mem_iSup
  rw [partition_isotypic_top]
  trivial

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators Classical
open Equiv Equiv.Perm Finset

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Representations_IsotypicProjectionMoment
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical ComplexOrder MonoidAlgebra
open Matrix

namespace BinaryCoordinateSweeps
open Density Irrep Representation

lemma trace_mul_projection {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] (S : Submodule ℂ W) (B : W →ₗ[ℂ] W)
    (hS : ∀w∈S, B w∈S) :
    LinearMap.trace ℂ W (B*S.starProjection.toLinearMap)=
      LinearMap.trace ℂ S (B.restrict hS) := by
  have hm (w : W) : (B*S.starProjection.toLinearMap) w∈S :=
    hS _ (S.starProjection_apply_mem w)
  have he : (B*S.starProjection.toLinearMap).restrict (fun w _ => hm w)=B.restrict hS := by
    ext w
    change B (S.starProjection w.val)=B w.val
    rw [Submodule.starProjection_eq_self_iff.mpr w.property]
  rw [← LinearMap.trace_restrict_eq_of_forall_mem S _ hm,he]

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Fourier
open Representation

variable (G : Type*) [Group G] [Fintype G]

lemma regular_unitary (g : G) (v : RegularSpace G) : ‖regular G g v‖=‖v‖ := by
  simp only [EuclideanSpace.norm_eq]
  congr 1
  exact Equiv.sum_comp (Equiv.mulLeft g⁻¹) (fun x => ‖v x‖^2)

lemma regular_character (g : G) :
    (regular G).character g=if g=1 then (Fintype.card G:ℂ) else 0 := by
  rw [Representation.character,LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun G ℂ)]
  by_cases hg : g=1
  · subst g; simp
  · rw [ite_eq_right hg]
    apply Finset.sum_eq_zero
    intro x _
    rw [EuclideanSpace.basisFun_inner,regular_apply,EuclideanSpace.basisFun_apply]
    simp only [PiLp.single_apply]
    have hh : g⁻¹*x≠x := by
      intro he
      have := mul_right_cancel (show g⁻¹*x=1*x from by simpa using he)
      exact hg (inv_eq_one.mp this)
    simp [hh]

lemma regular_multiplicity {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) :
    Module.finrank ℂ (IntertwiningMap ρ (regular G))=Module.finrank ℂ V := by
  have hc : (Nat.card G:ℂ)≠0 := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_ne_zero
  let : Invertible (Nat.card G:ℂ) := invertibleOfNonzero hc
  have hh := card_inv_mul_sum_char_mul_char_eq_finrank ρ (regular G)
  simp only [regular_character,ite_mul,zero_mul] at hh
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true,inv_one,char_one] at hh
  rw [←Nat.card_eq_fintype_card,←mul_assoc,inv_mul_cancel₀ hc,one_mul] at hh
  exact_mod_cast hh.symm

lemma regular_average_apply (p : G → ℂ) (v : RegularSpace G) (x : G) :
    Irrep.groupAverage (regular G) p v x=∑g,p g*v (g⁻¹*x) := by
  simp [Irrep.groupAverage,LinearMap.sum_apply,LinearMap.smul_apply]

lemma regular_moment_one (p : G → ℂ) :
    Irrep.evenMoment 1 (Irrep.groupAverage (regular G) p)=
      (Fintype.card G:ℝ)*(∑g,‖p g‖^2) := by
  unfold Irrep.evenMoment
  rw [pow_one,LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun G ℂ)]
  simp only [Complex.re_sum,Module.End.mul_apply,LinearMap.adjoint_inner_right,inner_self_eq_norm_sq_to_K]
  have he (x : G) : ‖Irrep.groupAverage (regular G) p ((EuclideanSpace.basisFun G ℂ) x)‖^2=
      ∑g,‖p g‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    have ha (y : G) : Irrep.groupAverage (regular G) p ((EuclideanSpace.basisFun G ℂ) x) y=p (y*x⁻¹) := by
      rw [regular_average_apply]
      simp only [EuclideanSpace.basisFun_apply,PiLp.single_apply]
      have hiff (g : G) : x=g⁻¹*y ↔ g=y*x⁻¹ := by
        constructor <;> intro hh
        · calc g=(g*x)*x⁻¹ := by group
                 _=y*x⁻¹ := by rw [hh]; simp
        · subst g; group
      simp_rw [eq_comm (a:=_⁻¹*y) (b:=x),hiff,mul_ite,mul_one,mul_zero]
      simp
    simp_rw [ha]
    exact Equiv.sum_comp (Equiv.mulRight x⁻¹) (fun g => ‖p g‖^2)
  change (∑i, ((‖Irrep.groupAverage (regular G) p ((EuclideanSpace.basisFun G ℂ) i)‖:ℂ)^2).re)=_
  simp only [←Complex.ofReal_pow,Complex.ofReal_re]
  simp_rw [he]
  simp

end BinaryCoordinateSweeps.Fourier

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_GroupedLogBounds
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical MonoidAlgebra ComplexOrder Matrix.Norms.L2Operator
open Matrix

namespace BinaryCoordinateSweeps.Signed
open Density Irrep Representation TraceHolder

variable {A I : Type*} [Fintype A] [DecidableEq A] [Fintype I] [LinearOrder I]
  {n : I → ℕ} {N : ℕ}
  {V : I → Type*} [∀i, NormedAddCommGroup (V i)]
  [∀i, InnerProductSpace ℂ (V i)] [∀i, FiniteDimensional ℂ (V i)]

lemma irreducible_finrank_pos {G W : Type*} [Group G]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G W) [ρ.IsIrreducible] : 0<Module.finrank ℂ W := by
  let : Nontrivial ρ.asModule := IsSimpleModule.nontrivial ℂ[G] ρ.asModule
  rw [← ρ.asModuleEquiv.finrank_eq]
  exact Module.finrank_pos

end BinaryCoordinateSweeps.Signed

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungInducedMap
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.instIsIrreduciblePermFinComplexPartitionSpacePartitionRep _root_.OAI.BinaryCoordinateSweeps.Young.instIsIrreduciblePermFinComplexSubtypeEuclideanSpaceElemForallCellDiagramNatTabloidMemSubmodulePartitionHilbertPartitionHilbertRep _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
variable (μ : YoungDiagram)
variable {V : Type*} [AddCommMonoid V] [Module ℂ V]

lemma spechtPoly_column (c : C μ) :
    spechtRep μ c.val (spechtPoly μ) = signC μ c.val • spechtPoly μ := by
  apply spechtInclude_injective μ
  simp only [spechtInclude_rep, spechtInclude_poly, map_smul]
  have he : tabloidRepresentation μ c.val (polytabloid μ) =
      signC μ c.val • polytabloid μ := by
    unfold polytabloid
    rw [columnAnti_apply, map_sum]
    have hh := Equiv.sum_comp (Equiv.mulLeft c)
      (fun d : C μ => signC μ c.val • (signC μ d.val •
        tabloidRepresentation μ d.val (tabloidBasis μ (tabloidOfPerm μ 1))))
    rw [Finset.smul_sum, ← hh]
    apply Finset.sum_congr rfl
    intro d hd
    change tabloidRepresentation μ c.val
      (signC μ d.val • tabloidRepresentation μ d.val (tabloidBasis μ (tabloidOfPerm μ 1))) =
      signC μ c.val • (signC μ (c*d).val •
        tabloidRepresentation μ (c*d).val (tabloidBasis μ (tabloidOfPerm μ 1)))
    simp only [map_smul, Subgroup.coe_mul, map_mul, Module.End.mul_apply, smul_smul]
    rw [show signC μ c.val * (signC μ c.val * signC μ d.val) = signC μ d.val from by
      rw [← mul_assoc, signC_sq, one_mul]]
  exact he

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators Classical
open Equiv Equiv.Perm

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_OneCard
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable

lemma coordinateLayer_apply_at (d : ℕ) (j : Fin d)
    (c : ({i : Fin d // i≠j} → Bool) → Bool) (x : Slot d) :
    coordinateLayer d j c x j = (x j ^^ c (fun i => x i)) := by
  simp [coordinateLayer,Equiv.piSplitAt_symm_apply]

lemma coordinateLayer_apply_other (d : ℕ) (j i : Fin d) (hi : i≠j)
    (c : ({i : Fin d // i≠j} → Bool) → Bool) (x : Slot d) :
    coordinateLayer d j c x i = x i := by
  simp [coordinateLayer,Equiv.piSplitAt_symm_apply,hi]

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_GridSplitWeights
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.GridSplit

section
variable {m n h : ℕ} (bits : Fin (m+n) → ℕ)

lemma gridWeight_split (z : ℝ) (g : GridChoices bits) :
    gridWeight bits z g =
      (∏y : GridSlot (rightBits bits), gridWeight (leftBits bits) z (rowChoices bits g y)) *
      (∏x : GridSlot (leftBits bits), gridWeight (rightBits bits) z (columnChoices bits g x)) := by
  unfold gridWeight
  rw [Fin.prod_univ_add]
  congr 1
  · rw [Finset.prod_comm]
    apply Finset.prod_congr rfl
    intro j _
    have he := (leftOutsideEquiv bits j).symm.prod_comp (fun u => lineLaw (bits (j.castAdd n)) z (g (j.castAdd n) u))
    rw [Fintype.prod_prod_type] at he
    exact he.symm
  · rw [Finset.prod_comm]
    apply Finset.prod_congr rfl
    intro j _
    have he := (rightOutsideEquiv bits j).symm.prod_comp (fun u => lineLaw (bits (j.natAdd m)) z (g (j.natAdd m) u))
    rw [Fintype.prod_prod_type] at he
    exact he.symm

end

end BinaryCoordinateSweeps.GridSplit

end

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_GridSplitSweep
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.GridSplit

variable {X Y : Type*}

variable {m n : ℕ} (bits : Fin (m+n) → ℕ)

lemma gridLayer_left (g : GridChoices bits) (j : Fin m) (x : GridSlot bits) :
    (slotEquiv bits) (gridLayer bits g (j.castAdd n) x) =
      (gridLayer (leftBits bits) (rowChoices bits g (rightSlot bits x)) j (leftSlot bits x),
        rightSlot bits x) := by
  apply Prod.ext
  · simp only
    funext i
    change gridLayer bits g (j.castAdd n) x (i.castAdd n)=_
    by_cases hi : i=j
    · subst i
      rw [gridLayer_at,gridLayer_at,rowChoices_at]
      rfl
    · rw [gridLayer_other bits g _ _ (fun he => hi (Fin.castAdd_injective m n he)),
        gridLayer_other _ _ _ _ hi]
      rfl
  · funext i
    exact gridLayer_other bits g _ _ (by
      intro he
      have hh := congrArg (fun i : Fin (m+n) => i.val) he
      simp only [Fin.val_natAdd,Fin.val_castAdd] at hh; omega) x

lemma gridLayer_right (g : GridChoices bits) (j : Fin n) (x : GridSlot bits) :
    (slotEquiv bits) (gridLayer bits g (j.natAdd m) x) =
      (leftSlot bits x,
        gridLayer (rightBits bits) (columnChoices bits g (leftSlot bits x)) j (rightSlot bits x)) := by
  apply Prod.ext
  · funext i
    exact gridLayer_other bits g _ _ (by
      intro he
      have hh := congrArg (fun i : Fin (m+n) => i.val) he
      simp only [Fin.val_natAdd,Fin.val_castAdd] at hh; omega) x
  · simp only
    funext i
    change gridLayer bits g (j.natAdd m) x (i.natAdd m)=_
    by_cases hi : i=j
    · subst i
      rw [gridLayer_at,gridLayer_at,columnChoices_at]
      rfl
    · rw [gridLayer_other bits g _ _ (fun he => hi (Fin.natAdd_injective n m he)),
        gridLayer_other _ _ _ _ hi]
      rfl

lemma layer_left_congr (g : GridChoices bits) (j : Fin m) :
    (slotEquiv bits).permCongr (gridLayer bits g (j.castAdd n)) =
      rowPerm (fun y => gridLayer (leftBits bits) (rowChoices bits g y) j) := by
  apply Equiv.ext
  intro xy
  have he := gridLayer_left bits g j ((slotEquiv bits).symm xy)
  change (slotEquiv bits) (gridLayer bits g (j.castAdd n) ((slotEquiv bits).symm xy))= _
  rw [he]
  have ht := (slotEquiv bits).apply_symm_apply xy
  rw [show leftSlot bits ((slotEquiv bits).symm xy)=xy.1 from congrArg Prod.fst ht,
    show rightSlot bits ((slotEquiv bits).symm xy)=xy.2 from congrArg Prod.snd ht]
  rfl

lemma layer_right_congr (g : GridChoices bits) (j : Fin n) :
    (slotEquiv bits).permCongr (gridLayer bits g (j.natAdd m)) =
      columnPerm (fun x => gridLayer (rightBits bits) (columnChoices bits g x) j) := by
  apply Equiv.ext
  intro xy
  have he := gridLayer_right bits g j ((slotEquiv bits).symm xy)
  change (slotEquiv bits) (gridLayer bits g (j.natAdd m) ((slotEquiv bits).symm xy))= _
  rw [he]
  have ht := (slotEquiv bits).apply_symm_apply xy
  rw [show leftSlot bits ((slotEquiv bits).symm xy)=xy.1 from congrArg Prod.fst ht,
    show rightSlot bits ((slotEquiv bits).symm xy)=xy.2 from congrArg Prod.snd ht]
  rfl

lemma prod_rows (L : List (Y → Equiv.Perm X)) :
    (L.map rowPerm).prod=rowPerm (fun y => (L.map (fun f => f y)).prod) := by
  induction L with
  | nil => rfl
  | cons f L ih =>
    simp only [List.map_cons,List.prod_cons,ih]
    apply Equiv.ext
    intro xy
    rfl
lemma prod_columns (L : List (X → Equiv.Perm Y)) :
    (L.map columnPerm).prod=columnPerm (fun x => (L.map (fun f => f x)).prod) := by
  induction L with
  | nil => rfl
  | cons f L ih =>
    simp only [List.map_cons,List.prod_cons,ih]
    apply Equiv.ext
    intro xy
    rfl

theorem gridSweep_split (g : GridChoices bits) :
    (slotEquiv bits).permCongr (gridSweep bits g) =
      columnPerm (fun x => gridSweep (rightBits bits) (columnChoices bits g x)) *
        rowPerm (fun y => gridSweep (leftBits bits) (rowChoices bits g y)) := by
  change (slotEquiv bits).permCongrHom (gridSweep bits g)=_
  unfold gridSweep
  rw [List.ofFn_add,List.reverse_append,List.prod_append]
  rw [map_mul]
  congr 1
  · rw [map_list_prod (slotEquiv bits).permCongrHom,List.map_reverse,List.map_ofFn]
    change (List.ofFn (fun j : Fin n => (slotEquiv bits).permCongr (gridLayer bits g (j.natAdd m)))).reverse.prod=_
    simp_rw [layer_right_congr]
    simpa only [List.map_reverse,List.map_ofFn,Function.comp_def] using
      (prod_columns (List.ofFn (fun j : Fin n => fun x =>
        gridLayer (rightBits bits) (columnChoices bits g x) j)).reverse)
  · rw [map_list_prod (slotEquiv bits).permCongrHom,List.map_reverse,List.map_ofFn]
    change (List.ofFn (fun j : Fin m => (slotEquiv bits).permCongr (gridLayer bits g (j.castAdd n)))).reverse.prod=_
    simp_rw [layer_left_congr]
    simpa only [List.map_reverse,List.map_ofFn,Function.comp_def] using
      (prod_rows (List.ofFn (fun j : Fin m => fun y =>
        gridLayer (leftBits bits) (rowChoices bits g y) j)).reverse)

end BinaryCoordinateSweeps.GridSplit

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungDimensionLower
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.hilbertInner _root_.OAI.BinaryCoordinateSweeps.Young.hilbertNormed _root_.OAI.BinaryCoordinateSweeps.Young.instIsIrreducibleGComplexSubtypeEuclideanSpaceElemForallCellNatTabloidMemSubmoduleSpechtHilbertHilbertSpecht _root_.OAI.BinaryCoordinateSweeps.Young.instIsIrreduciblePermFinComplexPartitionSpacePartitionRep _root_.OAI.BinaryCoordinateSweeps.Young.instIsIrreduciblePermFinComplexSubtypeEuclideanSpaceElemForallCellDiagramNatTabloidMemSubmodulePartitionHilbertPartitionHilbertRep _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
variable (μ : YoungDiagram)

lemma two_pow_card_sub_diagonal_le_dimension (L : ℕ)
    (hL : ∀ x : Cell μ, diagonal μ x < L) :
    2^(Fintype.card (Cell μ)-L) ≤ Module.finrank ℂ (SpechtSpace μ) := by
  let f : Cell μ → Fin L := fun x => ⟨diagonal μ x,hL x⟩
  have hf : fiberStabilizer f = diagonalStabilizer μ := by
    ext g
    constructor
    · intro hg x; exact congrArg Fin.val (hg x)
    · intro hg x; exact Fin.ext (hg x)
  have hb := two_pow_card_sub_colors_le_stabilizer f
  rw [Fintype.card_fin, hf, Nat.card_eq_fintype_card] at hb
  exact hb.trans (diagonal_card_le_dimension μ)

theorem log_dimension_lower :
    (Real.log 2 / 2) *
      (Fintype.card (Cell μ) - max (μ.colLen 0) (μ.rowLen 0) : ℕ) ≤
      Real.log (Module.finrank ℂ (SpechtSpace μ)) := by
  let N := Fintype.card (Cell μ)
  let W := max (μ.colLen 0) (μ.rowLen 0)
  let L := (N+W)/2
  have hWN : W ≤ N := height_width_le_card μ
  have hLN : L ≤ N := by dsimp only [L]; omega
  have hnat : N-W ≤ 2*(N-L) := by dsimp only [L]; omega
  have hr : ((N-W : ℕ) : ℝ) ≤ 2*((N-L : ℕ) : ℝ) := by exact_mod_cast hnat
  have hb := two_pow_card_sub_diagonal_le_dimension μ L (diagonal_lt_half_card_add_max μ)
  have hbr : (2 : ℝ)^(N-L) ≤ (Module.finrank ℂ (SpechtSpace μ) : ℝ) := by exact_mod_cast hb
  have hlog := Real.log_le_log (show (0 : ℝ) < 2^(N-L) from by positivity) hbr
  rw [Real.log_pow] at hlog
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  change (Real.log 2 / 2) * ((N-W : ℕ) : ℝ) ≤ _
  nlinarith

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungTranspose
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.instIsIrreduciblePermFinComplexPartitionSpacePartitionRep _root_.OAI.BinaryCoordinateSweeps.Young.instIsIrreduciblePermFinComplexSubtypeEuclideanSpaceElemForallCellDiagramNatTabloidMemSubmodulePartitionHilbertPartitionHilbertRep _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
variable (μ : YoungDiagram)
variable {V : Type*} [AddCommMonoid V] [Module ℂ V]

lemma transpose_sign (g : G μ) : signC μ.transpose ((transposeCells μ).permCongr g) =
    signC μ g := by rw [signC_eq, signC_eq, Equiv.Perm.sign_permCongr]

lemma transpose_row_to_col (r : rowStabilizer μ) :
    (transposeCells μ).permCongr r.val ∈ colStabilizer μ.transpose := by
  intro x
  exact r.property ((transposeCells μ).symm x)

lemma transpose_col_to_row (c : C μ) :
    (transposeCells μ).permCongr c.val ∈ rowStabilizer μ.transpose := by
  intro x
  exact c.property ((transposeCells μ).symm x)

instance instIsIrreducibleGComplexSpechtSpaceTransposeTransposeRep : Representation.IsIrreducible (k := ℂ) (G := G μ)
    (V := SpechtSpace μ.transpose) (transposeRep μ) :=
  Irrep.irreducible_comp_equiv _ _

lemma transposePoly_row_fixed (r : rowStabilizer μ) :
    signTwist (V := SpechtSpace μ.transpose) μ (transposeRep μ) r.val (spechtPoly μ.transpose) = spechtPoly μ.transpose := by
  change signC μ r.val • spechtRep μ.transpose ((transposeCells μ).permCongr r.val)
    (spechtPoly μ.transpose) = _
  rw [spechtPoly_column μ.transpose ⟨_,transpose_row_to_col μ r⟩,
    transpose_sign, smul_smul, signC_sq, one_smul]

lemma transposeMap_intertwines (g : G μ) (v : SpechtSpace μ) :
    transposeMap μ (spechtRep μ g v) =
      signTwist (V := SpechtSpace μ.transpose) μ (transposeRep μ) g (transposeMap μ v) := by
  simp only [transposeMap, LinearMap.comp_apply, spechtInclude_rep]
  exact fromTabloid_intertwines μ _ _ (transposePoly_row_fixed μ) g _

lemma row_fixes_base_evaluation (r : rowStabilizer μ) (v : Tabloid μ → ℂ) :
    tabloidRepresentation μ r.val v (tabloidOfPerm μ 1) = v (tabloidOfPerm μ 1) := by
  change v (r.val⁻¹ • tabloidOfPerm μ 1) = _
  rw [smul_tabloidOfPerm, mul_one]
  congr 1
  exact (tabloidOfPerm_eq_iff μ _ _).mpr (by simp [r.property])

lemma transposeMap_poly_evaluation : spechtInclude μ.transpose
    (transposeMap μ (spechtPoly μ)) (tabloidOfPerm μ.transpose 1) = Fintype.card (C μ) := by
  change spechtInclude μ.transpose
    (fromTabloid μ (signTwist (V := SpechtSpace μ.transpose) μ (transposeRep μ)) (spechtPoly μ.transpose)
      (spechtInclude μ (spechtPoly μ))) _ = _
  rw [spechtInclude_poly, polytabloid, columnAnti_apply, map_sum]
  simp only [map_smul, rep_basis, smul_tabloidOfPerm, mul_one, fromTabloid_basis]
  simp_rw [tabloidVector_eq μ _ _ (transposePoly_row_fixed μ)]
  have ht (c : C μ) : signC μ c.val • signTwist (V := SpechtSpace μ.transpose) μ (transposeRep μ) c.val
      (spechtPoly μ.transpose) = spechtRep μ.transpose ((transposeCells μ).permCongr c.val)
        (spechtPoly μ.transpose) := by
    change signC μ c.val • (signC μ c.val •
      spechtRep μ.transpose ((transposeCells μ).permCongr c.val) (spechtPoly μ.transpose)) = _
    rw [smul_smul, signC_sq, one_smul]
  simp_rw [ht]
  rw [map_sum]
  simp only [Finset.sum_apply, spechtInclude_rep, spechtInclude_poly]
  have he (c : C μ) : tabloidRepresentation μ.transpose ((transposeCells μ).permCongr c.val)
      (polytabloid μ.transpose) (tabloidOfPerm μ.transpose 1) = 1 := by
    rw [row_fixes_base_evaluation μ.transpose ⟨_,transpose_col_to_row μ c⟩,
      polytabloid_base]
  simp only [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

theorem specht_transpose_sign : Nonempty (Representation.Equiv (spechtRep μ)
    (signTwist (V := SpechtSpace μ.transpose) μ (transposeRep μ))) := by
  let f := (transposeMap μ).intertwiningMap_of_isIntertwiningMap
    (spechtRep μ) (signTwist (V := SpechtSpace μ.transpose) μ (transposeRep μ)) (transposeMap_intertwines μ)
  have hn : f ≠ 0 := by
    intro h
    have hz : transposeMap μ (spechtPoly μ) = 0 := by
      exact congrArg (fun g : Representation.IntertwiningMap (spechtRep μ)
        (signTwist (V := SpechtSpace μ.transpose) μ (transposeRep μ)) => g (spechtPoly μ)) h
    have he := transposeMap_poly_evaluation μ
    rw [hz, map_zero, Pi.zero_apply] at he
    exact (Nat.cast_ne_zero.mpr Fintype.card_ne_zero : (Fintype.card (C μ) : ℂ) ≠ 0) he.symm
  have : (signTwist μ (transposeRep μ)).IsIrreducible :=
    signTwist_irreducible μ (transposeRep μ)
  have hf := (Representation.IsIrreducible.bijective_or_eq_zero (k := ℂ) (G := G μ)
    (V := SpechtSpace μ) (W := SpechtSpace μ.transpose) f).resolve_right hn
  exact ⟨f.ofBijective hf⟩

lemma specht_finrank_transpose : Module.finrank ℂ (SpechtSpace μ) =
    Module.finrank ℂ (SpechtSpace μ.transpose) := by
  obtain ⟨e⟩ := specht_transpose_sign μ
  exact e.toLinearEquiv.finrank_eq

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Representations_IrrepSupport
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators MonoidAlgebra

namespace BinaryCoordinateSweeps
namespace Irrep

variable {G V : Type*} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  (ρ : Representation ℂ G V) [ρ.IsIrreducible]

omit [Fintype G] [FiniteDimensional ℂ V] in
lemma invariant_eq_zero_of_finrank_gt_one (hD : 1 < Module.finrank ℂ V)
    (v : V) (hv : ∀ g, ρ g v = v) : v = 0 := by
  let f : Representation.IntertwiningMap (1 : Representation ℂ G ℂ) ρ :=
    (LinearMap.toSpanSingleton ℂ V v).intertwiningMap_of_isIntertwiningMap _ _ (by
      intro g c
      simp only [MonoidHom.one_apply, Module.End.one_apply, LinearMap.toSpanSingleton_apply,
        map_smul, hv])
  rcases Representation.IsIrreducible.surjective_or_eq_zero f with hf | hf
  · have hd := LinearMap.finrank_le_finrank_of_surjective (f := f.toLinearMap) hf
    simp only [Module.finrank_self] at hd
    omega
  · have hh := congrArg (fun a : Representation.IntertwiningMap
        (1 : Representation ℂ G ℂ) ρ => a (1 : ℂ)) hf
    simpa [f] using hh

omit [FiniteDimensional ℂ V] in
lemma sum_apply_eq_zero_of_finrank_gt_one (hD : 1 < Module.finrank ℂ V) (x : V) :
    ∑ g : G, ρ g x = 0 := by
  apply invariant_eq_zero_of_finrank_gt_one ρ hD
  intro g
  simp only [map_sum, ← Module.End.mul_apply, ← map_mul]
  exact Function.Bijective.sum_comp (Group.mulLeft_bijective g) (fun h : G => ρ h x)

omit [FiniteDimensional ℂ V] in
lemma sum_eq_zero_of_finrank_gt_one (hD : 1 < Module.finrank ℂ V) :
    ∑ g : G, ρ g = 0 := by
  ext x
  simpa using sum_apply_eq_zero_of_finrank_gt_one ρ hD x

end Irrep
end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Analytic_OneAxis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable

lemma oneAxis_gridWeight (bits : Fin 1 → ℕ) (z : ℝ) (g : GridChoices bits) :
    gridWeight bits z g = lineLaw (bits 0) z (oneAxisChoiceEquiv bits g) := by
  simp [gridWeight, oneAxisChoiceEquiv, Equiv.piUnique, Equiv.funUnique]

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Conditional_ConditionalSpecht
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Young Irrep

variable {b h k r : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

lemma groupAverage_comp_slots {X Y V : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (e : X ≃ Y) (ρ : Representation ℂ (Equiv.Perm X) V) (p : Equiv.Perm Y → ℂ) :
    groupAverage (ρ.comp e.symm.permCongrHom.toMonoidHom) p =
      groupAverage ρ (fun g => p (e.permCongr g)) := by
  unfold groupAverage
  rw [← Equiv.sum_comp e.permCongr]
  apply Finset.sum_congr rfl
  intro g _
  congr 1
  change ρ (e.permCongr.symm (e.permCongr g))=ρ g
  rw [Equiv.symm_apply_apply]

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical
open Filter Topology

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_HilbertTranspose
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.instIsIrreduciblePermFinComplexPartitionSpacePartitionRep _root_.OAI.BinaryCoordinateSweeps.Young.instIsIrreduciblePermFinComplexSubtypeEuclideanSpaceElemForallCellDiagramNatTabloidMemSubmodulePartitionHilbertPartitionHilbertRep _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
open Irrep Representation

variable (μ : YoungDiagram)

lemma norm_signC (g : G μ) : ‖signC μ g‖=1 := by
  have h := congrArg Norm.norm (signC_sq μ g)
  rw [norm_mul,norm_one] at h
  nlinarith [norm_nonneg (signC μ g)]

lemma hilbert_transpose_equiv : Nonempty ((hilbertSpecht μ).Equiv
    (signTwist μ ((hilbertSpecht μ.transpose).comp (transposeCells μ).permCongrHom.toMonoidHom))) := by
  obtain ⟨f⟩ := specht_transpose_sign μ
  let E := (spechtHilbertEquiv μ).symm.trans (f.toLinearEquiv.trans (spechtHilbertEquiv μ.transpose))
  refine ⟨.mk E ?_⟩
  intro g
  apply LinearMap.ext
  intro v
  obtain ⟨w,rfl⟩ := (spechtHilbertEquiv μ).surjective v
  change spechtHilbertEquiv μ.transpose
      (f.toLinearEquiv.toFun ((spechtHilbertEquiv μ).symm.toFun
        (spechtHilbertEquiv μ (spechtRep μ g ((spechtHilbertEquiv μ).symm.toFun
          (spechtHilbertEquiv μ w)))))) =
    signC μ g • spechtHilbertEquiv μ.transpose
      (spechtRep μ.transpose ((transposeCells μ).permCongr g)
        ((spechtHilbertEquiv μ.transpose).symm.toFun
          (spechtHilbertEquiv μ.transpose (f.toLinearEquiv.toFun
            ((spechtHilbertEquiv μ).symm.toFun (spechtHilbertEquiv μ w))))))
  have hs (ν : YoungDiagram) (x : SpechtSpace ν) :
      (spechtHilbertEquiv ν).symm.toFun (spechtHilbertEquiv ν x) = x :=
    (spechtHilbertEquiv ν).symm_apply_apply x
  simp only [hs]
  have h := Representation.IntertwiningMap.isIntertwining _ _ f.toIntertwiningMap g w
  change f.toLinearEquiv.toFun (spechtRep μ g w) = signC μ g •
    spechtRep μ.transpose ((transposeCells μ).permCongr g) (f.toLinearEquiv.toFun w) at h
  exact (congrArg (spechtHilbertEquiv μ.transpose).toFun h).trans (map_smul _ _ _)

lemma hilbert_transpose_moment (p : G μ → ℂ) (q : ℕ) :
    evenMoment q (groupAverage (hilbertSpecht μ) p) =
      evenMoment q (groupAverage (hilbertSpecht μ.transpose)
        (fun g => p ((transposeCells μ).symm.permCongr g)*signC μ.transpose g)) := by
  obtain ⟨f⟩ := hilbert_transpose_equiv μ
  rw [equivalent_evenMoment _ _ f (hilbertSpecht_unitary μ) (fun g v => by
    change ‖signC μ g • hilbertSpecht μ.transpose ((transposeCells μ).permCongr g) v‖=‖v‖
    rw [norm_smul,norm_signC,hilbertSpecht_unitary,one_mul])]
  congr 1
  unfold groupAverage
  rw [←Equiv.sum_comp (transposeCells μ).permCongr]
  apply Finset.sum_congr rfl
  intro g _
  change p g • (signC μ g • hilbertSpecht μ.transpose ((transposeCells μ).permCongr g)) = _
  dsimp only
  rw [smul_smul,transpose_sign]
  rw [show (transposeCells μ).symm.permCongr ((transposeCells μ).permCongr g)=g from
    (transposeCells μ).permCongr.symm_apply_apply g]

end BinaryCoordinateSweeps.Young
namespace BinaryCoordinateSweeps
open Young Irrep

lemma realSign_permCongr_complex {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (e : X≃Y) (g : Equiv.Perm X) :
    (realSign (e.permCongr g):ℂ)=(realSign g:ℂ) := by
  exact congrArg (fun sign : ℤˣ => (((sign : ℤ) : ℝ) : ℂ))
    (Equiv.Perm.sign_permCongr e g)

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_AssignmentSign
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
variable {I X : Type*} [Fintype I] [Fintype X] [DecidableEq X]

lemma realSign_swap {u v : X} (huv : u≠v) : realSign (Equiv.swap u v) = -1 := by
  simp [realSign,Equiv.Perm.sign_swap huv]

omit [Fintype I] [Fintype X] in
lemma assigns_swap_left (A B : I ↪ X) {u v : X}
    (hu : u∉Set.range B) (hv : v∉Set.range B) (σ : Equiv.Perm X) :
    Assigns A B (Equiv.swap u v*σ) ↔ Assigns A B σ := by
  have hf (i : I) : Equiv.swap u v (B i)=B i := by
    apply Equiv.swap_apply_of_ne_of_ne
    · intro he; exact hu ⟨i,he⟩
    · intro he; exact hv ⟨i,he⟩
  constructor
  · intro hh i
    apply (Equiv.swap u v).injective
    exact (hh i).trans (hf i).symm
  · intro hh i
    change Equiv.swap u v (σ (A i))=B i
    rw [hh i,hf]

omit [Fintype I] in
theorem sum_sign_assigns_zero (A B : I ↪ X) {u v : X}
    (huv : u≠v) (hu : u∉Set.range B) (hv : v∉Set.range B) :
    (∑σ : Equiv.Perm X, if Assigns A B σ then realSign σ else 0) = 0 := by
  classical
  let f (σ : Equiv.Perm X) := if Assigns A B σ then realSign σ else 0
  have ht (σ : Equiv.Perm X) : f (Equiv.swap u v*σ) = -f σ := by
    dsimp [f]
    rw [assigns_swap_left A B hu hv,map_mul,realSign_swap huv]
    split_ifs <;> ring
  have he := Equiv.sum_comp (Equiv.mulLeft (Equiv.swap u v)) f
  change (∑σ, f (Equiv.swap u v*σ))=∑σ,f σ at he
  simp_rw [ht] at he
  rw [Finset.sum_neg_distrib] at he
  dsimp [f] at he
  linarith

omit [Fintype I] in
lemma uniform_sign_assigns_zero (A B : I ↪ X) {u v : X}
    (huv : u≠v) (hu : u∉Set.range B) (hv : v∉Set.range B) :
    (∑σ : Equiv.Perm X, if Assigns A B σ then
      uniformLaw (Equiv.Perm X) σ * realSign σ else 0) = 0 := by
  have ht (σ : Equiv.Perm X) :
      (if Assigns A B σ then uniformLaw (Equiv.Perm X) σ*realSign σ else 0) =
      (Fintype.card (Equiv.Perm X):ℝ)⁻¹*(if Assigns A B σ then realSign σ else 0) := by
    split_ifs <;> simp [uniformLaw]
  simp_rw [ht]
  rw [←Finset.mul_sum,sum_sign_assigns_zero A B huv hu hv,mul_zero]

lemma uniform_sign_zero [Nontrivial X] :
    (∑σ : Equiv.Perm X, uniformLaw (Equiv.Perm X) σ*realSign σ)=0 := by
  obtain ⟨u,v,huv⟩ := exists_pair_ne X
  let E : Fin 0 ↪ X := ⟨Fin.elim0,by intro i; exact Fin.elim0 i⟩
  have hs := uniform_sign_assigns_zero E E huv
    (by rintro ⟨i,_⟩; exact Fin.elim0 i) (by rintro ⟨i,_⟩; exact Fin.elim0 i)
  simpa [Assigns] using hs

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Analytic_AnalyticTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped Topology
open Set Complex Complex.HadamardThreeLines

namespace BinaryCoordinateSweeps

lemma cosh_norm_le (z : ℂ) : ‖Complex.cosh z‖ ≤ Real.cosh z.re := by
  rw [Complex.cosh, norm_div]
  norm_num only [Complex.norm_ofNat]
  rw [Real.cosh_eq]
  have h := norm_add_le (Complex.exp z) (Complex.exp (-z))
  rw [Complex.norm_exp,Complex.norm_exp,Complex.neg_re] at h
  linarith

lemma ellipseMap_norm {v L : ℝ} (hv : 0 ≤ v) (hL : 0 ≤ L) (z : ℂ)
    (hz : z ∈ verticalClosedStrip 0 L) :
    ‖ellipseMap v z‖ ≤ v/2*(Real.cosh L+1) := by
  change 0 ≤ z.re ∧ z.re ≤ L at hz
  have hc : Real.cosh z.re ≤ Real.cosh L := by
    rw [Real.cosh_le_cosh,abs_of_nonneg hz.1,abs_of_nonneg hL]
    exact hz.2
  have hn : ‖Complex.cosh z+1‖ ≤ Real.cosh L+1 := by
    have := norm_add_le (Complex.cosh z) (1:ℂ)
    norm_num only [norm_one] at this
    linarith [cosh_norm_le z]
  simpa only [ellipseMap,norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg hv,Complex.norm_ofNat] using mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ v/2)

lemma ellipseMap_left {v : ℝ} (hv : 0 ≤ v) (z : ℂ) (hz : z.re=0) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ v ∧ ellipseMap v z=(t:ℂ) := by
  have he : z=(z.im:ℂ)*Complex.I := by apply Complex.ext <;> simp [hz]
  refine ⟨v/2*(Real.cos z.im+1),?_,?_,?_⟩
  · have := Real.neg_one_le_cos z.im
    exact mul_nonneg (div_nonneg hv (by norm_num)) (by linarith)
  · have := Real.cos_le_one z.im
    nlinarith
  · have hc : Complex.cosh z=(Real.cos z.im:ℂ) := by
      calc Complex.cosh z = Complex.cosh ((z.im:ℂ)*Complex.I) := congrArg _ he
           _ = (Real.cos z.im:ℂ) := by rw [Complex.cosh_mul_I,Complex.ofReal_cos]
    rw [ellipseMap,hc]
    push_cast
    rfl

theorem analytic_segment_transfer (R a : ℝ) (hR : 1 < R) (ha : 0 < a) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧
    ∀ E : Type*, ∀ [NormedAddCommGroup E] [NormedSpace ℂ E],
    ∀ f : ℂ → E, Differentiable ℂ f → ∀ ε : ℝ, 0 ≤ ε →
    (∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ 1) →
    (∀ t : ℝ, 0 ≤ t → t ≤ a → ‖f (t:ℂ)‖ ≤ ε) → ‖f 1‖ ≤ ε^θ := by
  let v := min a (1/2)
  have hv : 0 < v := lt_min ha (by norm_num)
  have hva : v ≤ a := min_le_left _ _
  have hv1 : v < 1 := (min_le_right _ _).trans_lt (by norm_num)
  let x := Real.arcosh (2/v-1)
  let L := Real.arcosh (2*R/v-1)
  have hargx : 1 < 2/v-1 := by
    have : (2:ℝ) < 2/v := (lt_div_iff₀ hv).mpr (by linarith)
    linarith
  have hargL : 2/v-1 < 2*R/v-1 := by
    apply sub_lt_sub_right
    apply (div_lt_div_iff_of_pos_right hv).2
    linarith
  have hx : 0 < x := Real.arcosh_pos hargx
  have hxL : x < L := (Real.arcosh_lt_arcosh (by linarith) (by linarith)).mpr hargL
  have hL : 0 < L := hx.trans hxL
  have hcoshx : Real.cosh x=2/v-1 := Real.cosh_arcosh hargx.le
  have hcoshL : Real.cosh L=2*R/v-1 := Real.cosh_arcosh (hargx.trans hargL).le
  have houter : v/2*(Real.cosh L+1)=R := by rw [hcoshL]; field_simp; ring
  have hat : ellipseMap v (x:ℂ)=1 := by
    rw [ellipseMap,←Complex.ofReal_cosh,hcoshx]
    push_cast
    have hvC : (v:ℂ) ≠ 0 := by exact_mod_cast hv.ne'
    field_simp [hvC]
    ring
  refine ⟨1-x/L,by have := (div_lt_one hL).mpr hxL; linarith,
    by have := div_nonneg hx.le hL.le; linarith,?_⟩
  intro E _ _ f hf ε hε hbound hsmall
  let F : ℂ → E := fun z => f (ellipseMap v z)
  have hmap : Differentiable ℂ (ellipseMap v) :=
    (Complex.differentiable_cosh.add_const 1).const_mul ((v:ℂ)/2)
  have hFd : Differentiable ℂ F := hf.comp hmap
  have hF1 : ∀z ∈ verticalClosedStrip 0 L, ‖F z‖ ≤ 1 := by
    intro z hz
    exact hbound _ ((ellipseMap_norm hv.le hL.le z hz).trans_eq houter)
  have hc : BddAbove ((norm ∘ F) '' verticalClosedStrip 0 L) := by
    use 1
    rintro y ⟨z,hz,rfl⟩
    exact hF1 z hz
  have hleft : ∀z ∈ Complex.re ⁻¹' {(0:ℝ)}, ‖F z‖ ≤ ε := by
    intro z hz
    obtain ⟨t,ht,htv,he⟩ := ellipseMap_left hv.le z hz
    dsimp [F]
    rw [he]
    exact hsmall t ht (htv.trans hva)
  have hright : ∀z ∈ Complex.re ⁻¹' {L}, ‖F z‖ ≤ 1 := by
    intro z hz
    apply hF1
    change 0 ≤ z.re ∧ z.re ≤ L
    change z.re=L at hz
    rw [hz]
    exact ⟨hL.le,le_rfl⟩
  have ht := norm_le_interp_of_mem_verticalClosedStrip' hL
    (show (x:ℂ) ∈ verticalClosedStrip 0 L from ⟨hx.le,hxL.le⟩)
    hFd.diffContOnCl hc hleft hright
  simpa only [F,hat,Complex.ofReal_re,sub_zero,Real.one_rpow,mul_one] using ht

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

theorem grid_analytic_contraction : ∃ r : ℕ, 0<r ∧ ∃ g : ℝ, 0<g ∧
    ∀b : ℕ, 1≤b → ∀bits : Fin b → ℕ,
    (∀j,r≤bits j ∧ bits j≤2*r) → ∀D : ℕ,
    ∀ρ : Representation ℂ (Equiv.Perm (GridSlot bits)) (RepSpace D),
    ρ.IsIrreducible → IsUnitaryRep ρ →
      ‖complexGridAverage bits ρ 1‖ ≤ (D:ℝ)^(-g) := by
  obtain ⟨r,hr,q,hq,a,ha,hreal⟩ := real_grid_bound
  obtain ⟨R,hR,hdisk⟩ := complex_grid_disk (2*r)
  obtain ⟨θ,hθ,hθ1,htrans⟩ := analytic_segment_transfer R a hR ha
  refine ⟨r,hr,(c0/(2*q))*θ,mul_pos (div_pos (by norm_num [c0]) (by positivity)) hθ,?_⟩
  intro b hb bits hbits D ρ hi hρ
  have := hi
  have : Nontrivial (RepSpace D) :=
    Module.nontrivial_of_finrank_pos (Signed.irreducible_finrank_pos ρ)
  have ht := htrans (RepSpace D →L[ℂ] RepSpace D) (complexGridAverage bits ρ)
    (complexGridAverage_differentiable bits ρ) ((D:ℝ)^(-c0/(2*q))) (by positivity)
    (hdisk b bits (fun j => (hbits j).2) (RepSpace D) ρ hρ)
    (hreal b hb bits hbits D ρ hi hρ)
  rw [←Real.rpow_mul (Nat.cast_nonneg D)] at ht
  have he : (-c0/(2*(q:ℝ)))*θ = -(c0/(2*q)*θ) := by ring
  simpa only [he] using ht

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_BitBlocks
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

lemma exists_bit_blocks (r : ℕ) (hr : 0<r) : ∀d : ℕ, r≤d →
    ∃b : ℕ, 1≤b ∧ ∃bits : Fin b → ℕ,
      (∀j,r≤bits j ∧ bits j≤2*r) ∧ ∑j,bits j=d := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd
    by_cases hsmall : d≤2*r
    · refine ⟨1,by omega,fun _ => d,fun _ => ⟨hd,hsmall⟩,?_⟩
      simp
    obtain ⟨b,hb,bits,hbits,hsum⟩ := ih (d-r) (by omega) (by omega)
    refine ⟨b+1,by omega,Fin.cons r bits,?_,?_⟩
    · intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · simp only [Fin.cons_zero]; omega
      · simpa using hbits i
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero,Fin.cons_succ,hsum,Nat.add_sub_of_le hd]

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_FiniteLawAverage
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

lemma finiteLaw_pushLaw {A B : Type*} [Fintype A] [Fintype B] (f : A → B) :
    finiteLaw f=pushLaw (uniformLaw A) f := rfl

lemma pushLaw_expectation {A B R : Type*} [Fintype A] [Fintype B]
    [AddCommMonoid R] [Module ℝ R] (p : A → ℝ) (f : A → B) (F : B → R) :
    (∑b,pushLaw p f b • F b)=∑a,p a • F (f a) := by
  unfold pushLaw
  simp only [Finset.sum_smul]
  rw [Finset.sum_comm]
  simp [ite_smul]

lemma pushLaw_comp {A B C : Type*} [Fintype A] [Fintype B]
    (p : A → ℝ) (f : A → B) (g : B → C) :
    pushLaw (pushLaw p f) g=pushLaw p (g ∘ f) := by
  funext c
  have he := pushLaw_expectation p f (fun b => if g b=c then (1:ℝ) else 0)
  simpa [pushLaw,smul_eq_mul,mul_ite] using he

lemma pushLaw_equiv {A B C : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (p : B → ℝ) (f : B → C) :
    pushLaw (p ∘ e) (f ∘ e)=pushLaw p f := by
  funext c
  exact e.sum_comp (fun b => if f b=c then p b else 0)

lemma pushLaw_equiv_apply {A B : Type*} [Fintype A]
    (e : A ≃ B) (p : A → ℝ) (b : B) : pushLaw p e b=p (e.symm b) := by
  simp only [pushLaw,←e.eq_symm_apply]
  simp

lemma pushLaw_id {A : Type*} [Fintype A] (p : A → ℝ) : pushLaw p id=p := by
  funext a; simp [pushLaw]

lemma pushLaw_prod {A B X Y : Type*} [Fintype A] [Fintype B]
    (p : A → ℝ) (q : B → ℝ) (f : A → X) (g : B → Y) :
    pushLaw (fun ab : A×B => p ab.1*q ab.2) (Prod.map f g)=
      fun xy => pushLaw p f xy.1 * pushLaw q g xy.2 := by
  funext xy
  simp only [pushLaw,Fintype.sum_prod_type,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm (f := fun b a => (if f a=xy.1 then p a else 0)*(if g b=xy.2 then q b else 0))]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rcases xy with ⟨x,y⟩
  simp only [Prod.map_apply,Prod.mk.injEq]
  split_ifs <;> simp_all

lemma pushLaw_pi {I : Type*} [Fintype I] [DecidableEq I] {A X : I → Type*}
    [∀i,Fintype (A i)] [∀i,Fintype (X i)]
    (p : ∀i,A i → ℝ) (f : ∀i,A i → X i) :
    pushLaw (fun a : ∀i,A i => ∏i,p i (a i)) (fun a i => f i (a i))=
      fun x => ∏i,pushLaw (p i) (f i) (x i) := by
  funext x
  unfold pushLaw
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [funext_iff]
  by_cases h : ∀i,f i (a i)=x i
  · simp [h]
  · obtain ⟨i,hi⟩ := not_forall.mp h
    rw [ite_eq_right (by aesop)]
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

lemma uniformLaw_prod {A B : Type*} [Fintype A] [Fintype B] :
    uniformLaw (A×B)=fun ab => uniformLaw A ab.1 * uniformLaw B ab.2 := by
  funext ab
  simp [uniformLaw,Fintype.card_prod,mul_comm]

lemma uniformLaw_pi {I : Type*} [Fintype I] [DecidableEq I] {A : I → Type*} [∀i,Fintype (A i)] :
    uniformLaw (∀i,A i)=fun a => ∏i,uniformLaw (A i) (a i) := by
  funext a
  simp [uniformLaw,Fintype.card_pi,Finset.prod_inv_distrib]

lemma uniformLaw_equiv {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) :
    uniformLaw B ∘ e=uniformLaw A := by
  funext a
  simp [uniformLaw,Fintype.card_congr e]

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_BoardLaw
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open GridSplit

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

lemma boardSampleLaw {A B : Type*} [Fintype A] [Fintype B]
    (p : A → ℝ) (q : B → ℝ) (f : A → Equiv.Perm X) (g : B → Equiv.Perm Y) :
    pushLaw (fun LR : (Y → A)×(X → B) => (∏y,p (LR.1 y))*(∏x,q (LR.2 x)))
      (fun LR => columnPerm (g ∘ LR.2) * rowPerm (f ∘ LR.1))=
      boardLaw (pushLaw p f) (pushLaw q g) := by
  have he := pushLaw_prod (fun L : Y → A => ∏y,p (L y)) (fun R : X → B => ∏x,q (R x))
    (fun L y => f (L y)) (fun R x => g (R x))
  rw [pushLaw_pi,pushLaw_pi] at he
  unfold boardLaw boardWeight
  rw [←he,pushLaw_comp]
  rfl

variable {X' Y' : Type*} [Fintype X'] [Fintype Y'] [DecidableEq X'] [DecidableEq Y']

omit [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  [Fintype X'] [Fintype Y'] [DecidableEq X'] [DecidableEq Y'] in
lemma rowPerm_congr (e : X ≃ X') (f : Y ≃ Y') (L : Y → Equiv.Perm X) :
    (Equiv.prodCongr e f).permCongr (rowPerm L)=
      rowPerm (f.arrowCongr e.permCongr L) := by
  apply Equiv.ext
  intro xy
  apply Prod.ext <;> simp [rowPerm,Equiv.permCongr_apply,Equiv.arrowCongr_apply]

omit [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  [Fintype X'] [Fintype Y'] [DecidableEq X'] [DecidableEq Y'] in
lemma columnPerm_congr (e : X ≃ X') (f : Y ≃ Y') (R : X → Equiv.Perm Y) :
    (Equiv.prodCongr e f).permCongr (columnPerm R)=
      columnPerm (e.arrowCongr f.permCongr R) := by
  apply Equiv.ext
  intro xy
  apply Prod.ext <;> simp [columnPerm,Equiv.permCongr_apply,Equiv.arrowCongr_apply]

omit [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  [Fintype X'] [Fintype Y'] [DecidableEq X'] [DecidableEq Y'] in
lemma boardSweep_congr (e : X ≃ X') (f : Y ≃ Y') (LR : BoardChoices X Y) :
    (Equiv.prodCongr e f).permCongr (boardSweep LR)=
      boardSweep (boardChoicesEquiv e f LR) := by
  change (Equiv.prodCongr e f).permCongrHom (columnPerm LR.2 * rowPerm LR.1)=_
  rw [map_mul]
  change (Equiv.prodCongr e f).permCongr (columnPerm LR.2) *
    (Equiv.prodCongr e f).permCongr (rowPerm LR.1)=_
  rw [rowPerm_congr,columnPerm_congr]
  rfl

omit [DecidableEq X'] [DecidableEq Y'] in
lemma boardWeight_congr (e : X ≃ X') (f : Y ≃ Y')
    (p : Equiv.Perm X → ℝ) (q : Equiv.Perm Y → ℝ) (LR : BoardChoices X Y) :
    boardWeight (pushLaw p e.permCongr) (pushLaw q f.permCongr)
      (boardChoicesEquiv e f LR)=boardWeight p q LR := by
  unfold boardWeight boardChoicesEquiv
  simp only [Equiv.prodCongr_apply,pushLaw_equiv_apply]
  rw [←f.prod_comp,←e.prod_comp]
  have he (σ : Equiv.Perm X) : e.symm.permCongr (e.permCongr σ)=σ :=
    e.permCongr.symm_apply_apply σ
  have hf (σ : Equiv.Perm Y) : f.symm.permCongr (f.permCongr σ)=σ :=
    f.permCongr.symm_apply_apply σ
  simp [Equiv.arrowCongr_apply,he,hf]

lemma boardLaw_congr (e : X ≃ X') (f : Y ≃ Y')
    (p : Equiv.Perm X → ℝ) (q : Equiv.Perm Y → ℝ) :
    pushLaw (boardLaw p q) (Equiv.prodCongr e f).permCongr=
      boardLaw (pushLaw p e.permCongr) (pushLaw q f.permCongr) := by
  unfold boardLaw
  rw [pushLaw_comp]
  have hw : boardWeight (pushLaw p e.permCongr) (pushLaw q f.permCongr) ∘
      boardChoicesEquiv e f=boardWeight p q := funext (boardWeight_congr e f p q)
  have hs : (Equiv.prodCongr e f).permCongr ∘ boardSweep=
      boardSweep ∘ boardChoicesEquiv e f := funext (boardSweep_congr e f)
  rw [hs,←hw]
  exact pushLaw_equiv (boardChoicesEquiv e f) _ _

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
variable {X Y A B Ω : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  [Fintype A] [Fintype B] [Fintype Ω]
lemma board_equiv_sample (p : A → ℝ) (q : B → ℝ)
    (f : A → Equiv.Perm X) (g : B → Equiv.Perm Y)
    (e : Ω ≃ (Y → A)×(X → B)) (w : Ω → ℝ) (F : Ω → Equiv.Perm (X×Y))
    (hw : ∀c,w c=(∏y,p ((e c).1 y))*(∏x,q ((e c).2 x)))
    (hF : ∀c,F c=GridSplit.columnPerm (g ∘ (e c).2)*GridSplit.rowPerm (f ∘ (e c).1)) :
    pushLaw w F=boardLaw (pushLaw p f) (pushLaw q g) := by
  have hw' : w=(fun LR : (Y→A)×(X→B) => (∏y,p (LR.1 y))*(∏x,q (LR.2 x))) ∘ e := funext hw
  have hf' : F=(fun LR : (Y→A)×(X→B) => GridSplit.columnPerm (g ∘ LR.2)*GridSplit.rowPerm (f ∘ LR.1)) ∘ e := funext hF
  rw [hw',hf',pushLaw_equiv]
  exact boardSampleLaw p q f g
end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Mixing_BinarySplitChoices
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.BinarySplit
open GridSplit

variable {m n : ℕ}

lemma rowChoices_at (c : SweepCoins (m+n)) (x : Slot (m+n)) (j : Fin m) :
    rowChoices c (Signed.splitWord x).2 j (fun i => (Signed.splitWord x).1 i)=
      c (j.castAdd n) (fun i => x i) := by
  unfold rowChoices
  congr 1
  apply (leftOutsideEquiv j).injective
  rw [Equiv.apply_symm_apply]
  rfl

lemma columnChoices_at (c : SweepCoins (m+n)) (x : Slot (m+n)) (j : Fin n) :
    columnChoices c (Signed.splitWord x).1 j (fun i => (Signed.splitWord x).2 i)=
      c (j.natAdd m) (fun i => x i) := by
  unfold columnChoices
  congr 1
  apply (rightOutsideEquiv j).injective
  rw [Equiv.apply_symm_apply]
  rfl

lemma layer_left (c : SweepCoins (m+n)) (j : Fin m) (x : Slot (m+n)) :
    Signed.splitWord (coordinateLayer (m+n) (j.castAdd n) (c (j.castAdd n)) x)=
      (coordinateLayer m j (rowChoices c (Signed.splitWord x).2 j) (Signed.splitWord x).1,
        (Signed.splitWord x).2) := by
  apply Prod.ext
  · dsimp only
    funext i
    change coordinateLayer _ _ _ x (i.castAdd n)=_
    by_cases hi : i=j
    · subst i
      rw [coordinateLayer_apply_at,coordinateLayer_apply_at,rowChoices_at]
      rfl
    · rw [coordinateLayer_apply_other _ _ _ (fun he => hi (Fin.ext
        (congrArg (fun i : Fin (m+n) => i.val) he))),coordinateLayer_apply_other _ _ _ hi]
      rfl
  · dsimp only
    funext i
    exact coordinateLayer_apply_other (m+n) (j.castAdd n) (i.natAdd m) (by
      intro he
      have hh := congrArg (fun i : Fin (m+n) => i.val) he
      simp only [Fin.val_natAdd,Fin.val_castAdd] at hh; omega) _ x

lemma layer_right (c : SweepCoins (m+n)) (j : Fin n) (x : Slot (m+n)) :
    Signed.splitWord (coordinateLayer (m+n) (j.natAdd m) (c (j.natAdd m)) x)=
      ((Signed.splitWord x).1,
        coordinateLayer n j (columnChoices c (Signed.splitWord x).1 j) (Signed.splitWord x).2) := by
  apply Prod.ext
  · dsimp only
    funext i
    exact coordinateLayer_apply_other (m+n) (j.natAdd m) (i.castAdd n) (by
      intro he
      have hh := congrArg (fun i : Fin (m+n) => i.val) he
      simp only [Fin.val_natAdd,Fin.val_castAdd] at hh; omega) _ x
  · dsimp only
    funext i
    change coordinateLayer _ _ _ x (i.natAdd m)=_
    by_cases hi : i=j
    · subst i
      rw [coordinateLayer_apply_at,coordinateLayer_apply_at,columnChoices_at]
      rfl
    · rw [coordinateLayer_apply_other _ _ _ (fun he => hi (Fin.ext (by
        have hh := congrArg (fun i : Fin (m+n) => i.val) he; simpa using hh))),
        coordinateLayer_apply_other _ _ _ hi]
      rfl

lemma layer_left_congr (c : SweepCoins (m+n)) (j : Fin m) :
    Signed.splitWord.permCongr (coordinateLayer (m+n) (j.castAdd n) (c (j.castAdd n)))=
      rowPerm (fun y => coordinateLayer m j (rowChoices c y j)) := by
  apply Equiv.ext
  intro xy
  have he := layer_left c j (Signed.splitWord.symm xy)
  change Signed.splitWord (coordinateLayer _ _ _ (Signed.splitWord.symm xy))=_
  rw [he,Equiv.apply_symm_apply]
  rfl

lemma layer_right_congr (c : SweepCoins (m+n)) (j : Fin n) :
    Signed.splitWord.permCongr (coordinateLayer (m+n) (j.natAdd m) (c (j.natAdd m)))=
      columnPerm (fun x => coordinateLayer n j (columnChoices c x j)) := by
  apply Equiv.ext
  intro xy
  have he := layer_right c j (Signed.splitWord.symm xy)
  change Signed.splitWord (coordinateLayer _ _ _ (Signed.splitWord.symm xy))=_
  rw [he,Equiv.apply_symm_apply]
  rfl

theorem binarySweep_split (c : SweepCoins (m+n)) :
    Signed.splitWord.permCongr (binarySweep (m+n) c)=
      columnPerm (fun x => binarySweep n (columnChoices c x)) *
        rowPerm (fun y => binarySweep m (rowChoices c y)) := by
  change Signed.splitWord.permCongrHom (binarySweep (m+n) c)=_
  unfold binarySweep
  rw [List.ofFn_add,List.reverse_append,List.prod_append,map_mul]
  congr 1
  · rw [map_list_prod Signed.splitWord.permCongrHom,List.map_reverse,List.map_ofFn]
    change (List.ofFn (fun j : Fin n => Signed.splitWord.permCongr
      (coordinateLayer _ (j.natAdd m) (c (j.natAdd m))))).reverse.prod=_
    simp_rw [layer_right_congr]
    simpa only [List.map_reverse,List.map_ofFn,Function.comp_def] using
      (prod_columns (List.ofFn (fun j : Fin n => fun x =>
        coordinateLayer n j (columnChoices c x j))).reverse)
  · rw [map_list_prod Signed.splitWord.permCongrHom,List.map_reverse,List.map_ofFn]
    change (List.ofFn (fun j : Fin m => Signed.splitWord.permCongr
      (coordinateLayer _ (j.castAdd n) (c (j.castAdd n))))).reverse.prod=_
    simp_rw [layer_left_congr]
    simpa only [List.map_reverse,List.map_ofFn,Function.comp_def] using
      (prod_rows (List.ofFn (fun j : Fin m => fun y =>
        coordinateLayer m j (rowChoices c y j))).reverse)

end BinaryCoordinateSweeps.BinarySplit

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_GridLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable
open GridSplit

lemma pushLaw_inverse {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (p : A → ℝ) : pushLaw (pushLaw p e) e.symm=p := by
  rw [pushLaw_comp]
  have he : e.symm ∘ e = id := funext e.symm_apply_apply
  rw [he,pushLaw_id]

lemma pushLaw_injective {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) : Function.Injective (fun p : A → ℝ => pushLaw p e) := by
  intro p q he
  have hh := congrArg (fun w => pushLaw w e.symm) he
  simpa only [pushLaw_inverse] using hh

lemma binary_splitLaw (m n : ℕ) :
    pushLaw (binaryLaw (m+n)) Signed.splitWord.permCongr=
      boardLaw (binaryLaw m) (binaryLaw n) := by
  unfold binaryLaw
  rw [finiteLaw_pushLaw,finiteLaw_pushLaw,finiteLaw_pushLaw,pushLaw_comp]
  let e := BinarySplit.choicesEquiv (m:=m) (n:=n)
  have hs : Signed.splitWord.permCongr ∘ binarySweep (m+n)=
      (fun LR : (Slot n → SweepCoins m) × (Slot m → SweepCoins n) =>
        columnPerm (binarySweep n ∘ LR.2)*rowPerm (binarySweep m ∘ LR.1)) ∘ e :=
    funext BinarySplit.binarySweep_split
  rw [hs,←uniformLaw_equiv e,pushLaw_equiv]
  have hu : uniformLaw ((Slot n → SweepCoins m)×(Slot m → SweepCoins n))=
      fun LR => (∏y,uniformLaw (SweepCoins m) (LR.1 y))*
        (∏x,uniformLaw (SweepCoins n) (LR.2 x)) := by
    rw [uniformLaw_prod]
    simp only [uniformLaw_pi (I:=Slot n) (A:=fun _ => SweepCoins m),
      uniformLaw_pi (I:=Slot m) (A:=fun _ => SweepCoins n)]
  rw [hu]
  exact boardSampleLaw _ _ _ _

lemma grid_splitLaw {m n : ℕ} (bits : Fin (m+n) → ℕ) :
    pushLaw (gridLaw bits) (slotEquiv (m:=m) (n:=n) bits).permCongr=
      boardLaw (gridLaw (leftBits (m:=m) (n:=n) bits)) (gridLaw (rightBits (m:=m) (n:=n) bits)) := by
  let : DecidableEq (GridSlot (leftBits (m:=m) (n:=n) bits)) := inferInstance
  let : DecidableEq (GridSlot (rightBits (m:=m) (n:=n) bits)) := inferInstance
  let : Fintype (GridChoices (leftBits (m:=m) (n:=n) bits)) := inferInstance
  let : Fintype (GridChoices (rightBits (m:=m) (n:=n) bits)) := inferInstance
  unfold gridLaw
  rw [pushLaw_comp]
  exact board_equiv_sample
    (gridWeight (leftBits (m:=m) (n:=n) bits) 1)
    (gridWeight (rightBits (m:=m) (n:=n) bits) 1)
    (gridSweep (leftBits (m:=m) (n:=n) bits))
    (gridSweep (rightBits (m:=m) (n:=n) bits))
    (GridSplit.choicesEquiv (m:=m) (n:=n) bits) _ _
    (gridWeight_split (m:=m) (n:=n) bits 1) (gridSweep_split (m:=m) (n:=n) bits)

lemma oneAxis_gridLaw (bits : Fin 1 → ℕ) :
    pushLaw (gridLaw bits) (oneAxisSlotEquiv bits).permCongr=binaryLaw (bits 0) := by
  unfold gridLaw
  rw [pushLaw_comp]
  have hw : gridWeight bits 1=binaryLaw (bits 0) ∘ oneAxisChoiceEquiv bits := by
    funext c
    simp [oneAxis_gridWeight,lineLaw]
  have hs : (oneAxisSlotEquiv bits).permCongr ∘ gridSweep bits=oneAxisChoiceEquiv bits := by
    funext c
    rw [Function.comp_apply,←oneAxisSweepEquiv_apply]
    exact (oneAxisSlotEquiv bits).permCongr.apply_symm_apply _
  rw [hw,hs]
  have hh := pushLaw_equiv (oneAxisChoiceEquiv bits) (binaryLaw (bits 0)) id
  simpa only [Function.id_comp,pushLaw_id] using hh

theorem gridLaw_binary : ∀b : ℕ, 1≤b → ∀bits : Fin b → ℕ,
    ∃d : ℕ, d=∑j,bits j ∧ ∃e : GridSlot bits ≃ Slot d,
      pushLaw (gridLaw bits) e.permCongr=binaryLaw d := by
  intro b
  induction b using Nat.case_strong_induction_on with
  | hz => intro hb; omega
  | hi b ih =>
    intro hb bits
    by_cases hb0 : b=0
    · subst b
      exact ⟨bits 0,by simp,oneAxisSlotEquiv bits,oneAxis_gridLaw bits⟩
    obtain ⟨dL,hdL,eL,heL⟩ := ih b (by omega) (by omega) (leftBits (n:=1) bits)
    let eR := oneAxisSlotEquiv (rightBits (m:=b) bits)
    have heR := oneAxis_gridLaw (rightBits (m:=b) bits)
    let dR := rightBits (m:=b) (n:=1) bits 0
    let ep := Equiv.prodCongr eL eR
    let e := ((slotEquiv (m:=b) (n:=1) bits).trans ep).trans Signed.splitWord.symm
    refine ⟨dL+dR,?_,e,?_⟩
    · rw [Fin.sum_univ_add,←hdL]
      simp [dR]
    · apply pushLaw_injective Signed.splitWord.permCongr
      change pushLaw (pushLaw (gridLaw bits) e.permCongr) Signed.splitWord.permCongr=
        pushLaw (binaryLaw (dL+dR)) Signed.splitWord.permCongr
      rw [binary_splitLaw,pushLaw_comp]
      have he : Signed.splitWord.permCongr ∘ e.permCongr=
          ep.permCongr ∘ (slotEquiv (m:=b) (n:=1) bits).permCongr := by
        funext σ
        apply Equiv.ext
        intro xy
        simp [e,Equiv.permCongr_apply]
      let : DecidableEq (GridSlot (leftBits (m:=b) (n:=1) bits) × GridSlot (rightBits (m:=b) (n:=1) bits)) := inferInstance
      rw [he,←pushLaw_comp (gridLaw bits) (slotEquiv (m:=b) (n:=1) bits).permCongr ep.permCongr]
      rw [grid_splitLaw (m:=b) (n:=1)]
      change pushLaw (boardLaw _ _) (Equiv.prodCongr eL eR).permCongr = _
      rw [boardLaw_congr eL eR,heL,heR]

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_MatrixBounds_FourierTrace
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.instIsIrreducibleGComplexSpechtSpaceTransposeTransposeRep _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Fourier
open Representation Irrep Young

theorem young_trace_resolution {n : ℕ} (p : Equiv.Perm (Fin n) → ℂ) (q : ℕ) :
    evenMoment q (groupAverage (regular (Equiv.Perm (Fin n))) p)=
    ∑ℓ : n.Partition,(Module.finrank ℂ (PartitionHilbert ℓ):ℝ)*
      evenMoment q (groupAverage (partitionHilbertRep ℓ) p) := by
  let σ := regular (Equiv.Perm (Fin n))
  let B := ((groupAverage σ p).adjoint*groupAverage σ p)^q
  let S := fun ℓ : n.Partition => isotypicSpan (partitionHilbertRep ℓ) σ
  have hP : (∑ℓ : n.Partition,(S ℓ).starProjection.toLinearMap)=1 := by
    apply LinearMap.ext
    intro v
    simp only [LinearMap.sum_apply,ContinuousLinearMap.coe_coe,Module.End.one_apply]
    exact partition_projection_sum σ (regular_unitary _) v
  have he (ℓ : n.Partition) :
      LinearMap.trace ℂ (RegularSpace (Equiv.Perm (Fin n)))
          (B*(S ℓ).starProjection.toLinearMap)=
        (Module.finrank ℂ (PartitionHilbert ℓ):ℂ)*
          LinearMap.trace ℂ (PartitionHilbert ℓ)
            (((groupAverage (partitionHilbertRep ℓ) p).adjoint*
              groupAverage (partitionHilbertRep ℓ) p)^q) := by
    have hc := even_compatible (partitionHilbertRep ℓ) σ p
      (partitionHilbertRep_unitary ℓ) (regular_unitary _) q
    rw [trace_mul_projection _ _ (isotypic_invariant_of_compatible _ _ _ _ hc),
      isotypic_trace _ _ _ _ hc,regular_multiplicity]
  unfold evenMoment
  change (LinearMap.trace ℂ _ B).re=_
  rw [←mul_one B,←hP,Finset.mul_sum,map_sum,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro ℓ _
  rw [he]
  simp

theorem variation_fourier_bound {n : ℕ} (p q : Equiv.Perm (Fin n) → ℝ) :
    totalVariation p q ^2 ≤ (1/4:ℝ)*
      ∑ℓ : n.Partition,(Module.finrank ℂ (PartitionHilbert ℓ):ℝ)*
        evenMoment 1 (groupAverage (partitionHilbertRep ℓ) (fun g => (p g-q g:ℂ))) := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Equiv.Perm (Fin n)))
    (fun _ => (1:ℝ)) (fun g => |p g-q g|)
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,sq_abs] at hc
  rw [←young_trace_resolution,regular_moment_one]
  simp only [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  unfold totalVariation
  nlinarith

end BinaryCoordinateSweeps.Fourier

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Mixing_BinaryContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

lemma averageOperator_sum {G : Type*} [Fintype G] [Monoid G] {D : ℕ}
    (p : G → ℝ) (ρ : Representation ℂ G (RepSpace D)) :
    averageOperator p ρ=∑g,(p g:ℂ) • Module.End.toContinuousLinearMap (RepSpace D) (ρ g) := by
  apply ContinuousLinearMap.coe_injective
  simp [averageOperator,Module.End.toContinuousLinearMap]

lemma pushLaw_complex_expectation {A B R : Type*} [Fintype A] [Fintype B]
    [AddCommMonoid R] [Module ℂ R] (p : A → ℝ) (f : A → B) (F : B → R) :
    (∑b,(pushLaw p f b:ℂ) • F b)=∑a,(p a:ℂ) • F (f a) := by
  unfold pushLaw
  simp only [Complex.ofReal_sum,apply_ite,Complex.ofReal_zero,Finset.sum_smul]
  rw [Finset.sum_comm]
  simp [ite_smul]

lemma gridAverage_relabel {b D d : ℕ} (bits : Fin b → ℕ) (e : GridSlot bits ≃ Slot d)
    (ρ : Representation ℂ (Equiv.Perm (Slot d)) (RepSpace D))
    (he : pushLaw (gridLaw bits) e.permCongr=binaryLaw d) :
    complexGridAverage bits (ρ.comp e.permCongrHom.toMonoidHom) 1=
      averageOperator (binaryLaw d) ρ := by
  rw [averageOperator_sum,←he,pushLaw_complex_expectation]
  unfold gridLaw
  rw [pushLaw_complex_expectation]
  unfold complexGridAverage
  apply Finset.sum_congr rfl
  intro c _
  rw [show (1:ℂ)=(1:ℝ) from rfl,complexGridWeight_real]
  rfl

theorem binary_contraction : BinaryContractionTarget := by
  obtain ⟨r,hr,g,hg,hgrid⟩ := grid_analytic_contraction
  refine ⟨g,hg,r,?_⟩
  intro d hd D ρ hi hu
  have := hi
  obtain ⟨b,hb,bits,hbits,hsum⟩ := exists_bit_blocks r hr d hd
  obtain ⟨d',hd',e,he⟩ := gridLaw_binary b hb bits
  have hdd : d'=d := hd'.trans hsum
  cases hdd
  have hσ : Representation.IsIrreducible (ρ.comp e.permCongrHom.toMonoidHom) :=
    Irrep.irreducible_comp_equiv e.permCongrHom ρ
  have hunit : IsUnitaryRep (ρ.comp e.permCongrHom.toMonoidHom) := fun g v => hu _ _
  have hh := hgrid b hb bits hbits D (ρ.comp e.permCongrHom.toMonoidHom) hσ hunit
  rwa [gridAverage_relabel bits e ρ he] at hh

open Irrep

variable {G V : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

lemma complexAverage_transport (ρ : Representation ℂ G V) (p : G → ℂ)
    (v : V) :
    (stdOrthonormalBasis ℂ V).repr (complexAverage ρ p v)=
      complexAverage (conjugateRep ρ (stdOrthonormalBasis ℂ V).repr.toLinearEquiv) p
        ((stdOrthonormalBasis ℂ V).repr v) := by
  simp only [complexAverage_apply,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro g _
  congr 1
  change _ = (stdOrthonormalBasis ℂ V).repr
    (ρ g ((stdOrthonormalBasis ℂ V).repr.symm ((stdOrthonormalBasis ℂ V).repr v)))
  rw [LinearIsometryEquiv.symm_apply_apply]

lemma hilbert_norm_of_coordinates (ρ : Representation ℂ G V) (p : G → ℂ) {a : ℝ}
    (ha : 0≤a)
    (h : ‖complexAverage (conjugateRep ρ (stdOrthonormalBasis ℂ V).repr.toLinearEquiv) p‖≤a) :
    ‖complexAverage ρ p‖≤a := by
  apply ContinuousLinearMap.opNorm_le_bound _ ha
  intro v
  rw [←(stdOrthonormalBasis ℂ V).repr.norm_map (complexAverage ρ p v),
    complexAverage_transport]
  exact ((complexAverage _ _).le_opNorm _).trans (by
    rw [LinearIsometryEquiv.norm_map]
    exact mul_le_mul_of_nonneg_right h (norm_nonneg _))

theorem binary_hilbert_contraction : ∃ g : ℝ, 0<g ∧ ∃ d₀ : ℕ,
    ∀ d ≥ d₀, ∀ (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
      [FiniteDimensional ℂ V],
    ∀ (ρ : Representation ℂ (Equiv.Perm (Slot d)) V), ρ.IsIrreducible →
      (∀g v, ‖ρ g v‖=‖v‖) →
      ‖complexAverage ρ (fun g => (binaryLaw d g:ℂ))‖≤(Module.finrank ℂ V:ℝ)^(-g) := by
  obtain ⟨g,hg,d₀,hh⟩ := binary_contraction
  refine ⟨g,hg,d₀,?_⟩
  intro d hd V _ _ _ ρ hi hu
  let := hi
  let E := (stdOrthonormalBasis ℂ V).repr
  let σ := conjugateRep ρ E.toLinearEquiv
  have hσ : σ.IsIrreducible := irreducible_equiv ρ σ (conjugateEquiv ρ E.toLinearEquiv)
  have hunit : IsUnitaryRep σ := by
    intro g v
    change ‖E (ρ g (E.symm v))‖=‖v‖
    rw [E.norm_map,hu,E.symm.norm_map]
  exact hilbert_norm_of_coordinates ρ _ (by positivity) (hh d hd _ σ hσ hunit)

lemma evenMoment_one_norm_bound (A : V →L[ℂ] V) {a : ℝ} (_ha : 0≤a) (hA : ‖A‖≤a) :
    evenMoment 1 A.toLinearMap ≤ (Module.finrank ℂ V:ℝ)*a^2 := by
  let e := stdOrthonormalBasis ℂ V
  unfold evenMoment
  rw [pow_one,LinearMap.trace_eq_sum_inner _ e,Complex.re_sum]
  calc
    _ ≤ ∑i : Fin (Module.finrank ℂ V),a^2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [Module.End.mul_apply,LinearMap.adjoint_inner_right]
      have hn : ‖e i‖=1 := e.orthonormal.1 i
      have hb := (A.le_opNorm (e i)).trans
        (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
      rw [hn,mul_one] at hb
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast
      exact pow_le_pow_left₀ (norm_nonneg _) hb 2
    _ = _ := by simp

lemma complexAverage_uniform_zero (ρ : Representation ℂ G V) [ρ.IsIrreducible]
    (hD : 1<Module.finrank ℂ V) :
    complexAverage ρ (fun g => (uniformLaw G g:ℂ))=0 := by
  apply ContinuousLinearMap.coe_injective
  change groupAverage ρ _ = 0
  simp only [groupAverage,uniformLaw,Complex.ofReal_inv,Complex.ofReal_natCast,
    ←Finset.smul_sum,Irrep.sum_eq_zero_of_finrank_gt_one ρ hD,smul_zero]

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
variable (μ : YoungDiagram)

lemma swap_tabloid_eq {I : Type*} [DecidableEq I]
    (a : Cell μ) (ha : row a≠0) (u : I ↪ Cell μ) (hu : ∀i,row (u i)=0)
    (hfix : ∀c : C μ, ∀i,c.val (u i)=u i) (i j : I) (c : C μ) :
    tabloidOfPerm μ (Equiv.swap a (u i)*c.val)=tabloidOfPerm μ (Equiv.swap a (u j)) ↔
      i=j ∧ c=1 := by
  have hau (i : I) : a≠u i := fun he => ha (he ▸ hu i)
  constructor
  · intro he
    have hij : i=j := by
      by_contra hij
      have huij : u j≠u i := fun hh => hij (u.injective hh).symm
      have hju : u j≠a := (hau j).symm
      have hh := congrArg (fun t : Tabloid μ => t.val (u j)) he
      have hc := hfix c⁻¹ j
      have hs : Equiv.swap a (u i) (u j)=u j := Equiv.swap_apply_of_ne_of_ne hju huij
      simp only [tabloidOfPerm,labels,mul_inv_rev,Equiv.swap_inv,
        Equiv.Perm.mul_apply,hs,Equiv.swap_apply_right] at hh
      change row (c.val⁻¹ (u j))=row a at hh
      rw [show c.val⁻¹ (u j)=u j from hc,hu] at hh
      exact ha hh.symm
    subst j
    have hc : c.val⁻¹ ∈ rowStabilizer μ := by
      have hh := (tabloidOfPerm_eq_iff μ _ _).mp he
      simpa only [mul_inv_rev,mul_assoc,inv_mul_cancel,mul_one] using hh
    have hc' : c.val ∈ rowStabilizer μ := by
      simpa using (rowStabilizer μ).inv_mem hc
    have hh : c.val ∈ rowStabilizer μ ⊓ colStabilizer μ := ⟨hc',c.property⟩
    rw [row_col_intersection] at hh
    exact ⟨rfl,Subtype.ext hh⟩
  · rintro ⟨rfl,rfl⟩
    simp

lemma swap_poly_coefficient {I : Type*} [DecidableEq I]
    (a : Cell μ) (ha : row a≠0) (u : I ↪ Cell μ) (hu : ∀i,row (u i)=0)
    (hfix : ∀c : C μ, ∀i,c.val (u i)=u i) (i j : I) :
    tabloidRepresentation μ (Equiv.swap a (u i)) (polytabloid μ)
      (tabloidOfPerm μ (Equiv.swap a (u j)))=if i=j then (1:ℂ) else 0 := by
  rw [polytabloid,columnAnti_apply]
  simp_rw [rep_basis,smul_tabloidOfPerm,mul_one]
  rw [map_sum]
  simp_rw [map_smul,rep_basis,smul_tabloidOfPerm]
  simp only [Finset.sum_apply,Pi.smul_apply,tabloidBasis,Pi.single_apply]
  have he (c : C μ) : tabloidOfPerm μ (Equiv.swap a (u j))=
      tabloidOfPerm μ (Equiv.swap a (u i)*c.val) ↔ i=j ∧ c=1 :=
    eq_comm.trans (swap_tabloid_eq μ a ha u hu hfix i j c)
  simp only [he]
  by_cases hij : i=j <;> simp [hij]

theorem singleton_column_dimension {I : Type*} [Fintype I] [DecidableEq I]
    (a : Cell μ) (ha : row a≠0) (u : I ↪ Cell μ) (hu : ∀i,row (u i)=0)
    (hfix : ∀c : C μ, ∀i,c.val (u i)=u i) :
    Fintype.card I ≤ Module.finrank ℂ (SpechtSpace μ) := by
  have hind : LinearIndependent ℂ
      (fun i : I => spechtRep μ (Equiv.swap a (u i)) (spechtPoly μ)) := by
    apply LinearIndependent.of_comp (f:=spechtInclude μ)
    rw [Fintype.linearIndependent_iff]
    intro t ht j
    have hh := congrFun ht (tabloidOfPerm μ (Equiv.swap a (u j)))
    simp only [Finset.sum_apply,Pi.smul_apply,Function.comp_apply,Pi.zero_apply] at hh
    simp_rw [spechtInclude_rep,spechtInclude_poly,swap_poly_coefficient μ a ha u hu hfix] at hh
    simpa using hh
  let : Module.Finite ℂ (SpechtSpace μ) :=
    inferInstanceAs (FiniteDimensional ℂ (SpechtSpace μ))
  exact hind.fintype_card_le_finrank

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Mixing_LongRowDimension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
variable (μ : YoungDiagram)

lemma longRowCells_fixed (c : C μ) (j : Fin (μ.rowLen 0-μ.rowLen 1)) :
    c.val (longRowCells μ j)=longRowCells μ j := by
  have hc := c.property (longRowCells μ j)
  have hm := YoungDiagram.mem_iff_lt_rowLen.mp (c.val (longRowCells μ j)).property
  have hr : row (c.val (longRowCells μ j))=0 := by
    by_contra hne
    have ha := μ.rowLen_anti 1 (row (c.val (longRowCells μ j))) (by omega)
    change col (c.val (longRowCells μ j)) < μ.rowLen (row (c.val (longRowCells μ j))) at hm
    change col (c.val (longRowCells μ j))=μ.rowLen 1+j.val at hc
    omega
  apply Subtype.ext
  exact Prod.ext hr hc

theorem long_row_dimension (hrow : 0<μ.rowLen 1) :
    μ.rowLen 0-μ.rowLen 1 ≤ Module.finrank ℂ (SpechtSpace μ) := by
  let a : Cell μ := ⟨(1,0),YoungDiagram.mem_iff_lt_rowLen.mpr hrow⟩
  have hh := singleton_column_dimension μ a (by change (1:ℕ)≠0; omega)
    (longRowCells μ) (fun _ => rfl) (longRowCells_fixed μ)
  simpa only [Fintype.card_fin] using hh

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young

lemma transpose_card (μ : YoungDiagram) : μ.transpose.card=μ.card := by
  simp

lemma positive_list_tail_injective {a b : List ℕ}
    (ha : ∀x∈a,0<x) (hb : ∀x∈b,0<x)
    (hs : a.sum=b.sum) (ht : a.tail=b.tail) : a=b := by
  cases a with
  | nil =>
    cases b with
    | nil => rfl
    | cons x b =>
      have hh := hb x (by simp)
      simp only [List.sum_nil,List.sum_cons] at hs
      omega
  | cons x a =>
    cases b with
    | nil =>
      have hh := ha x (by simp)
      simp only [List.sum_nil,List.sum_cons] at hs
      omega
    | cons y b =>
      simp only [List.tail_cons] at ht
      subst b
      simp only [List.sum_cons] at hs
      have he : x=y := by omega
      subst y
      rfl

lemma tailCode_injective {n k : ℕ} : Function.Injective (tailCode (n:=n) (k:=k)) := by
  intro p q he
  have ho : longOriented (diagram p.val)=longOriented (diagram q.val) := by
    apply YoungDiagram.equivListRowLens.injective
    apply Subtype.ext
    apply positive_list_tail_injective (YoungDiagram.pos_of_mem_rowLens _) (YoungDiagram.pos_of_mem_rowLens _)
    · rw [rowLens_sum,rowLens_sum,longOriented_card,longOriented_card,diagram_card,diagram_card]
    · exact congrArg (fun c : Bool × Composition k => c.2.blocks) he
  have hb := congrArg Prod.fst he
  change decide ((diagram p.val).colLen 0 ≤ (diagram p.val).rowLen 0)=
    decide ((diagram q.val).colLen 0 ≤ (diagram q.val).rowLen 0) at hb
  have hi := of_decide_eq_true (show decide (((diagram p.val).colLen 0 ≤ (diagram p.val).rowLen 0) ↔
    ((diagram q.val).colLen 0 ≤ (diagram q.val).rowLen 0))=true from by simp [hb])
  apply Subtype.ext
  apply diagram_injective
  unfold longOriented at ho
  by_cases hp : (diagram p.val).colLen 0 ≤ (diagram p.val).rowLen 0
  · simpa [hp,hi.mp hp] using ho
  · have hq : ¬(diagram q.val).colLen 0 ≤ (diagram q.val).rowLen 0 := fun hh => hp (hi.mpr hh)
    have hh := congrArg YoungDiagram.transpose ho
    simpa [hp,hq] using hh

theorem flatTail_card (n k : ℕ) :
    Fintype.card {p : n.Partition // flatTail (diagram p)=k} ≤ 2*2^k := by
  have h := Fintype.card_le_of_injective (tailCode (n:=n) (k:=k)) tailCode_injective
  simp only [Fintype.card_prod,Fintype.card_bool,composition_card] at h
  exact h.trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by omega) (by omega)))

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Mixing_ShapeDimension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young

lemma rowLen_one_le_tail (μ : YoungDiagram) : μ.rowLen 1 ≤ μ.rowLens.tail.sum := by
  by_cases hh : μ.colLen 0≤1
  · have hz : μ.rowLen 1=0 := by
      by_contra hn
      have hm : (1,0)∈μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hc := YoungDiagram.mem_iff_lt_colLen.mp hm
      omega
    rw [hz]; omega
  · have hl : 1<μ.rowLens.length := by rw [YoungDiagram.length_rowLens]; omega
    have hmem : μ.rowLen 1 ∈ μ.rowLens.tail := by
      have hh := List.getElem_mem (show 0<μ.rowLens.tail.length from by simp; omega)
      simpa using hh
    exact List.single_le_sum (by simp) _ hmem

lemma rowLen_one_pos_of_tail (μ : YoungDiagram) (h : 0<μ.card-μ.rowLen 0) :
    0<μ.rowLen 1 := by
  have ht : 0<μ.rowLens.tail.sum := by rwa [rowLens_tail_sum]
  have hc : 1<μ.colLen 0 := by
    by_contra hn
    have ha : μ.colLen 0=0 ∨ μ.colLen 0=1 := by omega
    rcases ha with ha|ha <;> simp [YoungDiagram.rowLens,ha] at ht
  exact YoungDiagram.mem_iff_lt_rowLen.mp (YoungDiagram.mem_iff_lt_colLen.mpr hc)

lemma longOriented_dimension (μ : YoungDiagram) :
    Module.finrank ℂ (SpechtSpace (longOriented μ))=Module.finrank ℂ (SpechtSpace μ) := by
  by_cases h : μ.colLen 0 ≤ μ.rowLen 0
  · exact congrArg (fun ν => Module.finrank ℂ (SpechtSpace ν)) (ite_eq_left h)
  · exact (congrArg (fun ν => Module.finrank ℂ (SpechtSpace ν)) (ite_eq_right h)).trans
      (specht_finrank_transpose μ).symm

lemma dimension_grows (μ : YoungDiagram) (hk : 0 < flatTail μ) :
    μ.card-2*flatTail μ ≤ Module.finrank ℂ (SpechtSpace μ) := by
  have ht : (longOriented μ).card-(longOriented μ).rowLen 0=flatTail μ := by
    rw [longOriented_card,longOriented_row]; rfl
  have hr := rowLen_one_pos_of_tail (longOriented μ) (by rwa [ht])
  have hh := long_row_dimension (longOriented μ) hr
  rw [longOriented_dimension] at hh
  have hle := rowLen_one_le_tail (longOriented μ)
  rw [rowLens_tail_sum,ht] at hle
  have hc := height_width_le_card μ
  have hc' : max (μ.colLen 0) (μ.rowLen 0)≤μ.card := by simpa using hc
  rw [longOriented_row] at hh
  unfold flatTail at *
  omega

lemma partition_dimension_pos {n : ℕ} (p : n.Partition) :
    0<Module.finrank ℂ (PartitionHilbert p) := by
  exact Signed.irreducible_finrank_pos (partitionHilbertRep p)

lemma partition_dimension_grows {n k : ℕ} (p : n.Partition)
    (hp : flatTail (diagram p)=k) (hk : 0<k) :
    n-2*k ≤ Module.finrank ℂ (PartitionHilbert p) := by
  rw [hilbertSpecht_finrank]
  have hh := dimension_grows (diagram p) (by rwa [hp])
  rwa [diagram_card,hp] at hh

lemma partition_log_lower {n k : ℕ} (p : n.Partition) (hp : flatTail (diagram p)=k) :
    (Real.log 2/2)*(k:ℝ)≤Real.log (Module.finrank ℂ (PartitionHilbert p)) := by
  rw [hilbertSpecht_finrank,←hp]
  simpa only [flatTail,Fintype.card_coe] using log_dimension_lower (diagram p)

lemma partition_dimension_gt_one {n : ℕ} (p : n.Partition)
    (hp : 0<flatTail (diagram p)) : 1<Module.finrank ℂ (PartitionHilbert p) := by
  have hd := partition_dimension_pos p
  have hl := partition_log_lower p rfl
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  by_contra hn
  have he : Module.finrank ℂ (PartitionHilbert p)=1 := by omega
  rw [he,Nat.cast_one,Real.log_one] at hl
  have hk : (0:ℝ)<flatTail (diagram p) := by exact_mod_cast hp
  nlinarith

open Irrep

lemma row_shape_cells (μ : YoungDiagram) (hμ : μ.card=μ.rowLen 0) (x : Cell μ) : row x=0 := by
  have ht := rowLen_one_le_tail μ
  rw [rowLens_tail_sum,hμ,Nat.sub_self] at ht
  have hm := YoungDiagram.mem_iff_lt_rowLen.mp x.property
  by_contra hn
  have ha := μ.rowLen_anti 1 (row x) (by omega)
  change col x<μ.rowLen (row x) at hm
  omega

lemma row_shape_tabloid (μ : YoungDiagram) (hμ : μ.card=μ.rowLen 0) (s t : Tabloid μ) : s=t := by
  obtain ⟨g,rfl⟩ := tabloidOfPerm_surjective μ s
  obtain ⟨h,rfl⟩ := tabloidOfPerm_surjective μ t
  apply Subtype.ext
  funext x
  exact (row_shape_cells μ hμ _).trans (row_shape_cells μ hμ _).symm

lemma hilbertSpecht_row (μ : YoungDiagram) (hμ : μ.card=μ.rowLen 0)
    (g : G μ) (v : SpechtHilbert μ) : hilbertSpecht μ g v=v := by
  apply Subtype.ext
  apply PiLp.ext
  intro t
  rw [hilbertSpecht_coeff,row_shape_tabloid μ hμ (g⁻¹ • t) t]

lemma row_average_zero {X : Type*} [Fintype X] [DecidableEq X]
    (μ : YoungDiagram) (hμ : μ.card=μ.rowLen 0) (e : Cell μ ≃ X) (p : Equiv.Perm X → ℂ)
    (hp : ∑g,p g=0) : groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom) p=0 := by
  apply LinearMap.ext
  intro v
  simp only [groupAverage,LinearMap.sum_apply,LinearMap.smul_apply,MonoidHom.comp_apply]
  change (∑g,p g • hilbertSpecht μ _ v)=0
  simp only [hilbertSpecht_row μ hμ,←Finset.sum_smul,hp,zero_smul]

lemma transpose_slot_moment {X : Type*} [Fintype X] [DecidableEq X]
    (μ : YoungDiagram) (e : Cell μ ≃ X) (p : Equiv.Perm X → ℂ) (q : ℕ) :
    evenMoment q (groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom) p)=
    evenMoment q (groupAverage ((hilbertSpecht μ.transpose).comp
      ((transposeCells μ).symm.trans e).symm.permCongrHom.toMonoidHom)
      (fun g => p g*(realSign g:ℂ))) := by
  rw [groupAverage_comp_slots,groupAverage_comp_slots,hilbert_transpose_moment]
  congr 2
  funext g
  congr 1
  change signC μ.transpose g=(realSign (((transposeCells μ).symm.trans e).permCongr g):ℂ)
  rw [realSign_permCongr_complex]
  change ((Equiv.Perm.sign g:ℤ):ℂ)=(((Equiv.Perm.sign g:ℤ):ℝ):ℂ)
  norm_cast

theorem flat_shape_moment_zero {X : Type*} [Fintype X] [DecidableEq X]
    (μ : YoungDiagram) (e : Cell μ ≃ X) (p : Equiv.Perm X → ℂ)
    (hμ : flatTail μ=0) (hp : ∑g,p g=0) (hs : ∑g,p g*(realSign g:ℂ)=0) :
    evenMoment 1 (groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom) p)=0 := by
  have hc : max (μ.colLen 0) (μ.rowLen 0)≤μ.card := by simpa using height_width_le_card μ
  have hh : μ.card=μ.rowLen 0 ∨ μ.card=μ.colLen 0 := by
    unfold flatTail at hμ
    omega
  rcases hh with hh|hh
  · rw [row_average_zero μ hh e p hp]
    simp [evenMoment]
  · rw [transpose_slot_moment]
    have ht : μ.transpose.card=μ.transpose.rowLen 0 := by
      rw [transpose_card,YoungDiagram.rowLen_transpose,hh]
    rw [row_average_zero μ.transpose ht _ _ hs]
    simp [evenMoment]

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Irrep Young

lemma sign_convolution {X : Type*} [Fintype X] [DecidableEq X]
    (p q : Equiv.Perm X → ℝ) :
    (∑g,convolution p q g*realSign g)=(∑g,p g*realSign g)*(∑g,q g*realSign g) := by
  simp only [convolution,Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    _ = ∑x,∑y,p x*q y*realSign (x*y) := by
      apply Finset.sum_congr rfl
      intro x _
      simpa only [Equiv.coe_mulLeft,inv_mul_cancel_left] using
        (Equiv.sum_comp (Equiv.mulLeft x) (fun g => p x*q (x⁻¹*g)*realSign g)).symm
    _ = _ := by
      simp only [map_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      ring

lemma sweep_sign_zero {d w : ℕ} (hd : 0<d) (hw : 0<w) :
    (∑g,sweepLaw d w g*realSign g)=0 := by
  obtain ⟨w,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : w≠0)
  rw [sweepLaw,convolutionPower,sign_convolution,binary_sign_annihilated d hd,zero_mul]

lemma sweep_centered_mass (d w : ℕ) :
    (∑g : Equiv.Perm (Slot d),((sweepLaw d w g:ℝ)-uniformLaw _ g:ℂ))=0 := by
  simp only [←Complex.ofReal_sub]
  rw [←Complex.ofReal_sum,Finset.sum_sub_distrib]
  have hp : IsProbability (sweepLaw d w) := convolutionPower_probability
    ⟨finiteLaw_nonneg _,finiteLaw_sum _⟩ w
  rw [hp.2,uniformLaw_sum,sub_self,Complex.ofReal_zero]

lemma sweep_centered_sign {d w : ℕ} (hd : 0<d) (hw : 0<w) :
    (∑g : Equiv.Perm (Slot d),((sweepLaw d w g:ℝ)-uniformLaw _ g:ℂ)*(realSign g:ℂ))=0 := by
  have : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  simp only [←Complex.ofReal_mul,←Complex.ofReal_sum,sub_mul,Finset.sum_sub_distrib,
    sweep_sign_zero hd hw,uniform_sign_zero,sub_self,Complex.ofReal_zero]

lemma variation_fourier_equiv {X : Type} [Fintype X] [DecidableEq X]
    {n : ℕ} (e : X ≃ Fin n) (p q : Equiv.Perm X → ℝ) :
    totalVariation p q ^2 ≤ (1/4:ℝ)*
      ∑ℓ : n.Partition,(Module.finrank ℂ (PartitionHilbert ℓ):ℝ)*
        evenMoment 1 (groupAverage ((partitionHilbertRep ℓ).comp e.permCongrHom.toMonoidHom)
          (fun g => (p g-q g:ℂ))) := by
  have ht := Fourier.variation_fourier_bound (p ∘ e.symm.permCongr) (q ∘ e.symm.permCongr)
  have he : totalVariation (p ∘ e.symm.permCongr) (q ∘ e.symm.permCongr)=totalVariation p q := by
    unfold totalVariation
    congr 1
    exact Equiv.sum_comp e.symm.permCongr (fun g => |p g-q g|)
  rw [he] at ht
  convert ht using 2
  apply Finset.sum_congr rfl
  intro ℓ _
  have hh := groupAverage_comp_slots e.symm (partitionHilbertRep ℓ)
    (fun g => (p g-q g:ℂ))
  simpa only [Equiv.symm_symm,Function.comp_apply] using
    congrArg (fun A => (Module.finrank ℂ (PartitionHilbert ℓ):ℝ)*evenMoment 1 A) hh

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Mixing_DimensionSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young

lemma dimensionInv_nonneg {n : ℕ} (p : n.Partition) : 0≤dimensionInv p := by
  unfold dimensionInv; positivity

lemma dimensionInv_exponential {n k : ℕ} (p : n.Partition) (hp : flatTail (diagram p)=k) :
    dimensionInv p≤(1/16:ℝ)^k := by
  have hD : (0:ℝ)<Module.finrank ℂ (PartitionHilbert p) := by exact_mod_cast partition_dimension_pos p
  have hl := partition_log_lower p hp
  have hh : (16:ℝ)^k≤(Module.finrank ℂ (PartitionHilbert p):ℝ)^8 := by
    apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    rw [Real.log_pow,Real.log_pow]
    have h16 : Real.log (16:ℝ)=4*Real.log 2 := by
      rw [show (16:ℝ)=2^4 by norm_num,Real.log_pow]
      norm_num
    rw [h16]
    norm_num only [Nat.cast_ofNat]
    nlinarith
  have hi := (inv_le_inv₀ (by positivity : (0:ℝ)<(Module.finrank ℂ (PartitionHilbert p):ℝ)^8)
    (by positivity : (0:ℝ)<16^k)).mpr hh
  simpa only [dimensionInv,one_div,inv_pow] using hi

lemma dimensionFiber_nonneg (n k : ℕ) : 0≤dimensionFiber n k := by
  unfold dimensionFiber
  split
  · rfl
  · exact Finset.sum_nonneg (fun _ _ => dimensionInv_nonneg _)

lemma dimensionFiber_bound (n k : ℕ) : dimensionFiber n k≤2*(1/8:ℝ)^k := by
  by_cases hk : k=0
  · simp [dimensionFiber,hk]
  rw [dimensionFiber,ite_eq_right hk]
  calc
    _ ≤ (Fintype.card {p : n.Partition // flatTail (diagram p)=k}:ℝ)*(1/16:ℝ)^k := by
      calc
        _ ≤ ∑p : {p : n.Partition // flatTail (diagram p)=k}, (1/16:ℝ)^k :=
          Finset.sum_le_sum (fun p _ => dimensionInv_exponential p.val p.property)
        _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    _ ≤ (2*2^k:ℝ)*(1/16:ℝ)^k := by
      have hh : (Fintype.card {p : n.Partition // flatTail (diagram p)=k}:ℝ)≤2*2^k := by
        exact_mod_cast flatTail_card n k
      exact mul_le_mul_of_nonneg_right hh (by positivity)
    _ = _ := by rw [mul_assoc,←mul_pow]; norm_num

lemma dimensionFiber_grows_bound {n k : ℕ} (hk : 0<k) (hn : 2*k<n) :
    dimensionFiber n k≤(2*2^k:ℝ)*(((n-2*k:ℕ):ℝ)⁻¹)^8 := by
  rw [dimensionFiber,ite_eq_right (by omega : k≠0)]
  have hp : (0:ℝ)<(n-2*k:ℕ) := by exact_mod_cast (show 0<n-2*k by omega)
  calc
    _ ≤ (Fintype.card {p : n.Partition // flatTail (diagram p)=k}:ℝ)*(((n-2*k:ℕ):ℝ)⁻¹)^8 := by
      calc
        _ ≤ ∑p : {p : n.Partition // flatTail (diagram p)=k}, (((n-2*k:ℕ):ℝ)⁻¹)^8 := ?_
        _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      apply Finset.sum_le_sum
      intro p _
      have hd : ((n-2*k:ℕ):ℝ)≤Module.finrank ℂ (PartitionHilbert p.val) := by
        exact_mod_cast partition_dimension_grows p.val p.property hk
      have hi := one_div_le_one_div_of_le hp hd
      simp only [dimensionInv,←inv_pow]
      apply pow_le_pow_left₀ (by positivity)
      simpa only [one_div] using hi
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast flatTail_card n k) (by positivity)

lemma dimensionFiber_tendsto (k : ℕ) :
    Filter.Tendsto (fun n => dimensionFiber n k) Filter.atTop (nhds 0) := by
  by_cases hk : k=0
  · subst k
    simpa only [dimensionFiber,ite_true] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0:ℝ)) Filter.atTop (nhds 0))
  have ht : Filter.Tendsto (fun n : ℕ => n-2*k) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    exact Filter.eventually_atTop.2 ⟨b+2*k,fun n hn => by omega⟩
  have hr : Filter.Tendsto (fun n : ℕ => ((n-2*k:ℕ):ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp ht
  have hlim : Filter.Tendsto (fun n : ℕ => (2*2^k:ℝ)*(((n-2*k:ℕ):ℝ)⁻¹)^8)
      Filter.atTop (nhds 0) := by
    simpa using (hr.inv_tendsto_atTop.pow 8).const_mul (2*2^k:ℝ)
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => dimensionFiber_nonneg n k)) _ hlim
  exact Filter.eventually_atTop.2 ⟨2*k+1,fun n hn => dimensionFiber_grows_bound (by omega) (by omega)⟩

lemma dimensionFiber_eq_filter (n k : ℕ) : dimensionFiber n k=
    ∑p ∈ Finset.univ.filter (fun p : n.Partition => flatTail (diagram p)=k),
      if flatTail (diagram p)=0 then 0 else dimensionInv p := by
  unfold dimensionFiber
  split
  · subst k
    symm
    apply Finset.sum_eq_zero
    intro p hp
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hp
    simp only [hp,ite_true]
  · rename_i hk
    rw [Finset.sum_subtype _ (by simp : ∀p : n.Partition,
      p ∈ Finset.univ.filter (fun p => flatTail (diagram p)=k) ↔ flatTail (diagram p)=k)]
    apply Finset.sum_congr rfl
    intro p _
    rw [ite_eq_right (by rw [p.property]; exact hk)]

lemma dimensionSeries_tsum (n : ℕ) : dimensionSeries n=∑'k,dimensionFiber n k := by
  rw [tsum_eq_sum (s:=Finset.range (n+1))]
  · simp_rw [dimensionFiber_eq_filter]
    symm
    apply Finset.sum_fiberwise_of_maps_to
    intro p _
    simp only [Finset.mem_range]
    have ht : flatTail (diagram p)≤n := by unfold flatTail; rw [diagram_card]; omega
    omega
  · intro k hk
    by_cases he : k=0
    · simp [dimensionFiber,he]
    rw [dimensionFiber,ite_eq_right he]
    apply Finset.sum_eq_zero
    intro p _
    have ht : flatTail (diagram p.val)≤n := by unfold flatTail; rw [diagram_card]; omega
    have hp := p.property
    simp only [Finset.mem_range,not_lt] at hk
    omega

theorem dimensionSeries_tendsto : Filter.Tendsto dimensionSeries Filter.atTop (nhds 0) := by
  have hs : Summable (fun k : ℕ => 2*(1/8:ℝ)^k) :=
    Summable.mul_left 2 (summable_geometric_of_norm_lt_one (by norm_num))
  have ht := tendsto_tsum_of_dominated_convergence hs dimensionFiber_tendsto
    (Filter.Eventually.of_forall (fun n k => by
      rw [Real.norm_eq_abs,abs_of_nonneg (dimensionFiber_nonneg n k)]
      exact dimensionFiber_bound n k))
  simpa only [←dimensionSeries_tsum,tsum_zero] using ht

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Mixing_BinaryMixingBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Irrep Young

lemma decay_eighth {D : ℝ} (hD : 0<D) :
    D*(D*(D^(-5:ℝ))^2)=(D^8)⁻¹ := by
  rw [Real.rpow_neg hD.le,show D^(5:ℝ)=D^5 from Real.rpow_natCast D 5]
  field_simp

lemma centered_power_moment {d w : ℕ} {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Slot d)) V) [ρ.IsIrreducible]
    (hD : 1<Module.finrank ℂ V) {g : ℝ} (hgw : 5≤g*(w:ℝ))
    (hA : ‖complexAverage ρ (fun g => (binaryLaw d g:ℂ))‖≤(Module.finrank ℂ V:ℝ)^(-g)) :
    (Module.finrank ℂ V:ℝ)*evenMoment 1
      (groupAverage ρ (fun g => (sweepLaw d w g-uniformLaw _ g:ℂ))) ≤
        ((Module.finrank ℂ V:ℝ)^8)⁻¹ := by
  obtain ⟨v,hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp
    (show 0<Module.finrank ℂ V from by omega)
  have : Nontrivial V := ⟨⟨v,0,hv⟩⟩
  let D : ℝ := Module.finrank ℂ V
  have hp : 0<D := by dsimp [D]; exact_mod_cast (by omega : 0<Module.finrank ℂ V)
  have hone : 1≤D := by dsimp [D]; exact_mod_cast hD.le
  have he : complexAverage ρ (fun g => (sweepLaw d w g-uniformLaw _ g:ℂ))=
      (complexAverage ρ (fun g => (binaryLaw d g:ℂ)))^w := by
    simp only [complexAverage_sub,complexAverage_uniform_zero ρ hD,
      sub_zero,sweepLaw,complexAverage_power]
  have hb : ‖complexAverage ρ (fun g => (sweepLaw d w g-uniformLaw _ g:ℂ))‖≤D^(-5:ℝ) := by
    rw [he]
    calc
      _ ≤ ‖complexAverage ρ (fun g => (binaryLaw d g:ℂ))‖^w := norm_pow_le _ _
      _ ≤ (D^(-g))^w := pow_le_pow_left₀ (norm_nonneg _) hA w
      _ = D^((-g)*(w:ℝ)) := (Real.rpow_mul_natCast hp.le _ _).symm
      _ ≤ D^(-5:ℝ) := Real.rpow_le_rpow_of_exponent_le hone (by nlinarith)
  have hm := evenMoment_one_norm_bound
    (complexAverage ρ (fun g => (sweepLaw d w g-uniformLaw _ g:ℂ)))
    (Real.rpow_nonneg hp.le _) hb
  change evenMoment 1 (groupAverage ρ _)≤D*(D^(-5:ℝ))^2 at hm
  exact (mul_le_mul_of_nonneg_left hm hp.le).trans_eq (decay_eighth hp)

lemma partition_slot_flat {d : ℕ} (p : (2^d).Partition) (w : ℕ)
    (hd : 0<d) (hw : 0<w) (hp : flatTail (diagram p)=0) :
    evenMoment 1 (groupAverage
      ((partitionHilbertRep p).comp (binarySlotsFin d).permCongrHom.toMonoidHom)
      (fun g => (sweepLaw d w g-uniformLaw _ g:ℂ)))=0 := by
  have he : (partitionHilbertRep p).comp (binarySlotsFin d).permCongrHom.toMonoidHom=
      (hilbertSpecht (diagram p)).comp
        ((cellsEquivFin p).trans (binarySlotsFin d).symm).symm.permCongrHom.toMonoidHom := by
    rfl
  rw [he]
  exact flat_shape_moment_zero _ _ _ hp (sweep_centered_mass d w) (sweep_centered_sign hd hw)

theorem binary_variation_bound_exists : ∃ w : ℕ, 0<w ∧ ∃ d₀ : ℕ,
    ∀ d ≥ d₀, totalVariation (sweepLaw d w) (uniformLaw (Equiv.Perm (Slot d)))^2 ≤
      (1/4:ℝ)*dimensionSeries (2^d) := by
  obtain ⟨g,hg,d₀,hcont⟩ := binary_hilbert_contraction
  obtain ⟨w,hw⟩ := exists_nat_gt (5/g)
  have hwpos : 0<w := by
    have hh : (0:ℝ)<(w:ℝ) := (div_pos (by norm_num) hg).trans hw
    exact_mod_cast hh
  have hgw : 5≤g*(w:ℝ) := by
    have hh := (div_lt_iff₀ hg).mp hw
    nlinarith
  refine ⟨w,hwpos,max d₀ 1,?_⟩
  intro d hd
  have hd₀ : d₀≤d := (le_max_left _ _).trans hd
  have hdpos : 0<d := by have := (le_max_right d₀ 1).trans hd; omega
  refine (variation_fourier_equiv (binarySlotsFin d) _ _).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  unfold dimensionSeries
  apply Finset.sum_le_sum
  intro p _
  by_cases hp : flatTail (diagram p)=0
  · rw [ite_eq_left hp,partition_slot_flat p w hdpos hwpos hp,mul_zero]
  · rw [ite_eq_right hp]
    let ρ : Representation ℂ (Equiv.Perm (Slot d)) (PartitionHilbert p) :=
      (partitionHilbertRep p).comp (binarySlotsFin d).permCongrHom.toMonoidHom
    have : ρ.IsIrreducible := irreducible_comp_equiv _ _
    exact centered_power_moment ρ (partition_dimension_gt_one p (by omega)) hgw
      (hcont d hd₀ _ ρ inferInstance (fun g v => partitionHilbertRep_unitary p _ v))

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Young

lemma binary_dimension_series_tendsto : Filter.Tendsto (fun d : ℕ => dimensionSeries (2^d))
    Filter.atTop (nhds 0) := by
  apply dimensionSeries_tendsto.comp
  apply Filter.tendsto_atTop.2
  intro b
  exact Filter.eventually_atTop.2 ⟨b,fun d hd => hd.trans (Nat.le_of_lt d.lt_two_pow_self)⟩

theorem constant_sweep_mixing_oai : ConstantSweepMixingTarget := by
  obtain ⟨w,hw,d₀,hbound⟩ := binary_variation_bound_exists
  refine ⟨w,?_⟩
  intro ε hε
  have heps : 0<4*ε^2 := by positivity
  have ht : ∀ᶠ d : ℕ in Filter.atTop, dimensionSeries (2^d)<4*ε^2 :=
    (Filter.Tendsto.eventually_lt_const heps binary_dimension_series_tendsto)
  obtain ⟨d₁,hd₁⟩ := Filter.eventually_atTop.1 ht
  refine ⟨max d₀ d₁,?_⟩
  intro d hd τ
  rw [totalVariation_fromInitial]
  have hb := hbound d ((le_max_left _ _).trans hd)
  have hs := hd₁ d ((le_max_right _ _).trans hd)
  have hh : totalVariation (sweepLaw d w) (uniformLaw (Equiv.Perm (Slot d)))^2<ε^2 := by
    nlinarith
  nlinarith

end BinaryCoordinateSweeps

end

end OAI
end

theorem solution : type_of% @OAI.BinaryCoordinateSweeps.constant_sweep_mixing_oai := @OAI.BinaryCoordinateSweeps.constant_sweep_mixing_oai
