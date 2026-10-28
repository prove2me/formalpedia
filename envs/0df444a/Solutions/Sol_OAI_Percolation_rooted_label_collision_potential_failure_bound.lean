-- Prove2me | solution 1 for OAI.Percolation.rooted_label_collision_potential_failure_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T01:10:36.487732+00:00
-- url     : https://prove2.me/submissions/2b05da48-f287-4528-84d7-fbdae9664b2b

import Mathlib
import Definitions.Def_CayleyPercolation
import Definitions.Def_OAIQ040C002
import Theorems.Thm_OAI_Percolation_conditional_first_escape_collision_bound

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Graph_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Indexed bond graphs, connectivity, percolation laws, kernels and countability. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section Probability
variable (G : BondGraph V E)

theorem twoPoint_symm (p : unitInterval) (x y : V) : twoPoint G p x y = twoPoint G p y x := by
  have he : {ω | Conn G ω x y} = {ω | Conn G ω y x} := by
    ext ω
    exact ⟨conn_symm G ω, conn_symm G ω⟩
  simp only [twoPoint, he]

end Probability

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_Bounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Kernel domination, monotone couplings and endpoint bounds. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section KernelLimits
open scoped Topology
open Filter
attribute [local instance] Classical.propDecidable


theorem finiteEmbedding_dense : DenseRange (finiteEmbedding (V := V)) := by
  intro f
  apply isClosed_closure.mem_of_tendsto (lp.hasSum_single (by norm_num) f)
  apply Eventually.of_forall
  intro s
  apply subset_closure
  refine ⟨∑ y ∈ s, Finsupp.single y (f y), ?_⟩
  simp



end KernelLimits

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_Spectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Isoperimetric energy, symmetric walks and invariant operator traces. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section IsoperimetricEnergy
attribute [local instance] Classical.propDecidable


theorem adj_symm (G : BondGraph V E) {x y : V} (h : Adj G x y) : Adj G y x := by
  obtain ⟨e,he⟩ := h
  exact ⟨e,he.trans (Sym2.eq_swap)⟩

end IsoperimetricEnergy

section FiniteQuadraticForms
attribute [local instance] Classical.propDecidable

 theorem kernel_finiteEmbedding (A : Hilbert V →L[ℂ] Hilbert V)
    (U : V → V → ℝ) (hA : ∀ x y, A (lp.single 2 y (1 : ℂ)) x = (U x y : ℂ))
    (f : V →₀ ℂ) (x : V) :
    A (finiteEmbedding f) x = ∑ y ∈ f.support, f y * (U x y : ℂ) := by
  simp only [finiteEmbedding, Finsupp.linearCombination_apply, Finsupp.sum,
    map_sum, map_smul]
  change (∑ y ∈ f.support, f y • A (lp.single 2 y (1 : ℂ))) x = _
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
    hA, smul_eq_mul]

 theorem symmetric_of_symmetric_kernel (A : Hilbert V →L[ℂ] Hilbert V)
    (U : V → V → ℝ) (hA : ∀ x y, A (lp.single 2 y (1 : ℂ)) x = (U x y : ℂ))
    (hU : ∀ x y, U x y = U y x) : A.toLinearMap.IsSymmetric := by
  apply finiteEmbedding_dense.induction_on₂
    (p := fun f g => inner ℂ (A f) g = inner ℂ f (A g))
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro f g
    simp only [finiteEmbedding_inner_left, finiteEmbedding_inner_right,
      kernel_finiteEmbedding A U hA, map_sum, map_mul, RCLike.star_def,
      Complex.conj_ofReal]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [hU y x]
    ring

end FiniteQuadraticForms

section SymmetricWalk
attribute [local instance] Classical.propDecidable



 theorem walkKernel_symmetric (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (x y : V) : walkKernel G hloc a x y = walkKernel G hloc a y x := by
  have ha : Adj G x y ↔ Adj G y x := ⟨adj_symm G,adj_symm G⟩
  by_cases h : x = y
  · subst y; rfl
  · simp [walkKernel,h,Ne.symm h,ha]

 theorem walkKernel_row_sum (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (x : V) :
    ∑ y ∈ insert x (neighbors G hloc x), walkKernel G hloc a x y = 1 := by
  let N := neighbors G hloc x
  have hf : (insert x N).filter (fun y => Adj G x y) = N := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_insert]
    rw [mem_neighbors]
    exact ⟨fun h => h.2, fun h => ⟨Or.inr h,h⟩⟩
  simp only [walkKernel, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_insert_self,ite_true]
  rw [← Finset.sum_filter,hf]
  simp only [Finset.sum_const, nsmul_eq_mul]
  dsimp [N]
  ring

end SymmetricWalk

section PositiveConnectionKernel
open scoped ComplexOrder Matrix
attribute [local instance] Classical.propDecidable

 

theorem equivalenceMatrix_posSemidef {α : Type*} [Fintype α] (R : Setoid α) :
    Matrix.PosSemidef (fun x y => if R.r x y then (1:ℂ) else 0) := by
  classical
  let : Fintype (Quotient R) := Fintype.ofFinite (Quotient R)
  let J : Matrix (Quotient R) α ℂ := fun q x => if q = Quotient.mk R x then 1 else 0
  have hJ : Jᴴ * J = (fun x y => if R.r x y then (1:ℂ) else 0) := by
    ext x y
    change (∑ q : Quotient R, star (J q x) * J q y) = _
    have hr : R.r y x ↔ R.r x y := ⟨R.symm, R.symm⟩
    simp [J, Quotient.eq, hr]
  rw [← hJ]
  exact Matrix.posSemidef_conjTranspose_mul_self J

theorem connection_quadratic_nonneg (G : BondGraph V E) (ω : Set E)
    (S : Finset V) (f : V → ℂ) :
    0 ≤ ∑ x ∈ S, ∑ y ∈ S,
      star (f x) * (if Conn G ω x y then (1:ℂ) else 0) * f y := by
  classical
  let R : Setoid S := ⟨fun x y => Conn G ω x y,
    ⟨fun x => conn_refl G ω x, fun h => conn_symm G ω h, fun h h' => conn_trans G ω h h'⟩⟩
  have h := (equivalenceMatrix_posSemidef R).dotProduct_mulVec_nonneg
    (fun x : S => f x)
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply] at h
  change 0 ≤ ∑ x : S, ∑ y : S,
    star (f x) * ((if Conn G ω x y then (1:ℂ) else 0) * f y) at h
  have he : (∑ x : S, ∑ y : S,
      star (f x) * ((if Conn G ω x y then (1:ℂ) else 0) * f y)) =
      ∑ x ∈ S, ∑ y ∈ S,
      star (f x) * ((if Conn G ω x y then (1:ℂ) else 0) * f y) := by
    rw [Finset.sum_coe_sort S (fun x => ∑ y : S,
      star (f x) * ((if Conn G ω x y then (1:ℂ) else 0) * f y))]
    apply Finset.sum_congr rfl
    intro x _
    exact Finset.sum_coe_sort S (fun y =>
      star (f x) * ((if Conn G ω x y then (1:ℂ) else 0) * f y))
  rw [he] at h
  simpa only [mul_assoc] using h

variable [Countable V] [Countable E]

theorem conn_indicator_integrable (G : BondGraph V E) (p : unitInterval) (x y : V) :
    Integrable (fun ω => if Conn G ω x y then (1:ℂ) else 0) (law p) := by
  change Integrable ({ω | Conn G ω x y}.indicator (fun _ => (1:ℂ))) (law p)
  exact (integrable_const (1:ℂ)).indicator (measurableSet_conn G x y)

theorem twoPoint_eq_integral (G : BondGraph V E) (p : unitInterval) (x y : V) :
    (twoPoint G p x y : ℂ) =
      ∫ ω, (if Conn G ω x y then (1:ℂ) else 0) ∂law p := by
  simpa only [Set.indicator, Set.mem_ofPred_eq, Measure.real, twoPoint,
    Complex.real_smul, mul_one] using
    (integral_indicator_const (μ := law p) (1:ℂ) (measurableSet_conn G x y)).symm

theorem twoPoint_quadratic_nonneg (G : BondGraph V E) (p : unitInterval)
    (S : Finset V) (f : V → ℂ) :
    0 ≤ ∑ x ∈ S, ∑ y ∈ S, star (f x) * (twoPoint G p x y : ℂ) * f y := by
  have hi (x y : V) : Integrable
      (fun ω => star (f x) * (if Conn G ω x y then (1:ℂ) else 0) * f y) (law p) :=
    ((conn_indicator_integrable G p x y).const_mul _).mul_const _
  have hsum : (∑ x ∈ S, ∑ y ∈ S, star (f x) * (twoPoint G p x y : ℂ) * f y) =
      ∫ ω, ∑ x ∈ S, ∑ y ∈ S,
        star (f x) * (if Conn G ω x y then (1:ℂ) else 0) * f y ∂law p := by
    rw [integral_finsetSum S (fun x _ => integrable_finsetSum S (fun y _ => hi x y))]
    apply Finset.sum_congr rfl
    intro x _
    rw [integral_finsetSum S (fun y _ => hi x y)]
    apply Finset.sum_congr rfl
    intro y _
    rw [integral_mul_const, integral_const_mul, twoPoint_eq_integral]
  rw [hsum]
  exact integral_nonneg (fun ω => connection_quadratic_nonneg G ω S f)

 

theorem HasKernel.isPositive (G : BondGraph V E) (p : unitInterval)
    (A : Hilbert V →L[ℂ] Hilbert V) (hA : HasKernel G p A) : A.IsPositive := by
  have hs : A.toLinearMap.IsSymmetric :=
    symmetric_of_symmetric_kernel A (twoPoint G p) (fun x y => hA x y) (twoPoint_symm G p)
  refine ⟨hs, ?_⟩
  intro f
  apply finiteEmbedding_dense.induction_on f
    (p := fun g => 0 ≤ (inner ℂ (A g) g).re)
  · exact isClosed_le continuous_const (by fun_prop)
  · intro g
    rw [show inner ℂ (A (finiteEmbedding g)) (finiteEmbedding g) =
      inner ℂ (finiteEmbedding g) (A (finiteEmbedding g)) from hs _ _, finiteEmbedding_inner_left]
    simp only [kernel_finiteEmbedding A (twoPoint G p) (fun x y => hA x y)]
    simp_rw [Finset.mul_sum]
    have h := twoPoint_quadratic_nonneg G p g.support g
    apply Complex.nonneg_iff.mp at h
    convert h.1 using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring

end PositiveConnectionKernel

section InvariantOperatorTrace
open scoped ComplexOrder InnerProduct
attribute [local instance] Classical.propDecidable
local instance spectralContinuousFunctionalCalculus : ContinuousFunctionalCalculus ℝ
    (Hilbert V →L[ℂ] Hilbert V) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus (A := Hilbert V →L[ℂ] Hilbert V)

theorem operator_kernel_hasSum (A : Hilbert V →L[ℂ] Hilbert V) (f : Hilbert V) (x : V) :
    HasSum (fun y => matrixCoeff A x y * f y) (A f x) := by
  have h := ((lp.evalCLM ℂ (fun _ : V => ℂ) 2 x).comp A).hasSum
    (lp.hasSum_single (by norm_num : (2:ℝ≥0∞) ≠ ⊤) f)
  change HasSum (fun y => A (lp.single 2 y (f y)) x) (A f x) at h
  have heq : (fun y : V => A (lp.single 2 y (f y)) x) =
      (fun y => matrixCoeff A x y * f y) := by
    funext y
    have he : lp.single (E := fun _ : V => ℂ) 2 y (f y) =
        f y • lp.single 2 y (1:ℂ) := by
      rw [← lp.single_smul]; simp
    simp [he, matrixCoeff, mul_comm]
  rw [heq] at h
  exact h

@[simp] theorem matrixCoeff_mul (A B : Hilbert V →L[ℂ] Hilbert V) (x y : V) :
    matrixCoeff (A*B) x y = ∑' z, matrixCoeff A x z * matrixCoeff B z y := by
  exact (operator_kernel_hasSum A (B (lp.single 2 y (1:ℂ))) x).tsum_eq.symm


theorem matrixCoeff_invariant_iff (a : V ≃ V) (A : Hilbert V →L[ℂ] Hilbert V) :
    (∀ x y, matrixCoeff A (a x) (a y) = matrixCoeff A x y) ↔
      Commute A (permuteHilbert a).toContinuousLinearEquiv.toContinuousLinearMap := by
  constructor
  · intro h
    change A * (permuteHilbert a).toContinuousLinearEquiv.toContinuousLinearMap =
      (permuteHilbert a).toContinuousLinearEquiv.toContinuousLinearMap * A
    apply lp.ext_continuousLinearMap (by norm_num : (2:ℝ≥0∞) ≠ ⊤)
    intro y
    apply ContinuousLinearMap.ext
    intro c
    ext x
    have hs : lp.single (E := fun _ : V => ℂ) 2 y c =
        c • lp.single 2 y (1:ℂ) := by rw [← lp.single_smul]; simp
    have hh := h (a.symm x) y
    simp only [Equiv.apply_symm_apply] at hh
    change A (permuteHilbert a (lp.single 2 y c)) x =
      permuteHilbert a (A (lp.single 2 y c)) x
    rw [hs]
    simp only [map_smul, permuteHilbert_single, lp.coeFn_smul, Pi.smul_apply,
      permuteHilbert_apply]
    change c * matrixCoeff A x (a y) = c * matrixCoeff A (a.symm x) y
    rw [hh]
  · intro h x y
    have hh := congrArg (fun F : Hilbert V →L[ℂ] Hilbert V =>
      F (lp.single 2 y (1:ℂ)) (a x)) h.eq
    simpa only [mul_apply_eq_comp, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearEquiv.coe_coe, permuteHilbert_single, permuteHilbert_apply,
      Equiv.symm_apply_apply, matrixCoeff] using hh

 attribute [local instance] OAI.Percolation.spectralNonUnitalContinuousFunctionalCalculus
theorem matrixCoeff_sqrt_invariant (a : V ≃ V) (A : Hilbert V →L[ℂ] Hilbert V)
    (h : ∀ x y, matrixCoeff A (a x) (a y) = matrixCoeff A x y) :
    ∀ x y, matrixCoeff (CFC.sqrt A) (a x) (a y) = matrixCoeff (CFC.sqrt A) x y := by
  apply (matrixCoeff_invariant_iff a _).mpr
  rw [CFC.sqrt_eq_cfc]
  exact ((matrixCoeff_invariant_iff a A).mp h).cfc_nnreal NNReal.sqrt

 theorem matrixCoeff_mul_invariant (a : V ≃ V) (A B : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, matrixCoeff A (a x) (a y) = matrixCoeff A x y)
    (hB : ∀ x y, matrixCoeff B (a x) (a y) = matrixCoeff B x y) :
    ∀ x y, matrixCoeff (A*B) (a x) (a y) = matrixCoeff (A*B) x y := by
  intro x y
  simp only [matrixCoeff_mul]
  rw [← a.tsum_eq (fun z => matrixCoeff A (a x) z * matrixCoeff B z (a y))]
  simp only [hA,hB]

 theorem matrixCoeff_nonneg (A : Hilbert V →L[ℂ] Hilbert V) (hA : 0 ≤ A) (x : V) :
    0 ≤ matrixCoeff A x x := by
  rw [matrixCoeff_eq_inner]
  exact ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hA).inner_nonneg_right _

 theorem matrixCoeff_mono {A B : Hilbert V →L[ℂ] Hilbert V} (h : A ≤ B) (x : V) :
    matrixCoeff A x x ≤ matrixCoeff B x x := by
  have hh := matrixCoeff_nonneg (B-A) (sub_nonneg.mpr h) x
  simpa only [matrixCoeff, sub_apply, lp.coeFn_sub,
    Pi.sub_apply, sub_nonneg] using hh

section RootTrace
variable {ι : Type*} [Fintype ι]
variable (root : ι → V) (weight : ι → ℝ)

theorem rootTrace_mono (hw : ∀ i, 0 ≤ weight i)
    {A B : Hilbert V →L[ℂ] Hilbert V} (h : A ≤ B) :
    rootTrace root weight A ≤ rootTrace root weight B := by
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (matrixCoeff_mono h (root i)) (by simpa using hw i)

theorem KernelInvariant.mul {Γ : Set (V ≃ V)}
    {A B : Hilbert V →L[ℂ] Hilbert V}
    (hA : KernelInvariant Γ A) (hB : KernelInvariant Γ B) :
    KernelInvariant Γ (A*B) := by
  intro a ha
  exact matrixCoeff_mul_invariant a A B (hA a ha) (hB a ha)

theorem KernelInvariant.star {Γ : Set (V ≃ V)}
    {A : Hilbert V →L[ℂ] Hilbert V} (hA : KernelInvariant Γ A) :
    KernelInvariant Γ (star A) := by
  intro a ha x y
  simp only [matrixCoeff_adjoint, hA a ha]

attribute [local instance] OAI.Percolation.spectralNonUnitalContinuousFunctionalCalculus
theorem KernelInvariant.sqrt {Γ : Set (V ≃ V)}
    {A : Hilbert V →L[ℂ] Hilbert V} (hA : KernelInvariant Γ A) :
    KernelInvariant Γ (CFC.sqrt A) := by
  intro a ha
  exact matrixCoeff_sqrt_invariant a A (hA a ha)



theorem rootTrace_cyclic {Γ : Set (V ≃ V)}
    (htr : RootTransport root weight Γ)
    (A B : Hilbert V →L[ℂ] Hilbert V)
    (hA : KernelInvariant Γ A) (hB : KernelInvariant Γ B) :
    rootTrace root weight (A*B) = rootTrace root weight (B*A) := by
  have ht := htr (fun x y => matrixCoeff A x y * matrixCoeff B y x)
    (by intro a ha x y; rw [hA a ha, hB a ha])
    (fun x => (operator_kernel_hasSum A (B (lp.single 2 x (1:ℂ))) x).summable)
    (fun y => by
      simpa only [matrixCoeff, mul_comm] using
        (operator_kernel_hasSum B (A (lp.single 2 y (1:ℂ))) y).summable)
  simpa only [rootTrace, matrixCoeff_mul, mul_comm] using ht

theorem rootTrace_diag_le {Γ : Set (V ≃ V)}
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (c : ℝ) (hc : 0 ≤ c)
    (hmin : ∀ i, 1 ≤ c * weight i)
    (A : Hilbert V →L[ℂ] Hilbert V) (hA : KernelInvariant Γ A)
    (hApos : 0 ≤ A) (x : V) :
    matrixCoeff A x x ≤ (c : ℂ) * rootTrace root weight A := by
  obtain ⟨i,a,ha,hax⟩ := hcov x
  have hi : (weight i : ℂ) * matrixCoeff A (root i) (root i) ≤
      rootTrace root weight A := by
    unfold rootTrace
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun j => (weight j : ℂ) * matrixCoeff A (root j) (root j))
      (fun j _ => mul_nonneg (by simpa using hw j) (matrixCoeff_nonneg A hApos _))
      (Finset.mem_univ i)
  calc
    matrixCoeff A x x = matrixCoeff A (root i) (root i) := by
      rw [← hax, hA a ha]
    _ ≤ (c * weight i : ℝ) * matrixCoeff A (root i) (root i) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (show (1:ℂ) ≤ ((c * weight i : ℝ) : ℂ) by exact_mod_cast hmin i)
        (matrixCoeff_nonneg A hApos (root i))
    _ = (c : ℂ) * ((weight i : ℂ) * matrixCoeff A (root i) (root i)) := by
      push_cast; ring
    _ ≤ (c : ℂ) * rootTrace root weight A :=
      mul_le_mul_of_nonneg_left hi (by exact_mod_cast hc)

theorem rootTrace_positive_mul_le {Γ : Set (V ≃ V)}
    (htr : RootTransport root weight Γ) (hw : ∀ i, 0 ≤ weight i)
    (A B : Hilbert V →L[ℂ] Hilbert V)
    (hA : KernelInvariant Γ A) (hB : KernelInvariant Γ B)
    (hApos : 0 ≤ A) (hBsa : IsSelfAdjoint B) :
    rootTrace root weight (B*A) ≤ (‖B‖ : ℂ) * rootTrace root weight A := by
  let S := CFC.sqrt A
  have hS : S*S = A := CFC.sqrt_mul_sqrt_self A hApos
  have hSstar : star S = S := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A)).star_eq
  have hSI : KernelInvariant Γ S := hA.sqrt
  have hbound : S*B*S ≤ ‖B‖ • A := by
    convert (CStarAlgebra.star_left_conjugate_le_norm_smul (a := S) (b := B) hBsa) using 1
    · rw [hSstar]
    · rw [hSstar, hS]
      ext f x
      rfl
  calc
    rootTrace root weight (B*A) = rootTrace root weight (S*(B*S)) := by
      rw [rootTrace_cyclic root weight htr S (B*S) hSI (hB.mul hSI)]
      rw [mul_assoc, hS]
    _ = rootTrace root weight (S*B*S) := by rw [mul_assoc]
    _ ≤ rootTrace root weight (‖B‖ • A) := rootTrace_mono root weight hw hbound
    _ = (‖B‖ : ℂ) * rootTrace root weight A := rootTrace_real_smul root weight _ _

theorem rootTrace_conjugate_le {Γ : Set (V ≃ V)}
    (htr : RootTransport root weight Γ) (hw : ∀ i, 0 ≤ weight i)
    (A B : Hilbert V →L[ℂ] Hilbert V)
    (hA : KernelInvariant Γ A) (hB : KernelInvariant Γ B)
    (hApos : 0 ≤ A) :
    rootTrace root weight (B*A*star B) ≤ ((‖B‖ ^ 2 : ℝ) : ℂ) * rootTrace root weight A := by
  calc
    rootTrace root weight (B*A*star B) = rootTrace root weight (star B*(B*A)) :=
      rootTrace_cyclic root weight htr (B*A) (star B) (hB.mul hA) hB.star
    _ = rootTrace root weight ((star B*B)*A) := by rw [mul_assoc]
    _ ≤ (‖star B*B‖ : ℂ) * rootTrace root weight A :=
      rootTrace_positive_mul_le root weight htr hw A (star B*B) hA (hB.star.mul hB)
        hApos (IsSelfAdjoint.of_nonneg (star_mul_self_nonneg B))
    _ = ((‖B‖ ^ 2 : ℝ) : ℂ) * rootTrace root weight A := by
      have hnorm := CStarRing.norm_star_mul_self (x := B)
      have hn : ‖star B * B‖ = ‖B‖ ^ 2 := by
        convert hnorm using 1; simp only [pow_two]
      rw [hn]

 theorem matrixCoeff_gram (L M : Hilbert V →L[ℂ] Hilbert V) (x y : V) :
    matrixCoeff (L*star M) x y =
      inner ℂ (star L (lp.single 2 x (1:ℂ))) (star M (lp.single 2 y (1:ℂ))) := by
  rw [matrixCoeff_eq_inner]
  change inner ℂ _ (L ((ContinuousLinearMap.adjoint M) _)) = _
  rw [← ContinuousLinearMap.adjoint_inner_left]
  rfl

 theorem matrixCoeff_gram_norm_sq_le
    (L M : Hilbert V →L[ℂ] Hilbert V) (x y : V) :
    ‖matrixCoeff (L*star M) x y‖ ^ 2 ≤
      (matrixCoeff (L*star L) x x).re * (matrixCoeff (M*star M) y y).re := by
  simp only [matrixCoeff_gram]
  have h := inner_mul_inner_self_le (𝕜 := ℂ)
      (star L (lp.single 2 x (1:ℂ))) (star M (lp.single 2 y (1:ℂ)))
  rw [norm_inner_symm (star M (lp.single 2 y (1:ℂ)))] at h
  simpa only [pow_two, RCLike.re_to_complex] using h

 theorem matrixCoeff_positive_product_norm_sq_le
    (A B : Hilbert V →L[ℂ] Hilbert V) (hA : 0 ≤ A) (x y : V) :
    ‖matrixCoeff (B*A) x y‖ ^ 2 ≤
      (matrixCoeff (B*A*star B) x x).re * (matrixCoeff A y y).re := by
  let S := CFC.sqrt A
  have hSS : S*S = A := CFC.sqrt_mul_sqrt_self A hA
  have hSstar : star S = S := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A)).star_eq
  convert matrixCoeff_gram_norm_sq_le (B*S) S x y using 1 <;>
    simp only [star_mul, hSstar, mul_assoc, ← mul_assoc S S, hSS]

 

theorem matrixCoeff_smoothing {Γ : Set (V ≃ V)}
    (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hsum : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c * weight i)
    (A B : Hilbert V →L[ℂ] Hilbert V)
    (hA : KernelInvariant Γ A) (hB : KernelInvariant Γ B)
    (hApos : 0 ≤ A) (hdiag : ∀ y, matrixCoeff A y y = 1) (x y : V) :
    ‖matrixCoeff (B*A) x y‖ ≤ Real.sqrt c * ‖B‖ := by
  have htA : rootTrace root weight A = 1 := by
    simp only [rootTrace, hdiag, mul_one, ← Complex.ofReal_sum, hsum, Complex.ofReal_one]
  have hD : 0 ≤ B*A*star B := star_right_conjugate_nonneg hApos B
  have hi : KernelInvariant Γ (B*A*star B) := (hB.mul hA).mul hB.star
  have ht := rootTrace_conjugate_le root weight htr hw A B hA hB hApos
  rw [htA, mul_one] at ht
  have hd : matrixCoeff (B*A*star B) x x ≤ ((c * ‖B‖^2 : ℝ) : ℂ) := by
    calc
      _ ≤ (c : ℂ) * rootTrace root weight (B*A*star B) :=
        rootTrace_diag_le root weight hcov hw c hc hmin _ hi hD x
      _ ≤ (c : ℂ) * ((‖B‖^2 : ℝ) : ℂ) :=
        mul_le_mul_of_nonneg_left ht (by exact_mod_cast hc)
      _ = _ := by push_cast; rfl
  have hd' : (matrixCoeff (B*A*star B) x x).re ≤ c * ‖B‖^2 :=
    (Complex.le_def.mp hd).1
  have hs : ‖matrixCoeff (B*A) x y‖ ^ 2 ≤ c * ‖B‖ ^ 2 := by
    have hh := matrixCoeff_positive_product_norm_sq_le A B hApos x y
    rw [hdiag, Complex.one_re, mul_one] at hh
    exact hh.trans hd'
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rwa [mul_pow, Real.sq_sqrt hc]

end RootTrace

end InvariantOperatorTrace

section InvariantPercolationOperators
open scoped ComplexOrder InnerProduct
attribute [local instance] Classical.propDecidable


theorem HasKernel.invariant [Countable V] [Countable E] (G : BondGraph V E) (p : unitInterval)
    (A : Hilbert V →L[ℂ] Hilbert V) (hA : HasKernel G p A) :
    KernelInvariant (vertexAut G) A := by
  rintro a ⟨b, hab⟩ x y
  change A (lp.single 2 (a y) (1:ℂ)) (a x) = A (lp.single 2 y (1:ℂ)) x
  rw [hA, hA, twoPoint_aut G p hab]

theorem KernelInvariant.one (Γ : Set (V ≃ V)) :
    KernelInvariant Γ (1 : Hilbert V →L[ℂ] Hilbert V) := by
  intro a _ x y
  simp only [matrixCoeff, one_apply_eq_self, lp.coeFn_single]
  simp [Pi.single_apply, a.injective.eq_iff]

theorem KernelInvariant.pow {Γ : Set (V ≃ V)}
    {A : Hilbert V →L[ℂ] Hilbert V} (hA : KernelInvariant Γ A) (n : ℕ) :
    KernelInvariant Γ (A^n) := by
  induction n with
  | zero => simpa only [pow_zero] using KernelInvariant.one Γ
  | succ n ih => simpa only [pow_succ] using ih.mul hA

 

theorem twoPoint_operator_smoothing [Countable V] [Countable E] [Nonempty V] {ι : Type*} [Fintype ι]
    (G : BondGraph V E) (p : unitInterval) (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G))
    (hcov : ∀ x, ∃ i, ∃ a ∈ vertexAut G, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hsum : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c * weight i)
    (A P : Hilbert V →L[ℂ] Hilbert V) (hA : HasKernel G p A)
    (hP : KernelInvariant (vertexAut G) P) (l : ℕ) (x y : V) :
    ‖matrixCoeff (P^l*A) x y‖ ≤ Real.sqrt c * ‖P‖^l := by
  have hdiag (y : V) : matrixCoeff A y y = 1 := by
    change A (lp.single 2 y (1:ℂ)) y = 1
    rw [hA y y, twoPoint_self, Complex.ofReal_one]
  have h := matrixCoeff_smoothing root weight htr hcov hw hsum c hc hmin A (P^l)
    (hA.invariant G p A) (hP.pow l) ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr
      (hA.isPositive G p A)) hdiag x y
  have hn (n : ℕ) : ‖P^n‖ ≤ ‖P‖^n := by
    induction n with
    | zero => simpa only [pow_zero, ContinuousLinearMap.one_def] using (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := Hilbert V))
    | succ n ih =>
      rw [pow_succ, pow_succ]
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (norm_nonneg P))
  exact h.trans (mul_le_mul_of_nonneg_left (hn l) (Real.sqrt_nonneg c))
end InvariantPercolationOperators

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Transport_TrajectoryMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trajectory Mass for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section TrajectoryTransport
attribute [local instance] Classical.propDecidable Classical.decEq
variable {ι : Type*} [Fintype ι]

 

theorem RootTransport.real (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ) (m : V → V → ℝ)
    (hi : ∀ a ∈ Γ, ∀ x y, m (a x) (a y) = m x y)
    (hr : ∀ x, Summable (m x)) (hc : ∀ y, Summable (fun x => m x y)) :
    (∑ i, weight i * ∑' y, m (root i) y) =
      (∑ i, weight i * ∑' x, m x (root i)) := by
  have ht := htr (fun x y => (m x y:ℂ))
    (fun a ha x y => congrArg Complex.ofReal (hi a ha x y))
    (fun x => Complex.summable_ofReal.mpr (hr x))
    (fun y => Complex.summable_ofReal.mpr (hc y))
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_tsum] using ht



end TrajectoryTransport

end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_Amplification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Amplification for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section PositivePathOperator
attribute [local instance] Classical.propDecidable Classical.decEq


namespace PositiveRealMatrix
variable {A H : Hilbert V →L[ℂ] Hilbert V}

theorem mul_hasSum (hA : PositiveRealMatrix A) (H : Hilbert V →L[ℂ] Hilbert V) (x y : V) :
    HasSum (fun z => (matrixCoeff A x z).re * (matrixCoeff H z y).re)
      (matrixCoeff (A*H) x y).re := by
  have h := Complex.reCLM.hasSum (operator_kernel_hasSum A (H (lp.single 2 y (1:ℂ))) x)
  change HasSum (fun z => (matrixCoeff A x z * matrixCoeff H z y).re)
    (matrixCoeff (A*H) x y).re at h
  simpa only [Complex.mul_re,(hA _ _).1,zero_mul,sub_zero] using h

theorem mul (hA : PositiveRealMatrix A) (hH : PositiveRealMatrix H) :
    PositiveRealMatrix (A*H) := by
  intro x y
  constructor
  · have hs := (operator_kernel_hasSum A (H (lp.single 2 y (1:ℂ))) x).summable
    change Summable (fun z => matrixCoeff A x z * matrixCoeff H z y) at hs
    rw [matrixCoeff_mul,Complex.im_tsum hs]
    simp only [Complex.mul_im,(hA _ _).1,(hH _ _).1,mul_zero,zero_mul,add_zero,tsum_zero]
  · rw [← (hA.mul_hasSum H x y).tsum_eq]
    exact tsum_nonneg fun z => mul_nonneg (hA x z).2 (hH z y).2

theorem one : PositiveRealMatrix (1 : Hilbert V →L[ℂ] Hilbert V) := by
  intro x y
  simp only [matrixCoeff,one_apply_eq_self,lp.single_apply,Pi.single_apply]
  split_ifs <;> norm_num

theorem pow (hA : PositiveRealMatrix A) (k : ℕ) : PositiveRealMatrix (A^k) := by
  induction k with
  | zero => simpa only [pow_zero] using (one (V := V))
  | succ k ih => rw [pow_succ]; exact ih.mul hA

end PositiveRealMatrix



end PositivePathOperator

end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_Connections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Connections for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section WalkPowerSupport
attribute [local instance] Classical.propDecidable Classical.decEq

theorem walkKernel_zero_of_not_step (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (x y : V) (hxy : x ≠ y) (hadj : ¬ Adj G x y) :
    walkKernel G hloc a x y = 0 := by simp only [walkKernel,ite_eq_right hxy,ite_eq_right hadj,zero_add]

theorem walkKernel_hasSum (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ) (x : V) :
    HasSum (walkKernel G hloc a x) 1 := by
  rw [← walkKernel_row_sum G hloc a x]
  apply hasSum_sum_of_ne_finset_zero
  intro y hy
  simp only [Finset.mem_insert,mem_neighbors,not_or] at hy
  exact walkKernel_zero_of_not_step G hloc a x y (Ne.symm hy.1) hy.2

theorem walkPower_support (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (k : ℕ) (x y : V) (hy : y ∉ reachBall G x k) : (matrixCoeff (P^k) x y).re = 0 := by
  induction k generalizing y with
  | zero =>
    have he : y ≠ x := by simpa only [reachBall,Set.mem_singleton_iff] using hy
    simp only [pow_zero,matrixCoeff,one_apply_eq_self,lp.single_apply,Pi.single_apply,ite_eq_right (Ne.symm he),Complex.zero_re]
  | succ k ih =>
    rw [pow_succ,← ((hpos.pow k).mul_hasSum P x y).tsum_eq]
    rw [← tsum_zero]
    apply tsum_congr
    intro z
    by_cases hz : z ∈ reachBall G x k
    · have hzy : z ≠ y := by intro he; subst y; exact hy (Or.inl hz)
      have hadj : ¬ Adj G z y := by
        intro h
        apply hy
        apply Or.inr
        simp only [Set.mem_iUnion,Set.mem_ofPred_eq]
        exact ⟨z,hz,h⟩
      rw [hP,walkKernel_zero_of_not_step G hloc a z y hzy hadj,Complex.ofReal_zero,Complex.zero_re,mul_zero]
    · rw [ih z hz,zero_mul]

theorem walkPower_hasSum (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (k : ℕ) (x : V) : HasSum (fun y => (matrixCoeff (P^k) x y).re) 1 := by
  induction k with
  | zero =>
    have h : HasSum (fun y : V => if x=y then (1:ℝ) else 0) 1 := by
      exact hasSum_ite_eq' x (1:ℝ)
    simpa only [pow_zero,matrixCoeff,one_apply_eq_self,lp.single_apply,Pi.single_apply,apply_ite,Complex.one_re,Complex.zero_re] using h
  | succ k ih =>
    let B := (finite_reachBall hloc x k).toFinset
    have he (y : V) : (matrixCoeff (P^(k+1)) x y).re =
        ∑ z ∈ B, (matrixCoeff (P^k) x z).re * walkKernel G hloc a z y := by
      rw [pow_succ,← ((hpos.pow k).mul_hasSum P x y).tsum_eq]
      simp only [hP,Complex.ofReal_re]
      apply tsum_eq_sum
      intro z hz
      rw [walkPower_support G hloc a P hpos hP k x z (by simpa only [B,Set.Finite.mem_toFinset] using hz),zero_mul]
    have hs := hasSum_sum (s := B) (fun z _ => (walkKernel_hasSum G hloc a z).mul_left (matrixCoeff (P^k) x z).re)
    simp only [mul_one] at hs
    have hr : (∑ z ∈ B, (matrixCoeff (P^k) x z).re) = 1 := by
      rw [← ih.tsum_eq]
      exact (tsum_eq_sum fun z hz => walkPower_support G hloc a P hpos hP k x z
        (by simpa only [B,Set.Finite.mem_toFinset] using hz)).symm
    simpa only [← he,hr] using hs

end WalkPowerSupport

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section WalkCovariance
attribute [local instance] Classical.propDecidable Classical.decEq

theorem neighbors_aut_card (G : BondGraph V E) (hloc : LocallyFinite G)
    {g : V ≃ V} {b : E ≃ E} (hg : IsAut G g b) (x : V) :
    (neighbors G hloc (g x)).card = (neighbors G hloc x).card := by
  have he : neighbors G hloc (g x) = (neighbors G hloc x).map g.toEmbedding := by
    ext y
    simp only [mem_neighbors,Finset.mem_map,Equiv.coe_toEmbedding]
    constructor
    · intro h
      refine ⟨g.symm y,?_,by simp⟩
      simpa only [g.symm_apply_apply] using adj_aut G (isAut_symm G hg) h
    · rintro ⟨z,hz,rfl⟩
      exact adj_aut G hg hz
  rw [he,Finset.card_map]

theorem walkKernel_covariant (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    {g : V ≃ V} {b : E ≃ E} (hg : IsAut G g b) (x y : V) :
    walkKernel G hloc a (g x) (g y) = walkKernel G hloc a x y := by
  have hadj : Adj G (g x) (g y) ↔ Adj G x y :=
    ⟨fun h => by simpa using adj_aut G (isAut_symm G hg) h,adj_aut G hg⟩
  simp only [walkKernel,g.apply_eq_iff_eq,neighbors_aut_card G hloc hg,hadj]

end WalkCovariance
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section OrbitReturn
attribute [local instance] Classical.propDecidable Classical.decEq

lemma finiteKernel_summable_mul (K : V → V → ℝ)
    (hf : ∀ x, (Function.support (K x)).Finite) (x : V) (f : V → ℝ) :
    Summable (fun y => K x y * f y) := by
  apply summable_of_ne_finset_zero (s := (hf x).toFinset)
  intro y hy
  have hd : K x y = 0 := by simpa only [Set.Finite.mem_toFinset,Function.mem_support,not_not] using hy
  rw [hd,zero_mul]

 

theorem orbit_two_step_return_lower (G : BondGraph V E)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (K : V → V → ℝ)
    (hfin : ∀ x, (Function.support (K x)).Finite)
    (hrow : ∀ x, HasSum (K x) 1) (hsym : ∀ x y, K x y = K y x)
    (hcov : ∀ a b, IsAut G a b → ∀ x y, K (a x) (a y) = K x y) :
    (∑ i, if root i ∈ vertexOrbit G (root i₀) then weight i else 0) ≤
      ∑' z, K (root i₀) z * ∑' y, if y ∈ vertexOrbit G (root i₀) then K z y else 0 := by
  let O := vertexOrbit G (root i₀)
  let I : V → ℝ := fun x => if x ∈ O then 1 else 0
  let f : V → ℝ := fun x => ∑' y, K x y * I y
  let g : V → ℝ := fun x => ∑' y, K x y * f y
  let σ := ∑ i, weight i * I (root i)
  have hI (a : V ≃ V) (b : E ≃ E) (hab : IsAut G a b) (x : V) : I (a x) = I x := by
    simp only [I,O,mem_vertexOrbit_aut_iff G (root i₀) hab]
  have hf (a : V ≃ V) (b : E ≃ E) (hab : IsAut G a b) (x : V) : f (a x) = f x := by
    dsimp only [f]
    rw [←a.tsum_eq (fun y => K (a x) y*I y)]
    simp only [hcov a b hab,hI a b hab]
  have hg (a : V ≃ V) (b : E ≃ E) (hab : IsAut G a b) (x : V) : g (a x) = g x := by
    dsimp only [g]
    rw [←a.tsum_eq (fun y => K (a x) y*f y)]
    simp only [hcov a b hab,hf a b hab]
  have hgO (x : V) (hx : x ∈ O) : g x = g (root i₀) := by
    obtain ⟨a,b,hab,rfl⟩ := hx
    exact hg a b hab _
  have hmean : ∑ i, weight i*f (root i) = σ := by
    have ht := htr.real root weight Γ (fun x y => K x y*I y)
      (fun a ha x y => by obtain ⟨b,hab⟩ := hΓ ha; rw [hcov a b hab,hI a b hab])
      (fun x => finiteKernel_summable_mul K hfin x I)
      (fun y => by simpa only [hsym, mul_comm] using (hrow y).summable.mul_left (I y))
    calc
      _ = ∑ i, weight i * ∑' x, K x (root i)*I (root i) := ht
      _ = σ := by simp only [tsum_mul_right,show ∀ y, ∑' x, K x y = 1 from fun y => by simpa only [hsym] using (hrow y).tsum_eq,one_mul,σ]
  have hsecond : σ*g (root i₀) = ∑ i, weight i*f (root i)^2 := by
    have ht := htr.real root weight Γ (fun x y => I x*K x y*f y)
      (fun a ha x y => by obtain ⟨b,hab⟩ := hΓ ha; rw [hcov a b hab,hI a b hab,hf a b hab])
      (fun x => by simpa only [mul_assoc] using (finiteKernel_summable_mul K hfin x f).mul_left (I x))
      (fun y => by simpa only [hsym,mul_comm,mul_left_comm,mul_assoc] using (finiteKernel_summable_mul K hfin y I).mul_right (f y))
    have hr (i : ι) : I (root i)*g (root i) = I (root i)*g (root i₀) := by
      by_cases hi : root i ∈ O
      · rw [hgO _ hi]
      · simp only [I,ite_eq_right hi,zero_mul]
    calc
      _ = ∑ i, weight i*(I (root i)*g (root i)) := by
        simp only [hr,σ,Finset.sum_mul,mul_assoc]
      _ = ∑ i, weight i*∑' x, I x*K x (root i)*f (root i) := by
        simpa only [mul_assoc,tsum_mul_left,g] using ht
      _ = ∑ i, weight i*f (root i)^2 := by
        simp only [tsum_mul_right]
        congr 1
        ext i
        congr 1
        rw [show (∑' x, I x*K x (root i)) = f (root i) by simp only [f,hsym,mul_comm]]
        ring
  have hvariance : 0 ≤ ∑ i, weight i*(f (root i)-σ)^2 :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (sq_nonneg _))
  have he : (∑ i, weight i*(f (root i)-σ)^2) = (∑ i, weight i*f (root i)^2)-σ^2 := by
    simp_rw [sub_sq,mul_add,mul_sub]
    rw [Finset.sum_add_distrib,Finset.sum_sub_distrib]
    have hc : (∑ i, weight i*(2*f (root i)*σ)) = 2*σ*(∑ i, weight i*f (root i)) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi; ring
    rw [hc,hmean,←Finset.sum_mul,hw1,one_mul]
    ring
  rw [he,←hsecond] at hvariance
  have hσ : 0 < σ := by
    have hx : root i₀ ∈ O := ⟨Equiv.refl _,Equiv.refl _,fun _ => by simp,rfl⟩
    have hIn (x : V) : 0 ≤ I x := by dsimp [I]; split_ifs <;> norm_num
    have hb := Finset.single_le_sum (fun i _ => mul_nonneg (hw i) (hIn (root i))) (Finset.mem_univ i₀)
    have he₀ : weight i₀*I (root i₀) = weight i₀ := by simp only [I,ite_eq_left hx,mul_one]
    rw [he₀] at hb
    exact hw₀.trans_le hb
  have hbound : σ ≤ g (root i₀) := by nlinarith only [hvariance,hσ]
  simpa only [σ,g,f,I,mul_ite,mul_one,mul_zero,zero_mul] using hbound

end OrbitReturn
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section WalkOrbitReturn
attribute [local instance] Classical.propDecidable Classical.decEq

theorem matrixCoeff_real_symm (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : IsSelfAdjoint A) (x y : V) : (matrixCoeff A x y).re = (matrixCoeff A y x).re := by
  have h := congrArg Complex.re (matrixCoeff_adjoint A x y)
  simpa only [hA.star_eq,Complex.star_def,Complex.conj_re] using h

theorem finite_positive_square_row (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : PositiveRealMatrix A) (hfin : ∀ x, (Function.support (fun y => (matrixCoeff A x y).re)).Finite)
    (f : V → ℝ) (x : V) :
    (∑' y, (matrixCoeff (A*A) x y).re*f y) =
      ∑' z, (matrixCoeff A x z).re*∑' y, (matrixCoeff A z y).re*f y := by
  let K := fun x y => (matrixCoeff A x y).re
  let B := (hfin x).toFinset
  have hz (z : V) (hz : z ∉ B) : K x z = 0 := by
    simpa only [B,Set.Finite.mem_toFinset,Function.mem_support,not_not] using hz
  have he (y : V) : (matrixCoeff (A*A) x y).re*f y = ∑ z ∈ B, K x z*(K z y*f y) := by
    rw [←(hA.mul_hasSum A x y).tsum_eq,tsum_eq_sum (s := B) (fun z h => by change K x z*K z y = 0; rw [hz z h,zero_mul]),Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro z h
    exact mul_assoc _ _ _
  have hs := hasSum_sum (s := B) (fun z _ =>
    (finiteKernel_summable_mul K hfin z f).hasSum.mul_left (K x z))
  have hr : (∑' z, K x z*∑' y, K z y*f y) = ∑ z ∈ B, K x z*∑' y, K z y*f y :=
    tsum_eq_sum (fun z h => by rw [hz z h,zero_mul])
  simpa only [←he,←hr] using hs.tsum_eq

theorem walkPower_finite_support (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ)) (k : ℕ) (x : V) :
    (Function.support (fun y => (matrixCoeff (P^k) x y).re)).Finite := by
  apply (finite_reachBall hloc x k).subset
  intro y hy
  by_contra hn
  exact hy (walkPower_support G hloc a P hpos hP k x y hn)

theorem walkPower_invariant (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ)) (k : ℕ) :
    KernelInvariant (vertexAut G) (P^k) := by
  apply KernelInvariant.pow
  intro g hg x y
  obtain ⟨b,hb⟩ := hg
  simp only [hP,walkKernel_covariant G hloc a hb]

 

theorem walkPower_even_orbit_return (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ)) (k : ℕ) :
    (∑ i, if root i ∈ vertexOrbit G (root i₀) then weight i else 0) ≤
      ∑' y, if y ∈ vertexOrbit G (root i₀) then (matrixCoeff (P^(2*k)) (root i₀) y).re else 0 := by
  have h := orbit_two_step_return_lower G root weight Γ hΓ htr hw hw1 i₀ hw₀
    (fun x y => (matrixCoeff (P^k) x y).re)
    (walkPower_finite_support G hloc a P hpos hP k)
    (walkPower_hasSum G hloc a P hpos hP k)
    (matrixCoeff_real_symm (P^k) (hsym.pow k))
    (fun g b hb x y => congrArg Complex.re (walkPower_invariant G hloc a P hP k g ⟨b,hb⟩ x y))
  have he := finite_positive_square_row (P^k) (hpos.pow k)
    (walkPower_finite_support G hloc a P hpos hP k)
    (fun y => if y ∈ vertexOrbit G (root i₀) then 1 else 0) (root i₀)
  simp only [mul_ite,mul_one,mul_zero] at he
  rw [←he] at h
  simpa only [←pow_add,←two_mul] using h

end WalkOrbitReturn
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteOrbitPartition
attribute [local instance] Classical.propDecidable Classical.decEq



theorem vertexOrbit_eq_of_mem (G : BondGraph V E) (o x : V) (hx : x ∈ vertexOrbit G o) :
    vertexOrbit G x = vertexOrbit G o := by
  obtain ⟨a,b,hab,rfl⟩ := hx
  ext y
  constructor
  · rintro ⟨c,d,hcd,hc⟩
    exact ⟨a.trans c,b.trans d,isAut_trans G hab hcd,hc⟩
  · rintro ⟨c,d,hcd,hc⟩
    exact ⟨a.symm.trans c,b.symm.trans d,isAut_trans G (isAut_symm G hab) hcd,by simpa using hc⟩



end FiniteOrbitPartition
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_DistinctMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Distinct Moments for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FinitePositiveOperatorPowers
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem finite_positive_product_support (A B : Hilbert V →L[ℂ] Hilbert V)
    (hA : PositiveRealMatrix A)
    (ha : ∀ x, (Function.support (fun y => (matrixCoeff A x y).re)).Finite)
    (hb : ∀ x, (Function.support (fun y => (matrixCoeff B x y).re)).Finite) (x : V) :
    (Function.support (fun y => (matrixCoeff (A*B) x y).re)).Finite := by
  let S := (ha x).toFinset
  let T := S.biUnion (fun z => (hb z).toFinset)
  apply T.finite_toSet.subset
  intro y hy
  by_contra hn
  apply hy
  change (matrixCoeff (A*B) x y).re = 0
  rw [←(hA.mul_hasSum B x y).tsum_eq]
  rw [←tsum_zero]
  apply tsum_congr
  intro z
  by_cases hz : z ∈ S
  · have hzy : (matrixCoeff B z y).re = 0 := by
      by_contra hh
      apply hn
      exact Finset.mem_biUnion.mpr ⟨z,hz,by simpa only [Set.Finite.mem_toFinset,Function.mem_support] using hh⟩
    rw [hzy,mul_zero]
  · have hzx : (matrixCoeff A x z).re = 0 := by
      simpa only [S,Set.Finite.mem_toFinset,Function.mem_support,not_not] using hz
    rw [hzx,zero_mul]

theorem finite_positive_product_action (A B : Hilbert V →L[ℂ] Hilbert V)
    (hA : PositiveRealMatrix A)
    (ha : ∀ x, (Function.support (fun y => (matrixCoeff A x y).re)).Finite)
    (hb : ∀ x, (Function.support (fun y => (matrixCoeff B x y).re)).Finite)
    (f : V → ℝ) (x : V) :
    (∑' y, (matrixCoeff (A*B) x y).re*f y) =
      ∑' z, (matrixCoeff A x z).re*∑' y, (matrixCoeff B z y).re*f y := by
  let K := fun x y => (matrixCoeff A x y).re
  let J := fun x y => (matrixCoeff B x y).re
  let S := (ha x).toFinset
  have hz (z : V) (hz : z ∉ S) : K x z = 0 := by
    simpa only [S,Set.Finite.mem_toFinset,Function.mem_support,not_not] using hz
  have he (y : V) : (matrixCoeff (A*B) x y).re*f y = ∑ z ∈ S, K x z*(J z y*f y) := by
    rw [←(hA.mul_hasSum B x y).tsum_eq,tsum_eq_sum (s := S)
      (fun z h => by change K x z*J z y = 0; rw [hz z h,zero_mul]),Finset.sum_mul]
    exact Finset.sum_congr rfl (fun z _ => mul_assoc _ _ _)
  have hs := hasSum_sum (s := S) (fun z _ =>
    (finiteKernel_summable_mul J hb z f).hasSum.mul_left (K x z))
  have hr : (∑' z, K x z*∑' y, J z y*f y) = ∑ z ∈ S, K x z*∑' y, J z y*f y :=
    tsum_eq_sum (fun z h => by rw [hz z h,zero_mul])
  simpa only [←he,←hr] using hs.tsum_eq

theorem finite_positive_pow_support (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : PositiveRealMatrix A)
    (ha : ∀ x, (Function.support (fun y => (matrixCoeff A x y).re)).Finite)
    (j : ℕ) (x : V) : (Function.support (fun y => (matrixCoeff (A^j) x y).re)).Finite := by
  induction j generalizing x with
  | zero =>
      apply (Set.finite_singleton x).subset
      intro y hy
      by_contra hn
      apply hy
      have he : x ≠ y := fun h => hn (by simp only [Set.mem_singleton_iff]; exact h.symm)
      simp only [pow_zero,matrixCoeff,one_apply_eq_self,lp.single_apply,Pi.single_apply,ite_eq_right he,Complex.zero_re]
  | succ j ih =>
      rw [pow_succ']
      exact finite_positive_product_support A (A^j) hA ha ih x

theorem positive_identity_action (f : V → ℝ) (x : V) :
    (∑' y, (matrixCoeff (1 : Hilbert V →L[ℂ] Hilbert V) x y).re*f y) = f x := by
  rw [tsum_eq_single x (fun y hy => by
    simp only [matrixCoeff,one_apply_eq_self,lp.single_apply,Pi.single_apply,ite_eq_right (Ne.symm hy),Complex.zero_re,zero_mul])]
  simp only [matrixCoeff,one_apply_eq_self,lp.single_apply,Pi.single_apply,ite_true,Complex.one_re,one_mul]

end FinitePositiveOperatorPowers
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_TraceBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trace Bounds for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u
section ChronologicalErasure
open List
variable {V : Type u}
attribute [local instance] Classical.propDecidable Classical.decEq



namespace HoldingWalk
variable {H : SimpleGraph V} {k : ℕ} {x y : V}

theorem mass_nonneg (P : V → V → ℝ) (hP : ∀ a b, 0 ≤ P a b) (w : HoldingWalk H k x y) :
    0 ≤ w.mass P := by
  induction w with
  | nil => exact zero_le_one
  | hold w ih => exact mul_nonneg (hP _ _) ih
  | step h w ih => exact mul_nonneg (hP _ _) ih

end HoldingWalk
end ChronologicalErasure
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Deformation_Corridors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Corridors for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section RawPathIntegration
attribute [local instance] Classical.propDecidable Classical.decEq

namespace RawFrom
variable {H : SimpleGraph V}

theorem integral_zero (P : V → V → ℝ) (x : V) (f : V → ℝ) :
    integral (H := H) P 0 x f = f x := by
  unfold integral
  rw [←(zeroEquiv x).symm.tsum_eq]
  simp only [zeroEquiv,Equiv.symm_mk,Equiv.coe_fn_mk,HoldingWalk.mass,one_mul,tsum_fintype,Fintype.sum_unique]

theorem integral_succ [∀ x, Finite (H.neighborSet x)] (P : V → V → ℝ)
    (k : ℕ) (x : V) (f : V → ℝ) :
    integral (H := H) P (k+1) x f =
      P x x * integral (H := H) P k x f +
        ∑' z : H.neighborSet x, P x z * integral (H := H) P k z f := by
  unfold integral
  rw [←(succEquiv k x).symm.tsum_eq]
  let := Fintype.ofFinite (RawFrom H k x)
  let := Fintype.ofFinite (H.neighborSet x)
  let (z : H.neighborSet x) := Fintype.ofFinite (RawFrom H k z)
  simp only [tsum_fintype,Fintype.sum_sum_type,Fintype.sum_sigma,succEquiv,
    Equiv.symm_mk,Equiv.coe_fn_mk,HoldingWalk.mass,mul_assoc,Finset.mul_sum]

end RawFrom

theorem finite_openSimpleGraph_neighbors (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) :
    Finite ((openSimpleGraph G Set.univ).neighborSet x) := by
  apply Set.Finite.to_subtype
  apply (finite_neighbors hloc x).subset
  intro y hy
  obtain ⟨_,e,_,he⟩ := hy
  exact ⟨e,he⟩

end RawPathIntegration
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section RawPathOperator
attribute [local instance] Classical.propDecidable Classical.decEq

 theorem sum_step_decomposition (H : SimpleGraph V) (P : V → V → ℝ)
    (hs : ∀ x, (Function.support (P x)).Finite)
    (hstep : ∀ x y, x ≠ y → ¬H.Adj x y → P x y = 0) (x : V) (f : V → ℝ) :
    (∑' y, P x y * f y) = P x x * f x + ∑' y : H.neighborSet x, P x y * f y := by
  rw [(finiteKernel_summable_mul P hs x f).tsum_eq_add_tsum_ite x]
  congr 1
  have he : (∑' y : H.neighborSet x, if (y:V) = x then (0:ℝ) else P x y * f y) =
      ∑' y, if y = x then (0:ℝ) else P x y * f y := by
    apply tsum_subtype_eq_of_support_subset (f := fun y : V => if y = x then (0:ℝ) else P x y * f y)
    intro y hy
    by_contra hn
    apply hy
    by_cases h : y = x
    · simp only [h,ite_true]
    · simp only [ite_eq_right h,hstep x y (Ne.symm h) hn,zero_mul]
  rw [←he]
  apply tsum_congr
  intro y
  have hn : (y:V) ≠ x := by
    intro h
    have hy : H.Adj x y := y.property
    rw [h] at hy
    exact H.loopless.irrefl x hy
  rw [ite_eq_right hn]

 theorem raw_integral_operator (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (k : ℕ) (x : V) (f : V → ℝ) :
    RawFrom.integral (H := openSimpleGraph G Set.univ) (walkKernel G hloc a) k x f =
      ∑' y, (matrixCoeff (P^k) x y).re * f y := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) :=
    finite_openSimpleGraph_neighbors G hloc z
  have hs (x : V) : (Function.support (walkKernel G hloc a x)).Finite := by
    simpa only [pow_one,hP,Complex.ofReal_re] using walkPower_finite_support G hloc a P hpos hP 1 x
  have hsP (x : V) : (Function.support (fun y => (matrixCoeff P x y).re)).Finite := by
    simpa only [hP,Complex.ofReal_re] using hs x
  induction k generalizing x with
  | zero => rw [RawFrom.integral_zero,pow_zero,positive_identity_action]
  | succ k ih =>
    rw [RawFrom.integral_succ,pow_succ',finite_positive_product_action P (P^k) hpos hsP
      (finite_positive_pow_support P hpos hsP k)]
    simp only [hP,Complex.ofReal_re]
    rw [sum_step_decomposition (openSimpleGraph G Set.univ) (walkKernel G hloc a) hs]
    · simp only [ih]
    · intro u v huv hn
      apply walkKernel_zero_of_not_step G hloc a u v huv
      intro ha
      apply hn
      obtain ⟨e,he⟩ := ha
      exact ⟨huv,e,Set.mem_univ e,he⟩

end RawPathOperator
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Deformation_Derivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Derivatives for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section RawWalkTotalMass
attribute [local instance] Classical.propDecidable Classical.decEq

theorem walkKernel_finite_support (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (x : V) : (Function.support (walkKernel G hloc a x)).Finite := by
  apply (Finset.finite_toSet (insert x (neighbors G hloc x))).subset
  intro y hy
  by_contra hn
  have hn' : y ≠ x ∧ ¬Adj G x y := by simpa only [Finset.mem_coe,Finset.mem_insert,mem_neighbors,not_or] using hn
  exact hy (by simp only [walkKernel,ite_eq_right hn'.1.symm,ite_eq_right hn'.2,add_zero])

theorem walkKernel_tsum (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ) (x : V) :
    (∑' y, walkKernel G hloc a x y) = 1 := by
  rw [tsum_eq_sum (s := insert x (neighbors G hloc x))]
  · exact walkKernel_row_sum G hloc a x
  · intro y hy
    have hn : y ≠ x ∧ ¬Adj G x y := by simpa only [Finset.mem_insert,mem_neighbors,not_or] using hy
    simp only [walkKernel,ite_eq_right hn.1.symm,ite_eq_right hn.2,add_zero]

theorem raw_integral_one (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (k : ℕ) (x : V) :
    RawFrom.integral (H := openSimpleGraph G Set.univ) (walkKernel G hloc a) k x (fun _ => 1) = 1 := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  induction k generalizing x with
  | zero => exact RawFrom.integral_zero _ _ _
  | succ k ih =>
    rw [RawFrom.integral_succ]
    simp only [ih,mul_one]
    have he := sum_step_decomposition (openSimpleGraph G Set.univ) (walkKernel G hloc a)
      (walkKernel_finite_support G hloc a) (fun x y hxy hn => by
        apply walkKernel_zero_of_not_step G hloc a x y hxy
        intro h
        obtain ⟨e,he⟩ := h
        exact hn ⟨hxy,e,Set.mem_univ e,he⟩) x (fun _ => 1)
    simpa only [mul_one,walkKernel_tsum G hloc a] using he.symm

 
theorem rawFrom_probability_sum (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (k : ℕ) (x : V) :
    (∑' w : RawFrom (openSimpleGraph G Set.univ) k x, w.2.mass (walkKernel G hloc a)) = 1 := by
  simpa only [RawFrom.integral,mul_one] using raw_integral_one G hloc a k x

end RawWalkTotalMass
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Deformation_Calibration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Calibration for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u u' v
section ErasureNaturality
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type u} {V' : Type u'} {H : SimpleGraph V} {H' : SimpleGraph V'}

namespace HoldingWalk

theorem map_vertices (f : H →g H') {k : ℕ} {x y : V} (w : HoldingWalk H k x y) :
    (w.map f).vertices = w.vertices.map f := by
  induction w with
  | nil => rfl
  | hold w ih => simp only [map,vertices,List.map_cons,ih]
  | step h w ih => simp only [map,vertices,List.map_cons,ih]

end HoldingWalk
end ErasureNaturality
end Percolation

 
namespace Percolation
universe u u' u'' v
section RawWalkMaps
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type u} {V' : Type u'} {V'' : Type u''}
  {H : SimpleGraph V} {H' : SimpleGraph V'} {H'' : SimpleGraph V''}
namespace HoldingWalk

theorem mass_map (f : H →g H') (P : V → V → ℝ) (Q : V' → V' → ℝ)
    (hPQ : ∀ x y, Q (f x) (f y) = P x y)
    {k : ℕ} {x y : V} (w : HoldingWalk H k x y) : (w.map f).mass Q = w.mass P := by
  induction w with
  | nil => rfl
  | hold w ih => simp only [map,mass,hPQ,ih]
  | step h w ih => simp only [map,mass,hPQ,ih]
end HoldingWalk

end RawWalkMaps
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Deformation_AveragedDecrease
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Averaged Decrease for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AnchoredSegments
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I : Type*} [Fintype I]


theorem segmentAnchors_nonempty_iff (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i : I) (x : V) :
    (segmentAnchors G hloc γ n hdiam i x).Nonempty ↔ x ∈ vertexOrbit G (γ i) := by
  constructor
  · rintro ⟨s,hs⟩
    obtain ⟨⟨a,b,h,rfl⟩,hx⟩ := (mem_segmentAnchors G hloc γ n hdiam i x s).mp hs
    exact ⟨a,b,h,hx⟩
  · rintro ⟨a,b,h,hx⟩
    exact ⟨a ∘ γ,(mem_segmentAnchors G hloc γ n hdiam i x _).mpr ⟨⟨a,b,h,rfl⟩,hx⟩⟩

end AnchoredSegments
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AnchoredPositionKernels
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I : Type*} [Fintype I]

theorem segmentAnchors_map (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i : I) (x : V)
    {a : V ≃ V} {b : E ≃ E} (h : IsAut G a b) :
    segmentAnchors G hloc γ n hdiam i (a x) =
      (segmentAnchors G hloc γ n hdiam i x).map (segmentAut a).toEmbedding := by
  ext s
  rw [Finset.mem_map,mem_segmentAnchors]
  constructor
  · rintro ⟨hs,hx⟩
    refine ⟨a.symm ∘ s,(mem_segmentAnchors G hloc γ n hdiam i x _).mpr ⟨?_,?_⟩,?_⟩
    · exact (segmentOrbit_aut_iff G γ s (isAut_symm G h)).mpr hs
    · simp only [Function.comp_apply,hx,Equiv.symm_apply_apply]
    · funext j; exact a.apply_symm_apply (s j)
  · rintro ⟨t,ht,rfl⟩
    obtain ⟨ht,hx⟩ := (mem_segmentAnchors G hloc γ n hdiam i x t).mp ht
    exact ⟨(segmentOrbit_aut_iff G γ t h).mpr ht,congrArg a hx⟩

theorem segmentAnchors_card_aut (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i : I) (x : V)
    {a : V ≃ V} {b : E ≃ E} (h : IsAut G a b) :
    (segmentAnchors G hloc γ n hdiam i (a x)).card = (segmentAnchors G hloc γ n hdiam i x).card := by
  rw [segmentAnchors_map G hloc γ n hdiam i x h,Finset.card_map]



end AnchoredPositionKernels
end Percolation


namespace Percolation
universe u
variable {V : Type u}
section RawReversal
namespace HoldingWalk
variable {H : SimpleGraph V}


theorem mass_snocHold (P : V → V → ℝ) {k : ℕ} {x y : V} (w : HoldingWalk H k x y) :
    w.snocHold.mass P = w.mass P * P y y := by
  induction w with
  | nil => simp only [snocHold,mass,mul_one,one_mul]
  | hold w ih => simp only [snocHold,mass,ih,mul_assoc]
  | step h w ih => simp only [snocHold,mass,ih,mul_assoc]

theorem mass_snocStep (P : V → V → ℝ) {k : ℕ} {x y z : V} (w : HoldingWalk H k x y) (h : H.Adj y z) :
    (w.snocStep h).mass P = w.mass P * P y z := by
  induction w with
  | nil => simp only [snocStep,mass,mul_one,one_mul]
  | hold w ih => simp only [snocStep,mass,ih,mul_assoc]
  | step h' w ih => simp only [snocStep,mass,ih,mul_assoc]

theorem mass_reverse (P : V → V → ℝ) (hP : ∀ x y, P x y = P y x)
    {k : ℕ} {x y : V} (w : HoldingWalk H k x y) : w.reverse.mass P = w.mass P := by
  induction w with
  | nil => rfl
  | hold w ih => simp only [reverse,mass_snocHold,mass,ih,mul_comm]
  | step h w ih => simp only [reverse,mass_snocStep,mass,ih,hP,mul_comm]

end HoldingWalk
end RawReversal
end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Escape_Labels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Labels for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section LabeledEscapeExperiment



namespace EscapeLabel
variable {G : BondGraph V E} {γ : I → V} {ep neg : I} {L m : ℕ}

theorem mass_nonneg (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (ξ : EscapeLabel G γ ep neg L m) : 0 ≤ ξ.mass P :=
  mul_nonneg (mul_nonneg (ξ.middle.mass_nonneg P hP) (ξ.leftTail.2.mass_nonneg P hP))
    (ξ.rightTail.2.mass_nonneg P hP)

theorem mass_reverse (P : V → V → ℝ) (hP : ∀ x y, P x y = P y x)
    (ξ : EscapeLabel G γ ep neg L m) : ξ.reverse.mass P = ξ.mass P := by
  simp only [mass,reverse,HoldingWalk.mass_reverse P hP]
  ring



end EscapeLabel
end LabeledEscapeExperiment
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section FiniteRootedLabels
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

instance finite_rootedLabelCode (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) :
    Finite (RootedLabelCode G hloc γ n hdiam center ep neg L m x) := by
  let (z : V) := finite_openSimpleGraph_neighbors G hloc z
  unfold RootedLabelCode
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

theorem finite_rootedEscapeLabels (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) :
    Finite {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x} :=
  Finite.of_equiv _ (rootedLabelEquiv G hloc γ n hdiam center ep neg L m x).symm

end FiniteRootedLabels
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section LabeledMass
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

theorem segmentAnchors_card_on_orbit (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i : I) (x : V)
    (hx : x ∈ vertexOrbit G (γ i)) :
    (segmentAnchors G hloc γ n hdiam i x).card = (segmentAnchors G hloc γ n hdiam i (γ i)).card := by
  obtain ⟨a,b,h,rfl⟩ := hx
  exact segmentAnchors_card_aut G hloc γ n hdiam i (γ i) h

theorem segmentAnchors_card_eq_indicator (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i : I) (x : V) :
    ((segmentAnchors G hloc γ n hdiam i x).card : ℝ) =
      if x ∈ vertexOrbit G (γ i) then (segmentAnchors G hloc γ n hdiam i (γ i)).card else 0 := by
  split_ifs with hx
  · exact congrArg Nat.cast (segmentAnchors_card_on_orbit G hloc γ n hdiam i x hx)
  · have hh := (segmentAnchors_nonempty_iff G hloc γ n hdiam i x).not.mpr hx
    rw [Finset.not_nonempty_iff_eq_empty.mp hh]
    rfl

theorem labelFromCode_mass (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) (P : V → V → ℝ)
    (c : RootedLabelCode G hloc γ n hdiam center ep neg L m x) :
    (labelFromCode G hloc γ n hdiam center ep neg L m x c).1.mass P =
      c.2.1.2.mass P * c.2.2.2.1.2.mass P * c.2.2.2.2.2.mass P := by
  rcases c with ⟨⟨s,hs⟩,⟨z,mid⟩,⟨h,hh⟩,α,β⟩
  obtain ⟨hhm,hhz⟩ := (mem_segmentAnchors G hloc γ n hdiam ep z h).mp hh
  subst z
  rfl

 

theorem rooted_label_mass_sum (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      ξ.1.mass (walkKernel G hloc a)) =
    ∑ s ∈ segmentAnchors G hloc γ n hdiam center x,
      ((segmentAnchors G hloc γ n hdiam ep (γ ep)).card : ℝ) *
        segmentReturnMass G hloc a γ ep L (s ep) := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let := finite_rootedEscapeLabels G hloc γ n hdiam center ep neg L m x
  let R := rootedLabelEquiv G hloc γ n hdiam center ep neg L m x
  rw [←R.symm.tsum_eq]
  simp only [R,rootedLabelEquiv,Equiv.coe_fn_symm_mk,labelFromCode_mass]
  unfold RootedLabelCode at *
  rw [(summable_of_hasFiniteSupport (Set.toFinite _)).tsum_sigma]
  change (∑' s : (segmentAnchors G hloc γ n hdiam center x), _) = _
  rw [tsum_fintype]
  conv_rhs => rw [←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro s _
  rw [(summable_of_hasFiniteSupport (Set.toFinite _)).tsum_sigma]
  have he (mid : RawFrom (openSimpleGraph G Set.univ) L (s.val ep)) :
      (∑' h : (segmentAnchors G hloc γ n hdiam ep mid.1),
        ∑' tails : RawFrom (openSimpleGraph G Set.univ) m (s.val neg) ×
            RawFrom (openSimpleGraph G Set.univ) m (h.val neg),
          mid.2.mass (walkKernel G hloc a) * tails.1.2.mass (walkKernel G hloc a) *
            tails.2.2.mass (walkKernel G hloc a)) =
      ((segmentAnchors G hloc γ n hdiam ep (γ ep)).card : ℝ) *
        (if mid.1 ∈ vertexOrbit G (γ ep) then mid.2.mass (walkKernel G hloc a) else 0) := by
    have ht (h : (segmentAnchors G hloc γ n hdiam ep mid.1)) :
        (∑' tails : RawFrom (openSimpleGraph G Set.univ) m (s.val neg) ×
            RawFrom (openSimpleGraph G Set.univ) m (h.val neg),
          mid.2.mass (walkKernel G hloc a) * tails.1.2.mass (walkKernel G hloc a) *
            tails.2.2.mass (walkKernel G hloc a)) = mid.2.mass (walkKernel G hloc a) := by
      rw [(summable_of_hasFiniteSupport (Set.toFinite _)).tsum_prod]
      simp only [tsum_mul_left,rawFrom_probability_sum G hloc a,mul_one]
    simp only [ht,tsum_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
    rw [segmentAnchors_card_eq_indicator G hloc γ n hdiam ep mid.1]
    split_ifs <;> ring
  calc
    _ = ∑' mid : RawFrom (openSimpleGraph G Set.univ) L (s.val ep),
        ((segmentAnchors G hloc γ n hdiam ep (γ ep)).card : ℝ) *
          (if mid.1 ∈ vertexOrbit G (γ ep) then mid.2.mass (walkKernel G hloc a) else 0) := by
      apply tsum_congr
      intro mid
      rw [(summable_of_hasFiniteSupport (Set.toFinite _)).tsum_sigma]
      exact he mid
    _ = _ := tsum_mul_left

end LabeledMass
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section LabeledNormalization
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

omit [Fintype I] in
theorem segmentReturnMass_operator (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (γ : I → V) (ep : I) (L : ℕ) (x : V)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ)) :
    segmentReturnMass G hloc a γ ep L x =
      ∑' y, if y ∈ vertexOrbit G (γ ep) then (matrixCoeff (P^L) x y).re else 0 := by
  have hh := raw_integral_operator G hloc a P hpos hP L x
    (fun y => if y ∈ vertexOrbit G (γ ep) then 1 else 0)
  simpa only [RawFrom.integral,mul_ite,mul_one,mul_zero,segmentReturnMass] using hh

omit [Fintype I] in
theorem segmentReturnMass_aut (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (γ : I → V) (ep : I) (L : ℕ) (x : V)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    {g : V ≃ V} {b : E ≃ E} (hg : IsAut G g b) :
    segmentReturnMass G hloc a γ ep L (g x) = segmentReturnMass G hloc a γ ep L x := by
  rw [segmentReturnMass_operator G hloc a γ ep L (g x) P hpos hP,
    segmentReturnMass_operator G hloc a γ ep L x P hpos hP,←g.tsum_eq]
  apply tsum_congr
  intro y
  rw [mem_vertexOrbit_aut_iff G (γ ep) hg]
  have hh := walkPower_invariant G hloc a P hP L g ⟨b,hg⟩ x y
  rw [hh]

omit [Fintype I] in
theorem segmentReturnMass_on_orbit (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (γ : I → V) (ep : I) (L : ℕ) (x : V)
    (hx : x ∈ vertexOrbit G (γ ep))
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ)) :
    segmentReturnMass G hloc a γ ep L x = segmentReturnMass G hloc a γ ep L (γ ep) := by
  obtain ⟨g,b,hg,rfl⟩ := hx
  exact segmentReturnMass_aut G hloc a γ ep L (γ ep) P hpos hP hg



theorem rooted_label_probability_sum (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) (hx : x ∈ vertexOrbit G (γ center))
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hq : segmentReturnMass G hloc a γ ep L (γ ep) ≠ 0) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1) = 1 := by
  have hN (i : I) : ((segmentAnchors G hloc γ n hdiam i (γ i)).card : ℝ) ≠ 0 := by
    apply ne_of_gt
    exact_mod_cast Finset.card_pos.mpr ((segmentAnchors_nonempty_iff G hloc γ n hdiam i (γ i)).mpr
      (by exact ⟨Equiv.refl V,Equiv.refl E,(fun e => by simp),rfl⟩))
  simp only [escapeLabelProbability,tsum_div_const]
  rw [rooted_label_mass_sum G hloc a γ n hdiam center ep neg L m x]
  have he (s : I → V) (hs : s ∈ segmentAnchors G hloc γ n hdiam center x) :
      segmentReturnMass G hloc a γ ep L (s ep) = segmentReturnMass G hloc a γ ep L (γ ep) := by
    obtain ⟨⟨g,b,hg,rfl⟩,_⟩ := (mem_segmentAnchors G hloc γ n hdiam center x s).mp hs
    exact segmentReturnMass_aut G hloc a γ ep L (γ ep) P hpos hP hg
  rw [Finset.sum_congr rfl (fun s hs => congrArg (fun q => _ * q) (he s hs))]
  simp only [Finset.sum_const,nsmul_eq_mul]
  rw [segmentAnchors_card_on_orbit G hloc γ n hdiam center x hx,←mul_assoc]
  exact div_self (mul_ne_zero (mul_ne_zero (hN center) (hN ep)) hq)

theorem escapeLabelProbability_reverse (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (ξ : EscapeLabel G γ ep neg L m) :
    escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.reverse =
      escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ := by
  simp only [escapeLabelProbability,EscapeLabel.mass_reverse _ (walkKernel_symmetric G hloc a)]

end LabeledNormalization
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}

namespace EscapeLabel
variable {G : BondGraph V E} {γ : I → V} {ep neg : I} {L m : ℕ}

theorem mass_autMap (hloc : LocallyFinite G) (a₀ : ℝ)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b)
    (ξ : EscapeLabel G γ ep neg L m) :
    (autMap hab ξ).mass (walkKernel G hloc a₀) = ξ.mass (walkKernel G hloc a₀) := by
  change (ξ.middle.map (autSimpleGraph G hab).toHom).mass (walkKernel G hloc a₀) *
    (ξ.leftTail.2.map (autSimpleGraph G hab).toHom).mass (walkKernel G hloc a₀) *
    (ξ.rightTail.2.map (autSimpleGraph G hab).toHom).mass (walkKernel G hloc a₀) = _
  simp only [HoldingWalk.mass_map (autSimpleGraph G hab).toHom _ _ (walkKernel_covariant G hloc a₀ hab)]
  rfl

end EscapeLabel
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section LazyOrbitReturn
attribute [local instance] Classical.propDecidable Classical.decEq

theorem positive_lazy_power_step (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re) (k : ℕ) (x y : V) :
    (1/2) * (matrixCoeff (P^k) x y).re ≤ (matrixCoeff (P^(k+1)) x y).re := by
  have hs := hpos.mul_hasSum (P^k) x y
  have hh := hs.summable.sum_le_tsum ({x} : Finset V)
    (fun z _ => mul_nonneg (hpos x z).2 ((hpos.pow k) z y).2)
  simp only [Finset.sum_singleton,hs.tsum_eq,←pow_succ'] at hh
  exact (mul_le_mul_of_nonneg_right (hdiag x) ((hpos.pow k) x y).2).trans hh

 

theorem walkPower_orbit_return_lower (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re) (L : ℕ) :
    (1/2) * (∑ i, if root i ∈ vertexOrbit G (root i₀) then weight i else 0) ≤
      ∑' y, if y ∈ vertexOrbit G (root i₀) then (matrixCoeff (P^L) (root i₀) y).re else 0 := by
  have hsum (k : ℕ) : Summable (fun y =>
      if y ∈ vertexOrbit G (root i₀) then (matrixCoeff (P^k) (root i₀) y).re else 0) := by
    simpa only [mul_ite,mul_one,mul_zero] using finiteKernel_summable_mul
      (fun x y => (matrixCoeff (P^k) x y).re) (walkPower_finite_support G hloc a P hpos hP k)
      (root i₀) (fun y => if y ∈ vertexOrbit G (root i₀) then 1 else 0)
  obtain ⟨k,hk | hk⟩ := Nat.even_or_odd' L
  · rw [hk]
    have hh := walkPower_even_orbit_return G hloc a root weight Γ hΓ htr hw hw1 i₀ hw₀ P hpos hsym hP k
    have hn : 0 ≤ ∑ i, if root i ∈ vertexOrbit G (root i₀) then weight i else 0 :=
      Finset.sum_nonneg (fun i _ => by split_ifs <;> first | exact hw i | rfl)
    linarith
  · rw [hk]
    have hh := mul_le_mul_of_nonneg_left
      (walkPower_even_orbit_return G hloc a root weight Γ hΓ htr hw hw1 i₀ hw₀ P hpos hsym hP k)
      (show (0:ℝ) ≤ 1/2 by norm_num)
    apply hh.trans
    rw [←tsum_mul_left]
    apply ((hsum (2*k)).mul_left (1/2)).tsum_le_tsum _ (hsum (2*k+1))
    intro y
    split_ifs
    · exact positive_lazy_power_step P hpos hdiag (2*k) (root i₀) y
    · simp only [mul_zero,le_refl]

end LazyOrbitReturn
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section UniformLabeledLaw
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

omit [Fintype I] in
 

theorem segmentReturnMass_uniform_lower (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ g ∈ Γ, g (root i) = x)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ i, 1 ≤ c*weight i)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re) (γ : I → V) (ep : I) (L : ℕ) :
    1/(2*c) ≤ segmentReturnMass G hloc a γ ep L (γ ep) := by
  obtain ⟨i,g,hg,hx⟩ := hcov (γ ep)
  obtain ⟨b,hb⟩ := hΓ hg
  have hO := vertexOrbit_eq_of_mem G (root i) (γ ep) ⟨g,b,hb,hx⟩
  rw [←hx,segmentReturnMass_aut G hloc a γ ep L (root i) P hpos hP hb]
  rw [segmentReturnMass_operator G hloc a γ ep L (root i) P hpos hP]
  rw [hO]
  have hh := walkPower_orbit_return_lower G hloc a root weight Γ hΓ htr
    (fun i => (hw i).le) hw1 i (hw i) P hpos hsym hP hdiag L
  have hi : weight i ≤ ∑ r, if root r ∈ vertexOrbit G (root i) then weight r else 0 := by
    have hx' : root i ∈ vertexOrbit G (root i) := ⟨Equiv.refl _,Equiv.refl _,isAut_refl G,rfl⟩
    simpa only [ite_eq_left hx'] using Finset.single_le_sum
      (f := fun r => if root r ∈ vertexOrbit G (root i) then weight r else 0)
      (fun r _ => by split_ifs <;> first | exact (hw r).le | rfl) (Finset.mem_univ i)
  apply le_trans _ hh
  have hct : 0 < 2*c := mul_pos (by norm_num) hc
  apply (div_le_iff₀ hct).mpr
  have hh' := mul_le_mul_of_nonneg_left hi hc.le
  nlinarith [hmin i]

 

theorem rooted_label_probability_hasSum (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ g ∈ Γ, g (root i) = x)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ i, 1 ≤ c*weight i)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) (hx : x ∈ vertexOrbit G (γ center)) :
    HasSum (fun ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x} =>
      escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1) 1 := by
  let := finite_rootedEscapeLabels G hloc γ n hdiam center ep neg L m x
  have hq := segmentReturnMass_uniform_lower G hloc a root weight Γ hΓ htr hcov hw hw1 c hc hmin
    P hpos hsym hP hdiag γ ep L
  have hp : 0 < segmentReturnMass G hloc a γ ep L (γ ep) :=
    (one_div_pos.mpr (mul_pos (by norm_num) hc)).trans_le hq
  have hs : Summable (fun ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x} =>
      escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1) :=
    summable_of_hasFiniteSupport (Set.toFinite _)
  rw [←rooted_label_probability_sum G hloc a γ n hdiam center ep neg L m x hx P hpos hP (ne_of_gt hp)]
  exact hs.hasSum

end UniformLabeledLaw
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section LabeledTransport
attribute [local instance] Classical.propDecidable Classical.decEq
variable {G : BondGraph V E} {γ : I → V} {ep neg : I} {L m : ℕ}

theorem escapeLabelTransport_reverse (center : I) (B : EscapeLabel G γ ep neg L m → ℝ) (x y : V) :
    escapeLabelTransport center B x y =
      escapeLabelTransport center (fun ξ => B ξ.reverse) y x := by
  unfold escapeLabelTransport
  exact (EscapeLabel.reverseRootedEquiv center y x).tsum_eq _ |>.symm

theorem escapeLabelTransport_aut (center : I) (B : EscapeLabel G γ ep neg L m → ℝ)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b)
    (hB : ∀ ξ, B (EscapeLabel.autMap hab ξ) = B ξ) (x y : V) :
    escapeLabelTransport center B (a x) (a y) = escapeLabelTransport center B x y := by
  unfold escapeLabelTransport
  rw [←(labelAutPairEquiv hab center x y).tsum_eq]
  exact tsum_congr (fun ξ => hB ξ.1)

variable [Fintype I]

theorem finite_pair_label_sigma (hloc : LocallyFinite G) (n : ℕ)
    (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (center : I) (x : V) :
    Finite (Σ y : V, {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x ∧ ξ.last center = y}) := by
  let := finite_rootedEscapeLabels G hloc γ n hdiam center ep neg L m x
  exact Finite.of_equiv _ (labelEndpointEquiv center x).symm

theorem escapeLabelTransport_row_sum (hloc : LocallyFinite G) (n : ℕ)
    (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (center : I)
    (B : EscapeLabel G γ ep neg L m → ℝ) (x : V) :
    (∑' y, escapeLabelTransport center B x y) =
      ∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x}, B ξ.1 := by
  let := finite_pair_label_sigma hloc n hdiam center (ep := ep) (neg := neg) (L := L) (m := m) x
  have hs : Summable (fun ξ : Σ y : V, {ξ : EscapeLabel G γ ep neg L m //
      ξ.first center = x ∧ ξ.last center = y} => B ξ.2.1) :=
    summable_of_hasFiniteSupport (Set.toFinite _)
  unfold escapeLabelTransport
  rw [←hs.tsum_sigma]
  exact (labelEndpointEquiv (G := G) (γ := γ) (ep := ep) (neg := neg) (L := L) (m := m) center x).tsum_eq (fun ξ => B ξ.1)

theorem escapeLabelTransport_rowSummable (hloc : LocallyFinite G) (n : ℕ)
    (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (center : I)
    (B : EscapeLabel G γ ep neg L m → ℝ) (x : V) :
    Summable (escapeLabelTransport center B x) := by
  let := finite_pair_label_sigma hloc n hdiam center (ep := ep) (neg := neg) (L := L) (m := m) x
  have hs : Summable (fun ξ : Σ y : V, {ξ : EscapeLabel G γ ep neg L m //
      ξ.first center = x ∧ ξ.last center = y} => B ξ.2.1) :=
    summable_of_hasFiniteSupport (Set.toFinite _)
  exact hs.sigma

theorem escapeLabelTransport_columnSummable (hloc : LocallyFinite G) (n : ℕ)
    (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (center : I)
    (B : EscapeLabel G γ ep neg L m → ℝ) (y : V) :
    Summable (fun x => escapeLabelTransport center B x y) := by
  simp only [escapeLabelTransport_reverse center B]
  exact escapeLabelTransport_rowSummable hloc n hdiam center (fun ξ => B ξ.reverse) y

end LabeledTransport
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section LabeledReRooting
attribute [local instance] Classical.propDecidable Classical.decEq
variable {G : BondGraph V E} {γ : I → V} {ep neg : I} {L m : ℕ}

theorem EscapeLabel.first_orbit (ξ : EscapeLabel G γ ep neg L m) (i : I) :
    ξ.first i ∈ vertexOrbit G (γ i) := by
  obtain ⟨a,b,h,he⟩ := ξ.first_mem
  exact ⟨a,b,h,(congrFun he i).symm⟩

theorem EscapeLabel.last_orbit (ξ : EscapeLabel G γ ep neg L m) (i : I) :
    ξ.last i ∈ vertexOrbit G (γ i) := by
  obtain ⟨a,b,h,he⟩ := ξ.last_mem
  exact ⟨a,b,h,(congrFun he i).symm⟩

theorem escapeLabelTransport_zero (center : I) (B : EscapeLabel G γ ep neg L m → ℝ)
    (x y : V) (hxy : x ∉ vertexOrbit G (γ center) ∨ y ∉ vertexOrbit G (γ center)) :
    escapeLabelTransport center B x y = 0 := by
  let : IsEmpty {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x ∧ ξ.last center = y} :=
    ⟨fun ξ => by
      rcases hxy with hx | hy
      · exact hx (ξ.2.1 ▸ ξ.1.first_orbit center)
      · exact hy (ξ.2.2 ▸ ξ.1.last_orbit center)⟩
  exact tsum_empty

variable [Fintype I]

 

theorem rooted_label_weight_reversal (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (center : I)
    (hθ : 0 < ∑ i, if root i ∈ vertexOrbit G (γ center) then weight i else 0)
    (B : EscapeLabel G γ ep neg L m → ℝ)
    (hB : ∀ (a : V ≃ V) (b : E ≃ E) (hab : IsAut G a b) ξ, B (EscapeLabel.autMap hab ξ) = B ξ)
    (x : V) (hx : x ∈ vertexOrbit G (γ center)) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x}, B ξ.1) =
      ∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x}, B ξ.1.reverse := by
  let M := escapeLabelTransport center B
  have hM (a : V ≃ V) (b : E ≃ E) (hab : IsAut G a b) (u v : V) : M (a u) (a v) = M u v :=
    escapeLabelTransport_aut center B hab (hB a b hab) u v
  have hr (u : V) : (∑' v, M u v) = if u ∈ vertexOrbit G (γ center) then ∑' v, M (γ center) v else 0 := by
    split_ifs with hu
    · obtain ⟨a,b,hab,rfl⟩ := hu
      rw [←a.tsum_eq]
      exact tsum_congr (fun v => hM a b hab (γ center) v)
    · calc
        _ = ∑' _ : V, (0:ℝ) := tsum_congr (fun v => escapeLabelTransport_zero center B u v (Or.inl hu))
        _ = 0 := tsum_zero
  have hc (v : V) : (∑' u, M u v) = if v ∈ vertexOrbit G (γ center) then ∑' u, M u (γ center) else 0 := by
    split_ifs with hv
    · obtain ⟨a,b,hab,rfl⟩ := hv
      rw [←a.tsum_eq]
      exact tsum_congr (fun u => hM a b hab u (γ center))
    · calc
        _ = ∑' _ : V, (0:ℝ) := tsum_congr (fun u => escapeLabelTransport_zero center B u v (Or.inr hv))
        _ = 0 := tsum_zero
  have ht := htr.real root weight Γ M
    (fun a ha u v => by obtain ⟨b,hb⟩ := hΓ ha; exact hM a b hb u v)
    (escapeLabelTransport_rowSummable hloc n hdiam center B)
    (escapeLabelTransport_columnSummable hloc n hdiam center B)
  have hfactor (f : V → ℝ) (q : ℝ) (he : ∀ u, f u = if u ∈ vertexOrbit G (γ center) then q else 0) :
      (∑ i, weight i*f (root i)) = (∑ i, if root i ∈ vertexOrbit G (γ center) then weight i else 0)*q := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [he]
    split_ifs <;> simp only [mul_zero,zero_mul]
  rw [hfactor _ _ hr,hfactor _ _ hc] at ht
  have hrc := (mul_left_cancel₀ (ne_of_gt hθ)) ht
  have hxe : (∑' v, M x v) = ∑' u, M u x := by
    rw [hr x,hc x,ite_eq_left hx,ite_eq_left hx]
    exact hrc
  calc
    _ = ∑' v, M x v := (escapeLabelTransport_row_sum hloc n hdiam center B x).symm
    _ = ∑' u, M u x := hxe
    _ = ∑' u, escapeLabelTransport center (fun ξ => B ξ.reverse) x u :=
      tsum_congr (fun u => escapeLabelTransport_reverse center B u x)
    _ = _ := escapeLabelTransport_row_sum hloc n hdiam center (fun ξ => B ξ.reverse) x

end LabeledReRooting
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section ExactLabeledReversal
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

theorem escapeLabelProbability_aut (G : BondGraph V E) (hloc : LocallyFinite G)
    (a₀ : ℝ) (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b)
    (ξ : EscapeLabel G γ ep neg L m) :
    escapeLabelProbability G hloc a₀ γ n hdiam center ep neg L m (EscapeLabel.autMap hab ξ) =
      escapeLabelProbability G hloc a₀ γ n hdiam center ep neg L m ξ := by
  simp only [escapeLabelProbability,EscapeLabel.mass_autMap]

 

theorem rooted_escape_label_reversal (G : BondGraph V E) (hloc : LocallyFinite G) (a₀ : ℝ)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (center ep neg : I) (L m : ℕ)
    (hθ : 0 < ∑ i, if root i ∈ vertexOrbit G (γ center) then weight i else 0)
    (F : EscapeLabel G γ ep neg L m → ℝ)
    (hF : ∀ (a : V ≃ V) (b : E ≃ E) (hab : IsAut G a b) ξ, F (EscapeLabel.autMap hab ξ) = F ξ)
    (x : V) (hx : x ∈ vertexOrbit G (γ center)) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      escapeLabelProbability G hloc a₀ γ n hdiam center ep neg L m ξ.1 * F ξ.1) =
    ∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      escapeLabelProbability G hloc a₀ γ n hdiam center ep neg L m ξ.1 * F ξ.1.reverse := by
  have hh := rooted_label_weight_reversal hloc root weight Γ hΓ htr n hdiam center hθ
    (fun ξ => escapeLabelProbability G hloc a₀ γ n hdiam center ep neg L m ξ * F ξ)
    (fun a b hab ξ => by rw [escapeLabelProbability_aut G hloc a₀ γ n hdiam center ep neg L m hab,hF a b hab]) x hx
  simpa only [escapeLabelProbability_reverse] using hh

theorem escapeLabelProbability_nonneg (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (hP : ∀ x y, 0 ≤ walkKernel G hloc a x y)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (ξ : EscapeLabel G γ ep neg L m) :
    0 ≤ escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ := by
  have hq : 0 ≤ segmentReturnMass G hloc a γ ep L (γ ep) := by
    apply tsum_nonneg
    intro mid
    split_ifs
    · exact mid.2.mass_nonneg _ hP
    · rfl
  exact div_nonneg (ξ.mass_nonneg _ hP) (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hq)

end ExactLabeledReversal
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ActualTailPotentials
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem raw_tail_twoPoint_expectation (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P A : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (p : unitInterval) (hA : HasKernel G p A) (m : ℕ) (x b : V) :
    (∑' w : RawFrom (openSimpleGraph G Set.univ) m x,
      w.2.mass (walkKernel G hloc a) * twoPoint G p w.1 b) =
      (matrixCoeff (P^m*A) x b).re := by
  have he : (fun y => twoPoint G p y b) = (fun y => (matrixCoeff A y b).re) := by
    funext y
    rw [matrixCoeff,hA y b,Complex.ofReal_re]
  change RawFrom.integral (H := openSimpleGraph G Set.univ) (walkKernel G hloc a) m x (twoPoint G p · b) = _
  rw [he,raw_integral_operator G hloc a P hpos hP]
  exact ((hpos.pow m).mul_hasSum A x b).tsum_eq

 

theorem raw_tail_potential_bound [Countable V] [Countable E] [Nonempty V]
    {ι : Type*} [Fintype ι]
    (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (root : ι → V) (weight : ι → ℝ) (htr : RootTransport root weight (vertexAut G))
    (hcov : ∀ x, ∃ i, ∃ e ∈ vertexAut G, e (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hsum : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c * weight i)
    (P A : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (p : unitInterval) (hA : HasKernel G p A) (m : ℕ) (x : V) (S : Finset V) :
    (∑' w : RawFrom (openSimpleGraph G Set.univ) m x,
      w.2.mass (walkKernel G hloc a) * ∑ b ∈ S, twoPoint G p w.1 b) ≤
      (S.card:ℝ) * Real.sqrt c * ‖P‖^m := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let := Fintype.ofFinite (RawFrom (openSimpleGraph G Set.univ) m x)
  have hPinv : KernelInvariant (vertexAut G) P := by
    intro e he x y
    obtain ⟨f,hf⟩ := he
    rw [hP,hP,walkKernel_covariant G hloc a hf]
  calc
    _ = ∑ b ∈ S, (∑' w : RawFrom (openSimpleGraph G Set.univ) m x,
        w.2.mass (walkKernel G hloc a) * twoPoint G p w.1 b) := by
      simp only [tsum_fintype,Finset.mul_sum]
      exact Finset.sum_comm
    _ = ∑ b ∈ S, (matrixCoeff (P^m*A) x b).re := by
      apply Finset.sum_congr rfl
      intro b _
      exact raw_tail_twoPoint_expectation G hloc a P A hpos hP p hA m x b
    _ ≤ ∑ _b ∈ S, Real.sqrt c * ‖P‖^m := by
      apply Finset.sum_le_sum
      intro b _
      exact (Complex.re_le_norm _).trans (twoPoint_operator_smoothing G p root weight htr hcov hw hsum c hc hmin A P hA hPinv m x b)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,mul_assoc]

end ActualTailPotentials
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AuxiliaryTailMarkov
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem finite_weighted_markov {α : Type*} [Fintype α] (μ F : α → ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hF : ∀ x, 0 ≤ F x) (t : ℝ) (ht : 0 < t) :
    (∑ x, if t < F x then μ x else 0) ≤ (∑ x, μ x*F x)/t := by
  apply (le_div_iff₀ ht).mpr
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro x _
  split_ifs with hx
  · exact mul_le_mul_of_nonneg_left hx.le (hμ x)
  · exact (by simpa only [zero_mul] using mul_nonneg (hμ x) (hF x))

theorem raw_tail_potential_failure [Countable V] [Countable E] [Nonempty V]
    {ι : Type*} [Fintype ι]
    (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (root : ι → V) (weight : ι → ℝ) (htr : RootTransport root weight (vertexAut G))
    (hcov : ∀ x, ∃ i, ∃ e ∈ vertexAut G, e (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hsum : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c * weight i)
    (P A : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (p : unitInterval) (hA : HasKernel G p A) (m : ℕ) (x : V) (S : Finset V)
    (t : ℝ) (ht : 0 < t) :
    (∑' w : RawFrom (openSimpleGraph G Set.univ) m x,
      if t < ∑ b ∈ S, twoPoint G p w.1 b then w.2.mass (walkKernel G hloc a) else 0) ≤
      ((S.card:ℝ) * Real.sqrt c * ‖P‖^m)/t := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let := Fintype.ofFinite (RawFrom (openSimpleGraph G Set.univ) m x)
  have hK (x y : V) : 0 ≤ walkKernel G hloc a x y := by
    simpa only [hP,Complex.ofReal_re] using (hpos x y).2
  have hM := finite_weighted_markov
    (fun w : RawFrom (openSimpleGraph G Set.univ) m x => w.2.mass (walkKernel G hloc a))
    (fun w => ∑ b ∈ S, twoPoint G p w.1 b)
    (fun w => w.2.mass_nonneg _ hK)
    (fun w => Finset.sum_nonneg (fun b _ => twoPoint_nonneg G p w.1 b)) t ht
  have hB := raw_tail_potential_bound G hloc a root weight htr hcov hw hsum c hc hmin P A hpos hP p hA m x S
  simp only [tsum_fintype] at hB ⊢
  exact hM.trans (div_le_div_of_nonneg_right hB ht.le)

 

theorem finite_product_failure_union {α β : Type*} [Fintype α] [Fintype β]
    (μ : α → ℝ) (ν : β → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hν : ∀ y, 0 ≤ ν y)
    (hμ1 : ∑ x, μ x = 1) (hν1 : ∑ y, ν y = 1) (B : α → Prop) (C : β → Prop) :
    (∑ z : α × β, if B z.1 ∨ C z.2 then μ z.1*ν z.2 else 0) ≤
      (∑ x, if B x then μ x else 0) + ∑ y, if C y then ν y else 0 := by
  calc
    _ ≤ ∑ z : α × β, ((if B z.1 then μ z.1 else 0)*ν z.2 + μ z.1*(if C z.2 then ν z.2 else 0)) := by
      apply Finset.sum_le_sum
      intro z _
      by_cases hB : B z.1 <;> by_cases hC : C z.2 <;>
        simp [hB,hC]
      exact mul_nonneg (hμ _) (hν _)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul,hμ1,hν1,mul_one,one_mul]

end AuxiliaryTailMarkov
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section IndependentTailPotentialTests
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem two_raw_tail_potential_failure [Countable V] [Countable E] [Nonempty V]
    {ι : Type*} [Fintype ι]
    (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (root : ι → V) (weight : ι → ℝ) (htr : RootTransport root weight (vertexAut G))
    (hcov : ∀ x, ∃ i, ∃ e ∈ vertexAut G, e (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hsum : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c * weight i)
    (P A : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (p : unitInterval) (hA : HasKernel G p A) (m : ℕ) (x y : V) (S : Finset V)
    (t : ℝ) (ht : 0 < t) :
    (∑' w : RawFrom (openSimpleGraph G Set.univ) m x × RawFrom (openSimpleGraph G Set.univ) m y,
      if (t < ∑ b ∈ S, twoPoint G p w.1.1 b) ∨ (t < ∑ b ∈ S, twoPoint G p w.2.1 b)
      then w.1.2.mass (walkKernel G hloc a) * w.2.2.mass (walkKernel G hloc a) else 0) ≤
      2*((S.card:ℝ) * Real.sqrt c * ‖P‖^m)/t := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let := Fintype.ofFinite (RawFrom (openSimpleGraph G Set.univ) m x)
  let := Fintype.ofFinite (RawFrom (openSimpleGraph G Set.univ) m y)
  have hK (u v : V) : 0 ≤ walkKernel G hloc a u v := by
    simpa only [hP,Complex.ofReal_re] using (hpos u v).2
  have hμ := rawFrom_probability_sum G hloc a m x
  have hν := rawFrom_probability_sum G hloc a m y
  simp only [tsum_fintype] at hμ hν
  have hU := finite_product_failure_union
    (fun w : RawFrom (openSimpleGraph G Set.univ) m x => w.2.mass (walkKernel G hloc a))
    (fun w : RawFrom (openSimpleGraph G Set.univ) m y => w.2.mass (walkKernel G hloc a))
    (fun w => w.2.mass_nonneg _ hK) (fun w => w.2.mass_nonneg _ hK) hμ hν
    (fun w => t < ∑ b ∈ S, twoPoint G p w.1 b)
    (fun w => t < ∑ b ∈ S, twoPoint G p w.1 b)
  have hx := raw_tail_potential_failure G hloc a root weight htr hcov hw hsum c hc hmin P A hpos hP p hA m x S t ht
  have hy := raw_tail_potential_failure G hloc a root weight htr hcov hw hsum c hc hmin P A hpos hP p hA m y S t ht
  simp only [tsum_fintype] at hx hy ⊢
  exact hU.trans ((add_le_add hx hy).trans_eq (by ring))

end IndependentTailPotentialTests
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Escape_CollisionTails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Collision Tails for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section NormalizedProjection
attribute [local instance] Classical.propDecidable Classical.decEq

theorem tsum_indicator_div {α : Type*} (f : α → ℝ) (B : α → Prop) [DecidablePred B] (d : ℝ) :
    (∑' a, if B a then f a/d else 0) = (∑' a, if B a then f a else 0)/d := by
  rw [←tsum_div_const]
  apply tsum_congr
  intro a
  split_ifs <;> simp

end NormalizedProjection
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Escape_PositiveEscapes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive Escapes for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
section WeightedBinaryUnion
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finite_weighted_event_or {α : Type*} [Fintype α]
    (μ : α → ℝ) (hμ : ∀ a, 0 ≤ μ a) (B C : α → Prop) [DecidablePred B] [DecidablePred C] :
    (∑ a, if B a ∨ C a then μ a else 0) ≤
      (∑ a, if B a then μ a else 0) + ∑ a, if C a then μ a else 0 := by
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  by_cases hb : B a <;> by_cases hc : C a <;> simp only [hb,hc,or_self,or_false,false_or,ite_true,ite_false,add_zero,zero_add,le_refl]
  exact le_add_of_nonneg_right (hμ a)

end WeightedBinaryUnion
end Percolation


namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section FirstLabeledMarginal
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]


theorem labelFromCode_first_collision (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (J L m : ℕ) (x : V)
    (posIdx negIdx suffixIdx : Fin (J+1) → I)
    (c : RootedLabelCode G hloc γ n hdiam center ep neg L m x) :
    labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx
      (labelFromCode G hloc γ n hdiam center ep neg L m x c).1 =
    firstEscapeCollision G J m L (c.1.val neg) (c.1.val ep)
      (fun t => c.1.val (posIdx t)) (fun t => c.1.val (negIdx t)) suffixIdx
      c.2.2.2.1 c.2.1 c.2.2.1.val := by
  rcases c with ⟨⟨s,hs⟩,⟨z,mid⟩,⟨h,hh⟩,α,β⟩
  obtain ⟨_,hhz⟩ := (mem_segmentAnchors G hloc γ n hdiam ep z h).mp hh
  subst z
  rfl

 

theorem raw_rooted_first_collision_marginal (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (J L m : ℕ) (x : V)
    (posIdx negIdx suffixIdx : Fin (J+1) → I) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      if labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ.1 then
        ξ.1.mass (walkKernel G hloc a) else 0) =
    ∑' s : segmentAnchors G hloc γ n hdiam center x,
      ∑' tail : RawFrom (openSimpleGraph G Set.univ) m (s.val neg),
        ∑' mid : RawFrom (openSimpleGraph G Set.univ) L (s.val ep),
          ∑' h : segmentAnchors G hloc γ n hdiam ep mid.1,
            if firstEscapeCollision G J m L (s.val neg) (s.val ep)
              (fun t => s.val (posIdx t)) (fun t => s.val (negIdx t)) suffixIdx tail mid h.val then
              tail.2.mass (walkKernel G hloc a)*mid.2.mass (walkKernel G hloc a) else 0 := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let (k : ℕ) (z : V) : Fintype (RawFrom (openSimpleGraph G Set.univ) k z) := Fintype.ofFinite _
  let := finite_rootedEscapeLabels G hloc γ n hdiam center ep neg L m x
  let R := rootedLabelEquiv G hloc γ n hdiam center ep neg L m x
  rw [←R.symm.tsum_eq]
  simp only [R,rootedLabelEquiv,Equiv.coe_fn_symm_mk,labelFromCode_mass,labelFromCode_first_collision]
  unfold RootedLabelCode at *
  rw [(summable_of_hasFiniteSupport (Set.toFinite _)).tsum_sigma]
  apply tsum_congr
  intro s
  rw [(summable_of_hasFiniteSupport (Set.toFinite _)).tsum_sigma]
  have hh (mid : RawFrom (openSimpleGraph G Set.univ) L (s.val ep)) :
      (∑' hh : Σ h : segmentAnchors G hloc γ n hdiam ep mid.1,
          RawFrom (openSimpleGraph G Set.univ) m (s.val neg) × RawFrom (openSimpleGraph G Set.univ) m (h.val neg),
        if firstEscapeCollision G J m L (s.val neg) (s.val ep)
          (fun t => s.val (posIdx t)) (fun t => s.val (negIdx t)) suffixIdx hh.2.1 mid hh.1.val then
          mid.2.mass (walkKernel G hloc a)*hh.2.1.2.mass (walkKernel G hloc a)*hh.2.2.2.mass (walkKernel G hloc a) else 0) =
      ∑' h : segmentAnchors G hloc γ n hdiam ep mid.1,
        ∑' tail : RawFrom (openSimpleGraph G Set.univ) m (s.val neg),
          if firstEscapeCollision G J m L (s.val neg) (s.val ep)
            (fun t => s.val (posIdx t)) (fun t => s.val (negIdx t)) suffixIdx tail mid h.val then
            tail.2.mass (walkKernel G hloc a)*mid.2.mass (walkKernel G hloc a) else 0 := by
    rw [(summable_of_hasFiniteSupport (Set.toFinite _)).tsum_sigma]
    apply tsum_congr
    intro h
    rw [(summable_of_hasFiniteSupport (Set.toFinite _)).tsum_prod]
    apply tsum_congr
    intro tail
    split_ifs
    · simp only [tsum_mul_left,rawFrom_probability_sum G hloc a,mul_one]
      exact mul_comm _ _
    · simp only [tsum_zero]
  simp_rw [hh]
  simp only [tsum_fintype]
  conv_lhs =>
    arg 2
    intro mid
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]

end FirstLabeledMarginal
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section NormalizedMarginal
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

 

theorem rooted_first_collision_probability_marginal (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (J L m : ℕ) (x : V)
    (posIdx negIdx suffixIdx : Fin (J+1) → I) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      if labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ.1 then
        escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1 else 0) =
    (∑' s : segmentAnchors G hloc γ n hdiam center x,
      (∑' tail : RawFrom (openSimpleGraph G Set.univ) m (s.val neg),
        ∑' mid : RawFrom (openSimpleGraph G Set.univ) L (s.val ep),
          ∑' h : segmentAnchors G hloc γ n hdiam ep mid.1,
            if firstEscapeCollision G J m L (s.val neg) (s.val ep)
              (fun t => s.val (posIdx t)) (fun t => s.val (negIdx t)) suffixIdx tail mid h.val then
              tail.2.mass (walkKernel G hloc a)*mid.2.mass (walkKernel G hloc a)/
                (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) /
          segmentReturnMass G hloc a γ ep L (γ ep)) /
      (segmentAnchors G hloc γ n hdiam center (γ center)).card := by
  simp only [escapeLabelProbability,tsum_indicator_div,tsum_div_const]
  rw [raw_rooted_first_collision_marginal G hloc a γ n hdiam center ep neg J L m x posIdx negIdx suffixIdx]
  ring

end NormalizedMarginal
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section FullFirstEscapeBound
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I] {ι : Type*} [Fintype ι]

 

theorem rooted_first_collision_probability_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G)
    (htr : RootTransport root weight Γ) (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
    (hcov : ∀ x, ∃ r, ∃ g ∈ Γ, g (root r) = x)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ r, 1 ≤ c*weight r)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (center ep neg : I)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re) (hρ : ‖P‖ < 1)
    (m L J : ℕ) (x : V) (hx : x ∈ vertexOrbit G (γ center))
    (posIdx negIdx suffixIdx : Fin (J+1) → I)
    (hsep : ∀ s ∈ segmentOrbit G γ,
      (∀ i, J ≤ (openSimpleGraph G Set.univ).dist (s neg) (s (posIdx i))) ∧
      (∀ i, J ≤ (openSimpleGraph G Set.univ).dist (s ep) (s (negIdx i))) ∧
      2*J ≤ (openSimpleGraph G Set.univ).dist (s neg) (s ep)) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      if labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ.1 then
        escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1 else 0) ≤
      2*c*(earlyCollisionCost ‖P‖ J + suffixCollisionCost ‖P‖ c J*‖P‖^L) := by
  rw [rooted_first_collision_probability_marginal G hloc a γ n hdiam center ep neg J L m x posIdx negIdx suffixIdx]
  have hN : 0 < ((segmentAnchors G hloc γ n hdiam center (γ center)).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ((segmentAnchors_nonempty_iff G hloc γ n hdiam center (γ center)).mpr
      ⟨Equiv.refl V,Equiv.refl E,isAut_refl G,rfl⟩)
  apply (div_le_iff₀ hN).mpr
  simp only [tsum_fintype]
  calc
    _ ≤ ∑ s : segmentAnchors G hloc γ n hdiam center x,
        2*c*(earlyCollisionCost ‖P‖ J + suffixCollisionCost ‖P‖ c J*‖P‖^L) := by
      apply Finset.sum_le_sum
      intro s _
      have hs := ((mem_segmentAnchors G hloc γ n hdiam center x s.val).mp s.property).1
      have hy : s.val ep ∈ vertexOrbit G (γ ep) := by
        obtain ⟨g,b,hg,he⟩ := hs
        rw [he]
        exact ⟨g,b,hg,rfl⟩
      obtain ⟨hp,hn,hxy⟩ := hsep s.val hs
      have hh := conditional_first_escape_collision_bound G hloc a root weight Γ hΓ htr hw hw1 hcov
        c hc hmin γ n hdiam ep P hpos hsym hP hdiag hρ m L J (s.val neg) (s.val ep) hy
        (fun i => s.val (posIdx i)) (fun i => s.val (negIdx i)) suffixIdx hp hn hxy
      rw [segmentReturnMass_on_orbit G hloc a γ ep L (s.val ep) hy P hpos hP] at hh
      simpa only [tsum_fintype] using hh
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
      rw [segmentAnchors_card_on_orbit G hloc γ n hdiam center x hx]
      ring

end FullFirstEscapeBound
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section CollisionNaturality
attribute [local instance] Classical.propDecidable Classical.decEq

namespace HoldingWalk
variable {W : Type*} {H : SimpleGraph V} {H' : SimpleGraph W}
theorem map_position (f : H →g H') {k : ℕ} {x y : V} (q : HoldingWalk H k x y) (i : ℕ) :
    (q.map f).position i = f (q.position i) := by
  induction q generalizing i with
  | nil => rfl
  | hold q ih => cases i <;> simp only [map,position,ih]
  | step h q ih => cases i <;> simp only [map,position,ih]
end HoldingWalk

theorem list_common_vertex_map_iff {W : Type*} (f : V → W) (hf : Function.Injective f)
    (l r : List V) :
    (∃ z, z ∈ l.map f ∧ z ∈ r.map f) ↔ ∃ z, z ∈ l ∧ z ∈ r := by
  constructor
  · rintro ⟨z,hz,hz'⟩
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz
    obtain ⟨y,hy,he⟩ := List.mem_map.mp hz'
    have : y = x := hf he
    subst y
    exact ⟨x,hx,hy⟩
  · rintro ⟨z,hz,hz'⟩
    exact ⟨f z,List.mem_map.mpr ⟨z,hz,rfl⟩,List.mem_map.mpr ⟨z,hz',rfl⟩⟩

 
theorem labelFirstEscapeCollision_aut (G : BondGraph V E) (γ : I → V) (ep neg : I)
    (J L m : ℕ) (posIdx negIdx suffixIdx : Fin (J+1) → I)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b)
    (ξ : EscapeLabel G γ ep neg L m) :
    labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx (EscapeLabel.autMap hab ξ) ↔
      labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ := by
  dsimp only [labelFirstEscapeCollision,firstEscapeCollision,EscapeLabel.autMap,Function.comp_apply,autSimpleGraph]
  simp only [HoldingWalk.map_vertices,HoldingWalk.map_position]
  change (((∃ s, a (ξ.first (posIdx s)) ∈ ξ.leftTail.2.vertices.map a) ∨
    (∃ s, a (ξ.first (negIdx s)) ∈ ξ.middle.vertices.map a)) ∨
    (∃ z, z ∈ ξ.leftTail.2.vertices.map a ∧ z ∈ ξ.middle.vertices.map a)) ∨
    ((∃ st : Fin (J+1) × Fin (J+1), a (ξ.last (suffixIdx st.1)) = a (ξ.first (negIdx st.2))) ∨
      (∃ ij : Fin (m+1) × Fin (J+1), a (ξ.leftTail.2.position ij.1.val) = a (ξ.last (suffixIdx ij.2)))) ↔ _
  rw [list_common_vertex_map_iff a a.injective]
  simp only [List.mem_map,Equiv.apply_eq_iff_eq]
  simp

end CollisionNaturality
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section BothEscapeEvents
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I] {ι : Type*} [Fintype ι]

 
theorem rootOrbitWeight_pos (G : BondGraph V E)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (hw : ∀ i, 0 < weight i)
    (hcov : ∀ x, ∃ r, ∃ g ∈ Γ, g (root r) = x) (x : V) :
    0 < ∑ i, if root i ∈ vertexOrbit G x then weight i else 0 := by
  obtain ⟨r,g,hg,he⟩ := hcov x
  obtain ⟨b,hab⟩ := hΓ hg
  have hr : root r ∈ vertexOrbit G x := by
    refine ⟨g.symm,b.symm,isAut_symm G hab,?_⟩
    rw [←he,Equiv.symm_apply_apply]
  have hh : (if root r ∈ vertexOrbit G x then weight r else 0) ≤
      ∑ i, if root i ∈ vertexOrbit G x then weight i else 0 :=
    Finset.single_le_sum (f := fun i => if root i ∈ vertexOrbit G x then weight i else 0)
      (fun i _ => by split_ifs <;> first | exact (hw i).le | rfl) (Finset.mem_univ r)
  simpa only [ite_eq_left hr] using lt_of_lt_of_le (by simpa only [ite_eq_left hr] using hw r) hh

 

theorem rooted_escape_collision_reversal (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G)
    (htr : RootTransport root weight Γ) (hw : ∀ r, 0 < weight r)
    (hcov : ∀ x, ∃ r, ∃ g ∈ Γ, g (root r) = x)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (center ep neg : I)
    (m L J : ℕ) (x : V) (hx : x ∈ vertexOrbit G (γ center))
    (posIdx negIdx suffixIdx : Fin (J+1) → I) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      if labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ.1 then
        escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1 else 0) =
    ∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      if labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ.1.reverse then
        escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1 else 0 := by
  have hh := rooted_escape_label_reversal G hloc a root weight Γ hΓ htr γ n hdiam center ep neg L m
    (rootOrbitWeight_pos G root weight Γ hΓ hw hcov (γ center))
    (fun ξ => if labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ then (1:ℝ) else 0)
    (fun g b hab ξ => by rw [labelFirstEscapeCollision_aut G γ ep neg J L m posIdx negIdx suffixIdx hab ξ]) x hx
  simpa only [mul_ite,mul_one,mul_zero] using hh

end BothEscapeEvents
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section BothEscapeBound
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I] {ι : Type*} [Fintype ι]

 
theorem rooted_both_collision_probability_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G)
    (htr : RootTransport root weight Γ) (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
    (hcov : ∀ x, ∃ r, ∃ g ∈ Γ, g (root r) = x)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ r, 1 ≤ c*weight r)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (center ep neg : I)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re) (hρ : ‖P‖ < 1)
    (m L J : ℕ) (x : V) (hx : x ∈ vertexOrbit G (γ center))
    (posIdx negIdx suffixIdx : Fin (J+1) → I)
    (hsep : ∀ s ∈ segmentOrbit G γ,
      (∀ i, J ≤ (openSimpleGraph G Set.univ).dist (s neg) (s (posIdx i))) ∧
      (∀ i, J ≤ (openSimpleGraph G Set.univ).dist (s ep) (s (negIdx i))) ∧
      2*J ≤ (openSimpleGraph G Set.univ).dist (s neg) (s ep)) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      if labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ.1 ∨
        labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ.1.reverse then
        escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1 else 0) ≤
      4*c*(earlyCollisionCost ‖P‖ J + suffixCollisionCost ‖P‖ c J*‖P‖^L) := by
  have hK (x y : V) : 0 ≤ walkKernel G hloc a x y := by
    simpa only [hP,Complex.ofReal_re] using (hpos x y).2
  have hb := rooted_first_collision_probability_bound G hloc a root weight Γ hΓ htr hw hw1 hcov
    c hc hmin γ n hdiam center ep neg P hpos hsym hP hdiag hρ m L J x hx posIdx negIdx suffixIdx hsep
  have he := rooted_escape_collision_reversal G hloc a root weight Γ hΓ htr hw hcov
    γ n hdiam center ep neg m L J x hx posIdx negIdx suffixIdx
  let := finite_rootedEscapeLabels G hloc γ n hdiam center ep neg L m x
  let := Fintype.ofFinite {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x}
  have hu := finite_weighted_event_or
    (fun ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x} =>
      escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1)
    (fun ξ => escapeLabelProbability_nonneg G hloc a hK γ n hdiam center ep neg L m ξ.1)
    (fun ξ => labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ.1)
    (fun ξ => labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ.1.reverse)
  simp only [tsum_fintype] at hb he ⊢
  rw [←he] at hu
  linarith

end BothEscapeBound
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Escape_SelectionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Selection Bounds for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section TailConditioning
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

 

theorem rooted_label_event_of_tail_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (hK : ∀ x y, 0 ≤ walkKernel G hloc a x y)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V)
    (B : EscapeLabel G γ ep neg L m → Prop) (ε : ℝ)
    (hB : ∀ (s : segmentAnchors G hloc γ n hdiam center x)
      (mid : RawFrom (openSimpleGraph G Set.univ) L (s.val ep))
      (h : segmentAnchors G hloc γ n hdiam ep mid.1),
      (∑' tails : RawFrom (openSimpleGraph G Set.univ) m (s.val neg) ×
          RawFrom (openSimpleGraph G Set.univ) m (h.val neg),
        if B (labelFromCode G hloc γ n hdiam center ep neg L m x ⟨s,mid,h,tails⟩).1 then
          tails.1.2.mass (walkKernel G hloc a)*tails.2.2.mass (walkKernel G hloc a) else 0) ≤ ε) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      if B ξ.1 then ξ.1.mass (walkKernel G hloc a) else 0) ≤
      ε * ∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
        ξ.1.mass (walkKernel G hloc a) := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let (k : ℕ) (z : V) : Fintype (RawFrom (openSimpleGraph G Set.univ) k z) := Fintype.ofFinite _
  let := finite_rootedEscapeLabels G hloc γ n hdiam center ep neg L m x
  let R := rootedLabelEquiv G hloc γ n hdiam center ep neg L m x
  rw [←R.symm.tsum_eq,←R.symm.tsum_eq]
  simp only [R,rootedLabelEquiv,Equiv.coe_fn_symm_mk,labelFromCode_mass]
  unfold RootedLabelCode at *
  simp only [tsum_fintype,Fintype.sum_sigma,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  apply Finset.sum_le_sum
  intro mid _
  apply Finset.sum_le_sum
  intro h _
  have hh := hB s mid h
  simp only [tsum_fintype] at hh
  have ht : (∑ tails : RawFrom (openSimpleGraph G Set.univ) m (s.val neg) ×
      RawFrom (openSimpleGraph G Set.univ) m (h.val neg),
        tails.1.2.mass (walkKernel G hloc a)*tails.2.2.mass (walkKernel G hloc a)) = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [←Finset.mul_sum,←Finset.sum_mul]
    simpa only [tsum_fintype,mul_one] using congrArg₂ (fun r t : ℝ => r*t)
      (rawFrom_probability_sum G hloc a m (s.val neg))
      (rawFrom_probability_sum G hloc a m (h.val neg))
  calc
    _ = mid.2.mass (walkKernel G hloc a) *
        ∑ tails : RawFrom (openSimpleGraph G Set.univ) m (s.val neg) ×
          RawFrom (openSimpleGraph G Set.univ) m (h.val neg),
          if B (labelFromCode G hloc γ n hdiam center ep neg L m x ⟨s,mid,h,tails⟩).1 then
            tails.1.2.mass (walkKernel G hloc a)*tails.2.2.mass (walkKernel G hloc a) else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro tails _
      split_ifs <;> simp only [mul_zero,mul_assoc]
    _ ≤ mid.2.mass (walkKernel G hloc a)*ε := mul_le_mul_of_nonneg_left hh (mid.2.mass_nonneg _ hK)
    _ = _ := by
      simp only [mul_assoc,←Finset.mul_sum]
      rw [ht]
      ring

end TailConditioning
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section NormalizedTailConditioning
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

 

theorem rooted_label_probability_of_tail_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ g ∈ Γ, g (root i) = x)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ i, 1 ≤ c*weight i)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) (hx : x ∈ vertexOrbit G (γ center)) 
    (B : EscapeLabel G γ ep neg L m → Prop) (ε : ℝ)
    (hB : ∀ (s : segmentAnchors G hloc γ n hdiam center x)
      (mid : RawFrom (openSimpleGraph G Set.univ) L (s.val ep))
      (h : segmentAnchors G hloc γ n hdiam ep mid.1),
      (∑' tails : RawFrom (openSimpleGraph G Set.univ) m (s.val neg) ×
          RawFrom (openSimpleGraph G Set.univ) m (h.val neg),
        if B (labelFromCode G hloc γ n hdiam center ep neg L m x ⟨s,mid,h,tails⟩).1 then
          tails.1.2.mass (walkKernel G hloc a)*tails.2.2.mass (walkKernel G hloc a) else 0) ≤ ε) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      if B ξ.1 then escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1 else 0) ≤ ε := by
  have hK (x y : V) : 0 ≤ walkKernel G hloc a x y := by
    simpa only [hP,Complex.ofReal_re] using (hpos x y).2
  have hq := segmentReturnMass_uniform_lower G hloc a root weight Γ hΓ htr hcov hw hw1 c hc hmin
    P hpos hsym hP hdiag γ ep L
  have hqp : 0 ≤ segmentReturnMass G hloc a γ ep L (γ ep) :=
    (one_div_pos.mpr (mul_pos (by norm_num) hc)).le.trans hq
  let D := ((segmentAnchors G hloc γ n hdiam center (γ center)).card : ℝ) *
    ((segmentAnchors G hloc γ n hdiam ep (γ ep)).card : ℝ) *
      segmentReturnMass G hloc a γ ep L (γ ep)
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hqp
  have hr := rooted_label_event_of_tail_bound G hloc a hK γ n hdiam center ep neg L m x B ε hB
  have hs := (rooted_label_probability_hasSum G hloc a root weight Γ hΓ htr hcov hw hw1 c hc hmin
    P hpos hsym hP hdiag γ n hdiam center ep neg L m x hx).tsum_eq
  have hd := div_le_div_of_nonneg_right hr hD
  have he : (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      ξ.1.mass (walkKernel G hloc a))/D = 1 := by
    simpa only [escapeLabelProbability,tsum_div_const,D] using hs
  simpa only [escapeLabelProbability,tsum_indicator_div,tsum_div_const,D,
    mul_div_assoc,he,mul_one] using hd

end NormalizedTailConditioning
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section FullPotentialTests
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]


theorem labelFromCode_potential_failure (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V)
    (F : (s : I → V) → RawFrom (openSimpleGraph G Set.univ) L (s ep) → (I → V) → Finset V)
    (t : ℝ) (s : segmentAnchors G hloc γ n hdiam center x)
    (mid : RawFrom (openSimpleGraph G Set.univ) L (s.val ep))
    (h : segmentAnchors G hloc γ n hdiam ep mid.1)
    (tails : RawFrom (openSimpleGraph G Set.univ) m (s.val neg) ×
      RawFrom (openSimpleGraph G Set.univ) m (h.val neg)) :
    labelPotentialFailure G p γ ep neg L m F t
      (labelFromCode G hloc γ n hdiam center ep neg L m x ⟨s,mid,h,tails⟩).1 ↔
      (t < ∑ b ∈ F s.val mid h.val, twoPoint G p tails.1.1 b) ∨
      (t < ∑ b ∈ F s.val mid h.val, twoPoint G p tails.2.1 b) := by
  rcases s with ⟨s,hs⟩
  rcases mid with ⟨z,mid⟩
  rcases h with ⟨h,hh⟩
  obtain ⟨_,hhz⟩ := (mem_segmentAnchors G hloc γ n hdiam ep z h).mp hh
  subst z
  rfl

 

theorem rooted_label_potential_failure_bound [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G))
    (hcov : ∀ x, ∃ r, ∃ g ∈ vertexAut G, g (root r) = x)
    (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ r, 1 ≤ c*weight r)
    (P A : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re)
    (p : unitInterval) (hA : HasKernel G p A)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) (hx : x ∈ vertexOrbit G (γ center))
    (F : (s : I → V) → RawFrom (openSimpleGraph G Set.univ) L (s ep) → (I → V) → Finset V)
    (N : ℝ) (hN : ∀ s mid h, ((F s mid h).card : ℝ) ≤ N) (t : ℝ) (ht : 0 < t) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      if labelPotentialFailure G p γ ep neg L m F t ξ.1 then
        escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1 else 0) ≤
      2*(N*Real.sqrt c*‖P‖^m)/t := by
  apply rooted_label_probability_of_tail_bound G hloc a root weight (vertexAut G) (Set.Subset.refl _)
    htr hcov hw hw1 c hc hmin P hpos hsym hP hdiag γ n hdiam center ep neg L m x hx
  intro s mid h
  simp only [labelFromCode_potential_failure]
  have hh := two_raw_tail_potential_failure G hloc a root weight htr hcov (fun r => (hw r).le) hw1
    c hc.le hmin P A hpos hP p hA m (s.val neg) (h.val neg) (F s.val mid h.val) t ht
  apply hh.trans
  gcongr
  exact hN s.val mid h.val

end FullPotentialTests
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section CombinedSelectionEvents
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

 

theorem rooted_label_collision_potential_failure_bound_oai [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G))
    (hcov : ∀ x, ∃ r, ∃ g ∈ vertexAut G, g (root r) = x)
    (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ r, 1 ≤ c*weight r)
    (P A : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re)
    (p : unitInterval) (hA : HasKernel G p A)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) (hx : x ∈ vertexOrbit G (γ center))
    (hρ : ‖P‖ < 1) (J : ℕ) (posIdx negIdx suffixIdx : Fin (J+1) → I)
    (hsep : ∀ s ∈ segmentOrbit G γ,
      (∀ i, J ≤ (openSimpleGraph G Set.univ).dist (s neg) (s (posIdx i))) ∧
      (∀ i, J ≤ (openSimpleGraph G Set.univ).dist (s ep) (s (negIdx i))) ∧
      2*J ≤ (openSimpleGraph G Set.univ).dist (s neg) (s ep))
    (F : (s : I → V) → RawFrom (openSimpleGraph G Set.univ) L (s ep) → (I → V) → Finset V)
    (N : ℝ) (hN : ∀ s mid h, ((F s mid h).card : ℝ) ≤ N) (t : ℝ) (ht : 0 < t) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      if (labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ.1 ∨
        labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ.1.reverse) ∨
        labelPotentialFailure G p γ ep neg L m F t ξ.1 then
        escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1 else 0) ≤
      4*c*(earlyCollisionCost ‖P‖ J + suffixCollisionCost ‖P‖ c J*‖P‖^L) +
        2*(N*Real.sqrt c*‖P‖^m)/t := by
  have hK (x y : V) : 0 ≤ walkKernel G hloc a x y := by
    simpa only [hP,Complex.ofReal_re] using (hpos x y).2
  have hb := rooted_both_collision_probability_bound G hloc a root weight (vertexAut G) (Set.Subset.refl _)
    htr hw hw1 hcov c hc hmin γ n hdiam center ep neg P hpos hsym hP hdiag hρ m L J x hx posIdx negIdx suffixIdx hsep
  have hp := rooted_label_potential_failure_bound G hloc a root weight htr hcov hw hw1 c hc hmin
    P A hpos hsym hP hdiag p hA γ n hdiam center ep neg L m x hx F N hN t ht
  let := finite_rootedEscapeLabels G hloc γ n hdiam center ep neg L m x
  let := Fintype.ofFinite {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x}
  have hu := finite_weighted_event_or
    (fun ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x} =>
      escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1)
    (fun ξ => escapeLabelProbability_nonneg G hloc a hK γ n hdiam center ep neg L m ξ.1)
    (fun ξ => labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ.1 ∨
      labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ.1.reverse)
    (fun ξ => labelPotentialFailure G p γ ep neg L m F t ξ.1)
  simp only [tsum_fintype] at hb hp ⊢
  exact hu.trans (add_le_add hb hp)

end CombinedSelectionEvents
end Percolation


end OAI
end

theorem solution.{u, v, w, u_1} : type_of% @OAI.Percolation.rooted_label_collision_potential_failure_bound_oai.{u, v, w, u_1} := @OAI.Percolation.rooted_label_collision_potential_failure_bound_oai.{u, v, w, u_1}
