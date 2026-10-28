-- Prove2me | solution 1 for OAI.Percolation.rooted_selected_label_mass_lower
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T01:10:37.87279+00:00
-- url     : https://prove2.me/submissions/94574739-d419-4de3-baa3-f2494b020dd6

import Mathlib
import Definitions.Def_CayleyPercolation
import Definitions.Def_OAIQ040C002
import Theorems.Thm_OAI_Percolation_rooted_label_collision_potential_failure_bound

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
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Graph_Paths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bond paths, degree bounds and positivity of the critical parameter. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section DegreeBound
attribute [local instance] Classical.propDecidable

 theorem finite_steps (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) :
    Set.Finite {ey : E × V | G ey.1 = s(x,ey.2)} := by
  apply ((hloc x).prod (finite_neighbors hloc x)).subset
  rintro ⟨e,y⟩ he
  change G e = s(x,y) at he
  exact ⟨by change x ∈ G e; rw [he]; simp, e, he⟩

end DegreeBound

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


theorem neighbors_card_le_degree (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) :
    (neighbors G hloc x).card ≤ degree G x := by
  let : Fintype (Step G x) := (finite_steps G hloc x).fintype
  let p : Step G x → {y // y ∈ neighbors G hloc x} :=
    fun d => ⟨d.val.2, (mem_neighbors G hloc x d.val.2).mpr ⟨d.val.1,d.property⟩⟩
  have hp : Function.Surjective p := by
    intro y
    obtain ⟨e,he⟩ := (mem_neighbors G hloc x y.val).mp y.property
    exact ⟨⟨(e,y.val),he⟩,Subtype.ext rfl⟩
  simpa only [degree,Nat.card_eq_fintype_card,Fintype.card_coe] using
    Fintype.card_le_of_surjective p hp

end IsoperimetricEnergy

section SymmetricWalk
attribute [local instance] Classical.propDecidable



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

section InvariantOperatorTrace
open scoped ComplexOrder InnerProduct
attribute [local instance] Classical.propDecidable

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

 theorem matrixCoeff_mul_invariant (a : V ≃ V) (A B : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, matrixCoeff A (a x) (a y) = matrixCoeff A x y)
    (hB : ∀ x y, matrixCoeff B (a x) (a y) = matrixCoeff B x y) :
    ∀ x y, matrixCoeff (A*B) (a x) (a y) = matrixCoeff (A*B) x y := by
  intro x y
  simp only [matrixCoeff_mul]
  rw [← a.tsum_eq (fun z => matrixCoeff A (a x) z * matrixCoeff B z (a y))]
  simp only [hA,hB]

section RootTrace
variable {ι : Type*} [Fintype ι]
variable (root : ι → V) (weight : ι → ℝ)

theorem KernelInvariant.mul {Γ : Set (V ≃ V)}
    {A B : Hilbert V →L[ℂ] Hilbert V}
    (hA : KernelInvariant Γ A) (hB : KernelInvariant Γ B) :
    KernelInvariant Γ (A*B) := by
  intro a ha
  exact matrixCoeff_mul_invariant a A B (hA a ha) (hB a ha)

end RootTrace

end InvariantOperatorTrace

section InvariantPercolationOperators
open scoped ComplexOrder InnerProduct
attribute [local instance] Classical.propDecidable


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

 

theorem transported_column_le (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (m : V → V → ℝ) (hm : ∀ x y, 0 ≤ m x y)
    (hi : ∀ a ∈ Γ, ∀ x y, m (a x) (a y) = m x y)
    (hr : ∀ x, Summable (m x)) (hcol : ∀ y, Summable (fun x => m x y))
    (B : ℝ) (hB : ∀ x, ∑' y, m x y ≤ B) (y : V) :
    (∑' x, m x y) ≤ c*B := by
  have ht := htr.real root weight Γ m hi hr hcol
  have hb : (∑ i, weight i * ∑' x, m x (root i)) ≤ B := by
    rw [← ht]
    calc
      _ ≤ ∑ i, weight i * B := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hB _) (hw i)
      _ = B := by rw [← Finset.sum_mul,hw1,one_mul]
  obtain ⟨i,a,ha,hay⟩ := hcov y
  have he : (∑' x, m x y) = ∑' x, m x (root i) := by
    rw [← hay,← a.tsum_eq (fun x => m x (a (root i)))]
    exact tsum_congr (fun x => hi a ha x (root i))
  have hn : 0 ≤ ∑' x, m x (root i) := tsum_nonneg (fun x => hm x _)
  have hs : weight i * ∑' x, m x (root i) ≤ ∑ j, weight j * ∑' x, m x (root j) :=
    Finset.single_le_sum (fun j _ => mul_nonneg (hw j) (tsum_nonneg (fun x => hm x (root j))))
      (Finset.mem_univ i)
  rw [he]
  calc
    _ ≤ (c*weight i) * ∑' x, m x (root i) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hmin i) hn
    _ = c * (weight i * ∑' x, m x (root i)) := by ring
    _ ≤ c * (∑ j, weight j * ∑' x, m x (root j)) := mul_le_mul_of_nonneg_left hs hc
    _ ≤ c*B := mul_le_mul_of_nonneg_left hb hc



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

theorem length_vertices (w : HoldingWalk H k x y) : w.vertices.length = k+1 := by
  induction w with
  | nil => rfl
  | hold w ih => simpa only [vertices,List.length_cons] using congrArg (fun n => n+1) ih
  | step h w ih => simpa only [vertices,List.length_cons] using congrArg (fun n => n+1) ih

theorem withoutHolds_length (w : HoldingWalk H k x y) : w.withoutHolds.length ≤ k := by
  induction w with
  | nil => simp [withoutHolds]
  | hold w ih => exact ih.trans (Nat.le_succ _)
  | step h w ih => simpa only [withoutHolds,SimpleGraph.Walk.length_cons] using Nat.succ_le_succ ih

theorem withoutHolds_support (w : HoldingWalk H k x y) : w.withoutHolds.support <+ w.vertices := by
  induction w with
  | nil => exact List.Sublist.refl _
  | hold w ih => exact ih.cons _
  | step h w ih => exact ih.cons_cons _



theorem erase_isPath (w : HoldingWalk H k x y) : w.erase.IsPath :=
  w.withoutHolds.reverse.bypass_isPath.reverse

theorem erase_length (w : HoldingWalk H k x y) : w.erase.length ≤ k := by
  have hh := w.withoutHolds.reverse.length_bypass_le_length
  simpa only [erase,SimpleGraph.Walk.length_reverse] using hh.trans (by simpa using w.withoutHolds_length)

theorem erase_support (w : HoldingWalk H k x y) : w.erase.support <+ w.vertices := by
  have hh := w.withoutHolds.reverse.support_bypass_sublist_support.reverse
  simp only [SimpleGraph.Walk.support_reverse,List.reverse_reverse] at hh
  simpa only [erase,SimpleGraph.Walk.support_reverse] using hh.trans w.withoutHolds_support

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
section CorridorSizeBounds
attribute [local instance] Classical.propDecidable Classical.decEq

theorem reachBall_ncard_le_pow (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (x : V) (k : ℕ) :
    (reachBall G x k).ncard ≤ (d+1)^k := by
  induction k with
  | zero => simp only [reachBall,Set.ncard_singleton,pow_zero,le_refl]
  | succ k ih =>
    let W := (finite_reachBall hloc x k).toFinset
    have he : reachBall G x (k+1) = (W ∪ W.biUnion (neighbors G hloc) : Finset V) := by
      ext z
      simp only [reachBall,Set.mem_union,Set.mem_iUnion,Set.mem_ofPred_eq,Finset.mem_coe,
        Finset.mem_union,Finset.mem_biUnion,mem_neighbors,Set.Finite.mem_toFinset,W,Adj,exists_prop]
    rw [he,Set.ncard_coe_finset]
    have hb : (W.biUnion (neighbors G hloc)).card ≤ W.card*d :=
      Finset.card_biUnion_le_card_mul _ _ _ (fun a _ => (neighbors_card_le_degree G hloc a).trans (hd a))
    have hi : W.card ≤ (d+1)^k := by simpa only [W,←Set.ncard_eq_toFinset_card] using ih
    calc
      _ ≤ W.card + (W.biUnion (neighbors G hloc)).card := Finset.card_union_le _ _
      _ ≤ W.card + W.card*d := Nat.add_le_add_left hb _
      _ = W.card*(d+1) := by ring
      _ ≤ (d+1)^k*(d+1) := Nat.mul_le_mul_right _ hi
      _ = _ := (pow_succ _ _).symm

end CorridorSizeBounds
end Percolation

 
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
universe u v
variable {V : Type u} {E : Type v}
section WeightedLegComparison
attribute [local instance] Classical.propDecidable Classical.decEq

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}
theorem base_not_interior (w : RawCorridor G k) : w.base ∉ w.interior := by
  simp only [interior,Finset.mem_sdiff,Finset.mem_insert,true_or,not_true_eq_false,and_false,not_false_eq_true]
theorem endpoint_not_interior (w : RawCorridor G k) : w.endpoint ∉ w.interior := by
  simp only [interior,Finset.mem_sdiff,Finset.mem_insert,Finset.mem_singleton,or_true,not_true_eq_false,and_false,not_false_eq_true]
end RawCorridor


end WeightedLegComparison
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



theorem anchoredPositionKernel_nonneg (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i j : I) (x y : V) :
    0 ≤ anchoredPositionKernel G hloc γ n hdiam i j x y := by
  apply Finset.sum_nonneg
  intro s _
  split_ifs <;> positivity

theorem anchoredPositionKernel_aut (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i j : I) (x y : V)
    {a : V ≃ V} {b : E ≃ E} (h : IsAut G a b) :
    anchoredPositionKernel G hloc γ n hdiam i j (a x) (a y) =
      anchoredPositionKernel G hloc γ n hdiam i j x y := by
  simp only [anchoredPositionKernel,segmentAnchors_map G hloc γ n hdiam i x h,
    Finset.card_map,Finset.sum_map,Equiv.toEmbedding_apply,
    segmentAut,Equiv.coe_fn_mk,Function.comp_apply,Equiv.apply_eq_iff_eq]

end AnchoredPositionKernels
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AnchoredPositionRows
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I : Type*} [Fintype I]

theorem anchoredPositionKernel_hasSum (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i j : I) (x : V) :
    HasSum (anchoredPositionKernel G hloc γ n hdiam i j x)
      (if x ∈ vertexOrbit G (γ i) then (1:ℝ) else 0) := by
  have hh := hasSum_sum (s := segmentAnchors G hloc γ n hdiam i x)
    (fun s _ => hasSum_ite_eq (s j) (((segmentAnchors G hloc γ n hdiam i x).card:ℝ)⁻¹))
  have he : (∑ s ∈ segmentAnchors G hloc γ n hdiam i x,
      ((segmentAnchors G hloc γ n hdiam i x).card:ℝ)⁻¹) =
      if x ∈ vertexOrbit G (γ i) then (1:ℝ) else 0 := by
    simp only [Finset.sum_const,nsmul_eq_mul]
    by_cases hx : x ∈ vertexOrbit G (γ i)
    · have hn := Finset.card_pos.mpr ((segmentAnchors_nonempty_iff G hloc γ n hdiam i x).mpr hx)
      rw [ite_eq_left hx,mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))]
    · have he : segmentAnchors G hloc γ n hdiam i x = ∅ := Finset.not_nonempty_iff_eq_empty.mp
        (fun h => hx ((segmentAnchors_nonempty_iff G hloc γ n hdiam i x).mp h))
      simp only [he,Finset.card_empty,Nat.cast_zero,zero_mul,ite_eq_right hx]
  rw [he] at hh
  exact hh

end AnchoredPositionRows
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AnchoredPositionColumns
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I : Type*} [Fintype I]

theorem anchoredPositionKernel_columnSummable (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i j : I) (y : V) :
    Summable (fun x => anchoredPositionKernel G hloc γ n hdiam i j x y) := by
  apply summable_of_ne_finset_zero (s := (finite_reachBall hloc y n).toFinset)
  intro x hx
  simp only [Set.Finite.mem_toFinset] at hx
  apply Finset.sum_eq_zero
  intro s hs
  apply ite_eq_right
  intro hy
  obtain ⟨⟨a,b,hab,rfl⟩,he⟩ := (mem_segmentAnchors G hloc γ n hdiam i x s).mp hs
  change a (γ i) = x at he
  change y = a (γ j) at hy
  exact hx (by simpa only [he,←hy] using mem_reachBall_aut G hab (hdiam j i))

end AnchoredPositionColumns
end Percolation

 
namespace Percolation
universe u
variable {V : Type u}
section AsymmetricSchur
open scoped ENNReal
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem exists_operator_of_unit_row_column_bound (U : V → V → ℝ) (D : ℝ)
    (hD : 0 ≤ D) (hU : ∀ x y, 0 ≤ U x y)
    (hrow : ∀ x (s : Finset V), ∑ y ∈ s, U x y ≤ 1)
    (hcol : ∀ y (s : Finset V), ∑ x ∈ s, U x y ≤ D) :
    ∃ A : Hilbert V →L[ℂ] Hilbert V, ‖A‖ ≤ Real.sqrt D ∧
      ∀ x y, matrixCoeff A x y = (U x y : ℂ) := by
  have hentry (x y : V) : U x y ≤ 1 := by simpa only [Finset.sum_singleton] using hrow x {y}
  have hcm (y : V) : Memℓp (fun x => (U x y : ℂ)) 2 := by
    apply (memℓp_gen_iff'' (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mpr
    refine ⟨D,hD,fun s => ?_⟩
    simp only [ENNReal.toReal_ofNat,Real.rpow_two,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    exact (Finset.sum_le_sum (fun x _ => by nlinarith [hentry x y,hU x y])).trans (hcol y s)
  let col (y : V) : Hilbert V := ⟨fun x => (U x y : ℂ),hcm y⟩
  let L : (V →₀ ℂ) →ₗ[ℂ] Hilbert V := Finsupp.linearCombination ℂ col
  have hn (f : V →₀ ℂ) : ‖L f‖ ≤ Real.sqrt D * ‖finiteEmbedding f‖ := by
    apply lp.norm_le_of_forall_sum_le (by norm_num)
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    intro s
    simp only [ENNReal.toReal_ofNat,Real.rpow_two]
    have hpoint (x : V) : ‖L f x‖^2 ≤ ∑ y ∈ f.support, ‖f y‖^2 * U x y := by
      have hn0 : 0 ≤ ∑ y ∈ f.support, ‖f y‖*U x y :=
        Finset.sum_nonneg (fun y _ => mul_nonneg (norm_nonneg _) (hU x y))
      have hn1 : ‖L f x‖ ≤ ∑ y ∈ f.support, ‖f y‖*U x y := by
        simp only [L,Finsupp.linearCombination_apply,Finsupp.sum,lp.coeFn_sum,
          Finset.sum_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul]
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro y _
        simp [col,abs_of_nonneg (hU x y)]
      have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul f.support
        (f := fun y => U x y) (g := fun y => ‖f y‖^2*U x y)
        (r := fun y => ‖f y‖*U x y)
        (fun y _ => hU x y)
        (fun y _ => mul_nonneg (sq_nonneg _) (hU x y)) (fun y _ => by nlinarith)
      have hn2 : 0 ≤ ∑ y ∈ f.support, ‖f y‖^2*U x y :=
        Finset.sum_nonneg (fun y _ => mul_nonneg (sq_nonneg _) (hU x y))
      have hr := mul_le_mul_of_nonneg_right (hrow x f.support) hn2
      rw [one_mul] at hr
      exact (sq_le_sq₀ (norm_nonneg _) hn0 |>.mpr hn1).trans (hcs.trans hr)
    calc
      ∑ x ∈ s, ‖L f x‖^2 ≤ ∑ x ∈ s, ∑ y ∈ f.support, ‖f y‖^2*U x y :=
        Finset.sum_le_sum (fun x _ => hpoint x)
      _ = ∑ y ∈ f.support, ‖f y‖^2*∑ x ∈ s, U x y := by
        rw [Finset.sum_comm]
        simp_rw [Finset.mul_sum]
      _ ≤ ∑ y ∈ f.support, ‖f y‖^2*D :=
        Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (hcol y s) (sq_nonneg _))
      _ = D*∑ y ∈ f.support, ‖finiteEmbedding f y‖^2 := by
        simp only [finiteEmbedding_apply]
        rw [←Finset.sum_mul,mul_comm]
      _ ≤ D*‖finiteEmbedding f‖^2 := by
        apply mul_le_mul_of_nonneg_left _ hD
        simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
          lp.sum_rpow_le_norm_rpow (by norm_num : 0 < (2:ℝ≥0∞).toReal) (finiteEmbedding f) f.support
      _ = (Real.sqrt D*‖finiteEmbedding f‖)^2 := by rw [mul_pow,Real.sq_sqrt hD]
  refine ⟨L.extendOfNorm finiteEmbedding,
    LinearMap.opNorm_extendOfNorm_le finiteEmbedding_dense (Real.sqrt_nonneg _) hn,?_⟩
  intro x y
  have he := LinearMap.extendOfNorm_eq (f := L) finiteEmbedding_dense ⟨Real.sqrt D,hn⟩
    (Finsupp.single y (1:ℂ))
  simp only [finiteEmbedding_single] at he
  change (L.extendOfNorm finiteEmbedding) (lp.single 2 y (1:ℂ)) x = _
  rw [he]
  simp [L,col]

end AsymmetricSchur
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AnchoredPositionOperators
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I ι : Type*} [Fintype I] [Fintype ι]



theorem exists_anchoredPositionOperator_uniform (G : BondGraph V E) (hloc : LocallyFinite G)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G)
    (htr : RootTransport root weight Γ) (hw : ∀ r, 0 ≤ weight r) (hw1 : ∑ r, weight r = 1)
    (hcov : ∀ x, ∃ r, ∃ a ∈ Γ, a (root r) = x)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ r, 1 ≤ c*weight r)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i j : I) :
    ∃ H : Hilbert V →L[ℂ] Hilbert V,
      (∀ x y, matrixCoeff H x y = (anchoredPositionKernel G hloc γ n hdiam i j x y : ℂ)) ∧
      ‖H‖ ≤ Real.sqrt c := by
  let U := anchoredPositionKernel G hloc γ n hdiam i j
  have hn : ∀ x y, 0 ≤ U x y := anchoredPositionKernel_nonneg G hloc γ n hdiam i j
  have hr : ∀ x, Summable (U x) := fun x => (anchoredPositionKernel_hasSum G hloc γ n hdiam i j x).summable
  have hcol := anchoredPositionKernel_columnSummable G hloc γ n hdiam i j
  have hb (x : V) : (∑' y, U x y) ≤ 1 := by
    rw [(anchoredPositionKernel_hasSum G hloc γ n hdiam i j x).tsum_eq]
    split_ifs <;> norm_num
  have hi : ∀ a ∈ Γ, ∀ x y, U (a x) (a y) = U x y := by
    intro a ha x y
    obtain ⟨b,hb⟩ := hΓ ha
    exact anchoredPositionKernel_aut G hloc γ n hdiam i j x y hb
  have hbcol (y : V) : (∑' x, U x y) ≤ c := by
    simpa only [mul_one] using transported_column_le root weight Γ htr hcov hw hw1 c hc hmin U hn hi hr hcol 1 hb y
  obtain ⟨H,hHn,hH⟩ := exists_operator_of_unit_row_column_bound U c hc hn
    (fun x s => ((hr x).sum_le_tsum s (fun y _ => hn x y)).trans (hb x))
    (fun y s => ((hcol y).sum_le_tsum s (fun x _ => hn x y)).trans (hbcol y))
  exact ⟨H,hH,hHn⟩

end AnchoredPositionOperators
end Percolation

 
namespace Percolation
universe u
variable {V : Type u}
section RawReversal
namespace HoldingWalk
variable {H : SimpleGraph V}


theorem vertices_snocHold {k : ℕ} {x y : V} (w : HoldingWalk H k x y) :
    w.snocHold.vertices = w.vertices ++ [y] := by
  induction w with
  | nil => rfl
  | hold w ih => simp only [snocHold,vertices,ih,List.cons_append]
  | step h w ih => simp only [snocHold,vertices,ih,List.cons_append]

theorem vertices_snocStep {k : ℕ} {x y z : V} (w : HoldingWalk H k x y) (h : H.Adj y z) :
    (w.snocStep h).vertices = w.vertices ++ [z] := by
  induction w with
  | nil => rfl
  | hold w ih => simp only [snocStep,vertices,ih,List.cons_append]
  | step h' w ih => simp only [snocStep,vertices,ih,List.cons_append]

theorem vertices_reverse {k : ℕ} {x y : V} (w : HoldingWalk H k x y) :
    w.reverse.vertices = w.vertices.reverse := by
  induction w with
  | nil => rfl
  | hold w ih => simp only [reverse,vertices_snocHold,vertices,ih,List.reverse_cons]
  | step h w ih => simp only [reverse,vertices_snocStep,vertices,ih,List.reverse_cons]

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

end LabeledNormalization
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
section ExactLabeledReversal
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

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
universe u
variable {V : Type u}
namespace HoldingWalk
variable {H : SimpleGraph V}



theorem position_mem_vertices {k : ℕ} {x y : V} (w : HoldingWalk H k x y) (i : ℕ) :
    w.position i ∈ w.vertices := by
  induction w generalizing i with
  | nil => simp only [position,vertices,List.mem_singleton]
  | hold w ih => cases i <;> simp only [position,vertices,List.mem_cons,true_or,ih,or_true]
  | step h w ih => cases i <;> simp only [position,vertices,List.mem_cons,true_or,ih,or_true]

theorem mem_vertices_iff_position {k : ℕ} {x y z : V} (w : HoldingWalk H k x y) :
    z ∈ w.vertices ↔ ∃ i : ℕ, i ≤ k ∧ w.position i = z := by
  induction w with
  | nil => simp only [vertices,List.mem_singleton,Nat.le_zero,exists_eq_left,position,eq_comm]
  | @hold k x y w ih =>
    constructor
    · intro hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact ⟨0,Nat.zero_le _,rfl⟩
      · obtain ⟨i,hi,he⟩ := ih.mp hz
        exact ⟨i+1,Nat.succ_le_succ hi,he⟩
    · rintro ⟨i,hi,he⟩
      cases i with
      | zero => exact List.mem_cons.mpr (Or.inl he.symm)
      | succ i => exact List.mem_cons.mpr (Or.inr (ih.mpr ⟨i,Nat.le_of_succ_le_succ hi,he⟩))
  | @step k x u y h w ih =>
    constructor
    · intro hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact ⟨0,Nat.zero_le _,rfl⟩
      · obtain ⟨i,hi,he⟩ := ih.mp hz
        exact ⟨i+1,Nat.succ_le_succ hi,he⟩
    · rintro ⟨i,hi,he⟩
      cases i with
      | zero => exact List.mem_cons.mpr (Or.inl he.symm)
      | succ i => exact List.mem_cons.mpr (Or.inr (ih.mpr ⟨i,Nat.le_of_succ_le_succ hi,he⟩))

end HoldingWalk
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
section IndependentRawCollisions
attribute [local instance] Classical.propDecidable Classical.decEq



theorem matrixCoeff_norm_le (A : Hilbert V →L[ℂ] Hilbert V) (x y : V) :
    ‖matrixCoeff A x y‖ ≤ ‖A‖ := by
  apply (lp.norm_apply_le_norm (by norm_num : (2:ENNReal) ≠ 0) (A (lp.single 2 y (1:ℂ))) x).trans
  simpa using A.le_opNorm (lp.single 2 y (1:ℂ))

end IndependentRawCollisions
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ActualCollisionUnion
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finite_nonnegative_event_union {α β : Type*} [Fintype α] [Fintype β]
    (μ : α → ℝ) (hμ : ∀ a, 0 ≤ μ a) (B : α → β → Prop) :
    (∑ a, if ∃ b, B a b then μ a else 0) ≤ ∑ b, ∑ a, if B a b then μ a else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a _
  by_cases hh : ∃ b, B a b
  · obtain ⟨b,hb⟩ := hh
    rw [ite_eq_left ⟨b,hb⟩]
    calc
      μ a = (if B a b then μ a else 0) := (ite_eq_left hb).symm
      _ ≤ ∑ b, if B a b then μ a else 0 :=
        Finset.single_le_sum (f := fun b => if B a b then μ a else 0)
          (fun b _ => by split_ifs; exact hμ a; exact le_rfl) (Finset.mem_univ b)
  · rw [ite_eq_right hh]
    exact Finset.sum_nonneg (fun b _ => by split_ifs; exact hμ a; exact le_rfl)



end ActualCollisionUnion
end Percolation


namespace Percolation
universe u
variable {V : Type u}
namespace HoldingWalk
variable {H : SimpleGraph V}



theorem position_fromPositions (k : ℕ) (f : Fin (k+1) → V)
    (h : ∀ i : Fin k, H.Adj (f i.castSucc) (f i.succ)) (i : ℕ) (hi : i ≤ k) :
    (fromPositions k f h).position i = f ⟨i,by omega⟩ := by
  induction k generalizing i with
  | zero =>
    obtain rfl : i = 0 := by omega
    rfl
  | succ k ih =>
    cases i with
    | zero => rfl
    | succ i =>
      exact ih (fun j => f j.succ) (fun j => h j.succ) i (by omega)

end HoldingWalk
end Percolation


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

 
namespace Percolation
universe u
variable {V : Type u}
section SuffixCollisionOperator

theorem operator_pow_norm_le (P : Hilbert V →L[ℂ] Hilbert V) (k : ℕ) : ‖P^k‖ ≤ ‖P‖^k := by
  cases k with
  | zero => simpa only [pow_zero,ContinuousLinearMap.one_def] using
      (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := Hilbert V))
  | succ k => exact norm_pow_le' P (Nat.succ_pos k)



end SuffixCollisionOperator
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ActualSuffixCollision
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I : Type*} [Fintype I]

 

theorem raw_anchored_position_expectation (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (ep j : I)
    (P H : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hH : ∀ x y, matrixCoeff H x y = (anchoredPositionKernel G hloc γ n hdiam ep j x y : ℂ))
    (L : ℕ) (x z : V) :
    (∑' mid : RawFrom (openSimpleGraph G Set.univ) L x,
      mid.2.mass (walkKernel G hloc a)*anchoredPositionKernel G hloc γ n hdiam ep j mid.1 z) =
      (matrixCoeff (P^L*H) x z).re := by
  change RawFrom.integral (walkKernel G hloc a) L x
    (fun y => anchoredPositionKernel G hloc γ n hdiam ep j y z) = _
  rw [raw_integral_operator G hloc a P hpos hP]
  simpa only [hH,Complex.ofReal_re] using ((hpos.pow L).mul_hasSum H x z).tsum_eq



end ActualSuffixCollision
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section GlobalAnchorDenominator
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I : Type*} [Fintype I]

 

theorem anchoredPositionKernel_global_denominator (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (ep j : I) (x z : V) :
    (∑ h : segmentAnchors G hloc γ n hdiam ep x,
      if h.val j = z then ((segmentAnchors G hloc γ n hdiam ep (γ ep)).card : ℝ)⁻¹ else 0) =
      anchoredPositionKernel G hloc γ n hdiam ep j x z := by
  rw [Finset.sum_coe_sort _ (fun h : I → V => if h j = z then
    ((segmentAnchors G hloc γ n hdiam ep (γ ep)).card : ℝ)⁻¹ else 0)]
  by_cases hx : x ∈ vertexOrbit G (γ ep)
  · unfold anchoredPositionKernel
    rw [segmentAnchors_card_on_orbit G hloc γ n hdiam ep x hx]
    apply Finset.sum_congr rfl
    intro h _
    simp only [eq_comm]
  · have hz := ((segmentAnchors_nonempty_iff G hloc γ n hdiam ep x).not.mpr hx)
    have he := Finset.not_nonempty_iff_eq_empty.mp hz
    simp only [anchoredPositionKernel,he,Finset.sum_empty]

end GlobalAnchorDenominator
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ActualAnchorPointTest
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I : Type*} [Fintype I]

theorem raw_anchor_position_identity (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (ep j : I)
    (L : ℕ) (y z : V) :
    (∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
      ∑' h : segmentAnchors G hloc γ n hdiam ep mid.1,
        if h.val j = z then mid.2.mass (walkKernel G hloc a)/
          (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) =
    (∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
      mid.2.mass (walkKernel G hloc a)*anchoredPositionKernel G hloc γ n hdiam ep j mid.1 z) := by
  apply tsum_congr
  intro mid
  rw [←anchoredPositionKernel_global_denominator G hloc γ n hdiam ep j mid.1 z,tsum_fintype,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  split_ifs <;> simp only [div_eq_mul_inv,mul_zero]

theorem raw_anchor_point_collision_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (ep j : I)
    (P H : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hH : ∀ x y, matrixCoeff H x y = (anchoredPositionKernel G hloc γ n hdiam ep j x y : ℂ))
    (C : ℝ) (hC : ‖H‖ ≤ C) (L : ℕ) (y z : V) :
    (∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
      ∑' h : segmentAnchors G hloc γ n hdiam ep mid.1,
        if h.val j = z then mid.2.mass (walkKernel G hloc a)/
          (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) ≤ C*‖P‖^L := by
  rw [raw_anchor_position_identity G hloc a γ n hdiam ep j L y z,
    raw_anchored_position_expectation G hloc a γ n hdiam ep j P H hpos hP hH L y z]
  apply (Complex.re_le_norm _).trans ((matrixCoeff_norm_le (P^L*H) y z).trans _)
  calc
    _ ≤ ‖P^L‖*‖H‖ := norm_mul_le _ _
    _ ≤ ‖P‖^L*C := mul_le_mul (operator_pow_norm_le P L) hC (norm_nonneg _) (pow_nonneg (norm_nonneg P) L)
    _ = _ := mul_comm _ _

end ActualAnchorPointTest
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
section DependentFiniteUnion
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finite_dependent_event_union {β δ : Type*} [Fintype β] [Fintype δ]
    {γ : β → Type*} [∀ b, Fintype (γ b)]
    (μ : (b : β) → γ b → ℝ) (hμ : ∀ b c, 0 ≤ μ b c)
    (B : (b : β) → γ b → δ → Prop) :
    (∑ b, ∑ c, if ∃ d, B b c d then μ b c else 0) ≤
      ∑ d, ∑ b, ∑ c, if B b c d then μ b c else 0 := by
  have hh := finite_nonnegative_event_union
    (fun ξ : Sigma γ => μ ξ.1 ξ.2)
    (fun ξ => hμ ξ.1 ξ.2)
    (fun ξ : Sigma γ => B ξ.1 ξ.2)
  simpa only [Fintype.sum_sigma] using hh

end DependentFiniteUnion
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ActualFinitePositionHits
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I ι S T : Type*} [Fintype I] [Fintype ι] [Fintype S] [Fintype T]

 

theorem raw_anchor_finite_collision_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G)
    (htr : RootTransport root weight Γ) (hw : ∀ r, 0 ≤ weight r) (hw1 : ∑ r, weight r = 1)
    (hcov : ∀ x, ∃ r, ∃ g ∈ Γ, g (root r) = x)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ r, 1 ≤ c*weight r)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (ep : I)
    (j : S → I) (z : T → V)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (L : ℕ) (y : V) :
    (∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
      ∑' h : segmentAnchors G hloc γ n hdiam ep mid.1,
        if ∃ st : S × T, h.val (j st.1) = z st.2 then mid.2.mass (walkKernel G hloc a)/
          (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) ≤
      (Fintype.card S : ℝ)*(Fintype.card T : ℝ)*Real.sqrt c*‖P‖^L := by
  let (v : V) : Finite ((openSimpleGraph G Set.univ).neighborSet v) := finite_openSimpleGraph_neighbors G hloc v
  let : Fintype (RawFrom (openSimpleGraph G Set.univ) L y) := Fintype.ofFinite _
  have hK (x y : V) : 0 ≤ walkKernel G hloc a x y := by
    simpa only [hP,Complex.ofReal_re] using (hpos x y).2
  simp only [tsum_fintype]
  have hu := finite_dependent_event_union
    (β := RawFrom (openSimpleGraph G Set.univ) L y)
    (γ := fun mid => segmentAnchors G hloc γ n hdiam ep mid.1)
    (δ := S × T)
    (fun mid _ => mid.2.mass (walkKernel G hloc a)/(segmentAnchors G hloc γ n hdiam ep (γ ep)).card)
    (fun mid _ => div_nonneg (mid.2.mass_nonneg _ hK) (Nat.cast_nonneg _))
    (fun _ h st => h.val (j st.1) = z st.2)
  apply hu.trans
  calc
    _ ≤ ∑ _st : S × T, Real.sqrt c*‖P‖^L := by
      apply Finset.sum_le_sum
      intro st _
      obtain ⟨H,hH,hHn⟩ := exists_anchoredPositionOperator_uniform G hloc root weight Γ hΓ htr hw hw1 hcov
        c hc hmin γ n hdiam ep (j st.1)
      simpa only [tsum_fintype] using raw_anchor_point_collision_bound G hloc a γ n hdiam ep (j st.1)
        P H hpos hP hH (Real.sqrt c) hHn L y (z st.2)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Nat.cast_mul,nsmul_eq_mul]; ring

end ActualFinitePositionHits
end Percolation


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
section QuantitativeSelectionMass
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

theorem finite_weighted_success_lower {α : Type*} [Fintype α]
    (μ : α → ℝ) (hμ : ∑ a, μ a = 1) (B : α → Prop) [DecidablePred B] (ε : ℝ)
    (hB : (∑ a, if B a then μ a else 0) ≤ ε) :
    1-ε ≤ ∑ a, if ¬B a then μ a else 0 := by
  have he : (∑ a, if ¬B a then μ a else 0) + (∑ a, if B a then μ a else 0) = 1 := by
    rw [←Finset.sum_add_distrib,←hμ]
    apply Finset.sum_congr rfl
    intro a _
    by_cases h : B a <;> simp only [h,not_true_eq_false,not_false_eq_true,ite_true,ite_false,zero_add,add_zero]
  linarith



end QuantitativeSelectionMass
end Percolation


namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section SpineMarginal
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

theorem labelFromCode_anchor_event (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) (B : (I → V) → (I → V) → Prop)
    (s : segmentAnchors G hloc γ n hdiam center x)
    (mid : RawFrom (openSimpleGraph G Set.univ) L (s.val ep))
    (h : segmentAnchors G hloc γ n hdiam ep mid.1)
    (tails : RawFrom (openSimpleGraph G Set.univ) m (s.val neg) ×
      RawFrom (openSimpleGraph G Set.univ) m (h.val neg)) :
    B (labelFromCode G hloc γ n hdiam center ep neg L m x ⟨s,mid,h,tails⟩).1.first
      (labelFromCode G hloc γ n hdiam center ep neg L m x ⟨s,mid,h,tails⟩).1.last ↔ B s.val h.val := by
  rcases s with ⟨s,hs⟩
  rcases mid with ⟨z,mid⟩
  rcases h with ⟨h,hh⟩
  obtain ⟨_,hhz⟩ := (mem_segmentAnchors G hloc γ n hdiam ep z h).mp hh
  subst z
  rfl

 
theorem rooted_label_anchor_event_marginal (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) (B : (I → V) → (I → V) → Prop)
    [∀ s h, Decidable (B s h)] :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      if B ξ.1.first ξ.1.last then ξ.1.mass (walkKernel G hloc a) else 0) =
    ∑' s : segmentAnchors G hloc γ n hdiam center x,
      ∑' mid : RawFrom (openSimpleGraph G Set.univ) L (s.val ep),
        ∑' h : segmentAnchors G hloc γ n hdiam ep mid.1,
          if B s.val h.val then mid.2.mass (walkKernel G hloc a) else 0 := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let (k : ℕ) (z : V) : Fintype (RawFrom (openSimpleGraph G Set.univ) k z) := Fintype.ofFinite _
  let := finite_rootedEscapeLabels G hloc γ n hdiam center ep neg L m x
  let R := rootedLabelEquiv G hloc γ n hdiam center ep neg L m x
  rw [←R.symm.tsum_eq]
  simp only [R,rootedLabelEquiv,Equiv.coe_fn_symm_mk,labelFromCode_mass]
  unfold RootedLabelCode at *
  simp only [tsum_fintype,Fintype.sum_sigma,labelFromCode_anchor_event]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro mid _
  apply Finset.sum_congr rfl
  intro h _
  by_cases hb : B s.val h.val
  · simp only [hb,ite_true,Fintype.sum_prod_type,mul_assoc,←Finset.mul_sum,←Finset.sum_mul]
    have hl := rawFrom_probability_sum G hloc a m (s.val neg)
    have hr := rawFrom_probability_sum G hloc a m (h.val neg)
    simp only [tsum_fintype] at hl hr
    rw [hl,hr]
    ring
  · simp only [hb,ite_false,Finset.sum_const_zero]

end SpineMarginal
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section EndpointMarginal
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

 
theorem rooted_label_endpoint_marginal (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) (S : Finset V) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      if ξ.1.last center ∈ S then escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1 else 0) =
    (∑' s : segmentAnchors G hloc γ n hdiam center x,
      ∑' mid : RawFrom (openSimpleGraph G Set.univ) L (s.val ep),
        ∑' h : segmentAnchors G hloc γ n hdiam ep mid.1,
          if h.val center ∈ S then mid.2.mass (walkKernel G hloc a)/
            (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) /
      (((segmentAnchors G hloc γ n hdiam center (γ center)).card : ℝ)*
        segmentReturnMass G hloc a γ ep L (γ ep)) := by
  simp only [escapeLabelProbability,tsum_indicator_div,tsum_div_const]
  rw [rooted_label_anchor_event_marginal G hloc a γ n hdiam center ep neg L m x (fun _ h => h center ∈ S)]
  ring

end EndpointMarginal
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section ActualEndpointSeparation
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I] {ι : Type*} [Fintype ι]

 

theorem rooted_label_endpoint_hit_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G)
    (htr : RootTransport root weight Γ) (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
    (hcov : ∀ x, ∃ r, ∃ g ∈ Γ, g (root r) = x)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ r, 1 ≤ c*weight r)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (center ep neg : I)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re)
    (m L : ℕ) (x : V) (hx : x ∈ vertexOrbit G (γ center))
    (S : Finset V) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      if ξ.1.last center ∈ S then escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1 else 0) ≤
      2*c*(S.card:ℝ)*Real.sqrt c*‖P‖^L := by
  rw [rooted_label_endpoint_marginal G hloc a γ n hdiam center ep neg L m x S]
  have hN : 0 < ((segmentAnchors G hloc γ n hdiam center (γ center)).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ((segmentAnchors_nonempty_iff G hloc γ n hdiam center (γ center)).mpr
      ⟨Equiv.refl V,Equiv.refl E,isAut_refl G,rfl⟩)
  have hq := segmentReturnMass_uniform_lower G hloc a root weight Γ hΓ htr hcov hw hw1 c hc hmin
    P hpos hsym hP hdiag γ ep L
  have hqp : 0 < segmentReturnMass G hloc a γ ep L (γ ep) :=
    (one_div_pos.mpr (mul_pos (by norm_num) hc)).trans_le hq
  apply (div_le_iff₀ (mul_pos hN hqp)).mpr
  have hb (s : segmentAnchors G hloc γ n hdiam center x) :
      (∑' mid : RawFrom (openSimpleGraph G Set.univ) L (s.val ep),
        ∑' h : segmentAnchors G hloc γ n hdiam ep mid.1,
          if h.val center ∈ S then mid.2.mass (walkKernel G hloc a)/
            (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) ≤
      (S.card:ℝ)*Real.sqrt c*‖P‖^L := by
    have hh := raw_anchor_finite_collision_bound G hloc a root weight Γ hΓ htr (fun r => (hw r).le)
      hw1 hcov c hc.le hmin γ n hdiam ep (fun _ : PUnit.{1} => center) (fun z : S => z.val)
      P hpos hP L (s.val ep)
    simpa [Subtype.exists] using hh
  have hu := Finset.sum_le_sum (s := Finset.univ) (fun s _ => hb s)
  simp only [tsum_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul] at hu ⊢
  rw [segmentAnchors_card_on_orbit G hloc γ n hdiam center x hx] at hu
  apply hu.trans
  have he : 1 ≤ 2*c*segmentReturnMass G hloc a γ ep L (γ ep) := by
    have hh := (div_le_iff₀ (by positivity : 0 < 2*c)).mp hq
    nlinarith
  have hp : 0 ≤ ((segmentAnchors G hloc γ n hdiam center (γ center)).card : ℝ)*
      (S.card:ℝ)*Real.sqrt c*‖P‖^L := by positivity
  nlinarith [mul_le_mul_of_nonneg_left he hp]

end ActualEndpointSeparation
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section EndpointBallBound
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I] {ι : Type*} [Fintype ι]

 
theorem rooted_label_endpoint_ball_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G)
    (htr : RootTransport root weight Γ) (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
    (hcov : ∀ x, ∃ r, ∃ g ∈ Γ, g (root r) = x)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ r, 1 ≤ c*weight r)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (center ep neg : I)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re)
    (m L : ℕ) (x : V) (hx : x ∈ vertexOrbit G (γ center))
    (d : ℕ) (hd : ∀ z, degree G z ≤ d) (r : ℕ) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      if ξ.1.last center ∈ reachBall G x r then escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1 else 0) ≤
      2*c*(((d+1)^r:ℕ):ℝ)*Real.sqrt c*‖P‖^L := by
  have hh := rooted_label_endpoint_hit_bound G hloc a root weight Γ hΓ htr hw hw1 hcov c hc hmin
    γ n hdiam center ep neg P hpos hsym hP hdiag m L x hx (finite_reachBall hloc x r).toFinset
  have hb : ((finite_reachBall hloc x r).toFinset.card : ℝ) ≤ (((d+1)^r:ℕ):ℝ) := by
    exact_mod_cast (by
      simpa only [←Set.ncard_eq_toFinset_card] using reachBall_ncard_le_pow G hloc d hd x r)
  calc
    _ ≤ 2*c*((finite_reachBall hloc x r).toFinset.card:ℝ)*Real.sqrt c*‖P‖^L := by
      simpa only [Set.Finite.mem_toFinset] using hh
    _ ≤ _ := by gcongr

end EndpointBallBound
end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Escape_PathSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Selection of geometrically separated paths from labelled escape events. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section EscapeGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

namespace HoldingWalk
variable {H : SimpleGraph V}

theorem mem_vertices_append {k l : ℕ} {x y z b : V}
    (w : HoldingWalk H k x y) (v : HoldingWalk H l y z) :
    b ∈ (w.append v).vertices ↔ b ∈ w.vertices ∨ b ∈ v.vertices := by
  induction w with
  | nil x =>
    have hx : x ∈ v.vertices := by simpa using v.position_mem_vertices 0
    simp only [append, vertices, List.mem_singleton]
    exact ⟨fun h => Or.inr h, fun h => h.elim (fun he => he ▸ hx) id⟩
  | hold w ih => simp only [append, vertices, List.mem_cons, ih, or_assoc]
  | step h w ih => simp only [append, vertices, List.mem_cons, ih, or_assoc]

theorem mem_vertices_fromPositions (k : ℕ) (f : Fin (k+1) → V)
    (h : ∀ i : Fin k, H.Adj (f i.castSucc) (f i.succ)) (b : V) :
    b ∈ (fromPositions k f h).vertices ↔ ∃ i, f i = b := by
  rw [mem_vertices_iff_position]
  constructor
  · rintro ⟨i, hi, he⟩
    exact ⟨⟨i,by omega⟩, (position_fromPositions k f h i hi).symm.trans he⟩
  · rintro ⟨i,hi⟩
    exact ⟨i.val,by omega,(position_fromPositions k f h i.val (by omega)).trans hi⟩

end HoldingWalk


theorem positiveStem_vertices (H : SimpleGraph V) (J : ℕ) (s : Fin (J+J+1) → V)
    (hs : ∀ i : Fin (J+J), H.Adj (s i.castSucc) (s i.succ)) (z : V) :
    z ∈ (positiveStem H J s hs).vertices ↔ ∃ i : Fin (J+1), s ⟨J+i.val,by omega⟩ = z := by
  exact HoldingWalk.mem_vertices_fromPositions J _ _ z

theorem negativeStem_vertices (H : SimpleGraph V) (J : ℕ) (s : Fin (J+J+1) → V)
    (hs : ∀ i : Fin (J+J), H.Adj (s i.castSucc) (s i.succ)) (z : V) :
    z ∈ (negativeStem H J s hs).vertices ↔ ∃ i : Fin (J+1), s ⟨i.val,by omega⟩ = z := by
  let w := HoldingWalk.fromPositions J (fun i : Fin (J+1) => s ⟨i.val,by omega⟩)
    (fun i : Fin J => hs ⟨i.val,by omega⟩)
  have he : z ∈ w.reverse.vertices ↔ z ∈ w.vertices := by
    rw [HoldingWalk.vertices_reverse, List.mem_reverse]
  exact he.trans (HoldingWalk.mem_vertices_fromPositions J _ _ z)


theorem segmentOrbit_injective {I : Type*} (G : BondGraph V E) (γ s : I → V)
    (hγ : Function.Injective γ) (hs : s ∈ segmentOrbit G γ) : Function.Injective s := by
  obtain ⟨a,b,hab,rfl⟩ := hs
  exact a.injective.comp hγ

 

theorem labelLeftEscape_raw_intersection (G : BondGraph V E) (J L m : ℕ)
    (γ : Fin (J+J+1) → V) (hinj : Function.Injective γ)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m)
    (hgood : ¬labelFirstEscapeCollision G γ (Fin.last (J+J)) 0 J L m
      (segmentPositiveIndex J) (segmentNegativeIndex J) (segmentPositiveIndex J) ξ)
    (z : V) (hz : z ∈ (labelLeftEscape G J L m γ hγ ξ).vertices)
    (hr : z ∈ (escapeLabelRaw G J L m γ hγ ξ).vertices) :
    z = ξ.first (segmentCenter J) := by
  have hfirst := segmentOrbit_injective G γ ξ.first hinj ξ.first_mem
  have hfail := hgood
  unfold labelFirstEscapeCollision firstEscapeCollision at hfail
  have hraw : (∃ i : Fin (J+1), ξ.first (segmentPositiveIndex J i) = z) ∨
      z ∈ ξ.middle.vertices ∨ (∃ i : Fin (J+1), ξ.last (segmentPositiveIndex J i) = z) := by
    simpa only [escapeLabelRaw, HoldingWalk.mem_vertices_append,
      HoldingWalk.vertices_reverse, List.mem_reverse, positiveStem_vertices,
      segmentPositiveIndex] using hr
  have hleft : (∃ i : Fin (J+1), ξ.first (segmentNegativeIndex J i) = z) ∨
      z ∈ ξ.leftTail.2.vertices := by
    simpa only [labelLeftEscape, HoldingWalk.mem_vertices_append,
      negativeStem_vertices, segmentNegativeIndex] using hz
  rcases hleft with ⟨i,hi⟩ | ht
  · rcases hraw with ⟨j,hj⟩ | hm | ⟨j,hj⟩
    · have he := congrArg Fin.val (hfirst (hi.trans hj.symm))
      change i.val = J+j.val at he
      have hiJ : i.val = J := by omega
      rw [←hi]
      congr 1
      apply Fin.ext
      exact hiJ
    · exact False.elim (hfail (Or.inl (Or.inl (Or.inr ⟨i,by simpa only [hi] using hm⟩))))
    · exact False.elim (hfail (Or.inr (Or.inl ⟨(j,i),hj.trans hi.symm⟩)))
  · rcases hraw with ⟨i,hi⟩ | hm | ⟨i,hi⟩
    · exact False.elim (hfail (Or.inl (Or.inl (Or.inl ⟨i,by simpa only [hi] using ht⟩))))
    · exact False.elim (hfail (Or.inl (Or.inr ⟨z,ht,hm⟩)))
    · obtain ⟨l,hl,he⟩ := ξ.leftTail.2.mem_vertices_iff_position.mp ht
      exact False.elim (hfail (Or.inr (Or.inr ⟨(⟨l,by omega⟩,i),he.trans hi.symm⟩)))

 
theorem labelRaw_reverse_vertices (G : BondGraph V E) (J L m : ℕ)
    (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m) (z : V) :
    z ∈ (escapeLabelRaw G J L m γ hγ ξ.reverse).vertices ↔
      z ∈ (escapeLabelRaw G J L m γ hγ ξ).vertices := by
  simp only [escapeLabelRaw, HoldingWalk.mem_vertices_append,
    HoldingWalk.vertices_reverse, List.mem_reverse, EscapeLabel.reverse]
  tauto

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem interior_mem_raw (w : RawCorridor G k) {z : V} (hz : z ∈ w.interior) :
    z ∈ w.2.2.vertices := by
  have hp : z ∈ w.path.support := List.mem_toFinset.mp (Finset.mem_sdiff.mp hz).1
  exact w.2.2.erase_support.subset hp


end RawCorridor



theorem mem_spineVertices (G : BondGraph V E) (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m) (z : V) :
    z ∈ spineVertices G J L ξ.first ⟨ξ.last (Fin.last (J+J)),ξ.middle⟩ ξ.last ↔
      z ∈ (escapeLabelRaw G J L m γ hγ ξ).vertices := by
  simp only [spineVertices, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
    true_and, Function.comp_apply, List.mem_toFinset, escapeLabelRaw,
    HoldingWalk.mem_vertices_append, HoldingWalk.vertices_reverse, List.mem_reverse,
    positiveStem_vertices, segmentPositiveIndex]
  tauto

theorem labelCorridor_neighborhood_subset (G : BondGraph V E) (hloc : LocallyFinite G)
    (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m) :
    (labelCorridor G J L m γ hγ ξ).neighborhood hloc ⊆
      spineNeighborhood G hloc J L ξ.first ⟨ξ.last (Fin.last (J+J)),ξ.middle⟩ ξ.last := by
  have hi : (labelCorridor G J L m γ hγ ξ).interior ⊆
      spineVertices G J L ξ.first ⟨ξ.last (Fin.last (J+J)),ξ.middle⟩ ξ.last := by
    intro z hz
    exact (mem_spineVertices G J L m γ hγ ξ z).mpr
      ((labelCorridor G J L m γ hγ ξ).interior_mem_raw hz)
  exact Finset.union_subset_union hi (Finset.biUnion_subset_biUnion_of_subset_left _ hi)

theorem neighborhood_card_le (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (W : Finset V) :
    (W ∪ W.biUnion (neighbors G hloc)).card ≤ (d+1)*W.card := by
  have hb : (W.biUnion (neighbors G hloc)).card ≤ W.card*d :=
    Finset.card_biUnion_le_card_mul _ _ _
      (fun x _ => (neighbors_card_le_degree G hloc x).trans (hd x))
  calc
    _ ≤ W.card + (W.biUnion (neighbors G hloc)).card := Finset.card_union_le _ _
    _ ≤ W.card + W.card*d := Nat.add_le_add_left hb _
    _ = _ := by ring

theorem spineVertices_card_le (G : BondGraph V E) (J L : ℕ)
    (s : Fin (J+J+1) → V)
    (mid : RawFrom (openSimpleGraph G Set.univ) L (s (Fin.last (J+J))))
    (h : Fin (J+J+1) → V) :
    (spineVertices G J L s mid h).card ≤ ((J+L)+J)+3 := by
  have h₁ : (Finset.univ.image (s ∘ segmentPositiveIndex J)).card ≤ J+1 :=
    (Finset.card_image_le).trans (by simp)
  have h₂ : mid.2.vertices.toFinset.card ≤ L+1 :=
    (List.toFinset_card_le _).trans (le_of_eq mid.2.length_vertices)
  have h₃ : (Finset.univ.image (h ∘ segmentPositiveIndex J)).card ≤ J+1 :=
    (Finset.card_image_le).trans (by simp)
  have hauto := (Finset.card_union_le
    (Finset.univ.image (s ∘ segmentPositiveIndex J)) mid.2.vertices.toFinset)
  have hauto' := (Finset.card_union_le
    (Finset.univ.image (s ∘ segmentPositiveIndex J) ∪ mid.2.vertices.toFinset)
    (Finset.univ.image (h ∘ segmentPositiveIndex J)))
  unfold spineVertices
  omega

theorem spineNeighborhood_card_le (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (J L : ℕ)
    (s : Fin (J+J+1) → V)
    (mid : RawFrom (openSimpleGraph G Set.univ) L (s (Fin.last (J+J))))
    (h : Fin (J+J+1) → V) :
    ((spineNeighborhood G hloc J L s mid h).card : ℝ) ≤
      (3*(d:ℝ)+3)*((((J+L)+J):ℕ)+1) := by
  have hn := neighborhood_card_le G hloc d hd (spineVertices G J L s mid h)
  have hs := spineVertices_card_le G J L s mid h
  have hb : (spineNeighborhood G hloc J L s mid h).card ≤ (d+1)*(((J+L)+J)+3) :=
    hn.trans (Nat.mul_le_mul_left _ hs)
  have hb' : ((spineNeighborhood G hloc J L s mid h).card : ℝ) ≤
      ((d:ℝ)+1)*((((J+L)+J):ℕ)+3) := by exact_mod_cast hb
  have hk : (0:ℝ) ≤ (((J+L)+J):ℕ) := Nat.cast_nonneg _
  nlinarith [show (0:ℝ) ≤ (d:ℝ) from Nat.cast_nonneg d]

 

theorem selected_of_good_label (G : BondGraph V E) (hloc : LocallyFinite G)
    (J L m : ℕ) (γ : Fin (J+J+1) → V) (hinj : Function.Injective γ)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m) (p : unitInterval) (t : ℝ)
    (hleft : ¬labelFirstEscapeCollision G γ (Fin.last (J+J)) 0 J L m
      (segmentPositiveIndex J) (segmentNegativeIndex J) (segmentPositiveIndex J) ξ)
    (hright : ¬labelFirstEscapeCollision G γ (Fin.last (J+J)) 0 J L m
      (segmentPositiveIndex J) (segmentNegativeIndex J) (segmentPositiveIndex J) ξ.reverse)
    (hdist : ξ.last (segmentCenter J) ∉ reachBall G (ξ.first (segmentCenter J)) 2)
    (hpot : ¬labelPotentialFailure G p γ (Fin.last (J+J)) 0 L m
      (spineNeighborhood G hloc J L) t ξ) :
    (labelCorridor G J L m γ hγ ξ).Selected hloc p (J+m) t := by
  let w := labelCorridor G J L m γ hγ ξ
  have hlength : 3 ≤ w.path.length := by
    by_contra h
    have hx : w.endpoint ∈ reachBall G w.base w.path.length := by
      simpa only [Nat.zero_add] using walk_mem_reachBall G Set.univ w.path 0 rfl
    exact hdist (reachBall_mono_local G w.base (by omega : w.path.length ≤ 2) hx)
  have hn := labelCorridor_neighborhood_subset G hloc J L m γ hγ ξ
  have hp := not_or.mp hpot
  have hp₁ : (∑ b ∈ w.neighborhood hloc, twoPoint G p ξ.leftTail.1 b) ≤ t := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg hn (fun b _ _ => twoPoint_nonneg G p _ b))
    exact le_of_not_gt hp.1
  have hp₂ : (∑ b ∈ w.neighborhood hloc, twoPoint G p ξ.rightTail.1 b) ≤ t := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg hn (fun b _ _ => twoPoint_nonneg G p _ b))
    exact le_of_not_gt hp.2
  refine ⟨hlength, ?_, ?_⟩
  · let e := labelLeftEscape G J L m γ hγ ξ
    refine ⟨ξ.leftTail.1, e.erase, e.erase_isPath, ?_, ?_, hp₁⟩
    · exact e.erase_length.trans (by omega)
    · intro z hz hzI
      have hr := w.interior_mem_raw hzI
      have he := labelLeftEscape_raw_intersection G J L m γ hinj hγ ξ hleft z
        (e.erase_support.subset hz) hr
      change z = w.base at he
      apply w.base_not_interior
      simpa only [he] using hzI
  · let e := labelLeftEscape G J L m γ hγ ξ.reverse
    refine ⟨ξ.rightTail.1, e.erase, e.erase_isPath, ?_, ?_, hp₂⟩
    · exact e.erase_length.trans (by omega)
    · intro z hz hzI
      have hr := w.interior_mem_raw hzI
      have he := labelLeftEscape_raw_intersection G J L m γ hinj hγ ξ.reverse hright z
        (e.erase_support.subset hz) ((labelRaw_reverse_vertices G J L m γ hγ ξ z).mpr hr)
      change z = w.endpoint at he
      apply w.endpoint_not_interior
      simpa only [he] using hzI

end EscapeGeometry
end Percolation

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SelectedLabelMass
attribute [local instance] Classical.propDecidable Classical.decEq
variable {ι : Type*} [Fintype ι]

 

theorem rooted_selected_label_mass_lower_oai [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G))
    (hcov : ∀ x, ∃ r, ∃ g ∈ vertexAut G, g (root r) = x)
    (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ r, 1 ≤ c*weight r)
    (P A : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re)
    (p : unitInterval) (hA : HasKernel G p A)
    (J L m : ℕ) (γ : Fin (J+J+1) → V) (hinj : Function.Injective γ)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) (J+J))
    (x : V) (hx : x ∈ vertexOrbit G (γ (segmentCenter J))) (hρ : ‖P‖ < 1)
    (hsep : ∀ s ∈ segmentOrbit G γ,
      (∀ i, J ≤ (openSimpleGraph G Set.univ).dist (s 0) (s (segmentPositiveIndex J i))) ∧
      (∀ i, J ≤ (openSimpleGraph G Set.univ).dist (s (Fin.last (J+J))) (s (segmentNegativeIndex J i))) ∧
      2*J ≤ (openSimpleGraph G Set.univ).dist (s 0) (s (Fin.last (J+J))))
    (d : ℕ) (hd : ∀ z, degree G z ≤ d) (t : ℝ) (ht : 0 < t) :
    1 - (4*c*(earlyCollisionCost ‖P‖ J + suffixCollisionCost ‖P‖ c J*‖P‖^L) +
      2*((3*(d:ℝ)+3)*((((J+L)+J):ℕ)+1)*Real.sqrt c*‖P‖^m)/t +
      2*c*(((d+1)^2:ℕ):ℝ)*Real.sqrt c*‖P‖^L) ≤
    ∑' ξ : {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x},
      if (labelCorridor G J L m γ hγ ξ.1).Selected hloc p (J+m) t then
        escapeLabelProbability G hloc a γ (J+J) hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m ξ.1 else 0 := by
  let F := spineNeighborhood G hloc J L
  let μ := fun ξ : {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x} =>
    escapeLabelProbability G hloc a γ (J+J) hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m ξ.1
  let B₁ := fun ξ : {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x} =>
    (labelFirstEscapeCollision G γ (Fin.last (J+J)) 0 J L m
        (segmentPositiveIndex J) (segmentNegativeIndex J) (segmentPositiveIndex J) ξ.1 ∨
      labelFirstEscapeCollision G γ (Fin.last (J+J)) 0 J L m
        (segmentPositiveIndex J) (segmentNegativeIndex J) (segmentPositiveIndex J) ξ.1.reverse) ∨
      labelPotentialFailure G p γ (Fin.last (J+J)) 0 L m F t ξ.1
  let B₂ := fun ξ : {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x} =>
    ξ.1.last (segmentCenter J) ∈ reachBall G x 2
  have hb := rooted_label_collision_potential_failure_bound G hloc a root weight htr hcov hw hw1 c hc hmin
    P A hpos hsym hP hdiag p hA γ (J+J) hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m x hx hρ
    J (segmentPositiveIndex J) (segmentNegativeIndex J) (segmentPositiveIndex J) hsep F
    ((3*(d:ℝ)+3)*((((J+L)+J):ℕ)+1)) (spineNeighborhood_card_le G hloc d hd J L) t ht
  have he := rooted_label_endpoint_ball_bound G hloc a root weight (vertexAut G) (Set.Subset.refl _)
    htr hw hw1 hcov c hc hmin γ (J+J) hdiam (segmentCenter J) (Fin.last (J+J)) 0
    P hpos hsym hP hdiag m L x hx d hd 2
  have hs := (rooted_label_probability_hasSum G hloc a root weight (vertexAut G) (Set.Subset.refl _)
    htr hcov hw hw1 c hc hmin P hpos hsym hP hdiag γ (J+J) hdiam
    (segmentCenter J) (Fin.last (J+J)) 0 L m x hx).tsum_eq
  have hK (x y : V) : 0 ≤ walkKernel G hloc a x y := by
    simpa only [hP,Complex.ofReal_re] using (hpos x y).2
  let := finite_rootedEscapeLabels G hloc γ (J+J) hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m x
  let := Fintype.ofFinite {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x}
  have hμ (ξ) : 0 ≤ μ ξ := escapeLabelProbability_nonneg G hloc a hK γ (J+J) hdiam
    (segmentCenter J) (Fin.last (J+J)) 0 L m ξ.1
  simp only [tsum_fintype] at hs hb he ⊢
  have hu := (finite_weighted_event_or μ hμ B₁ B₂).trans (add_le_add hb he)
  have hl := finite_weighted_success_lower μ hs (fun ξ => B₁ ξ ∨ B₂ ξ) _ hu
  apply hl.trans
  apply Finset.sum_le_sum
  intro ξ _
  by_cases h : B₁ ξ ∨ B₂ ξ
  · simp only [h,not_true_eq_false,ite_false]
    split_ifs <;> first | exact hμ ξ | rfl
  · have h₁ := not_or.mp (not_or.mp h).1
    have h₂ := not_or.mp h₁.1
    have hdist : ξ.1.last (segmentCenter J) ∉ reachBall G (ξ.1.first (segmentCenter J)) 2 := by
      simpa only [ξ.2] using (not_or.mp h).2
    have hsel := selected_of_good_label G hloc J L m γ hinj hγ ξ.1 p t h₂.1 h₂.2 hdist h₁.2
    simp only [h,not_false_eq_true,hsel,ite_true]
    exact le_rfl

end SelectedLabelMass
end Percolation

end OAI
end

theorem solution.{u, v, u_1} : type_of% @OAI.Percolation.rooted_selected_label_mass_lower_oai.{u, v, u_1} := @OAI.Percolation.rooted_selected_label_mass_lower_oai.{u, v, u_1}
