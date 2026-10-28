-- Prove2me | solution 1 for OAI.Percolation.conditional_first_escape_collision_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T00:57:51.35395+00:00
-- url     : https://prove2.me/submissions/4ada120a-2269-44cd-9b55-09d1843e1a9e

import Mathlib
import Definitions.Def_CayleyPercolation
import Definitions.Def_OAIQ040C002

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



end UniformLabeledLaw
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AuxiliaryTailMarkov
attribute [local instance] Classical.propDecidable Classical.decEq



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
section RawTimeMarginals
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem raw_position_integral (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (i m : ℕ) (him : i ≤ m) (x : V) (f : V → ℝ) :
    (∑' w : RawFrom (openSimpleGraph G Set.univ) m x,
      w.2.mass (walkKernel G hloc a) * f (w.2.position i)) =
      RawFrom.integral (H := openSimpleGraph G Set.univ) (walkKernel G hloc a) i x f := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  induction i generalizing m x with
  | zero =>
    simp only [HoldingWalk.position_zero,tsum_mul_right,rawFrom_probability_sum G hloc a,one_mul,RawFrom.integral_zero]
  | succ i ih =>
    cases m with
    | zero => omega
    | succ m =>
      rw [←(RawFrom.succEquiv m x).symm.tsum_eq,RawFrom.integral_succ]
      let (z : V) := Fintype.ofFinite (RawFrom (openSimpleGraph G Set.univ) m z)
      let := Fintype.ofFinite ((openSimpleGraph G Set.univ).neighborSet x)
      have hh (z : V) := ih m (Nat.le_of_succ_le_succ him) z
      simp only [tsum_fintype,Fintype.sum_sum_type,Fintype.sum_sigma,RawFrom.succEquiv,
        Equiv.symm_mk,Equiv.coe_fn_mk,HoldingWalk.mass,HoldingWalk.position,mul_assoc]
      simp only [tsum_fintype] at hh
      simp only [←Finset.mul_sum,hh]

theorem raw_position_probability (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (i m : ℕ) (him : i ≤ m) (x z : V) :
    (∑' w : RawFrom (openSimpleGraph G Set.univ) m x,
      if w.2.position i = z then w.2.mass (walkKernel G hloc a) else 0) =
      (matrixCoeff (P^i) x z).re := by
  have hh := raw_position_integral G hloc a i m him x (fun y => if y = z then (1:ℝ) else 0)
  simp only [mul_ite,mul_one,mul_zero] at hh
  rw [hh,raw_integral_operator G hloc a P hpos hP]
  simp only [mul_ite,mul_one,mul_zero,tsum_ite_eq]

end RawTimeMarginals
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section IndependentRawCollisions
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem raw_two_time_collision (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (i m j n : ℕ) (him : i ≤ m) (hjn : j ≤ n) (x y : V) :
    (∑' w : RawFrom (openSimpleGraph G Set.univ) m x × RawFrom (openSimpleGraph G Set.univ) n y,
      if w.1.2.position i = w.2.2.position j then
        w.1.2.mass (walkKernel G hloc a)*w.2.2.mass (walkKernel G hloc a) else 0) =
      (matrixCoeff (P^(i+j)) x y).re := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let := Fintype.ofFinite (RawFrom (openSimpleGraph G Set.univ) m x)
  let := Fintype.ofFinite (RawFrom (openSimpleGraph G Set.univ) n y)
  have hi (w : RawFrom (openSimpleGraph G Set.univ) m x) :
      (∑' v : RawFrom (openSimpleGraph G Set.univ) n y,
        if w.2.position i = v.2.position j then w.2.mass (walkKernel G hloc a)*v.2.mass (walkKernel G hloc a) else 0) =
      w.2.mass (walkKernel G hloc a)*(matrixCoeff (P^j) y (w.2.position i)).re := by
    rw [← raw_position_probability G hloc a P hpos hP j n hjn y (w.2.position i),←tsum_mul_left]
    apply tsum_congr
    intro v
    by_cases hh : w.2.position i = v.2.position j
    · simp only [ite_eq_left hh,ite_eq_left hh.symm]
    · simp only [ite_eq_right hh,ite_eq_right (Ne.symm hh),mul_zero]
  rw [(summable_of_hasFiniteSupport (Set.toFinite _)).tsum_prod]
  simp only [hi]
  rw [raw_position_integral G hloc a i m him x (fun z => (matrixCoeff (P^j) y z).re),raw_integral_operator G hloc a P hpos hP]
  simp only [matrixCoeff_real_symm (P^j) (hsym.pow j) y]
  rw [((hpos.pow i).mul_hasSum (P^j) x y).tsum_eq,←pow_add]

theorem matrixCoeff_norm_le (A : Hilbert V →L[ℂ] Hilbert V) (x y : V) :
    ‖matrixCoeff A x y‖ ≤ ‖A‖ := by
  apply (lp.norm_apply_le_norm (by norm_num : (2:ENNReal) ≠ 0) (A (lp.single 2 y (1:ℂ))) x).trans
  simpa using A.le_opNorm (lp.single 2 y (1:ℂ))

theorem matrixCoeff_power_le (P : Hilbert V →L[ℂ] Hilbert V) (k : ℕ) (x y : V) :
    (matrixCoeff (P^k) x y).re ≤ ‖P‖^k := by
  have hn (k : ℕ) : ‖P^k‖ ≤ ‖P‖^k := by
    induction k with
    | zero => simpa only [pow_zero,ContinuousLinearMap.one_def] using
        (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := Hilbert V))
    | succ k ih =>
      rw [pow_succ,pow_succ]
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (norm_nonneg P))
  exact (Complex.re_le_norm _).trans ((matrixCoeff_norm_le (P^k) x y).trans (hn k))

end IndependentRawCollisions
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FinitePropagation
attribute [local instance] Classical.propDecidable Classical.decEq

theorem reachBall_exists_short_walk (G : BondGraph V E) (x : V) (k : ℕ) {y : V}
    (hy : y ∈ reachBall G x k) :
    ∃ q : (openSimpleGraph G Set.univ).Walk x y, q.length ≤ k := by
  induction k generalizing y with
  | zero =>
    have he : y = x := hy
    subst y
    exact ⟨.nil,by simp⟩
  | succ k ih =>
    rcases hy with hy | hy
    · obtain ⟨q,hq⟩ := ih hy
      exact ⟨q,hq.trans (Nat.le_succ _)⟩
    · simp only [Set.mem_iUnion,Set.mem_ofPred_eq] at hy
      obtain ⟨z,hz,hzy⟩ := hy
      obtain ⟨q,hq⟩ := ih hz
      by_cases he : z = y
      · subst z
        exact ⟨q,hq.trans (Nat.le_succ _)⟩
      · let h : (openSimpleGraph G Set.univ).Adj z y :=
          (openSimpleGraph_univ_adj G z y).mpr ⟨he,hzy⟩
        refine ⟨q.append (.cons h .nil),?_⟩
        simpa only [SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_cons,
          SimpleGraph.Walk.length_nil,zero_add] using Nat.add_le_add_right hq 1

theorem dist_le_of_mem_reachBall (G : BondGraph V E) (x y : V) (k : ℕ)
    (hy : y ∈ reachBall G x k) : (openSimpleGraph G Set.univ).dist x y ≤ k := by
  obtain ⟨q,hq⟩ := reachBall_exists_short_walk G x k hy
  exact (SimpleGraph.dist_le q).trans hq

theorem walkPower_zero_of_lt_dist (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (k : ℕ) (x y : V) (hk : k < (openSimpleGraph G Set.univ).dist x y) :
    (matrixCoeff (P^k) x y).re = 0 := by
  apply walkPower_support G hloc a P hpos hP
  intro hy
  exact Nat.not_le_of_gt hk (dist_le_of_mem_reachBall G x y k hy)

 

theorem raw_two_time_collision_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (i m j n : ℕ) (him : i ≤ m) (hjn : j ≤ n) (x y : V) :
    (∑' w : RawFrom (openSimpleGraph G Set.univ) m x × RawFrom (openSimpleGraph G Set.univ) n y,
      if w.1.2.position i = w.2.2.position j then
        w.1.2.mass (walkKernel G hloc a)*w.2.2.mass (walkKernel G hloc a) else 0) ≤
      if i+j < (openSimpleGraph G Set.univ).dist x y then 0 else ‖P‖^(i+j) := by
  rw [raw_two_time_collision G hloc a P hpos hsym hP i m j n him hjn x y]
  split_ifs with hh
  · exact (walkPower_zero_of_lt_dist G hloc a P hpos hP (i+j) x y hh).le
  · exact matrixCoeff_power_le P (i+j) x y

end FinitePropagation
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

 

theorem raw_intersection_probability_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (m n : ℕ) (x y : V) :
    (∑' w : RawFrom (openSimpleGraph G Set.univ) m x × RawFrom (openSimpleGraph G Set.univ) n y,
      if ∃ z, z ∈ w.1.2.vertices ∧ z ∈ w.2.2.vertices then
        w.1.2.mass (walkKernel G hloc a)*w.2.2.mass (walkKernel G hloc a) else 0) ≤
    ∑ i : Fin (m+1), ∑ j : Fin (n+1),
      if i.val+j.val < (openSimpleGraph G Set.univ).dist x y then 0 else ‖P‖^(i.val+j.val) := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let := Fintype.ofFinite (RawFrom (openSimpleGraph G Set.univ) m x)
  let := Fintype.ofFinite (RawFrom (openSimpleGraph G Set.univ) n y)
  have hK (x y : V) : 0 ≤ walkKernel G hloc a x y := by
    simpa only [hP,Complex.ofReal_re] using (hpos x y).2
  have he (w : RawFrom (openSimpleGraph G Set.univ) m x × RawFrom (openSimpleGraph G Set.univ) n y) :
      (∃ z, z ∈ w.1.2.vertices ∧ z ∈ w.2.2.vertices) ↔
        ∃ ij : Fin (m+1) × Fin (n+1), w.1.2.position ij.1 = w.2.2.position ij.2 := by
    constructor
    · rintro ⟨z,hz,hz'⟩
      obtain ⟨i,hi,he⟩ := w.1.2.mem_vertices_iff_position.mp hz
      obtain ⟨j,hj,he'⟩ := w.2.2.mem_vertices_iff_position.mp hz'
      exact ⟨(⟨i,by omega⟩,⟨j,by omega⟩),he.trans he'.symm⟩
    · rintro ⟨⟨i,j⟩,hij⟩
      exact ⟨w.1.2.position i,w.1.2.position_mem_vertices i,hij ▸ w.2.2.position_mem_vertices j⟩
  simp only [he,tsum_fintype]
  have hu := finite_nonnegative_event_union
    (fun w : RawFrom (openSimpleGraph G Set.univ) m x × RawFrom (openSimpleGraph G Set.univ) n y =>
      w.1.2.mass (walkKernel G hloc a)*w.2.2.mass (walkKernel G hloc a))
    (fun w => mul_nonneg (w.1.2.mass_nonneg _ hK) (w.2.2.mass_nonneg _ hK))
    (fun w (ij : Fin (m+1) × Fin (n+1)) => w.1.2.position ij.1 = w.2.2.position ij.2)
  apply hu.trans
  rw [Fintype.sum_prod_type]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  simpa only [tsum_fintype] using
    raw_two_time_collision_bound G hloc a P hpos hsym hP i m j n (by omega) (by omega) x y

end ActualCollisionUnion
end Percolation

 
namespace Percolation
section UniformCollisionTails
attribute [local instance] Classical.propDecidable Classical.decEq

theorem geometric_cutoff_summable (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (J : ℕ) :
    Summable (fun i : ℕ => if J ≤ i then ρ^i else 0) :=
  Summable.of_nonneg_of_le (fun i => by split_ifs <;> positivity)
    (fun i => by split_ifs <;> first | exact le_rfl | exact pow_nonneg hρ i)
    (summable_geometric_of_lt_one hρ hρ1)

theorem geometric_cutoff_tsum (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (J : ℕ) :
    (∑' i : ℕ, if J ≤ i then ρ^i else 0) = ρ^J/(1-ρ) := by
  have hs := geometric_cutoff_summable ρ hρ hρ1 J
  rw [←hs.sum_add_tsum_nat_add J]
  have hz : (∑ i ∈ Finset.range J, if J ≤ i then ρ^i else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact ite_eq_right (Nat.not_le_of_gt (Finset.mem_range.mp hi))
  rw [hz,zero_add]
  simp only [Nat.le_add_left,ite_true,pow_add,tsum_mul_right,
    tsum_geometric_of_lt_one hρ hρ1,div_eq_mul_inv]
  exact mul_comm _ _

theorem finite_geometric_cutoff_bound (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (J M : ℕ) :
    (∑ i : Fin M, if J ≤ i.val then ρ^i.val else 0) ≤ ρ^J/(1-ρ) := by
  change (∑ i : Fin M, (fun n : ℕ => if J ≤ n then ρ^n else 0) i.val) ≤ _
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => if J ≤ n then ρ^n else 0) M,←geometric_cutoff_tsum ρ hρ hρ1 J]
  exact Summable.sum_le_tsum (s := Finset.range M) (fun i _ => by split_ifs <;> positivity)
    (geometric_cutoff_summable ρ hρ hρ1 J)

 

theorem finite_double_geometric_cutoff_bound (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (J M N D : ℕ) (hD : 2*J ≤ D) :
    (∑ i : Fin M, ∑ j : Fin N, if i.val+j.val < D then 0 else ρ^(i.val+j.val)) ≤
      2*ρ^J/(1-ρ)^2 := by
  let q : ℕ → ℝ := fun i => if J ≤ i then ρ^i else 0
  have hq (i : ℕ) : 0 ≤ q i := by dsimp [q]; split_ifs <;> positivity
  have hp (i : ℕ) : 0 ≤ ρ^i := pow_nonneg hρ i
  have hQ := finite_geometric_cutoff_bound ρ hρ hρ1 J M
  have hQ' := finite_geometric_cutoff_bound ρ hρ hρ1 J N
  have hS := finite_geometric_cutoff_bound ρ hρ hρ1 0 M
  have hS' := finite_geometric_cutoff_bound ρ hρ hρ1 0 N
  simp only [Nat.zero_le,ite_true,pow_zero,one_div] at hS hS'
  have hd : 0 < 1-ρ := sub_pos.mpr hρ1
  calc
    _ ≤ ∑ i : Fin M, ∑ j : Fin N, (q i.val*ρ^j.val + ρ^i.val*q j.val) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      by_cases hh : i.val+j.val < D
      · rw [ite_eq_left hh]
        exact add_nonneg (mul_nonneg (hq _) (hp _)) (mul_nonneg (hp _) (hq _))
      · rw [ite_eq_right hh,pow_add]
        have hj : J ≤ i.val ∨ J ≤ j.val := by omega
        rcases hj with hi | hj
        · simp only [q,ite_eq_left hi]
          exact le_add_of_nonneg_right (mul_nonneg (hp _) (by split_ifs <;> positivity))
        · simp only [q,ite_eq_left hj]
          exact le_add_of_nonneg_left (mul_nonneg (by split_ifs <;> positivity) (hp _))
    _ = (∑ i : Fin M, q i.val)*(∑ j : Fin N, ρ^j.val) +
        (∑ i : Fin M, ρ^i.val)*(∑ j : Fin N, q j.val) := by
      simp only [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul]
    _ ≤ (ρ^J/(1-ρ))*(1-ρ)⁻¹ + (1-ρ)⁻¹*(ρ^J/(1-ρ)) := by
      apply add_le_add
      · exact mul_le_mul hQ hS' (Finset.sum_nonneg (fun i _ => hp _)) (by positivity)
      · exact mul_le_mul hS hQ' (Finset.sum_nonneg (fun i _ => hq _)) (by positivity)
    _ = _ := by field_simp; ring

end UniformCollisionTails
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section UniformRawCollision
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem raw_intersection_uniform_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ)) (hcontract : ‖P‖ < 1)
    (m n J : ℕ) (x y : V) (hD : 2*J ≤ (openSimpleGraph G Set.univ).dist x y) :
    (∑' w : RawFrom (openSimpleGraph G Set.univ) m x × RawFrom (openSimpleGraph G Set.univ) n y,
      if ∃ z, z ∈ w.1.2.vertices ∧ z ∈ w.2.2.vertices then
        w.1.2.mass (walkKernel G hloc a)*w.2.2.mass (walkKernel G hloc a) else 0) ≤
      2*‖P‖^J/(1-‖P‖)^2 :=
  (raw_intersection_probability_bound G hloc a P hpos hsym hP m n x y).trans
    (finite_double_geometric_cutoff_bound ‖P‖ (norm_nonneg _) hcontract J (m+1) (n+1) _ hD)


end UniformRawCollision
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

 

theorem positive_rows_collision_hasSum (A B : Hilbert V →L[ℂ] Hilbert V)
    (hA : PositiveRealMatrix A) (x y : V) :
    HasSum (fun z => (matrixCoeff A x z).re*(matrixCoeff B y z).re)
      (matrixCoeff (A*star B) x y).re := by
  simpa only [matrixCoeff_adjoint,Complex.star_def,Complex.conj_re] using
    hA.mul_hasSum (star B) x y

theorem positive_rows_collision_bound (A B : Hilbert V →L[ℂ] Hilbert V)
    (hA : PositiveRealMatrix A) (x y : V) :
    (∑' z, (matrixCoeff A x z).re*(matrixCoeff B y z).re) ≤ ‖A‖*‖B‖ := by
  rw [(positive_rows_collision_hasSum A B hA x y).tsum_eq]
  apply (Complex.re_le_norm _).trans ((matrixCoeff_norm_le (A*star B) x y).trans _)
  have hs : ‖star B‖ = ‖B‖ := ContinuousLinearMap.adjoint.norm_map B
  simpa only [hs] using norm_mul_le A (star B)

theorem walk_suffix_collision_operator_bound (P H : Hilbert V →L[ℂ] Hilbert V)
    (hP : PositiveRealMatrix P) (C : ℝ) (hH : ‖H‖ ≤ C) (l L : ℕ) (x y : V) :
    (∑' z, (matrixCoeff (P^l) x z).re*(matrixCoeff (P^L*H) y z).re) ≤
      C*‖P‖^(l+L) := by
  calc
    _ ≤ ‖P^l‖*‖P^L*H‖ := positive_rows_collision_bound _ _ (hP.pow l) x y
    _ ≤ ‖P‖^l*(‖P‖^L*C) := mul_le_mul (operator_pow_norm_le P l)
      ((norm_mul_le _ _).trans (mul_le_mul (operator_pow_norm_le P L) hH (norm_nonneg H)
        (pow_nonneg (norm_nonneg P) L))) (norm_nonneg _) (pow_nonneg (norm_nonneg P) l)
    _ = _ := by rw [pow_add]; ring

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

 

theorem raw_tail_anchored_collision_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (ep j : I)
    (P H : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hH : ∀ x y, matrixCoeff H x y = (anchoredPositionKernel G hloc γ n hdiam ep j x y : ℂ))
    (C : ℝ) (hHC : ‖H‖ ≤ C) (l m L : ℕ) (hlm : l ≤ m) (x y : V) :
    (∑' tail : RawFrom (openSimpleGraph G Set.univ) m x,
      tail.2.mass (walkKernel G hloc a) *
        ∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
          mid.2.mass (walkKernel G hloc a)*
            anchoredPositionKernel G hloc γ n hdiam ep j mid.1 (tail.2.position l)) ≤
      C*‖P‖^(l+L) := by
  simp only [raw_anchored_position_expectation G hloc a γ n hdiam ep j P H hpos hP hH]
  rw [raw_position_integral G hloc a l m hlm x (fun z => (matrixCoeff (P^L*H) y z).re),
    raw_integral_operator G hloc a P hpos hP]
  exact walk_suffix_collision_operator_bound P H hpos C hHC l L x y

end ActualSuffixCollision
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section UniformSuffixCollision
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I ι : Type*} [Fintype I] [Fintype ι]

 

theorem raw_tail_anchored_collision_uniform (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G)
    (htr : RootTransport root weight Γ) (hw : ∀ r, 0 ≤ weight r) (hw1 : ∑ r, weight r = 1)
    (hcov : ∀ x, ∃ r, ∃ g ∈ Γ, g (root r) = x)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ r, 1 ≤ c*weight r)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (ep j : I)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (l m L : ℕ) (hlm : l ≤ m) (x y : V) :
    (∑' tail : RawFrom (openSimpleGraph G Set.univ) m x,
      tail.2.mass (walkKernel G hloc a) *
        ∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
          mid.2.mass (walkKernel G hloc a)*
            anchoredPositionKernel G hloc γ n hdiam ep j mid.1 (tail.2.position l)) ≤
      Real.sqrt c*‖P‖^(l+L) := by
  obtain ⟨H,hH,hHn⟩ := exists_anchoredPositionOperator_uniform G hloc root weight Γ hΓ htr hw hw1 hcov
    c hc hmin γ n hdiam ep j
  exact raw_tail_anchored_collision_bound G hloc a γ n hdiam ep j P H hpos hP hH
    (Real.sqrt c) hHn l m L hlm x y

end UniformSuffixCollision
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

theorem finite_geometric_sum_bound (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (M : ℕ) :
    (∑ i : Fin M, ρ^i.val) ≤ 1/(1-ρ) := by
  simpa only [Nat.zero_le,ite_true,pow_zero] using finite_geometric_cutoff_bound ρ hρ hρ1 0 M

end GlobalAnchorDenominator
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section LiteralSuffixExperiment
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I : Type*} [Fintype I]

 

theorem raw_tail_anchor_collision_identity (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (ep j : I)
    (l m L : ℕ) (x y : V) :
    (∑' tail : RawFrom (openSimpleGraph G Set.univ) m x,
      ∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
        ∑' h : segmentAnchors G hloc γ n hdiam ep mid.1,
          if tail.2.position l = h.val j then
            tail.2.mass (walkKernel G hloc a)*mid.2.mass (walkKernel G hloc a)/
              (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) =
    (∑' tail : RawFrom (openSimpleGraph G Set.univ) m x,
      tail.2.mass (walkKernel G hloc a) *
        ∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
          mid.2.mass (walkKernel G hloc a)*
            anchoredPositionKernel G hloc γ n hdiam ep j mid.1 (tail.2.position l)) := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let (k : ℕ) (z : V) : Fintype (RawFrom (openSimpleGraph G Set.univ) k z) := Fintype.ofFinite _
  simp only [tsum_fintype]
  apply Finset.sum_congr rfl
  intro tail _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro mid _
  rw [←anchoredPositionKernel_global_denominator G hloc γ n hdiam ep j mid.1 (tail.2.position l)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  by_cases hh : tail.2.position l = h.val j
  · simp only [ite_eq_left hh,ite_eq_left hh.symm,div_eq_mul_inv,mul_assoc]
  · simp only [ite_eq_right hh,ite_eq_right (Ne.symm hh),mul_zero]

end LiteralSuffixExperiment
end Percolation

 
namespace Percolation
section NestedFiniteUnion
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finite_threefold_event_union {α β δ : Type*} [Fintype α] [Fintype β] [Fintype δ]
    {γ : β → Type*} [∀ b, Fintype (γ b)]
    (μ : (a : α) → (b : β) → γ b → ℝ) (hμ : ∀ a b c, 0 ≤ μ a b c)
    (B : (a : α) → (b : β) → γ b → δ → Prop) :
    (∑ a, ∑ b, ∑ c, if ∃ d, B a b c d then μ a b c else 0) ≤
      ∑ d, ∑ a, ∑ b, ∑ c, if B a b c d then μ a b c else 0 := by
  have hh := finite_nonnegative_event_union
    (fun ξ : α × Sigma γ => μ ξ.1 ξ.2.1 ξ.2.2)
    (fun ξ => hμ ξ.1 ξ.2.1 ξ.2.2)
    (fun ξ : α × Sigma γ => B ξ.1 ξ.2.1 ξ.2.2)
  simpa only [Fintype.sum_prod_type,Fintype.sum_sigma] using hh

end NestedFiniteUnion
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section WholeSuffixCollision
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I ι S : Type*} [Fintype I] [Fintype ι] [Fintype S]

 

theorem raw_tail_whole_suffix_collision_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G)
    (htr : RootTransport root weight Γ) (hw : ∀ r, 0 ≤ weight r) (hw1 : ∑ r, weight r = 1)
    (hcov : ∀ x, ∃ r, ∃ g ∈ Γ, g (root r) = x)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ r, 1 ≤ c*weight r)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (ep : I) (j : S → I)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hρ : ‖P‖ < 1) (m L : ℕ) (x y : V) :
    (∑' tail : RawFrom (openSimpleGraph G Set.univ) m x,
      ∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
        ∑' h : segmentAnchors G hloc γ n hdiam ep mid.1,
          if ∃ ij : Fin (m+1) × S, tail.2.position ij.1.val = h.val (j ij.2) then
            tail.2.mass (walkKernel G hloc a)*mid.2.mass (walkKernel G hloc a)/
              (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) ≤
      (Fintype.card S : ℝ)*Real.sqrt c*‖P‖^L/(1-‖P‖) := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let (k : ℕ) (z : V) : Fintype (RawFrom (openSimpleGraph G Set.univ) k z) := Fintype.ofFinite _
  have hK (x y : V) : 0 ≤ walkKernel G hloc a x y := by
    simpa only [hP,Complex.ofReal_re] using (hpos x y).2
  simp only [tsum_fintype]
  have hu := finite_threefold_event_union
    (α := RawFrom (openSimpleGraph G Set.univ) m x)
    (β := RawFrom (openSimpleGraph G Set.univ) L y)
    (γ := fun mid => segmentAnchors G hloc γ n hdiam ep mid.1)
    (δ := Fin (m+1) × S)
    (fun tail mid _ => tail.2.mass (walkKernel G hloc a)*mid.2.mass (walkKernel G hloc a)/
      (segmentAnchors G hloc γ n hdiam ep (γ ep)).card)
    (fun tail mid _ => div_nonneg (mul_nonneg (tail.2.mass_nonneg _ hK) (mid.2.mass_nonneg _ hK)) (Nat.cast_nonneg _))
    (fun tail _ h ij => tail.2.position ij.1.val = h.val (j ij.2))
  apply hu.trans
  rw [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ i : Fin (m+1), ∑ _s : S, Real.sqrt c*‖P‖^(i.val+L) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro s _
      have hh := raw_tail_anchored_collision_uniform G hloc a root weight Γ hΓ htr hw hw1 hcov c hc hmin
        γ n hdiam ep (j s) P hpos hP i.val m L (by omega) x y
      rw [←raw_tail_anchor_collision_identity G hloc a γ n hdiam ep (j s) i.val m L x y] at hh
      simpa only [tsum_fintype] using hh
    _ = ((Fintype.card S : ℝ)*Real.sqrt c*‖P‖^L)*(∑ i : Fin (m+1), ‖P‖^i.val) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,pow_add,←Finset.mul_sum,←Finset.sum_mul]
      ring
    _ ≤ ((Fintype.card S : ℝ)*Real.sqrt c*‖P‖^L)*(1/(1-‖P‖)) :=
      mul_le_mul_of_nonneg_left (finite_geometric_sum_bound ‖P‖ (norm_nonneg P) hρ (m+1)) (by positivity)
    _ = _ := by ring

end WholeSuffixCollision
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
universe u v
variable {V : Type u} {E : Type v}
section EarlyFiniteCollisions
attribute [local instance] Classical.propDecidable Classical.decEq
variable {S : Type*} [Fintype S]

 

theorem raw_hits_distant_set_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ)) (hρ : ‖P‖ < 1)
    (m J : ℕ) (x : V) (z : S → V) (hD : ∀ s, J ≤ (openSimpleGraph G Set.univ).dist x (z s)) :
    (∑' w : RawFrom (openSimpleGraph G Set.univ) m x,
      if ∃ s, z s ∈ w.2.vertices then w.2.mass (walkKernel G hloc a) else 0) ≤
      (Fintype.card S : ℝ)*‖P‖^J/(1-‖P‖) := by
  let (v : V) : Finite ((openSimpleGraph G Set.univ).neighborSet v) := finite_openSimpleGraph_neighbors G hloc v
  let : Fintype (RawFrom (openSimpleGraph G Set.univ) m x) := Fintype.ofFinite _
  have hK (x y : V) : 0 ≤ walkKernel G hloc a x y := by
    simpa only [hP,Complex.ofReal_re] using (hpos x y).2
  have he (w : RawFrom (openSimpleGraph G Set.univ) m x) :
      (∃ s, z s ∈ w.2.vertices) ↔ ∃ si : S × Fin (m+1), w.2.position si.2.val = z si.1 := by
    constructor
    · rintro ⟨s,hs⟩
      obtain ⟨i,hi,he⟩ := w.2.mem_vertices_iff_position.mp hs
      exact ⟨(s,⟨i,by omega⟩),he⟩
    · rintro ⟨⟨s,i⟩,he⟩
      exact ⟨s,he ▸ w.2.position_mem_vertices i.val⟩
  simp only [he,tsum_fintype]
  have hu := finite_nonnegative_event_union
    (fun w : RawFrom (openSimpleGraph G Set.univ) m x => w.2.mass (walkKernel G hloc a))
    (fun w => w.2.mass_nonneg _ hK)
    (fun w (si : S × Fin (m+1)) => w.2.position si.2.val = z si.1)
  apply hu.trans
  rw [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ _s : S, ∑ i : Fin (m+1), if J ≤ i.val then ‖P‖^i.val else 0 := by
      apply Finset.sum_le_sum
      intro s _
      apply Finset.sum_le_sum
      intro i _
      have hh := raw_position_probability G hloc a P hpos hP i.val m (by omega) x (z s)
      simp only [tsum_fintype] at hh
      rw [hh]
      split_ifs with hi
      · exact matrixCoeff_power_le P i.val x (z s)
      · exact (walkPower_zero_of_lt_dist G hloc a P hpos hP i.val x (z s) (by have hd := hD s; omega)).le
    _ ≤ ∑ _s : S, ‖P‖^J/(1-‖P‖) := Finset.sum_le_sum (fun _ _ =>
      finite_geometric_cutoff_bound ‖P‖ (norm_nonneg _) hρ J (m+1))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

end EarlyFiniteCollisions
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

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ActualEarlyExperiment
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem raw_early_collision_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ)) (hρ : ‖P‖ < 1)
    (m L J : ℕ) (x y : V) (pos neg : Fin (J+1) → V)
    (hposD : ∀ s, J ≤ (openSimpleGraph G Set.univ).dist x (pos s))
    (hnegD : ∀ s, J ≤ (openSimpleGraph G Set.univ).dist y (neg s))
    (hxy : 2*J ≤ (openSimpleGraph G Set.univ).dist x y) :
    (∑' w : RawFrom (openSimpleGraph G Set.univ) m x × RawFrom (openSimpleGraph G Set.univ) L y,
      if ((∃ s, pos s ∈ w.1.2.vertices) ∨ (∃ s, neg s ∈ w.2.2.vertices)) ∨
          (∃ z, z ∈ w.1.2.vertices ∧ z ∈ w.2.2.vertices) then
        w.1.2.mass (walkKernel G hloc a)*w.2.2.mass (walkKernel G hloc a) else 0) ≤
      earlyCollisionCost ‖P‖ J := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let : Fintype (RawFrom (openSimpleGraph G Set.univ) m x) := Fintype.ofFinite _
  let : Fintype (RawFrom (openSimpleGraph G Set.univ) L y) := Fintype.ofFinite _
  have hK (x y : V) : 0 ≤ walkKernel G hloc a x y := by
    simpa only [hP,Complex.ofReal_re] using (hpos x y).2
  have hu := finite_weighted_event_or
    (fun w : RawFrom (openSimpleGraph G Set.univ) m x × RawFrom (openSimpleGraph G Set.univ) L y =>
      w.1.2.mass (walkKernel G hloc a)*w.2.2.mass (walkKernel G hloc a))
    (fun w => mul_nonneg (w.1.2.mass_nonneg _ hK) (w.2.2.mass_nonneg _ hK))
    (fun w => (∃ s, pos s ∈ w.1.2.vertices) ∨ (∃ s, neg s ∈ w.2.2.vertices))
    (fun w => ∃ z, z ∈ w.1.2.vertices ∧ z ∈ w.2.2.vertices)
  have hp := finite_product_failure_union
    (fun w : RawFrom (openSimpleGraph G Set.univ) m x => w.2.mass (walkKernel G hloc a))
    (fun w : RawFrom (openSimpleGraph G Set.univ) L y => w.2.mass (walkKernel G hloc a))
    (fun w => w.2.mass_nonneg _ hK) (fun w => w.2.mass_nonneg _ hK)
    (by simpa only [tsum_fintype] using rawFrom_probability_sum G hloc a m x)
    (by simpa only [tsum_fintype] using rawFrom_probability_sum G hloc a L y)
    (fun w => ∃ s, pos s ∈ w.2.vertices) (fun w => ∃ s, neg s ∈ w.2.vertices)
  have hx := raw_hits_distant_set_bound G hloc a P hpos hP hρ m J x pos hposD
  have hy := raw_hits_distant_set_bound G hloc a P hpos hP hρ L J y neg hnegD
  have hi := raw_intersection_uniform_bound G hloc a P hpos hsym hP hρ m L J x y hxy
  simp only [tsum_fintype,Fintype.card_fin,Nat.cast_add,Nat.cast_one] at hx hy hi ⊢
  have hx' : (∑ w : RawFrom (openSimpleGraph G Set.univ) m x,
      if ∃ s, pos s ∈ w.2.vertices then w.2.mass (walkKernel G hloc a) else 0) ≤
      ((J:ℝ)+1)*‖P‖^J/(1-‖P‖) := by
    convert hx using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro w _
    split_ifs <;> rfl
  have hy' : (∑ w : RawFrom (openSimpleGraph G Set.univ) L y,
      if ∃ s, neg s ∈ w.2.vertices then w.2.mass (walkKernel G hloc a) else 0) ≤
      ((J:ℝ)+1)*‖P‖^J/(1-‖P‖) := by
    convert hy using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro w _
    split_ifs <;> rfl
  have hp' : (∑ w : RawFrom (openSimpleGraph G Set.univ) m x × RawFrom (openSimpleGraph G Set.univ) L y,
      if (∃ s, pos s ∈ w.1.2.vertices) ∨ (∃ s, neg s ∈ w.2.2.vertices) then
        w.1.2.mass (walkKernel G hloc a)*w.2.2.mass (walkKernel G hloc a) else 0) ≤
      (∑ w : RawFrom (openSimpleGraph G Set.univ) m x,
        if ∃ s, pos s ∈ w.2.vertices then w.2.mass (walkKernel G hloc a) else 0) +
      (∑ w : RawFrom (openSimpleGraph G Set.univ) L y,
        if ∃ s, neg s ∈ w.2.vertices then w.2.mass (walkKernel G hloc a) else 0) := by
    convert hp using 1
    · apply Finset.sum_congr rfl
      intro w _
      split_ifs <;> rfl
    · congr 1 <;> apply Finset.sum_congr rfl <;> intro w _ <;> split_ifs <;> rfl
  have hr : (((J:ℝ)+1)*‖P‖^J/(1-‖P‖) + ((J:ℝ)+1)*‖P‖^J/(1-‖P‖)) +
      2*‖P‖^J/(1-‖P‖)^2 = earlyCollisionCost ‖P‖ J := by
    unfold earlyCollisionCost
    ring
  have hh := hu.trans ((add_le_add (hp'.trans (add_le_add hx' hy')) hi).trans_eq hr)
  exact hh

end ActualEarlyExperiment
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ConditioningCost
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I : Type*} [Fintype I]

 

theorem raw_anchor_event_le_unconditioned (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (hK : ∀ x y, 0 ≤ walkKernel G hloc a x y)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (ep : I)
    (m L : ℕ) (x y : V)
    (B : RawFrom (openSimpleGraph G Set.univ) m x → RawFrom (openSimpleGraph G Set.univ) L y → Prop) [∀ tail mid, Decidable (B tail mid)] :
    (∑' tail : RawFrom (openSimpleGraph G Set.univ) m x,
      ∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
        ∑' _h : segmentAnchors G hloc γ n hdiam ep mid.1,
          if B tail mid then tail.2.mass (walkKernel G hloc a)*mid.2.mass (walkKernel G hloc a)/
            (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) ≤
    (∑' w : RawFrom (openSimpleGraph G Set.univ) m x × RawFrom (openSimpleGraph G Set.univ) L y,
      if B w.1 w.2 then w.1.2.mass (walkKernel G hloc a)*w.2.2.mass (walkKernel G hloc a) else 0) := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let (k : ℕ) (z : V) : Fintype (RawFrom (openSimpleGraph G Set.univ) k z) := Fintype.ofFinite _
  have hN : 0 < ((segmentAnchors G hloc γ n hdiam ep (γ ep)).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ((segmentAnchors_nonempty_iff G hloc γ n hdiam ep (γ ep)).mpr
      ⟨Equiv.refl V,Equiv.refl E,isAut_refl G,rfl⟩)
  simp only [tsum_fintype,Fintype.sum_prod_type]
  apply Finset.sum_le_sum
  intro tail _
  apply Finset.sum_le_sum
  intro mid _
  by_cases hb : B tail mid
  · simp only [ite_eq_left hb,Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
    have hc : ((segmentAnchors G hloc γ n hdiam ep mid.1).card : ℝ) ≤
        (segmentAnchors G hloc γ n hdiam ep (γ ep)).card := by
      rw [segmentAnchors_card_eq_indicator G hloc γ n hdiam ep mid.1]
      split_ifs
      · exact le_rfl
      · exact_mod_cast Nat.zero_le _
    rw [←mul_div_assoc]
    apply (div_le_iff₀ hN).mpr
    have hh := mul_le_mul_of_nonneg_right hc
      (mul_nonneg (tail.2.mass_nonneg _ hK) (mid.2.mass_nonneg _ hK))
    nlinarith
  · simp only [ite_eq_right hb,Finset.sum_const_zero]
    exact le_rfl

end ConditioningCost
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section EarlyAnchoredCollision
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I : Type*} [Fintype I]

 

theorem raw_anchor_early_collision_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (ep : I)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ)) (hρ : ‖P‖ < 1)
    (m L J : ℕ) (x y : V) (pos neg : Fin (J+1) → V)
    (hposD : ∀ s, J ≤ (openSimpleGraph G Set.univ).dist x (pos s))
    (hnegD : ∀ s, J ≤ (openSimpleGraph G Set.univ).dist y (neg s))
    (hxy : 2*J ≤ (openSimpleGraph G Set.univ).dist x y) :
    (∑' tail : RawFrom (openSimpleGraph G Set.univ) m x,
      ∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
        ∑' _h : segmentAnchors G hloc γ n hdiam ep mid.1,
          if ((∃ s, pos s ∈ tail.2.vertices) ∨ (∃ s, neg s ∈ mid.2.vertices)) ∨
              (∃ z, z ∈ tail.2.vertices ∧ z ∈ mid.2.vertices) then
            tail.2.mass (walkKernel G hloc a)*mid.2.mass (walkKernel G hloc a)/
              (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) ≤
      earlyCollisionCost ‖P‖ J := by
  have hK (x y : V) : 0 ≤ walkKernel G hloc a x y := by
    simpa only [hP,Complex.ofReal_re] using (hpos x y).2
  exact (raw_anchor_event_le_unconditioned G hloc a hK γ n hdiam ep m L x y
    (fun tail mid => ((∃ s, pos s ∈ tail.2.vertices) ∨ (∃ s, neg s ∈ mid.2.vertices)) ∨
      (∃ z, z ∈ tail.2.vertices ∧ z ∈ mid.2.vertices))).trans
    (raw_early_collision_bound G hloc a P hpos hsym hP hρ m L J x y pos neg hposD hnegD hxy)

 

theorem raw_tail_integrate_anchor_event (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (ep : I)
    (m L : ℕ) (x y : V)
    (B : (mid : RawFrom (openSimpleGraph G Set.univ) L y) →
      segmentAnchors G hloc γ n hdiam ep mid.1 → Prop) [∀ mid h, Decidable (B mid h)] :
    (∑' tail : RawFrom (openSimpleGraph G Set.univ) m x,
      ∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
        ∑' h : segmentAnchors G hloc γ n hdiam ep mid.1,
          if B mid h then tail.2.mass (walkKernel G hloc a)*mid.2.mass (walkKernel G hloc a)/
            (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) =
    (∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
      ∑' h : segmentAnchors G hloc γ n hdiam ep mid.1,
        if B mid h then mid.2.mass (walkKernel G hloc a)/
          (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) := by
  have he (tail : RawFrom (openSimpleGraph G Set.univ) m x)
      (mid : RawFrom (openSimpleGraph G Set.univ) L y)
      (h : segmentAnchors G hloc γ n hdiam ep mid.1) :
      (if B mid h then tail.2.mass (walkKernel G hloc a)*mid.2.mass (walkKernel G hloc a)/
        (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) =
      tail.2.mass (walkKernel G hloc a) *
        (if B mid h then mid.2.mass (walkKernel G hloc a)/
          (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) := by
    split_ifs <;> ring
  simp only [he,tsum_mul_left,tsum_mul_right,rawFrom_probability_sum G hloc a,one_mul]

end EarlyAnchoredCollision
end Percolation

 
namespace Percolation
section DependentUnion
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finite_threefold_event_or {α β : Type*} {γ : β → Type*}
    [Fintype α] [Fintype β] [∀ b, Fintype (γ b)]
    (μ : α → (b : β) → γ b → ℝ) (hμ : ∀ a b c, 0 ≤ μ a b c)
    (B C : α → (b : β) → γ b → Prop)
    [∀ a b c, Decidable (B a b c)] [∀ a b c, Decidable (C a b c)] :
    (∑ a, ∑ b, ∑ c, if B a b c ∨ C a b c then μ a b c else 0) ≤
      (∑ a, ∑ b, ∑ c, if B a b c then μ a b c else 0) +
      (∑ a, ∑ b, ∑ c, if C a b c then μ a b c else 0) := by
  simp only [←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  apply Finset.sum_le_sum
  intro c _
  by_cases hb : B a b c <;> by_cases hc : C a b c <;>
    simp only [hb,hc,or_self,or_false,false_or,ite_true,ite_false,add_zero,zero_add,le_refl]
  exact le_add_of_nonneg_right (hμ a b c)

end DependentUnion
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section CombinedRawAvoidance
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I ι : Type*} [Fintype I] [Fintype ι]



theorem raw_first_escape_collision_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G)
    (htr : RootTransport root weight Γ) (hw : ∀ r, 0 ≤ weight r) (hw1 : ∑ r, weight r = 1)
    (hcov : ∀ x, ∃ r, ∃ g ∈ Γ, g (root r) = x)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ r, 1 ≤ c*weight r)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (ep : I)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ)) (hρ : ‖P‖ < 1)
    (m L J : ℕ) (x y : V) (pos neg : Fin (J+1) → V) (j : Fin (J+1) → I)
    (hposD : ∀ s, J ≤ (openSimpleGraph G Set.univ).dist x (pos s))
    (hnegD : ∀ s, J ≤ (openSimpleGraph G Set.univ).dist y (neg s))
    (hxy : 2*J ≤ (openSimpleGraph G Set.univ).dist x y) :
    (∑' tail : RawFrom (openSimpleGraph G Set.univ) m x,
      ∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
        ∑' h : segmentAnchors G hloc γ n hdiam ep mid.1,
          if firstEscapeCollision G J m L x y pos neg j tail mid h.val then
            tail.2.mass (walkKernel G hloc a)*mid.2.mass (walkKernel G hloc a)/
              (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) ≤
      earlyCollisionCost ‖P‖ J + suffixCollisionCost ‖P‖ c J*‖P‖^L := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let (k : ℕ) (z : V) : Fintype (RawFrom (openSimpleGraph G Set.univ) k z) := Fintype.ofFinite _
  have hK (x y : V) : 0 ≤ walkKernel G hloc a x y := by
    simpa only [hP,Complex.ofReal_re] using (hpos x y).2
  let μ := fun (tail : RawFrom (openSimpleGraph G Set.univ) m x)
      (mid : RawFrom (openSimpleGraph G Set.univ) L y)
      (_h : segmentAnchors G hloc γ n hdiam ep mid.1) =>
    tail.2.mass (walkKernel G hloc a)*mid.2.mass (walkKernel G hloc a)/
      (segmentAnchors G hloc γ n hdiam ep (γ ep)).card
  have hμ : ∀ tail mid h, 0 ≤ μ tail mid h := fun tail mid _ =>
    div_nonneg (mul_nonneg (tail.2.mass_nonneg _ hK) (mid.2.mass_nonneg _ hK)) (Nat.cast_nonneg _)
  let B := fun (tail : RawFrom (openSimpleGraph G Set.univ) m x)
      (mid : RawFrom (openSimpleGraph G Set.univ) L y)
      (_h : segmentAnchors G hloc γ n hdiam ep mid.1) =>
    ((∃ s, pos s ∈ tail.2.vertices) ∨ (∃ s, neg s ∈ mid.2.vertices)) ∨
      (∃ z, z ∈ tail.2.vertices ∧ z ∈ mid.2.vertices)
  let C := fun (_tail : RawFrom (openSimpleGraph G Set.univ) m x)
      (mid : RawFrom (openSimpleGraph G Set.univ) L y)
      (h : segmentAnchors G hloc γ n hdiam ep mid.1) =>
    ∃ st : Fin (J+1) × Fin (J+1), h.val (j st.1) = neg st.2
  let D := fun (tail : RawFrom (openSimpleGraph G Set.univ) m x)
      (mid : RawFrom (openSimpleGraph G Set.univ) L y)
      (h : segmentAnchors G hloc γ n hdiam ep mid.1) =>
    ∃ ij : Fin (m+1) × Fin (J+1), tail.2.position ij.1.val = h.val (j ij.2)
  have hu := finite_threefold_event_or μ hμ B (fun tail mid h => C tail mid h ∨ D tail mid h)
  have hv := finite_threefold_event_or μ hμ C D
  have he := raw_anchor_early_collision_bound G hloc a γ n hdiam ep P hpos hsym hP hρ
    m L J x y pos neg hposD hnegD hxy
  have hn := raw_anchor_finite_collision_bound G hloc a root weight Γ hΓ htr hw hw1 hcov
    c hc hmin γ n hdiam ep j neg P hpos hP L y
  rw [←raw_tail_integrate_anchor_event G hloc a γ n hdiam ep m L x y
    (fun _ h => ∃ st : Fin (J+1) × Fin (J+1), h.val (j st.1) = neg st.2)] at hn
  have ht := raw_tail_whole_suffix_collision_bound G hloc a root weight Γ hΓ htr hw hw1 hcov
    c hc hmin γ n hdiam ep j P hpos hP hρ m L x y
  simp only [tsum_fintype,Fintype.card_fin,Nat.cast_add,Nat.cast_one] at he hn ht ⊢
  have hr : earlyCollisionCost ‖P‖ J +
      ((((J:ℝ)+1)*((J:ℝ)+1)*Real.sqrt c*‖P‖^L) +
        ((J:ℝ)+1)*Real.sqrt c*‖P‖^L/(1-‖P‖)) =
      earlyCollisionCost ‖P‖ J + suffixCollisionCost ‖P‖ c J*‖P‖^L := by
    unfold suffixCollisionCost
    ring
  have hh := hu.trans ((add_le_add he (hv.trans (add_le_add hn ht))).trans_eq hr)
  apply le_trans ?_ hh
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro tail _
  apply Finset.sum_congr rfl
  intro mid _
  apply Finset.sum_congr rfl
  intro h _
  unfold firstEscapeCollision B C D μ
  split_ifs <;> rfl

end CombinedRawAvoidance
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section NormalizedFirstEscape
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I ι : Type*} [Fintype I] [Fintype ι]

 

theorem conditional_first_escape_collision_bound_oai (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G)
    (htr : RootTransport root weight Γ) (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
    (hcov : ∀ x, ∃ r, ∃ g ∈ Γ, g (root r) = x)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ r, 1 ≤ c*weight r)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (ep : I)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re) (hρ : ‖P‖ < 1)
    (m L J : ℕ) (x y : V) (hy : y ∈ vertexOrbit G (γ ep))
    (pos neg : Fin (J+1) → V) (j : Fin (J+1) → I)
    (hposD : ∀ s, J ≤ (openSimpleGraph G Set.univ).dist x (pos s))
    (hnegD : ∀ s, J ≤ (openSimpleGraph G Set.univ).dist y (neg s))
    (hxy : 2*J ≤ (openSimpleGraph G Set.univ).dist x y) :
    (∑' tail : RawFrom (openSimpleGraph G Set.univ) m x,
      ∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
        ∑' h : segmentAnchors G hloc γ n hdiam ep mid.1,
          if firstEscapeCollision G J m L x y pos neg j tail mid h.val then
            tail.2.mass (walkKernel G hloc a)*mid.2.mass (walkKernel G hloc a)/
              (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) /
        segmentReturnMass G hloc a γ ep L y ≤
      2*c*(earlyCollisionCost ‖P‖ J + suffixCollisionCost ‖P‖ c J*‖P‖^L) := by
  have hb := raw_first_escape_collision_bound G hloc a root weight Γ hΓ htr
    (fun r => (hw r).le) hw1 hcov c hc.le hmin γ n hdiam ep P hpos hsym hP hρ
    m L J x y pos neg j hposD hnegD hxy
  have hq := segmentReturnMass_uniform_lower G hloc a root weight Γ hΓ htr hcov hw hw1 c hc hmin
    P hpos hsym hP hdiag γ ep L
  rw [←segmentReturnMass_on_orbit G hloc a γ ep L y hy P hpos hP] at hq
  have htc : 0 < 2*c := mul_pos (by norm_num) hc
  have hqp : 0 < segmentReturnMass G hloc a γ ep L y := (one_div_pos.mpr htc).trans_le hq
  apply (div_le_iff₀ hqp).mpr
  apply hb.trans
  have hB : 0 ≤ earlyCollisionCost ‖P‖ J + suffixCollisionCost ‖P‖ c J*‖P‖^L := by
    unfold earlyCollisionCost suffixCollisionCost
    have : 0 < 1-‖P‖ := sub_pos.mpr hρ
    positivity
  have h1 : 1 ≤ (2*c)*segmentReturnMass G hloc a γ ep L y := by
    exact (div_le_iff₀ htc).mp hq |>.trans_eq (mul_comm _ _)
  have hh := mul_le_mul_of_nonneg_right h1 hB
  nlinarith only [hh]

end NormalizedFirstEscape
end Percolation


end OAI
end

theorem solution.{u, v, u_1, u_2} : type_of% @OAI.Percolation.conditional_first_escape_collision_bound_oai.{u, v, u_1, u_2} := @OAI.Percolation.conditional_first_escape_collision_bound_oai.{u, v, u_1, u_2}
