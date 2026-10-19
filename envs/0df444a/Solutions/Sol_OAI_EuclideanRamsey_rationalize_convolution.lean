-- Prove2me | solution 1 for OAI.EuclideanRamsey.rationalize_convolution
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:23:37.141895+00:00
-- url     : https://prove2.me/submissions/54570e71-a53a-44a6-b653-2f9b4a679e15

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/RationalConvolution.lean:L136-L223
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.rationalize_convolution. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EuclideanRamsey
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization

-- ---- from OAI.Combinatorics.EuclideanRamsey.RationalConvolution ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

universe uGroup uIndex

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter

namespace EuclideanRamsey
open MeasureTheory Filter
open scoped BigOperators Pointwise Topology

end EuclideanRamsey

open scoped BigOperators Pointwise
namespace EuclideanRamsey

lemma rational_convolution_coeff {G : Type uGroup} [AddCommGroup G] [DecidableEq G]
    (ν d : AddMonoidAlgebra ℚ G) (δ : G) :
    (ν*d).coeff δ = ∑ γ ∈ ν.coeff.support,ν.coeff γ*d.coeff (δ-γ) := by
  rw [AddMonoidAlgebra.coeff_mul]
  apply Finset.sum_congr rfl
  intro γ hγ
  change (∑ β ∈ d.coeff.support,if γ+β=δ then ν.coeff γ*d.coeff β else 0) = _
  have he (β : G) : γ+β=δ ↔ β=δ-γ := by
    constructor
    · intro h; apply eq_sub_iff_add_eq.mpr; simpa [add_comm] using h
    · intro h; rw [h]; abel
  simp only [he,Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · simp [Finsupp.notMem_support_iff.mp h]

end EuclideanRamsey

open scoped BigOperators Topology
namespace EuclideanRamsey

lemma rational_vector_strict {ι : Type uIndex} [Fintype ι]
    (ζ N : (ι → ℝ) → ℝ) (hζ : Continuous ζ) (hN : Continuous N)
    (η : ℝ) (d : ι → ℝ) (hp : 0 < ζ d) (hn : N d < η*ζ d) :
    ∃ q : ι → ℚ, 0 < ζ (fun i => q i) ∧ N (fun i => q i) < η*ζ (fun i => q i) := by
  have hDense : DenseRange (fun q : ι → ℚ => fun i => (q i : ℝ)) := by
    exact DenseRange.piMap (fun _ => Rat.denseRange_cast)
  have hopen : IsOpen {d : ι → ℝ | 0 < ζ d ∧ N d < η*ζ d} :=
    (isOpen_lt continuous_const hζ).inter (isOpen_lt hN (continuous_const.mul hζ))
  exact hDense.exists_mem_open hopen ⟨d,hp,hn⟩
end EuclideanRamsey

namespace EuclideanRamsey
open scoped BigOperators Pointwise

lemma rationalize_convolution {G : Type uGroup} [AddCommGroup G] [DecidableEq G]
    (ν : AddMonoidAlgebra ℚ G) (w : G → ℝ) (t η : ℝ)
    {a : G → ℝ} (ha : Function.HasFiniteSupport a)
    (hp : 0 < (∑' γ,a γ)/t)
    (hn : (∑' δ,max (-(∑ γ ∈ ν.coeff.support,(ν.coeff γ:ℝ)*a (δ-γ))) 0*w δ) <
      η*((∑' γ,a γ)/t)) :
    ∃ b : AddMonoidAlgebra ℚ G,
      0 < ((b.coeff.sum fun _ q => q : ℚ):ℝ)/t ∧
      (∑' δ,max (-((ν*b).coeff δ:ℝ)) 0*w δ) <
        η*(((b.coeff.sum fun _ q => q : ℚ):ℝ)/t) := by
  classical
  let E := ha.toFinset
  let : Fintype E := inferInstance
  let K := ν.coeff.support+E
  let ext (d : E → ℝ) (γ : G) := if h : γ ∈ E then d ⟨γ,h⟩ else 0
  let ζ (d : E → ℝ) := (∑ γ : E,d γ)/t
  let N (d : E → ℝ) := ∑ δ ∈ K,max (-(∑ γ ∈ ν.coeff.support,(ν.coeff γ:ℝ)*ext d (δ-γ))) 0*w δ
  have hζ : Continuous ζ := by unfold ζ; fun_prop
  have hExt (γ : G) : Continuous (fun d : E → ℝ => ext d γ) := by
    dsimp [ext]
    split_ifs <;> fun_prop
  have hN : Continuous N := by unfold N; fun_prop
  have hsum (d : E → ℝ) : ∑' γ,ext d γ = ∑ γ : E,d γ := by
    rw [tsum_eq_sum (s := E)]
    · rw [← Finset.sum_coe_sort]
      apply Finset.sum_congr rfl
      intro γ hγ
      simp only [ext,dite_eq_left γ.property]
    · intro γ hγ
      simp [ext,hγ]
  have hNeg (d : E → ℝ) : (∑' δ,max (-(∑ γ ∈ ν.coeff.support,(ν.coeff γ:ℝ)*ext d (δ-γ))) 0*w δ) = N d := by
    apply tsum_eq_sum
    intro δ hδ
    have hz : ∑ γ ∈ ν.coeff.support,(ν.coeff γ:ℝ)*ext d (δ-γ) = 0 := by
      apply Finset.sum_eq_zero
      intro γ hγ
      have hE : δ-γ ∉ E := by
        intro h
        exact hδ (Finset.mem_add.mpr ⟨γ,hγ,δ-γ,h,by abel⟩)
      simp [ext,hE]
    simp [hz]
  let aE : E → ℝ := fun γ => a γ
  have haE : ext aE = a := by
    funext γ
    dsimp [ext,aE]
    split_ifs with h
    · rfl
    · have hγ : γ ∉ Function.support a := by
        intro hh
        exact h (ha.mem_toFinset.mpr hh)
      exact (not_not.mp hγ).symm
  have hpE : 0 < ζ aE := by
    change 0 < (∑ γ : E,aE γ)/t
    rw [← hsum aE,haE]
    exact hp
  have hnE : N aE < η*ζ aE := by
    rw [← hNeg,haE]
    change _ < η*((∑ γ : E,aE γ)/t)
    rw [← hsum aE,haE]
    exact hn
  obtain ⟨q,hq0,hqN⟩ := rational_vector_strict ζ N hζ hN η aE hpE hnE
  let b : AddMonoidAlgebra ℚ G := ∑ γ : E,AddMonoidAlgebra.single γ.val (q γ)
  have hb (γ : G) : (b.coeff γ : ℝ) = ext (fun i => (q i:ℝ)) γ := by
    simp only [b,AddMonoidAlgebra.coeff_sum,Finsupp.finsetSum_apply,Rat.cast_sum]
    by_cases h : γ ∈ E
    · rw [Finset.sum_eq_single ⟨γ,h⟩]
      · simp [ext,h]
      · intro β hβ hne
        have hne' : β.val ≠ γ := fun he => hne (Subtype.ext he)
        simp [hne']
      · simp
    · have hz (β : E) : β.val ≠ γ := fun hb => h (hb ▸ β.property)
      simp [ext,h,hz]
  have hbMass : ((b.coeff.sum fun _ q => q : ℚ):ℝ) = ∑ γ : E,(q γ:ℝ) := by
    have ht : ∑' γ,(b.coeff γ:ℝ) = ((b.coeff.sum fun _ q => q : ℚ):ℝ) := by
      rw [tsum_eq_sum (s := b.coeff.support)]
      · simp [Finsupp.sum]
      · intro γ hγ; simp [Finsupp.notMem_support_iff.mp hγ]
    rw [← ht]
    simp only [hb]
    exact hsum (fun i => (q i:ℝ))
  refine ⟨b,?_,?_⟩
  · simpa only [hbMass,ζ] using hq0
  · have hc (δ : G) : ((ν*b).coeff δ:ℝ) = ∑ γ ∈ ν.coeff.support,(ν.coeff γ:ℝ)*ext (fun i => (q i:ℝ)) (δ-γ) := by
      rw [rational_convolution_coeff]
      simp only [Rat.cast_sum,Rat.cast_mul,hb]
    simp only [hc,hNeg,hbMass]
    exact hqN

end EuclideanRamsey

end

end OAI

-- ---- platform node ----
open OAI OAI.EuclideanRamsey
open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped BigOperators Pointwise


theorem solution.{uGroup} : type_of% @_root_.OAI.EuclideanRamsey.rationalize_convolution.{uGroup} := @_root_.OAI.EuclideanRamsey.rationalize_convolution.{uGroup}
