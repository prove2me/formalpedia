-- Prove2me | solution 1 for OAI.SingleLatticeCovering.Assembly.eventual_single_lattice_covering
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T15:00:59.107493+00:00
-- url     : https://prove2.me/submissions/dd78a951-d5fb-4329-b1e6-96f13eb4f7e5

import Mathlib
import Definitions.Def_OAIQ16Cd002
import Theorems.Thm_OAI_SingleLatticeCovering_GaussianNumerics_eventually_local_position
import Theorems.Thm_OAI_SingleLatticeCovering_PrimeKernel_eventually_meanPrimeHole_all
import Theorems.Thm_OAI_SingleLatticeCovering_Vertical_vertical_patterns_alphabets

section
-- module Solutions.OAIQ16_CD.Compat
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_Products
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators
open Real
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
noncomputable section
open scoped BigOperators
open MeasureTheory Set
noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators
noncomputable section
open Real Filter Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter Topology Asymptotics
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
noncomputable section
open Module MeasureTheory

namespace SingleLatticeCovering.LatticeGeometry


variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma finProduct_covolume {m n : ℕ} (L : Submodule ℤ (Fin m → ℝ))
    (N : Submodule ℤ (Fin n → ℝ)) [DiscreteTopology L] [DiscreteTopology N]
    [IsZLattice ℝ L] [IsZLattice ℝ N] :
    ZLattice.covolume (finProduct L N) = ZLattice.covolume L * ZLattice.covolume N := by
  let b := IsZLattice.basis L
  let c := IsZLattice.basis N
  rw [ZLattice.covolume_eq_det _ (finProductBasis L N b c),
    ZLattice.covolume_eq_det _ b, ZLattice.covolume_eq_det _ c]
  have he : Matrix.of (Subtype.val ∘ finProductBasis L N b c) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (Matrix.of (Subtype.val ∘ b)) 0 0 (Matrix.of (Subtype.val ∘ c))) := by
    ext i j
    simp only [Matrix.of_apply, Function.comp_apply]
    rw [finProductBasis, Basis.reindex_apply, Basis.ofZLatticeComap_apply]
    simp only [LinearEquiv.symm_symm, Basis.map_apply]
    obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective j
    cases i <;> cases j <;>
      simp [Basis.prod_apply, prodSubtypeEquiv, Fin.appendEquiv, appendEquiv, Matrix.reindex_apply]
  rw [he, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, abs_mul]


end SingleLatticeCovering.LatticeGeometry

namespace SingleLatticeCovering.LatticeGeometry
open Module MeasureTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


lemma mem_image {ι : Type*} [Fintype ι] [DecidableEq ι] (L : Submodule ℤ (ι → ℝ)) (e : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) (x : ι → ℝ) :
    x ∈ image L e ↔ ∃ l ∈ L, e l=x := by
  change e.symm x ∈ L ↔ _
  constructor
  · intro hx; exact ⟨e.symm x,hx,e.apply_symm_apply x⟩
  · rintro ⟨l,hl,rfl⟩; simpa using hl

lemma image_covolume (L : Submodule ℤ (ι → ℝ)) (e : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    ZLattice.covolume (image L e) = |LinearMap.det e.toLinearMap| * ZLattice.covolume L := by
  let b := IsZLattice.basis L
  let b' : Basis ι ℤ (image L e) := b.ofZLatticeComap ℝ L e.symm
  rw [ZLattice.covolume_eq_det _ b',ZLattice.covolume_eq_det _ b,
    ←Pi.basisFun_det_apply, ←Pi.basisFun_det_apply]
  have he : Subtype.val ∘ b' = e.toLinearMap ∘ (Subtype.val ∘ b) := by
    ext j k
    simp [b', Basis.ofZLatticeComap_apply]
  rw [he, Basis.det_comp, abs_mul]


end SingleLatticeCovering.LatticeGeometry

namespace SingleLatticeCovering.LatticeGeometry
open Module MeasureTheory



lemma single_left {m n : ℕ} (i : Fin m) :
    (Pi.single (Fin.castAdd n i) (1 : ℝ) : Fin (m+n) → ℝ) =
      Fin.append (Pi.single i 1) 0 := by
  ext j
  refine Fin.addCases ?_ ?_ j <;> intro k <;> simp [Pi.single_apply]
  all_goals intro h; have hv := congrArg Fin.val h; simp at hv; omega

lemma single_right {m n : ℕ} (i : Fin n) :
    (Pi.single (Fin.natAdd m i) (1 : ℝ) : Fin (m+n) → ℝ) =
      Fin.append 0 (Pi.single i 1) := by
  ext j
  refine Fin.addCases ?_ ?_ j <;> intro k <;> simp [Pi.single_apply]
  all_goals intro h; have hv := congrArg Fin.val h; simp at hv; omega

lemma triangular_det {m n : ℕ}
    (e : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) (S : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :
    LinearMap.det (triangular e f S).toLinearMap =
      LinearMap.det e.toLinearMap * LinearMap.det f.toLinearMap := by
  rw [←LinearMap.det_toMatrix', ←LinearMap.det_toMatrix' e.toLinearMap,
    ←LinearMap.det_toMatrix' f.toLinearMap]
  have he : LinearMap.toMatrix' (triangular e f S).toLinearMap =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (LinearMap.toMatrix' e.toLinearMap) (LinearMap.toMatrix' S) 0
          (LinearMap.toMatrix' f.toLinearMap)) := by
    ext i j
    obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective j
    cases i <;> cases j <;>
      simp [LinearMap.toMatrix'_apply, single_left, single_right, Matrix.reindex_apply]
  rw [he, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]



theorem triangular_lattice_covolume {m n : ℕ}
    (L : Submodule ℤ (Fin m → ℝ)) (N : Submodule ℤ (Fin n → ℝ))
    [DiscreteTopology L] [DiscreteTopology N] [IsZLattice ℝ L] [IsZLattice ℝ N]
    (e : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) (S : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :
    ZLattice.covolume (image (finProduct L N) (triangular e f S)) =
      |LinearMap.det e.toLinearMap| * ZLattice.covolume L *
        (|LinearMap.det f.toLinearMap| * ZLattice.covolume N) := by
  rw [image_covolume,triangular_det,finProduct_covolume,abs_mul]
  ring


end SingleLatticeCovering.LatticeGeometry

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA _root_.OAI.SingleLatticeCovering.Blocks LatticeGeometry
open scoped BigOperators

namespace Block
lemma lattice_covolume (B : Block) : ZLattice.covolume B.lattice = (B.p : ℝ)⁻¹ :=
  (Classical.choose_spec (line_lattice B.p B.direction B.direction_ne)).2

lemma linear_det (B : Block) : LinearMap.det B.linear.toLinearMap = B.h^B.b := by
  change LinearMap.det (B.h • (LinearMap.id : B.Vec →ₗ[ℝ] B.Vec)) = _
  rw [LinearMap.det_smul]
  simp
lemma physical_covolume (B : Block) :
    ZLattice.covolume (image B.lattice B.linear) = B.det := by
  rw [image_covolume, linear_det, abs_of_pos (pow_pos B.h_pos _), lattice_covolume]
  simp only [det,div_eq_mul_inv]

end Block

namespace Chain
variable {A B : Block}

lemma subLast_eq_sub (c : Chain B) (y : c.Vec) (t : B.Vec) :
    c.subLast y t = y-c.injectLast t := by
  cases c with
  | base B => rfl
  | append c B w =>
    ext j
    refine Fin.addCases ?_ ?_ j <;> intro k <;> simp [subLast,injectLast,appendEquiv]

lemma mem_raw (c : Chain B) (l : c.Vec) : l ∈ c.rawLattice ↔ c.RawMem l := by
  induction c with
  | base B => rfl
  | append c B w ih => exact and_congr (ih _) Iff.rfl

lemma physical_covolume (c : Chain B) : ZLattice.covolume c.physicalLattice = c.det := by
  induction c with
  | base B => exact B.physical_covolume
  | append c B w ih =>
    change ZLattice.covolume (image (finProduct c.rawLattice B.lattice)
      (triangular c.linear B.linear _)) = c.det*B.det
    rw [triangular_lattice_covolume, ←image_covolume, ←image_covolume]
    exact congrArg₂ (fun x y : ℝ => x*y) ih B.physical_covolume

lemma residual_append (c : Chain A) (B : Block) (w : Fin B.b → A.Group)
    (y l : (Chain.append c B w).Vec) :
    y-(Chain.append c B w).linear l =
      Fin.append
        (c.subLast (fun j => y (Fin.castAdd B.b j))
          (A.shift B w (fun j => l (Fin.natAdd c.dim j))) -
          c.linear (fun j => l (Fin.castAdd B.b j)))
        (fun j => y (Fin.natAdd c.dim j)-B.h*l (Fin.natAdd c.dim j)) := by
  rw [subLast_eq_sub]
  ext j
  refine Fin.addCases ?_ ?_ j <;> intro k <;>
    simp [linear,triangular,sub_eq_add_neg,add_comm,add_assoc]



end Chain
end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA _root_.OAI.SingleLatticeCovering.Blocks LatticeGeometry Module Submodule MeasureTheory
open scoped BigOperators

lemma integerLattice_covolume (n : ℕ) : ZLattice.covolume (integerLattice n) = 1 := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume
    (ZSpan.isAddFundamentalDomain (Pi.basisFun ℝ (Fin n)) volume),
    ZSpan.volume_real_fundamentalDomain]
  have hm : Matrix.of (Pi.basisFun ℝ (Fin n)) = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simp [Pi.basisFun_apply,Pi.single_apply,Matrix.one_apply,eq_comm]
  rw [hm,Matrix.det_one,abs_one]
lemma integer_mem (n : ℕ) (k : Fin n → ℤ) : (fun j => (k j : ℝ)) ∈ integerLattice n := by
  apply ((Pi.basisFun ℝ (Fin n)).mem_span_iff_repr_mem ℤ _).mpr
  intro j
  exact ⟨k j,by simp⟩

namespace Chain
variable {B : Block}

lemma full_covolume (c : Chain B) : ZLattice.covolume c.fullLattice = c.det := by
  rw [show c.fullLattice = image (finProduct c.rawLattice (integerLattice B.terminalDim))
    (triangular c.linear (LinearEquiv.refl ℝ _) (c.injectLast.comp B.terminalShift)) from rfl,
    triangular_lattice_covolume,←image_covolume]
  have hc := c.physical_covolume
  have ht := integerLattice_covolume B.terminalDim
  simpa using congrArg₂ (fun x y : ℝ => x*y) hc ht

lemma full_residual (c : Chain B) (y : c.FullVec) (v : c.Vec) (t : Fin B.terminalDim → ℝ) :
    y-c.fullLinear (Fin.append v t) = Fin.append
      (c.subLast (fun j => y (Fin.castAdd B.terminalDim j)) (B.terminalShift t)-c.linear v)
      (fun j => y (Fin.natAdd c.dim j)-t j) := by
  rw [subLast_eq_sub]
  ext j
  refine Fin.addCases ?_ ?_ j <;> intro k <;>
    simp [fullLinear,triangular_append,sub_eq_add_neg,add_comm,add_assoc]



end Chain
end SingleLatticeCovering.Vertical


end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_Residuals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators
open Real
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
noncomputable section
open scoped BigOperators
open MeasureTheory Set
noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators
noncomputable section
open Real Filter Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter Topology Asymptotics
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
noncomputable section
open Module MeasureTheory

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA _root_.OAI.SingleLatticeCovering.Blocks LatticeGeometry Module Submodule MeasureTheory
open scoped BigOperators

namespace Chain
variable {A B : Block}

lemma heights_square_sum (c : Chain B) : ∑ j, c.heights j^2 = c.radiusSq := by
  induction c with
  | base B => simp [heights,radiusSq,blockSum]
  | append c B w ih =>
    simp only [heights,Fin.sum_univ_add,Fin.append_left,Fin.append_right,ih,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    rfl

lemma residual_physical (c : Chain B) (y l : c.Vec) (hl : c.Residual y l) :
    ∀ j, |(y-c.linear l) j| ≤ c.heights j := by
  induction c with
  | base B => exact hl
  | @append A c B w ih =>
    rw [residual_append]
    intro j
    refine Fin.addCases ?_ ?_ j <;> intro k
    · simpa only [heights,Fin.append_left] using ih _ _ hl.1 k
    · simpa only [heights,Fin.append_right] using hl.2 k

lemma heights_nonneg (c : Chain B) : ∀ j, 0 ≤ c.heights j := by
  induction c with
  | base B => exact fun _ => B.h_pos.le
  | append c B w ih =>
    intro j
    refine Fin.addCases ?_ ?_ j <;> intro k
    · simpa only [heights,Fin.append_left] using ih k
    · simpa only [heights,Fin.append_right] using B.h_pos.le

lemma full_residual_square (c : Chain B) (y l : c.FullVec) (hl : c.FullResidual y l) :
    (∑ j, ((y-c.fullLinear l) j)^2) ≤ c.radiusSq+(B.terminalDim : ℝ) := by
  have he : l=Fin.append (fun j => l (Fin.castAdd B.terminalDim j))
      (fun j => l (Fin.natAdd c.dim j)) := by
    ext j
    refine Fin.addCases ?_ ?_ j <;> intro k <;> simp
  rw [he,full_residual,Fin.sum_univ_add]
  simp only [Fin.append_left,Fin.append_right]
  have hp := c.residual_physical _ _ hl.1
  have hsum : (∑ j, ((c.subLast (fun j => y (Fin.castAdd B.terminalDim j))
      (B.terminalShift (fun j => l (Fin.natAdd c.dim j))) -
      c.linear (fun j => l (Fin.castAdd B.terminalDim j))) j)^2) ≤ c.radiusSq := by
    rw [←heights_square_sum]
    apply Finset.sum_le_sum
    intro j _
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (c.heights_nonneg j)).2 (hp j)
  have ht : (∑ j, (y (Fin.natAdd c.dim j)-l (Fin.natAdd c.dim j))^2) ≤ (B.terminalDim : ℝ) := by
    calc
      _ ≤ ∑ j : Fin B.terminalDim, (1 : ℝ) := Finset.sum_le_sum (fun j _ =>
        (sq_le_one_iff_abs_le_one _).mpr (hl.2 j))
      _ = _ := by simp
  exact add_le_add hsum ht



end Chain
end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA _root_.OAI.SingleLatticeCovering.Blocks LatticeGeometry
open scoped BigOperators

namespace Block
lemma shiftDim_bound (B : Block) (d : ℕ) (w : Fin d → B.Group) (l : Fin d → ℝ)
    {S : ℝ} (hS : 0 ≤ S) (hl : ∀ j, |l j| ≤ S) (j : Fin B.b) :
    |B.shiftDim d w l j| ≤ B.h*((d : ℝ)*S) := by
  have _ := hS
  have hp : (0 : ℝ) < B.p := by exact_mod_cast B.prime.pos
  have hsum : |∑ k, ((w k j).val : ℝ)*l k| ≤ (d : ℝ)*((B.p : ℝ)*S) := by
    calc
      _ ≤ ∑ k, |((w k j).val : ℝ)*l k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin d, (B.p : ℝ)*S := by
        apply Finset.sum_le_sum
        intro k _
        rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
        apply mul_le_mul _ (hl k) (abs_nonneg _) (Nat.cast_nonneg _)
        exact_mod_cast (ZMod.val_lt (w k j)).le
      _ = _ := by simp
  calc
    _ = B.h/(B.p : ℝ)*|∑ k, ((w k j).val : ℝ)*l k| := by
      rw [shiftDim,abs_mul,abs_of_pos (div_pos B.h_pos hp)]
    _ ≤ B.h/(B.p : ℝ)*((d : ℝ)*((B.p : ℝ)*S)) :=
      mul_le_mul_of_nonneg_left hsum (div_nonneg B.h_pos.le hp.le)
    _ = _ := by field_simp

lemma shift_bound (A B : Block) (w : Fin B.b → A.Group) (l : B.Vec)
    {S : ℝ} (hS : 0 ≤ S) (hl : ∀ j, |l j| ≤ S) (j : Fin A.b) :
    |A.shift B w l j| ≤ A.h*((B.b : ℝ)*S) := A.shiftDim_bound B.b w l hS hl j
end Block

lemma succ_le_two_power (n : ℕ) : n+1 ≤ 2^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ]; omega

lemma inverse_factor_bound (m n : ℕ) :
    (n+1)*(m+2)^m ≤ (m+n+2)^(m+n) := by
  calc
    _ ≤ 2^n*(m+n+2)^m := Nat.mul_le_mul (succ_le_two_power n)
      (Nat.pow_le_pow_left (by omega) _)
    _ ≤ (m+n+2)^n*(m+n+2)^m := Nat.mul_le_mul_right _
      (Nat.pow_le_pow_left (by omega) _)
    _ = _ := by rw [←pow_add]; congr 1; omega

namespace Chain
variable {B : Block}
lemma injectLast_bound (c : Chain B) (t : B.Vec) {S : ℝ} (hS : 0 ≤ S)
    (ht : ∀ j, |t j| ≤ B.h*S) : ∀ j, |c.injectLast t j| ≤ c.heights j*S := by
  cases c with
  | base B => exact ht
  | append c B w =>
    intro j
    refine Fin.addCases ?_ ?_ j <;> intro k
    · simpa [injectLast,appendEquiv,heights] using mul_nonneg (c.heights_nonneg k) hS
    · simpa [injectLast,appendEquiv,heights] using ht k

lemma inverse_coordinate_bound (c : Chain B) (x : c.Vec) {S : ℝ} (hS : 0 ≤ S)
    (hx : ∀ j, |c.linear x j| ≤ c.heights j*S) :
    ∀ j, |x j| ≤ S*((c.dim+2 : ℕ) : ℝ)^c.dim := by
  induction c generalizing S with
  | base B =>
    intro j
    have hj := hx j
    change |B.h*x j| ≤ B.h*S at hj
    rw [abs_mul,abs_of_pos B.h_pos] at hj
    have hsmall := (mul_le_mul_iff_right₀ B.h_pos).mp hj
    exact hsmall.trans (le_mul_of_one_le_right hS (one_le_pow₀ (by norm_cast; omega) ))
  | @append A c B w ih =>
    let x₁ : c.Vec := fun j => x (Fin.castAdd B.b j)
    let x₂ : B.Vec := fun j => x (Fin.natAdd c.dim j)
    have hdec : x = Fin.append x₁ x₂ := by
      ext j
      refine Fin.addCases ?_ ?_ j <;> intro k <;> simp [x₁,x₂]
    have hlin : (Chain.append c B w).linear x =
        Fin.append (c.linear x₁+c.injectLast (A.shift B w x₂)) (B.h • x₂) := by
      rw [hdec]
      change triangular c.linear B.linear (c.injectLast.comp (A.shiftMap B w))
        (Fin.append x₁ x₂) = _
      rw [triangular_append,LinearMap.comp_apply,Block.shiftMap_apply,Block.linear_apply]
    have h₂ : ∀ j, |x₂ j| ≤ S := by
      intro j
      have hj := hx (Fin.natAdd c.dim j)
      rw [hlin] at hj
      simp only [heights,Fin.append_right,Pi.smul_apply,smul_eq_mul] at hj
      rw [abs_mul,abs_of_pos B.h_pos] at hj
      exact (mul_le_mul_iff_right₀ B.h_pos).mp hj
    have hshift := c.injectLast_bound (A.shift B w x₂) (mul_nonneg (Nat.cast_nonneg _) hS)
      (A.shift_bound B w x₂ hS h₂)
    have h₁ : ∀ j, |c.linear x₁ j| ≤ c.heights j*((B.b+1 : ℕ)*S) := by
      intro j
      have hj := hx (Fin.castAdd B.b j)
      have hj' : |c.linear x₁ j + c.injectLast (A.shift B w x₂) j| ≤ c.heights j*S := by
        rw [hlin] at hj
        simpa only [heights,Fin.append_left,Pi.add_apply] using hj
      calc
        _ = |(c.linear x₁ j + c.injectLast (A.shift B w x₂) j)-
            c.injectLast (A.shift B w x₂) j| := by congr 1; ring
        _ ≤ |c.linear x₁ j + c.injectLast (A.shift B w x₂) j|+
            |c.injectLast (A.shift B w x₂) j| := abs_sub _ _
        _ ≤ c.heights j*S+c.heights j*((B.b : ℝ)*S) := add_le_add hj' (hshift j)
        _ = _ := by push_cast; ring
    have hb := ih x₁ (mul_nonneg (Nat.cast_nonneg _) hS) h₁
    intro j
    refine Fin.addCases ?_ ?_ j <;> intro k
    · have hpow : (((B.b+1 : ℕ) : ℝ)*((c.dim+2 : ℕ) : ℝ)^c.dim) ≤
          ((c.dim+B.b+2 : ℕ) : ℝ)^(c.dim+B.b) := by
        exact_mod_cast inverse_factor_bound c.dim B.b
      calc
        _ ≤ ((B.b+1 : ℕ) : ℝ)*S*((c.dim+2 : ℕ) : ℝ)^c.dim := hb k
        _ = S*((B.b+1 : ℕ)*((c.dim+2 : ℕ) : ℝ)^c.dim) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hpow hS
    · exact (h₂ k).trans (le_mul_of_one_le_right hS (one_le_pow₀ (by norm_cast; omega)))

end Chain
end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA _root_.OAI.SingleLatticeCovering.Blocks LatticeGeometry
open scoped BigOperators

namespace Chain
variable {B : Block}

lemma full_inverse_coordinate_bound (c : Chain B) (x : c.FullVec) {S : ℝ} (hS : 0 ≤ S)
    (hx : ∀ j, |c.fullLinear x j| ≤ (Fin.append c.heights (fun _ => 1)) j*S) :
    ∀ j, |x j| ≤ S*((c.fullDim+2 : ℕ) : ℝ)^c.fullDim := by
  let x₁ : c.Vec := fun j => x (Fin.castAdd B.terminalDim j)
  let x₂ : Fin B.terminalDim → ℝ := fun j => x (Fin.natAdd c.dim j)
  have hdec : x = Fin.append x₁ x₂ := by
    ext j
    refine Fin.addCases ?_ ?_ j <;> intro k <;> simp [x₁,x₂]
  have hlin : c.fullLinear x = Fin.append (c.linear x₁+c.injectLast (B.terminalShift x₂)) x₂ := by
    rw [hdec]
    exact triangular_append c.linear (LinearEquiv.refl ℝ _) _ x₁ x₂
  have h₂ : ∀ j, |x₂ j| ≤ S := by
    intro j
    have hj := hx (Fin.natAdd c.dim j)
    rw [hlin] at hj
    simpa only [Fin.append_right,one_mul] using hj
  have hshift₀ : ∀ j, |B.terminalShift x₂ j| ≤ B.h*((B.terminalDim : ℝ)*S) := by
    simpa only [Block.terminalShift,Block.shiftDimMap_apply] using
      B.shiftDim_bound B.terminalDim (terminalColumns B.b B.p) x₂ hS h₂
  have hshift := c.injectLast_bound (B.terminalShift x₂)
    (mul_nonneg (Nat.cast_nonneg _) hS) hshift₀
  have h₁ : ∀ j, |c.linear x₁ j| ≤ c.heights j*((B.terminalDim+1 : ℕ)*S) := by
    intro j
    have hj := hx (Fin.castAdd B.terminalDim j)
    have hj' : |c.linear x₁ j + c.injectLast (B.terminalShift x₂) j| ≤ c.heights j*S := by
      rw [hlin] at hj
      simpa only [Fin.append_left,Pi.add_apply] using hj
    calc
      _ = |(c.linear x₁ j + c.injectLast (B.terminalShift x₂) j)-
          c.injectLast (B.terminalShift x₂) j| := by congr 1; ring
      _ ≤ |c.linear x₁ j + c.injectLast (B.terminalShift x₂) j|+
          |c.injectLast (B.terminalShift x₂) j| := abs_sub _ _
      _ ≤ c.heights j*S+c.heights j*((B.terminalDim : ℝ)*S) := add_le_add hj' (hshift j)
      _ = _ := by push_cast; ring
  have hb := c.inverse_coordinate_bound x₁ (mul_nonneg (Nat.cast_nonneg _) hS) h₁
  intro j
  refine Fin.addCases ?_ ?_ j <;> intro k
  · have hpow : (((B.terminalDim+1 : ℕ) : ℝ)*((c.dim+2 : ℕ) : ℝ)^c.dim) ≤
        ((c.fullDim+2 : ℕ) : ℝ)^c.fullDim := by
      exact_mod_cast inverse_factor_bound c.dim B.terminalDim
    calc
      _ ≤ ((B.terminalDim+1 : ℕ) : ℝ)*S*((c.dim+2 : ℕ) : ℝ)^c.dim := hb k
      _ = S*((B.terminalDim+1 : ℕ)*((c.dim+2 : ℕ) : ℝ)^c.dim) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow hS
  · exact (h₂ k).trans (le_mul_of_one_le_right hS (one_le_pow₀ (by norm_cast; omega)))

lemma full_residual_physical (c : Chain B) (y l : c.FullVec) (hl : c.FullResidual y l) :
    ∀ j, |(y-c.fullLinear l) j| ≤ (Fin.append c.heights (fun _ => 1)) j := by
  have he : l=Fin.append (fun j => l (Fin.castAdd B.terminalDim j))
      (fun j => l (Fin.natAdd c.dim j)) := by
    ext j
    refine Fin.addCases ?_ ?_ j <;> intro k <;> simp
  rw [he,full_residual]
  intro j
  refine Fin.addCases ?_ ?_ j <;> intro k
  · simpa only [Fin.append_left] using c.residual_physical _ _ hl.1 k
  · simpa only [Fin.append_right] using hl.2 k


lemma raw_coordinate_bound (c : Chain B) (z l : c.FullVec)
    (hz : ∀ j, 0 ≤ z j ∧ z j < 1) (hl : c.FullResidual (c.fullLinear z) l) :
    ∀ j, |l j| ≤ (c.alphabetRadius : ℝ) := by
  have hx := c.full_residual_physical _ _ hl
  rw [←map_sub] at hx
  have hb := c.full_inverse_coordinate_bound (z-l) (by norm_num : (0 : ℝ) ≤ 1)
    (by simpa only [mul_one] using hx)
  intro j
  calc
    _ = |z j-(z-l) j| := by simp
    _ ≤ |z j|+|(z-l) j| := abs_sub _ _
    _ ≤ 1+1*((c.fullDim+2 : ℕ) : ℝ)^c.fullDim := add_le_add
      (by rw [abs_of_nonneg (hz j).1]; exact (hz j).2.le) (hb j)
    _ = _ := by simp [alphabetRadius]

lemma denominators_pos (c : Chain B) : ∀ j, 0 < c.denominators j := by
  induction c with
  | base B => exact fun _ => B.prime.pos
  | append c B w ih =>
    intro j
    exact Fin.addCases (fun k => by simpa [denominators] using ih k)
      (fun k => by simpa [denominators] using B.prime.pos) j

lemma raw_rational (c : Chain B) (l : c.Vec) (hl : c.RawMem l) :
    ∀ j, ∃ k : ℤ, l j=(k : ℝ)/(c.denominators j : ℝ) := by
  induction c with
  | base B =>
    obtain ⟨k,hk,hkl⟩ := hl
    intro j
    exact ⟨k j,(congr_fun hkl j).symm⟩
  | append c B w ih =>
    intro j
    refine Fin.addCases ?_ ?_ j <;> intro k
    · simpa only [denominators,Fin.append_left] using ih _ hl.1 k
    · obtain ⟨v,hv,hvl⟩ := hl.2
      refine ⟨v k,?_⟩
      simpa only [denominators,Fin.append_right,generator] using (congr_fun hvl k).symm

lemma full_raw_rational (c : Chain B) (l : c.FullVec) (hl : l ∈ c.fullRaw) :
    ∀ j, ∃ k : ℤ, l j=(k : ℝ)/(c.fullDenominators j : ℝ) := by
  have hl' : (fun j => l (Fin.castAdd B.terminalDim j)) ∈ c.rawLattice ∧
      (fun j => l (Fin.natAdd c.dim j)) ∈ integerLattice B.terminalDim := hl
  have h₁ := c.raw_rational _ ((c.mem_raw _).mp hl'.1)
  have h₂ := ((Pi.basisFun ℝ (Fin B.terminalDim)).mem_span_iff_repr_mem ℤ _).mp hl'.2
  intro j
  refine Fin.addCases ?_ ?_ j <;> intro k
  · simpa only [fullDenominators,Fin.append_left] using h₁ k
  · obtain ⟨v,hv⟩ := h₂ k
    refine ⟨v,?_⟩
    simpa [fullDenominators] using hv.symm

end Chain


lemma mem_rationalAlphabet (Q p : ℕ) (hp : 0 < p) {x : ℝ}
    (hx : |x| ≤ (Q : ℝ)) (hk : ∃ k : ℤ, x=(k : ℝ)/(p : ℝ)) :
    x ∈ rationalAlphabet Q p := by
  classical
  obtain ⟨k,rfl⟩ := hk
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  rw [abs_div,abs_of_pos hpr,div_le_iff₀ hpr,abs_le] at hx
  apply Finset.mem_image.mpr
  refine ⟨k,Finset.mem_Icc.mpr ⟨?_,?_⟩,rfl⟩
  · exact_mod_cast hx.1
  · exact_mod_cast hx.2

lemma Chain.mem_alphabets {B : Block} (c : Chain B) (z l : c.FullVec)
    (hz : ∀ j, 0 ≤ z j ∧ z j < 1) (hl : c.FullResidual (c.fullLinear z) l)
    (hmem : l ∈ c.fullRaw) : ∀ j, l j ∈ c.alphabets j := by
  intro j
  apply mem_rationalAlphabet _ _ _ (c.raw_coordinate_bound z l hz hl j)
    (c.full_raw_rational l hmem j)
  exact Fin.addCases (fun k => by simpa [Chain.fullDenominators] using c.denominators_pos k)
    (fun _ => by simp [Chain.fullDenominators]) j


end SingleLatticeCovering.Vertical


end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_Patterns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section





noncomputable section
open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal Pointwise
namespace SingleLatticeCovering.Shear

section Haar
variable {T : Type*} [AddCommGroup T] [MeasurableSpace T]
  [MeasurableAdd₂ T] [MeasurableNeg T]
  (μ : Measure T) [IsProbabilityMeasure μ] [IsAddLeftInvariant μ] [IsNegInvariant μ]



lemma measurableSet_translate {A : Set T} (hA : MeasurableSet A) (t : T) :
    MeasurableSet (translate A t) := hA.preimage (by fun_prop)

lemma measure_translate {T : Type*} [AddCommGroup T] [MeasurableSpace T] [MeasurableAdd₂ T] [MeasurableNeg T] (μ : Measure T) [IsProbabilityMeasure μ] [IsAddLeftInvariant μ] [IsNegInvariant μ] (A : Set T) (t : T) : μ (translate A t) = μ A := by
  simp only [translate, sub_eq_add_neg, measure_preimage_add_right]

lemma translate_add {T : Type*} [AddCommGroup T] [MeasurableSpace T] [MeasurableAdd₂ T] [MeasurableNeg T] (A : Set T) (a b : T) :
    translate A (a+b) = translate (translate A a) b := by
  ext x
  simp only [translate, mem_preimage]
  abel_nf

lemma translate_inter {T : Type*} [AddCommGroup T] [MeasurableSpace T] [MeasurableAdd₂ T] [MeasurableNeg T] (A B : Set T) (t : T) :
    translate (A ∩ B) t = translate A t ∩ translate B t := rfl

lemma overlap_common_translate (A B : Set T) (a b : T) :
    μ (translate A a ∩ translate B (a+b)) = μ (A ∩ translate B b) := by
  rw [add_comm a b, translate_add, ← translate_inter, measure_translate]

lemma measurable_overlap {T : Type*} [AddCommGroup T] [MeasurableSpace T] [MeasurableAdd₂ T] [MeasurableNeg T] (μ : Measure T) [IsProbabilityMeasure μ] [IsAddLeftInvariant μ] [IsNegInvariant μ] {A B : Set T} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Measurable (fun t => μ (A ∩ translate B t)) := by
  exact measurable_measure_prodMk_left
    ((hA.preimage measurable_snd).inter (hB.preimage (by fun_prop :
      Measurable (fun z : T × T => z.2-z.1))))


lemma lintegral_overlap {A B : Set T} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∫⁻ t, μ (A ∩ translate B t) ∂μ = μ A * μ B := by
  let f : T × T → T × T := fun z => (z.2, z.2-z.1)
  have hf : MeasurePreserving f (μ.prod μ) (μ.prod μ) := by
    have h := (measurePreserving_prod_add_swap μ μ).comp
      ((measurePreserving_neg μ).prod (MeasurePreserving.id μ))
    simpa [f, Function.comp_def, sub_eq_add_neg] using h
  have hm : MeasurableSet (f ⁻¹' (A ×ˢ B)) := (hA.prod hB).preimage hf.measurable
  calc
    _ = (μ.prod μ) (f ⁻¹' (A ×ˢ B)) := (Measure.prod_apply hm).symm
    _ = (μ.prod μ) (A ×ˢ B) := hf.measure_preimage (hA.prod hB).nullMeasurableSet
    _ = _ := Measure.prod_prod A B

end Haar

section FiniteChoice
variable {X I : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]



lemma simultaneous_choice (s : Finset I) (f : I → X → ℝ≥0∞) (w : I → ℝ≥0∞)
    (hf : ∀ i ∈ s, Measurable (f i))
    (hw0 : ∀ i ∈ s, w i ≠ 0) (hwt : ∀ i ∈ s, w i ≠ ∞)
    (hfint : ∀ i ∈ s, ∫⁻ x, f i x ∂μ ≤ w i)
    (L : ℝ≥0∞) (hL : (s.card : ℝ≥0∞) < L) :
    ∃ x, ∀ i ∈ s, f i x ≤ L * w i := by
  classical
  let F : X → ℝ≥0∞ := fun x => ∑ i ∈ s, (w i)⁻¹ * f i x
  have hF : ∫⁻ x, F x ∂μ ≤ (s.card : ℝ≥0∞) := by
    dsimp [F]
    rw [lintegral_finsetSum s (fun i hi => (hf i hi).const_mul _)]
    calc
      _ = ∑ i ∈ s, (w i)⁻¹ * ∫⁻ x, f i x ∂μ := by
        apply Finset.sum_congr rfl
        intro i hi
        exact lintegral_const_mul _ (hf i hi)
      _ ≤ ∑ i ∈ s, (w i)⁻¹ * w i := Finset.sum_le_sum (fun i hi =>
        mul_le_mul' le_rfl (hfint i hi))
      _ = ∑ _i ∈ s, (1 : ℝ≥0∞) := Finset.sum_congr rfl (fun i hi =>
        ENNReal.inv_mul_cancel (hw0 i hi) (hwt i hi))
      _ = _ := by simp
  have hex : ∃ x, F x < L := by
    by_contra h
    push Not at h
    have hle := lintegral_mono (μ := μ) h
    simp only [lintegral_const, measure_univ, mul_one] at hle
    exact (not_le_of_gt hL) (hle.trans hF)
  obtain ⟨x, hx⟩ := hex
  refine ⟨x, fun i hi => ?_⟩
  have hiF : (w i)⁻¹ * f i x ≤ F x := by
    dsimp [F]
    exact Finset.single_le_sum (f := fun j => (w j)⁻¹ * f j x) (fun _ _ => zero_le) hi
  have hdiv : f i x / w i ≤ L := by
    simpa only [div_eq_mul_inv, mul_comm] using hiF.trans hx.le
  exact (ENNReal.div_le_iff (hw0 i hi) (hwt i hi)).mp hdiv

end FiniteChoice

end SingleLatticeCovering.Shear

namespace SingleLatticeCovering.Shear

universe u



namespace Pattern
variable {α : Type*}

lemma size_le_two_pow {q : ℕ} (p : Pattern α q) : p.size ≤ 2^q := by
  induction p with
  | leaf => simp [size]
  | @mono q v p ih =>
    simpa only [size, pow_succ] using ih.trans (Nat.le_mul_of_pos_right (2^q) (by decide))
  | @split q v p r ih ihr =>
    simp only [size, pow_succ]
    omega

lemma weight_eq {q : ℕ} (p : Pattern α q) (L : ℝ≥0∞) (η : α → ℝ≥0∞) :
    p.weight L η = L^(p.size-1) * p.labelProduct η := by
  induction p with
  | leaf => simp [weight, size, labelProduct]
  | mono v p ih => exact ih
  | split v p r ih ihr =>
    have he : p.size+r.size-1 = 1+(p.size-1)+(r.size-1) := by
      have := p.size_pos
      have := r.size_pos
      omega
    simp only [weight, size, labelProduct, ih, ihr, he, pow_add, pow_one]
    ac_rfl

lemma weight_ne_zero {q : ℕ} (p : Pattern α q) {L : ℝ≥0∞} (hL : L ≠ 0)
    {η : α → ℝ≥0∞} (hη : ∀ a, η a ≠ 0) : p.weight L η ≠ 0 := by
  induction p with
  | leaf a => exact hη a
  | mono v p ih => exact ih
  | split v p r ih ihr => exact mul_ne_zero (mul_ne_zero hL ih) ihr

lemma weight_ne_top {q : ℕ} (p : Pattern α q) {L : ℝ≥0∞} (hL : L ≠ ∞)
    {η : α → ℝ≥0∞} (hη : ∀ a, η a ≠ ∞) : p.weight L η ≠ ∞ := by
  induction p with
  | leaf a => exact hη a
  | mono v p ih => exact ih
  | split v p r ih ihr => exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hL ih) ihr

section Evaluation
variable {E T : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup T]

lemma measurableSet_failure [MeasurableSpace T] [MeasurableAdd₂ T] [MeasurableNeg T]
    (π : E →+ T) {U : α → Set T} (hU : ∀ a, MeasurableSet (U a))
    {q : ℕ} (p : Pattern α q) (Z : Fin q → E) : MeasurableSet (p.failure π U Z) := by
  induction p with
  | leaf a => exact hU a
  | mono v p ih => exact measurableSet_translate (ih _) _
  | split v p r ih ihr =>
    exact (measurableSet_translate (ih _) _).inter (measurableSet_translate (ihr _) _)

end Evaluation
end Pattern



lemma restrictColumns_snoc {E : Type*} {q d : ℕ} (h : q ≤ d) (Z : Fin d → E) (z : E) :
    restrictColumns (h.trans (Nat.le_succ d)) (Fin.snoc Z z) = restrictColumns h Z := by
  funext i
  exact Fin.snoc_castSucc (α := fun _ => E) z Z (Fin.castLE h i)

section Simultaneous
variable {α E T : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup T]
  [MeasurableSpace T] [MeasurableAdd₂ T] [MeasurableNeg T]
  (μ : Measure T) [IsProbabilityMeasure μ] [IsAddLeftInvariant μ] [IsNegInvariant μ]
  (π : E →+ T) (hπ : Function.Surjective π)
  (U : α → Set T) (hU : ∀ a, MeasurableSet (U a))
  (η : α → ℝ≥0∞) (hη0 : ∀ a, η a ≠ 0) (hηt : ∀ a, η a ≠ ∞)
  (hUη : ∀ a, μ (U a) ≤ η a)
  (L : ℝ≥0∞) (hL0 : L ≠ 0) (hLt : L ≠ ∞)

include hπ hU hη0 hηt hUη hL0 hLt




theorem simultaneous_shear_aux (D : ℕ) (P : (q : ℕ) → Finset (Pattern α q))
    (hP : SliceClosed P D) (hcard : ∀ q ≤ D, ((P q).card : ℝ≥0∞) < L) :
    ∃ Z : Fin D → E, ∀ q (hq : q ≤ D) (p : Pattern α q), p ∈ P q →
      μ (p.failure π U (restrictColumns hq Z)) ≤ p.weight L η := by
  classical
  induction D with
  | zero =>
    refine ⟨fun i => Fin.elim0 i, ?_⟩
    intro q hq p hp
    have hq0 : q = 0 := by omega
    subst q
    cases p with
    | leaf a => exact hUη a
  | succ D ih =>
    have hP' : SliceClosed P D := fun q hq p hp => hP q (by omega) p hp
    obtain ⟨Z, hZ⟩ := ih hP' (fun q hq => hcard q (by omega))
    let s := (P (D+1)).filter Pattern.branches
    let f := fun p : Pattern α (D+1) => fun t : T =>
      μ (p.first.failure π U Z ∩ translate (p.second.failure π U Z) t)
    let w := fun p : Pattern α (D+1) => p.first.weight L η * p.second.weight L η
    have hf : ∀ p ∈ s, Measurable (f p) := fun p _ =>
      measurable_overlap μ (p.first.measurableSet_failure π hU Z)
        (p.second.measurableSet_failure π hU Z)
    have hw0 : ∀ p ∈ s, w p ≠ 0 := fun p _ => mul_ne_zero
      (p.first.weight_ne_zero hL0 hη0) (p.second.weight_ne_zero hL0 hη0)
    have hwt : ∀ p ∈ s, w p ≠ ∞ := fun p _ => ENNReal.mul_ne_top
      (p.first.weight_ne_top hLt hηt) (p.second.weight_ne_top hLt hηt)
    have hfint : ∀ p ∈ s, ∫⁻ t, f p t ∂μ ≤ w p := by
      intro p hp
      have hpP : p ∈ P (D+1) := (Finset.mem_filter.mp hp).1
      obtain ⟨hp1,hp2⟩ := hP D (by omega) p hpP
      dsimp [f, w]
      rw [lintegral_overlap μ (p.first.measurableSet_failure π hU Z)
        (p.second.measurableSet_failure π hU Z)]
      exact mul_le_mul' (hZ D le_rfl p.first hp1) (hZ D le_rfl p.second hp2)
    have hsL : (s.card : ℝ≥0∞) < L := lt_of_le_of_lt
      (Nat.cast_le.mpr (Finset.card_filter_le _ _)) (hcard (D+1) le_rfl)
    obtain ⟨t,ht⟩ := simultaneous_choice μ s f w hf hw0 hwt hfint L hsL
    obtain ⟨z,hz⟩ := hπ t
    refine ⟨Fin.snoc Z z, ?_⟩
    intro q hq p hp
    by_cases hqD : q ≤ D
    · rw [show restrictColumns hq (Fin.snoc Z z) = restrictColumns hqD Z from
        restrictColumns_snoc hqD Z z]
      exact hZ q hqD p hp
    · have hqeq : q = D+1 := by omega
      subst q
      simp only [restrictColumns_self]
      cases p with
      | mono v p =>
        have hp' := (hP D (by omega) (.mono v p) hp).1
        simpa only [Pattern.failure, Pattern.weight, Fin.init_snoc, Fin.snoc_last,
          measure_translate, Pattern.first, restrictColumns_self] using hZ D le_rfl p hp'
      | split v p r =>
        have hp' : Pattern.split v p r ∈ s := Finset.mem_filter.mpr ⟨hp, trivial⟩
        have hφ : π ((v+1) • z) = π (v • z)+t := by
          rw [add_smul, one_smul, map_add, hz]
        simp only [Pattern.failure, Fin.init_snoc, Fin.snoc_last, hφ,
          overlap_common_translate, Pattern.weight]
        simpa only [f, w, Pattern.first, Pattern.second, mul_assoc] using ht (.split v p r) hp'


theorem simultaneous_shear (D : ℕ) (P : (q : ℕ) → Finset (Pattern α q))
    (hP : SliceClosed P D)
    (hQ : (∑ q ∈ Finset.range (D+1), ((P q).card : ℝ≥0∞)) < L) :
    ∃ Z : Fin D → E, ∀ q (hq : q ≤ D) (p : Pattern α q), p ∈ P q →
      μ (p.failure π U (restrictColumns hq Z)) ≤
        L^(p.size-1) * p.labelProduct η := by
  obtain ⟨Z,hZ⟩ := simultaneous_shear_aux μ π hπ U hU η hη0 hηt hUη L hL0 hLt D P hP
    (fun q hq => (Finset.single_le_sum (f := fun q => ((P q).card : ℝ≥0∞)) (fun _ _ => zero_le)
      (Finset.mem_range.mpr (by omega : q < D+1))).trans_lt hQ)
  exact ⟨Z, fun q hq p hp => (hZ q hq p hp).trans_eq (p.weight_eq L η)⟩

end Simultaneous

end SingleLatticeCovering.Shear

namespace SingleLatticeCovering.Shear.Pattern
variable {α : Type*}

attribute [local instance] OAI.SingleLatticeCovering.Shear.Pattern.instDecidableEqProdForallFinReal
lemma labelProduct_eq_prod {q : ℕ} (p : Pattern α q) (η : α → ℝ≥0∞) :
    p.labelProduct η = ∏ l ∈ p.points, η l.2 := by
  classical
  induction p with
  | leaf a => simp [points, labelProduct]
  | mono v p ih =>
    rw [points, Finset.prod_image (fun _ _ _ _ h => appendPoint_injective v h)]
    exact ih
  | split v p r ih ihr =>
    rw [points, Finset.prod_union (appendPoint_disjoint _ _ _)]
    rw [Finset.prod_image (fun _ _ _ _ h => appendPoint_injective v h),
      Finset.prod_image (fun _ _ _ _ h => appendPoint_injective (v+1) h)]
    exact congrArg₂ (· * ·) ih ihr

section Semantics
variable {E T : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup T]

lemma linearShift_snoc {q : ℕ} (Z : Fin (q+1) → E) (x : Fin q → ℝ) (v : ℝ) :
    linearShift Z (Fin.snoc x v) = linearShift (Fin.init Z) x + v • Z (Fin.last q) := by
  rw [linearShift, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, linearShift, Fin.init_def]


attribute [local instance] OAI.SingleLatticeCovering.Shear.Pattern.instDecidableEqProdForallFinReal
lemma mem_failure_iff (π : E →+ T) (U : α → Set T) {q : ℕ} (p : Pattern α q)
    (Z : Fin q → E) (x : T) :
    x ∈ p.failure π U Z ↔
      ∀ l ∈ p.points, x ∈ translate (U l.2) (π (linearShift Z l.1)) := by
  classical
  induction p generalizing x with
  | leaf a => simp [failure, points, linearShift, translate]
  | @mono q v p ih =>
    simp only [failure, translate, mem_preimage]
    rw [ih]
    simp only [points, Finset.forall_mem_image, appendPoint, linearShift_snoc, map_add,
      translate, mem_preimage]
    have hs (a b : T) : x-a-b = x-(b+a) := by abel
    simp only [hs]
  | @split q v p r ih ihr =>
    simp only [failure, mem_inter_iff, translate, mem_preimage]
    rw [ih, ihr]
    simp only [points, Finset.forall_mem_union, Finset.forall_mem_image, appendPoint,
      linearShift_snoc, map_add, translate, mem_preimage]
    have hs (a b : T) : x-a-b = x-(b+a) := by abel
    simp only [hs]

lemma failure_eq_intersection (π : E →+ T) (U : α → Set T) {q : ℕ} (p : Pattern α q)
    (Z : Fin q → E) :
    p.failure π U Z = ⋂ l ∈ p.points, translate (U l.2) (π (linearShift Z l.1)) := by
  ext x
  simpa only [mem_iInter] using p.mem_failure_iff π U Z x

end Semantics
end SingleLatticeCovering.Shear.Pattern


end
end
end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_Shears
attribute [-instance] _root_.OAI.SingleLatticeCovering.CoverGeometry.torusMeasure_neg
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal Pointwise

namespace SingleLatticeCovering.Shear
variable {α : Type*}

namespace Pattern
lemma UniqueLabels_slice {q : ℕ} {s : Finset ((Fin (q+1) → ℝ) × α)}
    (hs : UniqueLabels s) (v : ℝ) : UniqueLabels (slice s v) := by
  intro l hl r hr h
  have heq : (appendPoint v l).1 = (appendPoint v r).1 := congrArg (fun x : Fin q → ℝ => Fin.snoc (α := fun _ => ℝ) x v) h
  exact hs _ ((mem_slice _ _ _).mp hl) _ ((mem_slice _ _ _).mp hr) heq

lemma SuffixBinary_slice {q : ℕ} {s : Finset ((Fin (q+1) → ℝ) × α)}
    (hs : SuffixBinary s) (v : ℝ) : SuffixBinary (slice s v) := by
  intro j y
  obtain ⟨a,ha⟩ := hs j.castSucc (Fin.snoc (α := fun _ => ℝ) y v)
  refine ⟨a, ?_⟩
  intro l hl hy
  have htail : ∀ k : Fin (q+1), j.castSucc < k →
      (appendPoint v l).1 k = (Fin.snoc (α := fun _ => ℝ) y v) k := by
    intro k
    refine Fin.lastCases ?_ (fun k => ?_) k
    · intro hk
      simp only [appendPoint, Fin.snoc_last]
    · intro hk
      simp only [appendPoint, Fin.snoc_castSucc]
      exact hy k (by simpa using hk)
  simpa only [appendPoint, Fin.snoc_castSucc] using ha _ ((mem_slice _ _ _).mp hl) htail

lemma suffix_last_bound {q : ℕ} {s : Finset ((Fin (q+1) → ℝ) × α)}
    (hs : SuffixBinary s) : ∃ v : ℝ, ∀ l ∈ s,
      l.1 (Fin.last q) = v ∨ l.1 (Fin.last q) = v+1 := by
  obtain ⟨v,hv⟩ := hs (Fin.last q) 0
  refine ⟨v, fun l hl => hv l hl ?_⟩
  intro k hk
  exact False.elim ((not_lt_of_ge (Fin.le_last k)) hk)

attribute [local instance] OAI.SingleLatticeCovering.Shear.instDecidableEqProdForallFinReal_solutions
lemma slice_partition {q : ℕ} {s : Finset ((Fin (q+1) → ℝ) × α)} (v : ℝ)
    (hv : ∀ l ∈ s, l.1 (Fin.last q) = v ∨ l.1 (Fin.last q) = v+1) :
    s = (slice s v).image (appendPoint v) ∪ (slice s (v+1)).image (appendPoint (v+1)) := by
  classical
  have hin (l : (Fin (q+1) → ℝ) × α) (a : ℝ) (hl : l ∈ s) (ha : l.1 (Fin.last q)=a) :
      l ∈ (slice s a).image (appendPoint a) := by
    have heq : appendPoint a (Fin.init l.1, l.2) = l := by
      simp only [appendPoint, ← ha, Fin.snoc_init_self]
    exact Finset.mem_image.mpr ⟨(Fin.init l.1,l.2), (mem_slice _ _ _).mpr (heq.symm ▸ hl), heq⟩
  ext l
  constructor
  · intro hl
    rcases hv l hl with h | h
    · exact Finset.mem_union_left _ (hin l v hl h)
    · exact Finset.mem_union_right _ (hin l (v+1) hl h)
  · intro hl
    rcases Finset.mem_union.mp hl with hl | hl
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hl
      exact (mem_slice _ _ _).mp ha
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hl
      exact (mem_slice _ _ _).mp ha


lemma exists_tree {q : ℕ} (s : Finset ((Fin q → ℝ) × α)) (hs : SourcePattern s) :
    ∃ p : Pattern α q, p.points=s := by
  classical
  induction q with
  | zero =>
    obtain ⟨a,ha⟩ := hs.1
    refine ⟨.leaf a.2, ?_⟩
    have hcoord (l : (Fin 0 → ℝ) × α) : l.1=0 := by ext i; exact Fin.elim0 i
    ext l
    simp only [points, Finset.mem_singleton]
    constructor
    · rintro rfl
      convert ha using 1
      all_goals try with_reducible_and_instances rfl
      exact Prod.ext (hcoord a).symm rfl
    · intro hl
      exact Prod.ext (hcoord l) (hs.2.1 l hl a ha ((hcoord l).trans (hcoord a).symm))
  | succ q ih =>
    obtain ⟨v,hv⟩ := suffix_last_bound hs.2.2
    have hpart := slice_partition v hv
    have h0 := UniqueLabels_slice hs.2.1 v
    have h1 := UniqueLabels_slice hs.2.1 (v+1)
    have hb0 := SuffixBinary_slice hs.2.2 v
    have hb1 := SuffixBinary_slice hs.2.2 (v+1)
    by_cases hn0 : (slice s v).Nonempty
    · obtain ⟨p,hp⟩ := ih _ ⟨hn0,h0,hb0⟩
      by_cases hn1 : (slice s (v+1)).Nonempty
      · obtain ⟨r,hr⟩ := ih _ ⟨hn1,h1,hb1⟩
        exact ⟨.split v p r, by rw [points, hp, hr, ← hpart]⟩
      · have he := Finset.not_nonempty_iff_eq_empty.mp hn1
        exact ⟨.mono v p, by simpa only [points, hp, he, Finset.image_empty, Finset.union_empty] using hpart.symm⟩
    · have he := Finset.not_nonempty_iff_eq_empty.mp hn0
      have hn1 : (slice s (v+1)).Nonempty := by
        by_contra hn1
        have he1 := Finset.not_nonempty_iff_eq_empty.mp hn1
        simp only [he, he1, Finset.image_empty, Finset.union_self] at hpart
        exact hs.1.ne_empty hpart
      obtain ⟨r,hr⟩ := ih _ ⟨hn1,h1,hb1⟩
      exact ⟨.mono (v+1) r, by simpa only [points, hr, he, Finset.image_empty, Finset.empty_union] using hpart.symm⟩

end Pattern
end SingleLatticeCovering.Shear

namespace SingleLatticeCovering.Shear
open Pattern
variable {α : Type*}


lemma encodeFamily_card_le (S : (q : ℕ) → Finset (Finset ((Fin q → ℝ) × α))) (q : ℕ) :
    (encodeFamily S q).card ≤ (S q).card := by
  classical
  rw [encodeFamily, Finset.card_preimage]
  exact Finset.card_filter_le _ _


lemma encodeFamily_sliceClosed (S : (q : ℕ) → Finset (Finset ((Fin q → ℝ) × α)))
    (D : ℕ) (hS : SourceSliceClosed S D) : SliceClosed (encodeFamily S) D := by
  intro q hq p hp
  have hp' := (mem_encodeFamily S (q+1) p).mp hp
  cases p with
  | mono v p =>
    have hm : p.points ∈ S q := by
      simpa only [slice_mono] using hS q hq _ hp' v (by simpa only [slice_mono] using p.points_nonempty)
    exact ⟨(mem_encodeFamily _ _ _).mpr hm, (mem_encodeFamily _ _ _).mpr hm⟩
  | split v p r =>
    have hm : p.points ∈ S q := by
      simpa only [slice_split_left] using hS q hq _ hp' v (by simpa only [slice_split_left] using p.points_nonempty)
    have hn : r.points ∈ S q := by
      simpa only [slice_split_right] using hS q hq _ hp' (v+1) (by simpa only [slice_split_right] using r.points_nonempty)
    exact ⟨(mem_encodeFamily _ _ _).mpr hm, (mem_encodeFamily _ _ _).mpr hn⟩

section Endpoint
variable {E T : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup T]
  [MeasurableSpace T] [MeasurableAdd₂ T] [MeasurableNeg T]
  (μ : Measure T) [IsProbabilityMeasure μ] [IsAddLeftInvariant μ] [IsNegInvariant μ]
  (π : E →+ T) (hπ : Function.Surjective π)
  (U : α → Set T) (hU : ∀ a, MeasurableSet (U a))
  (η : α → ℝ≥0∞) (hη0 : ∀ a, η a ≠ 0) (hηt : ∀ a, η a ≠ ∞)
  (hUη : ∀ a, μ (U a) ≤ η a)
  (L : ℝ≥0∞) (hL0 : L ≠ 0) (hLt : L ≠ ∞)

include hπ hU hη0 hηt hUη hL0 hLt



theorem source_simultaneous_shear (D : ℕ)
    (S : (q : ℕ) → Finset (Finset ((Fin q → ℝ) × α)))
    (hsource : ∀ q ≤ D, ∀ s ∈ S q, SourcePattern s)
    (hslice : SourceSliceClosed S D)
    (hQ : (∑ q ∈ Finset.range (D+1), ((S q).card : ℝ≥0∞)) < L) :
    ∃ Z : Fin D → E, ∀ q (hq : q ≤ D) (s : Finset ((Fin q → ℝ) × α)), s ∈ S q →
      μ (⋂ l ∈ s, translate (U l.2) (π (linearShift (restrictColumns hq Z) l.1))) ≤
        L^(s.card-1) * ∏ l ∈ s, η l.2 := by
  classical
  have hbudget : (∑ q ∈ Finset.range (D+1), ((encodeFamily S q).card : ℝ≥0∞)) < L :=
    (Finset.sum_le_sum (fun q _ => Nat.cast_le.mpr (encodeFamily_card_le S q))).trans_lt hQ
  obtain ⟨Z,hZ⟩ := simultaneous_shear μ π hπ U hU η hη0 hηt hUη L hL0 hLt D
    (encodeFamily S) (encodeFamily_sliceClosed S D hslice) hbudget
  refine ⟨Z, ?_⟩
  intro q hq s hs
  obtain ⟨p,hp⟩ := exists_tree s (hsource q hq s hs)
  have hm : p ∈ encodeFamily S q := (mem_encodeFamily _ _ _).mpr (hp.symm ▸ hs)
  have h := hZ q hq p hm
  rw [failure_eq_intersection, ← points_card, labelProduct_eq_prod, hp] at h
  exact h

end Endpoint
end SingleLatticeCovering.Shear



namespace SingleLatticeCovering.Shear
open scoped BigOperators

lemma source_card_le_two_pow {α : Type*} {q : ℕ}
    {s : Finset ((Fin q → ℝ) × α)} (hs : SourcePattern s) : s.card ≤ 2^q := by
  obtain ⟨p,hp⟩ := Pattern.exists_tree s hs
  rw [←hp,Pattern.points_card]
  exact p.size_le_two_pow



lemma small_subsets_card {α : Type*} (s : Finset α) (k : ℕ) :
    (s.powerset.filter (fun t => t.card ≤ k)).card ≤ (s.card+1)^k := by
  classical
  induction k with
  | zero =>
    have hsub : s.powerset.filter (fun t => t.card ≤ 0) ⊆ {∅} := by
      intro t ht
      have ht0 := (Finset.mem_filter.mp ht).2
      simp only [Nat.le_zero, Finset.card_eq_zero] at ht0
      simpa using ht0
    simpa using Finset.card_le_card hsub
  | succ k ih =>
    let F := s.powerset.filter (fun t => t.card ≤ k)
    have hsub : s.powerset.filter (fun t => t.card ≤ k+1) ⊆
        F ∪ s.biUnion (fun a => F.image (insert a)) := by
      intro t ht
      obtain ⟨hts,htk⟩ := Finset.mem_filter.mp ht
      have hts' := Finset.mem_powerset.mp hts
      by_cases hem : t=∅
      · subst t
        apply Finset.mem_union_left
        simp [F]
      · obtain ⟨a,ha⟩ := Finset.nonempty_iff_ne_empty.mpr hem
        have hE : t.erase a ∈ F := by
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_powerset.mpr ((Finset.erase_subset a t).trans hts'),?_⟩
          have hcard := Finset.card_erase_add_one ha
          omega
        apply Finset.mem_union_right
        exact Finset.mem_biUnion.mpr ⟨a,hts' ha,Finset.mem_image.mpr
          ⟨t.erase a,hE,Finset.insert_erase ha⟩⟩
    calc
      _ ≤ (F ∪ s.biUnion (fun a => F.image (insert a))).card := Finset.card_le_card hsub
      _ ≤ F.card+(s.biUnion (fun a => F.image (insert a))).card := Finset.card_union_le _ _
      _ ≤ F.card+∑ a ∈ s, (F.image (insert a)).card :=
        Nat.add_le_add_left (Finset.card_biUnion_le) _
      _ ≤ F.card+s.card*F.card := by
        apply Nat.add_le_add_left
        simpa using Finset.sum_le_sum (fun a (ha : a ∈ s) => Finset.card_image_le (s := F) (f := insert a))
      _ = (s.card+1)*F.card := by ring
      _ ≤ (s.card+1)*(s.card+1)^k := Nat.mul_le_mul_left _ ih
      _ = _ := by ring

lemma mem_alphabetPoints {α : Type*} (A : ℕ → Finset ℝ) (labels : Finset α) (q : ℕ)
    (l : (Fin q → ℝ) × α) :
    l ∈ alphabetPoints A labels q ↔ (∀ j, l.1 j ∈ A j.val) ∧ l.2 ∈ labels := by
  simp [alphabetPoints,Fintype.mem_piFinset]

lemma mem_allPatterns {α : Type*} (A : ℕ → Finset ℝ) (labels : Finset α) (q : ℕ)
    (s : Finset ((Fin q → ℝ) × α)) : s ∈ allPatterns A labels q ↔
      s ⊆ alphabetPoints A labels q ∧ SourcePattern s := by
  classical
  simp [allPatterns]

lemma allPatterns_sliceClosed {α : Type*} (A : ℕ → Finset ℝ) (labels : Finset α) (D : ℕ) :
    SourceSliceClosed (allPatterns A labels) D := by
  intro q hq s hs v hv
  obtain ⟨hsub,hsource⟩ := (mem_allPatterns A labels (q+1) s).mp hs
  apply (mem_allPatterns A labels q _).mpr
  refine ⟨?_,hv,Pattern.UniqueLabels_slice hsource.2.1 v,
    Pattern.SuffixBinary_slice hsource.2.2 v⟩
  intro l hl
  have hl' := hsub ((Pattern.mem_slice s v l).mp hl)
  obtain ⟨ha,hlabel⟩ := (mem_alphabetPoints A labels (q+1) _).mp hl'
  apply (mem_alphabetPoints A labels q l).mpr
  refine ⟨fun j => ?_,hlabel⟩
  simpa only [Pattern.appendPoint,Fin.snoc_castSucc,Fin.val_castSucc] using ha j.castSucc

lemma allPatterns_card_bound {α : Type*} (A : ℕ → Finset ℝ) (labels : Finset α) (q : ℕ) :
    (allPatterns A labels q).card ≤ ((alphabetPoints A labels q).card+1)^(2^q) := by
  classical
  apply le_trans _ (small_subsets_card (alphabetPoints A labels q) (2^q))
  apply Finset.card_le_card
  intro s hs
  obtain ⟨hsub,hsource⟩ := (mem_allPatterns A labels q s).mp hs
  exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsub,source_card_le_two_pow hsource⟩

lemma allPatterns_total_bound {α : Type*} (A : ℕ → Finset ℝ) (labels : Finset α)
    (D N : ℕ) (hN : ∀ q ≤ D, (alphabetPoints A labels q).card ≤ N) :
    (∑ q ∈ Finset.range (D+1), (allPatterns A labels q).card) ≤ (D+1)*(N+1)^(2^D) := by
  have hf (q : ℕ) (hq : q ∈ Finset.range (D+1)) :
      (allPatterns A labels q).card ≤ (N+1)^(2^D) := by
    have hq' : q ≤ D := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hq
    calc
      _ ≤ ((alphabetPoints A labels q).card+1)^(2^q) := allPatterns_card_bound A labels q
      _ ≤ (N+1)^(2^q) := Nat.pow_le_pow_left (Nat.add_le_add_right (hN q hq') 1) _
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by omega) hq')
  simpa using Finset.sum_le_sum hf


end SingleLatticeCovering.Shear

end
end

section



noncomputable section
open MeasureTheory MeasureTheory.Measure Set Module
open scoped Pointwise ENNReal

namespace SingleLatticeCovering.Completion

section Haar
variable {T : Type*} [AddCommGroup T] [TopologicalSpace T] [IsTopologicalAddGroup T]
  [MeasurableSpace T] [BorelSpace T] [CompactSpace T]
  (μ : Measure T) [IsAddHaarMeasure μ] [IsProbabilityMeasure μ]



lemma add_eq_univ_of_measure_sum {A B : Set T} (hB : MeasurableSet B)
    (h : 1 < μ.real A + μ.real B) : A+B = univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_contra hx
  let C := (fun t : T => x-t) ⁻¹' B
  have hC : MeasurableSet C := hB.preimage (by fun_prop)
  have hm : μ C = μ B := (measurePreserving_sub_left μ x).measure_preimage hB.nullMeasurableSet
  have hd : Disjoint A C := by
    apply Set.disjoint_left.mpr
    intro a ha hc
    apply hx
    exact ⟨a, ha, x-a, hc, by abel_nf⟩
  have hu := measureReal_le_one (μ := μ) (s := A ∪ C)
  rw [measureReal_union hd hC] at hu
  have hmreal : μ.real C = μ.real B := congrArg ENNReal.toReal hm
  rw [hmreal] at hu
  exact (not_le_of_gt h) hu


lemma preimage_image_eq_kernel_union {T : Type*} [AddCommGroup T] [TopologicalSpace T] [IsTopologicalAddGroup T] [MeasurableSpace T] [BorelSpace T] [CompactSpace T] (f : T →+ T) (A : Set T) :
    f ⁻¹' (f '' A) = ⋃ z : f.ker, (fun x : T => x-z) ⁻¹' A := by
  ext x
  simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion]
  constructor
  · rintro ⟨a, ha, hax⟩
    have hz : x-a ∈ f.ker := by simp only [AddMonoidHom.mem_ker, map_sub, hax, sub_self]
    exact ⟨⟨x-a, hz⟩, by simpa using ha⟩
  · rintro ⟨z, hz⟩
    refine ⟨x-z, hz, ?_⟩
    simpa only [map_sub, sub_eq_self] using (show f z = 0 from z.property)


lemma measure_image_le_kernel {T : Type*} [AddCommGroup T] [TopologicalSpace T] [IsTopologicalAddGroup T] [MeasurableSpace T] [BorelSpace T] [CompactSpace T] (μ : Measure T) [IsAddHaarMeasure μ] [IsProbabilityMeasure μ] (f : T →+ T) [Fintype f.ker]
    (hf : MeasurePreserving f μ μ) {A : Set T} (hA : MeasurableSet (f '' A)) :
    μ (f '' A) ≤ (Fintype.card f.ker : ℝ≥0∞)*μ A := by
  rw [← hf.measure_preimage hA.nullMeasurableSet, preimage_image_eq_kernel_union]
  calc
    _ ≤ ∑ z : f.ker, μ ((fun x : T => x-z) ⁻¹' A) := measure_iUnion_fintype_le μ _
    _ = _ := by simp only [sub_eq_add_neg, measure_preimage_add_right, Finset.sum_const,
      nsmul_eq_mul, Finset.card_univ]

lemma measureReal_image_le_kernel (f : T →+ T) [Fintype f.ker]
    (hf : MeasurePreserving f μ μ) {A : Set T} (hA : MeasurableSet (f '' A)) :
    μ.real (f '' A) ≤ (Fintype.card f.ker : ℝ)*μ.real A := by
  have h := ENNReal.toReal_mono (by finiteness :
      (Fintype.card f.ker : ℝ≥0∞)*μ A ≠ ∞) (measure_image_le_kernel μ f hf hA)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast, measureReal_def] using h

end Haar

lemma real_nsmul_regular (k : ℕ) (hk : k ≠ 0) : IsSMulRegular ℝ k := by
  intro x y h
  have heq : (k : ℝ)*x = (k : ℝ)*y := by simpa only [nsmul_eq_mul] using h
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr hk) heq

lemma circle_torsion_card (k : ℕ) (hk : k ≠ 0) :
    Nat.card {x : AddCircle (1 : ℝ) // k • x = 0} ≤ k := by
  have hfin := AddCircle.finite_torsion_of_isSMulRegular (1 : ℝ) k (real_nsmul_regular k hk)
  let : Finite {x : AddCircle (1 : ℝ) // k • x = 0} := hfin.to_subtype
  have h := AddCircle.card_torsion_le_of_isSMulRegular (1 : ℝ) k hk (real_nsmul_regular k hk)
  change ENat.card {x : AddCircle (1 : ℝ) // k • x = 0} ≤ (k : ℕ∞) at h
  rw [ENat.card_eq_coe_natCard] at h
  exact_mod_cast h

lemma torus_torsion_card (n k : ℕ) (hk : k ≠ 0) :
    Finite {x : Torus n // k • x = 0} ∧
      Nat.card {x : Torus n // k • x = 0} ≤ k^n := by
  have hfin := AddCircle.finite_torsion_of_isSMulRegular (1 : ℝ) k (real_nsmul_regular k hk)
  let : Finite {x : AddCircle (1 : ℝ) // k • x = 0} := hfin.to_subtype
  let f : {x : Torus n // k • x = 0} → (Fin n → {x : AddCircle (1 : ℝ) // k • x = 0}) :=
    fun x i => ⟨x.1 i, congr_fun x.property i⟩
  have hinj : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congr_fun h i)
  let : Finite {x : Torus n // k • x = 0} := Finite.of_injective f hinj
  refine ⟨inferInstance, ?_⟩
  have hcard := Nat.card_le_card_of_injective f hinj
  have hp := Nat.pow_le_pow_left (circle_torsion_card k hk) n
  exact hcard.trans (by simpa only [Nat.card_fun, Nat.card_fin] using hp)


lemma torus_measure_image_nsmul (n k : ℕ) (hk : k ≠ 0)
    {A : Set (Torus n)} (hA : IsCompact A) :
    (torusMeasure n).real ((fun x : Torus n => k • x) '' A) ≤
      (k : ℝ)^n * (torusMeasure n).real A := by
  let f : Torus n →+ Torus n := nsmulAddMonoidHom k
  have hfin := (torus_torsion_card n k hk).1
  let : Finite f.ker := hfin
  let : Fintype f.ker := Fintype.ofFinite _
  have hf : MeasurePreserving f (torusMeasure n) (torusMeasure n) := by
    change MeasurePreserving (fun x : Torus n => k • x) (torusMeasure n) (torusMeasure n)
    simpa only [natCast_zsmul] using
      (measurePreserving_zsmul (torusMeasure n) (Int.natCast_ne_zero.mpr hk))
  have hcont : Continuous f := by
    change Continuous (fun x : Torus n => k • x)
    fun_prop
  have hmeas : MeasurableSet (f '' A) := (hA.image hcont).measurableSet
  have h := measureReal_image_le_kernel (torusMeasure n) f hf hmeas
  have hc : (Fintype.card f.ker : ℝ) ≤ (k : ℝ)^n := by
    have : Fintype.card f.ker ≤ k^n := by
      rw [← Nat.card_eq_fintype_card]
      exact (torus_torsion_card n k hk).2
    exact_mod_cast this
  exact h.trans (mul_le_mul_of_nonneg_right hc ENNReal.toReal_nonneg)

lemma latticeProjection_surjective {n : ℕ} (L : Submodule ℤ (RealSpace n))
    [DiscreteTopology L] [IsZLattice ℝ L] : Function.Surjective (latticeProjection L) := by
  intro y
  have hy : ∀ i, ∃ x : ℝ, (x : AddCircle (1 : ℝ)) = y i :=
    fun i => QuotientAddGroup.mk'_surjective _ (y i)
  choose x hx using hy
  refine ⟨(latticeBasis L).equivFun.symm x, ?_⟩
  ext i
  change (((latticeBasis L).equivFun ((latticeBasis L).equivFun.symm x)) i :
    AddCircle (1 : ℝ)) = y i
  rw [LinearEquiv.apply_symm_apply]
  exact hx i

lemma latticeProjection_eq_zero_iff {n : ℕ} (L : Submodule ℤ (RealSpace n))
    [DiscreteTopology L] [IsZLattice ℝ L] (x : RealSpace n) :
    latticeProjection L x = 0 ↔ x ∈ L := by
  have hspan : Submodule.span ℤ (Set.range (latticeBasis L)) = L :=
    (IsZLattice.basis L).ofZLatticeBasis_span ℝ
  have hcoords : x ∈ L ↔ ∀ i, (latticeBasis L).repr x i ∈ Set.range (algebraMap ℤ ℝ) := by
    conv_lhs => rw [← hspan]
    exact (latticeBasis L).mem_span_iff_repr_mem ℤ x
  rw [hcoords]
  constructor
  · intro h i
    have hi := congr_fun h i
    change (((latticeBasis L).repr x i : ℝ) : AddCircle (1 : ℝ)) = 0 at hi
    obtain ⟨z, hz⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hi
    exact ⟨z, by simpa using hz⟩
  · intro h
    ext i
    change (((latticeBasis L).repr x i : ℝ) : AddCircle (1 : ℝ)) = 0
    apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
    obtain ⟨z, hz⟩ := h i
    exact ⟨z, by simpa using hz⟩

lemma contractLattice_covolume {n : ℕ} (L : Submodule ℤ (RealSpace n))
    [DiscreteTopology L] [IsZLattice ℝ L] (a : ℝ) (ha : 0 < a) :
    ZLattice.covolume (contractLattice L a ha.ne') = a⁻¹^n * ZLattice.covolume L := by
  let b := IsZLattice.basis L
  let e := LinearEquiv.smulOfNeZero ℝ (RealSpace n) a ha.ne'
  let b' := b.ofZLatticeComap ℝ L e
  let : DiscreteTopology (ZLattice.comap ℝ L e.toLinearMap) := contractLattice_discrete L a ha.ne'
  let : IsZLattice ℝ (ZLattice.comap ℝ L e.toLinearMap) := contractLattice_fullSpan L a ha.ne'
  change ZLattice.covolume (ZLattice.comap ℝ L e.toLinearMap) = _
  rw [ZLattice.covolume_eq_det _ b', ZLattice.covolume_eq_det _ b]
  have hm : Matrix.of (Subtype.val ∘ b') = a⁻¹ • (Matrix.of (Subtype.val ∘ b) : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simp only [Matrix.of_apply, Function.comp_apply, Matrix.smul_apply,
      Basis.ofZLatticeComap_apply, LinearEquiv.smulOfNeZero_symm_apply, Pi.smul_apply,
      smul_eq_mul, b', e]
    simp [Units.smul_def]
  rw [hm, Matrix.det_smul, abs_mul, abs_pow, abs_of_pos (inv_pos.mpr ha), Fintype.card_fin]

lemma cover_contractLattice {n : ℕ} (L : Submodule ℤ (RealSpace n)) (K : Set (RealSpace n))
    (a : ℝ) (ha : a ≠ 0) (hcover : a • K+(L : Set (RealSpace n)) = univ) :
    K+(contractLattice L a ha : Set (RealSpace n)) = univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hx : a • x ∈ a • K+(L : Set (RealSpace n)) := by rw [hcover]; trivial
  obtain ⟨v, hv, z, hz, hvz⟩ := hx
  obtain ⟨y, hy, rfl⟩ := hv
  refine ⟨y, hy, a⁻¹ • z, ?_, ?_⟩
  · change a • (a⁻¹ • z) ∈ L
    rw [smul_smul, mul_inv_cancel₀ ha, one_smul]
    exact hz
  · have h := congrArg (fun w : RealSpace n => a⁻¹ • w) hvz
    simpa only [smul_add, smul_smul, inv_mul_cancel₀ ha, one_smul] using h

lemma one_add_inv_pow_le_exp (n : ℕ) (hn : n ≠ 0) :
    (1+(n : ℝ)⁻¹)^n ≤ Real.exp 1 := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1+(n : ℝ)⁻¹)
    (by simpa only [add_comm] using Real.add_one_le_exp (n : ℝ)⁻¹) n
  rw [← Real.exp_nat_mul, mul_inv_cancel₀ hnR] at h
  exact h

lemma small_hole_strict {n : ℕ} (hn : 2 ≤ n) {δ : ℝ}
    (hδ : δ ≤ 1/(n : ℝ)^(2*n)) : δ < (1-δ)/(n : ℝ)^n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 2 ≤ (n : ℝ)^n := hnR.trans (le_self_pow₀ (by linarith) (by omega))
  have hp₀ : 0 < (n : ℝ)^n := by linarith
  rw [Nat.mul_comm 2 n, pow_mul] at hδ
  have hδ' := (le_div_iff₀ (sq_pos_of_pos hp₀)).mp hδ
  apply (lt_div_iff₀ hp₀).mpr
  have hpos : 0 < ((n : ℝ)^n)^2 - (n : ℝ)^n - 1 := by nlinarith
  have hratio : (1/((n : ℝ)^n)^2)*((n : ℝ)^n+1) < 1 := by
    rw [div_mul_eq_mul_div, one_mul]
    apply (div_lt_one (sq_pos_of_pos hp₀)).mpr
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hδ (by positivity : 0 ≤ (n : ℝ)^n+1)
  nlinarith




end SingleLatticeCovering.Completion

end
end

end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_Completion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace SingleLatticeCovering.Completion
open MeasureTheory MeasureTheory.Measure Set Module
open scoped Pointwise ENNReal

lemma projection_mem_image_iff {n : ℕ}
    (Γ : Submodule ℤ (RealSpace n)) (π : RealSpace n →+ Torus n)
    (hker : ∀ x, π x = 0 ↔ x ∈ Γ) (K : Set (RealSpace n)) (x : RealSpace n) :
    π x ∈ π '' K ↔ x ∈ K+(Γ : Set (RealSpace n)) := by
  constructor
  · rintro ⟨a,ha,hax⟩
    refine ⟨a,ha,x-a,?_,by abel_nf⟩
    apply (hker _).mp
    simp [map_sub,hax]
  · rintro ⟨a,ha,z,hz,rfl⟩
    refine ⟨a,ha,?_⟩
    simp [map_add,(hker z).mpr hz]

lemma projection_image_eq_univ {n : ℕ}
    (Γ : Submodule ℤ (RealSpace n)) (π : RealSpace n →+ Torus n)
    (hsurj : Function.Surjective π) (hker : ∀ x, π x = 0 ↔ x ∈ Γ)
    (K : Set (RealSpace n)) : π '' K = univ ↔ K+(Γ : Set (RealSpace n)) = univ := by
  constructor
  · intro h
    apply Set.eq_univ_of_forall
    intro x
    apply (projection_mem_image_iff Γ π hker K x).mp
    rw [h]; trivial
  · intro h
    apply Set.eq_univ_of_forall
    intro t
    obtain ⟨x,rfl⟩ := hsurj t
    apply (projection_mem_image_iff Γ π hker K x).mpr
    rw [h]; trivial

lemma projection_scalar_image {n : ℕ} (π : RealSpace n →+ Torus n)
    (K : Set (RealSpace n)) (k : ℕ) (hk : k ≠ 0) :
    (fun t : Torus n => k • t) '' (π '' ((k : ℝ)⁻¹ • K)) = π '' K := by
  have heq (x : RealSpace n) : k • π ((k : ℝ)⁻¹ • x) = π x := by
    rw [← map_nsmul]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul ℝ,smul_smul,mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hk),one_smul]
  rw [←Set.image_smul,Set.image_image,Set.image_image]
  simp only [heq]




theorem completion_with_projection {n : ℕ}
    (Γ : Submodule ℤ (RealSpace n)) (π : RealSpace n →ₜ+ Torus n)
    (hsurj : Function.Surjective π) (hker : ∀ x, π x = 0 ↔ x ∈ Γ)
    (K : Set (RealSpace n)) (hK : IsCompact K) (hconv : Convex ℝ K)
    (k : ℕ) (hk : 0 < k)
    (hhole : 1-(torusMeasure n).real (π '' K) <
      (torusMeasure n).real (π '' K)/(k : ℝ)^n) :
    ((1+(k : ℝ)⁻¹) • K)+(Γ : Set (RealSpace n)) = univ := by
  let A := π '' K
  let B := π '' ((k : ℝ)⁻¹ • K)
  have hB : IsCompact B := (hK.smul _).image π.continuous
  have hm : (torusMeasure n).real A ≤ (k : ℝ)^n*(torusMeasure n).real B := by
    have h := torus_measure_image_nsmul n k hk.ne' hB
    change (torusMeasure n).real ((fun t : Torus n => k • t) ''
      (π.toAddMonoidHom '' ((k : ℝ)⁻¹ • K))) ≤ _ at h
    rw [projection_scalar_image π.toAddMonoidHom K k hk.ne'] at h
    exact h
  have hkpow : 0 < (k : ℝ)^n := pow_pos (Nat.cast_pos.mpr hk) n
  have hlow : 1-(torusMeasure n).real A < (torusMeasure n).real B := by
    have hh := (lt_div_iff₀ hkpow).mp hhole
    exact (mul_lt_mul_iff_right₀ hkpow).mp (by dsimp [A] at *; nlinarith)
  have hsum : A+B = univ := add_eq_univ_of_measure_sum (torusMeasure n) hB.measurableSet
    (by linarith)
  apply (projection_image_eq_univ Γ π.toAddMonoidHom hsurj hker _).mp
  rw [hconv.add_smul (show (0 : ℝ) ≤ 1 by norm_num) (inv_nonneg.mpr (Nat.cast_nonneg k)),
    one_smul,Set.image_add]
  exact hsum


theorem complete_almost_cover_projection {n : ℕ} (hn : 2 ≤ n)
    (Γ : Submodule ℤ (RealSpace n)) [DiscreteTopology Γ] [IsZLattice ℝ Γ]
    (π : RealSpace n →ₜ+ Torus n) (hsurj : Function.Surjective π)
    (hker : ∀ x, π x = 0 ↔ x ∈ Γ)
    (K : Set (RealSpace n)) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hhole : 1-(torusMeasure n).real (π '' K) ≤ 1/(n : ℝ)^(2*n)) :
    ∃ (L' : Submodule ℤ (RealSpace n)) (_ : DiscreteTopology L'),
      IsZLattice ℝ L' ∧ K+(L' : Set (RealSpace n)) = univ ∧
      (volume K).toReal / ZLattice.covolume L' ≤
        Real.exp 1*((volume K).toReal / ZLattice.covolume Γ) := by
  have hn₀ : 0 < n := by omega
  let a := 1+(n : ℝ)⁻¹
  have ha : 0 < a := by dsimp [a]; positivity
  let L' := contractLattice Γ a ha.ne'
  refine ⟨L',inferInstance,inferInstance,?_,?_⟩
  · apply cover_contractLattice Γ K a ha.ne'
    apply completion_with_projection Γ π hsurj hker K hK hconv n hn₀
    have h := small_hole_strict hn hhole
    simpa only [sub_sub_cancel] using h
  · have heq : (volume K).toReal / ZLattice.covolume L' =
        a^n*((volume K).toReal / ZLattice.covolume Γ) := by
      rw [contractLattice_covolume Γ a ha,inv_pow,div_mul_eq_div_div,div_inv_eq_mul]
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right (one_add_inv_pow_le_exp n hn₀.ne')
      (div_nonneg ENNReal.toReal_nonneg (ZLattice.covolume_pos Γ).le)


end SingleLatticeCovering.Completion

namespace SingleLatticeCovering.Shear
open MeasureTheory
open scoped BigOperators ENNReal

lemma source_pattern_mono {α : Type*} {q : ℕ}
    {s t : Finset ((Fin q → ℝ) × α)} (hs : SourcePattern s)
    (ht : t.Nonempty) (hts : t ⊆ s) : SourcePattern t := by
  refine ⟨ht,fun l hl r hr he => hs.2.1 l (hts hl) r (hts hr) he,?_⟩
  intro j y
  obtain ⟨v,hv⟩ := hs.2.2 j y
  exact ⟨v,fun l hl hy => hv l (hts hl) hy⟩



lemma retained_load {A : Type*} (s : Finset A) (u : A → ℝ) (τ : ℝ) (hτ : 0 ≤ τ) :
    (∑ x ∈ s, u x) - (s.card : ℝ)*τ ≤ ∑ x ∈ s.filter (fun x => τ ≤ u x), u x := by
  classical
  have hdrop : ∑ x ∈ s.filter (fun x => ¬τ ≤ u x), u x ≤ (s.card : ℝ)*τ := by
    calc
      _ ≤ ∑ x ∈ s.filter (fun x => ¬τ ≤ u x), τ := by
        apply Finset.sum_le_sum
        intro x hx
        exact (lt_of_not_ge (Finset.mem_filter.mp hx).2).le
      _ = ((s.filter (fun x => ¬τ ≤ u x)).card : ℝ)*τ := by simp
      _ ≤ (s.card : ℝ)*τ := mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_filter_le s _) hτ
  have hsum := Finset.sum_filter_add_sum_filter_not s (fun x => τ ≤ u x) u
  linarith

lemma retain_source_pattern {α : Type*} {q : ℕ}
    (s : Finset ((Fin q → ℝ) × α)) (hs : SourcePattern s)
    (u : α → ℝ) (τ A : ℝ) (hτ : 0 ≤ τ) (hA : 0 < A)
    (hload : A+(2^q : ℕ)*τ ≤ ∑ l ∈ s, u l.2) :
    ∃ t : Finset ((Fin q → ℝ) × α), t ⊆ s ∧ SourcePattern t ∧
      (∀ l ∈ t, τ ≤ u l.2) ∧ A ≤ ∑ l ∈ t, u l.2 := by
  classical
  let t := s.filter (fun l => τ ≤ u l.2)
  have hc : (s.card : ℝ) ≤ (2^q : ℕ) := by exact_mod_cast source_card_le_two_pow hs
  have htload : A ≤ ∑ l ∈ t, u l.2 := by
    have hd := retained_load s (fun l => u l.2) τ hτ
    have hm := mul_le_mul_of_nonneg_right hc hτ
    change A ≤ ∑ l ∈ s.filter (fun l => τ ≤ u l.2), u l.2
    linarith
  have hn : t.Nonempty := by
    by_contra he
    rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.sum_empty] at htload
    exact (not_le_of_gt hA) htload
  refine ⟨t,Finset.filter_subset _ _,source_pattern_mono hs hn (Finset.filter_subset _ _),?_,htload⟩
  exact fun l hl => (Finset.mem_filter.mp hl).2

lemma finite_weight_load_bounds {A : Type*} (s : Finset A) (w u : A → ℝ)
    (κ ρ c C ε : ℝ) (hρ : 0 ≤ ρ) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hweight : κ ≤ ∑ x ∈ s, w x)
    (hlo : ∀ x ∈ s, c*ρ*w x ≤ u x)
    (hup : ∀ x ∈ s, u x ≤ C*ρ*w x)
    (hcap : ∀ x ∈ s, w x ≤ ε) :
    c*κ*ρ ≤ ∑ x ∈ s, u x ∧ ∀ x ∈ s, u x ≤ C*ρ*ε := by
  constructor
  · have hs := Finset.sum_le_sum hlo
    rw [←Finset.mul_sum] at hs
    have hm := mul_le_mul_of_nonneg_left hweight (mul_nonneg hc hρ)
    nlinarith
  · intro x hx
    exact (hup x hx).trans (mul_le_mul_of_nonneg_left (hcap x hx) (mul_nonneg hC hρ))

lemma exponential_pattern_bound {α : Type*} {q : ℕ}
    (s : Finset ((Fin q → ℝ) × α)) (hs : SourcePattern s)
    (u : α → ℝ) (L A : ℝ) (hL : 1 ≤ L) (hA : A ≤ ∑ l ∈ s, u l.2) :
    ENNReal.ofReal L^(s.card-1) * (∏ l ∈ s, ENNReal.ofReal (Real.exp (-u l.2/2))) ≤
      ENNReal.ofReal (Real.exp ((2^q : ℕ)*Real.log L-A/2)) := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hp : (∏ l ∈ s, ENNReal.ofReal (Real.exp (-u l.2/2))) =
      ENNReal.ofReal (Real.exp (-(∑ l ∈ s, u l.2)/2)) := by
    rw [←ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le),←Real.exp_sum]
    congr 2
    rw [←Finset.sum_div,Finset.sum_neg_distrib]
  rw [hp,←ENNReal.ofReal_pow hL0.le,←ENNReal.ofReal_mul (pow_nonneg hL0.le _)]
  have hpow : L^(s.card-1)=Real.exp ((s.card-1 : ℕ)*Real.log L) := by
    rw [Real.exp_nat_mul,Real.exp_log hL0]
  rw [hpow,←Real.exp_add]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hc : ((s.card-1 : ℕ) : ℝ) ≤ (2^q : ℕ) := by
    exact_mod_cast (Nat.sub_le s.card 1).trans (source_card_le_two_pow hs)
  have hm := mul_le_mul_of_nonneg_right hc (Real.log_nonneg hL)
  linarith


end SingleLatticeCovering.Shear

namespace SingleLatticeCovering.Vertical
open scoped BigOperators

lemma mem_labelPattern {α : Type*} {D : ℕ} (P : Finset (Fin D → ℝ))
    (a : (Fin D → ℝ) → α) (l : (Fin D → ℝ) × α) :
    l ∈ labelPattern P a ↔ l.1 ∈ P ∧ l.2=a l.1 := by
  classical
  simp [labelPattern,Prod.ext_iff,eq_comm]

lemma labelPattern_source {α : Type*} {D : ℕ} (P : Finset (Fin D → ℝ))
    (a : (Fin D → ℝ) → α) (hP : P.Nonempty) (hPb : SuffixBinary P) :
    Shear.SourcePattern (labelPattern P a) := by
  classical
  refine ⟨Finset.Nonempty.image hP _,?_,?_⟩
  · intro l hl r hr he
    obtain ⟨_,hl⟩ := (mem_labelPattern P a l).mp hl
    obtain ⟨_,hr⟩ := (mem_labelPattern P a r).mp hr
    rw [hl,hr,he]
  · intro j y
    obtain ⟨v,hv⟩ := hPb j y
    exact ⟨v,fun l hl hy => hv l.1 ((mem_labelPattern P a l).mp hl).1 hy⟩

lemma sum_labelPattern {α : Type*} {D : ℕ} (P : Finset (Fin D → ℝ))
    (a : (Fin D → ℝ) → α) (f : ((Fin D → ℝ) × α) → ℝ) :
    ∑ l ∈ labelPattern P a, f l = ∑ l ∈ P, f (l,a l) := by
  classical
  apply Finset.sum_image
  intro x hx y hy he
  exact congrArg Prod.fst he


end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open MeasureTheory Folded
open scoped BigOperators





theorem section_labeled_retained {α : Type*} [Fintype α] {m D : ℕ}
    (P : Finset (Fin D → ℝ)) (hP : P.Nonempty) (hPb : SuffixBinary P)
    (N : Submodule ℤ (Fin D → ℝ)) (hraw : ∀ l ∈ P, l ∈ N)
    (M : (Fin D → ℝ) ≃ₗ[ℝ] (Fin D → ℝ)) (y : Fin D → ℝ)
    (K : Set (Fin (m+D) → ℝ)) (J : α → Set (Fin m → ℝ))
    (u : α → ℝ) (w : (Fin D → ℝ) → ℝ) (κ ρ c C ε τ A : ℝ)
    (hρ : 0 ≤ ρ) (hc : 0 ≤ c) (hC : 0 ≤ C) (hτ : 0 ≤ τ) (hA : 0 < A)
    (hweight : κ ≤ ∑ l ∈ P, w l) (hcap : ∀ l ∈ P, w l ≤ ε)
    (hsection : ∀ l ∈ P, ∃ a : α,
      (∀ j ∈ J a, Fin.append j (y-M l) ∈ K) ∧ c*ρ*w l ≤ u a ∧ u a ≤ C*ρ*w l)
    (hload : A+(2^D : ℕ)*τ ≤ c*κ*ρ)
    (alphabet : ℕ → Finset ℝ) (halph : ∀ l ∈ P, ∀ j : Fin D, l j ∈ alphabet j.val) :
    ∃ s : Finset ((Fin D → ℝ) × α),
      s ∈ Shear.allPatterns alphabet (Finset.univ.filter (fun a => τ ≤ u a ∧ u a ≤ C*ρ*ε)) D ∧
      (∀ l ∈ s, l.1 ∈ N) ∧
      (∀ l ∈ s, ∀ j ∈ J l.2, Fin.append j (y-M l.1) ∈ K) ∧
      A ≤ ∑ l ∈ s, u l.2 := by
  classical
  obtain ⟨l₀,hl₀⟩ := hP
  obtain ⟨a₀,ha₀⟩ := hsection l₀ hl₀
  have hex : ∀ l : Fin D → ℝ, ∃ a : α, l ∈ P →
      (∀ j ∈ J a, Fin.append j (y-M l) ∈ K) ∧ c*ρ*w l ≤ u a ∧ u a ≤ C*ρ*w l := by
    intro l
    by_cases hl : l ∈ P
    · obtain ⟨a,ha⟩ := hsection l hl
      exact ⟨a,fun _ => ha⟩
    · exact ⟨a₀,fun h => (hl h).elim⟩
  choose a ha using hex
  have hbnds := Shear.finite_weight_load_bounds P w (fun l => u (a l)) κ ρ c C ε hρ hc hC
    hweight (fun l hl => (ha l hl).2.1) (fun l hl => (ha l hl).2.2) hcap
  let s₀ := labelPattern P a
  have hs₀ : Shear.SourcePattern s₀ := labelPattern_source P a ⟨l₀,hl₀⟩ hPb
  have hload₀ : A+(2^D : ℕ)*τ ≤ ∑ l ∈ s₀, u l.2 := by
    rw [sum_labelPattern]
    exact hload.trans hbnds.1
  obtain ⟨s,hsub,hsource,hthreshold,hsum⟩ :=
    Shear.retain_source_pattern s₀ hs₀ u τ A hτ hA hload₀
  refine ⟨s,?_,?_,?_,hsum⟩
  · apply (Shear.mem_allPatterns _ _ _ _).mpr
    refine ⟨?_,hsource⟩
    intro l hl
    have hmem := hsub hl
    obtain ⟨hlP,hlA⟩ := (mem_labelPattern P a l).mp hmem
    apply (Shear.mem_alphabetPoints _ _ _ _).mpr
    refine ⟨halph l.1 hlP,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hthreshold l hl,?_⟩⟩
    rw [hlA]
    exact hbnds.2 l.1 hlP
  · intro l hl
    exact hraw l.1 ((mem_labelPattern P a l).mp (hsub hl)).1
  · intro l hl
    obtain ⟨hlP,hlA⟩ := (mem_labelPattern P a l).mp (hsub hl)
    rw [hlA]
    exact (ha l.1 hlP).1


end SingleLatticeCovering.Vertical

noncomputable section
namespace SingleLatticeCovering.CoverGeometry
open MeasureTheory LatticeGeometry Completion
open scoped BigOperators Pointwise ENNReal



lemma joined_point_mem {m D : ℕ} (L : Submodule ℤ (Fin m → ℝ))
    (N : Submodule ℤ (Fin D → ℝ)) (M : (Fin D → ℝ) ≃ₗ[ℝ] (Fin D → ℝ))
    (Z : Fin D → (Fin m → ℝ)) {h : Fin m → ℝ} {l : Fin D → ℝ}
    (hh : h ∈ L) (hl : l ∈ N) :
    Fin.append (h+columnMap Z l) (M l) ∈ joinedLattice L N M Z := by
  apply (mem_image _ _ _).mpr
  refine ⟨Fin.append h l,?_,?_⟩
  · simpa only [mem_finProduct,Fin.append_left,Fin.append_right] using ⟨hh,hl⟩
  · exact triangular_append _ _ _ h l

lemma joined_covolume {m D : ℕ} (L : Submodule ℤ (Fin m → ℝ))
    (N : Submodule ℤ (Fin D → ℝ)) [DiscreteTopology L] [DiscreteTopology N]
    [IsZLattice ℝ L] [IsZLattice ℝ N]
    (M : (Fin D → ℝ) ≃ₗ[ℝ] (Fin D → ℝ)) (Z : Fin D → (Fin m → ℝ)) :
    ZLattice.covolume (joinedLattice L N M Z) =
      ZLattice.covolume L * ZLattice.covolume (image N M) := by
  rw [joinedLattice,triangular_lattice_covolume,image_covolume]
  simp



lemma covered_of_section {m D : ℕ} (L : Submodule ℤ (Fin m → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L]
    (N : Submodule ℤ (Fin D → ℝ)) (M : (Fin D → ℝ) ≃ₗ[ℝ] (Fin D → ℝ))
    (Z : Fin D → (Fin m → ℝ)) (K : Set (Fin (m+D) → ℝ))
    (x : Fin m → ℝ) (y l : Fin D → ℝ) (hl : l ∈ N)
    (J : Set (Fin m → ℝ)) (hJ : ∀ j ∈ J, Fin.append j (y-M l) ∈ K)
    (hx : latticeProjection L (x-columnMap Z l) ∈ latticeProjection L '' J) :
    Fin.append x y ∈ K+(joinedLattice L N M Z : Set (Fin (m+D) → ℝ)) := by
  obtain ⟨j,hj,hjx⟩ := hx
  let h := x-columnMap Z l-j
  have hh : h ∈ L := by
    apply (latticeProjection_eq_zero_iff L h).mp
    dsimp [h]
    rw [map_sub]
    simpa only [columnMap_apply] using sub_eq_zero.mpr hjx.symm
  refine ⟨Fin.append j (y-M l),hJ j hj,Fin.append (h+columnMap Z l) (M l),
    joined_point_mem L N M Z hh hl,?_⟩
  ext i
  refine Fin.addCases ?_ ?_ i <;> intro k <;>
    simp only [Pi.add_apply,Fin.append_left,Fin.append_right,Pi.sub_apply,h] <;> ring

lemma horizontal_hole_subset {α : Type*} {m D : ℕ}
    (L : Submodule ℤ (Fin m → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (N : Submodule ℤ (Fin D → ℝ)) (M : (Fin D → ℝ) ≃ₗ[ℝ] (Fin D → ℝ))
    (Z : Fin D → (Fin m → ℝ)) (K : Set (Fin (m+D) → ℝ))
    (J : α → Set (Fin m → ℝ)) (y : Fin D → ℝ)
    (s : Finset ((Fin D → ℝ) × α))
    (hraw : ∀ l ∈ s, l.1 ∈ N)
    (hsection : ∀ l ∈ s, ∀ j ∈ J l.2, Fin.append j (y-M l.1) ∈ K) :
    horizontalHole L K (joinedLattice L N M Z) y ⊆
      ⋂ l ∈ s, Shear.translate ((latticeProjection L '' J l.2)ᶜ)
        (latticeProjection L (Shear.Pattern.linearShift Z l.1)) := by
  rintro t ⟨x,hx,rfl⟩
  simp only [Set.mem_iInter]
  intro l hl
  change latticeProjection L x-latticeProjection L (columnMap Z l.1) ∉ latticeProjection L '' J l.2
  rw [←map_sub]
  intro hc
  exact hx (covered_of_section L N M Z K x y l.1 (hraw l hl) (J l.2) (hsection l hl) hc)



end SingleLatticeCovering.CoverGeometry

namespace SingleLatticeCovering.CoverGeometry
open MeasureTheory LatticeGeometry Completion Shear
open scoped BigOperators Pointwise ENNReal




theorem finite_family_lattice_shear {α : Type*} [Fintype α] {m D : ℕ}
    (L : Submodule ℤ (Fin m → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (N : Submodule ℤ (Fin D → ℝ)) (M : (Fin D → ℝ) ≃ₗ[ℝ] (Fin D → ℝ))
    (K : Set (Fin (m+D) → ℝ)) (J : α → Set (Fin m → ℝ))
    (hJ : ∀ a, IsCompact (J a)) (u : α → ℝ) (labels : Finset α)
    (hhole : ∀ a ∈ labels, torusMeasure m ((latticeProjection L '' J a)ᶜ) ≤
      ENNReal.ofReal (Real.exp (-u a/2)))
    (alphabet : ℕ → Finset ℝ) (Lstar : ℝ) (hLstar : 1 ≤ Lstar)
    (hcost : ((∑ q ∈ Finset.range (D+1),
      (allPatterns alphabet labels q).card : ℕ) : ℝ) < Lstar) :
    ∃ Z : Fin D → (Fin m → ℝ), ∀ (y : Fin D → ℝ)
      (s : Finset ((Fin D → ℝ) × α)), s ∈ allPatterns alphabet labels D →
      (∀ l ∈ s, l.1 ∈ N) →
      (∀ l ∈ s, ∀ j ∈ J l.2, Fin.append j (y-M l.1) ∈ K) →
      ∀ A : ℝ, A ≤ ∑ l ∈ s, u l.2 →
        torusMeasure m (horizontalHole L K (joinedLattice L N M Z) y) ≤
          ENNReal.ofReal (Real.exp ((2^D : ℕ)*Real.log Lstar-A/2)) := by
  classical
  let U : α → Set (Torus m) := fun a => (latticeProjection L '' J a)ᶜ
  have hU : ∀ a, MeasurableSet (U a) := fun a =>
    ((hJ a).image (latticeProjection L).continuous).isClosed.measurableSet.compl
  let η : α → ℝ≥0∞ := fun a => if a ∈ labels then ENNReal.ofReal (Real.exp (-u a/2)) else 1
  have hη0 : ∀ a, η a ≠ 0 := by
    intro a; dsimp [η]; split
    · exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
    · exact one_ne_zero
  have hηt : ∀ a, η a ≠ ∞ := by
    intro a; dsimp [η]; split <;> simp
  have hUη : ∀ a, torusMeasure m (U a) ≤ η a := by
    intro a; dsimp [η]; split
    · exact hhole a (by assumption)
    · exact prob_le_one
  have hL0 : 0 < Lstar := lt_of_lt_of_le zero_lt_one hLstar
  have hQ : (∑ q ∈ Finset.range (D+1),
      ((allPatterns alphabet labels q).card : ℝ≥0∞)) < ENNReal.ofReal Lstar := by
    rw [←Nat.cast_sum]
    exact ENNReal.natCast_lt_ofReal.mpr hcost
  obtain ⟨Z,hZ⟩ := source_simultaneous_shear (torusMeasure m)
    (latticeProjection L).toAddMonoidHom (latticeProjection_surjective L) U hU
    η hη0 hηt hUη
    (ENNReal.ofReal Lstar) (ENNReal.ofReal_pos.mpr hL0).ne' ENNReal.ofReal_ne_top D
    (allPatterns alphabet labels)
    (fun q _ s hs => ((mem_allPatterns alphabet labels q s).mp hs).2)
    (allPatterns_sliceClosed alphabet labels D) hQ
  refine ⟨Z,fun y s hs hraw hsection A hload => ?_⟩
  have hmain := hZ D le_rfl s hs
  simp only [restrictColumns_self] at hmain
  have hp : (∏ l ∈ s, η l.2) = ∏ l ∈ s, ENNReal.ofReal (Real.exp (-u l.2/2)) := by
    apply Finset.prod_congr rfl
    intro l hl
    have hm := ((mem_allPatterns alphabet labels D s).mp hs).1 hl
    have ha := ((mem_alphabetPoints alphabet labels D l).mp hm).2
    simp only [η,ite_eq_left ha]
  rw [hp] at hmain
  apply le_trans (measure_mono (horizontal_hole_subset L N M Z K J y s hraw hsection))
  apply hmain.trans
  exact exponential_pattern_bound s ((mem_allPatterns alphabet labels D s).mp hs).2
    u Lstar A hLstar hload


end SingleLatticeCovering.CoverGeometry

namespace SingleLatticeCovering.CoverGeometry
open MeasureTheory Completion LatticeGeometry
open scoped Pointwise ENNReal

lemma add_lattice_cover_iff {E : Type*} [AddCommGroup E] [Module ℤ E]
    (Γ : Submodule ℤ E) (K : Set E) (x z : E) (hz : z ∈ Γ) :
    x+z ∈ K+(Γ : Set E) ↔ x ∈ K+(Γ : Set E) := by
  constructor
  · rintro ⟨a,ha,b,hb,hab⟩
    change a+b = x+z at hab
    refine ⟨a,ha,b-z,Γ.sub_mem hb hz,?_⟩
    calc a+(b-z) = (a+b)-z := by abel
         _ = x := by rw [hab]; abel
  · rintro ⟨a,ha,b,hb,hab⟩
    refine ⟨a,ha,b+z,Γ.add_mem hb hz,?_⟩
    change a+b=x at hab
    change a+(b+z)=x+z
    rw [←add_assoc,hab]

lemma horizontalHole_reduce {m D : ℕ}
    (L : Submodule ℤ (Fin m → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (N : Submodule ℤ (Fin D → ℝ)) (M : (Fin D → ℝ) ≃ₗ[ℝ] (Fin D → ℝ))
    (Z : Fin D → (Fin m → ℝ)) (K : Set (Fin (m+D) → ℝ))
    (y₀ k : Fin D → ℝ) (hk : k ∈ N) :
    horizontalHole L K (joinedLattice L N M Z) (y₀+M k) ⊆
      Shear.translate (horizontalHole L K (joinedLattice L N M Z) y₀)
        (latticeProjection L (columnMap Z k)) := by
  rintro t ⟨x,hx,rfl⟩
  change latticeProjection L x-latticeProjection L (columnMap Z k) ∈
    horizontalHole L K (joinedLattice L N M Z) y₀
  rw [←map_sub]
  refine ⟨x-columnMap Z k,?_,rfl⟩
  intro hc
  have hg : Fin.append (columnMap Z k) (M k) ∈ joinedLattice L N M Z := by
    simpa only [zero_add] using joined_point_mem L N M Z L.zero_mem hk
  have h := (add_lattice_cover_iff (joinedLattice L N M Z) K
    (Fin.append (x-columnMap Z k) y₀) (Fin.append (columnMap Z k) (M k)) hg).mpr hc
  apply hx
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext i; refine Fin.addCases ?_ ?_ i <;> intro j <;>
    simp only [Pi.add_apply,Pi.sub_apply,Fin.append_left,Fin.append_right] ; abel



theorem all_height_hole_bound {m D : ℕ}
    (L : Submodule ℤ (Fin m → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (N : Submodule ℤ (Fin D → ℝ))
    (hints : ∀ k : Fin D → ℤ, (fun j => (k j : ℝ)) ∈ N)
    (M : (Fin D → ℝ) ≃ₗ[ℝ] (Fin D → ℝ)) (Z : Fin D → (Fin m → ℝ))
    (K : Set (Fin (m+D) → ℝ)) (ε : ℝ≥0∞)
    (hcell : ∀ z : Fin D → ℝ, (∀ j, 0 ≤ z j ∧ z j < 1) →
      torusMeasure m (horizontalHole L K (joinedLattice L N M Z) (M z)) ≤ ε) :
    ∀ y : Fin D → ℝ, torusMeasure m (horizontalHole L K (joinedLattice L N M Z) y) ≤ ε := by
  intro y
  let z := M.symm y
  let k : Fin D → ℝ := fun j => (⌊z j⌋ : ℤ)
  let z₀ : Fin D → ℝ := fun j => Int.fract (z j)
  have hk : k ∈ N := hints (fun j => ⌊z j⌋)
  have hy : y = M z₀+M k := by
    rw [←map_add]
    have hz : z₀+k = z := by
      ext j
      exact Int.fract_add_floor (z j)
    rw [hz]
    exact (M.apply_symm_apply y).symm
  rw [hy]
  apply le_trans (measure_mono (horizontalHole_reduce L N M Z K (M z₀) k hk))
  simp only [Shear.translate,sub_eq_add_neg,measure_preimage_add_right]
  exact hcell z₀ (fun j => ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩)


end SingleLatticeCovering.CoverGeometry

namespace SingleLatticeCovering.CoverGeometry
open MeasureTheory Completion LatticeGeometry
open scoped Pointwise ENNReal


lemma appendTorus_surjective (m D : ℕ) : Function.Surjective (appendTorus m D) :=
  (Fin.appendEquiv m D).surjective

lemma appendTorus_measurePreserving (m D : ℕ) :
    MeasurePreserving (appendTorus m D) ((torusMeasure m).prod (torusMeasure D))
      (torusMeasure (m+D)) :=
  by
    let : Measure.IsAddHaarMeasure ((torusMeasure m).prod (torusMeasure D)) :=
      Measure.prod.instIsAddHaarMeasure (torusMeasure m) (torusMeasure D)
    exact AddMonoidHom.measurePreserving (appendTorus m D).continuous (appendTorus_surjective m D)
      (by simp)


lemma productProjection_surjective {m D : ℕ}
    (L : Submodule ℤ (Fin m → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (N : Submodule ℤ (Fin D → ℝ)) [DiscreteTopology N] [IsZLattice ℝ N] :
    Function.Surjective (productProjection L N) := by
  intro t
  obtain ⟨x,hx⟩ := latticeProjection_surjective L (fun j => t (Fin.castAdd D j))
  obtain ⟨z,hz⟩ := latticeProjection_surjective N (fun j => t (Fin.natAdd m j))
  refine ⟨Fin.append x z,?_⟩
  rw [productProjection_append,hx,hz]
  exact (Fin.appendEquiv m D).apply_symm_apply t

lemma productProjection_eq_zero_iff {m D : ℕ}
    (L : Submodule ℤ (Fin m → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (N : Submodule ℤ (Fin D → ℝ)) [DiscreteTopology N] [IsZLattice ℝ N]
    (x : Fin (m+D) → ℝ) : productProjection L N x = 0 ↔ x ∈ finProduct L N := by
  rw [mem_finProduct,←latticeProjection_eq_zero_iff L,←latticeProjection_eq_zero_iff N]
  constructor
  · intro h
    constructor
    · ext j; simpa only [productProjection_apply,Fin.append_left,Pi.zero_apply] using congr_fun h (Fin.castAdd D j)
    · ext j; simpa only [productProjection_apply,Fin.append_right,Pi.zero_apply] using congr_fun h (Fin.natAdd m j)
  · rintro ⟨hL,hN⟩
    ext i; refine Fin.addCases ?_ ?_ i <;> intro k
    · simpa only [productProjection_apply,Pi.zero_apply,Fin.append_left] using congr_fun hL k
    · simpa only [productProjection_apply,Pi.zero_apply,Fin.append_right] using congr_fun hN k


lemma joinedProjection_surjective {m D : ℕ}
    (L : Submodule ℤ (Fin m → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (N : Submodule ℤ (Fin D → ℝ)) [DiscreteTopology N] [IsZLattice ℝ N]
    (M : (Fin D → ℝ) ≃ₗ[ℝ] (Fin D → ℝ)) (Z : Fin D → (Fin m → ℝ)) :
    Function.Surjective (joinedProjection L N M Z) :=
  (productProjection_surjective L N).comp (triangular (LinearEquiv.refl ℝ _) M (columnMap Z)).symm.surjective

lemma joinedProjection_eq_zero_iff {m D : ℕ}
    (L : Submodule ℤ (Fin m → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (N : Submodule ℤ (Fin D → ℝ)) [DiscreteTopology N] [IsZLattice ℝ N]
    (M : (Fin D → ℝ) ≃ₗ[ℝ] (Fin D → ℝ)) (Z : Fin D → (Fin m → ℝ))
    (x : Fin (m+D) → ℝ) : joinedProjection L N M Z x = 0 ↔ x ∈ joinedLattice L N M Z :=
  productProjection_eq_zero_iff L N _


end SingleLatticeCovering.CoverGeometry


end
end
end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_Covering
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section

namespace SingleLatticeCovering.CoverGeometry
open MeasureTheory Completion LatticeGeometry
open scoped Pointwise ENNReal




theorem quotient_hole_bound {m D : ℕ}
    (L : Submodule ℤ (Fin m → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (N : Submodule ℤ (Fin D → ℝ)) [DiscreteTopology N] [IsZLattice ℝ N]
    (M : (Fin D → ℝ) ≃ₗ[ℝ] (Fin D → ℝ)) (Z : Fin D → (Fin m → ℝ))
    (K : Set (Fin (m+D) → ℝ)) (hK : IsCompact K) (ε : ℝ≥0∞)
    (hhole : ∀ y, torusMeasure m (horizontalHole L K (joinedLattice L N M Z) y) ≤ ε) :
    torusMeasure (m+D) ((joinedProjection L N M Z '' K)ᶜ) ≤ ε := by
  let π := joinedProjection L N M Z
  have hC : MeasurableSet ((π '' K)ᶜ) := (hK.image π.continuous).measurableSet.compl
  rw [←(appendTorus_measurePreserving m D).measure_preimage hC.nullMeasurableSet]
  have hpre : MeasurableSet ((appendTorus m D) ⁻¹' (π '' K)ᶜ) :=
    (appendTorus m D).continuous.measurable hC
  rw [Measure.prod_apply_symm hpre]
  calc
    (∫⁻ v : Torus D, torusMeasure m ((fun t => (t,v)) ⁻¹'
        ((appendTorus m D) ⁻¹' (π '' K)ᶜ)) ∂(torusMeasure D)) ≤
        (∫⁻ _v : Torus D, ε ∂(torusMeasure D)) := by
      apply lintegral_mono
      intro v
      obtain ⟨z,hz⟩ := latticeProjection_surjective N v
      have hsub : (fun t => (t,v)) ⁻¹' ((appendTorus m D) ⁻¹' (π '' K)ᶜ) ⊆
          (fun t => t+latticeProjection L (columnMap Z z)) ⁻¹'
            horizontalHole L K (joinedLattice L N M Z) (M z) := by
        intro t ht
        obtain ⟨x,hx⟩ := latticeProjection_surjective L (t+latticeProjection L (columnMap Z z))
        have hπ : π (Fin.append x (M z)) = appendTorus m D (t,v) := by
          simp only [π,joinedProjection_append,map_sub,hx,hz,add_sub_cancel_right]
          rfl
        have hnot : Fin.append x (M z) ∉ K+(joinedLattice L N M Z : Set (Fin (m+D) → ℝ)) := by
          intro hc
          have hm := (projection_mem_image_iff (joinedLattice L N M Z) π.toAddMonoidHom
            (joinedProjection_eq_zero_iff L N M Z) K (Fin.append x (M z))).mpr hc
          change π (Fin.append x (M z)) ∈ π '' K at hm
          rw [hπ] at hm
          exact ht hm
        exact ⟨x,hnot,hx⟩
      apply le_trans (measure_mono hsub)
      rw [measure_preimage_add_right]
      exact hhole (M z)
    _ = ε := by simp

lemma quotient_real_hole_bound {m D : ℕ}
    (L : Submodule ℤ (Fin m → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (N : Submodule ℤ (Fin D → ℝ)) [DiscreteTopology N] [IsZLattice ℝ N]
    (M : (Fin D → ℝ) ≃ₗ[ℝ] (Fin D → ℝ)) (Z : Fin D → (Fin m → ℝ))
    (K : Set (Fin (m+D) → ℝ)) (hK : IsCompact K) (ε : ℝ) (hε : 0 ≤ ε)
    (hhole : ∀ y, torusMeasure m (horizontalHole L K (joinedLattice L N M Z) y) ≤ ENNReal.ofReal ε) :
    1-(torusMeasure (m+D)).real (joinedProjection L N M Z '' K) ≤ ε := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (quotient_hole_bound L N M Z K hK (ENNReal.ofReal ε) hhole)
  rw [ENNReal.toReal_ofReal hε] at h
  have he := measureReal_compl (μ := torusMeasure (m+D))
    (hK.image (joinedProjection L N M Z).continuous).measurableSet
  simpa using he.symm.trans_le h



theorem joined_holes_to_cover {m D : ℕ} (hn : 2 ≤ m+D)
    (L : Submodule ℤ (Fin m → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (N : Submodule ℤ (Fin D → ℝ)) [DiscreteTopology N] [IsZLattice ℝ N]
    (M : (Fin D → ℝ) ≃ₗ[ℝ] (Fin D → ℝ)) (Z : Fin D → (Fin m → ℝ))
    (K : Set (Fin (m+D) → ℝ)) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hhole : ∀ y, torusMeasure m (horizontalHole L K (joinedLattice L N M Z) y) ≤
      ENNReal.ofReal (1/((m+D : ℕ) : ℝ)^(2*(m+D)))) :
    ∃ (Λ : Submodule ℤ (Fin (m+D) → ℝ)) (_ : DiscreteTopology Λ),
      IsZLattice ℝ Λ ∧ K+(Λ : Set (Fin (m+D) → ℝ)) = Set.univ ∧
      (volume K).toReal / ZLattice.covolume Λ ≤
        Real.exp 1*((volume K).toReal /
          (ZLattice.covolume L*ZLattice.covolume (image N M))) := by
  have hh := quotient_real_hole_bound L N M Z K hK
    (1/((m+D : ℕ) : ℝ)^(2*(m+D))) (by positivity) hhole
  obtain ⟨Λ,hd,hfull,hcover,hdensity⟩ := complete_almost_cover_projection hn
    (joinedLattice L N M Z) (joinedProjection L N M Z)
    (joinedProjection_surjective L N M Z) (joinedProjection_eq_zero_iff L N M Z)
    K hK hconv hh
  exact ⟨Λ,hd,hfull,hcover,by simpa only [joined_covolume] using hdensity⟩



end SingleLatticeCovering.CoverGeometry

namespace SingleLatticeCovering.CoverGeometry
open MeasureTheory LatticeGeometry Completion Shear
open scoped BigOperators Pointwise ENNReal




theorem finite_patterns_to_cover {α : Type*} [Fintype α] {m D : ℕ} (hn : 2 ≤ m+D)
    (L : Submodule ℤ (Fin m → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (N : Submodule ℤ (Fin D → ℝ)) [DiscreteTopology N] [IsZLattice ℝ N]
    (hints : ∀ k : Fin D → ℤ, (fun j => (k j : ℝ)) ∈ N)
    (M : (Fin D → ℝ) ≃ₗ[ℝ] (Fin D → ℝ))
    (K : Set (Fin (m+D) → ℝ)) (hK : IsCompact K) (hconv : Convex ℝ K)
    (J : α → Set (Fin m → ℝ)) (hJ : ∀ a, IsCompact (J a))
    (u : α → ℝ) (labels : Finset α)
    (hhole : ∀ a ∈ labels, torusMeasure m ((latticeProjection L '' J a)ᶜ) ≤
      ENNReal.ofReal (Real.exp (-u a/2)))
    (alphabet : ℕ → Finset ℝ) (Lstar A : ℝ) (hLstar : 1 ≤ Lstar)
    (hcost : ((∑ q ∈ Finset.range (D+1),
      (allPatterns alphabet labels q).card : ℕ) : ℝ) < Lstar)
    (herror : Real.exp ((2^D : ℕ)*Real.log Lstar-A/2) ≤ 1/((m+D : ℕ) : ℝ)^(2*(m+D)))
    (hpatterns : ∀ z : Fin D → ℝ, (∀ j, 0 ≤ z j ∧ z j < 1) →
      ∃ s : Finset ((Fin D → ℝ) × α), s ∈ allPatterns alphabet labels D ∧
        (∀ l ∈ s, l.1 ∈ N) ∧
        (∀ l ∈ s, ∀ j ∈ J l.2, Fin.append j (M z-M l.1) ∈ K) ∧
        A ≤ ∑ l ∈ s, u l.2) :
    ∃ (Λ : Submodule ℤ (Fin (m+D) → ℝ)) (_ : DiscreteTopology Λ),
      IsZLattice ℝ Λ ∧ K+(Λ : Set (Fin (m+D) → ℝ)) = Set.univ ∧
      (volume K).toReal / ZLattice.covolume Λ ≤
        Real.exp 1*((volume K).toReal /
          (ZLattice.covolume L*ZLattice.covolume (image N M))) := by
  obtain ⟨Z,hZ⟩ := finite_family_lattice_shear L N M K J hJ u labels hhole alphabet Lstar hLstar hcost
  apply joined_holes_to_cover hn L N M Z K hK hconv
  apply all_height_hole_bound L N hints M Z K
  intro z hz
  obtain ⟨s,hs,hraw,hsection,hload⟩ := hpatterns z hz
  exact (hZ (M z) s hs hraw hsection A hload).trans (ENNReal.ofReal_le_ofReal herror)


end SingleLatticeCovering.CoverGeometry

namespace SingleLatticeCovering.Vertical
open ConstructionA LatticeGeometry

lemma Block.integer_mem (B : Block) (k : Fin B.b → ℤ) :
    (fun j => (k j : ℝ)) ∈ B.lattice := by
  change ∃ z : Fin B.b → ℤ, residue B.p z ∈ Submodule.span (ZMod B.p) {B.direction} ∧
    (fun j => (z j : ℝ)/(B.p : ℝ)) = (fun j => (k j : ℝ))
  refine ⟨fun j => B.p*k j,?_,?_⟩
  · convert (Submodule.span (ZMod B.p) {B.direction}).zero_mem using 1
    all_goals try with_reducible_and_instances rfl
    ext j
    simp [residue]
  · ext j
    push_cast
    field_simp [B.prime.ne_zero]

namespace Chain
variable {B : Block}
lemma raw_integer_mem (c : Chain B) (k : Fin c.dim → ℤ) :
    (fun j => (k j : ℝ)) ∈ c.rawLattice := by
  induction c with
  | base B => exact B.integer_mem k
  | append c B w ih =>
    exact ⟨ih (fun j => k (Fin.castAdd B.b j)),
      B.integer_mem (fun j => k (Fin.natAdd c.dim j))⟩

lemma full_raw_integer_mem (c : Chain B) (k : Fin c.fullDim → ℤ) :
    (fun j => (k j : ℝ)) ∈ c.fullRaw :=
  ⟨c.raw_integer_mem (fun j => k (Fin.castAdd B.terminalDim j)),
    integer_mem _ (fun j => k (Fin.natAdd c.dim j))⟩

end Chain
end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open MeasureTheory Folded LatticeGeometry Completion Shear CoverGeometry
open scoped BigOperators Pointwise ENNReal





theorem prepared_chain_to_cover {α : Type*} [Fintype α] {B : Block} (c : Chain B)
    {m : ℕ} (hn : 2 ≤ m+c.fullDim)
    (L : Submodule ℤ (Fin m → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (K : Set (Fin (m+c.fullDim) → ℝ)) (hK : IsCompact K) (hconv : Convex ℝ K)
    (J : α → Set (Fin m → ℝ)) (hJ : ∀ a, IsCompact (J a)) (u : α → ℝ)
    (κ ρ csec Csec ε τ A Lstar : ℝ)
    (hρ : 0 ≤ ρ) (hc : 0 ≤ csec) (hC : 0 ≤ Csec) (hτ : 0 ≤ τ) (hA : 0 < A)
    (hpat : ∀ y : c.FullVec, ∃ P : Finset c.FullVec,
      P.Nonempty ∧ SuffixBinary P ∧
      (∀ l ∈ P, l ∈ c.fullRaw ∧ c.FullResidual y l ∧
        c.det*gamma (y-c.fullLinear l) ≤ ε) ∧
      κ ≤ ∑ l ∈ P, c.det*gamma (y-c.fullLinear l))
    (hsection : ∀ v : c.FullVec, (∑ j, (v j)^2) ≤ c.radiusSq+(B.terminalDim : ℝ) →
      ∃ a : α, (∀ j ∈ J a, Fin.append j v ∈ K) ∧
        csec*ρ*(c.det*gamma v) ≤ u a ∧ u a ≤ Csec*ρ*(c.det*gamma v))
    (hhole : ∀ a, τ ≤ u a → u a ≤ Csec*ρ*ε →
      torusMeasure m ((latticeProjection L '' J a)ᶜ) ≤ ENNReal.ofReal (Real.exp (-u a/2)))
    (hload : A+(2^c.fullDim : ℕ)*τ ≤ csec*κ*ρ)
    (hLstar : 1 ≤ Lstar)
    (hcost : ((∑ q ∈ Finset.range (c.fullDim+1),
      (allPatterns c.alphabetSeq
        (Finset.univ.filter (fun a => τ ≤ u a ∧ u a ≤ Csec*ρ*ε)) q).card : ℕ) : ℝ) < Lstar)
    (herror : Real.exp ((2^c.fullDim : ℕ)*Real.log Lstar-A/2) ≤
      1/((m+c.fullDim : ℕ) : ℝ)^(2*(m+c.fullDim))) :
    ∃ (Λ : Submodule ℤ (Fin (m+c.fullDim) → ℝ)) (_ : DiscreteTopology Λ),
      IsZLattice ℝ Λ ∧ K+(Λ : Set (Fin (m+c.fullDim) → ℝ)) = Set.univ ∧
      (volume K).toReal / ZLattice.covolume Λ ≤
        Real.exp 1*((volume K).toReal /(ZLattice.covolume L*c.det)) := by
  classical
  let labels := Finset.univ.filter (fun a => τ ≤ u a ∧ u a ≤ Csec*ρ*ε)
  have hs : ∀ a ∈ labels, torusMeasure m ((latticeProjection L '' J a)ᶜ) ≤
      ENNReal.ofReal (Real.exp (-u a/2)) := by
    intro a ha
    exact hhole a (Finset.mem_filter.mp ha).2.1 (Finset.mem_filter.mp ha).2.2
  obtain ⟨Λ,hd,hfull,hcover,hdens⟩ := finite_patterns_to_cover hn L c.fullRaw
    c.full_raw_integer_mem c.fullLinear K hK hconv J hJ u labels hs
    c.alphabetSeq Lstar A hLstar hcost herror (by
      intro z hz
      obtain ⟨P,hPn,hPb,hPl,hPw⟩ := hpat (c.fullLinear z)
      exact section_labeled_retained P hPn hPb c.fullRaw (fun l hl => (hPl l hl).1)
        c.fullLinear (c.fullLinear z) K J u (fun l => c.det*gamma (c.fullLinear z-c.fullLinear l))
        κ ρ csec Csec ε τ A hρ hc hC hτ hA hPw (fun l hl => (hPl l hl).2.2)
        (fun l hl => hsection _ (c.full_residual_square _ _ (hPl l hl).2.1))
        hload c.alphabetSeq (by
          intro l hl j
          rw [Chain.alphabetSeq_fin]
          exact c.mem_alphabets z l hz (hPl l hl).2.1 (hPl l hl).1 j))
  refine ⟨Λ,hd,hfull,hcover,?_⟩
  change (volume K).toReal / ZLattice.covolume Λ ≤
    Real.exp 1*((volume K).toReal /(ZLattice.covolume L*ZLattice.covolume c.fullLattice)) at hdens
  simpa only [c.full_covolume] using hdens


end SingleLatticeCovering.Vertical

end
end

section

noncomputable section
namespace SingleLatticeCovering.Vertical
open MeasureTheory Folded LatticeGeometry Completion Shear CoverGeometry
open scoped BigOperators Pointwise ENNReal

lemma Chain.det_pos {B : Block} (c : Chain B) : 0 < c.det := by
  rw [←c.full_covolume]
  exact ZLattice.covolume_pos c.fullLattice




theorem labeled_chain_to_cover {α : Type*} [Fintype α] {B : Block} (c : Chain B)
    {m : ℕ} (hn : 2 ≤ m+c.fullDim)
    (L : Submodule ℤ (Fin m → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (K : Set (Fin (m+c.fullDim) → ℝ)) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hV : 0 < (volume K).toReal)
    (J : α → Set (Fin m → ℝ)) (hJ : ∀ a, IsCompact (J a))
    (κ ρ csec Csec ε τ A Lstar : ℝ)
    (hρ : 0 < ρ) (hc : 0 ≤ csec) (hC : 0 ≤ Csec) (hτ : 0 ≤ τ) (hA : 0 < A)
    (hcov : ZLattice.covolume L volume=(volume K).toReal/(ρ*c.det))
    (hpat : ∀ y : c.FullVec, ∃ P : Finset c.FullVec,
      P.Nonempty ∧ SuffixBinary P ∧
      (∀ l ∈ P, l ∈ c.fullRaw ∧ c.FullResidual y l ∧
        c.det*gamma (y-c.fullLinear l) ≤ ε) ∧
      κ ≤ ∑ l ∈ P, c.det*gamma (y-c.fullLinear l))
    (hsection : ∀ v : c.FullVec, (∑ j, (v j)^2) ≤ c.radiusSq+(B.terminalDim : ℝ) →
      ∃ a : α, (∀ j ∈ J a, Fin.append j v ∈ K) ∧
        csec*(volume K).toReal*gamma v ≤ (volume (J a)).toReal ∧
        (volume (J a)).toReal ≤ Csec*(volume K).toReal*gamma v)
    (hhole : ∀ a, τ ≤ (volume (J a)).toReal/ZLattice.covolume L volume →
      (volume (J a)).toReal/ZLattice.covolume L volume ≤ Csec*ρ*ε →
      torusMeasure m ((latticeProjection L '' J a)ᶜ) ≤
        ENNReal.ofReal (Real.exp (-((volume (J a)).toReal/ZLattice.covolume L volume)/2)))
    (hload : A+(2^c.fullDim : ℕ)*τ ≤ csec*κ*ρ)
    (hLstar : 1 ≤ Lstar)
    (hcost : ((∑ q ∈ Finset.range (c.fullDim+1),
      (allPatterns c.alphabetSeq
        (Finset.univ.filter (fun a => τ ≤ (volume (J a)).toReal/ZLattice.covolume L volume ∧
          (volume (J a)).toReal/ZLattice.covolume L volume ≤ Csec*ρ*ε)) q).card : ℕ) : ℝ) < Lstar)
    (herror : Real.exp ((2^c.fullDim : ℕ)*Real.log Lstar-A/2) ≤
      1/((m+c.fullDim : ℕ) : ℝ)^(2*(m+c.fullDim))) :
    ∃ (Λ : Submodule ℤ (Fin (m+c.fullDim) → ℝ)) (_ : DiscreteTopology Λ),
      IsZLattice ℝ Λ ∧ K+(Λ : Set (Fin (m+c.fullDim) → ℝ)) = Set.univ ∧
      (volume K).toReal / ZLattice.covolume Λ volume ≤ Real.exp 1*ρ := by
  have _ := hV
  have hL : 0 < ZLattice.covolume L volume := ZLattice.covolume_pos L
  have hVeq : (volume K).toReal=ZLattice.covolume L volume*(ρ*c.det) := by
    rw [hcov]; exact (div_mul_cancel₀ _ (mul_pos hρ c.det_pos).ne').symm
  have hratio (a g : ℝ) : (a*(volume K).toReal*g)/ZLattice.covolume L volume=a*ρ*(c.det*g) := by
    rw [hVeq]
    field_simp [hL.ne']
  obtain ⟨Λ,hd,hfull,hcover,hbound⟩ := prepared_chain_to_cover c hn L K hK hconv J hJ
    (fun a => (volume (J a)).toReal/ZLattice.covolume L volume) κ ρ csec Csec ε τ A Lstar
    hρ.le hc hC hτ hA hpat (by
      intro v hv
      obtain ⟨a,ha,hl,hu⟩ := hsection v hv
      refine ⟨a,ha,?_,?_⟩
      · rw [←hratio csec (gamma v)]
        exact div_le_div_of_nonneg_right hl hL.le
      · rw [←hratio Csec (gamma v)]
        exact div_le_div_of_nonneg_right hu hL.le) hhole hload hLstar hcost herror
  refine ⟨Λ,hd,hfull,hcover,?_⟩
  have heq : (volume K).toReal/(ZLattice.covolume L volume*c.det)=ρ := by
    rw [hVeq]
    field_simp [hL.ne',c.det_pos.ne']
  simpa only [heq] using hbound


end SingleLatticeCovering.Vertical

end
end

section

namespace SingleLatticeCovering.LatticeGeometry
open MeasureTheory
open scoped Pointwise

lemma affine_image_volume {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (t : Fin n → ℝ) (K : Set (Fin n → ℝ)) :
    volume ((fun x => e x+t) '' K) = ENNReal.ofReal |LinearMap.det e.toLinearMap| * volume K := by
  have hs : (fun x => e x+t) '' K = (fun x => x+t) '' (e '' K) := by
    rw [Set.image_image]
  rw [hs,Set.image_add_right,measure_preimage_add_right]
  exact volume.addHaar_image_linearMap e.toLinearMap K

lemma affine_image_cover {n : ℕ} (L : Submodule ℤ (Fin n → ℝ))
    (e : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) (t : Fin n → ℝ)
    (K : Set (Fin n → ℝ)) (hcover : K+(L : Set (Fin n → ℝ))=Set.univ) :
    (fun x => e x+t) '' K+(image L e : Set (Fin n → ℝ))=Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hx : e.symm (x-t) ∈ K+(L : Set (Fin n → ℝ)) := by rw [hcover]; trivial
  obtain ⟨k,hk,l,hl,hkl⟩ := hx
  refine ⟨e k+t,⟨k,hk,rfl⟩,e l,(mem_image L e (e l)).mpr ⟨l,hl,rfl⟩,?_⟩
  change e k+t+e l=x
  have he : e k+e l=x-t := by
    rw [←map_add]
    change k+l=e.symm (x-t) at hkl
    rw [hkl,e.apply_symm_apply]
  calc e k+t+e l = (e k+e l)+t := by abel
       _ = x := by rw [he]; abel

lemma affine_image_density {n : ℕ} (L : Submodule ℤ (Fin n → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L]
    (e : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) (t : Fin n → ℝ)
    (K : Set (Fin n → ℝ)) :
    (volume ((fun x => e x+t) '' K)).toReal / ZLattice.covolume (image L e) =
      (volume K).toReal / ZLattice.covolume L := by
  rw [affine_image_volume,ENNReal.toReal_mul,ENNReal.toReal_ofReal (abs_nonneg _),image_covolume]
  exact mul_div_mul_left _ _ (abs_ne_zero.mpr e.isUnit_det'.ne_zero)


end SingleLatticeCovering.LatticeGeometry

noncomputable section
namespace SingleLatticeCovering.LatticeGeometry
open MeasureTheory
open scoped Pointwise

lemma affineEquiv_eq_linear_add {n : ℕ}
    (e : (Fin n → ℝ) ≃ᵃ[ℝ] (Fin n → ℝ)) (x : Fin n → ℝ) : e x=e.linear x+e 0 := by
  have h := e.map_vadd (0 : Fin n → ℝ) x
  simpa using h



lemma pull_back_cover {n : ℕ} (e : (Fin n → ℝ) ≃ᵃ[ℝ] (Fin n → ℝ))
    (K : Set (Fin n → ℝ)) (L : Submodule ℤ (Fin n → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L]
    (hcover : e '' K+(L : Set (Fin n → ℝ))=Set.univ) {d : ℝ}
    (hd : (volume (e '' K)).toReal/ZLattice.covolume L ≤ d) :
    ∃ (Λ : Submodule ℤ (Fin n → ℝ)) (_ : DiscreteTopology Λ), IsZLattice ℝ Λ ∧
      K+(Λ : Set (Fin n → ℝ))=Set.univ ∧ (volume K).toReal/ZLattice.covolume Λ ≤ d := by
  let Λ := image L e.symm.linear
  have he : (fun x => e.symm.linear x+e.symm 0) '' (e '' K)=K := by
    simp_rw [←affineEquiv_eq_linear_add]
    exact e.symm_image_image K
  refine ⟨Λ,inferInstance,inferInstance,?_,?_⟩
  · have h := affine_image_cover L e.symm.linear (e.symm 0) (e '' K) hcover
    rwa [he] at h
  · have h := affine_image_density L e.symm.linear (e.symm 0) (e '' K)
    rw [he] at h
    exact h.trans_le hd


end SingleLatticeCovering.LatticeGeometry

end
end

section


noncomputable section
open Set Metric MeasureTheory MeasureTheory.Measure Module
open scoped ENNReal NNReal BigOperators
namespace SingleLatticeCovering.Sections

lemma compact_separated_cover {E : Type*} [PseudoMetricSpace E]
    (K : Set E) (hK : IsCompact K) {δ : ℝ≥0} (hδ : 0 < δ) :
    ∃ S : Finset E, (↑S : Set E) ⊆ K ∧
      Metric.IsSeparated δ (↑S : Set E) ∧ Metric.IsCover δ K (↑S : Set E) := by
  classical
  obtain ⟨U,hUK,hUf,hUC⟩ := Metric.exists_finite_isCover_of_isCompact
    (ε := δ/2) (by positivity) hK
  have hfin : Metric.packingNumber δ K ≠ ⊤ := by
    have hh := Metric.packingNumber_two_mul_le_externalCoveringNumber (δ/2) K
    rw [mul_div_cancel₀ _ (by norm_num : (2 : ℝ≥0) ≠ 0)] at hh
    exact ne_top_of_le_ne_top (Set.encard_ne_top_iff.mpr hUf) (hh.trans hUC.externalCoveringNumber_le_encard)
  have hSf' : (Metric.maximalSeparatedSet δ K).Finite :=
    Set.encard_ne_top_iff.mp (by rw [Metric.encard_maximalSeparatedSet hfin]; exact hfin)
  exact ⟨hSf'.toFinset,by simpa using (Metric.maximalSeparatedSet_subset (ε := δ) (A := K)),
    by simpa using (Metric.isSeparated_maximalSeparatedSet (ε := δ) (A := K)),
    by simpa using Metric.isCover_maximalSeparatedSet hfin⟩



lemma separated_card_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsAddHaarMeasure μ]
    (S : Finset E) {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ)
    (hS : ∀ x ∈ S, ‖x‖ ≤ R)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ < dist x y) :
    (S.card : ℝ) ≤ (1+2*R/δ)^(finrank ℝ E) := by
  classical
  have hd : 0 < δ/2 := half_pos hδ
  have hdis : (↑S : Set E).PairwiseDisjoint (fun x => Metric.ball x (δ/2)) := by
    intro x hx y hy hxy
    apply Set.disjoint_left.mpr
    intro z hzx hzy
    have hxz : dist x z < δ/2 := by simpa only [Metric.mem_ball,dist_comm] using hzx
    have hzy' : dist z y < δ/2 := hzy
    have hh := dist_triangle x z y
    have hxy' := hsep x hx y hy hxy
    linarith
  have hsub : (⋃ x ∈ (↑S : Set E), Metric.ball x (δ/2)) ⊆ Metric.ball (0 : E) (R+δ/2) := by
    intro z hz
    obtain ⟨x,hx,hzx⟩ := Set.mem_iUnion₂.mp hz
    rw [Metric.mem_ball,dist_zero_right]
    have hdist : dist z x < δ/2 := hzx
    have hh := norm_add_le (z-x) x
    rw [sub_add_cancel,←dist_eq_norm] at hh
    linarith [hS x hx]
  have hμ := measure_mono (μ := μ) hsub
  simp only [Finset.mem_coe] at hμ
  rw [measure_biUnion_finset hdis (fun x hx => Metric.isOpen_ball.measurableSet)] at hμ
  simp_rw [μ.addHaar_ball_of_pos _ hd] at hμ
  rw [Finset.sum_const, nsmul_eq_mul,
    μ.addHaar_ball_of_pos _ (by linarith : 0 < R+δ/2)] at hμ
  have hunit0 : μ (Metric.ball (0 : E) 1) ≠ 0 :=
    Metric.isOpen_ball.measure_ne_zero μ ⟨0, by simp⟩
  have hunitTop : μ (Metric.ball (0 : E) 1) ≠ ∞ :=
    measure_ball_ne_top
  have hreal : (S.card : ℝ)*(δ/2)^finrank ℝ E ≤ (R+δ/2)^finrank ℝ E := by
    have hh := (ENNReal.mul_le_mul_iff_left hunit0 hunitTop).mp (by simpa only [←mul_assoc] using hμ)
    have hs : (S.card : ℝ≥0∞)*ENNReal.ofReal ((δ/2)^finrank ℝ E) =
        ENNReal.ofReal ((S.card : ℝ)*(δ/2)^finrank ℝ E) := by rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]; simp
    rw [hs] at hh
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh
  have he : (1+2*R/δ)^finrank ℝ E = (R+δ/2)^finrank ℝ E/(δ/2)^finrank ℝ E := by
    rw [←div_pow]; congr 1; field_simp; ring
  rw [he]
  exact (le_div_iff₀ (pow_pos hd _)).mpr hreal


lemma ball_finite_net {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsAddHaarMeasure μ] {R : ℝ} (hR : 0 < R)
    {m : ℕ} (hm : 1 ≤ m) :
    ∃ S : Finset E, (S.card : ℝ) ≤ (3*(m : ℝ)^2)^(finrank ℝ E) ∧
      (∀ a ∈ S, ‖a‖ ≤ R) ∧
      ∀ y : E, ‖y‖ ≤ R → ∃ a ∈ S, dist y a ≤ R/(m : ℝ)^2 := by
  classical
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hd : 0 < R/(m : ℝ)^2 := div_pos hR (pow_pos hm0 2)
  let δ : ℝ≥0 := ⟨R/(m : ℝ)^2,hd.le⟩
  obtain ⟨S,hS,hsep,hcover⟩ := compact_separated_cover (Metric.closedBall (0 : E) R)
    (isCompact_closedBall _ _) (show 0 < δ from hd)
  have hSn : ∀ a ∈ S, ‖a‖ ≤ R := by
    intro a ha
    simpa only [Metric.mem_closedBall,dist_zero_right] using hS ha
  have hsep' : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → R/(m : ℝ)^2 < dist x y := by
    intro x hx y hy hxy
    have hh := ENNReal.toReal_strict_mono (edist_ne_top x y) (hsep hx hy hxy)
    rw [ENNReal.coe_toReal,edist_dist,ENNReal.toReal_ofReal dist_nonneg] at hh
    exact hh
  have hcard := separated_card_bound μ S hR.le hd hSn hsep'
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hratio : 1+2*R/(R/(m : ℝ)^2) ≤ 3*(m : ℝ)^2 := by
    have he : 2*R/(R/(m : ℝ)^2)=2*(m : ℝ)^2 := by field_simp
    rw [he]; nlinarith
  refine ⟨S,hcard.trans (pow_le_pow_left₀ (by positivity) hratio _),hSn,?_⟩
  intro y hy
  obtain ⟨a,ha,hya⟩ := hcover (show y ∈ Metric.closedBall (0 : E) R by simpa using hy)
  refine ⟨a,ha,?_⟩
  have hh := ENNReal.toReal_mono ENNReal.coe_ne_top hya
  rw [ENNReal.coe_toReal,edist_dist,ENNReal.toReal_ofReal dist_nonneg] at hh
  exact hh




end SingleLatticeCovering.Sections




noncomputable section
open Set Metric MeasureTheory MeasureTheory.Measure Module
open scoped Pointwise ENNReal NNReal BigOperators
namespace SingleLatticeCovering.Sections

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma fiber_compact {E : Type*} {F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {K : Set (E × F)} (hK : IsCompact K) (y : F) :
    IsCompact (fiber K y) := by
  have he : fiber K y = Prod.fst '' (K ∩ Prod.snd ⁻¹' {y}) := by
    ext x; constructor
    · intro hx; exact ⟨(x,y),⟨hx,by simp⟩,rfl⟩
    · rintro ⟨⟨x',y'⟩,⟨hxy,hy⟩,hx⟩
      have hy' : y'=y := hy
      change x'=x at hx
      subst x'; subst y'; exact hxy
  rw [he]
  exact (hK.inter_right (isClosed_singleton.preimage continuous_snd)).image continuous_fst

lemma fiber_convex {K : Set (E × F)} (hK : Convex ℝ K) (y : F) :
    Convex ℝ (fiber K y) := by
  intro x hx z hz a b ha hb hab
  have hh := hK hx hz ha hb hab
  simpa only [fiber, Set.mem_ofPred_eq, Prod.smul_mk, Prod.mk_add_mk,
    ←add_smul,hab,one_smul] using hh



lemma nearby_fiber_inclusion {K : Set (E × F)} (hK : Convex ℝ K)
    {R : ℝ} (hR : 0 ≤ R) {m : ℕ} (hm : 1 ≤ m)
    (hcenter : ∀ z : F, ‖z‖ ≤ 2*R → (0,z) ∈ K)
    {a y : F} (ha : ‖a‖ ≤ R) (hya : dist y a ≤ R/(m : ℝ)^2) :
    (1-(m : ℝ)^(-2 : ℤ)) • fiber K a ⊆ fiber K y := by
  have _ := hR
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le zero_lt_one hm1
  let z := a+(m : ℝ)^2 • (y-a)
  have hz : ‖z‖ ≤ 2*R := by
    calc
      _ ≤ ‖a‖+‖(m : ℝ)^2 • (y-a)‖ := norm_add_le _ _
      _ = ‖a‖+(m : ℝ)^2*dist y a := by rw [norm_smul, Real.norm_of_nonneg (sq_nonneg _),dist_eq_norm]
      _ ≤ R+(m : ℝ)^2*(R/(m : ℝ)^2) := add_le_add ha (mul_le_mul_of_nonneg_left hya (sq_nonneg _))
      _ = 2*R := by field_simp; ring
  have ht : 0 ≤ 1-(m : ℝ)^(-2 : ℤ) := by
    norm_num only [zpow_neg, zpow_ofNat]
    have hh : 1 ≤ (m : ℝ)^2 := one_le_pow₀ hm1
    exact sub_nonneg.mpr ((inv_le_one₀ (pow_pos hm0 _)).mpr hh)
  intro v hv
  obtain ⟨x,hx,rfl⟩ := hv
  have hh := hK hx (hcenter z hz) ht (by positivity : 0 ≤ (m : ℝ)^(-2 : ℤ)) (by ring)
  have he : (1-(m : ℝ)^(-2 : ℤ)) • a+(m : ℝ)^(-2 : ℤ) • z=y := by
    dsimp [z]; rw [smul_add,smul_smul]
    norm_num only [zpow_neg, zpow_ofNat]
    rw [inv_mul_cancel₀ (pow_ne_zero 2 hm0.ne'),one_smul]
    module
  simpa only [fiber,Set.mem_ofPred_eq,Prod.smul_mk,Prod.mk_add_mk,smul_zero,add_zero,he] using hh

lemma shrink_power_half {m : ℕ} (hm : 2 ≤ m) :
    (1-(m : ℝ)^(-2 : ℤ))^m ≥ (1/2 : ℝ) := by
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : 0 < (m : ℝ)^2 := by positivity
  have hinv : (m : ℝ)^(-2 : ℤ)=((m : ℝ)^2)⁻¹ := by norm_num [zpow_neg]
  rw [hinv]
  have hi : ((m : ℝ)^2)⁻¹ ≤ 1 := (inv_le_one₀ hp).mpr (by nlinarith)
  have hh := one_add_mul_le_pow (show -2 ≤ -((m : ℝ)^2)⁻¹ by linarith) m
  have he : (m : ℝ)*((m : ℝ)^2)⁻¹=(m : ℝ)⁻¹ := by field_simp
  have hi2 : (m : ℝ)⁻¹ ≤ 1/2 := by simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hm2
  simp only [mul_neg,he,←sub_eq_add_neg] at hh
  linarith



lemma prescribed_volume [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsAddHaarMeasure μ] (hn : 0 < finrank ℝ E)
    {A : Set E} (hA : IsCompact A) (hconv : Convex ℝ A) (hzero : (0 : E) ∈ A)
    {v : ℝ} (hv : 0 < v) (hvol : v ≤ (μ A).toReal) :
    ∃ J : Set E, IsCompact J ∧ Convex ℝ J ∧ (0 : E) ∈ J ∧ J ⊆ A ∧ (μ J).toReal=v := by
  have hμ : 0 < (μ A).toReal := hv.trans_le hvol
  let t : ℝ := (v/(μ A).toReal)^((finrank ℝ E : ℝ)⁻¹)
  have ht : 0 < t := Real.rpow_pos_of_pos (div_pos hv hμ) _
  have ht1 : t ≤ 1 := Real.rpow_le_one (by positivity) ((div_le_one hμ).mpr hvol) (by positivity)
  refine ⟨t • A, hA.smul t, hconv.smul t,?_,?_,?_⟩
  · exact ⟨0,hzero,smul_zero _⟩
  · rintro x ⟨a,ha,rfl⟩
    exact hconv.smul_mem_of_zero_mem hzero ha ⟨ht.le,ht1⟩
  · rw [μ.addHaar_smul_of_nonneg ht.le, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg ht.le _)]
    have he : t^finrank ℝ E=v/(μ A).toReal :=
      Real.rpow_inv_natCast_pow (div_pos hv hμ).le hn.ne'
    rw [he,div_mul_cancel₀ _ hμ.ne']




end SingleLatticeCovering.Sections





end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_Sections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Metric MeasureTheory MeasureTheory.Measure Module
open scoped ENNReal NNReal BigOperators
noncomputable section
open Set Metric MeasureTheory MeasureTheory.Measure Module
open scoped Pointwise ENNReal NNReal BigOperators
noncomputable section

namespace SingleLatticeCovering.Sections
open Set Module MeasureTheory
open scoped BigOperators Pointwise

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]



lemma affine_section_of_ball_projection {D : ℕ} (hD : 0 < D)
    (b : Basis (Fin D) ℝ F) (hunit : ∀ i, ‖b i‖ ≤ 1)
    (hcoord : ∀ y : F, ∀ i, |b.repr y i| ≤ ‖y‖)
    {K : Set (E × F)} (hconv : Convex ℝ K) {R : ℝ} (hR : 0 < R)
    (hproj : ∀ v : F, ‖v‖ ≤ 6*(D : ℝ)*R → ∃ x : E, (x,v) ∈ K) :
    ∃ T : F →ᵃ[ℝ] E, ∀ y : F, ‖y‖ ≤ 2*R → (T y,y) ∈ K := by
  classical
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  let c : ℝ := 4*R*D
  have hc : 0 < c := by dsimp [c]; positivity
  let v₀ : F := ∑ i : Fin D, (-2*R) • b i
  let v : Fin D → F := fun i => v₀+c • b i
  have hv₀ : ‖v₀‖ ≤ 2*R*D := by
    calc
      _ ≤ ∑ i : Fin D, ‖(-2*R) • b i‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin D, 2*R := by
        apply Finset.sum_le_sum; intro i hi
        rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg hR.le]
        norm_num
        nlinarith [hunit i]
      _ = _ := by simp; ring
  have hvi : ∀ i, ‖v i‖ ≤ 6*(D : ℝ)*R := by
    intro i
    calc
      _ ≤ ‖v₀‖+‖c • b i‖ := norm_add_le _ _
      _ ≤ 2*R*D+c := add_le_add hv₀ (by rw [norm_smul,Real.norm_of_nonneg hc.le]; nlinarith [hunit i])
      _ = _ := by dsimp [c]; ring
  obtain ⟨x₀,hx₀⟩ := hproj v₀ (by nlinarith)
  choose x hx using fun i => hproj (v i) (hvi i)
  let lam : F → Fin D → ℝ := fun y i => (b.repr y i+2*R)/c
  let L : F →ₗ[ℝ] E := ∑ i : Fin D, (b.coord i).smulRight (c⁻¹ • (x i-x₀))
  let t₀ : E := x₀+∑ i : Fin D, (2*R/c) • (x i-x₀)
  let T : F →ᵃ[ℝ] E := L.toAffineMap+AffineMap.const ℝ F t₀
  have hT : ∀ y, T y=x₀+∑ i : Fin D, lam y i • (x i-x₀) := by
    intro y
    dsimp [T,L,t₀,lam]
    simp only [      LinearMap.sum_apply,LinearMap.smulRight_apply,Basis.coord_apply,smul_smul]
    rw [add_comm _ (x₀+_),add_assoc]; congr 1
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i hi
    rw [←add_smul]
    congr 1; field_simp; ring
  refine ⟨T,fun y hy => ?_⟩
  have hlam0 : ∀ i, 0 ≤ lam y i := by
    intro i
    have hh := (abs_le.mp ((hcoord y i).trans hy)).1
    exact div_nonneg (by linarith) hc.le
  have hlamsum : ∑ i : Fin D, lam y i ≤ 1 := by
    calc
      _ ≤ ∑ i : Fin D, 4*R/c := by
        apply Finset.sum_le_sum; intro i hi
        apply div_le_div_of_nonneg_right _ hc.le
        have hh := (abs_le.mp ((hcoord y i).trans hy)).2
        linarith
      _ = 1 := by simp [c]; field_simp
  let w : Option (Fin D) → ℝ := fun o => o.elim (1-∑ i,lam y i) (lam y)
  let z : Option (Fin D) → E × F := fun o => o.elim (x₀,v₀) (fun i => (x i,v i))
  have hw0 : ∀ o ∈ (Finset.univ : Finset (Option (Fin D))), 0 ≤ w o := by
    intro o ho; cases o with
    | none => exact sub_nonneg.mpr hlamsum
    | some i => exact hlam0 i
  have hw1 : ∑ o : Option (Fin D), w o=1 := by simp [w,Fintype.sum_option]
  have hz : ∀ o ∈ (Finset.univ : Finset (Option (Fin D))), z o ∈ K := by
    intro o ho; cases o with
    | none => exact hx₀
    | some i => exact hx i
  have hmem := hconv.sum_mem hw0 hw1 hz
  have he : ∑ o : Option (Fin D), w o • z o=(T y,y) := by
    rw [Fintype.sum_option]
    dsimp only [w,z,Option.elim]
    apply Prod.ext
    · simp only [Prod.fst_add,Prod.fst_sum,Prod.smul_fst]
      change (1-∑ i,lam y i) • x₀+∑ i,lam y i • x i=T y
      rw [hT]
      simp only [smul_sub,Finset.sum_sub_distrib,←Finset.sum_smul]
      module
    · simp only [Prod.snd_add,Prod.snd_sum,Prod.smul_snd]
      change (1-∑ i,lam y i) • v₀+∑ i,lam y i • v i=y
      dsimp only [v]
      simp only [smul_add,smul_smul,Finset.sum_add_distrib,←Finset.sum_smul]
      have hh : ∀ i, lam y i*c=b.repr y i+2*R := by intro i; dsimp [lam]; field_simp
      simp_rw [hh,add_smul]
      rw [Finset.sum_add_distrib,b.sum_repr]
      have hsum : v₀+(∑ i : Fin D, (2*R) • b i)=0 := by
        dsimp only [v₀]
        rw [←Finset.sum_add_distrib]
        simp only [←add_smul,neg_mul,neg_add_cancel,zero_smul,Finset.sum_const_zero]
      calc
        _ = y+(v₀+∑ i : Fin D, (2*R) • b i) := by module
        _ = y := by rw [hsum,add_zero]
  rwa [he] at hmem


end SingleLatticeCovering.Sections

noncomputable section
namespace SingleLatticeCovering.Sections
open Set Metric MeasureTheory MeasureTheory.Measure Module
open scoped Pointwise ENNReal NNReal BigOperators

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]



lemma gaussian_pos {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] (y : F) : 0 < gaussian F y := by
  dsimp [gaussian]
  exact mul_pos (zpow_pos (Real.sqrt_pos.mpr (by positivity)) _) (Real.exp_pos _)



lemma gaussian_near {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] {R : ℝ} (hR : 0 ≤ R) {m : ℕ} (hm : 0 < m)
    {a y : F} (ha : ‖a‖ ≤ R) (hy : ‖y‖ ≤ R)
    (hya : dist y a ≤ R/(m : ℝ)^2) (hsmall : R^2/(m : ℝ)^2 ≤ 1) :
    Real.exp (-1)*gaussian F y ≤ gaussian F a ∧
      gaussian F a ≤ Real.exp 1*gaussian F y := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hdist : |‖a‖-‖y‖| ≤ R/(m : ℝ)^2 :=
    (abs_norm_sub_norm_le a y).trans (by simpa only [dist_comm,dist_eq_norm] using hya)
  have hsq : |‖a‖^2-‖y‖^2| ≤ 2 := by
    have he : ‖a‖^2-‖y‖^2=(‖a‖-‖y‖)*(‖a‖+‖y‖) := by ring
    rw [he,abs_mul,abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    calc
      _ ≤ (R/(m : ℝ)^2)*(2*R) := mul_le_mul hdist (by linarith) (by positivity) (by positivity)
      _ = 2*(R^2/(m : ℝ)^2) := by ring
      _ ≤ 2 := by linarith
  have hp := abs_le.mp hsq
  have hlow : -1+-‖y‖^2/2 ≤ -‖a‖^2/2 := by linarith
  have hupp : -‖a‖^2/2 ≤ 1+-‖y‖^2/2 := by linarith
  have hb : 0 ≤ (Real.sqrt (2*Real.pi))^(-(finrank ℝ F : ℤ)) := by positivity
  constructor
  · have hh := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hlow) hb
    simpa only [Real.exp_add,gaussian,mul_left_comm] using hh
  · have hh := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hupp) hb
    simpa only [Real.exp_add,gaussian,mul_left_comm] using hh




theorem finite_section_labels
    (μ : Measure E) [IsAddHaarMeasure μ] (ν : Measure F) [IsAddHaarMeasure ν]
    {K : Set (E × F)} (hK : IsCompact K) (hconv : Convex ℝ K)
    {R V : ℝ} (hR : 0 < R) (hV : 0 < V) (hm : 2 ≤ finrank ℝ E)
    (hcenter : ∀ z : F, ‖z‖ ≤ 2*R → (0,z) ∈ K)
    (hlower : ∀ y : F, ‖y‖ ≤ R → V*gaussian F y/2 ≤ (μ (fiber K y)).toReal)
    (hsmall : R^2/(finrank ℝ E : ℝ)^2 ≤ 1) :
    ∃ S : Finset F, (S.card : ℝ) ≤ (3*(finrank ℝ E : ℝ)^2)^(finrank ℝ F) ∧
      ∃ J : F → Set E, (∀ a ∈ S, IsCompact (J a) ∧ Convex ℝ (J a) ∧ (0 : E) ∈ J a ∧
        (μ (J a)).toReal=V*gaussian F a/8) ∧
      ∀ y : F, ‖y‖ ≤ R → ∃ a ∈ S, J a ⊆ fiber K y ∧
        (Real.exp (-1)/8)*V*gaussian F y ≤ (μ (J a)).toReal ∧
          (μ (J a)).toReal ≤ (Real.exp 1/8)*V*gaussian F y := by
  classical
  obtain ⟨S,hSc,hSn,hnet⟩ := ball_finite_net ν hR (show 1 ≤ finrank ℝ E by omega)
  let d : ℝ := 1-(finrank ℝ E : ℝ)^(-2 : ℤ)
  have hn2 : (2 : ℝ) ≤ finrank ℝ E := by exact_mod_cast hm
  have hd : 0 ≤ d := by
    dsimp [d]; norm_num only [zpow_neg, zpow_ofNat]
    have hh : 1 ≤ (finrank ℝ E : ℝ)^2 := by nlinarith
    exact sub_nonneg.mpr ((inv_le_one₀ (by positivity)).mpr hh)
  have hdata : ∀ a ∈ S, ∃ Ja : Set E, IsCompact Ja ∧ Convex ℝ Ja ∧ (0 : E) ∈ Ja ∧
      Ja ⊆ d • fiber K a ∧ (μ Ja).toReal=V*gaussian F a/8 := by
    intro a ha
    have haR := hSn a ha
    have hzero : (0 : E) ∈ fiber K a := hcenter a (by linarith)
    have hzero' : (0 : E) ∈ d • fiber K a := ⟨0,hzero,smul_zero _⟩
    apply prescribed_volume μ (by omega) ((fiber_compact hK a).smul d) ((fiber_convex hconv a).smul d) hzero'
      (by positivity [gaussian_pos a])
    rw [μ.addHaar_smul_of_nonneg hd,ENNReal.toReal_mul,ENNReal.toReal_ofReal (pow_nonneg hd _)]
    have hh := shrink_power_half hm
    have hv := hlower a haR
    have hgp := gaussian_pos a
    have hhalf : (1/2 : ℝ)*(V*gaussian F a/2) ≤ d^finrank ℝ E*(μ (fiber K a)).toReal :=
      mul_le_mul hh hv (by positivity) (pow_nonneg hd _)
    nlinarith
  have hex : ∀ a : F, ∃ Ja : Set E, a ∈ S → IsCompact Ja ∧ Convex ℝ Ja ∧ (0 : E) ∈ Ja ∧
      Ja ⊆ d • fiber K a ∧ (μ Ja).toReal=V*gaussian F a/8 := by
    intro a
    by_cases ha : a ∈ S
    · exact ⟨(hdata a ha).choose,fun _ => (hdata a ha).choose_spec⟩
    · exact ⟨∅,fun hh => (ha hh).elim⟩
  choose J hJ using hex
  refine ⟨S,hSc,J,?_,?_⟩
  · intro a ha; exact ⟨(hJ a ha).1,(hJ a ha).2.1,(hJ a ha).2.2.1,(hJ a ha).2.2.2.2⟩
  · intro y hy
    obtain ⟨a,ha,hya⟩ := hnet y hy
    have hsub := nearby_fiber_inclusion hconv hR.le (show 1 ≤ finrank ℝ E by omega) hcenter (hSn a ha) hya
    have hg := gaussian_near hR.le (show 0 < finrank ℝ E by omega) (hSn a ha) hy hya hsmall
    refine ⟨a,ha,(hJ a ha).2.2.2.1.trans hsub,?_,?_⟩ <;>
      rw [(hJ a ha).2.2.2.2]
    · nlinarith [mul_le_mul_of_nonneg_left hg.1 hV.le]
    · nlinarith [mul_le_mul_of_nonneg_left hg.2 hV.le]


end SingleLatticeCovering.Sections

noncomputable section
namespace SingleLatticeCovering.Sections
open Set MeasureTheory MeasureTheory.Measure Module
open scoped Pointwise ENNReal BigOperators

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]



lemma fiber_sectionShear (T : F →ᵃ[ℝ] E) (K : Set (E × F)) (y : F) :
    fiber (sectionShear T '' K) y=(fun x => x-T y) '' fiber K y := by
  ext x; constructor
  · rintro ⟨⟨u,v⟩,hK,he⟩
    have hv : v=y := congrArg Prod.snd he
    subst v
    exact ⟨u,hK,congrArg Prod.fst he⟩
  · rintro ⟨u,hu,rfl⟩
    exact ⟨(u,y),hu,rfl⟩

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

lemma fiber_sectionShear_measure {E : Type*} {F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] (μ : Measure E) [IsAddHaarMeasure μ]
    (T : F →ᵃ[ℝ] E) (K : Set (E × F)) (y : F) :
    μ (fiber (sectionShear T '' K) y)=μ (fiber K y) := by
  rw [fiber_sectionShear]
  simp only [sub_eq_add_neg,Set.image_add_right,measure_preimage_add_right]

lemma sectionShear_measure (μ : Measure E) [IsAddHaarMeasure μ]
    (ν : Measure F) [IsAddHaarMeasure ν]
    (T : F →ᵃ[ℝ] E) {K : Set (E × F)} (hK : IsCompact K) :
    (μ.prod ν) (sectionShear T '' K)=(μ.prod ν) K := by
  have hc := (sectionShear T).toAffineMap.continuous_of_finiteDimensional
  have hK' : IsCompact (sectionShear T '' K) := hK.image hc
  rw [Measure.prod_apply_symm hK'.measurableSet,Measure.prod_apply_symm hK.measurableSet]
  apply lintegral_congr
  intro y
  exact fiber_sectionShear_measure μ T K y



lemma convex_interior_of_measure_pos (μ : Measure E) [IsAddHaarMeasure μ]
    {J : Set E} (hconv : Convex ℝ J) (hpos : 0 < (μ J).toReal) :
    (interior J).Nonempty := by
  apply hconv.interior_nonempty_iff_affineSpan_eq_top.mpr
  by_contra h
  have hn : μ J=0 := measure_mono_null (subset_affineSpan ℝ J) (μ.addHaar_affineSubspace _ h)
  rw [hn,ENNReal.toReal_zero] at hpos
  exact (lt_irrefl 0) hpos



theorem centered_affine_image {D : ℕ} (hD : 0 < D)
    (b : Basis (Fin D) ℝ F) (hunit : ∀ i, ‖b i‖ ≤ 1)
    (hcoord : ∀ y : F, ∀ i, |b.repr y i| ≤ ‖y‖)
    (μ : Measure E) [IsAddHaarMeasure μ] (ν : Measure F) [IsAddHaarMeasure ν]
    {K : Set (E × F)} (hK : IsCompact K) (hconv : Convex ℝ K)
    {R : ℝ} (hR : 0 < R)
    (hproj : ∀ v : F, ‖v‖ ≤ 6*(D : ℝ)*R → ∃ x : E, (x,v) ∈ K) :
    ∃ e : (E × F) ≃ᵃ[ℝ] (E × F), IsCompact (e '' K) ∧ Convex ℝ (e '' K) ∧
      (μ.prod ν) (e '' K)=(μ.prod ν) K ∧
      (∀ y, μ (fiber (e '' K) y)=μ (fiber K y)) ∧
      (∀ y : F, ‖y‖ ≤ 2*R → (0,y) ∈ e '' K) := by
  obtain ⟨T,hT⟩ := affine_section_of_ball_projection hD b hunit hcoord hconv hR hproj
  refine ⟨sectionShear T,hK.image (sectionShear T).toAffineMap.continuous_of_finiteDimensional,
    hconv.affine_image (sectionShear T).toAffineMap,
    sectionShear_measure μ ν T hK,fun y => fiber_sectionShear_measure μ T K y,?_⟩
  intro y hy
  refine ⟨(T y,y),hT y hy,?_⟩
  simp


end SingleLatticeCovering.Sections

noncomputable section

noncomputable section
namespace SingleLatticeCovering.Sections
open Set Metric MeasureTheory MeasureTheory.Measure Module
open scoped Pointwise ENNReal BigOperators

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]





theorem gaussian_marginal_to_sections {D : ℕ} (hD : 0 < D)
    (b : Basis (Fin D) ℝ F) (hunit : ∀ i, ‖b i‖ ≤ 1)
    (hcoord : ∀ y : F, ∀ i, |b.repr y i| ≤ ‖y‖)
    (μ : Measure E) [IsAddHaarMeasure μ] (ν : Measure F) [IsAddHaarMeasure ν]
    {K : Set (E × F)} (hK : IsCompact K) (hconv : Convex ℝ K)
    {R : ℝ} (hR : 0 < R) (hV : 0 < ((μ.prod ν) K).toReal)
    (hm : 2 ≤ finrank ℝ E)
    (hlower : ∀ y : F, ‖y‖ ≤ 6*(D : ℝ)*R →
      ((μ.prod ν) K).toReal*gaussian F y/2 ≤ (μ (fiber K y)).toReal)
    (hsmall : R^2/(finrank ℝ E : ℝ)^2 ≤ 1) :
    ∃ e : (E × F) ≃ᵃ[ℝ] (E × F), IsCompact (e '' K) ∧ Convex ℝ (e '' K) ∧
      (μ.prod ν) (e '' K)=(μ.prod ν) K ∧
      ∃ S : Finset F, (S.card : ℝ) ≤ (3*(finrank ℝ E : ℝ)^2)^D ∧
        ∃ J : F → Set E,
          (∀ a ∈ S, IsCompact (J a) ∧ Convex ℝ (J a) ∧ (interior (J a)).Nonempty) ∧
          ∀ y : F, ‖y‖ ≤ R → ∃ a ∈ S, J a ⊆ fiber (e '' K) y ∧
            (Real.exp (-1)/8)*((μ.prod ν) (e '' K)).toReal*gaussian F y ≤ (μ (J a)).toReal ∧
            (μ (J a)).toReal ≤ (Real.exp 1/8)*((μ.prod ν) (e '' K)).toReal*gaussian F y := by
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
  obtain ⟨e,heK,heconv,heμ,hef,hezero⟩ := centered_affine_image hD b hunit hcoord μ ν hK hconv hR (by
    intro y hy
    have hp : 0 < (μ (fiber K y)).toReal := (by positivity [gaussian_pos y] :
      0 < ((μ.prod ν) K).toReal*gaussian F y/2).trans_le (hlower y hy)
    by_contra hn
    push Not at hn
    have hempty : fiber K y=∅ := Set.eq_empty_iff_forall_notMem.mpr hn
    rw [hempty,measure_empty,ENNReal.toReal_zero] at hp
    exact (lt_irrefl 0) hp)
  obtain ⟨S,hSc,J,hJ,hlabels⟩ := finite_section_labels μ ν heK heconv hR hV hm hezero (by
    intro y hy
    rw [hef]
    exact hlower y (hy.trans (by nlinarith))) hsmall
  have hdim : finrank ℝ F=D := by simpa using Module.finrank_eq_card_basis b
  refine ⟨e,heK,heconv,heμ,S,by simpa only [hdim] using hSc,J,?_,?_⟩
  · intro a ha
    refine ⟨(hJ a ha).1,(hJ a ha).2.1,convex_interior_of_measure_pos μ (hJ a ha).2.1 ?_⟩
    rw [(hJ a ha).2.2.2]
    positivity [gaussian_pos a]
  · intro y hy
    simpa only [heμ] using hlabels y hy


end SingleLatticeCovering.Sections

end
end
end
end
end
end
end
end

section

noncomputable section
namespace SingleLatticeCovering.Sections
open MeasureTheory
open scoped BigOperators

lemma gaussian_toLp {D : ℕ} (y : Fin D → ℝ) :
    gaussian (EuclideanSpace ℝ (Fin D)) (WithLp.toLp 2 y)=Folded.gamma y := by
  classical
  unfold gaussian Folded.gamma Folded.gamma1
  rw [finrank_euclideanSpace_fin,EuclideanSpace.real_norm_sq_eq]
  rw [Finset.prod_div_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [← Real.exp_sum,zpow_neg,zpow_natCast]
  rw [div_eq_mul_inv,mul_comm]
  congr 2
  simp only [div_eq_mul_inv,Finset.sum_mul,Finset.sum_neg_distrib,neg_mul]

end SingleLatticeCovering.Sections

end
end

section

noncomputable section
namespace SingleLatticeCovering.Sections
open MeasureTheory LatticeGeometry
open scoped BigOperators

lemma appendEquiv_measurePreserving (m D : ℕ) :
    MeasurePreserving (appendEquiv m D)
      ((volume : Measure (Fin m → ℝ)).prod (volume : Measure (Fin D → ℝ))) volume := by
  have h := (volume_preserving_arrowCongr' (finSumFinEquiv (m := m) (n := D))
    (MeasurableEquiv.refl ℝ) (MeasurePreserving.id volume)).comp
      (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin m ⊕ Fin D => ℝ))
  have he : (fun t : (Fin m → ℝ) × (Fin D → ℝ) =>
      (MeasurableEquiv.arrowCongr' finSumFinEquiv (MeasurableEquiv.refl ℝ))
        ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin D => ℝ)).symm t))=
      appendEquiv m D := by
    funext t i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp [MeasurableEquiv.arrowCongr',MeasurableEquiv.sumPiEquivProdPi,
        Equiv.arrowCongr',appendEquiv,Fin.appendEquiv]
  exact he ▸ h

lemma flatten_measurePreserving (m D : ℕ) :
    MeasurePreserving (flatten m D) volume volume :=
  (appendEquiv_measurePreserving m D).comp
    ((MeasurePreserving.id (volume : Measure (Fin m → ℝ))).prod
      (PiLp.volume_preserving_ofLp (Fin D)))

lemma flatten_volume (m D : ℕ) {K : Set ((Fin m → ℝ) × EuclideanSpace ℝ (Fin D))}
    (hK : IsCompact K) : volume (flatten m D '' K)=volume K := by
  have h := (flatten_measurePreserving m D).measure_preimage
    ((hK.image (flatten m D).toContinuousLinearEquiv.continuous).measurableSet.nullMeasurableSet)
  change volume ((flatten m D) ⁻¹' ((flatten m D) '' K))=volume ((flatten m D) '' K) at h
  rw [(flatten m D).injective.preimage_image] at h
  exact h.symm

end SingleLatticeCovering.Sections

end
end

section

noncomputable section
namespace SingleLatticeCovering.Sections
open MeasureTheory Set
open scoped BigOperators



lemma flatten_fiber {m D : ℕ} (K : Set (Fin (m+D) → ℝ)) (y : EuclideanSpace ℝ (Fin D)) :
    fiber ((flatten m D).symm '' K) y=coordinateFiber K (WithLp.ofLp y) := by
  ext x
  change (x,y) ∈ (flatten m D).symm '' K ↔ _
  constructor
  · rintro ⟨z,hz,hzxy⟩
    change flatten m D (x,y) ∈ K
    rw [←hzxy,(flatten m D).apply_symm_apply]
    exact hz
  · intro hx
    exact ⟨flatten m D (x,y),hx,(flatten m D).symm_apply_apply _⟩



theorem coordinate_marginal_to_labels {m D : ℕ} (hm : 2 ≤ m) (hD : 0 < D)
    {K : Set (Fin (m+D) → ℝ)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hV : 0 < (volume K).toReal) {R : ℝ} (hR : 0 < R)
    (hsmall : R^2/(m : ℝ)^2 ≤ 1)
    (hlower : ∀ y : Fin D → ℝ, ‖WithLp.toLp 2 y‖ ≤ 6*(D : ℝ)*R →
      (volume K).toReal*Folded.gamma y/2 ≤ (volume (coordinateFiber K y)).toReal) :
    ∃ e : (Fin (m+D) → ℝ) ≃ᵃ[ℝ] (Fin (m+D) → ℝ),
      IsCompact (e '' K) ∧ Convex ℝ (e '' K) ∧ volume (e '' K)=volume K ∧
      ∃ S : Finset (EuclideanSpace ℝ (Fin D)), (S.card : ℝ) ≤ (3*(m : ℝ)^2)^D ∧
        ∃ J : EuclideanSpace ℝ (Fin D) → Set (Fin m → ℝ),
          (∀ a ∈ S, IsCompact (J a) ∧ Convex ℝ (J a) ∧ (interior (J a)).Nonempty) ∧
          ∀ y : Fin D → ℝ, (∑ j, (y j)^2) ≤ R^2 → ∃ a ∈ S,
            (∀ x ∈ J a, Fin.append x y ∈ e '' K) ∧
            (Real.exp (-1)/8)*(volume (e '' K)).toReal*Folded.gamma y ≤ (volume (J a)).toReal ∧
            (volume (J a)).toReal ≤ (Real.exp 1/8)*(volume (e '' K)).toReal*Folded.gamma y := by
  let f := flatten m D
  let Kp : Set ((Fin m → ℝ) × EuclideanSpace ℝ (Fin D)) := f.symm '' K
  have hKp : IsCompact Kp := hK.image f.symm.toContinuousLinearEquiv.continuous
  have hconvp : Convex ℝ Kp := hconv.linear_image f.symm.toLinearMap
  have hflat : f '' Kp=K := by dsimp [Kp]; exact f.image_symm_image K
  have hvolp : volume Kp=volume K := by rw [←flatten_volume m D hKp]; exact congrArg volume hflat
  let b := EuclideanSpace.basisFun (Fin D) ℝ
  have hunit : ∀ i, ‖b.toBasis i‖ ≤ 1 := by intro i; exact (b.orthonormal.1 i).le
  have hcoord : ∀ y : EuclideanSpace ℝ (Fin D), ∀ i, |b.toBasis.repr y i| ≤ ‖y‖ := by
    intro y i
    rw [OrthonormalBasis.coe_toBasis_repr_apply]
    simpa only [Real.norm_eq_abs,b,EuclideanSpace.basisFun_repr] using PiLp.norm_apply_le y i
  obtain ⟨e,heK,heconv,hevol,S,hSc,J,hJ,hlabels⟩ := gaussian_marginal_to_sections hD b.toBasis hunit hcoord
    (volume : Measure (Fin m → ℝ)) (volume : Measure (EuclideanSpace ℝ (Fin D))) hKp hconvp hR
    (by simpa only [←Measure.volume_eq_prod,hvolp] using hV)
    (by simpa using hm) (by
      intro y hy
      have hh := hlower y.ofLp (by simpa using hy)
      simpa only [←Measure.volume_eq_prod,hvolp,Kp,f,flatten_fiber,←gaussian_toLp,WithLp.toLp_ofLp] using hh)
    (by simpa using hsmall)
  let e' : (Fin (m+D) → ℝ) ≃ᵃ[ℝ] (Fin (m+D) → ℝ) :=
    (f.symm.toAffineEquiv.trans e).trans f.toAffineEquiv
  have he'image : e' '' K=f '' (e '' Kp) := by
    change (fun x => f (e (f.symm x))) '' K = _
    simp only [Kp,Set.image_image]
  have hevol' : volume (e '' Kp)=volume Kp := by simpa only [←Measure.volume_eq_prod] using hevol
  have he'vol : volume (e' '' K)=volume K := by
    rw [he'image,flatten_volume m D heK]
    exact hevol'.trans hvolp
  refine ⟨e',?_,?_,he'vol,S,?_,J,hJ,?_⟩
  · rw [he'image]; exact heK.image f.toContinuousLinearEquiv.continuous
  · rw [he'image]; exact heconv.linear_image f.toLinearMap
  · simpa using hSc
  · intro y hy
    have hynorm : ‖WithLp.toLp 2 y‖ ≤ R := by
      apply (sq_le_sq₀ (norm_nonneg _) hR.le).mp
      simpa only [EuclideanSpace.real_norm_sq_eq] using hy
    obtain ⟨a,ha,hsub,hl,hu⟩ := hlabels (WithLp.toLp 2 y) hynorm
    refine ⟨a,ha,?_,?_,?_⟩
    · intro x hx
      rw [he'image]
      exact ⟨(x,WithLp.toLp 2 y),hsub hx,rfl⟩
    · rw [←gaussian_toLp,he'vol,←hvolp]
      simpa only [←Measure.volume_eq_prod,hevol'] using hl
    · rw [←gaussian_toLp,he'vol,←hvolp]
      simpa only [←Measure.volume_eq_prod,hevol'] using hu


end SingleLatticeCovering.Sections

end
end

end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_Rates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Real Filter Topology Asymptotics

namespace SingleLatticeCovering.FinalRates

lemma loglog_nat_atTop : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
  Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

lemma log_nat_atTop : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

lemma loglog_sq_littleO :
    (fun n : ℕ => (Real.log (Real.log (n : ℝ)))^2) =o[atTop]
      (fun n : ℕ => Real.log (n : ℝ)) := by
  simpa only [Function.comp_def,Real.rpow_two,Real.rpow_one] using
    (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1)).comp_tendsto log_nat_atTop

lemma firstSize_tendsto : Tendsto firstSize atTop atTop := by
  apply tendsto_nat_ceil_atTop.comp
  simpa only [Function.comp_def,Real.rpow_two] using (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2)).comp loglog_nat_atTop

lemma eventually_firstSize_le_log {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, (firstSize n : ℝ)+1 ≤ c*Real.log (n : ℝ) := by
  filter_upwards [loglog_sq_littleO.bound (half_pos hc),
    log_nat_atTop.eventually (eventually_ge_atTop (4/c))] with n hs hl
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),
    abs_of_nonneg (Real.log_natCast_nonneg n)] at hs
  have hceil := Nat.ceil_lt_add_one (sq_nonneg (Real.log (Real.log (n : ℝ))))
  have he : 4 ≤ c*Real.log (n : ℝ) := by simpa only [mul_comm] using (div_le_iff₀ hc).mp hl
  change (firstSize n : ℝ) < (Real.log (Real.log (n : ℝ)))^2+1 at hceil
  linarith



lemma eventually_dimension_power {C a r : ℝ} (hC : 0 < C) (ha : 1 < a) (hr : 0 < r) :
    ∀ᶠ n : ℕ in atTop, ∀ D : ℕ, (D : ℝ) ≤ C*((firstSize n : ℝ)+1) →
      a^D ≤ (n : ℝ)^r := by
  have hal : 0 < Real.log a := Real.log_pos ha
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  filter_upwards [eventually_firstSize_le_log (div_pos hr (mul_pos hC hal)),
    eventually_ge_atTop (1 : ℕ)] with n hn hn1 D hD
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  apply (Real.log_le_log_iff (pow_pos ha0 _) (Real.rpow_pos_of_pos hn0 r)).mp
  rw [Real.log_pow,Real.log_rpow hn0]
  calc
    (D : ℝ)*Real.log a ≤ C*((firstSize n : ℝ)+1)*Real.log a :=
      mul_le_mul_of_nonneg_right hD hal.le
    _ = (C*Real.log a)*((firstSize n : ℝ)+1) := by ring
    _ ≤ (C*Real.log a)*(r/(C*Real.log a)*Real.log (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hn (mul_pos hC hal).le
    _ = r*Real.log (n : ℝ) := by field_simp

lemma eventually_superlinear_power {k : ℝ} (hk : 0 < k) :
    ∀ᶠ s : ℝ in atTop, 2*s ≤ k*s^(7/5 : ℝ) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2/5)).eventually
      (eventually_ge_atTop (2/k))] with s hs hpow
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hmul : 2 ≤ k*s^(2/5 : ℝ) := by simpa only [mul_comm] using (div_le_iff₀ hk).mp hpow
  have he : s^(7/5 : ℝ)=s*s^(2/5 : ℝ) := by
    rw [show (7/5 : ℝ)=1+2/5 by norm_num,Real.rpow_add hs0,Real.rpow_one]
  rw [he]
  nlinarith [mul_nonneg hs0.le (sub_nonneg.mpr hmul)]



lemma cap_log_tendsto {k : ℝ} (hk : 0 < k) :
    Tendsto (fun n : ℕ => Real.log (n : ℝ)*
      Real.exp (-k*(firstSize n : ℝ)^(70/100 : ℝ))) atTop (𝓝 0) := by
  have hexp : Tendsto (fun n : ℕ => Real.exp (-Real.log (Real.log (n : ℝ)))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp loglog_nat_atTop)
  apply squeeze_zero' (Eventually.of_forall (fun n =>
    mul_nonneg (Real.log_natCast_nonneg n) (Real.exp_pos _).le)) ?_ hexp
  filter_upwards [loglog_nat_atTop.eventually (eventually_superlinear_power hk),
    loglog_nat_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_ge_atTop (2 : ℕ)] with n hpow hs hn
  have hnlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hs0 : 0 ≤ Real.log (Real.log (n : ℝ)) := le_trans zero_le_one hs
  have hceil := Nat.le_ceil ((Real.log (Real.log (n : ℝ)))^2)
  have hcappow : (Real.log (Real.log (n : ℝ)))^(7/5 : ℝ) ≤
      (firstSize n : ℝ)^(70/100 : ℝ) := by
    have hh := Real.rpow_le_rpow (sq_nonneg (Real.log (Real.log (n : ℝ)))) hceil
      (by norm_num : (0 : ℝ) ≤ 70/100)
    rw [←Real.rpow_natCast _ 2,←Real.rpow_mul hs0] at hh
    norm_num at hh
    simpa only [firstSize,show (70/100 : ℝ)=(7/10 : ℝ) by norm_num] using hh
  conv_lhs => rw [←Real.exp_log hnlog,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hcappow hk.le]



end SingleLatticeCovering.FinalRates
noncomputable section

namespace SingleLatticeCovering.FinalRates
open Real Filter Topology Asymptotics

lemma eventually_log_power_bound (k : ℕ) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (Real.log (n : ℝ))^k ≤ ε*(n : ℝ)^r := by
  have h : (fun n : ℕ => (Real.log (n : ℝ))^k) =o[atTop]
      (fun n : ℕ => (n : ℝ)^r) := by
    simpa only [Function.comp_def,Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (k : ℝ) hr).comp_tendsto tendsto_natCast_atTop_atTop
  filter_upwards [h.bound hε] with n hn
  simpa only [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (Real.log_natCast_nonneg n) _),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)] using hn

lemma eventually_dimension_small {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, ∀ D : ℕ, (D : ℝ) ≤ C*((firstSize n : ℝ)+1) →
      (D : ℝ) ≤ Real.log (n : ℝ) ∧ (D : ℝ) ≤ (n : ℝ)/2 := by
  filter_upwards [eventually_firstSize_le_log (inv_pos.mpr hC),
    eventually_log_power_bound 1 (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 1/2)] with n hn hlog D hD
  have hDl : (D : ℝ) ≤ Real.log (n : ℝ) := by
    calc
      _ ≤ C*((firstSize n : ℝ)+1) := hD
      _ ≤ C*(C⁻¹*Real.log (n : ℝ)) := mul_le_mul_of_nonneg_left hn hC.le
      _ = Real.log (n : ℝ) := by field_simp
  refine ⟨hDl,hDl.trans ?_⟩
  simpa only [pow_one,Real.rpow_one,one_div,mul_comm,div_eq_mul_inv,one_mul] using hlog

lemma eta_linear_lower :
    ∀ᶠ m : ℕ in atTop, (Real.log (27/16 : ℝ)/8)*(m : ℝ) ≤ eta m := by
  have hlog : 0 < Real.log (27/16 : ℝ) := Real.log_pos (by norm_num)
  filter_upwards [eventually_log_power_bound 1 (by norm_num : (0 : ℝ) < 1)
    (div_pos hlog (by norm_num : (0 : ℝ) < 24))] with m hm
  simp only [pow_one,Real.rpow_one] at hm
  dsimp [eta]
  linarith

lemma eventually_cap_linear {k H ε : ℝ} (hk : 0 < k) (hH : 0 ≤ H) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, (n : ℝ)/2 ≤ m →
      H*(n : ℝ)*Real.log (n : ℝ)*Real.exp (-k*(firstSize n : ℝ)^(70/100 : ℝ)) ≤ ε*m := by
  have _ := hH
  have ht : Tendsto (fun n : ℕ => H*(Real.log (n : ℝ)*
      Real.exp (-k*(firstSize n : ℝ)^(70/100 : ℝ)))) atTop (𝓝 0) :=
    by simpa only [mul_zero] using (cap_log_tendsto hk).const_mul H
  filter_upwards [ht.eventually (gt_mem_nhds (half_pos hε))] with n hn m hm
  calc
    _ = (n : ℝ)*(H*(Real.log (n : ℝ)*Real.exp (-k*(firstSize n : ℝ)^(70/100 : ℝ)))) := by ring
    _ ≤ (n : ℝ)*(ε/2) := mul_le_mul_of_nonneg_left hn.le (Nat.cast_nonneg n)
    _ ≤ ε*m := by nlinarith



lemma eventually_cap_eta {C k H : ℝ} (hC : 0 < C) (hk : 0 < k) (hH : 0 ≤ H) :
    ∀ᶠ n : ℕ in atTop, ∀ D : ℕ, (D : ℝ) ≤ C*((firstSize n : ℝ)+1) →
      D ≤ n ∧ H*(n : ℝ)*Real.log (n : ℝ)*
        Real.exp (-k*(firstSize n : ℝ)^(70/100 : ℝ)) ≤ eta (n-D) := by
  obtain ⟨M,hM⟩ := eventually_atTop.mp eta_linear_lower
  have hlog : 0 < Real.log (27/16 : ℝ) := Real.log_pos (by norm_num)
  filter_upwards [eventually_dimension_small hC,
    eventually_cap_linear hk hH (div_pos hlog (by norm_num : (0 : ℝ) < 8)),
    eventually_ge_atTop (2*M)] with n hD hn hnM D hdim
  have hhalf := (hD D hdim).2
  have hDn : D ≤ n := by exact_mod_cast (show (D : ℝ) ≤ n by linarith)
  have hm : (n : ℝ)/2 ≤ (n-D : ℕ) := by rw [Nat.cast_sub hDn]; linarith
  have hMm : M ≤ n-D := by
    have hnMr : (2 : ℝ)*M ≤ n := by exact_mod_cast hnM
    exact_mod_cast (show (M : ℝ) ≤ (n-D : ℕ) from by linarith)
  exact ⟨hDn,(hn (n-D) hm).trans (hM _ hMm)⟩

lemma eventually_rpow_bound {a b ε : ℝ} (hab : a < b) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ)^a ≤ ε*(n : ℝ)^b := by
  filter_upwards [((tendsto_rpow_atTop (sub_pos.mpr hab)).comp
    tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (1/ε)),
    eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hm : 1 ≤ ε*(n : ℝ)^(b-a) := by
    simpa only [Function.comp_def,mul_comm] using (div_le_iff₀ hε).mp hn
  have he : (n : ℝ)^b=(n : ℝ)^a*(n : ℝ)^(b-a) := by
    rw [←Real.rpow_add hn0]; congr 1; ring
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_left hm (Real.rpow_pos_of_pos hn0 a).le]

lemma sqrt_nat_atTop : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop := by
  simpa only [Function.comp_def,Real.sqrt_eq_rpow] using
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)).comp tendsto_natCast_atTop_atTop

lemma sqrt_half_bound {n m : ℕ} (hm : (n : ℝ)/2 ≤ m) :
    Real.sqrt (n : ℝ) ≤ 2*Real.sqrt (m : ℝ) := by
  have hn0 := Real.sqrt_nonneg (n : ℝ)
  have hm0 := Real.sqrt_nonneg (m : ℝ)
  have hn2 := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hm2 := Real.sq_sqrt (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  nlinarith


lemma eventually_discard_bound {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ D m : ℕ, (D : ℝ) ≤ C*((firstSize n : ℝ)+1) → m ≤ n →
      (2 : ℝ)^D*Real.sqrt (m : ℝ) ≤ ε*(n : ℝ)*Real.log (n : ℝ) := by
  filter_upwards [eventually_dimension_power hC (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 1/4),
    eventually_rpow_bound (by norm_num : (3/4 : ℝ) < 1) hε,
    log_nat_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_ge_atTop (1 : ℕ)] with n hp hr hlog hn1 D m hD hmn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  calc
    _ ≤ (n : ℝ)^(1/4 : ℝ)*Real.sqrt (n : ℝ) :=
      mul_le_mul (hp D hD) (Real.sqrt_le_sqrt (by exact_mod_cast hmn))
        (Real.sqrt_nonneg _) (Real.rpow_pos_of_pos hn0 _).le
    _ = (n : ℝ)^(3/4 : ℝ) := by
      rw [Real.sqrt_eq_rpow,←Real.rpow_add hn0]; norm_num
    _ ≤ ε*(n : ℝ) := by simpa only [Real.rpow_one] using hr
    _ ≤ ε*(n : ℝ)*Real.log (n : ℝ) := le_mul_of_one_le_right (by positivity) hlog



lemma eventually_label_criterion {C Cs CR : ℝ} (hC : 0 < C) (hCs : 1 ≤ Cs) (hCR : 0 ≤ CR) :
    ∀ᶠ n : ℕ in atTop, ∀ D m : ℕ, (D : ℝ) ≤ C*((firstSize n : ℝ)+1) →
      (n : ℝ)/2 ≤ m → m ≤ n →
      (1+CR)*(Cs*(m : ℝ)^2)^D*Real.exp (-Real.sqrt (m : ℝ)/2) < 1 := by
  have hCR1 : 0 < 1+CR := by linarith
  have hCs0 : 0 < Cs := lt_of_lt_of_le zero_lt_one hCs
  filter_upwards [eventually_dimension_small hC,
    eventually_log_power_bound 2 (by norm_num : (0 : ℝ) < 1/2)
      (by norm_num : (0 : ℝ) < 1/48),
    sqrt_nat_atTop.eventually (eventually_ge_atTop (16*(Real.log (1+CR)+1))),
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop Cs),
    eventually_ge_atTop (2 : ℕ)] with n hdim hpoly hsqrt hCsn hn2 D m hD hm hmn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hm1 : (1 : ℝ) ≤ m := by
    have hn2r : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    linarith
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le zero_lt_one hm1
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hDl := (hdim D hD).1
  have hlogm : Real.log (m : ℝ) ≤ Real.log (n : ℝ) := Real.log_le_log hm0 (by exact_mod_cast hmn)
  have hlogC : Real.log Cs ≤ Real.log (n : ℝ) := Real.log_le_log hCs0 hCsn
  have hlogm0 : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hm1
  have hlogC0 : 0 ≤ Real.log Cs := Real.log_nonneg hCs
  have hlogs : (D : ℝ)*(Real.log Cs+2*Real.log (m : ℝ)) ≤ 3*(Real.log (n : ℝ))^2 := by
    calc
      _ ≤ Real.log (n : ℝ)*(Real.log Cs+2*Real.log (m : ℝ)) :=
        mul_le_mul_of_nonneg_right hDl (by linarith)
      _ ≤ Real.log (n : ℝ)*(3*Real.log (n : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.log_natCast_nonneg n)
      _ = _ := by ring
  rw [←Real.sqrt_eq_rpow] at hpoly
  have hs := sqrt_half_bound hm
  have hneg : Real.log (1+CR)+(D : ℝ)*(Real.log Cs+2*Real.log (m : ℝ))-
      Real.sqrt (m : ℝ)/2 < 0 := by linarith [Real.sqrt_nonneg (m : ℝ)]
  have he : (1+CR)*(Cs*(m : ℝ)^2)^D*Real.exp (-Real.sqrt (m : ℝ)/2) =
      Real.exp (Real.log (1+CR)+(D : ℝ)*(Real.log Cs+2*Real.log (m : ℝ))-
      Real.sqrt (m : ℝ)/2) := by
    have hp : (Cs*(m : ℝ)^2)^D =
        Real.exp ((D : ℝ)*(Real.log Cs+2*Real.log (m : ℝ))) := by
      rw [Real.exp_nat_mul,Real.exp_add,Real.exp_log hCs0]
      rw [show (2 : ℝ)*Real.log (m : ℝ)=Real.log ((m : ℝ)^2) by rw [Real.log_pow]; norm_num,
        Real.exp_log (pow_pos hm0 2)]
    calc
      _ = Real.exp (Real.log (1+CR))*
          Real.exp ((D : ℝ)*(Real.log Cs+2*Real.log (m : ℝ)))*
          Real.exp (-Real.sqrt (m : ℝ)/2) := by rw [Real.exp_log hCR1,hp]
      _ = _ := by rw [←Real.exp_add,←Real.exp_add]; congr 1; ring
  rw [he]
  exact Real.exp_lt_one_iff.mpr hneg




end SingleLatticeCovering.FinalRates

end
end
end

section

noncomputable section
namespace SingleLatticeCovering.Shear
open Real Filter Topology
open scoped BigOperators



lemma pointBudget_pos {α : Type*} (A : ℕ → Finset ℝ) (s : Finset α) (D : ℕ) :
    0 < pointBudget A s D := by
  dsimp [pointBudget]
  exact Nat.mul_pos (by omega) (Finset.prod_pos (fun j hj => by omega))

lemma alphabetPoints_card_le_budget {α : Type*} (A : ℕ → Finset ℝ) (s : Finset α)
    {q D : ℕ} (hq : q ≤ D) : (alphabetPoints A s q).card ≤ pointBudget A s D := by
  classical
  have hp : ∏ j ∈ Finset.range q, (A j).card ≤
      ∏ j ∈ Finset.range D, ((A j).card+1) := by
    calc
      _ ≤ ∏ j ∈ Finset.range q, ((A j).card+1) := Finset.prod_le_prod (fun j hj => Nat.zero_le _) (fun j hj => Nat.le_succ _)
      _ ≤ _ := Finset.prod_le_prod_of_subset_of_one_le (Finset.range_mono hq) (fun j hj => Nat.zero_le _) (fun j hj _ => Nat.succ_pos _)
  dsimp [alphabetPoints,pointBudget]
  rw [Finset.card_product,Fintype.card_piFinset]
  have he : (∏ i : Fin q, (A i.val).card) = ∏ j ∈ Finset.range q, (A j).card :=
    Fin.prod_univ_eq_prod_range (fun j => (A j).card) q
  rw [he]
  exact le_trans (Nat.mul_le_mul_right s.card hp) (by simp [mul_comm])

lemma patternTotal_bound {α : Type*} (A : ℕ → Finset ℝ) (s : Finset α) (D : ℕ) :
    patternTotal A s D ≤ (D+1)*(pointBudget A s D+1)^(2^D) :=
  allPatterns_total_bound A s D (pointBudget A s D) (fun _ hq => alphabetPoints_card_le_budget A s hq)

lemma log_pointBudget {α : Type*} (A : ℕ → Finset ℝ) (s : Finset α) (D : ℕ) :
    Real.log (pointBudget A s D : ℝ) = Real.log (s.card+1 : ℝ)+
      ∑ j ∈ Finset.range D, Real.log ((A j).card+1 : ℝ) := by
  simp only [pointBudget,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_prod]
  rw [Real.log_mul (by positivity) (by positivity),Real.log_prod]
  intro j hj; positivity

lemma scalar_pattern_cost (D N Q : ℕ) (hN : 0 < N)
    (hQ : Q ≤ (D+1)*(N+1)^(2^D)) :
    (2 : ℝ)^D*Real.log (2*((Q : ℝ)+1)) ≤
      (4 : ℝ)^D*(Real.log 8+Real.log ((D : ℝ)+1)+Real.log (N : ℝ)) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hNr
  have hD : (0 : ℝ) < (D : ℝ)+1 := by positivity
  have hbase : (1 : ℝ) ≤ ((D : ℝ)+1)*((N : ℝ)+1)^(2^D) :=
    one_le_mul_of_one_le_of_one_le (by linarith [(Nat.cast_nonneg D : (0 : ℝ) ≤ D)]) (one_le_pow₀ (by linarith))
  have hQr : (Q : ℝ) ≤ ((D : ℝ)+1)*((N : ℝ)+1)^(2^D) := by exact_mod_cast hQ
  have hl : Real.log (2*((Q : ℝ)+1)) ≤ Real.log 4+Real.log ((D : ℝ)+1)+
      (2^D : ℕ)*Real.log ((N : ℝ)+1) := by
    calc
      _ ≤ Real.log (4*(((D : ℝ)+1)*((N : ℝ)+1)^(2^D))) :=
        Real.log_le_log (by positivity) (by linarith)
      _ = _ := by rw [Real.log_mul (by norm_num) (by positivity),
        Real.log_mul hD.ne' (by positivity),Real.log_pow]; ring
  have hNl : Real.log ((N : ℝ)+1) ≤ Real.log 2+Real.log (N : ℝ) := by
    rw [←Real.log_mul (by norm_num) hNp.ne']
    exact Real.log_le_log (by positivity) (by linarith)
  have h2 : (1 : ℝ) ≤ (2 : ℝ)^D := one_le_pow₀ (by norm_num)
  have hDl : 0 ≤ Real.log ((D : ℝ)+1) := Real.log_nonneg (by linarith [(Nat.cast_nonneg D : (0 : ℝ) ≤ D)])
  have hNlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNr
  have h4log : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have h2log : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hcast : ((2^D : ℕ) : ℝ)=(2 : ℝ)^D := by norm_cast
  rw [hcast] at hl
  have h24 : (2 : ℝ)^D*(2 : ℝ)^D=(4 : ℝ)^D := by rw [←mul_pow]; norm_num
  have h8 : Real.log 8=Real.log 4+Real.log 2 := by
    rw [←Real.log_mul (by norm_num) (by norm_num)]; norm_num
  calc
    _ ≤ (2 : ℝ)^D*(Real.log 4+Real.log ((D : ℝ)+1)+(2 : ℝ)^D*Real.log ((N : ℝ)+1)) :=
      mul_le_mul_of_nonneg_left hl (by positivity)
    _ ≤ (2 : ℝ)^D*((2 : ℝ)^D*(Real.log 4+Real.log ((D : ℝ)+1))+
        (2 : ℝ)^D*(Real.log 2+Real.log (N : ℝ))) := by gcongr; nlinarith
    _ = _ := by rw [h8,←h24]; ring

lemma all_pattern_cost {α : Type*} (A : ℕ → Finset ℝ) (s : Finset α) (D : ℕ) :
    (2 : ℝ)^D*Real.log (2*((patternTotal A s D : ℝ)+1)) ≤
      (4 : ℝ)^D*(Real.log 8+Real.log ((D : ℝ)+1)+Real.log (s.card+1 : ℝ)+
        ∑ j ∈ Finset.range D, Real.log ((A j).card+1 : ℝ)) := by
  have h := scalar_pattern_cost D (pointBudget A s D) (patternTotal A s D)
    (pointBudget_pos A s D) (patternTotal_bound A s D)
  rw [log_pointBudget] at h
  convert h using 1 <;> first | rfl | ring


end SingleLatticeCovering.Shear

noncomputable section
namespace SingleLatticeCovering.Shear
open Real Filter Topology
open scoped BigOperators

lemma polynomial_pattern_cost {α : Type*} (A : ℕ → Finset ℝ) (s : Finset α)
    (D : ℕ) {L CL CA : ℝ} (hL : 1 ≤ L) (hCL : 0 ≤ CL) (hCA : 0 ≤ CA)
    (hD : (D : ℝ) ≤ L)
    (hlabel : Real.log (s.card+1 : ℝ) ≤ CL*L^2)
    (halphabet : ∀ j < D, Real.log ((A j).card+1 : ℝ) ≤ CA*L^2) :
    (2 : ℝ)^D*Real.log (2*((patternTotal A s D : ℝ)+1)) ≤
      (4 : ℝ)^D*(Real.log 8+1+CL+CA)*L^3 := by
  have hs : ∑ j ∈ Finset.range D, Real.log ((A j).card+1 : ℝ) ≤ (D : ℝ)*(CA*L^2) := by
    calc
      _ ≤ ∑ j ∈ Finset.range D, CA*L^2 := Finset.sum_le_sum (fun j hj => halphabet j (Finset.mem_range.mp hj))
      _ = _ := by simp [nsmul_eq_mul]
  have hlogD : Real.log ((D : ℝ)+1) ≤ L := by
    have hh := Real.log_le_sub_one_of_pos (show (0 : ℝ) < D+1 by positivity)
    linarith
  have h12 : L ≤ L^2 := by nlinarith
  have h23 : L^2 ≤ L^3 := by nlinarith [sq_nonneg (L-1)]
  have h01 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have hterm : Real.log 8+Real.log ((D : ℝ)+1)+Real.log (s.card+1 : ℝ)+
      ∑ j ∈ Finset.range D, Real.log ((A j).card+1 : ℝ) ≤ (Real.log 8+1+CL+CA)*L^3 := by
    have hsd := mul_le_mul_of_nonneg_right hD (show 0 ≤ CA*L^2 by positivity)
    have hlab := mul_le_mul_of_nonneg_left h23 hCL
    have hc := mul_le_mul_of_nonneg_left (show 1 ≤ L^3 by nlinarith) h01
    nlinarith
  calc
    _ ≤ (4 : ℝ)^D*(Real.log 8+Real.log ((D : ℝ)+1)+Real.log (s.card+1 : ℝ)+
      ∑ j ∈ Finset.range D, Real.log ((A j).card+1 : ℝ)) := all_pattern_cost A s D
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hterm (show 0 ≤ (4 : ℝ)^D by positivity)]

lemma log_label_count {α : Type*} (s : Finset α) {D n : ℕ} {Cs : ℝ}
    (hn : 1 ≤ Real.log (n : ℝ)) (hCs : 1 ≤ Cs) (hD : (D : ℝ) ≤ Real.log (n : ℝ))
    (hs : (s.card : ℝ) ≤ (Cs*(n : ℝ)^2)^D) :
    Real.log (s.card+1 : ℝ) ≤ (Real.log 2+Real.log Cs+2)*(Real.log (n : ℝ))^2 := by
  have hn0 : (0 : ℝ) < n := by
    by_contra h; have h0 : n=0 := by exact_mod_cast le_antisymm (le_of_not_gt h) (Nat.cast_nonneg n)
    subst n; norm_num at hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by exact_mod_cast (Nat.succ_le_iff.mpr (by exact_mod_cast hn0)))
  have hp : 0 < Cs*(n : ℝ)^2 := by positivity
  have hp1 : 1 ≤ (Cs*(n : ℝ)^2)^D := one_le_pow₀ (by nlinarith [sq_nonneg ((n : ℝ)-1)])
  have hl : Real.log (s.card+1 : ℝ) ≤ Real.log 2+(D : ℝ)*(Real.log Cs+2*Real.log (n : ℝ)) := by
    calc
      _ ≤ Real.log (2*(Cs*(n : ℝ)^2)^D) := Real.log_le_log (by positivity) (by linarith)
      _ = _ := by rw [Real.log_mul (by norm_num) (pow_pos hp _).ne',Real.log_pow,
        Real.log_mul (by positivity) (by positivity),Real.log_pow]; ring
  have hc : 0 ≤ Real.log Cs := Real.log_nonneg hCs
  have hl2 : Real.log (n : ℝ) ≤ (Real.log (n : ℝ))^2 := by nlinarith
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hh := mul_le_mul_of_nonneg_right hD (show 0 ≤ Real.log Cs+2*Real.log (n : ℝ) by linarith)
  nlinarith [mul_le_mul_of_nonneg_left hl2 hc,
    mul_le_mul_of_nonneg_left (show 1 ≤ (Real.log (n : ℝ))^2 by nlinarith) h2]

lemma log_alphabet_bound {b D : ℕ} {L : ℝ} (hL : 1 ≤ L)
    (hD : (D : ℝ) ≤ L) (hb : (b : ℝ) ≤ L) :
    Real.log 8+(D : ℝ)*Real.log ((D : ℝ)+2)+(b : ℝ)^2 ≤
      (Real.log 8+3)*L^2 := by
  have hlog : Real.log ((D : ℝ)+2) ≤ 2*L := by
    have hh := Real.log_le_sub_one_of_pos (show (0 : ℝ) < D+2 by positivity)
    linarith
  have hp := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg D)
  have hD' := mul_le_mul_of_nonneg_right hD (show 0 ≤ 2*L by linarith)
  have hb2 := pow_le_pow_left₀ (Nat.cast_nonneg b) hb 2
  have hc := mul_le_mul_of_nonneg_left (show 1 ≤ L^2 by nlinarith)
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 8))
  nlinarith



lemma eventually_pattern_cost {C Cs ε : ℝ} (hC : 0 < C) (hCs : 1 ≤ Cs) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ D : ℕ, (D : ℝ) ≤ C*((FinalRates.firstSize n : ℝ)+1) →
      ∀ {α : Type*} (s : Finset α) (A : ℕ → Finset ℝ),
      (s.card : ℝ) ≤ (Cs*(n : ℝ)^2)^D →
      (∀ j < D, Real.log ((A j).card+1 : ℝ) ≤
        Real.log 8+(D : ℝ)*Real.log ((D : ℝ)+2)+(FinalRates.firstSize n : ℝ)^2) →
      (2 : ℝ)^D*Real.log (2*((patternTotal A s D : ℝ)+1)) ≤ ε*(n : ℝ)*Real.log (n : ℝ) := by
  let H := Real.log 8+1+(Real.log 2+Real.log Cs+2)+(Real.log 8+3)
  have hH : 0 < H := by
    dsimp [H]
    linarith [Real.log_nonneg hCs,Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 8),
      Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  filter_upwards [FinalRates.eventually_dimension_small hC,
    FinalRates.eventually_dimension_power (C := C) (a := 4) (r := 1/2) hC (by norm_num) (by norm_num),
    FinalRates.eventually_firstSize_le_log (c := 1) (by norm_num),
    FinalRates.eventually_log_power_bound 3 (r := 1/2) (by norm_num) (div_pos hε hH),
    FinalRates.log_nat_atTop.eventually (eventually_ge_atTop (1 : ℝ)),eventually_ge_atTop (1 : ℕ)]
    with n hdim hpow hb hlog hn hn1
  intro D hD α s A hs hA
  have hDL := (hdim D hD).1
  have hbL : (FinalRates.firstSize n : ℝ) ≤ Real.log (n : ℝ) := by linarith
  have hc := polynomial_pattern_cost A s D hn
    (show 0 ≤ Real.log 2+Real.log Cs+2 by linarith [Real.log_nonneg hCs,Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)])
    (show 0 ≤ Real.log 8+3 by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 8)]) hDL
    (log_label_count s hn hCs hDL hs)
    (fun j hj => (hA j hj).trans (log_alphabet_bound hn hDL hbL))
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have he : (n : ℝ)^(1/2 : ℝ)*(n : ℝ)^(1/2 : ℝ)=(n : ℝ) := by
    rw [←Real.rpow_add (show (0 : ℝ) < n by exact_mod_cast hn1)]
    norm_num
  calc
    _ ≤ (4 : ℝ)^D*H*(Real.log (n : ℝ))^3 := hc
    _ ≤ (n : ℝ)^(1/2 : ℝ)*H*((ε/H)*(n : ℝ)^(1/2 : ℝ)) := by gcongr; exact hpow D hD
    _ = ε*(n : ℝ) := by calc
      _ = ε*((n : ℝ)^(1/2 : ℝ)*(n : ℝ)^(1/2 : ℝ)) := by field_simp
      _ = _ := by rw [he]
    _ ≤ _ := le_mul_of_one_le_right (mul_nonneg hε.le hn0) hn


end SingleLatticeCovering.Shear

end
end
end

section



noncomputable section
namespace SingleLatticeCovering.FinalRates
open Real Filter Topology Shear
open scoped BigOperators



lemma exp_error {n : ℕ} (hn : 2 ≤ n) {cost : ℝ}
    (hcost : cost ≤ (n : ℝ)*Real.log (n : ℝ)) :
    Real.exp (cost-(8*(n : ℝ)*Real.log (n : ℝ))/2) ≤
      1/(n : ℝ)^(2*n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hemp : cost-(8*(n : ℝ)*Real.log (n : ℝ))/2 ≤ -((2*n : ℕ) : ℝ)*Real.log (n : ℝ) := by
    push_cast; nlinarith [mul_nonneg (Nat.cast_nonneg n) hlog]
  apply (Real.exp_le_exp.mpr hemp).trans_eq
  rw [neg_mul,Real.exp_neg,Real.exp_nat_mul,Real.exp_log hn0,one_div]




theorem final_conditions {C k csec Csec κ Cs CR : ℝ}
    (hC : 0 < C) (hk : 0 < k) (hcsec : 0 < csec) (hCsec : 0 ≤ Csec)
    (hκ : 0 < κ) (hCs : 1 ≤ Cs) (hCR : 0 ≤ CR) :
    ∃ Cstar : ℝ, 0 < Cstar ∧ ∀ᶠ n : ℕ in atTop,
      2 ≤ n ∧ ∀ D : ℕ, (D : ℝ) ≤ C*((firstSize n : ℝ)+1) →
        D ≤ n ∧ 2 ≤ n-D ∧
        Csec*(Cstar*(n : ℝ)*Real.log (n : ℝ))*Real.exp (-k*(firstSize n : ℝ)^(70/100 : ℝ)) ≤ eta (n-D) ∧
        8*(n : ℝ)*Real.log (n : ℝ)+(2 : ℝ)^D*Real.sqrt ((n-D : ℕ) : ℝ) ≤
          csec*κ*(Cstar*(n : ℝ)*Real.log (n : ℝ)) ∧
        (1+CR)*(Cs*((n-D : ℕ) : ℝ)^2)^D*Real.exp (-Real.sqrt ((n-D : ℕ) : ℝ)/2)<1 ∧
        ∀ {α : Type*} (s : Finset α) (A : ℕ → Finset ℝ),
          (s.card : ℝ) ≤ (Cs*(n : ℝ)^2)^D →
          (∀ j < D, Real.log ((A j).card+1 : ℝ) ≤
            Real.log 8+(D : ℝ)*Real.log ((D : ℝ)+2)+(firstSize n : ℝ)^2) →
          let Lstar := 2*((patternTotal A s D : ℝ)+1)
          1 ≤ Lstar ∧ (patternTotal A s D : ℝ)<Lstar ∧
          Real.exp ((2 : ℝ)^D*Real.log Lstar-(8*(n : ℝ)*Real.log (n : ℝ))/2) ≤
            1/(n : ℝ)^(2*n) := by
  let Cstar : ℝ := 16/(csec*κ)
  have hstar : 0 < Cstar := div_pos (by norm_num) (mul_pos hcsec hκ)
  have hprod : csec*κ*Cstar=16 := by dsimp [Cstar]; field_simp
  refine ⟨Cstar,hstar,?_⟩
  filter_upwards [eventually_cap_eta (C := C) (H := Csec*Cstar) hC hk (mul_nonneg hCsec hstar.le),
    eventually_discard_bound (C := C) (ε := 8) hC (by norm_num),
    eventually_label_criterion hC hCs hCR,
    eventually_pattern_cost (C := C) (Cs := Cs) (ε := 1) hC hCs (by norm_num),
    eventually_dimension_small hC,eventually_ge_atTop (4 : ℕ)] with n hcap hdiscard hlabel hpat hdim hn
  refine ⟨by omega,?_⟩
  intro D hD
  have hDn := (hcap D hD).1
  have hm : (n : ℝ)/2 ≤ ((n-D : ℕ) : ℝ) := by rw [Nat.cast_sub hDn]; linarith [(hdim D hD).2]
  have hmn : n-D ≤ n := Nat.sub_le _ _
  have hmh : (2 : ℝ) ≤ ((n-D : ℕ) : ℝ) := by
    have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine ⟨hDn,by exact_mod_cast hmh,?_,?_,?_,?_⟩
  · convert (hcap D hD).2 using 1 ; ring
  · have hh := hdiscard D (n-D) hD hmn
    have he : csec*κ*(Cstar*(n : ℝ)*Real.log (n : ℝ))=16*(n : ℝ)*Real.log (n : ℝ) := by
      calc
        _ = (csec*κ*Cstar)*(n : ℝ)*Real.log (n : ℝ) := by ring
        _ = _ := by rw [hprod]
    rw [he]; linarith
  · exact hlabel D (n-D) hD hm hmn
  · intro α s A hs hA
    have hQ : 0 ≤ (patternTotal A s D : ℝ) := Nat.cast_nonneg _
    refine ⟨by linarith,by linarith,?_⟩
    exact exp_error (by omega) (by simpa using hpat D hD s A hs hA)


end SingleLatticeCovering.FinalRates

end
end

end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_Horizontal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section

namespace SingleLatticeCovering.Horizontal
open MeasureTheory Completion
open scoped ENNReal BigOperators



attribute [instance] FullLattice.discrete FullLattice.full


end SingleLatticeCovering.Horizontal

end
end

section

noncomputable section
namespace SingleLatticeCovering.FinalRates
open Real Filter Topology


lemma sectionRadius_pos {C : ℝ} (hC : 0 < C) (n : ℕ) : 0 < sectionRadius C n := by
  dsimp [sectionRadius]; positivity

lemma radius_sq_bound {C b r : ℝ} (hC : 0 ≤ C) (hb : 0 ≤ b)
    (hr : r ≤ C*(b*Real.log (b+1)+1)) : r ≤ ((C+1)*(b+1))^2 := by
  have hl : Real.log (b+1) ≤ b := by simpa using Real.log_le_sub_one_of_pos (by linarith : 0 < b+1)
  have hinner : b*Real.log (b+1)+1 ≤ (b+1)^2 := by nlinarith [mul_le_mul_of_nonneg_left hl hb]
  calc
    r ≤ C*(b*Real.log (b+1)+1) := hr
    _ ≤ C*(b+1)^2 := mul_le_mul_of_nonneg_left hinner hC
    _ ≤ (C+1)^2*(b+1)^2 := mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg C]) (sq_nonneg _)
    _ = _ := by ring

lemma eventually_first_polynomial {H r ε : ℝ} (hH : 0 < H) (hr : 0 < r) (hε : 0 < ε) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, H*((firstSize n : ℝ)+1)^k ≤ ε*(n : ℝ)^r := by
  filter_upwards [eventually_firstSize_le_log (by norm_num : (0 : ℝ) < 1),
    eventually_log_power_bound k hr (div_pos hε hH)] with n hfirst hlog
  simp only [one_mul] at hfirst
  calc
    _ ≤ H*(Real.log (n : ℝ))^k := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hfirst k) hH.le
    _ ≤ H*((ε/H)*(n : ℝ)^r) := mul_le_mul_of_nonneg_left hlog hH.le
    _ = _ := by field_simp




lemma eventually_marginal_scales {C α β γ C₀ : ℝ} (hC : 0 < C)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hC₀ : 0 ≤ C₀) :
    ∀ᶠ n : ℕ in atTop, ∀ D : ℕ, (D : ℝ) ≤ C*((firstSize n : ℝ)+1) →
      D ≤ n ∧ 2 ≤ n-D ∧ (D : ℝ) ≤ (n : ℝ)^α ∧
      6*(D : ℝ)*sectionRadius C n < (n : ℝ)^β ∧
      C₀*(n : ℝ)^(-γ) ≤ 1/2 ∧
      sectionRadius C n^2/((n-D : ℕ) : ℝ)^2 ≤ 1 := by
  have _ := hC₀
  have herr : ∀ᶠ n : ℕ in atTop, C₀*(n : ℝ)^(-γ) ≤ 1/2 := by
    have ht : Tendsto (fun n : ℕ => C₀*(n : ℝ)^(-γ)) atTop (𝓝 0) := by
      have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
      simpa only [mul_zero,Function.comp_def] using ((tendsto_rpow_neg_atTop hγ).comp hn).const_mul C₀
    exact ht.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1/2))
  filter_upwards [eventually_first_polynomial hC hα (by norm_num : (0 : ℝ) < 1) 1,
    eventually_first_polynomial (show 0 < 6*C*(C+1) by positivity) hβ (by norm_num : (0 : ℝ) < 1/2) 2,
    eventually_first_polynomial (show 0 < C+1 by linarith) (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 1/2) 1,
    eventually_dimension_small hC,herr,eventually_ge_atTop (4 : ℕ)] with n hDim hRad hSmall hDsmall he hn D hD
  simp only [pow_one,one_mul] at hDim
  simp only [pow_one,Real.rpow_one] at hSmall
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hdhalf := (hDsmall D hD).2
  have hDn : D ≤ n := by exact_mod_cast (show (D : ℝ) ≤ n by linarith)
  have hmhalf : (n : ℝ)/2 ≤ ((n-D : ℕ) : ℝ) := by rw [Nat.cast_sub hDn]; linarith
  have hm2 : (2 : ℝ) ≤ ((n-D : ℕ) : ℝ) := by linarith
  refine ⟨hDn,by exact_mod_cast hm2,hD.trans hDim,?_,he,?_⟩
  · have hDR : 6*(D : ℝ)*sectionRadius C n ≤ 6*C*(C+1)*((firstSize n : ℝ)+1)^2 := by
      dsimp [sectionRadius]
      have hh := mul_le_mul_of_nonneg_right hD (show 0 ≤ 6*((C+1)*((firstSize n : ℝ)+1)) by positivity)
      nlinarith
    have hp : 0 < (n : ℝ)^β := Real.rpow_pos_of_pos hn0 β
    exact hDR.trans_lt (hRad.trans_lt (by nlinarith))
  · have hRm : sectionRadius C n ≤ ((n-D : ℕ) : ℝ) := by
      dsimp [sectionRadius]
      linarith
    apply (div_le_one (sq_pos_of_pos (by linarith : (0 : ℝ) < ((n-D : ℕ) : ℝ)))).mpr
    exact pow_le_pow_left₀ (sectionRadius_pos hC n).le hRm 2


end SingleLatticeCovering.FinalRates

end
end

section

noncomputable section
namespace SingleLatticeCovering.Assembly
open MeasureTheory Folded LatticeGeometry Completion Shear CoverGeometry Vertical Sections Horizontal Inputs
open Filter Topology
open scoped BigOperators Pointwise ENNReal

lemma body_volume_pos {n : ℕ} {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (hi : (interior K).Nonempty) : 0 < (volume K).toReal := by
  apply ENNReal.toReal_pos (ne_of_gt ?_) hK.measure_ne_top
  exact (isOpen_interior.measure_pos volume hi).trans_le (measure_mono interior_subset)

lemma affine_body {n : ℕ} (e : (Fin n → ℝ) ≃ᵃ[ℝ] (Fin n → ℝ))
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hc : Convex ℝ K) (hi : (interior K).Nonempty) :
    IsCompact (e '' K) ∧ Convex ℝ (e '' K) ∧ (interior (e '' K)).Nonempty := by
  let he : (Fin n → ℝ) ≃ₜ (Fin n → ℝ) :=
    { toEquiv := e.toEquiv
      continuous_toFun := e.toAffineMap.continuous_of_finiteDimensional
      continuous_invFun := e.symm.toAffineMap.continuous_of_finiteDimensional }
  refine ⟨hK.image he.continuous, hc.affine_image e.toAffineMap,?_⟩
  change (interior (he '' K)).Nonempty
  rw [←he.image_interior]
  exact hi.image he

lemma chain_first_le_dim {B : Block} (c : Chain B) : c.first.b ≤ c.dim := by
  induction c with
  | base B => rfl
  | append c B w ih => exact ih.trans (Nat.le_add_right _ _)


end SingleLatticeCovering.Assembly

end
end

end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_GaussianSections
attribute [-instance] _root_.OAI.SingleLatticeCovering.RogersPreparation.lattice_vadd_invariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace SingleLatticeCovering.Horizontal
open Completion MeasureTheory Set Topology
open scoped ENNReal Pointwise

lemma latticeProjection_isOpen {m : ℕ} (L : FullLattice m) :
    IsOpenMap (latticeProjection L.module) := by
  have hp : IsOpenMap (fun x : Fin m → ℝ => fun i => (x i : AddCircle (1 : ℝ))) :=
    IsOpenMap.piMap (fun _ => QuotientAddGroup.isOpenMap_coe)
      (Filter.Eventually.of_forall (fun _ => QuotientAddGroup.mk'_surjective _))
  exact hp.comp (latticeBasis L.module).equivFun.toContinuousLinearEquiv.toHomeomorph.isOpenMap



lemma exists_torus_transport {m : ℕ} (L N : FullLattice m)
    (e : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (hker : ∀ x, e x ∈ N.module ↔ x ∈ L.module) :
    ∃ T : Torus m ≃+ Torus m, Continuous T ∧
      MeasurePreserving T (torusMeasure m) (torusMeasure m) ∧
      ∀ x, T (latticeProjection L.module x)=latticeProjection N.module (e x) := by
  let p := latticeProjection L.module
  let q := (latticeProjection N.module).toAddMonoidHom.comp e.toAddMonoidHom
  have hp : Function.Surjective p := latticeProjection_surjective L.module
  have hq : Function.Surjective q := (latticeProjection_surjective N.module).comp e.surjective
  have heq {x y : Fin m → ℝ} : p x=p y ↔ q x=q y := by
    have h : p (x-y)=0 ↔ q (x-y)=0 :=
      ((latticeProjection_eq_zero_iff L.module (x-y)).trans
      ((hker (x-y)).symm.trans (latticeProjection_eq_zero_iff N.module (e (x-y))).symm))
    simpa only [map_sub,sub_eq_zero] using h
  let lift : Torus m → Torus m := fun t => q (Classical.choose (hp t))
  have hlift (x) : lift (p x)=q x := heq.mp (Classical.choose_spec (hp (p x)))
  let f : Torus m →+ Torus m :=
    { toFun := lift
      map_zero' := by simpa only [map_zero] using hlift 0
      map_add' := by
        intro a b
        obtain ⟨x,rfl⟩ := hp a
        obtain ⟨y,rfl⟩ := hp b
        rw [←map_add,hlift,map_add,hlift,hlift] }
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      obtain ⟨x,rfl⟩ := hp a
      obtain ⟨y,rfl⟩ := hp b
      exact heq.mpr (by simpa only [f,AddMonoidHom.coe_mk,ZeroHom.coe_mk,hlift] using hab)
    · intro t
      obtain ⟨x,hx⟩ := hq t
      exact ⟨p x,(hlift x).trans hx⟩
  have hcont : Continuous f := by
    apply ((latticeProjection_isOpen L).isQuotientMap p.continuous hp).continuous_iff.mpr
    have hh : (f ∘ p)=q := funext hlift
    rw [hh]
    exact (latticeProjection N.module).continuous.comp e.toContinuousLinearEquiv.continuous
  let T := AddEquiv.ofBijective f hf
  refine ⟨T,hcont,?_,hlift⟩
  exact f.measurePreserving hcont hf.2 rfl

namespace FullLattice

lemma image_covolume {m : ℕ} (L : FullLattice m) (e : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ)) :
    ZLattice.covolume (L.image e).module volume =
      |LinearMap.det e.toLinearMap| * ZLattice.covolume L.module volume :=
  LatticeGeometry.image_covolume L.module e



lemma image_hole {m : ℕ} (L : FullLattice m) (e : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    {J : Set (Fin m → ℝ)} (hJ : IsCompact J) : (L.image e).hole (e '' J)=L.hole J := by
  obtain ⟨T,hTc,hTm,hT⟩ := exists_torus_transport L (L.image e) e (by
    intro x
    change e.symm (e x) ∈ L.module ↔ x ∈ L.module
    rw [e.symm_apply_apply])
  have himage : latticeProjection (L.image e).module '' (e '' J)=
      T '' (latticeProjection L.module '' J) := by
    simp only [image_image]
    congr 1
    funext x
    exact (hT x).symm
  have hmeas : MeasurableSet ((latticeProjection (L.image e).module '' (e '' J))ᶜ) :=
    ((hJ.image e.toContinuousLinearEquiv.continuous).image
      (latticeProjection (L.image e).module).continuous).measurableSet.compl
  unfold hole
  rw [←hTm.measure_preimage hmeas.nullMeasurableSet,himage,preimage_compl,
    Set.preimage_image_eq _ T.injective]
end FullLattice

end SingleLatticeCovering.Horizontal

end
end

section

noncomputable section
namespace SingleLatticeCovering.Inputs
open Completion Horizontal MeasureTheory Set Topology
open scoped ENNReal Pointwise




lemma determinantScale_det {m : ℕ} (hm : 0 < m) (Dh : ℝ) (hDh : 0 < Dh) :
    LinearMap.det (determinantScale m Dh hDh).toLinearMap=Dh := by
  change LinearMap.det (Dh^((m : ℝ)⁻¹) • (LinearMap.id : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)))=Dh
  rw [LinearMap.det_smul, LinearMap.det_id, mul_one]
  have hdim : Module.finrank ℝ (Fin m → ℝ)=m := by simp
  rw [hdim,←Real.rpow_natCast,←Real.rpow_mul hDh.le,
    inv_mul_cancel₀ (by exact_mod_cast hm.ne'),Real.rpow_one]

lemma compact_linear_preimage {m : ℕ} {J : Set (Fin m → ℝ)} (hJ : IsCompact J)
    (e : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ)) : IsCompact (e.symm '' J) :=
  hJ.image e.symm.toContinuousLinearEquiv.continuous

lemma determinant_preimage_volume {m : ℕ}
    (e : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ)) (Dh : ℝ) (hDh : 0 < Dh)
    (hdet : |LinearMap.det e.toLinearMap|=Dh) (J : Set (Fin m → ℝ)) :
    (volume (e.symm '' J)).toReal=(volume J).toReal/Dh := by
  have h := LatticeGeometry.affine_image_volume e 0 (e.symm '' J)
  have he : (fun x => e x+0) '' (e.symm '' J)=J := by
    simp only [add_zero]
    change e '' (e.symm '' J)=J
    exact e.image_symm_image J
  rw [he,hdet] at h
  have hh := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal hDh.le] at hh
  apply (eq_div_iff hDh.ne').mpr
  linarith




end SingleLatticeCovering.Inputs

end
end

end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_CircuitErrors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section








section











noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators

namespace SingleLatticeCovering.PrimeKernel
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


lemma basis_apply (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) (j k : ι) :
    basis p hp i a j k =
      if k=i then (if j=i then (p : ℝ) else -(a j : ℝ))
      else if j=k then 1 else 0 := by
  simp only [basis, Basis.coe_ofEquivFun,coordinates,LinearEquiv.coe_symm_mk]
  by_cases hki : k=i
  · subst k
    by_cases hji : j=i
    · subst j
      simp [tailForm,Function.update_self,Pi.single_apply,Finset.mem_erase]
    · simp [tailForm,Function.update_self,Pi.single_apply,hji,Finset.mem_erase,eq_comm]
  · simp [Pi.single_apply,hki,eq_comm]

lemma covolume_lattice (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) :
    ZLattice.covolume (lattice p hp i a) = p := by
  change ZLattice.covolume (span ℤ (Set.range (basis p hp i a))) = _
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume
    (ZSpan.isAddFundamentalDomain (basis p hp i a) volume),
    ZSpan.volume_real_fundamentalDomain]
  let v : ι → ℝ := fun k => if k=i then p else -(a k : ℝ)
  have he : Matrix.of (basis p hp i a) = ((1 : Matrix ι ι ℝ).updateRow i v).transpose := by
    ext j k
    rw [Matrix.of_apply,basis_apply]
    by_cases hki : k=i
    · subst k; simp [v]
    · simp [Matrix.transpose_apply,Matrix.one_apply,hki,eq_comm]
  have hs : (∑ j, v j • (1 : Matrix ι ι ℝ) j) = v := by
    ext k
    simp [Matrix.one_apply,Pi.smul_apply,smul_eq_mul]
  rw [he,Matrix.det_transpose,←hs,Matrix.det_updateRow_sum]
  simp [v,abs_of_pos (show (0 : ℝ)<p by exact_mod_cast hp)]





end SingleLatticeCovering.PrimeKernel




end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_PrimeKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
section
noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators

namespace SingleLatticeCovering.PrimeKernel
open LatticeGeometry Module Submodule MeasureTheory
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma normalizeEquiv_det (p : ℕ) (hp : 0 < p) (i : ι) :
    LinearMap.det (normalizeEquiv (ι := ι) p hp).toLinearMap=(p : ℝ)⁻¹ := by
  have hpR : (0 : ℝ)<p := by exact_mod_cast hp
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨i⟩).ne'
  change LinearMap.det (scaleFactor (ι := ι) p • (LinearMap.id : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)))=_
  rw [LinearMap.det_smul,LinearMap.det_id,mul_one,Module.finrank_pi]
  rw [scaleFactor,←Real.rpow_natCast,←Real.rpow_mul hpR.le]
  have he : -(Fintype.card ι : ℝ)⁻¹*(Fintype.card ι : ℝ) = -1 := by field_simp
  rw [he,Real.rpow_neg_one]

lemma covolume_normalized (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) :
    ZLattice.covolume (normalized p hp i a)=1 := by
  have hpR : (0 : ℝ)<p := by exact_mod_cast hp
  rw [image_covolume,normalizeEquiv_det p hp i,covolume_lattice,
    abs_of_pos (inv_pos.mpr hpR),inv_mul_cancel₀ hpR.ne']



end SingleLatticeCovering.PrimeKernel

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_MeanHoles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
section
noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators
noncomputable section
noncomputable section

namespace SingleLatticeCovering.PrimeKernel
open Set MeasureTheory Filter Topology Horizontal ConvexGrid SimplexYoung
open scoped Pointwise ENNReal BigOperators
variable {n : ℕ}

lemma ensembleFull_covolume (p : ℕ) (hp : 0 < p) (a : Fin n → ZMod p) :
    ZLattice.covolume (ensembleFull p hp a).module=1 :=
  covolume_normalized p hp 0 (liftCoeff a)


end SingleLatticeCovering.PrimeKernel

namespace SingleLatticeCovering.PrimeKernel
open Set MeasureTheory Filter Topology Horizontal ConvexGrid SimplexYoung
open scoped Pointwise ENNReal BigOperators
variable {n : ℕ}

lemma exists_le_finite_average {A : Type*} [Fintype A] [Nonempty A] (f : A → ℝ) :
    ∃ a, f a ≤ (Fintype.card A : ℝ)⁻¹*∑ b, f b := by
  have hc : (Fintype.card A : ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have he : (∑ a : A, f a)=∑ _a : A, (Fintype.card A : ℝ)⁻¹*∑ b, f b := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    rw [←mul_assoc,mul_inv_cancel₀ hc,one_mul]
  obtain ⟨a,_,ha⟩ := Finset.exists_le_of_sum_le (Finset.univ_nonempty (α := A)) he.le
  exact ⟨a,ha⟩

lemma weighted_meanPrimeHole_sample {I : Type*} [Fintype I]
    (p : ℕ) [Fact p.Prime] (J : I → Set (Fin (n+1) → ℝ)) (w : I → ℝ) :
    ∃ a : Fin n → ZMod p,
      (∑ i, w i*((ensembleFull p (Nat.Prime.pos Fact.out) a).hole (J i)).toReal) ≤
        ∑ i, w i*meanPrimeHole (J i) p := by
  classical
  obtain ⟨a,ha⟩ := exists_le_finite_average
    (fun a : Fin n → ZMod p => ∑ i, w i*((ensembleFull p (Nat.Prime.pos Fact.out) a).hole (J i)).toReal)
  refine ⟨a,ha.trans_eq ?_⟩
  rw [Fintype.card_fun,Fintype.card_fin,ZMod.card,Nat.cast_pow,Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  unfold meanPrimeHole
  rw [←Finset.mul_sum]
  ring



theorem common_horizontal_source {I : Type*} [Fintype I]
    (J : I → Set (Fin (n+1) → ℝ)) (hJ : ∀ i, IsCompact (J i))
    (hconv : ∀ i, Convex ℝ (J i)) (hd : 270 ≤ n+1)
    (hVeta : ∀ i, volume.real (J i) ≤ sourceEta (n+1))
    (hcrit : 302*(∑ i, Real.exp (-volume.real (J i)/2)) ≤ 1) :
    ∃ L : FullLattice (n+1), ZLattice.covolume L.module=1 ∧ ∀ i,
      L.hole (J i) ≤ ENNReal.ofReal (Real.exp (-volume.real (J i)/2)) := by
  classical
  choose N hN using fun i => eventually_meanPrimeHole_all hd (hJ i) (hconv i) (hVeta i)
  obtain ⟨p,hpN,hpPrime⟩ := Nat.exists_infinite_primes (Finset.univ.sup N)
  let : Fact p.Prime := ⟨hpPrime⟩
  have hp : 0 < p := hpPrime.pos
  obtain ⟨a,ha⟩ := weighted_meanPrimeHole_sample p J
    (fun i => Real.exp (volume.real (J i)/2))
  have hnumeric (i : I) : Real.exp (volume.real (J i)/2)*meanPrimeHole (J i) p ≤
      302*Real.exp (-volume.real (J i)/2) := by
    have hh := mul_le_mul_of_nonneg_left
      (hN i p ((Finset.le_sup (f:=N) (Finset.mem_univ i)).trans hpN))
      (Real.exp_pos (volume.real (J i)/2)).le
    have hfirst : Real.exp (volume.real (J i)/2)*Real.exp (-volume.real (J i)) =
        Real.exp (-volume.real (J i)/2) := by rw [←Real.exp_add]; congr 1; ring
    have hsecond : Real.exp (volume.real (J i)/2)*Real.exp (-sourceEta (n+1)) ≤
        Real.exp (-volume.real (J i)/2) := by
      rw [←Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith [hVeta i])
    calc
      _ ≤ Real.exp (volume.real (J i)/2) *
          (Real.exp (-volume.real (J i))+301*Real.exp (-sourceEta (n+1))) := hh
      _ = Real.exp (-volume.real (J i)/2)+
          301*(Real.exp (volume.real (J i)/2)*Real.exp (-sourceEta (n+1))) := by
        rw [mul_add,hfirst]
        ring
      _ ≤ Real.exp (-volume.real (J i)/2)+301*Real.exp (-volume.real (J i)/2) :=
        add_le_add_right (mul_le_mul_of_nonneg_left hsecond (by norm_num : (0:ℝ) ≤ 301)) _
      _ = _ := by ring
  have hsum : (∑ i, Real.exp (volume.real (J i)/2)*((ensembleFull p hp a).hole (J i)).toReal) ≤ 1 := by
    apply ha.trans
    have hs := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hnumeric i)
    rw [←Finset.mul_sum] at hs
    exact hs.trans hcrit
  refine ⟨ensembleFull p hp a,ensembleFull_covolume p hp a,fun i => ?_⟩
  have hsingle := Finset.single_le_sum (s:=Finset.univ)
    (f:=fun j => Real.exp (volume.real (J j)/2)*((ensembleFull p hp a).hole (J j)).toReal)
    (fun j _ => mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg) (Finset.mem_univ i)
  have hh := mul_le_mul_of_nonneg_left (hsingle.trans hsum)
    (Real.exp_pos (-volume.real (J i)/2)).le
  have he : Real.exp (-volume.real (J i)/2)*Real.exp (volume.real (J i)/2)=1 := by
    rw [←Real.exp_add]
    rw [show -volume.real (J i)/2+volume.real (J i)/2=0 by ring,Real.exp_zero]
  simp only [←mul_assoc,he,one_mul,mul_one] at hh
  have hf : (ensembleFull p hp a).hole (J i)≠∞ := by
    unfold FullLattice.hole
    exact measure_ne_top _ _
  exact (ENNReal.toReal_le_toReal hf ENNReal.ofReal_ne_top).mp
    (by rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]; exact hh)


end SingleLatticeCovering.PrimeKernel


namespace SingleLatticeCovering.PrimeKernel
open SimplexYoung Inputs Horizontal MeasureTheory Set
open scoped ENNReal BigOperators
variable {n : ℕ}




theorem scaled_common_horizontal_source {I : Type*} [Fintype I]
    (J : I → Set (Fin (n+1) → ℝ)) (hJ : ∀ i, IsCompact (J i))
    (hconv : ∀ i, Convex ℝ (J i)) (hd : 270 ≤ n+1) (Dh : ℝ) (hDh : 0 < Dh)
    (hu : ∀ i, (volume (J i)).toReal/Dh ≤ sourceEta (n+1))
    (hcrit : 302*(∑ i, Real.exp (-((volume (J i)).toReal/Dh)/2)) ≤ 1) :
    ∃ L : FullLattice (n+1), ZLattice.covolume L.module=Dh ∧ ∀ i,
      L.hole (J i) ≤ ENNReal.ofReal (Real.exp (-((volume (J i)).toReal/Dh)/2)) := by
  let e := determinantScale (n+1) Dh hDh
  have hdet : |LinearMap.det e.toLinearMap|=Dh := by
    rw [determinantScale_det (Nat.succ_pos n),abs_of_pos hDh]
  let J' : I → Set (Fin (n+1) → ℝ) := fun i => e.symm '' J i
  have hc (i : I) : IsCompact (J' i) := compact_linear_preimage (hJ i) e
  have hv (i : I) : volume.real (J' i)=(volume (J i)).toReal/Dh :=
    determinant_preimage_volume e Dh hDh hdet (J i)
  obtain ⟨L,hLc,hL⟩ := common_horizontal_source J' hc
    (fun i => (hconv i).linear_image e.symm.toLinearMap) hd
    (by intro i; rw [hv i]; exact hu i) (by simpa only [hv] using hcrit)
  refine ⟨L.image e,?_,?_⟩
  · rw [FullLattice.image_covolume,hdet,hLc,mul_one]
  · intro i
    have hh := L.image_hole e (hc i)
    have he : e '' J' i=J i := e.image_symm_image (J i)
    rw [he] at hh
    rw [hh]
    simpa only [hv] using hL i



theorem common_horizontal_from_circuits {m : ℕ} {α : Type*}
    (J : α → Set (Fin m → ℝ)) (s : Finset α) (Dh τ N : ℝ)
    (hm : 270 ≤ m) (hDh : 0 < Dh)
    (hJ : ∀ a∈s, IsCompact (J a)) (hconv : ∀ a∈s, Convex ℝ (J a))
    (hlo : ∀ a∈s, τ ≤ (volume (J a)).toReal/Dh)
    (hhi : ∀ a∈s, (volume (J a)).toReal/Dh ≤ sourceEta m)
    (hcard : (s.card : ℝ) ≤ N)
    (hcriterion : 302*N*Real.exp (-τ/2)<1) :
    ∃ L : FullLattice m, ZLattice.covolume L.module=Dh ∧ ∀ a∈s,
      L.hole (J a) ≤ ENNReal.ofReal (Real.exp (-((volume (J a)).toReal/Dh)/2)) := by
  classical
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m≠0)
  let I := {a // a∈s}
  have hsum : 302*(∑ i : I, Real.exp (-((volume (J i.val)).toReal/Dh)/2)) ≤ 1 := by
    calc
      _ ≤ 302*(∑ _i : I, Real.exp (-τ/2)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 302)
        exact Finset.sum_le_sum (fun i _ => Real.exp_le_exp.mpr (by linarith [hlo i.val i.prop]))
      _ = 302*(s.card : ℝ)*Real.exp (-τ/2) := by
        simp only [Finset.sum_const,Finset.card_univ,I,Fintype.card_coe,nsmul_eq_mul]
        ring
      _ ≤ 302*N*Real.exp (-τ/2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard (by norm_num)) (Real.exp_pos _).le
      _ ≤ 1 := hcriterion.le
  obtain ⟨L,hLc,hL⟩ := scaled_common_horizontal_source (fun i : I => J i.val)
    (fun i => hJ i.val i.prop) (fun i => hconv i.val i.prop) hm Dh hDh
    (fun i => hhi i.val i.prop) hsum
  exact ⟨L,hLc,fun a ha => hL ⟨a,ha⟩⟩



end SingleLatticeCovering.PrimeKernel


noncomputable section
namespace SingleLatticeCovering.Assembly
open PrimeKernel SimplexYoung MeasureTheory Folded LatticeGeometry Completion Shear CoverGeometry Vertical Sections Horizontal
open scoped BigOperators Pointwise ENNReal




theorem sections_and_circuits_cover {B : Block} (c : Chain B) {m : ℕ}
    (hm : 270 ≤ m) (hD : 0 < c.fullDim)
    (K : Set (Fin (m+c.fullDim) → ℝ)) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hV : 0 < (volume K).toReal) {R : ℝ} (hR : 0 < R)
    (hrad : c.radiusSq+(B.terminalDim : ℝ) ≤ R^2)
    (hsmall : R^2/(m : ℝ)^2 ≤ 1)
    (hgauss : ∀ y : c.FullVec, ‖WithLp.toLp 2 y‖ ≤ 6*(c.fullDim : ℝ)*R →
      (volume K).toReal*gamma y/2 ≤ (volume (coordinateFiber K y)).toReal)
    (κ ρ ε τ A : ℝ) (hρ : 0 < ρ) (hτ : 0 ≤ τ) (hA : 0 < A)
    (hpat : ∀ y : c.FullVec, ∃ P : Finset c.FullVec,
      P.Nonempty ∧ SuffixBinary P ∧
      (∀ l ∈ P, l ∈ c.fullRaw ∧ c.FullResidual y l ∧ c.det*gamma (y-c.fullLinear l) ≤ ε) ∧
      κ ≤ ∑ l ∈ P, c.det*gamma (y-c.fullLinear l))
    (hload : A+(2^c.fullDim : ℕ)*τ ≤ (Real.exp (-1)/8)*κ*ρ)
    (hcap : (Real.exp 1/8)*ρ*ε ≤ FinalRates.eta m)
    (hcriterion : 302*(3*(m : ℝ)^2)^c.fullDim*Real.exp (-τ/2)<1)
    (hcount : ∀ {α : Type} (s : Finset α), (s.card : ℝ) ≤ (3*(m : ℝ)^2)^c.fullDim →
      let Lstar := 2*((patternTotal c.alphabetSeq s c.fullDim : ℝ)+1)
      1 ≤ Lstar ∧ (patternTotal c.alphabetSeq s c.fullDim : ℝ)<Lstar ∧
      Real.exp ((2 : ℝ)^c.fullDim*Real.log Lstar-A/2) ≤
        1/((m+c.fullDim : ℕ) : ℝ)^(2*(m+c.fullDim))) :
    ∃ (Λ : Submodule ℤ (Fin (m+c.fullDim) → ℝ)) (_ : DiscreteTopology Λ),
      IsZLattice ℝ Λ ∧ K+(Λ : Set (Fin (m+c.fullDim) → ℝ))=Set.univ ∧
      (volume K).toReal/ZLattice.covolume Λ volume ≤ Real.exp 1*ρ := by
  classical
  let Dh := (volume K).toReal/(ρ*c.det)
  have hDh : 0 < Dh := div_pos hV (mul_pos hρ c.det_pos)
  obtain ⟨e,heK,heconv,hevol,S,hSc,J,hJ,hsections⟩ :=
    coordinate_marginal_to_labels (by omega : 2 ≤ m) hD hK hconv hV hR hsmall hgauss
  let α := {a // a ∈ S}
  let J' : α → Set (Fin m → ℝ) := fun a => J a.val
  let u : α → ℝ := fun a => (volume (J' a)).toReal/Dh
  let s : Finset α := Finset.univ.filter (fun a => τ ≤ u a ∧ u a ≤ (Real.exp 1/8)*ρ*ε)
  have hcard : (s.card : ℝ) ≤ (3*(m : ℝ)^2)^c.fullDim := by
    have hh : s.card ≤ S.card := by
      calc
        s.card ≤ (Finset.univ : Finset α).card := Finset.card_le_card (Finset.filter_subset _ _)
        _ = S.card := by simp [α]
    exact (by exact_mod_cast hh : (s.card : ℝ) ≤ S.card).trans hSc
  have hulo (a : α) (ha : a ∈ s) : τ ≤ u a := (Finset.mem_filter.mp ha).2.1
  have huhi (a : α) (ha : a ∈ s) : u a ≤ FinalRates.eta m :=
    ((Finset.mem_filter.mp ha).2.2).trans hcap
  obtain ⟨L,hLc,hLhole⟩ := common_horizontal_from_circuits J' s Dh
    τ ((3*(m : ℝ)^2)^c.fullDim) hm hDh
    (by intro a ha; exact (hJ a.val a.property).1)
    (by intro a ha; exact (hJ a.val a.property).2.1)
    hulo huhi hcard hcriterion
  let Lstar := 2*((patternTotal c.alphabetSeq s c.fullDim : ℝ)+1)
  obtain ⟨hLstar,hcost,herror⟩ := hcount s hcard
  have hV' : 0 < (volume (e '' K)).toReal := by rwa [hevol]
  have hcov' : ZLattice.covolume L.module volume=(volume (e '' K)).toReal/(ρ*c.det) := by
    rw [hevol]; exact hLc
  obtain ⟨Λ,hd,hfull,hcover,hbound⟩ := labeled_chain_to_cover c (by omega) L.module (e '' K)
    heK heconv hV' J' (fun a => (hJ a.val a.property).1)
    κ ρ (Real.exp (-1)/8) (Real.exp 1/8) ε τ A Lstar hρ (by positivity) (by positivity)
    hτ hA hcov' hpat (by
      intro v hv
      obtain ⟨a,ha,hin,hl,hu⟩ := hsections v (hv.trans hrad)
      exact ⟨⟨a,ha⟩,hin,hl,hu⟩) (by
      intro a hlo hhi
      have ha : a ∈ s := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,?_,?_⟩
        · simpa only [hLc] using hlo
        · simpa only [hLc] using hhi
      simpa only [FullLattice.hole,hLc] using hLhole a ha) hload hLstar (by
      simpa only [hLc,s,u,patternTotal,Lstar] using hcost) (by
      simpa only [Nat.cast_pow,Nat.cast_ofNat] using herror)
  let := hd
  let := hfull
  exact pull_back_cover e K Λ hcover hbound


end SingleLatticeCovering.Assembly


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_GaussianPositions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SingleLatticeCovering.FinalRates
open Real Filter Topology Asymptotics

lemma sectionRadius_le_localScale (C : ℝ) (n : ℕ) :
    sectionRadius C n ≤ (localScale C n : ℝ) := by
  have H := Nat.le_ceil (sectionRadius C n)
  dsimp [localScale]
  push_cast
  linarith

lemma dimension_le_localScale {C : ℝ} (hC : 0 < C) {n D : ℕ}
    (hD : (D:ℝ) ≤ C*((firstSize n:ℝ)+1)) : D ≤ localScale C n := by
  have _ := hC
  have hc := sectionRadius_le_localScale C n
  have hh : (D:ℝ) ≤ (localScale C n:ℝ) := by
    dsimp [sectionRadius] at hc
    nlinarith [show (0:ℝ) ≤ (firstSize n:ℝ) by positivity]
  exact_mod_cast hh

lemma localScale_tendsto {C : ℝ} (hC : 0 < C) : Tendsto (localScale C) atTop atTop := by
  apply tendsto_atTop_mono _ firstSize_tendsto
  intro n
  have H := sectionRadius_le_localScale C n
  dsimp [sectionRadius] at H
  exact_mod_cast (show (firstSize n:ℝ) ≤ (localScale C n:ℝ) by
    nlinarith [show (0:ℝ) ≤ (firstSize n:ℝ) by positivity])

lemma eventually_localScale_root {C : ℝ} (hC : 0 < C) : ∀ᶠ n : ℕ in atTop,
    Real.exp ((localScale C n:ℝ)^30) ≤ Real.sqrt (Real.sqrt (n:ℝ)) := by
  let H : ℝ := 3*(C+2)
  have hH : 0 < H := by dsimp [H]; positivity
  have hsmall : (fun n : ℕ => (Real.log (Real.log (n:ℝ)))^60) =o[atTop]
      (fun n => Real.log (n:ℝ)) := by
    simpa only [Function.comp_def,Real.rpow_natCast,Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop ((60:ℕ):ℝ) (by norm_num : (0:ℝ) < 1)).comp_tendsto log_nat_atTop
  filter_upwards [hsmall.bound (by positivity : 0 < 1/(4*H^30)),
    loglog_nat_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    eventually_ge_atTop (1:ℕ)] with n hbound hs hn
  have hnp : (0:ℝ) < n := by exact_mod_cast hn
  have hs0 : 0 ≤ Real.log (Real.log (n:ℝ)) := le_trans zero_le_one hs
  have hs2 : 1 ≤ (Real.log (Real.log (n:ℝ)))^2 := one_le_pow₀ hs
  have hceil := Nat.ceil_lt_add_one (sq_nonneg (Real.log (Real.log (n:ℝ))))
  change (firstSize n:ℝ) < (Real.log (Real.log (n:ℝ)))^2+1 at hceil
  have hlceil := Nat.ceil_lt_add_one (sectionRadius_pos hC n).le
  have hl : (localScale C n:ℝ) ≤ H*(Real.log (Real.log (n:ℝ)))^2 := by
    dsimp [localScale,sectionRadius]
    push_cast
    dsimp [sectionRadius] at hlceil
    have hh := mul_le_mul_of_nonneg_left hceil.le (show 0 ≤ C+1 by linarith)
    dsimp [H]
    nlinarith [mul_nonneg (show 0 ≤ 2*C+5 by linarith) (sub_nonneg.mpr hs2)]
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hs0 _),
    abs_of_nonneg (Real.log_natCast_nonneg n)] at hbound
  have hpow : (localScale C n:ℝ)^30 ≤ H^30*(Real.log (Real.log (n:ℝ)))^60 := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg (localScale C n)) hl 30
    simpa only [mul_pow,←pow_mul] using hh
  have hexp : 4*(localScale C n:ℝ)^30 ≤ Real.log (n:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hbound (by positivity : 0 ≤ 4*H^30)
    have he : (4*H^30)*(1/(4*H^30)*Real.log (n:ℝ))=Real.log (n:ℝ) := by field_simp
    rw [he] at hh
    nlinarith
  have hlog : Real.log (Real.sqrt (Real.sqrt (n:ℝ)))=Real.log (n:ℝ)/4 := by
    rw [Real.log_sqrt (Real.sqrt_nonneg _),Real.log_sqrt hnp.le]
    ring
  rw [←Real.exp_log (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hnp))]
  apply Real.exp_le_exp.mpr
  rw [hlog]
  linarith


end SingleLatticeCovering.FinalRates



namespace SingleLatticeCovering.GaussianNumerics
open MeasureTheory MeasureTheory.Measure Set Filter Topology GaussianDensity CanonicalDensity Sections
open scoped ENNReal

lemma normalizer_half (D : ℕ) : normalizer D (1/2)=(Real.sqrt (2*Real.pi))^D := by
  unfold normalizer
  rw [show Real.pi/(1/2)=2*Real.pi by ring,Real.sqrt_eq_rpow,
    ←Real.rpow_natCast,←Real.rpow_mul (by positivity : 0 ≤ 2*Real.pi)]
  congr 1
  ring

lemma density_half_gaussian {D : ℕ} (y : E D) :
    GaussianDensity.density (1/2) y=Sections.gaussian (E D) y := by
  unfold GaussianDensity.density Sections.gaussian
  rw [normalizer_half,finrank_euclideanSpace_fin,zpow_neg,zpow_natCast]
  congr 1
  congr 1
  ring


theorem eventually_local_coordinate_position : ∀ᶠ l : ℕ in atTop,
    ∀ m D : ℕ, D ≤ l → 0 < m+D →
      Real.exp ((l:ℝ)^30) ≤ Real.sqrt (Real.sqrt ((m+D : ℕ):ℝ)) →
      ∀ K : Set (Fin (m+D) → ℝ), IsCompact K → Convex ℝ K → (interior K).Nonempty →
        ∃ e : (Fin (m+D) → ℝ) ≃ᵃ[ℝ] (Fin (m+D) → ℝ),
          ∀ y : Fin D → ℝ, ‖WithLp.toLp 2 y‖ ≤ 6*(l:ℝ)^2 →
            (volume (e '' K)).toReal*Folded.gamma y/2 ≤
              (volume (coordinateFiber (e '' K) y)).toReal := by
  filter_upwards [eventually_local_position] with l hl
  intro m D hD hn hroot K hK hc hi
  let A : (Fin (m+D) → ℝ) ≃ₗ[ℝ] E (m+D) := (WithLp.linearEquiv 2 ℝ (Fin (m+D) → ℝ)).symm
  have hAK : IsCompact (A '' K) := hK.image A.toContinuousLinearEquiv.continuous
  have hAc : Convex ℝ (A '' K) := hc.linear_image A.toLinearMap
  have hAi : (interior (A '' K)).Nonempty := by
    change (interior (A.toContinuousLinearEquiv.toHomeomorph '' K)).Nonempty
    rw [←A.toContinuousLinearEquiv.toHomeomorph.image_interior]
    exact hi.image _
  obtain ⟨g,hg⟩ := hl m D hD hn hroot (A '' K) hAK hAc hAi
  let J := g '' (A '' K)
  have hJ : IsCompact J := hAK.image g.toAffineMap.continuous_of_finiteDimensional
  let G : E (m+D) ≃ₜ ((Fin m → ℝ) × E D) :=
    { toEquiv := g.toEquiv
      continuous_toFun := g.toAffineMap.continuous_of_finiteDimensional
      continuous_invFun := g.symm.toAffineMap.continuous_of_finiteDimensional }
  have hJi : (interior J).Nonempty := by
    change (interior (G '' (A '' K))).Nonempty
    rw [←G.image_interior]
    exact hAi.image G
  have hJ0 : 0 < (volume J).toReal := by
    apply ENNReal.toReal_pos (ne_of_gt ?_) hJ.measure_ne_top
    exact (isOpen_interior.measure_pos volume hJi).trans_le (measure_mono interior_subset)
  let e := A.toAffineEquiv.trans (g.trans (flatten m D).toAffineEquiv)
  have he : e '' K=flatten m D '' J := by
    dsimp [e,J]
    rw [Set.image_image,Set.image_image]
    rfl
  refine ⟨e,fun y hy => ?_⟩
  rw [he,flatten_volume m D hJ]
  have hf : coordinateFiber (flatten m D '' J) y=Sections.fiber J (WithLp.toLp 2 y) := by
    have H := flatten_fiber (flatten m D '' J) (WithLp.toLp 2 y)
    have hc : (flatten m D).symm '' ((flatten m D) '' J)=J := by
      simp only [Set.image_image,LinearEquiv.symm_apply_apply,Set.image_id']
    rw [hc] at H
    exact H.symm
  rw [hf]
  have H := hg (WithLp.toLp 2 y) hy
  rw [density_half_gaussian,gaussian_toLp] at H
  change Folded.gamma y/2 ≤ canonical J (WithLp.toLp 2 y) at H
  rw [canonical,ENNReal.toReal_inv] at H
  have HH := mul_le_mul_of_nonneg_left H hJ0.le
  rw [←mul_assoc,mul_inv_cancel₀ hJ0.ne',one_mul] at HH
  simpa only [mul_div_assoc] using HH


end SingleLatticeCovering.GaussianNumerics




end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_Assembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The unconditional eventual covering bound, using the actual prime-congruence
and local affine Gaussian-position producers. Conditional intermediate interfaces
retain their stated hypotheses and are not used as unproved assumptions here. -/

noncomputable section

namespace SingleLatticeCovering.Assembly
open PrimeKernel SimplexYoung MeasureTheory Folded LatticeGeometry Completion Shear CoverGeometry Vertical Sections Horizontal Inputs
open Filter Topology
open scoped BigOperators Pointwise ENNReal




theorem eventual_single_lattice_covering_oai :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ K : Set (Fin n → ℝ),
      IsCompact K → Convex ℝ K → (interior K).Nonempty →
      ∃ (Λ : Submodule ℤ (Fin n → ℝ)) (_ : DiscreteTopology Λ), IsZLattice ℝ Λ ∧
        K+(Λ : Set (Fin n → ℝ))=Set.univ ∧
        (volume K).toReal/ZLattice.covolume Λ volume ≤ C*(n : ℝ)*Real.log (n : ℝ) := by
  classical
  obtain ⟨cutoff,hcut,C,k,κ,hC,hk,hκ,hvertical⟩ := vertical_patterns_alphabets
  let CT : ℝ := 301
  have hCT : 0 ≤ CT := by norm_num [CT]
  have hCTeq : 1+CT=302 := by norm_num [CT]
  obtain ⟨Cstar,hstar,hconditions⟩ := FinalRates.final_conditions hC hk
    (show 0 < Real.exp (-1)/8 by positivity) (show 0 ≤ Real.exp 1/8 by positivity)
    hκ (show (1 : ℝ) ≤ 3 by norm_num) hCT
  refine ⟨Real.exp 1*Cstar,by positivity,?_⟩
  filter_upwards [hconditions,FinalRates.eventually_marginal_scales hC (by norm_num : (0:ℝ) < 1)
      (by norm_num : (0:ℝ) < 1) (by norm_num : (0:ℝ) < 1) (by norm_num : (0:ℝ) ≤ 0),
    FinalRates.firstSize_tendsto.eventually (eventually_ge_atTop cutoff),
    (FinalRates.localScale_tendsto hC).eventually GaussianNumerics.eventually_local_coordinate_position,
    FinalRates.eventually_localScale_root hC,
      FinalRates.eventually_dimension_small hC,eventually_ge_atTop (540 : ℕ)]
      with n hn hscale hfirst hgaussian hroot hdim hn540
  obtain ⟨B,c,hcb,hcs,hDim,hRad,hAlphabet,hPattern⟩ := hvertical (FinalRates.firstSize n) hfirst
  have hDdim : (c.fullDim : ℝ) ≤ C*((FinalRates.firstSize n : ℝ)+1) := by
    simpa [Chain.fullDim,Nat.cast_add] using hDim
  obtain ⟨hDn,hm,hcap,hload,hcrit,hcount⟩ := hn.2 c.fullDim hDdim
  have hm270 : 270 ≤ n-c.fullDim := by
    have hd := (hdim c.fullDim hDdim).2
    have hnR : (540 : ℝ) ≤ n := by exact_mod_cast hn540
    have hh : (270 : ℝ) ≤ ((n-c.fullDim : ℕ) : ℝ) := by
      rw [Nat.cast_sub hDn]
      linarith
    exact_mod_cast hh
  rw [hCTeq] at hcrit
  obtain ⟨_,_,_,_,_,hSmall⟩ := hscale c.fullDim hDdim
  have hD : 0 < c.fullDim := by
    have hfirstdim := chain_first_le_dim c
    rw [hcb] at hfirstdim
    dsimp [Chain.fullDim]
    omega
  let m := n-c.fullDim
  have hmn : m+c.fullDim=n := Nat.sub_add_cancel hDn
  have hmnle : m ≤ n := Nat.sub_le _ _
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  let ρ := Cstar*(n : ℝ)*Real.log (n : ℝ)
  let ε := Real.exp (-k*(FinalRates.firstSize n : ℝ)^(70/100 : ℝ))
  let R := FinalRates.sectionRadius C n
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hrad : c.radiusSq+(B.terminalDim : ℝ) ≤ R^2 :=
    FinalRates.radius_sq_bound hC.le (Nat.cast_nonneg _) hRad
  have step : coversAtBound (m+c.fullDim) ((Real.exp 1*Cstar)*(n : ℝ)*Real.log (n : ℝ)) := by
    intro K hK hc hi
    obtain ⟨e,he⟩ := hgaussian m c.fullDim (FinalRates.dimension_le_localScale hC hDdim)
      (by omega : 0 < m+c.fullDim) (by simpa only [hmn] using hroot) K hK hc hi
    obtain ⟨heK,hec,hei⟩ := affine_body e hK hc hi
    have heV := body_volume_pos heK hei
    have hg : ∀ y : c.FullVec, ‖WithLp.toLp 2 y‖ ≤ 6*(c.fullDim : ℝ)*R →
        (volume (e '' K)).toReal*gamma y/2 ≤ (volume (coordinateFiber (e '' K) y)).toReal := by
      intro y hy
      apply he y
      apply hy.trans
      calc
        6*(c.fullDim:ℝ)*R ≤ 6*(FinalRates.localScale C n:ℝ)*(FinalRates.localScale C n:ℝ) := by
          gcongr
          · exact (FinalRates.sectionRadius_pos hC n).le
          · exact_mod_cast FinalRates.dimension_le_localScale hC hDdim
          · exact FinalRates.sectionRadius_le_localScale C n
        _ = 6*(FinalRates.localScale C n:ℝ)^2 := by ring
    obtain ⟨Λ,hd,hfull,hcover,hbound⟩ := sections_and_circuits_cover c hm270 hD (e '' K) heK hec heV
      (FinalRates.sectionRadius_pos hC n) hrad hSmall hg κ ρ ε (Real.sqrt (m : ℝ))
      (8*(n : ℝ)*Real.log (n : ℝ)) hρ (Real.sqrt_nonneg _) (by positivity)
      (by
        intro y
        obtain ⟨P,hPn,hPb,hPl,hPt,hPw⟩ := hPattern y
        exact ⟨P,hPn,hPb,hPl,hPw⟩)
      (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hload) hcap hcrit (by
        intro δ s hs
        have hs' : (s.card : ℝ) ≤ (3*(n : ℝ)^2)^c.fullDim := hs.trans (by
          gcongr)
        have ha : ∀ j < c.fullDim, Real.log ((c.alphabetSeq j).card+1 : ℝ) ≤
            Real.log 8+(c.fullDim : ℝ)*Real.log ((c.fullDim : ℝ)+2)+(FinalRates.firstSize n : ℝ)^2 := by
          intro j hj
          simpa only [c.alphabetSeq_fin ⟨j,hj⟩] using hAlphabet ⟨j,hj⟩
        simpa only [Nat.sub_add_cancel hDn] using hcount s c.alphabetSeq hs' ha)
    let := hd
    let := hfull
    have hb : (volume (e '' K)).toReal/ZLattice.covolume Λ volume ≤
        (Real.exp 1*Cstar)*(n : ℝ)*Real.log (n : ℝ) := by
      convert hbound using 1 ; dsimp [ρ] ; ring
    exact pull_back_cover e K Λ hcover hb
  change coversAtBound n ((Real.exp 1*Cstar)*(n : ℝ)*Real.log (n : ℝ))
  simpa only [hmn] using step


end SingleLatticeCovering.Assembly


end

end OAI
end

theorem solution : type_of% @OAI.SingleLatticeCovering.Assembly.eventual_single_lattice_covering_oai := @OAI.SingleLatticeCovering.Assembly.eventual_single_lattice_covering_oai
