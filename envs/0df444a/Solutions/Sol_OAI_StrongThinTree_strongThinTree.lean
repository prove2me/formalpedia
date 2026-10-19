-- Prove2me | solution 1 for OAI.StrongThinTree.strongThinTree
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T17:08:13.93512+00:00
-- url     : https://prove2.me/submissions/10d49473-f91d-4179-abc0-d0699c87d364

import Mathlib
import Definitions.Def_StrongThinTree
import Definitions.Def_OAIQWSTT000
import Theorems.Thm_OAI_StrongThinTree_MultiGraph_Hierarchy_binary_numerator_bound
import Theorems.Thm_OAI_StrongThinTree_MultiGraph_sparsify_from_extraction

section
-- module Solutions.OAIQW_StrongThinTree.Compat
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h := dif_neg h
end OAICompat434
end

section
-- module Solutions.OAIQW_StrongThinTree.Records
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Classical
open Matrix

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n h : ℕ} (H : Hierarchy n)

lemma mem_domain {A B : Finset (Fin n)} {P : Finset (Finset (Fin n))} :
    B ∈ H.domain A P ↔ B ∈ H.nodes ∧ B ⊆ A ∧ ∀S ∈ P, ¬B ⊆ S := by
  simp [domain]

lemma root_mem_domain {A : Finset (Fin n)} {P : Finset (Finset (Fin n))}
    (hA : A ∈ H.nodes) (hP : ∀S ∈ P, S ⊂ A) : A ∈ H.domain A P := by
  apply H.mem_domain.mpr
  refine ⟨hA,Subset.refl _,?_⟩
  intro S hS hh
  have hs := hP S hS
  exact (Finset.ssubset_iff_subset_ne.mp hs).2 (Subset.antisymm hs.subset hh)

end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry

namespace Record
variable {n m h : ℕ} (H : Hierarchy n) (G : MultiGraph n m)
  (X : Fin n → Fin h → ℝ)

lemma root_mem {B : Record n} (hB : B.Shape H) : B.owner ∈ B.conflict H :=
  H.root_mem_domain hB.1 (fun S hS => (hB.2 S hS).2)

end Record
end
end StrongThinTree.MultiGraph.Hierarchy

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Truncation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uE2 uE3 uE4

section
open scoped Classical
open Matrix

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry StrongThinTree.Geometry.RadialShell
open scoped Classical
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ}

lemma truncationGain_pos (α : ℝ) : 0 < truncationGain α := by
  dsimp [truncationGain,truncationBins]
  positivity

end
end StrongThinTree.MultiGraph.Hierarchy

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Duality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uI uJ uV uI2 uI3 uV2 uW uJ2 uV3 uE2 uT uJ3 uH uI4

section

namespace StrongThinTree.Duality
noncomputable section
open Finset
open scoped Classical
variable {E : Type uE} {I : Type uI} [AddCommGroup E] [Module ℝ E] [Fintype I]

omit [AddCommGroup E] [Module ℝ E] in
lemma strictUpperImage_isOpen (S : Set E) (F : I → E → ℝ) :
    IsOpen (strictUpperImage S F) := by
  have he : strictUpperImage S F = ⋃x ∈ S, ⋂i, {v : I → ℝ | F i x < v i} := by
    ext v; simp [strictUpperImage]
  rw [he]
  exact isOpen_iUnion (fun x => isOpen_iUnion (fun _ => isOpen_iInter_of_finite
    (fun i => isOpen_lt continuous_const (continuous_apply i))))

omit [Fintype I] in
lemma strictUpperImage_convex (S : Set E) (F : I → E → ℝ)
    (hS : Convex ℝ S) (hF : ∀i, ConvexOn ℝ S (F i)) :
    Convex ℝ (strictUpperImage S F) := by
  intro u hu v hv a b ha hb hab
  obtain ⟨x,hx,hxu⟩ := hu
  obtain ⟨y,hy,hyv⟩ := hv
  refine ⟨a • x+b • y,hS hx hy ha hb hab,?_⟩
  intro i
  have hf := (hF i).2 hx hy ha hb hab
  change F i (a • x+b • y) < a*u i+b*v i
  change F i (a • x+b • y) ≤ a*F i x+b*F i y at hf
  have hlt : a*F i x+b*F i y < a*u i+b*v i := by
    by_cases ha0 : a=0
    · have hb1 : b=1 := by linarith
      simpa [ha0,hb1] using hyv i
    · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left (hxu i) hapos)
        (mul_le_mul_of_nonneg_left (hyv i).le hb)
  exact hf.trans_lt hlt

lemma functional_coordinates (l : (I → ℝ) →L[ℝ] ℝ) (v : I → ℝ) :
    l v = ∑i, l (Pi.single i 1)*v i := by
  have he : v=∑i, v i • Pi.single i (1:ℝ) := by
    funext j
    simp [Pi.single_apply]
  calc
    l v = l (∑i, v i • Pi.single i (1:ℝ)) := congrArg l he
    _ = ∑i, l (Pi.single i 1)*v i := by
      rw [map_sum]
      apply sum_congr rfl
      intro i _
      rw [map_smul]
      simp only [smul_eq_mul,mul_comm]

lemma convex_alternative (S : Set E) (hS : Convex ℝ S) (hne : S.Nonempty)
    (F : I → E → ℝ) (hF : ∀i, ConvexOn ℝ S (F i))
    (hinfeasible : ¬∃x ∈ S, ∀i, F i x < 0) :
    ∃w : I → ℝ, (∀i, 0 ≤ w i) ∧ (∑i, w i)=1 ∧
      ∀x ∈ S, 0 ≤ ∑i, w i*F i x := by
  have hzero : (0:I → ℝ) ∉ strictUpperImage S F := hinfeasible
  obtain ⟨l,hl⟩ := geometric_hahn_banach_point_open (strictUpperImage_convex S F hS hF)
    (strictUpperImage_isOpen S F) hzero
  simp only [map_zero] at hl
  let w : I → ℝ := fun i => l (Pi.single i 1)
  obtain ⟨x₀,hx₀⟩ := hne
  let v₀ : I → ℝ := fun i => F i x₀+1
  have hv₀ : v₀ ∈ strictUpperImage S F := ⟨x₀,hx₀,fun i => by dsimp [v₀]; linarith⟩
  have hlv : 0 < l v₀ := hl v₀ hv₀
  have hw : ∀i, 0 ≤ w i := by
    intro i
    by_contra hh
    have hi : w i < 0 := lt_of_not_ge hh
    let t := (l v₀+1)/(-w i)
    have ht : 0 ≤ t := div_nonneg (by linarith only [hlv]) (neg_pos.mpr hi).le
    have hv : v₀+t • Pi.single i 1 ∈ strictUpperImage S F := by
      refine ⟨x₀,hx₀,?_⟩
      intro j
      change F j x₀ < v₀ j+t*((Pi.single i (1:ℝ) : I → ℝ) j)
      have hj : 0 ≤ ((Pi.single i (1:ℝ) : I → ℝ) j) := by simp [Pi.single_apply]; split_ifs <;> norm_num
      exact (show F j x₀ < v₀ j by dsimp [v₀]; linarith).trans_le (le_add_of_nonneg_right (mul_nonneg ht hj))
    have hh := hl _ hv
    rw [map_add,map_smul] at hh
    change 0 < l v₀+t*w i at hh
    have hid : t*w i=-(l v₀+1) := by dsimp [t]; field_simp [ne_of_lt hi]
    linarith only [hh,hid]
  let W := ∑i, w i
  have hW : 0 < W := by
    have hWnon : 0 ≤ W := sum_nonneg (fun i _ => hw i)
    by_contra hh
    have hW0 : W=0 := le_antisymm (le_of_not_gt hh) hWnon
    have hw0 : ∀i, w i=0 := fun i => (sum_eq_zero_iff_of_nonneg (fun i _ => hw i)).mp hW0 i (mem_univ i)
    rw [functional_coordinates] at hlv
    have hz : ∑i, l (Pi.single i 1)*v₀ i=0 := by
      change (∑i, w i*v₀ i)=0
      simp [hw0]
    linarith only [hlv,hz]
  have hbound : ∀x ∈ S, 0 ≤ ∑i, w i*F i x := by
    intro x hx
    apply le_of_forall_pos_lt_add
    intro ε hε
    have heps : 0 < ε/W := div_pos hε hW
    have hv : (fun i => F i x+ε/W) ∈ strictUpperImage S F :=
      ⟨x,hx,fun i => lt_add_of_pos_right _ heps⟩
    have hh := hl _ hv
    rw [functional_coordinates] at hh
    change 0 < ∑i, w i*(F i x+ε/W) at hh
    simp only [mul_add,sum_add_distrib,←sum_mul] at hh
    have heq : W*(ε/W)=ε := by field_simp
    change 0 < (∑i, w i*F i x)+W*(ε/W) at hh
    rwa [heq] at hh
  refine ⟨fun i => w i/W,fun i => div_nonneg (hw i) hW.le,?_,?_⟩
  · rw [←sum_div]
    exact div_self hW.ne'
  · intro x hx
    simp only [div_mul_eq_mul_div,←sum_div]
    exact div_nonneg (hbound x hx) hW.le
variable {J : Type uJ} [Fintype J]

lemma slater_certificate (S : Set E) (hS : Convex ℝ S)
    (f : I → E → ℝ) (g : J → E → ℝ)
    (hf : ∀i, ConvexOn ℝ S (f i)) (hg : ∀j, ConvexOn ℝ S (g j))
    (hslater : ∃x ∈ S, ∀j, g j x < 0) (K : ℝ)
    (hinfeasible : ¬∃x ∈ S, (∀i, f i x < K) ∧ (∀j, g j x < 0)) :
    ∃lam : I → ℝ, ∃y : J → ℝ, (∀i, 0 ≤ lam i) ∧ (∑i, lam i)=1 ∧
      (∀j, 0 ≤ y j) ∧ ∀x ∈ S, K ≤ (∑i, lam i*f i x)+(∑j, y j*g j x) := by
  let F : I ⊕ J → E → ℝ := Sum.elim (fun i x => f i x-K) g
  have hF : ∀i, ConvexOn ℝ S (F i) := by
    intro i
    cases i with
    | inl i =>
      refine ⟨hS,?_⟩
      intro x hx y hy a b ha hb hab
      have hh := (hf i).2 hx hy ha hb hab
      change f i (a • x+b • y)-K ≤ a*(f i x-K)+b*(f i y-K)
      change f i (a • x+b • y) ≤ a*f i x+b*f i y at hh
      linarith only [hh,congrArg (fun z : ℝ => z*K) hab]
    | inr j => exact hg j
  have hnone : ¬∃x ∈ S, ∀i, F i x < 0 := by
    intro ⟨x,hx,h⟩
    apply hinfeasible
    exact ⟨x,hx,fun i => sub_neg.mp (h (Sum.inl i)),fun j => h (Sum.inr j)⟩
  obtain ⟨x₀,hx₀,hg₀⟩ := hslater
  obtain ⟨w,hw,hws,hwb⟩ := convex_alternative S hS ⟨x₀,hx₀⟩ F hF hnone
  let p := ∑i, w (Sum.inl i)
  have hpnon : 0 ≤ p := sum_nonneg (fun i _ => hw (Sum.inl i))
  have hsum : p+(∑j, w (Sum.inr j))=1 := by simpa only [p,Fintype.sum_sum_type] using hws
  have hp : 0 < p := by
    by_contra hh
    have hp0 : p=0 := le_antisymm (le_of_not_gt hh) hpnon
    have hwi0 : ∀i, w (Sum.inl i)=0 := fun i =>
      (sum_eq_zero_iff_of_nonneg (fun i _ => hw (Sum.inl i))).mp hp0 i (mem_univ i)
    have hjpos : 0 < ∑j, w (Sum.inr j) := by linarith only [hsum,hp0]
    obtain ⟨j,hj,hjpos⟩ := (sum_pos_iff_of_nonneg (fun j _ => hw (Sum.inr j))).mp hjpos
    have hgneg : (∑j, w (Sum.inr j)*g j x₀) < 0 := by
      apply sum_neg' (fun j _ => mul_nonpos_of_nonneg_of_nonpos (hw (Sum.inr j)) (hg₀ j).le)
      exact ⟨j,mem_univ j,mul_neg_of_pos_of_neg hjpos (hg₀ j)⟩
    have hh := hwb x₀ hx₀
    simp only [Fintype.sum_sum_type,F,Sum.elim_inl,Sum.elim_inr,hwi0,zero_mul,sum_const_zero,zero_add] at hh
    linarith only [hh,hgneg]
  refine ⟨fun i => w (Sum.inl i)/p,fun j => w (Sum.inr j)/p,
    fun i => div_nonneg (hw (Sum.inl i)) hp.le,?_,
    fun j => div_nonneg (hw (Sum.inr j)) hp.le,?_⟩
  · rw [←sum_div]
    exact div_self hp.ne'
  · intro x hx
    have hh := hwb x hx
    simp only [Fintype.sum_sum_type,F,Sum.elim_inl,Sum.elim_inr,mul_sub,sum_sub_distrib,←sum_mul] at hh
    simp only [div_mul_eq_mul_div,←sum_div,←add_div]
    apply (le_div_iff₀ hp).mpr
    change 0 ≤ (∑i, w (Sum.inl i)*f i x)-p*K+(∑j, w (Sum.inr j)*g j x) at hh
    linarith only [hh]

lemma strict_feasible_of_dual_bound (S : Set E) (hS : Convex ℝ S)
    (f : I → E → ℝ) (g : J → E → ℝ)
    (hf : ∀i, ConvexOn ℝ S (f i)) (hg : ∀j, ConvexOn ℝ S (g j))
    (hslater : ∃x ∈ S, ∀j, g j x < 0) (K : ℝ)
    (hdual : ∀lam : I → ℝ, ∀y : J → ℝ, (∀i, 0 ≤ lam i) → (∑i, lam i)=1 →
      (∀j, 0 ≤ y j) → ∃x ∈ S, (∑i, lam i*f i x)+(∑j, y j*g j x) < K) :
    ∃x ∈ S, (∀i, f i x < K) ∧ (∀j, g j x < 0) := by
  by_contra hh
  obtain ⟨lam,y,hlam,hlams,hy,hbound⟩ := slater_certificate S hS f g hf hg hslater K hh
  obtain ⟨x,hx,hval⟩ := hdual lam y hlam hlams hy
  exact (not_lt_of_ge (hbound x hx)) hval
end
end StrongThinTree.Duality

namespace StrongThinTree.MatrixDual
noncomputable section
open Matrix Finset
open scoped Classical MatrixOrder
variable {V : Type uV} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma quadratic_symm {D : Matrix V V ℝ} (hD : D.IsHermitian) (x y : V → ℝ) :
    x ⬝ᵥ (D *ᵥ y) = y ⬝ᵥ (D *ᵥ x) := by
  have hsym : D.transpose=D := isHermitian_iff_isSymm.mp hD
  rw [dotProduct_mulVec,dotProduct_comm,←vecMul_transpose,hsym]

lemma solve {D : Matrix V V ℝ} (hD : D.PosDef) (b : V → ℝ) :
    D *ᵥ (D⁻¹ *ᵥ b)=b := by
  rw [mulVec_mulVec,mul_nonsing_inv D ((isUnit_iff_isUnit_det D).mp hD.isUnit),one_mulVec]

lemma inverse_quadratic_variational {D : Matrix V V ℝ} (hD : D.PosDef) (b x : V → ℝ) :
    2*(b ⬝ᵥ x)-x ⬝ᵥ (D *ᵥ x) ≤ b ⬝ᵥ (D⁻¹ *ᵥ b) := by
  let y := D⁻¹ *ᵥ b
  have hDy : D *ᵥ y=b := solve hD b
  have hs : y ⬝ᵥ (D *ᵥ x)=x ⬝ᵥ b := by rw [quadratic_symm hD.isHermitian,hDy]
  have hh := hD.posSemidef.dotProduct_mulVec_nonneg (x-y)
  simp only [star_trivial,mulVec_sub,sub_dotProduct,dotProduct_sub,hDy,hs,
    dotProduct_comm x b,dotProduct_comm y b] at hh
  change 2*(b ⬝ᵥ x)-x ⬝ᵥ (D *ᵥ x) ≤ b ⬝ᵥ y
  linarith only [hh]

lemma inverse_quadratic_attained {D : Matrix V V ℝ} (hD : D.PosDef) (b : V → ℝ) :
    b ⬝ᵥ (D⁻¹ *ᵥ b)=2*(b ⬝ᵥ (D⁻¹ *ᵥ b))-(D⁻¹ *ᵥ b) ⬝ᵥ (D *ᵥ (D⁻¹ *ᵥ b)) := by
  rw [solve hD b,dotProduct_comm (D⁻¹ *ᵥ b) b]
  ring

omit [Fintype V] [DecidableEq V] in
lemma posDef_convex : Convex ℝ {D : Matrix V V ℝ | D.PosDef} := by
  intro X hX Y hY a b ha hb hab
  by_cases ha0 : a=0
  · have hb1 : b=1 := by linarith only [hab,ha0]
    simpa [ha0,hb1] using hY
  · exact (hX.smul (lt_of_le_of_ne ha (Ne.symm ha0))).add_posSemidef (hY.posSemidef.smul hb)

lemma inverse_quadratic_convex (v : V → ℝ) :
    ConvexOn ℝ {D : Matrix V V ℝ | D.PosDef} (fun D => v ⬝ᵥ (D⁻¹ *ᵥ v)) := by
  refine ⟨posDef_convex,?_⟩
  intro X hX Y hY a b ha hb hab
  let D := a • X+b • Y
  have hD : D.PosDef := posDef_convex hX hY ha hb hab
  let z := D⁻¹ *ᵥ v
  have hXv := inverse_quadratic_variational hX v z
  have hYv := inverse_quadratic_variational hY v z
  have hDv := inverse_quadratic_attained hD v
  have hf : 2*(v ⬝ᵥ z)-z ⬝ᵥ (D *ᵥ z) =
      a*(2*(v ⬝ᵥ z)-z ⬝ᵥ (X *ᵥ z))+b*(2*(v ⬝ᵥ z)-z ⬝ᵥ (Y *ᵥ z)) := by
    dsimp [D]
    simp only [add_mulVec,smul_mulVec,dotProduct_add,dotProduct_smul,smul_eq_mul]
    linarith only [congrArg (fun t : ℝ => t*(v ⬝ᵥ z)) hab]
  change v ⬝ᵥ (D⁻¹ *ᵥ v) ≤ a*(v ⬝ᵥ (X⁻¹ *ᵥ v))+b*(v ⬝ᵥ (Y⁻¹ *ᵥ v))
  rw [hDv]
  change 2*(v ⬝ᵥ z)-z ⬝ᵥ (D *ᵥ z) ≤ _
  rw [hf]
  exact add_le_add (mul_le_mul_of_nonneg_left hXv ha) (mul_le_mul_of_nonneg_left hYv hb)

omit [DecidableEq V] in
lemma cut_quadratic_convex (v : V → ℝ) (c : ℝ) :
    ConvexOn ℝ {D : Matrix V V ℝ | D.PosDef} (fun D => v ⬝ᵥ (D *ᵥ v)-c) := by
  refine ⟨posDef_convex,?_⟩
  intro X hX Y hY a b ha hb hab
  simp only [add_mulVec,smul_mulVec,dotProduct_add,dotProduct_smul,smul_eq_mul]
  linarith only [congrArg (fun t : ℝ => t*c) hab]

lemma posDef_sqrt {A : Matrix V V ℝ} (hA : A.PosDef) : (CFC.sqrt A).PosDef := by
  apply (CFC.sqrt_nonneg A).posSemidef.posDef_iff_isUnit.mpr
  apply (isUnit_pow_iff (by decide : 2 ≠ 0)).mp
  rw [CFC.sq_sqrt A hA.posSemidef.nonneg]
  exact hA.isUnit

lemma congr_posDef {A S : Matrix V V ℝ} (hA : A.PosDef)
    (hSH : S.IsHermitian) (hSU : IsUnit S) : (S*A*S).PosDef := by
  simpa only [hSH.eq] using hA.conjTranspose_mul_mul_same
    (mulVec_injective_iff_isUnit.mpr hSU)

lemma trace_objective_attained {A Z : Matrix V V ℝ} (hA : A.PosDef) (hZ : Z.PosDef) :
    ∃ D : Matrix V V ℝ, D.PosDef ∧
      (A*D⁻¹).trace+(Z*D).trace =
        2*(CFC.sqrt (CFC.sqrt Z*A*CFC.sqrt Z)).trace := by
  let S := CFC.sqrt Z
  have hS : S.PosDef := posDef_sqrt hZ
  have hSS : S*S=Z := CFC.sqrt_mul_sqrt_self Z hZ.posSemidef.nonneg
  have hSi : S*S⁻¹=1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hS.isUnit)
  have hiS : S⁻¹*S=1 := nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hS.isUnit)
  let C := S*A*S
  have hC : C.PosDef := congr_posDef hA hS.isHermitian hS.isUnit
  let T := CFC.sqrt C
  have hT : T.PosDef := posDef_sqrt hC
  have hTT : T*T=C := CFC.sqrt_mul_sqrt_self C hC.posSemidef.nonneg
  have hTi : T*T⁻¹=1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hT.isUnit)
  let D := S⁻¹*T*S⁻¹
  have hD : D.PosDef := congr_posDef hT hS.inv.isHermitian hS.inv.isUnit
  have hDinv : D⁻¹=S*T⁻¹*S := by
    apply inv_eq_right_inv
    dsimp [D]
    simp only [mul_assoc,←mul_assoc S⁻¹ S,hiS,←mul_assoc T T⁻¹,hTi,one_mul]
  have hAeq : A=S⁻¹*(T*T)*S⁻¹ := by
    rw [hTT]
    dsimp [C]
    simp only [mul_assoc,hSi,mul_one,←mul_assoc S⁻¹ S,hiS,one_mul]
  have htA : (A*D⁻¹).trace=T.trace := by
    rw [hDinv,hAeq]
    have heq : S⁻¹*(T*T)*S⁻¹*(S*T⁻¹*S)=S⁻¹*T*S := by
      simp only [mul_assoc,←mul_assoc S⁻¹ S,hiS,one_mul]
      simp only [←mul_assoc T T⁻¹,hTi,one_mul]
    rw [heq,Matrix.trace_mul_cycle,hSi,one_mul]
  have htZ : (Z*D).trace=T.trace := by
    rw [←hSS]
    dsimp [D]
    have heq : S*S*(S⁻¹*T*S⁻¹)=S*T*S⁻¹ := by
      simp only [mul_assoc,←mul_assoc S S⁻¹,hSi,one_mul]
    rw [heq,Matrix.trace_mul_cycle,hiS,one_mul]
  refine ⟨D,hD,?_⟩
  change (A*D⁻¹).trace+(Z*D).trace=2*T.trace
  rw [htA,htZ]
  ring

open Filter Topology
open scoped Matrix.Norms.L2Operator

lemma sqrt_tendsto {I : Type uI2} {l : Filter I} {A : Matrix V V ℝ}
    (hA : A.PosSemidef) {f : I → Matrix V V ℝ}
    (hf : Tendsto f l (𝓝 A)) (hfp : ∀ᶠ i in l, (f i).PosSemidef) :
    Tendsto (fun i => CFC.sqrt (f i)) l (𝓝 (CFC.sqrt A)) := by
  apply (CFC.continuousOn_sqrt A hA.nonneg).tendsto.comp
  exact tendsto_nhdsWithin_iff.mpr ⟨hf,hfp.mono (fun i hi => hi.nonneg)⟩

lemma traceRoot_tendsto {I : Type uI3} {l : Filter I} {A Z : Matrix V V ℝ}
    (hA : A.PosSemidef) (hZ : Z.PosSemidef) {f g : I → Matrix V V ℝ}
    (hf : Tendsto f l (𝓝 A)) (hg : Tendsto g l (𝓝 Z))
    (hfp : ∀ᶠ i in l, (f i).PosSemidef) (hgp : ∀ᶠ i in l, (g i).PosSemidef) :
    Tendsto (fun i => 2*(CFC.sqrt (CFC.sqrt (g i)*f i*CFC.sqrt (g i))).trace) l
      (𝓝 (2*(CFC.sqrt (CFC.sqrt Z*A*CFC.sqrt Z)).trace)) := by
  have hs := sqrt_tendsto hZ hg hgp
  have hp : (CFC.sqrt Z*A*CFC.sqrt Z).PosSemidef := by
    simpa only [(CFC.sqrt_nonneg Z).posSemidef.isHermitian.eq] using
      hA.conjTranspose_mul_mul_same (CFC.sqrt Z)
  have hps : ∀ᶠ i in l, (CFC.sqrt (g i)*f i*CFC.sqrt (g i)).PosSemidef := by
    filter_upwards [hfp] with i hi
    simpa only [(CFC.sqrt_nonneg (g i)).posSemidef.isHermitian.eq] using
      hi.conjTranspose_mul_mul_same (CFC.sqrt (g i))
  have ht := sqrt_tendsto hp ((hs.mul hf).mul hs) hps
  have htr := (continuous_id.matrix_trace.tendsto _).comp ht
  exact htr.const_mul 2

lemma trace_objective_approx {A Z : Matrix V V ℝ} (hA : A.PosSemidef) (hZ : Z.PosSemidef)
    {K : ℝ} (hK : 2*(CFC.sqrt (CFC.sqrt Z*A*CFC.sqrt Z)).trace < K) :
    ∃ D : Matrix V V ℝ, D.PosDef ∧ (A*D⁻¹).trace+(Z*D).trace < K := by
  let f : ℝ → Matrix V V ℝ := fun t => A+t•1
  let g : ℝ → Matrix V V ℝ := fun t => Z+t•1
  have hf : Tendsto f (𝓝[>] 0) (𝓝 A) := by
    have hc : Continuous f := by dsimp [f]; fun_prop
    simpa [f] using (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  have hg : Tendsto g (𝓝[>] 0) (𝓝 Z) := by
    have hc : Continuous g := by dsimp [g]; fun_prop
    simpa [g] using (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0<t := self_mem_nhdsWithin
  have hfp : ∀t, 0<t → (f t).PosDef := by
    intro t ht
    simpa [f,add_comm] using (Matrix.PosDef.one.smul ht).add_posSemidef hA
  have hgp : ∀t, 0<t → (g t).PosDef := by
    intro t ht
    simpa [g,add_comm] using (Matrix.PosDef.one.smul ht).add_posSemidef hZ
  have hv := traceRoot_tendsto hA hZ hf hg
    (hpos.mono (fun t ht => (hfp t ht).posSemidef))
    (hpos.mono (fun t ht => (hgp t ht).posSemidef))
  obtain ⟨t,ht,htK⟩ := (hpos.and (hv.eventually_lt_const hK)).exists
  obtain ⟨D,hD,heq⟩ := trace_objective_attained (hfp t ht) (hgp t ht)
  have hterms : (A*D⁻¹).trace+(Z*D).trace ≤ ((f t)*D⁻¹).trace+((g t)*D).trace := by
    dsimp [f,g]
    simp only [add_mul,smul_mul_assoc,one_mul,trace_add,trace_smul,smul_eq_mul]
    linarith only [mul_nonneg ht.le hD.inv.posSemidef.trace_nonneg,
      mul_nonneg ht.le hD.posSemidef.trace_nonneg]
  exact ⟨D,hD,hterms.trans_lt (heq.trans_lt htK)⟩
end
end StrongThinTree.MatrixDual

namespace StrongThinTree.Polar
noncomputable section
open Matrix Finset
open scoped Classical MatrixOrder Matrix.Norms.L2Operator
variable {V : Type uV2} {W : Type uW} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

lemma sqrt_eq_real_cfc {A : Matrix V V ℝ} (hA : A.PosSemidef) :
    CFC.sqrt A=cfc Real.sqrt A := by
  rw [CFC.sqrt_eq_cfc,cfc_nnreal_eq_real _ _ hA.nonneg]
  unfold Real.sqrt
  rfl

lemma trace_sqrt_roots {A : Matrix V V ℝ} (hA : A.PosSemidef) :
    (CFC.sqrt A).trace=(A.charpoly.roots.map Real.sqrt).sum := by
  rw [sqrt_eq_real_cfc hA,hA.isHermitian.cfc_eq]
  unfold Matrix.IsHermitian.cfc
  rw [Unitary.conjStarAlgAut_apply,Matrix.trace_mul_cycle]
  simp only [Unitary.coe_star_mul_self,one_mul,trace_diagonal]
  rw [hA.isHermitian.roots_charpoly_eq_eigenvalues,Multiset.map_map]
  rfl

lemma trace_sqrt_mul_comm (A : Matrix V W ℝ) (B : Matrix W V ℝ)
    (hAB : (A*B).PosSemidef) (hBA : (B*A).PosSemidef) :
    (CFC.sqrt (A*B)).trace=(CFC.sqrt (B*A)).trace := by
  rw [trace_sqrt_roots hAB,trace_sqrt_roots hBA]
  have heq := congrArg (fun p : Polynomial ℝ => (p.roots.map Real.sqrt).sum)
    (Matrix.charpoly_mul_comm' A B)
  rw [Polynomial.roots_mul (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (A*B).charpoly_monic.ne_zero),
    Polynomial.roots_mul (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (B*A).charpoly_monic.ne_zero)] at heq
  have hz (n : ℕ) : ((n • ({0} : Multiset ℝ)).map Real.sqrt).sum=0 := by
    induction n with
    | zero => simp
    | succ n hn => simp [succ_nsmul,Multiset.map_add,hn]
  simpa [Polynomial.roots_X_pow,Multiset.map_add,hz] using heq

lemma trace_sqrt_gram (M : Matrix V W ℝ) :
    (CFC.sqrt (M*Mᵀ)).trace=(CFC.sqrt (Mᵀ*M)).trace := by
  exact trace_sqrt_mul_comm M Mᵀ
    (by simpa using posSemidef_self_mul_conjTranspose M)
    (by simpa using posSemidef_conjTranspose_mul_self M)

lemma cfc_continuousOn {A : Matrix V V ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    ContinuousOn f (spectrum ℝ A) := by
  rw [hA.spectrum_real_eq_range_eigenvalues]
  exact (Set.finite_range _).continuousOn f

lemma inverse_sqrt_scalar {x : ℝ} (hx : 0 ≤ x) : (Real.sqrt x)⁻¹*x=Real.sqrt x := by
  by_cases hx0 : x=0
  · simp [hx0]
  · have hs : Real.sqrt x ≠ 0 := Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne hx (Ne.symm hx0))
    calc
      (Real.sqrt x)⁻¹*x=(Real.sqrt x)⁻¹*(Real.sqrt x*Real.sqrt x) :=
        congrArg (fun t : ℝ => (Real.sqrt x)⁻¹*t) (Real.mul_self_sqrt hx).symm
      _=Real.sqrt x := by rw [←mul_assoc,inv_mul_cancel₀ hs,one_mul]

lemma inverse_sqrt_scalar_bound {x : ℝ} (hx : 0 ≤ x) :
    (Real.sqrt x)⁻¹*x*(Real.sqrt x)⁻¹ ≤ 1 := by
  rw [inverse_sqrt_scalar hx]
  by_cases hs : Real.sqrt x=0
  · simp [hs]
  · simp [hs]

omit [DecidableEq W] in

lemma polar_optimizer (M : Matrix V W ℝ) :
    ∃ U : Matrix W V ℝ, Uᵀ*U ≤ 1 ∧
      (U*M).trace=(CFC.sqrt (M*Mᵀ)).trace := by
  let H := M*Mᵀ
  have hH : H.PosSemidef := by simpa [H] using posSemidef_self_mul_conjTranspose M
  let f : ℝ → ℝ := fun x => (Real.sqrt x)⁻¹
  let P := cfc f H
  have hid : cfc (fun x : ℝ => x) H=H := cfc_id ℝ H hH.isHermitian
  have hP : P.IsHermitian := cfc_predicate f H
  have hPtrans : Pᵀ=P := isHermitian_iff_isSymm.mp hP
  have hPH : P*H=CFC.sqrt H := by
    rw [sqrt_eq_real_cfc hH]
    calc
      P*H=cfc (fun x => f x*x) H := by
        rw [cfc_mul f (fun x => x) H (cfc_continuousOn hH.isHermitian f)
          (cfc_continuousOn hH.isHermitian (fun x => x)),hid]
      _=cfc Real.sqrt H := cfc_congr (fun x hx => inverse_sqrt_scalar (spectrum_nonneg_of_nonneg hH.nonneg hx))
  have hPHP : P*H*P ≤ 1 := by
    have heq : P*H*P=cfc (fun x => f x*x*f x) H := by
      rw [cfc_mul (fun x => f x*x) f H (cfc_continuousOn hH.isHermitian _)
        (cfc_continuousOn hH.isHermitian _),cfc_mul f (fun x => x) H
        (cfc_continuousOn hH.isHermitian _) (cfc_continuousOn hH.isHermitian _),
        hid]
    rw [heq]
    exact cfc_le_one _ _ (fun x hx => inverse_sqrt_scalar_bound (spectrum_nonneg_of_nonneg hH.nonneg hx))
  refine ⟨Mᵀ*P,?_,?_⟩
  · simpa only [transpose_mul,transpose_transpose,hPtrans,Matrix.mul_assoc,H] using hPHP
  · rw [Matrix.trace_mul_cycle]
    change (M*Mᵀ*P).trace=(CFC.sqrt H).trace
    change (H*P).trace=(CFC.sqrt H).trace
    rw [Matrix.trace_mul_comm,hPH]

variable {J : Type uJ2} [Fintype J] [DecidableEq J]

lemma dual_trace_rectangular (C : Matrix V W ℝ) (Y : Matrix J V ℝ) :
    (CFC.sqrt (CFC.sqrt (Yᵀ*Y)*(C*Cᵀ)*CFC.sqrt (Yᵀ*Y))).trace =
      (CFC.sqrt ((Y*C)*(Y*C)ᵀ)).trace := by
  let S := CFC.sqrt (Yᵀ*Y)
  have hZ : (Yᵀ*Y).PosSemidef := by simpa using posSemidef_conjTranspose_mul_self Y
  have hSH : Sᵀ=S := isHermitian_iff_isSymm.mp (CFC.sqrt_nonneg (Yᵀ*Y)).posSemidef.isHermitian
  have hSS : S*S=Yᵀ*Y := CFC.sqrt_mul_sqrt_self _ hZ.nonneg
  have hleft : S*(C*Cᵀ)*S=(S*C)*(S*C)ᵀ := by
    simp only [transpose_mul,hSH,Matrix.mul_assoc]
  change (CFC.sqrt (S*(C*Cᵀ)*S)).trace=_
  rw [hleft,trace_sqrt_gram,trace_sqrt_gram (Y*C)]
  congr 2
  simp only [transpose_mul,hSH]
  calc
    (Cᵀ*S)*(S*C)=Cᵀ*(S*S)*C := by simp only [Matrix.mul_assoc]
    _=(Cᵀ*Yᵀ)*(Y*C) := by rw [hSS]; simp only [Matrix.mul_assoc]

lemma signed_diag_orthogonal (a : W → ℝ) :
    let D : Matrix W W ℝ := diagonal (fun e => if 0 ≤ a e then (1:ℝ) else -1)
    Dᵀ*D=1 := by
  dsimp
  rw [diagonal_transpose,diagonal_mul_diagonal]
  ext i j
  by_cases hij : i=j
  · subst j
    simp only [diagonal_apply_eq,one_apply_eq]
    split_ifs <;> norm_num
  · simp [diagonal_apply_ne _ hij,one_apply_ne hij]

lemma positive_optimizer (M : Matrix V W ℝ) (w : W → ℝ) (hw : ∀e, 0 ≤ w e) :
    ∃ U : Matrix W V ℝ, Uᵀ*U ≤ 1 ∧ (∀e, 0 ≤ (U*M) e e) ∧
      (CFC.sqrt ((M*diagonal w)*(M*diagonal w)ᵀ)).trace ≤
        ∑e, w e*(U*M) e e := by
  obtain ⟨U,hU,htr⟩ := polar_optimizer (M*diagonal w)
  let a : W → ℝ := fun e => (U*M) e e
  let s : W → ℝ := fun e => if 0 ≤ a e then 1 else -1
  let D : Matrix W W ℝ := diagonal s
  have hDD : Dᵀ*D=1 := signed_diag_orthogonal a
  have hsa (e : W) : s e*a e=|a e| := by
    dsimp [s]
    split_ifs with he
    · simp [abs_of_nonneg he]
    · simp [abs_of_neg (lt_of_not_ge he)]
  have hdiag (e : W) : ((D*U)*M) e e=|a e| := by
    rw [Matrix.mul_assoc]
    change (diagonal s*(U*M)) e e=|a e|
    rw [diagonal_mul]
    exact hsa e
  refine ⟨D*U,?_,fun e => (hdiag e).symm ▸ abs_nonneg _,?_⟩
  · have heq : (D*U)ᵀ*(D*U)=Uᵀ*U := by
      rw [transpose_mul]
      calc
        (Uᵀ*Dᵀ)*(D*U)=Uᵀ*(Dᵀ*D)*U := by simp only [Matrix.mul_assoc]
        _=Uᵀ*U := by rw [hDD,Matrix.mul_one]
    rw [heq]
    exact hU
  · rw [←htr,←Matrix.mul_assoc]
    unfold Matrix.trace
    apply sum_le_sum
    intro e _
    change (U*M*diagonal w) e e ≤ w e*((D*U)*M) e e
    rw [mul_diagonal,hdiag]
    change a e*w e ≤ w e*|a e|
    rw [mul_comm (a e)]
    exact mul_le_mul_of_nonneg_left (le_abs_self _) (hw e)
end
end StrongThinTree.Polar

namespace StrongThinTree.ShortcutDual
noncomputable section
open Matrix Finset Filter Topology
open scoped Classical MatrixOrder Matrix.Norms.L2Operator
variable {V : Type uV3} {E : Type uE2} {T : Type uT} {J : Type uJ3} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype T] [Fintype J]

omit [DecidableEq V] in
lemma outer_posSemidef (v : V → ℝ) : (vecMulVec v v).PosSemidef := by
  simpa using posSemidef_vecMulVec_self_star v

omit [Fintype E] [DecidableEq E] [Fintype T] in
omit [DecidableEq V] in
lemma boundaryMatrix_posSemidef (b : E → V → ℝ) (O : T → Finset E) (t : T) :
    (boundaryMatrix b O t).PosSemidef := by
  apply Matrix.PosSemidef.smul _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  exact Matrix.posSemidef_sum _ (fun e _ => outer_posSemidef (b e))

omit [Fintype E] [DecidableEq E] in
omit [DecidableEq V] in
lemma objectiveMatrix_posSemidef (b : E → V → ℝ) (O : T → Finset E)
    {lam : T → ℝ} (hlam : ∀t, 0 ≤ lam t) : (objectiveMatrix b O lam).PosSemidef := by
  exact Matrix.posSemidef_sum _ (fun t _ => (boundaryMatrix_posSemidef b O t).smul (hlam t))

omit [DecidableEq V] in
lemma cutMatrix_posSemidef (c : J → V → ℝ) {y : J → ℝ} (hy : ∀j, 0 ≤ y j) :
    (cutMatrix c y).PosSemidef := by
  exact Matrix.posSemidef_sum _ (fun j _ => (outer_posSemidef (c j)).smul (hy j))

omit [DecidableEq V] in
lemma trace_outer_mul (v : V → ℝ) (D : Matrix V V ℝ) :
    (vecMulVec v v * D).trace = v ⬝ᵥ (D *ᵥ v) := by
  rw [vecMulVec_mul,trace_vecMulVec,dotProduct_comm,dotProduct_mulVec]

omit [Fintype E] [DecidableEq E] [Fintype T] in
lemma boundaryAverage_convex (b : E → V → ℝ) (O : T → Finset E) (t : T) :
    ConvexOn ℝ {D : Matrix V V ℝ | D.PosDef} (boundaryAverage b O t) := by
  refine ⟨MatrixDual.posDef_convex,?_⟩
  intro X hX Y hY a a' ha ha' haa'
  have hs := sum_le_sum (fun e (_ : e ∈ O t) =>
    (MatrixDual.inverse_quadratic_convex (b e)).2 hX hY ha ha' haa')
  dsimp [boundaryAverage]
  simp only [smul_eq_mul] at hs ⊢
  have h := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (Nat.cast_nonneg (O t).card) :
    0 ≤ ((O t).card : ℝ)⁻¹)
  simpa only [sum_add_distrib,←mul_sum,mul_add,mul_left_comm] using h

omit [Fintype E] [DecidableEq E] in
lemma trace_objectiveMatrix (b : E → V → ℝ) (O : T → Finset E)
    (lam : T → ℝ) (D : Matrix V V ℝ) :
    (objectiveMatrix b O lam * D⁻¹).trace = ∑t, lam t * boundaryAverage b O t D := by
  simp only [objectiveMatrix,Finset.sum_mul,smul_mul_assoc,trace_sum,trace_smul,
    boundaryMatrix,boundaryAverage,smul_eq_mul,trace_outer_mul]

lemma trace_cutMatrix (c : J → V → ℝ) (y d : J → ℝ) (D : Matrix V V ℝ) :
    (cutMatrix c y * D).trace - ∑j, y j*d j = ∑j, y j*(c j ⬝ᵥ (D *ᵥ c j)-d j) := by
  simp only [cutMatrix,Finset.sum_mul,smul_mul_assoc,trace_sum,trace_smul,
    smul_eq_mul,trace_outer_mul,mul_sub,sum_sub_distrib]

lemma cut_slater (c : J → V → ℝ) {d : J → ℝ} (hd : ∀j, 0 < d j) :
    ∃D : Matrix V V ℝ, D.PosDef ∧ ∀j, c j ⬝ᵥ (D *ᵥ c j)-d j < 0 := by
  have hlim (j : J) : Tendsto (fun t : ℝ => t*(c j ⬝ᵥ c j)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => t*(c j ⬝ᵥ c j)) := by fun_prop
    simpa only [zero_mul] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t : ℝ in 𝓝[>] 0, ∀j, t*(c j ⬝ᵥ c j) < d j :=
    eventually_all.mpr (fun j => (hlim j).eventually_lt_const (hd j))
  have hup : ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ), t ∈ Set.Ioi 0 := eventually_mem_nhdsWithin
  obtain ⟨t,htd,ht⟩ := (hev.and hup).exists
  refine ⟨t • (1 : Matrix V V ℝ), Matrix.PosDef.one.smul ht, ?_⟩
  intro j
  simpa only [smul_mulVec,one_mulVec,dotProduct_smul,smul_eq_mul,sub_lt_zero] using htd j

omit [Fintype E] [DecidableEq E] in

lemma shortcut_of_trace_bound (b : E → V → ℝ) (O : T → Finset E)
    (c : J → V → ℝ) (d : J → ℝ) (hd : ∀j, 0 < d j) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀lam : T → ℝ, ∀y : J → ℝ, (∀t, 0 ≤ lam t) → (∑t, lam t)=1 →
      (∀j, 0 ≤ y j) →
      (CFC.sqrt (CFC.sqrt (cutMatrix c y) * objectiveMatrix b O lam *
        CFC.sqrt (cutMatrix c y))).trace^2 ≤ K * ∑j, y j*d j)
    {eta : ℝ} (heta : 0 < eta) :
    ∃D : Matrix V V ℝ, D.PosDef ∧
      (∀t, boundaryAverage b O t D < K+eta) ∧ (∀j, c j ⬝ᵥ (D *ᵥ c j) < d j) := by
  have hs := Duality.strict_feasible_of_dual_bound {D : Matrix V V ℝ | D.PosDef}
    MatrixDual.posDef_convex (boundaryAverage b O) (fun j D => c j ⬝ᵥ (D *ᵥ c j)-d j)
    (boundaryAverage_convex b O) (fun j => MatrixDual.cut_quadratic_convex (c j) (d j))
    (cut_slater c hd) (K+eta)
  obtain ⟨D,hD,hf,hg⟩ := hs (by
    intro lam y hlam hlams hy
    let A := objectiveMatrix b O lam
    let Z := cutMatrix c y
    let N := (CFC.sqrt (CFC.sqrt Z*A*CFC.sqrt Z)).trace
    let v := ∑j, y j*d j
    have hv : 0 ≤ v := sum_nonneg (fun j _ => mul_nonneg (hy j) (hd j).le)
    have hN : 0 ≤ N := (CFC.sqrt_nonneg _).posSemidef.trace_nonneg
    have hb : N^2 ≤ K*v := hbound lam y hlam hlams hy
    have hNv : 2*N ≤ K+v := by nlinarith only [hb,hK,hv,hN,sq_nonneg (K-v)]
    obtain ⟨D,hD,hval⟩ := MatrixDual.trace_objective_approx
      (objectiveMatrix_posSemidef b O hlam) (cutMatrix_posSemidef c hy)
      (show 2*N < K+eta+v by linarith only [hNv,heta])
    refine ⟨D,hD,?_⟩
    have htr := trace_cutMatrix c y d D
    rw [trace_objectiveMatrix] at hval
    change (∑t,lam t*boundaryAverage b O t D) + (cutMatrix c y*D).trace < K+eta+v at hval
    linarith only [hval,htr])
  exact ⟨D,hD,hf,fun j => sub_neg.mp (hg j)⟩

lemma weighted_rows_bound (O : T → Finset E) (lam : T → ℝ) (a : E → ℝ)
    (hlam : ∀t, 0 ≤ lam t) (hsum : (∑t, lam t)=1) (ha : ∀e, 0 ≤ a e) :
    (∑e, Real.sqrt (∑t, if e ∈ O t then lam t / ((O t).card : ℝ) else 0)*a e)^2 ≤
      ∑t, (∑e ∈ O t, a e)^2/((O t).card : ℝ) := by
  let r : T → ℝ := fun t => Real.sqrt (lam t / ((O t).card : ℝ))
  let c : T → ℝ := fun t => (∑e ∈ O t, a e)/Real.sqrt ((O t).card : ℝ)
  have hw (e : E) : Real.sqrt (∑t, if e ∈ O t then lam t / ((O t).card : ℝ) else 0) ≤
      ∑t, if e ∈ O t then r t else 0 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨sum_nonneg (fun t _ => by split_ifs; exact Real.sqrt_nonneg _; exact le_rfl), ?_⟩
    calc
      (∑t, if e ∈ O t then lam t / ((O t).card : ℝ) else 0) =
          ∑t, (if e ∈ O t then r t else 0)^2 := by
        apply sum_congr rfl
        intro t _
        split_ifs
        · exact (Real.sq_sqrt (div_nonneg (hlam t) (Nat.cast_nonneg _))).symm
        · norm_num
      _ ≤ _ := sum_sq_le_sq_sum_of_nonneg (fun t _ => by split_ifs; exact Real.sqrt_nonneg _; exact le_rfl)
  have heq : (∑e, (∑t, if e ∈ O t then r t else 0)*a e) =
      ∑t, Real.sqrt (lam t)*c t := by
    simp_rw [sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro t _
    calc
      (∑e, (if e ∈ O t then r t else 0)*a e) = r t*∑e ∈ O t, a e := by
        rw [mul_sum]
        simp only [ite_mul,zero_mul]
        rw [←sum_filter]
        simp
      _ = Real.sqrt (lam t)*c t := by
        dsimp [r,c]
        rw [Real.sqrt_div (hlam t)]
        ring
  have hle := sum_le_sum (fun e (_ : e ∈ (univ : Finset E)) =>
    mul_le_mul_of_nonneg_right (hw e) (ha e))
  rw [heq] at hle
  have hsq := pow_le_pow_left₀ (sum_nonneg (fun e _ =>
    mul_nonneg (Real.sqrt_nonneg _) (ha e))) hle 2
  have hc := sum_mul_sq_le_sq_mul_sq univ (fun t => Real.sqrt (lam t)) c
  have hs : (∑t, (Real.sqrt (lam t))^2)=1 := by simpa only [Real.sq_sqrt (hlam _)] using hsum
  rw [hs,one_mul] at hc
  refine hsq.trans (hc.trans_eq ?_)
  apply sum_congr rfl
  intro t _
  simp only [c,div_pow,Real.sq_sqrt (Nat.cast_nonneg _)]

omit [Fintype V] [DecidableEq V] in
lemma objectiveMatrix_eq_sum_edges (b : E → V → ℝ) (O : T → Finset E) (lam : T → ℝ) :
    objectiveMatrix b O lam = ∑e, (∑t, if e ∈ O t then lam t / ((O t).card : ℝ) else 0) •
      vecMulVec (b e) (b e) := by
  have ht (t : T) : lam t • boundaryMatrix b O t =
      ∑e, (if e ∈ O t then lam t / ((O t).card : ℝ) else 0) • vecMulVec (b e) (b e) := by
    simp only [boundaryMatrix,smul_smul,div_eq_mul_inv,smul_sum,ite_smul,zero_smul]
    rw [←sum_filter]
    simp
  simp only [objectiveMatrix,ht]
  rw [sum_comm]
  simp only [sum_smul]

omit [Fintype V] [DecidableEq V] in
lemma weighted_gram (b : E → V → ℝ) (w : E → ℝ) :
    let B : Matrix V E ℝ := fun v e => b e v
    (B*diagonal w)*(B*diagonal w)ᵀ=∑e, (w e)^2 • vecMulVec (b e) (b e) := by
  dsimp
  ext i j
  change (∑e, ((Matrix.of (fun v e => b e v))*diagonal w) i e *
    ((Matrix.of (fun v e => b e v))*diagonal w) j e) = _
  simp only [mul_diagonal,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,vecMulVec_apply,Matrix.of_apply]
  apply sum_congr rfl
  intro e _
  ring

omit [Fintype V] [DecidableEq V] in
lemma objectiveMatrix_gram (b : E → V → ℝ) (O : T → Finset E) {lam : T → ℝ}
    (hlam : ∀t, 0 ≤ lam t) :
    let C : Matrix V E ℝ := (Matrix.of (fun v e => b e v))*diagonal (edgeWeight O lam)
    objectiveMatrix b O lam=C*Cᵀ := by
  dsimp
  rw [weighted_gram,objectiveMatrix_eq_sum_edges]
  apply sum_congr rfl
  intro e _
  have hp : 0 ≤ ∑t, if e ∈ O t then lam t / ((O t).card : ℝ) else 0 :=
    sum_nonneg (fun t _ => by split_ifs; exact div_nonneg (hlam t) (Nat.cast_nonneg _); exact le_rfl)
  rw [edgeWeight,Real.sq_sqrt hp]
  rfl

lemma nuclear_bound_of_embedding_bound (b : E → V → ℝ) (O : T → Finset E)
    {H : Type uH} [Fintype H] [DecidableEq H] (X : Matrix H V ℝ) {K : ℝ}
    (hbound : ∀U : Matrix E H ℝ, Uᵀ*U ≤ 1 → (∀e, 0 ≤ (U*(X*(Matrix.of (fun v e => b e v)))) e e) →
      (∑t, (∑e ∈ O t, (U*(X*(Matrix.of (fun v e => b e v)))) e e)^2/((O t).card : ℝ)) ≤ K)
    {lam : T → ℝ} (hlam : ∀t, 0 ≤ lam t) (hsum : (∑t, lam t)=1) :
    (CFC.sqrt (CFC.sqrt (Xᵀ*X)*objectiveMatrix b O lam*CFC.sqrt (Xᵀ*X))).trace^2 ≤ K := by
  let B : Matrix V E ℝ := fun v e => b e v
  let w := edgeWeight O lam
  have hw : ∀e, 0 ≤ w e := fun e => Real.sqrt_nonneg _
  obtain ⟨U,hU,hpos,htr⟩ := Polar.positive_optimizer (X*B) w hw
  rw [objectiveMatrix_gram b O hlam,Polar.dual_trace_rectangular]
  change (CFC.sqrt ((X*(B*diagonal w))*(X*(B*diagonal w))ᵀ)).trace^2 ≤ K
  rw [←Matrix.mul_assoc]
  have hsq := pow_le_pow_left₀ (CFC.sqrt_nonneg _).posSemidef.trace_nonneg htr 2
  exact hsq.trans ((weighted_rows_bound O lam (fun e => (U*(X*B)) e e) hlam hsum hpos).trans
    (hbound U hU hpos))

lemma sqrt_smul_real {A : Matrix V V ℝ} (hA : A.PosSemidef) {s : ℝ} (hs : 0 ≤ s) :
    CFC.sqrt (s • A)=Real.sqrt s • CFC.sqrt A := by
  apply CFC.sqrt_unique
  · simp only [smul_mul_assoc,mul_smul_comm,smul_smul,
      Real.mul_self_sqrt hs,CFC.sqrt_mul_sqrt_self A hA.nonneg]
  · exact ((CFC.sqrt_nonneg A).posSemidef.smul (Real.sqrt_nonneg s)).nonneg

lemma traceRoot_sq_smul {A Z : Matrix V V ℝ} (hA : A.PosSemidef) (hZ : Z.PosSemidef)
    {s : ℝ} (hs : 0 ≤ s) :
    (CFC.sqrt (CFC.sqrt (s • Z)*A*CFC.sqrt (s • Z))).trace^2 =
      s*(CFC.sqrt (CFC.sqrt Z*A*CFC.sqrt Z)).trace^2 := by
  have hp : (CFC.sqrt Z*A*CFC.sqrt Z).PosSemidef := by
    simpa only [(CFC.sqrt_nonneg Z).posSemidef.isHermitian.eq] using
      hA.conjTranspose_mul_mul_same (CFC.sqrt Z)
  rw [sqrt_smul_real hZ hs]
  simp only [smul_mul_assoc,mul_smul_comm,smul_smul,Real.mul_self_sqrt hs]
  rw [sqrt_smul_real hp hs,trace_smul]
  simp only [smul_eq_mul,mul_pow,Real.sq_sqrt hs]

lemma traceRoot_sq_tendsto {I : Type uI4} {l : Filter I} {A Z : Matrix V V ℝ}
    (hA : A.PosSemidef) (hZ : Z.PosSemidef) {g : I → Matrix V V ℝ}
    (hg : Tendsto g l (𝓝 Z)) (hgp : ∀ᶠ i in l, (g i).PosSemidef) :
    Tendsto (fun i => (CFC.sqrt (CFC.sqrt (g i)*A*CFC.sqrt (g i))).trace^2) l
      (𝓝 ((CFC.sqrt (CFC.sqrt Z*A*CFC.sqrt Z)).trace^2)) := by
  have h := MatrixDual.traceRoot_tendsto hA hZ tendsto_const_nhds hg
    (Eventually.of_forall (fun _ => hA)) hgp
  have hr := h.div_const 2
  simp only [mul_div_cancel_left₀ _ (show (2:ℝ) ≠ 0 by norm_num)] at hr
  exact hr.pow 2

omit [Fintype V] [DecidableEq V] in
lemma cutMatrix_smul (c : J → V → ℝ) (y : J → ℝ) (s : ℝ) :
    cutMatrix c (fun j => s*y j)=s • cutMatrix c y := by
  simp only [cutMatrix,smul_sum,smul_smul]

lemma trace_bound_of_nat_weights {A : Matrix V V ℝ} (hA : A.PosSemidef)
    (c : J → V → ℝ) (d : J → ℝ) (K : ℝ)
    (hb : ∀a : J → ℕ,
      (CFC.sqrt (CFC.sqrt (cutMatrix c (fun j => (a j : ℝ)))*A*
        CFC.sqrt (cutMatrix c (fun j => (a j : ℝ))))).trace^2 ≤ K*∑j, (a j : ℝ)*d j)
    {y : J → ℝ} (hy : ∀j, 0 ≤ y j) :
    (CFC.sqrt (CFC.sqrt (cutMatrix c y)*A*CFC.sqrt (cutMatrix c y))).trace^2 ≤
      K*∑j, y j*d j := by
  let a : ℝ → J → ℕ := fun t j => ⌊y j*t⌋₊
  let z : ℝ → J → ℝ := fun t j => (a t j : ℝ)/t
  have hz (j : J) : Tendsto (fun t => z t j) atTop (𝓝 (y j)) :=
    tendsto_nat_floor_mul_div_atTop (hy j)
  have hg : Tendsto (fun t => cutMatrix c (z t)) atTop (𝓝 (cutMatrix c y)) :=
    tendsto_finsetSum univ (fun j _ => (hz j).smul_const (vecMulVec (c j) (c j)))
  have hgp : ∀ᶠ t in atTop, (cutMatrix c (z t)).PosSemidef := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    exact cutMatrix_posSemidef c (fun j => div_nonneg (Nat.cast_nonneg _) ht.le)
  have hl := traceRoot_sq_tendsto hA (cutMatrix_posSemidef c hy) hg hgp
  have hr : Tendsto (fun t => K*∑j, z t j*d j) atTop (𝓝 (K*∑j,y j*d j)) :=
    (tendsto_finsetSum univ (fun j _ => (hz j).mul_const (d j))).const_mul K
  apply le_of_tendsto_of_tendsto hl hr
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  have heq : cutMatrix c (z t)=t⁻¹ • cutMatrix c (fun j => (a t j : ℝ)) := by
    simpa only [z,div_eq_mul_inv,mul_comm] using
      cutMatrix_smul c (fun j => (a t j : ℝ)) t⁻¹
  rw [heq,traceRoot_sq_smul hA (cutMatrix_posSemidef c (fun j => Nat.cast_nonneg _))
    (inv_nonneg.mpr ht.le)]
  have hh := mul_le_mul_of_nonneg_left (hb (a t)) (inv_nonneg.mpr ht.le)
  convert hh using 1
  simp only [z,div_eq_mul_inv,mul_sum]
  apply sum_congr rfl
  intro j _
  ring

omit [Fintype V] [DecidableEq V] in
lemma replicaMatrix_binary (c : J → V → ℝ) (hc : ∀j v, c j v=0 ∨ c j v=1)
    (a : J → ℕ) : ∀i v, replicaMatrix c a i v=0 ∨ replicaMatrix c a i v=1 :=
  fun _i v => hc _ v

omit [Fintype V] [DecidableEq V] in
lemma replicaMatrix_gram (c : J → V → ℝ) (a : J → ℕ) :
    (replicaMatrix c a)ᵀ*replicaMatrix c a=cutMatrix c (fun j => (a j : ℝ)) := by
  ext v w
  change (∑i, c ((Fintype.equivFin (Σj, Fin (a j))).symm i).1 v *
    c ((Fintype.equivFin (Σj, Fin (a j))).symm i).1 w) = _
  rw [(Fintype.equivFin (Σj, Fin (a j))).symm.sum_comp
    (fun i : (Σj, Fin (a j)) => c i.1 v*c i.1 w)]
  simp only [Fintype.sum_sigma,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    cutMatrix,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,vecMulVec_apply]

omit [DecidableEq V] [DecidableEq E] in
lemma replicaMatrix_energy (b : E → V → ℝ) (c : J → V → ℝ) (a : J → ℕ) :
    (∑e, ∑i, (replicaMatrix c a * Matrix.of (fun v e => b e v)) i e ^ 2) =
      ∑j, (a j : ℝ)*(∑e, (∑v, c j v*b e v)^2) := by
  rw [sum_comm]
  change (∑i, (fun j : (Σj, Fin (a j)) => ∑e, (∑v, c j.1 v*b e v)^2)
    ((Fintype.equivFin (Σj, Fin (a j))).symm i)) = _
  rw [(Fintype.equivFin (Σj, Fin (a j))).symm.sum_comp
    (fun j : (Σj, Fin (a j)) => ∑e, (∑v, c j.1 v*b e v)^2)]
  simp only [Fintype.sum_sigma,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

lemma shortcut_of_binary_bound (b : E → V → ℝ) (O : T → Finset E)
    (c : J → V → ℝ) (d : J → ℝ) (hc : ∀j v, c j v=0 ∨ c j v=1)
    (hd : ∀j, 0 < d j) (henergy : ∀j, (∑e, (∑v, c j v*b e v)^2)=d j)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀h : ℕ, ∀X : Matrix (Fin h) V ℝ, (∀i v, X i v=0 ∨ X i v=1) →
      ∀U : Matrix E (Fin h) ℝ, Uᵀ*U ≤ 1 →
      (∀e, 0 ≤ (U*(X*Matrix.of (fun v e => b e v))) e e) →
      (∑t, (∑e ∈ O t, (U*(X*Matrix.of (fun v e => b e v))) e e)^2/((O t).card : ℝ)) ≤
        K*(∑e, ∑i, (X*Matrix.of (fun v e => b e v)) i e ^2))
    {eta : ℝ} (heta : 0 < eta) :
    ∃D : Matrix V V ℝ, D.PosDef ∧
      (∀t, boundaryAverage b O t D < K+eta) ∧ (∀j, c j ⬝ᵥ (D *ᵥ c j) < d j) := by
  apply shortcut_of_trace_bound b O c d hd hK _ heta
  intro lam y hlam hlams hy
  apply trace_bound_of_nat_weights (objectiveMatrix_posSemidef b O hlam) c d K _ hy
  intro a
  have heq := nuclear_bound_of_embedding_bound b O (replicaMatrix c a)
    (hbound _ _ (replicaMatrix_binary c hc a)) hlam hlams
  rwa [replicaMatrix_gram,replicaMatrix_energy,show
    (∑j, (a j : ℝ)*(∑ e, (∑ v, c j v*b e v)^2))=∑j, (a j : ℝ)*d j by simp_rw [henergy]] at heq

end
end StrongThinTree.ShortcutDual

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.ShortcutDuality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace StrongThinTree.MultiGraph
noncomputable section
open Matrix Finset StrongThinTree.Geometry
open scoped Classical MatrixOrder Matrix.Norms.L2Operator
variable {n m h : ℕ} (G : MultiGraph n m)

lemma eval_incidence (x : Fin n → ℝ) (e : Fin m) :
    (∑v, x v*G.incidence e v)=x (G.left e)-x (G.right e) := by
  simp [incidence,point,Pi.sub_apply,mul_sub,sum_sub_distrib,Pi.single_apply,mul_ite]

lemma cutIndicator_binary (S : Finset (Fin n)) (v : Fin n) :
    cutIndicator S v=0 ∨ cutIndicator S v=1 := by
  by_cases hv : v ∈ S <;> simp [cutIndicator,hv]

lemma cutIndicator_energy (S : Finset (Fin n)) :
    (∑e, (∑v, cutIndicator S v*G.incidence e v)^2)=((G.cut univ S).card : ℝ) := by
  simp only [G.eval_incidence]
  simp only [cut,card_eq_sum_ones,Nat.cast_sum,sum_filter]
  apply sum_congr rfl
  intro e _
  by_cases hl : G.left e ∈ S <;> by_cases hr : G.right e ∈ S <;>
    simp [cutIndicator,hl,hr]

namespace Hierarchy
variable {G : MultiGraph n m} {H : Hierarchy n}

lemma shortcutCoefficient_nonneg (q L R : ℕ) {α ε : ℝ} (hα : 0 ≤ α) :
    0 ≤ shortcutCoefficient q L R α ε := by
  unfold shortcutCoefficient
  have hg := (truncationGain_pos α).le
  positivity

lemma exists_shortcut_explicit {q L R : ℕ} (hq : 0 < q) (hL : 0 < L) (hR : 0 < R)
    (hk : G.EdgeConnected q) (hconn : H.LocallyConnectedReal G q)
    (M : Finset (Finset (Fin n))) (hM : M ⊆ H.nodes) (hroot : ∀t ∈ M, t ≠ univ)
    {α ε ρ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (he : 0 < ε) (he1 : ε < 1/3)
    (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/1536)
    (hsmall : (α*truncationGain α/32)^ε ≤ 1/(1728*(1024/ε^2)))
    (hassign : (6144:ℝ)/q ≤ (α*truncationGain α/32)^(1+2*ε))
    (hratio : ∀t ∈ M, (q:ℝ)*ρ*((G.cut univ t).card : ℝ) ≤ (H.parentBoundary G t).card)
    (hlogL : Real.logb 2 (16/(α*truncationGain α))+1 < L)
    (hlogR : Real.logb 2 (24/(ρ*(α*truncationGain α/32)^2)) < R)
    {η : ℝ} (hη : 0 < η) :
    ∃D : Matrix (Fin n) (Fin n) ℝ, D.PosDef ∧
      (∀t ∈ M, ShortcutDual.boundaryAverage G.incidence (H.parentBoundary G) t D <
        shortcutCoefficient q L R α ε+η) ∧
      (∀S : Finset (Fin n), S.Nonempty → S ≠ univ →
        cutIndicator S ⬝ᵥ (D *ᵥ cutIndicator S) < ((G.cut univ S).card : ℝ)) := by
  have hd (S : ProperCut n) : 0 < ((G.cut univ S).card : ℝ) :=
    Nat.cast_pos.mpr (hq.trans_le (hk S.val S.property.1 S.property.2))
  obtain ⟨D,hD,hb,hc⟩ := ShortcutDual.shortcut_of_binary_bound G.incidence
    (fun t : M => H.parentBoundary G t) (fun S : ProperCut n => cutIndicator S.val)
    (fun S : ProperCut n => ((G.cut univ S.val).card : ℝ))
    (fun S v => cutIndicator_binary S.val v) hd (fun S => G.cutIndicator_energy S.val)
    (shortcutCoefficient_nonneg q L R hα.le)
    (fun _ X hX U hU hp => binary_numerator_bound hq hL hR hk hconn M hM hroot
      hα hα1 he he1 hρ hρsmall hsmall hassign hratio hlogL hlogR X hX U hU hp) hη
  exact ⟨D,hD,fun t ht => hb ⟨t,ht⟩,fun S hS hS' => hc ⟨S,hS,hS'⟩⟩

end Hierarchy
end
end StrongThinTree.MultiGraph

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Matrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι

section
open Matrix
namespace StrongThinTree
section Resistance
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma quadratic_cauchy_schwarz {X : Matrix ι ι ℝ} (hX : X.PosSemidef)
    (x y : ι → ℝ) :
    (x ⬝ᵥ (X *ᵥ y)) ^ 2 ≤ (x ⬝ᵥ (X *ᵥ x)) * (y ⬝ᵥ (X *ᵥ y)) := by
  let := X.toSeminormedAddCommGroup hX
  let := X.toInnerProductSpace hX
  have h := real_inner_mul_inner_self_le x y
  change ((X *ᵥ y) ⬝ᵥ star x) * ((X *ᵥ y) ⬝ᵥ star x) ≤
    ((X *ᵥ x) ⬝ᵥ star x) * ((X *ᵥ y) ⬝ᵥ star y) at h
  simpa only [star_trivial, dotProduct_comm, pow_two] using h

omit [DecidableEq ι] in
lemma rankOne_quadratic (b x : ι → ℝ) :
    x ⬝ᵥ (vecMulVec b b *ᵥ x) = (b ⬝ᵥ x) ^ 2 := by
  rw [vecMulVec_mulVec]
  simp [dotProduct, Finset.mul_sum, pow_two, mul_comm, mul_left_comm]

lemma posDef_solve {X : Matrix ι ι ℝ} (hX : X.PosDef) (b : ι → ℝ) :
    X *ᵥ (X⁻¹ *ᵥ b) = b := by
  rw [mulVec_mulVec, mul_nonsing_inv X ((isUnit_iff_isUnit_det X).mp hX.isUnit),
    one_mulVec]

theorem resistance_order {X : Matrix ι ι ℝ} (hX : X.PosDef)
    (b : ι → ℝ) {t : ℝ} (ht : 0 < t) :
    b ⬝ᵥ (X⁻¹ *ᵥ b) ≤ t ↔ (t • X - vecMulVec b b).PosSemidef := by
  let y := X⁻¹ *ᵥ b
  have hsolve : X *ᵥ y = b := posDef_solve hX b
  have hq (x : ι → ℝ) : 0 ≤ x ⬝ᵥ (X *ᵥ x) := by
    simpa only [star_trivial] using hX.posSemidef.dotProduct_mulVec_nonneg x
  have hr : 0 ≤ b ⬝ᵥ y := by
    simpa only [hsolve, dotProduct_comm] using hq y
  constructor
  · intro h
    have hb : (vecMulVec b b).IsHermitian := by
      simpa only [star_trivial] using (posSemidef_vecMulVec_self_star b).isHermitian
    refine PosSemidef.of_dotProduct_mulVec_nonneg
      ((hX.isHermitian.smul (isSelfAdjoint_iff.mpr (star_trivial t))).sub hb) ?_
    intro x
    have hcs := quadratic_cauchy_schwarz hX.posSemidef x y
    rw [hsolve] at hcs
    have hm : (x ⬝ᵥ (X *ᵥ x)) * (b ⬝ᵥ y) ≤ (x ⬝ᵥ (X *ᵥ x)) * t :=
      mul_le_mul_of_nonneg_left h (hq x)
    rw [dotProduct_comm y b, dotProduct_comm x b] at hcs
    simp only [star_trivial, sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul,
      smul_eq_mul, rankOne_quadratic]
    linarith
  · intro h
    have htest := h.dotProduct_mulVec_nonneg y
    simp only [star_trivial, sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul,
      smul_eq_mul, rankOne_quadratic, hsolve, dotProduct_comm y b] at htest
    change b ⬝ᵥ y ≤ t
    nlinarith

theorem resistance_antitone {X Y : Matrix ι ι ℝ}
    (hX : X.PosDef) (hY : Y.PosDef) (hXY : (X - Y).PosSemidef) (b : ι → ℝ) :
    b ⬝ᵥ (X⁻¹ *ᵥ b) ≤ b ⬝ᵥ (Y⁻¹ *ᵥ b) := by
  let x := X⁻¹ *ᵥ b
  let y := Y⁻¹ *ᵥ b
  have hx : X *ᵥ x = b := posDef_solve hX b
  have hy : Y *ᵥ y = b := posDef_solve hY b
  have hrX : 0 ≤ b ⬝ᵥ x := by
    simpa only [star_trivial, hx, dotProduct_comm] using
      hX.posSemidef.dotProduct_mulVec_nonneg x
  have hrY : 0 ≤ b ⬝ᵥ y := by
    simpa only [star_trivial, hy, dotProduct_comm] using
      hY.posSemidef.dotProduct_mulVec_nonneg y
  have hcomp : x ⬝ᵥ (Y *ᵥ x) ≤ b ⬝ᵥ x := by
    have h := hXY.dotProduct_mulVec_nonneg x
    simp only [star_trivial, sub_mulVec, dotProduct_sub, hx, dotProduct_comm x b] at h
    linarith
  have hcs := quadratic_cauchy_schwarz hY.posSemidef x y
  rw [hy, dotProduct_comm x b, dotProduct_comm y b] at hcs
  have hm := mul_le_mul_of_nonneg_right hcomp hrY
  change b ⬝ᵥ x ≤ b ⬝ᵥ y
  nlinarith

end Resistance
end StrongThinTree

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.GraphMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV

section

noncomputable section
open Matrix Finset
open scoped MatrixOrder
namespace StrongThinTree
variable {V : Type uV} [Fintype V] [DecidableEq V]
omit [DecidableEq V] in
lemma qform_add (X Y : Matrix V V ℝ) (v : V → ℝ) : qform (X+Y) v=qform X v+qform Y v := by
  simp [qform,add_mulVec,dotProduct_add]
omit [DecidableEq V] in
lemma qform_smul (a : ℝ) (X : Matrix V V ℝ) (v : V → ℝ) : qform (a • X) v=a*qform X v := by
  simp [qform,smul_mulVec,dotProduct_smul]
omit [DecidableEq V] in
lemma qform_nonneg {X : Matrix V V ℝ} (hX : X.PosSemidef) (v : V → ℝ) : 0 ≤ qform X v := by
  simpa only [qform,star_trivial] using hX.dotProduct_mulVec_nonneg v
omit [DecidableEq V] in
lemma qform_continuous (v : V → ℝ) : Continuous (fun X : Matrix V V ℝ => qform X v) := by
  unfold qform mulVec dotProduct
  fun_prop
lemma qform_single (X : Matrix V V ℝ) (i : V) : qform X (Pi.single i 1)=X i i := by
  simp [qform]
omit [Fintype V] [DecidableEq V] in
lemma posDef_of_le {X Y : Matrix V V ℝ} (hX : X.PosDef) (hXY : X ≤ Y) : Y.PosDef := by
  convert hX.add_posSemidef (Matrix.le_iff.mp hXY) using 1; abel

namespace MultiGraph
variable {n m : ℕ} (G : MultiGraph n m)
lemma laplacian_psd (F : Finset (Fin m)) : (G.laplacian F).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro e _
  simpa only [star_trivial] using posSemidef_vecMulVec_self_star (G.incidence e)
lemma laplacian_qform (F : Finset (Fin m)) (v : Fin n → ℝ) :
    qform (G.laplacian F) v=∑e ∈ F, (v (G.left e)-v (G.right e))^2 := by
  simp only [laplacian,qform,sum_mulVec,dotProduct_sum,rankOne_quadratic]
  apply sum_congr rfl
  intro e _
  rw [dotProduct_comm]
  congr 1
  exact G.eval_incidence v e
lemma laplacian_cut (F : Finset (Fin m)) (S : Finset (Fin n)) :
    qform (G.laplacian F) (cutIndicator S)=(G.cut F S).card := by
  rw [G.laplacian_qform]
  simp only [cut,card_eq_sum_ones,Nat.cast_sum,sum_filter]
  apply sum_congr rfl
  intro e _
  by_cases hl : G.left e ∈ S <;> by_cases hr : G.right e ∈ S <;> simp [cutIndicator,hl,hr]
lemma indicator_norm (S : Finset (Fin n)) : qform (1 : Matrix (Fin n) (Fin n) ℝ) (cutIndicator S)=S.card := by
  simp only [qform,one_mulVec,dotProduct,cutIndicator]
  simp

lemma baseMatrix_pd (hn : 0 < n) : G.baseMatrix.PosDef := by
  exact Matrix.PosDef.posSemidef_add (G.laplacian_psd univ) (Matrix.PosDef.one.smul (inv_pos.mpr (Nat.cast_pos.mpr hn)))
lemma baseMatrix_cut (S : Finset (Fin n)) :
    qform G.baseMatrix (cutIndicator S)=(G.cut univ S).card+S.card/(n:ℝ) := by
  rw [baseMatrix,qform_add,qform_smul,G.laplacian_cut,indicator_norm,mul_comm,←div_eq_mul_inv]
lemma resistance_nonneg {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.PosDef) (e : Fin m) : 0 ≤ G.resistance X e :=
  qform_nonneg hX.inv.posSemidef _
lemma resistance_antitone {X Y : Matrix (Fin n) (Fin n) ℝ} (hX : X.PosDef) (hY : Y.PosDef)
    (h : Y ≤ X) (e : Fin m) : G.resistance X e ≤ G.resistance Y e :=
  StrongThinTree.resistance_antitone hX hY (Matrix.le_iff.mp h) _

end MultiGraph
end StrongThinTree

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.MatrixDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV

section

noncomputable section
open Matrix Finset
open scoped MatrixOrder Matrix.Norms.Elementwise
namespace StrongThinTree
variable {V : Type uV} [Fintype V] [DecidableEq V]
omit [DecidableEq V] in
lemma isClosed_psd : IsClosed {X : Matrix V V ℝ | X.PosSemidef} := by
  have heq : {X : Matrix V V ℝ | X.PosSemidef}=
      {X | X.IsHermitian} ∩ ⋂v : V → ℝ, {X | 0 ≤ qform X v} := by
    ext X
    simp only [Set.mem_ofPred,Set.mem_inter_iff,Set.mem_iInter]
    exact ⟨fun h => ⟨h.isHermitian,qform_nonneg h⟩,fun h =>
      Matrix.PosSemidef.of_dotProduct_mulVec_nonneg h.1 (by simpa only [star_trivial,qform] using h.2)⟩
  rw [heq]
  apply IsClosed.inter
  · exact isClosed_eq continuous_id.matrix_conjTranspose continuous_id
  · exact isClosed_iInter (fun v => isClosed_le continuous_const (qform_continuous v))
omit [DecidableEq V] in
lemma isClosed_matrixAbove (A : Matrix V V ℝ) : IsClosed {X : Matrix V V ℝ | A ≤ X} :=
  isClosed_psd.preimage (continuous_id.sub continuous_const)
lemma psd_entry_bound {X : Matrix V V ℝ} (hX : X.PosSemidef) {C : ℝ} (hC : 0 ≤ C)
    (hdiag : ∀i, X i i ≤ C) (i j : V) : |X i j| ≤ C := by
  have hi : 0 ≤ X i i := by simpa only [qform_single] using qform_nonneg hX (Pi.single i 1)
  have hj : 0 ≤ X j j := by simpa only [qform_single] using qform_nonneg hX (Pi.single j 1)
  have hh := quadratic_cauchy_schwarz hX (Pi.single i 1) (Pi.single j 1)
  simp only [mulVec_single_one,single_one_dotProduct] at hh
  change (X i j)^2 ≤ X i i*X j j at hh
  have hm := mul_le_mul (hdiag i) (hdiag j) hj hC
  nlinarith [sq_abs (X i j),abs_nonneg (X i j)]

namespace MultiGraph
variable {n m : ℕ} (G : MultiGraph n m)

lemma domain_pd (hn : 0 < n) {X : Matrix (Fin n) (Fin n) ℝ} (hX : X ∈ G.matrixDomain) : X.PosDef :=
  posDef_of_le (G.baseMatrix_pd hn) hX.1
lemma domain_closed : IsClosed G.matrixDomain := by
  simp only [matrixDomain,Set.ofPred_and,Set.ofPred_forall]
  exact (isClosed_matrixAbove _).inter (isClosed_iInter fun S => isClosed_iInter fun _ =>
    isClosed_iInter fun _ => isClosed_le (qform_continuous _) continuous_const)
lemma domain_convex : Convex ℝ G.matrixDomain := by
  intro X hX Y hY a b ha hb hab
  refine ⟨?_,?_⟩
  · have hh := add_le_add (smul_le_smul_of_nonneg_left hX.1 ha) (smul_le_smul_of_nonneg_left hY.1 hb)
    simpa only [←add_smul,hab,one_smul] using hh
  · intro S hS hS'
    rw [qform_add,qform_smul,qform_smul]
    have hh := add_le_add (mul_le_mul_of_nonneg_left (hX.2 S hS hS') ha)
      (mul_le_mul_of_nonneg_left (hY.2 S hS hS') hb)
    simpa only [←add_mul,hab,one_mul] using hh
lemma domain_nonempty (hn : 0 < n) (hc : G.EdgeConnected 1) : G.matrixDomain.Nonempty := by
  refine ⟨G.baseMatrix,le_rfl,?_⟩
  intro S hS hS'
  rw [G.baseMatrix_cut]
  have hcut : (1:ℝ) ≤ (G.cut univ S).card := by exact_mod_cast hc S hS hS'
  have hcard : (S.card:ℝ) ≤ n := by exact_mod_cast (show S.card ≤ n by simpa using card_le_univ S)
  have hdiv : (S.card:ℝ)/n ≤ 1 := (div_le_one (Nat.cast_pos.mpr hn)).mpr hcard
  linarith
lemma indicator_singleton (i : Fin n) : cutIndicator {i}=Pi.single i 1 := by
  ext j
  simp [cutIndicator,Pi.single_apply,eq_comm]
lemma domain_diag_bound (hn : 2 ≤ n) {X : Matrix (Fin n) (Fin n) ℝ} (hX : X ∈ G.matrixDomain) (i : Fin n) :
    X i i ≤ 3*m := by
  have hproper : ({i} : Finset (Fin n)) ≠ univ := by
    intro he
    have hh := congrArg card he
    simp only [card_singleton,card_univ,Fintype.card_fin] at hh
    omega
  have hh := hX.2 {i} (singleton_nonempty _) hproper
  rw [indicator_singleton,qform_single] at hh
  have hm : ((G.cut univ {i}).card:ℝ) ≤ m := by exact_mod_cast (show (G.cut univ {i}).card ≤ m by simpa using card_le_univ (G.cut univ {i}))
  linarith
lemma domain_bounded (hn : 2 ≤ n) : Bornology.IsBounded G.matrixDomain := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨3*m,fun X hX => ?_⟩
  have hC : (0:ℝ) ≤ 3*m := by positivity
  apply (pi_norm_le_iff_of_nonneg hC).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg hC).mpr
  intro j
  simpa only [Real.norm_eq_abs] using psd_entry_bound (G.domain_pd (by omega) hX).posSemidef hC
    (G.domain_diag_bound hn hX) i j
lemma domain_compact (hn : 2 ≤ n) : IsCompact G.matrixDomain :=
  Metric.isCompact_iff_isClosed_bounded.mpr ⟨G.domain_closed,G.domain_bounded hn⟩
lemma resistance_continuousAt {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.PosDef) (e : Fin m) :
    ContinuousAt (fun Y => G.resistance Y e) X := by
  apply (qform_continuous (G.incidence e)).continuousAt.comp
  apply continuousAt_matrix_inv
  simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hX.det_pos.ne'
lemma resistance_continuousOn (hn : 0 < n) (e : Fin m) : ContinuousOn (fun X => G.resistance X e) G.matrixDomain :=
  fun _ hX => (G.resistance_continuousAt (G.domain_pd hn hX) e).continuousWithinAt

end MultiGraph
end StrongThinTree

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.HierarchyBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Finset Filter
open scoped Topology
namespace StrongThinTree.ShortcutNumeric
open MultiGraph.Hierarchy

lemma eventually_affine_log_lt_rpow (a b : ℝ) {z : ℝ} (hz : 0 < z) :
    ∀ᶠ x : ℝ in atTop, a+b*Real.log x < x^z := by
  have hc : Tendsto (fun x : ℝ => a/x^z) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Pi.inv_apply] using
      ((tendsto_rpow_atTop hz).inv_tendsto_atTop.const_mul a)
  have hl := (isLittleO_log_rpow_atTop hz).tendsto_div_nhds_zero.const_mul b
  have ht : Tendsto (fun x : ℝ => (a+b*Real.log x)/x^z) atTop (𝓝 0) := by
    convert hc.add hl using 1 <;> simp only [mul_zero,add_zero,add_div,mul_div_assoc]
  filter_upwards [ht.eventually_lt_const (show (0:ℝ)<1 by norm_num),eventually_gt_atTop (0:ℝ)] with x hx hxp
  exact (div_lt_one (Real.rpow_pos_of_pos hxp _)).mp hx

lemma eventually_const_mul_rpow_le_rpow (c : ℝ) {a b : ℝ} (hab : a < b) :
    ∀ᶠ x : ℝ in atTop, c*x^a ≤ x^b := by
  have hh := (tendsto_rpow_atTop (sub_pos.mpr hab)).eventually (eventually_ge_atTop c)
  filter_upwards [hh,eventually_gt_atTop (0:ℝ)] with x hx hxp
  calc
    c*x^a ≤ x^(b-a)*x^a := mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg hxp.le _)
    _ = x^b := by rw [←Real.rpow_add hxp]; congr 1; ring

lemma eventually_logb_mul_rpow_lt (c a b : ℝ) (hc : 0 < c) {z : ℝ} (hz : 0 < z) :
    ∀ᶠ x : ℝ in atTop, Real.logb 2 (c*x^a)+b < x^z := by
  filter_upwards [eventually_affine_log_lt_rpow (Real.log c/Real.log 2+b) (a/Real.log 2) hz,
    eventually_gt_atTop (0:ℝ)] with x hx hxp
  rw [Real.logb,Real.log_mul hc.ne' (Real.rpow_pos_of_pos hxp a).ne',Real.log_rpow hxp]
  convert hx using 1; ring

lemma bins_log (x : ℝ) (hx : 0 < x) :
    Real.logb 2 (256/(alpha x)^2) = Real.logb 2 256+(8/5:ℝ)/Real.log 2*Real.log x := by
  have ha : 0 < alpha x := Real.rpow_pos_of_pos hx _
  rw [Real.logb,Real.log_div (by norm_num) (pow_ne_zero _ ha.ne'),Real.log_pow,
    alpha,Real.log_rpow hx,Real.logb]
  ring

lemma eventually_bins_le :
    ∀ᶠ x : ℝ in atTop, (truncationBins (alpha x) : ℝ) ≤ x^(1/1000:ℝ) := by
  filter_upwards [eventually_affine_log_lt_rpow (Real.logb 2 256+2) ((8/5:ℝ)/Real.log 2)
    (show 0 < (1/1000:ℝ) by norm_num),eventually_ge_atTop (1:ℝ)] with x hh hx
  have hxp : 0 < x := zero_lt_one.trans_le hx
  have hlog : 0 ≤ Real.logb 2 (256/alpha x^2) := by
    rw [bins_log x hxp]
    have hlogx := Real.log_nonneg hx
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog256 : 0 ≤ Real.logb 2 256 := Real.logb_nonneg (by norm_num) (by norm_num)
    positivity
  have hc := Nat.ceil_lt_add_one hlog
  dsimp [truncationBins]
  push_cast
  rw [bins_log x hxp] at hc ⊢
  linarith

lemma gamma_pos {x : ℝ} : 0 < gamma x := truncationGain_pos _
lemma scale_pos {x : ℝ} (hx : 0 < x) : 0 < scale x := by
  have ha : 0 < alpha x := Real.rpow_pos_of_pos hx _
  have hg : 0 < gamma x := gamma_pos
  dsimp [scale]; positivity

lemma gamma_le_one (x : ℝ) : gamma x ≤ 1 := by
  have hJ : 1 ≤ (truncationBins (alpha x) : ℝ) := by
    dsimp [truncationBins]
    push_cast
    have hh : (0:ℝ) ≤ ⌈Real.logb 2 (256/alpha x^2)⌉₊ := Nat.cast_nonneg _
    linarith
  have hp : 1 ≤ (truncationBins (alpha x) : ℝ)^4 := one_le_pow₀ hJ
  change 1/(4*(truncationBins (alpha x) : ℝ)^4) ≤ 1
  apply (div_le_one (by positivity : (0:ℝ)<4*(truncationBins (alpha x):ℝ)^4)).mpr
  linarith

lemma eventually_gamma_lower :
    ∀ᶠ x : ℝ in atTop, x^(-1/100:ℝ) ≤ gamma x := by
  filter_upwards [eventually_bins_le,
    eventually_const_mul_rpow_le_rpow 4 (show (1/250:ℝ)<1/100 by norm_num),
    eventually_gt_atTop (0:ℝ)] with x hJ hc hx
  have hp : 4*(truncationBins (alpha x):ℝ)^4 ≤ x^(1/100:ℝ) := by
    calc
      _ ≤ 4*(x^(1/1000:ℝ))^4 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hJ 4) (by norm_num)
      _ = 4*x^(1/250:ℝ) := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hx.le]
        norm_num
      _ ≤ _ := hc
  have hJp : 0 < (truncationBins (alpha x):ℝ) := by
    dsimp [truncationBins]
    positivity
  rw [show (-1/100:ℝ)=-(1/100) by ring,Real.rpow_neg hx.le]
  change (x^(1/100:ℝ))⁻¹ ≤ 1/(4*(truncationBins (alpha x):ℝ)^4)
  simpa only [one_div] using one_div_le_one_div_of_le (by positivity) hp

lemma scale_le_alpha {x : ℝ} (hx : 0 < x) : scale x ≤ alpha x := by
  have ha : 0 < alpha x := Real.rpow_pos_of_pos hx _
  have hh := mul_le_mul_of_nonneg_left (gamma_le_one x) ha.le
  dsimp [scale]
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<32)).mpr
  linarith

lemma eventually_scale_lower :
    ∀ᶠ x : ℝ in atTop, x^(-41/50:ℝ) ≤ scale x := by
  filter_upwards [eventually_gamma_lower,
    eventually_const_mul_rpow_le_rpow 32 (show (-41/50:ℝ) < -81/100 by norm_num),
    eventually_gt_atTop (0:ℝ)] with x hg hc hx
  have ha : 0 < alpha x := Real.rpow_pos_of_pos hx _
  have hh := mul_le_mul_of_nonneg_left hg ha.le
  have heq : alpha x*x^(-1/100:ℝ)=x^(-81/100:ℝ) := by
    rw [alpha,←Real.rpow_add hx]
    norm_num
  rw [heq] at hh
  dsimp [scale]
  apply (le_div_iff₀ (by norm_num : (0:ℝ)<32)).mpr
  linarith

lemma count_pos {x : ℝ} (hx : 0 < x) : 0 < count x :=
  Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hx _)

lemma count_upper {x : ℝ} (hx : 1 ≤ x) : (count x : ℝ) ≤ 2*x^(1/100:ℝ) := by
  have hh : 1 ≤ x^(1/100:ℝ) := Real.one_le_rpow hx (by norm_num)
  have hc := Nat.ceil_lt_add_one (Real.rpow_nonneg (zero_le_one.trans hx) (1/100:ℝ))
  change (⌈x^(1/100:ℝ)⌉₊:ℝ) ≤ _
  linarith

lemma eventually_small :
    ∀ᶠ x : ℝ in atTop, (scale x)^(1/10:ℝ) ≤ 1/(1728*(1024/(1/10:ℝ)^2)) := by
  have ht : Tendsto (fun x : ℝ => x^(-2/25:ℝ)) atTop (𝓝 0) := by
    convert tendsto_rpow_neg_atTop (show (0:ℝ)<2/25 by norm_num) using 1; norm_num
  filter_upwards [ht.eventually_lt_const (show (0:ℝ)<1/(1728*(1024/(1/10:ℝ)^2)) by norm_num),
    eventually_gt_atTop (0:ℝ)] with x hh hx
  have hl := Real.rpow_le_rpow (scale_pos hx).le (scale_le_alpha hx) (by norm_num : (0:ℝ)≤1/10)
  have heq : (alpha x)^(1/10:ℝ)=x^(-2/25:ℝ) := by
    rw [alpha,←Real.rpow_mul hx.le]
    norm_num
  rw [heq] at hl
  exact hl.trans hh.le

lemma eventually_assignment :
    ∀ᶠ x : ℝ in atTop, 6144/x ≤ (scale x)^(1+2*(1/10:ℝ)) := by
  filter_upwards [eventually_scale_lower,
    eventually_const_mul_rpow_le_rpow 6144 (show (-1:ℝ) < -123/125 by norm_num),
    eventually_gt_atTop (0:ℝ)] with x hs hc hx
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg hx.le _) hs
    (by norm_num : (0:ℝ)≤1+2*(1/10:ℝ))
  rw [←Real.rpow_mul hx.le] at hh
  norm_num at hh
  norm_num only at hc ⊢
  simpa only [Real.rpow_neg_one,div_eq_mul_inv] using hc.trans hh

lemma eventually_log_count_left :
    ∀ᶠ x : ℝ in atTop, Real.logb 2 (16/(alpha x*gamma x))+1 < (count x:ℝ) := by
  filter_upwards [eventually_gamma_lower,
    eventually_logb_mul_rpow_lt 16 (81/100) 1 (by norm_num) (show (0:ℝ)<1/100 by norm_num),
    eventually_gt_atTop (0:ℝ)] with x hg hh hx
  have hb : x^(-81/100:ℝ) ≤ alpha x*gamma x := by
    have h := mul_le_mul_of_nonneg_left hg (Real.rpow_nonneg hx.le (-4/5:ℝ))
    rw [←Real.rpow_add hx] at h
    norm_num at h
    norm_num [alpha] at ⊢
    exact h
  have harg : 16/(alpha x*gamma x) ≤ 16*x^(81/100:ℝ) := by
    calc
      _ ≤ 16/x^(-81/100:ℝ) := div_le_div_of_nonneg_left (by norm_num) (Real.rpow_pos_of_pos hx _) hb
      _ = _ := by rw [show (-81/100:ℝ)=-(81/100) by ring,Real.rpow_neg hx.le,div_inv_eq_mul]
  have hp : 0 < 16/(alpha x*gamma x) := by
    have ha : 0 < alpha x := Real.rpow_pos_of_pos hx _
    have hg : 0 < gamma x := gamma_pos
    positivity
  have hl := (Real.logb_le_logb (by norm_num : (1:ℝ)<2) hp (hp.trans_le harg)).mpr harg
  have hcount := Nat.le_ceil (x^(1/100:ℝ))
  dsimp [count]
  linarith

lemma eventually_log_count_right :
    ∀ᶠ x : ℝ in atTop, Real.logb 2 (24/(rho x*(scale x)^2)) < (count x:ℝ) := by
  filter_upwards [eventually_scale_lower,
    eventually_logb_mul_rpow_lt 48 (91/25) 0 (by norm_num) (show (0:ℝ)<1/100 by norm_num),
    eventually_gt_atTop (0:ℝ)] with x hs hh hx
  have hs2 : x^(-41/25:ℝ) ≤ (scale x)^2 := by
    have h := pow_le_pow_left₀ (Real.rpow_nonneg hx.le _) hs 2
    rw [←Real.rpow_natCast,←Real.rpow_mul hx.le] at h
    norm_num at h
    norm_num at ⊢
    exact h
  have hr : 0 < rho x := by dsimp [rho]; positivity
  have hp : 0 < rho x*(scale x)^2 := mul_pos hr (sq_pos_of_pos (scale_pos hx))
  have harg : 24/(rho x*(scale x)^2) ≤ 48*x^(91/25:ℝ) := by
    apply (div_le_iff₀ hp).mpr
    calc
      24 = (48*x^(91/25:ℝ)*rho x)*x^(-41/25:ℝ) := by
        rw [rho]
        have heq : x^(91/25:ℝ)*x^(-41/25:ℝ)=x^2 := by
          rw [←Real.rpow_add hx]
          norm_num
        field_simp
        linarith only [heq]
      _ ≤ (48*x^(91/25:ℝ)*rho x)*(scale x)^2 :=
        mul_le_mul_of_nonneg_left hs2 (by positivity)
      _ = _ := by ring
  have hl := (Real.logb_le_logb (by norm_num : (1:ℝ)<2) (div_pos (by norm_num) hp)
    ((div_pos (by norm_num) hp).trans_le harg)).mpr harg
  exact hl.trans_lt (by simpa only [add_zero,count] using hh.trans_le (Nat.le_ceil _))

lemma coefficient_eq {x : ℝ} (hx : 0 < x) :
    coefficient x = 2*alpha x+(2*8192*6912*102400)*((count x:ℝ)^2)/(x*(scale x)^(1/10:ℝ)*gamma x) := by
  unfold coefficient
  norm_num
  field_simp
  ring

lemma eventually_denominator_lower :
    ∀ᶠ x : ℝ in atTop, x^(227/250:ℝ) ≤ x*(scale x)^(1/10:ℝ)*gamma x := by
  filter_upwards [eventually_scale_lower,eventually_gamma_lower,eventually_gt_atTop (0:ℝ)] with x hs hg hx
  have hsp := Real.rpow_le_rpow (Real.rpow_nonneg hx.le _) hs (by norm_num : (0:ℝ)≤1/10)
  rw [←Real.rpow_mul hx.le] at hsp
  have hh := mul_le_mul (mul_le_mul_of_nonneg_left hsp hx.le) hg (Real.rpow_nonneg hx.le _)
    (mul_nonneg hx.le (Real.rpow_nonneg (scale_pos hx).le _))
  have heq : x*x^((-41/50:ℝ)*(1/10))*x^(-1/100:ℝ)=x^(227/250:ℝ) := by
    calc
      _ = x^((1:ℝ)+(-41/50:ℝ)*(1/10))*x^(-1/100:ℝ) := by
        rw [Real.rpow_add hx,Real.rpow_one]
      _ = _ := by rw [←Real.rpow_add hx]; norm_num
  rwa [heq] at hh

lemma eventually_coefficient_bound :
    ∀ᶠ x : ℝ in atTop, coefficient x ≤ 2*x^(-4/5:ℝ)+largeConstant*x^(-111/125:ℝ) := by
  filter_upwards [eventually_denominator_lower,eventually_ge_atTop (1:ℝ)] with x hd hx
  have hxp : 0 < x := zero_lt_one.trans_le hx
  have hc : (count x:ℝ)^2 ≤ 4*x^(1/50:ℝ) := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg _) (count_upper hx) 2
    rw [mul_pow,←Real.rpow_natCast (x^(1/100:ℝ)) 2,←Real.rpow_mul hxp.le] at hh
    norm_num at hh
    exact hh
  rw [coefficient_eq hxp]
  apply add_le_add (le_refl (2*alpha x))
  calc
    _ ≤ (2*8192*6912*102400)*(4*x^(1/50:ℝ))/x^(227/250:ℝ) :=
      div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hc (by norm_num))
        (Real.rpow_pos_of_pos hxp _) hd
    _ = largeConstant*x^(-111/125:ℝ) := by
      calc
        _ = largeConstant*(x^(1/50:ℝ)/x^(227/250:ℝ)) := by unfold largeConstant; ring
        _ = _ := by rw [←Real.rpow_sub hxp]; norm_num

lemma eventually_coefficient_small :
    ∀ᶠ x : ℝ in atTop, coefficient x ≤ x^(-31/40:ℝ)/2 := by
  filter_upwards [eventually_coefficient_bound,
    eventually_const_mul_rpow_le_rpow 8 (show (-4/5:ℝ) < -31/40 by norm_num),
    eventually_const_mul_rpow_le_rpow (4*largeConstant) (show (-111/125:ℝ) < -31/40 by norm_num)]
    with x hb h1 h2
  linarith

lemma eventually_rho_small :
    ∀ᶠ x : ℝ in atTop, rho x ≤ 1/1536 := by
  filter_upwards [eventually_ge_atTop (100:ℝ)] with x hx
  have hp : 0 < 2*x^2 := by positivity
  apply (div_le_iff₀ hp).mpr
  linarith [sq_nonneg (x-100)]

lemma eventually_good : ∀ᶠ x : ℝ in atTop, GoodParameters x := by
  filter_upwards [eventually_ge_atTop (2:ℝ),eventually_small,eventually_assignment,
    eventually_rho_small,eventually_log_count_left,eventually_log_count_right,
    eventually_coefficient_small] with x h1 h2 h3 h4 h5 h6 h7
  exact ⟨h1,h2,h3,h4,h5,h6,h7⟩

lemma exists_cutoff : ∃qH : ℕ, 2 ≤ qH ∧ ∀q : ℕ, qH ≤ q → GoodParameters q := by
  have hh : ∀ᶠ q : ℕ in atTop, GoodParameters q :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun q : ℕ => (q:ℝ)) atTop atTop).eventually eventually_good
  obtain ⟨qH,hqH⟩ := hh.exists_forall_of_atTop
  exact ⟨max 2 qH,le_max_left _ _,fun q hq => hqH q ((le_max_right _ _).trans hq)⟩

end StrongThinTree.ShortcutNumeric

namespace StrongThinTree.MultiGraph.Hierarchy
open Matrix Finset ShortcutNumeric
open scoped Classical MatrixOrder
variable {n m : ℕ} {G : MultiGraph n m} {H : Hierarchy n}

lemma edgeConnected_of_locally {q : ℕ} (hconn : H.LocallyConnectedReal G q) : G.EdgeConnected q := by
  intro S hS hS'
  have hh := hconn univ H.root_mem S hS (Finset.ssubset_iff_subset_ne.mpr ⟨subset_univ _,hS'⟩)
  have heq : G.inducedEdges univ=univ := by ext e; simp [MultiGraph.inducedEdges]
  rw [heq] at hh
  exact_mod_cast hh

theorem polynomial_shortcut :
    ∃qH : ℕ, 2 ≤ qH ∧ ∀q : ℕ, qH ≤ q →
      ∀(n m : ℕ) (G : MultiGraph n m) (H : Hierarchy n),
      H.LocallyConnectedReal G q →
      ∀M : Finset (Finset (Fin n)), M ⊆ H.nodes →
      (∀t ∈ M, t ≠ univ) →
      (∀t ∈ M, ((G.cut univ t).card : ℝ)/q ≤ (H.parentBoundary G t).card) →
      ∃D : Matrix (Fin n) (Fin n) ℝ, D.PosDef ∧
        (∀S : Finset (Fin n), S.Nonempty → S ≠ univ →
          cutIndicator S ⬝ᵥ (D *ᵥ cutIndicator S) ≤ ((G.cut univ S).card : ℝ)) ∧
        (∀t ∈ M, ShortcutDual.boundaryAverage G.incidence (H.parentBoundary G) t D ≤
          (q:ℝ)^(-31/40:ℝ)) := by
  obtain ⟨qH,hqH,hgood⟩ := exists_cutoff
  refine ⟨qH,hqH,?_⟩
  intro q hq n m G H hconn M hM hroot hratio
  have hg := hgood q hq
  have hqpos : 0 < q := lt_of_lt_of_le (by omega : 0 < qH) hq
  have hqp : (0:ℝ) < q := Nat.cast_pos.mpr hqpos
  have hq1 : (1:ℝ) ≤ q := le_trans (by norm_num) hg.large
  have hα : 0 < alpha q := Real.rpow_pos_of_pos hqp _
  have hα1 : alpha q ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hq1 (by norm_num)
  have hρ : 0 < rho q := by dsimp [rho]; positivity
  have hr : ∀t ∈ M, (q:ℝ)*rho q*((G.cut univ t).card : ℝ) ≤ (H.parentBoundary G t).card := by
    intro t ht
    have heq : (q:ℝ)*rho q*((G.cut univ t).card : ℝ)=((G.cut univ t).card : ℝ)/q/2 := by
      unfold rho
      field_simp
    rw [heq]
    have hp : (0:ℝ) ≤ ((G.cut univ t).card : ℝ)/q := div_nonneg (Nat.cast_nonneg _) hqp.le
    exact (by linarith : ((G.cut univ t).card : ℝ)/q/2 ≤ ((G.cut univ t).card : ℝ)/q).trans (hratio t ht)
  have hη : 0 < (q:ℝ)^(-31/40:ℝ)/2 := by positivity
  obtain ⟨D,hD,hb,hc⟩ := exists_shortcut_explicit hqpos (count_pos hqp) (count_pos hqp)
    (edgeConnected_of_locally hconn) hconn M hM hroot hα hα1
    (by norm_num : (0:ℝ)<1/10) (by norm_num : (1/10:ℝ)<1/3)
    hρ hg.rho_small hg.small hg.assignment hr hg.log_left hg.log_right hη
  refine ⟨D,hD,fun S hS hS' => (hc S hS hS').le,?_⟩
  intro t ht
  have hh := hb t ht
  have hcoef : shortcutCoefficient q (count q) (count q) (alpha q) (1/10)=coefficient q := rfl
  rw [hcoef] at hh
  linarith [hg.coefficient_small]

end StrongThinTree.MultiGraph.Hierarchy

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.BasePacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uI uV uI2

section

noncomputable section
open Finset Submodule
namespace StrongThinTree.Packing

variable {E : Type uE} {I : Type uI} {V : Type uV} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
  [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

omit [Fintype E] [FiniteDimensional ℝ V] in
lemma span_insert (v : E → V) (s : Finset E) (e : E) :
    span v (insert e s) = Submodule.span ℝ (insert (v e) (v '' (s : Set E))) := by
  simp only [span, coe_insert, Set.image_insert_eq]

omit [Fintype E] [DecidableEq E] [FiniteDimensional ℝ V] in
lemma indep_rank (v : E → V) {s : Finset E} (hs : LinearIndepOn ℝ v s) :
    Module.finrank ℝ (span v s) = s.card := by
  have heq : Set.range (fun e : (s : Set E) => v e) = v '' (s : Set E) := by
    ext x; simp
  have h := finrank_span_eq_card hs.linearIndependent
  change Module.finrank ℝ (Submodule.span ℝ (Set.range (fun e : (s : Set E) => v e))) = _ at h
  rw [heq] at h
  simpa using h

omit [Fintype E] [FiniteDimensional ℝ V] in

lemma support_exchange (v : E → V) {s : Finset E}
    (hs : LinearIndepOn ℝ v s) {x : V} {l : E →₀ ℝ}
    (hl : l ∈ Finsupp.supported ℝ ℝ (s : Set E))
    (hx : Finsupp.linearCombination ℝ v l = x) {f : E} (hf : f ∈ l.support) :
    x ∉ span v (s.erase f) := by
  intro h
  obtain ⟨l', hl', hx'⟩ := (Finsupp.mem_span_image_iff_linearCombination ℝ).mp h
  have hl's : l' ∈ Finsupp.supported ℝ ℝ (s : Set E) := by
    rw [Finsupp.mem_supported] at hl' ⊢
    exact hl'.trans (Finset.erase_subset _ _)
  have heq : l = l' := (linearIndepOn_iffₛ.mp hs) l hl l' hl's (hx.trans hx'.symm)
  have hz : l' f = 0 := by
    apply Finsupp.notMem_support_iff.mp
    intro hmem
    have := ((Finsupp.mem_supported ℝ l').mp hl') hmem
    simp at this
  exact (Finsupp.mem_support_iff.mp hf) (heq ▸ hz)

omit [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] [FiniteDimensional ℝ V] in
lemma valid_empty (v : E → V) : Valid v (fun _ : I => ∅) := by
  constructor
  · intro i; simp
  · intro i j h; simp

omit [Fintype E] [DecidableEq E] [FiniteDimensional ℝ V] in
lemma valid_update {v : E → V} (F : State v I) (i : I) (s : Finset E)
    (hs : LinearIndepOn ℝ v (s : Set E))
    (hd : ∀ j, j ≠ i → Disjoint s (F.1 j)) : Valid v (Function.update F.1 i s) := by
  constructor
  · intro j
    by_cases h : j = i
    · subst j; simpa using hs
    · simpa [Function.update_of_ne h] using F.2.1 j
  · intro j k hjk
    by_cases hj : j = i
    · subst j
      simpa [Function.update_of_ne (Ne.symm hjk)] using hd k (Ne.symm hjk)
    · by_cases hk : k = i
      · subst k
        simpa [Function.update_of_ne hj] using (hd j hj).symm
      · simpa [Function.update_of_ne hj, Function.update_of_ne hk] using F.2.2 hjk

omit [Fintype E] [DecidableEq I] [FiniteDimensional ℝ V] in
lemma disjoint_insert_unused {v : E → V} (F : State v I) {i : I} {s : Finset E}
    (hs : s ⊆ F.1 i) {e : E} (he : unused F e) :
    ∀ j, j ≠ i → Disjoint (insert e s) (F.1 j) := by
  intro j hj
  rw [Finset.disjoint_insert_left]
  exact ⟨he j, (F.2.2 (Ne.symm hj)).mono_left hs⟩

omit [Fintype E] [DecidableEq E] [FiniteDimensional ℝ V] in
lemma cost_update {v : E → V} (F : State v I) {i : I} {s : Finset E}
    (h : Valid v (Function.update F.1 i s)) :
    cost (⟨Function.update F.1 i s, h⟩ : State v I) + (F.1 i).card = cost F + s.card := by
  unfold cost
  have hsum := Finset.sum_update_of_mem (Finset.mem_univ i) (fun j => (F.1 j).card) s.card
  have heq : (fun j => ((Function.update F.1 i s) j).card) =
      Function.update (fun j => (F.1 j).card) i s.card := by
    ext j; by_cases hj : j = i <;> simp [hj, Function.update_of_ne]
  rw [heq]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  rw [← Finset.sum_erase_add (Finset.univ : Finset I) _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  have he : ∑ j ∈ Finset.univ.erase i,
      Function.update (fun j => (F.1 j).card) i s.card j =
      ∑ j ∈ Finset.univ.erase i, (F.1 j).card := by
    apply Finset.sum_congr rfl
    intro j hj
    exact Function.update_of_ne (Finset.mem_erase.mp hj).1 _ _
  rw [he]
  omega

omit [DecidableEq E] [DecidableEq I] [FiniteDimensional ℝ V] in
lemma exists_maximal_state (v : E → V) :
    ∃ F : State v I, ∀ F' : State v I, cost F' ≤ cost F := by
  classical
  let : Fintype (State v I) := Fintype.ofFinite _
  have hne : (Finset.univ : Finset (State v I)).Nonempty :=
    ⟨⟨fun _ => ∅, valid_empty v⟩, Finset.mem_univ _⟩
  obtain ⟨F, _, hF⟩ := Finset.exists_max_image (Finset.univ : Finset (State v I)) cost hne
  exact ⟨F, fun F' => hF F' (Finset.mem_univ _)⟩

omit [Fintype E] [FiniteDimensional ℝ V] in
lemma maximal_unused_mem_span {v : E → V} {F : State v I}
    (hF : ∀ F' : State v I, cost F' ≤ cost F) {e : E} (he : unused F e) (i : I) :
    v e ∈ span v (F.1 i) := by
  by_contra h
  have hs : LinearIndepOn ℝ v (insert e (F.1 i) : Finset E) := by
    simpa only [Finset.coe_insert] using (F.2.1 i).insert h
  have hv := valid_update F i _ hs (disjoint_insert_unused F (Subset.refl _) he)
  have hc := cost_update F hv
  have hu := hF ⟨_, hv⟩
  rw [Finset.card_insert_of_notMem (he i)] at hc
  omega

omit [Fintype E] [FiniteDimensional ℝ V] in
lemma unused_after_exchange {v : E → V} {F F' : State v I} {i : I} {e f : E}
    (he : unused F e) (hf : f ∈ F.1 i)
    (h : F'.1 = Function.update F.1 i (insert e ((F.1 i).erase f))) : unused F' f := by
  intro j
  rw [h]
  by_cases hj : j = i
  · subst j
    have hfe : f ≠ e := by rintro rfl; exact he i hf
    simp [hfe]
  · rw [Function.update_of_ne hj]
    exact fun hfj => Finset.disjoint_left.mp (F.2.2 (Ne.symm hj)) hf hfj

omit [Fintype E] [FiniteDimensional ℝ V] in
lemma Move.cost_eq {v : E → V} {F F' : State v I} (h : Move F F') : cost F' = cost F := by
  obtain ⟨i, e, f, he, hf, heq⟩ := h
  have hv : Valid v (Function.update F.1 i (insert e ((F.1 i).erase f))) := heq ▸ F'.2
  have hc := cost_update F hv
  have hsame : (⟨_, hv⟩ : State v I) = F' := Subtype.ext heq.symm
  rw [hsame, Finset.card_insert_of_notMem (fun hh => he i (Finset.mem_erase.mp hh).2),
    Finset.card_erase_of_mem hf] at hc
  have hfpos := Finset.card_pos.mpr ⟨f, hf⟩
  omega

omit [Fintype E] [FiniteDimensional ℝ V] in
lemma reachable_cost_eq {v : E → V} {F F' : State v I}
    (h : Relation.ReflTransGen Move F F') : cost F' = cost F := by
  induction h with
  | refl => rfl
  | @tail F' F'' hr hm ih => exact hm.cost_eq.trans ih

omit [Fintype E] [FiniteDimensional ℝ V] in
lemma reachable_maximal {v : E → V} {F F' : State v I}
    (hF : ∀ G : State v I, cost G ≤ cost F)
    (h : Relation.ReflTransGen Move F F') : ∀ G : State v I, cost G ≤ cost F' := by
  intro G
  rw [reachable_cost_eq h]
  exact hF G

omit [FiniteDimensional ℝ V] in
lemma mem_recycled {v : E → V} {F : State v I} {e : E} :
    e ∈ recycled F ↔ ∃ F', Relation.ReflTransGen Move F F' ∧ unused F' e := by
  classical
  simp [recycled]

omit [FiniteDimensional ℝ V] in
lemma unused_span_recycled {v : E → V} {F F' : State v I}
    (hF : ∀ G : State v I, cost G ≤ cost F)
    (hr : Relation.ReflTransGen Move F F') {e : E} (he : unused F' e) (i : I) :
    v e ∈ span v (F'.1 i ∩ recycled F) := by
  have hsp := maximal_unused_mem_span (reachable_maximal hF hr) he i
  obtain ⟨l, hl, hle⟩ := (Finsupp.mem_span_image_iff_linearCombination ℝ).mp hsp
  apply (Finsupp.mem_span_image_iff_linearCombination ℝ).mpr
  refine ⟨l, ?_, hle⟩
  rw [Finsupp.mem_supported]
  intro f hf
  have hfi : f ∈ F'.1 i := (Finsupp.mem_supported ℝ l).mp hl hf
  refine Finset.mem_inter.mpr ⟨hfi, mem_recycled.mpr ?_⟩
  have hex := support_exchange v (F'.2.1 i) hl hle hf
  have hs : LinearIndepOn ℝ v (insert e ((F'.1 i).erase f) : Finset E) := by
    simpa only [Finset.coe_insert] using
      ((F'.2.1 i).mono (Finset.erase_subset _ _)).insert hex
  have hv := valid_update F' i _ hs
    (disjoint_insert_unused F' (Finset.erase_subset _ _) he)
  let F'' : State v I := ⟨_, hv⟩
  have hm : Move F' F'' := ⟨i, e, f, he, hfi, rfl⟩
  exact ⟨F'', hr.tail hm, unused_after_exchange he hfi rfl⟩

omit [FiniteDimensional ℝ V] in
lemma move_span_recycled_eq {v : E → V} {F F' F'' : State v I}
    (hF : ∀ G : State v I, cost G ≤ cost F)
    (hr : Relation.ReflTransGen Move F F') (hm : Move F' F'') (j : I) :
    span v (F''.1 j ∩ recycled F) = span v (F'.1 j ∩ recycled F) := by
  obtain ⟨i, e, f, he, hf, hup⟩ := hm
  by_cases hji : j = i
  · subst j
    have heU : v e ∈ span v (F'.1 i ∩ recycled F) := unused_span_recycled hF hr he i
    have hfU : v f ∈ span v (F''.1 i ∩ recycled F) :=
      unused_span_recycled hF (hr.tail ⟨i, e, f, he, hf, hup⟩)
        (unused_after_exchange he hf hup) i
    apply le_antisymm
    · apply (span_le_iff v).mpr
      intro g hg
      have hgU := (Finset.mem_inter.mp hg).2
      have hg' := (Finset.mem_inter.mp hg).1
      rw [hup, Function.update_self] at hg'
      rcases Finset.mem_insert.mp hg' with rfl | hg'
      · exact heU
      · exact mem_span_self v (Finset.mem_inter.mpr ⟨(Finset.mem_erase.mp hg').2, hgU⟩)
    · apply (span_le_iff v).mpr
      intro g hg
      by_cases hgf : g = f
      · subst g; exact hfU
      · apply mem_span_self v
        apply Finset.mem_inter.mpr
        refine ⟨?_, (Finset.mem_inter.mp hg).2⟩
        rw [hup, Function.update_self]
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hgf, (Finset.mem_inter.mp hg).1⟩)
  · rw [hup, Function.update_of_ne hji]

omit [FiniteDimensional ℝ V] in
lemma reachable_span_recycled_eq {v : E → V} {F F' : State v I}
    (hF : ∀ G : State v I, cost G ≤ cost F)
    (hr : Relation.ReflTransGen Move F F') (i : I) :
    span v (F'.1 i ∩ recycled F) = span v (F.1 i ∩ recycled F) := by
  induction hr with
  | refl => rfl
  | @tail F' F'' hr hm ih => exact (move_span_recycled_eq hF hr hm i).trans ih

omit [FiniteDimensional ℝ V] in

lemma span_recycled_eq {v : E → V} {F : State v I}
    (hF : ∀ G : State v I, cost G ≤ cost F) (i : I) :
    span v (recycled F) = span v (F.1 i ∩ recycled F) := by
  apply le_antisymm
  · apply (span_le_iff v).mpr
    intro e he
    obtain ⟨F', hr, he'⟩ := mem_recycled.mp he
    rw [← reachable_span_recycled_eq hF hr i]
    exact unused_span_recycled hF hr he' i
  · exact span_mono v Finset.inter_subset_right

omit [FiniteDimensional ℝ V] in
lemma cost_decomposition {v : E → V} {F : State v I}
    (hF : ∀ G : State v I, cost G ≤ cost F) :
    cost F = (Finset.univ \ recycled F).card +
      Fintype.card I * Module.finrank ℝ (span v (recycled F)) := by
  classical
  have hcover : Finset.univ \ recycled F =
      Finset.univ.biUnion (fun i => F.1 i \ recycled F) := by
    ext e
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · intro he
      have hused : ∃ i, e ∈ F.1 i := by
        by_contra h
        have hu : unused F e := by simpa only [unused, not_exists] using h
        exact he (mem_recycled.mpr ⟨F, Relation.ReflTransGen.refl, hu⟩)
      obtain ⟨i, hi⟩ := hused
      exact ⟨i, hi, he⟩
    · rintro ⟨i, hi, he⟩; exact he
  have hdisj : (↑(Finset.univ : Finset I) : Set I).PairwiseDisjoint
      (fun i => F.1 i \ recycled F) := by
    intro i _ j _ hij
    exact (F.2.2 hij).mono Finset.sdiff_subset Finset.sdiff_subset
  have hrank (i : I) : (F.1 i ∩ recycled F).card =
      Module.finrank ℝ (span v (recycled F)) := by
    rw [span_recycled_eq hF i]
    exact (indep_rank v ((F.2.1 i).mono Finset.inter_subset_left)).symm
  rw [hcover, Finset.card_biUnion hdisj]
  calc
    cost F = ∑ i, ((F.1 i \ recycled F).card + (F.1 i ∩ recycled F).card) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (Finset.card_sdiff_add_card_inter _ _).symm
    _ = (∑ i, (F.1 i \ recycled F).card) +
        Fintype.card I * Module.finrank ℝ (span v (recycled F)) := by
      simp_rw [hrank, Finset.sum_add_distrib]
      simp

theorem vector_base_packing (v : E → V)
    (hcut : ∀ U : Finset E,
      Fintype.card I * Module.finrank ℝ (span v Finset.univ) ≤
        (Finset.univ \ U).card + Fintype.card I * Module.finrank ℝ (span v U)) :
    ∃ F : State v I, ∀ i, span v (F.1 i) = span v Finset.univ := by
  obtain ⟨F, hF⟩ := exists_maximal_state (I := I) v
  have hle (i : I) : (F.1 i).card ≤ Module.finrank ℝ (span v Finset.univ) := by
    rw [← indep_rank v (F.2.1 i)]
    exact Submodule.finrank_mono (span_mono v (Finset.subset_univ _))
  have htotal : cost F = Fintype.card I * Module.finrank ℝ (span v Finset.univ) := by
    apply le_antisymm
    · calc
        cost F ≤ ∑ _i : I, Module.finrank ℝ (span v Finset.univ) :=
          Finset.sum_le_sum fun i _ => hle i
        _ = _ := by simp
    · rw [cost_decomposition hF]
      exact hcut (recycled F)
  have hcards (i : I) : (F.1 i).card = Module.finrank ℝ (span v Finset.univ) := by
    apply (Finset.sum_eq_sum_iff_of_le (fun i (_ : i ∈ (Finset.univ : Finset I)) => hle i)).mp ?_ i
      (Finset.mem_univ i)
    simpa [cost] using htotal
  refine ⟨F, fun i => ?_⟩
  apply Submodule.eq_of_le_of_finrank_eq (span_mono v (Finset.subset_univ _))
  rw [indep_rank v (F.2.1 i), hcards]

omit [Fintype E] [FiniteDimensional ℝ V] in
lemma masked_span (v : E → V) (T U : Finset E) :
    span (fun e => if e ∈ T then v e else 0) U = span v (U ∩ T) := by
  classical
  apply le_antisymm
  · apply (span_le_iff _).mpr
    intro e he
    by_cases heT : e ∈ T
    · simp only [ite_eq_left heT]
      exact mem_span_self v (Finset.mem_inter.mpr ⟨he, heT⟩)
    · simp [heT]
  · apply (span_le_iff _).mpr
    intro e he
    have hm := mem_span_self (fun e => if e ∈ T then v e else 0) (Finset.mem_inter.mp he).1
    simpa only [ite_eq_left (Finset.mem_inter.mp he).2] using hm

theorem vector_base_packing_on (v : E → V) (T : Finset E)
    (hcut : ∀ U : Finset E, U ⊆ T →
      Fintype.card I * Module.finrank ℝ (span v T) ≤
        (T \ U).card + Fintype.card I * Module.finrank ℝ (span v U)) :
    ∃ F : I → Finset E, Valid v F ∧ ∀ i, F i ⊆ T ∧ span v (F i) = span v T := by
  classical
  let w : E → V := fun e => if e ∈ T then v e else 0
  have hcrit : ∀ U : Finset E, Fintype.card I * Module.finrank ℝ (span w Finset.univ) ≤
      (Finset.univ \ U).card + Fintype.card I * Module.finrank ℝ (span w U) := by
    intro U
    have hw (A : Finset E) : span w A = span v (A ∩ T) := masked_span v T A
    rw [hw, hw, Finset.univ_inter]
    have h := hcut (U ∩ T) Finset.inter_subset_right
    apply h.trans
    apply Nat.add_le_add_right
    apply Finset.card_le_card
    intro e he
    simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_univ, true_and] at he ⊢
    tauto
  obtain ⟨F, hF⟩ := vector_base_packing (I := I) w hcrit
  have hsub (i : I) : F.1 i ⊆ T := by
    intro e he
    have hz := (F.2.1 i).ne_zero he
    by_contra h
    exact hz (by simp [w, h])
  refine ⟨F.1, ⟨?_, F.2.2⟩, fun i => ⟨hsub i, ?_⟩⟩
  · intro i
    apply (F.2.1 i).congr
    intro e he
    simp [w, hsub i he]
  · have heq := hF i
    simpa only [w, masked_span, Finset.inter_eq_left.mpr (hsub i), Finset.univ_inter] using heq

end StrongThinTree.Packing

namespace StrongThinTree.MultiGraph
variable {n m : ℕ} (G : MultiGraph n m)

lemma rep_same (T : Finset (Fin m)) (u : Fin n) : G.Same T (G.rep T u) u :=
  Quotient.mk_out (s := G.components T) u

lemma rep_eq_iff (T : Finset (Fin m)) (u v : Fin n) : G.rep T u = G.rep T v ↔ G.Same T u v := by
  constructor
  · intro h
    exact G.same_trans (G.same_symm (G.rep_same T u)) (h ▸ G.rep_same T v)
  · intro h
    exact congrArg Quotient.out (Quotient.sound h)

lemma rep_idempotent (T : Finset (Fin m)) (u : Fin n) : G.rep T (G.rep T u) = G.rep T u :=
  (G.rep_eq_iff T _ _).mpr (G.rep_same T u)

lemma same_endpoints {T : Finset (Fin m)} {e : Fin m} (he : e ∈ T) :
    G.Same T (G.left e) (G.right e) := Packing.mem_span_self G.incidence he

lemma rep_endpoints {T : Finset (Fin m)} {e : Fin m} (he : e ∈ T) :
    G.rep T (G.left e) = G.rep T (G.right e) :=
  (G.rep_eq_iff T _ _).mpr (G.same_endpoints he)

lemma repDifference_mem (T : Finset (Fin m)) (u : Fin n) : G.repDifference T u ∈ G.edgeSpan T :=
  G.same_symm (G.rep_same T u)

lemma repDifference_independent (T : Finset (Fin m)) :
    LinearIndependent ℝ (fun u : {u : Fin n // G.rep T u ≠ u} => G.repDifference T u) := by
  apply LinearIndependent.of_pairwise_dual_eq_zero_one _ (fun u => LinearMap.proj u.1)
  · intro u v huv
    have huv' : u.1 ≠ v.1 := fun h => huv (Subtype.ext h)
    have hru : u.1 ≠ G.rep T v.1 := by
      intro h
      have := G.rep_idempotent T v.1
      rw [← h] at this
      exact u.2 this
    simp [repDifference, point, huv', hru]
  · intro u
    simp [repDifference, point, (Ne.symm u.2)]

lemma edgeSpan_eq_repSpan (T : Finset (Fin m)) :
    G.edgeSpan T = Submodule.span ℝ
      (Set.range (fun u : {u : Fin n // G.rep T u ≠ u} => G.repDifference T u)) := by
  classical
  apply le_antisymm
  · apply (Packing.span_le_iff G.incidence).mpr
    intro e he
    have hdiff (u : Fin n) : G.repDifference T u ∈ Submodule.span ℝ
        (Set.range (fun u : {u : Fin n // G.rep T u ≠ u} => G.repDifference T u)) := by
      by_cases hu : G.rep T u = u
      · simp [repDifference, hu]
      · exact Submodule.subset_span ⟨⟨u, hu⟩, rfl⟩
    have h := (Submodule.span ℝ _).sub_mem (hdiff (G.left e)) (hdiff (G.right e))
    have heq : G.repDifference T (G.left e) - G.repDifference T (G.right e) = G.incidence e := by
      dsimp [repDifference, incidence]
      rw [G.rep_endpoints he]
      abel
    rwa [heq] at h
  · apply Submodule.span_le.mpr
    rintro x ⟨u, rfl⟩
    exact G.repDifference_mem T u

theorem incidence_rank (T : Finset (Fin m)) :
    Module.finrank ℝ (G.edgeSpan T) = n - G.componentCount T := by
  classical
  rw [G.edgeSpan_eq_repSpan, finrank_span_eq_card (G.repDifference_independent T),
    Fintype.card_subtype_compl]
  have heq : Finset.univ.image (G.rep T) = Finset.univ.filter (fun u => G.rep T u = u) := by
    ext u
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨v, rfl⟩
      exact G.rep_idempotent T v
    · intro hu
      exact ⟨u, hu⟩
  simp only [componentCount, heq, Fintype.card_fin, Fintype.card_subtype]

lemma sumOn_point (S : Finset (Fin n)) (v : Fin n) :
    (∑ u ∈ S, LinearMap.proj u : (Fin n → ℝ) →ₗ[ℝ] ℝ) (point v) =
      if v ∈ S then 1 else 0 := by
  simp [LinearMap.sum_apply, point, Pi.single_apply, Finset.sum_ite_eq']

theorem connected_iff_same (T : Finset (Fin m)) :
    G.Connected T ↔ ∀ u v, G.Same T u v := by
  classical
  constructor
  · intro hconn u v
    by_contra huv
    let S := Finset.univ.filter (fun w => G.Same T w v)
    have hS : S.Nonempty := ⟨v, by simp [S, G.same_refl]⟩
    have hSne : S ≠ Finset.univ := by
      intro heq
      have hu : u ∈ S := heq ▸ Finset.mem_univ u
      exact huv (by simpa [S] using hu)
    obtain ⟨e, he⟩ := hconn S hS hSne
    obtain ⟨heT, hecut⟩ := Finset.mem_filter.mp he
    rcases hecut with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · have hl' : G.Same T (G.left e) v := by simpa [S] using hl
      have hr' := G.same_trans (G.same_symm (G.same_endpoints heT)) hl'
      exact hr (by simpa [S] using hr')
    · have hr' : G.Same T (G.right e) v := by simpa [S] using hr
      have hl' := G.same_trans (G.same_endpoints heT) hr'
      exact hl (by simpa [S] using hl')
  · intro hsame S hS hSne
    by_contra hcut
    have hempty : G.cut T S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hcut
    let f : (Fin n → ℝ) →ₗ[ℝ] ℝ := ∑ u ∈ S, LinearMap.proj u
    have hker : G.edgeSpan T ≤ LinearMap.ker f := by
      apply (Packing.span_le_iff G.incidence).mpr
      intro e he
      have hiff : G.left e ∈ S ↔ G.right e ∈ S := by
        have h : ¬ ((G.left e ∈ S ∧ G.right e ∉ S) ∨
            (G.right e ∈ S ∧ G.left e ∉ S)) := by
          intro hc
          have : e ∈ G.cut T S := Finset.mem_filter.mpr ⟨he, hc⟩
          simp [hempty] at this
        tauto
      change f (G.incidence e) = 0
      rw [incidence, map_sub]
      change (∑ u ∈ S, LinearMap.proj u : (Fin n → ℝ) →ₗ[ℝ] ℝ) (point (G.left e)) -
        (∑ u ∈ S, LinearMap.proj u : (Fin n → ℝ) →ₗ[ℝ] ℝ) (point (G.right e)) = 0
      simp only [sumOn_point]
      simp only [hiff, sub_self]
    obtain ⟨u, hu⟩ := hS
    have hv : ∃ v, v ∉ S := by
      by_contra h
      push Not at h
      exact hSne (Finset.eq_univ_of_forall h)
    obtain ⟨v, hv⟩ := hv
    have hz := hker (hsame u v)
    change f (point u - point v) = 0 at hz
    rw [map_sub] at hz
    change (∑ w ∈ S, LinearMap.proj w : (Fin n → ℝ) →ₗ[ℝ] ℝ) (point u) -
      (∑ w ∈ S, LinearMap.proj w : (Fin n → ℝ) →ₗ[ℝ] ℝ) (point v) = 0 at hz
    simp [sumOn_point, hu, hv] at hz

lemma connected_of_span_eq {T U : Finset (Fin m)}
    (h : G.edgeSpan T = G.edgeSpan U) (hT : G.Connected T) : G.Connected U := by
  rw [G.connected_iff_same] at hT ⊢
  intro u v
  change point u - point v ∈ G.edgeSpan U
  rw [← h]
  exact hT u v

theorem spanningTree_iff_independent (T : Finset (Fin m)) :
    G.SpanningTree T ↔ G.Connected T ∧ LinearIndepOn ℝ G.incidence (T : Set (Fin m)) := by
  constructor
  · rintro ⟨hconn, hmin⟩
    refine ⟨hconn, linearIndepOn_iff_notMem_span.mpr ?_⟩
    intro e he hdep
    have hd : G.incidence e ∈ G.edgeSpan (T.erase e) := by
      simpa only [edgeSpan, Packing.span, Finset.coe_erase] using hdep
    have heq : G.edgeSpan T = G.edgeSpan (T.erase e) := by
      calc
        G.edgeSpan T = G.edgeSpan (insert e (T.erase e)) := by rw [Finset.insert_erase he]
        _ = G.edgeSpan (T.erase e) := by
          change Packing.span G.incidence (insert e (T.erase e)) = _
          rw [Packing.span_insert, Submodule.span_insert_eq_span hd]
    exact hmin e he (G.connected_of_span_eq heq hconn)
  · rintro ⟨hconn, hind⟩
    refine ⟨hconn, fun e he hdel => ?_⟩
    have hnot := linearIndepOn_iff_notMem_span.mp hind e he
    apply hnot
    have hsame := (G.connected_iff_same (T.erase e)).mp hdel (G.left e) (G.right e)
    simpa only [Same, incidence, edgeSpan, Packing.span, Finset.coe_erase] using hsame

lemma componentCount_pos (hn : 0 < n) (T : Finset (Fin m)) : 0 < G.componentCount T := by
  apply Finset.card_pos.mpr
  exact ⟨G.rep T ⟨0, hn⟩, Finset.mem_image.mpr ⟨⟨0, hn⟩, Finset.mem_univ _, rfl⟩⟩

lemma componentCount_le (T : Finset (Fin m)) : G.componentCount T ≤ n := by
  exact (Finset.card_image_le).trans_eq (Finset.card_univ.trans (Fintype.card_fin n))

lemma connected_componentCount {T : Finset (Fin m)} (hn : 0 < n) (hc : G.Connected T) :
    G.componentCount T = 1 := by
  apply Finset.card_eq_one.mpr
  let u : Fin n := ⟨0, hn⟩
  refine ⟨G.rep T u, ?_⟩
  ext v
  constructor
  · intro hv
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_singleton.mpr ((G.rep_eq_iff T w u).mpr ((G.connected_iff_same T).mp hc w u))
  · intro hv
    have hv' := Finset.mem_singleton.mp hv
    subst v
    exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩

lemma connected_rank {T : Finset (Fin m)} (hn : 0 < n) (hc : G.Connected T) :
    Module.finrank ℝ (G.edgeSpan T) = n - 1 := by
  rw [G.incidence_rank, G.connected_componentCount hn hc]

lemma spanningTree_card {T : Finset (Fin m)} (hn : 0 < n) (hT : G.SpanningTree T) : T.card = n - 1 := by
  rw [← Packing.indep_rank G.incidence ((G.spanningTree_iff_independent T).mp hT).2]
  exact G.connected_rank hn hT.1

lemma connected_of_componentCount_eq_one {T : Finset (Fin m)}
    (hc : G.componentCount T = 1) : G.Connected T := by
  rw [G.connected_iff_same]
  have ⟨v, hv⟩ := Finset.card_eq_one.mp hc
  intro a b
  have ha : G.rep T a ∈ Finset.univ.image (G.rep T) :=
    Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
  have hb : G.rep T b ∈ Finset.univ.image (G.rep T) :=
    Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩
  rw [hv, Finset.mem_singleton] at ha hb
  exact (G.rep_eq_iff T a b).mp (ha.trans hb.symm)

lemma crossing_components_subset (T U : Finset (Fin m)) :
    G.crossing T (G.rep U) ⊆ T \ U := by
  intro e he
  obtain ⟨heT, hec⟩ := Finset.mem_filter.mp he
  exact Finset.mem_sdiff.mpr ⟨heT, fun heU => hec (G.rep_endpoints heU)⟩

lemma crossing_components_self (T : Finset (Fin m)) : G.crossing T (G.rep T) = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro e he
  have := G.crossing_components_subset T T he
  simp at this

theorem partition_criterion_sufficient (T : Finset (Fin m)) {r : ℕ} (hr : 0 < r) (hn : 0 < n)
    (hp : ∀ p : Fin n → Fin n, r * (partitionSize p - 1) ≤ (G.crossing T p).card) :
    G.TreePackable T r := by
  have hc : G.Connected T := by
    have h := hp (G.rep T)
    rw [G.crossing_components_self, Finset.card_empty] at h
    change r * (G.componentCount T - 1) ≤ 0 at h
    have hpos := G.componentCount_pos hn T
    have hz : G.componentCount T - 1 = 0 := by nlinarith
    exact G.connected_of_componentCount_eq_one (by omega)
  have hcrit : ∀ U : Finset (Fin m), U ⊆ T →
      Fintype.card (Fin r) * Module.finrank ℝ (Packing.span G.incidence T) ≤
        (T \ U).card + Fintype.card (Fin r) * Module.finrank ℝ (Packing.span G.incidence U) := by
    intro U hUT
    change Fintype.card (Fin r) * Module.finrank ℝ (G.edgeSpan T) ≤
      (T \ U).card + Fintype.card (Fin r) * Module.finrank ℝ (G.edgeSpan U)
    rw [Fintype.card_fin, G.connected_rank hn hc, G.incidence_rank]
    have hpart := hp (G.rep U)
    have hcross := Finset.card_le_card (G.crossing_components_subset T U)
    have hcp := G.componentCount_pos hn U
    have hcle := G.componentCount_le U
    change r * (G.componentCount U - 1) ≤ (G.crossing T (G.rep U)).card at hpart
    have hnid : n - 1 = (G.componentCount U - 1) + (n - G.componentCount U) := by omega
    rw [hnid, Nat.mul_add]
    exact Nat.add_le_add_right (hpart.trans hcross) _
  obtain ⟨F, hv, hF⟩ := Packing.vector_base_packing_on G.incidence T hcrit
  refine ⟨F, fun i => ?_, hv.2⟩
  refine ⟨(hF i).1, (G.spanningTree_iff_independent (F i)).mpr ⟨?_, hv.1 i⟩⟩
  exact G.connected_of_span_eq (hF i).2.symm hc

lemma sum_partition_cuts (T : Finset (Fin m)) (p : Fin n → Fin n) :
    (∑ c ∈ Finset.univ.image p, (G.cut T (Finset.univ.filter (p · = c))).card) =
      2 * (G.crossing T p).card := by
  classical
  simp only [cut, crossing, Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Finset.sum_comm]
  calc
    _ = ∑ e ∈ T, if p (G.left e) ≠ p (G.right e) then 2 else 0 := by
      apply Finset.sum_congr rfl
      intro e he
      by_cases h : p (G.left e) = p (G.right e)
      · simp [h]
      · rw [ite_eq_left h]
        have hl : p (G.left e) ∈ Finset.univ.image p := Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
        have hr : p (G.right e) ∈ Finset.univ.image p := Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
        rw [Finset.sum_eq_add (p (G.left e)) (p (G.right e)) h]
        · simp [h, Ne.symm h]
        · intro c hc hh
          simp [Ne.symm hh.1, Ne.symm hh.2]
        · exact fun hh => (hh hl).elim
        · exact fun hh => (hh hr).elim
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; split_ifs <;> omega

lemma partition_fiber_proper (p : Fin n → Fin n) (hp : 1 < partitionSize p) (c : Fin n) :
    Finset.univ.filter (p · = c) ≠ Finset.univ := by
  intro h
  have him : Finset.univ.image p ⊆ {c} := by
    intro d hd
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hd
    have hv' : v ∈ Finset.univ.filter (p · = c) := by rw [h]; exact Finset.mem_univ v
    simpa using hv'
  have : partitionSize p ≤ 1 := by simpa [partitionSize] using Finset.card_le_card him
  omega

theorem edgeConnected_treePackable {r : ℕ} (hr : 0 < r) (hn : 0 < n)
    (hc : G.EdgeConnected (2 * r)) : G.TreePackable Finset.univ r := by
  apply G.partition_criterion_sufficient _ hr hn
  intro p
  by_cases hp : partitionSize p ≤ 1
  · have : partitionSize p - 1 = 0 := by omega
    simp [this]
  have hp' : 1 < partitionSize p := by omega
  have hsum : (∑ c ∈ Finset.univ.image p, 2 * r) ≤
      ∑ c ∈ Finset.univ.image p, (G.cut Finset.univ (Finset.univ.filter (p · = c))).card := by
    apply Finset.sum_le_sum
    intro c hc'
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hc'
    exact hc _ ⟨v, by simp⟩ (partition_fiber_proper p hp' _)
  rw [G.sum_partition_cuts] at hsum
  simp only [Finset.sum_const, smul_eq_mul] at hsum
  change partitionSize p * (2 * r) ≤ _ at hsum
  have : r * partitionSize p ≤ (G.crossing Finset.univ p).card := by linarith
  exact (Nat.mul_le_mul_left r (Nat.sub_le _ _)).trans this

lemma same_preserves_label {U : Finset (Fin m)} {p : Fin n → Fin n}
    (hp : ∀ e ∈ U, p (G.left e) = p (G.right e)) {u v : Fin n}
    (huv : G.Same U u v) : p u = p v := by
  classical
  by_contra h
  let S := Finset.univ.filter (fun w => p w = p u)
  let f : (Fin n → ℝ) →ₗ[ℝ] ℝ := ∑ w ∈ S, LinearMap.proj w
  have hker : G.edgeSpan U ≤ LinearMap.ker f := by
    apply (Packing.span_le_iff G.incidence).mpr
    intro e he
    change f (G.incidence e) = 0
    rw [incidence, map_sub]
    change (∑ w ∈ S, LinearMap.proj w : (Fin n → ℝ) →ₗ[ℝ] ℝ) (point (G.left e)) -
      (∑ w ∈ S, LinearMap.proj w : (Fin n → ℝ) →ₗ[ℝ] ℝ) (point (G.right e)) = 0
    simp [sumOn_point, S, hp e he]
  have hz := hker huv
  change f (point u - point v) = 0 at hz
  rw [map_sub] at hz
  change (∑ w ∈ S, LinearMap.proj w : (Fin n → ℝ) →ₗ[ℝ] ℝ) (point u) -
    (∑ w ∈ S, LinearMap.proj w : (Fin n → ℝ) →ₗ[ℝ] ℝ) (point v) = 0 at hz
  simp [sumOn_point, S, Ne.symm h] at hz

lemma partitionSize_le_components {U : Finset (Fin m)} {p : Fin n → Fin n}
    (hp : ∀ e ∈ U, p (G.left e) = p (G.right e)) :
    partitionSize p ≤ G.componentCount U := by
  apply Finset.card_le_card_of_surjOn p
  intro c hc
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hc
  exact ⟨G.rep U v, Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩,
    G.same_preserves_label hp (G.rep_same U v)⟩

lemma spanningTree_crossing {T : Finset (Fin m)} (hn : 0 < n)
    (hT : G.SpanningTree T) (p : Fin n → Fin n) :
    partitionSize p - 1 ≤ (G.crossing T p).card := by
  classical
  let U := T \ G.crossing T p
  have hUT : U ⊆ T := Finset.sdiff_subset
  have hUi := ((G.spanningTree_iff_independent T).mp hT).2.mono hUT
  have hrank := Packing.indep_rank G.incidence hUi
  change Module.finrank ℝ (G.edgeSpan U) = U.card at hrank
  rw [G.incidence_rank] at hrank
  have hc := G.partitionSize_le_components (U := U) (p := p) (by
    intro e he
    obtain ⟨heT, hec⟩ := Finset.mem_sdiff.mp he
    by_contra h
    exact hec (Finset.mem_filter.mpr ⟨heT, h⟩))
  have hcard : U.card + (G.crossing T p).card = T.card :=
    Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)
  rw [G.spanningTree_card hn hT] at hcard
  have hle := G.componentCount_le U
  omega

theorem partition_criterion_necessary {T : Finset (Fin m)} {r : ℕ} (hn : 0 < n)
    (hpack : G.TreePackable T r) (p : Fin n → Fin n) :
    r * (partitionSize p - 1) ≤ (G.crossing T p).card := by
  classical
  obtain ⟨F, hF, hd⟩ := hpack
  have hdis : (↑(Finset.univ : Finset (Fin r)) : Set (Fin r)).PairwiseDisjoint
      (fun i => G.crossing (F i) p) := by
    intro i hi j hj hij
    exact Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
      (Finset.disjoint_of_subset_right (Finset.filter_subset _ _) (hd hij))
  have hsub : Finset.univ.biUnion (fun i => G.crossing (F i) p) ⊆ G.crossing T p := by
    apply Finset.biUnion_subset.mpr
    intro i hi
    exact Finset.filter_subset_filter _ (hF i).1
  have hc := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdis] at hc
  have ht : (∑ i : Fin r, (partitionSize p - 1)) ≤
      ∑ i : Fin r, (G.crossing (F i) p).card :=
    Finset.sum_le_sum (fun i hi => G.spanningTree_crossing hn (hF i).2 p)
  simpa using ht.trans hc

end StrongThinTree.MultiGraph

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.PartitionRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uI uV uE2 uV2

section

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset Submodule
variable {n m : ℕ} (G : MultiGraph n m)

lemma independent_spanning_subset (F : Finset (Fin m)) :
    ∃ T ⊆ F, LinearIndepOn ℝ G.incidence (T : Set (Fin m)) ∧ G.edgeSpan T = G.edgeSpan F := by
  classical
  let h : LinearIndepOn ℝ G.incidence (∅ : Set (Fin m)) := linearIndepOn_empty ℝ G.incidence
  let U := h.extend (Set.empty_subset (F : Set (Fin m)))
  refine ⟨U.toFinset, ?_, ?_, ?_⟩
  · intro e he
    exact h.extend_subset (Set.empty_subset (F : Set (Fin m))) (Set.mem_toFinset.mp he)
  · simpa only [Set.coe_toFinset] using h.linearIndepOn_extend (Set.empty_subset (F : Set (Fin m)))
  · simpa only [edgeSpan, Packing.span, Set.coe_toFinset] using
      h.span_image_extend_eq_span_image (Set.empty_subset (F : Set (Fin m)))

lemma packableOn_iff_trees (F : Finset (Fin m)) (q : ℕ) (A : Finset (Fin n)) :
    G.PackableOn F q A ↔ ∃ T : Fin q → Finset (Fin m),
      (∀ i, T i ⊆ F ∧ G.TreeOn A (T i)) ∧
      ∀ ⦃i j⦄, i ≠ j → Disjoint (T i) (T j) := by
  classical
  constructor
  · rintro ⟨T, hT, hd⟩
    choose U hU hi hs using fun i => G.independent_spanning_subset (T i)
    refine ⟨U, fun i => ⟨?_, ?_, ?_, hi i⟩, fun i j hij =>
      disjoint_of_subset_left (hU i) (disjoint_of_subset_right (hU j) (hd hij))⟩
    · exact (hU i).trans ((hT i).1.trans (filter_subset _ _))
    · intro e he
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp ((hT i).1 (hU i he))).2⟩
    · exact G.connectedOn_mono_span (le_of_eq (hs i).symm) (hT i).2
  · rintro ⟨T, hT, hd⟩
    refine ⟨T, fun i => ⟨?_, (hT i).2.2.1⟩, hd⟩
    intro e he
    exact mem_filter.mpr ⟨(hT i).1 he, (mem_filter.mp ((hT i).2.1 he)).2⟩

lemma maxPackable_contains {F : Finset (Fin m)} {q : ℕ} {A B : Finset (Fin n)}
    (hA : G.MaxPackable F q A) (hB : G.PackableOn F q B) (hAB : (A ∩ B).Nonempty) : B ⊆ A := by
  have heq := hA.2.2 _ subset_union_left (G.packableOn_union hA.2.1 hB hAB)
  exact heq ▸ subset_union_right

lemma connectedOn_univ (T : Finset (Fin m)) : G.ConnectedOn univ T ↔ G.Connected T := by
  rw [G.connected_iff_same]
  simp only [ConnectedOn, mem_univ, forall_const]

lemma packableOn_univ (F : Finset (Fin m)) (q : ℕ) :
    G.PackableOn F q univ ↔ G.TreePackable F q := by
  rw [G.packableOn_iff_trees]
  constructor
  · rintro ⟨T, hT, hd⟩
    refine ⟨T, fun i => ⟨(hT i).1, ?_⟩, hd⟩
    exact (G.spanningTree_iff_independent _).mpr
      ⟨(G.connectedOn_univ _).mp (hT i).2.2.1, (hT i).2.2.2⟩
  · rintro ⟨T, hT, hd⟩
    refine ⟨T, fun i => ⟨(hT i).1, ?_, ?_, ?_⟩, hd⟩
    · simp [internal]
    · exact (G.connectedOn_univ _).mpr (hT i).2.1
    · exact ((G.spanningTree_iff_independent _).mp (hT i).2).2

lemma vertexProjection_point (A : Finset (Fin n)) (u : Fin n) :
    vertexProjection A (point u) = if u ∈ A then point u else 0 := by
  ext v
  by_cases hu : u ∈ A <;> by_cases hv : v ∈ A <;> by_cases h : v = u <;>
    simp_all [vertexProjection, point]

lemma restrict_span {F : Finset (Fin m)} {A : Finset (Fin n)}
    (h : ∀ e ∈ F, G.left e ∈ A ↔ G.right e ∈ A) {x : Fin n → ℝ}
    (hx : x ∈ G.edgeSpan F) : vertexProjection A x ∈ G.edgeSpan (G.internal F A) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨e, he, rfl⟩ := hx
    have he' : e ∈ F := he
    rw [incidence, map_sub, vertexProjection_point, vertexProjection_point]
    by_cases hl : G.left e ∈ A
    · simp only [ite_eq_left hl, ite_eq_left ((h e he').mp hl)]
      exact Packing.mem_span_self G.incidence (mem_filter.mpr ⟨he', hl, (h e he').mp hl⟩)
    · simp [hl, not_congr (h e he') |>.mp hl]
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using add_mem ihx ihy
  | smul c x hx ih => simpa only [map_smul] using smul_mem _ c ih

lemma restrict_same {F : Finset (Fin m)} {A : Finset (Fin n)}
    (h : ∀ e ∈ F, G.left e ∈ A ↔ G.right e ∈ A) {u v : Fin n}
    (hu : u ∈ A) (hv : v ∈ A) (hs : G.Same F u v) : G.Same (G.internal F A) u v := by
  have hp := G.restrict_span h hs
  change point u - point v ∈ G.edgeSpan (G.internal F A)
  simpa only [map_sub, vertexProjection_point, ite_eq_left hu, ite_eq_left hv] using hp

end
end StrongThinTree.MultiGraph

namespace StrongThinTree.Packing
noncomputable section
open Finset Submodule
variable {E : Type uE} {I : Type uI} {V : Type uV} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
  [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in

theorem packing_certificate_on (v : E → V) (T : Finset E) :
    ∃ (F : I → Finset E) (U : Finset E), Valid v F ∧
      (∀ i, F i ⊆ T) ∧ U ⊆ T ∧
      (∀ i, span v U = span v (F i ∩ U)) ∧
      (∑ i, (F i).card) = (T \ U).card + Fintype.card I * Module.finrank ℝ (span v U) := by
  classical
  let w : E → V := fun e => if e ∈ T then v e else 0
  obtain ⟨F, hF⟩ := exists_maximal_state (I := I) w
  have hsub (i : I) : F.1 i ⊆ T := by
    intro e he
    have hz := (F.2.1 i).ne_zero he
    by_contra h
    exact hz (by simp [w, h])
  let U := recycled F ∩ T
  have hout {e : E} (he : e ∉ T) : e ∈ recycled F := by
    apply mem_recycled.mpr
    refine ⟨F, Relation.ReflTransGen.refl, ?_⟩
    intro i hi
    exact he (hsub i hi)
  have hdiff : univ \ recycled F = T \ U := by
    ext e
    simp only [mem_sdiff, mem_univ, true_and, U, mem_inter]
    constructor
    · intro h; exact ⟨by_contra (fun he => h (hout he)), fun he => h he.1⟩
    · rintro ⟨hT, h⟩ hr; exact h ⟨hr, hT⟩
  refine ⟨F.1, U, ⟨?_, F.2.2⟩, hsub, inter_subset_right, ?_, ?_⟩
  · intro i
    apply (F.2.1 i).congr
    intro e he; simp [w, hsub i he]
  · intro i
    have hs := span_recycled_eq hF i
    change span v (recycled F ∩ T) = span v (F.1 i ∩ (recycled F ∩ T))
    rw [← inter_assoc]
    simpa only [w, masked_span] using hs
  · have hc := cost_decomposition hF
    rw [hdiff] at hc
    change cost F = (T \ U).card + Fintype.card I *
      Module.finrank ℝ (span (fun e => if e ∈ T then v e else 0) (recycled F)) at hc
    rw [masked_span] at hc
    exact hc

end
end StrongThinTree.Packing

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset Submodule
variable {n m : ℕ} (G : MultiGraph n m)

lemma component_packable_of_certificate {F U : Finset (Fin m)} {q : ℕ}
    {T : Fin q → Finset (Fin m)} (hT : ∀ i, T i ⊆ F)
    (hd : ∀ ⦃i j⦄, i ≠ j → Disjoint (T i) (T j))
    (hs : ∀ i, G.edgeSpan U = G.edgeSpan (T i ∩ U)) (v : Fin n) :
    G.PackableOn F q (univ.filter (fun w => G.rep U w = G.rep U v)) := by
  let A := univ.filter (fun w => G.rep U w = G.rep U v)
  refine ⟨fun i => G.internal (T i ∩ U) A, fun i => ⟨?_, ?_⟩, ?_⟩
  · exact filter_subset_filter _ (inter_subset_left.trans (hT i))
  · intro u hu w hw
    have hu' : G.rep U u = G.rep U v := (mem_filter.mp hu).2
    have hw' : G.rep U w = G.rep U v := (mem_filter.mp hw).2
    have hh : G.Same (T i ∩ U) u w := by
      rw [Same, ← hs i]
      exact (G.rep_eq_iff U u w).mp (hu'.trans hw'.symm)
    refine G.restrict_same ?_ hu hw hh
    intro e he
    simp only [A, mem_filter, mem_univ, true_and, G.rep_endpoints (mem_inter.mp he).2]
  · intro i j hij
    exact disjoint_of_subset_left (filter_subset _ _ |>.trans inter_subset_left)
      (disjoint_of_subset_right (filter_subset _ _ |>.trans inter_subset_left) (hd hij))

lemma partOf_eq_iff (F : Finset (Fin m)) (q : ℕ) (u v : Fin n) :
    G.partOf F q u = G.partOf F q v ↔ u ∈ G.partOf F q v := by
  constructor
  · intro h; rw [← h]; exact (G.partOf_spec F q u).1
  · intro h
    rcases G.maxPackable_disjoint (G.partOf_spec F q u).2 (G.partOf_spec F q v).2 with heq | hd
    · exact heq
    · exact False.elim (disjoint_left.mp hd (G.partOf_spec F q u).1 h)

lemma partOf_eq_of_mem {F : Finset (Fin m)} {q : ℕ} {A : Finset (Fin n)}
    (hA : G.MaxPackable F q A) {v : Fin n} (hv : v ∈ A) : G.partOf F q v = A := by
  rcases G.maxPackable_disjoint (G.partOf_spec F q v).2 hA with heq | hd
  · exact heq
  · exact False.elim (disjoint_left.mp hd (G.partOf_spec F q v).1 hv)

lemma partLabel_mem (F : Finset (Fin m)) (q : ℕ) (v : Fin n) :
    G.partLabel F q v ∈ G.partOf F q v := min'_mem _ _

lemma partLabel_eq_iff (F : Finset (Fin m)) (q : ℕ) (u v : Fin n) :
    G.partLabel F q u = G.partLabel F q v ↔ G.partOf F q u = G.partOf F q v := by
  constructor
  · intro h
    rcases G.maxPackable_disjoint (G.partOf_spec F q u).2 (G.partOf_spec F q v).2 with heq | hd
    · exact heq
    · exact False.elim (disjoint_left.mp hd (G.partLabel_mem F q u) (h ▸ G.partLabel_mem F q v))
  · intro h
    unfold partLabel
    congr 1

lemma partLabel_idempotent (F : Finset (Fin m)) (q : ℕ) (v : Fin n) :
    G.partLabel F q (G.partLabel F q v) = G.partLabel F q v := by
  apply (G.partLabel_eq_iff F q _ _).mpr
  exact (G.partOf_eq_iff F q _ _).mpr (G.partLabel_mem F q v)

lemma partLabel_size (F : Finset (Fin m)) (q : ℕ) :
    partitionSize (G.partLabel F q) = (G.packingParts F q).card := by
  classical
  apply card_bij (fun v _ => G.partOf F q v)
  · intro v hv
    exact mem_filter.mpr ⟨mem_univ _, (G.partOf_spec F q v).2⟩
  · intro u hu v hv heq
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hu
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hv
    have h := (G.partLabel_eq_iff F q _ _).mpr heq
    simpa only [G.partLabel_idempotent] using h
  · intro A hA
    have hm : G.MaxPackable F q A := (mem_filter.mp hA).2
    obtain ⟨v, hv⟩ := hm.1
    refine ⟨G.partLabel F q v, mem_image.mpr ⟨v, mem_univ _, rfl⟩, ?_⟩
    have heq := G.partOf_eq_of_mem hm hv
    exact (G.partOf_eq_iff F q _ _).mpr (G.partLabel_mem F q v) |>.trans heq

end
end StrongThinTree.MultiGraph

namespace StrongThinTree.Packing
noncomputable section
open Finset Submodule
variable {E : Type uE2} {V : Type uV2} [Fintype E] [DecidableEq E]
  [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

omit [Fintype E] [DecidableEq E] [FiniteDimensional ℝ V] in
lemma span_rank_le_card (v : E → V) (T : Finset E) :
    Module.finrank ℝ (span v T) ≤ T.card := by
  classical
  have h := finrank_span_finset_le_card (R := ℝ) (T.image v)
  rw [coe_image] at h
  exact h.trans card_image_le

omit [Fintype E] in
lemma rank_le_sdiff_card_add (v : E → V) (T U : Finset E) :
    Module.finrank ℝ (span v T) ≤ (T \ U).card + Module.finrank ℝ (span v U) := by
  have hsub : span v T ≤ span v (T \ U) ⊔ span v U := by
    apply (span_le_iff v).mpr
    intro e he
    by_cases h : e ∈ U
    · exact (show span v U ≤ span v (T \ U) ⊔ span v U from le_sup_right) (mem_span_self v h)
    · exact (show span v (T \ U) ≤ span v (T \ U) ⊔ span v U from le_sup_left) (mem_span_self v (mem_sdiff.mpr ⟨he, h⟩))
  exact (Submodule.finrank_mono hsub).trans
    ((show Module.finrank ℝ (span v (T \ U) ⊔ span v U : Submodule ℝ V) ≤
        Module.finrank ℝ (span v (T \ U)) + Module.finrank ℝ (span v U) by
        have h := Submodule.finrank_sup_add_finrank_inf_eq (span v (T \ U)) (span v U)
        omega).trans (Nat.add_le_add_right (span_rank_le_card v _) _))

end
end StrongThinTree.Packing

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset Submodule
variable {n m : ℕ} (G : MultiGraph n m)

lemma internal_subset_withinParts {F : Finset (Fin m)} {q : ℕ} {A : Finset (Fin n)}
    (hA : G.MaxPackable F q A) : G.internal F A ⊆ G.withinParts F q := by
  intro e he
  obtain ⟨heF, hl, hr⟩ := mem_filter.mp he
  exact mem_filter.mpr ⟨heF, (G.partLabel_eq_iff F q _ _).mpr
    ((G.partOf_eq_of_mem hA hl).trans (G.partOf_eq_of_mem hA hr).symm)⟩

lemma same_withinParts {F : Finset (Fin m)} {q : ℕ} (hq : 0 < q) (u v : Fin n) :
    G.Same (G.withinParts F q) u v ↔ G.partLabel F q u = G.partLabel F q v := by
  constructor
  · exact G.same_preserves_label (fun e he => (mem_filter.mp he).2)
  · intro h
    let A := G.partOf F q u
    have hA : G.MaxPackable F q A := (G.partOf_spec F q u).2
    have hu : u ∈ A := (G.partOf_spec F q u).1
    have hv : v ∈ A := by
      change v ∈ G.partOf F q u
      rw [(G.partLabel_eq_iff F q u v).mp h]
      exact (G.partOf_spec F q v).1
    obtain ⟨T, hT, hd⟩ := hA.2.1
    let i : Fin q := ⟨0, hq⟩
    exact Packing.span_mono G.incidence
      ((hT i).1.trans (G.internal_subset_withinParts hA)) ((hT i).2 u hu v hv)

lemma componentCount_eq_partitionSize {T : Finset (Fin m)} {p : Fin n → Fin n}
    (h : ∀ u v, G.Same T u v ↔ p u = p v) : G.componentCount T = partitionSize p := by
  classical
  apply card_bij (fun v _ => p v)
  · intro v hv; exact mem_image.mpr ⟨v, mem_univ _, rfl⟩
  · intro u hu v hv hp
    have hr := (G.rep_eq_iff T u v).mpr ((h u v).mpr hp)
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hu
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hv
    simpa only [G.rep_idempotent] using hr
  · intro c hc
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hc
    exact ⟨G.rep T v, mem_image.mpr ⟨v, mem_univ _, rfl⟩,
      (h _ _).mp (G.rep_same T v)⟩

lemma withinParts_rank {F : Finset (Fin m)} {q : ℕ} (hq : 0 < q) :
    Module.finrank ℝ (G.edgeSpan (G.withinParts F q)) =
      n - (G.packingParts F q).card := by
  rw [G.incidence_rank, G.componentCount_eq_partitionSize (G.same_withinParts hq), G.partLabel_size]

lemma withinParts_spanning_packing (F : Finset (Fin m)) (q : ℕ) :
    ∃ S : Fin q → Finset (Fin m),
      (∀ i, S i ⊆ G.withinParts F q ∧ G.edgeSpan (S i) = G.edgeSpan (G.withinParts F q)) ∧
      ∀ ⦃i j⦄, i ≠ j → Disjoint (S i) (S j) := by
  classical
  let P := G.packingParts F q
  have hp (A : ↥P) : G.PackableOn F q A.val := (mem_filter.mp A.property).2.2.1
  choose T hT hd using hp
  let S := fun i => univ.biUnion (fun A : ↥P => T A i)
  have hmax (A : ↥P) : G.MaxPackable F q A.val := (mem_filter.mp A.property).2
  have hsub (i : Fin q) : S i ⊆ G.withinParts F q := by
    apply biUnion_subset.mpr
    intro A hA
    exact (hT A i).1.trans (G.internal_subset_withinParts (hmax A))
  refine ⟨S, fun i => ⟨hsub i, ?_⟩, ?_⟩
  · apply le_antisymm (Packing.span_mono G.incidence (hsub i))
    apply (Packing.span_le_iff G.incidence).mpr
    intro e he
    have heq := (G.partLabel_eq_iff F q _ _).mp (mem_filter.mp he).2
    let A : ↥P := ⟨G.partOf F q (G.left e), mem_filter.mpr ⟨mem_univ _, (G.partOf_spec F q _).2⟩⟩
    have hl : G.left e ∈ A.val := (G.partOf_spec F q _).1
    have hr : G.right e ∈ A.val := by
      change G.right e ∈ G.partOf F q (G.left e)
      rw [heq]
      exact (G.partOf_spec F q _).1
    exact Packing.span_mono G.incidence (subset_biUnion_of_mem (fun A : ↥P => T A i) (mem_univ A))
      ((hT A i).2 _ hl _ hr)
  · intro i j hij
    apply disjoint_left.mpr
    intro e he hi
    obtain ⟨A, hA, heA⟩ := mem_biUnion.mp he
    obtain ⟨B, hB, heB⟩ := mem_biUnion.mp hi
    have hlA := (mem_filter.mp ((hT A i).1 heA)).2.1
    have hlB := (mem_filter.mp ((hT B j).1 heB)).2.1
    have hab : A = B := by
      apply Subtype.ext
      rcases G.maxPackable_disjoint (hmax A) (hmax B) with heq | hd
      · exact heq
      · exact False.elim (disjoint_left.mp hd hlA hlB)
    subst B
    exact disjoint_left.mp (hd A hij) heA heB

lemma recycled_subset_withinParts {F U : Finset (Fin m)} {q : ℕ}
    {T : Fin q → Finset (Fin m)} (hT : ∀ i, T i ⊆ F) (hUF : U ⊆ F)
    (hd : ∀ ⦃i j⦄, i ≠ j → Disjoint (T i) (T j))
    (hs : ∀ i, G.edgeSpan U = G.edgeSpan (T i ∩ U)) : U ⊆ G.withinParts F q := by
  intro e he
  let A := G.partOf F q (G.left e)
  let B := univ.filter (fun w => G.rep U w = G.rep U (G.left e))
  have hpB : G.PackableOn F q B := G.component_packable_of_certificate hT hd hs (G.left e)
  have hsub := G.maxPackable_contains (G.partOf_spec F q (G.left e)).2 hpB
    (show (A ∩ B).Nonempty from ⟨G.left e, mem_inter.mpr ⟨(G.partOf_spec F q _).1, by simp [B]⟩⟩)
  have hr : G.right e ∈ A := hsub (by simp only [B, mem_filter, mem_univ, true_and]; exact (G.rep_endpoints he).symm)
  have hlabel := (G.partLabel_eq_iff F q (G.right e) (G.left e)).mpr ((G.partOf_eq_iff F q _ _).mpr hr)
  exact mem_filter.mpr ⟨hUF he, hlabel.symm⟩

end
end StrongThinTree.MultiGraph

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset Submodule
variable {n m : ℕ} (G : MultiGraph n m)

lemma not_packable_of_parts {F : Finset (Fin m)} {q : ℕ}
    (hparts : 1 < (G.packingParts F q).card) : ¬G.TreePackable F q := by
  classical
  intro hp
  have hull := (G.packableOn_univ F q).mpr hp
  have hsub : G.packingParts F q ⊆ {univ} := by
    intro A hA
    have hm : G.MaxPackable F q A := (mem_filter.mp hA).2
    exact mem_singleton.mpr (hm.2.2 _ (subset_univ _) hull).symm
  have hc := card_le_card hsub
  simp only [card_singleton] at hc
  omega

lemma forest_card_le {T : Finset (Fin m)} (hn : 0 < n)
    (hi : LinearIndepOn ℝ G.incidence (T : Set (Fin m))) : T.card ≤ n - 1 := by
  have hr := Packing.indep_rank G.incidence hi
  change Module.finrank ℝ (G.edgeSpan T) = T.card at hr
  rw [G.incidence_rank] at hr
  have hp := G.componentCount_pos hn T
  omega

lemma packing_cost_lt {F : Finset (Fin m)} {q : ℕ} (hn : 0 < n)
    (hp : ¬G.TreePackable F q) {T : Fin q → Finset (Fin m)}
    (hv : Packing.Valid G.incidence T) (hs : ∀ i, T i ⊆ F) :
    (∑ i, (T i).card) < q * (n - 1) := by
  classical
  have hle (i : Fin q) : (T i).card ≤ n - 1 := G.forest_card_le hn (hv.1 i)
  have ht : (∑ i, (T i).card) ≤ q * (n - 1) := by
    calc
      _ ≤ ∑ _i : Fin q, (n - 1) := sum_le_sum (fun i _ => hle i)
      _ = _ := by simp
  by_contra h
  have heq : (∑ i, (T i).card) = ∑ _i : Fin q, (n - 1) := by simpa using (Nat.le_antisymm ht (by omega))
  have hi := (sum_eq_sum_iff_of_le (fun i (_ : i ∈ (univ : Finset (Fin q))) => hle i)).mp heq
  apply hp
  refine ⟨T, fun i => ⟨hs i, (G.spanningTree_iff_independent _).mpr ⟨?_, hv.1 i⟩⟩, hv.2⟩
  apply G.connected_of_componentCount_eq_one
  have hc := hi i (mem_univ i)
  have hr := Packing.indep_rank G.incidence (hv.1 i)
  change Module.finrank ℝ (G.edgeSpan (T i)) = (T i).card at hr
  rw [G.incidence_rank, hc] at hr
  have hp := G.componentCount_pos hn (T i)
  have hnz : 0 < n := hn
  have hcn := G.componentCount_le (T i)
  omega

lemma withinParts_rank_count {F U : Finset (Fin m)} {q : ℕ} :
    q * Module.finrank ℝ (G.edgeSpan (G.withinParts F q)) ≤
      (G.withinParts F q \ U).card + q * Module.finrank ℝ (G.edgeSpan U) := by
  classical
  obtain ⟨S, hS, hd⟩ := G.withinParts_spanning_packing F q
  have hi (i : Fin q) : Module.finrank ℝ (G.edgeSpan (G.withinParts F q)) ≤
      (S i \ U).card + Module.finrank ℝ (G.edgeSpan U) := by
    rw [← (hS i).2]
    exact Packing.rank_le_sdiff_card_add G.incidence (S i) U
  have hsum := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin q))) => hi i)
  simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  have hcard : (∑ i, (S i \ U).card) ≤ (G.withinParts F q \ U).card := by
    rw [← card_biUnion]
    · apply card_le_card
      intro e he
      obtain ⟨i, hi, he⟩ := mem_biUnion.mp he
      exact mem_sdiff.mpr ⟨(hS i).1 (mem_sdiff.mp he).1, (mem_sdiff.mp he).2⟩
    · intro i hi j hj hij
      exact disjoint_of_subset_left sdiff_subset (disjoint_of_subset_right sdiff_subset (hd hij))
  exact hsum.trans (Nat.add_le_add_right hcard _)

theorem packingParts_crossing_lt {F : Finset (Fin m)} {q : ℕ} (hq : 0 < q)
    (hparts : 1 < (G.packingParts F q).card) :
    (G.crossing F (G.partLabel F q)).card < q * ((G.packingParts F q).card - 1) := by
  classical
  have hn : 0 < n := by
    have hsz := G.partLabel_size F q
    have hc : partitionSize (G.partLabel F q) ≤ n :=
      card_image_le.trans_eq (card_univ.trans (Fintype.card_fin n))
    omega
  obtain ⟨T, U, hv, hs, hUF, heq, hcost⟩ :=
    Packing.packing_certificate_on (I := Fin q) G.incidence F
  simp only [Fintype.card_fin] at hcost
  have hlt := G.packing_cost_lt hn (G.not_packable_of_parts hparts) hv hs
  have hUJ := G.recycled_subset_withinParts hs hUF hv.2 heq
  have hJ := G.withinParts_rank_count (F := F) (U := U) (q := q)
  rw [G.withinParts_rank hq] at hJ
  have hd : (G.withinParts F q \ U).card + (G.crossing F (G.partLabel F q)).card = (F \ U).card := by
    have hdis : Disjoint (G.withinParts F q \ U) (G.crossing F (G.partLabel F q)) := by
      apply disjoint_left.mpr
      intro e he hc
      exact (mem_filter.mp hc).2 (mem_filter.mp (mem_sdiff.mp he).1).2
    rw [← card_union_of_disjoint hdis]
    congr 1
    ext e
    simp only [mem_union, mem_sdiff, withinParts, crossing, mem_filter]
    constructor
    · rintro (⟨⟨heF, hp⟩, heU⟩ | ⟨heF, hp⟩)
      · exact ⟨heF, heU⟩
      · exact ⟨heF, fun heU => hp (mem_filter.mp (hUJ heU)).2⟩
    · rintro ⟨heF, heU⟩
      by_cases hp : G.partLabel F q (G.left e) = G.partLabel F q (G.right e)
      · exact Or.inl ⟨⟨heF, hp⟩, heU⟩
      · exact Or.inr ⟨heF, hp⟩
  have hsz : (G.packingParts F q).card ≤ n := by
    rw [← G.partLabel_size F q]
    exact card_image_le.trans_eq (card_univ.trans (Fintype.card_fin n))
  have hid : n - 1 = (n - (G.packingParts F q).card) + ((G.packingParts F q).card - 1) := by omega
  rw [hid, Nat.mul_add, hcost, ← hd] at hlt
  change q * (n - (G.packingParts F q).card) ≤ _ + q * Module.finrank ℝ (Packing.span G.incidence U) at hJ
  omega

end
end StrongThinTree.MultiGraph

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.HierarchyBuilder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset
variable {n : ℕ}

namespace Hierarchy

theorem exists_structure (N : Finset (Finset (Fin n)))
    (hne : ∀A ∈ N, A.Nonempty) (hroot : univ ∈ N)
    (hleaf : ∀v, {v} ∈ N)
    (hlam : ∀A ∈ N, ∀B ∈ N, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B) :
    ∃ H : Hierarchy n, H.nodes=N := by
  classical
  have hp (A : Finset (Fin n)) (hA : A ∈ N) (hAr : A ≠ univ) :
      ∃B ∈ N, A ⊂ B ∧ ∀C ∈ N, A ⊂ C → B ⊆ C := by
    let U := N.filter (fun B => A ⊂ B)
    have hu : univ ∈ U := mem_filter.mpr ⟨hroot,
      Finset.ssubset_iff_subset_ne.mpr ⟨subset_univ _,hAr⟩⟩
    obtain ⟨B,hB,hmin⟩ := exists_min_image U card ⟨univ,hu⟩
    obtain ⟨hBN,hAB⟩ := mem_filter.mp hB
    refine ⟨B,hBN,hAB,?_⟩
    intro C hCN hAC
    rcases hlam B hBN C hCN with hBC | hCB | hd
    · exact hBC
    · have hc : C ∈ U := mem_filter.mpr ⟨hCN,hAC⟩
      exact (eq_of_subset_of_card_le hCB (hmin C hc)).symm.subset
    · obtain ⟨a,ha⟩ := hne A hA
      exact False.elim (disjoint_left.mp hd (hAB.subset ha) (hAC.subset ha))
  let par (A : Finset (Fin n)) := if h : A ∈ N ∧ A ≠ univ then (hp A h.1 h.2).choose else univ
  have hs (A : Finset (Fin n)) (hA : A ∈ N) (hAr : A ≠ univ) :
      par A ∈ N ∧ A ⊂ par A ∧ ∀C ∈ N, A ⊂ C → par A ⊆ C := by
    dsimp [par]
    rw [dite_eq_left ⟨hA,hAr⟩]
    exact (hp A hA hAr).choose_spec
  exact ⟨⟨N,hne,hroot,hleaf,hlam,par,
    fun A hA hAr => (hs A hA hAr).1,
    fun A hA hAr => (hs A hA hAr).2.1,
    fun A hA hAr => (hs A hA hAr).2.2⟩,rfl⟩
end Hierarchy

namespace PartitionChain
variable (P : PartitionChain n)
lemma parts_nonempty {i : ℕ} {A : Finset (Fin n)} (hA : A ∈ P.parts i) : A.Nonempty :=
  ((P.partition i).1 A hA).1

lemma parts_disjoint {i : ℕ} {A B : Finset (Fin n)}
    (hA : A ∈ P.parts i) (hB : B ∈ P.parts i) (hne : A ≠ B) : Disjoint A B :=
  (P.partition i).2.1 hA hB hne

lemma intersect_eq {i : ℕ} {A B : Finset (Fin n)}
    (hA : A ∈ P.parts i) (hB : B ∈ P.parts i) (hab : (A ∩ B).Nonempty) : A=B := by
  by_contra h
  exact hab.ne_empty (disjoint_iff_inter_eq_empty.mp (P.parts_disjoint hA hB h))

lemma subset_of_intersect {i j : ℕ} (hij : i ≤ j) {A B : Finset (Fin n)}
    (hA : A ∈ P.parts i) (hB : B ∈ P.parts j) (hab : (A ∩ B).Nonempty) : A ⊆ B := by
  obtain ⟨C,hC,hAC⟩ := P.coarsens i j hij A hA
  have hCB : (C ∩ B).Nonempty := by
    obtain ⟨v,hv⟩ := hab
    exact ⟨v,mem_inter.mpr ⟨hAC (mem_inter.mp hv).1,(mem_inter.mp hv).2⟩⟩
  exact P.intersect_eq hC hB hCB ▸ hAC

lemma laminar {i j : ℕ} {A B : Finset (Fin n)}
    (hA : A ∈ P.parts i) (hB : B ∈ P.parts j) :
    A ⊆ B ∨ B ⊆ A ∨ Disjoint A B := by
  by_cases hd : Disjoint A B
  · exact Or.inr (Or.inr hd)
  have he := not_disjoint_iff_nonempty_inter.mp hd
  rcases le_total i j with hij | hji
  · exact Or.inl (P.subset_of_intersect hij hA hB he)
  · exact Or.inr (Or.inl (P.subset_of_intersect hji hB hA (by simpa [inter_comm] using he)))

lemma mem_nodes {I : Finset ℕ} {A : Finset (Fin n)} :
    A ∈ P.nodes I ↔ (∃i ∈ I, A ∈ P.parts i) ∨ ∃v, A={v} := by
  simp only [nodes,mem_union,mem_biUnion,mem_image,mem_univ,true_and]
  constructor
  · rintro (h | ⟨v,hv⟩)
    · exact Or.inl h
    · exact Or.inr ⟨v,hv.symm⟩
  · rintro (h | ⟨v,hv⟩)
    · exact Or.inl h
    · exact Or.inr ⟨v,hv.symm⟩

lemma nodes_nonempty {I : Finset ℕ} {A : Finset (Fin n)} (hA : A ∈ P.nodes I) : A.Nonempty := by
  rcases P.mem_nodes.mp hA with ⟨i,_,hi⟩ | ⟨v,rfl⟩
  · exact P.parts_nonempty hi
  · exact singleton_nonempty _

lemma nodes_laminar (I : Finset ℕ) : ∀A ∈ P.nodes I, ∀B ∈ P.nodes I,
    A ⊆ B ∨ B ⊆ A ∨ Disjoint A B := by
  intro A hA B hB
  rcases P.mem_nodes.mp hA with ⟨i,_,hi⟩ | ⟨v,rfl⟩ <;>
    rcases P.mem_nodes.mp hB with ⟨j,_,hj⟩ | ⟨w,rfl⟩
  · exact P.laminar hi hj
  · by_cases h : w ∈ A
    · exact Or.inr (Or.inl (singleton_subset_iff.mpr h))
    · exact Or.inr (Or.inr (disjoint_singleton_right.mpr h))
  · by_cases h : v ∈ B
    · exact Or.inl (singleton_subset_iff.mpr h)
    · exact Or.inr (Or.inr (disjoint_singleton_left.mpr h))
  · by_cases h : v=w
    · exact Or.inl (h ▸ Subset.rfl)
    · exact Or.inr (Or.inr (disjoint_singleton.mpr h))

lemma exists_hierarchy (I : Finset ℕ) (hroot : ∃i ∈ I, univ ∈ P.parts i) :
    ∃H : Hierarchy n, H.nodes=P.nodes I := by
  apply Hierarchy.exists_structure (P.nodes I)
  · exact fun A hA => P.nodes_nonempty hA
  · exact P.mem_nodes.mpr (Or.inl hroot)
  · intro v; exact P.mem_nodes.mpr (Or.inr ⟨v,rfl⟩)
  · exact P.nodes_laminar I

lemma parent_at_transition {I : Finset ℕ} {H : Hierarchy n} (hH : H.nodes=P.nodes I)
    {i j : ℕ} (hi : i ∈ I) (hj : j ∈ I) (_hij : i < j)
    (hnext : ∀k ∈ I, i < k → j ≤ k)
    {A B : Finset (Fin n)} (hA : A ∈ P.parts i) (hB : B ∈ P.parts j) (hAB : A ⊂ B) :
    H.parent A=B := by
  have hAN : A ∈ H.nodes := hH ▸ P.mem_nodes.mpr (Or.inl ⟨i,hi,hA⟩)
  have hBN : B ∈ H.nodes := hH ▸ P.mem_nodes.mpr (Or.inl ⟨j,hj,hB⟩)
  have hAr : A ≠ univ := fun h => (not_ssubset_of_subset (subset_univ _)) (h ▸ hAB)
  have hpB := H.parent_minimal A hAN hAr B hBN hAB
  have hAp := H.parent_strict A hAN hAr
  apply Subset.antisymm hpB
  have hpN : H.parent A ∈ P.nodes I := hH ▸ H.parent_mem A hAN hAr
  rcases P.mem_nodes.mp hpN with ⟨k,hk,hp⟩ | ⟨v,hp⟩
  · have hik : i < k := by
      by_contra h
      have hki : k ≤ i := by omega
      have hin : (H.parent A ∩ A).Nonempty := by
        obtain ⟨v,hv⟩ := P.parts_nonempty hA
        exact ⟨v,mem_inter.mpr ⟨hAp.subset hv,hv⟩⟩
      have he := P.subset_of_intersect hki hp hA hin
      exact (not_ssubset_of_subset he) hAp
    apply P.subset_of_intersect (hnext k hk hik) hB hp
    obtain ⟨v,hv⟩ := P.parts_nonempty hA
    exact ⟨v,mem_inter.mpr ⟨hAB.subset hv,hAp.subset hv⟩⟩
  · have hc := card_lt_card hAp
    rw [hp,card_singleton] at hc
    have hn := card_pos.mpr (P.parts_nonempty hA)
    omega

end PartitionChain
end
end StrongThinTree.MultiGraph

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.ChainEdges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace StrongThinTree.MultiGraph.PartitionChain
noncomputable section
open Finset
variable {n m : ℕ} (P : PartitionChain n) (G : MultiGraph n m)

lemma block_mem (i : ℕ) (v : Fin n) : P.block i v ∈ P.parts i := (P.part_exists i v).choose_spec.1
lemma mem_block (i : ℕ) (v : Fin n) : v ∈ P.block i v := (P.part_exists i v).choose_spec.2
lemma block_eq_of_mem {i : ℕ} {A : Finset (Fin n)} (hA : A ∈ P.parts i) {v : Fin n} (hv : v ∈ A) :
    P.block i v=A := P.intersect_eq (P.block_mem i v) hA ⟨v,mem_inter.mpr ⟨P.mem_block i v,hv⟩⟩
lemma block_subset {i j : ℕ} (hij : i ≤ j) (v : Fin n) : P.block i v ⊆ P.block j v :=
  P.subset_of_intersect hij (P.block_mem i v) (P.block_mem j v)
    ⟨v,mem_inter.mpr ⟨P.mem_block i v,P.mem_block j v⟩⟩

lemma mem_crossing (i : ℕ) (e : Fin m) : e ∈ P.crossing G i ↔ P.block i (G.left e) ≠ P.block i (G.right e) := by
  simp [crossing]
lemma crossing_antitone : Antitone (P.crossing G) := by
  intro i j hij e he
  rw [P.mem_crossing] at he ⊢
  intro h
  apply he
  apply P.block_eq_of_mem (P.block_mem j (G.right e))
  exact P.block_subset hij (G.right e) (h ▸ P.mem_block i (G.left e))
lemma crossing_root {z : ℕ} (hz : P.parts z={univ}) : P.crossing G z=∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  have hl : P.block z (G.left e)=univ := mem_singleton.mp (hz ▸ P.block_mem z (G.left e))
  have hr : P.block z (G.right e)=univ := mem_singleton.mp (hz ▸ P.block_mem z (G.right e))
  exact (P.mem_crossing G z e).mp he (hl.trans hr.symm)

lemma cut_part_crossing {i : ℕ} {A : Finset (Fin n)} (hA : A ∈ P.parts i) :
    G.cut univ A ⊆ P.crossing G i := by
  intro e he
  rw [P.mem_crossing]
  intro h
  have hc := (mem_filter.mp he).2
  rcases hc with ⟨hl,hr⟩ | ⟨hr,hl⟩
  · have hla := P.block_eq_of_mem hA hl
    exact hr ((h.symm.trans hla) ▸ P.mem_block i (G.right e))
  · have hra := P.block_eq_of_mem hA hr
    exact hl ((h.trans hra) ▸ P.mem_block i (G.left e))

lemma boundary_sum_le (i : ℕ) :
    ∑A ∈ P.parts i, (G.cut univ A).card ≤ 2*(P.crossing G i).card := by
  classical
  let C (e : Fin m) := (P.parts i).filter (fun A => e ∈ G.cut univ A)
  have hC (e : Fin m) : C e ⊆ {P.block i (G.left e),P.block i (G.right e)} := by
    intro A hA
    obtain ⟨hAP,he⟩ := mem_filter.mp hA
    rcases (mem_filter.mp he).2 with ⟨hl,_⟩ | ⟨hr,_⟩
    · exact mem_insert.mpr (Or.inl (P.block_eq_of_mem hAP hl).symm)
    · exact mem_insert.mpr (Or.inr (mem_singleton.mpr (P.block_eq_of_mem hAP hr).symm))
  have hc (e : Fin m) : (C e).card ≤ if e ∈ P.crossing G i then 2 else 0 := by
    split_ifs with he
    · exact (card_le_card (hC e)).trans (by simpa using card_insert_le (P.block i (G.left e)) {P.block i (G.right e)})
    · have hem : C e=∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro A hA
        obtain ⟨hAP,heA⟩ := mem_filter.mp hA
        exact he (P.cut_part_crossing G hAP heA)
      simp [hem]
  have heq : (∑A ∈ P.parts i, (G.cut univ A).card)=∑e : Fin m, (C e).card := by
    simp only [C,card_eq_sum_ones,sum_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro e _
    simp [cut]
  rw [heq]
  calc
    (∑e : Fin m, (C e).card) ≤ ∑e : Fin m, if e ∈ P.crossing G i then 2 else 0 := sum_le_sum (fun e _ => hc e)
    _ = 2*(P.crossing G i).card := by rw [←sum_filter]; simp [mul_comm]

lemma disappearing_in_parentBoundary {I : Finset ℕ} {H : Hierarchy n} (hH : H.nodes=P.nodes I)
    {i j : ℕ} (hi : i ∈ I) (hj : j ∈ I) (hij : i < j)
    (hnext : ∀k ∈ I, i < k → j ≤ k) {e : Fin m}
    (he : e ∈ P.crossing G i \ P.crossing G j) :
    ∃A ∈ P.parts i, e ∈ H.parentBoundary G A := by
  have he1 := (P.mem_crossing G i e).mp (mem_sdiff.mp he).1
  have he2 : P.block j (G.left e)=P.block j (G.right e) := by
    by_contra h
    exact (mem_sdiff.mp he).2 ((P.mem_crossing G j e).mpr h)
  have hr : G.right e ∉ P.block i (G.left e) := by
    intro hr
    exact he1 (P.block_eq_of_mem (P.block_mem i (G.left e)) hr).symm
  have hrB : G.right e ∈ P.block j (G.left e) := he2 ▸ P.mem_block j (G.right e)
  have hstrict : P.block i (G.left e) ⊂ P.block j (G.left e) := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨P.block_subset hij.le _,?_⟩
    intro hh
    exact hr (hh ▸ hrB)
  have hparent := P.parent_at_transition hH hi hj hij hnext (P.block_mem i (G.left e)) (P.block_mem j (G.left e)) hstrict
  refine ⟨P.block i (G.left e),P.block_mem i _,?_⟩
  change e ∈ G.cut (G.inducedEdges (H.parent (P.block i (G.left e)))) (P.block i (G.left e))
  rw [hparent]
  exact mem_filter.mpr ⟨(G.mem_inducedEdges _ e).mpr ⟨P.mem_block j _,hrB⟩,Or.inl ⟨P.mem_block i _,hr⟩⟩

end
end StrongThinTree.MultiGraph.PartitionChain

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.PartitionHierarchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset
variable {n m : ℕ} (G : MultiGraph n m)

lemma connectedOn_cut {A S : Finset (Fin n)} {T : Finset (Fin m)}
    (hc : G.ConnectedOn A T) (hS : S.Nonempty) (hSA : S ⊂ A) : (G.cut T S).Nonempty := by
  classical
  by_contra hcut
  have hempty : G.cut T S=∅ := not_nonempty_iff_eq_empty.mp hcut
  let f : (Fin n → ℝ) →ₗ[ℝ] ℝ := ∑u ∈ S, LinearMap.proj u
  have hker : G.edgeSpan T ≤ LinearMap.ker f := by
    apply (Packing.span_le_iff G.incidence).mpr
    intro e he
    have hiff : G.left e ∈ S ↔ G.right e ∈ S := by
      have hh : ¬((G.left e ∈ S ∧ G.right e ∉ S) ∨ (G.right e ∈ S ∧ G.left e ∉ S)) := by
        intro h
        have hm : e ∈ G.cut T S := mem_filter.mpr ⟨he,h⟩
        simp [hempty] at hm
      tauto
    change f (G.incidence e)=0
    rw [incidence,map_sub]
    change (∑u ∈ S, LinearMap.proj u : (Fin n → ℝ) →ₗ[ℝ] ℝ) (point (G.left e)) -
      (∑u ∈ S, LinearMap.proj u : (Fin n → ℝ) →ₗ[ℝ] ℝ) (point (G.right e))=0
    simp only [sumOn_point,hiff,sub_self]
  obtain ⟨u,hu⟩ := hS
  have hv : (A \ S).Nonempty := sdiff_nonempty.mpr (not_subset.mpr (by
    by_contra h
    push Not at h
    exact (not_ssubset_of_subset h) hSA))
  obtain ⟨v,hv⟩ := hv
  obtain ⟨hvA,hvS⟩ := mem_sdiff.mp hv
  have hz := hker (hc u (hSA.subset hu) v hvA)
  change f (point u-point v)=0 at hz
  rw [map_sub] at hz
  change (∑w ∈ S, LinearMap.proj w : (Fin n → ℝ) →ₗ[ℝ] ℝ) (point u) -
    (∑w ∈ S, LinearMap.proj w : (Fin n → ℝ) →ₗ[ℝ] ℝ) (point v)=0 at hz
  simp [sumOn_point,hu,hvS] at hz

lemma packableOn_edgeConnectedReal {F : Finset (Fin m)} {q : ℕ} {A : Finset (Fin n)}
    (hp : G.PackableOn F q A) : G.EdgeConnectedReal A q := by
  classical
  obtain ⟨T,hT,hd⟩ := hp
  intro S hS hSA
  have hne (i : Fin q) := G.connectedOn_cut (hT i).2 hS hSA
  have hdis : (↑(univ : Finset (Fin q)) : Set (Fin q)).PairwiseDisjoint (fun i => G.cut (T i) S) := by
    intro i _ j _ hij
    exact disjoint_of_subset_left (filter_subset _ _) (disjoint_of_subset_right (filter_subset _ _) (hd hij))
  have hsub : univ.biUnion (fun i : Fin q => G.cut (T i) S) ⊆ G.cut (G.inducedEdges A) S := by
    apply biUnion_subset.mpr
    intro i _ e he
    obtain ⟨het,hes⟩ := mem_filter.mp he
    have hh := (mem_filter.mp ((hT i).1 het)).2
    exact mem_filter.mpr ⟨(G.mem_inducedEdges A e).mpr hh,hes⟩
  have hh := card_le_card hsub
  rw [card_biUnion hdis] at hh
  have hl : q ≤ ∑i : Fin q, (G.cut (T i) S).card := by
    simpa using sum_le_sum (s := (univ : Finset (Fin q))) (f := fun _ => 1)
      (g := fun i => (G.cut (T i) S).card) (fun i _ => card_pos.mpr (hne i))
  exact_mod_cast hl.trans hh

lemma packingParts_local (F : Finset (Fin m)) (q : ℕ) :
    ∀A ∈ G.packingParts F q, G.EdgeConnectedReal A q := by
  intro A hA
  exact G.packableOn_edgeConnectedReal ((G.packingParts_partition F q).1 A hA).2

lemma packingParts_eq_root {F : Finset (Fin m)} {q : ℕ} (hn : 0 < n)
    (hp : G.TreePackable F q) : G.packingParts F q={univ} := by
  classical
  have hu : (univ : Finset (Fin n)).Nonempty := ⟨⟨0,hn⟩,mem_univ _⟩
  have hmax : G.MaxPackable F q univ := ⟨hu,(G.packableOn_univ F q).mpr hp,
    fun B hB _ => (Subset.antisymm (subset_univ _) hB)⟩
  have hr : univ ∈ G.packingParts F q := mem_filter.mpr ⟨mem_univ _,hmax⟩
  apply Subset.antisymm
  · intro A hA
    apply mem_singleton.mpr
    rcases G.maxPackable_disjoint (mem_filter.mp hA).2 hmax with h | h
    · exact h
    · obtain ⟨v,hv⟩ := ((G.packingParts_partition F q).1 A hA).1
      exact False.elim (disjoint_left.mp h hv (mem_univ _))
  · exact singleton_subset_iff.mpr hr

end
end StrongThinTree.MultiGraph

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.ThresholdChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset
variable {n m : ℕ} (G : MultiGraph n m)

lemma rankedEdges_full (R : Fin m → ℝ) : G.rankedEdges R m=univ := by
  ext e
  simp only [rankedEdges,mem_filter,mem_univ,true_and,iff_true]
  exact (card_le_card (subset_univ _)).trans_eq (by simp)
lemma rankedEdges_threshold (R : Fin m → ℝ) (s : ℝ) :
    G.rankedEdges R (G.thresholdEdges R s).card=G.thresholdEdges R s := by
  ext e
  change (e ∈ univ.filter (fun f => (univ.filter (fun g => R g ≤ R f)).card ≤ (univ.filter (fun g => R g ≤ s)).card)) ↔ e ∈ univ.filter (fun f => R f ≤ s)
  simp only [mem_filter,mem_univ,true_and]
  constructor
  · intro h
    by_contra he
    have hlt : s < R e := lt_of_not_ge he
    have hsub : (univ.filter (fun f => R f ≤ s)) ⊂ (univ.filter (fun f => R f ≤ R e)) := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨(by intro f hf; exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hf).2.trans hlt.le⟩),?_⟩
      intro hh
      have he' : e ∈ univ.filter (fun f => R f ≤ s) := hh ▸ mem_filter.mpr ⟨mem_univ _,le_rfl⟩
      exact he (mem_filter.mp he').2
    have hh := card_lt_card hsub
    omega
  · intro he
    exact card_le_card ((by intro f hf; exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hf).2.trans he⟩))

lemma packingChain_local (R : Fin m → ℝ) (q : ℕ) (i : ℕ) :
    ∀A ∈ (G.packingChain R q).parts i, G.EdgeConnectedReal A q := G.packingParts_local _ q

lemma packingChain_crossing (R : Fin m → ℝ) (q i : ℕ) :
    (G.packingChain R q).crossing G i=G.crossing univ (G.partLabel (G.rankedEdges R i) q) := by
  classical
  ext e
  rw [PartitionChain.mem_crossing]
  simp only [MultiGraph.crossing,mem_filter,mem_univ,true_and]
  rw [Ne,Ne,G.partLabel_eq_iff]
  have he (v : Fin n) : (G.packingChain R q).block i v=G.partOf (G.rankedEdges R i) q v := by
    apply (G.packingChain R q).block_eq_of_mem
    · exact mem_filter.mpr ⟨mem_univ _,(G.partOf_spec _ q v).2⟩
    · exact (G.partOf_spec _ q v).1
  rw [he,he]

lemma treePackable_mono_edges {F F' : Finset (Fin m)} {q : ℕ}
    (h : F ⊆ F') (hp : G.TreePackable F q) : G.TreePackable F' q := by
  obtain ⟨T,hT,hd⟩ := hp
  exact ⟨T,fun i => ⟨(hT i).1.trans h,(hT i).2⟩,hd⟩

lemma treePackable_mono_count {F : Finset (Fin m)} {q r : ℕ}
    (h : q ≤ r) (hp : G.TreePackable F r) : G.TreePackable F q := by
  obtain ⟨T,hT,hd⟩ := hp
  exact ⟨fun i => T (Fin.castLE h i),fun i => hT _,fun i j hij => hd (fun he => hij (Fin.castLE_injective h he))⟩

lemma packingChain_root (R : Fin m → ℝ) {q : ℕ} (hn : 0 < n) (hp : G.TreePackable univ q) :
    (G.packingChain R q).parts m={univ} := by
  change G.packingParts (G.rankedEdges R m) q={univ}
  rw [G.rankedEdges_full]
  exact G.packingParts_eq_root hn hp

end
end StrongThinTree.MultiGraph

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.DyadicSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace StrongThinTree.Dyadic
noncomputable section
open Finset

lemma selected_spec {M : ℕ → ℕ} {z i : ℕ} (hi : i ∈ selected M z) :
    i ≤ z ∧ 0 < M i ∧ ∀j ≤ z, 0 < M j → Nat.log 2 (M j)=Nat.log 2 (M i) → i ≤ j := by
  simp only [selected,mem_filter,mem_range] at hi
  exact ⟨by omega,hi.1.2,hi.2⟩

lemma selected_injective (M : ℕ → ℕ) (z : ℕ) :
    Set.InjOn (fun i => Nat.log 2 (M i)) (selected M z) := by
  intro i hi j hj h
  obtain ⟨hiz,hip,himin⟩ := selected_spec hi
  obtain ⟨hjz,hjp,hjmin⟩ := selected_spec hj
  exact Nat.le_antisymm (himin j hjz hjp h.symm) (hjmin i hiz hip h)

lemma representative {M : ℕ → ℕ} {z i : ℕ} (hiz : i ≤ z) (hip : 0 < M i) :
    ∃j ∈ selected M z, j ≤ i ∧ Nat.log 2 (M j)=Nat.log 2 (M i) := by
  classical
  let C := (range (z+1)).filter (fun j => 0 < M j ∧ Nat.log 2 (M j)=Nat.log 2 (M i))
  have hi : i ∈ C := mem_filter.mpr ⟨mem_range.mpr (by omega),hip,rfl⟩
  let j := C.min' ⟨i,hi⟩
  have hj : j ∈ C := min'_mem _ _
  obtain ⟨hjz,hjp,hlog⟩ := mem_filter.mp hj
  refine ⟨j,?_,min'_le _ _ hi,hlog⟩
  apply mem_filter.mpr
  refine ⟨mem_filter.mpr ⟨hjz,hjp⟩,?_⟩
  intro k hk hkp hkl
  exact min'_le C k (mem_filter.mpr ⟨mem_range.mpr (by omega),hkp,hkl.trans hlog⟩)

lemma same_bin_ratio {a b : ℕ} (hb : 0 < b) (h : Nat.log 2 a=Nat.log 2 b) : a < 2*b := by
  have ha := Nat.lt_pow_succ_log_self (by decide : 1 < 2) a
  have hl := Nat.pow_log_le_self 2 (Nat.ne_of_gt hb)
  rw [h,pow_succ] at ha
  omega

lemma tail_bound {M : ℕ → ℕ} {z : ℕ} (hmono : Antitone M) {i : ℕ}
    (hi : i ∈ selected M z) :
    (∑j ∈ (selected M z).filter (fun j => i ≤ j), (M j : ℝ)) ≤ 4*(M i : ℝ) := by
  classical
  let J := (selected M z).filter (fun j => i ≤ j)
  let a := Nat.log 2 (M i)
  have hinj : Set.InjOn (fun j => Nat.log 2 (M j)) J :=
    (selected_injective M z).mono (filter_subset _ _)
  have hsub : J.image (fun j => Nat.log 2 (M j)) ⊆ range (a+1) := by
    intro b hb
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hb
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right (hmono (mem_filter.mp hj).2)))
  have hpow : (2 : ℝ)^a ≤ (M i : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (Nat.ne_of_gt (selected_spec hi).2.1)
  calc
    (∑j ∈ J, (M j : ℝ)) ≤ ∑j ∈ J, (2 : ℝ)^(Nat.log 2 (M j)+1) := by
      apply sum_le_sum
      intro j _
      exact_mod_cast (Nat.lt_pow_succ_log_self (by decide : 1 < 2) (M j)).le
    _ = ∑b ∈ J.image (fun j => Nat.log 2 (M j)), (2 : ℝ)^(b+1) :=
      (sum_image (f := fun b => (2 : ℝ)^(b+1)) hinj).symm
    _ ≤ ∑b ∈ range (a+1), (2 : ℝ)^(b+1) :=
      sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
    _ = 2*((2 : ℝ)^(a+1)-1) := by
      simp_rw [pow_succ]
      rw [←Finset.sum_mul,geom_sum_eq (by norm_num : (2:ℝ) ≠ 1) (a+1)]
      ring
    _ ≤ 4*(M i : ℝ) := by rw [pow_succ]; linarith

end
end StrongThinTree.Dyadic

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.ResponseBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace StrongThinTree.MultiGraph.PartitionChain
noncomputable section
open Finset
variable {n m : ℕ} (P : PartitionChain n) (G : MultiGraph n m)

lemma nextIndex_spec {I : Finset ℕ} {i z : ℕ} (hz : z ∈ I) (hiz : i < z) :
    nextIndex I i z ∈ I ∧ i < nextIndex I i z ∧ ∀j ∈ I, i < j → nextIndex I i z ≤ j := by
  classical
  have h : (I.filter (fun j => i < j)).Nonempty := ⟨z,mem_filter.mpr ⟨hz,hiz⟩⟩
  rw [nextIndex,dite_eq_left h]
  have hm := min'_mem _ h
  exact ⟨(mem_filter.mp hm).1,(mem_filter.mp hm).2,fun j hj hij => min'_le _ _ (mem_filter.mpr ⟨hj,hij⟩)⟩

lemma transition_bad_bound {I : Finset ℕ} {H : Hierarchy n} (hH : H.nodes=P.nodes I)
    {i j : ℕ} (hi : i ∈ I) (hj : j ∈ I) (hij : i < j)
    (hnext : ∀k ∈ I, i < k → j ≤ k) (Bad : Finset (Fin m)) {c : ℝ} (hc : 0 ≤ c)
    (hnode : ∀A ∈ H.nodes, ((Bad ∩ H.parentBoundary G A).card : ℝ) ≤ c*(G.cut univ A).card) :
    ((Bad ∩ (P.crossing G i \ P.crossing G j)).card : ℝ) ≤ 2*c*(P.crossing G i).card := by
  classical
  have hs : Bad ∩ (P.crossing G i \ P.crossing G j) ⊆
      (P.parts i).biUnion (fun A => Bad ∩ H.parentBoundary G A) := by
    intro e he
    obtain ⟨hBad,hc⟩ := mem_inter.mp he
    obtain ⟨A,hA,heA⟩ := P.disappearing_in_parentBoundary G hH hi hj hij hnext hc
    exact mem_biUnion.mpr ⟨A,hA,mem_inter.mpr ⟨hBad,heA⟩⟩
  have hh := (card_le_card hs).trans (card_biUnion_le)
  calc
    ((Bad ∩ (P.crossing G i \ P.crossing G j)).card : ℝ) ≤
        ∑A ∈ P.parts i, ((Bad ∩ H.parentBoundary G A).card : ℝ) := by exact_mod_cast hh
    _ ≤ ∑A ∈ P.parts i, c*(G.cut univ A).card := by
      apply sum_le_sum
      intro A hA
      exact hnode A (hH ▸ P.mem_nodes.mpr (Or.inl ⟨i,hi,hA⟩))
    _ = c*(∑A ∈ P.parts i, (G.cut univ A).card : ℕ) := by rw [Nat.cast_sum,mul_sum]
    _ ≤ c*(2*(P.crossing G i).card) := by
      apply mul_le_mul_of_nonneg_left _ hc
      exact_mod_cast P.boundary_sum_le G i
    _ = _ := by ring

lemma selected_lt_end {z i : ℕ} (hz : P.parts z={univ})
    (hi : i ∈ Dyadic.selected (fun j => (P.crossing G j).card) z) : i < z := by
  obtain ⟨hiz,hip,_⟩ := Dyadic.selected_spec hi
  have hzero : (P.crossing G z).card=0 := by rw [P.crossing_root G hz,card_empty]
  apply lt_of_le_of_ne hiz
  intro he
  subst i
  omega

lemma selected_tail_bad_bound {z : ℕ} (hz : P.parts z={univ})
    {H : Hierarchy n}
    (hH : H.nodes=P.nodes (insert z (Dyadic.selected (fun j => (P.crossing G j).card) z)))
    (Bad : Finset (Fin m)) {c : ℝ} (hc : 0 ≤ c)
    (hnode : ∀A ∈ H.nodes, ((Bad ∩ H.parentBoundary G A).card : ℝ) ≤ c*(G.cut univ A).card)
    {i : ℕ} (hi : i ∈ Dyadic.selected (fun j => (P.crossing G j).card) z) :
    ((Bad ∩ P.crossing G i).card : ℝ) ≤ 8*c*(P.crossing G i).card := by
  classical
  let J := Dyadic.selected (fun j => (P.crossing G j).card) z
  let I := insert z J
  let K := J.filter (fun j => i ≤ j)
  let nx := fun j => nextIndex I j z
  have hn (j : ℕ) (hj : j ∈ J) : nx j ∈ I ∧ j < nx j ∧ ∀k ∈ I, j < k → nx j ≤ k :=
    nextIndex_spec (mem_insert_self _ _) (P.selected_lt_end G hz hj)
  have hcover : Bad ∩ P.crossing G i ⊆ K.biUnion (fun j => Bad ∩ (P.crossing G j \ P.crossing G (nx j))) := by
    intro e he
    obtain ⟨hBad,hei⟩ := mem_inter.mp he
    let E := J.filter (fun j => i ≤ j ∧ e ∈ P.crossing G j)
    have hei' : i ∈ E := mem_filter.mpr ⟨hi,le_rfl,hei⟩
    let j := E.max' ⟨i,hei'⟩
    have hjE : j ∈ E := max'_mem _ _
    obtain ⟨hjJ,hij,hej⟩ := mem_filter.mp hjE
    have hen : e ∉ P.crossing G (nx j) := by
      intro hen
      rcases mem_insert.mp (hn j hjJ).1 with hroot | hJ
      · rw [hroot,P.crossing_root G hz] at hen
        exact notMem_empty e hen
      · have hnx : nx j ∈ E := mem_filter.mpr ⟨hJ,hij.trans (hn j hjJ).2.1.le,hen⟩
        have hmax := le_max' E (nx j) hnx
        have hlt := (hn j hjJ).2.1
        omega
    exact mem_biUnion.mpr ⟨j,mem_filter.mpr ⟨hjJ,hij⟩,mem_inter.mpr ⟨hBad,mem_sdiff.mpr ⟨hej,hen⟩⟩⟩
  have hcount := (card_le_card hcover).trans (card_biUnion_le)
  calc
    ((Bad ∩ P.crossing G i).card : ℝ) ≤ ∑j ∈ K, ((Bad ∩ (P.crossing G j \ P.crossing G (nx j))).card : ℝ) := by
      exact_mod_cast hcount
    _ ≤ ∑j ∈ K, 2*c*(P.crossing G j).card := by
      apply sum_le_sum
      intro j hj
      have hjJ := (mem_filter.mp hj).1
      exact P.transition_bad_bound G hH (mem_insert_of_mem hjJ) (hn j hjJ).1
        (hn j hjJ).2.1 (hn j hjJ).2.2 Bad hc hnode
    _ = 2*c*(∑j ∈ K, ((P.crossing G j).card : ℝ)) := by rw [mul_sum]
    _ ≤ 2*c*(4*(P.crossing G i).card) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Dyadic.tail_bound (fun _ _ hij => card_le_card (P.crossing_antitone G hij)) hi
    _ = _ := by ring

lemma simultaneous_bad_bound {z : ℕ} (hz : P.parts z={univ})
    {H : Hierarchy n}
    (hH : H.nodes=P.nodes (insert z (Dyadic.selected (fun j => (P.crossing G j).card) z)))
    (Bad : Finset (Fin m)) {c : ℝ} (hc : 0 ≤ c)
    (hnode : ∀A ∈ H.nodes, ((Bad ∩ H.parentBoundary G A).card : ℝ) ≤ c*(G.cut univ A).card)
    (i : ℕ) (hiz : i ≤ z) :
    ((Bad ∩ P.crossing G i).card : ℝ) ≤ 16*c*(P.crossing G i).card := by
  classical
  by_cases hzero : (P.crossing G i).card=0
  · have hz' : P.crossing G i=∅ := card_eq_zero.mp hzero
    simp [hz']
  have hip : 0 < (P.crossing G i).card := Nat.pos_of_ne_zero hzero
  obtain ⟨j,hj,hji,hlog⟩ := Dyadic.representative (M := fun j => (P.crossing G j).card) hiz hip
  have hratio := Dyadic.same_bin_ratio hip hlog
  calc
    ((Bad ∩ P.crossing G i).card : ℝ) ≤ ((Bad ∩ P.crossing G j).card : ℝ) := by
      exact_mod_cast card_le_card (inter_subset_inter_left (P.crossing_antitone G hji))
    _ ≤ 8*c*(P.crossing G j).card := P.selected_tail_bad_bound G hz hH Bad hc hnode hj
    _ ≤ 8*c*(2*(P.crossing G i).card) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact_mod_cast hratio.le
    _ = _ := by ring

end
end StrongThinTree.MultiGraph.PartitionChain

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.HierarchyResponse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section

noncomputable section
open Matrix Finset
open scoped MatrixOrder
namespace StrongThinTree
lemma finite_markov {E : Type uE} [DecidableEq E] (B : Finset E) (R : E → ℝ)
    (hR : ∀e ∈ B, 0 ≤ R e) {t a : ℝ} (ht : 0 < t)
    (havg : (B.card:ℝ)⁻¹*(∑e ∈ B, R e) ≤ a) :
    ((B.filter (fun e => t < R e)).card:ℝ) ≤ a/t*B.card := by
  classical
  by_cases hz : B=∅
  · simp [hz]
  have hc : (0:ℝ) < B.card := Nat.cast_pos.mpr (card_pos.mpr (nonempty_iff_ne_empty.mpr hz))
  have hs : (∑e ∈ B, R e) ≤ a*B.card := by
    rw [mul_comm,←div_eq_mul_inv] at havg
    exact (div_le_iff₀ hc).mp havg
  have hm : ((B.filter (fun e => t < R e)).card:ℝ)*t ≤ ∑e ∈ B, R e := by
    calc
      _ = ∑e ∈ B.filter (fun e => t < R e), t := by simp
      _ ≤ ∑e ∈ B.filter (fun e => t < R e), R e := sum_le_sum (fun e he => (mem_filter.mp he).2.le)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun e he _ => hR e he)
  have hh := (le_div_iff₀ ht).mpr (hm.trans hs)
  calc
    _ ≤ (a*(B.card:ℝ))/t := hh
    _ = _ := by ring

namespace MultiGraph
variable {n m : ℕ} (G : MultiGraph n m)
lemma parentBoundary_sub (H : Hierarchy n) (A : Finset (Fin n)) : H.parentBoundary G A ⊆ G.cut univ A := by
  intro e he
  exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp he).2⟩
lemma singleton_locally (v : Fin n) (q : ℝ) : G.EdgeConnectedReal {v} q := by
  intro S hS hS'
  have hlt := card_lt_card hS'
  simp only [card_singleton] at hlt
  have hp := card_pos.mpr hS
  omega
lemma chain_locally (P : PartitionChain n) (I : Finset ℕ) (H : Hierarchy n) (hH : H.nodes=P.nodes I)
    {q : ℝ} (hlocal : ∀i ∈ I, ∀A ∈ P.parts i, G.EdgeConnectedReal A q) : H.LocallyConnectedReal G q := by
  intro A hA
  rw [hH] at hA
  rcases P.mem_nodes.mp hA with ⟨i,hi,hA⟩ | ⟨v,rfl⟩
  · exact hlocal i hi A hA
  · exact G.singleton_locally v q

lemma shortcut_response {H : Hierarchy n} {q : ℕ} (hq : 0 < q) (hn : 0 < n)
    (hc : G.EdgeConnected 1) {a t : ℝ} (ha : 0 ≤ a) (ht : 0 < t)
    (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.PosDef)
    (hcut : ∀S : Finset (Fin n), S.Nonempty → S ≠ univ → qform D (cutIndicator S) ≤ (G.cut univ S).card)
    (havg : ∀A ∈ H.nodes, A ≠ univ → ((G.cut univ A).card:ℝ)/q ≤ (H.parentBoundary G A).card →
      ShortcutDual.boundaryAverage G.incidence (H.parentBoundary G) A D ≤ a) :
    ∃Y ∈ G.matrixDomain, ∀A ∈ H.nodes,
      (((univ.filter (fun e => t < G.resistance Y e)) ∩ H.parentBoundary G A).card:ℝ) ≤
      (a/t+1/(q:ℝ))*(G.cut univ A).card := by
  let Y := G.baseMatrix+D
  have hY : Y.PosDef := (G.baseMatrix_pd hn).add hD
  have hYm : Y ∈ G.matrixDomain := by
    refine ⟨le_add_of_nonneg_right (Matrix.nonneg_iff_posSemidef.mpr hD.posSemidef),?_⟩
    intro S hS hS'
    rw [qform_add,G.baseMatrix_cut]
    have h1 : (1:ℝ) ≤ (G.cut univ S).card := by exact_mod_cast hc S hS hS'
    have hcard : (S.card:ℝ) ≤ n := by exact_mod_cast (show S.card ≤ n by simpa using card_le_univ S)
    have hdiv := (div_le_one (Nat.cast_pos.mpr hn)).mpr hcard
    linarith [hcut S hS hS']
  have hRY (e : Fin m) : G.resistance Y e ≤ G.resistance D e := by
    apply G.resistance_antitone hY hD
    have hb := Matrix.nonneg_iff_posSemidef.mpr (G.baseMatrix_pd hn).posSemidef
    exact le_add_of_nonneg_left hb
  have hcoeff : 0 ≤ a/t := div_nonneg ha ht.le
  have hqR : (0:ℝ) < q := Nat.cast_pos.mpr hq
  refine ⟨Y,hYm,fun A hA => ?_⟩
  have hsub := G.parentBoundary_sub H A
  have hcard : ((H.parentBoundary G A).card:ℝ) ≤ (G.cut univ A).card := by exact_mod_cast card_le_card hsub
  have hbadsub : (univ.filter (fun e => t < G.resistance Y e)) ∩ H.parentBoundary G A ⊆
      (H.parentBoundary G A).filter (fun e => t < G.resistance D e) := by
    intro e he
    obtain ⟨hb,heA⟩ := mem_inter.mp he
    exact mem_filter.mpr ⟨heA,(mem_filter.mp hb).2.trans_le (hRY e)⟩
  by_cases hroot : A=univ
  · subst A
    have he : G.cut univ univ=∅ := by ext e; simp [cut]
    have ho : H.parentBoundary G univ=∅ := subset_empty.mp (he ▸ hsub)
    simp [ho,he]
  by_cases hmark : ((G.cut univ A).card:ℝ)/q ≤ (H.parentBoundary G A).card
  · have hm := finite_markov (H.parentBoundary G A) (G.resistance D) (fun e _ => G.resistance_nonneg hD e)
      ht (havg A hA hroot hmark)
    calc
      _ ≤ (((H.parentBoundary G A).filter (fun e => t < G.resistance D e)).card:ℝ) := by exact_mod_cast card_le_card hbadsub
      _ ≤ a/t*(H.parentBoundary G A).card := hm
      _ ≤ a/t*(G.cut univ A).card := mul_le_mul_of_nonneg_left hcard hcoeff
      _ ≤ _ := by
        have hnon : 0 ≤ 1/(q:ℝ)*(G.cut univ A).card := by positivity
        linarith
  · have hb : (((univ.filter (fun e => t < G.resistance Y e)) ∩ H.parentBoundary G A).card:ℝ) ≤
        (H.parentBoundary G A).card := by exact_mod_cast card_le_card (inter_subset_right)
    have hm := (lt_of_not_ge hmark).le
    have hnon : 0 ≤ a/t*(G.cut univ A).card := mul_nonneg hcoeff (Nat.cast_nonneg _)
    calc
      _ ≤ ((H.parentBoundary G A).card:ℝ) := hb
      _ ≤ ((G.cut univ A).card:ℝ)/q := hm
      _ ≤ _ := by linarith [show ((G.cut univ A).card:ℝ)/q=(1/(q:ℝ))*(G.cut univ A).card by ring]

end MultiGraph
end StrongThinTree

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.SimultaneousResponse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Matrix Finset
open scoped MatrixOrder Classical
namespace StrongThinTree.MultiGraph

theorem simultaneous_response_exists : ∃qH : ℕ, 2 ≤ qH ∧ ∀q : ℕ, qH ≤ q →
    ∀(n m : ℕ) (G : MultiGraph n m), 0 < n → G.TreePackable univ q →
    ∀(R : Fin m → ℝ) (t : ℝ), 0 < t → ∃Y ∈ G.matrixDomain, ∀s : ℝ,
      (((univ.filter (fun e => t < G.resistance Y e)) ∩
        G.crossing univ (G.partLabel (G.thresholdEdges R s) q)).card:ℝ) ≤
      16*((q:ℝ)^(-31/40:ℝ)/t+1/(q:ℝ)) *
        (G.crossing univ (G.partLabel (G.thresholdEdges R s) q)).card := by
  obtain ⟨qH,hqH,hshortcut⟩ := Hierarchy.polynomial_shortcut
  refine ⟨qH,hqH,?_⟩
  intro q hq n m G hn hpack R t ht
  have hqp : 0 < q := by omega
  let P := G.packingChain R q
  let I := insert m (Dyadic.selected (fun j => (P.crossing G j).card) m)
  have hroot : P.parts m={univ} := G.packingChain_root R hn hpack
  obtain ⟨H,hH⟩ := P.exists_hierarchy I ⟨m,mem_insert_self _ _,hroot ▸ mem_singleton_self _⟩
  have hlocal : H.LocallyConnectedReal G q := G.chain_locally P I H hH (fun i _ => G.packingChain_local R q i)
  let M := H.nodes.filter (fun A => A ≠ univ ∧ ((G.cut univ A).card:ℝ)/q ≤ (H.parentBoundary G A).card)
  obtain ⟨D,hD,hcut,havg⟩ := hshortcut q hq n m G H hlocal M (filter_subset _ _)
    (fun A hA => (mem_filter.mp hA).2.1) (fun A hA => (mem_filter.mp hA).2.2)
  have hc : G.EdgeConnected 1 := fun S hS hS' => (by omega : 1 ≤ q).trans (Hierarchy.edgeConnected_of_locally hlocal S hS hS')
  obtain ⟨Y,hYm,hnode⟩ := G.shortcut_response hqp hn hc (Real.rpow_nonneg (Nat.cast_nonneg q) _) ht D hD hcut
    (fun A hA hA' hr => havg A (mem_filter.mpr ⟨hA,hA',hr⟩))
  refine ⟨Y,hYm,fun s => ?_⟩
  have hz : (G.thresholdEdges R s).card ≤ m := by simpa using card_le_univ (G.thresholdEdges R s)
  have hh := P.simultaneous_bad_bound G hroot hH (univ.filter (fun e => t < G.resistance Y e))
    (by positivity : 0 ≤ (q:ℝ)^(-31/40:ℝ)/t+1/(q:ℝ)) hnode (G.thresholdEdges R s).card hz
  have heq : P.crossing G (G.thresholdEdges R s).card=G.crossing univ (G.partLabel (G.thresholdEdges R s) q) := by
    rw [G.packingChain_crossing,G.rankedEdges_threshold]
  simpa only [heq] using hh

end StrongThinTree.MultiGraph

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.FixedPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV uV2 uW uI uV3 uV4 uV5 uE

section

namespace StrongThinTree.FixedPoint
noncomputable section
open Finset

variable {V : Type uV2} {W : Type uW} [DecidableEq V] [DecidableEq W]

lemma boundary_face (s : Finset V) : boundary (face s) = ∑ v ∈ s, face (s.erase v) := by
  simp [face, boundary]

lemma boundary_empty : boundary (face (∅ : Finset V)) = 0 := by
  simp [boundary_face]

lemma cone_face (v : V) (s : Finset V) :
    cone v (face s) = if v ∈ s then 0 else face (insert v s) := by
  simp [cone, face]

omit [DecidableEq V] in
lemma add_self (c : Chain V) : c + c = 0 := by
  ext s
  exact CharTwo.add_self_eq_zero (c s)

lemma boundary_cone_face (v : V) (s : Finset V) :
    boundary (cone v (face s)) + cone v (boundary (face s)) = face s := by
  classical
  by_cases hv : v ∈ s
  · rw [cone_face, ite_eq_left hv, map_zero, zero_add, boundary_face, map_sum]
    rw [Finset.sum_eq_single_of_mem v hv]
    · rw [cone_face, ite_eq_right (by simp), Finset.insert_erase hv]
    · intro w hw hwv
      rw [cone_face, ite_eq_left (Finset.mem_erase.mpr ⟨Ne.symm hwv, hv⟩)]
  · rw [cone_face, ite_eq_right hv, boundary_face, Finset.sum_insert hv, Finset.erase_insert hv,
      boundary_face, map_sum]
    simp only [cone_face]
    have heq : (∑ w ∈ s, face ((insert v s).erase w)) =
        ∑ w ∈ s, if v ∈ s.erase w then 0 else face (insert v (s.erase w)) := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [ite_eq_right (fun h => hv (Finset.mem_of_mem_erase h)),
        Finset.erase_insert_of_ne (ne_of_mem_of_not_mem hw hv).symm]
    rw [heq, add_assoc, add_self, add_zero]

lemma boundary_cone (v : V) (c : Chain V) :
    boundary (cone v c) + cone v (boundary c) = c := by
  have h : boundary.comp (cone v) + (cone v).comp boundary =
      (LinearMap.id : Chain V →ₗ[ZMod 2] Chain V) := by
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext_ring
    simpa [face] using boundary_cone_face v s
  exact congrArg (fun f : Chain V →ₗ[ZMod 2] Chain V => f c) h

lemma boundary_cone_eq (v : V) (c : Chain V) :
    boundary (cone v c) = c + cone v (boundary c) := by
  have h := congrArg (fun z => z + cone v (boundary c)) (boundary_cone v c)
  simpa only [add_assoc, add_self, add_zero] using h

lemma boundary_boundary_face (s : Finset V) : boundary (boundary (face s)) = 0 := by
  induction s using Finset.induction_on with
  | empty => simp [boundary_empty]
  | @insert v s hv ih =>
    have hs : face (insert v s) = cone v (face s) := by simp [cone_face, hv]
    rw [hs, boundary_cone_eq, map_add, boundary_cone_eq, ih, map_zero, add_zero,
      add_self]

lemma boundary_boundary (c : Chain V) : boundary (boundary c) = 0 := by
  have h : boundary.comp boundary = (0 : Chain V →ₗ[ZMod 2] Chain V) := by
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext_ring
    simpa [face] using boundary_boundary_face s
  exact congrArg (fun f : Chain V →ₗ[ZMod 2] Chain V => f c) h

lemma subdivision_face (s : Finset V) : subdivision (face s) = subdivFace s := by
  simp [subdivision, face]

lemma subdiv_empty : subdivFace (∅ : Finset V) = face ∅ := by rw [subdivFace, dite_eq_left rfl]

lemma subdiv_nonempty (s : Finset V) (hs : s.Nonempty) :
    subdivFace s = cone s (subdivision (boundary (face s))) := by
  rw [subdivFace, dite_eq_right hs.ne_empty, boundary_face]
  simp only [map_sum, subdivision_face]
  exact Finset.sum_coe_sort s (fun v => cone s (subdivFace (s.erase v)))

lemma boundary_subdivFace (s : Finset V) :
    boundary (subdivFace s) = subdivision (boundary (face s)) := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases hs : s = ∅
    · subst s
      simp [subdiv_empty, boundary_empty]
    · rw [subdiv_nonempty s (Finset.nonempty_iff_ne_empty.mpr hs), boundary_cone_eq]
      suffices boundary (subdivision (boundary (face s))) = 0 by simp [this]
      rw [boundary_face, map_sum, map_sum]
      simp only [subdivision_face]
      have heq : (∑ v ∈ s, boundary (subdivFace (s.erase v))) =
          subdivision (boundary (boundary (face s))) := by
        rw [boundary_face, map_sum, map_sum]
        apply Finset.sum_congr rfl
        intro v hv
        exact ih (s.erase v) (Finset.erase_ssubset hv)
      rw [heq, boundary_boundary, map_zero]

lemma boundary_subdivision (c : Chain V) :
    boundary (subdivision c) = subdivision (boundary c) := by
  have h : (boundary : Chain (Finset V) →ₗ[ZMod 2] Chain (Finset V)).comp subdivision =
      (subdivision : Chain V →ₗ[ZMod 2] _).comp boundary := by
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext_ring
    change boundary (subdivision (face s)) = subdivision (boundary (face s))
    rw [subdivision_face]
    exact boundary_subdivFace s
  exact congrArg (fun f : Chain V →ₗ[ZMod 2] Chain (Finset V) => f c) h

omit [DecidableEq V] in
lemma rename_face (f : V → W) (s : Finset V) :
    rename f (face s) = if Set.InjOn f (s : Set V) then face (s.image f) else 0 := by
  classical
  simp [rename, face]

lemma rename_cone_face (f : V → W) (v : V) (s : Finset V) :
    rename f (cone v (face s)) = cone (f v) (rename f (face s)) := by
  classical
  by_cases hv : v ∈ s
  · rw [cone_face, ite_eq_left hv, map_zero, rename_face]
    split_ifs with h
    · simp [cone_face, Finset.mem_image_of_mem f hv]
    · simp
  · rw [cone_face, ite_eq_right hv, rename_face, rename_face]
    have hinj : Set.InjOn f (↑(insert v s) : Set V) ↔
        Set.InjOn f (s : Set V) ∧ f v ∉ s.image f := by
      simpa using (Set.injOn_insert (f := f) (s := (s : Set V)) hv)
    simp only [hinj]
    by_cases hs : Set.InjOn f (s : Set V)
    · by_cases hf : f v ∈ s.image f
      · simp [hs, hf, cone_face]
      · simp [hs, hf, cone_face, Finset.image_insert]
    · simp [hs]

lemma rename_cone (f : V → W) (v : V) (c : Chain V) :
    rename f (cone v c) = cone (f v) (rename f c) := by
  have h : (rename f).comp (cone v) = (cone (f v)).comp (rename f) := by
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext_ring
    simpa [face] using rename_cone_face f v s
  exact congrArg (fun g : Chain V →ₗ[ZMod 2] Chain W => g c) h

lemma boundary_rename_face (f : V → W) (s : Finset V) :
    boundary (rename f (face s)) = rename f (boundary (face s)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rename_face, boundary_empty]
  | @insert v s hv ih =>
    have heq : face (insert v s) = cone v (face s) := by simp [cone_face, hv]
    rw [heq, rename_cone, boundary_cone_eq, boundary_cone_eq, map_add, rename_cone, ih]

lemma boundary_rename (f : V → W) (c : Chain V) :
    boundary (rename f c) = rename f (boundary c) := by
  have h : boundary.comp (rename f) = (rename f).comp boundary := by
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext_ring
    simpa [face] using boundary_rename_face f s
  exact congrArg (fun g : Chain V →ₗ[ZMod 2] Chain W => g c) h

omit [DecidableEq V] in
lemma supported_zero (P : Finset V → Prop) : Supported P 0 := by
  intro s hs; rfl

omit [DecidableEq V] in
lemma supported_face {P : Finset V → Prop} {s : Finset V} (hs : P s) :
    Supported P (face s) := by
  intro t ht
  have hne : s ≠ t := fun h => ht (h ▸ hs)
  simp [face, Ne.symm hne]

omit [DecidableEq V] in
lemma supported_add {P : Finset V → Prop} {c d : Chain V}
    (hc : Supported P c) (hd : Supported P d) : Supported P (c + d) := by
  intro s hs
  simp [hc s hs, hd s hs]

omit [DecidableEq V] in
lemma supported_smul {P : Finset V → Prop} {c : Chain V}
    (hc : Supported P c) (a : ZMod 2) : Supported P (a • c) := by
  intro s hs
  simp [hc s hs]

omit [DecidableEq V] in
lemma supported_sum {I : Type uI} (s : Finset I) (f : I → Chain V)
    {P : Finset V → Prop} (h : ∀i ∈ s, Supported P (f i)) :
    Supported P (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using supported_zero P
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact supported_add (h i (Finset.mem_insert_self ..))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

omit [DecidableEq V] in
lemma chain_expansion (c : Chain V) : c = ∑ s ∈ c.support, c s • face s := by
  simpa [Finsupp.sum, face] using (Finsupp.sum_single c).symm

omit [DecidableEq V] in
omit [DecidableEq W] in
lemma supported_map (L : Chain V →ₗ[ZMod 2] Chain W)
    {P : Finset V → Prop} {Q : Finset W → Prop} {c : Chain V}
    (hc : Supported P c) (hL : ∀s, P s → Supported Q (L (face s))) :
    Supported Q (L c) := by
  classical
  rw [chain_expansion c, map_sum]
  apply supported_sum
  intro s hs
  rw [map_smul]
  apply supported_smul
  apply hL s
  by_contra hn
  exact (Finsupp.mem_support_iff.mp hs) (hc s hn)

lemma supported_cone (v : V) {P Q : Finset V → Prop} {c : Chain V}
    (hc : Supported P c) (h : ∀ s, P s → v ∉ s → Q (insert v s)) :
    Supported Q (cone v c) := by
  apply supported_map (cone v) hc
  intro s hs
  rw [cone_face]
  split_ifs with hv
  · exact supported_zero Q
  · exact supported_face (h s hs hv)

omit [DecidableEq V] in
lemma supported_mono {P Q : Finset V → Prop} {c : Chain V}
    (hc : Supported P c) (h : ∀s, P s → Q s) : Supported Q c := by
  intro s hs
  exact hc s (fun hp => hs (h s hp))

lemma subdiv_supported (s : Finset V) : Supported (Flag s) (subdivFace s) := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases hs : s = ∅
    · subst s
      rw [subdiv_empty]
      apply supported_face
      simp [Flag]
    · rw [subdiv_nonempty s (Finset.nonempty_iff_ne_empty.mpr hs), boundary_face]
      simp only [map_sum, subdivision_face]
      apply supported_sum
      intro v hv
      apply supported_cone s (ih (s.erase v) (Finset.erase_ssubset hv))
      intro t ht hst
      rcases ht with ⟨hcard, hsub, hnest⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hst, hcard, Finset.card_erase_of_mem hv]
        have hpos : 0 < s.card := Finset.card_pos.mpr ⟨v, hv⟩
        omega
      · intro a ha
        rcases Finset.mem_insert.mp ha with ha | ha
        · subst a
          exact ⟨Finset.nonempty_iff_ne_empty.mpr hs, Finset.Subset.refl s⟩
        · exact ⟨(hsub a ha).1, (hsub a ha).2.trans (Finset.erase_subset v s)⟩
      · intro a ha b hb
        rcases Finset.mem_insert.mp ha with ha | ha
        · subst a
          rcases Finset.mem_insert.mp hb with hb | hb
          · subst b
            exact Or.inl (Finset.Subset.refl s)
          · exact Or.inr ((hsub b hb).2.trans (Finset.erase_subset v s))
        · rcases Finset.mem_insert.mp hb with hb | hb
          · subst b
            exact Or.inl ((hsub a ha).2.trans (Finset.erase_subset v s))
          · exact hnest a ha b hb

omit [DecidableEq V] in
lemma supported_rename (f : V → W) {P : Finset V → Prop} {Q : Finset W → Prop}
    {c : Chain V} (hc : Supported P c)
    (h : ∀s, P s → Set.InjOn f (s : Set V) → Q (s.image f)) :
    Supported Q (rename f c) := by
  classical
  apply supported_map (rename f) hc
  intro s hs
  rw [rename_face]
  split_ifs with hf
  · exact supported_face (h s hs hf)
  · exact supported_zero Q

lemma boundary_face_erase {s : Finset V} {v : V} (hv : v ∈ s) :
    boundary (face s) (s.erase v) = 1 := by
  classical
  rw [boundary_face, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single_of_mem v hv]
  · simp [face]
  · intro w hw hwv
    have hne : s.erase w ≠ s.erase v := fun h => hwv ((Finset.erase_inj s hw).mp h)
    simp [face, Ne.symm hne]

lemma supported_singleton_eq {c : Chain V} {s : Finset V}
    (hc : Supported (fun t => t = s) c) : c = c s • face s := by
  ext t
  by_cases ht : t = s
  · subst t; simp [face]
  · simp [hc t ht, face, ht]

theorem sperner_chain (F : Chain V →ₗ[ZMod 2] Chain W) (f : W → V)
    (hboundary : ∀c, boundary (F c) = F (boundary c))
    (hempty : F (face ∅) = face ∅) (s : Finset V)
    (hcarrier : ∀u ⊆ s, Supported
      (fun t => t.card = u.card ∧ ∀w ∈ t, f w ∈ u) (F (face u))) :
    rename f (F (face s)) = face s := by
  classical
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases hs : s = ∅
    · subst s
      rw [hempty]
      simp [rename_face]
    · have hsupport : Supported (fun t => t = s) (rename f (F (face s))) := by
        apply supported_rename f (hcarrier s (Finset.Subset.refl s))
        intro t ht hf
        apply Finset.eq_of_subset_of_card_le
        · intro v hv
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
          exact ht.2 w hw
        · rw [Finset.card_image_of_injOn hf, ht.1]
      have hb : boundary (rename f (F (face s))) = boundary (face s) := by
        rw [boundary_rename, hboundary, boundary_face]
        simp only [map_sum]
        apply Finset.sum_congr rfl
        intro v hv
        exact ih (s.erase v) (Finset.erase_ssubset hv)
          (fun u hu => hcarrier u (hu.trans (Finset.erase_subset v s)))
      obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hs
      have heq := supported_singleton_eq hsupport
      rw [heq, map_smul] at hb
      have hcoeff := congrArg (fun c : Chain V => c (s.erase v)) hb
      simp only [Finsupp.smul_apply, smul_eq_mul, boundary_face_erase hv, mul_one] at hcoeff
      rw [heq, hcoeff, one_smul]

omit [DecidableEq W] in
omit [DecidableEq V] in
lemma map_coefficient_witness (L : Chain V →ₗ[ZMod 2] Chain W)
    (c : Chain V) (s : Finset W) (hs : (L c) s ≠ 0) :
    ∃t ∈ c.support, (L (face t)) s ≠ 0 := by
  classical
  by_contra! hn
  apply hs
  conv_lhs => rw [chain_expansion c]
  rw [map_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro t ht
  simp [map_smul, hn t ht]

theorem sperner_witness (F : Chain V →ₗ[ZMod 2] Chain W) (f : W → V)
    (hboundary : ∀c, boundary (F c) = F (boundary c))
    (hempty : F (face ∅) = face ∅) (s : Finset V)
    (hcarrier : ∀u ⊆ s, Supported
      (fun t => t.card = u.card ∧ ∀w ∈ t, f w ∈ u) (F (face u))) :
    ∃t ∈ (F (face s)).support, Set.InjOn f (t : Set W) ∧ t.image f = s := by
  classical
  have hmain := sperner_chain F f hboundary hempty s hcarrier
  have hcoeff : (rename f (F (face s))) s ≠ 0 := by rw [hmain]; simp [face]
  obtain ⟨t, ht, hn⟩ := map_coefficient_witness (rename f) (F (face s)) s hcoeff
  rw [rename_face] at hn
  split_ifs at hn with hf
  · refine ⟨t, ht, hf, ?_⟩
    by_contra heq
    exact hn (by simp [face, Ne.symm heq])
  · exact (hn rfl).elim

lemma boundary_iterSubdivision (k : ℕ) (c : Chain V) :
    boundary (iterSubdivision k c) = iterSubdivision k (boundary c) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change boundary (subdivision (iterSubdivision k c)) =
      subdivision (iterSubdivision k (boundary c))
    rw [boundary_subdivision, ih]

lemma iterSubdivision_empty (k : ℕ) :
    iterSubdivision k (face (∅ : Finset V)) = face ∅ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change subdivision (iterSubdivision k (face (∅ : Finset V))) = face ∅
    rw [ih, subdivision_face, subdiv_empty]

omit [DecidableEq V] in
lemma mean_nonneg {z : V → ℝ} {s : Finset V} (h : ∀v ∈ s, 0 ≤ z v) :
    0 ≤ mean z s := div_nonneg (Finset.sum_nonneg h) (Nat.cast_nonneg _)

omit [DecidableEq V] in
lemma mean_zero {z : V → ℝ} {s : Finset V} (h : ∀v ∈ s, z v = 0) :
    mean z s = 0 := by simp [mean, Finset.sum_eq_zero h]

omit [DecidableEq V] in
lemma mean_difference (z : V → ℝ) (a b : Finset V) (ha : a.Nonempty)
    (hb : b.Nonempty) :
    mean z a - mean z b =
      (∑ w ∈ a ×ˢ b, (z w.1 - z w.2)) / ((a.card : ℝ) * b.card) := by
  have hac : (a.card : ℝ) ≠ 0 := by exact_mod_cast ha.card_ne_zero
  have hbc : (b.card : ℝ) ≠ 0 := by exact_mod_cast hb.card_ne_zero
  have hsum : (∑ w ∈ a ×ˢ b, (z w.1 - z w.2)) =
      (b.card : ℝ) * (∑v ∈ a, z v) - (a.card : ℝ) * (∑v ∈ b, z v) := by
    rw [Finset.sum_product]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    simp only [Finset.mul_sum]
  rw [hsum]
  unfold mean
  field_simp

lemma mean_mesh {z : V → ℝ} {a b t : Finset V} {N : ℕ} {D : ℝ}
    (ha : a ⊆ t) (hb : b ⊆ t) (hab : (a ∩ b).Nonempty)
    (ht : t.card ≤ N) (hD : 0 ≤ D)
    (hz : ∀u ∈ t, ∀v ∈ t, |z u - z v| ≤ D) :
    |mean z a - mean z b| ≤ (1 - 1 / (N : ℝ)^2) * D := by
  classical
  obtain ⟨w, hw⟩ := hab
  obtain ⟨hwa, hwb⟩ := Finset.mem_inter.mp hw
  have hane : a.Nonempty := ⟨w, hwa⟩
  have hbne : b.Nonempty := ⟨w, hwb⟩
  have hac : 0 < (a.card : ℝ) := by exact_mod_cast hane.card_pos
  have hbc : 0 < (b.card : ℝ) := by exact_mod_cast hbne.card_pos
  have hprod : 0 < (a.card : ℝ) * b.card := mul_pos hac hbc
  have hN : 0 < (N : ℝ) := by
    have : 0 < N := lt_of_lt_of_le hane.card_pos ((Finset.card_le_card ha).trans ht)
    exact_mod_cast this
  have hbound : (a.card : ℝ) * b.card ≤ (N : ℝ)^2 := by
    have h1 : (a.card : ℝ) ≤ N := by exact_mod_cast (Finset.card_le_card ha).trans ht
    have h2 : (b.card : ℝ) ≤ N := by exact_mod_cast (Finset.card_le_card hb).trans ht
    linarith [mul_le_mul h1 h2 hbc.le hN.le]
  have hwprod : (w,w) ∈ a ×ˢ b := Finset.mem_product.mpr ⟨hwa,hwb⟩
  have hsum : |∑ p ∈ a ×ˢ b, (z p.1 - z p.2)| ≤
      ((a.card : ℝ) * b.card - 1) * D := by
    rw [← Finset.sum_erase_add _ _ hwprod]
    simp only [sub_self, add_zero]
    calc
      |∑ p ∈ (a ×ˢ b).erase (w,w), (z p.1 - z p.2)| ≤
          ∑ p ∈ (a ×ˢ b).erase (w,w), |z p.1 - z p.2| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _p ∈ (a ×ˢ b).erase (w,w), D := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨hu,hv⟩ := Finset.mem_product.mp (Finset.mem_of_mem_erase hp)
        exact hz p.1 (ha hu) p.2 (hb hv)
      _ = ((a.card : ℝ) * b.card - 1) * D := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        congr 1
        rw [Finset.card_erase_of_mem hwprod, Nat.cast_sub (Finset.card_pos.mpr ⟨_, hwprod⟩),
          Finset.card_product, Nat.cast_mul, Nat.cast_one]
  rw [mean_difference z a b hane hbne, abs_div, abs_of_pos hprod]
  apply le_trans (div_le_div_of_nonneg_right hsum hprod.le)
  apply (div_le_iff₀ hprod).mpr
  have hNsq : 0 < (N : ℝ)^2 := sq_pos_of_pos hN
  have hrat : ((a.card : ℝ) * b.card) / (N : ℝ)^2 ≤ 1 :=
    (div_le_one hNsq).mpr hbound
  have : (((a.card : ℝ) * b.card) / (N : ℝ)^2) * D ≤ D :=
    (mul_le_mul_of_nonneg_right hrat hD).trans_eq (one_mul D)
  nlinarith [show (1 / (N : ℝ)^2) * ((a.card : ℝ) * b.card) =
      ((a.card : ℝ) * b.card) / (N : ℝ)^2 by ring]

section Coordinates
variable [Fintype V]

omit [DecidableEq V] in
omit [DecidableEq W] in
lemma coordFace_bary {s : Finset V} {t : Finset W} {p : W → V → ℝ}
    (ht : t.Nonempty) (hp : ∀w ∈ t, CoordFace s (p w)) :
    CoordFace s (baryPoint p t) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact mean_nonneg (fun w hw => (hp w hw).1 i)
  · change (∑i, (∑w ∈ t, p w i) / (t.card : ℝ)) = 1
    rw [← Finset.sum_div, Finset.sum_comm]
    have hsum : (∑w ∈ t, ∑i, p w i) = (t.card : ℝ) := by
      calc
        _ = ∑_w ∈ t, (1 : ℝ) := Finset.sum_congr rfl (fun w hw => (hp w hw).2.1)
        _ = _ := by simp
    rw [hsum, div_self]
    exact_mod_cast ht.card_ne_zero
  · intro i hi
    exact mean_zero (fun w hw => (hp w hw).2.2 i hi)

lemma meshFactor_nonneg {N : ℕ} (hN : 0 < N) : 0 ≤ meshFactor N := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs : 0 < (N : ℝ)^2 := by positivity
  unfold meshFactor
  have hsq : (1 : ℝ) ≤ (N : ℝ)^2 := by nlinarith
  exact sub_nonneg.mpr ((div_le_one hs).mpr hsq)

lemma meshFactor_lt_one {N : ℕ} (hN : 0 < N) : meshFactor N < 1 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  unfold meshFactor
  have : 0 < 1 / (N : ℝ)^2 := by positivity
  linarith

lemma iterSubdivision_supported (hV : 0 < Fintype.card V) (k : ℕ) (s : Finset V) :
    Supported (GeometricFacet k s) (iterSubdivision k (face s)) := by
  classical
  induction k with
  | zero =>
    change Supported (GeometricFacet 0 s) (face s)
    apply supported_face
    refine ⟨rfl, ?_, ?_⟩
    · intro v hv
      change V at v
      refine ⟨?_, ?_, ?_⟩
      · intro i
        simp only [iterPoint]
        split_ifs <;> norm_num
      · simp [iterPoint]
      · intro i hi
        have hne : v ≠ i := fun h => hi (h ▸ hv)
        simp only [iterPoint]
        exact ite_eq_right hne
    · intro u hu v hv i
      simp only [iterPoint, pow_zero]
      split_ifs <;> norm_num
  | succ k ih =>
    change Supported (GeometricFacet (k+1) s)
      (subdivision (iterSubdivision k (face s)))
    apply supported_map subdivision ih
    intro t ht
    rw [subdivision_face]
    apply supported_mono (subdiv_supported t)
    intro u hu
    refine ⟨hu.1.trans ht.1, ?_, ?_⟩
    · intro a ha
      exact coordFace_bary (hu.2.1 a ha).1
        (fun w hw => ht.2.1 w ((hu.2.1 a ha).2 hw))
    · intro a ha b hb i
      change Finset (IterV V k) at a b
      have hab : (a ∩ b).Nonempty := by
        rcases hu.2.2 a ha b hb with hab | hba
        · obtain ⟨w, hw⟩ := (hu.2.1 a ha).1
          exact ⟨w, Finset.mem_inter.mpr ⟨hw, hab hw⟩⟩
        · obtain ⟨w, hw⟩ := (hu.2.1 b hb).1
          exact ⟨w, Finset.mem_inter.mpr ⟨hba hw, hw⟩⟩
      have hcard : t.card ≤ Fintype.card V := by
        rw [ht.1]
        exact Finset.card_le_univ s
      have hm := mean_mesh (z := fun w => iterPoint k w i)
        (hu.2.1 a ha).2 (hu.2.1 b hb).2 hab hcard
        (pow_nonneg (meshFactor_nonneg hV) k)
        (fun v hv w hw => ht.2.2 v hv w hw i)
      simpa [iterPoint, baryPoint, meshFactor, pow_succ, mul_comm] using hm

omit [DecidableEq V] in

lemma simplex_label {x y : V → ℝ}
    (hx : x ∈ simplex V) (hy : y ∈ simplex V) :
    ∃i, 0 < x i ∧ y i ≤ x i := by
  by_contra! hn
  have hex : ∃i, 0 < x i := by
    by_contra! h
    have hs := Finset.sum_nonpos (s := (univ : Finset V)) (fun i _ => h i)
    rw [hx.2] at hs
    norm_num at hs
  obtain ⟨i, hi⟩ := hex
  have hle : ∀j, x j ≤ y j := by
    intro j
    by_cases hj : 0 < x j
    · exact (hn j hj).le
    · have he : x j = 0 := le_antisymm (not_lt.mp hj) (hx.1 j)
      rw [he]
      exact hy.1 j
  have hs := Finset.sum_lt_sum (fun j (_ : j ∈ (univ : Finset V)) => hle j)
    ⟨i, mem_univ i, hn i hi⟩
  rw [hx.2, hy.2] at hs
  exact (lt_irrefl (1 : ℝ)) hs

theorem simplex_approximation [Nonempty V] (F : Delta V → Delta V) (k : ℕ) :
    ∃ x : V → Delta V, (∀i, (F (x i)).1 i ≤ (x i).1 i) ∧
      ∀i j a, |(x i).1 a - (x j).1 a| ≤ (meshFactor (Fintype.card V))^k := by
  classical
  let label : IterV V k → V := fun v =>
    if h : iterPoint k v ∈ simplex V then
      (simplex_label h (F ⟨iterPoint k v, h⟩).2).choose
    else Classical.choice inferInstance
  have hlabel (v : IterV V k) (hv : iterPoint k v ∈ simplex V) :
      0 < iterPoint k v (label v) ∧
      (F ⟨iterPoint k v, hv⟩).1 (label v) ≤ iterPoint k v (label v) := by
    dsimp [label]
    rw [dite_eq_left hv]
    exact (simplex_label hv (F ⟨iterPoint k v, hv⟩).2).choose_spec
  have hV : 0 < Fintype.card V := Fintype.card_pos
  have hcarrier (u : Finset V) (_ : u ⊆ univ) :
      Supported (fun t => t.card = u.card ∧ ∀w ∈ t, label w ∈ u)
        (iterSubdivision k (face u)) := by
    apply supported_mono (iterSubdivision_supported hV k u)
    intro t ht
    refine ⟨ht.1, ?_⟩
    intro w hw
    have hp := ht.2.1 w hw
    have hl := (hlabel w ⟨hp.1, hp.2.1⟩).1
    by_contra hn
    rw [hp.2.2 _ hn] at hl
    exact (lt_irrefl 0) hl
  obtain ⟨t, ht, _, heq⟩ := sperner_witness (iterSubdivision k) label
    (boundary_iterSubdivision k) (iterSubdivision_empty k) univ hcarrier
  have hgeom : GeometricFacet k univ t := by
    by_contra hn
    exact (Finsupp.mem_support_iff.mp ht)
      (iterSubdivision_supported hV k univ t hn)
  have hpre : ∀i : V, ∃v ∈ t, label v = i := by
    intro i
    have : i ∈ t.image label := heq ▸ mem_univ i
    exact mem_image.mp this
  choose v hv hl using hpre
  let x : V → Delta V := fun i =>
    ⟨iterPoint k (v i), (hgeom.2.1 (v i) (hv i)).1,
      (hgeom.2.1 (v i) (hv i)).2.1⟩
  refine ⟨x, ?_, ?_⟩
  · intro i
    have hi := (hlabel (v i) (x i).2).2
    simpa only [hl i] using hi
  · intro i j a
    exact hgeom.2.2 (v i) (hv i) (v j) (hv j) a

theorem simplex_fixed_point [Nonempty V] (F : Delta V → Delta V) (hF : Continuous F) :
    ∃x, F x = x := by
  classical
  have hclosed : IsClosed (simplex V) := by
    have heq : simplex V = (⋂ i : V, {x : V → ℝ | 0 ≤ x i}) ∩
        {x : V → ℝ | ∑ i, x i = 1} := by
      ext x
      simp [simplex]
    rw [heq]
    exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
      (isClosed_eq (by fun_prop) continuous_const)
  have hcompact : IsCompact (simplex V) :=
    IsCompact.of_isClosed_subset (s := Set.Icc (0 : V → ℝ) 1) isCompact_Icc hclosed (by
      intro x hx
      refine ⟨hx.1, fun i => ?_⟩
      change x i ≤ 1
      exact hx.2 ▸ Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i))
  let : CompactSpace (Delta V) := isCompact_iff_compactSpace.mp hcompact
  choose x hlabel hmesh using simplex_approximation F
  let i₀ : V := Classical.choice inferInstance
  obtain ⟨z, _, φ, hφ, hz⟩ := isCompact_univ.tendsto_subseq
    (x := fun k => x k i₀) (fun _ => Set.mem_univ _)
  have hq0 := meshFactor_nonneg (Fintype.card_pos (α := V))
  have hq1 := meshFactor_lt_one (Fintype.card_pos (α := V))
  have hpow := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).comp hφ.tendsto_atTop
  have hdist (n : ℕ) (i : V) :
      dist (x (φ n) i) (x (φ n) i₀) ≤ (meshFactor (Fintype.card V))^(φ n) := by
    change dist (x (φ n) i).1 (x (φ n) i₀).1 ≤ _
    apply (dist_pi_le_iff (pow_nonneg hq0 _)).mpr
    intro a
    exact hmesh (φ n) i i₀ a
  have hlim (i : V) : Filter.Tendsto (fun n => x (φ n) i) Filter.atTop (nhds z) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    have hz' := tendsto_iff_dist_tendsto_zero.mp hz
    apply squeeze_zero (fun _ => dist_nonneg)
      (fun n => (dist_triangle _ (x (φ n) i₀) _).trans (_root_.add_le_add (hdist n i) le_rfl))
    simpa only [zero_add, Function.comp_def] using hpow.add hz'
  have hle (i : V) : (F z).1 i ≤ z.1 i := by
    have hc : Continuous (fun y : Delta V => y.1 i) :=
      (continuous_apply i).comp continuous_subtype_val
    exact le_of_tendsto_of_tendsto ((hc.comp hF).tendsto z |>.comp (hlim i))
      (hc.tendsto z |>.comp (hlim i)) (Filter.Eventually.of_forall (fun n => hlabel (φ n) i))
  refine ⟨z, Subtype.ext (funext fun i => ?_)⟩
  have he := (Finset.sum_eq_sum_iff_of_le
    (fun i (_ : i ∈ (univ : Finset V)) => hle i)).mp ((F z).2.2.trans z.2.2.symm)
  exact he i (mem_univ i)

end Coordinates

section ConvexFixedPoint
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem compact_convex_approximation {K : Set E} (hK : IsCompact K)
    (hne : K.Nonempty) (hc : Convex ℝ K) (F : K → K) (hF : Continuous F)
    {ε : ℝ} (hε : 0 < ε) : ∃x : K, dist x (F x) ≤ ε := by
  classical
  obtain ⟨t, htK, htfin, htcover⟩ := hK.finite_cover_balls hε
  let : Fintype t := htfin.fintype
  have htne : t.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    have h := htcover hx
    simp only [Set.mem_iUnion] at h
    obtain ⟨y, hy, _⟩ := h
    exact ⟨y, hy⟩
  let : Nonempty t := htne.to_subtype
  let bump (x : K) (i : t) : ℝ := max 0 (ε - dist x.1 i.1)
  let total (x : K) : ℝ := ∑i : t, bump x i
  have hbump (x : K) (i : t) : 0 ≤ bump x i := le_max_left _ _
  have htotal (x : K) : 0 < total x := by
    obtain ⟨y, hyx⟩ := Set.mem_iUnion.mp (htcover x.2)
    obtain ⟨hy, hxy⟩ := Set.mem_iUnion.mp hyx
    apply Finset.sum_pos' (fun i _ => hbump x i)
    refine ⟨⟨y, hy⟩, mem_univ _, ?_⟩
    exact lt_of_lt_of_le (sub_pos.mpr hxy) (le_max_right _ _)
  let weights (x : K) : Delta t := ⟨fun i => bump x i / total x,
    (fun i => div_nonneg (hbump x i) (htotal x).le), by
      rw [← Finset.sum_div]
      exact div_self (htotal x).ne'⟩
  have cbump (i : t) : Continuous (fun x : K => bump x i) :=
    continuous_const.max (continuous_const.sub (continuous_subtype_val.dist continuous_const))
  have ctotal : Continuous total := continuous_finsetSum _ (fun i _ => cbump i)
  have cweights : Continuous weights := by
    apply Continuous.subtype_mk
    exact continuous_pi (fun i => (cbump i).div ctotal (fun x => (htotal x).ne'))
  let combo (u : Delta t) : K := ⟨∑i : t, u.1 i • i.1,
    hc.sum_mem (fun i _ => u.2.1 i) u.2.2 (fun i _ => htK i.2)⟩
  have ccombo : Continuous combo := by
    apply Continuous.subtype_mk
    apply continuous_finsetSum
    intro i _
    exact ((continuous_apply i).comp continuous_subtype_val).smul continuous_const
  have happrox (y : K) : dist (combo (weights y)) y ≤ ε := by
    change dist (∑i : t, (weights y).1 i • i.1) y.1 ≤ ε
    rw [dist_eq_norm]
    have he : (∑i : t, (weights y).1 i • i.1) - y.1 =
        ∑i : t, (weights y).1 i • (i.1 - y.1) := by
      rw [Finset.sum_congr rfl (fun i _ => smul_sub _ _ _), Finset.sum_sub_distrib,
        ← Finset.sum_smul, (weights y).2.2, one_smul]
    rw [he]
    calc
      _ ≤ ∑i : t, ‖(weights y).1 i • (i.1 - y.1)‖ := norm_sum_le _ _
      _ ≤ ∑i : t, (weights y).1 i * ε := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ((weights y).2.1 i)]
        by_cases hi : bump y i = 0
        · have hw : (weights y).1 i = 0 := by simp [weights, hi]
          simp only [hw, zero_mul, le_refl]
        · have hd : dist y.1 i.1 < ε := by
            have hp : 0 < bump y i := (hbump y i).lt_of_ne' hi
            dsimp [bump] at hp
            exact sub_pos.mp ((lt_max_iff.mp hp).resolve_left (lt_irrefl 0))
          apply mul_le_mul_of_nonneg_left _ ((weights y).2.1 i)
          simpa only [← dist_eq_norm, dist_comm] using hd.le
      _ = ε := by rw [← Finset.sum_mul, (weights y).2.2, one_mul]
  obtain ⟨u, hu⟩ := simplex_fixed_point (fun u => weights (F (combo u)))
    (cweights.comp (hF.comp ccombo))
  refine ⟨combo u, ?_⟩
  have := happrox (F (combo u))
  rwa [hu] at this

theorem compact_convex_fixed_point {K : Set E} (hK : IsCompact K)
    (hne : K.Nonempty) (hc : Convex ℝ K) (F : K → K) (hF : Continuous F) :
    ∃x, F x = x := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have heps (n : ℕ) : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  choose x hx using fun n => compact_convex_approximation hK hne hc F hF (heps n)
  obtain ⟨z, _, φ, hφ, hz⟩ := isCompact_univ.tendsto_subseq
    (x := x) (fun _ => Set.mem_univ _)
  have hlim : Filter.Tendsto (fun n => dist (x (φ n)) (F (x (φ n))))
      Filter.atTop (nhds 0) :=
    squeeze_zero (fun _ => dist_nonneg) (fun n => hx (φ n))
      (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop)
  have hzero : dist z (F z) = 0 := tendsto_nhds_unique
    ((continuous_id.dist hF).tendsto z |>.comp hz) hlim
  exact ⟨z, (dist_eq_zero.mp hzero).symm⟩
end ConvexFixedPoint

end
end StrongThinTree.FixedPoint

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.ResponseFixedPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section

noncomputable section
open Finset
namespace StrongThinTree

theorem response_fixed_point {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (hK : IsCompact K) (hne : K.Nonempty) (hc : Convex ℝ K)
    (R : K → K) {ε : ℝ} (hε : 0 < ε) :
    ∃X : K, ∃C : Finset K, ∃w : K → ℝ,
      (∀c ∈ C, 0 ≤ w c) ∧ (∑c ∈ C, w c)=1 ∧
      (∑c ∈ C, w c • (R c).val)=X.val ∧
      (∀c ∈ C, 0 < w c → dist c X < ε) := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨U,_,hUfin,hUcover⟩ := (isCompact_univ : IsCompact (Set.univ : Set K)).finite_cover_balls hε
  let C := hUfin.toFinset
  have hcover (x : K) : ∃c ∈ C, dist x c < ε := by
    obtain ⟨c,hc⟩ := Set.mem_iUnion.mp (hUcover (Set.mem_univ x))
    obtain ⟨hcU,hxc⟩ := Set.mem_iUnion.mp hc
    exact ⟨c,hUfin.mem_toFinset.mpr hcU,hxc⟩
  let bump (x c : K) : ℝ := max 0 (ε-dist x c)
  let total (x : K) : ℝ := ∑c ∈ C, bump x c
  have hbump (x c : K) : 0 ≤ bump x c := le_max_left _ _
  have ht (x : K) : 0 < total x := by
    obtain ⟨c,hc,hxc⟩ := hcover x
    exact sum_pos' (fun c _ => hbump x c) ⟨c,hc,lt_of_lt_of_le (sub_pos.mpr hxc) (le_max_right _ _)⟩
  let w (x c : K) : ℝ := bump x c/total x
  have hw (x c : K) : 0 ≤ w x c := div_nonneg (hbump x c) (ht x).le
  have hw1 (x : K) : (∑c ∈ C, w x c)=1 := by
    dsimp [w]
    rw [←sum_div]
    exact div_self (ht x).ne'
  have cb (c : K) : Continuous (fun x => bump x c) :=
    continuous_const.max (continuous_const.sub (continuous_id.dist continuous_const))
  have ct : Continuous total := continuous_finsetSum _ (fun c _ => cb c)
  have cw (c : K) : Continuous (fun x => w x c) := (cb c).div ct (fun x => (ht x).ne')
  let F (x : K) : K := ⟨∑c ∈ C, w x c • (R c).val,
    hc.sum_mem (fun c _ => hw x c) (hw1 x) (fun c _ => (R c).property)⟩
  have cF : Continuous F := by
    apply Continuous.subtype_mk
    exact continuous_finsetSum _ (fun c _ => (cw c).smul continuous_const)
  obtain ⟨X,hX⟩ := FixedPoint.compact_convex_fixed_point hK hne hc F cF
  refine ⟨X,C,w X,fun c _ => hw X c,hw1 X,congrArg Subtype.val hX,?_⟩
  intro c _ hpos
  have hp : 0 < bump X c := (div_pos_iff_of_pos_right (ht X)).mp hpos
  have hh : dist X c < ε := sub_pos.mp ((lt_max_iff.mp hp).resolve_left (lt_irrefl 0))
  simpa only [dist_comm] using hh

end StrongThinTree

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.MatrixMixture
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uV uE

section

noncomputable section
open Matrix Finset
open scoped MatrixOrder
namespace StrongThinTree
variable {I : Type uI} {V : Type uV} [Fintype V] [DecidableEq V]
lemma mixture_resistance (C : Finset I) (w : I → ℝ) (Y : I → Matrix V V ℝ)
    (hw : ∀i ∈ C, 0 ≤ w i) (hw1 : (∑i ∈ C, w i)=1)
    (hY : ∀i ∈ C, (Y i).PosDef) {X : Matrix V V ℝ} (hX : X.PosDef)
    (heq : (∑i ∈ C, w i • Y i)=X) {t : ℝ} (ht : 0 < t) (b : V → ℝ)
    (hb : mixtureBadWeight C w Y t b ≤ 1/2) : qform X⁻¹ b ≤ 2*t := by
  classical
  let good : I → ℝ := fun i => if t < qform (Y i)⁻¹ b then 0 else w i
  have hsplit : (∑i ∈ C, good i)+mixtureBadWeight C w Y t b=1 := by
    rw [mixtureBadWeight,←sum_add_distrib,←hw1]
    apply sum_congr rfl
    intro i _
    dsimp [good]
    split_ifs <;> simp
  have hgood : (1/2:ℝ) ≤ ∑i ∈ C, good i := by linarith
  have ho : ∀i ∈ C, good i • vecMulVec b b ≤ (t*w i) • Y i := by
    intro i hi
    dsimp [good]
    split_ifs with h
    · simp only [zero_smul]
      exact smul_nonneg (mul_nonneg ht.le (hw i hi)) (Matrix.nonneg_iff_posSemidef.mpr (hY i hi).posSemidef)
    · have hh : vecMulVec b b ≤ t • Y i := Matrix.le_iff.mpr ((resistance_order (hY i hi) b ht).mp (le_of_not_gt h))
      simpa only [smul_smul,mul_comm] using smul_le_smul_of_nonneg_left hh (hw i hi)
  have hs : (∑i ∈ C, good i) • vecMulVec b b ≤ t • X := by
    have hh := sum_le_sum ho
    rw [←sum_smul] at hh
    rw [←heq,smul_sum]
    convert hh using 1
    apply sum_congr rfl
    intro i _
    rw [smul_smul]
  have hbpsd : 0 ≤ vecMulVec b b := Matrix.nonneg_iff_posSemidef.mpr (by simpa only [star_trivial] using posSemidef_vecMulVec_self_star b)
  have hhalf : (1/2:ℝ) • vecMulVec b b ≤ t • X := (smul_le_smul_of_nonneg_right hgood hbpsd).trans hs
  have hdouble := smul_le_smul_of_nonneg_left hhalf (by norm_num : (0:ℝ) ≤ 2)
  have horder : vecMulVec b b ≤ (2*t) • X := by
    simpa only [smul_smul,show (2:ℝ)*(1/2)=1 by norm_num,one_smul] using hdouble
  exact (resistance_order hX b (by positivity)).mpr (Matrix.le_iff.mp horder)

lemma mixture_bad_bound {E : Type uE} [DecidableEq E] (B : Finset E) (b : E → V → ℝ)
    (C : Finset I) (w : I → ℝ) (Y : I → Matrix V V ℝ)
    (hw : ∀i ∈ C, 0 ≤ w i) (hw1 : (∑i ∈ C, w i)=1)
    (hY : ∀i ∈ C, (Y i).PosDef) {X : Matrix V V ℝ} (hX : X.PosDef)
    (heq : (∑i ∈ C, w i • Y i)=X) {t δ : ℝ} (ht : 0 < t)
    (hcount : ∀i ∈ C, 0 < w i → ((B.filter (fun e => t < qform (Y i)⁻¹ (b e))).card:ℝ) ≤ δ*B.card) :
    ((B.filter (fun e => 2*t < qform X⁻¹ (b e))).card:ℝ) ≤ 2*δ*B.card := by
  classical
  by_cases hB : B=∅
  · simp [hB]
  have hBp : (0:ℝ) < B.card := Nat.cast_pos.mpr (card_pos.mpr (nonempty_iff_ne_empty.mpr hB))
  let z := fun e => mixtureBadWeight C w Y t (b e)
  have hz (e : E) : 0 ≤ z e := sum_nonneg (fun i hi => by split_ifs; exact hw i hi; exact le_rfl)
  have hsum : (∑e ∈ B, z e) ≤ δ*B.card := by
    calc
      _ = ∑i ∈ C, w i*((B.filter (fun e => t < qform (Y i)⁻¹ (b e))).card:ℝ) := by
        dsimp [z,mixtureBadWeight]
        rw [sum_comm]
        apply sum_congr rfl
        intro i _
        rw [←sum_filter]
        simp [mul_comm]
      _ ≤ ∑i ∈ C, w i*(δ*B.card) := by
        apply sum_le_sum
        intro i hi
        rcases (hw i hi).eq_or_lt with hzero | hpos
        · simp [←hzero]
        · exact mul_le_mul_of_nonneg_left (hcount i hi hpos) (hw i hi)
      _ = δ*B.card := by rw [←sum_mul,hw1,one_mul]
  have havg : (B.card:ℝ)⁻¹*(∑e ∈ B, z e) ≤ δ := by
    rw [mul_comm,←div_eq_mul_inv]
    exact (div_le_iff₀ hBp).mpr hsum
  have hm := finite_markov B z (fun e _ => hz e) (by norm_num : (0:ℝ)<1/2) havg
  have hsub : B.filter (fun e => 2*t < qform X⁻¹ (b e)) ⊆ B.filter (fun e => 1/2 < z e) := by
    intro e he
    obtain ⟨heB,heR⟩ := mem_filter.mp he
    refine mem_filter.mpr ⟨heB,?_⟩
    by_contra h
    have hh := mixture_resistance C w Y hw hw1 hY hX heq ht (b e) (le_of_not_gt h)
    linarith
  have hc : ((B.filter (fun e => 2*t < qform X⁻¹ (b e))).card:ℝ) ≤ (B.filter (fun e => 1/2 < z e)).card := by
    exact_mod_cast card_le_card hsub
  linarith

end StrongThinTree

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.ExtractionLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Matrix Finset Filter
open scoped MatrixOrder Matrix.Norms.Elementwise Topology
namespace StrongThinTree.MultiGraph
variable {n m : ℕ} (G : MultiGraph n m)
lemma bad_inter_eq (R : Fin m → ℝ) (t : ℝ) (B : Finset (Fin m)) :
    (univ.filter (fun e => t < R e)) ∩ B=B.filter (fun e => t < R e) := by
  ext e
  simp only [mem_inter,mem_filter,mem_univ,true_and,and_comm]
lemma resistance_domain_continuous (hn : 0 < n) (e : Fin m) :
    Continuous (fun X : G.matrixDomain => G.resistance X.val e) :=
  continuousOn_iff_continuous_domRestrict.mp (G.resistance_continuousOn hn e)
lemma threshold_stable_neighborhood (hn : 0 < n) (X : G.matrixDomain) (s : ℝ)
    (havoid : ∀e, G.resistance X.val e ≠ s) :
    ∃ε : ℝ, 0 < ε ∧ ∀Y : G.matrixDomain, dist Y X < ε →
      G.thresholdEdges (G.resistance Y.val) s=G.thresholdEdges (G.resistance X.val) s := by
  have hneigh : ∀ᶠ Y : G.matrixDomain in 𝓝 X, ∀e,
      (G.resistance Y.val e ≤ s ↔ G.resistance X.val e ≤ s) := by
    apply Filter.eventually_all.mpr
    intro e
    by_cases hle : G.resistance X.val e ≤ s
    · have hlt := lt_of_le_of_ne hle (havoid e)
      filter_upwards [(G.resistance_domain_continuous hn e).continuousAt.eventually_lt_const hlt] with Y hY
      exact iff_of_true hY.le hle
    · have hlt := lt_of_not_ge hle
      filter_upwards [(G.resistance_domain_continuous hn e).continuousAt.eventually_const_lt hlt] with Y hY
      exact iff_of_false (not_le.mpr hY) hle
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hneigh
  refine ⟨ε,hε,fun Y hY => ?_⟩
  ext e
  simp only [thresholdEdges, mem_filter, mem_univ, true_and]
  exact hball hY e

theorem response_limit (hn : 2 ≤ n) (hc : G.EdgeConnected 1) (q : ℕ) {t δ : ℝ} (ht : 0 < t)
    (hresponse : ∀X ∈ G.matrixDomain, ∃Y ∈ G.matrixDomain, ∀s : ℝ,
      (((univ.filter (fun e => t < G.resistance Y e)) ∩ G.thresholdCrossing q X s).card:ℝ) ≤
        δ*(G.thresholdCrossing q X s).card) :
    ∃X ∈ G.matrixDomain, ∀s : ℝ, (∀e, G.resistance X e ≠ s) →
      (((G.thresholdCrossing q X s).filter (fun e => 2*t < G.resistance X e)).card:ℝ) ≤
        2*δ*(G.thresholdCrossing q X s).card := by
  classical
  have hnp : 0 < n := by omega
  have hK := G.domain_compact hn
  have hne := G.domain_nonempty hnp hc
  have hcv := G.domain_convex
  have hr (X : G.matrixDomain) : ∃Y : G.matrixDomain, ∀s : ℝ,
      (((univ.filter (fun e => t < G.resistance Y.val e)) ∩ G.thresholdCrossing q X.val s).card:ℝ) ≤
        δ*(G.thresholdCrossing q X.val s).card := by
    obtain ⟨Y,hY,h⟩ := hresponse X.val X.property
    exact ⟨⟨Y,hY⟩,h⟩
  choose R hR using hr
  have heps (p : ℕ) : (0:ℝ) < 1/((p:ℝ)+1) := by positivity
  choose Xp C w hw hw1 heq hnear using fun p => response_fixed_point hK hne hcv R (heps p)
  let : CompactSpace G.matrixDomain := isCompact_iff_compactSpace.mp hK
  let : FirstCountableTopology (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (FirstCountableTopology (Fin n → Fin n → ℝ))
  obtain ⟨X,_,φ,hφ,hlim⟩ := isCompact_univ.tendsto_subseq (x := Xp) (fun _ => Set.mem_univ _)
  have hnearTime : Tendsto (fun p => 1/((φ p:ℝ)+1)+dist (Xp (φ p)) X) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, add_zero] using (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop).add
      (tendsto_iff_dist_tendsto_zero.mp hlim)
  refine ⟨X.val,X.property,fun s havoid => ?_⟩
  let B := G.thresholdCrossing q X.val s
  obtain ⟨ε,hε,hεspec⟩ := G.threshold_stable_neighborhood hnp X s havoid
  have hstable : ∀ᶠ p in atTop, ∀c ∈ C (φ p), 0 < w (φ p) c →
      G.thresholdCrossing q c.val s=B := by
    filter_upwards [hnearTime.eventually_lt_const hε] with p hp
    intro c hc hwc
    have hd : dist c X < ε := by
      have hh := hnear (φ p) c hc hwc
      have htri := dist_triangle c (Xp (φ p)) X
      linarith
    unfold thresholdCrossing
    rw [hεspec c hd]
    rfl
  have hcounts : ∀ᶠ p in atTop,
      ((B.filter (fun e => 2*t < G.resistance (Xp (φ p)).val e)).card:ℝ) ≤ 2*δ*B.card := by
    filter_upwards [hstable] with p hp
    apply mixture_bad_bound B G.incidence (C (φ p)) (w (φ p)) (fun c => (R c).val)
      (hw (φ p)) (hw1 (φ p)) (fun c _ => G.domain_pd hnp (R c).property)
      (G.domain_pd hnp (Xp (φ p)).property) (heq (φ p)) ht
    intro c hc hwc
    have hh := hR c s
    rw [hp c hc hwc,bad_inter_eq] at hh
    exact hh
  let Bad := B.filter (fun e => 2*t < G.resistance X.val e)
  have hpersist : ∀ᶠ p in atTop, ∀e ∈ Bad, 2*t < G.resistance (Xp (φ p)).val e := by
    apply (Filter.eventually_all_finset Bad).mpr
    intro e he
    have hgt := (mem_filter.mp he).2
    exact ((G.resistance_domain_continuous hnp e).tendsto X |>.comp hlim).eventually_const_lt hgt
  obtain ⟨p,hp,hpers⟩ := (hcounts.and hpersist).exists
  have hsub : Bad ⊆ B.filter (fun e => 2*t < G.resistance (Xp (φ p)).val e) := by
    intro e he
    exact mem_filter.mpr ⟨(mem_filter.mp he).1,hpers e he⟩
  exact (show (Bad.card:ℝ) ≤ (B.filter (fun e => 2*t < G.resistance (Xp (φ p)).val e)).card by
    exact_mod_cast card_le_card hsub).trans hp

end StrongThinTree.MultiGraph

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.ExtractionCriterion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Finset Matrix
open scoped MatrixOrder
namespace StrongThinTree.MultiGraph
variable {n m : ℕ} (G : MultiGraph n m)
lemma treePackable_edgeConnected {r : ℕ} (hp : G.TreePackable univ r) : G.EdgeConnected r := by
  have hh := G.packableOn_edgeConnectedReal ((G.packableOn_univ univ r).mpr hp)
  intro S hS hS'
  have hs : S ⊂ (univ : Finset (Fin n)) := Finset.ssubset_iff_subset_ne.mpr ⟨subset_univ _,hS'⟩
  have hc := hh S hS hs
  have hi : G.inducedEdges univ = univ := by ext e; simp [mem_inducedEdges]
  rw [hi] at hc
  exact_mod_cast hc

lemma packable_of_parts_le_one (hn : 0 < n) {F : Finset (Fin m)} {q : ℕ}
    (hc : (G.packingParts F q).card ≤ 1) : G.TreePackable F q := by
  classical
  have hne : (G.packingParts F q).Nonempty :=
    ⟨G.partOf F q ⟨0,hn⟩,mem_filter.mpr ⟨mem_univ _,(G.partOf_spec F q ⟨0,hn⟩).2⟩⟩
  have hc1 : (G.packingParts F q).card=1 := by have := card_pos.mpr hne; omega
  obtain ⟨A,hA⟩ := card_eq_one.mp hc1
  have hh := (G.packingParts_partition F q).2.2
  rw [hA] at hh
  have hAu : A = univ := by simpa using hh
  apply (G.packableOn_univ F q).mp
  rw [hA] at hne
  have hp := ((G.packingParts_partition F q).1 A (hA ▸ mem_singleton_self A)).2
  simpa only [hAu] using hp

lemma consistent_packable (hn : 0 < n) {r q : ℕ} (hqp : 0 < q)
    (hp : G.TreePackable univ r) {X : Matrix (Fin n) (Fin n) ℝ} {t δ s : ℝ}
    (hst : 2*t < s) (hnum : (q:ℝ) < (1-2*δ)*r)
    (hcount : (((G.thresholdCrossing q X s).filter (fun e => 2*t < G.resistance X e)).card:ℝ) ≤
      2*δ*(G.thresholdCrossing q X s).card) :
    G.TreePackable (G.thresholdEdges (G.resistance X) s) q := by
  classical
  let F := G.thresholdEdges (G.resistance X) s
  let p := G.partLabel F q
  let B := G.crossing univ p
  by_contra hnot
  have hd : 1 < (G.packingParts F q).card := by
    by_contra hh
    exact hnot (G.packable_of_parts_le_one hn (F:=F) (q:=q) (by omega))
  have hupper := G.packingParts_crossing_lt hqp hd
  have hlower := G.partition_criterion_necessary hn hp p
  rw [G.partLabel_size] at hlower
  let Bad := B.filter (fun e => 2*t < G.resistance X e)
  let Good := B.filter (fun e => ¬(2*t < G.resistance X e))
  have hsub : Good ⊆ G.crossing F p := by
    intro e he
    obtain ⟨heB,heR⟩ := mem_filter.mp he
    refine mem_filter.mpr ⟨?_,(mem_filter.mp heB).2⟩
    exact mem_filter.mpr ⟨mem_univ _,(le_of_not_gt heR).trans hst.le⟩
  have hsum : Bad.card+Good.card=B.card := card_filter_add_card_filter_not _
  have hrate : 0 < 1-2*δ := by
    have hr : (0:ℝ) ≤ r := Nat.cast_nonneg _
    have hq : (0:ℝ) ≤ q := Nat.cast_nonneg _
    nlinarith
  have hMR : (r:ℝ)*((G.packingParts F q).card-1:ℕ) ≤ (B.card:ℝ) := by
    exact_mod_cast hlower
  have hpos : (0:ℝ) < ((G.packingParts F q).card-1:ℕ) := by
    exact_mod_cast (show 0 < (G.packingParts F q).card-1 by omega)
  have hm := mul_le_mul_of_nonneg_left hMR hrate.le
  have hstrict := mul_lt_mul_of_pos_right hnum hpos
  have hGood : (Good.card:ℝ) ≤ (G.crossing F p).card := by exact_mod_cast card_le_card hsub
  have hu : ((G.crossing F p).card:ℝ) < (q:ℝ)*((G.packingParts F q).card-1:ℕ) := by exact_mod_cast hupper
  have hs : (Bad.card:ℝ)+(Good.card:ℝ)=B.card := by exact_mod_cast hsum
  change (Bad.card:ℝ) ≤ 2*δ*B.card at hcount
  linarith

theorem extraction_from_response_threshold {qH : ℕ} (hqH : 2 ≤ qH)
    (hresp : ∀q : ℕ, qH ≤ q → ∀(n m : ℕ) (G : MultiGraph n m), 0 < n →
      G.TreePackable univ q → ∀(R : Fin m → ℝ) (t : ℝ), 0 < t →
      ∃Y ∈ G.matrixDomain, ∀s : ℝ,
      (((univ.filter (fun e => t < G.resistance Y e)) ∩
        G.crossing univ (G.partLabel (G.thresholdEdges R s) q)).card:ℝ) ≤
      16*((q:ℝ)^(-31/40:ℝ)/t+1/q)*(G.crossing univ (G.partLabel (G.thresholdEdges R s) q)).card)
    (hn : 2 ≤ n) {r q : ℕ} (hqr : q ≤ r) (hq : qH ≤ q)
    (hp : G.TreePackable univ r) {t : ℝ} (ht : 0 < t)
    (hnum : (q:ℝ) < (1-2*(16*((q:ℝ)^(-31/40:ℝ)/t+1/q)))*r) :
    ∃X ∈ G.matrixDomain, G.TreePackable (G.thresholdEdges (G.resistance X) (4*t)) q := by
  classical
  have hqp : 0 < q := by omega
  have hc : G.EdgeConnected 1 := fun S hS hS' => (by omega : 1 ≤ r).trans
    (G.treePackable_edgeConnected hp S hS hS')
  obtain ⟨X,hX,hconsistent⟩ := G.response_limit hn hc q ht (fun X _ =>
    hresp q hq n m G (by omega) (G.treePackable_mono_count hqr hp) (G.resistance X) t ht)
  obtain ⟨s,hs,havoid⟩ := (Set.Ioo_infinite (show 3*t < 4*t by linarith)).exists_notMem_finite
    (Set.finite_range (G.resistance X))
  have ha : ∀e, G.resistance X e ≠ s := fun e he => havoid ⟨e,he⟩
  have hpF := G.consistent_packable (by omega) hqp hp (by linarith [hs.1] : 2*t < s) hnum (hconsistent s ha)
  refine ⟨X,hX,G.treePackable_mono_edges ?_ hpF⟩
  intro e he
  exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp he).2.trans hs.2.le⟩

end StrongThinTree.MultiGraph

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.ExtractionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Filter
open scoped Topology
namespace StrongThinTree

lemma extractQ_bounds {r : ℕ} (hr : (4:ℝ) ≤ r) (hu : errorU r ≤ 1/4) :
    (r:ℝ)/2 ≤ extractQ r ∧ extractQ r ≤ r ∧
    (extractQ r:ℝ) ≤ (1-errorU r)*r ∧ (1-errorU r)*r-1 ≤ extractQ r := by
  have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg _
  have hu0 : 0 ≤ errorU r := Real.rpow_nonneg hr0 _
  have ha : 0 ≤ (1-errorU r)*r := mul_nonneg (by linarith) hr0
  have hl := Nat.sub_one_lt_floor ((1-errorU r)*r)
  have hh := Nat.floor_le ha
  change (extractQ r:ℝ) ≤ (1-errorU r)*r at hh
  change (1-errorU r)*r-1 < (extractQ r:ℝ) at hl
  have hmul := mul_le_mul_of_nonneg_right hu hr0
  have hmul0 := mul_nonneg hu0 hr0
  refine ⟨by linarith,?_,hh,hl.le⟩
  have hqr : (extractQ r:ℝ) ≤ r := by linarith
  exact_mod_cast hqr

lemma negative_power_q_bound {x y : ℝ} (hx : 0 < x) (hxy : x/2 ≤ y) :
    y^(-31/40:ℝ) ≤ 2*x^(-31/40:ℝ) := by
  have hh := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < x/2) hxy (by norm_num : (-31/40:ℝ) ≤ 0)
  have hp : (2:ℝ)^(31/40:ℝ) ≤ 2 := Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
  have heq : (x/2)^(-31/40:ℝ)=x^(-31/40:ℝ)*(2:ℝ)^(31/40:ℝ) := by
    rw [Real.div_rpow hx.le (by norm_num), div_eq_mul_inv, ←Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  rw [heq] at hh
  exact hh.trans (by nlinarith [Real.rpow_nonneg hx.le (-31/40:ℝ)])

lemma extract_response_ratio {r q : ℕ} (hr : 0 < r) (hqr : (r:ℝ)/2 ≤ q)
    (hsmall : 64*((r:ℝ)^(-17/80:ℝ)+(r:ℝ)^(-15/16:ℝ)) < 1) :
    2*(16*((q:ℝ)^(-31/40:ℝ)/resistanceT r + 1/q)) < errorU r := by
  have hrR : (0:ℝ) < r := Nat.cast_pos.mpr hr
  have hqR : (0:ℝ) < q := lt_of_lt_of_le (by positivity) hqr
  have ht : 0 < resistanceT r := Real.rpow_pos_of_pos hrR _
  have hu : 0 < errorU r := Real.rpow_pos_of_pos hrR _
  have hpow := negative_power_q_bound hrR hqr
  have hdiv := div_le_div_of_nonneg_right hpow ht.le
  have hinv : 1/(q:ℝ) ≤ 2/(r:ℝ) := by
    apply (div_le_div_iff₀ hqR hrR).mpr
    linarith
  have hid : 64*((r:ℝ)^(-17/80:ℝ)+(r:ℝ)^(-15/16:ℝ))*errorU r =
      32*(2*(r:ℝ)^(-31/40:ℝ)/resistanceT r+2/(r:ℝ)) := by
    unfold errorU resistanceT
    rw [mul_add, add_mul]
    have h1 : (r:ℝ)^(-17/80:ℝ)*(r:ℝ)^(-1/16:ℝ) =
        (r:ℝ)^(-31/40:ℝ)/(r:ℝ)^(-1/2:ℝ) := by
      rw [←Real.rpow_add hrR, ←Real.rpow_sub hrR]
      norm_num
    have h2 : (r:ℝ)^(-15/16:ℝ)*(r:ℝ)^(-1/16:ℝ) = 1/(r:ℝ) := by
      rw [←Real.rpow_add hrR]
      norm_num [Real.rpow_neg_one]
    calc
      _ = 64*((r:ℝ)^(-17/80:ℝ)*(r:ℝ)^(-1/16:ℝ))+
          64*((r:ℝ)^(-15/16:ℝ)*(r:ℝ)^(-1/16:ℝ)) := by ring
      _ = _ := by rw [h1,h2]; ring
  have hh := mul_lt_mul_of_pos_right hsmall hu
  rw [one_mul,hid] at hh
  linarith

lemma eventual_extraction_numeric (qH : ℕ) : ∃R : ℕ, 4 ≤ R ∧ ∀r : ℕ, R ≤ r →
    qH ≤ extractQ r ∧ extractQ r ≤ r ∧
    (extractQ r:ℝ) < (1-2*(16*((extractQ r:ℝ)^(-31/40:ℝ)/resistanceT r+1/extractQ r)))*r := by
  have hu : Tendsto (fun r : ℕ => errorU r) atTop (𝓝 0) := by
    simpa [errorU, Function.comp_def, neg_div] using (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/16)).comp tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun r : ℕ => 64*((r:ℝ)^(-17/80:ℝ)+(r:ℝ)^(-15/16:ℝ))) atTop (𝓝 0) := by
    simpa [Function.comp_def, neg_div] using (((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 17/80)).add
      (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 15/16))).const_mul 64).comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ r : ℕ in atTop, 4 ≤ r ∧ 2*qH ≤ r ∧ errorU r ≤ 1/4 ∧
      64*((r:ℝ)^(-17/80:ℝ)+(r:ℝ)^(-15/16:ℝ)) < 1 := by
    filter_upwards [eventually_ge_atTop 4,eventually_ge_atTop (2*qH),
      hu.eventually_lt_const (by norm_num : (0:ℝ) < 1/4),
      hsmall.eventually_lt_const (by norm_num : (0:ℝ) < 1)] with r hr hq hu hs
    exact ⟨hr,hq,hu.le,hs⟩
  obtain ⟨R,hR⟩ := eventually_atTop.mp hevent
  refine ⟨max R 4,le_max_right _ _,fun r hr => ?_⟩
  obtain ⟨hr4,hqr,hu,hs⟩ := hR r ((le_max_left _ _).trans hr)
  have hrR : (4:ℝ) ≤ r := by exact_mod_cast hr4
  obtain ⟨hqlo,hqhi,hqfrac,_⟩ := extractQ_bounds hrR hu
  have hsmall' := extract_response_ratio (by omega : 0 < r) hqlo hs
  have hqH : (qH:ℝ) ≤ extractQ r := by
    have hh : (2:ℝ)*qH ≤ r := by exact_mod_cast hqr
    linarith
  refine ⟨by exact_mod_cast hqH,hqhi,?_⟩
  have hh := mul_lt_mul_of_pos_right hsmall' (show (0:ℝ) < r by exact_mod_cast (by omega : 0 < r))
  linarith

end StrongThinTree

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Extraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Finset Matrix
open scoped MatrixOrder
namespace StrongThinTree.MultiGraph

theorem extraction : ∃R : ℕ, 4 ≤ R ∧ ∀r : ℕ, R ≤ r →
    ∀(n m : ℕ) (G : MultiGraph n m), 2 ≤ n → G.TreePackable univ r →
    ∃X ∈ G.matrixDomain,
      G.TreePackable (G.thresholdEdges (G.resistance X) (4*resistanceT r)) (extractQ r) := by
  obtain ⟨qH,hqH,hresponse⟩ := simultaneous_response_exists
  obtain ⟨R,hR,hnum⟩ := eventual_extraction_numeric qH
  refine ⟨R,hR,fun r hr n m G hn hp => ?_⟩
  obtain ⟨hq,hqr,hstrict⟩ := hnum r hr
  have ht : 0 < resistanceT r := Real.rpow_pos_of_pos
    (by exact_mod_cast (show 0 < r by omega)) _
  exact G.extraction_from_response_threshold hqH hresponse hn hqr hq hp ht hstrict
end StrongThinTree.MultiGraph

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.StepBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter
open scoped Topology
namespace StrongThinTree

lemma tendsto_errorU : Tendsto errorU atTop (𝓝 0) := by
  change Tendsto (fun r : ℕ => errorU r) atTop (𝓝 0)
  simpa [errorU,Function.comp_def,neg_div] using
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/16)).comp tendsto_natCast_atTop_atTop
lemma tendsto_resistanceT : Tendsto resistanceT atTop (𝓝 0) := by
  change Tendsto (fun r : ℕ => resistanceT r) atTop (𝓝 0)
  simpa [resistanceT,Function.comp_def,neg_div] using
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/2)).comp tendsto_natCast_atTop_atTop
lemma resistanceT_sq {r : ℕ} (hr : 0 < r) : resistanceT r^2=1/(r:ℝ) := by
  have hrR : (0:ℝ) < r := Nat.cast_pos.mpr hr
  unfold resistanceT
  rw [pow_two,←Real.rpow_add hrR]
  norm_num [Real.rpow_neg_one]
lemma splitTau_ratio {r : ℕ} (hr : 0 < r) :
    splitTau r=(2*Real.sqrt 6*(r:ℝ)^(-3/16:ℝ)+6*(r:ℝ)^(-7/16:ℝ))*errorU r := by
  have hrR : (0:ℝ) < r := Nat.cast_pos.mpr hr
  have hs : Real.sqrt (splitEpsilon r)=Real.sqrt 6*(r:ℝ)^(-1/4:ℝ) := by
    rw [splitEpsilon,resistanceT,Real.sqrt_mul (by norm_num),Real.sqrt_eq_rpow ((r:ℝ)^(-1/2:ℝ)),←Real.rpow_mul hrR.le]
    norm_num
  rw [splitTau,hs,splitEpsilon,resistanceT,errorU,add_mul]
  have h1 : (r:ℝ)^(-3/16:ℝ)*(r:ℝ)^(-1/16:ℝ)=(r:ℝ)^(-1/4:ℝ) := by
    rw [←Real.rpow_add hrR]; norm_num
  have h2 : (r:ℝ)^(-7/16:ℝ)*(r:ℝ)^(-1/16:ℝ)=(r:ℝ)^(-1/2:ℝ) := by
    rw [←Real.rpow_add hrR]; norm_num
  calc
    _ = 2*Real.sqrt 6*((r:ℝ)^(-3/16:ℝ)*(r:ℝ)^(-1/16:ℝ))+
        6*((r:ℝ)^(-7/16:ℝ)*(r:ℝ)^(-1/16:ℝ)) := by rw [h1,h2]; ring
    _ = _ := by ring

lemma inverse_le_errorU {r : ℕ} (hr : 1 ≤ r) : 1/(r:ℝ) ≤ errorU r := by
  have hh := Real.rpow_le_rpow_of_exponent_le
    (show (1:ℝ) ≤ r by exact_mod_cast hr) (by norm_num : (-1:ℝ) ≤ -1/16)
  simpa only [Real.rpow_neg_one,one_div,errorU] using hh

lemma step_rounding {r : ℕ} (hr : 4 ≤ r) (hu : errorU r ≤ 1/16)
    (hτ : splitTau r ≤ errorU r/2) :
    stepCount r ≤ ⌊(1/2-splitTau r)*(extractQ r:ℝ)/(1+errorU r)⌋₊ ∧
    (5/16:ℝ)*r ≤ stepCount r ∧ (stepCount r:ℝ) ≤ (r:ℝ)/2 ∧
    (1/2+3*splitTau r)*(r:ℝ) ≤ (1+15*errorU r)*stepCount r := by
  have hrR : (4:ℝ) ≤ r := by exact_mod_cast hr
  have hrp : (0:ℝ) < r := by linarith
  have hu0 : 0 ≤ errorU r := Real.rpow_nonneg hrp.le _
  have ht0 : 0 ≤ splitTau r := by unfold splitTau splitEpsilon resistanceT; positivity
  have hc : 0 ≤ 1/2-splitTau r := by linarith
  have hinv := inverse_le_errorU (by omega : 1 ≤ r)
  have hru : 1 ≤ errorU r*r := (div_le_iff₀ hrp).mp hinv
  obtain ⟨_,_,_,hq⟩ := extractQ_bounds hrR (by linarith)
  have hab : 0 ≤ (1-errorU r)*r-1 := by linarith
  have hm := mul_le_mul_of_nonneg_left hq hc
  have hτm := mul_le_mul_of_nonneg_right hτ hab
  have hur2 : 0 ≤ (r:ℝ)*(errorU r)^2 := mul_nonneg hrp.le (sq_nonneg _)
  have hpack : (1-4*errorU r)*r/2 ≤ (1/2-splitTau r)*(extractQ r:ℝ)/(1+errorU r) := by
    apply (le_div_iff₀ (by linarith : 0 < 1+errorU r)).mpr
    linarith
  have hfloorLo := Nat.sub_one_lt_floor ((1-4*errorU r)*r/2)
  have hfloorHi := Nat.floor_le (show 0 ≤ (1-4*errorU r)*r/2 by positivity [show 0 ≤ 1-4*errorU r by linarith])
  change (1-4*errorU r)*r/2-1 < (stepCount r:ℝ) at hfloorLo
  change (stepCount r:ℝ) ≤ (1-4*errorU r)*r/2 at hfloorHi
  have hcountLo : (1/2-3*errorU r)*r ≤ (stepCount r:ℝ) := by linarith
  have hcountPos : 0 ≤ (stepCount r:ℝ) := Nat.cast_nonneg _
  have hul := mul_le_mul_of_nonneg_right hu hrp.le
  have hum := mul_nonneg hu0 (show 0 ≤ 3-45*errorU r by linarith)
  have humr := mul_nonneg hrp.le hum
  have hproduct := mul_le_mul_of_nonneg_left hcountLo (show 0 ≤ 1+15*errorU r by positivity)
  refine ⟨Nat.floor_le_floor hpack,by linarith,by linarith,?_⟩
  have hτr := mul_le_mul_of_nonneg_right hτ hrp.le
  linarith

lemma eventual_step_numeric : ∃R : ℕ, ∀r : ℕ, R ≤ r → StepNumeric r := by
  have htau : Tendsto (fun r : ℕ => 2*Real.sqrt 6*(r:ℝ)^(-3/16:ℝ)+6*(r:ℝ)^(-7/16:ℝ)) atTop (𝓝 0) := by
    simpa [Function.comp_def,neg_div] using
      (((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 3/16)).const_mul (2*Real.sqrt 6)).add
        ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 7/16)).const_mul 6)).comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ r : ℕ in atTop, 4 ≤ r ∧ errorU r ≤ 1/16 ∧ resistanceT r ≤ 1/2 ∧
      2*Real.sqrt 6*(r:ℝ)^(-3/16:ℝ)+6*(r:ℝ)^(-7/16:ℝ) ≤ 1/2 := by
    filter_upwards [eventually_ge_atTop 4,
      tendsto_errorU.eventually_lt_const (by norm_num : (0:ℝ) < 1/16),
      tendsto_resistanceT.eventually_lt_const (by norm_num : (0:ℝ) < 1/2),
      htau.eventually_lt_const (by norm_num : (0:ℝ) < 1/2)] with r hr hu ht hτ
    exact ⟨hr,hu.le,ht.le,hτ.le⟩
  obtain ⟨R,hR⟩ := eventually_atTop.mp hev
  refine ⟨R,fun r hr => ?_⟩
  obtain ⟨hr4,hu,ht,hτ⟩ := hR r hr
  have hrp : 0 < r := by omega
  have hrR : (0:ℝ) < r := Nat.cast_pos.mpr hrp
  have hu0 : 0 ≤ errorU r := Real.rpow_nonneg hrR.le _
  have hτsmall : splitTau r ≤ errorU r/2 := by
    rw [splitTau_ratio hrp]
    have hh := mul_le_mul_of_nonneg_right hτ hu0
    linarith
  obtain ⟨hpack,hlo,hhi,hratio⟩ := step_rounding hr4 hu hτsmall
  obtain ⟨hqlo,_,_,_⟩ := extractQ_bounds (by exact_mod_cast hr4) (by linarith)
  have hqp : (0:ℝ) < extractQ r := by linarith
  have htpos : 0 < resistanceT r := Real.rpow_pos_of_pos hrR _
  have hinv : 4/(r:ℝ) ≤ 2*resistanceT r := by
    have hh := resistanceT_sq hrp
    have hmul := mul_le_mul_of_nonneg_left ht htpos.le
    rw [show 4/(r:ℝ)=4*(resistanceT r)^2 by rw [hh]; ring]
    linarith
  have hsize : (1+errorU r)/(extractQ r:ℝ) ≤ 2*resistanceT r := by
    apply le_trans _ hinv
    apply (div_le_div_iff₀ hqp hrR).mpr
    linarith
  exact ⟨hr4,hu,by exact_mod_cast hqp,hsize,hτsmall,hpack,hlo,hhi,hratio⟩
end StrongThinTree

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Sparsification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Finset
namespace StrongThinTree.MultiGraph

theorem sparsification : ∃R : ℕ, 4 ≤ R ∧ ∀r : ℕ, R ≤ r → StepNumeric r ∧
    ∀(n m : ℕ) (G : MultiGraph n m), 2 ≤ n → G.TreePackable univ r →
      ∃A : Finset (Fin m), G.TreePackable A (stepCount r) ∧
        ∀S : Finset (Fin n), S.Nonempty → S ≠ univ →
          ((G.cut A S).card:ℝ) ≤ (1/2+3*splitTau r)*(G.cut univ S).card := by
  obtain ⟨RE,hRE,hE⟩ := extraction
  obtain ⟨RN,hN⟩ := eventual_step_numeric
  refine ⟨max RE RN,hRE.trans (le_max_left _ _),fun r hr => ?_⟩
  have hn := hN r ((le_max_right _ _).trans hr)
  refine ⟨hn,fun n m G hn' hp => ?_⟩
  obtain ⟨X,hX,hpack⟩ := hE r ((le_max_left _ _).trans hr) n m G hn' hp
  exact G.sparsify_from_extraction hn' hn hX hpack
end StrongThinTree.MultiGraph

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Restriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Finset
namespace StrongThinTree.MultiGraph
variable {n m : ℕ} (G : MultiGraph n m)

lemma embedding_mem (F : Finset (Fin m)) (e : Fin F.card) : edgeEmbedding F e ∈ F :=
  (F.equivFin.symm e).property
lemma embedding_surj (F : Finset (Fin m)) {e : Fin m} (he : e ∈ F) :
    ∃i : Fin F.card, edgeEmbedding F i=e := by
  refine ⟨F.equivFin ⟨e,he⟩,?_⟩
  change (F.equivFin.symm (F.equivFin ⟨e,he⟩)).val=e
  simp
lemma lift_univ (F : Finset (Fin m)) : liftEdges F univ=F := by
  ext e
  simp only [liftEdges,mem_map,mem_univ,true_and]
  exact ⟨fun ⟨i,hi⟩ => hi ▸ embedding_mem F i, embedding_surj F⟩
lemma lift_lower (F T : Finset (Fin m)) (hT : T ⊆ F) : liftEdges F (lowerEdges F T)=T := by
  ext e
  simp only [liftEdges,lowerEdges,mem_map,mem_preimage]
  refine ⟨fun ⟨i,hi,hie⟩ => hie ▸ hi,fun he => ?_⟩
  obtain ⟨i,rfl⟩ := embedding_surj F (hT he)
  exact ⟨i,he,rfl⟩
lemma restrict_cut (F : Finset (Fin m)) (T : Finset (Fin F.card)) (S : Finset (Fin n)) :
    liftEdges F ((G.restrict F).cut T S)=G.cut (liftEdges F T) S := by
  ext e
  simp only [liftEdges,cut,mem_map,mem_filter]
  constructor
  · rintro ⟨i,⟨hi,hc⟩,rfl⟩
    exact ⟨⟨i,hi,rfl⟩,hc⟩
  · rintro ⟨⟨i,hi,rfl⟩,hc⟩
    exact ⟨i,⟨hi,hc⟩,rfl⟩
lemma restrict_cut_card (F : Finset (Fin m)) (T : Finset (Fin F.card)) (S : Finset (Fin n)) :
    ((G.restrict F).cut T S).card=(G.cut (liftEdges F T) S).card := by
  rw [←G.restrict_cut]
  exact (card_map _).symm
lemma restrict_connected (F : Finset (Fin m)) (T : Finset (Fin F.card)) :
    (G.restrict F).Connected T ↔ G.Connected (liftEdges F T) := by
  unfold Connected
  constructor <;> intro h S hS hS'
  · rw [←G.restrict_cut]
    exact map_nonempty.mpr (h S hS hS')
  · apply (map_nonempty (f := edgeEmbedding F)).mp
    change (liftEdges F ((G.restrict F).cut T S)).Nonempty
    rw [G.restrict_cut]
    exact h S hS hS'
lemma restrict_spanningTree (F : Finset (Fin m)) (T : Finset (Fin F.card)) :
    (G.restrict F).SpanningTree T ↔ G.SpanningTree (liftEdges F T) := by
  constructor
  · rintro ⟨hc,hmin⟩
    refine ⟨(G.restrict_connected F T).mp hc,?_⟩
    intro e he hh
    obtain ⟨i,hi,rfl⟩ := mem_map.mp he
    apply hmin i hi
    apply (G.restrict_connected F (T.erase i)).mpr
    simpa only [liftEdges,map_erase] using hh
  · rintro ⟨hc,hmin⟩
    refine ⟨(G.restrict_connected F T).mpr hc,?_⟩
    intro e he hh
    apply hmin (edgeEmbedding F e) (mem_map.mpr ⟨e,he,rfl⟩)
    have hh' := (G.restrict_connected F (T.erase e)).mp hh
    simpa only [liftEdges,map_erase] using hh'
lemma restrict_packable (F : Finset (Fin m)) {r : ℕ} (h : G.TreePackable F r) :
    (G.restrict F).TreePackable univ r := by
  obtain ⟨T,hT,hd⟩ := h
  refine ⟨fun i => lowerEdges F (T i),fun i => ⟨subset_univ _,?_⟩,?_⟩
  · apply (G.restrict_spanningTree F _).mpr
    rw [lift_lower F (T i) (hT i).1]
    exact (hT i).2
  · intro i j hij
    exact disjoint_preimage (hd hij)
end StrongThinTree.MultiGraph

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.IterationBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace StrongThinTree

lemma iterationB_pos : 0 < iterationB := by
  unfold iterationB
  exact div_pos (by norm_num) (sub_pos.mpr (Real.one_lt_rpow (by norm_num) (by norm_num)))
lemma errorU_nonneg (r : ℕ) : 0 ≤ errorU r := Real.rpow_nonneg (Nat.cast_nonneg _) _
lemma errorU_le_one {r : ℕ} (hr : 1 ≤ r) : errorU r ≤ 1 := by
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hr) (by norm_num)
lemma iterationPotential_pos (r : ℕ) : 0 < iterationPotential r := Real.exp_pos _
lemma iterationPotential_one_le {r : ℕ} (hr : 1 ≤ r) : 1 ≤ iterationPotential r := by
  exact Real.one_le_exp (mul_nonneg iterationB_pos.le (sub_nonneg.mpr (errorU_le_one hr)))
lemma iterationPotential_le (r : ℕ) : iterationPotential r ≤ Real.exp iterationB := by
  apply Real.exp_le_exp.mpr
  have := mul_nonneg iterationB_pos.le (errorU_nonneg r)
  linarith

lemma errorU_halving {r s : ℕ} (hs : 0 < s) (hrs : (s:ℝ) ≤ (r:ℝ)/2) :
    (2:ℝ)^(1/16:ℝ)*errorU r ≤ errorU s := by
  have hsR : (0:ℝ) < s := Nat.cast_pos.mpr hs
  have hrR : (0:ℝ) < r := by linarith
  have hh := Real.rpow_le_rpow_of_nonpos hsR hrs (by norm_num : (-1/16:ℝ) ≤ 0)
  rw [Real.div_rpow hrR.le (by norm_num)] at hh
  have hi : (2:ℝ)^(-1/16:ℝ)=((2:ℝ)^(1/16:ℝ))⁻¹ := by
    rw [show (-1/16:ℝ)=-(1/16:ℝ) by ring,Real.rpow_neg (by norm_num)]
  simpa only [hi,div_inv_eq_mul,mul_comm,errorU] using hh

lemma iterationPotential_step {r s : ℕ} (hs : 0 < s) (hrs : (s:ℝ) ≤ (r:ℝ)/2) :
    (1+15*errorU r)*iterationPotential s ≤ iterationPotential r := by
  have hd : 0 < (2:ℝ)^(1/16:ℝ)-1 :=
    sub_pos.mpr (Real.one_lt_rpow (by norm_num) (by norm_num))
  have hm := mul_le_mul_of_nonneg_left (errorU_halving hs hrs) iterationB_pos.le
  have hB : iterationB*((2:ℝ)^(1/16:ℝ)-1)=15 := by
    unfold iterationB
    exact div_mul_cancel₀ _ (ne_of_gt hd)
  have hdiff : 15*errorU r ≤ iterationB*(errorU s-errorU r) := by
    have hBu := congrArg (fun x : ℝ => x*errorU r) hB
    linarith
  have he : 1+15*errorU r ≤ Real.exp (15*errorU r) := by
    simpa only [add_comm] using Real.add_one_le_exp (15*errorU r)
  calc
    _ ≤ Real.exp (15*errorU r)*iterationPotential s :=
      mul_le_mul_of_nonneg_right he (iterationPotential_pos s).le
    _ = Real.exp (15*errorU r+iterationB*(1-errorU s)) := by
      rw [iterationPotential,Real.exp_add]
    _ ≤ iterationPotential r := by
      apply Real.exp_le_exp.mpr
      linarith

lemma iteration_coefficient_step {r : ℕ} (h : StepNumeric r) :
    iterationPotential (stepCount r)/(stepCount r:ℝ)*(1/2+3*splitTau r) ≤
      iterationPotential r/(r:ℝ) := by
  have hrR : (0:ℝ) < r := by exact_mod_cast (show 0 < r by have := h.rlarge; omega)
  have hsR : (0:ℝ) < stepCount r := lt_of_lt_of_le (by positivity) h.lower
  have hs : 0 < stepCount r := Nat.cast_pos.mp hsR
  rw [div_mul_eq_mul_div]
  apply (div_le_div_iff₀ hsR hrR).mpr
  have hp := iterationPotential_step hs h.upper
  have hm := mul_le_mul_of_nonneg_left h.ratio (iterationPotential_pos (stepCount r)).le
  have hp' := mul_le_mul_of_nonneg_right hp hsR.le
  linarith
end StrongThinTree

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Iteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Finset
namespace StrongThinTree.MultiGraph

lemma cut_card_le_full {n m : ℕ} (G : MultiGraph n m) (T : Finset (Fin m))
    (S : Finset (Fin n)) : (G.cut T S).card ≤ (G.cut univ S).card := by
  exact card_le_card (filter_subset_filter _ (subset_univ T))

theorem packing_thinness : ∃C : ℝ, 0 < C ∧ ∀r : ℕ, 1 ≤ r →
    ∀(n m : ℕ) (G : MultiGraph n m), 2 ≤ n → G.TreePackable univ r →
      ∃T : Finset (Fin m), G.SpanningTree T ∧
        ∀S : Finset (Fin n), S.Nonempty → S ≠ univ →
          ((G.cut T S).card:ℝ) ≤ C/(r:ℝ)*(G.cut univ S).card := by
  obtain ⟨R,hR,hstep⟩ := sparsification
  have hRR : (0:ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  have hI : ∀r : ℕ, 1 ≤ r → ∀(n m : ℕ) (G : MultiGraph n m),
      2 ≤ n → G.TreePackable univ r →
        ∃T : Finset (Fin m), G.SpanningTree T ∧
          ∀S : Finset (Fin n), S.Nonempty → S ≠ univ →
            ((G.cut T S).card:ℝ) ≤
              R*(iterationPotential r/(r:ℝ))*(G.cut univ S).card := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro hr n m G hn hp
      have hrR : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
      by_cases hlarge : R ≤ r
      · obtain ⟨hnum,hstep'⟩ := hstep r hlarge
        obtain ⟨A,hA,hcuts⟩ := hstep' n m G hn hp
        have hsR : (0:ℝ) < stepCount r :=
          lt_of_lt_of_le (by positivity) hnum.lower
        have hs : 1 ≤ stepCount r := by exact_mod_cast hsR
        have hlt : stepCount r < r := by
          have hh : (stepCount r:ℝ) < r := by linarith [hnum.upper]
          exact_mod_cast hh
        obtain ⟨T,hT,hthin⟩ := ih (stepCount r) hlt hs n A.card (G.restrict A) hn
          (G.restrict_packable A hA)
        refine ⟨liftEdges A T,(G.restrict_spanningTree A T).mp hT,?_⟩
        intro S hS hS'
        have ht := hthin S hS hS'
        rw [G.restrict_cut_card,G.restrict_cut_card,lift_univ] at ht
        have hcoef : 0 ≤ R*(iterationPotential (stepCount r)/(stepCount r:ℝ)) :=
          mul_nonneg hRR.le (div_nonneg (iterationPotential_pos _).le hsR.le)
        calc
          _ ≤ R*(iterationPotential (stepCount r)/(stepCount r:ℝ))*(G.cut A S).card := ht
          _ ≤ R*(iterationPotential (stepCount r)/(stepCount r:ℝ))*
              ((1/2+3*splitTau r)*(G.cut univ S).card) :=
            mul_le_mul_of_nonneg_left (hcuts S hS hS') hcoef
          _ = R*(iterationPotential (stepCount r)/(stepCount r:ℝ)*(1/2+3*splitTau r))*
              (G.cut univ S).card := by ring
          _ ≤ R*(iterationPotential r/(r:ℝ))*(G.cut univ S).card :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (iteration_coefficient_step hnum) hRR.le)
              (Nat.cast_nonneg _)
      · obtain ⟨F,hF,_⟩ := hp
        let i : Fin r := ⟨0,by omega⟩
        refine ⟨F i,(hF i).2,?_⟩
        intro S _ _
        have hrleR : (r:ℝ) ≤ R := by exact_mod_cast (show r ≤ R by omega)
        have hcoef : 1 ≤ R*(iterationPotential r/(r:ℝ)) := by
          rw [←mul_div_assoc]
          apply (le_div_iff₀ hrR).mpr
          have hh := mul_le_mul_of_nonneg_left (iterationPotential_one_le hr) hRR.le
          linarith
        have hc : ((G.cut (F i) S).card:ℝ) ≤ (G.cut univ S).card := by
          exact_mod_cast G.cut_card_le_full (F i) S
        exact hc.trans (le_mul_of_one_le_left (Nat.cast_nonneg _) hcoef)
  refine ⟨R*Real.exp iterationB,mul_pos hRR (Real.exp_pos _),?_⟩
  intro r hr n m G hn hp
  obtain ⟨T,hT,hthin⟩ := hI r hr n m G hn hp
  refine ⟨T,hT,fun S hS hS' => (hthin S hS hS').trans ?_⟩
  have hrR : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [←mul_div_assoc]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (iterationPotential_le r) hRR.le) hrR.le

end StrongThinTree.MultiGraph

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Finset
namespace StrongThinTree.MultiGraph

lemma connected_has_spanningTree {n m : ℕ} (G : MultiGraph n m)
    (hG : G.Connected univ) : ∃T : Finset (Fin m), G.SpanningTree T := by
  classical
  let A : Finset (Finset (Fin m)) := univ.filter G.Connected
  have hA : A.Nonempty := ⟨univ,by simp only [A,mem_filter,mem_univ,true_and]; exact hG⟩
  obtain ⟨T,hT,hmin⟩ := exists_min_image A Finset.card hA
  refine ⟨T,(mem_filter.mp hT).2,?_⟩
  intro e he hc
  have hh := hmin (T.erase e) (by simp only [A,mem_filter,mem_univ,true_and]; exact hc)
  exact (not_le_of_gt (card_erase_lt_of_mem he)) hh

end MultiGraph

theorem strongThinTree_oai : MainStatement := by
  obtain ⟨C₀,hC₀,hpacking⟩ := MultiGraph.packing_thinness
  let C : ℝ := 3*max C₀ 1
  have hm : 1 ≤ max C₀ 1 := le_max_right _ _
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨C,hC,?_⟩
  intro k hk n m hn G hc
  by_cases hk2 : 2 ≤ k
  · let r := k/2
    have hr : 0 < r := Nat.div_pos hk2 (by norm_num)
    have hr' : 1 ≤ r := hr
    have hconn : G.EdgeConnected (2*r) := by
      intro S hS hS'
      exact (show 2*r ≤ k by dsimp [r]; omega).trans (hc S hS hS')
    have hpack := G.edgeConnected_treePackable hr (by omega) hconn
    obtain ⟨T,hT,hthin⟩ := hpacking r hr' n m G hn hpack
    refine ⟨T,hT,fun S hS hS' => (hthin S hS hS').trans ?_⟩
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    have hrR : (0:ℝ) < r := Nat.cast_pos.mpr hr
    have hkR : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    apply (div_le_div_iff₀ hrR hkR).mpr
    have hkr : (k:ℝ) ≤ 3*(r:ℝ) := by exact_mod_cast (show k ≤ 3*r by dsimp [r]; omega)
    have h1 := mul_le_mul_of_nonneg_left hkr hC₀.le
    have h2 := mul_le_mul_of_nonneg_right (le_max_left C₀ 1) hrR.le
    dsimp [C]
    linarith
  · have hk1 : k=1 := by omega
    subst k
    have hconn : G.Connected univ := by
      intro S hS hS'
      exact card_pos.mp (hc S hS hS')
    obtain ⟨T,hT⟩ := G.connected_has_spanningTree hconn
    refine ⟨T,hT,?_⟩
    intro S _ _
    have hh : ((G.cut T S).card:ℝ) ≤ (G.cut univ S).card := by
      exact_mod_cast G.cut_card_le_full T S
    have hCle : 1 ≤ C := by dsimp [C]; linarith
    simpa only [Nat.cast_one,div_one] using
      hh.trans (le_mul_of_one_le_left (Nat.cast_nonneg _) hCle)

end StrongThinTree

end

end

end OAI
end

theorem solution : type_of% @OAI.StrongThinTree.strongThinTree_oai := @OAI.StrongThinTree.strongThinTree_oai
