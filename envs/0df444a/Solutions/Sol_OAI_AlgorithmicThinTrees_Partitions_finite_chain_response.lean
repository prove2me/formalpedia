-- Prove2me | solution 1 for OAI.AlgorithmicThinTrees.Partitions.finite_chain_response
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:55:27.726077+00:00
-- url     : https://prove2.me/submissions/7428ab30-ad36-4f4f-bc04-2acf23301b48

import Mathlib
import Definitions.Def_AlgorithmicThinTrees
import Definitions.Def_OAIQ241TT006
import Theorems.Thm_OAI_AlgorithmicThinTrees_MetricTests_polynomial_nuclear_bound

section
-- module Solutions.OAIQ241_TT.Compat
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Duality
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
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
  have hv₀ : v₀ ∈ strictUpperImage S F := ⟨x₀,hx₀,fun i => by dsimp [v₀] <;> linarith⟩
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
      exact (show F j x₀ < v₀ j by dsimp [v₀] <;> linarith).trans_le (le_add_of_nonneg_right (mul_nonneg ht hj))
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
      nlinarith only [hh,congrArg (fun z : ℝ => z*K) hab]
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
    nlinarith only [congrArg (fun t : ℝ => t*(v ⬝ᵥ z)) hab]
  change v ⬝ᵥ (D⁻¹ *ᵥ v) ≤ a*(v ⬝ᵥ (X⁻¹ *ᵥ v))+b*(v ⬝ᵥ (Y⁻¹ *ᵥ v))
  rw [hDv]
  change 2*(v ⬝ᵥ z)-z ⬝ᵥ (D *ᵥ z) ≤ _
  rw [hf]
  exact add_le_add (mul_le_mul_of_nonneg_left hXv ha) (mul_le_mul_of_nonneg_left hYv hb)

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
    nlinarith only [mul_nonneg ht.le hD.inv.posSemidef.trace_nonneg,
      mul_nonneg ht.le hD.posSemidef.trace_nonneg]
  exact ⟨D,hD,hterms.trans_lt (heq.trans_lt htK)⟩
end
end StrongThinTree.MatrixDual

namespace StrongThinTree.ShortcutDual
noncomputable section
open Matrix Finset Filter Topology
open scoped Classical MatrixOrder Matrix.Norms.L2Operator
variable {V : Type uV3} {E : Type uE2} {T : Type uT} {J : Type uJ3} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype T] [Fintype J]

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

end
end StrongThinTree.ShortcutDual

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_ShortcutDuality
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.Partitions.mem_crossing
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

end
end StrongThinTree.MultiGraph

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Matrix
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
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
    nlinarith
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
-- module Solutions.OAIQ241_TT.ThinTrees_GraphMatrix
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
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
omit [Fintype V] [DecidableEq V] in
lemma posDef_of_le {X Y : Matrix V V ℝ} (hX : X.PosDef) (hXY : X ≤ Y) : Y.PosDef := by
  convert hX.add_posSemidef (Matrix.le_iff.mp hXY) using 1 <;> first | (with_reducible_and_instances rfl) | (abel)

namespace MultiGraph
variable {n m : ℕ} (G : MultiGraph n m)
lemma laplacian_qform (F : Finset (Fin m)) (v : Fin n → ℝ) :
    qform (G.laplacian F) v=∑e ∈ F, (v (G.left e)-v (G.right e))^2 := by
  simp only [laplacian,qform,sum_mulVec,dotProduct_sum,rankOne_quadratic]
  apply sum_congr rfl
  intro e _
  rw [dotProduct_comm]
  congr 1
  exact G.eval_incidence v e

end MultiGraph
end StrongThinTree

end
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_MatrixDomain
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
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
lemma isClosed_matrixAbove (A : Matrix V V ℝ) : IsClosed {X : Matrix V V ℝ | A ≤ X} :=
  isClosed_psd.preimage (continuous_id.sub continuous_const)
end StrongThinTree

end
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_HierarchyBounds
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.Partitions.mem_crossing
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

lemma eventually_const_mul_rpow_le_rpow (c : ℝ) {a b : ℝ} (hab : a < b) :
    ∀ᶠ x : ℝ in atTop, c*x^a ≤ x^b := by
  have hh := (tendsto_rpow_atTop (sub_pos.mpr hab)).eventually (eventually_ge_atTop c)
  filter_upwards [hh,eventually_gt_atTop (0:ℝ)] with x hx hxp
  calc
    c*x^a ≤ x^(b-a)*x^a := mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg hxp.le _)
    _ = x^b := by rw [←Real.rpow_add hxp]; congr 1; ring

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

end StrongThinTree.MultiGraph.Hierarchy

end
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_HierarchyBuilder
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
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
-- module Solutions.OAIQ241_TT.ThinTrees_ChainEdges
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.Partitions.mem_crossing
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
-- module Solutions.OAIQ241_TT.ThinTrees_DyadicSelection
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
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
    _ ≤ 4*(M i : ℝ) := by rw [pow_succ]; nlinarith

end
end StrongThinTree.Dyadic

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_ResponseBounds
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.Partitions.mem_crossing
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
-- module Solutions.OAIQ241_TT.ThinTrees_HierarchyResponse
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
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

end MultiGraph
end StrongThinTree

end
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Representation
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.Partitions.mem_crossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι uE uT uI uE2 uE3 uV uE4 uV2 uW

section

open Matrix Finset
open scoped BigOperators MatrixOrder Matrix.Norms.Elementwise

namespace StrongThinTree.MultiGraph
noncomputable section
open Matrix Finset
open scoped BigOperators
variable {n m : ℕ} (G : MultiGraph n m)

lemma edgeSpan_le_zeroSum (T : Finset (Fin m)) : G.edgeSpan T ≤ zeroSumSpace n :=
  (Packing.span_le_iff G.incidence).mpr (fun e _he => G.incidence_zeroSum e)

lemma connected_span_zeroSum {T : Finset (Fin m)} (hn : 0 < n) (hT : G.Connected T) :
    G.edgeSpan T = zeroSumSpace n := by
  apply le_antisymm (G.edgeSpan_le_zeroSum T)
  intro x hx
  have hx0 := (mem_zeroSumSpace x).mp hx
  let u₀ : Fin n := ⟨0, hn⟩
  have hs : ∑ u, x u • (point u - point u₀) ∈ G.edgeSpan T := by
    apply Submodule.sum_mem
    intro u hu
    exact Submodule.smul_mem _ _ ((G.connected_iff_same T).mp hT u u₀)
  have heq : ∑ u, x u • (point u - point u₀) = x := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hx0, zero_smul, sub_zero]
    ext u
    simp [point, Pi.single_apply, Finset.sum_apply, mul_ite]
  rwa [heq] at hs

end
end StrongThinTree.MultiGraph

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Metric_MatrixBound
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric matrix bound. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder

variable {n m d : ℕ}

lemma test_zero : Test (0 : Matrix (Fin n) (Fin n) ℝ) := by
  refine ⟨Matrix.PosSemidef.zero,?_⟩
  intro u v w
  simp [qform]

lemma test_add {X Y : Matrix (Fin n) (Fin n) ℝ} (hX : Test X) (hY : Test Y) :
    Test (X+Y) := by
  refine ⟨hX.1.add hY.1,?_⟩
  intro u v w
  simp only [qform_add]
  linarith only [hX.2 u v w,hY.2 u v w]

lemma test_smul {X : Matrix (Fin n) (Fin n) ℝ} (hX : Test X) {a : ℝ} (ha : 0 ≤ a) :
    Test (a • X) := by
  refine ⟨hX.1.smul ha,?_⟩
  intro u v w
  simpa only [qform_smul,mul_add] using mul_le_mul_of_nonneg_left (hX.2 u v w) ha

lemma test_sum {I : Type*} (S : Finset I) (X : I → Matrix (Fin n) (Fin n) ℝ)
    (hX : ∀i ∈ S, Test (X i)) : Test (∑i ∈ S, X i) := by
  induction S using Finset.induction_on with
  | empty => simpa using test_zero (n := n)
  | @insert i S hi ih =>
    rw [sum_insert hi]
    exact test_add (hX i (mem_insert_self _ _)) (ih (fun j hj => hX j (mem_insert_of_mem hj)))

lemma sqrt_gram {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Z.PosSemidef) :
    (CFC.sqrt Z)ᵀ*CFC.sqrt Z=Z := by
  rw [isHermitian_iff_isSymm.mp (CFC.sqrt_nonneg Z).posSemidef.isHermitian]
  exact CFC.sqrt_mul_sqrt_self Z hZ.nonneg

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Metric_CenteredMatrices
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.Partitions.mem_crossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Centered matrices. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder

variable {n m : ℕ}

lemma ones_dot (x : Fin n → ℝ) : ones n ⬝ᵥ x=∑i, x i := by
  simp [ones,dotProduct]

lemma constantProjection_mulVec (x : Fin n → ℝ) :
    constantProjection n *ᵥ x=((∑i, x i)/(n:ℝ)) • ones n := by
  ext j
  simp [constantProjection,mulVec,dotProduct,Matrix.smul_apply,vecMulVec,ones,div_eq_mul_inv,Finset.sum_mul,mul_comm]

lemma qform_constantProjection (x : Fin n → ℝ) :
    qform (constantProjection n) x=(∑i, x i)^2/(n:ℝ) := by
  rw [qform,constantProjection_mulVec,dotProduct_smul,dotProduct_comm x,ones_dot]
  simp only [smul_eq_mul]
  ring

lemma centering_mulVec (x : Fin n → ℝ) :
    centering n *ᵥ x=x-((∑i, x i)/(n:ℝ)) • ones n := by
  rw [centering,sub_mulVec,one_mulVec,constantProjection_mulVec]

lemma centering_mulVec_of_sum_zero {x : Fin n → ℝ} (hx : ∑i, x i=0) :
    centering n *ᵥ x=x := by
  simp only [centering_mulVec,hx,zero_div,zero_smul,sub_zero]

lemma centering_mulVec_sum (hn : 0 < n) (x : Fin n → ℝ) :
    ∑i, (centering n *ᵥ x) i=0 := by
  rw [centering_mulVec]
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,ones,sum_sub_distrib,mul_one,
    sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp
  ring

lemma constantProjection_ones (hn : 0 < n) : constantProjection n *ᵥ ones n=ones n := by
  rw [constantProjection_mulVec]
  simp only [ones,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  rw [div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)),one_smul]

lemma centering_ones (hn : 0 < n) : centering n *ᵥ ones n=0 := by
  rw [centering,sub_mulVec,one_mulVec,constantProjection_ones hn,sub_self]

lemma centered_dot (b y : Fin n → ℝ) (hb : ∑i, b i=0) :
    b ⬝ᵥ (centering n *ᵥ y)=b ⬝ᵥ y := by
  rw [dotProduct_mulVec,←mulVec_transpose,centering_symmetric,centering_mulVec_of_sum_zero hb]

lemma centered_psd {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.PosSemidef) : (centered D).PosSemidef := by
  have hh := hD.mul_mul_conjTranspose_same (centering n)
  simpa only [centered,conjTranspose_eq_transpose_of_trivial,centering_symmetric] using hh

lemma centered_ones (hn : 0 < n) (D : Matrix (Fin n) (Fin n) ℝ) : centered D *ᵥ ones n=0 := by
  simp only [centered,←mulVec_mulVec,centering_ones hn,mulVec_zero]

lemma qform_centered (D : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    qform (centered D) x=qform D (centering n *ᵥ x) := by
  unfold centered qform
  rw [←mulVec_mulVec,←mulVec_mulVec,dotProduct_mulVec,←mulVec_transpose,centering_symmetric]

lemma centered_positive (hn : 0 < n) {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.PosDef) :
    CenteredPositive (centered D) := by
  refine ⟨(centered_psd hD.posSemidef).isHermitian,centered_ones hn D,?_⟩
  intro x hx hne
  rw [qform_centered,centering_mulVec_of_sum_zero hx]
  simpa only [qform,star_trivial] using hD.dotProduct_mulVec_pos hne

lemma regularize_centered_pd (hn : 0 < n) {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.PosDef) :
    (regularize (centered D)).PosDef := by
  apply PosDef.of_dotProduct_mulVec_pos
    ((centered_psd hD.posSemidef).add constantProjection_psd).isHermitian
  intro x hx
  change 0 < qform (regularize (centered D)) x
  rw [regularize,qform_add,qform_centered]
  by_cases hp : centering n *ᵥ x=0
  · have hs : (∑i, x i) ≠ 0 := by
      intro hs
      rw [centering_mulVec_of_sum_zero hs] at hp
      exact hx hp
    have hq : 0 < qform (constantProjection n) x := by
      rw [qform_constantProjection]
      exact div_pos (sq_pos_of_ne_zero hs) (Nat.cast_pos.mpr hn)
    exact add_pos_of_nonneg_of_pos (qform_nonneg hD.posSemidef _) hq
  · have hq : 0 < qform D (centering n *ᵥ x) := by
      simpa only [qform,star_trivial] using hD.dotProduct_mulVec_pos hp
    exact add_pos_of_pos_of_nonneg hq (qform_nonneg constantProjection_psd _)

lemma inverse_centered_le (hn : 0 < n) {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : D.PosDef) {b : Fin n → ℝ} (hb : (∑i, b i)=0) :
    qform (inverseOnZeroSum (centered D)) b ≤ qform D⁻¹ b := by
  let A := regularize (centered D)
  have hA : A.PosDef := regularize_centered_pd hn hD
  let y := A⁻¹ *ᵥ b
  have hs : A *ᵥ y=b := posDef_solve hA b
  have hq : qform D (centering n *ᵥ y) ≤ b ⬝ᵥ y := by
    have hh : qform A y=b ⬝ᵥ y := by rw [qform,hs,dotProduct_comm]
    dsimp [A] at hh
    rw [regularize,qform_add,qform_centered] at hh
    linarith only [hh,qform_nonneg (constantProjection_psd (n:=n)) y]
  have hv := MatrixDual.inverse_quadratic_variational hD b (centering n *ᵥ y)
  rw [centered_dot b y hb] at hv
  change 2*(b ⬝ᵥ y)-qform D (centering n *ᵥ y) ≤ qform D⁻¹ b at hv
  change b ⬝ᵥ y ≤ qform D⁻¹ b
  linarith only [hv,hq]

lemma centeredTest_mul_constant {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : CenteredTest Z) :
    Z*constantProjection n=0 := by
  have h0 : Z *ᵥ ones n=0 := hZ.2
  simp only [constantProjection,mul_smul_comm,mul_vecMulVec,h0,zero_vecMulVec,smul_zero]

lemma centeredTest_constant_mul {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : CenteredTest Z) :
    constantProjection n*Z=0 := by
  have hh := congrArg transpose (centeredTest_mul_constant hZ)
  simpa only [transpose_mul,constantProjection_symmetric,
    (isHermitian_iff_isSymm.mp hZ.1.1.isHermitian).eq,transpose_zero] using hh

lemma centeredTest_mul_centering {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : CenteredTest Z) :
    Z*centering n=Z := by
  rw [centering,mul_sub,mul_one,centeredTest_mul_constant hZ,sub_zero]

lemma centeredTest_centering_mul {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : CenteredTest Z) :
    centering n*Z=Z := by
  rw [centering,sub_mul,one_mul,centeredTest_constant_mul hZ,sub_zero]

lemma centered_trace (D : Matrix (Fin n) (Fin n) ℝ)
    {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : CenteredTest Z) :
    (centered D*Z).trace=(D*Z).trace := by
  rw [centered,mul_assoc (centering n*D),centeredTest_centering_mul hZ,
    mul_assoc,trace_mul_comm,mul_assoc,centeredTest_mul_centering hZ]

lemma regularize_trace (D : Matrix (Fin n) (Fin n) ℝ)
    {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : CenteredTest Z) :
    (regularize D*Z).trace=(D*Z).trace := by
  rw [regularize,add_mul,trace_add,centeredTest_constant_mul hZ,trace_zero,add_zero]

lemma laplacian_zeroSum_pos (G : MultiGraph n m) (hn : 0 < n) (hc : G.Connected univ)
    (x : Fin n → ℝ) (hx : (∑i, x i)=0) (hxne : x ≠ 0) :
    0 < qform (G.laplacian univ) x := by
  have hnonneg := qform_nonneg (G.laplacian_psd univ) x
  by_contra hpos
  have hzero : qform (G.laplacian univ) x=0 := le_antisymm (not_lt.mp hpos) hnonneg
  have hedge (e : Fin m) : x (G.left e)-x (G.right e)=0 := by
    rw [G.laplacian_qform] at hzero
    have he := (single_le_sum (fun i _ => sq_nonneg (x (G.left i)-x (G.right i))) (mem_univ e))
    rw [hzero] at he
    exact sq_eq_zero_iff.mp (le_antisymm he (sq_nonneg _))
  let f : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun v => x ⬝ᵥ v
      map_add' := fun v w => dotProduct_add x v w
      map_smul' := fun c v => dotProduct_smul c x v }
  have hf : G.edgeSpan univ ≤ f.ker := by
    apply (Packing.span_le_iff G.incidence).mpr
    intro e _
    change (∑v, x v*G.incidence e v)=0
    rw [G.eval_incidence]
    exact hedge e
  have hxx : x ⬝ᵥ x=0 := hf (by rw [G.connected_span_zeroSum hn hc]; exact (mem_zeroSumSpace x).mpr hx)
  exact hxne (dotProduct_self_eq_zero.mp hxx)

lemma laplacian_ones (G : MultiGraph n m) : G.laplacian univ *ᵥ ones n=0 := by
  simp only [laplacian,sum_mulVec,vecMulVec_mulVec]
  apply Finset.sum_eq_zero
  intro e _
  rw [dotProduct_comm]
  change MulOpposite.op (∑v, ones n v*G.incidence e v) • G.incidence e=0
  rw [G.eval_incidence]
  simp [ones]

lemma laplacian_regularize_pd (G : MultiGraph n m) (hn : 0 < n) (hc : G.Connected univ) :
    (regularize (G.laplacian univ)).PosDef := by
  apply PosDef.of_dotProduct_mulVec_pos ((G.laplacian_psd univ).add constantProjection_psd).isHermitian
  intro x hx
  change 0 < qform (regularize (G.laplacian univ)) x
  rw [regularize,qform_add]
  by_cases hxs : (∑i, x i)=0
  · exact add_pos_of_pos_of_nonneg (laplacian_zeroSum_pos G hn hc x hxs hx)
      (qform_nonneg constantProjection_psd x)
  · apply add_pos_of_nonneg_of_pos (qform_nonneg (G.laplacian_psd univ) x)
    rw [qform_constantProjection]
    exact div_pos (sq_pos_of_ne_zero hxs) (Nat.cast_pos.mpr hn)

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Metric_ConicDuality
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric conic duality. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree
open scoped Classical MatrixOrder Topology
open Filter

section GeneralFinite
variable {V E T J : Type*} [Fintype V] [DecidableEq V] [Fintype T] [Fintype J]

lemma trace_pairing_convex (Z : Matrix V V ℝ) (d : ℝ) :
    ConvexOn ℝ {D : Matrix V V ℝ | D.PosDef} (fun D => (D*Z).trace-d) := by
  refine ⟨MatrixDual.posDef_convex,?_⟩
  intro X _ Y _ a b _ _ hab
  simp only [add_mul,smul_mul_assoc,trace_add,trace_smul,smul_eq_mul]
  nlinarith only [congrArg (fun v : ℝ => v*d) hab]

lemma trace_test_slater (Z : J → Matrix V V ℝ) {d : J → ℝ} (hd : ∀j, 0 < d j) :
    ∃D : Matrix V V ℝ, D.PosDef ∧ ∀j, (D*Z j).trace-d j < 0 := by
  have hlim (j : J) : Tendsto (fun t : ℝ => t*(Z j).trace) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => t*(Z j).trace) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have he : ∀ᶠ t : ℝ in 𝓝[>] 0, ∀j, t*(Z j).trace < d j :=
    eventually_all.mpr (fun j => (hlim j).eventually_lt_const (hd j))
  have hp : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := eventually_mem_nhdsWithin
  obtain ⟨t,ht,htp⟩ := (he.and hp).exists
  refine ⟨t • (1 : Matrix V V ℝ),Matrix.PosDef.one.smul htp,?_⟩
  intro j
  simpa only [smul_mul_assoc,one_mul,trace_smul,smul_eq_mul,sub_lt_zero] using ht j

lemma trace_weighted_tests (Z : J → Matrix V V ℝ) (y d : J → ℝ) (D : Matrix V V ℝ) :
    ((∑j, y j • Z j)*D).trace-∑j, y j*d j = ∑j, y j*((D*Z j).trace-d j) := by
  simp only [sum_mul,smul_mul_assoc,trace_sum,trace_smul,smul_eq_mul,mul_sub,sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intro j _
  rw [trace_mul_comm]

lemma finite_shortcut_of_trace_bound (b : E → V → ℝ) (O : T → Finset E)
    (Z : J → Matrix V V ℝ) (hZ : ∀j, (Z j).PosSemidef) (d : J → ℝ)
    (hd : ∀j, 0 < d j) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀lam : T → ℝ, ∀y : J → ℝ, (∀t, 0 ≤ lam t) → (∑t, lam t)=1 →
      (∀j, 0 ≤ y j) →
      (CFC.sqrt (CFC.sqrt (∑j, y j • Z j) * ShortcutDual.objectiveMatrix b O lam *
        CFC.sqrt (∑j, y j • Z j))).trace^2 ≤ K * ∑j, y j*d j)
    {eta : ℝ} (heta : 0 < eta) :
    ∃D : Matrix V V ℝ, D.PosDef ∧
      (∀t, ShortcutDual.boundaryAverage b O t D < K+eta) ∧
      (∀j, (D*Z j).trace < d j) := by
  have hs := Duality.strict_feasible_of_dual_bound {D : Matrix V V ℝ | D.PosDef}
    MatrixDual.posDef_convex (ShortcutDual.boundaryAverage b O) (fun j D => (D*Z j).trace-d j)
    (ShortcutDual.boundaryAverage_convex b O) (fun j => trace_pairing_convex (Z j) (d j))
    (trace_test_slater Z hd) (K+eta)
  obtain ⟨D,hD,hf,hg⟩ := hs (by
    intro lam y hlam hlams hy
    let A := ShortcutDual.objectiveMatrix b O lam
    let W := ∑j, y j • Z j
    let N := (CFC.sqrt (CFC.sqrt W*A*CFC.sqrt W)).trace
    let v := ∑j, y j*d j
    have hv : 0 ≤ v := sum_nonneg (fun j _ => mul_nonneg (hy j) (hd j).le)
    have hN : 0 ≤ N := (CFC.sqrt_nonneg _).posSemidef.trace_nonneg
    have hb : N^2 ≤ K*v := hbound lam y hlam hlams hy
    have hNv : 2*N ≤ K+v := by nlinarith only [hb,hK,hv,hN,sq_nonneg (K-v)]
    have hW : W.PosSemidef := Matrix.posSemidef_sum _ (fun j _ => (hZ j).smul (hy j))
    obtain ⟨D,hD,hval⟩ := MatrixDual.trace_objective_approx
      (ShortcutDual.objectiveMatrix_posSemidef b O hlam) hW
      (show 2*N < K+eta+v by linarith only [hNv,heta])
    refine ⟨D,hD,?_⟩
    have htr := trace_weighted_tests Z y d D
    rw [ShortcutDual.trace_objectiveMatrix] at hval
    change (∑t,lam t*ShortcutDual.boundaryAverage b O t D) + (W*D).trace < K+eta+v at hval
    linarith only [hval,htr])
  exact ⟨D,hD,hf,fun j => sub_neg.mp (hg j)⟩

end GeneralFinite

section Pairing
variable {n : ℕ}

lemma trace_gram_pairing (B X : Matrix (Fin n) (Fin n) ℝ) :
    (B*(Xᵀ*X)).trace=∑i, qform B (X i) := by
  rw [←mul_assoc,trace_mul_cycle]
  apply sum_congr rfl
  intro i _
  simp only [diag_apply,mul_apply,transpose_apply,qform,mulVec,dotProduct]
  simp only [sum_mul,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro k _
  ring

lemma trace_pairing_nonneg {B Z : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.PosSemidef) (hZ : Z.PosSemidef) : 0 ≤ (B*Z).trace := by
  conv_rhs => rw [←sqrt_gram hZ]
  rw [trace_gram_pairing]
  exact sum_nonneg (fun i _ => qform_nonneg hB _)

lemma trace_pairing_pos {B Z : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.PosDef) (hZ : Z.PosSemidef) (hZ0 : Z ≠ 0) : 0 < (B*Z).trace := by
  have hX : CFC.sqrt Z ≠ 0 := by
    intro he
    have hh := sqrt_gram hZ
    rw [he,transpose_zero,zero_mul] at hh
    exact hZ0 hh.symm
  have hi : ∃i, CFC.sqrt Z i ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hX (funext hh)
  obtain ⟨i,hi⟩ := hi
  rw [←sqrt_gram hZ,trace_gram_pairing]
  apply sum_pos'
  · intro j _
    exact qform_nonneg hB.posSemidef _
  · exact ⟨i,mem_univ i,by simpa only [qform,star_trivial] using hB.dotProduct_mulVec_pos hi⟩

lemma trace_pairing_mono {B D Z : Matrix (Fin n) (Fin n) ℝ}
    (hBD : B ≤ D) (hZ : Z.PosSemidef) : (B*Z).trace ≤ (D*Z).trace := by
  have hh := trace_pairing_nonneg (Matrix.le_iff.mp hBD) hZ
  simpa only [sub_mul,trace_sub,sub_nonneg] using hh

lemma test_one : Test (1 : Matrix (Fin n) (Fin n) ℝ) := by
  refine ⟨Matrix.PosSemidef.one,?_⟩
  intro u v w
  have heq (a b : Fin n) : qform (1 : Matrix (Fin n) (Fin n) ℝ) (difference a b)=
      if a=b then 0 else 2 := by
    by_cases hab : a=b
    · simp [hab,difference,qform]
    · norm_num [qform,difference,MultiGraph.point,sub_dotProduct,dotProduct_sub,hab,Ne.symm hab]
  simp only [heq]
  split_ifs <;> try norm_num
  all_goals simp_all

end Pairing
end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Metric_CompactDuality
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric compact duality. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree
open scoped Classical MatrixOrder Matrix.Norms.Elementwise

variable {n : ℕ} {E T : Type*}

lemma average_antitone (b : E → Fin n → ℝ) (O : T → Finset E) (t : T)
    {D F : Matrix (Fin n) (Fin n) ℝ} (hD : D.PosDef) (hF : F.PosDef) (hDF : D ≤ F) :
    ShortcutDual.boundaryAverage b O t F ≤ ShortcutDual.boundaryAverage b O t D := by
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  exact sum_le_sum (fun e _ => resistance_antitone hF hD (Matrix.le_iff.mp hDF) (b e))

lemma average_smul (b : E → Fin n → ℝ) (O : T → Finset E) (t : T)
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.PosDef) {c : ℝ} (hc : 0 < c) :
    ShortcutDual.boundaryAverage b O t (c • D)=c⁻¹*ShortcutDual.boundaryAverage b O t D := by
  let : Invertible c := invertibleOfNonzero hc.ne'
  simp only [ShortcutDual.boundaryAverage,Matrix.inv_smul D c ((Matrix.isUnit_iff_isUnit_det D).mp hD.isUnit),
    invOf_eq_inv,smul_mulVec,dotProduct_smul,smul_eq_mul,←mul_sum]
  ring

lemma average_continuousAt (b : E → Fin n → ℝ) (O : T → Finset E) (t : T)
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.PosDef) :
    ContinuousAt (ShortcutDual.boundaryAverage b O t) D := by
  have hc : Continuous (fun X : Matrix (Fin n) (Fin n) ℝ =>
      ((O t).card : ℝ)⁻¹ * ∑e ∈ O t, qform X (b e)) :=
    (continuous_finsetSum _ (fun e _ => qform_continuous (b e))).const_mul _
  apply hc.continuousAt.comp
  apply continuousAt_matrix_inv
  simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hD.det_pos.ne'

lemma pdBox_pd {B D : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosDef) (hD : D ∈ pdBox B) : D.PosDef :=
  posDef_of_le (hB.smul (by norm_num : (0:ℝ)<1/4)) hD.1

lemma pdBox_closed (B : Matrix (Fin n) (Fin n) ℝ) : IsClosed (pdBox B) :=
  (isClosed_matrixAbove _).inter (isClosed_le
    (by simpa only [mul_one] using trace_pairing_continuous (1 : Matrix (Fin n) (Fin n) ℝ)) continuous_const)

lemma pdBox_bounded {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosDef) : Bornology.IsBounded (pdBox B) := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨B.trace,fun D hD => ?_⟩
  have hC : 0 ≤ B.trace := hB.posSemidef.trace_nonneg
  have hDp := (pdBox_pd hB hD).posSemidef
  have hdiag : ∀i, D i i ≤ B.trace := by
    intro i
    exact (single_le_sum (fun j _ => hDp.diag_nonneg (i := j)) (mem_univ i)).trans hD.2
  apply (pi_norm_le_iff_of_nonneg hC).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg hC).mpr
  intro j
  simpa only [Real.norm_eq_abs] using psd_entry_bound hDp hC hdiag i j

lemma pdBox_compact {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosDef) : IsCompact (pdBox B) :=
  Metric.isCompact_iff_isClosed_bounded.mpr ⟨pdBox_closed B,pdBox_bounded hB⟩

lemma pdBox_objective_closed (b : E → Fin n → ℝ) (O : T → Finset E)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosDef) (K : ℝ) :
    IsClosed {D | D ∈ pdBox B ∧ ∀t, ShortcutDual.boundaryAverage b O t D ≤ K} := by
  have ht (t : T) : IsClosed {D | D ∈ pdBox B ∧ ShortcutDual.boundaryAverage b O t D ≤ K} :=
    (pdBox_closed B).isClosed_le (fun D hD => (average_continuousAt b O t (pdBox_pd hB hD)).continuousWithinAt)
      continuousOn_const
  have heq : {D | D ∈ pdBox B ∧ ∀t, ShortcutDual.boundaryAverage b O t D ≤ K}=
      pdBox B ∩ ⋂t, {D | D ∈ pdBox B ∧ ShortcutDual.boundaryAverage b O t D ≤ K} := by
    ext D
    simp only [Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_iInter]
    constructor
    · exact fun h => ⟨h.1,fun t => ⟨h.1,h.2 t⟩⟩
    · exact fun h => ⟨h.1,fun t => (h.2 t).2⟩
  rw [heq]
  exact (pdBox_closed B).inter (isClosed_iInter ht)

section Cone
variable [Fintype T]

theorem metric_shortcut_of_trace_bound (hn : 0 < n)
    (b : E → Fin n → ℝ) (O : T → Finset E)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.PosDef) {K : ℝ} (hK : 0 < K)
    (hbound : ∀Z : Matrix (Fin n) (Fin n) ℝ, Test Z →
      ∀lam : T → ℝ, (∀t, 0 ≤ lam t) → (∑t, lam t)=1 →
      (CFC.sqrt (CFC.sqrt Z*ShortcutDual.objectiveMatrix b O lam*CFC.sqrt Z)).trace^2 ≤ K*(B*Z).trace) :
    ∃D : Matrix (Fin n) (Fin n) ℝ, D.PosDef ∧
      (∀t, ShortcutDual.boundaryAverage b O t D ≤ 2*K) ∧
      (∀Z : Matrix (Fin n) (Fin n) ℝ, Test Z → (D*Z).trace ≤ (B*Z).trace) := by
  let C := {D | D ∈ pdBox B ∧ ∀t, ShortcutDual.boundaryAverage b O t D ≤ 2*K}
  have hC : IsCompact C := (pdBox_compact hB).of_isClosed_subset
    (pdBox_objective_closed b O hB (2*K)) (fun _ h => h.1)
  let I := {Z : Matrix (Fin n) (Fin n) ℝ // Test Z}
  let A : I → Set (Matrix (Fin n) (Fin n) ℝ) := fun Z => {D | (D*Z.val).trace ≤ (B*Z.val).trace}
  have hA : ∀Z, IsClosed (A Z) := fun Z => isClosed_le (trace_pairing_continuous Z.val) continuous_const
  have hfinite : ∀s : Finset I, (C ∩ ⋂Z ∈ s, A Z).Nonempty := by
    intro s
    have h1 : (1 : Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
      intro he
      have hh := congrFun (congrFun he ⟨0,hn⟩) ⟨0,hn⟩
      norm_num at hh
    let s' : Finset I := (insert ⟨1,test_one⟩ s).filter fun Z => Z.val ≠ 0
    have hbnd : ∀lam : T → ℝ, ∀y : s' → ℝ,
        (∀t, 0 ≤ lam t) → (∑t, lam t)=1 → (∀j, 0 ≤ y j) →
        (CFC.sqrt (CFC.sqrt (∑j, y j • j.val.val)*ShortcutDual.objectiveMatrix b O lam*
          CFC.sqrt (∑j, y j • j.val.val))).trace^2 ≤ K*∑j, y j*(B*j.val.val).trace := by
      intro lam y hlam hsum hy
      have ht : Test (∑j : s', y j • j.val.val) := test_sum univ _
        (fun j _ => test_smul j.val.property (hy j))
      simpa only [mul_sum,mul_smul_comm,trace_sum,trace_smul,smul_eq_mul] using hbound _ ht lam hlam hsum
    obtain ⟨D,hD,hobj,htr⟩ := finite_shortcut_of_trace_bound b O (fun j : s' => j.val.val)
      (fun j => j.val.property.1) (fun j => (B*j.val.val).trace)
      (fun j => trace_pairing_pos hB j.val.property.1 ((mem_filter.mp j.property).2))
      hK.le hbnd (eta := K/2) (by positivity)
    let F : Matrix (Fin n) (Fin n) ℝ := (3/4:ℝ) • D+(1/4:ℝ) • B
    have hF : F.PosDef := (hD.smul (by norm_num : (0:ℝ)<3/4)).add_posSemidef
      (hB.posSemidef.smul (by norm_num : (0:ℝ)≤1/4))
    have hFB : (1/4:ℝ) • B ≤ F := by
      apply Matrix.le_iff.mpr
      simpa only [F,add_sub_cancel_right] using hD.posSemidef.smul (show (0:ℝ)≤3/4 by norm_num)
    have hFD : (3/4:ℝ) • D ≤ F := by
      apply Matrix.le_iff.mpr
      simpa only [F,add_sub_cancel_left] using hB.posSemidef.smul (show (0:ℝ)≤1/4 by norm_num)
    have hfbound (t : T) : ShortcutDual.boundaryAverage b O t F ≤ 2*K := by
      have hh := average_antitone b O t (hD.smul (show (0:ℝ)<3/4 by norm_num)) hF hFD
      rw [average_smul b O t hD (by norm_num : (0:ℝ)<3/4)] at hh
      norm_num at hh
      linarith only [hh,hobj t]
    have hFtr (Z : I) (hZ : Z ∈ insert ⟨1,test_one⟩ s) : (F*Z.val).trace ≤ (B*Z.val).trace := by
      by_cases hZ0 : Z.val=0
      · simp [hZ0]
      have hh := htr ⟨Z,mem_filter.mpr ⟨hZ,hZ0⟩⟩
      dsimp [F]
      simp only [add_mul,smul_mul_assoc,trace_add,trace_smul,smul_eq_mul]
      linarith only [hh]
    have hFt : F.trace ≤ B.trace := by
      simpa only [mul_one] using hFtr ⟨1,test_one⟩ (mem_insert_self _ _)
    refine ⟨F,⟨⟨hFB,hFt⟩,hfbound⟩,?_⟩
    simp only [Set.mem_iInter]
    intro Z hZ
    exact hFtr Z (mem_insert_of_mem hZ)
  obtain ⟨D,hDC,hDA⟩ := hC.inter_iInter_nonempty A hA hfinite
  refine ⟨D,pdBox_pd hB hDC.1,hDC.2,?_⟩
  intro Z hZ
  exact Set.mem_iInter.mp hDA ⟨Z,hZ⟩

end Cone
end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Metric_Hierarchy
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.Partitions.mem_crossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric hierarchy. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder

variable {n m : ℕ}

lemma incidence_sum (G : MultiGraph n m) (e : Fin m) : ∑i, G.incidence e i=0 :=
  (mem_zeroSumSpace _).mp (G.incidence_zeroSum e)

lemma connected_of_edgeConnected {G : MultiGraph n m} {q : ℕ}
    (hq : 0 < q) (hc : G.EdgeConnected q) : G.Connected univ := by
  intro S hS hS'
  exact card_pos.mp (hq.trans_le (hc S hS hS'))

theorem metric_hierarchy_bound :
    ∃h0 : ℕ, 2 ≤ h0 ∧ ∀h : ℕ, h0 ≤ h →
      ∀(n m : ℕ) (G : MultiGraph n m) (H : Hierarchy n), 2 ≤ n →
      H.LocallyConnectedReal G h →
      ∀M : Finset (Finset (Fin n)), M ⊆ H.nodes →
      (∀A ∈ M, A ≠ univ) →
      (∀A ∈ M, ((G.cut univ A).card : ℝ)/h ≤ (H.parentBoundary G A).card) →
      ∃D : Matrix (Fin n) (Fin n) ℝ, CenteredPositive D ∧
        (∀Z : Matrix (Fin n) (Fin n) ℝ, CenteredTest Z → (D*Z).trace ≤ (G.laplacian univ*Z).trace) ∧
        (∀A ∈ M, boundaryResistance G H D A ≤ (h:ℝ)^(-31/40:ℝ)) := by
  obtain ⟨h0,hh0,hbound⟩ := polynomial_nuclear_bound
  refine ⟨h0,hh0,?_⟩
  intro h hh n m G H hn hconn M hM hroot hratio
  have hn' : 0 < n := by omega
  have hh' : 0 < h := by omega
  have hhp : (0:ℝ) < h := Nat.cast_pos.mpr hh'
  let B := regularize (G.laplacian univ)
  have hB : B.PosDef := laplacian_regularize_pd G hn'
    (connected_of_edgeConnected hh' (Hierarchy.edgeConnected_of_locally hconn))
  let K : ℝ := (h:ℝ)^(-31/40:ℝ)/2
  have hK : 0 < K := div_pos (Real.rpow_pos_of_pos hhp _) (by norm_num)
  have hb : ∀Z : Matrix (Fin n) (Fin n) ℝ, Test Z →
      ∀lam : M → ℝ, (∀A, 0 ≤ lam A) → (∑A, lam A)=1 →
      (CFC.sqrt (CFC.sqrt Z*ShortcutDual.objectiveMatrix G.incidence
        (fun A : M => H.parentBoundary G A) lam*CFC.sqrt Z)).trace^2 ≤ K*(B*Z).trace := by
    intro Z hZ lam hlam hsum
    have hle : (G.laplacian univ*Z).trace ≤ (B*Z).trace := by
      dsimp [B,regularize]
      rw [add_mul,trace_add]
      exact le_add_of_nonneg_right (trace_pairing_nonneg constantProjection_psd hZ.1)
    exact (hbound h hh n m G H hconn M hM hroot hratio Z hZ lam hlam hsum).trans
      (mul_le_mul_of_nonneg_left hle hK.le)
  obtain ⟨D,hD,havg,htr⟩ := metric_shortcut_of_trace_bound hn' G.incidence
    (fun A : M => H.parentBoundary G A) B hB hK hb
  refine ⟨centered D,centered_positive hn' hD,?_,?_⟩
  · intro Z hZ
    rw [centered_trace D hZ]
    have hh := htr Z hZ.1
    rwa [regularize_trace (G.laplacian univ) hZ] at hh
  · intro A hA
    have hc : boundaryResistance G H (centered D) A ≤
        ShortcutDual.boundaryAverage G.incidence (fun A : M => H.parentBoundary G A) ⟨A,hA⟩ D := by
      unfold boundaryResistance ShortcutDual.boundaryAverage
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
      exact sum_le_sum (fun e _ => inverse_centered_le hn' hD (incidence_sum G e))
    have ht : 2*K=(h:ℝ)^(-31/40:ℝ) := by dsimp [K] <;> ring
    exact ht ▸ hc.trans (havg ⟨A,hA⟩)

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_CenteredDomain
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Centered domain. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder Matrix.Norms.Elementwise

variable {n m : ℕ}

lemma mul_constant_of_ones {D : Matrix (Fin n) (Fin n) ℝ} (hD0 : D *ᵥ ones n=0) :
    D*constantProjection n=0 := by
  simp only [constantProjection,mul_smul_comm,mul_vecMulVec,hD0,zero_vecMulVec,smul_zero]

lemma constant_mul_of_ones {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.IsHermitian)
    (hD0 : D *ᵥ ones n=0) : constantProjection n*D=0 := by
  have hh := congrArg transpose (mul_constant_of_ones hD0)
  simpa only [transpose_mul,constantProjection_symmetric,
    (isHermitian_iff_isSymm.mp hD).eq,transpose_zero] using hh

lemma mul_centering_of_ones {D : Matrix (Fin n) (Fin n) ℝ} (hD0 : D *ᵥ ones n=0) :
    D*centering n=D := by
  rw [centering,mul_sub,mul_one,mul_constant_of_ones hD0,sub_zero]

lemma centering_mul_of_ones {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.IsHermitian)
    (hD0 : D *ᵥ ones n=0) : centering n*D=D := by
  rw [centering,sub_mul,one_mul,constant_mul_of_ones hD hD0,sub_zero]

lemma centered_eq {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.IsHermitian)
    (hD0 : D *ᵥ ones n=0) : centered D=D := by
  rw [centered,centering_mul_of_ones hD hD0,mul_centering_of_ones hD0]

lemma centeredPositive_psd (hn : 0 < n) {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : CenteredPositive D) : D.PosSemidef := by
  apply PosSemidef.of_dotProduct_mulVec_nonneg hD.1
  intro x
  change 0 ≤ qform D x
  rw [←centered_eq hD.1 hD.2.1,qform_centered]
  by_cases hx : centering n *ᵥ x=0
  · simp [hx,qform]
  · exact (hD.2.2 _ (centering_mulVec_sum hn x) hx).le

lemma regularize_pd (hn : 0 < n) {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : CenteredPositive D) : (regularize D).PosDef := by
  apply PosDef.of_dotProduct_mulVec_pos (hD.1.add constantProjection_psd.isHermitian)
  intro x hx
  change 0 < qform (regularize D) x
  rw [regularize,qform_add]
  by_cases hp : centering n *ᵥ x=0
  · have hs : (∑i, x i) ≠ 0 := by
      intro hs
      rw [centering_mulVec_of_sum_zero hs] at hp
      exact hx hp
    have hq : 0 < qform (constantProjection n) x := by
      rw [qform_constantProjection]
      exact div_pos (sq_pos_of_ne_zero hs) (Nat.cast_pos.mpr hn)
    exact add_pos_of_nonneg_of_pos (qform_nonneg (centeredPositive_psd hn hD) _) hq
  · have hq : 0 < qform D x := by
      rw [←centered_eq hD.1 hD.2.1,qform_centered]
      exact hD.2.2 _ (centering_mulVec_sum hn x) hp
    exact add_pos_of_pos_of_nonneg hq (qform_nonneg constantProjection_psd _)

lemma centeredPositive_add_psd {D F : Matrix (Fin n) (Fin n) ℝ}
    (hD : CenteredPositive D) (hF : F.PosSemidef) (hF0 : F *ᵥ ones n=0) :
    CenteredPositive (D+F) := by
  refine ⟨hD.1.add hF.isHermitian,?_,?_⟩
  · simp only [add_mulVec,hD.2.1,hF0,add_zero]
  · intro x hx hx0
    rw [qform_add]
    exact add_pos_of_pos_of_nonneg (hD.2.2 x hx hx0) (qform_nonneg hF _)

lemma centered_rankOne {b : Fin n → ℝ} (hb : (∑i, b i)=0) :
    centered (vecMulVec b b)=vecMulVec b b := by
  apply centered_eq
  · simpa only [star_trivial] using (posSemidef_vecMulVec_self_star b).isHermitian
  · rw [vecMulVec_mulVec,dotProduct_comm,ones_dot,hb,IsCentralScalar.op_smul_eq_smul,zero_smul]

lemma centered_regularize {D : Matrix (Fin n) (Fin n) ℝ} (hn : 0 < n)
    (hD : D.IsHermitian) (hD0 : D *ᵥ ones n=0) : centered (regularize D)=D := by
  have hc0 : centering n*constantProjection n=0 := by
    exact mul_constant_of_ones (centering_ones hn)
  simp only [centered,regularize,mul_add,hc0,add_zero,
    centering_mul_of_ones hD hD0,mul_centering_of_ones hD0]

lemma centered_resistance_nonneg (G : MultiGraph n m) (hn : 0 < n)
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : CenteredPositive D) (e : Fin m) :
    0 ≤ resistance G D e := qform_nonneg (regularize_pd hn hD).inv.posSemidef _

lemma centered_inverse_antitone (hn : 0 < n) {D X : Matrix (Fin n) (Fin n) ℝ}
    (hD : CenteredPositive D) (hX : CenteredPositive X) (hDX : D ≤ X) (b : Fin n → ℝ) :
    qform (inverseOnZeroSum X) b ≤ qform (inverseOnZeroSum D) b := by
  apply StrongThinTree.resistance_antitone (regularize_pd hn hX) (regularize_pd hn hD)
  have hh : regularize X-regularize D=X-D := by unfold regularize; abel
  rw [hh]
  exact Matrix.le_iff.mp hDX

lemma centered_resistance_order (hn : 0 < n) {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : CenteredPositive X) {b : Fin n → ℝ} (hb : (∑i, b i)=0)
    {a : ℝ} (ha : 0 < a) :
    (X-a • vecMulVec b b).PosSemidef ↔ a*qform (inverseOnZeroSum X) b ≤ 1 := by
  have heq : a • (a⁻¹ • regularize X-vecMulVec b b)=regularize X-a • vecMulVec b b := by
    rw [smul_sub,smul_smul,mul_inv_cancel₀ ha.ne',one_smul]
  have hproblem := StrongThinTree.resistance_order (regularize_pd hn hX) b (inv_pos.mpr ha)
  constructor
  · intro h
    have h' : (regularize X-a • vecMulVec b b).PosSemidef := by
      convert h.add constantProjection_psd using 1
      all_goals try with_reducible_and_instances rfl
      unfold regularize
      abel
    have hinv := h'.smul (inv_nonneg.mpr ha.le)
    have hi : a⁻¹ • (regularize X-a • vecMulVec b b)=a⁻¹ • regularize X-vecMulVec b b := by
      rw [smul_sub,smul_smul,inv_mul_cancel₀ ha.ne',one_smul]
    rw [hi] at hinv
    have hh := hproblem.mpr hinv
    change qform (inverseOnZeroSum X) b ≤ a⁻¹ at hh
    have hm := mul_le_mul_of_nonneg_left hh ha.le
    rwa [mul_inv_cancel₀ ha.ne'] at hm
  · intro h
    have hh : qform (inverseOnZeroSum X) b ≤ a⁻¹ := by
      rw [←one_div,le_div_iff₀ ha]
      simpa only [mul_comm] using h
    have h' := (hproblem.mp hh).smul ha.le
    rw [heq] at h'
    have hc := centered_psd h'
    have he : centered (regularize X-a • vecMulVec b b)=X-a • vecMulVec b b := by
      simp only [centered,mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc]
      rw [show centering n*regularize X*centering n=X from centered_regularize hn hX.1 hX.2.1]
      rw [show centering n*vecMulVec b b*centering n=vecMulVec b b from centered_rankOne hb]
    rwa [he] at hc

lemma shortcut_add_mem_domain {m' : ℕ} (G : MultiGraph n m) (H : MultiGraph n m')
    (hn : 0 < n) (hGH : G.laplacian univ ≤ H.laplacian univ)
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : CenteredPositive D)
    (ht : ∀Z, CenteredTest Z → (D*Z).trace ≤ (G.laplacian univ*Z).trace) :
    H.laplacian univ+D ∈ metricDomain H := by
  refine ⟨(H.laplacian_psd univ).isHermitian.add hD.1,?_,?_,?_⟩
  · simp only [add_mulVec,laplacian_ones H,hD.2.1,add_zero]
  · exact le_add_of_nonneg_right (Matrix.nonneg_iff_posSemidef.mpr (centeredPositive_psd hn hD))
  · intro Z hZ
    rw [add_mul,trace_add]
    have h1 := ht Z hZ
    have h2 := trace_pairing_mono hGH hZ.1.1
    have h3 := trace_pairing_nonneg (H.laplacian_psd univ) hZ.1.1
    linarith only [h1,h2,h3]

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_PartitionGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Partition geometry. -/

section

namespace AlgorithmicThinTrees.Partitions
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical

variable {V : Type*} [Fintype V]

lemma parts_top [Nonempty V] : parts (⊤ : Setoid V)={univ} := by
  have hb (v : V) : block (⊤ : Setoid V) v=univ := by ext w; simp [block]
  unfold parts
  rw [show block (⊤ : Setoid V)=(fun _ => univ) from funext hb]
  exact image_const univ_nonempty _

variable {n m : ℕ}

lemma toChain_block (f : ℕ → Setoid (Fin n)) (hf : Monotone f) (i : ℕ) (v : Fin n) :
    (toChain f hf).block i v=block (f i) v :=
  (toChain f hf).block_eq_of_mem (block_mem_parts _ _) (self_mem_block _ _)

lemma toChain_crossing (G : MultiGraph n m) (f : ℕ → Setoid (Fin n)) (hf : Monotone f) (i : ℕ) :
    (toChain f hf).crossing G i=crossing G (f i) := by
  ext e
  simp only [PartitionChain.mem_crossing,toChain_block,mem_crossing,block_eq_iff,ne_eq]

lemma enumerate_chain (J : Finset (Setoid (Fin n)))
    (hJ : IsChain (· ≤ ·) (J : Set (Setoid (Fin n)))) :
    ∃f : ℕ → Setoid (Fin n), Monotone f ∧ f J.card=⊤ ∧
      (∀i, f i ∈ J ∨ f i=⊤) ∧ ∀p ∈ J, ∃i < J.card, f i=p := by
  let : LinearOrder J := hJ.linearOrder
  let e : Fin J.card ≃o J := (univ : Finset J).orderIsoOfFin (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    |>.trans ((OrderIso.setCongr _ _ (Finset.coe_univ)).trans OrderIso.Set.univ)
  let f (i : ℕ) : Setoid (Fin n) := if hi : i < J.card then (e ⟨i,hi⟩).val else ⊤
  refine ⟨f,?_,?_,?_,?_⟩
  · intro i j hij
    dsimp only [f]
    split_ifs with hi hj
    · exact e.monotone (show (⟨i,hi⟩ : Fin J.card) ≤ ⟨j,hj⟩ from hij)
    · exact le_top
    · omega
    · exact le_rfl
  · dsimp [f]
    rw [dite_eq_right (lt_irrefl _)]
  · intro i
    dsimp only [f]
    split_ifs with hi
    · exact Or.inl (e ⟨i,hi⟩).property
    · exact Or.inr rfl
  · intro p hp
    let j := e.symm ⟨p,hp⟩
    refine ⟨j.val,j.isLt,?_⟩
    dsimp only [f]
    rw [dite_eq_left j.isLt]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨p,hp⟩)

end
end AlgorithmicThinTrees.Partitions
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Restriction
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
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
end StrongThinTree.MultiGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Metric_Response
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.Partitions.mem_crossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric response. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder

variable {n m m' : ℕ}

lemma laplacian_mono (G : MultiGraph n m) {F B : Finset (Fin m)} (hFB : F ⊆ B) :
    G.laplacian F ≤ G.laplacian B := by
  unfold MultiGraph.laplacian
  apply sum_le_sum_of_subset_of_nonneg hFB
  intro e _ _
  exact Matrix.nonneg_iff_posSemidef.mpr (by
    simpa only [star_trivial] using posSemidef_vecMulVec_self_star (G.incidence e))

lemma restrict_laplacian (H : MultiGraph n m') (F : Finset (Fin m')) :
    (H.restrict F).laplacian univ=H.laplacian F := by
  conv_rhs => rw [←lift_univ F]
  simp only [MultiGraph.laplacian,liftEdges,sum_map]
  rfl

lemma restrict_laplacian_le (H : MultiGraph n m') (F : Finset (Fin m')) :
    (H.restrict F).laplacian univ ≤ H.laplacian univ := by
  rw [restrict_laplacian]
  exact laplacian_mono H (subset_univ _)

lemma metric_shortcut_response (G : MultiGraph n m) (H : MultiGraph n m')
    (hn : 0 < n) (hGH : G.laplacian univ ≤ H.laplacian univ)
    {J : Hierarchy n} {h : ℕ} (hh : 0 < h) {a t : ℝ}
    (ha : 0 ≤ a) (ht : 0 < t)
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : CenteredPositive D)
    (htr : ∀Z, CenteredTest Z → (D*Z).trace ≤ (G.laplacian univ*Z).trace)
    (havg : ∀A ∈ J.nodes, A ≠ univ →
      ((G.cut univ A).card:ℝ)/h ≤ (J.parentBoundary G A).card →
      boundaryResistance G J D A ≤ a) :
    ∃Y ∈ metricDomain H, CenteredPositive Y ∧ ∀A ∈ J.nodes,
      (((univ.filter (fun e => t < resistance G Y e)) ∩ J.parentBoundary G A).card:ℝ) ≤
      (a/t+1/(h:ℝ))*(G.cut univ A).card := by
  let Y := H.laplacian univ+D
  have hY : CenteredPositive Y := by
    rw [show Y=D+H.laplacian univ by dsimp [Y]; ac_rfl]
    exact centeredPositive_add_psd hD (H.laplacian_psd univ) (laplacian_ones H)
  have hRY (e : Fin m) : resistance G Y e ≤ resistance G D e := by
    apply centered_inverse_antitone hn hD hY
    exact le_add_of_nonneg_left (Matrix.nonneg_iff_posSemidef.mpr (H.laplacian_psd univ))
  have hcoeff : 0 ≤ a/t := div_nonneg ha ht.le
  have hhR : (0:ℝ) < h := Nat.cast_pos.mpr hh
  refine ⟨Y,shortcut_add_mem_domain G H hn hGH hD htr,hY,fun A hA => ?_⟩
  have hsub := G.parentBoundary_sub J A
  have hcard : ((J.parentBoundary G A).card:ℝ) ≤ (G.cut univ A).card := by
    exact_mod_cast card_le_card hsub
  have hbadsub : (univ.filter (fun e => t < resistance G Y e)) ∩ J.parentBoundary G A ⊆
      (J.parentBoundary G A).filter (fun e => t < resistance G D e) := by
    intro e he
    obtain ⟨hb,heA⟩ := mem_inter.mp he
    exact mem_filter.mpr ⟨heA,(mem_filter.mp hb).2.trans_le (hRY e)⟩
  by_cases hroot : A=univ
  · subst A
    have he : G.cut univ univ=∅ := by ext e; simp [cut]
    have ho : J.parentBoundary G univ=∅ := subset_empty.mp (he ▸ hsub)
    simp [ho,he]
  by_cases hmark : ((G.cut univ A).card:ℝ)/h ≤ (J.parentBoundary G A).card
  · have hm := finite_markov (J.parentBoundary G A) (resistance G D)
      (fun e _ => centered_resistance_nonneg G hn hD e) ht (havg A hA hroot hmark)
    calc
      _ ≤ (((J.parentBoundary G A).filter (fun e => t < resistance G D e)).card:ℝ) := by
        exact_mod_cast card_le_card hbadsub
      _ ≤ a/t*(J.parentBoundary G A).card := hm
      _ ≤ a/t*(G.cut univ A).card := mul_le_mul_of_nonneg_left hcard hcoeff
      _ ≤ _ := by
        have hnon : 0 ≤ 1/(h:ℝ)*(G.cut univ A).card := by positivity
        nlinarith
  · have hb : (((univ.filter (fun e => t < resistance G Y e)) ∩ J.parentBoundary G A).card:ℝ) ≤
        (J.parentBoundary G A).card := by exact_mod_cast card_le_card inter_subset_right
    have hm := (lt_of_not_ge hmark).le
    have hnon : 0 ≤ a/t*(G.cut univ A).card := mul_nonneg hcoeff (Nat.cast_nonneg _)
    calc
      _ ≤ ((J.parentBoundary G A).card:ℝ) := hb
      _ ≤ ((G.cut univ A).card:ℝ)/h := hm
      _ ≤ _ := by
        nlinarith [show ((G.cut univ A).card:ℝ)/h=(1/(h:ℝ))*(G.cut univ A).card by ring]

theorem simultaneous_metric_response_bound :
    ∃ h0 : ℕ, 2 ≤ h0 ∧ ∀h : ℕ, h0 ≤ h →
      ∀(n m m' : ℕ) (G : MultiGraph n m) (H : MultiGraph n m'), 2 ≤ n →
      G.laplacian univ ≤ H.laplacian univ →
      ∀(P : PartitionChain n) (z : ℕ), P.parts z={univ} →
      (∀i ≤ z, ∀A ∈ P.parts i, G.EdgeConnectedReal A h) →
      ∀t : ℝ, 0 < t → ∃Y ∈ metricDomain H, CenteredPositive Y ∧
        ∀i ≤ z, (((univ.filter (fun e => t < resistance G Y e)) ∩ P.crossing G i).card:ℝ) ≤
          16*((h:ℝ)^(-31/40:ℝ)/t+1/(h:ℝ))*(P.crossing G i).card := by
  obtain ⟨h0,hh0,hshortcut⟩ := metric_hierarchy_bound
  refine ⟨h0,hh0,?_⟩
  intro h hh n m m' G H hn hGH P z hz hlocal t ht
  let I := insert z (Dyadic.selected (fun j => (P.crossing G j).card) z)
  obtain ⟨J,hJ⟩ := P.exists_hierarchy I ⟨z,mem_insert_self _ _,hz ▸ mem_singleton_self _⟩
  have hloc : J.LocallyConnectedReal G h := by
    apply G.chain_locally P I J hJ
    intro i hi A hA
    have hiz : i ≤ z := by
      rcases mem_insert.mp hi with rfl | hi
      · exact le_rfl
      · exact (Dyadic.selected_spec hi).1
    exact hlocal i hiz A hA
  let M := J.nodes.filter (fun A => A ≠ univ ∧
    ((G.cut univ A).card:ℝ)/h ≤ (J.parentBoundary G A).card)
  obtain ⟨D,hD,htr,havg⟩ := hshortcut h hh n m G J hn hloc M (filter_subset _ _)
    (fun A hA => (mem_filter.mp hA).2.1) (fun A hA => (mem_filter.mp hA).2.2)
  obtain ⟨Y,hYm,hY,hnode⟩ := metric_shortcut_response G H (by omega) hGH (by omega : 0 < h)
    (Real.rpow_nonneg (Nat.cast_nonneg h) _) ht hD htr
    (fun A hA hA' hr => havg A (mem_filter.mpr ⟨hA,hA',hr⟩))
  refine ⟨Y,hYm,hY,?_⟩
  intro i hiz
  exact P.simultaneous_bad_bound G hz hJ (univ.filter (fun e => t < resistance G Y e))
    (by positivity : 0 ≤ (h:ℝ)^(-31/40:ℝ)/t+1/(h:ℝ)) hnode i hiz

lemma quarter_negative_power {x y : ℝ} (hx : 0 < x) (hxy : x/4 ≤ y) :
    y^(-31/40:ℝ) ≤ 4*x^(-31/40:ℝ) := by
  have hh := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < x/4) hxy
    (by norm_num : (-31/40:ℝ) ≤ 0)
  have hp : (4:ℝ)^(31/40:ℝ) ≤ 4 :=
    Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
  have heq : (x/4)^(-31/40:ℝ)=x^(-31/40:ℝ)*(4:ℝ)^(31/40:ℝ) := by
    rw [Real.div_rpow hx.le (by norm_num),div_eq_mul_inv,
      ←Real.rpow_neg (by norm_num : (0:ℝ) ≤ 4)]
    norm_num
  rw [heq] at hh
  exact hh.trans (by nlinarith [Real.rpow_nonneg hx.le (-31/40:ℝ)])

lemma response_fraction_cutoff :
    ∃r0 : ℕ, 2 ≤ r0 ∧ ∀r : ℕ, r0 ≤ r → ∀s : ℝ,
      0 < s → s ≤ (r:ℝ)^(1/4:ℝ) →
      16*(((r/2:ℕ):ℝ)^(-31/40:ℝ)/(1/(6*s))+1/((r/2:ℕ):ℝ)) ≤ (r:ℝ)^(-1/3:ℝ) := by
  open Filter in
  have he : ∀ᶠ x : ℝ in atTop,
      128*x^(-1:ℝ) ≤ x^(-1/3:ℝ) ∧ 768*x^(-21/40:ℝ) ≤ x^(-1/3:ℝ) := by
    exact (ShortcutNumeric.eventually_const_mul_rpow_le_rpow 128 (by norm_num)).and
      (ShortcutNumeric.eventually_const_mul_rpow_le_rpow 768 (by norm_num))
  open Filter in
  have heN : ∀ᶠ r : ℕ in atTop,
      128*(r:ℝ)^(-1:ℝ) ≤ (r:ℝ)^(-1/3:ℝ) ∧
      768*(r:ℝ)^(-21/40:ℝ) ≤ (r:ℝ)^(-1/3:ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun r : ℕ => (r:ℝ)) atTop atTop).eventually he
  obtain ⟨r0,hr0⟩ := heN.exists_forall_of_atTop
  refine ⟨max 2 r0,le_max_left _ _,?_⟩
  intro r hr s hs hsR
  have hr2 : 2 ≤ r := (le_max_left _ _).trans hr
  have hlarge := hr0 r ((le_max_right _ _).trans hr)
  have hrR : (0:ℝ) < r := Nat.cast_pos.mpr (by omega)
  have hrh : (r:ℝ)/4 ≤ ((r/2:ℕ):ℝ) := by
    have hnn : r ≤ 4*(r/2) := by omega
    have hrr : (r:ℝ) ≤ 4*((r/2:ℕ):ℝ) := by exact_mod_cast hnn
    linarith
  have hhR : (0:ℝ) < ((r/2:ℕ):ℝ) := lt_of_lt_of_le (by positivity) hrh
  have hpow := quarter_negative_power hrR hrh
  have hprod : (r:ℝ)^(1/4:ℝ)*(r:ℝ)^(-31/40:ℝ)=(r:ℝ)^(-21/40:ℝ) := by
    rw [←Real.rpow_add hrR]
    norm_num
  have hp := mul_le_mul hsR hpow (Real.rpow_nonneg hhR.le _) (Real.rpow_nonneg hrR.le _)
  have hp' : s*((r/2:ℕ):ℝ)^(-31/40:ℝ) ≤ 4*(r:ℝ)^(-21/40:ℝ) := by
    nlinarith only [hp,hprod]
  have hi : 1/((r/2:ℕ):ℝ) ≤ 4/(r:ℝ) := by
    apply (div_le_div_iff₀ hhR hrR).mpr
    linarith
  have ht : ((r/2:ℕ):ℝ)^(-31/40:ℝ)/(1/(6*s))=
      6*(s*((r/2:ℕ):ℝ)^(-31/40:ℝ)) := by
    simp only [one_div,div_inv_eq_mul]
    ring
  rw [ht]
  have hl1 := hlarge.1
  rw [Real.rpow_neg_one] at hl1
  have hl2 := hlarge.2
  nlinarith [show 4/(r:ℝ)=4*(r:ℝ)⁻¹ by ring]

theorem simultaneous_metric_response :
    ∃r0 : ℕ, 2 ≤ r0 ∧ ∀r : ℕ, r0 ≤ r →
      ∀(n m : ℕ) (H : MultiGraph n m), 2 ≤ n → H.Connected univ →
      ∀(F : Finset (Fin m)) (P : PartitionChain n) (z : ℕ), P.parts z={univ} →
      (∀i ≤ z, ∀A ∈ P.parts i, (H.restrict F).EdgeConnectedReal A (r/2:ℕ)) →
      ∀s : ℝ, 0 < s → s ≤ (r:ℝ)^(1/4:ℝ) →
      ∃Y ∈ metricDomain H, CenteredPositive Y ∧ ∀i ≤ z,
        (((P.crossing (H.restrict F) i).filter (fun e =>
          ¬ (6*s) • vecMulVec ((H.restrict F).incidence e) ((H.restrict F).incidence e) ≤ Y)).card:ℝ) ≤
          (r:ℝ)^(-1/3:ℝ)*(P.crossing (H.restrict F) i).card := by
  obtain ⟨h0,hh0,hresp⟩ := simultaneous_metric_response_bound
  obtain ⟨r1,hr1,hfrac⟩ := response_fraction_cutoff
  refine ⟨max (2*h0) r1,hr1.trans (le_max_right _ _),?_⟩
  intro r hr n m H hn _ F P z hz hlocal s hs hsR
  have hrh : h0 ≤ r/2 := by have := (le_max_left _ _).trans hr; omega
  have hrr : r1 ≤ r := (le_max_right _ _).trans hr
  have ht : 0 < 1/(6*s) := by positivity
  obtain ⟨Y,hYm,hY,hbad⟩ := hresp (r/2) hrh n F.card m (H.restrict F) H hn
    (restrict_laplacian_le H F) P z hz hlocal (1/(6*s)) ht
  refine ⟨Y,hYm,hY,?_⟩
  intro i hi
  have heq : (P.crossing (H.restrict F) i).filter (fun e =>
      ¬ (6*s) • vecMulVec ((H.restrict F).incidence e) ((H.restrict F).incidence e) ≤ Y) =
      (univ.filter (fun e => 1/(6*s) < resistance (H.restrict F) Y e)) ∩
        P.crossing (H.restrict F) i := by
    ext e
    simp only [mem_filter,mem_inter,mem_univ,true_and]
    have hor := centered_resistance_order (by omega : 0 < n) hY
      (incidence_sum (H.restrict F) e) (by positivity : 0 < 6*s)
    rw [Matrix.le_iff,hor,not_le]
    have he : 1 < 6*s*qform (inverseOnZeroSum Y) ((H.restrict F).incidence e) ↔
        1/(6*s) < resistance (H.restrict F) Y e := by
      unfold resistance
      rw [div_lt_iff₀ (by positivity : 0 < 6*s)]
      rw [mul_comm]
    rw [he,and_comm]
  rw [heq]
  exact (hbad i hi).trans (mul_le_mul_of_nonneg_right (hfrac r hrr s hs hsR) (Nat.cast_nonneg _))

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_PartitionResponse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Partition response. -/

section

namespace AlgorithmicThinTrees.Partitions
noncomputable section
open Finset Matrix StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder

variable {n m : ℕ}

lemma lift_restrict_crossing (H : MultiGraph n m) (F : Finset (Fin m)) (p : Setoid (Fin n)) :
    liftEdges F (crossing (H.restrict F) p)=crossing H p ∩ F := by
  ext e
  simp only [liftEdges,mem_map,mem_crossing,mem_inter]
  constructor
  · rintro ⟨i,hi,rfl⟩
    exact ⟨hi,embedding_mem F i⟩
  · rintro ⟨hi,he⟩
    obtain ⟨i,rfl⟩ := embedding_surj F he
    exact ⟨i,hi,rfl⟩

lemma restrict_crossing_card (H : MultiGraph n m) (F : Finset (Fin m)) (p : Setoid (Fin n)) :
    (crossing (H.restrict F) p).card=(crossing H p ∩ F).card := by
  rw [←lift_restrict_crossing,liftEdges,card_map]

lemma lift_restrict_crossing_filter (H : MultiGraph n m) (F : Finset (Fin m)) (p : Setoid (Fin n))
    (b : Fin m → Prop) :
    liftEdges F ((crossing (H.restrict F) p).filter (fun e => b (edgeEmbedding F e)))=
      (crossing H p ∩ F).filter b := by
  rw [←lift_restrict_crossing,liftEdges,liftEdges,filter_map]
  congr 1

lemma restrict_bad_card (H : MultiGraph n m) (F : Finset (Fin m)) (p : Setoid (Fin n))
    (b : Fin m → Prop) :
    ((crossing (H.restrict F) p).filter (fun e => b (edgeEmbedding F e))).card=
      ((crossing H p ∩ F).filter b).card := by
  rw [←lift_restrict_crossing_filter,liftEdges,card_map]

open MetricTests

theorem finite_chain_response_oai :
    ∃r0 : ℕ, 2 ≤ r0 ∧ ∀r : ℕ, r0 ≤ r →
      ∀(n m : ℕ) (H : MultiGraph n m), 2 ≤ n → H.Connected univ →
      ∀(F : Finset (Fin m)) (J : Finset (Setoid (Fin n))),
      IsChain (· ≤ ·) (J : Set (Setoid (Fin n))) →
      (∀p ∈ J, ∀A ∈ parts p, (H.restrict F).EdgeConnectedReal A (r/2:ℕ)) →
      (H.restrict F).EdgeConnectedReal univ (r/2:ℕ) →
      ∀s : ℝ, 0 < s → s ≤ (r:ℝ)^(1/4:ℝ) →
      ∃Y ∈ metricDomain H, CenteredPositive Y ∧ ∀p ∈ J,
        (((crossing H p ∩ F).filter (fun e =>
          ¬ (6*s) • vecMulVec (H.incidence e) (H.incidence e) ≤ Y)).card:ℝ) ≤
          (r:ℝ)^(-1/3:ℝ)*(crossing H p ∩ F).card := by
  obtain ⟨r0,hr0,hresp⟩ := simultaneous_metric_response
  refine ⟨r0,hr0,?_⟩
  intro r hr n m H hn hconn F J hJ hlocal hroot s hs hsR
  have : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
  obtain ⟨f,hf,hfroot,hfmem,hfsurj⟩ := enumerate_chain J hJ
  let P := toChain f hf
  have hpF : P.parts J.card={univ} := by
    change parts (f J.card)={univ}
    rw [hfroot,parts_top]
  have hpL : ∀i ≤ J.card, ∀A ∈ P.parts i, (H.restrict F).EdgeConnectedReal A (r/2:ℕ) := by
    intro i _ A hA
    rcases hfmem i with hi | hi
    · exact hlocal (f i) hi A hA
    · change A ∈ parts (f i) at hA
      rw [hi,parts_top,mem_singleton] at hA
      exact hA ▸ hroot
  obtain ⟨Y,hY,hYP,hbad⟩ := hresp r hr n m H hn hconn F P J.card hpF hpL s hs hsR
  refine ⟨Y,hY,hYP,?_⟩
  intro p hp
  obtain ⟨i,hi,hfi⟩ := hfsurj p hp
  have hh := hbad i hi.le
  rw [toChain_crossing,hfi,restrict_crossing_card] at hh
  have he := restrict_bad_card H F p
    (fun e => ¬ (6*s) • vecMulVec (H.incidence e) (H.incidence e) ≤ Y)
  have hinc (e : Fin F.card) : (H.restrict F).incidence e=H.incidence (edgeEmbedding F e) := by
    ext v
    simp only [MultiGraph.incidence,MultiGraph.restrict,Pi.sub_apply]
  simp_rw [hinc] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  convert he.symm using 1 <;> first | (with_reducible_and_instances rfl) | (congr 1 <;> ext e <;> simp only [mem_filter])

end
end AlgorithmicThinTrees.Partitions
end

end OAI
end

theorem solution : type_of% @OAI.AlgorithmicThinTrees.Partitions.finite_chain_response_oai := @OAI.AlgorithmicThinTrees.Partitions.finite_chain_response_oai
