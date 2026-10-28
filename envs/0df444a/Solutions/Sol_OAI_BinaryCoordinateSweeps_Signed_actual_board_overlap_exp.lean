-- Prove2me | solution 1 for OAI.BinaryCoordinateSweeps.Signed.actual_board_overlap_exp
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T15:58:37.197454+00:00
-- url     : https://prove2.me/submissions/7112cb84-fef0-4797-a43b-62381e098c62

import Mathlib
import Definitions.Def_OAIB3Bs000

section
-- module Solutions.OAIB3_Bsw.Compat
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_TensorBounds_PiTensorMatrices
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical ComplexOrder MatrixOrder
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {I : Type*} [Fintype I] [DecidableEq I]
  {A B C : I → Type*} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
  [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)]
  [∀ i, Fintype (C i)] [∀ i, DecidableEq (C i)]

omit [∀ index, Fintype (A index)] [∀ index, DecidableEq (A index)]
  [∀ index, DecidableEq (B index)] [∀ index, Fintype (C index)]
  [∀ index, DecidableEq (C index)] in
lemma piTensorMatrices_mul (M : ∀ i, Matrix (A i) (B i) ℂ)
    (N : ∀ i, Matrix (B i) (C i) ℂ) :
    piTensorMatrices M * piTensorMatrices N = piTensorMatrices (fun i => M i*N i) := by
  ext x z
  simp only [Matrix.mul_apply,piTensorMatrices,← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i b => M i (x i) b * N i b (z i))).symm

omit [DecidableEq I] [∀ index, Fintype (A index)] [∀ index, DecidableEq (A index)]
  [∀ index, Fintype (B index)] [∀ index, DecidableEq (B index)] in
lemma piTensorMatrices_star (M : ∀ i, Matrix (A i) (B i) ℂ) :
    (piTensorMatrices M).conjTranspose = piTensorMatrices (fun i => (M i).conjTranspose) := by
  ext x y
  simp [piTensorMatrices]

omit [DecidableEq I] [∀ index, Fintype (A index)] in
lemma piTensorMatrices_one : piTensorMatrices (fun i : I => (1 : Matrix (A i) (A i) ℂ))=1 := by
  ext x y
  by_cases h : x=y
  · subst y; simp [piTensorMatrices]
  · obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    simp only [piTensorMatrices,Matrix.one_apply,ite_eq_right h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

lemma piTensorMatrices_psd (M : ∀ i, Matrix (A i) (A i) ℂ) (hM : ∀ i, (M i).PosSemidef) :
    (piTensorMatrices M).PosSemidef := by
  have hx (i : I) : ∃ X : Matrix (A i) (A i) ℂ, M i=X.conjTranspose*X :=
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (hM i).nonneg
  choose X hX using hx
  have he : piTensorMatrices M = (piTensorMatrices X).conjTranspose*piTensorMatrices X := by
    rw [piTensorMatrices_star,piTensorMatrices_mul]
    congr 1
    funext i
    exact hX i
  rw [he]
  exact Matrix.posSemidef_conjTranspose_mul_self _

omit [DecidableEq I] [∀ index, Fintype (A index)] [∀ index, DecidableEq (A index)]
  [∀ index, Fintype (B index)] [∀ index, DecidableEq (B index)] in
lemma piTensorMatrices_smul (c : I → ℂ) (M : ∀ i, Matrix (A i) (B i) ℂ) :
    piTensorMatrices (fun i => c i • M i) = (∏i, c i) • piTensorMatrices M := by
  ext x y
  simp only [piTensorMatrices,Matrix.smul_apply,smul_eq_mul,Finset.prod_mul_distrib]

omit [∀ index, Fintype (A index)] [∀ index, DecidableEq (A index)]
  [∀ index, Fintype (B index)] [∀ index, DecidableEq (B index)] in
lemma piTensorMatrices_sum {W : I → Type*} [∀ i, Fintype (W i)]
    (M : ∀ i, W i → Matrix (A i) (B i) ℂ) :
    piTensorMatrices (fun i => ∑w, M i w) = ∑f : ∀ i, W i, piTensorMatrices (fun i => M i (f i)) := by
  ext x y
  simp only [piTensorMatrices,Matrix.sum_apply]
  exact Fintype.prod_sum (fun i w => M i w (x i) (y i))

lemma piTensorMatrices_mono (M N : ∀ i, Matrix (A i) (A i) ℂ)
    (hM : ∀ i, (M i).PosSemidef) (hMN : ∀ i, (N i-M i).PosSemidef) :
    (piTensorMatrices N-piTensorMatrices M).PosSemidef := by
  let T (i : I) (b : Bool) := if b then N i-M i else M i
  have he : piTensorMatrices N = ∑f : I → Bool, piTensorMatrices (fun i => T i (f i)) := by
    rw [← piTensorMatrices_sum]
    congr 1
    funext i
    simp [T]
  have hf : piTensorMatrices M = piTensorMatrices (fun i => T i false) := by simp [T]
  rw [he,hf,← Finset.sum_erase_add _ _ (Finset.mem_univ (fun _ : I => false)),add_sub_cancel_right]
  apply Matrix.posSemidef_sum
  intro f _
  apply piTensorMatrices_psd
  intro i
  dsimp [T]
  split
  · exact hMN i
  · exact hM i

theorem piTensor_density_domination {W : I → Type*} [∀ i, Fintype (W i)]
    (P : ∀ i, Matrix (A i) (A i) ℂ) (r : ∀ i, W i → Matrix (A i) (A i) ℂ)
    (c : I → ℂ) (hP : ∀ i, (P i).PosSemidef)
    (hdom : ∀ i, (c i • ∑w, r i w-P i).PosSemidef) :
    ((∏i, c i) • (∑f : ∀ i, W i, piTensorMatrices (fun i => r i (f i)))-piTensorMatrices P).PosSemidef := by
  have h := piTensorMatrices_mono P (fun i => c i • ∑w, r i w) hP hdom
  rwa [piTensorMatrices_smul,piTensorMatrices_sum] at h

end BinaryCoordinateSweeps.Density

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_MatrixBounds_PositiveTraceRestriction
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical ComplexOrder

namespace BinaryCoordinateSweeps
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [FiniteDimensional ℂ W]

theorem positive_trace_restrict_le (S : Submodule ℂ W) (B : W →ₗ[ℂ] W)
    (hB : B.IsPositive) (hS : ∀ x ∈ S, B x ∈ S) :
    (LinearMap.trace ℂ S (B.restrict hS)).re ≤ (LinearMap.trace ℂ W B).re := by
  let P := S.starProjection.toLinearMap
  let Q : W →ₗ[ℂ] W := 1-P
  have hPsy : P.IsSymmetric := (Submodule.isSymmetricProjection_starProjection S).isSymmetric
  have hQsy : Q.IsSymmetric := LinearMap.IsSymmetric.id.sub hPsy
  have hPP : P*P = P := by
    ext x
    exact congrArg (fun t : W →L[ℂ] W => t x) S.isIdempotentElem_starProjection
  have hQQ : Q*Q = Q := by
    dsimp [Q]
    noncomm_ring [hPP]
  have hQBQ : (Q*B*Q).IsPositive := by
    simpa only [Module.End.mul_eq_comp,LinearMap.comp_assoc,hQsy.adjoint_eq] using hB.conj_adjoint Q
  have hpRange : ∀ x, ((P*B)*P) x ∈ S := by
    intro x
    exact S.starProjection_apply_mem _
  have hpRestr : ((P*B)*P).restrict (fun x _ => hpRange x) = B.restrict hS := by
    ext x
    change P (B (P x.val)) = B x.val
    rw [show P x.val = x.val from Submodule.starProjection_eq_self_iff.mpr x.property]
    exact Submodule.starProjection_eq_self_iff.mpr (hS x.val x.property)
  have hTrP : LinearMap.trace ℂ W (P*B*P) = LinearMap.trace ℂ W (B*P) := by
    change LinearMap.trace ℂ W (P.comp (B*P)) = _
    rw [LinearMap.trace_comp_comm']
    change LinearMap.trace ℂ W (B*P*P) = _
    rw [mul_assoc,hPP]
  have hTrQ : LinearMap.trace ℂ W (Q*B*Q) = LinearMap.trace ℂ W B -
      LinearMap.trace ℂ W (B*P) := by
    change LinearMap.trace ℂ W (Q.comp (B*Q)) = _
    rw [LinearMap.trace_comp_comm']
    change LinearMap.trace ℂ W (B*Q*Q) = _
    rw [mul_assoc,hQQ]
    dsimp [Q]
    rw [mul_sub,mul_one,map_sub]
  have hTrace := LinearMap.trace_restrict_eq_of_forall_mem S (P*B*P) hpRange
  rw [hpRestr,hTrP] at hTrace
  have hn := (Complex.nonneg_iff.mp hQBQ.trace_nonneg).1
  rw [hTrQ,Complex.sub_re,← hTrace] at hn
  linarith

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

theorem multiplicity_le_commutant [ρ.IsIrreducible] :
    Module.finrank ℂ (IntertwiningMap ρ σ) ≤ Module.finrank ℂ (IntertwiningMap σ σ) := by
  by_cases h : ∃ f : IntertwiningMap ρ σ, f ≠ 0
  · obtain ⟨f,hf⟩ := h
    have hfi : Function.Injective f := (IsIrreducible.injective_or_eq_zero f).resolve_right hf
    obtain ⟨r,hr⟩ := intertwiner_retraction ρ σ f hfi
    let T : IntertwiningMap ρ σ →ₗ[ℂ] IntertwiningMap σ σ :=
      (IntertwiningMap.llcomp σ ρ σ).flip r
    have hT : Function.Injective T := by
      intro a b hab
      ext v
      have hh := congrArg (fun t : IntertwiningMap σ σ => t (f v)) hab
      change a (r (f v)) = b (r (f v)) at hh
      change a v = b v
      simpa only [hr] using hh
    exact LinearMap.finrank_le_finrank_of_injective hT
  · have hs : Subsingleton (IntertwiningMap ρ σ) := ⟨by
      intro a b
      have ha : a=0 := by_contra (fun ha => h ⟨a,ha⟩)
      have hb : b=0 := by_contra (fun hb => h ⟨b,hb⟩)
      exact ha.trans hb.symm⟩
    rw [Module.finrank_eq_zero_of_subsingleton]
    exact Nat.zero_le _

omit [Fintype G] in
lemma isotypicSpan_finrank : Module.finrank ℂ (isotypicSpan ρ σ) ≤
    Module.finrank ℂ V * Module.finrank ℂ (IntertwiningMap ρ σ) := by
  rw [← evaluation_range]
  simpa only [Module.finrank_tensorProduct] using LinearMap.finrank_range_le (evaluation ρ σ)

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
-- module Solutions.OAIB3_Bsw.BinarySweep_MatrixBounds_MatrixProjection
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical ComplexOrder
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma projectionMatrix_linear (S : Submodule ℂ (EuclideanSpace ℂ I)) :
    (projectionMatrix S).toEuclideanLin = S.starProjection.toLinearMap := by
  have h := (Matrix.toEuclideanCLM (𝕜 := ℂ)).apply_symm_apply S.starProjection
  exact congrArg ContinuousLinearMap.toLinearMap h

lemma projectionMatrix_psd (S : Submodule ℂ (EuclideanSpace ℂ I)) :
    (projectionMatrix S).PosSemidef := by
  rw [← Matrix.isPositive_toEuclideanLin_iff, projectionMatrix_linear]
  exact (Submodule.isSymmetricProjection_starProjection S).isPositive

lemma projectionMatrix_idempotent (S : Submodule ℂ (EuclideanSpace ℂ I)) :
    projectionMatrix S * projectionMatrix S = projectionMatrix S := by
  apply (Matrix.toEuclideanCLM (𝕜 := ℂ)).injective
  simp only [map_mul]
  have h : (Matrix.toEuclideanCLM (𝕜 := ℂ)).toRingEquiv (projectionMatrix S) =
      S.starProjection := (Matrix.toEuclideanCLM (𝕜 := ℂ)).apply_symm_apply _
  rw [h]
  exact S.isIdempotentElem_starProjection

lemma trace_toEuclideanLinear (M : Matrix I I ℂ) :
    LinearMap.trace ℂ (EuclideanSpace ℂ I) M.toEuclideanLin = M.trace := by
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun I ℂ)]
  unfold Matrix.trace
  apply Finset.sum_congr rfl
  intro i _
  simp [EuclideanSpace.basisFun_apply, PiLp.inner_apply, Matrix.ofLp_toLpLin,
    Matrix.toLin'_apply, PiLp.ofLp_single, Matrix.mulVec, dotProduct, Pi.single_apply]

lemma projectionMatrix_trace (S : Submodule ℂ (EuclideanSpace ℂ I)) :
    (projectionMatrix S).trace = (Module.finrank ℂ S : ℂ) := by
  rw [← trace_toEuclideanLinear, projectionMatrix_linear]
  have h : LinearMap.IsProj S S.starProjection.toLinearMap :=
    ⟨S.starProjection_apply_mem, fun v hv => Submodule.starProjection_eq_self_iff.mpr hv⟩
  exact h.trace

lemma projectionMatrix_coeff (S : Submodule ℂ (EuclideanSpace ℂ I)) :
    LinearMap.toMatrix' ((WithLp.linearEquiv 2 ℂ (I → ℂ)).conj S.starProjection.toLinearMap) =
      projectionMatrix S := by
  apply Matrix.toEuclideanLin.injective
  rw [projectionMatrix_linear]
  ext v i
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin, LinearEquiv.conj_apply]
  simp

end BinaryCoordinateSweeps.Density

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Representations_IsotypicSpectral
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical ComplexOrder

namespace BinaryCoordinateSweeps.Irrep
open Representation

variable {G V W : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  (ρ : Representation ℂ G V) (σ : Representation ℂ G W)

omit [Fintype G] [FiniteDimensional ℂ V] in
lemma eigenvalue_multiplicity_ge [ρ.IsIrreducible] (T : Module.End ℂ W)
    (hT : ∀ g w, T (σ g w) = σ g (T w))
    (hσ : ∀ g w, ‖σ g w‖ = ‖w‖) (μ : ℂ)
    {w : W} (hw : w ∈ isotypicSpan ρ σ) (he : T w = μ • w) (hn : w ≠ 0) :
    Module.finrank ℂ V ≤ Module.finrank ℂ (T.eigenspace μ) := by
  let P := eigenspaceProjectionIntertwiner σ T hT hσ μ
  have hP : ∃ f : IntertwiningMap ρ σ, P.comp f ≠ 0 := by
    by_contra! hall
    have hz : P w = 0 := by
      change w ∈ ⨆ f : IntertwiningMap ρ σ, LinearMap.range f.toLinearMap at hw
      refine Submodule.iSup_induction _ (motive := fun x => P x = 0) hw ?_ (map_zero P) ?_
      · intro f x hx
        obtain ⟨v,rfl⟩ := hx
        exact DFunLike.congr_fun (hall f) v
      · intro x y hx hy
        rw [map_add,hx,hy,zero_add]
    have hpw : P w = w := Submodule.starProjection_eq_self_iff.mpr
      (Module.End.mem_eigenspace_iff.mpr he)
    exact hn (hpw.symm.trans hz)
  obtain ⟨f,hf⟩ := hP
  have hi := (IsIrreducible.injective_or_eq_zero (P.comp f)).resolve_right hf
  let Q : V →ₗ[ℂ] T.eigenspace μ := (P.comp f).toLinearMap.codRestrict _
    (fun v => (T.eigenspace μ).starProjection_apply_mem (f v))
  apply LinearMap.finrank_le_finrank_of_injective (f:=Q)
  intro v v' hv
  exact hi (congrArg Subtype.val hv)

omit [Fintype G] [FiniteDimensional ℂ V] in
theorem isotypic_eigenvalue_trace_le [ρ.IsIrreducible] (T : Module.End ℂ W)
    (hpos : T.IsPositive) (hT : ∀ g w, T (σ g w) = σ g (T w))
    (hσ : ∀ g w, ‖σ g w‖ = ‖w‖) {μ : ℝ} (hμ : 0 ≤ μ)
    {w : W} (hw : w ∈ isotypicSpan ρ σ) (he : T w = (μ:ℂ) • w) (hn : w ≠ 0) :
    (Module.finrank ℂ V : ℝ) * μ ≤ (LinearMap.trace ℂ W T).re := by
  let E := T.eigenspace (μ:ℂ)
  have hE : ∀ x ∈ E, T x ∈ E := by
    intro x hx
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    rw [hx,map_smul,hx]
  have hr : T.restrict hE = (μ:ℂ) • (LinearMap.id : E →ₗ[ℂ] E) := by
    ext x
    exact Module.End.mem_eigenspace_iff.mp x.property
  have ht := positive_trace_restrict_le E T hpos hE
  rw [hr,map_smul,LinearMap.trace_id] at ht
  have hd := eigenvalue_multiplicity_ge ρ σ T hT hσ (μ:ℂ) hw he hn
  have hd' : (Module.finrank ℂ V : ℝ) ≤ (Module.finrank ℂ E : ℝ) := by exact_mod_cast hd
  have ht' : μ * (Module.finrank ℂ E : ℝ) ≤ (LinearMap.trace ℂ W T).re := by
    simpa using ht
  nlinarith

end BinaryCoordinateSweeps.Irrep

end

open scoped BigOperators Classical ComplexOrder

namespace BinaryCoordinateSweeps.Irrep
open Representation

variable {G V W : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  (ρ : Representation ℂ G V) (σ : Representation ℂ G W)

omit [Fintype G] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
lemma isotypic_restrict_positive (T : Module.End ℂ W) (hpos : T.IsPositive)
    (hT : ∀ g w, T (σ g w) = σ g (T w)) :
    (T.restrict (commuting_isotypic_invariant ρ σ T hT)).IsPositive :=
  ⟨hpos.isSymmetric.restrict_invariant _, fun x => hpos.2 x.val⟩

omit [Fintype G] [FiniteDimensional ℂ V] in
theorem isotypic_restriction_cap [ρ.IsIrreducible] (T : Module.End ℂ W)
    (hpos : T.IsPositive) (hT : ∀ g w, T (σ g w) = σ g (T w))
    (hσ : ∀ g w, ‖σ g w‖ = ‖w‖) :
    (((LinearMap.trace ℂ W T).re : ℂ) • (LinearMap.id : isotypicSpan ρ σ →ₗ[ℂ] isotypicSpan ρ σ) -
      (Module.finrank ℂ V : ℂ) • T.restrict (commuting_isotypic_invariant ρ σ T hT)).IsPositive := by
  let S := isotypicSpan ρ σ
  let R := T.restrict (commuting_isotypic_invariant ρ σ T hT)
  have hR : R.IsPositive := isotypic_restrict_positive ρ σ T hpos hT
  let b := hR.isSymmetric.eigenvectorBasis rfl
  apply (LinearMap.posSemidef_toMatrix_iff b).mp
  rw [map_sub,map_smul,map_smul,LinearMap.toMatrix_id]
  rw [show LinearMap.toMatrix b.toBasis b.toBasis R =
    Matrix.diagonal (fun i => (hR.isSymmetric.eigenvalues rfl i : ℂ)) from
      hR.isSymmetric.toMatrix_eigenvectorBasis rfl]
  rw [← Matrix.diagonal_one,← Matrix.diagonal_smul,← Matrix.diagonal_smul,Matrix.diagonal_sub]
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro i
  have hi := isotypic_eigenvalue_trace_le ρ σ T hpos hT hσ
    (hR.nonneg_eigenvalues rfl i) (b i).property
    (congrArg Subtype.val (hR.isSymmetric.apply_eigenvectorBasis rfl i))
    (fun hz => (hR.isSymmetric.hasEigenvector_eigenvectorBasis rfl i).2 (Subtype.ext hz))
  change 0 ≤ ((LinearMap.trace ℂ W T).re : ℂ)*1 - _
  have he : (0:ℂ) ≤ (((LinearMap.trace ℂ W T).re -
      (Module.finrank ℂ V : ℝ)*hR.isSymmetric.eigenvalues rfl i : ℝ):ℂ) := by
    exact_mod_cast sub_nonneg.mpr hi
  simpa using he

end BinaryCoordinateSweeps.Irrep

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_MatrixBounds_MatrixSqrtBlocks
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical ComplexOrder MatrixOrder
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J]

lemma block_diagonal_commute (f : I → J) (Q : Matrix I I ℂ)
    (hQ : ∀ i j, f i ≠ f j → Q i j = 0) (a : J) :
    Commute Q (Matrix.diagonal (fun i => if f i = a then (1 : ℂ) else 0)) := by
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : f i = f j
  · rw [h]; ring
  · rw [hQ i j h]; ring

lemma sqrt_block_diagonal (f : I → J) (Q : Matrix I I ℂ)
    (hQ : ∀ i j, f i ≠ f j → Q i j = 0) :
    ∀ i j, f i ≠ f j → CFC.sqrt Q i j = 0 := by
  intro i j hij
  have h := (block_diagonal_commute f Q hQ (f i)).cfc_nnreal NNReal.sqrt
  rw [← CFC.sqrt_eq_cfc] at h
  have hh := congrFun (congrFun h.eq i) j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, ite_true,
    ite_eq_right (Ne.symm hij), mul_zero, one_mul] at hh
  exact hh.symm

lemma sqrt_submatrix_invariant (Q : Matrix I I ℂ) (hQ : Q.PosSemidef)
    (e : Equiv.Perm I) (he : Q.submatrix e e = Q) :
    (CFC.sqrt Q).submatrix e e = CFC.sqrt Q := by
  apply Eq.symm
  apply CFC.sqrt_unique _ ((CFC.sqrt_nonneg Q).posSemidef.submatrix e).nonneg
  rw [Matrix.submatrix_mul_equiv, CFC.sqrt_mul_sqrt_self Q hQ.nonneg, he]

lemma sqrt_gram (Q : Matrix I I ℂ) (hQ : Q.PosSemidef) :
    CFC.sqrt Q * (CFC.sqrt Q).conjTranspose = Q := by
  rw [(CFC.sqrt_nonneg Q).posSemidef.1.eq, CFC.sqrt_mul_sqrt_self Q hQ.nonneg]

end BinaryCoordinateSweeps.Density

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_TensorBounds_TypeMass
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators

namespace BinaryCoordinateSweeps.Density

lemma factorial_mode (b c : ℕ) : c.factorial * c^b ≤ b.factorial * c^c := by
  rcases le_total c b with h | h
  · have hi := Nat.factorial_mul_pow_sub_le_factorial h
    calc
      c.factorial * c^b = (c.factorial * c^(b-c)) * c^c := by
        rw [mul_assoc, ← pow_add, Nat.sub_add_cancel h]
      _ ≤ b.factorial * c^c := Nat.mul_le_mul_right _ hi
  · have hi : c.factorial ≤ b.factorial * c^(c-b) := by
      calc
        c.factorial = b.factorial * c.descFactorial (c-b) := by
          simpa only [Nat.sub_sub_self h] using
            (Nat.factorial_mul_descFactorial (Nat.sub_le c b)).symm
        _ ≤ _ := Nat.mul_le_mul_left _ (Nat.descFactorial_le_pow _ _)
    calc
      c.factorial * c^b ≤ (b.factorial * c^(c-b)) * c^b := Nat.mul_le_mul_right _ hi
      _ = b.factorial * c^c := by rw [mul_assoc, ← pow_add, Nat.sub_add_cancel h]

variable {A : Type*} [Fintype A] [DecidableEq A]

omit [DecidableEq A] in
lemma multinomial_mode (n : ℕ) (c b : A → ℕ) (hc : ∑ a, c a = n) (hb : ∑ a, b a = n) :
    Nat.multinomial Finset.univ b * ∏ a, (c a)^(b a) ≤
      Nat.multinomial Finset.univ c * ∏ a, (c a)^(c a) := by
  have h := Finset.prod_le_prod' (fun a (_ : a ∈ (Finset.univ : Finset A)) => factorial_mode (b a) (c a))
  simp only [Finset.prod_mul_distrib] at h
  have hbs := Nat.multinomial_spec (s := Finset.univ) (f := b)
  have hcs := Nat.multinomial_spec (s := Finset.univ) (f := c)
  rw [hb] at hbs
  rw [hc] at hcs
  refine Nat.le_of_mul_le_mul_left (c := n.factorial) ?_ (Nat.factorial_pos n)
  calc
    n.factorial * (Nat.multinomial Finset.univ b * ∏ a, c a ^ b a) =
        (Nat.multinomial Finset.univ b * Nat.multinomial Finset.univ c) *
          ((∏ a, (c a).factorial) * ∏ a, c a ^ b a) := by rw [← hcs]; ring
    _ ≤ (Nat.multinomial Finset.univ b * Nat.multinomial Finset.univ c) *
          ((∏ a, (b a).factorial) * ∏ a, c a ^ c a) := Nat.mul_le_mul_left _ h
    _ = n.factorial * (Nat.multinomial Finset.univ c * ∏ a, c a ^ c a) := by rw [← hbs]; ring

lemma card_types_le (n : ℕ) :
    (Finset.piAntidiag (Finset.univ : Finset A) n).card ≤ (n+1)^(Fintype.card A) := by
  classical
  let T := ↥(Finset.piAntidiag (Finset.univ : Finset A) n)
  let : Fintype T := FinsetCoe.fintype _
  let f : T → (A → Fin (n+1)) := fun b a => ⟨b.val a, by
    have hb := (Finset.mem_piAntidiag.mp b.property).1
    have hh := Finset.single_le_sum (f := b.val) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
    exact Nat.lt_succ_of_le (hh.trans_eq hb)⟩
  have hf : Function.Injective f := by
    intro b c h
    apply Subtype.ext
    funext a
    exact congrArg Fin.val (congrFun h a)
  have h := Fintype.card_le_of_injective f hf
  simpa [T, Fintype.card_pi] using h

theorem type_mass_lower_nat (n : ℕ) (c : A → ℕ) (hc : ∑ a, c a = n) :
    n^n ≤ (n+1)^(Fintype.card A) *
      (Nat.multinomial Finset.univ c * ∏ a, c a ^ c a) := by
  calc
    n^n = ∑ b ∈ Finset.piAntidiag Finset.univ n,
        Nat.multinomial Finset.univ b * ∏ a, c a ^ b a := by
      simpa only [Nat.cast_id, hc] using Finset.sum_pow_eq_sum_piAntidiag Finset.univ c n
    _ ≤ ∑ _b ∈ Finset.piAntidiag (Finset.univ : Finset A) n,
        Nat.multinomial Finset.univ c * ∏ a, c a ^ c a := by
      apply Finset.sum_le_sum
      intro b hb
      exact multinomial_mode n c b hc (Finset.mem_piAntidiag.mp hb).1
    _ = (Finset.piAntidiag (Finset.univ : Finset A) n).card *
        (Nat.multinomial Finset.univ c * ∏ a, c a ^ c a) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (card_types_le n)

theorem type_mass_lower (n : ℕ) (hn : 0 < n) (c : A → ℕ) (hc : ∑ a, c a = n) :
    1 ≤ ((n+1 : ℕ) : ℝ)^(Fintype.card A) *
      ((Nat.multinomial Finset.univ c : ℝ) * ∏ a, ((c a : ℝ) / n) ^ c a) := by
  have h : (n : ℝ)^n ≤ ((n+1 : ℕ) : ℝ)^(Fintype.card A) *
      ((Nat.multinomial Finset.univ c : ℝ) * ∏ a, (c a : ℝ)^c a) := by
    exact_mod_cast type_mass_lower_nat n c hc
  have hn' : 0 < (n : ℝ)^n := pow_pos (by exact_mod_cast hn) _
  simp_rw [div_pow]
  rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, hc]
  rw [← mul_div_assoc, ← mul_div_assoc]
  apply (le_div_iff₀ hn').mpr
  simpa only [one_mul, mul_div_assoc] using h

end BinaryCoordinateSweeps.Density

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Density
variable {A I : Type*} [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]

omit [Fintype A] [DecidableEq I] in
lemma wordCounts_apply (w : I → A) (a : A) :
    wordCounts w a = (Finset.univ.filter (fun i => w i = a)).card := by
  simp only [wordCounts, Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.card_filter]

omit [Fintype A] [DecidableEq I] in
lemma wordCounts_fiber (w : I → A) (a : A) :
    wordCounts w a = Fintype.card {i // w i = a} := by
  rw [Fintype.card_subtype, wordCounts_apply]

omit [DecidableEq I] in
lemma prod_wordCounts {M : Type*} [CommMonoid M] (v : A → M) (w : I → A) :
    ∏ i, v (w i) = ∏ a, v a ^ wordCounts w a := by
  rw [← Fintype.prod_fiberwise' w v]
  apply Finset.prod_congr rfl
  intro a ha
  simp only [Finset.prod_const, Finset.card_univ, wordCounts_fiber]

omit [Fintype A] [DecidableEq I] in
lemma exists_perm_eq_of_wordCounts {w v : I → A} (h : wordCounts w = wordCounts v) :
    ∃ g : Equiv.Perm I, ∀ i, v (g i) = w i := by
  have hc (a : A) : Fintype.card {i // w i = a} = Fintype.card {i // v i = a} := by
    rw [← wordCounts_fiber, ← wordCounts_fiber, h]
  let e (a : A) := Fintype.equivOfCardEq (hc a)
  let g := (Equiv.sigmaFiberEquiv w).symm.trans
    ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv v))
  refine ⟨g, fun i => ?_⟩
  change v ((e (w i) ⟨i,rfl⟩).val) = w i
  exact (e (w i) ⟨i,rfl⟩).property

omit [DecidableEq A] in
lemma word_polynomial (n : ℕ) :
    (∑ a, MvPolynomial.X a : MvPolynomial A ℕ)^n =
      ∑ w : Fin n → A, MvPolynomial.monomial (wordCounts w) 1 := by
  calc
    _ = ∏ _i : Fin n, (∑ a, MvPolynomial.X a : MvPolynomial A ℕ) := by simp
    _ = ∑ w : Fin n → A, ∏ i, (MvPolynomial.X (w i) : MvPolynomial A ℕ) := by
      exact Fintype.prod_sum _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [wordCounts, MvPolynomial.monomial_sum_one]
      rfl

lemma card_words_counts (n : ℕ) (c : A →₀ ℕ) (hc : c.sum (fun _ k => k) = n) :
    Fintype.card {w : Fin n → A // wordCounts w = c} = c.multinomial := by
  have he := congrArg (fun polynomial : MvPolynomial A ℕ => polynomial.coeff c)
    (word_polynomial (A := A) n)
  rw [MvPolynomial.coeff_sum_X_pow_of_fintype, ite_eq_left hc] at he
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Nat.cast_id] at he
  rw [Fintype.card_subtype, Finset.card_filter]
  convert he.symm using 1

lemma card_words_counts_fun (n : ℕ) (c : A → ℕ) (hc : ∑ a, c a = n) :
    Fintype.card {w : Fin n → A // ∀ a, wordCounts w a = c a} =
      Nat.multinomial Finset.univ c := by
  let c' : A →₀ ℕ := Finsupp.equivFunOnFinite.symm c
  have htotal : c'.sum (fun _ k => k) = n := by
    rw [Finsupp.sum_of_support_subset _ (Finset.subset_univ _) _ (by simp)]
    exact hc
  have he : {w : Fin n → A // ∀ a, wordCounts w a = c a} ≃
      {w : Fin n → A // wordCounts w = c'} := Equiv.subtypeEquivRight (fun w => by
    constructor
    · intro h
      apply Finsupp.ext
      exact h
    · intro h a
      exact congrArg (fun b : A →₀ ℕ => b a) h)
  rw [Fintype.card_congr he, card_words_counts n c' htotal,
    Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _)]
  rfl

end BinaryCoordinateSweeps.Density

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_TensorBounds_TensorPhases
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Density
variable {A : Type*} [Fintype A] [DecidableEq A]

omit [DecidableEq A] in
lemma wordCounts_le (n : ℕ) (w : Fin n → A) (a : A) : wordCounts w a ≤ n := by
  have h := Finset.single_le_sum (f := fun a => wordCounts w a)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
  simpa only [wordCounts_sum, Fintype.card_fin] using h

lemma phase_star (n : ℕ) (j : ZMod (n+1)) :
    star (ZMod.stdAddChar j) = ZMod.stdAddChar (-j) := by
  change (starRingEnd ℂ) (ZMod.stdAddChar j) = _
  rw [AddChar.starComp_apply (by rw [ringChar.eq (ZMod (n+1)) (n+1)]; omega : 0 < ringChar (ZMod (n+1)))]
  rfl

omit [Fintype A] in
lemma phase_sum_prod (n : ℕ) (f : A → ZMod (n+1)) (s : Finset A) :
    ZMod.stdAddChar (∑ a ∈ s, f a) = ∏ a ∈ s, ZMod.stdAddChar (f a) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp only [Finset.sum_insert ha, Finset.prod_insert ha,
      AddChar.map_add_eq_mul, ih]

lemma phase_sum (n : ℕ) (b : A → ZMod (n+1)) :
    (∑ θ : A → ZMod (n+1), ZMod.stdAddChar (∑ a, θ a * b a)) =
      if b = 0 then ((n+1 : ℕ) : ℂ) ^ Fintype.card A else 0 := by
  classical
  simp_rw [phase_sum_prod]
  rw [← Fintype.prod_sum (fun a (x : ZMod (n+1)) => ZMod.stdAddChar (x * b a))]
  simp_rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar _), ZMod.card]
  by_cases hb : b = 0
  · simp [hb]
  · rw [ite_eq_right hb]
    obtain ⟨a, ha⟩ : ∃ a, b a ≠ 0 := by simpa only [funext_iff, not_forall, Pi.zero_apply] using hb
    exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp [ha])

lemma tensorPhase_counts (n : ℕ) (θ : A → ZMod (n+1)) (w : Fin n → A) :
    tensorPhase n θ w = ZMod.stdAddChar (∑ a, θ a * (wordCounts w a : ZMod (n+1))) := by
  rw [tensorPhase, prod_wordCounts (fun a => ZMod.stdAddChar (θ a)) w]
  simp_rw [phase_sum_prod, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
  simp_rw [mul_comm]

lemma phase_pair_sum (n : ℕ) (w v : Fin n → A) :
    (∑ θ : A → ZMod (n+1), tensorPhase n θ w * star (tensorPhase n θ v)) =
      if wordCounts w = wordCounts v then ((n+1 : ℕ) : ℂ)^Fintype.card A else 0 := by
  simp_rw [tensorPhase_counts, phase_star, ← AddChar.map_add_eq_mul, ← sub_eq_add_neg,
    ← Finset.sum_sub_distrib, ← mul_sub]
  rw [phase_sum]
  congr 1
  apply propext
  constructor
  · intro h
    apply Finsupp.ext
    intro a
    have h' := congrFun h a
    dsimp at h'
    have hh := congrArg ZMod.val (sub_eq_zero.mp h')
    simpa only [ZMod.val_natCast_of_lt (Nat.lt_succ_of_le (wordCounts_le n w a)),
      ZMod.val_natCast_of_lt (Nat.lt_succ_of_le (wordCounts_le n v a))] using hh
  · intro h
    simp only [h, sub_self, Pi.zero_def]

end BinaryCoordinateSweeps.Density

end

open scoped BigOperators Classical ComplexOrder
open Matrix

namespace BinaryCoordinateSweeps.Density

variable {I T : Type*} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]

omit [DecidableEq I] in
lemma rankOne_psd (v : I → ℂ) : (rankOne v).PosSemidef := by
  let A : Matrix I Unit ℂ := fun i _ => v i
  have hA : rankOne v = A * Aᴴ := by
    ext i j
    change v i * star (v j) = ∑ _ : Unit, v i * star (v j)
    simp
  rw [hA]
  exact posSemidef_self_mul_conjTranspose A

omit [Fintype I] [DecidableEq I] [Fintype T] in
lemma typeOnes_apply (f : I → T) (t : T) (i j : I) :
    typeOnes f t i j = if f i = t ∧ f j = t then 1 else 0 := by
  simp only [typeOnes, rankOne, vecMulVec, typeVector, Pi.star_apply]
  by_cases hi : f i = t <;> by_cases hj : f j = t <;> simp [hi, hj]

omit [DecidableEq I] [Fintype T] in
lemma typeOnes_psd (f : I → T) (t : T) : (typeOnes f t).PosSemidef := rankOne_psd _

omit [Fintype I] [DecidableEq I] in
lemma sum_typeOnes (f : I → T) (c : T → ℝ) (i j : I) :
    (∑ t, (c t : ℂ) • typeOnes f t : Matrix I I ℂ) i j = if f i = f j then (c (f i) : ℂ) else 0 := by
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, typeOnes_apply]
  rw [Finset.sum_eq_single (f i)]
  · by_cases h : f i = f j <;> simp [h, eq_comm]
  · intro b hb hba
    simp [Ne.symm hba]
  · simp

omit [DecidableEq I] in
lemma typeKernel_psd (f : I → T) (c : T → ℝ) (hc : ∀ t, 0 ≤ c t) :
    Matrix.PosSemidef (fun i j => if f i = f j then (c (f i) : ℂ) else 0 : Matrix I I ℂ) := by
  have hh : (fun i j => if f i = f j then (c (f i) : ℂ) else 0 : Matrix I I ℂ) =
      ∑ t, (c t : ℂ) • typeOnes f t := by ext i j; exact (sum_typeOnes f c i j).symm
  rw [hh]
  exact Matrix.posSemidef_sum _ (fun t _ => (typeOnes_psd f t).smul (by exact_mod_cast hc t))

omit [DecidableEq I] in
lemma typeKernel_mono (f : I → T) (c d : T → ℝ) (h : ∀ t, c t ≤ d t) :
    Matrix.PosSemidef ((fun i j => if f i = f j then (d (f i) : ℂ) else 0) -
      (fun i j => if f i = f j then (c (f i) : ℂ) else 0) : Matrix I I ℂ) := by
  have hkernel :
      ((fun i j => if f i = f j then (d (f i) : ℂ) else 0) -
        (fun i j => if f i = f j then (c (f i) : ℂ) else 0) : Matrix I I ℂ) =
      (fun i j => if f i = f j then ((d (f i) - c (f i) : ℝ) : ℂ) else 0) := by
    ext i j
    by_cases hh : f i = f j <;> simp [hh]
  rw [hkernel]
  exact typeKernel_psd f (fun t => d t - c t) (fun t => sub_nonneg.mpr (h t))

variable {A : Type*} [Fintype A] [DecidableEq A]

lemma wordType_eq_iff (n : ℕ) (w v : Fin n → A) :
    wordType n w = wordType n v ↔ wordCounts w = wordCounts v := by
  simp only [wordType, Subtype.ext_iff, funext_iff, Finsupp.ext_iff]

lemma wordType_total (n : ℕ) (c : WordType A n) : ∑ a, c.val a = n :=
  (Finset.mem_piAntidiag.mp c.property).1

lemma card_wordType (n : ℕ) (c : WordType A n) :
    Fintype.card {w : Fin n → A // wordType n w = c} = Nat.multinomial Finset.univ c.val := by
  have he : {w : Fin n → A // wordType n w = c} ≃
      {w : Fin n → A // ∀ a, wordCounts w a = c.val a} :=
    Equiv.subtypeEquivRight (fun w => by simp only [wordType, Subtype.ext_iff, funext_iff])
  rw [Fintype.card_congr he, card_words_counts_fun n c.val (wordType_total n c)]

lemma symmetricProjector_psd (n : ℕ) : (symmetricProjector (A := A) n).PosSemidef := by
  unfold symmetricProjector
  simpa only [Complex.ofReal_inv] using typeKernel_psd (wordType (A := A) n)
    (fun c => (Nat.multinomial Finset.univ c.val : ℝ)⁻¹)
    (fun _ => inv_nonneg.mpr (Nat.cast_nonneg _))

end BinaryCoordinateSweeps.Density

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_TensorBounds_EmpiricalTensor
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical ComplexOrder
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {A : Type*} [Fintype A] [DecidableEq A]

omit [Fintype A] [DecidableEq A] in
lemma tensorProductVector_phased (n : ℕ) (r : A → ℝ) (θ : A → ZMod (n+1)) (w : Fin n → A) :
    tensorProductVector n (phasedVector n r θ) w =
      (tensorAmplitude n r w : ℂ) * tensorPhase n θ w := by
  simp only [tensorProductVector, phasedVector, tensorAmplitude, tensorPhase,
    Finset.prod_mul_distrib, Complex.ofReal_prod]

lemma tensorAmplitude_counts (n : ℕ) (r : A → ℝ) (w : Fin n → A) :
    tensorAmplitude n r w = ∏ a, Real.sqrt (r a)^wordCounts w a :=
  prod_wordCounts (fun a => Real.sqrt (r a)) w

lemma tensorAmplitude_sq (n : ℕ) (r : A → ℝ) (hr : ∀ a, 0 ≤ r a) (w : Fin n → A) :
    tensorAmplitude n r w * tensorAmplitude n r w = ∏ a, (r a)^wordCounts w a := by
  rw [tensorAmplitude_counts, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro a ha
  rw [← mul_pow, Real.mul_self_sqrt (hr a)]

lemma phaseAverage_apply (n : ℕ) (r : A → ℝ) (hr : ∀ a, 0 ≤ r a)
    (w v : Fin n → A) :
    phaseAverage n r w v = if wordCounts w = wordCounts v then
      ((∏ a, r a^wordCounts w a : ℝ) : ℂ) else 0 := by
  simp only [phaseAverage, Matrix.smul_apply, Matrix.sum_apply, rankOne, vecMulVec,
    Matrix.of_apply, Pi.star_apply, tensorProductVector_phased, star_mul, Complex.star_def,
    Complex.conj_ofReal]
  have hfactor : (∑ θ : A → ZMod (n+1),
        ((tensorAmplitude n r w : ℂ) * tensorPhase n θ w) *
          (star (tensorPhase n θ v) * (tensorAmplitude n r v : ℂ))) =
      ((tensorAmplitude n r w : ℂ) * (tensorAmplitude n r v : ℂ)) *
        ∑ θ : A → ZMod (n+1), tensorPhase n θ w * star (tensorPhase n θ v) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro θ hθ
    ring
  change (((n+1 : ℕ) : ℂ)^Fintype.card A)⁻¹ * _ = _
  simp only [Complex.star_def] at hfactor
  rw [hfactor]
  change _ * (_ * ∑ θ : A → ZMod (n+1), tensorPhase n θ w * star (tensorPhase n θ v)) = _
  rw [phase_pair_sum]
  by_cases h : wordCounts w = wordCounts v
  · rw [ite_eq_left h, ite_eq_left h]
    have ha : tensorAmplitude n r w = tensorAmplitude n r v := by
      simp only [tensorAmplitude_counts, h]
    rw [← ha, ← Complex.ofReal_mul, tensorAmplitude_sq n r hr w]
    have hp : (((n+1 : ℕ) : ℂ)^Fintype.card A) ≠ 0 := pow_ne_zero _ (by exact_mod_cast Nat.succ_ne_zero n)
    field_simp
  · simp [h]

omit [Fintype A] [DecidableEq A] in
lemma phasedVector_norm (n : ℕ) (r : A → ℝ) (hr : ∀ a, 0 ≤ r a)
    (θ : A → ZMod (n+1)) (a : A) :
    phasedVector n r θ a * star (phasedVector n r θ a) = (r a : ℂ) := by
  have he : ZMod.stdAddChar (θ a) * star (ZMod.stdAddChar (θ a)) = 1 := by
    rw [phase_star, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  simp only [phasedVector, star_mul, Complex.star_def, Complex.conj_ofReal]
  calc
    _ = ((Real.sqrt (r a) : ℂ) * Real.sqrt (r a)) *
        (ZMod.stdAddChar (θ a) * star (ZMod.stdAddChar (θ a))) := by simp only [Complex.star_def]; ring
    _ = _ := by rw [he, mul_one, ← Complex.ofReal_mul, Real.mul_self_sqrt (hr a)]

omit [DecidableEq A] in
lemma phasedVector_trace (n : ℕ) (r : A → ℝ) (hr : ∀ a, 0 ≤ r a)
    (hs : ∑ a, r a = 1) (θ : A → ZMod (n+1)) :
    Matrix.trace (rankOne (phasedVector n r θ)) = 1 := by
  simp only [Matrix.trace, Matrix.diag, rankOne, vecMulVec, Matrix.of_apply, Pi.star_apply,
    phasedVector_norm n r hr, ← Complex.ofReal_sum, hs, Complex.ofReal_one]

end BinaryCoordinateSweeps.Density

end

open scoped BigOperators Classical ComplexOrder
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {A : Type*} [Fintype A] [DecidableEq A]

lemma empirical_nonneg (n : ℕ) (c : WordType A n) (a : A) : 0 ≤ empirical n c a :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma empirical_sum (n : ℕ) (hn : 0 < n) (c : WordType A n) : ∑ a, empirical n c a = 1 := by
  simp only [empirical, ← Finset.sum_div, ← Nat.cast_sum, wordType_total,
    div_self (by exact_mod_cast Nat.ne_of_gt hn : (n : ℝ) ≠ 0)]

lemma type_mass_inv (n : ℕ) (hn : 0 < n) (c : WordType A n) :
    (Nat.multinomial Finset.univ c.val : ℝ)⁻¹ ≤
      ((n+1 : ℕ) : ℝ)^Fintype.card A * ∏ a, empirical n c a ^ c.val a := by
  have hm : 0 < (Nat.multinomial Finset.univ c.val : ℝ) := by exact_mod_cast Nat.multinomial_pos _ _
  rw [inv_eq_one_div]
  apply (div_le_iff₀ hm).mpr
  have hh := type_mass_lower n hn c.val (wordType_total n c)
  simpa only [empirical, mul_assoc, mul_left_comm, mul_comm] using hh

theorem finite_postselection (n : ℕ) (hn : 0 < n) :
    ((((n+1 : ℕ) : ℂ)^Fintype.card A) •
      (∑ c : WordType A n, phaseAverage n (empirical n c)) - symmetricProjector n).PosSemidef := by
  let d : WordType A n → ℝ := fun t => ((n+1 : ℕ) : ℝ)^Fintype.card A *
    ∑ c : WordType A n, ∏ a, empirical n c a ^ t.val a
  have hd (t : WordType A n) : (Nat.multinomial Finset.univ t.val : ℝ)⁻¹ ≤ d t := by
    refine (type_mass_inv n hn t).trans ?_
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Nat.cast_nonneg _) _)
    exact Finset.single_le_sum (f := fun c : WordType A n => ∏ a, empirical n c a ^ t.val a)
      (fun c _ => Finset.prod_nonneg
        (fun a _ => pow_nonneg (empirical_nonneg n c a) _)) (Finset.mem_univ t)
  convert typeKernel_mono (wordType (A := A) n)
    (fun t => (Nat.multinomial Finset.univ t.val : ℝ)⁻¹) d hd using 1
  apply Iff.of_eq
  congr 1
  ext w v
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.sum_apply,
    phaseAverage_apply n _ (empirical_nonneg n _), symmetricProjector, smul_eq_mul,
    wordType_eq_iff, Pi.sub_apply]
  split_ifs with h
  · simp only [d, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_natCast,
      Complex.ofReal_sum, Complex.ofReal_inv]
    rfl
  · simp

end BinaryCoordinateSweeps.Density

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_MatrixBounds_SymmetricDensity
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical ComplexOrder
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma psd_trace_domination {B : Matrix I I ℂ} (hB : B.PosSemidef) :
    (B.trace • (1 : Matrix I I ℂ) - B).PosSemidef := by
  let U : unitaryGroup I ℂ := hB.1.eigenvectorUnitary
  let e : I → ℝ := hB.1.eigenvalues
  have he (i) : 0 ≤ e i := hB.eigenvalues_nonneg i
  have htr : B.trace = ∑ j, (e j : ℂ) := hB.1.trace_eq_sum_eigenvalues
  have hs : B = (U : Matrix I I ℂ) * Matrix.diagonal (fun i => (e i : ℂ)) *
      star (U : Matrix I I ℂ) := hB.1.spectral_theorem
  let d : I → ℂ := fun i => B.trace - (e i : ℂ)
  have hd : ∀ i, 0 ≤ d i := by
    intro i
    have hh := Finset.single_le_sum (fun j _ => he j) (Finset.mem_univ i)
    have hc : (e i : ℂ) ≤ ∑ j, (e j : ℂ) := by exact_mod_cast hh
    dsimp only [d]
    rw [htr]
    exact sub_nonneg.mpr hc
  have hp := (Matrix.PosSemidef.diagonal hd).mul_mul_conjTranspose_same (U : Matrix I I ℂ)
  have hdiag : Matrix.diagonal d = B.trace • (1 : Matrix I I ℂ) -
      Matrix.diagonal (fun i => (e i : ℂ)) := by
    ext i j
    by_cases hij : i = j <;> simp [hij, d]
  have hmain : (U : Matrix I I ℂ) * Matrix.diagonal d * star (U : Matrix I I ℂ) =
      B.trace • 1 - B := by
    rw [hdiag, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, ← Unitary.coe_star, Unitary.coe_mul_star_self, Unitary.coe_star, ← hs]
  exact hmain ▸ hp

omit [DecidableEq I] in
lemma rankOne_conjugate {J : Type*} [Fintype J] [DecidableEq J] (P : Matrix J I ℂ) (v : I → ℂ) :
    P * rankOne v * P.conjTranspose = rankOne (P.mulVec v) := by
  simp only [rankOne, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_conjTranspose,
    star_star]

lemma rankOne_projection_bound (P : Matrix I I ℂ) (hP : P.IsHermitian)
    (hPP : P * P = P) (v : I → ℂ) (hv : P.mulVec v = v) :
    ((rankOne v).trace • P - rankOne v).PosSemidef := by
  have hh := (psd_trace_domination (rankOne_psd v)).mul_mul_conjTranspose_same P
  have he : P * ((rankOne v).trace • (1 : Matrix I I ℂ) - rankOne v) * P.conjTranspose =
      (rankOne v).trace • P - rankOne v := by
    rw [Matrix.mul_sub, Matrix.sub_mul, rankOne_conjugate, hv,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hP.eq, hPP]
  exact he ▸ hh

variable {A : Type*} [Fintype A] [DecidableEq A]

lemma symmetricProjector_identity (n : ℕ) (x : (Fin n → A) → ℂ)
    (hx : ∀ w v, wordCounts w = wordCounts v → x w = x v) :
    (symmetricProjector n).mulVec x = x := by
  funext w
  change (∑ v, (if wordType n w = wordType n v then
    ((Nat.multinomial Finset.univ (wordType n w).val : ℝ)⁻¹ : ℂ) else 0) * x v) = x w
  have he (v) : (if wordType n w = wordType n v then
      ((Nat.multinomial Finset.univ (wordType n w).val : ℝ)⁻¹ : ℂ) else 0) * x v =
      if wordType n v = wordType n w then
        ((Nat.multinomial Finset.univ (wordType n w).val : ℝ)⁻¹ : ℂ) * x w else 0 := by
    by_cases h : wordType n w = wordType n v
    · rw [ite_eq_left h, ite_eq_left h.symm, hx w v ((wordType_eq_iff n w v).mp h)]
    · simp [h, Ne.symm h]
  simp_rw [he]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hc : (Finset.univ.filter (fun v : Fin n → A => wordType n v = wordType n w)).card =
      Nat.multinomial Finset.univ (wordType n w).val := by
    rw [← Fintype.card_subtype, card_wordType]
  rw [hc]
  have hn : (Nat.multinomial Finset.univ (wordType n w).val : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.multinomial_pos Finset.univ (wordType n w).val))
  push_cast
  field_simp

lemma symmetricProjector_idempotent (n : ℕ) :
    symmetricProjector (A := A) n * symmetricProjector n = symmetricProjector n := by
  ext w v
  have h := symmetricProjector_identity n (fun u => symmetricProjector n u v) (by
    intro u t hut
    simp only [symmetricProjector, wordType_eq_iff, hut]
    have ht : wordType n u = wordType n t := (wordType_eq_iff n u t).mpr hut
    rw [ht])
  exact congrFun h w

lemma symmetric_rankOne_bound (n : ℕ) (v : (Fin n → A) → ℂ)
    (hv : ∀ w u, wordCounts w = wordCounts u → v w = v u) :
    ((rankOne v).trace • symmetricProjector n - rankOne v).PosSemidef :=
  rankOne_projection_bound _ (symmetricProjector_psd n).1
    (symmetricProjector_idempotent n) _ (symmetricProjector_identity n v hv)

theorem symmetric_vector_postselection (n : ℕ) (hn : 0 < n) (v : (Fin n → A) → ℂ)
    (hv : ∀ w u, wordCounts w = wordCounts u → v w = v u) :
    (((rankOne v).trace * ((n+1 : ℕ) : ℂ)^Fintype.card A) •
      (∑ c : WordType A n, phaseAverage n (empirical n c)) - rankOne v).PosSemidef := by
  have hh := (finite_postselection (A := A) n hn).smul (rankOne_psd v).trace_nonneg
  have hr := symmetric_rankOne_bound n v hv
  have he : ((rankOne v).trace * ((n+1 : ℕ) : ℂ)^Fintype.card A) •
      (∑ c : WordType A n, phaseAverage n (empirical n c)) - rankOne v =
      (rankOne v).trace • ((((n+1 : ℕ) : ℂ)^Fintype.card A) •
      (∑ c : WordType A n, phaseAverage n (empirical n c)) - symmetricProjector n) +
      ((rankOne v).trace • symmetricProjector n - rankOne v) := by
    simp only [smul_sub, smul_smul]
    abel
  rw [he]
  exact hh.add hr

end BinaryCoordinateSweeps.Density

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_TensorBounds_TensorReduction
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical ComplexOrder
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {K A B : Type*} [Fintype K] [DecidableEq K] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]

omit [DecidableEq K] in
lemma densityChannel_psd (e : K → A × B) {M : Matrix K K ℂ} (hM : M.PosSemidef) :
    (densityChannel e M).PosSemidef :=
  Matrix.posSemidef_sum _ (fun _ _ => hM.mul_mul_conjTranspose_same _)

omit [DecidableEq K] [Fintype A] in
lemma densityChannel_sub (e : K → A × B) (M N : Matrix K K ℂ) :
    densityChannel e (M-N) = densityChannel e M - densityChannel e N := by
  simp only [densityChannel, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]

omit [DecidableEq K] [Fintype A] in
lemma densityChannel_smul (e : K → A × B) (c : ℂ) (M : Matrix K K ℂ) :
    densityChannel e (c • M) = c • densityChannel e M := by
  simp only [densityChannel, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

omit [DecidableEq K] [Fintype A] in
lemma densityChannel_sum {T : Type*} [Fintype T] (e : K → A × B) (M : T → Matrix K K ℂ) :
    densityChannel e (∑ t, M t) = ∑ t, densityChannel e (M t) := by
  simp only [densityChannel, Matrix.mul_sum, Matrix.sum_mul]
  exact Finset.sum_comm

omit [DecidableEq K] [Fintype A] [Fintype B] in
lemma kraus_mulVec (e : K → A × B) (v : K → ℂ) (b : B) :
    (kraus e b).mulVec v = fun a => reshape e v a b := by
  ext a
  simp only [Matrix.mulVec, dotProduct, kraus, reshape, ite_mul, one_mul, zero_mul]

omit [DecidableEq K] in
lemma densityChannel_rankOne (e : K → A × B) (v : K → ℂ) :
    densityChannel e (rankOne v) = reshape e v * (reshape e v).conjTranspose := by
  simp only [densityChannel, rankOne_conjugate, kraus_mulVec]
  ext a b
  simp only [Matrix.sum_apply, rankOne, vecMulVec_apply, Pi.star_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply]

omit [Fintype A] [Fintype B] in
lemma reshape_injective_apply (e : K → A × B) (he : Function.Injective e) (v : K → ℂ) (k : K) :
    reshape e v (e k).1 (e k).2 = v k := by
  simp only [reshape, Prod.mk.eta, he.eq_iff, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

omit [DecidableEq K] [Fintype A] [Fintype B] in
lemma reshape_outside (e : K → A × B) (v : K → ℂ) (a : A) (b : B)
    (h : (a,b) ∉ Set.range e) : reshape e v a b = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  exact ite_eq_right (fun hh => h ⟨k,hh⟩)

omit [Fintype K] [DecidableEq K] [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] in
lemma wordPair_eq_iff (n : ℕ) (e : K → A × B) (w : Fin n → K)
    (x : Fin n → A) (y : Fin n → B) : wordPair n e w = (x,y) ↔ ∀ i, e (w i) = (x i,y i) := by
  simp only [wordPair, funext_iff, Prod.ext_iff]
  exact ⟨fun h i => ⟨h.1 i,h.2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩

omit [Fintype K] [DecidableEq K] [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] in
lemma wordPair_injective (n : ℕ) (e : K → A × B) (he : Function.Injective e) :
    Function.Injective (wordPair n e) := by
  intro w v h
  funext i
  apply he
  exact Prod.ext (congrFun (congrArg Prod.fst h) i) (congrFun (congrArg Prod.snd h) i)

omit [DecidableEq K] [Fintype A] [Fintype B] in
lemma reshape_tensor (n : ℕ) (e : K → A × B) (u : K → ℂ)
    (x : Fin n → A) (y : Fin n → B) :
    reshape (wordPair n e) (tensorProductVector n u) x y = ∏ i, reshape e u (x i) (y i) := by
  simp only [reshape, tensorProductVector, wordPair_eq_iff]
  rw [Fintype.prod_sum (fun i k => if e k = (x i,y i) then u k else 0)]
  apply Finset.sum_congr rfl
  intro w hw
  by_cases h : ∀ i, e (w i) = (x i,y i)
  · simp only [ite_eq_left h]
    apply Finset.prod_congr rfl
    intro i hi
    rw [ite_eq_left (h i)]
  · rw [ite_eq_right h]
    obtain ⟨i,hi⟩ := not_forall.mp h
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)).symm

omit [Fintype A] [DecidableEq A] [DecidableEq B] in
lemma tensor_gram (n : ℕ) (U : Matrix A B ℂ) :
    matrixTensorRect n U * (matrixTensorRect n U).conjTranspose =
    matrixTensorPower n (U * U.conjTranspose) := by
  ext x z
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, matrixTensorPower, matrixTensorRect, star_prod,
    ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i b => U (x i) b * star (U (z i) b))).symm

omit [DecidableEq K] in
lemma densityChannel_tensorRankOne (n : ℕ) (e : K → A × B) (u : K → ℂ) :
    densityChannel (wordPair n e) (rankOne (tensorProductVector n u)) =
      matrixTensorPower n (reshape e u * (reshape e u).conjTranspose) := by
  rw [densityChannel_rankOne]
  have he : reshape (wordPair n e) (tensorProductVector n u) =
      matrixTensorRect n (reshape e u) := by
    ext x y
    exact reshape_tensor n e u x y
  rw [he, tensor_gram]

end BinaryCoordinateSweeps.Density

end

open scoped BigOperators Classical ComplexOrder
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {K A B : Type*} [Fintype K] [DecidableEq K] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]

lemma reshape_trace (e : K → A × B) (he : Function.Injective e) (v : K → ℂ) :
    (reshape e v * (reshape e v).conjTranspose).trace = (rankOne v).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    rankOne, Matrix.vecMulVec_apply, Pi.star_apply]
  symm
  calc
    _ = ∑ x : A × B, reshape e v x.1 x.2 * star (reshape e v x.1 x.2) :=
      Fintype.sum_of_injective e he (fun k => v k * star (v k))
        (fun x : A × B => reshape e v x.1 x.2 * star (reshape e v x.1 x.2))
        (by rintro ⟨a,b⟩ h; rw [reshape_outside e v a b h]; simp)
        (by intro k; rw [reshape_injective_apply e he])
    _ = _ := Fintype.sum_prod_type _

omit [DecidableEq A] in
lemma gram_psd (U : Matrix A B ℂ) : (U * U.conjTranspose).PosSemidef := by
  simpa only [Matrix.mul_one] using
    (Matrix.PosSemidef.one : (1 : Matrix B B ℂ).PosSemidef).mul_mul_conjTranspose_same U

omit [DecidableEq K] [Fintype A] in
lemma reshape_even {P : Type*} (pa : A → P) (pb : B → P) (e : K → A × B)
    (he : ∀ k, pa (e k).1 = pb (e k).2) (v : K → ℂ) (a a' : A)
    (haa : pa a ≠ pa a') : (reshape e v * (reshape e v).conjTranspose) a a' = 0 := by
  apply Finset.sum_eq_zero
  intro b hb
  change reshape e v a b * star (reshape e v a' b) = 0
  by_cases ha : pa a = pb b
  · have hn : (a', b) ∉ Set.range e := by
      rintro ⟨k,hk⟩
      have hh := he k
      rw [hk] at hh
      exact haa (ha.trans hh.symm)
    rw [reshape_outside e v a' b hn, star_zero, mul_zero]
  · have hn : (a,b) ∉ Set.range e := by
      rintro ⟨k,hk⟩
      have hh := he k
      rw [hk] at hh
      exact ha hh
    rw [reshape_outside e v a b hn, zero_mul]

lemma reducedPhaseDensity_psd (n : ℕ) (e : K → A × B) (c : WordType K n)
    (t : K → ZMod (n+1)) : (reducedPhaseDensity n e c t).PosSemidef := gram_psd _

lemma reducedPhaseDensity_trace (n : ℕ) (hn : 0 < n) (e : K → A × B)
    (he : Function.Injective e) (c : WordType K n) (t : K → ZMod (n+1)) :
    (reducedPhaseDensity n e c t).trace = 1 := by
  rw [reducedPhaseDensity, reshape_trace e he]
  exact phasedVector_trace n (empirical n c) (empirical_nonneg n c) (empirical_sum n hn c) t

omit [Fintype A] in
lemma reducedPhaseDensity_even {P : Type*} (n : ℕ) (pa : A → P) (pb : B → P)
    (e : K → A × B) (he : ∀ k, pa (e k).1 = pb (e k).2)
    (c : WordType K n) (t : K → ZMod (n+1)) (a a' : A) (haa : pa a ≠ pa a') :
    reducedPhaseDensity n e c t a a' = 0 := reshape_even pa pb e he _ a a' haa

end BinaryCoordinateSweeps.Density

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungHilbert
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Classical
open Equiv Equiv.Perm Finset

namespace BinaryCoordinateSweeps.Signed
variable {n : ℕ}

lemma adjacent_swap_inversion (a b i j : Fin n) (hab : a.val + 1 = b.val) (hij : j < i) :
    Equiv.swap a b i ≤ Equiv.swap a b j ↔ i = b ∧ j = a := by
  have hn : a ≠ b := by intro h; subst b; omega
  simp only [Equiv.swap_apply_def]
  split_ifs <;> simp_all only [Fin.le_def, Fin.lt_def, Fin.ext_iff, and_true, and_false, iff_true, iff_false] <;> omega

lemma koszulSign_swap_adjacent (β : Fin n → Bool) (a b : Fin n) (hab : a.val+1=b.val) :
    koszulSign β (Equiv.swap a b) = if β a = true ∧ β b = true then -1 else 1 := by
  unfold koszulSign
  rw [Finset.prod_eq_single (⟨b,a⟩ : Σ _ : Fin n, Fin n)]
  · simp only [swap_apply_right, swap_apply_left]
    rw [ite_eq_left (show a ≤ b by omega)]
    simp only [and_comm]
  · rintro ⟨i,j⟩ hij hne
    have hi : ¬ Equiv.swap a b i ≤ Equiv.swap a b j := by
      rw [adjacent_swap_inversion a b i j hab (mem_finPairsLT.mp hij)]
      rintro ⟨rfl,rfl⟩; exact hne rfl
    simp [hi]
  · intro h
    exact False.elim (h (mem_finPairsLT.mpr (show a < b by omega)))

lemma mask_swap (β : Fin n → Bool) (a b : Fin n) (h : β a = β b) :
    β ∘ Equiv.swap a b = β := by
  funext i
  simp only [Function.comp_apply, Equiv.swap_apply_def]
  split_ifs <;> simp_all

lemma koszulSign_conjugate (β : Fin n → Bool) (g f : Equiv.Perm (Fin n))
    (hf : β ∘ f.symm = β) :
    koszulSign (β ∘ g.symm) (g*f*g⁻¹) = koszulSign β f := by
  have hc : (g*f*g⁻¹)*g = g*f := by group
  have h := congrArg (koszulSign β) hc
  rw [koszulSign_mul β (g*f*g⁻¹) g, koszulSign_mul β g f, hf] at h
  have he : koszulSign β g * koszulSign β f = koszulSign β f * koszulSign β g := mul_comm _ _
  rw [he] at h
  exact mul_right_cancel h

lemma exists_perm_pair (a b c d : Fin n) (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ g : Equiv.Perm (Fin n), g a = c ∧ g b = d := by
  let h := Equiv.swap a c
  have hh : h b ≠ c := by
    intro hbc
    have ha : h a = c := by simp [h]
    exact hab (h.injective (ha.trans hbc.symm))
  refine ⟨Equiv.swap (h b) d * h, ?_, ?_⟩
  · change Equiv.swap (h b) d (h a) = c
    rw [show h a = c by simp [h]]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hh) hcd
  · simp

lemma koszulSign_swap (β : Fin n → Bool) (a b : Fin n) (hab : a ≠ b)
    (hβ : β a = β b) :
    koszulSign β (Equiv.swap a b) = if β a = true then -1 else 1 := by
  have hn : 2 ≤ n := by
    by_contra h
    have ha := a.isLt
    have hb := b.isLt
    apply hab
    apply Fin.ext
    omega
  let c : Fin n := ⟨0, by omega⟩
  let d : Fin n := ⟨1, by omega⟩
  have hcd : c ≠ d := by intro hh; have := congrArg Fin.val hh; dsimp [c,d] at this; omega
  obtain ⟨g,hga,hgb⟩ := exists_perm_pair a b c d hab hcd
  have hc := koszulSign_conjugate β g (Equiv.swap a b) (by simpa using mask_swap β a b hβ)
  have hconj : g * Equiv.swap a b * g⁻¹ = Equiv.swap c d := by
    have ht := Equiv.symm_trans_swap_trans a b g
    change g * Equiv.swap a b * g⁻¹ = Equiv.swap (g a) (g b) at ht
    simpa only [hga,hgb] using ht
  rw [hconj, koszulSign_swap_adjacent _ c d (by rfl)] at hc
  have hgca : g.symm c = a := by rw [← hga]; simp
  have hgdb : g.symm d = b := by rw [← hgb]; simp
  simpa only [Function.comp_apply, hgca, hgdb, ← hβ, and_self] using hc.symm

end BinaryCoordinateSweeps.Signed

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_TensorBounds_EvenPostselection
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical ComplexOrder MatrixOrder
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {K A B : Type*} [Fintype K] [DecidableEq K] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]

lemma reduced_postselection (n : ℕ) (hn : 0 < n) (e : K → A × B)
    (v : (Fin n → K) → ℂ)
    (hv : ∀ w u, wordCounts w = wordCounts u → v w = v u) :
    ((rankOne v).trace • (∑ c : WordType K n, ∑ t : K → ZMod (n+1),
      matrixTensorPower n (reducedPhaseDensity n e c t)) -
      reshape (wordPair n e) v * (reshape (wordPair n e) v).conjTranspose).PosSemidef := by
  have h := densityChannel_psd (wordPair n e) (symmetric_vector_postselection n hn v hv)
  rw [densityChannel_sub, densityChannel_smul, densityChannel_sum] at h
  simp only [phaseAverage, densityChannel_smul, densityChannel_sum,
    densityChannel_tensorRankOne, ← Finset.smul_sum, smul_smul] at h
  have hd : (((n+1 : ℕ) : ℂ)^Fintype.card K) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast Nat.succ_ne_zero n)
  rw [mul_assoc, mul_inv_cancel₀ hd, mul_one, densityChannel_rankOne] at h
  exact h

variable {P : Type*} [DecidableEq P]

omit [Fintype A] [DecidableEq A] [DecidableEq P] in
lemma matchedEmbedding_injective (p : A → P) : Function.Injective (matchedEmbedding p) :=
  Subtype.val_injective

lemma reshape_pairVector (n : ℕ) (p : A → P) (Q : Matrix (Fin n → A) (Fin n → A) ℂ)
    (hQ : ∀ x y, (fun i => p (x i)) ≠ (fun i => p (y i)) → Q x y = 0) :
    reshape (wordPair n (matchedEmbedding p)) (pairVector n p Q) = Q := by
  ext x y
  by_cases h : (fun i => p (x i)) = (fun i => p (y i))
  · let w : Fin n → MatchedPair p := fun i => ⟨(x i,y i), congrFun h i⟩
    have hw : wordPair n (matchedEmbedding p) w = (x,y) := rfl
    have ht := reshape_injective_apply (wordPair n (matchedEmbedding p))
      (wordPair_injective n _ (matchedEmbedding_injective p)) (pairVector n p Q) w
    rw [hw] at ht
    exact ht
  · have hn : (x,y) ∉ Set.range (wordPair n (matchedEmbedding p)) := by
      rintro ⟨w,hw⟩
      apply h
      funext i
      have hi := (wordPair_eq_iff n _ w x y).mp hw i
      have hh := (w i).property
      change p (matchedEmbedding p (w i)).1 = p (matchedEmbedding p (w i)).2 at hh
      rw [hi] at hh
      exact hh
    rw [reshape_outside _ _ x y hn, hQ x y h]

omit [Fintype A] [DecidableEq P] in
lemma pairVector_symmetric (n : ℕ) (p : A → P) (Q : Matrix (Fin n → A) (Fin n → A) ℂ)
    (hQ : ∀ (g : Equiv.Perm (Fin n)) x y, Q (x ∘ g) (y ∘ g) = Q x y) :
    ∀ w u, wordCounts w = wordCounts u → pairVector n p Q w = pairVector n p Q u := by
  intro w u h
  obtain ⟨g,hg⟩ := exists_perm_eq_of_wordCounts h
  have hw : w = u ∘ g := (funext hg).symm
  rw [hw]
  simpa only [pairVector, Function.comp_def] using
    hQ g (fun i => (u i).val.1) (fun i => (u i).val.2)

theorem even_block_postselection (n : ℕ) (hn : 0 < n) (p : A → P)
    (Q : Matrix (Fin n → A) (Fin n → A) ℂ) (hQ : Q.PosSemidef)
    (hblock : ∀ x y, (p ∘ x) ≠ (p ∘ y) → Q x y = 0)
    (hperm : ∀ (g : Equiv.Perm (Fin n)) x y, Q (x ∘ g) (y ∘ g) = Q x y) :
    (Q.trace • (∑ c : WordType (MatchedPair p) n, ∑ t : MatchedPair p → ZMod (n+1),
      matrixTensorPower n (reducedPhaseDensity n (matchedEmbedding p) c t)) - Q).PosSemidef := by
  let S := CFC.sqrt Q
  have hSblock : ∀ x y, (p ∘ x) ≠ (p ∘ y) → S x y = 0 :=
    sqrt_block_diagonal (fun x => p ∘ x) Q hblock
  have hSperm (g : Equiv.Perm (Fin n)) (x y) : S (x ∘ g) (y ∘ g) = S x y := by
    have hh := sqrt_submatrix_invariant Q hQ (wordPerm n g) (by
      ext u v; exact hperm g u v)
    exact congrFun (congrFun hh x) y
  let v := pairVector n p S
  have hr : reshape (wordPair n (matchedEmbedding p)) v = S :=
    reshape_pairVector n p S hSblock
  have ht : (rankOne v).trace = Q.trace := by
    rw [← reshape_trace (wordPair n (matchedEmbedding p))
      (wordPair_injective n _ (matchedEmbedding_injective p)) v, hr, sqrt_gram Q hQ]
  have hh := reduced_postselection n hn (matchedEmbedding p) v (pairVector_symmetric n p S hSperm)
  rw [ht, hr, sqrt_gram Q hQ] at hh
  exact hh

end BinaryCoordinateSweeps.Density

end

open scoped BigOperators Classical ComplexOrder
open Equiv Equiv.Perm Matrix

namespace BinaryCoordinateSweeps.Signed
variable {A : Type*} {n : ℕ}

lemma signC_swap (β : Fin n → Bool) (a b : Fin n) (hab : a ≠ b) (hβ : β a = β b) :
    signC β (Equiv.swap a b) = if β a = true then -1 else 1 := by
  simp only [signC, koszulSign_swap β a b hab hβ]
  split_ifs <;> norm_num

lemma invariant_same_parity (p : A → Bool) (M : Matrix (Fin n → A) (Fin n → A) ℂ)
    (hM : Invariant p M) (g : Equiv.Perm (Fin n)) (x y : Fin n → A)
    (h : p ∘ x = p ∘ y) : M (x ∘ g) (y ∘ g) = M x y := by
  rw [hM g x y, h, signC_sq, one_mul]

lemma comp_swap_eq {T : Type*} (x : Fin n → T) (i j : Fin n) (h : x i = x j) :
    x ∘ Equiv.swap i j = x := by
  funext k
  simp only [Function.comp_apply, Equiv.swap_apply_def]
  split_ifs <;> simp_all

lemma invariant_repeated_mismatch_zero (p : A → Bool)
    (M : Matrix (Fin n → A) (Fin n → A) ℂ) (hM : Invariant p M)
    (x y : Fin n → A) (i j : Fin n) (hij : i ≠ j)
    (hx : x i = x j) (hy : y i = y j) (hp : p (x i) ≠ p (y i)) : M x y = 0 := by
  have h := hM (Equiv.swap i j) x y
  rw [comp_swap_eq x i j hx, comp_swap_eq y i j hy, Equiv.swap_inv,
    signC_swap _ i j hij (by change p (x i)=p (x j); rw [hx]),
    signC_swap _ i j hij (by change p (y i)=p (y j); rw [hy])] at h
  simp only [Function.comp_apply] at h
  cases hx' : p (x i) <;> cases hy' : p (y i)
  · exact False.elim (hp (hx'.trans hy'.symm))
  · simp only [hx', hy', Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul] at h
    linear_combination (1/2 : ℂ) * h
  · simp only [hx', hy', Bool.false_eq_true, ↓reduceIte, mul_one, neg_one_mul] at h
    linear_combination (1/2 : ℂ) * h
  · exact False.elim (hp (hx'.trans hy'.symm))

variable [Fintype A]

lemma invariant_mismatch_card (p : A → Bool)
    (M : Matrix (Fin n → A) (Fin n → A) ℂ) (hM : Invariant p M)
    (x y : Fin n → A) (hxy : M x y ≠ 0) :
    (Finset.univ.filter (fun i => p (x i) ≠ p (y i))).card ≤ (Fintype.card A)^2 := by
  let T := {i : Fin n // p (x i) ≠ p (y i)}
  let f : T → A × A := fun i => (x i.val,y i.val)
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    by_contra h
    have hx := congrArg Prod.fst hij
    have hy := congrArg Prod.snd hij
    exact hxy (invariant_repeated_mismatch_zero p M hM x y i j h hx hy i.property)
  have hc := Fintype.card_le_of_injective f hf
  simpa only [T, Fintype.card_subtype, Fintype.card_prod, pow_two] using hc

end BinaryCoordinateSweeps.Signed

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_TensorBounds_SignedCommutant
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical
open Equiv Equiv.Perm Matrix

namespace BinaryCoordinateSweeps.Signed
open Density

variable {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ}

lemma typeRepresentative_type (c : RealizedType A n) :
    wordType n (typeRepresentative c) = c.val := c.property.choose_spec

lemma invariantCode_injective (p : A → Bool) (n : ℕ) :
    Function.Injective (invariantCode p n) := by
  intro M N h
  apply Subtype.ext
  ext x y
  let w : Fin n → A × A := fun i => (x i,y i)
  let c : RealizedType A n := ⟨wordType n w, ⟨w,rfl⟩⟩
  have hc : wordCounts w = wordCounts (typeRepresentative c) :=
    (wordType_eq_iff n w _).mp (typeRepresentative_type c).symm
  obtain ⟨g,hg⟩ := exists_perm_eq_of_wordCounts hc
  have hx : (Prod.fst ∘ typeRepresentative c) ∘ g = x := by
    funext i
    exact congrArg Prod.fst (hg i)
  have hy : (Prod.snd ∘ typeRepresentative c) ∘ g = y := by
    funext i
    exact congrArg Prod.snd (hg i)
  have hm := M.property g (Prod.fst ∘ typeRepresentative c) (Prod.snd ∘ typeRepresentative c)
  have hn := N.property g (Prod.fst ∘ typeRepresentative c) (Prod.snd ∘ typeRepresentative c)
  rw [hx,hy] at hm hn
  rw [hm,hn]
  exact congrArg (fun z : ℂ => signC (p ∘ (Prod.fst ∘ typeRepresentative c)) g⁻¹ *
    signC (p ∘ (Prod.snd ∘ typeRepresentative c)) g⁻¹ * z) (congrFun h c)

lemma invariantSubspace_finrank (p : A → Bool) (n : ℕ) :
    Module.finrank ℂ (invariantSubspace p n) ≤ (n+1)^((Fintype.card A)^2) := by
  let : Fintype (RealizedType A n) := Fintype.ofFinite _
  have h := LinearMap.finrank_le_finrank_of_injective (f := invariantCode p n)
    (invariantCode_injective p n)
  rw [Module.finrank_pi] at h
  have hc := Fintype.card_le_of_injective (fun c : RealizedType A n => c.val) Subtype.val_injective
  have ht := card_types_le (A := A × A) n
  simp only [Fintype.card_coe, Fintype.card_prod, ← pow_two] at hc ht
  exact h.trans (hc.trans ht)

lemma commutantToInvariant_injective (p : A → Bool) (n : ℕ) :
    Function.Injective (commutantToInvariant p n) := by
  intro f g h
  apply Representation.IntertwiningMap.toLinearMap_injective
  apply LinearMap.toMatrix'.injective
  exact congrArg Subtype.val h

theorem tensor_commutant_finrank (p : A → Bool) (n : ℕ) :
    Module.finrank ℂ (Representation.IntertwiningMap (tensorRep p n) (tensorRep p n)) ≤
      (n+1)^((Fintype.card A)^2) :=
  (LinearMap.finrank_le_finrank_of_injective (f := commutantToInvariant p n)
    (commutantToInvariant_injective p n)).trans (invariantSubspace_finrank p n)

end BinaryCoordinateSweeps.Signed

end

open scoped BigOperators Classical ComplexOrder
open Equiv Equiv.Perm Matrix

namespace BinaryCoordinateSweeps.Signed
variable {A : Type*} [Fintype A] {n : ℕ}

lemma hilbertSubspace_finrank (S : Submodule ℂ ((Fin n → A) → ℂ)) :
    Module.finrank ℂ (hilbertSubspace S) = Module.finrank ℂ S :=
  (Submodule.equivMapOfInjective (coeffEquiv A n).symm.toLinearMap
    (coeffEquiv A n).symm.injective S).finrank_eq.symm

end BinaryCoordinateSweeps.Signed

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_TensorBounds_TensorProductMatrices
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical ComplexOrder MatrixOrder
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {I A B C : Type*} [Fintype I] [DecidableEq I]
 [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

omit [Fintype A] [DecidableEq A] [DecidableEq B] [Fintype C] [DecidableEq C] in
lemma tensorMatrices_mul (M : I → Matrix A B ℂ) (N : I → Matrix B C ℂ) :
    tensorMatrices M * tensorMatrices N = tensorMatrices (fun i => M i * N i) := by
  ext x z
  simp only [Matrix.mul_apply,tensorMatrices,← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i b => M i (x i) b * N i b (z i))).symm

omit [DecidableEq I] [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] in
lemma tensorMatrices_star (M : I → Matrix A B ℂ) :
    (tensorMatrices M).conjTranspose = tensorMatrices (fun i => (M i).conjTranspose) := by
  ext x y
  simp [tensorMatrices]

omit [DecidableEq I] [Fintype A] in
lemma tensorMatrices_one : tensorMatrices (fun _ : I => (1 : Matrix A A ℂ)) = 1 := by
  ext x y
  by_cases h : x = y
  · subst y; simp [tensorMatrices]
  · have ⟨i,hi⟩ := Function.ne_iff.mp h
    simp only [tensorMatrices,Matrix.one_apply,ite_eq_right h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

omit [DecidableEq A] in
lemma tensorMatrices_trace (M : I → Matrix A A ℂ) :
    (tensorMatrices M).trace = ∏ i, (M i).trace := by
  simp only [Matrix.trace,tensorMatrices,diag]
  exact (Fintype.prod_sum (fun i a => M i a a)).symm

lemma tensorMatrices_psd (M : I → Matrix A A ℂ) (hM : ∀ i, (M i).PosSemidef) :
    (tensorMatrices M).PosSemidef := by
  have hex (i : I) : ∃ X : Matrix A A ℂ, M i = X.conjTranspose * X := by
    exact CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (hM i).nonneg
  choose X hX using hex
  have he : tensorMatrices M = (tensorMatrices X).conjTranspose * tensorMatrices X := by
    rw [tensorMatrices_star,tensorMatrices_mul]
    congr 1
    funext i
    exact hX i
  rw [he]
  exact Matrix.posSemidef_conjTranspose_mul_self _

end BinaryCoordinateSweeps.Density

end

open scoped BigOperators Classical ComplexOrder
open Matrix

namespace BinaryCoordinateSweeps.Signed
open Density

variable {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ}

omit [Fintype A] [DecidableEq A] in
lemma even_tensor_invariant (p : A → Bool) (M : Matrix A A ℂ)
    (hM : ∀ a b, p a ≠ p b → M a b = 0) :
    Invariant p (matrixTensorPower n M) := by
  intro g x y
  have hr : matrixTensorPower n M (x ∘ g) (y ∘ g) = matrixTensorPower n M x y := by
    exact Equiv.prod_comp g (fun i => M (x i) (y i))
  rw [hr]
  by_cases h : p ∘ x = p ∘ y
  · rw [h,signC_sq,one_mul]
  · obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    have hz : matrixTensorPower n M x y = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (hM (x i) (y i) hi)
    simp [hz]

omit [DecidableEq A] in
lemma invariant_mulVec_commutes (p : A → Bool) (M : Matrix (Fin n → A) (Fin n → A) ℂ)
    (hM : Invariant p M) (g : Equiv.Perm (Fin n)) (v : (Fin n → A) → ℂ) :
    M.mulVec (act p g v) = act p g (M.mulVec v) := by
  funext x
  simp only [Matrix.mulVec,dotProduct,act_apply,Finset.mul_sum]
  conv_rhs => rw [← (wordReorder (A:=A) g).sum_comp]
  apply Finset.sum_congr rfl
  intro y _
  have he := hM g x y
  dsimp only [wordReorder,Equiv.coe_fn_mk]
  rw [he]
  linear_combination -(signC (p ∘ y) g⁻¹ * M x y * v (y ∘ g)) * signC_sq (p ∘ x) g⁻¹

end BinaryCoordinateSweeps.Signed

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_MatrixBounds_Whitening
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical ComplexOrder

namespace BinaryCoordinateSweeps.Irrep
open Representation

variable {G V W : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  (ρ : Representation ℂ G V) (σ : Representation ℂ G W)

lemma symmetric_projection_commutes (S : Submodule ℂ W) (A : Module.End ℂ W)
    (hA : A.IsSymmetric) (hS : ∀ w ∈ S, A w ∈ S) (w : W) :
    A (S.starProjection w) = S.starProjection (A w) := by
  symm
  apply S.eq_starProjection_of_mem_of_inner_eq_zero (hS _ (S.starProjection_apply_mem w))
  intro u hu
  rw [← map_sub, hA]
  exact S.starProjection_inner_eq_zero w (A u) (hS u hu)

omit [Fintype G] [FiniteDimensional ℂ V] in
lemma isotypic_norm_cap [ρ.IsIrreducible] (B : Module.End ℂ W)
    (hT : ∀ g w, (B.adjoint * B) (σ g w) = σ g ((B.adjoint * B) w))
    (hσ : ∀ g w, ‖σ g w‖ = ‖w‖)
    (ht : (LinearMap.trace ℂ W (B.adjoint * B)).re = 1)
    {w : W} (hw : w ∈ isotypicSpan ρ σ) :
    (Module.finrank ℂ V : ℝ) * ‖B w‖^2 ≤ ‖w‖^2 := by
  have hp : (B.adjoint * B).IsPositive := LinearMap.isPositive_adjoint_comp_self B
  have hc := (isotypic_restriction_cap ρ σ (B.adjoint*B) hp hT hσ).2 ⟨w,hw⟩
  have hr := hc
  change 0 ≤ (inner ℂ ((↑((LinearMap.trace ℂ W) (B.adjoint*B)).re : ℂ) • w -
    (Module.finrank ℂ V : ℂ) • B.adjoint (B w)) w).re at hr
  rw [ht,Complex.ofReal_one,one_smul,inner_sub_left,inner_smul_left,
    LinearMap.adjoint_inner_left,inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K] at hr
  simp only [← RCLike.ofReal_pow,Complex.sub_re,Complex.mul_re,Complex.natCast_re,
    Complex.natCast_im,map_natCast,zero_mul,sub_zero] at hr
  change 0 ≤ ‖w‖^2 - (Module.finrank ℂ V : ℝ)*‖B w‖^2 at hr
  linarith

omit [Fintype G] [FiniteDimensional ℂ V] in
theorem whitening_norm [ρ.IsIrreducible] (B A : Module.End ℂ W)
    (hA : A.IsSymmetric) (hAc : ∀ g w, A (σ g w) = σ g (A w))
    (hBA : B*A = 1)
    (hT : ∀ g w, (B.adjoint * B) (σ g w) = σ g ((B.adjoint * B) w))
    (hσ : ∀ g w, ‖σ g w‖ = ‖w‖)
    (ht : (LinearMap.trace ℂ W (B.adjoint * B)).re = 1) (w : W) :
    (Module.finrank ℂ V : ℝ) * ‖(isotypicSpan ρ σ).starProjection w‖^2 ≤ ‖A w‖^2 := by
  let S := isotypicSpan ρ σ
  have hi := commuting_isotypic_invariant ρ σ A hAc
  have hb : B (A (S.starProjection w)) = S.starProjection w := by
    exact congrArg (fun T : Module.End ℂ W => T (S.starProjection w)) hBA
  have hn := isotypic_norm_cap ρ σ B hT hσ ht
    (hi _ (S.starProjection_apply_mem w))
  rw [hb,symmetric_projection_commutes S A hA hi] at hn
  exact hn.trans (pow_le_pow_left₀ (norm_nonneg _) (S.norm_starProjection_apply_le (A w)) 2)

omit [Fintype G] [FiniteDimensional ℂ V] in
theorem whitening_positive [ρ.IsIrreducible] (B A : Module.End ℂ W)
    (hA : A.IsSymmetric) (hAc : ∀ g w, A (σ g w) = σ g (A w))
    (hBA : B*A = 1)
    (hT : ∀ g w, (B.adjoint * B) (σ g w) = σ g ((B.adjoint * B) w))
    (hσ : ∀ g w, ‖σ g w‖ = ‖w‖)
    (ht : (LinearMap.trace ℂ W (B.adjoint * B)).re = 1) :
    (A.adjoint * A - (Module.finrank ℂ V : ℂ) •
      (isotypicSpan ρ σ).starProjection.toLinearMap).IsPositive := by
  have hsym := (LinearMap.isPositive_adjoint_comp_self A).1
  have hP : (isotypicSpan ρ σ).starProjection.toLinearMap.IsSymmetric :=
    fun u v => (isotypicSpan ρ σ).inner_starProjection_left_eq_right u v
  refine ⟨hsym.sub (hP.smul (by simp)),?_⟩
  intro w
  have hn := whitening_norm ρ σ B A hA hAc hBA hT hσ ht w
  change 0 ≤ (inner ℂ (A.adjoint (A w) -
    (Module.finrank ℂ V : ℂ) • (isotypicSpan ρ σ).starProjection w) w).re
  rw [inner_sub_left,inner_smul_left,LinearMap.adjoint_inner_left,
    inner_self_eq_norm_sq_to_K]
  simp only [Complex.sub_re,Complex.mul_re,Complex.natCast_re,Complex.natCast_im,
    ← RCLike.ofReal_pow,map_natCast,zero_mul,sub_zero]
  change 0 ≤ ‖A w‖^2 - (Module.finrank ℂ V : ℝ) *
    RCLike.re (inner ℂ ((isotypicSpan ρ σ).starProjection w) w)
  rw [(isotypicSpan ρ σ).re_inner_starProjection_eq_normSq]
  exact sub_nonneg.mpr hn

end BinaryCoordinateSweeps.Irrep

end

section

open scoped BigOperators Classical ComplexOrder MatrixOrder
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma trace_product_nonneg {A B : Matrix I I ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A*B).trace := by
  obtain ⟨X,hX⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [hX,Matrix.star_eq_conjTranspose,Matrix.trace_mul_cycle,Matrix.trace_mul_cycle]
  exact (hB.mul_mul_conjTranspose_same X).trace_nonneg

lemma trace_product_mono {A B C : Matrix I I ℂ}
    (hA : A.PosSemidef) (hBC : (C-B).PosSemidef) : (A*B).trace ≤ (A*C).trace := by
  have h := trace_product_nonneg hA hBC
  rw [Matrix.mul_sub,Matrix.trace_sub] at h
  exact sub_nonneg.mp h

lemma trace_product_re_nonneg {A B : Matrix I I ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A*B).trace.re :=
  (Complex.nonneg_iff.mp (trace_product_nonneg hA hB)).1

lemma trace_product_re_mono {A B C : Matrix I I ℂ}
    (hA : A.PosSemidef) (hBC : (C-B).PosSemidef) :
    (A*B).trace.re ≤ (A*C).trace.re :=
  (Complex.le_def.mp (trace_product_mono hA hBC)).1

lemma tensor_product_trace_re {J A : Type*} [Fintype J] [DecidableEq J]
    [Fintype A] [DecidableEq A] (R C : J → Matrix A A ℂ)
    (hR : ∀ j, (R j).PosSemidef) (hC : ∀ j, (C j).PosSemidef) :
    (tensorMatrices R * tensorMatrices C).trace.re = ∏ j, (R j * C j).trace.re := by
  rw [tensorMatrices_mul,tensorMatrices_trace]
  have hh (j : J) : (R j * C j).trace = ((R j * C j).trace.re : ℂ) := by
    apply Complex.ext <;> simp [ (Complex.nonneg_iff.mp (trace_product_nonneg (hR j) (hC j))).2]
  rw [show (∏ j, (R j * C j).trace) = ∏ j, ((R j * C j).trace.re : ℂ) from
    Finset.prod_congr rfl (fun j _ => hh j)]
  rw [← Complex.ofReal_prod,Complex.ofReal_re]

end BinaryCoordinateSweeps.Density

end

open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {A : Type*} [Fintype A] [DecidableEq A]

lemma commutes_parity_iff (p : A → Bool) (M : Matrix A A ℂ) :
    Commute M (parityProjection p) ↔ ∀ a b, p a ≠ p b → M a b = 0 := by
  constructor
  · intro h a b hab
    have he := congrArg (fun N : Matrix A A ℂ => N a b) h.eq
    simp only [parityProjection,Matrix.mul_diagonal,Matrix.diagonal_mul] at he
    cases ha : p a <;> cases hb : p b <;> simp_all
  · intro h
    apply Matrix.ext
    intro a b
    simp only [parityProjection,Matrix.mul_diagonal,Matrix.diagonal_mul]
    by_cases he : p a = p b
    · rw [he]; ring
    · rw [h a b he]; simp

lemma sqrt_commutes {M N : Matrix A A ℂ} (hM : M.PosSemidef) (hc : Commute M N) :
    Commute (CFC.sqrt M) N := by
  rw [CFC.sqrt_eq_real_sqrt M hM.nonneg]
  exact hc.cfcₙ (by rwa [hM.isHermitian.star_eq]) Real.sqrt

theorem exists_even_whitening (p : A → Bool) (M : Matrix A A ℂ)
    (hM : M.PosDef) (he : ∀ a b, p a ≠ p b → M a b = 0) :
    ∃ B C : Matrix A A ℂ,
      B.PosSemidef ∧ C.PosSemidef ∧ B*B = M ∧ B*C = 1 ∧ C*B = 1 ∧
      (∀ a b, p a ≠ p b → B a b = 0) ∧ (∀ a b, p a ≠ p b → C a b = 0) := by
  let B := CFC.sqrt M
  have hB : B.PosSemidef := (CFC.sqrt_nonneg M).posSemidef
  have hBB : B*B = M := CFC.sqrt_mul_sqrt_self M hM.posSemidef.nonneg
  have hu : IsUnit B := (CFC.isUnit_sqrt_iff M hM.posSemidef.nonneg).mpr hM.isUnit
  let := hu.nonempty_invertible.some
  have heB := sqrt_commutes hM.posSemidef ((commutes_parity_iff p M).mpr he)
  refine ⟨B,⅟B,hB,?_,hBB,mul_invOf_self B,invOf_mul_self B,
    (commutes_parity_iff p B).mp heB,(commutes_parity_iff p (⅟B)).mp heB.invOf_left⟩
  rw [Matrix.invOf_eq_nonsing_inv]
  exact hB.inv

end BinaryCoordinateSweeps.Density

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

section

open scoped BigOperators Classical ComplexOrder MatrixOrder
open Matrix

namespace BinaryCoordinateSweeps.Irrep
open Representation Density

variable {G V I : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [Fintype I] [DecidableEq I]
  (ρ : Representation ℂ G V) (σ : Representation ℂ G (EuclideanSpace ℂ I))

omit [Fintype G] [FiniteDimensional ℂ V] in
theorem matrix_whitening_positive [ρ.IsIrreducible] (B C : Matrix I I ℂ)
    (hC : C.IsHermitian)
    (hCc : ∀ g w, C.toEuclideanLin (σ g w) = σ g (C.toEuclideanLin w))
    (hBC : B*C = 1)
    (hT : ∀ g w, (B.conjTranspose*B).toEuclideanLin (σ g w) =
      σ g ((B.conjTranspose*B).toEuclideanLin w))
    (hσ : ∀ g w, ‖σ g w‖ = ‖w‖)
    (ht : (B.conjTranspose*B).trace.re = 1) :
    (C.conjTranspose*C - (Module.finrank ℂ V : ℂ) •
      projectionMatrix (isotypicSpan ρ σ)).PosSemidef := by
  rw [← Matrix.isPositive_toEuclideanLin_iff]
  have hsym : C.toEuclideanLin.IsSymmetric := by
    apply (LinearMap.isSymmetric_iff_isSelfAdjoint _).mpr
    change C.toEuclideanLin.adjoint = C.toEuclideanLin
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,hC.eq]
  have h := whitening_positive ρ σ B.toEuclideanLin C.toEuclideanLin hsym hCc
    (by simpa only [Matrix.toLpLin_mul_same,← Module.End.mul_eq_comp,Matrix.toLpLin_one,← Module.End.one_eq_id] using
      congrArg Matrix.toEuclideanLin hBC)
    (by simpa only [Matrix.toLpLin_mul_same,← Module.End.mul_eq_comp,Matrix.toEuclideanLin_conjTranspose_eq_adjoint] using hT)
    hσ (by
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,Module.End.mul_eq_comp,← Matrix.toLpLin_mul_same,
        trace_toEuclideanLinear]
      exact ht)
  simpa only [map_sub,map_smul,projectionMatrix_linear,Matrix.toLpLin_mul_same,← Module.End.mul_eq_comp,
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint] using h

end BinaryCoordinateSweeps.Irrep

end

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep
open Representation

variable {G V W U : Type*} [Group G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U]
  (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (τ : Representation ℂ G U)

lemma map_isotypic_le (f : IntertwiningMap σ τ) :
    (isotypicSpan ρ σ).map f.toLinearMap ≤ isotypicSpan ρ τ := by
  rintro _ ⟨w,hw,rfl⟩
  apply Submodule.iSup_induction (fun g : IntertwiningMap ρ σ => LinearMap.range g.toLinearMap)
    (motive:=fun w => f w ∈ isotypicSpan ρ τ) hw
  · intro g w hw
    obtain ⟨v,rfl⟩ := hw
    exact (le_iSup (fun g : IntertwiningMap ρ τ => LinearMap.range g.toLinearMap) (f.comp g)) ⟨v,rfl⟩
  · simp
  · intro x y hx hy; simpa only [map_add] using (isotypicSpan ρ τ).add_mem hx hy

lemma map_isotypic_equiv (e : σ.Equiv τ) :
    (isotypicSpan ρ σ).map e.toLinearEquiv.toLinearMap = isotypicSpan ρ τ := by
  apply le_antisymm (map_isotypic_le ρ σ τ e.toIntertwiningMap)
  intro u hu
  refine ⟨e.symm u,?_,e.toLinearEquiv.apply_symm_apply u⟩
  apply map_isotypic_le ρ τ σ e.symm.toIntertwiningMap
  exact ⟨u,hu,rfl⟩

end BinaryCoordinateSweeps.Irrep

open scoped BigOperators Classical
open Matrix

end

open scoped BigOperators Classical MonoidAlgebra

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungResolution
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Classical
open Equiv Equiv.Perm Finset

namespace BinaryCoordinateSweeps.Signed

lemma koszulSign_eq_prod {n : ℕ} (β : Fin n → Bool) (g : Equiv.Perm (Fin n)) :
    koszulSign β g = ∏a, ∏b, pairWeight β g a b := by
  rw [← Fintype.prod_sigma (fun x : Σ _ : Fin n, Fin n => pairWeight β g x.1 x.2)]
  have he : finPairsLT n = Finset.univ.filter (fun x : Σ _ : Fin n, Fin n => x.2<x.1) := by
    ext x
    simp only [mem_finPairsLT,mem_filter,mem_univ,true_and]
  rw [koszulSign,he,Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro x _
  dsimp [pairWeight]
  by_cases h : x.2<x.1 <;> by_cases h1 : β x.1=true <;> by_cases h2 : β x.2=true <;> simp [h,h1,h2]

end BinaryCoordinateSweeps.Signed

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_TensorBounds_SignedBlock
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical Kronecker
open Equiv Matrix

namespace BinaryCoordinateSweeps.Signed
variable {A : Type*} [Fintype A] [DecidableEq A] {n m : ℕ}

lemma actionMatrix_apply (p : A → Bool) (g : Equiv.Perm (Fin n)) (x y : Fin n → A) :
    LinearMap.toMatrix' (act p g) x y = if x ∘ g = y then signC (p ∘ x) g⁻¹ else 0 := by
  simp only [LinearMap.toMatrix'_apply,act_apply,Pi.single_apply]
  split_ifs with h
  · simp
  · simp

end BinaryCoordinateSweeps.Signed

end

open scoped BigOperators Classical
open Matrix

namespace BinaryCoordinateSweeps.Signed
open Density

variable {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ}

lemma actionMatrix_conjugate_apply (p : A → Bool) (g : Equiv.Perm (Fin n))
    (M : Matrix (Fin n → A) (Fin n → A) ℂ) (x y : Fin n → A) :
    (actionMatrix p g * M * (actionMatrix p g).conjTranspose) x y=
      signC (p ∘ x) g⁻¹ * signC (p ∘ y) g⁻¹ * M (x ∘ g) (y ∘ g) := by
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,actionMatrix_apply]
  simp [apply_ite,signC_star,mul_assoc,mul_left_comm,mul_comm]

lemma actionMatrix_unitary (p : A → Bool) (g : Equiv.Perm (Fin n)) :
    actionMatrix p g * (actionMatrix p g).conjTranspose=1 := by
  have he (x y : Fin n → A) : x ∘ g = y ∘ g ↔ x=y :=
    (wordReorder g).injective.eq_iff
  ext x y
  have hh := actionMatrix_conjugate_apply p g 1 x y
  rw [mul_one] at hh
  rw [hh]
  by_cases h:x=y
  · subst y
    simp only [Matrix.one_apply,ite_true,signC_sq,mul_one]
  · simp [he,h]

lemma actionMatrix_star_mul (p : A → Bool) (g : Equiv.Perm (Fin n)) :
    (actionMatrix p g).conjTranspose * actionMatrix p g = 1 :=
  mul_eq_one_comm.mp (actionMatrix_unitary p g)

theorem even_tensor_covariance (p : A → Bool) (g : Equiv.Perm (Fin n))
    (M : Fin n → Matrix A A ℂ)
    (hM : ∀ i a b, p a ≠ p b → M i a b=0) :
    actionMatrix p g * tensorMatrices M * (actionMatrix p g).conjTranspose =
      tensorMatrices (fun i => M (g⁻¹ i)) := by
  ext x y
  rw [actionMatrix_conjugate_apply]
  have he : tensorMatrices M (x ∘ g) (y ∘ g) = tensorMatrices (fun i => M (g⁻¹ i)) x y := by
    simpa [tensorMatrices] using
      Equiv.prod_comp g (fun i => M (g⁻¹ i) (x i) (y i))
  rw [he]
  by_cases h : p ∘ x=p ∘ y
  · rw [h,signC_sq,one_mul]
  · obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    have hz : tensorMatrices (fun i => M (g⁻¹ i)) x y=0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (hM _ _ _ hi)
    rw [hz,mul_zero]

end BinaryCoordinateSweeps.Signed

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_TensorBounds_SignedConjugation
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical ComplexOrder
open Matrix

namespace BinaryCoordinateSweeps.Signed
open Density Irrep Representation

variable {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ}

lemma actionMatrix_one (p : A → Bool) : actionMatrix (n:=n) p 1=1 := by
  change LinearMap.toMatrix' ((tensorRep p n) 1)=_
  rw [map_one]
  exact LinearMap.toMatrix'_id

lemma signedConj_mul (p : A → Bool) (g : Equiv.Perm (Fin n))
    (M L : Matrix (Fin n → A) (Fin n → A) ℂ) :
    signedConj p g (M*L)=signedConj p g M*signedConj p g L := by
  unfold signedConj
  simp only [mul_assoc,← mul_assoc (actionMatrix p g).conjTranspose (actionMatrix p g),
    actionMatrix_star_mul,one_mul]

lemma signedConj_psd (p : A → Bool) (g : Equiv.Perm (Fin n))
    (M : Matrix (Fin n → A) (Fin n → A) ℂ) (hM : M.PosSemidef) :
    (signedConj p g M).PosSemidef := hM.mul_mul_conjTranspose_same _

lemma signedConj_fixed (p : A → Bool) (g : Equiv.Perm (Fin n))
    (M : Matrix (Fin n → A) (Fin n → A) ℂ)
    (hc : M*actionMatrix p g=actionMatrix p g*M) : signedConj p g M=M := by
  unfold signedConj
  rw [← hc,mul_assoc,actionMatrix_unitary,mul_one]

lemma signedConj_commutes (p : A → Bool) (g : Equiv.Perm (Fin n))
    (M Q : Matrix (Fin n → A) (Fin n → A) ℂ)
    (hc : M*actionMatrix p g=actionMatrix p g*M) (hq : M*Q=Q*M) :
    M*signedConj p g Q=signedConj p g Q*M := by
  rw [← signedConj_fixed p g M hc,← signedConj_mul,← signedConj_mul,hq]

lemma signedConj_sub_smul_sum {U : Type*} [Fintype U] (p : A → Bool) (g : Equiv.Perm (Fin n))
    (c : ℂ) (M : U → Matrix (Fin n → A) (Fin n → A) ℂ)
    (Q : Matrix (Fin n → A) (Fin n → A) ℂ) :
    signedConj p g (c • ∑u, M u-Q)=c • ∑u, signedConj p g (M u)-signedConj p g Q := by
  simp [signedConj,mul_sub,sub_mul,Matrix.mul_sum,Matrix.sum_mul]

end BinaryCoordinateSweeps.Signed

end

open scoped BigOperators Classical Kronecker
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {A B G : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

omit [DecidableEq A] in
lemma matrixSlice_mul_left (M : Matrix (A×B) (A×B) ℂ) (T : Matrix A A ℂ) (b c : B) :
    matrixSlice ((T ⊗ₖ (1 : Matrix B B ℂ))*M) b c = T*matrixSlice M b c := by
  ext a a'
  simp [matrixSlice,Matrix.mul_apply,Fintype.sum_prod_type,
    Matrix.one_apply,mul_ite,ite_mul]

omit [DecidableEq A] in
lemma matrixSlice_mul_right (M : Matrix (A×B) (A×B) ℂ) (T : Matrix A A ℂ) (b c : B) :
    matrixSlice (M*(T ⊗ₖ (1 : Matrix B B ℂ))) b c = matrixSlice M b c*T := by
  ext a a'
  simp [matrixSlice,Matrix.mul_apply,Fintype.sum_prod_type,
    Matrix.one_apply,mul_ite]

omit [DecidableEq A] in
theorem kronecker_centrality (T : G → Matrix A A ℂ) (P : Matrix A A ℂ)
    (hP : ∀ X : Matrix A A ℂ, (∀ g, X*T g=T g*X) → X*P=P*X)
    (M : Matrix (A×B) (A×B) ℂ)
    (hM : ∀ g, M*(T g ⊗ₖ (1 : Matrix B B ℂ))=(T g ⊗ₖ (1 : Matrix B B ℂ))*M) :
    M*(P ⊗ₖ (1 : Matrix B B ℂ))=(P ⊗ₖ (1 : Matrix B B ℂ))*M := by
  ext ⟨a,b⟩ ⟨a',c⟩
  have hc : ∀ g, matrixSlice M b c*T g=T g*matrixSlice M b c := by
    intro g
    have hh := congrArg (fun X => matrixSlice X b c) (hM g)
    simpa only [matrixSlice_mul_left,matrixSlice_mul_right] using hh
  have hh := hP (matrixSlice M b c) hc
  have he : matrixSlice (M*(P ⊗ₖ (1 : Matrix B B ℂ))) b c =
      matrixSlice ((P ⊗ₖ (1 : Matrix B B ℂ))*M) b c := by
    simpa only [matrixSlice_mul_left,matrixSlice_mul_right] using hh
  exact congrFun (congrFun he a) a'

end BinaryCoordinateSweeps.Density

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_PiCentrality
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical Kronecker
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {I : Type*} [Fintype I] [DecidableEq I]
  {A : I → Type*} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

omit [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] in
lemma piTensorMatrices_split (i : I) (P : ∀i, Matrix (A i) (A i) ℂ) :
    piTensorMatrices P = (P i ⊗ₖ piTensorMatrices (fun j : {j // j≠i} => P j)).submatrix
      (Equiv.piSplitAt i A) (Equiv.piSplitAt i A) := by
  ext x y
  change (∏j, P j (x j) (y j)) = P i (x i) (y i) * ∏j : {j // j≠i}, P j (x j) (y j)
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  congr 1
  exact Finset.prod_subtype (Finset.univ.erase i) (by intro j; simp [ne_comm]) _

omit [∀ i, Fintype (A i)] in
lemma siteMatrix_eq_mask (i : I) (P : ∀i, Matrix (A i) (A i) ℂ) :
    siteMatrix i (P i) = piTensorMatrices (fun j => if j=i then P j else 1) := by
  rw [piTensorMatrices_split i]
  simp only
  have he : piTensorMatrices (fun j : {j // j≠i} => if j.val=i then P j else 1)=1 := by
    have hh : (fun j : {j // j≠i} => if j.val=i then P j else 1) = (fun j : {j // j≠i} => (1 : Matrix (A j) (A j) ℂ)) := by
      funext j
      exact ite_eq_right j.property
    rw [hh]
    exact piTensorMatrices_one
  rw [he]
  rfl

lemma siteMatrix_centrality {G : Type*} (i : I) (T : G → Matrix (A i) (A i) ℂ)
    (P : Matrix (A i) (A i) ℂ)
    (hP : ∀ X : Matrix (A i) (A i) ℂ, (∀g, X*T g=T g*X) → X*P=P*X)
    (M : Matrix (∀i,A i) (∀i,A i) ℂ) (hM : ∀g, M*siteMatrix i (T g)=siteMatrix i (T g)*M) :
    M*siteMatrix i P=siteMatrix i P*M := by
  let e := Equiv.piSplitAt i A
  let E := Matrix.reindexAlgEquiv ℂ ℂ e
  have he (Q : Matrix (A i) (A i) ℂ) : E (siteMatrix i Q)=Q ⊗ₖ 1 := by
    ext x y
    change (Q ⊗ₖ 1) (e (e.symm x)) (e (e.symm y))=(Q ⊗ₖ 1) x y
    rw [Equiv.apply_symm_apply,Equiv.apply_symm_apply]
  have hc : ∀g, E M*(T g ⊗ₖ 1)=(T g ⊗ₖ 1)*E M := by
    intro g
    simpa only [map_mul,he] using congrArg E (hM g)
  apply E.injective
  simp only [map_mul,he]
  exact kronecker_centrality T P hP (E M) hc

theorem piTensor_centrality {G : I → Type*} (T : ∀ i, G i → Matrix (A i) (A i) ℂ)
    (P : ∀i, Matrix (A i) (A i) ℂ)
    (hP : ∀i, ∀X : Matrix (A i) (A i) ℂ, (∀g, X*T i g=T i g*X) → X*P i=P i*X)
    (M : Matrix (∀i,A i) (∀i,A i) ℂ)
    (hM : ∀i g, M*siteMatrix i (T i g)=siteMatrix i (T i g)*M) :
    M*piTensorMatrices P=piTensorMatrices P*M := by
  have hi (i : I) : M*siteMatrix i (P i)=siteMatrix i (P i)*M :=
    siteMatrix_centrality i (T i) (P i) (hP i) M (hM i)
  have hh (s : Finset I) : M*piTensorMatrices (fun i => if i∈s then P i else 1)=
      piTensorMatrices (fun i => if i∈s then P i else 1)*M := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.notMem_empty,ite_false,piTensorMatrices_one,mul_one,one_mul]
    | @insert i s his ih =>
      have he : piTensorMatrices (fun j => if j∈insert i s then P j else 1)=
          siteMatrix i (P i)*piTensorMatrices (fun j => if j∈s then P j else 1) := by
        rw [siteMatrix_eq_mask,piTensorMatrices_mul]
        congr 1
        funext j
        by_cases hji : j=i
        · subst j; simp [his]
        · simp [hji,Finset.mem_insert]
      rw [he,← mul_assoc,hi,mul_assoc,ih,← mul_assoc]
  simpa only [Finset.mem_univ,ite_true] using hh Finset.univ

end BinaryCoordinateSweeps.Density

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_MatrixBounds_SparsePinching
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators ComplexOrder
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]

omit [Fintype I] in
lemma sum_blockVec (f : I → J) (x : I → ℂ) : ∑ a, blockVec f a x = x := by
  ext i
  simp [blockVec]

omit [Fintype I] [Fintype J] in
lemma pinch_hermitian (f : I → J) {A : Matrix I I ℂ} (hA : A.IsHermitian) :
    (pinch f A).IsHermitian := by
  ext i j
  change star (if f j = f i then A j i else 0) = if f i = f j then A i j else 0
  by_cases h : f i = f j
  · rw [ite_eq_left h, ite_eq_left h.symm]
    exact congrFun (congrFun hA i) j
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h), star_zero]

lemma pinch_form (f : I → J) (A : Matrix I I ℂ) (x : I → ℂ) :
    star x ⬝ᵥ (pinch f A).mulVec x =
      ∑ a, star (blockVec f a x) ⬝ᵥ A.mulVec (blockVec f a x) := by
  simp only [dotProduct, mulVec, blockVec, pinch, Pi.star_apply, apply_ite, star_zero,
    Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [ite_mul, zero_mul, mul_ite, mul_zero]
  by_cases h : f i = f j
  · rw [h]
    simp
  · simp [h]

lemma pinch_posSemidef (f : I → J) {A : Matrix I I ℂ} (hA : A.PosSemidef) :
    (pinch f A).PosSemidef := by
  refine .of_dotProduct_mulVec_nonneg (pinch_hermitian f hA.1) (fun x => ?_)
  rw [pinch_form]
  exact Finset.sum_nonneg (fun a _ => hA.dotProduct_mulVec_nonneg _)

lemma form_cross_le {A : Matrix I I ℂ} (hA : A.PosSemidef) (x y : I → ℂ) :
    star x ⬝ᵥ A.mulVec y + star y ⬝ᵥ A.mulVec x ≤
      star x ⬝ᵥ A.mulVec x + star y ⬝ᵥ A.mulVec y := by
  have h := hA.dotProduct_mulVec_nonneg (x-y)
  rw [star_sub, mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub] at h
  exact sub_nonneg.mp (by convert h using 1; abel)

omit [Fintype J] in
lemma block_form_zero (f : I → J) (A : Matrix I I ℂ) (a b : J)
    (h : ∀ i j, f i = a → f j = b → A i j = 0) (x : I → ℂ) :
    star (blockVec f a x) ⬝ᵥ A.mulVec (blockVec f b x) = 0 := by
  simp only [dotProduct, mulVec, blockVec, Pi.star_apply, apply_ite, star_zero,
    Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  by_cases ha : f i = a
  · by_cases hb : f j = b
    · simp [ha, hb, h i j ha hb]
    · simp [hb]
  · simp [ha]

theorem sparse_pinching (f : I → J) (R : J → J → Prop) [DecidableRel R]
    (hR : ∀ ⦃left right⦄, R left right → R right left)
    (D : ℕ) (hD : ∀ a, (Finset.univ.filter (R a)).card ≤ D)
    {A : Matrix I I ℂ} (hA : A.PosSemidef)
    (hz : ∀ i j, ¬ R (f i) (f j) → A i j = 0) :
    ((D : ℂ) • pinch f A - A).PosSemidef := by
  have hp := pinch_hermitian f hA.1
  refine .of_dotProduct_mulVec_nonneg ((hp.smul (by simp)).sub hA.1) (fun x => ?_)
  let t : J → J → ℂ := fun a b => star (blockVec f a x) ⬝ᵥ A.mulVec (blockVec f b x)
  have hdiag (a : J) : 0 ≤ t a a := hA.dotProduct_mulVec_nonneg _
  have ht (a b : J) (hab : ¬R a b) : t a b = 0 := by
    apply block_form_zero
    intro i j hi hj
    exact hz i j (by simpa [hi, hj] using hab)
  have hsum : ∑ a, ∑ b ∈ Finset.univ.filter (R a), t a b = star x ⬝ᵥ A.mulVec x := by
    simp_rw [Finset.sum_filter]
    have ht' : ∀ a b, (if R a b then t a b else 0) = t a b := by
      intro a b
      split_ifs with h
      · rfl
      · exact (ht a b h).symm
    simp_rw [ht']
    dsimp [t]
    simp_rw [← dotProduct_sum, ← mulVec_sum, sum_blockVec]
    rw [← sum_dotProduct, ← star_sum, sum_blockVec]
  have hswap : ∑ a, ∑ b ∈ Finset.univ.filter (R a), t b a =
      ∑ a, ∑ b ∈ Finset.univ.filter (R a), t a b := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    have he : R b a ↔ R a b := ⟨fun h => hR h, fun h => hR h⟩
    simp only [he]
  have hdeg : ∑ a, ∑ b ∈ Finset.univ.filter (R a), (t a a + t b b) =
      2 * ∑ a, ((Finset.univ.filter (R a)).card : ℂ) * t a a := by
    simp only [Finset.sum_add_distrib]
    have hs : ∑ a, ∑ b ∈ Finset.univ.filter (R a), t b b =
        ∑ a, ∑ b ∈ Finset.univ.filter (R a), t a a := by
      simp only [Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      simp only [show R b a ↔ R a b from ⟨fun h => hR h, fun h => hR h⟩]
    rw [hs]
    simp [two_mul]
  have hle := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset J)) =>
    Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ.filter (R a)) =>
      form_cross_le hA (blockVec f a x) (blockVec f b x)))
  change (∑ a, ∑ b ∈ Finset.univ.filter (R a), (t a b + t b a)) ≤ _ at hle
  simp only [Finset.sum_add_distrib] at hle
  rw [hswap, hsum] at hle
  have hc : star x ⬝ᵥ A.mulVec x ≤ ∑ a, ((Finset.univ.filter (R a)).card : ℂ) * t a a := by
    have hh := hdeg
    simp only [Finset.sum_add_distrib] at hh
    rw [hh] at hle
    simp only [two_mul, Complex.le_def, Complex.add_re, Complex.add_im] at hle
    exact Complex.le_def.mpr ⟨by linarith [hle.1], by linarith [hle.2]⟩
  have hd : ∑ a, ((Finset.univ.filter (R a)).card : ℂ) * t a a ≤
      (D : ℂ) * ∑ a, t a a := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hD a) (hdiag a)
  have hf := hc.trans hd
  rw [sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, smul_eq_mul]
  apply sub_nonneg.mpr
  simpa only [pinch_form, t] using hf

end BinaryCoordinateSweeps.Density

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Density
variable {I : Type*} [Fintype I] [LinearOrder I]

omit [Fintype I] in
lemma subsetCode_range (k : ℕ) (s : Finset I) (hs : s.card ≤ k) (j : I) :
    some j ∈ Set.range (subsetCode k s) ↔ j ∈ s := by
  constructor
  · rintro ⟨i,hi⟩
    dsimp only [subsetCode] at hi
    split_ifs at hi with h
    · have hj := Option.some.inj hi
      rw [← hj]
      exact Finset.orderEmbOfFin_mem s rfl _
  · intro hj
    have hr : j ∈ Set.range (s.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]; exact hj
    obtain ⟨i,hi⟩ := hr
    refine ⟨⟨i.val, i.isLt.trans_le hs⟩, ?_⟩
    simp only [subsetCode, dite_eq_left i.isLt]
    exact congrArg some hi

lemma card_small_subsets_le (k : ℕ) :
    Fintype.card {s : Finset I // s.card ≤ k} ≤ (Fintype.card I + 1)^k := by
  let f : {s : Finset I // s.card ≤ k} → (Fin k → Option I) := fun s => subsetCode k s.val
  have hf : Function.Injective f := by
    intro s t h
    apply Subtype.ext
    ext j
    rw [← subsetCode_range k s.val s.property j, ← subsetCode_range k t.val t.property j]
    rw [show Set.range (subsetCode k s.val) = Set.range (subsetCode k t.val) from
      congrArg Set.range h]
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_fun, Fintype.card_fin, Fintype.card_option] using hc

omit [LinearOrder I] in
lemma hamming_symm (a b : I → Bool) : hamming a b = hamming b a := by
  unfold hamming
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_comm]

lemma hamming_degree (a : I → Bool) (k : ℕ) :
    (Finset.univ.filter (fun b => hamming a b ≤ k)).card ≤ (Fintype.card I + 1)^k := by
  let f : {b : I → Bool // hamming a b ≤ k} → {s : Finset I // s.card ≤ k} :=
    fun b => ⟨Finset.univ.filter (fun i => a i ≠ b.val i), b.property⟩
  have hf : Function.Injective f := by
    intro b c h
    apply Subtype.ext
    funext i
    have hi := Finset.ext_iff.mp (congrArg Subtype.val h) i
    simp only [f, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    cases ha : a i <;> cases hb : b.val i <;> cases hc : c.val i <;>
      simp_all only [Bool.false_eq_true, Bool.true_eq_false, not_false_eq_true, ne_eq,
        not_true_eq_false, iff_false, iff_true]
  have hh := (Fintype.card_le_of_injective f hf).trans (card_small_subsets_le (I := I) k)
  simpa only [Fintype.card_subtype] using hh

end BinaryCoordinateSweeps.Density

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_TensorBounds_SignedPinching
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical ComplexOrder
open Equiv Equiv.Perm Matrix

namespace BinaryCoordinateSweeps.Signed
open Density

variable {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ}

lemma pinch_trace {I J : Type*} [Fintype I] [DecidableEq J] (f : I → J) (M : Matrix I I ℂ) :
    (pinch f M).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag, pinch, ite_true]

omit [Fintype A] [DecidableEq A] in
lemma comp_parity_eq_iff (p : A → Bool) (x y : Fin n → A) (g : Equiv.Perm (Fin n)) :
    p ∘ (x ∘ g) = p ∘ (y ∘ g) ↔ p ∘ x = p ∘ y := by
  constructor
  · intro h
    funext i
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using congrFun h (g.symm i)
  · intro h
    exact congrArg (fun f => f ∘ g) h

omit [Fintype A] [DecidableEq A] in
lemma pinch_block (p : A → Bool) (M : Matrix (Fin n → A) (Fin n → A) ℂ)
    (x y : Fin n → A) (h : p ∘ x ≠ p ∘ y) :
    pinch (fun w => p ∘ w) M x y = 0 := ite_eq_right h

omit [Fintype A] [DecidableEq A] in
lemma pinch_invariant (p : A → Bool) (M : Matrix (Fin n → A) (Fin n → A) ℂ)
    (hM : Invariant p M) (g : Equiv.Perm (Fin n)) (x y : Fin n → A) :
    pinch (fun w => p ∘ w) M (x ∘ g) (y ∘ g) = pinch (fun w => p ∘ w) M x y := by
  simp only [pinch, comp_parity_eq_iff]
  split_ifs with h
  · exact invariant_same_parity p M hM g x y h
  · rfl

omit [DecidableEq A] in
lemma signed_sparse_pinching (p : A → Bool) (M : Matrix (Fin n → A) (Fin n → A) ℂ)
    (hM : M.PosSemidef) (hInv : Invariant p M) :
    (((n+1 : ℕ)^((Fintype.card A)^2) : ℂ) • pinch (fun w => p ∘ w) M - M).PosSemidef := by
  let R : (Fin n → Bool) → (Fin n → Bool) → Prop :=
    fun a b => hamming a b ≤ (Fintype.card A)^2
  have hR : ∀ ⦃left right⦄, R left right → R right left := by
    intro a b h
    change hamming b a ≤ (Fintype.card A)^2
    rw [hamming_symm b a]
    exact h
  have hD : ∀ a : Fin n → Bool, (Finset.univ.filter (R a)).card ≤
      (n+1)^((Fintype.card A)^2) := by
    intro a
    simpa only [Fintype.card_fin] using hamming_degree a ((Fintype.card A)^2)
  have hz : ∀ x y : Fin n → A, ¬R (p ∘ x) (p ∘ y) → M x y = 0 := by
    intro x y h
    by_contra hn
    exact h (invariant_mismatch_card p M hInv x y hn)
  simpa only [Nat.cast_pow] using
    sparse_pinching (fun w => p ∘ w) R hR ((n+1)^((Fintype.card A)^2)) hD hM hz

theorem signed_psd_postselection (n : ℕ) (hn : 0 < n) (p : A → Bool)
    (M : Matrix (Fin n → A) (Fin n → A) ℂ) (hM : M.PosSemidef) (hInv : Invariant p M) :
    ((((n+1 : ℕ)^((Fintype.card A)^2) : ℂ) * M.trace) •
      (∑ c : WordType (MatchedPair p) n, ∑ t : MatchedPair p → ZMod (n+1),
        matrixTensorPower n (reducedPhaseDensity n (matchedEmbedding p) c t)) - M).PosSemidef := by
  let Q := pinch (fun w => p ∘ w) M
  have hQ := pinch_posSemidef (fun w => p ∘ w) hM
  have hd := even_block_postselection n hn p Q hQ (pinch_block p M) (pinch_invariant p M hInv)
  rw [pinch_trace] at hd
  have hc : (0 : ℂ) ≤ ((n+1 : ℕ)^((Fintype.card A)^2) : ℂ) := by
    exact_mod_cast Nat.zero_le ((n+1)^((Fintype.card A)^2))
  have hh := (hd.smul hc).add (signed_sparse_pinching p M hM hInv)
  simp only [smul_sub, smul_smul] at hh
  convert hh using 1; dsimp only [Q]; abel

end BinaryCoordinateSweeps.Signed

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Representations_IsotypicDensity
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical ComplexOrder
open Equiv Equiv.Perm Matrix Representation

namespace BinaryCoordinateSweeps.Signed
open Density Irrep

variable {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ}

lemma projectionMatrix_invariant (p : A → Bool) (S : Submodule ℂ ((Fin n → A) → ℂ))
    (hS : ∀ g, S.map (act p g) = S) :
    Invariant p (projectionMatrix (hilbertSubspace S)) := by
  have h := intertwiner_matrix_invariant p (projectionIntertwiner p S hS)
  change Invariant p (LinearMap.toMatrix' ((coeffEquiv A n).conj
    (hilbertSubspace S).starProjection.toLinearMap)) at h
  rw [show coeffEquiv A n = WithLp.linearEquiv 2 ℂ ((Fin n → A) → ℂ) from rfl,
    projectionMatrix_coeff] at h
  exact h

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

omit [FiniteDimensional ℂ V] in
lemma isotypicProjection_psd (p : A → Bool) (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) :
    (isotypicProjection p ρ).PosSemidef := projectionMatrix_psd _

omit [FiniteDimensional ℂ V] in
lemma isotypicProjection_invariant (p : A → Bool)
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) : Invariant p (isotypicProjection p ρ) := by
  apply projectionMatrix_invariant
  exact isotypicSpan_map ρ (tensorRep p n)

omit [FiniteDimensional ℂ V] in
lemma isotypicProjection_trace (p : A → Bool)
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) :
    (isotypicProjection p ρ).trace =
      (Module.finrank ℂ (isotypicSpan ρ (tensorRep p n)) : ℂ) := by
  rw [isotypicProjection, projectionMatrix_trace, hilbertSubspace_finrank]

lemma isotypicSpan_rank_bound (p : A → Bool)
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) [ρ.IsIrreducible] :
    Module.finrank ℂ (isotypicSpan ρ (tensorRep p n)) ≤
      Module.finrank ℂ V * (n+1)^((Fintype.card A)^2) := by
  exact (isotypicSpan_finrank ρ (tensorRep p n)).trans (Nat.mul_le_mul_left _
    ((multiplicity_le_commutant ρ (tensorRep p n)).trans (tensor_commutant_finrank p n)))

theorem isotypic_density_domination (n : ℕ) (hn : 0 < n) (p : A → Bool)
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) [ρ.IsIrreducible] :
    (((Module.finrank ℂ V : ℂ) * (n+1 : ℂ)^(2*(Fintype.card A)^2)) •
      (∑ c : WordType (MatchedPair p) n, ∑ t : MatchedPair p → ZMod (n+1),
        matrixTensorPower n (reducedPhaseDensity n (matchedEmbedding p) c t)) -
      isotypicProjection p ρ).PosSemidef := by
  let Q := ∑ c : WordType (MatchedPair p) n, ∑ t : MatchedPair p → ZMod (n+1),
        matrixTensorPower n (reducedPhaseDensity n (matchedEmbedding p) c t)
  have hQ : Q.PosSemidef := by
    apply Matrix.posSemidef_sum
    intro c _
    apply Matrix.posSemidef_sum
    intro t _
    rw [reducedPhaseDensity, ← tensor_gram]
    exact gram_psd _
  have hd := signed_psd_postselection n hn p (isotypicProjection p ρ)
    (isotypicProjection_psd p ρ) (isotypicProjection_invariant p ρ)
  rw [isotypicProjection_trace] at hd
  simp only [Nat.cast_add, Nat.cast_one] at hd
  have hr : (Module.finrank ℂ (isotypicSpan ρ (tensorRep p n)) : ℂ) ≤
      (Module.finrank ℂ V : ℂ) * (n+1 : ℂ)^((Fintype.card A)^2) := by
    exact_mod_cast isotypicSpan_rank_bound p ρ
  have hc : (0 : ℂ) ≤ (n+1 : ℂ)^((Fintype.card A)^2) := by positivity
  have hh := hQ.smul (mul_nonneg hc (sub_nonneg.mpr hr))
  have he : (n+1 : ℂ)^((Fintype.card A)^2) *
        ((Module.finrank ℂ V : ℂ) * (n+1 : ℂ)^((Fintype.card A)^2) -
          (Module.finrank ℂ (isotypicSpan ρ (tensorRep p n)) : ℂ)) +
        (n+1 : ℂ)^((Fintype.card A)^2) *
          (Module.finrank ℂ (isotypicSpan ρ (tensorRep p n)) : ℂ) =
      (Module.finrank ℂ V : ℂ) * (n+1 : ℂ)^(2*(Fintype.card A)^2) := by
    rw [two_mul, pow_add]
    ring
  have hi := hh.add hd
  change (_ • Q + (_ • Q - isotypicProjection p ρ)).PosSemidef at hi
  rw [← add_sub_assoc, ← add_smul, he] at hi
  exact hi

end BinaryCoordinateSweeps.Signed

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_TensorBounds_SignedWhitening
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace BinaryCoordinateSweeps.Signed
open Irrep Density Representation

variable {A V : Type*} [Fintype A] [DecidableEq A] {n : ℕ}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

omit [DecidableEq A] in
lemma hilbertTensorRep_unitary (p : A → Bool) (g : Equiv.Perm (Fin n)) (v : TensorSpace A n) :
    ‖hilbertTensorRep p n g v‖ = ‖v‖ := (actionIsometry p g).norm_map v

omit [FiniteDimensional ℂ V] [DecidableEq A] in
lemma hilbert_isotypic_eq (p : A → Bool) (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) :
    isotypicSpan ρ (hilbertTensorRep p n) = hilbertSubspace (isotypicSpan ρ (tensorRep p n)) := by
  exact (map_isotypic_equiv ρ (tensorRep p n) (hilbertTensorRep p n)
    (conjugateEquiv (tensorRep p n) (coeffEquiv A n).symm)).symm

lemma even_tensor_hilbert_commutes (p : A → Bool) (M : Matrix A A ℂ)
    (hM : ∀ a b, p a ≠ p b → M a b = 0) (g : Equiv.Perm (Fin n)) (v : TensorSpace A n) :
    (matrixTensorPower n M).toEuclideanLin (hilbertTensorRep p n g v) =
      hilbertTensorRep p n g ((matrixTensorPower n M).toEuclideanLin v) := by
  apply (coeffEquiv A n).injective
  exact invariant_mulVec_commutes p (matrixTensorPower n M) (even_tensor_invariant p M hM) g
    (coeffEquiv A n v)

omit [FiniteDimensional ℂ V] in
theorem signed_tensor_whitening (p : A → Bool)
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) [ρ.IsIrreducible]
    (M B C : Matrix A A ℂ) (hB : B.PosSemidef) (hC : C.PosSemidef)
    (hBB : B*B=M) (hBC : B*C=1) (ht : M.trace=1)
    (heM : ∀ a b, p a ≠ p b → M a b = 0)
    (heC : ∀ a b, p a ≠ p b → C a b = 0) :
    ((matrixTensorPower n C).conjTranspose * matrixTensorPower n C -
      (Module.finrank ℂ V : ℂ) • isotypicProjection p ρ).PosSemidef := by
  have hpow (N : Matrix A A ℂ) : matrixTensorPower n N = tensorMatrices (fun _ : Fin n => N) := rfl
  have hBA : matrixTensorPower n B * matrixTensorPower n C = 1 := by
    rw [hpow,hpow,tensorMatrices_mul]
    simpa only [hBC] using (tensorMatrices_one (I:=Fin n) (A:=A))
  have hBT : (matrixTensorPower n B).conjTranspose * matrixTensorPower n B =
      matrixTensorPower n M := by
    rw [hpow,hpow,tensorMatrices_star,tensorMatrices_mul]
    simp only [hB.isHermitian.eq,hBB]
  have hCt : (matrixTensorPower n C).PosSemidef := by
    rw [hpow]; exact tensorMatrices_psd _ (fun _ => hC)
  have h := matrix_whitening_positive ρ (hilbertTensorRep p n)
    (matrixTensorPower n B) (matrixTensorPower n C) hCt.isHermitian
    (even_tensor_hilbert_commutes p C heC) hBA (by
      rw [hBT]; exact even_tensor_hilbert_commutes p M heM)
    (hilbertTensorRep_unitary p) (by rw [hBT,hpow,tensorMatrices_trace]; simp [ht])
  simpa only [hilbert_isotypic_eq,isotypicProjection] using h

end BinaryCoordinateSweeps.Signed

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_BoardProduct
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Density

theorem product_on_board_le_exp {I : Type*} [Fintype I] [DecidableEq I]
    (S : Finset I) (x : I → ℝ) (hx : ∀ i, 0 ≤ x i) (C : ℝ)
    (hs : ∑ i, x i ≤ C) :
    ∏ i ∈ S, x i ≤ Real.exp (C - S.card) := by
  have he (a : ℝ) : a ≤ Real.exp (a-1) := by
    have := Real.add_one_le_exp (a-1)
    linarith
  calc
    _ ≤ ∏ i ∈ S, Real.exp (x i - 1) :=
      Finset.prod_le_prod (fun index _ => hx index) (fun index _ => he (x index))
    _ = Real.exp ((∑ i ∈ S, x i) - S.card) := by
      rw [← Real.exp_sum,Finset.sum_sub_distrib]
      simp
    _ ≤ Real.exp (C - S.card) := by
      apply Real.exp_le_exp.mpr
      exact sub_le_sub_right ((Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ S) (fun i _ _ => hx i)).trans hs) _

 theorem rectangular_product_holes {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (S : Finset (I × J)) (x : I → J → ℝ)
    (hx : ∀ i j, 0 ≤ x i j)
    (hs : ∀ j, ∑ i, x i j ≤ Fintype.card I) :
    ∏ t ∈ S, x t.1 t.2 ≤
      Real.exp (Fintype.card I * Fintype.card J - S.card) := by
  apply product_on_board_le_exp S (fun t => x t.1 t.2) (fun t => hx t.1 t.2)
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  simpa [mul_comm] using Finset.sum_le_sum (s:=Finset.univ) (fun j _ => hs j)

end BinaryCoordinateSweeps.Density

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_MatrixBounds_TraceInterpolation
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator

namespace BinaryCoordinateSweeps.TraceHolder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma star_diagReal (s : ι → ℝ) : star (diagReal s) = diagReal s := by
  simp [diagReal, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]

lemma diagReal_mul (s t : ι → ℝ) : diagReal s * diagReal t = diagReal (fun i => s i*t i) := by
  simp [diagReal, Matrix.diagonal_mul_diagonal, Complex.ofReal_mul]

omit [DecidableEq ι] in
lemma gram_product (X Y : M ι) :
    star (X*Y) * (X*Y) = star Y * (star X * X) * Y := by
  simp only [star_mul, mul_assoc]

lemma gram_diagonal_factor (X : M ι) (s : ι → ℝ)
    (hX : star X * X = diagReal (fun i => s i ^ 2)) :
    ∃ U : M ι, ‖U‖ ≤ 1 ∧ X = U * diagReal s := by
  let t : ι → ℝ := fun i => (s i)⁻¹
  let U := X * diagReal t
  have hU : star U * U = diagReal (fun i => if s i = 0 then 0 else 1) := by
    rw [gram_product, hX, star_diagReal, diagReal_mul, diagReal_mul]
    congr 1
    funext i
    dsimp [t]
    split_ifs with hi
    · simp [hi]
    · field_simp
  have hUnorm : ‖U‖ ≤ 1 := by
    have h : ‖star U * U‖ ≤ 1 := by
      rw [hU, diagReal, Matrix.l2_opNorm_diagonal]
      apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
      intro i
      split_ifs <;> norm_num
    rw [CStarRing.norm_star_mul_self] at h
    nlinarith [norm_nonneg U]
  let w : ι → ℝ := fun i => 1 - t i * s i
  have hz : star (X * diagReal w) * (X * diagReal w) = 0 := by
    rw [gram_product, hX, star_diagReal, diagReal_mul, diagReal_mul]
    have hw : (fun i => (w i * s i ^ 2) * w i) = 0 := by
      funext i
      dsimp [w, t]
      by_cases hi : s i = 0 <;> simp [hi]
    rw [hw]
    simp [diagReal]
  have hzero : X * diagReal w = 0 := (CStarRing.star_mul_self_eq_zero_iff _).mp hz
  have hw : diagReal w = 1 - diagReal t * diagReal s := by
    rw [diagReal_mul]
    dsimp [diagReal, w]
    rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
    congr 1
    funext i
    simp
  rw [hw, mul_sub, mul_one] at hzero
  refine ⟨U, hUnorm, ?_⟩
  exact (sub_eq_zero.mp hzero).trans (mul_assoc _ _ _).symm

theorem exists_partial_svd (A : M ι) :
    ∃ (U : M ι) (V : Matrix.unitaryGroup ι ℂ) (s : ι → ℝ),
      (∀ i, 0 ≤ s i) ∧ ‖U‖ ≤ 1 ∧
      A = U * diagReal s * star (V : M ι) ∧
      star A * A = (V : M ι) * diagReal (fun i => s i ^ 2) * star (V : M ι) := by
  let h := Matrix.isHermitian_conjTranspose_mul_self A
  let V := h.eigenvectorUnitary
  let s : ι → ℝ := fun i => Real.sqrt (h.eigenvalues i)
  have hs0 : ∀ i, 0 ≤ s i := fun i => Real.sqrt_nonneg _
  have hs : ∀ i, s i ^ 2 = h.eigenvalues i := fun i =>
    Real.sq_sqrt (Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i)
  have hdiag : star (V : M ι) * (star A * A) * (V : M ι) =
      diagReal (fun i => s i ^ 2) := by
    simpa only [V, s, hs, diagReal, Matrix.star_eq_conjTranspose, Function.comp_def,
      Unitary.conjStarAlgAut_star_apply] using! h.conjStarAlgAut_star_eigenvectorUnitary
  have hgram : star (A * (V : M ι)) * (A * (V : M ι)) =
      diagReal (fun i => s i ^ 2) := by rw [gram_product, hdiag]
  obtain ⟨U, hU, heq⟩ := gram_diagonal_factor (A * (V : M ι)) s hgram
  have hVV : (V : M ι) * star (V : M ι) = 1 := by
    simpa only [Unitary.coe_star] using Unitary.coe_mul_star_self V
  refine ⟨U, V, s, hs0, hU, ?_, ?_⟩
  · have heq' := congrArg (fun X => X * star (V : M ι)) heq
    simpa only [mul_assoc, hVV, mul_one] using heq'
  · calc
      star A * A = ((V : M ι) * star (V : M ι)) * (star A * A) *
          ((V : M ι) * star (V : M ι)) := by rw [hVV, one_mul, mul_one]
      _ = (V : M ι) * (star (V : M ι) * (star A * A) * (V : M ι)) *
          star (V : M ι) := by simp only [mul_assoc]
      _ = _ := by rw [hdiag]

end BinaryCoordinateSweeps.TraceHolder

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_MatrixBounds_SpectralMoment
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace BinaryCoordinateSweeps.TraceHolder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma diagReal_pow (s : ι → ℝ) (q : ℕ) :
    (diagReal s)^q = diagReal (fun i => s i ^ q) := by
  simp [diagReal, Matrix.diagonal_pow]

lemma trace_unitary_conj (V : Matrix.unitaryGroup ι ℂ) (B : M ι) :
    Matrix.trace ((V : M ι) * B * star (V : M ι)) = Matrix.trace B := by
  rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]

lemma unitary_conj_pow (V : Matrix.unitaryGroup ι ℂ) (B : M ι) (q : ℕ) :
    ((V : M ι) * B * star (V : M ι))^q = (V : M ι) * B^q * star (V : M ι) := by
  have h := ((Unitary.conjStarAlgAut ℂ (M ι) V).toAlgEquiv.map_pow B q).symm
  change (Unitary.conjStarAlgAut ℂ (M ι) V B)^q =
    Unitary.conjStarAlgAut ℂ (M ι) V (B^q) at h
  simpa only [Unitary.conjStarAlgAut_apply, Unitary.coe_star] using h

lemma matrixMoment_of_svd (A : M ι) (q : ℕ) (V : Matrix.unitaryGroup ι ℂ)
    (s : ι → ℝ) (hgram : star A * A = (V : M ι) * diagReal (fun i => s i^2) * star (V : M ι)) :
    matrixMoment q A = ∑ i, s i ^ (2*q) := by
  rw [matrixMoment, hgram, unitary_conj_pow, trace_unitary_conj, diagReal_pow]
  simp only [diagReal, Matrix.trace_diagonal,
    Complex.re_sum, Complex.ofReal_re, ← pow_mul]

lemma matrixMoment_nonneg (q : ℕ) (A : M ι) : 0 ≤ matrixMoment q A := by
  obtain ⟨U, V, s, hs, hU, hA, hg⟩ := exists_partial_svd A
  rw [matrixMoment_of_svd A q V s hg]
  exact Finset.sum_nonneg (fun i _ => pow_nonneg (hs i) _)

lemma unitary_norm_le_one (V : Matrix.unitaryGroup ι ℂ) : ‖(V : M ι)‖ ≤ 1 := by
  have h1 : ‖(1 : M ι)‖ ≤ 1 := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr (by simp)
  have h : ‖(V : M ι)‖ * ‖(V : M ι)‖ ≤ 1 := by
    rw [← CStarRing.norm_star_mul_self, Unitary.coe_star_mul_self]
    exact h1
  nlinarith [norm_nonneg (V : M ι)]

end BinaryCoordinateSweeps.TraceHolder

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Representations_IsotypicCentrality
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
open Matrix

namespace BinaryCoordinateSweeps.Irrep
open Representation Density

variable {G V W I : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  [Fintype I] [DecidableEq I]

lemma projection_commutes_of_adjoint_invariant (S : Submodule ℂ W) (T : Module.End ℂ W)
    (hT : ∀ w ∈ S, T w ∈ S) (hTadj : ∀ w ∈ S, T.adjoint w ∈ S) (w : W) :
    T (S.starProjection w)=S.starProjection (T w) := by
  symm
  apply S.eq_starProjection_of_mem_of_inner_eq_zero (hT _ (S.starProjection_apply_mem w))
  intro u hu
  rw [← map_sub,← LinearMap.adjoint_inner_right]
  exact S.starProjection_inner_eq_zero w (T.adjoint u) (hTadj u hu)

omit [Fintype G] [FiniteDimensional ℂ V] in
theorem isotypicProjection_central (ρ : Representation ℂ G V)
    (σ : Representation ℂ G (EuclideanSpace ℂ I))
    (hσ : ∀ g v, ‖σ g v‖=‖v‖) (M : Matrix I I ℂ)
    (hc : ∀ g v, M.toEuclideanLin (σ g v)=σ g (M.toEuclideanLin v)) :
    M*projectionMatrix (isotypicSpan ρ σ)=projectionMatrix (isotypicSpan ρ σ)*M := by
  let f : IntertwiningMap σ σ :=
    ⟨M.toEuclideanLin,fun g => LinearMap.ext (hc g)⟩
  have hf : ∀ w ∈ isotypicSpan ρ σ, M.toEuclideanLin.adjoint w ∈ isotypicSpan ρ σ := by
    intro w hw
    exact map_isotypic_le ρ σ σ (adjointIntertwiner σ σ hσ hσ f) ⟨w,hw,rfl⟩
  apply Matrix.toEuclideanLin.injective
  simp only [Matrix.toLpLin_mul_same,projectionMatrix_linear]
  apply LinearMap.ext
  intro v
  exact projection_commutes_of_adjoint_invariant (isotypicSpan ρ σ) M.toEuclideanLin
    (commuting_isotypic_invariant ρ σ M.toEuclideanLin hc) hf v

end BinaryCoordinateSweeps.Irrep

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_TensorBounds_SignedTypeCentrality
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
open Matrix

namespace BinaryCoordinateSweeps.Signed
open Density Irrep Representation

variable {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ}
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

lemma actionMatrix_linear (p : A → Bool) (g : Equiv.Perm (Fin n)) :
    (actionMatrix p g).toEuclideanLin=hilbertTensorRep p n g := by
  ext v x
  change ((LinearMap.toMatrix' (act p g)).mulVec (coeffEquiv A n v)) x = _
  rw [LinearMap.toMatrix'_mulVec]
  rfl

lemma invariant_matrix_commutes (p : A → Bool) (M : Matrix (Fin n → A) (Fin n → A) ℂ)
    (hM : Invariant p M) (g : Equiv.Perm (Fin n)) :
    M*actionMatrix p g=actionMatrix p g*M := by
  apply Matrix.toEuclideanLin.injective
  simp only [Matrix.toLpLin_mul_same,actionMatrix_linear]
  apply LinearMap.ext
  intro v
  apply (coeffEquiv A n).injective
  exact invariant_mulVec_commutes p M hM g (coeffEquiv A n v)

omit [FiniteDimensional ℂ V] in
lemma typeProjection_central (p : A → Bool)
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V)
    (M : Matrix (Fin n → A) (Fin n → A) ℂ)
    (hc : ∀g, M*actionMatrix p g=actionMatrix p g*M) :
    M*isotypicProjection p ρ=isotypicProjection p ρ*M := by
  have hh (g : Equiv.Perm (Fin n)) (v : TensorSpace A n) :
      M.toEuclideanLin (hilbertTensorRep p n g v)=hilbertTensorRep p n g (M.toEuclideanLin v) := by
    have h := congrArg (fun Q => Q.toEuclideanLin v) (hc g)
    simpa only [Matrix.toLpLin_mul_same,LinearMap.comp_apply,actionMatrix_linear] using h
  have h := isotypicProjection_central ρ (hilbertTensorRep p n)
    (hilbertTensorRep_unitary p) M hh
  simpa only [hilbert_isotypic_eq,isotypicProjection] using h

end BinaryCoordinateSweeps.Signed

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_KoszulBlocks
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Signed
variable {I : Type*} [Fintype I] [LinearOrder I] {n : I → ℕ} {N : ℕ}

omit [Fintype I] in
private lemma block_lt_iff (e : (Σₗ i, Fin (n i)) ≃o Fin N)
    (i j : I) (a : Fin (n i)) (b : Fin (n j)) :
    e (toLex ⟨i,a⟩) < e (toLex ⟨j,b⟩) ↔ i < j ∨ ∃ h : i = j, h ▸ a < b :=
  e.lt_iff_lt.trans Sigma.lex_iff

omit [Fintype I] in
private lemma block_le_iff (e : (Σₗ i, Fin (n i)) ≃o Fin N)
    (i j : I) (a : Fin (n i)) (b : Fin (n j)) :
    e (toLex ⟨i,a⟩) ≤ e (toLex ⟨j,b⟩) ↔ i < j ∨ ∃ h : i = j, h ▸ a ≤ b :=
  e.le_iff_le.trans Sigma.lex_iff

omit [Fintype I] in
lemma pairWeight_sameBlock (e : (Σₗ i, Fin (n i)) ≃o Fin N)
    (g : ∀i, Equiv.Perm (Fin (n i))) (β : Fin N → Bool) (i : I) (a b : Fin (n i)) :
    pairWeight β (blockPerm e g) (e (toLex ⟨i,a⟩)) (e (toLex ⟨i,b⟩)) =
      pairWeight (fun a => β (e (toLex ⟨i,a⟩))) (g i) a b := by
  simp only [pairWeight, blockPerm_apply, block_lt_iff, block_le_iff]
  simp

omit [Fintype I] in
lemma pairWeight_differentBlock (e : (Σₗ i, Fin (n i)) ≃o Fin N)
    (g : ∀i, Equiv.Perm (Fin (n i))) (β : Fin N → Bool)
    {i j : I} (hji : j≠i) (a : Fin (n i)) (b : Fin (n j)) :
    pairWeight β (blockPerm e g) (e (toLex ⟨i,a⟩)) (e (toLex ⟨j,b⟩)) = 1 := by
  simp only [pairWeight, blockPerm_apply, block_lt_iff, block_le_iff]
  rcases lt_or_gt_of_ne hji with h | h
  · simp [h, hji, hji.symm, not_lt_of_gt h]
  · simp [hji, not_lt_of_gt h]

theorem koszulSign_blocks (e : (Σₗ i, Fin (n i)) ≃o Fin N)
    (g : ∀i, Equiv.Perm (Fin (n i))) (β : Fin N → Bool) :
    koszulSign β (blockPerm e g) = ∏i, koszulSign (fun a => β (e (toLex ⟨i,a⟩))) (g i) := by
  rw [koszulSign_eq_prod,← Equiv.prod_comp e.toEquiv]
  change (∏x : Σ i, Fin (n i), ∏b, pairWeight β (blockPerm e g) (e (toLex x)) b)=_
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro i _
  rw [koszulSign_eq_prod]
  apply Finset.prod_congr rfl
  intro a _
  rw [← Equiv.prod_comp e.toEquiv]
  change (∏y : Σ j, Fin (n j), pairWeight β (blockPerm e g) (e (toLex ⟨i,a⟩)) (e (toLex y)))=_
  rw [Fintype.prod_sigma]
  rw [Finset.prod_eq_single i]
  · apply Finset.prod_congr rfl
    intro b _
    exact pairWeight_sameBlock e g β i a b
  · intro j _ hji
    apply Finset.prod_eq_one
    intro b _
    exact pairWeight_differentBlock e g β hji a b
  · simp

end BinaryCoordinateSweeps.Signed

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_TensorBounds_SignedBlocks
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Signed
open Matrix Density

variable {I A : Type*} [Fintype I] [LinearOrder I]
  [Fintype A] [DecidableEq A] {n : I → ℕ} {N : ℕ}

lemma signC_blocks (e : (Σₗ i, Fin (n i)) ≃o Fin N)
    (g : ∀i, Equiv.Perm (Fin (n i))) (β : Fin N → Bool) :
    signC β (blockPerm e g) = ∏i, signC (fun a => β (e (toLex ⟨i,a⟩))) (g i) := by
  simp only [signC,koszulSign_blocks,Units.coe_prod,Int.cast_prod]

omit [Fintype I] [Fintype A] [DecidableEq A] in
lemma blockWords_comp (e : (Σₗ i, Fin (n i)) ≃o Fin N)
    (g : ∀i, Equiv.Perm (Fin (n i))) (x : Fin N → A) :
    blockWords e (x ∘ blockPerm e g) = fun i => (blockWords e x i) ∘ g i := by
  funext i a
  simp

theorem actionMatrix_blocks (e : (Σₗ i, Fin (n i)) ≃o Fin N)
    (g : ∀i, Equiv.Perm (Fin (n i))) (p : A → Bool) :
    LinearMap.toMatrix' (act p (blockPerm e g)) =
      (piTensorMatrices (fun i => LinearMap.toMatrix' (act p (g i)))).submatrix
        (blockWords e) (blockWords e) := by
  ext x y
  change LinearMap.toMatrix' (act p (blockPerm e g)) x y =
    ∏i, LinearMap.toMatrix' (act p (g i)) (blockWords e x i) (blockWords e y i)
  simp only [actionMatrix_apply]
  have he : x ∘ blockPerm e g=y ↔ ∀i, (blockWords e x i) ∘ g i=blockWords e y i := by
    rw [← (blockWords e).injective.eq_iff,blockWords_comp]
    exact funext_iff
  by_cases h : x ∘ blockPerm e g=y
  · rw [ite_eq_left h,blockPerm_inv,signC_blocks]
    apply Finset.prod_congr rfl
    intro i _
    rw [ite_eq_left (he.mp h i)]
    rfl
  · rw [ite_eq_right h]
    have hh := h
    rw [he] at hh
    push Not at hh
    obtain ⟨i,hi⟩ := hh
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

end BinaryCoordinateSweeps.Signed

end

open scoped BigOperators Classical ComplexOrder MonoidAlgebra
open Matrix

namespace BinaryCoordinateSweeps.Signed
open Density Irrep Representation

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

omit [Fintype A] in
lemma vacuumDensity_psd : (vacuumDensity (A:=A)).PosSemidef := by
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro a
  split <;> norm_num

lemma vacuumDensity_trace : (vacuumDensity (A:=A)).trace=1 := by
  simp [vacuumDensity,Matrix.trace,Matrix.diag]

omit [Fintype A] in
lemma vacuumDensity_even (p : A → Bool) (a b : A) (h : p a ≠ p b) :
    vacuumDensity a b=0 := by
  have hh : a≠b := fun he => h (congrArg p he)
  simp [vacuumDensity,hh]

lemma localDensity_psd (p : A → Bool) (n : ℕ) (u : LocalDensityIndex p n) :
    (localDensity p n u).PosSemidef := by
  unfold localDensity
  split
  · exact vacuumDensity_psd
  · exact reducedPhaseDensity_psd _ _ _ _

lemma localDensity_trace (p : A → Bool) (n : ℕ) (u : LocalDensityIndex p n) :
    (localDensity p n u).trace=1 := by
  unfold localDensity
  split
  · exact vacuumDensity_trace
  · exact reducedPhaseDensity_trace n (by omega) _ (matchedEmbedding_injective p) _ _

lemma localDensity_even (p : A → Bool) (n : ℕ) (u : LocalDensityIndex p n)
    (a b : A) (h : p a ≠ p b) : localDensity p n u a b=0 := by
  unfold localDensity
  split
  · exact vacuumDensity_even p a b h
  · exact reducedPhaseDensity_even n p p (matchedEmbedding p) (fun k => k.property) _ _ a b h

omit [Nonempty A] in
lemma localDensityIndex_card (p : A → Bool) (n : ℕ) :
    Fintype.card (LocalDensityIndex p n) ≤ (n+1)^(2*(Fintype.card A)^2) := by
  have hc : Fintype.card (MatchedPair p) ≤ (Fintype.card A)^2 := by
    simpa only [Fintype.card_prod,pow_two] using Fintype.card_le_of_injective
      (matchedEmbedding p) (matchedEmbedding_injective p)
  calc
    _ = Fintype.card (WordType (MatchedPair p) n) * (n+1)^Fintype.card (MatchedPair p) := by
      rw [Fintype.card_prod,Fintype.card_fun,ZMod.card]
    _ ≤ (n+1)^Fintype.card (MatchedPair p) * (n+1)^Fintype.card (MatchedPair p) :=
      Nat.mul_le_mul_right _ (by simpa only [Fintype.card_coe] using card_types_le (A:=MatchedPair p) n)
    _ = (n+1)^(2*Fintype.card (MatchedPair p)) := by rw [two_mul,pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left 2 hc)

lemma localDensityIndex_nonempty (p : A → Bool) (n : ℕ) : Nonempty (LocalDensityIndex p n) := by
  let a : A := Classical.choice inferInstance
  exact ⟨wordType n (fun _ => ⟨(a,a),rfl⟩),fun _ => 0⟩

lemma projection_complement_psd {I : Type*} [Fintype I] [DecidableEq I]
    (P : Matrix I I ℂ) (hP : P.IsHermitian) (hPP : P*P=P) : (1-P).PosSemidef := by
  have he : (1-P).conjTranspose*(1-P)=1-P := by
    simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_one,hP.eq,mul_sub,sub_mul,
      one_mul,mul_one,hPP]
    abel
  rw [← he]
  exact Matrix.posSemidef_conjTranspose_mul_self _

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem local_type_density_domination (p : A → Bool) (n : ℕ)
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) [ρ.IsIrreducible] :
    (((Module.finrank ℂ V : ℂ)*(n+1 : ℂ)^(2*(Fintype.card A)^2)) •
      (∑u : LocalDensityIndex p n, matrixTensorPower n (localDensity p n u)) -
      isotypicProjection p ρ).PosSemidef := by
  by_cases hn : n=0
  · subst n
    have : Nonempty (LocalDensityIndex p 0) := localDensityIndex_nonempty p 0
    have hc : Fintype.card (LocalDensityIndex p 0)=1 := le_antisymm
      (by simp) (Fintype.card_pos_iff.mpr inferInstance)
    have he (u : LocalDensityIndex p 0) : matrixTensorPower 0 (localDensity p 0 u)=1 := by
      ext x y
      simp [matrixTensorPower,Matrix.one_apply,Subsingleton.elim x y]
    simp only [he,Finset.sum_const,Finset.card_univ,hc,one_nsmul,Nat.cast_zero,zero_add,one_pow,mul_one]
    have : Nontrivial ρ.asModule := IsSimpleModule.nontrivial ℂ[Equiv.Perm (Fin 0)] ρ.asModule
    have hd : (1:ℂ) ≤ (Module.finrank ℂ V : ℂ) := by
      have hh : 0 < Module.finrank ℂ V := by
        rw [← ρ.asModuleEquiv.finrank_eq]
        exact Module.finrank_pos
      exact_mod_cast hh
    have h := (Matrix.PosSemidef.one : (1 : Matrix (Fin 0 → A) (Fin 0 → A) ℂ).PosSemidef).smul
      (sub_nonneg.mpr hd)
    have hp := projection_complement_psd (isotypicProjection p ρ)
      (isotypicProjection_psd p ρ).isHermitian (projectionMatrix_idempotent _)
    convert h.add hp using 1
    simp only [sub_smul,one_smul]
    abel
  · simpa only [localDensity,ite_eq_right hn,Fintype.sum_prod_type] using
      isotypic_density_domination n (by omega) p ρ

end BinaryCoordinateSweeps.Signed

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_TensorBounds_BlockTypes
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical ComplexOrder
open Matrix

namespace BinaryCoordinateSweeps.Signed
open Density Irrep Representation

variable {I A : Type*} [Fintype I] [LinearOrder I]
  [Fintype A] [DecidableEq A] {n : I → ℕ} {N : ℕ}
  {V : I → Type*} [∀i, NormedAddCommGroup (V i)]
  [∀i, InnerProductSpace ℂ (V i)] [∀i, FiniteDimensional ℂ (V i)]

lemma submatrix_sum_eq {U X Y : Type*} [Fintype U]
    (M : U → Matrix X X ℂ) (f : Y → X) :
    (∑u, M u).submatrix f f=∑u, (M u).submatrix f f := by
  ext x y
  simp [Matrix.submatrix,Matrix.sum_apply]

omit [∀i, FiniteDimensional ℂ (V i)] in
lemma blockProjection_psd (e : (Σₗ i, Fin (n i)) ≃o Fin N) (p : A → Bool)
    (ρ : ∀i, Representation ℂ (Equiv.Perm (Fin (n i))) (V i)) :
    (blockProjection e p ρ).PosSemidef :=
  (piTensorMatrices_psd _ (fun i => isotypicProjection_psd p (ρ i))).submatrix _

omit [∀i, FiniteDimensional ℂ (V i)] in
lemma blockProjection_idempotent (e : (Σₗ i, Fin (n i)) ≃o Fin N) (p : A → Bool)
    (ρ : ∀i, Representation ℂ (Equiv.Perm (Fin (n i))) (V i)) :
    blockProjection e p ρ*blockProjection e p ρ=blockProjection e p ρ := by
  unfold blockProjection
  rw [Matrix.submatrix_mul_equiv,piTensorMatrices_mul]
  have hh : (fun i => isotypicProjection p (ρ i)*isotypicProjection p (ρ i)) =
      (fun i => isotypicProjection p (ρ i)) := by
    funext i
    exact projectionMatrix_idempotent (hilbertSubspace (isotypicSpan (ρ i) (tensorRep p (n i))))
  rw [hh]

omit [Fintype A] [DecidableEq A] in
lemma block_tensor_density (e : (Σₗ i, Fin (n i)) ≃o Fin N)
    (r : I → Matrix A A ℂ) :
    (piTensorMatrices (fun i => matrixTensorPower (n i) (r i))).submatrix
      (blockWords e) (blockWords e) = tensorMatrices (fun t => r (ofLex (e.symm t)).1) := by
  ext x y
  change (∏i, ∏a : Fin (n i), r i (x (e (toLex ⟨i,a⟩))) (y (e (toLex ⟨i,a⟩)))) =
    ∏t, r (ofLex (e.symm t)).1 (x t) (y t)
  calc
    _ = ∏t : Σ i, Fin (n i), r t.1 (x (e (toLex t))) (y (e (toLex t))) := (Fintype.prod_sigma _).symm
    _ = _ := by
      have hh := (toLex.trans e.toEquiv).prod_comp (fun t => r (ofLex (e.symm t)).1 (x t) (y t))
      change (∏t : Σ i, Fin (n i), r (ofLex (e.symm (e (toLex t)))).1 (x (e (toLex t))) (y (e (toLex t)))) = _ at hh
      simpa only [OrderIso.symm_apply_apply, ofLex_toLex] using hh

lemma block_density_domination [Nonempty A] (e : (Σₗ i, Fin (n i)) ≃o Fin N)
    (p : A → Bool) (ρ : ∀i, Representation ℂ (Equiv.Perm (Fin (n i))) (V i))
    [∀i, (ρ i).IsIrreducible] :
    (((∏i, (Module.finrank ℂ (V i):ℂ)*(n i+1:ℂ)^(2*(Fintype.card A)^2))) •
      (∑u : ∀i, LocalDensityIndex p (n i),
        tensorMatrices (fun t => localDensity p (n (ofLex (e.symm t)).1) (u (ofLex (e.symm t)).1))) -
      blockProjection e p ρ).PosSemidef := by
  have h := piTensor_density_domination (fun i => isotypicProjection p (ρ i))
    (fun i u => matrixTensorPower (n i) (localDensity p (n i) u))
    (fun i => (Module.finrank ℂ (V i):ℂ)*(n i+1:ℂ)^(2*(Fintype.card A)^2))
    (fun i => isotypicProjection_psd p (ρ i))
    (fun i => local_type_density_domination p (n i) (ρ i))
  have hh := h.submatrix (blockWords (A:=A) e)
  simpa only [Matrix.submatrix_sub,Matrix.submatrix_smul,Pi.sub_apply,Pi.smul_apply,submatrix_sum_eq,
    block_tensor_density,blockProjection] using hh

omit [∀i, FiniteDimensional ℂ (V i)] in
lemma blockProjection_central (e : (Σₗ i, Fin (n i)) ≃o Fin N)
    (p : A → Bool) (ρ : ∀i, Representation ℂ (Equiv.Perm (Fin (n i))) (V i))
    (M : Matrix (Fin N → A) (Fin N → A) ℂ)
    (hc : ∀g : ∀i, Equiv.Perm (Fin (n i)),
      M*actionMatrix p (blockPerm e g)=actionMatrix p (blockPerm e g)*M) :
    M*blockProjection e p ρ=blockProjection e p ρ*M := by
  let E := Matrix.reindexAlgEquiv ℂ ℂ (blockWords (A:=A) e)
  have he (g : ∀i, Equiv.Perm (Fin (n i))) :
      E (actionMatrix p (blockPerm e g))=piTensorMatrices (fun i => actionMatrix p (g i)) := by
    change E (LinearMap.toMatrix' (act p (blockPerm e g)))=_
    rw [actionMatrix_blocks]
    ext x y
    change (piTensorMatrices (fun i => actionMatrix p (g i))) (blockWords e ((blockWords e).symm x)) (blockWords e ((blockWords e).symm y)) = _
    simp
  have hP : E (blockProjection e p ρ)=piTensorMatrices (fun i => isotypicProjection p (ρ i)) := by
    ext x y
    change (piTensorMatrices (fun i => isotypicProjection p (ρ i))) (blockWords e ((blockWords e).symm x)) (blockWords e ((blockWords e).symm y)) = _
    simp
  have hsingle (i : I) (g : Equiv.Perm (Fin (n i))) :
      piTensorMatrices (fun j => actionMatrix p (Pi.mulSingle (M:=fun j => Equiv.Perm (Fin (n j))) i g j)) =
        siteMatrix i (actionMatrix p g) := by
    have hs := siteMatrix_eq_mask (i:=i) (P:=fun j => actionMatrix p (Pi.mulSingle (M:=fun j => Equiv.Perm (Fin (n j))) i g j))
    simp only [Pi.mulSingle_eq_same] at hs
    rw [hs]
    congr 1
    funext j
    by_cases hji : j=i
    · subst j; simp
    · simp [Pi.mulSingle_eq_of_ne hji,actionMatrix_one]
  apply E.injective
  simp only [map_mul,hP]
  apply piTensor_centrality (fun i g => actionMatrix p g) (fun i => isotypicProjection p (ρ i))
    (fun i => typeProjection_central p (ρ i))
  intro i g
  have hh := congrArg E (hc (Pi.mulSingle (M:=fun j => Equiv.Perm (Fin (n j))) i g))
  simpa only [map_mul,he,hsingle] using hh

end BinaryCoordinateSweeps.Signed

end

open scoped BigOperators Classical ComplexOrder
open Matrix

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_GroupedTypes
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical ComplexOrder
open Matrix

namespace BinaryCoordinateSweeps.Signed
open Density Irrep Representation

variable {I A : Type*} [Fintype I] [LinearOrder I]
  [Fintype A] [DecidableEq A] {n : I → ℕ} {N : ℕ}
  {V : I → Type*} [∀i, NormedAddCommGroup (V i)]
  [∀i, InnerProductSpace ℂ (V i)] [∀i, FiniteDimensional ℂ (V i)]

omit [∀i, FiniteDimensional ℂ (V i)] in
lemma groupedProjection_psd (e : (Σₗ i, Fin (n i)) ≃o Fin N) (g : Equiv.Perm (Fin N))
    (p : A → Bool) (ρ : ∀i, Representation ℂ (Equiv.Perm (Fin (n i))) (V i)) :
    (groupedProjection e g p ρ).PosSemidef :=
  signedConj_psd p g _ (blockProjection_psd e p ρ)

omit [∀i, FiniteDimensional ℂ (V i)] in
lemma groupedProjection_idempotent (e : (Σₗ i, Fin (n i)) ≃o Fin N) (g : Equiv.Perm (Fin N))
    (p : A → Bool) (ρ : ∀i, Representation ℂ (Equiv.Perm (Fin (n i))) (V i)) :
    groupedProjection e g p ρ*groupedProjection e g p ρ=groupedProjection e g p ρ := by
  unfold groupedProjection
  rw [← signedConj_mul,blockProjection_idempotent]

omit [∀i, FiniteDimensional ℂ (V i)] in
lemma groupedProjection_commutes (e : (Σₗ i, Fin (n i)) ≃o Fin N) (g : Equiv.Perm (Fin N))
    (p : A → Bool) (ρ : ∀i, Representation ℂ (Equiv.Perm (Fin (n i))) (V i))
    (M : Matrix (Fin N → A) (Fin N → A) ℂ) (hM : Invariant p M) :
    M*groupedProjection e g p ρ=groupedProjection e g p ρ*M := by
  apply signedConj_commutes p g M _ (invariant_matrix_commutes p M hM g)
  apply blockProjection_central e p ρ
  intro h
  exact invariant_matrix_commutes p M hM (blockPerm e h)

lemma grouped_density_domination [Nonempty A] (e : (Σₗ i, Fin (n i)) ≃o Fin N)
    (g : Equiv.Perm (Fin N)) (p : A → Bool)
    (ρ : ∀i, Representation ℂ (Equiv.Perm (Fin (n i))) (V i))
    [∀i, (ρ i).IsIrreducible] :
    (((∏i, (Module.finrank ℂ (V i):ℂ)*(n i+1:ℂ)^(2*(Fintype.card A)^2))) •
      (∑u : ∀i, LocalDensityIndex p (n i),
        tensorMatrices (fun t => localDensity p (n (groupOf e g t)) (u (groupOf e g t)))) -
      groupedProjection e g p ρ).PosSemidef := by
  have h := signedConj_psd p g _ (block_density_domination e p ρ)
  rw [signedConj_sub_smul_sum] at h
  have he (u : ∀i, LocalDensityIndex p (n i)) :
      signedConj p g (tensorMatrices (fun t => localDensity p (n (ofLex (e.symm t)).1) (u (ofLex (e.symm t)).1))) =
      tensorMatrices (fun t => localDensity p (n (groupOf e g t)) (u (groupOf e g t))) := by
    exact even_tensor_covariance p g _ (fun t => localDensity_even p _ _)
  simpa only [he,groupedProjection] using h

lemma grouped_density_card_bound (p : A → Bool) :
    Fintype.card (∀i, LocalDensityIndex p (n i)) ≤ ∏i, (n i+1)^(2*(Fintype.card A)^2) := by
  rw [Fintype.card_pi]
  exact Finset.prod_le_prod' (fun i _ => localDensityIndex_card p (n i))

end BinaryCoordinateSweeps.Signed

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_MatrixBounds_MatrixRegularize
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {A I : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype I] [Nonempty I]

omit [Fintype A] [DecidableEq A] [Nonempty A] [Nonempty I] in
lemma meanDensity_psd (r : I → Matrix A A ℂ) (hr : ∀ i, (r i).PosSemidef) :
    (meanDensity r).PosSemidef := by
  exact (Matrix.posSemidef_sum _ (fun i _ => hr i)).smul (by positivity)

omit [DecidableEq A] [Nonempty A] in
lemma meanDensity_trace (r : I → Matrix A A ℂ) (ht : ∀ i, (r i).trace = 1) :
    (meanDensity r).trace = 1 := by
  simp [meanDensity,Matrix.trace_sum,Matrix.trace_smul,ht,
    ne_of_gt (Fintype.card_pos : 0 < Fintype.card I)]

lemma regularizedMean_trace (r : I → Matrix A A ℂ) (ht : ∀ i, (r i).trace = 1) (ε : ℝ) :
    (regularizedMean r ε).trace = 1 := by
  simp [regularizedMean,Matrix.trace_smul,meanDensity_trace r ht,Matrix.trace_one,
    ne_of_gt (Fintype.card_pos : 0 < Fintype.card A)]

omit [Nonempty I] in
lemma regularizedMean_posDef (r : I → Matrix A A ℂ) (hr : ∀ i, (r i).PosSemidef)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) : (regularizedMean r ε).PosDef := by
  rw [regularizedMean,add_comm]
  apply Matrix.PosDef.add_posSemidef
  · apply Matrix.PosDef.one.smul
    exact_mod_cast div_pos hε (Nat.cast_pos.mpr (Fintype.card_pos : 0 < Fintype.card A))
  · exact (meanDensity_psd r hr).smul (by exact_mod_cast sub_nonneg.mpr hε1)

omit [Nonempty A] [Nonempty I] in
lemma regularizedMean_even (r : I → Matrix A A ℂ) (p : A → Bool)
    (he : ∀ i a b, p a ≠ p b → r i a b = 0) (ε : ℝ) :
    ∀ a b, p a ≠ p b → regularizedMean r ε a b = 0 := by
  intro a b hab
  have hn : a ≠ b := fun h => hab (congrArg p h)
  simp [regularizedMean,meanDensity,Matrix.smul_apply,Matrix.sum_apply,he,hab,hn]

omit [Nonempty A] in
lemma whitened_column_budget (r : I → Matrix A A ℂ) (v C : Matrix A A ℂ)
    (_hr : ∀ i, (r i).PosSemidef) (hv : v.PosSemidef) (htv : v.trace = 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hC : C.IsHermitian)
    (hCMC : C * regularizedMean r ε * C = 1) :
    (1-ε) * (∑ i, (C * r i * C * v).trace.re) ≤ Fintype.card I := by
  have hd : (regularizedMean r ε - (1-ε:ℂ) • meanDensity r).PosSemidef := by
    simp only [regularizedMean,add_sub_cancel_left]
    exact Matrix.PosSemidef.one.smul (by exact_mod_cast div_nonneg hε (Nat.cast_nonneg (Fintype.card A)))
  have hc := hd.mul_mul_conjTranspose_same C
  rw [hC.eq,Matrix.mul_sub,Matrix.sub_mul,hCMC,Matrix.mul_smul,Matrix.smul_mul] at hc
  have ht := trace_product_re_nonneg hc hv
  rw [Matrix.sub_mul,Matrix.one_mul,Matrix.smul_mul,Matrix.trace_sub,Matrix.trace_smul,htv] at ht
  simp only [Complex.sub_re,Complex.one_re,smul_eq_mul,Complex.mul_re,Complex.sub_im,Complex.one_im,Complex.ofReal_re,Complex.ofReal_im,sub_zero,zero_mul] at ht
  have hn : (Fintype.card I : ℝ) > 0 := Nat.cast_pos.mpr Fintype.card_pos
  have hs : (C * meanDensity r * C * v).trace.re =
      (Fintype.card I : ℝ)⁻¹ * ∑ i, (C * r i * C * v).trace.re := by
    simp [meanDensity,Matrix.mul_sum,Matrix.sum_mul,
      Matrix.trace_sum,Matrix.trace_smul,Complex.mul_re]
  rw [hs] at ht
  have := mul_nonneg hn.le ht
  field_simp at this
  nlinarith

end BinaryCoordinateSweeps.Density

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_MatrixBounds_SchattenBounds
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace BinaryCoordinateSweeps.TraceHolder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma schatten_nonneg (q : ℕ) (A : M ι) : 0 ≤ schatten q A :=
  Real.rpow_nonneg (matrixMoment_nonneg _ _) _

lemma schatten_pow {q : ℕ} (hq : 0 < q) (A : M ι) :
    schatten q A ^ (2*q) = matrixMoment q A := by
  exact Real.rpow_inv_natCast_pow (matrixMoment_nonneg _ _) (by omega : 2*q ≠ 0)

lemma op_norm_le_schatten {q : ℕ} (hq : 0 < q) (A : M ι) : ‖A‖ ≤ schatten q A := by
  obtain ⟨U,V,s,hs,hU,hA,hg⟩ := exists_partial_svd A
  have ht := matrixMoment_of_svd A q V s hg
  have hd : ‖diagReal s‖ ≤ schatten q A := by
    rw [diagReal, Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (schatten_nonneg _ _)).mpr
    intro i
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hs i)]
    have hi : s i^(2*q) ≤ matrixMoment q A := by
      rw [ht]
      exact Finset.single_le_sum (fun j _ => pow_nonneg (hs j) _) (Finset.mem_univ i)
    have h := Real.rpow_le_rpow (pow_nonneg (hs i) _) hi
      (show 0 ≤ (((2*q : ℕ) : ℝ)⁻¹) by positivity)
    rw [Real.pow_rpow_inv_natCast (hs i) (by omega : 2*q ≠ 0)] at h
    exact h
  calc
    ‖A‖ = ‖U * diagReal s * star (V : M ι)‖ := congrArg norm hA
    _ ≤ (‖U‖ * ‖diagReal s‖) * ‖star (V : M ι)‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1 * schatten q A) * 1 := by
      apply mul_le_mul
      · exact mul_le_mul hU hd (norm_nonneg _) zero_le_one
      · simpa only [norm_star] using unitary_norm_le_one V
      · exact norm_nonneg _
      · exact mul_nonneg zero_le_one (schatten_nonneg _ _)
    _ = _ := by ring

end BinaryCoordinateSweeps.TraceHolder

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_GroupedMoments
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical ComplexOrder MatrixOrder
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {A I J : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J] [DecidableEq J]

omit [Nonempty A] in
theorem whitened_board_budget {n : ℕ} (e : Fin n ↪ I × J)
    (r : I → Matrix A A ℂ) (v : J → Matrix A A ℂ) (C : Matrix A A ℂ)
    (hr : ∀ i, (r i).PosSemidef) (hv : ∀ j, (v j).PosSemidef)
    (htv : ∀ j, (v j).trace = 1) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hC : C.IsHermitian) (hCMC : C * regularizedMean r ε * C = 1) :
    (1-ε)^n * (tensorMatrices (fun t : Fin n => C * r (e t).1 * C) *
      tensorMatrices (fun t : Fin n => v (e t).2)).trace.re ≤
      Real.exp (Fintype.card I * Fintype.card J - (n : ℝ)) := by
  let x : I → J → ℝ := fun i j => (C*r i*C*v j).trace.re
  have hp (i : I) : (C*r i*C).PosSemidef := by
    simpa only [hC.eq] using (hr i).mul_mul_conjTranspose_same C
  have hx (i : I) (j : J) : 0 ≤ x i j := trace_product_re_nonneg (hp i) (hv j)
  have hs (j : J) : ∑ i, (1-ε)*x i j ≤ Fintype.card I := by
    rw [← Finset.mul_sum]
    exact whitened_column_budget r (v j) C hr (hv j) (htv j) hε hC hCMC
  have he := rectangular_product_holes (Finset.univ.map e) (fun i j => (1-ε)*x i j)
    (fun i j => mul_nonneg (sub_nonneg.mpr hε1) (hx i j)) hs
  rw [Finset.prod_map,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,
    Fintype.card_fin,Finset.card_map,Finset.card_univ,Fintype.card_fin] at he
  rw [tensor_product_trace_re _ _ (fun t => hp (e t).1) (fun t => hv (e t).2)]
  exact he

end BinaryCoordinateSweeps.Density

end

open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma matrix_norm_sq_le_trace (M : Matrix I I ℂ) : ‖M‖^2 ≤ (M.conjTranspose*M).trace.re := by
  have h := pow_le_pow_left₀ (norm_nonneg M) (TraceHolder.op_norm_le_schatten (q:=1) (by omega) M) 2
  have he := TraceHolder.schatten_pow (q:=1) (by omega) M
  simpa only [Nat.mul_one,he,TraceHolder.matrixMoment,pow_one,Matrix.star_eq_conjTranspose] using h

lemma projection_overlap_norm_trace (R Q P : Matrix I I ℂ)
    (hR : R.IsHermitian) (hQ : Q.IsHermitian) (hP : P.IsHermitian)
    (hRR : R*R=R) (hQQ : Q*Q=Q) (hPP : P*P=P) (hPQ : P*Q=Q*P) :
    ‖Q*P*R‖^2 ≤ (R*Q*P).trace.re := by
  have h := matrix_norm_sq_le_trace (Q*P*R)
  have he : ((Q*P*R).conjTranspose*(Q*P*R)).trace = (R*Q*P).trace := by
    simp only [Matrix.conjTranspose_mul,hR.eq,hQ.eq,hP.eq]
    calc
      _ = (R*(P*(Q*Q)*P)*R).trace := by congr 1; noncomm_ring
      _ = (R*(Q*P)*R).trace := by rw [hQQ,hPQ,mul_assoc Q P P,hPP]
      _ = (R*R*(Q*P)).trace := by rw [Matrix.trace_mul_cycle]
      _ = _ := by rw [hRR,mul_assoc]
  rw [he] at h
  exact h

omit [DecidableEq I] in
lemma commuting_projection_product_psd (P Q : Matrix I I ℂ)
    (hP : P.PosSemidef) (hQ : Q.IsHermitian) (hQQ : Q*Q=Q) (hPQ : P*Q=Q*P) :
    (Q*P).PosSemidef := by
  have h := hP.mul_mul_conjTranspose_same Q
  rw [hQ.eq,mul_assoc, hPQ,← mul_assoc,hQQ] at h
  exact h

omit [DecidableEq I] in
lemma compress_whitening_cap (P Q C : Matrix I I ℂ) (d : ℂ)
    (hQ : Q.IsHermitian) (hQQ : Q*Q=Q) (hPQ : P*Q=Q*P) (hCQ : C*Q=Q*C)
    (hc : (C*C-d•P).PosSemidef) : (C*Q*C-d•(Q*P)).PosSemidef := by
  have h := hc.mul_mul_conjTranspose_same Q
  rw [hQ.eq,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul] at h
  have he1 : Q*(C*C)*Q = C*Q*C := by
    calc
      _ = (Q*C)*(C*Q) := by noncomm_ring
      _ = (C*Q)*(Q*C) := by rw [hCQ,← hCQ]
      _ = C*(Q*Q)*C := by noncomm_ring
      _ = _ := by rw [hQQ]
  have he2 : Q*P*Q = Q*P := by rw [mul_assoc,hPQ,← mul_assoc,hQQ]
  rwa [he1,he2] at h

end BinaryCoordinateSweeps.Density

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_MatrixBounds_TraceDensityComparison
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical ComplexOrder MatrixOrder
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {I W : Type*} [Fintype I] [DecidableEq I] [Fintype W]

omit [DecidableEq I] in
lemma trace_re_real_smul (a : ℝ) (X : Matrix I I ℂ) :
    ((a : ℂ) • X).trace.re = a * X.trace.re := by
  simp [Matrix.trace_smul,Complex.mul_re]

lemma trace_density_whitening (R Q P C : Matrix I I ℂ) (d a : ℝ)
    (V : W → Matrix I I ℂ) (hR : R.PosSemidef) (hC : C.IsHermitian)
    (hcap : (C*Q*C-(d:ℂ)•(Q*P)).PosSemidef)
    (hdom : ((a:ℂ)•∑w, V w-Q).PosSemidef) :
    d*(R*Q*P).trace.re ≤ a*∑w, (C*R*C*V w).trace.re := by
  have h1 := trace_product_re_mono hR hcap
  rw [Matrix.mul_smul,trace_re_real_smul,← mul_assoc R Q P] at h1
  have h2 := hdom.mul_mul_conjTranspose_same C
  rw [hC.eq,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,
    Matrix.mul_sum,Matrix.sum_mul] at h2
  have h3 := trace_product_re_mono hR h2
  rw [Matrix.mul_smul,trace_re_real_smul,Matrix.mul_sum,Matrix.trace_sum,
    Complex.re_sum] at h3
  have he (w : W) : (R*(C*V w*C)).trace = (C*R*C*V w).trace := by
    rw [← mul_assoc R (C*V w) C,Matrix.trace_mul_cycle]
    congr 1
    noncomm_ring
  simp only [he] at h3
  exact h1.trans h3

lemma trace_right_density_domination (R S : Matrix I I ℂ) (a : ℝ)
    (U : W → Matrix I I ℂ) (hS : S.PosSemidef)
    (hdom : ((a:ℂ)•∑w, U w-R).PosSemidef) :
    (R*S).trace.re ≤ a * ∑w, (U w*S).trace.re := by
  have ht := trace_product_re_mono hS hdom
  rw [Matrix.mul_smul,trace_re_real_smul,Matrix.mul_sum,Matrix.trace_sum,Complex.re_sum,
    Matrix.trace_mul_comm S R] at ht
  simpa only [Matrix.trace_mul_comm S] using ht

end BinaryCoordinateSweeps.Density

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_BoardOverlap
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace BinaryCoordinateSweeps.Signed
open Density Irrep Representation

variable {A I J U W V : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J] [DecidableEq J]
  [Fintype U] [Fintype W]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

omit [FiniteDimensional ℂ V] in
theorem regularized_board_overlap {n : ℕ} (e : Fin n ↪ I × J) (p : A → Bool)
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) [ρ.IsIrreducible]
    (R Q : Matrix (Fin n → A) (Fin n → A) ℂ)
    (hR : R.IsHermitian) (hQ : Q.IsHermitian) (hRR : R*R=R) (hQQ : Q*Q=Q)
    (hPQ : isotypicProjection p ρ * Q = Q * isotypicProjection p ρ)
    (hCQ : ∀ M : Matrix A A ℂ, M.PosSemidef →
      (∀ a b, p a ≠ p b → M a b = 0) → matrixTensorPower n M * Q = Q * matrixTensorPower n M)
    (r : U → I → Matrix A A ℂ) (v : W → J → Matrix A A ℂ)
    (hr : ∀ u i, (r u i).PosSemidef) (hv : ∀ w j, (v w j).PosSemidef)
    (htr : ∀ u i, (r u i).trace=1) (htv : ∀ w j, (v w j).trace=1)
    (her : ∀ u i a b, p a ≠ p b → r u i a b=0)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hdr : ((a:ℂ) • ∑u, tensorMatrices (fun t : Fin n => r u (e t).1)-R).PosSemidef)
    (hdv : ((b:ℂ) • ∑w, tensorMatrices (fun t : Fin n => v w (e t).2)-Q).PosSemidef)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (Module.finrank ℂ V : ℝ) * (1-ε)^n * ‖Q * isotypicProjection p ρ * R‖^2 ≤
      a*b*Fintype.card U*Fintype.card W*
        Real.exp (Fintype.card I * Fintype.card J - (n : ℝ)) := by
  let P := isotypicProjection p ρ
  let d : ℝ := Module.finrank ℂ V
  let L : ℝ := (1-ε)^n
  let E := Real.exp (Fintype.card I * Fintype.card J - (n : ℝ))
  let T (u : U) := tensorMatrices (fun t : Fin n => r u (e t).1)
  let Z (w : W) := tensorMatrices (fun t : Fin n => v w (e t).2)
  have hL : 0 ≤ L := pow_nonneg (sub_nonneg.mpr hε1) n
  have hd : 0 ≤ d := Nat.cast_nonneg _
  have hP : P.PosSemidef := isotypicProjection_psd p ρ
  have hPP : P*P=P := projectionMatrix_idempotent _
  have hn := projection_overlap_norm_trace R Q P hR hQ hP.isHermitian hRR hQQ hPP hPQ
  have hQP := commuting_projection_product_psd P Q hP hQ hQQ hPQ
  have hrow := trace_right_density_domination R (Q*P) a T hQP hdr
  rw [← mul_assoc R Q P] at hrow
  have hlocal (u : U) : L * (d * (T u*Q*P).trace.re) ≤ b*(Fintype.card W*E) := by
    let M := regularizedMean (r u) ε
    have hM : M.PosDef := regularizedMean_posDef (r u) (hr u) hε hε1
    have heM := regularizedMean_even (r u) p (her u) ε
    obtain ⟨B,C,hB,hC,hBB,hBC,hCB,heB,heC⟩ := exists_even_whitening p M hM heM
    let H := matrixTensorPower n C
    have hH : H.PosSemidef := tensorMatrices_psd _ (fun _ => hC)
    have hcap := signed_tensor_whitening p ρ M B C hB hC hBB hBC
      (regularizedMean_trace (r u) (htr u) ε) heM heC
    change (H.conjTranspose*H-(d:ℂ)•P).PosSemidef at hcap
    rw [hH.isHermitian.eq] at hcap
    have hcomp := compress_whitening_cap P Q H (d:ℂ) hQ hQQ hPQ (hCQ C hC heC) hcap
    have htu : (T u).PosSemidef := tensorMatrices_psd _ (fun t => hr u (e t).1)
    have ht := trace_density_whitening (T u) Q P H d b Z htu hH.isHermitian hcomp hdv
    have hCMC : C * regularizedMean (r u) ε * C = 1 := by
      change C * M * C = 1
      rw [← hBB,← mul_assoc C B B,hCB,one_mul,hBC]
    have hz (w : W) : L * (H*T u*H*Z w).trace.re ≤ E := by
      have hh := whitened_board_budget e (r u) (v w) C (hr u) (hv w) (htv w)
        hε.le hε1 hC.isHermitian hCMC
      change L * (tensorMatrices (fun _ : Fin n => C) * T u *
        tensorMatrices (fun _ : Fin n => C) * Z w).trace.re ≤ E
      simpa only [T,Z,L,E,tensorMatrices_mul] using hh
    calc
      L*(d*(T u*Q*P).trace.re) ≤ L*(b*∑w, (H*T u*H*Z w).trace.re) :=
        mul_le_mul_of_nonneg_left ht hL
      _ = b*∑w, L*(H*T u*H*Z w).trace.re := by simp only [Finset.mul_sum]; congr 1; ring_nf
      _ ≤ b*∑w : W, E := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun w _ => hz w)) hb
      _ = b*(Fintype.card W*E) := by simp
  change d*L*‖Q*P*R‖^2 ≤ a*b*Fintype.card U*Fintype.card W*E
  calc
    _ ≤ d*L*(a*∑u, (T u*(Q*P)).trace.re) :=
      mul_le_mul_of_nonneg_left (hn.trans hrow) (mul_nonneg hd hL)
    _ = a*∑u, L*(d*(T u*Q*P).trace.re) := by
      simp only [← mul_assoc,Finset.mul_sum]
      ring_nf
    _ ≤ a*∑u : U, b*(Fintype.card W*E) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun u _ => hlocal u)) ha
    _ = _ := by simp; ring

omit [FiniteDimensional ℂ V] in
theorem board_overlap {n : ℕ} (e : Fin n ↪ I × J) (p : A → Bool)
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) [ρ.IsIrreducible]
    (R Q : Matrix (Fin n → A) (Fin n → A) ℂ)
    (hR : R.IsHermitian) (hQ : Q.IsHermitian) (hRR : R*R=R) (hQQ : Q*Q=Q)
    (hPQ : isotypicProjection p ρ * Q = Q * isotypicProjection p ρ)
    (hCQ : ∀ M : Matrix A A ℂ, M.PosSemidef →
      (∀ a b, p a ≠ p b → M a b = 0) → matrixTensorPower n M * Q = Q * matrixTensorPower n M)
    (r : U → I → Matrix A A ℂ) (v : W → J → Matrix A A ℂ)
    (hr : ∀ u i, (r u i).PosSemidef) (hv : ∀ w j, (v w j).PosSemidef)
    (htr : ∀ u i, (r u i).trace=1) (htv : ∀ w j, (v w j).trace=1)
    (her : ∀ u i a b, p a ≠ p b → r u i a b=0)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hdr : ((a:ℂ) • ∑u, tensorMatrices (fun t : Fin n => r u (e t).1)-R).PosSemidef)
    (hdv : ((b:ℂ) • ∑w, tensorMatrices (fun t : Fin n => v w (e t).2)-Q).PosSemidef)
    : (Module.finrank ℂ V : ℝ) * ‖Q * isotypicProjection p ρ * R‖^2 ≤
      a*b*Fintype.card U*Fintype.card W*
        Real.exp (Fintype.card I * Fintype.card J - (n : ℝ)) := by
  have hε1 : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0), ε < 1 :=
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
  have hbound : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),
      (Module.finrank ℂ V : ℝ) * (1-ε)^n * ‖Q*isotypicProjection p ρ*R‖^2 ≤
        a*b*Fintype.card U*Fintype.card W*
          Real.exp (Fintype.card I * Fintype.card J - (n : ℝ)) := by
    filter_upwards [self_mem_nhdsWithin,hε1] with ε hε hε1
    exact regularized_board_overlap e p ρ R Q hR hQ hRR hQQ hPQ hCQ r v hr hv
      htr htv her a b ha hb hdr hdv hε hε1.le
  apply le_of_tendsto _ hbound
  have ht : Filter.Tendsto (fun ε : ℝ => (Module.finrank ℂ V:ℝ)*(1-ε)^n*
      ‖Q*isotypicProjection p ρ*R‖^2) (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((Module.finrank ℂ V:ℝ)*(1-(0:ℝ))^n*‖Q*isotypicProjection p ρ*R‖^2)) := by
    exact (show Continuous (fun ε : ℝ => (Module.finrank ℂ V:ℝ)*(1-ε)^n*
      ‖Q*isotypicProjection p ρ*R‖^2) by fun_prop).continuousWithinAt.tendsto
  simpa using ht

end BinaryCoordinateSweeps.Signed

end

open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace BinaryCoordinateSweeps.Signed
open Density Irrep Representation

variable {A I J : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype I] [LinearOrder I] [Nonempty I] [Fintype J] [LinearOrder J]
  {nR : I → ℕ} {nC : J → ℕ} {N : ℕ}
  {VR : I → Type*} [∀i, NormedAddCommGroup (VR i)]
  [∀i, InnerProductSpace ℂ (VR i)] [∀i, FiniteDimensional ℂ (VR i)]
  {VC : J → Type*} [∀j, NormedAddCommGroup (VC j)]
  [∀j, InnerProductSpace ℂ (VC j)] [∀j, FiniteDimensional ℂ (VC j)]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

omit [FiniteDimensional ℂ V] in
theorem actual_board_overlap (board : Fin N ↪ I × J) (p : A → Bool)
    (eR : (Σₗ i, Fin (nR i)) ≃o Fin N) (eC : (Σₗ j, Fin (nC j)) ≃o Fin N)
    (gR gC : Equiv.Perm (Fin N))
    (hR : ∀t, groupOf eR gR t=(board t).1) (hC : ∀t, groupOf eC gC t=(board t).2)
    (ρ : Representation ℂ (Equiv.Perm (Fin N)) V) [ρ.IsIrreducible]
    (α : ∀i, Representation ℂ (Equiv.Perm (Fin (nR i))) (VR i)) [∀i, (α i).IsIrreducible]
    (β : ∀j, Representation ℂ (Equiv.Perm (Fin (nC j))) (VC j)) [∀j, (β j).IsIrreducible] :
    (Module.finrank ℂ V:ℝ)*
      ‖groupedProjection eC gC p β*isotypicProjection p ρ*groupedProjection eR gR p α‖^2 ≤
    (∏i, (Module.finrank ℂ (VR i):ℝ)*(nR i+1:ℝ)^(2*(Fintype.card A)^2))*
    (∏j, (Module.finrank ℂ (VC j):ℝ)*(nC j+1:ℝ)^(2*(Fintype.card A)^2))*
    Fintype.card (∀i, LocalDensityIndex p (nR i))*Fintype.card (∀j, LocalDensityIndex p (nC j))*
    Real.exp (Fintype.card I*Fintype.card J-(N:ℝ)) := by
  apply board_overlap board p ρ _ _
    (groupedProjection_psd eR gR p α).isHermitian
    (groupedProjection_psd eC gC p β).isHermitian
    (groupedProjection_idempotent eR gR p α)
    (groupedProjection_idempotent eC gC p β)
    (groupedProjection_commutes eC gC p β _ (isotypicProjection_invariant p ρ))
    (fun M _ he => groupedProjection_commutes eC gC p β _ (even_tensor_invariant p M he))
    (fun u i => localDensity p (nR i) (u i)) (fun w j => localDensity p (nC j) (w j))
    (fun u i => localDensity_psd p _ _) (fun w j => localDensity_psd p _ _)
    (fun u i => localDensity_trace p _ _) (fun w j => localDensity_trace p _ _)
    (fun u i => localDensity_even p _ _)
  · positivity
  · positivity
  · have h := grouped_density_domination eR gR p α
    rw [show groupOf eR gR = (fun t => (board t).1) from funext hR] at h
    simpa only [hR,Complex.ofReal_prod,Complex.ofReal_mul,Complex.ofReal_natCast,
      Complex.ofReal_pow,Complex.ofReal_add,Complex.ofReal_one] using h
  · have h := grouped_density_domination eC gC p β
    rw [show groupOf eC gC = (fun t => (board t).2) from funext hC] at h
    simpa only [hC,Complex.ofReal_prod,Complex.ofReal_mul,Complex.ofReal_natCast,
      Complex.ofReal_pow,Complex.ofReal_add,Complex.ofReal_one] using h

end BinaryCoordinateSweeps.Signed

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

lemma prod_pos_log_exp {I : Type*} [Fintype I] (d : I → ℝ) (hd : ∀i, 0<d i) :
    (∏i, d i)=Real.exp (∑i, Real.log (d i)) := by
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  exact (Real.exp_log (hd i)).symm

lemma natShift_pow_exp (n t : ℕ) :
    (n+1:ℝ)^t=Real.exp ((t:ℝ)*Real.log (n+1:ℝ)) := by
  rw [Real.exp_nat_mul,Real.exp_log (by positivity)]

variable {A I : Type*} [Fintype A] [DecidableEq A] [Fintype I] [LinearOrder I]
  {n : I → ℕ} {N : ℕ}
  {V : I → Type*} [∀i, NormedAddCommGroup (V i)]
  [∀i, InnerProductSpace ℂ (V i)] [∀i, FiniteDimensional ℂ (V i)]

lemma prod_dimension_shift {K : Type*} [Fintype K] (d : K → ℝ) (hd : ∀i, 0<d i)
    (n : K → ℕ) (t : ℕ) :
    (∏i, d i*(n i+1:ℝ)^t)=
      Real.exp ((∑i, Real.log (d i))+(t:ℝ)*(∑i, Real.log (n i+1:ℝ))) := by
  rw [Finset.prod_mul_distrib,prod_pos_log_exp d hd,Real.exp_add,Finset.mul_sum,Real.exp_sum]
  congr 1
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  exact natShift_pow_exp (n i) t

lemma grouped_density_card_exp [Nonempty A] (p : A → Bool) :
    (Fintype.card (∀i, LocalDensityIndex p (n i)):ℝ) ≤
      Real.exp ((2*(Fintype.card A)^2:ℕ)*(∑i, Real.log (n i+1:ℝ))) := by
  have hc : (Fintype.card (∀i, LocalDensityIndex p (n i)):ℝ) ≤
      ∏i, (n i+1:ℝ)^(2*(Fintype.card A)^2) := by
    exact_mod_cast grouped_density_card_bound (n:=n) p
  refine hc.trans_eq ?_
  rw [Finset.mul_sum,Real.exp_sum]
  exact Finset.prod_congr rfl (fun i _ => natShift_pow_exp (n i) _)

lemma irreducible_finrank_pos {G W : Type*} [Group G]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G W) [ρ.IsIrreducible] : 0<Module.finrank ℂ W := by
  let : Nontrivial ρ.asModule := IsSimpleModule.nontrivial ℂ[G] ρ.asModule
  rw [← ρ.asModuleEquiv.finrank_eq]
  exact Module.finrank_pos

theorem actual_board_overlap_exp_oai
    [Nonempty A] [Nonempty I]
    {J W : Type*} [Fintype J] [LinearOrder J]
    {m : J → ℕ} {U : J → Type*} [∀j,NormedAddCommGroup (U j)]
    [∀j,InnerProductSpace ℂ (U j)] [∀j,FiniteDimensional ℂ (U j)]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (board : Fin N ↪ I × J) (p : A → Bool)
    (eR : (Σₗ i, Fin (n i)) ≃o Fin N) (eC : (Σₗ j, Fin (m j)) ≃o Fin N)
    (gR gC : Equiv.Perm (Fin N))
    (hR : ∀t, groupOf eR gR t=(board t).1) (hC : ∀t, groupOf eC gC t=(board t).2)
    (ρ : Representation ℂ (Equiv.Perm (Fin N)) W) [ρ.IsIrreducible]
    (α : ∀i, Representation ℂ (Equiv.Perm (Fin (n i))) (V i)) [∀i, (α i).IsIrreducible]
    (β : ∀j, Representation ℂ (Equiv.Perm (Fin (m j))) (U j)) [∀j, (β j).IsIrreducible] :
    ‖groupedProjection eC gC p β*isotypicProjection p ρ*groupedProjection eR gR p α‖^2 ≤
      Real.exp ((∑i, Real.log (Module.finrank ℂ (V i):ℝ))+
        (∑j, Real.log (Module.finrank ℂ (U j):ℝ))-Real.log (Module.finrank ℂ W:ℝ)+
        (Fintype.card I*Fintype.card J-(N:ℝ))+
        4*(Fintype.card A:ℝ)^2*((∑i, Real.log (n i+1:ℝ))+(∑j, Real.log (m j+1:ℝ)))) := by
  have hd : 0<(Module.finrank ℂ W:ℝ) := by exact_mod_cast irreducible_finrank_pos ρ
  have hdR (i : I) : 0<(Module.finrank ℂ (V i):ℝ) := by exact_mod_cast irreducible_finrank_pos (α i)
  have hdC (j : J) : 0<(Module.finrank ℂ (U j):ℝ) := by exact_mod_cast irreducible_finrank_pos (β j)
  have hb := actual_board_overlap board p eR eC gR gC hR hC ρ α β
  rw [prod_dimension_shift _ hdR,prod_dimension_shift _ hdC] at hb
  have hb' := hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul ((mul_le_mul_of_nonneg_left (grouped_density_card_exp (n:=n) p)
      (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)))
      (grouped_density_card_exp (n:=m) p) (by positivity)
      (by positivity)) (Real.exp_pos _).le)
  apply (mul_le_mul_iff_right₀ hd).mp
  refine hb'.trans_eq ?_
  rw [←Real.exp_log hd]
  simp only [←Real.exp_add,Real.log_exp]
  congr 1
  push_cast
  ring

end BinaryCoordinateSweeps.Signed

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6} : type_of% @OAI.BinaryCoordinateSweeps.Signed.actual_board_overlap_exp_oai.{u_1, u_2, u_3, u_4, u_5, u_6} := @OAI.BinaryCoordinateSweeps.Signed.actual_board_overlap_exp_oai.{u_1, u_2, u_3, u_4, u_5, u_6}
