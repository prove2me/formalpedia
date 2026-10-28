-- Prove2me | solution 1 for OAI.BinaryCoordinateSweeps.GridSplit.occurring_auxiliary_eventually
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T15:58:35.669002+00:00
-- url     : https://prove2.me/submissions/01c0a169-bf54-4f8c-b6ea-3ed53d99817c

import Mathlib
import Definitions.Def_BinarySweep
import Definitions.Def_OAIB3Bs000
import Theorems.Thm_OAI_BinaryCoordinateSweeps_Signed_actual_board_overlap_exp

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

lemma positive_pow {B : W →ₗ[ℂ] W} (hB : B.IsPositive) (q : ℕ) : (B^q).IsPositive :=
  match q with
  | 0 => LinearMap.isPositive_one
  | 1 => by simpa using hB
  | n+2 => by
    rw [pow_succ,pow_succ']
    simpa only [Module.End.mul_eq_comp,LinearMap.comp_assoc,hB.adjoint_eq] using (positive_pow hB n).conj_adjoint B

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

namespace BinaryCoordinateSweeps.Irrep
open Representation

variable {G V W : Type*} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [ρ.IsIrreducible]

lemma isotypicSpan_finrank_eq : Module.finrank ℂ (isotypicSpan ρ σ) =
    Module.finrank ℂ V * Module.finrank ℂ (IntertwiningMap ρ σ) := by
  rw [← evaluation_range, LinearMap.finrank_range_of_inj (evaluation_injective ρ σ),
    Module.finrank_tensorProduct]

end BinaryCoordinateSweeps.Irrep

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
-- module Solutions.OAIB3_Bsw.BinarySweep_Conditional_ConditionalAverage
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Irrep Representation

variable {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h) (z : ℝ)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

omit [FiniteDimensional ℂ V] in
lemma groupAverage_conditional (ρ : Representation ℂ (Equiv.Perm (FreeSlot H 0)) V) :
    groupAverage ρ (fun a => (conditionalGroupLaw H z a : ℂ)) =
      ∑ g : ConditionalChoices H, (conditionalChoiceWeight H z g : ℂ) •
        ρ (remainingPerm H g.val g.property) := by
  simp only [groupAverage,conditionalGroupLaw,Complex.ofReal_sum,Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  simp only [apply_ite,Complex.ofReal_zero,ite_smul,zero_smul]
  simp

end BinaryCoordinateSweeps

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

variable {A : Type*} [Fintype A] [DecidableEq A]

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

open scoped BigOperators Classical ComplexOrder
open Matrix

namespace BinaryCoordinateSweeps.Density

variable {I T : Type*} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]

variable {A : Type*} [Fintype A] [DecidableEq A]

lemma wordType_eq_iff (n : ℕ) (w v : Fin n → A) :
    wordType n w = wordType n v ↔ wordCounts w = wordCounts v := by
  simp only [wordType, Subtype.ext_iff, funext_iff, Finsupp.ext_iff]

end BinaryCoordinateSweeps.Density

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

end BinaryCoordinateSweeps.Irrep

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

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators Classical
open Equiv Equiv.Perm Finset

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

lemma isotypicSpan_rank_bound (p : A → Bool)
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) [ρ.IsIrreducible] :
    Module.finrank ℂ (isotypicSpan ρ (tensorRep p n)) ≤
      Module.finrank ℂ V * (n+1)^((Fintype.card A)^2) := by
  exact (isotypicSpan_finrank ρ (tensorRep p n)).trans (Nat.mul_le_mul_left _
    ((multiplicity_le_commutant ρ (tensorRep p n)).trans (tensor_commutant_finrank p n)))

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

open scoped BigOperators Classical ComplexOrder
open Matrix

namespace BinaryCoordinateSweeps.Signed
open Density

variable {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ}

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
-- module Solutions.OAIB3_Bsw.BinarySweep_Representations_MatrixIsotypicWhitening
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

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

end BinaryCoordinateSweeps.Signed

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
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_ActiveTypes
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
open Matrix

namespace BinaryCoordinateSweeps
open Density Irrep Representation

lemma orthogonal_idempotents_independent {I X : Type*} [Fintype I] [Fintype X]
    (P : I → Matrix X X ℂ) (hp : ∀i, P i*P i=P i)
    (hz : ∀i j, i≠j → P i*P j=0) (hne : ∀i, P i≠0) :
    LinearIndependent ℂ P := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hh := congrArg (fun M => P i*M) hc
  rw [Matrix.mul_zero,Matrix.mul_sum] at hh
  have he : (∑j, P i*(c j • P j))=c i • P i := by
    rw [Finset.sum_eq_single i]
    · rw [Matrix.mul_smul,hp]
    · intro j _ hji; rw [Matrix.mul_smul,hz i j hji.symm,smul_zero]
    · simp
  rw [he] at hh
  exact (smul_eq_zero.mp hh).resolve_right (hne i)

namespace Signed
variable {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ}

lemma typeProjection_linear (p : A → Bool) (α : n.Partition) :
    (typeProjection p α).toEuclideanLin=
      (isotypicSpan (Young.partitionHilbertRep α) (hilbertTensorRep p n)).starProjection.toLinearMap := by
  rw [hilbert_isotypic_eq]
  exact projectionMatrix_linear _

lemma typeProjection_idempotent (p : A → Bool) (α : n.Partition) :
    typeProjection p α*typeProjection p α=typeProjection p α := projectionMatrix_idempotent _

lemma typeProjection_orthogonal (p : A → Bool) (α β : n.Partition) (h : α≠β) :
    typeProjection p α*typeProjection p β=0 := by
  apply Matrix.toEuclideanLin.injective
  simp only [Matrix.toLpLin_mul_same,map_zero,typeProjection_linear]
  apply LinearMap.ext
  intro v
  change (isotypicSpan (Young.partitionHilbertRep α) (hilbertTensorRep p n)).starProjection
    ((isotypicSpan (Young.partitionHilbertRep β) (hilbertTensorRep p n)).starProjection v)=0
  apply (Submodule.starProjection_apply_eq_zero_iff _).mpr
  apply isotypic_orthogonal (Young.partitionHilbertRep α) (Young.partitionHilbertRep β)
    (hilbertTensorRep p n) (Young.partitionHilbertRep_unitary α)
    (Young.partitionHilbertRep_unitary β) (hilbertTensorRep_unitary p)
    (fun ⟨e⟩ => h (Young.partitionHilbertRep_equiv_injective α β e))
  exact Submodule.starProjection_apply_mem _ _

lemma activeType_card (p : A → Bool) (n : ℕ) :
    Fintype.card (ActiveType p n) ≤ (n+1)^((Fintype.card A)^2) := by
  let P (α : ActiveType p n) : invariantSubspace p n :=
    ⟨typeProjection p α.val,isotypicProjection_invariant p _⟩
  have hi : LinearIndependent ℂ (fun α : ActiveType p n => typeProjection p α.val) :=
    orthogonal_idempotents_independent _ (fun α => typeProjection_idempotent p α.val)
      (fun α β h => typeProjection_orthogonal p α.val β.val (fun he => h (Subtype.ext he)))
      (fun α => α.property)
  have hP : LinearIndependent ℂ P := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    apply Fintype.linearIndependent_iff.mp hi c
    have hh := congrArg (fun v : invariantSubspace p n => v.val) hc
    simpa only [Submodule.coe_sum,Submodule.coe_smul,Submodule.coe_zero,P] using hh
  exact hP.fintype_card_le_finrank.trans (invariantSubspace_finrank p n)

lemma all_typeProjection_sum (p : A → Bool) (n : ℕ) :
    (∑α : n.Partition, typeProjection p α)=1 := by
  apply Matrix.toEuclideanLin.injective
  simp only [map_sum,typeProjection_linear,Matrix.toLpLin_one]
  apply LinearMap.ext
  intro v
  simp only [LinearMap.sum_apply,ContinuousLinearMap.coe_coe,LinearMap.id_apply]
  exact Young.partition_projection_sum (hilbertTensorRep p n) (hilbertTensorRep_unitary p) v

theorem active_typeProjection_sum (p : A → Bool) (n : ℕ) :
    (∑α : ActiveType p n, typeProjection p α.val)=1 := by
  rw [← all_typeProjection_sum p n]
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter (fun α : n.Partition => typeProjection p α≠0))
    (by simp) (fun α => typeProjection p α)]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro α _
  split_ifs with h
  · rfl
  · exact (not_ne_iff.mp h).symm

end Signed
end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_IndependentPush
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

variable {I : Type*} [Fintype I] {Ω G : I → Type*}
  [∀i,Fintype (Ω i)] [∀i,Fintype (G i)]

omit [∀ i, Fintype (G i)] in
lemma finitePush_pi (w : ∀i, Ω i → ℂ) (f : ∀i, Ω i → G i) (g : ∀i, G i) :
    (∏i, finitePush (w i) (f i) (g i)) =
      finitePush (fun x : ∀i, Ω i => ∏i,w i (x i)) (fun x i => f i (x i)) g := by
  unfold finitePush
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Fintype.prod_ite_zero]
  congr 1
  exact propext funext_iff.symm

lemma finitePush_expectation {X Y V : Type*} [Fintype X] [Fintype Y]
    [AddCommMonoid V] [Module ℂ V] (w : X → ℂ) (f : X → Y) (F : Y → V) :
    (∑y, finitePush w f y • F y)=∑x,w x • F (f x) := by
  classical
  unfold finitePush
  simp only [Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp only [ite_smul,zero_smul]
  simp

lemma independentPush_expectation {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (w : ∀i, Ω i → ℂ) (f : ∀i, Ω i → G i) (F : (∀i,G i) → V) :
    (∑g : ∀i,G i, (∏i,finitePush (w i) (f i) (g i)) • F g)=
      ∑x : ∀i,Ω i, (∏i,w i (x i)) • F (fun i=>f i (x i)) := by
  simp_rw [finitePush_pi]
  exact finitePush_expectation _ _ _

end BinaryCoordinateSweeps

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

section

open scoped BigOperators Matrix.Norms.L2Operator
open Complex

namespace BinaryCoordinateSweeps.TraceHolder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma entry_norm_le (A : M ι) (i j : ι) : ‖A i j‖ ≤ ‖A‖ := by
  let e : EuclideanSpace ℂ ι := PiLp.single 2 j 1
  have he : ‖e‖ = 1 := by simp [e]
  have hi := PiLp.norm_apply_le ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) A e) i
  have hval : ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) A e).ofLp i = A i j := by
    simp only [Matrix.ofLp_toEuclideanCLM, e, PiLp.ofLp_single, Matrix.mulVec_single, MulOpposite.op_one, one_smul, Matrix.col_apply]
  rw [hval] at hi
  exact hi.trans (by simpa only [he, mul_one, ← Matrix.cstar_norm_def] using ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) A).le_opNorm e)

lemma trace_norm_le (A : M ι) : ‖Matrix.trace A‖ ≤ Fintype.card ι * ‖A‖ := by
  unfold Matrix.trace
  calc
    _ ≤ ∑ i, ‖A i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, ‖A‖ := Finset.sum_le_sum fun i _ => entry_norm_le A i i
    _ = _ := by simp

lemma prod_norm_le_one (l : List (M ι))
    (hl : ∀ a ∈ l, ‖a‖ ≤ 1) : ‖l.prod‖ ≤ 1 := by
  induction l with
  | nil =>
      change ‖(1 : M ι)‖ ≤ 1
      rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
      exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr (by simp)
  | cons a l ih =>
      rw [List.prod_cons]
      exact (norm_mul_le _ _).trans
        ((mul_le_of_le_one_left (norm_nonneg _) (hl _ (by simp))).trans
          (ih (fun b hb => hl b (by simp [hb]))))

lemma diagPower_add (d : ι → ℝ) (z w : ℂ) :
    diagPower d (z+w) = diagPower d z * diagPower d w := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [diagPower, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq]
    split_ifs <;> simp [add_mul, Complex.exp_add]
  · simp [diagPower, Matrix.diagonal_apply_ne _ hij]

lemma diagPower_norm_le_one (d : ι → ℝ) (hd0 : ∀ i, 0 ≤ d i) (hd : ∀ i, d i ≤ 1)
    {z : ℂ} (hz : 0 ≤ z.re) : ‖diagPower d z‖ ≤ 1 := by
  rw [diagPower, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  split_ifs with hi
  · simp
  · rw [Complex.norm_exp]
    apply Real.exp_le_one_iff.mpr
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_nonpos_of_nonneg_of_nonpos hz (Real.log_nonpos (hd0 i) (hd i))

lemma diagPower_imag_norm_le_one (d : ι → ℝ) (t : ℝ) :
    ‖diagPower d ((t : ℂ) * Complex.I)‖ ≤ 1 := by
  rw [diagPower, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  split_ifs <;> simp [Complex.norm_exp, Complex.mul_re]

omit [Fintype ι] in
lemma diagPower_one (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) :
    diagPower d 1 = Matrix.diagonal (fun i => (d i : ℂ)) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [diagPower, Matrix.diagonal_apply_eq, one_mul]
    by_cases hi : d i = 0
    · simp [hi]
    · rw [ite_eq_right hi, ← Complex.ofReal_exp, Real.exp_log (lt_of_le_of_ne (hd i) (Ne.symm hi))]
  · simp [diagPower, Matrix.diagonal_apply_ne _ hij]

lemma differentiable_diagPower (d : ι → ℝ) : Differentiable ℂ (diagPower d) := by
  let L := (Matrix.diagonalLinearMap ι ℂ ℂ).toContinuousLinearMap
  change Differentiable ℂ (fun z => L (fun i => if d i = 0 then 0 else
    Complex.exp (z * (Real.log (d i) : ℂ))))
  apply L.differentiable.comp
  apply differentiable_pi.mpr
  intro i
  by_cases hi : d i = 0
  · simp [hi]
  · simp only [hi, ite_false]
    exact Complex.differentiable_exp.comp (differentiable_id.mul_const _)

lemma word_norm_le_one {m : ℕ} (A : Fin m → M ι) (d : Fin m → ι → ℝ)
    (x : Fin m → ℂ) (hA : ∀ j, ‖A j‖ ≤ 1) (hd0 : ∀ j i, 0 ≤ d j i) (hd : ∀ j i, d j i ≤ 1)
    (hx : ∀ j, 0 ≤ (x j).re) : ‖word A d x‖ ≤ 1 := by
  apply prod_norm_le_one
  intro B hB
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hB
  exact (norm_mul_le _ _).trans
    ((mul_le_of_le_one_left (norm_nonneg _) (hA j)).trans
      (diagPower_norm_le_one (d j) (hd0 j) (hd j) (hx j)))

lemma differentiable_word {m : ℕ} (A : Fin m → M ι) (d : Fin m → ι → ℝ)
    (x : Fin m → ℂ → ℂ) (hx : ∀ j, Differentiable ℂ (x j)) :
    Differentiable ℂ (fun z => word A d (fun j => x j z)) := by
  induction m with
  | zero => simp [word]
  | succ m ih =>
      simp only [word, List.ofFn_succ, List.prod_cons]
      apply Differentiable.mul
      · have h₀ : Differentiable ℂ (fun z => diagPower (d 0) (x 0 z)) :=
          (differentiable_diagPower (d 0)).comp (hx 0)
        exact (differentiable_const (A 0)).mul h₀
      · exact ih (fun j => A j.succ) (fun j => d j.succ) (fun j => x j.succ)
          (fun j => hx j.succ)

lemma differentiable_traceWord {m : ℕ} (A : Fin m → M ι) (d : Fin m → ι → ℝ)
    (x : Fin m → ℂ → ℂ) (hx : ∀ j, Differentiable ℂ (x j)) :
    Differentiable ℂ (fun z => traceWord A d (fun j => x j z)) := by
  exact (Matrix.traceLinearMap ι ℂ ℂ).toContinuousLinearMap.differentiable.comp
    (differentiable_word A d x hx)

end BinaryCoordinateSweeps.TraceHolder

end

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

lemma matrixMoment_eq_zero_iff {q : ℕ} (hq : 0 < q) (A : M ι) :
    matrixMoment q A = 0 ↔ A = 0 := by
  constructor
  · intro h
    obtain ⟨U, V, s, hs, hU, hA, hg⟩ := exists_partial_svd A
    rw [matrixMoment_of_svd A q V s hg] at h
    have hi : ∀ i, s i = 0 := by
      intro i
      have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => pow_nonneg (hs j) (2*q))).mp h
      exact (pow_eq_zero_iff (by omega : 2*q ≠ 0)).mp (hz i (Finset.mem_univ _))
    rw [hA]
    simp [diagReal, hi]
  · intro h
    simp [matrixMoment, h, zero_pow (by omega : q ≠ 0)]

lemma unitary_norm_le_one (V : Matrix.unitaryGroup ι ℂ) : ‖(V : M ι)‖ ≤ 1 := by
  have h1 : ‖(1 : M ι)‖ ≤ 1 := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr (by simp)
  have h : ‖(V : M ι)‖ * ‖(V : M ι)‖ ≤ 1 := by
    rw [← CStarRing.norm_star_mul_self, Unitary.coe_star_mul_self]
    exact h1
  nlinarith [norm_nonneg (V : M ι)]

omit [Fintype ι] in
lemma diagPower_real (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) {x : ℝ} (hx : 0 < x) :
    diagPower d (x : ℂ) = diagReal (fun i => (d i) ^ x) := by
  unfold diagPower diagReal
  congr 1
  funext i
  by_cases hi : d i = 0
  · simp [hi, Real.zero_rpow hx.ne']
  · rw [ite_eq_right hi]
    change Complex.exp ((x : ℂ) * (Real.log (d i) : ℂ)) = ((d i ^ x : ℝ) : ℂ)
    rw [Real.rpow_def_of_pos (lt_of_le_of_ne (hd i) (Ne.symm hi))]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_exp]
    congr 2
    ring

lemma density_normalization {m : ℕ} (hm : 0 < m) (s : ι → ℝ) (hs : ∀ i, 0 ≤ s i)
    {t : ℝ} (ht : 0 < t) (hts : ∑ i, s i^m = t) :
    let d : ι → ℝ := fun i => s i ^ m / t
    (∀ i, 0 ≤ d i) ∧ (∑ i, d i = 1) ∧
    diagReal s = (t ^ ((m : ℝ)⁻¹) : ℝ) • diagPower d (((m : ℝ)⁻¹ : ℝ) : ℂ) := by
  dsimp only
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hd : ∀ i, 0 ≤ s i^m/t := fun i => div_nonneg (pow_nonneg (hs i) _) ht.le
  refine ⟨hd, ?_, ?_⟩
  · rw [← Finset.sum_div, hts, div_self ht.ne']
  · rw [diagPower_real _ hd (inv_pos.mpr hm')]
    unfold diagReal
    rw [← Matrix.diagonal_smul]
    congr 1
    funext i
    change (s i : ℂ) = ((t ^ (m : ℝ)⁻¹ : ℝ) : ℂ) *
      (((s i ^ m / t) ^ (m : ℝ)⁻¹ : ℝ) : ℂ)
    rw [Real.div_rpow (pow_nonneg (hs i) _) ht.le,
      Real.pow_rpow_inv_natCast (hs i) (Nat.ne_of_gt hm)]
    norm_cast
    exact (mul_div_cancel₀ (s i) (Real.rpow_pos_of_pos ht _).ne').symm

end BinaryCoordinateSweeps.TraceHolder

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_MatrixBounds_TraceConvex
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Matrix.Norms.L2Operator
open Complex

namespace BinaryCoordinateSweeps.TraceHolder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma trace_mul_diagonal_le (A : M ι) (d : ι → ℝ)
    (hA : ‖A‖ ≤ 1) (hd : ∀ i, 0 ≤ d i) :
    ‖Matrix.trace (A * Matrix.diagonal (fun i => (d i : ℂ)))‖ ≤ ∑ i, d i := by
  unfold Matrix.trace
  simp only [Matrix.diag_apply, Matrix.mul_diagonal]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hd i)]
  exact mul_le_of_le_one_left (hd i) ((entry_norm_le A i i).trans hA)

lemma trace_prod_density_le (L : List (M ι)) (A : M ι) (d : ι → ℝ)
    (hL : ∀ B ∈ L, ‖B‖ ≤ 1) (hA : ‖A‖ ≤ 1) (hd : ∀ i, 0 ≤ d i)
    (hmem : A * Matrix.diagonal (fun i => (d i : ℂ)) ∈ L) :
    ‖Matrix.trace L.prod‖ ≤ ∑ i, d i := by
  obtain ⟨l, r, rfl⟩ := List.mem_iff_append.mp hmem
  have hl : ‖l.prod‖ ≤ 1 := prod_norm_le_one l (fun B hB => hL B (by simp [hB]))
  have hr : ‖r.prod‖ ≤ 1 := prod_norm_le_one r (fun B hB => hL B (by simp [hB]))
  simp only [List.prod_append, List.prod_cons]
  rw [← mul_assoc, Matrix.trace_mul_cycle]
  rw [← mul_assoc]
  apply trace_mul_diagonal_le _ d _ hd
  exact (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _)
    ((norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) hr).trans hl))).trans hA)

lemma word_absorb_phase {m : ℕ} (A : Fin m → M ι) (d : Fin m → ι → ℝ)
    (x : Fin m → ℂ) :
    word A d x = word (fun j => A j * diagPower (d j) ((x j).im * I)) d
      (fun j => ((x j).re : ℂ)) := by
  unfold word
  congr 1
  apply List.ofFn_inj.mpr
  funext j
  have hx : x j = ((x j).im : ℂ) * I + ((x j).re : ℂ) := by
    rw [add_comm]; exact (Complex.re_add_im (x j)).symm
  calc
    A j * diagPower (d j) (x j) = A j *
        diagPower (d j) (((x j).im : ℂ) * I + ((x j).re : ℂ)) := by rw [← hx]
    _ = _ := by rw [diagPower_add, mul_assoc]

lemma admissible_complex {m : ℕ} (d : Fin m → ι → ℝ) (x : Fin m → ℝ)
    (hx : Admissible d x) (A : Fin m → M ι) (hA : ∀ j, ‖A j‖ ≤ 1)
    (z : Fin m → ℂ) (hz : ∀ j, (z j).re = x j) : ‖traceWord A d z‖ ≤ 1 := by
  unfold traceWord
  rw [word_absorb_phase]
  simp only [hz]
  apply hx
  intro j
  exact (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) (hA j)).trans
    (diagPower_imag_norm_le_one _ _))

lemma vertex_mem_exponentSet {m : ℕ} (d : Fin m → ι → ℝ)
    (hd : ∀ j i, 0 ≤ d j i) (hs : ∀ j, ∑ i, d j i = 1) (j : Fin m) :
    Pi.single j 1 ∈ exponentSet d := by
  have hd1 : ∀ j i, d j i ≤ 1 := by
    intro j i
    rw [← hs j]
    exact Finset.single_le_sum (fun i _ => hd j i) (Finset.mem_univ i)
  constructor
  · intro i; simp only [Pi.single_apply]; split_ifs <;> norm_num
  · intro A hA
    have hv0 : ∀ i : Fin m, 0 ≤ (((Pi.single j 1 : Fin m → ℝ) i) : ℂ).re := by
      intro i; simp only [ofReal_re, Pi.single_apply]; split_ifs <;> norm_num
    have hmem : A j * Matrix.diagonal (fun i => (d j i : ℂ)) ∈
        List.ofFn (fun k => A k * diagPower (d k) (((Pi.single j 1 : Fin m → ℝ) k) : ℂ)) := by
      apply List.mem_ofFn.mpr
      refine ⟨j, ?_⟩
      simp [diagPower_one _ (hd j)]
    have hlist : ∀ B ∈ List.ofFn (fun k => A k *
        diagPower (d k) (((Pi.single j 1 : Fin m → ℝ) k) : ℂ)), ‖B‖ ≤ 1 := by
      intro B hB
      obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hB
      exact (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) (hA k)).trans
        (diagPower_norm_le_one _ (hd k) (hd1 k) (hv0 k)))
    unfold traceWord word
    exact (trace_prod_density_le _ _ (d j) hlist (hA j) (hd j) hmem).trans_eq (hs j)

lemma convex_exponentSet {m : ℕ} (d : Fin m → ι → ℝ)
    (hd : ∀ j i, 0 ≤ d j i) (hd1 : ∀ j i, d j i ≤ 1) :
    Convex ℝ (exponentSet d) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro j
    exact add_nonneg (mul_nonneg ha (hx.1 j)) (mul_nonneg hb (hy.1 j))
  · intro A hA
    let e (j : Fin m) (z : ℂ) := (1-z) * (x j : ℂ) + z * (y j : ℂ)
    let f (z : ℂ) := traceWord A d (fun j => e j z)
    have he : ∀ j, Differentiable ℂ (e j) := fun j =>
      (((differentiable_const (1 : ℂ)).sub differentiable_id).mul_const _).add
        (differentiable_id.mul_const _)
    have hf : Differentiable ℂ f := differentiable_traceWord A d e he
    have hre (j : Fin m) (z : ℂ) : (e j z).re = (1-z.re)*x j + z.re*y j := by
      simp [e, Complex.mul_re]
    have hbound : BddAbove ((norm ∘ f) '' HadamardThreeLines.verticalClosedStrip 0 1) := by
      refine ⟨Fintype.card ι, ?_⟩
      rintro t ⟨z, hz, rfl⟩
      have hz' : 0 ≤ z.re ∧ z.re ≤ 1 := hz
      have hw : ‖word A d (fun j => e j z)‖ ≤ 1 :=
        word_norm_le_one A d _ hA hd hd1 (fun j => by
          rw [hre]
          exact add_nonneg (mul_nonneg (sub_nonneg.mpr hz'.2) (hx.1 j))
            (mul_nonneg hz'.1 (hy.1 j)))
      exact (trace_norm_le _).trans (mul_le_of_le_one_right (Nat.cast_nonneg _) hw)
    have hleft : ∀ z ∈ Complex.re ⁻¹' {(0 : ℝ)}, ‖f z‖ ≤ 1 := by
      intro z hz
      have hz' : z.re = 0 := hz
      exact admissible_complex d x hx.2 A hA _ (fun j => by rw [hre, hz']; ring)
    have hright : ∀ z ∈ Complex.re ⁻¹' {(1 : ℝ)}, ‖f z‖ ≤ 1 := by
      intro z hz
      have hz' : z.re = 1 := hz
      exact admissible_complex d y hy.2 A hA _ (fun j => by rw [hre, hz']; ring)
    have hb1 : b ≤ 1 := by linarith
    have hbi : (b : ℂ) ∈ HadamardThreeLines.verticalClosedStrip 0 1 := ⟨hb, hb1⟩
    have hthree := HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'
      f hbi hf.diffContOnCl hbound hleft hright
    have heval : f (b : ℂ) = traceWord A d (fun j => ((a • x + b • y) j : ℂ)) := by
      change traceWord A d (fun j => e j (b : ℂ)) = _
      apply congrArg (traceWord A d)
      funext j
      dsimp only [e]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_add,
        Complex.ofReal_mul]
      have ha' : (a : ℂ) = 1 - (b : ℂ) := by exact_mod_cast (show a = 1-b by linarith)
      rw [ha']
    simpa [heval] using hthree

theorem trace_diagonal_simplex {m : ℕ} (d : Fin m → ι → ℝ)
    (hd : ∀ j i, 0 ≤ d j i) (hs : ∀ j, ∑ i, d j i = 1)
    (x : Fin m → ℝ) (hx : ∀ j, 0 ≤ x j) (hsx : ∑ j, x j = 1)
    (A : Fin m → M ι) (hA : ∀ j, ‖A j‖ ≤ 1) :
    ‖traceWord A d (fun j => (x j : ℂ))‖ ≤ 1 := by
  have hd1 : ∀ j i, d j i ≤ 1 := by
    intro j i
    rw [← hs j]
    exact Finset.single_le_sum (fun i _ => hd j i) (Finset.mem_univ i)
  have hc := convex_exponentSet d hd hd1
  have hsum := hc.sum_mem (t := Finset.univ) (w := x) (z := fun j => Pi.single j (1 : ℝ))
    (fun j _ => hx j) hsx (fun j _ => vertex_mem_exponentSet d hd hs j)
  have heq : ∑ j, x j • Pi.single j (1 : ℝ) = x := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [heq] at hsum
  exact hsum.2 A hA

end BinaryCoordinateSweeps.TraceHolder

end

open scoped BigOperators Matrix.Norms.L2Operator

namespace BinaryCoordinateSweeps.TraceHolder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma prod_sandwich_succ {α : Type*} [Monoid α] (n : ℕ)
    (U D V : Fin (n+1) → α) :
    (List.ofFn (fun j => U j * D j * V j)).prod =
      U 0 * D 0 * (List.ofFn (fun j : Fin n =>
        (V j.castSucc * U j.succ) * D j.succ)).prod * V (Fin.last n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.prod_cons]
      rw [ih (fun j => U j.succ) (fun j => D j.succ) (fun j => V j.succ)]
      simp only [List.ofFn_succ, List.prod_cons, Fin.castSucc_zero, Fin.succ_zero_eq_one,
        Fin.succ_last, Fin.castSucc_succ]
      simp only [mul_assoc]

lemma trace_prod_sandwich {n : ℕ} (U D V : Fin (n+1) → M ι) :
    Matrix.trace (List.ofFn (fun j => U j * D j * V j)).prod =
      Matrix.trace (List.ofFn (Fin.cons (V (Fin.last n) * U 0 * D 0)
        (fun j : Fin n => (V j.castSucc * U j.succ) * D j.succ))).prod := by
  rw [prod_sandwich_succ, List.ofFn_succ, List.prod_cons]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [Matrix.trace_mul_comm]
  congr 1
  simp only [mul_assoc]

theorem trace_diagonal_sandwich {n : ℕ} (d : Fin (n+1) → ι → ℝ)
    (hd : ∀ j i, 0 ≤ d j i) (hs : ∀ j, ∑ i, d j i = 1)
    (x : Fin (n+1) → ℝ) (hx : ∀ j, 0 ≤ x j) (hsx : ∑ j, x j = 1)
    (U V : Fin (n+1) → M ι) (hU : ∀ j, ‖U j‖ ≤ 1) (hV : ∀ j, ‖V j‖ ≤ 1) :
    ‖Matrix.trace (List.ofFn (fun j => U j * diagPower (d j) (x j : ℂ) * V j)).prod‖ ≤ 1 := by
  let A : Fin (n+1) → M ι := Fin.cons (V (Fin.last n) * U 0)
    (fun j : Fin n => V j.castSucc * U j.succ)
  have hA : ∀ j, ‖A j‖ ≤ 1 := by
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · exact (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) (hV _)).trans (hU _))
    · exact (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) (hV _)).trans (hU _))
  have heq : Matrix.trace (List.ofFn (fun j => U j * diagPower (d j) (x j : ℂ) * V j)).prod =
      traceWord A d (fun j => (x j : ℂ)) := by
    rw [trace_prod_sandwich]
    unfold traceWord word
    congr 2
    apply List.ofFn_inj.mpr
    funext j
    refine Fin.cases ?_ (fun k => ?_) j <;> rfl
  rw [heq]
  exact trace_diagonal_simplex d hd hs x hx hsx A hA

end BinaryCoordinateSweeps.TraceHolder

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_MatrixBounds_TraceHolder
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

lemma normalized_svd {q : ℕ} (hq : 0 < q) (A : M ι) (ht : 0 < matrixMoment q A) :
    ∃ (U V : M ι) (d : ι → ℝ), ‖U‖ ≤ 1 ∧ ‖V‖ ≤ 1 ∧
      (∀ i, 0 ≤ d i) ∧ (∑ i, d i = 1) ∧
      A = (matrixMoment q A ^ ((2*q : ℕ) : ℝ)⁻¹ : ℝ) •
        (U * diagPower d ((((2*q : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) * V) := by
  obtain ⟨U, W, s, hs, hU, hA, hg⟩ := exists_partial_svd A
  have hsum := matrixMoment_of_svd A q W s hg
  obtain ⟨hd, hsumd, heq⟩ := density_normalization (by omega : 0 < 2*q) s hs ht hsum.symm
  refine ⟨U, star (W : M ι), fun i => s i ^ (2*q) / matrixMoment q A,
    hU, ?_, hd, hsumd, ?_⟩
  · simpa only [norm_star] using unitary_norm_le_one W
  · conv_lhs => rw [hA, heq]
    simp only [mul_smul_comm, smul_mul_assoc]

lemma prod_ofFn_smul {m : ℕ} (r : Fin m → ℝ) (A : Fin m → M ι) :
    (List.ofFn (fun j => r j • A j)).prod = (∏ j, r j) • (List.ofFn A).prod := by
  induction m with
  | zero => simp
  | succ m ih =>
      simp only [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ]
      rw [ih]
      rw [smul_mul_smul_comm]

lemma trace_diagonal_sandwich_pos {m : ℕ} (hm : 0 < m) (d : Fin m → ι → ℝ)
    (hd : ∀ j i, 0 ≤ d j i) (hs : ∀ j, ∑ i, d j i = 1)
    (x : Fin m → ℝ) (hx : ∀ j, 0 ≤ x j) (hsx : ∑ j, x j = 1)
    (U V : Fin m → M ι) (hU : ∀ j, ‖U j‖ ≤ 1) (hV : ∀ j, ‖V j‖ ≤ 1) :
    ‖Matrix.trace (List.ofFn (fun j => U j * diagPower (d j) (x j : ℂ) * V j)).prod‖ ≤ 1 := by
  cases m with
  | zero => omega
  | succ n => exact trace_diagonal_sandwich d hd hs x hx hsx U V hU hV

theorem matrix_trace_holder {q : ℕ} (hq : 0 < q) (A : Fin (2*q) → M ι) :
    ‖Matrix.trace (List.ofFn A).prod‖ ≤
      ∏ j, matrixMoment q (A j) ^ (((2*q : ℕ) : ℝ)⁻¹) := by
  classical
  have hm : 0 < 2*q := by omega
  have hm' : 0 < ((2*q : ℕ) : ℝ) := by exact_mod_cast hm
  by_cases hzero : ∃ j, matrixMoment q (A j) = 0
  · obtain ⟨j, hj⟩ := hzero
    have hAj : A j = 0 := (matrixMoment_eq_zero_iff hq (A j)).mp hj
    have hp : (List.ofFn A).prod = 0 := List.prod_eq_zero (List.mem_ofFn.mpr ⟨j, hAj⟩)
    rw [hp, Matrix.trace_zero, norm_zero]
    exact Finset.prod_nonneg (fun k _ => Real.rpow_nonneg (matrixMoment_nonneg _ _) _)
  · have ht : ∀ j, 0 < matrixMoment q (A j) := by
      intro j
      exact lt_of_le_of_ne (matrixMoment_nonneg _ _) (Ne.symm (fun h => hzero ⟨j, h⟩))
    choose U V d hU hV hd hs heq using fun j => normalized_svd hq (A j) (ht j)
    let r : Fin (2*q) → ℝ := fun j => matrixMoment q (A j) ^ (((2*q : ℕ) : ℝ)⁻¹)
    let B : Fin (2*q) → M ι := fun j =>
      U j * diagPower (d j) (((((2*q : ℕ) : ℝ)⁻¹ : ℝ) : ℂ)) * V j
    have hb : ‖Matrix.trace (List.ofFn B).prod‖ ≤ 1 := by
      apply trace_diagonal_sandwich_pos hm d hd hs (fun _ => ((2*q : ℕ) : ℝ)⁻¹)
        (fun _ => (inv_pos.mpr hm').le) _ U V hU hV
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact mul_inv_cancel₀ hm'.ne'
    have hEq : A = fun j => r j • B j := funext heq
    conv_lhs => rw [hEq, prod_ofFn_smul, Matrix.trace_smul, norm_smul]
    have hr : 0 ≤ ∏ j, r j := Finset.prod_nonneg fun j _ => Real.rpow_nonneg (ht j).le _
    rw [Real.norm_eq_abs, abs_of_nonneg hr]
    exact mul_le_of_le_one_right hr hb

end BinaryCoordinateSweeps.TraceHolder

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

lemma trace_mul_pow_comm (A B : M ι) (q : ℕ) :
    Matrix.trace ((A * B)^q) = Matrix.trace ((B * A)^q) := by
  cases q with
  | zero => rfl
  | succ q =>
      rw [pow_succ, ← mul_assoc, mul_pow_mul, Matrix.trace_mul_comm,
        ← mul_assoc, ← pow_succ']

lemma matrixMoment_star (q : ℕ) (A : M ι) :
    matrixMoment q (star A) = matrixMoment q A := by
  simp only [matrixMoment, star_star]
  rw [trace_mul_pow_comm]

lemma schatten_nonneg (q : ℕ) (A : M ι) : 0 ≤ schatten q A :=
  Real.rpow_nonneg (matrixMoment_nonneg _ _) _

lemma schatten_star (q : ℕ) (A : M ι) : schatten q (star A) = schatten q A := by
  simp only [schatten, matrixMoment_star]

lemma schatten_pow {q : ℕ} (hq : 0 < q) (A : M ι) :
    schatten q A ^ (2*q) = matrixMoment q A := by
  exact Real.rpow_inv_natCast_pow (matrixMoment_nonneg _ _) (by omega : 2*q ≠ 0)

lemma prod_ofFn_sum {R κ : Type*} [Semiring R] [Fintype κ] {m : ℕ}
    (A : Fin m → κ → R) :
    (List.ofFn (fun j => ∑ k, A j k)).prod =
      ∑ f : Fin m → κ, (List.ofFn (fun j => A j (f j))).prod := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.ofFn_succ, List.prod_cons, ih]
      rw [← (Fin.consEquiv (fun _ : Fin (m+1) => κ)).sum_comp, Fintype.sum_prod_type]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f _
      simp only [Fin.consEquiv, Equiv.coe_fn_mk, List.ofFn_succ, List.prod_cons,
        Fin.cons_zero, Fin.cons_succ]

lemma trace_holder_sums {κ : Type*} [Fintype κ] {q : ℕ} (hq : 0 < q)
    (A : Fin (2*q) → κ → M ι) :
    ‖Matrix.trace (List.ofFn (fun j => ∑ k, A j k)).prod‖ ≤
      ∏ j, ∑ k, schatten q (A j k) := by
  rw [prod_ofFn_sum, Matrix.trace_sum]
  calc
    _ ≤ ∑ f : Fin (2*q) → κ, ‖Matrix.trace (List.ofFn (fun j => A j (f j))).prod‖ :=
      norm_sum_le _ _
    _ ≤ ∑ f : Fin (2*q) → κ, ∏ j, schatten q (A j (f j)) := by
      exact Finset.sum_le_sum (fun f _ => matrix_trace_holder hq _)
    _ = ∏ j, ∑ k, schatten q (A j k) := by
      exact (Fintype.prod_sum (fun j k => schatten q (A j k))).symm

lemma prod_alternating {R : Type*} [Monoid R] (q : ℕ) (A B : R) :
    (List.ofFn (fun j : Fin (2*q) => if j.val % 2 = 0 then A else B)).prod =
      (A * B)^q := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Nat.mul_succ]
      have hf : (fun j : Fin (2*q+2) => if j.val % 2 = 0 then A else B) =
          Fin.append (fun j : Fin (2*q) => if j.val % 2 = 0 then A else B)
            (fun j : Fin 2 => if j.val % 2 = 0 then A else B) := by
        funext j
        refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · simp
        · simp [Nat.add_mod]
      rw [hf, List.ofFn_fin_append, List.prod_append, ih, pow_succ]
      simp [List.ofFn_succ]

lemma matrixMoment_le_sum_pow {κ : Type*} [Fintype κ] {q : ℕ} (hq : 0 < q)
    (A : κ → M ι) :
    matrixMoment q (∑ k, A k) ≤ (∑ k, schatten q (A k))^(2*q) := by
  let W : Fin (2*q) → κ → M ι :=
    fun j k => if j.val % 2 = 0 then star (A k) else A k
  have hW : (List.ofFn (fun j => ∑ k, W j k)).prod =
      (star (∑ k, A k) * (∑ k, A k))^q := by
    have heq : (fun j => ∑ k, W j k) =
        (fun j : Fin (2*q) => if j.val % 2 = 0 then star (∑ k, A k) else ∑ k, A k) := by
      funext j
      dsimp [W]
      split_ifs <;> simp [star_sum]
    rw [heq, prod_alternating]
  have hS : ∀ j : Fin (2*q), (∑ k, schatten q (W j k)) = ∑ k, schatten q (A k) := by
    intro j
    apply Finset.sum_congr rfl
    intro k _
    dsimp [W]
    split_ifs <;> simp only [schatten_star]
  have hh := trace_holder_sums hq W
  rw [hW] at hh
  simp only [hS, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hh
  exact (Complex.re_le_norm _).trans hh

theorem schatten_sum_le {κ : Type*} [Fintype κ] {q : ℕ} (hq : 0 < q)
    (A : κ → M ι) : schatten q (∑ k, A k) ≤ ∑ k, schatten q (A k) := by
  have hn : 0 ≤ ∑ k, schatten q (A k) := Finset.sum_nonneg fun k _ => schatten_nonneg _ _
  have hh := Real.rpow_le_rpow (matrixMoment_nonneg q (∑ k, A k))
    (matrixMoment_le_sum_pow hq A) (show 0 ≤ (((2*q : ℕ) : ℝ)⁻¹) by positivity)
  rw [Real.pow_rpow_inv_natCast hn (by omega : 2*q ≠ 0)] at hh
  exact hh

end BinaryCoordinateSweeps.TraceHolder

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_MatrixBounds_SchattenBasic
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical Matrix.Norms.L2Operator

namespace BinaryCoordinateSweeps.TraceHolder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma alternating_prod {R : Type*} [Monoid R] (q : ℕ) (x y : R) :
    (List.ofFn (fun i : Fin (2*q) => if i.val%2=0 then x else y)).prod=(x*y)^q := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show 2*(q+1)=2*q+1+1 by omega]
    simp only [List.ofFn_succ,List.prod_cons,Fin.val_zero,Fin.val_succ]
    norm_num only [Nat.zero_mod,Nat.reduceMod,ite_eq_left,ite_eq_right]
    have he (i : Fin (2*q)) : (i.val+1+1)%2=i.val%2 := by omega
    simp_rw [he]
    rw [ih,pow_succ']
    exact (mul_assoc _ _ _).symm

lemma alternating_gram (q : ℕ) (A : M ι) :
    (List.ofFn (fun i : Fin (2*q) => if i.val%2=0 then star A else A)).prod=
      (star A*A)^q := alternating_prod q _ _

lemma matrixMoment_smul (q : ℕ) (r : ℝ) (A : M ι) :
    matrixMoment q (r • A)=r^(2*q)*matrixMoment q A := by
  unfold matrixMoment
  rw [star_smul,star_trivial,smul_mul_smul_comm,smul_pow,Matrix.trace_smul]
  simp only [Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [← pow_two,← pow_mul]

lemma momentRoot_pow {q : ℕ} (hq : 0 < q) (A : M ι) :
    (matrixMoment q A ^ (((2*q:ℕ):ℝ)⁻¹))^(2*q)=matrixMoment q A := by
  rw [← Real.rpow_natCast,← Real.rpow_mul (matrixMoment_nonneg q A),
    inv_mul_cancel₀ (show ((2*q:ℕ):ℝ)≠0 by positivity),Real.rpow_one]

lemma matrixMoment_of_density_sandwich_le {q : ℕ} (hq : 0<q)
    (d : ι → ℝ) (hd : ∀i, 0≤d i) (hs : ∑i, d i=1)
    (U V : M ι) (hU : ‖U‖≤1) (hV : ‖V‖≤1) :
    matrixMoment q (U*diagPower d ((((2*q:ℕ):ℝ)⁻¹ : ℝ) : ℂ)*V) ≤ 1 := by
  let D := diagPower d ((((2*q:ℕ):ℝ)⁻¹ : ℝ) : ℂ)
  have hD : star D=D := by
    unfold D
    rw [diagPower_real d hd (by positivity)]
    exact star_diagReal _
  have hb := trace_diagonal_sandwich_pos (show 0<2*q by omega)
    (fun _ => d) (fun _ => hd) (fun _ => hs)
    (fun _ => ((2*q:ℕ):ℝ)⁻¹) (fun _ => by positivity)
    (by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];
        exact mul_inv_cancel₀ (by positivity))
    (fun i : Fin (2*q) => if i.val%2=0 then star V else U)
    (fun i : Fin (2*q) => if i.val%2=0 then star U else V)
    (by intro i; split_ifs <;> simpa only [norm_star] using (by assumption))
    (by intro i; split_ifs <;> simpa only [norm_star] using (by assumption))
  have he : (fun i : Fin (2*q) =>
      (if i.val%2=0 then star V else U)*D*(if i.val%2=0 then star U else V))=
      fun i => if i.val%2=0 then star (U*D*V) else U*D*V := by
    funext i
    split_ifs <;> simp only [star_mul,hD,mul_assoc]
  change ‖Matrix.trace (List.ofFn (fun i : Fin (2*q) =>
    (if i.val%2=0 then star V else U)*D*(if i.val%2=0 then star U else V))).prod‖≤1 at hb
  rw [he,alternating_gram] at hb
  exact (Complex.re_le_norm _).trans hb

lemma matrixMoment_contract_left {q : ℕ} (hq : 0<q) (C A : M ι) (hC : ‖C‖≤1) :
    matrixMoment q (C*A) ≤ matrixMoment q A := by
  by_cases hz : matrixMoment q A=0
  · have ha := (matrixMoment_eq_zero_iff hq A).mp hz
    simp only [ha,mul_zero]
    exact le_rfl
  have ht := lt_of_le_of_ne (matrixMoment_nonneg q A) (Ne.symm hz)
  obtain ⟨U,V,d,hU,hV,hd,hs,he⟩ := normalized_svd hq A ht
  have hec : C*A = matrixMoment q A ^ (((2*q:ℕ):ℝ)⁻¹) •
      ((C*U)*diagPower d ((((2*q:ℕ):ℝ)⁻¹ : ℝ) : ℂ)*V) := by
    conv_lhs => rw [he]
    rw [mul_smul_comm]
    congr 1
    simp only [mul_assoc]
  rw [hec,matrixMoment_smul,momentRoot_pow hq A]
  exact mul_le_of_le_one_right ht.le (matrixMoment_of_density_sandwich_le hq d hd hs
    (C*U) V ((norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) hC).trans hU)) hV)

lemma matrixMoment_mul_left {q : ℕ} (hq : 0<q) (C A : M ι) :
    matrixMoment q (C*A) ≤ ‖C‖^(2*q)*matrixMoment q A := by
  by_cases hc : C=0
  · simp only [hc,zero_mul,norm_zero,zero_pow (by omega : 2*q≠0),
      (matrixMoment_eq_zero_iff hq (0:M ι)).mpr rfl]
    exact le_rfl
  have hn : 0<‖C‖ := norm_pos_iff.mpr hc
  have hf : ‖‖C‖⁻¹ • C‖≤1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
  have he : C=‖C‖ • (‖C‖⁻¹ • C) := by rw [smul_smul,mul_inv_cancel₀ hn.ne',one_smul]
  conv_lhs => rw [he,smul_mul_assoc,matrixMoment_smul]
  exact mul_le_mul_of_nonneg_left (matrixMoment_contract_left hq _ A hf) (pow_nonneg hn.le _)

lemma matrixMoment_unitary_conj (q : ℕ) (U : Matrix.unitaryGroup ι ℂ) (A : M ι) :
    matrixMoment q ((U:M ι)*A*star (U:M ι))=matrixMoment q A := by
  unfold matrixMoment
  have he : star ((U:M ι)*A*star (U:M ι))*((U:M ι)*A*star (U:M ι))=
      (U:M ι)*(star A*A)*star (U:M ι) := by
    simp only [star_mul,star_star,mul_assoc,← mul_assoc (star (U:M ι)) (U:M ι),
      Unitary.coe_star_mul_self,one_mul]
  rw [he,unitary_conj_pow,trace_unitary_conj]

end BinaryCoordinateSweeps.TraceHolder

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_LinearEvenMoment
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep
open TraceHolder

variable {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V] [Fintype ι] [DecidableEq ι]

lemma trace_orthonormalMatrix (v : OrthonormalBasis ι ℂ V) (A : V →ₗ[ℂ] V) :
    LinearMap.trace ℂ V A = Matrix.trace (LinearMap.toMatrixOrthonormal v A) :=
  LinearMap.trace_eq_matrix_trace ℂ v.toBasis A

lemma evenMoment_orthonormalMatrix (v : OrthonormalBasis ι ℂ V) (q : ℕ) (A : V →ₗ[ℂ] V) :
    evenMoment q A=matrixMoment q (LinearMap.toMatrixOrthonormal v A) := by
  unfold evenMoment matrixMoment
  rw [trace_orthonormalMatrix v]
  simp only [map_pow,map_mul,← LinearMap.star_eq_adjoint,map_star]

lemma evenMoment_nonneg (q : ℕ) (A : V →ₗ[ℂ] V) : 0≤evenMoment q A := by
  rw [evenMoment_orthonormalMatrix (stdOrthonormalBasis ℂ V)]
  exact matrixMoment_nonneg _ _

lemma evenMoment_unitary_left (q : ℕ) (U A : V →ₗ[ℂ] V) (hu : U.adjoint*U=1) :
    evenMoment q (U*A)=evenMoment q A := by
  unfold evenMoment
  rw [show (U*A).adjoint*(U*A)=A.adjoint*A by
    rw [← LinearMap.star_eq_adjoint,star_mul]; calc
      _ = A.adjoint*(U.adjoint*U)*A := by noncomm_ring
      _ = _ := by rw [hu,mul_one]]

end BinaryCoordinateSweeps.Irrep

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

end BinaryCoordinateSweeps.Signed

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
lemma typeProjection_commutes_action (p : A → Bool)
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) (g : Equiv.Perm (Fin n)) :
    isotypicProjection p ρ*actionMatrix p g=actionMatrix p g*isotypicProjection p ρ :=
  invariant_matrix_commutes p _ (isotypicProjection_invariant p ρ) g

end BinaryCoordinateSweeps.Signed

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

lemma euclidean_pow {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) (q : ℕ) : (M^q).toEuclideanLin=M.toEuclideanLin^q := by
  induction q with
  | zero => simp only [pow_zero,Matrix.toLpLin_one,Module.End.one_eq_id]
  | succ q ih => rw [pow_succ,Matrix.toLpLin_mul_same,ih,pow_succ,Module.End.mul_eq_comp]

lemma projected_gram_power {I : Type*} [Fintype I] [DecidableEq I]
    (P M : Matrix I I ℂ) (hP : P.IsHermitian) (hPP : P*P=P) (hPM : P*M=M*P)
    {q : ℕ} (hq : 0 < q) :
    (star (P*M)*(P*M))^q = (star M*M)^q*P := by
  have hs : P*star M=star M*P := by
    have hh := congrArg star hPM
    simpa only [star_mul,show star P=P from hP.eq] using hh.symm
  have hc : Commute (star M*M) P := by
    change star M*M*P=P*(star M*M)
    rw [mul_assoc,← hPM,← mul_assoc,← hs,mul_assoc]
  have he : star (P*M)*(P*M)=(star M*M)*P := by
    simp only [star_mul,show star P=P from hP.eq]
    rw [mul_assoc,← mul_assoc P P M,hPP,hPM,← mul_assoc]
  rw [he,hc.mul_pow,(show IsIdempotentElem P from hPP).pow_eq (ne_of_gt hq)]

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

namespace Signed
variable {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ}
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

lemma signedAverage_linear (p : A → Bool) (w : Equiv.Perm (Fin n) → ℂ) :
    (signedAverage p w).toEuclideanLin=groupAverage (hilbertTensorRep p n) w := by
  simp only [signedAverage,map_sum,map_smul,actionMatrix_linear,groupAverage]

omit [FiniteDimensional ℂ V] in
lemma isotypicProjection_commutes_average (p : A → Bool)
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) (w : Equiv.Perm (Fin n) → ℂ) :
    isotypicProjection p ρ*signedAverage p w=signedAverage p w*isotypicProjection p ρ := by
  simp only [signedAverage,Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc,
    typeProjection_commutes_action]

theorem local_projected_moment (p : A → Bool)
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) [ρ.IsIrreducible]
    (hρ : ∀g v, ‖ρ g v‖=‖v‖) (w : Equiv.Perm (Fin n) → ℂ) {q : ℕ} (hq : 0 < q) :
    TraceHolder.matrixMoment q (isotypicProjection p ρ*signedAverage p w)=
      (Module.finrank ℂ (IntertwiningMap ρ (hilbertTensorRep p n)):ℝ)*evenMoment q (groupAverage ρ w) := by
  unfold TraceHolder.matrixMoment
  rw [projected_gram_power _ _ (isotypicProjection_psd p ρ).isHermitian
    (projectionMatrix_idempotent _) (isotypicProjection_commutes_average p ρ w) hq]
  rw [← trace_toEuclideanLinear]
  simp only [Matrix.toLpLin_mul_same,← Module.End.mul_eq_comp,euclidean_pow,
    Matrix.star_eq_conjTranspose,Matrix.toEuclideanLin_conjTranspose_eq_adjoint,signedAverage_linear]
  have hP : (isotypicProjection p ρ).toEuclideanLin=
      (isotypicSpan ρ (hilbertTensorRep p n)).starProjection.toLinearMap := by
    rw [hilbert_isotypic_eq]; exact projectionMatrix_linear _
  rw [hP]
  have hc := even_compatible ρ (hilbertTensorRep p n) w hρ (hilbertTensorRep_unitary p) q
  rw [trace_mul_projection _ _ (isotypic_invariant_of_compatible ρ _ _ _ hc),
    isotypic_trace ρ _ _ _ hc]
  simp only [evenMoment,Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero]

lemma hilbert_multiplicity_bound (p : A → Bool)
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) [ρ.IsIrreducible] :
    Module.finrank ℂ (IntertwiningMap ρ (hilbertTensorRep p n)) ≤ (n+1)^((Fintype.card A)^2) := by
  have hd : 0 < Module.finrank ℂ V := by
    let : Nontrivial ρ.asModule := IsSimpleModule.nontrivial ℂ[Equiv.Perm (Fin n)] ρ.asModule
    rw [← ρ.asModuleEquiv.finrank_eq]
    exact Module.finrank_pos
  have h := isotypicSpan_rank_bound p ρ
  rw [← hilbertSubspace_finrank,← hilbert_isotypic_eq p ρ,isotypicSpan_finrank_eq] at h
  exact Nat.le_of_mul_le_mul_left h hd

theorem local_projected_moment_le (p : A → Bool)
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) [ρ.IsIrreducible]
    (hρ : ∀g v, ‖ρ g v‖=‖v‖) (w : Equiv.Perm (Fin n) → ℂ) {q : ℕ} (hq : 0 < q) :
    TraceHolder.matrixMoment q (isotypicProjection p ρ*signedAverage p w) ≤
      (n+1:ℝ)^((Fintype.card A)^2)*evenMoment q (groupAverage ρ w) := by
  rw [local_projected_moment p ρ hρ w hq]
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast hilbert_multiplicity_bound p ρ
  · exact (Complex.nonneg_iff.mp (positive_pow (LinearMap.isPositive_adjoint_comp_self _) q).trace_nonneg).1

end Signed
end BinaryCoordinateSweeps

end

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_SampleMoment
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Irrep Representation TraceHolder Density

lemma matrixMoment_linear {I : Type*} [Fintype I] [DecidableEq I]
    (q : ℕ) (M : Matrix I I ℂ) : matrixMoment q M=evenMoment q M.toEuclideanLin := by
  unfold matrixMoment evenMoment
  rw [← trace_toEuclideanLinear]
  simp only [euclidean_pow,Matrix.toLpLin_mul_same,←Module.End.mul_eq_comp,
    Matrix.star_eq_conjTranspose,Matrix.toEuclideanLin_conjTranspose_eq_adjoint]

namespace Signed
variable {A X : Type*} [Fintype A] [DecidableEq A] [Fintype X] {N : ℕ}
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

lemma sampleMatrix_linear (p : A → Bool) (w : X → ℂ) (f : X → Equiv.Perm (Fin N)) :
    (sampleMatrix p w f).toEuclideanLin=∑x, w x • hilbertTensorRep p N (f x) := by
  simp only [sampleMatrix,map_sum,map_smul,actionMatrix_linear]

lemma sampleMatrix_average (p : A → Bool) (w : X → ℂ) (f : X → Equiv.Perm (Fin N)) :
    sampleMatrix p w f=signedAverage p (finitePush w f) := by
  exact (finitePush_expectation w f (actionMatrix p)).symm

lemma sample_projected_moment (p : A → Bool)
    (ρ : Representation ℂ (Equiv.Perm (Fin N)) V) [ρ.IsIrreducible]
    (hρ : ∀g v, ‖ρ g v‖=‖v‖) (w : X → ℂ) (f : X → Equiv.Perm (Fin N)) {q : ℕ} (hq : 0<q) :
    matrixMoment q (isotypicProjection p ρ*sampleMatrix p w f)=
      (Module.finrank ℂ (IntertwiningMap ρ (hilbertTensorRep p N)):ℝ)*
        evenMoment q (∑x, w x • ρ (f x)) := by
  rw [sampleMatrix_average,local_projected_moment p ρ hρ _ hq]
  rw [groupAverage,finitePush_expectation]

lemma sampleMoment_le_projected (p : A → Bool)
    (ρ : Representation ℂ (Equiv.Perm (Fin N)) V) [ρ.IsIrreducible]
    (hρ : ∀g v, ‖ρ g v‖=‖v‖)
    (hocc : 0<Module.finrank ℂ (IntertwiningMap ρ (hilbertTensorRep p N)))
    (w : X → ℂ) (f : X → Equiv.Perm (Fin N)) {q : ℕ} (hq : 0<q) :
    evenMoment q (∑x, w x • ρ (f x))≤
      matrixMoment q (isotypicProjection p ρ*sampleMatrix p w f) := by
  rw [sample_projected_moment p ρ hρ w f hq]
  exact le_mul_of_one_le_left (evenMoment_nonneg _ _) (by exact_mod_cast hocc)

end Signed
end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Trajectories_PathExtension
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable

lemma gridSize_pos {b : ℕ} (bits : Fin b → ℕ) : 0 < gridSize bits := by
  unfold gridSize
  exact Finset.prod_pos (fun j _ => Nat.pow_pos (by norm_num))

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_GridSplit
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
variable {m n h : ℕ} (bits : Fin (m+n) → ℕ)

lemma size_split : gridSize bits=gridSize (leftBits bits)*gridSize (rightBits bits) := by
  rw [← card_gridSlot, Fintype.card_congr (slotEquiv bits),Fintype.card_prod,
    card_gridSlot,card_gridSlot]

end BinaryCoordinateSweeps.GridSplit

end

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_GridSplitWeights
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
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

namespace BinaryCoordinateSweeps.GridSplit
attribute [local instance] Classical.propDecidable
variable {m n h : ℕ} (bits : Fin (m+n) → ℕ) (H : PathFamily bits h)

lemma eventWeight_split (z : ℝ) (g : GridChoices bits) :
    (if pathEvent H g then gridWeight bits z g else 0) =
      (∏y, if pathEvent (rowFamily bits H y) (rowChoices bits g y) then
        gridWeight (leftBits bits) z (rowChoices bits g y) else 0) *
      (∏x, if pathEvent (columnFamily bits H x) (columnChoices bits g x) then
        gridWeight (rightBits bits) z (columnChoices bits g x) else 0) := by
  classical
  rw [pathEvent_split,gridWeight_split]
  simp only [Fintype.prod_ite_zero]
  split_ifs <;> simp_all

theorem conditionalNormalizer_split (z : ℝ) :
    conditionalNormalizer H z =
      (∏y, conditionalNormalizer (rowFamily bits H y) z) *
      (∏x, conditionalNormalizer (columnFamily bits H x) z) := by
  classical
  let : Fintype (GridChoices (leftBits bits)) := inferInstance
  let : Fintype (GridChoices (rightBits bits)) := inferInstance
  have he := (choicesEquiv bits).symm.sum_comp
    (fun g => if pathEvent H g then gridWeight bits z g else 0)
  have hs (LR : (GridSlot (rightBits bits) → GridChoices (leftBits bits)) ×
      (GridSlot (leftBits bits) → GridChoices (rightBits bits))) :
      (if pathEvent H ((choicesEquiv bits).symm LR) then
        gridWeight bits z ((choicesEquiv bits).symm LR) else 0) =
        (∏y, if pathEvent (rowFamily bits H y) (LR.1 y) then
          gridWeight (leftBits bits) z (LR.1 y) else 0) *
        (∏x, if pathEvent (columnFamily bits H x) (LR.2 x) then
          gridWeight (rightBits bits) z (LR.2 x) else 0) := by
    classical
    rw [eventWeight_split,rowChoices_symm,columnChoices_symm]
  simp_rw [hs] at he
  unfold conditionalNormalizer
  rw [← he,Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  congr 1
  · exact (Fintype.prod_sum (fun (y : GridSlot (rightBits bits)) (g : GridChoices (leftBits bits)) =>
      if pathEvent (rowFamily bits H y) g then gridWeight (leftBits bits) z g else 0)).symm
  · exact (Fintype.prod_sum (fun (x : GridSlot (leftBits bits)) (g : GridChoices (rightBits bits)) =>
      if pathEvent (columnFamily bits H x) g then gridWeight (rightBits bits) z g else 0)).symm

theorem conditionalChoiceWeight_split (z : ℝ) (g : ConditionalChoices H) :
    conditionalChoiceWeight H z g =
      (∏y, conditionalChoiceWeight (rowFamily bits H y) z
        ((conditionalChoicesEquiv bits H g).1 y)) *
      (∏x, conditionalChoiceWeight (columnFamily bits H x) z
        ((conditionalChoicesEquiv bits H g).2 x)) := by
  classical
  unfold conditionalChoiceWeight
  rw [gridWeight_split,conditionalNormalizer_split]
  simp only [Finset.prod_div_distrib,conditionalChoicesEquiv]
  exact mul_div_mul_comm _ _ _ _

end BinaryCoordinateSweeps.GridSplit

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
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_GridSplitFree
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.GridSplit
variable {m n h : ℕ} (bits : Fin (m+n) → ℕ) (H : PathFamily bits h)

lemma remainingBijection_split (g : ConditionalChoices H) :
    remainingBijection H g.val g.property =
      (rowRemaining bits H ((conditionalChoicesEquiv bits H g).1)).trans
        (columnRemaining bits H ((conditionalChoicesEquiv bits H g).2)) := by
  apply Equiv.ext
  intro a
  apply Subtype.ext
  change gridSweep bits g.val a.val =
    (columnRemaining bits H ((conditionalChoicesEquiv bits H g).2)
      (rowRemaining bits H ((conditionalChoicesEquiv bits H g).1) a)).val
  rw [columnRemaining_val,rowRemaining_val,left_join,right_join]
  apply (slotEquiv bits).injective
  have he := Equiv.congr_fun (gridSweep_split bits g.val) (slotEquiv bits a.val)
  simpa [conditionalChoicesEquiv,Equiv.permCongr_apply,rowPerm,columnPerm,
    slotEquiv] using he

end BinaryCoordinateSweeps.GridSplit

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.GridSplit
open Irrep Representation

variable {m n h : ℕ} (bits : Fin (m+n) → ℕ) (H : PathFamily bits h)

theorem remainingPerm_factor (g : ConditionalChoices H) :
    remainingPerm H g.val g.property = framePermutation bits H *
      (rowReference bits H).symm.permCongr
        (columnRelative bits H ((conditionalChoicesEquiv bits H g).2)) *
      rowRelative bits H ((conditionalChoicesEquiv bits H g).1) := by
  unfold remainingPerm
  rw [remainingBijection_split]
  apply Equiv.ext
  intro x
  simp [framePermutation,rowRelative,columnRelative,Equiv.permCongr_apply]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  (ρ : Representation ℂ (Equiv.Perm (FreeSlot H 0)) V)

omit [FiniteDimensional ℂ V] in
theorem groupAverage_split (z : ℝ) :
    groupAverage ρ (fun a => (conditionalGroupLaw H z a:ℂ)) =
      ρ (framePermutation bits H) * columnAverage bits H ρ z * rowAverage bits H ρ z := by
  rw [groupAverage_conditional,← Equiv.sum_comp (conditionalChoicesEquiv bits H).symm]
  simp_rw [conditionalChoiceWeight_split,remainingPerm_factor,
    Equiv.apply_symm_apply,map_mul,Complex.ofReal_mul]
  rw [Fintype.sum_prod_type]
  unfold columnAverage rowAverage
  simp only [Finset.mul_sum,Finset.sum_mul,smul_mul_assoc,mul_smul_comm,
    Finset.smul_sum,smul_smul,Complex.ofReal_prod]

end BinaryCoordinateSweeps.GridSplit

end

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

omit [∀ index, DecidableEq (A index)] in
lemma piTensorMatrices_trace (M : ∀ i, Matrix (A i) (A i) ℂ) :
    (piTensorMatrices M).trace = ∏ i, (M i).trace := by
  simp only [Matrix.trace,Matrix.diag,piTensorMatrices]
  exact (Fintype.prod_sum (fun i a => M i a a)).symm

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

end BinaryCoordinateSweeps.Density

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

lemma actionMatrix_mul (p : A → Bool) (g h : Equiv.Perm (Fin n)) :
    actionMatrix p (g*h)=actionMatrix p g*actionMatrix p h := by
  change LinearMap.toMatrix' ((tensorRep p n) (g*h))=_
  rw [map_mul]
  exact LinearMap.toMatrix'_comp _ _

lemma actionMatrix_one (p : A → Bool) : actionMatrix (n:=n) p 1=1 := by
  change LinearMap.toMatrix' ((tensorRep p n) 1)=_
  rw [map_one]
  exact LinearMap.toMatrix'_id

lemma actionMatrix_inv (p : A → Bool) (g : Equiv.Perm (Fin n)) :
    actionMatrix p g⁻¹=(actionMatrix p g).conjTranspose := by
  calc
    _ = actionMatrix p g⁻¹*(actionMatrix p g*(actionMatrix p g).conjTranspose) := by
      rw [actionMatrix_unitary,mul_one]
    _ = _ := by rw [← mul_assoc,← actionMatrix_mul,inv_mul_cancel,actionMatrix_one,one_mul]

lemma signedConj_mul (p : A → Bool) (g : Equiv.Perm (Fin n))
    (M L : Matrix (Fin n → A) (Fin n → A) ℂ) :
    signedConj p g (M*L)=signedConj p g M*signedConj p g L := by
  unfold signedConj
  simp only [mul_assoc,← mul_assoc (actionMatrix p g).conjTranspose (actionMatrix p g),
    actionMatrix_star_mul,one_mul]

lemma signedConj_psd (p : A → Bool) (g : Equiv.Perm (Fin n))
    (M : Matrix (Fin n → A) (Fin n → A) ℂ) (hM : M.PosSemidef) :
    (signedConj p g M).PosSemidef := hM.mul_mul_conjTranspose_same _

end BinaryCoordinateSweeps.Signed

end

open scoped BigOperators Classical Kronecker
open Matrix

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

end BinaryCoordinateSweeps.Signed

end

open scoped BigOperators Classical ComplexOrder
open Matrix

namespace BinaryCoordinateSweeps
open Density TraceHolder Irrep Representation

lemma piTensorMatrices_pow {I : Type*} [Fintype I] [DecidableEq I]
    {A : I → Type*} [∀i, Fintype (A i)] [∀i, DecidableEq (A i)]
    (M : ∀i, Matrix (A i) (A i) ℂ) (q : ℕ) :
    (piTensorMatrices M)^q=piTensorMatrices (fun i => M i^q) := by
  induction q with
  | zero => simp only [pow_zero,piTensorMatrices_one]
  | succ q ih => rw [pow_succ,ih,piTensorMatrices_mul]; simp only [pow_succ]

lemma gram_trace_real {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) (q : ℕ) : ((matrixMoment q M:ℝ):ℂ)=((star M*M)^q).trace := by
  have hh := ((Matrix.posSemidef_conjTranspose_mul_self M).pow q).trace_nonneg
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im, Matrix.star_eq_conjTranspose] using (Complex.nonneg_iff.mp hh).2

lemma tensor_matrixMoment {I : Type*} [Fintype I] [DecidableEq I]
    {A : I → Type*} [∀i, Fintype (A i)] [∀i, DecidableEq (A i)]
    (M : ∀i, Matrix (A i) (A i) ℂ) (q : ℕ) :
    matrixMoment q (piTensorMatrices M)=∏i, matrixMoment q (M i) := by
  unfold matrixMoment
  rw [Matrix.star_eq_conjTranspose,piTensorMatrices_star,piTensorMatrices_mul,
    piTensorMatrices_pow,piTensorMatrices_trace]
  have he (i : I) : (((M i).conjTranspose*M i)^q).trace=
      ((matrixMoment q (M i):ℝ):ℂ) := (gram_trace_real (M i) q).symm
  simp_rw [he]
  rw [← Complex.ofReal_prod,Complex.ofReal_re]
  rfl

lemma matrixMoment_reindex {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (M : Matrix J J ℂ) (q : ℕ) :
    matrixMoment q (M.submatrix e e)=matrixMoment q M := by
  have hp (B : Matrix J J ℂ) : (B.submatrix e e)^q=(B^q).submatrix e e := by
    induction q with
    | zero => simp only [pow_zero,Matrix.submatrix_one_equiv]
    | succ q ih => rw [pow_succ,ih,Matrix.submatrix_mul_equiv,← pow_succ]
  unfold matrixMoment
  rw [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv,hp]
  congr 1
  exact e.sum_comp (fun i => ((M.conjTranspose*M)^q) i i)

namespace Signed
variable {I A : Type*} [Fintype I] [LinearOrder I]
  [Fintype A] [DecidableEq A] {n : I → ℕ} {N : ℕ}
  {V : I → Type*} [∀i, NormedAddCommGroup (V i)]
  [∀i, InnerProductSpace ℂ (V i)] [∀i, FiniteDimensional ℂ (V i)]

lemma blockAverage_tensor (e : (Σₗ i, Fin (n i)) ≃o Fin N) (p : A → Bool)
    (w : ∀i, Equiv.Perm (Fin (n i)) → ℂ) :
    blockAverage e p w=(piTensorMatrices (fun i => signedAverage p (w i))).submatrix
      (blockWords e) (blockWords e) := by
  unfold blockAverage signedAverage
  rw [piTensorMatrices_sum,submatrix_sum_eq]
  apply Finset.sum_congr rfl
  intro g _
  rw [piTensorMatrices_smul,Matrix.submatrix_smul]
  congr 1
  exact actionMatrix_blocks e g p

theorem block_projected_moment_le (e : (Σₗ i, Fin (n i)) ≃o Fin N) (p : A → Bool)
    (ρ : ∀i, Representation ℂ (Equiv.Perm (Fin (n i))) (V i))
    [∀i, (ρ i).IsIrreducible] (hρ : ∀i g v, ‖ρ i g v‖=‖v‖)
    (w : ∀i, Equiv.Perm (Fin (n i)) → ℂ) {q : ℕ} (hq : 0 < q) :
    matrixMoment q (blockProjection e p ρ*blockAverage e p w) ≤
      ∏i, (n i+1:ℝ)^((Fintype.card A)^2)*evenMoment q (groupAverage (ρ i) (w i)) := by
  rw [blockAverage_tensor,blockProjection,Matrix.submatrix_mul_equiv,
    piTensorMatrices_mul,matrixMoment_reindex,tensor_matrixMoment]
  apply Finset.prod_le_prod
  · intro i _; exact matrixMoment_nonneg _ _
  · intro i _; exact local_projected_moment_le p (ρ i) (hρ i) (w i) hq

end Signed
end BinaryCoordinateSweeps

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

end BinaryCoordinateSweeps.Signed

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_GroupedMoments
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical ComplexOrder
open scoped Matrix.Norms.L2Operator
open Matrix

namespace BinaryCoordinateSweeps.Signed
open Density Irrep Representation TraceHolder

variable {A I : Type*} [Fintype A] [DecidableEq A] [Fintype I] [LinearOrder I]
  {n : I → ℕ} {N : ℕ}

lemma action_unitary (p : A → Bool) (g : Equiv.Perm (Fin N)) :
    actionMatrix p g ∈ Matrix.unitaryGroup (Fin N → A) ℂ := by
  exact ⟨actionMatrix_star_mul p g,actionMatrix_unitary p g⟩

lemma matrixMoment_signedConj (p : A → Bool) (g : Equiv.Perm (Fin N))
    (q : ℕ) (M : Matrix (Fin N → A) (Fin N → A) ℂ) :
    matrixMoment q (signedConj p g M)=matrixMoment q M :=
  matrixMoment_unitary_conj q ⟨actionMatrix p g,action_unitary p g⟩ M

lemma groupedAverage_law (e : (Σₗ i, Fin (n i)) ≃o Fin N) (g : Equiv.Perm (Fin N))
    (p : A → Bool) (w : ∀i, Equiv.Perm (Fin (n i)) → ℂ) :
    groupedAverage e g p w =
      ∑a : ∀i, Equiv.Perm (Fin (n i)),
        (∏i, w i (a i)) • actionMatrix p (g*blockPerm e a*g⁻¹) := by
  simp only [groupedAverage,signedConj,blockAverage,Finset.mul_sum,Finset.sum_mul,
    mul_smul_comm,smul_mul_assoc,actionMatrix_mul,actionMatrix_inv]

variable {V : I → Type*} [∀i, NormedAddCommGroup (V i)]
  [∀i, InnerProductSpace ℂ (V i)] [∀i, FiniteDimensional ℂ (V i)]

theorem grouped_projected_moment_le (e : (Σₗ i, Fin (n i)) ≃o Fin N)
    (g : Equiv.Perm (Fin N)) (p : A → Bool)
    (ρ : ∀i, Representation ℂ (Equiv.Perm (Fin (n i))) (V i))
    [∀i, (ρ i).IsIrreducible] (hρ : ∀i a v, ‖ρ i a v‖=‖v‖)
    (w : ∀i, Equiv.Perm (Fin (n i)) → ℂ) {q : ℕ} (hq : 0<q) :
    matrixMoment q (groupedProjection e g p ρ*groupedAverage e g p w) ≤
      ∏i, (n i+1:ℝ)^((Fintype.card A)^2)*evenMoment q (groupAverage (ρ i) (w i)) := by
  rw [groupedProjection,groupedAverage,←signedConj_mul,matrixMoment_signedConj]
  exact block_projected_moment_le e p ρ hρ w hq

omit [∀i, FiniteDimensional ℂ (V i)] in
lemma blockProjection_commutes_average (e : (Σₗ i, Fin (n i)) ≃o Fin N)
    (p : A → Bool) (ρ : ∀i, Representation ℂ (Equiv.Perm (Fin (n i))) (V i))
    (w : ∀i, Equiv.Perm (Fin (n i)) → ℂ) :
    blockProjection e p ρ*blockAverage e p w=blockAverage e p w*blockProjection e p ρ := by
  rw [blockAverage_tensor,blockProjection,Matrix.submatrix_mul_equiv,
    Matrix.submatrix_mul_equiv,piTensorMatrices_mul,piTensorMatrices_mul]
  congr 2
  funext i
  exact isotypicProjection_commutes_average p (ρ i) (w i)

omit [∀i, FiniteDimensional ℂ (V i)] in
lemma groupedProjection_commutes_average (e : (Σₗ i, Fin (n i)) ≃o Fin N)
    (g : Equiv.Perm (Fin N)) (p : A → Bool)
    (ρ : ∀i, Representation ℂ (Equiv.Perm (Fin (n i))) (V i))
    (w : ∀i, Equiv.Perm (Fin (n i)) → ℂ) :
    groupedProjection e g p ρ*groupedAverage e g p w=
      groupedAverage e g p w*groupedProjection e g p ρ := by
  rw [groupedProjection,groupedAverage,←signedConj_mul,←signedConj_mul,
    blockProjection_commutes_average]

omit [∀ i, FiniteDimensional ℂ (V i)] in
lemma groupedProjection_norm_le (e : (Σₗ i, Fin (n i)) ≃o Fin N)
    (g : Equiv.Perm (Fin N)) (p : A → Bool)
    (ρ : ∀i, Representation ℂ (Equiv.Perm (Fin (n i))) (V i)) :
    ‖groupedProjection e g p ρ‖ ≤ 1 := by
  exact IsStarProjection.norm_le _ ⟨groupedProjection_idempotent e g p ρ,
    (groupedProjection_psd e g p ρ).isHermitian⟩

lemma blockActive_projection_sum (e : (Σₗ i, Fin (n i)) ≃o Fin N) (p : A → Bool) :
    (∑a : ∀i, ActiveType p (n i),
      blockProjection e p (fun i => Young.partitionHilbertRep (a i).val))=1 := by
  unfold blockProjection
  rw [←submatrix_sum_eq]
  have hs := piTensorMatrices_sum (fun i (a : ActiveType p (n i)) =>
    isotypicProjection p (Young.partitionHilbertRep a.val))
  rw [←hs]
  have he : (fun i => ∑a : ActiveType p (n i),
      isotypicProjection p (Young.partitionHilbertRep a.val)) = (fun i => (1 : Matrix (Fin (n i) → A) (Fin (n i) → A) ℂ)) := by
    funext i
    exact active_typeProjection_sum p (n i)
  rw [he,piTensorMatrices_one,Matrix.submatrix_one_equiv]

lemma groupedActive_projection_sum (e : (Σₗ i, Fin (n i)) ≃o Fin N)
    (g : Equiv.Perm (Fin N)) (p : A → Bool) :
    (∑a : ∀i, ActiveType p (n i),
      groupedProjection e g p (fun i => Young.partitionHilbertRep (a i).val))=1 := by
  unfold groupedProjection signedConj
  rw [←Finset.sum_mul,←Finset.mul_sum,blockActive_projection_sum,mul_one,actionMatrix_unitary]

lemma blockActive_card (p : A → Bool) :
    Fintype.card (∀i, ActiveType p (n i))≤∏i,(n i+1)^((Fintype.card A)^2) := by
  rw [Fintype.card_pi]
  exact Finset.prod_le_prod' (fun i _ => activeType_card p (n i))

end BinaryCoordinateSweeps.Signed

end

open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_GroupingGeometry
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Signed
variable {I : Type*} [Fintype I] [LinearOrder I]
  {X : I → Type*} [∀i,Fintype (X i)] {N : ℕ}

lemma groupingPerm_apply (e : (Σi, X i) ≃ Fin N) (i : I) (a : Fin (Fintype.card (X i))) :
    groupingPerm e (groupingOrder e (toLex ⟨i,a⟩))=e ⟨i,(Fintype.equivFin (X i)).symm a⟩ := by
  simp [groupingPerm,Equiv.sigmaCongrRight]

@[simp] lemma groupingPerm_inv_apply (e : (Σi, X i) ≃ Fin N) (i : I) (x : X i) :
    (groupingPerm e)⁻¹ (e ⟨i,x⟩)=groupingOrder e (toLex ⟨i,Fintype.equivFin (X i) x⟩) := by
  apply (groupingPerm e).injective
  rw [groupingPerm_apply,Equiv.symm_apply_apply]
  exact (groupingPerm e).apply_symm_apply _

lemma grouping_groupOf (e : (Σi, X i) ≃ Fin N) (t : Fin N) :
    groupOf (groupingOrder e) (groupingPerm e) t=(e.symm t).1 := by
  simp [groupOf,groupingPerm,Equiv.sigmaCongrRight]

lemma grouping_permutation (e : (Σi, X i) ≃ Fin N)
    (a : ∀i, Equiv.Perm (X i)) :
    e.permCongr (Equiv.Perm.sigmaCongrRight a)=
      groupingPerm e*blockPerm (groupingOrder e)
        (fun i => (Fintype.equivFin (X i)).permCongr (a i))*(groupingPerm e)⁻¹ := by
  apply Equiv.ext
  intro t
  obtain ⟨⟨i,x⟩,rfl⟩ := e.surjective t
  simp only [Equiv.Perm.mul_apply,groupingPerm_inv_apply,blockPerm_apply,groupingPerm_apply,
    Equiv.permCongr_apply,Equiv.symm_apply_apply]
  rfl

end BinaryCoordinateSweeps.Signed

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_GridChildAverage
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Irrep Representation

lemma finitePush_conditional {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (z : ℝ) (a : Equiv.Perm (FreeSlot H 0)) :
    finitePush (fun g : ConditionalChoices H => (conditionalChoiceWeight H z g:ℂ))
      (fun g => remainingPerm H g.val g.property) a = (conditionalGroupLaw H z a:ℂ) := by
  simp only [finitePush,conditionalGroupLaw,Complex.ofReal_sum,apply_ite,Complex.ofReal_zero]

lemma independentConditional_expectation {I : Type*} [Fintype I]
    (b h : I → ℕ) (bits : ∀i, Fin (b i) → ℕ) (H : ∀i, PathFamily (bits i) (h i))
    {V : Type*} [AddCommMonoid V] [Module ℂ V] (z : ℝ)
    (F : (∀i, Equiv.Perm (FreeSlot (H i) 0)) → V) :
    (∑a, (∏i, (conditionalGroupLaw (H i) z (a i):ℂ)) • F a) =
      ∑g : ∀i, ConditionalChoices (H i),
        (∏i, (conditionalChoiceWeight (H i) z (g i):ℂ)) •
          F (fun i => remainingPerm (H i) (g i).val (g i).property) := by
  have he := independentPush_expectation
    (fun i (g : ConditionalChoices (H i)) => (conditionalChoiceWeight (H i) z g:ℂ))
    (fun i (g : ConditionalChoices (H i)) => remainingPerm (H i) g.val g.property) F
  simpa only [finitePush_conditional] using he

private lemma sigma_relative {I X Y : Type*} {A B : I → Type*}
    (e : X ≃ Σ i, A i) (f : Y ≃ Σ i, B i) (g r : ∀ i, A i ≃ B i) :
    (e.trans ((Equiv.sigmaCongrRight g).trans f.symm)).trans
      (e.trans ((Equiv.sigmaCongrRight r).trans f.symm)).symm =
      e.symm.permCongr (Equiv.Perm.sigmaCongrRight (fun i => (g i).trans (r i).symm)) := by
  ext x
  simp [Equiv.permCongr_apply, Equiv.sigmaCongrRight, Equiv.Perm.sigmaCongrRight]

namespace GridSplit
variable {m n h : ℕ} (bits : Fin (m+n) → ℕ) (H : PathFamily bits h)

lemma rowRelative_sigma (g : RowSamples bits H) :
    rowRelative bits H g = (rowInputEquiv bits H).symm.permCongr
      (Equiv.Perm.sigmaCongrRight (fun y =>
        remainingPerm (rowFamily bits H y) (g y).val (g y).property)) := by
  exact sigma_relative (rowFreeEquiv bits H 0) (rowFreeEquiv bits H (Fin.last m))
    (fun y => remainingBijection (rowFamily bits H y) (g y).val (g y).property)
    (fun y => freeIdentification (rowFamily bits H y))

lemma columnRelative_sigma (g : ColumnSamples bits H) :
    columnRelative bits H g = (columnFreeEquiv bits H 0).symm.permCongr
      (Equiv.Perm.sigmaCongrRight (fun x =>
        remainingPerm (columnFamily bits H x) (g x).val (g x).property)) := by
  exact sigma_relative (columnFreeEquiv bits H 0) (columnFreeEquiv bits H (Fin.last n))
    (fun x => remainingBijection (columnFamily bits H x) (g x).val (g x).property)
    (fun x => freeIdentification (columnFamily bits H x))

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  (ρ : Representation ℂ (Equiv.Perm (FreeSlot H 0)) V)

omit [FiniteDimensional ℂ V] in
theorem rowAverage_child_laws (z : ℝ) :
    rowAverage bits H ρ z =
      ∑a : ∀y, Equiv.Perm (FreeSlot (rowFamily bits H y) 0),
        (∏y, (conditionalGroupLaw (rowFamily bits H y) z (a y):ℂ)) •
          ρ ((rowInputEquiv bits H).symm.permCongr (Equiv.Perm.sigmaCongrRight a)) := by
  trans ∑g : RowSamples bits H,
    (∏y, (conditionalChoiceWeight (rowFamily bits H y) z (g y):ℂ)) •
      ρ ((rowInputEquiv bits H).symm.permCongr (Equiv.Perm.sigmaCongrRight
        (fun y => remainingPerm (rowFamily bits H y) (g y).val (g y).property)))
  · unfold rowAverage
    apply Finset.sum_congr rfl
    intro g _
    rw [rowRelative_sigma]
  · let F : (∀y, Equiv.Perm (FreeSlot (rowFamily bits H y) 0)) → Module.End ℂ V :=
      fun a => ρ ((rowInputEquiv bits H).symm.permCongr (Equiv.Perm.sigmaCongrRight a))
    have he := independentConditional_expectation (I := GridSlot (rightBits bits)) (fun _ => m)
      (fun y => Fintype.card (RowLabels bits H y)) (fun _ => leftBits bits) (rowFamily bits H) z
      F
    apply Eq.symm
    refine Eq.trans ?_ (Eq.trans he ?_)
    all_goals
      apply Finset.sum_congr
      · ext g; simp only [Finset.mem_univ]
      · intro g _; rfl

omit [FiniteDimensional ℂ V] in
theorem columnAverage_child_laws (z : ℝ) :
    columnAverage bits H ρ z =
      ∑a : ∀x, Equiv.Perm (FreeSlot (columnFamily bits H x) 0),
        (∏x, (conditionalGroupLaw (columnFamily bits H x) z (a x):ℂ)) •
          ρ ((rowReference bits H).symm.permCongr
            ((columnFreeEquiv bits H 0).symm.permCongr (Equiv.Perm.sigmaCongrRight a))) := by
  trans ∑g : ColumnSamples bits H,
    (∏x, (conditionalChoiceWeight (columnFamily bits H x) z (g x):ℂ)) •
      ρ ((rowReference bits H).symm.permCongr
        ((columnFreeEquiv bits H 0).symm.permCongr (Equiv.Perm.sigmaCongrRight
          (fun x => remainingPerm (columnFamily bits H x) (g x).val (g x).property))))
  · unfold columnAverage
    apply Finset.sum_congr rfl
    intro g _
    rw [columnRelative_sigma]
  · let F : (∀x, Equiv.Perm (FreeSlot (columnFamily bits H x) 0)) → Module.End ℂ V :=
      fun a => ρ ((rowReference bits H).symm.permCongr
        ((columnFreeEquiv bits H 0).symm.permCongr (Equiv.Perm.sigmaCongrRight a)))
    have he := independentConditional_expectation (I := GridSlot (leftBits bits)) (fun _ => n)
      (fun x => Fintype.card (ColumnLabels bits H x)) (fun _ => rightBits bits) (columnFamily bits H) z
      F
    apply Eq.symm
    refine Eq.trans ?_ (Eq.trans he ?_)
    all_goals
      apply Finset.sum_congr
      · ext g; simp only [Finset.mem_univ]
      · intro g _; rfl

end GridSplit
end BinaryCoordinateSweeps

namespace BinaryCoordinateSweeps.GridSplit
open Signed

variable {m n h : ℕ} (bits : Fin (m+n) → ℕ) (H : PathFamily bits h)

lemma rowReference_right (a : FreeSlot H 0) :
    rightSlot bits (rowReference bits H a).val=rightSlot bits a.val := by
  exact right_join bits _ _

lemma rowGrouping_first (t : Fin (junctionSize bits H)) :
    ((rowGrouping bits H).symm t).1=(physicalBoard bits H t).1 := by
  change rightSlot bits ((rowReference bits H).symm ((junctionEnum bits H).symm t)).val =
    rightSlot bits ((junctionEnum bits H).symm t).val
  symm
  simpa only [Equiv.apply_symm_apply] using
    rowReference_right bits H ((rowReference bits H).symm ((junctionEnum bits H).symm t))

lemma columnGrouping_first (t : Fin (junctionSize bits H)) :
    ((columnGrouping bits H).symm t).1=(physicalBoard bits H t).2 := rfl

attribute [local instance] OAI.BinaryCoordinateSweeps.GridSplit.rowOrder
attribute [local instance] OAI.BinaryCoordinateSweeps.GridSplit.columnOrder
lemma physicalBoard_row (t : Fin (junctionSize bits H)) :
    groupOf (groupingOrder (rowGrouping bits H)) (groupingPerm (rowGrouping bits H)) t=
      (physicalBoard bits H t).1 := by
  rw [grouping_groupOf,rowGrouping_first]

lemma physicalBoard_column (t : Fin (junctionSize bits H)) :
    groupOf (groupingOrder (columnGrouping bits H)) (groupingPerm (columnGrouping bits H)) t=
      (physicalBoard bits H t).2 := by
  rw [grouping_groupOf,columnGrouping_first]

lemma junctionSize_eq : junctionSize bits H=gridSize bits-h := by
  exact card_freeSlot H _

end BinaryCoordinateSweeps.GridSplit

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Signed
variable {I A : Type*} [Fintype I] [LinearOrder I] [Fintype A] [DecidableEq A]
  {X : I → Type*} [∀i,Fintype (X i)] {N : ℕ}

theorem groupedAverage_literal (e : (Σi, X i) ≃ Fin N) (p : A → Bool)
    (w : ∀i, Equiv.Perm (X i) → ℂ) :
    groupedAverage (groupingOrder e) (groupingPerm e) p
      (fun i a => w i ((Fintype.equivFin (X i)).symm.permCongr a)) =
      ∑a : ∀i, Equiv.Perm (X i), (∏i, w i (a i)) •
        actionMatrix p (e.permCongr (Equiv.Perm.sigmaCongrRight a)) := by
  rw [groupedAverage_law,← (finBlockPermEquiv (X:=X)).sum_comp]
  apply Finset.sum_congr rfl
  intro a _
  rw [grouping_permutation]
  have he (i : I) : (Fintype.equivFin (X i)).symm.permCongr
      (finBlockPermEquiv a i)=a i := by
    ext x
    simp [finBlockPermEquiv,Equiv.permCongr_apply]
  simp only [he]
  rfl

lemma groupedAverage_literal_linear (e : (Σi, X i) ≃ Fin N) (p : A → Bool)
    (w : ∀i, Equiv.Perm (X i) → ℂ) :
    (groupedAverage (groupingOrder e) (groupingPerm e) p
      (fun i a => w i ((Fintype.equivFin (X i)).symm.permCongr a))).toEuclideanLin =
      ∑a : ∀i, Equiv.Perm (X i), (∏i, w i (a i)) •
        hilbertTensorRep p N (e.permCongr (Equiv.Perm.sigmaCongrRight a)) := by
  rw [groupedAverage_literal]
  simp only [map_sum,map_smul,actionMatrix_linear]

end BinaryCoordinateSweeps.Signed

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_GridBoardAverage
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.GridSplit
open Signed Irrep Representation

variable {m n h : ℕ} (bits : Fin (m+n) → ℕ) (H : PathFamily bits h)
  {A : Type*} [Fintype A] [DecidableEq A]

lemma column_perm_to_junction (a : ∀x, Equiv.Perm (FreeSlot (columnFamily bits H x) 0)) :
    (inputToJunction bits H).permCongr
      ((rowReference bits H).symm.permCongr
        ((columnFreeEquiv bits H 0).symm.permCongr (Equiv.Perm.sigmaCongrRight a)))=
      (columnGrouping bits H).permCongr (Equiv.Perm.sigmaCongrRight a) := by
  ext t
  simp [inputToJunction,columnGrouping,Equiv.permCongr_apply]

attribute [local instance] OAI.BinaryCoordinateSweeps.GridSplit.instLinearOrderGridSlotRightBits
attribute [local instance] OAI.BinaryCoordinateSweeps.GridSplit.instLinearOrderGridSlotLeftBits
lemma rowMatrix_linear (p : A → Bool) (z : ℝ) :
    (rowMatrix bits H p z).toEuclideanLin=
      ∑a : ∀y, Equiv.Perm (FreeSlot (rowFamily bits H y) 0),
        (∏y, (conditionalGroupLaw (rowFamily bits H y) z (a y):ℂ)) •
          hilbertTensorRep p _ ((rowGrouping bits H).permCongr (Equiv.Perm.sigmaCongrRight a)) := by
  refine Eq.trans (groupedAverage_literal_linear (I := GridSlot (rightBits bits))
    (X := fun y => FreeSlot (rowFamily bits H y) 0) (N := junctionSize bits H)
    (A := A) (rowGrouping bits H) p
    (fun y a => (conditionalGroupLaw (rowFamily bits H y) z a : ℂ))) ?_
  apply Finset.sum_congr
  · ext a; simp only [Finset.mem_univ]
  · intro a _; rfl

lemma columnMatrix_linear (p : A → Bool) (z : ℝ) :
    (columnMatrix bits H p z).toEuclideanLin=
      ∑a : ∀x, Equiv.Perm (FreeSlot (columnFamily bits H x) 0),
        (∏x, (conditionalGroupLaw (columnFamily bits H x) z (a x):ℂ)) •
          hilbertTensorRep p _ ((columnGrouping bits H).permCongr (Equiv.Perm.sigmaCongrRight a)) := by
  refine Eq.trans (groupedAverage_literal_linear (I := GridSlot (leftBits bits))
    (X := fun x => FreeSlot (columnFamily bits H x) 0) (N := junctionSize bits H)
    (A := A) (columnGrouping bits H) p
    (fun x a => (conditionalGroupLaw (columnFamily bits H x) z a : ℂ))) ?_
  apply Finset.sum_congr
  · ext a; simp only [Finset.mem_univ]
  · intro a _; rfl

theorem rowAverage_matrix (p : A → Bool) (z : ℝ) :
    rowAverage bits H (junctionTensorRep bits H p) z=(rowMatrix bits H p z).toEuclideanLin := by
  rw [rowAverage_child_laws,rowMatrix_linear]
  apply Finset.sum_congr
  · ext a; simp only [Finset.mem_univ]
  intro a _
  congr 1

theorem columnAverage_matrix (p : A → Bool) (z : ℝ) :
    columnAverage bits H (junctionTensorRep bits H p) z=(columnMatrix bits H p z).toEuclideanLin := by
  rw [columnAverage_child_laws,columnMatrix_linear]
  apply Finset.sum_congr
  · ext a; simp only [Finset.mem_univ]
  intro a _
  congr 1
  change hilbertTensorRep p _ ((inputToJunction bits H).permCongr _) = _
  rw [column_perm_to_junction]

end BinaryCoordinateSweeps.GridSplit

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

lemma natShift_pow_exp (n t : ℕ) :
    (n+1:ℝ)^t=Real.exp ((t:ℝ)*Real.log (n+1:ℝ)) := by
  rw [Real.exp_nat_mul,Real.exp_log (by positivity)]

variable {A I : Type*} [Fintype A] [DecidableEq A] [Fintype I] [LinearOrder I]
  {n : I → ℕ} {N : ℕ}
  {V : I → Type*} [∀i, NormedAddCommGroup (V i)]
  [∀i, InnerProductSpace ℂ (V i)] [∀i, FiniteDimensional ℂ (V i)]

theorem grouped_projected_exp_bound (e : (Σₗ i, Fin (n i)) ≃o Fin N)
    (g : Equiv.Perm (Fin N)) (p : A → Bool)
    (ρ : ∀i, Representation ℂ (Equiv.Perm (Fin (n i))) (V i)) [∀i, (ρ i).IsIrreducible]
    (hρ : ∀i a v, ‖ρ i a v‖=‖v‖) (w : ∀i, Equiv.Perm (Fin (n i)) → ℂ)
    {q : ℕ} (hq : 0<q) (B : I → ℝ)
    (hB : ∀i, evenMoment q (groupAverage (ρ i) (w i))≤Real.exp (B i)) :
    matrixMoment q (groupedProjection e g p ρ*groupedAverage e g p w) ≤
      Real.exp (∑i, ((((Fintype.card A)^2:ℕ):ℝ)*Real.log (n i+1:ℝ)+B i)) := by
  refine (grouped_projected_moment_le e g p ρ hρ w hq).trans ?_
  rw [Real.exp_sum]
  apply Finset.prod_le_prod
  · intro i _; exact mul_nonneg (by positivity) (evenMoment_nonneg _ _)
  · intro i _
    rw [Real.exp_add,←natShift_pow_exp]
    exact mul_le_mul_of_nonneg_left (hB i) (by positivity)

omit [∀ i, FiniteDimensional ℂ (V i)] in
lemma groupedProjection_overlap_contract
    {J W : Type*} [Fintype J] [LinearOrder J]
    {m : J → ℕ} {U : J → Type*} [∀j,NormedAddCommGroup (U j)]
    [∀j,InnerProductSpace ℂ (U j)] [∀j,FiniteDimensional ℂ (U j)]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (eR : (Σₗ i, Fin (n i)) ≃o Fin N) (eC : (Σₗ j, Fin (m j)) ≃o Fin N)
    (gR gC : Equiv.Perm (Fin N)) (p : A → Bool)
    (ρ : Representation ℂ (Equiv.Perm (Fin N)) W)
    (α : ∀i, Representation ℂ (Equiv.Perm (Fin (n i))) (V i))
    (β : ∀j, Representation ℂ (Equiv.Perm (Fin (m j))) (U j)) :
    ‖groupedProjection eC gC p β*isotypicProjection p ρ*groupedProjection eR gR p α‖≤1 := by
  have hP : ‖isotypicProjection p ρ‖≤1 := IsStarProjection.norm_le _
    ⟨projectionMatrix_idempotent _,(isotypicProjection_psd p ρ).isHermitian⟩
  calc
    _ ≤ (‖groupedProjection eC gC p β‖*‖isotypicProjection p ρ‖)*‖groupedProjection eR gR p α‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1*1)*1 := mul_le_mul
      (mul_le_mul (groupedProjection_norm_le eC gC p β) hP (norm_nonneg _) zero_le_one)
      (groupedProjection_norm_le eR gR p α) (norm_nonneg _) (by norm_num)
    _ = 1 := by norm_num

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
-- module Solutions.OAIB3_Bsw.BinarySweep_MatrixBounds_SchattenTriangle
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical Matrix.Norms.L2Operator

namespace BinaryCoordinateSweeps.TraceHolder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma schatten_mul_left {q : ℕ} (hq : 0<q) (C A : M ι) :
    schatten q (C*A) ≤ ‖C‖*schatten q A := by
  apply (pow_le_pow_iff_left₀ (schatten_nonneg _ _)
      (mul_nonneg (norm_nonneg _) (schatten_nonneg _ _)) (by omega : 2*q≠0)).mp
  rw [mul_pow,schatten_pow hq,schatten_pow hq]
  exact matrixMoment_mul_left hq C A

lemma schatten_mul_right {q : ℕ} (hq : 0<q) (A C : M ι) :
    schatten q (A*C) ≤ schatten q A*‖C‖ := by
  rw [← schatten_star q (A*C),star_mul]
  simpa only [norm_star,schatten_star,mul_comm] using schatten_mul_left hq (star C) (star A)

lemma norm_le_schatten {q : ℕ} (hq : 0<q) (A : M ι) : ‖A‖≤ schatten q A := by
  by_cases hz : matrixMoment q A=0
  · rw [(matrixMoment_eq_zero_iff hq A).mp hz,norm_zero]
    exact schatten_nonneg _ _
  have ht := lt_of_le_of_ne (matrixMoment_nonneg q A) (Ne.symm hz)
  obtain ⟨U,V,d,hU,hV,hd,hs,he⟩ := normalized_svd hq A ht
  have hd1 : ∀i, d i≤ 1 := by
    intro i
    rw [← hs]
    exact Finset.single_le_sum (fun j _ => hd j) (Finset.mem_univ i)
  have hD : ‖diagPower d ((((2*q:ℕ):ℝ)⁻¹:ℝ):ℂ)‖≤ 1 :=
    diagPower_norm_le_one d hd hd1 (by simp)
  conv_lhs => rw [he,norm_smul,Real.norm_eq_abs]
  change |schatten q A| * _ ≤ schatten q A
  rw [abs_of_nonneg (schatten_nonneg q A)]
  apply mul_le_of_le_one_right (schatten_nonneg _ _)
  refine (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) ?_).trans hV)
  exact (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) hU).trans hD)

lemma schatten_sandwich {q : ℕ} (hq : 0<q) (A B C : M ι) :
    schatten q (A*B*C)≤ schatten q A*‖B‖*schatten q C := by
  exact (schatten_mul_right hq (A*B) C).trans
    ((mul_le_mul_of_nonneg_right (schatten_mul_right hq A B) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (norm_le_schatten hq C)
        (mul_nonneg (schatten_nonneg _ _) (norm_nonneg _))))

end BinaryCoordinateSweeps.TraceHolder

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_ProjectionSplitting
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical Matrix.Norms.L2Operator

namespace BinaryCoordinateSweeps.TraceHolder
variable {ι α β : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [Fintype β]

lemma projection_sandwich_split (X Y P : M ι) (R : α → M ι) (C : β → M ι)
    (hR : ∀a, R a*R a=R a) (hC : ∀b, C b*C b=C b)
    (hsR : ∑a, R a=1) (hsC : ∑b, C b=1) :
    Y*P*X = ∑b, ∑a, (Y*C b)*(C b*P*R a)*(R a*X) := by
  have he (a : α) (b : β) : (Y*C b)*(C b*P*R a)*(R a*X)=Y*C b*P*R a*X := by
    simp only [mul_assoc,← mul_assoc (C b) (C b),hC b,
      ← mul_assoc (R a) (R a),hR a]
  simp_rw [he]
  simp only [← Finset.sum_mul,← Finset.mul_sum,hsR,hsC,mul_one]

theorem schatten_projection_split {q : ℕ} (hq : 0<q)
    (X Y P : M ι) (R : α → M ι) (C : β → M ι)
    (hR : ∀a, R a*R a=R a) (hC : ∀b, C b*C b=C b)
    (hsR : ∑a, R a=1) (hsC : ∑b, C b=1) :
    schatten q (Y*P*X) ≤ ∑b, ∑a,
      schatten q (Y*C b)*‖C b*P*R a‖*schatten q (R a*X) := by
  rw [projection_sandwich_split X Y P R C hR hC hsR hsC]
  apply (schatten_sum_le hq _).trans
  apply Finset.sum_le_sum
  intro b _
  apply (schatten_sum_le hq _).trans
  exact Finset.sum_le_sum fun a _ => schatten_sandwich hq _ _ _

theorem matrixMoment_projection_split_bound {q : ℕ} (hq : 0<q)
    (X Y P : M ι) (R : α → M ι) (C : β → M ι)
    (hR : ∀a, R a*R a=R a) (hC : ∀b, C b*C b=C b)
    (hsR : ∑a, R a=1) (hsC : ∑b, C b=1)
    (B : ℝ) (hB : 0≤B)
    (hterm : ∀a b, matrixMoment q (Y*C b)*‖C b*P*R a‖^(2*q)*
      matrixMoment q (R a*X) ≤ B^(2*q)) :
    matrixMoment q (Y*P*X) ≤ ((Fintype.card α*Fintype.card β:ℕ):ℝ)^(2*q)*B^(2*q) := by
  have ht (a : α) (b : β) :
      schatten q (Y*C b)*‖C b*P*R a‖*schatten q (R a*X) ≤ B := by
    apply (pow_le_pow_iff_left₀
      (mul_nonneg (mul_nonneg (schatten_nonneg _ _) (norm_nonneg _)) (schatten_nonneg _ _))
      hB (by omega : 2*q≠0)).mp
    simpa only [mul_pow,schatten_pow hq] using hterm a b
  have hs : schatten q (Y*P*X) ≤ ((Fintype.card α*Fintype.card β:ℕ):ℝ)*B := by
    apply (schatten_projection_split hq X Y P R C hR hC hsR hsC).trans
    calc
      _ ≤ ∑b : β, ∑a : α, B := Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun a _ => ht a b
      _ = _ := by simp [mul_comm,mul_assoc]
  have hh := pow_le_pow_left₀ (schatten_nonneg _ _) hs (2*q)
  simpa only [schatten_pow hq,mul_pow] using hh

end BinaryCoordinateSweeps.TraceHolder

end

open scoped BigOperators Classical Matrix.Norms.L2Operator

namespace BinaryCoordinateSweeps.TraceHolder

lemma overlap_power_le {x c L : ℝ} {q : ℕ} (hx : 0≤x) (hx1 : x≤1)
    (hc : 0≤c) (hcq : c≤q) (hq : 0<q) (hL : x^2≤Real.exp L) :
    x^(2*q)≤Real.exp (c*L) := by
  by_cases hz : x=0
  · rw [hz,zero_pow (by omega : 2*q≠0)]
    exact (Real.exp_pos _).le
  have hp : 0<x := lt_of_le_of_ne hx (Ne.symm hz)
  have hl : Real.log x≤0 := Real.log_nonpos hp.le hx1
  have he : 2*Real.log x≤L := by
    have hh := Real.log_le_log (sq_pos_of_pos hp) hL
    simpa only [Real.log_pow,Real.log_exp,Nat.cast_ofNat] using hh
  calc
    x^(2*q) = Real.exp (((2*q:ℕ):ℝ)*Real.log x) := by
      rw [Real.exp_nat_mul,Real.exp_log hp]
    _ ≤ Real.exp (c*L) := by
      apply Real.exp_le_exp.mpr
      calc
        ((2*q:ℕ):ℝ)*Real.log x = (q:ℝ)*(2*Real.log x) := by push_cast; ring
        _ ≤ c*(2*Real.log x) := mul_le_mul_of_nonpos_right hcq (by linarith)
        _ ≤ c*L := mul_le_mul_of_nonneg_left he hc

variable {ι α β : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [Fintype β]

theorem matrixMoment_dense_exponential {q : ℕ} (hq : 0<q)
    (X Y P : M ι) (R : α → M ι) (C : β → M ι)
    (hR : ∀a, R a*R a=R a) (hC : ∀b, C b*C b=C b)
    (hsR : ∑a, R a=1) (hsC : ∑b, C b=1)
    (FR : α → ℝ) (FC : β → ℝ) (c F H Echild Eoverlap : ℝ)
    (hc : 0≤c) (hcq : c≤q)
    (hchild : ∀a b, matrixMoment q (Y*C b)*matrixMoment q (R a*X) ≤
      Real.exp (-c*(FR a+FC b)+Echild))
    (hoverlap : ∀a b, ‖C b*P*R a‖^2≤Real.exp (FR a+FC b-F+H+Eoverlap))
    (hcontract : ∀a b, ‖C b*P*R a‖≤1) :
    matrixMoment q (Y*P*X) ≤ ((Fintype.card α*Fintype.card β:ℕ):ℝ)^(2*q)*
      Real.exp (-c*F+Echild+c*H+c*Eoverlap) := by
  let B := -c*F+Echild+c*H+c*Eoverlap
  have hq0 : ((2*q:ℕ):ℝ)≠0 := by exact_mod_cast (by omega : 2*q≠0)
  have he : (Real.exp (B/((2*q:ℕ):ℝ)))^(2*q)=Real.exp B := by
    rw [←Real.exp_nat_mul]
    congr 1
    field_simp
  have ht (a : α) (b : β) :
      matrixMoment q (Y*C b)*‖C b*P*R a‖^(2*q)*matrixMoment q (R a*X) ≤
        (Real.exp (B/((2*q:ℕ):ℝ)))^(2*q) := by
    rw [he]
    calc
      _ = (matrixMoment q (Y*C b)*matrixMoment q (R a*X))*‖C b*P*R a‖^(2*q) := by ring
      _ ≤ Real.exp (-c*(FR a+FC b)+Echild)*
          Real.exp (c*(FR a+FC b-F+H+Eoverlap)) :=
        mul_le_mul (hchild a b)
          (overlap_power_le (norm_nonneg _) (hcontract a b) hc hcq hq (hoverlap a b))
          (pow_nonneg (norm_nonneg _) _) (Real.exp_pos _).le
      _ = Real.exp B := by rw [←Real.exp_add]; congr 1; dsimp [B]; ring
  have hh := matrixMoment_projection_split_bound hq X Y P R C hR hC hsR hsC
    (Real.exp (B/((2*q:ℕ):ℝ))) (Real.exp_pos _).le ht
  rw [he] at hh
  exact hh

end BinaryCoordinateSweeps.TraceHolder

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_GridProjectedMoment
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.GridSplit
open Irrep Representation Signed TraceHolder Density

variable {m n h : ℕ} (bits : Fin (m+n) → ℕ) (H : PathFamily bits h)
  {A : Type*} [Fintype A] [DecidableEq A]

lemma junctionAverage_linear (p : A → Bool) (z : ℝ) :
    (junctionAverage bits H p z).toEuclideanLin=
      groupAverage (junctionTensorRep bits H p) (fun a => (conditionalGroupLaw H z a:ℂ)) := by
  exact sampleMatrix_linear p _ _

lemma junctionAverage_split (p : A → Bool) (z : ℝ) :
    junctionAverage bits H p z=junctionFrame bits H p*columnMatrix bits H p z*rowMatrix bits H p z := by
  apply Matrix.toEuclideanLin.injective
  rw [junctionAverage_linear,groupAverage_split,rowAverage_matrix,columnAverage_matrix]
  simp only [Matrix.toLpLin_mul_same,←Module.End.mul_eq_comp,junctionFrame,actionMatrix_linear]
  rfl

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin (junctionSize bits H))) V)

local instance instLinearOrderGridSlotRightBits_1_r03ce33_1 : LinearOrder (GridSlot (rightBits bits)) := rowOrder bits
local instance instLinearOrderGridSlotLeftBits_1_r03ce33_1 : LinearOrder (GridSlot (leftBits bits)) := columnOrder bits
omit [FiniteDimensional ℂ V] in
lemma projection_commutes_column (p : A → Bool) (z : ℝ) :
    isotypicProjection p ρ*columnMatrix bits H p z=columnMatrix bits H p z*isotypicProjection p ρ := by
  unfold columnMatrix
  rw [groupedAverage_law]
  simp only [Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc,typeProjection_commutes_action]

omit [FiniteDimensional ℂ V] in
lemma junction_projected_moment (p : A → Bool) (z : ℝ) (q : ℕ) :
    matrixMoment q (isotypicProjection p ρ*junctionAverage bits H p z)=
      matrixMoment q (columnMatrix bits H p z*isotypicProjection p ρ*rowMatrix bits H p z) := by
  rw [junctionAverage_split,←mul_assoc,←mul_assoc]
  have hu : isotypicProjection p ρ*junctionFrame bits H p=
      junctionFrame bits H p*isotypicProjection p ρ := typeProjection_commutes_action p ρ _
  rw [hu,mul_assoc (junctionFrame bits H p),projection_commutes_column,
    mul_assoc (junctionFrame bits H p)]
  rw [matrixMoment_linear,matrixMoment_linear,Matrix.toLpLin_mul_same,
    ←Module.End.mul_eq_comp]
  apply evenMoment_unitary_left
  change (Matrix.toEuclideanLin (junctionFrame bits H p)).adjoint*
    Matrix.toEuclideanLin (junctionFrame bits H p)=1
  unfold junctionFrame
  rw [actionMatrix_linear,unitary_rep_adjoint _ (hilbertTensorRep_unitary p),←map_mul,
    inv_mul_cancel,map_one]

theorem conditional_le_junction [ρ.IsIrreducible]
    (hρ : ∀g v, ‖ρ g v‖=‖v‖) (p : A → Bool)
    (hocc : 0<Module.finrank ℂ (IntertwiningMap ρ (hilbertTensorRep p (junctionSize bits H))))
    (z : ℝ) {q : ℕ} (hq : 0<q) :
    evenMoment q (groupAverage (ρ.comp (inputToJunction bits H).permCongrHom.toMonoidHom)
      (fun a => (conditionalGroupLaw H z a:ℂ)))≤
      matrixMoment q (columnMatrix bits H p z*isotypicProjection p ρ*rowMatrix bits H p z) := by
  rw [←junction_projected_moment bits H ρ p z q]
  exact sampleMoment_le_projected p ρ hρ hocc _ _ hq

end BinaryCoordinateSweeps.GridSplit

end

open scoped BigOperators Classical Matrix.Norms.L2Operator

namespace BinaryCoordinateSweeps.Signed
open Irrep Representation TraceHolder

variable {A I J : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype I] [LinearOrder I] [Nonempty I] [Fintype J] [LinearOrder J]
  {n : I → ℕ} {m : J → ℕ} {N : ℕ}

omit [Nonempty A] [Nonempty I] in
lemma blockActive_card_exp (p : A → Bool) :
    (Fintype.card (∀i, ActiveType p (n i)):ℝ)≤
      Real.exp ((Fintype.card A:ℝ)^2*blockLogSize n) := by
  have hc : (Fintype.card (∀i, ActiveType p (n i)):ℝ)≤∏i,(n i+1:ℝ)^((Fintype.card A)^2) := by
    exact_mod_cast blockActive_card (n:=n) p
  refine hc.trans_eq ?_
  rw [blockLogSize,Finset.mul_sum,Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  exact_mod_cast natShift_pow_exp (n i) ((Fintype.card A)^2)

theorem grouped_dense_bound
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (board : Fin N ↪ I × J) (p : A → Bool)
    (eR : (Σₗ i, Fin (n i)) ≃o Fin N) (eC : (Σₗ j, Fin (m j)) ≃o Fin N)
    (gR gC : Equiv.Perm (Fin N))
    (hR : ∀t, groupOf eR gR t=(board t).1) (hC : ∀t, groupOf eC gC t=(board t).2)
    (ρ : Representation ℂ (Equiv.Perm (Fin N)) W) [ρ.IsIrreducible]
    (wR : ∀i, Equiv.Perm (Fin (n i)) → ℂ) (wC : ∀j, Equiv.Perm (Fin (m j)) → ℂ)
    {q : ℕ} (hq : 0<q) (c : ℝ) (hc : 0≤c) (hcq : c≤q)
    (ER : I → ℝ) (EC : J → ℝ)
    (hchildR : ∀i (a : ActiveType p (n i)),
      evenMoment q (groupAverage (Young.partitionHilbertRep a.val) (wR i))≤Real.exp (-c*typeF a.val+ER i))
    (hchildC : ∀j (a : ActiveType p (m j)),
      evenMoment q (groupAverage (Young.partitionHilbertRep a.val) (wC j))≤Real.exp (-c*typeF a.val+EC j)) :
    matrixMoment q (groupedAverage eC gC p wC*isotypicProjection p ρ*groupedAverage eR gR p wR) ≤
      Real.exp (-c*Real.log (Module.finrank ℂ W:ℝ)+(∑i, ER i)+(∑j, EC j)+
        c*(Fintype.card I*Fintype.card J-(N:ℝ))+
        (1+4*c+2*(q:ℝ))*(Fintype.card A:ℝ)^2*(blockLogSize n+blockLogSize m)) := by
  let R := fun a : ∀i, ActiveType p (n i) =>
    groupedProjection eR gR p (fun i => Young.partitionHilbertRep (a i).val)
  let C := fun a : ∀j, ActiveType p (m j) =>
    groupedProjection eC gC p (fun j => Young.partitionHilbertRep (a j).val)
  let FR := fun a : ∀i, ActiveType p (n i) => ∑i, typeF (a i).val
  let FC := fun a : ∀j, ActiveType p (m j) => ∑j, typeF (a j).val
  let L := blockLogSize n+blockLogSize m
  let D : ℝ := (Fintype.card A:ℝ)^2
  let E := (∑i, ER i)+(∑j, EC j)+D*L
  have hchild (a : ∀i, ActiveType p (n i)) (b : ∀j, ActiveType p (m j)) :
      matrixMoment q (groupedAverage eC gC p wC*C b)*
        matrixMoment q (R a*groupedAverage eR gR p wR)≤Real.exp (-c*(FR a+FC b)+E) := by
    have hr := grouped_projected_exp_bound eR gR p
      (fun i => Young.partitionHilbertRep (a i).val)
      (fun i => Young.partitionHilbertRep_unitary (a i).val) wR hq
      (fun i => -c*typeF (a i).val+ER i) (fun i => hchildR i (a i))
    have ht := grouped_projected_exp_bound eC gC p
      (fun j => Young.partitionHilbertRep (b j).val)
      (fun j => Young.partitionHilbertRep_unitary (b j).val) wC hq
      (fun j => -c*typeF (b j).val+EC j) (fun j => hchildC j (b j))
    rw [groupedProjection_commutes_average] at ht
    refine (mul_le_mul ht hr (matrixMoment_nonneg _ _) (Real.exp_pos _).le).trans_eq ?_
    rw [←Real.exp_add]
    congr 1
    simp only [FR,FC,E,D,L,blockLogSize,Finset.sum_add_distrib,
      ←Finset.mul_sum,Nat.cast_pow]
    ring
  have ho (a : ∀i, ActiveType p (n i)) (b : ∀j, ActiveType p (m j)) :
      ‖C b*isotypicProjection p ρ*R a‖^2≤Real.exp
        (FR a+FC b-Real.log (Module.finrank ℂ W:ℝ)+
          (Fintype.card I*Fintype.card J-(N:ℝ))+4*D*L) := by
    exact actual_board_overlap_exp board p eR eC gR gC hR hC ρ
      (fun i => Young.partitionHilbertRep (a i).val) (fun j => Young.partitionHilbertRep (b j).val)
  have hk (a : ∀i, ActiveType p (n i)) (b : ∀j, ActiveType p (m j)) :
      ‖C b*isotypicProjection p ρ*R a‖≤1 :=
    groupedProjection_overlap_contract eR eC gR gC p ρ
      (fun i => Young.partitionHilbertRep (a i).val) (fun j => Young.partitionHilbertRep (b j).val)
  have hb := matrixMoment_dense_exponential hq (groupedAverage eR gR p wR)
    (groupedAverage eC gC p wC) (isotypicProjection p ρ) R C
    (fun a => groupedProjection_idempotent eR gR p _) (fun b => groupedProjection_idempotent eC gC p _)
    (groupedActive_projection_sum eR gR p) (groupedActive_projection_sum eC gC p)
    FR FC c (Real.log (Module.finrank ℂ W:ℝ)) (Fintype.card I*Fintype.card J-(N:ℝ))
    E (4*D*L) hc hcq hchild ho hk
  have hn : ((Fintype.card (∀i, ActiveType p (n i))*Fintype.card (∀j, ActiveType p (m j)):ℕ):ℝ) ≤
      Real.exp (D*L) := by
    rw [Nat.cast_mul]
    refine (mul_le_mul (blockActive_card_exp (n:=n) p) (blockActive_card_exp (n:=m) p)
      (by positivity) (Real.exp_pos _).le).trans_eq ?_
    rw [←Real.exp_add]
    congr 1
    dsimp [D,L]
    ring
  refine hb.trans ((mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hn (2*q))
    (Real.exp_pos _).le).trans_eq ?_)
  rw [←Real.exp_nat_mul,←Real.exp_add]
  congr 1
  dsimp [E,D,L]
  push_cast
  ring

end BinaryCoordinateSweeps.Signed

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_GridSplitCost
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.GridSplit
variable {m n h : ℕ} (bits : Fin (m+n) → ℕ) (H : PathFamily bits h)

lemma left_path_address (j : Fin m) (k : Fin h) :
    leftOutsideEquiv bits j (fun i => H.position (j.castAdd n).castSucc k i)=
      (rightSlot bits (H.position 0 k),
        fun i : {i : Fin m // i≠j} => leftSlot bits (H.position (leftTime j.castSucc) k) i) := by
  apply Prod.ext
  · change rightSlot bits (H.position (leftTime j.castSucc) k)=_
    exact rightSlot_leftTime bits H j.castSucc k
  · rfl

lemma right_path_address (j : Fin n) (k : Fin h) :
    rightOutsideEquiv bits j (fun i => H.position (j.natAdd m).castSucc k i)=
      (leftSlot bits (H.position (rightTime (m:=m) 0) k),
        fun i : {i : Fin n // i≠j} => rightSlot bits (H.position (rightTime j.castSucc) k) i) := by
  apply Prod.ext
  · change leftSlot bits (H.position (rightTime j.castSucc) k)=_
    exact leftSlot_rightTime bits H j.castSucc k
  · rfl

lemma card_pair_fiber {K Y U : Type*} [Fintype K] {l : ℕ}
    (f : K → Y) (g : K → U) (y : Y) (u : U)
    (e : {k : K // f k=y} ≃ Fin l) :
    Fintype.card {k : K // (f k,g k)=(y,u)} =
      Fintype.card {i : Fin l // g (e.symm i).val=u} := by
  apply Fintype.card_congr
  refine { toFun := fun k => ⟨e ⟨k.val,congrArg Prod.fst k.property⟩, ?_⟩
           invFun := fun i => ⟨(e.symm i.val).val, ?_⟩
           left_inv := ?_
           right_inv := ?_ }
  · simpa only [Equiv.symm_apply_apply] using congrArg Prod.snd k.property
  · exact Prod.ext (e.symm i.val).property i.property
  · intro k; apply Subtype.ext; simp only [Equiv.symm_apply_apply]
  · intro i; apply Subtype.ext
    exact e.apply_symm_apply i.val

lemma lineHoles_left (j : Fin m) (u : GridOutside bits (j.castAdd n)) :
    lineHoles H (j.castAdd n) u =
      lineHoles (rowFamily bits H ((leftOutsideEquiv bits j) u).1) j
        ((leftOutsideEquiv bits j) u).2 := by
  unfold lineHoles
  let y := ((leftOutsideEquiv bits j) u).1
  let v := ((leftOutsideEquiv bits j) u).2
  have he (k : Fin h) : (fun i : {i : Fin (m+n) // i≠j.castAdd n} => H.position (j.castAdd n).castSucc k i)=u ↔
      (rightSlot bits (H.position 0 k),
        fun i : {i : Fin m // i≠j} => leftSlot bits (H.position (leftTime j.castSucc) k) i)=(y,v) := by
    rw [← Equiv.apply_eq_iff_eq (leftOutsideEquiv bits j),left_path_address]
  rw [Fintype.card_congr (Equiv.subtypeEquivRight he)]
  convert card_pair_fiber (fun k => rightSlot bits (H.position 0 k))
    (fun k => fun i : {i : Fin m // i≠j} => leftSlot bits (H.position (leftTime j.castSucc) k) i) y v
    (@Fintype.equivFin (RowLabels bits H y) (rowLabelsFintype bits H y)) using 1 <;>
    congr!

lemma lineHoles_right (j : Fin n) (u : GridOutside bits (j.natAdd m)) :
    lineHoles H (j.natAdd m) u =
      lineHoles (columnFamily bits H ((rightOutsideEquiv bits j) u).1) j
        ((rightOutsideEquiv bits j) u).2 := by
  unfold lineHoles
  let x := ((rightOutsideEquiv bits j) u).1
  let v := ((rightOutsideEquiv bits j) u).2
  have he (k : Fin h) : (fun i : {i : Fin (m+n) // i≠j.natAdd m} => H.position (j.natAdd m).castSucc k i)=u ↔
      (leftSlot bits (H.position (rightTime (m:=m) 0) k),
        fun i : {i : Fin n // i≠j} => rightSlot bits (H.position (rightTime j.castSucc) k) i)=(x,v) := by
    rw [← Equiv.apply_eq_iff_eq (rightOutsideEquiv bits j),right_path_address]
  rw [Fintype.card_congr (Equiv.subtypeEquivRight he)]
  convert card_pair_fiber (fun k => leftSlot bits (H.position (rightTime (m:=m) 0) k))
    (fun k => fun i : {i : Fin n // i≠j} => rightSlot bits (H.position (rightTime j.castSucc) k) i) x v
    (@Fintype.equivFin (ColumnLabels bits H x) (columnLabelsFintype bits H x)) using 1 <;>
    congr!

theorem pathCost_split : pathCost H =
    (∑y, pathCost (rowFamily bits H y)) + (∑x, pathCost (columnFamily bits H x)) := by
  unfold pathCost
  rw [Fin.sum_univ_add]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simp_rw [lineHoles_left]
    have he := Equiv.sum_comp (leftOutsideEquiv bits j) (fun yu =>
      Real.log (((2^leftBits bits j:ℕ):ℝ)^lineHoles (rowFamily bits H yu.1) j yu.2 /
        (Nat.descFactorial (2^leftBits bits j) (lineHoles (rowFamily bits H yu.1) j yu.2):ℝ)))
    simpa only [Fintype.sum_prod_type] using he
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simp_rw [lineHoles_right]
    have he := Equiv.sum_comp (rightOutsideEquiv bits j) (fun xu =>
      Real.log (((2^rightBits bits j:ℕ):ℝ)^lineHoles (columnFamily bits H xu.1) j xu.2 /
        (Nat.descFactorial (2^rightBits bits j) (lineHoles (columnFamily bits H xu.1) j xu.2):ℝ)))
    simpa only [Fintype.sum_prod_type] using he

end BinaryCoordinateSweeps.GridSplit

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.GridSplit
open Irrep Representation Signed TraceHolder Density

variable {m n h : ℕ} (bits : Fin (m+n) → ℕ) (H : PathFamily bits h)
  {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

local instance instNonemptyGridSlotRightBits : Nonempty (GridSlot (rightBits bits)) := ⟨fun _ _ => false⟩

lemma holeCount_junction :
    (Fintype.card (GridSlot (rightBits bits)):ℝ)*Fintype.card (GridSlot (leftBits bits))-
      (junctionSize bits H:ℝ)=h := by
  have hh : h≤gridSize bits := by
    have he := Fintype.card_le_of_injective (H.position 0) (H.disjoint 0)
    simpa only [Fintype.card_fin,card_gridSlot] using he
  rw [junctionSize_eq,Nat.cast_sub hh,card_gridSlot,card_gridSlot,
    size_split,Nat.cast_mul]
  ring

attribute [local instance] OAI.BinaryCoordinateSweeps.GridSplit.instLinearOrderGridSlotRightBits_2
attribute [local instance] OAI.BinaryCoordinateSweeps.GridSplit.instLinearOrderGridSlotLeftBits_2
theorem conditional_dense_bound
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin (junctionSize bits H))) V) [ρ.IsIrreducible]
    (hρ : ∀g v, ‖ρ g v‖=‖v‖) (p : A → Bool)
    (hocc : 0<Module.finrank ℂ (IntertwiningMap ρ (hilbertTensorRep p (junctionSize bits H))))
    (z : ℝ) {q : ℕ} (hq : 0<q) (c : ℝ) (hc : 0≤c) (hcq : c≤q)
    (ER : GridSlot (rightBits bits) → ℝ) (EC : GridSlot (leftBits bits) → ℝ)
    (hchildR : ∀y (a : ActiveType p (rowFreeSize bits H y)),
      evenMoment q (groupAverage (Young.partitionHilbertRep a.val) (rowChildWeight bits H z y))≤
        Real.exp (-c*typeF a.val+ER y))
    (hchildC : ∀x (a : ActiveType p (columnFreeSize bits H x)),
      evenMoment q (groupAverage (Young.partitionHilbertRep a.val) (columnChildWeight bits H z x))≤
        Real.exp (-c*typeF a.val+EC x)) :
    evenMoment q (groupAverage (ρ.comp (inputToJunction bits H).permCongrHom.toMonoidHom)
      (fun a => (conditionalGroupLaw H z a:ℂ)))≤
      Real.exp (-c*Real.log (Module.finrank ℂ V:ℝ)+(∑y, ER y)+(∑x, EC x)+c*h+
        (1+4*c+2*(q:ℝ))*(Fintype.card A:ℝ)^2*
          (blockLogSize (rowFreeSize bits H)+blockLogSize (columnFreeSize bits H))) := by
  refine (conditional_le_junction bits H ρ hρ p hocc z hq).trans ?_
  have hb := grouped_dense_bound (physicalBoard bits H) p
    (groupingOrder (rowGrouping bits H)) (groupingOrder (columnGrouping bits H))
    (groupingPerm (rowGrouping bits H)) (groupingPerm (columnGrouping bits H))
    (physicalBoard_row bits H) (physicalBoard_column bits H) ρ
    (rowChildWeight bits H z) (columnChildWeight bits H z) hq c hc hcq ER EC hchildR hchildC
  rw [holeCount_junction] at hb
  exact hb

end BinaryCoordinateSweeps.GridSplit

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_GridDenseCost
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.GridSplit
open Irrep Representation Signed

variable {m n h : ℕ} (bits : Fin (m+n) → ℕ) (H : PathFamily bits h)

lemma sum_row_holes : ∑y, Fintype.card (RowLabels bits H y)=h := by
  rw [←Fintype.card_sigma]
  have he := Fintype.card_congr (Equiv.sigmaFiberEquiv (fun k : Fin h => rightSlot bits (H.position 0 k)))
  exact he.trans (Fintype.card_fin h)

lemma sum_column_holes : ∑x, Fintype.card (ColumnLabels bits H x)=h := by
  rw [←Fintype.card_sigma]
  have he := Fintype.card_congr (Equiv.sigmaFiberEquiv
    (fun k : Fin h => leftSlot bits (H.position (rightTime (m:=m) 0) k)))
  exact he.trans (Fintype.card_fin h)

lemma child_error_sum (e : ℝ) :
    (∑y, (e*Fintype.card (RowLabels bits H y)*Real.log (gridSize (leftBits bits))-
      pathCost (rowFamily bits H y)))+
    (∑x, (e*Fintype.card (ColumnLabels bits H x)*Real.log (gridSize (rightBits bits))-
      pathCost (columnFamily bits H x)))=
      e*h*Real.log (gridSize bits)-pathCost H := by
  rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,←Finset.sum_mul,←Finset.mul_sum,
    ←Finset.sum_mul,←Finset.mul_sum,←Nat.cast_sum,←Nat.cast_sum,
    sum_row_holes,sum_column_holes,pathCost_split,size_split,Nat.cast_mul,
    Real.log_mul (by exact_mod_cast (gridSize_pos (leftBits bits)).ne')
      (by exact_mod_cast (gridSize_pos (rightBits bits)).ne')]
  ring

lemma blockLogSize_le {I : Type*} [Fintype I] (f : I → ℕ) (s : ℕ) (hf : ∀i, f i ≤ s) :
    blockLogSize f ≤ Fintype.card I*Real.log (s+1:ℝ) := by
  calc
    _ ≤ ∑_i : I, Real.log (s+1:ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right (hf i) 1)
    _ = _ := by simp

lemma blocksLog_le :
    blockLogSize (rowFreeSize bits H)+blockLogSize (columnFreeSize bits H)≤
      (gridSize (rightBits bits):ℝ)*Real.log (gridSize (leftBits bits)+1:ℝ)+
      (gridSize (leftBits bits):ℝ)*Real.log (gridSize (rightBits bits)+1:ℝ) := by
  have hr := blockLogSize_le (rowFreeSize bits H) (gridSize (leftBits bits)) (fun _ => by
    rw [rowFreeSize,card_freeSlot]
    exact Nat.sub_le _ _)
  have hc := blockLogSize_le (columnFreeSize bits H) (gridSize (rightBits bits)) (fun _ => by
    rw [columnFreeSize,card_freeSlot]
    exact Nat.sub_le _ _)
  simpa only [card_gridSlot] using add_le_add hr hc

end BinaryCoordinateSweeps.GridSplit

end

open Filter Asymptotics
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_HookScalar
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open Filter Asymptotics
open scoped Topology

namespace BinaryCoordinateSweeps

lemma hook_polynomial_error_eventually (q : ℕ) : ∀ᶠ s : ℝ in atTop,
    ∀ u v p c : ℝ, 1≤u → 1≤v → 0≤p → p≤ s^(1/100:ℝ) →
      u≤ s^(4/5:ℝ) → v≤ s^(4/5:ℝ) → 0≤c → c≤2 →
      (1+4*c+2*(q:ℝ))*(2*p)^2*(v*Real.log (u+1)+u*Real.log (v+1)) ≤
        s^(9/10:ℝ) := by
  let C : ℝ := 16*(9+2*(q:ℝ))
  have hC : 0<C := by dsimp [C]; positivity
  have ho := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<2/25)).bound (inv_pos.mpr hC)
  filter_upwards [ho,eventually_ge_atTop (2:ℝ)] with s hs hs2
  have hs1 : 1≤ s := by linarith
  have hs0 : 0<s := by linarith
  have hl : 0≤Real.log s := Real.log_nonneg hs1
  have hlog : Real.log s ≤ C⁻¹*s^(2/25:ℝ) := by
    simpa only [Real.norm_of_nonneg hl,Real.norm_of_nonneg (Real.rpow_nonneg hs0.le _)] using hs
  intro u v p c hu hv hp hps hus hvs hc hc2
  have hu0 : 0<u := by linarith
  have hv0 : 0<v := by linarith
  have hup : u≤ s := hus.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hs1 (show (4/5:ℝ)≤1 by norm_num))
  have hvp : v≤ s := hvs.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hs1 (show (4/5:ℝ)≤1 by norm_num))
  have logle (w : ℝ) (hw : 1≤w) (hws : w≤ s) : Real.log (w+1)≤2*Real.log s := by
    have hsq : w+1≤ s*s := by nlinarith
    calc
      _ ≤ Real.log (s*s) := Real.log_le_log (by linarith) hsq
      _ = _ := by rw [Real.log_mul hs0.ne' hs0.ne']; ring
  have hlu := logle u hu hup
  have hlv := logle v hv hvp
  have hsum : v*Real.log (u+1)+u*Real.log (v+1)≤4*s^(4/5:ℝ)*Real.log s := by
    have h1 := mul_le_mul hlu hvs (by positivity) (mul_nonneg (by norm_num) hl)
    have h2 := mul_le_mul hlv hus (by positivity) (mul_nonneg (by norm_num) hl)
    nlinarith
  have hpp : (2*p)^2≤4*s^(1/50:ℝ) := by
    have hp2 := pow_le_pow_left₀ hp hps 2
    rw [←Real.rpow_mul_natCast hs0.le] at hp2
    norm_num at hp2
    nlinarith
  have hsum0 : 0≤v*Real.log (u+1)+u*Real.log (v+1) := by
    have h1 := Real.log_nonneg (show 1≤u+1 by linarith)
    have h2 := Real.log_nonneg (show 1≤v+1 by linarith)
    positivity
  calc
    _ ≤ (9+2*(q:ℝ))*(4*s^(1/50:ℝ))*(4*s^(4/5:ℝ)*Real.log s) := by
      gcongr
      linarith
    _ = C*s^(41/50:ℝ)*Real.log s := by
      rw [show (9+2*(q:ℝ))*(4*s^(1/50:ℝ))*(4*s^(4/5:ℝ)*Real.log s)=
        C*(s^(1/50:ℝ)*s^(4/5:ℝ))*Real.log s by dsimp [C]; ring,
        ←Real.rpow_add hs0]
      norm_num
    _ ≤ C*s^(41/50:ℝ)*(C⁻¹*s^(2/25:ℝ)) := by gcongr
    _ = s^(9/10:ℝ) := by
      rw [show C*s^(41/50:ℝ)*(C⁻¹*s^(2/25:ℝ))=
        (C*C⁻¹)*(s^(41/50:ℝ)*s^(2/25:ℝ)) by ring,mul_inv_cancel₀ hC.ne',one_mul,
        ←Real.rpow_add hs0]
      norm_num

lemma child_exponent_gap {s u : ℝ} (hs : 0<Real.log s) (hu : 0<Real.log u)
    (hbalance : Real.log u≤(4/5:ℝ)*Real.log s) :
    (11/10:ℝ)/Real.sqrt (Real.log s) ≤ 1/Real.sqrt (Real.log u) := by
  have hsqrt : 0<Real.sqrt (Real.log s) := Real.sqrt_pos.mpr hs
  have huqrt : 0<Real.sqrt (Real.log u) := Real.sqrt_pos.mpr hu
  have hsq := Real.sq_sqrt hu.le
  have hss := Real.sq_sqrt hs.le
  have hb : (11:ℝ)*Real.sqrt (Real.log u)≤10*Real.sqrt (Real.log s) := by
    nlinarith [Real.sqrt_nonneg (Real.log u),Real.sqrt_nonneg (Real.log s)]
  apply (div_le_div_iff₀ hsqrt huqrt).mpr
  nlinarith

lemma hook_strengthened_scalar {s F h C c e E : ℝ}
    (hs : 1600≤Real.log s) (hF : 0≤F) (hh : 0≤h)
    (hc : c0+(11/10:ℝ)/Real.sqrt (Real.log s)≤c) (hc2 : c≤2)
    (he : e≤e0-(11/10:ℝ)/Real.sqrt (Real.log s)) (hE : E≤ s^(9/10:ℝ)) :
    -c*F+e*h*Real.log s-C+c*h+E ≤
      -(c0+1/Real.sqrt (Real.log s)+inductionGap s)*F+
      (e0-1/Real.sqrt (Real.log s)-inductionGap s)*h*Real.log s-C+s^(9/10:ℝ) := by
  have hl : 0<Real.log s := by linarith
  have hsq : 0<Real.sqrt (Real.log s) := Real.sqrt_pos.mpr hl
  have hs40 : 40≤Real.sqrt (Real.log s) := Real.le_sqrt_of_sq_le (by norm_num; exact hs)
  have hsqe := Real.sq_sqrt hl.le
  have hgap : inductionGap s = (1/20:ℝ)/Real.sqrt (Real.log s) := by
    unfold inductionGap
    ring
  rw [hgap]
  have hsave : (1/20:ℝ)/Real.sqrt (Real.log s)*Real.log s≥2 := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hsq).mpr
    nlinarith
  have hc' : c0+1/Real.sqrt (Real.log s)+(1/20:ℝ)/Real.sqrt (Real.log s)≤c := by
    have hn := div_pos (show (1/20:ℝ)>0 by norm_num) hsq
    have heq : (11/10:ℝ)/Real.sqrt (Real.log s)=
      1/Real.sqrt (Real.log s)+(1/20:ℝ)/Real.sqrt (Real.log s)+(1/20:ℝ)/Real.sqrt (Real.log s) := by ring
    rw [heq] at hc
    linarith
  have he' : e*Real.log s+c≤(e0-1/Real.sqrt (Real.log s)-(1/20:ℝ)/Real.sqrt (Real.log s))*Real.log s := by
    have h1 := mul_le_mul_of_nonneg_right he hl.le
    have heq : (11/10:ℝ)/Real.sqrt (Real.log s)=
      1/Real.sqrt (Real.log s)+2*((1/20:ℝ)/Real.sqrt (Real.log s)) := by ring
    rw [heq] at h1
    nlinarith
  have hf := mul_le_mul_of_nonneg_right hc' hF
  have hholes := mul_le_mul_of_nonneg_right he' hh
  nlinarith

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical
open Filter

namespace BinaryCoordinateSweeps.GridSplit
open Irrep Representation Signed

lemma typeF_nonneg {n : ℕ} (α : n.Partition) : 0≤typeF α := by
  apply Real.log_nonneg
  exact_mod_cast irreducible_finrank_pos (Young.partitionHilbertRep α)

lemma cExponent_nonneg (s : ℕ) : 0≤cExponent s := by
  unfold cExponent c0
  positivity

lemma cExponent_le_two {s : ℕ} (hs : 1≤Real.log s) : cExponent s≤2 := by
  have hsq : 1≤Real.sqrt (Real.log s) := Real.le_sqrt_of_sq_le (by norm_num; exact hs)
  have hi := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hsq
  unfold cExponent c0
  norm_num at hi ⊢
  linarith

end BinaryCoordinateSweeps.GridSplit

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_GenericHookAux
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical
open Filter

namespace BinaryCoordinateSweeps.GridSplit
open Irrep Representation Signed

variable {m n h : ℕ} (bits : Fin (m+n) → ℕ) (H : PathFamily bits h)

theorem conditional_occurring_with_cost {t : ℕ} (ht : 0<t)
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin (junctionSize bits H))) V) [ρ.IsIrreducible]
    (hρ : ∀g v, ‖ρ g v‖=‖v‖)
    (hocc : 0<Module.finrank ℂ (IntertwiningMap ρ
      (hilbertTensorRep (Prod.fst : Bool × Fin t → Bool) (junctionSize bits H))))
    (z : ℝ) {q : ℕ} (hq : 0<q) (c e : ℝ) (hc : 0≤c) (hcq : c≤q)
    (hchildR : ∀y (a : ActiveType (Prod.fst : Bool × Fin t → Bool) (rowFreeSize bits H y)),
      evenMoment q (groupAverage (Young.partitionHilbertRep a.val) (rowChildWeight bits H z y))≤
        Real.exp (-c*typeF a.val+e*Fintype.card (RowLabels bits H y)*
          Real.log (gridSize (leftBits bits))-pathCost (rowFamily bits H y)))
    (hchildC : ∀x (a : ActiveType (Prod.fst : Bool × Fin t → Bool) (columnFreeSize bits H x)),
      evenMoment q (groupAverage (Young.partitionHilbertRep a.val) (columnChildWeight bits H z x))≤
        Real.exp (-c*typeF a.val+e*Fintype.card (ColumnLabels bits H x)*
          Real.log (gridSize (rightBits bits))-pathCost (columnFamily bits H x))) :
    evenMoment q (groupAverage (ρ.comp
      (inputToJunction bits H).permCongrHom.toMonoidHom)
      (fun a => (conditionalGroupLaw H z a:ℂ)))≤
      Real.exp (-c*Real.log (Module.finrank ℂ V:ℝ)+e*h*Real.log (gridSize bits)-pathCost H+c*h+
        (1+4*c+2*(q:ℝ))*(2*(t:ℝ))^2*
          ((gridSize (rightBits bits):ℝ)*Real.log (gridSize (leftBits bits)+1:ℝ)+
           (gridSize (leftBits bits):ℝ)*Real.log (gridSize (rightBits bits)+1:ℝ))) := by
  have hr : ∀y (a : ActiveType (Prod.fst : Bool × Fin t → Bool) (rowFreeSize bits H y)),
      evenMoment q (groupAverage (Young.partitionHilbertRep a.val) (rowChildWeight bits H z y))≤
        Real.exp (-c*typeF a.val+(e*Fintype.card (RowLabels bits H y)*
          Real.log (gridSize (leftBits bits))-pathCost (rowFamily bits H y))) := by
    intros; simpa only [add_sub_assoc] using hchildR _ _
  have hc' : ∀x (a : ActiveType (Prod.fst : Bool × Fin t → Bool) (columnFreeSize bits H x)),
      evenMoment q (groupAverage (Young.partitionHilbertRep a.val) (columnChildWeight bits H z x))≤
        Real.exp (-c*typeF a.val+(e*Fintype.card (ColumnLabels bits H x)*
          Real.log (gridSize (rightBits bits))-pathCost (columnFamily bits H x))) := by
    intros; simpa only [add_sub_assoc] using hchildC _ _
  let : NeZero t := ⟨ne_of_gt ht⟩
  have hh := conditional_dense_bound bits H ρ hρ (Prod.fst : Bool × Fin t → Bool)
    hocc z hq c hc hcq _ _ hr hc'
  simp only [Fintype.card_prod,Fintype.card_bool,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat] at hh
  refine hh.trans ?_
  apply Real.exp_le_exp.mpr
  rw [add_assoc (-c*Real.log (Module.finrank ℂ V:ℝ)),child_error_sum]
  have hb := mul_le_mul_of_nonneg_left (blocksLog_le bits H)
    (by positivity : 0≤(1+4*c+2*(q:ℝ))*(2*(t:ℝ))^2)
  linarith

theorem occurring_auxiliary_eventually_oai (q : ℕ) (hq : 2≤q) : ∀ᶠ s : ℕ in atTop,
    ∀ m n h : ℕ, ∀ bits : Fin (m+n) → ℕ, ∀ H : PathFamily bits h,
    gridSize bits=s →
    1≤Real.log (gridSize (leftBits bits)) → 1≤Real.log (gridSize (rightBits bits)) →
    Real.log (gridSize (leftBits bits))≤(4/5:ℝ)*Real.log s →
    Real.log (gridSize (rightBits bits))≤(4/5:ℝ)*Real.log s →
    ∀ t : ℕ, 0<t → (t:ℝ)≤(s:ℝ)^(1/100:ℝ) →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V],
    ∀ (ρ : Representation ℂ (Equiv.Perm (Fin (junctionSize bits H))) V) [ρ.IsIrreducible],
    (∀g v, ‖ρ g v‖=‖v‖) →
    0<Module.finrank ℂ (IntertwiningMap ρ
      (hilbertTensorRep (Prod.fst : Bool × Fin t → Bool) (junctionSize bits H))) → ∀z : ℝ,
    (∀y (a : ActiveType (Prod.fst : Bool × Fin t → Bool) (rowFreeSize bits H y)),
      evenMoment q (groupAverage (Young.partitionHilbertRep a.val) (rowChildWeight bits H z y))≤
        Real.exp (-cExponent (gridSize (leftBits bits))*typeF a.val+
          eExponent (gridSize (leftBits bits))*Fintype.card (RowLabels bits H y)*
          Real.log (gridSize (leftBits bits))-pathCost (rowFamily bits H y))) →
    (∀x (a : ActiveType (Prod.fst : Bool × Fin t → Bool) (columnFreeSize bits H x)),
      evenMoment q (groupAverage (Young.partitionHilbertRep a.val) (columnChildWeight bits H z x))≤
        Real.exp (-cExponent (gridSize (rightBits bits))*typeF a.val+
          eExponent (gridSize (rightBits bits))*Fintype.card (ColumnLabels bits H x)*
          Real.log (gridSize (rightBits bits))-pathCost (columnFamily bits H x))) →
    evenMoment q (groupAverage (ρ.comp
      (inputToJunction bits H).permCongrHom.toMonoidHom)
      (fun a => (conditionalGroupLaw H z a:ℂ)))≤
      Real.exp (-(cExponent s+inductionGap s)*Real.log (Module.finrank ℂ V:ℝ)+
        (eExponent s-inductionGap s)*h*Real.log s-pathCost H+(s:ℝ)^(9/10:ℝ)) := by
  have hcast : Tendsto (fun s : ℕ => (s:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hcast.eventually (hook_polynomial_error_eventually q),
    (Real.tendsto_log_atTop.comp hcast).eventually_ge_atTop 1600] with s herr hs
  intro m n h bits H hsize hu hv hub hvb t ht hts V _ _ _ ρ _ hρ hocc z hR hC
  let u := gridSize (leftBits bits)
  let v := gridSize (rightBits bits)
  let c := min (cExponent u) (cExponent v)
  let e := max (eExponent u) (eExponent v)
  have hq0 : 0<q := by omega
  have hc : 0≤c := le_min (cExponent_nonneg _) (cExponent_nonneg _)
  have hc2 : c≤2 := (min_le_left _ _).trans (cExponent_le_two hu)
  have hcq : c≤q := hc2.trans (by exact_mod_cast hq)
  have hl0 : 0<Real.log s := by linarith
  have hu0 : 0<Real.log u := by dsimp [u]; linarith
  have hv0 : 0<Real.log v := by dsimp [v]; linarith
  have hcg : c0+(11/10:ℝ)/Real.sqrt (Real.log s)≤c := by
    apply le_min <;> unfold cExponent
    · linarith [child_exponent_gap hl0 hu0 hub]
    · linarith [child_exponent_gap hl0 hv0 hvb]
  have heg : e≤e0-(11/10:ℝ)/Real.sqrt (Real.log s) := by
    apply max_le <;> unfold eExponent
    · linarith [child_exponent_gap hl0 hu0 hub]
    · linarith [child_exponent_gap hl0 hv0 hvb]
  have weaken (U N : ℕ) (F C : ℝ) (hF : 0≤F) (hU : 0≤Real.log U)
      (hcu : c≤cExponent U) (heu : eExponent U≤e) :
      -cExponent U*F+eExponent U*N*Real.log U-C≤-c*F+e*N*Real.log U-C := by
    have h1 := mul_le_mul_of_nonneg_right hcu hF
    have h2 := mul_le_mul_of_nonneg_right heu
      (mul_nonneg (Nat.cast_nonneg N) hU)
    nlinarith
  have hRR : ∀y (a : ActiveType (Prod.fst : Bool × Fin t → Bool) (rowFreeSize bits H y)),
      evenMoment q (groupAverage (Young.partitionHilbertRep a.val) (rowChildWeight bits H z y))≤
        Real.exp (-c*typeF a.val+e*Fintype.card (RowLabels bits H y)*
          Real.log (gridSize (leftBits bits))-pathCost (rowFamily bits H y)) := by
    intro y a
    exact (hR y a).trans (Real.exp_le_exp.mpr
      (weaken u _ _ _ (typeF_nonneg _) hu0.le (min_le_left _ _) (le_max_left _ _)))
  have hCC : ∀x (a : ActiveType (Prod.fst : Bool × Fin t → Bool) (columnFreeSize bits H x)),
      evenMoment q (groupAverage (Young.partitionHilbertRep a.val) (columnChildWeight bits H z x))≤
        Real.exp (-c*typeF a.val+e*Fintype.card (ColumnLabels bits H x)*
          Real.log (gridSize (rightBits bits))-pathCost (columnFamily bits H x)) := by
    intro x a
    exact (hC x a).trans (Real.exp_le_exp.mpr
      (weaken v _ _ _ (typeF_nonneg _) hv0.le (min_le_right _ _) (le_max_right _ _)))
  have hup : (u:ℝ)≤(s:ℝ)^(4/5:ℝ) := by
    rw [←Real.exp_log (show 0<(u:ℝ) by exact_mod_cast gridSize_pos (leftBits bits)),Real.rpow_def_of_pos (by
      rw [←hsize]; exact_mod_cast gridSize_pos bits)]
    exact Real.exp_le_exp.mpr (by simpa only [mul_comm] using hub)
  have hvp : (v:ℝ)≤(s:ℝ)^(4/5:ℝ) := by
    rw [←Real.exp_log (show 0<(v:ℝ) by exact_mod_cast gridSize_pos (rightBits bits)),Real.rpow_def_of_pos (by
      rw [←hsize]; exact_mod_cast gridSize_pos bits)]
    exact Real.exp_le_exp.mpr (by simpa only [mul_comm] using hvb)
  have hE := herr u v t c (by exact_mod_cast gridSize_pos (leftBits bits))
    (by exact_mod_cast gridSize_pos (rightBits bits)) (by positivity) hts hup hvp hc hc2
  refine (conditional_occurring_with_cost bits H ht ρ hρ hocc z hq0 c e hc hcq hRR hCC).trans ?_
  apply Real.exp_le_exp.mpr
  rw [hsize]
  exact hook_strengthened_scalar hs (Real.log_nonneg (by exact_mod_cast irreducible_finrank_pos ρ)) (by positivity) hcg hc2 heg hE

end BinaryCoordinateSweeps.GridSplit

end

open scoped BigOperators Classical
open Filter

end

end OAI
end

theorem solution : type_of% @OAI.BinaryCoordinateSweeps.GridSplit.occurring_auxiliary_eventually_oai := @OAI.BinaryCoordinateSweeps.GridSplit.occurring_auxiliary_eventually_oai
